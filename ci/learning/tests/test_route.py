"""The precheck/router and fetch (spec tests L02, L03, L04, L09 manifest/policy side, L16)."""

import base64
import json
import unittest

from ci.learning import fetch, policy as POL, route as RT
from ci.learning.tests.helpers import (CERTIFICATE, GENERATE, GEN_NS, REV, TempCase, family,
                                       generator_rows, manifest, policy)

NB_TEXT = b"# Design notebook\n\nPrefer small reductions.\n"


class Admission(TempCase):
    """L02: collaborator admission exactly as the gate; unauthorized first, before reading."""

    def setUp(self):
        super().setUp()
        self.make_base()
        self.fetched = self.make_fetched(generator_rows())

    def test_writer_admitted(self):
        for perm in ("admin", "maintain", "write"):
            r = RT.route(self.base, self.fetched, "someone", perm)
            self.assertTrue(r["accepted"], perm)
            self.assertEqual(r["route"], "generator", r["problems"])

    def test_accept_list_admitted_without_write(self):
        r = RT.route(self.base, self.fetched, "listed", "read")
        self.assertTrue(r["accepted"])

    def test_unauthorized_rejected_before_reading_files(self):
        (self.fetched / "files.json").write_text("not json")      # never read
        for perm in ("read", "none", "triage", ""):
            r = RT.route(self.base, self.fetched, "outsider", perm)
            self.assertEqual(r["route"], "rejected")
            self.assertFalse(r["accepted"])
            self.assertFalse(r["evaluate"])
            self.assertIn("no write access", r["problems"][0])

    def test_unauthorized_draft_still_rejected(self):
        r = RT.route(self.base, self.fetched, "outsider", "read", draft=True)
        self.assertEqual(r["route"], "rejected")

    def test_draft_skipped(self):
        """L04: a draft is never checked or evaluated."""
        (self.fetched / "files.json").write_text("not json")
        r = RT.route(self.base, self.fetched, "someone", "write", draft=True)
        self.assertEqual(r["route"], "skipped")
        self.assertFalse(r["evaluate"])
        self.assertIsNone(r["notebook"])


class Paths(TempCase):
    """L03: mixed pull requests and maintainer-only paths are rejected."""

    def setUp(self):
        super().setUp()
        self.make_base()

    def r(self, rows):
        return RT.route(self.base, self.make_fetched(rows), "someone", "write")

    def test_math_only(self):
        r = self.r([("dag/Notes/x.md", "added", b"x"), ("dag/Theorems/Thm_a.lean", "added",
                                                        b"x")])
        self.assertEqual(r["route"], "math")
        self.assertTrue(r["ok"])
        self.assertFalse(r["evaluate"])

    def test_maintainer_paths(self):
        for p in ("ci/learning/route.py", ".github/workflows/learning.yml",
                  "meta/learning.json", "meta/trusted.json", "env/environments.json",
                  "lakefile.toml", "lean-toolchain", "README.md"):
            r = self.r([(p, "modified", b"x")])
            self.assertEqual(r["route"], "rejected", p)
            self.assertIn("maintainer-only", r["problems"][0])

    def test_maintainer_path_with_math(self):
        r = self.r([("dag/Notes/x.md", "added", b"x"), ("meta/learning.json", "modified", b"{}")])
        self.assertEqual(r["route"], "rejected")

    def test_rename_out_of_dag(self):
        r = self.r([("dag/Notes/x.md", "renamed", b"x", {"previous_filename": "ci/x.py"})])
        self.assertEqual(r["route"], "rejected")

    def test_mixed_generator_notebook(self):
        r = self.r(generator_rows() + [("notebooks/design.md", "added", NB_TEXT)])
        self.assertEqual(r["route"], "rejected")
        self.assertIn("only one of", r["problems"][0])

    def test_mixed_math_notebook(self):
        r = self.r([("dag/Notes/x.md", "added", b"x"), ("notebooks/design.md", "added", NB_TEXT)])
        self.assertEqual(r["route"], "rejected")

    def test_notebook_deleted(self):
        r = self.r([("notebooks/design.md", "removed", None)])
        self.assertEqual(r["route"], "rejected")

    def test_two_notebooks(self):
        r = self.r([("notebooks/design.md", "added", NB_TEXT),
                    ("notebooks/cryptanalysis.md", "added", NB_TEXT)])
        self.assertEqual(r["route"], "rejected")

    def test_other_notebook_path(self):
        r = self.r([("notebooks/extra.md", "added", NB_TEXT)])
        self.assertEqual(r["route"], "rejected")

    def test_symlink(self):
        r = self.r([("notebooks/design.md", "added", NB_TEXT,
                     {"type": "blob", "mode": "120000"})])
        self.assertEqual(r["route"], "rejected")
        self.assertIn("symbolic", r["problems"][0])


class Notebook(TempCase):
    """L16: caps, exact bytes and hash, tokenizer recorded."""

    def setUp(self):
        super().setUp()
        self.make_base(notebooks={"design": b"old\n"})

    def r(self, data, status="modified"):
        return RT.route(self.base, self.make_fetched([("notebooks/design.md", status, data)]),
                        "someone", "write")

    def test_valid(self):
        r = self.r(NB_TEXT)
        self.assertEqual(r["route"], "notebook", r["problems"])
        self.assertTrue(r["evaluate"])
        nb = r["notebook"]
        import hashlib
        self.assertEqual(nb["sha256"], "sha256:" + hashlib.sha256(NB_TEXT).hexdigest())
        self.assertEqual(nb["bytes"], len(NB_TEXT))
        self.assertEqual(nb["tokens"], -(-len(NB_TEXT) // 3))
        self.assertEqual(nb["tokenizer"], {"kind": "proxy-bytes-div-3", "version": "1"})
        self.assertEqual(nb["incumbent_bytes"], 4)

    def test_caps(self):
        self.assertEqual(self.r(b"x" * 401)["route"], "rejected")          # bytes
        pol = policy()
        pol["notebooks"]["max_bytes"] = 10000
        self.set_policy(pol)
        r = self.r(b"x" * 301)                                             # 101 tokens
        self.assertEqual(r["route"], "rejected")
        self.assertIn("tokens", r["problems"][0])
        self.assertEqual(self.r(b"x" * 300)["route"], "notebook")

    def test_encoding(self):
        self.assertEqual(self.r(b"\xff\xfe")["route"], "rejected")
        self.assertEqual(self.r(b"a\r\nb")["route"], "rejected")
        self.assertEqual(self.r(b"\xef\xbb\xbfa")["route"], "rejected")

    def test_unchanged(self):
        self.assertEqual(self.r(b"old\n")["route"], "rejected")


class Generator(TempCase):
    """L09 (manifest/policy side): the family policy fixes k and h; versions are immutable."""

    def setUp(self):
        super().setUp()
        self.make_base()

    def r(self, rows, records=None):
        return RT.route(self.base, self.make_fetched(rows), "someone", "write",
                        records=records)

    def test_valid_bootstrap(self):
        r = self.r(generator_rows())
        self.assertEqual(r["route"], "generator", r["problems"])
        g = r["generator"]
        self.assertEqual(g["generate_module"], GEN_NS + ".Generate")
        self.assertEqual(g["entropy_bits"], 8)          # from the policy, not the manifest
        self.assertEqual(g["seed_bits"], 16)
        self.assertEqual(len(g["files"]), 3)
        self.assertFalse(r["evaluate"])

    def assertRejected(self, rows, fragment):
        r = self.r(rows)
        self.assertEqual(r["route"], "rejected", r)
        self.assertTrue(any(fragment in p for p in r["problems"]), r["problems"])

    def test_manifest_cannot_choose_entropy(self):
        m = manifest()
        m["entropy_bits"] = 1
        self.assertRejected(generator_rows(m), "unknown key `entropy_bits`")

    def test_seed_bits_must_match_policy(self):
        self.assertRejected(generator_rows(manifest(seed_bits=8)), "seed_bits")

    def test_levels_capped(self):
        self.assertRejected(generator_rows(manifest(levels=5)), "levels")

    def test_family_must_be_approved(self):
        self.assertRejected(generator_rows(manifest(family_id="fam-x"),
                                           d="generators/design/fam-x/gen1/v0001"),
                            "not approved")

    def test_family_role(self):
        self.assertRejected(generator_rows(manifest(role="cryptanalysis", family_id="fam-a"),
                                           d="generators/cryptanalysis/fam-a/gen1/v0001"),
                            "approved for design")

    def test_family_revision(self):
        self.assertRejected(generator_rows(manifest(family_revision="sha256:" + "2" * 64)),
                            "family_revision")

    def test_path_mismatch(self):
        self.assertRejected(generator_rows(manifest(generator_id="gen2")), "path says")

    def test_version_sequence(self):
        self.assertRejected(generator_rows(manifest(version=2, parent=None),
                                           d="generators/design/fam-a/gen1/v0002"),
                            "next version")
        (self.base / "generators/design/fam-a/gen1/v0001").mkdir(parents=True)
        rows = generator_rows(manifest(version=2, parent={"generator_id": "gen1",
                                                          "version": 1}, bootstrap=...,
                                       source_refs=[]),
                              d="generators/design/fam-a/gen1/v0002")
        self.assertRejected(rows, "source_refs")
        self.assertRejected(generator_rows(manifest(version=2, parent=None),
                                           d="generators/design/fam-a/gen1/v0002"), "parent")

    def test_existing_version_immutable(self):
        (self.base / "generators/design/fam-a/gen1/v0001").mkdir(parents=True)
        self.assertRejected(generator_rows(), "immutable")
        rows = generator_rows()
        rows[1] = (rows[1][0], "modified", rows[1][2])
        self.assertRejected(rows, "immutable")

    def test_extra_or_missing_files(self):
        self.assertRejected(generator_rows()[:2], "exactly manifest.json")
        self.assertRejected(generator_rows() + [("generators/design/fam-a/gen1/v0001/x.lean",
                                                 "added", b"x")], "not a generator file")

    def test_unsafe_identifiers(self):
        self.assertRejected(generator_rows(d="generators/design/fam-a/Gen1/v0001"),
                            "safe identifier")
        self.assertRejected(generator_rows(d="generators/design/fam-a/g--1/v0001"),
                            "safe identifier")

    def test_bootstrap_requires_policy_entry(self):
        pol = policy()
        pol["bootstrap_generators"] = []
        self.set_policy(pol)
        self.assertRejected(generator_rows(), "bootstrap_generators")

    def test_source_refs_need_records(self):
        ref = {"node_id": "theorem:A.b", "commit": "d" * 40, "content_sha256": "sha256:" + "0" * 64}
        self.assertRejected(generator_rows(manifest(bootstrap=..., source_refs=[ref])),
                            "records")
        recs = self.tmp / "records"
        recs.mkdir()
        r = self.r(generator_rows(manifest(bootstrap=..., source_refs=[ref])), recs)
        self.assertTrue(any("not a verified node" in p for p in r["problems"]))

    def test_decl_namespace(self):
        self.assertRejected(generator_rows(manifest(generate_decl="SigabaNeo.foo")),
                            "namespace")

    def test_lean_restrictions(self):
        bad = {
            "import Lean\n": "import Lean",
            "import SigabaNeo.Platform\n": "SigabaNeo.Platform",
            "import Definitions.Def_x\n": "Definitions.Def_x",
            "import Generators.Design.Other.V0001.Generate\n": "Generators",
            "def x := 1\n#eval x\n": "#eval",
            "unsafe def x : Nat := 1\n": "unsafe",
            "@[extern \"c\"] def x : Nat := 1\n": "extern",
            "@[implemented_by y] def x : Nat := 1\n": "implemented_by",
            "run_cmd pure ()\n": "run_cmd",
            "elab \"x\" : term => pure default\n": "elab",
            "macro \"x\" : term => `(1)\n": "macro",
            "syntax \"x\" : term\n": "syntax",
            "initialize pure ()\n": "initialize",
            "set_option debug.skipKernelTC true\n": "debug.skipKernelTC",
            "axiom bad : False\n": "axiom",
            "theorem t : 1 = 1 := by native_decide\n": "native_decide",
            "@[command_elab foo] def x := 1\n": "attribute",
            "local notation \"q\" => 1\n": "notation",
            'def s := "--" #eval 1\n': "#eval",
        }
        for text, frag in bad.items():
            body = text if text.startswith("import") else "import Mathlib\n" + text
            probs = RT.lean_problems(body)
            self.assertTrue(any(frag in p for p in probs), (text, probs))

    def test_lean_allowed(self):
        self.assertEqual(RT.lean_problems(GENERATE), [])
        self.assertEqual(RT.lean_problems(CERTIFICATE, (GEN_NS + ".Generate",)), [])
        ok = ("import Mathlib\n-- #eval in a comment\n/- unsafe /- nested -/ -/\n"
              "@[simp, reducible] def f (x : Nat) : Nat := x\n"
              "attribute [local instance] Nat.instDecidableEqNat\n"
              "set_option maxHeartbeats 400000 in\ntheorem t : f 1 = 1 := rfl\n"
              "def arr := #[1, 2]\ndef c := 'x'\n")
        self.assertEqual(RT.lean_problems(ok), [])

    def test_certificate_cannot_import_other_generators(self):
        probs = RT.lean_problems("import Generators.Design.X.Y.V0001.Generate\n",
                                 (GEN_NS + ".Generate",))
        self.assertTrue(probs)


class PolicyRules(unittest.TestCase):
    """L11 (policy side): h = 0 and h > k are rejected; the shipped policy is valid."""

    def test_entropy_zero(self):
        p = policy(families=[family("f", entropy_bits=0)])
        self.assertTrue(any("entropy_bits" in x for x in POL.problems(p)))

    def test_entropy_above_seed(self):
        p = policy(families=[family("f", entropy_bits=17, seed_bits=16)])
        self.assertTrue(any("0 < h <= seed_bits" in x for x in POL.problems(p)))

    def test_valid(self):
        self.assertEqual(POL.problems(policy()), [])

    def test_shipped_policy(self):
        import pathlib
        root = pathlib.Path(__file__).resolve().parents[3]
        p = POL.load_base(root)
        self.assertFalse(p["evaluator"]["enabled"])

    def test_alpha_and_curriculum(self):
        p = policy()
        p["promotion"]["alpha"] = "0.6"
        p["curriculum"]["lo"] = "0.5"
        probs = POL.problems(p)
        self.assertTrue(any("alpha" in x for x in probs))
        self.assertTrue(any("lo <= target" in x for x in probs))

    def test_bootstrap_entry_needs_bootstrap_family(self):
        p = policy()
        p["bootstrap_generators"] = [{"family_id": "fam-b", "generator_id": "g", "version": 1}]
        self.assertTrue(POL.problems(p))


class FakeApi:
    def __init__(self, files, tree, blobs):
        self.files, self.tree, self.blobs = files, tree, blobs
        self.paths = []

    def __call__(self, path):
        self.paths.append(path)
        if "/compare/" in path:
            return {"files": self.files}
        if "/git/commits/" in path:
            return {"tree": {"sha": "root"}}
        if "/git/trees/" in path:
            sha = path.rsplit("/", 1)[1]
            return {"tree": self.tree[sha]}
        if "/git/blobs/" in path:
            sha = path.rsplit("/", 1)[1]
            return {"encoding": "base64", "content": base64.b64encode(self.blobs[sha]).decode()}
        raise AssertionError(path)


class Fetch(TempCase):
    def test_fetch_learning_files_only(self):
        files = [{"filename": "notebooks/design.md", "status": "modified"},
                 {"filename": "dag/Notes/n.md", "status": "added"},
                 {"filename": "notebooks/link.md", "status": "added"},
                 {"filename": "old.txt", "status": "removed"}]
        tree = {"root": [{"path": "notebooks", "type": "tree", "sha": "nbt"},
                         {"path": "dag", "type": "tree", "sha": "dagt"}],
                "nbt": [{"path": "design.md", "type": "blob", "mode": "100644", "sha": "b1",
                         "size": 4},
                        {"path": "link.md", "type": "blob", "mode": "120000", "sha": "b2",
                         "size": 3}],
                "dagt": [{"path": "Notes", "type": "tree", "sha": "nt"}],
                "nt": [{"path": "n.md", "type": "blob", "mode": "100644", "sha": "b3",
                        "size": 2}]}
        api = FakeApi(files, tree, {"b1": b"new\n", "b2": b"../", "b3": b"hi"})
        out = self.tmp / "f"
        rows = fetch.fetch("o/r", out, "1" * 40, REV, api)
        listing = json.loads((out / "files.json").read_text())
        self.assertEqual(listing["revision"], REV)
        self.assertEqual(len(listing["files"]), 4)
        self.assertEqual((out / "files/notebooks/design.md").read_bytes(), b"new\n")
        self.assertFalse((out / "files/notebooks/link.md").exists())   # symlink: not fetched
        self.assertFalse((out / "files/dag/Notes/n.md").exists())      # not a learning path
        by = {r["filename"]: r for r in rows}
        self.assertEqual(by["notebooks/link.md"]["mode"], "120000")
        self.assertEqual(by["old.txt"]["status"], "removed")
        self.assertFalse(any("/blobs/b3" in p for p in api.paths))
        # The format is exactly what `route` consumes.
        self.make_base(notebooks={"design": b"old\n"})
        r = RT.route(self.base, out, "someone", "write")
        self.assertEqual(r["route"], "rejected")       # mixed (dag + notebooks + root path)

    def test_fetch_rejects_bad_commits(self):
        with self.assertRaises(SystemExit):
            fetch.fetch("o/r", self.tmp / "x", "nope", REV, FakeApi([], {}, {}))


if __name__ == "__main__":
    unittest.main()


class MergeGroups(TempCase):
    """A merge group may combine a mathematical pull request with a learning one: the gate checks
    the nodes, and the learning route sees only the learning files. A pull request itself still
    may not mix them."""

    def test_merge_group_mixing(self):
        import json as _json
        self.make_base(notebooks={"design": b""})
        rows = [("dag/Notes/x.md", "added", b"---\ntitle: x\n---\n"),
                ("notebooks/design.md", "modified", b"a better note\n")]
        f = self.make_fetched(rows)
        r = RT.route(self.base, f, "listed", "write", event="merge_group", pr=1)
        self.assertEqual(r["route"], "notebook", r)
        r = RT.route(self.base, f, "listed", "write", event="pull_request_target", pr=1)
        self.assertEqual(r["route"], "rejected")
