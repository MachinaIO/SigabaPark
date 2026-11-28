"""`fetch-local`: the post-merge job reads what a merge changed from a local checkout, in the
same format as `fetch` (only learning paths are downloaded; links are not)."""

from __future__ import annotations

import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

from ci.learning import fetch


def git(d, *a):
    return subprocess.run(["git", "-C", str(d), *a], check=True, capture_output=True,
                          text=True).stdout.strip()


class FetchLocal(unittest.TestCase):
    def test_rows_and_downloads(self):
        with tempfile.TemporaryDirectory() as t:
            d = Path(t) / "r"
            env = dict(GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@e", GIT_COMMITTER_NAME="t",
                       GIT_COMMITTER_EMAIL="t@e")
            os.environ.update(env)
            subprocess.run(["git", "init", "-q", "-b", "main", str(d)], check=True)
            (d / "notebooks").mkdir()
            (d / "notebooks" / "design.md").write_text("old\n")
            (d / "README.md").write_text("x\n")
            git(d, "add", "-A")
            git(d, "commit", "-qm", "a")
            base = git(d, "rev-parse", "HEAD")
            (d / "notebooks" / "design.md").write_text("new\n")
            g = d / "generators" / "design" / "fam" / "gen" / "v0001"
            g.mkdir(parents=True)
            (g / "manifest.json").write_text("{}")
            (g / "link.lean").symlink_to("manifest.json")
            (d / "README.md").unlink()
            git(d, "add", "-A")
            git(d, "commit", "-qm", "b")
            head = git(d, "rev-parse", "HEAD")
            out = Path(t) / "out"
            rows = {r["filename"]: r for r in fetch.fetch_local(d, base, head, out)}
            self.assertEqual(rows["notebooks/design.md"]["status"], "modified")
            self.assertEqual(rows["README.md"]["status"], "removed")
            self.assertEqual((out / "files" / "notebooks/design.md").read_text(), "new\n")
            self.assertTrue((out / "files" / "generators/design/fam/gen/v0001/manifest.json")
                            .is_file())
            self.assertEqual(rows["generators/design/fam/gen/v0001/link.lean"]["mode"], "120000")
            self.assertFalse((out / "files" / "generators/design/fam/gen/v0001/link.lean")
                             .exists())
            self.assertEqual(json.loads((out / "files.json").read_text())["revision"], head)


if __name__ == "__main__":
    unittest.main()


class SplitVersions(unittest.TestCase):
    """A push may land several generator versions (and nodes): one listing per version."""

    def test_split(self):
        with tempfile.TemporaryDirectory() as t:
            f = Path(t) / "merged"
            rows = []
            for d in ("generators/design/a/g/v0001", "generators/cryptanalysis/b/g/v0001"):
                for n in ("manifest.json", "Generate.lean", "Certificate.lean"):
                    p = f / "files" / d / n
                    p.parent.mkdir(parents=True, exist_ok=True)
                    p.write_text(n)
                    rows.append({"filename": f"{d}/{n}", "status": "added", "type": "blob",
                                 "mode": "100644", "size": len(n)})
            rows.append({"filename": "dag/Notes/x.md", "status": "added", "type": "blob",
                         "mode": "100644", "size": 1})
            (f / "files.json").write_text(json.dumps({"revision": "a" * 40, "files": rows}))
            out = fetch.split_versions(f, Path(t) / "split")
            self.assertEqual([o["version_dir"] for o in out],
                             ["generators/cryptanalysis/b/g/v0001", "generators/design/a/g/v0001"])
            for o in out:
                listing = json.loads((Path(o["dir"]) / "files.json").read_text())
                self.assertEqual(len(listing["files"]), 3)
                self.assertTrue(all(r["filename"].startswith(o["version_dir"])
                                    for r in listing["files"]))
                self.assertTrue((Path(o["dir"]) / "files" / o["version_dir"] /
                                 "manifest.json").is_file())
