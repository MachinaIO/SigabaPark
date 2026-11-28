"""A deterministic solver for the bootstrap fixture families (ci/learning/providers.py).

It answers only when the notebook names the family's target lemma
(`avoidDesign_target` / `avoidAttack_target`), with a Lean module that applies it to the
descriptor. It is a pipeline test that makes a notebook comparison produce a real,
Lean-verified difference without a model; it is not research and proves nothing about models.
"""

import json
import sys

LEMMAS = {"SigabaNeo.Benchmark.Fixture.avoidDesignFamily": "avoidDesign_target",
          "SigabaNeo.Benchmark.Fixture.avoidAttackFamily": "avoidAttack_target"}


def main() -> int:
    req = json.loads(sys.stdin.read())
    fam = req["family"]
    lemma = LEMMAS.get(fam["lean_family"])
    usage = {"model_calls": 1, "input_tokens": len(req["notebook"]) // 3, "output_tokens": 0}
    if lemma is None or lemma not in req["notebook"]:
        print(json.dumps({"status": "no_answer", "solution": None, "usage": usage,
                          "model": "scripted-fixture-1"}))
        return 0
    bits = req["descriptor_bits"]
    lit = "[" + ", ".join("true" if c == "1" else "false" for c in bits) + "]"
    module = (f"import {fam['lean_module']}\n\nnamespace Answers.Solution\n\n"
              "open SigabaNeo.Benchmark SigabaNeo.Benchmark.Fixture\n\n"
              f"theorem solve : Target {fam['lean_family']} {lit} :=\n"
              f"  {lemma} (by decide) (by simp)\n\nend Answers.Solution\n")
    usage["output_tokens"] = len(module) // 3
    print(json.dumps({"status": "answered", "usage": usage, "model": "scripted-fixture-1",
                      "solution": {"module_text": module,
                                   "theorem": "Answers.Solution.solve"}}))
    return 0


if __name__ == "__main__":
    sys.exit(main())
