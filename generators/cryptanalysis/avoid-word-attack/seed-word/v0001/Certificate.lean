import SigabaNeoStd.Benchmarks.Entropy
import Generators.Cryptanalysis.AvoidWordAttack.SeedWord.V0001.Generate

/-! The universal certificate: every seed is solvable (gain 1, cost 30 ≤ 2^5, strict against
6 bits) and equal gains force equal seeds (8 bits of diversity out of 8). -/

namespace Generators.Cryptanalysis.AvoidWordAttack.SeedWord.V0001

open SigabaNeo.Benchmark SigabaNeo.Benchmark.Fixture

theorem certified : Certified avoidAttackFamily 1 8 8 generate :=
  certified_of_injective (by norm_num)
    (fun _ _ => avoidAttack_solvable (by simp [generate]))
    (fun _ _ _ h => List.ofFn_injective
      (List.cons.inj (congrArg Word.bits (avoidAttack_sameProblem h))).2)

end Generators.Cryptanalysis.AvoidWordAttack.SeedWord.V0001
