import SigabaNeoStd.Benchmarks.Entropy
import Generators.Design.AvoidWord.SeedWord.V0001.Generate

/-! The universal certificate of the bootstrap generator: every level and seed is solvable, and
equal problems force equal seeds (8 bits of diversity out of 8). -/

namespace Generators.Design.AvoidWord.SeedWord.V0001

open SigabaNeo.Benchmark SigabaNeo.Benchmark.Fixture

theorem word_injective {d : ℕ} {r s : Seed 8} (h : word d r = word d s) : r = s :=
  List.ofFn_injective (List.cons.inj (List.append_cancel_left h)).2

theorem certified : Certified avoidDesignFamily 2 8 8 generate :=
  certified_of_injective (by norm_num)
    (fun d r => avoidDesign_solvable (by simp [generate, word]))
    (fun _ _ _ h => word_injective (congrArg Word.bits (avoidDesign_sameProblem h)))

end Generators.Design.AvoidWord.SeedWord.V0001
