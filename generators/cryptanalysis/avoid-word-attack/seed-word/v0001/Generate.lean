import SigabaNeoStd.Benchmarks.Families.AvoidWordAttack

/-!
# Bootstrap generator: "avoid a word" (cryptanalysis), one level

A maintainer-approved BOOTSTRAP generator for the pilot of the learning extension, not a research
benchmark. At seed r the task is the search problem of outputting anything but the word 1 r, with
an explicit machine of cost at most 2^5 times its gain (strictly below the claimed 6 bits).
-/

namespace Generators.Cryptanalysis.AvoidWordAttack.SeedWord.V0001

open SigabaNeo.Benchmark SigabaNeo.Benchmark.Fixture

/-- The generator. -/
def generate (_ : Fin 1) (r : Seed 8) : Word :=
  ⟨true :: List.ofFn r, by simp [Word.maxLen]⟩

end Generators.Cryptanalysis.AvoidWordAttack.SeedWord.V0001
