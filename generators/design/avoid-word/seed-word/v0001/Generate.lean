import SigabaNeoStd.Benchmarks.Families.AvoidWordDesign

/-!
# Bootstrap generator: "avoid a word" (design), two levels

A maintainer-approved BOOTSTRAP generator for the pilot of the learning extension, not a research
benchmark (its family is a tiny fixture of the core's SigabaNeoStd.Benchmarks.Families). At level
d and seed r the task is the word 0^d 1 r: implement an algorithm whose output is never that word,
at cost at most the family's cap.
-/

namespace Generators.Design.AvoidWord.SeedWord.V0001

open SigabaNeo.Benchmark SigabaNeo.Benchmark.Fixture

/-- The word of level `d` and seed `r`. -/
def word (d : ℕ) (r : Seed 8) : List Bool := List.replicate d false ++ true :: List.ofFn r

theorem word_length (d : ℕ) (r : Seed 8) : (word d r).length = d + 9 := by
  simp [word]

/-- The generator. -/
def generate (d : Fin 2) (r : Seed 8) : Word :=
  ⟨word d r, by rw [word_length]; unfold Word.maxLen; omega⟩

end Generators.Design.AvoidWord.SeedWord.V0001
