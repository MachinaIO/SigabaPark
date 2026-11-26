import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.LinearCombination
open Matrix

/-- Equivalence encodings carry the MinRank instance in the clear. If a matrix space with basis
`M_j` is published under a hidden equivalence `M ↦ A * M * B` (`A`, `B` invertible: matrix code
equivalence, and the slice view of tensor isomorphism and of lattice isomorphism with `B = Aᵀ`),
then every linear combination of the published matrices has the same rank as the same combination
of the `M_j`. So any rank-based (MinRank / rank-gap) test on the encoding is the same test on the
statement's own space, and hiding `A, B` adds nothing to it. Used in the note
`pq-we-exotic-algebraic-structures`. -/
theorem AdvancedEncryption.WE.Exotic.rank_equiv_combination {K : Type*} [Field K] {m n k : ℕ}
    (A : Matrix (Fin m) (Fin m) K) (B : Matrix (Fin n) (Fin n) K) (hA : IsUnit A.det)
    (hB : IsUnit B.det) (M : Fin k → Matrix (Fin m) (Fin n) K) (a : Fin k → K) :
    (∑ j, a j • (A * M j * B)).rank = (∑ j, a j • M j).rank := by sorry
