import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.LinearCombination

/-- Canonical labels plus scalar multiplication make a hidden-subgroup instance. If a structure
assigns to every hidden value `z` of a commutative ring a canonical label `F z` (an injective map,
as with the handles of a prime-order group or the invariant of a cryptographic invariant map),
and lets anyone compute the label of `x + y * s` for known `x, y` and a hidden `s` (addition and
multiplication by arbitrary known scalars, as in the Hair--Sahai decryption test), then the
function `(x, y) ↦ F (x + y * s)` is constant exactly on the cosets of the subgroup
`L_s = {(a, b) | a + b * s = 0}`, and `L_s` determines `s`. Over `ZMod p` this is the abelian
hidden-subgroup problem on `(ZMod p)²` that Shor's algorithm solves in quantum polynomial time.
Used in the note `pq-we-exotic-algebraic-structures`. -/
theorem AdvancedEncryption.WE.Exotic.canonical_linear_test_hsp {R S : Type*} [CommRing R]
    (F : R → S) (hF : Function.Injective F) (s : R) :
    (∀ x y x' y' : R, F (x + y * s) = F (x' + y' * s) ↔ (x - x') + (y - y') * s = 0) ∧
    (∀ t : R, (∀ a b : R, a + b * s = 0 ↔ a + b * t = 0) → s = t) := by sorry
