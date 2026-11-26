import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Abel

/-- Abelian (commutative) path labels collapse. For an oblivious (width-one, state-free) branching program over an abelian group `G` (a class group acting on curves, in exponent notation) the path label `P(v) = Σ_j f_j(v_{var j})` satisfies the rectangle identity `P(00) + P(11) = P(01) + P(10)` in any two positions, whatever the reading order and the number of reads; equivalently `P` is affine in the witness bits. Commutativity therefore turns mix-and-match into an exact identity and reduces gating to an affine predicate, which `AdvancedEncryption.WE.Direct.nand_gadget_affine_closure` breaks. Used in the note `pq-we-non-lattice-ggh15-analogues`. -/
theorem AdvancedEncryption.WE.NonLattice.abelian_path_rectangle {G : Type*} [AddCommGroup G] {L n : ℕ}
    (var : Fin L → Fin n) (f : Fin L → Bool → G) (w : Fin n → Bool) (i k : Fin n) (hik : i ≠ k) :
    (∑ j, f j (Function.update (Function.update w i false) k false (var j))) +
      ∑ j, f j (Function.update (Function.update w i true) k true (var j))
    = (∑ j, f j (Function.update (Function.update w i false) k true (var j))) +
      ∑ j, f j (Function.update (Function.update w i true) k false (var j)) := by sorry
