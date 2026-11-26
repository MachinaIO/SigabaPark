import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.Group.Basic

/-- Noiseless non-commutative composition (Kilian randomization of a matrix branching program, `GL_n` or any group) telescopes on **every** word `c`, consistent with one input or not: `Π_j p_j⁻¹ M_j(c_j) p_{j+1} = p_0⁻¹ (Π_j M_j(c_j)) p_L`. With exact (noiseless) data, linear-action / tensor-isomorphism encodings of a branching program therefore give the adversary the bookended BP value on all mixed inputs, and equal states get canonical labels, so a forward search with deduplication decides mixed reachability. Used in the note `pq-we-non-lattice-ggh15-analogues`. -/
theorem AdvancedEncryption.WE.NonLattice.kilian_mixed_telescope {G : Type*} [Group G] (L : ℕ) (p : Fin (L + 1) → G) (M : Fin L → Bool → G)
    (c : Fin L → Bool) :
    (List.ofFn fun j : Fin L => (p j.castSucc)⁻¹ * M j (c j) * p j.succ).prod
      = (p 0)⁻¹ * (List.ofFn fun j : Fin L => M j (c j)).prod * p (Fin.last L) := by sorry
