import SigabaNeoStd.Lattices.BoxSampler
import SigabaNeoStd.Lattices.LeftoverHash
import SigabaNeoStd.Lattices.Homomorphic.Eval
import CslibFrontier.Probability.Product
import SigabaNeoStd.Lattices.Boxes
import SigabaNeoStd.Lattices.Homomorphic.NoiseBound
import Definitions.Def_WE_EncryptorSetup

open Matrix SigabaNeo.Lattices Cslib Cslib.Probability AdvancedEncryption.WE.Assumptions.SuccinctLWE
  AdvancedEncryption.WE.EncryptorSetup
open scoped ENNReal

/-- **A `ℤ_q` gadget for the leaf lemma**: `G = gadget n k q` (the `G` of `Def_SuccinctLWE`) with
binary decompositions (`G⁻¹` and `dec`) whose entries are at most `1`, whenever `q ≤ 2^k`. -/
theorem AdvancedEncryption.WE.LeafView.succ_gadget_exists (n k q : ℕ) [NeZero q] (hq : q ≤ 2 ^ k) :
    ∃ Γ : GadgetMatrix (ZMod q) (Fin n) (Fin (n * k)),
      Γ.G = AdvancedEncryption.WE.Assumptions.SuccinctLWE.gadget n k q ∧
      (∀ A c c', zabs (Γ.ginv A c c') ≤ 1) ∧
      ∃ dec : (Fin n → ZMod q) → (Fin (n * k) → ZMod q),
        (∀ y, Γ.G *ᵥ dec y = y) ∧ ∀ y c, zabs (dec y c) ≤ 1 := by sorry
