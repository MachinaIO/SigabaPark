import Mathlib

theorem AdvancedEncryption.WE.SourcePads.bank_injective {I F : Type} [Field F] (g : F → F) (hg : Function.Injective g)
    (a c : I → F) (ha : ∀ i, a i ≠ 0) :
    Function.Injective (fun t : I → F => fun i => c i + a i * g (t i)) := by sorry
