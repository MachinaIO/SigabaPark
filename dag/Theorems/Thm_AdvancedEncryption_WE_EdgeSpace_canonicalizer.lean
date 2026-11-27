import Mathlib

open scoped BigOperators

theorem AdvancedEncryption.WE.EdgeSpace.canonicalizer {X Key : Type} (x₀ : X) (f : X → Bool)
    (canonical : (Bool → Bool → X → Bool) → Key)
    (exactKey : ∀ a b, canonical a = canonical b ↔ ∀ u x, a true u x = b true u x) :
    let g := fun y u x => if y = true then f x else u
    (g false false x₀ ≠ g false true x₀) ∧
    (canonical g = canonical (fun _ _ _ => false) ↔ ∀ x, f x = false) := by sorry
