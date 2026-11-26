import Mathlib

theorem AdvancedEncryption.WE.Separator.template901_counts (a t : ℕ) (ha : 1 ≤ a) (ht : t ≤ 454*a) :
    let c := fun (h m : ℕ) => 2*m*(1+t) + 2*(h-2)*m^2
    let d := fun (h m : ℕ) => (h-2)*m^2 + m*t
    let p := fun (h m : ℕ) => 2*((h-2)*m + t)
    4*c 387 (454*a) < c 1551 (456*a) ∧
    4*d 387 (454*a) < d 1551 (456*a) ∧
    4*p 387 (454*a) < p 1551 (456*a) := by sorry
