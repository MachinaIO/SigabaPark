import Mathlib

namespace ResidualCube
variable {G : Type} [AddCommGroup G]

def alt : ℕ → (List Bool → G) → G
  | 0, f => f []
  | n+1, f => alt n (fun xs => f (true::xs)) - alt n (fun xs => f (false::xs))

theorem congr_len (n : ℕ) {f g : List Bool → G}
    (h : ∀ x, x.length = n → f x = g x) : alt n f = alt n g := by
  induction n generalizing f g with
  | zero => exact h [] rfl
  | succ n ih =>
    apply congrArg₂ (·-·)
    · apply ih
      intro x hx
      apply h
      simp [hx]
    · apply ih
      intro x hx
      apply h
      simp [hx]
end ResidualCube
