import Mathlib.Data.Nat.Basic

theorem solution (m j s e k h : ℕ) (hs : s ≤ e) (hk : s ≤ k) :
    (∃ first middle left right : ℕ,
      first + middle + left + right = m ∧ first ≤ e ∧ middle ≤ j * (e-s) ∧
      s + left ≤ k ∧ right ≤ h) ↔ m + (j+1)*s ≤ (j+1)*e + k + h := by
  have heq : j * e = j * (e - s) + j * s := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hs]
  simp only [Nat.add_mul, Nat.one_mul]
  constructor
  · rintro ⟨first,middle,left,right,hm,hf,hm',hl,hr⟩
    omega
  · intro hm
    let f := min m e
    let u := min (m-f) (j*(e-s))
    let l := min (m-f-u) (k-s)
    refine ⟨f,u,l,m-f-u-l,?_⟩
    dsimp [f,u,l]
    omega
