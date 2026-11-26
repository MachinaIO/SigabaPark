module

public import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnQRPotential

set_option autoImplicit true

@[expose] public section

namespace SigabaNeo.Rogers

theorem columnCandidate_of_qr_and_multiplier {n : ℕ} (x : SL n)
    (k r : Matrix (Fin n) (Fin n) ℝ) (hk : k.transpose * k = 1) (hx : x.val = k * r)
    (γ : Matrix.SpecialLinearGroup (Fin n) ℤ)
    (s : Matrix (Fin n) (Fin n) ℝ)
    (hs : s = r * (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ).val)
    (hp : ∀ i, 0 < s i i) (ht : ∀ i j, j < i → s i j = 0)
    (hr : ∀ i j, i < j → |s i j| ≤ s i i / 2) : Nonempty (ColumnCandidate x) := by
  refine ⟨⟨γ, k, s, hk, ?_, hp, ht, hr⟩⟩
  change x.val * _ = k * s
  rw [hx, hs, Matrix.mul_assoc]

theorem columnSublevel_finite_of_entry_bound {n : ℕ} {x : SL n} (a : ColumnCandidate x)
    (B : ℤ) (bound : ∀ c : ColumnCandidate x, c.potential ≤ a.potential →
      ∀ i j, |c.γ.val i j| ≤ B)
    (unique : ∀ c b : ColumnCandidate x, c.γ = b.γ → c.potential = b.potential) :
    {v : ℝ | ∃ c : ColumnCandidate x, c.potential = v ∧ v ≤ a.potential}.Finite := by
  classical
  let box := Fin n → Fin n → Set.Icc (-B) B
  let encode (c : ColumnCandidate x) (h : c.potential ≤ a.potential) : box :=
    fun i j ↦ ⟨c.γ.val i j, abs_le.mp (bound c h i j)⟩
  let decode (m : box) : ℝ :=
    if h : ∃ c : ColumnCandidate x, ∀ i j, c.γ.val i j = (m i j).val then
      h.choose.potential else 0
  apply (Set.finite_range decode).subset
  rintro v ⟨c, rfl, hc⟩
  refine ⟨encode c hc, ?_⟩
  have h : ∃ b : ColumnCandidate x, ∀ i j, b.γ.val i j = ((encode c hc) i j).val :=
    ⟨c, fun _ _ ↦ rfl⟩
  simp only [decode, dite_eq_left h]
  apply unique
  apply Subtype.ext
  exact Matrix.ext h.choose_spec

end SigabaNeo.Rogers
