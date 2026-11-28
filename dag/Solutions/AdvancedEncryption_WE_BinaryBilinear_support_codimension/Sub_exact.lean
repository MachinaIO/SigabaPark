import Mathlib

theorem solution {I Q : Type} [AddCommGroup Q] [Module (ZMod 2) Q] [Fintype Q]
    (s : Finset I) (odd : Odd s.card) (v : I → Q) (hn : ∀ i ∈ s, v i ≠ 0)
    (hz : ∑ i ∈ s, v i = 0) : 2 ≤ Module.finrank (ZMod 2) Q := by
  classical
  by_contra! h
  have hc : Fintype.card Q ≤ 2 := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
    have := Nat.pow_le_pow_right (by decide : 0 < 2) (show Module.finrank (ZMod 2) Q ≤ 1 by omega)
    simpa using this
  obtain ⟨j,hj⟩ : s.Nonempty := by
    by_contra! he
    simp [he] at odd
  have hn0 := hn j hj
  have eqs : ∀ i ∈ s, v i = v j := by
    intro i hi
    by_contra ne
    have bound := Finset.card_le_card (Finset.subset_univ ({0,v j,v i} : Finset Q))
    have a := hn i hi
    simp [a,hn0,Ne.symm a,Ne.symm hn0,ne,Ne.symm ne] at bound
    omega
  rw [Finset.sum_congr rfl eqs,Finset.sum_const] at hz
  obtain ⟨t,ht⟩ := odd
  have htwo : (2:ℕ) • v j = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
    change ((2 : ZMod 2) • v j) = 0
    rw [show (2 : ZMod 2) = 0 by decide, zero_smul]
  rw [ht,add_nsmul,mul_nsmul,htwo,smul_zero,one_nsmul,zero_add] at hz
  exact hn0 hz
