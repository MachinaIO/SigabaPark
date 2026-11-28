import Definitions.Def_ShortNand

open SigabaNeo ShortNand

theorem solution (q : ℤ) (hq : 5≤q) (n : ℕ) (gs : GateList) :
    ((∃ x : List Bool, x.length=n ∧ evalGates (x,gs)=true) ↔
      ∃ bs, feasible q n gs bs ∧ energy bs = gs.length) ∧
    (∀ bs, feasible q n gs bs →
      (energy bs = gs.length ∧ ∀ t∈bs,hot t) ∨ (gs.length : ℤ)+2 ≤ energy bs) := by
  constructor
  · constructor
    · rintro ⟨x,hx,hw⟩
      obtain ⟨bs,ht,he⟩ := synth q gs (true::x) true hw
      exact ⟨bs,⟨x.map bit,by simp [hx],ht⟩,he⟩
    · rintro ⟨bs,hf,he⟩
      exact (exactFiber q hq n gs).mpr ⟨bs,hf,by omega⟩
  · rintro bs ⟨x,_,ht⟩
    obtain ⟨hl,_,hh⟩ := rowFacts q hq gs bs _ _ ht
    by_cases h : energy bs ≤ (gs.length : ℤ)+1
    · exact Or.inl ⟨by rw [noNext bs (hh h),hl],hh h⟩
    · exact Or.inr (by omega)
