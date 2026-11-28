import Definitions.Def_ProjectiveJoin
open ProjectiveJoin
theorem solution {F K V : Type} [Field F] [DecidableEq F] [Field K]
    [AddCommGroup V] [Module K V] (d : Nat) (points : Finset (Option F))
    (target : V) (ranges : Option F → Submodule K V)
    (positive : Finset (Module.Dual K V)) (poly : Module.Dual K V → Polynomial F)
    (listAll : ∀ f : Module.Dual K V, f target ≠ 0 → f ∈ positive)
    (degree : ∀ f ∈ positive, (poly f).natDegree≤d)
    (nonzero : ∀ f ∈ positive, poly f ≠ 0)
    (sound : ∀ x ∈ points, ∀ f ∈ positive,
        f ∈ (ranges x).dualAnnihilator → atPoint d (poly f) x=0)
    (budget : positive.card*d<points.card) :
    ∃ x ∈ points, target ∈ ranges x := by
  classical
  have hb (f) (hf : f∈positive) : (bad d (poly f)).card≤d := by
    have base:=((poly f).roots.toFinset_card_le).trans (Polynomial.card_roots' (poly f))
    by_cases h:(poly f).natDegree<d
    · simp [bad,h,Finset.card_insert_of_notMem]; omega
    · simp [bad,h]; exact base.trans (degree f hf)
  have hu : (positive.biUnion (fun f=>bad d (poly f))).card≤positive.card*d := by
    refine Finset.card_biUnion_le.trans ?_
    calc
      _ ≤ ∑ f ∈ positive,d := Finset.sum_le_sum hb
      _ = _ := by simp
  obtain ⟨x,hx,hfree⟩:=Finset.exists_mem_notMem_of_card_lt_card (hu.trans_lt budget)
  use x,hx
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff (ranges x) target).mp
  intro f hf
  by_contra h
  have hp:=listAll f h
  apply hfree
  apply Finset.mem_biUnion.mpr
  use f,hp
  have he:=sound x hx f hp hf
  have hn:=nonzero f hp
  cases x with
  | none =>
    change (poly f).coeff d=0 at he
    have hl : (poly f).natDegree<d := by
      have hd:=degree f hp
      by_contra! hge
      have eq:(poly f).natDegree=d := by omega
      rw [←eq,Polynomial.coeff_natDegree] at he
      exact (Polynomial.leadingCoeff_ne_zero.mpr hn) he
    simp [bad,hl]
  | some x =>
    have hm : x∈(poly f).roots.toFinset := by
      simpa [Polynomial.mem_roots hn,Polynomial.IsRoot,atPoint] using he
    by_cases hl:(poly f).natDegree<d <;> simp [bad,hl,hm]
