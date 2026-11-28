import Definitions.Def_NullSamplerCosts
open OneBitSampler
theorem solution {I S X : Type} [Fintype I] [Fintype S] [DecidableEq I]
    (T : Bool → S → Tree I X) (D : I → X → Bool) (margin : ℤ)
    (hgap : ∀ v, margin ≤ ∑ s,
      ((accept (T true s) (spike v) (D v)-accept (T false s) (spike v) (D v))-
       (accept (T true s) (fun _=>false) (D v)-accept (T false s) (fun _=>false) (D v)))) :
    (Fintype.card I:ℤ)*margin ≤
      ∑ s, ((visited (T true s)).card+(visited (T false s)).card:ℤ) := by
  classical
  have one (v : I) (s : S) :
      ((accept (T true s) (spike v) (D v)-accept (T false s) (spike v) (D v))-
       (accept (T true s) (fun _=>false) (D v)-accept (T false s) (fun _=>false) (D v))) ≤
      (if v∈visited (T true s) then (1:ℤ) else 0)+(if v∈visited (T false s) then (1:ℤ) else 0) := by
    have a:=abs_le.mp (costOnMiss (T true s) v (D v))
    have b:=abs_le.mp (costOnMiss (T false s) v (D v))
    omega
  calc
    _ = ∑ _ : I, margin := by simp
    _ ≤ _ := Finset.sum_le_sum (fun v _ => (hgap v).trans (Finset.sum_le_sum (fun s _ => one v s)))
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s hs
      simp [Finset.sum_add_distrib]
