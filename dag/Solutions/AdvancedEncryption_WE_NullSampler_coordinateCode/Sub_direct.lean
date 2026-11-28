import Definitions.Def_NullSamplerCosts
open OneBitSampler
theorem solution (n k : Nat) (enc : (Fin n→Bool) → Fin (2^k))
    (dec : Fin (2^k) → Fin n→Bool) :
    2^n ≤ 2^k + ∑ x : Fin n→Bool, ∑ i : Fin n, if dec (enc x) i=x i then 0 else 1 := by
  classical
  let good:=Finset.univ.filter (fun x : Fin n→Bool => dec (enc x)=x)
  have hg : good.card ≤ 2^k := by
    suffices HH : good.card≤(Finset.univ : Finset (Fin (2^k))).card by simpa using HH
    apply Finset.card_le_card_of_injOn enc (fun _ _=>Finset.mem_univ _)
    intro x hx y hy h
    have h₁ : dec (enc x)=x := (Finset.mem_filter.mp hx).2
    have h₂ : dec (enc y)=y := (Finset.mem_filter.mp hy).2
    rw [←h₁,←h₂,h]
  let error:=fun x : Fin n→Bool => ∑ i : Fin n, if dec (enc x) i=x i then 0 else 1
  have each (x : Fin n→Bool) : 1 ≤ (if x∈good then 1 else 0)+error x := by
    by_cases hx:x∈good
    · simp [hx]
    · simp only [hx,ite_false,zero_add]
      have hne : ¬ (∀ i,dec (enc x) i=x i) := by
        intro hh;apply hx; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,funext hh⟩
      obtain ⟨i,hi⟩:=Classical.not_forall.mp hne
      calc
        1 = (if dec (enc x) i=x i then 0 else 1) := by simp [hi]
        _ ≤ error x := Finset.single_le_sum (f:=fun j => if dec (enc x) j=x j then 0 else 1)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hsum:=Finset.sum_le_sum (s:=Finset.univ) (fun x _=>each x)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fun,
    Fintype.card_bool,Fintype.card_fin,smul_eq_mul,mul_one,Finset.sum_boole] at hsum
  simpa [error] using hsum.trans (Nat.add_le_add_right (by simpa using hg : (Finset.univ.filter (fun x=>x∈good)).card≤2^k) _)
