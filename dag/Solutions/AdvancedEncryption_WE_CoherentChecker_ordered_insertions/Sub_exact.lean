import Definitions.Def_CoherentCheckerExpansion
open CoherentCheckerExpansion

theorem solution {R : Type} [Ring R] (l : List (R × R)) :
    actual l - zeros l = (singles l).sum + (pairs l).sum ∧
    (singles l).length = l.length ∧ (pairs l).length = l.length.choose 2 := by
  induction l with
  | nil => simp [actual,zeros,singles,pairs]
  | cons x l ih =>
    obtain ⟨he,hs,hp⟩ := ih
    constructor
    · simp only [actual,zeros,singles,pairs,List.sum_cons,List.sum_append,sum_left,mixed_sum]
      rw [show actual l = zeros l + ((singles l).sum+(pairs l).sum) by rw [← he]; noncomm_ring]
      noncomm_ring
    · simp [singles,pairs,hs,hp,mixed_count,Nat.choose_succ_succ,add_comm]
