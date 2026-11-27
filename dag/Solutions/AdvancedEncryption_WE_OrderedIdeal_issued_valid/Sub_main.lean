import Definitions.Def_OrderedNand
import Theorems.Thm_AdvancedEncryption_WE_OrderedIdeal_row_exact

open OrderedNand SigabaNeo

theorem solution (gs : GateList) (x : List Bool) (last : Bool) (p q y : Key)
    (mem : issued (true::x).length gs p q y) :
    let v := val (gs.foldl estep (true::x,last)).1
    live v p → live v q → live v y := by
  have suffix (gates : GateList) (state : List Bool × Bool) :
      ∃ tail, (gates.foldl estep state).1 = state.1 ++ tail := by
    induction gates generalizing state with
    | nil => exact ⟨[], by simp⟩
    | cons gate rest ih =>
      obtain ⟨tail,hh⟩ := ih (estep state gate)
      exact ⟨_::tail, by simpa [estep,List.append_assoc] using hh⟩
  induction gs generalizing x last with
  | nil => exact False.elim mem
  | cons g gs ih =>
    let v := val (true::x)
    let d := (true::x).length
    let b := !(v g.1 && v g.2)
    let x' := x ++ [b]
    let out := (gs.foldl estep (true::x',b)).1
    change live (val out) p → live (val out) q → live (val out) y
    rcases mem with here | later
    · obtain ⟨tail, ht⟩ := suffix gs (true::x',b)
      change out = (true::x) ++ [b] ++ tail at ht
      have prev (i : Nat) (hi : i < d) : val out i = v i := by
        dsimp [val,v];rw [ht,List.getD_append _ _ _ _ (by simp; dsimp [d] at hi;omega),List.getD_append _ _ _ _ hi]
      have dest : val out d = b := by
        dsimp [val]; rw [ht,List.append_assoc,List.getD_append_right _ _ _ _ (by rfl)]
        simp [d]
      have less (i : Nat) : OrderedNand.norm d i < d := by
        unfold OrderedNand.norm;split <;> simp_all [d]
      have equiv (i : Nat) : v (OrderedNand.norm d i) = v i := by
        by_cases h : i < d
        · simp only [OrderedNand.norm,if_pos h]
        · simp only [OrderedNand.norm,if_neg h]
          exact (List.getD_eq_default _ _ (Nat.le_of_not_gt h)).symm
      let l := OrderedNand.norm d g.1
      let r := OrderedNand.norm d g.2
      have lo : min l r < d := lt_of_le_of_lt (min_le_left _ _) (less g.1)
      have hi : max l r < d := max_lt (less g.1) (less g.2)
      have vv : (val out (min l r) && val out (max l r)) = (v g.1 && v g.2) := by
        rw [prev _ lo,prev _ hi]
        by_cases h : l ≤ r
        · simp only [min_eq_left h,max_eq_right h,l,r,equiv]
        · have h' := Nat.le_of_lt (Nat.lt_of_not_ge h)
          simp only [min_eq_right h',max_eq_left h',l,r,equiv,Bool.and_comm]
      intro hp hq
      have h0 : val out 0 = true := by rw [prev 0 (by simp [d])];rfl
      have hy := (AdvancedEncryption.WE.OrderedIdeal.row_exact (val out) h0 d (min l r) (max l r) y).mp ⟨p,q,here,hp,hq⟩
      rw [hy]; change val out d = !(val out (min l r) && val out (max l r))
      rw [dest,vv]
    · apply ih x' b
      simpa [x',d] using later
