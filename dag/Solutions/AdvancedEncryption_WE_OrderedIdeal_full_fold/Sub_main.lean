import Definitions.Def_OrderedNand

open OrderedNand SigabaNeo

theorem solution (gs : GateList) (x : List Bool) (b : Bool) :
    (compiled (true::x).length gs).foldl estep (true::x,b) = gs.foldl estep (true::x,b) := by
  have reading (xs : List Bool) (i : Nat) :
      val (true::xs) (OrderedNand.norm (true::xs).length i) = val (true::xs) i := by
    by_cases h : i < (true::xs).length
    · simp only [OrderedNand.norm,if_pos h]
    · simp only [OrderedNand.norm,if_neg h]
      change true = (true::xs).getD i true
      exact (List.getD_eq_default _ _ (Nat.le_of_not_gt h)).symm
  have local_eq (x : List Bool) (b : Bool) (g : Nat × Nat) :
      estep (true::x,b) (physical (true::x).length g) = estep (true::x,b) g := by
    let l := OrderedNand.norm (true::x).length g.1
    let r := OrderedNand.norm (true::x).length g.2
    apply congrArg (fun v : Bool => ((true::x) ++ [!v], !v))
      (show (val (true::x) (min l r) && val (true::x) (max l r)) =
          (val (true::x) g.1 && val (true::x) g.2) from ?_)
    by_cases hr : l ≤ r
    · simp only [min_eq_left hr, max_eq_right hr, l, r, reading]
    · have hr' := Nat.le_of_lt (Nat.lt_of_not_ge hr)
      simp only [min_eq_right hr', max_eq_left hr',l,r,reading,Bool.and_comm]

  induction gs generalizing x b with
  | nil => rfl
  | cons g gs ih =>
    simp only [compiled,List.foldl_cons,local_eq]
    let z := !(val (true::x) g.1 && val (true::x) g.2)
    change (compiled ((true::x).length+1) gs).foldl estep (true::(x++[z]),z) =
      gs.foldl estep (true::(x++[z]),z)
    simpa using ih (x++[z]) z
