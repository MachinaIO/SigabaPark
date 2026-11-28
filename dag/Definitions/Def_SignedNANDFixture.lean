import Mathlib.Tactic

set_option maxRecDepth 16000
namespace SignedNANDFixture

/-- On the circuit with all gates reading wire zero twice, a gate has no
fanout, and both of its reads use the least-significant wire place. -/
def base (L : Int) (j : Nat) := 1+L*(2:Int)^j
def gateValue (u v : Int) (replacement : Bool) :=
  if replacement then -u+(u+v)+(u+v) else u+2*v
theorem identical (u v : Int) (b : Bool) : gateValue u v b=u+2*v := by
  cases b <;> simp [gateValue] <;> ring

def bases (L : Int) (n : Nat) := ∑ j ∈ Finset.range n,base L j
theorem sum_bases (L : Int) (n : Nat) : bases L n=(n:Int)+L*(2^n-1) := by
  induction n with
  | zero => simp [bases]
  | succ n ih =>
    simp only [bases,Finset.sum_range_succ] at ih ⊢
    rw [ih]; simp only [base,Nat.cast_succ,pow_succ]; ring

/-- The dedicated constant row carries the translation by minus 8192 wire
units. The first 129 base terms include that row and 128 input choices. -/
def ledger (L v : Int) (mask : Fin 4095 → Bool) :=
  bases L 4225-8192*v+
  (∑ i : Fin 4095, (gateValue (base L (129+i.val)) v (mask i)-base L (129+i.val)))+
  (gateValue (base L 4224) v true-base L 4224)

theorem all_masks (L v : Int) (mask : Fin 4095 → Bool) :
    ledger L v mask=4225+L*(2^4225-1) := by
  unfold ledger
  simp_rw [identical,add_sub_cancel_left]
  rw [sum_bases]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  norm_num <;> ring

def four (b : Bool) : List Int := if b then [-1,1,1,0] else [0,0,0,1]
def squared (l : List Int) := (l.map (fun x ↦ x*x)).sum
theorem four_sq (b : Bool) : squared (four b)=1+2*(if b then 1 else 0) := by cases b <;> decide
theorem fours (mask : List Bool) :
    squared (mask.flatMap four)=(mask.length:Int)+2*(mask.count true:Int) := by
  induction mask with
  | nil => rfl
  | cons b mask ih =>
    change squared (four b++mask.flatMap four)=_
    have ha (a c : List Int) : squared (a++c)=squared a+squared c := by simp [squared]
    rw [ha,four_sq,ih]
    cases b <;> simp <;> ring

def coords (mask : List Bool) : List Int :=
  [1]++(List.replicate 128 [1,0]).flatten++mask.flatMap four++[-1,1,1]

theorem full_sq (mask : List Bool) (h : mask.length=4095) :
    squared (coords mask)=4225+2*(1+(mask.count true:Int)) := by
  have ha (a c : List Int) : squared (a++c)=squared a+squared c := by simp [squared]
  have a : squared ([1]++(List.replicate 128 [1,0]).flatten)=129 := by decide
  have b : squared [-1,1,1]=3 := by decide
  unfold coords
  rw [ha,ha,a,b,fours,h]; norm_num; ring

end SignedNANDFixture
