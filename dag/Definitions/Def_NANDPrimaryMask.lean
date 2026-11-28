import Definitions.Def_NANDCanonicalBank
import Mathlib.Data.Finset.Max

namespace NANDPrimaryMask
open NANDCanonicalBank SigabaNeo
noncomputable section

/-- Extensional equality of square-free Boolean coefficient tables is literal equality.
An inclusion-minimal monomial in the difference supplies a separating assignment. -/
theorem eval_injective (p : Poly) (h : ∀ u, eval u p=0) : p=0 := by
  classical
  by_contra hp
  obtain ⟨m,hm,hmin⟩ := p.support.exists_min_image Finset.card (Finsupp.support_nonempty_iff.mpr hp)
  let u (i : Nat) : Bool := decide (i ∈ m)
  have char (s : Mon) : mv u s = if s ⊆ m then 1 else 0 := by
    simp only [mv,u,decide_eq_true_eq]
    rfl
  have he := h u
  change p.sum (fun i a ↦ a • mv u i) = 0 at he
  rw [Finsupp.sum,Finset.sum_eq_single m] at he
  · have hx : p m=0 := by simpa [char] using he
    exact (Finsupp.mem_support_iff.mp hm) hx
  · intro s hs hne
    have hn : ¬s⊆m := fun hsm ↦ hne (Finset.eq_of_subset_of_card_le hsm (hmin s hs))
    simp [char,hn]
  · exact fun hn ↦ (hn hm).elim

def shift (m : Mon) := Finsupp.linearCombination F (fun n : Mon ↦ term (m ∪ n))
def times (p q : Poly) : Poly := Finsupp.linearCombination F (fun m : Mon ↦ shift m q) p

theorem eval_single (u : Nat → Bool) (n : Mon) (v : F) : eval u (Finsupp.single n v)=v*mv u n := by simp [eval]

theorem eval_shift (u : Nat → Bool) (m : Mon) (q : Poly) :
    eval u (shift m q) = mv u m * eval u q := by
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha,hb,mul_add]
  | single n v => simp only [shift,Finsupp.linearCombination_single,map_smul,eval_term,mv_union,eval_single,smul_eq_mul]; ring

theorem eval_times (u : Nat → Bool) (p q : Poly) :
    eval u (times p q)=eval u p*eval u q := by
  induction p using Finsupp.induction_linear with
  | zero => simp [times]
  | add a b ha hb => simp only [times,map_add] at ha hb ⊢; rw [ha,hb,add_mul]
  | single m v => simp only [times,Finsupp.linearCombination_single,map_smul,eval_shift,eval_single,smul_eq_mul]; ring

def pstep (s : List Poly × Poly) (g : Nat × Nat) : List Poly × Poly :=
  let z := one + times (s.1.getD g.1 one) (s.1.getD g.2 one)
  (s.1 ++ [z],z)
def init (n : Nat) : List Poly × Poly := (one :: (List.range n).map (fun i ↦ term {i}),one)
def output (n : Nat) (gs : GateList) := (gs.foldl pstep (init n)).2
def inputs (u : Nat → Bool) (n : Nat) := (List.range n).map u
def generator (n : Nat) (gs : GateList) := one-output n gs
def encrypt (n : Nat) (gs : GateList) (m r : F) := m • one + r • generator n gs

def Agree (u : Nat → Bool) (s : List Poly × Poly) (t : List Bool × Bool) :=
  List.Forall₂ (fun p b ↦ eval u p=bit b) s.1 t.1 ∧ eval u s.2=bit t.2

theorem read_ok (u : Nat → Bool) {l : List Poly} {k : List Bool}
    (h : List.Forall₂ (fun p b ↦ eval u p=bit b) l k) (i : Nat) :
    eval u (l.getD i one)=bit (k.getD i true) := by
  induction h generalizing i with
  | nil => simp [one,eval_term,mv_empty,bit]
  | cons ha _ ih => cases i with
    | zero => exact ha
    | succ i => exact ih i

theorem nand_poly : ∀ a b : Bool, (1:F)+bit a*bit b=bit (!(a && b)) := by decide

theorem step_ok (u : Nat → Bool) {s : List Poly × Poly} {t : List Bool × Bool}
    (h : Agree u s t) (g : Nat × Nat) : Agree u (pstep s g) (estep t g) := by
  have hnew : eval u (one+times (s.1.getD g.1 one) (s.1.getD g.2 one)) =
      bit (!(t.1.getD g.1 true && t.1.getD g.2 true)) := by
    have hone : eval u one=1 := by simp [one,eval_term,mv_empty]
    simp only [map_add,hone,eval_times] 
    rw [read_ok u h.1,read_ok u h.1,nand_poly]
  have extn {l : List Poly} {k : List Bool} {p : Poly} {b : Bool} (hh : List.Forall₂ (fun a z ↦ eval u a=bit z) l k) (hp : eval u p=bit b) : List.Forall₂ (fun a z ↦ eval u a=bit z) (l++[p]) (k++[b]) := by
    induction hh with
    | nil => exact .cons hp .nil
    | cons hv _ ih => exact .cons hv ih
  exact ⟨extn h.1 hnew,hnew⟩

theorem run_ok (u : Nat → Bool) {s : List Poly × Poly} {t : List Bool × Bool}
    (h : Agree u s t) (gs : GateList) : Agree u (gs.foldl pstep s) (gs.foldl estep t) := by
  induction gs generalizing s t with
  | nil => exact h
  | cons g gs ih => exact ih (step_ok u h g)

theorem init_ok (u : Nat → Bool) (n : Nat) : Agree u (init n) (true::inputs u n,true) := by
  have h1 : eval u one=bit true := by simp [one,eval_term,mv_empty,bit]
  refine ⟨.cons h1 ?_,h1⟩
  have aux (l : List Nat) : List.Forall₂ (fun p b ↦ eval u p=bit b)
      (l.map (fun i ↦ term {i})) (l.map u) := by
    induction l with
    | nil => exact .nil
    | cons i l ih => exact .cons (by simp [eval_term,mv,bit]) ih
  exact aux _

theorem output_spec (u : Nat → Bool) (n : Nat) (gs : GateList) :
    eval u (output n gs) = bit (evalGates (inputs u n,gs)) := (run_ok u (init_ok u n) gs).2

theorem correct (u : Nat → Bool) (n : Nat) (gs : GateList) (m r : F)
    (yes : evalGates (inputs u n,gs)=true) : eval u (encrypt n gs m r)=m := by
  simp [encrypt,generator,output_spec,yes,one,eval_term,mv_empty,bit]

theorem genuine_inputs (x : List Bool) : inputs (fun i ↦ x.getD i false) x.length=x := by
  apply List.ext_getElem
  · simp [inputs]
  · intro i hi hi'
    simp [inputs,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi']

theorem zero_on_no (n : Nat) (gs : GateList)
    (no : ∀ x : List Bool,x.length=n → evalGates (x,gs)=false) : output n gs=0 := by
  apply eval_injective
  intro u
  rw [output_spec,no _ (by simp [inputs])]; rfl

theorem shift_no (n : Nat) (gs : GateList) (no : ∀ x : List Bool,x.length=n → evalGates (x,gs)=false)
    (m r : F) : encrypt n gs m r = encrypt n gs (m+1) (r-1) := by
  simp only [encrypt,generator,zero_on_no n gs no,sub_zero,← add_smul]
  congr 1
  ring


/-- A public input center gives a possibly smaller canonical dictionary. -/
def centeredInit (c : Nat → Bool) (n : Nat) : List Poly × Poly :=
  (one :: (List.range n).map (fun i ↦ term {i} + bit (c i) • one),one)
def centeredOutput (c : Nat → Bool) (n : Nat) (gs : GateList) :=
  (gs.foldl pstep (centeredInit c n)).2

theorem xor_bit : ∀ a b : Bool, bit (xor a b) = bit a + bit b := by decide

theorem centered_spec (c u : Nat → Bool) (n : Nat) (gs : GateList) :
    eval u (centeredOutput c n gs)=bit (evalGates (inputs (fun i ↦ xor (u i) (c i)) n,gs)) := by
  apply (run_ok u _ gs).2
  have h1 : eval u one = bit true := by simp [one,eval_term,mv_empty,bit]
  refine ⟨.cons h1 ?_,h1⟩
  have aux (l : List Nat) : List.Forall₂ (fun p b ↦ eval u p=bit b)
      (l.map (fun i ↦ term {i} + bit (c i) • one)) (l.map fun i ↦ xor (u i) (c i)) := by
    induction l with
    | nil => exact .nil
    | cons i l ih => exact .cons (by cases ha : u i <;> cases hb : c i <;> simp [eval_term,mv,one,bit,ha,hb] <;> decide) ih
  exact aux _

theorem centered_no (c : Nat → Bool) (n : Nat) (gs : GateList)
    (h : ∀ x : List Bool,x.length=n → evalGates (x,gs)=false) : centeredOutput c n gs=0 := by
  apply eval_injective
  intro u
  rw [centered_spec,h _ (by simp [inputs])]; rfl

end
end NANDPrimaryMask
