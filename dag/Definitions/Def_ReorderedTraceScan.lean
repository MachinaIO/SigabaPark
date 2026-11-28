import SigabaNeoStd.Machines.Gates
import Mathlib.Tactic
namespace ReorderedTraceScan
open SigabaNeo
abbrev State := Option Bool
abbrev Triple := Bool × Bool × Bool
def first (s : State) (b : Bool) : State := s.map fun _ ↦ b
def second (s : State) (b : Bool) : State := s.map fun a ↦ !(a && b)
def check (s : State) (b : Bool) : State := s.bind fun a ↦ if a=b then some a else none
def block (s : State) (t : Triple) := check (second (first s t.1) t.2.1) t.2.2
def good (t : Triple) := t.2.2 = !(t.1 && t.2.1)
theorem block_ok (s : State) (t : Triple) : (block s t).isSome=true ↔ s.isSome=true ∧ good t := by
  rcases t with ⟨a,b,c⟩
  cases s <;> cases a <;> cases b <;> cases c <;> simp [block,first,second,check,good]
def groupStart (pinned : Bool) (s : State) (b : Bool) : State :=
  if pinned && !b then none else first s b
theorem group_ok (s : State) (b pin : Bool) (pins : List Bool) :
    (pins.foldl check (groupStart pin s b)).isSome=true ↔
      s.isSome=true ∧ (pin=true → b=true) ∧ ∀ c∈pins,c=b := by
  have absent (l : List Bool) : l.foldl check none=none := by
    induction l with | nil => rfl | cons x xs ih => exact ih
  have present (l : List Bool) : (l.foldl check (some b)).isSome=true ↔ ∀ c∈l,c=b := by
    induction l with
    | nil => simp
    | cons a l ih =>
      by_cases h : b=a
      · subst a; simp [check,ih]
      · simp [check,h,absent,Ne.symm h]
  cases s <;> cases pin <;> cases b <;> simp_all [groupStart,first]

def reads (ws : List Bool) (g : Nat × Nat) : Bool × Bool := (ws.getD g.1 true,ws.getD g.2 true)
def matchTrace : List (Nat × Nat) → List Triple → List Bool × Bool → Prop
  | [],[],_ => True
  | g::gs,t::ts,(ws,_) =>
    (t.1,t.2.1)=reads ws g ∧ good t ∧ matchTrace gs ts (ws++[t.2.2],t.2.2)
  | _,_,_ => False

def witnessTrace : List (Nat × Nat) → List Bool × Bool → List Triple
  | [],_ => []
  | g::gs,s =>
    let p := reads s.1 g
    (p.1,p.2,!(p.1 && p.2)) :: witnessTrace gs (estep s g)
theorem unique_trace (gs : List (Nat × Nat)) (s : List Bool × Bool) (ts : List Triple) :
    matchTrace gs ts s ↔ ts=witnessTrace gs s := by
  induction gs generalizing s ts with
  | nil => cases ts <;> simp [matchTrace,witnessTrace]
  | cons g gs ih =>
    rcases s with ⟨ws,last⟩
    cases ts with
    | nil => simp [matchTrace,witnessTrace]
    | cons t ts =>
      rcases t with ⟨a,b,c⟩
      simp only [matchTrace,reads,Prod.mk.injEq,good,witnessTrace,List.cons.injEq]
      constructor
      · rintro ⟨⟨rfl,rfl⟩,rfl,h⟩
        exact ⟨⟨rfl,rfl,rfl⟩,(ih _ _).mp h⟩
      · rintro ⟨⟨rfl,rfl,rfl⟩,h⟩
        exact ⟨⟨rfl,rfl⟩,rfl,(ih _ _).mpr h⟩

def lastOut (ts : List Triple) (start : Bool) := ts.foldl (fun _ t ↦ t.2.2) start
theorem result (gs : List (Nat × Nat)) (s : List Bool × Bool) :
    lastOut (witnessTrace gs s) s.2=(gs.foldl estep s).2 := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih => exact ih (estep s g)

theorem accepts (gs : GateList) (x : List Bool) :
    (∃ ts,matchTrace gs ts (true::x,true) ∧ lastOut ts true=true) ↔ evalGates (x,gs)=true := by
  simp only [unique_trace,exists_eq_left,evalGates]
  rw [result gs (true::x,true)]

theorem counts : 3*4096+128+1=12417 ∧ 4096+128+1=4225 ∧
    4^4096=2^8192 ∧ 4225-2=4223 := by
  refine ⟨by decide,by decide,?_,by decide⟩
  exact (Nat.pow_mul 2 2 4096).symm
end ReorderedTraceScan
