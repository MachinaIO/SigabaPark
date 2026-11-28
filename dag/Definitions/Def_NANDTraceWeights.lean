import SigabaNeoStd.Machines.Gates
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace NANDTraceWeights
open SigabaNeo
abbrev F := ZMod 2
abbrev Mass := Nat →₀ F
def bit (b : Bool) : F := if b then 1 else 0
abbrev Entry := (Nat × Nat) × Bool
abbrev State := (List Bool × Bool) × (List Bool × Bool)

structure Row where
  out : Nat
  left : Nat
  right : Nat
  actualRight : F
  claimedLeft : F
  residual : F

noncomputable def score (d : Nat → F) := Finsupp.linearCombination F d
noncomputable def pull (r : Row) (w : Mass) : Mass :=
  w - Finsupp.single r.out (w r.out) +
    Finsupp.single r.left (w r.out*r.actualRight) +
    Finsupp.single r.right (w r.out*r.claimedLeft)

def advance (r : Row) (d : Nat → F) :=
  Function.update d r.out (r.residual + r.actualRight*d r.left + r.claimedLeft*d r.right)

theorem score_update (d : Nat → F) (i : Nat) (v : F) (w : Mass) :
    score (Function.update d i v) w = score d w + w i*(v-d i) := by
  induction w using Finsupp.induction_linear with
  | zero => simp [score]
  | add x y hx hy => simp only [map_add,Finsupp.add_apply,hx,hy]; ring
  | single j x =>
    by_cases h : j=i
    · subst j; simp [score,Finsupp.linearCombination_single]; ring
    · simp [score,Finsupp.linearCombination_single,Function.update_of_ne h,
        Finsupp.single_eq_of_ne (Ne.symm h)]

theorem adjoint (r : Row) (d : Nat → F) (w : Mass) :
    score (advance r d) w = score d (pull r w) + w r.out*r.residual := by
  rw [advance,score_update]
  simp only [pull,map_add,map_sub,score,Finsupp.linearCombination_single,smul_eq_mul]
  ring

noncomputable def reversePass : List Row → Mass → Mass × List F
  | [], w => (w,[])
  | r::rs,w =>
    let t := reversePass rs w
    (pull r t.1,t.1 r.out :: t.2)

def dot : List F → List F → F
  | a::as,b::bs => a*b+dot as bs
  | _,_ => 0

theorem reverse_size (rs : List Row) (w : Mass) : (reversePass rs w).2.length = rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [reversePass,ih]

theorem telescope (rs : List Row) (w : Mass) (d : Nat → F) :
    score (rs.foldl (fun t r ↦ advance r t) d) w =
    score d (reversePass rs w).1 + dot (reversePass rs w).2 (rs.map Row.residual) := by
  induction rs generalizing d with
  | nil => simp [reversePass,dot]
  | cons r rs ih =>
    simp only [List.foldl_cons,List.map_cons,reversePass,dot]
    rw [ih,adjoint]; ring

def start (x : List Bool) : State := ((true::x,true),(true::x,true))
def step (s : State) (p : Entry) : State := (estep s.1 p.1,(s.2.1 ++ [p.2],p.2))
def delta (s : State) (i : Nat) := bit (s.2.1.getD i true) - bit (s.1.1.getD i true)
def row (s : State) (p : Entry) : Row :=
  let x := s.2.1.getD p.1.1 true
  let y := s.2.1.getD p.1.2 true
  ⟨s.1.1.length,p.1.1,p.1.2,bit (s.1.1.getD p.1.2 true),bit x,bit p.2-bit (!(x && y))⟩
def compile (s : State) : List Entry → List Row
  | [] => []
  | p::ps => row s p :: compile (step s p) ps

theorem local_discrepancy : ∀ x y z a b : Bool, bit z-bit (!(a && b)) =
    (bit z-bit (!(x && y))) + bit b*(bit x-bit a) + bit x*(bit y-bit b) := by decide

theorem residual_form : ∀ x y z : Bool, bit z-bit (!(x && y)) = 1+bit z+bit x*bit y := by decide

theorem read_append (l : List Bool) (b : Bool) (i : Nat) :
    (l ++ [b]).getD i true = (if i=l.length then b else l.getD i true) := by
  induction l generalizing i with
  | nil => cases i <;> rfl
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ i => simpa [List.getD_cons_succ] using ih i

theorem consistent_step (s : State) (p : Entry) (hl : s.1.1.length=s.2.1.length) :
    (step s p).1.1.length = (step s p).2.1.length := by simp [step,estep,hl]

theorem native_step (s : State) (p : Entry) (hl : s.1.1.length=s.2.1.length) :
    delta (step s p) = advance (row s p) (delta s) := by
  funext i
  by_cases h : i=s.1.1.length
  · subst i
    simp only [delta,step,estep,read_append,← hl,ite_true,advance,row,Function.update_self]
    exact local_discrepancy .. 
  · simp only [delta,step,estep,read_append,← hl,if_neg h,advance,row,Function.update_of_ne h]

theorem compiled_run (s : State) (ps : List Entry) (hl : s.1.1.length=s.2.1.length) :
    (compile s ps).foldl (fun t r ↦ advance r t) (delta s) = delta (ps.foldl step s) := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih =>
    simp only [compile,List.foldl_cons]
    rw [← native_step s p hl, ih (step s p) (consistent_step s p hl)]

theorem actual_run (s : State) (ps : List Entry) :
    (ps.foldl step s).1 = (ps.map Prod.fst).foldl estep s.1 := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih => exact ih (step s p)

theorem length_run (s : State) (ps : List Entry) :
    (ps.foldl step s).1.1.length = s.1.1.length + ps.length := by
  induction ps generalizing s with
  | nil => simp
  | cons p ps ih => simp [ih,step,estep,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem aligned_run (s : State) (ps : List Entry) (hl : s.1.1.length=s.2.1.length) :
    (ps.foldl step s).1.1.length = (ps.foldl step s).2.1.length := by
  induction ps generalizing s with
  | nil => exact hl
  | cons p ps ih => exact ih (step s p) (consistent_step s p hl)

/-- The actual registered evaluator occurs on the right, with true for all as-yet
unavailable wires. Coincident parents collect both reverse contributions. -/
theorem functional_refutation (x : List Bool) (ps : List Entry) (p : Entry) :
    let all := ps ++ [p]
    let rs := compile (start x) all
    let t := (start x).1.1.length + ps.length
    let weights := (reversePass rs (Finsupp.single t 1)).2
    (1-bit p.2) + dot weights (rs.map Row.residual) =
      1-bit (evalGates (x,all.map Prod.fst)) := by
  dsimp only
  let s := ps.foldl step (start x)
  let t := (start x).1.1.length + ps.length
  let ws := Finsupp.single t (1:F)
  let rs := compile (start x) (ps++[p])
  have hz : delta (start x) = 0 := by funext i; simp [delta,start]
  have h0 (w : Mass) : score (0 : Nat → F) w = 0 := by simp [score]
  have hh := telescope rs ws (delta (start x))
  have hc := compiled_run (start x) (ps++[p]) rfl
  rw [hc,hz,h0,zero_add] at hh
  have ht : s.1.1.length=t := length_run _ _
  have ht' : s.2.1.length=t := (aligned_run (start x) ps rfl).symm.trans ht
  have he : delta ((ps++[p]).foldl step (start x)) t =
      bit p.2 - bit (evalGates (x,(ps++[p]).map Prod.fst)) := by
    have ha := actual_run (start x) ps
    simp only [List.foldl_append,List.foldl_cons,List.foldl_nil,List.map_append,List.map_cons,List.map_nil]
    unfold evalGates
    rw [List.foldl_append]
    change delta (step s p) t = bit p.2 - bit (estep ((ps.map Prod.fst).foldl estep (start x).1) p.1).2
    simp only [delta,step,estep,read_append,ht,ht',ite_true]
    change _ = bit p.2 - bit (!( _ && _))
    rw [← ha]
  have hx : score (delta ((ps++[p]).foldl step (start x))) ws =
      bit p.2 - bit (evalGates (x,(ps++[p]).map Prod.fst)) := by
    simpa [ws,score,Finsupp.linearCombination_single] using he
  rw [← hh,hx]
  ring

end NANDTraceWeights
