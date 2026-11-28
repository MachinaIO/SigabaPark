import SigabaNeoStd.Machines.Gates
import Mathlib.Tactic

namespace ShortSumTrace
open SigabaNeo
structure Choice where
  a : Nat
  b : Nat
  x : Bool
  y : Bool
def Choice.gate (p : Choice) := (p.a,p.b)
def norm (n i : Nat) := if i<n then i else 0
def events (n : Nat) : List Choice → List (Nat × Bool)
 | [] => []
 | p::ps => (norm n p.a,p.x)::(norm n p.b,p.y)::events (n+1) ps
def column (i : Nat) (e : List (Nat × Bool)) := (e.filter (fun t ↦ decide (t.1=i))).map Prod.snd
def ones (l : List Bool) := l.count true
def digit (b : Bool) (l : List Bool) := (if b then 0 else l.length)+ones l

theorem column_exact (b : Bool) (l : List Bool) :
    digit b l=l.length ↔ ∀ x ∈ l,x=b := by
  cases b <;> induction l with
  | nil => simp [digit,ones]
  | cons x l ih =>
    have h := List.count_le_length (a:=true) (l:=l)
    cases x <;> simp [digit,ones,List.count_cons] at ih ⊢ <;> omega

theorem read_exact (u : Nat → Bool) (e : List (Nat × Bool))
    (h : ∀ j, digit (u j) (column j e)=(column j e).length) (j : Nat) (b : Bool)
    (he : (j,b)∈e) : b=u j := by
  apply (column_exact (u j) _).mp (h j)
  exact List.mem_map.mpr ⟨(j,b),List.mem_filter.mpr ⟨he,by simp⟩,rfl⟩

def outputOK (u : Nat → Bool) : Nat → List Choice → Prop
 | _,[] => True
 | n,p::ps => u n= !(p.x && p.y) ∧ outputOK u (n+1) ps

def make (s : List Bool × Bool) : GateList → List Choice
 | [] => []
 | (a,b)::gs => ⟨a,b,s.1.getD a true,s.1.getD b true⟩ :: make (estep s (a,b)) gs

def wiring (ps : List Choice) := ps.map Choice.gate

theorem make_wiring (s : List Bool × Bool) (gs : GateList) : wiring (make s gs)=gs := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih => obtain ⟨a,b⟩ := g; exact congrArg (List.cons (a,b)) (ih _)

def last (n k old : Nat) := if k=0 then old else n+k-1

theorem unique_trace (u : Nat → Bool) (hu : u 0=true) (s : List Bool × Bool)
    (old : Nat) (ps : List Choice)
    (hinput : ∀ i<s.1.length,s.1.getD i true=u i) (hl : s.2=u old)
    (ho : outputOK u s.1.length ps)
    (hr : ∀ j b, (j,b)∈events s.1.length ps → b=u j) :
    ps=make s (wiring ps) ∧ ((wiring ps).foldl estep s).2=u (last s.1.length ps.length old) := by
  induction ps generalizing s old with
  | nil => exact ⟨rfl,hl⟩
  | cons p ps ih =>
    obtain ⟨a,b,x,y⟩ := p
    let n := s.1.length
    have read (j : Nat) : s.1.getD j true=u (norm n j) := by
      by_cases h : j<n
      · rw [norm, if_pos h]; exact hinput j h
      · have hj : s.1.length ≤ j := by omega
        simp [norm,h,hu,List.getD_eq_getElem?_getD,List.getElem?_eq_none hj]
    have hx : x=s.1.getD a true := (hr _ _ (by simp [events,n])).trans (read a).symm
    have hy : y=s.1.getD b true := (hr _ _ (by simp [events,n])).trans (read b).symm
    let t := estep s (a,b)
    have ht : t.1.length=n+1 := by simp [t,n,estep]
    have hv : t.2=u n := by rw [ho.1,hx,hy]; rfl
    have hi (i : Nat) (h : i<t.1.length) : t.1.getD i true=u i := by
      by_cases hc : i<n
      · change (s.1++[t.2]).getD i true=u i
        simpa only [List.getD_eq_getElem?_getD,List.getElem?_append_left hc] using hinput i hc
      · have hz : i=n := by omega
        rw [hz,← hv]; simp [t,n,estep]
    have htO : outputOK u t.1.length ps := ht ▸ ho.2
    have htR (j : Nat) (v : Bool) (h : (j,v)∈events t.1.length ps) : v=u j := by
      apply hr j v; simp only [events,List.mem_cons]; right; right; simpa [ht,n] using h
    obtain ⟨huq,he⟩ := ih t n hi hv htO htR
    constructor
    · change _ :: ps = _ :: make t (wiring ps)
      rw [← huq,hx,hy]
    · change ((wiring ps).foldl estep t).2=_
      rw [he,ht]
      congr 1
      unfold last; simp only [List.length_cons]; split <;> split <;> omega

theorem digit_decodes (x : List Bool) (u : Nat → Bool) (ps : List Choice)
    (hk : u 0=true) (hi : ∀ j<(true::x).length, (true::x).getD j true=u j)
    (ho : outputOK u (true::x).length ps)
    (hd : ∀ j, digit (u j) (column j (events (true::x).length ps))=(column j (events (true::x).length ps)).length)
    (terminal : u (last (true::x).length ps.length 0)=true) :
    ps=make (true::x,true) (wiring ps) ∧ evalGates (x,wiring ps)=true := by
  obtain ⟨uniq,eval⟩ := unique_trace u hk (true::x,true) 0 ps hi hk.symm ho
    (fun j b he ↦ read_exact u _ hd j b he)
  exact ⟨uniq,eval.trans terminal⟩

end ShortSumTrace
