import SigabaNeoStd.Machines.Gates
import Mathlib.Tactic

namespace ParabolaChain
open SigabaNeo

def alt : Nat → Bool
  | 0 => false
  | n+1 => !(alt n)

@[simp] theorem alt_even (k : Nat) : alt (2*k) = false := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Nat.mul_succ,alt,ih]

def advance (x : Bool) : Nat → Bool → Bool
  | 0, b => b
  | n+1,b => advance x n (!(x && b))

theorem advance_true (n : Nat) (b : Bool) : advance true n b = (alt n ^^ b) := by
  induction n generalizing b with
  | zero => simp [advance,alt]
  | succ n ih => cases b <;> simp [advance,alt,ih]

/-- The first m gates continue the chain. The last two gates compute its conjunction with x. -/
def tail (p : Nat) : Nat → GateList
  | 0 => [(1,p),(p+1,p+1)]
  | m+1 => (1,p) :: tail (p+1) m

def circuit (n m : Nat) : GateList := (0,0) :: (1,1) :: tail (n+2) m

theorem tail_length (p m : Nat) : (tail p m).length = m+2 := by
  induction m generalizing p <;> simp [tail, *]

theorem gate_count : (circuit 128 4092).length = 4096 := by simp [circuit,tail_length]

theorem get_old (w : List Bool) (i : Nat) (b : Bool) (h : i < w.length) :
    (w++[b]).getD i true = w.getD i true := by
  simp [List.getD_eq_getElem?_getD,List.getElem?_append_left h]

theorem get_new (w : List Bool) (b : Bool) :
    (w++[b]).getD w.length true = b := by simp

theorem tail_run (p m : Nat) (w : List Bool) (prev : Bool)
    (hl : w.length = p+1) (h1 : 1 < w.length) :
    ((tail p m).foldl estep (w,prev)).2 =
      (w.getD 1 true && advance (w.getD 1 true) m (w.getD p true)) := by
  induction m generalizing p w prev with
  | zero =>
    simp only [tail,List.foldl_cons,List.foldl_nil,estep,advance]
    rw [← hl,get_new]; simp
  | succ m ih =>
    simp only [tail,List.foldl_cons,estep,advance]
    rw [ih]
    · rw [get_old _ _ _ h1,← hl,get_new]
    · simp [hl] <;> omega
    · simp <;> omega

theorem unsat (bits : List Bool) (n k : Nat) (hn : bits.length = n) (hpos : 0 < n) :
    evalGates (bits,circuit n (2*k)) = false := by
  cases bits with
  | nil => simp at hn; omega
  | cons x xs =>
    unfold evalGates circuit
    simp only [List.foldl_cons,estep]
    let w := (true :: x :: xs)
    have len : w.length = n+1 := by simp [w] at *; omega
    have v0 : w.getD 0 true = true := rfl
    change ((tail (n+2) (2*k)).foldl estep
      ((w ++ [!(w.getD 0 true && w.getD 0 true)]) ++
        [!((w ++ [!(w.getD 0 true && w.getD 0 true)]).getD 1 true &&
          (w ++ [!(w.getD 0 true && w.getD 0 true)]).getD 1 true)],_)).2 = false
    rw [v0]
    simp only [Bool.and_self,Bool.not_true]
    have hx : w.getD 1 true = x := rfl
    have h1 : 1 < w.length := by omega
    rw [get_old _ _ _ h1,hx,tail_run]
    · have hl : (w++[false]).length = n+2 := by simp [len] <;> omega
      rw [← hl,get_new,get_old _ _ _ (by simp <;> omega),get_old _ _ _ h1,hx]
      cases x <;> simp [advance_true]
    · simp [len] <;> omega
    · simp <;> omega

/-- Reverse the suffix beginning at gate r, numbered starting at one. -/
def broken (r j : Nat) := if r ≤ j then !(alt j) else alt j

theorem broken_step (r j : Nat) :
    broken r (j+1) = !(true && broken r j) ↔ j+1 ≠ r := by
  by_cases h : r ≤ j
  · simp [broken,alt,h,show r ≤ j+1 by omega,show j+1 ≠ r by omega]
  · by_cases e : j+1 = r
    · subst r; simp [broken,alt]
    · simp [broken,alt,h,show ¬r ≤ j+1 by omega,e]

/-- Every group omitting any chain link admits one common Boolean trace on the whole group,
with the accepted output value. The other gates in the Boolean chain hold simultaneously. -/
theorem group_witness (k : Nat) (G : Set (Fin (2*k))) (hG : G ≠ Set.univ) :
    ∃ v : Nat → Bool, v 0 = false ∧ v (2*k) = true ∧
      ∀ j ∈ G, v (j.val+1) = !(true && v j.val) := by
  obtain ⟨i,hi⟩ : ∃ i, i ∉ G := by simpa [Set.eq_univ_iff_forall] using hG
  refine ⟨broken (i.val+1),by simp [broken,alt],by simp [broken,show i.val+1 ≤ 2*k by omega],?_⟩
  intro j hj
  apply (broken_step _ _).mpr
  intro e
  exact hi ((Fin.ext (by omega : j.val = i.val)) ▸ hj)

section Margins
variable {K : Type} [CommRing K]

/-- Row order 00,01,10,11. -/
def weights (a b c : K) : Fin 4 → K := ![2-a-b-c,b+c-1,a+c-1,1-c]

theorem margins (a b c : K) :
    let z := weights a b c
    z 0+z 1+z 2+z 3 = 1 ∧ z 2+z 3 = a ∧ z 1+z 3 = b ∧ z 0+z 1+z 2 = c := by
  simp [weights] <;> constructor <;> ring

def bit (b : Bool) : K := if b then 1 else 0

theorem unit_row (a b : Bool) :
    weights (bit a : K) (bit b) (bit (!(a && b))) =
      fun i ↦ if i.val = (if a then 2 else 0) + (if b then 1 else 0) then 1 else 0 := by
  funext i
  cases a <;> cases b <;> fin_cases i <;> simp [weights,bit] <;> ring

/-- The normalized affine relaxation extends every Boolean-valued wire triple, including
the unique inconsistent position of the broken trace. -/
theorem affine_group (k : Nat) (G : Set (Fin (2*k))) (hG : G ≠ Set.univ) :
    ∃ v : Nat → Bool, v 0 = false ∧ v (2*k) = true ∧
      ∀ j ∈ G, weights (1:K) (bit (v j.val)) (bit (v (j.val+1))) =
        fun i ↦ if i.val = 2 + (if v j.val then 1 else 0) then 1 else 0 := by
  obtain ⟨v,h0,hm,hv⟩ := group_witness k G hG
  refine ⟨v,h0,hm,fun j hj ↦ ?_⟩
  rw [hv j hj]
  exact unit_row true (v j.val)

end Margins
end ParabolaChain
