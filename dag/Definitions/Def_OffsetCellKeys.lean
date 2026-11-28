import SigabaNeoStd.Lattices.RingLWEInst
import Mathlib.Tactic
namespace OffsetCellKeys
open Cslib.Probability
variable {X J S : Type} [Fintype J] [DecidableEq J] [Fintype S] [Nonempty S]
def Key (J S : Type) := J → Option (S × Bool)
def issue (a b : J → Bool) (m : Bool) (k : J → S × Bool) : Key J S × Key J S :=
  (fun j ↦ if a j then some (k j) else none,
   fun j ↦ if b j then some ((k j).1,(k j).2 ^^ m) else none)
def eval (h : S → X → Bool) (j : J) (x : X) (k : Key J S) :=
  (k j).map fun q ↦ h q.1 x ^^ q.2
theorem opens (a b : J → Bool) (m : Bool) (k : J → S × Bool) (j : J) (x : X)
    (h : S → X → Bool) (ha : a j=true) (hb : b j=true) :
    ∃ v,eval h j x (issue a b m k).1=some v ∧ eval h j x (issue a b m k).2=some (v ^^ m) := by
  simp [issue,eval,ha,hb,Bool.xor_assoc]
def flip (b : J → Bool) : (J → S × Bool) ≃ (J → S × Bool) where
  toFun k j := ((k j).1,(k j).2 ^^ b j)
  invFun k j := ((k j).1,(k j).2 ^^ b j)
  left_inv k := by funext j; simp [Bool.xor_assoc]
  right_inv k := by funext j; simp [Bool.xor_assoc]
theorem no_view (a b : J → Bool) (disj : ∀ j,a j=true → b j=false) :
    (Cslib.Probability.PMF.uniformOfFintype (J → S × Bool)).map (issue a b false) =
    (Cslib.Probability.PMF.uniformOfFintype (J → S × Bool)).map (issue a b true) := by
  have hh := congrArg (PMF.map (issue a b true (S:=S)))
    (Cslib.Probability.PMF.uniformOfFintype_map_equiv (flip b))
  rw [PMF.map_comp] at hh
  refine Eq.trans ?_ hh; apply congrArg (fun f ↦ (Cslib.Probability.PMF.uniformOfFintype (J → S × Bool)).map f)
  funext k; apply Prod.ext
  · funext j; cases ha : a j <;> simp [issue,flip,Function.comp_def,ha,disj]
  · funext j; cases hb : b j <;> simp [issue,flip,Function.comp_def,hb]
theorem observed_cells (seen : Bool × Bool → Bool) (no : seen (true,true)=false) :
    let a := fun j : Bool × Bool ↦ seen j && j.1
    let b := fun j : Bool × Bool ↦ seen j && j.2
    (Cslib.Probability.PMF.uniformOfFintype (Bool × Bool → S × Bool)).map (issue a b false) =
    (Cslib.Probability.PMF.uniformOfFintype (Bool × Bool → S × Bool)).map (issue a b true) := by
  apply no_view
  rintro ⟨p,q⟩; cases p <;> cases q <;> simp [no]
end OffsetCellKeys
