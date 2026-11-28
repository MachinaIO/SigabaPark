import SigabaNeoStd.Lattices.RingLWEInst
import Mathlib
namespace AttainableDictionary
open Cslib.Probability
variable {W J : Type}
def table (valid : W → Bool) (rep : J → W) (msg : Bool) (coins : J → Bool) :=
  fun j ↦ if valid (rep j) then msg else coins j

theorem read (valid : W → Bool) (rep : J → W) (route : W → J)
    (h : ∀ w,valid w=true → valid (rep (route w))=true)
    (w : W) (hw : valid w=true) (m : Bool) (coins : J → Bool) :
    table valid rep m coins (route w)=m := by simp [table,h w hw]

theorem no_view {O : Type} (valid : W → Bool) (no : ∀ w, valid w=false) (rep : J → W)
    (coins : PMF (J → Bool)) (emit : (J → Bool) → O) :
    coins.map (fun r ↦ emit (table valid rep false r))=
    coins.map (fun r ↦ emit (table valid rep true r)) := by
  congr 1; funext r; congr 1; funext j; simp [table,no]

def scan (entries : List J) (rep : J → W) (valid : W → Bool) :=
  entries.findSome? fun j ↦ if valid (rep j) then some (rep j) else none

theorem scan_spec (entries : List J) (rep : J → W) (valid : W → Bool) :
    (scan entries rep valid).isSome=true ↔ ∃ j∈entries,valid (rep j)=true := by
  induction entries with
  | nil => simp [scan]
  | cons j js ih => cases h : valid (rep j) <;> simp [scan,List.findSome?,h] at ih ⊢ <;> tauto

theorem scan_valid (entries : List J) (rep : J → W) (valid : W → Bool) (w : W)
    (h : scan entries rep valid=some w) : valid w=true := by
  induction entries with
  | nil => simp [scan] at h
  | cons j js ih =>
    cases hj : valid (rep j) <;> simp [scan,List.findSome?,hj] at h
    · exact ih h
    · simpa [← h] using hj

theorem solves (entries : List J) (rep : J → W) (valid : W → Bool)
    (cover : (∃ w,valid w=true) → ∃ j∈entries,valid (rep j)=true) :
    (scan entries rep valid).isSome=true ↔ ∃ w,valid w=true := by
  rw [scan_spec]
  exact ⟨fun ⟨j,_,h⟩ ↦ ⟨_,h⟩,cover⟩

/-- Canonical semantically evaluated sign of the one-coin two-fiber construction. -/
def orbit (ok : W → Bool) (msg coin : Bool) := fun w ↦ if ok w then msg else msg ^^ coin

theorem orbit_correct (ok : W → Bool) (w : W) (h : ok w=true) (m k : Bool) :
    orbit ok m k w=m := by simp [orbit,h]

def flip : Bool ≃ Bool := ⟨not,not,Bool.not_not,Bool.not_not⟩

theorem orbit_no {O : Type} (ok : W → Bool) (no : ∀ w,ok w=false) (serialize : (W → Bool) → O) :
    (Cslib.Probability.PMF.uniformOfFintype Bool).map (fun k ↦ serialize (orbit ok false k)) =
    (Cslib.Probability.PMF.uniformOfFintype Bool).map (fun k ↦ serialize (orbit ok true k)) := by
  have hh := congrArg (PMF.map (fun k ↦ serialize (orbit ok false k))) (Cslib.Probability.PMF.uniformOfFintype_map_equiv flip)
  rw [PMF.map_comp] at hh
  apply hh.symm.trans
  apply congrArg (fun f ↦ (Cslib.Probability.PMF.uniformOfFintype Bool).map f)
  funext k; apply congrArg serialize; funext w; cases k <;> simp [flip,orbit,no,Function.comp_def]

theorem compare {O : Type} (ok : W → Bool) (serialize : (W → Bool) ↪ O) :
    serialize (orbit ok false true) ≠ serialize (fun _ ↦ true) ↔ ∃ w,ok w=true := by
  classical
  rw [Ne,serialize.injective.eq_iff]
  constructor
  · contrapose!; intro h; funext w; simp [orbit,h w]
  · rintro ⟨w,hw⟩ he
    have hz := congrFun he w; simp [orbit,hw] at hz
end AttainableDictionary
