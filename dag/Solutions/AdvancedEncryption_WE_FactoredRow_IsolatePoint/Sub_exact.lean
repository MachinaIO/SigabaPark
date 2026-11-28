import Mathlib

theorem solution {Z I K : Type*} [Fintype I] [DecidableEq Z] [Zero K]
    (key : Z → I → Bool) (inj : Function.Injective key)
    (V : (Z → K) → Prop)
    (step : ∀ (i : I) (b : Bool) (f : Z → K), V f →
      V (fun z => if key z i = b then f z else 0))
    (a : Z) (f : Z → K) (hf : V f) :
    V (fun z => if z = a then f z else 0) := by
  classical
  have aux (S : Finset I) : V (fun z => if ∀ i ∈ S, key z i = key a i then f z else 0) := by
    induction S using Finset.induction_on with
    | empty => simpa using hf
    | @insert i S hi ih =>
      convert step i (key a i) _ ih using 1
      funext z
      by_cases h : key z i = key a i <;> simp [h]
  have eqv (z : Z) : (∀ i ∈ (Finset.univ : Finset I), key z i = key a i) ↔ z = a := by
    constructor
    · intro h
      exact inj (funext fun i => h i (Finset.mem_univ i))
    · rintro rfl i _
      rfl
  simpa only [eqv] using aux Finset.univ
