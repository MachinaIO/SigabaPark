import Mathlib.Tactic.Common

/-- An unsatisfiable 4-variable NAND Tseitin CNF whose clause slots, under class-covered moves and level-0 cover flips, never yield an all-ones slot (note `pq-we-class-lock`). -/
theorem AdvancedEncryption.WE.ClassLock.tseitin_example_lock {ι : Type*} (conf : ℕ → ι → ℕ → Bool → Bool)
    (h0 : ∀ e, conf 0 e ∈ ([fun _ _ => false,
      fun i β => if i = 0 then β == false else if i = 1 then β == false else true,
      fun i β => if i = 0 then β == true else if i = 1 then β == true else true,
      fun i β => if i = 0 then β == false else if i = 2 then β == false else true,
      fun i β => if i = 1 then β == false else if i = 2 then β == false else true,
      fun i β => if i = 0 then β == true else if i = 1 then β == true else
        if i = 2 then β == true else true,
      fun i β => if i = 2 then β == false else if i = 3 then β == false else true,
      fun i β => if i = 2 then β == true else if i = 3 then β == true else true,
      fun i β => if i = 3 then β == false else true] : List (ℕ → Bool → Bool)))
    (hstep : ∀ t, ∃ d, (∀ e, e ≠ d → conf (t + 1) e = conf t e) ∧
      ((∀ x : ℕ → Bool, (∀ i, conf (t + 1) d i (x i) = true) →
        ∃ e, (∀ c, conf t e 0 c = conf (t + 1) d 0 c) ∧ ∀ i, conf t e i (x i) = true) ∨
       ∃ c b, conf t c 0 b = true ∧ ∀ i, 0 < i → ∀ β, conf t c i β = true)) :
    (∀ w n1 n2 o : Bool, ((w || n1) && (!w || !n1) && (w || n2) && (n1 || n2) &&
        (!w || !n1 || !n2) && (n2 || o) && (!n2 || !o) && o) = false) ∧
    ∀ t e, ¬ ∀ i β, conf t e i β = true := by sorry
