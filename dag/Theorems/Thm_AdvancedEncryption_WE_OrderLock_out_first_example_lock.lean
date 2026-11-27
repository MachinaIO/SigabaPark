import Mathlib.Tactic.Common

/-- With the output gate first in the level order, the 4-variable NAND Tseitin CNF is still locked: pinning out = 1, class-covered moves and low cover flips never yield an all-ones slot (note `pq-we-order-lock`). -/
theorem AdvancedEncryption.WE.OrderLock.out_first_example_lock {ι : Type*} (conf : ℕ → ι → ℕ → Bool → Bool)
    (h0 : ∀ e, conf 0 e ∈ ([fun _ _ => false,
      fun i β => if i = 1 then β == false else if i = 2 then β == false else true,
      fun i β => if i = 1 then β == true else if i = 2 then β == true else true,
      fun i β => if i = 1 then β == false else if i = 3 then β == false else true,
      fun i β => if i = 2 then β == false else if i = 3 then β == false else true,
      fun i β => if i = 1 then β == true else if i = 2 then β == true else
        if i = 3 then β == true else true,
      fun i β => if i = 0 then β == false else if i = 3 then β == false else true,
      fun i β => if i = 0 then β == true else if i = 3 then β == true else true,
      fun i β => if i = 0 then β == false else true] : List (ℕ → Bool → Bool)))
    (hstep : ∀ t, ∃ d, (∀ e, e ≠ d → conf (t + 1) e = conf t e) ∧
      ((∀ x : ℕ → Bool, (∀ i, conf (t + 1) d i (x i) = true) →
        ∃ e, (∀ β, conf t e 1 β = conf (t + 1) d 1 β) ∧ ∀ i, conf t e i (x i) = true) ∨
       ∃ c L b, L < 2 ∧ (∀ i < L, ∀ β, conf t c i β = conf t d i β) ∧ conf t c L b = true ∧
         (∀ i, L < i → ∀ β, conf t c i β = true) ∧
         ∀ i β, ¬ (i = L ∧ β = b) → conf (t + 1) d i β = conf t d i β)) :
    (∀ w n1 n2 o : Bool, ((w || n1) && (!w || !n1) && (w || n2) && (n1 || n2) &&
        (!w || !n1 || !n2) && (n2 || o) && (!n2 || !o) && o) = false) ∧
    ∀ t e, ¬ ∀ i β, conf t e i β = true := by sorry
