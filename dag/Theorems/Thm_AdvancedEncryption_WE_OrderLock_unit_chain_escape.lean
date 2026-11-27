import Mathlib.Tactic.Common

/-- With the order (out, n2, w, n1), eight co-located cover flips on the clause slots of the 4-variable NAND Tseitin CNF reach the all-ones slot (note `pq-we-order-lock`). -/
theorem AdvancedEncryption.WE.OrderLock.unit_chain_escape
    (CC : (ℕ → Bool → Bool) → (ℕ → Bool → Bool) → (ℕ → Bool → Bool) → Prop)
    (hCC : ∀ d c d', CC d c d' ↔ ∃ L b, (∀ i < L, ∀ β, d i β = c i β) ∧ c L b = true ∧
      (∀ i, L < i → ∀ β, c i β = true) ∧ d' L b = !(d L b) ∧
      ∀ i β, ¬ (i = L ∧ β = b) → d' i β = d i β) :
    CC (fun i β => if i = 2 then β == true else if i = 3 then β == true else true)
      (fun i β => if i = 0 then β == false else true)
      (fun i β => if i = 0 then β == true else if i = 2 then β == true else if i = 3 then β == true else true) ∧
    CC (fun i β => if i = 0 then β == true else if i = 2 then β == true else if i = 3 then β == true else true)
      (fun i β => if i = 0 then β == true else if i = 1 then β == true else true)
      (fun i β => if i = 0 then β == true else if i = 1 then β == false else if i = 2 then β == true else if i = 3 then β == true else true) ∧
    CC (fun i β => if i = 1 then β == false else if i = 2 then β == false else true)
      (fun i β => if i = 0 then β == false else true)
      (fun i β => if i = 0 then β == true else if i = 1 then β == false else if i = 2 then β == false else true) ∧
    CC (fun i β => if i = 0 then β == true else if i = 1 then β == false else if i = 2 then β == true else if i = 3 then β == true else true)
      (fun i β => if i = 0 then β == true else if i = 1 then β == false else if i = 2 then β == false else true)
      (fun i β => if i = 0 then β == true else if i = 1 then β == false else if i = 3 then β == true else true) ∧
    CC (fun i β => if i = 1 then β == false else if i = 3 then β == false else true)
      (fun i β => if i = 0 then β == false else true)
      (fun i β => if i = 0 then β == true else if i = 1 then β == false else if i = 3 then β == false else true) ∧
    CC (fun i β => if i = 0 then β == true else if i = 1 then β == false else if i = 3 then β == true else true)
      (fun i β => if i = 0 then β == true else if i = 1 then β == false else if i = 3 then β == false else true)
      (fun i β => if i = 0 then β == true else if i = 1 then β == false else true) ∧
    CC (fun i β => if i = 0 then β == true else if i = 1 then β == false else true)
      (fun i β => if i = 0 then β == true else if i = 1 then β == true else true)
      (fun i β => if i = 0 then β == true else true) ∧
    CC (fun i β => if i = 0 then β == true else true)
      (fun i β => if i = 0 then β == false else true)
      (fun _ _ => true) := by sorry
