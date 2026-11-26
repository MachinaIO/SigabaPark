import Mathlib

theorem solution {T V S : Type*} [DecidableEq V] [DecidableEq S]
    (cert : Finset T) (res : T → Finset V) (bad : V → Finset S) (B D : ℕ)
    (hsize : ∀ t ∈ cert, (res t).card ≤ D)
    (hhash : ∀ t ∈ cert, ∀ v ∈ res t, (bad v).card ≤ B) :
    (cert.biUnion fun t ↦ (res t).biUnion bad).card ≤ cert.card * D * B := by
  calc
    _ ≤ ∑ t ∈ cert, ((res t).biUnion bad).card := Finset.card_biUnion_le
    _ ≤ ∑ t ∈ cert, D * B := by
      apply Finset.sum_le_sum
      intro t ht
      calc
        _ ≤ ∑ v ∈ res t, (bad v).card := Finset.card_biUnion_le
        _ ≤ ∑ _v ∈ res t, B := Finset.sum_le_sum (hhash t ht)
        _ = (res t).card * B := by simp
        _ ≤ _ := Nat.mul_le_mul_right B (hsize t ht)
    _ = _ := by simp [Nat.mul_assoc]
