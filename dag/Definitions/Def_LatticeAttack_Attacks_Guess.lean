module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit true

public section

namespace SigabaNeo.Lattices.Guess

/-- If at most K inputs admit each competing candidate, bound the count of inputs
admitting no competitor. The per-candidate counts may depend on the input ensemble. -/
theorem uniqueCountLower {ι Ω : Type*} [DecidableEq ι] [DecidableEq Ω]
    (inputs : Finset Ω) (support : Finset ι) (secret : ι) (hs : secret ∈ support)
    (collision : ι → Finset Ω) (K : ℕ)
    (sub : ∀ c ∈ support.erase secret, collision c ⊆ inputs)
    (bound : ∀ c ∈ support.erase secret, (collision c).card ≤ K) :
    inputs.card - (support.card - 1) * K ≤
      (inputs \ ((support.erase secret).biUnion collision)).card := by
  rw [Finset.card_sdiff_of_subset (Finset.biUnion_subset.mpr sub)]
  apply Nat.sub_le_sub_left
  simpa [Finset.card_erase_of_mem hs] using
    Finset.card_biUnion_le_card_mul (support.erase secret) collision K bound

end SigabaNeo.Lattices.Guess
