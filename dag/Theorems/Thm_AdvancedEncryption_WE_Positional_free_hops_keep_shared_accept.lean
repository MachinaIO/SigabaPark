import Mathlib.Data.Fintype.Card

/-- Free hops never empty a shared accepting state. Hybrid `i` routes every path `p` to a final
state `route i p`, accepted iff `acc i (route i p)`. A hop is *free* if it is either a reroute
that keeps every accepted path where it is and sends rejected paths only to rejecting states, or a
change of acceptance of final states that are reached by at most one path. If initially more
paths are accepted than there are final states, then after any number of free hops some path is
still accepted. In the positional GGH15 WE candidate with row-partitioned trapdoors (note
`pq-we-ggh15-row-partitioned-trapdoors`), the two free hop types are the ones provable from LWE
(reject-class reroutes and isolated leaf flips), so a walk to the all-reject hybrid with
polynomial width needs hops that change the accept class (splits). -/
theorem AdvancedEncryption.WE.Positional.free_hops_keep_shared_accept {P K : Type*} [Fintype P]
    [Fintype K] [DecidableEq K]
    (route : ℕ → P → K) (acc : ℕ → K → Bool) (T : ℕ)
    (hmove : ∀ i < T,
      (acc (i + 1) = acc i ∧ (∀ p, acc i (route i p) = true → route (i + 1) p = route i p) ∧
          (∀ p, acc i (route i p) = false → acc i (route (i + 1) p) = false)) ∨
        (route (i + 1) = route i ∧
          ∀ k, acc (i + 1) k ≠ acc i k → (Finset.univ.filter fun p => route i p = k).card ≤ 1))
    (hwide : Fintype.card K < (Finset.univ.filter fun p => acc 0 (route 0 p) = true).card) :
    ∃ p, acc T (route T p) = true := by sorry
