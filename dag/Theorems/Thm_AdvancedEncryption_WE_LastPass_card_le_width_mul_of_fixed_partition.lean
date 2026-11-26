import Mathlib.Data.Fintype.Card

/-- **Label-only walks need exponential width.** Let `f : X → Fin W` be a fixed map of the
consistent strings `X` to `W` final classes, and let every hybrid `s ≤ T` label strings through
their class (`lab s (f x)`), starting all `false` (`mask`) and ending all `true` (`mask'`). If
every hop changes the label of at most `k` strings of `X`, then `|X| ≤ W · k`: each class flips
at some hop, all of its strings at once. With `|X| = 2^n` witnesses and `k = 1` consistent string
per equality-cube flip, a walk of flips without changes of the class structure (reroutes) needs
`W ≥ 2^n` final classes. -/
theorem AdvancedEncryption.WE.LastPass.card_le_width_mul_of_fixed_partition {X : Type}
    [Fintype X] (W k T : ℕ) (f : X → Fin W) (lab : ℕ → Fin W → Bool)
    (h0 : ∀ c, lab 0 c = false) (hT : ∀ c, lab T c = true)
    (hstep : ∀ s < T, (Finset.univ.filter fun x => lab s (f x) ≠ lab (s + 1) (f x)).card ≤ k) :
    Fintype.card X ≤ W * k := by sorry
