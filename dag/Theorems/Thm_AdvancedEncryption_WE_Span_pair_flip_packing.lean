import Mathlib

theorem AdvancedEncryption.WE.Span.pair_flip_packing {I V W K : Type*} [Fintype I] [Fintype V] [Field K]
    [DecidableEq K] [DecidableEq W] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (s : V →ₗ[K] K) (view : I → V →ₗ[K] W)
    (recovers : ∀ i j, i ≠ j → ∀ x, view i x = 0 → view j x = 0 → s x = 0) :
    (∑ i, (Finset.univ.filter (fun x : V => s x = 1 ∧ view i x = 0)).card) ≤
      (Finset.univ.filter (fun x : V => s x = 1)).card := by sorry
