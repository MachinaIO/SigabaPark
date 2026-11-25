import Mathlib

open Finset in
theorem solution {F : Type*} [AddCommMonoid F] [Fintype F] [DecidableEq F]
    {T : Type*} [Fintype T] {N ρ : ℕ} (f : (Fin N → F) → T)
    (hf : ∀ t, ∃ x, f x = t ∧ (univ.filter fun j => x j ≠ 0).card ≤ ρ) :
    Fintype.card T ≤ ((N + 1) * Fintype.card F) ^ ρ := by
  classical
  -- decoding map from (positions, values) to sparse vectors
  let g : (Fin ρ → Option (Fin N)) × (Fin ρ → F) → (Fin N → F) :=
    fun p j => ∑ i ∈ univ.filter (fun i => p.1 i = some j), p.2 i
  have hsurj : ∀ x : Fin N → F, (univ.filter fun j => x j ≠ 0).card ≤ ρ →
      ∃ p, g p = x := by
    intro x hx
    set s := univ.filter fun j => x j ≠ 0 with hs
    let e : s ↪ Fin ρ := (s.equivFin.toEmbedding).trans (Fin.castLEEmb hx)
    let c : Fin ρ → Option (Fin N) := fun i =>
      if h : ∃ j : s, e j = i then some (h.choose : Fin N) else none
    let v : Fin ρ → F := fun i => match c i with
      | some j => x j
      | none => 0
    refine ⟨(c, v), funext fun j => ?_⟩
    simp only [g]
    by_cases hj : j ∈ s
    · have hfil : univ.filter (fun i => c i = some j) = {e ⟨j, hj⟩} := by
        ext i
        simp only [mem_filter, mem_univ, true_and, mem_singleton]
        constructor
        · intro hi
          simp only [c] at hi
          split_ifs at hi with h
          · have hj' : (h.choose : Fin N) = j := Option.some_injective _ hi
            rw [← h.choose_spec]
            congr 1
            exact Subtype.ext hj'
        · rintro rfl
          have h : ∃ j' : s, e j' = e ⟨j, hj⟩ := ⟨⟨j, hj⟩, rfl⟩
          have hcs : (h.choose : Fin N) = j := congrArg Subtype.val (e.injective h.choose_spec)
          simp only [c, h, ↓reduceDIte, hcs]
      rw [hfil, sum_singleton]
      have hc : c (e ⟨j, hj⟩) = some j := by
        have : e ⟨j, hj⟩ ∈ univ.filter (fun i => c i = some j) := by rw [hfil]; simp
        simpa using this
      simp only [v, hc]
    · have hx0 : x j = 0 := by simpa [hs] using hj
      rw [hx0]
      apply sum_eq_zero
      intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi
      exfalso
      simp only [c] at hi
      split_ifs at hi with h
      have hj' : (h.choose : Fin N) = j := Option.some_injective _ hi
      exact hj (hj' ▸ h.choose.2)
  -- choose a sparse preimage for every target
  have hT : ∀ t, ∃ p, f (g p) = t := by
    intro t
    obtain ⟨x, hxt, hx⟩ := hf t
    obtain ⟨p, hp⟩ := hsurj x hx
    exact ⟨p, hp ▸ hxt⟩
  have hsurjfg : Function.Surjective (f ∘ g) := fun t => hT t
  calc Fintype.card T ≤ Fintype.card ((Fin ρ → Option (Fin N)) × (Fin ρ → F)) :=
        Fintype.card_le_of_surjective _ hsurjfg
    _ = ((N + 1) * Fintype.card F) ^ ρ := by
        simp [Fintype.card_prod, Fintype.card_option, mul_pow]
