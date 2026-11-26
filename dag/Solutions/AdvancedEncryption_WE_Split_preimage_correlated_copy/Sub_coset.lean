import SigabaNeoStd.Lattices.Trapdoor.Family

open Matrix SigabaNeo.Lattices
open scoped ENNReal

private theorem cosetGauss_congr {n n' m q : ℕ} (B : Matrix (Fin n) (Fin m) (ZMod q))
    (B' : Matrix (Fin n') (Fin m) (ZMod q)) (u : Fin n → ZMod q) (u' : Fin n' → ZMod q)
    (τ : ℝ) (hτ : 0 < τ)
    (h : ∀ x : Fin m → ℤ, B *ᵥ (fun i => (x i : ZMod q)) = u ↔
      B' *ᵥ (fun i => (x i : ZMod q)) = u') :
    cosetGauss B u τ hτ = cosetGauss B' u' τ hτ := by
  classical
  have hs := cosetGauss_isSome_iff B u τ hτ
  have hs' := cosetGauss_isSome_iff B' u' τ hτ
  have hiff : (cosetGauss B u τ hτ).isSome ↔ (cosetGauss B' u' τ hτ).isSome := by
    rw [hs, hs']; exact ⟨fun ⟨x, hx⟩ => ⟨x, (h x).1 hx⟩, fun ⟨x, hx⟩ => ⟨x, (h x).2 hx⟩⟩
  cases hp : cosetGauss B u τ hτ with
  | none =>
    cases hp' : cosetGauss B' u' τ hτ with
    | none => rfl
    | some p' => rw [hp, hp'] at hiff; simp at hiff
  | some p =>
    cases hp' : cosetGauss B' u' τ hτ with
    | none => rw [hp, hp'] at hiff; simp at hiff
    | some p' =>
      obtain ⟨M, hM, hpM⟩ := Trapdoor.Family.cosetGauss_apply B u hτ hp
      obtain ⟨M', hM', hpM'⟩ := Trapdoor.Family.cosetGauss_apply B' u' hτ hp'
      set W : (Fin m → ℤ) → ℝ≥0∞ := fun x =>
        if B *ᵥ (fun i => (x i : ZMod q)) = u then
          ENNReal.ofReal (ProbabilityTheory.gaussianWeight τ (embed m x)) else 0 with hW
      have e1 : ∀ x, p x = W x / ENNReal.ofReal M := by
        intro x; rw [hpM x, hW]; simp only
        by_cases hx : B *ᵥ (fun i => (x i : ZMod q)) = u
        · simp only [hx, ite_true]
        · simp only [hx, ite_false, ENNReal.zero_div]
      have e2 : ∀ x, p' x = W x / ENNReal.ofReal M' := by
        intro x; rw [hpM' x, hW]; simp only
        by_cases hx : B *ᵥ (fun i => (x i : ZMod q)) = u
        · simp only [hx, (h x).1 hx, ite_true]
        · have hx' : ¬ B' *ᵥ (fun i => (x i : ZMod q)) = u' := fun h' => hx ((h x).2 h')
          simp only [hx, hx', ite_false, ENNReal.zero_div]
      have hM0 : ENNReal.ofReal M ≠ 0 := by simpa using hM
      have hM0' : ENNReal.ofReal M' ≠ 0 := by simpa using hM'
      have t1 : (∑' x, W x) / ENNReal.ofReal M = 1 := by
        rw [div_eq_mul_inv, ← ENNReal.tsum_mul_right, ← p.tsum_coe]
        exact tsum_congr fun x => by rw [e1 x, div_eq_mul_inv]
      have t2 : (∑' x, W x) / ENNReal.ofReal M' = 1 := by
        rw [div_eq_mul_inv, ← ENNReal.tsum_mul_right, ← p'.tsum_coe]
        exact tsum_congr fun x => by rw [e2 x, div_eq_mul_inv]
      rw [ENNReal.div_eq_one_iff hM0 ENNReal.ofReal_ne_top] at t1
      rw [ENNReal.div_eq_one_iff hM0' ENNReal.ofReal_ne_top] at t2
      congr 1
      ext x
      rw [e1 x, e2 x, ← t1, ← t2]

private theorem preimage_congr {n n' m k q : ℕ} (B : Matrix (Fin n) (Fin m) (ZMod q))
    (B' : Matrix (Fin n') (Fin m) (ZMod q)) (P : Matrix (Fin n) (Fin k) (ZMod q))
    (P' : Matrix (Fin n') (Fin k) (ZMod q)) (τ : ℝ) (hτ : 0 < τ)
    (h : ∀ (j : Fin k) (x : Fin m → ℤ), B *ᵥ (fun i => (x i : ZMod q)) = (fun i => P i j) ↔
      B' *ᵥ (fun i => (x i : ZMod q)) = (fun i => P' i j)) :
    Trapdoor.preimage B P τ hτ = Trapdoor.preimage B' P' τ hτ := by
  unfold Trapdoor.preimage
  congr 2
  exact List.map_congr_left fun j _ => cosetGauss_congr _ _ _ _ τ hτ (h j)

theorem solution {n n' m k q : ℕ} (B : Matrix (Fin n) (Fin m) (ZMod q))
    (R : Matrix (Fin n') (Fin n) (ZMod q)) (P : Matrix (Fin n) (Fin k) (ZMod q))
    (τ : ℝ) (hτ : 0 < τ) :
    Trapdoor.preimage (Matrix.of fun i j => Fin.addCases (fun a => B a j) (fun b => (R * B) b j) i)
        (Matrix.of fun i j => Fin.addCases (fun a => P a j) (fun b => (R * P) b j) i) τ hτ =
      Trapdoor.preimage B P τ hτ := by
  refine preimage_congr _ _ _ _ τ hτ fun j x => ?_
  set xv : Fin m → ZMod q := fun i => (x i : ZMod q)
  constructor
  · intro hx
    funext a
    have := congrFun hx (Fin.castAdd n' a)
    simpa [Matrix.mulVec, dotProduct] using this
  · intro hx
    funext i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · have := congrFun hx a
      simpa [Matrix.mulVec, dotProduct] using this
    · have key : (R * B) *ᵥ xv = R *ᵥ (fun i => P i j) := by
        rw [← Matrix.mulVec_mulVec, hx]
      have := congrFun key b
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Fin.addCases_right] at this ⊢
      rw [this]
      simp [Matrix.mul_apply]
