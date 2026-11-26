import SigabaNeoStd.Lattices.LeftoverHash

open SigabaNeo.Lattices Cslib.Probability
open scoped ENNReal

private theorem row_pad {K V : Type} [CommRing K] [Fintype K] [DecidableEq K]
    {n m t : ℕ} [NeZero m]
    (post : Matrix (Option (Fin n)) (Fin m) K →
      (Fin t → Fin n → K) → (Fin t → K) → PMF V) (d₀ d₁ : Fin t → K) :
    let run := fun (d : Fin t → K) ↦
      (PMF.uniformOfFintype (Matrix (Option (Fin n)) (Fin m) K)).bind fun A ↦
        (Cslib.Probability.PMF.pi fun _ : Fin t ↦
          (PMF.uniformOfFintype (Fin m → Bool)).map (binaryHash A)).bind fun H ↦
            post A (fun i j ↦ H i (some j)) (fun i ↦ d i + H i none)
    let ε := ENNReal.ofReal ((t : ℝ) * (Real.sqrt
      ((Fintype.card K : ℝ) ^ (n + 1) * (2 ^ m : ℝ)⁻¹) / 2))
    CloseTo (run d₀) (run d₁) (ε + ε) := by
  intro run ε
  let F := fun (d : Fin t → K) (A : Matrix (Option (Fin n)) (Fin m) K)
      (H : Fin t → Option (Fin n) → K) ↦
    post A (fun i j ↦ H i (some j)) (fun i ↦ d i + H i none)
  let ideal := fun (d : Fin t → K) ↦
    (PMF.uniformOfFintype (Matrix (Option (Fin n)) (Fin m) K)).bind fun A ↦
      (PMF.uniformOfFintype (Fin t → Option (Fin n) → K)).bind (F d A)
  have hh (d : Fin t → K) : CloseTo (run d) (ideal d) ε := by
    simpa [run, ideal, F, ε, Cslib.Probability.PMF.pi_uniformOfFintype] using
      (closeTo_binaryHash_bind (F d))
  have hid (d : Fin t → K) : ideal d = ideal 0 := by
    unfold ideal
    apply congrArg
    funext A
    let shift : Fin t → Option (Fin n) → K := fun i j ↦ j.elim (d i) (fun _ ↦ 0)
    have hind (H : Fin t → Option (Fin n) → K) : F d A H = F 0 A (shift + H) := by
      simp [F, shift, Pi.add_apply]
    rw [show F d A = (fun H ↦ F 0 A (shift + H)) from funext hind]
    ext v
    simp only [PMF.bind_apply, PMF.uniformOfFintype_apply, tsum_fintype]
    exact Fintype.sum_equiv (Equiv.addLeft shift) _ _ fun _ ↦ rfl
  have h₀ := hh d₀
  have h₁ := hh d₁
  rw [hid d₀] at h₀
  rw [hid d₁] at h₁
  exact h₀.trans h₁.symm

theorem solution {K U : Type} [CommRing K] [Fintype K] [DecidableEq K]
    {n m t : ℕ} [NeZero m]
    (key : Matrix (Option (Fin n)) (Fin m) K → (Fin t → Fin m → Bool) → PMF U)
    (hkey : ∀ A x x', (∀ i j, binaryHash A (x i) (some j) = binaryHash A (x' i) (some j)) →
      key A x = key A x') (d₀ d₁ : Fin t → K) :
    let run := fun (d : Fin t → K) ↦
      (PMF.uniformOfFintype (Matrix (Option (Fin n)) (Fin m) K)).bind fun A ↦
        (Cslib.Probability.PMF.pi fun _ : Fin t ↦ PMF.uniformOfFintype (Fin m → Bool)).bind fun x ↦
          (key A x).map fun u ↦
            (A, (fun i j ↦ binaryHash A (x i) (some j)), u, (fun i ↦ d i + binaryHash A (x i) none))
    let ε := ENNReal.ofReal ((t : ℝ) * (Real.sqrt
      ((Fintype.card K : ℝ) ^ (n + 1) * (2 ^ m : ℝ)⁻¹) / 2))
    CloseTo (run d₀) (run d₁) (ε + ε) := by
  classical
  intro run ε
  let hsh := fun (A : Matrix (Option (Fin n)) (Fin m) K) (x : Fin t → Fin m → Bool)
      (i : Fin t) (j : Fin n) ↦ binaryHash A (x i) (some j)
  let rep := fun A (H : Fin t → Fin n → K) ↦
    if h : ∃ x, hsh A x = H then h.choose else fun _ _ ↦ false
  have hrep (A) (x) : key A (rep A (hsh A x)) = key A x := by
    have h : ∃ z, hsh A z = hsh A x := ⟨x, rfl⟩
    apply hkey
    intro i j
    simpa only [rep, dite_eq_left h] using congrFun (congrFun h.choose_spec i) j
  let post := fun A H (v : Fin t → K) ↦ (key A (rep A H)).map fun u ↦ (A, H, u, v)
  have hh := row_pad post d₀ d₁
  dsimp only at hh
  simp only [Cslib.Probability.PMF.pi_map, PMF.bind_map] at hh
  change CloseTo _ _ (ε + ε) at hh
  convert hh using 1 <;> unfold run <;> apply congrArg <;> funext A <;> apply congrArg <;> funext x <;>
    simp only [post, Function.comp_apply] <;> rw [show (fun i j ↦ binaryHash A (x i) (some j)) =
      hsh A x from rfl, hrep]
