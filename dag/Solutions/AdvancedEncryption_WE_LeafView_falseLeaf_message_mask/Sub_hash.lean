import SigabaNeoStd.Lattices.LeftoverHash
import SigabaNeoStd.Lattices.BoxSampler
import SigabaNeoStd.Lattices.Homomorphic.Eval

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

private theorem shared_key_mask {K U : Type} [CommRing K] [Fintype K] [DecidableEq K]
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

private theorem box_mask {K X Y Z WT : Type} [CommRing K] [Fintype K] [DecidableEq K] [AddCommGroup X]
    [DecidableEq X] [AddCommGroup Y] {n m t : ℕ} [NeZero m]
    (S : Matrix (Option (Fin n)) (Fin m) K → PMF WT)
    (good : WT → Prop) [DecidablePred good] (Big Small : Finset X) (hBig : Big.Nonempty)
    (F : Matrix (Option (Fin n)) (Fin m) K → X →+ Y) (G : Z → Y) (dec : Y → Z)
    (hdec : ∀ y, G (dec y) = y) (u : Y)
    (Tr : Matrix (Option (Fin n)) (Fin m) K → WT → (Fin t → Fin m → Bool) → Z → X)
    (pub : Matrix (Option (Fin n)) (Fin m) K → WT → (Fin t → Fin n → K) → Z → Y)
    (hpub : ∀ A w, w ∈ (S A).support → good w → ∀ x z,
      F A (Tr A w x z) = pub A w (fun i j ↦ binaryHash A (x i) (some j)) z)
    (hcov : ∀ A w, w ∈ (S A).support → good w → ∀ x v, v ∈ Small → ∀ y,
      v + Tr A w x (dec y) ∈ Big) (d₀ d₁ : Fin t → K) :
    let key := fun A x ↦ (S A).bind fun w ↦
      (if good w then boxSample Big hBig Small (F A) dec (Tr A w x) u
        else PMF.pure none).map fun k ↦ (w,k)
    let run := fun (d : Fin t → K) ↦
      (PMF.uniformOfFintype (Matrix (Option (Fin n)) (Fin m) K)).bind fun A ↦
        (Cslib.Probability.PMF.pi fun _ : Fin t ↦ PMF.uniformOfFintype (Fin m → Bool)).bind fun x ↦
          (key A x).map fun k ↦ (A, fun i j ↦ binaryHash A (x i) (some j), k,
            fun i ↦ d i + binaryHash A (x i) none)
    let ε := ENNReal.ofReal ((t : ℝ) * (Real.sqrt
      ((Fintype.card K : ℝ) ^ (n+1) * (2 ^ m : ℝ)⁻¹) / 2))
    CloseTo (run d₀) (run d₁) (ε+ε) := by
  intro key run ε
  apply shared_key_mask key _ d₀ d₁
  intro A x x' heq
  have hH : (fun i j ↦ binaryHash A (x i) (some j)) = fun i j ↦ binaryHash A (x' i) (some j) :=
    funext fun i ↦ funext fun j ↦ heq i j
  unfold key
  ext out
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro w
  by_cases hw : w ∈ (S A).support
  · by_cases hg : good w
    · have hk := boxSample_eq Big hBig Small (F A) G dec hdec (Tr A w x) (Tr A w x') u
        (hcov A w hw hg x) (hcov A w hw hg x') (fun z ↦ by
          rw [hpub A w hw hg x z, hpub A w hw hg x' z, hH])
      simp [hg, hk]
    · simp [hg]
  · rw [(PMF.apply_eq_zero_iff _ _).mpr hw]
    simp

namespace JointFalseLeaf
open Matrix
variable {K : Type} [CommRing K] [Fintype K] [DecidableEq K] {n m mW k ℓ : ℕ} {Tt : Type}

/-- The matrix with columns `H c`. -/
def ofCols (H : Fin mW → Fin n → K) : Matrix (Fin n) (Fin mW) K := Matrix.of fun a c => H c a

/-- The binary matrix with columns `xs c`. -/
def binOf (xs : Fin mW → Fin m → Bool) : Matrix (Fin m) (Fin mW) K :=
  Matrix.of fun a c => bitVal (xs c a)

omit [Fintype K] [DecidableEq K] in
theorem mul_binOf (B : Matrix (Fin n) (Fin m) K) (xs : Fin mW → Fin m → Bool) :
    B * binOf xs = ofCols fun c => binaryHash B (xs c) := by
  ext a c
  simp [binOf, ofCols, binaryHash, Matrix.mul_apply, Matrix.mulVec, dotProduct]


end JointFalseLeaf

open JointFalseLeaf Matrix

theorem solution {K : Type} [CommRing K] [Fintype K] [DecidableEq K]
    {n m mW k ℓ : ℕ} {Tt : Type} [NeZero m]
    (Γ : GadgetMatrix K (Fin n) (Fin k)) (dec : (Fin n → K) → Fin k → K)
    (hdec : ∀ y, Γ.G *ᵥ dec y = y) (Big Small : Finset (Fin m → K)) (hBig : Big.Nonempty)
    (u : Fin n → K) (φ : Circuit (Fin ℓ)) (w : Fin ℓ → K) (hφw : φ.eval w = 0)
    (S : Matrix (Fin n) (Fin m) K → PMF ((Fin ℓ → Matrix (Fin n) (Fin mW) K) × Tt))
    (good : Tt → Prop) [DecidablePred good]
    (TB : Tt → Fin ℓ → Fin ℓ → Matrix (Fin m) (Fin k) K)
    (TW : Tt → Fin ℓ → Matrix (Fin mW) (Fin k) K)
    (hblock : ∀ B, ∀ WT ∈ (S B).support, good WT.2 → ∀ i j,
      B * TB WT.2 i j + WT.1 i * TW WT.2 j = if i = j then Γ.G else 0)
    (hcov : ∀ B, ∀ WT ∈ (S B).support, good WT.2 → ∀ xs : Fin mW → Fin m → Bool,
      ∀ a ∈ Small, ∀ y, a + evalSim Γ (fun j ↦ ((∑ i, w i • WT.1 i) + B * (Matrix.of fun a c ↦ bitVal (xs c a) : Matrix (Fin m) (Fin mW) K)) * TW WT.2 j)
        w (fun j ↦ (Matrix.of fun a c ↦ bitVal (xs c a) : Matrix (Fin m) (Fin mW) K) * TW WT.2 j - ∑ i, w i • TB WT.2 i j) φ *ᵥ dec (-y) ∈ Big)
    (d₀ d₁ : Fin mW → K) :
    let ordinary : Matrix (Option (Fin n)) (Fin m) K → Matrix (Fin n) (Fin m) K := fun A i ↦ A (some i)
    let key := fun A xs ↦ (S (ordinary A)).bind fun WT ↦
      (if good WT.2 then boxSample Big hBig Small (Matrix.mulVecLin (ordinary A)).toAddMonoidHom
        (fun y ↦ dec (-y)) (fun z ↦ evalSim Γ (fun j ↦ ((∑ i, w i • WT.1 i) +
          ordinary A * (Matrix.of fun a c ↦ bitVal (xs c a) : Matrix (Fin m) (Fin mW) K)) * TW WT.2 j) w
          (fun j ↦ (Matrix.of fun a c ↦ bitVal (xs c a) : Matrix (Fin m) (Fin mW) K) * TW WT.2 j - ∑ i, w i • TB WT.2 i j) φ *ᵥ z) u
        else PMF.pure none).map fun k ↦ (WT,k)
    let run := fun (d : Fin mW → K) ↦
      (PMF.uniformOfFintype (Matrix (Option (Fin n)) (Fin m) K)).bind fun A ↦
        (Cslib.Probability.PMF.pi fun _ : Fin mW ↦ PMF.uniformOfFintype (Fin m → Bool)).bind fun xs ↦
          (key A xs).map fun k ↦ (A, fun i j ↦ binaryHash A (xs i) (some j), k,
            fun i ↦ d i + binaryHash A (xs i) none)
    let ε := ENNReal.ofReal ((mW : ℝ) * (Real.sqrt
      ((Fintype.card K : ℝ) ^ (n+1) * (2 ^ m : ℝ)⁻¹) / 2))
    CloseTo (run d₀) (run d₁) (ε+ε) := by
  intro B key run ε
  let Tr := fun A (WT : (Fin ℓ → Matrix (Fin n) (Fin mW) K) × Tt) xs ↦
    evalSim Γ (fun j ↦ ((∑ i, w i • WT.1 i) + B A * binOf xs) * TW WT.2 j) w
      (fun j ↦ binOf xs * TW WT.2 j - ∑ i, w i • TB WT.2 i j) φ
  let pub := fun (_ : Matrix (Option (Fin n)) (Fin m) K)
      (WT : (Fin ℓ → Matrix (Fin n) (Fin mW) K) × Tt) (H : Fin mW → Fin n → K) z ↦
    evalMat Γ (fun j ↦ ((∑ i, w i • WT.1 i) + ofCols H) * TW WT.2 j) φ *ᵥ z
  apply box_mask (fun A ↦ S (B A)) (fun WT ↦ good WT.2) Big Small hBig
    (fun A ↦ (Matrix.mulVecLin (B A)).toAddMonoidHom)
    (fun z ↦ -(Γ.G *ᵥ z)) (fun y ↦ dec (-y)) (fun y ↦ by simp [hdec]) u
    (fun A WT xs z ↦ Tr A WT xs *ᵥ z) pub _ (fun A WT h hg xs ↦ hcov _ WT h hg xs) d₀ d₁
  intro A WT hWT hg xs z
  let R : Matrix (Fin m) (Fin mW) K := binOf xs
  have hA : ∀ j, ((∑ i, w i • WT.1 i) + B A * R) * TW WT.2 j =
      B A * (R * TW WT.2 j - ∑ i, w i • TB WT.2 i j) + w j • Γ.G := by
    intro j
    have hW : ∀ i, WT.1 i * TW WT.2 j = (if i = j then Γ.G else 0) - B A * TB WT.2 i j :=
      fun i ↦ eq_sub_of_add_eq' (hblock _ WT hWT hg i j)
    rw [Matrix.add_mul, Matrix.sum_mul, Matrix.mul_sub, Matrix.mul_sum, Matrix.mul_assoc]
    simp_rw [Matrix.smul_mul, hW, smul_sub, Matrix.mul_smul]
    rw [Finset.sum_sub_distrib]
    simp [smul_ite, Finset.sum_ite_eq']
    abel
  have h := sim_relation Γ (B A) _ w _ hA φ
  rw [hφw, zero_smul, add_zero] at h
  change B A *ᵥ (Tr A WT xs *ᵥ z) = _
  rw [Matrix.mulVec_mulVec]
  change ((B A * evalSim Γ _ w _ φ) *ᵥ z) = _
  rw [← h]
  have hh : B A * R = ofCols (fun i j ↦ binaryHash A (xs i) (some j)) := mul_binOf (B A) xs
  simp only [pub, hh]
