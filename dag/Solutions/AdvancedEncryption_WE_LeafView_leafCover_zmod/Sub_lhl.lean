import SigabaNeoStd.Lattices.BoxSampler
import SigabaNeoStd.Lattices.LeftoverHash
import SigabaNeoStd.Lattices.Homomorphic.Eval
import CslibFrontier.Probability.Product
import SigabaNeoStd.Lattices.Boxes
import SigabaNeoStd.Lattices.Homomorphic.NoiseBound

open Matrix SigabaNeo.Lattices Cslib Cslib.Probability
open scoped ENNReal

namespace LeafViewAux

open Matrix SigabaNeo.Lattices Cslib
open Cslib.Probability
open scoped ENNReal

/-- Product of pushed-forward laws is the pushforward of the product. -/
theorem pi_map {ι : Type} [Fintype ι] [DecidableEq ι] {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq β] (p : PMF α) (f : α → β) :
    Cslib.Probability.PMF.pi (fun _ : ι => p.map f) =
      (Cslib.Probability.PMF.pi fun _ : ι => p).map fun xs i => f (xs i) := by
  classical
  ext o
  rw [Cslib.Probability.PMF.pi_apply, PMF.map_apply, tsum_fintype]
  simp_rw [PMF.map_apply, tsum_fintype, Cslib.Probability.PMF.pi_apply]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun xs _ => ?_
  by_cases h : o = fun i => f (xs i)
  · subst h; simp
  · simp only [h, ite_false]
    obtain ⟨i, hi⟩ : ∃ i, o i ≠ f (xs i) := by
      by_contra hc; exact h (funext fun i => not_not.mp fun hn => hc ⟨i, hn⟩)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])


/-- Binding a uniform matrix shifted by a constant gives the same law. -/
theorem uniform_bind_add {α β : Type} [Fintype α] [Nonempty α] [AddGroup α] (d : α)
    (g : α → PMF β) :
    (PMF.uniformOfFintype α).bind (fun H => g (d + H)) = (PMF.uniformOfFintype α).bind g := by
  ext b
  simp only [PMF.bind_apply, PMF.uniformOfFintype_apply, tsum_fintype]
  exact Fintype.sum_equiv (Equiv.addLeft d) _ _ (fun _ => rfl)

theorem bind_congr_support {α β : Type} (p : PMF α) {f g : α → PMF β}
    (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  ext b
  simp only [PMF.bind_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · rw [(PMF.apply_eq_zero_iff _ _).mpr ha]; simp

section Main

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

/-- **The leaf view is simulated up to the leftover hash lemma, with no trapdoor for `B`.**

Real (attribute `0`): `B` uniform, `R` binary, `(W, T) ← S(B)`, `A = B R`; if the public check
`good T` passes, the leaf key is one try of box rejection for `[B | A_φ − G]` with the
simulation trapdoor `R_φ^{(0)}` (`φ(0) = 0`), otherwise `⊥`.
Simulated (attribute `w` with `φ(w) = 0`): `A = Σ w_i W_i + B R` and the trapdoor
`R_φ^{(w)}` built from `R T_W[j] − Σ_i w_i T_B[i,j]`.
The two views `(B, W, T, A, key)` are within twice the leftover-hash bound. -/
theorem leafView_close (Γ : GadgetMatrix K (Fin n) (Fin k)) (dec : (Fin n → K) → (Fin k → K))
    (hdec : ∀ y, Γ.G *ᵥ dec y = y) (Big Small : Finset (Fin m → K)) (hBig : Big.Nonempty)
    (u : Fin n → K) (φ : Circuit (Fin ℓ)) (w : Fin ℓ → K) (hφ0 : φ.eval (0 : Fin ℓ → K) = 0)
    (hφw : φ.eval w = 0) [NeZero m]
    (S : Matrix (Fin n) (Fin m) K → PMF ((Fin ℓ → Matrix (Fin n) (Fin mW) K) × Tt))
    (good : Tt → Prop) [DecidablePred good]
    (TB : Tt → Fin ℓ → Fin ℓ → Matrix (Fin m) (Fin k) K) (TW : Tt → Fin ℓ → Matrix (Fin mW) (Fin k) K)
    (hblock : ∀ B, ∀ WT ∈ (S B).support, good WT.2 → ∀ i j,
      B * TB WT.2 i j + WT.1 i * TW WT.2 j = if i = j then Γ.G else 0)
    (hcov : ∀ B, ∀ WT ∈ (S B).support, good WT.2 → ∀ R : Matrix (Fin m) (Fin mW) K,
      (∀ a c, R a c = 0 ∨ R a c = 1) →
      (∀ x ∈ Small, ∀ y, x + evalSim Γ (fun j => (B * R) * TW WT.2 j) 0
          (fun j => R * TW WT.2 j) φ *ᵥ dec (-y) ∈ Big) ∧
      (∀ x ∈ Small, ∀ y, x + evalSim Γ (fun j => ((∑ i, w i • WT.1 i) + B * R) * TW WT.2 j) w
          (fun j => R * TW WT.2 j - ∑ i, w i • TB WT.2 i j) φ *ᵥ dec (-y) ∈ Big)) :
    CloseTo
      ((PMF.uniformOfFintype (Matrix (Fin n) (Fin m) K)).bind fun B =>
        (Cslib.Probability.PMF.pi fun _ : Fin mW => PMF.uniformOfFintype (Fin m → Bool)).bind
          fun xs => (S B).bind fun WT =>
            (if good WT.2 then
              boxSample Big hBig Small (Matrix.mulVecLin B).toAddMonoidHom (fun y => dec (-y))
                (fun z => evalSim Γ (fun j => (B * binOf xs) * TW WT.2 j) 0
                  (fun j => binOf xs * TW WT.2 j) φ *ᵥ z) u
            else PMF.pure none).map fun key => (B, WT, B * binOf xs, key))
      ((PMF.uniformOfFintype (Matrix (Fin n) (Fin m) K)).bind fun B =>
        (Cslib.Probability.PMF.pi fun _ : Fin mW => PMF.uniformOfFintype (Fin m → Bool)).bind
          fun xs => (S B).bind fun WT =>
            (if good WT.2 then
              boxSample Big hBig Small (Matrix.mulVecLin B).toAddMonoidHom (fun y => dec (-y))
                (fun z => evalSim Γ (fun j => ((∑ i, w i • WT.1 i) + B * binOf xs) * TW WT.2 j) w
                  (fun j => binOf xs * TW WT.2 j - ∑ i, w i • TB WT.2 i j) φ *ᵥ z) u
            else PMF.pure none).map fun key => (B, WT, (∑ i, w i • WT.1 i) + B * binOf xs, key))
      (ENNReal.ofReal (mW * (Real.sqrt ((Fintype.card K : ℝ) ^ n * (2 ^ m : ℝ)⁻¹) / 2)) +
        ENNReal.ofReal (mW * (Real.sqrt ((Fintype.card K : ℝ) ^ n * (2 ^ m : ℝ)⁻¹) / 2))) := by
  -- the trapdoor-free leaf key: box rejection with any covered trapdoor of `A_φ`
  let keyI : Matrix (Fin n) (Fin m) K → Matrix (Fin n) (Fin k) K → PMF (Option ((Fin m → K) × (Fin k → K))) :=
    fun B Aφ => @dite _ (∃ Tr : Matrix (Fin m) (Fin k) K, B * Tr = Aφ ∧
        ∀ x ∈ Small, ∀ y, x + Tr *ᵥ dec (-y) ∈ Big) (Classical.propDecidable _) (fun h =>
      boxSample Big hBig Small (Matrix.mulVecLin B).toAddMonoidHom (fun y => dec (-y))
        (fun z => h.choose *ᵥ z) u) (fun _ => PMF.pure none)
  /-if h : ∃ Tr : Matrix (Fin m) (Fin k) K, B * Tr = Aφ ∧
        ∀ x ∈ Small, ∀ y, x + Tr *ᵥ dec (-y) ∈ Big then
      boxSample Big hBig Small (Matrix.mulVecLin B).toAddMonoidHom (fun y => dec (-y))
        (fun z => h.choose *ᵥ z) u
    else PMF.pure none-/
  have hkeyI : ∀ (B : Matrix (Fin n) (Fin m) K) (Aφ : Matrix (Fin n) (Fin k) K) (Tr : Matrix (Fin m) (Fin k) K), B * Tr = Aφ →
      (∀ x ∈ Small, ∀ y, x + Tr *ᵥ dec (-y) ∈ Big) →
      boxSample Big hBig Small (Matrix.mulVecLin B).toAddMonoidHom (fun y => dec (-y))
        (fun z => Tr *ᵥ z) u = keyI B Aφ := by
    intro B Aφ Tr hTr hc
    have hex : ∃ Tr : Matrix (Fin m) (Fin k) K, B * Tr = Aφ ∧
        ∀ x ∈ Small, ∀ y, x + Tr *ᵥ dec (-y) ∈ Big := ⟨Tr, hTr, hc⟩
    simp only [keyI, hex, ↓reduceDIte]
    refine boxSample_eq Big hBig Small _ (fun z => -(Γ.G *ᵥ z)) (fun y => dec (-y))
      (fun y => by simp [hdec]) _ _ u (fun x hx y => hc x hx y)
      (fun x hx y => hex.choose_spec.2 x hx y) fun z => ?_
    simp only [LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hTr,
      hex.choose_spec.1]
  -- the continuation, a function of `B` and the hashes only
  let Φ : Matrix (Fin n) (Fin m) K → (Fin ℓ → Matrix (Fin n) (Fin mW) K) × Tt →
      Matrix (Fin n) (Fin mW) K → PMF _ :=
    fun B WT A => (if good WT.2 then keyI B (evalMat Γ (fun j => A * TW WT.2 j) φ)
        else PMF.pure none).map fun key => (B, WT, A, key)
  let F : ((Fin ℓ → Matrix (Fin n) (Fin mW) K) → Matrix (Fin n) (Fin mW) K) →
      Matrix (Fin n) (Fin m) K → (Fin mW → Fin n → K) → PMF _ :=
    fun c B H => (S B).bind fun WT => Φ B WT (c WT.1 + ofCols H)
  have hreal : ∀ (c : (Fin ℓ → Matrix (Fin n) (Fin mW) K) → Matrix (Fin n) (Fin mW) K)
      (Rφ : Matrix (Fin n) (Fin m) K → (Fin ℓ → Matrix (Fin n) (Fin mW) K) → Tt →
        Matrix (Fin m) (Fin mW) K → Matrix (Fin m) (Fin k) K),
      (∀ B, ∀ WT ∈ (S B).support, good WT.2 → ∀ R : Matrix (Fin m) (Fin mW) K,
        (∀ a c, R a c = 0 ∨ R a c = 1) →
        B * Rφ B WT.1 WT.2 R = evalMat Γ (fun j => (c WT.1 + B * R) * TW WT.2 j) φ ∧
        ∀ x ∈ Small, ∀ y, x + Rφ B WT.1 WT.2 R *ᵥ dec (-y) ∈ Big) →
      ((PMF.uniformOfFintype (Matrix (Fin n) (Fin m) K)).bind fun B =>
        (Cslib.Probability.PMF.pi fun _ : Fin mW => PMF.uniformOfFintype (Fin m → Bool)).bind
          fun xs => (S B).bind fun WT =>
            (if good WT.2 then
              boxSample Big hBig Small (Matrix.mulVecLin B).toAddMonoidHom (fun y => dec (-y))
                (fun z => Rφ B WT.1 WT.2 (binOf xs) *ᵥ z) u
            else PMF.pure none).map fun key => (B, WT, c WT.1 + B * binOf xs, key)) =
      ((PMF.uniformOfFintype (Matrix (Fin n) (Fin m) K)).bind fun B =>
        (Cslib.Probability.PMF.pi fun _ : Fin mW =>
          (PMF.uniformOfFintype (Fin m → Bool)).map (binaryHash B)).bind (F c B)) := by
    intro c Rφ hR
    refine congrArg _ (funext fun B => ?_)
    rw [pi_map, PMF.bind_map]
    refine congrArg _ (funext fun xs => ?_)
    simp only [Function.comp_def, F, Φ]
    refine bind_congr_support _ fun WT hWT => ?_
    rw [← mul_binOf]
    by_cases hg : good WT.2
    · have hbin : ∀ a c, (binOf xs : Matrix (Fin m) (Fin mW) K) a c = 0 ∨
          (binOf xs : Matrix (Fin m) (Fin mW) K) a c = 1 := by
        intro a c; simp only [binOf, Matrix.of_apply, bitVal]; split_ifs <;> simp
      obtain ⟨h1, h2⟩ := hR B WT hWT hg _ hbin
      simp only [hg, ↓reduceIte, hkeyI B _ _ h1 h2]
    · simp only [hg, ↓reduceIte]
  -- the two experiments in hash form
  have e1 := hreal (fun _ => 0)
    (fun B _ T R => evalSim Γ (fun j => (B * R) * TW T j) 0 (fun j => R * TW T j) φ)
    (by
      intro B WT hWT hg R hR
      refine ⟨?_, by simpa using (hcov B WT hWT hg R hR).1⟩
      have h := sim_relation Γ B (fun j => (B * R) * TW WT.2 j) (0 : Fin ℓ → K)
        (fun j => R * TW WT.2 j) (fun j => by simp [Matrix.mul_assoc]) φ
      rw [hφ0, zero_smul, add_zero] at h
      simp only [zero_add]
      exact h.symm)
  have e2 := hreal (fun W => ∑ i, w i • W i)
    (fun B W T R => evalSim Γ (fun j => ((∑ i, w i • W i) + B * R) * TW T j) w
      (fun j => R * TW T j - ∑ i, w i • TB T i j) φ)
    (by
      intro B WT hWT hg R hR
      refine ⟨?_, (hcov B WT hWT hg R hR).2⟩
      have hA : ∀ j, ((∑ i, w i • WT.1 i) + B * R) * TW WT.2 j =
          B * (R * TW WT.2 j - ∑ i, w i • TB WT.2 i j) + w j • Γ.G := by
        intro j
        have hW : ∀ i, WT.1 i * TW WT.2 j = (if i = j then Γ.G else 0) - B * TB WT.2 i j :=
          fun i => eq_sub_of_add_eq' (hblock B WT hWT hg i j)
        rw [Matrix.add_mul, Matrix.sum_mul, Matrix.mul_sub, Matrix.mul_sum, Matrix.mul_assoc]
        simp_rw [Matrix.smul_mul, hW, smul_sub, Matrix.mul_smul]
        rw [Finset.sum_sub_distrib]
        simp [smul_ite, Finset.sum_ite_eq']
        abel
      have h := sim_relation Γ B _ w _ hA φ
      rw [hφw, zero_smul, add_zero] at h
      exact h.symm)
  simp only [zero_add] at e1
  rw [e1, e2]
  have hε : ((Fintype.card (Fin mW) : ℝ) * (Real.sqrt (Fintype.card (Fin n → K) *
      (2 ^ Fintype.card (Fin m) : ℝ)⁻¹) / 2)) =
      mW * (Real.sqrt ((Fintype.card K : ℝ) ^ n * (2 ^ m : ℝ)⁻¹) / 2) := by
    simp [Fintype.card_fin]
  have lhl : ∀ c, CloseTo
      ((PMF.uniformOfFintype (Matrix (Fin n) (Fin m) K)).bind fun B =>
        (Cslib.Probability.PMF.pi fun _ : Fin mW =>
          (PMF.uniformOfFintype (Fin m → Bool)).map (binaryHash B)).bind (F c B))
      ((PMF.uniformOfFintype (Matrix (Fin n) (Fin m) K)).bind fun B =>
        (Cslib.Probability.PMF.pi fun _ : Fin mW => PMF.uniformOfFintype (Fin n → K)).bind (F c B))
      (ENNReal.ofReal (mW * (Real.sqrt ((Fintype.card K : ℝ) ^ n * (2 ^ m : ℝ)⁻¹) / 2))) := by
    intro c
    rw [← hε]
    exact closeTo_binaryHash_bind (R := K) (rr := Fin n) (mm := Fin m) (I := Fin mW) (F c)
  have hid : ((PMF.uniformOfFintype (Matrix (Fin n) (Fin m) K)).bind fun B =>
        (Cslib.Probability.PMF.pi fun _ : Fin mW => PMF.uniformOfFintype (Fin n → K)).bind
          (F (fun _ => 0) B)) =
      ((PMF.uniformOfFintype (Matrix (Fin n) (Fin m) K)).bind fun B =>
        (Cslib.Probability.PMF.pi fun _ : Fin mW => PMF.uniformOfFintype (Fin n → K)).bind
          (F (fun W => ∑ i, w i • W i) B)) := by
    refine congrArg _ (funext fun B => ?_)
    rw [Cslib.Probability.PMF.pi_uniformOfFintype]
    simp only [F]
    conv_lhs => rw [PMF.bind_comm]
    conv_rhs => rw [PMF.bind_comm]
    refine congrArg _ (funext fun WT => ?_)
    have hc : ∀ H : Fin mW → Fin n → K, (∑ i, w i • WT.1 i) + ofCols H =
        ofCols ((fun col a => (∑ i, w i • WT.1 i) a col) + H) := by
      intro H; ext a col; simp [ofCols]
    simp only [zero_add, hc]
    exact (uniform_bind_add _ (fun H => Φ B WT (ofCols H))).symm
  have l1 := lhl (fun _ => 0)
  have l2 := (lhl (fun W => ∑ i, w i • W i)).symm
  rw [← hid] at l2
  exact l1.trans l2

end Main

section Cover

variable {q n m k ℓ : ℕ} [NeZero q]

theorem zabs_mul_mat_le {a b c : Type*} [Fintype b] (M : Matrix a b (ZMod q))
    (X : Matrix b c (ZMod q)) (E D : ℕ) (hM : ∀ i j, zabs (M i j) ≤ E)
    (hX : ∀ i j, zabs (X i j) ≤ D) (i : a) (j : c) :
    zabs ((M * X) i j) ≤ Fintype.card b * E * D := by
  rw [Matrix.mul_apply]
  refine (zabs_sum_le _ _).trans ?_
  calc ∑ l, zabs (M i l * X l j) ≤ ∑ _l : b, E * D := Finset.sum_le_sum fun l _ =>
        (zabs_mul_le _ _).trans (Nat.mul_le_mul (hM i l) (hX l j))
    _ = Fintype.card b * E * D := by simp [mul_assoc]

/-- **The entries of a simulation trapdoor over `ℤ_q`**: with decompositions of norm at most `1`,
`0/1` inputs and input trapdoors with entries at most `E`, every entry of `evalSim` is at most
`errBound k E φ`. -/
theorem zabs_evalSim_le (Γ : GadgetMatrix (ZMod q) (Fin n) (Fin k))
    (hΓ : ∀ A c c', zabs (Γ.ginv A c c') ≤ 1) (A : Fin ℓ → Matrix (Fin n) (Fin k) (ZMod q))
    (x : Fin ℓ → ZMod q) (hx : ∀ j, x j = 0 ∨ x j = 1)
    (Wm : Fin ℓ → Matrix (Fin m) (Fin k) (ZMod q)) (E : ℕ) (hW : ∀ j a c, zabs (Wm j a c) ≤ E)
    (φ : Circuit (Fin ℓ)) (a : Fin m) (c : Fin k) :
    zabs (evalSim Γ A x Wm φ a c) ≤ errBound k E φ := by
  induction φ generalizing a c with
  | input j => exact hW j a c
  | one => simp [evalSim, errBound, zabs_zero]
  | nand f g ihf ihg =>
    simp only [evalSim, errBound, Matrix.neg_apply, zabs_neg, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul]
    refine (zabs_add_le _ _).trans (Nat.add_le_add ?_ ?_)
    · have h := zabs_mul_mat_le (evalSim Γ A x Wm f) (Γ.ginv (evalMat Γ A g)) _ 1
        (fun i j => ihf i j) (hΓ _) a c
      simpa using h
    · rcases Circuit.eval_bit x hx f with h | h <;> rw [h]
      · simp [zabs_zero]
      · simpa using ihg a c

/-- **Coverage over `ℤ_q`**: with gadget decompositions and `dec` of entries at most `1`, bit
inputs `x` and input trapdoors `Wm` with entries at most `E`, the simulation trapdoor
`evalSim Γ A x Wm φ` keeps `ball s` in the big box of `Bb` bits when
`s + k · errBound k E φ ≤ 2^{Bb−1} − 1`. -/
theorem leafCover_zmod (Γ : GadgetMatrix (ZMod q) (Fin n) (Fin k))
    (hΓ : ∀ A c c', zabs (Γ.ginv A c c') ≤ 1) (dec : (Fin n → ZMod q) → (Fin k → ZMod q))
    (hdecN : ∀ y c, zabs (dec y c) ≤ 1) (A : Fin ℓ → Matrix (Fin n) (Fin k) (ZMod q))
    (x : Fin ℓ → ZMod q) (hx : ∀ j, x j = 0 ∨ x j = 1)
    (Wm : Fin ℓ → Matrix (Fin m) (Fin k) (ZMod q)) (E : ℕ) (hW : ∀ j a c, zabs (Wm j a c) ≤ E)
    (φ : Circuit (Fin ℓ)) (Bb s : ℕ) (hB : 2 ^ Bb ≤ q) (hB1 : 1 ≤ Bb)
    (hs : s + k * errBound k E φ ≤ 2 ^ (Bb - 1) - 1) :
    ∀ v ∈ (ball q s : Finset (Fin m → ZMod q)), ∀ y,
      v + evalSim Γ A x Wm φ *ᵥ dec (-y) ∈ (bigBox Bb hB : Finset (Fin m → ZMod q)) := by
  intro v hv y
  refine ball_subset_bigBox Bb hB hB1 (mem_ball.mpr fun a => ?_)
  rw [mem_ball] at hv
  have h := zabs_mul_mat_le (evalSim Γ A x Wm φ) (Matrix.of fun c (_ : Fin 1) => dec (-y) c)
    _ 1 (zabs_evalSim_le Γ hΓ A x hx Wm E hW φ) (fun i _ => hdecN _ i) a 0
  simp only [Fintype.card_fin, mul_one] at h
  have h' : (evalSim Γ A x Wm φ *ᵥ dec (-y)) a =
      (evalSim Γ A x Wm φ * Matrix.of fun c (_ : Fin 1) => dec (-y) c) a 0 := by
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  simp only [Pi.add_apply]
  refine (zabs_add_le _ _).trans ?_
  rw [h']
  have := hv a
  omega

end Cover


section Zmod

variable {q n m mW k ℓ : ℕ} [NeZero q] {Tt : Type}

/-- **The leaf view over `ℤ_q` with norm-checked trapdoors.** The public check `good T` bounds the
entries of `T_B`, `T_W` by `E_T`; with bit attributes, `φ(0) = φ(w) = 0`, small box `ball s` and
big box of `Bb` bits with `s + k · errBound k ((m_W + ℓ) E_T) φ ≤ 2^{Bb−1} − 1`, the real view
(attribute `0`, no trapdoor for `B`) and the simulated view (attribute `w`) are within twice the
leftover-hash bound `m_W √(q^n / 2^m) / 2`. -/
theorem leafView_close_zmod (Γ : GadgetMatrix (ZMod q) (Fin n) (Fin k))
    (hΓ : ∀ A c c', zabs (Γ.ginv A c c') ≤ 1) (dec : (Fin n → ZMod q) → (Fin k → ZMod q))
    (hdec : ∀ y, Γ.G *ᵥ dec y = y) (hdecN : ∀ y c, zabs (dec y c) ≤ 1)
    (Bb s : ℕ) (hB : 2 ^ Bb ≤ q) (hB1 : 1 ≤ Bb)
    (hBig : (bigBox Bb hB : Finset (Fin m → ZMod q)).Nonempty)
    (u : Fin n → ZMod q) (φ : Circuit (Fin ℓ)) (w : Fin ℓ → ZMod q) (hw : ∀ i, w i = 0 ∨ w i = 1)
    (hφ0 : φ.eval (0 : Fin ℓ → ZMod q) = 0) (hφw : φ.eval w = 0) [NeZero m]
    (S : Matrix (Fin n) (Fin m) (ZMod q) → PMF ((Fin ℓ → Matrix (Fin n) (Fin mW) (ZMod q)) × Tt))
    (good : Tt → Prop) [DecidablePred good]
    (TB : Tt → Fin ℓ → Fin ℓ → Matrix (Fin m) (Fin k) (ZMod q))
    (TW : Tt → Fin ℓ → Matrix (Fin mW) (Fin k) (ZMod q))
    (hblock : ∀ B, ∀ WT ∈ (S B).support, good WT.2 → ∀ i j,
      B * TB WT.2 i j + WT.1 i * TW WT.2 j = if i = j then Γ.G else 0)
    (ET : ℕ) (hgood : ∀ T, good T →
      (∀ i j a c, zabs (TB T i j a c) ≤ ET) ∧ ∀ j a c, zabs (TW T j a c) ≤ ET)
    (hs : s + k * errBound k ((mW + ℓ) * ET) φ ≤ 2 ^ (Bb - 1) - 1) :
    CloseTo
      ((PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))).bind fun B =>
        (Cslib.Probability.PMF.pi fun _ : Fin mW => PMF.uniformOfFintype (Fin m → Bool)).bind
          fun xs => (S B).bind fun WT =>
            (if good WT.2 then
              boxSample (bigBox Bb hB) hBig (ball q s)
                (Matrix.mulVecLin B).toAddMonoidHom (fun y => dec (-y))
                (fun z => evalSim Γ (fun j => (B * binOf xs) * TW WT.2 j) 0
                  (fun j => binOf xs * TW WT.2 j) φ *ᵥ z) u
            else PMF.pure none).map fun key => (B, WT, B * binOf xs, key))
      ((PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))).bind fun B =>
        (Cslib.Probability.PMF.pi fun _ : Fin mW => PMF.uniformOfFintype (Fin m → Bool)).bind
          fun xs => (S B).bind fun WT =>
            (if good WT.2 then
              boxSample (bigBox Bb hB) hBig (ball q s)
                (Matrix.mulVecLin B).toAddMonoidHom (fun y => dec (-y))
                (fun z => evalSim Γ (fun j => ((∑ i, w i • WT.1 i) + B * binOf xs) * TW WT.2 j) w
                  (fun j => binOf xs * TW WT.2 j - ∑ i, w i • TB WT.2 i j) φ *ᵥ z) u
            else PMF.pure none).map fun key => (B, WT, (∑ i, w i • WT.1 i) + B * binOf xs, key))
      (ENNReal.ofReal (mW * (Real.sqrt ((q : ℝ) ^ n * (2 ^ m : ℝ)⁻¹) / 2)) +
        ENNReal.ofReal (mW * (Real.sqrt ((q : ℝ) ^ n * (2 ^ m : ℝ)⁻¹) / 2))) := by
  have h := leafView_close Γ dec hdec (bigBox Bb hB) (ball q s) hBig u φ w
    hφ0 hφw S good TB TW hblock ?_
  · simpa [ZMod.card] using h
  intro B WT hWT hg R hR
  obtain ⟨hTB, hTW⟩ := hgood WT.2 hg
  have hRle : ∀ a c, zabs (R a c) ≤ 1 := fun a c => by
    rcases hR a c with h | h <;> rw [h]
    · simp [zabs_zero]
    · exact zabs_one_le
  have hRT : ∀ j a c, zabs ((R * TW WT.2 j) a c) ≤ mW * ET := fun j a c => by
    simpa using zabs_mul_mat_le R (TW WT.2 j) 1 ET hRle (hTW j) a c
  constructor
  · refine leafCover_zmod Γ hΓ dec hdecN _ 0 (fun _ => Or.inl rfl) _ ((mW + ℓ) * ET)
      (fun j a c => (hRT j a c).trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))
      φ Bb s hB hB1 hs
  · refine leafCover_zmod Γ hΓ dec hdecN _ w hw _ ((mW + ℓ) * ET) (fun j a c => ?_)
      φ Bb s hB hB1 hs
    simp only [Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    refine (zabs_sub_le _ _).trans ?_
    rw [add_mul]
    refine Nat.add_le_add (hRT j a c) ((zabs_sum_le _ _).trans ?_)
    calc ∑ i, zabs (w i * TB WT.2 i j a c) ≤ ∑ _i : Fin ℓ, ET := Finset.sum_le_sum fun i _ => by
          refine (zabs_mul_le _ _).trans ?_
          rcases hw i with h | h <;> rw [h]
          · simp [zabs_zero]
          · simpa using Nat.mul_le_mul zabs_one_le (hTB i j a c)
      _ = ℓ * ET := by simp

end Zmod

end LeafViewAux


theorem solution {q n m k ℓ : ℕ} [NeZero q] (Γ : GadgetMatrix (ZMod q) (Fin n) (Fin k))
    (hΓ : ∀ A c c', zabs (Γ.ginv A c c') ≤ 1) (dec : (Fin n → ZMod q) → (Fin k → ZMod q))
    (hdecN : ∀ y c, zabs (dec y c) ≤ 1) (A : Fin ℓ → Matrix (Fin n) (Fin k) (ZMod q))
    (x : Fin ℓ → ZMod q) (hx : ∀ j, x j = 0 ∨ x j = 1)
    (Wm : Fin ℓ → Matrix (Fin m) (Fin k) (ZMod q)) (E : ℕ) (hW : ∀ j a c, zabs (Wm j a c) ≤ E)
    (φ : Circuit (Fin ℓ)) (Bb s : ℕ) (hB : 2 ^ Bb ≤ q) (hB1 : 1 ≤ Bb)
    (hs : s + k * errBound k E φ ≤ 2 ^ (Bb - 1) - 1) :
    ∀ v ∈ (ball q s : Finset (Fin m → ZMod q)), ∀ y,
      v + evalSim Γ A x Wm φ *ᵥ dec (-y) ∈ (bigBox Bb hB : Finset (Fin m → ZMod q)) :=
  LeafViewAux.leafCover_zmod Γ hΓ dec hdecN A x hx Wm E hW φ Bb s hB hB1 hs
