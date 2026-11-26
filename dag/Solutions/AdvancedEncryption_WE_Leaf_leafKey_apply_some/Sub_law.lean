import SigabaNeoStd.Lattices.BoxSampler
import Definitions.Def_RingBoxesCopy
import SigabaNeoStd.Lattices.SimNorm
import SigabaNeoStd.Lattices.Homomorphic.Eval
import Mathlib.Tactic.Abel

open Matrix SigabaNeo.Lattices Cslib AdvancedEncryption.WE.RingBoxesCopy
open scoped ENNReal

namespace LeafKeyAux

open Matrix SigabaNeo.Lattices Cslib
open scoped ENNReal

section Generic

variable {K : Type*} [CommRing K] [DecidableEq K] {n m k : ℕ}

open Classical in
/-- **The law of the leaf key is explicit**: for every trapdoor `T` of `[B | A]` covered by the
boxes, an output `(x, z)` has probability `1 / |Big|` if `x ∈ Small`, `z` is a decomposition and
`B x + A z = u`, and `0` otherwise. -/
theorem leafKey_apply_some (G : Matrix (Fin n) (Fin k) K) (dec : (Fin n → K) → (Fin k → K))
    (hdec : ∀ y, G *ᵥ dec y = y) (B : Matrix (Fin n) (Fin m) K) (A : Matrix (Fin n) (Fin k) K)
    (T : (Fin k → K) → (Fin m → K)) (hT : ∀ z, B *ᵥ T z = (A + G) *ᵥ z)
    (Big Small : Finset (Fin m → K)) (hBig : Big.Nonempty)
    (hcov : ∀ x ∈ Small, ∀ y, x + T (dec (-y)) ∈ Big) (u : Fin n → K)
    (x : Fin m → K) (z : Fin k → K) :
    boxSample Big hBig Small (Matrix.mulVecLin B).toAddMonoidHom (fun y => dec (-y)) T u
        (some (x, z)) =
      if x ∈ Small ∧ (∃ y, dec y = z) ∧ B *ᵥ x + A *ᵥ z = u then (Big.card : ℝ≥0∞)⁻¹ else 0 := by
  rw [boxSample_some Big hBig Small (Matrix.mulVecLin B).toAddMonoidHom (fun z => -(G *ᵥ z))
    (fun y => dec (-y)) (fun y => by simp [hdec]) T u hcov]
  refine if_congr ?_ rfl rfl
  simp only [boxTarget, LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply, hT, Matrix.add_mulVec]
  constructor
  · rintro ⟨h1, ⟨y, hy⟩, h3⟩
    exact ⟨h1, ⟨-y, hy⟩, by rw [← h3]; abel⟩
  · rintro ⟨h1, ⟨y, hy⟩, h3⟩
    exact ⟨h1, ⟨-y, by simpa using hy⟩, by rw [← h3]; abel⟩

/-- **Exact simulation of the leaf key.** If `B Tm = G` and `A = B R − G`, the leaf-key law with
the real trapdoor `Tm · G⁻¹(A + G)` of `B` equals the law with the `−G` trapdoor `R`, provided
the big box covers both shifts. -/
theorem leafKey_real_eq_sim (Γ : GadgetMatrix K (Fin n) (Fin k))
    (dec : (Fin n → K) → (Fin k → K)) (hdec : ∀ y, Γ.G *ᵥ dec y = y)
    (B : Matrix (Fin n) (Fin m) K) (Tm : Matrix (Fin m) (Fin k) K) (hTm : B * Tm = Γ.G)
    (R : Matrix (Fin m) (Fin k) K) (A : Matrix (Fin n) (Fin k) K) (hA : A = B * R - Γ.G)
    (Big Small : Finset (Fin m → K)) (hBig : Big.Nonempty)
    (hcov : ∀ x ∈ Small, ∀ y, x + (Tm * Γ.ginv (A + Γ.G)) *ᵥ dec (-y) ∈ Big)
    (hcov' : ∀ x ∈ Small, ∀ y, x + R *ᵥ dec (-y) ∈ Big) (u : Fin n → K) :
    boxSample Big hBig Small (Matrix.mulVecLin B).toAddMonoidHom (fun y => dec (-y))
        (fun z => (Tm * Γ.ginv (A + Γ.G)) *ᵥ z) u =
      boxSample Big hBig Small (Matrix.mulVecLin B).toAddMonoidHom (fun y => dec (-y))
        (fun z => R *ᵥ z) u := by
  have hreal : ∀ z, B *ᵥ ((Tm * Γ.ginv (A + Γ.G)) *ᵥ z) = (A + Γ.G) *ᵥ z := by
    intro z
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hTm, Γ.mul_ginv]
  have hsim : ∀ z, B *ᵥ (R *ᵥ z) = (A + Γ.G) *ᵥ z := by
    intro z
    rw [Matrix.mulVec_mulVec, hA, sub_add_cancel]
  refine PMF.ext_option fun ⟨x, z⟩ => ?_
  rw [leafKey_apply_some Γ.G dec hdec B A _ hreal Big Small hBig hcov,
    leafKey_apply_some Γ.G dec hdec B A _ hsim Big Small hBig hcov']

end Generic

section Ring

variable {q N n m k : ℕ} [NeZero q]

/-- A matrix with rows of norm at most `ρ`, applied to a binary decomposition, stays within
`k N ρ`. -/
theorem cnorm_mulVec_dec_le (M : Matrix (Fin m) (Fin k) (Negacyclic (ZMod q) N))
    (dec : (Fin n → Negacyclic (ZMod q) N) → (Fin k → Negacyclic (ZMod q) N))
    (hdecN : ∀ y c, cnorm (dec y c) ≤ 1) (ρ : ℕ) (hM : ∀ a, rnorm (rowOf M a) ≤ ρ)
    (y : Fin n → Negacyclic (ZMod q) N) (a : Fin m) :
    cnorm ((M *ᵥ dec y) a) ≤ k * N * ρ := by
  simpa using cnorm_mulVec_le M (dec y) ρ 1 hM (hdecN y) a

/-- The rows of `Tm · X` with `cnorm (Tm a j) ≤ E_T` and `cnorm (X j c) ≤ 1` have norm at most
`k N E_T`. -/
theorem rnorm_rowOf_mul_le (Tm : Matrix (Fin m) (Fin k) (Negacyclic (ZMod q) N))
    (X : Matrix (Fin k) (Fin k) (Negacyclic (ZMod q) N)) (ET : ℕ)
    (hT : ∀ a j, cnorm (Tm a j) ≤ ET) (hX : ∀ j c, cnorm (X j c) ≤ 1) (a : Fin m) :
    rnorm (rowOf (Tm * X) a) ≤ k * N * ET := by
  refine rnorm_rowOf_le _ _ _ fun c => ?_
  have h := cnorm_mulVec_le Tm (fun j => X j c) ET 1
    (fun a => rnorm_rowOf_le _ _ _ (hT a)) (fun j => hX j c) a
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using h

/-- **Coverage**: a trapdoor matrix with rows of norm at most `ρ` keeps `famBall s` in the big box
of `Bb` bits when `s + k N ρ ≤ 2^{Bb−1} − 1`. -/
theorem leafKey_cover (M : Matrix (Fin m) (Fin k) (Negacyclic (ZMod q) N))
    (dec : (Fin n → Negacyclic (ZMod q) N) → (Fin k → Negacyclic (ZMod q) N))
    (hdecN : ∀ y c, cnorm (dec y c) ≤ 1) (ρ : ℕ) (hM : ∀ a, rnorm (rowOf M a) ≤ ρ)
    (Bb s : ℕ) (hB : 2 ^ Bb ≤ q) (hB1 : 1 ≤ Bb) (hs : s + k * N * ρ ≤ 2 ^ (Bb - 1) - 1) :
    ∀ x ∈ famBall q N (Fin m) s, ∀ y, x + M *ᵥ dec (-y) ∈ famBig q N (Fin m) Bb hB := by
  intro x hx y
  exact add_mem_of_eq rfl rfl hB1 hs (cnorm_mulVec_dec_le M dec hdecN ρ hM (-y)) x hx

/-- **The abort probability of a leaf key**: with a trapdoor matrix whose rows have norm at most
`ρ`, `k N ρ ≤ τ`, the small box `famBall s` with `2^{Bb−1} − 1 − τ ≤ s` and the big box of `Bb`
bits, a try aborts with probability at most `2^{−κ}` when `m N (4τ + 1) 2^κ ≤ 2^{Bb}`. -/
theorem leafKey_abort_le (M : Matrix (Fin m) (Fin k) (Negacyclic (ZMod q) N))
    (dec : (Fin n → Negacyclic (ZMod q) N) → (Fin k → Negacyclic (ZMod q) N))
    (hdecN : ∀ y c, cnorm (dec y c) ≤ 1) (ρ τ κ : ℕ) (hM : ∀ a, rnorm (rowOf M a) ≤ ρ)
    (hρ : k * N * ρ ≤ τ) (B : Matrix (Fin n) (Fin m) (Negacyclic (ZMod q) N))
    (Bb s : ℕ) (hB : 2 ^ Bb ≤ q) (hB1 : 1 ≤ Bb) (hs : 2 ^ (Bb - 1) - 1 - τ ≤ s)
    (hτ : 4 * τ + 1 ≤ 2 ^ Bb) (hκ : m * N * (4 * τ + 1) * 2 ^ κ ≤ 2 ^ Bb)
    (u : Fin n → Negacyclic (ZMod q) N) :
    boxSample (famBig q N (Fin m) Bb hB) (famBig_nonempty Bb hB) (famBall q N (Fin m) s)
        (Matrix.mulVecLin B).toAddMonoidHom (fun y => dec (-y)) (fun z => M *ᵥ z) u none ≤
      ((2 : ℝ≥0∞) ^ κ)⁻¹ := by
  have hpow : 2 ^ Bb = 2 * 2 ^ (Bb - 1) := by rw [← pow_succ']; congr 1; omega
  refine (boxSample_none_le _ _ _ _ _ _ u (famBall q N (Fin m) (2 ^ (Bb - 1) - 1 - 2 * τ))
    (subset_of_eq rfl rfl hB1 (by omega)) ?_).trans ?_
  · intro p hp y
    exact sub_mem_of_eq rfl rfl (by omega) (cnorm_mulVec_dec_le M dec hdecN ρ hM (-y)) p hp
  · simpa using abort_of_eq (P := Fin m) Bb τ κ hB rfl rfl hB1 hτ (by simpa using hκ)

end Ring

section Leaf

variable {q N ℓ n m mW k : ℕ} [NeZero q]

/-- **The leaf lemma (C1), statistical half: exact simulation of the leaf key.**
Over `ℤ_q[X]/(X^N + 1)`, with the ℓ-succinct LWE block identity
`B T_B[i,j] + W_i T_W[j] = δ_{ij} G`, a bit attribute `w`, `A := Σ_i w_i W_i + B R`, attribute
keys `A_j := A T_W[j]` and their trapdoors `R T_W[j] − Σ_i w_i T_B[i,j]` of entries at most `E`:
for every NAND circuit `φ` with `φ(w) = 0`, the leaf key of `[B | A_φ − G]` sampled with a gadget
trapdoor `Tm` of `B` (`B Tm = G`, entries at most `E_T`) has **the same law** as the one sampled
with `R_φ := EvalSim(φ, …)`, which uses no trapdoor of `B` — provided the small box `famBall s`
plus `k N errBound(k N, E, φ)` and plus `(k N)² E_T` stays in the big box of `Bb` bits. -/
theorem leafKey_sim_of_false_leaf (Γ : GadgetMatrix (Negacyclic (ZMod q) N) (Fin n) (Fin k))
    (hΓ : ∀ A c c', cnorm (Γ.ginv A c c') ≤ 1)
    (dec : (Fin n → Negacyclic (ZMod q) N) → (Fin k → Negacyclic (ZMod q) N))
    (hdec : ∀ y, Γ.G *ᵥ dec y = y) (hdecN : ∀ y c, cnorm (dec y c) ≤ 1)
    (B : Matrix (Fin n) (Fin m) (Negacyclic (ZMod q) N))
    (W : Fin ℓ → Matrix (Fin n) (Fin mW) (Negacyclic (ZMod q) N))
    (TB : Fin ℓ → Fin ℓ → Matrix (Fin m) (Fin k) (Negacyclic (ZMod q) N))
    (TW : Fin ℓ → Matrix (Fin mW) (Fin k) (Negacyclic (ZMod q) N))
    (h : ∀ i j, B * TB i j + W i * TW j = if i = j then Γ.G else 0)
    (w : Fin ℓ → Negacyclic (ZMod q) N) (hw : ∀ i, w i = 0 ∨ w i = 1)
    (R : Matrix (Fin m) (Fin mW) (Negacyclic (ZMod q) N)) (E : ℕ)
    (hE : ∀ j a c, cnorm ((R * TW j - ∑ i, w i • TB i j) a c) ≤ E)
    (φ : Circuit (Fin ℓ)) (hφ : φ.eval w = 0)
    (Tm : Matrix (Fin m) (Fin k) (Negacyclic (ZMod q) N)) (hTm : B * Tm = Γ.G) (ET : ℕ)
    (hET : ∀ a j, cnorm (Tm a j) ≤ ET)
    (Bb s : ℕ) (hB : 2 ^ Bb ≤ q) (hB1 : 1 ≤ Bb)
    (hsR : s + k * N * errBound (k * N) E φ ≤ 2 ^ (Bb - 1) - 1)
    (hsT : s + k * N * (k * N * ET) ≤ 2 ^ (Bb - 1) - 1)
    (u : Fin n → Negacyclic (ZMod q) N) :
    boxSample (famBig q N (Fin m) Bb hB) (famBig_nonempty Bb hB) (famBall q N (Fin m) s)
        (Matrix.mulVecLin B).toAddMonoidHom (fun y => dec (-y))
        (fun z => (Tm * Γ.ginv (evalMat Γ (fun j => ((∑ i, w i • W i) + B * R) * TW j) φ)) *ᵥ z)
        u =
      boxSample (famBig q N (Fin m) Bb hB) (famBig_nonempty Bb hB) (famBall q N (Fin m) s)
        (Matrix.mulVecLin B).toAddMonoidHom (fun y => dec (-y))
        (fun z => evalSim Γ (fun j => ((∑ i, w i • W i) + B * R) * TW j) w
          (fun j => R * TW j - ∑ i, w i • TB i j) φ *ᵥ z) u := by
  set Aw := fun j => ((∑ i, w i • W i) + B * R) * TW j with hAw
  set Rφ := evalSim Γ Aw w (fun j => R * TW j - ∑ i, w i • TB i j) φ
  -- Wee's identity: the attribute keys are in BGG+ form
  have hA : ∀ j, Aw j = B * (R * TW j - ∑ i, w i • TB i j) + w j • Γ.G := by
    intro j
    have hW : ∀ i, W i * TW j = (if i = j then Γ.G else 0) - B * TB i j := fun i =>
      eq_sub_of_add_eq' (h i j)
    simp only [hAw]
    rw [Matrix.add_mul, Matrix.sum_mul, Matrix.mul_sub, Matrix.mul_sum, Matrix.mul_assoc]
    simp_rw [Matrix.smul_mul, hW, smul_sub, Matrix.mul_smul]
    rw [Finset.sum_sub_distrib]
    simp [smul_ite, Finset.sum_ite_eq']
    abel
  have hrel : evalMat Γ Aw φ = B * Rφ := by
    rw [sim_relation Γ B Aw w _ hA φ, hφ, zero_smul, add_zero]
  have hRφ : ∀ a, rnorm (rowOf Rφ a) ≤ errBound (k * N) E φ := fun a => by
    simpa using rnorm_rowOf_evalSim_le Γ hΓ Aw w hw (fun j => R * TW j - ∑ i, w i • TB i j) E hE φ a
  have key := leafKey_real_eq_sim Γ dec hdec B Tm hTm Rφ (evalMat Γ Aw φ - Γ.G)
    (by rw [hrel]) (famBig q N (Fin m) Bb hB) (famBall q N (Fin m) s) (famBig_nonempty Bb hB)
    (by
      rw [sub_add_cancel]
      exact leafKey_cover _ dec hdecN _
        (rnorm_rowOf_mul_le Tm _ ET hET (hΓ _)) Bb s hB hB1 hsT)
    (leafKey_cover Rφ dec hdecN _ hRφ Bb s hB hB1 hsR) u
  rw [sub_add_cancel] at key
  exact key

end Leaf

end LeafKeyAux

open Classical in
theorem solution {K : Type*} [CommRing K] [DecidableEq K] {n m k : ℕ}
    (G : Matrix (Fin n) (Fin k) K) (dec : (Fin n → K) → (Fin k → K))
    (hdec : ∀ y, G *ᵥ dec y = y) (B : Matrix (Fin n) (Fin m) K) (A : Matrix (Fin n) (Fin k) K)
    (T : (Fin k → K) → (Fin m → K)) (hT : ∀ z, B *ᵥ T z = (A + G) *ᵥ z)
    (Big Small : Finset (Fin m → K)) (hBig : Big.Nonempty)
    (hcov : ∀ x ∈ Small, ∀ y, x + T (dec (-y)) ∈ Big) (u : Fin n → K)
    (x : Fin m → K) (z : Fin k → K) :
    boxSample Big hBig Small (Matrix.mulVecLin B).toAddMonoidHom (fun y => dec (-y)) T u
        (some (x, z)) =
      if x ∈ Small ∧ (∃ y, dec y = z) ∧ B *ᵥ x + A *ᵥ z = u then (Big.card : ℝ≥0∞)⁻¹ else 0 :=
  LeafKeyAux.leafKey_apply_some G dec hdec B A T hT Big Small hBig hcov u x z
