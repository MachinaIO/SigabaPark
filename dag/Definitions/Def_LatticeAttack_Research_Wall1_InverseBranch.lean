import Definitions.Def_LatticeAttack_Research_Wall1_ProjectedCovolume
import Definitions.Def_LatticeAttack_Research_Wall1_MarkedLineage
import Definitions.Def_LatticeAttack_Research_Wall1_VoronoiMarkLaw
import Definitions.Def_LatticeAttack_Research_Wall1_FreshDisplacement

set_option autoImplicit true

/-! # Inverting a framed append and counting its raw fiber (Part 176) -/

noncomputable section

namespace SigabaNeo.Wall1.InverseBranch

open Submodule WithLp

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The horizontal intercept along the recorded winner direction. -/
def intercept (v : WindowSpace V) : WindowSpace V →ₗ[ℝ] V :=
  fstₗ 2 ℝ V ℝ - (sndₗ 2 ℝ V ℝ).smulRight (v.snd⁻¹ • v.fst)

/-- Recover the horizontal refinement directly from the embedded output. -/
def refinement (v : WindowSpace V) (L : Submodule ℤ (ℝ ∙ v)ᗮ) : Submodule ℤ V :=
  L.map (((intercept v).comp (ℝ ∙ v)ᗮ.subtype).restrictScalars ℤ)

variable [FiniteDimensional ℝ V]

/-- The inverse image formula before intersecting with the projected cubic lattice. -/
theorem refinement_retained (M : Submodule ℤ V) (u : V) (v : WindowSpace V) (hv : v.snd ≠ 0) :
    refinement v (retainedWindow M u v) = M ⊔ ℤ ∙ (u - v.snd⁻¹ • v.fst) := by
  let B := intercept v
  have hkill : B v = 0 := by
    change v.fst - v.snd • v.snd⁻¹ • v.fst = 0
    simp [smul_inv_smul₀ hv]
  have hproj (w : WindowSpace V) : B ((ℝ ∙ v)ᗮ.starProjection w) = B w := by
    rw [starProjection_orthogonal_val, starProjection_singleton, map_sub, map_smul, hkill,
      smul_zero, sub_zero]
  have hhor (x : V) : B (horizontalInclusion x) = x := by
    change x - (0 : ℝ) • _ = x
    simp
  have hgen : B (toLp 2 (u, (1 : ℝ))) = u - v.snd⁻¹ • v.fst := by
    change u - (1 : ℝ) • _ = _
    rw [one_smul]
  unfold refinement retainedWindow projectedModule
  rw [← Submodule.map_comp]
  have he : (((intercept v).comp (ℝ ∙ v)ᗮ.subtype).restrictScalars ℤ).comp
      ((ℝ ∙ v)ᗮ.orthogonalProjectionOnto.toLinearMap.restrictScalars ℤ) =
      B.restrictScalars ℤ := LinearMap.ext hproj
  rw [he, appendWindow, Submodule.map_sup, ← Submodule.map_comp, Submodule.map_span,
    Set.image_singleton, show (B.restrictScalars ℤ).comp (horizontalInclusion.restrictScalars ℤ) =
      LinearMap.id from LinearMap.ext hhor, Submodule.map_id]
  change M ⊔ ℤ ∙ (B (toLp 2 (u, (1 : ℝ)))) = _
  rw [hgen]

omit [FiniteDimensional ℝ V] in
private theorem winner_horizontal {M : Submodule ℤ V} {u : V} {v : WindowSpace V} {k : ℕ}
    (hv : v ∈ appendWindow M u) (hh : v.snd = k) : v.fst - k • u ∈ M := by
  obtain ⟨_, ⟨l, hl, rfl⟩, _, hz, rfl⟩ := mem_sup.mp hv
  obtain ⟨j, rfl⟩ := mem_span_singleton.mp hz
  change (0 : ℝ) + j • (1 : ℝ) = k at hh
  have hj : j = (k : ℤ) := by exact_mod_cast (by simpa using hh : (j : ℝ) = k)
  change l + j • u - k • u ∈ M
  simpa [hj] using hl

private theorem bezout_split {A : Type*} [AddCommGroup A] {k q : ℕ} (hc : k.Coprime q) (x : A) :
    k.gcdA q • (k • x) + k.gcdB q • (q • x) = x := by
  have h := Nat.gcd_eq_gcd_ab k q
  rw [hc.gcd_eq_one] at h
  rw [← Nat.cast_smul_eq_nsmul ℤ k x, ← Nat.cast_smul_eq_nsmul ℤ q x, smul_smul, smul_smul, ← add_smul,
    mul_comm (k.gcdA q), mul_comm (k.gcdB q), ← h]
  simp

/-- The inverse formulas for any positive-height window vector with height coprime to q.
The mark is an element of K/M represented in the ambient quotient V/M. -/
theorem recover {M K : Submodule ℤ V} {u : V} {v : WindowSpace V} {k q : ℕ}
    (hMK : M ≤ K) (hq : ∀ x ∈ K, q • x ∈ M) (hu : u ∈ K)
    (hv : v ∈ appendWindow M u) (hh : v.snd = k) (hk : 0 < k) (hc : k.Coprime q) :
    let R := refinement v (retainedWindow M u v)
    span ℝ (R : Set V) = span ℝ (M : Set V) ∧ R ⊓ K = M ∧
      M.mkQ (k.gcdA q • v.fst) = M.mkQ u := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hy := winner_horizontal hv hh
  rw [refinement_retained M u v (hh ▸ hk'), hh]
  let d := u - (k : ℝ)⁻¹ • v.fst
  let R := M ⊔ ℤ ∙ d
  have hd : k • d ∈ M := by
    change k • (u - (k : ℝ)⁻¹ • v.fst) ∈ M
    rw [smul_sub, ← Nat.cast_smul_eq_nsmul ℝ k (_ • _), smul_inv_smul₀ hk']
    simpa using M.neg_mem hy
  have hmul (x : V) (hx : x ∈ R) : k • x ∈ M := by
    obtain ⟨a, ha, _, hb, rfl⟩ := mem_sup.mp hx
    obtain ⟨j, rfl⟩ := mem_span_singleton.mp hb
    rw [smul_add, smul_comm k j]
    exact M.add_mem (M.toAddSubmonoid.nsmul_mem ha k) (M.smul_mem j hd)
  change span ℝ (R : Set V) = span ℝ (M : Set V) ∧ R ⊓ K = M ∧ _
  refine ⟨le_antisymm (span_le.mpr ?_) (span_mono (show M ≤ R from le_sup_left)), ?_, ?_⟩
  · intro x hx
    have hw := (span ℝ (M : Set V)).smul_mem (k : ℝ)⁻¹ (subset_span (hmul x hx))
    rwa [← Nat.cast_smul_eq_nsmul ℝ, inv_smul_smul₀ hk'] at hw
  · apply le_antisymm _ (le_inf le_sup_left hMK)
    intro x hx
    rw [← bezout_split hc x]
    exact M.add_mem (M.smul_mem _ (hmul x hx.1)) (M.smul_mem _ (hq x hx.2))
  · have hky : M.mkQ v.fst = k • M.mkQ u :=
      (Submodule.Quotient.eq M).2 hy |>.trans (map_nsmul M.mkQ k u)
    have hqu : q • M.mkQ u = 0 := by
      rw [← map_nsmul]
      exact (Submodule.Quotient.mk_eq_zero M).2 (hq u hu)
    rw [map_zsmul, hky]
    simpa only [hqu, smul_zero, add_zero] using bezout_split hc (M.mkQ u)

/-- In the fixed ordered orthonormal frame, K is the cubic lattice projected onto E,
with its original ambient coordinates and scale. -/
def framedGrid {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V) (E : Submodule ℝ V) :
    Submodule ℤ V := (cubicModule b).map (E.starProjection.toLinearMap.restrictScalars ℤ)

/-- Reachability hypotheses for one append at the given time and in the given ambient frame.
The retained horizontal space is the full real span of the embedded incoming lattice. -/
structure FramedInput {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V) (q : ℕ) where
  space : Submodule ℝ V
  lattice : Submodule ℤ V
  full : span ℝ (lattice : Set V) = space
  integral : lattice ≤ framedGrid b space
  multiple : ∀ x ∈ framedGrid b space, q • x ∈ lattice
  lift : V
  lift_mem : lift ∈ framedGrid b space

/-- At a shared oriented winner and embedded output, the space, lattice, and mark agree.
Membership alone suffices, hence this applies to every designated shortest winner. -/
theorem framed_injective {ι : Type*} [Fintype ι] {b : OrthonormalBasis ι ℝ V} {q k : ℕ}
    (A C : FramedInput b q) (v : WindowSpace V) (hh : v.snd = k) (hk : 0 < k)
    (hc : k.Coprime q) (ha : v ∈ appendWindow A.lattice A.lift)
    (hcw : v ∈ appendWindow C.lattice C.lift)
    (he : retainedWindow A.lattice A.lift v = retainedWindow C.lattice C.lift v) :
    A.space = C.space ∧ A.lattice = C.lattice ∧ A.lattice.mkQ A.lift = A.lattice.mkQ C.lift := by
  obtain ⟨ea, ma, ua⟩ := recover A.integral A.multiple A.lift_mem ha hh hk hc
  obtain ⟨ec, mc, uc⟩ := recover C.integral C.multiple C.lift_mem hcw hh hk hc
  rw [A.full, he] at ea
  rw [C.full] at ec
  have es := ea.symm.trans ec
  rw [he, es] at ma
  have ms := ma.symm.trans mc
  exact ⟨es, ms, ua.symm.trans (ms ▸ uc)⟩

open scoped Classical in
/-- The raw fiber over one reachable output. The uniqueness hypothesis is local to that
output, so other outputs may include horizontal winners or collisions. -/
theorem raw_fiber_card {P G S O : Type*} [Fintype P] [AddGroup G] [Fintype G]
    {H : S → Type*} [∀ s, AddGroup (H s)] (parent : P → S) (φ : (s : S) → G →+ H s)
    (emit : (Σ s, H s) → O) (o : O) (s : S) (h : H s) (hh : h ∈ (φ s).range)
    (hinv : ∀ t, emit t = o ↔ t = ⟨s, h⟩) :
    (Finset.univ.filter fun x : P × G ↦ emit ⟨parent x.1, φ (parent x.1) x.2⟩ = o).card =
      (Finset.univ.filter fun p ↦ parent p = s).card * Nat.card (φ s).ker := by
  classical
  have iff_input (p : P) (g : G) :
      emit ⟨parent p, φ (parent p) g⟩ = o ↔ parent p = s ∧ φ s g = h := by
    rw [hinv, Sigma.mk.inj_iff]
    by_cases hp : parent p = s
    · subst s
      simp
    · simp [hp]
  simp only [iff_input, ← Finset.univ_product_univ]
  rw [Finset.filter_product (fun p ↦ parent p = s) (fun g ↦ φ s g = h),
    Finset.card_product, FreshDisplacement.fiber_card (φ s) h hh]

/-- For the height-two toy winner (-1,2), its first coordinate recovers mark 8 modulo 17. -/
theorem toy_mark_mod17 : ∀ j : Fin 17, (2 * j.val + 1) % 17 = 0 ↔ j.val = 8 := by decide

end SigabaNeo.Wall1.InverseBranch

#print axioms SigabaNeo.Wall1.InverseBranch.refinement_retained
#print axioms SigabaNeo.Wall1.InverseBranch.recover
#print axioms SigabaNeo.Wall1.InverseBranch.framed_injective
#print axioms SigabaNeo.Wall1.InverseBranch.raw_fiber_card
#print axioms SigabaNeo.Wall1.InverseBranch.toy_mark_mod17
