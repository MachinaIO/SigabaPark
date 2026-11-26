module

public import Definitions.Def_LatticeAttack_Attacks_Bkw_Retry
public import Definitions.Def_LatticeAttack_Attacks_Bkw_Leaves

import all Definitions.Def_LatticeAttack_Attacks_Bkw_Leaves

set_option autoImplicit true

public section
namespace SigabaNeo.Lattices.Attacks.Bkw
open scoped ENNReal
noncomputable section

/-- Independent draws with product mass. -/
def independentPair {X Y : Type*} (p : PMF X) (q : PMF Y) : PMF (X × Y) :=
  p.bind fun x ↦ q.map (x, ·)

theorem independentPair_apply {X Y : Type*} (p : PMF X) (q : PMF Y) (x : X) (y : Y) :
    independentPair p q (x,y) = p x * q y := by
  classical
  rw [independentPair, PMF.bind_apply, tsum_eq_single x]
  · simp [PMF.map_apply]
  · intro a ha
    simp [PMF.map_apply, Ne.symm ha]

def iidLeaves {E : Type*} (p : PMF E) : (a : ℕ) → PMF (LeafDraw E a)
  | 0 => p
  | a+1 => independentPair (iidLeaves p a) (iidLeaves p a)

def signedLaw {E : Type*} [Sub E] (p : PMF E) (a : ℕ) : PMF E :=
  (iidLeaves p a).map (leafDifference id a)

def diffLaw {E : Type*} [Sub E] (p : PMF E) : PMF E :=
  p.bind fun i ↦ p.map fun j ↦ i - j

theorem signedLaw_succ {E : Type*} [Sub E] (p : PMF E) (a : ℕ) :
    signedLaw p (a+1) = diffLaw (signedLaw p a) := by
  unfold signedLaw diffLaw
  rw [iidLeaves, independentPair]
  change PMF.map (fun x : LeafDraw E a × LeafDraw E a ↦
    leafDifference id a x.1 - leafDifference id a x.2) _ = _
  rw [PMF.map_bind]
  simp [PMF.map_comp,
    Function.comp_def]

def flat (X : Type*) [Fintype X] [Nonempty X] : PMF X :=
  PMF.ofFintype (fun _ ↦ (Fintype.card X : ℝ≥0∞)⁻¹) (by
    simp [nsmul_eq_mul, ENNReal.mul_inv_cancel, Fintype.card_ne_zero])

variable {B R E : Type} [Fintype B] [Nonempty B] [Fintype R] [Nonempty R]
  [AddCommGroup R] [Fintype E] [AddCommGroup E] [DecidableEq E]

/-- Sum over the common block, the right suffix and both errors. The left suffix
is uniquely determined by the required output difference. -/
def hit (w : ((B × R) × E) → ℝ≥0∞) (v : R × E) : ℝ≥0∞ :=
  ∑ i : E, ∑ j : E, if v.2 = i-j then
    ∑ b : B, ∑ y : R, w ((b,v.1+y),i) * w ((b,y),j) else 0

/-- First-hit expansion for independent fresh-pair attempts with uniform block. -/
def retryStage (w : ((B × R) × E) → ℝ≥0∞) (v : R × E) : ℝ≥0∞ :=
  ∑' n : ℕ, (1 - (Fintype.card B : ℝ≥0∞)⁻¹)^n * hit w v

theorem retryStage_flat (p : PMF E) (v : R × E) :
    retryStage (B := B) (independentPair (flat (B × R)) p) v =
      independentPair (flat R) (diffLaw p) v := by
  classical
  rcases v with ⟨r,z⟩
  have hb : (Fintype.card B : ℝ≥0∞) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hr : (Fintype.card R : ℝ≥0∞) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hone : (Fintype.card B : ℝ≥0∞)⁻¹ ≤ 1 := by
    rw [ENNReal.inv_le_one]
    exact_mod_cast Fintype.card_pos (α := B)
  rw [retryStage, ENNReal.tsum_mul_right, ENNReal.tsum_geometric,
    ENNReal.sub_sub_cancel ENNReal.one_ne_top hone, inv_inv]
  simp only [hit, independentPair_apply,
    flat, PMF.ofFintype_apply, Fintype.card_prod, Nat.cast_mul, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, diffLaw, PMF.bind_apply, PMF.map_apply,
    tsum_fintype, Finset.mul_sum, mul_ite, mul_zero]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · rw [ENNReal.mul_inv (Or.inl hb) (Or.inr hr)]
    let u : ℝ≥0∞ := Fintype.card B
    let t : ℝ≥0∞ := Fintype.card R
    calc
      _ = (u*u⁻¹) * (u*u⁻¹) * (t*t⁻¹) * (t⁻¹ * (p i * p j)) := by dsimp [u,t]; ac_rfl
      _ = _ := by simp [u,t, ENNReal.mul_inv_cancel hb, ENNReal.mul_inv_cancel hr]
  · rfl

/-- The total one-attempt acceptance mass is the reciprocal block cardinality. -/
theorem hit_total (p : PMF E) :
    ∑' v : R × E, hit (B := B) (independentPair (flat (B × R)) p) v =
      (Fintype.card B : ℝ≥0∞)⁻¹ := by
  have hb : (Fintype.card B : ℝ≥0∞) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hone : (Fintype.card B : ℝ≥0∞)⁻¹ ≤ 1 := by
    rw [ENNReal.inv_le_one]
    exact_mod_cast Fintype.card_pos (α := B)
  have h (v : R × E) := retryStage_flat (B := B) p v
  simp only [retryStage, ENNReal.tsum_mul_right, ENNReal.tsum_geometric,
    ENNReal.sub_sub_cancel ENNReal.one_ne_top hone, inv_inv] at h
  calc
    _ = ∑' v : R × E, (Fintype.card B : ℝ≥0∞)⁻¹ *
        independentPair (flat R) (diffLaw p) v := by
      apply tsum_congr
      intro v
      rw [← h, ← mul_assoc, ENNReal.inv_mul_cancel hb (by simp), one_mul]
    _ = _ := by rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]

/-- Each recursive call starts with one extra block in its suffix. -/
def stages (B E : Type) [Fintype B] [Nonempty B] [AddCommGroup B]
    [Fintype E] [AddCommGroup E] [DecidableEq E] (p : PMF E) :
    (a : ℕ) → (R : Type) → [Fintype R] → [Nonempty R] → [AddCommGroup R] → R × E → ℝ≥0∞
  | 0, R, _, _, _ => independentPair (flat R) p
  | a+1, R, _, _, _ => retryStage (stages B E p a (B × R))

theorem stages_eq [AddCommGroup B] (p : PMF E) (a : ℕ) :
    stages B E p a R = ⇑(independentPair (flat R) (signedLaw p a)) := by
  induction a generalizing R with
  | zero =>
    change _ = ⇑(independentPair (flat R) (p.map id))
    rw [PMF.map_id]
    rfl
  | succ a ih =>
    funext v
    rw [stages, ih, retryStage_flat, signedLaw_succ]

/-- The stage masses bundled with their normalization proof. -/
def stagePMF [AddCommGroup B] (p : PMF E) (a : ℕ) : PMF (R × E) :=
  ⟨stages B E p a R, by rw [stages_eq]; exact (independentPair (flat R) (signedLaw p a)).2⟩

/-- Ordered outputs of independent executions, encoded as a list of fixed length. -/
def batch {X : Type} (p : PMF X) : ℕ → PMF (List X)
  | 0 => PMF.pure []
  | n+1 => (independentPair p (batch p n)).map (fun x ↦ x.1 :: x.2)

theorem batch_mass {X : Type} (p : PMF X) (xs : List X) :
    batch p xs.length xs = (xs.map (fun x ↦ p x)).prod := by
  classical
  induction xs with
  | nil => simp [batch, PMF.pure_apply]
  | cons x xs ih =>
    simp only [List.length_cons, batch, PMF.map_apply]
    rw [tsum_eq_single (x,xs), ite_eq_left rfl, independentPair_apply, ih]
    · rfl
    · rintro ⟨y,ys⟩ h
      simp only [List.cons.injEq, ite_eq_right_iff]
      rintro ⟨rfl,rfl⟩
      exact (h rfl).elim

theorem stages_iid [AddCommGroup B] (p : PMF E) (a : ℕ) (xs : List (R × E)) :
    batch (stagePMF (B := B) p a) xs.length xs =
      (xs.map (fun v ↦ flat R v.1 * signedLaw p a v.2)).prod := by
  rw [batch_mass]
  change (xs.map (stages B E p a R)).prod = _
  rw [stages_eq]
  congr 1
  exact List.map_congr_left fun ⟨r,z⟩ _ ↦ independentPair_apply _ _ r z

#print axioms hit_total
#print axioms stages_iid
#print axioms stages_eq

/-- Expected cost by summing the cost of each attempt weighted by its reach probability. -/
def freshCost (K : ℕ) : ℕ → ℝ
  | 0 => 1
  | a+1 => (∑' n : ℕ, (1 - (K : ℝ)⁻¹)^n) * (2 * freshCost K a)

theorem freshCost_eq {K : ℕ} (hK : 0 < K) (a : ℕ) :
    freshCost K a = (2 * (K : ℝ))^a := by
  have h : (1 : ℝ) ≤ K := by exact_mod_cast hK
  induction a with
  | zero => simp [freshCost]
  | succ a ih =>
    rw [freshCost, tsum_geometric_of_lt_one (by exact sub_nonneg.mpr (inv_le_one_of_one_le₀ h))
      (sub_lt_self _ (by positivity)), ih]
    simp only [sub_sub_cancel, inv_inv, pow_succ]
    ring

theorem twoStage_cost_counterexample : freshCost 2 2 ≠ 2^2 * 2 := by
  rw [freshCost_eq (by decide)]
  norm_num

#print axioms retryStage_flat
#print axioms signedLaw_succ
#print axioms freshCost_eq
#print axioms twoStage_cost_counterexample
end
end SigabaNeo.Lattices.Attacks.Bkw
