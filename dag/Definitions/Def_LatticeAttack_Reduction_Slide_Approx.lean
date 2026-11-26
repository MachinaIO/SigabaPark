module

public import Definitions.Def_LatticeAttack_Reduction_Slide_Update
import all Definitions.Def_LatticeAttack_Reduction_Slide_Update

set_option autoImplicit true

public section
namespace SigabaNeo.Slide
open Matrix LLL.Algorithm

private theorem first_weight {n d β : ℕ} (B : Rows n d) (hb : LinearIndependent ℤ B)
    (p : ℕ) (pos : 0 < β) (fit : p + β ≤ n) :
    weight (blockAt B p β fit) (Pi.single ⟨0,pos⟩ 1) = normSq B ⟨p, by omega⟩ := by
  let A := blockAt B p 1 (by omega)
  have row : vector (blockAt B p β fit) (Pi.single ⟨0,pos⟩ 1) = A 0 := by
    unfold vector
    have e : (fun i : Fin β ↦ (((Pi.single ⟨0,pos⟩ 1 : Fin β → ℤ) i : ℤ) : ℚ)) =
        Pi.single ⟨0,pos⟩ 1 := by ext; simp [Pi.single_apply, apply_ite]
    rw [e, single_vecMul, one_smul]
    rfl
  have pref (m : ℕ) (hm : m ≤ n) : (gramDet (firstRows B m hm) : ℚ) =
      ∏ j : Fin m, normSq B (j.castLE hm) := by
    cases m with
    | zero => simp [gramDet]
    | succ j => exact gramDet_prefix B ⟨j,hm⟩
  have hp := firstRows_pos B hb p (by omega)
  have e := factor_prefix B p 1 (by omega) hp.ne'
  rw [pref, Fin.prod_univ_castSucc] at e
  change (∏ j : Fin p, normSq B (j.castLE (by omega))) * normSq B ⟨p,by omega⟩ =
    (gramDet (firstRows B p (by omega)) : ℚ) * (A * A.transpose).det at e
  rw [← pref] at e
  have hn : (gramDet (firstRows B p (by omega)) : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have g := (mul_left_cancel₀ hn e).symm
  rw [weight, row]
  simpa [A, det_fin_one, Matrix.mul_apply, sq] using g

/-- Squared GSO length ratio across a checked block, bounded using any primal and
shifted reciprocal witnesses. Hermite witnesses can be substituted independently. -/
theorem checked_boundary {k b d : ℕ} (B : Rows (k * (b+1)) d) (hb : LinearIndependent ℤ B)
    {q : ℚ} (hq : 0 ≤ q) (ok : slideCheck B (by omega) q = true) (i : Fin (k-1))
    (x y : Fin (b+1) → ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (fit : i.val*(b+1)+1+(b+1) ≤ k*(b+1)) :
    let p := i.val*(b+1)
    let A := blockAt B p (b+1) (by dsimp [p]; omega)
    let D := dualRows (blockAt B (p+1) (b+1) fit)
    normSq B ⟨p, by dsimp [p]; omega⟩ ≤
      weight A x * (q * weight D y) * normSq B ⟨p+(b+1), by dsimp [p]; omega⟩ := by
  intro p A D
  have hr := block_regular B hb p (b+1) (by omega)
  have primal := slideCheck_primal B (by omega) ok ⟨i.val,by omega⟩ (by change i.val*(b+1)+(b+1) ≤ _; omega) x hr
    (vector_ne_zero A hr x hx)
  rw [first_weight B hb] at primal
  let S := blockAt B (p+1) (b+1) fit
  let s : Fin (b+1) → ℤ := Pi.single (Fin.last b) (1 : ℤ)
  obtain ⟨c,hc⟩ := repr_dual S s
  have reci := reciprocal_normSq B hb (p+1) b fit c _ hc
    (single_last_pair S (block_regular B hb _ _ fit))
  have dual := slideCheck_dual B (by omega) hq ok i fit y hy (block_regular B hb _ _ fit)
  change weight D s ≤ q * weight D y at dual
  let j : Fin (k*(b+1)) := ⟨p+(b+1),by omega⟩
  have idx : (⟨p+1+b,by omega⟩ : Fin (k*(b+1))) = j := Fin.ext (by dsimp [j]; omega)
  rw [idx] at reci
  have iden : weight D s * normSq B j = 1 := by
    simpa only [mul_comm (normSq B j), weight, sq, dotProduct] using reci
  have nn : 0 ≤ normSq B j := by
    unfold normSq LLL.Algorithm.dot
    exact Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _
  have one := mul_le_mul_of_nonneg_right dual nn
  rw [iden] at one
  exact primal.trans (by
    rw [mul_assoc]
    exact le_mul_of_one_le_right (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) one)

/-- Iterate the checked boundary comparison with an upper bound C on each witness product. -/
theorem checked_telescope {k b d : ℕ} (B : Rows (k * (b+1)) d) (hb : LinearIndependent ℤ B)
    {q : ℚ} (hq : 0 ≤ q) (ok : slideCheck B (by omega) q = true)
    (m : ℕ) (hm : m < k) (C : ℕ → ℚ) (hC : ∀ i < m, 0 ≤ C i)
    (witness : ∀ i < m, ∃ (fit : i*(b+1)+1+(b+1) ≤ k*(b+1)) (x y : Fin (b+1) → ℤ),
      x ≠ 0 ∧ y ≠ 0 ∧ weight (blockAt B (i*(b+1)) (b+1) (by omega)) x *
        (q * weight (dualRows (blockAt B (i*(b+1)+1) (b+1) fit)) y) ≤ C i) :
    normSq B ⟨0, Nat.mul_pos (by omega) (by omega)⟩ ≤
      (∏ i ∈ Finset.range m, C i) * normSq B ⟨m*(b+1), Nat.mul_lt_mul_of_pos_right hm (by omega)⟩ := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨fit,x,y,hx,hy,hxy⟩ := witness m (by omega)
    have prev := ih (by omega) (fun i hi ↦ hC i (by omega)) (fun i hi ↦ witness i (by omega))
    have step := checked_boundary B hb hq ok ⟨m,by omega⟩ x y hx hy fit
    dsimp only at step
    let j : Fin (k*(b+1)) := ⟨(m+1)*(b+1), Nat.mul_lt_mul_of_pos_right hm (by omega)⟩
    have eqj : (⟨m*(b+1)+(b+1),by omega⟩ : Fin (k*(b+1))) = j := Fin.ext (Nat.succ_mul ..).symm
    rw [eqj] at step
    have nn : 0 ≤ normSq B j := by
      unfold normSq LLL.Algorithm.dot
      exact Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _
    rw [Finset.prod_range_succ, mul_assoc]
    exact prev.trans (mul_le_mul_of_nonneg_left
      (step.trans (mul_le_mul_of_nonneg_right hxy nn))
      (Finset.prod_nonneg fun i hi ↦ hC i (by have := Finset.mem_range.mp hi; omega)))

/-- Cancellation of the overlapping log-volume in the primal and reciprocal Hermite
inequalities, with r and s the consecutive log GSO lengths. -/
theorem mordell_log_step {β g e r s volume : ℝ}
    (primal : β*r ≤ β*g + volume)
    (dual : -β*s ≤ β*(g+e) - (volume-r+s)) :
    (β-1)*(r-s) ≤ β*(2*g+e) := by linarith

theorem mordell_log_telescope (r : ℕ → ℝ) (m : ℕ) (β g e : ℝ)
    (step : ∀ i < m, (β-1)*(r i-r (i+1)) ≤ β*(2*g+e)) :
    (β-1)*(r 0-r m) ≤ (m:ℝ)*β*(2*g+e) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have prev := ih (fun i hi ↦ step i (by omega))
    have last := step m (by omega)
    push_cast
    linarith

#print axioms checked_telescope
#print axioms checked_boundary
#print axioms mordell_log_step
#print axioms mordell_log_telescope
end SigabaNeo.Slide
