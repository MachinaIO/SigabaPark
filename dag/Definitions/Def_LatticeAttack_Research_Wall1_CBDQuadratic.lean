module

public import Definitions.Def_LatticeAttack_Research_Wall1_CBDTail
import all Definitions.Def_LatticeAttack_Research_Wall1_CBDTail
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

set_option autoImplicit true

public section

namespace SigabaNeo.Wall1.CBDQuadratic

open SampleDeletion CBDTail
open scoped BigOperators

private abbrev value (b : Digit 3) : ℝ := centered b
noncomputable def moment (n : ℕ) := ∑ b : Digit 3, weight b * (centered b : ℝ)^n

theorem coordinate_moments : moment 0 = 1 ∧ moment 1 = 0 ∧ moment 2 = 3/2 ∧ moment 4 = 6 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (unfold moment; change (∑ b : Fin 7, _) = _; norm_num [Fin.sum_univ_succ, weight, mass, centered, Nat.choose, Fin.val_succ])

theorem odd_moments (k : ℕ) : moment (2*k+1) = 0 := by
  (unfold moment; change (∑ b : Fin 7, _) = _; norm_num [Fin.sum_univ_succ, weight, mass, centered, Nat.choose, Fin.val_succ])
  simp only [pow_succ, pow_mul]
  norm_num

private theorem mu_small (e : ℕ) (he : e ∈ [1,2,3,4]) :
    moment e = (if e = 2 then 3/2 else if e = 4 then 6 else 0) := by
  have h := odd_moments 1
  norm_num at h
  rcases coordinate_moments with ⟨_,a,b,c⟩
  simp at he
  rcases he with rfl | rfl | rfl | rfl <;> norm_num [a,b,c,h]

private theorem weight_sum : ∑ b : Digit 3, weight b = 1 := by
  simpa [moment] using coordinate_moments.1

variable {N : ℕ}
private abbrev Outcome (N : ℕ) := Fin N → Digit 3

theorem joint_mass : (∑ w : Fin N → Digit 3, jointWeight w) = 1 := by
  simpa [jointWeight,weight_sum] using
    (Fintype.prod_sum (fun (_ : Fin N) (b : Digit 3) ↦ weight b)).symm

private noncomputable def E (f : Outcome N → ℝ) := ∑ w, jointWeight w * f w

private theorem peel (i : Fin N) (e : ℕ) (f : Outcome N → ℝ)
    (hf : ∀ w w' : Outcome N, (∀ j, j ≠ i → w j = w' j) → f w = f w') :
    E (fun w ↦ value (w i)^e * f w) = moment e * E f := by
  let T := (Equiv.funSplitAt i (Digit 3)).symm
  let g := fun (r : {j : Fin N // j ≠ i} → Digit 3) ↦ f (T (0, r))
  have hh (b : Digit 3) (r) : f (T (b,r)) = g r := by
    apply hf
    intro j hj
    simp [T, Equiv.funSplitAt, Equiv.piSplitAt, hj]
  have hi (b : Digit 3) (r) : T (b,r) i = b := by
    simp [T, Equiv.funSplitAt, Equiv.piSplitAt, *]
  have hw (b : Digit 3) (r) : jointWeight (T (b,r)) = weight b * ∏ j, weight (r j) := by
    unfold jointWeight
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i, hi]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    have hj := j.property
    simp [T, Equiv.funSplitAt, Equiv.piSplitAt, *]
  unfold E
  conv_lhs => rw [← T.sum_comp]
  conv_rhs => rhs; rw [← T.sum_comp]
  simp only [Fintype.sum_prod_type, hw, hi, hh]
  simp_rw [show ∀ a b c d : ℝ, a*b*(c*d) = (a*c)*(b*d) by intros; ring,
    mul_assoc, ← Finset.mul_sum]
  simp only [← Finset.sum_mul, weight_sum, one_mul, moment, value]
  simp [Finset.sum_mul, mul_assoc]

private theorem joint (s : List (Fin N × ℕ)) (hs : (s.map Prod.fst).Nodup) :
    E (fun w ↦ (s.map (fun p ↦ value (w p.1) ^ p.2)).prod) =
      (s.map (fun p ↦ moment p.2)).prod := by
  induction s with
  | nil => simp [E,joint_mass]
  | cons p s ih =>
    rcases p with ⟨i,e⟩
    simp only [List.map_cons, List.nodup_cons] at hs
    simp only [List.map_cons, List.prod_cons]
    rw [peel i e, ih hs.2]
    intro w w' h
    congr 1
    apply List.map_congr_left
    intro p hp
    rw [h p.1 (fun he ↦ hs.1 (List.mem_map.mpr ⟨p,hp,he⟩))]

private noncomputable def d (i j : Fin N) : ℝ := if i = j then 1 else 0

private theorem two (i j : Fin N) :
    E (fun w ↦ value (w i) * value (w j)) = (3/2) * d i j := by
  by_cases hji : j = i
  · subst j
    (calc
      _ = _ := congrArg E (funext fun w ↦ by
        show _ = (List.map (fun p : Fin _ × ℕ ↦ value (w p.1) ^ p.2) [(i,2)]).prod
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one]
        <;> ring)
      _ = _ := joint [(i,2)] (by simp_all [ne_comm])
      _ = _ := by simp_all [d, mu_small, eq_comm] <;> ring_nf <;> simp)
  · (calc
      _ = _ := congrArg E (funext fun w ↦ by
        show _ = (List.map (fun p : Fin _ × ℕ ↦ value (w p.1) ^ p.2) [(i,1), (j,1)]).prod
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one]
        <;> ring)
      _ = _ := joint [(i,1), (j,1)] (by simp_all [ne_comm])
      _ = _ := by simp_all [d, mu_small, eq_comm] <;> ring_nf <;> simp)
private theorem four (i j k l : Fin N) :
    E (fun w ↦ value (w i) * value (w j) * value (w k) * value (w l)) = (9/4) * (d i j * d k l + d i k * d j l + d i l * d j k) - (3/4) * d i j * d i k * d i l := by
  by_cases hji : j = i
  · subst j
    by_cases hki : k = i
    · subst k
      by_cases hli : l = i
      · subst l
        (calc
          _ = _ := congrArg E (funext fun w ↦ by
            show _ = (List.map (fun p : Fin _ × ℕ ↦ value (w p.1) ^ p.2) [(i,4)]).prod
            simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one]
            <;> ring)
          _ = _ := joint [(i,4)] (by simp_all [ne_comm])
          _ = _ := by simp_all [d, mu_small, eq_comm] <;> ring_nf <;> simp)
      · (calc
          _ = _ := congrArg E (funext fun w ↦ by
            show _ = (List.map (fun p : Fin _ × ℕ ↦ value (w p.1) ^ p.2) [(i,3), (l,1)]).prod
            simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one]
            <;> ring)
          _ = _ := joint [(i,3), (l,1)] (by simp_all [ne_comm])
          _ = _ := by simp_all [d, mu_small, eq_comm] <;> ring_nf <;> simp)
    · by_cases hli : l = i
      · subst l
        (calc
          _ = _ := congrArg E (funext fun w ↦ by
            show _ = (List.map (fun p : Fin _ × ℕ ↦ value (w p.1) ^ p.2) [(i,3), (k,1)]).prod
            simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one]
            <;> ring)
          _ = _ := joint [(i,3), (k,1)] (by simp_all [ne_comm])
          _ = _ := by simp_all [d, mu_small, eq_comm] <;> ring_nf <;> simp)
      · by_cases hlk : l = k
        · subst l
          (calc
            _ = _ := congrArg E (funext fun w ↦ by
              show _ = (List.map (fun p : Fin _ × ℕ ↦ value (w p.1) ^ p.2) [(i,2), (k,2)]).prod
              simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one]
              <;> ring)
            _ = _ := joint [(i,2), (k,2)] (by simp_all [ne_comm])
            _ = _ := by simp_all [d, mu_small, eq_comm] <;> ring_nf <;> simp)
        · (calc
            _ = _ := congrArg E (funext fun w ↦ by
              show _ = (List.map (fun p : Fin _ × ℕ ↦ value (w p.1) ^ p.2) [(i,2), (k,1), (l,1)]).prod
              simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one]
              <;> ring)
            _ = _ := joint [(i,2), (k,1), (l,1)] (by simp_all [ne_comm])
            _ = _ := by simp_all [d, mu_small, eq_comm] <;> ring_nf <;> simp)
  · by_cases hki : k = i
    · subst k
      by_cases hli : l = i
      · subst l
        (calc
          _ = _ := congrArg E (funext fun w ↦ by
            show _ = (List.map (fun p : Fin _ × ℕ ↦ value (w p.1) ^ p.2) [(i,3), (j,1)]).prod
            simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one]
            <;> ring)
          _ = _ := joint [(i,3), (j,1)] (by simp_all [ne_comm])
          _ = _ := by simp_all [d, mu_small, eq_comm] <;> ring_nf <;> simp)
      · by_cases hlj : l = j
        · subst l
          (calc
            _ = _ := congrArg E (funext fun w ↦ by
              show _ = (List.map (fun p : Fin _ × ℕ ↦ value (w p.1) ^ p.2) [(i,2), (j,2)]).prod
              simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one]
              <;> ring)
            _ = _ := joint [(i,2), (j,2)] (by simp_all [ne_comm])
            _ = _ := by simp_all [d, mu_small, eq_comm] <;> ring_nf <;> simp)
        · (calc
            _ = _ := congrArg E (funext fun w ↦ by
              show _ = (List.map (fun p : Fin _ × ℕ ↦ value (w p.1) ^ p.2) [(i,2), (j,1), (l,1)]).prod
              simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one]
              <;> ring)
            _ = _ := joint [(i,2), (j,1), (l,1)] (by simp_all [ne_comm])
            _ = _ := by simp_all [d, mu_small, eq_comm] <;> ring_nf <;> simp)
    · by_cases hkj : k = j
      · subst k
        by_cases hli : l = i
        · subst l
          (calc
            _ = _ := congrArg E (funext fun w ↦ by
              show _ = (List.map (fun p : Fin _ × ℕ ↦ value (w p.1) ^ p.2) [(i,2), (j,2)]).prod
              simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one]
              <;> ring)
            _ = _ := joint [(i,2), (j,2)] (by simp_all [ne_comm])
            _ = _ := by simp_all [d, mu_small, eq_comm] <;> ring_nf <;> simp)
        · by_cases hlj : l = j
          · subst l
            (calc
              _ = _ := congrArg E (funext fun w ↦ by
                show _ = (List.map (fun p : Fin _ × ℕ ↦ value (w p.1) ^ p.2) [(i,1), (j,3)]).prod
                simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one]
                <;> ring)
              _ = _ := joint [(i,1), (j,3)] (by simp_all [ne_comm])
              _ = _ := by simp_all [d, mu_small, eq_comm] <;> ring_nf <;> simp)
          · (calc
              _ = _ := congrArg E (funext fun w ↦ by
                show _ = (List.map (fun p : Fin _ × ℕ ↦ value (w p.1) ^ p.2) [(i,1), (j,2), (l,1)]).prod
                simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one]
                <;> ring)
              _ = _ := joint [(i,1), (j,2), (l,1)] (by simp_all [ne_comm])
              _ = _ := by simp_all [d, mu_small, eq_comm] <;> ring_nf <;> simp)
      · by_cases hli : l = i
        · subst l
          (calc
            _ = _ := congrArg E (funext fun w ↦ by
              show _ = (List.map (fun p : Fin _ × ℕ ↦ value (w p.1) ^ p.2) [(i,2), (j,1), (k,1)]).prod
              simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one]
              <;> ring)
            _ = _ := joint [(i,2), (j,1), (k,1)] (by simp_all [ne_comm])
            _ = _ := by simp_all [d, mu_small, eq_comm] <;> ring_nf <;> simp)
        · by_cases hlj : l = j
          · subst l
            (calc
              _ = _ := congrArg E (funext fun w ↦ by
                show _ = (List.map (fun p : Fin _ × ℕ ↦ value (w p.1) ^ p.2) [(i,1), (j,2), (k,1)]).prod
                simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one]
                <;> ring)
              _ = _ := joint [(i,1), (j,2), (k,1)] (by simp_all [ne_comm])
              _ = _ := by simp_all [d, mu_small, eq_comm] <;> ring_nf <;> simp)
          · by_cases hlk : l = k
            · subst l
              (calc
                _ = _ := congrArg E (funext fun w ↦ by
                  show _ = (List.map (fun p : Fin _ × ℕ ↦ value (w p.1) ^ p.2) [(i,1), (j,1), (k,2)]).prod
                  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one]
                  <;> ring)
                _ = _ := joint [(i,1), (j,1), (k,2)] (by simp_all [ne_comm])
                _ = _ := by simp_all [d, mu_small, eq_comm] <;> ring_nf <;> simp)
            · (calc
                _ = _ := congrArg E (funext fun w ↦ by
                  show _ = (List.map (fun p : Fin _ × ℕ ↦ value (w p.1) ^ p.2) [(i,1), (j,1), (k,1), (l,1)]).prod
                  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one]
                  <;> ring)
                _ = _ := joint [(i,1), (j,1), (k,1), (l,1)] (by simp_all [ne_comm])
                _ = _ := by simp_all [d, mu_small, eq_comm] <;> ring_nf <;> simp)

private theorem E_sum {α : Type*} [Fintype α] (f : α → Outcome N → ℝ) :
    E (fun w ↦ ∑ i, f i w) = ∑ i, E (f i) := by
  simp only [E, Finset.mul_sum]
  exact Finset.sum_comm

private theorem E_mul (c : ℝ) (f : Outcome N → ℝ) :
    E (fun w ↦ c * f w) = c * E f := by simp [E, Finset.mul_sum, mul_left_comm]

noncomputable def quadratic (Q : Matrix (Fin N) (Fin N) ℝ) (w : Fin N → Digit 3) :=
  ∑ i, ∑ j, Q i j * ((centered (w i) : ℝ) * (centered (w j) : ℝ))

theorem quadratic_mean (Q : Matrix (Fin N) (Fin N) ℝ) :
    ∑ w, jointWeight w * quadratic Q w = (3/2) * Q.trace := by
  change E (fun w ↦ ∑ i, ∑ j, Q i j * (value (w i) * value (w j))) = _
  simp_rw [E_sum, E_mul, two]
  simp [d, Matrix.trace, mul_ite, Finset.mul_sum, mul_comm]

private noncomputable def z (w : Outcome N) (i j : Fin N) :=
  value (w i) * value (w j) - (3/2) * d i j

private theorem cov (i j k l : Fin N) :
    E (fun w ↦ z w i j * z w k l) =
    (9/4) * (d i k * d j l + d i l * d j k) - (3/4) * d i j * d i k * d i l := by
  have sub (f g : Outcome N → ℝ) : E (fun w ↦ f w - g w) = E f - E g := by
    simp [E,mul_sub,Finset.sum_sub_distrib]
  have const (c : ℝ) : E (fun _ : Outcome N ↦ c) = c := by simp [E,← Finset.sum_mul,joint_mass]
  unfold z
  simp only [sub_mul, mul_sub, sub]
  rw [show E (fun w ↦ value (w i)*value (w j)*(value (w k)*value (w l))) = _ from
    congrArg E (funext fun w ↦ (mul_assoc _ (value (w k)) (value (w l))).symm)]
  rw [four]
  simp_rw [mul_comm (value _ * value _) ((3/2)*d k l)]
  simp only [E_mul, two, const]
  ring

theorem quadratic_variance (Q : Matrix (Fin N) (Fin N) ℝ) :
    (∑ w, jointWeight w * (quadratic Q w - (3/2)*Q.trace)^2) =
      (9/4)*(∑ i, ∑ j, ((Q i j)^2 + Q i j * Q j i)) - (3/4)*(∑ i, (Q i i)^2) := by
  let p := fun a : Fin N × Fin N ↦ Q a.1 a.2
  let f := fun (w : Outcome N) (a : Fin N × Fin N) ↦ z w a.1 a.2
  have expand (w : Outcome N) : quadratic Q w - (3/2)*Q.trace = ∑ a, p a * f w a := by
    simp [quadratic, p, f, z, d, Matrix.trace, Fintype.sum_prod_type, mul_sub,
      Finset.sum_sub_distrib, Finset.mul_sum, mul_ite, value, mul_comm]
  change E (fun w ↦ (quadratic Q w - (3/2)*Q.trace)^2) = _
  simp_rw [expand, pow_two, Finset.sum_mul, Finset.mul_sum, E_sum]
  simp_rw [show ∀ a b c e : ℝ, a*b*(c*e) = a*(c*(b*e)) by intros; ring, E_mul]
  simp only [f,p,Fintype.sum_prod_type,cov]
  have pairing (a b : Fin N) : (∑ k, d a k * ∑ l, d b l * Q k l) = Q a b := by
    simp [d, ite_mul]
  have contract (i j k l : Fin N) :
      Q k l * (9/4 * (d i k * d j l + d i l * d j k) - 3/4*d i j*d i k*d i l) =
        9/4*(d i k*(d j l*Q k l) + d j k*(d i l*Q k l)) -
          (3/4*d i j)*(d i k*(d i l*Q k l)) := by ring
  simp only [contract, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib, pairing]
  have dist (i j : Fin N) : Q i j * (9/4*(Q i j + Q j i) - 3/4*d i j*Q i i) =
      9/4*(Q i j * Q i j + Q i j * Q j i) - 3/4*(if i=j then Q i i*Q i i else 0) := by
    by_cases h : i=j <;> simp [d,h] <;> ring
  simp [dist, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]

theorem symmetric_variance (Q : Matrix (Fin N) (Fin N) ℝ) (hs : Q.transpose = Q) :
    (∑ w, jointWeight w * (quadratic Q w - (3/2)*Q.trace)^2) =
      (9/2)*(∑ i, ∑ j, (Q i j)^2) - (3/4)*(∑ i, (Q i i)^2) := by
  have h (i j : Fin N) : Q i j ^ 2 + Q i j * Q j i = 2 * Q i j ^ 2 := by
    rw [show Q j i = Q i j from congrFun (congrFun hs i) j]; ring
  rw [quadratic_variance]
  simp_rw [h, ← Finset.mul_sum]
  ring

theorem projection_variance (Q : Matrix (Fin N) (Fin N) ℝ) (hs : Q.transpose = Q)
    (hp : Q*Q = Q) :
    (∑ w, jointWeight w * (quadratic Q w - (3/2)*Q.trace)^2) =
      (9/2)*Q.trace - (3/4)*(∑ i, (Q i i)^2) := by
  have row (i : Fin N) : ∑ j, Q i j ^ 2 = Q i i := by
    conv_rhs => rw [← hp, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [show Q j i = Q i j from congrFun (congrFun hs i) j, pow_two]
  rw [symmetric_variance Q hs]
  simp only [row,Matrix.trace,Matrix.diag_apply]

theorem projection_variance_le (Q : Matrix (Fin N) (Fin N) ℝ) (hs : Q.transpose = Q)
    (hp : Q*Q = Q) :
    (∑ w, jointWeight w * (quadratic Q w - (3/2)*Q.trace)^2) ≤ (9/2)*Q.trace := by
  rw [projection_variance Q hs hp]
  exact sub_le_self _ (by positivity)

theorem cantelli {α : Type*} [Fintype α] (w X : α → ℝ) (hw : ∀ x, 0 ≤ w x)
    (h₁ : ∑ x, w x = 1) (a : ℝ) (ha : 0 < a) :
    let m := ∑ x, w x * X x
    let v := ∑ x, w x * (X x - m)^2
    (∑ x with X x ≤ m-a, w x) ≤ v/(v+a^2) := by
  intro m v
  have hv : 0 ≤ v := Finset.sum_nonneg fun x _ ↦ mul_nonneg (hw x) (sq_nonneg _)
  let b := v/a
  have hb : 0 ≤ b := div_nonneg hv ha.le
  have hc : ∑ x, w x * (X x - m) = 0 := by
    simp [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h₁, m]
  have shift : ∑ x, w x * (X x-m-b)^2 = v+b^2 := by
    have t (x : α) : w x*(X x-m-b)^2 =
        w x*(X x-m)^2 - (w x*(X x-m))*(2*b) + w x*b^2 := by ring
    simp only [t, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
      hc,h₁,zero_mul,sub_zero,one_mul,v]
  have bound : (∑ x with X x ≤ m-a, w x)*(a+b)^2 ≤ v+b^2 := by
    rw [← shift, Finset.sum_mul, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro x _
    split_ifs with h
    · apply mul_le_mul_of_nonneg_left _ (hw x)
      nlinarith [sq_nonneg (m-a-X x), mul_nonneg (show 0 ≤ m-a-X x by linarith)
        (show 0 ≤ a+b by linarith)]
    · exact mul_nonneg (hw x) (sq_nonneg _)
  apply (le_div_iff₀ (by positivity : 0 < (a+b)^2)).mpr bound |>.trans_eq
  dsimp [b]
  field_simp
  ring

theorem quadratic_cantelli (Q : Matrix (Fin N) (Fin N) ℝ) (a : ℝ) (ha : 0 < a) :
    let m := (3/2)*Q.trace
    let v := ∑ w, jointWeight w * (quadratic Q w - m)^2
    (∑ w with quadratic Q w ≤ m-a, jointWeight w) ≤ v/(v+a^2) := by
  have hw (w : Outcome N) : 0 ≤ jointWeight w := by
    unfold jointWeight weight
    positivity
  simpa only [quadratic_mean] using cantelli jointWeight (quadratic Q) hw joint_mass a ha

#print axioms quadratic_cantelli
#print axioms coordinate_moments
#print axioms odd_moments
#print axioms joint_mass
#print axioms quadratic_mean
#print axioms quadratic_variance
#print axioms symmetric_variance
#print axioms projection_variance
#print axioms projection_variance_le
#print axioms cantelli

end SigabaNeo.Wall1.CBDQuadratic
