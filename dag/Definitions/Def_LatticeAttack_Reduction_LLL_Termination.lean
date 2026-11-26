module

public import Definitions.Def_LatticeAttack_Reduction_LLL_Bridge
import all Definitions.Def_LatticeAttack_Reduction_LLL_Bridge

set_option autoImplicit true

public section

namespace SigabaNeo.LLL.Algorithm

open Matrix InnerProductSpace
open scoped RealInnerProductSpace

variable {n d : ℕ}

private theorem dot_ortho (B : Rows n d) {i j : Fin n} (h : i ≠ j) :
    dot (starRow B i) (starRow B j) = 0 := by
  apply Rat.cast_injective (α := ℝ)
  rw [dot_cast, Rat.cast_zero, starRow_cast, starRow_cast]
  exact gramSchmidt_orthogonal ℝ _ h.symm

/-- Gram determinant of rows expanded in a unit lower triangular system of orthogonal rows. -/
private theorem gram_triangular {m : ℕ} (T : Matrix (Fin m) (Fin m) ℚ)
    (G : Matrix (Fin m) (Fin d) ℚ) (ht : T.IsLowerTriangular) (hd : ∀ a, T a a = 1)
    (ho : ∀ a b, a ≠ b → dot (G a) (G b) = 0) :
    ((T * G) * (T * G).transpose).det = ∏ a, dot (G a) (G a) := by
  have hG : G * G.transpose = diagonal (fun a ↦ dot (G a) (G a)) := by
    ext a b
    by_cases e : a = b
    · subst b; simp [Matrix.mul_apply, diagonal_apply_eq, dot]
    · simpa [Matrix.mul_apply, diagonal_apply_ne _ e, dot] using ho a b e
  have hT : T.det = 1 := by simp [det_of_isLowerTriangular T ht, hd]
  rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc G, hG]
  simp [det_mul, hT]

private theorem row_expansion (B : Rows n d) (i : Fin n) :
    rationalRow B i = starRow B i + ∑ j : Fin i.val,
      mu B i ⟨j.val, lt_trans j.isLt i.isLt⟩ • starRow B ⟨j.val, lt_trans j.isLt i.isLt⟩ := by
  conv_rhs => lhs; rw [starRow]
  exact (sub_add_cancel _ _).symm

/-- An integer Gram determinant computed from an ordered orthogonal decomposition. -/
private theorem gram_of_expansion {m : ℕ} (A : Matrix (Fin m) (Fin d) ℤ)
    (G : Matrix (Fin m) (Fin d) ℚ) (c : Fin m → Fin m → ℚ)
    (ho : ∀ a b, a ≠ b → dot (G a) (G b) = 0)
    (he : ∀ (a : Fin m) (u : Fin d), (A a u : ℚ) =
      G a u + ∑ b : Fin a.val, c a (b.castLE a.isLt.le) * G (b.castLE a.isLt.le) u) :
    (gramDet A : ℚ) = ∏ a, dot (G a) (G a) := by
  classical
  let T : Matrix (Fin m) (Fin m) ℚ := fun a b ↦ if b = a then 1 else if b < a then c a b else 0
  have hA : A.map (Int.castRingHom ℚ) = T * G := by
    ext a u
    rw [Matrix.mul_apply]
    change (A a u : ℚ) = _
    rw [he]
    simp only [T, ite_mul, one_mul, zero_mul, Finset.sum_ite, Finset.filter_eq', Finset.mem_univ,
      ite_true, Finset.sum_singleton, Finset.sum_const_zero, add_zero]
    congr 1
    apply Finset.sum_bij (fun (b : Fin a.val) _ ↦ b.castLE a.isLt.le)
    · intro b _; have hb : b.castLE a.isLt.le < a := b.isLt; simp [hb, hb.ne]
    · exact fun _ _ _ _ e ↦ Fin.ext (congrArg (@Fin.val m) e)
    · intro b hb
      have h : b < a := by simpa using (Finset.mem_filter.mp hb).2
      exact ⟨⟨b.val,h⟩, Finset.mem_univ _, rfl⟩
    · intros; rfl
  have ht : T.IsLowerTriangular := fun a b (h : a < b) ↦ by simp [T, h.ne', h.not_gt]
  have := gram_triangular T G ht (by simp [T]) ho
  rw [← hA] at this
  change (Int.castRingHom ℚ) (A * A.transpose).det = _
  rw [RingHom.map_det]
  change ((A * A.transpose).map (Int.castRingHom ℚ)).det = _
  rw [Matrix.map_mul]
  exact this

theorem gramDet_prefix (B : Rows n d) (j : Fin n) :
    (gramDet (prefixRows B j) : ℚ) = ∏ a : Fin (j.val + 1), normSq B (a.castLE j.isLt) := by
  apply gram_of_expansion _ (fun a ↦ starRow B (a.castLE j.isLt))
    (fun a b ↦ mu B (a.castLE j.isLt) (b.castLE j.isLt))
  · intro a b h
    exact dot_ortho B (fun e ↦ h (Fin.castLE_injective _ e))
  · intro a u
    simpa [Finset.sum_apply, prefixRows, rationalRow, Fin.castLE] using congrFun (row_expansion B (a.castLE j.isLt)) u

private theorem dot_add_smul (x y z : Fin d → ℚ) (c : ℚ) :
    dot (x + c • y) z = dot x z + c * dot y z := by
  simp [dot, add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]

private theorem dot_comm' (x y : Fin d → ℚ) : dot x y = dot y x := by simp [dot, mul_comm]

private theorem swap_tail (B : Rows n d) (i j : Fin n) (adj : j.val + 1 = i.val) :
    rationalRow B i = (starRow B i + mu B i j • starRow B j) +
      ∑ b : Fin j.val, mu B i ⟨b.val, lt_trans b.isLt j.isLt⟩ •
        starRow B ⟨b.val, lt_trans b.isLt j.isLt⟩ := by
  obtain ⟨iv, hi⟩ := i
  change j.val + 1 = iv at adj
  subst iv
  conv_lhs => rw [row_expansion, Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, Fin.eta]
  abel

private theorem swapped_prefix (B : Rows n d) (i j : Fin n) (adj : j.val + 1 = i.val) :
    (gramDet (prefixRows (swapRows B i j) j) : ℚ) =
      (∏ b : Fin j.val, normSq B ⟨b.val, lt_trans b.isLt j.isLt⟩) *
        (normSq B i + mu B i j ^ 2 * normSq B j) := by
  classical
  let idx (a : Fin (j.val+1)) := a.castLE j.isLt
  let tail := starRow B i + mu B i j • starRow B j
  let G : Matrix (Fin (j.val+1)) (Fin d) ℚ := fun a ↦ if a.val = j.val then tail else starRow B (idx a)
  let src (a : Fin (j.val+1)) := if a.val = j.val then i else idx a
  have ltj (a : Fin (j.val+1)) (ha : a.val ≠ j.val) : idx a < j := by
    change a.val < j.val; omega
  have hji : j < i := by change j.val < i.val; omega
  have orth (a : Fin (j.val+1)) (ha : a.val ≠ j.val) : dot tail (starRow B (idx a)) = 0 := by
    rw [dot_add_smul, dot_ortho B ((ltj a ha).trans hji).ne', dot_ortho B (ltj a ha).ne']; ring
  rw [gram_of_expansion _ G (fun a b ↦ mu B (src a) (idx b))]
  · rw [Fin.prod_univ_castSucc]
    congr 1
    · apply Finset.prod_congr rfl; intro a _; simp [G, a.isLt.ne, normSq, idx, Fin.castLE]
    · simp only [G, Fin.val_last, ite_true, tail, dot_add_smul]
      rw [dot_comm' (starRow B i), dot_comm' (starRow B j), dot_add_smul, dot_add_smul,
        dot_ortho B hji.ne, dot_ortho B hji.ne']
      unfold normSq; ring
  · intro a b hab
    by_cases ha : a.val = j.val <;> by_cases hb : b.val = j.val
    · exact False.elim (hab (Fin.ext (ha.trans hb.symm)))
    · simpa [G, ha, hb] using orth b hb
    · simpa [G, ha, hb, dot_comm' (starRow B (idx a)) tail] using orth a ha
    · exact (by simpa [G, ha, hb] using dot_ortho B (fun e : idx a = idx b ↦ hab (Fin.castLE_injective _ e)))
  · intro a u
    have earlier (b : Fin a.val) : b.val ≠ j.val := by omega
    simp only [G, Fin.val_castLE, ite_eq_right_iff.mpr (fun h ↦ False.elim (earlier _ h))]
    by_cases ha : a.val = j.val
    · have ea : idx a = j := Fin.ext ha
      have hh := congrFun (swap_tail B i j adj) u
      obtain ⟨av, hav⟩ := a
      change av = j.val at ha
      subst av
      simpa [src, idx, tail, prefixRows, swapRows, Function.comp_def, ea, hji.ne,
        Finset.sum_apply, rationalRow, Fin.castLE] using hh
    · have h := congrFun (row_expansion B (idx a)) u
      have es : Equiv.swap i j (a.castLE j.isLt) = a.castLE j.isLt := Equiv.swap_apply_of_ne_of_ne ((ltj a ha).trans hji).ne (ltj a ha).ne
      simp only [prefixRows, swapRows, Function.comp_apply, es]
      simpa [ha, src, prefixRows, swapRows, Function.comp_def, ← show a.castLE j.isLt = idx a from rfl,
        Equiv.swap_apply_of_ne_of_ne ((ltj a ha).trans hji).ne (ltj a ha).ne,
        Finset.sum_apply, rationalRow, idx, Fin.castLE] using h

theorem gramDet_swap_contract (B : Rows n d) (h : LinearIndependent ℤ B)
    (i j : Fin n) (adj : j.val + 1 = i.val) (bad : ¬ lovasz B i j) :
    4 * gramDet (prefixRows (swapRows B i j) j) < 3 * gramDet (prefixRows B j) := by
  let P := ∏ b : Fin j.val, normSq B ⟨b.val, lt_trans b.isLt j.isLt⟩
  have orig : (gramDet (prefixRows B j) : ℚ) = P * normSq B j := by
    rw [gramDet_prefix, Fin.prod_univ_castSucc]
    rfl
  have pos : 0 < P := by
    have hp : (0 : ℚ) < gramDet (prefixRows B j) := by exact_mod_cast gramDet_prefix_pos B h j
    rw [orig] at hp
    have nn : 0 ≤ normSq B j := by unfold normSq dot; exact Finset.sum_nonneg fun a _ ↦ mul_self_nonneg _
    exact pos_of_mul_pos_left hp nn
  unfold lovasz at bad
  have hh := mul_lt_mul_of_pos_left (lt_of_not_ge bad) pos
  have goalQ : (4 : ℚ) * (gramDet (prefixRows (swapRows B i j) j) : ℚ) <
      3 * (gramDet (prefixRows B j) : ℚ) := by
    rw [orig, swapped_prefix B i j adj]
    change 4 * (P * _) < _
    linarith
  exact_mod_cast goalQ

theorem potential_swap_contract (B : Rows n d) (h : LinearIndependent ℤ B)
    (i j : Fin n) (adj : j.val + 1 = i.val) (bad : ¬ lovasz B i j) :
    4 * potential (swapRows B i j) < 3 * potential B := by
  classical
  let rest := Finset.univ.erase j
  have eq : (∏ k ∈ rest, gramDet (prefixRows (swapRows B i j) k)) =
      ∏ k ∈ rest, gramDet (prefixRows B k) := Finset.prod_congr rfl fun k hk ↦
        gramDet_swap_of_ne B i j k adj (Finset.mem_erase.mp hk).1
  have hp := Finset.prod_pos (s := rest) (fun k _ ↦ gramDet_prefix_pos B h k)
  unfold potential
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), ← Finset.prod_erase_mul _ (fun k ↦ gramDet (prefixRows B k)) (Finset.mem_univ j)]
  rw [show Finset.univ.erase j = rest from rfl, eq]
  linarith only [mul_lt_mul_of_pos_left (gramDet_swap_contract B h i j adj bad) hp]

#print axioms gramDet_prefix
#print axioms gramDet_swap_contract
#print axioms potential_swap_contract

private theorem independent_shear (B : Rows n d) (h : LinearIndependent ℤ B) (i j : Fin n)
    (hj : j < i) (z : ℤ) : LinearIndependent ℤ (shear B i j z) := by
  apply h.update
  refine ⟨1, one_mem _, Finsupp.single i 1 - Finsupp.single j z, ?_, ?_⟩
  · simp [hj.ne]
  · simp

private theorem star_before (B : Rows n d) (i j a : Fin n) (z : ℤ) (ha : a < i) :
    starRow (shear B i j z) a = starRow B a := by
  conv_lhs => rw [starRow]
  conv_rhs => rw [starRow]
  have e : rationalRow (shear B i j z) a = rationalRow B a := by
    funext u; simp [shear, rationalRow, ha.ne]
  simp only [e]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  rw [star_before B i j _ z (lt_trans (show (⟨b.val, lt_trans b.isLt a.isLt⟩ : Fin n) < a from b.isLt) ha)]
termination_by a.val
decreasing_by exact b.isLt

private theorem mu_shear_same (B : Rows n d) (i j b : Fin n) (z : ℤ) (hb : b < i) :
    mu (shear B i j z) i b = mu B i b - z * mu B j b := by
  have e : rationalRow (shear B i j z) i =
      rationalRow B i + (-(z : ℚ)) • rationalRow B j := by
    ext; simp [rationalRow, shear, sub_eq_add_neg]
  simp only [mu, normSq, star_before B i j b z hb, e, dot_add_smul]
  ring

private theorem mu_above (B : Rows n d) {j b : Fin n} (h : j < b) : mu B j b = 0 := by
  have hz : dot (rationalRow B j) (starRow B b) = 0 := by
    apply Rat.cast_injective (α := ℝ)
    rw [dot_cast, starRow_cast, Rat.cast_zero]
    exact gramSchmidt_inv_triangular ℝ (realRows B) h
  simp [mu, hz]

private theorem mu_diag (B : Rows n d) (h : LinearIndependent ℤ B) (j : Fin n) : mu B j j = 1 := by
  have hn : normSq B j ≠ 0 := by
    have hh := gramDet_prefix B j
    rw [Fin.prod_univ_castSucc] at hh
    intro hz
    rw [show (Fin.last j.val).castLE j.isLt = j from Fin.ext rfl, hz, mul_zero] at hh
    have := gramDet_prefix_pos B h j
    exact (ne_of_gt this) (by exact_mod_cast hh)
  apply (div_eq_iff hn).mpr
  rw [one_mul]
  apply Rat.cast_injective (α := ℝ)
  rw [dot_cast, normSq, norm_cast, starRow_cast]
  change ⟪gramSchmidt ℝ (realRows B) j, realRows B j⟫_ℝ = _
  conv_lhs => rhs; rw [gramSchmidt_def'' ℝ (realRows B) j]
  rw [inner_add_right, inner_sum, real_inner_self_eq_norm_sq, add_eq_left]
  apply Finset.sum_eq_zero
  intro k hk
  simp [real_inner_smul_right, gramSchmidt_orthogonal ℝ (realRows B) (Finset.mem_Iio.mp hk).ne']

private def badSize (B : Rows n d) (p : Fin n × Fin n) : Bool :=
  decide (p.2 < p.1 ∧ 1 / 2 < |mu B p.1 p.2|)

private def before (p q : Fin n × Fin n) := p.1 < q.1 ∨ p.1 = q.1 ∧ q.2 < p.2

private theorem pairs_order (n : ℕ) : (pairs n).Pairwise before := by
  rw [pairs, List.pairwise_flatMap]
  constructor
  · intro i _
    rw [List.pairwise_map, List.pairwise_reverse]
    exact (List.sortedLT_finRange n).pairwise.imp fun h ↦ Or.inr ⟨rfl, h⟩
  · apply (List.sortedLT_finRange n).pairwise.imp
    intro i k hik p hp q hq
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hp
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hq
    exact Or.inl hik

private theorem findIdx_progress {α : Type*} {r : α → α → Prop} {p q : α → Bool} {a : α}
    (l : List α) (hs : l.Pairwise r) (hf : l.find? p = some a) (ha : q a = false)
    (hprev : ∀ b, r b a → p b = false → q b = false) : l.findIdx p < l.findIdx q := by
  induction l with
  | nil => simp at hf
  | cons b l ih =>
    by_cases hb : p b
    · simp [hb] at hf
      subst b
      simp [List.findIdx_cons, hb, ha]
    · have hf' : l.find? p = some a := by simpa [hb] using hf
      have hq := hprev b ((List.pairwise_cons.mp hs).1 _ (List.mem_of_find?_eq_some hf')) (by simpa using hb)
      simpa [List.findIdx_cons, hb, hq] using ih hs.tail hf'

private theorem shear_progress (B : Rows n d) (h : LinearIndependent ℤ B) {p : Fin n × Fin n}
    (hs : (pairs n).find? (badSize B) = some p) :
    (pairs n).findIdx (badSize B) <
      (pairs n).findIdx (badSize (shear B p.1 p.2 (round (mu B p.1 p.2)))) := by
  have hb := List.find?_some hs
  have hp : p.2 < p.1 := (of_decide_eq_true hb).1
  apply findIdx_progress _ (pairs_order n) hs
  · simp [badSize, mu_shear_same _ _ _ _ _ hp, mu_diag B h, hp]
    simpa using abs_sub_round (mu B p.1 p.2)
  · rintro ⟨a,b⟩ (hlt | ⟨he,hgt⟩) hfalse
    · by_cases hba : b < a
      · let z := round (mu B p.1 p.2)
        have e : rationalRow (shear B p.1 p.2 z) a = rationalRow B a := by
          funext u; simp [rationalRow, shear, hlt.ne]
        have em : mu (shear B p.1 p.2 z) a b = mu B a b := by
          rw [mu, mu, normSq, normSq, e, star_before _ _ _ _ _ (hba.trans hlt)]
        dsimp [z] at em
        simpa only [badSize, em] using hfalse
      · simp [badSize, hba]
    · change a = p.1 at he
      subst a
      by_cases hba : b < p.1
      · simpa [badSize, mu_shear_same _ _ _ _ _ hba, mu_above B hgt] using hfalse
      · simp [badSize, hba]

/-- Each potential level allows one full ordered scan of size-reduction pairs. -/
noncomputable def fuelBound (B : Rows n d) : ℕ :=
  (Nat.log 2 ((potential B).toNat ^ 3) + 1) * ((pairs n).length + 1) +
    ((pairs n).length - (pairs n).findIdx (badSize B))

private theorem fuel_pos (B : Rows n d) : 0 < fuelBound B := by
  unfold fuelBound
  positivity

private theorem fuel_shear_lt (B : Rows n d) (h : LinearIndependent ℤ B) {p : Fin n × Fin n}
    (hs : (pairs n).find? (badSize B) = some p) :
    fuelBound (shear B p.1 p.2 (round (mu B p.1 p.2))) < fuelBound B := by
  have hb := List.find?_some hs
  have hp : p.2 < p.1 := (of_decide_eq_true (show decide (_ ∧ _) = true from hb)).1
  simp only [fuelBound, potential_shear _ _ _ hp, Nat.add_lt_add_iff_left]
  have := shear_progress B h hs
  have := List.findIdx_le_length (xs := pairs n)
    (p := badSize (shear B p.1 p.2 (round (mu B p.1 p.2))))
  omega

private theorem fuel_swap_lt (B : Rows n d) (h : LinearIndependent ℤ B)
    (i j : Fin n) (adj : j.val + 1 = i.val) (bad : ¬ lovasz B i j) :
    fuelBound (swapRows B i j) < fuelBound B := by
  have hc := potential_swap_contract B h i j adj bad
  have hp := potential_one_le B h
  let C := swapRows B i j
  have hC := potential_one_le C (h.comp _ (Equiv.swap i j).injective)
  change 4 * potential C < 3 * potential B at hc
  have hd : 4 * (potential C).toNat ≤ 3 * (potential B).toNat := by omega
  have cube := Nat.pow_le_pow_left hd 3
  rw [mul_pow, mul_pow] at cube
  norm_num at cube
  have hp3 : (potential C).toNat ^ 3 ≠ 0 := by
    have : (potential C).toNat ≠ 0 := by omega
    exact pow_ne_zero _ this
  have logs := Nat.log_mono_right (b := 2)
    (show (potential C).toNat ^ 3 * 2 ≤ (potential B).toNat ^ 3 by omega)
  rw [Nat.log_mul_base (by decide) hp3] at logs
  have hm := Nat.mul_le_mul_right ((pairs n).length + 1) (Nat.succ_le_succ logs)
  rw [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul] at hm
  simp only [Nat.succ_eq_add_one] at hm
  change fuelBound C < fuelBound B
  unfold fuelBound
  omega

theorem run_normal_of_fuel (fuel : ℕ) (B : Rows n d) (h : LinearIndependent ℤ B)
    (hf : fuelBound B ≤ fuel) : (run fuel B).normal = true := by
  induction fuel generalizing B with
  | zero => have := fuel_pos B; omega
  | succ f ih =>
    rw [run]
    dsimp only
    split
    · rename_i p hs
      have hb := List.find?_some hs
      have hp : p.2 < p.1 := (of_decide_eq_true (show decide (_ ∧ _) = true from hb)).1
      exact ih _ (independent_shear _ h _ _ hp _) (by have := fuel_shear_lt B h hs; omega)
    · split
      · rename_i p hw
        have hh := List.find?_some hw
        have hp := of_decide_eq_true (show decide (_ ∧ _) = true from hh)
        exact ih _ (h.comp _ (Equiv.swap p.1 p.2).injective)
          (by have := fuel_swap_lt B h _ _ hp.1 hp.2; omega)
      · rfl

theorem run_swap_bound (fuel : ℕ) (B : Rows n d) (h : LinearIndependent ℤ B) :
    (4 : ℤ) ^ (run fuel B).swaps ≤ 3 ^ (run fuel B).swaps * potential B := by
  induction fuel generalizing B with
  | zero =>
    have := potential_one_le B h
    rw [run]
    dsimp only
    split <;> first | split <;> simpa | simpa
  | succ f ih =>
    rw [run]
    dsimp only
    split
    · rename_i p hs
      have hb := List.find?_some hs
      have hp : p.2 < p.1 := (of_decide_eq_true (show decide (_ ∧ _) = true from hb)).1
      simpa only [potential_shear _ _ _ hp] using
        ih _ (independent_shear _ h _ _ hp (round (mu B p.1 p.2)))
    · split
      · rename_i p hw
        have hh := List.find?_some hw
        have hp := of_decide_eq_true (show decide (_ ∧ _) = true from hh)
        let C := swapRows B p.1 p.2
        have hi := ih C (h.comp _ (Equiv.swap p.1 p.2).injective)
        have hc : 4 * potential C ≤ 3 * potential B := (potential_swap_contract B h _ _ hp.1 hp.2).le
        change (4 : ℤ) ^ ((run f C).swaps + 1) ≤ 3 ^ ((run f C).swaps + 1) * potential B
        rw [pow_succ, pow_succ]
        linarith only [mul_le_mul_of_nonneg_left hc (show (0 : ℤ) ≤ 3 ^ (run f C).swaps by positivity), hi]
      · simpa using potential_one_le B h

theorem realRows_independent (B : Rows n n) (h : LinearIndependent ℤ B) :
    LinearIndependent ℝ (realRows B) := by
  let A : Matrix (Fin n) (Fin n) ℤ := B
  have hd : A.det ≠ 0 := by
    intro hz
    obtain ⟨v, hv, he⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hz
    exact hv ((Matrix.vecMul_injective_iff.mpr (show LinearIndependent ℤ A.row from h))
      (he.trans (Matrix.zero_vecMul A).symm))
  let R := (Int.castRingHom ℝ).mapMatrix A
  have hR : R.det ≠ 0 := by
    change ((Int.castRingHom ℝ).mapMatrix A).det ≠ 0
    rw [← RingHom.map_det]
    change (A.det : ℝ) ≠ 0
    exact_mod_cast hd
  have hi := Matrix.linearIndependent_rows_of_det_ne_zero hR
  let e := (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm
  have hi' := hi.map' e.toLinearMap e.ker
  convert hi' using 1
  funext i
  ext a
  simp [realRows, realVec, rationalRow, e, R, A]
  rfl

theorem run_approx [NeZero n] (B : Rows n n) (h : LinearIndependent ℤ B)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ∈ Submodule.span ℤ (Set.range (realRows B)))
    (hne : v ≠ 0) :
    ‖realRows (run (fuelBound B) B).rows 0‖ ≤ (2 : ℝ) ^ (((n : ℝ) - 1) / 2) * ‖v‖ :=
  run_approx_of_normal _ B (realRows_independent B h) (run_normal_of_fuel _ B h le_rfl) v hv hne

#print axioms realRows_independent
#print axioms run_approx
#print axioms run_normal_of_fuel
#print axioms run_swap_bound

end SigabaNeo.LLL.Algorithm
