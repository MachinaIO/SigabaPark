import SigabaNeoStd.Lattices.Boxes
import Mathlib.Basic.ENNReal.Inv

/-!
# Boxes of families of ring elements (copy of `SigabaNeoStd.Lattices.RingBoxes`)

A verbatim copy, in its own namespace, of `SigabaNeoStd.Lattices.RingBoxes` at v0.1.1, which the
DAG environment does not build (it is not imported from the root `SigabaNeoStd`).


For a finite index type `P` and `R = ℤ_Q[X]/(X^N + 1)`, a family `v : P → R` is a vector of
`|P| N` coefficients (`famCoeffs`). On families:

* `famBig B`: the big box, the image of `|P| N B` fair bits (centered residues, `bigBox`);
* `famBall r`: the families whose entries have `cnorm ≤ r` (`mem_famBall`), the product of balls;
* `famBall (2^{B−1} − 1) ⊆ famBig B` (`famBall_subset_big`); shifting by a family within `s`
  moves `famBall r` into `famBall (r + s)` (`add_mem_famBall`, `sub_mem_famBall`);
* **`famAbort_le`**: the abort probability of box rejection with the big box of `B` bits and the
  inner ball of radius `2^{B−1} − 1 − 2τ` is at most `2^{−κ}` when `|P| N (4τ + 1) 2^κ ≤ 2^B`.

These are the boxes of key generation by box rejection (`SigabaNeo.Lattices.boxSample`) for keys
whose short part is a family of ring elements (as in `AdvancedEncryption.ExpLUT`).
-/

namespace AdvancedEncryption.WE.RingBoxesCopy

open Cslib SigabaNeo SigabaNeo.Lattices
open scoped ENNReal

variable {Q N : ℕ} [NeZero Q] {P : Type*} [Fintype P] [DecidableEq P]

/-- The coefficients of a family of ring elements. -/
def famCoeffs : (P → Negacyclic (ZMod Q) N) ≃ (P × Fin N → ZMod Q) :=
  (Equiv.arrowCongr (Equiv.refl P) Negacyclic.coeffsEquiv).trans (Equiv.curry _ _ _).symm

omit [NeZero Q] [Fintype P] [DecidableEq P] in
@[simp] theorem famCoeffs_apply (v : P → Negacyclic (ZMod Q) N) (p : P) (j : Fin N) :
    famCoeffs v (p, j) = (v p).coeffs j := rfl

omit [NeZero Q] [Fintype P] [DecidableEq P] in
theorem famCoeffs_add (u v : P → Negacyclic (ZMod Q) N) :
    famCoeffs (u + v) = famCoeffs u + famCoeffs v := by
  funext ⟨p, j⟩; simp [Negacyclic.coeffs_add]

omit [NeZero Q] [Fintype P] [DecidableEq P] in
theorem famCoeffs_sub (u v : P → Negacyclic (ZMod Q) N) :
    famCoeffs (u - v) = famCoeffs u - famCoeffs v := by
  funext ⟨p, j⟩; simp [Negacyclic.coeffs_sub]

variable (Q N P) in
/-- **The ball**: the families whose entries have all coefficients within `r`. -/
def famBall (r : ℕ) : Finset (P → Negacyclic (ZMod Q) N) :=
  (ball Q r).map famCoeffs.symm.toEmbedding

theorem mem_famBall {r : ℕ} {v : P → Negacyclic (ZMod Q) N} :
    v ∈ famBall Q N P r ↔ ∀ p, cnorm (v p) ≤ r := by
  simp only [famBall, Finset.mem_map_equiv, Equiv.symm_symm, mem_ball]
  constructor
  · intro h p
    exact (cnorm_le_iff _ _).mpr fun j => h (p, j)
  · rintro h ⟨p, j⟩
    exact (zabs_coeffs_le_cnorm _ j).trans (h p)

variable (Q N P) in
/-- **The big box**: the image of `|P| N B` fair bits. -/
def famBig (B : ℕ) (hB : 2 ^ B ≤ Q) : Finset (P → Negacyclic (ZMod Q) N) :=
  (bigBox B hB).map famCoeffs.symm.toEmbedding

omit [NeZero Q] in
theorem famBig_nonempty (B : ℕ) (hB : 2 ^ B ≤ Q) : (famBig Q N P B hB).Nonempty := by
  simp only [famBig, Finset.map_nonempty, bigBox]
  exact Finset.univ_nonempty

theorem famBall_subset_big (B : ℕ) (hB : 2 ^ B ≤ Q) (hB1 : 1 ≤ B) :
    famBall Q N P (2 ^ (B - 1) - 1) ⊆ famBig Q N P B hB :=
  Finset.map_subset_map.mpr (ball_subset_bigBox B hB hB1)

theorem famBall_mono {r s : ℕ} (h : r ≤ s) : famBall Q N P r ⊆ famBall Q N P s := by
  intro v hv
  rw [mem_famBall] at hv ⊢
  exact fun p => (hv p).trans h

/-- A shift by a family within `s` moves `famBall r` into `famBall (r + s)`. -/
theorem add_mem_famBall {r s : ℕ} {y t : P → Negacyclic (ZMod Q) N} (hy : y ∈ famBall Q N P r)
    (ht : ∀ p, cnorm (t p) ≤ s) : y + t ∈ famBall Q N P (r + s) := by
  rw [mem_famBall] at hy ⊢
  exact fun p => (cnorm_add_le _ _).trans (Nat.add_le_add (hy p) (ht p))

theorem sub_mem_famBall {r s : ℕ} {y t : P → Negacyclic (ZMod Q) N} (hy : y ∈ famBall Q N P r)
    (ht : ∀ p, cnorm (t p) ≤ s) : y - t ∈ famBall Q N P (r + s) := by
  rw [mem_famBall] at hy ⊢
  exact fun p => (cnorm_sub_le _ _).trans (Nat.add_le_add (hy p) (ht p))

theorem card_famBig (B : ℕ) (hB : 2 ^ B ≤ Q) :
    (famBig Q N P B hB).card = (2 ^ B) ^ (Fintype.card P * N) := by
  rw [famBig, Finset.card_map, card_bigBox, Fintype.card_prod, Fintype.card_fin]

theorem card_famBall (r : ℕ) (hr : 2 * r < Q) :
    (famBall Q N P r).card = (2 * r + 1) ^ (Fintype.card P * N) := by
  rw [famBall, Finset.card_map, card_ball _ hr, Fintype.card_prod, Fintype.card_fin]

/-- **The abort probability of box rejection** with the big box of `B` bits and the inner ball of
radius `2^{B−1} − 1 − 2τ`: at most `2^{−κ}` when `|P| N (4τ + 1) 2^κ ≤ 2^B`. -/
theorem famAbort_le (B τ κ : ℕ) (hB : 2 ^ B ≤ Q) (hB1 : 1 ≤ B) (hτ : 4 * τ + 1 ≤ 2 ^ B)
    (hκ : Fintype.card P * N * (4 * τ + 1) * 2 ^ κ ≤ 2 ^ B) :
    (((famBig Q N P B hB).card - (famBall Q N P (2 ^ (B - 1) - 1 - 2 * τ)).card : ℕ) : ℝ≥0∞) /
      (famBig Q N P B hB).card ≤ ((2 : ℝ≥0∞) ^ κ)⁻¹ := by
  set n := Fintype.card P * N
  have hpow : 2 ^ B = 2 * 2 ^ (B - 1) := by rw [← pow_succ']; congr 1; omega
  have hrad : 2 * (2 ^ (B - 1) - 1 - 2 * τ) + 1 = 2 ^ B - (4 * τ + 1) := by omega
  have hcI : (famBall Q N P (2 ^ (B - 1) - 1 - 2 * τ)).card = (2 ^ B - (4 * τ + 1)) ^ n := by
    rw [card_famBall _ (by omega), hrad]
  rw [card_famBig, hcI]
  have hdiff := pow_sub_pow_le (2 ^ B) (4 * τ + 1) hτ n
  have hA : (2 : ℝ≥0∞) ^ κ ≠ 0 := pow_ne_zero _ two_ne_zero
  have hA' : (2 : ℝ≥0∞) ^ κ ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have h0 : Fintype.card P * N = 0 := hn
    simp [h0, hn]
  have hD : ((2 ^ B) ^ n - (2 ^ B - (4 * τ + 1)) ^ n) * 2 ^ κ ≤ (2 ^ B) ^ n := by
    calc ((2 ^ B) ^ n - (2 ^ B - (4 * τ + 1)) ^ n) * 2 ^ κ
        ≤ n * (4 * τ + 1) * (2 ^ B) ^ (n - 1) * 2 ^ κ := Nat.mul_le_mul_right _ hdiff
      _ = n * (4 * τ + 1) * 2 ^ κ * (2 ^ B) ^ (n - 1) := by ring
      _ ≤ 2 ^ B * (2 ^ B) ^ (n - 1) := Nat.mul_le_mul_right _ hκ
      _ = (2 ^ B) ^ n := by rw [← pow_succ']; congr 1; omega
  refine ENNReal.div_le_of_le_mul ?_
  set D := (2 ^ B) ^ n - (2 ^ B - (4 * τ + 1)) ^ n
  calc ((D : ℕ) : ℝ≥0∞) = (D : ℝ≥0∞) * 2 ^ κ * (2 ^ κ)⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hA hA', mul_one]
    _ ≤ (((2 ^ B) ^ n : ℕ) : ℝ≥0∞) * (2 ^ κ)⁻¹ := by
        gcongr
        exact_mod_cast hD
    _ = (2 ^ κ)⁻¹ * (((2 ^ B) ^ n : ℕ) : ℝ≥0∞) := mul_comm _ _

/-! ### Boxes given by equations

For concrete parameters, the boxes are best kept opaque (`irreducible_def`): the elaborator may
`whnf` the type `v ∈ S` of a hypothesis, which enumerates `S` when it unfolds to a box over a large
index type. The following statements take the boxes as variables with their defining equations. -/

omit [NeZero Q] in
theorem nonempty_of_eq_famBig {S : Finset (P → Negacyclic (ZMod Q) N)} {B : ℕ} {hB : 2 ^ B ≤ Q}
    (h : S = famBig Q N P B hB) : S.Nonempty := by
  subst h; exact famBig_nonempty B hB

theorem mem_of_eq_famBall {S : Finset (P → Negacyclic (ZMod Q) N)} {r : ℕ}
    (h : S = famBall Q N P r) (v : P → Negacyclic (ZMod Q) N) :
    v ∈ S ↔ ∀ p, cnorm (v p) ≤ r := by
  subst h; exact mem_famBall

/-- **Coverage**: a shift within `s` maps `famBall r` into the big box when `r + s ≤ 2^{B−1} − 1`. -/
theorem add_mem_of_eq {Sm Bg : Finset (P → Negacyclic (ZMod Q) N)} {r s B : ℕ} {hB : 2 ^ B ≤ Q}
    (hSm : Sm = famBall Q N P r) (hBg : Bg = famBig Q N P B hB) (hB1 : 1 ≤ B)
    (hr : r + s ≤ 2 ^ (B - 1) - 1) {t : P → Negacyclic (ZMod Q) N} (ht : ∀ p, cnorm (t p) ≤ s) :
    ∀ x ∈ Sm, x + t ∈ Bg := by
  subst hSm hBg
  intro x hx
  exact famBall_subset_big B hB hB1 (famBall_mono hr (add_mem_famBall hx ht))

/-- A shift within `s` maps `famBall r'` into `famBall r` when `r' + s ≤ r`. -/
theorem sub_mem_of_eq {In Sm : Finset (P → Negacyclic (ZMod Q) N)} {r r' s : ℕ}
    (hIn : In = famBall Q N P r') (hSm : Sm = famBall Q N P r) (hr : r' + s ≤ r)
    {t : P → Negacyclic (ZMod Q) N} (ht : ∀ p, cnorm (t p) ≤ s) : ∀ x ∈ In, x - t ∈ Sm := by
  subst hIn hSm
  intro x hx
  exact famBall_mono hr (sub_mem_famBall hx ht)

theorem subset_of_eq {In Bg : Finset (P → Negacyclic (ZMod Q) N)} {r B : ℕ} {hB : 2 ^ B ≤ Q}
    (hIn : In = famBall Q N P r) (hBg : Bg = famBig Q N P B hB) (hB1 : 1 ≤ B)
    (hr : r ≤ 2 ^ (B - 1) - 1) : In ⊆ Bg := by
  subst hIn hBg
  exact (famBall_mono hr).trans (famBall_subset_big B hB hB1)

/-- **The abort probability**, for boxes given by equations. -/
theorem abort_of_eq {In Bg : Finset (P → Negacyclic (ZMod Q) N)} (B τ κ : ℕ) (hB : 2 ^ B ≤ Q)
    (hIn : In = famBall Q N P (2 ^ (B - 1) - 1 - 2 * τ)) (hBg : Bg = famBig Q N P B hB)
    (hB1 : 1 ≤ B) (hτ : 4 * τ + 1 ≤ 2 ^ B)
    (hκ : Fintype.card P * N * (4 * τ + 1) * 2 ^ κ ≤ 2 ^ B) :
    ((Bg.card - In.card : ℕ) : ℝ≥0∞) / Bg.card ≤ ((2 : ℝ≥0∞) ^ κ)⁻¹ := by
  subst hIn hBg
  exact famAbort_le B τ κ hB hB1 hτ hκ

end AdvancedEncryption.WE.RingBoxesCopy
