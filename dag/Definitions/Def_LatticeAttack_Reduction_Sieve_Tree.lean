module

public import Definitions.Def_LatticeAttack_Reduction_Sieve_Bounds

set_option autoImplicit true

@[expose] public section

namespace SigabaNeo.Lattices.Sieve

open Finset Real

/-- A positive extension of the lower threshold to unused levels past the finite tree. -/
noncomputable def lowerThreshold (x : ℝ) := if 0 < x then x else 1

private theorem lowerThreshold_pos (x : ℝ) : 0 < lowerThreshold x := by
  unfold lowerThreshold
  split <;> positivity

/-- The shell tree uses disjoint coins and the ideal product law at level zero. -/
noncomputable def prescribedLaw {G : Type*} [AddCommGroup G] [DecidableEq G]
    (n : ℕ) (U : ℕ → Finset G) (V α β : ℕ → ℝ) : (i : ℕ) → (Fin (prescribedSize n i) → U i) → ℝ := by
  classical
  let M := prescribedSize n
  let A := fun i ↦ 3*(M i*α i/V i)
  let lo := fun i ↦ lowerThreshold ((M i*β i/V i)/4)
  let hi := fun i ↦ 3*(M i*β i/V i)
  let good := fun i (b : Fin (M i) → U i) ↦
    GoodBank (U i) (U (i+1)) (fun j ↦ (b j : G)) (A i) (lo i) (hi i)
  let q := shellAtom U M A lo
  exact treeWeight (fun i ↦ ↥(U i)) M good (fun i b u ↦ 1 - ∑ d, q i b u d) q

/-- With ideal uniform initialization the supplied joint atom equals the product
of exactly the leaf weights used by the tree recurrence. -/
theorem idealUniformLeaves_factor {G : Type*} [AddCommGroup G] [DecidableEq G]
    (n leaves : ℕ) (U : ℕ → Finset G) (V α β : ℕ → ℝ)
    (atom : (Fin leaves → Fin (prescribedSize n 0) → U 0) → ℝ)
    (ideal : IdealUniformLeaves (U 0) leaves (prescribedSize n 0) atom) (xs) :
    atom xs = ∏ j, prescribedLaw n U V α β 0 (xs j) := by
  rw [ideal xs]
  simp [prescribedLaw, treeWeight, pow_mul, mul_comm, inv_pow]
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

theorem prescribedTree_survival {G : Type*} [AddCommGroup G] [DecidableEq G]
    (n depth : ℕ) (U : ℕ → Finset G) (V θ α β : ℕ → ℝ)
    (pop : ∀ i ≤ depth, S1 (U i) (V i) (θ i))
    (degs : ∀ i < depth, S2 (U i) (U (i+1)) (α i) (β i))
    (vol : ∀ i ≤ depth, 0 < V i)
    (pos : ∀ i < depth, 0 < α i ∧ 0 < β i ∧ 0 < prescribedSize n i)
    (scale : ∀ i < depth, V (i+1)*β i = V i*α i)
    (e : ℝ) (he' : e ≤ 1)
    (errors : ∀ i < depth,
      bankError (U i).card (U (i+1)).card (prescribedSize n i) (V i) (α i) (β i) +
        exp (-(prescribedSize n i : ℝ)/1000) ≤ e) :
    1 - (2^depth-1)*e ≤ ∑ xs, prescribedLaw n U V α β depth xs := by
  classical
  let M := prescribedSize n
  let A := fun i ↦ 3*(M i*α i/V i)
  let lo := fun i ↦ lowerThreshold ((M i*β i/V i)/4)
  let hi := fun i ↦ 3*(M i*β i/V i)
  let good := fun i (b : Fin (M i) → U i) ↦
    GoodBank (U i) (U (i+1)) (fun j ↦ (b j : G)) (A i) (lo i) (hi i)
  let q := shellAtom U M A lo
  let r := fun i b u ↦ 1 - ∑ d, q i b u d
  let mass := fun i ↦ ∑ xs, prescribedLaw n U V α β i xs
  have nonempty (i) (h : i ≤ depth) : Nonempty (U i) := by
    apply Finset.Nonempty.to_subtype
    apply card_pos.mp
    have : 0 < ((U i).card : ℝ) := by
      rw [(pop i h).population]; exact mul_pos (by linarith [(pop i h).lower]) (vol i h)
    exact_mod_cast this
  have cancel i b (hg : good i b) (d f : U (i+1)) : ∑ u, q i b u d = ∑ u, q i b u f := by
    have hl : 0 < lo i := lowerThreshold_pos _
    have h (x : U (i+1)) : 0 < (reps (U i) (fun j ↦ (b j : G)) x).card := by
        exact_mod_cast lt_of_lt_of_le hl (hg.difference x x.property).1
    exact (sum_moverAtom _ _ _ _ (h d)).trans (sum_moverAtom _ _ _ _ (h f)).symm
  have chain (i : ℕ) (h : i ≤ depth) : 1-(2^i-1)*e ≤ mass i := by
    induction i with
    | zero =>
      have := nonempty 0 h
      have hc : (0:ℝ) < (U 0).card := by exact_mod_cast (card_pos.mpr (show (U 0).Nonempty from ⟨_, (nonempty 0 h).some.property⟩))
      simp [mass, prescribedLaw, treeWeight, hc.ne', nsmul_eq_mul]
    | succ i ih =>
      have hi' : i < depth := h
      have prev := ih hi'.le
      have := nonempty i hi'.le
      let ref : Fin (M i) → U i := fun _ ↦ Classical.choice inferInstance
      have hrec := survival_recurrence (fun i ↦ ↥(U i)) M good r q cancel i ref
      have step := shellMerge_survival (pop i hi'.le) (pop _ h) (degs i hi') (vol i hi'.le)
        (pos i hi').1 (pos i hi').2.1 (scale i hi') (M i) (pos i hi').2.2
      let δ := bankError (U i).card (U (i+1)).card (M i) (V i) (α i) (β i)
      let ε := exp (-(M i : ℝ)/1000)
      have hd : 0 ≤ δ := by dsimp [δ,bankError]; positivity
      have hε : 0 ≤ ε := (exp_pos _).le
      have herr : δ+ε ≤ e := errors i hi'
      have lower : 1-e ≤ (1-δ)*(1-ε) := by nlinarith [mul_nonneg hd hε]
      change 1 - _ ≤ ∑ xs, treeWeight (fun i ↦ ↥(U i)) M good r q (i+1) xs
      rw [hrec]
      have hv := vol i hi'.le
      have hb := (pos i hi').2.1
      have hm : 0 < M i := (pos i hi').2.2
      have hl : lo i = (M i*β i/V i)/4 := ite_eq_left (by positivity)
      dsimp only [good, r, q, shellAtom]
      have hq (b : Fin (M i) → U i) : shellAtom U M A lo i b = fun (u : U i) (d : U (i+1)) ↦
          moverAtom (U i) (fun j ↦ (b j : G)) (A i) ((M i*β i/V i)/4) u d := by
        funext u d; simp [shellAtom, hl]
      simp only [hl, hq]
      apply le_trans _ (mul_le_mul_of_nonneg_left (lower.trans step) (sq_nonneg _))
      change _ ≤ mass i ^ 2 * (1-e)
      have sq : 1-2*((2^i-1)*e) ≤ mass i^2 := by nlinarith [sq_nonneg (1-mass i)]
      have hpow : (1:ℝ) ≤ 2^i := one_le_pow₀ (by norm_num)
      rw [pow_succ]
      nlinarith [mul_le_mul_of_nonneg_right sq (sub_nonneg.mpr he'),
        mul_nonneg (sub_nonneg.mpr hpow) (sq_nonneg e)]
  exact chain depth le_rfl

/-- Lower bound for the mass of successful terminal scans, using the two independent trees.
The tree kernel starts with ideal uniform leaves. -/
theorem prescribedScan_success {G : Type*} [AddCommGroup G] [DecidableEq G]
    (n depth : ℕ) (U : ℕ → Finset G) (V θ α β : ℕ → ℝ)
    (pop : ∀ i ≤ depth, S1 (U i) (V i) (θ i))
    (degs : ∀ i < depth, S2 (U i) (U (i+1)) (α i) (β i))
    (vol : ∀ i ≤ depth, 0 < V i)
    (pos : ∀ i < depth, 0 < α i ∧ 0 < β i ∧ 0 < prescribedSize n i)
    (scale : ∀ i < depth, V (i+1)*β i = V i*α i)
    (e : ℝ) (he : e ≤ 1) (budget : 0 ≤ 1-(2^depth-1)*e)
    (errors : ∀ i < depth, bankError (U i).card (U (i+1)).card
      (prescribedSize n i) (V i) (α i) (β i) + exp (-(prescribedSize n i : ℝ)/1000) ≤ e)
    {short : Set G} {v : G} (covers : S3prime (U depth) short) (hv : v ∈ short)
    (ref : Fin (prescribedSize n depth) → U depth) :
    let S := U depth
    let M := prescribedSize n depth
    let K := S.card^M
    let B := banks S M
    let hits := (B ×ˢ B).filter fun p ↦ v ∈ candidates (univ.image p.1) (univ.image p.2)
    let lift := fun x : Fin M → G ↦ if h : x ∈ B then
      fun j ↦ (⟨x j, Fintype.mem_piFinset.mp h j⟩ : S) else ref
    let law := prescribedLaw n U V α β depth
    ((K*K - 2*(S.card*(S.card-1)^M)*K : ℕ) : ℝ) * ((1-(2^depth-1)*e)/K)^2 ≤
      ∑ p ∈ hits, law (lift p.1) * law (lift p.2) := by
  classical
  extract_lets S M K B hits lift law
  let sizes := prescribedSize n
  let A := fun i ↦ 3*(sizes i*α i/V i)
  let lo := fun i ↦ lowerThreshold ((sizes i*β i/V i)/4)
  let hi := fun i ↦ 3*(sizes i*β i/V i)
  have positive (i) : 0 < lo i := lowerThreshold_pos _
  have surv := prescribedTree_survival n depth U V θ α β pop degs vol pos scale e he errors
  change _ ≤ ∑ x, law x at surv
  have uniform (x) : law x = law ref :=
    shellTree_uniform U sizes A lo hi positive depth x ref
  simp only [uniform, sum_const, card_univ, nsmul_eq_mul, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_coe] at surv
  have hs : 0 < (S.card : ℝ) := by
    rw [(pop depth le_rfl).population]
    exact mul_pos (by linarith [(pop depth le_rfl).lower]) (vol depth le_rfl)
  have hk : 0 < (K:ℝ) := by dsimp [K]; push_cast; positivity
  have hw : (1-(2^depth-1)*e)/K ≤ law ref := (div_le_iff₀ hk).2 (by
    rw [mul_comm (law ref)]; exact surv)
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (div_nonneg budget hk.le) hw 2)
    (Nat.cast_nonneg _)).trans (treeScan_success U sizes A lo hi positive depth ref covers hv)

/-- Simplify the finite terminal success bound to two subtree errors and the coupon tail. -/
theorem scanFailure_additive (u m : ℕ) (hu : 0 < u) (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    let K := u^m
    1-2*t-2*u*exp (-(m:ℝ)/u) ≤
      ((K*K-2*(u*(u-1)^m)*K : ℕ) : ℝ) * ((1-t)/K)^2 := by
  dsimp only
  have hp : 0 < (u:ℝ) := by exact_mod_cast hu
  have hpow : 0 < (u:ℝ)^m := by positivity
  have ratio : ((u:ℝ)-1)^m / (u:ℝ)^m ≤ exp (-(m:ℝ)/u) := by
    rw [← div_pow]
    have h1 : ((u:ℝ)-1)/u ≤ exp (-1/(u:ℝ)) := by
      have hh := Real.add_one_le_exp (-1/(u:ℝ))
      rw [sub_div, div_self hp.ne']
      linarith [show -(1:ℝ)/u = -(1/u) by ring]
    have h0 : 0 ≤ (u:ℝ)-1 := by exact sub_nonneg.mpr (by exact_mod_cast hu)
    apply (pow_le_pow_left₀ (div_nonneg h0 hp.le) h1 m).trans_eq
    rw [← Real.exp_nat_mul]
    congr 1; ring
  have trunc (a b : ℕ) : (a:ℝ)-b ≤ ((a-b:ℕ):ℝ) := by
    by_cases h : b ≤ a
    · rw [Nat.cast_sub h]
    · have hh : (a:ℝ) ≤ b := by exact_mod_cast le_of_not_ge h
      linarith [Nat.cast_nonneg (α := ℝ) (a-b)]
  have bound := trunc (u^m*u^m) (2*(u*(u-1)^m)*u^m)
  have hsub : ((u-1:ℕ):ℝ) = u-1 := by rw [Nat.cast_sub hu]; norm_num
  push_cast at bound ⊢
  rw [hsub] at bound
  apply le_trans _ (mul_le_mul_of_nonneg_right bound (sq_nonneg _))
  let d := 2*(u:ℝ)*(((u:ℝ)-1)^m/(u:ℝ)^m)
  have hd : 0 ≤ d := by
    dsimp [d]
    have : 0 ≤ (u:ℝ)-1 := sub_nonneg.mpr (by exact_mod_cast hu)
    positivity
  have hd' : d ≤ 2*u*exp (-(m:ℝ)/u) :=
    mul_le_mul_of_nonneg_left ratio (by positivity)
  calc
    _ ≤ (1-d)*(1-t)^2 := by
      nlinarith [mul_nonneg hd (show 0 ≤ 1-(1-t)^2 by nlinarith [mul_nonneg ht (sub_nonneg.mpr ht')]),
        sq_nonneg t]
    _ = _ := by dsimp [d]; field_simp

/-- Dimension-only success bound, conditional on the two lens-volume margins and
terminal occupancy. The population and degree bounds are those of S1 and S2. -/
theorem prescribedScan_dimension {G : Type*} [AddCommGroup G] [DecidableEq G]
    (n depth : ℕ) (U : ℕ → Finset G) (V θ α β : ℕ → ℝ)
    (pop : ∀ i ≤ depth, S1 (U i) (V i) (θ i))
    (degs : ∀ i < depth, S2 (U i) (U (i+1)) (α i) (β i))
    (vol : ∀ i ≤ depth, 0 < V i)
    (pos : ∀ i < depth, 0 < α i ∧ 0 < β i ∧ 0 < prescribedSize n i)
    (scale : ∀ i < depth, V (i+1)*β i = V i*α i)
    (x : ℝ) (hx : x = n/log n) (hx0 : 0 ≤ x)
    (overhead : 4*(2:ℝ)^depth+2 ≤ exp (x/2))
    (sizes : ∀ i < depth, 1000*x ≤ prescribedSize n i)
    (lens : ∀ i < depth, let m : ℝ := prescribedSize n i
      let H : ℝ := 1+(U i).card+2*((U (i+1)).card:ℝ)
      240*(log H+x) ≤ m*α i/V i ∧ 240*(log H+x) ≤ m*β i/V i)
    (terminal : log (U depth).card + x ≤ prescribedSize n depth / ((U depth).card:ℝ))
    {short : Set G} {v : G} (covers : S3prime (U depth) short) (hv : v ∈ short)
    (ref : Fin (prescribedSize n depth) → U depth) :
    let S := U depth
    let M := prescribedSize n depth
    let B := banks S M
    let hits := (B ×ˢ B).filter fun p ↦ v ∈ candidates (univ.image p.1) (univ.image p.2)
    let lift := fun x : Fin M → G ↦ if h : x ∈ B then
      fun j ↦ (⟨x j, Fintype.mem_piFinset.mp h j⟩ : S) else ref
    let law := prescribedLaw n U V α β depth
    1-exp (-x/2) ≤ ∑ p ∈ hits, law (lift p.1) * law (lift p.2) := by
  classical
  let E := exp (-x)
  have hE : 0 ≤ E := (exp_pos _).le
  have total : (4*(2:ℝ)^depth+2)*E ≤ exp (-x/2) := by
    apply (mul_le_mul_of_nonneg_right overhead hE).trans_eq
    rw [show E = exp (-x) by rfl, ← exp_add]; congr 1; ring
  have h1 : exp (-x/2) ≤ 1 := exp_le_one_iff.mpr (by linarith)
  have hp : (1:ℝ) ≤ 2^depth := one_le_pow₀ (by norm_num)
  have prod := mul_nonneg (sub_nonneg.mpr hp) hE
  have he : 2*E ≤ 1 := by nlinarith
  have budget : 0 ≤ 1-(2^depth-1)*(2*E) := by nlinarith
  have hs : 0 < ((U depth).card : ℝ) := by
    rw [(pop depth le_rfl).population]
    exact mul_pos (by linarith [(pop depth le_rfl).lower]) (vol depth le_rfl)
  have term : (U depth).card * exp (-(prescribedSize n depth:ℝ)/(U depth).card) ≤ E := by
    rw [← exp_log hs, ← exp_add, exp_log hs]
    apply exp_le_exp.mpr
    rw [neg_div]; linarith
  have err i hi := dimensionErrors n (U i).card (U (i+1)).card (prescribedSize n i)
    (V i) (α i) (β i) (hx ▸ sizes i hi) (hx ▸ (lens i hi).1) (hx ▸ (lens i hi).2)
    (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (pos i hi).1.le) (vol i hi.le).le)
    (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (pos i hi).2.1.le) (vol i hi.le).le)
  have scan := prescribedScan_success n depth U V θ α β pop degs vol pos scale (2*E) he budget
    (fun i hi ↦ by
      have h := add_le_add (err i hi).1 (err i hi).2
      simpa [E, hx, two_mul] using h) covers hv ref
  apply le_trans _ ((scanFailure_additive _ _ (by exact_mod_cast hs)
    ((2^depth-1)*(2*E)) (by positivity) (by linarith)).trans scan)
  nlinarith only [term, total, hE]

#print axioms prescribedScan_dimension
#print axioms scanFailure_additive
#print axioms idealUniformLeaves_factor
#print axioms prescribedScan_success
#print axioms prescribedTree_survival

end SigabaNeo.Lattices.Sieve
