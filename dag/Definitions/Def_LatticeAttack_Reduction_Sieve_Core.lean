module

public import Mathlib

set_option autoImplicit true

@[expose] public section

/-!
# Finite shell sieve

Algorithmic identities from §§3.1–3.8 of `docs/research/provable_sieving.md`.
Shells are finite sets in an additive group. The bank counts indices, including repetitions.
S1 supplies shell populations. S2 and pointwise concentration hypotheses bound the bad-bank
count. The tree starts with ideal independent uniform leaves and tracks mass surviving all
good-bank and truncation tests. The one-merge lower-tail estimate is an explicit hypothesis.
Terminal recovery uses S3′ (§3.10) and S4. S5 and the §3.7 initialization sampler are outside
this finite model. The real-RAM cost counts exhaustive comparisons at prescribed list sizes.
The probability of the static hypotheses and the dimension-asymptotic estimates are open here.
-/

namespace SigabaNeo.Lattices.Sieve

open Finset
variable {G : Type*} [AddCommGroup G] [DecidableEq G] {M : ℕ}

def eligible (T : Finset G) (C : Fin M → G) (u : G) :=
  univ.filter fun j ↦ u - C j ∈ T

def reps (U : Finset G) (C : Fin M → G) (d : G) :=
  univ.filter fun j ↦ d + C j ∈ U

structure GoodBank (U T : Finset G) (C : Fin M → G) (A lo hi : ℝ) : Prop where
  mover : ∀ u ∈ U, ((eligible T C u).card : ℝ) ≤ A
  difference : ∀ d ∈ T, lo ≤ ((reps U C d).card : ℝ) ∧ ((reps U C d).card : ℝ) ≤ hi

/-- Sum the probabilities of the disjoint paths through each bank index representing d. -/
noncomputable def outputWeight (U T : Finset G) (C : Fin M → G) (A lo hi : ℝ) (d : G) : ℝ :=
  ∑ j ∈ reps U C d,
    let a : ℝ := (eligible T C (d + C j)).card
    let b : ℝ := (reps U C d).card
    if d ∈ T ∧ 0 < a ∧ a ≤ A ∧ lo ≤ b ∧ b ≤ hi then
      (1 / U.card) * (a / A) * (1 / a) * (lo / b)
    else 0

theorem exactCancellation {U T : Finset G} {C : Fin M → G} {A lo hi : ℝ}
    (good : GoodBank U T C A lo hi) (hlo : 0 < lo) {d : G} (hd : d ∈ T) :
    outputWeight U T C A lo hi d = lo / (A * U.card) := by
  have hb := good.difference d hd
  have hp := lt_of_lt_of_le hlo hb.1
  unfold outputWeight
  calc
    _ = ∑ _j ∈ reps U C d, lo / (A * U.card) / (reps U C d).card := by
      apply sum_congr rfl
      intro j hj
      have hu : d + C j ∈ U := (mem_filter.mp hj).2
      have hj' : j ∈ eligible T C (d + C j) := by simpa [eligible] using hd
      have ha : (0 : ℝ) < (eligible T C (d + C j)).card := by
        exact_mod_cast card_pos.mpr ⟨j, hj'⟩
      simp [hd, ha, good.mover _ hu, hb.1, hb.2, div_eq_mul_inv,
        mul_comm, mul_left_comm, mul_assoc, ne_of_gt ha]

    _ = _ := by simp [nsmul_eq_mul, ne_of_gt hp, div_eq_mul_inv, mul_comm, mul_left_comm]

structure S1 (U : Finset G) (V θ : ℝ) : Prop where
  population : (U.card : ℝ) = (1 + θ) * V
  lower : -(1/100 : ℝ) ≤ θ
  upper : θ ≤ 1/100

theorem acceptance {U T : Finset G} {C : Fin M → G} {V W α β θ η : ℝ}
    (sU : S1 U V θ) (sT : S1 T W η) (hV : 0 < V) (hα : 0 < α)
    (hβ : 0 < β) (hM : 0 < M) (scale : W * β = V * α)
    (good : GoodBank U T C (3*M*α/V) (M*β/(4*V)) (3*M*β/V)) :
    let p := ∑ d ∈ T, outputWeight U T C (3*M*α/V) (M*β/(4*V)) (3*M*β/V) d
    p = (1+η)/(12*(1+θ)) ∧ 99/1212 ≤ p := by
  have ht : 0 < 1+θ := by linarith [sU.lower]
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  dsimp only
  simp_rw [sum_congr rfl (fun d hd ↦ exactCancellation good (by positivity) hd)]
  rw [sum_const, nsmul_eq_mul, sU.population, sT.population]
  suffices he : (1+η)*W*(M*β/(4*V)/(3*M*α/V*((1+θ)*V))) = (1+η)/(12*(1+θ)) by
    rw [he]
    refine ⟨rfl, (le_div_iff₀ (by positivity)).2 ?_⟩
    linarith [sT.lower, sU.upper]
  field_simp
  linear_combination 12*(1+η)*scale

/-- The static, full-shell lens count windows of §3.1. -/
structure S2 (U T : Finset G) (α β : ℝ) : Prop where
  mover : ∀ u ∈ U,
    let a : ℝ := (U.filter fun c ↦ u-c ∈ T).card
    α/3 ≤ a ∧ a ≤ 2*α
  difference : ∀ d ∈ T,
    let b : ℝ := (U.filter fun c ↦ d+c ∈ U).card
    β/3 ≤ b ∧ b ≤ 2*β

/-- Under uniform sampling the probability of an event is its count divided by the
sample-space size. This union bound uses no independence between the bad events. -/
theorem failureCount {ι Ω : Type*} [DecidableEq Ω] (points : Finset ι)
    (bad : ι → Finset Ω) {k : ℕ} (tails : ∀ i ∈ points, (bad i).card ≤ k) :
    (points.biUnion bad).card ≤ points.card * k :=
  card_biUnion_le_card_mul _ _ _ tails

def banks (U : Finset G) (m : ℕ) : Finset (Fin m → G) := Fintype.piFinset fun _ ↦ U

/-- Uniform PMF on all indexed lists, including lists with repeated entries. -/
noncomputable def listPMF (U : Finset G) (hU : U.Nonempty) (m : ℕ) : PMF (Fin m → U) := by
  haveI : Nonempty U := hU.to_subtype
  exact PMF.ofFintype (fun _ ↦ (Fintype.card (Fin m → U) : ENNReal)⁻¹) (by
    simp only [sum_const, card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (by simp))

open scoped Classical in
/-- Count all bad banks by a union bound, given pointwise concentration estimates
for the two families of lens counts. Counts are out of |U|^M equiprobable banks. -/
theorem bankFailure {U T : Finset G} {α β A lo hi : ℝ} (s2 : S2 U T α β) (M ka kb : ℕ)
    (moverChernoff : ∀ u ∈ U, ((U.filter fun c ↦ u-c ∈ T).card : ℝ) ≤ 2*α →
      ((banks U M).filter fun C ↦ A < ((eligible T C u).card : ℝ)).card ≤ ka)
    (repChernoff : ∀ d ∈ T,
      (let b : ℝ := (U.filter fun c ↦ d+c ∈ U).card; β/3 ≤ b ∧ b ≤ 2*β) →
      ((banks U M).filter fun C ↦ ¬(lo ≤ ((reps U C d).card : ℝ) ∧
        ((reps U C d).card : ℝ) ≤ hi)).card ≤ kb) :
    ((banks U M).filter fun C ↦ ¬GoodBank U T C A lo hi).card ≤ U.card*ka + T.card*kb := by
  classical
  let a := fun u ↦ (banks U M).filter fun C ↦ A < ((eligible T C u).card : ℝ)
  let b := fun d ↦ (banks U M).filter fun C ↦ ¬(lo ≤ ((reps U C d).card : ℝ) ∧
    ((reps U C d).card : ℝ) ≤ hi)
  apply le_trans _ (add_le_add (failureCount U a fun u hu ↦ moverChernoff u hu (s2.mover u hu).2)
    (failureCount T b fun d hd ↦ repChernoff d hd (s2.difference d hd)))
  apply le_trans _ (card_union_le _ _)
  apply card_le_card
  intro C hC
  obtain ⟨hc, bad⟩ := mem_filter.mp hC
  by_contra h
  apply bad
  constructor
  · intro u hu
    by_contra! h'
    exact h (mem_union_left _ (mem_biUnion.mpr ⟨u, hu, mem_filter.mpr ⟨hc,h'⟩⟩))
  · intro d hd
    by_contra h'
    exact h (mem_union_right _ (mem_biUnion.mpr ⟨d, hd, mem_filter.mpr ⟨hc,h'⟩⟩))

/-- Atom weight for the first k successes matching a prescribed list. A rejection consumes
one attempt and leaves the desired list intact. A matching success consumes its head. -/
noncomputable def firstHits {D : Type*} (reject : ℝ) (atom : D → ℝ) : ℕ → List D → ℝ
  | _, [] => 1
  | 0, _ :: _ => 0
  | n+1, d :: ds =>
    reject * firstHits reject atom n (d :: ds) + atom d * firstHits reject atom n ds

theorem firstHits_uniform {D : Type*} {atom : D → ℝ} {w : ℝ}
    (constant : ∀ d, atom d = w) (reject : ℝ) (n : ℕ) (xs ys : List D)
    (lengths : xs.length = ys.length) :
    firstHits reject atom n xs = firstHits reject atom n ys := by
  induction n generalizing xs ys with
  | zero => cases xs <;> cases ys <;> simp_all [firstHits]
  | succ n ih =>
    cases xs <;> cases ys <;> simp_all [firstHits]
    congr 1 <;> congr 1 <;> apply ih <;> simp_all

theorem goodBank_firstHits {U T : Finset G} {C : Fin M → G} {A lo hi : ℝ}
    (good : GoodBank U T C A lo hi) (hlo : 0 < lo) (n : ℕ) (xs ys : List T)
    (lengths : xs.length = ys.length) :
    let atom := fun d : T ↦ outputWeight U T C A lo hi d
    let reject := 1 - ∑ d ∈ T, outputWeight U T C A lo hi d
    firstHits reject atom n xs = firstHits reject atom n ys :=
  firstHits_uniform (fun d ↦ exactCancellation good hlo d.property) _ n xs ys lengths

/-- Sum over indexed words, exposing the first coordinate to the trial kernel. -/
noncomputable def wordSum {D : Type*} [Fintype D] :
    (n : ℕ) → ((Fin n → D) → ℝ) → ℝ
  | 0, f => f Fin.elim0
  | n+1, f => ∑ u, wordSum n fun tail ↦ f (Fin.cons u tail)

private theorem wordSum_linear {D : Type*} [Fintype D] (n : ℕ)
    (f g : (Fin n → D) → ℝ) (a b : ℝ) :
    wordSum n (fun x ↦ a*f x + b*g x) = a*wordSum n f + b*wordSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [wordSum, ih, sum_add_distrib, mul_sum]

/-- First successes for a fixed mover list, before averaging its coordinates. -/
noncomputable def fixedHits {U D : Type*} (r : U → ℝ) (q : U → D → ℝ) :
    (n : ℕ) → (Fin n → U) → List D → ℝ
  | _, _, [] => 1
  | 0, _, _ :: _ => 0
  | n+1, us, d :: ds =>
    r (us 0) * fixedHits r q n (Fin.tail us) (d :: ds) +
    q (us 0) d * fixedHits r q n (Fin.tail us) ds

theorem sumFixedHits_uniform {U D : Type*} [Fintype U] (r : U → ℝ) (q : U → D → ℝ)
    (same : ∀ d e, ∑ u, q u d = ∑ u, q u e) (n : ℕ) (xs ys : List D)
    (lengths : xs.length = ys.length) :
    wordSum n (fun us ↦ fixedHits r q n us xs) =
      wordSum n (fun us ↦ fixedHits r q n us ys) := by
  induction n generalizing xs ys with
  | zero => cases xs <;> cases ys <;> simp_all [wordSum, fixedHits]
  | succ n ih =>
    cases xs with
    | nil => cases ys <;> simp_all
    | cons x xs =>
      cases ys with
      | nil => simp at lengths
      | cons y ys =>
        have ht : xs.length = ys.length := by simpa using lengths
        simp only [wordSum, fixedHits, Fin.cons_zero, Fin.tail_cons, wordSum_linear,
          sum_add_distrib, ← sum_mul]
        rw [ih _ _ lengths, ih _ _ ht, same x y]

/-- Binary-tree law restricted to good banks and enough successes. Subtrees use
independent coins, hence their atom weights multiply. The good-bank transition
is given the actual ordered mover list. -/
noncomputable def treeWeight (D : ℕ → Type*) [∀ i, Fintype (D i)] (m : ℕ → ℕ)
    (good : ∀ i, (Fin (m i) → D i) → Prop)
    (r : ∀ i, (Fin (m i) → D i) → D i → ℝ)
    (q : ∀ i, (Fin (m i) → D i) → D i → D (i+1) → ℝ)
    (i : ℕ) (out : Fin (m i) → D i) : ℝ := by
  classical
  exact match i with
  | 0 => (Fintype.card (D 0) : ℝ)⁻¹ ^ m 0
  | i+1 => ∑ bank, if good i bank then
      treeWeight D m good r q i bank * wordSum (m i) (fun us ↦
        treeWeight D m good r q i us *
          fixedHits (r i bank) (q i bank) (m i) us (List.ofFn out)) else 0

theorem treeWeight_uniform (D : ℕ → Type*) [∀ i, Fintype (D i)] (m : ℕ → ℕ)
    (good : ∀ i, (Fin (m i) → D i) → Prop)
    (r : ∀ i, (Fin (m i) → D i) → D i → ℝ)
    (q : ∀ i, (Fin (m i) → D i) → D i → D (i+1) → ℝ)
    (cancel : ∀ i bank, good i bank → ∀ d e, ∑ u, q i bank u d = ∑ u, q i bank u e)
    (i : ℕ) (xs ys : Fin (m i) → D i) :
    treeWeight D m good r q i xs = treeWeight D m good r q i ys := by
  classical
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [treeWeight]
    apply sum_congr rfl
    intro bank _
    split_ifs with hg
    · congr 1
      simp_rw [ih _ bank]
      have factor (f : (Fin (m i) → D i) → ℝ) (a : ℝ) :
          wordSum _ (fun u ↦ a*f u) = a * wordSum _ f := by
        simpa using wordSum_linear (m i) f f a 0
      rw [factor, factor, sumFixedHits_uniform _ _ (cancel i bank hg) _ (List.ofFn xs) (List.ofFn ys) (by simp)]
    · rfl

/-- At a good bank, the first rejection and the index choice cancel for every
eligible index. Sum the remaining path weights for a fixed mover. -/
noncomputable def moverAtom (U : Finset G) (C : Fin M → G) (A lo : ℝ) (u d : G) :=
  ∑ j ∈ reps U C d, if u = d + C j then lo / A / (reps U C d).card else 0

theorem sum_moverAtom {U : Finset G} (C : Fin M → G) (A lo : ℝ) (d : G)
    (h : 0 < (reps U C d).card) : ∑ u : U, moverAtom U C A lo u d = lo/A := by
  unfold moverAtom
  rw [sum_comm]
  calc
    _ = ∑ _j ∈ reps U C d, lo/A/(reps U C d).card := by
      apply sum_congr rfl
      intro j hj
      let x : U := ⟨d + C j, (mem_filter.mp hj).2⟩
      have eq (u : U) : ((u : G) = d + C j) ↔ u = x := by
        change ((u : G) = (x : G)) ↔ u = x
        exact Subtype.ext_iff.symm
      simp_rw [eq]
      simp
    _ = _ := by
      have hn : ((reps U C d).card : ℝ) ≠ 0 := by exact_mod_cast h.ne'
      simp [nsmul_eq_mul, div_eq_mul_inv, mul_left_comm, hn]

/-- Each row of the good-bank kernel is a subprobability distribution. -/
theorem moverAtom_subprob {U T : Finset G} {C : Fin M → G} {A lo hi : ℝ}
    (good : GoodBank U T C A lo hi) (hA : 0 < A) (hl : 0 < lo) {u : G} (hu : u ∈ U) :
    (∀ d ∈ T, 0 ≤ moverAtom U C A lo u d) ∧ (∑ d ∈ T, moverAtom U C A lo u d) ≤ 1 := by
  constructor
  · intro d _
    unfold moverAtom
    apply sum_nonneg
    intro j _
    split_ifs <;> positivity
  · have per (d : G) (hd : d ∈ T) :
        moverAtom U C A lo u d ≤ ∑ j : Fin M, if d = u-C j then 1/A else 0 := by
      unfold moverAtom
      rw [reps, sum_filter]
      apply sum_le_sum
      intro j _
      by_cases e : u = d+C j
      · have ed : d = u-C j := by rw [e]; simp
        have hb := (good.difference d hd).1
        have hp := lt_of_lt_of_le hl hb
        have hj : d + C j ∈ U := e ▸ hu
        simp only [ite_eq_left hj, ite_eq_left e, ite_eq_left ed]
        apply (div_le_iff₀ hp).2
        exact (div_le_div_iff_of_pos_right hA).2 hb |> fun h ↦ by
          simpa [div_eq_mul_inv, mul_comm] using h
      · have ed : d ≠ u-C j := fun h ↦ e (by rw [h]; simp)
        simp [e, ed]
    apply le_trans (sum_le_sum per)
    rw [sum_comm]
    simp only [sum_ite_eq', ← sum_filter]
    simpa [eligible, sum_filter, nsmul_eq_mul, ← div_eq_mul_inv] using
      (div_le_one hA).2 (good.mover u hu)

noncomputable abbrev shellAtom (U : ℕ → Finset G) (m : ℕ → ℕ) (A lo : ℕ → ℝ)
    (i : ℕ) (bank : Fin (m i) → U i) (u : U i) (d : U (i+1)) : ℝ :=
  moverAtom (U i) (fun j ↦ bank j) (A i) (lo i) u d

/-- The live output atoms at every level have equal mass. Upon normalization
at positive survival probability this is the uniform law on ordered lists. -/
theorem shellTree_uniform (U : ℕ → Finset G) (m : ℕ → ℕ) (A lo hi : ℕ → ℝ)
    (positive : ∀ i, 0 < lo i) (i : ℕ) (xs ys : Fin (m i) → U i) :
    let good := fun k (b : Fin (m k) → U k) ↦
      GoodBank (U k) (U (k+1)) (fun j ↦ (b j : G)) (A k) (lo k) (hi k)
    let q := shellAtom U m A lo
    let law := treeWeight (fun k ↦ ↥(U k)) m good (fun k b u ↦ 1 - ∑ d, q k b u d) q
    law i xs = law i ys := by
  apply treeWeight_uniform
  intro k b hg d e
  have hp (x : U (k+1)) : 0 < (reps (U k) (fun j ↦ (b j : G)) x).card := by
    exact_mod_cast lt_of_lt_of_le (positive k) (hg.difference x x.property).1
  exact (sum_moverAtom _ _ _ _ (hp d)).trans (sum_moverAtom _ _ _ _ (hp e)).symm

/-- Total surviving mass obeys a scalar recurrence. Here step is the mass of a
single merge from two fresh uniform input lists, including both abort conditions. -/
theorem survival_recurrence (D : ℕ → Type*) [∀ i, Fintype (D i)] (m : ℕ → ℕ)
    (good : ∀ i, (Fin (m i) → D i) → Prop) [∀ i b, Decidable (good i b)]
    (r : ∀ i, (Fin (m i) → D i) → D i → ℝ)
    (q : ∀ i, (Fin (m i) → D i) → D i → D (i+1) → ℝ)
    (cancel : ∀ i bank, good i bank → ∀ d e, ∑ u, q i bank u d = ∑ u, q i bank u e)
    (i : ℕ) (ref : Fin (m i) → D i) :
    let law := treeWeight D m good r q
    let K : ℝ := Fintype.card (Fin (m i) → D i)
    let step := (∑ out : Fin (m (i+1)) → D (i+1), ∑ bank, if good i bank then
      wordSum (m i) (fun us ↦ fixedHits (r i bank) (q i bank) (m i) us (List.ofFn out))
      else 0) / K^2
    ∑ out, law (i+1) out = (∑ us, law i us)^2 * step := by
  classical
  dsimp only
  have : Nonempty (Fin (m i) → D i) := ⟨ref⟩
  have hk : (Fintype.card (Fin (m i) → D i) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  let w := treeWeight D m good r q i ref
  have hw (x) : treeWeight D m good r q i x = w :=
    treeWeight_uniform _ _ _ _ _ cancel i x ref
  have hf (f : (Fin (m i) → D i) → ℝ) :
      wordSum _ (fun u ↦ w*f u) = w * wordSum _ f := by
    simpa using wordSum_linear (m i) f f w 0
  simp only [treeWeight, hw, hf, sum_const, card_univ, nsmul_eq_mul]
  field_simp
  simp only [mul_sum]
  apply sum_congr rfl
  intro out _
  apply sum_congr rfl
  intro bank _
  split_ifs <;> ring

/-- Convert pointwise lower-tail estimates for the number of accepted movers at
good banks into a lower bound on the normalized one-merge survival mass. -/
theorem mergeSurvival {U D : Type*} [Fintype U] [Fintype D] (m k : ℕ)
    [Nonempty (Fin m → U)] (good : (Fin m → U) → Prop) [DecidablePred good]
    (r : (Fin m → U) → U → ℝ) (q : (Fin m → U) → U → D → ℝ)
    (δ ε : ℝ) (hε : ε ≤ 1)
    (bankTail : ((univ.filter good).card : ℝ) ≥
      (1-δ) * Fintype.card (Fin m → U))
    (moverChernoff : ∀ b, good b → (1-ε) * Fintype.card (Fin m → U) ≤
      ∑ out : Fin k → D, wordSum m fun us ↦ fixedHits (r b) (q b) m us (List.ofFn out)) :
    let K : ℝ := Fintype.card (Fin m → U)
    (1-δ)*(1-ε) ≤ (∑ out : Fin k → D, ∑ b, if good b then
      wordSum m (fun us ↦ fixedHits (r b) (q b) m us (List.ofFn out)) else 0) / K^2 := by
  dsimp only
  have hp : (0 : ℝ) < Fintype.card (Fin m → U) := by exact_mod_cast Fintype.card_pos
  apply (le_div_iff₀ (sq_pos_of_pos hp)).2
  simp_rw [← sum_filter]
  rw [sum_comm]
  calc
    _ ≤ ∑ _b ∈ univ.filter good, (1-ε) * (Fintype.card (Fin m → U) : ℝ) := by
      simp only [sum_const, nsmul_eq_mul]
      have h := mul_le_mul_of_nonneg_right bankTail
        (show 0 ≤ (1-ε)*(Fintype.card (Fin m → U) : ℝ) by exact mul_nonneg (sub_nonneg.mpr hε) hp.le)
      linarith only [h]
    _ ≤ _ := sum_le_sum fun b hb ↦ moverChernoff b (mem_filter.mp hb).2

/-- Propagate finite one-node errors through the binary tree. -/
theorem treeFailure (mass step err : ℕ → ℝ) (initial : mass 0 = 1)
    (recurrence : ∀ i, mass (i+1) = mass i ^ 2 * step i)
    (unit : ∀ i, 0 ≤ mass i ∧ mass i ≤ 1) (herr : ∀ i, 0 ≤ err i) (tails : ∀ i, 1-step i ≤ err i) (n : ℕ) :
    1-mass n ≤ Nat.rec 0 (fun i acc ↦ 2*acc + err i) n := by
  induction n with
  | zero => simp [initial]
  | succ i ih =>
    rw [recurrence]
    change _ ≤ 2 * Nat.rec (motive := fun _ ↦ ℝ) 0 (fun j acc ↦ 2*acc + err j) i + err i
    have hu := unit i
    by_cases h : step i ≤ 1
    · have hs : mass i ^ 2 ≤ 1 := by nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hu.2)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr h), tails i,
        sq_nonneg (1-mass i)]
    · -- This branch also follows from the subprobability bound on a merge.
      have := herr i
      nlinarith [sq_nonneg (1-mass i), mul_nonneg (sq_nonneg (mass i))
        (show 0 ≤ step i - 1 by linarith)]

/-- Lists missing a fixed point draw every coordinate from the erased shell. -/
def missingLists (U : Finset G) (m : ℕ) (d : G) : Finset (Fin m → G) :=
  Fintype.piFinset fun _ ↦ U.erase d

omit [AddCommGroup G] in
theorem missingLists_count (U : Finset G) (m : ℕ) :
    (U.biUnion (missingLists U m)).card ≤ U.card * (U.card-1)^m := by
  apply failureCount
  intro d hd
  simp [missingLists, card_erase_of_mem hd]

/-- Pairs tested at one merge (two bank scans per mover) and at the terminal scan. -/
def scanBudget (m : ℕ) (size : ℕ → ℕ) :=
  (∑ i ∈ range m, 2^(m-i) * (2*size i*size i)) + size m ^ 2

theorem scanBudget_le (m B : ℕ) (size : ℕ → ℕ) (bound : ∀ i ≤ m, size i ≤ B) :
    scanBudget m size ≤ m * (2^m * (2*B*B)) + B^2 := by
  unfold scanBudget
  apply Nat.add_le_add _ (Nat.pow_le_pow_left (bound m le_rfl) _)
  calc
    _ ≤ ∑ _i ∈ range m, 2^m * (2*B*B) := by
      apply sum_le_sum
      intro i hi
      have h := bound i (Nat.le_of_lt (mem_range.mp hi))
      gcongr
      exact Nat.sub_le _ _
    _ = _ := by simp

def candidates (X Y : Finset G) := (X ×ˢ Y).image fun p ↦ p.1 - p.2

def S3prime (U : Finset G) (short : Set G) : Prop :=
  ∀ v ∈ short, ∃ x ∈ U, ∃ y ∈ U, x - y = v

theorem terminalRecovery {U X Y : Finset G} {short : Set G} {v : G}
    (s3 : S3prime U short) (s4 : v ∈ short) (left : U ⊆ X) (right : U ⊆ Y) :
    v ∈ candidates X Y := by
  obtain ⟨x, hx, y, hy, h⟩ := s3 v s4
  exact mem_image.mpr ⟨(x,y), mem_product.mpr ⟨left hx, right hy⟩, h⟩

theorem shortestInScan {U X Y : Finset G} {short : Set G} {v : G}
    (score : G → ℝ) (cut : ℝ) (s3 : S3prime U short) (s4 : v ∈ short)
    (hv : v ≠ 0) (hcut : score v ≤ cut) (left : U ⊆ X) (right : U ⊆ Y)
    (minimal : ∀ z ∈ candidates X Y, z ≠ 0 → score v ≤ score z) :
    let hits := (candidates X Y).filter fun z ↦ z ≠ 0 ∧ score z ≤ cut
    hits.Nonempty ∧ ∀ z ∈ hits, (∀ y ∈ hits, score z ≤ score y) → score z = score v := by
  have hit : v ∈ (candidates X Y).filter (fun z ↦ z ≠ 0 ∧ score z ≤ cut) := mem_filter.mpr ⟨terminalRecovery s3 s4 left right, hv, hcut⟩
  exact ⟨⟨v, hit⟩, fun z hz least ↦ le_antisymm (least v hit)
    (minimal z (mem_filter.mp hz).1 (mem_filter.mp hz).2.1)⟩

/-- Number of ordered pairs of terminal lists on which the scan misses a specified
short vector. Divide by |U|^(2m) for the conditional failure probability. -/
theorem terminalFailure_count {U : Finset G} {short : Set G} {v : G}
    (s3 : S3prime U short) (s4 : v ∈ short) (m : ℕ) :
    let B := banks U m
    let points := fun x : Fin m → G ↦ univ.image x
    (((B ×ˢ B).filter fun p ↦ v ∉ candidates (points p.1) (points p.2)).card)
      ≤ 2 * (U.card*(U.card-1)^m) * U.card^m := by
  classical
  let bad := U.biUnion (missingLists U m)
  let B := banks U m
  have miss {x : Fin m → G} (hx : x ∈ B) (ok : x ∉ bad) : U ⊆ univ.image x := by
    intro d hd
    by_contra h
    apply ok
    apply mem_biUnion.mpr ⟨d, hd, ?_⟩
    apply Fintype.mem_piFinset.mpr
    intro j
    exact mem_erase.mpr ⟨fun eq ↦ h (mem_image.mpr ⟨j, mem_univ j, eq⟩),
      Fintype.mem_piFinset.mp hx j⟩
  have incl : ((B ×ˢ B).filter fun p ↦
      v ∉ candidates (univ.image p.1) (univ.image p.2)) ⊆
      (bad ×ˢ B) ∪ (B ×ˢ bad) := by
    intro p hp
    obtain ⟨pair, fail⟩ := mem_filter.mp hp
    obtain ⟨hx, hy⟩ := mem_product.mp pair
    by_cases xbad : p.1 ∈ bad
    · exact mem_union_left _ (mem_product.mpr ⟨xbad,hy⟩)
    by_cases ybad : p.2 ∈ bad
    · exact mem_union_right _ (mem_product.mpr ⟨hx,ybad⟩)
    exact (fail (terminalRecovery s3 s4 (miss hx xbad) (miss hy ybad))).elim
  have est := (card_le_card incl).trans (card_union_le _ _)
  simp only [card_product] at est
  have cb : B.card = U.card^m := by simp [B, banks]
  rw [cb] at est
  have hbad : bad.card ≤ U.card*(U.card-1)^m := missingLists_count U m
  exact est.trans (by nlinarith [Nat.mul_le_mul_right (U.card^m) hbad])

/-- The two terminal subtrees have independent coins. Sum their product weights
over pairs for which exhaustive search finds the specified shortest vector. -/
theorem treeScan_success (U : ℕ → Finset G) (m : ℕ → ℕ) (A lo hi : ℕ → ℝ)
    (positive : ∀ k, 0 < lo k) (i : ℕ) (ref : Fin (m i) → U i)
    {short : Set G} {v : G} (s3 : S3prime (U i) short) (s4 : v ∈ short) :
    let good := fun k (b : Fin (m k) → U k) ↦
      GoodBank (U k) (U (k+1)) (fun j ↦ (b j : G)) (A k) (lo k) (hi k)
    let q := shellAtom U m A lo
    let law := treeWeight (fun k ↦ ↥(U k)) m good (fun k b u ↦ 1 - ∑ d, q k b u d) q
    let B := banks (U i) (m i)
    let hits := (B ×ˢ B).filter fun p ↦
      v ∈ candidates (univ.image p.1) (univ.image p.2)
    let lift := fun (x : Fin (m i) → G) ↦
      if h : x ∈ B then fun j ↦ (⟨x j, Fintype.mem_piFinset.mp h j⟩ : U i) else ref
    let K := (U i).card
    (K^(m i)*K^(m i) - 2*(K*(K-1)^m i)*K^m i : ℕ) * (law i ref)^2 ≤
      ∑ p ∈ hits, law i (lift p.1) * law i (lift p.2) := by
  classical
  dsimp only
  simp_rw [shellTree_uniform U m A lo hi positive i _ ref]
  rw [sum_const, nsmul_eq_mul, sq]
  apply mul_le_mul_of_nonneg_right _ (mul_self_nonneg _)
  exact_mod_cast (by
    have h := terminalFailure_count s3 s4 (m i)
    have eq := card_filter_add_card_filter_not (s := banks (U i) (m i) ×ˢ banks (U i) (m i))
      (fun p ↦ v ∈ candidates (univ.image p.1) (univ.image p.2))
    simp only [card_product, banks, Fintype.card_piFinset, prod_const, card_univ,
      Fintype.card_fin] at eq
    dsimp only at h
    unfold banks at h ⊢
    omega : _ ≤ _)

section Lattice

variable {E : Type*} [NormedAddCommGroup E] [DecidableEq E]

/-- The shortest nonzero length is attained below the specified radius (§3.1). -/
def S4 (L : AddSubgroup E) (r₀ : ℝ) : Prop :=
  ∃ v ∈ L, v ≠ 0 ∧ ‖v‖ ≤ r₀ ∧ ∀ z ∈ L, z ≠ 0 → ‖v‖ ≤ ‖z‖

/-- On terminal coverage the filtered scan has a minimum, and every minimizer is a
shortest nonzero lattice vector. The additive subgroup can be a Euclidean lattice. -/
theorem latticeScan_shortest (L : AddSubgroup E) (U X Y : Finset E) (r₀ cut : ℝ)
    (s3 : S3prime U {v | v ∈ L ∧ v ≠ 0 ∧ ‖v‖ ≤ r₀}) (s4 : S4 L r₀) (radii : r₀ ≤ cut)
    (left : U ⊆ X) (right : U ⊆ Y) (lx : ∀ x ∈ X, x ∈ L) (ly : ∀ y ∈ Y, y ∈ L) :
    let hits := (candidates X Y).filter fun z ↦ z ≠ 0 ∧ ‖z‖ ≤ cut
    (∃ z ∈ hits, ∀ y ∈ hits, ‖z‖ ≤ ‖y‖) ∧
      ∀ z ∈ hits, (∀ y ∈ hits, ‖z‖ ≤ ‖y‖) →
        z ∈ L ∧ z ≠ 0 ∧ ∀ y ∈ L, y ≠ 0 → ‖z‖ ≤ ‖y‖ := by
  obtain ⟨v, hvL, hv, hr, least⟩ := s4
  have closed : ∀ z ∈ candidates X Y, z ∈ L := by
    intro z hz
    obtain ⟨⟨x,y⟩, hp, rfl⟩ := mem_image.mp hz
    exact L.sub_mem (lx x (mem_product.mp hp).1) (ly y (mem_product.mp hp).2)
  obtain ⟨hne, hmin⟩ := shortestInScan norm cut s3 (v := v) ⟨hvL,hv,hr⟩ hv
    (hr.trans radii) left right (fun z hz ↦ least z (closed z hz))
  refine ⟨exists_min_image _ norm hne, ?_⟩
  intro z hz hm
  exact ⟨closed z (mem_filter.mp hz).1, (mem_filter.mp hz).2.1,
    fun y hy hn ↦ (hmin z hz hm).le.trans (least y hy hn)⟩

end Lattice

#print axioms mergeSurvival
#print axioms treeFailure
#print axioms survival_recurrence
#print axioms latticeScan_shortest
#print axioms moverAtom_subprob
#print axioms treeScan_success
#print axioms terminalFailure_count
#print axioms shellTree_uniform
#print axioms listPMF
#print axioms bankFailure
#print axioms scanBudget_le
#print axioms shortestInScan
#print axioms exactCancellation
#print axioms acceptance
#print axioms goodBank_firstHits
#print axioms missingLists_count
#print axioms terminalRecovery

end SigabaNeo.Lattices.Sieve
