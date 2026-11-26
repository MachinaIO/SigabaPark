module

public import Definitions.Def_LatticeAttack_Reduction_Sieve_Movers
public import Definitions.Def_LatticeAttack_Reduction_Sieve_Estimates

set_option autoImplicit true

@[expose] public section

namespace SigabaNeo.Lattices.Sieve

open Finset Filter Real

theorem scanBudget_prescribed (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, (m:ℝ) ≤ K * log n ^ 3 →
      (scanBudget m (prescribedSize n) : ℝ) ≤
        (4/3 : ℝ)^n * exp ((2*K+8)*n/log n) := by
  filter_upwards [prescribedBudget K hK] with n hn
  intro m hm
  exact (Nat.cast_le.mpr (scanBudget_le _ _ _ fun i _ ↦ prescribedSize_le n i)).trans (hn m hm)

open scoped Classical in
theorem bankFailure_explicit {G : Type*} [AddCommGroup G] [DecidableEq G]
    {U T : Finset G} {V θ α β : ℝ} (sU : S1 U V θ) (s2 : S2 U T α β)
    (hV : 0 < V) (hα : 0 ≤ α) (hβ : 0 ≤ β) (M : ℕ) :
    let a := M*α/V
    let b := M*β/V
    let N := (U.card : ℝ)^M
    (((banks U M).filter fun C ↦ ¬GoodBank U T C (3*a) (b/4) (3*b)).card : ℝ) ≤
      U.card * (N * exp (-a/120)) +
      T.card * (N * exp (-b/120) + N * exp (-b/240)) := by
  classical
  dsimp only
  have hU : 0 < (U.card : ℝ) := by
    rw [sU.population]; exact mul_pos (by linarith [sU.lower]) hV
  have tails (P : G → Prop) [DecidablePred P] (x : ℝ) (hx : 0 ≤ x)
      (hl : x/3 ≤ (U.filter P).card) (hh : ((U.filter P).card : ℝ) ≤ 2*x) :=
    bankLensTails U P M (M*x/V) hU (by positivity)
      (by
        have h : ((U.filter P).card : ℝ) / U.card ≤ 203/100 * (x/V) := by
          apply (div_le_iff₀ hU).2
          rw [sU.population]
          field_simp
          nlinarith [mul_nonneg hx (show 0 ≤ θ+1/100 by linarith [sU.lower])]
        convert mul_le_mul_of_nonneg_left h (Nat.cast_nonneg M) using 1; ring)
      (by
        have h : 33/100 * (x/V) ≤ ((U.filter P).card : ℝ) / U.card := by
          apply (le_div_iff₀ hU).2
          rw [sU.population]
          field_simp
          nlinarith [mul_nonneg hx (show 0 ≤ 1/100-θ by linarith [sU.upper])]
        convert mul_le_mul_of_nonneg_left h (Nat.cast_nonneg M) using 1; ring)
  let A := (U.card:ℝ)^M * exp (-(M*α/V)/120)
  let B := (U.card:ℝ)^M * exp (-(M*β/V)/120) + (U.card:ℝ)^M * exp (-(M*β/V)/240)
  have bound := bankFailure (A := 3*(M*α/V)) (lo := (M*β/V)/4) (hi := 3*(M*β/V))
    s2 M ⌊A⌋₊ ⌊B⌋₊
    (fun u hu hh ↦ Nat.le_floor ((tails _ α hα (s2.mover u hu).1 hh).1))
    (fun d _ hd ↦ Nat.le_floor (by
      obtain ⟨up, low⟩ := tails (fun c ↦ d+c ∈ U) β hβ hd.1 hd.2
      let X := fun C : Fin M → G ↦ ((reps U C d).card : ℝ)
      let H := (banks U M).filter fun C ↦ 3*(M*β/V) < X C
      let L := (banks U M).filter fun C ↦ X C < (M*β/V)/4
      have sub : ((banks U M).filter fun C ↦ ¬((M*β/V)/4 ≤ X C ∧ X C ≤ 3*(M*β/V))) ⊆
          H ∪ L := by
        intro C hc
        obtain ⟨hc,h⟩ := mem_filter.mp hc
        by_cases hh : X C ≤ 3*(M*β/V)
        · exact mem_union_right _ (mem_filter.mpr ⟨hc, lt_of_not_ge fun hl ↦ h ⟨hl,hh⟩⟩)
        · exact mem_union_left _ (mem_filter.mpr ⟨hc, lt_of_not_ge hh⟩)
      have c := (card_le_card sub).trans (card_union_le H L)
      exact (Nat.cast_le.mpr c).trans (by rw [Nat.cast_add]; exact add_le_add up low)))
  apply (Nat.cast_le.mpr bound).trans
  push_cast
  exact add_le_add (mul_le_mul_of_nonneg_left (Nat.floor_le (by dsimp [A]; positivity)) (by positivity))
    (mul_le_mul_of_nonneg_left (Nat.floor_le (by dsimp [B]; positivity)) (by positivity))

/-- Fraction of bad banks from the pointwise Chernoff counts. -/
noncomputable def bankError (u t M : ℕ) (V α β : ℝ) : ℝ :=
  u * exp (-(M*α/V)/120) + t * (exp (-(M*β/V)/120) + exp (-(M*β/V)/240))

/-- Sufficient geometric size inequalities for dimension-only per-node errors. -/
theorem dimensionErrors (n u t M : ℕ) (V α β : ℝ)
    (movers : 1000 * ((n:ℝ)/log n) ≤ M)
    (moverLens : 240 * (log (1+u+2*(t:ℝ)) + n/log n) ≤ M*α/V)
    (repLens : 240 * (log (1+u+2*(t:ℝ)) + n/log n) ≤ M*β/V)
    (ha : 0 ≤ M*α/V) (hb : 0 ≤ M*β/V) :
    bankError u t M V α β ≤ exp (-((n:ℝ)/log n)) ∧
      exp (-(M:ℝ)/1000) ≤ exp (-((n:ℝ)/log n)) := by
  let H : ℝ := 1+u+2*(t:ℝ)
  have hH : 0 < H := by dsimp [H]; positivity
  let E := exp (-((n:ℝ)/log n))
  have bound (x : ℝ) (hx : 240*(log H+n/log n) ≤ x) :
      exp (-x/240) ≤ E/H := by
    change exp _ ≤ exp _ / H
    rw [← Real.exp_log hH, ← Real.exp_sub]
    exact exp_le_exp.mpr (by linarith)
  have h1 := bound _ moverLens
  have h2 := bound _ repLens
  have short (x : ℝ) (hx : 0 ≤ x) : exp (-x/120) ≤ exp (-x/240) :=
    exp_le_exp.mpr (by linarith)
  constructor
  · unfold bankError
    calc
      _ ≤ u*(E/H) + t*(E/H + E/H) := by
        exact add_le_add (mul_le_mul_of_nonneg_left ((short _ ha).trans h1) (by positivity))
          (mul_le_mul_of_nonneg_left (add_le_add ((short _ hb).trans h2) h2) (by positivity))
      _ ≤ H*(E/H) := by
        have h : 0 ≤ E/H := div_nonneg (exp_pos _).le hH.le
        dsimp only [H] at h ⊢; linarith
      _ = _ := by change H*(E/H) = E; field_simp
  · exact exp_le_exp.mpr (by linarith)

open scoped Classical in
theorem shellMerge_survival {G : Type*} [AddCommGroup G] [DecidableEq G]
    {U T : Finset G} {V W θ η α β : ℝ} (sU : S1 U V θ) (sT : S1 T W η)
    (s2 : S2 U T α β) (hV : 0 < V) (hα : 0 < α) (hβ : 0 < β)
    (scale : W*β = V*α) (M : ℕ) (hM : 0 < M) :
    let A := 3*(M*α/V)
    let lo := (M*β/V)/4
    let hi := 3*(M*β/V)
    let good := fun b : Fin M → U ↦ GoodBank U T (fun j ↦ (b j : G)) A lo hi
    let q := fun (b : Fin M → U) (u : U) (d : T) ↦ moverAtom U (fun j ↦ (b j : G)) A lo u d
    let r := fun b u ↦ 1-∑ d, q b u d
    let K : ℝ := Fintype.card (Fin M → U)
    (1-bankError U.card T.card M V α β)*(1-exp (-(M:ℝ)/1000)) ≤
      (∑ out : Fin (M/16) → T, ∑ b, if good b then
        wordSum M (fun us ↦ fixedHits (r b) (q b) M us (List.ofFn out)) else 0) / K^2 := by
  classical
  extract_lets A lo hi good q r K
  have hU : 0 < (U.card : ℝ) := by rw [sU.population]; exact mul_pos (by linarith [sU.lower]) hV
  have : Nonempty U := (card_pos.mp (by exact_mod_cast hU)).to_subtype
  have hlo : 0 < lo := by dsimp [lo]; positivity
  apply mergeSurvival
  · exact Real.exp_le_one_iff.mpr (by linarith [Nat.cast_nonneg (α := ℝ) M])
  · have bad := bankFailure_explicit sU s2 hV hα.le hβ.le M
    have eq : (univ.filter (fun b ↦ ¬good b)).card =
        ((banks U M).filter fun C ↦ ¬GoodBank U T C A lo hi).card := by
      apply card_bij (fun (b : Fin M → U) _ j ↦ (b j : G))
      · intro b hb
        exact mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun j ↦ (b j).property), (mem_filter.mp hb).2⟩
      · intro b _ c _ h
        exact funext fun j ↦ Subtype.ext (congrFun h j)
      · intro c hc
        exact ⟨fun j ↦ ⟨c j, Fintype.mem_piFinset.mp (mem_filter.mp hc).1 j⟩,
          mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hc).2⟩, rfl⟩
    have h := card_filter_add_card_filter_not (s := univ) good
    rw [eq, card_univ] at h
    have hh := congrArg (fun x : ℕ ↦ (x:ℝ)) h
    push_cast at hh
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe] at hh ⊢
    push_cast at hh ⊢
    dsimp [bankError]
    dsimp only [A, lo, hi] at hh
    linarith only [bad,hh]
  · intro b hb
    let p := (1+η)/(12*(1+θ))
    have ht : 0 < 1+θ := by linarith [sU.lower]
    have hp : 99/1212 ≤ p := by
      dsimp [p]; apply (le_div_iff₀ (by positivity)).2; linarith [sT.lower,sU.upper]
    have hp' : p ≤ 1 := by
      dsimp [p]; apply (div_le_iff₀ (by positivity)).2; linarith [sT.upper,sU.lower]
    have accept : ∑ d, ∑ u, q b u d = Fintype.card U * p := by
      have hd (d : T) : ∑ u, q b u d = lo/A := sum_moverAtom _ _ _ _ (by
        exact_mod_cast lt_of_lt_of_le hlo (hb.difference d d.property).1)
      simp only [hd, sum_const, card_univ, nsmul_eq_mul, Fintype.card_coe]
      rw [sT.population, sU.population]
      dsimp [lo,A,p]
      have hm : (0:ℝ) < M := by exact_mod_cast hM
      field_simp
      linear_combination 12*(1+η)*scale
    apply moverChernoff _ _ p hp hp' _ accept
    simp only [r, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one]
    rw [sum_comm, accept]
    ring

/-- S5 interface for the joint law of all leaf coordinates. -/
def IdealUniformLeaves {G : Type*} (U : Finset G) (leaves size : ℕ)
    (atom : (Fin leaves → Fin size → U) → ℝ) : Prop :=
  ∀ xs, atom xs = ((U.card : ℝ) ^ (leaves * size))⁻¹

theorem treeSurvival_uniformError (mass step : ℕ → ℝ) (e : ℝ) (he : 0 ≤ e)
    (initial : mass 0 = 1) (rec : ∀ i, mass (i+1) = mass i^2 * step i)
    (unit : ∀ i, 0 ≤ mass i ∧ mass i ≤ 1) (tail : ∀ i, 1-step i ≤ e) (m : ℕ) :
    1 - (2^m-1)*e ≤ mass m := by
  have eq : Nat.rec (motive := fun _ ↦ ℝ) 0 (fun _ a ↦ 2*a+e) m = (2^m-1)*e := by
    induction m with
    | zero => simp
    | succ m ih => simp only [ih, pow_succ]; ring
  have h := treeFailure mass step (fun _ ↦ e) initial rec unit (fun _ ↦ he) tail m
  linarith [eq]

#print axioms dimensionErrors
#print axioms shellMerge_survival
#print axioms bankFailure_explicit
#print axioms scanBudget_prescribed
#print axioms treeSurvival_uniformError

end SigabaNeo.Lattices.Sieve
