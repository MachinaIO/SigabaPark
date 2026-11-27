import Definitions.Def_LatticeAttack_Research_Wall1_TerminalProjection
import Definitions.Def_LatticeAttack_Research_Wall1_DualMinimumExit

set_option autoImplicit true

/-! # The conditional first moment for a single append (Part 183) -/

noncomputable section

namespace SigabaNeo.Wall1.TerminalProjection

open Submodule WithLp Finset DecoupledDecoder
open scoped Classical BigOperators

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The full marked preimage is K, and its image modulo M is the group of possible marks. -/
abbrev Marks (M K : Submodule ℤ V) := ↥(K.map M.mkQ)

private theorem finite_candidates (K : Submodule ℤ V) [DiscreteTopology K] [IsZLattice ℝ K]
    (R : ℝ) : {w : WindowSpace V | w ∈ appendWindow K 0 ∧ 0 < w.snd ∧ ‖w‖ ≤ R}.Finite := by
  let L := appendWindow K 0
  obtain ⟨hL, _⟩ := appendWindow_lattice K 0
  have : DiscreteTopology L.toAddSubgroup := hL
  have hf : (Metric.closedBall (0 : WindowSpace V) R ∩ (L : Set _)).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete Metric.isBounded_closedBall
      L.toAddSubgroup.isClosed_of_discreteTopology
  exact hf.subset fun _ h ↦ ⟨mem_closedBall_zero_iff.mpr h.2.2, h.1⟩

/-- The actual finite set of points in the positive-height half of the closed ball in K × ℤ. -/
def candidates (K : Submodule ℤ V) [DiscreteTopology K] [IsZLattice ℝ K] (R : ℝ) :
    Finset (WindowSpace V) := (finite_candidates K R).toFinset

@[simp] theorem mem_candidates {K : Submodule ℤ V} [DiscreteTopology K] [IsZLattice ℝ K]
    {R : ℝ} {w : WindowSpace V} : w ∈ candidates K R ↔
      w ∈ appendWindow K 0 ∧ 0 < w.snd ∧ ‖w‖ ≤ R := Set.Finite.mem_toFinset _

omit [FiniteDimensional ℝ V] in
private theorem window_le {M K : Submodule ℤ V} (hMK : M ≤ K) {u : V} (hu : u ∈ K) :
    appendWindow M u ≤ appendWindow K 0 := by
  intro w hw
  obtain ⟨j, hj⟩ := integral_height hw
  have he := (mem_append_at_height M u w j hj).1 hw
  have hm : w.fst - j • u ∈ M := (Submodule.Quotient.eq M).1
    (he.trans (map_zsmul M.mkQ j u).symm)
  have hk := K.add_mem (hMK hm) (K.smul_mem j hu)
  apply (mem_append_at_height K 0 w j hj).2
  simpa using (Submodule.Quotient.mk_eq_zero K).2 (by simpa using hk : w.fst ∈ K)

private theorem bezout_inverse {G : Type*} [AddCommGroup G] {j q : ℕ} (hc : j.Coprime q)
    (hq : ∀ g : G, q • g = 0) (g : G) : j.gcdA q • (j • g) = g := by
  have e := j.gcd_eq_gcd_ab q
  rw [hc.gcd_eq_one] at e
  have h := congrArg (fun a : ℤ ↦ a • g) e
  simpa [add_smul, mul_smul, smul_comm (q : ℤ), smul_comm (j : ℤ), hq] using h.symm

variable (M K : Submodule ℤ V) (u : Marks M K → V)
variable [DiscreteTopology K] [IsZLattice ℝ K]

/-- For each integer candidate there is exactly one possible mark. The equality tested is
`[w.fst] = j • [u]` in the incoming quotient, where j is the height. -/
theorem unique_mark {q : ℕ} (hq : q.Prime) (htors : ∀ a ∈ K, q • a ∈ M)
    (hu : ∀ g, M.mkQ (u g) = g.val) {R : ℝ} (hR : R < q)
    {w : WindowSpace V} (hw : w ∈ candidates K R) :
    ∃! g : Marks M K, w ∈ appendWindow M (u g) := by
  obtain ⟨hK, hp, hlen⟩ := mem_candidates.mp hw
  obtain ⟨k, hk⟩ := integral_height hK
  have hkpos : 0 < k := by exact_mod_cast (hk ▸ hp : (0 : ℝ) < k)
  lift k to ℕ using hkpos.le with j
  have hj : 0 < j := by exact_mod_cast hkpos
  have hr : (j : ℝ) ≤ R := by
    have hs := (WithLp.norm_snd_le V w).trans hlen
    simpa [Real.norm_eq_abs, abs_of_pos hp, hk] using hs
  have hc := (Nat.coprime_of_lt_prime hj.ne' (show j < q by exact_mod_cast hr.trans_lt hR) hq).symm
  have hf : w.fst ∈ K := (Submodule.Quotient.mk_eq_zero K).mp
    (by simpa using (mem_append_at_height K 0 w (j : ℤ) hk).mp hK)
  let b : Marks M K := ⟨M.mkQ w.fst, ⟨_, hf, rfl⟩⟩
  have ht (g : Marks M K) : q • g = 0 := by
    obtain ⟨a, ha, he⟩ := g.property
    apply Subtype.ext
    change q • g.val = 0
    rw [← he, ← map_nsmul]
    exact (Submodule.Quotient.mk_eq_zero M).2 (htors a ha)
  have test (g : Marks M K) : w ∈ appendWindow M (u g) ↔ b = j • g := by
    rw [mem_append_at_height M (u g) w (j : ℤ) hk, hu, natCast_zsmul]
    exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩
  refine ⟨j.gcdA q • b, (test _).2 ?_, ?_⟩
  · rw [smul_comm j, bezout_inverse hc ht]
  · intro g hg
    rw [(test g).mp hg, bezout_inverse hc ht]

/-- Uniform mass over a finite sample space. -/
def mass {G : Type*} [Fintype G] (P : G → Prop) : ℝ :=
  ((univ.filter P).card : ℝ) / Fintype.card G

private theorem mass_mono {G : Type*} [Fintype G] {P Q : G → Prop} (h : ∀ g, P g → Q g) :
    mass P ≤ mass Q := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast card_le_card (monotone_filter_right univ fun g _ ↦ h g)

variable [Fintype (Marks M K)]

/-- Double counting gives equality for the number of hits, including multiple hits on one draw. -/
theorem positive_first_moment {q : ℕ} (hq : q.Prime) (htors : ∀ a ∈ K, q • a ∈ M)
    (hu : ∀ g, M.mkQ (u g) = g.val) {R : ℝ} (hR : R < q) :
    (∑ g : Marks M K, (((candidates K R).filter fun w ↦ w ∈ appendWindow M (u g)).card : ℝ)) /
        Fintype.card (Marks M K) = (candidates K R).card / (Fintype.card (Marks M K) : ℝ) := by
  congr 1
  simp_rw [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [sum_comm]
  have hsingle (w) (hw : w ∈ candidates K R) :
      (∑ g : Marks M K, if w ∈ appendWindow M (u g) then (1 : ℝ) else 0) = 1 := by
    obtain ⟨g, hg, hg'⟩ := unique_mark M K u hq htors hu hR hw
    rw [Finset.sum_eq_single g]
    · simp [hg]
    · intro b _ hne
      have hb : w ∉ appendWindow M (u b) := fun h ↦ hne (hg' b h)
      simp [hb]
    · simp
  simpa using Finset.sum_congr rfl hsingle

/-- Existence costs at most the first moment. The denominator is the size of the mark group. -/
theorem positive_probability {q : ℕ} (hq : q.Prime) (htors : ∀ a ∈ K, q • a ∈ M)
    (hMK : M ≤ K) (huK : ∀ g, u g ∈ K) (hu : ∀ g, M.mkQ (u g) = g.val)
    {R : ℝ} (hR : R < q) :
    mass (fun g ↦ PositiveHit M (u g) R) ≤
      (candidates K R).card / (Fintype.card (Marks M K) : ℝ) := by
  rw [← positive_first_moment M K u hq htors hu hR]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro g _
  split_ifs with h
  · obtain ⟨w, hw, hp, hr⟩ := h
    have hn : ((candidates K R).filter fun w ↦ w ∈ appendWindow M (u g)).Nonempty :=
      ⟨w, mem_filter.mpr ⟨mem_candidates.mpr ⟨window_le hMK (huK g) hw, hp, hr⟩, hw⟩⟩
    exact_mod_cast Finset.card_pos.mpr hn
  · simp

/-- Conditional comparison at every fixed incoming lattice and designated old minimum. -/
theorem discrepancy_probability {q : ℕ} (hq : q.Prime) (htors : ∀ a ∈ K, q • a ∈ M)
    (hMK : M ≤ K) (huK : ∀ g, u g ∈ K) (hu : ∀ g, M.mkQ (u g) = g.val)
    {x : V} (hx : IsShortest M x) (v : Marks M K → WindowSpace V)
    (hv : ∀ g, IsShortest (appendWindow M (u g)) (v g))
    (htie : ∀ g, HorizontalAgreement x (v g)) {r : ℝ} (hR : 2*r / Real.sqrt 3 < q) :
    mass (fun g ↦ ¬ (ShortProjection (appendWindow M (u g)) (v g) r ↔ ShortProjection M x r)) ≤
      (candidates K (2*r / Real.sqrt 3)).card / (Fintype.card (Marks M K) : ℝ) :=
  (mass_mono fun g h ↦ discrepancy hx (hv g) (htie g) h).trans
    (positive_probability M K u hq htors hMK huK hu hR)

/-- The same bound for uniform raw columns mapped onto the mark group. -/
theorem uniform_column_mass {C G : Type*} [AddGroup C] [Fintype C] [AddGroup G] [Fintype G]
    (φ : C →+ G) (hs : Function.Surjective φ) (P : G → Prop) :
    mass (fun c ↦ P (φ c)) = mass P := by
  have hf (g : G) : (univ.filter fun c ↦ φ c = g).card = Nat.card φ.ker :=
    FreshDisplacement.fiber_card φ g (hs g)
  have count (s : Finset G) :
      (univ.filter fun c ↦ φ c ∈ s).card = s.card * Nat.card φ.ker := by
    rw [← Finset.sum_card_fiberwise_eq_card_filter univ s φ]
    simp [hf]
  have he := count (univ.filter P)
  have ht := count univ
  simp only [mem_filter, mem_univ, true_and] at he
  simp only [mem_univ, Finset.filter_true, card_univ] at ht
  unfold mass
  apply (div_eq_div_iff (by positivity) (by positivity)).2
  exact_mod_cast (by rw [he, ht]; ring :
    (univ.filter fun c ↦ P (φ c)).card * Fintype.card G = (univ.filter P).card * Fintype.card C)

/-- Fresh-column bound for any lift of the raw column. A surjective homomorphism to the
mark group gives uniform marks, and changing representatives preserves the whole window. -/
theorem fresh_column_probability {C : Type*} [AddGroup C] [Fintype C]
    (φ : C →+ Marks M K) (hs : Function.Surjective φ)
    (raw : C → V) (hraw : ∀ c, M.mkQ (raw c) = (φ c).val)
    {q : ℕ} (hq : q.Prime) (htors : ∀ a ∈ K, q • a ∈ M)
    (hMK : M ≤ K) (huK : ∀ g, u g ∈ K) (hu : ∀ g, M.mkQ (u g) = g.val)
    {R : ℝ} (hR : R < q) :
    mass (fun c ↦ PositiveHit M (raw c) R) ≤
      (candidates K R).card / (Fintype.card (Marks M K) : ℝ) := by
  have incl (c : C) : appendWindow M (raw c) ≤ appendWindow M (u (φ c)) := by
    intro w hw
    obtain ⟨j, hj⟩ := integral_height hw
    apply (mem_append_at_height M _ w j hj).2
    rw [hu, ← hraw]
    exact (mem_append_at_height M _ w j hj).1 hw
  calc
    _ ≤ mass (fun c ↦ PositiveHit M (u (φ c)) R) := by
      apply mass_mono
      rintro c ⟨w, hw, hp, hr⟩
      exact ⟨w, incl c hw, hp, hr⟩
    _ = _ := uniform_column_mass φ hs (fun g ↦ PositiveHit M (u g) R)
    _ ≤ _ := positive_probability M K u hq htors hMK huK hu hR

/-- Average the conditional discrepancy over any finite law of incoming histories. The old
event is measured before the fresh draw. The mark space may vary with the history. -/
theorem terminal_probability {H : Type*} [Fintype H] {G : H → Type*} [∀ h, Fintype (G h)]
    [∀ h, Nonempty (G h)] (p : H → ℝ) (hp : ∀ h, 0 ≤ p h) (hs : ∑ h, p h = 1)
    (F : (h : H) → G h → Prop) (J : H → Prop) (ε : ℝ)
    (hε : ∀ h, mass (fun g ↦ ¬ (F h g ↔ J h)) ≤ ε) :
    ∑ h, p h * mass (F h) ≤ (∑ h, if J h then p h else 0) + ε := by
  calc
    _ ≤ ∑ h, p h * ((if J h then 1 else 0) + ε) := by
      apply sum_le_sum
      intro h _
      apply mul_le_mul_of_nonneg_left _ (hp h)
      by_cases hj : J h
      · have hone : mass (F h) ≤ 1 := by
          apply (div_le_iff₀ (by exact_mod_cast Fintype.card_pos (α := G h))).2
          simpa using (show (((univ.filter (F h)).card : ℝ) ≤ Fintype.card (G h)) by
            exact_mod_cast (card_filter_le univ (F h)).trans_eq card_univ)
        have he : 0 ≤ ε := le_trans (by unfold mass; positivity) (hε h)
        simpa [hj] using hone.trans (le_add_of_nonneg_right he)
      · simpa [hj] using hε h
    _ = _ := by simp [mul_add, sum_add_distrib, ← sum_mul, hs, mul_ite]


/-- The geometric comparison averaged over histories, with a uniform bound on the physical
candidate-to-mark ratio. Each history may have a different incoming lattice and mark group. -/
theorem terminal_probability_of_candidates {H : Type*} [Fintype H] (p : H → ℝ)
    (hp : ∀ h, 0 ≤ p h) (hs : ∑ h, p h = 1) (M K : H → Submodule ℤ V)
    [∀ h, DiscreteTopology (K h)] [∀ h, IsZLattice ℝ (K h)] [∀ h, Fintype (Marks (M h) (K h))]
    (u : (h : H) → Marks (M h) (K h) → V) (x : H → V)
    (v : (h : H) → Marks (M h) (K h) → WindowSpace V)
    {q : ℕ} (hq : q.Prime) (htors : ∀ h a, a ∈ K h → q • a ∈ M h) (hMK : ∀ h, M h ≤ K h)
    (huK : ∀ h g, u h g ∈ K h) (hu : ∀ h g, (M h).mkQ (u h g) = g.val)
    (hx : ∀ h, IsShortest (M h) (x h)) (hv : ∀ h g, IsShortest (appendWindow (M h) (u h g)) (v h g))
    (htie : ∀ h g, HorizontalAgreement (x h) (v h g)) {r ε : ℝ} (hR : 2*r / Real.sqrt 3 < q)
    (hc : ∀ h, (candidates (K h) (2*r / Real.sqrt 3)).card /
      (Fintype.card (Marks (M h) (K h)) : ℝ) ≤ ε) :
    ∑ h, p h * mass (fun g ↦ ShortProjection (appendWindow (M h) (u h g)) (v h g) r) ≤
      (∑ h, if ShortProjection (M h) (x h) r then p h else 0) + ε :=
  terminal_probability p hp hs _ _ ε fun h ↦
    (discrepancy_probability _ _ _ hq (htors h) (hMK h) (huK h) (hu h) (hx h) (v h)
      (hv h) (htie h) hR).trans (hc h)

/-- Final rational enclosure at width 506 and radius 26. The analytic majorant, the
upper bound on its prefactor, and the lower bound on its scale are hypotheses. -/
theorem discrepancy_506 (htors : ∀ a ∈ K, 3329 • a ∈ M) (hMK : M ≤ K)
    (huK : ∀ g, u g ∈ K) (hu : ∀ g, M.mkQ (u g) = g.val)
    {x : V} (hx : IsShortest M x) (v : Marks M K → WindowSpace V)
    (hv : ∀ g, IsShortest (appendWindow M (u g)) (v g)) (htie : ∀ g, HorizontalAgreement x (v g))
    (hwidth : Module.finrank ℝ V + 1 = 506) {C g : ℝ}
    (hC : C ≤ 1.422743743939) (hg : 31.9457118986 ≤ g)
    (hcount : (candidates K (52 / Real.sqrt 3)).card / (Fintype.card (Marks M K) : ℝ) ≤
      C * ((52 / Real.sqrt 3) / g) ^ (Module.finrank ℝ V + 1)) :
    mass (fun b ↦ ¬ (ShortProjection (appendWindow M (u b)) (v b) 26 ↔ ShortProjection M x 26))
      < 3.210 / 10^14 := by
  have hl : (1.7320508 : ℝ) ≤ Real.sqrt 3 := (Real.le_sqrt (by norm_num) (by norm_num)).2
    (by norm_num)
  have hr : 52 / Real.sqrt 3 ≤ (30.022215 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).2
    linarith
  have ht := discrepancy_probability M K u (q := 3329) (by norm_num) htors hMK huK hu hx v hv htie
    (r := 26) (by norm_num only [Nat.cast_ofNat, show (2:ℝ)*26=52 by norm_num]; linarith)
  norm_num only [show (2:ℝ)*26=52 by norm_num] at ht
  have hg0 : 0 < g := by linarith
  have ratio : (52 / Real.sqrt 3) / g ≤ 0.9397886 := by
    apply (div_le_iff₀ hg0).2
    linarith
  rw [hwidth] at hcount
  calc
    _ ≤ _ := ht.trans hcount
    _ ≤ 1.422743743939 * (0.9397886 : ℝ)^506 :=
      mul_le_mul hC (pow_le_pow_left₀ (by positivity) ratio 506) (by positivity) (by norm_num)
    _ < _ := by
      norm_num
      have h : (1422743743939 / 1000000000000 : ℚ) * (4698943 / 5000000)^506 <
          321 / 10000000000000000 := by decide +kernel
      simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using
        (Rat.cast_lt (K := ℝ)).2 h

end SigabaNeo.Wall1.TerminalProjection

#print axioms SigabaNeo.Wall1.TerminalProjection.unique_mark
#print axioms SigabaNeo.Wall1.TerminalProjection.positive_first_moment
#print axioms SigabaNeo.Wall1.TerminalProjection.positive_probability
#print axioms SigabaNeo.Wall1.TerminalProjection.discrepancy_probability
#print axioms SigabaNeo.Wall1.TerminalProjection.uniform_column_mass
#print axioms SigabaNeo.Wall1.TerminalProjection.fresh_column_probability
#print axioms SigabaNeo.Wall1.TerminalProjection.terminal_probability
#print axioms SigabaNeo.Wall1.TerminalProjection.terminal_probability_of_candidates
#print axioms SigabaNeo.Wall1.TerminalProjection.discrepancy_506
