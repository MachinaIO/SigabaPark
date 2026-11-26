import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true

/-! # Finite occupancy certificates for coset voids

These inequalities retain the number of representatives in each coset. They do not
assert a distributional bound for the selected BKZ history. The final theorem transfers
an explicitly supplied certificate-failure count to the history exit count.
-/

noncomputable section
namespace SigabaNeo.Wall1.CosetOccupancy
open Finset
open scoped Classical

/-- Number of labels receiving no representative. -/
def emptyCount {α : Type*} [Fintype α] (n : α → ℕ) : ℕ :=
  (univ.filter fun c ↦ n c = 0).card

/-- Ordered pairs of representatives belonging to the same label, including the diagonal. -/
def collisionCount {α : Type*} [Fintype α] (n : α → ℕ) : ℕ := ∑ c, n c ^ 2

/-- Cauchy--Schwarz after restricting to the occupied labels. -/
theorem support_bound {α : Type*} [Fintype α] (n : α → ℕ) :
    (∑ c, n c) ^ 2 ≤ (Fintype.card α - emptyCount n) * collisionCount n := by
  let occupied : Finset α := univ.filter fun c ↦ n c ≠ 0
  have hsum : ∑ c ∈ occupied, n c = ∑ c, n c := by
    apply sum_subset (filter_subset _ _)
    intro c hc hn
    simp only [mem_filter, mem_univ, true_and, not_not] at hn
    exact hn
  have hsq : ∑ c ∈ occupied, n c ^ 2 = ∑ c, n c ^ 2 := by
    apply sum_subset (filter_subset _ _)
    intro c hc hn
    simp only [mem_filter, mem_univ, true_and, not_not] at hn
    simp [hn]
  have hcard : occupied.card = Fintype.card α - emptyCount n := by
    have h := card_filter_add_card_filter_not (s := (univ : Finset α))
      (p := fun c ↦ n c = 0)
    change emptyCount n + occupied.card = Fintype.card α at h
    omega
  have h := sq_sum_le_card_mul_sum_sq (s := occupied) (f := n)
  simpa only [hsum, hsq, hcard, Nat.cast_id, collisionCount] using h

/-- An integer certificate for an arbitrary rational void ceiling `a / b`.
The nonempty representative condition is essential. -/
theorem void_ceiling {α : Type*} [Fintype α] (n : α → ℕ)
    {a b : ℕ} (hab : a ≤ b) (hN : 0 < ∑ c, n c)
    (hcert : (b-a) * Fintype.card α * collisionCount n ≤ b * (∑ c, n c)^2) :
    b * emptyCount n ≤ a * Fintype.card α := by
  have hs := support_bound n
  have he : emptyCount n ≤ Fintype.card α := card_filter_le _ _
  have hJ : 0 < collisionCount n := by
    by_contra h
    have hz : collisionCount n = 0 := by omega
    rw [hz, mul_zero] at hs
    nlinarith
  have hm := Nat.mul_le_mul_left b hs
  have hd : Fintype.card α - emptyCount n + emptyCount n = Fintype.card α :=
    Nat.sub_add_cancel he
  have ha : b-a+a=b := Nat.sub_add_cancel hab
  have hc : (b-a) * Fintype.card α ≤ b * (Fintype.card α - emptyCount n) := by
    apply le_of_mul_le_mul_right _ hJ
    simpa only [mul_assoc] using hcert.trans hm
  nlinarith

/-- The relaxed 0.280 ceiling in the correlation-moment route. -/
theorem void_ceiling_280 {α : Type*} [Fintype α] (n : α → ℕ)
    (hN : 0 < ∑ c, n c)
    (hcert : 18 * Fintype.card α * collisionCount n ≤ 25 * (∑ c, n c)^2) :
    25 * emptyCount n ≤ 7 * Fintype.card α :=
  void_ceiling n (by norm_num) hN (by simpa using hcert)

/-- A rational-ceiling exit forces failure of its integer collision certificate. -/
theorem exit_implies_certificate_failure_of {α : Type*} [Fintype α] (n : α → ℕ)
    {a b : ℕ} (hab : a ≤ b) (hN : 0 < ∑ c, n c)
    (hexit : a * Fintype.card α < b * emptyCount n) :
    b * (∑ c, n c)^2 < (b-a) * Fintype.card α * collisionCount n := by
  by_contra h
  exact (not_lt_of_ge (void_ceiling n hab hN (by omega))) hexit

/-- The history union bound for any rational void threshold. The label type may depend
on both the draw and the history, as for the actual quotient groups. -/
theorem history_exit_count_of {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    {α : ι → Ω → Type*} [∀ i ω, Fintype (α i ω)] (n : ∀ i ω, α i ω → ℕ)
    {a b : ℕ} (hab : a ≤ b) (hN : ∀ i ω, 0 < ∑ c, n i ω c) :
    (univ.filter fun ω ↦ ∃ i, a * Fintype.card (α i ω) <
      b * emptyCount (n i ω)).card ≤
    ∑ i, (univ.filter fun ω ↦ b * (∑ c, n i ω c)^2 <
      (b-a) * Fintype.card (α i ω) * collisionCount (n i ω)).card := by
  let bad (i : ι) : Finset Ω := univ.filter fun ω ↦
    b * (∑ c, n i ω c)^2 <
      (b-a) * Fintype.card (α i ω) * collisionCount (n i ω)
  have hsub : (univ.filter fun ω ↦ ∃ i, a * Fintype.card (α i ω) <
      b * emptyCount (n i ω)) ⊆ univ.biUnion bad := by
    intro ω hω
    obtain ⟨i, hi⟩ := (mem_filter.mp hω).2
    apply mem_biUnion.mpr
    exact ⟨i, mem_univ i, mem_filter.mpr
      ⟨mem_univ ω, exit_implies_certificate_failure_of (n i ω) hab (hN i ω) hi⟩⟩
  exact (card_le_card hsub).trans (card_biUnion_le)

/-- The 0.273 ceiling used in the proposed exceptional-history route. -/
theorem void_ceiling_273 {α : Type*} [Fintype α] (n : α → ℕ)
    (hN : 0 < ∑ c, n c)
    (hcert : 727 * Fintype.card α * collisionCount n ≤ 1000 * (∑ c, n c)^2) :
    1000 * emptyCount n ≤ 273 * Fintype.card α :=
  void_ceiling n (by norm_num) hN (by simpa using hcert)

/-- A void exit forces failure of the collision certificate on that very history. -/
theorem exit_implies_certificate_failure {α : Type*} [Fintype α] (n : α → ℕ)
    (hN : 0 < ∑ c, n c)
    (hexit : 273 * Fintype.card α < 1000 * emptyCount n) :
    1000 * (∑ c, n c)^2 < 727 * Fintype.card α * collisionCount n := by
  by_contra h
  exact (not_lt_of_ge (void_ceiling_273 n hN (by omega))) hexit

/-- Uniform finite-history exit counting, allowing different label types at each draw.
No independence of the selected histories or of different draws is assumed. -/
theorem history_exit_count {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    {α : ι → Ω → Type*} [∀ i ω, Fintype (α i ω)] (n : ∀ i ω, α i ω → ℕ)
    (hN : ∀ i ω, 0 < ∑ c, n i ω c) :
    (univ.filter fun ω ↦ ∃ i, 273 * Fintype.card (α i ω) <
      1000 * emptyCount (n i ω)).card ≤
    ∑ i, (univ.filter fun ω ↦ 1000 * (∑ c, n i ω c)^2 <
      727 * Fintype.card (α i ω) * collisionCount (n i ω)).card := by
  simpa using history_exit_count_of n (a := 273) (b := 1000) (by norm_num) hN

end SigabaNeo.Wall1.CosetOccupancy

#print axioms SigabaNeo.Wall1.CosetOccupancy.support_bound
#print axioms SigabaNeo.Wall1.CosetOccupancy.void_ceiling
#print axioms SigabaNeo.Wall1.CosetOccupancy.void_ceiling_273
#print axioms SigabaNeo.Wall1.CosetOccupancy.exit_implies_certificate_failure
#print axioms SigabaNeo.Wall1.CosetOccupancy.history_exit_count

#print axioms SigabaNeo.Wall1.CosetOccupancy.void_ceiling_280
#print axioms SigabaNeo.Wall1.CosetOccupancy.exit_implies_certificate_failure_of
#print axioms SigabaNeo.Wall1.CosetOccupancy.history_exit_count_of
