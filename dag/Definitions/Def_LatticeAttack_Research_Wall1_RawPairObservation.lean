import Definitions.Def_LatticeAttack_Research_Wall1_RawConnectedSupport

set_option autoImplicit true

/-! Two distinct centered inputs admit arbitrary joint observations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SigabaNeo.Wall1.RawPrefixOccupancy
open Finset ControlledPlane TerminalProjection
open scoped Classical
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

theorem inputObservation_pair_surjective {k : ℕ} (hk : k ≤ 512)
    (s t : Fin k → ℤ) (j : Fin k) (hj : (s j : ZMod 3329) ≠ (t j : ZMod 3329)) :
    Function.Surjective ((inputObservation hk s).prod (inputObservation hk t)) := by
  intro y
  let a : Column := fun i ↦ (y.1 i - y.2 i) / ((s j : ZMod 3329) - t j)
  let A : Sample := fun i l ↦ if l = j.castLE hk then a i else 0
  let c : Column := fun i ↦ y.1 i - (s j : ZMod 3329) * a i
  have hs (u : Fin k → ℤ) (i : Fin 400) :
      (∑ l, (u l : ZMod 3329) * A i (l.castLE hk)) = (u j : ZMod 3329) * a i := by
    have he (l : Fin k) : l.castLE hk = j.castLE hk ↔ l = j := by
      simp only [Fin.ext_iff]
      rfl
    simp [A, he, mul_ite]
  refine ⟨(A,c), ?_⟩
  apply Prod.ext <;> ext i
  · change c i + ∑ l, (s l : ZMod 3329) * A i (l.castLE hk) = y.1 i
    rw [hs]
    simp [c]
  · change c i + ∑ l, (t l : ZMod 3329) * A i (l.castLE hk) = y.2 i
    rw [hs]
    dsimp [c,a]
    have hne := sub_ne_zero.mpr hj
    field_simp
    ring

theorem centered_inputObservation_pair_surjective {k : ℕ} (hk : k ≤ 512)
    (s t : Fin k → ℤ) (hs : ∀ i, -1664 ≤ s i ∧ s i ≤ 1664)
    (ht : ∀ i, -1664 ≤ t i ∧ t i ≤ 1664) (hne : s ≠ t) :
    Function.Surjective ((inputObservation hk s).prod (inputObservation hk t)) := by
  have hex : ∃ j, (s j : ZMod 3329) ≠ (t j : ZMod 3329) := by
    by_contra! h
    apply hne
    funext j
    exact centered_intCast_injective (hs j) (ht j) (h j)
  obtain ⟨j,hj⟩ := hex
  exact inputObservation_pair_surjective hk s t j hj

theorem singletonFamily_pair_surjective {k : ℕ} (hk : k ≤ 512)
    (s t : Fin k → ℤ) (hs : ∀ i, -1664 ≤ s i ∧ s i ≤ 1664)
    (ht : ∀ i, -1664 ≤ t i ∧ t i ≤ 1664) (hne : s ≠ t) :
    Function.Surjective ((inputFamilyObservation hk {s}).prod
      (inputFamilyObservation hk {t})) := by
  intro y
  obtain ⟨p,hp⟩ := centered_inputObservation_pair_surjective hk s t hs ht hne
    (y.1 ⟨s,mem_singleton_self s⟩, y.2 ⟨t,mem_singleton_self t⟩)
  refine ⟨p, ?_⟩
  apply Prod.ext
  · funext u
    obtain ⟨u,hu⟩ := u
    have he : u = s := mem_singleton.mp hu
    subst u
    exact congrArg Prod.fst hp
  · funext u
    obtain ⟨u,hu⟩ := u
    have he : u = t := mem_singleton.mp hu
    subst u
    exact congrArg Prod.snd hp

theorem centered_pair_rankSeparable {k : ℕ} (hk : k ≤ 512)
    (s t : Fin k → ℤ) (hs : ∀ i, -1664 ≤ s i ∧ s i ≤ 1664)
    (ht : ∀ i, -1664 ≤ t i ∧ t i ≤ 1664) (hne : s ≠ t) :
    RankSeparable hk {s,t} := by
  have hj := singletonFamily_pair_surjective hk s t hs ht hne
  have hf : Function.Surjective (inputFamilyObservation hk {s}) := by
    intro y
    obtain ⟨p,hp⟩ := hj (y,0)
    exact ⟨p,congrArg Prod.fst hp⟩
  have hg : Function.Surjective (inputFamilyObservation hk {t}) := by
    intro y
    obtain ⟨p,hp⟩ := hj (0,y)
    exact ⟨p,congrArg Prod.snd hp⟩
  refine ⟨{s},{t},singleton_nonempty _,singleton_nonempty _, ?_, ?_, ?_⟩
  · simpa using hne
  · simp
  · rw [LinearMap.range_eq_top.mpr hj, LinearMap.range_eq_top.mpr hf,
      LinearMap.range_eq_top.mpr hg]
    simp only [finrank_top, Module.finrank_prod]

theorem rawExactSupport_centered_pair_zero {k : ℕ} (hk : k ≤ 512)
    (T : Finset (Candidate k)) (s t : Fin k → ℤ)
    (hs : ∀ i, -1664 ≤ s i ∧ s i ≤ 1664)
    (ht : ∀ i, -1664 ≤ t i ∧ t i ≤ 1664) (hne : s ≠ t) (n : ℕ) :
    rawExactSupport hk T n {s,t} = 0 :=
  rawExactSupport_zero_of_rankSeparable hk T {s,t}
    (centered_pair_rankSeparable hk s t hs ht hne) n

theorem rawExactSupport_card_two_zero {k : ℕ} (hk : k ≤ 512)
    (T : Finset (Candidate k)) (S : Finset (Fin k → ℤ))
    (hS : ∀ s ∈ S, ∀ i, -1664 ≤ s i ∧ s i ≤ 1664)
    (hc : S.card = 2) (n : ℕ) : rawExactSupport hk T n S = 0 := by
  obtain ⟨s,t,hne,rfl⟩ := card_eq_two.mp hc
  exact rawExactSupport_centered_pair_zero hk T s t
    (hS s (by simp)) (hS t (by simp)) hne n

end SigabaNeo.Wall1.RawPrefixOccupancy
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.centered_inputObservation_pair_surjective
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.rawExactSupport_centered_pair_zero
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.rawExactSupport_card_two_zero
