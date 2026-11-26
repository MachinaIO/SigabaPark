import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Common

theorem solution {W V U : Type*} (pre : W → V) (suf : W → U)
    (hinj : Function.Injective pre ∨ Function.Injective suf)
    (S : Finset V) (T : Finset U)
    (hST : ∀ x ∈ S, ∀ u ∈ T, ∃ w, pre w = x ∧ suf w = u) :
    S.card ≤ 1 ∨ T.card ≤ 1 := by
  by_contra hc
  simp only [not_or, not_le] at hc
  obtain ⟨x, hx, x', hx', hxx⟩ := Finset.one_lt_card.mp hc.1
  obtain ⟨u, hu, u', hu', huu⟩ := Finset.one_lt_card.mp hc.2
  obtain ⟨w1, h1p, h1s⟩ := hST x hx u hu
  obtain ⟨w2, h2p, h2s⟩ := hST x' hx' u hu
  obtain ⟨w3, h3p, h3s⟩ := hST x hx u' hu'
  rcases hinj with hp | hs
  · have : w1 = w3 := hp (h1p.trans h3p.symm)
    subst this
    exact huu (h1s.symm.trans h3s)
  · have : w1 = w2 := hs (h1s.trans h2s.symm)
    subst this
    exact hxx (h1p.symm.trans h2p)
