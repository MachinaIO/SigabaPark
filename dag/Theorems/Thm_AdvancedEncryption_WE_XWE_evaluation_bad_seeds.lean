import SigabaNeoStd

open Polynomial

theorem AdvancedEncryption.WE.XWE.evaluation_bad_seeds {K T : Type*} [Field K] [Fintype K] [DecidableEq K]
    (cert : Finset T) (res : T → Finset K[X]) (D h : ℕ)
    (hsize : ∀ t ∈ cert, (res t).card ≤ D)
    (hnz : ∀ t ∈ cert, ∀ p ∈ res t, p ≠ 0)
    (hdeg : ∀ t ∈ cert, ∀ p ∈ res t, p.natDegree ≤ h) :
    (Finset.univ.filter (fun a : K ↦ ∃ t ∈ cert, ∃ p ∈ res t, p.eval a = 0)).card ≤
      cert.card * D * h := by
  sorry
