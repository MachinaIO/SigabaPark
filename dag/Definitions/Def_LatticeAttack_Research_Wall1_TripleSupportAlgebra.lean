import Definitions.Def_LatticeAttack_Research_Wall1_ExactSupportReconstruction

set_option autoImplicit true

/-! Three-label Mobius support after the zero- and two-label terms vanish. -/
noncomputable section
namespace SigabaNeo.Wall1.ExactSupportReconstruction
open Finset
open scoped Classical
variable {α : Type*} [DecidableEq α]

lemma sum_powerset_singleton (f : Finset α → ℝ) (s : α) :
    (∑ A ∈ ({s} : Finset α).powerset, f A) = f ∅ + f {s} := by
  have h := sum_powerset_insert (s := (∅ : Finset α)) (a := s) (notMem_empty s) f
  simpa using h

theorem exactSupport_pair (f : Finset α → ℝ) (s t : α) (hst : s ≠ t) :
    exactSupport f {s,t} = f {s,t} - f {s} - f {t} + f ∅ := by
  simp [exactSupport, sum_powerset_insert, sum_powerset_singleton, hst]
  ring

theorem exactSupport_triple (f : Finset α → ℝ) (s t u : α)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    exactSupport f {s,t,u} = f {s,t,u} - f {s,t} - f {s,u} - f {t,u} +
      f {s} + f {t} + f {u} - f ∅ := by
  simp [exactSupport, sum_powerset_insert, sum_powerset_singleton, hst, hsu, htu]
  ring

theorem exactSupport_triple_of_pair_zero (f : Finset α → ℝ) (s t u : α)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) (h0 : f ∅ = 0)
    (hST : exactSupport f {s,t} = 0) (hSU : exactSupport f {s,u} = 0)
    (hTU : exactSupport f {t,u} = 0) :
    exactSupport f {s,t,u} = f {s,t,u} - f {s} - f {t} - f {u} := by
  rw [exactSupport_pair f s t hst] at hST
  rw [exactSupport_pair f s u hsu] at hSU
  rw [exactSupport_pair f t u htu] at hTU
  rw [exactSupport_triple f s t u hst hsu htu]
  linarith

end SigabaNeo.Wall1.ExactSupportReconstruction
#print axioms SigabaNeo.Wall1.ExactSupportReconstruction.exactSupport_triple_of_pair_zero
