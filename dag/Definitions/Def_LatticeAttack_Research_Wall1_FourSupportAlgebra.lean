import Definitions.Def_LatticeAttack_Research_Wall1_TripleSupportAlgebra

set_option autoImplicit true

/-! Four-input exact support after subtracting all proper connected supports. -/
noncomputable section
namespace SigabaNeo.Wall1.ExactSupportReconstruction
open Finset
open scoped Classical
variable {α : Type*} [DecidableEq α]

theorem exactSupport_four (f : Finset α → ℝ) (a b c d : α)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    exactSupport f {a,b,c,d} = f {a,b,c,d} -
      (f {a,b,c} + f {a,b,d} + f {a,c,d} + f {b,c,d}) +
      (f {a,b} + f {a,c} + f {a,d} + f {b,c} + f {b,d} + f {c,d}) -
      (f {a} + f {b} + f {c} + f {d}) + f ∅ := by
  simp [exactSupport, sum_powerset_insert, sum_powerset_singleton,
    hab, hac, had, hbc, hbd, hcd]
  ring

/-- Pairwise independence removes pair supports, but the four triple corrections remain. -/
theorem exactSupport_four_of_pair_zero (f : Finset α → ℝ) (a b c d : α)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (h0 : f ∅ = 0)
    (hAB : exactSupport f {a,b} = 0) (hAC : exactSupport f {a,c} = 0)
    (hAD : exactSupport f {a,d} = 0) (hBC : exactSupport f {b,c} = 0)
    (hBD : exactSupport f {b,d} = 0) (hCD : exactSupport f {c,d} = 0) :
    exactSupport f {a,b,c,d} =
      f {a,b,c,d} - (f {a} + f {b} + f {c} + f {d}) -
      (exactSupport f {a,b,c} + exactSupport f {a,b,d} +
        exactSupport f {a,c,d} + exactSupport f {b,c,d}) := by
  rw [exactSupport_four f a b c d hab hac had hbc hbd hcd,
    exactSupport_triple f a b c hab hac hbc,
    exactSupport_triple f a b d hab had hbd,
    exactSupport_triple f a c d hac had hcd,
    exactSupport_triple f b c d hbc hbd hcd]
  rw [exactSupport_pair f a b hab] at hAB
  rw [exactSupport_pair f a c hac] at hAC
  rw [exactSupport_pair f a d had] at hAD
  rw [exactSupport_pair f b c hbc] at hBC
  rw [exactSupport_pair f b d hbd] at hBD
  rw [exactSupport_pair f c d hcd] at hCD
  linarith

end SigabaNeo.Wall1.ExactSupportReconstruction
#print axioms SigabaNeo.Wall1.ExactSupportReconstruction.exactSupport_four_of_pair_zero
