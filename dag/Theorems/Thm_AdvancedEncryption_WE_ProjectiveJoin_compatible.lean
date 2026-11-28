import Definitions.Def_ProjectiveJoin
open ProjectiveJoin
theorem AdvancedEncryption.WE.ProjectiveJoin.compatible {F K V : Type} [Field F] [DecidableEq F] [Field K]
    [AddCommGroup V] [Module K V] (d : Nat) (points : Finset (Option F))
    (target : V) (ranges : Option F → Submodule K V)
    (positive : Finset (Module.Dual K V)) (poly : Module.Dual K V → Polynomial F)
    (listAll : ∀ f : Module.Dual K V, f target ≠ 0 → f ∈ positive)
    (degree : ∀ f ∈ positive, (poly f).natDegree≤d)
    (nonzero : ∀ f ∈ positive, poly f ≠ 0)
    (sound : ∀ x ∈ points, ∀ f ∈ positive,
        f ∈ (ranges x).dualAnnihilator → atPoint d (poly f) x=0)
    (budget : positive.card*d<points.card) :
    ∃ x ∈ points, target ∈ ranges x := by sorry
