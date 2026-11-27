import Mathlib

theorem AdvancedEncryption.WE.DirectedLabels.chart_record {K X Y P Q : Type} [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y] [AddCommGroup P] [Module K P]
    [AddCommGroup Q] [Module K Q] (T : X →ₗ[K] Y) (M : P →ₗ[K] Q)
    (f h : X →ₗ[K] P) (g j : Y →ₗ[K] Q) (inter : j.comp T = M.comp h) :
    (g+j).comp T - M.comp (f+h) = g.comp T - M.comp f := by sorry
