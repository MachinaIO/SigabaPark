import Definitions.Def_ColumnElimination

open AdvancedEncryption.WE.ColumnElimination

theorem solution {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (choose : V → (V →ₗ[K] K)) (cs : List V) (H : V →ₗ[K] V) (v : V) :
    (backsolve choose cs H v).length = cs.length := by
  induction cs generalizing H with
  | nil => rfl
  | cons a cs ih => simp [backsolve,ih]
