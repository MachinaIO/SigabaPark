import Definitions.Def_ColumnElimination

open AdvancedEncryption.WE.ColumnElimination

theorem solution {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (choose : V → (V →ₗ[K] K)) (cs : List V) (H : V →ₗ[K] V) (v : V) :
    H v - H (weighted cs (backsolve choose cs H v)) = terminal choose cs H v := by
  induction cs generalizing H with
  | nil => simp [weighted, terminal]
  | cons a cs ih =>
    let l := choose (H a)
    let P := kill (H a) l
    let hp := P.comp H
    let u := weighted cs (backsolve choose cs hp v)
    change H v - H (l (H v - H u) • a + u) = terminal choose cs hp v
    calc
      _ = (H v - H u) - l (H v - H u) • H a := by rw [map_add, map_smul]; abel
      _ = P (H v - H u) := rfl
      _ = hp v - hp u := by rw [map_sub]; rfl
      _ = terminal choose cs hp v := ih hp
