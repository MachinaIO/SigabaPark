import Mathlib.LinearAlgebra.Matrix.Rank

theorem solution {K ι : Type*} [Field K] [Fintype ι] {d : ℕ}
    (U : Matrix (Fin (d + 1)) (Fin d) K) (T : Matrix (Fin d) ι K) :
    ¬ LinearIndependent K (fun i => (U * T) i) := by
  intro h
  have h1 : (U * T).rank = d + 1 := by
    rw [Matrix.rank_eq_finrank_span_row]
    have := finrank_span_eq_card h
    rw [Fintype.card_fin] at this; exact this
  have h2 : (U * T).rank ≤ d := (Matrix.rank_mul_le_left U T).trans (Matrix.rank_le_width U)
  omega
