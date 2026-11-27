import Mathlib.Logic.Function.Basic

theorem solution {X Y K A : Type} (row : X → K) (col : X → Y → A)
    (rows : Function.Surjective row) (cols : ∀ x, Function.Surjective (col x)) :
    Function.Surjective (fun p : X × Y => (row p.1, col p.1 p.2)) := by
  rintro ⟨k, a⟩
  obtain ⟨x, hx⟩ := rows k
  obtain ⟨y, hy⟩ := cols x a
  exact ⟨(x,y), Prod.ext hx hy⟩
