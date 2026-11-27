import Mathlib

set_option maxHeartbeats 2000000 in
theorem solution {ι : Type} (p h slope : Bool) (y v active : ι → Bool) :
    let pad0 (r : ι → Bool) (i : ι) := if p then r i else active i
    let pad1 (r : ι → Bool) (i : ι) := if p then active i else r i
    let pi (r : ι → Bool) (i : ι) := v i ^^ pad0 r i ^^ pad1 r i
    let u (r : ι → Bool) (i : ι) := y i ^^ pi r i
    let g (r : ι → Bool) (i : ι) :=
      ((if h then pi r i else v i) ^^ pad0 r i) ^^ (u r i && slope)
    let out (i : ι) := if p ^^ h then y i else v i
    let c := h ^^ slope
    ∃ e : (ι → Bool) ≃ (ι → Bool), ∀ r,
      (u r, g r) = (e r, fun i => out i ^^ (e r i && (c ^^ p)) ^^ active i) ∧
      (fun i => g r i ^^ (u r i && (c ^^ p)) ^^ active i) = out := by
  dsimp only
  let f (r : ι → Bool) (i : ι) := y i ^^ v i ^^ active i ^^ r i
  have inv : Function.Involutive f := by
    intro r
    funext i
    simp only [f]
    generalize y i = yy
    generalize v i = vv
    generalize active i = aa
    generalize r i = rr
    cases yy <;> cases vv <;> cases aa <;> cases rr <;> rfl
  refine ⟨⟨f, f, inv, inv⟩, ?_⟩
  intro r
  constructor
  · apply Prod.ext
    all_goals funext i
    all_goals
      first
      | change _ = (y i ^^ v i ^^ active i ^^ r i)
      | change _ = ((if p ^^ h then y i else v i) ^^ ((y i ^^ v i ^^ active i ^^ r i) && ((h ^^ slope) ^^ p)) ^^ active i)
    all_goals dsimp only
    all_goals generalize y i = yy
    all_goals generalize v i = vv
    all_goals generalize active i = aa
    all_goals generalize r i = rr
    all_goals cases p <;> cases h <;> cases slope <;> cases yy <;> cases vv <;> cases aa <;> cases rr <;> rfl
  · funext i
    try dsimp only
    generalize y i = yy
    generalize v i = vv
    generalize active i = aa
    generalize r i = rr
    cases p <;> cases h <;> cases slope <;> cases yy <;> cases vv <;> cases aa <;> cases rr <;> rfl
