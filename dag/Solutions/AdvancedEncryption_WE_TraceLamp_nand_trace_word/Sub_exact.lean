import Mathlib

theorem solution {G : Type} [AddCommGroup G] (one : G) (gs : List (Bool × Bool × Bool)) (u : G) :
    let bit := fun b : Bool ↦ if b then (1 : ZMod 3) else 0
    let update := fun (q : G × ZMod 3) (g : Bool × Bool × Bool) ↦
      let s₁ := q.2 + bit g.1
      let s₂ := s₁ + bit g.2.1
      let v := if g.2.2 = decide (s₂ ≠ 2) then q.1 else q.1 + one
      (v, s₂ - bit g.2.1 - bit g.1)
    let bad := fun (g : Bool × Bool × Bool) ↦ g.2.2 != !(g.1 && g.2.1)
    gs.foldl update (u, 0) = (u + (gs.filter bad).length • one, 0) := by
  let bit := fun b : Bool ↦ if b then (1 : ZMod 3) else 0
  let update := fun (q : G × ZMod 3) (g : Bool × Bool × Bool) ↦
    let s₁ := q.2 + bit g.1
    let s₂ := s₁ + bit g.2.1
    let v := if g.2.2 = decide (s₂ ≠ 2) then q.1 else q.1 + one
    (v, s₂ - bit g.2.1 - bit g.1)
  let bad := fun (g : Bool × Bool × Bool) ↦ g.2.2 != !(g.1 && g.2.1)
  change gs.foldl update (u, 0) = (u + (gs.filter bad).length • one, 0)
  have localStep (g : Bool × Bool × Bool) (v : G) :
      update (v,0) g = (if bad g then v + one else v, 0) := by
    rcases g with ⟨x,y,z⟩
    cases x <;> cases y <;> cases z <;> rfl
  induction gs generalizing u with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, localStep, ih]
    cases h : bad g <;> simp [List.filter_cons, h, add_nsmul, add_assoc, add_comm, add_left_comm]
