module

public import Definitions.Def_LatticeAttack_Attacks_AroraGe_Rank

set_option autoImplicit true

public section

namespace SigabaNeo.Lattices.AroraGe.CubicSolver

abbrev F := ZMod 5
abbrev Triple := F × F × F

/-- Count each field multiplication in the straight-line computation. -/
def mul (x y : F) : StateM ℕ F := do
  modify (· + 1)
  return x * y

/-- Coefficients and RHS of (b-aX)³-(b-aX) = 0. -/
def row (a b : F) : StateM ℕ (Triple × F) := do
  let aa ← mul a a
  let bb ← mul b b
  let aaa ← mul aa a
  let bbb ← mul bb b
  let u ← mul 3 bb
  let v ← mul (u - 1) a
  let w ← mul (-3) b
  let z ← mul w aa
  return ((v, z, aaa), bbb - b)

def det (x y z : Triple) : StateM ℕ F := do
  let u ← mul y.2.1 z.2.2
  let v ← mul y.2.2 z.2.1
  let w ← mul y.2.2 z.1
  let t ← mul y.1 z.2.2
  let h ← mul y.1 z.2.1
  let k ← mul y.2.1 z.1
  return (← mul x.1 (u-v)) + (← mul x.2.1 (w-t)) + (← mul x.2.2 (h-k))

/-- Cramer's rule for the degree-one coordinate. The counter records multiplications
including scalar multiplications; one pivot test is extra. For a nonzero pivot in F₅, its cube is its inverse. -/
def solve (a b : Triple) : Option F × ℕ := (do
  let (x, p) ← row a.1 b.1
  let (y, q) ← row a.2.1 b.2.1
  let (z, r) ← row a.2.2 b.2.2
  let d ← det x y z
  let t ← det (p, x.2) (q, y.2) (r, z.2)
  let dd ← mul d d
  let inv ← mul dd d
  let x ← mul t inv
  return if d = 0 then none else some x : StateM ℕ (Option F)).run 0

/-- Sample RHS with the fixed, legal error vector (1,0,-1). -/
def rhs (s : F) (a : Triple) : Triple := (a.1*s+1, a.2.1*s, a.2.2*s-1)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- Under three independent uniform coefficients, exactly 32 of the 125 inputs recover
each fixed secret. The operation count holds for arbitrary right-hand sides. -/
theorem recovery (s : F) :
    (Finset.univ.filter (fun a : Triple ↦ (solve a (rhs s a)).1 = some s)).card = 32 ∧
    Fintype.card Triple = 125 ∧ ∀ a b : Triple, (solve a b).2 = 45 := by
  refine ⟨?_, by decide, fun _ _ ↦ rfl⟩
  revert s
  decide

abbrev Errors := Fin 3 × Fin 3 × Fin 3

/-- Codes 0, 1 and 2 represent the errors +1, 0 and -1. -/
def noisyRhs (s : F) (a : Triple) (e : Errors) : Triple :=
  (a.1*s + (1 - e.1.val : F), a.2.1*s + (1 - e.2.1.val : F),
    a.2.2*s + (1 - e.2.2.val : F))

set_option maxRecDepth 10000 in
/-- A lower bound for the joint experiment with independent uniform coefficients and errors. -/
theorem uniform_recovery (s : F) :
    32 ≤ (Finset.univ.filter (fun p : Triple × Errors ↦
      (solve p.1 (noisyRhs s p.1 p.2)).1 = some s)).card ∧
    Fintype.card (Triple × Errors) = 3375 ∧ ∀ a b : Triple, (solve a b).2 = 45 := by
  refine ⟨?_, by simp [Triple, Errors, F, ZMod.card], (recovery s).2.2⟩
  let emb : Triple ↪ Triple × Errors := ⟨fun a ↦ (a, 0, 1, 2), fun _ _ h ↦ congrArg Prod.fst h⟩
  let good := Finset.univ.filter (fun a : Triple ↦ (solve a (rhs s a)).1 = some s)
  have hs : good.map emb ⊆ Finset.univ.filter (fun p : Triple × Errors ↦
      (solve p.1 (noisyRhs s p.1 p.2)).1 = some s) := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hp
    have he : noisyRhs s a (0, 1, 2) = rhs s a := by
      simp [noisyRhs, rhs, sub_eq_add_neg]
      ring_nf
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, he ▸ (Finset.mem_filter.mp ha).2⟩
  simpa only [Finset.card_map, good, (recovery s).1] using Finset.card_le_card hs

end SigabaNeo.Lattices.AroraGe.CubicSolver

#print axioms SigabaNeo.Lattices.AroraGe.CubicSolver.recovery

#print axioms SigabaNeo.Lattices.AroraGe.CubicSolver.uniform_recovery
