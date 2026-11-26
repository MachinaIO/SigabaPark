module

public import Definitions.Def_LatticeAttack_Attacks_Bkw_Fresh
import Mathlib.Tactic

set_option autoImplicit true

public section

namespace SigabaNeo.Lattices.Attacks.Bkw.BinaryPair

variable {B : Type} [DecidableEq B]

/-- Public row: block, last coefficient, noisy right-hand side. -/
abbrev Row (B : Type*) := B × Bool × Bool

def row (blockTerm : B → Bool) (s : Bool) (b : B) (x e : Bool) : Row B :=
  (b, x, (blockTerm b ^^ (x && s)) ^^ e)

/-- One block reduction; a useless difference gives a fair fallback guess. -/
def decode (u v : Row B) (coin : Bool) : Bool :=
  if u.1 = v.1 ∧ u.2.1 ≠ v.2.1 then u.2.2 ^^ v.2.2 else coin

/-- Charge one unit for a public-row read, block equality, bit comparison, or XOR.
Control flow, the supplied random bit, and generation of the public rows are free. -/
def charge {α : Type} (a : α) : StateM Nat α := do
  modify (· + 1)
  return a

def run (u v : Row B) (coin : Bool) : StateM Nat Bool := do
  let a ← charge u
  let b ← charge v
  if ← charge (decide (a.1 = b.1)) then
    if ← charge (decide (a.2.1 ≠ b.2.1)) then
      charge (a.2.2 ^^ b.2.2)
    else pure coin
  else pure coin

private theorem run_spec (u v : Row B) (coin : Bool) :
    ((run u v coin).run 0).1 = decode u v coin ∧ ((run u v coin).run 0).2 ≤ 5 := by
  by_cases hb : u.1 = v.1 <;> by_cases hx : u.2.1 = v.2.1 <;>
    simp [run, charge, decode, hb, hx, StateT.run, bind, pure, StateT.bind, StateT.pure,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]

private theorem run_value (u v : Row B) (coin : Bool) :
    ((run u v coin).run 0).1 = decode u v coin := (run_spec u v coin).1

def bern (p : ℝ) (f : Bool → ℝ) : ℝ := (1 - p) * f false + p * f true

/-- Conditional success probability for fixed blocks. Last coordinates and fallback
are fair independent bits, and both errors are fresh Bernoulli(p) bits. -/
noncomputable def fixedSuccess (t : B → Bool) (s : Bool) (p : ℝ) (b c : B) : ℝ :=
  bern (1/2) fun x ↦ bern (1/2) fun y ↦ bern p fun e ↦ bern p fun f ↦
    bern (1/2) fun coin ↦
      if ((run (row t s b x e) (row t s c y f) coin).run 0).1 = s then 1 else 0

private theorem fixed_eq (t : B → Bool) (s : Bool) (p : ℝ) (b c : B) :
    fixedSuccess t s p b c = 1/2 + if c = b then (1 - 2*p)^2 / 4 else 0 := by
  by_cases h : c = b
  · subst c
    cases hs : t b <;> cases s <;>
      norm_num [fixedSuccess, bern, run_value, row, decode, hs] <;> ring
  · have h' := Ne.symm h
    cases s <;>
      norm_num [fixedSuccess, bern, run_value, row, decode, h, h'] <;> ring

variable [Fintype B] [Nonempty B]

/-- Average over the two independent uniform blocks. -/
noncomputable def success (t : B → Bool) (s : Bool) (p : ℝ) : ℝ :=
  (∑ b : B, ∑ c : B, fixedSuccess t s p b c) / (Fintype.card B : ℝ)^2

theorem end_to_end (t : B → Bool) (s : Bool) (p : Set.Icc (0 : ℝ) 1) :
    success t s p = 1/2 + (1 - 2*(p : ℝ))^2 / (4 * Fintype.card B) ∧
    ∀ (u v : Row B) (coin : Bool), ((run u v coin).run 0).2 ≤ 5 := by
  constructor
  · simp only [success, fixed_eq, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h : (Fintype.card B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    field_simp
  · exact fun u v coin ↦ (run_spec u v coin).2

#print axioms end_to_end

end SigabaNeo.Lattices.Attacks.Bkw.BinaryPair
