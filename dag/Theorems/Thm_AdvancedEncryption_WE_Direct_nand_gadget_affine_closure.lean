import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.FinCases

/-- Affine closure of NAND gadgets (note `pq-we-direct-algebraic-languages`). Let `L : V →+ W` be
any additive map (the constraint map of a linear encoding) and let `sol x y` be block solutions for
the four valid NAND triples `(x, y, 1 - x y)`, i.e. `L (sol x y) = T(x, y, 1 - x y)` for an affine
map `T(a, b, c) = t0 + a t1 + b t2 + c t3`. Then for every triple `(a, b, c)` in `{0,1}^3`, valid or
not, some integer combination of the four block solutions with coefficient `ℓ₁` norm at most `5`
is mapped to `T(a, b, c)`. So any encoding that is linear in local block data accepts a violated
gate at constant extra cost. -/
theorem AdvancedEncryption.WE.Direct.nand_gadget_affine_closure {V W : Type*} [AddCommGroup V]
    [AddCommGroup W] (L : V →+ W) (t0 t1 t2 t3 : W) (sol : Fin 2 → Fin 2 → V)
    (hsol : ∀ x y : Fin 2, L (sol x y) =
      t0 + ((x : ℕ) : ℤ) • t1 + ((y : ℕ) : ℤ) • t2 + (1 - ((x : ℕ) : ℤ) * ((y : ℕ) : ℤ)) • t3)
    (a b c : Fin 2) :
    ∃ l : Fin 2 → Fin 2 → ℤ, (∑ x, ∑ y, |l x y|) ≤ 5 ∧
      L (∑ x, ∑ y, l x y • sol x y) =
        t0 + ((a : ℕ) : ℤ) • t1 + ((b : ℕ) : ℤ) • t2 + ((c : ℕ) : ℤ) • t3 := by sorry
