import Definitions.Def_OwnedGarbling

open OwnedGarbling
open scoped BigOperators

theorem solution {I : Type} [Fintype I] [DecidableEq I] (slope pad point : I → ZMod 2)
    (offset : ZMod 2) (test : ZMod 2 → (I → ZMod 2) → ℝ) :
    (∑ inactive : I → ZMod 2,
       test (offset + ∑ i, (pad i + point i * (pad i + inactive i)))
         (fun i ↦ slope i + pad i + inactive i)) =
    ∑ delta : I → ZMod 2,
      test ((offset + ∑ i, point i * slope i) + ∑ i, pad i + ∑ i, point i * delta i)
        delta := by
  classical
  let e : (I → ZMod 2) ≃ (I → ZMod 2) := {
    toFun := fun v i ↦ slope i + pad i + v i
    invFun := fun v i ↦ v i - (slope i + pad i)
    left_inv := by intro v; funext i; dsimp; abel
    right_inv := by intro v; funext i; dsimp; abel }
  let kernel := fun delta : I → ZMod 2 ↦
    test ((offset + ∑ i, point i * slope i) + ∑ i, pad i + ∑ i, point i * delta i) delta
  calc
    _ = ∑ v : I → ZMod 2, kernel (e v) := by
      apply Finset.sum_congr rfl
      intro v _
      dsimp [kernel, e]
      congr 1
      rw [Finset.sum_add_distrib]
      have zero (a : ZMod 2) : a+a=0 := by exact CharTwo.add_self_eq_zero a
      have eqn : ∀ i, point i*(pad i+v i) =
        point i*slope i + point i*(slope i+pad i+v i) := by
        intro i
        simp only [mul_add]
        linear_combination -(zero (point i * slope i))
      simp_rw [eqn]
      rw [Finset.sum_add_distrib]
      abel
    _ = _ := e.sum_comp kernel
