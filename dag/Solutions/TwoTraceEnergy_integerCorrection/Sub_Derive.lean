import Definitions.Def_TwoTraceEnergy
import Mathlib.Tactic

private theorem quadratic (a b t u s : ℤ) :
    a*a+b*b+t*t+u*u+s*s ≤ 8*(a*a+b*b+t*t+u*u+s*s)
      + 2*(a*u-2*a*s-4*b*u-2*t*u-4*t*s) := by
  nlinarith [sq_nonneg (a+u),sq_nonneg (a-s),sq_nonneg (b-u),
    sq_nonneg (t-u),sq_nonneg (t-s),sq_nonneg a,sq_nonneg b,
    sq_nonneg t,sq_nonneg u,sq_nonneg s]

private def sign (b : Bool) : ℤ := if b then 1 else -1

private theorem push_eq (b : Bool) (r : ℕ) :
    TwoTraceEnergy.push b r = TwoTraceEnergy.bit b + sign b * (r:ℤ) := by
  cases b <;> simp [TwoTraceEnergy.push, TwoTraceEnergy.bit, sign]

private theorem gradient : ∀ a b t u s : Bool,
    let A := TwoTraceEnergy.bit a
    let B := TwoTraceEnergy.bit b
    let T := TwoTraceEnergy.bit t
    let U := TwoTraceEnergy.bit u
    let S := TwoTraceEnergy.bit s
    0 ≤ 4 + sign a*(U-2*S) ∧ 0 ≤ 4 + sign b*(2-4*U) ∧
    0 ≤ 4 + sign t*(3-2*U-4*S) ∧ 0 ≤ 4 + sign u*(A-2*T-4*B+2) ∧
    0 ≤ 4 + sign s*(-2*A-4*T+4) := by decide

private theorem sign_sq (b : Bool) : sign b*sign b=1 := by cases b <;> decide
private theorem penalty_push (b : Bool) (r : ℕ) :
    TwoTraceEnergy.pen (TwoTraceEnergy.push b r) = (sign b*(r:ℤ))^2+(r:ℤ) := by
  cases b <;> simp [TwoTraceEnergy.pen,TwoTraceEnergy.push,sign] <;> ring

theorem solution (a b t u s : Bool) (i j k l m : ℕ) :
    let A := TwoTraceEnergy.push a i
    let B := TwoTraceEnergy.push b j
    let T := TwoTraceEnergy.push t k
    let U := TwoTraceEnergy.push u l
    let S := TwoTraceEnergy.push s m
    (i:ℤ)^2+(j:ℤ)^2+(k:ℤ)^2+(l:ℤ)^2+(m:ℤ)^2 ≤
      2*(TwoTraceEnergy.h A B T U S + 4*(TwoTraceEnergy.pen A + TwoTraceEnergy.pen B +
      TwoTraceEnergy.pen T + TwoTraceEnergy.pen U + TwoTraceEnergy.pen S) -
      TwoTraceEnergy.localCost a b t u s) := by
  dsimp only
  rw [penalty_push,penalty_push,penalty_push,penalty_push,penalty_push]
  simp only [push_eq, TwoTraceEnergy.localCost, TwoTraceEnergy.h]
  obtain ⟨ha,hb,ht,hu,hs⟩ := gradient a b t u s
  have aux (v : Bool) (r : ℕ) : (sign v*(r:ℤ))^2=(r:ℤ)^2 := by
    cases v <;> simp [sign]
  have hq := quadratic (sign a*(i:ℤ)) (sign b*(j:ℤ)) (sign t*(k:ℤ)) (sign u*(l:ℤ)) (sign s*(m:ℤ))
  have hi := mul_nonneg ha (Int.natCast_nonneg i)
  have hj := mul_nonneg hb (Int.natCast_nonneg j)
  have hk := mul_nonneg ht (Int.natCast_nonneg k)
  have hl := mul_nonneg hu (Int.natCast_nonneg l)
  have hm := mul_nonneg hs (Int.natCast_nonneg m)
  nlinarith only [hq,hi,hj,hk,hl,hm,aux a i,aux b j,aux t k,aux u l,aux s m]
