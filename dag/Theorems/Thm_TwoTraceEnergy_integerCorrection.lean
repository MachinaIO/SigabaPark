import Definitions.Def_TwoTraceEnergy
import Mathlib.Tactic

theorem TwoTraceEnergy.integerCorrection (a b t u s : Bool) (i j k l m : ℕ) :
    let A := TwoTraceEnergy.push a i
    let B := TwoTraceEnergy.push b j
    let T := TwoTraceEnergy.push t k
    let U := TwoTraceEnergy.push u l
    let S := TwoTraceEnergy.push s m
    (i:ℤ)^2+(j:ℤ)^2+(k:ℤ)^2+(l:ℤ)^2+(m:ℤ)^2 ≤
      2*(TwoTraceEnergy.h A B T U S + 4*(TwoTraceEnergy.pen A + TwoTraceEnergy.pen B +
      TwoTraceEnergy.pen T + TwoTraceEnergy.pen U + TwoTraceEnergy.pen S) -
      TwoTraceEnergy.localCost a b t u s) := by
  sorry
