import SigabaNeoStd.Lattices.RingLWEInst
import Mathlib.Tactic
namespace RingPrefixArithmetic
open SigabaNeo.Lattices
def params : RingLWE.decision.Params :=
  ({ N:=1024,m:=514,q:=2^19,error:=.bounded 1,secret:=.uniform } : RingLWE.Params)

def hint (x : Int) : Int := if x%8<2 ∨ 6≤x%8 then 1 else 0
def bin (x j : Int) := ((x+4*j)/8)%65536

theorem exact (x δ : Int) (lo : -1≤δ) (hi : δ≤1) : bin (x+δ) (hint x)=bin x (hint x) := by
  unfold hint bin; split <;> congr 1 <;> omega

theorem periodic (x j : Int) : bin (x+524288) j=bin x j := by
  unfold bin; omega

theorem upper (x k : Int) :
    hint (x+8*k)=hint x ∧ bin (x+8*k) (hint x)=(bin x (hint x)+k)%65536 := by
  unfold bin hint; constructor
  · rw [show (x+8*k)%8=x%8 by omega]
  · split <;> omega

theorem lengths :
    8*1024*19+(8*1024-1)*19+13+1+16+1=311308 ∧
    (1024+1023)*19+10+1+16+1=38921 ∧ (1024+511)*19+9+1+16+1=29192 := by decide

def coarseHint (x : Int) : Int := if x%131072<32768 ∨ 98304≤x%131072 then 1 else 0
def coarseBin (x j : Int) := ((x+65536*j)/131072)%4

theorem coarse_exact (x δ : Int) (lo : -32768≤δ) (hi : δ≤32768) :
    coarseBin (x+δ) (coarseHint x)=coarseBin x (coarseHint x) := by
  unfold coarseBin coarseHint; split <;> congr 1 <;> omega

theorem coarse_sizes : 14*1024+1024+2047+11+1=17419 ∧
    12*1024+1024+2047+11+1=15371 ∧ 16*1024+1+16383=32768 := by decide

variable {R : Type} [CommRing R]
def row (u : Rˣ) (a : R) := -a*(↑(u⁻¹):R)
theorem cancellation (u : Rˣ) (a s e f : R) :
    (a*s+f)+row u a*((u:R)*s+e)=row u a*e+f := by
  have hh : row u a*(u:R) = -a := by simp [row,mul_assoc]
  linear_combination s*hh

def normalized (u : Rˣ) : R ≃ R where
  toFun := row u
  invFun x := -x*(u:R)
  left_inv x := by simp [row,mul_assoc]
  right_inv x := by simp [row,mul_assoc]

def idealPair (u : Rˣ) (pivotBody : R) : R × R ≃ R × R where
  toFun p := (normalized u p.1,p.2+normalized u p.1*pivotBody)
  invFun p := ((normalized u).symm p.1,p.2-p.1*pivotBody)
  left_inv p := by simp
  right_inv p := by simp

theorem uniform_header [Fintype R] (u : Rˣ) :
    (Cslib.Probability.PMF.uniformOfFintype R).map (normalized u)=
    Cslib.Probability.PMF.uniformOfFintype R :=
  Cslib.Probability.PMF.uniformOfFintype_map_equiv _
theorem uniform_real [Fintype R] (u : Rˣ) (s e f : R) :
    (Cslib.Probability.PMF.uniformOfFintype R).map
      (fun a ↦ (row u a,(a*s+f)+row u a*((u:R)*s+e))) =
    (Cslib.Probability.PMF.uniformOfFintype R).map (fun a ↦ (a,a*e+f)) := by
  have hh := congrArg (PMF.map (fun a : R ↦ (a,a*e+f))) (uniform_header u)
  rw [PMF.map_comp] at hh
  simpa only [cancellation,Function.comp_def,normalized,Equiv.coe_fn_mk,Equiv.toFun_as_coe] using hh

theorem uniform_ideal [Fintype R] (u : Rˣ) (y : R) :
    (Cslib.Probability.PMF.uniformOfFintype (R × R)).map (idealPair u y)=
    Cslib.Probability.PMF.uniformOfFintype (R × R) :=
  Cslib.Probability.PMF.uniformOfFintype_map_equiv _
end RingPrefixArithmetic
