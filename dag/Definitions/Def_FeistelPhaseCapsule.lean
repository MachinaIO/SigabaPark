import Mathlib.Tactic
namespace StatisticGuess

/-- A global feedback statistic can determine a whole vector of matrix shifts. -/
def accepted {X Z : Type*} (p : Z → X ≃ X) (stat : X → Z) :
    {a : X × Z // a.2 = stat (p a.2 a.1)} ≃ X where
  toFun a := p a.val.2 a.val.1
  invFun x := ⟨((p (stat x)).symm x, stat x), by simp⟩
  left_inv := by
    rintro ⟨⟨x,z⟩,hz⟩
    change z = stat (p z x) at hz
    apply Subtype.ext
    change ((p (stat (p z x))).symm (p z x),stat (p z x)) = (x,z)
    rw [← hz]
    simp
  right_inv := by intro x; simp

/-- Exact equal-multiplicity rule for a typical set of statistic values. -/
def retained {X Z : Type*} (p : Z → X ≃ X) (stat : X → Z) (allowed : Set Z) :
    {a : X × Z // a.2 = stat (p a.2 a.1) ∧ a.2 ∈ allowed} ≃
      {x : X // stat x ∈ allowed} where
  toFun a := ⟨p a.val.2 a.val.1, a.property.1 ▸ a.property.2⟩
  invFun x := ⟨((p (stat x.val)).symm x.val,stat x.val), by simp [x.property]⟩
  left_inv := by
    rintro ⟨⟨x,z⟩,hz,mem⟩
    change z = stat (p z x) at hz
    apply Subtype.ext
    change ((p (stat (p z x))).symm (p z x),stat (p z x)) = (x,z)
    rw [← hz]
    simp
  right_inv := by intro x; apply Subtype.ext; simp
def feistel {G : Type*} [AddCommGroup G] (f : G → G) : G × G ≃ G × G where
  toFun z := (z.2+f z.1,z.1)
  invFun r := (r.2,r.1-f r.2)
  left_inv := by rintro ⟨u,v⟩; simp
  right_inv := by rintro ⟨u,v⟩; simp

/-- For an additive group of characteristic 2 subtraction is XOR. -/
theorem messageShares {G : Type*} [AddCommGroup G] (f : G → G) (u v : G) :
  ((feistel f (u,v)).1-u)+((feistel f (u,v)).2-v)=f u := by
  change (v+f u-u)+(u-v)=f u
  abel
end StatisticGuess

namespace FeistelPhaseCapsule

/-- q=8s; transmit one of four centers, indexed by floor((h+s)/(2s)) modulo four.
    The formula below uses its integer lift. -/
def center (s h : Int) := 2*s*((h+s)/(2*s))

def openBit (s h y : Int) : Bool := decide (4*s ≤ (y-h+2*s)%(8*s))

theorem centerResidual {s : Int} (hs : 0 < s) (h : Int) :
    -s ≤ h-center s h ∧ h-center s h < s := by
  have key := Int.emod_add_mul_ediv (h+s) (2*s)
  have lo := Int.emod_nonneg (h+s) (by omega : (2*s : Int) ≠ 0)
  have hi := Int.emod_lt_of_pos (h+s) (by omega : 0 < (2*s : Int))
  unfold center
  omega

theorem recover {s : Int} (hs : 0 < s) (h e : Int) (b : Bool)
    (elo : -s ≤ e) (ehi : e ≤ s) :
    openBit s (center s h) (h+e+(if b then 4*s else 0)) = b := by
  have hr := centerResidual hs h
  cases b <;> simp only [openBit, Bool.false_eq_true, ite_false, ite_true, add_zero] <;>
    rw [Int.emod_eq_of_lt (by omega) (by omega)] <;> simp <;> omega

theorem centerPeriodic (s h y k : Int) :
    openBit s (h+k*(8*s)) y = openBit s h y := by
  unfold openBit
  rw [show y-(h+k*(8*s))+2*s = (y-h+2*s)+(-k)*(8*s) by ring,
      Int.add_mul_emod_self_right]

/-- Nonzero conditional mask on one NO affine branch flips the tag at fixed public R. -/
theorem cosetMask {V : Type*} [AddCommGroup V] (R : V →+ ZMod 2) (T : V →+ ZMod 2)
    (u v : V) (hR : R v=0) (hT : T v=1) :
    R (u+v)=R u ∧ T (u+v)=T u+1 := by simp [hR,hT]

theorem packetCounts :
    10*161*8 = 12880 ∧ 12880+2*(128+1)=13138 ∧
    2*(2^10-1)*2^149 < 2^(160:Nat) := by decide

end FeistelPhaseCapsule
