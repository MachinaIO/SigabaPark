import SigabaNeoStd.Lattices.RingLWEInst
import Mathlib
namespace RootCharacterRelease
open Cslib.Probability
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
abbrev Coins (F : Type) [Field F] := Fˣ × Fˣ

def squarePair (a r s : F) : F × F := (r^2+a*s^2,2*r*s)
def payload (a : F) (u : Coins F) : F × F :=
  if (u.1:F)^2=a*(u.2:F)^2 then (1,0) else squarePair a u.1 u.2
def scale (v : F) (w : F × F) := (v*w.1,v*w.2)
def enc (a γ : F) (b : Bool) (u : Coins F) := scale (if b then γ else 1) (payload a u)
def eval (z : F) (w : F × F) := w.1+w.2*z
noncomputable def law (a γ : F) (b : Bool) := (Cslib.Probability.PMF.uniformOfFintype (Coins F)).map (enc a γ b)

theorem opens (a z : F) (hz : z^2=a) (u : Coins F) :
    ∃ t : F,t≠0 ∧ eval z (payload a u)=t^2 := by
  unfold payload
  split
  · exact ⟨1,one_ne_zero,by simp [eval]⟩
  · rename_i hn
    refine ⟨(u.1:F)+(u.2:F)*z,?_,?_⟩
    · intro h
      apply hn
      rw [← hz]
      linear_combination ((u.1:F)-(u.2:F)*z)*h
    · simp only [eval,squarePair]; rw [← hz]; ring

theorem decode (a γ z : F) (hn : ¬IsSquare γ) (hz : z^2=a) (b : Bool) (u : Coins F) :
    quadraticChar F (eval z (enc a γ b u))=if b then -1 else 1 := by
  obtain ⟨t,h0,he⟩ := opens a z hz u
  have hs (x : F) (w : F × F) : eval z (scale x w)=x*eval z w := by simp [eval,scale]; ring
  cases b
  · change quadraticChar F (eval z (scale 1 _))=1
    rw [hs,one_mul,he,quadraticChar_sq_one' h0]
  · change quadraticChar F (eval z (scale γ _))= -1
    rw [hs,he,map_mul,quadraticChar_sq_one' h0,mul_one,quadraticChar_neg_one_iff_not_isSquare.mpr hn]

theorem no_norm (a : F) (no : ¬IsSquare a) (u : Coins F) : (u.1:F)^2≠a*(u.2:F)^2 := by
  intro h
  apply no
  refine ⟨(u.1:F)/(u.2:F),?_⟩
  field_simp; linear_combination -h

theorem ratio_square (a γ : F) (na : ¬IsSquare a) (ng : ¬IsSquare γ) :
    ∃ t : Fˣ,a*(t:F)^2=γ := by
  have az : a≠0 := by intro he; exact na (he ▸ IsSquare.zero)
  have gz : γ≠0 := by intro he; exact ng (he ▸ IsSquare.zero)
  have hh : quadraticChar F (γ/a) * quadraticChar F a = quadraticChar F γ := by
    rw [← map_mul,div_mul_cancel₀ _ az]
  rw [quadraticChar_neg_one_iff_not_isSquare.mpr na,
    quadraticChar_neg_one_iff_not_isSquare.mpr ng] at hh
  obtain ⟨x,hx⟩ := (quadraticChar_one_iff_isSquare (div_ne_zero gz az)).mp (by linarith)
  have h : γ=a*x^2 := by field_simp at hx; linear_combination hx
  have xz : x≠0 := by intro he; simp [he] at h; exact gz h
  exact ⟨Units.mk0 x xz,h.symm⟩

def swap (a t : Fˣ) : Coins F ≃ Coins F where
  toFun u := (a*t*u.2,t*u.1)
  invFun u := (t⁻¹*u.2,(a*t)⁻¹*u.1)
  left_inv := by intro x; apply Prod.ext <;> simp <;> group
  right_inv := by intro x; apply Prod.ext <;> simp <;> group

theorem exact_no (a γ : F) (na : ¬IsSquare a) (ng : ¬IsSquare γ) : law a γ false=law a γ true := by
  have az : a≠0 := by intro he; exact na (he ▸ IsSquare.zero)
  obtain ⟨t,ht⟩ := ratio_square a γ na ng
  let s := swap (Units.mk0 a az) t
  have hx (u : Coins F) : enc a γ false (s u)=enc a γ true u := by
    have p (w : Coins F) : payload a w=squarePair a w.1 w.2 := if_neg (no_norm a na w)
    change scale 1 (payload a (s u))=scale γ (payload a u)
    rw [p,p,← ht]
    apply Prod.ext <;> simp [scale,s,swap,squarePair] <;> ring
  have hh := congrArg (PMF.map (enc a γ false)) (Cslib.Probability.PMF.uniformOfFintype_map_equiv s)
  rw [PMF.map_comp] at hh
  exact hh.symm.trans (congrArg (fun f ↦ (Cslib.Probability.PMF.uniformOfFintype (Coins F)).map f)
    (funext hx))

local instance : Fact (Nat.Prime 257) := ⟨by norm_num⟩
theorem three_nonsquare : ¬IsSquare (3:ZMod 257) := by
  rw [ZMod.euler_criterion 257 (by decide)]
  decide
theorem params : 256*256=2^16 ∧ 2*9=18 ∧ (3:ZMod 257)^128=256 := by decide

abbrev FF := ZMod 257
def fromByte (i : Fin 256) : FFˣ :=
  Units.mk0 ((i.val+1:Nat):FF) (by
    intro h; have hd := (ZMod.natCast_eq_zero_iff _ _).mp h; omega)
theorem positive_val (u : FFˣ) : 0<(u:FF).val := by
  have h := u.ne_zero
  by_contra! hh
  exact h ((ZMod.val_eq_zero _).mp (by omega))
def byteEquiv : Fin 256 ≃ FFˣ where
  toFun := fromByte
  invFun u := ⟨(u:FF).val-1,by
    have := ZMod.val_lt (u:FF); have := positive_val u; omega⟩
  left_inv := by
    intro i; apply Fin.ext
    change (((i.val+1:Nat):FF).val-1)=i.val
    rw [ZMod.val_natCast,Nat.mod_eq_of_lt (by omega)]; omega
  right_inv := by
    intro u; apply Units.ext; apply ZMod.val_injective
    change (((((u:FF).val-1)+1:Nat):FF).val)=(u:FF).val
    have hp := positive_val u
    have hz : (u:FF).val-1+1=(u:FF).val := by omega
    rw [hz,ZMod.val_natCast,Nat.mod_eq_of_lt (ZMod.val_lt _)]

theorem byte_law : (Cslib.Probability.PMF.uniformOfFintype (Fin 256 × Fin 256)).map
    (byteEquiv.prodCongr byteEquiv) = Cslib.Probability.PMF.uniformOfFintype (Coins FF) :=
  Cslib.Probability.PMF.uniformOfFintype_map_equiv _

end RootCharacterRelease
