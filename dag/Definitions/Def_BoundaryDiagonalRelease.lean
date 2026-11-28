import SigabaNeoStd.Lattices.RingLWEInst
import Mathlib.Tactic

namespace BoundaryDiagonalRelease
open Cslib.Probability
variable {V I R : Type} [CommRing R]
def shift (t : V → R) (s : R) := fun v ↦ s+t v
def slope (f : (V → R) → R) (t : V → R) := f (shift t 1)-f t
def Admissible (f : (V → R) → R) :=
  ∀ t s, f (shift t s)=f t+slope f t*s

/-- Even allowing the header function and additive correction to depend
on the original header, the payload increment is forced by s=0 and s=1. -/
theorem criterion (f : (V → R) → R) (u : V) : Admissible f ↔
    ∃ (header extra : (V → R) → R → R), ∀ t a s,
      a*s+extra t a=header t a*(s+t u)+f (shift t s) := by
  constructor
  · intro h
    refine ⟨fun t a ↦ a-slope f t,fun t a ↦ (a-slope f t)*t u+f t,?_⟩
    intro t a s; rw [h]; ring
  · rintro ⟨a,b,hh⟩ t s
    have h0 := hh t 0 0
    have h1 := hh t 0 1
    have hs := hh t 0 s
    have hz : shift t 0=t := by funext v; simp [shift]
    rw [hz] at h0
    simp only [zero_mul,zero_add] at h0 h1 hs
    have ha : slope f t= -a t 0 := by unfold slope; linear_combination h0-h1
    rw [ha]; linear_combination h0-hs

theorem difference_product (v w x : V) :
    Admissible (fun k : V → R ↦ (k v-k w)*k x) := by
  intro t s
  simp only [slope,shift]
  ring

theorem raw_square_boundary (u : V) (h : (2:R)≠0) :
    ¬Admissible (fun k : V → R ↦ k u*k u) := by
  intro hh
  have hz := hh (fun _ ↦ 0) 2
  simp only [slope,shift,add_zero,mul_zero,one_mul,sub_zero,zero_add] at hz
  apply h
  linear_combination hz

abbrev Bank (I R : Type) := (I → R) × (I → R)
abbrev Coins (V I R : Type) := (V → R) × (I → R)
def rowHeader (f : I → (V → R) → R) (t : V → R) (a : I → R) :=
  fun i ↦ a i-slope (f i) t

/-- The mask-dependent header offset is applied after the keys are
shifted. Its inverse first recovers the original shifts. -/
def realPerm (f : I → (V → R) → R) (s : R) : Coins V I R ≃ Coins V I R where
  toFun x := (shift x.1 s,rowHeader f x.1 x.2)
  invFun x := (fun v ↦ x.1 v-s,fun i ↦ x.2 i+slope (f i) (fun v ↦ x.1 v-s))
  left_inv := by intro x; ext <;> simp [shift,rowHeader]
  right_inv := by intro x; ext <;> simp [shift,rowHeader]

def corr (src : I → V) (f : I → (V → R) → R) (t : V → R) (a : I → R) :=
  fun i ↦ a i*t (src i)+f i t

def idealPerm (src : I → V) (f : I → (V → R) → R) (t : V → R) : Bank I R ≃ Bank I R where
  toFun x := (rowHeader f t x.1,fun i ↦ x.2 i+corr src f t (rowHeader f t x.1) i)
  invFun x := (fun i ↦ x.1 i+slope (f i) t,fun i ↦ x.2 i-corr src f t x.1 i)
  left_inv := by intro x; ext <;> simp [rowHeader,corr]
  right_inv := by intro x; ext <;> simp [rowHeader,corr]

def sample (s : R) (e a : I → R) : Bank I R := (a,fun i ↦ a i*s+e i)
def issuer (src : I → V) (f : I → (V → R) → R) (e : I → R) (x : Coins V I R) :
    Bank I R := (x.2,fun i ↦ x.2 i*x.1 (src i)+e i+f i x.1)

theorem rows_agree (src : I → V) (f : I → (V → R) → R) (h : ∀ i,Admissible (f i))
    (s : R) (e : I → R) (x : Coins V I R) :
    idealPerm src f x.1 (sample s e x.2)=issuer src f e (realPerm f s x) := by
  apply Prod.ext
  · rfl
  · funext i
    simp only [idealPerm,realPerm,sample,issuer,Equiv.coe_fn_mk,corr,rowHeader,
      h i x.1 s]
    simp only [shift]; ring

theorem real_law [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Fintype R]
    (src : I → V) (f : I → (V → R) → R) (h : ∀ i,Admissible (f i)) (s : R) (e : I → R) :
    (PMF.uniformOfFintype (Coins V I R)).map
      (fun x ↦ idealPerm src f x.1 (sample s e x.2)) =
    (PMF.uniformOfFintype (Coins V I R)).map (issuer src f e) := by
  simp_rw [rows_agree src f h]
  simpa only [PMF.map_comp,Function.comp_def] using congrArg (PMF.map (issuer src f e))
    (PMF.uniformOfFintype_map_equiv (realPerm f s))

theorem ideal_law [Fintype I] [DecidableEq I] [Fintype R]
    (src : I → V) (f : I → (V → R) → R) (t : V → R) :
    (PMF.uniformOfFintype (Bank I R)).map (idealPerm src f t)=PMF.uniformOfFintype _ :=
  PMF.uniformOfFintype_map_equiv _

/-- A derived key can itself serve as a source if its diagonal slope is
invertible. The unknown-secret coefficient must span the full header ring. -/
theorem unit_necessary (a b : R) (h : ∀ z, ∃ y, y*a+b=z) : IsUnit a := by
  obtain ⟨y,hy⟩ := h (1+b)
  have he : y*a=1 := add_right_cancel hy
  exact ⟨⟨a,y,(mul_comm a y).trans he,he⟩,rfl⟩

theorem invariant_offset_source (u v w : V) :
    Admissible (fun k : V → R ↦ k u+(k v-k w)^2) ∧
    ∀ t,slope (fun k : V → R ↦ k u+(k v-k w)^2) t=1 := by
  constructor
  · intro t s; simp only [shift,slope]; ring
  · intro t; simp only [shift,slope]; ring

/-- The header permutation for a unit source slope and affine target slope. -/
def headerEquiv (a : Rˣ) (b : R) : R ≃ R where
  toFun z := (z-b)*↑(a⁻¹)
  invFun y := y*↑a+b
  left_inv := by intro z; simp [mul_assoc]
  right_inv := by intro y; simp [mul_assoc]

def headerVector (a : (V → R) → I → Rˣ) (f : I → (V → R) → R) (t : V → R) :
    (I → R) ≃ (I → R) :=
  Equiv.piCongrRight (fun i ↦ headerEquiv (a t i) (slope (f i) t))

def symbolicCoins (a : (V → R) → I → Rˣ) (f : I → (V → R) → R) (s : R) :
    Coins V I R ≃ Coins V I R where
  toFun x := (shift x.1 s,headerVector a f x.1 x.2)
  invFun x := (fun v ↦ x.1 v-s,(headerVector a f (fun v ↦ x.1 v-s)).symm x.2)
  left_inv := by intro x; simp [shift]
  right_inv := by
    intro x; apply Prod.ext
    · funext v; change s+(x.1 v-s)=x.1 v; abel
    · exact (headerVector a f _).apply_symm_apply _

def symbolicBank (a : (V → R) → I → Rˣ) (g f : I → (V → R) → R) (t : V → R) :
    Bank I R ≃ Bank I R where
  toFun x := (headerVector a f t x.1,
    fun i ↦ x.2 i+(headerVector a f t x.1) i*g i t+f i t)
  invFun x := ((headerVector a f t).symm x.1, fun i ↦ x.2 i-f i t-x.1 i*g i t)
  left_inv := by intro x; apply Prod.ext <;> simp
  right_inv := by intro x; apply Prod.ext <;> simp

def symbolicIssue (g f : I → (V → R) → R) (e : I → R) (x : Coins V I R) :
    Bank I R := (x.2,fun i ↦ x.2 i*g i x.1+e i+f i x.1)

theorem symbolic_agree (a : (V → R) → I → Rˣ) (g f : I → (V → R) → R)
    (hg : ∀ i,Admissible (g i)) (ha : ∀ t i,slope (g i) t=↑(a t i))
    (hf : ∀ i,Admissible (f i)) (s : R) (e : I → R) (x : Coins V I R) :
    symbolicBank a g f x.1 (sample s e x.2)=symbolicIssue g f e (symbolicCoins a f s x) := by
  apply Prod.ext
  · rfl
  · funext i
    let A := (headerVector a f x.1 x.2) i
    have hA : A*(↑(a x.1 i):R)+slope (f i) x.1=x.2 i :=
      (headerEquiv (a x.1 i) (slope (f i) x.1)).left_inv _
    change x.2 i*s+e i+A*g i x.1+f i x.1 =
      A*g i (shift x.1 s)+e i+f i (shift x.1 s)
    rw [hg i x.1 s,hf i x.1 s,ha]
    linear_combination -s*hA

theorem symbolic_real [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Fintype R]
    (a : (V → R) → I → Rˣ) (g f : I → (V → R) → R)
    (hg : ∀ i,Admissible (g i)) (ha : ∀ t i,slope (g i) t=↑(a t i))
    (hf : ∀ i,Admissible (f i)) (s : R) (e : I → R) :
    (PMF.uniformOfFintype (Coins V I R)).map
      (fun x ↦ symbolicBank a g f x.1 (sample s e x.2)) =
    (PMF.uniformOfFintype (Coins V I R)).map (symbolicIssue g f e) := by
  simp_rw [symbolic_agree a g f hg ha hf]
  simpa only [PMF.map_comp,Function.comp_def] using congrArg (PMF.map (symbolicIssue g f e))
    (PMF.uniformOfFintype_map_equiv (symbolicCoins a f s))

theorem symbolic_ideal [Fintype I] [DecidableEq I] [Fintype R]
    (a : (V → R) → I → Rˣ) (g f : I → (V → R) → R) (t : V → R) :
    (PMF.uniformOfFintype (Bank I R)).map (symbolicBank a g f t)=PMF.uniformOfFintype _ :=
  PMF.uniformOfFintype_map_equiv _

end BoundaryDiagonalRelease
