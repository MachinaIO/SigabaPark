import Mathlib.Data.Int.GCD
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

set_option autoImplicit true

/-! An explicit integer basis for a primitive zero-sum normal congruence lattice. -/
noncomputable section
namespace SigabaNeo.Wall1.AffineNormalLattice

/-- Pairing with the zero-sum normal (u,v,-u-v). -/
def normalDot (u v : ℤ) (x : Fin 3 → ℤ) : ℤ :=
  u*x 0 + v*x 1 + (-u-v)*x 2

/-- Coefficients in the basis e=(1,1,1), f=(v,-u,0), q*g=q*(a,b,0). -/
def encode (u v a b q : ℤ) (c : Fin 3 → ℤ) : Fin 3 → ℤ :=
  ![c 0 + c 1*v + c 2*q*a, c 0 - c 1*u + c 2*q*b, c 0]

/-- Every encoded vector satisfies the congruence. -/
theorem normalDot_encode (u v a b q : ℤ) (hab : u*a+v*b=1) (c : Fin 3 → ℤ) :
    normalDot u v (encode u v a b q c) = q*c 2 := by
  simp [normalDot, encode]
  linear_combination (q*c 2)*hab

/-- The second coefficient is recovered by the complementary Bezout pairing. -/
theorem transverse_encode (u v a b q : ℤ) (hab : u*a+v*b=1) (c : Fin 3 → ℤ) :
    b*((encode u v a b q c) 0 - (encode u v a b q c) 2) -
      a*((encode u v a b q c) 1 - (encode u v a b q c) 2) = c 1 := by
  simp [encode]
  linear_combination c 1*hab

/-- The three integer basis coefficients are unique when q is nonzero. -/
theorem encode_injective (u v a b q : ℤ) (hab : u*a+v*b=1) (hq : q ≠ 0) :
    Function.Injective (encode u v a b q) := by
  intro c d he
  have h0 : c 0 = d 0 := congrFun he 2
  have h1 := congrArg (fun x : Fin 3 → ℤ ↦ b*(x 0-x 2)-a*(x 1-x 2)) he
  rw [transverse_encode u v a b q hab, transverse_encode u v a b q hab] at h1
  have h2 := congrArg (normalDot u v) he
  rw [normalDot_encode u v a b q hab, normalDot_encode u v a b q hab] at h2
  have h2' : c 2 = d 2 := mul_left_cancel₀ hq h2
  funext i
  fin_cases i <;> assumption

/-- Divisibility by q is exactly membership in the explicit integer basis image. -/
theorem dvd_normalDot_iff_exists_encode (u v a b q : ℤ) (hab : u*a+v*b=1)
    (x : Fin 3 → ℤ) :
    q ∣ normalDot u v x ↔ ∃ c : Fin 3 → ℤ, encode u v a b q c = x := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨![x 2, b*(x 0-x 2)-a*(x 1-x 2), r], ?_⟩
    funext i
    fin_cases i
    · simp [encode]
      dsimp [normalDot] at hr
      linear_combination (x 0-x 2)*hab - a*hr
    · simp [encode]
      dsimp [normalDot] at hr
      linear_combination (x 1-x 2)*hab - b*hr
    · rfl
  · rintro ⟨c, rfl⟩
    rw [normalDot_encode u v a b q hab]
    exact dvd_mul_right _ _

/-- Primitive normal coordinates always admit the required Bezout coefficients. -/
theorem exists_bezout (u v : ℤ) (hg : Int.gcd u v = 1) :
    ∃ a b : ℤ, u*a+v*b=1 := by
  refine ⟨Int.gcdA u v, Int.gcdB u v, ?_⟩
  have h := Int.gcd_eq_gcd_ab u v
  simpa only [hg, Int.natCast_one] using h.symm

/-- Every congruence vector has one and only one integer coefficient triple. -/
theorem existsUnique_encode (u v a b q : ℤ) (hab : u*a+v*b=1) (hq : q ≠ 0)
    (x : Fin 3 → ℤ) (hx : q ∣ normalDot u v x) :
    ∃! c : Fin 3 → ℤ, encode u v a b q c = x := by
  obtain ⟨c, hc⟩ := (dvd_normalDot_iff_exists_encode u v a b q hab x).mp hx
  exact ⟨c, hc, fun d hd ↦ encode_injective u v a b q hab hq (hd.trans hc.symm)⟩

end SigabaNeo.Wall1.AffineNormalLattice
#print axioms SigabaNeo.Wall1.AffineNormalLattice.encode_injective
#print axioms SigabaNeo.Wall1.AffineNormalLattice.existsUnique_encode
#print axioms SigabaNeo.Wall1.AffineNormalLattice.exists_bezout
