import Mathlib.Tactic

namespace SelfProgrammedRow

/-- h is the uniform challenge header, b is a private guessed shift bit. -/
def trial {A : Type*} [AddGroup A] (g : A) (h : A) (b : Bool) : A :=
  h + (if b then g else 0)

def native {A : Type*} [AddGroup A] (g : A) (c : A → Bool) (a : A) : A :=
  a - (if c a then g else 0)

/-- An exact bijection, including for self-dependent c, between accepted
    header/coin pairs and native uniform headers. -/
def acceptedEquiv {A : Type*} [AddGroup A] (g : A) (c : A → Bool) :
    {p : A × Bool // p.2 = c (trial g p.1 p.2)} ≃ A where
  toFun p := trial g p.1.1 p.1.2
  invFun a := ⟨(native g c a, c a), by simp [native, trial]⟩
  left_inv := by
    rintro ⟨⟨h,b⟩, valid⟩
    change b = c (trial g h b) at valid
    apply Subtype.ext
    change (native g c (trial g h b), c (trial g h b)) = (h,b)
    simp only [native, ← valid]
    simp [trial]
  right_inv := by intro a; simp [trial,native]

theorem retained_header {A : Type*} [AddGroup A] (g : A) (c : A → Bool)
    (h : A) (b : Bool) (keep : b = c (trial g h b)) :
    native g c (trial g h b) = h := by
  simp only [native, ← keep]
  simp [trial]

end SelfProgrammedRow

namespace SelfProgrammedRow

/-- The inner challenge header can absorb a public coefficient chosen
    after the outer tentative header. -/
theorem affine_phase {K : Type*} [CommRing K] (s j d e m : K) :
    s*(j-d)+s*d+e+m=s*j+e+m := by ring

/-- The keep condition may inspect auxiliary values provided these were
    generated from the tentative native header using a fixed independent tape. -/
def innerOuterEquiv {A B : Type*} [AddGroup A] (g : A) (aux : A → B)
    (take : A → B → Bool) :
    {p : A × Bool // p.2 = take (trial g p.1 p.2) (aux (trial g p.1 p.2))} ≃ A :=
  acceptedEquiv g (fun a => take a (aux a))

end SelfProgrammedRow

namespace SelfProgrammedRow
/-- On the four Boolean points, multiplication by the first coordinate
    of an affine message has mixed finite difference equal to the other slope. -/
theorem mixed_rectangle {K : Type*} [CommRing K] (d a b : K) :
    (1:K)*(d+a+b)-1*(d+a)-0*(d+b)+0*d = b := by ring

theorem affine_rectangle {K : Type*} [CommRing K] (d a b : K) :
    (d+a+b)-(d+a)-(d+b)+d=0 := by ring

/-- In a half-modulus gadget column no four uniformly small signed
    errors can absorb its nonzero Boolean mixed difference. -/
theorem quarter_failure (s B k a b c d : Int) (hs : 0<s) (hB : 4*B < 4*s)
    (ha : -B ≤ a ∧ a ≤ B) (hb : -B ≤ b ∧ b ≤ B)
    (hc : -B ≤ c ∧ c ≤ B) (hd : -B ≤ d ∧ d ≤ B) :
    a-b-c+d ≠ 4*s+(8*s)*k := by
  intro eq
  by_cases hk : 0 ≤ k
  · have nn : 0 ≤ (8*s)*k := mul_nonneg (by omega) hk
    omega
  · have nn : 0 ≤ (8*s)*(-1-k) := mul_nonneg (by omega) (by omega)
    nlinarith

end SelfProgrammedRow
namespace SelectorGsw

/-- Row-vector action on (inactive block, active block, selector, sentinel). -/
def proj {K : Type*} [Ring K] (_ y bit _last : K) := ((0 : K),y,bit,-bit)
theorem selector_row {K : Type*} [Ring K] (b : Bool) (u : K) :
    let t : K := if b then 1 else 0
    proj ((1-t)*u) (t*u) t (-1) =
      (t*((1-t)*u), t*(t*u), t*t, t*(-1)) := by
  cases b <;> simp [proj]

/-- With a switch bit known to the reduction, fill the inactive public
    headers independently and reuse the original secret's LWE response. -/
theorem sample_body {K : Type*} [CommRing K] (b : Bool) (t a₀ a₁ a₂ e : K) :
    let bit : K := if b then 1 else 0
    (1-bit)*t*a₀ + bit*t*a₁ + bit*a₂ + e =
      t*(if b then a₁ else a₀) + e + bit*a₂ := by
  cases b <;> simp [add_right_comm]

end SelectorGsw

namespace CyclicProgrammedLaw

/-- Even the rejected proposals are independent of the success bit, after a private inversion
    of the guess. The permutations may use any fixed secret, errors and earlier transcript. -/
def splitTrial {X : Type*} (perm : Bool → X ≃ X) (test : X → Bool) :
    X × Bool ≃ X × Bool where
  toFun p := (perm p.2 p.1, p.2 == test (perm p.2 p.1))
  invFun p := let g := if p.2 then test p.1 else !(test p.1)
              ((perm g).symm p.1, g)
  left_inv := by
    rintro ⟨x,g⟩
    cases g <;> simp only <;> split <;> rename_i h <;> simp_all
  right_inv := by
    rintro ⟨y,b⟩
    cases b <;> simp

/-- Shifting the first header by a fixed guess and the second by a function of the resulting
    first header is a permutation. -/
def headerPair {A B : Type*} [AddGroup A] [AddGroup B] (shift : A) (coeff : A → B) :
    A × B ≃ A × B where
  toFun p := (p.1 + shift, p.2 - coeff (p.1 + shift))
  invFun p := (p.1 - shift, p.2 + coeff p.1)
  left_inv := by rintro ⟨h,j⟩; simp
  right_inv := by rintro ⟨a,b⟩; simp

/-- Ideal-body translation, evaluated after the complete tentative header, without using the
    still-uninspected outer ideal response. -/
def shiftedBody {X K : Type*} [AddGroup K] (off : X → K) : X × K ≃ X × K where
  toFun p := (p.1, p.2 + off p.1)
  invFun p := (p.1, p.2 - off p.1)
  left_inv := by rintro ⟨x,k⟩; simp
  right_inv := by rintro ⟨x,k⟩; simp

def Tape (X : Type*) : Nat → Type _
  | 0 => PUnit
  | n+1 => (X × Bool) × Tape X n

def nextEquiv {A B : Type*} (e : A ≃ A) (tail : A → B ≃ B) : A × B ≃ A × B where
  toFun p := (e p.1, tail (e p.1) p.2)
  invFun p := (e.symm p.1, (tail p.1).symm p.2)
  left_inv := by rintro ⟨x,xs⟩; simp
  right_inv := by rintro ⟨x,xs⟩; simp

/-- Finite adaptive coin tapes are permuted, with the same prefix on the inverse path. -/
def adaptiveTape {X S : Type*} (step : S → X × Bool ≃ X × Bool)
    (advance : S → X × Bool → S) : (n : Nat) → S → Tape X n ≃ Tape X n :=
  Nat.rec (motive := fun n => S → Tape X n ≃ Tape X n)
    (fun _ => Equiv.refl _)
    (fun _ prev st => nextEquiv (step st) (fun y => prev (advance st y)))

/-- A radix split is bijective on fixed-width uniform residues, for arbitrary factor sizes. -/
def digits {d m : Nat} (hd : 0 < d) : Fin d × Fin m ≃ Fin (d*m) where
  toFun p := ⟨p.1.val + d*p.2.val, by
    have h := Nat.mul_le_mul_left d (Nat.succ_le_of_lt p.2.isLt)
    have hl := p.1.isLt
    simp only [Nat.mul_succ] at h
    omega⟩
  invFun z := (⟨z.val % d, Nat.mod_lt _ hd⟩, ⟨z.val / d,
    (Nat.div_lt_iff_lt_mul hd).mpr (by simpa only [Nat.mul_comm m d] using z.isLt)⟩)
  left_inv := by
    rintro ⟨a,b⟩
    apply Prod.ext <;> apply Fin.ext
    · simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt a.isLt]
    · simp [Nat.add_mul_div_left, Nat.div_eq_of_lt a.isLt, hd]
  right_inv := by intro z; apply Fin.ext; exact Nat.mod_add_div _ _

/-- Carry and high header digits disappear modulo d*m; the signed dither may use any fixed
    translate of the d residue representatives. -/
theorem liftedColumn (d m a t h k e u carry : Int) :
    d*(t*h+e-m*carry)+a*(h+m*k)+u -
      ((a+d*t)*(h+m*k)+d*e+u) = (d*m)*(-carry-t*k) := by ring

/-- Vanishing mixed differences of the scalar m and the product s_i m on every
    i,j rectangle force every affine slope to vanish. -/
theorem constantScalarSlopes {K I : Type*} [CommRing K] [Nontrivial I]
    (d : K) (slope : I → K) (atPair : I → I → K)
    (aff : ∀ i j, i ≠ j → atPair i j-(d+slope i)-(d+slope j)+d=0)
    (prodAff : ∀ i j, i ≠ j → atPair i j-(d+slope i)=0) :
    ∀ j, slope j = 0 := by
  intro j
  obtain ⟨i, hij⟩ := exists_ne j
  linear_combination prodAff i j hij - aff i j hij

end CyclicProgrammedLaw


namespace DigitSmoothing

theorem square {K : Type*} [CommRing K] (a b x z : K) :
  (a^2+b^2)*(b^2*x^2+a^2*(z-x)^2) =
    a^2*b^2*z^2+((a^2+b^2)*x-a^2*z)^2 := by ring

set_option exponentiation.threshold 600 in
theorem illustrativeColumns :
    2632016 * 5 * (2^183 + 1) * 2^160 < 2 * 2^(366:Nat) := by decide

theorem oddOrderCenter (h t k : Int) (pos : 0<h) :
    (h*(2*t+1)+k*(2*h))%(2*h)=h := by
  rw [show h*(2*t+1)+k*(2*h)=h+(t+k)*(2*h) by ring, Int.add_mul_emod_self_right]
  exact Int.emod_eq_of_lt (by omega) (by omega)

theorem evenOrderCenter (h t k : Int) : (h*t+k*h)%h=0 := by
  rw [show h*t+k*h = (t+k)*h by ring]
  simp

end DigitSmoothing
