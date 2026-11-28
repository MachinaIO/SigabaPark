import Mathlib.Tactic

namespace GuardedShiftDecode

/-- Quarter-modulus shift units; the two message codewords are 0 and 2.
    The pre-rounding phase is taken modulo 8s. -/
def bitCode (b : Bool) : Int := if b then 2 else 0

def decode (s raw : Int) : Bool := decide (4*s ≤ (raw+s) % (8*s))

theorem cancellation (s y e : Int) (b : Bool) :
    y+(2*s)*(bitCode b-y/(2*s))+e =
    y%(2*s)+(2*s)*bitCode b+e := by
  have h := Int.emod_add_mul_ediv y (2*s)
  linear_combination -h

theorem correct (s y e : Int) (b : Bool) (hs : 0<s)
    (lower : -s ≤ e) (upper : e ≤ s) :
    decode s (y+(2*s)*(bitCode b-y/(2*s))+e) = b := by
  rw [cancellation]
  have pos : 0 < 2*s := by omega
  have h₁ := Int.emod_nonneg y (by omega : 2*s ≠ 0)
  have h₂ := Int.emod_lt_of_pos y pos
  cases b <;> simp only [bitCode, Bool.false_eq_true, ite_false, ite_true,
    mul_zero, add_zero, decode] <;>
    rw [Int.emod_eq_of_lt (by omega) (by omega)] <;> simp <;> omega

theorem periodic (s t raw : Int) : decode s (raw + t*(8*s)) = decode s raw := by
  unfold decode
  rw [show raw+t*(8*s)+s = (raw+s)+t*(8*s) by ring, Int.add_mul_emod_self_right]

end GuardedShiftDecode

namespace GuardedShiftDecode

/-- If one extra integer noise unit is allowed, the same raw phase can
    represent both messages, so the uniform radius q/8 is sharp. -/
theorem ambiguity (s : Int) (hs : 0<s) :
    ∃ (r₀ r₁ e₀ e₁ : Int),
      (0 ≤ r₀ ∧ r₀ < 2*s) ∧ (0 ≤ r₁ ∧ r₁ < 2*s) ∧
      (-s-1 ≤ e₀ ∧ e₀ ≤ s+1) ∧ (-s-1 ≤ e₁ ∧ e₁ ≤ s+1) ∧
      r₀+e₀ = 4*s+r₁+e₁ := by
  exact ⟨2*s-1,0,s+1,-s,by omega⟩

theorem public_residue (s y f e : Int) :
    (y+(2*s)*f+e)%(2*s) = (y+e)%(2*s) := by
  rw [show y+(2*s)*f+e = (y+e)+f*(2*s) by ring, Int.add_mul_emod_self_right]

end GuardedShiftDecode

namespace GuardedShiftDecode

def optimisticEnvelope (l : Nat) := 8 * (2*l^5)^128

private theorem raiseWidth {l a b : Nat} (cap : optimisticEnvelope l ≤ 2^l)
    (ha : a ≤ l) (step : 2^b < optimisticEnvelope a) : b+1 ≤ l := by
  by_contra! bad
  have h : l ≤ b := by omega
  have hm : optimisticEnvelope a ≤ optimisticEnvelope l := by
    unfold optimisticEnvelope
    gcongr
  have he : 2^l ≤ 2^b := Nat.pow_le_pow_right (by decide) h
  omega

set_option exponentiation.threshold 16000
set_option maxRecDepth 30000
theorem envelope_width {l : Nat} (pos : 1 ≤ l)
    (cap : optimisticEnvelope l ≤ 2^l) : 8484 ≤ l := by
  have h1 := raiseWidth (b:=130) cap pos (by decide)
  have h2 := raiseWidth (b:=4632) cap h1 (by decide)
  have h3 := raiseWidth (b:=7924) cap h2 (by decide)
  have h4 := raiseWidth (b:=8420) cap h3 (by decide)
  have h5 := raiseWidth (b:=8476) cap h4 (by decide)
  have h6 := raiseWidth (b:=8482) cap h5 (by decide)
  exact raiseWidth (b:=8483) cap h6 (by decide)

theorem outer_body_over_cap {l : Nat} (pos : 1 ≤ l)
    (cap : optimisticEnvelope l ≤ 2^l) : 2^32 < 8*l^4 := by
  have h := envelope_width pos cap
  calc
    2^32 < 8*(8484:Nat)^4 := by decide
    _ ≤ 8*l^4 := by gcongr

end GuardedShiftDecode

namespace GuardedShiftDecode

/-- Scalar output, with the master precontracted to a fixed-width row. -/
theorem fixedWidthRow {l : Nat} (pos : 1 ≤ l) (cap : optimisticEnvelope l ≤ 2^l) :
    2^133 < 8*l^10 := by
  have bound := envelope_width pos cap
  calc
    2^133 < 8*(8484:Nat)^10 := by decide
    _ ≤ 8*l^10 := by gcongr

/-- Scalar output, transmitting the literal fixed-width master matrix in the constraint. -/
theorem fixedWidthMaster {l : Nat} (pos : 1 ≤ l) (cap : optimisticEnvelope l ≤ 2^l) :
    2^146 < 8*l^11 := by
  have bound := envelope_width pos cap
  calc
    2^146 < 8*(8484:Nat)^11 := by decide
    _ ≤ 8*l^11 := by gcongr

section Anchor
variable {W I : Type*}

/-- The representative compression needs only a public reconstruction rule on legal rows.
    This covers a point representative as well as public linear combinations. -/
theorem recover {a : I → W} {pubPart privatePart target : W → ZMod 2}
    {reconstruct : W → (I → ZMod 2) → ZMod 2}
    (correctRows : ∀ w, pubPart w + privatePart w = target w)
    (spanRows : ∀ w, reconstruct w (fun i => privatePart (a i)) = privatePart w) (w : W) :
    pubPart w + reconstruct w (fun i => privatePart (a i)) = target w := by
  rw [spanRows, correctRows]

/-- Equality of the entire correction vector on a false statement. -/
theorem simAll {a : I → W} {pubPart privatePart : W → ZMod 2}
    (correctRows : ∀ w, pubPart w + privatePart w = 0) :
    (fun i => privatePart (a i)) = fun i => -pubPart (a i) := by
  funext i
  have h := correctRows (a i)
  linear_combination h

/-- Even on a satisfiable statement, when all selected anchor targets vanish, public data
    reconstruct the target at an arbitrary witness on the correctness event. -/
theorem publicRecovery {a : I → W} {pub priv target : W → ZMod 2}
    {rec : W → (I → ZMod 2) → ZMod 2} (hc : ∀ w, pub w + priv w = target w)
    (hr : ∀ w, rec w (fun i => priv (a i)) = priv w) (ha : ∀ i, target (a i) = 0) (w : W) :
    pub w + rec w (fun i => -pub (a i)) = target w := by
  have h : (fun i => priv (a i)) = fun i => -pub (a i) := by
    funext i
    have h' := (hc (a i)).trans (ha i)
    linear_combination h'
  rw [← h]
  exact recover hc hr w

end Anchor
end GuardedShiftDecode
