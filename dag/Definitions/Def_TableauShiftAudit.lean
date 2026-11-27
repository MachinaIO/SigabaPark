import Mathlib

namespace TableauFirstFailure

abbrev Row := Bool × Bool

def mask : List Row → Bool
  | [] => false
  | (p, r) :: tail => (if p then false else r) ^^ mask tail

def changeFirst : List Row → List Row
  | [] => []
  | (true, r) :: tail => (true, r) :: changeFirst tail
  | (false, r) :: tail => (false, !r) :: tail

theorem involution (rows : List Row) : changeFirst (changeFirst rows) = rows := by
  induction rows with
  | nil => rfl
  | cons row tail ih =>
    rcases row with ⟨p,r⟩
    cases p <;> cases r <;> simp [changeFirst, ih]

theorem public_checks (rows : List Row) :
    (changeFirst rows).map Prod.fst = rows.map Prod.fst := by
  induction rows with
  | nil => rfl
  | cons row tail ih =>
    rcases row with ⟨p,r⟩
    cases p <;> simp [changeFirst, ih]

theorem mask_flip (rows : List Row) :
    mask (changeFirst rows) = if rows.all Prod.fst then mask rows else !(mask rows) := by
  induction rows with
  | nil => decide
  | cons row tail ih =>
    rcases row with ⟨p,r⟩
    cases p <;> cases r <;> cases h : mask tail <;> cases ha : tail.all Prod.fst <;>
      simp_all [changeFirst,mask] <;> grind

end TableauFirstFailure


namespace ShiftPairView

/-- Tag on a shifted representation; evaluation of the underlying scheme ignores it. -/
def tag (r f₀ f₁ : Bool) := r ^^ (f₀ && f₁)

theorem singleTagPermutation (f₀ f₁ : Bool) :
    ∀ r, tag (tag r f₀ f₁) f₀ f₁ = r := by
  intro r
  cases r <;> cases f₀ <;> cases f₁ <;> rfl

def guess (r b f₀ f₁ : Bool) := tag r b b ^^ tag r f₀ f₁

theorem pairedTag (r b f₀ f₁ : Bool) :
    guess r b f₀ f₁ = (b ^^ (f₀ && f₁)) := by
  cases r <;> cases b <;> cases f₀ <;> cases f₁ <;> rfl

def acceptingCount (r b : Bool) :=
  (([false,true] : List Bool).flatMap fun u =>
    ([false,true] : List Bool).map fun v => guess r b u v).count true

/-- Number of bits in the two literal public tensors in Construction 3.1.
    l is ceil(log₂ q) and m=n*l. -/
def setupBits (n l z tau : Nat) := n*(z+1+tau)*(n*l)*l

theorem chargedExample :
    setupBits 64 16 4095 1 = 4296015872 ∧
    2^32 < setupBits 64 16 4095 1 := by decide

end ShiftPairView


namespace GuardedIssuer

/-- Fix the issuer's coins and all its public inputs. Its Boolean oracle calls can be adaptive. -/
inductive Tree (Q A : Type) where
  | done (artifact : A)
  | ask (q : Q) (lo hi : Tree Q A)

variable {Q A : Type}

def run (o : Q → Bool) : Tree Q A → A
  | .done a => a
  | .ask q lo hi => if o q then run o hi else run o lo

def hit (o valid : Q → Bool) : Tree Q A → Bool
  | .done _ => false
  | .ask q lo hi => valid q || (if o q then hit o valid hi else hit o valid lo)

theorem replay (base other valid : Q → Bool)
    (agree : ∀ q, valid q = false → other q = base q) (t : Tree Q A)
    (miss : hit base valid t = false) : run other t = run base t := by
  induction t with
  | done => rfl
  | ask q lo hi il ih =>
    cases hv : valid q <;> cases hb : base q <;>
      simp_all [hit,run]

/-- A missed query costs at least one decryption error across the two coupled messages. -/
def misses (xs : List (Bool × Bool × Bool)) : Nat :=
  (xs.filter fun p => !p.1).length

def errors (xs : List (Bool × Bool × Bool)) : Nat :=
  (xs.filter fun p => p.2.1).length + (xs.filter fun p => !p.2.2).length

theorem count_bound (xs : List (Bool × Bool × Bool))
    (h : ∀ p ∈ xs, p.1 = false → p.2.1 = true ∨ p.2.2 = false) :
    misses xs ≤ errors xs := by
  induction xs with
  | nil => decide
  | cons p xs ih =>
    have ht := ih (fun u hu => h u (by simp [hu]))
    have hp := h p (by simp)
    rcases p with ⟨a,b,c⟩
    cases a <;> cases b <;> cases c <;>
      simp_all [misses,errors] <;> omega

theorem point_query_arithmetic : 2 ^ 32 < 2 ^ 128 - 2 := by decide

end GuardedIssuer

namespace TableauShiftAudit

def History (G : Type) : Nat → Type
  | 0 => Unit
  | n+1 => History G n × G

def translate {G X Y : Type} [AddGroup G] (e : X ≃ Y) (s : X → G) :
    (X × G) ≃ (Y × G) where
  toFun p := (e p.1, p.2 + s p.1)
  invFun q := (e.symm q.1, q.2 - s (e.symm q.1))
  left_inv := by rintro ⟨x,g⟩; simp
  right_inv := by rintro ⟨y,g⟩; simp

def triangular {G : Type} [AddGroup G] :
    (n : Nat) → ((i : Fin n) → History G i.val → G) → History G n ≃ History G n
  | 0, _ => Equiv.refl _
  | n+1, s => translate (triangular n (fun i => s i.castSucc)) (s (Fin.last n))

end TableauShiftAudit
