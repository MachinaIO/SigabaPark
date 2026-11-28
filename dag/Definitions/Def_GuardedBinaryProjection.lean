import Mathlib.Tactic
namespace GuardedBinaryProjection

/-- A guarded bucket for one forgotten Boolean variable. Each enabled residual
is a unary literal or false when one projects an actual binary clause. -/
def bucket {A I J : Type*} (base : A → Prop) (P : I → A → Prop) (N : J → A → Prop)
    (v : A) (x : Bool) : Prop :=
  base v ∧ (∀ i, x = true ∨ P i v) ∧ (∀ j, x = false ∨ N j v)

def reduced {A I J : Type*} (base : A → Prop) (P : I → A → Prop) (N : J → A → Prop)
    (v : A) : Prop := base v ∧ ∀ i j, P i v ∨ N j v

def encode {W B : Type*} (block : W → B) (anchor : B → W) (v : W → Bool) (w : W) : Bool :=
  xor (v w) (v (anchor (block w)))

def decode {W B : Type*} (block : W → B) (r : W → Bool) (y : B → Bool) (w : W) : Bool :=
  xor (r w) (y (block w))

end GuardedBinaryProjection
