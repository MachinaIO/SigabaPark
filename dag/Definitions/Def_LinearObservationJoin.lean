import Mathlib.Tactic
import Mathlib.LinearAlgebra.Quotient.Basic
namespace ObservationJoin
def fibre {K E A B : Type*} [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    (L : E→ₗ[K]A) (R : E→ₗ[K]B) (V : Submodule K E) :=
  (LinearMap.ker L ⊓ V) ⊔ (LinearMap.ker R ⊓ V)

def agrees {I : Type*} (s a : I→Bool) (used : I→Prop) := ∀ i, used i → s i = a i
end ObservationJoin
open ObservationJoin