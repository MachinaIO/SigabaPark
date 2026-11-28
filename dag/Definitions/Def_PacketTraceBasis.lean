import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.LinearAlgebra.Span.Basic

namespace PacketTraceBasis

def rowsAgree {R M I : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (rows : I → M) (f g : M →ₗ[R] R) : Prop := ∀ i, f (rows i) = g (rows i)

end PacketTraceBasis
