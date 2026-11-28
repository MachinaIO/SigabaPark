import Definitions.Def_PacketTraceBasis
import Mathlib.Tactic

theorem PacketTraceBasis.traceConstant {F : Type*} [Field F] (S : ℕ) (hs : 0 < S) (a : ℕ → F)
    (alpha omega : F) (ho : IsPrimitiveRoot omega S) :
    (∑ i ∈ Finset.range S, ∑ j ∈ Finset.range S, a j * (alpha * omega ^ i) ^ j) =
      (S : F) * a 0 := by
  sorry
