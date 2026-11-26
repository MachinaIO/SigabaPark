import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Common

/-- **Zero entries are hints (note `pq-we-native-hop-designs`, §6).** If a level of a GGH15
encoding has a zero program entry, its preimage `D` satisfies `A D = E` (short) on the rows of
that block. Then every LWE sample `S A + E'` on those rows satisfies
`(S A + E') D = S E + E' D`, which is short for short `S, E, E', D`, while a uniform matrix times
`D` is not. So the rows `A` of the level above a departure (a zero entry) cannot be switched to
uniform by an LWE step with secret `A`: this is the algebraic reason leaf-first LWE stops at the
first departure from a cube or chain. -/
theorem AdvancedEncryption.WE.NativeHop.zero_entry_hint {R : Type*} [Ring R] {a b c d : Type*}
    [Fintype b] [Fintype c]
    (S : Matrix a b R) (A : Matrix b c R) (E' : Matrix a c R) (D : Matrix c d R)
    (E : Matrix b d R)
    (hAD : A * D = E) :
    (S * A + E') * D = S * E + E' * D := by sorry
