import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-- **Cube decomposition of lexicographic prefixes (note `pq-we-native-hop-designs`, §6).**
`w < k` iff, at some bit `j`, `k` has a `1`, `w` has a `0`, and all higher bits agree. So the
erased set `{w : w < k}` of a positional walk is the disjoint union, over the `1`-bits `j` of
`k`, of the subcubes "bits above `j` as in `k`, bit `j` equal to `0`, lower bits free": at most
`n` pad slots for `n`-bit witnesses. -/
theorem AdvancedEncryption.WE.NativeHop.lex_prefix_cubes (w k : ℕ) :
    w < k ↔ ∃ j, k.testBit j = true ∧ w.testBit j = false ∧
      ∀ i, j < i → w.testBit i = k.testBit i := by sorry
