import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-- **Mix-and-match saturation (note `pq-we-native-hop-designs`, §2, direction (a)).** In a NAND
circuit with `n` inputs and `g` gates (gate `j` is wire `n + j` and reads wires `a j, b j < n + j`),
let `R w ⊆ {0,1}` be any family of value sets that contains both values on every input and is
closed under gate propagation (`α ∈ R (a j)`, `β ∈ R (b j)` give `NAND α β ∈ R (n + j)`). Then
`R w` is all of `{0,1}` on every wire. Read with `R w` = the values whose wire label a decryptor can
derive: any wire-labelled scheme whose gate step works on any pair of derivable input labels
yields the label of output value `1` on every statement. -/
theorem AdvancedEncryption.WE.NativeHop.nand_reach_saturate (n g : ℕ) (a b : ℕ → ℕ)
    (ha : ∀ j < g, a j < n + j) (hb : ∀ j < g, b j < n + j)
    (R : ℕ → Set Bool) (hin : ∀ i < n, R i = Set.univ)
    (hprop : ∀ j < g, ∀ α ∈ R (a j), ∀ β ∈ R (b j), (!(α && β)) ∈ R (n + j)) :
    ∀ w < n + g, R w = Set.univ := by sorry
