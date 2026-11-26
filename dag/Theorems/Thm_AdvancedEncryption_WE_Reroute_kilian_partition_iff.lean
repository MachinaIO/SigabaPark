import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Common

open Matrix

/-- **An invertible comparator re-randomization preserves the state partition.** With
bit-independent comparator secrets the comparator part of the prefix row at a cut is
`e_{κ(x)} ⊗ ρ` (note `pq-we-plr-hop-rank-and-erase` §2). A Kilian map `T ⊗ I` with `T`
invertible that turns hybrid `A` into hybrid `B` must send `e_{κA x}` to `e_{κB x}` for every
prefix, and then the two state maps have the same fibres. A reroute merges the single chain prefix
`t_{≤i}` into the lt class (`κB` identifies two prefixes that `κA` separates), so it is not a
Kilian re-randomization at any width (note `pq-we-two-pass-reroute`, §3). -/
theorem AdvancedEncryption.WE.Reroute.kilian_partition_iff {K V S : Type*} [Field K] [Fintype S] [DecidableEq S]
    (κA κB : V → S) (T : Matrix S S K) (hT : IsUnit T.det)
    (h : ∀ x, Pi.single (κA x) (1 : K) ᵥ* T = Pi.single (κB x) 1) (x y : V) :
    κA x = κA y ↔ κB x = κB y := by sorry
