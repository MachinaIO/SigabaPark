import Definitions.Def_WE_UnaryTraceWalk
import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg

namespace AdvancedEncryption.WE.UnaryTraceWalk

open Turing

/-- A configuration at a gate boundary or inside a lookup. The input offset is zero based. -/
def scanCfg (x cert hist : List Bool) (p : ℕ) (z : ℤ) (q : Phase) : Cfg 2 Bool State x :=
  ⟨some (.inr q), ⟨min p x.length + 1, by omega⟩,
    fun i => tapeOfList (if i = 0 then cert else hist), fun _ => z, []⟩

/-- A read-only block consumes exactly the indicated prefix on every suffix and at every
valid input offset. Its equality covers both tapes, all three heads, the state and output. -/
def Scans (cert hist : List Bool) (q : Phase) (z : ℤ) (bits : List Bool) (ticks : ℕ)
    (r : Phase) (y : ℤ) : Prop :=
  ∀ (x : List Bool) (p : ℕ) (tail : List Bool), p ≤ x.length → x.drop p = bits ++ tail →
    tm.runFrom (scanCfg x cert hist p z q) ticks = scanCfg x cert hist (p + bits.length) y r

end AdvancedEncryption.WE.UnaryTraceWalk
