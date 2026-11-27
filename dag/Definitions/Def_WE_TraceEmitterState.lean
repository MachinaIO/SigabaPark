import Definitions.Def_WE_TraceEmitter
import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg
namespace AdvancedEncryption.WE.TraceEmitter
open Turing
/-- Snapshot on the registered word. The third tape contains one stationary origin mark. -/
def snap (x : List Bool) (p : ℕ) (s h : List Bool) (z j : ℤ) (q : Option Phase)
    (out : List Bool := []) : Cfg 3 Bool Phase x :=
  ⟨q, ⟨min p x.length + 1, by omega⟩,
    fun t ↦ tapeOfList (if t = 0 then s else if t = 1 then h else [true]),
    fun t ↦ if t = 0 then z else j, out⟩
end AdvancedEncryption.WE.TraceEmitter
