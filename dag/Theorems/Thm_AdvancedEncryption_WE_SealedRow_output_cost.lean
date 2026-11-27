import Definitions.Def_WE
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import SigabaNeoStd.Machines.Compose.AndThen

open SigabaNeo AdvancedEncryption

theorem AdvancedEncryption.WE.SealedRow.output_cost (R : WE.Relation) (p : WE.Params) (impl : Impl WE.sig) (φ : R.Stmt)
    (β : Bool) (ct : List Bool) (hs : ct ∈ (WE.enc (R := R) p impl φ β).support) (hn : ct ≠ []) :
    2 * ct.length + 1 ≤ (impl.machine WE.Alg.enc).time := by sorry
