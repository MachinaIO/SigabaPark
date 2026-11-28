import Definitions.Def_WE_CBDWirePad
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size

open Turing.MultiTapeTM Cslib.Crypto
open AdvancedEncryption.WE.CBDWirePad

theorem AdvancedEncryption.WE.CBDWirePad.transport (n : ℕ)
    (μ : PMF (Matrix (Fin 1) (Fin 1) (Fin (n+1) → ZMod 256) × (Fin 1 → Fin (n+1) → ZMod 256))) :
    (μ.map ModuleLWE.encodeSample).map (boundedConvert (n+1)) =
      μ.map (fun ab =>
        ((List.ofFn fun i : Fin (1*(n+1)) => fixed8 ((expandModuleMatrix ab.1 i 0).val.bits)).flatten,
         (List.ofFn fun i : Fin (1*(n+1)) => fixed8 ((flattenPolyVec ab.2 i).val.bits)).flatten)) := by sorry
