import Definitions.Def_WE_CircuitSAT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Run

open SigabaNeo AdvancedEncryption AdvancedEncryption.WE AdvancedEncryption.WE.CircuitSAT
open Turing.MultiTapeTM

theorem AdvancedEncryption.WE.CircuitSAT.correct_clock_floor (impl : Impl WE.sig)
    (hc : WE.Correct (relation inputs size) params impl) :
    207643654 ≤ (impl.machine Alg.enc).time ∧ 207643910 ≤ (impl.machine Alg.dec).time := by sorry
