import Definitions.Def_FrontierNandCompiler

open FrontierNandCompiler SigabaNeo Turing Turing.MultiTapeTM

theorem AdvancedEncryption.WE.FrontierNand.decode (gs : SigabaNeo.GateList) : decodeWirePairs (SigabaNeo.encGates gs) = gs := by sorry
