import Definitions.Def_FrontierNandCompiler

open FrontierNandCompiler SigabaNeo Turing Turing.MultiTapeTM

theorem solution : parserMachine.tapes = 0 ∧ parserMachine.states = 475136 ∧
    parserMachine.descLen = 65568768 ∧ parserMachine.time = 2^28 := by
  decide
