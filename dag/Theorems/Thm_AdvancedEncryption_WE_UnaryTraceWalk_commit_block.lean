import Definitions.Def_WE_UnaryTraceBlocks

open Turing SigabaNeo AdvancedEncryption.WE.UnaryTraceWalk

theorem AdvancedEncryption.WE.UnaryTraceWalk.commit_block (x cert hist : List Bool) (p : ℕ) (v : Bool) :
    tm.runFrom (scanCfg x cert hist p 0 (.appendBit v)) (hist.length + 1) =
      if cert[hist.length]? = some v then
        scanCfg x cert (hist ++ [v]) p ((hist.length : ℤ) + 1) (.advance v)
      else { scanCfg x cert hist p hist.length (.appendBit v) with state := none, output := [false] } := by sorry
