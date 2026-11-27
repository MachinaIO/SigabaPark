import Definitions.Def_WE_UnaryTraceBlocks

open Turing SigabaNeo AdvancedEncryption.WE.UnaryTraceWalk

theorem AdvancedEncryption.WE.UnaryTraceWalk.lookup_block (cert hist : List Bool) (a b : ℕ)
    (ha : a < cert.length) (hb : b < cert.length) :
    Scans cert hist .first 0 (Turing.MultiTapeTM.frame (SigabaNeo.encGate (a, b)))
      (5 * a + 3 * b + 5) (.appendBit (!(hist.getD a true && hist.getD b true))) 0 := by sorry
