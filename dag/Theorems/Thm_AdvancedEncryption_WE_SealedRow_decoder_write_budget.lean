import Definitions.Def_WE

open SigabaNeo AdvancedEncryption

theorem AdvancedEncryption.WE.SealedRow.decoder_write_budget (impl : Impl WE.sig) (cap : WE.cost impl ≤ 2 ^ 32) :
    (impl.machine WE.Alg.dec).tapes ≤ 14 ∧
    (impl.machine WE.Alg.dec).tapes * (impl.machine WE.Alg.dec).time ≤
      14 * (2 ^ 32 - (impl.machine WE.Alg.enc).time) := by sorry
