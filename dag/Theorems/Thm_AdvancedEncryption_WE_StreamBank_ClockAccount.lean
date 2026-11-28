import Definitions.Def_StreamBucketBank

theorem AdvancedEncryption.WE.StreamBank.ClockAccount (n t k : Nat) :
    let r := StreamBucketBank.rows t k
    (5*n+17*r+8) + r*(7*n+11) + (16*r+6*k+3) =
    StreamBucketBank.ticks n t k := by sorry
