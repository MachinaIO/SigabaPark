import Definitions.Def_StreamBucketBank

theorem AdvancedEncryption.WE.StreamBank.SentinelWord (a : Fin 64) :
    (64+a.val)/32 = 2+a.val/32 ∧ (64+a.val)/64 = 1 ∧
    (∀ j : Fin 6, (64+a.val).testBit j.val = a.val.testBit j.val) := by sorry
