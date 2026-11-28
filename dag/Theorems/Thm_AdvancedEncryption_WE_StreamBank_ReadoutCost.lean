import Definitions.Def_StreamBucketBank

theorem AdvancedEncryption.WE.StreamBank.ReadoutCost (tag : Nat → Fin 16) :
    (StreamBucketBank.localDecoder 1024 513).cost = 5420940 ∧
    (StreamBucketBank.framedDecoder tag).states = 15877 ∧
    (StreamBucketBank.framedDecoder tag).descLen = 1714716 ∧
    (StreamBucketBank.framedDecoder tag).cost = 270150172 := by sorry
