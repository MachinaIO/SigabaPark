import Definitions.Def_StreamBucketBank

theorem solution (tag : Nat → Fin 16) :
    (StreamBucketBank.localDecoder 1024 513).cost = 5420940 ∧
    (StreamBucketBank.framedDecoder tag).states = 15877 ∧
    (StreamBucketBank.framedDecoder tag).descLen = 1714716 ∧
    (StreamBucketBank.framedDecoder tag).cost = 270150172 := by
  change (StreamBucketBank.localDecoder 1024 513).cost = 5420940 ∧
    (StreamBucketBank.framedDecoder (fun _ => 0)).states = 15877 ∧
    (StreamBucketBank.framedDecoder (fun _ => 0)).descLen = 1714716 ∧
    (StreamBucketBank.framedDecoder (fun _ => 0)).cost = 270150172
  decide
