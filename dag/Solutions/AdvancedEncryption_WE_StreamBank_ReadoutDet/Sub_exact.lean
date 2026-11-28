import Definitions.Def_StreamBucketBank

theorem solution (tag : Nat → Fin 16) : (StreamBucketBank.framedDecoder tag).Deterministic := by
  intro q a w o
  rfl
