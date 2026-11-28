import Definitions.Def_StreamBucketBank

theorem AdvancedEncryption.WE.StreamBank.ShareFold (xs : List Nat) (a : Nat) :
    (xs.foldl (fun z x => (z+63*x)%64) (a%64)) =
    (a+63*xs.sum)%64 := by sorry
