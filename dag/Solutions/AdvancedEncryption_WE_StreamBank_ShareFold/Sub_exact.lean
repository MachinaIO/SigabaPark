import Definitions.Def_StreamBucketBank

theorem solution (xs : List Nat) (a : Nat) :
    (xs.foldl (fun z x => (z+63*x)%64) (a%64)) =
    (a+63*xs.sum)%64 := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.sum_cons]
    rw [show (a % 64 + 63*x)%64 = (a+63*x)%64 by omega]
    rw [ih]
    congr 1
    ring
