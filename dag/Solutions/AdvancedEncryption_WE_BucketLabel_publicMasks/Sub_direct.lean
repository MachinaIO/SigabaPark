import Definitions.Def_BucketLabel
open BucketLabel
theorem solution {I V Secret : Type} [AddGroup V]
    (mask share : I → V) (rec : (I → V) → Secret) (secret : Secret)
    (h : rec share = secret) :
    rec (fun i => -mask i + (mask i + share i)) = secret := by simpa using h
