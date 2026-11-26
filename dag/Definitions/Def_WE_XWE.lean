import SigabaNeo.Trusted.Assumption
import SigabaNeo.Trusted.Primitive

/-!
# XWE from ABE (Brakerski–Jain–Komargodski–Passelègue–Wichs, ePrint 2017/874, Thm. 3.2)

An attribute-based encryption scheme given by its laws: `setup` (the master secret key), `key msk v`
(a key for the function `f_{φ, v}(w2) = φ(v ‖ w2)`, the statement being fixed outside) and
`enc msk w b` (an encryption of the bit `b` under the attribute `w`). For enumerations `W1` (key
halves) and `W2` (attribute halves) of the witness space, the XWE ciphertext is all the keys
`key msk v` for `v ∈ W1` and all the ciphertexts `enc msk w β` for `w ∈ W2`, encoded as a tuple
and then post-processed by a fixed map `post` (for example the framing of the WE challenge).

`hybLaw j` encrypts `true` under the first `j` attributes and `false` under the others, so
`hybLaw 0` and `hybLaw |W2|` are the XWE laws of `false` and `true` (`hybLaw_zero`,
`hybLaw_length`). If each hop `j → j + 1` (one ABE ciphertext switched) has `k` bits, the
XWE laws are distinguished with `2^k · gain ≤ |W2|² · cost` (`security`).
-/

namespace AdvancedEncryption.WE.XWE

open SigabaNeo

/-- An ABE scheme given by the laws of its algorithms. -/
structure ABELaws where
  /-- The master secret keys. -/
  MSK : Type
  /-- The law of the master secret key. -/
  setup : PMF MSK
  /-- The law of the key for the key half `v`. -/
  key : MSK → List Bool → PMF (List Bool)
  /-- The law of the encryption of a bit under an attribute. -/
  enc : MSK → List Bool → Bool → PMF (List Bool)

/-- Independent samples from a list of laws. -/
noncomputable def seqLaw : List (PMF (List Bool)) → PMF (List (List Bool))
  | [] => PMF.pure []
  | p :: ps => p.bind fun x => (seqLaw ps).map (x :: ·)

/-- The XWE ciphertext law in which the `i`-th attribute of `W2` encrypts `bit i`. -/
noncomputable def ctLaw (S : ABELaws) (W1 W2 : List (List Bool)) (post : List Bool → List Bool)
    (bit : ℕ → Bool) : PMF (List Bool) :=
  S.setup.bind fun msk =>
    (seqLaw (W1.map (S.key msk))).bind fun ks =>
      (seqLaw (W2.mapIdx fun i w => S.enc msk w (bit i))).map fun cs =>
        post (encodeTuple [encodeTuple ks, encodeTuple cs])

/-- The XWE encryption law of the bit `β`. -/
noncomputable def xweLaw (S : ABELaws) (W1 W2 : List (List Bool)) (post : List Bool → List Bool)
    (β : Bool) : PMF (List Bool) :=
  ctLaw S W1 W2 post fun _ => β

/-- The hybrid `j`: the first `j` attributes encrypt `true`, the others `false`. -/
noncomputable def hybLaw (S : ABELaws) (W1 W2 : List (List Bool)) (post : List Bool → List Bool)
    (j : ℕ) : PMF (List Bool) :=
  ctLaw S W1 W2 post fun i => decide (i < j)

end AdvancedEncryption.WE.XWE
