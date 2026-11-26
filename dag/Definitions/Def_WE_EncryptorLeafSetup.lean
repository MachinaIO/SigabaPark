import Definitions.Def_WE_EncryptorSetup

/-!
# The leaf lemma's setup kernel with the WE encryptor's own `(W, T)`

`leafSetupEnc p mb hm hσ B`: `W = [A | H − A R]` with a gadget trapdoor (`A` uniform, `R` uniform
binary), split into its `ℓ` row blocks, and `T` by flooding (`floodT`) with the short preimage map
of `W` — the encryptor's sampler of `Def_WE_EncryptorSetup` (`encLaw`), for a given `B`.
-/

namespace AdvancedEncryption.WE.EncryptorSetup

open Matrix SigabaNeo.Lattices Cslib.Probability AdvancedEncryption.WE.Assumptions.SuccinctLWE

/-- The encryptor's `(W_1, …, W_ℓ, T)` for a given `B`. -/
noncomputable def leafSetupEnc (p : Params) (mb : ℕ) (hm : mb + p.ℓ * p.n * p.k = p.m)
    (hσ : (0 : ℝ) < p.σ) (B : Matrix (Fin p.n) (Fin p.m) (ZMod p.q)) :
    PMF ((Fin p.ℓ → Matrix (Fin p.n) (Fin p.m) (ZMod p.q)) ×
      Option (Matrix (Fin (p.ℓ * p.m + p.m)) (Fin (p.ℓ * (p.n * p.k))) ℤ)) :=
  (PMF.uniformOfFintype (Matrix (Fin (p.ℓ * p.n)) (Fin mb) (ZMod p.q))).bind fun A =>
    (Cslib.Probability.PMF.pi fun _ : Fin (p.ℓ * p.n * p.k) =>
      PMF.uniformOfFintype (Fin mb → Bool)).bind fun Rc =>
        (floodT p hσ B (Wof hm A fun c => binaryHash A (Rc c)) (dOf hm Rc)).map fun T =>
          (fun i r c => (Wof hm A fun c => binaryHash A (Rc c)) (finProdFinEquiv (i, r)) c, T)

end AdvancedEncryption.WE.EncryptorSetup
