import SigabaNeoStd.Lattices.Trapdoor.Family.Joint
import SigabaNeoStd.Lattices.LeftoverHash
import SigabaNeoStd.Lattices.BoxSampler
import SigabaNeoStd.Lattices.Homomorphic.Eval
import CslibFrontier.Probability.Product
import SigabaNeoStd.Lattices.Boxes
import SigabaNeoStd.Lattices.Homomorphic.NoiseBound
import Definitions.Def_SuccinctLWE


/-!
# The WE encryptor's own ℓ-succinct LWE setup `(B, W, T)`

`Def_WE_CircuitSAT` has no common reference string, so the WE encryptor samples the succinct-LWE
instance itself:

* `B ← Z_q^{n×m}` uniform, with no trapdoor;
* `W = [A | H − A R] ∈ Z_q^{ℓn × m}` (`Wof`), `A ← Z_q^{ℓn × mb}` uniform, `R ∈ {0,1}^{mb × ℓnk}`
  uniform (its columns `Rc`), `H = gadget (ℓn) k q`, `m = mb + ℓnk`;
* `W` has the short preimage map `dOf Rc v = [R x; x]`, `x = bits v` the binary decomposition;
* each column of `T` is the flooding sample `y + [0; dOf(t − [I_ℓ ⊗ B | W] y)]`,
  `y ← D_{Z^{ℓm+m}, σ}`, `t` the column of `I_ℓ ⊗ G` (`floodT`).

`encLaw` is the law of `(B, W, T)`; `chalLaw` is the law of `(B, W, T)` in `Def_SuccinctLWE`
(`B`, `W` uniform, `T ← trapdoorLaw`).
-/

namespace AdvancedEncryption.WE.EncryptorSetup

open Matrix SigabaNeo.Lattices Cslib.Probability AdvancedEncryption.WE.Assumptions.SuccinctLWE

/-- The bits of the entries of `v`, laid out as the columns of `gadget r k q`. -/
def bits {r k q : ℕ} (v : Fin r → ZMod q) : Fin (r * k) → ℤ := fun j =>
  (((v (finProdFinEquiv.symm j).1).val / 2 ^ (finProdFinEquiv.symm j).2.val % 2 : ℕ) : ℤ)

/-- `W = [A | H − V] ∈ Z_q^{r × m}`, `H = gadget r k q`, with `V` given by its columns. -/
def Wof {q r k mb m : ℕ} (hm : mb + r * k = m) (A : Matrix (Fin r) (Fin mb) (ZMod q))
    (V : Fin (r * k) → Fin r → ZMod q) : Matrix (Fin r) (Fin m) (ZMod q) := fun i j =>
  if h : j.val < mb then A i ⟨j.val, h⟩
  else AdvancedEncryption.WE.Assumptions.SuccinctLWE.gadget r k q i ⟨j.val - mb, by have := j.isLt; omega⟩ -
    V ⟨j.val - mb, by have := j.isLt; omega⟩ i

/-- The short preimage map of `[A | H − A R]` (`R` by its columns `Rc`): `v ↦ [R x; x]`,
`x = bits v`. -/
def dOf {q r k mb m : ℕ} (hm : mb + r * k = m) (Rc : Fin (r * k) → Fin mb → Bool)
    (v : Fin r → ZMod q) : Fin m → ℤ := fun j =>
  if h : j.val < mb then ∑ c, (if Rc c ⟨j.val, h⟩ then bits (k := k) v c else 0)
  else bits (k := k) v ⟨j.val - mb, by have := j.isLt; omega⟩

/-- `T` by flooding: each column `y + [0; d(t − [I_ℓ ⊗ B | W] y)]`, `y ← D_{Z^{ℓm+m}, σ}`. -/
noncomputable def floodT (p : Params) (hσ : (0 : ℝ) < p.σ)
    (B : Matrix (Fin p.n) (Fin p.m) (ZMod p.q)) (W : Matrix (Fin (p.ℓ * p.n)) (Fin p.m) (ZMod p.q))
    (dW : (Fin (p.ℓ * p.n) → ZMod p.q) → Fin p.m → ℤ) :
    PMF (Option (Matrix (Fin (p.ℓ * p.m + p.m)) (Fin (p.ℓ * (p.n * p.k))) ℤ)) :=
  (sampleOptList ((List.finRange (p.ℓ * (p.n * p.k))).map fun c =>
      some (((sampleList (gaussZ (p.σ : ℝ) hσ) (p.ℓ * p.m + p.m)).map
          (fun l (j : Fin (p.ℓ * p.m + p.m)) => l.getD j default)).map fun y =>
        y + fun j : Fin (p.ℓ * p.m + p.m) =>
          if h : j.val < p.ℓ * p.m then (0 : ℤ) else
            dW ((fun i => blockDiag (ℓ := p.ℓ) (AdvancedEncryption.WE.Assumptions.SuccinctLWE.gadget p.n p.k p.q) i c) -
              stacked B W *ᵥ fun j => ((y j : ℤ) : ZMod p.q))
              ⟨j.val - p.ℓ * p.m, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt h) j.isLt⟩))).map
    (Option.map fun cols r j => (cols.getD j.val 0) r)

/-- The encryptor's `(B, W, T)`. -/
noncomputable def encLaw (p : Params) (mb : ℕ) (hm : mb + p.ℓ * p.n * p.k = p.m)
    (hσ : (0 : ℝ) < p.σ) :
    PMF (Matrix (Fin p.n) (Fin p.m) (ZMod p.q) × Matrix (Fin (p.ℓ * p.n)) (Fin p.m) (ZMod p.q) ×
      Option (Matrix (Fin (p.ℓ * p.m + p.m)) (Fin (p.ℓ * (p.n * p.k))) ℤ)) :=
  (PMF.uniformOfFintype (Matrix (Fin p.n) (Fin p.m) (ZMod p.q))).bind fun B =>
    (PMF.uniformOfFintype (Matrix (Fin (p.ℓ * p.n)) (Fin mb) (ZMod p.q))).bind fun A =>
      (Cslib.Probability.PMF.pi fun _ : Fin (p.ℓ * p.n * p.k) =>
        PMF.uniformOfFintype (Fin mb → Bool)).bind fun Rc =>
          (floodT p hσ B (Wof hm A fun c => binaryHash A (Rc c)) (dOf hm Rc)).map fun T =>
            (B, Wof hm A (fun c => binaryHash A (Rc c)), T)

/-- The challenger's `(B, W, T)` in `Def_SuccinctLWE`. -/
noncomputable def chalLaw (p : Params) :
    PMF (Matrix (Fin p.n) (Fin p.m) (ZMod p.q) × Matrix (Fin (p.ℓ * p.n)) (Fin p.m) (ZMod p.q) ×
      Option (Matrix (Fin (p.ℓ * p.m + p.m)) (Fin (p.ℓ * (p.n * p.k))) ℤ)) :=
  (PMF.uniformOfFintype (Matrix (Fin p.n) (Fin p.m) (ZMod p.q))).bind fun B =>
    (PMF.uniformOfFintype (Matrix (Fin (p.ℓ * p.n)) (Fin p.m) (ZMod p.q))).bind fun W =>
      (trapdoorLaw p B W).map fun T => (B, W, T)

/-- Row `i`, column `a` of the `B` block `i` of `T`: index `i·m + a` of `Z^{ℓm+m}`. -/
def idxB {ℓ m : ℕ} (i : Fin ℓ) (a : Fin m) : Fin (ℓ * m + m) := Fin.castAdd m (finProdFinEquiv (i, a))

/-- Row `a` of the `W` block of `T`: index `ℓm + a`. -/
def idxW {ℓ m : ℕ} (a : Fin m) : Fin (ℓ * m + m) := Fin.natAdd (ℓ * m) a

/-- The setup kernel of the leaf lemma from `Def_SuccinctLWE`: `W` uniform, split into its `ℓ`
row blocks `W_i ∈ Z_q^{n×m}`, and `T ← trapdoorLaw p B W`. -/
noncomputable def leafSetup (p : Params) (B : Matrix (Fin p.n) (Fin p.m) (ZMod p.q)) :
    PMF ((Fin p.ℓ → Matrix (Fin p.n) (Fin p.m) (ZMod p.q)) ×
      Option (Matrix (Fin (p.ℓ * p.m + p.m)) (Fin (p.ℓ * (p.n * p.k))) ℤ)) :=
  (PMF.uniformOfFintype (Matrix (Fin (p.ℓ * p.n)) (Fin p.m) (ZMod p.q))).bind fun W =>
    (trapdoorLaw p B W).map fun T => (fun i r c => W (finProdFinEquiv (i, r)) c, T)

/-- The public check on `T`: it exists and its entries are at most `E` in absolute value. -/
def leafGood {r c : ℕ} (E : ℕ) (T : Option (Matrix (Fin r) (Fin c) ℤ)) : Prop :=
  ∃ T' : Matrix (Fin r) (Fin c) ℤ, T = some T' ∧ ∀ a b, |T' a b| ≤ E

/-- The block `T_B[i, j] ∈ Z_q^{m × nk}` of `T` (zero if `T = none`). -/
def leafTB {ℓ m nk : ℕ} {q : ℕ} (T : Option (Matrix (Fin (ℓ * m + m)) (Fin (ℓ * nk)) ℤ))
    (i j : Fin ℓ) : Matrix (Fin m) (Fin nk) (ZMod q) := fun a c =>
  (((T.getD 0) (idxB i a) (finProdFinEquiv (j, c)) : ℤ) : ZMod q)

/-- The block `T_W[j] ∈ Z_q^{m × nk}` of `T` (zero if `T = none`). -/
def leafTW {ℓ m nk : ℕ} {q : ℕ} (T : Option (Matrix (Fin (ℓ * m + m)) (Fin (ℓ * nk)) ℤ))
    (j : Fin ℓ) : Matrix (Fin m) (Fin nk) (ZMod q) := fun a c =>
  (((T.getD 0) (idxW a) (finProdFinEquiv (j, c)) : ℤ) : ZMod q)

end AdvancedEncryption.WE.EncryptorSetup
