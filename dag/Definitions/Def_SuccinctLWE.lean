import SigabaNeoStd.Lattices.LWE
import SigabaNeoStd.Lattices.Trapdoor
import SigabaNeo.Trusted.Primitive
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option

/-!
# ℓ-succinct LWE (Wee, CRYPTO 2024)

The `(ℓ, σ)`-succinct LWE assumption of Wee, *Circuit ABE with poly(depth, λ)-sized ciphertexts
and keys from lattices* (CRYPTO 2024), as stated in Assumption 1 of arXiv 2603.16117
("Ciphertext-Policy ABE for NC¹ circuits with constant-size ciphertexts from succinct LWE"):
for `m ≥ 2 n log q`,

    (B, sᵀB + eᵀ, W, T) ≈_c (B, c, W, T)

with `B ← Z_q^{n×m}`, `s ← Z_q^n`, `c ← Z_q^m`, `W ← Z_q^{ℓn×m}` uniform, `e ← D_{Z,χ}^m`, and `T ← [I_ℓ ⊗ B | W]^{-1}_σ(I_ℓ ⊗ G)`. Here `G = I_n ⊗ gᵀ` with
`gᵀ = (1, 2, …, 2^{⌈log q⌉−1})` (the gadget matrix of [MP12], Section III of the same paper), and
`A^{-1}_σ(Y)` draws each column of a preimage of `Y` independently from the discrete Gaussian of
width `σ` on the corresponding coset (`SigabaNeo.Lattices.Trapdoor.preimage`; `none` if a coset is
empty). The 1-succinct LWE assumption is equivalent to LWE (ibid.).

**Concrete form.** The real and ideal laws above, encoded, as a decision problem. The width
convention is that of `SigabaNeoStd`: `ρ_s(x) = exp(−π x²/s²)`. The security function claims the
strength of plain decision LWE at `(n, m, q, χ)` with a uniform secret (`LWE.H`), and only when
`m ≥ 2 n ⌈log q⌉`, `ℓ ≥ 1` and `σ ≥ √n · ⌈log q⌉` (a concrete stand-in for the trapdoor-sampling
bound `σ ≥ O(√(n log q)) · ω(√log n)` of Lemma 3 of the same paper, below which `T` is not a
proper Gaussian preimage); `0` otherwise. For `ℓ ≥ 2` the claim is a conjecture: no attack using
`(W, T)` better than on LWE is known, and Cryptanalysis AI lowers it if one is found.
-/

namespace AdvancedEncryption.WE.Assumptions.SuccinctLWE

open SigabaNeo SigabaNeo.Lattices Turing.MultiTapeTM Cslib.Probability

/-- The parameters: dimension `n`, samples `m`, modulus `q`, succinctness `ℓ`, error width `χ`,
preimage width `σ`. -/
structure Params where
  n : ℕ
  m : ℕ
  q : ℕ
  ℓ : ℕ
  χ : ℚ
  σ : ℚ
  q_pos : 0 < q := by decide

instance (p : Params) : NeZero p.q := ⟨p.q_pos.ne'⟩

/-- The gadget length `⌈log₂ q⌉`. -/
def Params.k (p : Params) : ℕ := Nat.clog 2 p.q

/-- The gadget matrix `G = I_n ⊗ gᵀ ∈ Z_q^{n × n⌈log q⌉}`, `gᵀ = (1, 2, …, 2^{k−1})`. -/
def gadget (n k q : ℕ) : Matrix (Fin n) (Fin (n * k)) (ZMod q) := fun i j =>
  let ij := finProdFinEquiv.symm j
  if ij.1 = i then (2 ^ ij.2.val : ZMod q) else 0

/-- `I_ℓ ⊗ M`, with rows and columns indexed block by block. -/
def blockDiag {r c ℓ q : ℕ} (M : Matrix (Fin r) (Fin c) (ZMod q)) :
    Matrix (Fin (ℓ * r)) (Fin (ℓ * c)) (ZMod q) := fun i j =>
  let a := finProdFinEquiv.symm i
  let b := finProdFinEquiv.symm j
  if a.1 = b.1 then M a.2 b.2 else 0

/-- `[I_ℓ ⊗ B | W] ∈ Z_q^{ℓn × (ℓm + m)}`. -/
def stacked {n m ℓ q : ℕ} (B : Matrix (Fin n) (Fin m) (ZMod q))
    (W : Matrix (Fin (ℓ * n)) (Fin m) (ZMod q)) : Matrix (Fin (ℓ * n)) (Fin (ℓ * m + m)) (ZMod q) :=
  fun i j => if h : j.val < ℓ * m then blockDiag (ℓ := ℓ) B i ⟨j.val, h⟩
    else W i ⟨j.val - ℓ * m, by omega⟩

/-- `T ← [I_ℓ ⊗ B | W]^{-1}_σ(I_ℓ ⊗ G)` (`none` if a coset is empty or `σ ≤ 0`). -/
noncomputable def trapdoorLaw (p : Params) (B : Matrix (Fin p.n) (Fin p.m) (ZMod p.q))
    (W : Matrix (Fin (p.ℓ * p.n)) (Fin p.m) (ZMod p.q)) :
    PMF (Option (Matrix (Fin (p.ℓ * p.m + p.m)) (Fin (p.ℓ * (p.n * p.k))) ℤ)) :=
  if h : 0 < p.σ then
    Trapdoor.preimage (stacked B W) (blockDiag (ℓ := p.ℓ) (gadget p.n p.k p.q)) p.σ
      (by exact_mod_cast h)
  else PMF.pure none

/-- An instance `(B, b, W, T)`. -/
abbrev Instance (p : Params) : Type :=
  Matrix (Fin p.n) (Fin p.m) (ZMod p.q) × (Fin p.m → ZMod p.q) ×
    Matrix (Fin (p.ℓ * p.n)) (Fin p.m) (ZMod p.q) ×
    Option (Matrix (Fin (p.ℓ * p.m + p.m)) (Fin (p.ℓ * (p.n * p.k))) ℤ)

/-- The encoding of an instance: the entries of `B`, `b`, `W` as natural numbers below `q`, and the
columns of `T` (or nothing), framed. -/
def encode (p : Params) (x : Instance p) : List Bool :=
  encodeTuple [encList encNat (matVals x.1), encList encNat (List.ofFn fun j => (x.2.1 j).val),
    encList encNat (matVals x.2.2.1),
    encOption (encList (encList encIntBin)) (x.2.2.2.map Trapdoor.cols)]

/-- `(B, W, T)` with `B`, `W` uniform and `T ← [I_ℓ ⊗ B | W]^{-1}_σ(I_ℓ ⊗ G)`, and the second
component chosen from `B` by `second`. -/
noncomputable def lawWith (p : Params)
    (second : Matrix (Fin p.n) (Fin p.m) (ZMod p.q) → PMF (Fin p.m → ZMod p.q)) :
    PMF (List Bool) := do
  let B ← PMF.uniformOfFintype (Matrix (Fin p.n) (Fin p.m) (ZMod p.q))
  let b ← second B
  let W ← PMF.uniformOfFintype (Matrix (Fin (p.ℓ * p.n)) (Fin p.m) (ZMod p.q))
  let T ← trapdoorLaw p B W
  return encode p (B, b, W, T)

/-- The error `e ← D_{Z,χ}^m`, reduced mod `q`. -/
noncomputable def errorLaw (p : Params) : PMF (Fin p.m → ZMod p.q) :=
  sampleFun (ModuleLWE.coeffLaw p.q (.gauss p.χ))

/-- The real law: `b = sᵀB + eᵀ`, `s ← Z_q^n` uniform. -/
noncomputable def realLaw (p : Params) : PMF (List Bool) :=
  lawWith p fun B => do
    let s ← PMF.uniformOfFintype (Fin p.n → ZMod p.q)
    let e ← errorLaw p
    return fun j => (∑ i, s i * B i j) + e j

/-- The ideal law: `b = c ← Z_q^m` uniform. -/
noncomputable def idealLaw (p : Params) : PMF (List Bool) :=
  lawWith p fun _ => PMF.uniformOfFintype (Fin p.m → ZMod p.q)

/-- The plain LWE parameters at `(n, m, q, χ)` with a uniform secret. -/
def Params.toLWE (p : Params) : LWE.Params :=
  { n := p.n, m := p.m, q := p.q, error := .gauss p.χ, secret := .uniform, q_pos := p.q_pos }

/-- The claimed strength: that of plain decision LWE at `(n, m, q, χ)`, when `m ≥ 2 n ⌈log q⌉`
(the paper's condition), `ℓ ≥ 1` and `σ² ≥ n ⌈log q⌉²`; `0` otherwise. -/
def H (p : Params) : ℕ :=
  if 2 * p.n * p.k ≤ p.m ∧ 1 ≤ p.ℓ ∧ ((p.n * p.k ^ 2 : ℕ) : ℚ) ≤ p.σ ^ 2 ∧ 0 < p.σ then
    LWE.H p.toLWE
  else 0

/-- **Decision ℓ-succinct LWE**, with `H p` bits. -/
noncomputable def decision : Assumption where
  Params := Params
  problem p := Problem.decision (realLaw p) (idealLaw p)
  H := H

end AdvancedEncryption.WE.Assumptions.SuccinctLWE
