import SigabaNeoStd.Lattices.LWE
import SigabaNeo.Trusted.Primitive
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary

/-!
# Decomposed LWE (Abram–Malavolta–Roy, CRYPTO 2025)

Definition 4.1 of Abram, Malavolta and Roy, *Key-Homomorphic Computations for RAM: Fully Succinct
Randomised Encodings and More* (ePrint 2025/339): for integer parameters `k, m, σ, σ̃, t, q` and
`n := k · log q`,

    (A_i, B_j, sᵀ A_i B_j + sᵀ G · δ_{i,j} + e_{i,j}ᵀ)_{i,j ∈ [t]} ≈_c (A_i, B_j, u_{i,j}ᵀ)_{i,j ∈ [t]}

with `A_i ← Z_q^{k×m}` and `s ← Z_q^k` uniform, `B_j ← D_σ^{m×n}` and `e_{i,j} ← D_σ̃^n` discrete
Gaussian over the integers, `u_{i,j} ← Z_q^n` uniform, `δ_{i,j}` the Kronecker delta, and
`G = I ⊗ gᵀ` the gadget matrix (§3.1). The paper writes `gᵀ = (1 2 … 2^{log q})`; with
`n = k · log q` the gadget has `log q` entries per row, so here `gᵀ = (1, 2, …, 2^{⌈log q⌉−1})` and
`n = k · ⌈log q⌉`. `B_j` is an integer matrix; the products `A_i B_j` and the samples are taken
mod `q`.

**Concrete form.** The real and ideal laws, encoded, as a decision problem. Widths follow the
convention of `SigabaNeoStd` (`ρ_s(x) = exp(−π x²/s²)`); a non-positive width gives the point
mass at `0`. Theorem 4.2 of the paper reduces this assumption to `t`-succinct LWE when
`m ≥ 2k log q`, `σ = √(k log q) · ω(√log m)`, `q` is prime and `σ̃/σ` is super-polynomial; the paper
conjectures `k log k / log α` bits for `m = 2k log q`, `σ = ω(√log k)`, `σ̃ = mσq/α`. The security
function claims the strength of plain decision LWE in dimension `k` with `t²·n` samples and error
width `σ̃` (`LWE.H`), and only in the regime of Theorem 4.2: `q` prime, `m ≥ 2k⌈log q⌉`,
`σ² ≥ k⌈log q⌉⌈log m⌉` (a concrete stand-in for `σ = √(k log q) · ω(√log m)`) and
`σ̃ ≥ 2^128 σ` (a concrete stand-in for a super-polynomial `σ̃/σ`); `0` otherwise. Even there,
Theorem 4.2 reduces only to `t`-succinct LWE, which has no known reduction from LWE, and the
estimator treats the `t²n` samples as having independent uniform matrices although the `A_i B_j`
share `B_j`. The claim is therefore a conjecture, open to Cryptanalysis AI.
-/

namespace AdvancedEncryption.WE.Assumptions.DecomposedLWE

open SigabaNeo SigabaNeo.Lattices Turing.MultiTapeTM Cslib.Probability

/-- The parameters `k, m, q, t, σ, σ̃`. -/
structure Params where
  k : ℕ
  m : ℕ
  q : ℕ
  t : ℕ
  σ : ℚ
  σt : ℚ
  q_pos : 0 < q := by decide

instance (p : Params) : NeZero p.q := ⟨p.q_pos.ne'⟩

/-- The gadget length `⌈log₂ q⌉`. -/
def Params.logq (p : Params) : ℕ := Nat.clog 2 p.q

/-- `n = k · ⌈log q⌉`. -/
def Params.n (p : Params) : ℕ := p.k * p.logq

/-- The gadget matrix `G = I_k ⊗ gᵀ ∈ Z_q^{k × n}`. -/
def gadget (p : Params) : Matrix (Fin p.k) (Fin p.n) (ZMod p.q) := fun a l =>
  let al := finProdFinEquiv.symm l
  if al.1 = a then (2 ^ al.2.val : ZMod p.q) else 0

/-- `D_s` over the integers (point mass at `0` if `s ≤ 0`). -/
noncomputable def gauss (s : ℚ) : PMF ℤ :=
  if h : 0 < s then gaussZ s (by exact_mod_cast h) else PMF.pure 0

/-- An instance: the `A_i`, the `B_j` and the `t × t` samples. -/
abbrev Instance (p : Params) : Type :=
  (Fin p.t → Matrix (Fin p.k) (Fin p.m) (ZMod p.q)) × (Fin p.t → Matrix (Fin p.m) (Fin p.n) ℤ) ×
    (Fin p.t → Fin p.t → Fin p.n → ZMod p.q)

/-- The encoding: the entries of the `A_i` (as naturals below `q`), of the `B_j` (as integers) and
of the samples, each list framed, in the order of `i`, then `j`, then entry. -/
def encode (p : Params) (x : Instance p) : List Bool :=
  encodeTuple [encList encNat ((List.ofFn x.1).flatMap matVals),
    encList encIntBin ((List.ofFn x.2.1).flatMap fun B =>
      (List.ofFn fun r => List.ofFn fun c => B r c).flatten),
    encList encNat ((List.ofFn fun i => List.ofFn fun j => List.ofFn fun l =>
      (x.2.2 i j l).val).flatten.flatten)]

/-- `A_i` uniform and `B_j ← D_σ^{m×n}`, then the samples from `(A, B)`. -/
noncomputable def lawWith (p : Params)
    (samples : (Fin p.t → Matrix (Fin p.k) (Fin p.m) (ZMod p.q)) →
      (Fin p.t → Matrix (Fin p.m) (Fin p.n) ℤ) → PMF (Fin p.t → Fin p.t → Fin p.n → ZMod p.q)) :
    PMF (List Bool) := do
  let A ← PMF.uniformOfFintype (Fin p.t → Matrix (Fin p.k) (Fin p.m) (ZMod p.q))
  let Bf ← sampleFun (ι := Fin p.t × Fin p.m × Fin p.n) (gauss p.σ)
  let B : Fin p.t → Matrix (Fin p.m) (Fin p.n) ℤ := fun j r c => Bf (j, r, c)
  let y ← samples A B
  return encode p (A, B, y)

/-- The real law: `y_{i,j} = sᵀ A_i B_j + sᵀ G δ_{i,j} + e_{i,j}ᵀ`, `s ← Z_q^k`,
`e_{i,j} ← D_σ̃^n`. -/
noncomputable def realLaw (p : Params) : PMF (List Bool) :=
  lawWith p fun A B => do
    let s ← PMF.uniformOfFintype (Fin p.k → ZMod p.q)
    let e ← sampleFun (ι := Fin p.t × Fin p.t × Fin p.n) (gauss p.σt)
    return fun i j l =>
      (∑ a, ∑ r, s a * A i a r * (B j r l : ZMod p.q)) +
        (if i = j then ∑ a, s a * gadget p a l else 0) + (e (i, j, l) : ZMod p.q)

/-- The ideal law: `u_{i,j} ← Z_q^n` uniform. -/
noncomputable def idealLaw (p : Params) : PMF (List Bool) :=
  lawWith p fun _ _ => PMF.uniformOfFintype (Fin p.t → Fin p.t → Fin p.n → ZMod p.q)

/-- Plain LWE in dimension `k` with `t²·n` samples, error width `σ̃`, uniform secret. -/
def Params.toLWE (p : Params) : LWE.Params :=
  { n := p.k, m := p.t * p.t * p.n, q := p.q, error := .gauss p.σt, secret := .uniform,
    q_pos := p.q_pos }

/-- The claimed strength: plain LWE's (`Params.toLWE`) in the regime of Theorem 4.2 (`q` prime,
`m ≥ 2k⌈log q⌉`, `σ² ≥ k⌈log q⌉⌈log m⌉`, `σ̃ ≥ 2^128 σ`, `σ > 0`, `t ≥ 1`); `0` otherwise. -/
def H (p : Params) : ℕ :=
  if p.q.Prime ∧ 2 * p.k * p.logq ≤ p.m ∧
      ((p.k * p.logq * Nat.clog 2 p.m : ℕ) : ℚ) ≤ p.σ ^ 2 ∧ 2 ^ 128 * p.σ ≤ p.σt ∧ 0 < p.σ ∧
      1 ≤ p.t then
    LWE.H p.toLWE
  else 0

/-- **Decomposed LWE**, with `H p` bits. -/
noncomputable def decision : Assumption where
  Params := Params
  problem p := Problem.decision (realLaw p) (idealLaw p)
  H := H

end AdvancedEncryption.WE.Assumptions.DecomposedLWE
