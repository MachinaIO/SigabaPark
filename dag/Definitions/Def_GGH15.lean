import SigabaNeoStd.Lattices.Trapdoor
import SigabaNeoStd.Lattices.LWE
import SigabaNeo.Trusted.Primitive
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Matrix.Block
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option

/-!
# γ-GGH15 encodings (Chen–Vaikuntanathan–Wee, CRYPTO 2018, ePrint 2018/360, "CVW18")

Vocabulary for stating the open lemmas of the GGH15-based witness-encryption candidates of the
DAG (notes `pq-we-witness-prf-masked-evaluator`, `pq-we-masked-evaluator-mechanisms`,
`pq-we-masked-overcomplete-leaf`). Everything follows CVW18 §5.1, Construction 5.1
(γ-GGH15 encodings), with the following conventions.

* **Rows by type.** The level matrices `A_0, …, A_h ∈ Z_q^{t×m}` have their rows indexed by a
  finite type `ι` (`t = |ι|`), so that block-diagonal secrets (`γ_diag`, `γ_⊗diag` and the masked
  shapes of the candidates) are `Matrix.fromBlocks` of Kronecker products on sum and product
  types. Preimages are taken after renumbering the rows by `Fintype.equivFin ι`, which does not
  change any coset `{x : A x = y}`.
* **Ideal trapdoor sampling.** CVW18 sample `A_i, τ_i ← TrapSam(1^t, 1^m, q)` and
  `D ← A_{i−1}^{-1}(Y, σ)` with the trapdoor. Here `A_0, …, A_{h−1}` are uniform and `D` is drawn
  from the exact coset Gaussian `Trapdoor.preimage` (`SigabaNeoStd`): the ideal distribution
  `Trapdoor.ideal`, which a trapdoor sampler (`Trapdoor.Sampler`) reaches up to a negligible
  statistical distance [GPV08, MP12]. A preimage is `none` when a coset is empty (or `σ ≤ 0`).
* **Widths.** `σ` is the preimage width and the width of the secrets (`S_{i,b} ← D_{Z,σ}^{n×n}`,
  CVW18 Definition 3); `χ = D_{Z,χ}` is the error law of Construction 5.1. Widths use the
  convention of `SigabaNeoStd` (`ρ_s(x) = exp(−π x²/s²)`).

## Contents

* `indep`: independent draws from a family of laws; `gaussInt`, `gaussMat`, `uniformMat`.
* `preimageRows A Y σ`: `A^{-1}(Y, σ)` for row-indexed `A`.
* `target A S E i b = Ŝ_{i,b} A_{i+1} + E_{i,b}`; `preimages`; `encodeWith`; `encode` (CVW18
  Construction 5.1 with a given `A_h`): the law of `(A_0, …, A_h, {D_{i,b}})`.
* `pathProd`: the subset product `X_x = ∏_i X_{i, x_i}` (left to right).
* `gammaTensor`, `gammaDiag`, `gammaTensorDiag`: the three γ functions of CVW18 §5.1.
* `encodeD`: an encoding of the published family `{D_{i,b}}` as bits.
* `CloseAt D₀ D₁ k L W`: concrete-security closeness with an explicit loss, in the form of
  `SigabaNeo.Problem.HardAt`: every machine `A` has `2^k · gain ≤ L² · (cost A + W)`. With
  `L = 1, W = 0` it is `(Problem.decision D₀ D₁).HardAt k`.
-/

namespace AdvancedEncryption.WE.GGH15

open SigabaNeo SigabaNeo.Lattices Matrix
open Turing.MultiTapeTM Cslib.Probability

/-! ### Independent draws -/

/-- Independent draws `(a_0, …, a_{n−1})`, `a_i ← d i`. -/
noncomputable def indepFin {α : Type} : (n : ℕ) → (Fin n → PMF α) → PMF (Fin n → α)
  | 0, _ => PMF.pure finZeroElim
  | n + 1, d => (d 0).bind fun a => (indepFin n fun i => d i.succ).map fun f => Fin.cons a f

/-- Independent draws indexed by a finite type: `a_x ← d x` for every `x`. -/
noncomputable def indep {κ α : Type} [Fintype κ] (d : κ → PMF α) : PMF (κ → α) :=
  (indepFin (Fintype.card κ) fun i => d ((Fintype.equivFin κ).symm i)).map
    fun f x => f (Fintype.equivFin κ x)

/-- `D_{Z,s}` for a rational width `s` (the point mass at `0` if `s ≤ 0`). -/
noncomputable def gaussInt (s : ℚ) : PMF ℤ :=
  if h : 0 < s then gaussZ s (by exact_mod_cast h) else PMF.pure 0

/-- A matrix with independent `D_{Z,s}` entries. -/
noncomputable def gaussMat (κ ν : Type) [Fintype κ] [Fintype ν] (s : ℚ) : PMF (Matrix κ ν ℤ) :=
  indep fun _ : κ => indep fun _ : ν => gaussInt s

/-- A uniform matrix over `Z_q`. -/
noncomputable def uniformMat (κ ν : Type) [Fintype κ] [Fintype ν] [DecidableEq κ] [DecidableEq ν]
    (q : ℕ) [NeZero q] : PMF (Matrix κ ν (ZMod q)) :=
  PMF.uniformOfFintype (Matrix κ ν (ZMod q))

/-- All values present: `some` of the family if every value is `some`, else `none`. -/
noncomputable def allSome {κ α : Type} [Fintype κ] (f : κ → Option α) : Option (κ → α) :=
  open Classical in
  if h : ∀ x, (f x).isSome then some fun x => (f x).get (h x) else none

/-! ### Parameters and the encoding (CVW18 Construction 5.1) -/

/-- The parameters of Construction 5.1 other than the number of levels `h` and the rows `ι`:
columns `m`, modulus `q`, preimage (and secret) width `σ`, error width `χ`. -/
structure Params where
  m : ℕ
  q : ℕ
  σ : ℚ
  χ : ℚ
  q_pos : 0 < q := by decide

instance (p : Params) : NeZero p.q := ⟨p.q_pos.ne'⟩

/-- Reduce an integer matrix mod `q`. -/
def modq {κ ν : Type} (q : ℕ) (X : Matrix κ ν ℤ) : Matrix κ ν (ZMod q) := X.map (Int.cast)

/-- `A^{-1}(Y, σ)`: each column of `D ∈ Z^{m×k}` from the discrete Gaussian of width `σ` on the
coset `{x ∈ Z^m : A x = Y_j (mod q)}`, for `A` with rows indexed by `ι` (`none` if a coset is
empty or `σ ≤ 0`). -/
noncomputable def preimageRows {ι : Type} [Fintype ι] {m k q : ℕ}
    (A : Matrix ι (Fin m) (ZMod q)) (Y : Matrix ι (Fin k) (ZMod q)) (σ : ℚ) :
    PMF (Option (Matrix (Fin m) (Fin k) ℤ)) :=
  if h : 0 < σ then
    Trapdoor.preimage (A.submatrix (Fintype.equivFin ι).symm id)
      (Y.submatrix (Fintype.equivFin ι).symm id) σ (by exact_mod_cast h)
  else PMF.pure none

/-- The GGH15 target of level `i + 1` (levels are `1, …, h` in CVW18, `Fin h` here):
`Ŝ_{i+1,b} · A_{i+1} + E_{i+1,b} (mod q)`. -/
def target {ι : Type} [Fintype ι] {h m : ℕ} (q : ℕ) (A : Fin (h + 1) → Matrix ι (Fin m) (ZMod q))
    (S : Fin h → Bool → Matrix ι ι ℤ) (E : Fin h → Bool → Matrix ι (Fin m) ℤ) (i : Fin h)
    (b : Bool) : Matrix ι (Fin m) (ZMod q) :=
  modq q (S i b) * A i.succ + modq q (E i b)

/-- Independent preimages `D_{i,b} ← A'_i^{-1}(Y_{i,b}, σ)` for all `i < h`, `b`; `none` if one is
unavailable. In Construction 5.1, `A'_i = A_{i}` (CVW18's `A_{i−1}` for level `i`) and `Y = target`. -/
noncomputable def preimages {ι : Type} [Fintype ι] {h m : ℕ} (q : ℕ) (σ : ℚ)
    (A' : Fin h → Matrix ι (Fin m) (ZMod q)) (Y : Fin h → Bool → Matrix ι (Fin m) (ZMod q)) :
    PMF (Option (Fin h → Bool → Matrix (Fin m) (Fin m) ℤ)) :=
  (indep fun ib : Fin h × Bool => preimageRows (A' ib.1) (Y ib.1 ib.2) σ).map
    fun f => (allSome f).map fun g i b => g (i, b)

/-- The encodings for given level matrices, secrets `Ŝ_{i,b}` and errors:
`D_{i,b} ← A_{i−1}^{-1}(Ŝ_{i,b} A_i + E_{i,b}, σ)` (CVW18 Construction 5.1, third bullet). -/
noncomputable def encodeWith {ι : Type} [Fintype ι] {h : ℕ} (p : Params)
    (A : Fin (h + 1) → Matrix ι (Fin p.m) (ZMod p.q)) (S : Fin h → Bool → Matrix ι ι ℤ)
    (E : Fin h → Bool → Matrix ι (Fin p.m) ℤ) :
    PMF (Option (Fin h → Bool → Matrix (Fin p.m) (Fin p.m) ℤ)) :=
  preimages p.q p.σ (fun i => A i.castSucc) (target p.q A S E)

/-- The level matrices from `A_0, …, A_{h−1}` and the given top matrix `A_h`. -/
def levelMats {ι : Type} {h m q : ℕ} (Alow : Fin h → Matrix ι (Fin m) (ZMod q))
    (Ah : Matrix ι (Fin m) (ZMod q)) : Fin (h + 1) → Matrix ι (Fin m) (ZMod q) :=
  fun i => if hi : (i : ℕ) < h then Alow ⟨i, hi⟩ else Ah

/-- The errors `E_{i,b} ← χ^{t×m}`, independent. -/
noncomputable def errorLaw (ι : Type) [Fintype ι] (h : ℕ) (p : Params) :
    PMF (Fin h → Bool → Matrix ι (Fin p.m) ℤ) :=
  indep fun _ : Fin h => indep fun _ : Bool => gaussMat ι (Fin p.m) p.χ

/-- **CVW18 Construction 5.1** (`ggh.encode`, ideal trapdoor sampling), for secrets
`Ŝ_{i,b} = γ(M_{i,b}, S_{i,b})` already computed and a given `A_h`: uniform
`A_0, …, A_{h−1}`, errors `E_{i,b} ← χ^{t×m}`, `D_{i,b} ← A_{i−1}^{-1}(Ŝ_{i,b} A_i + E_{i,b}, σ)`.
Returns all level matrices (the caller publishes what the scheme publishes, e.g. `J·A_0`) and the
encodings. -/
noncomputable def encode {ι : Type} [Fintype ι] [DecidableEq ι] {h : ℕ} (p : Params)
    (S : Fin h → Bool → Matrix ι ι ℤ) (Ah : Matrix ι (Fin p.m) (ZMod p.q)) :
    PMF ((Fin (h + 1) → Matrix ι (Fin p.m) (ZMod p.q)) ×
      Option (Fin h → Bool → Matrix (Fin p.m) (Fin p.m) ℤ)) := do
  let Alow ← PMF.uniformOfFintype (Fin h → Matrix ι (Fin p.m) (ZMod p.q))
  let E ← errorLaw ι h p
  let A := levelMats Alow Ah
  let D ← encodeWith p A S E
  return (A, D)

/-- The subset product `X_x = X_{0,x_0} X_{1,x_1} ⋯ X_{h−1,x_{h−1}}` along the path `x`. -/
def pathProd {R : Type} [Semiring R] {κ : Type} [Fintype κ] [DecidableEq κ] {h : ℕ}
    (X : Fin h → Bool → Matrix κ κ R) (x : Fin h → Bool) : Matrix κ κ R :=
  (List.ofFn fun i => X i (x i)).prod

/-! ### The γ functions of CVW18 §5.1 ("Interesting γ functions") -/

/-- `γ_⊗(M, S) = M ⊗ S`. -/
def gammaTensor {R : Type} [Mul R] {w n : Type} (M : Matrix w w R) (S : Matrix n n R) :
    Matrix (w × n) (w × n) R :=
  Matrix.kroneckerMap (· * ·) M S

/-- `γ_diag(M, S) = diag(M, S)`. -/
def gammaDiag {R : Type} [Zero R] {w n : Type} (M : Matrix w w R) (S : Matrix n n R) :
    Matrix (w ⊕ n) (w ⊕ n) R :=
  Matrix.fromBlocks M 0 0 S

/-- `γ_⊗diag(M, S) = diag(M ⊗ S, S)`. -/
def gammaTensorDiag {R : Type} [MulZeroClass R] {w n : Type} (M : Matrix w w R)
    (S : Matrix n n R) : Matrix ((w × n) ⊕ n) ((w × n) ⊕ n) R :=
  Matrix.fromBlocks (gammaTensor M S) 0 0 S

/-! ### Bits -/

/-- A `Z_q` matrix as bits: its entries as numbers below `q`, row by row. -/
noncomputable def encodeZq {κ ν : Type} [Fintype κ] [Fintype ν] {q : ℕ} (X : Matrix κ ν (ZMod q)) :
    List Bool :=
  encList encNat (matVals (X.submatrix (Fintype.equivFin κ).symm (Fintype.equivFin ν).symm))

/-- A `Z_q` row vector as bits. -/
noncomputable def encodeVec {ν : Type} [Fintype ν] {q : ℕ} (v : ν → ZMod q) : List Bool :=
  encList encNat (List.ofFn fun j => (v ((Fintype.equivFin ν).symm j)).val)

/-- The published encodings `{D_{i,b}}` (or nothing) as bits: for each level the columns of
`D_{i,0}`, then those of `D_{i,1}`, entries in binary. -/
def encodeD {h m : ℕ} (D : Option (Fin h → Bool → Matrix (Fin m) (Fin m) ℤ)) : List Bool :=
  encOption (encList (encList (encList encIntBin)))
    (D.map fun D => (List.finRange h).flatMap fun i =>
      [Trapdoor.cols (D i false), Trapdoor.cols (D i true)])

/-! ### Concrete-security closeness -/

/-- **Closeness with an explicit loss.** Every machine `A` distinguishing `D₀` from `D₁` has
`2^k · gain ≤ L² · (cost A + W)`, where the gain is the squared advantage
(`SigabaNeo.Problem.gain` of `Problem.decision D₀ D₁`). This is the form a hybrid or a reduction
from a `k`-bit premise produces: the advantage grows by the factor `L` and the reduction adds the
cost `W`. With `L = 1` and `W = 0` it is exactly `(Problem.decision D₀ D₁).HardAt k`. -/
def CloseAt (D₀ D₁ : PMF (List Bool)) (k : ℕ) (L W : ℕ) : Prop :=
  ∀ A : Machine, (2 : ℝ) ^ k * (Problem.decision D₀ D₁).gain A ≤ (L : ℝ) ^ 2 * (A.cost + W)

end AdvancedEncryption.WE.GGH15
