import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Fintype.Card

open Matrix

/-- Linear verification and its hash-proof key (Fredholm alternative over a field). A linear
check `M *ᵥ π = v` is satisfiable iff every key `k` with `k ᵥ* M = 0` also has `k ⬝ᵥ v = 0`.
In the WE-from-linear-verification template (encrypt `μ` as `(k ᵥ* M, k ⬝ᵥ v + μ)`, decrypt
with an accepting `π` as `(k ᵥ* M) ⬝ᵥ π`), the right-hand side fails exactly when some key
direction is invisible in `k ᵥ* M` but moves `k ⬝ᵥ v`. Used in the note
`pq-we-proof-system-routes`. -/
theorem AdvancedEncryption.WE.LinearVerif.check_alternative
    {K : Type*} [Field K] {r c : Type*} [Fintype r] [Fintype c] [DecidableEq r] [DecidableEq c]
    (M : Matrix r c K) (v : r → K) :
    (∃ π : c → K, M *ᵥ π = v) ↔ ∀ k : r → K, k ᵥ* M = 0 → k ⬝ᵥ v = 0 := by sorry
