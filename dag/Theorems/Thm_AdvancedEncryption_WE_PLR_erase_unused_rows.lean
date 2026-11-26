import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Common

open Matrix Module

/-- **ERASE: unused hidden rows.** Step 5 of the ERASE lemma (note
`pq-we-plr-hop-rank-and-erase`, §3, on PR #56): a uniform hidden matrix `U` (`k` rows) enters the
published view only through `|ι|` linearly independent row combinations `C · U`, each padding a
hidden value (the rows of `W`, e.g. the eq-chain contribution `c · U^{eq,k}` with `c ≠ 0` is the
case `|ι| = 1`). Then every value of `C · U` is hit by exactly `|K|^((k − |ι|) n)` matrices `U`,
so the padded view `C · U + W` is uniform and its law does not depend on `W`: summing any test
function `F` over all `U` gives `|K|^((k − |ι|) n)` times the uniform sum. -/
theorem AdvancedEncryption.WE.PLR.erase_unused_rows {K : Type*} [Field K] [Fintype K] [DecidableEq K] {ι β : Type*} [Fintype ι]
    [DecidableEq ι] [AddCommMonoid β] {k n : ℕ} (C : Matrix ι (Fin k) K)
    (hC : C.rank = Fintype.card ι) :
    (∀ R : Matrix ι (Fin n) K,
      (Finset.univ.filter (fun U : Matrix (Fin k) (Fin n) K => C * U = R)).card =
        Fintype.card K ^ ((k - Fintype.card ι) * n)) ∧
    ∀ (W : Matrix ι (Fin n) K) (F : Matrix ι (Fin n) K → β),
      ∑ U : Matrix (Fin k) (Fin n) K, F (C * U + W) =
        (Fintype.card K ^ ((k - Fintype.card ι) * n)) • ∑ R : Matrix ι (Fin n) K, F R := by sorry
