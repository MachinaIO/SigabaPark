import Mathlib.LinearAlgebra.Matrix.Rank

/-- **Merged path secrets are linearly dependent.** Over a field, if `d + 1` row vectors factor
through a common `d × N` matrix, `s_x = u_x T` (rows of `U * T` with `U` of width `d`), they are
linearly dependent. In the positional GGH15 witness-encryption candidate the path secrets of
witnesses `x y` that share a suffix factor `T_y` behind one state of LWE dimension `d` have this
form in the merged hybrid, while a split gives a fresh factor `T'_y` to one prefix; exact secrets
recovered by decryption therefore distinguish merged from split for statements with enough
structured witnesses. This is the distinguisher behind the SZK-type barrier for the split lemma
(note `pq-we-split-lemma-attempts`). -/
theorem AdvancedEncryption.WE.Split.merged_secrets_dependent {K ι : Type*} [Field K] [Fintype ι]
    {d : ℕ} (U : Matrix (Fin (d + 1)) (Fin d) K) (T : Matrix (Fin d) ι K) :
    ¬ LinearIndependent K (fun i => (U * T) i) := by sorry
