import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Common

/-- **Width condition for leaf-first LWE steps (note `pq-we-exposed-root-reachable-lemma`, §6).**
CVW18 Lemma 5.10 (phase 1) uses LWE with secret `a` (rows of a slot of `A_i`) and the short
public matrix `S = [S_{i,0}; S_{i,1}]` (`2n'` rows, `n'` columns). A nonzero integer left-kernel
vector `z` of `S` exists, and exact linear algebra (Cramer's rule) finds one with entries at most
the Hadamard bound `(√n' ‖S‖)^{n'}`. Then `z (S a + E) = z E` is small whenever
`n' log₂(√n' ‖S‖) ≪ log q`, so the LWE instance is distinguishable in polynomial time. With
`n' ≈ 2^{10}` and `log q ≈ 2^{16.5}` (the APG parameters) this is the case, so every phase-1 step
needs `n' ≈ λ log q / O(1)`, as CVW18 Remark 7.2 requires (`n = Ω(λ log q)`). -/
theorem AdvancedEncryption.WE.ExposedRoot.phase_one_kernel_break {R : Type*} [Ring R] {a b c d : Type*}
    [Fintype b] [Fintype c]
    (z : Matrix a b R) (S : Matrix b c R) (A : Matrix c d R) (E : Matrix b d R)
    (hz : z * S = 0) :
    z * (S * A + E) = z * E := by sorry
