import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Common

open Matrix

/-- **The rank condition of related-trapdoor LWE is necessary** (scalar case `n = 1` of the
generalized related-trapdoor LWE game, Waters–Wee–Wu, Assumption 4.1). The challenge is an LWE
sample `σ (u B) + e` along the row `u B`; the oracle returns preimages `y` with `(M B) y = t`. If
the query `M` contains the challenge direction (`u = c M`, i.e. `[u; M]` is not of full rank), then
`⟨σ (u B) + e, y⟩ = σ ⟨c, t⟩ + ⟨e, y⟩`: with a target `t` satisfying `⟨c, t⟩ = 0` the answer
removes the secret and the game is lost. The masked-leak lemma `ML_i` needs exactly such
preimages (children of the hidden row, with small targets on it), so no reduction can obtain them
from this oracle (note `pq-we-hinted-lattice-assumptions`, §2). -/
theorem AdvancedEncryption.WE.Hints.rank_condition_necessary {R κ L μ : Type*} [CommRing R]
    [Fintype κ] [Fintype L] [Fintype μ] (M : Matrix κ L R) (B : Matrix L μ R) (c : κ → R)
    (u : L → R) (hu : u = c ᵥ* M) (y : μ → R) (t : κ → R) (hy : (M * B) *ᵥ y = t)
    (σ : R) (e : μ → R) :
    (σ • (u ᵥ* B) + e) ⬝ᵥ y = σ * (c ⬝ᵥ t) + e ⬝ᵥ y := by sorry
