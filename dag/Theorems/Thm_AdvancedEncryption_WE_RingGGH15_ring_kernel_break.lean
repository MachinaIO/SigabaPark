import Mathlib.Algebra.Module.Defs
import Mathlib.Tactic.Common
import Mathlib.Tactic.Abel

/-- **Ring kernel break (note `pq-we-apg-width-ring-analysis`, §2).** CVW18 Lemma 5.10 treats the level secrets as public. Over a commutative ring with one secret per bit (module rank 1), the combination `s1 y0 - s0 y1` of the two targets `y_b = s_b a + e_b` removes the uniform `a` and leaves the short `s1 e0 - s0 e1`, at every ring degree. -/
theorem AdvancedEncryption.WE.RingGGH15.ring_kernel_break {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (s0 s1 : R) (a e0 e1 : M) :
    s1 • (s0 • a + e0) - s0 • (s1 • a + e1) = s1 • e0 - s0 • e1 := by sorry
