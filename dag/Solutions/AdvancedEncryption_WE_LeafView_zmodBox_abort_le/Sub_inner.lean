import Definitions.Def_RingBoxesCopy
import SigabaNeoStd.Lattices.BoxSampler

open SigabaNeo.Lattices AdvancedEncryption.WE.RingBoxesCopy
open scoped ENNReal

theorem solution {q m : ℕ} [NeZero q] {Y Z : Type} [AddCommGroup Y]
    (F : (Fin m → ZMod q) →+ Y) (dec : Y → Z) (T : Z → Fin m → ZMod q) (u : Y)
    (Bb s τ κ : ℕ) (hB : 2 ^ Bb ≤ q) (hB1 : 1 ≤ Bb)
    (hBig : (bigBox Bb hB : Finset (Fin m → ZMod q)).Nonempty)
    (hs : 2 ^ (Bb - 1) - 1 - τ ≤ s) (hτ : 4 * τ + 1 ≤ 2 ^ Bb)
    (hκ : m * (4 * τ + 1) * 2 ^ κ ≤ 2 ^ Bb)
    (hshift : ∀ y i, zabs (T (dec y) i) ≤ τ) :
    boxSample (bigBox Bb hB) hBig (ball q s) F dec T u none ≤ ((2 : ℝ≥0∞) ^ κ)⁻¹ := by
  have hpow : 2 ^ Bb = 2 * 2 ^ (Bb - 1) := by rw [← pow_succ']; congr 1; omega
  let r := 2 ^ (Bb - 1) - 1 - 2 * τ
  have hr : 2 * r < q := by dsimp [r]; omega
  apply (boxSample_none_le _ _ _ _ _ _ u (ball q r) ?_ ?_).trans
  · have hc := famAbort_le (Q := q) (P := Fin m) (N := 1) Bb τ κ hB hB1 hτ
      (by simpa using hκ)
    simpa only [card_bigBox, card_ball _ hr, card_famBig, card_famBall _ hr,
      Fintype.card_fin, mul_one, r] using hc
  · intro x hx
    apply ball_subset_bigBox Bb hB hB1
    exact mem_ball.mpr fun i ↦ (mem_ball.mp hx i).trans (by dsimp [r]; omega)
  · intro x hx y
    apply mem_ball.mpr
    intro i
    apply (zabs_sub_le _ _).trans
    have hi := mem_ball.mp hx i
    have ht := hshift y i
    dsimp [r] at hi
    omega
