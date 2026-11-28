import Definitions.Def_LatticeAttack_Research_Wall1_FourHitSeries
import Definitions.Def_LatticeAttack_Research_Wall1_RawFourRecurrence

set_option autoImplicit true

/-! The actual four-hit series has the cancellation-compatible quartic form. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SigabaNeo.Wall1.RawPrefixOccupancy
open Finset PowerSeries ControlledPlane TerminalProjection FourHitSeries TripleHitSeries
open scoped Classical

theorem inputHitSeries_four_eq_corrected {k : ℕ} (hk : k ≤ 512)
    (T : Finset (Candidate k)) (s : Fin 4 → Fin k → ℤ)
    (hc : ∀ j i, -1664 ≤ s j i ∧ s j i ≤ 1664) (hi : Function.Injective s) :
    let P := fun j (p : Sample × Column) ↦ inputHit hk T p.1 p.2 (s j)
    inputHitSeries hk T {s 0,s 1,s 2,s 3} =
      (1+C (eventProbability (P 0))*X)*(1+C (eventProbability (P 1))*X)*
      (1+C (eventProbability (P 2))*X)*(1+C (eventProbability (P 3))*X) +
      C (tripleEventDefect (P 1) (P 2) (P 3) + tripleEventDefect (P 0) (P 2) (P 3) +
         tripleEventDefect (P 0) (P 1) (P 3) + tripleEventDefect (P 0) (P 1) (P 2))*X^3 +
      C (connectedFourthDefect (P 0) (P 1) (P 2) (P 3) +
        eventProbability (P 0) * tripleEventDefect (P 1) (P 2) (P 3) +
        eventProbability (P 1) * tripleEventDefect (P 0) (P 2) (P 3) +
        eventProbability (P 2) * tripleEventDefect (P 0) (P 1) (P 3) +
        eventProbability (P 3) * tripleEventDefect (P 0) (P 1) (P 2))*X^4 := by
  dsimp only
  have he : inputHitSeries hk T {s 0,s 1,s 2,s 3} =
      fourSeries (fun p : Sample × Column ↦ inputHit hk T p.1 p.2 (s 0))
        (fun p ↦ inputHit hk T p.1 p.2 (s 1))
        (fun p ↦ inputHit hk T p.1 p.2 (s 2))
        (fun p ↦ inputHit hk T p.1 p.2 (s 3)) := by
    simp [inputHitSeries, fourSeries, mul_assoc,
      hi.ne (by decide : (0 : Fin 4) ≠ 1),
      hi.ne (by decide : (0 : Fin 4) ≠ 2),
      hi.ne (by decide : (0 : Fin 4) ≠ 3),
      hi.ne (by decide : (1 : Fin 4) ≠ 2),
      hi.ne (by decide : (1 : Fin 4) ≠ 3),
      hi.ne (by decide : (2 : Fin 4) ≠ 3)]
  rw [he]
  apply fourSeries_eq_corrected
  · exact inputHit_pair_probability hk T _ _ (hc 0) (hc 1) (hi.ne (by decide))
  · exact inputHit_pair_probability hk T _ _ (hc 0) (hc 2) (hi.ne (by decide))
  · exact inputHit_pair_probability hk T _ _ (hc 0) (hc 3) (hi.ne (by decide))
  · exact inputHit_pair_probability hk T _ _ (hc 1) (hc 2) (hi.ne (by decide))
  · exact inputHit_pair_probability hk T _ _ (hc 1) (hc 3) (hi.ne (by decide))
  · exact inputHit_pair_probability hk T _ _ (hc 2) (hc 3) (hi.ne (by decide))

end SigabaNeo.Wall1.RawPrefixOccupancy
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.inputHitSeries_four_eq_corrected
