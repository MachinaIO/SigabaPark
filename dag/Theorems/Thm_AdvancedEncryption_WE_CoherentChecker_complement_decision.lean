import Mathlib

theorem AdvancedEncryption.WE.CoherentChecker.complement_decision (delta ca cr qa qr q pairs p : ℝ)
    (acc : delta = 2*ca + qa) (rej : -delta = 2*cr + qr)
    (qa0 : 0 ≤ qa) (qr0 : 0 ≤ qr) (count : 2*pairs = q*(q-1))
    (ba : |ca| ≤ q*(2*p) + pairs*(4*p))
    (br : |cr| ≤ q*(2*p) + pairs*(4*p)) : |delta| ≤ 4*q^2*p := by
  sorry
