import Mathlib

theorem AdvancedEncryption.WE.FourierTerminal.clean_amplitude {R : Type} (rows : Finset R) (q : R → ℝ) (p : R → Bool) (D : R → Bool → ℝ) :
    ((∑ r ∈ rows, q r * (if p r then -(1-2*D r false) else (1-2*D r false))) +
     (∑ r ∈ rows, q r * (if p r then (1-2*D r true) else -(1-2*D r true)))) / 2 =
    ∑ r ∈ rows, q r * (D r (!(p r)) - D r (p r)) := by
  sorry
