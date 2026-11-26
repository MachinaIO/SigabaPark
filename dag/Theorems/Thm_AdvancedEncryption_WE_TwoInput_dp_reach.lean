import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Basic

theorem AdvancedEncryption.WE.TwoInput.dp_reach {S B : Type} [DecidableEq S] [Fintype S] [Fintype B]
    (h : S → B → S) (s0 : S) (R : ℕ → Finset S) (hR0 : R 0 = {s0})
    (hRs : ∀ n, R (n + 1) = (R n ×ˢ (Finset.univ : Finset B)).image (fun p => h p.1 p.2)) :
    (∀ n s, s ∈ R n ↔ ∃ ws : List B, ws.length = n ∧ ws.foldl h s0 = s) ∧
      ∀ n, (R n ×ˢ (Finset.univ : Finset B)).card ≤ Fintype.card S * Fintype.card B := by
  sorry
