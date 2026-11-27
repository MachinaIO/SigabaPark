import Mathlib

theorem AdvancedEncryption.WE.JoinRoute.hidden_incidence_frame {E V G : Type} [AddCommGroup G] (dest : E → V) (key : V → G) (other : E → G) :
    Function.Bijective (fun (pad : E → G) (e : E) ↦ key (dest e) + other e + pad e) := by
  sorry
