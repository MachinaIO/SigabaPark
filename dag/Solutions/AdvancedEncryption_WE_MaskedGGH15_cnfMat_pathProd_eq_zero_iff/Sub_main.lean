import Definitions.Def_WE_MaskedGGH15

open Matrix SigabaNeo SigabaNeo.Lattices AdvancedEncryption.WE.GGH15 AdvancedEncryption.WE.MaskedGGH15

namespace CnfAux

theorem pathProd_diagonal {w : ℕ} : ∀ {h : ℕ} (d : Fin h → Bool → Fin w → ℤ) (x : Fin h → Bool),
    pathProd (fun i b => diagonal (d i b)) x = diagonal fun j => ∏ i, d i (x i) j
  | 0, d, x => by simp [pathProd]
  | h + 1, d, x => by
    have ih := pathProd_diagonal (fun i => d i.succ) (fun i => x i.succ)
    simp only [pathProd] at ih ⊢
    rw [List.ofFn_succ, List.prod_cons, ih, diagonal_mul_diagonal]
    congr 1
    funext j
    rw [Fin.prod_univ_succ]

end CnfAux

open CnfAux in
theorem solution {w h : ℕ} (Ψ : CNF w h) (x : Fin h → Bool) :
    pathProd (cnfMat Ψ) x = 0 ↔ Sat Ψ x := by
  have hp : pathProd (cnfMat Ψ) x =
      diagonal fun j => ∏ i, (if Ψ j i (x i) then (0 : ℤ) else 1) :=
    pathProd_diagonal (fun i b j => if Ψ j i b then (0 : ℤ) else 1) x
  rw [hp, ← diagonal_zero, diagonal_eq_diagonal_iff]
  simp only [Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, ite_eq_left_iff,
    one_ne_zero, imp_false, not_not]
  rfl
