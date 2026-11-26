import Definitions.Def_GGH15

open Matrix AdvancedEncryption.WE.GGH15

namespace PathIdentityAux

theorem go {R : Type} [CommRing R] {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] : ∀ {h : ℕ} (A : Fin (h + 1) → Matrix ι κ R)
    (S : Fin h → Bool → Matrix ι ι R) (E : Fin h → Bool → Matrix ι κ R)
    (D : Fin h → Bool → Matrix κ κ R),
    (∀ i b, A i.castSucc * D i b = S i b * A i.succ + E i b) → ∀ x : Fin h → Bool,
    A 0 * pathProd D x = pathProd S x * A (Fin.last h) +
      ∑ j : Fin h, ((List.ofFn fun i => S i (x i)).take j).prod * E j (x j) *
        ((List.ofFn fun i => D i (x i)).drop (j + 1)).prod
  | 0, A, S, E, D, _, x => by simp [pathProd]
  | h + 1, A, S, E, D, hyp, x => by
    have key := go (fun i => A i.succ) (fun i => S i.succ) (fun i => E i.succ)
      (fun i => D i.succ) (fun i b => by
        have := hyp i.succ b
        rw [← Fin.succ_castSucc] at this
        exact this) (fun i => x i.succ)
    simp only [pathProd] at key ⊢
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    simp only [Fin.val_zero, List.take_zero, List.prod_nil, Matrix.one_mul, zero_add,
      Fin.val_succ, List.take_succ_cons, List.prod_cons,
      List.drop_succ_cons]
    have h0 := hyp 0 (x 0)
    simp only [Fin.castSucc_zero] at h0
    rw [← Matrix.mul_assoc, h0, Matrix.add_mul, Matrix.mul_assoc, key, Fin.succ_last]
    simp only [Matrix.mul_add, Matrix.mul_sum, Matrix.mul_assoc, List.drop_zero]
    abel

end PathIdentityAux

theorem solution {R : Type} [CommRing R] {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] : ∀ {h : ℕ} (A : Fin (h + 1) → Matrix ι κ R)
    (S : Fin h → Bool → Matrix ι ι R) (E : Fin h → Bool → Matrix ι κ R)
    (D : Fin h → Bool → Matrix κ κ R),
    (∀ i b, A i.castSucc * D i b = S i b * A i.succ + E i b) → ∀ x : Fin h → Bool,
    A 0 * pathProd D x = pathProd S x * A (Fin.last h) +
      ∑ j : Fin h, ((List.ofFn fun i => S i (x i)).take j).prod * E j (x j) *
        ((List.ofFn fun i => D i (x i)).drop (j + 1)).prod
    :=
  PathIdentityAux.go
