import Definitions.Def_GGH15
import SigabaNeoStd.Lattices.Prob

open Matrix SigabaNeo SigabaNeo.Lattices AdvancedEncryption.WE.GGH15 Cslib.Probability

namespace EncodePathAux

theorem path_identity {R : Type} [CommRing R] {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] : ∀ {h : ℕ} (A : Fin (h + 1) → Matrix ι κ R)
    (S : Fin h → Bool → Matrix ι ι R) (E : Fin h → Bool → Matrix ι κ R)
    (D : Fin h → Bool → Matrix κ κ R),
    (∀ i b, A i.castSucc * D i b = S i b * A i.succ + E i b) → ∀ x : Fin h → Bool,
    A 0 * pathProd D x = pathProd S x * A (Fin.last h) +
      ∑ j : Fin h, ((List.ofFn fun i => S i (x i)).take j).prod * E j (x j) *
        ((List.ofFn fun i => D i (x i)).drop (j + 1)).prod
  | 0, A, S, E, D, _, x => by simp [pathProd]
  | h + 1, A, S, E, D, hyp, x => by
    have key := path_identity (fun i => A i.succ) (fun i => S i.succ) (fun i => E i.succ)
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

theorem indepFin_support {α : Type} : ∀ (n : ℕ) (d : Fin n → PMF α) {f : Fin n → α},
    f ∈ (indepFin n d).support → ∀ i, f i ∈ (d i).support
  | 0, _, _, _, i => i.elim0
  | n + 1, d, f, hf, i => by
    simp only [indepFin, PMF.support_bind, PMF.support_map, Set.mem_iUnion, Set.mem_image] at hf
    obtain ⟨a, ha, g, hg, rfl⟩ := hf
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using ha
    · simpa using indepFin_support n (fun i => d i.succ) hg j

theorem indep_support {κ α : Type} [Fintype κ] (d : κ → PMF α) {f : κ → α}
    (hf : f ∈ (indep d).support) (x : κ) : f x ∈ (d x).support := by
  simp only [indep, PMF.support_map, Set.mem_image] at hf
  obtain ⟨g, hg, rfl⟩ := hf
  have := indepFin_support _ _ hg (Fintype.equivFin κ x)
  simpa using this

theorem allSome_eq_some {κ α : Type} [Fintype κ] {f : κ → Option α} {g : κ → α}
    (h : allSome f = some g) (x : κ) : f x = some (g x) := by
  unfold allSome at h
  split_ifs at h with hs
  obtain rfl := Option.some.inj h
  simp

theorem preimageRows_mul {ι : Type} [Fintype ι] {m k q : ℕ} (A : Matrix ι (Fin m) (ZMod q))
    (Y : Matrix ι (Fin k) (ZMod q)) (σ : ℚ) {X : Matrix (Fin m) (Fin k) ℤ}
    (hX : some X ∈ (preimageRows A Y σ).support) : A * modq q X = Y := by
  unfold preimageRows at hX
  split_ifs at hX with hσ
  · unfold Trapdoor.preimage at hX
    rw [PMF.support_map] at hX
    obtain ⟨o, ho, hoT⟩ := hX
    have hs := support_sampleOptList _ o ho
    cases o with
    | none => cases hoT
    | some cols =>
      have hoT' := Option.some.inj hoT
      subst hoT'
      simp only at hs
      obtain ⟨hlen, hall⟩ := List.forall₂_iff_get.mp hs
      ext a j
      have hj : j.val < cols.length := by rw [hlen]; simp
      obtain ⟨d, hd, hx⟩ := hall j.val hj (by rw [← hlen]; exact hj)
      simp only [List.get_eq_getElem, List.getElem_map, List.getElem_finRange] at hd
      have hcol := cosetGauss_mem_coset _ _ _ _ hd hx
      have := congrFun hcol (Fintype.equivFin ι a)
      rw [Matrix.mulVec, dotProduct] at this
      simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply, id] at this
      rw [Matrix.mul_apply]
      refine Eq.trans ?_ this
      refine Finset.sum_congr rfl fun b _ => ?_
      show A a b * ((cols.getD j.val 0 b : ℤ) : ZMod q) = _
      rw [List.getD_eq_getElem _ _ hj]
      rfl
  · simp at hX

theorem encodeWith_spec {ι : Type} [Fintype ι] {h : ℕ} (p : Params)
    (A : Fin (h + 1) → Matrix ι (Fin p.m) (ZMod p.q)) (S : Fin h → Bool → Matrix ι ι ℤ)
    (E : Fin h → Bool → Matrix ι (Fin p.m) ℤ) {D : Fin h → Bool → Matrix (Fin p.m) (Fin p.m) ℤ}
    (hD : some D ∈ (encodeWith p A S E).support) (i : Fin h) (b : Bool) :
    A i.castSucc * modq p.q (D i b) = modq p.q (S i b) * A i.succ + modq p.q (E i b) := by
  unfold encodeWith preimages at hD
  rw [PMF.support_map] at hD
  obtain ⟨f, hf, hfD⟩ := hD
  dsimp only at hfD
  cases hg : allSome f with
  | none => rw [hg] at hfD; cases hfD
  | some g =>
    rw [hg] at hfD
    obtain rfl := Option.some.inj ((Option.map_some _ _).symm.trans hfD)
    have h1 := indep_support _ hf (i, b)
    rw [allSome_eq_some hg (i, b)] at h1
    exact preimageRows_mul _ _ _ h1


end EncodePathAux

open EncodePathAux in
theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] {h : ℕ} (p : Params)
    (S : Fin h → Bool → Matrix ι ι ℤ) (Ah : Matrix ι (Fin p.m) (ZMod p.q))
    {A : Fin (h + 1) → Matrix ι (Fin p.m) (ZMod p.q)}
    {D : Fin h → Bool → Matrix (Fin p.m) (Fin p.m) ℤ}
    (hmem : (A, some D) ∈ (encode p S Ah).support) :
    ∃ E : Fin h → Bool → Matrix ι (Fin p.m) ℤ, ∀ x : Fin h → Bool,
      A 0 * pathProd (fun i b => modq p.q (D i b)) x =
        pathProd (fun i b => modq p.q (S i b)) x * Ah +
        ∑ j : Fin h, ((List.ofFn fun i => modq p.q (S i (x i))).take j).prod *
          modq p.q (E j (x j)) *
          ((List.ofFn fun i => modq p.q (D i (x i))).drop (j + 1)).prod := by
  simp only [encode, bind, pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff,
    Prod.mk.injEq] at hmem
  obtain ⟨Alow, -, E, -, D', hD', rfl, hD⟩ := hmem
  subst hD
  refine ⟨E, fun x => ?_⟩
  have hlast : levelMats Alow Ah (Fin.last h) = Ah := by simp [levelMats]
  have := path_identity (levelMats Alow Ah) (fun i b => modq p.q (S i b))
    (fun i b => modq p.q (E i b)) (fun i b => modq p.q (D i b))
    (fun i b => encodeWith_spec p _ S E hD' i b) x
  rw [hlast] at this
  exact this
