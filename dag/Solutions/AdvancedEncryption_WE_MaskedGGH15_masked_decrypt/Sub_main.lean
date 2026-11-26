import Definitions.Def_WE_MaskedGGH15
import SigabaNeoStd.Lattices.Prob

open Matrix SigabaNeo SigabaNeo.Lattices AdvancedEncryption.WE.GGH15 AdvancedEncryption.WE.MaskedGGH15 Cslib.Probability

namespace MaskedDecryptAux

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


theorem encode_path_identity {ι : Type} [Fintype ι] [DecidableEq ι] {h : ℕ} (p : Params)
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


theorem cnfMat_pathProd_eq_zero_iff {w h : ℕ} (Ψ : CNF w h) (x : Fin h → Bool) :
    pathProd (cnfMat Ψ) x = 0 ↔ Sat Ψ x := by
  have hp : pathProd (cnfMat Ψ) x =
      diagonal fun j => ∏ i, (if Ψ j i (x i) then (0 : ℤ) else 1) :=
    pathProd_diagonal (fun i b j => if Ψ j i b then (0 : ℤ) else 1) x
  rw [hp, ← diagonal_zero, diagonal_eq_diagonal_iff]
  simp only [Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, ite_eq_left_iff,
    one_ne_zero, imp_false, not_not]
  rfl

theorem maskedSecret_mul {c : ℕ} {sh : Shape} (P P2 : Matrix (Fin c) (Fin c) ℤ)
    (R R2 : Matrix (Fin sh.dR) (Fin sh.dR) ℤ) (M M2 : Matrix (Fin sh.w) (Fin sh.w) ℤ)
    (S' S'2 : Matrix (Fin sh.n') (Fin sh.n') ℤ) (S S2 : Matrix (Fin sh.n) (Fin sh.n) ℤ) :
    maskedSecret P R M S' S * maskedSecret P2 R2 M2 S'2 S2 =
      maskedSecret (P * P2) (R * R2) (M * M2) (S' * S'2) (S * S2) := by
  simp only [maskedSecret, gammaTensor, fromBlocks_multiply, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]

theorem maskedSecret_one {c : ℕ} {sh : Shape} :
    maskedSecret (c := c) (sh := sh) 1 1 1 1 1 = 1 := by
  simp only [maskedSecret, gammaTensor]
  rw [show Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin c) (Fin c) ℤ)
      (1 : Matrix (Fin sh.dR) (Fin sh.dR) ℤ) = 1 from Matrix.one_kronecker_one,
    show Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin sh.w) (Fin sh.w) ℤ)
      (1 : Matrix (Fin sh.n') (Fin sh.n') ℤ) = 1 from Matrix.one_kronecker_one,
    fromBlocks_one, fromBlocks_one]

theorem pathProd_maskedSecret {c : ℕ} {sh : Shape} : ∀ {h : ℕ}
    (P : Fin h → Bool → Matrix (Fin c) (Fin c) ℤ) (R : Fin h → Matrix (Fin sh.dR) (Fin sh.dR) ℤ)
    (M : Fin h → Bool → Matrix (Fin sh.w) (Fin sh.w) ℤ)
    (S' : Fin h → Bool → Matrix (Fin sh.n') (Fin sh.n') ℤ)
    (S : Fin h → Bool → Matrix (Fin sh.n) (Fin sh.n) ℤ) (x : Fin h → Bool),
    pathProd (fun i b => maskedSecret (P i b) (R i) (M i b) (S' i b) (S i b)) x =
      maskedSecret (pathProd P x) (List.ofFn R).prod (pathProd M x) (pathProd S' x)
        (pathProd S x)
  | 0, P, R, M, S', S, x => by simp [pathProd, maskedSecret_one]
  | h + 1, P, R, M, S', S, x => by
    have ih := pathProd_maskedSecret (fun i => P i.succ) (fun i => R i.succ) (fun i => M i.succ)
      (fun i => S' i.succ) (fun i => S i.succ) (fun i => x i.succ)
    simp only [pathProd] at ih ⊢
    rw [List.ofFn_succ, List.prod_cons, ih, maskedSecret_mul]
    simp only [List.ofFn_succ, List.prod_cons]

theorem leftDiff_mul_maskedSecret {c : ℕ} {sh : Shape} (st : Fin c) (r0 : Fin sh.dR → ℤ)
    (jC : Fin sh.w → ℤ) (s0 : Fin sh.n' → ℤ) (P : Matrix (Fin c) (Fin c) ℤ)
    (R : Matrix (Fin sh.dR) (Fin sh.dR) ℤ) (M : Matrix (Fin sh.w) (Fin sh.w) ℤ)
    (S' : Matrix (Fin sh.n') (Fin sh.n') ℤ) (S : Matrix (Fin sh.n) (Fin sh.n) ℤ) :
    (leftO st r0 - leftC jC s0) * maskedSecret P R M S' S =
      Matrix.of fun _ => Sum.elim (fun sr => P st sr.1 * (r0 ᵥ* R) sr.2)
        (Sum.elim (fun kr => -((jC ᵥ* M) kr.1 * (s0 ᵥ* S') kr.2)) 0) := by
  ext j col
  rw [Matrix.mul_apply, Matrix.of_apply]
  rcases col with ⟨s, r⟩ | (⟨k, r⟩ | l)
  · simp only [Fintype.sum_sum_type, maskedSecret, fromBlocks_apply₁₁,
      fromBlocks_apply₂₁, Matrix.sub_apply, leftO, leftC, Sum.elim_inl, Sum.elim_inr,
      Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, sub_zero, gammaTensor,
      Matrix.kroneckerMap_apply, Fintype.sum_prod_type, vecMul, dotProduct]
    rw [Fintype.sum_eq_single st (fun x hx => by simp [hx]), Finset.mul_sum]
    refine Finset.sum_congr rfl fun r' _ => ?_
    simp only [↓reduceIte]
    ring
  · simp only [Fintype.sum_sum_type, maskedSecret, fromBlocks_apply₁₂,
      fromBlocks_apply₂₂, fromBlocks_apply₁₁, fromBlocks_apply₂₁, Matrix.sub_apply, leftO, leftC,
      Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, zero_add,
      add_zero, zero_sub, gammaTensor, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, vecMul,
      dotProduct, neg_mul, Finset.sum_neg_distrib]
    rw [Finset.sum_mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  · simp only [Fintype.sum_sum_type, maskedSecret, fromBlocks_apply₁₂,
      fromBlocks_apply₂₂, Matrix.sub_apply, leftO, leftC, Sum.elim_inl, Sum.elim_inr,
      Matrix.zero_apply, mul_zero, Finset.sum_const_zero, zero_add, sub_self, zero_mul,
      Pi.zero_apply]

theorem modq_mul {κ ν ρ : Type} [Fintype ν] (q : ℕ) (X : Matrix κ ν ℤ) (Y : Matrix ν ρ ℤ) :
    modq q X * modq q Y = modq q (X * Y) :=
  (Matrix.map_mul (f := Int.castRingHom (ZMod q))).symm

theorem pathProd_modq {κ : Type} [Fintype κ] [DecidableEq κ] (q : ℕ) : ∀ {h : ℕ}
    (X : Fin h → Bool → Matrix κ κ ℤ) (x : Fin h → Bool),
    pathProd (fun i b => modq q (X i b)) x = modq q (pathProd X x)
  | 0, X, x => by
    simp only [pathProd, List.ofFn_zero, List.prod_nil, modq]
    exact (Matrix.map_one _ Int.cast_zero Int.cast_one).symm
  | h + 1, X, x => by
    have ih := pathProd_modq q (fun i => X i.succ) (fun i => x i.succ)
    simp only [pathProd] at ih ⊢
    rw [List.ofFn_succ, List.prod_cons, ih, List.ofFn_succ, List.prod_cons]
    simp only [modq]
    exact (Matrix.map_mul (f := Int.castRingHom (ZMod q))).symm

end MaskedDecryptAux

open MaskedDecryptAux in
theorem solution (p : Params) {h : ℕ} {sh : Shape} (Ψ : CNF sh.w h) (r0 : Fin sh.dR → ℤ)
    (jC : Fin sh.w → ℤ) (s0 : Fin sh.n' → ℤ) (R : Fin h → Matrix (Fin sh.dR) (Fin sh.dR) ℤ)
    (S' : Fin h → Bool → Matrix (Fin sh.n') (Fin sh.n') ℤ)
    (S : Fin h → Bool → Matrix (Fin sh.n) (Fin sh.n) ℤ)
    (Ah : Matrix (Rows 1 sh) (Fin p.m) (ZMod p.q))
    {A : Fin (h + 1) → Matrix (Rows 1 sh) (Fin p.m) (ZMod p.q)}
    {D : Fin h → Bool → Matrix (Fin p.m) (Fin p.m) ℤ}
    (hmem : (A, some D) ∈ (encode p (fun i b => maskedSecret (c := 1) 1 (R i) (cnfMat Ψ i b)
      (S' i b) (S i b)) Ah).support) :
    ∃ E : Fin h → Bool → Matrix (Rows 1 sh) (Fin p.m) ℤ, ∀ x : Fin h → Bool, Sat Ψ x →
      modq p.q (leftO (c := 1) (sh := sh) 0 r0) * A 0 * pathProd (fun i b => modq p.q (D i b)) x -
        modq p.q (leftC (c := 1) (sh := sh) jC s0) * A 0 * pathProd (fun i b => modq p.q (D i b)) x =
      Matrix.of (fun _ => maskOf p.q r0 R (maskRows Ah)) +
        modq p.q (leftO (c := 1) (sh := sh) 0 r0 - leftC (c := 1) (sh := sh) jC s0) *
          ∑ j : Fin h, ((List.ofFn fun i => modq p.q (maskedSecret (c := 1) 1 (R i)
            (cnfMat Ψ i (x i)) (S' i (x i)) (S i (x i)))).take j).prod *
          modq p.q (E j (x j)) *
          ((List.ofFn fun i => modq p.q (D i (x i))).drop (j + 1)).prod := by
  obtain ⟨E, hE⟩ := encode_path_identity p _ Ah hmem
  refine ⟨E, fun x hx => ?_⟩
  have hsub : modq p.q (leftO (c := 1) (sh := sh) 0 r0 - leftC (c := 1) (sh := sh) jC s0) =
      modq p.q (leftO (c := 1) (sh := sh) 0 r0) - modq p.q (leftC (c := 1) (sh := sh) jC s0) := by
    ext i j; simp [modq]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.sub_mul, ← hsub, hE x, Matrix.mul_add,
    pathProd_modq, ← Matrix.mul_assoc]
  congr 1
  have hM : pathProd (cnfMat Ψ) x = 0 := (cnfMat_pathProd_eq_zero_iff Ψ x).mpr hx
  have hpp := pathProd_maskedSecret (c := 1) (sh := sh) (fun _ _ => 1) R (cnfMat Ψ) S' S x
  have h1 : pathProd (fun _ _ => (1 : Matrix (Fin 1) (Fin 1) ℤ)) x = 1 := by
    simp only [pathProd, List.ofFn_const, List.prod_replicate, one_pow]
  rw [hpp, h1, hM, modq_mul, leftDiff_mul_maskedSecret]
  ext j col
  simp only [modq, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero,
    add_zero, mul_zero, neg_zero, Fintype.sum_prod_type, maskOf, vecMul,
    dotProduct, maskRows, Matrix.one_apply_eq, one_mul]
  simp only [Matrix.zero_apply, mul_zero, Finset.sum_const_zero, neg_zero, Int.cast_zero,
    zero_mul, add_zero]
  rw [Fin.sum_univ_one]
  simp only [Matrix.one_apply_eq, one_mul]
