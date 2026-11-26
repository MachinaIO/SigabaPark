import SigabaNeoStd.Lattices.BoxSampler
import SigabaNeoStd.Lattices.LeftoverHash
import SigabaNeoStd.Lattices.Homomorphic.Eval
import CslibFrontier.Probability.Product
import SigabaNeoStd.Lattices.Boxes
import SigabaNeoStd.Lattices.Homomorphic.NoiseBound
import Definitions.Def_WE_EncryptorSetup
import Theorems.Thm_AdvancedEncryption_WE_LeafView_leafView_close_zmod


namespace LeafAux

open Matrix SigabaNeo.Lattices Cslib.Probability AdvancedEncryption.WE.Assumptions.SuccinctLWE
  AdvancedEncryption.WE.EncryptorSetup
open scoped ENNReal Matrix

/-- Outputs of `preimage M P` are preimages of `P`. -/
theorem preimage_mul {r c m' q : ℕ} (M : Matrix (Fin r) (Fin m') (ZMod q))
    (P : Matrix (Fin r) (Fin c) (ZMod q)) (τ : ℝ) (hτ : 0 < τ) {T : Matrix (Fin m') (Fin c) ℤ}
    (hT : some T ∈ (Trapdoor.preimage M P τ hτ).support) :
    M * T.map (fun z => (z : ZMod q)) = P := by
  unfold Trapdoor.preimage at hT
  rw [PMF.support_map] at hT
  obtain ⟨o, ho, hoT⟩ := hT
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
    have hcol := cosetGauss_mem_coset M _ τ hτ hd hx
    have := congrFun hcol a
    rw [Matrix.mulVec, dotProduct] at this
    rw [Matrix.mul_apply]
    refine Eq.trans ?_ this
    refine Finset.sum_congr rfl fun b _ => ?_
    show M a b * (((cols.getD j.val 0) b : ℤ) : ZMod q) = _
    rw [List.getD_eq_getElem _ _ hj]
    rfl

theorem sum_split {R : Type} [AddCommMonoid R] {ℓ m : ℕ} (z : Fin (ℓ * m + m) → R) :
    ∑ k, z k = ∑ i : Fin ℓ, ∑ j : Fin m, z (idxB i j) + ∑ j : Fin m, z (idxW j) := by
  rw [Fin.sum_univ_add]
  congr 1
  rw [← Fintype.sum_prod_type', ← finProdFinEquiv.sum_comp]
  rfl

theorem stacked_idxB {n m q ℓ : ℕ} (B : Matrix (Fin n) (Fin m) (ZMod q))
    (W : Matrix (Fin (ℓ * n)) (Fin m) (ZMod q)) (a b : Fin ℓ) (t : Fin n) (j : Fin m) :
    stacked B W (finProdFinEquiv (a, t)) (idxB b j) = if a = b then B t j else 0 := by
  have h : (idxB b j : Fin (ℓ * m + m)).val < ℓ * m := (finProdFinEquiv (b, j)).isLt
  unfold stacked
  rw [dif_pos h]
  have : (⟨(idxB b j).val, h⟩ : Fin (ℓ * m)) = finProdFinEquiv (b, j) := Fin.ext rfl
  rw [this]
  simp [AdvancedEncryption.WE.Assumptions.SuccinctLWE.blockDiag]

theorem stacked_idxW {n m q ℓ : ℕ} (B : Matrix (Fin n) (Fin m) (ZMod q))
    (W : Matrix (Fin (ℓ * n)) (Fin m) (ZMod q)) (r : Fin (ℓ * n)) (j : Fin m) :
    stacked B W r (idxW j) = W r j := by
  simp [stacked, idxW]

/-- **The block identity on the support of `Def_SuccinctLWE`'s setup**: whenever `T` passes the
check, `B T_B[i,j] + W_i T_W[j] = δ_{ij} G`. -/
theorem leaf_block (p : Params) (E : ℕ) (B : Matrix (Fin p.n) (Fin p.m) (ZMod p.q))
    (WT : (Fin p.ℓ → Matrix (Fin p.n) (Fin p.m) (ZMod p.q)) ×
      Option (Matrix (Fin (p.ℓ * p.m + p.m)) (Fin (p.ℓ * (p.n * p.k))) ℤ))
    (hWT : WT ∈ (leafSetup p B).support) (hg : leafGood E WT.2) (i j : Fin p.ℓ) :
    B * leafTB WT.2 i j + WT.1 i * leafTW WT.2 j =
      if i = j then AdvancedEncryption.WE.Assumptions.SuccinctLWE.gadget p.n p.k p.q else 0 := by
  unfold leafSetup at hWT
  rw [PMF.mem_support_bind_iff] at hWT
  obtain ⟨W, -, hW⟩ := hWT
  rw [PMF.support_map] at hW
  obtain ⟨T, hT, rfl⟩ := hW
  obtain ⟨T', rfl, -⟩ := hg
  unfold trapdoorLaw at hT
  split_ifs at hT with hσ
  swap
  · simp at hT
  have hmul := preimage_mul _ _ _ _ hT
  ext r c
  have := congrFun (congrFun hmul (finProdFinEquiv (i, r))) (finProdFinEquiv (j, c))
  rw [Matrix.mul_apply, sum_split] at this
  rw [Finset.sum_eq_single i (fun b _ hb => by
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [stacked_idxB, if_neg (Ne.symm hb), zero_mul]) (by simp)] at this
  simp only [stacked_idxB, if_true, stacked_idxW, Matrix.map_apply] at this
  have hrhs : blockDiag (ℓ := p.ℓ) (AdvancedEncryption.WE.Assumptions.SuccinctLWE.gadget p.n p.k p.q)
      (finProdFinEquiv (i, r)) (finProdFinEquiv (j, c)) =
      (if i = j then AdvancedEncryption.WE.Assumptions.SuccinctLWE.gadget p.n p.k p.q else 0) r c := by
    simp only [AdvancedEncryption.WE.Assumptions.SuccinctLWE.blockDiag, Equiv.symm_apply_apply]
    split_ifs <;> rfl
  rw [hrhs] at this
  rw [← this, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
  rfl

theorem sum_bits (x : ℕ) : ∀ k : ℕ, ∑ t : Fin k, 2 ^ t.val * (x / 2 ^ t.val % 2) = x % 2 ^ k
  | 0 => by simp [Nat.mod_one]
  | k + 1 => by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [sum_bits x k, Nat.mod_pow_succ]

theorem bits_mem {r k q : ℕ} (v : Fin r → ZMod q) (j : Fin (r * k)) :
    0 ≤ bits (k := k) v j ∧ bits (k := k) v j ≤ 1 := by
  unfold bits
  constructor
  · positivity
  · have := Nat.mod_lt ((v (finProdFinEquiv.symm j).1).val / 2 ^ (finProdFinEquiv.symm j).2.val)
      (show 2 > 0 by norm_num)
    omega

theorem gadget_bits {r k q : ℕ} [NeZero q] (hq : q ≤ 2 ^ k) (v : Fin r → ZMod q) :
    AdvancedEncryption.WE.Assumptions.SuccinctLWE.gadget r k q *ᵥ
      (fun j => ((bits (k := k) v j : ℤ) : ZMod q)) = v := by
  funext i
  rw [Matrix.mulVec, dotProduct, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type,
    Finset.sum_eq_single i]
  · have hv : (v i).val % 2 ^ k = (v i).val :=
      Nat.mod_eq_of_lt (lt_of_lt_of_le (ZMod.val_lt (v i)) hq)
    have h := congrArg (fun z : ℕ => (z : ZMod q)) (sum_bits (v i).val k)
    simp only [hv, ZMod.natCast_zmod_val] at h
    rw [← h, Nat.cast_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [AdvancedEncryption.WE.Assumptions.SuccinctLWE.gadget, bits,
      Equiv.symm_apply_apply, if_true, Int.cast_natCast, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat]
  · intro b _ hb
    refine Finset.sum_eq_zero fun t _ => ?_
    simp [AdvancedEncryption.WE.Assumptions.SuccinctLWE.gadget, hb]
  · simp

theorem zabs_bits_le {r k q : ℕ} [NeZero q] (v : Fin r → ZMod q) (c : Fin (r * k)) :
    zabs (((bits (k := k) v c : ℤ) : ZMod q)) ≤ 1 := by
  refine (zabs_intCast_le _).trans ?_
  have h := bits_mem (k := k) v c
  omega

/-- **A `ℤ_q` gadget for the leaf lemma**: `G = gadget n k q` (the `G` of `Def_SuccinctLWE`) with
binary decompositions, entries at most `1`. -/
theorem succ_gadget_exists (n k q : ℕ) [NeZero q] (hq : q ≤ 2 ^ k) :
    ∃ Γ : GadgetMatrix (ZMod q) (Fin n) (Fin (n * k)),
      Γ.G = AdvancedEncryption.WE.Assumptions.SuccinctLWE.gadget n k q ∧
      (∀ A c c', zabs (Γ.ginv A c c') ≤ 1) ∧
      ∃ dec : (Fin n → ZMod q) → (Fin (n * k) → ZMod q),
        (∀ y, Γ.G *ᵥ dec y = y) ∧ ∀ y c, zabs (dec y c) ≤ 1 := by
  refine ⟨⟨AdvancedEncryption.WE.Assumptions.SuccinctLWE.gadget n k q,
    fun A => Matrix.of fun c col => ((bits (k := k) (fun r => A r col) c : ℤ) : ZMod q),
    fun A => ?_⟩, rfl, fun A c c' => zabs_bits_le _ _,
    fun y c => ((bits (k := k) y c : ℤ) : ZMod q), fun y => gadget_bits hq y,
    fun y c => zabs_bits_le _ _⟩
  ext r col
  have := congrFun (gadget_bits (r := n) hq (fun r => A r col)) r
  rw [Matrix.mul_apply]
  rw [Matrix.mulVec, dotProduct] at this
  exact this

theorem leaf_good {ℓ m nk q : ℕ} [NeZero q] (E : ℕ)
    (T : Option (Matrix (Fin (ℓ * m + m)) (Fin (ℓ * nk)) ℤ)) (hT : leafGood E T) :
    (∀ i j a c, zabs (leafTB (q := q) T i j a c) ≤ E) ∧ ∀ j a c, zabs (leafTW (q := q) T j a c) ≤ E := by
  obtain ⟨T', rfl, hT'⟩ := hT
  have key : ∀ a b, zabs (((T' a b : ℤ) : ZMod q)) ≤ E := by
    intro a b
    refine (zabs_intCast_le _).trans ?_
    have h1 : ((T' a b).natAbs : ℤ) ≤ E := by rw [Int.natCast_natAbs]; exact hT' a b
    exact_mod_cast h1
  exact ⟨fun i j a c => key _ _, fun j a c => key _ _⟩

end LeafAux

open Matrix SigabaNeo.Lattices Cslib Cslib.Probability AdvancedEncryption.WE.Assumptions.SuccinctLWE
  AdvancedEncryption.WE.EncryptorSetup
open scoped ENNReal

open Classical in
/-- **The leaf view with `Def_SuccinctLWE`'s own setup.** `leafView_close_zmod` instantiated with the
setup kernel `B ↦ (W ← uniform, T ← trapdoorLaw p B W)` (`W` split into its `ℓ` row blocks), the
public check "`T ≠ none` and its entries are at most `E_T`", the blocks `T_B[i,j]`, `T_W[j]` of
`T`, and a gadget `Γ` with `Γ.G = G` of `Def_SuccinctLWE` (one exists: `succ_gadget_exists`). The
block identity `B T_B[i,j] + W_i T_W[j] = δ_ij G` then holds on the support, so the real view
(attribute `0`) and the simulated view (attribute `w`) are within `m √(q^n / 2^m)`. -/
theorem solution (p : Params) [NeZero p.m]
    (Γ : GadgetMatrix (ZMod p.q) (Fin p.n) (Fin (p.n * p.k)))
    (hΓG : Γ.G = AdvancedEncryption.WE.Assumptions.SuccinctLWE.gadget p.n p.k p.q)
    (hΓ : ∀ A c c', zabs (Γ.ginv A c c') ≤ 1) (dec : (Fin p.n → ZMod p.q) → (Fin (p.n * p.k) → ZMod p.q))
    (hdec : ∀ y, Γ.G *ᵥ dec y = y) (hdecN : ∀ y c, zabs (dec y c) ≤ 1)
    (Bb s : ℕ) (hB : 2 ^ Bb ≤ p.q) (hB1 : 1 ≤ Bb)
    (hBig : (bigBox Bb hB : Finset (Fin p.m → ZMod p.q)).Nonempty)
    (u : Fin p.n → ZMod p.q) (φ : Circuit (Fin p.ℓ)) (w : Fin p.ℓ → ZMod p.q) (hw : ∀ i, w i = 0 ∨ w i = 1)
    (hφ0 : φ.eval (0 : Fin p.ℓ → ZMod p.q) = 0) (hφw : φ.eval w = 0) (ET : ℕ)
    (hs : s + p.n * p.k * errBound (p.n * p.k) ((p.m + p.ℓ) * ET) φ ≤ 2 ^ (Bb - 1) - 1) :
    CloseTo
      ((PMF.uniformOfFintype (Matrix (Fin p.n) (Fin p.m) (ZMod p.q))).bind fun B =>
        (Cslib.Probability.PMF.pi fun _ : Fin p.m => PMF.uniformOfFintype (Fin p.m → Bool)).bind
          fun xs => (leafSetup p B).bind fun WT =>
            (if leafGood ET WT.2 then
              boxSample (bigBox Bb hB) hBig (ball p.q s)
                (Matrix.mulVecLin B).toAddMonoidHom (fun y => dec (-y))
                (fun z => evalSim Γ (fun j => (B * (Matrix.of fun a c => bitVal (xs c a) : Matrix (Fin p.m) (Fin p.m) (ZMod p.q))) * leafTW WT.2 j) 0
                  (fun j => (Matrix.of fun a c => bitVal (xs c a) : Matrix (Fin p.m) (Fin p.m) (ZMod p.q)) * leafTW WT.2 j) φ *ᵥ z) u
            else PMF.pure none).map fun key => (B, WT, B * (Matrix.of fun a c => bitVal (xs c a) : Matrix (Fin p.m) (Fin p.m) (ZMod p.q)), key))
      ((PMF.uniformOfFintype (Matrix (Fin p.n) (Fin p.m) (ZMod p.q))).bind fun B =>
        (Cslib.Probability.PMF.pi fun _ : Fin p.m => PMF.uniformOfFintype (Fin p.m → Bool)).bind
          fun xs => (leafSetup p B).bind fun WT =>
            (if leafGood ET WT.2 then
              boxSample (bigBox Bb hB) hBig (ball p.q s)
                (Matrix.mulVecLin B).toAddMonoidHom (fun y => dec (-y))
                (fun z => evalSim Γ (fun j => ((∑ i, w i • WT.1 i) + B * (Matrix.of fun a c => bitVal (xs c a) : Matrix (Fin p.m) (Fin p.m) (ZMod p.q))) * leafTW WT.2 j) w
                  (fun j => (Matrix.of fun a c => bitVal (xs c a) : Matrix (Fin p.m) (Fin p.m) (ZMod p.q)) * leafTW WT.2 j - ∑ i, w i • leafTB WT.2 i j) φ *ᵥ z) u
            else PMF.pure none).map fun key => (B, WT, (∑ i, w i • WT.1 i) + B * (Matrix.of fun a c => bitVal (xs c a) : Matrix (Fin p.m) (Fin p.m) (ZMod p.q)), key))
      (ENNReal.ofReal (p.m * (Real.sqrt ((p.q : ℝ) ^ p.n * (2 ^ p.m : ℝ)⁻¹) / 2)) +
        ENNReal.ofReal (p.m * (Real.sqrt ((p.q : ℝ) ^ p.n * (2 ^ p.m : ℝ)⁻¹) / 2))) := AdvancedEncryption.WE.LeafView.leafView_close_zmod Γ hΓ dec hdec hdecN Bb s hB hB1 hBig u φ w
    hw hφ0 hφw (leafSetup p) (leafGood ET) leafTB leafTW
    (fun B WT hWT hg i j => by rw [hΓG]; exact LeafAux.leaf_block p ET B WT hWT hg i j) ET
    (fun T hT => LeafAux.leaf_good ET T hT) hs
