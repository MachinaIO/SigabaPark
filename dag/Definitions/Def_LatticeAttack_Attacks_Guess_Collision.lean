module

public import Definitions.Def_LatticeAttack_Planted
public import Definitions.Def_LatticeAttack_Attacks_Guess

set_option autoImplicit true

public section

namespace SigabaNeo.Lattices.Guess

variable {q n m : ℕ} [Fact q.Prime]

abbrev Vec (q d : ℕ) := Fin d → ZMod q
abbrev PublicMatrix (q m n : ℕ) := Matrix (Fin m) (Fin n) (ZMod q)

def fibre (u : Vec q n) (v : Vec q m) : Finset (PublicMatrix q m n) :=
  Finset.univ.filter fun A ↦ A.mulVec u = v

theorem fibre_card_le (u : Vec q n) (v : Vec q m) (hu : u ≠ 0) :
    (fibre u v).card ≤ q ^ ((n - 1) * m) := by
  classical
  by_cases h : (fibre u v).Nonempty
  · obtain ⟨a, ha⟩ := h
    have ha' := (Finset.mem_filter.mp ha).2
    let X : Matrix (Fin 1) (Fin n) (ZMod q) := fun _ ↦ u
    have hr : X.rank = 1 := by
      rw [Matrix.rank_eq_finrank_span_row]
      change Module.finrank (ZMod q) (Submodule.span (ZMod q) (Set.range
        (fun _ : Fin 1 ↦ (fun j : Fin n ↦ u j)))) = 1
      rw [Set.range_const]
      exact finrank_span_singleton hu
    have equiv_eval (A : PublicMatrix q m n) :
        (∀ i, X.mulVec (A i) = fun _ ↦ v i) ↔ A.mulVec u = v := by
      simp [funext_iff, X, Matrix.mulVec, dotProduct, mul_comm]
    have hc := SigabaNeo.Planted.affineCount X (fun i _ ↦ v i) a ((equiv_eval a).2 ha')
    rw [hr] at hc
    have he := Fintype.card_congr (Equiv.subtypeEquivRight (fun A ↦ equiv_eval A))
    exact (by simpa [Fintype.card_subtype, fibre] using (he.symm.trans hc).le)
  · simp [Finset.not_nonempty_iff_eq_empty.mp h]

/-- Matrices admitting a distinct support point with a residual in E, at fixed planted error e. -/
def ambiguous (S : Finset (Vec q n)) (s : Vec q n) (E : Finset (Vec q m)) (e : Vec q m) :=
  (S.erase s).biUnion fun t ↦ E.biUnion fun z ↦ fibre (s - t) (z - e)

theorem mem_ambiguous (S : Finset (Vec q n)) (s : Vec q n) (E : Finset (Vec q m))
    (e : Vec q m) (A : PublicMatrix q m n) :
    A ∈ ambiguous S s E e ↔ ∃ t ∈ S, t ≠ s ∧ A.mulVec s + e - A.mulVec t ∈ E := by
  simp only [ambiguous, Finset.mem_biUnion, Finset.mem_erase, fibre, Finset.mem_filter,
    Finset.mem_univ, true_and, Matrix.mulVec_sub]
  constructor
  · rintro ⟨t, ⟨ht, hS⟩, z, hz, he⟩
    exact ⟨t, hS, ht, (show A.mulVec s + e - A.mulVec t = z by linear_combination he) ▸ hz⟩
  · rintro ⟨t, hS, ht, hz⟩
    exact ⟨t, ⟨ht, hS⟩, _, hz, by abel⟩

theorem ambiguous_card_le (S : Finset (Vec q n)) (s : Vec q n) (hs : s ∈ S)
    (E : Finset (Vec q m)) (e : Vec q m) :
    (ambiguous S s E e).card ≤ (S.card - 1) * (E.card * q ^ ((n - 1) * m)) := by
  unfold ambiguous
  rw [← Finset.card_erase_of_mem hs]
  apply Finset.card_biUnion_le_card_mul
  intro t ht
  apply Finset.card_biUnion_le_card_mul
  intro z _
  exact fibre_card_le _ _ (sub_ne_zero.mpr (Finset.mem_erase.mp ht).1.symm)

/-- Modular image of the centered integer error interval in each coordinate. -/
def errorBox (q m B : ℕ) : Finset (Vec q m) :=
  Fintype.piFinset fun _ ↦ (Finset.range (2 * B + 1)).image fun (k : ℕ) ↦ (k : ZMod q) - B

omit [Fact q.Prime] in
theorem errorBox_card_le (B : ℕ) : (errorBox q m B).card ≤ (2 * B + 1) ^ m := by
  unfold errorBox
  rw [Fintype.card_piFinset_const]
  apply Nat.pow_le_pow_left
  exact Finset.card_image_le.trans_eq (Finset.card_range _)

/-- Uniform-matrix ambiguity bound with denominators cleared. -/
theorem ambiguity_probability (hn : 0 < n) (S : Finset (Vec q n)) (s : Vec q n)
    (hs : s ∈ S) (B : ℕ) (e : Vec q m) :
    (ambiguous S s (errorBox q m B) e).card * q ^ m ≤
      (S.card - 1) * (2 * B + 1) ^ m * q ^ (n * m) := by
  have hk := Nat.mul_le_mul_right (q ^ m) (ambiguous_card_le S s hs (errorBox q m B) e)
  calc
    _ ≤ _ := hk
    _ = (S.card - 1) * (errorBox q m B).card * q ^ (n * m) := by
      rw [Nat.mul_assoc, Nat.mul_assoc, ← pow_add, ← Nat.succ_mul, show (n - 1).succ = n by omega]
      simp [Nat.mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (errorBox_card_le B))

@[expose] def scan (S : Finset (Vec q n)) (E : Finset (Vec q m)) (A : PublicMatrix q m n)
    (b : Vec q m) := S.filter fun t ↦ b - A.mulVec t ∈ E

theorem scan_singleton_iff (S : Finset (Vec q n)) (s : Vec q n) (hs : s ∈ S)
    (E : Finset (Vec q m)) (e : Vec q m) (he : e ∈ E) (A : PublicMatrix q m n) :
    scan S E A (A.mulVec s + e) = {s} ↔ A ∉ ambiguous S s E e := by
  rw [mem_ambiguous]
  constructor
  · rintro h ⟨t, ht, hne, hz⟩
    have hm : t ∈ scan S E A (A.mulVec s + e) := Finset.mem_filter.mpr ⟨ht, hz⟩
    exact hne (Finset.mem_singleton.mp (h ▸ hm))
  · intro h
    ext t
    simp only [scan, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨ht, hz⟩
      by_contra hn
      exact h ⟨t, ht, hn, hz⟩
    · rintro rfl
      simpa using And.intro hs he

/-- Dense scan accounting: one ring multiplication per candidate, row and column. -/
def scanMultiplications (S : Finset (Vec q n)) (m : ℕ) : ℕ :=
  ∑ _ ∈ S, ∑ _ : Fin m, ∑ _ : Fin n, 1

theorem scanMultiplications_eq (S : Finset (Vec q n)) :
    scanMultiplications S m = S.card * m * n := by simp [scanMultiplications, mul_assoc]

end SigabaNeo.Lattices.Guess
