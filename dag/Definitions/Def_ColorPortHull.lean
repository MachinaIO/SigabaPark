import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace ColorPort
variable {r q : Nat} {K : Type} [Field K]
abbrev Table (r q : Nat) (K : Type) := Fin r → Fin q → K

def incidence (f : Fin r → Fin q) : Table r q K :=
  fun i c ↦ if f i = c then 1 else 0

def hull (r q : Nat) (K : Type) [Field K] : AffineSubspace K (Table r q K) :=
  affineSpan K (Set.range (fun f : Fin r ↪ Fin q ↦ incidence (K := K) f))

def move (i : Fin r) (a b : Fin q) : Table r q K := fun j c ↦
  if j=i then (if a=c then 1 else 0) - (if b=c then 1 else 0) else 0

theorem row_mem (f : Fin r ↪ Fin q) : incidence (K := K) f ∈ hull r q K :=
  mem_affineSpan K ⟨f,rfl⟩

/-- Realize a single-vertex exchange by two actual injections that agree elsewhere. -/
theorem exchange (hr : r < q) (i : Fin r) (a b : Fin q) (hab : a ≠ b) :
    ∃ f g : Fin r ↪ Fin q, f i=a ∧ g i=b ∧ ∀ j, j ≠ i → f j = g j := by
  classical
  let X := (Finset.univ : Finset (Fin r)).erase i
  let Y := ((Finset.univ : Finset (Fin q)).erase a).erase b
  have hxy : Fintype.card ↥X ≤ Fintype.card ↥Y := by
    have hba : b ∈ (Finset.univ : Finset (Fin q)).erase a := by simp [Ne.symm hab]
    rw [Fintype.card_coe,Fintype.card_coe]
    change (Finset.univ.erase i).card ≤ ((Finset.univ.erase a).erase b).card
    rw [Finset.card_erase_of_mem hba,Finset.card_erase_of_mem (Finset.mem_univ a),
      Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp only [Finset.card_univ,Fintype.card_fin]; omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hxy
  let make (c : Fin q) (hc : c ∉ Y) : Fin r ↪ Fin q :=
    ⟨fun j ↦ if h : j=i then c else (e ⟨j,by simpa [X] using h⟩).val,by
      intro j k h
      by_cases hj : j=i <;> by_cases hk : k=i
      · exact hj.trans hk.symm
      · simp only [dif_pos hj,dif_neg hk] at h
        exact (hc (h ▸ (e ⟨k,by simpa [X] using hk⟩).property)).elim
      · simp only [dif_neg hj,dif_pos hk] at h
        exact (hc (h ▸ (e ⟨j,by simpa [X] using hj⟩).property)).elim
      · simp only [dif_neg hj,dif_neg hk] at h
        exact congrArg Subtype.val (e.injective (Subtype.ext h))⟩
  refine ⟨make a (by simp [Y]),make b (by simp [Y]),by change (if h : i=i then _ else _) = _; rw [dif_pos rfl],by change (if h : i=i then _ else _) = _; rw [dif_pos rfl],?_⟩
  intro j hj
  change (if h : j=i then a else _) = (if h : j=i then b else _); rw [dif_neg hj,dif_neg hj]

theorem move_mem (hr : r < q) (i : Fin r) (a b : Fin q) :
    move (K := K) i a b ∈ (hull r q K).direction := by
  by_cases h : a=b
  · subst a; have hz : move (K := K) i b b = 0 := by funext j c; simp [move]
    rw [hz]; exact Submodule.zero_mem _
  obtain ⟨f,g,ha,hb,he⟩ := exchange hr i a b h
  have hh : move (K := K) i a b = incidence (K := K) f -ᵥ incidence (K := K) g := by
    funext j c
    by_cases hj : j=i
    · subst j; simp [move,incidence,ha,hb]
    · simp [move,incidence,hj,he j hj]
  rw [hh]
  exact AffineSubspace.vsub_mem_direction (row_mem f) (row_mem g)

theorem hull_iff (hr : r < q) (X : Table r q K) :
    X ∈ hull r q K ↔ ∀ i, ∑ c, X i c = 1 := by
  classical
  constructor
  · intro hx
    apply affineSpan_induction (p := fun x : Table r q K ↦ ∀ i, ∑ c, x i c = 1) hx
    · rintro _ ⟨f,rfl⟩ i; simp [incidence]
    · intro k u v w hu hv hw i
      change (∑ c, (k * (u i c-v i c) + w i c)) = _
      simp [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_sub_distrib,hu,hv,hw]
  · intro h
    let f : Fin r ↪ Fin q := Fin.castLEEmb hr.le
    let D := (hull r q K).direction
    have hd : (∑ i, ∑ c, X i c • move (K := K) i c (f i)) ∈ D :=
      Submodule.sum_mem _ (fun i _ ↦ Submodule.sum_mem _ fun c _ ↦
        Submodule.smul_mem _ _ (move_mem hr i c (f i)))
    have he (i : Fin r) (c : Fin q) :
        (∑ a, X i a * ((if a=c then 1 else 0) - (if f i=c then 1 else 0))) =
          X i c - (if f i=c then 1 else 0) := by
      simp [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,h i,mul_ite]
    have hm : (∑ i, ∑ c, X i c • move (K := K) i c (f i)) +ᵥ incidence (K := K) f = X := by
      funext j d
      simp only [vadd_eq_add,Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
      have hh (i : Fin r) : (∑ c, X i c * move i c (f i) j d) =
          if i=j then X j d - incidence f j d else 0 := by
        by_cases hij : i=j
        · subst i; simpa [move,incidence] using he j d
        · simp [move,hij,Ne.symm hij]
      simp [hh]
    rw [← hm]
    exact AffineSubspace.vadd_mem_of_mem_direction hd (row_mem f)

theorem deterministic (hr : r < q) (f : Fin r → Fin q) : incidence (K := K) f ∈ hull r q K := by
  apply (hull_iff hr _).mpr
  simp [incidence]

/-- Fix a named color. A bijection of sixteen words has exactly one occurrence of it. -/
theorem one_color (c : Fin 16) (w : Fin 16 ↪ Fin 16) :
    ∑ i, incidence (K := ZMod 2) w i c = 1 := by
  obtain ⟨j,hj⟩ := (Finite.surjective_of_injective w.injective) c
  rw [← hj]
  simp [incidence,w.injective.eq_iff]

def equation (i : Nat) := 2 * (Nat.xor (2^17-1) (2^i)) + 1

theorem seventeen_rows : ((List.range 17).map equation).foldl Nat.xor 0 = 1 := by decide


/-- No unary marginal meets the seventeen justified bag equations for a fixed color. -/
theorem no_inventory (x : Fin 17 → ZMod 2) :
    ¬ ∀ i : Fin 17, ∑ j ∈ Finset.univ.erase i, x j = 1 := by
  intro h
  have he (i : Fin 17) : (∑ j, x j) = 1 + x i := by
    rw [← h i]; exact (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
  have eq (i : Fin 17) : x i = x 0 := add_left_cancel ((he i).symm.trans (he 0))
  have hh := h 0
  exact (by
      have bad : (16:Nat) • x 0 = 1 := by
        simpa only [eq,Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ,Fintype.card_fin] using hh
      have hz : ((16 : Nat) : ZMod 2) = 0 := by decide
      rw [nsmul_eq_mul,hz,zero_mul] at bad
      exact zero_ne_one bad)

end ColorPort
