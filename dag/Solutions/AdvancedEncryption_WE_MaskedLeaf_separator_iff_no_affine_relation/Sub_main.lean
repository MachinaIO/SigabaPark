import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Common
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

open Matrix

theorem solution {K : Type*} [Field K] {ι : Type*} [Fintype ι] {k : ℕ}
    (c : ι → Fin k → K) :
    (∃ ℓ : Fin k → K, ∀ z, c z ⬝ᵥ ℓ = 1) ↔
      ¬ ∃ α : ι → K, ∑ z, α z = 1 ∧ ∑ z, α z • c z = 0 := by
  constructor
  · rintro ⟨ℓ, hℓ⟩ ⟨α, hα, hrel⟩
    have : (∑ z, α z • c z) ⬝ᵥ ℓ = 1 := by
      rw [sum_dotProduct]
      simp [smul_dotProduct, hℓ, hα]
    rw [hrel, zero_dotProduct] at this
    exact zero_ne_one this
  · intro hno
    classical
    let v : ι → K × (Fin k → K) := fun z => (1, c z)
    let p := Submodule.span K (Set.range v)
    have hx : ((1 : K), (0 : Fin k → K)) ∉ p := by
      intro hmem
      rw [Submodule.mem_span_range_iff_exists_fun] at hmem
      obtain ⟨α, hα⟩ := hmem
      apply hno
      refine ⟨α, ?_, ?_⟩
      · have := congrArg Prod.fst hα
        simpa [v, Prod.fst_sum] using this
      · have := congrArg Prod.snd hα
        simpa [v, Prod.snd_sum] using this
    obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
    have hfv : ∀ z, f (v z) = 0 := by
      intro z
      have : f (v z) ∈ p.map f := Submodule.mem_map_of_mem (Submodule.subset_span ⟨z, rfl⟩)
      rw [hmap] at this
      simpa using this
    set a := f ((1 : K), (0 : Fin k → K)) with ha
    refine ⟨fun j => - f ((0 : K), Pi.single j (1 : K)) / a, fun z => ?_⟩
    have hdecomp : v z = ((1 : K), (0 : Fin k → K)) +
        ∑ j, c z j • ((0 : K), Pi.single j (1 : K)) := by
      ext
      · simp [v, Prod.fst_sum]
      · rename_i i
        simp [v, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
    have h0 := hfv z
    rw [hdecomp, map_add, map_sum] at h0
    simp only [map_smul, smul_eq_mul] at h0
    have hs : ∑ j, c z j * f ((0 : K), Pi.single j (1 : K)) = -a := by
      rw [← ha] at h0; linear_combination h0
    show ∑ j, c z j * (- f ((0 : K), Pi.single j (1 : K)) / a) = 1
    calc ∑ j, c z j * (- f ((0 : K), Pi.single j (1 : K)) / a)
        = (∑ j, c z j * f ((0 : K), Pi.single j (1 : K))) * (-a⁻¹) := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => ?_; ring
      _ = 1 := by rw [hs]; field_simp
