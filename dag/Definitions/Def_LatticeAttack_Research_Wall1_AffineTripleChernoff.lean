import Definitions.Def_LatticeAttack_Research_Wall1_FiniteGaussianChernoff
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic

set_option autoImplicit true

/-! Finite Gaussian counting for centered triples obeying a fixed affine relation. -/
noncomputable section
namespace SigabaNeo.Wall1.AffineTripleChernoff
open Finset
open scoped Classical

abbrev ScalarTriple := ℤ × ℤ × ℤ
abbrev VectorTriple (N : ℕ) := (Fin N → ℤ) × (Fin N → ℤ) × (Fin N → ℤ)

/-- Centered scalar triples satisfying the given relation modulo3329. -/
def scalarAlphabet (t : ZMod 3329) : Finset ScalarTriple :=
  ((Icc (-1664) 1664) ×ˢ ((Icc (-1664) 1664) ×ˢ (Icc (-1664) 1664))).filter
    fun p ↦ (p.2.2 : ZMod 3329) = (1-t) * (p.1 : ZMod 3329) + t * (p.2.1 : ZMod 3329)

/-- The sum of the three squared scalar coordinates. -/
def scalarEnergy (p : ScalarTriple) : ℝ :=
  (p.1 : ℝ)^2 + (p.2.1 : ℝ)^2 + (p.2.2 : ℝ)^2

/-- The finite scalar Gaussian partition sum, retaining every compatible triple. -/
def scalarPartition (t : ZMod 3329) (β : ℝ) : ℝ :=
  ∑ p : scalarAlphabet t, Real.exp (-β * scalarEnergy p.val)

/-- Encode each vector triple by its coordinate triples and apply the finite Chernoff bound. -/
theorem card_le_scalarPartition (N : ℕ) (S : Finset (VectorTriple N))
    (t : ZMod 3329) (R β : ℝ) (hβ : 0 ≤ β)
    (hcenter : ∀ p ∈ S, ∀ i,
      (-1664 ≤ p.1 i ∧ p.1 i ≤ 1664) ∧
      (-1664 ≤ p.2.1 i ∧ p.2.1 i ≤ 1664) ∧
      (-1664 ≤ p.2.2 i ∧ p.2.2 i ≤ 1664))
    (henergy : ∀ p ∈ S,
      (∑ i, (p.1 i : ℝ)^2) ≤ R^2 ∧
      (∑ i, (p.2.1 i : ℝ)^2) ≤ R^2 ∧
      (∑ i, (p.2.2 i : ℝ)^2) ≤ R^2)
    (hline : ∀ p ∈ S, ∀ i,
      (p.2.2 i : ZMod 3329) =
        (1-t) * (p.1 i : ZMod 3329) + t * (p.2.1 i : ZMod 3329)) :
    (S.card : ℝ) ≤ Real.exp (3 * β * R^2) * (scalarPartition t β)^N := by
  let encode (p : S) : Fin N → scalarAlphabet t := fun i ↦
    ⟨(p.val.1 i, p.val.2.1 i, p.val.2.2 i), by
      simp only [scalarAlphabet, mem_filter, mem_product, mem_Icc]
      exact ⟨hcenter p.val p.property i, hline p.val p.property i⟩⟩
  have hinj : Function.Injective encode := by
    intro p q he
    apply Subtype.ext
    apply Prod.ext
    · funext i
      exact congrArg (fun z : scalarAlphabet t ↦ z.val.1) (congrFun he i)
    · apply Prod.ext
      · funext i
        exact congrArg (fun z : scalarAlphabet t ↦ z.val.2.1) (congrFun he i)
      · funext i
        exact congrArg (fun z : scalarAlphabet t ↦ z.val.2.2) (congrFun he i)
  let U : Finset (Fin N → scalarAlphabet t) := univ.image encode
  have hcard : U.card = S.card := by
    rw [card_image_of_injective _ hinj]
    simp
  have hE : ∀ x ∈ U, (∑ i, scalarEnergy (x i).val) ≤ 3 * R^2 := by
    intro x hx
    obtain ⟨p, _, rfl⟩ := mem_image.mp hx
    have hp := henergy p.val p.property
    simp only [encode, scalarEnergy, sum_add_distrib]
    linarith [hp.1, hp.2.1, hp.2.2]
  have hc := FiniteGaussianChernoff.card_le_exp_partition N
    (fun p : scalarAlphabet t ↦ scalarEnergy p.val) U (3 * R^2) β hβ hE
  rw [hcard] at hc
  have he : β * (3 * R^2) = 3 * β * R^2 := by ring
  simpa only [he, scalarPartition] using hc

end SigabaNeo.Wall1.AffineTripleChernoff
#print axioms SigabaNeo.Wall1.AffineTripleChernoff.card_le_scalarPartition
