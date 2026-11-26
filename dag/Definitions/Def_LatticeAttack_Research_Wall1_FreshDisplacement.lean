module

public import Mathlib.GroupTheory.Index
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Prod

set_option autoImplicit true

public section

namespace SigabaNeo.Wall1.FreshDisplacement

open scoped Classical

variable {G K : Type*} [AddGroup G] [AddGroup K] [Fintype G]

/-- Every occupied fiber is a translate of the kernel. -/
theorem fiber_card (φ : G →+ K) (k : K) (hk : k ∈ φ.range) :
    (Finset.univ.filter fun g ↦ φ g = k).card = Nat.card φ.ker := by
  obtain ⟨a, rfl⟩ := hk
  have e : {g // φ g = φ a} ≃ φ.ker := φ.fiberEquivKer a
  simpa [Nat.card_eq_fintype_card, Fintype.card_subtype] using Nat.card_congr e

/-- Counting mass of each image point under uniform sampling from the domain. -/
theorem uniform_image (φ : G →+ K) (k : K) (hk : k ∈ φ.range) :
    (Finset.univ.filter fun g ↦ φ g = k).card = Fintype.card G / Nat.card φ.range := by
  rw [fiber_card φ k hk, ← Nat.card_eq_fintype_card, ← AddSubgroup.card_ker_mul_card_range φ,
    Nat.mul_div_cancel _ Nat.card_pos]

/-- Column coordinates grouped as ((revealed prefix, unread suffix), fresh column). -/
abbrev Columns (p s m q : ℕ) :=
  ((Fin p → Fin m → ZMod q) × (Fin s → Fin m → ZMod q)) × (Fin m → ZMod q)

/-- Exact conditional counting law, including histories with empty fiber.
Taking the identity homomorphism gives uniformity of the fresh column itself. -/
theorem conditional_image {p s m q : ℕ} [NeZero q] {H : Type*}
    (F : (Fin p → Fin m → ZMod q) → H) (φ : H → (Fin m → ZMod q) →+ K)
    (h : H) (k : K) (hk : k ∈ (φ h).range) :
    (Finset.univ.filter fun x : Columns p s m q ↦ F x.1.1 = h ∧ φ h x.2 = k).card =
    (Finset.univ.filter fun x : Columns p s m q ↦ F x.1.1 = h).card / Nat.card (φ h).range := by
  simp only [← Finset.univ_product_univ]
  rw [Finset.filter_product (fun y : (Fin p → Fin m → ZMod q) × (Fin s → Fin m → ZMod q) ↦ F y.1 = h) (fun c ↦ φ h c = k),
    Finset.filter_product_left (fun y : (Fin p → Fin m → ZMod q) × (Fin s → Fin m → ZMod q) ↦ F y.1 = h)]
  simp only [
    Finset.card_product, Finset.card_univ]
  rw [fiber_card (φ h) k hk, ← Nat.card_eq_fintype_card,
    ← AddSubgroup.card_ker_mul_card_range (φ h), ← Nat.mul_assoc,
    Nat.mul_div_cancel _ Nat.card_pos]

#print axioms fiber_card
#print axioms uniform_image
#print axioms conditional_image

end SigabaNeo.Wall1.FreshDisplacement
