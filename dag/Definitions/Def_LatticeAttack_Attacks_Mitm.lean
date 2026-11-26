module

public import Definitions.Def_LatticeAttack_Attacks_Guess_Collision

set_option autoImplicit true

public section

namespace SigabaNeo.Lattices.Mitm

open Guess

variable {q n m : ℕ} [Fact q.Prime]

/-- Left and right vectors are embedded into the full coordinate space by zero padding.
A bucket retains all preimages, including collisions. -/
def bucket (L : Finset (Vec q n)) (A : PublicMatrix q m n) (k : Vec q m) :=
  L.filter fun x ↦ A.mulVec x = k

/-- Exact-match join specification, with one bucket query per right point and error guess. -/
def exactJoin (L R : Finset (Vec q n)) (E : Finset (Vec q m)) (A : PublicMatrix q m n)
    (b : Vec q m) :=
  R.biUnion fun y ↦ E.biUnion fun z ↦
    (bucket L A (b - A.mulVec y - z)).image fun x ↦ x + y

def support (L R : Finset (Vec q n)) := (L.product R).image fun p ↦ p.1 + p.2

theorem matches_eq_scan (L R : Finset (Vec q n)) (E : Finset (Vec q m))
    (A : PublicMatrix q m n) (b : Vec q m) :
    exactJoin L R E A b = scan (support L R) E A b := by
  ext t
  simp only [exactJoin, Finset.mem_biUnion, Finset.mem_image, bucket, Finset.mem_filter,
    scan, support, Prod.exists]
  constructor
  · rintro ⟨y, hy, z, hz, x, ⟨hx, h⟩, rfl⟩
    refine ⟨⟨x, y, Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩, ?_⟩
    rw [Matrix.mulVec_add, h, show b - (b - A.mulVec y - z + A.mulVec y) = z by abel]
    exact hz
  · rintro ⟨⟨x, y, hxy, rfl⟩, hz⟩
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
    refine ⟨y, hy, _, hz, x, ⟨hx, ?_⟩, rfl⟩
    rw [Matrix.mulVec_add]
    abel

/-- Model counts one insertion for each left point and one query per right point and error.
It does not charge for evaluating the keys or enumerating returned witnesses. -/
def tableOperations (left right errors : ℕ) := left + right * errors

theorem balanced_tableOperations (k errors : ℕ) :
    tableOperations k k errors = k * (1 + errors) := by simp [tableOperations, Nat.mul_add]

end SigabaNeo.Lattices.Mitm
