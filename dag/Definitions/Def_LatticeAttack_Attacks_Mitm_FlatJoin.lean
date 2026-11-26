module

public import Definitions.Def_LatticeAttack_Attacks_Mitm
import all Definitions.Def_LatticeAttack_Attacks_Mitm
public import Definitions.Def_LatticeAttack_Attacks_Mitm_BucketCost

set_option autoImplicit true

@[expose] public section
namespace SigabaNeo.Lattices.Mitm

open Guess SigabaNeo.IndexedLookup

variable {q n m : ℕ} [Fact q.Prime]

/-- A single flat bucket. Each right row and error queries every cached left key. -/
def flatJoin (L R : List (Vec q n)) (E : List (Vec q m)) (A : PublicMatrix q m n)
    (b : Vec q m) : Finset (Vec q n) × ℕ :=
  let rows := L.map fun x ↦ (A.mulVec x, x)
  let runs := R.flatMap fun y ↦ E.map fun z ↦
    let hit := filterCount (b - A.mulVec y - z) rows
    (hit.1.map (fun p ↦ p.2 + y), hit.2)
  ((runs.flatMap Prod.fst).toFinset, (runs.map Prod.snd).sum)

theorem flatJoin_spec (L R : List (Vec q n)) (E : List (Vec q m)) (A : PublicMatrix q m n)
    (b : Vec q m) :
    flatJoin L R E A b =
      (exactJoin L.toFinset R.toFinset E.toFinset A b, R.length * E.length * L.length) := by
  apply Prod.ext
  · ext t
    simp [flatJoin, filterCount_spec, exactJoin, bucket, List.mem_flatMap, List.mem_map]
    aesop
  · simp [flatJoin, filterCount_spec, List.map_flatMap, List.map_map,
      Function.comp_def, Nat.mul_assoc]
    induction R with
    | nil => simp
    | cons y ys ih =>
      simp [ih, Nat.add_mul]
      omega

/-- Failure mass over uniform matrices (denominator cleared), and exact vector-key tests. -/
theorem flatJoin_end_to_end (hn : 0 < n) (L R : List (Vec q n)) (B : ℕ)
    (E : List (Vec q m)) (hE : E.toFinset = errorBox q m B)
    (s : Vec q n) (hs : s ∈ support L.toFinset R.toFinset) (e : Vec q m)
    (he : e ∈ errorBox q m B) :
    (Finset.univ.filter (fun A : PublicMatrix q m n ↦
      (flatJoin L R E A (A.mulVec s + e)).1 ≠ {s})).card * q ^ m ≤
      ((support L.toFinset R.toFinset).card - 1) * (2 * B + 1) ^ m * q ^ (n * m) ∧
    ∀ (A : PublicMatrix q m n) (b : Vec q m),
      (flatJoin L R E A b).2 = R.length * E.length * L.length := by
  constructor
  · simpa [flatJoin_spec, matches_eq_scan, hE, scan_singleton_iff _ _ hs _ _ he] using
      ambiguity_probability hn _ s hs B e
  · intros
    simp [flatJoin_spec]

#print axioms flatJoin_spec
#print axioms flatJoin_end_to_end
end SigabaNeo.Lattices.Mitm
