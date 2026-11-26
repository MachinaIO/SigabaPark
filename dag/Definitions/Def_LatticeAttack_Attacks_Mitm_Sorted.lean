module

public import Definitions.Def_LatticeAttack_Attacks_Mitm_FlatJoin
import all Definitions.Def_LatticeAttack_Attacks_Mitm
public import Definitions.Def_LatticeAttack_Algorithms_PairJoin

set_option autoImplicit true

/-!
# Meet-in-the-middle with a sorted table, end to end

The left table `{(A x, x) : x ∈ L}` is sorted once by an injective numeric code of `A x`. Each
right vector `y` and error guess `z` issues one query for the key `b − A y − z`, carrying `y`
as payload; `pairJoin` returns every matching `(y, x)`, and the candidate is `x + y`.

`sortedMitm_spec`: the candidate set is exactly `exactJoin`, and the number of charged
comparisons is at most `|L|·⌈log₂(|L|+1)⌉ + |R||E|·(⌈log₂(|L|+1)⌉+1) + #hits`.
`sortedMitm_end_to_end`: combined with `ambiguity_probability`, the output is exactly `{s}`
except on a fraction `(|S|−1)(2B+1)^m/q^m` of public matrices.
-/

@[expose] public section
namespace SigabaNeo.Lattices.Mitm

open Guess SigabaNeo.SortedJoin

variable {q n m : ℕ} [Fact q.Prime]

/-- Injective numeric code of a syndrome. -/
noncomputable def code (v : Vec q m) : ℕ := (Fintype.equivFin (Vec q m) v).val

theorem code_inj {u v : Vec q m} : code u = code v ↔ u = v := by
  constructor
  · intro h; exact (Fintype.equivFin _).injective (Fin.ext h)
  · rintro rfl; rfl

/-- The queries: one per right vector and error guess, with the right vector as payload. -/
noncomputable def queries (R : List (Vec q n)) (E : List (Vec q m)) (A : PublicMatrix q m n)
    (b : Vec q m) : List (Vec q n × ℕ) :=
  R.flatMap fun y ↦ E.map fun z ↦ (y, code (b - A.mulVec y - z))

/-- Sorted-table meet in the middle: candidates and charged comparisons. -/
noncomputable def sortedMitm (L R : List (Vec q n)) (E : List (Vec q m)) (A : PublicMatrix q m n)
    (b : Vec q m) : Finset (Vec q n) × ℕ :=
  let out := pairJoin (fun x ↦ code (A.mulVec x)) L (queries R E A b)
  ((out.1.map fun p ↦ p.2 + p.1).toFinset, out.2)

theorem queries_length (R : List (Vec q n)) (E : List (Vec q m)) (A : PublicMatrix q m n)
    (b : Vec q m) : (queries R E A b).length = R.length * E.length := by
  induction R with
  | nil => simp [queries]
  | cons y ys ih =>
    simp only [queries, List.flatMap_cons, List.length_append, List.length_map] at ih ⊢
    rw [ih]; simp [Nat.succ_mul]; ring

theorem sortedMitm_spec (L R : List (Vec q n)) (E : List (Vec q m)) (A : PublicMatrix q m n)
    (b : Vec q m) :
    (sortedMitm L R E A b).1 = exactJoin L.toFinset R.toFinset E.toFinset A b ∧
    (sortedMitm L R E A b).2 ≤ L.length * Nat.clog 2 (L.length + 1) +
      R.length * E.length * (Nat.clog 2 (L.length + 1) + 1) +
      (pairJoin (fun x ↦ code (A.mulVec x)) L (queries R E A b)).1.length := by
  obtain ⟨hp, hc⟩ := pairJoin_spec (fun x ↦ code (A.mulVec x)) L (queries R E A b)
  refine ⟨?_, by simpa [sortedMitm, queries_length] using hc⟩
  ext t
  change t ∈ ((pairJoin (fun x ↦ code (A.mulVec x)) L (queries R E A b)).1.map
    fun p ↦ p.2 + p.1).toFinset ↔ _
  rw [List.mem_toFinset, List.mem_map]
  simp_rw [hp.mem_iff]
  simp only [queries, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq,
    exactJoin, Finset.mem_biUnion, Finset.mem_image, bucket, Finset.mem_filter,
    List.mem_toFinset, Prod.exists]
  constructor
  · rintro ⟨_, _, ⟨_, _, ⟨y, hy, z, hz, he⟩, x, ⟨hx, hk⟩, he'⟩, rfl⟩
    simp only [Prod.mk.injEq] at he he'
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨rfl, rfl⟩ := he'
    exact ⟨y, hy, z, hz, x, ⟨hx, code_inj.mp hk⟩, rfl⟩
  · rintro ⟨y, hy, z, hz, x, ⟨hx, hk⟩, rfl⟩
    exact ⟨y, x, ⟨y, _, ⟨y, hy, z, hz, rfl⟩, x, ⟨hx, code_inj.mpr hk⟩, rfl⟩, rfl⟩

/-- **Sorted-table meet in the middle, end to end.** For any secret `s` in the support `L + R`
and error `e` in the box `[−B, B]^m` (enumerated by `E`), the output equals `{s}` except on a
fraction `(|S|−1)(2B+1)^m / q^m` of public matrices, and the comparison count is
`|L| log|L| + |R||E| (log|L| + 1) + #hits`. -/
theorem sortedMitm_end_to_end (hn : 0 < n) (L R : List (Vec q n)) (B : ℕ)
    (E : List (Vec q m)) (hE : E.toFinset = errorBox q m B)
    (s : Vec q n) (hs : s ∈ support L.toFinset R.toFinset) (e : Vec q m)
    (he : e ∈ errorBox q m B) :
    (Finset.univ.filter (fun A : PublicMatrix q m n ↦
      (sortedMitm L R E A (A.mulVec s + e)).1 ≠ {s})).card * q ^ m ≤
      ((support L.toFinset R.toFinset).card - 1) * (2 * B + 1) ^ m * q ^ (n * m) ∧
    ∀ (A : PublicMatrix q m n) (b : Vec q m),
      (sortedMitm L R E A b).2 ≤ L.length * Nat.clog 2 (L.length + 1) +
        R.length * E.length * (Nat.clog 2 (L.length + 1) + 1) +
        (pairJoin (fun x ↦ code (A.mulVec x)) L (queries R E A b)).1.length := by
  refine ⟨?_, fun A b ↦ (sortedMitm_spec L R E A b).2⟩
  have h := (flatJoin_end_to_end hn L R B E hE s hs e he).1
  simp only [flatJoin_spec] at h
  simpa only [(sortedMitm_spec L R E _ _).1] using h

end SigabaNeo.Lattices.Mitm

#print axioms SigabaNeo.Lattices.Mitm.sortedMitm_spec
#print axioms SigabaNeo.Lattices.Mitm.sortedMitm_end_to_end
