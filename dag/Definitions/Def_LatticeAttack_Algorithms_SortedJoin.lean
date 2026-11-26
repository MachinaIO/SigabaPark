module

import all Init.Data.List.Sort.Basic
public import Definitions.Def_LatticeAttack_Attacks_Mitm_LowerBound
public import Definitions.Def_LatticeAttack_Attacks_Mitm_SortedRows

set_option autoImplicit true

@[expose] public section
namespace SigabaNeo.SortedJoin

open SortedLookup
open Lattices.Mitm.SortedRows

variable {α κ : Type*} [LinearOrder κ]

def merge (le : α → α → Bool) : Nat → List α → List α → List α × Nat
  | 0, xs, ys => (xs ++ ys, 0)
  | _ + 1, [], ys => (ys, 0)
  | _ + 1, xs, [] => (xs, 0)
  | f + 1, x :: xs, y :: ys =>
    if le x y then
      let r := merge le f xs (y :: ys)
      (x :: r.1, r.2 + 1)
    else
      let r := merge le f (x :: xs) ys
      (y :: r.1, r.2 + 1)

private theorem merge_spec (le : α → α → Bool) (f : Nat) (xs ys : List α)
    (h : xs.length + ys.length ≤ f) :
    (merge le f xs ys).1 = xs.merge ys le ∧ (merge le f xs ys).2 ≤ f := by
  induction f generalizing xs ys with
  | zero => simp_all [merge]
  | succ f ih =>
    cases xs with
    | nil => simp [merge]
    | cons x xs =>
      cases ys with
      | nil => simp [merge]
      | cons y ys =>
        simp only [List.length_cons] at h
        have ha := ih xs (y :: ys) (by simp; omega)
        have hb := ih (x :: xs) ys (by simp; omega)
        cases e : le x y <;> simp_all [merge]

def sort (le : α → α → Bool) : Nat → List α → List α × Nat
  | 0, xs => (xs, 0)
  | _ + 1, [] => ([], 0)
  | _ + 1, [x] => ([x], 0)
  | f + 1, x :: y :: xs =>
    let s := List.MergeSort.Internal.splitInTwo ⟨x :: y :: xs, rfl⟩
    let a := sort le f s.1.val
    let b := sort le f s.2.val
    let r := merge le (xs.length + 2) a.1 b.1
    (r.1, a.2 + b.2 + r.2)

theorem sort_spec (le : α → α → Bool) (f : Nat) (xs : List α)
    (h : xs.length ≤ 2 ^ f) :
    (sort le f xs).1 = xs.mergeSort le ∧ (sort le f xs).2 ≤ xs.length * f := by
  induction f generalizing xs with
  | zero =>
    cases xs with
    | nil => simp [sort]
    | cons x xs =>
      cases xs <;> simp_all [sort]
  | succ f ih =>
    cases xs with
    | nil => simp [sort]
    | cons x xs =>
      cases xs with
      | nil => simp [sort]
      | cons y xs =>
        let s := List.MergeSort.Internal.splitInTwo ⟨x :: y :: xs, rfl⟩
        have h₁ := s.1.property
        have h₂ := s.2.property
        simp only [List.length_cons, pow_succ] at h h₁ h₂
        obtain ⟨ea, ca⟩ := ih s.1.val (by omega)
        obtain ⟨eb, cb⟩ := ih s.2.val (by omega)
        have hm := merge_spec le (xs.length + 2) (sort le f s.1.val).1 (sort le f s.2.val).1
          (by rw [ea, eb]; simp only [List.length_mergeSort]; omega)
        have hs : s.1.val.length + s.2.val.length = xs.length + 2 := by omega
        have hc := Nat.add_le_add ca cb
        rw [← Nat.add_mul, hs] at hc
        constructor
        · simp only [List.mergeSort]
          exact hm.1.trans (by rw [ea, eb])
        · change _ + _ + _ ≤ (xs.length + 2) * (f + 1)
          rw [Nat.mul_succ]
          exact Nat.add_le_add hc hm.2

private theorem run_eq (key : α → κ) (k : κ) (xs : List α)
    (hs : xs.Pairwise (fun a b ↦ key a ≤ key b)) (hl : ∀ x ∈ xs, k ≤ key x) :
    xs.takeWhile (fun x ↦ decide (key x = k)) = xs.filter (fun x ↦ decide (key x = k)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨h, ht⟩ := List.pairwise_cons.mp hs
    by_cases e : key x = k
    · simp [e, ih ht (fun y hy ↦ hl y (by simp [hy]))]
    · have hx := hl x (by simp)
      have hn : ∀ y ∈ xs, ¬ key y = k := fun y hy ↦ by have := h y hy; order
      simp [e, List.filter_eq_nil_iff.mpr (by simpa using hn : ∀ y ∈ xs, ¬ decide (key y = k))]

private theorem cut_spec (key : α → κ) (k : κ) (xs : List α)
    (hs : xs.Pairwise (fun a b ↦ key a ≤ key b)) :
    ∃ c ≤ xs.length, (∀ i (hi : i < xs.length), key xs[i] < k ↔ i < c) ∧
      (xs.drop c).takeWhile (fun x ↦ decide (key x = k)) =
        xs.filter (fun x ↦ decide (key x = k)) := by
  induction xs with
  | nil => exact ⟨0, by simp, by simp, rfl⟩
  | cons x xs ih =>
    obtain ⟨h, ht⟩ := List.pairwise_cons.mp hs
    by_cases hx : key x < k
    · obtain ⟨c, hc, hi, he⟩ := ih ht
      refine ⟨c+1, by simp [hc], ?_, ?_⟩
      · intro i hb
        cases i with
        | zero => simp [hx]
        | succ i => simpa using hi i (by simpa using hb)
      · simpa [ne_of_lt hx] using he
    · have hl : ∀ y ∈ x :: xs, k ≤ key y := by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact le_of_not_gt hx
        · exact le_trans (le_of_not_gt hx) (h y hy)
      exact ⟨0, Nat.zero_le _, fun i hi ↦ by
        have := hl _ (List.getElem_mem hi); simp [not_lt_of_ge this], by
        simpa using run_eq key k _ hs hl⟩

/-- Inspect the array from the lower bound until the first failed predicate. -/
def scanArray (p : α → Bool) (a : Array α) (i : Nat) : List α × Nat :=
  if h : i < a.size then
    let x := a[i]
    if p x then
      let r := scanArray p a (i + 1)
      (x :: r.1, r.2 + 1)
    else ([], 1)
  else ([], 0)
termination_by a.size - i

private theorem scanArray_eq (p : α → Bool) (xs : List α) (i : Nat) :
    scanArray p xs.toArray i = scan p (xs.drop i) := by
  rw [scanArray]
  split
  · rename_i h
    have hi : i < xs.length := by simpa using h
    rw [List.drop_eq_getElem_cons hi, scan]
    simp only [List.getElem_toArray]
    split <;> simp_all [scanArray_eq p xs (i + 1)]
  · rename_i h
    have hi : xs.length ≤ i := by simpa using h
    simp [List.drop_eq_nil_of_le hi, scan]
termination_by xs.length - i

def probe (key : α → κ) (a : Array α) (k : κ) :=
  let b := lowerBound a (fun x ↦ decide (key x < k))
  let r := scanArray (fun x ↦ decide (key x = k)) a b.1
  (r.1, b.2 + r.2)

theorem probe_spec (key : α → κ) (xs : List α) (k : κ)
    (hs : xs.Pairwise (fun a b ↦ key a ≤ key b)) :
    (probe key xs.toArray k).1 = xs.filter (fun x ↦ decide (key x = k)) ∧
    (probe key xs.toArray k).2 ≤ Nat.clog 2 (xs.length + 1) + 1 +
      (probe key xs.toArray k).1.length := by
  obtain ⟨c, hc, hi, he⟩ := cut_spec key k xs hs
  obtain ⟨eb, cb⟩ := lowerBound_spec xs.toArray (fun x ↦ decide (key x < k)) c
    (by simpa using hc) (by intro i h; simpa using hi i (by simpa using h))
  simp only [probe, eb, scanArray_eq]
  have h := scan_spec (fun x ↦ decide (key x = k)) (xs.drop c)
  simp only [List.size_toArray] at cb
  exact ⟨h.1.trans he, by omega⟩

def batch (key : α → κ) (a : Array α) : List κ → List α × Nat
  | [] => ([], 0)
  | k :: ks =>
    let p := probe key a k
    let t := batch key a ks
    (p.1 ++ t.1, p.2 + t.2)

def naiveJoin (key : α → κ) (rows : List α) (qs : List κ) :=
  qs.flatMap fun k ↦ rows.filter fun x ↦ decide (key x = k)

def sortedJoin (key : α → κ) (rows : List α) (qs : List κ) :=
  let s := sort (fun x y ↦ decide (key x ≤ key y)) (Nat.clog 2 (rows.length + 1)) rows
  let b := batch key s.1.toArray qs
  (b.1, s.2 + b.2)

theorem sortedJoin_spec (key : α → κ) (rows : List α) (qs : List κ) :
    (sortedJoin key rows qs).1.Perm (naiveJoin key rows qs) ∧
    (sortedJoin key rows qs).2 ≤ rows.length * Nat.clog 2 (rows.length + 1) +
      qs.length * (Nat.clog 2 (rows.length + 1) + 1) + (naiveJoin key rows qs).length := by
  let xs := sorted key rows
  let d := Nat.clog 2 (rows.length + 1)
  obtain ⟨es, cs⟩ := sort_spec (fun x y ↦ decide (key x ≤ key y)) d rows
    (by dsimp [d]; have := Nat.le_pow_clog (by decide : 1 < 2) (rows.length + 1); omega)
  change _ = xs at es
  have hl : xs.length = rows.length := List.length_mergeSort ..
  have hb : (batch key xs.toArray qs).1.Perm (naiveJoin key rows qs) ∧
      (batch key xs.toArray qs).2 ≤ qs.length * (d + 1) + (naiveJoin key rows qs).length := by
    induction qs with
    | nil => simp [batch, naiveJoin]
    | cons k ks ih =>
      obtain ⟨ep, cp⟩ := probe_spec key xs k (sorted_pairwise key rows)
      have hp' : (probe key xs.toArray k).1.Perm (rows.filter fun x ↦ decide (key x = k)) := by
        rw [ep]; exact filter_sorted_perm key k rows
      rw [hl, hp'.length_eq] at cp
      refine ⟨hp'.append ih.1, ?_⟩
      simp only [batch, naiveJoin, List.flatMap_cons, List.length_append, List.length_cons,
        Nat.succ_mul] at *
      dsimp [d] at *
      omega
  dsimp [d] at es cs hb
  simp only [sortedJoin, es]
  exact ⟨hb.1, by have := Nat.add_le_add cs hb.2; omega⟩

#print axioms sortedJoin_spec

end SigabaNeo.SortedJoin
