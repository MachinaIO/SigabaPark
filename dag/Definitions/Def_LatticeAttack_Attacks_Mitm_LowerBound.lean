module

public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic

set_option autoImplicit true

@[expose] public section
namespace SigabaNeo.SortedLookup

variable {α : Type*}

/-- Search a half-open interval. The second result counts predicate evaluations. -/
def bisect (before : ℕ → Bool) : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, lo, _ => (lo, 0)
  | f + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      let r := if before mid then bisect before f (mid + 1) hi else bisect before f lo mid
      (r.1, r.2 + 1)
    else (lo, 0)

theorem bisect_spec (p : ℕ → Bool) (cut : ℕ) (f lo hi : ℕ)
    (hl : lo ≤ cut) (hh : cut ≤ hi) (hw : hi - lo < 2 ^ f)
    (hp : ∀ i, lo ≤ i → i < hi → (p i = true ↔ i < cut)) :
    (bisect p f lo hi).1 = cut ∧ (bisect p f lo hi).2 ≤ f := by
  induction f generalizing lo hi with
  | zero =>
    simp [bisect]
    simp at hw
    omega
  | succ f ih =>
    rw [pow_succ] at hw
    simp only [bisect]
    split
    · rename_i h
      generalize hm : (lo + hi) / 2 = mid
      have hmid := hp mid (by omega) (by omega)
      split
      · rename_i hb
        obtain ⟨he, hc⟩ := ih (mid + 1) hi (by simp_all) hh (by omega)
          (fun i ha hb ↦ hp i (by omega) hb)
        exact ⟨he, by omega⟩
      · rename_i hb
        obtain ⟨he, hc⟩ := ih lo mid hl (by simp_all) (by omega)
          (fun i ha hb ↦ hp i ha (by omega))
        exact ⟨he, by omega⟩
    · exact ⟨by omega, by simp⟩

/-- Array lookup with an arbitrary predicate which is true on an initial segment. -/
def lowerBound (a : Array α) (p : α → Bool) :=
  bisect (fun i ↦ (a[i]?).any p) (Nat.clog 2 (a.size + 1)) 0 a.size

theorem lowerBound_spec (a : Array α) (p : α → Bool) (cut : ℕ) (hc : cut ≤ a.size)
    (h : ∀ i (hi : i < a.size), p a[i] = true ↔ i < cut) :
    (lowerBound a p).1 = cut ∧ (lowerBound a p).2 ≤ Nat.clog 2 (a.size + 1) := by
  apply bisect_spec _ _ _ _ _ (Nat.zero_le _) hc
  · have := Nat.le_pow_clog (by decide : 1 < 2) (a.size + 1)
    omega
  · intro i _ hi
    simpa [Array.getElem?_eq_getElem hi] using h i hi

/-- Consume a matching prefix, charging one test for each inspected row. -/
def scan (p : α → Bool) : List α → List α × ℕ
  | [] => ([], 0)
  | x :: xs =>
    if p x then
      let r := scan p xs
      (x :: r.1, r.2 + 1)
    else ([], 1)

theorem scan_spec (p : α → Bool) (xs : List α) :
    (scan p xs).1 = xs.takeWhile p ∧ (scan p xs).2 ≤ (scan p xs).1.length + 1 := by
  induction xs with
  | nil => simp [scan]
  | cons x xs ih =>
    obtain ⟨he, hc⟩ := ih
    rw [he] at hc
    cases h : p x <;> simp [scan, List.takeWhile, h, he] <;> omega

#print axioms lowerBound_spec
#print axioms scan_spec

end SigabaNeo.SortedLookup
