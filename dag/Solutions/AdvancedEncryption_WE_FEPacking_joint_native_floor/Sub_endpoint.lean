import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

theorem solution (a b : ℕ) (m : List ℕ) (total : a + m.sum + b = 128) :
    2^32 ≤ 65536 * ((a :: m).zipWith (fun x y => 2^(x+y)) (m ++ [b])).sum +
      1024 * (2^(m.length + 1) - 2) := by
  let edge := fun (x y : ℕ) (l : List ℕ) =>
    ((x :: l).zipWith (fun i j => 2^(i+j)) (l ++ [y])).sum
  have base (x y : ℕ) : edge x y [] = 2^(x+y) := by simp [edge]
  have step (x y c : ℕ) (l : List ℕ) :
      edge x y (c :: l) = 2^(x+c) + edge c y l := by simp [edge]
  have powMono {x y : ℕ} (e : x ≤ y) : 2^x ≤ 2^y :=
    Nat.pow_le_pow_right (n := 2) (by decide) e
  have lastBound (x y : ℕ) (l : List ℕ) : 2^y ≤ edge x y l := by
    induction l generalizing x with
    | nil => rw [base]; exact powMono (by omega)
    | cons c l ih => rw [step]; exact (ih c).trans (Nat.le_add_left _ _)
  have tangent (v : ℕ) : 2048*v ≤ 2^v + 20480 := by
    by_cases hv : v < 11
    · interval_cases v <;> decide
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (show 11 ≤ v by omega)
      induction i with
      | zero => decide
      | succ i ih =>
        have hh : 2^11 ≤ 2^(11+i) := powMono (by omega)
        rw [show 11+(i+1)=(11+i)+1 by omega, pow_succ]
        omega
  have totalBound (x y : ℕ) (l : List ℕ) :
      2048*(x + 2*l.sum + y) ≤ edge x y l + 20480*(l.length + 1) := by
    induction l generalizing x with
    | nil => simpa [base] using tangent (x+y)
    | cons c l ih =>
      have h1 := tangent (x+c)
      have h2 := ih c
      rw [step]
      simp only [List.sum_cons, List.length_cons]
      omega
  change 2^32 ≤ 65536 * edge a b m + 1024 * (2^(m.length + 1) - 2)
  cases m with
  | nil =>
    simp only [List.sum_nil, Nat.add_zero] at total
    rw [base, total]
    decide
  | cons c l =>
    let E := edge a b (c :: l)
    let s := (c :: l).length + 1
    change 2^32 ≤ 65536 * E + 1024 * (2^s - 2)
    by_cases large : 65536 ≤ E
    · omega
    have ends : 2^a + 2^b ≤ E := by
      dsimp only [E]
      rw [step]
      exact Nat.add_le_add (powMono (by omega)) (lastBound c b l)
    have oneEnd (z : ℕ) (hz : 2^z ≤ E) : z ≤ 15 := by
      by_contra! bad
      have h16 : 2^16 ≤ 2^z := powMono (by omega)
      omega
    have az := oneEnd a ((Nat.le_add_right _ _).trans ends)
    have bz := oneEnd b ((Nat.le_add_left _ _).trans ends)
    have small : a+b ≤ 29 := by
      by_contra! hh
      have aa : a = 15 := by omega
      have bb : b = 15 := by omega
      rw [aa,bb] at ends
      omega
    have ht : 2048*(a + 2*(c::l).sum + b) ≤ E + 20480*s :=
      totalBound a b (c::l)
    have minE : 1 ≤ E := by
      exact (show 1 ≤ 2^a from Nat.one_le_pow _ _ (by decide)).trans ((Nat.le_add_right _ _).trans ends)
    by_cases low : s ≤ 19
    · omega
    by_cases h20 : s = 20
    · rw [h20]
      omega
    by_cases h21 : s = 21
    · rw [h21]
      omega
    have big : 2^22 ≤ 2^s := powMono (by omega)
    omega
