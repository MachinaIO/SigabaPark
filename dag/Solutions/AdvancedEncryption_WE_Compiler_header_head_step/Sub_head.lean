import Mathlib

theorem solution (a b n j d : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : 0 ≤ n)
    (hj : 0 ≤ j) (hend : j ≤ a + n + 1) (hd : -1 ≤ d) (hu : d ≤ 1) :
    let next := min (a+n+1) (max 0 (j+d))
    let tag := min j (a+1)
    let off := max 0 (j-(a+1))
    let phys := b+1+off
    let back := tag=a+1 ∧ d = -1 ∧ off=0
    let travel := if tag≠a+1 ∨ back ∨ (d=1 ∧ phys=b+n+1) then 0 else d
    let newTag := if tag=a+1 then (if back then a else a+1)
      else min (a+1) (max 0 (tag+d))
    newTag = min next (a+1) ∧ off+travel = max 0 (next-(a+1)) ∧
      min (b+n+1) (max 0 (phys+travel)) = b+1+max 0 (next-(a+1)) := by
  dsimp only
  split_ifs <;> omega
