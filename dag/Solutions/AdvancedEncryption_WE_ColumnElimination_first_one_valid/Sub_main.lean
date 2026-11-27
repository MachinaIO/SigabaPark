import Definitions.Def_ColumnElimination

open AdvancedEncryption.WE.ColumnElimination

theorem solution {m : Nat} (a : Fin m → ZMod 2) :
    a = 0 ∨ firstOne a a = 1 := by
  let s := Finset.univ.filter (fun i => a i ≠ 0)
  by_cases h : s.Nonempty
  · right
    have mem := s.min'_mem h
    have nz : a (s.min' h) ≠ 0 := (Finset.mem_filter.mp mem).2
    have unique : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    simpa [firstOne, s, h] using unique _ nz
  · left
    funext i
    by_contra hn
    exact h ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i, hn⟩⟩
