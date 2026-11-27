import Mathlib

theorem solution {K : Type*} [Field K] (l r x y : K) (hxy : x ≠ y) :
    Function.Bijective (fun t : K × K ↦ (t.2 + l + t.1*x, t.2 + r + t.1*y)) := by
  have hn : y-x ≠ 0 := sub_ne_zero.mpr hxy.symm
  constructor
  · rintro ⟨i,b⟩ ⟨j,c⟩ he
    have h₁ : b+l+i*x = c+l+j*x := congrArg Prod.fst he
    have h₂ : b+r+i*y = c+r+j*y := congrArg Prod.snd he
    have hz : (i-j)*(y-x)=0 := by linear_combination h₂-h₁
    have hij : i=j := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hn)
    subst j
    have hbc : b=c := by linear_combination h₁
    subst c
    rfl
  · rintro ⟨a,b⟩
    let i := (b-a-r+l)/(y-x)
    refine ⟨(i,a-l-i*x), ?_⟩
    apply Prod.ext
    · dsimp; ring
    · dsimp [i]; field_simp [hn]; ring
