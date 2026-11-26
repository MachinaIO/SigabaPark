import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrder3Assembly

set_option autoImplicit true

noncomputable section

namespace SigabaNeo.Rogers.PlaneParam

variable {n r k q : ℕ} (A : Diagram r k (q+1))

/-- Integer reconstruction, with the independent-frame condition imposed separately. -/
def expand (x : Fin r → Fin n → ℤ) (j : Fin k) (l : Fin n) : ℤ :=
  ∑ a, diagramIntegerEntry A a j * x a l

def Compatible (z : Fin k → Fin n → ℤ) : Prop :=
  ∀ j l, ((q+1 : ℕ) : ℤ) * z j l = ∑ i, A.entry i j * z (A.pivot i) l

theorem expand_compatible (x : Fin r → Fin n → ℤ) : Compatible A (expand A x) := by
  intro j l
  simp only [expand, diagramIntegerEntry_pivot, Finset.mul_sum, ← mul_assoc,
    diagramIntegerEntry_spec, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  ring

private def pivotRow (z : Fin k → Fin n → ℤ) (hz : Compatible A z) (l : Fin n) :
    (diagramResidue A).ker :=
  ⟨fun i ↦ z (A.pivot i) l, (diagramResidue_mem_ker_iff A _).mpr fun j ↦
    ⟨z j l, by simpa only [mul_comm (z _ l)] using (hz j l).symm⟩⟩

private def recover (z : Fin k → Fin n → ℤ) (hz : Compatible A z) (a : Fin r) (l : Fin n) :=
  (diagramKernelBasis A).repr (pivotRow A z hz l) a

theorem expand_injective : Function.Injective (@expand n _ _ _ A) := by
  intro x y he
  funext a l
  let b := diagramKernelBasis A
  have h : ∑ i, x i l • b i = ∑ i, y i l • b i := by
    apply Subtype.ext
    funext j
    have hh := congrFun (congrFun he (A.pivot j)) l
    simpa [expand, diagramIntegerEntry_pivot, diagramBasisMatrix_entry, b,
      Finset.sum_apply, mul_comm] using hh
  simpa [Module.Basis.repr_self, Finsupp.single_apply] using
    congrArg (fun v ↦ b.repr v a) h

theorem expand_range (z : Fin k → Fin n → ℤ) : z ∈ Set.range (expand A) ↔ Compatible A z := by
  constructor
  · rintro ⟨x,rfl⟩
    exact expand_compatible A x
  intro hz
  let x := recover A z hz
  have hp (i l) : expand A x (A.pivot i) l = z (A.pivot i) l := by
    have h := congrArg (fun v : (diagramResidue A).ker ↦ v.val i)
      ((diagramKernelBasis A).sum_repr (pivotRow A z hz l))
    simpa [-Module.Basis.sum_repr, expand, x, recover, diagramIntegerEntry_pivot, diagramBasisMatrix_entry,
      Finset.sum_apply, mul_comm, pivotRow] using h
  refine ⟨x, funext fun j ↦ funext fun l ↦ ?_⟩
  apply mul_left_cancel₀ (show ((q+1 : ℕ) : ℤ) ≠ 0 by positivity)
  simp only [expand_compatible A x j l, hp, hz j l]

end SigabaNeo.Rogers.PlaneParam
