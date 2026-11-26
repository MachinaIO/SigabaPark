module

public import Definitions.Def_LatticeAttack_Planted_Probability

set_option autoImplicit true

public section
namespace SigabaNeo.SampleDeletion

@[expose] def normSq {ι : Type*} [Fintype ι] (z : ι → ℤ) := ∑ i, (z i).natAbs ^ 2

/-- Summing over signed coordinates includes the two signs of every positive square. -/
@[expose] def ballCount : ℕ → ℕ → ℕ
  | 0, _ => 1
  | d+1, j => ∑ a ∈ Finset.Icc (-(j.sqrt : ℤ)) (j.sqrt : ℤ),
      ballCount d (j - a.natAbs ^ 2)

abbrev Points (ι : Type*) [Fintype ι] (j : ℕ) := {z : ι → ℤ // normSq z ≤ j}

private theorem cons_sq {d} (z : Fin (d+1) → ℤ) :
    normSq z = (z 0).natAbs^2 + normSq (Fin.tail z) := Fin.sum_univ_succ _

private theorem coord_mem {a : ℤ} {j : ℕ} :
    a ∈ Finset.Icc (-(j.sqrt : ℤ)) (j.sqrt : ℤ) ↔ a.natAbs^2 ≤ j := by
  rw [Finset.mem_Icc, ← abs_le, ← Int.natCast_natAbs, Nat.cast_le, pow_two,
    ← Nat.le_sqrt]

private def splitPoint (d j : ℕ) : Points (Fin (d+1)) j ≃
    (Σ a : ↥(Finset.Icc (-(j.sqrt : ℤ)) (j.sqrt : ℤ)), Points (Fin d) (j-a.val.natAbs^2)) where
  toFun z := by
    have h := z.property
    rw [cons_sq] at h
    exact ⟨⟨z.val 0, coord_mem.mpr (by omega)⟩, Fin.tail z.val, by dsimp; omega⟩
  invFun := fun ⟨a,z⟩ ↦ ⟨Fin.cons a.val z.val, by
    rw [cons_sq, Fin.cons_zero, Fin.tail_cons]
    have := coord_mem.mp a.property
    have := z.property
    omega⟩
  left_inv z := Subtype.ext (Fin.cons_self_tail _)
  right_inv := fun ⟨a,z⟩ ↦ by cases a; cases z; rfl

private instance pointsFinite (ι : Type*) [Fintype ι] (j : ℕ) : Finite (Points ι j) := by
  let f (z : Points ι j) (i : ι) : ↥(Finset.Icc (-(j.sqrt : ℤ)) (j.sqrt : ℤ)) :=
    ⟨z.val i, coord_mem.mpr ((Finset.single_le_sum (f := fun i ↦ (z.val i).natAbs^2)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)).trans z.property)⟩
  exact Finite.of_injective f fun _ _ h ↦ Subtype.ext (funext fun i ↦ congrArg Subtype.val (congrFun h i))

theorem card_points_fin (d j : ℕ) : Nat.card (Points (Fin d) j) = ballCount d j := by
  classical
  induction d generalizing j with
  | zero =>
    have e : Points (Fin 0) j ≃ Unit :=
      { toFun := fun _ ↦ (), invFun := fun _ ↦ ⟨0, by simp [normSq]⟩
        left_inv := fun _ ↦ Subtype.ext (Subsingleton.elim _ _)
        right_inv := fun _ ↦ rfl }
    rw [Nat.card_congr e]; simp [ballCount]
  | succ d ih =>
    rw [Nat.card_congr (splitPoint d j), Nat.card_sigma]
    simp only [ih, ballCount]
    exact (Finset.sum_coe_sort _ (fun a : ℤ ↦ ballCount d (j-a.natAbs^2)))

def reindexPoints {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (j : ℕ) :
    Points ι j ≃ Points κ j where
  toFun z := ⟨z.val ∘ e.symm, (e.symm.sum_comp (fun i ↦ (z.val i).natAbs^2)).le.trans z.property⟩
  invFun z := ⟨z.val ∘ e, (e.sum_comp (fun i ↦ (z.val i).natAbs^2)).le.trans z.property⟩
  left_inv z := by ext; simp
  right_inv z := by ext; simp

theorem card_points (ι : Type*) [Fintype ι] (j : ℕ) :
    Nat.card (Points ι j) = ballCount (Fintype.card ι) j :=
  (Nat.card_congr (reindexPoints (Fintype.equivFin ι) j)).trans (card_points_fin _ _)

end SigabaNeo.SampleDeletion
#print axioms SigabaNeo.SampleDeletion.card_points
