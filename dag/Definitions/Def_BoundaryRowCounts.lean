import Mathlib.Tactic
namespace BoundaryRowCounts

/-- At every layer at least one of the two states is reachable. -/
def Covered {n : Nat} (live : Fin n → Bool → Bool) := ∀ i, ∃ b, live i b=true

theorem unique_dead {n : Nat} {live : Fin n → Bool → Bool} (h : Covered live)
    (i : Fin n) {a b : Bool} (ha : live i a=false) (hb : live i b=false) : a=b := by
  obtain ⟨w,hw⟩ := h i
  cases a <;> cases b <;> cases w <;> simp_all

abbrev DeadSlots {n : Nat} (live : Fin n → Bool → Bool) (r : Nat) :=
  {x : (Fin n × Bool) × Fin r // live x.1.1 x.1.2=false}

def forgetState {n r : Nat} {live : Fin n → Bool → Bool} (h : Covered live) :
    DeadSlots live r ↪ Fin n × Fin r where
  toFun x := (x.val.1.1,x.val.2)
  inj' := by
    rintro ⟨⟨⟨i,a⟩,x⟩,ha⟩ ⟨⟨⟨j,b⟩,y⟩,hb⟩ he
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    have hz := unique_dead h i ha hb
    cases hz; rfl

theorem row_count {n : Nat} (live : Fin n → Bool → Bool) (h : Covered live) (r : Nat) :
    Fintype.card (DeadSlots live r) ≤ n*r := by
  simpa only [Fintype.card_prod,Fintype.card_fin] using
    Fintype.card_le_of_injective _ (forgetState (r:=r) h).injective

/-- Select one arbitrary clean symbol at each layer. Every clean word is
realizable since the coordinates refer to disjoint blocks. -/
def parity {n : Nat} {A : Type} (h : Fin n → A → ZMod 2) (w : Fin n → A) :=
  ∑ i,h i (w i)

theorem no_implies_constant {n : Nat} {A : Type} [Nonempty A]
    (h : Fin n → A → ZMod 2) (no : ∀ w,parity h w=0) (i : Fin n) (a b : A) :
    h i a=h i b := by
  classical
  let w : Fin n → A := fun _ ↦ Classical.choice inferInstance
  have ex (z : A) : parity h (Function.update w i z) =
      h i z + ∑ j ∈ Finset.univ.erase i,h j (w j) := by
    unfold parity
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    simp only [Function.update_self]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have ha := no (Function.update w i a)
  have hb := no (Function.update w i b)
  rw [ex] at ha hb
  exact add_right_cancel (ha.trans hb.symm)

theorem general_cap (live : Fin 42 → Bool → Bool) (h : Covered live) :
    Fintype.card (DeadSlots live 6)+1 ≤ 253 := by have := row_count live h 6; omega

theorem xor_cap (live : Fin 42 → Bool → Bool) (h : Covered live) :
    Fintype.card (DeadSlots live 4)+1 ≤ 169 := by have := row_count live h 4; omega

end BoundaryRowCounts
