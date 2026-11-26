import Definitions.Def_WE_WirePolarity

namespace PolarityProof
open AdvancedEncryption.WE.CircuitSAT AdvancedEncryption.WE.CircuitSAT.WirePolarity SigabaNeo

private theorem run_map {α β : Type} (h : α → β) (one : α) (op : α → α → α)
    (op' : β → β → β) (hop : ∀ a b, h (op a b) = op' (h a) (h b)) (gs : GateList)
    (w : List α) (last : α) :
    h (run one op gs w last) = run (h one) op' gs (w.map h) (h last) := by
  induction gs generalizing w last with
  | nil => rfl
  | cons g gs ih =>
    rcases g with ⟨a,b⟩
    change h (run one op gs _ _) = run (h one) op' gs _ _
    simp only [ih, List.map_append, List.map_cons, List.map_nil, hop, List.getD_map]

private theorem run_bool (gs : GateList) (w : List Bool) (last : Bool) :
    run true (fun a b ↦ !(a && b)) gs w last = (gs.foldl estep (w,last)).2 := by
  induction gs generalizing w last with
  | nil => rfl
  | cons g gs ih => cases g; exact ih _ _

private structure Wire (n : ℕ) where
  sign : Signs n
  val : (Fin n → Bool) → Bool
  mono : ∀ x y, (∀ i ∈ sign.pos, x i ≤ y i) → (∀ i ∈ sign.neg, y i ≤ x i) → val x ≤ val y

private def one (n : ℕ) : Wire n := ⟨⟨∅, ∅⟩, fun _ ↦ true, by simp⟩

private def var {n : ℕ} (i : Fin n) : Wire n :=
  ⟨⟨{i}, ∅⟩, fun x ↦ x i, fun _ _ hp _ ↦ hp i (by simp)⟩

private def nand {n : ℕ} (a b : Wire n) : Wire n where
  sign := combine a.sign b.sign
  val := fun x ↦ !(a.val x && b.val x)
  mono := by
    intro x y hp hn
    have ha := a.mono y x (fun i hi ↦ hn i (Finset.mem_union_left _ hi))
      (fun i hi ↦ hp i (Finset.mem_union_left _ hi))
    have hb := b.mono y x (fun i hi ↦ hn i (Finset.mem_union_right _ hi))
      (fun i hi ↦ hp i (Finset.mem_union_right _ hi))
    revert ha hb
    cases a.val x <;> cases a.val y <;> cases b.val x <;> cases b.val y <;> decide

private def out (n : ℕ) (gs : GateList) : Wire n :=
  run (one n) nand gs (one n :: List.ofFn var) (one n)

private theorem sign_out (n : ℕ) (gs : GateList) : (out n gs).sign = analyze n gs := by
  unfold out analyze
  rw [run_map Wire.sign _ _ combine (fun _ _ ↦ rfl)]
  simp [List.map_ofFn, one, var, Function.comp_def]

private theorem val_out {n : ℕ} (gs : GateList) (x : Fin n → Bool) :
    (out n gs).val x = evalGates (List.ofFn x,gs) := by
  have h := run_map (fun w : Wire n ↦ w.val x) (one n) nand (fun a b ↦ !(a && b))
    (fun _ _ ↦ rfl) gs (one n :: List.ofFn var) (one n)
  simp only [List.map_cons, List.map_ofFn, Function.comp_def] at h
  exact h.trans (run_bool gs _ _)

end PolarityProof

open PolarityProof AdvancedEncryption.WE.CircuitSAT
open AdvancedEncryption.WE.CircuitSAT.WirePolarity SigabaNeo

theorem solution {n s : ℕ} (φ : Circuit n s) :
    let p := analyze n φ.gates
    (∀ x : Fin n → Bool, Satisfies φ x →
      Satisfies φ (liftBits p (fun i ↦ x i.val))) ∧
    (∀ β : Bool, AdvancedEncryption.WE.CircuitSAT.WirePolarity.encBit (n := n) φ.gates β = true ↔ β = true ∧ ∃ x, Satisfies φ x) := by
  dsimp only
  let p := analyze n φ.gates
  have dom (x : Fin n → Bool) : Satisfies φ x →
      Satisfies φ (liftBits p (fun i ↦ x i.val)) := by
    intro hx
    let y := liftBits p (fun i ↦ x i.val)
    have le := (out n φ.gates).mono x y
    rw [sign_out] at le
    have hp (i) (hi : i ∈ p.pos) : x i ≤ y i := by
      by_cases h : i ∈ mixed p <;> simp [y, liftBits, h, hi]
    have hn (i) (hi : i ∈ p.neg) : y i ≤ x i := by
      by_cases h : i ∈ mixed p
      · simp [y, liftBits, h]
      · have h' : i ∉ p.pos := fun hp ↦ h (Finset.mem_inter.mpr ⟨hp, hi⟩)
        simp [y, liftBits, h, h']
    have hxy := le hp hn
    simp only [val_out] at hxy
    change evalGates (List.ofFn x,φ.gates) = true at hx
    change evalGates (List.ofFn y,φ.gates) = true
    rw [hx] at hxy
    exact le_antisymm (by cases evalGates (List.ofFn y,φ.gates) <;> decide) hxy
  refine ⟨dom, ?_⟩
  intro β
  simp only [encBit, Bool.and_eq_true, decide_eq_true_eq]
  apply and_congr_right
  intro _
  exact ⟨fun ⟨z,hz⟩ ↦ ⟨_, hz⟩, fun ⟨x,hx⟩ ↦ ⟨_, dom x hx⟩⟩
