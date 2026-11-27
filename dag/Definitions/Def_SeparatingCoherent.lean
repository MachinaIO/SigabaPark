import Definitions.Def_WE_SeparatingTerminal
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

namespace SeparatingCoherent

open AdvancedEncryption.WE.SeparatingTerminal
open scoped BigOperators Matrix

/-- Query-address histories, most recent address first. -/
def History (D : Type) : ℕ → Type
  | 0 => Unit
  | n+1 => D × History D n

instance histFinite (D : Type) [Fintype D] : (n : ℕ) → Fintype (History D n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => letI := histFinite D n; inferInstanceAs (Fintype (D × History D n))

def visits {D : Type} : (n : ℕ) → History D n → D → Prop
  | 0, _, _ => False
  | n+1, h, d => d = h.1 ∨ visits n h.2 d

variable {D Y H : Type} [Fintype D] [Fintype H] [DecidableEq H]

abbrev Mat (H : Type) := Matrix H H ℂ

/-- K n d y is the address-d summand of the nth oracle and the following public operation. -/
def path (K : ℕ → D → Y → Mat H) (f : D → Y) : (n : ℕ) → History D n → Mat H
  | 0, _ => 1
  | n+1, h => K n h.1 (f h.1) * path K f n h.2

def evolve (K : ℕ → D → Y → Mat H) (f : D → Y) : ℕ → Mat H
  | 0 => 1
  | n+1 => (∑ d, K n d (f d)) * evolve K f n

theorem expand (K : ℕ → D → Y → Mat H) (f : D → Y) (n : ℕ) :
    evolve K f n = ∑ h : History D n, path K f n h := by
  induction n with
  | zero => change 1 = ∑ _ : Unit, (1 : Mat H); simp
  | succ n ih =>
    change _ = ∑ h : D × History D n, K n h.1 (f h.1) * path K f n h.2
    rw [evolve, ih, Fintype.sum_prod_type, Finset.sum_mul]
    simp only [Finset.mul_sum]

omit [Fintype D] in
theorem path_local (K : ℕ → D → Y → Mat H) (f g : D → Y) (n : ℕ) (h : History D n)
    (ha : ∀ d, visits n h d → f d = g d) : path K f n h = path K g n h := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [path]
    rw [ha h.1 (Or.inl rfl), ih h.2 (fun d hd ↦ ha d (Or.inr hd))]

def Mask {I : Type} (src : D → Role × I) (n : ℕ) (h k : History D n) (r : Role) (i : I) : Prop :=
  ∃ d, (visits n h d ∨ visits n k d) ∧ src d = (r,i)

variable {I T : Type} [DecidableEq I] {e : Role → I → T → Prop}

def answer (s : Coins e) (a : Role × I) (k : Index e) : Bool :=
  if (k.val.1,k.val.2.1) = a then s.2.2 k else false

def publicBits (b : Bool) (s : Coins e) := (view (fun _ _ ↦ False) b s).1

theorem local_answer {o : Role → I → Prop} {b b' : Bool} {s z : Coins e}
    (hv : view o b s = view o b' z) (a : Role × I) (ha : o a.1 a.2) :
    answer s a = answer z a := by
  funext k
  unfold answer
  split
  · rename_i eq
    have h : o k.val.1 k.val.2.1 := by simpa [← eq] using ha
    exact congrFun (congrArg Prod.snd hv) ⟨k,h⟩
  · rfl

/-- Unnormalized block of the final density matrix for one fixed complete public record. All
coins carry the same mass; dividing by their common count gives the usual density block. -/
noncomputable def block [Fintype (Coins e)] (src : D → Role × I)
    (K : ℕ → D → (Index e → Bool) → Mat H) (ρ : Mat H)
    (n : ℕ) (c : Index e → Bool) (b : Bool) : Mat H := by
  classical
  exact ∑ s : Coins e, if publicBits b s = c then
    let U := evolve K (fun d ↦ answer s (src d)) n
    U * ρ * U.conjTranspose else 0

theorem pair_losing [Fintype (Coins e)] (src : D → Role × I)
    (K : ℕ → D → (Index e → Bool) → Mat H) (ρ : Mat H)
    (n : ℕ) (c : Index e → Bool) (b : Bool)
    (loss : ∀ h k : History D n, ¬ Wins e (Mask src n h k)) :
    block src K ρ n c b = block src K ρ n c (!b) := by
  classical
  let term (d : Bool) (s : Coins e) (h k : History D n) : Mat H :=
    if publicBits d s = c then path K (fun i ↦ answer s (src i)) n h * ρ *
      (path K (fun i ↦ answer s (src i)) n k).conjTranspose else 0
  have sum_block (d : Bool) : block src K ρ n c d =
      ∑ h, ∑ k, ∑ s : Coins e, term d s h k := by
    calc
      _ = ∑ s : Coins e, ∑ h, ∑ k, term d s h k := by
        unfold block
        apply Finset.sum_congr rfl
        intro s _
        by_cases hs : publicBits d s = c
        · simp only [hs, ite_true, expand, Matrix.conjTranspose_sum, Finset.sum_mul,
            Finset.mul_sum, term]
          exact Finset.sum_comm
        · simp [hs, term]
      _ = ∑ h, ∑ s : Coins e, ∑ k, term d s h k := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun h _ ↦ Finset.sum_comm
  rw [sum_block, sum_block]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro k _
  obtain ⟨m,hm⟩ := missing_role e _ (loss h k)
  let E : Coins e ≃ Coins e :=
    ⟨toggle m,toggle m,toggle_twice m,toggle_twice m⟩
  rw [← E.sum_comp (fun s ↦ term (!b) s h k)]
  apply Finset.sum_congr rfl
  intro s _
  have hv := view_toggle hm b s
  have hp : publicBits (!b) (E s) = publicBits b s := by
    have hpub := congrArg Prod.fst hv
    exact hpub
  have ha (i : D) (hh : visits n h i ∨ visits n k i) :
      answer (E s) (src i) = answer s (src i) :=
    local_answer hv _ ⟨i,hh,rfl⟩
  simp only [term,hp]
  rw [path_local K (fun i ↦ answer (E s) (src i)) (fun i ↦ answer s (src i))
        n h (fun i hi ↦ ha i (Or.inl hi)),
      path_local K (fun i ↦ answer (E s) (src i)) (fun i ↦ answer s (src i))
        n k (fun i hi ↦ ha i (Or.inr hi))]

/-- Two addresses cannot occupy all three roles, even on an unrestricted single-query oracle. -/
theorem one_losing (src : D → Role × I) (h k : History D 1) :
    ¬ Wins e (Mask src 1 h k) := by
  have spare : ∀ a c : Fin 3, ∃ r : Fin 3, r ≠ a ∧ r ≠ c := by decide
  obtain ⟨r,ha,hc⟩ := spare (src h.1).1 (src k.1).1
  rintro ⟨t, ht⟩
  obtain ⟨i, ⟨d,hd,hs⟩,_⟩ := ht r
  have hr := congrArg Prod.fst hs
  rcases hd with (hh|hh)|(hh|hh)
  · exact ha (hh ▸ hr.symm)
  · exact hh.elim
  · exact hc (hh ▸ hr.symm)
  · exact hh.elim

theorem one_equal [Fintype (Coins e)] (src : D → Role × I)
    (K : ℕ → D → (Index e → Bool) → Mat H) (ρ : Mat H) (c : Index e → Bool) :
    block src K ρ 1 c false = block src K ρ 1 c true :=
  pair_losing src K ρ 1 c false (one_losing src)

/-- Address components of the ordinary XOR lookup on a word, leaving the ancillary basis alone. -/
noncomputable def xorPiece {J W : Type} [DecidableEq (D × (J → Bool) × W)]
    (d : D) (y : J → Bool) : Mat (D × (J → Bool) × W) := by
  classical
  exact fun row col ↦ if col.1 = d ∧
    row = (d,fun j ↦ col.2.1 j ^^ y j,col.2.2) then 1 else 0

theorem xor_oracle {J W : Type} [DecidableEq (D × (J → Bool) × W)]
    (f : D → J → Bool) (row col : D × (J → Bool) × W) :
    (∑ d, xorPiece d (f d) row col) =
      (if row = (col.1,fun j ↦ col.2.1 j ^^ f col.1 j,col.2.2) then 1 else 0) := by
  classical
  rw [Finset.sum_eq_single col.1]
  · simp [xorPiece]
  · intro d _ hd
    simp [xorPiece, Ne.symm hd]
  · simp

end SeparatingCoherent
