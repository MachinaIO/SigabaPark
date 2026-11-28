import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace SemanticQueryBound
variable {I R C : Type} [Fintype I] [DecidableEq I]
def singletonOracle (i j : I) := decide (j=i)

/-- On the all-zero oracle, keep only the distinct positions inspected by the
encoder. An adaptive transcript is unchanged if another oracle agrees there. -/
theorem covers (enc : Bool → (I → Bool) → R → C)
    (dec : (I → Bool) → I → C → Bool) (queries : Bool → R → Finset I)
    (stable : ∀ m r f, (∀ i ∈ queries m r,f i=false) →
      enc m f r=enc m (fun _ ↦ false) r)
    (correct : ∀ m r i, dec (singletonOracle i) i (enc m (singletonOracle i) r)=m)
    (r s : R) (same : enc false (fun _ ↦ false) r=enc true (fun _ ↦ false) s) :
    queries false r ∪ queries true s = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  by_contra hn
  have h0 : i ∉ queries false r := fun hi ↦ hn (Finset.mem_union_left _ hi)
  have h1 : i ∉ queries true s := fun hi ↦ hn (Finset.mem_union_right _ hi)
  have z0 := stable false r (singletonOracle i) (fun j hj ↦ by
    have hji : j≠i := fun h ↦ h0 (h ▸ hj)
    simp [singletonOracle,hji])
  have z1 := stable true s (singletonOracle i) (fun j hj ↦ by
    have hji : j≠i := fun h ↦ h1 (h ▸ hj)
    simp [singletonOracle,hji])
  have bad := correct false r i
  rw [z0,same,← z1,correct true s i] at bad
  exact Bool.noConfusion bad

/-- Equality of full public laws under uniform finite coins supplies the common
ciphertext needed by the adversary argument. Decoder work is unrestricted. -/
theorem lower_bound [Fintype R] [Nonempty R] (enc : Bool → (I → Bool) → R → C)
    (dec : (I → Bool) → I → C → Bool) (queries : Bool → R → Finset I)
    (stable : ∀ m r f, (∀ i ∈ queries m r,f i=false) →
      enc m f r=enc m (fun _ ↦ false) r)
    (correct : ∀ m r i, dec (singletonOracle i) i (enc m (singletonOracle i) r)=m)
    (hidden : ∀ c, Nat.card {r : R // enc false (fun _ ↦ false) r=c} =
      Nat.card {s : R // enc true (fun _ ↦ false) s=c})
    (q : Nat) (bound : ∀ m r, (queries m r).card ≤ q) : Fintype.card I ≤ 2*q := by
  classical
  let r : R := Classical.choice ‹Nonempty R›
  let c := enc false (fun _ ↦ false) r
  have hp : 0 < Nat.card {t : R // enc false (fun _ ↦ false) t=c} :=
    Nat.card_pos_iff.mpr ⟨⟨⟨r,rfl⟩⟩,inferInstance⟩
  rw [hidden] at hp
  obtain ⟨⟨s,hs⟩⟩ := (Nat.card_pos_iff.mp hp).1
  have hh := covers enc dec queries stable correct r s hs.symm
  have total := Finset.card_union_le (queries false r) (queries true s)
  rw [hh,Finset.card_univ] at total
  have := bound false r; have := bound true s; omega

/-- A matching upper bound for arbitrary Boolean predicates on a balanced product. -/
def searchSide {J : Type} [Fintype J] (f : Bool × J → Bool) (m : Bool) : Option Bool :=
  if ∃ j, f (m,j)=true then some m else none
def openSide {J : Type} (w : Bool × J) (ct : Option Bool) : Bool := ct.getD (!w.1)

theorem search_correct {J : Type} [Fintype J] (f : Bool × J → Bool) (w : Bool × J)
    (hw : f w=true) (m : Bool) : openSide w (searchSide f m) = m := by
  unfold searchSide openSide; split
  · rfl
  · rename_i h
    have hn : w.1≠m := by intro he; apply h; exact ⟨w.2,he ▸ hw⟩
    cases w with | mk a j => cases a <;> cases m <;> simp_all

theorem search_hidden {J : Type} [Fintype J] (m : Bool) :
    searchSide (J:=J) (fun _ ↦ false) m=none := by simp [searchSide]

def side {J : Type} [Fintype J] (m : Bool) : Finset (Bool × J) :=
  Finset.univ.map ⟨fun j ↦ (m,j),fun _ _ h ↦ congrArg Prod.snd h⟩

theorem search_stable {J : Type} [Fintype J] (m : Bool) (f : Bool × J → Bool)
    (h : ∀ i ∈ side (J:=J) m,f i=false) : searchSide f m = searchSide (J:=J) (fun _ ↦ false) m := by
  have hn (j : J) : f (m,j)=false := h _ (Finset.mem_map.mpr ⟨j,Finset.mem_univ _,rfl⟩)
  simp [searchSide,hn]

theorem side_cost (m : Bool) : (side (J:=Fin 127 → Bool) m).card = 2^127 := by
  simp [side]

theorem size128 (q : Nat) (h : Fintype.card (Fin 128 → Bool) ≤ 2*q) : 2^127 ≤ q := by
  simp at h; omega

end SemanticQueryBound
