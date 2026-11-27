import Definitions.Def_MixedOrderCircuit
import Mathlib.Data.Finset.Basic

namespace MixedOrderMask
open SigabaNeo MixedOrderCircuit

inductive A (ι : Type) where
  | unknown
  | fixed (b : Bool)
  | live (support : Finset ι)

variable {ι : Type} [DecidableEq ι]
abbrev Assignment (ι : Type) := ι → Bool

/-- A live wire is local to its support and can attain either value. -/
def Models (f : Assignment ι → Bool) : A ι → Prop
  | .unknown => True
  | .fixed b => ∀ x, f x = b
  | .live s => (∀ x y, (∀ i ∈ s, x i = y i) → f x = f y) ∧ ∀ b, ∃ x, f x = b

def flip : A ι → A ι
  | .unknown => .unknown
  | .fixed b => .fixed (!b)
  | .live s => .live s

theorem flip_sound {f : Assignment ι → Bool} {a : A ι} (h : Models f a) :
    Models (fun x ↦ !f x) (flip a) := by
  cases a with
  | unknown => trivial
  | fixed b => intro x; simp [h x]
  | live s =>
    refine ⟨fun x y he ↦ congrArg (!·) (h.1 x y he),fun b ↦ ?_⟩
    obtain ⟨x,hx⟩ := h.2 (!b)
    exact ⟨x,by simp [hx]⟩

def merge : A ι → A ι → A ι
  | .fixed false,_ | _,.fixed false => .fixed true
  | .fixed true,b => flip b
  | a,.fixed true => flip a
  | .live s,.live t => if Disjoint s t then .live (s ∪ t) else .unknown
  | _,_ => .unknown

theorem live_pair {f g : Assignment ι → Bool} {s t : Finset ι}
    (hf : Models f (.live s)) (hg : Models g (.live t)) (hd : Disjoint s t) :
    Models (fun x ↦ !(f x && g x)) (.live (s ∪ t)) := by
  refine ⟨fun x y h ↦ ?_,fun v ↦ ?_⟩
  · change (!(f x && g x)) = (!(f y && g y))
    rw [hf.1 x y (fun i hi ↦ h i (Finset.mem_union_left _ hi)),
      hg.1 x y (fun i hi ↦ h i (Finset.mem_union_right _ hi))]
  · cases v
    · obtain ⟨x,hx⟩ := hf.2 true
      obtain ⟨y,hy⟩ := hg.2 true
      let z := fun i ↦ if i ∈ s then x i else y i
      have ha : f z = f x := hf.1 _ _ (fun i hi ↦ by simp [z,hi])
      have hb : g z = g y := hg.1 _ _ (fun i hi ↦ by
        have hn : i ∉ s := fun h ↦ Finset.disjoint_left.mp hd h hi
        simp [z,hn])
      exact ⟨z,by simp [ha,hb,hx,hy]⟩
    · obtain ⟨x,hx⟩ := hf.2 false
      exact ⟨x,by simp [hx]⟩

theorem merge_sound {f g : Assignment ι → Bool} {a b : A ι}
    (hf : Models f a) (hg : Models g b) : Models (fun x ↦ !(f x && g x)) (merge a b) := by
  cases a with
  | fixed v =>
    cases v
    · exact fun x ↦ by simp [hf x]
    · have he : (fun x ↦ !(f x && g x)) = (fun x ↦ !g x) := funext fun x ↦ by simp [hf x]
      rw [he]; have heq : merge (.fixed true) b = flip b := by cases b with
        | fixed w => cases w <;> rfl
        | live | unknown => rfl
      rw [heq]; exact flip_sound hg
  | unknown =>
    cases b with
    | fixed v => cases v <;> simp [merge,flip,Models] <;> exact fun x ↦ Or.inr (hg x)
    | unknown | live => trivial
  | live s =>
    cases b with
    | unknown => trivial
    | fixed v =>
      cases v
      · exact fun x ↦ by simp [hg x]
      · have he : (fun x ↦ !(f x && g x)) = (fun x ↦ !f x) := funext fun x ↦ by simp [hg x]
        rw [he]; exact flip_sound hf
    | live t =>
      by_cases h : Disjoint s t
      · simpa only [merge,h,ite_true] using live_pair hf hg h
      · simp [merge,h,Models]

def step (s : List (A ι) × A ι) (g : Nat × Nat) : List (A ι) × A ι :=
  let a := s.1.getD g.1 (.fixed true)
  let b := s.1.getD g.2 (.fixed true)
  let z := if g.1 = g.2 then flip a else merge a b
  (s.1 ++ [z],z)

def valStep (s : List (Assignment ι → Bool) × (Assignment ι → Bool)) (g : Nat × Nat) :=
  let z := fun x ↦ !(s.1.getD g.1 (fun _ ↦ true) x && s.1.getD g.2 (fun _ ↦ true) x)
  (s.1 ++ [z],z)

def Matches (s : List (A ι) × A ι) (t : List (Assignment ι → Bool) × (Assignment ι → Bool)) :=
  List.Forall₂ (fun a f ↦ Models f a) s.1 t.1 ∧ Models t.2 s.2

theorem getD_models {l : List (A ι)} {fs : List (Assignment ι → Bool)}
    (h : List.Forall₂ (fun a f ↦ Models f a) l fs) (i : Nat) :
    Models (fs.getD i (fun _ ↦ true)) (l.getD i (.fixed true)) := by
  induction h generalizing i with
  | nil => exact fun _ ↦ rfl
  | cons ha _ ih => cases i with
    | zero => exact ha
    | succ i => exact ih i

theorem for_append {α β : Type} {R : α → β → Prop} {xs us : List α} {ys vs : List β}
    (h : List.Forall₂ R xs ys) (g : List.Forall₂ R us vs) :
    List.Forall₂ R (xs ++ us) (ys ++ vs) := by
  induction h with
  | nil => exact g
  | cons hh _ ih => exact .cons hh ih

theorem step_matches {s : List (A ι) × A ι} {t} (h : Matches s t) (g : Nat × Nat) :
    Matches (step s g) (valStep t g) := by
  have hh : Models (valStep t g).2 (step s g).2 := by
    by_cases he : g.1 = g.2
    · simpa [step,valStep,he] using flip_sound (getD_models h.1 g.2)
    · simpa only [step,valStep,he,ite_false] using
        merge_sound (getD_models h.1 g.1) (getD_models h.1 g.2)
  exact ⟨for_append h.1 (List.Forall₂.cons hh List.Forall₂.nil),hh⟩

theorem fold_matches {s : List (A ι) × A ι} {t} (h : Matches s t) (gs : GateList) :
    Matches (gs.foldl step s) (gs.foldl valStep t) := by
  induction gs generalizing s t with
  | nil => exact h
  | cons g gs ih => exact ih (step_matches h g)

def call (s : List (Assignment ι → Bool) × (Assignment ι → Bool)) (x : Assignment ι) :=
  (s.1.map (fun f ↦ f x),s.2 x)

theorem call_fold (s : List (Assignment ι → Bool) × (Assignment ι → Bool)) (gs : GateList)
    (x : Assignment ι) : call (gs.foldl valStep s) x = gs.foldl estep (call s x) := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons,ih]
    congr 1
    have hread (i : Nat) : (s.1.map (fun f ↦ f x)).getD i true =
        s.1.getD i (fun _ ↦ true) x := by
      simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
      cases s.1[i]? <;> rfl
    simp only [call,valStep,estep,hread,List.map_append,List.map_cons,List.map_nil]

def summary (n : Nat) (addr : List Bool) (gs : GateList) : A (Fin n) :=
  (gs.foldl step (.fixed true :: ((List.finRange n).map (fun i ↦ .live {i}) ++
    addr.map A.fixed),.fixed true)).2

theorem summary_sound (n : Nat) (addr : List Bool) (gs : GateList) :
    Models (fun x ↦ evalGates ((List.finRange n).map x ++ addr,gs)) (summary n addr gs) := by
  let s : List (A (Fin n)) × A (Fin n) := (.fixed true ::
    ((List.finRange n).map (fun i ↦ .live {i}) ++ addr.map A.fixed),.fixed true)
  let t : List (Assignment (Fin n) → Bool) × (Assignment (Fin n) → Bool) :=
    ((fun _ ↦ true) :: ((List.finRange n).map (fun i x ↦ x i) ++ addr.map (fun b _ ↦ b)),
      fun _ ↦ true)
  have h : Matches s t := by
    refine ⟨List.Forall₂.cons (fun _ ↦ rfl) ?_,fun _ ↦ rfl⟩
    apply for_append
    · induction List.finRange n with
      | nil => exact .nil
      | cons i is ih =>
        exact .cons ⟨fun _ _ he ↦ he i (by simp),fun b ↦ ⟨fun _ ↦ b,rfl⟩⟩ ih
    · induction addr with
      | nil => exact .nil
      | cons b _ ih => exact .cons (fun _ ↦ rfl) ih
  have hv : (gs.foldl valStep t).2 = (fun x ↦ evalGates ((List.finRange n).map x ++ addr,gs)) := by
    funext x
    have hx := congrArg Prod.snd (call_fold t gs x)
    simpa [t,call,evalGates,List.map_map,Function.comp_def] using hx
  exact hv ▸ (fold_matches h gs).2

def branch (n : Nat) (addr : List Bool) (gs : GateList) : Option Bool :=
  match summary n addr gs with
  | .unknown => none
  | .fixed b => some b
  | .live _ => some true

theorem branch_sound {n : Nat} {addr : List Bool} {gs : GateList} {v : Bool}
    (h : branch n addr gs = some v) : v = true ↔
      ∃ x, evalGates ((List.finRange n).map x ++ addr,gs) = true := by
  have hs := summary_sound n addr gs
  cases ha : summary n addr gs with
  | unknown => simp [branch,ha] at h
  | fixed b =>
    rw [ha] at hs
    have hb : b = v := by simpa [branch,ha] using h
    subst v
    exact ⟨fun e ↦ ⟨fun _ ↦ false,(hs _).trans e⟩,fun ⟨x,hx⟩ ↦ (hs x).symm.trans hx⟩
  | live s =>
    rw [ha] at hs
    have hb : true = v := by simpa [branch,ha] using h
    subst v
    exact ⟨fun _ ↦ hs.2 true,fun _ ↦ rfl⟩


def decideWord (n k : Nat) (w : List Bool) : Option Bool :=
  collect (fun a ↦ branch n a (gateDecoder.decode w)) (addresses k)

theorem decideWord_sound {n k : Nat} {gs : GateList} {v : Bool}
    (h : decideWord n k (encGates gs) = some v) :
    v = true ↔ ∃ a, a.length = k ∧ ∃ x, evalGates ((List.finRange n).map x ++ a,gs) = true := by
  simp only [decideWord,decode_gates] at h
  simpa only [mem_addresses] using collect_sound (P := fun a ↦
    ∃ x, evalGates ((List.finRange n).map x ++ a,gs) = true)
    (fun _ _ hc ↦ branch_sound hc) (addresses k) v h

/-- One of the full registered input limits, prior to its outer tuple frame. -/
theorem input_bound (gs : GateList) (hl : gs.length = 4096)
    (hw : ∀ g ∈ gs, g.1 ≤ 4224 ∧ g.2 ≤ 4224) : (encGates gs).length < 2^27 := by
  have h := length_encGates_le gs hw
  rw [hl] at h
  omega

theorem logical_record_bits : (1+128+4096)*(124+2) = 532350 := by decide

end MixedOrderMask
