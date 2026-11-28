import SigabaNeoStd.Machines.Gates
import Mathlib.Data.List.FinRange
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import Mathlib.Tactic

namespace ColorInventoryDecision
open SigabaNeo Turing.MultiTapeTM
abbrev Vertex := Fin 32
abbrev Color := Fin 4 → Bool
abbrev Assignment := Vertex → Color
abbrev Domain := Bool × Bool

def adm (d : Domain) (v : Bool) := if v then d.2 else d.1
def known (v : Bool) : Domain := (!v,v)
def unknown : Domain := (true,true)

def nand (a b : Domain) : Domain := (a.2 && b.2,a.1 || b.1)

theorem nand_sound {a b : Domain} {x y : Bool} (hx : adm a x = true) (hy : adm b y = true) :
    adm (nand a b) (!(x && y)) = true := by cases x <;> cases y <;> simp_all [adm,nand]

theorem admit_get {ws : List Bool} {ds : List Domain}
    (h : List.Forall₂ (fun x d ↦ adm d x = true) ws ds) (i : Nat) :
    adm (ds.getD i (known true)) (ws.getD i true) = true := by
  induction h generalizing i with
  | nil => rfl
  | cons hv _ ih => cases i with
    | zero => exact hv
    | succ i => exact ih i

def dstep (s : List Domain × Domain) (g : Nat × Nat) : List Domain × Domain :=
  let v := nand (s.1.getD g.1 (known true)) (s.1.getD g.2 (known true))
  (s.1 ++ [v],v)

def Agree (s : List Bool × Bool) (t : List Domain × Domain) :=
  List.Forall₂ (fun x d ↦ adm d x = true) s.1 t.1 ∧ adm t.2 s.2 = true

theorem extend {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β} {x y}
    (h : List.Forall₂ R xs ys) (he : R x y) : List.Forall₂ R (xs++[x]) (ys++[y]) := by
  induction h with
  | nil => exact .cons he .nil
  | cons hh _ ih => exact .cons hh ih

theorem run_sound (s : List Bool × Bool) (t : List Domain × Domain) (h : Agree s t)
    (gs : GateList) : Agree (gs.foldl estep s) (gs.foldl dstep t) := by
  induction gs generalizing s t with
  | nil => exact h
  | cons g gs ih =>
    apply ih
    have hh := nand_sound (admit_get h.1 g.1) (admit_get h.1 g.2)
    exact ⟨extend h.1 hh,hh⟩

def keys : List (Vertex × Fin 4) := (List.finRange 128).map finProdFinEquiv.symm
def bits (w : Assignment) := keys.map (fun k ↦ w k.1 k.2)
def initial (a b : Vertex) (c : Color) := keys.map fun k ↦
  if k.1 = a ∨ k.1 = b then known (c k.2) else unknown

theorem init_sound (a b : Vertex) (w : Assignment) (h : w a = w b) :
    Agree (true :: bits w,true) (known true :: initial a b (w a),known true) := by
  refine ⟨.cons rfl ?_,rfl⟩
  unfold bits initial
  induction keys with
  | nil => exact .nil
  | cons k ks ih =>
    refine .cons ?_ ih
    by_cases he : k.1 = a ∨ k.1 = b
    · rcases he with hh|hh
      · cases hv : w a k.2 <;> simp [hh,hv,adm,known]
      · cases hv : w b k.2 <;> simp [hh,h,hv,adm,known]
    · cases hv : w k.1 k.2 <;> simp [he,hv,adm,unknown]

/-- Test an equal common word by deterministic two-valued upper bounds on every NAND wire. -/
def allowed (gs : GateList) (a b : Vertex) (c : Color) :=
  (gs.foldl dstep (known true :: initial a b c,known true)).2.2

def edge (gs : GateList) (a b : Vertex) : Bool :=
  decide (∀ c : Color, allowed gs a b c = false)

theorem edge_sound {gs : GateList} {a b : Vertex} {w : Assignment} (he : edge gs a b = true)
    (yes : evalGates (bits w,gs) = true) : w a ≠ w b := by
  intro eq
  have hh := (run_sound _ _ (init_sound a b w eq) gs).2
  change adm _ (evalGates (bits w,gs)) = true at hh
  rw [yes] at hh
  have hn : ∀ c : Color, allowed gs a b c = false := of_decide_eq_true he
  exact Bool.noConfusion ((hn (w a)).symm.trans hh)

/-- All candidates are generated from the public graph. Each candidate is rechecked. -/
def greedy (gs : GateList) (start : Vertex) := (List.finRange 32).foldl
  (fun acc v ↦ if v ∉ acc ∧ acc.all (edge gs v) then v :: acc else acc) [start]

def clique (gs : GateList) (vs : List Vertex) : Bool :=
  decide (17 ≤ vs.length ∧ vs.Pairwise (fun i j ↦ edge gs i j = true))

def gateDecoder := Decoder.list (Decoder.pair Decoder.unary Decoder.unary)

def reject (word : List Bool) : Bool :=
  let gs := gateDecoder.decode word
  (List.finRange 32).any (fun v ↦ clique gs (greedy gs v))

theorem clique_sound {vs : List Vertex} {gs : GateList} (hc : clique gs vs = true)
    (w : Assignment) : evalGates (bits w,gs) = false := by
  by_contra! h
  have ha : evalGates (bits w,gs) = true := by cases hv : evalGates (bits w,gs) <;> simp_all
  have hp : 17 ≤ vs.length ∧ vs.Pairwise (fun i j ↦ edge gs i j = true) := of_decide_eq_true hc
  have hn : (vs.map w).Nodup := List.pairwise_map.mpr
    (hp.2.imp (fun he ↦ edge_sound he ha))
  have bound := List.Nodup.length_le_card hn
  simp at bound
  omega

theorem reject_sound (gs : GateList) (h : reject (encGates gs) = true) (w : Assignment) :
    evalGates (bits w,gs) = false := by
  simp only [reject,gateDecoder.decode_enc,List.any_eq_true] at h
  obtain ⟨v,_,hc⟩ := h
  exact clique_sound hc w

/-- The registered assignment uses the same contiguous four-bit ordering. -/
theorem all_inputs (x : Fin 128 → Bool) : ∃ w, bits w = List.ofFn x := by
  let w : Assignment := fun i j ↦ x (finProdFinEquiv (i,j))
  refine ⟨w,?_⟩
  simp only [bits,keys,List.map_map]
  have he : (fun k : Vertex × Fin 4 ↦ w k.1 k.2) ∘ finProdFinEquiv.symm = x := by
    funext i
    simp [w,Function.comp_def]
  rw [he]
  exact List.ofFn_eq_map.symm

theorem registered_reject (gs : GateList) (h : reject (encGates gs) = true) (x : Fin 128 → Bool) :
    evalGates (List.ofFn x,gs) = false := by
  obtain ⟨w,hw⟩ := all_inputs x
  rw [← hw]; exact reject_sound gs h w


/-- Emit a sparse fixed-color inventory row only after checking every distinct position pair. -/
def emitRow (gs : GateList) (v : Fin 16 → Vertex) (c : Color) : Option (List (Vertex × Color)) :=
  if ∀ i j, i ≠ j → edge gs (v i) (v j) = true then
    some (List.ofFn fun i ↦ (v i,c)) else none

theorem emitted_row_sound (gs : GateList) (v : Fin 16 → Vertex) (c : Color)
    (out : List (Vertex × Color)) (ho : emitRow gs v c = some out)
    (w : Assignment) (yes : evalGates (bits w,gs) = true) :
    ∃! i : Fin 16, ∃ e, out[i.val]? = some e ∧ w e.1 = e.2 := by
  classical
  unfold emitRow at ho
  split at ho
  next he =>
    injection ho with hout
    subst out
    have hinj : Function.Injective (fun i ↦ w (v i)) := by
      intro i j hh
      by_contra hn
      exact edge_sound (he i j hn) yes hh
    let e : Color ≃ Fin 16 := Fintype.equivFinOfCardEq (by decide)
    obtain ⟨i,hi⟩ := (Finite.surjective_of_injective (e.injective.comp hinj)) (e c)
    have hv : w (v i) = c := e.injective hi
    have idx {n : Nat} (f : Fin n → Vertex × Color) (j : Fin n) : (List.ofFn f)[j.val]? = some (f j) := by
      rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using j.isLt)]
      simp only [List.getElem_ofFn]
    refine ⟨i,?_,?_⟩
    · exact ⟨(v i,c),idx _ _,hv⟩
    · intro j hj
      obtain ⟨p,hp,hval⟩ := hj
      have hp' : (v j,c) = p := by rw [idx] at hp; exact Option.some.inj hp
      subst p
      exact hinj (hval.trans hv.symm)
  next _ => cases ho

end ColorInventoryDecision
