import Definitions.Def_SeparatingTerminalDirect
import SigabaNeoStd.Machines.FromPTM
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Sampling
import Mathlib.Data.List.NodupEquivFin

namespace SeparatingPrivateSampler

open SigabaNeo Turing Cslib SeparatingTerminalMachine

abbrev Coord := Term × (Bool ⊕ Slot)
def offsets : List (Bool ⊕ Slot) := .inl false :: .inl true :: slots.map Sum.inr
def layout : List Coord := terms.product offsets

theorem term_all (t : Term) : t ∈ terms := by
  exact List.mem_map.mpr ⟨finProdFinEquiv t,by simp,finProdFinEquiv.symm_apply_apply _⟩

theorem slot_all (s : Slot) : s ∈ slots := by
  exact List.mem_map.mpr ⟨finProdFinEquiv s,by simp,finProdFinEquiv.symm_apply_apply _⟩

theorem layout_all (c : Coord) : c ∈ layout := by
  apply List.mem_product.mpr
  refine ⟨term_all _,?_⟩
  obtain ⟨t, (v|s)⟩ := c
  · cases v <;> simp [offsets]
  · simp [offsets,slot_all]

theorem layout_nodup : layout.Nodup := by
  apply List.Nodup.product
  · exact (List.nodup_finRange _).map finProdFinEquiv.symm.injective
  · have hd : slots.Nodup := (List.nodup_finRange _).map finProdFinEquiv.symm.injective
    simpa [offsets, List.nodup_map_iff Sum.inr_injective] using hd

def ix : Fin layout.length ≃ Coord :=
  List.Nodup.getEquivOfForallMemList layout layout_nodup layout_all

noncomputable def sampler (n : ℕ) : Machine := Machine.ofPTM MultiTapePTM.uniformListMachine (n+1)

theorem sampler_law (n : ℕ) :
    (sampler n).run (List.replicate n false) = BitString.uniformList n := by
  rw [sampler,Machine.run_ofPTM]
  simpa using MultiTapePTM.eval_uniformListMachine (List.replicate n false)

theorem sampler_cost (n : ℕ) : (sampler n).cost = n + 31 := by
  change n+1 + 6 * Nat.card Unit * 3^0 * 3^0 * (4+4*0+4*0+Nat.size 0+Nat.size (Nat.card Unit)) = _
  simp [Nat.size_zero]

theorem layout_length : layout.length = 798462 := by
  change (terms ×ˢ offsets).length = _
  rw [List.length_product]
  simp [offsets,terms,slots]

def pack (a : Coord → Bool) := layout.map a

def padAt (raw : List Bool) (t : Term) (s : Slot) : Bool :=
  raw[ix.symm (t,.inr s) |>.val]?.getD false

theorem read_pack (a : Coord → Bool) (t : Term) (s : Slot) :
    padAt (pack a) t s = a (t,.inr s) := by
  let i := ix.symm (t,.inr s)
  have hi : i.val < layout.length := i.isLt
  have h : layout[i.val] = (t,.inr s) := ix.apply_symm_apply _
  simp only [padAt,pack,List.getElem?_map]
  rw [List.getElem?_eq_getElem hi]
  exact congrArg a h

theorem pack_word (a : Coord → Bool) (b : Bool) :
    b :: pack a = (packet terms slots Prod.fst allow b
      (fun t ↦ a (t,.inl false)) (fun t ↦ a (t,.inl true)) (fun t s ↦ a (t,.inr s))).map Prod.snd := by
  simp [pack,layout,List.product,offsets,packet,block,List.map_flatMap,List.map_map,Function.comp_def]

theorem uniform_serial {A : Type} [Fintype A] [DecidableEq A] (l : List A) (lookup : Fin l.length ≃ A)
    (hl : ∀ i, lookup i = l.get i) :
    BitString.uniformList l.length =
    (Probability.PMF.uniformOfFintype (A → Bool)).map (fun a ↦ l.map a) := by
  let E : (A → Bool) ≃ (Fin l.length → Bool) :=
    Equiv.arrowCongr lookup.symm (Equiv.refl Bool)
  rw [BitString.uniformList,← Probability.PMF.uniformOfFintype_map_equiv E, PMF.map_comp]
  congr 1
  funext a
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [E, hl, Function.comp_def]

theorem sampler_assignments :
    (sampler layout.length).run (List.replicate layout.length false) =
    (Probability.PMF.uniformOfFintype (Coord → Bool)).map pack :=
  (sampler_law _).trans (uniform_serial layout ix (fun _ ↦ rfl))

/-- A private serialized tape from a fair scanner, followed by the verified dense correction
machine. The private return port retains only the source pads, discarding both share coins. -/
noncomputable def joint (b : Bool) : PMF ((Term → Slot → Bool) × List Bool) :=
  ((sampler layout.length).run (List.replicate layout.length false)).bind fun raw ↦
    (Direct.dense.run (b :: raw)).map fun ct ↦ (padAt raw,ct)

noncomputable def expected (b : Bool) (a : Coord → Bool) :=
  let pad := fun t s ↦ a (t,.inr s)
  (pad, terms.flatMap fun t ↦ slots.map fun s ↦
    if allow t s then AdvancedEncryption.WE.SeparatingTerminal.roleShare b
      (a (t,.inl false)) (a (t,.inl true)) s.1 ^^ pad t s else false)

theorem joint_correct (b : Bool) :
    joint b = (Probability.PMF.uniformOfFintype (Coord → Bool)).map (expected b) := by
  rw [joint,sampler_assignments,PMF.bind_map]
  change _ = (Probability.PMF.uniformOfFintype (Coord → Bool)).bind _
  apply congrArg (_root_.PMF.bind _)
  funext a
  simp only [Function.comp_apply]
  rw [pack_word, Direct.dense_run, encCorrection_run, PMF.pure_map]
  have h : padAt (pack a) = fun t s ↦ a (t,.inr s) := funext fun t ↦ funext (read_pack a t)
  rw [h]
  rfl

end SeparatingPrivateSampler
