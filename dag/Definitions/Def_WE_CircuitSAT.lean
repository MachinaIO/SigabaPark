import Definitions.Def_WE
import SigabaNeoStd.Machines.Gates
import SigabaNeoStd.Lattices.LWE
import SigabaNeoStd.Lattices.RingLWE
import SigabaNeoStd.Lattices.ModuleLWE
import SigabaNeoStd.Lattices.CircularRingLWE
import SigabaNeo.Trusted.Submission

/-!
# Witness encryption for NAND-circuit satisfiability

Witness encryption (`AdvancedEncryption.WE`) for the satisfiability of NAND circuits with
`n = 128` input bits and `s = 2^12` gates, at `λ = κ = 128`. This file is the problem author's: it
fixes the relation, the parameters and the registry of assumptions, and so what a submission must
achieve and at which cost it is measured.

**Circuits.** A statement `φ : Circuit n s` is `s` NAND gates; gate `i` reads two wires by index,
each below `n + 1 + s`. The wires are those of `SigabaNeo.evalGates` (`SigabaNeoStd.Machines.Gates`):
wire `0` is the constant `true`, wires `1, …, n` are the input bits, and wire `n + 1 + j` is the
output of gate `j`; a wire not yet computed (a forward reference) reads `true`. The circuit's output
is that of its last gate. A statement is encoded as its gate list in the format of
`SigabaNeo.encGates` (each index in unary).

**Witnesses.** An assignment `x : Fin n → Bool`, encoded as its `n` bits in order. The relation is
`evalGates (x, φ) = true`: the circuit outputs `1`.

**Why this relation.** It is the statement class of Theorem 1.1 of Hair–Sahai (arXiv 2609.18275,
"it suffices to treat Boolean circuit SAT"), NP-complete, with statements and witnesses of bounded
length (the condition the note of `Def_WE` asks of instances). Deciding the language by brute force
costs about `2^128 · s` steps, and a hard-wired table of the language is about `2^{|φ|}` bits, so
trivial implementations are far more expensive than the intended constructions.

**Registry.** The plain post-quantum lattice assumptions of `SigabaNeoStd`: decision LWE, Ring-LWE,
Module-LWE and circular Ring-LWE with automorphism keys, each with its security function. An
assumption Design AI registers later (for example decomposed LWE) comes with a new Submission
proposition over an extended registry.

**Checks.** `allNand00` is a circuit no assignment satisfies (`allNand00_unsat`) and `falseThenTrue`
one every assignment satisfies (`falseThenTrue_sat`): the language is neither empty nor everything,
so neither proposition is vacuous for this relation.
-/

namespace AdvancedEncryption.WE.CircuitSAT

open SigabaNeo SigabaNeo.Lattices

/-! ### The relation -/

/-- A NAND circuit with `n` inputs and `s` gates: the two wires each gate reads. -/
abbrev Circuit (n s : ℕ) := Fin s → Fin (n + 1 + s) × Fin (n + 1 + s)

/-- The gate list of a circuit, in the format of `SigabaNeo.evalGates`. -/
def Circuit.gates {n s : ℕ} (φ : Circuit n s) : GateList :=
  List.ofFn fun i => ((φ i).1.val, (φ i).2.val)

theorem Circuit.gates_injective (n s : ℕ) : Function.Injective (Circuit.gates (n := n) (s := s)) := by
  intro φ ψ h
  have h' := List.ofFn_injective h
  funext i
  have hi := congrFun h' i
  simp only [Prod.mk.injEq] at hi
  exact Prod.ext (Fin.ext hi.1) (Fin.ext hi.2)

/-- The encoding of a circuit: its gate list, each index in unary. -/
def encCircuit (n s : ℕ) : Circuit n s ↪ List Bool :=
  ⟨fun φ => encGates φ.gates, encGates.injective.comp (Circuit.gates_injective n s)⟩

/-- The encoding of an assignment: its `n` bits in order. -/
def encAssignment (n : ℕ) : (Fin n → Bool) ↪ List Bool :=
  ⟨fun x => List.ofFn x, fun _ _ h => List.ofFn_injective h⟩

/-- The circuit outputs `1` on the assignment. -/
def Satisfies {n s : ℕ} (φ : Circuit n s) (x : Fin n → Bool) : Prop :=
  evalGates (List.ofFn x, φ.gates) = true

/-- NAND-circuit satisfiability with `n` inputs and `s` gates. The relation is fixed, so the
algorithms are given no description of it. -/
def relation (n s : ℕ) : Relation where
  Stmt := Circuit n s
  Wit := Fin n → Bool
  encStmt := encCircuit n s
  encWit := encAssignment n
  rel := Satisfies
  desc := []

/-! ### The primitive -/

/-- The number of input bits. -/
abbrev inputs : ℕ := 128

/-- The number of gates. -/
abbrev size : ℕ := 2 ^ 12

/-- `λ = 128` and `κ = 128`. -/
def params : Params where
  secBits := 128
  corrBits := 128

/-- Witness encryption for NAND-circuit satisfiability with 128 inputs and `2^12` gates. -/
def P : Primitive := AdvancedEncryption.WE (relation inputs size) params

/-! ### The registry -/

/-- The registered assumptions: `0` decision LWE, `1` decision Ring-LWE, `2` decision Module-LWE,
`3` decision circular Ring-LWE with automorphism keys. -/
noncomputable def assumptions : Fin 4 → Assumption :=
  ![LWE.decision, RingLWE.decision, ModuleLWE.decision, CircularRingLWE.decision]

/-- The registry. -/
noncomputable def R : Registry := Registry.of assumptions

/-- The Submission proposition that Design AI proves for its submission `u`. -/
def SubmissionProp : Submission P R → Prop := Spec P R

/-! ### Checks of the definition -/

/-- The circuit all of whose gates are `NAND(1, 1) = 0`. -/
def allNand00 (n s : ℕ) : Circuit n s := fun _ => (0, 0)

/-- Gate `0` is `NAND(1, 1) = 0` (wire `n + 1`); every later gate is `NAND(1, wire n+1) = 1`. -/
def falseThenTrue (n s : ℕ) : Circuit n s := fun i =>
  if i.val = 0 then (0, 0) else (0, ⟨n + 1, by have := i.isLt; omega⟩)

theorem foldl_estep_zero (gs : GateList) (hgs : ∀ g ∈ gs, g = (0, 0)) (w : List Bool) (b : Bool) :
    (gs.foldl estep (true :: w, b)).2 = if gs = [] then b else false := by
  induction gs generalizing w b with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, hgs g (by simp)]
    have hst : estep (true :: w, b) (0, 0) = (true :: (w ++ [false]), false) := by
      simp [estep]
    rw [hst, ih (fun g hg => hgs g (by simp [hg]))]
    split <;> simp

theorem allNand00_unsat {n s : ℕ} (hs : 0 < s) (x : Fin n → Bool) :
    ¬ Satisfies (allNand00 n s) x := by
  unfold Satisfies evalGates
  rw [foldl_estep_zero]
  · have : (allNand00 n s).gates ≠ [] := by
      simp [Circuit.gates, List.ofFn_eq_nil_iff]; omega
    simp [this]
  · intro g hg
    simp only [Circuit.gates, allNand00, List.mem_ofFn] at hg
    obtain ⟨_, rfl⟩ := hg
    rfl

theorem foldl_estep_copy (n : ℕ) (j : ℕ) (v : List Bool) (c : Bool) (hl : n + 2 ≤ v.length)
    (hv0 : v.getD 0 true = true) (hv1 : v.getD (n + 1) true = false) :
    ((List.replicate j ((0 : ℕ), n + 1)).foldl estep (v, c)).2 = if j = 0 then c else true := by
  induction j generalizing v c with
  | zero => simp
  | succ j ihj =>
    rw [List.replicate_succ, List.foldl_cons]
    have e : estep (v, c) (0, n + 1) = (v ++ [true], true) := by
      simp only [List.getD_eq_getElem?_getD] at hv0 hv1
      simp [estep, hv1]
    rw [e, ihj]
    · split <;> simp
    · simp; omega
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
        ← List.getD_eq_getElem?_getD, hv0]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
        ← List.getD_eq_getElem?_getD, hv1]

theorem falseThenTrue_sat {n s : ℕ} (hs : 2 ≤ s) (x : Fin n → Bool) :
    Satisfies (falseThenTrue n s) x := by
  unfold Satisfies evalGates
  have hg : (falseThenTrue n s).gates = (0, 0) :: List.replicate (s - 1) ((0 : ℕ), n + 1) := by
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    simp only [Circuit.gates, List.ofFn_succ, falseThenTrue, Fin.val_zero, ite_true, Fin.val_succ,
      Nat.add_one_ne_zero, ite_false, add_tsub_cancel_right]
    congr 1
    apply List.ext_getElem <;> simp
  rw [hg, List.foldl_cons]
  have hst : estep (true :: List.ofFn x, true) (0, 0) = ((true :: List.ofFn x) ++ [false], false) := by
    simp [estep]
  rw [hst, foldl_estep_copy n (s - 1)]
  · have : s - 1 ≠ 0 := by omega
    simp [this]
  · simp
  · simp
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]; simp

end AdvancedEncryption.WE.CircuitSAT
