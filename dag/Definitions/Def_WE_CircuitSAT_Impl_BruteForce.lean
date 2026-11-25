import Definitions.Def_WE_CircuitSAT
import SigabaNeoStd.Machines.FiniteAlg

/-!
# Brute-force witness encryption: an assumption-free baseline submission

A submission `u` for `AdvancedEncryption.WE.CircuitSAT.P` that needs no assumption. It is a
baseline, not a construction: its cost is astronomically large.

* `Enc(φ, β)` outputs `[β]` if the circuit `φ` is satisfiable and `[false]` otherwise (`ctOf`).
* `Dec(φ, w, ct)` outputs `ct` (on the ciphertexts `[b]` that `Enc` produces).

Correctness is exact, and for an unsatisfiable `φ` the encryptions of `0` and `1` are the same
word, so every adversary has advantage `0`. Both algorithms are deterministic.

The machines are obtained non-constructively from `Machine.exists_finiteAlg_det` (the valid
inputs form a finite set; the machine is in effect a hard-wired table), and the claimed cost `N`
is the cost of these machines itself, `WE.cost impl`: it is **not** an explicit number. Any
explicit bound would be at least that of deciding satisfiability by exhaustive search, about
`2^128 · 2^12` gate evaluations.
-/

namespace AdvancedEncryption.WE.CircuitSAT.BruteForce

open SigabaNeo

/-- The relation of the problem: NAND-circuit SAT with 128 inputs and `2^12` gates. -/
abbrev Rel : Relation := relation inputs size

/-- The input variables of `Enc` on `(φ, β)`: `(1^λ, 1^κ, desc)`, `φ`, `[β]`. -/
def encIn (a : Circuit inputs size × Bool) : List (List Bool) :=
  [paramsWord Rel params, encCircuit inputs size a.1, encBit a.2]

theorem encIn_injective : Function.Injective encIn := by
  rintro ⟨φ, β⟩ ⟨ψ, γ⟩ h
  simp only [encIn, List.cons.injEq, and_true, true_and] at h
  obtain ⟨h1, h2⟩ := h
  refine Prod.ext ((encCircuit inputs size).injective h1) ?_
  simpa [encBit] using h2

open Classical in
/-- The ciphertext of brute-force witness encryption: `[β]` if `φ` is satisfiable, `[false]`
otherwise. -/
noncomputable def ctOf (a : Circuit inputs size × Bool) : List Bool :=
  if Rel.InL a.1 then encBit a.2 else encBit false

/-- The input variables of `Dec` on `(φ, w, [b])`. -/
def decIn (a : Circuit inputs size × (Fin inputs → Bool) × Bool) : List (List Bool) :=
  [paramsWord Rel params, encCircuit inputs size a.1, encAssignment inputs a.2.1, encBit a.2.2]

theorem decIn_injective : Function.Injective decIn := by
  rintro ⟨φ, w, β⟩ ⟨ψ, v, γ⟩ h
  simp only [decIn, List.cons.injEq, and_true, true_and] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine Prod.ext ((encCircuit inputs size).injective h1)
    (Prod.ext ((encAssignment inputs).injective h2) ?_)
  simpa [encBit] using h3

theorem exists_encMachine : ∃ M : Machine, M.Deterministic ∧
    ∀ a, M.run (encodeTuple (encIn a)) = PMF.pure (encodeTuple [ctOf a]) :=
  Machine.exists_finiteAlg_det encIn encIn_injective ctOf

theorem exists_decMachine : ∃ M : Machine, M.Deterministic ∧
    ∀ a, M.run (encodeTuple (decIn a)) = PMF.pure (encodeTuple [encBit a.2.2]) :=
  Machine.exists_finiteAlg_det decIn decIn_injective fun a => encBit a.2.2

/-- `Enc`: a deterministic machine whose output word is the tuple `[ctOf (φ, β)]`. -/
noncomputable def encMachine : Machine := exists_encMachine.choose

/-- `Dec`: a deterministic machine whose output word is the tuple `[[b]]` on the ciphertext
`[b]`. -/
noncomputable def decMachine : Machine := exists_decMachine.choose

/-- The implementation: `Enc` is algorithm `0`, `Dec` algorithm `1`. -/
noncomputable def impl : Impl WE.sig where
  machine a := if a = Alg.enc then encMachine else decMachine
  deterministic a _ := by
    by_cases h : a = Alg.enc
    · simp only [h, ite_true]; exact exists_encMachine.choose_spec.1
    · simp only [h, ite_false]; exact exists_decMachine.choose_spec.1

/-- The brute-force submission: no premises, and `N` the cost of the implementation itself (not
an explicit number). -/
noncomputable def u : Submission P R where
  impl := impl
  deps _ := []
  N := WE.cost impl

end AdvancedEncryption.WE.CircuitSAT.BruteForce
