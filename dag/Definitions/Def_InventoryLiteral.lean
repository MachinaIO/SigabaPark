import Definitions.Def_InventoryCircuit
import SigabaNeoStd.Machines.FromPolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.Transducer
import Mathlib.Data.List.Infix
import Mathlib.Tactic
import Mathlib.Data.Nat.Size

set_option maxRecDepth 8192

namespace InventoryLiteral
open SigabaNeo Turing MultiTapeTM

abbrev S (pat : List Bool) := ↥pat.tails.toFinset
abbrev Q (pat : List Bool) := Option (S pat)

def advance (pat : List Bool) (q : Q pat) (x : Bool) : Q pat :=
  match q with
  | none => none
  | some ⟨[],_⟩ => none
  | some ⟨a::s,hs⟩ => if a=x then some ⟨s,by
      apply List.mem_toFinset.mpr
      apply (List.mem_tails ..).mpr
      exact (List.suffix_cons a s).trans ((List.mem_tails ..).mp (List.mem_toFinset.mp hs))⟩ else none

def scan (pat : List Bool) : Transducer Bool (Q pat) where
  q₀ := some ⟨pat,by simp [List.mem_tails]⟩
  step q x := (advance pat q x,[])
  final q := [decide (q.map Subtype.val = some [])]
  length_step_le _ _ := by simp
  length_final_le _ := by simp

theorem run_eq (p x : List Bool) (q : Q p) :
    (scan p).run q x = [decide (q.map Subtype.val = some x)] := by
  induction x generalizing q with
  | nil => rfl
  | cons b bs ih =>
    change (scan p).run (advance p q b) bs = _
    rw [ih]
    cases q with
    | none => rfl
    | some q =>
      obtain ⟨s,hs⟩ := q
      cases s with
      | nil => rfl
      | cons a s =>
        by_cases h : a=b <;> simp [advance,h]

noncomputable def machine (p : List Bool) (L : Nat) : Machine :=
  Machine.ofTM (scan p).toTM (2*L+3)

theorem machine_run (p x : List Bool) (L : Nat) (hx : x.length ≤ L) :
    (machine p L).run x = PMF.pure [decide (p=x)] := by
  rw [machine,Machine.run_ofTM]
  congr 1
  obtain ⟨⟨u,hu,ho⟩,ht,_⟩ := (scan p).computesInTimeAndSpace_toTM x
  have hh := runsInTime_iff_halted.mp ht
  rw [runFrom_eq_of_halt _ _ (show 2*x.length+3 ≤ 2*L+3 by omega) hh]
  have he : ((scan p).toTM.runFrom ((scan p).toTM.initCfg x) (2*x.length+3)).output =
      (scan p).run (scan p).q₀ x := by
    rcases le_total u (2*x.length+3) with h|h
    · rw [runFrom_eq_of_halt _ _ h hu]; exact ho
    · rw [← runFrom_eq_of_halt _ _ h hh]; exact ho
  rw [he,run_eq]
  simp [scan]

theorem machine_cost (p : List Bool) (L : Nat) (hp : p.length ≤ 2^27) (hl : L ≤ 2^27) :
    (machine p L).cost < 2^40 := by
  have hc : p.tails.toFinset.card ≤ p.length+1 := by
    simpa [List.length_tails] using List.toFinset_card_le p.tails
  have hs : (machine p L).states ≤ 6*(2^27+2) := by
    change Nat.card (Q p × Option Bool × Bool) ≤ _
    have hf : Fintype.card (S p) = p.tails.toFinset.card := Fintype.card_coe _
    simp only [Nat.card_eq_fintype_card,Q,Fintype.card_prod,Fintype.card_option,Fintype.card_bool,hf]
    omega
  have hn : Nat.size (machine p L).states ≤ 30 := by
    exact Nat.size_le.mpr (by omega)
  unfold Machine.cost Machine.descLen Machine.entryBits
  change 2*L+3 + 6*(machine p L).states*3^0*3^0*
    (4+4*0+4*0+Nat.size 0+Nat.size (machine p L).states) < _
  simp only [Nat.pow_zero,Nat.mul_one,Nat.mul_zero,Nat.add_zero,Nat.size_zero]
  nlinarith [Nat.mul_le_mul hs (show 4+Nat.size (machine p L).states ≤ 34 by omega)]


open AdvancedEncryption.WE.CircuitSAT

theorem encoded_bound {n s : Nat} (φ : Circuit n s) :
    (encCircuit n s φ).length ≤ s * (6 * (n+1+s) + 3) := by
  have hb (g : Nat × Nat) (hg : g ∈ φ.gates) : g.1 ≤ n+1+s ∧ g.2 ≤ n+1+s := by
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hg
    exact ⟨(φ j).1.isLt.le,(φ j).2.isLt.le⟩
  have h := length_encGates_le φ.gates hb
  have hl : φ.gates.length = s := List.length_ofFn
  rw [hl] at h
  exact h

theorem registered_length (φ : Circuit 128 4096) : (encCircuit 128 4096 φ).length ≤ 2^27 :=
  (encoded_bound φ).trans (by decide)

noncomputable def identifier := machine (encCircuit 128 4096 InventoryCircuit.fixture) (2^27)

theorem identify (φ : Circuit 128 4096) : identifier.run (encCircuit 128 4096 φ) =
    PMF.pure [decide (encCircuit 128 4096 InventoryCircuit.fixture = encCircuit 128 4096 φ)] :=
  machine_run _ _ _ (registered_length φ)

theorem identify_cost : identifier.cost < 2^40 := machine_cost _ _ (registered_length _) le_rfl

theorem identify_sound (φ : Circuit 128 4096) (h : identifier.run (encCircuit 128 4096 φ) =
    PMF.pure [true]) (x : Fin 128 → Bool) : ¬ Satisfies φ x := by
  rw [identify] at h
  by_cases he : InventoryCircuit.fixture = φ
  · rw [← he]; exact InventoryCircuit.fixture_unsatisfiable x
  · have hn : encCircuit 128 4096 InventoryCircuit.fixture ≠ encCircuit 128 4096 φ := fun e ↦ he ((encCircuit 128 4096).injective e)
    have hv := congrArg (fun μ : PMF (List Bool) ↦ μ [true]) h
    simp [hn,PMF.pure_apply] at hv

end InventoryLiteral
