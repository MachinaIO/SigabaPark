import SigabaNeoStd.Machines.FromPolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.Transducer
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic

namespace MixedOrderMaskMachine
open SigabaNeo Turing MultiTapeTM

abbrev Q := Bool × Option Bool

/-- The first register remembers whether a collision has occurred, the second an unfinished pair. -/
def scanner : Transducer Bool Q where
  q₀ := (false,none)
  step q x := match q.2 with
    | none => ((q.1,some x),[])
    | some y => ((q.1 || (x && y),none),[x || y])
  final q := [!q.1]
  length_step_le q _ := by cases q.2 <;> simp
  length_final_le _ := by simp

def interleave (l : List (Bool × Bool)) := l.flatMap (fun p ↦ [p.1,p.2])

theorem scan_pairs (l : List (Bool × Bool)) (seen : Bool) :
    scanner.run (seen,none) (interleave l) =
    l.map (fun p ↦ p.1 || p.2) ++ [!(seen || l.any (fun p ↦ p.1 && p.2))] := by
  induction l generalizing seen with
  | nil => cases seen <;> rfl
  | cons pr l ih =>
    obtain ⟨a,b⟩ := pr
    cases a <;> cases b <;> cases seen <;>
      simp [interleave,Transducer.run_cons,scanner,List.flatMap_cons,interleave] at ih ⊢ <;>
      simp_all

noncomputable def machine (n : Nat) : Machine := Machine.ofTM scanner.toTM (4*n+3)

theorem machine_run (l : List (Bool × Bool)) :
    (machine l.length).run (interleave l) = PMF.pure
      (l.map (fun p ↦ p.1 || p.2) ++ [!(l.any (fun p ↦ p.1 && p.2))]) := by
  rw [machine,Machine.run_ofTM]
  congr 1
  let w := interleave l
  have hlen : w.length = 2*l.length := by
    change (interleave l).length = _
    induction l with
    | nil => rfl
    | cons z l ih => simp [interleave] at ih ⊢; omega
  obtain ⟨⟨u,hu,hout⟩,htime,_⟩ := scanner.computesInTimeAndSpace_toTM w
  have hh := runsInTime_iff_halted.mp htime
  rw [show 4*l.length+3 = 2*w.length+3 by omega]
  have hrun : (scanner.toTM.runFrom (scanner.toTM.initCfg w) (2*w.length+3)).output =
      scanner.run scanner.q₀ w := by
    rcases le_total u (2*w.length+3) with le|le
    · rw [runFrom_eq_of_halt _ _ le hu]; exact hout
    · rw [← runFrom_eq_of_halt _ _ le hh]; exact hout
  exact hrun.trans (by change scanner.run (false,none) (interleave l) = _; simpa using scan_pairs l false)

theorem machine_cost (n : Nat) : (machine n).cost = 4*n+2163 := by
  have hs : (machine n).states = 36 := by
    change Nat.card (Q × Option Bool × Bool) = _
    simp [Q,Nat.card_eq_fintype_card,Fintype.card_option]
  unfold Machine.cost Machine.descLen Machine.entryBits
  rw [hs]
  change 4*n+3 + 6*36*3^0*3^0*(4+4*0+4*0+Nat.size 0+Nat.size 36) = _
  rw [show Nat.size 36 = 6 by decide, show Nat.size 0 = 0 by decide]
  omega

theorem cost124 : (machine 124).cost = 2659 := by rw [machine_cost]


def pairs {n : Nat} (s t : Finset (Fin n)) :=
  (List.finRange n).map (fun i ↦ (decide (i ∈ s),decide (i ∈ t)))

theorem run_finsets {n : Nat} (s t : Finset (Fin n)) :
    (machine n).run (interleave (pairs s t)) = PMF.pure
      ((List.finRange n).map (fun i ↦ decide (i ∈ s ∪ t)) ++ [decide (Disjoint s t)]) := by
  have hl : (pairs s t).length = n := by simp [pairs]
  have h := machine_run (pairs s t)
  rw [hl] at h
  rw [h]
  congr 1
  have hmeet : (!(pairs s t).any (fun p ↦ p.1 && p.2)) = decide (Disjoint s t) := by
    apply Bool.eq_iff_iff.mpr
    simp [pairs,List.any_map,List.any_eq_true,Function.comp_def,Finset.disjoint_left]
  rw [hmeet]
  simp [pairs,List.map_map,Function.comp_def]

end MixedOrderMaskMachine
