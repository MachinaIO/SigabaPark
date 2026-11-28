import SigabaNeoStd.Lattices.RingLWEInst
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic
namespace PrefixWalkGrant
open Cslib.Probability
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
abbrev Edges := (e : {p : V × V // G.Adj p.1 p.2}) → Bool
def grant (s t : V) (phase : Bool) (k : V → Bool) : Edges G × Bool :=
  (fun e ↦ k e.1.1 ^^ k e.1.2,phase ^^ (k s ^^ k t))
def onWalk {s t : V} (labels : Edges G) : G.Walk s t → Bool
  | .nil => false
  | .cons h p => labels ⟨(s,_),h⟩ ^^ onWalk labels p

theorem telescope {s t : V} (p : G.Walk s t) (k : V → Bool) :
    onWalk G (fun e ↦ k e.1.1 ^^ k e.1.2) p = (k s ^^ k t) := by
  induction p with
  | nil => simp [onWalk]
  | @cons a b c h p ih =>
    simp only [onWalk,ih]
    cases k a <;> cases k b <;> cases k c <;> decide

theorem opens {s t : V} (p : G.Walk s t) (k : V → Bool) (phase msg : Bool) :
    ((msg ^^ phase) ^^ ((grant G s t phase k).2 ^^ onWalk G (grant G s t phase k).1 p))=msg := by
  simp only [grant,telescope]; cases phase <;> cases msg <;> cases k s <;> cases k t <;> decide

def flip (cut : V → Bool) : (V → Bool) ≃ (V → Bool) where
  toFun k v := k v ^^ cut v
  invFun k v := k v ^^ cut v
  left_inv k := by funext v; change ((k v ^^ cut v) ^^ cut v)=k v; cases k v <;> cases cut v <;> decide
  right_inv k := by funext v; change ((k v ^^ cut v) ^^ cut v)=k v; cases k v <;> cases cut v <;> decide

noncomputable def law (s t : V) (phase : Bool) :=
  (Cslib.Probability.PMF.uniformOfFintype (V → Bool)).map (grant G s t phase)

theorem phase_blind (s t : V) (no : ¬G.Reachable s t) (phase : Bool) :
    law G s t phase=law G s t false := by
  classical
  cases phase with
  | false => rfl
  | true =>
    let cut := fun v ↦ decide (G.Reachable s v)
    have hs : cut s=true := by simp [cut]
    have ht : cut t=false := by simp [cut,no]
    have he (v w : V) (h : G.Adj v w) : cut v=cut w := by
      have eqv : G.Reachable s v ↔ G.Reachable s w :=
        ⟨fun a ↦ a.trans h.reachable,fun a ↦ a.trans h.reachable.symm⟩
      simp [cut,eqv]
    have hi := congrArg (PMF.map (grant G s t false))
      (Cslib.Probability.PMF.uniformOfFintype_map_equiv (flip cut))
    rw [PMF.map_comp] at hi
    refine Eq.trans ?_ hi
    apply congrArg (fun f ↦ (Cslib.Probability.PMF.uniformOfFintype (V → Bool)).map f)
    funext k; apply Prod.ext
    · funext e; change (k e.1.1 ^^ k e.1.2) = ((k e.1.1 ^^ cut e.1.1) ^^ (k e.1.2 ^^ cut e.1.2))
      rw [he _ _ e.property]; cases k e.1.1 <;> cases k e.1.2 <;> cases cut e.1.2 <;> decide
    · change (true ^^ (k s ^^ k t))=(false ^^ ((k s ^^ cut s) ^^ (k t ^^ cut t)))
      rw [hs,ht]; cases k s <;> cases k t <;> decide

/-- For every joint prefix/phase law the simulator sends a grant of zero, independent of the front. -/
theorem joint_sim {Ω H : Type} (μ : PMF Ω) (hdr : Ω → H) (key : Ω → Bool) (msg : Bool)
    (s t : V) (no : ¬G.Reachable s t) :
    μ.bind (fun ω ↦ (law G s t (key ω)).map fun u ↦ (hdr ω,msg ^^ key ω,u)) =
    μ.bind (fun ω ↦ (law G s t false).map fun u ↦ (hdr ω,msg ^^ key ω,u)) := by
  simp only [phase_blind G s t no]
end PrefixWalkGrant
