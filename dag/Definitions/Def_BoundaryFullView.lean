import SigabaNeoStd.Lattices.RingLWEInst
import Mathlib.Tactic

namespace BoundaryFullView
open Cslib.Probability
variable {R I V : Type} [CommRing R]

/-- One independent challenge row for an edge from a hidden source to
either another hidden key or a known contribution (including a terminal). -/
structure Plan (V I R : Type) where
  source : I → V
  hiddenTarget : I → Option V
  scale : I → R
  known : I → R

def delta (p : Plan V I R) (i : I) : R :=
  match p.hiddenTarget i with | none => 0 | some _ => p.scale i

def addend (p : Plan V I R) (k : V → R) (i : I) : R :=
  match p.hiddenTarget i with | none => p.known i | some v => p.scale i * k v

abbrev Bank (I R : Type) := (I → R) × (I → R)

def correction (p : Plan V I R) (t : V → R) (a : I → R) (i : I) :=
  a i*t (p.source i)+addend p t i

/-- A triangular permutation of all ideal header/body coins together. -/
def bankPerm (p : Plan V I R) (t : V → R) : Bank I R ≃ Bank I R where
  toFun x := (fun i ↦ x.1 i-delta p i,fun i ↦ x.2 i+correction p t (fun j ↦ x.1 j-delta p j) i)
  invFun x := (fun i ↦ x.1 i+delta p i,fun i ↦ x.2 i-correction p t x.1 i)
  left_inv := by intro x; ext <;> simp
  right_inv := by intro x; ext <;> simp

theorem ideal_joint [Fintype I] [DecidableEq I] [Fintype R] (p : Plan V I R) (t : V → R) :
    (PMF.uniformOfFintype (Bank I R)).map (bankPerm p t) = PMF.uniformOfFintype _ :=
  PMF.uniformOfFintype_map_equiv _

/-- The secret remains fixed in this equivalence. Independently translating
all keys and headers maps independent uniform shifts and challenge headers
to independent uniform issuer keys and issuer headers. -/
def realPerm (p : Plan V I R) (s : R) : ((V → R) × (I → R)) ≃ ((V → R) × (I → R)) where
  toFun x := (fun v ↦ s+x.1 v,fun i ↦ x.2 i-delta p i)
  invFun x := (fun v ↦ x.1 v-s,fun i ↦ x.2 i+delta p i)
  left_inv := by intro x; ext <;> simp
  right_inv := by intro x; ext <;> simp

def realRows (s : R) (e a : I → R) : Bank I R := (a,fun i ↦ a i*s+e i)
def issue (p : Plan V I R) (e : I → R) (x : (V → R) × (I → R)) : Bank I R :=
  (x.2,fun i ↦ x.2 i*x.1 (p.source i)+e i+addend p x.1 i)

theorem simulate_eq_issue (p : Plan V I R) (s : R) (e : I → R) (x : (V → R) × (I → R)) :
    bankPerm p x.1 (realRows s e x.2)=issue p e (realPerm p s x) := by
  apply Prod.ext
  · rfl
  · funext i
    simp only [bankPerm,realPerm,realRows,issue,Equiv.coe_fn_mk,correction]
    cases h : p.hiddenTarget i <;> simp [delta,addend,h] <;> ring

/-- Exact complete real row law conditioned on the secret, errors, and
all live and terminal randomness. The observation can append any fixed
live records, root keys and public metadata, or permute the row order. -/
theorem real_full [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Fintype R] {O : Type}
    (p : Plan V I R) (s : R) (e : I → R) (observe : Bank I R → O) :
    (PMF.uniformOfFintype ((V → R) × (I → R))).map
      (fun x ↦ observe (bankPerm p x.1 (realRows s e x.2))) =
    (PMF.uniformOfFintype ((V → R) × (I → R))).map (fun x ↦ observe (issue p e x)) := by
  simp_rw [simulate_eq_issue]
  have he := PMF.uniformOfFintype_map_equiv (realPerm p s)
  simpa only [PMF.map_comp,Function.comp_def] using
    congrArg (PMF.map (fun x ↦ observe (issue p e x))) he

theorem ideal_full [Fintype I] [DecidableEq I] [Fintype R] {O : Type}
    (p : Plan V I R) (t : V → R) (observe : Bank I R → O) :
    (PMF.uniformOfFintype (Bank I R)).map (fun x ↦ observe (bankPerm p t x)) =
    (PMF.uniformOfFintype (Bank I R)).map observe := by
  simpa only [PMF.map_comp,Function.comp_def] using congrArg (PMF.map observe) (ideal_joint p t)


section Integrate
variable [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Fintype R]
variable {O : Type}
noncomputable def transport (p : Plan V I R) (ob : Bank I R → O) (x : Bank I R) : PMF O :=
  (PMF.uniformOfFintype (V → R)).map (fun t ↦ ob (bankPerm p t x))

theorem integrate_fixed (p : Plan V I R) (s : R) (e : I → R) (ob : Bank I R → O) :
    (PMF.uniformOfFintype (I → R)).bind (fun a ↦ transport p ob (realRows s e a)) =
    (PMF.uniformOfFintype ((V → R) × (I → R))).map (fun x ↦ ob (issue p e x)) := by
  rw [← real_full p s e ob, ← PMF.uniformOfFintype_prod (V → R) (I → R), PMF.map_bind]
  simp only [PMF.map_comp,Function.comp_def,transport,PMF.map,PMF.bind_bind,PMF.pure_bind]
  exact PMF.bind_comm _ _ _

noncomputable def inputReal (S : PMF R) (E : PMF (I → R)) : PMF (Bank I R) :=
  S.bind fun s ↦ (PMF.uniformOfFintype (I → R)).bind fun a ↦ E.map fun e ↦ realRows s e a

noncomputable def issuedLaw (p : Plan V I R) (E : PMF (I → R)) (ob : Bank I R → O) : PMF O :=
  E.bind fun e ↦ (PMF.uniformOfFintype ((V → R) × (I → R))).map (fun x ↦ ob (issue p e x))

theorem integrate_real (p : Plan V I R) (S : PMF R) (E : PMF (I → R)) (ob : Bank I R → O) :
    (inputReal S E).bind (transport p ob)=issuedLaw p E ob := by
  simp only [inputReal,PMF.bind_bind,PMF.bind_map,Function.comp_def]
  trans S.bind (fun _ ↦ issuedLaw p E ob)
  · congr 1; funext s
    rw [PMF.bind_comm]
    unfold issuedLaw
    congr 1; funext e
    exact integrate_fixed p s e ob
  · exact PMF.bind_const _ _

theorem integrate_ideal (p : Plan V I R) (ob : Bank I R → O) :
    (PMF.uniformOfFintype (Bank I R)).bind (transport p ob)=
    (PMF.uniformOfFintype (Bank I R)).map ob := by
  change (PMF.uniformOfFintype (Bank I R)).bind (fun x ↦ (PMF.uniformOfFintype (V → R)).bind (fun t ↦ PMF.pure (ob (bankPerm p t x)))) = _
  rw [PMF.bind_comm]
  trans (PMF.uniformOfFintype (V → R)).bind (fun _ ↦ (PMF.uniformOfFintype (Bank I R)).map ob)
  · congr 1; funext t
    exact ideal_full p t ob
  · exact PMF.bind_const _ _
end Integrate

open SigabaNeo SigabaNeo.Lattices Cslib
abbrev params : RingLWE.Params := ⟨1024,548,16,.cbd 1,.uniform,by decide⟩
abbrev RR := Negacyclic (ZMod 16) 1024
abbrev Slots := Fin 548
noncomputable def errorRows : PMF (Slots → RR) :=
  PMF.pi fun _ : Slots ↦ polyOf (N:=1024) (ModuleLWE.coeffLaw 16 (.cbd 1))

section Words
variable [Fintype V] [DecidableEq V]
variable (p : Plan V Slots RR) (ob : Bank Slots RR → Bool)

theorem registered_real :
    (ModuleLWE.realLaw params.toModule).bind
      (wordDist (Equiv.refl Slots) (transport p ob))=issuedLaw p errorRows ob := by
  refine (realLaw_bind_wordDist params (Equiv.refl Slots) (transport p ob)).trans ?_
  have h := integrate_real p (polyOf (N:=1024) (ModuleLWE.coeffLaw 16 .uniform)) errorRows ob
  exact h

theorem registered_ideal :
    (ModuleLWE.idealLaw params.toModule).bind
      (wordDist (Equiv.refl Slots) (transport p ob))=
    (PMF.uniformOfFintype (Bank Slots RR)).map ob := by
  refine (idealLaw_bind_wordDist params (Equiv.refl Slots) (transport p ob)).trans ?_
  exact integrate_ideal p ob
end Words

end BoundaryFullView
