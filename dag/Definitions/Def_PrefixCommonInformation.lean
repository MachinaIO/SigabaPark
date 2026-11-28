import Mathlib.Analysis.SpecialFunctions.Log.Base
import CslibFrontier.Probability.Conditioning
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
/- Finite-law lemmas adapted from the pinned cslib-frontier Entropy,
Divergence, MutualInformation and MutualInformation/DataProcessing modules.
Copyright (c) 2026 Samuel Schlesinger and Christian Reitwiessner. Apache License 2.0. -/
namespace PrefixCommonInformation.FiniteLaw
open scoped ENNReal
open Cslib.Probability
open Cslib.Probability.PMF
variable {α β γ δ τ τ' Ω : Type*}

noncomputable def surprisal (p : PMF α) (a : α) : ℝ := -Real.logb 2 (p a).toReal

noncomputable def entropy [Finite α] (p : PMF α) : ℝ :=
  let := Fintype.ofFinite α
  (∑ a, Real.negMulLog (p a).toReal) / Real.log 2

theorem entropy_eq_sum [Fintype α] (p : PMF α) :
    entropy p = (∑ a, Real.negMulLog (p a).toReal) / Real.log 2 := by
  rw [entropy, Subsingleton.elim (Fintype.ofFinite α) ‹Fintype α›]

theorem entropy_eq_sum_surprisal [Fintype α] (p : PMF α) :
    entropy p = ∑ a, (p a).toReal * surprisal p a := by
  simp only [entropy_eq_sum, Finset.sum_div, Real.negMulLog, surprisal, Real.logb,
    neg_div, neg_mul, mul_neg, mul_div_assoc]

theorem entropy_pure [Finite α] (a : α) : entropy (PMF.pure a) = 0 := by
  classical
  simp [entropy, PMF.pure_apply, apply_ite]

theorem entropy_map_eq_sum [Fintype α] [Finite β] (p : PMF α) (f : α → β) :
    entropy (p.map f) = ∑ a, (p a).toReal * surprisal (p.map f) (f a) := by
  let := Fintype.ofFinite β
  rw [entropy_eq_sum_surprisal, sum_map_mul]

theorem entropy_map_le [Finite α] [Finite β] (p : PMF α) (f : α → β) :
    entropy (p.map f) ≤ entropy p := by
  classical
  let := Fintype.ofFinite α
  rw [entropy_map_eq_sum, entropy_eq_sum_surprisal]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : (p a).toReal = 0
  · simp [ha]
  have hmass := ENNReal.toReal_mono (PMF.apply_ne_top _ _) (le_map_apply p f a)
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  exact neg_le_neg (Real.logb_le_logb_of_le (by norm_num)
    (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm ha)) hmass)

theorem entropy_map_of_injOn [Finite α] [Finite β] (p : PMF α) {f : α → β}
    (hf : Set.InjOn f p.support) : entropy (p.map f) = entropy p := by
  classical
  let : Nonempty α := ⟨p.support_nonempty.choose⟩
  have hmap : (p.map f).map (Function.invFunOn f p.support) = p := by
    rw [PMF.map_comp]
    exact (map_congr_on_support p _ id (fun a ha => hf.leftInvOn_invFunOn ha)).trans
      (PMF.map_id p)
  exact le_antisymm (entropy_map_le p f)
    (by simpa only [hmap] using entropy_map_le (p.map f) (Function.invFunOn f p.support))

theorem entropy_map_of_injective [Finite α] [Finite β] (p : PMF α) {f : α → β}
    (hf : Function.Injective f) : entropy (p.map f) = entropy p :=
  entropy_map_of_injOn p hf.injOn

theorem sum_mul_entropy_le_entropy_bind [Fintype α] [Finite β]
    (p : PMF α) (kernel : α → PMF β) :
    (∑ a, (p a).toReal * entropy (kernel a)) ≤ entropy (p.bind kernel) := by
  let := Fintype.ofFinite β
  simp only [entropy_eq_sum, ← mul_div_assoc, ← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num))
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro b _
  have h := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
    (w := fun a => (p a).toReal) (p := fun a => (kernel a b).toReal)
    (fun _ _ => ENNReal.toReal_nonneg) (sum_toReal p) (fun _ _ => ENNReal.toReal_nonneg)
  simpa only [smul_eq_mul, bind_apply_toReal] using h

theorem entropy_bind_pair [Fintype α] [Finite β] (p : PMF α) (kernel : α → PMF β) :
    entropy (p.bind (fun a => (kernel a).map (a, ·))) =
      entropy p + ∑ a, (p a).toReal * entropy (kernel a) := by
  let := Fintype.ofFinite β
  simp only [entropy_eq_sum, Fintype.sum_prod_type, bind_map_prodMk_apply,
    ENNReal.toReal_mul, Real.negMulLog_mul, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, sum_toReal, one_mul, add_div, Finset.sum_div,
    mul_div_assoc]

noncomputable def conditionalEntropy [Finite α] [Finite β] (joint : PMF (α × β)) : ℝ :=
  entropy joint - entropy (joint.map Prod.fst)

theorem conditionalEntropy_map_const [Finite α] [Finite β] (p : PMF β) (a : α) :
    conditionalEntropy (p.map (a, ·)) = entropy p := by
  rw [conditionalEntropy, entropy_map_of_injective p (Prod.mk_right_injective a), PMF.map_comp]
  change entropy p - entropy (p.map (Function.const β a)) = entropy p
  rw [PMF.map_const, entropy_pure, sub_zero]

theorem conditionalEntropy_bind_pair [Fintype α] [Finite β]
    (p : PMF α) (kernel : α → PMF β) :
    conditionalEntropy (p.bind (fun a => (kernel a).map (a, ·))) =
      ∑ a, (p a).toReal * entropy (kernel a) := by
  simp [conditionalEntropy, entropy_bind_pair]

theorem conditionalEntropy_eq_sum [Fintype α] [Finite β] (joint : PMF (α × β)) :
    conditionalEntropy joint =
      ∑ a, ((joint.map Prod.fst) a).toReal * entropy (conditionalSnd joint a) := by
  simpa only [bind_conditionalSnd] using
    conditionalEntropy_bind_pair (joint.map Prod.fst) (conditionalSnd joint)

theorem conditionalEntropy_observe_ge [Fintype α] [Finite β] [Finite γ]
    (p : PMF α) (kernel : α → PMF β) (observe : α → γ) :
    (∑ a, (p a).toReal * entropy (kernel a)) ≤
      conditionalEntropy (p.bind (fun a => (kernel a).map (observe a, ·))) := by
  let := Fintype.ofFinite γ
  let conditional := conditionalSnd (p.map (fun a => (observe a, a)))
  have hreplay : (p.map observe).bind (fun c => ((conditional c).bind kernel).map (c, ·)) =
      p.bind (fun a => (kernel a).map (observe a, ·)) := by
    have h := congrArg (fun joint : PMF (γ × α) =>
      joint.bind (fun pair => (kernel pair.2).map (pair.1, ·)))
        (bind_conditionalSnd (p.map (fun a => (observe a, a))))
    simpa only [PMF.map_comp, Function.comp_def, PMF.map_bind, PMF.bind_bind, PMF.bind_map]
      using h
  calc
    _ = ∑ c, ((p.map observe) c).toReal *
        ∑ a, (conditional c a).toReal * entropy (kernel a) := by
      rw [sum_map_mul]
      exact (sum_conditionalSnd_map p observe (fun _ a => entropy (kernel a))).symm
    _ ≤ ∑ c, ((p.map observe) c).toReal * entropy ((conditional c).bind kernel) :=
      Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left
        (sum_mul_entropy_le_entropy_bind (conditional c) kernel) ENNReal.toReal_nonneg)
    _ = _ := by rw [← hreplay, conditionalEntropy_bind_pair]

theorem conditionalEntropy_map_fst_ge [Finite α] [Finite β] [Finite γ]
    (joint : PMF (α × β)) (observe : α → γ) :
    conditionalEntropy joint ≤
      conditionalEntropy (joint.map (fun pair => (observe pair.1, pair.2))) := by
  let := Fintype.ofFinite α
  have h := conditionalEntropy_observe_ge (joint.map Prod.fst) (conditionalSnd joint) observe
  have hlaw := congrArg (PMF.map (fun pair : α × β => (observe pair.1, pair.2)))
    (bind_conditionalSnd joint)
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at hlaw
  simpa only [hlaw, ← conditionalEntropy_eq_sum] using h

theorem conditionalEntropy_le_entropy_map_snd [Finite α] [Finite β] (joint : PMF (α × β)) :
    conditionalEntropy joint ≤ entropy (joint.map Prod.snd) := by
  have h := conditionalEntropy_map_fst_ge joint (fun _ => ())
  rwa [show joint.map (fun pair => ((), pair.2)) = (joint.map Prod.snd).map ((), ·) by
    rw [PMF.map_comp]; rfl, conditionalEntropy_map_const] at h

theorem entropy_le_entropy_map_fst_add_entropy_map_snd [Finite α] [Finite β] (joint : PMF (α × β)) :
    entropy joint ≤ entropy (joint.map Prod.fst) + entropy (joint.map Prod.snd) := by
  have h := conditionalEntropy_le_entropy_map_snd joint
  rw [conditionalEntropy] at h
  linarith

noncomputable def mutualInfo [Finite α] [Finite β] (joint : PMF (α × β)) : ℝ :=
  entropy (joint.map Prod.fst) + entropy (joint.map Prod.snd) - entropy joint

noncomputable def condMutualInfo [Finite γ] [Finite α] [Finite β] (joint : PMF (γ × α × β)) : ℝ :=
  entropy (joint.map (Prod.map id Prod.fst)) + entropy (joint.map (Prod.map id Prod.snd)) -
    entropy joint - entropy (joint.map Prod.fst)

theorem mutualInfo_nonneg [Finite α] [Finite β] (joint : PMF (α × β)) :
    0 ≤ mutualInfo joint := by
  have := entropy_le_entropy_map_fst_add_entropy_map_snd joint
  rw [mutualInfo]
  linarith

theorem mutualInfo_le_entropy_map_snd [Finite α] [Finite β] (joint : PMF (α × β)) :
    mutualInfo joint ≤ entropy (joint.map Prod.snd) := by
  have := entropy_map_le joint Prod.fst
  rw [mutualInfo]
  linarith

theorem entropy_map_eq_of_comp [Finite α] [Finite β] (ν : PMF Ω) {F : Ω → α} {G : Ω → β}
    {e : α → β} (he : Function.Injective e) (h : ∀ ω ∈ ν.support, G ω = e (F ω)) :
    entropy (ν.map G) = entropy (ν.map F) := by
  rw [map_congr_on_support ν G (e ∘ F) h, ← PMF.map_comp]
  exact entropy_map_of_injective _ he

theorem mutualInfo_map [Finite α] [Finite β] (ν : PMF Ω) (A : Ω → α) (B : Ω → β) :
    mutualInfo (ν.map fun ω => (A ω, B ω)) =
      entropy (ν.map A) + entropy (ν.map B) - entropy (ν.map fun ω => (A ω, B ω)) := by
  simp only [mutualInfo, PMF.map_comp]
  rfl

theorem condMutualInfo_map [Finite γ] [Finite α] [Finite β] (ν : PMF Ω) (C : Ω → γ)
    (A : Ω → α) (B : Ω → β) :
    condMutualInfo (ν.map fun ω => (C ω, A ω, B ω)) =
      entropy (ν.map fun ω => (C ω, A ω)) + entropy (ν.map fun ω => (C ω, B ω)) -
        entropy (ν.map fun ω => (C ω, A ω, B ω)) - entropy (ν.map C) := by
  simp only [condMutualInfo, PMF.map_comp]
  rfl

theorem condMutualInfo_nonneg [Finite γ] [Finite α] [Finite β] (joint : PMF (γ × α × β)) :
    0 ≤ condMutualInfo joint := by
  have h := conditionalEntropy_map_fst_ge
    (joint.map (fun t => ((t.1, t.2.1), t.2.2))) Prod.fst
  have e1 : entropy (joint.map fun t => ((t.1, t.2.1), t.2.2)) = entropy joint :=
    entropy_map_of_injective joint (fun s t h => by
      obtain ⟨c, a, b⟩ := s
      obtain ⟨c', a', b'⟩ := t
      simp only [Prod.mk.injEq] at h
      simp [h])
  simp only [conditionalEntropy, PMF.map_comp, Function.comp_def, e1] at h
  change 0 ≤ entropy (joint.map fun x => (x.1, x.2.1)) + entropy (joint.map fun x => (x.1, x.2.2)) -
    entropy joint - entropy (joint.map fun x => x.1)
  linarith

theorem mutualInfo_map_prodMk_eq_add [Finite γ] [Finite α] [Finite β] (ν : PMF Ω)
    (C : Ω → γ) (A : Ω → α) (B : Ω → β) :
    mutualInfo (ν.map fun ω => ((C ω, A ω), B ω)) =
      mutualInfo (ν.map fun ω => (C ω, B ω)) +
        condMutualInfo (ν.map fun ω => (C ω, A ω, B ω)) := by
  rw [mutualInfo_map, mutualInfo_map, condMutualInfo_map,
    entropy_map_eq_of_comp ν (F := fun ω => (C ω, A ω, B ω))
      (e := fun t => ((t.1, t.2.1), t.2.2))
      (fun s t hst => by
        obtain ⟨c, a, b⟩ := s
        obtain ⟨c', a', b'⟩ := t
        simp only [Prod.mk.injEq] at hst
        simp [hst])
      (fun _ _ => rfl)]
  ring

theorem condMutualInfo_map_swap [Finite γ] [Finite α] [Finite β]
    (ν : PMF Ω) (C : Ω → γ) (A : Ω → α) (B : Ω → β) :
    condMutualInfo (ν.map fun ω => (C ω, A ω, B ω)) =
      condMutualInfo (ν.map fun ω => (C ω, B ω, A ω)) := by
  rw [condMutualInfo_map, condMutualInfo_map,
    entropy_map_eq_of_comp ν (F := fun ω => (C ω, A ω, B ω))
      (G := fun ω => (C ω, B ω, A ω)) (e := Prod.map id Prod.swap)
      (Function.injective_id.prodMap Prod.swap_injective) (fun _ _ => rfl)]
  ring

theorem condMutualInfo_map_prodMk_left_eq_add [Finite γ] [Finite δ] [Finite α] [Finite β]
    (ν : PMF Ω) (C : Ω → γ) (D : Ω → δ) (A : Ω → α) (B : Ω → β) :
    condMutualInfo (ν.map fun ω => (C ω, (D ω, A ω), B ω)) =
      condMutualInfo (ν.map fun ω => (C ω, D ω, B ω)) +
        condMutualInfo (ν.map fun ω => ((C ω, D ω), A ω, B ω)) := by
  let e1 : (γ × δ) × α ≃ γ × δ × α := Equiv.prodAssoc γ δ α
  let e2 : (γ × δ) × β ≃ γ × δ × β := Equiv.prodAssoc γ δ β
  let e3 : (γ × δ) × (α × β) ≃ γ × (δ × α) × β :=
    (Equiv.prodAssoc (γ × δ) α β).symm.trans
      (((Equiv.prodAssoc γ δ α).prodCongr (Equiv.refl β)).trans
        (Equiv.prodAssoc γ (δ × α) β))
  rw [condMutualInfo_map, condMutualInfo_map, condMutualInfo_map,
    entropy_map_eq_of_comp ν (F := fun ω => ((C ω, D ω), A ω))
      (G := fun ω => (C ω, D ω, A ω)) (e := e1) e1.injective (fun _ _ => rfl),
    entropy_map_eq_of_comp ν (F := fun ω => ((C ω, D ω), B ω))
      (G := fun ω => (C ω, D ω, B ω)) (e := e2) e2.injective (fun _ _ => rfl),
    entropy_map_eq_of_comp ν (F := fun ω => ((C ω, D ω), A ω, B ω))
      (G := fun ω => (C ω, (D ω, A ω), B ω)) (e := e3) e3.injective (fun _ _ => rfl)]
  ring

theorem condMutualInfo_map_prodMk_right_eq_add [Finite γ] [Finite α] [Finite δ] [Finite β]
    (ν : PMF Ω) (C : Ω → γ) (A : Ω → α) (D : Ω → δ) (B : Ω → β) :
    condMutualInfo (ν.map fun ω => (C ω, A ω, (D ω, B ω))) =
      condMutualInfo (ν.map fun ω => (C ω, A ω, D ω)) +
        condMutualInfo (ν.map fun ω => ((C ω, D ω), A ω, B ω)) := by
  rw [condMutualInfo_map_swap ν C A (fun ω => (D ω, B ω)),
    condMutualInfo_map_prodMk_left_eq_add ν C D B A,
    condMutualInfo_map_swap ν C D A,
    condMutualInfo_map_swap ν (fun ω => (C ω, D ω)) B A]

theorem condMutualInfo_map_le_of_comp_left {α' : Type*}
    [Finite γ] [Finite α] [Finite α'] [Finite β]
    (ν : PMF Ω) (C : Ω → γ) (A : Ω → α) (S : Ω → α') (B : Ω → β)
    (f : α → α') (hf : ∀ ω ∈ ν.support, S ω = f (A ω)) :
    condMutualInfo (ν.map fun ω => (C ω, S ω, B ω)) ≤
      condMutualInfo (ν.map fun ω => (C ω, A ω, B ω)) := by
  have hinj : Function.Injective (fun a : α => (f a, a)) := fun _ _ h => congrArg Prod.snd h
  have h1 : condMutualInfo (ν.map fun ω => (C ω, A ω, B ω)) =
      condMutualInfo (ν.map fun ω => (C ω, (S ω, A ω), B ω)) := by
    rw [condMutualInfo_map, condMutualInfo_map,
      entropy_map_eq_of_comp ν (F := fun ω => (C ω, A ω)) (G := fun ω => (C ω, (S ω, A ω)))
        (e := Prod.map id fun a => (f a, a)) (Function.injective_id.prodMap hinj)
        (fun ω hω => Prod.ext rfl (Prod.ext (hf ω hω) rfl)),
      entropy_map_eq_of_comp ν (F := fun ω => (C ω, A ω, B ω))
        (G := fun ω => (C ω, (S ω, A ω), B ω))
        (e := Prod.map id (Prod.map (fun a => (f a, a)) id))
        (Function.injective_id.prodMap (hinj.prodMap Function.injective_id))
        (fun ω hω => Prod.ext rfl (Prod.ext (Prod.ext (hf ω hω) rfl) rfl))]
  rw [h1, condMutualInfo_map_prodMk_left_eq_add]
  have := condMutualInfo_nonneg (ν.map fun ω => ((C ω, S ω), A ω, B ω))
  linarith

theorem condMutualInfo_map_le_of_comp {α' β' : Type*}
    [Finite γ] [Finite α] [Finite α'] [Finite β] [Finite β']
    (ν : PMF Ω) (C : Ω → γ) (A : Ω → α) (S : Ω → α') (B : Ω → β) (R : Ω → β')
    (f : α → α') (hf : ∀ ω ∈ ν.support, S ω = f (A ω))
    (g : β → β') (hg : ∀ ω ∈ ν.support, R ω = g (B ω)) :
    condMutualInfo (ν.map fun ω => (C ω, S ω, R ω)) ≤
      condMutualInfo (ν.map fun ω => (C ω, A ω, B ω)) := by
  calc condMutualInfo (ν.map fun ω => (C ω, S ω, R ω))
      ≤ condMutualInfo (ν.map fun ω => (C ω, A ω, R ω)) :=
        condMutualInfo_map_le_of_comp_left ν C A S R f hf
    _ = condMutualInfo (ν.map fun ω => (C ω, R ω, A ω)) :=
        condMutualInfo_map_swap ν C A R
    _ ≤ condMutualInfo (ν.map fun ω => (C ω, B ω, A ω)) :=
        condMutualInfo_map_le_of_comp_left ν C B R A g hg
    _ = condMutualInfo (ν.map fun ω => (C ω, A ω, B ω)) :=
        condMutualInfo_map_swap ν C B A

end PrefixCommonInformation.FiniteLaw

namespace PrefixCommonInformation
open FiniteLaw
open Cslib.Probability
open Cslib.Probability.PMF
variable {Ω P T Y J V A : Type} [Finite P] [Finite T] [Finite Y] [Finite J] [Finite V]

/-- A noisy sample and the key, with a public helper, give exactly the same reconciled value. -/
theorem one (μ : PMF Ω) (p : Ω → P) (s : Ω → T) (y : Ω → Y)
    (j : Y → J) (v : Y → V) (openKey : P → T → J → V)
    (h : ∀ ω ∈ μ.support,v (y ω)=openKey (p ω) (s ω) (j (y ω))) :
    conditionalEntropy (μ.map fun ω ↦ ((p ω,j (y ω)),v (y ω))) ≤
      condMutualInfo (μ.map fun ω ↦ (p ω,s ω,y ω)) := by
  let c := fun ω ↦ (p ω,j (y ω))
  let z := fun ω ↦ v (y ω)
  have determined : entropy (μ.map fun ω ↦ (c ω,s ω,z ω)) =
      entropy (μ.map fun ω ↦ (c ω,s ω)) := by
    apply entropy_map_eq_of_comp μ (e:=fun a : (P × J) × T ↦
      (a.1,a.2,openKey a.1.1 a.2 a.1.2))
    · intro x y he; exact Prod.ext (congrArg (fun a : (P × J) × T × V ↦ a.1) he) (congrArg (fun a : (P × J) × T × V ↦ a.2.1) he)
    · intro ω hω; exact Prod.ext rfl (Prod.ext rfl (h ω hω))
  have bound := condMutualInfo_map_le_of_comp μ p s s y (fun ω ↦ (j (y ω),v (y ω)))
    id (fun _ _ ↦ rfl) (fun x ↦ (j x,v x)) (fun _ _ ↦ rfl)
  rw [condMutualInfo_map_prodMk_right_eq_add μ p s (fun ω ↦ j (y ω)) z] at bound
  have pos := condMutualInfo_nonneg (μ.map fun ω ↦ (p ω,s ω,j (y ω)))
  have eq : condMutualInfo (μ.map fun ω ↦ (c ω,s ω,z ω)) =
      conditionalEntropy (μ.map fun ω ↦ (c ω,z ω)) := by
    rw [condMutualInfo_map,determined,conditionalEntropy,PMF.map_comp]; change _ = _ - entropy (μ.map c)
    ring
  change conditionalEntropy (μ.map fun ω ↦ (c ω,z ω)) ≤ _
  rw [← eq]
  linarith

/-- Fixed-length histories in reverse chronological order. -/
def History (A Y : Type) (n : Nat) := A × (Fin n → Y)

def extend {n : Nat} (a : History A Y n) (y : Y) : History A Y (n+1) :=
  (a.1,Fin.cons y a.2)

theorem extend_inj {n : Nat} : Function.Injective
    (fun (p : History A Y n × Y) ↦ extend p.1 p.2) := by
  rintro ⟨⟨a,l⟩,v⟩ ⟨⟨b,k⟩,w⟩ h
  have h₁ : a=b := congrArg Prod.fst h
  have h₂ : v=w := congrArg (fun s ↦ s.2 0) h
  have h₃ : l=k := funext fun i ↦ congrArg (fun s ↦ s.2 i.succ) h
  cases h₁; cases h₂; cases h₃; rfl

def historyAt (a : Ω → A) (ys : Nat → Ω → Y) : (n : Nat) → Ω → History A Y n
  | 0,ω => (a ω,Fin.elim0)
  | n+1,ω => extend (historyAt a ys n ω) (ys n ω)

instance [Finite A] {n : Nat} : Finite (History A Y n) := inferInstanceAs (Finite (A × (Fin n → Y)))

theorem total [Finite A] (μ : PMF Ω) (a : Ω → A) (s : Ω → T) (ys : Nat → Ω → Y)
    (j : Y → J) (v : Y → V) (op : (i : Nat) → History A Y i → T → J → V)
    (h : ∀ i ω,ω∈μ.support → v (ys i ω)=op i (historyAt a ys i ω) (s ω) (j (ys i ω)))
    (n : Nat) :
    (∑ i ∈ Finset.range n,conditionalEntropy (μ.map fun ω ↦
      ((historyAt a ys i ω,j (ys i ω)),v (ys i ω)))) ≤ entropy (μ.map s) := by
  let info := fun i ↦ mutualInfo (μ.map fun ω ↦ (historyAt a ys i ω,s ω))
  have aux (i : Nat) :
      (∑ k ∈ Finset.range i,conditionalEntropy (μ.map fun ω ↦
        ((historyAt a ys k ω,j (ys k ω)),v (ys k ω)))) ≤ info i := by
    induction i with
    | zero => simpa [info] using mutualInfo_nonneg (μ.map fun ω ↦ (historyAt a ys 0 ω,s ω))
    | succ i ih =>
      have step := one μ (historyAt a ys i) s (ys i) j v (op i) (h i)
      have chain := mutualInfo_map_prodMk_eq_add μ (historyAt a ys i) (ys i) s
      rw [condMutualInfo_map_swap μ (historyAt a ys i) (ys i) s] at chain
      have e : info (i+1)=mutualInfo (μ.map fun ω ↦ ((historyAt a ys i ω,ys i ω),s ω)) := by
        change mutualInfo _ = _
        rw [mutualInfo_map, mutualInfo_map]
        have hi := extend_inj (A:=A) (Y:=Y) (n:=i)
        have h₁ := entropy_map_eq_of_comp μ hi (F:=fun ω ↦ (historyAt a ys i ω,ys i ω))
          (G:=historyAt a ys (i+1)) (fun _ _ ↦ rfl)
        have h₂ := entropy_map_eq_of_comp μ (hi.prodMap Function.injective_id)
          (F:=fun ω ↦ ((historyAt a ys i ω,ys i ω),s ω))
          (G:=fun ω ↦ (historyAt a ys (i+1) ω,s ω)) (fun _ _ ↦ rfl)
        rw [h₁,h₂]
      rw [Finset.sum_range_succ,e,chain]
      exact add_le_add ih step
  have hcap := mutualInfo_le_entropy_map_snd (μ.map fun ω ↦ (historyAt a ys n ω,s ω))
  simpa only [PMF.map_comp,Function.comp_def] using (aux n).trans hcap
/-- Convert average posterior Shannon entropy directly to average independent agreement. -/
theorem exponential_mean {I : Type} [Fintype I] (p : PMF I) (x : I → ℝ) :
    (2:ℝ)^(-(∑ i,(p i).toReal*x i)) ≤ ∑ i,(p i).toReal*(2:ℝ)^(-x i) := by
  have hj := (convexOn_rpow_left (b:=(2:ℝ)) (by norm_num)).map_sum_le (t:=Finset.univ)
    (w:=fun i ↦ (p i).toReal) (p:=fun i ↦ -x i)
    (fun _ _ ↦ ENNReal.toReal_nonneg) (sum_toReal p) (fun _ _ ↦ Set.mem_univ _)
  simpa only [smul_eq_mul,mul_neg,Finset.sum_neg_distrib] using hj

theorem collision {I : Type} [Fintype I] (p : PMF I) :
    (2:ℝ)^(-entropy p) ≤ ∑ i,(p i).toReal^2 := by
  rw [entropy_eq_sum_surprisal]
  refine (exponential_mean p (surprisal p)).trans_eq ?_
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : (p i).toReal=0
  · simp [h]
  · have hp := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm h)
    simp only [surprisal,neg_neg,Real.rpow_logb (by norm_num : (0:ℝ)<2)
      (by norm_num : (2:ℝ)≠1) hp,pow_two]

theorem posterior {I Z : Type} [Fintype I] [Fintype Z] (μ : PMF (I × Z)) :
    (2:ℝ)^(-conditionalEntropy μ) ≤
      ∑ i,((μ.map Prod.fst) i).toReal * ∑ z,(conditionalSnd μ i z).toReal^2 := by
  rw [conditionalEntropy_eq_sum]
  refine (exponential_mean (μ.map Prod.fst) (fun i ↦ entropy (conditionalSnd μ i))).trans ?_
  exact Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left
    (collision (conditionalSnd μ i)) ENNReal.toReal_nonneg
end PrefixCommonInformation
