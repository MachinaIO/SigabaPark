import SigabaNeoStd.Machines.Gates
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic

noncomputable section
namespace NANDCanonicalBank
open SigabaNeo
abbrev F := ZMod 2
abbrev Mon := Finset Nat
abbrev Poly := Mon →₀ F
def bit (b : Bool) : F := if b then 1 else 0
def var (i : Nat) : Mon := if i=0 then ∅ else {i}
def mv (u : Nat → Bool) (m : Mon) : F := if ∀ j ∈ m, u j=true then 1 else 0
noncomputable def eval (u : Nat → Bool) : Poly →ₗ[F] F := Finsupp.linearCombination F (mv u)
def term (m : Mon) : Poly := Finsupp.single m 1
def one : Poly := term ∅
theorem eval_term (u : Nat → Bool) (m : Mon) : eval u (term m) = mv u m := by simp [term,eval]
theorem mv_empty (u : Nat → Bool) : mv u ∅ = 1 := by simp [mv]
theorem mv_var (u : Nat → Bool) (hu : u 0=true) (i : Nat) : mv u (var i)=bit (u i) := by
  by_cases h : i=0 <;> simp [var,h,mv,bit,hu]
theorem mv_union (u : Nat → Bool) (m n : Mon) : mv u (m ∪ n) = mv u m * mv u n := by
  have he : (∀ j ∈ m ∪ n, u j=true) ↔ (∀ j ∈ m, u j=true) ∧ (∀ j ∈ n, u j=true) := by
    constructor
    · intro h; exact ⟨fun j hj ↦ h j (Finset.mem_union_left _ hj),fun j hj ↦ h j (Finset.mem_union_right _ hj)⟩
    · intro h j hj; exact (Finset.mem_union.mp hj).elim (h.1 j) (h.2 j)
  unfold mv
  split_ifs <;> first | decide | rfl | exfalso; tauto

/-- Square-free canonical multiplication of one NAND constraint by a public monomial. -/
def gated (m : Mon) (a b z : Nat) : Poly :=
  term m + term (m ∪ var z) + term (m ∪ (var a ∪ var b))

theorem gated_eval (u : Nat → Bool) (hu : u 0=true) (m : Mon) (a b z : Nat) :
    eval u (gated m a b z) = mv u m * (1+bit (u z)+bit (u a)*bit (u b)) := by
  simp only [gated,map_add,eval_term,mv_union,mv_var _ hu]; ring

def normWire (n i : Nat) := if i<n then i else 0
def library (n last : Nat) : GateList → List Poly
 | [] => [one + term (var last)]
 | (i,j)::gs =>
   let a := normWire n i
   let b := normWire n j
   ([∅,var a,var b,var n] : List Mon).map (fun m ↦ gated m a b n) ++ library (n+1) n gs

theorem library_length (gs : GateList) (n last : Nat) :
    (library n last gs).length = 4*gs.length+1 := by
  induction gs generalizing n last with
  | nil => rfl
  | cons g gs ih => rcases g with ⟨a,b⟩; simp [library,ih]; omega

theorem read_before (s : List Bool × Bool) (gs : GateList) (i : Nat) (hi : i<s.1.length) :
    (gs.foldl estep s).1.getD i true = s.1.getD i true := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,ih (estep s g) (by simp [estep]; omega)]
    simp only [estep,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]

theorem len_run (s : List Bool × Bool) (gs : GateList) :
    (gs.foldl estep s).1.length=s.1.length+gs.length := by
  induction gs generalizing s with
  | nil => simp
  | cons g gs ih => simp [ih,estep,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]

theorem nand_zero : ∀ a b : Bool, (1:F)+bit (!(a && b))+bit a*bit b=0 := by decide

theorem library_zero (u : Nat → Bool) (hu : u 0=true) (s : List Bool × Bool)
    (last : Nat) (gs : GateList) (hl : u last=s.2) (yes : (gs.foldl estep s).2=true)
    (ht : ∀ i < (gs.foldl estep s).1.length, u i = (gs.foldl estep s).1.getD i true) :
    ∀ p ∈ library s.1.length last gs, eval u p = 0 := by
  induction gs generalizing s last with
  | nil =>
    intro p hp
    simp only [library,List.mem_singleton] at hp; subst p
    change s.2=true at yes
    simp only [one,map_add,eval_term,mv_empty,mv_var _ hu,hl,yes]
    decide
  | cons g gs ih =>
    obtain ⟨i,j⟩ := g
    let t := estep s (i,j)
    have hn : t.1.length=s.1.length+1 := by simp [t,estep]
    have read (k : Nat) : u (normWire s.1.length k) = s.1.getD k true := by
      by_cases hk : k<s.1.length
      · rw [normWire,if_pos hk,ht k (by rw [len_run]; omega),read_before s _ k hk]
      · simp [normWire,hk,hu,List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : s.1.length ≤ k)]
    have out : u s.1.length=t.2 := by
      rw [ht _ (by rw [len_run]; simp),List.foldl_cons,read_before t gs _ (by omega)]
      simp [t,estep]
    have zero := nand_zero (s.1.getD i true) (s.1.getD j true)
    have hr (m : Mon) : eval u (gated m (normWire s.1.length i) (normWire s.1.length j) s.1.length)=0 := by
      rw [gated_eval u hu,read,read,out]
      change mv u m * (1+bit (!(s.1.getD i true && s.1.getD j true))+_) = _
      rw [zero,mul_zero]
    have tail := ih t s.1.length out yes ht
    intro p hp
    simp only [library,List.mem_append,List.mem_map] at hp
    rcases hp with ⟨m,_,rfl⟩|hp
    · exact hr _
    · exact tail _ (hn ▸ hp)

noncomputable def mix {V : Type} [AddCommGroup V] [Module F V] {k : Nat}
    (bank : Fin k → V) : (Fin k → F) →ₗ[F] V where
  toFun r := ∑ i, r i • bank i
  map_add' r s := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' a r := by simp [Finset.smul_sum,mul_smul]

noncomputable def packet (l : List Poly) (m : F) (r : Fin l.length → F) : Poly :=
  m • one + mix l.get r

/-- Evaluate the canonical coefficient packet on the authentic full registered trace. -/
theorem authentic_open (x : List Bool) (gs : GateList) (yes : evalGates (x,gs)=true)
    (m : F) (r : Fin (library (x.length+1) 0 gs).length → F) :
    let u := fun i ↦ (gs.foldl estep (true::x,true)).1.getD i true
    eval u (packet (library (x.length+1) 0 gs) m r) = m := by
  intro u
  have hu : u 0=true := read_before (true::x,true) gs 0 (by simp)
  have h := library_zero u hu (true::x,true) 0 gs hu yes (fun _ _ ↦ rfl)
  let l := library (x.length+1) 0 gs
  have hn (i : Fin l.length) : eval u (l.get i) = 0 := h _ (List.get_mem ..)
  change eval u (packet l m r)=m
  simp only [packet,map_add,map_smul,one,eval_term,mv_empty,smul_eq_mul,mul_one]
  change m + eval u (∑ i, r i • l.get i) = m
  simp only [map_sum,map_smul,hn,smul_zero,Finset.sum_const_zero,add_zero]

section Coset
variable {S V : Type} [AddCommGroup S] [Module F S] [Fintype S] [AddCommGroup V] [Module F V]
variable (A : S →ₗ[F] V) (e : V)
noncomputable def count (m : Bool) (y : V) := Nat.card {r : S // (if m then e else 0) + A r = y}

theorem equal_laws : count A e false = count A e true ↔ ∃ v, A v=e := by
  classical
  constructor
  · intro h
    have ha : 0 < count A e true e := by
      apply Nat.card_pos_iff.mpr
      exact ⟨⟨⟨0,by simp⟩⟩,inferInstance⟩
    rw [← congrFun h e] at ha
    have hn : Nonempty {r : S // (if false then e else 0)+A r=e} := Nat.card_pos_iff.mp ha |>.1
    obtain ⟨⟨v,hv⟩⟩ := hn; exact ⟨v,by simpa using hv⟩
  · rintro ⟨v,hv⟩
    funext y
    apply Nat.card_congr
    exact {toFun := fun r ↦ ⟨r.val-v,by simpa [map_sub,hv] using (show A r.val=y by simpa using r.property)⟩
           invFun := fun r ↦ ⟨r.val+v,by simpa [map_add,hv,add_comm] using r.property⟩
           left_inv := fun r ↦ by ext; simp
           right_inv := fun r ↦ by ext; simp}

theorem disjoint_laws (hn : ¬∃ v,A v=e) (r s : S) : A r ≠ e + A s := by
  intro h; apply hn; exact ⟨r-s,by rw [map_sub,h]; abel⟩

/-- Semantic equivalence of a refutation and an exact public representation
are separated by the kernel of the interpretation. Randomizing a span of null
terms repairs a supplied refutation precisely when its residual lies in that span. -/
theorem kernel_repair {W : Type} [AddCommGroup W] [Module F W] (E : V →ₗ[F] W) :
    (∃ v, E (A v)=E e) ↔ ∃ v d, E d=0 ∧ A v+d=e := by
  constructor
  · rintro ⟨v,hv⟩; exact ⟨v,e-A v,by rw [map_sub,hv,sub_self],by abel⟩
  · rintro ⟨v,d,hd,he⟩; exact ⟨v,by rw [← he,map_add,hd,add_zero]⟩


theorem public_separator (hn : ¬∃ v,A v=e) :
    ∃ f : V →ₗ[F] F, ∀ m : F, ∀ r : S, f (m • e + A r)=m := by
  have he : e ∉ LinearMap.range A := hn
  obtain ⟨f,hf,hz⟩ := Submodule.exists_dual_map_eq_bot_of_notMem he inferInstance
  have h1 : f e=1 := by
    have aux : ∀ a : F, a≠0 → a=1 := by decide
    exact aux _ hf
  refine ⟨f,?_⟩; intro m r
  have hr : f (A r) ∈ (LinearMap.range A).map f := ⟨A r,⟨r,rfl⟩,rfl⟩
  rw [hz,Submodule.mem_bot] at hr
  simp [map_add,map_smul,h1,hr]

end Coset
end NANDCanonicalBank
