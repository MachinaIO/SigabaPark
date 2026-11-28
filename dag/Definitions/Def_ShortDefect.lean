import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Roots

namespace ShortDefect
def mass (xs : List Int) := xs.sum
def sq (xs : List Int) := (xs.map (fun x ↦ x*x)).sum
def cost (x : Int) := x*(x-1)/2
def D (xs : List Int) := (xs.map cost).sum
def Binary (xs : List Int) := ∀ x ∈ xs,x=0 ∨ x=1
def dot : List Int → List Int → Int
  | x::xs,a::as => x*a+dot xs as
  | _,_ => 0

theorem twice (x : Int) : 2*cost x=x*(x-1) := by
  have h : x*(x-1)%2=0 := by
    rw [Int.mul_emod,Int.sub_emod]
    rcases (show x%2=0 ∨ x%2=1 by omega) with he|he <;> rw [he] <;> decide
  unfold cost; omega

theorem sign_cost (x : Int) : 0≤x*(x-1) := by
  by_cases h : x≤0
  · exact mul_nonneg_of_nonpos_of_nonpos h (by omega)
  · exact mul_nonneg (by omega) (by omega)

theorem cost_nonneg (x : Int) : 0≤cost x := by have := twice x; have := sign_cost x; omega
theorem cost_zero (x : Int) : cost x=0 ↔ x=0 ∨ x=1 := by
  constructor
  · intro h; have hh := twice x; rw [h,mul_zero] at hh
    rcases mul_eq_zero.mp hh.symm with h|h <;> omega
  · rintro (rfl|rfl) <;> decide

theorem certificate (xs : List Int) : sq xs=mass xs+2*D xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [sq,mass,D,List.map_cons,List.sum_cons] at ih ⊢; linarith [twice x]

theorem D_nonneg (xs : List Int) : 0≤D xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => change 0≤cost x+D xs; linarith [cost_nonneg x]

theorem detects (xs : List Int) : D xs=0 ↔ Binary xs := by
  induction xs with
  | nil => simp [D,Binary]
  | cons x xs ih =>
    change cost x+D xs=0 ↔ _
    have hh : Binary (x::xs) ↔ (x=0 ∨ x=1) ∧ Binary xs := by simp [Binary]
    rw [hh,← cost_zero,← ih]; have := cost_nonneg x; have := D_nonneg xs; omega

theorem lower_mass (xs : List Int) : -sq xs ≤ mass xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [sq,mass,List.map_cons,List.sum_cons] at ih ⊢; nlinarith [sign_cost (-x)]

theorem affine_dot (xs as : List Int) (h : xs.length=as.length) (L : Int) :
    dot xs (as.map (fun a ↦ 1+L*a))=mass xs+L*dot xs as := by
  induction xs generalizing as with
  | nil => simp [dot,mass]
  | cons x xs ih =>
    cases as with
    | nil => simp at h
    | cons a as => simp only [List.length_cons,Nat.succ.injEq] at h
                   simp only [List.map_cons,dot,ih as h,mass,List.sum_cons]; ring

/-- Signed target solutions, with all weights 1 modulo 16384 and bounded square norm. -/
def Allowed (as : List Int) (targetHigh modulusHigh T : Int) (xs : List Int) :=
  xs.length=as.length ∧ sq xs≤4225+2*T ∧ ∃ z : Int,
    dot xs (as.map (fun a ↦ 1+16384*a))=4225+16384*targetHigh+16384*modulusHigh*z

theorem bounded {as xs : List Int} {a q T : Int} (h : Allowed as a q T xs) (ht : T≤3966) :
    mass xs=4225 ∧ 0≤D xs ∧ D xs≤T := by
  obtain ⟨hl,hs,z,hz⟩ := h
  rw [affine_dot xs as hl] at hz
  have hm : mass xs=4225+16384*(a+q*z-dot xs as) := by linarith only [hz] <;> ring_nf at * <;> linarith
  have := lower_mass xs; have hd := D_nonneg xs; have hc := certificate xs
  omega

noncomputable def distance (xs : List Int) (p : ℝ) : ℝ := (xs.map (fun x ↦ (|(2*x-1 : Int)| : ℝ)^p)).sum
theorem single_distance (x : Int) : 1 ≤ |2*x-1| ∧ ((x≠0 ∧ x≠1) → 3≤|2*x-1|) := by
  by_cases h : 0≤2*x-1
  · rw [abs_of_nonneg h]; omega
  · rw [abs_of_nonpos (by omega : 2*x-1≤0)]; omega

theorem distance_min (xs : List Int) (p : ℝ) (hp : 0≤p) :
    (xs.length : ℝ)≤distance xs p := by
  induction xs with
  | nil => simp [distance]
  | cons x xs ih =>
    have hx : (1:ℝ)≤(|(2*x-1:Int)|:ℝ)^p := by
      have hcast : (1:ℝ) ≤ ((|2*x-1| : Int):ℝ) := by exact_mod_cast (single_distance x).1
      simpa only [Real.one_rpow,Int.cast_abs] using Real.rpow_le_rpow (by norm_num : (0:ℝ)≤1) hcast hp
    simp only [distance,List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one] at ih ⊢
    linarith

theorem distance_gap (xs : List Int) (p : ℝ) (hp : 0≤p) (h : ¬Binary xs) :
    (xs.length:ℝ)-1+3^p≤distance xs p := by
  induction xs with
  | nil => simp [Binary] at h
  | cons x xs ih =>
    by_cases b : x=0 ∨ x=1
    · have hn : ¬Binary xs := by intro h'; apply h; simpa [Binary] using And.intro b h'
      have hh := ih hn
      rcases b with rfl|rfl <;> norm_num [distance] at hh ⊢ <;> linarith
    · have hz : (3:ℝ)^p≤(|(2*x-1:Int)|:ℝ)^p := Real.rpow_le_rpow (by norm_num)
        (by exact_mod_cast (single_distance x).2 (by tauto)) hp
      have hh := distance_min xs p hp
      simp only [distance,List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one] at hh ⊢
      linarith

section Filter
variable {F : Type} [Field F] [DecidableEq F]
noncomputable def indicator (J : Finset F) (v : F) := 1- ∏ j ∈ J,(1-v/j)
theorem zero_value (J : Finset F) : indicator J 0=0 := by simp [indicator]
theorem defect_value (J : Finset F) (hn : 0 ∉ J) {v : F} (hv : v ∈ J) : indicator J v=1 := by
  have nz : v≠0 := fun h ↦ hn (h ▸ hv)
  unfold indicator
  rw [Finset.prod_eq_zero (f:=fun j ↦ 1-v/j) hv (by simp [nz]),sub_zero]

/-- Publishing the entire authorized response table is simulable by one uniform
field element when every authorized query has a nonzero defect in the filter. -/
noncomputable def response {I : Type} (J : Finset F) (v : I → F) (m r : F) :=
  fun i ↦ m+r*indicator J (v i)

theorem joint_translate {I : Type} (J : Finset F) (hn : 0 ∉ J) (v : I → F) (hv : ∀ i,v i∈J)
    (a b r : F) : response J v a r=response J v b (r+a-b) := by
  funext i; simp [response,defect_value J hn (hv i)]; ring

theorem honest {I : Type} (J : Finset F) (v : I → F) {i : I} (h : v i=0) (a r : F) :
    response J v a r i=a := by simp [response,h,zero_value]

theorem min_degree {T : Nat} (nodes : Fin T ↪ F) (P : Polynomial F)
    (h0 : P.eval 0=0) (h : ∀ i,P.eval (nodes i)=1) : T≤P.natDegree := by
  by_contra! small
  have hh : P-1=0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (P-1)
    nodes.injective (fun i ↦ by simp [h]) (by
      have hd := Polynomial.natDegree_sub_le P 1
      simp at hd; simpa using hd.trans_lt small)
  have := sub_eq_zero.mp hh
  simp_all

end Filter

local instance : Fact (Nat.Prime 4099) := ⟨by norm_num⟩
abbrev FF := ZMod 4099
def nodes (T : Int) : Finset FF := (Finset.Icc (1:Int) T).image (fun j : Int ↦ (j:FF))
theorem zero_out (T : Int) (h : T≤3966) : (0:FF) ∉ nodes T := by
  intro hv
  obtain ⟨j,hj,eq⟩ := Finset.mem_image.mp hv
  obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp hj
  have hd : (4099:Int) ∣ j := (ZMod.intCast_zmod_eq_zero_iff_dvd j 4099).mp eq
  omega

def Query (as : List Int) (a q T : Int) := {xs : List Int // Allowed as a q T xs}
def label {as : List Int} {a q T : Int} (i : Query as a q T) : FF := (D i.val:FF)

theorem restricted_simulation (as : List Int) (a q T : Int) (ht : T≤3966)
    (no : ∀ i : Query as a q T, ¬ Binary i.val) (m n r : FF) :
    response (nodes T) (@label as a q T) m r =
    response (nodes T) (@label as a q T) n (r+m-n) := by
  apply joint_translate _ (zero_out T ht)
  intro i
  have bd := bounded i.property ht
  have hn : D i.val≠0 := fun h ↦ no i ((detects _).mp h)
  unfold nodes
  exact Finset.mem_image.mpr ⟨D i.val,Finset.mem_Icc.mpr ⟨by omega,bd.2.2⟩,rfl⟩

theorem restricted_correct (as : List Int) (a q T : Int) (i : Query as a q T)
    (h : Binary i.val) (m r : FF) : response (nodes T) (@label as a q T) m r i=m := by
  apply honest
  simp [label,(detects _).mpr h]

end ShortDefect
