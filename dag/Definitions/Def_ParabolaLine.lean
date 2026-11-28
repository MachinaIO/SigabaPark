import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic

namespace ParabolaLine
variable {K : Type} [Field K]

abbrev Four (K : Type) := K × K × K × K

def seed (a b c d : K) : Four K := (a,b,c,d)

/-- The two independent rows are the slope and intercept of each published map. -/
def header (s : K) (r : Four K) : Four K :=
  let (a,b,c,d) := r
  (c-b,c^2-b^2,a-c+d,a^2-c^2+d^2+s)

def changeSeed (h2 : (2:K) ≠ 0) : Four K ≃ Four K where
  toFun r := let (a,b,c,d) := r; (c-b,c+b,a+d,a-d)
  invFun r := let (u,v,w,t) := r; ((w+t)/2,(v-u)/2,(v+u)/2,(w-t)/2)
  left_inv := by rintro ⟨a,b,c,d⟩; ext <;> dsimp <;> field_simp <;> ring
  right_inv := by rintro ⟨a,b,c,d⟩; ext <;> dsimp <;> field_simp <;> ring

/-- On a nonzero-slope stratum this transformation of the full public header is invertible. -/
def normalize (y : Four K) : Four K :=
  let (u,v,x,z) := y
  let c := (v/u+u)/2
  (u,v/u,x+c,z+c^2-(x+c)^2/2)

def denormalize (y : Four K) : Four K :=
  let (u,v,x,z) := y
  let c := (v+u)/2
  (u,u*v,x-c,z-c^2+x^2/2)

theorem inverse_header (y : Four K) (h : y.1 ≠ 0) :
    denormalize (normalize y) = y := by
  obtain ⟨u,v,x,z⟩ := y
  change u ≠ 0 at h
  ext <;> simp [normalize,denormalize] <;> field_simp <;> ring

theorem nonzero_chart (a b c d s : K) (hu : c-b ≠ 0) (h2 : (2:K) ≠ 0) :
    normalize (header s (seed a b c d)) = (c-b,c+b,a+d,(a-d)^2/2+s) := by
  have hv : (c^2-b^2)/(c-b) = c+b := (div_eq_iff hu).mpr (by ring)
  have hc : (c+b+(c-b))/2 = c := (div_eq_iff h2).mpr (by ring)
  ext <;> simp [normalize,header,seed,hv,hc] <;> ring_nf <;> field_simp <;> ring

def zeroNormalize (y : Four K) : K × K := (y.2.2.1,y.2.2.2-y.2.2.1^2)

theorem zero_chart (a b d s : K) :
    zeroNormalize (header s (seed a b b d)) = (a-b+d,(-2)*(a-b)*(d-b)+s) := by
  ext <;> simp [zeroNormalize,header,seed] <;> ring

def zeroChange : (K × K × K) ≃ (K × K × K) where
  toFun r := let (a,b,d) := r; (a-b+d,a-b,d-b)
  invFun r := let (x,u,v) := r; (x-v,x-u-v,x-u)
  left_inv := by rintro ⟨a,b,d⟩; ext <;> dsimp <;> ring
  right_inv := by rintro ⟨x,u,v⟩; ext <;> dsimp <;> ring

/-- Number of representations of a nonzero difference of squares. -/
def differenceEquiv (e : K) (he : e ≠ 0) (h2 : (2:K) ≠ 0) :
    {p : K × K // p.1^2-p.2^2=e} ≃ Kˣ where
  toFun p := Units.mk0 (p.val.1-p.val.2) (by
    intro h
    have hh : p.val.1 = p.val.2 := sub_eq_zero.mp h
    exact he (by rw [← p.property,hh,sub_self]))
  invFun u := ⟨(((u:K)+e/u)/2,(e/u-(u:K))/2),by
    have h := u.ne_zero
    dsimp; field_simp; ring⟩
  left_inv := by
    rintro ⟨⟨x,y⟩,hpp⟩
    change x^2-y^2=e at hpp
    have hn : x-y ≠ 0 := by intro h; exact he (by rw [← hpp,sub_eq_zero.mp h,sub_self])
    apply Subtype.ext
    apply Prod.ext <;> dsimp
    all_goals field_simp <;> rw [← hpp] <;> ring
  right_inv := by
    intro u
    apply Units.ext
    dsimp
    have hu := u.ne_zero
    field_simp
    ring

theorem difference_count [Fintype K] [DecidableEq K] (e : K) (he : e ≠ 0) (h2 : (2:K) ≠ 0) :
    Fintype.card {p : K × K // p.1^2-p.2^2=e} = Fintype.card K - 1 := by
  rw [Fintype.card_congr (differenceEquiv e he h2),Fintype.card_units]


section Count
variable [Fintype K] [DecidableEq K]
def roots (z : K) := Finset.univ.filter (fun x : K ↦ x^2=z)

theorem roots_at (v : K) : roots (v^2) = {v,-v} := by
  ext x
  simp [roots,sq_eq_sq_iff_eq_or_eq_neg]

theorem zero_root : (roots (0:K)).card = 1 := by
  have h := roots_at (0:K)
  simpa using congrArg Finset.card h

theorem two_roots {z : K} (hz : z ≠ 0) (h2 : (2:K) ≠ 0) :
    (roots z).card = 0 ∨ (roots z).card = 2 := by
  by_cases h : (roots z).Nonempty
  · obtain ⟨v,hv⟩ := h
    have hv' : v^2 = z := (Finset.mem_filter.mp hv).2
    have hn : v ≠ -v := by
      intro he
      apply hz
      have hh : (2:K)*v=0 := by linear_combination he
      have := (mul_eq_zero.mp hh).resolve_left h2
      simp [← hv',this]
    right
    rw [← hv',roots_at]
    simp [hn]
  · left; simpa using h

theorem overlap_term (z e : K) (he : e ≠ 0) (h2 : (2:K) ≠ 0) :
    2 * min (roots z).card (roots (z-e)).card =
      (roots z).card * (roots (z-e)).card := by
  have hc : ∀ u : K, (roots u).card = 0 ∨ (roots u).card = 2 ∨ u=0 := by
    intro u; by_cases hu : u=0
    · exact Or.inr (Or.inr hu)
    · exact (two_roots hu h2).elim Or.inl (fun hh ↦ Or.inr (Or.inl hh))
  rcases hc z with h|h|h <;> rcases hc (z-e) with g|g|g <;> simp_all [zero_root]
  all_goals try omega

def fiberEquiv (e : K) :
    (Σ z : K, ↥(roots z) × ↥(roots (z-e))) ≃ {p : K × K // p.1^2-p.2^2=e} where
  toFun v := ⟨(v.2.1.val,v.2.2.val),by
    have h := (Finset.mem_filter.mp v.2.1.property).2
    have g := (Finset.mem_filter.mp v.2.2.property).2
    change v.2.1.val^2 = v.1 at h
    change v.2.2.val^2 = v.1-e at g
    rw [h,g]; ring⟩
  invFun p := ⟨p.val.1^2,⟨p.val.1,by simp [roots]⟩,⟨p.val.2,by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by linear_combination -p.property⟩⟩⟩
  left_inv := by
    rintro ⟨z,⟨x,hx⟩,⟨y,hy⟩⟩
    have hz : x^2=z := (Finset.mem_filter.mp hx).2
    subst z; rfl
  right_inv _ := rfl

theorem square_overlap (e : K) (he : e ≠ 0) (h2 : (2:K) ≠ 0) :
    2 * ∑ z : K, min (roots z).card (roots (z-e)).card = Fintype.card K - 1 := by
  rw [Finset.mul_sum]
  simp only [overlap_term _ _ he h2]
  have h := Fintype.card_congr (fiberEquiv e)
  simpa [Fintype.card_sigma,Fintype.card_prod,difference_count e he h2] using h

end Count

end ParabolaLine
