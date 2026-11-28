import Mathlib.Tactic

set_option maxRecDepth 18000
namespace ShortSumDigits
def radix : List Nat → Nat
  | [] => 1
  | d::ds => (d+1)*radix ds
def marker : List Nat → Nat
  | [] => 0
  | c::cs => c + 2*marker cs
def mixed : List (Nat × Nat) → Nat
  | [] => 0
  | (d,x)::rs => x+(d+1)*mixed rs

theorem digit_product (n : Nat) : (n+1)*3*2^n ≤ 4*3^n := by
  cases n with
  | zero => decide
  | succ n =>
    induction n with
    | zero => decide
    | succ n ih =>
      rw [Nat.pow_succ _ (n+1),Nat.pow_succ _ (n+1)]
      nlinarith [Nat.mul_le_mul_right 3 ih,
        Nat.zero_le (n * 2^(n+1))]

theorem balance (ds : List Nat) :
    radix ds * 3^ds.length * 2^ds.sum ≤ 4^ds.length * 3^ds.sum := by
  induction ds with
  | nil => decide
  | cons d ds ih =>
    simp only [radix,List.length_cons,List.sum_cons,pow_add,pow_succ]
    calc
      _ = ((d+1)*3*2^d)*(radix ds*3^ds.length*2^ds.sum) := by ring
      _ ≤ (4*3^d)*(4^ds.length*3^ds.sum) := Nat.mul_le_mul (digit_product d) ih
      _ = _ := by ring

theorem all_radices (ds : List Nat) (hl : ds.length=4225) (hs : ds.sum=8192) :
    radix ds ≤ 2^6546 := by
  have h := balance ds
  rw [hl,hs] at h
  have hb : 4^4225 * 3^8192 ≤ (2^6546 : Nat)*(3^4225*2^8192) := by decide
  rw [Nat.mul_assoc] at h
  exact Nat.le_of_mul_le_mul_right (h.trans hb) (by positivity)

/-- The cardinality and marker residues of the translated total separate exactly. -/
theorem fields (S m L K H markerVal hi z : Int) (hL : 0<L) (hK : 0<K)
    (cong : S+L*(markerVal+K*hi)=m+L*(K-1)+L*K*H*z) (hs : S=m) :
    markerVal+1 = K*(1+H*z-hi) := by
  subst S
  have h : L*(markerVal+1-K*(1+H*z-hi))=0 := by linarith only [cong] <;> ring_nf at * <;> linarith
  rcases mul_eq_zero.mp h with h|h
  · omega
  · omega

theorem centered_exact (K H markerVal hi z : Int) (hK : 0<K)
    (sep : markerVal+1=K*(1+H*z-hi)) (all : markerVal=K-1)
    (small : -H<hi ∧ hi<H) : hi=0 := by
  have h : K*(H*z-hi)=0 := by rw [all] at sep; nlinarith
  have ha : H*z=hi := by rcases mul_eq_zero.mp h with hx|hx <;> omega
  by_cases hz : z=0
  · rw [hz,mul_zero] at ha; omega
  by_cases hp : 0<z
  · nlinarith [Int.mul_nonneg (show 0≤H by omega) (show 0≤z-1 by omega)]
  · nlinarith [Int.mul_nonneg (show 0≤H by omega) (show 0≤-z-1 by omega)]

theorem carry_step {d k : Nat} {cs : List Nat} {z : Nat}
    (he : k+marker (d::cs)+1 = 2^(d::cs).length*z) :
    k+d=2*((k+d)/2)+1 ∧ (k+d)/2+marker cs+1=2^cs.length*z := by
  have h : k+d+2*marker cs+1=2*(2^cs.length*z) := by
    simpa [marker,pow_succ,Nat.add_assoc,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using he
  omega

theorem marker_min (cs : List Nat) (k z : Nat) (h : k+marker cs+1=2^cs.length*z) :
    cs.length≤k+cs.sum := by
  induction cs generalizing k with
  | nil => simp
  | cons d cs ih =>
    have h1 := carry_step h
    have hh := ih _ h1.2
    simp only [List.length_cons,List.sum_cons]; omega

theorem marker_unique (cs : List Nat) (z : Nat) (hs : cs.sum=cs.length)
    (he : marker cs+1=2^cs.length*z) : ∀ d ∈ cs,d=1 := by
  induction cs with
  | nil => simp
  | cons d cs ih =>
    have h := carry_step (k:=0) (by simpa using he)
    have hh := marker_min cs ((0+d)/2) z h.2
    simp only [List.sum_cons,List.length_cons] at hs
    have hd : d=1 := by omega
    have ht : cs.sum=cs.length := by omega
    have hm : marker cs+1=2^cs.length*z := by omega
    simpa [hd] using (show d=1 ∧ ∀ a∈cs,a=1 from ⟨hd,ih ht hm⟩)

theorem marker_ones (cs : List Nat) (h : ∀ d ∈ cs,d=1) :
    marker cs+1=2^cs.length := by
  induction cs with
  | nil => rfl
  | cons d cs ih =>
    have hd := h d (by simp)
    have ht := ih (fun k hk ↦ h k (by simp [hk]))
    simp only [marker,List.length_cons,pow_succ]; omega

theorem translated_target (ds : List Nat) :
    mixed (ds.map fun d ↦ (d,d))+1 = radix ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [List.map_cons,mixed,radix]; nlinarith

theorem mixed_exact (rs : List (Nat × Nat)) (bounds : ∀ p ∈ rs,p.2≤2*p.1)
    (he : mixed rs+1=radix (rs.map Prod.fst)) : ∀ p ∈ rs,p.2=p.1 := by
  induction rs with
  | nil => simp
  | cons p rs ih =>
    obtain ⟨d,x⟩ := p
    have hb := bounds (d,x) (by simp)
    simp only [mixed,List.map_cons,radix] at he
    let a := mixed rs
    let b := radix (rs.map Prod.fst)
    change x+(d+1)*a+1=(d+1)*b at he
    have hh : b=a+1 := by
      by_contra hn
      by_cases h : b≤a
      · nlinarith [Nat.mul_le_mul_left (d+1) h]
      · nlinarith [Nat.mul_le_mul_left (d+1) (show a+2≤b by omega)]
    have hx : x=d := by rw [hh] at he; nlinarith
    have ht := ih (fun p hp ↦ bounds p (by simp [hp])) hh.symm
    intro p hp; rcases List.mem_cons.mp hp with rfl|hp
    · exact hx
    · exact ht _ hp

theorem fixed_numbers : (2:Nat)^14>3*4225 ∧ 14+4225+6546=10785 ∧
    1+2*128+4*4095+3=16640 ∧ 16640*10785=179462400 := by decide


theorem mixed_bound (rs : List (Nat × Nat)) (hb : ∀ p ∈ rs,p.2≤2*p.1) :
    mixed rs+2≤2*radix (rs.map Prod.fst) := by
  induction rs with
  | nil => decide
  | cons p rs ih =>
    obtain ⟨d,x⟩ := p
    have hx := hb (d,x) (by simp)
    have ht := ih (fun p h ↦ hb p (by simp [h]))
    simp only [mixed,List.map_cons,radix]
    nlinarith [Nat.mul_le_mul_left (d+1) ht]

/-- After selecting exactly one item in every group, the centered high
field vanishes precisely when the wire digits are all at their targets. -/
theorem exact_high (rs : List (Nat × Nat)) (H : Nat) (z : Int)
    (hb : ∀ p ∈ rs,p.2≤2*p.1) (hh : radix (rs.map Prod.fst)≤H)
    (he : (mixed rs:Int)+1-(radix (rs.map Prod.fst):Int)=H*z) :
    ∀ p ∈ rs,p.2=p.1 := by
  apply mixed_exact rs hb
  have hu := mixed_bound rs hb
  have hz : z=0 := by
    by_contra hn
    by_cases ha : 0<z
    · nlinarith [Int.mul_nonneg (Int.natCast_nonneg H) (show 0≤z-1 by omega),
        (show (mixed rs:Int)+2≤2*(radix (rs.map Prod.fst):Int) by exact_mod_cast hu),
        (show (radix (rs.map Prod.fst):Int)≤H by exact_mod_cast hh)]
    · nlinarith [Int.mul_nonneg (Int.natCast_nonneg H) (show 0≤ -z-1 by omega),
        (show (radix (rs.map Prod.fst):Int)≤H by exact_mod_cast hh),
        Int.natCast_nonneg (mixed rs)]
  rw [hz,mul_zero] at he
  omega

end ShortSumDigits
