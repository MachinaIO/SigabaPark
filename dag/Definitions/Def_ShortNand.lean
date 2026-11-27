import Mathlib
import SigabaNeoStd.Machines.Gates
namespace ShortNand
open SigabaNeo
structure B where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
deriving DecidableEq
def bit (x : Bool) : ℤ := if x then 1 else 0
def sel (x y : Bool) : B :=
  match x,y with
  | false,false => ⟨1,0,0,0⟩
  | false,true => ⟨0,1,0,0⟩
  | true,false => ⟨0,0,1,0⟩
  | true,true => ⟨0,0,0,1⟩
def mass (b : B) := b.a+b.b+b.c+b.d
def left (b : B) := b.c+b.d
def right (b : B) := b.b+b.d
def out (b : B) := b.a+b.b+b.c
def sq (b : B) := b.a^2+b.b^2+b.c^2+b.d^2
def eqm (q x y : ℤ) := ∃ k : ℤ, x=y+q*k
def hot (b : B) := ∃ x y : Bool, b=sel x y
def decode (q z : ℤ) : Bool := z%q==1

theorem smallCong (q x y : ℤ) (hq : 0<q) (h : eqm q x y)
    (hl : -q < x-y) (hr : x-y<q) : x=y := by
  obtain ⟨k,hk⟩ := h
  rcases lt_trichotomy k 0 with h|h|h
  · have h' : 0 ≤ q*(-k-1) := mul_nonneg (by omega) (by omega)
    nlinarith
  · subst k; simp_all
  · have h' : 0 ≤ q*(k-1) := mul_nonneg (by omega) (by omega)
    nlinarith

theorem block (q : ℤ) (hq : 5≤q) (b : B) (hn : eqm q (mass b) 1) :
    (hot b ∧ sq b=1) ∨ 3 ≤ sq b := by
  by_cases h : 3 ≤ sq b
  · exact Or.inr h
  left
  rcases b with ⟨a,b,c,d⟩
  simp only [sq] at h ⊢
  have ha : -1≤a ∧ a≤1 := by constructor <;> by_contra! hc <;> nlinarith [sq_nonneg b,sq_nonneg c,sq_nonneg d]
  have hb : -1≤b ∧ b≤1 := by constructor <;> by_contra! hc <;> nlinarith [sq_nonneg a,sq_nonneg c,sq_nonneg d]
  have hc : -1≤c ∧ c≤1 := by constructor <;> by_contra! hd <;> nlinarith [sq_nonneg b,sq_nonneg a,sq_nonneg d]
  have hd : -1≤d ∧ d≤1 := by constructor <;> by_contra! he <;> nlinarith [sq_nonneg b,sq_nonneg c,sq_nonneg a]
  have prodNonneg (j : ℤ) : 0 ≤ (j-1)*j := by
    by_cases hj : j≤0
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) hj
    · exact mul_nonneg (by omega) (by omega)
  have low : -2≤a+b+c+d := by nlinarith [prodNonneg ( -a),prodNonneg (-b),prodNonneg (-c),prodNonneg (-d)]
  have high : a+b+c+d≤2 := by nlinarith [prodNonneg a,prodNonneg b,prodNonneg c,prodNonneg d]
  have mass1 := smallCong q (a+b+c+d) 1 (by omega) hn (by omega) (by omega)
  obtain ⟨ha0,ha1⟩ := ha
  obtain ⟨hb0,hb1⟩ := hb
  obtain ⟨hc0,hc1⟩ := hc
  obtain ⟨hd0,hd1⟩ := hd
  clear hn low high prodNonneg
  interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;>
    first | (exfalso; norm_num at *; done) | (constructor <;> first | decide | (unfold hot; decide))

def rows (q : ℤ) : List ℤ → ℤ → GateList → List B → Prop
 | _,v,[],[] => eqm q v 1
 | s,_,(a,b)::gs,t::ts => eqm q (mass t) 1 ∧ eqm q (left t) (s.getD a 1) ∧
     eqm q (right t) (s.getD b 1) ∧ rows q (s++[out t]) (out t) gs ts
 | _,_,_,_ => False
def energy (bs : List B) : ℤ := (bs.map sq).sum
def feasible (q : ℤ) (n : ℕ) (gs : GateList) (bs : List B) :=
  ∃ inp : List ℤ, inp.length=n ∧ rows q (1::inp) 1 gs bs

theorem rowFacts (q : ℤ) (hq : 5≤q) (gs : GateList) (bs : List B) (s : List ℤ) (v : ℤ)
    (h : rows q s v gs bs) : bs.length=gs.length ∧ (gs.length : ℤ)≤energy bs ∧
    (energy bs ≤ (gs.length : ℤ)+1 → ∀ t∈bs, hot t) := by
  induction gs generalizing bs s v with
  | nil =>
    cases bs <;> simp_all [rows,energy]
  | cons g gs ih =>
    cases g with | mk a b =>
    cases bs with
    | nil => exact False.elim h
    | cons t ts =>
      obtain ⟨hn,_,_,ht⟩ := h
      obtain ⟨hlen,hfloor,htail⟩ := ih ts _ _ ht
      simp only [List.length_cons, Nat.cast_succ,energy,List.map_cons,List.sum_cons] at *
      refine ⟨by omega, ?_, ?_⟩
      · rcases block q hq t hn with h|h <;> omega
      · intro hm x hx
        rcases block q hq t hn with h|h
        · rcases List.mem_cons.mp hx with hh|hh
          · exact hh ▸ h.1
          · exact htail (by omega) x hh
        · omega

theorem readBit (q : ℤ) (hq : 5≤q) (x : Bool) (z : ℤ) (h : eqm q (bit x) z) :
    decode q z = x := by
  obtain ⟨k,h⟩ := h
  have he : bit x % q = z%q := by rw [h]; simp [Int.add_emod]
  cases x <;> simp [bit,Int.emod_eq_of_lt (by decide : (0:ℤ)≤1) (by omega : 1<q)] at he <;> simp [decode,←he]

theorem getMap {A D : Type} (f : A → D) (s : List A) (i : ℕ) (v : A) :
    (s.map f).getD i (f v)=f (s.getD i v) := by
  induction s generalizing i with
  | nil => simp [List.getD]
  | cons a s ih => cases i <;> simp [List.getD, List.getElem?_map]

theorem selFacts (a b : Bool) : mass (sel a b)=1 ∧ left (sel a b)=bit a ∧ right (sel a b)=bit b ∧
    out (sel a b)=bit (!(a && b)) ∧ sq (sel a b)=1 := by
  cases a <;> cases b <;> decide

theorem rowsYield (q : ℤ) (hq : 5≤q) (gs : GateList) (bs : List B) (s : List ℤ) (v : ℤ)
    (h : rows q s v gs bs) (hh : ∀ t∈bs, hot t) :
    (gs.foldl estep (s.map (decode q),decode q v)).2 = true := by
  have one : decode q 1=true := by simp [decode,Int.emod_eq_of_lt (by decide : (0:ℤ)≤1) (by omega : 1<q)]
  induction gs generalizing bs s v with
  | nil =>
    cases bs with
    | nil =>
      obtain ⟨k,hk⟩ := h
      apply readBit q hq true v
      exact ⟨-k,by change (1:ℤ)=_;linarith⟩
    | cons => exact False.elim h
  | cons g gs ih =>
    rcases g with ⟨a,b⟩
    cases bs with
    | nil => exact False.elim h
    | cons t ts =>
      obtain ⟨_,hl,hr,ht⟩ := h
      obtain ⟨x,y,rfl⟩ := hh t (by simp)
      obtain ⟨_,h1,h2,h3,_⟩ := selFacts x y
      rw [h1] at hl; rw [h2] at hr
      have decBit (k : Bool) : decode q (bit k)=k := readBit q hq _ _ ⟨0,by simp⟩
      have l : (s.map (decode q)).getD a true=x := by
        rw [←one,getMap];exact readBit q hq _ _ hl
      have r : (s.map (decode q)).getD b true=y := by
        rw [←one,getMap];exact readBit q hq _ _ hr
      specialize ih ts _ _ ht (fun z hz => hh z (by simp [hz]))
      simp only [List.foldl_cons,estep,l,r]
      simpa only [List.map_append,List.map_cons,List.map_nil,h3,decBit] using ih

theorem synth (q : ℤ) (gs : GateList) (s : List Bool) (v : Bool)
    (h : (gs.foldl estep (s,v)).2=true) :
    ∃ bs, rows q (s.map bit) (bit v) gs bs ∧ energy bs=gs.length := by
  induction gs generalizing s v with
  | nil =>
    simp only [List.foldl_nil] at h;subst v
    exact ⟨[],⟨0,by simp [bit]⟩,rfl⟩
  | cons g gs ih =>
    rcases g with ⟨a,b⟩
    let x:=s.getD a true
    let y:=s.getD b true
    let z:= !(x && y)
    obtain ⟨bs,ht,he⟩ := ih (s++[z]) z h
    obtain ⟨hm,hl,hr,ho,hs⟩ := selFacts x y
    refine ⟨sel x y::bs, ⟨⟨0,by simp [hm]⟩,⟨0,?_⟩,⟨0,?_⟩,?_⟩,?_⟩
    · rw [hl, mul_zero, add_zero]; exact (getMap bit s a true).symm
    · rw [hr, mul_zero, add_zero]; exact (getMap bit s b true).symm
    · simpa [List.map_append,ho,z] using ht
    · simp only [energy,List.map_cons,List.sum_cons] at *; rw [hs,he];simp;omega

theorem noNext (bs : List B) (hh : ∀ b ∈ bs, hot b) : energy bs = bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨x,y,rfl⟩ := hh b (by simp)
    have h := ih (fun a ha => hh a (by simp [ha]))
    simp only [energy,List.map_cons,List.sum_cons] at *
    rw [(selFacts x y).2.2.2.2,h]
    simp; omega



theorem exactFiber (q : ℤ) (hq : 5≤q) (n : ℕ) (gs : GateList) :
    (∃ inp : List Bool, inp.length=n ∧ evalGates (inp,gs)=true) ↔
      ∃ bs, feasible q n gs bs ∧ energy bs ≤ (gs.length : ℤ)+1 := by
  constructor
  · rintro ⟨x,hx,hw⟩
    obtain ⟨bs,ht,he⟩ := synth q gs (true::x) true hw
    exact ⟨bs,⟨x.map bit,by simp [hx],ht⟩,by omega⟩
  · rintro ⟨bs,⟨x,hx,ht⟩,hb⟩
    obtain ⟨_,_,hh⟩ := rowFacts q hq gs bs (1::x) 1 ht
    have h:=rowsYield q hq gs bs (1::x) 1 ht (hh hb)
    have one : decode q 1=true := by simp [decode,Int.emod_eq_of_lt (by decide : (0:ℤ)≤1) (by omega : 1<q)]
    exact ⟨x.map (decode q),by simp [hx],by simpa [evalGates,one] using h⟩
theorem halfSq (s : ℤ) : (s/2)^2 + (s-s/2)^2 ≤ s^2 := by
  generalize hk : s/2=k
  have h : s=2*k ∨ s=2*k+1 := by omega
  rcases h with h|h
  · rw [h]; nlinarith [sq_nonneg k]
  · rw [h]; by_cases h0 : 0≤k
    · nlinarith [mul_nonneg h0 (show 0≤k+1 by omega)]
    · nlinarith [mul_nonneg_of_nonpos_of_nonpos (show k≤0 by omega) (show k+1≤0 by omega)]
end ShortNand
