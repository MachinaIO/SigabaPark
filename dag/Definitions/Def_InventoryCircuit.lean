import Definitions.Def_WE_CircuitSAT
import SigabaNeoStd.Machines.Gates
import Mathlib.Tactic

set_option maxRecDepth 8192

namespace InventoryCircuit
open SigabaNeo
abbrev V := Fin 17
def pairs : List (V × V) := ((List.finRange 17).product (List.finRange 17)).filter
  (fun p ↦ decide (p.1 < p.2))
theorem num_pairs : pairs.length = 136 := by decide
def pair (k : Nat) := pairs[k]?.getD (0,0)
def primary (v : V) (d : Nat) := 1 + 4*v.val + d
def spec (B : Nat) (u v : Nat → Nat) : GateList := [
    (u 0,v 0),
    (u 0,B+0),
    (v 0,B+0),
    (B+1,B+2),
    (u 1,v 1),
    (u 1,B+4),
    (v 1,B+4),
    (B+5,B+6),
    (u 2,v 2),
    (u 2,B+8),
    (v 2,B+8),
    (B+9,B+10),
    (u 3,v 3),
    (u 3,B+12),
    (v 3,B+12),
    (B+13,B+14),
    (B+3,B+3),
    (B+7,B+7),
    (B+16,B+17),
    (B+18,B+18),
    (B+11,B+11),
    (B+19,B+20),
    (B+21,B+21),
    (B+15,B+15),
    (B+22,B+23)]
def cmpBase (k : Nat) := 129+25*k
def cmpOut (k : Nat) := cmpBase k+24
def tmp (j : Nat) := 3529+2*j
def prev : Nat → Nat
  | 0 => cmpOut 0
  | j+1 => tmp j+1
def gate (n : Nat) : Nat × Nat :=
  if n < 3400 then
    let k := n/25
    (spec (cmpBase k) (primary (pair k).1) (primary (pair k).2)).getD (n%25) (0,0)
  else if n < 3669 then
    let j := (n-3400)/2
    if (n-3400)%2 = 0 then (prev j,cmpOut (j+1)) else (tmp j,tmp j)
  else if n = 4095 then (tmp 134,tmp 134) else (1,1)

def gates := (List.range 4096).map gate
theorem gate_count : gates.length = 4096 := by simp [gates]

def state (w : List Bool) (k : Nat) := ((List.range k).map gate).foldl estep (w,true)

theorem state_succ (w : List Bool) (k : Nat) :
    state w (k+1) = estep (state w k) (gate k) := by simp [state,List.range_succ]

theorem state_length (w : List Bool) (k : Nat) : (state w k).1.length = w.length+k := by
  induction k with
  | zero => simp [state]
  | succ k ih => simp [state_succ,estep,ih,Nat.add_assoc]

theorem earlier (w : List Bool) (k n i : Nat) (h : k ≤ n) (hi : i < w.length+k) :
    (state w n).1.getD i true = (state w k).1.getD i true := by
  induction n,h using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [state_succ]
    simp only [estep,List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show i < (state w n).1.length by rw [state_length]; omega)] at ih ⊢
    exact ih

def trace (w : List Bool) (i : Nat) := (state w 4096).1.getD i true

theorem recorded (w : List Bool) (hw : w.length = 129) (j : Nat) (hj : j < 4096)
    (h₁ : (gate j).1 < 129+j) (h₂ : (gate j).2 < 129+j) :
    trace w (129+j) = !(trace w (gate j).1 && trace w (gate j).2) := by
  unfold trace
  rw [earlier w (j+1) 4096 _ (by omega) (by omega),
    earlier w j 4096 _ (by omega) (by omega : (gate j).1 < w.length+j),
    earlier w j 4096 _ (by omega) (by omega : (gate j).2 < w.length+j),state_succ]
  have hl : (state w j).1.length = 129+j := by rw [state_length,hw]
  simp [estep,← hl]

theorem cmp_at {k t : Nat} (hk : k < 136) (ht : t < 25) :
    gate (25*k+t) = (spec (cmpBase k) (primary (pair k).1) (primary (pair k).2)).getD t (0,0) := by
  simp [gate,show 25*k+t < 3400 by omega,show (25*k+t)/25=k by omega,
    show (25*k+t)%25=t by omega]

theorem cmp_valid (a b : V) (k t : Nat) (ht : t < 25) :
    let p := (spec (cmpBase k) (primary a) (primary b)).getD t (0,0)
    p.1 < cmpBase k+t ∧ p.2 < cmpBase k+t := by
  have := a.isLt; have := b.isLt
  interval_cases t <;> simp [spec,cmpBase,primary] <;> omega

theorem cmp_false (T : Nat → Bool) (B : Nat) (u v : Nat → Nat)
    (H : ∀ t < 25, T (B+t) =
      !((T ((spec B u v).getD t (0,0)).1) && (T ((spec B u v).getD t (0,0)).2)))
    (he : ∀ d < 4, T (u d) = T (v d)) : T (B+24) = false := by
  have h0 := H 0 (by decide)
  change T (B+0) = !(T (u 0) && T (v 0)) at h0
  have h1 := H 1 (by decide)
  change T (B+1) = !(T (u 0) && T (B+0)) at h1
  have h2 := H 2 (by decide)
  change T (B+2) = !(T (v 0) && T (B+0)) at h2
  have h3 := H 3 (by decide)
  change T (B+3) = !(T (B+1) && T (B+2)) at h3
  have h4 := H 4 (by decide)
  change T (B+4) = !(T (u 1) && T (v 1)) at h4
  have h5 := H 5 (by decide)
  change T (B+5) = !(T (u 1) && T (B+4)) at h5
  have h6 := H 6 (by decide)
  change T (B+6) = !(T (v 1) && T (B+4)) at h6
  have h7 := H 7 (by decide)
  change T (B+7) = !(T (B+5) && T (B+6)) at h7
  have h8 := H 8 (by decide)
  change T (B+8) = !(T (u 2) && T (v 2)) at h8
  have h9 := H 9 (by decide)
  change T (B+9) = !(T (u 2) && T (B+8)) at h9
  have h10 := H 10 (by decide)
  change T (B+10) = !(T (v 2) && T (B+8)) at h10
  have h11 := H 11 (by decide)
  change T (B+11) = !(T (B+9) && T (B+10)) at h11
  have h12 := H 12 (by decide)
  change T (B+12) = !(T (u 3) && T (v 3)) at h12
  have h13 := H 13 (by decide)
  change T (B+13) = !(T (u 3) && T (B+12)) at h13
  have h14 := H 14 (by decide)
  change T (B+14) = !(T (v 3) && T (B+12)) at h14
  have h15 := H 15 (by decide)
  change T (B+15) = !(T (B+13) && T (B+14)) at h15
  have h16 := H 16 (by decide)
  change T (B+16) = !(T (B+3) && T (B+3)) at h16
  have h17 := H 17 (by decide)
  change T (B+17) = !(T (B+7) && T (B+7)) at h17
  have h18 := H 18 (by decide)
  change T (B+18) = !(T (B+16) && T (B+17)) at h18
  have h19 := H 19 (by decide)
  change T (B+19) = !(T (B+18) && T (B+18)) at h19
  have h20 := H 20 (by decide)
  change T (B+20) = !(T (B+11) && T (B+11)) at h20
  have h21 := H 21 (by decide)
  change T (B+21) = !(T (B+19) && T (B+20)) at h21
  have h22 := H 22 (by decide)
  change T (B+22) = !(T (B+21) && T (B+21)) at h22
  have h23 := H 23 (by decide)
  change T (B+23) = !(T (B+15) && T (B+15)) at h23
  have h24 := H 24 (by decide)
  change T (B+24) = !(T (B+22) && T (B+23)) at h24
  have z3 : T (B+3) = false := by
    rw [h3,h1,h2,h0,← he 0 (by decide)]
    cases T (u 0) <;> rfl
  have z7 : T (B+7) = false := by
    rw [h7,h5,h6,h4,← he 1 (by decide)]
    cases T (u 1) <;> rfl
  have z11 : T (B+11) = false := by
    rw [h11,h9,h10,h8,← he 2 (by decide)]
    cases T (u 2) <;> rfl
  have z15 : T (B+15) = false := by
    rw [h15,h13,h14,h12,← he 3 (by decide)]
    cases T (u 3) <;> rfl
  have z18 : T (B+18) = false := by rw [h18,h16,h17,z3,z7]; rfl
  have z21 : T (B+21) = false := by rw [h21,h19,h20,z18,z11]; rfl
  have z24 : T (B+24) = false := by rw [h24,h22,h23,z21,z15]; rfl
  exact z24

theorem one_false {T : Nat → Bool}
    (H : ∀ j < 4096, (gate j).1 < 129+j → (gate j).2 < 129+j →
      T (129+j) = !(T (gate j).1 && T (gate j).2)) :
    ∃ k < 136, T (cmpOut k) = false := by
  let color : V → Fin 4 → Bool := fun v d ↦ T (primary v d.val)
  obtain ⟨a,b,ha,he⟩ : ∃ a b, a < b ∧ color a = color b := by
    by_contra! h
    have hinj : Function.Injective color := by
      intro a b hab
      rcases lt_trichotomy a b with hh|hh|hh
      · exact False.elim (h a b hh hab)
      · exact hh
      · exact False.elim (h b a hh hab.symm)
    have := Fintype.card_le_of_injective _ hinj
    simp at this
  have hm : (a,b) ∈ pairs := by simp [pairs,ha]
  obtain ⟨k,hk,hpair⟩ := List.mem_iff_getElem.mp hm
  have hkv : k < 136 := by simpa [num_pairs] using hk
  have hp : pair k = (a,b) := by simp [pair,List.getElem?_eq_getElem hk,hpair]
  refine ⟨k,hkv,cmp_false T (cmpBase k) (primary a) (primary b) ?_ ?_⟩
  · intro t ht
    have hv := cmp_valid a b k t ht
    have hg := cmp_at hkv ht
    rw [hp] at hg
    have hh := H (25*k+t) (by omega) (by rw [hg]; simpa [cmpBase,Nat.add_assoc] using hv.1)
      (by rw [hg]; simpa [cmpBase,Nat.add_assoc] using hv.2)
    simpa [hg,cmpBase,Nat.add_assoc] using hh
  · intro d hd; exact congrFun he ⟨d,hd⟩

theorem and_at (j : Nat) (hj : j < 135) :
    gate (3400+2*j) = (prev j,cmpOut (j+1)) := by simp [gate,show 3400+2*j < 3669 by omega]
theorem inv_at (j : Nat) (hj : j < 134) :
    gate (3401+2*j) = (tmp j,tmp j) := by
  simp [gate,show ¬3401+2*j < 3400 by omega,show 3401+2*j < 3669 by omega,
    show 3401+2*j-3400 = 2*j+1 by omega,show (2*j+1)/2=j by omega,
    show (2*j+1)%2=1 by omega]

theorem output_false {T : Nat → Bool}
    (H : ∀ j < 4096, (gate j).1 < 129+j → (gate j).2 < 129+j →
      T (129+j) = !(T (gate j).1 && T (gate j).2)) : T 4224 = false := by
  have htmp (j : Nat) (hj : j < 135) :
      T (tmp j) = !(T (prev j) && T (cmpOut (j+1))) := by
    have ha := and_at j hj
    have hp : prev j < 129+(3400+2*j) := by cases j <;> simp [prev,tmp,cmpOut,cmpBase] <;> omega
    have hc : cmpOut (j+1) < 129+(3400+2*j) := by simp [cmpOut,cmpBase]; omega
    have h := H (3400+2*j) (by omega) (by simpa [ha] using hp) (by simpa [ha] using hc)
    simpa [ha,tmp,← Nat.add_assoc] using h
  have hand (j : Nat) (hj : j < 134) : T (prev (j+1)) = (T (prev j) && T (cmpOut (j+1))) := by
    have hi := inv_at j hj
    have hlt : tmp j < 129+(3401+2*j) := by simp [tmp]; omega
    have hh := H (3401+2*j) (by omega) (by simpa [hi] using hlt) (by simpa [hi] using hlt)
    rw [hi] at hh
    change T (tmp j+1) = _
    rw [show tmp j+1 = 129+(3401+2*j) by unfold tmp; omega,hh]
    simp [htmp j (by omega)]
  have propagate (n : Nat) (hn : n ≤ 134) (k : Nat) (hk : k ≤ n) (hz : T (cmpOut k)=false) :
      T (prev n)=false := by
    induction n with
    | zero =>
      obtain rfl : k=0 := by omega
      exact hz
    | succ n ih =>
      rw [hand n (by omega)]
      by_cases he : k=n+1
      · simp [← he,hz]
      · simp [ih (by omega) (by omega)]
  obtain ⟨k,hk,hz⟩ := one_false H
  have endgate := H 4095 (by decide) (by decide) (by decide)
  change T 4224 = !(T (tmp 134) && T (tmp 134)) at endgate
  rw [endgate,htmp 134 (by decide)]
  by_cases he : k=135
  · subst k; simp [hz]
  · simp [propagate 134 (by decide) k (by omega) hz]

theorem raw_unsat (bits : List Bool) (hlen : bits.length = 128) : evalGates (bits,gates) = false := by
  let w := true :: bits
  have hw : w.length=129 := by simp [w,hlen]
  have hx := output_false (recorded w hw)
  have hh : (state w 4096).2 = trace w 4224 := by
    change (state w (4095+1)).2 = (state w (4095+1)).1.getD 4224 true
    rw [state_succ]
    have hl : (state w 4095).1.length=4224 := by rw [state_length,hw]
    simp [estep,← hl]
  change (state w 4096).2 = false
  exact hh.trans hx


theorem wire_bounds (j : Fin 4096) : (gate j.val).1 < 4225 ∧ (gate j.val).2 < 4225 := by
  have hj := j.isLt
  by_cases h : j.val < 3400
  · have ht : j.val%25 < 25 := Nat.mod_lt _ (by decide)
    have he := cmp_at (k:=j.val/25) (t:=j.val%25) (by omega) ht
    rw [show 25*(j.val/25)+j.val%25=j.val by omega] at he
    rw [he]
    have hv := cmp_valid (pair (j.val/25)).1 (pair (j.val/25)).2 (j.val/25) (j.val%25) ht
    dsimp [cmpBase] at hv
    exact ⟨lt_trans hv.1 (by omega), lt_trans hv.2 (by omega)⟩
  · by_cases h2 : j.val < 3669
    · let k := (j.val-3400)/2
      have hk : k ≤ 134 := by dsimp [k]; omega
      have aux : ∀ t ≤ 134, prev t < 4225 := by
        intro t ht; cases t <;> simp [prev,cmpOut,cmpBase,tmp] <;> omega
      have hp := aux k hk
      simp only [gate,if_neg h,if_pos h2]
      split
      · change prev k < _ ∧ cmpOut (k+1) < _
        exact ⟨hp,by unfold cmpOut cmpBase; omega⟩
      · change tmp k < _ ∧ tmp k < _
        unfold tmp; omega
    · simp only [gate,if_neg h,if_neg h2]; split <;> decide

open AdvancedEncryption.WE.CircuitSAT

def fixture : Circuit 128 4096 := fun j ↦
  (⟨(gate j.val).1,(wire_bounds j).1⟩,⟨(gate j.val).2,(wire_bounds j).2⟩)

theorem fixture_gates : fixture.gates = gates := by
  have aux (n : Nat) (f : Nat → Nat × Nat) : List.ofFn (fun i : Fin n ↦ f i.val) = (List.range n).map f := by
    apply List.ext_getElem
    · simp
    · intro i hi hj; simp
  exact aux 4096 gate

theorem fixture_unsatisfiable (x : Fin 128 → Bool) : ¬ Satisfies fixture x := by
  simp [Satisfies,fixture_gates,raw_unsat]

end InventoryCircuit
