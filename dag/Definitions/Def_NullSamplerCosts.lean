import Mathlib

namespace OneBitSampler
inductive Tree (I X : Type) where
  | ret (x : X)
  | ask (i : I) (ifFalse ifTrue : Tree I X)

def run {I X : Type} (f : I → Bool) : Tree I X → X
  | .ret x => x
  | .ask i l r => if f i then run f r else run f l

def visited {I X : Type} [DecidableEq I] : Tree I X → Finset I
  | .ret _ => ∅
  | .ask i l _ => insert i (visited l)

def accept {I X : Type} (t : Tree I X) (f : I → Bool) (test : X → Bool) : ℤ :=
  if test (run f t) then 1 else 0

def spike {I : Type} [DecidableEq I] (v : I) (i : I) := decide (i=v)

theorem unchanged {I X : Type} [DecidableEq I] (t : Tree I X) (v : I)
    (h : v∉visited t) : run (spike v) t=run (fun _=>false) t := by
  induction t with
  | ret x => rfl
  | ask i l r hl hr =>
    simp only [visited, Finset.mem_insert, not_or] at h
    simpa [run,spike,Ne.symm h.1] using hl h.2

theorem costOnMiss {I X : Type} [DecidableEq I] (t : Tree I X) (v : I) (D : X → Bool) :
    |accept t (spike v) D-accept t (fun _=>false) D| ≤ if v∈visited t then (1:ℤ) else 0 := by
  by_cases h:v∈visited t
  · simp only [if_pos h,accept]
    split <;> split <;> decide
  · simp [accept,unchanged t v h,h]

def block (u k W : Nat) := (W*u^(2*k+9), u^(4*k+16))

theorem perBlock (u k W : Nat) (hu : 0<u) (hN : u^(4*k+16)≤2^128)
    (hW : u^(2*k+6)≤W) :
    (block u k W).2 ≤ 256*(block u k W).1 := by
  have hu' : u≤256 := by
    by_contra! hn
    have h₁ : 257^16 ≤ u^16 := Nat.pow_le_pow_left hn 16
    have h₂ : u^16 ≤ u^(4*k+16) := Nat.pow_le_pow_right hu (by omega)
    have bad := h₁.trans (h₂.trans hN)
    norm_num at bad
  unfold block
  change u^(4*k+16) ≤ 256*(W*u^(2*k+9))
  calc
    _ = u*(u^(2*k+6)*u^(2*k+9)) := by
      rw [←pow_add,←pow_succ'];congr 1;omega
    _ ≤ _ := Nat.mul_le_mul hu' (Nat.mul_le_mul_right _ hW)
end OneBitSampler
