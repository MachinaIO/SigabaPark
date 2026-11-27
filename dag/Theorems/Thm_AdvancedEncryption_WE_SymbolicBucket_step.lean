import Mathlib.Data.Bool.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Defs
import Mathlib

theorem AdvancedEncryption.WE.SymbolicBucket.step {V P D : Type} [DecidableEq V]
    (v : V) (ev : D → P → Bool) (nand : D → D → D) (top : D)
    (ht : ∀ p, ev top p = true)
    (hn : ∀ x y p, ev (nand x y) p = !(ev x p && ev y p))
    (keep bucket : List ((V → Bool) → D))
    (p : P) (a : V → Bool)
    (absent : ∀ f ∈ keep, ∀ b : Bool, ev (f (Function.update a v b)) p = ev (f a) p) :
    let conj := fun x y => nand (nand x y) (nand x y)
    let slice := fun b => (bucket.map (fun f => f (Function.update a v b))).foldr conj top
    ((∀ f ∈ keep, ev (f a) p = true) ∧
      ev (nand (nand (slice false) (slice false)) (nand (slice true) (slice true))) p = true) ↔
      ∃ b : Bool, ∀ f ∈ keep ++ bucket, ev (f (Function.update a v b)) p = true := by
  sorry
