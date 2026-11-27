import Mathlib.Data.Bool.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Defs
import Mathlib

theorem solution {V P D : Type} [DecidableEq V]
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
  dsimp only
  have fold (xs : List ((V → Bool) → D)) (b : Bool) :
      ev ((xs.map (fun f => f (Function.update a v b))).foldr
        (fun x y => nand (nand x y) (nand x y)) top) p = true ↔
      ∀ f ∈ xs, ev (f (Function.update a v b)) p = true := by
    induction xs with
    | nil => simp [ht]
    | cons x xs ih => simp [hn, ih]
  simp only [hn, Bool.and_self, Bool.not_and, Bool.not_not, Bool.or_eq_true, fold]
  constructor
  · rintro ⟨hk, hb | hb⟩
    · exact ⟨false, fun f hf => (List.mem_append.mp hf).elim
        (fun h => (absent f h false).trans (hk f h)) (hb f)⟩
    · exact ⟨true, fun f hf => (List.mem_append.mp hf).elim
        (fun h => (absent f h true).trans (hk f h)) (hb f)⟩
  · rintro ⟨b,h⟩
    refine ⟨fun f hf => (absent f hf b).symm.trans (h f (List.mem_append_left _ hf)), ?_⟩
    cases b with
    | false => exact Or.inl (fun f hf => h f (List.mem_append_right _ hf))
    | true => exact Or.inr (fun f hf => h f (List.mem_append_right _ hf))
