import Definitions.Def_OwnedGarbling

open OwnedGarbling
open scoped BigOperators

theorem AdvancedEncryption.WE.OwnedGarbling.selector_word :
    (∀ sel color p0 p1 q0 q1 a b : Bool,
      let dp := p0 ^^ p1
      let dq := q0 ^^ q1
      let c := color && !(dp ^^ dq)
      let h := if sel then dq ^^ c else dp
      (((if a then p1 else p0) ^^ (if b then q1 else q0)) ^^ (b && c) ^^ ((a ^^ b) && h)) =
        (p0 ^^ q0 ^^ ((if sel then a else b) && (if color then true else dp ^^ dq)))) ∧
    (∀ sel : Bool,
      Function.Bijective (fun p : Bool × Bool ↦ ((if sel then p.2 else p.1), p.1 ^^ p.2)) ∧
      Function.Bijective (fun p : Bool × Bool ↦ ((if sel then !p.1 else p.1), !(p.1 ^^ p.2)))) := by sorry
