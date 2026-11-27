import Mathlib.Tactic.Abel

theorem AdvancedEncryption.WE.BranchTags.nand_rectangle_quotient
    {G : Type*} [AddCommGroup G] (a b : Bool → Bool → G) :
    (∃ r c : Bool → G, ∀ i j, a i j = b i j + r i + c j) ↔
      a false false - a false true - a true false + a true true =
      b false false - b false true - b true false + b true true := by sorry
