import Mathlib

theorem AdvancedEncryption.WE.LegalBranch.LeafLine (a b t : Bool) :
    (a ^^ (t && (a ^^ b))) = (if t then b else a) := by sorry
