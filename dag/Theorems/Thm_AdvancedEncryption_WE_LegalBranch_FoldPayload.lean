import Mathlib

theorem AdvancedEncryption.WE.LegalBranch.FoldPayload (m base r out : Bool) :
    (m ^^ base) ^^ (base ^^ r) ^^ (out && r) = m ^^ ((!out) && r) := by sorry
