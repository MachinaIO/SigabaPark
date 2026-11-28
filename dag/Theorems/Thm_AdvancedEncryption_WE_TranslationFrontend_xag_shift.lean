import Definitions.Def_WE_TranslationXAG
open AdvancedEncryption.WE.TranslationXAG
/-- Live AND input parity equations certify a constant derivative of an XOR-AND circuit. -/
theorem AdvancedEncryption.WE.TranslationFrontend.xag_shift {ι : Type} (t x : ι → Bool) (gates : List (Form ι × Form ι))
    (zero : ∀ ab ∈ gates, parity ab.1.raw t=false ∧ parity ab.2.raw t=false)
    (f : Form ι) (init : List Bool) :
    value f (fun i => x i ^^ t i) (run (fun i => x i ^^ t i) init gates) =
      (value f x (run x init gates) ^^ parity f.raw t) := by sorry
