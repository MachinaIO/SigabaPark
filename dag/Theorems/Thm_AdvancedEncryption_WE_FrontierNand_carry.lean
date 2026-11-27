import Definitions.Def_FrontierNandCompiler

open FrontierNandCompiler SigabaNeo Turing Turing.MultiTapeTM

theorem AdvancedEncryption.WE.FrontierNand.carry (u v b₀ b₁ r na : Bool) :
    fuse (b₁ ^^ v) (!r) v = fuse b₁ r v ∧
    fuse (b₀ ^^ u) (!r) (na && v) = (fuse b₀ r (na && v) ^^ (u ^^ (na && v))) := by sorry
