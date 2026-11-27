import Definitions.Def_FrontierNandCompiler

open FrontierNandCompiler SigabaNeo Turing Turing.MultiTapeTM

theorem solution (v b₀ b₁ r na : Bool) :
    ((na && fuse b₁ r v) ^^ fuse b₀ r (na && v)) = ((na && b₁) ^^ b₀) := by
  decide +revert
