import Definitions.Def_WE

open SigabaNeo AdvancedEncryption.WE

theorem AdvancedEncryption.WE.Compiler.transport
    (R S : Relation) (p q : Params) (source target : Impl sig)
    (compile : R.Stmt → S.Stmt) (project : R.Stmt → R.Wit → S.Wit)
    (k : ℕ) (hsec : q.secBits = p.secBits + k) (hcorr : q.corrBits = p.corrBits)
    (forward : ∀ x w, R.rel x w → S.rel (compile x) (project x w))
    (reflects : ∀ x, S.InL (compile x) → R.InL x)
    (encEq : ∀ x b, enc p source x b = enc q target (compile x) b)
    (decEq : ∀ x w, R.rel x w → ∀ ct, dec p source x w ct = dec q target (compile x) (project x w) ct)
    (simulate : ∀ x, ¬ R.InL x → ∀ A : Machine, ∃ B : Machine,
      B.cost ≤ 2 ^ k * A.cost ∧ ∀ ct : List Bool,
        B.run (encodeTuple [paramsWord S q, S.encStmt (compile x), ct]) =
          A.run (encodeTuple [paramsWord R p, R.encStmt x, ct]))
    (correct : Correct S q target) (secure : FalseStatementSecure S q target) :
    Correct R p source ∧ FalseStatementSecure R p source := by sorry
