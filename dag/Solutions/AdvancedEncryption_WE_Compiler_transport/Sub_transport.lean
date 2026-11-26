import Definitions.Def_WE

open SigabaNeo AdvancedEncryption.WE

theorem solution
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
    Correct R p source ∧ FalseStatementSecure R p source := by
  constructor
  · intro x w hw b
    have h := correct (compile x) (project x w) (forward x w hw) b
    simpa only [decryptLaw, encEq, funext (decEq x w hw), hcorr] using h
  · intro x hx A
    obtain ⟨B, costB, runB⟩ := simulate x hx A
    have law (b : Bool) :
        B.acceptProb (challenge S q target (compile x) b) =
          A.acceptProb (challenge R p source x b) := by
      simp only [Machine.acceptProb, challenge, PMF.bind_map, encEq]
      have eqf : (B.run ∘ fun ct => encodeTuple [paramsWord S q, S.encStmt (compile x), ct]) =
          (A.run ∘ fun ct => encodeTuple [paramsWord R p, R.encStmt x, ct]) := funext runB
      rw [eqf]
    have h := secure (compile x) (fun hs => hx (reflects x hs)) B
    simp only [Problem.gain, law, hsec, pow_add] at h
    have hc : (B.cost : ℝ) ≤ (2 : ℝ)^k * (A.cost : ℝ) := by exact_mod_cast costB
    apply (le_of_mul_le_mul_left _ (by positivity : (0 : ℝ) < 2^k))
    simpa only [Problem.gain, mul_assoc, mul_left_comm, mul_comm] using h.trans hc
