import Definitions.Def_WE_CircuitSAT_Impl_BruteForce

/-!
The brute-force submission is correct and false-statement secure with no premises, and its cost
is `N` by definition.
-/

open AdvancedEncryption AdvancedEncryption.WE AdvancedEncryption.WE.CircuitSAT
  AdvancedEncryption.WE.CircuitSAT.BruteForce SigabaNeo

namespace BruteForceProof

theorem encMachine_run (a : Circuit inputs size × Bool) :
    encMachine.run (encodeTuple (encIn a)) = PMF.pure (encodeTuple [ctOf a]) :=
  exists_encMachine.choose_spec.2 a

theorem decMachine_run (a : Circuit inputs size × (Fin inputs → Bool) × Bool) :
    decMachine.run (encodeTuple (decIn a)) = PMF.pure (encodeTuple [encBit a.2.2]) :=
  exists_decMachine.choose_spec.2 a

theorem impl_enc : impl.machine Alg.enc = encMachine := by
  simp [impl]

theorem impl_dec : impl.machine Alg.dec = decMachine := by
  simp [impl, Alg.enc, Alg.dec]

theorem enc_eq (φ : Rel.Stmt) (β : Bool) :
    WE.enc (R := Rel) params impl φ β = PMF.pure (ctOf (φ, β)) := by
  show (((impl.machine Alg.enc).run (encodeTuple (paramsWord Rel params ::
    [encCircuit inputs size φ, encBit β]))).map _).map _ = _
  rw [impl_enc]
  change ((encMachine.run (encodeTuple (encIn (φ, β)))).map (decodeTuple 1)).map _ = _
  rw [encMachine_run, PMF.pure_map, PMF.pure_map]
  rw [show (1 : ℕ) = [ctOf (φ, β)].length from rfl, decodeTuple_encodeTuple]
  rfl

theorem dec_eq (φ : Circuit inputs size) (w : Fin inputs → Bool) (b : Bool) :
    WE.dec (R := Rel) params impl φ w (encBit b) = PMF.pure (encBit b) := by
  show (((impl.machine Alg.dec).run (encodeTuple (paramsWord Rel params ::
    [encCircuit inputs size φ, encAssignment inputs w, encBit b]))).map _).map _ = _
  rw [impl_dec]
  change ((decMachine.run (encodeTuple (decIn (φ, w, b)))).map (decodeTuple 1)).map _ = _
  rw [decMachine_run, PMF.pure_map, PMF.pure_map]
  rw [show (1 : ℕ) = [encBit (φ, w, b).2.2].length from rfl, decodeTuple_encodeTuple]
  rfl

theorem enc_of_inL (φ : Rel.Stmt) (hL : Rel.InL φ) (β : Bool) :
    WE.enc (R := Rel) params impl φ β = PMF.pure (encBit β) := by
  rw [enc_eq]; simp [ctOf, hL]

theorem enc_of_not_inL (φ : Rel.Stmt) (hL : ¬ Rel.InL φ) (β : Bool) :
    WE.enc (R := Rel) params impl φ β = PMF.pure (encBit false) := by
  rw [enc_eq]; simp [ctOf, hL]

theorem dec_eq' (φ : Rel.Stmt) (w : Rel.Wit) (b : Bool) :
    WE.dec (R := Rel) params impl φ w (encBit b) = PMF.pure (encBit b) :=
  dec_eq φ w b

theorem correct : WE.Correct Rel params impl := by
  intro φ w hw β
  unfold WE.decryptLaw
  rw [enc_of_inL φ ⟨w, hw⟩ β, PMF.pure_bind, dec_eq', PMF.pure_apply_self, ENNReal.toReal_one]
  have : (0 : ℝ) ≤ ((2 : ℝ) ^ params.corrBits)⁻¹ := by positivity
  linarith

theorem falseStatementSecure : WE.FalseStatementSecure Rel params impl := by
  intro φ hφ A
  have h : WE.challenge Rel params impl φ false = WE.challenge Rel params impl φ true := by
    unfold WE.challenge
    rw [enc_of_not_inL φ hφ, enc_of_not_inL φ hφ]
  rw [h]
  simp only [Problem.gain, sub_self]
  simp

end BruteForceProof

open BruteForceProof in
theorem solution : AdvancedEncryption.WE.CircuitSAT.SubmissionProp AdvancedEncryption.WE.CircuitSAT.BruteForce.u := by
  refine ⟨fun (i : Fin 2) _ => ?_, le_refl _⟩
  fin_cases i
  · exact correct
  · exact falseStatementSecure
