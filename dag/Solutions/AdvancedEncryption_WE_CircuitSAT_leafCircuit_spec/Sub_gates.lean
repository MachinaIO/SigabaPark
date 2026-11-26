import Definitions.Def_WE_CircuitSAT
import SigabaNeoStd.Machines.GatesSLP
import SigabaNeoStd.Lattices.Homomorphic.Depth

open SigabaNeo SigabaNeo.Lattices AdvancedEncryption.WE.CircuitSAT

theorem solution {n g : ℕ} (hg : 0 < g)
    (φ : AdvancedEncryption.WE.CircuitSAT.Circuit n g) (R : Type) [CommRing R] (W E : ℕ) :
    let P := predOf n φ.gates
    let f := P.1.circuit P.2
    (∀ x : Fin n → Bool, f.eval (fun i ↦ if x i then (1 : R) else 0) =
      if evalGates (List.ofFn x, φ.gates) then 1 else 0) ∧ errBound W E f ≤ (W + 1) ^ g * E := by
  dsimp only
  have hlen : φ.gates.length = g := by simp [Circuit.gates]
  have hne : φ.gates ≠ [] := by intro he; simp [he] at hlen; omega
  constructor
  · intro x
    rw [SLP.eval_circuit, SLP.eval_bits, evalGates_predOf x φ.gates hne]
  · rw [errBound_circuit]
    simpa [predOf, fromGates, hlen] using
      slpBound_le_length W E (predOf n φ.gates).1 (predOf n φ.gates).2
