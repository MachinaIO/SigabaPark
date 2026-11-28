import Definitions.Def_WE_CBDWirePad
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size

open Turing.MultiTapeTM Cslib.Crypto
open AdvancedEncryption.WE.CBDWirePad

theorem solution (n : ℕ)
    (μ : PMF (Matrix (Fin 1) (Fin 1) (Fin (n+1) → ZMod 256) × (Fin 1 → Fin (n+1) → ZMod 256))) :
    (μ.map ModuleLWE.encodeSample).map (boundedConvert (n+1)) =
      μ.map (fun ab =>
        ((List.ofFn fun i : Fin (1*(n+1)) => fixed8 ((expandModuleMatrix ab.1 i 0).val.bits)).flatten,
         (List.ofFn fun i : Fin (1*(n+1)) => fixed8 ((flattenPolyVec ab.2 i).val.bits)).flatten)) := by
  have codec (n : ℕ) (A : Matrix (Fin 1) (Fin 1) (Fin (n+1) → ZMod 256))
      (b : Fin 1 → Fin (n+1) → ZMod 256) :
      convert (ModuleLWE.encodeSample (A,b)) =
        ((List.ofFn fun i : Fin (1*(n+1)) => fixed8 ((expandModuleMatrix A i 0).val.bits)).flatten,
         (List.ofFn fun i : Fin (1*(n+1)) => fixed8 ((flattenPolyVec b i).val.bits)).flatten) := by
    rw [convert, ModuleLWE.encodeSample]
    simp only [encPair_apply, encBits_apply, unframe_frame_append, dropFrame_frame_append,
      ModuleSIS.encodeMatrix, SIS.encodeMatrix, frames_encList, List.map_ofFn]
    apply Prod.ext
    · simp only [List.flatMap, List.map_ofFn]
      congr 1
      apply congrArg List.ofFn
      funext i
      simp only [Function.comp_apply, List.ofFn_succ, encList_cons, unframe_frame_append, encNat_apply]
    · simp only [List.flatMap, List.map_ofFn]
      rfl
  have bound (N : ℕ) (A : Matrix (Fin 1) (Fin 1) (Fin N → ZMod 256))
      (b : Fin 1 → Fin N → ZMod 256) :
      (ModuleLWE.encodeSample (A,b)).length ≤ 68*N*N + 19*N + 1 := by
    have row {k : ℕ} (f : Fin k → ZMod 256) :
        (encList encNat (List.ofFn fun j => (f j).val)).length ≤ k*17 := by
      have h := length_encList_le encNat (List.ofFn fun j => (f j).val) (b:=8) (by
        intro a ha
        obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
        rw [encNat_apply, Nat.size_eq_bits_len]
        exact Nat.size_le.mpr (ZMod.val_lt (f j)))
      simpa only [List.length_ofFn] using h
    have mat : (ModuleSIS.encodeMatrix A).length ≤ (1*N)*(2*((1*N)*17)+1) := by
      unfold ModuleSIS.encodeMatrix SIS.encodeMatrix
      apply le_trans (length_encList_le (encList encNat) _ (b:=(1*N)*17) ?_)
      · simp
      · intro l hl
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hl
        exact row _
    rw [ModuleLWE.encodeSample, length_encPair]
    simp only [encBits_apply]
    have resp := row (flattenPolyVec b)
    simp only [Nat.one_mul] at mat
    nlinarith [Nat.one_mul N]

  have packetLength {n : ℕ} (f : Fin n → List Bool) :
      (List.ofFn fun i => fixed8 (f i)).flatten.length = 8*n := by
    rw [List.length_flatten, List.map_ofFn]
    change (List.ofFn fun i : Fin n => (fixed8 (f i)).length).sum = _
    simp [fixed8, List.ofFn_const, Nat.mul_comm]

  have clipped (n : ℕ) (A : Matrix (Fin 1) (Fin 1) (Fin (n+1) → ZMod 256))
      (b : Fin 1 → Fin (n+1) → ZMod 256) :
    boundedConvert (n+1) (ModuleLWE.encodeSample (A,b)) = convert (ModuleLWE.encodeSample (A,b)) := by
    unfold boundedConvert
    rw [List.take_of_length_le (bound (n+1) A b), codec]
    apply Prod.ext <;> apply List.take_of_length_le <;> rw [packetLength, Nat.one_mul]
  rw [_root_.PMF.map_comp]
  apply congrArg (fun f => _root_.PMF.map f μ)
  funext ab
  exact (clipped n ab.1 ab.2).trans (codec n ab.1 ab.2)
