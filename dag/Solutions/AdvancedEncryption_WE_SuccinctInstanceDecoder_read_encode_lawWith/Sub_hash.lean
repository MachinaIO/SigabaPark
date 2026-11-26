import Definitions.Def_WE_SuccinctInstanceDecoder

open Turing.MultiTapeTM SigabaNeo SigabaNeo.Lattices
open AdvancedEncryption.WE.Assumptions.SuccinctLWE AdvancedEncryption.WE.SuccinctInstanceDecoder

private theorem unsigned_ok (l : List ℕ) : unsignedEntries (encList encNat l) = l := by
  simp [unsignedEntries, frames_encList, List.map_map, Function.comp_def, ofBits, Nat.foldr_bit_bits]

private theorem signed_ok (z : ℤ) : signed (encIntBin z) = z := by
  cases z <;> simp [signed, ofBits, Nat.foldr_bit_bits]; omega

private theorem mat_ok {r c q : ℕ} [NeZero q] (M : Matrix (Fin r) (Fin c) (ZMod q)) :
    matrix (encList encNat (matVals M)) = M := by
  ext i j
  simp only [matrix, unsigned_ok, List.getElem?_toArray, ← List.getD_eq_getElem?_getD,
    getD_matVals, ZMod.natCast_zmod_val]

private theorem td_ok {r c : ℕ} (T : Option (Matrix (Fin r) (Fin c) ℤ)) :
    trapdoor (encOption (encList (encList encIntBin)) (T.map Trapdoor.cols)) = T := by
  cases T with
  | none => rfl
  | some T =>
    simp only [Option.map_some, encOption_some, trapdoor, frames_encList, Trapdoor.cols,
      List.map_ofFn]
    congr 1
    funext i j
    simp [frames_encList, List.map_ofFn, -encIntBin_apply, signed_ok]

private theorem roundtrip (p : Params) (x : Instance p) : read p (encode p x) = x := by
  obtain ⟨B,b,W,T⟩ := x
  simp only [encode, AdvancedEncryption.WE.SuccinctInstanceDecoder.read, encodeTuple, frames_encList, List.map_cons, List.map_nil, encBits_apply,
    List.getD_cons_zero, List.getD_cons_succ, unsigned_ok, mat_ok, td_ok]
  congr 2
  funext j
  simp

open Cslib.Probability

theorem solution (p : Params) :
    (∀ x : Instance p, read p (encode p x) = x) ∧
    (∀ {V : Type} (second : Matrix (Fin p.n) (Fin p.m) (ZMod p.q) → PMF (Fin p.m → ZMod p.q))
      (K : Instance p → PMF V),
      (lawWith p second).bind (fun w ↦ K (read p w)) =
        (do
          let B ← PMF.uniformOfFintype (Matrix (Fin p.n) (Fin p.m) (ZMod p.q))
          let b ← second B
          let W ← PMF.uniformOfFintype (Matrix (Fin (p.ℓ * p.n)) (Fin p.m) (ZMod p.q))
          let T ← trapdoorLaw p B W
          K (B, b, W, T))) := by
  refine ⟨roundtrip p, ?_⟩
  intro V second K
  simp only [lawWith, bind, pure, PMF.bind_bind, PMF.pure_bind, roundtrip]
