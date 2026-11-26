import Definitions.Def_SuccinctLWE
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Words

namespace AdvancedEncryption.WE.SuccinctInstanceDecoder

open Turing.MultiTapeTM AdvancedEncryption.WE.Assumptions.SuccinctLWE

/-- Read a sign-magnitude entry, with the least significant magnitude bit first. -/
def signed (w : List Bool) : ℤ :=
  if w.headD false then -(ofBits w.tail : ℤ) else (ofBits w.tail : ℤ)

/-- Read framed natural-number entries. -/
def unsignedEntries (w : List Bool) : List ℕ := (frames w).map ofBits

/-- Recover a modular matrix from the row-major entries. -/
def matrix {r c q : ℕ} (w : List Bool) : Matrix (Fin r) (Fin c) (ZMod q) :=
  let vals := (unsignedEntries w).toArray
  fun i j ↦ (vals[i.val * c + j.val]?.getD 0 : ℕ)

/-- The trapdoor encoding frames columns, with signed entries inside each column. -/
def trapdoor {r c : ℕ} (w : List Bool) : Option (Matrix (Fin r) (Fin c) ℤ) :=
  match w with
  | [] => none
  | _ :: ws =>
    let cols := ((frames ws).map fun col ↦ ((frames col).map signed).toArray).toArray
    some fun i j ↦ ((cols[j.val]?.getD #[])[i.val]?).getD 0

/-- Total readout for the registered instance. Correctness is required on encoded samples.
Missing fields or entries have defaults so this function is defined on every input word. -/
def read (p : Params) (w : List Bool) : Instance p :=
  let parts := frames w
  let b := (unsignedEntries (parts.getD 1 [])).toArray
  (matrix (parts.getD 0 []), fun j ↦ (b[j.val]?.getD 0 : ℕ),
    matrix (parts.getD 2 []), trapdoor (parts.getD 3 []))

end AdvancedEncryption.WE.SuccinctInstanceDecoder
