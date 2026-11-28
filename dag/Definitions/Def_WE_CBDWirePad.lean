import SigabaNeoStd.Lattices.RingLWE
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
open Turing.MultiTapeTM Cslib.Crypto
namespace AdvancedEncryption.WE.CBDWirePad

/-- Eight low-order bits, preserving zero digits at the high end. -/
def fixed8 (w : List Bool) : List Bool := (List.range 8).map fun j => w.getD j false
/-- Unframe the matrix rows and take their first coefficients, then decode the response. -/
def convert (w : List Bool) : List Bool × List Bool :=
  ((frames (unframe w)).flatMap fun row => fixed8 (unframe row),
    (frames (dropFrame w)).flatMap fixed8)

/-- Cap input traversal and output widths even on malformed words. -/
def boundedConvert (N : ℕ) (w : List Bool) : List Bool × List Bool :=
  let ab := convert (w.take (68*N*N+19*N+1))
  (ab.1.take (8*N), ab.2.take (8*N))

/-- CBD(1) from two independent fair bits. -/
def noise (a b : Bool) : ZMod 256 := (if a then 1 else 0) - (if b then 1 else 0)
def gen {N : ℕ} (a : Fin N → ZMod 256) (key : Fin N → Bool × Bool × Bool × Bool) : List Bool :=
  let s : Fin 1 → Fin N → ZMod 256 := fun _ i => noise (key i).1 (key i).2.1
  let e : Fin 1 → Fin N → ZMod 256 := fun _ i => noise (key i).2.2.1 (key i).2.2.2
  let b := ModuleLWE.sample (fun (_ : Fin 1) (_ : Fin 1) => a) s e
  (List.ofFn fun i : Fin N => fixed8 ((b 0 i).val.bits)).flatten

end AdvancedEncryption.WE.CBDWirePad
