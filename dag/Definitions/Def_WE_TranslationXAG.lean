import Mathlib
namespace AdvancedEncryption.WE.TranslationXAG
structure Form (ι : Type) where
  bias : Bool
  raw : List ι
  atoms : List ℕ

def parity {ι : Type} (xs : List ι) (x : ι → Bool) : Bool :=
  xs.foldr (fun i b => x i ^^ b) false

def value {ι : Type} (f : Form ι) (x : ι → Bool) (v : List Bool) : Bool :=
  f.bias ^^ parity f.raw x ^^ parity f.atoms (fun j => v.getD j false)

def run {ι : Type} (x : ι → Bool) (init : List Bool) (gates : List (Form ι × Form ι)) :
    List Bool := gates.foldl (fun v ab => v ++ [value ab.1 x v && value ab.2 x v]) init
end AdvancedEncryption.WE.TranslationXAG
