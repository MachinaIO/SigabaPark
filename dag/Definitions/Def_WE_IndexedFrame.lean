import Mathlib
namespace AdvancedEncryption.WE.IndexedFrame
structure Tape (U V W : Type*) where
  act : U
  other : U
  mask : V
  left : W
  right : W
  selected : W
  opposite : W
end AdvancedEncryption.WE.IndexedFrame
