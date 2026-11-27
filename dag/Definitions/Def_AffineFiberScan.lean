import SigabaNeoStd.Machines.Gates

namespace AdvancedEncryption.WE.AffineFiberScan

/-- Abstract data per wire and the concrete assignments allowed for each output bit. -/
structure Domain (W D : Type) where
  holds : D → Bool → W → Prop
  one : D
  one_true : ∀ w, holds one true w
  transfer : D → D → D
  transfer_sound : ∀ a b x y w, holds a x w → holds b y w →
    holds (transfer a b) (!(x && y)) w

/-- Concrete and abstract states use identical forward-reference behavior. -/
def advance {W D : Type} (d : Domain W D) (s : List D × D)
    (g : Nat × Nat) : List D × D :=
  let v := d.transfer (s.1.getD g.1 d.one) (s.1.getD g.2 d.one)
  (s.1 ++ [v], v)

/-- A predicate for both truth fibers, with a user-supplied sound binary hull. -/
def nandFiber {W : Type} (hull : (W → Prop) → (W → Prop) → W → Prop)
    (a b : Bool → W → Prop) : Bool → W → Prop
  | false => fun w => a true w ∧ b true w
  | true => hull (a false) (b false)

end AdvancedEncryption.WE.AffineFiberScan
