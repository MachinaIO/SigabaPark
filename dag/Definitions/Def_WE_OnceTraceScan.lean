import Mathlib
import SigabaNeoStd.Machines.Gates
namespace AdvancedEncryption.WE.OnceTrace
def pen (x y z : Bool) : ℕ :=
  match x,y,z with
  | false,false,false => 3
  | false,true,false | true,false,false | true,true,true => 1
  | _,_,_ => 0
def energy (s : List Bool × Bool) : List ((ℕ × ℕ) × Bool) → ℕ
  | [] => if s.2 then 0 else 1
  | ((i,j),z)::rest => pen (s.1.getD i true) (s.1.getD j true) z +
      energy (s.1 ++ [z],z) rest
end AdvancedEncryption.WE.OnceTrace
namespace AdvancedEncryption.WE.OnceScan
def stream {H K : Type*} [Add H] [AddMonoid K] (dot : H → H → K)
    (start : H) : List (H × H × K) → K
  | [] => 0
  | (a,b,c)::tail => c+dot start b+stream dot (start+a) tail
def later {H K : Type*} [AddMonoid H] : List (H × H × K) → H
  | [] => 0
  | (_,b,_)::tail => b+later tail
def pairs {H K : Type*} [AddMonoid H] [AddMonoid K] (dot : H → H → K) :
    List (H × H × K) → K
  | [] => 0
  | (a,_,c)::tail => c+dot a (later tail)+pairs dot tail
end AdvancedEncryption.WE.OnceScan
