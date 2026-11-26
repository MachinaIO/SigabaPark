import Definitions.Def_FixedHeaderMachine
import Mathlib.Data.Nat.Size

open SigabaNeo SigabaNeo.Machine

theorem AdvancedEncryption.WE.Compiler.fixed_header_cost (A : Machine) (src : List Bool) (skip : ℕ)
    (bound : src.length + skip + 3 ≤ 2^29) :
    (fixedHeaderMachine A src skip).cost ≤ 2^34 * A.cost := by sorry
