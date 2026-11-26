import Definitions.Def_FixedHeaderTrace
import Theorems.Thm_AdvancedEncryption_WE_Compiler_header_input_symbol

open SigabaNeo SigabaNeo.Machine SigabaNeo.Machine.Header Turing Turing.MultiTapeMachine
open AdvancedEncryption.WE.Compiler

set_option maxHeartbeats 1500000 in
set_option backward.isDefEq.respectTransparency false in
theorem AdvancedEncryption.WE.Compiler.header_tick (A : Machine) (src dst z : List Bool) (c : ConfigOf A (src++z)) (coin : Bool) :
    tick (A.fixedHeaderMachine src dst.length) (embed A src dst z c) coin =
      embed A src dst z (tick A c coin) := by sorry
