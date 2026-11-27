import SigabaNeo.Trusted.Machine

open Turing

theorem AdvancedEncryption.WE.Compiler.header_input_symbol {k l : ℕ} {Q Q' : Type} (src dst z : List Bool)
    (c : Cfg k Bool Q (src ++ z)) (e : Cfg l Bool Q' (dst ++ z))
    (hp : e.inputPos.val = dst.length + 1 + (c.inputPos.val - (src.length+1))) :
    let i := min c.inputPos.val (src.length+1)
    (if i = src.length+1 then e.inputSymbol else if i=0 then none else src[i-1]?) =
      c.inputSymbol := by sorry
