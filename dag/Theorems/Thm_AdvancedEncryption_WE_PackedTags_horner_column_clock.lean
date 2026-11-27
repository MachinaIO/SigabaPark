import SigabaNeoStd.Machines.Prog.Arith
open SigabaNeo.Tape
/-- Registered tape compiler clock for a fixed-width Horner multiply bit. -/
theorem AdvancedEncryption.WE.PackedTags.horner_column_clock (W : ℕ) :
    (Prog.seq (Prog.add (0 : Fin 3) 0)
      (Prog.seq (Prog.ifBit 2 (Prog.add 0 1) (Prog.prim (.copy 0 0)))
          (Prog.prim (.tail 2)))).timeBound W = 3*(2*W+3)+1 := by sorry
