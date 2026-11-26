import SigabaNeoStd.Lattices.Homomorphic.Depth

open SigabaNeo.Lattices

theorem AdvancedEncryption.WE.Noise.slpBound_le_alevel {ι : Type*} (WN E : ℕ) (p : SLP ι)
    (w : Wire ι) :
    slpBound WN E p w ≤
      (WN + 1) ^ SLP.valueOf (fun _ => 0) 0 (fun a b => max (a + 1) b) p w *
        (SLP.depth p w + 1) ^ (SLP.valueOf (fun _ => 0) 0 (fun a b => max (a + 1) b) p w + 1) *
          E := by sorry
