import SigabaNeoStd.Lattices.Homomorphic.Depth

open SigabaNeo.Lattices

theorem step_bound (WN E la lb da db Ba Bb : ℕ)
    (ha : Ba ≤ (WN + 1) ^ la * (da + 1) ^ (la + 1) * E)
    (hb : Bb ≤ (WN + 1) ^ lb * (db + 1) ^ (lb + 1) * E) :
    WN * Ba + Bb ≤ (WN + 1) ^ max (la + 1) lb * (max da db + 1 + 1) ^ (max (la + 1) lb + 1) * E := by
  set l := max (la + 1) lb with hl
  set D := max da db + 1 with hD
  have hD1 : 1 ≤ D := by omega
  have hla : la + 1 ≤ l := le_max_left _ _
  have hlb : lb ≤ l := le_max_right _ _
  have hda : da + 1 ≤ D := by omega
  have hdb : db + 1 ≤ D := by omega
  have hW : WN * (WN + 1) ^ la ≤ (WN + 1) ^ l :=
    calc WN * (WN + 1) ^ la ≤ (WN + 1) * (WN + 1) ^ la := Nat.mul_le_mul_right _ (by omega)
      _ = (WN + 1) ^ (la + 1) := by ring
      _ ≤ (WN + 1) ^ l := Nat.pow_le_pow_right (by omega) hla
  have hA : WN * Ba ≤ (WN + 1) ^ l * D ^ l * E :=
    calc WN * Ba ≤ WN * ((WN + 1) ^ la * (da + 1) ^ (la + 1) * E) := Nat.mul_le_mul_left _ ha
      _ = (WN * (WN + 1) ^ la) * (da + 1) ^ (la + 1) * E := by ring
      _ ≤ (WN + 1) ^ l * D ^ l * E := by
          apply Nat.mul_le_mul_right
          apply Nat.mul_le_mul hW
          calc (da + 1) ^ (la + 1) ≤ D ^ (la + 1) := Nat.pow_le_pow_left hda _
            _ ≤ D ^ l := Nat.pow_le_pow_right hD1 hla
  have hB : Bb ≤ (WN + 1) ^ l * D ^ (l + 1) * E :=
    calc Bb ≤ (WN + 1) ^ lb * (db + 1) ^ (lb + 1) * E := hb
      _ ≤ (WN + 1) ^ l * D ^ (l + 1) * E := by
          apply Nat.mul_le_mul_right
          apply Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) hlb)
          calc (db + 1) ^ (lb + 1) ≤ D ^ (lb + 1) := Nat.pow_le_pow_left hdb _
            _ ≤ D ^ (l + 1) := Nat.pow_le_pow_right hD1 (by omega)
  calc WN * Ba + Bb ≤ (WN + 1) ^ l * D ^ l * E + (WN + 1) ^ l * D ^ (l + 1) * E :=
        Nat.add_le_add hA hB
    _ = (WN + 1) ^ l * (D ^ l * (D + 1)) * E := by ring
    _ ≤ (WN + 1) ^ l * ((D + 1) ^ l * (D + 1)) * E := by
        apply Nat.mul_le_mul_right
        apply Nat.mul_le_mul_left
        exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) _)
    _ = (WN + 1) ^ l * (D + 1) ^ (l + 1) * E := by ring

/-- **Noise is exponential only in the asymmetric level.** -/
theorem solution {ι : Type*} (WN E : ℕ) (p : SLP ι) (w : Wire ι) :
    slpBound WN E p w ≤
      (WN + 1) ^ SLP.valueOf (fun _ => 0) 0 (fun a b => max (a + 1) b) p w *
        (SLP.depth p w + 1) ^ (SLP.valueOf (fun _ => 0) 0 (fun a b => max (a + 1) b) p w + 1) *
          E := by
  let step : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ → ℕ × ℕ × ℕ :=
    fun a b => (WN * a.1 + b.1, max (a.2.1 + 1) b.2.1, max a.2.2 b.2.2 + 1)
  have h1 : (SLP.valueOf (fun _ => (E, 0, 0)) (0, 0, 0) step p w).1 = slpBound WN E p w :=
    SLP.valueOf_map _ _ _ _ _ _ Prod.fst (fun _ => rfl) rfl (fun _ _ => rfl) p w
  have h2 : (SLP.valueOf (fun _ => (E, 0, 0)) (0, 0, 0) step p w).2.1 =
      SLP.valueOf (fun _ => 0) 0 (fun a b => max (a + 1) b) p w :=
    SLP.valueOf_map _ _ _ _ _ _ (fun u : ℕ × ℕ × ℕ => u.2.1) (fun _ => rfl) rfl (fun _ _ => rfl) p w
  have h3 : (SLP.valueOf (fun _ => (E, 0, 0)) (0, 0, 0) step p w).2.2 = SLP.depth p w :=
    SLP.valueOf_map _ _ _ _ _ _ (fun u : ℕ × ℕ × ℕ => u.2.2) (fun _ => rfl) rfl (fun _ _ => rfl) p w
  have hinv := SLP.valueOf_invariant (fun _ : ι => (E, 0, 0)) (0, 0, 0) step
    (fun u => u.1 ≤ (WN + 1) ^ u.2.1 * (u.2.2 + 1) ^ (u.2.1 + 1) * E)
    (fun _ => by simp) (by simp)
    (fun a b ha hb => step_bound WN E a.2.1 b.2.1 a.2.2 b.2.2 a.1 b.1 ha hb) p w
  rw [← h1, ← h2, ← h3]
  exact hinv
