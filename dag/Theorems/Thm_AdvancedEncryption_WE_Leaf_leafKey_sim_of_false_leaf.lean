import SigabaNeoStd.Lattices.BoxSampler
import SigabaNeoStd.Lattices.RingBoxes
import SigabaNeoStd.Lattices.SimNorm
import SigabaNeoStd.Lattices.Homomorphic.Eval

open Matrix SigabaNeo.Lattices Cslib
open scoped ENNReal

/-- **The leaf lemma (C1), statistical half: exact simulation of the leaf key.**
Over `ℤ_q[X]/(X^N + 1)`, with the ℓ-succinct LWE block identity
`B T_B[i,j] + W_i T_W[j] = δ_{ij} G`, a bit attribute `w`, `A := Σ_i w_i W_i + B R`, attribute
keys `A_j := A T_W[j]` and their trapdoors `R T_W[j] − Σ_i w_i T_B[i,j]` of entries at most `E`:
for every NAND circuit `φ` with `φ(w) = 0`, the leaf key of `[B | A_φ − G]` sampled with a gadget
trapdoor `Tm` of `B` (`B Tm = G`, entries at most `E_T`) has **the same law** as the one sampled
with `R_φ := EvalSim(φ, …)`, which uses no trapdoor of `B` — provided the small box `famBall s`
plus `k N errBound(k N, E, φ)` and plus `(k N)² E_T` stays in the big box of `Bb` bits. -/
theorem AdvancedEncryption.WE.Leaf.leafKey_sim_of_false_leaf {q N ℓ n m mW k : ℕ} [NeZero q]
    (Γ : GadgetMatrix (Negacyclic (ZMod q) N) (Fin n) (Fin k))
    (hΓ : ∀ A c c', cnorm (Γ.ginv A c c') ≤ 1)
    (dec : (Fin n → Negacyclic (ZMod q) N) → (Fin k → Negacyclic (ZMod q) N))
    (hdec : ∀ y, Γ.G *ᵥ dec y = y) (hdecN : ∀ y c, cnorm (dec y c) ≤ 1)
    (B : Matrix (Fin n) (Fin m) (Negacyclic (ZMod q) N))
    (W : Fin ℓ → Matrix (Fin n) (Fin mW) (Negacyclic (ZMod q) N))
    (TB : Fin ℓ → Fin ℓ → Matrix (Fin m) (Fin k) (Negacyclic (ZMod q) N))
    (TW : Fin ℓ → Matrix (Fin mW) (Fin k) (Negacyclic (ZMod q) N))
    (h : ∀ i j, B * TB i j + W i * TW j = if i = j then Γ.G else 0)
    (w : Fin ℓ → Negacyclic (ZMod q) N) (hw : ∀ i, w i = 0 ∨ w i = 1)
    (R : Matrix (Fin m) (Fin mW) (Negacyclic (ZMod q) N)) (E : ℕ)
    (hE : ∀ j a c, cnorm ((R * TW j - ∑ i, w i • TB i j) a c) ≤ E)
    (φ : Circuit (Fin ℓ)) (hφ : φ.eval w = 0)
    (Tm : Matrix (Fin m) (Fin k) (Negacyclic (ZMod q) N)) (hTm : B * Tm = Γ.G) (ET : ℕ)
    (hET : ∀ a j, cnorm (Tm a j) ≤ ET)
    (Bb s : ℕ) (hB : 2 ^ Bb ≤ q) (hB1 : 1 ≤ Bb)
    (hsR : s + k * N * errBound (k * N) E φ ≤ 2 ^ (Bb - 1) - 1)
    (hsT : s + k * N * (k * N * ET) ≤ 2 ^ (Bb - 1) - 1)
    (u : Fin n → Negacyclic (ZMod q) N) :
    boxSample (famBig q N (Fin m) Bb hB) (famBig_nonempty Bb hB) (famBall q N (Fin m) s)
        (Matrix.mulVecLin B).toAddMonoidHom (fun y => dec (-y))
        (fun z => (Tm * Γ.ginv (evalMat Γ (fun j => ((∑ i, w i • W i) + B * R) * TW j) φ)) *ᵥ z)
        u =
      boxSample (famBig q N (Fin m) Bb hB) (famBig_nonempty Bb hB) (famBall q N (Fin m) s)
        (Matrix.mulVecLin B).toAddMonoidHom (fun y => dec (-y))
        (fun z => evalSim Γ (fun j => ((∑ i, w i • W i) + B * R) * TW j) w
          (fun j => R * TW j - ∑ i, w i • TB i j) φ *ᵥ z) u := by sorry
