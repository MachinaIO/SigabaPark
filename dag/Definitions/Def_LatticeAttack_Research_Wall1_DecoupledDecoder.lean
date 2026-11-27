module

public import Definitions.Def_LatticeAttack_Research_Wall1_RestartLift
import all Definitions.Def_LatticeAttack_Research_Wall1_RestartLift
import all Definitions.Def_LatticeAttack_Research_Wall1_RestartReduction
import all Definitions.Def_LatticeAttack_Research_Wall1_BabaiLift
import all Definitions.Def_LatticeAttack_Research_Wall1_PlantBlindRestart
import Mathlib.Tactic

set_option autoImplicit true

/-! # The concrete decoder of the decoupled attack (PROOF_GAP Wall 1, Part 47)

`RestartLift.restartReduction_lwe_babai` bounds the probability of the *named* failure event
`decodeFail = ¬ Unique ∨ liftFail`. Two statements of Part 47 were left informal there:
the reducer's prefix spans `W ∩ L`, and success of the named events recovers the secret. This file
proves both and restates the restart bound for a concrete decoder.

Geometry. `E = ℝ^{N+1}` (horizontal coordinates and height). The decoupled lattice is
`L = L₀ ⊕ ℤu` (`decoupled`), with `L₀` the plant-free null lattice and `u = (X, 1)` the plant.
The prefix is `b₀, …, b_{J-1}`; `W` is its real span (`prefixSpan`), `K` its integer span
(`prefixLattice`) and `P` the orthogonal projection onto `Wᗮ` (`perpProj`).

1. **Fibers are prefix cosets** (`fiber_subset_coset`, `fiber_eq_coset`). If `L ∩ W ⊆ K` (the
   prefix generates the primitive sublattice `L ∩ W`, which is what a basis-reduction algorithm
   produces), then every `v ∈ L` with `P v = P u` is `u + Σ_{m<J} cₘ bₘ` with `cₘ ∈ ℤ`. With
   `L ∩ W = K` the fiber is exactly that coset.
2. **Decoder correctness** (`decode_eq`). The decoder (`decode`): exact SVP on `P L` (any oracle
   returning a shortest nonzero vector), orient to height `1`, take any lift in `L`, run Babai on
   the prefix. If the projected plant is the all-heights unique shortest pair (`Unique`) and the
   lift does not fail (`¬ LiftFail`), the output is `u`, so its coordinates are the secret.
   The block hypotheses (`Compatible`) are plant-free: `L₀ ∩ W ⊆ K`,
   `P` acts as the final-block projector `Q` on horizontal coordinates and fixes the height, and
   `P L₀` lies in the final-block horizontal lattice `H`.
3. **End-to-end** (`restartDecoder`, `restartDecoder_lwe`). For the restart algorithm running this
   decoder on the first accepted block,
   `Pr[output ≠ secret] ≤ ∏ δᵢ + ε + Σ_{m<J} 2 exp(−gₘ²/12)`.

Canonical oracles `chooseSVP` and `chooseLift` (choice functions) satisfy the oracle
specifications, so the decoder is a fixed (noncomputable) function of the public data `L`, the
prefix and `J`; the plant enters only through `L`. -/

public section

namespace SigabaNeo.Wall1.DecoupledDecoder

open SigabaNeo.Wall1 SigabaNeo.Wall1.MultiBlock SigabaNeo.Wall1.PlantBlindRestart
open SigabaNeo.Wall1.RestartReduction SigabaNeo.Wall1.RestartLift SigabaNeo.Wall1.BabaiLift
open SampleDeletion CBDTail Classical InnerProductSpace

/-! ## 1. Fibers of the projection are prefix cosets -/

section Fiber

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `W`: the real span of the prefix `b₀, …, b_{J-1}`. -/
@[expose] noncomputable def prefixSpan (b : ℕ → E) (J : ℕ) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range fun m : Fin J ↦ b m)

/-- `K`: the integer span of the prefix. -/
@[expose] noncomputable def prefixLattice (b : ℕ → E) (J : ℕ) : AddSubgroup E :=
  (Submodule.span ℤ (Set.range fun m : Fin J ↦ b m)).toAddSubgroup

theorem mem_prefixLattice_iff {b : ℕ → E} {J : ℕ} {v : E} :
    v ∈ prefixLattice b J ↔ ∃ c : ℕ → ℤ, v = comb b c J := by
  unfold prefixLattice comb
  rw [Submodule.mem_toAddSubgroup, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨fun m ↦ if h : m < J then c ⟨m, h⟩ else 0, ?_⟩
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [Int.cast_smul_eq_zsmul]
  · rintro ⟨c, rfl⟩
    refine ⟨fun i ↦ c i, ?_⟩
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [Int.cast_smul_eq_zsmul]

theorem comb_mem_prefixSpan (b : ℕ → E) (c : ℕ → ℤ) (J : ℕ) : comb b c J ∈ prefixSpan b J := by
  unfold comb
  refine Submodule.sum_mem _ fun m hm ↦ Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨⟨m, Finset.mem_range.1 hm⟩, rfl⟩

variable [FiniteDimensional ℝ E]

/-- `P`: the orthogonal projection onto `Wᗮ` (the final block is `P L`). -/
@[expose] noncomputable def perpProj (b : ℕ → E) (J : ℕ) : E →L[ℝ] E :=
  (prefixSpan b J)ᗮ.starProjection

theorem perpProj_eq_zero_iff {b : ℕ → E} {J : ℕ} {v : E} :
    perpProj b J v = 0 ↔ v ∈ prefixSpan b J := by
  rw [perpProj, Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal]

theorem perpProj_comb (b : ℕ → E) (c : ℕ → ℤ) (J : ℕ) : perpProj b J (comb b c J) = 0 :=
  perpProj_eq_zero_iff.2 (comb_mem_prefixSpan b c J)

/-- **Fibers lie in prefix cosets.** If every lattice vector in `W` is an integer prefix
combination (`L ∩ W ⊆ K`), then every `v ∈ L` with `P v = P u` (`u ∈ L`) is `u + Σ cₘ bₘ`. -/
theorem fiber_subset_coset {b : ℕ → E} {J : ℕ} (L : AddSubgroup E)
    (hK : ∀ v ∈ L, v ∈ prefixSpan b J → v ∈ prefixLattice b J) {u v : E} (hu : u ∈ L)
    (hv : v ∈ L) (h : perpProj b J v = perpProj b J u) : ∃ c : ℕ → ℤ, v = u + comb b c J := by
  have hd : perpProj b J (v - u) = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨c, hc⟩ := mem_prefixLattice_iff.1 (hK _ (L.sub_mem hv hu) (perpProj_eq_zero_iff.1 hd))
  exact ⟨c, by rw [← hc]; abel⟩

/-- **The fiber is exactly the prefix coset.** If the prefix generates the primitive sublattice
`L ∩ W` (`L ⊓ W = K`, e.g. it is a basis of `L ∩ W`), then for `u ∈ L` the lattice vectors
projecting to `P u` are exactly `u + Σ_{m<J} cₘ bₘ`, `c ∈ ℤ^J`. -/
theorem fiber_eq_coset {b : ℕ → E} {J : ℕ} (L : AddSubgroup E)
    (hprim : L ⊓ (prefixSpan b J).toAddSubgroup = prefixLattice b J) {u : E} (hu : u ∈ L) :
    {v | v ∈ L ∧ perpProj b J v = perpProj b J u} = Set.range fun c : ℕ → ℤ ↦ u + comb b c J := by
  ext v
  constructor
  · rintro ⟨hv, h⟩
    obtain ⟨c, rfl⟩ := fiber_subset_coset L (fun w hw hW ↦ by
      rw [← hprim]; exact ⟨hw, hW⟩) hu hv h
    exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    have hK : comb b c J ∈ L ⊓ (prefixSpan b J).toAddSubgroup :=
      hprim ▸ mem_prefixLattice_iff.2 ⟨c, rfl⟩
    exact ⟨L.add_mem hu hK.1, by rw [map_add, perpProj_comb, add_zero]⟩

end Fiber

/-! ## 2. The decoder and its correctness -/

/-- The ambient space `ℝ^{n+1}` of a block. -/
abbrev Amb (n : ℕ) := EuclideanSpace ℝ (Fin (n + 1))

section Decoder

variable {N d : ℕ}


/-- `(a, t) ∈ ℝ^{N+1}`: horizontal part `a`, height `t`. -/
@[expose] noncomputable def snocE (a : EuclideanSpace ℝ (Fin N)) (t : ℝ) : Amb N :=
  WithLp.toLp 2 (Fin.snoc (α := fun _ ↦ ℝ) (WithLp.ofLp a) t)

theorem snocE_last (a : EuclideanSpace ℝ (Fin N)) (t : ℝ) : snocE a t (Fin.last N) = t := by
  simp [snocE]

theorem snocE_castSucc (a : EuclideanSpace ℝ (Fin N)) (t : ℝ) (c : Fin N) :
    snocE a t c.castSucc = a c := by
  simp [snocE]

theorem snocE_add (a a' : EuclideanSpace ℝ (Fin N)) (t t' : ℝ) :
    snocE a t + snocE a' t' = snocE (a + a') (t + t') := by
  ext i
  refine Fin.lastCases ?_ (fun c ↦ ?_) i <;> simp [snocE]

theorem zsmul_snocE (k : ℤ) (a : EuclideanSpace ℝ (Fin N)) (t : ℝ) :
    k • snocE a t = snocE (k • a) (k * t) := by
  ext i
  refine Fin.lastCases ?_ (fun c ↦ ?_) i <;> simp [snocE, zsmul_eq_mul]

theorem snocE_zero : snocE (0 : EuclideanSpace ℝ (Fin N)) 0 = 0 := by
  ext i
  refine Fin.lastCases ?_ (fun c ↦ ?_) i <;> simp [snocE]

theorem norm_sq_snocE (a : EuclideanSpace ℝ (Fin N)) (t : ℝ) :
    ‖snocE a t‖ ^ 2 = ‖a‖ ^ 2 + t ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
  simp [snocE]

/-- The centered CBD vector as an element of `ℝ^N`. -/
@[expose] noncomputable def centeredVec (x : Fin N → Digit 3) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 fun c ↦ (centered (x c) : ℝ)

theorem plantVec_eq (x : Fin N → Digit 3) : plantVec x = snocE (centeredVec x) 1 := by
  ext i
  refine Fin.lastCases ?_ (fun c ↦ ?_) i <;> simp [plantVec, snocE, centeredVec]

/-- The decoupled lattice `L = L₀ ⊕ ℤu`. -/
@[expose] def decoupled (L₀ : AddSubgroup (Amb N)) (u : Amb N) : AddSubgroup (Amb N) :=
  L₀ ⊔ AddSubgroup.zmultiples u

/-- **Plant-free compatibility of a block** (the Part 47 reducer output). `L₀` is the null lattice,
`pre`/`J` the prefix, `F` the final block. Every field depends on the design only.
* `primitive`: `L₀ ∩ W ⊆ K` (the prefix generates the primitive sublattice `L₀ ∩ W`);
* `proj_snoc`: `P (a, t) = (Q a, t)`: `P` is the final-block projector `Q` on horizontal
  coordinates and preserves height (true when `W` is horizontal and `Q` is the matrix of `P`);
* `proj_null`: `P L₀ ⊆ (H, 0)`, `H` the final-block horizontal lattice. -/
structure Compatible (L₀ : AddSubgroup (Amb N)) (pre : PrefixData N) (J : ℕ) (F : FinalBlock N d) :
    Prop where
  primitive : ∀ v ∈ L₀, v ∈ prefixSpan pre.b J → v ∈ prefixLattice pre.b J
  proj_snoc : ∀ a t, perpProj pre.b J (snocE a t) = snocE (WithLp.toLp 2 (F.Q.mulVec a)) t
  proj_null : ∀ h ∈ L₀, ∃ h' ∈ horizontalLattice F.V F.basis, perpProj pre.b J h = snocE h' 0

/-- `v` is a shortest nonzero vector of `T`. -/
@[expose] def IsShortest {V : Type*} [Norm V] [Zero V] (T : Set V) (v : V) : Prop :=
  v ∈ T ∧ v ≠ 0 ∧ ∀ t ∈ T, t ≠ 0 → ‖v‖ ≤ ‖t‖

/-- An exact SVP oracle: returns a shortest nonzero vector whenever one exists. -/
@[expose] def SVPOracle {V : Type*} [Norm V] [Zero V] (svp : Set V → V) : Prop :=
  ∀ T, (∃ v, IsShortest T v) → IsShortest T (svp T)

/-- A lift oracle: given the projection `P`, the lattice `L` and `t ∈ P L`, returns some
`v ∈ L` with `P v = t` (in practice: reuse the integer coordinates of the SVP output). -/
@[expose] def LiftOracle {V : Type*} (lift : (V → V) → Set V → V → V) : Prop :=
  ∀ P L t, (∃ v ∈ L, P v = t) → lift P L t ∈ L ∧ P (lift P L t) = t

/-- The canonical (choice) SVP oracle. -/
@[expose] noncomputable def chooseSVP {V : Type*} [Norm V] [Zero V] (T : Set V) : V :=
  if h : ∃ v, IsShortest T v then h.choose else 0

/-- The canonical (choice) lift oracle. -/
@[expose] noncomputable def chooseLift {V : Type*} [Zero V] (P : V → V) (L : Set V) (t : V) : V :=
  if h : ∃ v ∈ L, P v = t then h.choose else 0

theorem chooseSVP_spec {V : Type*} [Norm V] [Zero V] : SVPOracle (chooseSVP (V := V)) := by
  intro T h
  simp only [chooseSVP, h, dite_true]
  exact h.choose_spec

theorem chooseLift_spec {V : Type*} [Zero V] : LiftOracle (chooseLift (V := V)) := by
  intro P L t h
  simp only [chooseLift, h, dite_true] 
  exact h.choose_spec

/-- Orient a vector to height `+1`. -/
@[expose] noncomputable def orient (v : Amb N) : Amb N :=
  if v (Fin.last N) = 1 then v else -v

/-- **The decoder of the decoupled attack.** Exact SVP on the final block `P L`, orient to height
one, lift to `L`, Babai nearest-plane on the prefix. Inputs: the oracles, the prefix data and the
lattice `L`; it does not see the plant. -/
@[expose] noncomputable def decode (svp : Set (Amb N) → Amb N)
    (lift : ((Amb N) → Amb N) → Set (Amb N) → Amb N → Amb N) (pre : PrefixData N) (J : ℕ)
    (L : Set (Amb N)) : Amb N :=
  babai pre.b pre.bs J
    (lift (perpProj pre.b J) L (orient (svp (perpProj pre.b J '' L))))

/-- Reading off the horizontal coordinates (secret and error) of the decoder output. -/
@[expose] def readCoords (v : Amb N) : Fin N → ℝ := fun c ↦ v c.castSucc

theorem readCoords_plantVec (x : Fin N → Digit 3) :
    readCoords (plantVec x) = fun c ↦ (centered (x c) : ℝ) := by
  funext c
  simp [readCoords, plantVec]

variable {L₀ : AddSubgroup (Amb N)} {pre : PrefixData N} {J : ℕ} {F : FinalBlock N d}

theorem proj_plantVec (C : Compatible L₀ pre J F) (x : Fin N → Digit 3) :
    perpProj pre.b J (plantVec x) = snocE (projectedCBD F.Q x) 1 := by
  rw [plantVec_eq, C.proj_snoc]
  rfl

/-- Every vector of the final block `P L` is `(h' + k y, k)` with `h' ∈ H`, `k ∈ ℤ`, where
`y = Q X` is the projected plant. -/
theorem proj_decoupled (C : Compatible L₀ pre J F) (x : Fin N → Digit 3) {v : Amb N}
    (hv : v ∈ decoupled L₀ (plantVec x)) :
    ∃ h' ∈ horizontalLattice F.V F.basis, ∃ k : ℤ,
      perpProj pre.b J v = snocE (h' + k • projectedCBD F.Q x) k := by
  obtain ⟨h, hh, w, hw, rfl⟩ := AddSubgroup.mem_sup.1 hv
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hw
  obtain ⟨h', hh', hP⟩ := C.proj_null h hh
  refine ⟨h', hh', k, ?_⟩
  rw [map_add, map_zsmul, hP, proj_plantVec C, zsmul_snocE, snocE_add, zero_add, mul_one]

/-- In the decoupled lattice, `L ∩ W ⊆ K` follows from the plant-free `L₀ ∩ W ⊆ K`: a vector of `W`
has height zero, so it has no `u`-component. -/
theorem decoupled_primitive (C : Compatible L₀ pre J F) (x : Fin N → Digit 3) :
    ∀ v ∈ decoupled L₀ (plantVec x), v ∈ prefixSpan pre.b J → v ∈ prefixLattice pre.b J := by
  intro v hv hW
  obtain ⟨h, hh, w, hw, rfl⟩ := AddSubgroup.mem_sup.1 hv
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hw
  have h0 := perpProj_eq_zero_iff.2 hW
  obtain ⟨h', -, hP⟩ := C.proj_null h hh
  rw [map_add, map_zsmul, hP, proj_plantVec C, zsmul_snocE, snocE_add] at h0
  have hk := congrArg (fun z : Amb N ↦ z (Fin.last N)) h0
  simp only [snocE_last, PiLp.zero_apply, zero_add, mul_one, Int.cast_eq_zero] at hk
  subst hk
  simpa using C.primitive h hh (by simpa using hW)

/-- **Ball uniqueness in the final block.** Under `Unique` (Part 94 all-heights criterion), the
only vectors of `P L` in the closed ball of radius `‖P u‖` are `0` and `±P u`. -/
theorem ball_unique (C : Compatible L₀ pre J F) (x : Fin N → Digit 3)
    (hU : allHeightsUnique (horizontalLattice F.V F.basis) (projectedCBD F.Q x)) {t : Amb N}
    (ht : t ∈ perpProj pre.b J '' decoupled L₀ (plantVec x))
    (hle : ‖t‖ ^ 2 ≤ ‖perpProj pre.b J (plantVec x)‖ ^ 2) :
    t = 0 ∨ t = perpProj pre.b J (plantVec x) ∨ t = -perpProj pre.b J (plantVec x) := by
  obtain ⟨v, hv, rfl⟩ := ht
  obtain ⟨h', hh', k, hP⟩ := proj_decoupled C x hv
  rw [proj_plantVec C, norm_sq_snocE, one_pow] at hle
  rw [proj_plantVec C, hP]
  rw [hP, norm_sq_snocE] at hle
  obtain ⟨rfl, hk⟩ := (hU h' hh' k).1 hle
  rcases hk with rfl | rfl | rfl
  · left; simpa using snocE_zero
  · right; left; simp
  · right; right
    ext i
    refine Fin.lastCases ?_ (fun c ↦ ?_) i <;> simp [snocE]

/-- **Decoder correctness.** If the projected plant is the all-heights unique shortest pair of the
final block (`Unique`) and Babai does not fail on the prefix (`¬ LiftFail`), then the decoder,
with any exact SVP oracle and any lift oracle, returns the plant `u = (X, 1)`. -/
theorem decode_eq (C : Compatible L₀ pre J F) {svp : Set (Amb N) → Amb N}
    {lift : ((Amb N) → Amb N) → Set (Amb N) → Amb N → Amb N} (hsvp : SVPOracle svp)
    (hlift : LiftOracle lift) (x : Fin N → Digit 3)
    (hU : allHeightsUnique (horizontalLattice F.V F.basis) (projectedCBD F.Q x))
    (hlf : ¬ LiftFail pre.b pre.bs J (plantVec x)) :
    decode svp lift pre J (decoupled L₀ (plantVec x)) = plantVec x := by
  set u := plantVec x
  set P := perpProj pre.b J
  set T := P '' (decoupled L₀ u : Set (Amb N))
  have hu : u ∈ decoupled L₀ u := AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples u)
  have hPu : P u = snocE (projectedCBD F.Q x) 1 := proj_plantVec C x
  have hPu1 : P u (Fin.last N) = 1 := by rw [hPu, snocE_last]
  have hPu0 : P u ≠ 0 := fun h ↦ by rw [h] at hPu1; simp at hPu1
  have hPuT : P u ∈ T := ⟨u, hu, rfl⟩
  -- `P u` is a shortest nonzero vector of `T`
  have hshort : IsShortest T (P u) := by
    refine ⟨hPuT, hPu0, fun t ht ht0 ↦ ?_⟩
    by_contra hlt
    push Not at hlt
    rcases ball_unique C x hU ht (by nlinarith [norm_nonneg t]) with h | h | h
    · exact ht0 h
    · rw [h] at hlt; exact lt_irrefl _ hlt
    · rw [h, norm_neg] at hlt; exact lt_irrefl _ hlt
  obtain ⟨hoT, ho0, hole⟩ := hsvp T ⟨_, hshort⟩
  have hout : orient (svp T) = P u := by
    have hle : ‖svp T‖ ≤ ‖P u‖ := hole _ hPuT hPu0
    rcases ball_unique C x hU hoT (by nlinarith [norm_nonneg (svp T)]) with h | h | h
    · exact absurd h ho0
    · have : svp T (Fin.last N) = 1 := by rw [h]; exact hPu1
      unfold orient
      split_ifs
      exact h
    · have : ¬ svp T (Fin.last N) = 1 := by
        rw [h, PiLp.neg_apply, hPu1]; norm_num
      unfold orient
      split_ifs
      rw [h, neg_neg]
  obtain ⟨hwL, hwP⟩ := hlift P (decoupled L₀ u) (P u) ⟨u, hu, rfl⟩
  obtain ⟨c, hc⟩ := fiber_subset_coset (decoupled L₀ u) (decoupled_primitive C x) hu hwL
    hwP
  have hlift_eq : lift P (decoupled L₀ u) (orient (svp T)) = u + comb pre.b c J := by
    rw [hout]; exact hc
  unfold decode
  change babai pre.b pre.bs J (lift P (decoupled L₀ u) (orient (svp T))) = u
  rw [hlift_eq]
  by_contra hne
  exact hlf ⟨c, hne⟩

/-- **Secret recovery.** Under the hypotheses of `decode_eq`, the horizontal coordinates of the
decoder output are the centered plant coordinates `(e, s)`. -/
theorem decode_readCoords (C : Compatible L₀ pre J F) {svp : Set (Amb N) → Amb N}
    {lift : ((Amb N) → Amb N) → Set (Amb N) → Amb N → Amb N} (hsvp : SVPOracle svp)
    (hlift : LiftOracle lift) (x : Fin N → Digit 3)
    (hU : allHeightsUnique (horizontalLattice F.V F.basis) (projectedCBD F.Q x))
    (hlf : ¬ LiftFail pre.b pre.bs J (plantVec x)) :
    readCoords (decode svp lift pre J (decoupled L₀ (plantVec x))) =
      fun c ↦ (centered (x c) : ℝ) := by
  rw [decode_eq C hsvp hlift x hU hlf, readCoords_plantVec]

end Decoder

/-! ## 3. End-to-end restart bound for the concrete decoder -/

section Restart

variable {Y ι P : Type*} [Fintype Y] [Fintype ι] [DecidableEq ι] [Fintype P] {k : ℕ}
  {r : Fin k → ℕ} {N d : Fin k → ℕ}

/-- `failProb` is monotone in the failure event on accepted rows. -/
theorem failProb_mono {w : Y → ℚ} (hw0 : ∀ y, 0 ≤ w y) {ρ : P → ℚ} (hρ0 : ∀ p, 0 ≤ ρ p)
    (acc : ∀ i, (Fin (r i) → Y) → Prop) {F F' : ∀ i, P → (Fin (r i) → Y) → Prop}
    (b : ∀ i, Fin (r i) → ι) (hF : ∀ i p z, acc i z → F i p z → F' i p z) :
    failProb w ρ acc F b ≤ failProb w ρ acc F' b := by
  unfold failProb expect plantProb
  refine Finset.sum_le_sum fun x _ ↦
    mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun j _ ↦ hw0 _)
  refine Finset.sum_le_sum fun p _ ↦ mul_le_mul_of_nonneg_left ?_ (hρ0 p)
  by_cases h : Fails acc F b x p
  · have h' : Fails acc F' b x p := by
      rcases h with h | ⟨i, hi, hF1⟩
      · exact Or.inl h
      · exact Or.inr ⟨i, hi, hF _ _ _ hi.1 hF1⟩
    simp [h, h']
  · by_cases h' : Fails acc F' b x p <;> simp [h, h']

/-- The output of the concrete decoder on block `i`: `decode` on the decoupled lattice
`L₀ i z ⊕ ℤ (π i p, 1)` with the block's prefix. -/
@[expose] noncomputable def blockOutput (svp : ∀ i, Set (Amb (N i)) → Amb (N i))
    (lift : ∀ i, (Amb (N i) → Amb (N i)) → Set (Amb (N i)) → Amb (N i) → Amb (N i))
    (L₀ : ∀ i, (Fin (r i) → Y) → AddSubgroup (Amb (N i)))
    (pre : ∀ i, (Fin (r i) → Y) → PrefixData (N i)) (J : Fin k → ℕ)
    (π : ∀ i, P → Fin (N i) → Digit 3) (i : Fin k) (p : P) (z : Fin (r i) → Y) : Amb (N i) :=
  decode (svp i) (lift i) (pre i z) (J i) (decoupled (L₀ i z) (plantVec (π i p)))

/-- The concrete decoder fails on block `i`: its output is not the plant `(π i p, 1)`. -/
@[expose] def outputFail (svp : ∀ i, Set (Amb (N i)) → Amb (N i))
    (lift : ∀ i, (Amb (N i) → Amb (N i)) → Set (Amb (N i)) → Amb (N i) → Amb (N i))
    (L₀ : ∀ i, (Fin (r i) → Y) → AddSubgroup (Amb (N i)))
    (pre : ∀ i, (Fin (r i) → Y) → PrefixData (N i)) (J : Fin k → ℕ)
    (π : ∀ i, P → Fin (N i) → Digit 3) (i : Fin k) (p : P) (z : Fin (r i) → Y) : Prop :=
  blockOutput svp lift L₀ pre J π i p z ≠ plantVec (π i p)

omit [Fintype Y] [Fintype P] in
/-- On accepted, compatible rows, failure of the concrete decoder implies the named event
`decodeFail = ¬ Unique ∨ liftFail` of `RestartReduction`. -/
theorem outputFail_imp {svp : ∀ i, Set (Amb (N i)) → Amb (N i)}
    {lift : ∀ i, (Amb (N i) → Amb (N i)) → Set (Amb (N i)) → Amb (N i) → Amb (N i)}
    (hsvp : ∀ i, SVPOracle (svp i)) (hlift : ∀ i, LiftOracle (lift i))
    (L₀ : ∀ i, (Fin (r i) → Y) → AddSubgroup (Amb (N i)))
    (R : ∀ i, (Fin (r i) → Y) → FinalBlock (N i) (d i))
    (pre : ∀ i, (Fin (r i) → Y) → PrefixData (N i)) (J : Fin k → ℕ)
    (π : ∀ i, P → Fin (N i) → Digit 3) {i : Fin k} {p : P} {z : Fin (r i) → Y}
    (hC : Compatible (L₀ i z) (pre i z) (J i) (R i z))
    (hf : outputFail svp lift L₀ pre J π i p z) : decodeFail R π (liftFail pre J π) i p z := by
  by_contra h
  simp only [decodeFail, not_or, not_not] at h
  exact hf (decode_eq hC (hsvp i) (hlift i) (π i p) h.1 h.2)

/-- **End-to-end restart bound for the concrete decoder.** `k` disjoint row blocks; on each
block a plant-free reducer supplies the null lattice `L₀ i z`, the prefix `pre i z` of length
`J i` and the final block `R i z`, compatible on accepted rows (`hC`). The restart algorithm runs
`decode` (exact SVP on the final block, orientation, lift, Babai on the prefix) on the first
accepted block. With any exact SVP oracle and any lift oracle,
`Pr[output ≠ (π i p, 1) or no block accepted] ≤ ∏ δᵢ + ε + ℓ`, where
`Σ_{m<J i} 2 exp(−(gp i m)²/12) ≤ ℓ`. -/
theorem restartDecoder {w : Y → ℚ} (hw : ∑ y, w y = 1) (hw0 : ∀ y, 0 ≤ w y)
    {ρ : P → ℚ} (hρ : ∑ p, ρ p = 1) (hρ0 : ∀ p, 0 ≤ ρ p)
    {svp : ∀ i, Set (Amb (N i)) → Amb (N i)}
    {lift : ∀ i, (Amb (N i) → Amb (N i)) → Set (Amb (N i)) → Amb (N i) → Amb (N i)}
    (hsvp : ∀ i, SVPOracle (svp i)) (hlift : ∀ i, LiftOracle (lift i))
    (L₀ : ∀ i, (Fin (r i) → Y) → AddSubgroup (Amb (N i)))
    (R : ∀ i, (Fin (r i) → Y) → FinalBlock (N i) (d i)) (π : ∀ i, P → Fin (N i) → Digit 3)
    (hπ : ∀ i v, ((∑ p with π i p = v, ρ p : ℚ) : ℝ) = jointWeight v)
    (pre : ∀ i, (Fin (r i) → Y) → PrefixData (N i)) (J : Fin k → ℕ) (gp : Fin k → ℕ → ℝ)
    (hgp : ∀ i m, 0 ≤ gp i m)
    {g L : Fin k → ℝ} (hg : ∀ i, 0 < g i) (hL : ∀ i, 0 ≤ L i)
    (gap : ∀ i, 0 < L i ^ 2 - 1 - (3/2) * (d i : ℝ))
    (hC : ∀ i z, accept R g L (prefixFloor pre J gp) i z →
      Compatible (L₀ i z) (pre i z) (J i) (R i z))
    (b : ∀ i, Fin (r i) → ι) (hb : Function.Injective (fun q : (Σ i, Fin (r i)) ↦ b q.1 q.2))
    {ε ℓ : ℝ} (hε0 : 0 ≤ ε) (hε : ∀ i, reductionError (N i) (d i) (g i) (L i) ≤ ε)
    (hℓ : ∀ i, ∑ m ∈ Finset.range (J i), 2 * Real.exp (-gp i m ^ 2 / 12) ≤ ℓ) (hℓ0 : 0 ≤ ℓ) :
    (failProb w ρ (accept R g L (prefixFloor pre J gp))
        (outputFail svp lift L₀ pre J π) b : ℝ) ≤
      (∏ i, (rejectProb w (accept R g L (prefixFloor pre J gp)) i : ℝ)) + ε + ℓ := by
  refine le_trans ?_ (restartReduction_babai hw hw0 hρ hρ0 R π hπ pre J gp hgp hg hL gap b hb
    hε0 hε hℓ hℓ0)
  exact_mod_cast failProb_mono hw0 hρ0 _ b fun i p z hz hf ↦
    outputFail_imp hsvp hlift L₀ R pre J π (hC i z hz) hf

/-- The block-`i` secret read off a decoder output: the horizontal coordinates labelled by the
secret indices under `σ i`. -/
@[expose] def readSecret {n : ℕ} (σ : ∀ i, Fin (N i) ≃ Fin n ⊕ Fin (r i)) (i : Fin k)
    (v : Amb (N i)) : Fin n → ℝ :=
  fun j ↦ v ((σ i).symm (.inl j)).castSucc

/-- The LWE decoder fails on block `i`: the secret read off its output is not the true centered
secret `s`. -/
@[expose] def secretFail {n : ℕ} (svp : ∀ i, Set (Amb (N i)) → Amb (N i))
    (lift : ∀ i, (Amb (N i) → Amb (N i)) → Set (Amb (N i)) → Amb (N i) → Amb (N i))
    (L₀ : ∀ i, (Fin (r i) → Y) → AddSubgroup (Amb (N i)))
    (pre : ∀ i, (Fin (r i) → Y) → PrefixData (N i)) (J : Fin k → ℕ)
    (σ : ∀ i, Fin (N i) ≃ Fin n ⊕ Fin (r i)) (b : ∀ i, Fin (r i) → ι) (i : Fin k)
    (p : (Fin n → Digit 3) × (ι → Digit 3)) (z : Fin (r i) → Y) : Prop :=
  readSecret σ i (blockOutput svp lift L₀ pre J (lwePlant σ b) i p z) ≠
    fun j ↦ (centered (p.1 j) : ℝ)

omit [Fintype Y] [Fintype ι] [DecidableEq ι] in
theorem readSecret_plantVec {n : ℕ} (σ : ∀ i, Fin (N i) ≃ Fin n ⊕ Fin (r i))
    (b : ∀ i, Fin (r i) → ι) (i : Fin k) (p : (Fin n → Digit 3) × (ι → Digit 3)) :
    readSecret σ i (plantVec (lwePlant σ b i p)) = fun j ↦ (centered (p.1 j) : ℝ) := by
  funext j
  simp [readSecret, plantVec, lwePlant]

/-- **End-to-end LWE theorem.** The secret `s` and the error `e` are iid CBD(3), independent of
the design; block `i` decodes against `(s, e restricted to block i)`. The restart algorithm runs
the concrete decoder on the first accepted block and reads `s` off the output. Then
`Pr[the secret read off ≠ s, or no block accepted] ≤ ∏ δᵢ + ε + ℓ`, with
`ε ≥ reductionError` and `ℓ ≥ Σ_{m<J i} 2 exp(−(gp i m)²/12)`. -/
theorem restartDecoder_lwe {w : Y → ℚ} (hw : ∑ y, w y = 1) (hw0 : ∀ y, 0 ≤ w y) {n : ℕ}
    (σ : ∀ i, Fin (N i) ≃ Fin n ⊕ Fin (r i))
    {svp : ∀ i, Set (Amb (N i)) → Amb (N i)}
    {lift : ∀ i, (Amb (N i) → Amb (N i)) → Set (Amb (N i)) → Amb (N i) → Amb (N i)}
    (hsvp : ∀ i, SVPOracle (svp i)) (hlift : ∀ i, LiftOracle (lift i))
    (L₀ : ∀ i, (Fin (r i) → Y) → AddSubgroup (Amb (N i)))
    (R : ∀ i, (Fin (r i) → Y) → FinalBlock (N i) (d i))
    (pre : ∀ i, (Fin (r i) → Y) → PrefixData (N i)) (J : Fin k → ℕ) (gp : Fin k → ℕ → ℝ)
    (hgp : ∀ i m, 0 ≤ gp i m)
    {g L : Fin k → ℝ} (hg : ∀ i, 0 < g i) (hL : ∀ i, 0 ≤ L i)
    (gap : ∀ i, 0 < L i ^ 2 - 1 - (3/2) * (d i : ℝ))
    (hC : ∀ i z, accept R g L (prefixFloor pre J gp) i z →
      Compatible (L₀ i z) (pre i z) (J i) (R i z))
    (b : ∀ i, Fin (r i) → ι) (hb : Function.Injective (fun q : (Σ i, Fin (r i)) ↦ b q.1 q.2))
    {ε ℓ : ℝ} (hε0 : 0 ≤ ε) (hε : ∀ i, reductionError (N i) (d i) (g i) (L i) ≤ ε)
    (hℓ : ∀ i, ∑ m ∈ Finset.range (J i), 2 * Real.exp (-gp i m ^ 2 / 12) ≤ ℓ) (hℓ0 : 0 ≤ ℓ) :
    (failProb w (plantWeight n cbdQ) (accept R g L (prefixFloor pre J gp))
        (secretFail svp lift L₀ pre J σ b) b : ℝ) ≤
      (∏ i, (rejectProb w (accept R g L (prefixFloor pre J gp)) i : ℝ)) + ε + ℓ := by
  have hρ0 (p : (Fin n → Digit 3) × (ι → Digit 3)) : 0 ≤ plantWeight n cbdQ p := by
    unfold plantWeight
    exact mul_nonneg (Finset.prod_nonneg fun j _ ↦ cbdQ_nonneg _)
      (Finset.prod_nonneg fun j _ ↦ cbdQ_nonneg _)
  refine le_trans ?_ (restartReduction_lwe_babai hw hw0 σ R pre J gp hgp hg hL gap b hb hε0 hε
    hℓ hℓ0)
  have hmono := failProb_mono (acc := accept R g L (prefixFloor pre J gp))
    (F := secretFail svp lift L₀ pre J σ b)
    (F' := decodeFail R (lwePlant σ b) (liftFail pre J (lwePlant σ b))) hw0 hρ0 (b := b)
    fun i p z hz hf ↦ outputFail_imp hsvp hlift L₀ R pre J (lwePlant σ b) (hC i z hz)
      fun he ↦ hf (by
        rw [he, readSecret_plantVec])
  exact_mod_cast hmono

/-- **Fully concrete decoder.** `restartDecoder_lwe` with the canonical choice oracles
`chooseSVP` and `chooseLift`: no oracle hypothesis remains. -/
theorem restartDecoder_lwe_choose {w : Y → ℚ} (hw : ∑ y, w y = 1) (hw0 : ∀ y, 0 ≤ w y)
    {n : ℕ} (σ : ∀ i, Fin (N i) ≃ Fin n ⊕ Fin (r i))
    (L₀ : ∀ i, (Fin (r i) → Y) → AddSubgroup (Amb (N i)))
    (R : ∀ i, (Fin (r i) → Y) → FinalBlock (N i) (d i))
    (pre : ∀ i, (Fin (r i) → Y) → PrefixData (N i)) (J : Fin k → ℕ) (gp : Fin k → ℕ → ℝ)
    (hgp : ∀ i m, 0 ≤ gp i m)
    {g L : Fin k → ℝ} (hg : ∀ i, 0 < g i) (hL : ∀ i, 0 ≤ L i)
    (gap : ∀ i, 0 < L i ^ 2 - 1 - (3/2) * (d i : ℝ))
    (hC : ∀ i z, accept R g L (prefixFloor pre J gp) i z →
      Compatible (L₀ i z) (pre i z) (J i) (R i z))
    (b : ∀ i, Fin (r i) → ι) (hb : Function.Injective (fun q : (Σ i, Fin (r i)) ↦ b q.1 q.2))
    {ε ℓ : ℝ} (hε0 : 0 ≤ ε) (hε : ∀ i, reductionError (N i) (d i) (g i) (L i) ≤ ε)
    (hℓ : ∀ i, ∑ m ∈ Finset.range (J i), 2 * Real.exp (-gp i m ^ 2 / 12) ≤ ℓ) (hℓ0 : 0 ≤ ℓ) :
    (failProb w (plantWeight n cbdQ) (accept R g L (prefixFloor pre J gp))
        (secretFail (fun _ ↦ chooseSVP) (fun _ ↦ chooseLift) L₀ pre J σ b) b : ℝ) ≤
      (∏ i, (rejectProb w (accept R g L (prefixFloor pre J gp)) i : ℝ)) + ε + ℓ :=
  restartDecoder_lwe hw hw0 σ (fun _ ↦ chooseSVP_spec) (fun _ ↦ chooseLift_spec) L₀ R pre J gp
    hgp hg hL gap hC b hb hε0 hε hℓ hℓ0

end Restart

end SigabaNeo.Wall1.DecoupledDecoder

#print axioms SigabaNeo.Wall1.DecoupledDecoder.mem_prefixLattice_iff
#print axioms SigabaNeo.Wall1.DecoupledDecoder.perpProj_eq_zero_iff
#print axioms SigabaNeo.Wall1.DecoupledDecoder.fiber_subset_coset
#print axioms SigabaNeo.Wall1.DecoupledDecoder.fiber_eq_coset
#print axioms SigabaNeo.Wall1.DecoupledDecoder.plantVec_eq
#print axioms SigabaNeo.Wall1.DecoupledDecoder.norm_sq_snocE
#print axioms SigabaNeo.Wall1.DecoupledDecoder.chooseSVP_spec
#print axioms SigabaNeo.Wall1.DecoupledDecoder.chooseLift_spec
#print axioms SigabaNeo.Wall1.DecoupledDecoder.proj_decoupled
#print axioms SigabaNeo.Wall1.DecoupledDecoder.decoupled_primitive
#print axioms SigabaNeo.Wall1.DecoupledDecoder.ball_unique
#print axioms SigabaNeo.Wall1.DecoupledDecoder.decode_eq
#print axioms SigabaNeo.Wall1.DecoupledDecoder.decode_readCoords
#print axioms SigabaNeo.Wall1.DecoupledDecoder.failProb_mono
#print axioms SigabaNeo.Wall1.DecoupledDecoder.outputFail_imp
#print axioms SigabaNeo.Wall1.DecoupledDecoder.restartDecoder
#print axioms SigabaNeo.Wall1.DecoupledDecoder.readSecret_plantVec
#print axioms SigabaNeo.Wall1.DecoupledDecoder.restartDecoder_lwe
#print axioms SigabaNeo.Wall1.DecoupledDecoder.restartDecoder_lwe_choose
