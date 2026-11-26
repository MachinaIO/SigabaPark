import Definitions.Def_GGH15

/-!
# The masked γ⊗-GGH15 witness-encryption candidates (DAG notes, PRs #45, #54, #55)

Vocabulary on top of `Def_GGH15` for the candidates of the notes
`pq-we-witness-prf-masked-evaluator` (§5, "masked γ⊗-GGH15 WE"),
`pq-we-masked-evaluator-mechanisms` (§3, "positional masked γ⊗-GGH15") and the hybrid of
`pq-we-masked-overcomplete-leaf` (§6, §10, "cut lemma").

* **CNF branching program** (CVW18 Construction 6.4). A CNF `Ψ` with `w` clauses over `h`
  variables is `Ψ : Fin w → Fin h → Bool → Bool`, with `Ψ j i b = true` iff the literal
  "`x_i = b`" occurs in clause `j` (`x_i` for `b = true`, `x̄_i` for `b = false`). Its read-once
  BP is `M_{i,b} = diag_j([Ψ j i b = false]) ∈ {0,1}^{w×w}`, so `M_x = 0` iff `Ψ(x) = 1`
  (`cnfMat`, `Sat`).
* **Row blocks.** `Rows c sh = (Fin c × Fin dR) ⊕ ((Fin w × Fin n') ⊕ Fin n)`: a comparator /
  mask block (`c` comparator states, mask secret dimension `dR`), the constraint block (`w`
  clauses, constraint secret dimension `n'`) and the CPRF block (dimension `n`).
* **Per-level secret** `maskedSecret P R M S' S = diag(P ⊗ R, M ⊗ S', S)`. The masked candidate
  (PR #45) uses `c = 1`, `P = 1` and a bit-independent `R_i`: `diag(R_i, M_{i,b} ⊗ S'_{i,b}, S_{i,b})`.
  The positional candidate (PR #54) uses the reflected-Gray comparator `P_{i,b}` (`c = 3`).
* **Left matrices** `J_O`, `J_C ∈ Z^{n × t}` (CVW18's `J = (J' | I_n)`, Theorem 5.7): `J_O` reads
  the comparator start state through `r₀` and the CPRF block; `J_C` reads the constraint block
  through `j_C ⊗ s'₀` and the CPRF block. `J'_O − J'_C` has rank one (PR #45, attack 2).
  `r₀ ∈ Z^{dR}`, `j_C ∈ Z^w`, `s'₀ ∈ Z^{n'}` are public parameters of the scheme.
* **Mask.** `mask = (r₀ R_*) A_h^{mask} ∈ Z_q^{1×m}` with `R_* = R_1 ⋯ R_h`: the canonical
  value `O(z) − ck(z)` on every witness path (up to noise).

## Laws (all as PMFs on bits, `encodeTuple` of the components)

* `maskedView … chal`: `(J_O A_0, J_C A_0, {D_{i,b}}, c)` for the masked candidate, with
  `c = mask` (`maskedReal`) or `c` uniform (`maskedIdeal`): the two sides of the *masked two-vector
  lemma* (PR #45 §6). `maskedCiphertext μ`: the WE ciphertext with `c = ⌊mask⌉₂ ⊕ μ`.
* `positionalView … t`: hybrid `t ∈ [0, 2^h]` of the positional candidate (PR #54 §3): comparator
  against threshold `t` in reflected Gray order, final comparator rows of `A_h` equal to `mask'`
  on state lt and `mask` on eq/gt, challenge component `mask` value `(r₀ R_*) mask`.
* `cutView … L ideal`: the hybrid of PR #55 §6 after steps 1–2 (CPRF block stripped, leaf-first
  on the blocks of the clauses inside the first `L` variables), truncated to `(W, D_1, …, D_L)`;
  `ideal = true` replaces every level-`L` target by an independent uniform matrix (PR #55 §10).
-/

namespace AdvancedEncryption.WE.MaskedGGH15

open SigabaNeo SigabaNeo.Lattices Matrix AdvancedEncryption.WE.GGH15
open Cslib.Probability

/-! ### CNF branching programs (CVW18 Construction 6.4) -/

/-- A CNF with `w` clauses over `h` variables: `Ψ j i b = true` iff the literal `x_i = b` occurs
in clause `j`. -/
abbrev CNF (w h : ℕ) : Type := Fin w → Fin h → Bool → Bool

/-- `x` satisfies `Ψ`: every clause has a literal made true by `x`. -/
def Sat {w h : ℕ} (Ψ : CNF w h) (x : Fin h → Bool) : Prop := ∀ j, ∃ i, Ψ j i (x i) = true

/-- **CVW18 Construction 6.4**: `M_{i,b} = diag_j([literal x_i = b does not occur in clause j])`. -/
def cnfMat {w h : ℕ} (Ψ : CNF w h) (i : Fin h) (b : Bool) : Matrix (Fin w) (Fin w) ℤ :=
  diagonal fun j => if Ψ j i b then 0 else 1

/-! ### Shapes, secrets and left matrices -/

/-- Block dimensions: clauses `w`, mask secret `dR`, constraint secret `n'`, CPRF secret `n`. -/
structure Shape where
  w : ℕ
  dR : ℕ
  n' : ℕ
  n : ℕ

/-- Rows of the level matrices: comparator/mask block, constraint block, CPRF block. -/
abbrev Rows (c : ℕ) (sh : Shape) : Type :=
  (Fin c × Fin sh.dR) ⊕ ((Fin sh.w × Fin sh.n') ⊕ Fin sh.n)

/-- The per-level secret `diag(P ⊗ R, M ⊗ S', S)` (PR #54 §3; PR #45 §5 with `c = 1`, `P = 1`). -/
def maskedSecret {c : ℕ} {sh : Shape} (P : Matrix (Fin c) (Fin c) ℤ)
    (R : Matrix (Fin sh.dR) (Fin sh.dR) ℤ) (M : Matrix (Fin sh.w) (Fin sh.w) ℤ)
    (S' : Matrix (Fin sh.n') (Fin sh.n') ℤ) (S : Matrix (Fin sh.n) (Fin sh.n) ℤ) :
    Matrix (Rows c sh) (Rows c sh) ℤ :=
  fromBlocks (gammaTensor P R) 0 0 (fromBlocks (gammaTensor M S') 0 0 S)

/-- `J_O = (1_n ⊗ (e_st ⊗ r₀) | 0 | I_n)`: comparator start state `st` through `r₀`, and the CPRF
block. -/
def leftO {c : ℕ} {sh : Shape} (st : Fin c) (r0 : Fin sh.dR → ℤ) :
    Matrix (Fin sh.n) (Rows c sh) ℤ :=
  fun j => Sum.elim (fun sr => if sr.1 = st then r0 sr.2 else 0)
    (Sum.elim (fun _ => 0) fun j' => if j = j' then 1 else 0)

/-- `J_C = (0 | 1_n ⊗ (j_C ⊗ s'₀) | I_n)`: the constraint block through `j_C ⊗ s'₀`, and the CPRF
block. -/
def leftC {c : ℕ} {sh : Shape} (jC : Fin sh.w → ℤ) (s0 : Fin sh.n' → ℤ) :
    Matrix (Fin sh.n) (Rows c sh) ℤ :=
  fun j => Sum.elim (fun _ => 0)
    (Sum.elim (fun kr => jC kr.1 * s0 kr.2) fun j' => if j = j' then 1 else 0)

/-- The mask value `(r₀ R_*) · A^{mask} ∈ Z_q^{1×m}`, `R_* = R_0 ⋯ R_{h−1}`. -/
def maskOf {h m dR : ℕ} (q : ℕ) (r0 : Fin dR → ℤ) (R : Fin h → Matrix (Fin dR) (Fin dR) ℤ)
    (Amask : Matrix (Fin dR) (Fin m) (ZMod q)) : Fin m → ZMod q :=
  (fun r => ((r0 ᵥ* (List.ofFn R).prod) r : ZMod q)) ᵥ* Amask

/-- The secrets: bit-independent `R_i ← D_{Z,σ}^{dR×dR}`, `S'_{i,b} ← D_{Z,σ}^{n'×n'}`,
`S_{i,b} ← D_{Z,σ}^{n×n}`, all independent. -/
noncomputable def secretLaw (h : ℕ) (sh : Shape) (σ : ℚ) :
    PMF ((Fin h → Matrix (Fin sh.dR) (Fin sh.dR) ℤ) ×
      (Fin h → Bool → Matrix (Fin sh.n') (Fin sh.n') ℤ) ×
      (Fin h → Bool → Matrix (Fin sh.n) (Fin sh.n) ℤ)) := do
  let R ← indep fun _ : Fin h => gaussMat (Fin sh.dR) (Fin sh.dR) σ
  let S' ← indep fun _ : Fin h => indep fun _ : Bool => gaussMat (Fin sh.n') (Fin sh.n') σ
  let S ← indep fun _ : Fin h => indep fun _ : Bool => gaussMat (Fin sh.n) (Fin sh.n) σ
  return (R, S', S)

/-- The published view `(J_O A_0, J_C A_0, {D_{i,b}}, c)` as bits. -/
noncomputable def encodeView {ι : Type} [Fintype ι] {h n m q : ℕ}
    (JO JC : Matrix (Fin n) ι ℤ) (A0 : Matrix ι (Fin m) (ZMod q))
    (D : Option (Fin h → Bool → Matrix (Fin m) (Fin m) ℤ)) (chal : List Bool) : List Bool :=
  encodeTuple [encodeZq (modq q JO * A0), encodeZq (modq q JC * A0), encodeD D, chal]

/-! ### The masked candidate (PR #45 §5) -/

/-- The mask rows `A_h^{mask}` of a level matrix of the masked candidate (`c = 1`). -/
def maskRows {sh : Shape} {m q : ℕ} (A : Matrix (Rows 1 sh) (Fin m) (ZMod q)) :
    Matrix (Fin sh.dR) (Fin m) (ZMod q) :=
  fun r => A (Sum.inl (0, r))

/-- The masked candidate's view, with the challenge component drawn by `chal` from the mask.
Secrets as in `secretLaw`, `A_h` uniform, `Ŝ_{i,b} = diag(R_i, M_{i,b} ⊗ S'_{i,b}, S_{i,b})`,
GGH15 encodings (Construction 5.1), published `(J_O A_0, J_C A_0, {D_{i,b}})`. -/
noncomputable def maskedView (p : Params) (h : ℕ) (sh : Shape) (Ψ : CNF sh.w h)
    (r0 : Fin sh.dR → ℤ) (jC : Fin sh.w → ℤ) (s0 : Fin sh.n' → ℤ)
    (chal : (Fin p.m → ZMod p.q) → PMF (List Bool)) : PMF (List Bool) := do
  let RS ← secretLaw h sh p.σ
  let Ah ← PMF.uniformOfFintype (Matrix (Rows 1 sh) (Fin p.m) (ZMod p.q))
  let Shat := fun i b => maskedSecret (c := 1) 1 (RS.1 i) (cnfMat Ψ i b) (RS.2.1 i b) (RS.2.2 i b)
  let AD ← encode p Shat Ah
  let c ← chal (maskOf p.q r0 RS.1 (maskRows Ah))
  return encodeView (leftO 0 r0) (leftC jC s0) (AD.1 0) AD.2 c

/-- The real side of the masked two-vector lemma: the challenge is the mask itself. -/
noncomputable def maskedReal (p : Params) (h : ℕ) (sh : Shape) (Ψ : CNF sh.w h)
    (r0 : Fin sh.dR → ℤ) (jC : Fin sh.w → ℤ) (s0 : Fin sh.n' → ℤ) : PMF (List Bool) :=
  maskedView p h sh Ψ r0 jC s0 fun mask => PMF.pure (encodeVec mask)

/-- The ideal side: the challenge is an independent uniform vector. -/
noncomputable def maskedIdeal (p : Params) (h : ℕ) (sh : Shape) (Ψ : CNF sh.w h)
    (r0 : Fin sh.dR → ℤ) (jC : Fin sh.w → ℤ) (s0 : Fin sh.n' → ℤ) : PMF (List Bool) :=
  maskedView p h sh Ψ r0 jC s0 fun _ =>
    (PMF.uniformOfFintype (Fin p.m → ZMod p.q)).map encodeVec

/-- `⌊x⌉₂ = ⌊2x/q⌉ mod 2`: `true` iff `q/4 ≤ x < 3q/4` (as integers in `[0, q)`). -/
def roundBit {q : ℕ} (x : ZMod q) : Bool := decide (q ≤ 4 * x.val ∧ 4 * x.val < 3 * q)

/-- The WE ciphertext of the masked candidate for the bit `μ`: the challenge component is
`⌊mask⌉₂ ⊕ μ`, coordinatewise (PR #45 §5: "`⌊mask⌉ + μ`"). -/
noncomputable def maskedCiphertext (p : Params) (h : ℕ) (sh : Shape) (Ψ : CNF sh.w h)
    (r0 : Fin sh.dR → ℤ) (jC : Fin sh.w → ℤ) (s0 : Fin sh.n' → ℤ) (μ : Bool) : PMF (List Bool) :=
  maskedView p h sh Ψ r0 jC s0 fun mask => PMF.pure (List.ofFn fun j => xor (roundBit (mask j)) μ)

/-! ### The positional candidate (PR #54 §3) -/

/-- The reflected Gray codeword of rank `t`, most significant bit at level `0`:
bit `i` of `t ⊕ ⌊t/2⌋` counted from the top. -/
def grayCode (h t : ℕ) : Fin h → Bool := fun i => Nat.testBit (t ^^^ t / 2) (h - 1 - i)

/-- The rank of a path in reflected Gray order: its binary digits are the prefix parities. -/
def grayRank {h : ℕ} (x : Fin h → Bool) : ℕ :=
  ∑ i : Fin h, if (Finset.univ.filter fun j : Fin h => j ≤ i ∧ x j = true).card % 2 = 1
    then 2 ^ (h - 1 - i) else 0

/-- Comparator states: `0` = lt, `1` = eq, `2` = gt. The state reached from eq at level `i`
(reading `x_i = b`) against the threshold `t`. The eq prefix of length `i` is the prefix of the
codeword of rank `t`; its completions have the ranks `[v·2^{h−i}, (v+1)·2^{h−i})` with
`v = ⌊t / 2^{h−i}⌋`, and its parity is `v mod 2`. Appending `b` gives the binary digit
`(v mod 2) ⊕ b` and the rank interval `[lo, lo + 2^{h−i−1})`: lt if it lies below `t`, gt if
above, eq if it contains `t`. -/
def cmpFromEq (h t : ℕ) (i : Fin h) (b : Bool) : Fin 3 :=
  let v := t / 2 ^ (h - i)
  let v' := 2 * v + (if xor (decide (v % 2 = 1)) b then 1 else 0)
  let size := 2 ^ (h - i - 1)
  let lo := v' * size
  if lo + size ≤ t then 0 else if t < lo then 2 else 1

/-- The comparator's start state: eq if `t < 2^h` (the threshold path exists), else lt. -/
def cmpStart (h t : ℕ) : Fin 3 := if t < 2 ^ h then 1 else 0

/-- **The reflected-Gray comparator** `P_{i,b} ∈ {0,1}^{3×3}` against the threshold `t` (rows are
source states, `e_s · P_{i,b} = e_{s'}`): lt and gt are absorbing, eq moves by `cmpFromEq`. -/
def cmpMat (h t : ℕ) (i : Fin h) (b : Bool) : Matrix (Fin 3) (Fin 3) ℤ :=
  fun s s' => if (if s = 1 then cmpFromEq h t i b else s) = s' then 1 else 0

/-- The top matrix of the positional candidate: comparator rows `mask'` on lt and `mask` on eq,
gt; constraint rows `A^{con}`; CPRF rows `A^{bot}`. -/
def positionalTop {sh : Shape} {m q : ℕ} (mask mask' : Matrix (Fin sh.dR) (Fin m) (ZMod q))
    (Acon : Matrix (Fin sh.w × Fin sh.n') (Fin m) (ZMod q))
    (Abot : Matrix (Fin sh.n) (Fin m) (ZMod q)) : Matrix (Rows 3 sh) (Fin m) (ZMod q) :=
  Sum.elim (fun sr => if sr.1 = 0 then mask' sr.2 else mask sr.2) (Sum.elim Acon Abot)

/-- **Hybrid `t` of the positional masked γ⊗-GGH15 candidate** (PR #54 §3), `t ∈ [0, 2^h]`.
Secrets as in `secretLaw`; `mask, mask', A^{con}, A^{bot}` uniform;
`Ŝ_{i,b} = diag(P^{(t)}_{i,b} ⊗ R_i, M_{i,b} ⊗ S'_{i,b}, S_{i,b})`; GGH15 encodings with
`A_h = positionalTop`; published `(J_O A_0, J_C A_0, {D_{i,b}})` with `J_O` reading the start
state, and the challenge component `(r₀ R_*) · mask`. In hybrid `t` the paths of Gray rank `< t`
end in lt (`mask'`), the others in eq/gt (`mask`). Hybrid `0` is the real view; in hybrid `2^h`
`mask` occurs only in the challenge component. -/
noncomputable def positionalView (p : Params) (h : ℕ) (sh : Shape) (Ψ : CNF sh.w h)
    (r0 : Fin sh.dR → ℤ) (jC : Fin sh.w → ℤ) (s0 : Fin sh.n' → ℤ) (t : ℕ) : PMF (List Bool) := do
  let RS ← secretLaw h sh p.σ
  let mask ← PMF.uniformOfFintype (Matrix (Fin sh.dR) (Fin p.m) (ZMod p.q))
  let mask' ← PMF.uniformOfFintype (Matrix (Fin sh.dR) (Fin p.m) (ZMod p.q))
  let Acon ← PMF.uniformOfFintype (Matrix (Fin sh.w × Fin sh.n') (Fin p.m) (ZMod p.q))
  let Abot ← PMF.uniformOfFintype (Matrix (Fin sh.n) (Fin p.m) (ZMod p.q))
  let Shat := fun i b =>
    maskedSecret (cmpMat h t i b) (RS.1 i) (cnfMat Ψ i b) (RS.2.1 i b) (RS.2.2 i b)
  let AD ← encode p Shat (positionalTop mask mask' Acon Abot)
  return encodeView (leftO (cmpStart h t) r0) (leftC jC s0) (AD.1 0) AD.2
    (encodeVec (maskOf p.q r0 RS.1 mask))

/-! ### The cut hybrid (PR #55 §6, §10) -/

/-- Rows without the CPRF block (stripped by CVW18 phase 1): mask block and constraint block. -/
abbrev CutRows (sh : Shape) : Type := Fin sh.dR ⊕ (Fin sh.w × Fin sh.n')

/-- Clause `j` uses only the variables `x_i` with `i < L`. -/
def ClauseWithin {w h : ℕ} (Ψ : CNF w h) (L : ℕ) (j : Fin w) : Prop :=
  ∀ i b, Ψ j i b = true → (i : ℕ) < L

/-- The sub-CNF of the clauses inside the first `L` variables is unsatisfiable. -/
def FirstUnsat {w h : ℕ} (Ψ : CNF w h) (L : ℕ) : Prop :=
  ∀ x : Fin h → Bool, ∃ j, ClauseWithin Ψ L j ∧ ∀ i, Ψ j i (x i) = false

/-- **The cut hybrid** of PR #55, levels `1, …, L` (`L ≤ h`, level `i + 1` reads `x_i`), rows
`CutRows`. Uniform `A_0, …, A_L`; secrets `diag(R_i, M_{i,b} ⊗ S'_{i,b})`; GGH15 targets
`Ŝ A + E` at levels `< L`. At level `L` the target of bit `b` is, row block by row block:
mask block `R_L A_L^{mask} + E`; a clause `k` inside the first `L` variables
`(M_{L,b})_{kk} · U_{b,k} + E` with `U_{b,k}` uniform (the result of leaf-first steps, §6 step 2);
any other clause `(M_{L,b})_{kk} S'_{L,b} A_L^{k} + E`. With `ideal = true` every level-`L` target
is an independent uniform matrix instead (§10). Published: `W = (r₀ | −(j_C ⊗ s'₀)) A_0` (the
exposed root row `u_O − u_C`) and `D_1, …, D_L`. -/
noncomputable def cutView (p : Params) (h : ℕ) (sh : Shape) (Ψ : CNF sh.w h)
    (r0 : Fin sh.dR → ℤ) (jC : Fin sh.w → ℤ) (s0 : Fin sh.n' → ℤ) (L : ℕ) (hL : L ≤ h)
    (ideal : Bool) : PMF (List Bool) := do
  let A ← PMF.uniformOfFintype (Fin (L + 1) → Matrix (CutRows sh) (Fin p.m) (ZMod p.q))
  let R ← indep fun _ : Fin L => gaussMat (Fin sh.dR) (Fin sh.dR) p.σ
  let S' ← indep fun _ : Fin L => indep fun _ : Bool => gaussMat (Fin sh.n') (Fin sh.n') p.σ
  let E ← errorLaw (CutRows sh) L p
  let U ← PMF.uniformOfFintype (Bool → Matrix (Fin sh.w × Fin sh.n') (Fin p.m) (ZMod p.q))
  let Yid ← PMF.uniformOfFintype (Bool → Matrix (CutRows sh) (Fin p.m) (ZMod p.q))
  let M := fun (i : Fin L) b => cnfMat Ψ ⟨i, lt_of_lt_of_le i.isLt hL⟩ b
  let Shat : Fin L → Bool → Matrix (CutRows sh) (CutRows sh) ℤ :=
    fun i b => fromBlocks (R i) 0 0 (gammaTensor (M i b) (S' i b))
  let Y : Fin L → Bool → Matrix (CutRows sh) (Fin p.m) (ZMod p.q) := fun i b =>
    if (i : ℕ) + 1 = L then
      (if ideal then Yid b else
        Sum.elim (fun r => target p.q A Shat E i b (Sum.inl r))
          (fun kr => open Classical in
            if ClauseWithin Ψ L kr.1 then
              ((M i b kr.1 kr.1 : ZMod p.q) • U b kr) + modq p.q (E i b) (Sum.inr kr)
            else target p.q A Shat E i b (Sum.inr kr)))
    else target p.q A Shat E i b
  let D ← preimages p.q p.σ (fun i => A i.castSucc) Y
  let W : CutRows sh → ℤ := Sum.elim r0 fun kr => -(jC kr.1 * s0 kr.2)
  return encodeTuple [encodeVec ((fun r => (W r : ZMod p.q)) ᵥ* A 0), encodeD D]

/-! ### Parameter regime and explicit losses for the open lemmas -/

/-- **The parameter regime of the open lemmas**, for level matrices with `t` rows, smallest secret
block dimension `d`, target strength `k` and the plain LWE parameters `pL` of the premise. The
conditions are those of CVW18's proofs, read with the standard LWE of `SigabaNeoStd`
(`LWE.decision`, uniform public matrix):
* `pL` has modulus `q`, a uniform secret and errors `D_{Z,χ}` (CVW18 Theorem 5.7 assumes
  `LWE_{n,2m,q,U(Z_q),D_{Z,σ},D_{Z,σ}}`, with small public matrices);
* `2 n_L ⌈log q⌉ ≤ d`: LWE with small public matrices of dimension `d` follows from LWE of
  dimension `n_L` (CVW18 Lemma 3.9, [BLMR13]);
* `2m ≤ m_L` samples (Theorem 5.7);
* `m ≥ 4 t ⌈log q⌉` and `σ² ≥ 4 t ⌈log q⌉` (CVW18 Lemma 4.4: `m ≥ 4n log q`, `σ ≥ 2√(n log q)`,
  with `n = t` rows);
* `0 < χ ≤ σ` (Lemma 5.3: `‖χ‖ ≤ σ`);
* `k ≤ n_L`: statistical terms (smoothing, Lemmas 4.1, 3.12, 3.13) are below `2^{−k}`. -/
structure Regime (p : Params) (t d k : ℕ) (pL : LWE.Params) : Prop where
  q_eq : pL.q = p.q
  secret_eq : pL.secret = .uniform
  error_eq : pL.error = .gauss p.χ
  dim : 2 * pL.n * Nat.clog 2 p.q ≤ d
  samples : 2 * p.m ≤ pL.m
  cols : 4 * t * Nat.clog 2 p.q ≤ p.m
  width : (4 * t * Nat.clog 2 p.q : ℚ) ≤ p.σ ^ 2
  noise_pos : 0 < p.χ
  noise_le : p.χ ≤ p.σ
  stat : k ≤ pL.n

/-- The loss `poly(h)` of one CVW18-type hybrid argument over `h` levels and `t` rows: at most
`4h` LWE steps per row block (phase 1 and phase 2 of the proof of Theorem 5.7) and at most `t`
blocks, with room to spare. -/
def hopLoss (h t : ℕ) : ℕ := 64 * (h + 1) ^ 2 * (t + 1)

/-- The cost `W` that a reduction adds to the distinguisher: sampling and publishing one GGH15
view (`2h` preimages of `m × m` matrices with `t`-row trapdoors over `Z_q`, Gaussians to `k` bits
of precision) in the machine model of `SigabaNeo.Trusted.Machine`, with room to spare. -/
def simCost (h t m q k : ℕ) : ℕ :=
  2 ^ 30 * (h + 1) ^ 2 * (t + m + 1) ^ 6 * (Nat.clog 2 q + k + 1) ^ 4

end AdvancedEncryption.WE.MaskedGGH15
