---
title: Witness PRFs from a constrained PRF plus a masked evaluator - the reduction, the canonical-deviation attack, relation to the evaluation-oracle crux, and a masked GGH15 candidate
refs: [definition:WE, definition:WE_CircuitSAT, note:pq-we-evaluation-oracle-crux, note:pq-we-hybrid-count-barrier, note:pq-we-function-hiding-crux, note:pq-we-matrix-collision-barrier, note:pq-we-affine-syzygy-barrier, note:pq-we-ggh15-chain-verdict, theorem:AdvancedEncryption.WE.MaskedEval.subtract_identity, theorem:AdvancedEncryption.WE.MaskedEval.mask_leak, theorem:AdvancedEncryption.WE.MaskedEval.otp_hop]
tags: [witness-encryption, candidate, attack, barrier, strategy]
---
Design-AI sub-task (l) on `Def_WE_CircuitSAT`: build WE through a **witness PRF** (Zhandry,
"How to Avoid Obfuscation Using Witness PRFs", TCC 2016, ePrint 2014/301). The plan is to start
from a constrained PRF (Brakerski–Vaikuntanathan, TCC 2015, ePrint 2015/032, "BV15") and remove
the dependence of its output on the witness. The human's concrete form of the idea is a *masked
evaluator*:

> `O(x, w) = CPRF(k, (x, w)) + PRF(k', x)` together with the constrained key `ck` of `k` for the
> NP verifier `C`. With a witness, `O(x, w) − CPRF(k, (x, w)) = PRF(k', x)` is a witness-independent
> witness-PRF value. On a false `x` no point `(x, ·)` is constrained-evaluable, so `CPRF` masks
> `PRF(k', x)` at every `w`.

Summary of findings (informal, except the three theorem nodes, which have complete proofs in this
PR):

1. **The reduction is sound** (§2). A masked evaluator with the security game of §2 gives a witness
   PRF, and a witness PRF gives WE with loss 2 (`otp_hop`). In the ideal-oracle model the masked
   evaluator is secure from a single-key CPRF with multi-point pseudorandomness plus a PRF, in
   polynomially many hops.
2. **With the simplest BGG+ CPRF, the statement-independent evaluator is broken**
   (`mask_leak`, §3). The deviation of a BGG+ constrained key off the constraint is the fixed vector
   `sᵀG`. One trivially true statement reveals it, and then every mask `PRF(k', x)` leaks. BV15's
   actual PRF (`⌊sᵀA_x G⁻¹(D_x)⌉`) has a point-dependent deviation `sᵀD_x` and avoids this.
3. **Relation to the crux** (§4). For one statement and the simple BGG+ CPRF, the masked evaluator
   *is* the evaluation oracle of `pq-we-evaluation-oracle-crux`, and the mask is redundant. In
   general it is a relaxation with two new degrees of freedom (the CPRF and the mask). All
   data-only lattice instantiations (BGG+ encodings, key homomorphism, succinct-LWE trapdoors) fall
   back to the evaluation-collision barrier. The only instantiation that changes the picture is
   GGH15.
4. **Candidate: masked γ⊗-GGH15 WE** (§5). This is the CNF candidate of Chen–Vaikuntanathan–Wee
   (CRYPTO 2018, ePrint 2018/360, "CVW18", Construction 10.1) with a **witness-independent message
   block**. That block is exactly the human's "removal of witness dependence": decryption returns
   a canonical key instead of a small/large test. It survives the subtraction attack that CVW18
   (Remark 10.3) found against naive γdiag-WE, and a rank attack on the two left vectors fixes how
   they must be chosen. Its security needs one lemma (§6). By the barrier that lemma must use the
   falsity of `φ`. CVW18's LWE theorem (Thm 5.7 / Cor 5.9) covers one left vector, and we show that
   no correct WE can live inside it.

## 1. Witness PRFs and WE

Zhandry's Definition 3.1 (p. 16): `Gen(λ, R) → (fk, ek)`, `F(fk, x) → y`, and a deterministic
`Eval(ek, x, w)` with `Eval(ek, x, w) = F(fk, x)` if `R(x, w) = 1` and `⊥` otherwise. Security
(Definition 3.2, "adaptive instance interactive"): given `ek` and `F`-queries, `F(fk, x*)` is
pseudorandom for a challenge `x* ∉ L` that was not queried.

* **wPRF ⇒ WE.** `Enc(φ, μ)`: `(fk, ek) ← Gen`, output `(ek, F(fk, φ) + μ)`. The view of an
  adversary is `(ek, y + μ_b)`, where `y` is real or uniform. `otp_hop` bounds the WE advantage by
  the sum of two real-or-random advantages (the ideal term is shift-invariant). Fresh keys per
  ciphertext suffice, so only the **single-statement, non-interactive** notion is needed for
  `Def_WE_CircuitSAT`. That notion is *equivalent* to a WE key encapsulation. So the witness-PRF
  route is not easier than WE. Its value lies in the *shape* of the construction it suggests.
* **Removing witness dependence.** Abstractly, a constrained PRF gives `w ↦ Eval(ck, (x, w))`, and
  a "remover" is a public map `R_x(w, ·)` that sends every valid evaluation to one value `z`. For
  BGG+-type keys the remover always exists and is linear (`subtract_identity`): for every point
  `O(z) − EvalCt(z) = mask + f_z(x)·sᵀG + noise`. So the witness dependence of the *constrained key*
  is never the problem. The problem is the other operand, the master value `F(w)` at a witness,
  which the key does not give. The masked evaluator is a precise name for the object that supplies
  it.

## 2. The masked-evaluator primitive and its reduction

**Syntax.** `KeyGen → (k, k')`; `ck ← Constrain(k, C)` for the fixed verifier `C(x, w)`
(statement-independent); `Ô ← EvGen(k, k')`, a program with `Ô(x, w) = CPRF(k, (x, w)) + PRF(k', x)`
for all `(x, w)`. The program **does not check the witness**: it is a fixed, witness-oblivious
function family. The check is delegated to `ck`.

**Correctness.** If `C(x, w) = 1` then `Ô(x, w) − ConstrainEval(ck, (x, w)) = PRF(k', x)`
(CPRF correctness on evaluable points; here BV15's convention is flipped so that `ck` evaluates
where `C = 1`).

**Security game MEV(x*)** (static instance, the notion WE needs). Challenger samples the keys and
gives `(ck, Ô, y_b)` with `y_0 = PRF(k', x*)` and `y_1` uniform. Advantage
`|Pr[A = 1 | b = 0] − Pr[A = 1 | b = 1]|` is required small for every `x* ∉ L`. (An adaptive
version adds `PRF(k', ·)` queries at `x ≠ x*`. That is Zhandry's game for the wPRF
`ek = (ck, Ô)`, `F = PRF(k', ·)`.)

**Theorem (wPRF, then WE).** MEV-security for `x*` is literally wPRF security for `x*`, and
`otp_hop` turns it into WE security for `φ = x*` with loss 2.

**Ideal-oracle model (the human's argument, made precise).** Replace `Ô` by oracle access to `O`.
Let the CPRF have *multi-point unconstrained pseudorandomness* (MPU): given `ck` and evaluation
queries at points outside a set `Q` of non-evaluable points (`|Q|` polynomial, chosen adaptively),
the values on `Q` are jointly pseudorandom. Then MEV holds in polynomially many hops.
(1) Replace `PRF(k', x*)` by a uniform `u` in the challenge and in every oracle answer at `x*`
(PRF security; answers at `x ≠ x*` use the PRF oracle and CPRF evaluation queries, which are
allowed because those points are not in `Q`). (2) The answers at `x*` are `CPRF(x*, w_i) + u`,
and the points `(x*, w_i)` are all non-evaluable because `x* ∉ L`. MPU replaces them by
independent uniform values, and `u` disappears from the view. BV15's Definition 3.1 has no
evaluation queries after the challenge, so MPU is a (standard-looking) strengthening that we have
not checked against BV15's admissible-hash proof. There is no contradiction with
`pq-we-hybrid-count-barrier`, because the oracle is not part of the ciphertext.

**What the proof needs without an oracle.** The natural standard-model proof is a hybrid over
`w ∈ {0,1}^128` for the fixed `x*`. Hop `t` changes the program's behaviour at `(x*, t)` from
`CPRF + PRF(k', x*)` to `CPRF + u`, justified by the local fact `C(x*, t) = 0`. That is a
puncturing argument on `Ô` (iO in the folklore proof), i.e. function hiding for equivalent
programs (`pq-we-function-hiding-crux`). Without iO the hop has to change only *data*, and the
data-only barriers (`pq-we-affine-syzygy-barrier`) apply unless the representation of `Ô` leaves
their scope (§5 does, through trapdoors).

## 3. The canonical-deviation attack (theorem `mask_leak`)

Take the CPRF to be the plain BGG+ one: attribute `x` (the description of `C`), point circuits
`f_z`, master value `s·EvalF(f_z, A)`. The constrained key evaluates to
`s(EvalF(f_z, A) − f_z(x) G) + noise`. `subtract_identity`: for **every** point,
`D(z) := O(z) − EvalCt(f_z, c) = P(stmt z) + f_z(x)·sG + noise`.

**Attack.** Pick a trivially true statement `x_0` with a known witness `w_0` and a non-witness
`w_1` (so the two values `f(x)` differ by 1). Then `D(x_0, w_1) − D(x_0, w_0) = sG + noise`.
`mask_leak` states the algebra exactly: for every target point `zs`,
`D(zs) − f_zs(x)·(D(z_1) − D(z_0)) = P(stmt zs) + (an explicit short combination of errors)`.
So the statement-independent evaluator leaks **every** mask, including those of false statements.
(With rounding, the errors become `±1` rounding terms; the statement is exact before rounding.)

**Consequences.**
* For the plain BGG+ CPRF the mask is redundant even for one statement. With `P = 0` the scheme is
  `pq-we-evaluation-oracle-crux`, whose secret `sᵀG` already plays the role of the mask.
* A secure statement-independent evaluator needs a CPRF whose deviation off the constraint is not
  one fixed vector: every unconstrained value must stay pseudorandom given the constrained key
  *and* other unconstrained values (MPU). BV15 does this (overview §2, "Pseudorandomness and
  Adaptive Security"): `PRF_s(x) = sᵀ A_x G⁻¹(D_x)` with `D_x` from an admissible hash, so the
  deviation is `sᵀD_x`, a fresh PRF value per point.
* **Repair tried and attacked: binary randomized deviation.** Put an encrypted key `κ` in the
  attribute and evaluate `C(z)·h_κ(z)` with bit outputs, so that the deviation is
  `Σ_j h_j(z)·σ_j` with `σ_j = sᵀG_j`. The adversary obtains these deviations at points of true
  statements. They are random **binary** combinations of the unknown `σ_j`, i.e. a hidden subset-sum
  instance (Nguyen–Stern). The orthogonal-lattice attack recovers the `σ_j`, and gadget decoding
  then gives `s`. Large-coefficient deviations are not available in BGG+ (values are bits), which is
  why BV15 multiplies by a separate LWE matrix `D_x` instead.

## 4. Relation to `pq-we-evaluation-oracle-crux`

* **Special case.** Crux = masked evaluator with the plain BGG+ CPRF, `P = 0`, restricted to one
  statement (the statement as attribute instead of as input; both are BV15 keys). Every solution
  of the crux solves the masked-evaluator problem.
* **Relaxation.** The masked evaluator allows any CPRF and an independent mask. It is not
  obviously harder than WE (it is sufficient for WE and, for one statement, WE plus this
  representation is all it asks for).
* **Data-only lattice instantiations collapse back to the crux.**
  1. *Key homomorphism.* With `PRF(k', x) = ⌊s'ᵀB_x⌉` and a key-homomorphic CPRF,
     `O(x, w) ≈ ⌊(s, s')ᵀ [M_{x,w}; B_x]⌉`: a BV-type master function under the joint key. The
     mask is absorbed, and the evaluator is the crux's object for the stacked matrices.
  2. *BGG+ encodings under `(s, s')`* on matrices other than those of `ck`: the evaluator's
     evaluations must coincide with `ck`'s on all `2^128` points. That is an evaluation collision
     (`pq-we-matrix-collision-barrier`), whether structural (reachable by constant circuits) or
     non-structural (no known mechanism). On the same matrices: the `X = A` leak of the crux note.
  3. *Succinct-LWE public trapdoors* only re-express attributes and give no `sᵀM` term
     (`pq-we-evaluation-oracle-crux`, consequence 3).
  4. *GGH15* (preimage chains with trapdoors) is outside the data-only barriers. §5.

## 5. Candidate: masked γ⊗-GGH15 WE

**Ingredients** (CVW18 §5, Construction 5.1). A γ-GGH15 encoding of per-level secrets `Ŝ_{i,b}`:
hidden trapdoor matrices `A_0, …, A_h`, `D_{i,b} ← A_{i−1}⁻¹(Ŝ_{i,b} A_i + E_{i,b})`, so that
`A_0 D_z ≈ Ŝ_z A_h` (`Ŝ_z = ∏ Ŝ_{i,z_i}`). CVW18 prove (Thm 5.7, Cor 5.9) under LWE that for
`γdiag(M, S) = diag(M, S)` and `γ⊗diag(M, S) = diag(M ⊗ S, S)`, with *arbitrary* (even
`S`-dependent) `M`, the encodings are pseudorandom given `aux = ({S_{i,b}}, J·A_0, top rows of A_h)`
for **one** `J = (J' | I_n)`.

**Construction.** `φ` is fixed, so the levels read the witness only. Convert `φ` to a CNF `Ψ_φ` over
`w` and the gate values (Tseitin; the satisfying assignments correspond to the witnesses one to
one). Take its read-once diagonal branching program `M_{i,b}` (CVW18 Construction 6.4, width = number
of clauses, `M_z = 0` iff `Ψ_φ(z) = 1`, otherwise `M_z = diag(unsatisfied-clause indicators)`).
Per level:

`Ŝ_{i,b} = diag(R_i, M_{i,b} ⊗ S'_{i,b}, S_{i,b})`

* `R_i` is a **bit-independent** random secret, the *mask block*. Its product `R_* = ∏R_i` is the same
  for all `w`; this is the removal of witness dependence;
* `M ⊗ S'` is the *constraint block* (γ⊗ as in CVW18's WE);
* `S` is the *CPRF block*: `S_z A_h^{bot}` is the human's `CPRF(k, (φ, w))`.

Two left vectors: `u_O = J_O A_0` (mask block and CPRF block) and `u_C = J_C A_0` (constraint block
and CPRF block), with `J'_O = 1_n ⊗ e_mask` and `J'_C = 1_n ⊗ j_C` (see the rank attack below). Then

* `O(z) := u_O D_z ≈ mask + S_z A^{bot}` (the masked evaluator, with `mask = r_0 R_* A^{mask}`),
* `ck(z) := u_C D_z ≈ C(z) + S_z A^{bot}` with `C(z) = (j_C M_z ⊗ s'_0 S'_z) A^{con}`.

The ciphertext is `(u_O, u_C, {D_{i,b}}, ⌊mask⌉ + μ)` (or a hard-core bit of `mask`).
**Decryption:** `O(z) − ck(z) ≈ mask − C(z)`, which equals `mask` up to noise when `z` satisfies
`Ψ_φ` (`M_z = 0`).

**Attacks checked.**
1. *Subtraction (CVW18 §9.3.1).* `u_O − u_C` gives `mask − C(z)` on every path: the CPRF block
   cancels, as intended. With a **plain** constraint block (γdiag, `C(z) = j_C M_z A^{con}`) this is
   fatal: `C(z) = Σ_{k ∈ U(z)} a_k` over the unsatisfied clauses, and an inclusion–exclusion
   combination (paths with unsatisfied sets `{k}`, `{l}`, `{k, l}`: `+1, +1, −1`) isolates the
   mask with coefficients `±1`. γ⊗ prevents it: `C(z)` carries the path product `s'_0 S'_z`, so no
   short combination with `Σα ≠ 0` cancels it, except through the low-rank structure below. This
   is why the message block must be `R_i` and the constraint block γ⊗.
2. *Rank of the left vectors.* `u_O − u_C = (J'_O − J'_C) A_0^{top}`. If the rows of
   `J'_O − J'_C` separate the mask block from the start vector of the constraint block, the
   adversary learns `A_0^{mask}` and computes `A_0^{mask} D_z ≈ R_* A^{mask}`, i.e. the mask.
   Repair: rank-one difference (`J'_O = 1_n ⊗ e_mask`, `J'_C = 1_n ⊗ j_C`), so that only
   `A_0^{mask} − j_C A_0^{con}` is exposed and every exposed product carries the mask with
   coefficient 1.
3. *Public `S`.* CVW18's theorem tolerates publishing the `S_{i,b}`. Here that is fatal: `ck(z)` is
   linear in the unknown `(A^{con}, A^{bot})` with coefficients the adversary could compute. So
   the `S_{i,b}` stay secret (we do not need them in `aux`).
4. *Bit-independent mask block.* `D_{i,0} − D_{i,1}` annihilates the mask block (an encoding of
   zero there). The resulting values are differences `O(z) − O(z')` of honest evaluations, which
   are mask-free and carry no new information. No zero test on the full encoding exists (the CPRF
   block never vanishes).
5. *Low-rank-plus-noise.* The values `mask − C(z)` lie near an affine space `mask + V` of dimension
   `n'·(#clauses)`. Exact knowledge of `V` would recover the mask (intersect the affine spans of
   single-unsatisfied-clause paths `{k}` and `{l}`). With noise this is a lattice problem, and it is
   infeasible under the usual GGH15 condition `n' ≫ log(q/β)·λ` (the same parameter constraint as
   in the positional GGH15 candidate). This is a parameter requirement, not an attack.
6. *Mixed-input paths.* The BP is read-once over `w` with the statement fixed, so every path is an
   assignment. Tseitin makes the extended witness unique per `w`, so inconsistent gate values are
   just more non-witness paths.

In the honest-linear-algebra (generic) model the scheme is secure on false `φ`. Every computable
quantity is a short combination `Σα_z (mask − C(z))`, plus mask-free terms, and isolating the mask
needs `Σα_z C(z) ≈ 0` with `Σα ≠ 0`. That requires a short relation among the path products, which
the γ⊗ structure and the parameter condition of attack 5 exclude.

## 6. Why the proof must leave CVW18's theorem, and the missing lemma

**No correct WE lives inside CVW18 Thm 5.7.** The theorem is a polynomial-hop LWE proof that
holds for *every* `M`, true statements included. Any WE whose ciphertext is
`(J A_0, {D_{i,b}}, c)` for a single admissible `J`, with the message component `c` a function of
`μ`, of the theorem's `aux` and of the (arbitrary, possibly random) `M`-blocks, would satisfy a polynomial-hop,
statement-independent proof, contradicting `pq-we-hybrid-count-barrier` (or correctness). The
candidate leaves the theorem in exactly one place: the **second left vector** (equivalently, the
exposure of the top-row combination `A_0^{mask} − j_C A_0^{con}`). That is the human's subtraction.

**Missing lemma (masked two-vector lemma).** For `Ψ_φ` unsatisfiable and the construction of §5
(secret `S, S', R`, hidden `A_i`, rank-one `J'_O − J'_C`):

`(u_O, u_C, {D_{i,b}}, mask)  ≈_c  (u_O, u_C, {D_{i,b}}, uniform)`

with loss `2^{|w|}·poly(h)·ε_LWE` allowed (witness-indexed hops; `2^128` hops fit the accounting of
`pq-we-hybrid-count-barrier` at premises of about 384 bits). The intended hop at a non-witness
path `t` is local: the constraint block at `t` has `M_t ≠ 0`, so path `t`'s value carries
`C(t) = (j_C M_t ⊗ s'_0 S'_t)A^{con}` with the path secret `S'_t`. The open step is to re-randomize
the contribution of `t` alone without touching the shared prefix and suffix encodings. This is the
same "split" difficulty as the accept-class split of the positional GGH15 candidate (open DAG PR
#42 at the time of writing), now in the γ⊗ setting, where CVW18's techniques do give LWE proofs
for a single left vector. A natural first instance is `h = 2` levels with a two-clause CNF.

## Verdict

* The human's masked evaluator is the right *interface*: statement-independent, witness-oblivious,
  correct by one subtraction, and secure in the oracle model from a multi-point CPRF in polynomially
  many hops. It does not escape the hybrid-count barrier in the standard model.
* With BGG+-type CPRFs and data-only evaluators it is the evaluation-oracle crux again. The plain
  BGG+ CPRF additionally breaks the statement-independent version (`mask_leak`).
* Most promising lead: the masked γ⊗-GGH15 candidate of §5, a WE candidate with a canonical key
  (witness dependence removed by a bit-independent mask block). It is not covered by CVW18's
  Remark 10.3 attack, and it has a single sharply stated missing lemma (§6).
