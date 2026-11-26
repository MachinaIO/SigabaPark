---
title: Post-quantum WE from combinations of different tools (garbling, group actions, LPN/codes, SPHF, local PRGs, compute-and-compare over lattices) - interface dichotomy and verdicts
refs: [definition:WE_CircuitSAT, definition:WE_CircuitSAT_Capped, definition:WE_MaskedGGH15, note:pq-we-summary-2026-11, note:pq-we-route-survey, note:pq-we-non-lattice-algebras, note:pq-we-gap-structure-routes, note:pq-we-hybrid-count-barrier, note:pq-we-function-hiding-crux, note:pq-we-evaluation-oracle-crux, note:pq-we-affine-syzygy-barrier, note:pq-we-proof-system-routes, note:pq-we-direct-algebraic-languages, note:pq-we-native-hop-designs, note:pq-we-multipass-ggh15, note:pq-we-two-input-abe-secret-key, note:pq-we-decryptor-attribute-dead-end, theorem:AdvancedEncryption.WE.Combine.two_query_label_release, theorem:AdvancedEncryption.WE.Combine.tag_free_consistent, theorem:AdvancedEncryption.WE.Combine.leakage_chain, theorem:AdvancedEncryption.WE.NativeHop.nand_reach_saturate, theorem:AdvancedEncryption.WE.NativeHop.zero_entry_hint, theorem:AdvancedEncryption.WE.Direct.nand_gadget_affine_closure, theorem:AdvancedEncryption.WE.LinearVerif.check_alternative, theorem:AdvancedEncryption.WE.LinearVerif.sph_perfect_hiding, theorem:AdvancedEncryption.WE.TwoInput.rect_leak, theorem:AdvancedEncryption.WE.Codes.card_le_of_sparse_preimages, theorem:AdvancedEncryption.WE.Hybrid.hardAt_chain, note:we-circuitsat-bruteforce-explicit-cost, note:pq-we-zero-entry-crossing, theorem:AdvancedEncryption.WE.ZeroCross.shift_overlap_card]
tags: [witness-encryption, strategy, barrier, dead-end, combination]
---
Design-AI sub-task (qq) on `Def_WE_CircuitSAT_Capped` (NAND Circuit-SAT, 128-bit witness, `2^12`
gates, `λ = κ = 128`, cost `≤ 2^100`). The owner asked not to stay inside lattices and to look for
**hybrid** designs in which different tools each cover what the others cannot, aimed at the known
obstacles: mix-and-match of per-bit encodings, both labels of a wire, the affine closure of
`nand_gadget_affine_closure`, and the SZK / hybrid-count barrier. Allowed tools: LWE family,
LPN, codes, isogeny group actions, Goldreich / local PRGs, MQ, hash functions in the standard
model, lattice SPHFs, garbled circuits, OT, one-way functions. Forbidden: iO and relatives,
evasive LWE, local mixing, statement-dependent assumptions, pairings.

The three `Combine.*` theorems have complete Lean proofs (Mathlib only). Everything else is an
informal argument, checked step by step by the submitting agent; no second model was used. Open
PRs of the DAG are cited by number only.

## 0. Answer

* **No hybrid design with a complete proof was found, and none beats the lattice-only frontier**
  (APG / MP2, about `2^{97}` bits, one LWE hop missing across a zero program entry, `pq-we-zero-entry-crossing`).
* **A dichotomy explains why (§1).** A combination either passes an *exact value* between tools
  in the clear (a rounded key, a label, a group element), or one tool evaluates *over the hidden
  encodings* of another.
  * Clear interfaces add nothing beyond Goldreich–Levin: the scheme is exactly as secure as the
    *unpredictability* of the value passed (§1.1).
  * Hidden interfaces need a public homomorphic evaluation with short preimages. Among the
    allowed tools only lattices have one. So every hidden-interface hybrid has a lattice carrier,
    and the other tools act inside it, where they only lower cost.
* **Per combination (§2–§8).**

| # | Combination | Verdict | Obstacle hit |
| --- | --- | --- | --- |
| 1 | garbled circuit + one-label-per-bit release (LWE / LPN / SPHF / commitments / group action) | dead | `two_query_label_release` (decomposable release); decryptor-chosen commitments = decryptor-attribute dead end; path-dependent labels need key-homomorphic tables = lattice carrier |
| 2 | group action enforcing consistency between GGH15 passes | dead | parallelization dichotomy: clear exponents are an additive map (`nand_gadget_affine_closure`); hidden ones cannot be combined by the honest decryptor |
| 3 | LPN / codes for the XOR part + lattices for NAND | no gain | XOR of independent parts is a secret-sharing combiner (security = best part); coupling through a clear value is §1.1; through hidden values needs the lattice carrier |
| 4 | SPHFs for algebraic sub-languages + reduction of Circuit-SAT to their AND / OR | dead | SPHF = linear template (`check_alternative`, `sph_perfect_hiding`); circuit-derived relaxed systems are always solvable; a statistical smoothness step puts `L` in SZK |
| 5 | local PRG for per-path fresh noise + LWE encodings | no gain | per-path pseudorandomness already exists in GGH15; small noise floods only short shifts, the zero-entry leak is uniform; decryption-side locality is constant degree |
| 6 | compute-and-compare / lockable obfuscation (or a one-way function) for the final extraction, lock from a lattice or group-action evaluation | no gain | Goldreich–Levin already turns search security into decision security; CC obfuscation needs the lock's pseudo-entropy given the *plain* program, which is the WE statement; leakage per witness hop must be `< 1` bit (`leakage_chain`) |
| 7 | (own) whole-string PRF tags across passes | removes mixing, but collapses to read-once | `tag_free_consistent`; read-once is APG, whose gap is not about mixing |

* **Most promising, and the precise gap (§9).** The only combination aimed at the gap that
  actually binds is (6) applied to APG's read-out: hide the exposed left-vector combination of
  APG inside an obfuscated read-out. It fails by self-reference. WZ17's premise is the lock's
  pseudo-entropy given the **plain** read-out program, which contains that combination, and that
  premise is APG's own security. The residual statement is unchanged: `ZF_Ψ` of `pq-we-zero-entry-crossing`, "Lemma
  4.4 of CVW18 with one exposed root row". **Mix-and-match is not the binding obstacle**: APG is
  read-once (no mixed strings) and still misses that lemma. Consistency gadgets, even perfect
  ones, therefore cannot close the gap.
* **Cost.** Unchanged: about `2^{97}` bits (APG/MP2), under the `2^{100}` cap but unproven.
  Brute force (`we-circuitsat-bruteforce-explicit-cost`) remains the only complete submission.

## 1. The interface dichotomy

Let a scheme use tools `X` and `Y`. An **interface** is what the honest decryptor passes from
`X`'s data to `Y`'s data.

### 1.1 Clear interfaces: everything reduces to unpredictability of one value

Suppose the decryptor computes, in the clear, a value `K(w)` from `CT_X` and `w`, with
`K(w) = K*` for every witness `w`, and `Y` then uses `K*` (as a key, a lock, a label, a group
element, an exponent).

* **Search suffices.** If `K*` is unpredictable given `CT_X` on false statements, then
  `(CT_X, r, ⟨K*, r⟩ ⊕ μ)` is a WE ciphertext. This is Goldreich–Levin, in the standard model, with
  no random oracle. So the best any `Y` can achieve is what Goldreich–Levin already gives.
* **Search is necessary.** If an adversary predicts `K*` from `CT_X` on a false statement, it runs
  `Y`'s honest decryption with `K*`, so no post-processing `Y` is secure.
* **Consequence.** With a clear interface, `Y` (a KDF, a group action, a point or
  compute-and-compare obfuscation, a garbled circuit keyed by `K*`) is interchangeable with
  Goldreich–Levin. The whole difficulty is "search-WE for `X`".

When the interface carries per-position values (labels for each input bit), the decryptor may
also evaluate it at several candidates and mix the results. §2 shows that this already breaks
decomposable releases.

### 1.2 Hidden interfaces: only lattices offer one

For `Y` to act on `X`'s encodings without decoding them, someone must evaluate a function of the
statement on hidden data with public information. The three non-lattice families fail at this:

* **Codes / LPN.** Public evaluation needs sparse preimages of arbitrary targets, and
  `card_le_of_sparse_preimages` bounds the number of reachable targets
  (`pq-we-non-lattice-algebras` §2).
* **Regular group actions.** Combining two hidden elements is the parallelization problem
  (`pq-we-non-lattice-algebras` §1).
* **Goldreich PRG, MQ.** There is no public homomorphism at all.

Lattices (BGG+, GGH15, GSW) have one. Hence a hidden-interface hybrid has a **lattice carrier**.
The other tools sit inside it, as computations evaluated homomorphically: a PRG lowers the depth,
and an isogeny or LPN computation becomes an ordinary circuit. In that role they are
statement-independent sub-computations, which lattices can evaluate already. They can only change
the cost of the carrier, not the missing lemma.

## 2. Combination (1): garbled circuit + one-label-per-bit release

**Scheme.** `CT = (GC(φ), Rel)`: a Yao garbling of the verifier `φ`, with input labels `L_{i,b}`,
plus a static release mechanism `Rel` from which the decryptor obtains `L_{i,w_i}`. `Rel` could
be labels encrypted under LWE / LPN keys, or under SPHF hash values keyed to commitments of the
witness bits, or keys derived from group-action set elements. Correctness: with a witness, the
decryptor evaluates `GC` on `(L_{i,w_i})_i` and obtains the output-1 label, which unlocks `μ`.
Fan-out inside `GC` is free, so consistency across uses is automatic **inside** the garbled
circuit. The only question is the release.

**Barrier (three exhaustive cases).**

1. **Decomposable release.** The label of wire `i` (use `u`) extracted from the public data
   depends on the candidate only through `w_i`. By `two_query_label_release`, the two runs
   `w = 0^n` and `w = 1^n` give **both** labels of every input wire at every use. With both input
   labels, every garbled row opens, and `nand_reach_saturate` yields the output-1 label on every
   statement. This needs two runs, not `2^n`: no "one-way consistency" gadget helps, because the
   decryptor never has to be inconsistent *within* a run.
2. **Decryptor-chosen release** (SPHF on a commitment that the decryptor creates, OT-style). A
   static ciphertext cannot react to the decryptor's commitment. The hash must be computed
   publicly as a function of that commitment, which is ABE with a decryptor-chosen attribute:
   the dead end of `pq-we-decryptor-attribute-dead-end`. Concretely, the decryptor commits to `0`
   in one run and to `1` in another, and case 1 applies.
3. **Joint (path-dependent) release.** The extracted labels depend on the whole `w`. Then the
   garbled tables are static while the keys come from `2^{128}` different paths. A table entry
   decryptable under `2^{128}` related keys is a key-homomorphic (ABE / GGH15) object, so the
   garbled circuit's job is taken over by a lattice carrier (§1.2). That is the lattice frontier.

**Assumptions / cost.** Each piece (garbling from OWF, LWE / LPN release, SPHF) is falsifiable and
statement-independent, and the ciphertext would be about `4 · 2^{12} · κ ≈ 2^{21}` bits. But case 1
breaks every statement, and cases 2–3 are not new routes. **Dead.**

## 3. Combination (2): a group action to make GGH15 passes "meet" only on equal bits

**Idea.** Pass `p` at level `i` reading bit `b` applies a class-group element `g_{p,i,b}`. By
commutativity, the final set elements of two passes agree exactly when the multisets of applied
elements agree, and the hope is that this happens only when both passes read the same bits.

**Dichotomy.**

* **Hidden exponents** (only `g ⋆ x_0` is published). The honest decryptor would have to apply
  `Σ_i g_{p,i,w_i}` to a set element without knowing any `g`, which is the parallelization
  problem. Every element it can reach is `(g ± ℓ_j) ⋆ x_0` with `g` known in the clear
  (`pq-we-non-lattice-algebras` §1). So the scheme is not correct.
* **Clear exponents** (the decryptor knows the `g`'s). The meeting test depends on the read string
  only through an additive map into the class group. `nand_gadget_affine_closure` holds for
  **every** additive map, so its relaxed combinations defeat the test exactly as for LWE / LPN
  encodings. Commutativity makes things *worse* than GGH15: it forgets the order, which is the
  only thing that blocks the closure in non-commutative products
  (`pq-we-direct-algebraic-languages` §2.2).
* **Group action only as a final equality check** between two rounded GGH15 outputs
  (`k_1 ⋆ X_A = k_2 ⋆ X_B`). This is a two-term test `k_1 − k_2 = b − a` with a hidden offset, that
  is, a point-function obfuscation of a clear value. That is the clear interface of §1.1.

The non-commutative analogue that does enforce "same bits on both passes" is a whole-string tag
computed by the lattice carrier itself (§7). **Dead** as a non-lattice contribution.

## 4. Combination (3): LPN / codes for the XOR part, lattices for the nonlinear part

**Scheme.** Split the Tseitin system of `φ` into its linear part (XOR / parity rows, encoded with
dual-LPN or a code) and its NAND part (masked GGH15). The decryptor obtains
`K = K_lin(x) ⊕ K_nl(x)` on a wire assignment `x`.

* **Independent shares.** If the two parts have independent randomness and `μ = μ_1 ⊕ μ_2`, the
  scheme is a secret-sharing combiner. It is secure iff at least one part is secure. The linear
  part is broken by the one-gate relaxation (`pq-we-direct-algebraic-languages` §2.2), so the
  scheme is exactly as secure as the lattice part alone.
* **Does the nonlinear layer block the affine closure?** Over `F_2` the relaxed decryption of the
  linear part is the XOR of its decryptions at three Boolean points `P_{00}, P_{01}, P_{10}`
  (coefficients `±1 ≡ 1`). The attacker obtains the lattice part at those same three points, but
  GGH15 values are not XOR-linear across points, so the closure does not transfer to `K`. This
  blocks the attack only because the lattice part is **already** a full WE on its own: it alone
  separates consistent satisfying points from the rest. The linear part contributes nothing to
  security.
* **Coupled designs.** Coupling the parts through a clear value (a rounded lattice output selecting
  LPN data, or the reverse) is §1.1. Coupling through hidden values needs public evaluation over
  LPN data, which the sparse-preimage lemma excludes; over lattice data it is the carrier.
  Hamming noise also cannot enter a GGH15 level additively: a lifted bit error is a shift by
  `q/2`.

**Cost.** LPN part about `2^{30}` bits, lattice part about `2^{97}`: no saving, since the lattice
part must still contain every NAND level. **No gain.**

## 5. Combination (4): hash-proof systems for sub-languages, Circuit-SAT as AND / OR of them

**Scheme.** Reduce `φ` to a conjunction (with shared variables) or a disjunction of languages with
lattice or linear SPHFs (Katz–Vaikuntanathan; Benhamouda et al.'s diverse vector spaces, which
cover AND and, by tensoring, OR). Encrypt `μ` under the combined hash.

* **SPHFs are the linear template.** For the algebraic (diverse-vector-space) languages, the hash
  is `k·v` with projection `kᵀM`. `check_alternative` and `sph_perfect_hiding` show that it is
  hiding exactly when `Mπ = v` has no solution, and determined by the projection key otherwise.
  NAND constraints are not linear, so the sub-languages must use linearized (relaxed) variables.
  For circuit-derived systems a relaxed solution with one violated gate always exists
  (`nand_gadget_affine_closure`, `pq-we-direct-algebraic-languages` §2), so the combined hash is
  determined on every false statement. OR via tensoring keeps the system linear in the tensored
  witness, and the same relaxation applies.
* **Lattice (approximate) SPHFs** are for languages of ciphertexts, where the witness is the
  randomness. Circuit-SAT statements contain no such ciphertexts, and the encryptor cannot create
  them for an unknown witness. Decryptor-created ones are case 2 of §2.
* **SZK barrier.** Smoothness is one statistical step. A reduction that keeps it statistically
  sound puts `L` in SZK (`pq-we-hybrid-count-barrier`; case 2 of the dichotomy in
  `pq-we-proof-system-routes` §1). A computationally sound reduction makes the inner statement
  true on most false `φ`, and `check_alternative` then opens the hash. There is no "mechanism
  against the SZK barrier" within SPHFs: the only one known is about `2^{128}` witness-indexed
  hops, and SPHF smoothness gives none of them.

**Dead.**

## 6. Combination (5): local PRGs for per-path fresh noise

**Question.** In GGH15 the noise of `V(z)` on different paths is correlated (it is built from shared
preimage errors). Does a local PRG supply 2^128 independent-looking noise terms that LWE cannot?

* **Per-path pseudorandomness is already there.** The CPRF / mask block of masked GGH15 is a
  BPR-type product `s ∏ S_{i,z_i} A`, pseudorandom per path under LWE. A local PRG computed
  inside the carrier only lowers the depth (`pq-we-non-lattice-algebras` §3).
* **Small per-path noise cannot do what the proof needs.** At a zero entry, `zero_entry_hint`
  makes `(S a + E') D` short, so the sample `S a + E'` is not fresh. Replacing it by a fresh
  sample, which is what the hop needs, changes that quantity from short to uniform. The values of
  the live strings that depart there then move by a uniform-sized shift. Flooding with small noise hides only shifts much smaller than the flood (`shift_overlap_card`,
  `pq-we-zero-entry-crossing` §5), and noise wide enough to hide a uniform shift destroys correctness.
* **Noise the decryptor can compute is not noise.** If the PRG output is computed in the clear
  from `z` and a public seed, it is subtracted. If it acts on ciphertext bits at the decryption
  side, the decryption has constant degree and the degree-`D` affine-syzygy argument applies
  (`pq-we-affine-syzygy-barrier`).

**Cost:** unchanged (`≈ 2^{97}`). **No gain.**

## 7. Combination (6): compute-and-compare / one-way-function extraction

**Scheme.** `CT = (CT_lat, CC.Obf(P, y, μ))`, where `P(w)` is the decryptor's extraction from
`CT_lat` (a rounded GGH15 / BGG+ value, or a group-action set element derived from it), and `y`
is its common value on witnesses. Compute-and-compare obfuscation exists from plain LWE
(Wichs–Zirdelis, ePrint 2017/276, abstract read: distributional VBB "as long as ... `y` has
sufficient pseudo-entropy given `f`"; Goyal–Koppula–Waters, ePrint 2017/274, for a lock that is
uniform and independent of the program).

* **Correctness:** with a witness, `P(w) = y`.
* **What it needs:** `y` pseudo-entropic given `P`. On false statements this is the search
  (HILL-entropy) form of the WE security of `CT_lat`, which by §1.1 Goldreich–Levin already
  exploits. GKW17's independence of the lock is false on true statements, and an encryptor
  cannot tell the cases apart. So (6) is WE ⇒ WE, as `pq-we-native-hop-designs` (e) found for
  CC alone.
* **Does search buy room per hop?** A search premise tolerates leakage: a hop that leaks `ℓ` bits
  multiplies the prediction probability by `2^ℓ`. `leakage_chain` gives the bound over a chain:
  `f_0 ≤ K^T f_T + ε Σ_{i<T} K^i`. The barrier of `pq-we-hybrid-count-barrier` forces
  `T ≈ 2^{128}` hops. With a key of `k ≤ 2^{100}` bits (`f_T = 2^{-k}`) and a target `f_0 ≤ 2^{-λ}`,
  this requires `ℓ · 2^{128} ≤ k − λ`, i.e. **less than `2^{-28}` bits per hop**. That is
  indistinguishability in all but name.
* **Caveat.** Whether *poly-hop* proofs of unpredictability with genuine leakage hops escape the
  SZK barrier is not settled by the statistical-distance argument. Computational hops do not
  preserve conditional Shannon entropy, so the Entropy-Difference version (Goldreich–Vadhan) does
  not go through as stated. The purely statistical search version does fall into SZK, through
  Entropy Difference. We found no leakage hop that is valid only on false statements, so this is
  recorded as an open point, not a route.
* **Group-action lock** (`y = κ ⋆ x_0`): the lock is still a clear value computed from `CT_lat`,
  so the same verdict applies.

**Cost:** `+ poly(λ)·|P|` for the obfuscation, i.e. at least the lattice carrier again.
**No gain.**

## 8. Own combination (7), and why consistency is not the binding obstacle

**Whole-string consistency tags.** In a two-pass masked GGH15 layout, add two γ⊗ blocks with
the same short secrets: one reads pass 1 and adds `+h(z^1)`, the other reads pass 2 and adds
`−h(z^2)`, with `h(z) = s ∏ S_{i,z_i} A` (no zero entries). A consistent string has
`h(z^1) − h(z^2) = 0` up to noise. A mixed one carries a pseudorandom difference.
`tag_free_consistent` (Lean): if a linear combination of mixed evaluations
`m + h(a_j) − h(b_j) − C_1(a_j) − C_2(b_j)` cancels every tag formally, it **equals** a
combination of consistent evaluations `m − C_1(x) − C_2(x)` with weights
`ω(x) = Σ_{a_j = x} c_j`. So against linear (zeroizing-type) attacks, tags remove everything that
mixing adds, unlike equality clauses, whose sums over bit positions admit rectangle cancellations
(`rect_leak` is the same phenomenon for additive per-slot secrets). This is the
consistency gadget that §2 and §3 asked for, realized in the lattice carrier. Cost: two more
blocks of width `n'`, under one bit on top of `2^{97}`.

**Why it does not close the gap.**

* `pq-we-multipass-ggh15` §2–§3 shows that, for ERASE / projection proofs, multi-pass escapes
  the read-once width bound **only through mixed strings** (regime (d)). Perfect consistency
  turns the scheme back into regime (a), the read-once bound. So tags make MP2's proof harder.
* The read-once design with no mixing at all is APG (`pq-we-native-hop-designs` §6), and its gap
  is the zero-flip lemma `ZF_Ψ` (`pq-we-zero-entry-crossing`). This gap concerns crossing a zero program entry
  under a row reachable from the public read-out, not mixing.
* **Hence no consistency mechanism**, whatever tools build it (labels, commitments, group actions,
  tags), can supply the missing lemma: with perfect consistency one lands at best on APG.

## 9. Most promising combination and its precise gap

The binding obstruction (`pq-we-zero-entry-crossing` §2) is that the slot rows of APG are reachable from the public
combination `r = (J'_O − J'_C)·Ā_0`. That blocks CVW18's phase 2, while the zero child blocks
phase 1. The only tool combination that targets `r` directly is (6) applied to the read-out:

* **Design.** Publish the preimages `D_{i,b}` as in APG, but give the left vectors only inside a
  compute-and-compare obfuscation of `z ↦ ⌊r·D_z⌉`, with lock = the rounded mask and payload `μ`.
  Correctness is that of APG.
* **Assumptions.** LWE for GGH15 and for WZ17. Both are falsifiable and statement-independent.
* **Hybrid count.** That of APG: about `2^{129}` hops, premises of about 400 bits.
* **Cost.** That of APG, `≈ 2^{97}` bits, plus an obfuscated read-out of size `poly(λ)·L·m`.
* **Gap (self-reference).** WZ17's premise is that the lock has pseudo-entropy given the **plain**
  program, and the plain program contains `r`. So the premise is APG's security with `r` public,
  i.e. the original statement. The obfuscation hides `r` only *after* that premise is proved. It
  cannot be used inside the proof of its own premise. GKW17 avoids premises by taking the lock
  independent of the program, but on false statements that independence is the WE claim itself.
* **Intrinsic.** Every WE has a public read-out. Hiding it requires obfuscating that read-out, so
  the zero-entry gap is a statement about the lattice carrier with one public row. In the words of
  `pq-we-zero-entry-crossing`, it is "Lemma 4.4 with one exposed root row", and no non-lattice tool reaches it (§1.2).

**Net result of the sub-task.**

* Six combinations and one new gadget were checked. Two are dead, (1) and (2), with exact
  barriers. Three, (3), (5) and (6), reduce to the lattice part alone, and (4) is dead.
* The consistency gadget (7) works against linear attacks but collapses to read-once.
* The single open lemma of the frontier is unchanged and has now been shown to be independent of
  mixing and of the choice of auxiliary tools.
