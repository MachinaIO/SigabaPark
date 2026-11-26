---
title: Non-linear representations of the evaluation oracle - key-switching ladders (with rounding) and homomorphic PRF evaluation, with repairs and why each fails
refs: [definition:WE_CircuitSAT, definition:SuccinctLWE, note:pq-we-evaluation-oracle-crux, note:pq-we-affine-syzygy-barrier, note:pq-we-matrix-collision-barrier, note:pq-we-ggh15-chain-verdict, note:pq-we-hybrid-count-barrier, note:pq-we-escape-routes-verdicts, note:pq-we-decryptor-attribute-dead-end, theorem:AdvancedEncryption.WE.Ladder.ladder_collapse, theorem:AdvancedEncryption.WE.Ladder.prefix_exposure, theorem:AdvancedEncryption.WE.Ladder.hint_collision, theorem:AdvancedEncryption.WE.Ladder.gsw_mul]
tags: [witness-encryption, candidate, attack, barrier, dead-end]
---
Design-AI sub-task on `Def_WE_CircuitSAT`. `pq-we-evaluation-oracle-crux` reduces lattice WE to a
representation `O` of `F_{s,A}(w) = ⌊sᵀ A_{U_w}⌉_p` next to `c_1 = sᵀ(A − φ⊗G) + e`, and
`pq-we-affine-syzygy-barrier` leaves two escapes for a data-only, witness-indexed proof:
(1) decryption of super-constant degree in the ciphertext data, and (2) non-linear processing of
the data (`G^{-1}`, rounding). This note examines the two candidate families that use escape (2)
and do not need trapdoors in the middle (unlike GGH15, `pq-we-ggh15-chain-verdict`):
**key-switching ladders**, with or without rounding between levels, and **homomorphic PRF evaluation
with public evaluation keys**. For each one we tried several repairs. The arguments are informal.
Four algebraic identities used below are theorem nodes with complete proofs
(`AdvancedEncryption.WE.Ladder.*`).

## 0. Normal form of non-linear lattice processing

Everything the decryptor can do with noisy-linear data (short linear combinations, multiplication
by `G^{-1}` of public **or data** values, GSW products, key-switching with hints, rounding)
keeps the form

`y = s_lastᵀ (M − v·G) + err`, with `M` computable from public data and the path, and `v` the
computed value.

* Key switching. `ladder_collapse`: with hints `K_i = s_{i+1}ᵀ B_{i+1} + e_i − s_iᵀ G` and
  `y_{i+1} = y_i + K_i G^{-1}(M_i) + r_i`, every `y_i = s_iᵀ M_i + ε_i` with the public
  `M_{i+1} = B_{i+1} G^{-1}(M_i)`. The perturbation `r_i` is arbitrary, so **rounding between
  levels** (`(q/p)⌊y⌉_p = y + r`, `|r| ≤ q/2p`) only adds a deterministic error. It never creates
  a path-dependent secret, because the secret at level `i` is the hint's secret.
* GSW products. `gsw_mul`: `tᵀ C_1 G^{-1}(C_2) = x_1 x_2 tᵀ G + noise`. Homomorphic evaluation
  stays in the "value times `tᵀ G`" form.
* `G^{-1}` of ciphertext data gives no extra restriction. For `q = 2^k` the binary decomposition
  is a bijection onto bit vectors, so the adversary can substitute any short vector for the
  data-dependent coefficients. The set of samples it can reach is still the short linear closure
  of the data (the linear-closure attack of `pq-we-matrix-collision-barrier`).

So escape (2) never removes the need for the cancellation term `sᵀ M` for some **public** `M`,
which is the object of `pq-we-evaluation-oracle-crux`. What escape (2) can change is **which**
public matrices are reachable: through `G^{-1}` of matrices that depend on the path, the
reachable set is no longer a fixed lattice. Ladders are the natural way to use this.

## 1. Key-switching ladders (the main candidate)

**Construction L.** Secrets `s_0, …, s_n = s`. Public `M_0`, and for each level `i` and bit `b`
a matrix `B_{i,b}` with a hint `K_{i,b} = s_iᵀ B_{i,b} + e − s_{i−1}ᵀ G`. Ciphertext data
`y_0 = s_0ᵀ M_0 + ε`. On `w` the decryptor runs the ladder and gets
`y_n(w) = sᵀ M_n(w) + err` with `M_n(w) = B_{n,w_n} G^{-1}(B_{n−1,w_{n−1}} G^{-1}(… M_0))`
(`ladder_collapse`). The degree in the data is `1`, but the processing is non-linear and the
reachable matrices depend on the path, as in a Banerjee–Peikert tree PRF. Correctness asks for
`M_n(w) = A_{U_w}` for every `w`. Then `y_n(w) − c_1 H_{U_w,φ} = φ(w) sᵀG + small`.

**Intended hybrid.** Positional over `w`: in `H_t` the data on paths `< t` is switched to values
computed from `c_1`, one path per hop, justified by `φ(t) = 0`. No trapdoor is planted anywhere,
which avoids obstruction 2 of `pq-we-ggh15-chain-verdict`.

### Dichotomy

The hints are LWE samples. If for every secret the stacked public matrices on which it is used
(`[A − φ⊗G | B_{n,0} | B_{n,1}]` for `s`, `[B_{i,0} | B_{i,1}]` for `s_i`) are LWE-hard, then
`n + 1` LWE hops from the top down make `(c_1, O)` pseudorandom for **every** `φ`. That is a
polynomial-hop proof with statement-independent premises, so by `pq-we-hybrid-count-barrier`
the scheme cannot be correct. So correctness forces a short public relation between `A` and the
ladder matrices. It is exactly the factorization
`A_{U_{(p,b)}} = B_{n,b} X'_p` with `X'_p = G^{-1}(M_{n−1}(p))`, and recursively below.

* **Structural factorization.** BGG+ evaluation of a branching program (the attribute is a
  width-`W` permutation BP for `φ`, evaluated in the style of Gorbunov–Vaikuntanathan) has exactly
  this ladder shape. The level-`i` ladder matrices are then the attribute matrices
  `A_{i,b,j,j'}`, and the last-level hints lie on matrices that `c_1` also encodes, under the same
  secret `s`. `hint_collision`: `K − c = (P s − s')ᵀ G + noise`, where `P` is the attribute value
  of that entry and `s'` the shift secret. BGG+ evaluation is value-oblivious, so the ladder needs
  hints for the entries `(acc, j')` of both `P_{n,0}` and `P_{n,1}`, and these share the shift
  secret `s'` of the prefix state `j'` (the prefix does not know the next bit). If `φ` depends on
  its last bit, some `j'` has entry `0` under one bit and `1` under the other. Gadget decoding
  gives `s'` and `s − s'`, hence `s`. This holds for
  every `φ`, true or false.
* **Different shift gadget.** Use `K = sᵀ B + e − s'ᵀ G'` with `G' ≠ G`, where `G'` has a public
  trapdoor (the decryptor needs `G'^{-1}`). The factorization needs `B X'_p = A X_p` for all
  prefixes, with `X_p` the short `G`-preimage used by BGG+. If `X_p = S X'_p` for a public short
  `S` (one may define `EvalPK` with these preimages), then `B = A S`. `K − c S` is then
  `(P s − s')ᵀ G' + noise`, which `G'`'s trapdoor decodes. Same leak. If the relation
  `X_p = L X'_p` holds only for a **non-short** `L`, the identity must hold for `2^{n−1}`
  pseudorandom prefix matrices by coincidence. That is a non-structural evaluation collision, which
  `pq-we-matrix-collision-barrier` records as having no known mechanism (generically no common
  `L` exists).
* **Prefix exposure (what survives, and why it is harmless).** Suppose the hint collision were
  avoided. `prefix_exposure`: `y_{n−1}(p) + K X' − c X = P · sᵀ M_p + noise`, so the adversary
  obtains the cancellation term `sᵀ M_p` of the prefix sub-circuit for each component `j'` whose
  last-level entry has `P = 1`. With `c_1`'s encoding `sᵀ(M_p − v_p[j'] G)` this leaks `s`
  exactly when some prefix reaches a state `j'` that accepts under the next bit, i.e. when a
  witness exists. On a false statement this exposure is **value-safe**. It is the only part of
  the ladder analysis that is compatible with security, and it is also why the attack has to go
  through the hint collision above rather than through values.

### Repairs tried

1. **Rounding between levels (LWR ladder).** `ladder_collapse` with `r_i` = rounding error: the
   normal form is unchanged and the hint collision is unaffected. Rounding only makes the errors
   deterministic, which would help a statistical hop but not security. A variant that rounds away
   the gadget term (short secret `s` and `G = I` columns, so `v·sᵀG` vanishes under `⌊·⌉_p`)
   also erases `φ(w)·sᵀG`, so decryption fails.
2. **Per-state shift secrets** (the level-`(n−1)` output for state `j'` under its own secret
   `s'_{j'}`). The two bits `b` still share `s'_{j'}`, because the prefix does not know the next
   bit. Giving each `(j', b)` its own secret is look-ahead: the state then has to record the next
   bit, and pushed down the whole ladder this needs width `2^n`
   (the width bound of `pq-we-ggh15-chain-verdict`, point 3).
3. **Flooding the hint noise beyond gadget decoding.** Decoding the leak needs one level of noise
   below `q/(2‖T_{G'}‖)`, while correctness needs `n` levels of accumulated noise below `q/4`.
   The leak is strictly easier, so no noise ratio separates them. Structured noise that cancels on
   honest paths (`e X'_p = 0` for all prefixes) forces `e = 0`, since the `X'_p` span everything.
4. **Prefix-null values** (make every exposed prefix value `0` on false statements). The ladder
   would then be indexed by `h_p(φ) = ∃y φ(p, y)`, an OR over the subtree. BGG+ computes
   `A_{h_p}` from its children (`h_p = h_{p0} ∨ h_{p1}`), leaf to root, while the decryptor walks
   root to leaf and must obtain the child matrix from the parent. Inverting `EvalPK` at each level
   needs a trapdoor per level, which is the GGH15 shape and its leaf-first obstruction. Computing
   the root `A_{h_ε}` also costs `2^n |φ|`.
5. **Last-level switch to `s` from an independent ladder** (`s_n ≠ s`, one final hint
   `s → s_n`). This moves the factorization requirement one level up. Same dichotomy.
6. **Succinct-LWE public trapdoors** (`Def_SuccinctLWE`) in place of `G'` to give the decryptor
   preimages under the ladder matrices. Any public trapdoor for a matrix on which a secret has LWE
   samples decodes that secret (obstruction 2 of `pq-we-ggh15-chain-verdict`). Succinct LWE is
   safe only because `sᵀ` is never given on `[I ⊗ B | W]` itself; with Wee's identity the
   decryptor can only re-express attributes (`pq-we-decryptor-attribute-dead-end`), which supplies
   no `sᵀ M` term.

**Verdict on ladders: dead.** Without trapdoors, correctness forces a structural relation between
the ladder and the BGG+ matrices. Every structural relation found (shared matrices, a short
change of gadget) puts a hint and an attribute encoding under the same secret on related
matrices, and `hint_collision` decodes the secret for every `φ`. Non-structural relations are
evaluation collisions with no known mechanism. Rounding and non-linear `G^{-1}` do not change this
(normal form).

## 2. Homomorphic PRF evaluation with public evaluation keys

**Construction H.** `O = C`, a GSW encryption under `t` of the bits of `s` (or of `s` itself),
used as a public evaluation key. On `w` the decryptor evaluates `w ↦ F_{s,A}(w)` homomorphically
and gets `C_w` with `tᵀ C_w = F(w)·tᵀG + noise` (`gsw_mul`, iterated). It then needs
`⌊tᵀ C_w⌉`.

**Self-reduction.** `C_w = Eval(w, C)` is publicly computable and `w ↦ ⌊tᵀ C_w⌉` is again a
function of the form `⌊(secret)ᵀ · (public evaluated matrix)⌉`. On a false statement it is also
computable from `c_1` (it equals the bits of `F(w)`). So construction H maps the problem for
`(s, A)` to the same problem for `(t, C)`, and the hybrid-count and function-hiding requirements are
unchanged. Moreover the decryptor may evaluate any circuit on `C`, so decrypting has to be
limited to the honest `C_w`. That restriction is the obfuscation again.

Repairs tried:

1. **Circular security** (`t = s`, `C` a GSW encryption of `s` under `s`). Then `C` plays the role
   of `A`: the needed object is `⌊sᵀ C_w⌉`, the same shape. KDM security makes `C` pseudorandom
   but supplies no decryption.
2. **Key-homomorphic splitting** (`F_s = F_{s+t} − F_t`, with a second BGG+ encoding under `t`
   for the negated statement). By linearity the decryptor gets
   `(s − t)ᵀ(A_{U_w} − φ(w) G) + noise`, which is the normal form with secret `s − t`, again with no
   cancellation term.
3. **Different secrets per witness bit** (multi-key GSW, decrypting along `w`). Combining the
   per-bit keys is a key-switching ladder (section 1).
4. **Compute-and-compare / lockable obfuscation of `Dec_t(C_w) = lock`.** The lock must be output
   on witnesses, so it is encrypted inside `C` and has no entropy given the program. This is
   recorded as dead in `pq-we-escape-routes-verdicts` (section 3); it amounts to null-iO.
5. **BV15 constrained key-homomorphic PRF with a second constrained key** for a never-true
   constraint on independent matrices `A'`. Agreement of the two keys' outputs on all `w` is an
   evaluation collision (`pq-we-matrix-collision-barrier`). On shared matrices it is the
   `X = A` leak of `pq-we-evaluation-oracle-crux`.

**Verdict on H: dead.** The family maps the problem to itself: homomorphic evaluation ends in the
GSW form, and its decryption is the original oracle.

## What remains

Escape (2) of `pq-we-affine-syzygy-barrier` does not escape the evaluation-oracle crux. Non-linear
processing changes which public matrices are reachable but not the requirement of a cancellation
term `sᵀ M`. Without trapdoors, the only way to reach exactly the matrices `A_{U_w}` is a
structural factorization, and structural factorizations leak through hint collisions.

* A ladder whose last-level factorization `A_{U_{(p,b)}} = B_{n,b} G'^{-1}(M_p)` holds with
  `B_{n,b}` **not** a short linear image of attribute matrices. This would need an `EvalPK`
  variant for which such a factorization exists by design. Every BGG+-style evaluation found
  computes products with the attribute matrices as left factors. A different left factor needs an
  evaluation algorithm whose multiplication step has a factor `B` that is unrelated to the
  attribute encodings, yet the result is consistent with them. This is the one sharply stated open
  question from this sub-task.
* Escape (1) with trapdoors (GGH15) needs a GGH15 proof technique that is not leaf-first
  (`pq-we-ggh15-chain-verdict`).
