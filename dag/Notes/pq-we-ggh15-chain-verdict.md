---
title: GGH15 chains with LWE data at every level do not give per-witness WE hops from plain LWE (positional Gray-code candidate, leaf-first obstruction)
refs: [definition:WE_CircuitSAT, note:pq-we-evaluation-oracle-crux, note:pq-we-matrix-collision-barrier, note:pq-we-function-hiding-crux, note:pq-we-tree-candidate-crux, theorem:AdvancedEncryption.WE.Gray.adjacent_one_bit]
tags: [witness-encryption, candidate, barrier, dead-end]
---
The previous round of the Design-AI search left one open lead: a witness-indexed WE proof whose
hops change only ciphertext **data**, with decryption of super-constant degree in that data
(constant-degree noisy-linear decryption with succinct ciphertexts admits no such proof, by a
pigeonhole affine-syzygy argument proposed in PR #26). The natural shape is a GGH15 chain with LWE
data at every level, a BGG+ leaf, and per-witness hops that change one level and end in the
`−G` leaf trapdoor (`AdvancedEncryption.WE.Wee.leaf_trapdoor`). This note gives the most
structured candidate of that shape that the search found, its hybrid, and why the hops have no
plain-LWE proof. The arguments are informal. Part of the analysis was cross-checked with a second
AI model. The one precise combinatorial step is a theorem node
(`AdvancedEncryption.WE.Gray.adjacent_one_bit`, with proof).

## Candidate G: positional GGH15 over the reflected Gray order

Notation: `n = 128` witness bits, statement `φ`, BGG+ evaluation `H_{φ,w}` with
`(A − w ⊗ G) H_{φ,w} = A_φ − φ(w) G`.

* **States.** A width-`3(n+1)` read-once branching program: a comparator state in
  `{lt, eq, gt}` (comparison of `w` with a threshold `g` in reflected Gray order), tensored with a
  unipotent state `(1, w_1, …, w_n)`. Level `i` reads `w_i`. The unipotent part is
  `U_{i,b} = I + b E_{0,i}`, so that `e_0ᵀ ∏ U_{i,w_i} = (1, w)`.
* **Encodings.** Trapdoored `A_0, …, A_{n−1}`, a leaf matrix `A_n`, and
  `D_{i,b} ← A_{i−1}^{-1}((M_{i,b} ⊗ S_{i,b}) A_i + E_{i,b})` with
  `M_{i,b} = C^{(g)}_{i,b} ⊗ U_{i,b}`, LWE secrets `S_{i,b}` and Gaussian `E_{i,b}`.
  A variant uses state-dependent secrets (block-diagonal per comparator state), so that the
  `eq`-row secret at level `i` is used only by the paths with prefix `g_{<i}`. The ciphertext
  starts with `a_0 = (J ⊗ sᵀ) A_0 + e`.
* **Leaf.** In accepting comparator rows (`w ≥_Gray g`), row block `0` of `A_n` is
  `[A_1 | … | A_n | A_φ | u]` and row block `k` is `−G` in column block `k`. The path output
  `a_0 ∏ D_{i,w_i}` is then `s_wᵀ [A − w ⊗ G | A_φ | u] + noise`, with path secret `s_w`.
  Rejecting rows carry uniform blocks in place of `A_φ` and `u`.
* **Decryption** for `φ(w) = 1`: `s_wᵀ(A − w⊗G) H_{φ,w} − s_wᵀ A_φ = −s_wᵀ G + small` gives
  `s_w`, which unmasks the message in the `u` block. The degree in the data is `n`, which escapes
  the affine-syzygy pigeonhole: `N^n` monomials are too many to pigeonhole.
* **Hybrid.** `H_g` uses threshold `g`. The real ciphertext is `H_{first}`. In `H_{end}` every
  row rejects, and the message is information-theoretically hidden. Two consecutive codewords
  `g, g'` of the reflected Gray code differ in exactly one bit `j`
  (`AdvancedEncryption.WE.Gray.adjacent_one_bit`). So `H_g` and `H_{g'}` differ **only in the
  level-`j` matrices** `C_{j,0}, C_{j,1}`, and the accepted sets differ only at the path `g`,
  where `φ(g) = 0`. This is the "one hop per witness, one level per hop" structure asked for, with
  `2^n` hops.

## Why the hops fail

**1. Leaf-first obstruction (GGH15 proofs).** Every LWE proof of GGH15 security
(Chen–Vaikuntanathan–Wee 2018 and its descendants) is an induction from the leaf. An LWE hop on a
level-`j` secret needs `A_j` to be a public LWE matrix without a trapdoor in the reduction. But the
level-`(j+1)` encodings are preimages under the whole stacked matrix `A_j`. So they must first be
simulated as Gaussian `D` with target `:= A_j D`, which requires every level-`(j+1)` target to
be pseudorandom, and so on up to `A_n`. The hop at level `j` therefore needs the whole suffix
`j+1, …, n` to be simulatable at once, including the accepting leaf rows that are shared by
exponentially many live paths. On a false statement that simulation is the WE security
statement itself, restricted to a sub-cube, so the induction is circular. Two sub-points:

* the suffix that must be simulated is the whole chain, not the `2^{n−j}`-path subtree whose
  routing changes. The comparator rows share the matrices `A_i`. Giving each state its own matrix
  and trapdoor instead makes the encodings block-structured. The decryptor then reads the
  branching-program graph, which depends on `g`, and distinguishes `H_g` from `H_{g'}` at once;
* the leaf target contains `S_{n,b} G + E` (the unipotent `−G` rows). It is not pseudorandom, so
  the induction cannot even begin in the real scheme. The rows are hidden behind `D_n`. Point 4
  covers what path products reveal.

**2. A reduction that holds a trapdoor for `A_j` cannot use LWE on `A_j`.** With any trapdoor for
`A_j` the reduction samples a short `K` with `A_j K = G`, and `(S A_j + E) K = S G + E K` decodes
`S`. So every planting trick fails, whether the trapdoor is on a column sub-block
(`[A_L | A_R]` with a trapdoor for `A_R` is a trapdoor for the whole matrix) or of the leaf-lemma
form `A_j = [B | B R − G]`. In the second case the reduction cannot even form
`S A_j + E = [y | yR − SG + E']` from an LWE challenge `y = SB + E` without knowing `S`. The `−G`
trapdoor is usable only at the leaf, where no later level needs a preimage. Row-block-diagonal
matrices with no trapdoor on the `eq` block run into obstruction 1 for that block's own
encodings.

**3. Moving the hybrid index to the leaf is impossible or visible.**
* *Width bound.* Suppose the data of levels `1, …, n−k` is the same in all hybrids and hop `t`
  drops one witness, in a fixed order. Then whether `H_t` accepts the path `(p, y)` (prefix `p` of
  `n−k` bits) depends only on the state that `p` reaches and on `y`. Two prefixes with the same
  state are accepted or rejected together in every hybrid, but some threshold separates them. So
  the state map is injective on prefixes, and the width is at least `2^{n−k}`. Leaf-only (`k = 0`)
  hybrids need width `2^n`, and a hop that touches only the bottom `k` levels needs width
  `2^{n−k}`. With polynomial width, some hops must change a level `j ≤ n − log₂(width)`, so obstruction 1
  applies to them.
* *Threshold in the leaf circuit.* The alternative is to keep the routing fixed and put the
  threshold in the leaf circuit, `f_g(w) = φ(w) ∧ [w ≥ g]`, with the leaf block `A_{f_g}`. On every
  non-witness path that block equals the value computed from the attribute block,
  `s_wᵀ(A − w⊗G) H_{f_g,w}`. The decryptor computes this for each candidate `g` and sees which
  matrix the block matches, so it reads `g`. This is the structural-collision problem of
  `pq-we-matrix-collision-barrier` again: an evaluated matrix reveals the circuit.

**4. Attacks on the real ciphertext: the `A_φ` leaf block gives exact zero tests.** On a
non-witness path, `Z_w = (H_{φ,w}; −I; 0)` annihilates the leaf, `(1,w) A_n Z_w = 0`, so
`a_0 ∏ D_{i,w_i} · Z_w` is short. Lifted from `Z_q` it is an **exact integer**
`v(w) = e(w) Z_w`, where `e(w) = e(x) D(y) + s_xᵀ F(y)` for a prefix/suffix split `w = (x, y)` (`e(x)` is the
prefix noise, `s_x` the prefix secret, and `F(y)` collects the suffix noise and secrets).
`H_{φ,w}` depends on all of `w`, but BGG+ multiplication short-circuits. When the left operand of
an AND has value `0`, `H` no longer depends on the other operand's subtree. For a CNF, for
example, any suffix `y` that falsifies one clause makes `Z_{(x,y)} = Z_y` independent of `x`.
On such suffixes `v(x, y) = [e(x) | s_xᵀ] · [D(y) Z_y ; F(y) Z_y]` factors through a fixed
dimension, which is the Cheon–Han–Lee–Ryu–Stehlé zeroizing setting (also used against GGH15
obfuscation by Chen–Vaikuntanathan–Wee). Kernel vectors over the suffixes remove `e(x)` and leave
linear images of the prefix secrets. The second AI model sketched a continuation:
intersecting the spans for `x_j = 0` and `x_j = 1` separates the unipotent rows. Short integer
relations among the `s_x` then cancel row block `0` and leave `(Σ α_t x^{(t)}_j s_{w^{(t)}})ᵀ G`
plus noise, which leaks secrets (the linear-closure attack of `pq-we-matrix-collision-barrier`,
now through zero tests). The submitting agent checked the factorization but not the full key
recovery. In any case the leaf must not carry `A_φ` in the clear. The standard repair is the VWW22
form: leaf blocks `[A − w⊗G | B']` and a public key `K_φ ← [A_φ − G | B']^{-1}(u)`. A non-witness
then yields `s_wᵀ u + s_wᵀ G K_1 + noise`, which is not a zero test. With that repair, the
remaining checks find nothing:
* a single path does not leak `s_wᵀ G` (leaf lemma);
* the linear-closure attack has no exact relations to start from: path secrets differ, and
  there are no zero tests;
* mod-`q` kernel attacks need a noiseless chain or the hidden `A_n`.
The repaired real ciphertext is the GGH15-plus-BGG+ shape of the evasive-LWE witness encryption
of Tsabary (2022) and Vaikuntanathan–Wee–Wichs (2022). Its security from plain LWE is not
established, and the positional structure changes nothing in that. The second model also noted
that a one-level evasive-LWE step at level `n−1` meets the same `−G` rows: its precondition
`(U ⊗ S) P_n + E` is not pseudorandom. The evasive proofs are structured around the projected
leaf `(1,w) A_n`, not around a leaf-first plain induction.

**5. Per-hop assumption.** The leaf hop at a single isolated path (the `eq`-final row, used only
by path `g`) *is* plain LWE: the row secret is fresh, the leaf needs no trapdoor, and
`[A − g⊗G | A_φ]` is simulatable from `S(A − g⊗G) + E` by noise flooding when `φ(g) = 0`. The
problem is that moving the isolated path from `g` to `g'` is a level-`j` hop, governed by
obstruction 1. The assumption that would justify it is "GGH15 encodings of two read-once
programs that agree on all live paths are indistinguishable when the leaf is structured". That is
statement-dependent (the live set is `φ`'s) and of evasive type, so it is excluded.

## Related shapes, same verdict

* **Non-linear processing of the data with `G^{-1}`** (GSW-style chains `C_1 G^{-1}(C_2 …)`).
  This is homomorphic evaluation. The result is an FHE ciphertext of `φ(w)` and must then be
  decrypted conditionally. Conditional decryption is BGG+ with the FHE ciphertext as attribute, and
  its cancellation term is the evaluation-oracle object of `pq-we-evaluation-oracle-crux` (or
  lockable obfuscation, which is null-iO here).
* **Intermediate rounding in the chain** (`⌊a_{i−1} D_i⌉`, BLMR/BP14 style). The `D_i` are
  still trapdoor preimages, so obstruction 1 is unchanged. Rounding only removes the noise.
* **Key-switching chains without trapdoors.** The final key depends only on the last
  level, not on the whole path. There is no path secret, so the per-path gating that the leaf
  lemma needs is absent.

## Conclusion

GGH15-type data chains do escape the constant-degree pigeonhole, and the Gray-code positional
hybrid gives exactly one witness and one level per hop. But the only known LWE technique for
GGH15 is leaf-first induction, so a hop at level `j < n` needs the whole suffix to be simulatable.
That is the WE statement again (obstruction 1), and the width bound forces such hops whenever the
width is polynomial. Trapdoors planted in the middle leak the level
secret (obstruction 2), and a hybrid index placed in the leaf needs exponential width or is
visible (obstruction 3). The candidate as written is also exposed to zeroizing through its
`A_φ` leaf block (point 4); the `K_φ` repair gives the known evasive-LWE scheme. The
lead closes unless there is a GGH15 proof technique that is **not** leaf-first: an LWE hop on a
middle level while the preimages under that level's matrix are still sampled with its trapdoor.
That would need LWE that stays hard on a public matrix while preimages under it are given for
targets of a restricted form, such as `S' A' + E`. With unrestricted targets this is false
(obstruction 2). With restricted targets it is the form of evasive LWE ("preimages of
pseudorandom targets do not help"), which is excluded here. So the GGH15 lead is closed for this
problem, and the remaining open object is the one in `pq-we-evaluation-oracle-crux`.
