---
title: A witness-tree WE candidate from succinct LWE - the leaf step is provable, the internal step is FE (hence iO)
refs: [definition:WE, definition:WE_CircuitSAT]
tags: [witness-encryption, candidate, barrier]
---
This note follows the hybrid-count barrier (`pq-we-hybrid-count-barrier`, open PR), which says a
statement-independent proof must walk over the `2^128` witnesses. It records the most promising
tree-structured candidate found so far and where its proof stops. The design and the analysis
came from a second AI model and have **not yet been checked line by line**; the two claims marked
(C1) and (C2) are the ones to verify first.

## Candidate (sketch)

A depth-128 binary tree over the witness bits, in the style of the BV15/AJ15 tree that turns FE
into iO:

* **Node `w_{≤i}`:** a BGG+ / circular-GSW ciphertext of a node state. The state is a PRG seed,
  the prefix `w_{≤i}`, a mode bit and the message. It is compressed with Wee's succinct-LWE public
  trapdoor `T^{(i)} ← [I_ℓ ⊗ B^{(i)} | W^{(i)}]^{-1}_σ(I_ℓ ⊗ G)`.
* **Children:** for each child bit `b`, a statement-independent circuit `F_{i,b}` expands the seed
  with Goldreich's PRG and outputs the child's ciphertext. The decryptor evaluates it
  homomorphically and obtains the child by rounding, using a transition key
  `K_{i,b} ← B^{(i)}^{-1}(u_{F_{i,b}})`.
* **Leaf `w`:** the statement enters only here, through a key
  `K_leaf ← [B^{(n)} | A_φ − G]^{-1}(u_leaf)`, where `A_φ` is `EvalPK(φ, A_wit)`.
* **Decryption:** walk the path `w` and open the leaf when `φ(w) = 1`.

## Proof structure (depth-first, about `2^131` hops; premises of about 400 bits)

* **Leaf base case, (C1): provable from ℓ-succinct LWE (`Def_SuccinctLWE`) alone.** For a leaf
  `w*` with `φ(w*) = 0`, Wee's identity
  `(I ⊗ B) T_B + W T_W = I ⊗ G` gives `A_wit,j = B R_j + w*_j G` with `R_j` short. BGG+ evaluation
  then gives `A_φ = B R_φ + φ(w*) G = B R_φ`, so `A_φ − G = B R_φ − G` has a `−G` trapdoor, and
  `SampleRight` simulates `K_leaf` without a trapdoor for `B`. Succinct LWE then switches the
  leaf's LWE part to uniform, and the leftover hash lemma hides the message.
  **Here the local fact `φ(w*) = 0` does the work.**
* **Internal step, (C2): the crux.** To switch a node from "expand the seed" to "output fixed
  ciphertexts", one needs the distribution
  `(B, W, T, A_W, K_{i,0}, K_{i,1}, c_0, c_1, x̂)` to hide which of two inputs with equal
  `F_{i,b}` outputs is encrypted. Honest decryption forces `K_{i,b}` to be authorized on *every*
  prefix, since whether a subtree contains a witness is NP-hard to tell. So no `−G` trapdoor
  appears, and simulating `K_{i,b}` needs a trapdoor for `B^{(i)}`, which breaks the LWE hop. The
  needed statement is **2-key succinct functional encryption for statement-independent circuits**.
  By BV15/AJ15, that already implies iO.

## Conclusion

The witness tree moves all of the difficulty into an internal-node lemma that amounts to
FE ⇒ iO. That is excluded for this problem (no route through iO, in substance as well as in
name). It is also a restricted cousin of the circular/private-coin assumptions broken by
Hopkins–Jain–Lin (2021).

What *is* reusable:

* **The leaf lemma (C1)** is a statement-independent, provable step: an "unauthorized leaf is
  simulatable from succinct LWE" lemma. It is worth stating and proving in the DAG for any later
  design.
* **The open question** sharpens to: is there a witness-indexed hybrid whose *internal* steps are
  also justified by local facts, so that they are not FE? Any such structure must avoid giving the
  decryptor keys that are authorized on all prefixes. Positional WE (Gentry–Lewko–Waters 2014)
  achieves this with multilinear maps; a lattice analogue of its positional assumption that is
  statement-independent and falsifiable is the missing piece.

Known attacks considered by the analysis, none of which breaks the real ciphertext:

* orthogonal-lattice attacks on `T_W` (defeated by `m_W > kL`);
* exact noise extraction from rounded outputs (defeated by smudging `r_frac`);
* the HJL21 covariance attack (it hits the naive proof, not the scheme);
* mod-`q` kernel attacks on noiseless GGH15 chains (the reason for using BGG+ with noise).
