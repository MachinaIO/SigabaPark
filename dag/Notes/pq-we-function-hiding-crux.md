---
title: Witness-indexed hybrids for WE need function-hiding for equivalent circuits (tree and positional alike)
refs: [definition:WE, definition:WE_CircuitSAT]
tags: [witness-encryption, barrier]
---
This note generalizes the internal-node crux of the witness-tree candidate (PR "pq-we-tree-candidate-crux")
to the other natural witness-indexed design. It is an informal argument, not a Lean proof.

**Positional (threshold) design.** Let the ciphertext carry a key for
`C_t(w) = φ(w) ∧ [w ≥ t]`. Real ciphertexts use `t = 0`, and the hybrids move `t` from `0` to
`2^128`, in the style of Gentry–Lewko–Waters' positional WE. Since `φ(t) = 0` on a false
statement, `C_t` and `C_{t+1}` are **functionally equivalent**. Each hop therefore needs keys for
two functionally equivalent circuits to be indistinguishable. This is *function hiding* on the
key side.

**Tree design.** At internal nodes the transition keys are authorized on every prefix. A hop
replaces "expand the seed" by "output fixed child ciphertexts"; the two transition functions agree
on the relevant inputs but are different circuits. This again needs function hiding for
(statistically) equivalent functions, i.e. 2-key succinct FE.

**Common cause.** In both designs only the *function inside a key* changes between hybrids,
while its input–output behavior does not. Lattice ABE keys (BGG+: a preimage of `A_C`) reveal
`C`, so the step needs keys that hide which of two equivalent circuits they are for. With succinct
ciphertexts that is FE, and FE ⇒ iO (BV15/AJ15). This explains why every construction in the
survey goes through iO, evasive LWE (which postulates the hiding), or an ideal model.

**What would escape.** A witness-indexed hybrid in which each hop changes the *ciphertext's
encoded data* at one position, using that the candidate `w` fails, while every key stays fixed.
The leaf step of the tree candidate does exactly this: it changes an LWE sample, justified by the
`−G` trapdoor that `φ(w*) = 0` creates (proved algebraically as
`AdvancedEncryption.WE.Wee.leaf_trapdoor`, open PR). The open problem is to obtain decryption
along a witness path without per-node keys whose function changes in the proof, for instance
with a single global key, and data-only hops over all `2^128` positions.
