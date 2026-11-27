---
title: Deterministic cover-free partitions for two hidden resource witnesses
refs: [definition:WE_CircuitSAT]
tags: [witness-encryption, composition, cost]
---

Consider a left local witness naming one label x out of N and a right local
witness naming at most q labels Y. Both witnesses can be hidden. Require the
local verifiers and x outside Y. As in the biased-color compiler, assume WE
for each local verifier augmented with the public symbol tests below. This
version gives one public set of partitions working for *all* valid witnesses
and uses no random coloring seeds. Encryption still uses fresh randomness.

Take a prime Q, k>=1 with Q^k>=N, and t=q(k-1)+1<=Q. Encode a label by its
k base-Q digits as coefficients of a polynomial of degree <k over F_Q.
Use t distinct evaluation points. For every point j and symbol a include a
pair of local encryptions with fresh independent encryption coins. Encrypt
a uniform random share s_(j,a) under the left condition P_x(j)=a and encrypt
s_(j,a) XOR m under the right condition that every y in Y has P_y(j)!=a.
Use independent shares across the entire t-by-Q array. The description of
the array and its order is canonical, with no per-pair coloring table.

Each distinct pair of labels can agree in at most k-1 coordinates, by the
polynomial root bound. Even the union of all agreement coordinates with Y
misses a point j. Decryption computes a=P_x(j) and opens just the indexed
pair. This works simultaneously for every disjoint pair, independent of the
encryption coins, up to the underlying local decryption errors. If the
application permits an empty left list, give it a reserved extra label and
use universe size N+1. Enforce valid label encodings in each local predicate.
This uses the classical Reed-Solomon one-hot construction for superimposed
codes of [Kautz and Singleton](https://doi.org/10.1109/TIT.1964.1053689).

On NO statements at least one side of every indexed pair is false. Switching
the message in one pair leaves the true side's share uniform. Embed a leaf
challenge on the false side, sampling the other share and forming the two
challenge messages by XOR. This proves a sum of at most tQ single-leaf QPT
advantage bounds under worst-case nonuniform leaf security: the index and
its false side may be hardwired for the fixed NO input. There is no need
to know either witness to encrypt. Shares are reused only inside their
own indexed pair.

For N>=2 and q>=1, one simple uniform polynomial choice takes a prime
Q>=q ceil(log2 N)+1 below twice that bound (find it by sieving) and the
smallest k with Q^k>=N. Smaller choices can be tested directly. Enc and
ciphertext cost tQ pairs evaluated at the actual augmented leaf costs.
Dec uses O(t(q+1)k) field operations for selection after digit conversion,
plus two leaf decryptions. Multiplying by fixed j is a public operation;
choosing a binary extension field instead can implement fixed-coordinate
symbol evaluation on binary coefficient chunks by an XOR circuit.

For 32-bit labels and q=8, take Q=41, k=6 and t=41, giving 1681 pairs
(3362 leaf ciphertexts) and zero partition failure for every witness.
This is a theoretical item count. The security parameter still affects
every leaf ciphertext. The bound depends polynomially on q and log N
and has no repetition multiplier for negligible partition error. An easy
leaf implementation for unrestricted local NP predicates is still missing;
the construction imposes no new hardness premise besides its leaves.
