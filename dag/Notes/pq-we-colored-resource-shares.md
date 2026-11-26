---
title: Combining two hidden resource witnesses by biased public colorings
refs: [definition:WE_CircuitSAT]
tags: [witness-encryption, composition, cost]
---

Let local verifiers accept witnesses extracting at most p left and q right
distinct labels, respectively. The combined statement asks for two local
witnesses whose label sets are disjoint. Both local witness spaces may be
implicit. Assume local WE for each verifier augmented with a public color
test on every extracted label. This closure requirement must be established
for any chosen leaf scheme.

Sample T independent public red/blue colorings. In trial i encrypt a fresh
uniform message-length string s_i under the left verifier requiring all
labels red, and s_i XOR m under the right verifier requiring all blue.
Use independent encryption coins. On input a joint witness, compute its
label lists, find the first matching coloring, decrypt both shares for that
trial and XOR. A failure to find a coloring is an explicit decryption
failure. Reusing the same share across trials would allow a left opening
in one trial to combine with a right opening elsewhere.

For an explicit N-label universe, choose each label red independently with
dyadic probability a. Alternatively encode labels injectively in a binary
field of size 2^b >= N and draw a random polynomial of degree below p+q
for each coloring. Compare its value as an integer to a threshold defining
a. Any at most p+q distinct evaluations are independent uniform by
Vandermonde interpolation. This takes (p+q)b seed bits per trial and
O(p+q) field operations per color query. Assume p,q positive (an empty
side's label test is vacuous). A fixed valid pair matches a trial with
probability at least u=a^p(1-a)^q. Failure is at most exp(-Tu).
Choose T >= lambda ln(2)/u for separation error at most 2^-lambda,
plus the sum of the two local decryption errors for the chosen trial.
Choosing the trial using only public colors and the witness keeps the
selected trial's encryption coins fresh. Local correctness here is
worst case over augmented statements, messages and valid witnesses.

The ideal bias p/(p+q) maximizes u. In particular for p=1, q>=1 choose
a=2^(-ceil(log2(q+1))) with b large enough to represent it. Then
a>1/(2(q+1)) and (1-a)^q >= (1+1/q)^(-q) >= 1/e. Consequently
T=ceil(2e(q+1)lambda) suffices even for polynomial q. A fair coloring
would require order 2^(q+1)lambda trials for the same fixed full-size
pair by this scheme. Color coding as a combinatorial technique is due
to [Alon, Yuster and Zwick](https://www.math.tau.ac.il/~nogaa/PDFS/col5.pdf).

**Short seed for one left label.** Pairwise independence already suffices
with a slightly different bias. Choose a=2^(-ceil(log2(2q))) and sample a
random affine polynomial over the field, using only 2b seed bits, where b
also represents this threshold. Conditional on the left label being red,
each distinct right label is red with probability a. The union bound gives
success at least a(1-qa) >= a/2 > 1/(8q), without joint independence of
the right labels. If the left list is empty, the unconditional union bound
also suffices. Thus ceil(8q lambda) trials suffice with one field multiply
and add per color query. The two seed-size and repetition tradeoffs can be
compared before producing the ciphertext.

**Security and cost.** On a NO input every coloring has at least one
false local statement: any two valid monochromatic witnesses in the same
trial would be disjoint. Switch m0 to m1 one trial at a time. If the
right side is false, keep the left share fixed and challenge the right
ciphertext. If the left is false, sample the right share uniformly and
challenge the left on its XORs with m0 and m1. Both simulations are exact.
This is a pointwise, nonuniform reduction: for a fixed NO input, fix public
color coins with signed distinguishing advantage at least its average,
then hardwire them, the trial and its false side. For polynomial T and
polynomial color descriptions this is polynomial advice. The total gap is
at most T times the worst local QPT gap at the resulting simulation size.
This proof requires nonuniform local security and supplies no efficient
procedure for deciding which side is false. Public colorings introduce
no new hardness assumption or iO step.

Ciphertext and encryption cost are T pairs of local encryptions plus
color descriptions and generation; decryption scans at most T(p+q)
colors and invokes just two local decryptions. These bounds are polynomial
for the one-versus-polynomial case provided the augmented leaf costs are
polynomial. Local problems may retain long witnesses. This compiler does
not construct WE for arbitrary augmented leaves, nor express every general
NP consistency condition as one-versus-many disjointness with easy leaves.
