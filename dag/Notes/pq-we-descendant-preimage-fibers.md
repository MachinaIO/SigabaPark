---
title: Counting compatible hidden matrices with all descendant preimages fixed
refs: [definition:WE_CircuitSAT]
tags: [witness-encryption, reduction, preimage-sampling]
---

The reachable-target test leaves the conditional law of the published
preimages open. At the ideal coset-sampler interface, these preimages can
be included in an exact likelihood calculation. The following diagnostic
compares distributions analytically; it does not give a fixed-challenge
simulator on its own.

Fix common transition and error coins independent of the remaining hidden
uniform matrix entries a, or an affine uniform parameterization of them.
The prior has size H. Condition only on coins whose prior law is shared by
both experiments. Let t comprise the exposed root R and the actual integer
preimage columns d_j at every included level and branch. Given a hidden
state, suppose those columns have independent conditional mass
p_j(d_j)/Z_j(a,t) on their required syndromes, where p_j is a normalized
ambient Gaussian mass and Z_j is its mass on the required fiber. Sequential
conditional sampling works too if the dependence is on the past transcript.
Assume the experiment has defined samplers on its prior support.

For program b, form F_b(t) from the root equation P A_0=R and every
equation A_(i-1) d_j = S_(b,i,j) A_i + e_j (with the appropriate target
column selected). With t fixed these are simultaneous *linear equations
in the unknown matrix entries*, even though d_j was sampled as a
preimage. Include other linear terminal constraints when present. The
exact joint probability is

    Pr_b[t] = (product_j p_j(d_j))/H
              times sum_{a in F_b(t)} product_j 1/Z_j(a,t).

This follows by summing the conditional sampler probabilities, not by
assuming that the preimages were originally sampled before the matrices.
For an affine uniform prior over the full parameter module, the unweighted
fiber size and consistency are computable by Smith form modulo q. For
a nonuniform trapdoor-generated prior use its actual weights or first
justify replacing it. Nonlinear residual constraints may also invalidate
linear counting. The ciphertext payload must be included or generated
from matched data before inferring full-view security.

**A transferable sufficient bound.** Suppose on selected good hidden
states each mass at column j lies in z_j[1-epsilon,1+epsilon], with
0<=epsilon<1 and common positive z_j (possibly depending on t).
Suppose for every t the number of good compatible states in world 1
is at least that in world 0. Then the good subprobability at t in world
1 is at least f=((1-epsilon)/(1+epsilon))^J times the good subprobability
at t in world 0, with J columns. If world 0 assigns at most gamma mass
to bad states under its actual sampling law, the overlap of the two full
transcript laws is at least f(1-gamma). TV is at most 1-f(1-gamma).
The proof uses no upper bound on a bad state's inverse mass. Counting
all states and then discarding bad states without controlling the good
fiber counts would not justify this estimate.

**Two-preimage control.** Over F_2 take uniform independent a,b and
A=(1,a). Draw two conditionally independent uniform preimages; their
targets are (b,b) in world 0 and (b,b+a) in world 1. Each individual
preimage is uniform in both worlds. Every syndrome has ambient mass
1/2, so the exact joint law on a pair of preimages is proportional to
the compatible (a,b) count. The following computes it both ways.
This finite control checks the transcript calculation, not Gaussian
smoothing or the APG-direct frontier.

~~~python
from collections import Counter
from fractions import Fraction
from itertools import product
laws=[]
for mode in (0,1):
    hist=Counter()
    for a,b,u,v in product(range(2),repeat=4):
        hist[b^(a*u),u,b^(a*mode)^(a*v),v]+=1
    for x,u,y,v in product(range(2),repeat=4):
        fiber=sum(x^(a*u)==b and y^(a*v)==b^(a*mode)
                  for a,b in product(range(2),repeat=2))
        assert hist[x,u,y,v]==fiber
    laws.append(hist)
tv=Fraction(sum(abs(laws[0][t]-laws[1][t])
                for t in product(range(2),repeat=4)),32)
assert tv==Fraction(1,2)
~~~

For the non-co-located flip the remaining concrete target is a comparison
of the *good weighted fibers* after both branches and the subsequent
preimages are included. Equal ranks for the clean reachable rows alone
do not provide this comparison. Neither the required fiber bound for the
actual transitions nor a general NP security reduction is established.

**Localizing one changed target.** At fixed t remove the equations for
the changed block and keep *all* common equations including descendants.
If the common system is consistent with solution a_*+K, write the
remaining test in world b as L_b a=v_b. The unweighted compatible count
is zero if v_b-L_b a_* is outside L_b K and otherwise equals
|K|/|L_b K|. This uses the actual restriction of each changed equation
to the residual kernel. It identifies exactly when downstream preimages
kill a proposed masking direction: they can reduce K even if the clean
target projections at the preceding level have identical image. One
common Smith solve and the two restricted images suffice per transcript
in the affine model. This optimization applies directly to the good
counts only when goodness is automatic on that system or has separately
been accounted for.
