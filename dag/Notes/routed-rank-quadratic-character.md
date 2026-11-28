---
title: High-rank routed masks, public representatives and a two-byte nonlinear witness release
refs: [definition:WE_CircuitSAT_Capped, definition:RoutedReciprocal, definition:AttainableDictionary, definition:RoutedSliceFixture, definition:RootCharacterRelease, definition:WholeViewRoutes]
tags: [witness-encryption, finite-fields, routed-masks]
---

## A clear evaluator and its complete NO view

Suppose each classical public evaluation returns P(x,s)=b+E(x,s)F(x,s) over the field of 4099 elements. A false NAND fixture admits a rectangular slice with E=1+|x∩s|. The field matrix D=1/E on the first n binary support masks factors as Z diag(c) Zᵀ with subset-incidence Z and c_T=(-1)^|T|/(|T|+1). The integer order is a linear extension of inclusion and the prefix is closed under taking subsets, giving det Z=1. All denominators up to 129 are nonzero. RoutedReciprocal.concrete proves rank n for every n≤2^128. With n=2k+1 the two possible mask explanations differ by D up to sign, so at most one has rank ≤k. This disjoins even message-dependent, coin-correlated masks of bounded rank. A rank-one rectangle needs nine evaluations. The larger tests cost n² public calls and polynomial elimination; no tape-clock bound for that test is implied.

RoutedSliceFixture computes each NAND wire as its native Boolean value and the complement of its selected routed parent; its gate score tests whether the selected parent is one and the other zero. Generate zero via NAND(true,true). For each of 128 inputs use NAND(x,zero), selecting x when s=1, and NAND(zero,first), selecting zero. The pinned outputs are ones and the total charge is |x∩s|. Join the ones with 127 two-gate conjunctions, use 1792 two-gate identity paddings and then NAND(v,v) to reject or NAND(v,zero) selecting zero to accept. The final score includes one when the routed output is zero. The Lean recursor uses a right-associated join and computes each intermediate gate once. Its run_spec gives exactly |x∩s|+1 or |x∩s| respectively, and count proves 4096 gates. Every test contributes by a wire path. The length-128 replay for each j=0,…,128 uses j coincident ones. The fixture models this gate schedule directly; a parser into the registered Boolean circuit encoding remains open.

AttainableDictionary.read and no_view prove a 129-bit table works on these siblings: at each j write the payload if the representative accepts and otherwise a filler bit, which may be deterministic. On the YES sibling every primary witness uses s=0. On the NO sibling even a constant-one table, interpreted as payload zero, implies the full-rank reciprocal mask of short_full. Routing and interpretation are public. A uniformly random 129-bit filler is another option. Reconstruction computes at most 128 bitwise products and a population count then one lookup. The ciphertext size excludes the shared fixture and program. For a general public list, scan_spec, scan_valid and solves give a decision and witness-finding algorithm as soon as one representative passes on each satisfiable input. This is a concrete solver consequence under whatever compiler, enumeration and original-verification costs are available. Missing representatives invalidate the implication. For example, publishing the payload on a gap in a claimed range can leak on NO. An authenticated bank for explicit bounded classical requests, or a secret short formula for a monomial tag, supplies neither this whole public evaluation nor the NO simulation of every field the evaluator transmits.

## A witness relation with no representative list

Let F=F_257, γ=3, and let a be public. A witness z satisfies z²=a. Use two independent fair bytes to select r,s uniformly from F× (add one to each byte, as byte_law proves). In F[Y]/(Y²−a) let U=r+sY, replacing it by 1 when its norm r²−as² vanishes. Publish only the canonical two coefficients of γ^b U². The replacement makes U(z) nonzero for every root. Hence testing whether the value at the supplied root is a square recovers b for every coin pair; this includes the repeated-root case a=0. If a is nonsquare, the norm cannot vanish and there exists t≠0 with at²=γ. Multiplication by tY acts on the coins by (r,s)↦(ats,tr), permutes all 65,536 pairs and scales U² by γ. Thus the *two coefficients together* have exactly the same law on NO. RootCharacterRelease proves this permutation argument for the complete PMF plus the byte specialization. Only the public statement and these coefficients are part of this interface. The coins, norm flag and arithmetic trace are private.

This gives an explicit 18-bit ciphertext (two residues), 16 fair bits, four field multiplications to form r²,s²,as²,rs, then sums, comparisons and scale by three using additions. Opening takes one multiplication and addition to evaluate, seven squarings for exponent 128, then comparison. These are arithmetic counts. The issuer does not compute roots. The relation itself is tractable; the character of public a decides root existence. No reduction from arbitrary NAND to this relation with the claimed registered bounds is known here.

Executable standard Python replay for both worlds and all randomness at the listed parameters:

```python
from collections import Counter
p = 257
for a in (0, 1, 3, 5, 7, 19):
    worlds = [Counter(), Counter()]
    roots = [z for z in range(p) if z*z % p == a]
    for r in range(1, p):
        for s in range(1, p):
            u, v = ((1, 0) if (r*r-a*s*s) % p == 0
                    else ((r*r+a*s*s) % p, 2*r*s % p))
            for b in (0, 1):
                c, d = 3**b*u % p, 3**b*v % p
                worlds[b][c, d] += 1
                assert all(pow((c+d*z) % p, 128, p) == (1, 256)[b] for z in roots)
    assert (worlds[0] == worlds[1]) == (not roots)
```

## Composition and extension boundaries

Independent monotone formulas of such relations admit exact NO hiding of the entire concatenated list. For OR send independent ciphertexts of the same bit. For AND choose a fresh fair share and encrypt that share and its XOR with the bit independently. WholeViewRoutes.complete_no proves equality of list-valued PMFs by induction, including the case in which only the left child of AND loses. Witnesses choose a successful OR branch or supply both AND witnesses and XOR their answers. For L leaves and m ANDs the fixed-formula ciphertext costs 18L raw bits and 16L+m fair bits. Shared witness consistency is an additional constraint: independent openings of “x=0” and “x=1” do not enforce one common x. Publishing the branch openings or sharing the leaf encryption coins also changes the theorem's hypotheses.

For general finite commutative groups, uniform sampler on H followed by f:H→G has shift-invariant full law under γ exactly when γ is in f(H) (WholeViewRoutes.subgroup). Applied to the square map on a restricted unit subgroup this requires a square root within the subgroup, even if γ has roots in the ambient algebra. Arbitrary nonuniform samplers require equality of the actual pushforwards; the two-byte sampler above establishes this directly.

For any Boolean NAND C, the semantic algebra with x_i²=x_i and y²=γ+(1−γ)C(x) splits into 2^128 quadratic fibers. Nonaccepting fibers are quadratic fields and accepting fibers split. Its dimension is 2^129. Over F_3 with γ=−1 send the value of (−1)^b (y²)^k with a fair coin k. NO gives a uniform sign, YES evaluates to (−1)^b. AttainableDictionary.orbit_no proves the one-coin law at the level of canonical sign functions and orbit_correct proves correctness. compare shows that injective canonical encoding with public deterministic evaluation and equality yields a SAT decision by comparing the encoding of the mixed sign with the constant sign. Serializing the raw syntax (b,k) fails even on NO. In public multiplication coordinates one can also compute Frobenius Fr and d_i=dim ker(Fr^i−I). On the displayed fibers the value 2d₁−d₂ is exactly twice the satisfying-assignment count. More generally each local residue degree f contributes gcd(i,f) to d_i by unique lifting of the simple roots of X^(q^i)−X. This yields a decision for compilers promising either a base-field point or a square root of γ. This last general algebra argument is explanatory mathematics, outside the Lean files here. Opaque witness evaluation without a public basis or semantic equality is still open. No typed hardness assumption or all-circuit capped Machine construction is introduced.
