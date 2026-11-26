---
title: Successive fixed-LWE embeddings modulo previously hidden output directions
refs: [note:pq-we-anchored-lwe-products, note:pq-we-rank-coded-shifts]
tags: [witness-encryption, reduction, correctness, complexity]
---

**Shared honest law.** Extend the anchored product layout by allowing multiple disjoint right groups. In each of the b rows every group carries independent z uniform in F_q^n and e with b iid errors of the fixed law. Use one common left factor L=[A | I_b | L_rest] across all groups and output blocks, and write P for the left-coordinate inclusion with LP=[A | I_b]. Ordinary honest encryption is still C_i=L K_i R^T+gamma_i Z_m. No intermediate proof masks are transmitted. Rank-one witness correctness and the perfect rank-code decoder hold for this honest law.

**Local step.** Let H be a subspace of the h-dimensional output-index space. The H experiment adds, for every individual b-by-b entry, an independent uniform output vector in H to the full honest transcript. Start at H=0. For one right group J let k_ab be the h-vector of entries K_i[a,J_b] across blocks (here a,b are coordinate indices). Suppose there is a v outside H such that

    k_ab - P_ab v belongs to H for every coordinate pair.

Then the H and H+span(v) experiments have distinguishing gap at most b times the single-secret fixed LWE advantage, including simulation time. To see this, omit the selected group's secret and error columns when forming the other contributions. Conditional on every honest coin, the discarded residual terms formed from k_ab-P_ab v are entrywise in H. Independent uniform H pads absorb the whole residual array even if it is correlated with the other terms. What remains to simulate is v times a matrix of b responses A z_j+e_j. Switch the responses one column at a time at the same public A. Every other group and every nonswitched column of this group can be simulated from known coins. In the uniform endpoint, adding the b-by-b uniform pad along v and the previous H pads gives uniform H+span(v) pads. The omitted honest group may now be restored without changing this endpoint, since its full contribution lies entrywise in that enlarged span. This proves the step without requiring each selected group to simulate the whole message translation independently.

If gamma lies in the final H after k productive steps, the final experiment is message independent. The two-message advantage costs at most 2kb single-secret advantages for the same falsifiable game. The required q,n,b and error law are independent of the statement; no joint hardness assumption for the groups is needed. The claim assumes parameters giving the required actual quantum LWE hardness. The right dimension and honest multiplication costs must include every physical group.

**Which steps are truly new?** Choose any public pivot with P_ab=1. Its k_ab gives the only possible v modulo H. Precompute a group's pivot vector v and all deviations k_ab-P_ab v. It can add v exactly when H contains all deviations. For example, a second group can have independent output patterns v_2 P+v_1 T with T not proportional to P. Once v_1 is hidden, this group adds v_2 even though its raw matrices do not match any single direction. With an explicit polynomial list of groups, iteratively applying these linear inclusion tests reaches a unique closure: every generated vector belongs to any closed subspace containing zero, and exhaustion leaves a closed subspace. At most h strict enlargements occur. Existing groups with v already in H need no further step.

**Boundary of composition.** Any rank-one normalized witness c annihilates every generated H. Inductively c annihilates all deviations in an eligible group, so its moment on J equals (c·v)P. P has rank n+b>1, forcing c·v=0. But normalization requires c·gamma=1. Thus closure containing gamma and a YES witness are incompatible. If every NO circuit compiled to an explicit polynomial group list whose closure contains gamma, computing the closure would decide CircuitSAT in polynomial time. Even exponentially many proof-only local choices do not by themselves avoid the certificate barrier: if each has a polynomial description, validity can be verified in polynomial time and the same honest law is preserved, a successful span chain still has at most h productive steps. Its list is then an NP certificate for the NO case. This rules out this monotone subspace mechanism as a general proof unless NP=coNP. It does not rule out hybrids that change the conditional distribution in other ways and can revisit the same output dimension. No general CircuitSAT fixed-game proof follows.

**Finite checks.** The first check uses the binary vector-space version of the inclusion rules (the reduction above is over prime fields). It compares all processing orders in 120 systems, and verifies a group that becomes usable only after another. The second checks exact absorption of correlated two-entry residuals with independent masks.
~~~python
from itertools import permutations,product
from random import Random
from collections import Counter

def saturate(groups):
    H={0}
    while True:
        size=len(H)
        for v,deviations in groups:
            if all(d in H for d in deviations):
                H |= {x^v for x in H}
        if len(H)==size:
            return H

assert saturate([(2,[1])])=={0}
assert saturate([(2,[1]),(1,[])])=={0,1,2,3}
rng=Random(1081)
for i in range(120):
    groups=[(rng.randrange(8),[rng.randrange(8) for _ in range(rng.randrange(3))])
            for _ in range(4)]
    reference=saturate(groups)
    assert all(saturate(order)==reference for order in permutations(groups))
H=(0,1)
small=Counter()
ideal=Counter()
for secret,rest,p1,p2 in product(range(2),range(2),H,H):
    base=(2*secret+4*rest,2*secret)
    small[(base[0]^secret^p1,base[1]^(secret&rest)^p2)]+=1
    ideal[(base[0]^p1,base[1]^p2)]+=1
assert small==ideal
print("2880 closure orders and joint pad identity verified")
~~~
