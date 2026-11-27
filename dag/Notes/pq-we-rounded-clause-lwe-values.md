---
title: Fixed LWE hybrids for correlated rounded clause values at random addresses
refs: [note:pq-we-bch-clause-addresses, note:pq-we-clause-key-sum]
tags: [witness-encryption, reduction, construction, correctness]
---

Replace the bounded-independence address row by a public random function A from traces to uniform rows of (Z/q)^d. Retain independent public dithers D_i modulo h and the deterministic nearest-multiple rounding of the clause-key note, q=ph and h odd. Give coherent XOR access to A(z) and the vector of rounded clause phases at z, replacing each forbidden component by a fixed marker. Key sums and the two message branches are unchanged. The claim here is security of this joint *oracle*, including correlations across all clauses and all queries. The proof uses ordinary decisional LWE samples, not an LWE game selected by the input formula.

**Finite random address table.** First let there be R independently sampled address records indexed by distinct public inputs. Express the zero-branch key matrix as a sum of m-1 independent secret directions v_j=e_j-e_m, each multiplied by its own uniform d-dimensional LWE secret. Use the m directions e_j for the independent branch. Replace the phase contributed by each secret at every record, one secret at a time, by a uniform scalar independent per record. To implement one replacement use R samples (a_l,y_l) from one fixed LWE challenge. Use a_l as the public row, and add v_j y_l to the phase vector along with the earlier uniform scalars and the later real contributions under independently generated secrets. Round *after* adding these terms. In the uniform challenge the next hybrid is exact. In the real challenge the only additional error is +E_l or -E_l in at most two coordinates. For a public uniform dither independent of all phases, changing an integer phase by e changes its bin with probability at most min(1,|e|/h). A union bound over the R records and at most two coordinates costs at most 2R E[|E|]/h per direction. Reusing a clause's public dither across records does not require independence of the bad events. This bounds the entire coupled table before the choice of which entries to expose.

At the end of the zero branch each record carries an independent uniform zero-sum m-vector. At the end of the independent branch it carries an independent uniform m-vector. On a false formula every record hides at least one coordinate. The two projected vectors have the same law, since every assignment to a proper subset of a uniform zero-sum vector has equally many completions. This equality survives rounding with fixed public dithers. For a finite explicit address table the total gap is at most (2m-1)(Adv_LWE(R)+2R E[|E|]/h). It also applies when an arbitrary quantum computation inspects the full *authorized* table. Giving out the unmasked records or secrets is a different experiment.

**Exponential input domain with quantum value queries.** Conditional on fixed keys and dithers, unfiltered records (public row and rounded phase vector) in the real oracle are iid across inputs. Compress that iid oracle in the proof to R iid records and a secret random index map from inputs to [R]. The distinguishing error is O(Q^3/R) for Q queries, by [Zhandry's small-range theorem](https://mzhandry.github.io/files/Thesis.pdf). The wrapper that applies the public clause predicates at the *original input* can compute and uncompute the record with two queries. For efficient simulation take R a power of two and replace the secret index oracle by a sufficiently high-wise independent map (e.g. 4Q-wise for the compute/uncompute implementation); averaging final acceptance uses only those joint moments. Use the finite-table LWE replacements on all records before applying the index map. Different inputs with the same index can expose different components of one record, so the two terminal compressed experiments must **not** be equated directly. Apply small-range switching again on each terminal branch to restore independent per-input random records, then use the proper-subset equality at each input. Switching at both real endpoints and both ideal endpoints costs O(Q^3/R) in total with an absolute constant. The resulting bound is

    O(Q^3/R) + (2m-1)(Adv_LWE(R) + 2R E[|E|]/h).

The classical LWE samples are embedded into polynomial-size reversible oracle circuits; the challenger itself sees neither the formula nor a quantum query. For a putative inverse-polynomial gap and any polynomial Q,m choose a polynomial R large enough for the switching term. To infer negligible advantage for all such choices, require E[|E|]/h negligible and quantum hardness of fixed-parameter decisional LWE for polynomially many samples. Such a rounding step can have polynomial bit length. No concrete LWE parameter strength is claimed. The earlier example h=3 does not establish this asymptotic condition. For honest recovery use the earlier bound with the new h, choosing p sufficiently large compared to sqrt(m); for q a power of an odd prime ell a fixed witness row fails to be primitive with probability ell^(-d). This extra probability must be included. Independent fresh address rows can be obtained for repetitions by domain separation.

**Remaining representation issue.** A public table of all authorized evaluations realizes this interface at exponential size. Publishing the secret index map and all R rounded records from the switching proof would allow combining clauses from different inputs at a common record, and the theorem gives no such interface. A small-range proof simulator depends on the adversary's query bound and advantage; it is not an encryption algorithm. Also, public agreement on a succinctly seeded address map is not modeled by a random-address oracle when the seed is exposed. Succinct public restricted keys and their security still require a separate construction.

The following enumerations check the equality for every proper subset of a zero-sum triple, the change-of-bin bound across wraparound, and the failure of the terminal equality if two differently masked inputs reuse a public record.
~~~python
from collections import Counter
from itertools import product,combinations
q,h,m=9,3,3
allrows=list(product(range(q),repeat=m))
zero=[x for x in allrows if sum(x)%q==0]
for k in range(m):
    for cols in combinations(range(m),k):
        a=Counter(tuple(x[i] for i in cols) for x in zero)
        b=Counter(tuple(x[i] for i in cols) for x in allrows)
        assert all(b[y]==q*v for y,v in a.items()) and a.keys()==b.keys()
def rounded(x): return ((x+h//2)//h)%(q//h)
for x,e in product(range(q),range(-q,q+1)):
    changes=sum(rounded(x+t)!=rounded(x+e+t) for t in range(h))
    assert changes<=min(h,abs(e))
def visible(row):
    return (row[0],row[1]),(row[1],row[2])
assert len(set(map(visible,zero)))==q*q
assert len(set(map(visible,allrows)))==q**3
print(len(zero),len(allrows),q*(2*q+1))
~~~
