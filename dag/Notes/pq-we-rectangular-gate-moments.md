---
title: Orienting NAND operands gives a rectangular rank-one witness compiler
refs: [note:pq-we-private-moment-products, note:pq-we-sparse-moment-completion, note:pq-we-praxis-selector-sketch]
tags: [witness-encryption, compilation, correctness, rank, complexity]
---

Put an anchor 0 on each side of a rectangle. Put every primary input on BOTH sides. Orient each NAND gate's operands (u,v) in either order and put u on the left and v on the right, allowing repeated operands. Write I,J for the resulting anchored lists. A trace supplies M_ij=x_i x_j on I by J, with x_0=1. No other wire pair is reconstructed. The following homogeneous linear equations define the public moment space.

* For every nonanchor wire on both sides equate M_i0 and M_0i. Use either available anchor entry for its wire value. For each input impose M_ii equal to its wire value.
* For a gate (u,v,z) whose output has a wire slot impose value(z)+M_uv=M_00. An unused gate output can be omitted. If the designated output has a slot impose value(out)=M_00. Otherwise it is a gate with no subsequent occurrence, so impose M_uv=0 on that gate's oriented pair.
* A normalized rank-one matrix satisfies M_ij=M_i0 M_0j, as follows from the anchor minor. The shared slots agree and the input diagonal equations force Boolean inputs over any field. Topological induction forces the actual Boolean value on every retained wire. The final output constraint is exactly acceptance. Conversely every accepting assignment supplies the normalized outer product. In particular, imposing Boolean diagonals on all gate outputs is unnecessary for this rank-one equivalence.

Compute a basis K_i of this rectangular linear space and let gamma_i=(K_i)_00. With independent private L,R of respective sizes 2 by |I| and 2 by |J|, use the preceding ciphertext blocks L K_i R^T + gamma_i Z. On an accepting trace they combine to (L x_I)(R x_J)^T+Z. Thus the same rank decoder and error 1/q+1/q²-1/q³ apply with four field elements per basis vector. Choose publicly between the original symmetric and rectangular formats by their actual kernel dimensions to avoid increasing the wire count. This selection costs polynomial preprocessing. Full worst-case honest costs remain polynomial when the modulus bit length is polynomial.

**Dimension control.** Take 32 primary inputs and a chain of 1,024 gates. At gate j use the cyclically selected primary input as its left operand and the previous output as its right operand (another primary input at the first gate). Use the last gate as the designated output. There are 1,056 wires. The rectangle has 33 by 1,056 entries, since the final output has no operand slot. Its kernel dimension is at most 34,848. The uncompressed symmetric compiler has 559,153 coordinates and at most 2,081 equations, hence kernel dimension at least 557,072. Thus the new wire count here is at most 6.26 percent of the old one, at the same q and rank test. This comparison is for this syntactic family and these two compilers; other simplifications of the chain are possible. The orientation idea is related to the operand-cover method in the selector note, but here the two operand lists specify an entire bilinear ciphertext and gate outputs can be inferred without diagonal slots.

**NO boundary.** The Fourier identity for private factors still holds with rectangular block matrices, by character orthogonality over the two independent factor spaces. Its ranks and even its frequency space change on compilation. The upper bound on normalized rank now includes min(|I|,|J|). In particular the YES equivalence and wire reduction alone cannot transfer an old NO-security estimate, let alone prove a general reduction to a fixed falsifiable assumption. Both formats retain the same positive fact that rank ONE normalized solutions are exactly accepting traces. Any general fixed-game comparison must handle higher-rank solutions on unsatisfiable instances.

The small test enumerates all normalized rank-one factors (not just Boolean factors) over F_3 and compares the projected input assignments with direct circuit evaluation. It covers shared slots, all orientations, repeated gate inputs, an output used inside a later gate, an input designated as output, and an unused final gate.
~~~python
from itertools import product

def compare(n,gates,out,orientation):
    oriented=[(b,a) if rev else (a,b) for (a,b),rev in zip(gates,orientation)]
    inputs=set(range(1,n+1))
    left=sorted(inputs|{a for a,b in oriented})
    right=sorted(inputs|{b for a,b in oriented})
    accepted=set()
    for vals in product(range(3),repeat=len(left)+len(right)):
        u=dict(zip(left,vals))
        v=dict(zip(right,vals[len(left):]))
        if any(u[i]!=v[i] for i in set(left)&set(right)):
            continue
        if any(u[i]*v[i]%3!=u[i] for i in inputs):
            continue
        wires=u|v
        ok=True
        for z,(a,b) in enumerate(oriented,n+1):
            result=(1-u[a]*v[b])%3
            if z in wires and wires[z]!=result:
                ok=False
            wires[z]=result
        if ok and wires[out]==1:
            accepted.add(tuple(wires[i] for i in sorted(inputs)))
    expected=set()
    for bits in product(range(2),repeat=n):
        wires=[1,*bits]
        for a,b in gates:
            wires.append(1-wires[a]*wires[b])
        if wires[out]:
            expected.add(bits)
    assert expected==accepted

cases=0
for gates in ([(1,1)],[(1,2),(3,1)],[(1,2),(3,2),(3,4)]):
    for out in range(1,3+len(gates)):
        for orientation in product(range(2),repeat=len(gates)):
            compare(2,gates,out,orientation)
            cases+=1
old=1057*1058//2
print(cases,old,old-2081,33*1056)
~~~
