---
title: Multi-symbol private moment ciphertexts with perfect witness decoding
refs: [note:pq-we-private-moment-products, note:pq-we-rectangular-gate-moments]
tags: [witness-encryption, correctness, reduction, coding]
---

Public rectangular moment matrices K_i and constants gamma_i are as in the preceding notes. A valid witness gives coefficients c with sum c_i K_i=x_L x_R^T and sum c_i gamma_i=1. Choose b-by-d_L and b-by-d_R independent uniform private matrices L,R, with b>=3. Let E be a fixed linear space of b-by-b matrices over F_q with minimum nonzero rank at least three. Encode the message injectively as Z in E. Send C_i=L K_i R^T+gamma_i Z. The witness sum is the codeword plus an outer product of rank at most one, so unique radius-one decoding always returns the message, including if either projected trace vanishes. There is no field-size-dependent decoding error.

**Payload.** In F_(q^b) fix a public basis and encode b-2 extension-field symbols as the coefficients of the q-linear polynomial sum_(j=0..b-3) m_j X^(q^j). Its values on the basis give the columns of the codeword. A nonzero difference has at most q^(b-3) field roots, hence rank at least three. This is the standard [Gabidulin code](https://www.mathnet.ru/eng/ppi967) with polynomial-time rank decoding. Deleting two rows must be injective on any code correcting every rank-one error, since rank-two differences split into two rank-at-most-one matrices. Thus the b(b-2) field symbols attained here are optimal for this square, worst-case rank-one correction interface. With h blocks the ciphertext takes hb² field elements, or hb/(b-2) field elements per payload field symbol. Honest complexity includes moment compilation, all matrix products, witness conversion and one code decode; these are polynomial for polynomial dimensions, log q, and a supplied field representation. For b=4 this gives eight field symbols in 16h transmitted elements. It changes the NO comparison size from the earlier 2-by-2 setting.

**The exact fixed-game obligation.** For a given false statement let P be the unshifted joint block law and U_E its average under the public shifts (gamma_i Z)_i with Z uniform in E. For any two fixed codewords z0,z1, shift invariance of U_E gives advantage gap at most twice the maximum advantage for P versus U_E with the cost of one public shift added. More explicitly, a single challenge wrapper chooses a fair bit, applies the corresponding shift, runs the original test once, and complements its output in one branch. Its gap is exactly half the original signed gap up to sign, since the two U_E terms cancel. This calculation works with a quantum test on classical ciphertext and never requires the underlying game to know either the circuit or the messages if a separate fixed-game reduction already supplies P versus U_E. The same wrapper works with averaging over the whole matrix space. No hardness of P versus U_E is being postulated here. An existing reduction or bound at a different b must be reestablished at the new size.

For the earlier Fourier identity replace the condition sum_i gamma_i T_i != 0 by sum_i gamma_i T_i outside the trace-pairing orthogonal of E (entrywise dot product over a prime field). These are precisely the frequencies that survive in the squared difference between P and U_E. In particular a security argument needs to hide only codeword translations. The raw compiler's earlier minimum-rank bound remains insufficient for general CircuitSAT. Neither efficient decoding nor optimal payload proves pseudorandomness of these remaining frequencies.

**Finite control.** For b=3, q=2 the code consists of the eight multiplication maps over F_8. The listing exhausts all codewords and all distinct rank-zero/one errors and checks disjoint radius-one balls. It also checks the signed probability identity of the wrapper with exact rational arithmetic on a nonuniform toy distribution.
~~~python
from fractions import Fraction
from itertools import product

def multiply(a,b):
    result=0
    for _ in range(3):
        if b&1:
            result^=a
        b>>=1
        a<<=1
        if a&8:
            a^=11
    return result

code=[sum(multiply(a,1<<j)<<(3*j) for j in range(3)) for a in range(8)]
errors={sum((u if v&(1<<j) else 0)<<(3*j) for j in range(3))
        for u,v in product(range(8),repeat=2)}
received={}
for message,z in enumerate(code):
    for error in errors:
        word=z^error
        assert word not in received
        received[word]=message
assert len(errors)==50 and len(received)==400
P={0:Fraction(1,3),1:Fraction(2,3)}
def accept(x):
    return int(x.bit_count()%3==1)
def shifted(z):
    return sum(p*accept(x^z) for x,p in P.items())
for z0,z1 in product(code,repeat=2):
    real=(shifted(z0)+1-shifted(z1))/2
    ideal=sum((shifted(z^z0)+1-shifted(z^z1))/2 for z in code)/len(code)
    assert real-ideal==(shifted(z0)-shifted(z1))/2
print(len(received),"unique decodes and 64 exact wrapper checks")
~~~
