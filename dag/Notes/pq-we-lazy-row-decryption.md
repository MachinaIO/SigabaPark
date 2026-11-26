---
title: Expected decryption work from prefix-rank survival
refs: [definition:WE_CircuitSAT, note:pq-we-tensor-rank-survival, note:pq-we-rectangular-levels]
tags: [witness-encryption, correctness, complexity]
---

For the centered-shortness decoder, a single long terminal entry certifies output one. Evaluate one selected root row through the entire chain, check all of its terminal entries, and stop at the first row containing a long entry. Return zero after all rows pass. This yields exactly the eager decoder's bit, including on malformed values of the correct shapes, and changes no encryption coins or ciphertext fields. The row calculation is ordinary left-associated modular matrix multiplication. In particular the row-wise method never uses more scalar multiply-adds than the same eager multiplication. It has data-dependent work and is intended for local decryption when timing observations about the decrypted bit are acceptable.

**Expected cost per message bit.** Fix a valid witness independently of encryption coins. With d retained root rows, let e_r upper-bound the probability that the first r ideal tensor rows jointly vanish modulo p after all H factors. Compute all these bounds by running the rank recursion once with initial rank r for its query. The rank proof permits any fixed r standard rows. For a message one, if these r rows survive, at least one of the corresponding ideal terminal rows has a unit coefficient modulo the prime-power q. The terminal-matrix argument in the rank note then bounds the probability that every tested entry looks short by the sum of e_r, ((4B+1)/q)^t and the terminal-key distance delta. This also covers correlated bounded residuals. No independence between successive row tests is needed. With T the number of evaluated rows, summing Pr[T>r] for r from zero to d-1 bounds the expected row count by one plus the sum of these clipped bounds for r from one to d-1. Multiply by the dense cost of a single row through the chosen chain. A zero message on a valid witness always incurs d rows under the same residual bound. This is a fixed-witness expectation over encryption coins.

**Equalizing expected work across messages.** Optionally sample a fresh independent uniform classical bit u, send u, and encrypt message XOR u. XOR the decoder output with u. For either plaintext the expected cost is the mean of the two conditional expected costs; the worst case stays d rows. Given a selector for a WE challenge on two messages, a hiding reduction samples u first, submits the two correspondingly shifted challenge messages, and appends u to the challenge ciphertext. This preserves the distinguishing advantage in the two-message game, including for a quantum distinguisher with classical challenge messages. Correctness transports by the same XOR identity. The change adds one public bit and one random bit per encrypted bit plus constant-time bit operations. The distribution of the pair consisting of the public mask and observed decryption timing can still depend on the plaintext; this transformation only equalizes the marginal expected work. Ciphertext hiding for false statements remains conditional on the underlying WE scheme.

**Numerical accounting.** Reuse the prior correctness example H=8, n=d=9, t=13, m=15490 and q=7^81. Exact rational arithmetic certifies fewer than 1.015876 expected rows for a fixed valid message-one path. The eager decoder takes 12,958,577,730 modular multiply-adds. The message-one bound is at most 1,462,699,904 and the public-mask version gives at most 7,210,638,817 for either bit. These are rounded-up expectations for the matrix arithmetic, excluding input access, packed-column decoding and threshold checks. Streaming a packed matrix once per attempted row can incur extra I/O or unpacking. The eager count remains the worst-case arithmetic bound. The example supplies a correctness budget, with quantum hiding and security-matched lattice dimensions still open. The listing checks the arithmetic bounds and compares both scan modes with a full matrix-product oracle over 1,350 toy chains.

~~~python
from fractions import Fraction
from pathlib import Path
from random import Random

def scan(root, factors, q, bound, eager=False):
    """Return the output bit and the number of modular multiply-adds."""
    work = 0
    long_entry = False
    for initial in root:
        row = initial
        for matrix in factors:
            work += len(row)*len(matrix[0])
            row = [sum(x*y for x,y in zip(row,col)) % q for col in zip(*matrix)]
        for entry in row:
            residue = entry % q
            if min(residue, q-residue) > bound:
                long_entry = True
        if long_entry and not eager:
            break
    return int(long_entry), work

def note(slug, index=1):
    src = Path('dag/Notes/pq-we-'+slug+'.md').read_text()
    return src.split('~~~python\n')[index].split('\n~~~')[0]
ns = {}
exec(note('self-consistent-modulus'), ns)
exec(note('ordered-radix-gadget',2), ns)
exec(note('tensor-rank-survival'), ns)
H,w,n,lam,d,t = 8,6,9,32,9,13
j,q,c = ns['select'](H,w,n,7,lam,8,16,4)
assert (j,c['m']) == (81,15490)
F = Fraction
rows = ns['rank_rows'](n,F(1,2))
bad = [F(1)] + [F(0)]*n
for _ in range(H):
    bad = [sum(a*b for a,b in zip(row,bad)) for row in rows]
box = F(4*c['B']+1,q)**t
delta = F(1,2**(lam+(H-1).bit_length()+3))
tails = [min(F(1),bad[r]+box+delta) for r in range(1,d+1)]
assert tails[-1] < F(1,2**lam)
expected = 1+sum(tails[:-1])
per_row = (H-2)*c['m']**2 + c['m']*t
def ceil(x):
    return -(-x.numerator//x.denominator)
print(ceil(expected*10**6), ceil(expected*per_row), per_row*d,
      ceil((d+expected)*per_row/2))
rng = Random(414)
tests = 0
for q in (2,3,16,17,256):
    for dims in ((2,3),(3,4,2),(4,2,5,3)):
        for trial in range(90):
            mats = [[[rng.randrange(-q,2*q) for _ in range(b)] for _ in range(a)]
                    for a,b in zip(dims,dims[1:])]
            if trial%5 == 0:
                mats[0] = [[0]*dims[1] for _ in range(dims[0])]
            bound = rng.randrange(q//2+1)
            val,work = scan(mats[0],mats[1:],q,bound)
            eager,full = scan(mats[0],mats[1:],q,bound,True)
            # Independent full product by summing row-scaled matrix rows.
            target = mats[0]
            for mat in mats[1:]:
                target = [[sum(r[a]*mat[a][b] for a in range(len(mat))) % q
                           for b in range(len(mat[0]))] for r in target]
            reference = int(any(bound < x%q < q-bound for r in target for x in r))
            assert val == eager == reference and work <= full
            if not val:assert work == full
            tests += 1
print(tests)
~~~
