---
title: Inferring zero slots in batched witness decryption by constant-weight coding
refs: [definition:WE_CircuitSAT, note:pq-we-lazy-row-decryption, note:pq-we-tensor-rank-survival]
tags: [witness-encryption, correctness, complexity]
---

The previous local decoder certifies a one as soon as a long row appears, but pays for every row to certify a zero. A public promise on the *number* of ones allows the decryptor to infer the remaining zeros. To transmit b bits choose public N,h with binom(N,h) >= 2^b. Encode the message interpreted as an integer by lexicographic unranking into the first 2^b binary words of length N and weight h. Encrypt all N slots under the same statement with independent full encryption coins. No shared lattice keys are assumed across slots. This can be applied to a random session key if an application already encrypts its payload separately.

**Decoder.** With a fixed valid witness, scan row one of every slot, then row two of every still unresolved slot, continuing until h distinct slots have produced a long entry. Infer all other bits as zero, rank the codeword and recover the fixed-length message (including leading zeros). Reject an out-of-range rank or an insufficient number of detected slots after d rounds. At each stage a row is propagated through the selected matrix chain of its slot. Cache or unpack public data as appropriate. Zero slots never produce a long entry under the bounded residual premise. Consequently every early output is the correct message, and failure implies that at least one true one failed the original full scan. No independence is required for this correctness argument. On arbitrary ciphertexts the procedure is bounded by N d row evaluations. The listing implements the row scheduler with a callback for the same row test as the preceding note. Rank/unrank use binomial counts of suffixes; these have O(N) bits and can be precomputed in polynomial time.

**Cost proof.** Write u_r for the prior upper bound on the probability that the first r rows of a single fixed valid one slot all pass the shortness test. A one slot attempts at most 1+sum_(r=1 to d-1) u_r rows in expectation. A zero slot is still scanned in round r+1 only if at least one true one has not been detected after r complete rounds. Its expected work is at most 1+sum_(r=1 to d-1) min(1,h u_r) rows. This argument may be coupled to scanning all rows before any early stopping, so the stopping decision introduces no independence assumption. Weight the first bound by h and the second by N-h. The total times the multiply-add count per row bounds expected dense arithmetic for *every* message. Whole-message failure is at most h u_d. Keeping N polynomial maintains polynomial honest times and ciphertext size. For a target whole-message error epsilon, price the component parameters with u_d <= epsilon/h. The available experiment uses fixed component parameters.

**Hiding.** For a false statement and a pair of messages, their equal-length codewords are public functions of the two messages. Hybridize their independent bit ciphertexts one slot at a time. In a hybrid reduction the other slots are encrypted locally by the public algorithm. The triangle inequality gives at most N times the underlying bit distinguishing advantage with the usual simulation overhead, also for quantum distinguishers of classical ciphertexts. A concrete whole-message security target must account for this loss. The argument transfers the underlying conditional hiding claim and does not resolve the quantum evasive-LWE root assumption. Timing of successful witness decryption is data-dependent.

**Control at the previous correctness parameters.** For 128 message bits the smallest feasible N is 132. Among its feasible weights the stated upper bound is minimized at h=68. All 128-bit inputs then cost at most 285,998,530,076 expected modular multiply-adds, versus 922,961,768,526 for 128 independent public-mask decoders using the same bit parameters. Both numbers are rounded-up arithmetic budgets. This lowers the bound by 69.0% with four additional full bit encryptions (3.125%) and removes the 128 public mask bits. It does not measure elapsed time or fix a common whole-message security level. The new union bound on block failure is below 1.22e-8. Allowing up to eight further slots selects N=137,h=84 with an expected bound of 277,776,564,666. For 64 input bits the minimum-length choice N=68,h=31 gives 124,835,899,291. Worst-case row work scales with N; the improvement concerns the expectation. Full-slot encryption, storage access, unpacking, rank arithmetic, and witness preparation are excluded from the modular operation counts.

The listing recomputes the exact rational bounds, enumerates all codewords through length seven, and checks 21,844 detection schedules including missing detections and late rows.

~~~python
from itertools import product
from math import comb
from pathlib import Path

def unrank(rank, length, ones):
    if not 0 <= rank < comb(length,ones):
        raise ValueError("rank outside codebook")
    word = []
    for remaining in reversed(range(length)):
        skip = comb(remaining,ones)
        take = rank >= skip
        word.append(int(take))
        if take:
            rank -= skip
            ones -= 1
    return word

def rank_word(word):
    ones = sum(word)
    rank = 0
    for pos,bit in enumerate(word):
        if bit:
            rank += comb(len(word)-pos-1,ones)
            ones -= 1
    return rank

def decode(length, ones, rows, long_row):
    word = [0]*length
    found = visits = 0
    for r in range(rows):
        for pos in range(length):
            if found == ones:
                return word, visits
            if not word[pos]:
                visits += 1
                if long_row(pos,r):
                    word[pos] = 1
                    found += 1
    return (word if found == ones else None), visits

def check_small():
    cases = 0
    for n in range(1,8):
        for w in range(n+1):
            for rank in range(comb(n,w)):
                word = unrank(rank,n,w)
                assert sum(word)==w and rank_word(word)==rank
                # Threshold row 3 is never reached by a three-row decoder.
                for times in product((0,2,3),repeat=w):
                    threshold = iter(times)
                    first = [next(threshold) if x else 3 for x in word]
                    actual,visits = decode(n,w,3,lambda p,r:r==first[p])
                    assert actual == (word if all(t<3 for t in times) else None)
                    assert visits<=3*n
                    cases += 1
    return cases

src = Path('dag/Notes/pq-we-lazy-row-decryption.md').read_text()
ns = {}
exec(src.split('~~~python\n',1)[1].split('rng = Random')[0],ns)
tails,per_row,ceil = (ns[k] for k in ('tails','per_row','ceil'))
def bound(n,w):
    one = 1+sum(tails[:-1])
    rounds = 1+sum(min(1,w*t) for t in tails[:-1])
    return ceil((w*one+(n-w)*rounds)*per_row)
def best(bits, extra):
    choices = [(bound(n,w),n,w) for n in range(bits,bits+extra+1)
               for w in range(1,n+1) if comb(n,w)>=2**bits]
    return min(choices)

print(check_small())
for bits in (16,64,128,256):
    n = bits
    while comb(n,n//2)<2**bits:n+=1
    print(bits,best(bits,n-bits),best(bits,n-bits+8))
print("128 independent masked bits:",ceil(128*(ns["d"]+ns["expected"])*per_row/2))
print("68-bit union failure bound:",float(68*tails[-1]))
~~~
