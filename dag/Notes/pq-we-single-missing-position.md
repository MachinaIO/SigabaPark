---
title: Recovering the last positive slot with a fixed position checksum
refs: [definition:WE_CircuitSAT, note:pq-we-constant-weight-row-decoding, note:pq-we-tensor-rank-survival]
tags: [witness-encryption, correctness, complexity]
---

Require every length-N, weight-h codeword to have its set of one positions sum to zero modulo N. After detecting h-1 long slots, the remaining position is the negative sum of the detected positions modulo N. Distinct positions in [0,N) have distinct residues even for composite N. This removes the need to verify the last true one and all unresolved zeros. The checksum value is a public constant fixed before seeing the message. Encrypt each slot with independent complete coins and keys. The earlier bit hybrid applies with N slots. The classical rank/unrank map and the position-sum promise add no hardness assumption. This does not construct a quantum hiding proof for the bit backend.

**Capacity and implementation.** Translating all positions cyclically preserves weight and adds h to the checksum. If gcd(h,N)=1, repeated shifts permute all N residue classes transitively and each contains exactly binom(N,h)/N words. For N=140 and h=69 this exceeds 2^128. Use the first 2^128 words in skip-first lexicographic order and reject other ranks. A suffix counter indexed by position, remaining weight and residue supports exact rank and unrank in polynomial bit time. It has O(N² h) entries of O(N) bits. The code also works when h and N have a common divisor by using the exact count. Fixed leading zeros in the message are restored by the public message length.

**Correctness and running time.** Fix a valid witness independently of encryption coins. The residual bound excludes false detections. Write u_r for the upper bound that a one slot has not been detected after r complete row tests. Couple decoding to precomputing every slot's tests. With independent complete encryptions, any fixed pair of one slots both remain undetected with probability at most u_r². If the scan needs another round, at least two of the h one slots remain undetected. Thus v_r=min(1,binom(h,2) u_r²) bounds the probability a zero slot needs another round. It also bounds the whole-message failure probability at r=d. The expected row budget is h(1+sum u_r)+(N-h)(1+sum v_r), with sums from 1 to d-1. Each true one contributes at most its own single-slot waiting time. A shared lattice key would invalidate the independence argument unless a uniform conditional bound or another joint estimate is supplied. Timing remains data dependent. All honest costs stay polynomial for polynomial N and backend parameters.

**Cost at matched block correctness.** Compare against the prior 132-slot, weight-68 code. Both transmit 128 data bits, use H=8, logical width 6, prime 7, scalar and error caps 8 and 16, radix 16, atom bound 1/2 and local precision parameter 40. Search n from 4 to 12, retained row counts d from 1 to n and retained column counts t from 1 to 48. Recompute the modulus and packed-column costs for each n. Minimize packed tensor bits subject to a whole-block failure bound at most 2^-32, using h u_d for the baseline and v_d for the new code. Expected work is the row-arithmetic bound, not measured time. Columns exclude setup and target-formation work. These are correctness parameters without a lattice-security dimension floor.

| Code and dimension | Packed payload bits | Preimage columns | Expected Dec multiply-add bound | d, t |
| --- | ---: | ---: | ---: | --- |
| Weight only, n=10 | 9865662837096 | 27653736 | 305001521909 | 8, 13 |
| Position checksum, n=8 | 6482514424680 | 23179240 | 243871883605 | 6, 7 |
| Position checksum, fixed n=10 | 10458566552000 | 29328320 | 275435293840 | 4, 8 |

The matched-dimension comparison increases payload and sampled columns. The largest payload saving above depends on allowing a smaller lattice dimension. For a deployment, a quantum hardness requirement could preclude that choice. The listing verifies each of 2,081 individual missing-position repairs on small complete codebooks and tests positive and failing row schedules on five 128-bit ranks. Run from the DAG root.

~~~python
from functools import lru_cache
from itertools import combinations
from math import comb
from fractions import Fraction as F
from pathlib import Path

class ResidueCode:
    def __init__(self,n,h):
        self.n,self.h = n,h
        @lru_cache(None)
        def count(i,k,s):
            if k==0:return int(s==0)
            if k<0 or n-i<k:return 0
            return count(i+1,k,s)+count(i+1,k-1,(s-i)%n)
        self.count=count

    def unrank(self,value):
        n,h = self.n,self.h
        if not 0<=value<self.count(0,h,0): raise ValueError("invalid rank")
        s=0
        chosen=[]
        for i in range(n):
            skip=self.count(i+1,h,s)
            if value>=skip:
                value-=skip
                chosen.append(i)
                h-=1
                s=(s-i)%n
        return tuple(chosen)

    def rank(self,chosen):
        n,h=self.n,self.h
        if len(chosen)!=h or len(set(chosen))!=h or sum(chosen)%n or any(not 0<=x<n for x in chosen):
            raise ValueError("invalid codeword")
        s=value=0
        for i in sorted(chosen):
            value+=self.count(i+1,h,s)
            h-=1
            s=(s-i)%n
        return value

    def finish(self,detected):
        if len(detected)!=self.h-1:raise ValueError("wrong detection count")
        missing=(-sum(detected))%self.n
        if missing in detected:raise ValueError("inconsistent detections")
        return tuple(sorted((*detected,missing)))

def decode(code,rows,long_row,bits):
    found=set()
    for r in range(rows):
        for i in range(code.n):
            if len(found)==code.h-1:break
            if i not in found and long_row(i,r):found.add(i)
        if len(found)==code.h-1:
            value=code.rank(code.finish(found))
            return value if value<2**bits else None
    return None

def controls():
    checks=0
    for n in range(2,12):
        for h in range(1,n+1):
            c=ResidueCode(n,h)
            words=[w for w in combinations(range(n),h) if sum(w)%n==0]
            assert len(words)==c.count(0,h,0)
            for w in words:
                assert c.unrank(c.rank(w))==w
                for i in range(h):
                    assert c.finish(w[:i]+w[i+1:])==w
                    checks+=1
    c=ResidueCode(140,69)
    assert c.count(0,69,0)==comb(140,69)//140>=2**128
    for v in (0,1,2**64,2**127,2**128-1):
        w=c.unrank(v)
        assert c.rank(c.finish(w[1:]))==v
        remaining=set(w[1:])
        assert decode(c,3,lambda i,r:i in remaining and r==i%3,128)==v
        remaining.remove(w[1])
        assert decode(c,3,lambda i,r:i in remaining and r==i%3,128) is None
    print("repairs",checks)

def listing(slug,index=1):
    return Path('dag/Notes/pq-we-'+slug+'.md').read_text().split('~~~python\n')[index].split('\n~~~')[0]

def compare():
    env={}
    for slug,index in [('self-consistent-modulus',1),('ordered-radix-gadget',2),
                       ('packed-columns',1),('tensor-rank-survival',1)]:
        exec(listing(slug,index),env)
    best=[None,None]
    fixed=[None,None]
    for n in range(4,13):
        j,q,c=env['select'](8,6,n,7,40,8,16,4)
        m=c['m']
        cap=env['layout'](m,q,c['C'])[0]
        kernel=env['rank_rows'](n,F(1,2))
        bad=[F(1)]+[F(0)]*n
        for _ in range(8):
            bad=[sum(x*y for x,y in zip(row,bad)) for row in kernel]
        box=F(4*c['B']+1,q)
        for d in range(1,n+1):
            for idx,(N,h) in enumerate(((132,68),(140,69))):
                for t in range(1,49):
                    tail=[min(1,v+box**t+F(1,2**46)) for v in bad[1:d+1]]
                    def unresolved(x):
                        return min(1,comb(h,2)*x*x if idx else h*x)
                    if unresolved(tail[-1])>F(1,2**32):continue
                    columns=N*2*(6*m+t)
                    bits=N*2*d*m*c['k']+columns*cap
                    expected_rows=h*(1+sum(tail[:-1]))+(N-h)*(1+sum(map(unresolved,tail[:-1])))
                    work=expected_rows*(6*m*m+m*t)
                    candidate=(bits,columns,-(-work.numerator//work.denominator),n,d,t,j)
                    if best[idx] is None or candidate<best[idx]:best[idx]=candidate
                    if n==10 and (fixed[idx] is None or candidate<fixed[idx]):fixed[idx]=candidate
                    break
    print("payload, preimage columns, expected work bound, n,d,t,j",best)
    print("fixed n=10",fixed)
controls()
compare()
~~~
