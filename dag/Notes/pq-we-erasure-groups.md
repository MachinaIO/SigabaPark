---
title: Recovering erased WE groups by polynomial interpolation
refs: [definition:WE_CircuitSAT, note:pq-we-constant-weight-row-decoding, note:pq-we-single-missing-position]
tags: [witness-encryption, correctness, complexity]
---

Partition a message into k equally sized b-bit symbols (public zero padding if required). Over a field of prime order p greater than 2^b-1 and at least k+a, interpolate the polynomial of degree below k taking these k values at 0,...,k-1. Append its values at the next a points. Within each group, encode the field element using the skip-first constant-weight code of length L and weight h with binom(L,h) at least p. Encrypt all (k+a)L slots with independent complete WE coins and keys under the same statement. This is systematic Reed–Solomon erasure coding outside the bit encoder.

For each of the first k groups, try at most d rounds of the prior weight-h decoder. Mark a group erased if h long slots have not been found. Decrypt parity groups in order until k distinct groups have succeeded or none remain. Recover missing data by interpolation at the missing indices and concatenate the fixed-width symbols. Reject an invalid inner rank, an interpolated data value outside the b-bit alphabet, inconsistent padding, or fewer than k successes. On a fixed valid witness the residual cap excludes false positives, making each group either correct or an identified erasure. Keeping genuine parity values up to p-1 is important when the field exceeds the data alphabet. On correct full data with no erasures the decryptor can skip interpolation. Encryption always transmits the parity groups.

**Accounting.** Write u_r for the prior fixed-witness upper bound on the probability that a one slot remains undetected after r rows. Each group has erasure probability at most f=min(1,h u_d), while its expected row work is at most W=h(1+sum u_r)+(L-h)(1+sum min(1,h u_r)), summing r from 1 to d-1. Independence of coins across complete slots implies independent group erasures for a fixed message and witness. A union bound over subsets of size a+1 gives total failure at most binom(k+a,a+1) f^(a+1). Parity group i (numbered from one) is needed only if the previous k+i-1 groups have at least i erasures, with probability at most min(1,binom(k+i-1,i) f^i). Multiply W by k plus the sum of these bounds. Independence justifies charging an attempted group's unconditional bound even when the decision to attempt it is adaptive. Column and ciphertext budgets charge every slot. The ordinary bit-ciphertext hybrid loses at most (k+a)L times the component distinguishing advantage for quantum distinguishers of classical ciphertexts. The bit scheme's quantum hiding remains conditional.

The public field in the example is fixed per symbol size. For larger inputs one can repeat fixed-size outer blocks and allocate correctness and hiding budgets across them. This gives polynomial overall size and honest work given polynomial-bit, clocked bit-WE parameters. Rank/unrank, field interpolation and scheduling add polynomial overhead. The operation figures below count only the dense modular multiplies and adds in the WE decoder.

**Matched 128-bit correctness control.** Use the preceding note's H=8, width six, radix 16, local precision 40 and block failure target 2^-32. For b in {8,16,32}, choose the smallest feasible L and then the smallest feasible h. Search a from one to six, lattice dimension n from four to twelve, d from one to n and t from one to 48 terminal columns. Upward dyadic rounding of each probability bound avoids overly precise search arithmetic. Compare the minimum packed payload in each family at this whole-message failure target.

| Construction | Lattice dimension | Packed bits | Sampled columns | Expected Dec multiply-add bound |
| --- | ---: | ---: | ---: | ---: |
| Previous position checksum | 8 | 6482514424680 | 23179240 | 243871883605 |
| Outer erasure code | 6 | 5436261782160 | 26724720 | 153969770631 |
| Previous checksum at n=10 | 10 | 10458566552000 | 29328320 | 275435293840 |
| Outer code minimizing payload at n=10 | 10 | 12774392002800 | 35822448 | 288976118762 |
| Outer code minimizing expected work at n=10 | 10 | 13073208190000 | 36660400 | 274579765872 |

The minimum-payload outer choice uses sixteen data groups and four parity groups, each with eleven slots of weight four. It pays for more independent preimage columns than the checksum scheme. At fixed n=10 the prior checksum has better payload, column count and expected work than the minimum-payload outer choice. The search allowing n=6 addresses correctness only; whether any of these dimensions meets a quantum security target remains unresolved. No encoder or decoder timing at these parameter sizes is claimed. The control enumerates 4,889 erasure patterns on three sample messages including every four-erasure pattern for the winning layout, uses the inner row scheduler, and exercises parity value 256 in the 8-bit data case.

~~~python
from fractions import Fraction as F
from math import comb, isqrt
from itertools import combinations
from pathlib import Path

def interpolate(points, x, p):
    total = 0
    for i,(a,value) in enumerate(points):
        numerator = denominator = 1
        for j,(b,_) in enumerate(points):
            if i != j:
                numerator = numerator*(x-b)%p
                denominator = denominator*(a-b)%p
        total += value*numerator*pow(denominator,-1,p)
    return total%p

def listing(slug,index=1):
    return Path('dag/Notes/pq-we-'+slug+'.md').read_text().split('~~~python\n')[index].split('\n~~~')[0]

def layout(b,p):
    length=1
    while comb(length,length//2)<p:length+=1
    weight=next(w for w in range(length) if comb(length,w)>=p)
    return length,weight

def controls():
    ns={}
    exec(listing('constant-weight-row-decoding').split('src = Path')[0],ns)
    count=0
    for b,p in ((8,257),(16,65537),(32,4294967311)):
        assert all(p%i for i in range(2,isqrt(p)+1))
        size=128//b
        length,weight=layout(b,p)
        data=[((1<<b)-1-i*i)%(1<<b) for i in range(size)]
        if b==8:data=[(256+(i-size))%p for i in range(size)]
        pts=list(enumerate(data))
        parity={8:4,16:1,32:3}[b]
        groups=data+[interpolate(pts,i,p) for i in range(size,size+parity)]
        if b==8:assert groups[size]==256
        groups_words=[ns['unrank'](v,length,weight) for v in groups]
        for erased in combinations(range(size+parity),parity):
            good=[]
            for i,symbol in enumerate(groups):
                word=groups_words[i]
                ones=[pos for pos,v in enumerate(word) if v]
                missed=set(ones[:int(i in erased)])
                decoded,_=ns['decode'](length,weight,3,
                    lambda pos,r:bool(word[pos]) and pos not in missed and pos%3==r)
                if decoded is not None:
                    good.append((i,ns['rank_word'](decoded)))
                if len(good)==size:break
            available=dict(good)
            assert [available[i] if i in available else interpolate(good,i,p) for i in range(size)]==data
            count+=1
    print("recovered erasure patterns",count)

def compare():
    ns={}
    for slug,idx in [('self-consistent-modulus',1),('ordered-radix-gadget',2),
                     ('packed-columns',1),('tensor-rank-survival',1)]:
        exec(listing(slug,idx),ns)
    best={}
    for n in range(4,13):
        j,q,c=ns['select'](8,6,n,7,40,8,16,4)
        m=c['m']
        slot=ns['layout'](m,q,c['C'])[0]
        kernel=ns['rank_rows'](n,F(1,2))
        bad=[F(1)]+[F(0)]*n
        for _ in range(8):bad=[sum(x*y for x,y in zip(row,bad)) for row in kernel]
        def upper(x):
            return F(-(-(x*2**64).numerator//(x*2**64).denominator),2**64)
        for t in range(1,49):
            box=F(4*c['B']+1,q)**t
            tails=[min(1,upper(x+box+F(1,2**46))) for x in bad[1:]]
            for b,p in ((8,257),(16,65537),(32,4294967311)):
                k=128//b
                L,h=layout(b,p)
                for parity in range(1,7):
                    G=k+parity
                    d=next((i for i,u in enumerate(tails,1)
                            if comb(G,parity+1)*min(1,h*u)**(parity+1)<=F(1,2**32)),None)
                    if d is None:continue
                    f=min(1,h*tails[d-1])
                    attempted=k+sum(min(1,comb(k+i-1,i)*f**i) for i in range(1,parity+1))
                    per=h*(1+sum(tails[:d-1]))+(L-h)*(1+sum(min(1,h*u) for u in tails[:d-1]))
                    work=F(attempted*per*(6*m*m+m*t))
                    cols=G*L*2*(6*m+t)
                    payload=G*L*2*d*m*c['k']+cols*slot
                    record=(payload,cols,-(-work.numerator//work.denominator),n,b,parity,L,h,d,t)
                    if n==10 and ('work10' not in best or record[2]<best['work10'][2]):
                        best['work10']=record
                    for tag in ('all',n):
                        if tag not in best or record<best[tag]:best[tag]=record
    print("payload, columns, expected work, n,b,parity,L,h,d,t")
    print(best['all'],best[10])
    print('fixed dimension, minimum work',best['work10'])
controls()
compare()
~~~
