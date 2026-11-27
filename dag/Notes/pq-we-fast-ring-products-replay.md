---
title: "Reproduce lifted and single-prime negacyclic product checks"
refs: [definition:WE_CircuitSAT_Capped]
tags: [ring-lwe, witness-encryption, arithmetic]
---

Save the following standard-library Python as a single file and execute it with Python 3. It compares every output coefficient and checks every local inverse division. Timing is CPython wall time; the reference interpreter materializes lists that a streaming schedule can avoid. The more compact single-prime route is exact for every allowed ternary input. The shared A and its transforms are constructed once per benchmark method.

```python
from itertools import product
from random import Random


def rotate(a, shift):
    m = len(a)
    return [(-1 if ((i-shift)//m) % 2 else 1) * a[(i-shift) % m]
            for i in range(m)]


def transform(blocks, direction, q, halve=False):
    d = len(blocks)
    if d == 1:
        return blocks
    left = transform(blocks[::2], direction, q, halve)
    right = transform(blocks[1::2], direction, q, halve)
    result = [None] * d
    m = len(left[0])
    modulus = q // (d//2) if halve else q
    for k, (u, v) in enumerate(zip(left, right)):
        v = rotate(v, direction*k*(2*m//d))
        for j, sign in ((k, 1), (k+d//2, -1)):
            word = [x + sign*y for x,y in zip(u,v)]
            if modulus:
                word = [x % modulus for x in word]
            if halve:
                assert all(x % 2 == 0 for x in word)
                word = [x//2 for x in word]
            result[j] = word
    return result


def direct(a, b, q):
    n = len(a)
    return [(sum(x * b[(k-i) % n] * (-1 if i > k else 1)
                 for i,x in enumerate(a))) % q for k in range(n)]


def prep(a, width):
    return sum(x << (i*width) for i,x in enumerate(a))


def point(a, b, L, q):
    m = len(a)
    width = (m * (q-1) * (2*L)).bit_length()
    mask = (1 << width)-1
    z = prep(a, width) * prep([x+L for x in b], width)
    digits = [(z >> (i*width)) & mask for i in range(2*m)]
    return [(digits[i] - digits[i+m] - L*(2*sum(a[:i+1])-sum(a))) % q
            for i in range(m)]


def multiply(a, b, L):
    n = len(a)
    m = n//L
    d = 2*L
    q = 256*d
    assert n == m*L and m % L == 0 and d & (d-1) == 0
    def blocks(v):
        return [list(v[i::L]) for i in range(L)] + [[0]*m for _ in range(L)]
    aa = transform(blocks(a), 1, q)
    bb = transform(blocks(b), 1, None)
    assert all(abs(x)<=L for v in bb for x in v)
    cc = transform([point(x,y,L,q) for x,y in zip(aa,bb)], -1, q, True)
    out = [0]*n
    for i in range(L):
        out[i::L] = [(x+y)%256 for x,y in zip(cc[i],rotate(cc[i+L],1))]
    return out


if __name__ == '__main__':
    rng = Random(156)
    tested = 0
    for n,L in [(4,2),(8,2),(16,4),(32,4),(128,8),(512,16)]:
        cases = product((-1,0,1), repeat=n) if n<=8 else (
            [rng.randrange(-1,2) for _ in range(n)] for _ in range(30))
        for s in cases:
            a = [rng.randrange(256) for _ in range(n)]
            assert multiply(a,s,L)==direct(a,s,256)
            tested += 1
    print(tested, 'exact normalized-transform products')

from itertools import accumulate
from statistics import median
from time import perf_counter
from random import Random



def lift_setup(a):
    L,m,q=16,32,8192
    aa=transform([a[i::L] for i in range(L)]+[[0]*m for _ in range(L)],1,q)
    width=(m*(q-1)*2*L).bit_length()
    mask=(1<<width)-1
    meta=[(prep(x,width),[L*(2*y-sum(x)) for y in accumulate(x)]) for x in aa]
    def evaluate(b):
        bb=transform([b[i::L] for i in range(L)]+[[0]*m for _ in range(L)],1,None)
        c=[]
        for (value,correction),v in zip(meta,bb):
            z=value*prep([x+L for x in v],width)
            digits=[(z>>(i*width))&mask for i in range(2*m)]
            c.append([(digits[i]-digits[i+m]-correction[i])%q for i in range(m)])
        cc=transform(c,-1,q,True)
        out=[0]*512
        for i in range(L):
            out[i::L]=[(x+y)%256 for x,y in zip(cc[i],rotate(cc[i+L],1))]
        return out
    return evaluate


def fermat_setup(a):
    p=65537; n=512; r=pow(3,64,p); assert pow(r,n,p)==p-1
    a=[((x+128)%256)-128 for x in a]
    u=[x+128 if x<0 else x-128 for x in a]
    toggle=sum(map(abs,u))<sum(map(abs,a))
    b=u if toggle else a
    rev=[int(f'{i:09b}'[::-1],2) for i in range(n)]
    def plan(sign):
        return [[pow(r,sign*2*n*j//m,p) for j in range(m//2)]
                for m in [2**i for i in range(1,10)]]
    def fft(v,tw):
        f=[v[j] for j in rev]
        for row in tw:
            h=len(row)
            for i in range(0,n,2*h):
                for j,t in enumerate(row):
                    x=f[i+j]; y=t*f[i+j+h]%p
                    f[i+j]=(x+y)%p; f[i+j+h]=(x-y)%p
        return f
    fw,iv=plan(1),plan(-1)
    t=[pow(r,i,p) for i in range(n)]
    u=[pow(n,-1,p)*pow(r,-i,p)%p for i in range(n)]
    aa=fft([x*y%p for x,y in zip(b,t)],fw)
    def evaluate(s):
        f=fft([x*y%p for x,y in zip(s,t)],fw)
        yy=fft([x*y%p for x,y in zip(f,aa)],iv)
        c=[x*y%p for x,y in zip(yy,u)]
        z=128 if toggle and sum(s)%2 else 0
        return [((x if x<=32768 else x-p)%256)^z for x in c]
    return evaluate


def bench():
    R=Random(156); A=[R.randrange(256) for _ in range(512)]
    secrets=[[R.randrange(-1,2) for _ in A] for _ in range(30)]
    refs=[direct(A,s,256) for s in secrets]
    for name,setup in [('lifted',lift_setup),('fermat',fermat_setup),
                         ('direct',lambda a: lambda s: direct(a,s,256))]:
        start=perf_counter(); f=setup(A); init=perf_counter()-start; runs=[]
        for s,y in zip(secrets,refs):
            start=perf_counter(); z=f(s); runs.append(perf_counter()-start)
            assert z==y
        print(name, 'setup_ms', round(1000*init,3), 'median_ms',
              round(1000*median(runs),3), 'range_ms',tuple(round(1000*x,3) for x in (min(runs),max(runs))))

if __name__=='__main__': bench()

```
