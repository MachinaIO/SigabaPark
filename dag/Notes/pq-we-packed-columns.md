---
title: Fixed-length packing of bounded preimage columns with streamed witness evaluation
refs: [definition:WE_CircuitSAT, note:pq-we-self-consistent-modulus, note:pq-we-clocked-preimage]
tags: [witness-encryption, encoding, complexity]
---

**Full tensor ciphertext.** The modulus may have hundreds of bits even though each sampled column x obeys a public bound ||x||_1 <= C. The previous planner gives C on every outcome. A separate k=ceil(log2 q) bits per entry of each internal and final transition then overcharges their payload. Keep the two full roots in their ordinary residue format. For each subsequent column, choose one fixed-length format from public m,q,C, independently of the message, witness and coins.

**Column code.** Center each residue, choosing the negative representative at the even-modulus tie. This minimizes absolute value coordinatewise, so the same C applies. Map a signed integer x to z=2x for nonnegative x and z=-2x-1 otherwise. For parameter b write floor(z/2^b) zero bits followed by one bit and then the b low bits. Sum z <= 2C, so a whole m-entry column fits in U_b=m(b+1)+floor(2C/2^b) bits including all delimiters. Pad with zeros to U_b. Pick the smallest public budget U among mk and these U_b, keeping the residue format on a tie. The scan through bitlength(2C) includes an optimum because larger b increases the cost once all quotients are zero. The slot size is uniform across columns; no length table is needed. With b=max(0,ceil(log2(max(1,2C/m)))) the amortized cost is at most b+2 bits per entry before any better candidate from the scan. For the preceding bounded sampler C/m=(2t+1)ceil(sigma). Thus the per-entry bound depends logarithmically on the Gaussian width and shell cutoff. The two roots still use k bits per residue. The full per-message-bit tensor payload is 2nmk+2(H-1)mU bits, excluding public framing. Individual bits can be packed continuously across adjacent columns; padding to bytes per column would change the bound.

**Costs and security.** The encryptor can stream fields directly after each column draw. Once the layout has been computed per parameter set, packing costs O(m) small integer operations plus writing the output bits per column. The witness evaluator reads the selected branch and consumes one column at a time, accumulating its dot product with the current row. It reduces modulo q once per column. On Rice-coded honest inputs, an accumulator for a row of residues has absolute value <= (q-1)C; on the residue fallback branch m(q-1)^2 suffices. A full root with n rows can update n accumulators per column and reuse decoded entries. The multiplication count is unchanged. An honest evaluation uses O(Hnm²) scalar multiply-adds, plus reading the selected payload and computing the witness path. Key setup and preimage sampling remain the main unresolved practical costs. On genuine inputs the transformation depends only on the original residue ciphertext; centering prevents revealing the original integer representative. A total postprocessor on arbitrary strings may return a fixed dummy payload on malformed input or overflow. Since decryption on genuine payloads reconstructs every residue in the selected columns, the change preserves correctness exactly and transfers any established computational hiding bound under polynomial postprocessing, including for quantum distinguishers. No quantum hiding bound for the backend is asserted.

**Calculated payload per message bit.** Using the prior planner with w=6, n=4, p=7, lambda=32, S=8 and E=16, the H=8 control drops from 798295456080 bits to 80240838912 bits; H=32 drops from 418204574922496 bits to 9552228211712 bits. These are exact bit budgets for two encodings of the same parameter choice, not timings or secure parameter recommendations. All 1825 tested bounded columns reconstructed correctly in each coordinate for moduli 2,3,11,257,65537 and dimensions 1 through 3. Adding q before encoding produced identical payloads. The bit iterator below is an executable format specification; a byte-buffered implementation may cache the layout and consume whole words.

~~~python
def layout(m,q,C):
    # Minimize a proven bit cap. Break exact ties in favor of residues.
    k=(q-1).bit_length()
    cap,mode,b=m*k,'residue',k
    for low in range((2*C).bit_length()+1):
        size=m*(low+1)+((2*C)>>low)
        if size<cap:
            cap,mode,b=size,'rice',low
    return cap,mode,b

def fields(column,q,C):
    cap,mode,b=layout(len(column),q,C)
    if mode=='residue':
        for x in column:
            yield x%q,b
        return
    used=0
    for x in column:
        r=x%q
        x=r-q if 2*r>=q else r
        z=2*x if x>=0 else -2*x-1
        hi=z>>b
        used+=hi+1+b
        if used>cap:
            raise ValueError('column outside packing budget')
        yield 0,hi
        yield 1,1
        yield z% (1<<b),b
    yield 0,cap-used

def bits_of(fields):
    for value,width in fields:
        for j in reversed(range(width)):
            yield (value>>j)&1

def dot_from_bits(row,stream,q,C):
    cap,mode,b=layout(len(row),q,C)
    used=0
    def read():
        nonlocal used
        if used>=cap:
            raise ValueError('missing field')
        bit=next(stream,None)
        if bit not in (0,1):
            raise ValueError('invalid bit')
        used+=1
        return bit
    def number(width):
        v=0
        for _ in range(width):
            v=2*v+read()
        return v
    acc=0
    for a in row:
        if mode=='residue':
            x=number(b)
            if x>=q:
                raise ValueError('invalid residue')
        else:
            hi=0
            while read()==0:
                hi+=1
            z=(hi<<b)+number(b)
            x=z//2 if z%2==0 else -(z//2)-1
        acc+=(a%q)*x
    while used<cap:
        if read():
            raise ValueError('invalid padding')
    return acc%q
~~~
