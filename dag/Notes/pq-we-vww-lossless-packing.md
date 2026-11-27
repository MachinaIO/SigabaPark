---
title: Lossless transition compression for the published VWW witness-encryption distribution
refs: [definition:WE_CircuitSAT, note:pq-we-packed-columns, note:pq-we-integer-rank-correctness]
tags: [witness-encryption, compilation, complexity, correctness]
---

**Security baseline.** [Vaikuntanathan, Wee and Wichs, Sections 2.1, 4, 5 and 6](https://ntt-research.com/wp-content/uploads/2023/01/Witness-encryption-and-null-iO-from-evasive-LWE.pdf) specify constant-width tensor factors, Gaussian preimages and different noise scales for the root and later levels. Their hardness requirement and noise-flooding inequalities in Remark 5.1 constrain the lattice dimension and modulus jointly. The dimension-one control with width growing exponentially in the correctness parameter specifies a different distribution from Construction 4.2. Its 161 MB accounting therefore does not instantiate their security theorem. In contrast, the following encoder can take the published ciphertext itself as input, without any trapdoor or change in parameter choices. It works with the original CNF frontend and with any other frontend for which security and correctness have separately been established.

**Format and reduction.** Leave root blocks in their usual residue representation. In the public ordering of all remaining columns let N=2(H-1)m and k=ceil(log2 q). Replace each integer by its residue, centering it for the signed Rice code from the linked note. Decryption of the original smallness predicate uses the centered modular result, so this preserves all path outputs. With public low-bit count b between 0 and k, first count Rice bits without emitting any unary runs. Use the shorter of Rice and mk raw bits per column, with a mode bit. In a second pass choose between the whole mixed stream and a wholly raw stream, writing one outer mode bit. When N=0 the format can omit that bit by public convention; the reference listing retains it. Worst case is 1+Nmk bits for all transition blocks together. Work to count a field is polynomial in the bit length of its integer; no unary run is written for an expensive rejected candidate. Decoding sequentially consumes at most the transmitted bits and polynomial modular arithmetic. Public dimensions specify all block boundaries once the stream is parsed. To access a later branch one may scan preceding fields. This can sacrifice fixed-offset random access.

For every witness and every draw of the original encoder the decoded residues reproduce the evaluated product modulo q. For every false instance and every distinguisher of the compressed ciphertext, compose it with the public deterministic packer to obtain exactly the same acceptance probabilities on the original challenges. This already accounts for the exposed payload length. The implication also holds for a quantum distinguisher of classical ciphertexts if the original security statement quantifies such distinguishers. The construction here inherits the adversary class and assumptions of the chosen backend. This transfer needs no Gaussian tail estimate. Honest encryption cost is the original Enc cost plus packing, and honest decryption cost is the original modular evaluation plus parsing.

**When the payload is short.** Write s in the convention exp(-pi ||x||²/s²); convert a Gaussian exponent written with standard-deviation parameter sigma by s=sqrt(2pi) sigma. For one transition column let K be its kernel lattice and v+K its target coset in Z^m. Define Z_s(v+K) as its Gaussian mass. For X distributed by the specified coset Gaussian, Markov's inequality gives

    Pr(||X||² > R²) <= exp(-pi R²/(2s²)) Z_(sqrt(2)s)(v+K)/Z_s(v+K).

For example if the nonzero dual Gaussian mass sum at width 1/s is at most 1/3, Poisson summation bounds the ratio by 2 times 2^(m/2), uniformly in v: the zero dual term gives the volume factor and all other terms have total relative magnitude at most 1/3 at either scale. With R²=s²(m+2u+4)/4, the displayed probability is at most 2^-u, using pi/8 > (ln 2)/2. Thus C=ceil(s sqrt(m(m+2u+4))/2) bounds the column 1-norm except with that probability. Centering residues cannot increase it. For N>=1 take u=lambda+ceil(log2 N). Under the specified smoothing condition on every key, except with probability at most 2^-lambda the transition payload fits 1+N(1+min(mk,m(b+1)+floor(2C/2^b))) bits. Add the probability of bad keys and any actual sampler approximation distances when invoking an implementation. Choosing b close to log2(max(1,2C/m)) costs O(log(2+s sqrt(1+u/m))) bits per transition entry on this event. For an unconditional independent integer Gaussian in the message-independent comparison distribution of Theorem 5.1, K=Z^m and the same mass ratio is at most 2^(m/2) even without the dual-mass test (all unshifted dual terms are positive and decrease at the larger primal width). A PPT overflow test transfers this typical-length property to false instances up to the theorem's distinguishing loss, with the public cap chosen for that width. For true instances the explicit coset condition above is sufficient. We have not verified its numerical margin for a concrete security-matched VWW parameter set. Whichever bound applies, overflow still decodes correctly.

**Reproduction.** The reference listing implements the transition stream; the roots and public statement are carried separately as before. Checks across five moduli, three dimensions, three column counts, three Rice settings and eight input draws verified exact residue recovery, modular dot products and the worst-case bit cap on all 1080 cases, exercising both outer formats. This preserves a conditional polynomial WE construction and gives no evidence that its absolute size is practical. The previous 161 MB and a security-matched compressed VWW ciphertext have no established numerical size comparison.

~~~python
def pack_columns(cols,q,b):
    # Reference bit strings. A production encoder can count fields in a first pass.
    k=(q-1).bit_length()
    def binary(v,w):
        return format(v,'0%db'%w) if w else ''
    raw=[]
    mixed=[]
    for col in cols:
        residues=[v%q for v in col]
        block=''.join(binary(x,k) for x in residues)
        raw.append(block)
        signed=[v-q if 2*v>=q else v for v in residues]
        z=[2*x if x>=0 else -2*x-1 for x in signed]
        count=sum((v>>b)+1+b for v in z)
        if count<len(block):
            mixed.append('1'+''.join('0'*(v>>b)+'1'+binary(v% (1<<b),b) for v in z))
        else:
            mixed.append('0'+block)
    plain=''.join(raw)
    adaptive=''.join(mixed)
    return '1'+adaptive if len(adaptive)<len(plain) else '0'+plain

def unpack_columns(payload,q,b,m,N):
    k=(q-1).bit_length()
    pos=0
    def take(w):
        nonlocal pos
        if pos+w>len(payload):
            raise ValueError('truncated payload')
        r=payload[pos:pos+w]
        pos+=w
        return int(r,2) if w else 0
    adaptive=take(1)
    cols=[]
    for _ in range(N):
        rice=adaptive and take(1)
        col=[]
        start=pos
        for _ in range(m):
            if rice:
                hi=0
                while take(1)==0:
                    hi+=1
                    if pos-start>=m*k:
                        raise ValueError('overlong Rice field')
                z=(hi<<b)+take(b)
                x=z//2 if z%2==0 else -(z//2)-1
                col.append(x%q)
            else:
                x=take(k)
                if x>=q:
                    raise ValueError('invalid residue')
                col.append(x)
        cols.append(col)
    if pos!=len(payload):
        raise ValueError('trailing bits')
    return cols
~~~
