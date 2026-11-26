---
title: Witness encryption under public relation compilation and certified port projection
refs: [definition:WE, theorem:AdvancedEncryption.WE.Compiler.transport, theorem:AdvancedEncryption.WE.Compiler.affine_port_image, theorem:AdvancedEncryption.WE.Compiler.checked_section]
tags: [witness-encryption, correctness, reduction, compilation]
---

**Relation compilation.** The transport theorem is stated with the registered WE primitive's actual PMF algorithms, Correct predicate and FalseStatementSecure predicate. A valid source witness must project to a valid target witness. For a fixed false source statement every target witness must be impossible: it suffices that target *existence* implies source existence. The projected witness alone need not identify the original witness. Given these conditions, equal Enc laws and equal Dec laws on valid witnesses transfer the backend correctness bound at the same correctness bits. Equalities concern the specified machines; the theorem does not supply implementations for them.

**Security cost.** A challenge includes the encoded statement and parameters alongside the ciphertext. A source adversary can depend on the original statement even when many statements compile to the same target. For every fixed false statement and source attacker A, supply a target machine B whose output law on every target-framed ciphertext equals A's on the original framing. The theorem rewrites the PMF binds to give equality of both acceptance probabilities, hence equality of squared advantages. If B.cost <= 2^k A.cost, target security at lambda+k bits suffices for source security at lambda. The cost includes the description of B: a nonuniform hard-wired source statement cannot silently be treated as free. The result is about the adversary model actually quantified by Def_WE. Establishing a quantum reduction in a different adversary model and charging the honest compiler and witness-projection clocks remain independent obligations.

**Eliminating affine wires.** For linear equation map F, port map P, public right-hand side r and arbitrary nonlinear port guard G, put Lx=(Fx,Px). The port-image theorem identifies the existence of a full witness over port y with G(y) and vanishing of the checks at (r,y), provided their span is the annihilator of range L. Over the binary field the checks are parities. A second theorem permits a simpler, constructive certificate: supply linear maps H,D,E with HL=0 and LD+EH=I. Then Hy=0 exactly characterizes the image and D is an explicit preimage map on every passing y. In particular a lift can be built without enumerating hidden assignments. D is needed for certification or witness recovery; projecting a valid original witness uses only P. The conclusions concern the linear system fed to the checker, so extraction of that system from a gate list must also preserve the gate semantics.

**Executable certificate.** The listing uses binary column vectors packed as integers. It returns D, E and H by row reduction and checks both identities separately on all basis vectors. For an m-by-n map with s check bits the displayed dense certificate costs mn+ms+sm bits in addition to L (before any sparse encoding). It is a public preprocessing certificate and need not be carried in every encrypted payload when layout reconstruction is already charged. The two matrix identities certify the entire range at once. Exhaustive small checks cover 4445 candidate output vectors. On the 128-input parity-and-nonlinear-taps circuit of [the compiler study](https://github.com/MachinaIO/SigabaPark/blob/f54a907261e5fbaec44feff2e3c71bb9a5535301/dag/Notes/pq-we-cut-width-compiler.md), L had 256 input coordinates, 134 output coordinates and a one-bit residual check. Of the 1024 possible port assignments, 512 lifted with the prescribed affine right-hand side, and 14 satisfied all nonlinear guards. All 14 reconstructed inputs were checked by evaluating the original NAND circuit. These values describe the test instance; the Lean proofs cover the abstract statements and do not certify this Python extraction or a complete WE submission.

Run python certificate.py for the independent matrix test, or python certificate.py lut.py affine.py to include the circuit test, using listings three and four of the linked compiler study.

~~~python
"""Check a right inverse on the image and independent parity checks using columns."""
from itertools import product
from random import Random

def apply(cols,word):
    result=0
    while word:
        bit=word&-word
        result^=cols[bit.bit_length()-1]
        word^=bit
    return result

def certificate(cols,height):
    # Represent each independent image pivot together with its input preimage.
    piv={}
    def reduce(value,source):
        for pos in sorted(piv,reverse=True):
            if value>>pos&1:
                vec,pre=piv[pos];value^=vec;source^=pre
        return value,source
    for j,col in enumerate(cols):
        vec,pre=reduce(col,1<<j)
        if vec:piv[vec.bit_length()-1]=(vec,pre)
    free=[p for p in range(height) if p not in piv]
    E=[1<<p for p in free];D=[];H=[]
    for p in range(height):
        rem,pre=reduce(1<<p,0);D.append(pre)
        H.append(sum((rem>>v&1)<<i for i,v in enumerate(free)))
    return D,E,H

def verify(cols,height,cert):
    D,E,H=cert
    if len(D)!=height or len(H)!=height:return False
    for entries,width in [(cols,height),(D,len(cols)),(E,height),(H,len(E))]:
        if any(x<0 or x.bit_length()>width for x in entries):return False
    return (all(apply(H,col)==0 for col in cols) and
            all(apply(cols,D[i])^apply(E,H[i])==1<<i for i in range(height)))

def audit():
    rng=Random(90164);words=0
    for n,m in product(range(7),repeat=2):
        for _ in range(5):
            cols=[rng.randrange(1<<m) for _ in range(n)]
            D,E,H=certificate(cols,m);assert verify(cols,m,(D,E,H))
            image={apply(cols,x) for x in range(1<<n)}
            for y in range(1<<m):
                assert (apply(H,y)==0)==(y in image)
                if y in image:assert apply(cols,apply(D,y))==y
                words+=1
            if m and n and any(cols):
                j=next(i for i,v in enumerate(cols) if v)
                bad=D.copy();bad[0]^=1<<j
                assert not verify(cols,m,(bad,E,H))
    print('complete image/section checks',words)
if __name__=='__main__':audit()

def port_control(lut,affine):
    n=128;gates=[]
    def nand(a,b):
        gates.append((a,b))
        return n+len(gates)
    def xor(a,b):
        c=nand(a,b)
        return nand(nand(a,c),nand(b,c))
    v=1
    for j in range(2,n-3):v=xor(v,j)
    b=n-3;w=xor(v,b)
    a=nand(v,n-2);c=nand(w,n-1);d=nand(b,n)
    z=nand(a,c);z=nand(z,z);z=nand(z,d);nand(z,z)
    functions,needed,top=lut['network'](n,gates,2)
    eqs=[];guards=[]
    for z in sorted(needed):
        ports,table=functions[z]
        linear=affine['affine'](ports,table)
        if linear is None:
            guards.append((None if z==top else z,ports,table))
        else:
            terms,offset=linear
            if z==top:offset^=1
            else:terms.add(z)
            eqs.append((terms,offset))
    ports=sorted({p for z,terms,_ in guards for p in terms}|{z for z,_,_ in guards if z is not None})
    wires=sorted(set(ports).union(*(t for t,_ in eqs)))
    outputs=[t for t,_ in eqs]+[{v} for v in ports]
    cols=[sum(1<<j for j,row in enumerate(outputs) if v in row) for v in wires]
    D,E,H=certificate(cols,len(outputs));assert verify(cols,len(outputs),(D,E,H))
    rhs=sum(offset<<j for j,(_,offset) in enumerate(eqs))
    ok=lifts=0
    for word in range(1<<len(ports)):
        y=rhs|(word<<len(eqs))
        if apply(H,y):continue
        lift=apply(D,y)
        assert apply(cols,lift)==y
        lifts+=1
        vals=dict(zip(wires,[(lift>>j)&1 for j in range(len(wires))]))
        if all((table>>sum(vals[p]<<j for j,p in enumerate(terms))&1)==(1 if z is None else vals[z])
               for z,terms,table in guards):
            ok+=1
            tr=lut['trace'](n,gates,[vals.get(i,0) for i in range(1,n+1)])
            assert tr[-1] and all(tr[z]==vals[z] for z in ports)
    print('columns, outputs, syndrome bits, reconstructed affine lifts, accepting lifts:',
          len(cols),len(outputs),len(E),lifts,ok)

if __name__=='__main__':
    import sys,runpy
    if len(sys.argv)>1:port_control(*map(runpy.run_path,sys.argv[1:]))
~~~
