---
title: Eliminating mandatory affine conditions in raw NAND circuits and encrypting the residual
refs: [definition:WE_CircuitSAT_Capped, definition:AffineFiberScan, theorem:AdvancedEncryption.WE.AffineFiberScan.scan_sound, theorem:AdvancedEncryption.WE.AffineFiberScan.hull_transfer, theorem:AdvancedEncryption.WE.AffineFiberScan.project_lift, theorem:AdvancedEncryption.WE.AffineFiberScan.pivot_patch]
tags: [witness-encryption, circuit-sat, affine-subspaces, preprocessing]
---

On one registered 128-input, 4096-gate mixed circuit the compiler extracts 20 independent mandatory parity checks. The resulting 108-dimensional affine space still contains rejecting witnesses. After quotienting, only four independent features reach the output. Ten NAND gates suffice for the child before padding. Of the 16 feature assignments, six accept. The example admits a direct SAT decision before invoking any cryptographic assumption. A second instance adding a contradictory check is rejected by the affine pass. The results below concern a partial front end to the registered witness-encryption problem.

### From gates to equations

Rows represent affine equations over GF(2). A row stores its constant in bit 0. Reduced row echelon form uses the highest variable bit as pivot, with zero and inconsistent systems represented separately. A descriptor is an affine set A or its complement. Canonicalize complements of hyperplanes by flipping the offset. For two positive operands the truth set of NAND is the complement of their intersection. For mixed signs compute a difference A minus B before complementing. A disjoint intersection or containment settles the extreme cases. If A is the whole space, return the complement of B. Otherwise a nontrivial difference is affine exactly when A intersection B is a hyperplane in A: flip any equation of B independent modulo A. For relative codimension d≥2 its size is |A|(1−2^-d), a non-power of two strictly below half the ambient space. This also rules out a co-affine result. With two negative operands take the union of their two excluded flats. Apart from containment, a union is affine exactly for two distinct parallel cosets of the same direction. Indeed, inside an affine union the two proper flats must cover it, hence each has half its size and the two are disjoint parallel hyperplanes. Each proper excluded flat in canonical negative form has codimension ≥2; their union has at most half the space and can be co-affine only at equality, when it must itself be a hyperplane. In the parallel case keep the equations whose offsets agree and take pairwise sums with one differing pivot row for the rest. These cases classify *representable* NAND outputs when both operands have exact descriptors.

Independently maintain supersets F0,F1 of both output fibers. For NAND, F0 is contained in the intersection of operand one-supersets, and F1 in the affine hull of the union of their zero-supersets. Here F0,F1 on the left denote the actual fibers. The intersection stacks equations. The join intersects the row spaces of valid augmented equations, handling the empty set separately: its construction reduces the first basis modulo the second, and tracks the source combinations reducing to zero. Where an exact descriptor is available, substitute the exact hull on each side. The hull of the complement of a proper flat of codimension ≥2 is the whole space by cardinality. Wire 0, forward reads before the current gate, and the last output for an empty list all use true. The Lean scanner theorem follows SigabaNeo.evalGates directly by a relation between the full abstract and concrete wire lists, including getD and the last result. The hull-transfer lemma discharges its local NAND rule whenever hull contains its union. The concrete RREF implementation is an executable reference with finite tests.

### Witness compression and reconstruction

Begin with the full domain H. Restrict each source variable to its affine normal form modulo H. Run the abstract scan on these normal forms, viewed as functions of the nonpivot variables. Intersect H with the final one-superset and repeat if its rank increases; an inconsistent intersection certifies UNSAT. On each restricted domain all previous valid witnesses remain, and the extended reduced equations involve only free coordinates before intersection. There are at most n rank increases. A fully recognized positive descriptor is decided by solving its intersection with H. For a recognized complement try violating one defining equation at a time in H. Thus the exact descriptor classes have direct SAT algorithms, even when the final hull alone is uninformative.

On the stable pass intern constants, affine bits and binary NAND nodes. Store integer node IDs and children; each raw gate contributes at most one raw NAND node and one replacement affine/constant node. Preserve shared cones, including when an input wire is referenced twice. Traverse backward once from the root. Let B be an RREF basis for the linear parts of all live affine forms, with rank r. Feature bits are y=Bw. Express each live form as the XOR of the basis bits selected by its pivot-column coefficients, plus its original offset. Every such combination matches the form on H. Given y, place it on B's pivot columns with zero elsewhere, then repair pivot variables of H to satisfy the required offsets. B has zero in every H-pivot column, so the repair preserves y. The pivot-patch theorem gives this binary-field identity, and a second application with an empty protected matrix gives exact realization of y. These operations yield project(lift(y))=y and pointwise output agreement on H. Necessity of H then gives both witness maps and equivalence of the two false statements. The Lean project/lift lemma records exactly these implications. The proof that the Python RREF, descriptors and synthesized gate IDs instantiate all premises is mathematical and tested, rather than a refinement proof for the Python program.

Number child inputs 1…r, with zero unused coordinates when embedding in the registered 128-input format. Checked parity synthesis uses a shared four-NAND XOR; a negation adds one NAND. Cache repeated NAND pairs. If the final output already names the last gate, move its definition to the final slot, inserting fresh, unreachable padding before it. Otherwise use a double negation ending at the final slot. All child gates use existing inputs or previously defined gates. A failed size test returns control to the fallback. A child WE supporting variable widths is optional: the emitted registered child has the original public arity. A backend gains from the narrower support only if its implementation exploits it.

### Mixed and unresolved cases

Column j of the 20-row syndrome matrix has packed components 1, j, j³, and the low five bits of j⁵ in the seven-bit representation with reduction polynomial X⁷+X+1. The predecessor's 42/43/43 cut-rank calculation concerns the syndrome guard alone; appending a nonlinear residual changes the predicate. Our fixture instantiates that same guard at the nonzero syndrome of witness 3. It ANDs the guard with (w0 AND w1) XOR (w2 AND w3). Repeated four-bit linear blocks share NANDs, and unused padding uses a legal forward index. The original and padded child evaluations agree for every lifted y. Each of the six accepting assignments has 2^104 preimages in the domain. The contradicted version requires both the first check and its negation. Separate tests checked every ordered descriptor pair through four bits and all 94,864 four-bit ordered affine-flat hulls against truth-table direction spans. Three hundred seeded five-input raw DAGs were checked on all original witnesses and all residual feature vectors, including source and child coordinate maps.

The extractor alone can overlook q AND (NOT q) once q has an unresolved nonlinear descriptor. On the four-bit example it returns zero mandatory equations while exact residual enumeration rejects every point. On a 4096-gate padded XOR of 64 independent pairwise NANDs it extracts zero equations and all 128 features remain live (316 child gates). This diagnoses the method on that input and gives no SAT time lower bound. On small r, decide the live child directly by checking up to 2^r assignments. On an unresolved gate with exact operands, choose the operand having fewer independent defining equations e₁,…,e_c. Partition the current domain into their common solution and cells whose first violated equation is e_i. Each cell is affine, the cells are disjoint, and their union covers the domain. The split makes the chosen operand constant; restriction preserves representability of each earlier exact wire. Re-run extraction on each nonempty cell. The first unresolved gate of the four-input quadratic example gave three cells with residual feature ranks 0, 0 and 2. Each cell was tested for source coverage and equivalence in both directions. Recursive splitting can have exponentially many leaves. A public node/clock cap and identity fallback give a total preprocessor.

### Ciphertexts and finite costs

For a directly decided public statement, output the one-bit message on YES and a fixed word on NO; Dec can return the first bit. For a compressed statement accepted by a selected backend, Enc returns exactly the child ciphertext. Dec recomputes the deterministic plan from the public statement, applies project, pads the witness, then runs child Dec. On a rejected or capped compression attempt a total backend can run on the original statement, leaving ciphertext and the adversary's original challenge distribution unchanged on this branch. The direct NO branch is perfectly secret. On compressed NO instances the child is false, but the registered attacker receives the tuple (parameters, original statement, ciphertext). Replacing the child statement by the original in that tuple, hardwiring it if needed, costs time and description bits. Equality of ciphertext laws gives equality of advantages for the translated attacker, not automatically the original finite cost/advantage-squared bound at 128 bits. For a public disjoint branch whose leaves use WE, independently encrypt the same message at every leaf and select the witness's leaf in Dec; NO requires every leaf false and a hybrid over all leaves. Charge their encryption, challenge simulations and advantage loss. No general cheap child WE is a premise of the direct SAT result.

With s raw gates, n inputs and L live affine nodes, one conservative dense-Elimination-RAM bound per pass is O((s+n)n³ log(n+2)) comparisons and operations on O(n)-bit rows, with O((s+n)n²) bits for wire systems plus IDs/headers. This allows the repeated relative-codimension tests. Hash-table operations in the Python prototype are host operations. An indexed deterministic dictionary implementation and all tape motion require their own accounting. At most n+1 passes plus Gaussian elimination produce B. Child NAND emission costs at most s+L(4 max(r−1,0)+1)+3 before optional padding, counting each live leaf only once. Direct exhaustive SAT after compression evaluates the *unpadded* child at most 2^r times. On the mixed example 16×10 logical NAND evaluations suffice after extraction. Reading the unary registered gate tuples is a separate cost: SigabaNeo.length_encGates_le with bound 4224 yields at most 103,821,312 bits for one statement. Both Enc and Dec may parse and compile it. The cost expression is time(Enc)+time(Dec)+descLen(Enc)+descLen(Dec), with each time its worst case separately, including every fallback. Neither the strict experimental target 2^32 nor the goal bound 2^100 has a machine-clock certificate here. The remaining obstacles are general fallback security and cost, verified parsing/elimination/child synthesis, and concrete reduction overhead.

### Executable audit

Run this single Python 3 listing. It contains the compiler, the registered fixtures, the constructor for disjoint cells, and the exhaustive finite checks.

```python
"""Exact affine/co-affine NAND abstraction. None is unknown only outside descriptors."""
# Row has constant in bit zero, inputs in the remaining bits. (1,) is the inconsistent system.
EMPTY=(1,); ALL=()
def reduce_rows(rows):
    basis={}
    for x in rows:
        for j in sorted(basis,reverse=True):
            if (x>>j)&1:x^=basis[j]
        if not x:continue
        if x==1:return EMPTY
        j=x.bit_length()-1
        for k,b in list(basis.items()):
            if b>>j&1:basis[k]^=x
        basis[j]=x
    return tuple(basis[j] for j in sorted(basis,reverse=True))
def canon(a,neg=False):
    if a==EMPTY:return (ALL,not neg)
    if neg and len(a)==1:return ((a[0]^1,),False)
    return (a,neg)
def negate(v):return canon(v[0],not v[1])
def minus(a,b):
    i=reduce_rows(a+b)
    if i==EMPTY:return canon(a)
    if i==a:return canon(EMPTY)
    if not a:return canon(b,True)
    if len(i)!=len(a)+1:return None
    for e in b:
        if reduce_rows(a+(e,))!=a:return canon(reduce_rows(a+(e^1,)))
    raise AssertionError()
def union(a,b):
    i=reduce_rows(a+b)
    if i==a:return canon(b)
    if i==b:return canon(a)
    if i==EMPTY and tuple(x>>1 for x in a)==tuple(x>>1 for x in b):
        k=next(j for j in range(len(a)) if a[j]!=b[j])
        return canon(reduce_rows(x^a[k] if x!=b[j] else x for j,x in enumerate(a) if j!=k))
    # Called on the excluded subspaces of two canonically negative descriptors.
    # A proper excluded subspace has codimension >=2, so their union is at most half.
    return None
def nand(x,y):
    if x==(ALL,True) or y==(ALL,True): return canon(ALL)
    if x is None or y is None:return None
    a,na=x;b,nb=y
    if na and nb:return union(a,b)
    if not na and not nb:return canon(reduce_rows(a+b),True)
    c=minus(b,a) if na else minus(a,b)
    return negate(c) if c is not None else None
def truth(desc,n):
    a,neg=desc
    return sum((int(all((r&(2*w+1)).bit_count()%2==0 for r in a))^int(neg))<<w for w in range(1<<n))
def exhaustive(n):
    aff={ALL,EMPTY}
    for eq in range(2,1<<(n+1)):
        aff|={reduce_rows(a+(eq,)) for a in aff}
    classes={truth(d,n):d for a in aff for d in (canon(a),canon(a,True))}
    top=(1<<(1<<n))-1
    for u,x in classes.items():
        for v,y in classes.items():
            z=nand(x,y);want=top^(u&v)
            assert (z is None)==(want not in classes)
            if z is not None: assert truth(z,n)==want
    print(n,'inputs;',len(classes)**2,'ordered pairs classified exactly')
def fieldmul(x,y):
    z=0
    for _ in range(7):
        if y&1:z^=x
        y>>=1;x<<=1
        if x&128:x^=131
    return z
def join(a,b):
    if a==EMPTY:return b
    if b==EMPTY:return a
    piv={};common=[]
    for equation in a:
        rem=equation;src=equation
        for y in b:
            if rem>>(y.bit_length()-1)&1:rem^=y
        while rem and (k:=rem.bit_length()-1) in piv:
            u,v=piv[k];rem^=u;src^=v
        if rem:piv[rem.bit_length()-1]=(rem,src)
        else:common.append(src)
    return reduce_rows(common)
def hull(v):
    a,neg=v
    if not neg:return a
    # Only co-affine sets remaining after canonicalization are empty, or
    # complements of proper subspaces of codimension at least two.
    return EMPTY if a==ALL else ALL
def fixture(target,bad,residual_builder=None):
    gates=[]
    def gate(a,b):
        gates.append((a,b));return 127+len(gates)
    def AND(a,b):
        t=gate(a,b);return gate(t,t)
    def XOR(a,b):
        t=gate(a,b);return gate(gate(a,t),gate(b,t))
    cols=[]
    for j in range(128):
        j2=fieldmul(j,j);j3=fieldmul(j,j2)
        cols.append(1|(j<<1)|(j3<<8)|((fieldmul(j2,j3)&31)<<15))
    rows=[sum(((c>>i)&1)<<(j+1) for j,c in enumerate(cols)) for i in range(20)]
    bank=[]
    for j in range(32):
        tbl={}
        for s in range(1,16):
            t=s&-s;a=4*j+t.bit_length()-1
            tbl[s]=a if t==s else XOR(a,tbl[s^t])
        bank.append(tbl)
    checks=[]
    for i in range(20):
        parts=[bank[j][s] for j in range(32) if (s:=((rows[i]>>1)>>(4*j))&15)]
        v=parts[0]
        for u in parts[1:]:v=XOR(v,u)
        checks.append(v if target>>i&1 else gate(v,v))
    q=(XOR(AND(0,1),AND(2,3)) if residual_builder is None else
       residual_builder(gate,AND,XOR,rows))
    for t in checks:q=AND(q,t)
    if bad:q=AND(q,gate(checks[0],checks[0]))
    last=gates.pop()
    gates += [(4223,4223)]*(4095-len(gates))
    gates.append(last)
    return [(i+1,j+1) for i,j in gates],reduce_rows([v^((target>>i)&1) for i,v in enumerate(rows)])
def reduce_form(f, rows):
    for row in rows:
        if f & (1 << (row.bit_length() - 1)):
            f ^= row
    return f

def bit(f, w):
    return (f & (2*w+1)).bit_count() & 1

def residual_pass(n, gates, domain, first_cut=None):
    nodes, ids = [], {}
    def intern(node):
        if node not in ids:
            ids[node] = len(nodes)
            nodes.append(node)
        return ids[node]
    def descriptor(v, expr):
        if v is not None:
            if v[0] == ALL:
                expr = intern(('C', int(not v[1])))
            elif len(v[0]) == 1 and not v[1]:
                expr = intern(('L', v[0][0] ^ 1))
            return (v, hull(negate(v)), hull(v), expr)
        return None
    default = descriptor(canon(ALL), None)
    wires = [default]
    for i in range(n):
        f = reduce_form(2 << i, domain)
        wires.append(descriptor(canon(reduce_rows((f ^ 1,))), None))
    for left, right in gates:
        a, a0, a1, x = wires[left] if left < len(wires) else default
        b, b0, b1, y = wires[right] if right < len(wires) else default
        z = nand(a,b)
        if z is None and a is not None and b is not None and first_cut is not None and not first_cut:
            first_cut.extend(min((a[0],b[0]),key=len))
        def normal(x,y):
            if nodes[x] == ('C',1) and nodes[y][0] == 'N' and nodes[y][1] == nodes[y][2]:
                return nodes[y][1]
            return None
        expr = normal(x,y)
        if expr is None:
            expr = normal(y,x)
        if expr is None:
            expr = intern(('N', min(x,y), max(x,y)))
        wires.append(descriptor(z,expr) or (None,reduce_rows(a1+b1),join(a0,b0),expr))
    z, _, target, root = wires[-1] if gates else default
    return z, target, nodes, root

def compile_affine(n, gates, domain=ALL):
    if domain == EMPTY:
        return None
    while True:
        z, target, nodes, root = residual_pass(n,gates,domain)
        merged = reduce_rows(domain + target)
        if merged == EMPTY:
            return None
        if merged == domain:
            break
        domain = merged
    active, todo = set(), [root]
    while todo:
        i = todo.pop()
        if i in active:
            continue
        active.add(i)
        if nodes[i][0] == 'N':
            todo.extend(nodes[i][1:])
    forms = {nodes[i][1] for i in active if nodes[i][0] == 'L'}
    basis = reduce_rows(f & ~1 for f in sorted(forms))
    pivots = [row.bit_length()-2 for row in basis]
    def project(w):
        return sum(bit(f,w)<<i for i,f in enumerate(basis))
    def lift(y):
        w = sum(((y>>i)&1)<<j for i,j in enumerate(pivots))
        for row in domain:
            if bit(row,w):
                w ^= 1<<(row.bit_length()-2)
        return w
    child, cache = [], {}
    def gate(a,b):
        key = (min(a,b),max(a,b))
        if key not in cache:
            child.append(key)
            cache[key] = n + len(child)
        return cache[key]
    def XOR(a,b):
        t = gate(a,b)
        return gate(gate(a,t),gate(b,t))
    wires = {}
    for i in sorted(active):
        node = nodes[i]
        if node[0] == 'C':
            v = 0 if node[1] else gate(0,0)
        elif node[0] == 'L':
            f = node[1]
            use = [j+1 for j,k in enumerate(pivots) if (f >> (k+1)) & 1]
            v = use[0]
            for j in use[1:]:
                v = XOR(v,j)
            if f & 1:
                v = gate(v,v)
        else:
            v = gate(wires[node[1]],wires[node[2]])
        wires[i] = v
    return domain, basis, project, lift, child, wires[root]

def pad_child(n, gates, out, size):
    gates = list(gates)
    if gates and out == n+len(gates):
        terminal = gates.pop()
    else:
        gates.append((out,out))
        terminal = (n+len(gates),)*2
    if len(gates)+1 > size:
        return None
    return gates + [(0,0)]*(size-len(gates)-1) + [terminal]

def runtime(n,w,gates):
    bits=[1]+[(w>>i)&1 for i in range(n)]
    for i,j in gates:
        bits.append(1^((bits[i] if i<len(bits) else 1)&
                       (bits[j] if j<len(bits) else 1)))
    return bits[-1] if gates else 1

def check(n,gates):
    status,witness=affine_decision(n,gates)
    if status=='yes':
        assert runtime(n,witness,gates)
    if status=='no':
        assert all(not runtime(n,w,gates) for w in range(1<<n))
    C=compile_affine(n,gates)
    if C is None:
        assert all(not runtime(n,w,gates) for w in range(1<<n))
        return
    H,B,project,lift,child,out=C
    padded=pad_child(n,child,out,max(2+len(child),len(gates)))
    for w in range(1<<n):
        inside=all(not bit(row,w) for row in H)
        assert runtime(n,w,gates)==(inside and runtime(n,project(w),padded))
    for y in range(1<<len(B)):
        w=lift(y)
        assert project(w)==y and all(not bit(row,w) for row in H)
        assert runtime(n,w,gates)==runtime(n,y,padded)

def point(rows):
    assert rows != EMPTY
    w = 0
    for row in rows:
        if bit(row,w):
            w ^= 1 << (row.bit_length()-2)
    return w

def affine_decision(n,gates):
    domain=ALL
    while True:
        z,target,_,_=residual_pass(n,gates,domain)
        if z is not None:
            A,negative=z
            candidates=([reduce_rows(domain+(e^1,)) for e in A] if negative
                        else [reduce_rows(domain+A)])
            for rows in candidates:
                if rows!=EMPTY:
                    return 'yes',point(rows)
            return 'no',None
        merged=reduce_rows(domain+target)
        if merged==EMPTY:
            return 'no',None
        if merged==domain:
            return 'residual',None
        domain=merged

def split_first_unknown(n,gates,domain=ALL):
    cut=[]
    residual_pass(n,gates,domain,cut)
    if not cut:
        return []
    prefix=list(domain)
    cells=[]
    for eq in cut:
        cells.append(reduce_rows(prefix+[eq^1]))
        prefix.append(eq)
    cells.append(reduce_rows(prefix))
    return [cell for cell in cells if cell!=EMPTY]
def exhaust_hulls(n):
    aff={ALL,EMPTY}
    for eq in range(2,1<<(n+1)):
        aff.update(reduce_rows(a+(eq,)) for a in list(aff))
    masks={a:truth(canon(a),n) for a in aff}
    for a,ma in masks.items():
        for b,mb in masks.items():
            mc=masks[join(a,b)]
            assert (ma|mb)&~mc == 0
            # The affine hull of unequal intersecting/disjoint flats has
            # direction span(U,V,b-a). The two ranks can be checked by
            # forming this span directly from the actual truth table.
            uv=ma|mb
            if not uv:
                assert not mc
                continue
            origin=(uv&-uv).bit_length()-1
            vectors=[(x^origin)<<1 for x in range(1<<n) if (uv>>x)&1]
            assert mc.bit_count()==1<<len(reduce_rows(vectors))
    print(n,'inputs;',len(aff)**2,'common-equation hulls match semantic direction spans')
def tests():
    from random import Random
    for n in (2,3,4):
        exhaustive(n)
        exhaust_hulls(n)
    rng=Random(157)
    for _ in range(300):
        n=5
        gates=[(rng.randrange(n+10),rng.randrange(n+10)) for _ in range(12)]
        check(n,gates)
    for bad in (False,True):
        g,H=fixture(2+256+32768,bad)
        C=compile_affine(128,g)
        if bad:
            assert C is None
            continue
        H,B,project,lift,c,out=C
        assert len(H)==20 and len(B)==4
        child=pad_child(128,c,out,4096)
        values=[]
        for y in range(16):
            w=lift(y)
            assert project(w)==y and all(not bit(r,w) for r in H)
            assert runtime(128,y,child)==runtime(128,w,g)
            values.append(runtime(128,y,child))
        assert sum(values)==6 and runtime(128,3,g)
        print('mixed: constraints',len(H),'feature rank',len(B),'live child gates',len(c),'accepted fibers',sum(values))
    # Six raw gates implement (x0 & x1) XOR (x2 & x3) up to common negations.
    g=[(1,2),(3,4),(5,6),(5,7),(6,7),(8,9)]
    check(4,g)
    H,B,_,_,c,out=compile_affine(4,g)
    assert H==ALL and len(B)==4 and pad_child(4,c,out,1) is None
    cells=split_first_unknown(4,g)
    assert cells
    for w in range(16):
        assert sum(all(not bit(r,w) for r in cell) for cell in cells)==1
    ranks=[]
    for cell in cells:
        C=compile_affine(4,g,cell)
        if C is None:
            assert all(not runtime(4,w,g) for w in range(16) if all(not bit(r,w) for r in cell))
            ranks.append(None)
        else:
            H,B,project,lift,c,out=C
            ranks.append(len(B))
            child=pad_child(4,c,out,len(c)+2)
            for w in range(16):
                if all(not bit(r,w) for r in cell):
                    assert runtime(4,w,g)==(all(not bit(r,w) for r in H) and runtime(4,project(w),child))
            for y in range(1<<len(B)):
                assert all(not bit(r,lift(y)) for r in cell)
                assert runtime(4,lift(y),g)==runtime(4,y,child)
    print('first unresolved-gate cell count and feature ranks',len(cells),ranks)
    # The scanner alone misses a contradiction when both operands lost their exact descriptor.
    # q AND (NOT q), with q the preceding unknown final wire.
    no=g+[(10,10),(10,11),(12,12)]
    assert all(not runtime(4,w,no) for w in range(16))
    C=compile_affine(4,no)
    assert C is not None and C[0]==ALL and affine_decision(4,no)[0]=='residual'
    check(4,no)
    print('affine-invisible four-input contradiction: zero mandatory rows, exact residual UNSAT')
    # Embed 32 nondegenerate four-bit blocks in 128 bits, composing via XOR.
    g=[]
    def gate(i,j):
        g.append((i,j))
        return 128+len(g)
    def xor(i,j):
        t=gate(i,j)
        return gate(gate(i,t),gate(j,t))
    terms=[gate(2*i+1,2*i+2) for i in range(64)]
    u=terms[0]
    for v in terms[1:]:
        u=xor(u,v)
    g=pad_child(128,g,u,4096)
    H,B,_,_,c,_=compile_affine(128,g)
    assert H==ALL and len(B)==128
    print('full-rank fallback: constraints',len(H),'feature rank',len(B),'child gates',len(c))
    print('300 five-input raw DAGs, all source witnesses and all lift coordinates checked')
if __name__=='__main__':
    tests()

```
