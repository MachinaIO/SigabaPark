---
title: Witness encryption under public relation compilation and certified port projection
refs: [definition:WE, theorem:AdvancedEncryption.WE.Compiler.transport, theorem:AdvancedEncryption.WE.Compiler.affine_port_image, theorem:AdvancedEncryption.WE.Compiler.checked_section, definition:FixedHeaderMachine, theorem:AdvancedEncryption.WE.Compiler.fixed_header_cost, theorem:AdvancedEncryption.WE.Compiler.header_head_step, theorem:AdvancedEncryption.WE.Compiler.header_input_symbol, definition:FixedHeaderTrace, theorem:AdvancedEncryption.WE.Compiler.header_tick]
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


### A tape machine for the adversary's changed challenge header

A WE challenge is a concatenation frame(paramsWord) ++ frame(encoded statement) ++ frame(ciphertext). The core's frame writes a leading one before each bit and a trailing zero. On each fixed false statement the simulation may hard-wire the two public headers. It suffices to simulate an attacker's read-only input src ++ z on a physical input dst ++ z, for every suffix z, with the source work tapes and all output symbols preserved. Common trailing bits of src and dst can be included in z. When the headers are identical the original machine itself suffices.

FixedHeaderMachine is an explicit zero-oracle Sigaba Machine over the same fair coin alphabet. Let a and b be the source and target header lengths. Move the physical input head b cells to the right from its initial position one and plant a marker on one extra work tape in a final setup step. Run the source control with the virtual input position 0 through a encoded in finite control (0 is the left blank); one additional tag denotes the suffix. The physical input head parks at the first suffix cell while the simulated head reads the hard-wired header. In suffix mode read the physical symbol, and move the marker head by the same displacement as the physical head. A left move from the marker switches back to virtual position a while parking both heads. A right move from the physical right blank is clamped, so both heads stay. The original work actions, next/halt choice, output and corresponding coin are passed through. This includes empty headers and an empty shared suffix.

For a source input position j and suffix length n, the intended control tag is min(j,a+1), the marker-tape head offset is max(0,j-a-1), and the physical input head is at b+1+max(0,j-a-1). The registered head-step theorem proves that every clamped source movement preserves all three coordinates under the adapter's update equations. Consequently the virtual reader sees the appropriate public header bit, suffix bit or boundary blank. After setup, coupling each fair coin to its corresponding source step and inducting on steps preserves the original work tapes, output and halt state. The first b+1 setup steps ignore their coins. The head arithmetic and machine cost are formalized; the full instantiation of the PMF run-equality premise of the transport theorem from this configuration simulation remains to be kernel-checked.

**Cost with the native transition table.** For a source machine with s states, t steps and w work tapes the new counts are exactly b+1+s(a+2) states, t+b+1 steps and w+1 tapes. The extra clock is independent of the ciphertext length, even if the source machine crosses the header boundary repeatedly. In this machine model an additional tape triples the number of symbol combinations in the transition table and adds four bits per entry. The cost theorem bounds the complete time-plus-description cost by 2^34 times the original when a+b+3 <= 2^29. This is a conservative uniform bound and does not claim that a particular reduction loses 34 bits. In the registered 128-input, 4096-gate instance, unary wire indices are at most 4224 and length_encGates_le bounds the encoded gate list by 4096*(6*4224+3) bits. At (128,128) and empty description the parameter word is 515 bits. The full source header therefore uses at most 207643656 bits. To invoke this cost theorem one must separately bound the compiled target header (including its actual security parameters); an arbitrary polynomial compiler does not automatically meet this concrete bound. Using a target with lambda+34 bits requires a security theorem at that strength. This adapter concerns security-reduction costs; it charges no extra bytes to an honest ciphertext.

**Transition replay.** Save the following listing as HeaderAudit.lean in a DAG Lake workspace with the definition built and run lake env lean HeaderAudit.lean. It interprets the actual adapter and source transition functions, including ordinary work tapes and mixed move/coin/output behavior. It checks 26352 coupled finite runs with empty and nonempty headers and suffixes, early halts, clock exhaustion, clamped moves, boundary crossings and repeated returns. The same simulation code covers arbitrary source transitions; the tests themselves range over the listed probes only.

~~~lean
import Definitions.Def_FixedHeaderMachine
open SigabaNeo Turing SigabaNeo.Machine

private def follow (A : Machine) (word coins : List Bool) : List Bool :=
  let start := A.machine.initialConfig word
  let endCfg := coins.foldl (fun cfg bit =>
    match cfg.tapes.state with
    | none => cfg
    | some q =>
      match A.machine.tr q cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols Fin.elim0 bit with
      | .step act w mv => cfg.step act w mv
      | .query o _ => Fin.elim0 o) start
  endCfg.tapes.output

private def probe (moves : List SignType) (blank early : Bool) : Machine := by
  refine ⟨1,moves.length+1,⟨0,?_⟩,moves.length⟩
  intro q sym tapes _ coin
  let m := moves[q.val]?.getD 0
  let v := (sym.getD blank ^^ coin) ^^ (tapes 0).getD false
  exact .step ⟨m,fun _ => (some (some v),m),some v,
    if early && q.val == 2 then none else if h : q.val+1<moves.length+1 then some ⟨q.val+1,h⟩ else none⟩ Fin.elim0 Fin.elim0

private def choices {α : Type} (xs : List α) : Nat → List (List α)
  | 0 => [[]]
  | n+1 => xs.flatMap fun x => (choices xs n).map (x :: ·)

private def compareRuns : Nat × Bool := Id.run do
  let mut count := 0
  for a in [[],[false],[true,false,true]] do
    for b in [[],[true],[false,true,false]] do
      for suffix in [[],[false],[true,false]] do
        for moves in choices ([-1,0,1] : List SignType) 5 ++
            [[1,1,1,1,1,1,-1,-1,-1,-1,-1,-1,-1,1,1]] do
          for blank in [false,true] do
            for early in [false,true] do
              let A := probe moves blank early
              let B := fixedHeaderMachine A a b.length
              let coins := (List.range moves.length).map (fun j => j%3==0)
              let x := follow A (a++suffix) coins
              let y := follow B (b++suffix) (List.replicate (b.length+1) true ++ coins)
              if x != y then return (count,false)
              count := count+1
  return (count,true)
#eval compareRuns
~~~

**Native transition.** The input symbol agrees at every represented position, including both end markers. Once the adapter is in the embedded configuration, each native transition on a given coin reproduces the entire source configuration under the embedding. This theorem covers arbitrary work tapes and early halt. Its statement starts after setup. The initial seek and the complete fixed-clock PMF law are separate obligations.

**Reducing encryption arithmetic.** In the [VWW tensor encoder](https://eprint.iacr.org/2022/1140.pdf), consider a binary transition matrix M of width w, a factor S of shape n by n, and the nw by m public matrix A. Split A into w consecutive n by m row blocks. For each nonzero column k of M, compute B[k] = S A[k] once. For each row h, output the sum of B[k] over the indices with M[h,k] = 1. Distributivity gives exactly block h of (M tensor S)A over the chosen modulus, even for a zero row or for composite q. This changes neither the sampled preimage target nor any encrypted bits for common sampler coins. Given sparse row lists, u used columns and e nonzero entries, forming one target takes at most u n²m modular multiplications and O(u n²m + (e+w)nm) modular additions and stores. Dense materialization would require O(w²n²m) scalar multiply-adds. This accounting covers target formation only. The encoder still pays trapdoor and column sampling costs. Different branch factors require separate products.

For the full two-branch tensor encoding with H levels the transmitted payload before public framing is bounded by (2nm + 2(H-1)m²) ceil(log2 q) bits. Decryption with a witness evaluates one selected matrix per level using O(Hnm²) modular multiply-adds, in addition to trace construction, scanning and the final test. These are per-message-bit bounds. In the published parameter regime with fixed hardness exponent, H, w, n, m and log q are polynomial in the statement length and unary security parameter. This gives conditional polynomial honest costs. Quantum security for the registered problem and a bounded implementation of the samplers remain open. The following reference check compares the target with the direct indexed formula in 9540 cases across three moduli.

~~~python
from itertools import product

def factored(M,S,A,q):
    w,n,m=len(M),len(S),len(A[0])
    blocks=[[[sum(S[i][j]*A[k*n+j][t] for j in range(n))%q
              for t in range(m)] for i in range(n)] for k in range(w)]
    return [[sum(blocks[k][i][t] for k in range(w) if M[h][k])%q
             for t in range(m)] for h in range(w) for i in range(n)]

def dense(M,S,A,q):
    w,n,m=len(M),len(S),len(A[0])
    return [[sum(M[h][k]*S[i][j]*A[k*n+j][t] for k in range(w)
                 for j in range(n))%q for t in range(m)]
            for h in range(w) for i in range(n)]

def check():
    total=0
    for w,n,m,q in product((1,2,3),(1,2,3),(1,3),(2,9,17)):
        for entries in product(range(2),repeat=w*w):
            M=[entries[i*w:(i+1)*w] for i in range(w)]
            S=[[(3+7*i-2*j)%q for j in range(n)] for i in range(n)]
            A=[[(2+5*i+3*t)%q for t in range(m)] for i in range(w*n)]
            assert factored(M,S,A,q)==dense(M,S,A,q)
            total+=1
    return total
print(check())
~~~

## Using bounded-degree consequences to remove witness bits before encryption

The certificate-dual method in [the construction survey](pq-we-new-directions.md) looks for the constant one in a truncated polynomial ideal. Even when this test fails, the *affine part* of the same span can shrink the witness dimension for any subsequent backend. Use Boolean multilinear polynomials over F_2 on the input bits and auxiliary gate bits, with the output pinned. For a chosen degree and public work budget collect true-on-solutions equations (polynomials equal to zero): for example the degree-bounded monomial multiples of the gate equations, reduced modulo x_i^2=x_i. Store columns for their occurring monomials. Retain the row space intersection with the affine polynomials in the primary inputs by eliminating every auxiliary-containing or degree-at-least-two column first. In row echelon form take the rows with zero eliminated part. This includes cancellations between rows whose individual nonlinear parts do not vanish. With a restricted list it may find fewer consequences, but every returned consequence still holds on all satisfying inputs.

If one obtains 1=0, emit a fixed ciphertext independent of the bit. Otherwise solve the retained linear equations as x=x0+Bt, with t the free primary coordinates and k=number of free coordinates. Compile a verifier C'(t)=C(x0+Bt) using the original verifier C; retaining C prevents spurious solutions to the relaxation. For every satisfying x its free coordinates give t with C'(t)=1. Every satisfying t lifts by the displayed affine map. No witness is used in Enc. This is an exact YES/NO reduction on *all* instances, including unrefutable NO inputs. The false-instance hiding proof for the remaining ciphertext is a single call to the backend on C', with no statement-specific hardness assumption added by preprocessing. A fixed-assumption proof for a bounded-k backend therefore applies on the entire family reduced to its domain. An unresolved backend for general k remains unresolved.

A pass costs polynomial time in the actual number of rows and columns (dense elimination O(R P min(R,P)) binary operations for R rows and P columns); use fixed degree or explicit polynomial budgets. Generate the final verifier from the original one and the final affine map, with at most O(n(k+1)) extra Boolean gates via XORs and constants. A subsequent pass can recompile the smaller verifier and repeat up to n times if each successful pass removes a primary dimension; compose affine maps before final code generation. The preprocessing and the resulting *gate count* must be charged for a circuit-sensitive backend; fall back to the original circuit if the reduction increases its certified budget. For a small residual k, an unconditional terminal implementation enumerates 2^k inputs, emits the payload iff one accepts and otherwise emits zero. Its ciphertext and receiver each cost one bit/read, and its sender costs the preprocessing plus O(2^k |C'|). In particular polynomial preprocessing and k=O(log |C|) suffice even for NO instances for which the original chosen row list does not span one. This is a tractable subclass; the reduction gives no such k bound for unrestricted circuits.

For a scalable family take primary bits u,v,a_1,...,a_m, constraints a_i+uv=0 for all i and any additional polynomial-size verifier on those same bits. These equations can be supplied by an exact conjunction frontend. Subtracting the first equation from each other equation removes m-1 independent dimensions regardless of the additional verifier. The remaining three bits suffice, so the terminal sender makes at most eight verifier evaluations instead of up to 2^(m+2). Identifying shared products directly would achieve the same improvement in this family; elimination also applies when nonlinear terms cancel only in linear combinations of several rows.

The example checks an unsatisfiable system of nonlinear constraints whose rows alone do not span one, and an adjacent satisfiable system. The first two constraints imply a=b by cancellation. After substitution the remaining equations can be checked by enumeration over three bits instead of four. The general identity for the source and compiled solution sets is checked for both outcomes.

~~~python
# Polynomials are sets of monomials, each monomial a mask of variable positions.
a,b,u,v = (1,2,4,8)
def value(poly,x):
    return sum((x & m)==m for m in poly)%2
for pin in (0,1):
    # a=uv and b=uv imply a=b. Pin a(1+b) to 0 or 1.
    eq = [{a,u|v},{b,u|v},{a,a|b} ^ ({0} if pin else set())]
    high = sorted({m for row in eq for m in row if m.bit_count()>1})
    basis = {}
    aff = []
    for row in eq:
        row = row.copy()
        for m in high:
            if m in row:
                if m in basis:
                    row ^= basis[m]
                else:
                    basis[m]=row
                    break
        else:
            aff.append(row)
    assert aff == [{a,b}]
    sols = {x for x in range(16) if all(not value(row,x) for row in eq)}
    lifted = set()
    for t in range(8):
        x = ((t&1)*3) | ((t>>1)<<2)
        if all(not value(row,x) for row in eq):
            lifted.add(x)
    assert lifted == sols and len(sols)==(0 if pin else 4)
print("NO and YES fibers matched exactly; 16 to 8 candidates before residual checks")
~~~
