---
title: Perfect full-view privacy for a bounded two-input bilinear rank with one secret function key
refs: [definition:WE_CircuitSAT_Capped, theorem:AdvancedEncryption.WE.FusedRank.public_consumer, theorem:AdvancedEncryption.WE.FusedRank.triangular_frame, theorem:AdvancedEncryption.WE.FusedRank.one_key_frame_fibers, note:pq-we-split-communication-rank]
tags: [witness-encryption, information-theoretic, functional-encryption, bilinear, cost]
---

### A real private rank

Fix before setup R row slots, M column slots and a feature width d, over F₂. An input issuer may hold any private row vector u_i of length d or private column vector v_j of length d. The function issuer holds a private β∈F₂. Give the evaluator every issued row token, column token, and one function key. It must recover β u_i v_j on every pair, with dot product in F₂. For static equal-shaped left/right batches we prove **perfect equality of the complete view whenever all authorized output bits coincide**, even when every feature vector changes across the two worlds. Hidden input equality patterns need not agree. The setup knows the capacities alone. Each ordinal accepts a single input; exact replay can return its original token. No party builds a private child garbling or obtains another party's private input. This is a restricted one-key private-rank primitive with an exact finite sampler.

Take four coordinate blocks of sizes R,d,d,M and D=R+2d+M. Let G be the group of binary upper block triangular matrices with identity diagonal blocks, whose block (2,3) is a scalar multiple of the d-dimensional identity. Every other strictly upper block is arbitrary. Multiplication and inversion preserve this form: on block (2,3) the scalars add, and for a strictly upper block matrix N one has N⁴=0. The inverse of I+N is I+N+N²+N³. There are
`γ = 1 + 2d(R+M) + RM`
free bits for d≥1. Draw P,Q independently by sampling these bits directly. This is exactly uniform, finite, with no cutoff and no statistical error.

Let J_β be identity with the single additional (2,3) block βI. Under the shared private setup the distributed algorithms are:

* The i-th row issuer needs P and its own input; emit L_i=(e_i,u_i,0,0)P. Its leading block is e_i and need not be transmitted.
* The j-th column issuer needs Q and its own input; emit C_j=Q(0,0,v_j,e_j)ᵀ, interpreting v_j as a column. Its final block is e_j and need not be transmitted.
* The function issuer needs P,Q and β; emit H=P⁻¹J_βQ⁻¹ encoded by its γ free bits.
* Public evaluation returns L_i H C_j exactly. Cancellation gives β u_i v_j, including zero outputs. All selections may be repeated or combined arbitrarily.

The two setup components are private. Row and column encoders can be invoked after a function key has been issued, provided the security experiment has fixed the compared batches before setup. This statement gives a static game and does not assert adaptive LR security. The construction also handles one arbitrary private d×d matrix F in place of βI when block (2,3) is allowed to be arbitrary; replace the one key bit parameter by d². The result computed is u_i F v_j. Field-word variants require their own encoding and cost accounting.

### Full-view proof including the key

Stack raw row lifts in `A_s=[I,L_s,0]` with central block size 2d and L_s=[U_s,0]. Stack the transformed raw column lifts for world s in `J_s B_s=[0;W_s;I]` with W_s=[β_s V_s;V_s]. Equal outputs for *all* row/column pairs mean L₀W₀=L₁W₁, an equality of R×M matrices. Existence of the following proof-only change of coordinates suffices:
```
                    [ I    L₁−L₀    −L₀(W₀−W₁) ]
                T = [ 0       I          W₀−W₁ ]
                    [ 0       0             I  ].
```
It belongs to G, with zero scalar in its off-diagonal central block. Multiplication gives A₀T=A₁ and T J₁ B₁=J₀ B₀. The first block of the latter equality is exactly L₁W₁−L₀W₀. The triangular transport lemma supplies the same map in coordinates b'=b−W₁c+W₀c and a'=a+L₁b−L₀b'. Additivity of L_s,W_s produces the displayed block matrix.

Couple world-zero keys P₀,Q₀ to P₁=T⁻¹P₀ and Q₁=Q₀J₀⁻¹TJ₁. This bijection preserves uniform independent key tapes. The complete row lists A_sP_s coincide, the complete column lists Q_s B_s coincide, and P₁⁻¹J₁Q₁⁻¹=P₀⁻¹J₀Q₀⁻¹. Thus each transcript has exactly the same probability, including all ciphertexts, indices, the secret-function handle and all correlations. The fiber bijection is separately proved in Lean for any group when its row and column transports are supplied. Perfect equality covers even unlimited quantum postprocessing of the classical disclosures. There is no LWE or hybrid loss in this restricted primitive. The proof-only matrix T may involve RM dot products; the real encoders do not evaluate those products or receive both inputs.

Fresh per-slot ordinal coordinates matter. Without them a zero feature can produce a visibly zero row token while some nonzero input with the same all-zero output vector produces a nonzero token. A second function key from the same P,Q is also unsafe: ask for two keys in both worlds on all-zero features. Identical β values give identical public handles, while different β values give distinct handles. All functional outputs still agree. For a fixed predeclared capacity t, independent setups and a separate copy of each input token per function slot yield the t-fold product of the one-key views, with t-fold physical costs. This only implements the supported function family. Fresh randomness for one of P,Q while keeping other correlated records requires a new proof.

### Size, clocks and comparison with public SAT

| Field | Fixed binary length |
|---|---:|
| Function key | γ |
| One row token | 2d+M |
| One column token | R+2d |
| Full public frame | 1+4d(R+M)+3RM |
| Private setup coins | 2γ |

No trial to invert a random binary matrix occurs. The inversion polynomial and matrix multiplication have fixed lengths. For example a literal dense implementation forms the two inverses and the function key in six D×D products (two powers for each inverse, two products for the key), plus O(D²) bit additions. One dense product uses D³ bit ANDs and D²(D−1) bit XORs. Rows and columns each take at most one dense matrix-vector product; the lifted input has at most d+1 nonzero positions. One public selection uses a matrix-vector product and a scalar product. Time for feature extraction, encoding/reconstruction and input-head traversal is additional. A direct constant-tape simulation can store a constant number of D×D matrices and an output stream and linearly scan O(D² log D) cells for each indexed bit operation (with a logarithmic address overhead if needed); this gives a polynomial, conservative tape implementation recipe, not a checked registered Machine clock. Sequential decryption must pay to locate the selected records. The full proof compares fiber counts and invokes no computational adversary; a brute-force enumerator used to check the proof is not an honest runtime.

For R=M=2,d=8, each of two parties can independently issue two private 8-bit input strings directly as features. There are 69 key bits, 18 per token, 141 public bits and 138 exact setup coins. All four dot-product answers for one β are obtained on demand. No shared input-pair truth table or other party's input is needed to generate a token. Example public NAND circuits first compute the d pairwise bit products (two NANDs per AND) then sum them using four NANDs per XOR; arbitrary private u_i and v_j work without a circuit-recognition promise in this restricted rank primitive.

Finite controls independently enumerated every one of the 64² setup pairs in **each** of the eight d=R=M=1 input/function worlds, verified every decryption and compared multiplicities of all public frames. Both output classes had 2,048 possible frames, with equal multiplicities within a class and disjoint supports across classes. For R=M=2,d=1 we enumerated all 8,192 P per each of 32 input/function worlds, conditioned on H=I. For general H, conditioning leaves P uniform and replaces visible columns by the invertible public transformation H⁻¹ applied to the I-conditional columns, so this check covered the joint structure of the two-by-two case. The check found exactly ten cross-output matrices, with identical conditional frame counts whenever they matched.

For public WE with an efficiently certified separated factorization φ(x_i,y_j)=u_i v_j, the same transcript and correctness directly apply. The published split-rank note already gives public SAT testing by finding the factor spans and testing orthogonality. If all factor tables are explicit, public row/column elimination plus a basis-pair test avoids the RM truth-table scan; it may beat this private rank outright. The new result is private joint functionality on secret inputs and a hidden function coefficient, rather than an improved public solver. At two fully enumerated 64-bit halves, R=M=2^64; the 3RM term alone exceeds the registered 2^100 threshold. Even the key's RM term is an actual public field in this encoding. The construction is useful at a bounded inner rank with small capacities only when the actual private producer/consumer word admits such a separated bilinear form. A smaller group representation or a computationally compressed key requires a separate proof.

At the initial two-input WE rank the function count may be one, even though there are many input pairs. In the original BKS recursive reduction a starred child master at a fixed row can receive one derived key per outer function. The shared inner master also receives multiple AGG keys, and a D or AGG constructor emits a serialized private object. Those functions have not been expressed as small separated bilinear forms, and reduction hybrids can change controls and inputs. Duplicating the one-key frame for a bounded list of bilinear functions handles quantity only. The argument supplies neither function closure for the actual BKS producers nor an unrestricted WE solution. PR #140's issuer tree, PR #142/#143's materialized descendants and PR #148's scoped terminal path have different key interfaces and costs.
