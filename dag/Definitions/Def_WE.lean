import SigabaNeo.Trusted.Assumption
import SigabaNeo.Trusted.Primitive

/-!
# Witness encryption

Witness encryption as a Sigaba Neo primitive (`SigabaNeo.Trusted.Primitive`), independent of any
implementation. It follows Definition 2.1 of Hair–Sahai, *Witness Encryption via Prime-Order
Generic Groups* (arXiv 2609.18275v3; after Garg–Gentry–Sahai–Waters, STOC 2013), made concrete in
the way of the Sigaba Neo concept: "`1 − κ(n)` for a negligible `κ`" becomes `1 − 2^{-κ}` and
"every nonuniform PPT adversary has advantage at most a negligible `ε_A(n)`" becomes "every
explicit adversary has `cost / advantage² ≥ 2^λ`".

**Relations.** A `Relation` is the paper's NP relation `R`: statements `φ` and witnesses `w`
with the encodings of both as bit strings, the relation `rel φ w` ("`w` is a witness for `φ`"),
and the description given to the algorithms. The language is `L = {φ : ∃ w, rel φ w}`
(`Relation.InL`). The relation is fixed outside the primitive; `WE R` is the primitive for `R`.
The paper's requirements that `R` be polynomial-time decidable and polynomially balanced are about
asymptotic families; at fixed parameters they are properties of the chosen `Relation` (for example
circuit satisfiability for circuits of bounded size), and the propositions do not need them. The
statements should have bounded length: a clocked `Enc` reads only a prefix of `φ`, so two statements
that share a long prefix, one in `L` and one not, would make false-statement security unattainable.
Conversely, at fixed parameters `Enc` could decide `L` by brute force, so a submission is only
meaningful at a cost well below that of deciding `L`.

**Parameters.** `λ` (`secBits`) and the correctness failure target `κ` (`corrBits`). Every
algorithm receives `(1^λ, 1^κ, desc)` first.

**Algorithms.**

| Algorithm | Inputs | Outputs | Randomized |
| --- | --- | --- | --- |
| `Enc` | `φ`, `β` | `ct` | yes |
| `Dec` | `φ`, `w`, `ct` | `β` | no |

The encodings of `φ` and `w` are fixed by the relation, and the bit `β` is encoded as the one-bit
word `[β]`; `ct` is the implementation's own. `Dec` outputs `⊥` by outputting a variable that is not
`[false]` or `[true]` (output words are decoded as tuples of variables, `Impl.run`). There is no setup: as in Definition 2.1, encryption takes only the
parameters, the statement and the message.

**Propositions.**

1. `Correct`: for every `(φ, w)` with `rel φ w` and every `β ∈ {0, 1}`,
   `Pr[Dec(φ, w, Enc(φ, β)) = β] ≥ 1 − 2^{-κ}` over the coins of `Enc`.
2. `FalseStatementSecure`: for every `φ ∉ L` and every adversary `A` (an explicit machine without
   oracles, given `(1^λ, 1^κ, desc)`, `φ` and `ct`, and outputting `[true]` for "1"),
   `cost A / Adv_A(φ)² ≥ 2^λ`, where
   `Adv_A(φ) = |Pr[A(φ, Enc(φ, 0)) = 1] − Pr[A(φ, Enc(φ, 1)) = 1]|`. No security is required
   for `φ ∈ L`. Quantifying the adversary after `φ` lets it depend on `φ` arbitrarily, which is the
   nonuniformity of the paper's adversary; its description length is counted in its cost.

**Model.** The propositions are in the standard model (plain machines). The generic-group model
in which the paper proves its construction secure is a property of that construction, not part of
Definition 2.1, and is not modelled here.

**Cost.** The steps of one run each of `Enc` and `Dec`, each counted at its worst case (the
machine's clock), plus the description length of each machine:

    time(Enc) + time(Dec) + descLen(Enc) + descLen(Dec)

`Enc` and `Dec` run equally often in a use of the scheme, so no number of runs is needed.

The description lengths exclude implementations that replace computation by a table hard-wired in
the control states, which the parameters being fixed would otherwise allow.
-/

namespace AdvancedEncryption

open SigabaNeo

namespace WE

/-- An NP relation: statements and witnesses with their encodings, the relation, and the
description given to the algorithms. -/
structure Relation where
  /-- The statements `φ`. -/
  Stmt : Type
  /-- The witnesses `w`. -/
  Wit : Type
  /-- The encoding of statements. -/
  encStmt : Stmt ↪ List Bool
  /-- The encoding of witnesses. -/
  encWit : Wit ↪ List Bool
  /-- `rel φ w`: `w` is a witness for `φ`. -/
  rel : Stmt → Wit → Prop
  /-- The description given to the algorithms. -/
  desc : List Bool

/-- The language of the relation: the statements that have a witness. -/
def Relation.InL (R : Relation) (φ : R.Stmt) : Prop := ∃ w, R.rel φ w

/-- The parameters of witness encryption. -/
structure Params where
  /-- `λ`: the bits of security of false-statement security. -/
  secBits : ℕ
  /-- `κ`: decryption fails with probability at most `2^{-κ}`. -/
  corrBits : ℕ

/-- The algorithms of witness encryption: `Enc` (`Alg.enc = 0`) and `Dec` (`Alg.dec = 1`). They
are numbered rather than an inductive type, whose compiler-generated `ctorIdx` the DAG gate rejects
as `implemented_by`. -/
abbrev Alg := Fin 2

/-- `Enc`, the algorithm `0`. -/
def Alg.enc : Alg := 0

/-- `Dec`, the algorithm `1`. -/
def Alg.dec : Alg := 1

/-- The signatures of the algorithms. -/
def sig (a : Alg) : AlgSig :=
  if a = Alg.enc then
    { name := "Enc", inputs := ["φ", "β"], outputs := ["ct"], randomized := true }
  else
    { name := "Dec", inputs := ["φ", "w", "ct"], outputs := ["β"], randomized := false }

/-- The propositions of witness encryption: correctness (`PropIndex.correctness = 0`) and
false-statement security (`PropIndex.falseStatementSecurity = 1`). -/
abbrev PropIndex := Fin 2

/-- Correctness, the proposition `0`. -/
def PropIndex.correctness : PropIndex := 0

/-- False-statement security, the proposition `1`. -/
def PropIndex.falseStatementSecurity : PropIndex := 1

variable (R : Relation)

/-- The encoded parameters given to every algorithm: `(1^λ, 1^κ, desc)`. -/
def paramsWord (p : Params) : List Bool :=
  encodeTuple [List.replicate p.secBits true, List.replicate p.corrBits true, R.desc]

/-- The encoding of a message bit `β`: the one-bit word `[β]`. -/
def encBit (β : Bool) : List Bool := [β]

/-! ### The algorithms of an implementation -/

section Algorithms

variable {R} (p : Params) (impl : Impl sig)

/-- `Enc(φ, β)`: the law of `ct`. -/
noncomputable def enc (φ : R.Stmt) (β : Bool) : PMF (List Bool) :=
  (impl.run Alg.enc (paramsWord R p) [R.encStmt φ, encBit β]).map fun out => out.getD 0 []

/-- `Dec(φ, w, ct)`: the law of its output variable (a point mass: `Dec` is deterministic). -/
noncomputable def dec (φ : R.Stmt) (w : R.Wit) (ct : List Bool) : PMF (List Bool) :=
  (impl.run Alg.dec (paramsWord R p) [R.encStmt φ, R.encWit w, ct]).map fun out => out.getD 0 []

end Algorithms

/-! ### Correctness -/

/-- The law of the output of `Dec(φ, w, ct)` for `ct ← Enc(φ, β)`. -/
noncomputable def decryptLaw (p : Params) (impl : Impl sig) (φ : R.Stmt) (w : R.Wit) (β : Bool) :
    PMF (List Bool) :=
  (enc p impl φ β).bind (dec p impl φ w)

/-- Correctness: for every `(φ, w)` in the relation and every bit `β`, decryption returns `β`
with probability at least `1 − 2^{-κ}`. -/
def Correct (p : Params) (impl : Impl sig) : Prop :=
  ∀ (φ : R.Stmt) (w : R.Wit), R.rel φ w → ∀ β : Bool,
    1 - ((2 : ℝ) ^ p.corrBits)⁻¹ ≤ (decryptLaw R p impl φ w β (encBit β)).toReal

/-! ### False-statement security -/

/-- The adversary's input for the encryption of `β` under `φ`: `(1^λ, 1^κ, desc)`, `φ` and
`ct ← Enc(φ, β)`. -/
noncomputable def challenge (p : Params) (impl : Impl sig) (φ : R.Stmt) (β : Bool) :
    PMF (List Bool) :=
  (enc p impl φ β).map fun ct => encodeTuple [paramsWord R p, R.encStmt φ, ct]

/-- False-statement security with `λ` bits: for every statement outside the language and every
adversary, `cost / advantage² ≥ 2^λ`, the advantage being that of distinguishing encryptions of
`0` (output `[true]`, "1") from encryptions of `1`. -/
def FalseStatementSecure (p : Params) (impl : Impl sig) : Prop :=
  ∀ φ : R.Stmt, ¬ R.InL φ → ∀ A : Machine,
    (2 : ℝ) ^ p.secBits *
        (Problem.decision (challenge R p impl φ false) (challenge R p impl φ true)).gain A ≤
      (A.cost : ℝ)

/-- The cost: one run each of `Enc` and `Dec`, at their worst-case steps, plus the description
length of each machine. -/
def cost (impl : Impl sig) : ℕ :=
  (impl.machine Alg.enc).time + (impl.machine Alg.dec).time +
    ((impl.machine Alg.enc).descLen + (impl.machine Alg.dec).descLen)

end WE

/-- Witness encryption for the relation `R` at the parameters `p`. -/
def WE (R : WE.Relation) (p : WE.Params) : Primitive where
  Params := WE.Params
  params := p
  encodeParams := WE.paramsWord R
  Alg := WE.Alg
  sig := WE.sig
  PropIndex := WE.PropIndex
  prop i p impl :=
    if i = WE.PropIndex.correctness then WE.Correct R p impl
    else WE.FalseStatementSecure R p impl
  cost _ impl := WE.cost impl

end AdvancedEncryption
