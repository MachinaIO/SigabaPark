import Definitions.Def_WE_CircuitSAT

/-!
# Witness encryption for NAND-circuit satisfiability with a cost cap

The problem of `AdvancedEncryption.WE.CircuitSAT` (witness encryption for NAND circuits with
`128` input bits and `2^12` gates, at `λ = κ = 128`, over the same registry) with one more
proposition: the cost is at most `2^100`.

**Why a cap.** `WE.CircuitSAT.P` only measures the cost `N` of a submission; it bounds neither the
running times nor the ciphertext length. At fixed parameters this admits submissions that are not
witness encryption in any useful sense:

* brute force: `Enc` decides the language and outputs `β` only for statements in it
  (`N ≈ 2^188` with explicit machines);
* padding: `Enc(φ, β) = 0^P ‖ β` with `P ≥ 2^128`. An adversary's input head moves one cell per
  step, so an adversary of cost below about `2^128` never reaches `β`, and false-statement
  security holds with no assumption (`N ≈ 2^128.6`);
* enumeration-based schemes (XWE from ABE, `N ≈ 2^145`).

Each of them costs at least about `2^128`, the work of reading or deciding over the whole witness
space. The cap `N ≤ 2^100` excludes all of them while keeping room for lattice constructions of
the GGH15 type (estimated at about `2^97`). Since `Enc` writes at most one output cell per step,
the cap also bounds the ciphertext length by `2^100` bits.

**Propositions.** `0` correctness and `1` false-statement security, exactly those of `Def_WE`
(`WE.Correct`, `WE.FalseStatementSecure`), and `2` the cost bound `WE.cost impl ≤ 2^100`. The cost
function is that of `Def_WE`.
-/

namespace AdvancedEncryption.WE.CircuitSAT.Capped

open SigabaNeo

/-- The cap on the cost: `N ≤ 2^costBits`. -/
abbrev costBits : ℕ := 100

/-- The propositions: correctness (`0`), false-statement security (`1`) and the cost bound
(`2`). -/
abbrev PropIndex := Fin 3

/-- Correctness, the proposition `0`. -/
def PropIndex.correctness : PropIndex := 0

/-- False-statement security, the proposition `1`. -/
def PropIndex.falseStatementSecurity : PropIndex := 1

/-- The cost bound, the proposition `2`. -/
def PropIndex.costBound : PropIndex := 2

/-- The cost bound: one run each of `Enc` and `Dec` plus both description lengths is at most
`2^costBits`. -/
def CostBounded (impl : Impl WE.sig) : Prop := WE.cost impl ≤ 2 ^ costBits

/-- Witness encryption for NAND-circuit satisfiability with 128 inputs and `2^12` gates, at
`λ = κ = 128`, with cost at most `2^100`. -/
def P : Primitive where
  Params := WE.Params
  params := CircuitSAT.params
  encodeParams := WE.paramsWord (relation inputs size)
  Alg := WE.Alg
  sig := WE.sig
  PropIndex := PropIndex
  prop i p impl :=
    if i = PropIndex.correctness then WE.Correct (relation inputs size) p impl
    else if i = PropIndex.falseStatementSecurity then
      WE.FalseStatementSecure (relation inputs size) p impl
    else CostBounded impl
  cost _ impl := WE.cost impl

/-- The registry: that of `WE.CircuitSAT` (decision LWE, Ring-LWE, Module-LWE, circular
Ring-LWE). -/
noncomputable def R : Registry := CircuitSAT.R

/-- The Submission proposition that Design AI proves for its submission `u`. -/
def SubmissionProp : Submission P R → Prop := Spec P R

/-! ### Checks of the definition -/

/-- The cost bound is the third proposition. -/
theorem prop_costBound (p : WE.Params) (impl : Impl WE.sig) :
    P.prop PropIndex.costBound p impl ↔ WE.cost impl ≤ 2 ^ costBits := by
  simp [P, PropIndex.costBound, PropIndex.correctness, PropIndex.falseStatementSecurity,
    CostBounded]

/-- An implementation whose `Enc` alone runs for more than `2^100` steps (for example one that
writes a ciphertext of `2^128` bits) violates the cost bound. -/
theorem not_costBounded_of_enc_time (impl : Impl WE.sig)
    (h : 2 ^ costBits < (impl.machine WE.Alg.enc).time) : ¬ CostBounded impl := by
  unfold CostBounded WE.cost
  intro h'
  have := Nat.le_add_right (impl.machine WE.Alg.enc).time
    ((impl.machine WE.Alg.dec).time +
      ((impl.machine WE.Alg.enc).descLen + (impl.machine WE.Alg.dec).descLen))
  omega

end AdvancedEncryption.WE.CircuitSAT.Capped
