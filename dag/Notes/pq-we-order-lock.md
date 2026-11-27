---
title: WE - the class lock survives every level order - pinned lock, output-first is locked after pinning out = 1, the only escapes are unit-propagation refutations from the output
refs: [definition:WE_CircuitSAT, definition:WE_CircuitSAT_Capped, definition:WE_MaskedGGH15, note:pq-we-native-hop-designs, note:pq-we-exposed-root-reachable-lemma, note:pq-we-point-insertion-frontier, note:pq-we-apg-width-ring-analysis, theorem:AdvancedEncryption.WE.NativeHop.lex_prefix_cubes, theorem:AdvancedEncryption.WE.OrderLock.pinned_walk_lock, theorem:AdvancedEncryption.WE.OrderLock.out_first_example_lock, theorem:AdvancedEncryption.WE.OrderLock.unit_chain_escape]
tags: [witness-encryption, ggh15, barrier, open-problem]
---
Design-AI sub-task (vv) on `Def_WE_CircuitSAT` and its capped version. The candidate is
APG′-direct (`pq-we-point-insertion-frontier`), with its proved moves from
`pq-we-exposed-root-reachable-lemma`: the co-located cover flip CC, dead resets, the symmetric copy
SCC, and the hypothetical `LEN`. Open PR #116 (note "pq-we-class-lock") proves `walk_lock`: with
the witness bits first (levels `< ℓ = 128`), no walk of class-covered moves reaches a full-cube
slot, whenever every class has a common non-falsified string. #116 names two escape hatches:
(a) put the output gate (or other gate values) first; (b) per-point certificate clauses. This note
studies (a) for every level order. Open PRs are cited by number only.

The three `OrderLock.*` theorems have complete Lean proofs (Mathlib tactics only). The search
results of §5 come from an exhaustive script, not from Lean. Everything else is an informal argument
checked step by step by the submitting agent.

## 0. Answer

1. **Generalized lock (§1, `pinned_walk_lock`).** For any level order, fix a depth `ℓ`, a set `P`
   of *pinned* levels below `ℓ`, and values `v` on `P`. The class of a slot is its program at the
   non-pinned levels below `ℓ`. Each class gets a witness string that equals `v` on `P`. Suppose
   that in the initial hybrid no slot is alive on its own class witness. Then no walk of
   class-covered moves and cover flips below `ℓ` ever produces a full slot. With `P = ∅` this is
   #116's `walk_lock`. Pinning is what output-first orders need.
2. **Output first is still locked (§2, `out_first_example_lock`).** The unit clause `(out)` sits at
   level 0 and is a valid CC cover there, so every unpinned class lock fails. Pin `out = 1`: a
   slot whose level-0 entry excludes `1` is alive on no class witness, and flips at level 0 never
   add a string with `out = 1`. The remaining condition is #116's condition with `out = 1`
   substituted. For the APG′ order with `out` moved to the front, it is literally #116's condition
   ("the witness-free clauses are satisfiable").
3. **Every order, depth 1 (§3).** Let `x` be the first non-output variable of the order, with `out`
   pinned to `1` if it comes earlier. Then the pinned lock holds at depth 1 whenever
   * (L1) the clauses of `Ψ` that do not mention `x` are satisfiable, and
   * (L2) `out` is not `NAND(x, x)`.
   This covers gate-first orders, reverse-topological orders, topological or interleaved orders
   (whose first variable is a witness bit), and "clause-blocks first". Let **F** be the family of
   `Ψ` for which (L1) holds for every non-output `x` and the output gate has two different inputs.
   For `Ψ ∈ F`, **no level order escapes**.
4. **The only escape is backward unit propagation (§4, `unit_chain_escape`).** In
   `out = NAND(n2, n2)`, `n2 = NAND(w, NAND(w, w))`, with the order `(out, n2, w, n1)`, eight CC
   flips on the clause slots reach the full slot. Every move is proved (CC with clause slots, in
   APG″). The walk is unit propagation from `(out)`, done in the order: (L2) fails and the CNF is
   refuted by unit propagation. Such a `Ψ` is refuted in polynomial time, so the encryptor can
   detect it. The escape does not reach hard instances.
5. **Search (§5).** In every small instance tested, the full slot is unreachable or the order is
   of the §4 type: the order starts with `out`, then the input of a NOT-shaped output gate.
   Reachability is tested with unlimited copies, CC, dead resets and arbitrary dead-slot changes.
   In every unreachable case the pinned lock applies, except some orders that put a dangling gate
   first. With an output gate that has two different inputs, all 1740 tested orders are locked.
6. **Hops (§6).** If an order were to escape, the lexicographic prefix-cube walk over that order
   has at least `max_j N_j` point hops, where `N_j` counts the length-`j` prefixes that fully
   falsify no clause. Witness-first, topological and output-first-then-witness orders keep
   `N_j ≤ 2^{128}`. A gates-first order has `N_G ≥ 2^{G_1}`, where `G_1` is the number of gates that
   read only witness bits. This exceeds `2^{128}` as soon as `G_1 > 128`, which is common for wide
   circuits.
7. **Remaining unproved move.** Unchanged: a class-crossing move (#116 §5). Reordering does not
   produce one.
8. **#114's size obstruction is unchanged (§7).** Reordering changes neither the number of levels
   (`128 + G ≈ 4224`) nor the widths.

## 1. The pinned lock

**Model** (as in #116 §1). Level `i` reads `x_i`. A slot program is `m : ℕ → Bool → Bool`, alive on
`x` iff `m i (x i) = 1` for all `i`. A clause slot (APG″) is the cube of strings falsifying its
clause. The final hybrid needs an all-ones slot.

**Data.**

* A depth `ℓ`, pinned levels `P` (predicate `pin`), and values `v`.
* `cls(m) = (m i)_{i<ℓ, i∉P}`.
* A map `z` from programs to strings. `z(m)` depends only on `cls(m)`, `z(m)_i = v_i` on `P`, and
  `z(m)` lies in `m`'s cube at the non-pinned levels below `ℓ` whenever `m` is nonempty there.

**Theorem (`pinned_walk_lock`).** Assume no initial slot is alive on its own `z`. Assume every
step changes one slot `d` in one of two ways:

* class-covered: every `x` alive in the new `d` is alive, before the step, in a slot of the new
  `d`'s class;
* a cover flip at `L < ℓ`: the cover `c` agrees with `d` below `L`, has `c(L, b) = 1` and is
  all ones after `L`, and only `d(L, b)` changes.

Then no slot is ever all-ones.

**Proof.** The invariant is "no slot is alive on its own `z`". Class-covered steps keep it, as in
#116. Take a low flip, and suppose the new `d` is alive on `x = z(new d)`.

* The cover `c` is nonempty at every non-pinned level below `ℓ`: below `L` it contains `x_i`, at
  `L` it contains `b`, and after `L` it is all ones.
* By the invariant `c` is not alive on `z(c)`. Since `z(c)` lies in `c`'s cube off `P` and `c` is
  all ones after `L`, `c` must fail at a pinned level `j ≤ L`.
* If `j < L`, the new `d` agrees with `c` at `j`, and `z(c)_j = v_j = x_j`. So the new `d` is not
  alive on `x`, a contradiction.
* If `j = L`, then `c(L, v_L) = 0`, so `b ≠ v_L = x_L`. The old `d` agrees with the new one
  everywhere except at `(L, b)`, so it is alive on `x`. It has the same class, because `L` is
  pinned. That contradicts the invariant for the old `d`. ∎

Unlike #116, no "cover nonempty below `L`" hypothesis is needed, and dead resets, `LEN`, SCC and
copies are class-covered exactly as in #116 §3. CC at `L ≥ ℓ` is class-covered because `d` and `c`
agree below `L`.

**Initial condition for clause slots.** For each class `K`, take the clauses whose literals at the
non-pinned levels below `ℓ` are exactly `K`. A clause with a pinned literal satisfied by `v` is
automatically satisfied. The remaining residues must have a common satisfying assignment that
equals `v` on `P`. Zero pads are dead.

## 2. Output first

With `out` at level 0, `(out)` is the program `[x_0 = 0]` followed by all ones. It is a CC cover at
level 0 for every slot. Every unpinned lock of depth `≥ 1` fails: `(out)`'s class cube is
`{out = 0}`, and `(out)` is alive on all of it. #116 §4 noted this and claimed no lock.

**Pin `out = 1`.** Then `(out)`, `(a ∨ out)` and `(b ∨ out)` are satisfied by `v`. The other
clauses lose the literal `¬out`. Flips at level 0 with the cover `(out)` add only strings with
`out = 0`, which no class witness contains. For the order "out, then witness bits, then gates",
take `ℓ = 129` with only `out` pinned. The classes are #116's witness classes, and the condition is
#116 §4's condition with `out = 1` in every class witness:

* `{w_i = 0}`: set the consumers to `1`;
* `{w_i = 1}`: set the gates that read `w_i` to `0`, or, for a clause `(¬w_i ∨ ¬b ∨ ¬out)`, set `b`
  to `0`;
* the witness-free class: the clauses without a witness literal are satisfiable with `out = 1`,
  which is #116's condition since `(out)` is one of them.

The only new exception is `out = NAND(w_i, w_i)`.

**Lean instance (`out_first_example_lock`).** #116's 4-variable CNF (`w`, `n1 = NAND(w, w)`,
`n2 = NAND(w, n1)`, `out = NAND(n2, n2)`) with the order `(out, w, n1, n2)`.

* `out` is pinned to `1`, and the class is the `w` entry.
* The class witnesses `(out, w, n1, n2)` are:
  * `(1,0,1,0)` for the clauses without `w`;
  * `(1,0,1,1)` for the class alive at `w = 0`;
  * `(1,1,0,0)` for the class alive at `w = 1`.
* Hence no walk produces a full slot, from any number of zero pads plus the eight clause slots.
* The exhaustive search agrees.

## 3. Every order: the depth-1 pinned lock

Let `x` be the first variable of the order other than `out`. If `out` comes first, pin it to `1`;
otherwise nothing is pinned. Take `ℓ` = the position of `x` plus one, so the class is `x`'s entry.
NAND-Tseitin clauses give three classes.

* **Literal `x`** (falsified at `x = 0`). The clauses `(a ∨ x)` and `(b ∨ x)` of `x = NAND(a, b)`
  leave the residues `(a)` and `(b)`. A consumer clause `(x ∨ c)` leaves `(c)`, or is satisfied
  when `c = out` is pinned. All residues are positive units, so "all ones" works.
* **Literal `¬x`.** The residues are `(¬a ∨ ¬b)`, `(¬y ∨ ¬c)`, and `(¬c)` for `c = NAND(x, x)`. If
  `c = out` is pinned, `(¬y)` remains. All are negative, so "all zeros, `out = 1`" works, unless
  `out = NAND(x, x)` makes a residue empty (L2).
* **No `x`.** The clauses not mentioning `x` must be satisfiable (L1). When `out` is not first,
  `(out)` is among them, so this includes `out = 1`.

So (L1) and (L2) suffice for every order. Freeing `x` and its consumers can make the circuit
satisfiable. When it does not, (L1) fails at this `x`, and the lock must use deeper or other pins.

**Family F.** In F, every non-output variable is *critical*: deleting its clauses makes `Ψ`
satisfiable. F is the natural hard family.

* Start from any unsatisfiable `φ` and repeatedly replace the consumers of a non-critical `x` by
  fresh inputs. This keeps `φ` unsatisfiable and only removes clauses, so refuting the result is
  at least as hard as refuting `φ`.
* The process stops in F.
* Caveat: the number of inputs can grow above 128.

Within F, every order the encryptor may choose, possibly depending on `φ`, is locked. So the
encryptor cannot escape by reordering.

**Designer-added clauses.** Clauses the encryptor adds must hold on every consistent assignment
with `out = 1` (#116 §4). They break (L1) only if `Ψ` minus `x`'s clauses becomes unsatisfiable,
that is, if the added clauses contain a refutation that avoids `x`. For hard `φ` a poly-time
encryptor cannot produce one. This is a heuristic remark, not a theorem.

## 4. The escape: unit propagation from the output

`unit_chain_escape` uses the order `(out, n2, w, n1)` for the same CNF, where
`out = NAND(n2, n2) = ¬n2`. In clause notation, each line below is one CC flip:

1. `(¬w ∨ ¬n1)` weakened by the cover `(out)` at level 0 gives `(¬out ∨ ¬w ∨ ¬n1)`.
2. With the cover `(¬out ∨ ¬n2)` at level 1 this gives `(¬out ∨ n2 ∨ ¬w ∨ ¬n1)`.
3. `(n2 ∨ w)` with `(out)` at level 0 gives `(¬out ∨ n2 ∨ w)`.
4. Resolving on `w` (cover 3, level 2) gives `(¬out ∨ n2 ∨ ¬n1)`.
5. `(n2 ∨ n1)` with `(out)` at level 0 gives `(¬out ∨ n2 ∨ n1)`.
6. Resolving on `n1` (cover 5, level 3) gives `(¬out ∨ n2)`.
7. Resolving on `n2` (cover `(¬out ∨ ¬n2)`, level 1) gives `(¬out)`.
8. Resolving on `out` (cover `(out)`, level 0) gives the empty clause, i.e. the full slot.

Every step is CC, which `pq-we-exposed-root-reachable-lemma` §3 proves, applied to clause slots
that share the pad secrets (APG″, #113 §5). The real multiset search with no spare pads also
reaches the full slot. So this is a **complete, proved walk** with 8 slots and 8 hops.

* It exists because the order begins with `out` and then `n2`. The clauses `(out)` and
  `(¬out ∨ ¬n2)` are *prefix-shaped*: their variables form an initial segment of the order. Such
  clauses are the covers that weakening needs.
* After pinning `out = 1` and the forced `n2 = 0`, both values of the next variable are already
  contradicted (by `(w)` and `(n1)`), so no pinned lock exists.
* The CNF is refuted by unit propagation (`out → ¬n2 → w, n1 → ⊥`).
* In general, the prefix-shaped covers come from forced literals along the order. When the forced
  chain stops before a contradiction, the first unforced variable satisfies the hypotheses of §3,
  given (L1).
* So escape (a) works exactly where it is useless: for formulas whose unsatisfiability the
  encryptor can see in polynomial time and replace by an encryption of nothing.

## 5. Exhaustive search

Script (not in the DAG):

* Slots are programs over `n ≤ 6` levels.
* The **relaxation** allows unlimited copies, never consumes a slot, and includes CC in both
  directions, dead resets, and any change to a dead slot that keeps it dead (a superset of `LEN`
  and SCC).
* The pinned-lock test tries every `ℓ`, every `P ⊆ [0, ℓ)` and every `v`.

Results:

* `#116`'s example, all 24 orders:
  * 22 orders: locked (pinned lock found) and unreachable;
  * `(out, n2, ·, ·)`: reachable (§4).
* Unsatisfiable random NAND circuits, two sets:
  * Set A: 1 input, 4 gates (6 instances, all 120 orders each). The output gate is often NOT-shaped
    (`out = NAND(g, g)`), and some gates dangle (have no consumer).
  * Set B: output `out = NAND(ga, gb)` with `ga ≠ gb`, built as `ga = NAND(u, v)` with `u ∧ v ≡ 0`,
    pruned to 5–6 variables (17 instances, 1740 orders: all 120 orders for the 5-variable ones,
    60 sampled orders otherwise).
* Results:
  * No case where the relaxation reaches the full slot while a pinned lock holds (consistent with
    the theorem).
  * Set B: every one of the 1740 orders is locked by a pinned lock, and none is reachable.
  * Set A: 50 of 720 orders are reachable. All of them have a NOT-shaped output and start with
    `out` followed by its input once dangling gates are removed from the order. This is the §4 pattern.
  * Set A: 24 orders have neither a lock nor reachability. All of them put a dangling gate (one
    with no consumer) first, and the pinned lock cannot skip that level. The relaxation shows they
    are still blocked.
* These instances are tiny (one or two effective inputs). The search supports the picture of §3–§4
  but proves nothing about large circuits.

## 6. Hop count over all levels

The lexicographic walk (`lex_prefix_cubes`) over an order `O` pads one maximal falsified prefix
cube per point hop. Their number is the number of leaves of the decision tree that reads the levels
in order and stops when a clause is fully falsified. This is at least `max_j N_j`, where `N_j` is
the number of length-`j` prefixes that fully falsify no clause.

* **Witness-first** (APG′): `N_j ≤ 2^{128}`; there are `2^{128}(G + 1)` leaves
  (#113 §2).
* **Output first, then witness**: one extra leaf (`out = 0`), otherwise the same.
* **Topological or interleaved** (each gate right after its inputs): every gate is determined when
  read, so `N_j ≤ 2^{128}` and the leaves number `≤ 2^{128}(G + 1)`.
* **A gate before its inputs:** both of its values survive until its inputs are read.
  * For gates-first, a gate that reads only witness bits has only clauses that contain witness
    literals. So these `G_1` gates are free in a gates-only prefix, the other gates can be set
    consistently, and `N_G ≥ 2^{G_1}`.
  * This exceeds the `2^{128}·poly` budget when `G_1 > 128 + O(log)`.
* So even ignoring the lock, only topological-type orders and output-first-then-witness keep the
  hop count at `2^{128}·poly`. These are exactly the orders that §2 and §3 lock.

## 7. Effect on #114's size obstruction

`pq-we-apg-width-ring-analysis` bounds the cost by:

* the number of levels `h = 128 + G ≈ 4224`, one per variable, independent of the order;
* the pad width forced by small-public-matrix LWE, independent of the order;
* `m ≥ 4N log q`.

Reordering permutes the levels and changes none of these quantities. That note's reordering
analysis already covers this. APG′ stays above `2^{100}` in every order.

## 8. Formal results (Lean, complete proofs)

| Theorem | Content | Used in |
| --- | --- | --- |
| `OrderLock.pinned_walk_lock` | with pinned levels: class-covered moves and low cover flips keep "no slot alive on its class witness", so no all-ones slot ever appears | §1 |
| `OrderLock.out_first_example_lock` | output-first order `(out, w, n1, n2)` for #116's CNF: locked with `out` pinned to `1` | §2 |
| `OrderLock.unit_chain_escape` | order `(out, n2, w, n1)`: eight explicit CC flips reach the all-ones program | §4 |
