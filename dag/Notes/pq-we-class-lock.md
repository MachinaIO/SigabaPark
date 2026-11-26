---
title: WE - class lock for APG'-direct - every class-covered slot move (cover flips on pads or clause slots, dead resets, copies, LEN) keeps the full-cube hybrid unreachable; a class-crossing cover is needed
refs: [definition:WE_CircuitSAT, definition:WE_CircuitSAT_Capped, definition:WE_MaskedGGH15, definition:GGH15, note:pq-we-native-hop-designs, note:pq-we-exposed-root-reachable-lemma, theorem:AdvancedEncryption.WE.ExposedRoot.dead_level_invisible, theorem:AdvancedEncryption.WE.ExposedRoot.colocated_part, theorem:AdvancedEncryption.WE.ClassLock.walk_lock, theorem:AdvancedEncryption.WE.ClassLock.cover_flip_high_covered, theorem:AdvancedEncryption.WE.ClassLock.dead_alive_nowhere, theorem:AdvancedEncryption.WE.ClassLock.tseitin_example_lock]
tags: [witness-encryption, ggh15, barrier, open-problem]
---
Design-AI sub-task (tt) on `Def_WE_CircuitSAT` and its capped version. The candidate is
APG′-direct: the masked γ⊗-GGH15 with one shared pad block and the single exposed left row
`R = P·A_0` (`pq-we-native-hop-designs` §6, `pq-we-exposed-root-reachable-lemma` §3). All hops
except point insertion PI are proved from LWE in `pq-we-exposed-root-reachable-lemma`. Open PR
#113 (note "pq-we-point-insertion-frontier") reduces PI to two atoms, `LEN` (a value-preserving
zero flip on a dead chain) and `NCF` (a cover flip whose cover is a clause slot that is not
co-located), and proves an alive-prefix invariant `J_Fals` for cover flips, dead resets and copies.
This note asks whether some move can break that obstruction, and answers with a stronger one.
"CC" is the co-located cover flip of `pq-we-exposed-root-reachable-lemma` §3, "dead reset" its §4
move, "SCC" the symmetric copy of #113 §5.

The four `ClassLock.*` theorems have complete Lean proofs (Mathlib tactics only). Everything else is
an informal argument checked step by step by the submitting agent.

## 0. Answer

1. **No direction (1)–(3) yields a proved move that reaches the final hybrid.** Instead we prove an
   impossibility for a class that contains every move proved so far, and also `LEN`.
2. **Class lock (§2, `walk_lock`).** Fix a depth `ℓ` (for APG′, `ℓ = 128`, the witness levels).
   The *class* of a slot is its program at the levels `< ℓ`. A move is *class-covered* if every
   string alive in the changed slot afterwards was alive, before the move, in some slot of the same
   class. Suppose that for every class the scheme's clauses of that class have a common
   non-falsified string inside the class cube. Then no walk of class-covered moves and cover flips
   at levels `< ℓ` ever produces a full-cube slot. The number of slots and the number of hops are
   arbitrary.
3. **What the class contains (§3).**
   * CC at any level `L ≥ ℓ`, with *any* two slots as flipped slot and cover, including clause
     slots in the shared-secret variant APG″ (#113 §5), where clause slots may themselves be
     flipped. This closes a gap in #113's level-0 lock, which never flips a clause slot
     (`cover_flip_high_covered`).
   * CC at levels `< ℓ`: it cannot occur, since the lock invariant rules out its cover.
   * Dead resets, `LEN`, kills, and every move that leaves the changed slot dead
     (`dead_alive_nowhere`).
   * Copies (SCC with a pad or clause partner, CC into a dead slot).
4. **When the hypothesis holds (§4).** For NAND-Tseitin CNFs with the witness levels first, every
   class except the witness-free one is always satisfiable. So the lock applies to every `Ψ` whose
   **witness-free clauses are satisfiable**, i.e. whose unsatisfiability needs the witness bits. The
   gate order and the hybrid order do not matter. An explicit 4-variable instance is checked in Lean
   (`tseitin_example_lock`). For the same instance with no spare slots, an exhaustive search over
   the move graph (CC, dead resets, SCC, 10065 configurations) finds no full slot.
5. **Consequence (§5).** Every proof of PI must contain a **class-crossing move**: a slot gains
   strings that, before the move, are alive only in slots of other classes. `NCF` and "string PI"
   are such moves; `LEN` is not. So `LEN` is not the bottleneck. Proving `LEN` (direction 1) would
   not help without a crossing move. Directions 2 and 3 only relocate the crossing (§5).
6. **Cost.** Unchanged (`pq-we-exposed-root-reachable-lemma` §6). The lock does not depend on the
   slot count.

## 1. Model

* Level `i` reads bit `x_i` of the string `x`. A slot program is `m : ℕ → Bool → Bool`. The slot is
  *alive* on `x` if `m i (x i) = 1` for all `i`; with shared pad secrets its contribution to `V(x)` is
  `S_x a_h^{(m)}` when alive and noise otherwise (`colocated_part`). Pads start as the zero program.
  A clause slot (APG″) is the cube `Q_κ` of strings falsifying `κ`: entry `[b falsifies κ's
  literal]` at `κ`'s variables, `1` elsewhere.
* The mask block is not a slot: it is alive everywhere, but a step using it as a cover would be the
  WE statement itself (#113 §6).
* The final hybrid (`pq-we-exposed-root-reachable-lemma` §5) needs one all-ones slot.
* **Class at depth `ℓ`:** `cls(m) = (m i)_{i<ℓ}`. A **class witness** is a map `z` from programs to
  strings with `z(m)` depending only on `cls(m)` and lying in `m`'s class cube whenever no level
  below `ℓ` is dead.

## 2. The lock

**Invariant `I`.** No slot is alive on the witness of its own class.

**Theorem (`walk_lock`).** Let `z` be a class witness. Assume `I` holds at time 0 and that each
step changes one slot `d` in one of two ways:

* class-covered: every `x` alive in the new `d` is alive, before the step, in some slot of the new
  `d`'s class;
* a cover flip at level `L < ℓ`: the cover has a nonempty entry at every level below `L`, entry `1`
  at `(L, b)`, and only `1`s after `L`.

Then no slot is ever all-ones.

**Proof.** Induction on time.

* A class-covered step moves aliveness on `z(new d)` to a slot of the same class, which has the same
  witness. So `I` is kept.
* A low cover is nonempty at every level below `ℓ` and all-ones from `ℓ` on. So it is alive on its
  own class witness, which contradicts `I`: such a step never happens.
* An all-ones slot is alive on its witness. ∎

**Initial hybrid.** Zero pads are dead. A clause slot is alive exactly on the strings falsifying
its clause. So `I` at time 0 says: for every class `A`, some string in `A`'s cube satisfies every
clause of class `A`. Classes without clauses need only some string in their cube.

## 3. Which moves are class-covered

* **CC at `L ≥ ℓ`** (`cover_flip_high_covered`). `d` and the cover `c` agree below `L`, so they
  have the same class, and `d`'s class does not change. A string newly alive in `d` has `x_L = b`,
  so it is alive in `c`. This holds in either flip direction, and for any slots, pads or clause
  slots, as `d` or `c`.
* **CC at `L < ℓ`.** If the cover is dead below `L`, then so is `d`, which stays alive nowhere.
  Otherwise the second alternative of the theorem rules it out.
* **CC with a clause slot as `d`** (APG″). In clause terms, CC with `c = A ∨ ℓ_L` (`ℓ_L` on `c`'s
  deepest variable) and `d = A ∨ ¬ℓ_L ∨ T` (same literals as `c` above `L`, `T` below `L`) replaces
  `d` by `A ∨ T`. This is ordered self-subsuming resolution. In a dead slot with `c`'s upper part,
  CC writes the weakening `A ∨ ℓ_L ∨ T` (a copy).
  * Example: `(x), (¬x ∨ y), (¬y)` with `x` first is refuted by three such steps.
  * So in APG″ the calculus is not empty, and #113's level-0 lock (which only constrains pads)
    misses it. The class lock covers it.
* **Dead reset, `LEN`, killing a slot.** The new `d` has a dead level, so it is alive nowhere
  (`dead_alive_nowhere`). `LEN` ends with `d` dead at the output level.
* **Copies.** SCC (pad or clause partner) and CC into a dead slot make `d` a copy, or a
  sub-cube, of its partner `c`, which has the same class.
* **L4.4-S and leaf-first steps.** They change no program.

## 4. When the hypothesis holds

Take APG′'s level order: witness bits `w_0 … w_127`, then gates in any order. Let `ℓ = 128`.
NAND-Tseitin clauses for `c = NAND(a, b)` are `(a ∨ c)`, `(b ∨ c)` and `(¬a ∨ ¬b ∨ ¬c)`, plus the
unit `(out)`. A class is the set of witness literals a clause carries.

* `{w_i = 0}` (clauses `(w_i ∨ c)`): set all such `c = 1`.
* `{w_i = 1}` (clauses `(¬w_i ∨ ¬b ∨ ¬c)`, `(¬w_i ∨ ¬c)`): set all such `c = 0`.
* `{w_i = w_j = 1}` (clauses `(¬w_i ∨ ¬w_j ∨ ¬c)`): set `c = 0`.
* **Witness-free class:** all clauses with no witness literal. This is the only real condition:
  `Ψ` minus every clause that mentions a witness bit must be satisfiable.

The condition fails when the gates alone are contradictory, e.g. `t = NAND(g, NAND(g, g)) ≡ 1`
feeding `out = NAND(t, t)`. There the contradiction does not need the witness, and no exponential
walk is needed either. The condition holds when deleting the clauses that touch witness bits
leaves a satisfiable CNF, as in the explicit instance below, where the contradiction relies on two
gates reading the same witness bit consistently.

**Explicit instance (`tseitin_example_lock`).** Levels `w, n1 = NAND(w, w), n2 = NAND(w, n1),
out = NAND(n2, n2)`, with `ℓ = 1`.

* The CNF is unsatisfiable (`decide`).
* The class witnesses are:
  * `(0,1,0,1)` for the clauses without `w`;
  * `(0,1,1,·)` for the class alive at `w = 0`;
  * `(1,0,0,0)` for the class alive at `w = 1`.
* Hence no walk of class-covered moves and level-0 cover flips, from any number of zero pads plus
  the clause slots, produces a full slot.

**Robustness.**

* The gate order is irrelevant, because the classes are read on the witness levels only.
* Any extra clauses the encryptor adds (for correctness they must be implied by `Ψ`) are allowed,
  as long as each class stays satisfiable in its cube.
* What does break the hypothesis is clauses that make a class contradictory. An example is
  "certificate" clauses `¬k ∨ C` for a single non-witness `k`, which hard-code PI for `k`. There are
  `2^{128}` points, so this cannot cover the walk.
* Orders that put gates first change the classes. A depth-1 lock still applies when the first
  variable is a non-output gate whose removal leaves `Ψ` satisfiable (each world is satisfiable as in
  the list above). Putting `out` first escapes it, since `(out)` is a level-0 unit. Then CC performs
  unit resolution from the output. That stalls at once for NAND (`out = 1` only gives
  `¬a ∨ ¬b`), but we do not claim a lock for every order.

## 5. The three directions of the task

**(1) `LEN` via the exposed-root lemma.** Not proved.

* Before the flip, the dead chain's rows at levels `≥ j` are unreachable (`dead_level_invisible`),
  so (a) of L4.4-S holds and `W` is a permutation, so (b) holds. This is the dead-reset proof.
* After the flip, the `d`-rows at levels `j, …, out−1` are reachable along `k g*`. In the
  lexicographic hybrid no other pad is alive on `k_{≤j}`, so no slot is co-located with `d` there.
* The only short-lift direction would be the `d`-direction itself, which now sits inside reachable
  rows next to mask and clause parts with large coefficients. Hypothesis (b) then fails, as for the
  deep complements of `pq-we-exposed-root-reachable-lemma` §2.
* A "dead-chain cover" with the same program after the flip would itself be a `LEN` output.
* More importantly, `LEN` is class-covered (its output is dead), so by §2 a proof of `LEN` would not
  advance the walk.

**(2) Making `NCF`'s clause target unshared.**

* Per-prefix re-randomisation needs, for each witness prefix `p`, a slot of class `p` carrying
  `κ`'s cube. Creating it from `κ`'s slot (class: `κ`'s witness literals) is a crossing move.
  Building such slots into the scheme costs one per `(κ, p)` pair, `≈ 2^{128} G` in the walk.
* A tree of clause copies "only at the needed levels" has the same issue. Copies are class-covered
  and stay in `κ`'s class. Restricting a copy at a witness level `i` above `κ`'s variables is a
  1→0 flip whose cover has an all-ones tail after `i`. So it is a low cover (excluded), or it pads
  strings with `w > k` (not available).
* An adaptive erasure order does not help. `walk_lock` holds for every walk, so no ordering of
  hops, lexicographic or clause-driven, avoids a crossing move.

**(3) Clause-indexed bookkeeping.**

* The sets `Q_κ ∩ p∗` ("falsify `κ` with prefix `p`") have class `p` whenever `p` fixes witness
  bits outside `κ`. So inserting them from `κ` is a crossing move.
* As slots in the scheme there are `2^{|p|}·|Ψ|` of them, exponential for `|p| ≥ 128`.
* With only clause cubes `Q_κ` (APG″), the moves form the resolution calculus of §3. The lock shows
  that it refutes no `Ψ` whose witness-free clauses are satisfiable.

**What a proof must contain.** A move that makes slot `d` alive on strings covered, before the move,
only by slots of other classes. Typically the cover is a clause slot alive on many witness
prefixes, used as a pad for one of them. That is exactly the pad-reuse situation of #113
(`pad_reuse_span`). Every LWE step used so far gets its hidden direction from co-location:
identical programs above the flipped level, or an unreachable dead chain. Such steps are
class-covered. We state this last sentence informally; the Lean class is the explicit one of §2.

## 6. Formal results (Lean, complete proofs)

| Theorem | Content | Used in |
| --- | --- | --- |
| `ClassLock.walk_lock` | class-covered steps and low cover flips keep "no slot alive on its class witness", so no all-ones slot ever appears | §2 |
| `ClassLock.cover_flip_high_covered` | a cover flip at `L ≥ ℓ` is class-covered (old slot or cover, both of the new slot's class) | §3 |
| `ClassLock.dead_alive_nowhere` | a program with a dead level is alive on no string (dead resets, `LEN`, kills) | §3, §5 |
| `ClassLock.tseitin_example_lock` | an unsatisfiable 4-variable NAND Tseitin CNF whose clause slots never yield an all-ones slot under class-covered moves and level-0 cover flips | §4 |
