---
title: Splitting a CNF witness by covering opposite-literal occurrences with clauses and variables
refs: [definition:WE_CircuitSAT]
tags: [witness-encryption, compilation, cost]
---

Take any partition of the clauses of a CNF into L and R. Remove tautologies
and repeated literals first and treat an empty clause as an immediate NO.
For every left clause A and right clause B containing opposite literals of
variable x, add the triple (A,x,B). Pick a hitting set consisting of
variables V and clauses C from either side. This is a syntactic certificate
verifiable in polynomial time. One may start with all crossing variables
and replace groups by incident clauses if this lowers the branch count;
optimal hitting set computation is unnecessary.

Branch on the bits of V and on one chosen literal of each clause in C.
The latter is required to be true and therefore fixes its variable globally.
Skip inconsistent choices. Apply all fixed bits to both sides and delete
satisfied clauses and false literals. The number of branches before pruning
is at most T = 2^|V| times the product of the lengths of clauses in C.
Every residual cross-side opposite-literal pair would give a triple with
no selected endpoint: selected variables have been fixed and selected
clauses have been satisfied. Hence any variable still occurring on both
sides occurs there with a common single polarity. Set every such variable
globally to satisfy it and simplify both sides once more. Now the residual
verifiers have disjoint variable sets. Even a joint witness which originally
assigned a common-polarity variable the other way can use this branch:
changing it to the satisfying polarity preserves all clauses.

Use two independent local WE encryptions per surviving branch to share m
as s and s XOR m, sampling s independently in each branch. A satisfying
assignment picks the matching V bits and one true literal from each selected
clause; its restrictions after simplification satisfy both local verifiers.
Conversely two local witnesses for the same branch combine by union with
the fixed bits and common-polarity assignments, yielding a global witness.
On NO each branch therefore has a false leaf. The usual hybrid switches
the payload one branch at a time, sampling the other share uniformly.
Nonuniform QPT security permits hardwiring the index and false side.
The advantage is at most T times the worst applicable local bound at
the simulation cost. The ciphertext may use canonical branch order and
the decryptor need only access its branch's two leaf ciphertexts, charging
branch lookup and parsing time. Branch preparation costs T times polynomial
simplification work. This method also permits brute-force leaf WE, with
the actual number of residual variables on each side charged separately.
A polynomial branch count alone does not make unrestricted leaves efficient.

**Example.** Put many clauses (x OR u_i) on the left and (NOT x OR v_j)
on the right, with fresh private variables, and put (a OR b OR c) on
the left and three clauses (NOT a OR z_a), (NOT b OR z_b), (NOT c OR z_c)
on the right. Take V={x}, C={(a OR b OR c)}. This gives six branches
before simplification; assigning all four crossing bits would use sixteen.
Arbitrary private constraints can be added on either side without adding
crossing triples. Counts concern the specified branching methods, not a
lower bound on general algorithms. A compiler may compare its full leaf
costs with the unsplit verifier before using the transformation.

The construction applies syntactically to arbitrary Tseitin CNF, including
the output constraint. It turns the sparse-resource intuition into an explicit
consistency certificate without making a promise that all NP instances
possess a small certificate of this form. Its use of local WE is conditional
on the chosen leaf implementation; no general polynomial WE theorem follows.
