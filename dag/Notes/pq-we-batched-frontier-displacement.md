---
title: Testing an entire frontier displacement and a one-sided decision consequence
refs: [definition:WE_CircuitSAT]
tags: [witness-encryption, reduction, construction, complexity]
---

Can the point-insertion walk from [PR 113](https://github.com/MachinaIO/SigabaPark/pull/113)
be shortened by translating the entire violating set at once? The following
test finds such a translation when it exists in a linear mask bank. It also
gives a stronger limitation than counting separately isolatable prefixes.

Let R=Z/q and r_x=s product_i M_(i,x_i) in R^d for every h-bit path x.
Specify the desired shift on each path by a second matrix program in the
same input order: f(x)=u product_i N_(i,x_i) v, with width k. This includes
a constant shift and a shift on a lexicographic interval (track comparison
with each endpoint using a constant-state automaton). We seek a *single*
column z with r_x z=f(x) for every x. Additional known linear constraints
on z, such as exposed linear observations that must remain fixed, may be
included as ordinary equations.

**Exact algorithm.** Starting from (s,u), take direct-sum transitions
diag(M_(i,b),N_(i,b)) for b=0,1. At each layer keep a generating matrix
for the joint reachable row module. Normalize by lifting the candidate
rows to integers, adding qI, taking a row Hermite basis, then reducing
mod q. Propagating both branches of this basis is exact by linearity,
even though the basis rows need not themselves be paths. At the end
split the generating matrix as [A B]. Solve A z = B v with the additional
constraints by modular linear algebra. This is equivalent to all path
equations since the linear functional (z,-v) must annihilate precisely
the generated module. Width d+k and h layers give polynomial bit
complexity in h,d,k,log q and the size of the additional constraints.
There is no enumeration of paths or guess of a violating clause.

The target and reader states must be propagated *jointly*. For q=2 on one
bit with r_x=x and f(x)=x, z=1 works. The two separate spans allow the
spurious pair (0,1) and would reject. Conversely, many individual shifts
can fail while the all-path shift succeeds: take the same unit reading on
every path. Thus a common shift really does avoid the single-point counting
obstruction. For a uniform independent mask U, successful z gives the
bijection U -> U+z on mask coins implementing the requested change of
the exact evaluation vector. Distributional claims about other ciphertext
components require a separate argument.

**Decision consequence.** Suppose a uniform polynomial compiler on a
CircuitSAT input samples a polynomial-size bank, including all secret
transition matrices, and runs the test for a fixed nonzero constant f.
On every satisfiable input, suppose every bank has some path with zero
row (e.g., a valid witness cancels every mask coordinate); then the
test always fails. On every unsatisfiable input, suppose the common shift
exists with probability at least an explicitly inverse-polynomial bound.
Repeating the compiler independently and declaring UNSAT on the first
successful test gives a one-sided randomized polynomial-time decider:
CircuitSAT belongs to coRP. With a deterministic always-successful bank
on NO inputs, this would put CircuitSAT in P. The decider is allowed the
compiler's private coins; keeping the transitions secret from ciphertext
recipients does not remove the implication. The stronger conclusion here
uses the explicit compact linear representation and decidability of its
global shift equations.

This distinguishes two concrete uses. Targeting a specified interval
in a sampled proof hybrid gives an efficiently checkable sufficient
mask translation. Applying a universally successful final translation
to a bank sampled by the honest compiler would decide an NP-complete
problem under the conditions above. A reduction whose programmed bank
depends on unavailable auxiliary information, a computational final
comparison, or an evaluator outside this common-order linear model
requires separate analysis. The test does not establish the public
preimage simulation or general CircuitSAT security.
