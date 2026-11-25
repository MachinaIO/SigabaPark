import SigabaNeo.Trusted.Assumption

/-- Statistical hops carry the decryptor's advantage. In a hybrid chain `D 0, …, D T`, let `C` be
the set of computational hops, on each of which the machine `A` has advantage at most `ε`. If `A`
has advantage at least `1 - δ` between the ends (for example the decryptor with a witness, on a
true statement), the remaining (statistical) hops carry total advantage at least
`1 - δ - |C| ε`. This is the counting step of the SZK barrier in the note
`pq-we-hybrid-count-barrier`, and of its extension to simulation-type reductions in the note
`pq-we-gap-structure-routes`. -/
theorem AdvancedEncryption.WE.Hybrid.stat_hops_carry (D : ℕ → PMF (List Bool)) (T : ℕ)
    (C : Finset ℕ) (A : SigabaNeo.Machine) (ε δ : ℝ)
    (hdec : 1 - δ ≤ A.acceptProb (D 0) - A.acceptProb (D T))
    (hcomp : ∀ i ∈ C, |A.acceptProb (D i) - A.acceptProb (D (i + 1))| ≤ ε) :
    1 - δ - (C.card : ℝ) * ε ≤
      ∑ i ∈ (Finset.range T).filter (fun i => i ∉ C),
        |A.acceptProb (D i) - A.acceptProb (D (i + 1))| := by sorry
