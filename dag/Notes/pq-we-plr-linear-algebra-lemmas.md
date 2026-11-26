---
title: The linear-algebra lemmas of the PLR-hop analysis (rank factorization, sibling identity, ERASE unused rows), proved
refs: [note:pq-we-split-lemma-attempts, note:pq-we-masked-overcomplete-leaf, theorem:AdvancedEncryption.WE.PLR.rank_factor_le, theorem:AdvancedEncryption.WE.PLR.rank_factor_eq_iff, theorem:AdvancedEncryption.WE.PLR.sibling_identity, theorem:AdvancedEncryption.WE.PLR.erase_unused_rows]
tags: [witness-encryption, ggh15, lemma]
---
The note `pq-we-plr-hop-rank-and-erase` (open PR #56, not yet merged, so it is not referenced
formally here) lists in its §6 three pure linear-algebra facts used by its informal arguments.
This PR states them in general form and proves them completely. They do not depend on the GGH15
vocabulary of PR #57.

1. **Rank factorization** (§1 of that note: `V'[x,u] = y_{xu} − y_{xu0} = [X_x | e_x]·ΔY`).
   * `rank_factor_le`: `rank ([X | E]·ΔY) ≤ rank [X | E] ≤ rank X + m`, with no hypotheses.
   * `rank_factor_eq_iff`: if `ΔY` has full row rank, then `rank ([X | E]·ΔY) = rank X + m` holds
     **iff** `rank E = m` and the column spaces of `X` and `E` intersect trivially. So the
     informal claim `rank V' = m + rank{X_x}` needs exactly three things: a full-row-rank
     `ΔY` (which needs `|U| ≥ dim X + m`), an error block of full column rank, and no column of
     the error block (or combination of columns) lying in the column space of `X`. For random
     Gaussian errors and `|S| ≥ rank X + m` this is the expected generic case, but it is a
     hypothesis, not a consequence; the rank obstruction is only as strong as this genericity.
2. **Sibling identity** (`sibling_identity`): if `y_{xc} = y_x·D_c` and `det D_{b'}` is a unit,
   then `y_{xb} = y_{xb'}·D_{b'}⁻¹·D_b`, and the whole subtree below `xb` is a public linear image
   of `y_{xb'}`: `y_{xbz} = y_{xb'}·D_{b'}⁻¹·D_b·D_{z_1}⋯D_{z_r}`.
3. **Unused hidden rows** (`erase_unused_rows`, step 5 of the ERASE lemma): over a finite field,
   if a uniform `k × n` matrix `U` is published only through `C·U + W` with `C` of full row rank
   (`|ι|` independent combinations of the `k` hidden rows), then each value of `C·U` has exactly
   `|K|^((k − |ι|)n)` preimages, so `C·U + W` is uniform and its law does not depend on `W`
   (stated as an identity of sums of an arbitrary test function). The eq-chain pad
   `c·U^{eq,k}` with `c ≠ 0` is the case `|ι| = 1`. What remains for the ERASE lemma is to check
   that in the hybrid, after steps 1-4, `U^{eq,k}` really is used only through such
   independent combinations (no other published product touches it); this lemma is the
   statistical step once that bookkeeping holds.
