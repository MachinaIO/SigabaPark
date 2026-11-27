import Definitions.Def_OrderedNand

open OrderedNand

theorem solution (v : Nat → Bool) (h0 : v 0 = true) (d l r : Nat) (y : Key) :
    (∃ p q, row d l r p q y ∧ live v p ∧ live v q) ↔ y = .wire d (!(v l && v r)) := by
  by_cases he : l = r
  · subst r
    constructor
    · rintro ⟨p,q,h,_,hq⟩
      simp only [row,if_pos rfl] at h
      obtain ⟨b,_,_,rfl,hy⟩ := h
      change v l = b at hq
      simpa [hq] using hy
    · intro hy
      refine ⟨.dummy, .wire l (v l), ?_, trivial, rfl⟩
      simp only [row,if_pos rfl]
      refine ⟨v l, ?_,trivial,rfl,?_⟩
      · intro hl
        simpa [hl] using h0
      · simpa using hy
  · constructor
    · rintro ⟨p,q,h,hp,hq⟩
      simp only [row,if_neg he] at h
      obtain ⟨a,b,_,_,rfl,rfl,hy⟩ := h
      change v l = a at hp
      change v r = b at hq
      simpa [hp,hq] using hy
    · intro hy
      refine ⟨.wire l (v l),.wire r (v r), ?_,rfl,rfl⟩
      simp only [row,if_neg he]
      refine ⟨v l,v r,?_,?_,rfl,rfl,hy⟩
      · intro hl; simpa [hl] using h0
      · intro hr; simpa [hr] using h0
