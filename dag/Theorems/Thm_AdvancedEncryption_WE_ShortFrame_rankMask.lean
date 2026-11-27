import Definitions.Def_ShortNand

open SigabaNeo ShortNand

theorem AdvancedEncryption.WE.ShortFrame.rankMask {K V W I : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (L : I→V) (d : V) (h : V→ₗ[K] K)
    (hz : ∀i,h (L i)=0) (hd : h d=1) (e e' : W) :
    ∃ f : (V→ₗ[K] W) ≃ (V→ₗ[K] W), ∀ M,
      (∀i,f M (L i)=M (L i)) ∧ f M d+e'=M d+e := by sorry
