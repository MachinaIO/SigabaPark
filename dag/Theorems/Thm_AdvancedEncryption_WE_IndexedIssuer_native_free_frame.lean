import Definitions.Def_WE_IndexedFrame
open AdvancedEncryption.WE.IndexedFrame
/-- The free coordinates of the structured native packet give a triangular tape bijection. -/
theorem AdvancedEncryption.WE.IndexedIssuer.native_free_frame {U V W : Type*} [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    (mul : U → V → W) (l r : U) (v : V) :
    ∃ e : Tape U V W ≃ Tape U V W, ∀ q,
      e q = ⟨l+q.act,r+q.other,v+q.mask,mul l q.mask+q.left,mul r q.mask+q.right,
        q.selected,mul q.other (v+q.mask)+q.right+q.opposite⟩ := by sorry
