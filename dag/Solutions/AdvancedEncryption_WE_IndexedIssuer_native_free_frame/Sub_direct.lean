import Definitions.Def_WE_IndexedFrame
open AdvancedEncryption.WE.IndexedFrame
/-- The free coordinates of the structured native packet give a triangular tape bijection. -/
theorem solution {U V W : Type*} [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    (mul : U → V → W) (l r : U) (v : V) :
    ∃ e : Tape U V W ≃ Tape U V W, ∀ q,
      e q = ⟨l+q.act,r+q.other,v+q.mask,mul l q.mask+q.left,mul r q.mask+q.right,
        q.selected,mul q.other (v+q.mask)+q.right+q.opposite⟩ := by
  let f (q : Tape U V W) : Tape U V W :=
    ⟨l+q.act,r+q.other,v+q.mask,mul l q.mask+q.left,mul r q.mask+q.right,
        q.selected,mul q.other (v+q.mask)+q.right+q.opposite⟩
  let g (z : Tape U V W) : Tape U V W :=
    let m := z.mask-v
    let b := z.other-r
    let k := z.right-mul r m
    ⟨z.act-l,b,m,z.left-mul l m,k,z.selected,z.opposite-k-mul b z.mask⟩
  refine ⟨⟨f,g,?_,?_⟩,fun _ => rfl⟩
  · intro q
    cases q
    simp [f,g,add_comm,add_left_comm,add_assoc]
  · intro z
    cases z
    simp [f,g,add_comm,add_left_comm,add_assoc,sub_eq_add_neg] <;> abel
