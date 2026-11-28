import Definitions.Def_LinearObservationJoin
open ObservationJoin
theorem AdvancedEncryption.WE.LinearProjection.polarity {I : Type*} (A B : I→Prop) (a b top : I→Bool)
    [DecidablePred A] [DecidablePred B] (P Q : (I→Bool)→Prop) (pa : P a) (qb : Q b)
    (lp : P a → ∀ w, (∀ i,A i→ w i=if B i then top i else a i)→P w)
    (rp : Q b → ∀ w, (∀ i,B i→ w i=if A i then top i else b i)→Q w)
    : ∃ w,P w ∧ Q w := by sorry
