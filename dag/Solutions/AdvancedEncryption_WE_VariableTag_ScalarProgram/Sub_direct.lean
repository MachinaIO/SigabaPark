import Definitions.Def_VariableLocalReplay
open VariableLocalReplay VariableTagFront
private theorem nativeTruth : ∀ (a b : Bool), nativeNand a b = !(a && b) := by decide

private theorem exactReplay (gs : List (Nat × Nat)) (xs : List Bool) (last : Bool)
    (h : Backward xs.length gs) :
    replay xs gs = some ((gs.foldl SigabaNeo.estep (xs,last)).1) := by
  induction gs generalizing xs last with
  | nil => rfl
  | cons g gs ih =>
    rcases g with ⟨a,b⟩
    obtain ⟨ha,hb,ht⟩ := h
    simp only [List.foldl_cons, SigabaNeo.estep, replay,
      List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb,
      Option.bind_some, nativeTruth, List.getD_eq_getElem?_getD,Option.getD_some]
    apply ih
    simpa using ht

private theorem rejection (gs : List (Nat × Nat)) (xs : List Bool) :
    (replay xs gs).isSome = true ↔ Backward xs.length gs := by
  induction gs generalizing xs with
  | nil => simp [replay, Backward]
  | cons g gs ih =>
    rcases g with ⟨a,b⟩
    by_cases ha : a < xs.length <;> by_cases hb : b < xs.length
    · simp [replay,Backward,ha,hb,ih]
    · simp [replay,Backward,ha,hb,List.getElem?_eq_none (by omega : xs.length ≤ b)]
    · simp [replay,Backward,ha,hb,List.getElem?_eq_none (by omega : xs.length ≤ a)]
    · simp [replay,Backward,ha,hb,List.getElem?_eq_none (by omega : xs.length ≤ a)]

private theorem seekAction (k i : Nat) (hk : k<3) (hi : i<256) (x r s t : Option Bool) :
    step (77000+256*k+i) x r s t =
      (match s with
       | none => {q:=bad,out:=some false}
       | some b => if i>0 then {q:=77000+256*k+i-1, ms:=1} else hit k b) := by
  have h₁ : (77000+256*k+i-77000)%256 = i := by omega
  have h₂ : (77000+256*k+i-77000)/256 = k := by omega
  have hh0 : ¬ (77000+256*k+i)≤1030 := by omega
  have hh1 : ¬ (77000+256*k+i)<1356 := by omega
  have hh2 : ¬ (77000+256*k+i)=1356 := by omega
  have hh3 : ¬ (77000+256*k+i)<4600 := by omega
  have hh4 : ¬ (77000+256*k+i)=4600 := by omega
  have hh5 : ¬ (77000+256*k+i)=4601 := by omega
  have hh6 : ¬ (77000+256*k+i)<10000+33788 := by omega
  have hh7 : ¬ (77000+256*k+i)<45000+16898 := by omega
  have hh8 : ¬ (77000+256*k+i)<69188 := by omega
  have hh9 : ¬ (77000+256*k+i)<69918 := by omega
  have hh10 : ¬ (77000+256*k+i)<71024 := by omega
  have hh11 : ¬ (77000+256*k+i)=71200 := by omega
  have hh12 : ¬ (77000+256*k+i)=71201 := by omega
  have hh13 : ¬ (77000+256*k+i)<71211 := by omega
  have hh14 : ¬ (77000+256*k+i)=71211 := by omega
  have hh15 : ¬ (77000+256*k+i)<71912 := by omega
  have hh16 : ¬ (77000+256*k+i)<74304 := by omega
  have hh17 : ¬ (77000+256*k+i)=74900 := by omega
  have hh18 : ¬ (77000+256*k+i)<75768 := by omega
  have hh19 : ¬ (77000+256*k+i)<76768 := by omega
  have hh20 : 77000≤(77000+256*k+i) := by omega
  have hh21 : (77000+256*k+i)<77768 := by omega
  simp only [step,left,right,hh0,hh1,hh2,hh3,hh4,hh5,hh6,hh7,hh8,hh9,hh10,hh11,hh12,hh13,hh14,hh15,hh16,hh17,hh18,hh19,hh20,hh21,decide_false,decide_true, Bool.and_false,Bool.and_true, Bool.false_and, Bool.true_and,Bool.false_or,Bool.false_eq_true,not_false_eq_true,ite_true,ite_false,beq_iff_eq, h₁,h₂]
  cases s with
  | none => rfl
  | some b =>
    by_cases hp : (0 < i) <;> by_cases hm : (k = 0) <;> cases b <;> simp [hp,hm,hit] <;> rfl

private theorem nativeSeek (k i : Nat) (hk : k<3) (hi : i<256)
    (x r t : Option Bool) (xs : List Bool) :
    scan x r t i (77000+256*k+i) xs =
      (match xs[i]? with
       | none => {q:=bad,out:=some false}
       | some b => hit k b) := by
  induction i generalizing xs with
  | zero =>
    rw [scan, seekAction k 0 hk (by omega)]
    cases xs <;> rfl
  | succ i ih =>
    cases xs with
    | nil => simp [scan,seekAction k (i+1) hk hi,List.head?,bad]
    | cons b bs =>
      simp only [scan, List.head?_cons, seekAction k (i+1) hk hi, Nat.zero_lt_succ,
        ite_true,List.tail_cons,List.getElem?_cons_succ]
      convert ih (by omega) bs using 1
      congr 1 <;> omega

private theorem activeGateLaw (xs : List Bool) (a b : Nat) (ha : a<256) (hb : b<256) :
    activeGate xs (a,b) = (do
      let u ← xs[a]?
      let v ← xs[b]?
      pure (nativeNand u v)) := by
  unfold activeGate
  have e := nativeSeek 0 a (by decide) ha none none none xs
  simp only [Nat.mul_zero,Nat.add_zero] at e
  rw [e]
  cases eu : xs[a]? with
  | none => rfl
  | some u =>
    cases u with
    | false =>
      change (if (75257:Nat)=bad then _ else _) = _
      simp only [show ¬(75257:Nat)=bad by decide,ite_false]
      change (if (scan none none none b (77000+256*1+b) xs).q=bad then none else (step (scan none none none b (77000+256*1+b) xs).q none none none none).ws.join) = _
      rw [nativeSeek 1 b (by decide) hb]
      cases xs[b]? with
      | none => rfl
      | some v => cases v <;> rfl
    | true =>
      change (if (75513:Nat)=bad then _ else _) = _
      simp only [show ¬(75513:Nat)=bad by decide,ite_false]
      change (if (scan none none none b (77000+256*2+b) xs).q=bad then none else (step (scan none none none b (77000+256*2+b) xs).q none none none none).ws.join) = _
      rw [nativeSeek 2 b (by decide) hb]
      cases xs[b]? with
      | none => rfl
      | some v => cases v <;> rfl

private theorem active_eq (gs : List (Nat × Nat)) (xs : List Bool) (h : Bytes gs) :
    activeProgram xs gs = replay xs gs := by
  induction gs generalizing xs with
  | nil => rfl
  | cons p gs ih =>
    rcases p with ⟨a,b⟩
    obtain ⟨ha,hb⟩ := h (a,b) (by simp)
    have ht : Bytes gs := fun p hp => h p (by simp [hp])
    simp only [activeProgram,activeGateLaw xs a b ha hb,replay]
    cases xs[a]? <;> cases xs[b]? <;> simp [ih _ ht]

theorem solution (gs : List (Nat × Nat)) (xs : List Bool) (last : Bool) (h : Bytes gs) :
    ((activeProgram xs gs).isSome = true ↔ Backward xs.length gs) ∧
    (Backward xs.length gs → activeProgram xs gs =
      some ((gs.foldl SigabaNeo.estep (xs,last)).1)) := by
  rw [active_eq gs xs h]
  exact ⟨rejection gs xs, exactReplay gs xs last⟩

