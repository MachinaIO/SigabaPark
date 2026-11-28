import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import SigabaNeoStd.Machines.FromPolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.Transducer

namespace ParabolaEmitter
open SigabaNeo Turing MultiTapeTM
abbrev K := ZMod 257
abbrev Row := Fin 4 → K
abbrev Mat := Fin 4 → Row
abbrev Reg := Bool × Bool × Row

inductive Op where
  | message
  | share (last : Bool)
  | digit (i : Fin 4)
  | write (row : Row) (sq : Bool) (j : Fin 9)

def digitVal (u : K) (b : Bool) : K := 2*u + if b then 1 else 0
def word (l : List Bool) : K := l.foldl digitVal 0

def form (c r : Row) (sq share : Bool) : K :=
  ∑ i, c i * (if sq then r i^2 + (if share then 1 else 0) else r i)

def upd (i : Op) (b : Bool) (q : Reg) : Reg :=
  match i with
  | .message => (b,false,0)
  | .share last =>
    let s := if last then q.1 else b
    (q.1 ^^ s,s,0)
  | .digit j => (q.1,q.2.1,Function.update q.2.2 j (digitVal (q.2.2 j) b))
  | .write .. => q

def emit (i : Op) (q : Reg) : List Bool :=
  match i with
  | .write c sq j => [(form c q.2.2 sq q.2.1).val.testBit j.val]
  | _ => []

def eval : List (Op × Bool) → Reg → List Bool
  | [],_ => []
  | (i,b)::l,q => emit i q ++ eval l (upd i b q)

abbrev Q (n : Nat) := Fin (n+1) × Reg

def reader (p : List Op) : Transducer Bool (Q p.length) where
  q₀ := (0,false,false,0)
  step q x :=
    let i := p[q.1.val]?.getD .message
    ((⟨min (q.1.val+1) p.length,by omega⟩,upd i x q.2),emit i q.2)
  final _ := []
  length_step_le q _ := by simp only; generalize p[q.1.val]?.getD Op.message = i; cases i <;> simp [emit]
  length_final_le _ := by simp

theorem suffix (p pre : List Op) (l : List (Op × Bool)) (hp : p = pre ++ l.map Prod.fst)
    (i : Fin (p.length+1)) (hi : i.val = pre.length) (s : Reg) :
    (reader p).run (i,s) (l.map Prod.snd) = eval l s := by
  induction l generalizing pre i s with
  | nil => rfl
  | cons h l ih =>
    obtain ⟨o,x⟩ := h
    have hget : p[i.val]? = some o := by simp [hp,hi]
    have hlt : pre.length < p.length := by simp [hp]
    simp only [List.map_cons,Transducer.run_cons,reader,hget,Option.getD_some,eval]
    congr 1
    apply ih (pre ++ [o])
    · simpa [List.append_assoc] using hp
    · simp [hi,Nat.min_eq_left (by omega : pre.length+1 ≤ p.length)]

noncomputable def machine (p : List Op) : Machine := Machine.ofTM (reader p).toTM (2*p.length+3)

theorem machine_run (p : List Op) (l : List (Op × Bool)) (hp : p = l.map Prod.fst) :
    (machine p).run (l.map Prod.snd) = PMF.pure (eval l (false,false,0)) := by
  rw [machine,Machine.run_ofTM]
  congr 1
  let w := l.map Prod.snd
  have hl : w.length = p.length := by simp [w,hp]
  obtain ⟨⟨u,hu,hout⟩,htime,_⟩ := (reader p).computesInTimeAndSpace_toTM w
  have hh := runsInTime_iff_halted.mp htime
  rw [show 2*p.length+3 = 2*w.length+3 by omega]
  have hr : ((reader p).toTM.runFrom ((reader p).toTM.initCfg w) (2*w.length+3)).output =
      (reader p).run (reader p).q₀ w := by
    rcases le_total u (2*w.length+3) with le|le
    · rw [runFrom_eq_of_halt _ _ le hu]; exact hout
    · rw [← runFrom_eq_of_halt _ _ le hh]; exact hout
  exact hr.trans (suffix p [] l (by simpa using hp) 0 rfl _)

def statesFor (n : Nat) := (n+1)*(4*257^4)*6

theorem machine_cost (p : List Op) : (machine p).cost =
    2*p.length+3 + 6*statesFor p.length*(4+Nat.size (statesFor p.length)) := by
  have hb : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
  have ho : Nat.card (Option Bool) = 3 := by simp [Nat.card_eq_fintype_card,Fintype.card_option]
  have hs : (machine p).states = statesFor p.length := by
    change Nat.card (Q p.length × Option Bool × Bool) = _
    simp only [Q,Reg,Row,K,Nat.card_prod,Nat.card_fun,Nat.card_zmod,Nat.card_fin,
      hb,ho,statesFor]
    ring
  have ht : (machine p).time = 2*p.length+3 := rfl
  have hk : (machine p).tapes = 0 := rfl
  rw [Machine.cost,ht,Machine.descLen,Machine.entryBits,hs,hk]
  simp only [pow_zero,mul_one,mul_zero,add_zero,show Nat.size 0 = 0 by decide]

def digits (i : Fin 4) (bs : List Bool) := bs.map (fun b ↦ (Op.digit i,b))

theorem eval_digits (i : Fin 4) (bs : List Bool) (l : List (Op × Bool)) (rem share : Bool) (r : Row) :
    eval (digits i bs ++ l) (rem,share,r) =
    eval l (rem,share,Function.update r i (bs.foldl digitVal (r i))) := by
  induction bs generalizing r with
  | nil => simp [digits]
  | cons b bs ih =>
    simp only [digits,List.map_cons,List.cons_append,eval,emit,List.nil_append,upd,List.foldl_cons]
    rw [show List.map (fun b ↦ (Op.digit i,b)) bs = digits i bs from rfl,ih]
    simp

def outs (m : Mat) : List (Row × Bool × Fin 9) :=
  (List.finRange 4).flatMap fun i ↦ [false,true].flatMap fun sq ↦
    (List.finRange 9).map (fun j ↦ (m i,sq,j))

def writes (m : Mat) := (outs m).map (fun z ↦ (Op.write z.1 z.2.1 z.2.2,false))

def columnBits (m : Mat) (r : Row) (s : Bool) :=
  (outs m).map fun z ↦ (form z.1 r z.2.1 s).val.testBit z.2.2.val

theorem eval_writes (m : Mat) (l : List (Op × Bool)) (rem s : Bool) (r : Row) :
    eval (writes m ++ l) (rem,s,r) = columnBits m r s ++ eval l (rem,s,r) := by
  unfold writes columnBits
  induction outs m with
  | nil => rfl
  | cons z zs ih =>
    simp only [List.map_cons,List.cons_append,eval,emit,upd,List.singleton_append]
    rw [ih]; rfl

def lane (m : Mat) (last split : Bool) (bs : Fin 4 → List Bool) :=
  (Op.share last,split) :: (digits 0 (bs 0) ++ (digits 1 (bs 1) ++
    (digits 2 (bs 2) ++ (digits 3 (bs 3) ++ writes m))))

theorem eval_lane (m : Mat) (last split : Bool) (bs : Fin 4 → List Bool)
    (l : List (Op × Bool)) (q : Reg) :
    let s := if last then q.1 else split
    eval (lane m last split bs ++ l) q = columnBits m (fun i ↦ word (bs i)) s ++
      eval l (q.1 ^^ s,s,fun i ↦ word (bs i)) := by
  simp only [lane,List.cons_append,eval,emit,List.nil_append,upd,List.append_assoc,eval_digits,
    eval_writes]
  have he : Function.update (Function.update (Function.update (Function.update (0 : Row) 0
      (word (bs 0))) 1 (word (bs 1))) 2 (word (bs 2))) 3 (word (bs 3)) =
      fun i ↦ word (bs i) := by funext i; fin_cases i <;> simp [Function.update]
  simp [word] at he ⊢
  rw [he]

theorem outs_length (m : Mat) : (outs m).length = 72 := by simp [outs,List.length_flatMap]
theorem lane_length (m : Mat) (last split : Bool) (bs : Fin 4 → List Bool)
    (hb : ∀ i, (bs i).length = 160) : (lane m last split bs).length = 713 := by
  simp [lane,digits,writes,outs_length,hb]

theorem fixed_cost {p : List Op} (hp : p.length = 1+4096*129*713) :
    (machine p).cost < 2^76 := by rw [machine_cost,hp]; decide

theorem residue_length : 2^160 % 257 = 1 := by decide
theorem line_budget : (((257:ℚ)^2+1)/(2*257^2))^129 + (2*2113536)/(2:ℚ)^160 < 1/(2:ℚ)^128 := by
  norm_num


/-- The complete deterministic opcode sequence depends only on the public matrices. -/
def code (ms : List Mat) : List Op :=
  match ms with
  | [] => []
  | m::rest => (lane m rest.isEmpty false (fun _ ↦ List.replicate 160 false)).map Prod.fst ++ code rest

def input (ms : List Mat) (j : Nat) (bs : Nat → Fin 4 → List Bool) (coins : Nat → Bool) :=
  match ms with
  | [] => ([] : List (Op × Bool))
  | m::rest => lane m rest.isEmpty (coins j) (bs j) ++ input rest (j+1) bs coins

def columns (ms : List Mat) (j : Nat) (b : Bool) (bs : Nat → Fin 4 → List Bool)
    (coins : Nat → Bool) : List Bool :=
  match ms with
  | [] => []
  | m::rest =>
    let share := if rest.isEmpty then b else coins j
    columnBits m (fun i ↦ word (bs j i)) share ++ columns rest (j+1) (b ^^ share) bs coins

theorem digits_code (i : Fin 4) (bs : List Bool) :
    (digits i bs).map Prod.fst = List.replicate bs.length (Op.digit i) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    change Op.digit i :: (digits i bs).map Prod.fst = _
    rw [ih]; rfl

theorem lane_code (m : Mat) (last split : Bool) (bs : Fin 4 → List Bool)
    (hb : ∀ i, (bs i).length = 160) :
    (lane m last split bs).map Prod.fst =
    (lane m last false (fun _ ↦ List.replicate 160 false)).map Prod.fst := by
  simp only [lane,List.map_cons,List.map_append,digits_code,hb,List.length_replicate]

theorem public_code (ms : List Mat) (j : Nat) (bs : Nat → Fin 4 → List Bool) (coins : Nat → Bool)
    (hb : ∀ j i, (bs j i).length = 160) : (input ms j bs coins).map Prod.fst = code ms := by
  induction ms generalizing j with
  | nil => rfl
  | cons m ms ih => simp only [input,code,List.map_append,lane_code _ _ _ _ (hb j),ih]

theorem all_bits (ms : List Mat) (j : Nat) (q : Reg) (bs : Nat → Fin 4 → List Bool)
    (coins : Nat → Bool) : eval (input ms j bs coins) q = columns ms j q.1 bs coins := by
  induction ms generalizing j q with
  | nil => rfl
  | cons m ms ih => simp only [input,columns,eval_lane,ih]

theorem public_run (ms : List Mat) (b : Bool) (bs : Nat → Fin 4 → List Bool)
    (coins : Nat → Bool) (hb : ∀ j i, (bs j i).length = 160) :
    (machine (.message :: code ms)).run (b :: (input ms 0 bs coins).map Prod.snd) =
    PMF.pure (columns ms 0 b bs coins) := by
  have h := machine_run (.message :: code ms) ((Op.message,b)::input ms 0 bs coins)
    (by simp [public_code _ _ _ _ hb])
  simpa [eval,emit,upd,all_bits] using h

theorem code_size (ms : List Mat) : (code ms).length = ms.length*713 := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    have hl := lane_length m ms.isEmpty false (fun _ ↦ List.replicate 160 false)
      (fun _ ↦ List.length_replicate)
    simp only [code,List.length_append,List.length_map,hl,ih,List.length_cons,Nat.add_mul,one_mul]
    omega

theorem full_static_cost (ms : List Mat) (h : ms.length = 4096*129) :
    (machine (.message :: code ms)).cost = 16566555350652150247109 := by
  rw [machine_cost,List.length_cons,code_size,h]; decide

theorem cycles (p m a : Nat) (ha : a < p) :
    ∑ i ∈ Finset.range (m*p), (if i%p=a then 1 else 0 : Nat) = m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul,Finset.sum_range_add,ih]
    have hz : ∑ i ∈ Finset.range p, (if (m*p+i)%p=a then 1 else 0 : Nat) = 1 := by
      apply Eq.trans (Finset.sum_congr rfl (g := fun i ↦ if i=a then 1 else 0) ?_) ?_
      · intro i hi
        simp [Nat.add_mod,Nat.mod_eq_of_lt (Finset.mem_range.mp hi)]
      · simp [ha]
    rw [hz]

theorem residue_counts (a : Fin 257) :
    ∑ i ∈ Finset.range (2^160), (if i%257=a.val then 1 else 0 : Nat) =
      (2^160-1)/257 + (if a.val=0 then 1 else 0) := by
  let m := (2^160-1)/257
  have he : 2^160 = m*257+1 := by decide +revert
  rw [he,Finset.sum_range_succ,cycles _ _ _ a.isLt]
  simp only [Nat.mul_mod_left]
  change m + (if 0 = a.val then 1 else 0) = _ + _
  rw [← he]
  simp [m,eq_comm]

end ParabolaEmitter
