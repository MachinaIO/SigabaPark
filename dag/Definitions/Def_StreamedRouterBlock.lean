import SigabaNeo.Trusted.Machine

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace StreamedRouterBlock
open SigabaNeo

/-- Run lengths of the deterministic 2-round schedule. Low six ternary digits encode
four row heads, scratch, and input. The quotient selects a Boolean action below. -/
def runs : Array (Nat × Nat) := #[
(1,81), (9,810), (1,81), (1,1539), (1,2188), (1,2917), (1,2188), (2,2917),
(2,2188), (4,2917), (4,2188), (5,2917), (3,2188), (1,2917), (1,2188), (4,2917),
(2,2188), (2,2917), (3,2188), (1,2917), (2,2188), (3,2917), (1,2188), (2,2917),
(2,2188), (6,2917), (1,2188), (2,2917), (2,2188), (2,2917), (2,2188), (3,2917),
(1,2188), (2,2917), (2,2188), (2,2917), (1,2188), (1,2917), (2,2188), (1,2917),
(1,2188), (3,2917), (1,2188), (3,2917), (2,2188), (1,2917), (1,2188), (2,2917),
(4,2188), (3,2917), (1,2188), (1,2917), (3,2188), (1,2917), (1,2188), (1,2917),
(1,2188), (2,2917), (2,2188), (6,2917), (1,2188), (2,2917), (2,2188), (1,2917),
(1,2188), (1,2917), (2,2188), (1,2917), (128,3891), (128,4626), (128,5130), (128,2024),
(128,1944), (1,5944), (31,6673), (1,1682), (16,1520), (15,1466), (16,7506), (32,1485),
(16,7506), (1,1593), (14,1512), (1,8139), (31,8868), (1,1698), (20,1536), (11,1530),
(12,9645), (32,1461), (20,9645), (1,1545), (10,1464), (1,5944), (31,6673), (1,1682),
(24,1520), (7,1466), (8,7506), (32,1485), (24,7506), (1,1593), (6,1512), (1,8139),
(31,8868), (1,1698), (25,1536), (6,1530), (7,9645), (32,1461), (25,9645), (1,1545),
(5,1464), (32,1498), (1,5944), (31,6673), (1,1682), (16,1520), (15,1466), (16,7506),
(32,1485), (16,7506), (1,1593), (14,1512), (1,8139), (31,8868), (1,1698), (20,1536),
(11,1530), (12,9645), (32,1461), (20,9645), (1,1545), (10,1464), (1,5944), (31,6673),
(1,1682), (24,1520), (7,1466), (8,7506), (32,1485), (24,7506), (1,1593), (6,1512),
(1,8139), (31,8868), (1,1698), (25,1536), (6,1530), (7,9645), (32,1461), (25,9645),
(1,1545), (5,1464), (32,1498), (1,5944), (31,6673), (1,1682), (16,1520), (15,1466),
(16,7506), (32,1485), (16,7506), (1,1593), (14,1512), (1,8139), (31,8868), (1,1698),
(20,1536), (11,1530), (12,9645), (32,1461), (20,9645), (1,1545), (10,1464), (1,5944),
(31,6673), (1,1682), (24,1520), (7,1466), (8,7506), (32,1485), (24,7506), (1,1593),
(6,1512), (1,8139), (31,8868), (1,1698), (25,1536), (6,1530), (7,9645), (32,1461),
(25,9645), (1,1545), (5,1464), (32,1498), (1,5944), (31,6673), (1,1682), (16,1520),
(15,1466), (16,7506), (32,1485), (16,7506), (1,1593), (14,1512), (1,8139), (31,8868),
(1,1698), (20,1536), (11,1530), (12,9645), (32,1461), (20,9645), (1,1545), (10,1464),
(1,5944), (31,6673), (1,1682), (24,1520), (7,1466), (8,7506), (32,1485), (24,7506),
(1,1593), (6,1512), (1,8139), (31,8868), (1,1698), (25,1536), (6,1530), (7,9645),
(32,1461), (25,9645), (1,1545), (5,1464), (32,1484), (32,1466), (32,1460), (1,5944),
(31,6673), (1,1682), (16,1520), (15,1466), (16,7506), (32,1485), (16,7506), (1,1593),
(14,1512), (1,8139), (31,8868), (1,1698), (20,1536), (11,1530), (12,9645), (32,1461),
(20,9645), (1,1545), (10,1464), (1,5944), (31,6673), (1,1682), (24,1520), (7,1466),
(8,7506), (32,1485), (24,7506), (1,1593), (6,1512), (1,8139), (31,8868), (1,1698),
(25,1536), (6,1530), (7,9645), (32,1461), (25,9645), (1,1545), (5,1464), (32,1525),
(64,1512), (1,5944), (31,6673), (1,1682), (16,1520), (15,1466), (16,7506), (32,1485),
(16,7506), (1,1593), (14,1512), (1,8139), (31,8868), (1,1698), (20,1536), (11,1530),
(12,9645), (32,1461), (20,9645), (1,1545), (10,1464), (1,5944), (31,6673), (1,1682),
(24,1520), (7,1466), (8,7506), (32,1485), (24,7506), (1,1593), (6,1512), (1,8139),
(31,8868), (1,1698), (25,1536), (6,1530), (7,9645), (32,1461), (25,9645), (1,1545),
(5,1464), (32,1507), (64,1476), (1,5944), (31,6673), (1,1682), (16,1520), (15,1466),
(16,7506), (32,1485), (16,7506), (1,1593), (14,1512), (1,8139), (31,8868), (1,1698),
(20,1536), (11,1530), (12,9645), (32,1461), (20,9645), (1,1545), (10,1464), (1,5944),
(31,6673), (1,1682), (24,1520), (7,1466), (8,7506), (32,1485), (24,7506), (1,1593),
(6,1512), (1,8139), (31,8868), (1,1698), (25,1536), (6,1530), (7,9645), (32,1461),
(25,9645), (1,1545), (5,1464), (32,1501), (64,1464), (1,5944), (31,6673), (1,1682),
(16,1520), (15,1466), (16,7506), (32,1485), (16,7506), (1,1593), (14,1512), (1,8139),
(31,8868), (1,1698), (20,1536), (11,1530), (12,9645), (32,1461), (20,9645), (1,1545),
(10,1464), (1,5944), (31,6673), (1,1682), (24,1520), (7,1466), (8,7506), (32,1485),
(24,7506), (1,1593), (6,1512), (1,8139), (31,8868), (1,1698), (25,1536), (6,1530),
(7,9645), (32,1461), (25,9645), (1,1545), (5,1464), (3,1694), (29,1532), (32,1514),
(32,1460), (1,10206), (1,10935), (1,11745), (1,12393), (1,1539), (1,13123), (1,13852),
(1,14581), (2,13852), (2,14581), (4,13852), (4,14581), (5,13852), (3,14581), (1,13852),
(1,14581), (4,13852), (2,14581), (1,13852), (1,15310), (3,14581), (1,13852), (2,14581),
(3,13852), (1,14581), (2,13852), (2,14581), (6,13852), (1,14581), (2,13852), (2,14581),
(2,13852), (2,14581), (2,13852), (1,15310), (1,14581), (2,13852), (2,14581), (2,13852),
(1,14581), (1,13852), (2,14581), (1,13852), (1,14581), (3,13852), (1,14581), (3,13852),
(2,14581), (1,13852), (1,14581), (2,13852), (4,14581), (1,13852), (1,15310), (1,13852),
(1,14581), (1,13852), (3,14581), (1,13852), (1,14581), (1,13852), (1,14581), (2,13852),
(2,14581), (6,13852), (1,14581), (2,13852), (2,14581), (1,13852), (1,14581), (1,13852),
(2,14581), (1,13852), (1,16284), (31,17013), (1,16284), (31,17013), (1,16284), (31,17013),
(1,16284), (31,17013), (1,17748), (31,18477), (1,17748), (31,18477), (1,17748), (31,18477),
(1,17748), (31,18477), (1,18981), (31,19710), (1,18981), (31,19710), (1,18981), (31,19710),
(1,18981), (31,19710), (12,1700), (116,1538)]

def code : Array Nat := runs.foldl (fun a r => a ++ Array.replicate r.1 r.2) #[]
def dir (n : Nat) : SignType := if n=1 then 1 else if n=2 then -1 else 0
def bitSum (x y carry : Bool) := (x.toNat + y.toNat + carry.toNat)
structure Local where
  wr : Fin 5 → Option (Option Bool) := fun _ => none
  out : Option Bool := none
  carry : Bool := false
  jump : Option Nat := none
  scratchMove : Option SignType := none
def update (i : Nat) (b : Option Bool) (h : Fin 5) : Option (Option Bool) :=
  if h.val=i then some b else none
def action (op : Nat) (rd : Nat → Option Bool) (carry : Bool) : Local :=
  match op with
  | 0 => { wr := update 4 none }
  | 1 => { wr := update 4 (some true) }
  | 2 => {}
  | 3 => { wr := update 0 (some true) }
  | 4 => { wr := update 0 (some false) }
  | 5 => { wr := update 1 (rd 5) }
  | 6 => { wr := update 2 (rd 5) }
  | 7 => { wr := update 3 (some false) }
  | 8 => 
    let b := bitSum ((rd 0).getD false) ((rd 1).getD false) false
    let l := b % 2 == 1
    { carry := b ≥ 2, wr := fun h => if h.val=0 then some (some l) else update 4 (some (xor ((rd 3).getD false) l)) h }
  | 9 => 
    let b := bitSum ((rd 0).getD false) ((rd 1).getD false) carry
    let l := b % 2 == 1
    { carry := b ≥ 2, wr := fun h => if h.val=0 then some (some l) else update 4 (some (xor ((rd 3).getD false) l)) h }
  | 10 => { wr := update 3 (rd 4) }
  | 11 => 
    let b := bitSum ((rd 2).getD false) ((rd 3).getD false) false
    let l := b % 2 == 1
    { carry := b ≥ 2, wr := fun h => if h.val=2 then some (some l) else update 4 (some (xor ((rd 1).getD false) l)) h }
  | 12 => 
    let b := bitSum ((rd 2).getD false) ((rd 3).getD false) carry
    let l := b % 2 == 1
    { carry := b ≥ 2, wr := fun h => if h.val=2 then some (some l) else update 4 (some (xor ((rd 1).getD false) l)) h }
  | 13 => { wr := update 1 (rd 4) }
  | 14 => 
    match rd 4 with
    | some false => { jump := some 5764, scratchMove := some (-1) }
    | some true => { wr := update 4 (some false), jump := some 5765, scratchMove := some 1 }
    | none => { jump := some 5767, scratchMove := some 1 }
  | 15 => { jump := some (if rd 4 = some false then 5765 else 5766), scratchMove := some 1 }
  | 16 => { jump := some 780 }
  | 17 => { jump := some (if rd 4 = some false then 5767 else 5768), scratchMove := some 1 }
  | 18 => 
    let b := bitSum ((rd 0).getD false) true false
    let l := b % 2 == 1
    { carry := b ≥ 2, out := some l }
  | 19 => 
    let b := bitSum ((rd 0).getD false) false carry
    let l := b % 2 == 1
    { carry := b ≥ 2, out := some l }
  | 20 => 
    let b := bitSum ((rd 0).getD false) true carry
    let l := b % 2 == 1
    { carry := b ≥ 2, out := some l }
  | 21 => 
    let b := bitSum ((rd 0).getD false) false false
    let l := b % 2 == 1
    { carry := b ≥ 2, out := some l }
  | 22 => 
    let b := bitSum ((rd 1).getD false) ((rd 5).getD false) false
    let l := b % 2 == 1
    { carry := b ≥ 2, out := some l }
  | 23 => 
    let b := bitSum ((rd 1).getD false) ((rd 5).getD false) carry
    let l := b % 2 == 1
    { carry := b ≥ 2, out := some l }
  | 24 => 
    let b := bitSum ((rd 2).getD false) ((rd 5).getD false) false
    let l := b % 2 == 1
    { carry := b ≥ 2, out := some l }
  | 25 => 
    let b := bitSum ((rd 2).getD false) ((rd 5).getD false) carry
    let l := b % 2 == 1
    { carry := b ≥ 2, out := some l }
  | 26 => 
    let b := bitSum ((rd 3).getD false) false false
    let l := b % 2 == 1
    { carry := b ≥ 2, out := some l }
  | 27 => 
    let b := bitSum ((rd 3).getD false) false carry
    let l := b % 2 == 1
    { carry := b ≥ 2, out := some l }

  | _ => {}
def needsCarry (op : Nat) : Bool := op == 9 || op == 12 || op == 19 || op == 20 || op == 23 || op == 25 || op == 27

/-- Only carry-consuming program counters need a second control state. -/
def carryPC : Array Nat := (Array.range 6409).filter fun i => needsCarry ((code[i]?.getD 0)/729)
def machine : Machine where
  tapes := 5
  states := 7898
  time := 51380
  machine := {
    initial := 0
    tr := fun st input ws _ _ =>
      let high := st.val ≥ 6409
      let pc := if high then carryPC[st.val-6409]?.getD 6409 else st.val
      let op := code[pc]?.getD 0
      let rd := fun j : Nat => if h : j < 5 then ws ⟨j,h⟩ else input
      let a := action (op / 729) rd high
      let mv := fun j : Nat => dir ((op / 3^j) % 3)
      let next := a.jump.getD (pc+1)
      let dest := if a.carry && needsCarry ((code[next]?.getD 0)/729) then 6409+carryPC.toList.idxOf next else next
      .step { inputTape := mv 5
              workTapes := fun i => (a.wr i, if i.val=4 then a.scratchMove.getD (mv i.val) else mv i.val)
              output := a.out
              state := if next ≥ 6409 then none else if h : dest < 7898 then some ⟨dest,h⟩ else none }
            (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) }
end StreamedRouterBlock

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace SharedQuarterBlock
open SigabaNeo

/-- Run lengths of the deterministic 2-round schedule. Low six ternary digits encode
four row heads, scratch, and input. The quotient selects a Boolean action below. -/
def runs : Array (Nat × Nat) := #[
(1,81), (9,810), (1,81), (1,1539), (1,2188), (1,2917), (1,2188), (2,2917),
(2,2188), (4,2917), (4,2188), (5,2917), (3,2188), (1,2917), (1,2188), (4,2917),
(2,2188), (2,2917), (3,2188), (1,2917), (2,2188), (3,2917), (1,2188), (2,2917),
(2,2188), (6,2917), (1,2188), (2,2917), (2,2188), (2,2917), (2,2188), (3,2917),
(1,2188), (2,2917), (2,2188), (2,2917), (1,2188), (1,2917), (2,2188), (1,2917),
(1,2188), (3,2917), (1,2188), (3,2917), (2,2188), (1,2917), (1,2188), (2,2917),
(4,2188), (3,2917), (1,2188), (1,2917), (3,2188), (1,2917), (1,2188), (1,2917),
(1,2188), (2,2917), (2,2188), (6,2917), (1,2188), (2,2917), (2,2188), (1,2917),
(1,2188), (1,2917), (2,2188), (1,2917), (128,3891), (128,4626), (128,5130), (128,2024),
(128,1944), (2,5913), (1,6642), (32,1498), (1,810), (1,5913), (1,6642), (32,1498),
(1,5913), (1,810), (1,6642), (32,1498), (2,810), (1,6642), (32,1484), (32,1466),
(32,1460), (2,5913), (1,7371), (32,1525), (64,1512), (1,810), (1,5913), (1,7371),
(32,1507), (64,1476), (1,5913), (1,810), (1,7371), (32,1501), (64,1464), (2,810),
(1,7371), (3,1694), (29,1532), (32,1514), (32,1460), (1,8019), (1,8748), (1,9558),
(1,10206), (1,1539), (1,10936), (1,11665), (1,12394), (2,11665), (2,12394), (4,11665),
(4,12394), (5,11665), (3,12394), (1,11665), (1,12394), (4,11665), (2,12394), (1,11665),
(1,13123), (3,12394), (1,11665), (2,12394), (3,11665), (1,12394), (2,11665), (2,12394),
(6,11665), (1,12394), (2,11665), (2,12394), (2,11665), (2,12394), (2,11665), (1,13123),
(1,12394), (2,11665), (2,12394), (2,11665), (1,12394), (1,11665), (2,12394), (1,11665),
(1,12394), (3,11665), (1,12394), (3,11665), (2,12394), (1,11665), (1,12394), (2,11665),
(4,12394), (1,11665), (1,13123), (1,11665), (1,12394), (1,11665), (3,12394), (1,11665),
(1,12394), (1,11665), (1,12394), (2,11665), (2,12394), (6,11665), (1,12394), (2,11665),
(2,12394), (1,11665), (1,12394), (1,11665), (2,12394), (1,11665), (1,14097), (31,14826),
(1,14097), (31,14826), (1,14097), (31,14826), (1,14097), (31,14826), (1,15561), (31,16290),
(1,15561), (31,16290), (1,15561), (31,16290), (1,15561), (31,16290), (1,16794), (31,17523),
(1,16794), (31,17523), (1,16794), (31,17523), (1,16794), (31,17523), (12,1700), (116,1538),
(1,18225), (1,19066), (31,19795), (1,1682), (16,1520), (15,1466), (16,20628), (32,1485),
(16,20628), (1,1593), (14,1512), (1,21261), (31,21990), (1,1698), (20,1536), (11,1530),
(12,22767), (32,1461), (20,22767), (1,1545), (10,1464), (1,19066), (31,19795), (1,1682),
(24,1520), (7,1466), (8,20628), (32,1485), (24,20628), (1,1593), (6,1512), (1,21261),
(31,21990), (1,1698), (25,1536), (6,1530), (7,22767), (32,1461), (25,22767), (1,1545),
(5,1464), (1,1620), (1,23490), (1,24219), (1,24948), (1,25515), (1,26244), (1,26973),
(1,27702)]

def code : Array Nat := runs.foldl (fun a r => a ++ Array.replicate r.1 r.2) #[]
def dir (n : Nat) : SignType := if n=1 then 1 else if n=2 then -1 else 0
def bitSum (x y carry : Bool) := (x.toNat + y.toNat + carry.toNat)
structure Local where
  wr : Fin 5 → Option (Option Bool) := fun _ => none
  out : Option Bool := none
  carry : Bool := false
  jump : Option Nat := none
  scratchMove : Option SignType := none
def update (i : Nat) (b : Option Bool) (h : Fin 5) : Option (Option Bool) :=
  if h.val=i then some b else none
def action (op : Nat) (rd : Nat → Option Bool) (carry : Bool) : Local :=
  match op with
  | 0 => { wr := update 4 none }
  | 1 => { wr := update 4 (some true) }
  | 2 => {}
  | 3 => { wr := update 0 (some true) }
  | 4 => { wr := update 0 (some false) }
  | 5 => { wr := update 1 (rd 5) }
  | 6 => { wr := update 2 (rd 5) }
  | 7 => { wr := update 3 (some false) }
  | 8 => { wr := update 4 (some false) }
  | 9 => { wr := update 4 (some false), jump := some 2026 }
  | 10 => { wr := update 4 (some true), jump := some 2026 }
  | 11 => 
    match rd 4 with
    | some false => { jump := some 1380, scratchMove := some (-1) }
    | some true => { wr := update 4 (some false), jump := some 1381, scratchMove := some 1 }
    | none => { jump := some 1383, scratchMove := some 1 }
  | 12 => { jump := some (if rd 4 = some false then 1381 else 1382), scratchMove := some 1 }
  | 13 => { jump := some 780 }
  | 14 => { jump := some (if rd 4 = some false then 1383 else 1384), scratchMove := some 1 }
  | 15 => 
    let b := bitSum ((rd 0).getD false) true false
    let l := b % 2 == 1
    { carry := b ≥ 2, out := some l }
  | 16 => 
    let b := bitSum ((rd 0).getD false) false carry
    let l := b % 2 == 1
    { carry := b ≥ 2, out := some l }
  | 17 => 
    let b := bitSum ((rd 0).getD false) true carry
    let l := b % 2 == 1
    { carry := b ≥ 2, out := some l }
  | 18 => 
    let b := bitSum ((rd 0).getD false) false false
    let l := b % 2 == 1
    { carry := b ≥ 2, out := some l }
  | 19 => 
    let b := bitSum ((rd 1).getD false) ((rd 5).getD false) false
    let l := b % 2 == 1
    { carry := b ≥ 2, out := some l }
  | 20 => 
    let b := bitSum ((rd 1).getD false) ((rd 5).getD false) carry
    let l := b % 2 == 1
    { carry := b ≥ 2, out := some l }
  | 21 => 
    let b := bitSum ((rd 2).getD false) ((rd 5).getD false) false
    let l := b % 2 == 1
    { carry := b ≥ 2, out := some l }
  | 22 => 
    let b := bitSum ((rd 2).getD false) ((rd 5).getD false) carry
    let l := b % 2 == 1
    { carry := b ≥ 2, out := some l }
  | 23 => 
    let b := bitSum ((rd 3).getD false) false false
    let l := b % 2 == 1
    { carry := b ≥ 2, out := some l }
  | 24 => 
    let b := bitSum ((rd 3).getD false) false carry
    let l := b % 2 == 1
    { carry := b ≥ 2, out := some l }
  | 25 => { jump := some 2585 }
  | 26 => 
    let b := bitSum ((rd 0).getD false) ((rd 1).getD false) false
    let l := b % 2 == 1
    { carry := b ≥ 2, wr := fun h => if h.val=0 then some (some l) else update 4 (some (xor ((rd 3).getD false) l)) h }
  | 27 => 
    let b := bitSum ((rd 0).getD false) ((rd 1).getD false) carry
    let l := b % 2 == 1
    { carry := b ≥ 2, wr := fun h => if h.val=0 then some (some l) else update 4 (some (xor ((rd 3).getD false) l)) h }
  | 28 => { wr := update 3 (rd 4) }
  | 29 => 
    let b := bitSum ((rd 2).getD false) ((rd 3).getD false) false
    let l := b % 2 == 1
    { carry := b ≥ 2, wr := fun h => if h.val=2 then some (some l) else update 4 (some (xor ((rd 1).getD false) l)) h }
  | 30 => 
    let b := bitSum ((rd 2).getD false) ((rd 3).getD false) carry
    let l := b % 2 == 1
    { carry := b ≥ 2, wr := fun h => if h.val=2 then some (some l) else update 4 (some (xor ((rd 1).getD false) l)) h }
  | 31 => { wr := update 1 (rd 4) }
  | 32 => { jump := some (if rd 4 = some true then 2580 else 2579) }
  | 33 => { jump := some (if rd 4 = some true then 2582 else 2581) }
  | 34 => { jump := some (if rd 4 = some true then 2584 else 2583) }
  | 35 => { jump := some (if rd 4 = some true then 818 else 783) }
  | 36 => { jump := some (if rd 4 = some true then 888 else 853) }
  | 37 => { jump := some (if rd 4 = some true then 1086 else 987) }
  | 38 => { jump := some (if rd 4 = some true then 1284 else 1185) }

  | _ => {}
def needsCarry (op : Nat) : Bool := op == 16 || op == 17 || op == 20 || op == 22 || op == 24 || op == 27 || op == 30

/-- Only carry-consuming program counters need a second control state. -/
def carryPC : Array Nat := (Array.range 2585).filter fun i => needsCarry ((code[i]?.getD 0)/729)
def machine : Machine where
  tapes := 5
  states := 3206
  time := 51941
  machine := {
    initial := 0
    tr := fun st input ws _ _ =>
      let high := st.val ≥ 2585
      let pc := if high then carryPC[st.val-2585]?.getD 2585 else st.val
      let op := code[pc]?.getD 0
      let rd := fun j : Nat => if h : j < 5 then ws ⟨j,h⟩ else input
      let a := action (op / 729) rd high
      let mv := fun j : Nat => dir ((op / 3^j) % 3)
      let next := a.jump.getD (pc+1)
      let dest := if a.carry && needsCarry ((code[next]?.getD 0)/729) then 2585+carryPC.toList.idxOf next else next
      .step { inputTape := mv 5
              workTapes := fun i => (a.wr i, if i.val=4 then a.scratchMove.getD (mv i.val) else mv i.val)
              output := a.out
              state := if next ≥ 2585 then none else if h : dest < 3206 then some ⟨dest,h⟩ else none }
            (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) }
end SharedQuarterBlock
