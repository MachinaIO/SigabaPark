import Definitions.Def_WE_TraceLock

open SigabaNeo AdvancedEncryption.WE.TraceLock


private def traceFrom (h : List Bool) : GateList → List Bool
  | [] => []
  | (a,b)::gs =>
    let v := !(h.getD a true && h.getD b true)
    v :: traceFrom (h++[v]) gs

private theorem fold_trace (h : List Bool) (gs : GateList) (last : Bool) :
    (gs.foldl estep (h,last)).1 = h ++ traceFrom h gs := by
  induction gs generalizing h last with
  | nil => simp [traceFrom]
  | cons g gs ih =>
    rcases g with ⟨a,b⟩
    simp [traceFrom,estep,ih,List.append_assoc]

private theorem map_read (h : List Atom) (w t : ℕ → Bool) (a : ℕ) :
    (h.getD a .one).read w t = (h.map (Atom.read w t)).getD a true := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h[a]? <;> rfl

private theorem faithful (w t : ℕ → Bool) (h : List Atom) (i : ℕ) (gs : GateList) :
    (∀ e ∈ flags h i gs, e.eval w t = true) ↔
      segment t i gs.length = traceFrom (h.map (Atom.read w t)) gs := by
  induction gs generalizing h i with
  | nil => simp [flags,segment,traceFrom]
  | cons g gs ih =>
    obtain ⟨a,b⟩ := g
    simp only [flags,List.mem_cons, forall_eq_or_imp,List.length_cons,segment,traceFrom,
      Expr.eval,map_read,List.cons.injEq]
    change ((xor (t i) _) = true ∧ _) ↔ (_ ∧ _)
    rw [ih]
    simp only [List.map_append,List.map_cons,List.map_nil,Atom.read]
    generalize (List.map (Atom.read w t) h).getD a true = A
    generalize (List.map (Atom.read w t) h).getD b true = B
    generalize t i = C
    cases A <;> cases B <;> cases C <;> simp

private theorem leaves (g : ℕ → Expr) (w t : ℕ → Bool) (i d : ℕ) :
    (tree g i d).eval w t = true ↔ ∀ j, i ≤ j → j < i+2^d → (g j).eval w t = true := by
  induction d generalizing i with
  | zero =>
    simp only [tree,pow_zero]
    constructor
    · intro h j left right
      have : j=i := by omega
      simpa [this] using h
    · intro h
      exact h i le_rfl (by omega)
  | succ d ih =>
    simp only [tree, Expr.eval, Bool.and_eq_true, ih, pow_succ]
    constructor
    · rintro ⟨a,b⟩ j lo hi
      by_cases hl : j < i+2^d
      · exact a j lo hl
      · exact b j (by omega) (by omega)
    · intro h
      constructor <;> intro j jlo jhi <;> apply h <;> omega

private theorem boundsFlags (h : List Atom) (i : ℕ) (gs : GateList) :
    (flags h i gs).length = gs.length ∧
      ∀ e ∈ flags h i gs, e.depth = 2 ∧ e.gates = 2 := by
  induction gs generalizing h i with
  | nil => simp [flags]
  | cons g gs ih =>
    obtain ⟨a,b⟩ := g
    obtain ⟨hl,hp⟩ := ih (h++[.gate i]) (i+1)
    simpa [flags,hl,Expr.depth,Expr.gates] using hp

private theorem shape (g : ℕ → Expr) (i d : ℕ)
    (h : ∀ j, i ≤ j → j < i+2^d → (g j).depth = 2 ∧ (g j).gates = 2) :
    (tree g i d).depth = 2+d ∧ (tree g i d).gates + 1 = 3*2^d := by
  induction d generalizing i with
  | zero =>
    obtain ⟨a,b⟩ := h i le_rfl (by simp)
    simp [tree,a,b]
  | succ d ih =>
    rw [pow_succ] at h ⊢
    obtain ⟨a,b⟩ := ih i (by intro j jl jr; apply h j jl; omega)
    obtain ⟨c,e⟩ := ih (i+2^d) (by intro j jl jr; apply h j <;> omega)
    simp [tree,Expr.depth,Expr.gates,a,c]
    omega


private theorem attach (node : Expr) (w t : ℕ → Bool) (rhs : Prop)
    (d : node.depth = 14) (n : node.gates+1 = 12288)
    (ev : node.eval w t = true ↔ rhs) :
    let e := Expr.conj node (.lit (.gate 4095))
    e.depth = 15 ∧ e.gates = 12288 ∧
      (e.eval w t = true ↔ rhs ∧ t 4095 = true) := by
  simp [Expr.depth,Expr.gates,Expr.eval,Atom.read,d,n,ev]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 12000 in
theorem solution (gs : GateList) (hg : gs.length = 4096) (w t : ℕ → Bool) :
    let h := (inputs 128).map (Atom.read w t)
    (predicate gs).depth = 15 ∧ (predicate gs).gates = 12288 ∧
    ((predicate gs).eval w t = true ↔
      segment t 0 4096 = (gs.foldl estep (h,true)).1.drop h.length ∧ t 4095 = true) := by
  dsimp only
  let fs := flags (inputs 128) 0 gs
  let g := fun i ↦ fs.getD i (.lit .one)
  obtain ⟨len,ok⟩ := boundsFlags (inputs 128) 0 gs
  have size : fs.length = 4096 := len.trans hg
  have within (j : ℕ) (hj : j < 4096) : g j = fs[j]'(by omega) := by
    simp [g,List.getD_eq_getElem?_getD,show j < fs.length by omega]
  obtain ⟨hd,hn⟩ := shape g 0 12 (by
    intro j _ hj
    rw [within j (by simpa using hj)]
    exact ok _ (List.getElem_mem ..))
  have use := attach (tree g 0 12) w t
  apply use
  · exact hd
  · exact hn
  rw [fold_trace,List.drop_left]
  have cover : (tree g 0 12).eval w t = true ↔ ∀ e ∈ fs, e.eval w t = true := by
    rw [leaves]
    constructor
    · intro all e he
      obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp he
      have lt : j < 4096 := by omega
      simpa [within j lt] using all j (by omega) (by simpa using lt)
    · intro all j _ hj
      rw [within j (by simpa using hj)]
      exact all _ (List.getElem_mem ..)
  exact cover.trans (by simpa only [hg] using faithful w t (inputs 128) 0 gs)
