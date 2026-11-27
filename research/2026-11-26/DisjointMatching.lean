import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace Alexrollo64.DisjointMatching

def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
def target (x : Fin 9 → Bool) :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def seed (i j : Fin 9) (b : Bool) : Nat := ([160,0,160,162,160,164,160,168,160,176,272,160,160,224,272,160,160,272,96,97,96,0,96,100,96,104,96,112,264,96,264,96,96,224,96,264,80,81,80,82,80,0,80,88,136,80,80,112,136,80,80,136,80,336,132,133,132,134,258,132,132,0,132,148,132,164,132,196,258,132,132,258,68,69,68,70,257,68,68,76,68,0,68,100,257,68,68,196,68,257,66,67,129,66,66,70,66,74,66,82,66,0,129,66,66,129,66,322,20,21,20,22,34,20,20,28,34,20,20,34,20,0,20,148,20,276,12,13,12,14,33,12,33,12,12,28,12,33,12,76,12,0,12,268,10,11,17,10,10,14,17,10,10,17,10,42,10,74,10,138,10,0] : List Nat).getD (18*i.val+2*j.val+b.toNat) 0
def x (i j : Fin 9) (b : Bool) (k : Fin 9) := (seed i j b).testBit k.val
def y (i j : Fin 9) (b : Bool) (k : Fin 9) := x i j b k || decide (k=i)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pivots : ∀ (i j : Fin 9) (b : Bool), i ≠ j →
  target (x i j b) ≠ target (y i j b) ∧ x i j b j = b := by decide +kernel

structure Pair where
  a : Fin 9
  b : Fin 9
  useOr : Bool

def val (p : Pair) (z : Fin 9 → Bool) := if p.useOr then z p.a || z p.b else z p.a && z p.b

theorem untouched (p : Pair) (i j : Fin 9) (b : Bool) (h₁ : p.a ≠ i) (h₂ : p.b ≠ i) :
    val p (x i j b) = val p (y i j b) := by simp [val,y,h₁,h₂]

theorem shield (p : Pair) (i : Fin 9) (h : p.a ≠ p.b) :
    ∃ j, i ≠ j ∧ val p (x i j p.useOr) = val p (y i j p.useOr) := by
  by_cases a : p.a = i
  · refine ⟨p.b, a ▸ h, ?_⟩
    have ne : p.b ≠ i := by grind
    have eq := (pivots i p.b p.useOr ne.symm).2
    cases op : p.useOr <;> simp_all [val,y]
  · refine ⟨p.a,Ne.symm a,?_⟩
    have eq := (pivots i p.a p.useOr (Ne.symm a)).2
    cases op : p.useOr <;> simp_all [val,y]

theorem collisions (p q : Pair) (i : Fin 9) (hp : p.a ≠ p.b) (hq : q.a ≠ q.b)
    (dis : ∀ k, k = p.a ∨ k = p.b → k ≠ q.a ∧ k ≠ q.b) :
    ∃ u v, target u ≠ target v ∧ val p u = val p v ∧ val q u = val q v ∧
      ∀ k, k ≠ i → u k = v k := by
  by_cases h : i = p.a ∨ i = p.b
  · obtain ⟨j,ne,eq⟩ := shield p i hp
    obtain ⟨a,b⟩ := dis i h
    exact ⟨_,_,(pivots i j p.useOr ne).1,eq,untouched q i j _ a.symm b.symm,
      fun k hk => by simp [y,hk]⟩
  · obtain ⟨j,ne,eq⟩ := shield q i hq
    exact ⟨_,_,(pivots i j q.useOr ne).1,untouched p i j _ (by grind) (by grind),eq,
      fun k hk => by simp [y,hk]⟩

theorem raw (z : Fin 9 → Bool) (k : Fin 9) : (List.ofFn z).getD k.val false = z k := by
  fin_cases k <;> rfl

def gate (p : Pair) : Gate := ⟨if p.useOr then .or else .and,[p.a.val,p.b.val]⟩
theorem step_gate (p : Pair) (z : Fin 9 → Bool) (extra : List Bool) :
    step (List.ofFn z ++ extra) (gate p) = (List.ofFn z ++ extra) ++ [val p z] := by
  have h (k : Fin 9) : (List.ofFn z ++ extra).getD k.val false = z k := by
    rw [List.getD_append _ _ _ _ (by simp)]
    exact raw z k
  unfold step gate val
  simp only [List.map_cons,List.map_nil,h]
  cases b : p.useOr <;> simp [GateOp.eval]

def agree (i : Nat) (x y : List Bool) := x.length = y.length ∧
  ∀ j, j ≠ i → x.getD j false = y.getD j false

theorem keep (gs : List Gate) (i : Nat) (x y : List Bool) (h : agree i x y)
    (miss : i ∉ gs.flatMap Gate.inputs) : agree i (gs.foldl step x) (gs.foldl step y) := by
  induction gs generalizing x y with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.flatMap_cons,List.mem_append,not_or] at miss
    apply ih _ _ _ miss.2
    have eq : (g.inputs.map fun j => x.getD j false) = (g.inputs.map fun j => y.getD j false) := by
      apply List.map_congr_left
      intro j hj; exact h.2 j (fun e => miss.1 (e ▸ hj))
    refine ⟨by simp [step,h.1],?_⟩
    intro j ne
    by_cases lt : j < x.length
    · exact (List.getD_append _ _ _ _ lt).trans ((h.2 j ne).trans (List.getD_append _ _ _ _ (h.1 ▸ lt)).symm)
    · unfold step
      rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by have := h.1; omega),eq,h.1]

theorem raw_reads (p q : Pair) (hp : p.a ≠ p.b) (hq : q.a ≠ q.b)
    (dis : ∀ k, k = p.a ∨ k = p.b → k ≠ q.a ∧ k ≠ q.b) (c : Circuit) (gs : List Gate) (shape : c.gates = (gate p)::(gate q)::gs)
    (last : c.output+1 = 9+c.size) (correct : ∀ x, c.eval (List.ofFn x) = target x) :
    ∀ i : Fin 9, i.val ∈ gs.flatMap Gate.inputs := by
  intro i
  by_contra absent

  obtain ⟨u,v,tar,eqp,eqq,eq⟩ := collisions p q i hp hq dis
  have after (z : Fin 9 → Bool) : step (step (List.ofFn z) (gate p)) (gate q) =
      (List.ofFn z ++ [val p z]) ++ [val q z] := by
    rw [show step (List.ofFn z) (gate p) = List.ofFn z ++ [val p z] by simpa using step_gate p z [], step_gate]
  have agreeStart : agree i.val (step (step (List.ofFn u) (gate p)) (gate q))
      (step (step (List.ofFn v) (gate p)) (gate q)) := by
    rw [after,after]; constructor
    · simp
    intro j ne
    simp only [List.append_assoc,eqp,eqq]
    by_cases lt : j < 9
    · rw [List.getD_append (List.ofFn u) _ _ _ (by simpa), List.getD_append (List.ofFn v) _ _ _ (by simpa)]
      exact (raw u ⟨j,lt⟩).trans ((eq ⟨j,lt⟩ (by grind)).trans (raw v ⟨j,lt⟩).symm)
    · rw [List.getD_append_right (List.ofFn u) _ _ _ (by simpa using Nat.le_of_not_gt lt),
          List.getD_append_right (List.ofFn v) _ _ _ (by simpa using Nat.le_of_not_gt lt)]
      simp
  have same := keep gs i.val _ _ agreeStart absent
  have far : c.output ≠ i.val := by simp [Circuit.size,shape] at last; omega
  apply tar
  rw [← correct,← correct]
  unfold Circuit.eval Circuit.wires
  rw [shape]
  exact same.2 c.output far

theorem slots (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2*gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have a := h g (by simp)
    have b := ih (fun x hx => h x (by simp [hx]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons]; omega

theorem lower (p q : Pair) (hp : p.a ≠ p.b) (hq : q.a ≠ q.b)
    (dis : ∀ k, k = p.a ∨ k = p.b → k ≠ q.a ∧ k ≠ q.b) (c : Circuit) (fan : FanInTwo c) (correct : ∀ x, c.eval (List.ofFn x) = target x)
    (last : c.output+1 = 9+c.size)
    (live : ∀ j : Fin c.gates.length, j.val+1 < c.gates.length →
      ∃ k : Fin c.gates.length, j.val < k.val ∧ 9+j.val ∈ (c.gates.get k).inputs)
    (one : c.gates.head? = some (gate p)) (two : c.gates.tail.head? = some (gate q)) :
    12 ≤ c.size := by
  obtain ⟨gs,shape⟩ : ∃ gs, c.gates = (gate p)::(gate q)::gs := by
    cases h : c.gates with
    | nil => simp [h] at one
    | cons a rest =>
      cases rest with
      | nil => simp [h] at two
      | cons b gs => simp [h] at one two; exact ⟨gs,by simp [one,two]⟩
  have reads := raw_reads p q hp hq dis c gs shape last correct
  have len : c.gates.length = gs.length+2 := by simp [shape]
  have all : Finset.range (gs.length+10) ⊆ (gs.flatMap Gate.inputs).toFinset := by
    intro j hj; apply List.mem_toFinset.mpr
    have bound := Finset.mem_range.mp hj
    by_cases small : j < 9
    · exact reads ⟨j,small⟩
    · let i : Fin c.gates.length := ⟨j-9,by omega⟩
      obtain ⟨k,gt,used⟩ := live i (by dsimp [i]; omega)
      have uses : j ∈ (c.gates.get k).inputs := by simpa [i,Nat.add_sub_of_le (by omega : 9 ≤ j)] using used
      let g := c.gates.get k
      change j ∈ g.inputs at uses
      have mem : g ∈ (gate p)::(gate q)::gs := shape ▸ List.get_mem c.gates k
      rcases List.mem_cons.mp mem with a|m
      · rw [a] at uses; simp [gate] at uses; have := p.a.isLt; have := p.b.isLt; omega
      · rcases List.mem_cons.mp m with a|m
        · rw [a] at uses; simp [gate] at uses; have := q.a.isLt; have := q.b.isLt; omega
        · exact List.mem_flatMap.mpr ⟨_,m,uses⟩
  have bd := Finset.card_le_card all
  rw [Finset.card_range] at bd
  have th := List.toFinset_card_le (l := gs.flatMap Gate.inputs)
  have sl := slots gs (fun g hg => (fan g (by simp [shape,hg])).2)
  change 12 ≤ c.gates.length
  omega

end Alexrollo64.DisjointMatching
#print axioms Alexrollo64.DisjointMatching.lower
