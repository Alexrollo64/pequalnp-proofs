import DisjointMatching
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Alexrollo64.OverlapMatching
open Alexrollo64.DisjointMatching
def matching (i : Fin 9) (b : Bool) : Nat :=
  if b then (![161,98,84,140,84,98,84,140,266] : Fin 9 → Nat) i else (![273,266,140,266,273,161,98,161,273] : Fin 9 → Nat) i
def on (i j k : Fin 9) (a b d : Bool) (t : Fin 9) :=
  (matching i d).testBit t.val || (a && decide (t=j)) || (b && decide (t=k))
def off (i j k : Fin 9) (a b d : Bool) (t : Fin 9) :=
  on i j k a b d t && decide (t ≠ i)

def blocked (i j k : Fin 9) (a b : Bool) : Bool :=
  !a && !b && [false,true].all (fun d =>
    (matching i d).testBit j.val || (matching i d).testBit k.val)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem masked : ∀ (i j k : Fin 9) (a b : Bool), i ≠ j → i ≠ k → j ≠ k →
    blocked i j k a b = false → ∃ d : Bool,
    target (on i j k a b d) ≠ target (off i j k a b d) ∧
    on i j k a b d j = a ∧ on i j k a b d k = b := by
  intro i
  fin_cases i <;> decide +kernel


theorem overlap (i j k : Fin 9) (a b : Bool) (ij : i ≠ j) (ik : i ≠ k) (jk : j ≠ k)
    (ok : blocked i j k a b = false) (t : Fin 9) :
    ∃ u v, target u ≠ target v ∧ val ⟨i,j,a⟩ u = val ⟨i,j,a⟩ v ∧
      val ⟨i,k,b⟩ u = val ⟨i,k,b⟩ v ∧ ∀ e, e ≠ t → u e = v e := by
  by_cases ti : t = i
  · subst t
    obtain ⟨d,ht,hj,hk⟩ := masked i j k a b ij ik jk ok
    refine ⟨_,_,ht,?_,?_,fun e he => by simp [off,he]⟩
    · cases a <;> simp_all [val,off,Ne.symm ij]
    · cases b <;> simp_all [val,off,Ne.symm ik]
  by_cases tj : t = j
  · obtain ⟨z,ne,eq⟩ := shield ⟨i,j,a⟩ t ij
    exact ⟨_,_,(pivots t z a ne).1,eq,untouched ⟨i,k,b⟩ t z a (Ne.symm ti) (by grind),
      fun e he => by simp [y,he]⟩
  · obtain ⟨z,ne,eq⟩ := shield ⟨i,k,b⟩ t ik
    exact ⟨_,_,(pivots t z b ne).1,untouched ⟨i,j,a⟩ t z b (Ne.symm ti) (Ne.symm tj),eq,
      fun e he => by simp [y,he]⟩
theorem raw_reads (i j k : Fin 9) (a b : Bool) (ij : i ≠ j) (ik : i ≠ k) (jk : j ≠ k) (ok : blocked i j k a b = false) (c : Circuit) (gs : List Gate) (shape : c.gates = (gate (⟨i,j,a⟩ : Pair))::(gate (⟨i,k,b⟩ : Pair))::gs)
    (last : c.output+1 = 9+c.size) (correct : ∀ x, c.eval (List.ofFn x) = target x) :
    ∀ i : Fin 9, i.val ∈ gs.flatMap Gate.inputs := by
  intro e
  by_contra absent

  obtain ⟨u,v,tar,eqp,eqq,eq⟩ := overlap i j k a b ij ik jk ok e
  have after (z : Fin 9 → Bool) : step (step (List.ofFn z) (gate (⟨i,j,a⟩ : Pair))) (gate (⟨i,k,b⟩ : Pair)) =
      (List.ofFn z ++ [val ⟨i,j,a⟩ z]) ++ [val ⟨i,k,b⟩ z] := by
    rw [show step (List.ofFn z) (gate (⟨i,j,a⟩ : Pair)) = List.ofFn z ++ [val ⟨i,j,a⟩ z] by simpa using step_gate (⟨i,j,a⟩ : Pair) z [], step_gate]
  have agreeStart : agree e.val (step (step (List.ofFn u) (gate (⟨i,j,a⟩ : Pair))) (gate (⟨i,k,b⟩ : Pair)))
      (step (step (List.ofFn v) (gate (⟨i,j,a⟩ : Pair))) (gate (⟨i,k,b⟩ : Pair))) := by
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
  have same := keep gs e.val _ _ agreeStart absent
  have far : c.output ≠ e.val := by simp [Circuit.size,shape] at last; omega
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

theorem lower (i j k : Fin 9) (a b : Bool) (ij : i ≠ j) (ik : i ≠ k) (jk : j ≠ k) (ok : blocked i j k a b = false) (c : Circuit) (fan : FanInTwo c) (correct : ∀ x, c.eval (List.ofFn x) = target x)
    (last : c.output+1 = 9+c.size)
    (live : ∀ j : Fin c.gates.length, j.val+1 < c.gates.length →
      ∃ k : Fin c.gates.length, j.val < k.val ∧ 9+j.val ∈ (c.gates.get k).inputs)
    (one : c.gates.head? = some (gate (⟨i,j,a⟩ : Pair))) (two : c.gates.tail.head? = some (gate (⟨i,k,b⟩ : Pair))) :
    12 ≤ c.size := by
  obtain ⟨gs,shape⟩ : ∃ gs, c.gates = (gate (⟨i,j,a⟩ : Pair))::(gate (⟨i,k,b⟩ : Pair))::gs := by
    cases h : c.gates with
    | nil => simp [h] at one
    | cons a rest =>
      cases rest with
      | nil => simp [h] at two
      | cons b gs => simp [h] at one two; exact ⟨gs,by simp [one,two]⟩
  have reads := raw_reads i j k a b ij ik jk ok c gs shape last correct
  have len : c.gates.length = gs.length+2 := by simp [shape]
  have all : Finset.range (gs.length+10) ⊆ (gs.flatMap Gate.inputs).toFinset := by
    intro wire hj; apply List.mem_toFinset.mpr
    have bound := Finset.mem_range.mp hj
    by_cases small : wire < 9
    · exact reads ⟨wire,small⟩
    · let ix : Fin c.gates.length := ⟨wire-9,by omega⟩
      obtain ⟨later,gt,used⟩ := live ix (by dsimp [ix]; omega)
      have uses : wire ∈ (c.gates.get later).inputs := by simpa [ix,Nat.add_sub_of_le (by omega : 9 ≤ wire)] using used
      let g := c.gates.get later
      change wire ∈ g.inputs at uses
      have mem : g ∈ (gate (⟨i,j,a⟩ : Pair))::(gate (⟨i,k,b⟩ : Pair))::gs := shape ▸ List.get_mem c.gates later
      rcases List.mem_cons.mp mem with a|m
      · rw [a] at uses; simp [gate] at uses; omega
      · rcases List.mem_cons.mp m with a|m
        · rw [a] at uses; simp [gate] at uses; omega
        · exact List.mem_flatMap.mpr ⟨_,m,uses⟩
  have bd := Finset.card_le_card all
  rw [Finset.card_range] at bd
  have th := List.toFinset_card_le (l := gs.flatMap Gate.inputs)
  have sl := slots gs (fun g hg => (fan g (by simp [shape,hg])).2)
  change 12 ≤ c.gates.length
  omega

end Alexrollo64.OverlapMatching
#print axioms Alexrollo64.OverlapMatching.lower
