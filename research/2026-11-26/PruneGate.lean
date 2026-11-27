import TreeCopies
import PEqualNP.Outside.L_meta_2606


namespace Alexrollo64.PruneGate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

open Alexrollo64.PaddedRows (mapCircuit rename mono_map map_eval)
open Alexrollo64.DisjointCopies (graph)

open PEqualNP.Outside.L_meta_2606 (wf wf_len wf_keep mono2 getD_snoc_lt getD_snoc_eq getD_snoc_gt)

def gateBit (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)

def skip (n : Nat) (c : Circuit) := mapCircuit
  (rename (n+1) n (fun i => if i < n then i else n+c.size)) c

theorem skip_eval (w : List Bool) (c : Circuit) :
    (skip w.length c).eval w = c.eval (w ++ [false]) := by
  unfold skip
  have len : (w ++ [false]).length = w.length+1 := by simp
  rw [←len]
  apply map_eval
  intro zs hz i hi
  by_cases h : i < w.length
  · simp only [ite_eq_left h,List.getD_append _ _ _ _ h]
  · have eq : i = w.length := by omega
    subst i
    rw [ite_eq_right (by omega),List.getD_eq_default _ _ (by simp; omega),
      List.getD_append_right _ _ _ _ (by omega)]
    simp

/-- A monotone suffix can be fed false on a negative-only wire, even when it shares
other gates. Removing the wire shifts every subsequent gate index by one. -/
theorem prune {D : Type} (f : D → Bool) (x : D → List Bool) (n : Nat)
    (fixed : ∀ d, (x d).length = n) (pre : List Gate) (g : Gate) (suffix : Circuit)
    (hm : Monotone2 ⟨pre ++ g :: suffix.gates,suffix.output⟩)
    (correct : ∀ d, (⟨pre ++ g :: suffix.gates,suffix.output⟩ : Circuit).eval (x d) = f d)
    (pos : ∀ d, f d = true → suffix.eval (wf pre (x d) ++ [false]) = true) :
    ∃ c : Circuit, Monotone2 c ∧ c.size = pre.length + suffix.size ∧
      ∀ d, c.eval (x d) = f d := by
  let rest := skip (n+pre.length) suffix
  let c : Circuit := ⟨pre ++ rest.gates,rest.output⟩
  have hs : Monotone2 suffix := fun a ha => hm a (by simp [ha])
  have hr : Monotone2 rest := mono_map _ hs
  refine ⟨c,?_,?_,?_⟩
  · intro a ha
    change a ∈ pre ++ rest.gates at ha
    rcases List.mem_append.mp ha with h|h
    · exact hm a (by simp [h])
    · exact hr a h
  · simp [c,rest,skip,mapCircuit,Circuit.size]
  · intro d
    let w := wf pre (x d)
    have len : w.length = n+pre.length := by simp [w,wf_len,fixed]
    have old : suffix.eval (w ++ [gateBit w g]) = f d := by
      simpa [Circuit.eval,Circuit.wires,w,wf,List.foldl_append,gateBit] using correct d
    have split : c.eval (x d) = rest.eval w := by simp [c,Circuit.eval,Circuit.wires,w,wf,List.foldl_append]
    rw [split]
    unfold rest
    rw [←len,skip_eval]
    change suffix.eval (w ++ [false]) = f d
    cases eq : f d with
    | true => exact pos d eq
    | false =>
      have le (i : Nat) : (w ++ [false]).getD i false = true →
          (w ++ [gateBit w g]).getD i false = true := by
        by_cases h : i < w.length
        · rw [getD_snoc_lt _ _ _ h,getD_snoc_lt _ _ _ h]
          exact id
        · rcases Nat.eq_or_lt_of_le (Nat.le_of_not_gt h) with eqi|gt
          · subst i; rw [getD_snoc_eq]; simp
          · rw [getD_snoc_gt _ _ _ gt]; simp
      have m := mono2 suffix.gates (fun a ha => hs a ha) _ _ (by simp) le suffix.output
      change suffix.eval _ = true → suffix.eval _ = true at m
      rw [old,eq] at m
      cases e : suffix.eval (w ++ [false]) <;> simp_all

/-- Every individual gate of a tight circuit must fire on at least one edge,
even if its computation and all downstream computations have arbitrary fan-out. -/
theorem essential_gate {k : Nat} (pre : List Gate) (g : Gate) (suffix : Circuit)
    (hm : Monotone2 ⟨pre ++ g :: suffix.gates,suffix.output⟩)
    (hr : Represents (graph k) ⟨pre ++ g :: suffix.gates,suffix.output⟩)
    (hs : pre.length + 1 + suffix.size ≤ 8*k) :
    ∃ u v : Fin (5*k), graph k u v = true ∧ suffix.eval (wf pre (oneEach u v) ++ [false]) = false := by
  by_contra! none
  obtain ⟨c,legal,size,correct⟩ := prune (D := Fin (5*k) × Fin (5*k))
    (fun d => graph k d.1 d.2) (fun d => oneEach d.1 d.2) (5*k+5*k)
    (fun d => by simp [oneEach]) pre g suffix hm (fun d => hr d.1 d.2)
    (fun d e => by simpa using none d.1 d.2 e)
  have low := Alexrollo64.DisjointCopies.lower k c.size
    ⟨c,legal,le_rfl,fun u v => correct (u,v)⟩
  omega

theorem tight_gate {k : Nat} (pre : List Gate) (g : Gate) (suffix : Circuit)
    (hm : Monotone2 ⟨pre ++ g :: suffix.gates,suffix.output⟩)
    (hr : Represents (graph k) ⟨pre ++ g :: suffix.gates,suffix.output⟩)
    (hs : pre.length + 1 + suffix.size ≤ 8*k) :
    ∃ u v : Fin (5*k), graph k u v = true ∧ gateBit (wf pre (oneEach u v)) g = true := by
  obtain ⟨u,v,pos,forced⟩ := essential_gate pre g suffix hm hr hs
  refine ⟨u,v,pos,?_⟩
  have orig := (hr u v).trans pos
  change (⟨pre ++ g :: suffix.gates,suffix.output⟩ : Circuit).eval (oneEach u v) = true at orig
  have eq : suffix.eval (wf pre (oneEach u v) ++ [gateBit (wf pre (oneEach u v)) g]) = true := by
    simpa [Circuit.eval,Circuit.wires,wf,List.foldl_append,gateBit] using orig
  cases h : gateBit (wf pre (oneEach u v)) g <;> simp_all

/-- Both raw operands must co-occur on an accepted input. -/
theorem and_pair {k : Nat} (pre : List Gate) (a b : Fin (10*k)) (suffix : Circuit)
    (hm : Monotone2 ⟨pre ++ ⟨.and,[a.val,b.val]⟩ :: suffix.gates,suffix.output⟩)
    (hr : Represents (graph k) ⟨pre ++ ⟨.and,[a.val,b.val]⟩ :: suffix.gates,suffix.output⟩)
    (hs : pre.length + 1 + suffix.size ≤ 8*k) :
    ∃ u v : Fin (5*k), graph k u v = true ∧
      (oneEach u v).getD a.val false = true ∧ (oneEach u v).getD b.val false = true := by
  obtain ⟨u,v,pos,on⟩ := tight_gate pre _ suffix hm hr hs
  have la : a.val < (oneEach u v).length := by simp [oneEach] <;> omega
  have lb : b.val < (oneEach u v).length := by simp [oneEach] <;> omega
  exact ⟨u,v,pos,by simpa only [gateBit,List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true,id_eq,wf_keep pre _ _ la,wf_keep pre _ _ lb]
    using on⟩

def admissiblePairs := ((Finset.univ : Finset (Fin 20 × Fin 20))).filter fun p =>
  p.1 < p.2 ∧ ∃ u v : Fin 10, graph 2 u v = true ∧
    (p.1.val = u.val ∨ p.1.val = 10+v.val) ∧ (p.2.val = u.val ∨ p.2.val = 10+v.val)

set_option maxHeartbeats 2000000 in
theorem count_pairs : admissiblePairs.card = 16 := by decide +kernel

/-- An AND reading a raw row and column must select a genuine edge. -/
theorem and_cell {k : Nat} (pre : List Gate) (a b : Fin (5*k)) (suffix : Circuit)
    (hm : Monotone2 ⟨pre ++ ⟨.and,[a.val,5*k+b.val]⟩ :: suffix.gates,suffix.output⟩)
    (hr : Represents (graph k) ⟨pre ++ ⟨.and,[a.val,5*k+b.val]⟩ :: suffix.gates,suffix.output⟩)
    (hs : pre.length + 1 + suffix.size ≤ 8*k) : graph k a b = true := by
  obtain ⟨u,v,pos,on⟩ := tight_gate pre _ suffix hm hr hs
  have la : a.val < (oneEach u v).length := by simp [oneEach] <;> omega
  have lb : 5*k+b.val < (oneEach u v).length := by simp [oneEach] <;> omega
  simp only [gateBit,List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,
    Bool.and_true,Bool.and_eq_true,id_eq,wf_keep pre _ _ la,wf_keep pre _ _ lb,
    Alexrollo64.PaddedRows.one_read,Bool.or_eq_true,decide_eq_true_eq] at on
  have ha : a = u := Fin.ext (by omega)
  have hb : b = v := Fin.ext (by omega)
  simpa [ha,hb] using pos

#print axioms and_cell
#print axioms essential_gate
#print axioms tight_gate
end Alexrollo64.PruneGate
