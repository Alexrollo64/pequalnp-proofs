import DeletedEdge
import OverlapMatching

namespace Alexrollo64.MatchingAccounting
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Alexrollo64.DisjointMatching
open Alexrollo64.DeletedEdge (cost Column samples wanted)

-- A value assignment for all wires, labelled by their cost on six graphs.
def valid (v : Nat → Nat) (n : Nat) : List Gate → Prop
  | [] => True
  | g :: gs => v n ≤ (g.inputs.map v).sum ∧ valid v (n+1) gs

theorem total (v : Nat → Nat) (n : Nat) (gs : List Gate) (h : valid v n gs) :
    ((List.range' n gs.length).map v).sum ≤ ((gs.flatMap Gate.inputs).map v).sum := by
  induction gs generalizing n with
  | nil => simp
  | cons g gs ih =>
    obtain ⟨first,rest⟩ := h
    have tail := ih (n+1) rest
    simp [List.range'_succ]; omega

-- An essential raw input other than the deleted one must still be read.
theorem other_reads (i j k : Fin 9) (a b : Bool) (ij : i ≠ j) (ik : i ≠ k) (jk : j ≠ k) (c : Circuit) (gs : List Gate) (shape : c.gates = (gate (⟨i,j,a⟩ : Pair))::(gate (⟨i,k,b⟩ : Pair))::gs)
    (last : c.output+1 = 9+c.size) (correct : ∀ x, c.eval (List.ofFn x) = target x) :
    ∀ e : Fin 9, e ≠ i → e.val ∈ gs.flatMap Gate.inputs := by
  intro e ei
  by_contra absent

  have col : ∃ u v, target u ≠ target v ∧ val ⟨i,j,a⟩ u = val ⟨i,j,a⟩ v ∧
      val ⟨i,k,b⟩ u = val ⟨i,k,b⟩ v ∧ ∀ z, z ≠ e → u z = v z := by
    by_cases ej : e = j
    · obtain ⟨z,ne,eq⟩ := shield ⟨i,j,a⟩ e ij
      exact ⟨_,_,(pivots e z a ne).1,eq,untouched ⟨i,k,b⟩ e z a (Ne.symm ei) (by grind), fun h hn => by simp [y,hn]⟩
    · obtain ⟨z,ne,eq⟩ := shield ⟨i,k,b⟩ e ik
      exact ⟨_,_,(pivots e z b ne).1,untouched ⟨i,j,a⟩ e z b (Ne.symm ei) (Ne.symm ej),eq,fun h hn => by simp [y,hn]⟩
  obtain ⟨u,v,tar,eqp,eqq,eq⟩ := col
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

theorem budget (i : Fin 9) (gs : List Gate) (v : Nat → Nat)
    (arity : ∀ g ∈ gs, g.inputs.length ≤ 2) (small : gs.length ≤ 9)
    (used : ∀ x < 10 + gs.length, x ≠ i.val → x ∈ gs.flatMap Gate.inputs)
    (h : valid v 11 gs) (free₁ : v 9 = 0) (free₂ : v 10 = 0)
    (start : ((List.range 9).map v).sum = 2) :
    v (10+gs.length) ≤ 2 := by
  let inputs := gs.flatMap Gate.inputs
  let out := 10+gs.length
  have lt : i.val < out := by dsimp [out]; omega
  let req := (List.range out).erase i.val
  have nod : req.Nodup := List.Nodup.erase _ (List.nodup_range)
  have sub : req.Subperm inputs := by
    apply List.subperm_of_subset nod
    intro x hx
    have mem := List.mem_of_mem_erase hx
    have ne : x ≠ i.val := by
      intro e; subst x; exact List.Nodup.not_mem_erase List.nodup_range hx
    exact used _ (List.mem_range.mp mem) ne
  have len : req.length = out-1 := by simpa [req] using List.length_erase_of_mem (List.mem_range.mpr lt)
  have slots := Alexrollo64.DisjointMatching.slots gs arity
  obtain ⟨l,perm,sl⟩ := sub
  have same : l = inputs := sl.eq_of_length_le (by
    have := perm.length_eq; dsimp [inputs,out] at *; omega)
  have P : inputs.Perm req := same ▸ perm
  have cap := total v 11 gs h
  have cover := ((List.erase_sublist (l := List.range out) (a := i.val)).map v)
  have H := Alexrollo64.DeletedEdge.subSum cover
  have eq := (P.map v).sum_eq
  change _ ≤ (inputs.map v).sum at cap
  have pack : List.range (11+gs.length) = List.range 9 ++ [9,10] ++ List.range' 11 gs.length := by
    rw [List.range_add, ← List.range'_eq_map_range]
    rfl
  have split : List.range (11+gs.length) = List.range out ++ [out] := by
    change List.range (11+gs.length) = _
    rw [show 11+gs.length = out+1 by dsimp [out]; omega, List.range_succ]
  have both := congrArg (fun l : List Nat => (l.map v).sum) (split.symm.trans pack)
  simp only [List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at both
  change (req.map v).sum ≤ _ at H
  change v out ≤ 2
  omega

end Alexrollo64.MatchingAccounting
#print axioms Alexrollo64.MatchingAccounting.budget
