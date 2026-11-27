import Saturation

namespace Alexrollo64.EssentialCost
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Alexrollo64.DisjointMatching (step keep agree slots)
open Alexrollo64.DeletedEdge (cost pack)
open Alexrollo64.Saturation (sig normal certify)

def Essential {N : Nat} (T : (Fin N → Bool) → Prop) (i : Fin N) :=
  ∃ x y, T x ∧ ¬ T y ∧ ∀ j, j ≠ i → x j = y j

theorem ofFn_read {N : Nat} (x : Fin N → Bool) (j : Fin N) :
    (List.ofFn x).getD j.val false = x j := by
  simp only [List.getD, List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using j.isLt :
    j.val < (List.ofFn x).length), Option.getD_some, List.getElem_ofFn]

theorem cost_lower {N : Nat} (T : (Fin N → Bool) → Prop)
    (essential : ∀ i, Essential T i) (c : Circuit) (fan : FanInTwo c)
    (correct : ∀ x, c.eval (List.ofFn x) = true ↔ T x)
    (legal : ∀ k : Fin c.gates.length, normal (N+k.val) (c.gates.get k))
    (live : ∀ k : Fin c.gates.length, N+k.val = c.output ∨
      ∃ g ∈ c.gates, N+k.val ∈ g.inputs)
    (samples : Fin 6 → Fin N → Bool)
    (gap : (∑ j : Fin N, cost (pack (fun s => samples s j))) <
      cost (pack (fun s => c.eval (List.ofFn (samples s))))) : N ≤ c.size := by
  by_contra! small
  let uses := c.gates.flatMap Gate.inputs ++ [c.output]
  have used (j : Nat) (hj : j < N+c.size) : j ∈ uses := by
    by_cases lt : j < N
    · by_contra absent
      have miss : j ∉ c.gates.flatMap Gate.inputs ∧ c.output ≠ j := by
        simpa [uses,eq_comm] using absent
      obtain ⟨x,y,yes,no,eq⟩ := essential ⟨j,lt⟩
      have ax : agree j (List.ofFn x) (List.ofFn y) := by
        constructor
        · simp
        intro k ne
        by_cases lk : k < N
        · exact (ofFn_read x ⟨k,lk⟩).trans ((eq ⟨k,lk⟩ (by grind)).trans (ofFn_read y ⟨k,lk⟩).symm)
        · rw [List.getD_eq_default,List.getD_eq_default] <;> simpa using Nat.le_of_not_gt lk
      have same := (keep c.gates j _ _ ax miss.1).2 _ miss.2
      change c.eval (List.ofFn x) = c.eval (List.ofFn y) at same
      exact no ((correct y).mp (same ▸ (correct x).mpr yes))
    · let k : Fin c.gates.length := ⟨j-N,by change j < N+c.gates.length at hj; omega⟩
      have idx : N+k.val = j := by dsimp [k]; omega
      rcases live k with h|⟨g,hg,h⟩
      · simp [uses,← h,idx]
      · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨g,hg,idx ▸ h⟩)
  have sub : (List.range (N+c.size)).Subperm uses :=
    List.subperm_of_subset List.nodup_range (fun j hj => used j (List.mem_range.mp hj))
  obtain ⟨l,perm,sl⟩ := sub
  have same : l = uses := sl.eq_of_length_le (by
    have := slots c.gates (fun g h => (fan g h).2)
    have len := perm.length_eq; simp only [List.length_range] at len
    simp only [uses,List.length_append,List.length_singleton]; change c.gates.length < N at small
    change l.length = N+c.gates.length at len; omega)
  obtain ⟨f,raw,valid,final⟩ := certify c.gates N (fun s => List.ofFn (samples s)) (by simp) legal
  let v := cost ∘ f
  have pay := MatchingAccounting.total v N c.gates valid
  have P := ((same ▸ perm : uses.Perm (List.range (N+c.size))).map v).sum_eq
  rw [List.range_add,← List.range'_eq_map_range] at P
  simp only [uses,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton] at P
  have init : ((List.range N).map v).sum = ∑ j : Fin N, cost (pack (fun s => samples s j)) := by
    have re (n : Nat) : ((List.range n).map v).sum = ∑ j ∈ Finset.range n, v j := by
      induction n with
      | zero => simp
      | succ n ih => simp [List.range_succ,Finset.sum_range_succ,ih]
    rw [re,← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl; intro j _
    simp only [v,Function.comp_apply,raw j j.isLt,sig]
    congr 2; funext s; exact ofFn_read _ j
  have out : v c.output = cost (pack (fun s => c.eval (List.ofFn (samples s)))) := by
    rw [show v c.output = cost (f c.output) by rfl,final]; rfl
  change _ = _ + ((List.range' N c.gates.length).map v).sum at P
  omega
end Alexrollo64.EssentialCost
