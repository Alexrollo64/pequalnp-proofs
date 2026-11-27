import Std.Sat.CNF.Sat
import FiveGateCNF

namespace Alexrollo64.FiveGateCNF

private theorem signs (t : Trace) (k : Key) (h : k ∈ keys) :
    litValue (assignment t) (pos k.number) = k.bit t ∧
    litValue (assignment t) (-(pos k.number)) = !(k.bit t) := by
  exact ⟨(lit_pos _ _ (allocated.2 k h).2).trans (assigned _ _ h),
    (lit_neg _ _).trans (congrArg Bool.not (assigned _ _ h))⟩

private theorem parent_keys (g i : Nat) (hg : g < 5) (hi : i < 6+g) :
    Key.left g i ∈ keys ∧ Key.right g i ∈ keys := by
  constructor <;> apply gate_mem g hg <;>
    simp only [gateKeys,List.mem_append] <;>
    have hl : Key.left g i ∈ (List.range (6+g)).map (Key.left g) := List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩ <;>
    have hr : Key.right g i ∈ (List.range (6+g)).map (Key.right g) := List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩ <;> tauto

private theorem op_key (g i : Nat) (hg : g < 5) (hi : i < 3) : Key.oper g i ∈ keys := by
  apply gate_mem g hg
  have hm : Key.oper g i ∈ (List.range 3).map (Key.oper g) := List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩
  simp only [gateKeys,List.mem_append]; tauto

private theorem row_keys (g r : Nat) (hg : g < 5) (hr : r < 21) :
    Key.lhs g r ∈ keys ∧ Key.rhs g r ∈ keys ∧ Key.wire (6+g) r ∈ keys := by
  have H (k : Key) (hk : k ∈ [Key.lhs g r,.rhs g r,.wire (6+g) r]) : k ∈ keys := by
    apply gate_mem g hg
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨r,List.mem_range.mpr hr,hk⟩
  exact ⟨H _ (by simp),H _ (by simp),H _ (by simp)⟩

private theorem wire_key (k r : Nat) (hk : k < 11) (hr : r < 21) : Key.wire k r ∈ keys := by
  by_cases h : k < 6
  · apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨k,List.mem_range.mpr h,List.mem_map.mpr ⟨r,List.mem_range.mpr hr,rfl⟩⟩
  · have he : k = 6 + (k-6) := by omega
    exact he ▸ (row_keys (k-6) r (by omega) hr).2.2

private theorem wire_out_id (g r : Nat) : (Key.wire (6+g) r).number = zId g r := by
  simp [Key.number,wireId]

theorem row_complete (t : Trace) (g r : Nat) (hg : g < 5) (hr : r < 21) :
    Holds (assignment t) (rowClauses g r) := by
  have hk := row_keys g r hg hr
  have A := signs t _ hk.1
  have B := signs t _ hk.2.1
  have Z := signs t _ hk.2.2
  rw [wire_out_id] at Z
  have O (i : Nat) (hi : i < 3) := (signs t _ (op_key g i hg hi)).2
  simp only [Key.number,Key.bit] at A B Z O
  intro c hc
  simp only [rowClauses,List.mem_append,List.mem_flatMap,List.mem_range,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with ⟨i,hi,h⟩ | h
  · have K := parent_keys g i hg hi
    have L := (signs t _ K.1).2
    have R := (signs t _ K.2).2
    have X := signs t _ (wire_key i r (by omega) hr)
    simp only [Key.number,Key.bit] at L R X
    rcases h with h|h|h|h <;> subst c <;>
      simp only [List.any_cons,List.any_nil,Bool.or_false,neg,L,R,A.1,A.2,B.1,B.2,X.1,X.2]
    all_goals by_cases hl : t.l g = i <;> by_cases hh : t.r g = i <;> simp [hl,hh]
  · have ev := t.eval g hg r hr
    have bound := t.op_lt g hg
    rcases h with h|h|h|h|h|h|h|h <;> subst c <;>
      simp only [List.any_cons,List.any_nil,Bool.or_false,neg,O 0 (by decide),O 1 (by decide),
        O 2 (by decide),A.1,A.2,B.1,B.2,Z.1,Z.2,ev]
    all_goals rcases (show t.op g = 0 ∨ t.op g = 1 ∨ t.op g = 2 by omega) with op|op|op <;>
      cases ha : t.value (t.l g) r <;> cases hb : t.value (t.r g) r <;> simp [op,ha,hb]

#print axioms row_complete

theorem gate_complete (t : Trace) (g : Nat) (hg : g < 5) :
    Holds (assignment t) (gateClauses g) := by
  have sel := selector_blocks t g hg
  intro c hc
  simp only [gateClauses,List.mem_append] at hc
  rcases hc with (((hl|hr)|ho)|hop)|hrow
  · exact sel.1 c hl
  · exact sel.2.1 c hr
  · obtain ⟨i,hi,hm⟩ := List.mem_flatMap.mp ho
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hm
    simp only [List.mem_range] at hi hj
    have L := (signs t _ (parent_keys g i hg hi).1).2
    have R := (signs t _ (parent_keys g j hg (by omega)).2).2
    simp only [Key.number,Key.bit] at L R
    have ord := t.left_le g hg
    simp only [List.any_cons,List.any_nil,Bool.or_false,neg,L,R,Bool.or_eq_true,
      Bool.not_eq_true',decide_eq_false_iff_not]
    omega
  · exact sel.2.2 c hop
  · obtain ⟨r,hr,hm⟩ := List.mem_flatMap.mp hrow
    exact row_complete t g r hg (List.mem_range.mp hr) c hm

private theorem unit_ok (t : Trace) (k r : Nat) (v : Bool) (hk : k < 11) (hr : r < 21)
    (hv : t.value k r = v) :
    (unit (wireId k r) v).any (litValue (assignment t)) = true := by
  have H := signs t _ (wire_key k r hk hr)
  simp only [Key.number,Key.bit,hv] at H
  cases v <;> simp [unit,neg,H.1,H.2]

/-- A consistent five-gate trace on the 21 promised inputs supplies one assignment
satisfying every clause of the independently reconstructed DIMACS. -/
theorem trace_satisfies (t : Trace) : Holds (assignment t) encoded := by
  intro c hc
  simp only [encoded,List.mem_append] at hc
  rcases hc with (hin|hg)|hout
  · obtain ⟨k,hk,hm⟩ := List.mem_flatMap.mp hin
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hm
    have k6 := List.mem_range.mp hk
    have r21 := List.mem_range.mp hr
    exact unit_ok t k r _ (by omega) r21 (t.input k k6 r r21)
  · obtain ⟨g,hg,hm⟩ := List.mem_flatMap.mp hg
    exact gate_complete t g (List.mem_range.mp hg) c hm
  · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hout
    have r21 := List.mem_range.mp hr
    exact unit_ok t 10 r _ (by decide) r21 (t.output r r21)

#print axioms trace_satisfies

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem nonzero : ∀ c ∈ encoded, ∀ z ∈ c, z ≠ 0 := by decide +kernel

open Std.Sat

/-- Shift DIMACS numbers to Lean's zero-based variables. -/
theorem trace_model (t : Trace) : formula.eval (fun k => assignment t (k+1)) = true := by
  unfold formula CNF.eval
  apply Array.all_eq_true_iff_forall_mem.mpr
  intro cl hcl
  obtain ⟨c,hc,rfl⟩ := Array.mem_map.mp hcl
  have hc' : c ∈ encoded := by simpa using hc
  obtain ⟨z,hz,hv⟩ := List.any_eq_true.mp (trace_satisfies t c hc')
  simp only [CNF.Clause.eval,CNF.Clause.literals_ofLiterals,List.any_map]
  apply List.any_eq_true.mpr
  refine ⟨z,hz,?_⟩
  have nz := nonzero c hc' z hz
  have shift : z.natAbs-1+1 = z.natAbs := by
    have : 0 < z.natAbs := Int.natAbs_pos.mpr nz
    omega
  change (assignment t (z.natAbs-1+1) == decide (z > 0)) = true
  rw [shift]
  by_cases h : z > 0 <;> simpa [litValue,h] using hv

theorem no_trace_of_unsat (hu : formula.Unsat) : IsEmpty Trace := by
  constructor
  intro t
  have h := hu (fun k => assignment t (k+1))
  rw [trace_model] at h
  contradiction

#print axioms no_trace_of_unsat
end Alexrollo64.FiveGateCNF
