import PEqualNP.Defs.MetaComplexity
import ConstantPropagation
import TwoLitTables

namespace Alexrollo64.SynthesisNormalForm
open PEqualNP.CircuitLowerBounds
open Alexrollo64.ConstantPropagation Alexrollo64.TwoLitTables

theorem fits_take (gs : List Gate) (n k : Nat) (h : FitsFrom n gs) :
    FitsFrom n (gs.take k) := by
  induction gs generalizing n k with
  | nil => simp [FitsFrom]
  | cons g gs ih =>
    cases k with
    | zero => trivial
    | succ k => exact ⟨h.1,ih _ _ h.2⟩

theorem fits_snoc (gs : List Gate) (n : Nat) (g : Gate)
    (h : FitsFrom n gs) (hg : fits (n + gs.length) g) : FitsFrom n (gs ++ [g]) := by
  induction gs generalizing n with
  | nil => exact ⟨by simpa using hg, trivial⟩
  | cons a gs ih =>
    refine ⟨h.1, ih (n+1) h.2 ?_⟩
    convert hg using 1; simp [Nat.add_comm,Nat.add_left_comm]

theorem pad_fits (C : Circuit) (n b : Nat) (hs : C.size ≤ b)
    (last : C.output + 1 = n + C.size) (hf : FitsFrom n C.gates) :
    ∃ D : Circuit, D.size = b ∧ D.output + 1 = n+b ∧ FitsFrom n D.gates ∧
      ∀ x : List Bool, x.length = n → D.eval x = C.eval x := by
  induction b, hs using Nat.le_induction with
  | base => exact ⟨C,rfl,last,hf,fun _ _ => rfl⟩
  | succ b _ ih =>
    obtain ⟨D,sz,out,fit,eq⟩ := ih
    refine ⟨appendCopy n D, ?_, ?_, ?_,fun x hx => (appendCopy_eval n D x hx).trans (eq x hx)⟩
    · change (D.gates ++ [_]).length = _
      simpa [Circuit.size] using sz
    · change n+D.size+1 = n+(b+1)
      omega
    · apply fits_snoc _ _ _ fit
      exact Or.inr ⟨D.output,D.output,le_rfl,by change D.output < n+D.size; omega,Or.inl rfl,rfl⟩

def bounded (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

/-- Exact-budget, sorted-parent, last-output form, with one unary or one binary
operation per gate. Evaluation on every length-six input is preserved. -/
theorem normalize (C : Circuit) (t : Nat × Nat) (ht : t ∈ targets)
    (b : Nat) (small : C.size ≤ b) (ops : bounded C)
    (solves : ∀ r, C.eval (List.ofFn (packedInput r)) = t.2.testBit r.val) :
    ∃ D : Circuit, D.size = b ∧ D.output + 1 = 6+b ∧ FitsFrom 6 D.gates ∧
      ∀ x : List Bool, x.length = 6 → D.eval x = C.eval x := by
  obtain ⟨r,s,hr,hs⟩ := targets_nonconstant t ht
  have nc : ∃ x y : List Bool, x.length = 6 ∧ y.length = 6 ∧ C.eval x ≠ C.eval y := by
    refine ⟨List.ofFn (packedInput r),List.ofFn (packedInput s),List.length_ofFn, List.length_ofFn,?_⟩
    rw [solves r,solves s,hr,hs]
    decide
  obtain ⟨i,sz,eq⟩ := eliminate_constants C 6 ops nc
  let E : Circuit := ⟨(translate 6 (inputs 6) C.gates).gates,i⟩
  have ef : FitsFrom 6 E.gates := translate_fits _ _ _ (inputs_valid 6)
  have es (r : Fin 21) : E.eval (List.ofFn (packedInput r)) = _ :=
    (eq _ List.length_ofFn).trans (solves r)
  obtain ⟨lo,hi⟩ := output_is_gate E t ht es
  obtain ⟨F,le,last,pre,fe⟩ := truncate_output E 6 lo hi
  have ff : FitsFrom 6 F.gates := pre ▸ fits_take _ _ _ ef
  obtain ⟨D,ds,dl,df,de⟩ := pad_fits F 6 b (le.trans (sz.trans small)) last ff
  exact ⟨D,ds,dl,df,fun x hx => (de x hx).trans ((fe x hx).trans (eq x hx))⟩

#print axioms normalize

theorem fits_bounded (gs : List Gate) (n : Nat) (hf : FitsFrom n gs) :
    ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
  induction gs generalizing n with
  | nil => simp
  | cons a gs ih =>
    intro g hg
    rcases List.mem_cons.mp hg with rfl | h
    · rcases hf.1 with ⟨i,_,hop,hins⟩ | ⟨i,j,_,_,hop,hins⟩
      · simp [hop,hins]
      · rcases hop with hop | hop <;> simp [hop,hins]
    · exact ih _ hf.2 _ h

/-- The left side uses precisely the posted pair specification and project fan-in predicate.
The right side is the structural search space, prior to assigning propositional variables. -/
theorem structural_iff (t : Nat × Nat) (ht : t ∈ targets) (b : Nat) :
    (∃ C : Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ b ∧
      ∀ i j : Fin 6, C.eval (List.ofFn (fun k => decide (k = i ∨ k = j))) =
      t.1.testBit (6 * min i.val j.val + max i.val j.val)) ↔
    (∃ D : Circuit, FitsFrom 6 D.gates ∧ D.size = b ∧ D.output + 1 = 6+b ∧
      ∀ r : Fin 21, D.eval (List.ofFn (packedInput r)) = t.2.testBit r.val) := by
  constructor
  · rintro ⟨C,fan,sz,sol⟩
    have h := (circuit_specification_iff C t ht).mp sol
    have ops : bounded C := by
      simpa only [bounded,PEqualNP.MetaComplexity.FanInTwo,Set.mem_insert_iff,Set.mem_singleton_iff] using fan
    obtain ⟨D,ds,last,hf,eq⟩ := normalize C t ht b sz ops h
    exact ⟨D,hf,ds,last,fun r => (eq _ List.length_ofFn).trans (h r)⟩
  · rintro ⟨D,hf,ds,_,h⟩
    have fan : PEqualNP.MetaComplexity.FanInTwo D := by
      simpa only [PEqualNP.MetaComplexity.FanInTwo,Set.mem_insert_iff,Set.mem_singleton_iff] using fits_bounded _ _ hf
    exact ⟨D,fan,ds.le,(circuit_specification_iff D t ht).mpr h⟩

#print axioms structural_iff
end Alexrollo64.SynthesisNormalForm
