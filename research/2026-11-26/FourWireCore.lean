import TreeCopies

namespace Alexrollo64.FourWireCore
open Alexrollo64.TreeCopies

/-- Six settings of row 3, row 4, column 1 and column 4, in that bit order.
    The target accepts the settings 5, 6 and 10. -/
def weights (x : BitVec 6) : Nat := (227894251691170633201912427355916679805083015163827104616 >>> (3*x.toNat)) % 8
def bits : Fin 4 → BitVec 6 := ![20,41,14,48]
def wanted : BitVec 6 := 44

theorem laws : ∀ a b : BitVec 6, weights (a &&& b) ≤ weights a + weights b ∧
    weights (a ||| b) ≤ weights a + weights b := by decide +kernel
theorem values : weights wanted = 5 ∧ (∀ j, weights (bits j) = 1) ∧
    weights 0 = 0 ∧ weights 63 = 0 := by decide +kernel

def run (x : Nat → BitVec 6) : Tree → BitVec 6
  | .leaf j => x j
  | .node isAnd l r => if isAnd then run x l &&& run x r else run x l ||| run x r

theorem bound (t : Tree) (x : Nat → BitVec 6) :
    weights (run x t) ≤ ((leaves t).map (fun j => weights (x j))).sum := by
  induction t with
  | leaf j => simp [run,leaves]
  | node p l r hl hr =>
    have h := laws (run x l) (run x r)
    cases p <;> simp [run,leaves] <;> omega

/-- Constants are free. Four occurrences of cost-one leaf patterns cannot
    produce the six prescribed outputs. -/
theorem obstruction (t : Tree) (x : Nat → BitVec 6)
    (budget : ((leaves t).map (fun j => weights (x j))).sum ≤ 4) : run x t ≠ wanted := by
  intro e
  have h := bound t x
  rw [e,values.1] at h
  omega

/-- Clamping a shared input down preserves all six outputs whenever the
    clamp agrees on the three positive cells.  `lo` and `hi` are assignments
    of six-column signatures to the input occurrences of the outer tree. -/
theorem run_le (t : Tree) (lo hi : Nat → BitVec 6) (i : Nat)
    (h : ∀ j, (lo j).getLsbD i = true → (hi j).getLsbD i = true) :
    (run lo t).getLsbD i = true → (run hi t).getLsbD i = true := by
  induction t with
  | leaf j => exact h j
  | node p l r hl hr =>
    cases p <;> simp only [run, Bool.false_eq_true, ite_false, ite_true,
      BitVec.getLsbD_and, BitVec.getLsbD_or, Bool.and_eq_true, Bool.or_eq_true] <;> tauto

theorem clamped_obstruction (t : Tree) (lo hi : Nat → BitVec 6)
    (lower : ∀ i j, (lo j).getLsbD i = true → (hi j).getLsbD i = true)
    (positive : ∀ i, wanted.getLsbD i = true → ∀ j,
      (hi j).getLsbD i = true → (lo j).getLsbD i = true)
    (budget : ((leaves t).map (fun j => weights (lo j))).sum ≤ 4) :
    run hi t ≠ wanted := by
  intro correct
  apply obstruction t lo budget
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  by_cases w : wanted.getLsbD i = true
  · have h := run_le t hi lo i (positive i w)
    exact (h (correct ▸ w)).trans w.symm
  · have h := run_le t lo hi i (lower i)
    rw [correct] at h
    cases e : (run lo t).getLsbD i <;> cases f : wanted.getLsbD i <;> simp_all

#print axioms clamped_obstruction
#print axioms obstruction
end Alexrollo64.FourWireCore
