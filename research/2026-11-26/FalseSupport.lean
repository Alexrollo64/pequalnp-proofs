import TreeCopies

namespace Alexrollo64.FalseSupport

open PEqualNP.Represents Alexrollo64.TreeCopies
open Alexrollo64.DisjointCopies (graph)
open Alexrollo64.PaddedRows (one_read)

theorem monotone_eval (t : Tree) (x y : Nat → Bool)
    (le : ∀ i, x i = true → y i = true) : eval x t = true → eval y t = true := by
  induction t with
  | leaf i => exact le i
  | node p a b ha hb => cases p <;> simp [eval,op] <;> tauto

/-- If replacing signals by smaller ones preserves every positive input, the same
monotone formula still computes the target on its whole promised domain. -/
theorem substitute {D : Type} (f : D → Bool) (x y : D → Nat → Bool) (t : Tree)
    (correct : ∀ d, eval (y d) t = f d)
    (le : ∀ d i, x d i = true → y d i = true)
    (pos : ∀ d, f d = true → x d = y d) : ∀ d, eval (x d) t = f d := by
  intro d
  cases h : f d with
  | true => rw [pos d h,correct,h]
  | false =>
    have m := monotone_eval t _ _ (le d)
    rw [correct,h] at m
    cases e : eval (x d) t <;> simp_all

def raw {k : Nat} (u v : Fin (5*k)) (i : Nat) := (oneEach u v).getD i false

/-- Extra ports start after the raw row and column wires. Their off-target
truth sets may overlap and each port may occur arbitrarily often. -/
def ports {k : Nat} (s : Fin (5*k) → Fin (5*k) → Nat → Bool)
    (u v : Fin (5*k)) (i : Nat) := raw u v i || s u v i

theorem lower {k : Nat} (s : Fin (5*k) → Fin (5*k) → Nat → Bool) (t : Tree)
    (positive : ∀ u v, graph k u v = true → ∀ i, s u v i = false)
    (correct : ∀ u v, eval (ports s u v) t = graph k u v) : 9*k ≤ cost t + 1 := by
  apply formula_lower t
  intro u v
  exact substitute (D := Fin (5*k) × Fin (5*k)) (fun d => graph k d.1 d.2)
    (fun d => raw d.1 d.2) (fun d => ports s d.1 d.2) t
    (fun d => correct d.1 d.2) (fun d i h => by simp [ports,h])
    (fun d h => funext fun i => by simp [ports,positive _ _ h]) (u,v)

/-- One shared AND for any zero cell, including every cross-copy cell. -/
def cell {k : Nat} (a b u v : Fin (5*k)) (i : Nat) :=
  decide (i = 10*k ∧ u = a ∧ v = b)

theorem zero_cell {k : Nat} (a b : Fin (5*k)) (zero : graph k a b = false) (t : Tree)
    (correct : ∀ u v, eval (ports (cell a b) u v) t = graph k u v) :
    9*k ≤ 1 + cost t := by
  rw [Nat.add_comm]
  apply lower _ t _ correct
  intro u v pos i
  simp only [cell,decide_eq_false_iff_not]
  rintro ⟨_,rfl,rfl⟩
  simp_all

theorem gate_semantics {k : Nat} (a b u v : Fin (5*k)) :
    ports (cell a b) u v (10*k) = (raw u v a.val && raw u v (5*k+b.val)) := by
  simp only [ports,raw,cell,one_read]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,Fin.ext_iff]
  have ha := a.isLt
  have hb := b.isLt
  have hu := u.isLt
  have hv := v.isLt
  constructor <;> intro h <;> rcases h with (h|h) <;> first | omega | grind

end Alexrollo64.FalseSupport
