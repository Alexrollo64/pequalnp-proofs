import DisjointCopies

namespace Alexrollo64.TreeCopies

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open Alexrollo64.DisjointCopies (graph vertex)
open Alexrollo64.PaddedRows (one_read step)
open Alexrollo64.Support20782 (target mask31917056_lower)

/-- Binary monotone formulas. Every occurrence of a subtree is counted. -/
inductive Tree where
  | leaf (i : Nat)
  | node (isAnd : Bool) (left right : Tree)

def op (p x y : Bool) := if p then x && y else x || y

def eval (x : Nat → Bool) : Tree → Bool
  | .leaf i => x i
  | .node p a b => op p (eval x a) (eval x b)

def leaves : Tree → List Nat
  | .leaf i => [i]
  | .node _ a b => leaves a ++ leaves b

def cost : Tree → Nat
  | .leaf _ => 0
  | .node _ a b => cost a + cost b + 1

theorem length_leaves (t : Tree) : (leaves t).length = cost t + 1 := by
  induction t <;> simp_all [leaves,cost] <;> omega

/-- The index of the result after compiling the tree at the given offset. -/
def out (base : Nat) : Tree → Nat
  | .leaf i => i
  | .node _ a b => base + cost a + cost b

def code (base : Nat) : Tree → List Gate
  | .leaf _ => []
  | .node p a b => code base a ++ code (base+cost a) b ++
      [⟨if p then .and else .or, [out base a,out (base+cost a) b]⟩]

theorem length_code (t : Tree) (n : Nat) : (code n t).length = cost t := by
  induction t generalizing n <;> simp_all [code,cost,Nat.add_assoc]

theorem legal (t : Tree) (n : Nat) (g : Gate) (h : g ∈ code n t) :
    g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction t generalizing n with
  | leaf => simp [code] at h
  | node p a b ia ib =>
    simp only [code,List.mem_append,List.mem_singleton] at h
    rcases h with (h|h)|rfl
    · exact ia _ h
    · exact ib _ h
    · cases p <;> simp

theorem run_code (t : Tree) (w : List Bool) (x : Nat → Bool)
    (ok : ∀ i ∈ leaves t, i < w.length ∧ w.getD i false = x i) :
    ∃ zs, zs.length = cost t ∧
      (code w.length t).foldl step w = w ++ zs ∧
      (w ++ zs).getD (out w.length t) false = eval x t ∧ out w.length t < (w ++ zs).length := by
  induction t generalizing w with
  | leaf i =>
    have h := ok i (by simp [leaves])
    exact ⟨[],rfl,by simp [code],by simpa [out,eval] using h.2,by simpa [out] using h.1⟩
  | node p a b ia ib =>
    obtain ⟨as,ha,ra,va,oa⟩ := ia w (fun i hi => ok i (by simp [leaves,hi]))
    obtain ⟨bs,hb,rb,vb,_⟩ := ib (w++as) (by
      intro i hi
      have h := ok i (by simp [leaves,hi])
      exact ⟨by simp; omega, (List.getD_append _ _ _ _ h.1).trans h.2⟩)
    have len : (w++as).length = w.length + cost a := by simp [ha]
    rw [len] at rb vb
    have prev := (List.getD_append _ bs _ _ oa).trans va
    let val := op p (eval x a) (eval x b)
    have go : (code w.length (.node p a b)).foldl step w = w ++ (as ++ bs ++ [val]) := by
      simp only [code,List.foldl_append,List.foldl_cons,List.foldl_nil,ra,rb,step,List.map_cons,
        List.map_nil,prev,vb]
      cases p <;> simp [GateOp.eval,val,op,List.append_assoc]
    refine ⟨as++bs++[val],by simp [cost,ha,hb,Nat.add_assoc],go,?_,?_⟩
    · simp only [out,eval]
      rw [← List.append_assoc,← List.append_assoc]
      rw [List.getD_append_right _ _ _ _ (by simp [ha,hb]; omega)]
      simp [val,ha,hb,Nat.add_assoc]
    · simp [out,ha,hb]; omega

def collapse (p : Bool) : Option Tree → Option Tree → Option Tree
  | some a,some b => some (.node p a b)
  | a,b => if p then none else a.or b

/-- Omitted wires evaluate to false on the restricted promise. -/
def restrict (m : Nat → Option Nat) : Tree → Option Tree
  | .leaf i => (m i).map Tree.leaf
  | .node p a b => collapse p (restrict m a) (restrict m b)

def valOpt (x : Nat → Bool) : Option Tree → Bool
  | none => false
  | some t => eval x t

theorem restrict_eval (m : Nat → Option Nat) (t : Tree) (x : Nat → Bool) :
    valOpt x (restrict m t) = eval (fun i => ((m i).map x).getD false) t := by
  induction t with
  | leaf i => cases h : m i <;> simp [restrict,h,valOpt,eval]
  | node p a b ia ib =>
    simp only [restrict,eval,← ia,← ib]
    cases p <;> cases restrict m a <;> cases restrict m b <;> simp [collapse,op,eval,valOpt]

def optLeaves : Option Tree → List Nat
  | none => []
  | some t => leaves t

theorem sublist (m : Nat → Option Nat) (t : Tree) :
    (optLeaves (restrict m t)).Sublist ((leaves t).filterMap m) := by
  induction t with
  | leaf i => cases h : m i <;> simp [restrict,h,optLeaves,leaves]
  | node p a b ia ib =>
    simp only [restrict,leaves,List.filterMap_append]
    cases p <;> cases ha : restrict m a <;> cases hb : restrict m b <;>
      simp [ha,hb,optLeaves,collapse,leaves] at ia ib ⊢ <;>
      first | exact ia.append ib | exact ia.trans (List.sublist_append_left ..) |
        exact ib.trans (List.sublist_append_right ..) | assumption

def owner (k i : Nat) := if i < 5*k then i/5 else (i-5*k)/5

def project {k : Nat} (b : Fin k) (i : Nat) : Option Nat :=
  if owner k i = b.val ∧ i < 10*k then
    some (if i < 5*k then i%5 else 5+(i-5*k)%5)
  else none

theorem project_read {k : Nat} (b : Fin k) (u v : Fin 5) (i : Nat) :
    ((project b i).map (fun j => (oneEach u v).getD j false)).getD false =
      (oneEach (vertex b u) (vertex b v)).getD i false := by
  have rowDiv : (5*b.val+u.val)/5 = b.val := by omega
  have colDiv : (5*k+(5*b.val+v.val)-5*k)/5 = b.val := by omega
  simp only [project,owner,vertex,one_read,Fin.val_mk]
  split_ifs <;> simp_all only [Option.map_some,Option.getD_some,Option.map_none,Option.getD_none]
  all_goals apply Bool.eq_iff_iff.mpr <;> simp only [Bool.or_eq_true,decide_eq_true_eq,Bool.false_eq_true] <;> try omega
  all_goals constructor
  all_goals first | exact False.elim | (rintro (rfl|rfl) <;> omega)

def realizes (k : Nat) (t : Tree) : Prop := ∀ u v : Fin (5*k),
  eval (fun i => (oneEach u v).getD i false) t = graph k u v

theorem nine_in_block {k : Nat} (b : Fin k) (t : Tree) (ht : realizes k t) :
    9 ≤ ((leaves t).filterMap (project b)).length := by
  have correct (u v : Fin 5) :
      valOpt (fun i => (oneEach u v).getD i false) (restrict (project b) t) = target u v := by
    rw [restrict_eval]
    simp_rw [project_read]
    exact (ht _ _).trans (DisjointCopies.same_block _ _ _)
  cases h : restrict (project b) t with
  | none =>
    have hc := correct 2 0
    rw [h] at hc
    exact False.elim ((by decide : false ≠ target 2 0) hc)
  | some a =>
    have sub := sublist (project b) t
    rw [h] at sub
    change (leaves a).Sublist _ at sub
    have bound : ∀ i ∈ leaves a, i < 10 := by
      intro i hi
      obtain ⟨j,_,eq⟩ := List.mem_filterMap.mp (sub.subset hi)
      unfold project at eq
      split_ifs at eq <;> simp_all <;> omega
    have big : 8 ≤ cost a := by
      by_contra! small
      apply mask31917056_lower
      refine ⟨⟨code 10 a,out 10 a⟩,legal a 10,by change (code 10 a).length ≤ 7; rw [length_code]; omega,?_⟩
      intro u v
      let w := oneEach u v
      have len : w.length = 10 := by simp [w,oneEach]
      obtain ⟨zs,_,run,result,_⟩ := run_code a w (fun i => w.getD i false)
        (fun i hi => ⟨len ▸ bound i hi,rfl⟩)
      rw [len] at run result
      change ((code 10 a).foldl step w).getD (out 10 a) false = _
      rw [run]
      have hc := correct u v
      rw [h] at hc
      exact result.trans hc
    have := sub.length_le
    rw [length_leaves] at this
    omega

theorem partition_le (k : Nat) (l : List Nat) :
    (∑ b : Fin k, (l.filterMap (project b)).length) ≤ l.length := by
  induction l with
  | nil => simp
  | cons i l ih =>
    by_cases hv : i < 10*k
    · have ho : owner k i < k := by unfold owner; split <;> omega
      let c : Fin k := ⟨owner k i,ho⟩
      have each (b : Fin k) : ((i::l).filterMap (project b)).length =
          (l.filterMap (project b)).length + (if b = c then 1 else 0) := by
        by_cases hb : b = c
        · subst b; simp [List.filterMap_cons,project,c,hv]
        · have hn : owner k i ≠ b.val := fun e => hb (Fin.ext e.symm)
          simp [List.filterMap_cons,project,hb,hn]
      simp_rw [each,Finset.sum_add_distrib]
      simp; omega
    · have each (b : Fin k) : ((i::l).filterMap (project b)).length =
          (l.filterMap (project b)).length := by simp [List.filterMap_cons,project,hv]
      simp_rw [each]
      simp; omega

theorem formula_lower {k : Nat} (t : Tree) (ht : realizes k t) : 9*k ≤ cost t + 1 := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin k))) (fun b _ => nine_in_block b t ht)
  have hp := partition_le k (leaves t)
  simpa [length_leaves,Nat.mul_comm] using h.trans hp

#print axioms formula_lower
/-- The eight-gate formula for one block with separately supplied row/column leaves. -/
def gadget (r c : Nat → Tree) : Tree :=
  .node false
    (.node false
      (.node true (.node false (r 3) (r 4)) (.node false (.node false (c 1) (c 2)) (c 3)))
      (.node true (r 4) (c 4)))
    (.node true (r 2) (c 0))

def block (k b : Nat) := gadget (fun i => .leaf (5*b+i)) (fun j => .leaf (5*k+5*b+j))

def blockVal (r c : Nat → Bool) :=
  (((r 3 || r 4) && ((c 1 || c 2) || c 3)) || (r 4 && c 4)) || (r 2 && c 0)

theorem local_truth : ∀ (x y : Fin 5) (p q : Bool),
    blockVal (fun j => p && decide (j = x.val)) (fun j => q && decide (j = y.val)) =
    ((p && q) && target x y) := by decide +kernel

theorem block_eval {k : Nat} (b : Fin k) (u v : Fin (5*k)) :
    eval (fun i => (oneEach u v).getD i false) (block k b.val) =
    (decide (b.val = u.val/5 ∧ b.val = v.val/5) &&
      target ⟨u.val%5,by omega⟩ ⟨v.val%5,by omega⟩) := by
  let x : Fin 5 := ⟨u.val%5,by omega⟩
  let y : Fin 5 := ⟨v.val%5,by omega⟩
  have rr (j : Nat) (h : j < 5) : (oneEach u v).getD (5*b.val+j) false =
      (decide (b.val = u.val/5) && decide (j = x.val)) := by
    rw [one_read]; apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,x]; omega
  have cc (j : Nat) (h : j < 5) : (oneEach u v).getD (5*k+5*b.val+j) false =
      (decide (b.val = v.val/5) && decide (j = y.val)) := by
    rw [one_read]; apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,y]; omega
  simp only [block,gadget,eval,op,Bool.false_eq_true,ite_true,ite_false]
  simp only [rr _ (by decide : 3 < 5),rr _ (by decide : 4 < 5),rr _ (by decide : 2 < 5),
    cc _ (by decide : 0 < 5),cc _ (by decide : 1 < 5),cc _ (by decide : 2 < 5),
    cc _ (by decide : 3 < 5),cc _ (by decide : 4 < 5)]
  convert local_truth x y (decide (b.val = u.val/5)) (decide (b.val = v.val/5)) using 1 <;> simp [blockVal]

/-- The OR of the first n+1 block formulas. -/
def chain (k : Nat) : Nat → Tree
  | 0 => block k 0
  | n+1 => .node false (chain k n) (block k (n+1))

theorem chain_cost (k n : Nat) : cost (chain k n) = 9*n+8 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change cost (chain k n) + 8 + 1 = _
    omega

theorem chain_eval (k n : Nat) (hn : n < k) (u v : Fin (5*k)) :
    eval (fun i => (oneEach u v).getD i false) (chain k n) =
    (decide (u.val/5 ≤ n) && graph k u v) := by
  induction n with
  | zero =>
    rw [chain,block_eval (⟨0,hn⟩ : Fin k)]
    apply Bool.eq_iff_iff.mpr
    simp only [graph,target,Bool.and_eq_true,decide_eq_true_eq,Fin.val_mk]
    constructor
    · rintro ⟨⟨h1,h2⟩,h3⟩; exact ⟨by omega,by omega,h3⟩
    · rintro ⟨h1,h2,h3⟩; exact ⟨⟨by omega,by omega⟩,h3⟩
  | succ n ih =>
    simp only [chain,eval,op,Bool.false_eq_true,ite_false]
    rw [ih (by omega),block_eval (⟨n+1,hn⟩ : Fin k)]
    apply Bool.eq_iff_iff.mpr
    simp only [graph,target,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,Fin.val_mk]
    grind

theorem optimum_tree (k : Nat) (hk : 0 < k) :
    ∃ t, realizes k t ∧ cost t + 1 = 9*k := by
  refine ⟨chain k (k-1),?_,?_⟩
  · intro u v
    rw [chain_eval k _ (by omega)]
    have h : u.val/5 ≤ k-1 := by omega
    simp [h]
  · rw [chain_cost]; omega

#print axioms optimum_tree
end Alexrollo64.TreeCopies
