import CutTrees
import FourWireCore

namespace Alexrollo64.PositiveCore

open PEqualNP.CircuitLowerBounds PEqualNP.Represents
open Alexrollo64.TreeCopies Alexrollo64.DisjointCopies Alexrollo64.CutTrees
open Alexrollo64.FourWireCore (weights wanted run)

def row : Fin 6 → Fin 5 := ![4,0,3,4,3,4]
def col : Fin 6 → Fin 5 := ![0,1,1,1,4,4]
def cell (b : Fin 3) (i : Fin 6) := oneEach (vertex b (row i)) (vertex b (col i))
def raw (b : Fin 3) (i : Fin 6) (j : Nat) := (cell b i).getD j false

/-- Wires active on the positive cells: two rows and two columns. -/
def core (b : Fin 3) : Finset Nat :=
  {5*b.val+3,5*b.val+4,15+5*b.val+1,15+5*b.val+4}

def signature (b : Fin 3) (j : Nat) : BitVec 6 :=
  if j ∈ core b then BitVec.ofBoolListLE [raw b 0 j,raw b 1 j,raw b 2 j,raw b 3 j,raw b 4 j,raw b 5 j] else 0

theorem answers : ∀ (b : Fin 3) (i : Fin 6),
    graph 3 (vertex b (row i)) (vertex b (col i)) = wanted.getLsbD i.val := by decide +kernel

theorem pos_wires (b : Fin 3) (i : Fin 6) (hi : wanted.getLsbD i.val = true)
    (j : Nat) (hj : raw b i j = true) : j ∈ core b := by
  by_cases lt : j < 30
  · exact (by decide +kernel : ∀ (b : Fin 3) (i : Fin 6) (j : Fin 30),
      wanted.getLsbD i.val = true → raw b i j.val = true → j.val ∈ core b) b i ⟨j,lt⟩ hi hj
  · have z : raw b i j = false := by apply List.getD_eq_default; simp [cell,oneEach]; omega
    simp_all

theorem bit_run (t : Tree) (f : Nat → BitVec 6) (i : Fin 6) :
    (run f t).getLsbD i.val = eval (fun j => (f j).getLsbD i.val) t := by
  induction t with
  | leaf => rfl
  | node p l r hl hr => cases p <;> simp only [run,eval,op,Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or,hl,hr]

theorem mono (t : Tree) (x y : Nat → Bool)
    (h : ∀ j ∈ leaves t, x j = true → y j = true) : eval x t = true → eval y t = true := by
  induction t with
  | leaf j => exact h j (by simp [leaves])
  | node p l r hl hr =>
    have a := hl (fun j hj => h j (by simp [leaves,hj]))
    have d := hr (fun j hj => h j (by simp [leaves,hj]))
    cases p <;> simp [eval,op] <;> tauto

def total (b : Fin 3) (m : Multiset Nat) := (m.map (fun j => weights (signature b j))).sum

theorem core_budget (b : Fin 3) (inner outer : Tree)
    (cover : footprint inner + footprint outer = CommonThree.requiredThree.val + {54} + {54}) :
    ((leaves outer).map (fun j => weights (signature b j))).sum ≤ 4 := by
  have h := congrArg (total b) cover
  have four : ∀ b : Fin 3, total b (CommonThree.requiredThree.val + {54} + {54}) = 4 := by decide +kernel
  rw [four] at h
  simp only [total,Multiset.map_add,Multiset.sum_add] at h
  change _ + ((leaves outer).map (fun j => weights (signature b j))).sum = 4 at h
  omega

theorem signature_on (b : Fin 3) (i : Fin 6) (j : Nat) : (signature b j).getLsbD i.val = true ↔ j ∈ core b ∧ raw b i j = true := by
    by_cases mem : j ∈ core b
    · have q : ∀ (b : Fin 3) (j : Fin 30) (i : Fin 6), j.val ∈ core b →
          (signature b j.val).getLsbD i.val = raw b i j.val := by decide +kernel
      have lt : j < 30 := by simp [core] at mem; rcases mem with h|h|h|h <;> omega
      simp only [q b ⟨j,lt⟩ i mem,mem,true_and]
    · simp [signature,mem]

theorem core_hit (inner outer : Tree)
    (cover : footprint inner + footprint outer = CommonThree.requiredThree.val + {54} + {54})
    (faithful : ∀ (b : Fin 3) (i : Fin 6),
      eval (Function.update (raw b i) 54 (eval (raw b i) inner)) outer = wanted.getLsbD i.val)
    (b : Fin 3) : ∃ i : Fin 6, wanted.getLsbD i.val = true ∧ eval (raw b i) inner = true := by
  by_contra! off
  apply FourWireCore.obstruction outer (signature b) (core_budget b inner outer cover)
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  let i : Fin 6 := ⟨k,hk⟩
  change (run (signature b) outer).getLsbD i.val = wanted.getLsbD i.val
  rw [bit_run]
  let lo := fun j => (signature b j).getLsbD i.val
  let hi := Function.update (raw b i) 54 (eval (raw b i) inner)
  have act := signature_on b i
  have valid := faithful b i
  change eval hi outer = _ at valid
  change eval lo outer = _
  have lower : eval lo outer = true → eval hi outer = true := by
    apply mono
    intro j _ on
    obtain ⟨m,v⟩ := (act j).mp on
    have ne : j ≠ 54 := by
      intro e; subst j; exact (by decide +kernel : ∀ b : Fin 3, 54 ∉ core b) b m
    simpa [hi,Function.update_of_ne ne] using v
  by_cases p : wanted.getLsbD i.val = true
  · have back : eval hi outer = true → eval lo outer = true := by
      apply mono
      intro j _ on
      by_cases e : j = 54
      · subst j; simp [hi,off i p] at on
      · have v : raw b i j = true := by simpa [hi,Function.update_of_ne e] using on
        exact (act j).mpr ⟨pos_wires b i p j v,v⟩
    exact (back (valid.trans p)).trans p.symm
  · cases h : eval lo outer <;> cases q : wanted.getLsbD i.val <;> simp_all

theorem leaf_hit (t : Tree) (x : Nat → Bool) (h : eval x t = true) :
    ∃ j ∈ leaves t, x j = true := by
  induction t with
  | leaf j => exact ⟨j,by simp [leaves],h⟩
  | node p l r hl hr =>
    have either : eval x l = true ∨ eval x r = true := by cases p <;> simp [eval,op] at h <;> tauto
    rcases either with a|a
    · obtain ⟨j,m,v⟩ := hl a; exact ⟨j,by simp [leaves,m],v⟩
    · obtain ⟨j,m,v⟩ := hr a; exact ⟨j,by simp [leaves,m],v⟩

theorem candidate_hits (c : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 c)
    (hr : Represents (graph 3) c) (hs : c.size ≤ 24) :
    ∃ inner outer : Tree,
      footprint inner + footprint outer = CommonThree.requiredThree.val + {54} + {54} ∧
      (∀ w : List Bool, w.length = 30 →
        let x := fun j => w.getD j false
        eval (Function.update x 54 (eval x inner)) outer = c.eval w) ∧
      ∀ b : Fin 3, ∃ j ∈ leaves inner, j ∈ core b := by
  obtain ⟨inner,outer,_,cover,sem⟩ := decompose c hm hr hs
  refine ⟨inner,outer,cover,sem,?_⟩
  intro b
  have faithful (d : Fin 3) (i : Fin 6) := (sem (cell d i) (by simp [cell,oneEach])).trans
    ((hr (vertex d (row i)) (vertex d (col i))).trans (answers d i))
  obtain ⟨i,pos,on⟩ := core_hit inner outer cover faithful b
  obtain ⟨j,mem,lit⟩ := leaf_hit inner _ on
  exact ⟨j,mem,pos_wires b i pos j lit⟩

#print axioms candidate_hits

def signalOnly (j : Nat) := decide (j = 54)

/-- If the marker alone makes the outer formula true, composition on these
    cells reduces to the OR of the two formulas with the marker held low. -/
theorem marker_insufficient (inner outer : Tree)
    (cover : footprint inner + footprint outer = CommonThree.requiredThree.val + {54} + {54})
    (faithful : ∀ (b : Fin 3) (i : Fin 6),
      eval (Function.update (raw b i) 54 (eval (raw b i) inner)) outer = wanted.getLsbD i.val) :
    eval signalOnly outer ≠ true := by
  intro alone
  let b : Fin 3 := 0
  let t : Tree := .node false inner outer
  have budget : ((leaves t).map (fun j => weights (signature b j))).sum ≤ 4 := by
    have h := congrArg (total b) cover
    have four : total b (CommonThree.requiredThree.val + {54} + {54}) = 4 := by decide +kernel
    rw [four] at h
    simp only [total,Multiset.map_add,Multiset.sum_add] at h
    change ((leaves inner).map (fun j => weights (signature b j))).sum + ((leaves outer).map (fun j => weights (signature b j))).sum = 4 at h
    simpa only [t,leaves,List.map_append,List.sum_append] using Nat.le_of_eq h
  apply FourWireCore.obstruction t (signature b) budget
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  let i : Fin 6 := ⟨k,hk⟩
  have faith := faithful b i
  have flat : eval (raw b i) t = wanted.getLsbD i.val := by
    cases e : eval (raw b i) inner with
    | false =>
      have z : raw b i 54 = false := by apply List.getD_eq_default; simp [cell,oneEach]
      have same : Function.update (raw b i) 54 false = raw b i := by rw [← z,Function.update_eq_self]
      simpa [t,eval,op,e,same] using (show eval (Function.update (raw b i) 54 (eval (raw b i) inner)) outer = _ from faith)
    | true =>
      have one : eval (Function.update (raw b i) 54 true) outer = true := by
        apply mono _ _ _ _ alone
        intro j _ lit; have eq : j = 54 := by simpa [signalOnly] using lit
        simp [eq]
      rw [e,one] at faith
      simpa [t,eval,op,e] using faith
  change (run _ t).getLsbD i.val = _
  rw [bit_run]
  let lo := fun j => (signature b j).getLsbD i.val
  change eval lo t = wanted.getLsbD i.val
  have lower := mono t lo (raw b i) (fun j _ hj => ((signature_on b i j).mp hj).2)
  by_cases pos : wanted.getLsbD i.val = true
  · have rev := mono t (raw b i) lo (fun j _ hj => (signature_on b i j).mpr ⟨pos_wires b i pos j hj,hj⟩)
    exact (rev (flat.trans pos)).trans pos.symm
  · cases e : eval lo t <;> cases q : wanted.getLsbD i.val <;> simp_all

theorem apart {inner outer : Tree}
    (cover : footprint inner + footprint outer = CommonThree.requiredThree.val + {54} + {54})
    {j : Nat} (ne : j ≠ 54) (inside : j ∈ leaves inner) : j ∉ leaves outer := by
  intro out
  have hi := Multiset.count_pos.mpr (show j ∈ footprint inner from inside)
  have ho := Multiset.count_pos.mpr (show j ∈ footprint outer from out)
  have eq := congrArg (Multiset.count j) cover
  have lim := Multiset.nodup_iff_count_le_one.mp CommonThree.requiredThree.nodup j
  simp [Multiset.count_add,ne] at eq
  omega

#print axioms marker_insufficient
end Alexrollo64.PositiveCore
