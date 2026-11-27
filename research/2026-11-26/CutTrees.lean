import WireUses
import TreeCopies

namespace Alexrollo64.CutTrees

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open Alexrollo64.WireUses Alexrollo64.TreeCopies

def cutMap (b : Nat → Tree) (cut marker i : Nat) :=
  if i = cut then Tree.leaf marker else b i

def nodeOf (g : Gate) (f : Nat → Tree) : Tree :=
  match g.inputs with
  | [a,b] => .node (match g.op with | .and => true | _ => false) (f a) (f b)
  | _ => .leaf 0

def builds (b : Nat → Tree) (cut marker n : Nat) : List Gate → Prop
  | [] => True
  | g::gs => b n = nodeOf g (cutMap b cut marker) ∧ builds b cut marker (n+1) gs

theorem node_congr (g : Gate) (f k : Nat → Tree) (h : ∀ i ∈ g.inputs, f i = k i) :
    nodeOf g f = nodeOf g k := by
  unfold nodeOf
  split <;> simp_all

theorem builder (gs : List Gate) (n cut marker : Nat) (initial : Nat → Tree)
    (early : earlier n gs) :
    ∃ b, (∀ i < n, b i = initial i) ∧ builds b cut marker n gs := by
  induction gs generalizing n initial with
  | nil => exact ⟨initial,fun _ _ => rfl,trivial⟩
  | cons g gs ih =>
    let u := Function.update initial n (nodeOf g (cutMap initial cut marker))
    obtain ⟨b,prev,rest⟩ := ih (n+1) u early.2
    have same (i : Nat) (lt : i < n) : b i = initial i := by
      rw [prev _ (by omega)]
      exact Function.update_of_ne (by omega) _ _
    refine ⟨b,same,?_,rest⟩
    calc
      b n = u n := prev _ (by omega)
      _ = nodeOf g (cutMap initial cut marker) := Function.update_self ..
      _ = _ := node_congr _ _ _ (fun i hi => by simp [cutMap,same i (early.1 i hi)])

def footprint (t : Tree) : Multiset Nat := ↑(leaves t)

theorem two_inputs (g : Gate) (card : g.inputs.toFinset.card = 2) (h : g.inputs.length ≤ 2) :
    ∃ a b, g.inputs = [a,b] := by
  have k := List.toFinset_card_le (l := g.inputs)
  match e : g.inputs with
  | [a,b] => exact ⟨a,b,rfl⟩
  | [] | [_] | _::_::_::_ => simp [e] at h k card

theorem as_labels (gs : List Gate) (n cut marker : Nat) (s : Finset Nat) (b : Nat → Tree)
    (reg : regular n gs s) (arity : ∀ g ∈ gs, g.inputs.length ≤ 2) (h : builds b cut marker n gs) :
    labeling (fun i => footprint (cutMap b cut marker i)) cut {marker} (footprint (b cut)) n gs := by
  induction gs generalizing n with
  | nil => trivial
  | cons g gs ih =>
    obtain ⟨a,z,inp⟩ := two_inputs g reg.2.1 (arity g (by simp))
    refine ⟨?_,ih _ reg.2.2 (fun x hx => arity x (by simp [hx])) h.2⟩
    have merge : (g.inputs : Multiset Nat).bind (fun i => footprint (cutMap b cut marker i)) =
        footprint (b n) := by
      rw [h.1,inp]
      simp only [nodeOf,inp,footprint,leaves]
      change (({a} + {z} : Multiset Nat).bind _) = _
      simp only [Multiset.add_bind,Multiset.singleton_bind]; rfl
    split_ifs with eq
    · subst cut; exact ⟨by simp [cutMap,footprint,leaves],merge⟩
    · simpa [cutMap,eq] using merge

theorem candidate_trees (c : Circuit) (hm : Monotone2 c) (hr : Represents (Alexrollo64.DisjointCopies.graph 3) c)
    (hs : c.size ≤ 24) :
    ∃ j b, 30 ≤ j ∧ j < 54 ∧ (∀ i < 30, b i = Tree.leaf i) ∧ builds b j 54 30 c.gates ∧
      footprint (b j) + footprint (cutMap b j 54 c.output) =
      CommonThree.requiredThree.val + {54} + {54} := by
  obtain ⟨j,lo,hi,leaves_eq⟩ := cut_leaves c hm hr hs
  obtain ⟨b,start,build⟩ := builder c.gates 30 j 54 Tree.leaf (candidate_earlier c hm hr hs)
  refine ⟨j,b,lo,hi,start,build,leaves_eq _ _ _ (as_labels _ _ _ _ _ _ (candidate_regular c hm hr hs)
    (fun g hg => (hm g hg).2) build) ?_ ?_⟩
  · intro i h
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp h
    have lt := (by decide +kernel : ∀ t : Fin 24, Alexrollo64.DisjointCopies.requiredWire 3 t < 30) t
    simp [cutMap,show Alexrollo64.DisjointCopies.requiredWire 3 t ≠ j by omega,start _ lt,footprint,leaves]
  · simp [cutMap,footprint,leaves]

#print axioms candidate_trees

open Alexrollo64.Support20782 (push read_other)

theorem eval_update (t : Tree) (raw : Nat → Bool) (marker : Nat) (v : Bool)
    (absent : marker ∉ leaves t) : eval (Function.update raw marker v) t = eval raw t := by
  induction t with
  | leaf i =>
    have ne : i ≠ marker := by simpa [leaves,eq_comm] using absent
    exact Function.update_of_ne ne _ _
  | node p l r hl hr =>
    simp only [leaves,List.mem_append,not_or] at absent
    simp only [eval,hl absent.1,hr absent.2]

/-- The tree computing the shared value has no occurrences of its own marker. -/
theorem marker_absent (gs : List Gate) (n cut marker : Nat) (s : Finset Nat) (b : Nat → Tree)
    (early : earlier n gs) (reg : regular n gs s)
    (arity : ∀ g ∈ gs, g.inputs.length ≤ 2) (h : builds b cut marker n gs)
    (old : ∀ i < n, i ≤ cut → marker ∉ leaves (b i)) :
    ∀ i < n+gs.length, i ≤ cut → marker ∉ leaves (b i) := by
  induction gs generalizing n with
  | nil => simpa using old
  | cons g gs ih =>
    have next (i : Nat) (hi : i < n+1) (hc : i ≤ cut) : marker ∉ leaves (b i) := by
      by_cases e : i = n
      · subst i
        obtain ⟨a,z,inp⟩ := two_inputs _ reg.2.1 (arity g (by simp))
        have aa := early.1 a (by simp [inp])
        have zz := early.1 z (by simp [inp])
        rw [h.1]
        simp [nodeOf,inp,leaves,cutMap,show a ≠ cut by omega,show z ≠ cut by omega,
          old a aa (by omega),old z zz (by omega)]
      · exact old i (by omega) hc
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1] using
      ih (n+1) early.2 reg.2.2 (fun k hk => arity k (by simp [hk])) h.2 next

theorem simulate (gs : List Gate) (n cut marker : Nat) (s : Finset Nat) (b : Nat → Tree)
    (x : Nat → Bool) (w : List Bool) (hw : w.length = n) (early : earlier n gs)
    (reg : regular n gs s) (hm : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (h : builds b cut marker n gs) (fixed : eval x (b cut) = x marker)
    (old : ∀ i < n, eval x (b i) = w.getD i false) :
    ∀ i < n+gs.length, eval x (b i) = (gs.foldl push w).getD i false := by
  induction gs generalizing n w with
  | nil => simpa using old
  | cons g gs ih =>
    have vlen : (push w g).length = n+1 := by simp [push,hw]
    have value (i : Nat) (hi : i < n) : eval x (cutMap b cut marker i) = w.getD i false := by
      by_cases e : i = cut
      · subst i; simpa [cutMap,eval,← fixed] using old cut hi
      · simpa [cutMap,e] using old i hi
    have next (i : Nat) (hi : i < n+1) : eval x (b i) = (push w g).getD i false := by
      by_cases e : i = n
      · subst i
        obtain ⟨a,z,inp⟩ := two_inputs _ reg.2.1 (hm g (by simp)).2
        have va := value a (early.1 a (by simp [inp]))
        have vz := value z (early.1 z (by simp [inp]))
        rw [h.1]
        rcases (hm g (by simp)).1 with hop|hop <;>
          simp [nodeOf,inp,hop,eval,op,push,hw,List.getD_eq_getElem?_getD,GateOp.eval] at va vz ⊢ <;>
          simp [va,vz]
      · rw [read_other _ _ _ (by omega)]; exact old _ (by omega)
    simpa only [List.length_cons,List.foldl_cons,Nat.add_assoc,Nat.add_comm 1] using
      ih (n+1) (push w g) vlen early.2 reg.2.2 (fun k hk => hm k (by simp [hk])) h.2 next

/-- A pair of actual formulas: evaluate the inner formula on the raw input,
    then supply its result at the marker of the outer formula. -/
theorem decompose (c : Circuit) (hm : Monotone2 c) (hr : Represents (Alexrollo64.DisjointCopies.graph 3) c)
    (hs : c.size ≤ 24) :
    ∃ inner outer : Tree,
      54 ∉ leaves inner ∧
      footprint inner + footprint outer = CommonThree.requiredThree.val + {54} + {54} ∧
      ∀ w : List Bool, w.length = 30 →
        let raw := fun i => w.getD i false
        eval (Function.update raw 54 (eval raw inner)) outer = c.eval w := by
  obtain ⟨j,b,lo,hi,start,build,mass⟩ := candidate_trees c hm hr hs

  have low := Alexrollo64.DisjointCopies.lower 3 c.size ⟨c,hm,le_rfl,hr⟩
  have len : c.gates.length = 24 := by change c.gates.length ≤ 24 at hs; change 8*3 ≤ c.gates.length at low; omega
  have early := candidate_earlier c hm hr hs
  have reg := candidate_regular c hm hr hs
  have no := marker_absent _ _ _ _ _ _ early reg (fun g hg => (hm g hg).2) build
    (fun i lt _ => by simp [start i lt,leaves]; omega) j (by omega) le_rfl
  refine ⟨b j,cutMap b j 54 c.output,no,mass,?_⟩
  intro w hw
  let raw := fun i => w.getD i false
  let x := Function.update raw 54 (eval raw (b j))
  have old (i : Nat) (lt : i < 30) : eval x (b i) = raw i := by
    rw [start i lt]; exact Function.update_of_ne (by omega) _ _
  have fixed : eval x (b j) = x 54 := by
    simpa [x] using eval_update (b j) raw 54 (eval raw (b j)) no
  have out : c.output < 30+c.gates.length := by
    obtain ⟨k,_,ku,eq⟩ := candidate_uses c hm hr hs
    have mem : c.output ∈ uses c.gates {c.output} := by simp [uses]
    rw [eq,Multiset.mem_add] at mem
    rcases mem with m|m
    · rcases Finset.mem_union.mp (show c.output ∈ wires from m) with a|a
      · obtain ⟨t,_,e⟩ := Finset.mem_image.mp a
        have := (by decide +kernel : ∀ t : Fin 24, Alexrollo64.DisjointCopies.requiredWire 3 t < 30) t
        omega
      · have := Finset.mem_range.mp (Finset.mem_filter.mp a).1; omega
    · simp at m; omega
  have ev := simulate _ _ _ _ _ _ x w hw early reg
    (fun g hg => ⟨by simpa using (hm g hg).1,(hm g hg).2⟩) build fixed old c.output out
  change eval x (cutMap b j 54 c.output) = (c.gates.foldl push w).getD c.output false
  by_cases e : c.output = j
  · simp only [cutMap,e,ite_true,eval,← fixed]; simpa only [e] using ev
  · rw [cutMap,ite_eq_right e]; exact ev

#print axioms decompose
end Alexrollo64.CutTrees
