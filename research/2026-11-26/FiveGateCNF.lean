import Std.Sat.CNF.Dimacs
import TwoLitTables

namespace Alexrollo64.FiveGateCNF
open Std.Sat Alexrollo64.TwoLitTables

/-- DIMACS variable numbers are one-based. Each gate allocates selectors and
counter bits first, then three bits per row for its two operands and result. -/
def start : Nat → Nat
  | 0 => 127
  | g+1 => start g + 4*(6+g) + 66

def leftId (g k : Nat) := start g + k
def rightId (g k : Nat) := start g + (6+g) + k
def opId (g k : Nat) := start g + 4*(6+g)-2 + k
def aId (g r : Nat) := opId g 5 + 3*r
def bId (g r : Nat) := aId g r + 1
def zId (g r : Nat) := aId g r + 2
def wireId (k r : Nat) := if k < 6 then 1 + 21*k + r else zId (k-6) r

abbrev Clauses := List (List Int)
def pos (k : Nat) : Int := k
def neg (k : Nat) : Int := -(pos k)

/-- Sequential exactly-one block for n ≥ 3, the only sizes used here. -/
def one (n : Nat) (v aux : Nat → Nat) : Clauses :=
  [(List.range n).map (fun i => pos (v i)), [neg (v 0),pos (aux 0)]] ++
  (List.range (n-2)).flatMap (fun i =>
    [[neg (aux i), pos (aux (i+1))], [neg (v (i+1)), neg (aux i)],
     [neg (v (i+1)), pos (aux (i+1))]]) ++ [[neg (v (n-1)), neg (aux (n-2))]]

def rowClauses (g r : Nat) : Clauses :=
  let a := pos (aId g r)
  let b := pos (bId g r)
  let z := pos (zId g r)
  let ops := fun i => neg (opId g i)
  (List.range (6+g)).flatMap (fun k =>
    let l := neg (leftId g k)
    let h := neg (rightId g k)
    let x := pos (wireId k r)
    [[l,-a,x],[l,a,-x],[h,-b,x],[h,b,-x]]) ++
  [[ops 0,-z,a],[ops 0,-z,b],[ops 0,z,-a,-b],
   [ops 1,z,-a],[ops 1,z,-b],[ops 1,-z,a,b],[ops 2,-z,-a],[ops 2,z,a]]

def gateClauses (g : Nat) : Clauses :=
  let w := 6+g
  one w (leftId g) (fun i => start g+2*w+i) ++
  one w (rightId g) (fun i => start g+3*w-1+i) ++
  (List.range w).flatMap (fun a => (List.range a).map (fun b =>
    [neg (leftId g a),neg (rightId g b)])) ++
  one 3 (opId g) (fun i => opId g (3+i)) ++
  (List.range 21).flatMap (rowClauses g)

def unit (k : Nat) (v : Bool) : List Int := [if v then pos k else neg k]

def encoded : Clauses :=
  (List.range 6).flatMap (fun k => (List.range 21).map (fun r =>
    unit (wireId k r) ((columnMasks.getD k 0).testBit r))) ++
  (List.range 5).flatMap gateClauses ++
  (List.range 21).map (fun r => unit (zId 4 r) ((1351679 : Nat).testBit r))

def formula : CNF Nat :=
  ⟨encoded.toArray.map (fun c =>
    CNF.Clause.ofLiterals (c.map (fun i => (i.natAbs-1, decide (i>0)))))⟩


/-- Interpretation on one-based DIMACS variable numbers. -/
def litValue (v : Nat → Bool) (i : Int) := if i > 0 then v i.natAbs else !(v i.natAbs)
def Holds (v : Nat → Bool) (cs : Clauses) : Prop :=
  ∀ c ∈ cs, c.any (litValue v) = true

theorem lit_pos (v : Nat → Bool) (k : Nat) (h : 0 < k) : litValue v (pos k) = v k := by
  simp [litValue,pos,h]
theorem lit_neg (v : Nat → Bool) (k : Nat) : litValue v (neg k) = !(v k) := by
  simp [litValue,neg,pos]

/-- The auxiliary bit at i records whether the chosen index has already appeared. -/
theorem one_complete (n pick : Nat) (hn : 3 ≤ n) (hp : pick < n)
    (v aux : Nat → Nat) (a : Nat → Bool)
    (pv : ∀ i, 0 < v i) (pa : ∀ i, 0 < aux i)
    (hv : ∀ i < n, a (v i) = decide (pick = i))
    (ha : ∀ i < n-1, a (aux i) = decide (pick ≤ i)) :
    Holds a (one n v aux) := by
  intro c hc
  simp only [one,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_flatMap,
    List.mem_range] at hc
  rcases hc with ((h|h)|⟨i,hi,h|h|h⟩)|h
  · subst c
    apply List.any_eq_true.mpr
    exact ⟨pos (v pick),List.mem_map.mpr ⟨pick,List.mem_range.mpr hp,rfl⟩,by
      rw [lit_pos _ _ (pv _),hv _ hp]; simp⟩
  all_goals subst c
  all_goals simp (disch := omega) only [List.any_cons,List.any_nil,Bool.or_false,lit_neg,lit_pos _ _ (pa _),
    hv,ha,Bool.or_eq_true,Bool.not_eq_true',decide_eq_false_iff_not,
    decide_eq_true_eq]
  all_goals omega

#print axioms one_complete

/-- Inputs for the clause-completeness proof. Each gate chooses two currently
available wires and an operation (0 = AND, 1 = OR, 2 = NOT). -/
structure Trace where
  l : Nat → Nat
  r : Nat → Nat
  op : Nat → Nat
  value : Nat → Nat → Bool
  left_le : ∀ g < 5, l g ≤ r g
  right_lt : ∀ g < 5, r g < 6+g
  op_lt : ∀ g < 5, op g < 3
  input : ∀ k < 6, ∀ r < 21, value k r = (columnMasks.getD k 0).testBit r
  output : ∀ r < 21, value 10 r = (1351679 : Nat).testBit r
  eval : ∀ g < 5, ∀ row < 21, value (6+g) row =
    (if op g = 0 then value (l g) row && value (r g) row
     else if op g = 1 then value (l g) row || value (r g) row else !value (l g) row)

inductive Key where
  | wire (k row : Nat)
  | left (g i : Nat)
  | right (g i : Nat)
  | oper (g i : Nat)
  | leftCount (g i : Nat)
  | rightCount (g i : Nat)
  | opCount (g i : Nat)
  | lhs (g row : Nat)
  | rhs (g row : Nat)
  deriving DecidableEq, Inhabited

def Key.number : Key → Nat
  | .wire k r => wireId k r
  | .left g i => leftId g i
  | .right g i => rightId g i
  | .oper g i => opId g i
  | .leftCount g i => start g + 2*(6+g) + i
  | .rightCount g i => start g + 3*(6+g) - 1 + i
  | .opCount g i => opId g (3+i)
  | .lhs g r => aId g r
  | .rhs g r => bId g r

def Key.bit (t : Trace) : Key → Bool
  | .wire k r => t.value k r
  | .left g i => decide (t.l g = i)
  | .right g i => decide (t.r g = i)
  | .oper g i => decide (t.op g = i)
  | .leftCount g i => decide (t.l g ≤ i)
  | .rightCount g i => decide (t.r g ≤ i)
  | .opCount g i => decide (t.op g ≤ i)
  | .lhs g r => t.value (t.l g) r
  | .rhs g r => t.value (t.r g) r

def gateKeys (g : Nat) : List Key :=
  let w := 6+g
  (List.range w).map (.left g) ++ (List.range w).map (.right g) ++
  (List.range (w-1)).map (.leftCount g) ++ (List.range (w-1)).map (.rightCount g) ++
  (List.range 3).map (.oper g) ++ (List.range 2).map (.opCount g) ++
  (List.range 21).flatMap (fun r => [.lhs g r,.rhs g r,.wire (6+g) r])

/-- Entries in exact DIMACS variable order. Index zero is a dummy. -/
def keys : List Key := [.wire 0 0] ++
  (List.range 6).flatMap (fun k => (List.range 21).map (.wire k)) ++
  (List.range 5).flatMap gateKeys

def assignment (t : Trace) (i : Nat) := (keys.getD i default).bit t

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem allocated : keys.length = 617 ∧ ∀ k ∈ keys, keys.getD k.number default = k ∧ 0 < k.number := by
  decide +kernel

theorem assigned (t : Trace) (k : Key) (hk : k ∈ keys) :
    assignment t k.number = k.bit t := by
  unfold assignment
  rw [((allocated.2 k hk).1)]

#print axioms allocated
theorem gate_mem (g : Nat) (hg : g < 5) (k : Key) (h : k ∈ gateKeys g) : k ∈ keys :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨g,List.mem_range.mpr hg,h⟩)

theorem selector_blocks (t : Trace) (g : Nat) (hg : g < 5) :
    let w := 6+g
    Holds (assignment t) (one w (leftId g) (fun i => (Key.leftCount g i).number)) ∧
    Holds (assignment t) (one w (rightId g) (fun i => (Key.rightCount g i).number)) ∧
    Holds (assignment t) (one 3 (opId g) (fun i => (Key.opCount g i).number)) := by
  have group {f : Nat → Key} {n : Nat}
      (mem : ∀ k ∈ (List.range n).map f, k ∈ gateKeys g) (i : Nat) (hi : i < n) :
      f i ∈ keys := gate_mem g hg _ (mem _ (List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩))
  have block (n pick : Nat) (hn : 3 ≤ n) (hp : pick < n) (v c : Nat → Key)
      (vm : ∀ i < n, v i ∈ keys) (cm : ∀ i < n-1, c i ∈ keys)
      (vp : ∀ i, 0 < (v i).number) (cp : ∀ i, 0 < (c i).number)
      (vb : ∀ i, (v i).bit t = decide (pick = i))
      (cb : ∀ i, (c i).bit t = decide (pick ≤ i)) :
      Holds (assignment t) (one n (fun i => (v i).number) (fun i => (c i).number)) :=
    one_complete _ _ hn hp _ _ _ vp cp
      (fun i hi => (assigned _ _ (vm i hi)).trans (vb i))
      (fun i hi => (assigned _ _ (cm i hi)).trans (cb i))
  have lower : ∀ j, 127 ≤ start j := by
    intro j; induction j with
    | zero => decide
    | succ j ih => simp only [start]; omega
  have startPos := lower g
  have hL := t.left_le g hg
  have hR := t.right_lt g hg
  refine ⟨block _ (t.l g) (by omega) (by omega) (.left g) (.leftCount g) ?_ ?_ ?_ ?_
    (fun _ => rfl) (fun _ => rfl), block _ (t.r g) (by omega) hR (.right g) (.rightCount g)
    ?_ ?_ ?_ ?_ (fun _ => rfl) (fun _ => rfl),
    block 3 (t.op g) (by decide) (t.op_lt g hg) (.oper g) (.opCount g)
    ?_ ?_ ?_ ?_ (fun _ => rfl) (fun _ => rfl)⟩
  all_goals first
    | apply group; intro k hk; simp only [gateKeys,List.mem_append]; tauto
    | intro i; simp only [Key.number,leftId,rightId,opId]; omega

#print axioms selector_blocks
end Alexrollo64.FiveGateCNF
