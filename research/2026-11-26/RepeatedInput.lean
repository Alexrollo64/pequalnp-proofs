import TreeCopies

namespace Alexrollo64.RepeatedInput
open PEqualNP.Represents Alexrollo64.TreeCopies
open Alexrollo64.Support20782 (Word pack pack_and pack_or rows cols target)

/-- One 3-bit weight for each truth pattern on the seven tests. -/
def weight (s : Fin 5) (x : Word) : Nat :=
  let table : Nat := ![16877102379750682026150201864814161298759648775202590028053491825642454519831415925865358056768998815462010548789904,
    11950498551025222962942584236826437587576853356221482654111697062861319977958773256236175225749368427688203821621320,
    11249618579450961605250731630881208761949883823351476807224447759909501020070037099239312081855374855356727113126544,
    11874875475352436742184524331657385421869254095296942167491237321441371728308608509846018650131590547644913900429960,
    11334821360971765696764234202759035296667504876321220565700713358168919122678847945196034289816833756300992983212688] s
  (table >>> (3*x.toNat)) % 8

def checkChunk (s : Fin 5) (k : Nat) :=
  (List.range 4).all fun r => (List.range 128).all fun n =>
    let a : Word := BitVec.ofNat 7 (4*k+r)
    let b : Word := BitVec.ofNat 7 n
    decide (weight s (a &&& b) ≤ weight s a + weight s b ∧
            weight s (a ||| b) ≤ weight s a + weight s b)

set_option maxHeartbeats 4000000 in
private theorem verified0 (k : Nat) (hk : k < 32) : checkChunk 0 k = true := by
  interval_cases k <;> decide +kernel

set_option maxHeartbeats 4000000 in
private theorem verified1 (k : Nat) (hk : k < 32) : checkChunk 1 k = true := by
  interval_cases k <;> decide +kernel

set_option maxHeartbeats 4000000 in
private theorem verified2 (k : Nat) (hk : k < 32) : checkChunk 2 k = true := by
  interval_cases k <;> decide +kernel

set_option maxHeartbeats 4000000 in
private theorem verified3 (k : Nat) (hk : k < 32) : checkChunk 3 k = true := by
  interval_cases k <;> decide +kernel

set_option maxHeartbeats 4000000 in
private theorem verified4 (k : Nat) (hk : k < 32) : checkChunk 4 k = true := by
  interval_cases k <;> decide +kernel

theorem weight_subadd (s : Fin 5) (a b : Word) :
    weight s (a &&& b) ≤ weight s a + weight s b ∧
    weight s (a ||| b) ≤ weight s a + weight s b := by
  let k := a.toNat / 4
  have hk : k < 32 := by dsimp [k]; have := a.isLt; omega
  have checked : checkChunk s k = true := by
    fin_cases s
    · exact verified0 k hk
    · exact verified1 k hk
    · exact verified2 k hk
    · exact verified3 k hk
    · exact verified4 k hk
  have row := List.all_eq_true.mp checked (a.toNat%4) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  have pair := List.all_eq_true.mp row b.toNat (List.mem_range.mpr b.isLt)
  have id : 4*k + a.toNat%4 = a.toNat := by dsimp [k]; omega
  simpa [id] using pair

def tableFor (d : Nat) : Fin 5 := if d = 2 then 1 else if d = 3 then 2 else if d = 5 then 3 else if d = 9 then 4 else 0

def col (d : Nat) (i : Fin 7) : Fin 5 := if d = 6 ∧ cols i = 1 then 2 else cols i
def input (d : Nat) (i : Fin 7) (j : Nat) := (oneEach (rows i) (col d i)).getD j false
def leafWeight (d j : Nat) := weight (tableFor d) (pack (fun i => input d i j))

theorem tree_weight (t : Tree) (d : Nat) :
    weight (tableFor d) (pack fun i => eval (input d i) t) ≤
      ((leaves t).map (leafWeight d)).sum := by
  induction t with
  | leaf j => simp [eval,leaves,leafWeight]
  | node p u v hu hv =>
    have law := weight_subadd (tableFor d) (pack fun i => eval (input d i) u)
      (pack fun i => eval (input d i) v)
    cases p <;> simp [eval,op,leaves,pack_and,pack_or] <;> omega

theorem numerical : ∀ d : Fin 10, d.val ≠ 4 →
    leafWeight d d = 0 ∧ (∑ j : Fin 10, leafWeight d j) <
      weight (tableFor d) (pack fun i => target (rows i) (col d i)) := by decide +kernel

theorem zeroWeight : ∀ s : Fin 5, weight s (pack fun _ => false) = 0 := by decide +kernel

theorem total (d : Fin 10) (l : List Nat) :
      (l.map (leafWeight d)).sum = ∑ j : Fin 10, l.count j.val * leafWeight d j := by
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons,List.sum_cons,ih,List.count_cons]
      simp_rw [Nat.add_mul,Finset.sum_add_distrib]
      by_cases ha : a < 10
      · simp [beq_iff_eq, show ∀ j : Fin 10, a = j.val ↔ j = ⟨a,ha⟩ by intro j; simp [Fin.ext_iff,eq_comm],Nat.add_comm]
      · have off (i) : input d i a = false := by
          apply List.getD_eq_default
          simp [oneEach]; omega
        have z : leafWeight d a = 0 := by
          unfold leafWeight; simp_rw [off]
          exact zeroWeight _
        simp [beq_iff_eq,z,show ∀ j : Fin 10, a ≠ j.val by intro j; omega]

/-- For every proposed repeated input other than row 4, some *other* input
must also repeat. The number of occurrences of the proposed input is unlimited. -/
theorem necessary (t : Tree) (d : Fin 10)
    (correct : ∀ u v : Fin 5, eval (fun j => (oneEach u v).getD j false) t = target u v)
    (only : ∀ j : Fin 10, j ≠ d → (leaves t).count j.val ≤ 1) : d.val = 4 := by
  by_contra bad
  obtain ⟨zero,strict⟩ := numerical d bad
  have charge := tree_weight t d
  have same : (fun i => eval (input d i) t) = (fun i => target (rows i) (col d i)) :=
    funext fun i => correct _ _
  rw [same] at charge
  have le : ∀ j : Fin 10, (leaves t).count j.val * leafWeight d j ≤ leafWeight d j := by
    intro j
    by_cases eq : j = d
    · subst j; simp [zero]
    · simpa using Nat.mul_le_mul_right (leafWeight d j) (only j eq)
  rw [total d _] at charge
  exact (Nat.not_lt_of_ge (charge.trans (Finset.sum_le_sum (fun j _ => le j)))) strict

/-- Replace every use of port 10 with the corresponding surviving local input. -/
def replacePort (d : Nat) (t : Tree) : Tree :=
  match t with
  | .leaf j => .leaf (if j = 10 then d else j)
  | .node p u v => .node p (replacePort d u) (replacePort d v)

theorem alias_eval (d : Nat) (t : Tree) (x : Nat → Bool) :
    eval x (replacePort d t) = eval (fun j => x (if j = 10 then d else j)) t := by
  induction t <;> simp_all [replacePort,eval]

theorem alias_count (d j : Fin 10) (ne : j ≠ d) (t : Tree) :
    (leaves (replacePort d t)).count j.val = (leaves t).count j.val := by
  induction t with
  | leaf i =>
    by_cases hi : i = 10
    · subst i; have h : d.val ≠ j.val := fun e => ne (Fin.ext e.symm)
      simp [replacePort,leaves,h,show 10 ≠ j.val by omega]
    · simp [replacePort,leaves,hi]
  | node p u v hu hv => simp [replacePort,leaves,List.count_append,hu,hv]

/-- On the block containing the column, the shared OR reduces to that column.
A downstream formula with arbitrary uses of this port must repeat another primary input. -/
theorem column_port (t : Tree) (c : Fin 5)
    (correct : ∀ u v : Fin 5,
      eval (fun j => (oneEach u v).getD (if j = 10 then 5+c.val else j) false) t = target u v) :
    ∃ j : Fin 10, j.val ≠ 5+c.val ∧ 2 ≤ (leaves t).count j.val := by
  let d : Fin 10 := ⟨5+c.val,by omega⟩
  by_contra! small
  have h := necessary (replacePort d t) d (fun u v => (alias_eval d t _).trans (correct u v))
    (fun j ne => by
      rw [alias_count d j ne]
      have eq : j.val ≠ 5+c.val := fun e => ne (Fin.ext e)
      exact Nat.le_of_lt_succ (small j eq))
  change 5+c.val = 4 at h
  omega

/-- Exact classification, including an eight-gate witness for the unique allowed input. -/
theorem classification (d : Fin 10) :
    (∃ t : Tree, (∀ u v : Fin 5, eval (fun j => (oneEach u v).getD j false) t = target u v) ∧
      (∀ j : Fin 10, j ≠ d → (leaves t).count j.val ≤ 1)) ↔ d.val = 4 := by
  constructor
  · rintro ⟨t,hc,ho⟩
    exact necessary t d hc ho
  · intro hd
    have eq : d = 4 := Fin.ext hd
    subst d
    refine ⟨block 1 0,?_,?_⟩
    · decide +kernel
    · decide +kernel

open Alexrollo64.DisjointCopies (wire graph vertex same_block)
open Alexrollo64.PaddedRows (one_read)

def localIndex (k : Fin 2) (j : Nat) : Nat :=
  if j = 20 then 10
  else if 5*k.val ≤ j ∧ j < 5*k.val+5 then j-5*k.val
  else if 10+5*k.val ≤ j ∧ j < 15+5*k.val then j-(10+5*k.val)+5
  else 11

theorem preimage (k : Fin 2) (j : Fin 10) (i : Nat) :
    localIndex k i = j.val ↔ i = wire k j.val := by
  unfold localIndex wire
  split_ifs <;> omega

def projectTree (k : Fin 2) : Tree → Tree
  | .leaf i => .leaf (localIndex k i)
  | .node p a b => .node p (projectTree k a) (projectTree k b)

theorem project_eval (k : Fin 2) (t : Tree) (x : Nat → Bool) :
    eval x (projectTree k t) = eval (fun i => x (localIndex k i)) t := by
  induction t <;> simp_all [projectTree,eval]

theorem project_count (k : Fin 2) (j : Fin 10) (t : Tree) :
    (leaves (projectTree k t)).count j.val = (leaves t).count (wire k j.val) := by
  induction t with
  | leaf i => simp [projectTree,leaves,List.count_cons,beq_iff_eq,preimage]
  | node p a b ha hb => simp [projectTree,leaves,List.count_append,ha,hb]

/-- Wire 20 carries the OR of a column in block k and a row in the other block. -/
def mixedInput (k : Fin 2) (r c : Fin 5) (u v : Fin 10) (i : Nat) :=
  if i = 20 then (oneEach u v).getD (10+5*k.val+c.val) false ||
    (oneEach u v).getD (5*(1-k.val)+r.val) false
  else (oneEach u v).getD i false

theorem mixed_restrict (k : Fin 2) (r c u v : Fin 5) (i : Nat) :
    (oneEach u v).getD (if localIndex k i = 10 then 5+c.val else localIndex k i) false =
    mixedInput k r c (vertex k u) (vertex k v) i := by
  simp only [mixedInput,one_read,vertex,localIndex]
  apply Bool.eq_iff_iff.mpr
  split_ifs <;> simp only [Bool.or_eq_true,decide_eq_true_eq] <;> omega

theorem mixed_requires_repeat (k : Fin 2) (r c : Fin 5) (t : Tree)
    (correct : ∀ u v : Fin 10, eval (mixedInput k r c u v) t = graph 2 u v) :
    ∃ j : Fin 10, j.val ≠ 5+c.val ∧ 2 ≤ (leaves t).count (wire k j.val) := by
  have localCorrect (u v : Fin 5) :
      eval (fun j => (oneEach u v).getD (if j = 10 then 5+c.val else j) false) (projectTree k t) = target u v := by
    rw [project_eval]
    simp_rw [mixed_restrict k r c u v]
    exact (correct _ _).trans (same_block k u v)
  obtain ⟨j,ne,many⟩ := column_port (projectTree k t) c localCorrect
  exact ⟨j,ne,project_count k j t ▸ many⟩

def expand (a b : Nat) : Tree → Tree
  | .leaf j => if j = 20 then .node false (.leaf a) (.leaf b) else .leaf j
  | .node p u v => .node p (expand a b u) (expand a b v)

theorem expand_eval (t : Tree) (k : Fin 2) (r c : Fin 5) (u v : Fin 10) :
    eval (fun j => (oneEach u v).getD j false) (expand (10+5*k.val+c.val) (5*(1-k.val)+r.val) t) =
    eval (mixedInput k r c u v) t := by
  induction t with
  | leaf j => by_cases h : j = 20 <;> simp [expand,eval,mixedInput,h,op]
  | node p a b ha hb => simp only [expand,eval,ha,hb]

theorem expand_length (a b : Nat) (t : Tree) :
    (leaves (expand a b t)).length = (leaves t).length + (leaves t).count 20 := by
  induction t with
  | leaf j => by_cases h : j = 20 <;> simp [expand,leaves,h]
  | node p u v hu hv => simp [expand,leaves,List.count_append,hu,hv]; omega

theorem not_new (a b i : Nat) (ha : i ≠ a) (hb : i ≠ b) (t : Tree)
    (h : i ∈ leaves (expand a b t)) : i ∈ leaves t := by
  induction t with
  | leaf j => by_cases e : j = 20 <;> simp_all [expand,leaves]
  | node p u v hu hv => simp_all [expand,leaves]; tauto

theorem mono_leaves (t : Tree) (x y : Nat → Bool)
    (h : ∀ i ∈ leaves t, x i = true → y i = true) :
    eval x t = true → eval y t = true := by
  induction t with
  | leaf i => exact h i (by simp [leaves])
  | node p a b ha hb =>
    have A := ha (fun i hi => h i (by simp [leaves,hi]))
    have B := hb (fun i hi => h i (by simp [leaves,hi]))
    cases p <;> simp [eval,op] <;> tauto

def rawSet : Finset Nat := {2,3,4,7,8,9,10,11,12,13,14,15,16,17,18,19}

theorem raw_needed (t : Tree) (good : realizes 2 t) : rawSet ⊆ (leaves t).toFinset := by
  intro i hi
  have hi20 : i < 20 := by simp [rawSet] at hi; omega
  have localW := Alexrollo64.Support20782.witnesses
  let k : Fin 2 := ⟨if i < 10 then i/5 else (i-10)/5,by split <;> omega⟩
  let j : Fin 10 := ⟨if i < 10 then i%5 else 5+(i-10)%5,by split <;> omega⟩
  have id : wire k j.val = i := by unfold wire k j; dsimp; split_ifs <;> omega
  have req : j.val ∈ Alexrollo64.Support20782.required := by
    simp [rawSet] at hi
    simp [j,Alexrollo64.Support20782.required]; split_ifs <;> omega
  obtain ⟨a,b,d,e,pos,neg,ord⟩ := localW j req
  by_contra missing
  let x := oneEach (vertex k a) (vertex k b)
  let y := oneEach (vertex k d) (vertex k e)
  have forward := mono_leaves t (fun m => x.getD m false) (fun m => y.getD m false) (by
    intro m hm hx
    have ne : m ≠ i := fun eq => missing (List.mem_toFinset.mpr (eq ▸ hm))
    have lift (s : Fin 10) (hs : m = wire k s.val) : y.getD m false = true := by
      rw [hs] at hx ⊢
      change (oneEach (vertex k d) (vertex k e)).getD _ false = true
      rw [DisjointCopies.wire_read _ _ _ _ s.isLt]
      apply ord s (fun eq => ne (hs.trans (eq ▸ id)))
      exact (DisjointCopies.wire_read k a b s.val s.isLt) ▸ hx
    change (oneEach _ _).getD m false = true at hx
    rw [one_read] at hx
    simp only [Bool.or_eq_true,decide_eq_true_eq] at hx
    rcases hx with h|h
    · exact lift ⟨a.val,by omega⟩ (by simpa [wire,vertex,a.isLt] using h)
    · apply lift ⟨5+b.val,by omega⟩
      simp only [wire,show ¬5+b.val < 5 by omega,ite_false,Nat.add_sub_cancel_left]
      simpa [vertex,Nat.add_assoc] using h)
  dsimp only [x,y] at forward
  rw [good,good,same_block,same_block,pos,neg] at forward
  contradiction

theorem list_length_bound (l : List Nat) (S : Finset Nat) (inc : S ⊆ l.toFinset)
    (j : Nat) (hj : j ≠ 20) (h2 : 2 ≤ l.count j) (port : 2 ≤ l.count 20) (no : 20 ∉ S) :
    S.card + 3 ≤ l.length := by
  let rest := (l.erase j).erase 20
  have jmem : j ∈ l := List.count_pos_iff.mp (by omega)
  have pmem : 20 ∈ l.erase j := List.count_pos_iff.mp (by simpa [List.count_erase,hj,Ne.symm hj] using (show 0 < l.count 20 by omega))
  have mem (n : Nat) (hn : n ∈ insert 20 S) : n ∈ rest.toFinset := by
    apply List.mem_toFinset.mpr
    apply List.count_pos_iff.mp
    by_cases e : n = 20
    · subst n; simp [rest,Ne.symm hj]; omega
    · have hs := (Finset.mem_insert.mp hn).resolve_left e
      have hp := List.count_pos_iff.mpr (List.mem_toFinset.mp (inc hs))
      by_cases f : n = j <;> simp_all [rest]
      omega
  have card := Finset.card_le_card mem
  rw [Finset.card_insert_of_notMem no] at card
  have len := List.toFinset_card_le (l := rest)
  have lr : rest.length = l.length - 1 - 1 := by simp [rest,List.length_erase_of_mem,pmem,jmem]
  omega

theorem mixed_lower (k : Fin 2) (r c : Fin 5) (t : Tree)
    (correct : ∀ u v : Fin 10, eval (mixedInput k r c u v) t = graph 2 u v) :
    17 ≤ 1 + cost t := by
  let a := 10+5*k.val+c.val
  let b := 5*(1-k.val)+r.val
  have good : realizes 2 (expand a b t) := fun u v => (expand_eval t k r c u v).trans (correct u v)
  have length := length_leaves t
  by_cases port : (leaves t).count 20 ≤ 1
  · have low := formula_lower (expand a b t) good
    rw [←length_leaves,expand_length] at low
    omega
  · let S := (rawSet.erase a).erase b
    have inc : S ⊆ (leaves t).toFinset := by
      intro i hi
      have mem := Finset.mem_erase.mp hi
      have m := Finset.mem_erase.mp mem.2
      exact List.mem_toFinset.mpr (not_new a b i m.1 mem.1 t (List.mem_toFinset.mp (raw_needed _ good m.2)))
    have rawcard : rawSet.card = 16 := by decide +kernel
    have sc : 14 ≤ S.card := by simp only [S,Finset.card_erase_eq_ite]; split_ifs <;> omega
    obtain ⟨j,_,repeatJ⟩ := mixed_requires_repeat k r c t correct
    have ne : wire k j.val ≠ 20 := by unfold wire; split <;> omega
    have no : 20 ∉ S := by simp [S,rawSet]
    have low := list_length_bound (leaves t) S inc _ ne repeatJ (by omega) no
    omega

#print axioms classification
#print axioms mixed_lower
end Alexrollo64.RepeatedInput
