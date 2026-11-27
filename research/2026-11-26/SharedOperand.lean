import OneDefect

namespace Alexrollo64.SharedOperand

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open Alexrollo64.Support20782 Alexrollo64.DisjointCopies Alexrollo64.OneDefect

theorem gate_bound (w : Fin 7 → List Bool) (n : Nat) (g : Gate)
    (hw : ∀ i, (w i).length = n) (hop : g.op = .and ∨ g.op = .or)
    (hf : g.inputs.length ≤ 2) (hne : g.inputs ≠ []) :
    score (fun i => push (w i) g) n ≤ mass w g.inputs.toFinset := by
  have read (k : Fin 7) : (push (w k) g).getD n false =
      g.op.eval (g.inputs.map fun i => (w k).getD i false) := by
    simp [push,List.getD_eq_getElem?_getD,hw]
  simp only [score,read]
  cases h : g.inputs with
  | nil => contradiction
  | cons a tail =>
    cases tail with
    | nil =>
      rcases hop with op|op <;> simp [score,op,mass,GateOp.eval]
    | cons b tail =>
      cases tail with
      | cons d ds => simp [h] at hf
      | nil =>
        by_cases eq : a = b
        · subst b
          rcases hop with op|op <;> simp [score,op,mass,GateOp.eval]
        · have law := subadd (pack fun k => (w k).getD a false) (pack fun k => (w k).getD b false)
          rcases hop with op|op
          · simpa [score,op,mass,GateOp.eval,pack_and,eq] using law.1
          · simpa [score,op,mass,GateOp.eval,pack_or,eq] using law.2

theorem overlap_pos (n : Nat) (g : Gate) (s : Finset Nat) (w : Fin 7 → List Bool)
    (hw : ∀ i, (w i).length = n) (hop : g.op = .and ∨ g.op = .or)
    (hf : g.inputs.length ≤ 2) (card : (before n g s).card ≥ s.card)
    (gain : mass w (before n g s) < mass (fun i => push (w i) g) s) :
    ∃ j ∈ (s.erase n ∩ g.inputs.toFinset), 0 < score w j := by
  let v := fun i => push (w i) g
  have hi := (gain_active w n g s hw gain).1
  have er := Finset.card_erase_add_one hi
  have ne : g.inputs ≠ [] := by
    intro eq
    simp [before,hi,eq] at card
    omega
  have bd := gate_bound w n g hw hop hf ne
  have keep (j) (hj : j ∈ s.erase n) : score v j = score w j := by
    unfold score; congr 2; funext i
    exact read_other _ _ _ (by rw [hw]; exact (Finset.mem_erase.mp hj).1)
  have sumk := Finset.sum_congr (s₁ := s.erase n) rfl keep
  have sumv := Finset.sum_erase_add _ (score v) hi
  rw [sumk] at sumv
  have law := Finset.sum_union_inter (s₁ := s.erase n) (s₂ := g.inputs.toFinset) (f := score w)
  by_contra! empty
  have z : ∑ i ∈ s.erase n ∩ g.inputs.toFinset, score w i = 0 := by
    apply Finset.sum_eq_zero
    intro i h; exact Nat.eq_zero_of_le_zero (empty i h)
  rw [z,Nat.add_zero] at law
  simp only [before,ite_eq_left hi,mass] at gain
  change score v n ≤ ∑ j ∈ g.inputs.toFinset, score w j at bd
  rw [←sumv,law] at gain
  exact (Nat.not_lt_of_ge (Nat.add_le_add_left bd _)) gain

theorem same_operand (n : Nat) (g : Gate) (s : Finset Nat) (w v : Fin 7 → List Bool)
    (hw : ∀ i, (w i).length = n) (hv : ∀ i, (v i).length = n)
    (hop : g.op = .and ∨ g.op = .or) (hf : g.inputs.length ≤ 2)
    (card : (before n g s).card ≥ s.card)
    (gw : mass w (before n g s) < mass (fun i => push (w i) g) s)
    (gv : mass v (before n g s) < mass (fun i => push (v i) g) s) :
    ∃ j ∈ s.erase n ∩ g.inputs.toFinset, 0 < score w j ∧ 0 < score v j := by
  obtain ⟨a,ha,pa⟩ := overlap_pos n g s w hw hop hf card gw
  obtain ⟨b,hb,pb⟩ := overlap_pos n g s v hv hop hf card gv
  have hi := (gain_active w n g s hw gw).1
  have hc := Finset.card_union_add_card_inter (s.erase n) g.inputs.toFinset
  have he := Finset.card_erase_add_one hi
  have ht := List.toFinset_card_le (l := g.inputs)
  simp only [before,ite_eq_left hi] at card
  have small : (s.erase n ∩ g.inputs.toFinset).card ≤ 1 := by omega
  have eq := Finset.card_le_one.mp small a ha b hb
  exact ⟨a,ha,pa,eq ▸ pb⟩

/-- A previously computed gate output occurs in the exceptional gate's inputs
and is still required by another branch. Its test weight is positive in both blocks. -/
def shared (n : Nat) : List Gate → Finset Nat → (Fin 7 → List Bool) → (Fin 7 → List Bool) → Prop
  | [], _, _, _ => False
  | g::gs, s, w, v =>
    (∃ j ∈ (needed (n+1) gs s).erase n ∩ g.inputs.toFinset,
      20 ≤ j ∧ j < n ∧ 0 < score w j ∧ 0 < score v j) ∨
    shared (n+1) gs s (fun i => push (w i) g) (fun i => push (v i) g)

theorem lift_gain (gs : List Gate) (n : Nat) (hn : 20 ≤ n) (s : Finset Nat)
    (w v : Fin 7 → List Bool) (hw : ∀ i, (w i).length = n) (hv : ∀ i, (v i).length = n)
    (raw : ∀ j < 20, score w j = 0 ∨ score v j = 0)
    (hm : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (d : (deficitList n gs s).sum ≤ 1) (gain : commonGain n gs s w v) :
    shared n gs s w v := by
  induction gs generalizing n w v with
  | nil => exact gain.elim
  | cons g gs ih =>
    let mid := needed (n+1) gs s
    have hg := hm g (by simp)
    change mid.card+1-(before n g mid).card + (deficitList (n+1) gs s).sum ≤ 1 at d
    rcases gain with ⟨gw,gv,_⟩|later
    · left
      obtain ⟨j,hj,p,q⟩ := same_operand n g mid w v hw hv hg.1 hg.2 (by omega) gw gv
      have lo : 20 ≤ j := by
        by_contra! h
        rcases raw j h with eq|eq <;> omega
      have up : j < n := by
        by_contra! h
        have empty (i) : (w i).getD j false = false := List.getD_eq_default _ _ (by rw [hw]; omega)
        have zero : score w j = 0 := by unfold score; simp_rw [empty]; decide +kernel
        omega
      exact ⟨j,hj,lo,up,p,q⟩
    · right
      have keep (x : Fin 7 → List Bool) (hx : ∀ i, (x i).length = n)
          (j : Nat) (hj : j < 20) : score (fun i => push (x i) g) j = score x j := by
        unfold score; congr 2; funext i; exact read_other _ _ _ (by rw [hx]; omega)
      exact ih (n+1) (by omega) _ _ (fun i => by simp [push,hw]) (fun i => by simp [push,hv])
        (fun j hj => by rw [keep w hw j hj,keep v hv j hj]; exact raw j hj)
        (fun a ha => hm a (by simp [ha])) (by omega) later

theorem candidate_shared (c : Circuit) (hm : Monotone2 c) (hr : Represents (graph 2) c) (hs : c.size ≤ 16) :
    shared 20 c.gates {c.output} (suite 0) (suite 1) := by
  have raw : ∀ j : Fin 20, score (suite 0) j.val = 0 ∨ score (suite 1) j.val = 0 := by decide +kernel
  exact lift_gain _ 20 le_rfl _ _ _ (fun i => by simp [suite,oneEach]) (fun i => by simp [suite,oneEach])
    (fun j hj => raw ⟨j,hj⟩) (fun g hg => ⟨by simpa using (hm g hg).1,(hm g hg).2⟩)
    (le_of_eq (candidate c hm hr hs).2) (both_blocks c hm hr hs)

def testedLeft : Finset Nat := {2,3,4,10,11,14}
def testedRight : Finset Nat := {7,8,9,15,16,19}

def binary (isAnd : Bool) (a b : Bool) := if isAnd then a && b else a || b

/-- If the shared signal is produced by a single binary gate on primary inputs,
the two certificate suites leave only six choices in each block and force OR. -/
theorem raw_pair (p : Bool) (a b : Fin 20)
    (h : ∀ k : Fin 2, ∃ i : Fin 7,
      binary p ((suite k i).getD a.val false) ((suite k i).getD b.val false) = true) :
    p = false ∧ ((a.val ∈ testedLeft ∧ b.val ∈ testedRight) ∨
                  (b.val ∈ testedLeft ∧ a.val ∈ testedRight)) := by
  have left : ∀ j : Fin 20, ∀ i, (suite 0 i).getD j.val false = true → j.val ∈ testedLeft := by decide +kernel
  have right : ∀ j : Fin 20, ∀ i, (suite 1 i).getD j.val false = true → j.val ∈ testedRight := by decide +kernel
  have disj : Disjoint testedLeft testedRight := by decide +kernel
  obtain ⟨i,hi⟩ := h 0
  obtain ⟨j,hj⟩ := h 1
  cases p
  · simp only [binary,Bool.false_eq_true,ite_false,Bool.or_eq_true] at hi hj
    rcases hi with x|x <;> rcases hj with y|y
    · exact (Finset.disjoint_left.mp disj (left _ _ x) (right _ _ y)).elim
    · exact ⟨rfl,Or.inl ⟨left _ _ x,right _ _ y⟩⟩
    · exact ⟨rfl,Or.inr ⟨left _ _ x,right _ _ y⟩⟩
    · exact (Finset.disjoint_left.mp disj (left _ _ x) (right _ _ y)).elim
  · simp only [binary,ite_true,Bool.and_eq_true] at hi hj
    exact (Finset.disjoint_left.mp disj (left _ _ hi.1) (right _ _ hj.1)).elim

theorem count_raw_pairs : (testedLeft ×ˢ testedRight).card = 36 := by decide +kernel

#print axioms candidate_shared
#print axioms raw_pair
#print axioms count_raw_pairs
end Alexrollo64.SharedOperand
