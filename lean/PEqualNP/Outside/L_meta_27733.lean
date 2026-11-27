import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_27733_aux

def firstGate : Gate := ⟨.or,[0,4]⟩
def secondGate : Gate := ⟨.or,[2,7]⟩
def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
def start (x : Fin 9 → Bool) := step (step (List.ofFn x) firstGate) secondGate
def target (x : Fin 9 → Bool) :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)
def seed : Fin 9 → Nat := ![176,96,136,132,69,66,20,12,10]
def leftInput (i j : Fin 9) := (seed i).testBit j.val
def rightInput (i j : Fin 9) := leftInput i j || decide (i = j)

theorem witnesses : ∀ i : Fin 9, target (leftInput i) ≠ target (rightInput i) ∧
    ∀ j : Fin 11, j.val ≠ i.val →
      (start (leftInput i)).getD j.val false = (start (rightInput i)).getD j.val false := by decide +kernel

def agree (i : Nat) (x y : List Bool) := x.length = y.length ∧
  ∀ j, j ≠ i → x.getD j false = y.getD j false

theorem after_two (i : Fin 9) : agree i.val (start (leftInput i)) (start (rightInput i)) := by
  constructor
  · simp [start,step]
  intro j ne
  by_cases lt : j < 11
  · exact (witnesses i).2 ⟨j,lt⟩ ne
  · rw [List.getD_eq_default,List.getD_eq_default] <;> simp [start,step] <;> omega

theorem keep (gs : List Gate) (i : Nat) (x y : List Bool) (h : agree i x y)
    (miss : i ∉ gs.flatMap Gate.inputs) : agree i (gs.foldl step x) (gs.foldl step y) := by
  induction gs generalizing x y with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.flatMap_cons,List.mem_append,not_or] at miss
    apply ih _ _ _ miss.2
    have eq : (g.inputs.map fun j => x.getD j false) = (g.inputs.map fun j => y.getD j false) := by
      apply List.map_congr_left
      intro j hj; exact h.2 j (fun e => miss.1 (e ▸ hj))
    refine ⟨by simp [step,h.1],?_⟩
    intro j ne
    by_cases lt : j < x.length
    · exact (List.getD_append _ _ _ _ lt).trans ((h.2 j ne).trans (List.getD_append _ _ _ _ (h.1 ▸ lt)).symm)
    · unfold step
      rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by have := h.1; omega),eq,h.1]

theorem raw_reads (c : Circuit) (gs : List Gate) (shape : c.gates = firstGate::secondGate::gs)
    (last : c.output+1 = 9+c.size) (correct : ∀ x, c.eval (List.ofFn x) = target x) :
    ∀ i : Fin 9, i.val ∈ gs.flatMap Gate.inputs := by
  intro i
  by_contra absent
  have same := keep gs i.val _ _ (after_two i) absent
  have far : c.output ≠ i.val := by simp [Circuit.size,shape] at last; omega
  apply (witnesses i).1
  rw [← correct,← correct]
  unfold Circuit.eval Circuit.wires
  rw [shape]
  exact same.2 c.output far

theorem slots (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2*gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have a := h g (by simp)
    have b := ih (fun x hx => h x (by simp [hx]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons]; omega

theorem lower (c : Circuit) (fan : FanInTwo c) (correct : ∀ x, c.eval (List.ofFn x) = target x)
    (last : c.output+1 = 9+c.size)
    (live : ∀ j : Fin c.gates.length, j.val+1 < c.gates.length →
      ∃ k : Fin c.gates.length, j.val < k.val ∧ 9+j.val ∈ (c.gates.get k).inputs)
    (one : c.gates.head? = some firstGate) (two : c.gates.tail.head? = some secondGate) :
    12 ≤ c.size := by
  obtain ⟨gs,shape⟩ : ∃ gs, c.gates = firstGate::secondGate::gs := by
    cases h : c.gates with
    | nil => simp [h] at one
    | cons a rest =>
      cases rest with
      | nil => simp [h] at two
      | cons b gs => simp [h] at one two; exact ⟨gs,by simp [one,two]⟩
  have reads := raw_reads c gs shape last correct
  have len : c.gates.length = gs.length+2 := by simp [shape]
  have all : Finset.range (gs.length+10) ⊆ (gs.flatMap Gate.inputs).toFinset := by
    intro j hj; apply List.mem_toFinset.mpr
    have bound := Finset.mem_range.mp hj
    by_cases small : j < 9
    · exact reads ⟨j,small⟩
    · let i : Fin c.gates.length := ⟨j-9,by omega⟩
      obtain ⟨k,gt,used⟩ := live i (by dsimp [i]; omega)
      have uses : j ∈ (c.gates.get k).inputs := by simpa [i,Nat.add_sub_of_le (by omega : 9 ≤ j)] using used
      let g := c.gates.get k
      change j ∈ g.inputs at uses
      have mem : g ∈ firstGate::secondGate::gs := shape ▸ List.get_mem c.gates k
      rcases List.mem_cons.mp mem with a|m
      · rw [a] at uses; simp [firstGate] at uses; omega
      · rcases List.mem_cons.mp m with a|m
        · rw [a] at uses; simp [secondGate] at uses; omega
        · exact List.mem_flatMap.mpr ⟨_,m,uses⟩
  have bd := Finset.card_le_card all
  rw [Finset.card_range] at bd
  have th := List.toFinset_card_le (l := gs.flatMap Gate.inputs)
  have sl := slots gs (fun g hg => (fan g (by simp [shape,hg])).2)
  change 12 ≤ c.gates.length
  omega

end PEqualNP.Outside.L_meta_27733_aux


theorem PEqualNP.Outside.L_meta_27733 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 7]⟩)) := by
  rintro ⟨c, fan, small, correct, last, _, _, live, first, second⟩
  have bound := PEqualNP.Outside.L_meta_27733_aux.lower c fan correct last live first second
  omega
