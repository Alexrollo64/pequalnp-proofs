import PEqualNP.Defs.CircuitLowerBounds

namespace Alexrollo64.TwoLitTables

def columnMasks : List Nat := [63, 1986, 30852, 233736, 860688, 1721376]

def packedInput (r : Fin 21) (k : Fin 6) : Bool :=
  (columnMasks.getD k.val 0).testBit r.val

def pairInput (i j k : Fin 6) : Bool := decide (k = i ∨ k = j)

def offset (i j : Fin 6) : Nat := 6 * min i.val j.val + max i.val j.val

def packedRow (i j : Fin 6) : Fin 21 :=
  let p := min i.val j.val
  let q := max i.val j.val
  ⟨(6*p - p*(p-1)/2 + (q-p)) % 21, Nat.mod_lt _ (by decide)⟩

theorem input_agreement : ∀ i j k, packedInput (packedRow i j) k = pairInput i j k := by decide +kernel

theorem covers_every_row : ∀ r : Fin 21, ∃ i j : Fin 6, packedRow i j = r := by decide +kernel

def targets : List (Nat × Nat) :=
  [(34630324159,1351679),(270649275,310267),(36669,6077),(797,413)]

theorem output_agreement : ∀ t ∈ targets, ∀ i j : Fin 6,
    t.1.testBit (offset i j) = t.2.testBit (packedRow i j).val := by decide +kernel

/-- For any evaluator, the posted promise agrees exactly with the finite SAT target table. -/
theorem specification_iff (f : (Fin 6 → Bool) → Bool) (t : Nat × Nat) (ht : t ∈ targets) :
    (∀ i j, f (pairInput i j) = t.1.testBit (offset i j)) ↔
    (∀ r, f (packedInput r) = t.2.testBit r.val) := by
  have h (i j : Fin 6) : packedInput (packedRow i j) = pairInput i j :=
    funext (input_agreement i j)
  constructor
  · intro hp r
    obtain ⟨i,j,rfl⟩ := covers_every_row r
    rw [h, hp, output_agreement t ht]
  · intro hr i j
    rw [← h, hr, output_agreement t ht]

/-- Conditional truth-table clauses in synth-circuit.py for one gate on one row.
Selectors for its parents and the exactly-one operation constraint are separate. -/
def gateClauses (gAnd gOr gNot a b z : Bool) : Bool :=
  (!gAnd || !z || a) && (!gAnd || !z || b) && (!gAnd || z || !a || !b) &&
  (!gOr || z || !a) && (!gOr || z || !b) && (!gOr || !z || a || b) &&
  (!gNot || !z || !a) && (!gNot || z || a)

theorem gate_agreement : ∀ a b z : Bool,
    (gateClauses true false false a b z = true ↔ z = (a && b)) ∧
    (gateClauses false true false a b z = true ↔ z = (a || b)) ∧
    (gateClauses false false true a b z = true ↔ z = !a) := by decide +kernel

/-- Exactly one selected wire, together with the two mux clauses for every
parent, forces the selected bit on this row. -/
theorem selected_value {n : Nat} (pick : Fin n) (w : Fin n → Bool) (a : Bool) :
    (∀ k : Fin n,
      ((!decide (k = pick) || !a || w k) && (!decide (k = pick) || a || !w k)) = true) ↔
    a = w pick := by
  constructor
  · intro h
    have h' := h pick
    cases ha : a <;> cases hw : w pick <;> simp_all
  · intro h k
    by_cases eq : k = pick
    · subst k
      rw [h]
      cases w pick <;> simp
    · simp [eq]

theorem targets_nonconstant : ∀ t ∈ targets, ∃ r s : Fin 21,
    t.2.testBit r.val = true ∧ t.2.testBit s.val = false := by decide +kernel

/-- The promise in the four posted specifications, evaluated by the project's own circuit semantics. -/
theorem circuit_specification_iff (C : PEqualNP.CircuitLowerBounds.Circuit)
    (t : Nat × Nat) (ht : t ∈ targets) :
    (∀ i j : Fin 6, C.eval (List.ofFn (fun k => decide (k = i ∨ k = j))) =
      t.1.testBit (6 * min i.val j.val + max i.val j.val)) ↔
    (∀ r : Fin 21, C.eval (List.ofFn (packedInput r)) = t.2.testBit r.val) :=
  specification_iff (fun x => C.eval (List.ofFn x)) t ht

/-- Masks describe the coordinates needed on the one- or two-active promise only.
The low-order bit represents input 0. -/
def supports : List (Nat × Nat) := [(1351679,60),(310267,61),(6077,63),(413,47)]

def agreesOn (m : Nat) (r s : Fin 21) : Prop :=
  ∀ k : Fin 6, m.testBit k.val = true → packedInput r k = packedInput s k

instance (m : Nat) (r s : Fin 21) : Decidable (agreesOn m r s) :=
  inferInstanceAs (Decidable (∀ k : Fin 6, m.testBit k.val = true → packedInput r k = packedInput s k))

theorem sufficient_coordinates : ∀ e ∈ supports, ∀ r s : Fin 21,
    agreesOn e.2 r s → e.1.testBit r.val = e.1.testBit s.val := by decide +kernel

theorem required_coordinates : ∀ e ∈ supports, ∀ k : Fin 6, e.2.testBit k.val = true →
    ∃ r s : Fin 21, (∀ j : Fin 6, j ≠ k → packedInput r j = packedInput s j) ∧
      e.1.testBit r.val ≠ e.1.testBit s.val := by decide +kernel

theorem determining_mask_iff (e : Nat × Nat) (he : e ∈ supports) (m : Nat) :
    (∀ r s, agreesOn m r s → e.1.testBit r.val = e.1.testBit s.val) ↔
    (∀ k : Fin 6, e.2.testBit k.val = true → m.testBit k.val = true) := by
  constructor
  · intro determines k needed
    obtain ⟨r,s,same,distinct⟩ := required_coordinates e he k needed
    cases h : m.testBit k.val with
    | true => rfl
    | false =>
      apply False.elim
      apply distinct (determines r s ?_)
      intro j hj
      apply same j
      intro eq
      subst j
      simp [h] at hj
  · intro included r s h
    exact sufficient_coordinates e he r s (fun k hk => h k (included k hk))

open PEqualNP.CircuitLowerBounds

theorem no_input_column : ∀ t ∈ targets, ∀ k : Fin 6,
    ∃ r : Fin 21, packedInput r k ≠ t.2.testBit r.val := by decide +kernel

private theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]) w).length =
      w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
                    omega

private theorem fold_prefix (gs : List Gate) (w : List Bool) (i : Nat) (hi : i < w.length) :
    (gs.foldl (fun a g => a ++ [g.op.eval (g.inputs.map fun j => a.getD j false)]) w).getD i false =
      w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

/-- Each solution has an actual gate as its output. This also applies to unrestricted fan-in. -/
theorem output_is_gate (C : Circuit) (t : Nat × Nat) (ht : t ∈ targets)
    (solves : ∀ r, C.eval (List.ofFn (packedInput r)) = t.2.testBit r.val) :
    6 ≤ C.output ∧ C.output < 6 + C.size := by
  constructor
  · by_contra! h
    let k : Fin 6 := ⟨C.output,h⟩
    obtain ⟨r,hr⟩ := no_input_column t ht k
    apply hr
    rw [← solves]
    unfold Circuit.eval Circuit.wires
    rw [fold_prefix _ _ _ (by simpa using h)]
    have hh : C.output < (List.ofFn (packedInput r)).length := by simpa only [List.length_ofFn] using h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hh, Option.getD_some, List.getElem_ofFn]
  · by_contra! h
    obtain ⟨r,_,hr,_⟩ := targets_nonconstant t ht
    have bad : C.eval (List.ofFn (packedInput r)) = false := by
      apply List.getD_eq_default
      unfold Circuit.wires
      rw [fold_length, List.length_ofFn]
      exact h
    rw [solves,hr] at bad
    contradiction

/-- Discard every gate after the designated output while preserving evaluation. -/
theorem truncate_output (C : Circuit) (n : Nat)
    (lo : n ≤ C.output) (hi : C.output < n + C.size) :
    ∃ D : Circuit, D.size ≤ C.size ∧ D.output + 1 = n + D.size ∧
      D.gates = C.gates.take (C.output + 1 - n) ∧
      ∀ x : List Bool, x.length = n → D.eval x = C.eval x := by
  let k := C.output + 1 - n
  have hk : k ≤ C.gates.length := by unfold k; unfold Circuit.size at hi; omega
  have last : n + k = C.output + 1 := by unfold k; omega
  let D : Circuit := ⟨C.gates.take k, C.output⟩
  have len : D.size = k := by simp [D, Circuit.size, List.length_take, Nat.min_eq_left hk]
  refine ⟨D, len ▸ hk, ?_, rfl, ?_⟩
  · change C.output + 1 = n + D.size
    rw [len,last]
  · intro x hx
    have bound : C.output < (D.wires x).length := by
      unfold Circuit.wires
      rw [fold_length, hx]
      change C.output < n + D.size
      omega
    conv_rhs =>
      unfold Circuit.eval Circuit.wires
      rw [← List.take_append_drop k C.gates, List.foldl_append]
    exact (fold_prefix (C.gates.drop k) (D.wires x) C.output bound).symm

/-- The transformation retains every per-gate condition, including the project's fan-in constraint. -/
theorem last_gate_solution (C : Circuit) (t : Nat × Nat) (ht : t ∈ targets)
    (solves : ∀ r, C.eval (List.ofFn (packedInput r)) = t.2.testBit r.val) :
    ∃ D : Circuit, D.size ≤ C.size ∧ D.output + 1 = 6 + D.size ∧
      (∀ g ∈ D.gates, g ∈ C.gates) ∧
      (∀ x : List Bool, x.length = 6 → D.eval x = C.eval x) := by
  obtain ⟨lo, hi⟩ := output_is_gate C t ht solves
  obtain ⟨D, small, last, htake, same⟩ := truncate_output C 6 lo hi
  refine ⟨D, small, last, ?_, same⟩
  intro g hg
  rw [htake] at hg
  exact List.mem_of_mem_take hg

#print axioms last_gate_solution
#print axioms truncate_output
#print axioms output_is_gate
end Alexrollo64.TwoLitTables
