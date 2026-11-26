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

/-- A binary gate copying one wire; the two selected parents coincide. -/
def copyWire (i : Nat) : Gate := ⟨.and,[i,i]⟩

def appendCopy (n : Nat) (C : Circuit) : Circuit :=
  ⟨C.gates ++ [copyWire C.output], n + C.size⟩

theorem appendCopy_eval (n : Nat) (C : Circuit) (x : List Bool) (hx : x.length = n) :
    (appendCopy n C).eval x = C.eval x := by
  let w := C.wires x
  have len : w.length = n + C.size := by
    unfold w Circuit.wires
    rw [fold_length, hx]
    rfl
  have step : (appendCopy n C).wires x = w ++ [C.eval x && C.eval x] := by
    simp [appendCopy, Circuit.wires, List.foldl_append, copyWire, GateOp.eval, Circuit.eval, w]
  unfold Circuit.eval at ⊢
  rw [step, Bool.and_self]
  change (w ++ [_]).getD (n + C.size) false = _
  rw [← len]
  simp [Circuit.eval]

/-- Padding by binary copy gates preserves any gate condition that permits such copies. -/
theorem pad_to_budget (n : Nat) (C : Circuit) (budget : Nat) (small : C.size ≤ budget)
    (last : C.output + 1 = n + C.size) (P : Gate → Prop)
    (hc : ∀ g ∈ C.gates, P g) (copyOK : ∀ i, P (copyWire i)) :
    ∃ D : Circuit, D.size = budget ∧ D.output + 1 = n + budget ∧
      (∀ g ∈ D.gates, P g) ∧ ∀ x : List Bool, x.length = n → D.eval x = C.eval x := by
  induction budget, small using Nat.le_induction with
  | base => exact ⟨C,rfl,last,hc,fun _ _ => rfl⟩
  | succ b _ ih =>
    obtain ⟨D, len, _, good, same⟩ := ih
    refine ⟨appendCopy n D, ?_, ?_, ?_, ?_⟩
    · change (D.gates ++ [_]).length = b+1
      simpa [Circuit.size] using len
    · change n + D.size + 1 = n + (b+1)
      omega
    · intro g hg
      change g ∈ D.gates ++ [_] at hg
      rcases List.mem_append.mp hg with h | h
      · exact good g h
      · simpa using (List.mem_singleton.mp h ▸ copyOK D.output : P g)
    · intro x hx
      exact (appendCopy_eval n D x hx).trans (same x hx)

/-- A solution below budget has an equivalent exact-budget last-output solution. -/
theorem exact_budget_solution (C : Circuit) (t : Nat × Nat) (ht : t ∈ targets)
    (solves : ∀ r, C.eval (List.ofFn (packedInput r)) = t.2.testBit r.val)
    (budget : Nat) (small : C.size ≤ budget) (P : Gate → Prop)
    (good : ∀ g ∈ C.gates, P g) (copyOK : ∀ i, P (copyWire i)) :
    ∃ D : Circuit, D.size = budget ∧ D.output + 1 = 6 + budget ∧
      (∀ g ∈ D.gates, P g) ∧ ∀ x : List Bool, x.length = 6 → D.eval x = C.eval x := by
  obtain ⟨E, le, last, sub, eq⟩ := last_gate_solution C t ht solves
  obtain ⟨D, size, out, ok, eq'⟩ := pad_to_budget 6 E budget (le.trans small) last P
    (fun g hg => good g (sub g hg)) copyOK
  exact ⟨D, size, out, ok, fun x hx => (eq' x hx).trans (eq x hx)⟩

#print axioms exact_budget_solution
#print axioms pad_to_budget

namespace Normalization

/- Normalization primitives and proofs from open-goat/pequalnp-proofs, Apache-2.0,
   L_meta_10422.lean at 04bd0cdce6413f75e63b6aa2a79097db6c65069c. -/
def trimInputs (cap : ℕ) (xs : List ℕ) : List ℕ :=
  xs.filter (fun i => decide (i < cap))

def gate (cap : ℕ) (g : Gate) : Gate :=
  match g.op with
  | .and => if ∀ i ∈ g.inputs, i < cap then g else ⟨.or,[]⟩
  | .or => ⟨.or,trimInputs cap g.inputs⟩
  | .not => ⟨.not,trimInputs cap (g.inputs.take 1)⟩
  | _ => ⟨.or,[]⟩

def gates (cap : ℕ) : List Gate → List Gate
  | [] => []
  | g :: gs => gate cap g :: gates (cap+1) gs

def norm (n : ℕ) (C : Circuit) : Circuit := ⟨gates n C.gates,C.output⟩

def allowed (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def legal (cap : ℕ) (g : Gate) : Prop :=
  allowed g ∧ (∀ i ∈ g.inputs, i < cap) ∧ (g.op=.not → g.inputs.length ≤ 1)

theorem trimInputs_length (cap : ℕ) (xs : List ℕ) :
    (trimInputs cap xs).length ≤ xs.length := List.length_filter_le _ _

theorem trimInputs_bound {cap : ℕ} {xs : List ℕ} {i : ℕ} (mem : i∈trimInputs cap xs) :
    i<cap := of_decide_eq_true (List.mem_filter.mp mem).2

theorem gate_legal (cap : ℕ) (g : Gate) (small : g.inputs.length≤2) : legal cap (gate cap g) := by
  cases g with
  | mk op xs =>
    change xs.length≤2 at small
    cases op with
    | and =>
      change legal cap (if ∀ i∈xs, i<cap then (⟨.and,xs⟩ : Gate) else ⟨.or,[]⟩)
      split
      · rename_i good
        exact ⟨⟨by simp,small⟩,good,by simp⟩
      · simp [legal,allowed]
    | or =>
      refine ⟨⟨by simp [gate],(trimInputs_length _ _).trans small⟩,
        fun _ => trimInputs_bound,by simp [gate]⟩
    | not =>
      have len : (trimInputs cap (xs.take 1)).length≤1 :=
        (trimInputs_length _ _).trans (by simp [List.length_take])
      exact ⟨⟨by simp [gate],len.trans (by decide)⟩,
        fun _ => trimInputs_bound,fun _ => len⟩
    | mod m => simp [gate,legal,allowed]
    | maj => simp [gate,legal,allowed]

def gateValue (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map (fun i => w.getD i false))

theorem gate_value (w : List Bool) (g : Gate) (good : allowed g) :
    gateValue w (gate w.length g) = gateValue w g := by
  rcases g with ⟨op,xs⟩
  have hop := good.1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  change op = .and ∨ op = .or ∨ op = .not at hop
  rcases hop with rfl | rfl | rfl
  · change gateValue w
      (if ∀ i∈xs, i<w.length then (⟨.and,xs⟩ : Gate) else ⟨.or,[]⟩) =
      gateValue w ⟨.and,xs⟩
    split
    · rfl
    · rename_i bad
      change false = (xs.map fun i => w.getD i false).all id
      symm
      apply Bool.eq_false_iff.mpr
      intro on
      apply bad
      intro i mem
      by_contra beyond
      have ix := List.all_eq_true.mp on (w.getD i false) (List.mem_map.mpr ⟨i,mem,rfl⟩)
      have miss : w.getD i false=false := List.getD_eq_default _ _ (by omega)
      rw [id_eq,miss] at ix
      contradiction
  · change ((trimInputs w.length xs).map fun i => w.getD i false).any id =
      (xs.map fun i => w.getD i false).any id
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_map,List.any_eq_true,Function.comp_apply,id_eq,trimInputs,
      List.mem_filter,decide_eq_true_eq]
    constructor
    · rintro ⟨i,⟨mem,_⟩,val⟩
      exact ⟨i,mem,val⟩
    · rintro ⟨i,mem,val⟩
      refine ⟨i,⟨mem,?_⟩,val⟩
      by_contra beyond
      have miss : w.getD i false=false := List.getD_eq_default _ _ (by omega)
      rw [miss] at val
      contradiction
  · cases xs with
    | nil => rfl
    | cons i xs =>
      by_cases keep : i<w.length
      · simp [gateValue,gate,trimInputs,GateOp.eval,keep]
      · have miss : w.getD i false=false := List.getD_eq_default _ _ (by omega)
        simp [gateValue,gate,trimInputs,GateOp.eval,keep]

theorem gates_length (cap : ℕ) (gs : List Gate) : (gates cap gs).length=gs.length := by
  induction gs generalizing cap with
  | nil => rfl
  | cons g gs ih => simp [gates,ih]

theorem gates_get (cap : ℕ) (gs : List Gate) (j : ℕ) (hj : j<gs.length) :
    (gates cap gs)[j]'(by rwa [gates_length]) = gate (cap+j) gs[j] := by
  induction gs generalizing cap j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero => simp [gates]
    | succ j =>
      simpa [gates,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        (ih (cap+1) j (Nat.lt_of_succ_lt_succ hj))

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun v g => v ++ [gateValue v g]) w

theorem run_length (gs : List Gate) (w : List Bool) : (run gs w).length=w.length+gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (w ++ [gateValue w g])).length = _
    rw [ih]
    simp [Nat.add_comm,Nat.add_left_comm]

theorem gates_run (gs : List Gate) (good : ∀ g∈gs, allowed g) (w : List Bool) :
    run (gates w.length gs) w=run gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have valid := good g (by simp)
    change run (gates (w.length+1) gs) (w ++ [gateValue w (gate w.length g)]) =
      run gs (w ++ [gateValue w g])
    rw [gate_value _ _ valid]
    have len : (w++[gateValue w g]).length=w.length+1 := by simp
    rw [←len]
    exact ih (fun g' mem => good g' (List.mem_cons_of_mem _ mem)) _


/-- Exact-budget form with no references to a future or nonexistent wire.
Constants are still allowed in the form of gates with empty input lists. -/
theorem exact_budget_legal (C : Circuit) (t : Nat × Nat) (ht : t ∈ targets)
    (solves : ∀ r, C.eval (List.ofFn (packedInput r)) = t.2.testBit r.val)
    (budget : Nat) (small : C.size ≤ budget) (good : ∀ g ∈ C.gates, allowed g) :
    ∃ D : Circuit, D.size = budget ∧ D.output + 1 = 6 + budget ∧
      (∀ j (hj : j < D.gates.length), legal (6+j) D.gates[j]) ∧
      ∀ x : List Bool, x.length = 6 → D.eval x = C.eval x := by
  have copyOK (i : Nat) : allowed (copyWire i) := by simp [allowed,copyWire]
  obtain ⟨E, size, last, ops, eq⟩ := exact_budget_solution C t ht solves budget small allowed good copyOK
  let D := norm 6 E
  have len : D.gates.length = E.gates.length := gates_length _ _
  refine ⟨D,len.trans size,last,?_,?_⟩
  · intro j hj
    have hj' : j < E.gates.length := by rwa [←len]
    have hwire : D.gates[j] = gate (6+j) E.gates[j] := gates_get 6 E.gates j hj'
    rw [hwire]
    exact gate_legal _ _ (ops _ (List.getElem_mem hj')).2
  · intro x hx
    rw [←eq x hx]
    change (run (gates 6 E.gates) x).getD E.output false = (run E.gates x).getD E.output false
    rw [←hx,gates_run _ ops]
#print axioms exact_budget_legal
end Normalization
end Alexrollo64.TwoLitTables
