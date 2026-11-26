import PEqualNP.Defs
import PEqualNP.Library.Helpers.ReplayColExpr

namespace Alexrollo64.MatrixProduct18919Reference_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Library.Helpers.ReplayCol PEqualNP.Library.Helpers.ReplayColExpr

def circuit : Circuit :=
  ⟨[
    ⟨.and, [4, 13]⟩,
    ⟨.and, [3, 10]⟩,
    ⟨.and, [5, 16]⟩,
    ⟨.or, [18, 19]⟩,
    ⟨.or, [21, 20]⟩,
    ⟨.and, [6, 11]⟩,
    ⟨.and, [7, 14]⟩,
    ⟨.and, [8, 17]⟩,
    ⟨.or, [23, 24]⟩,
    ⟨.or, [26, 25]⟩,
    ⟨.and, [1, 12]⟩,
    ⟨.and, [0, 9]⟩,
    ⟨.and, [2, 15]⟩,
    ⟨.or, [28, 29]⟩,
    ⟨.or, [31, 30]⟩,
    ⟨.and, [6, 9]⟩,
    ⟨.and, [7, 12]⟩,
    ⟨.and, [8, 15]⟩,
    ⟨.or, [33, 34]⟩,
    ⟨.or, [36, 35]⟩,
    ⟨.and, [5, 15]⟩,
    ⟨.and, [3, 9]⟩,
    ⟨.and, [4, 12]⟩,
    ⟨.or, [38, 39]⟩,
    ⟨.or, [41, 40]⟩,
    ⟨.and, [2, 16]⟩,
    ⟨.and, [1, 13]⟩,
    ⟨.and, [0, 10]⟩,
    ⟨.or, [43, 44]⟩,
    ⟨.or, [46, 45]⟩,
    ⟨.and, [8, 16]⟩,
    ⟨.and, [6, 10]⟩,
    ⟨.and, [7, 13]⟩,
    ⟨.or, [48, 49]⟩,
    ⟨.or, [51, 50]⟩,
    ⟨.and, [3, 11]⟩,
    ⟨.and, [4, 14]⟩,
    ⟨.and, [5, 17]⟩,
    ⟨.or, [53, 54]⟩,
    ⟨.or, [56, 55]⟩,
    ⟨.and, [1, 14]⟩,
    ⟨.and, [2, 17]⟩,
    ⟨.and, [0, 11]⟩,
    ⟨.or, [58, 59]⟩,
    ⟨.or, [61, 60]⟩
  ], 27⟩

def outputs (v : Fin 9) : ℕ := ![32, 47, 62, 42, 22, 57, 37, 52, 27] v

theorem fanin : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem wire0 : ∀ x : Fin 18 → Bool,
    (circuit.wires (List.ofFn x)).getD (outputs 0) false = (x 0 && x 9 || x 1 && x 12 || x 2 && x 15) := by
  apply wire_of_expr (C := circuit) (n := 18) (f := fun x => x 0 && x 9 || x 1 && x 12 || x 2 && x 15)
    (outputs 0) (((inCol 18 0) &&& (inCol 18 9)) ||| ((inCol 18 1) &&& (inCol 18 12)) ||| ((inCol 18 2) &&& (inCol 18 15)))
  · decide
  · decide +kernel
  · intro x
    simp [Nat.testBit_or, Nat.testBit_and, inCol_bit]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem wire1 : ∀ x : Fin 18 → Bool,
    (circuit.wires (List.ofFn x)).getD (outputs 1) false = (x 0 && x 10 || x 1 && x 13 || x 2 && x 16) := by
  apply wire_of_expr (C := circuit) (n := 18) (f := fun x => x 0 && x 10 || x 1 && x 13 || x 2 && x 16)
    (outputs 1) (((inCol 18 0) &&& (inCol 18 10)) ||| ((inCol 18 1) &&& (inCol 18 13)) ||| ((inCol 18 2) &&& (inCol 18 16)))
  · decide
  · decide +kernel
  · intro x
    simp [Nat.testBit_or, Nat.testBit_and, inCol_bit]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem wire2 : ∀ x : Fin 18 → Bool,
    (circuit.wires (List.ofFn x)).getD (outputs 2) false = (x 0 && x 11 || x 1 && x 14 || x 2 && x 17) := by
  apply wire_of_expr (C := circuit) (n := 18) (f := fun x => x 0 && x 11 || x 1 && x 14 || x 2 && x 17)
    (outputs 2) (((inCol 18 0) &&& (inCol 18 11)) ||| ((inCol 18 1) &&& (inCol 18 14)) ||| ((inCol 18 2) &&& (inCol 18 17)))
  · decide
  · decide +kernel
  · intro x
    simp [Nat.testBit_or, Nat.testBit_and, inCol_bit]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem wire3 : ∀ x : Fin 18 → Bool,
    (circuit.wires (List.ofFn x)).getD (outputs 3) false = (x 3 && x 9 || x 4 && x 12 || x 5 && x 15) := by
  apply wire_of_expr (C := circuit) (n := 18) (f := fun x => x 3 && x 9 || x 4 && x 12 || x 5 && x 15)
    (outputs 3) (((inCol 18 3) &&& (inCol 18 9)) ||| ((inCol 18 4) &&& (inCol 18 12)) ||| ((inCol 18 5) &&& (inCol 18 15)))
  · decide
  · decide +kernel
  · intro x
    simp [Nat.testBit_or, Nat.testBit_and, inCol_bit]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem wire4 : ∀ x : Fin 18 → Bool,
    (circuit.wires (List.ofFn x)).getD (outputs 4) false = (x 3 && x 10 || x 4 && x 13 || x 5 && x 16) := by
  apply wire_of_expr (C := circuit) (n := 18) (f := fun x => x 3 && x 10 || x 4 && x 13 || x 5 && x 16)
    (outputs 4) (((inCol 18 3) &&& (inCol 18 10)) ||| ((inCol 18 4) &&& (inCol 18 13)) ||| ((inCol 18 5) &&& (inCol 18 16)))
  · decide
  · decide +kernel
  · intro x
    simp [Nat.testBit_or, Nat.testBit_and, inCol_bit]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem wire5 : ∀ x : Fin 18 → Bool,
    (circuit.wires (List.ofFn x)).getD (outputs 5) false = (x 3 && x 11 || x 4 && x 14 || x 5 && x 17) := by
  apply wire_of_expr (C := circuit) (n := 18) (f := fun x => x 3 && x 11 || x 4 && x 14 || x 5 && x 17)
    (outputs 5) (((inCol 18 3) &&& (inCol 18 11)) ||| ((inCol 18 4) &&& (inCol 18 14)) ||| ((inCol 18 5) &&& (inCol 18 17)))
  · decide
  · decide +kernel
  · intro x
    simp [Nat.testBit_or, Nat.testBit_and, inCol_bit]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem wire6 : ∀ x : Fin 18 → Bool,
    (circuit.wires (List.ofFn x)).getD (outputs 6) false = (x 6 && x 9 || x 7 && x 12 || x 8 && x 15) := by
  apply wire_of_expr (C := circuit) (n := 18) (f := fun x => x 6 && x 9 || x 7 && x 12 || x 8 && x 15)
    (outputs 6) (((inCol 18 6) &&& (inCol 18 9)) ||| ((inCol 18 7) &&& (inCol 18 12)) ||| ((inCol 18 8) &&& (inCol 18 15)))
  · decide
  · decide +kernel
  · intro x
    simp [Nat.testBit_or, Nat.testBit_and, inCol_bit]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem wire7 : ∀ x : Fin 18 → Bool,
    (circuit.wires (List.ofFn x)).getD (outputs 7) false = (x 6 && x 10 || x 7 && x 13 || x 8 && x 16) := by
  apply wire_of_expr (C := circuit) (n := 18) (f := fun x => x 6 && x 10 || x 7 && x 13 || x 8 && x 16)
    (outputs 7) (((inCol 18 6) &&& (inCol 18 10)) ||| ((inCol 18 7) &&& (inCol 18 13)) ||| ((inCol 18 8) &&& (inCol 18 16)))
  · decide
  · decide +kernel
  · intro x
    simp [Nat.testBit_or, Nat.testBit_and, inCol_bit]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem wire8 : ∀ x : Fin 18 → Bool,
    (circuit.wires (List.ofFn x)).getD (outputs 8) false = (x 6 && x 11 || x 7 && x 14 || x 8 && x 17) := by
  apply wire_of_expr (C := circuit) (n := 18) (f := fun x => x 6 && x 11 || x 7 && x 14 || x 8 && x 17)
    (outputs 8) (((inCol 18 6) &&& (inCol 18 11)) ||| ((inCol 18 7) &&& (inCol 18 14)) ||| ((inCol 18 8) &&& (inCol 18 17)))
  · decide
  · decide +kernel
  · intro x
    simp [Nat.testBit_or, Nat.testBit_and, inCol_bit]

end Alexrollo64.MatrixProduct18919Reference_aux

theorem Alexrollo64.MatrixProduct18919Reference : (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin 9 → ℕ), PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 45 ∧ ∀ x : Fin 18 → Bool, (C.wires (List.ofFn x)).getD (o 0) false = (x 0 && x 9 || x 1 && x 12 || x 2 && x 15) ∧ (C.wires (List.ofFn x)).getD (o 1) false = (x 0 && x 10 || x 1 && x 13 || x 2 && x 16) ∧ (C.wires (List.ofFn x)).getD (o 2) false = (x 0 && x 11 || x 1 && x 14 || x 2 && x 17) ∧ (C.wires (List.ofFn x)).getD (o 3) false = (x 3 && x 9 || x 4 && x 12 || x 5 && x 15) ∧ (C.wires (List.ofFn x)).getD (o 4) false = (x 3 && x 10 || x 4 && x 13 || x 5 && x 16) ∧ (C.wires (List.ofFn x)).getD (o 5) false = (x 3 && x 11 || x 4 && x 14 || x 5 && x 17) ∧ (C.wires (List.ofFn x)).getD (o 6) false = (x 6 && x 9 || x 7 && x 12 || x 8 && x 15) ∧ (C.wires (List.ofFn x)).getD (o 7) false = (x 6 && x 10 || x 7 && x 13 || x 8 && x 16) ∧ (C.wires (List.ofFn x)).getD (o 8) false = (x 6 && x 11 || x 7 && x 14 || x 8 && x 17)) := by
  refine ⟨Alexrollo64.MatrixProduct18919Reference_aux.circuit, Alexrollo64.MatrixProduct18919Reference_aux.outputs, Alexrollo64.MatrixProduct18919Reference_aux.fanin, by decide, ?_⟩
  intro x
  exact ⟨Alexrollo64.MatrixProduct18919Reference_aux.wire0 x, Alexrollo64.MatrixProduct18919Reference_aux.wire1 x, Alexrollo64.MatrixProduct18919Reference_aux.wire2 x, Alexrollo64.MatrixProduct18919Reference_aux.wire3 x, Alexrollo64.MatrixProduct18919Reference_aux.wire4 x, Alexrollo64.MatrixProduct18919Reference_aux.wire5 x, Alexrollo64.MatrixProduct18919Reference_aux.wire6 x, Alexrollo64.MatrixProduct18919Reference_aux.wire7 x, Alexrollo64.MatrixProduct18919Reference_aux.wire8 x⟩
