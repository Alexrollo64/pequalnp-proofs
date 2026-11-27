import TwentyTests
namespace Alexrollo64.TwentyCounterexample
open Alexrollo64.EdgeEdits Alexrollo64.TwentyTests
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- A circuit found by SAT on the proposed 20 tests. -/
def cand : Circuit := ⟨[
  ⟨.or, [11, 12]⟩,
  ⟨.or, [9, 13]⟩,
  ⟨.or, [20, 21]⟩,
  ⟨.or, [3, 19]⟩,
  ⟨.or, [15, 22]⟩,
  ⟨.or, [4, 10]⟩,
  ⟨.or, [16, 25]⟩,
  ⟨.or, [7, 17]⟩,
  ⟨.and, [23, 24]⟩,
  ⟨.or, [2, 8]⟩,
  ⟨.or, [18, 26]⟩,
  ⟨.or, [28, 30]⟩,
  ⟨.or, [27, 31]⟩,
  ⟨.or, [14, 24]⟩,
  ⟨.or, [29, 33]⟩,
  ⟨.and, [32, 34]⟩], 35⟩

theorem legal : Monotone2 cand ∧ cand.size = 16 := by
  have ok : Alexrollo64.TestPacking.valid cand = true := by decide +kernel
  refine ⟨?_, rfl⟩
  intro g hg
  have hh := List.all_eq_true.mp ok g hg
  obtain ⟨op,ins⟩ := g
  cases op <;> simp_all [Alexrollo64.TestPacking.allowed]

set_option maxHeartbeats 20000000
set_option maxRecDepth 16384
def errors : Finset Cell := {(2, 6), (2, 7), (2, 8), (3, 5), (4, 5), (7, 1), (7, 2), (7, 3), (7, 4), (8, 0), (9, 0)}

theorem all_cells : ∀ p, (output cand p != truth p) = decide (p ∈ errors) := by decide +kernel
theorem passes : ∀ p ∈ suite20, output cand p = truth p := by decide +kernel
theorem error_count : errors.card = 11 := by decide +kernel
theorem incomplete : ¬ (∀ c : Circuit, Monotone2 c → c.size ≤ 16 →
    (∀ p ∈ suite20, output c p = truth p) → ∀ p, output c p = truth p) := by
  intro all
  have no : output cand (2,6) ≠ truth (2,6) := by decide +kernel
  exact no (all _ legal.1 (le_of_eq legal.2) passes _)
#print axioms incomplete
#print axioms all_cells
end Alexrollo64.TwentyCounterexample
