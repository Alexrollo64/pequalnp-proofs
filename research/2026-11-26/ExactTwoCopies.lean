import DisjointCopies

namespace Alexrollo64.ExactTwoCopies
open Alexrollo64.DisjointCopies (graph)
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- Wire 22 is row 9 OR columns 1, 2 and 3. Its two uses share all three gates. -/
def witness : Circuit := ⟨[
  ⟨.or, [11, 12]⟩,
  ⟨.or, [20, 13]⟩,
  ⟨.or, [21, 9]⟩,
  ⟨.or, [7, 10]⟩,
  ⟨.or, [2, 15]⟩,
  ⟨.and, [23, 24]⟩,
  ⟨.or, [4, 19]⟩,
  ⟨.or, [14, 22]⟩,
  ⟨.and, [26, 27]⟩,
  ⟨.or, [25, 28]⟩,
  ⟨.or, [3, 16]⟩,
  ⟨.or, [30, 17]⟩,
  ⟨.or, [31, 18]⟩,
  ⟨.or, [8, 22]⟩,
  ⟨.and, [32, 33]⟩,
  ⟨.or, [29, 34]⟩], 35⟩

theorem size_witness : witness.size = 16 := rfl

theorem upper : RepSizeAtMost (graph 2) 16 := by
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem exact_budget (n : Nat) : RepSizeAtMost (graph 2) n ↔ 16 ≤ n := by
  constructor
  · intro h
    have lb := DisjointCopies.lower 2 n h
    omega
  · intro hn
    obtain ⟨c,legal,size,correct⟩ := upper
    exact ⟨c,legal,size.trans hn,correct⟩

/-- The pair witness and a separate eight-gate copy, joined by one OR. -/
def three : Circuit := ⟨[
  ⟨.or, [16, 17]⟩,
  ⟨.or, [30, 18]⟩,
  ⟨.or, [31, 9]⟩,
  ⟨.or, [7, 15]⟩,
  ⟨.or, [2, 20]⟩,
  ⟨.and, [33, 34]⟩,
  ⟨.or, [4, 24]⟩,
  ⟨.or, [19, 32]⟩,
  ⟨.and, [36, 37]⟩,
  ⟨.or, [35, 38]⟩,
  ⟨.or, [3, 21]⟩,
  ⟨.or, [40, 22]⟩,
  ⟨.or, [41, 23]⟩,
  ⟨.or, [8, 32]⟩,
  ⟨.and, [42, 43]⟩,
  ⟨.or, [39, 44]⟩,
  ⟨.or, [26, 27]⟩,
  ⟨.or, [46, 28]⟩,
  ⟨.or, [13, 14]⟩,
  ⟨.and, [47, 48]⟩,
  ⟨.and, [14, 29]⟩,
  ⟨.and, [12, 25]⟩,
  ⟨.or, [49, 50]⟩,
  ⟨.or, [52, 51]⟩,
  ⟨.or, [45, 53]⟩], 54⟩

set_option maxHeartbeats 2000000 in
theorem three_bounds : RepSizeAtMost (graph 3) 25 ∧ ¬ RepSizeAtMost (graph 3) 23 := by
  constructor
  · refine ⟨three, ?_, by decide, by decide +kernel⟩
    intro g hg
    simp only [three, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro h
    have lb := DisjointCopies.lower 3 23 h
    omega

#print axioms three_bounds
#print axioms exact_budget
end Alexrollo64.ExactTwoCopies
