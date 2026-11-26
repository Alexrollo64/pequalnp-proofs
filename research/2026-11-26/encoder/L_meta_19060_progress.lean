import PEqualNP.Defs

namespace Alexrollo64.Encoder19060
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def grid : Circuit :=
  ⟨[⟨.or, [0, 1]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.or, [16, 17]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [19, 20]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [22, 23]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [14, 15]⟩,
    ⟨.or, [25, 26]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.or, [8, 12]⟩,
    ⟨.or, [28, 29]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.or, [9, 13]⟩,
    ⟨.or, [31, 32]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.or, [10, 14]⟩,
    ⟨.or, [34, 35]⟩,
    ⟨.or, [3, 7]⟩,
    ⟨.or, [11, 15]⟩,
    ⟨.or, [37, 38]⟩,
    ⟨.or, [18, 24]⟩,
    ⟨.or, [21, 27]⟩,
    ⟨.or, [18, 21]⟩,
    ⟨.or, [24, 27]⟩,
    ⟨.or, [30, 36]⟩,
    ⟨.or, [33, 39]⟩,
    ⟨.or, [30, 33]⟩,
    ⟨.or, [36, 39]⟩], 47⟩

def positiveWire (v : Fin 4) : ℕ := ![45, 47, 41, 43] v
def negativeWire (v : Fin 4) : ℕ := ![44, 46, 40, 42] v
def inputPattern (p : Fin 16) := List.ofFn (fun q : Fin 16 => decide (q = p))
theorem grid_size : grid.size = 32 := by decide
theorem grid_mono : Monotone2 grid := by
  intro g hg
  simp only [grid, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem grid_outputs : ∀ v : Fin 4, ∀ p : Fin 16,
    (grid.wires (inputPattern p)).getD (positiveWire v) false = p.val.testBit v.val ∧
    (grid.wires (inputPattern p)).getD (negativeWire v) false = !(p.val.testBit v.val) := by
  decide +kernel

-- In the transposed incidence table each word selects four of the eight signed literals.
def word (p : Fin 16) : Finset (Fin 8) :=
  Finset.univ.filter (fun l => p.val.testBit (l.val / 2) = decide (l.val % 2 = 1))

set_option maxHeartbeats 0 in
theorem support_capacity : ∀ S : Finset (Fin 8), 2 ≤ S.card →
    (Finset.univ.filter (fun p : Fin 16 => S ⊆ word p)).card ≤ 4 := by
  decide +kernel

-- The hypotheses describe intermediate supports in the transposed network.
-- This lemma proves the counting step only.
theorem eight_intermediates {k : ℕ} (supports : Fin k → Finset (Fin 8))
    (nontrivial : ∀ j, 2 ≤ (supports j).card)
    (uses : ∀ p : Fin 16, 2 ≤ (Finset.univ.filter (fun j => supports j ⊆ word p)).card) :
    8 ≤ k := by
  classical
  have cardBool {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P] :
      (Finset.univ.filter P).card = ∑ a, (if P a then 1 else 0 : ℕ) := by
    simpa only [Nat.cast_id] using (Finset.natCast_card_filter (R := ℕ) P Finset.univ)
  have total : 16 * 2 ≤ k * 4 := by
    calc
      16 * 2 = ∑ _ : Fin 16, (2 : ℕ) := by decide
      _ ≤ ∑ p : Fin 16, (Finset.univ.filter (fun j => supports j ⊆ word p)).card :=
        Finset.sum_le_sum (fun p _ => uses p)
      _ = ∑ j : Fin k, (Finset.univ.filter (fun p : Fin 16 => supports j ⊆ word p)).card := by
        simp only [cardBool]
        exact Finset.sum_comm
      _ ≤ ∑ _ : Fin k, (4 : ℕ) :=
        Finset.sum_le_sum (fun j _ => support_capacity (supports j) (nontrivial j))
      _ = k * 4 := by simp
  omega

end Alexrollo64.Encoder19060

