import EighteenTests

namespace Alexrollo64.SharedSuite
open Alexrollo64.EdgeEdits Alexrollo64.EighteenTests Alexrollo64.TestPacking
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def c0 : Circuit := ⟨[
  ⟨.or, [11, 9]⟩,
  ⟨.and, [10, 2]⟩,
  ⟨.and, [15, 7]⟩,
  ⟨.or, [19, 4]⟩,
  ⟨.or, [14, 20]⟩,
  ⟨.and, [23, 24]⟩,
  ⟨.or, [8, 20]⟩,
  ⟨.or, [13, 26]⟩,
  ⟨.or, [12, 27]⟩,
  ⟨.or, [18, 16]⟩,
  ⟨.or, [17, 29]⟩,
  ⟨.or, [3, 30]⟩,
  ⟨.and, [28, 31]⟩,
  ⟨.or, [25, 32]⟩,
  ⟨.or, [22, 33]⟩,
  ⟨.or, [21, 34]⟩], 35⟩

def c1 : Circuit := ⟨[
  ⟨.or, [4, 16]⟩,
  ⟨.and, [10, 2]⟩,
  ⟨.and, [15, 7]⟩,
  ⟨.or, [14, 9]⟩,
  ⟨.or, [19, 20]⟩,
  ⟨.and, [23, 24]⟩,
  ⟨.or, [8, 11]⟩,
  ⟨.or, [13, 26]⟩,
  ⟨.or, [12, 27]⟩,
  ⟨.or, [18, 20]⟩,
  ⟨.or, [17, 29]⟩,
  ⟨.or, [3, 30]⟩,
  ⟨.and, [28, 31]⟩,
  ⟨.or, [25, 32]⟩,
  ⟨.or, [22, 33]⟩,
  ⟨.or, [21, 34]⟩], 35⟩

def c2 : Circuit := ⟨[
  ⟨.or, [4, 16]⟩,
  ⟨.and, [10, 2]⟩,
  ⟨.and, [15, 7]⟩,
  ⟨.or, [14, 8]⟩,
  ⟨.and, [20, 23]⟩,
  ⟨.or, [3, 20]⟩,
  ⟨.or, [19, 25]⟩,
  ⟨.or, [11, 9]⟩,
  ⟨.or, [13, 27]⟩,
  ⟨.or, [12, 28]⟩,
  ⟨.and, [26, 29]⟩,
  ⟨.or, [24, 30]⟩,
  ⟨.or, [22, 31]⟩,
  ⟨.or, [21, 32]⟩,
  ⟨.or, [18, 33]⟩,
  ⟨.or, [17, 34]⟩], 35⟩

def c3 : Circuit := ⟨[
  ⟨.or, [11, 9]⟩,
  ⟨.and, [10, 2]⟩,
  ⟨.and, [15, 7]⟩,
  ⟨.or, [19, 3]⟩,
  ⟨.and, [20, 23]⟩,
  ⟨.or, [8, 20]⟩,
  ⟨.or, [14, 25]⟩,
  ⟨.or, [4, 16]⟩,
  ⟨.or, [18, 27]⟩,
  ⟨.or, [17, 28]⟩,
  ⟨.and, [26, 29]⟩,
  ⟨.or, [24, 30]⟩,
  ⟨.or, [22, 31]⟩,
  ⟨.or, [21, 32]⟩,
  ⟨.or, [13, 33]⟩,
  ⟨.or, [12, 34]⟩], 35⟩

def circuit : Fin 4 → Circuit := ![c0, c1, c2, c3]
def mistakes (i : Fin 4) : Finset Cell :=
  Finset.univ.filter (fun p => output (circuit i) p != truth p)

/-- Each circuit reads the output of the first gate twice. -/
theorem shared_twice : ∀ i, ((circuit i).gates.flatMap Gate.inputs).count 20 = 2 := by
  decide +kernel

theorem legal (i : Fin 4) : Monotone2 (circuit i) ∧ (circuit i).size = 16 := by
  have h : ∀ j, valid (circuit j) = true ∧ (circuit j).size = 16 := by decide +kernel
  refine ⟨?_, (h i).2⟩
  intro g hg
  have hg' := List.all_eq_true.mp (h i).1 g hg
  obtain ⟨op,ins⟩ := g
  cases op <;> simp_all [allowed]

set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
theorem passes_suite : ∀ i, ∀ p ∈ suite, output (circuit i) p = truth p := by
  intro i
  fin_cases i <;> decide +kernel

def mask : Fin 4 → Nat := ![13194139533312, 475368975085586025561263702016, 453790336981444382294400, 14869801762207956311998476300]
def bad (i : Fin 4) (p : Cell) := (mask i).testBit (10*p.1.val+p.2.val)

theorem error_table : ∀ (i : Fin 4) (p : Cell), (output (circuit i) p != truth p) = bad i p := by
  intro i
  fin_cases i <;> decide +kernel

theorem error_counts : ∀ i : Fin 4, (mistakes i).card = (![2,2,16,16] : Fin 4 → Nat) i := by
  intro i
  fin_cases i <;> decide +kernel

theorem supports_disjoint : ∀ i j p, bad i p → bad j p → i = j := by decide +kernel
theorem examples_fail : ∀ i : Fin 4, ∃ p : Cell, bad i p := by decide +kernel
theorem outside_suite : ∀ i p, bad i p → p ∉ suite := by decide +kernel

/-- Any complete test suite extending the published eighteen cases needs four further cells. -/
theorem extension_lower (s : Finset Cell) (contains : suite ⊆ s)
    (complete : ∀ c : Circuit, Monotone2 c → c.size ≤ 16 →
      (∀ p ∈ s, output c p = truth p) → ∀ p, output c p = truth p) : 22 ≤ s.card := by
  classical
  have hit (i : Fin 4) : ∃ p : ↥(s \ suite), bad i p.val := by
    by_contra! none
    have ok (p : Cell) (hp : p ∈ s) : output (circuit i) p = truth p := by
      by_contra ne
      have b : bad i p := by simpa [← error_table] using ne
      exact none ⟨p, Finset.mem_sdiff.mpr ⟨hp,outside_suite i p b⟩⟩ b
    obtain ⟨p,h⟩ := examples_fail i
    have eq := complete _ (legal i).1 (le_of_eq (legal i).2) ok p
    simp [← error_table,eq] at h
  choose f hf using hit
  have inj : Function.Injective f := by
    intro i j e
    exact supports_disjoint i j _ (e ▸ hf i) (hf j)
  have four : 4 ≤ (s \ suite).card := by simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective f inj
  have cards := Finset.card_sdiff_add_card_eq_card contains
  have eighteen := suite_checks.1
  omega

#print axioms extension_lower
#print axioms error_counts
end Alexrollo64.SharedSuite
