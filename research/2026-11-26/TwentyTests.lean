import SharedSuite
namespace Alexrollo64.TwentyTests
open Alexrollo64.EdgeEdits
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- An error pattern realized by a circuit within budget. -/
structure Witness where
  err : Cell → Bool
  realizes : ∃ c : Circuit, Monotone2 c ∧ c.size ≤ 16 ∧
    ∀ p, (output c p != truth p) = err p

def old (j : Fin 16) : Witness :=
  ⟨TestPacking.fails j, TestPacking.circuits j, (TestPacking.legality j).1,
    (TestPacking.legality j).2, TestPacking.tables j⟩
def triple (b : Fin 2) (k : Fin 8) : Witness :=
  ⟨EighteenTests.bad b k, EighteenTests.cand b k, EighteenTests.works b k⟩

def e0 : Circuit := ⟨[⟨.or, [4, 16]⟩, ⟨.and, [10, 2]⟩, ⟨.and, [15, 7]⟩, ⟨.or, [14, 8]⟩, ⟨.and, [20, 23]⟩, ⟨.or, [3, 20]⟩, ⟨.or, [19, 25]⟩, ⟨.or, [11, 9]⟩, ⟨.or, [13, 27]⟩, ⟨.or, [12, 28]⟩, ⟨.and, [26, 29]⟩, ⟨.or, [24, 30]⟩, ⟨.or, [22, 31]⟩, ⟨.or, [21, 32]⟩, ⟨.or, [18, 33]⟩, ⟨.or, [17, 34]⟩], 35⟩
def e1 : Circuit := ⟨[⟨.or, [4, 17]⟩, ⟨.and, [10, 2]⟩, ⟨.and, [15, 7]⟩, ⟨.or, [14, 8]⟩, ⟨.and, [20, 23]⟩, ⟨.or, [3, 20]⟩, ⟨.or, [19, 25]⟩, ⟨.or, [11, 9]⟩, ⟨.or, [13, 27]⟩, ⟨.or, [12, 28]⟩, ⟨.and, [26, 29]⟩, ⟨.or, [24, 30]⟩, ⟨.or, [22, 31]⟩, ⟨.or, [21, 32]⟩, ⟨.or, [16, 33]⟩, ⟨.or, [18, 34]⟩], 35⟩
def e2 : Circuit := ⟨[⟨.or, [4, 18]⟩, ⟨.and, [10, 2]⟩, ⟨.and, [15, 7]⟩, ⟨.or, [14, 8]⟩, ⟨.and, [20, 23]⟩, ⟨.or, [3, 20]⟩, ⟨.or, [19, 25]⟩, ⟨.or, [11, 9]⟩, ⟨.or, [13, 27]⟩, ⟨.or, [12, 28]⟩, ⟨.and, [26, 29]⟩, ⟨.or, [24, 30]⟩, ⟨.or, [22, 31]⟩, ⟨.or, [21, 32]⟩, ⟨.or, [17, 33]⟩, ⟨.or, [16, 34]⟩], 35⟩
def e3 : Circuit := ⟨[⟨.or, [11, 9]⟩, ⟨.and, [10, 2]⟩, ⟨.and, [15, 7]⟩, ⟨.or, [19, 3]⟩, ⟨.and, [20, 23]⟩, ⟨.or, [8, 20]⟩, ⟨.or, [14, 25]⟩, ⟨.or, [4, 16]⟩, ⟨.or, [18, 27]⟩, ⟨.or, [17, 28]⟩, ⟨.and, [26, 29]⟩, ⟨.or, [24, 30]⟩, ⟨.or, [22, 31]⟩, ⟨.or, [21, 32]⟩, ⟨.or, [13, 33]⟩, ⟨.or, [12, 34]⟩], 35⟩
def e4 : Circuit := ⟨[⟨.or, [12, 9]⟩, ⟨.and, [10, 2]⟩, ⟨.and, [15, 7]⟩, ⟨.or, [19, 3]⟩, ⟨.and, [20, 23]⟩, ⟨.or, [8, 20]⟩, ⟨.or, [14, 25]⟩, ⟨.or, [4, 16]⟩, ⟨.or, [18, 27]⟩, ⟨.or, [17, 28]⟩, ⟨.and, [26, 29]⟩, ⟨.or, [24, 30]⟩, ⟨.or, [22, 31]⟩, ⟨.or, [21, 32]⟩, ⟨.or, [11, 33]⟩, ⟨.or, [13, 34]⟩], 35⟩
def e5 : Circuit := ⟨[⟨.or, [13, 9]⟩, ⟨.and, [10, 2]⟩, ⟨.and, [15, 7]⟩, ⟨.or, [19, 3]⟩, ⟨.and, [20, 23]⟩, ⟨.or, [8, 20]⟩, ⟨.or, [14, 25]⟩, ⟨.or, [4, 16]⟩, ⟨.or, [18, 27]⟩, ⟨.or, [17, 28]⟩, ⟨.and, [26, 29]⟩, ⟨.or, [24, 30]⟩, ⟨.or, [22, 31]⟩, ⟨.or, [21, 32]⟩, ⟨.or, [12, 33]⟩, ⟨.or, [11, 34]⟩], 35⟩
def e6 : Circuit := ⟨[⟨.or, [11, 12]⟩, ⟨.or, [20, 13]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [4, 14]⟩, ⟨.or, [10, 23]⟩, ⟨.and, [21, 22]⟩, ⟨.or, [24, 25]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [27, 18]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [28, 29]⟩, ⟨.and, [9, 19]⟩, ⟨.or, [30, 31]⟩, ⟨.and, [7, 15]⟩, ⟨.or, [32, 33]⟩, ⟨.or, [26, 34]⟩], 35⟩
def e7 : Circuit := ⟨[⟨.or, [11, 12]⟩, ⟨.or, [20, 13]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [4, 14]⟩, ⟨.or, [15, 23]⟩, ⟨.and, [2, 10]⟩, ⟨.or, [24, 25]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [27, 18]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [28, 29]⟩, ⟨.and, [9, 19]⟩, ⟨.or, [30, 31]⟩, ⟨.and, [21, 22]⟩, ⟨.or, [32, 33]⟩, ⟨.or, [26, 34]⟩], 35⟩
def extras : Fin 8 → Circuit := ![e0, e1, e2, e3, e4, e5, e6, e7]
def errorMask : Fin 8 → Nat := ![453790336981444382294400, 378158614151203651912000, 226895168490722191147200, 14869801762207956311998476300, 12391501468506630259998730250, 7434900881103978155999238150, 1239150146850664126584194049, 39652766920289389093566054432]
def errorAt (i : Fin 8) (p : Cell) := (errorMask i).testBit (10*p.1.val+p.2.val)

set_option maxHeartbeats 20000000
set_option maxRecDepth 16384

theorem extra_table (i : Fin 8) : ∀ p, (output (extras i) p != truth p) = errorAt i p := by
  fin_cases i <;> decide +kernel
def extra (i : Fin 8) : Witness := by
  have h : ∀ j, TestPacking.valid (extras j) = true ∧ (extras j).size ≤ 16 := by decide +kernel
  refine ⟨errorAt i, extras i, ?_, (h i).2, extra_table i⟩
  intro g hg
  have hh := List.all_eq_true.mp (h i).1 g hg
  obtain ⟨op,ins⟩ := g
  cases op <;> simp_all [TestPacking.allowed]

/-- Six disjoint regions, each split into at most six labels. -/
def labels : Fin 10 → Fin 10 → Fin 6 × Fin 6 := ![
  ![(5, 0), (3, 0), (3, 1), (3, 2), (5, 5), (5, 1), (4, 0), (4, 1), (4, 2), (5, 5)],
  ![(5, 0), (3, 0), (3, 1), (3, 2), (5, 5), (5, 1), (4, 0), (4, 1), (4, 2), (5, 5)],
  ![(0, 0), (3, 0), (3, 1), (3, 2), (5, 5), (5, 1), (4, 0), (4, 1), (4, 2), (5, 5)],
  ![(5, 0), (1, 0), (1, 1), (1, 2), (0, 1), (5, 1), (4, 0), (4, 1), (4, 2), (5, 5)],
  ![(5, 0), (1, 3), (1, 4), (1, 5), (0, 2), (5, 1), (4, 0), (4, 1), (4, 2), (5, 5)],
  ![(5, 0), (3, 0), (3, 1), (3, 2), (5, 5), (5, 1), (4, 0), (4, 1), (4, 2), (5, 5)],
  ![(5, 0), (3, 0), (3, 1), (3, 2), (5, 5), (5, 1), (4, 0), (4, 1), (4, 2), (5, 5)],
  ![(5, 0), (3, 0), (3, 1), (3, 2), (5, 5), (0, 3), (4, 0), (4, 1), (4, 2), (5, 5)],
  ![(5, 0), (3, 0), (3, 1), (3, 2), (5, 5), (5, 1), (2, 0), (2, 1), (2, 2), (0, 4)],
  ![(5, 0), (3, 0), (3, 1), (3, 2), (5, 5), (5, 1), (2, 3), (2, 4), (2, 5), (0, 5)]]
def label (p : Cell) := labels p.1 p.2
def examples : Fin 36 → Witness := ![
  old 0, old 1, old 2, old 3, old 4, old 5,
  old 6, old 7, old 8, old 9, old 10, old 11,
  triple 0 0, triple 0 1, triple 0 2, triple 0 3, triple 0 4, triple 0 5,
  triple 0 6, triple 0 7, triple 1 0, triple 1 1, triple 1 2, triple 1 3,
  triple 1 4, triple 1 5, triple 1 6, triple 1 7, extra 0, extra 1,
  extra 2, extra 3, extra 4, extra 5, extra 6, extra 7]
def region : Fin 36 → Fin 6 := ![0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 4, 4, 4, 3, 3, 3, 5, 5]
def required : Fin 36 → Nat := ![1, 2, 4, 8, 16, 32, 9, 18, 36, 9, 18, 36, 7, 14, 21, 28, 35, 42, 49, 56, 7, 14, 21, 28, 35, 42, 49, 56, 6, 5, 3, 6, 5, 3, 1, 2]
theorem support (i : Fin 36) : ∀ p, (examples i).err p →
    (label p).1 = region i ∧ (required i).testBit (label p).2.val = true := by
  fin_cases i <;> decide +kernel

theorem nonempty : ∀ i, ∃ p, (examples i).err p := by decide +kernel
def minimum : Fin 6 → Nat := ![6,4,4,2,2,2]

/-- The finite check here ranges over subsets of six labels in one region. -/
theorem small_cover : ∀ z (t : Finset (Fin 6)),
    (∀ i, region i = z → ∃ x ∈ t, (required i).testBit x.val = true) → minimum z ≤ t.card := by
  intro z
  fin_cases z <;> decide +kernel

theorem lower (s : Finset Cell)
    (complete : ∀ c : Circuit, Monotone2 c → c.size ≤ 16 →
      (∀ p ∈ s, output c p = truth p) → ∀ p, output c p = truth p) : 20 ≤ s.card := by
  classical
  have hit (i : Fin 36) : ∃ p ∈ s, (examples i).err p := by
    obtain ⟨c,legal,sz,tab⟩ := (examples i).realizes
    by_contra! miss
    have ok (p : Cell) (hp : p ∈ s) : output c p = truth p := by
      by_contra neq
      exact miss p hp (by simpa [← tab] using neq)
    obtain ⟨p,h⟩ := nonempty i
    have eq := complete c legal sz ok p
    simp [← tab,eq] at h
  let group (z : Fin 6) := s.filter (fun p => (label p).1 = z)
  have bound (z : Fin 6) : minimum z ≤ (group z).card := by
    let t := (group z).image (fun p => (label p).2)
    have hh : minimum z ≤ t.card := small_cover z t (by
      intro i hi
      obtain ⟨p,hp,he⟩ := hit i
      obtain ⟨regionEq,bit⟩ := support i p he
      exact ⟨(label p).2,Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,regionEq.trans hi⟩,rfl⟩,bit⟩)
    exact hh.trans Finset.card_image_le
  have tot : s.card = ∑ z, (group z).card :=
    Finset.card_eq_sum_card_fiberwise (fun p _ => Finset.mem_univ (label p).1)
  rw [tot]
  have count : (∑ z, minimum z) = 20 := by decide +kernel
  rw [← count]
  exact Finset.sum_le_sum (fun z _ => bound z)

/-- A smallest suite for these 36 witnesses. -/
def suite20 : Finset Cell := {(2, 0), (3, 4), (4, 4), (7, 5), (8, 9), (9, 9), (3, 1), (3, 2), (4, 1), (4, 3), (8, 6), (8, 7), (9, 6), (9, 8), (4, 0), (9, 1), (2, 3), (7, 6), (0, 5), (0, 8)}

theorem detects_examples : suite20.card = 20 ∧ ∀ j, ∃ p ∈ suite20, (examples j).err p := by
  decide +kernel

#print axioms detects_examples
#print axioms lower
end Alexrollo64.TwentyTests
