import TestPacking
namespace Alexrollo64.EighteenTests
open Alexrollo64.EdgeEdits Alexrollo64.TreeCopies Alexrollo64.TestPacking
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def small (b : Nat) : Fin 8 → Tree := ![(.node false (.node true (row b 2) (col b 0)) (.node true (row b 4) (.node false (col b 1) (.node false (col b 2) (.node false (col b 3) (col b 4)))))),
(.node false (.node true (row b 2) (col b 0)) (.node false (.node true (row b 3) (col b 1)) (.node true (row b 4) (.node false (col b 2) (.node false (col b 3) (col b 4)))))),
(.node false (.node true (row b 2) (col b 0)) (.node false (.node true (row b 3) (col b 2)) (.node true (row b 4) (.node false (col b 1) (.node false (col b 3) (col b 4)))))),
(.node false (.node true (row b 2) (col b 0)) (.node false (.node true (row b 3) (.node false (col b 1) (col b 2))) (.node true (row b 4) (.node false (col b 3) (col b 4))))),
(.node false (.node true (row b 2) (col b 0)) (.node false (.node true (row b 3) (col b 3)) (.node true (row b 4) (.node false (col b 1) (.node false (col b 2) (col b 4)))))),
(.node false (.node true (row b 2) (col b 0)) (.node false (.node true (row b 3) (.node false (col b 1) (col b 3))) (.node true (row b 4) (.node false (col b 2) (col b 4))))),
(.node false (.node true (row b 2) (col b 0)) (.node true (.node false (row b 3) (.node false (col b 1) (col b 4))) (.node false (row b 4) (.node false (col b 2) (col b 3))))),
(.node false (.node true (row b 2) (col b 0)) (.node true (.node false (row b 3) (col b 4)) (.node false (row b 4) (.node false (col b 1) (.node false (col b 2) (col b 3))))))]

def tree (b : Fin 2) (m : Fin 8) : Tree := .node false (small b m) (block 2 (1-b.val))
def cand (b : Fin 2) (m : Fin 8) : Circuit := ⟨code 20 (tree b m),out 20 (tree b m)⟩
def bad (b : Fin 2) (m : Fin 8) (p : Cell) := decide
  (p.2.val ≥ 5*b.val+1 ∧ p.2.val ≤ 5*b.val+3 ∧
   p.1.val = 5*b.val+3+(if m.val.testBit (p.2.val-(5*b.val+1)) then 1 else 0))

set_option maxHeartbeats 3000000 in
theorem local_table : ∀ b m, cost (tree b m) ≤ 16 ∧
    (leaves (tree b m)).all (fun i => decide (i<20)) = true ∧
    ∀ p, (test (tree b m) p != truth p) = bad b m p := by
  intro b m
  fin_cases b <;> fin_cases m <;> decide +kernel

theorem works (b m) : Monotone2 (cand b m) ∧ (cand b m).size ≤ 16 ∧
    ∀ p, (output (cand b m) p != truth p) = bad b m p := by
  obtain ⟨sz,raw,tab⟩ := local_table b m
  refine ⟨legal _ _,by simpa [cand,Circuit.size,length_code] using sz,?_⟩
  intro p
  let w := oneEach p.1 p.2
  have hw : w.length = 20 := by simp [w,oneEach]
  have ok (j : Nat) (hj : j ∈ leaves (tree b m)) : j < w.length ∧ w.getD j false = w.getD j false :=
    ⟨hw ▸ of_decide_eq_true (List.all_eq_true.mp raw j hj),rfl⟩
  obtain ⟨zs,_,run,result,_⟩ := run_code (tree b m) w _ ok
  rw [hw] at run result
  have ev : output (cand b m) p = test (tree b m) p := by
    change ((code 20 (tree b m)).foldl Alexrollo64.PaddedRows.step w).getD _ false = _
    rw [run]; exact result
  rw [ev,tab]

def group (b : Fin 2) (j : Fin 3) : Fin 16 := ⟨6+3*b.val+j.val,by omega⟩
def bit (b : Fin 2) (p : Cell) := decide (p.1.val = 3+5*b.val)
def pick (bits : Fin 3 → Bool) : Fin 8 :=
  ⟨(if bits 0 then 1 else 0)+(if bits 1 then 2 else 0)+(if bits 2 then 4 else 0),by split_ifs <;> omega⟩

set_option maxHeartbeats 3000000 in
theorem overlap (b : Fin 2) (m : Fin 8) (p : Cell) (i : Fin 16) :
    bad b m p → fails i p → ∃ j, i = group b j ∧ (bit b p != m.val.testBit j.val) = true := by
  revert m p i
  fin_cases b <;> decide +kernel

theorem bits_ok : ∀ (bits : Fin 3 → Bool) (j : Fin 3), (pick bits).val.testBit j.val = bits j := by
  intro bits j
  fin_cases j <;> cases h₀ : bits 0 <;> cases h₁ : bits 1 <;> cases h₂ : bits 2 <;> simp [pick,h₀,h₁,h₂] <;> decide

theorem inhabited_bad : ∀ b m, ∃ p, bad b m p := by decide +kernel
theorem separate : ∀ m n p, bad 0 m p → bad 1 n p → False := by decide +kernel

theorem lower (s : Finset Cell)
    (complete : ∀ c : Circuit, Monotone2 c → c.size ≤ 16 →
      (∀ p ∈ s, output c p = truth p) → ∀ p, output c p = truth p) : 18 ≤ s.card := by
  classical
  have hit (c : Circuit) (ok : Monotone2 c) (sz : c.size ≤ 16) (d : Cell → Bool)
      (tab : ∀ p, (output c p != truth p) = d p) (ex : ∃ p, d p) : ∃ p : s, d p.val := by
    by_contra! miss
    have allgood (p) (hp : p ∈ s) : output c p = truth p := by
      have h := tab p
      have no := miss ⟨p,hp⟩
      cases h₁ : output c p <;> cases h₂ : truth p <;> simp_all
    obtain ⟨p,hp⟩ := ex
    have eq := complete _ ok sz allgood p
    rw [←tab,eq] at hp
    simp at hp
  choose f hf using fun i => hit _ (legality i).1 (legality i).2 _ (tables i) (nonempty_support i)
  have inj : Function.Injective f := by
    intro i j e
    exact distinct i j _ (e ▸ hf i) (hf j)
  let bits (b : Fin 2) (j : Fin 3) := bit b (f (group b j)).val
  let m (b : Fin 2) := pick (bits b)
  choose g hg using fun b => hit _ (works b (m b)).1 (works b (m b)).2.1 _ (works b (m b)).2.2 (inhabited_bad b (m b))
  have fresh (b : Fin 2) (i : Fin 16) : g b ≠ f i := by
    intro e
    obtain ⟨j,rfl,contra⟩ := overlap b (m b) _ _ (e ▸ hg b) (hf i)
    simp [m,bits_ok,bits] at contra
  have apart : g 0 ≠ g 1 := by
    intro e
    exact separate _ _ _ (e ▸ hg 0) (hg 1)
  let seen := Finset.univ.image f
  have n : seen.card = 16 := by simp [seen,Finset.card_image_of_injective _ inj]
  have out (b : Fin 2) : g b ∉ seen := by
    intro h
    obtain ⟨i,_,e⟩ := Finset.mem_image.mp h
    exact fresh b i e.symm
  have big := Finset.card_le_univ (insert (g 0) (insert (g 1) seen))
  rw [Finset.card_insert_of_notMem (by simp [apart,out]),Finset.card_insert_of_notMem (out 1),n] at big
  simpa using big

def suite : Finset Cell := {(2,0),(3,4),(4,4),(7,5),(8,9),(9,9),(3,1),(3,2),(3,3),(8,6),(8,7),(8,8),(4,1),(9,6),(4,0),(9,1),(2,5),(7,6)}

theorem suite_checks : suite.card = 18 ∧ (∀ i, ∃ p ∈ suite, fails i p) ∧
    (∀ b m, ∃ p ∈ suite, bad b m p) := by decide +kernel

#print axioms lower
end Alexrollo64.EighteenTests
