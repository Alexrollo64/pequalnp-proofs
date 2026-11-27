import DisjointCopies

namespace Alexrollo64.OneDefect

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open Alexrollo64.Support20782 Alexrollo64.DisjointCopies

def requiredTwo := (Finset.univ : Finset (Fin 16)).image (requiredWire 2)
def sample (i : Fin 7) := oneEach (vertex (0 : Fin 2) (rows i)) (vertex (0 : Fin 2) (cols i))

theorem extra_zero (j : Nat) (hj : j ∉ requiredTwo) : score sample j = 0 := by
  have finite : ∀ t : Fin 20, t.val ∉ requiredTwo → score sample t.val = 0 := by decide +kernel
  by_cases h : j < 20
  · exact finite ⟨j,h⟩ hj
  · have off (i : Fin 7) : (sample i).getD j false = false := by
      apply List.getD_eq_default
      simp [sample,oneEach]; omega
    unfold score; simp_rw [off]; decide +kernel

def deficitList (n : Nat) : List Gate → Finset Nat → List Nat
  | [], _ => []
  | g :: gs, s =>
    let m := needed (n+1) gs s
    (m.card + 1 - (before n g m).card) :: deficitList (n+1) gs s

theorem account (gs : List Gate) (n : Nat) (s : Finset Nat)
    (hf : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (deficitList n gs s).sum + (needed n gs s).card = s.card + gs.length := by
  induction gs generalizing n s with
  | nil => simp [deficitList,needed]
  | cons g gs ih =>
    have h := before_card n g (needed (n+1) gs s) (hf g (by simp))
    have t := ih (n+1) s (fun a ha => hf a (by simp [ha]))
    simp only [deficitList,needed,List.sum_cons,List.length_cons]; omega

/-- The backwards trace of any candidate of size at most 16 has one unit of deficit. -/
theorem candidate (c : Circuit) (hm : Monotone2 c) (hr : Represents (graph 2) c)
    (hs : c.size ≤ 16) :
    needed 20 c.gates {c.output} = requiredTwo ∧
    (deficitList 20 c.gates {c.output}).sum = 1 := by
  let s := needed 20 c.gates {c.output}
  have inc : requiredTwo ⊆ s := by
    intro j hj
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hj
    exact indispensable (⟨t.val/8,by omega⟩ : Fin 2) ⟨2+t.val%8,by omega⟩
      (by simp only [required,Finset.mem_insert,Finset.mem_singleton]; omega) c hm hr
  have card : requiredTwo.card = 16 := by decide +kernel
  have lb := Finset.card_le_card inc
  have low := lower 2 c.size ⟨c,hm,le_rfl,hr⟩
  change c.gates.length ≤ 16 at hs
  change 8*2 ≤ c.gates.length at low
  have ac := account c.gates 20 {c.output} (fun g hg => (hm g hg).2)
  change _ + s.card = _ at ac
  simp only [Finset.card_singleton] at ac
  have hne : s.card ≠ 17 := by
    intro h
    have m := mass_run c.gates {c.output} sample 20 (fun i => by simp [sample,oneEach])
      (fun g hg => ⟨by simpa using (hm g hg).1,(hm g hg).2⟩)
      (by change s.card = _; rw [Finset.card_singleton]; omega)
    have out : score (fun i => c.gates.foldl push (sample i)) c.output = 7 := by
      change price (pack (fun i => c.eval (sample i))) = 7
      have he : (fun i => c.eval (sample i)) = (fun i => target (rows i) (cols i)) := by
        funext i; exact (hr _ _).trans (same_block _ _ _)
      rw [he]; decide +kernel
    have eq : mass sample requiredTwo = mass sample s := Finset.sum_subset inc (fun j _ hj => extra_zero j hj)
    have six : mass sample requiredTwo = 6 := by decide +kernel
    change (∑ j ∈ ({c.output} : Finset Nat), _) ≤ mass sample s at m
    rw [Finset.sum_singleton,out,←eq,six] at m
    omega
  exact ⟨(Finset.eq_of_subset_of_card_le inc (by omega)).symm,by omega⟩

/-- A positive increase requires an output that is true on at least one test. -/
theorem gain_active (w : Fin 7 → List Bool) (n : Nat) (g : Gate) (s : Finset Nat)
    (hw : ∀ i, (w i).length = n)
    (h : mass w (before n g s) < mass (fun i => push (w i) g) s) :
    n ∈ s ∧ ∃ i, (push (w i) g).getD n false = true := by
  let w' := fun i => push (w i) g
  have keep (j : Nat) (hj : j ≠ n) : score w' j = score w j := by
    unfold score
    congr 2
    funext i
    exact read_other _ _ _ (by rw [hw]; exact hj)
  have hi : n ∈ s := by
    by_contra no
    have eq : mass w' s = mass w s :=
      Finset.sum_congr rfl (fun j hj => keep j (fun e => no (e ▸ hj)))
    change mass w (before n g s) < mass w' s at h
    simp [before,no,eq] at h
  refine ⟨hi,?_⟩
  by_contra! off
  have zero : score w' n = 0 := by
    have none (i) : (w' i).getD n false = false := by simpa [w'] using off i
    unfold score; simp_rw [none]; decide +kernel
  have eq := Finset.sum_congr (s₁ := s.erase n) rfl (fun j hj => keep j (Finset.mem_erase.mp hj).1)
  have hs := Finset.sum_erase_add _ (score w') hi
  rw [eq,zero,Nat.add_zero] at hs
  have sub : s.erase n ⊆ before n g s := by simp [before,hi]
  have le := Finset.sum_le_sum_of_subset_of_nonneg (f := score w) sub (fun _ _ _ => Nat.zero_le _)
  change (∑ j ∈ before n g s, score w j) < ∑ j ∈ s, score w' j at h
  exact (Nat.not_lt_of_ge le) (hs.symm ▸ h)

/-- At a single gate the mass on the required wires grows on both test suites. -/
def commonGain (n : Nat) : List Gate → Finset Nat → (Fin 7 → List Bool) → (Fin 7 → List Bool) → Prop
  | [], _, _, _ => False
  | g :: gs, s, w, v =>
    let mid := needed (n+1) gs s
    let afterW := fun i => push (w i) g
    let afterV := fun i => push (v i) g
    (mass w (before n g mid) < mass afterW mid ∧ mass v (before n g mid) < mass afterV mid ∧
      (∃ i, (afterW i).getD n false = true) ∧ (∃ i, (afterV i).getD n false = true)) ∨
    commonGain (n+1) gs s afterW afterV

theorem common_of_one (gs : List Gate) (n : Nat) (s : Finset Nat) (w v : Fin 7 → List Bool)
    (hw : ∀ i, (w i).length = n) (hv : ∀ i, (v i).length = n)
    (hm : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (d : (deficitList n gs s).sum = 1)
    (aw : mass w (needed n gs s) < mass (fun i => gs.foldl push (w i)) s)
    (av : mass v (needed n gs s) < mass (fun i => gs.foldl push (v i)) s) :
    commonGain n gs s w v := by
  induction gs generalizing n w v with
  | nil => simp [deficitList] at d
  | cons g gs ih =>
    let mid := needed (n+1) gs s
    let w' := fun i => push (w i) g
    let v' := fun i => push (v i) g
    have hw' (i) : (w' i).length = n+1 := by simp [w',push,hw]
    have hv' (i) : (v' i).length = n+1 := by simp [v',push,hv]
    have h := hm g (by simp)
    have hh := before_card n g mid h.2
    have ht : ∀ a ∈ gs, (a.op = .and ∨ a.op = .or) ∧ a.inputs.length ≤ 2 :=
      fun a ha => hm a (by simp [ha])
    change (mid.card+1-(before n g mid).card) + (deficitList (n+1) gs s).sum = 1 at d
    change mass w (before n g mid) < mass (fun i => gs.foldl push (w' i)) s at aw
    change mass v (before n g mid) < mass (fun i => gs.foldl push (v' i)) s at av
    by_cases tight : (before n g mid).card = mid.card+1
    · right
      exact ih (n+1) w' v' hw' hv' ht (by omega)
        (lt_of_le_of_lt (mass_step w n g mid hw h.2 h.1 tight) aw)
        (lt_of_le_of_lt (mass_step v n g mid hv h.2 h.1 tight) av)
    · left
      have ac := account gs (n+1) s (fun a ha => (ht a ha).2)
      change _ + mid.card = _ at ac
      have full : mid.card = s.card + gs.length := by omega
      have gw := lt_of_lt_of_le aw (mass_run gs s w' (n+1) hw' ht full)
      have gv := lt_of_lt_of_le av (mass_run gs s v' (n+1) hv' ht full)
      exact ⟨gw,gv,(gain_active w n g mid hw gw).2,(gain_active v n g mid hv gv).2⟩

def suite (b : Fin 2) (i : Fin 7) := oneEach (vertex b (rows i)) (vertex b (cols i))

theorem both_blocks (c : Circuit) (hm : Monotone2 c) (hr : Represents (graph 2) c)
    (hs : c.size ≤ 16) : commonGain 20 c.gates {c.output} (suite 0) (suite 1) := by
  obtain ⟨boundary,one⟩ := candidate c hm hr hs
  have gain (b : Fin 2) : mass (suite b) (needed 20 c.gates {c.output}) <
      mass (fun i => c.gates.foldl push (suite b i)) {c.output} := by
    rw [boundary]
    have six : ∀ b : Fin 2, mass (suite b) requiredTwo = 6 := by decide +kernel
    rw [six]
    simp only [mass,Finset.sum_singleton]
    change 6 < price (pack fun i => c.eval (suite b i))
    have he : (fun i => c.eval (suite b i)) = (fun i => target (rows i) (cols i)) := by
      funext i; exact (hr _ _).trans (same_block _ _ _)
    rw [he]; decide +kernel
  exact common_of_one _ _ _ _ _ (fun i => by simp [suite,oneEach]) (fun i => by simp [suite,oneEach])
    (fun g hg => ⟨by simpa using (hm g hg).1,(hm g hg).2⟩) one (gain 0) (gain 1)

#print axioms candidate
#print axioms both_blocks
end Alexrollo64.OneDefect
