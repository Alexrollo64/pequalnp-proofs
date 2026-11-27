import SharedOperand

namespace Alexrollo64.CommonThree
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open Alexrollo64.Support20782 Alexrollo64.DisjointCopies Alexrollo64.OneDefect
open Alexrollo64.SharedOperand (overlap_pos)
def requiredThree := (Finset.univ : Finset (Fin 24)).image (requiredWire 3)
def sampleThree (i : Fin 7) := oneEach (vertex (0 : Fin 3) (rows i)) (vertex (0 : Fin 3) (cols i))

theorem extra_zero (j : Nat) (hj : j ∉ requiredThree) : score sampleThree j = 0 := by
  have finite : ∀ t : Fin 30, t.val ∉ requiredThree → score sampleThree t.val = 0 := by decide +kernel
  by_cases h : j < 30
  · exact finite ⟨j,h⟩ hj
  · have off (i : Fin 7) : (sampleThree i).getD j false = false := by
      apply List.getD_eq_default
      simp [sampleThree,oneEach]; omega
    unfold score; simp_rw [off]; decide +kernel

theorem candidate (c : Circuit) (hm : Monotone2 c) (hr : Represents (graph 3) c)
    (hs : c.size ≤ 24) :
    needed 30 c.gates {c.output} = requiredThree ∧
    (deficitList 30 c.gates {c.output}).sum = 1 := by
  let s := needed 30 c.gates {c.output}
  have inc : requiredThree ⊆ s := by
    intro j hj
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hj
    exact indispensable (⟨t.val/8,by omega⟩ : Fin 3) ⟨2+t.val%8,by omega⟩
      (by simp only [required,Finset.mem_insert,Finset.mem_singleton]; omega) c hm hr
  have card : requiredThree.card = 24 := by decide +kernel
  have lb := Finset.card_le_card inc
  have low := lower 3 c.size ⟨c,hm,le_rfl,hr⟩
  change c.gates.length ≤ 24 at hs
  change 8*3 ≤ c.gates.length at low
  have ac := account c.gates 30 {c.output} (fun g hg => (hm g hg).2)
  change _ + s.card = _ at ac
  simp only [Finset.card_singleton] at ac
  have hne : s.card ≠ 25 := by
    intro h
    have m := mass_run c.gates {c.output} sampleThree 30 (fun i => by simp [sampleThree,oneEach])
      (fun g hg => ⟨by simpa using (hm g hg).1,(hm g hg).2⟩)
      (by change s.card = _; rw [Finset.card_singleton]; omega)
    have out : score (fun i => c.gates.foldl push (sampleThree i)) c.output = 7 := by
      change price (pack (fun i => c.eval (sampleThree i))) = 7
      have he : (fun i => c.eval (sampleThree i)) = (fun i => target (rows i) (cols i)) := by
        funext i; exact (hr _ _).trans (same_block _ _ _)
      rw [he]; decide +kernel
    have eq : mass sampleThree requiredThree = mass sampleThree s := Finset.sum_subset inc (fun j _ hj => extra_zero j hj)
    have six : mass sampleThree requiredThree = 6 := by decide +kernel
    change (∑ j ∈ ({c.output} : Finset Nat), _) ≤ mass sampleThree s at m
    rw [Finset.sum_singleton,out,←eq,six] at m
    omega
  exact ⟨(Finset.eq_of_subset_of_card_le inc (by omega)).symm,by omega⟩


def joint {ι : Type} (n : Nat) : List Gate → Finset Nat → (ι → Fin 7 → List Bool) → Prop
  | [], _, _ => False
  | g::gs, s, w =>
    let mid := needed (n+1) gs s
    (∃ j ∈ mid.erase n ∩ g.inputs.toFinset, 30 ≤ j ∧ j < n ∧ ∀ b, 0 < score (w b) j) ∨
    joint (n+1) gs s (fun b i => push (w b i) g)

theorem common {ι : Type} (base : ι) (gs : List Gate) (n : Nat) (hn : 30 ≤ n)
    (s : Finset Nat) (w : ι → Fin 7 → List Bool)
    (hw : ∀ b i, (w b i).length = n)
    (raw : ∀ j < 30, ∃ b, score (w b) j = 0)
    (hm : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (d : (deficitList n gs s).sum = 1)
    (gain : ∀ b, mass (w b) (needed n gs s) < mass (fun i => gs.foldl push (w b i)) s) :
    joint n gs s w := by
  induction gs generalizing n w with
  | nil => simp [deficitList] at d
  | cons g gs ih =>
    let mid := needed (n+1) gs s
    let v := fun b i => push (w b i) g
    have hv (b i) : (v b i).length = n+1 := by simp [v,push,hw]
    have h := hm g (by simp)
    have hh := before_card n g mid h.2
    have ht : ∀ a ∈ gs, (a.op = .and ∨ a.op = .or) ∧ a.inputs.length ≤ 2 :=
      fun a ha => hm a (by simp [ha])
    change mid.card+1-(before n g mid).card + (deficitList (n+1) gs s).sum = 1 at d
    change ∀ b, mass (w b) (before n g mid) < mass (fun i => gs.foldl push (v b i)) s at gain
    by_cases tight : (before n g mid).card = mid.card+1
    · right
      have keep (b) (j : Nat) (hj : j < 30) : score (v b) j = score (w b) j := by
        unfold score; congr 2; funext i
        exact read_other _ _ _ (by rw [hw]; omega)
      exact ih (n+1) (by omega) v hv (fun j hj => by simpa only [keep _ _ hj] using raw j hj)
        ht (by omega) (fun b => lt_of_le_of_lt (mass_step (w b) n g mid (hw b) h.2 h.1 tight) (gain b))
    · left
      have ac := account gs (n+1) s (fun a ha => (ht a ha).2)
      change _ + mid.card = _ at ac
      have full : mid.card = s.card + gs.length := by omega
      have gw (b) := lt_of_lt_of_le (gain b) (mass_run gs s (v b) (n+1) (hv b) ht full)
      have hi := (gain_active (w base) n g mid (hw base) (gw base)).1
      have hc := Finset.card_union_add_card_inter (mid.erase n) g.inputs.toFinset
      have he := Finset.card_erase_add_one hi
      have len := List.toFinset_card_le (l := g.inputs)
      have card : (before n g mid).card ≥ mid.card := by omega
      have small : (mid.erase n ∩ g.inputs.toFinset).card ≤ 1 := by
        simp only [before,ite_eq_left hi] at card
        omega
      obtain ⟨j,hj,_⟩ := overlap_pos n g mid (w base) (hw base) h.1 h.2 card (gw base)
      have pos (b) : 0 < score (w b) j := by
        obtain ⟨l,hl,pl⟩ := overlap_pos n g mid (w b) (hw b) h.1 h.2 card (gw b)
        exact (Finset.card_le_one.mp small l hl j hj) ▸ pl
      refine ⟨j,hj,?_,?_,pos⟩
      · by_contra! lt
        obtain ⟨b,eq⟩ := raw j lt
        exact (Nat.ne_of_gt (pos b)) eq
      · by_contra! le
        have empty (i) : (w base i).getD j false = false := by apply List.getD_eq_default; rw [hw]; omega
        have z : score (w base) j = 0 := by unfold score; simp_rw [empty]; decide +kernel
        exact (Nat.ne_of_gt (pos base)) z

def tests3 (b : Fin 3) (i : Fin 7) := oneEach (vertex b (rows i)) (vertex b (cols i))
theorem candidate_joint (c : Circuit) (hm : Monotone2 c) (hr : Represents (graph 3) c)
    (hs : c.size ≤ 24) : joint 30 c.gates {c.output} tests3 := by
  obtain ⟨support,one⟩ := candidate c hm hr hs
  have gain (b : Fin 3) : mass (tests3 b) (needed 30 c.gates {c.output}) <
      mass (fun i => c.gates.foldl push (tests3 b i)) {c.output} := by
    rw [support]
    have six : ∀ b, mass (tests3 b) requiredThree = 6 := by decide +kernel
    rw [six]
    simp only [mass,Finset.sum_singleton]
    change 6 < price (pack fun i => c.eval (tests3 b i))
    have eq : (fun i => c.eval (tests3 b i)) = (fun i => target (rows i) (cols i)) := by
      funext i; exact (hr _ _).trans (same_block _ _ _)
    rw [eq]; decide +kernel
  have r : ∀ j : Fin 30, ∃ b : Fin 3, score (tests3 b) j.val = 0 := by decide +kernel
  exact common 0 c.gates 30 le_rfl _ tests3 (fun b i => by simp [tests3,oneEach])
    (fun j hj => r ⟨j,hj⟩) (fun g hg => ⟨by simpa using (hm g hg).1,(hm g hg).2⟩) one gain

#print axioms candidate_joint
end Alexrollo64.CommonThree
