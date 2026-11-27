import SharedOperand

namespace Alexrollo64.FusionCriterion

/-- An observation lists the active wires available to the remainder of the circuit. -/
def Decodes {R C W : Type} (G : R → C → Prop) (obs : R → C → Set W) :=
  ∃ F : Set W → Prop, Monotone F ∧ ∀ r c, F (obs r c) ↔ G r c

/-- On finite domains the witness is the monotone DNF of all positive observations. -/
theorem decodes_iff {R C W : Type} (G : R → C → Prop) (obs : R → C → Set W) :
    Decodes G obs ↔ ∀ r c u v, G r c → obs r c ⊆ obs u v → G u v := by
  constructor
  · rintro ⟨F,mono,h⟩ r c u v pos sub
    exact (h u v).mp (mono sub ((h r c).mpr pos))
  · intro consistent
    refine ⟨fun s => ∃ r c, G r c ∧ obs r c ⊆ s,?_,?_⟩
    · rintro s t inc ⟨r,c,pos,hs⟩; exact ⟨r,c,pos,hs.trans inc⟩
    · intro u v
      exact ⟨fun ⟨r,c,pos,sub⟩ => consistent r c u v pos sub,
        fun pos => ⟨u,v,pos,fun _ h => h⟩⟩

/-- The fused row and column have a common wire labelled none. -/
def mixed {R C : Type} [DecidableEq R] [DecidableEq C] (a : R) (b : C) (r : R) (c : C) :
    Set (Option (Sum R C)) :=
  {if r = a then none else some (.inl r), if c = b then none else some (.inr c)}

theorem mixed_sub {R C : Type} [DecidableEq R] [DecidableEq C]
    (a : R) (b : C) (r u : R) (c v : C) :
    mixed a b r c ⊆ mixed a b u v ↔
      (r = u ∧ c = v) ∨ (r = a ∧ c = b ∧ (u = a ∨ v = b)) := by
  simp only [mixed,Set.insert_subset_iff,Set.singleton_subset_iff,Set.mem_insert_iff,Set.mem_singleton_iff]
  split_ifs <;> simp_all <;> grind

theorem mixed_iff {R C : Type} [DecidableEq R] [DecidableEq C]
    (G : R → C → Prop) (a : R) (b : C) :
    Decodes G (mixed a b) ↔ (G a b → (∀ v, G a v) ∧ (∀ u, G u b)) := by
  rw [decodes_iff]
  constructor
  · intro h hab
    exact ⟨fun v => h a b a v hab ((mixed_sub _ _ _ _ _ _).mpr (Or.inr ⟨rfl,rfl,Or.inl rfl⟩)),
      fun u => h a b u b hab ((mixed_sub _ _ _ _ _ _).mpr (Or.inr ⟨rfl,rfl,Or.inr rfl⟩))⟩
  · intro h r c u v pos sub
    rcases (mixed_sub _ _ _ _ _ _).mp sub with ⟨rfl,rfl⟩|⟨rfl,rfl,eq|eq⟩
    · exact pos
    · exact eq ▸ (h pos).1 v
    · exact eq ▸ (h pos).2 u

/-- Two wires on the row side are merged. Columns are all retained. -/
def rowFuse {R C : Type} [DecidableEq R] (a b : R) (r : R) (c : C) : Set (Sum R C) :=
  {Sum.inl (if r = b then a else r), Sum.inr c}

theorem rows_iff {R C : Type} [DecidableEq R] (G : R → C → Prop) (a b : R) :
    Decodes G (rowFuse a b) ↔ ∀ c, G a c ↔ G b c := by
  rw [decodes_iff]
  constructor
  · intro h c
    have eq : rowFuse a b a c = rowFuse a b b c := by by_cases e : a=b <;> simp [rowFuse,e]
    exact ⟨fun pos => h a c b c pos eq.subset,fun pos => h b c a c pos eq.symm.subset⟩
  · intro h r c u v pos sub
    simp only [rowFuse,Set.insert_subset_iff,Set.singleton_subset_iff,Set.mem_insert_iff,Set.mem_singleton_iff] at sub
    split_ifs at sub <;> simp_all

open Alexrollo64.DisjointCopies (graph)
open Alexrollo64.SharedOperand (testedLeft testedRight)

def G (r c : Fin 10) := graph 2 r c = true

/-- Use the matching observation map for the two types of primary wires. -/
def survives (a b : Fin 20) : Prop :=
  if ha : a.val < 10 then
    if hb : b.val < 10 then Decodes G (rowFuse ⟨a.val,ha⟩ ⟨b.val,hb⟩)
    else Decodes G (mixed ⟨a.val,ha⟩ ⟨b.val-10,by omega⟩)
  else if hb : b.val < 10 then Decodes G (mixed ⟨b.val,hb⟩ ⟨a.val-10,by omega⟩)
    else Decodes (fun c r => G r c) (rowFuse ⟨a.val-10,by omega⟩ ⟨b.val-10,by omega⟩)

def star (a b : Fin 10) := G a b → (∀ v, G a v) ∧ (∀ u, G u b)

def criterion (a b : Fin 20) : Prop :=
  if ha : a.val < 10 then
    if hb : b.val < 10 then (∀ c, G ⟨a.val,ha⟩ c ↔ G ⟨b.val,hb⟩ c)
    else star ⟨a.val,ha⟩ ⟨b.val-10,by omega⟩
  else if hb : b.val < 10 then star ⟨b.val,hb⟩ ⟨a.val-10,by omega⟩
    else (∀ r, G r ⟨a.val-10,by omega⟩ ↔ G r ⟨b.val-10,by omega⟩)

theorem tested_pairs (a b : Fin 20) (ha : a.val ∈ testedLeft) (hb : b.val ∈ testedRight) :
    survives a b ↔ (a.val < 10 ↔ ¬ b.val < 10) := by
  have all : ∀ a b : Fin 20, a.val ∈ testedLeft → b.val ∈ testedRight →
      (criterion a b ↔ (a.val < 10 ↔ ¬ b.val < 10)) := by
    unfold criterion star G
    decide +kernel
  rw [←all a b ha hb]
  unfold survives criterion star
  split <;> split <;> simp only [rows_iff,mixed_iff]

def pairs := testedLeft ×ˢ testedRight

theorem count_mixed : (pairs.filter (fun p => decide (p.1 < 10) != decide (p.2 < 10))).card = 18 := by decide +kernel

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open Alexrollo64.DisjointCopies (twoCircuit)

/-- Insert the OR as gate zero; its raw operands are unavailable to all later gates. -/
def renumber (a b i : Nat) : Nat :=
  if i = a ∨ i = b then 20 else if i < 20 then i else i+1

def mergedCircuit (a b : Nat) : Circuit :=
  ⟨⟨.or,[a,b]⟩ :: twoCircuit.gates.map (fun g => ⟨g.op,g.inputs.map (renumber a b)⟩),37⟩

theorem exclusive (a b : Fin 20) : ∀ g ∈ (mergedCircuit a b).gates.tail,
    a.val ∉ g.inputs ∧ b.val ∉ g.inputs := by
  intro g h
  simp only [mergedCircuit,List.tail_cons,List.mem_map] at h
  obtain ⟨old,_,rfl⟩ := h
  simp only [List.mem_map,not_exists,not_and]
  constructor <;> intro i _ <;> unfold renumber <;> split_ifs <;> omega

theorem merged_size (a b : Nat) : (mergedCircuit a b).size = 18 := rfl

theorem merged_legal (a b : Nat) : Monotone2 (mergedCircuit a b) := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hm
  · simp
  · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hm
    have legal : Monotone2 twoCircuit := by
      intro j hj
      simp only [twoCircuit,List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
    exact ⟨(legal q hq).1,by simpa using (legal q hq).2⟩

private theorem case_2_15 : Represents (graph 2) (mergedCircuit 2 15) := by
  unfold Represents; decide +kernel

private theorem case_2_16 : Represents (graph 2) (mergedCircuit 2 16) := by
  unfold Represents; decide +kernel

private theorem case_2_19 : Represents (graph 2) (mergedCircuit 2 19) := by
  unfold Represents; decide +kernel

private theorem case_3_15 : Represents (graph 2) (mergedCircuit 3 15) := by
  unfold Represents; decide +kernel

private theorem case_3_16 : Represents (graph 2) (mergedCircuit 3 16) := by
  unfold Represents; decide +kernel

private theorem case_3_19 : Represents (graph 2) (mergedCircuit 3 19) := by
  unfold Represents; decide +kernel

private theorem case_4_15 : Represents (graph 2) (mergedCircuit 4 15) := by
  unfold Represents; decide +kernel

private theorem case_4_16 : Represents (graph 2) (mergedCircuit 4 16) := by
  unfold Represents; decide +kernel

private theorem case_4_19 : Represents (graph 2) (mergedCircuit 4 19) := by
  unfold Represents; decide +kernel

private theorem case_10_7 : Represents (graph 2) (mergedCircuit 10 7) := by
  unfold Represents; decide +kernel

private theorem case_10_8 : Represents (graph 2) (mergedCircuit 10 8) := by
  unfold Represents; decide +kernel

private theorem case_10_9 : Represents (graph 2) (mergedCircuit 10 9) := by
  unfold Represents; decide +kernel

private theorem case_11_7 : Represents (graph 2) (mergedCircuit 11 7) := by
  unfold Represents; decide +kernel

private theorem case_11_8 : Represents (graph 2) (mergedCircuit 11 8) := by
  unfold Represents; decide +kernel

private theorem case_11_9 : Represents (graph 2) (mergedCircuit 11 9) := by
  unfold Represents; decide +kernel

private theorem case_14_7 : Represents (graph 2) (mergedCircuit 14 7) := by
  unfold Represents; decide +kernel

private theorem case_14_8 : Represents (graph 2) (mergedCircuit 14 8) := by
  unfold Represents; decide +kernel

private theorem case_14_9 : Represents (graph 2) (mergedCircuit 14 9) := by
  unfold Represents; decide +kernel

set_option maxHeartbeats 1500000 in
theorem merged_correct : ∀ a b : Fin 20, a.val ∈ testedLeft → b.val ∈ testedRight →
    (a.val < 10 ↔ ¬ b.val < 10) → Represents (graph 2) (mergedCircuit a b) := by
  intro a b ha hb mix
  have choices : ∀ a b : Fin 20, a.val ∈ testedLeft → b.val ∈ testedRight →
      (a.val < 10 ↔ ¬ b.val < 10) →
      (a.val = 2 ∧ b.val = 15) ∨ (a.val = 2 ∧ b.val = 16) ∨ (a.val = 2 ∧ b.val = 19) ∨ (a.val = 3 ∧ b.val = 15) ∨ (a.val = 3 ∧ b.val = 16) ∨ (a.val = 3 ∧ b.val = 19) ∨ (a.val = 4 ∧ b.val = 15) ∨ (a.val = 4 ∧ b.val = 16) ∨ (a.val = 4 ∧ b.val = 19) ∨ (a.val = 10 ∧ b.val = 7) ∨ (a.val = 10 ∧ b.val = 8) ∨ (a.val = 10 ∧ b.val = 9) ∨ (a.val = 11 ∧ b.val = 7) ∨ (a.val = 11 ∧ b.val = 8) ∨ (a.val = 11 ∧ b.val = 9) ∨ (a.val = 14 ∧ b.val = 7) ∨ (a.val = 14 ∧ b.val = 8) ∨ (a.val = 14 ∧ b.val = 9) := by decide +kernel
  rcases choices a b ha hb mix with ⟨ha,hb⟩|⟨ha,hb⟩|⟨ha,hb⟩|⟨ha,hb⟩|⟨ha,hb⟩|⟨ha,hb⟩|⟨ha,hb⟩|⟨ha,hb⟩|⟨ha,hb⟩|⟨ha,hb⟩|⟨ha,hb⟩|⟨ha,hb⟩|⟨ha,hb⟩|⟨ha,hb⟩|⟨ha,hb⟩|⟨ha,hb⟩|⟨ha,hb⟩|⟨ha,hb⟩
  · simpa only [ha,hb] using case_2_15
  · simpa only [ha,hb] using case_2_16
  · simpa only [ha,hb] using case_2_19
  · simpa only [ha,hb] using case_3_15
  · simpa only [ha,hb] using case_3_16
  · simpa only [ha,hb] using case_3_19
  · simpa only [ha,hb] using case_4_15
  · simpa only [ha,hb] using case_4_16
  · simpa only [ha,hb] using case_4_19
  · simpa only [ha,hb] using case_10_7
  · simpa only [ha,hb] using case_10_8
  · simpa only [ha,hb] using case_10_9
  · simpa only [ha,hb] using case_11_7
  · simpa only [ha,hb] using case_11_8
  · simpa only [ha,hb] using case_11_9
  · simpa only [ha,hb] using case_14_7
  · simpa only [ha,hb] using case_14_8
  · simpa only [ha,hb] using case_14_9

#print axioms tested_pairs
#print axioms exclusive
#print axioms merged_legal
#print axioms merged_correct
end Alexrollo64.FusionCriterion
