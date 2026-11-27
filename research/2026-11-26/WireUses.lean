import CommonThree

namespace Alexrollo64.WireUses

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open Alexrollo64.Support20782 Alexrollo64.DisjointCopies Alexrollo64.OneDefect
open Alexrollo64.SharedOperand (overlap_pos)

def regular (n : Nat) : List Gate → Finset Nat → Prop
  | [], _ => True
  | g :: gs, s =>
    let mid := needed (n+1) gs s
    n ∈ mid ∧ g.inputs.toFinset.card = 2 ∧ regular (n+1) gs s

theorem tight_step (n : Nat) (g : Gate) (s : Finset Nat) (h : g.inputs.length ≤ 2)
    (t : (before n g s).card = s.card + 1) : n ∈ s ∧ g.inputs.toFinset.card = 2 := by
  by_cases live : n ∈ s
  · refine ⟨live,?_⟩
    have er := Finset.card_erase_add_one live
    have un := Finset.card_union_le (s.erase n) g.inputs.toFinset
    have len := List.toFinset_card_le (l := g.inputs)
    simp only [before,ite_eq_left live] at t
    omega
  · simp [before,live] at t

theorem regular_zero (gs : List Gate) (n : Nat) (s : Finset Nat)
    (arity : ∀ g ∈ gs, g.inputs.length ≤ 2) (d : (deficitList n gs s).sum = 0) :
    regular n gs s := by
  induction gs generalizing n with
  | nil => trivial
  | cons g gs ih =>
    let mid := needed (n+1) gs s
    have h := arity g (by simp)
    have k := before_card n g mid h
    change mid.card+1-(before n g mid).card + (deficitList (n+1) gs s).sum = 0 at d
    obtain ⟨act,tw⟩ := tight_step n g mid h (by omega)
    exact ⟨act,tw,ih _ (fun a ha => arity a (by simp [ha])) (by omega)⟩

theorem regular_one (gs : List Gate) (n : Nat) (s : Finset Nat) (w : Fin 7 → List Bool)
    (hw : ∀ i, (w i).length = n)
    (hm : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (d : (deficitList n gs s).sum = 1)
    (gain : mass w (needed n gs s) < mass (fun i => gs.foldl push (w i)) s) :
    regular n gs s := by
  induction gs generalizing n w with
  | nil => trivial
  | cons g gs ih =>
    let mid := needed (n+1) gs s
    let v := fun i => push (w i) g
    have hv (i) : (v i).length = n+1 := by simp [v,push,hw]
    have h := hm g (by simp)
    have hh := before_card n g mid h.2
    have ht : ∀ a ∈ gs, (a.op = .and ∨ a.op = .or) ∧ a.inputs.length ≤ 2 :=
      fun a ha => hm a (by simp [ha])
    change mid.card+1-(before n g mid).card + (deficitList (n+1) gs s).sum = 1 at d
    change mass w (before n g mid) < mass (fun i => gs.foldl push (v i)) s at gain
    by_cases tight : (before n g mid).card = mid.card+1
    · obtain ⟨act,tw⟩ := tight_step n g mid h.2 tight
      exact ⟨act,tw,ih _ v hv ht (by omega) (lt_of_le_of_lt (mass_step w n g mid hw h.2 h.1 tight) gain)⟩
    · have ac := account gs (n+1) s (fun a ha => (ht a ha).2)
      change _ + mid.card = _ at ac
      have gw := lt_of_lt_of_le gain (mass_run gs s v (n+1) hv ht (by change mid.card = _; omega))
      have live := (gain_active w n g mid hw gw).1
      obtain ⟨j,hj,_⟩ := overlap_pos n g mid w hw h.1 h.2 (by omega) gw
      have card := Finset.card_union_add_card_inter (mid.erase n) g.inputs.toFinset
      have er := Finset.card_erase_add_one live
      have pos := Finset.card_pos.mpr ⟨j,hj⟩
      have len := List.toFinset_card_le (l := g.inputs)
      simp only [before,ite_eq_left live] at d tight hh
      exact ⟨live,by omega,regular_zero gs _ s (fun a ha => (ht a ha).2) (by omega)⟩

theorem candidate_regular (c : Circuit) (hm : Monotone2 c) (hr : Represents (graph 3) c)
    (hs : c.size ≤ 24) : regular 30 c.gates {c.output} := by
  obtain ⟨support,one⟩ := CommonThree.candidate c hm hr hs
  let w := CommonThree.tests3 0
  apply regular_one _ _ _ w (fun i => by simp [w,CommonThree.tests3,oneEach])
    (fun g hg => ⟨by simpa using (hm g hg).1,(hm g hg).2⟩) one
  rw [support]
  have six : mass w CommonThree.requiredThree = 6 := by decide +kernel
  rw [six]
  simp only [mass,Finset.sum_singleton]
  change 6 < price (pack fun i => c.eval (w i))
  have eq : (fun i => c.eval (w i)) = (fun i => target (rows i) (cols i)) := by
    funext i; exact (hr _ _).trans (same_block _ _ _)
  rw [eq]; decide +kernel

/-- Gate input slots, plus one read for each requested output. -/
def uses (gs : List Gate) (s : Finset Nat) : Multiset Nat :=
  ↑(gs.flatMap Gate.inputs) + s.val

theorem uses_cons (g : Gate) (gs : List Gate) (s : Finset Nat) :
    uses (g::gs) s = (g.inputs : Multiset Nat) + uses gs s := by
  exact add_assoc (g.inputs : Multiset Nat) ((gs.flatMap Gate.inputs : List Nat) : Multiset Nat) s.val

theorem frontier_mem (gs : List Gate) (n : Nat) (s : Finset Nat) (j : Nat)
    (h : j ∈ needed n gs s) : j ∈ uses gs s := by
  induction gs generalizing n with
  | nil => simpa [uses,needed] using h
  | cons g gs ih =>
    change j ∈ before n g (needed (n+1) gs s) at h
    rw [uses_cons,Multiset.mem_add]
    unfold before at h
    split at h
    · rcases Finset.mem_union.mp h with hj|hj
      · exact Or.inr (ih _ (Finset.mem_erase.mp hj).2)
      · exact Or.inl (by simpa using hj)
    · exact Or.inr (ih _ h)

theorem outputs_mem (gs : List Gate) (n : Nat) (s : Finset Nat) (h : regular n gs s)
    (j : Nat) (lo : n ≤ j) (hi : j < n + gs.length) : j ∈ uses gs s := by
  induction gs generalizing n with
  | nil => simp at hi; omega
  | cons g gs ih =>
    rw [uses_cons,Multiset.mem_add]
    right
    rcases eq_or_lt_of_le lo with rfl|gt
    · exact frontier_mem _ _ _ _ h.1
    · apply ih (n+1) h.2.2 (by omega)
      simp only [List.length_cons] at hi
      omega

theorem uses_size (gs : List Gate) (n : Nat) (s : Finset Nat) (h : regular n gs s)
    (arity : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (uses gs s).card = 2 * gs.length + s.card := by
  induction gs generalizing n with
  | nil => simp [uses]
  | cons g gs ih =>
    have len := List.toFinset_card_le (l := g.inputs)
    have two := h.2.1
    have al := arity g (by simp)
    rw [uses_cons,Multiset.card_add,Multiset.coe_card,ih (n+1) h.2.2 (fun a ha => arity a (by simp [ha]))]
    simp only [List.length_cons]
    omega

theorem repeated {ι : Type} (gs : List Gate) (n : Nat) (s : Finset Nat)
    (w : ι → Fin 7 → List Bool) (h : CommonThree.joint n gs s w) :
    ∃ j, 30 ≤ j ∧ 2 ≤ (uses gs s).count j := by
  induction gs generalizing n w with
  | nil => exact h.elim
  | cons g gs ih =>
    rw [uses_cons]
    rcases h with ⟨j,hj,lo,_,_⟩|tail
    · have hp : j ∈ (g.inputs : Multiset Nat) := by simpa using (Finset.mem_inter.mp hj).2
      have hq := frontier_mem _ _ _ _ (Finset.mem_erase.mp (Finset.mem_inter.mp hj).1).2
      refine ⟨j,lo,?_⟩
      rw [Multiset.count_add]
      have := Multiset.count_pos.mpr hp
      have := Multiset.count_pos.mpr hq
      omega
    · obtain ⟨j,lo,hj⟩ := ih _ _ tail
      exact ⟨j,lo,by rw [Multiset.count_add]; omega⟩

def wires := CommonThree.requiredThree ∪ ((Finset.range 54).filter (30 ≤ ·))

/-- Exact slot multiset. Every essential input and every gate output occurs
    once, with a second occurrence of one intermediate gate output. -/
theorem candidate_uses (c : Circuit) (hm : Monotone2 c) (hr : Represents (graph 3) c)
    (hs : c.size ≤ 24) : ∃ j, 30 ≤ j ∧ j < 54 ∧
      uses c.gates {c.output} = wires.val + {j} := by
  have reg := candidate_regular c hm hr hs
  have size := lower 3 c.size ⟨c,hm,le_rfl,hr⟩
  have len : c.gates.length = 24 := by change c.gates.length ≤ 24 at hs; change 8*3 ≤ c.gates.length at size; omega
  obtain ⟨support,_⟩ := CommonThree.candidate c hm hr hs
  let u := uses c.gates {c.output}
  have incl : wires.val ≤ u := by
    apply (Multiset.le_iff_subset wires.nodup).mpr
    intro j hj
    change j ∈ wires at hj
    rcases Finset.mem_union.mp hj with h|h
    · exact frontier_mem _ _ _ _ (support ▸ h)
    · obtain ⟨up,lo⟩ := Finset.mem_filter.mp h
      exact outputs_mem _ _ _ reg _ lo (by simpa [len] using Finset.mem_range.mp up)
  obtain ⟨r,eq⟩ := exists_add_of_le incl
  have forty : wires.card = 48 := by decide +kernel
  have count := uses_size _ _ _ reg (fun g hg => (hm g hg).2)
  change u.card = _ at count
  rw [eq,Multiset.card_add,len,Finset.card_singleton] at count
  change wires.card + r.card = _ at count
  obtain ⟨k,rfl⟩ := Multiset.card_eq_one.mp (show r.card = 1 by omega)
  obtain ⟨j,lo,dbl⟩ := repeated _ _ _ _ (CommonThree.candidate_joint c hm hr hs)
  change 2 ≤ u.count j at dbl
  rw [eq,Multiset.count_add] at dbl
  have one := Multiset.nodup_iff_count_le_one.mp wires.nodup j
  have jk : j = k := by by_contra ne; simp [ne] at dbl; omega
  subst k
  have inside : j ∈ wires := by
    apply (Multiset.count_pos (s := wires.val)).mp
    simp at dbl
    omega
  have up : ∀ t ∈ wires, t < 54 := by
    intro t ht
    rcases Finset.mem_union.mp ht with h|h
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h
      exact (by decide +kernel : ∀ i : Fin 24, requiredWire 3 i < 54) i
    · exact Finset.mem_range.mp (Finset.mem_filter.mp h).1
  exact ⟨j,lo,up _ inside,eq⟩

def earlier (n : Nat) : List Gate → Prop
  | [] => True
  | g::gs => (∀ j ∈ g.inputs, j < n) ∧ earlier (n+1) gs

theorem earlier_of_frontier (gs : List Gate) (n : Nat) (s : Finset Nat)
    (reg : regular n gs s) (h : ∀ j ∈ needed n gs s, j < n) : earlier n gs := by
  induction gs generalizing n with
  | nil => trivial
  | cons g gs ih =>
    let mid := needed (n+1) gs s
    have live : n ∈ mid := reg.1
    change ∀ j ∈ before n g mid, j < n at h
    rw [before,ite_eq_left live] at h
    refine ⟨fun j hj => h j (Finset.mem_union_right _ (by simpa using hj)), ih _ reg.2.2 ?_⟩
    intro j hj
    by_cases e : j = n
    · omega
    · have := h j (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,hj⟩))
      omega

theorem candidate_earlier (c : Circuit) (hm : Monotone2 c) (hr : Represents (graph 3) c)
    (hs : c.size ≤ 24) : earlier 30 c.gates := by
  apply earlier_of_frontier _ _ _ (candidate_regular c hm hr hs)
  rw [(CommonThree.candidate c hm hr hs).1]
  intro j hj
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hj
  exact (by decide +kernel : ∀ t : Fin 24, requiredWire 3 t < 30) i

#print axioms candidate_earlier
#print axioms candidate_uses

def outputs (n : Nat) : List Gate → Multiset Nat
  | [] => 0
  | _::gs => {n} + outputs (n+1) gs

theorem outputs_range (gs : List Gate) (n : Nat) :
    outputs n gs = (List.range' n gs.length : Multiset Nat) := by
  induction gs generalizing n with
  | nil => rfl
  | cons g gs ih => simp only [outputs,List.length_cons,List.range',ih]; rfl

/-- Track any additive multiset of labels carried by the wires. At the cut
    gate, the expanded body is stored separately and its wire is reset to a marker. -/
def labeling {α : Type} (f : Nat → Multiset α) (cut : Nat) (marker body : Multiset α)
    (n : Nat) : List Gate → Prop
  | [] => True
  | g::gs => (if n = cut then f n = marker ∧ (g.inputs : Multiset Nat).bind f = body
                else (g.inputs : Multiset Nat).bind f = f n) ∧
                labeling f cut marker body (n+1) gs

theorem conservation {α : Type} (gs : List Gate) (n cut : Nat) (f : Nat → Multiset α)
    (marker body : Multiset α) (h : labeling f cut marker body n gs) :
    (((gs.flatMap Gate.inputs : List Nat) : Multiset Nat).bind f) +
        (if n ≤ cut ∧ cut < n+gs.length then marker else 0) =
    (outputs n gs).bind f + (if n ≤ cut ∧ cut < n+gs.length then body else 0) := by
  induction gs generalizing n with
  | nil => simp [outputs,show ¬(n ≤ cut ∧ cut < n) by omega]
  | cons g gs ih =>
    let tail := ((gs.flatMap Gate.inputs : List Nat) : Multiset Nat).bind f
    have t := ih (n+1) h.2
    change tail + _ = _ at t
    change (((g.inputs : Multiset Nat) + ↑(gs.flatMap Gate.inputs)).bind f) + _ =
      (({n} : Multiset Nat) + outputs (n+1) gs).bind f + _
    simp only [Multiset.add_bind,Multiset.singleton_bind,List.length_cons]
    change _ + tail + _ = _
    have first := h.1
    by_cases eq : n = cut
    · subst cut
      simp at first t ⊢
      rw [first.1,first.2,t]
      ac_rfl
    · simp [eq] at first
      have iff : (n ≤ cut ∧ cut < n + (gs.length + 1)) ↔
          (n+1 ≤ cut ∧ cut < n+1+gs.length) := by omega
      simp only [iff,first]
      simpa only [add_assoc] using congrArg (f n + ·) t

/-- For a consistent expansion that labels an ordinary input by itself,
    the private body and the output together use the 24 raw inputs once,
    plus two occurrences of the marker. -/
theorem cut_leaves (c : Circuit) (hm : Monotone2 c) (hr : Represents (graph 3) c)
    (hs : c.size ≤ 24) : ∃ j, 30 ≤ j ∧ j < 54 ∧
      ∀ (f : Nat → Multiset Nat) (body : Multiset Nat) (marker : Nat),
      labeling f j {marker} body 30 c.gates →
      (∀ i ∈ CommonThree.requiredThree, f i = {i}) → f j = {marker} →
      body + f c.output = CommonThree.requiredThree.val + {marker} + {marker} := by
  obtain ⟨j,lo,hi,hu⟩ := candidate_uses c hm hr hs
  refine ⟨j,lo,hi,?_⟩
  intro f body marker lab raw shared
  have low := lower 3 c.size ⟨c,hm,le_rfl,hr⟩
  have len : c.gates.length = 24 := by change c.gates.length ≤ 24 at hs; change 8*3 ≤ c.gates.length at low; omega
  have cons := conservation c.gates 30 j f {marker} body lab
  simp only [len,ite_eq_left (show 30 ≤ j ∧ j < 30+24 from ⟨lo,hi⟩)] at cons
  have w : wires.val = CommonThree.requiredThree.val + outputs 30 c.gates := by
    rw [outputs_range,len]
    decide +kernel
  have hrw : CommonThree.requiredThree.val.bind f = CommonThree.requiredThree.val := by
    calc
      _ = CommonThree.requiredThree.val.bind (fun i => {i}) := Multiset.bind_congr raw
      _ = _ := by induction CommonThree.requiredThree.val using Multiset.induction_on <;> simp_all
  have slots := congrArg (fun m : Multiset Nat => m.bind f) hu
  simp only [uses,Finset.singleton_val,Multiset.add_bind,Multiset.singleton_bind,w,hrw,shared] at slots
  let outs := (outputs 30 c.gates).bind f
  let ins := ((c.gates.flatMap Gate.inputs : List Nat) : Multiset Nat).bind f
  change ins + {marker} = outs + body at cons
  change ins + f c.output = CommonThree.requiredThree.val + outs + {marker} at slots
  apply add_left_cancel (a := outs)
  calc
    outs + (body + f c.output) = (ins + f c.output) + {marker} := by rw [← add_assoc,← cons]; ac_rfl
    _ = _ := by rw [slots]; ac_rfl

#print axioms cut_leaves
end Alexrollo64.WireUses
