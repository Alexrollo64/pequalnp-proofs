import PEqualNP.Defs

/-!
A lower bound of eight binary monotone gates for the 5 by 5 promise table
with mask 31917056. Eight input wires are individually indispensable. With
seven gates every backwards dependency expansion must add one wire. Thus
the two operands of every expanded gate are fresh, and their seven-test
weights can be summed without charging a shared wire twice. The output has
weight seven, while the eight indispensable input wires together have six.
-/

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

namespace Alexrollo64.Support20782

/-- Replace a requested gate output by all its input wires, working backwards. -/
def before (i : Nat) (g : Gate) (s : Finset Nat) : Finset Nat :=
  if i ∈ s then s.erase i ∪ g.inputs.toFinset else s

def needed (n : Nat) : List Gate → Finset Nat → Finset Nat
  | [], s => s
  | g :: gs, s => before n g (needed (n+1) gs s)

theorem before_card (i : Nat) (g : Gate) (s : Finset Nat) (h : g.inputs.length ≤ 2) :
    (before i g s).card ≤ s.card + 1 := by
  unfold before
  split_ifs with hi
  · have h1 := Finset.card_union_le (s.erase i) g.inputs.toFinset
    have h2 := List.toFinset_card_le (l := g.inputs)
    have h3 := Finset.card_erase_add_one hi
    omega
  · omega

theorem needed_card (n : Nat) (gs : List Gate) (s : Finset Nat)
    (hf : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (needed n gs s).card ≤ s.card + gs.length := by
  induction gs generalizing n s with
  | nil => simp [needed]
  | cons g gs ih =>
    have a := before_card n g (needed (n+1) gs s) (hf g (by simp))
    have b := ih (n+1) s (fun g h => hf g (by simp [h]))
    simp only [needed,List.length_cons]
    omega

def agrees (s : Finset Nat) (x y : List Bool) : Prop :=
  ∀ i ∈ s, x.getD i false = true → y.getD i false = true

def push (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem gate_mono (g : Gate) (x y : List Bool)
    (hop : g.op = .and ∨ g.op = .or)
    (h : agrees g.inputs.toFinset x y) :
    g.op.eval (g.inputs.map fun i => x.getD i false) = true →
    g.op.eval (g.inputs.map fun i => y.getD i false) = true := by
  rcases hop with ha | ho
  · simp only [ha,GateOp.eval,List.all_map,List.all_eq_true, Function.comp_apply, id_eq]
    exact fun hx i hi => h i (by simpa using hi) (hx i hi)
  · simp only [ho,GateOp.eval,List.any_map,List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i,hi,hx⟩
    exact ⟨i,hi,h i (by simpa using hi) hx⟩

theorem push_agrees (x y : List Bool) (g : Gate) (s : Finset Nat)
    (hlen : x.length = y.length) (hop : g.op = .and ∨ g.op = .or)
    (h : agrees (before x.length g s) x y) :
    agrees s (push x g) (push y g) := by
  intro i hi
  rcases lt_trichotomy i x.length with hlt | he | hgt
  · have hy : i < y.length := hlen ▸ hlt
    simp only [push,List.getD_append _ _ _ _ hlt,List.getD_append _ _ _ _ hy]
    apply h i
    by_cases hx : x.length ∈ s <;> simp [before,hx,hi,ne_of_lt hlt]
  · subst i
    have ha : agrees g.inputs.toFinset x y := fun i hi => h i (by simp [before, ‹x.length ∈ s›,hi])
    simpa [push,hlen,List.getD_eq_getElem?_getD] using gate_mono g x y hop ha
  · have hx : (push x g).length ≤ i := by simp [push]; omega
    rw [List.getD_eq_default _ _ hx]; simp

theorem run_agrees (gs : List Gate) (s : Finset Nat) (x y : List Bool)
    (hlen : x.length = y.length)
    (hm : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (h : agrees (needed x.length gs s) x y) :
    agrees s (gs.foldl push x) (gs.foldl push y) := by
  induction gs generalizing x y s with
  | nil => exact h
  | cons g gs ih =>
    apply ih
    · simp [push,hlen]
    · exact fun a ha => hm a (by simp [ha])
    · have hh := push_agrees x y g (needed (x.length+1) gs s) hlen (hm g (by simp)) h
      simpa [push] using hh

def support (c : Circuit) := needed 10 c.gates {c.output}

theorem eval_mono (c : Circuit) (hm : Monotone2 c) (x y : List Bool)
    (hx : x.length = 10) (hy : y.length = 10) (h : agrees (support c) x y) :
    c.eval x = true → c.eval y = true := by
  have h' := run_agrees c.gates {c.output} x y (hx.trans hy.symm)
    (fun g hg => by simpa using (hm g hg).1) (by simpa [hx,support] using h)
  exact h' c.output (by simp)

def target (u v : Fin 5) := (31917056 : Nat).testBit (5*u.val+v.val)
def required : Finset Nat := {2,3,4,5,6,7,8,9}

/-- For each distinguished input there are two promise rows such that that input
alone drops, and the target goes from true to false. -/
theorem witnesses : ∀ i : Fin 10, i.val ∈ required →
    ∃ a b d e : Fin 5, target a b = true ∧ target d e = false ∧
      ∀ j : Fin 10, j ≠ i → (oneEach a b).getD j.val false = true →
        (oneEach d e).getD j.val false = true := by decide +kernel

theorem must_use (c : Circuit) (hm : Monotone2 c) (hr : Represents target c) :
    required ⊆ support c := by
  intro i hi
  have hlt : i < 10 := by simp [required] at hi; omega
  obtain ⟨a,b,d,e,h1,h0,hw⟩ := witnesses ⟨i,hlt⟩ hi
  by_contra hmiss
  have le : agrees (support c) (oneEach a b) (oneEach d e) := by
    intro j hj
    by_cases hj' : j < 10
    · exact hw ⟨j,hj'⟩ (by intro he; apply hmiss; simpa [Fin.mk.inj he] using hj)
    · have hlen : (oneEach a b).length ≤ j := by simpa [oneEach] using Nat.le_of_not_gt hj'
      rw [List.getD_eq_default _ _ hlen]; simp
  have := eval_mono c hm _ _ (by simp [oneEach]) (by simp [oneEach]) le
  rw [hr a b,hr d e,h1,h0] at this
  contradiction

theorem seven_necessary (c : Circuit) (hm : Monotone2 c) (hr : Represents target c) :
    7 ≤ c.size := by
  have h1 := Finset.card_le_card (must_use c hm hr)
  have h2 := needed_card 10 c.gates {c.output} (fun g hg => (hm g hg).2)
  have count : required.card = 8 := by decide
  simp only [count,support] at h1
  simp only [Finset.card_singleton] at h2
  unfold Circuit.size
  omega


abbrev Word := BitVec 7
/-- Three bits per seven-test pattern, least significant field first. -/
def price (x : Word) : Nat :=
  (16877102379750682026150201864814161298759648775202590028053491825642454519831415925865358056768998815462010548789904 >>> (3*x.toNat)) % 8

def pack (f : Fin 7 → Bool) : Word := BitVec.ofBoolListLE [f 0, f 1, f 2, f 3, f 4, f 5, f 6]

theorem pack_and (f g : Fin 7 → Bool) : pack (fun k => f k && g k) = pack f &&& pack g := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem,BitVec.getLsbD_and,pack,BitVec.getLsbD_ofBoolListLE]
  interval_cases i <;> rfl

theorem pack_or (f g : Fin 7 → Bool) : pack (fun k => f k || g k) = pack f ||| pack g := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem,BitVec.getLsbD_or,pack,BitVec.getLsbD_ofBoolListLE]
  interval_cases i <;> rfl

def pairOK (a b : Word) : Bool :=
  decide (price (a &&& b) ≤ price a + price b) &&
  decide (price (a ||| b) ≤ price a + price b)

def rowOK (a : Nat) :=
  (List.range 128).all (fun n => pairOK (BitVec.ofNat 7 a) (BitVec.ofNat 7 n))

def blockOK (k : Nat) :=
  (List.range 4).all (fun r => rowOK (4*k+r))

theorem block_0 : blockOK 0 = true := by decide +kernel
theorem block_1 : blockOK 1 = true := by decide +kernel
theorem block_2 : blockOK 2 = true := by decide +kernel
theorem block_3 : blockOK 3 = true := by decide +kernel
theorem block_4 : blockOK 4 = true := by decide +kernel
theorem block_5 : blockOK 5 = true := by decide +kernel
theorem block_6 : blockOK 6 = true := by decide +kernel
theorem block_7 : blockOK 7 = true := by decide +kernel
theorem block_8 : blockOK 8 = true := by decide +kernel
theorem block_9 : blockOK 9 = true := by decide +kernel
theorem block_10 : blockOK 10 = true := by decide +kernel
theorem block_11 : blockOK 11 = true := by decide +kernel
theorem block_12 : blockOK 12 = true := by decide +kernel
theorem block_13 : blockOK 13 = true := by decide +kernel
theorem block_14 : blockOK 14 = true := by decide +kernel
theorem block_15 : blockOK 15 = true := by decide +kernel
theorem block_16 : blockOK 16 = true := by decide +kernel
theorem block_17 : blockOK 17 = true := by decide +kernel
theorem block_18 : blockOK 18 = true := by decide +kernel
theorem block_19 : blockOK 19 = true := by decide +kernel
theorem block_20 : blockOK 20 = true := by decide +kernel
theorem block_21 : blockOK 21 = true := by decide +kernel
theorem block_22 : blockOK 22 = true := by decide +kernel
theorem block_23 : blockOK 23 = true := by decide +kernel
theorem block_24 : blockOK 24 = true := by decide +kernel
theorem block_25 : blockOK 25 = true := by decide +kernel
theorem block_26 : blockOK 26 = true := by decide +kernel
theorem block_27 : blockOK 27 = true := by decide +kernel
theorem block_28 : blockOK 28 = true := by decide +kernel
theorem block_29 : blockOK 29 = true := by decide +kernel
theorem block_30 : blockOK 30 = true := by decide +kernel
theorem block_31 : blockOK 31 = true := by decide +kernel

set_option maxRecDepth 2048 in
theorem subadd (a b : Word) :
    price (a &&& b) ≤ price a + price b ∧ price (a ||| b) ≤ price a + price b := by
  have ha : a.toNat < 128 := a.isLt
  have hb : b.toNat < 128 := b.isLt
  let k := a.toNat / 4
  have hblock : blockOK k = true := by
    have hk : k < 32 := by dsimp [k]; omega
    interval_cases k
    · exact block_0
    · exact block_1
    · exact block_2
    · exact block_3
    · exact block_4
    · exact block_5
    · exact block_6
    · exact block_7
    · exact block_8
    · exact block_9
    · exact block_10
    · exact block_11
    · exact block_12
    · exact block_13
    · exact block_14
    · exact block_15
    · exact block_16
    · exact block_17
    · exact block_18
    · exact block_19
    · exact block_20
    · exact block_21
    · exact block_22
    · exact block_23
    · exact block_24
    · exact block_25
    · exact block_26
    · exact block_27
    · exact block_28
    · exact block_29
    · exact block_30
    · exact block_31

  have hrow := List.all_eq_true.mp hblock (a.toNat % 4) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  change rowOK (4*k+a.toNat%4) = true at hrow
  have idx : 4*k+a.toNat%4 = a.toNat := by dsimp [k]; omega
  rw [idx] at hrow
  have hpair := List.all_eq_true.mp hrow b.toNat (List.mem_range.mpr hb)
  simpa [pairOK] using hpair

def score (w : Fin 7 → List Bool) (i : Nat) := price (pack fun k => (w k).getD i false)

def mass (w : Fin 7 → List Bool) (s : Finset Nat) := ∑ i ∈ s, score w i

/-- With maximal support growth the two children are distinct new requirements. -/
theorem fresh_pair (g : Gate) (i : Nat) (s : Finset Nat) (hf : g.inputs.length ≤ 2)
    (tight : (before i g s).card = s.card+1) :
    ∃ a b, i ∈ s ∧ g.inputs = [a,b] ∧ a ≠ b ∧ a ∉ s.erase i ∧ b ∉ s.erase i := by
  have hi : i ∈ s := by
    by_contra d
    simp [before,d] at tight
  have hc := Finset.card_erase_add_one hi
  have hbase := Finset.card_union_le (s.erase i) g.inputs.toFinset
  simp only [before, ite_eq_left hi] at tight
  obtain ⟨op,ls⟩ := g
  cases ls with
  | nil => simp_all
  | cons a tail =>
    cases tail with
    | nil =>
      simp at hbase tight
      omega
    | cons b tail =>
      cases tail with
      | cons _ _ => simp at hf
      | nil =>
        refine ⟨a,b,hi,rfl,?_⟩
        simp only [List.toFinset_cons,List.toFinset_nil,Finset.insert_empty] at tight
        have eq : s.erase i ∪ {a,b} = insert a (insert b (s.erase i)) := by ext; simp
        rw [eq] at tight
        have hb := Finset.card_insert_le b (s.erase i)
        have ha := Finset.card_insert_le a (insert b (s.erase i))
        by_cases haa : a ∈ insert b (s.erase i)
        · rw [Finset.insert_eq_of_mem haa] at tight; omega
        by_cases hbb : b ∈ s.erase i
        · rw [Finset.insert_eq_of_mem hbb] at tight
          have hh := Finset.card_insert_le a (s.erase i)
          omega
        simp only [Finset.mem_insert,not_or] at haa
        exact ⟨haa.1,haa.2,hbb⟩


theorem read_other (w : List Bool) (g : Gate) (j : Nat) (hne : j ≠ w.length) :
    (push w g).getD j false = w.getD j false := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact List.getD_append _ _ _ _ h
  · have h' : (push w g).length ≤ j := by simp [push]; omega
    rw [List.getD_eq_default _ _ h', List.getD_eq_default _ _ h.le]

theorem mass_step (w : Fin 7 → List Bool) (n : Nat) (g : Gate) (s : Finset Nat)
    (hw : ∀ k, (w k).length = n) (hf : g.inputs.length ≤ 2)
    (hop : g.op = .and ∨ g.op = .or) (tight : (before n g s).card = s.card + 1) :
    mass (fun k => push (w k) g) s ≤ mass w (before n g s) := by
  obtain ⟨a,b,hi,hab,hne,ha,hb⟩ := fresh_pair g n s hf tight
  let w' := fun k => push (w k) g
  have keep (j : Nat) (hj : j ∈ s.erase n) : score w' j = score w j := by
    unfold score
    congr 2
    funext k
    apply read_other
    rw [hw]
    exact (Finset.mem_erase.mp hj).1
  have cost : score w' n ≤ score w a + score w b := by
    let A := pack fun k => (w k).getD a false
    let B := pack fun k => (w k).getD b false
    have law := subadd A B
    have read (k : Fin 7) : (w' k).getD n false = g.op.eval (g.inputs.map fun i => (w k).getD i false) := by
      simp [w',push,List.getD_eq_getElem?_getD,hw]
    rcases hop with hg | hg
    · unfold score
      simp_rw [read,hg,hab]
      simpa [GateOp.eval,pack_and,A,B] using law.1
    · unfold score
      simp_rw [read,hg,hab]
      simpa [GateOp.eval,pack_or,A,B] using law.2
  have bef : before n g s = insert a (insert b (s.erase n)) := by
    ext j
    simp [before,hi,hab]
  have hsum := Finset.sum_congr (s₁ := s.erase n) rfl keep
  have hs := Finset.sum_erase_add _ (score w') hi
  have ha' : a ∉ insert b (s.erase n) := by simp [hne,ha]
  unfold mass
  change ∑ i ∈ s, score w' i ≤ _
  rw [← hs,hsum,bef,Finset.sum_insert ha',Finset.sum_insert hb]
  change (∑ i ∈ s.erase n, score w i) + score w' n ≤ score w a + (score w b + ∑ i ∈ s.erase n, score w i)
  omega

theorem mass_run (gs : List Gate) (s : Finset Nat) (w : Fin 7 → List Bool) (n : Nat)
    (hw : ∀ k, (w k).length = n)
    (hm : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (tight : (needed n gs s).card = s.card + gs.length) :
    mass (fun k => gs.foldl push (w k)) s ≤ mass w (needed n gs s) := by
  induction gs generalizing n s w with
  | nil => simp [needed]
  | cons g gs ih =>
    let mid := needed (n+1) gs s
    have hg := hm g (by simp)
    have hm' : ∀ a ∈ gs, (a.op = .and ∨ a.op = .or) ∧ a.inputs.length ≤ 2 :=
      fun a ha => hm a (by simp [ha])
    have h1 := before_card n g mid hg.2
    have h2 : mid.card ≤ s.card + gs.length := needed_card _ _ _ (fun a ha => (hm' a ha).2)
    change (before n g mid).card = s.card + (g :: gs).length at tight
    simp only [List.length_cons] at tight
    have ha : mid.card = s.card + gs.length := by omega
    have hb : (before n g mid).card = mid.card + 1 := by omega
    have htail := ih s (fun k => push (w k) g) (n+1) (fun k => by simp [push,hw]) hm' ha
    exact htail.trans (mass_step w n g mid hw hg.2 hg.1 hb)

def rows : Fin 7 → Fin 5 := ![2,2,3,3,4,4,4]
def cols : Fin 7 → Fin 5 := ![0,1,1,4,0,1,4]
def tests (k : Fin 7) := oneEach (rows k) (cols k)

theorem no_seven : ¬ RepSizeAtMost target 7 := by
  rintro ⟨c,hm,hsize,hr⟩
  have hsubset := must_use c hm hr
  have hc : required.card = 8 := by decide
  have hbound := needed_card 10 c.gates {c.output} (fun g hg => (hm g hg).2)
  simp only [Finset.card_singleton] at hbound
  change c.gates.length ≤ 7 at hsize
  have heq : required = support c := Finset.eq_of_subset_of_card_le hsubset (by
    unfold support; omega)
  have tight : (needed 10 c.gates {c.output}).card = ({c.output} : Finset Nat).card + c.gates.length := by
    change (support c).card = _
    rw [← heq,hc,Finset.card_singleton]
    have hg := seven_necessary c hm hr
    change 7 ≤ c.gates.length at hg
    omega
  have hmass := mass_run c.gates {c.output} tests 10 (fun k => by simp [tests,oneEach])
    (fun g hg => ⟨by simpa using (hm g hg).1,(hm g hg).2⟩) tight
  change mass (fun k => c.gates.foldl push (tests k)) {c.output} ≤ mass tests (support c) at hmass
  rw [← heq] at hmass
  have limit : mass tests required = 6 := by decide +kernel
  rw [limit] at hmass
  simp only [mass,Finset.sum_singleton,score] at hmass
  change price (pack (fun k => c.eval (tests k))) ≤ 6 at hmass
  have evals : (fun k => c.eval (tests k)) = (fun k => target (rows k) (cols k)) := funext fun k => hr _ _
  rw [evals] at hmass
  have bad : price (pack (fun k => target (rows k) (cols k))) = 7 := by decide +kernel
  omega

theorem mask31917056_lower :
    ¬ PEqualNP.Represents.RepSizeAtMost
      (fun u v : Fin 5 => (31917056 : Nat).testBit (5 * u.val + v.val)) 7 :=
  no_seven

#print axioms mask31917056_lower
end Alexrollo64.Support20782
