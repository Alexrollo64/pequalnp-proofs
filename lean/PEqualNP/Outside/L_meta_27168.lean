import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_27168_aux.DisjointMatching

def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
def target (x : Fin 9 → Bool) :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def seed (i j : Fin 9) (b : Bool) : Nat := ([160,0,160,162,160,164,160,168,160,176,272,160,160,224,272,160,160,272,96,97,96,0,96,100,96,104,96,112,264,96,264,96,96,224,96,264,80,81,80,82,80,0,80,88,136,80,80,112,136,80,80,136,80,336,132,133,132,134,258,132,132,0,132,148,132,164,132,196,258,132,132,258,68,69,68,70,257,68,68,76,68,0,68,100,257,68,68,196,68,257,66,67,129,66,66,70,66,74,66,82,66,0,129,66,66,129,66,322,20,21,20,22,34,20,20,28,34,20,20,34,20,0,20,148,20,276,12,13,12,14,33,12,33,12,12,28,12,33,12,76,12,0,12,268,10,11,17,10,10,14,17,10,10,17,10,42,10,74,10,138,10,0] : List Nat).getD (18*i.val+2*j.val+b.toNat) 0
def x (i j : Fin 9) (b : Bool) (k : Fin 9) := (seed i j b).testBit k.val
def y (i j : Fin 9) (b : Bool) (k : Fin 9) := x i j b k || decide (k=i)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pivots : ∀ (i j : Fin 9) (b : Bool), i ≠ j →
  target (x i j b) ≠ target (y i j b) ∧ x i j b j = b := by decide +kernel

structure Pair where
  a : Fin 9
  b : Fin 9
  useOr : Bool

def val (p : Pair) (z : Fin 9 → Bool) := if p.useOr then z p.a || z p.b else z p.a && z p.b

theorem untouched (p : Pair) (i j : Fin 9) (b : Bool) (h₁ : p.a ≠ i) (h₂ : p.b ≠ i) :
    val p (x i j b) = val p (y i j b) := by simp [val,y,h₁,h₂]

theorem shield (p : Pair) (i : Fin 9) (h : p.a ≠ p.b) :
    ∃ j, i ≠ j ∧ val p (x i j p.useOr) = val p (y i j p.useOr) := by
  by_cases a : p.a = i
  · refine ⟨p.b, a ▸ h, ?_⟩
    have ne : p.b ≠ i := by grind
    have eq := (pivots i p.b p.useOr ne.symm).2
    cases op : p.useOr <;> simp_all [val,y]
  · refine ⟨p.a,Ne.symm a,?_⟩
    have eq := (pivots i p.a p.useOr (Ne.symm a)).2
    cases op : p.useOr <;> simp_all [val,y]

theorem raw (z : Fin 9 → Bool) (k : Fin 9) : (List.ofFn z).getD k.val false = z k := by
  fin_cases k <;> rfl

def gate (p : Pair) : Gate := ⟨if p.useOr then .or else .and,[p.a.val,p.b.val]⟩
theorem step_gate (p : Pair) (z : Fin 9 → Bool) (extra : List Bool) :
    step (List.ofFn z ++ extra) (gate p) = (List.ofFn z ++ extra) ++ [val p z] := by
  have h (k : Fin 9) : (List.ofFn z ++ extra).getD k.val false = z k := by
    rw [List.getD_append _ _ _ _ (by simp)]
    exact raw z k
  unfold step gate val
  simp only [List.map_cons,List.map_nil,h]
  cases b : p.useOr <;> simp [GateOp.eval]

def agree (i : Nat) (x y : List Bool) := x.length = y.length ∧
  ∀ j, j ≠ i → x.getD j false = y.getD j false

theorem keep (gs : List Gate) (i : Nat) (x y : List Bool) (h : agree i x y)
    (miss : i ∉ gs.flatMap Gate.inputs) : agree i (gs.foldl step x) (gs.foldl step y) := by
  induction gs generalizing x y with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.flatMap_cons,List.mem_append,not_or] at miss
    apply ih _ _ _ miss.2
    have eq : (g.inputs.map fun j => x.getD j false) = (g.inputs.map fun j => y.getD j false) := by
      apply List.map_congr_left
      intro j hj; exact h.2 j (fun e => miss.1 (e ▸ hj))
    refine ⟨by simp [step,h.1],?_⟩
    intro j ne
    by_cases lt : j < x.length
    · exact (List.getD_append _ _ _ _ lt).trans ((h.2 j ne).trans (List.getD_append _ _ _ _ (h.1 ▸ lt)).symm)
    · unfold step
      rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by have := h.1; omega),eq,h.1]

theorem slots (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2*gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have a := h g (by simp)
    have b := ih (fun x hx => h x (by simp [hx]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons]; omega

end PEqualNP.Outside.L_meta_27168_aux.DisjointMatching


namespace PEqualNP.Outside.L_meta_27168_aux.DeletedEdge
open PEqualNP.Outside.L_meta_27168_aux.DisjointMatching (target)

abbrev Column := BitVec 6

def cost (x : Column) : Nat :=
  (49642165864535503169320950734538024280 >>> (2*x.toNat)) % 4

theorem laws : ∀ a b : Column, cost (a &&& b) ≤ cost a + cost b ∧
    cost (a ||| b) ≤ cost a + cost b ∧ cost (~~~a) = cost a := by decide +kernel

def samples : Fin 9 → Fin 6 → Nat :=
  ![![266,264,258,228,230,236],![273,272,257,228,229,244],![273,272,17,170,171,426],
    ![273,272,257,228,229,244],![161,129,33,78,110,206],![273,257,17,78,94,334],
    ![273,272,17,170,171,426],![273,257,17,78,94,334],![161,129,33,78,110,206]]

def pack (f : Fin 6 → Bool) : Column :=
  BitVec.ofBoolListLE [f 0,f 1,f 2,f 3,f 4,f 5]

theorem bit_pack (f : Fin 6 → Bool) (j : Fin 6) : (pack f).getLsbD j.val = f j := by
  unfold pack
  rw [BitVec.getLsbD_ofBoolListLE]
  fin_cases j <;> rfl


def wire (i j : Fin 9) := pack (fun n => (samples i n).testBit j)
def wanted (i : Fin 9) := pack (fun n => target (fun j => (samples i n).testBit j))
theorem data_ok : ∀ i, wire i i = 0 ∧ cost (wanted i) = 3 ∧
    (List.ofFn (fun j => cost (wire i j))).sum = 2 := by decide +kernel

theorem subSum {x y : List Nat} (h : x.Sublist y) : x.sum ≤ y.sum := by
  induction h <;> simp_all <;> omega

end PEqualNP.Outside.L_meta_27168_aux.DeletedEdge


namespace PEqualNP.Outside.L_meta_27168_aux.MatchingAccounting
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_27168_aux.DisjointMatching
open PEqualNP.Outside.L_meta_27168_aux.DeletedEdge (cost Column samples wanted)

def valid (v : Nat → Nat) (n : Nat) : List Gate → Prop
  | [] => True
  | g :: gs => v n ≤ (g.inputs.map v).sum ∧ valid v (n+1) gs

theorem total (v : Nat → Nat) (n : Nat) (gs : List Gate) (h : valid v n gs) :
    ((List.range' n gs.length).map v).sum ≤ ((gs.flatMap Gate.inputs).map v).sum := by
  induction gs generalizing n with
  | nil => simp
  | cons g gs ih =>
    obtain ⟨first,rest⟩ := h
    have tail := ih (n+1) rest
    simp [List.range'_succ]; omega

theorem other_reads (i j k : Fin 9) (a b : Bool) (ij : i ≠ j) (ik : i ≠ k) (jk : j ≠ k) (c : Circuit) (gs : List Gate) (shape : c.gates = (gate (⟨i,j,a⟩ : Pair))::(gate (⟨i,k,b⟩ : Pair))::gs)
    (last : c.output+1 = 9+c.size) (correct : ∀ x, c.eval (List.ofFn x) = target x) :
    ∀ e : Fin 9, e ≠ i → e.val ∈ gs.flatMap Gate.inputs := by
  intro e ei
  by_contra absent

  have col : ∃ u v, target u ≠ target v ∧ val ⟨i,j,a⟩ u = val ⟨i,j,a⟩ v ∧
      val ⟨i,k,b⟩ u = val ⟨i,k,b⟩ v ∧ ∀ z, z ≠ e → u z = v z := by
    by_cases ej : e = j
    · obtain ⟨z,ne,eq⟩ := shield ⟨i,j,a⟩ e ij
      exact ⟨_,_,(pivots e z a ne).1,eq,untouched ⟨i,k,b⟩ e z a (Ne.symm ei) (by grind), fun h hn => by simp [y,hn]⟩
    · obtain ⟨z,ne,eq⟩ := shield ⟨i,k,b⟩ e ik
      exact ⟨_,_,(pivots e z b ne).1,untouched ⟨i,j,a⟩ e z b (Ne.symm ei) (Ne.symm ej),eq,fun h hn => by simp [y,hn]⟩
  obtain ⟨u,v,tar,eqp,eqq,eq⟩ := col
  have after (z : Fin 9 → Bool) : step (step (List.ofFn z) (gate (⟨i,j,a⟩ : Pair))) (gate (⟨i,k,b⟩ : Pair)) =
      (List.ofFn z ++ [val ⟨i,j,a⟩ z]) ++ [val ⟨i,k,b⟩ z] := by
    rw [show step (List.ofFn z) (gate (⟨i,j,a⟩ : Pair)) = List.ofFn z ++ [val ⟨i,j,a⟩ z] by simpa using step_gate (⟨i,j,a⟩ : Pair) z [], step_gate]
  have agreeStart : agree e.val (step (step (List.ofFn u) (gate (⟨i,j,a⟩ : Pair))) (gate (⟨i,k,b⟩ : Pair)))
      (step (step (List.ofFn v) (gate (⟨i,j,a⟩ : Pair))) (gate (⟨i,k,b⟩ : Pair))) := by
    rw [after,after]; constructor
    · simp
    intro j ne
    simp only [List.append_assoc,eqp,eqq]
    by_cases lt : j < 9
    · rw [List.getD_append (List.ofFn u) _ _ _ (by simpa), List.getD_append (List.ofFn v) _ _ _ (by simpa)]
      exact (raw u ⟨j,lt⟩).trans ((eq ⟨j,lt⟩ (by grind)).trans (raw v ⟨j,lt⟩).symm)
    · rw [List.getD_append_right (List.ofFn u) _ _ _ (by simpa using Nat.le_of_not_gt lt),
          List.getD_append_right (List.ofFn v) _ _ _ (by simpa using Nat.le_of_not_gt lt)]
      simp
  have same := keep gs e.val _ _ agreeStart absent
  have far : c.output ≠ e.val := by simp [Circuit.size,shape] at last; omega
  apply tar
  rw [← correct,← correct]
  unfold Circuit.eval Circuit.wires
  rw [shape]
  exact same.2 c.output far

theorem budget (i : Fin 9) (gs : List Gate) (v : Nat → Nat)
    (arity : ∀ g ∈ gs, g.inputs.length ≤ 2) (small : gs.length ≤ 9)
    (used : ∀ x < 10 + gs.length, x ≠ i.val → x ∈ gs.flatMap Gate.inputs)
    (h : valid v 11 gs) (free₁ : v 9 = 0) (free₂ : v 10 = 0)
    (start : ((List.range 9).map v).sum = 2) :
    v (10+gs.length) ≤ 2 := by
  let inputs := gs.flatMap Gate.inputs
  let out := 10+gs.length
  have lt : i.val < out := by dsimp [out]; omega
  let req := (List.range out).erase i.val
  have nod : req.Nodup := List.Nodup.erase _ (List.nodup_range)
  have sub : req.Subperm inputs := by
    apply List.subperm_of_subset nod
    intro x hx
    have mem := List.mem_of_mem_erase hx
    have ne : x ≠ i.val := by
      intro e; subst x; exact List.Nodup.not_mem_erase List.nodup_range hx
    exact used _ (List.mem_range.mp mem) ne
  have len : req.length = out-1 := by simpa [req] using List.length_erase_of_mem (List.mem_range.mpr lt)
  have slots := PEqualNP.Outside.L_meta_27168_aux.DisjointMatching.slots gs arity
  obtain ⟨l,perm,sl⟩ := sub
  have same : l = inputs := sl.eq_of_length_le (by
    have := perm.length_eq; dsimp [inputs,out] at *; omega)
  have P : inputs.Perm req := same ▸ perm
  have cap := total v 11 gs h
  have cover := ((List.erase_sublist (l := List.range out) (a := i.val)).map v)
  have H := PEqualNP.Outside.L_meta_27168_aux.DeletedEdge.subSum cover
  have eq := (P.map v).sum_eq
  change _ ≤ (inputs.map v).sum at cap
  have pack : List.range (11+gs.length) = List.range 9 ++ [9,10] ++ List.range' 11 gs.length := by
    rw [List.range_add, ← List.range'_eq_map_range]
    rfl
  have split : List.range (11+gs.length) = List.range out ++ [out] := by
    change List.range (11+gs.length) = _
    rw [show 11+gs.length = out+1 by dsimp [out]; omega, List.range_succ]
  have both := congrArg (fun l : List Nat => (l.map v).sum) (split.symm.trans pack)
  simp only [List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at both
  change (req.map v).sum ≤ _ at H
  change v out ≤ 2
  omega

end PEqualNP.Outside.L_meta_27168_aux.MatchingAccounting


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_27168_aux.Saturation
open PEqualNP.Outside.L_meta_27168_aux.DisjointMatching
open PEqualNP.Outside.L_meta_27168_aux.DeletedEdge (Column cost pack bit_pack samples wanted)
open PEqualNP.Outside.L_meta_27168_aux.MatchingAccounting (valid budget other_reads)

def sig (w : Fin 6 → List Bool) (i : Nat) := pack (fun s => (w s).getD i false)

def normal (n : Nat) (g : Gate) : Prop :=
  (g.op = .not ∧ ∃ a < n, g.inputs = [a]) ∨
  ((g.op = .and ∨ g.op = .or) ∧ ∃ a b, a < b ∧ b < n ∧ g.inputs = [a,b])

theorem eqcol (a b : Column) (h : ∀ s : Fin 6, a.getLsbD s = b.getLsbD s) : a=b :=
  BitVec.eq_of_getLsbD_eq (fun i hi => h ⟨i,hi⟩)

theorem certify (gs : List Gate) (n : Nat) (w : Fin 6 → List Bool)
    (len : ∀ s, (w s).length = n) (ok : ∀ k : Fin gs.length, normal (n+k.val) (gs.get k)) :
    ∃ f : Nat → Column, (∀ j < n, f j = sig w j) ∧ valid (cost ∘ f) n gs ∧
      ∀ j, f j = sig (fun s => gs.foldl step (w s)) j := by
  induction gs generalizing n w with
  | nil => exact ⟨sig w,fun _ _ => rfl,trivial,fun _ => rfl⟩
  | cons g gs ih =>
    let w' := fun s => step (w s) g
    obtain ⟨f,old,rest,endval⟩ := ih (n+1) w' (fun s => by simp [w',step,len])
      (fun k => by simpa [Nat.add_assoc,Nat.add_comm 1] using ok k.succ)
    have prev (j : Nat) (hj : j < n) : f j = sig w j := by
      rw [old j (by omega)]
      apply congrArg pack; funext s
      exact List.getD_append _ _ _ _ (by simpa [len] using hj)
    refine ⟨f,prev,⟨?_,rest⟩,endval⟩
    have valn (s : Fin 6) : (f n).getLsbD s = g.op.eval (g.inputs.map fun j => (w s).getD j false) := by
      rw [old n (by omega),sig,bit_pack]
      dsimp [w',step]; rw [List.getD_append_right _ _ _ _ (by simp [len]),len]
      simp
    have ar (j : Nat) (hj : j<n) (s : Fin 6) : (f j).getLsbD s = (w s).getD j false := by
      rw [prev j hj,sig,bit_pack]
    have first : normal n g := by simpa using ok ⟨0,by simp⟩
    rcases first with ⟨o,a,ha,ins⟩ | ⟨ops,a,b,ab,bl,ins⟩
    · have eq : f n = ~~~(f a) := eqcol _ _ (fun s => by rw [valn,BitVec.getLsbD_not,ar a ha]; simp [o,ins,GateOp.eval,s.isLt])
      simp [ins,Function.comp_def,eq,(DeletedEdge.laws _ 0).2.2]
    · have al : a<n := by omega
      rcases ops with o|o
      · have eq : f n = (f a &&& f b) := eqcol _ _ (fun s => by rw [valn,BitVec.getLsbD_and,ar a al,ar b bl]; simp [o,ins,GateOp.eval])
        simpa [eq,ins,Function.comp_def] using (DeletedEdge.laws (f a) (f b)).1
      · have eq : f n = (f a ||| f b) := eqcol _ _ (fun s => by rw [valn,BitVec.getLsbD_or,ar a al,ar b bl]; simp [o,ins,GateOp.eval])
        simpa [eq,ins,Function.comp_def] using (DeletedEdge.laws (f a) (f b)).2.1

theorem missing : ∀ (i : Fin 9) (s : Fin 6), (samples i s).testBit i.val = false := by decide +kernel

theorem lower (i j k : Fin 9) (ij : i ≠ j) (ik : i ≠ k) (jk : j ≠ k)
    (c : Circuit) (gs : List Gate)
    (shape : c.gates = gate ⟨i,j,false⟩ :: gate ⟨i,k,false⟩ :: gs)
    (fan : FanInTwo c) (last : c.output+1 = 9+c.size)
    (correct : ∀ x, c.eval (List.ofFn x) = target x)
    (legal : ∀ l : Fin c.gates.length, normal (9+l.val) (c.gates.get l))
    (live : ∀ l : Fin c.gates.length, l.val+1 < c.gates.length →
      ∃ z : Fin c.gates.length, l.val < z.val ∧ 9+l.val ∈ (c.gates.get z).inputs) :
    12 ≤ c.size := by
  by_contra! small
  have length : c.size = gs.length+2 := by simp [Circuit.size,shape]
  let input := fun (s : Fin 6) (e : Fin 9) => (samples i s).testBit e.val
  let w := fun s => List.ofFn (input s) ++ [false,false]
  have after (s : Fin 6) : step (step (List.ofFn (input s)) (gate ⟨i,j,false⟩)) (gate ⟨i,k,false⟩) = w s := by
    rw [show step (List.ofFn (input s)) (gate ⟨i,j,false⟩) = List.ofFn (input s) ++ [val ⟨i,j,false⟩ (input s)] by simpa using step_gate ⟨i,j,false⟩ (input s) [],step_gate]
    simp [val,w,input,missing,List.append_assoc]
  have tail : ∀ l : Fin gs.length, normal (11+l.val) (gs.get l) := by
    intro l
    let h := legal ⟨2+l.val, by simp [shape]; omega⟩
    simp [shape, List.get_eq_getElem, Nat.add_comm 2 l.val] at h
    convert h using 1 <;> omega
  obtain ⟨f,old,h,endval⟩ := certify gs 11 w (fun s => by simp [w]) tail
  have rawEq (e : Fin 9) : f e.val = DeletedEdge.wire i e := by
    rw [old _ (by omega)]
    apply congrArg pack; funext s
    change (List.ofFn (input s) ++ _).getD e.val false = input s e
    rw [List.getD_append _ _ _ _ (by simp)]
    exact raw (input s) e
  have zero (z : Nat) (hz : z=9 ∨ z=10) : f z = 0 := by
    rcases hz with rfl|rfl <;> rw [old _ (by decide)] <;> apply eqcol <;> intro s <;> rw [sig,bit_pack] <;> simp [w]
  have sum : ((List.range 9).map (cost ∘ f)).sum = 2 := by
    have eq : ∀ e : Fin 9, cost (f e.val) = cost (DeletedEdge.wire i e) := fun e => congrArg cost (rawEq e)
    change (List.ofFn (fun e : Fin 9 => cost (f e.val))).sum = 2
    simp_rw [eq]; exact (DeletedEdge.data_ok i).2.2
  have rawReads := other_reads i j k false false ij ik jk c gs shape last correct
  have uses (wire : Nat) (hw : wire < 10+gs.length) (ne : wire ≠ i.val) : wire ∈ gs.flatMap Gate.inputs := by
    by_cases lo : wire < 9
    · exact rawReads ⟨wire,lo⟩ (by grind)
    · let ix : Fin c.gates.length := ⟨wire-9, by simp [shape]; omega⟩
      obtain ⟨later,_,used⟩ := live ix (by dsimp [ix]; simp [shape]; omega)
      have mem : c.gates.get later ∈ gate ⟨i,j,false⟩ :: gate ⟨i,k,false⟩ :: gs := shape ▸ List.get_mem c.gates later
      have u : wire ∈ (c.gates.get later).inputs := by simpa [ix,Nat.add_sub_of_le (by omega : 9 ≤ wire)] using used
      rcases List.mem_cons.mp mem with a|m
      · rw [a] at u; simp [gate] at u; omega
      · rcases List.mem_cons.mp m with a|m
        · rw [a] at u; simp [gate] at u; omega
        · exact List.mem_flatMap.mpr ⟨_,m,u⟩
  have lim := budget i gs (cost ∘ f) (fun g hg => (fan g (by simp [shape,hg])).2) (by omega) uses h
    (by simp [Function.comp_def,zero 9 (Or.inl rfl)]; decide +kernel)
    (by simp [Function.comp_def,zero 10 (Or.inr rfl)]; decide +kernel) sum
  have out : c.output = 10+gs.length := by omega
  have eq : f c.output = wanted i := by
    rw [endval]
    apply congrArg pack; funext s
    have h := correct (input s)
    change (c.gates.foldl step (List.ofFn (input s))).getD c.output false = target (input s) at h
    rw [shape,List.foldl_cons,List.foldl_cons,after] at h
    exact h
  change cost (f (10+gs.length)) ≤ 2 at lim
  rw [← out,eq,(DeletedEdge.data_ok i).2.1] at lim
  omega

end PEqualNP.Outside.L_meta_27168_aux.Saturation

theorem PEqualNP.Outside.L_meta_27168 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 5]⟩)) := by
  rintro ⟨c,fan,small,correct,last,legal,_,live,one,two⟩
  obtain ⟨gs,shape⟩ : ∃ gs, c.gates = ⟨.and,[0,4]⟩ :: ⟨.and,[0,5]⟩ :: gs := by
    cases h : c.gates with
    | nil => simp [h] at one
    | cons a rest =>
      cases rest with
      | nil => simp [h] at two
      | cons b gs => simp [h] at one two; exact ⟨gs,by simp [one,two]⟩
  have h := PEqualNP.Outside.L_meta_27168_aux.Saturation.lower 0 4 5 (by decide) (by decide) (by decide) c gs shape fan last correct legal live
  omega
