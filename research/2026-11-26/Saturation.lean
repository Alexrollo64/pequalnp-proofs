import Accounting

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Alexrollo64.Saturation
open Alexrollo64.DisjointMatching
open Alexrollo64.DeletedEdge (Column cost pack bit_pack samples wanted)
open Alexrollo64.MatchingAccounting (valid budget other_reads)

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

end Alexrollo64.Saturation
#print axioms Alexrollo64.Saturation.lower
