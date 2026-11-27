import PaddedRows

namespace Alexrollo64.DisjointCopies

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open Alexrollo64.Support20782
open Alexrollo64.PaddedRows (one_read)

/-- k diagonal copies of the 5 by 5 graph, with no edges between copies. -/
def graph (k : Nat) (u v : Fin (5*k)) : Bool :=
  decide (u.val/5 = v.val/5) && (31917056 : Nat).testBit (5*(u.val%5)+v.val%5)

def vertex {k : Nat} (b : Fin k) (i : Fin 5) : Fin (5*k) := ⟨5*b.val+i.val,by omega⟩

theorem same_block {k : Nat} (b : Fin k) (a v : Fin 5) :
    graph k (vertex b a) (vertex b v) = target a v := by
  simp [graph,vertex,target,show (5*b.val+a.val)/5 = b.val by omega,show (5*b.val+v.val)/5 = b.val by omega,Nat.add_mod,Nat.mod_eq_of_lt a.isLt,Nat.mod_eq_of_lt v.isLt]

def wire {k : Nat} (b : Fin k) (i : Nat) : Nat :=
  if i < 5 then 5*b.val+i else 5*k+5*b.val+(i-5)

theorem wire_read {k : Nat} (b : Fin k) (a v : Fin 5) (i : Nat) (hi : i < 10) :
    (oneEach (vertex b a) (vertex b v)).getD (wire b i) false =
    (oneEach a v).getD i false := by
  rw [one_read,one_read]
  by_cases h : i < 5
  · have h1 : 5*b.val+i ≠ 5*k+(5*b.val+v.val) := by omega
    simp [wire,h,vertex,h1,show i ≠ 5+v.val by omega]
  · have h1 : 5*k+5*b.val+(i-5) ≠ 5*b.val+a.val := by omega
    have h2 : 5*k+5*b.val+(i-5) = 5*k+(5*b.val+v.val) ↔ i = 5+v.val := by omega
    simp [wire,h,vertex,h1,h2,show i ≠ a.val by omega]

theorem indispensable {k : Nat} (b : Fin k) (i : Fin 10) (hi : i.val ∈ required)
    (c : Circuit) (hm : Monotone2 c) (hr : Represents (graph k) c) :
    wire b i.val ∈ needed (5*k+5*k) c.gates {c.output} := by
  obtain ⟨a,v,d,e,h1,h0,hw⟩ := witnesses i hi
  let x := oneEach (vertex b a) (vertex b v)
  let y := oneEach (vertex b d) (vertex b e)
  have hx : x.length = 5*k+5*k := by simp [x,oneEach]
  have hy : y.length = 5*k+5*k := by simp [y,oneEach]
  by_contra miss
  have agree : agrees (needed x.length c.gates {c.output}) x y := by
    rw [hx]
    intro j hj hjx
    have diff : j ≠ wire b i.val := fun eq => miss (eq ▸ hj)
    have small (t : Fin 10) (he : j = wire b t.val) : y.getD j false = true := by
      have ne : t ≠ i := fun ht => diff (ht ▸ he)
      rw [he] at hjx ⊢
      rw [show x = _ from rfl, wire_read b a v t.val t.isLt] at hjx
      exact (wire_read b d e t.val t.isLt).trans (hw t ne hjx)
    change (oneEach _ _).getD j false = true at hjx
    rw [one_read] at hjx
    simp only [Bool.or_eq_true,decide_eq_true_eq] at hjx
    rcases hjx with h | h
    · exact small ⟨a.val,by omega⟩ (by simpa [wire,vertex,a.isLt] using h)
    · apply small ⟨5+v.val,by omega⟩
      simp only [wire,show ¬5+v.val < 5 by omega,if_false,Nat.add_sub_cancel_left]
      simpa [vertex,Nat.add_assoc] using h
  have monot := run_agrees c.gates {c.output} x y (hx.trans hy.symm)
    (fun g hg => by simpa using (hm g hg).1) agree c.output (by simp)
  change c.eval x = true → c.eval y = true at monot
  change c.eval (oneEach _ _) = true → c.eval (oneEach _ _) = true at monot
  rw [hr,hr,same_block,same_block,h1,h0] at monot
  contradiction

/-- Each block contributes three row wires and all five column wires. -/
def requiredWire (k : Nat) (t : Fin (8*k)) : Nat :=
  wire (⟨t.val/8,by omega⟩ : Fin k) (2+t.val%8)

theorem requiredWire_injective (k : Nat) : Function.Injective (requiredWire k) := by
  intro a b eq
  unfold requiredWire wire at eq
  simp only [Fin.val_mk] at eq
  have h1 : a.val/8 < k := by omega
  have h2 : b.val/8 < k := by omega
  apply Fin.ext
  by_cases q : a.val/8 = b.val/8 <;> split_ifs at eq <;> omega

theorem lower (k budget : Nat) (h : RepSizeAtMost (graph k) budget) :
    8*k ≤ budget := by
  obtain ⟨c,hm,hsize,hr⟩ := h
  let S := needed (5*k+5*k) c.gates {c.output}
  let f : Fin (8*k) ↪ Nat := ⟨requiredWire k,requiredWire_injective k⟩
  have inc : Finset.univ.map f ⊆ S := by
    intro j hj
    obtain ⟨t,_,rfl⟩ := Finset.mem_map.mp hj
    have hi : 2+t.val%8 ∈ required := by
      simp only [required,Finset.mem_insert,Finset.mem_singleton]
      omega
    exact indispensable (⟨t.val/8,by omega⟩ : Fin k) ⟨2+t.val%8,by omega⟩ hi c hm hr
  have hn := Finset.card_le_card inc
  simp only [Finset.card_map,Finset.card_univ,Fintype.card_fin] at hn
  have hb := needed_card (5*k+5*k) c.gates {c.output} (fun g hg => (hm g hg).2)
  change S.card ≤ _ at hb
  simp only [Finset.card_singleton] at hb
  change c.gates.length ≤ budget at hsize
  by_contra small
  have hk : 0 < k := by omega
  have setEq : Finset.univ.map f = S := Finset.eq_of_subset_of_card_le inc (by
    simp only [Finset.card_map,Finset.card_univ,Fintype.card_fin]; omega)
  let b : Fin k := ⟨0,hk⟩
  let w := fun i => oneEach (vertex b (rows i)) (vertex b (cols i))
  have hmass := mass_run c.gates {c.output} w (5*k+5*k) (fun i => by simp [w,oneEach])
    (fun g hg => ⟨by simpa using (hm g hg).1,(hm g hg).2⟩)
    (by change S.card = _; simp only [Finset.card_singleton]; omega)
  change mass (fun i => c.gates.foldl push (w i)) {c.output} ≤ mass w S at hmass
  rw [← setEq] at hmass
  simp only [mass,Finset.sum_singleton,Finset.sum_map] at hmass
  have out : score (fun i => c.gates.foldl push (w i)) c.output = 7 := by
    change price (pack (fun i => c.eval (w i))) = 7
    have eq : (fun i => c.eval (w i)) = (fun i => target (rows i) (cols i)) := by
      funext i; exact (hr _ _).trans (same_block _ _ _)
    rw [eq]; decide +kernel
  let first : Fin 8 ↪ Fin (8*k) := ⟨fun i => ⟨i.val,by omega⟩,
    fun a b he => Fin.ext (congrArg (fun z : Fin (8*k) => z.val) he)⟩
  have zero (t : Fin (8*k)) (ht : 8 ≤ t.val) : score w (f t) = 0 := by
    have empty : ∀ i, (w i).getD (f t) false = false := by
      intro i
      rw [show w i = _ from rfl, one_read]
      change (decide (requiredWire k t = (vertex b (rows i)).val) ||
        decide (requiredWire k t = 5*k+(vertex b (cols i)).val)) = false
      unfold requiredWire wire vertex
      have hq : t.val / 8 < k := by omega
      dsimp [b]; split_ifs <;> simp only [Bool.or_eq_false_iff,decide_eq_false_iff_not] <;> constructor <;> omega
    unfold score
    simp_rw [empty]
    decide +kernel
  have restrict : ∑ t ∈ Finset.univ.map first, score w (f t) = ∑ t, score w (f t) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro t _ hnot
    apply zero
    by_contra! lt
    exact hnot (Finset.mem_map.mpr ⟨⟨t.val,lt⟩,Finset.mem_univ _,Fin.ext rfl⟩)
  have values (i : Fin 8) : score w (f (first i)) = score tests (2+i.val) := by
    have id : f (first i) = wire b (2+i.val) := by
      change wire (⟨i.val/8, _⟩ : Fin k) (2+i.val%8) = wire b (2+i.val)
      congr 1
      · exact Fin.ext (Nat.div_eq_of_lt i.isLt)
      · rw [Nat.mod_eq_of_lt i.isLt]
    rw [id]
    unfold score
    congr 2
    funext j
    exact wire_read b _ _ _ (by omega)
  rw [out,← restrict,Finset.sum_map] at hmass
  simp_rw [values] at hmass
  have six : (∑ i : Fin 8, score tests (2+i.val)) = 6 := by decide +kernel
  omega

/-- A two-block witness, independently evaluated on all 100 promise inputs. -/
def twoCircuit : Circuit :=
  ⟨[⟨.or, [11, 12]⟩,
    ⟨.or, [20, 13]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.and, [21, 22]⟩,
    ⟨.and, [4, 14]⟩,
    ⟨.or, [23, 24]⟩,
    ⟨.and, [2, 10]⟩,
    ⟨.or, [25, 26]⟩,
    ⟨.or, [16, 17]⟩,
    ⟨.or, [28, 18]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.and, [29, 30]⟩,
    ⟨.and, [9, 19]⟩,
    ⟨.or, [31, 32]⟩,
    ⟨.and, [7, 15]⟩,
    ⟨.or, [33, 34]⟩,
    ⟨.or, [27, 35]⟩], 36⟩

theorem upper_two : RepSizeAtMost (graph 2) 17 := by
  refine ⟨twoCircuit,?_,by decide,by decide +kernel⟩
  intro g hg
  simp only [twoCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

#print axioms upper_two

#print axioms lower
end Alexrollo64.DisjointCopies
