import TreeCopies

namespace Alexrollo64.EdgeEdits

open PEqualNP.Represents Alexrollo64.TreeCopies Alexrollo64.DisjointCopies

abbrev Cell := Fin 10 × Fin 10
def test (t : Tree) (p : Cell) := eval (fun i => (oneEach p.1 p.2).getD i false) t
def truth (p : Cell) := graph 2 p.1 p.2

def single (p : Cell) : Tree := .node true (.leaf p.1.val) (.leaf (10+p.2.val))
theorem single_eval (p q : Cell) : test (single p) q = decide (p = q) := by
  simp only [test,single,eval,op,ite_true,Alexrollo64.PaddedRows.one_read]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,Prod.ext_iff,Fin.ext_iff]
  have := p.1.isLt
  have := p.2.isLt
  have := q.1.isLt
  have := q.2.isLt
  constructor <;> intro h <;> grind

def patch (t : Tree) : List Cell → Tree
  | [] => t
  | p :: rest => .node false (single p) (patch t rest)

theorem patch_cost (t : Tree) (ps : List Cell) : cost (patch t ps) = cost t + 2*ps.length := by
  induction ps with
  | nil => simp [patch]
  | cons p l ih => simp [patch,cost,single,ih]; omega

theorem patch_eval (t : Tree) (ps : List Cell) (q : Cell) :
    test (patch t ps) q = (decide (q ∈ ps) || test t q) := by
  induction ps with
  | nil => simp [patch]
  | cons p l ih =>
    change (test (single p) q || test (patch t l) q) = _
    rw [single_eval,ih]
    simp [List.mem_cons,eq_comm,Bool.or_assoc]

def reduced (ps : List Cell) (q : Cell) := truth q && !decide (q ∈ ps)

/-- Adding back one deleted edge costs at most one AND and one OR. -/
theorem deletion_lower (ps : List Cell) (edges : ∀ q ∈ ps, truth q = true)
    (t : Tree) (good : ∀ q, test t q = reduced ps q) : 17 ≤ cost t + 2*ps.length := by
  have correct : realizes 2 (patch t ps) := by
    intro u v
    change test (patch t ps) (u,v) = truth (u,v)
    rw [patch_eval,good]
    by_cases h : (u,v) ∈ ps
    · simp [reduced,h,edges _ h]
    · simp [reduced,h]
  have h := formula_lower _ correct
  rw [patch_cost] at h
  omega

def special : List Cell := [(2,0),(4,4),(7,5),(9,9)]
def chosen (m : Fin 16) := ((List.range 4).filter (fun i => m.val.testBit i)).map
  (fun i => special.getD i (0,0))

def row (b i : Nat) : Tree := .leaf (5*b+i)
def col (b i : Nat) : Tree := .leaf (10+5*b+i)
def rect (b : Nat) : Tree := .node true (.node false (row b 3) (row b 4))
  (.node false (.node false (col b 1) (col b 2)) (col b 3))

def witness (m : Fin 16) : Tree :=
  patch (.node false (rect 0) (rect 1)) (special.filter (fun p => !(chosen m).contains p))

set_option maxRecDepth 8192 in
theorem data_ok : ∀ m : Fin 16,
    (∀ p ∈ chosen m, truth p = true) ∧
    cost (witness m) + 2*(chosen m).length = 17 ∧
    ∀ p : Cell, test (witness m) p = reduced (chosen m) p := by
  intro m
  fin_cases m <;> constructor <;> decide +kernel

theorem optimum (m : Fin 16) :
    (∃ t, (∀ q, test t q = reduced (chosen m) q) ∧ cost t + 2*(chosen m).length = 17) ∧
    ∀ t, (∀ q, test t q = reduced (chosen m) q) → 17 ≤ cost t + 2*(chosen m).length := by
  obtain ⟨edges,sz,good⟩ := data_ok m
  exact ⟨⟨witness m,good,sz⟩,deletion_lower _ edges⟩

/-- A rectangle extended by one column adds only the missing corner of that rectangle. -/
def extra (b : Nat) : Tree := .node false
  (.node true (row b 2) (col b 0))
  (.node true (.node false (row b 3) (row b 4))
    (.node false (.node false (col b 1) (col b 2)) (.node false (col b 3) (col b 4))))

def crucial : Fin 6 → Cell := ![(2,0),(4,4),(7,5),(9,9),(3,4),(8,9)]
def near (i : Fin 6) : Tree := if i.val < 4 then witness ⟨2^i.val % 16,by omega⟩
  else if i.val = 4 then .node false (extra 0) (block 2 1)
  else .node false (block 2 0) (extra 1)

set_option maxRecDepth 8192 in
theorem near_spec : ∀ i : Fin 6, cost (near i) ≤ 16 ∧
    ∀ p : Cell, test (near i) p = Bool.xor (truth p) (decide (p = crucial i)) := by
  decide +kernel

theorem required_tests (s : Finset Cell)
    (sound : ∀ t : Tree, cost t ≤ 16 → (∀ p ∈ s, test t p = truth p) → ∀ p, test t p = truth p) :
    ∀ i, crucial i ∈ s := by
  intro i
  by_contra missing
  obtain ⟨size,eq⟩ := near_spec i
  have h := sound _ size (fun p hp => by
    have ne : p ≠ crucial i := fun e => missing (e ▸ hp)
    simp [eq,ne]) (crucial i)
  rw [eq] at h
  cases truth (crucial i) <;> simp_all

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def exampleCircuit (i : Fin 6) : Circuit := ⟨code 20 (near i),out 20 (near i)⟩
def output (c : Circuit) (q : Cell) := c.eval (oneEach q.1 q.2)

theorem circuit_spec (i : Fin 6) : Monotone2 (exampleCircuit i) ∧ (exampleCircuit i).size ≤ 16 ∧
    ∀ p : Cell, output (exampleCircuit i) p = Bool.xor (truth p) (decide (p = crucial i)) := by
  refine ⟨legal _ _,?_,?_⟩
  · simpa [exampleCircuit,Circuit.size,length_code] using (near_spec i).1
  · intro p
    let w := oneEach p.1 p.2
    have hw : w.length = 20 := by simp [w,oneEach]
    have allRaw : ∀ j : Fin 6, (leaves (near j)).all (fun l => decide (l < 20)) = true := by
      decide +kernel
    have ok (j : Nat) (h : j ∈ leaves (near i)) : j < w.length ∧ w.getD j false = w.getD j false := by
      exact ⟨hw ▸ of_decide_eq_true (List.all_eq_true.mp (allRaw i) j h),rfl⟩
    obtain ⟨zs,_,run,result,_⟩ := run_code (near i) w _ ok
    rw [hw] at run result
    calc
      output (exampleCircuit i) p = (w ++ zs).getD (out 20 (near i)) false := by
        change ((code 20 (near i)).foldl Alexrollo64.PaddedRows.step w).getD _ false = _
        rw [run]
        rfl
      _ = _ := result.trans ((near_spec i).2 p)

theorem incomplete_dag_suite (s : Finset Cell) (i : Fin 6) (miss : crucial i ∉ s) :
    ∃ c : Circuit, Monotone2 c ∧ c.size ≤ 16 ∧ (∀ p ∈ s, output c p = truth p) ∧
      output c (crucial i) ≠ truth (crucial i) := by
  obtain ⟨legalC,sz,correct⟩ := circuit_spec i
  refine ⟨exampleCircuit i,legalC,sz,?_,?_⟩
  · intro p hp
    have ne : p ≠ crucial i := fun e => miss (e ▸ hp)
    simp [correct,ne]
  · simp [correct]

#print axioms incomplete_dag_suite
#print axioms optimum
#print axioms required_tests
end Alexrollo64.EdgeEdits
