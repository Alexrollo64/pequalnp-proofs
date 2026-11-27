import PositiveCore
import ExactTwoCopies

namespace Alexrollo64.ExactThreeCopies
open PEqualNP.CircuitLowerBounds PEqualNP.Represents PEqualNP.MetaComplexity
open Alexrollo64.TreeCopies Alexrollo64.DisjointCopies Alexrollo64.CutTrees
open Alexrollo64.PositiveCore

def rowWire (b : Fin 3) (i : Fin 6) : Nat := (vertex b (row i)).val
def colWire (b : Fin 3) (i : Fin 6) : Nat := 15 + (vertex b (col i)).val

def mixed (b d : Fin 3) (i k : Fin 6) :=
  oneEach (vertex b (row i)) (vertex d (col k))

theorem mix_lit (b d : Fin 3) (i k : Fin 6) (j : Nat) :
    (mixed b d i k).getD j false = true ↔ j = rowWire b i ∨ j = colWire d k := by
  unfold mixed; rw [PaddedRows.one_read]; simp [rowWire,colWire]

theorem lit (b : Fin 3) (i : Fin 6) (j : Nat) :
    raw b i j = true ↔ j = rowWire b i ∨ j = colWire b i := mix_lit b b i i j

def combined (inner outer : Tree) (x : Nat → Bool) :=
  eval (Function.update x 54 (eval x inner)) outer

/-- A positive inner evaluation on x and an accepted cell y can be
    transported to z when z preserves the relevant true leaves. -/
theorem transfer (inner outer : Tree) (x y z : Nat → Bool)
    (on : eval x inner = true) (accepted : combined inner outer y = true)
    (priv : ∀ j ∈ leaves inner, x j = true → z j = true)
    (pub : ∀ j ∈ leaves outer, y j = true → z j = true) : combined inner outer z = true := by
  have zv := mono inner x z priv on
  apply mono _ _ _ _ accepted
  intro j hj h
  by_cases e : j = 54
  · simp [e,zv]
  · simpa [Function.update_of_ne e] using pub j hj (by simpa [Function.update_of_ne e] using h)

theorem exclusive (inner outer : Tree)
    (cover : footprint inner + footprint outer = CommonThree.requiredThree.val + {54} + {54})
    (alone : eval signalOnly outer ≠ true) (b : Fin 3) (i : Fin 6)
    (on : eval (raw b i) inner = true) (ok : combined inner outer (raw b i) = true) :
    (rowWire b i ∈ leaves inner ↔ colWire b i ∉ leaves inner) := by
  constructor
  · intro r c
    apply alone
    apply mono _ _ _ _ ok
    intro j hj h
    by_cases e : j = 54
    · simp [signalOnly,e]
    · have v : raw b i j = true := by simpa [Function.update_of_ne e] using h
      rcases (lit b i j).mp v with a|a
      · exact (apart cover e (a ▸ r) hj).elim
      · exact (apart cover e (a ▸ c) hj).elim
  · intro no
    obtain ⟨j,hj,v⟩ := leaf_hit _ _ on
    rcases (lit b i j).mp v with a|a
    · simpa [a] using hj
    · exact (no (a ▸ hj)).elim

theorem impossible (c : Circuit) (hm : Monotone2 c) (hr : Represents (graph 3) c)
    (hs : c.size ≤ 24) : False := by
  classical
  obtain ⟨inner,outer,_,cover,sem⟩ := decompose c hm hr hs
  have faithful (b : Fin 3) (i : Fin 6) := (sem (cell b i) (by simp [cell,oneEach])).trans
    ((hr (vertex b (row i)) (vertex b (col i))).trans (answers b i))
  have alone := marker_insufficient _ _ cover faithful
  choose idx pos on using core_hit inner outer cover faithful
  have ok (b : Fin 3) : combined inner outer (raw b (idx b)) = true := (faithful b _).trans (pos b)
  have ex (b : Fin 3) := exclusive inner outer cover alone b (idx b) (on b) (ok b)
  let orient (b : Fin 3) := decide (rowWire b (idx b) ∈ leaves inner)
  have collide : ∀ f : Fin 3 → Bool, ∃ b d, b ≠ d ∧ f b = f d := by decide +kernel
  obtain ⟨b,d,neq,same⟩ := collide orient
  have denied (a e : Fin 3) (ae : a ≠ e) :
      combined inner outer (fun j => (mixed a e (idx a) (idx e)).getD j false) = false := by
    have cross : ∀ (a e : Fin 3) (i k : Fin 6), a ≠ e →
        graph 3 (vertex a (row i)) (vertex e (col k)) = false := by decide +kernel
    exact (sem _ (by simp [mixed,oneEach])).trans ((hr _ _).trans (cross _ _ _ _ ae))
  have rn (a : Fin 3) : rowWire a (idx a) ≠ 54 := by unfold rowWire; omega
  have cn (a : Fin 3) : colWire a (idx a) ≠ 54 := by unfold colWire; omega
  by_cases rb : rowWire b (idx b) ∈ leaves inner
  · have rd : rowWire d (idx d) ∈ leaves inner := by simpa [orient,rb] using same
    have bad := transfer inner outer _ _ ( fun j => (mixed b d (idx b) (idx d)).getD j false) (on b) (ok d)
    have yes := bad (by
      intro j hj v; apply (mix_lit ..).mpr
      rcases (lit ..).mp v with a|a
      · exact Or.inl a
      · exact ((ex b).mp rb (a ▸ hj)).elim) (by
      intro j hj v; apply (mix_lit ..).mpr
      rcases (lit ..).mp v with a|a
      · exact (apart cover (rn d) rd (a ▸ hj)).elim
      · exact Or.inr a)
    exact Bool.noConfusion (yes.symm.trans (denied b d neq))
  · have rd : rowWire d (idx d) ∉ leaves inner := by simpa [orient,rb] using same
    have cd : colWire d (idx d) ∈ leaves inner := by by_contra no; exact rd ((ex d).mpr no)
    have bad := transfer inner outer _ _ ( fun j => (mixed d b (idx d) (idx b)).getD j false) (on b) (ok d)
    have yes := bad (by
      intro j hj v; apply (mix_lit ..).mpr
      rcases (lit ..).mp v with a|a
      · exact (rb (a ▸ hj)).elim
      · exact Or.inr a) (by
      intro j hj v; apply (mix_lit ..).mpr
      rcases (lit ..).mp v with a|a
      · exact Or.inl a
      · exact (apart cover (cn d) cd (a ▸ hj)).elim)
    exact Bool.noConfusion (yes.symm.trans (denied d b neq.symm))

theorem exact_budget (n : Nat) : RepSizeAtMost (graph 3) n ↔ 25 ≤ n := by
  constructor
  · rintro ⟨c,hm,hs,hr⟩
    by_contra! small
    exact impossible c hm hr (by omega)
  · intro h
    obtain ⟨c,hm,hs,hr⟩ := ExactTwoCopies.three_bounds.1
    exact ⟨c,hm,hs.trans h,hr⟩

#print axioms exact_budget
end Alexrollo64.ExactThreeCopies
