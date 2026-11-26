import PEqualNP.Defs

namespace Alexrollo64.Cover4131
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CircuitLowerBounds
abbrev V := Fin 11
abbrev G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
  (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
-- A pentagon and two triangles, disjoint on vertices.
def cycles : Finset (V × V) := {(0,9),(0,10),(5,9),(2,5),(2,10),
  (1,4),(1,8),(4,8),(3,6),(3,7),(6,7)}
def links : Finset (V × V) := {(4,10),(5,8),(6,10),(7,9),(8,9)}
def missing (K : Finset V) (F : Finset (V × V)) :=
  (F.filter fun e => e.1 ∉ K ∧ e.2 ∉ K).card
def erased (U : Finset (Sym2 V)) (F : Finset (V × V)) :=
  (F.filter fun e => s(e.1,e.2) ∈ U).card

-- Each Boolean threshold accounts for one extra vertex that can be removed.
def cap (a b : ℕ) : ℕ :=
  min a 3 + (if 5 ≤ a then 1 else 0) + (if 7 ≤ a ∧ 1 ≤ b then 1 else 0) +
    (if 9 ≤ a ∧ 3 ≤ b then 1 else 0) + (if 11 ≤ a ∧ 5 ≤ b then 1 else 0)

lemma cap_mono {a b c d : ℕ} (h : a ≤ c) (g : b ≤ d) : cap a b ≤ cap c d := by
  unfold cap; split_ifs <;> omega

-- All 2048 vertex subsets are included, even covers not extendible to a minimum cover.
set_option maxHeartbeats 0 in
lemma shape : ∀ K : Finset V, 7 ≤ K.card + cap (missing K cycles) (missing K links) := by
  decide +kernel

private lemma miss_le (U : Finset (Sym2 V)) (K : Finset V)
    (ok : (G.deleteEdges ↑U).IsVertexCover (K : Set V)) (F : Finset (V × V))
    (edges : ∀ e ∈ F, G.Adj e.1 e.2) : missing K F ≤ erased U F := by
  apply Finset.card_le_card
  intro e h
  obtain ⟨he,ha,hb⟩ := Finset.mem_filter.mp h
  refine Finset.mem_filter.mpr ⟨he,?_⟩
  by_contra no
  exact (ok (SimpleGraph.deleteEdges_adj.mpr ⟨edges e he,no⟩)).elim ha hb

theorem cover_loss (U : Finset (Sym2 V)) (T X : Finset V) (seven : T.card = 7)
    (sub : X ⊆ T) (ok : (G.deleteEdges ↑U).IsVertexCover ((T \ X) : Finset V)) :
    X.card ≤ cap (erased U cycles) (erased U links) := by
  have hc : ∀ e ∈ cycles, G.Adj e.1 e.2 := by decide +kernel
  have hl : ∀ e ∈ links, G.Adj e.1 e.2 := by decide +kernel
  have h := cap_mono (miss_le U _ ok _ hc) (miss_le U _ ok _ hl)
  have hs := shape (T \ X)
  have hz := Finset.card_sdiff_add_card_eq_card sub
  omega

-- A single nested sequence of deletions realizes all the threshold jumps.
def baseCover : Finset V := {4,5,6,7,8,9,10}
def removedPrefix (k : ℕ) := baseCover.filter (fun v => v.val < 4+k)
def cut (k : ℕ) : Finset (Sym2 V) :=
  ((cycles ∪ links).filter (fun e => e.1 ∉ baseCover \ removedPrefix k ∧ e.2 ∉ baseCover \ removedPrefix k)).image
    (fun e => s(e.1,e.2))

set_option maxHeartbeats 0 in
theorem sharp : ∀ a : Fin 12, ∀ b : Fin 6,
    let k := cap a.val b.val
    (removedPrefix k).card = k ∧ removedPrefix k ⊆ baseCover ∧ baseCover.card = 7 ∧
    G.IsVertexCover (baseCover : Set V) ∧
    (G.deleteEdges ↑(cut k)).IsVertexCover ((baseCover \ removedPrefix k : Finset V) : Set V) ∧
    erased (cut k) cycles ≤ a.val ∧ erased (cut k) links ≤ b.val := by
  simp only [SimpleGraph.IsVertexCover, SimpleGraph.deleteEdges_adj, Finset.mem_coe]
  decide +kernel

def adjacentCut : Finset (Sym2 V) := {s(0,9), s(0,10)}

-- The two edge counts alone do not determine the loss for an individual cut.
set_option maxHeartbeats 0 in
theorem adjacent_cut_geometry :
    erased adjacentCut cycles = 2 ∧ erased adjacentCut links = 0 ∧
    (∀ K : Finset V, (G.deleteEdges ↑adjacentCut).IsVertexCover (K : Set V) → 6 ≤ K.card) ∧
    (G.deleteEdges ↑adjacentCut).IsVertexCover (({2,4,5,6,7,8} : Finset V) : Set V) := by
  simp only [SimpleGraph.IsVertexCover, SimpleGraph.deleteEdges_adj, Finset.mem_coe]
  decide +kernel

-- At the exact threshold, the two surviving vertices also determine the missing link.
set_option maxHeartbeats 0 in
theorem tight_pair_classification : ∀ K : Finset V, K.card = 2 →
    ((missing K cycles = 7 ∧ missing K links = 1) ↔
      (K = {8, 10} ∨ K = {9, 10})) := by
  decide +kernel

theorem tight_pair_missing_links :
    links.filter (fun e => e.1 ∉ ({8, 10} : Finset V) ∧ e.2 ∉ ({8, 10} : Finset V)) =
      {(7, 9)} ∧
    links.filter (fun e => e.1 ∉ ({9, 10} : Finset V) ∧ e.2 ∉ ({9, 10} : Finset V)) =
      {(5, 8)} := by
  decide +kernel

end Alexrollo64.Cover4131
