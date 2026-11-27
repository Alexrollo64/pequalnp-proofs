import EdgeEdits
namespace Alexrollo64.TestPacking
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Alexrollo64.EdgeEdits

def c0 : Circuit := ⟨[⟨.or,[11,13]⟩, ⟨.or,[3,4]⟩, ⟨.and,[20,21]⟩, ⟨.and,[4,14]⟩, ⟨.or,[22,23]⟩, ⟨.and,[12,21]⟩, ⟨.or,[24,25]⟩, ⟨.or,[16,17]⟩, ⟨.or,[27,18]⟩, ⟨.or,[8,9]⟩, ⟨.and,[28,29]⟩, ⟨.and,[9,19]⟩, ⟨.or,[30,31]⟩, ⟨.and,[7,15]⟩, ⟨.or,[32,33]⟩, ⟨.or,[26,34]⟩],35⟩
def c1 := exampleCircuit 4
def c2 : Circuit := ⟨[⟨.or,[11,13]⟩, ⟨.or,[3,4]⟩, ⟨.and,[20,21]⟩, ⟨.and,[12,21]⟩, ⟨.or,[22,23]⟩, ⟨.and,[2,10]⟩, ⟨.or,[24,25]⟩, ⟨.or,[16,17]⟩, ⟨.or,[27,18]⟩, ⟨.or,[8,9]⟩, ⟨.and,[28,29]⟩, ⟨.and,[9,19]⟩, ⟨.or,[30,31]⟩, ⟨.and,[7,15]⟩, ⟨.or,[32,33]⟩, ⟨.or,[26,34]⟩],35⟩
def c3 : Circuit := ⟨[⟨.or,[11,13]⟩, ⟨.or,[3,4]⟩, ⟨.and,[20,21]⟩, ⟨.and,[4,14]⟩, ⟨.or,[22,23]⟩, ⟨.and,[2,10]⟩, ⟨.or,[24,25]⟩, ⟨.or,[16,17]⟩, ⟨.or,[27,18]⟩, ⟨.or,[8,9]⟩, ⟨.and,[28,29]⟩, ⟨.and,[9,19]⟩, ⟨.or,[30,31]⟩, ⟨.and,[12,21]⟩, ⟨.or,[32,33]⟩, ⟨.or,[26,34]⟩],35⟩
def c4 := exampleCircuit 5
def c5 : Circuit := ⟨[⟨.or,[11,13]⟩, ⟨.or,[3,4]⟩, ⟨.and,[20,21]⟩, ⟨.and,[4,14]⟩, ⟨.or,[22,23]⟩, ⟨.and,[2,10]⟩, ⟨.or,[24,25]⟩, ⟨.or,[16,17]⟩, ⟨.or,[27,18]⟩, ⟨.or,[8,9]⟩, ⟨.and,[28,29]⟩, ⟨.and,[12,21]⟩, ⟨.or,[30,31]⟩, ⟨.and,[7,15]⟩, ⟨.or,[32,33]⟩, ⟨.or,[26,34]⟩],35⟩
def c6 : Circuit := ⟨[⟨.or,[12,13]⟩, ⟨.or,[3,4]⟩, ⟨.and,[20,21]⟩, ⟨.and,[4,14]⟩, ⟨.or,[22,23]⟩, ⟨.and,[2,10]⟩, ⟨.or,[24,25]⟩, ⟨.or,[16,17]⟩, ⟨.or,[27,18]⟩, ⟨.or,[8,9]⟩, ⟨.and,[28,29]⟩, ⟨.and,[9,19]⟩, ⟨.or,[30,31]⟩, ⟨.and,[7,15]⟩, ⟨.or,[32,33]⟩, ⟨.or,[26,34]⟩],35⟩
def c7 : Circuit := ⟨[⟨.or,[11,13]⟩, ⟨.or,[3,4]⟩, ⟨.and,[20,21]⟩, ⟨.and,[4,14]⟩, ⟨.or,[22,23]⟩, ⟨.and,[2,10]⟩, ⟨.or,[24,25]⟩, ⟨.or,[16,17]⟩, ⟨.or,[27,18]⟩, ⟨.or,[8,9]⟩, ⟨.and,[28,29]⟩, ⟨.and,[9,19]⟩, ⟨.or,[30,31]⟩, ⟨.and,[7,15]⟩, ⟨.or,[32,33]⟩, ⟨.or,[26,34]⟩],35⟩
def c8 : Circuit := ⟨[⟨.or,[11,12]⟩, ⟨.or,[3,4]⟩, ⟨.and,[20,21]⟩, ⟨.and,[4,14]⟩, ⟨.or,[22,23]⟩, ⟨.and,[2,10]⟩, ⟨.or,[24,25]⟩, ⟨.or,[16,17]⟩, ⟨.or,[27,18]⟩, ⟨.or,[8,9]⟩, ⟨.and,[28,29]⟩, ⟨.and,[9,19]⟩, ⟨.or,[30,31]⟩, ⟨.and,[7,15]⟩, ⟨.or,[32,33]⟩, ⟨.or,[26,34]⟩],35⟩
def c9 : Circuit := ⟨[⟨.or,[11,12]⟩, ⟨.or,[20,13]⟩, ⟨.or,[3,4]⟩, ⟨.and,[21,22]⟩, ⟨.and,[4,14]⟩, ⟨.or,[23,24]⟩, ⟨.and,[2,10]⟩, ⟨.or,[25,26]⟩, ⟨.or,[17,18]⟩, ⟨.or,[8,9]⟩, ⟨.and,[28,29]⟩, ⟨.and,[9,19]⟩, ⟨.or,[30,31]⟩, ⟨.and,[7,15]⟩, ⟨.or,[32,33]⟩, ⟨.or,[27,34]⟩],35⟩
def c10 : Circuit := ⟨[⟨.or,[11,12]⟩, ⟨.or,[20,13]⟩, ⟨.or,[3,4]⟩, ⟨.and,[21,22]⟩, ⟨.and,[4,14]⟩, ⟨.or,[23,24]⟩, ⟨.and,[2,10]⟩, ⟨.or,[25,26]⟩, ⟨.or,[16,18]⟩, ⟨.or,[8,9]⟩, ⟨.and,[28,29]⟩, ⟨.and,[9,19]⟩, ⟨.or,[30,31]⟩, ⟨.and,[7,15]⟩, ⟨.or,[32,33]⟩, ⟨.or,[27,34]⟩],35⟩
def c11 : Circuit := ⟨[⟨.or,[11,12]⟩, ⟨.or,[20,13]⟩, ⟨.or,[3,4]⟩, ⟨.and,[21,22]⟩, ⟨.and,[4,14]⟩, ⟨.or,[23,24]⟩, ⟨.and,[2,10]⟩, ⟨.or,[25,26]⟩, ⟨.or,[16,17]⟩, ⟨.or,[8,9]⟩, ⟨.and,[28,29]⟩, ⟨.and,[9,19]⟩, ⟨.or,[30,31]⟩, ⟨.and,[7,15]⟩, ⟨.or,[32,33]⟩, ⟨.or,[27,34]⟩],35⟩
def c12 : Circuit := ⟨[⟨.or,[11,12]⟩, ⟨.or,[20,13]⟩, ⟨.and,[21,3]⟩, ⟨.and,[4,4]⟩, ⟨.or,[22,23]⟩, ⟨.and,[2,10]⟩, ⟨.or,[24,25]⟩, ⟨.or,[16,17]⟩, ⟨.or,[27,18]⟩, ⟨.or,[8,9]⟩, ⟨.and,[28,29]⟩, ⟨.and,[9,19]⟩, ⟨.or,[30,31]⟩, ⟨.and,[7,15]⟩, ⟨.or,[32,33]⟩, ⟨.or,[26,34]⟩],35⟩
def c13 : Circuit := ⟨[⟨.or,[11,12]⟩, ⟨.or,[20,13]⟩, ⟨.or,[3,4]⟩, ⟨.and,[4,14]⟩, ⟨.or,[9,23]⟩, ⟨.and,[2,10]⟩, ⟨.or,[24,25]⟩, ⟨.or,[16,17]⟩, ⟨.or,[27,18]⟩, ⟨.or,[8,9]⟩, ⟨.and,[28,29]⟩, ⟨.and,[21,22]⟩, ⟨.or,[30,31]⟩, ⟨.and,[7,15]⟩, ⟨.or,[32,33]⟩, ⟨.or,[26,34]⟩],35⟩
def c14 : Circuit := ⟨[⟨.or,[11,12]⟩, ⟨.or,[20,13]⟩, ⟨.or,[3,4]⟩, ⟨.and,[4,14]⟩, ⟨.or,[2,23]⟩, ⟨.and,[21,22]⟩, ⟨.or,[24,25]⟩, ⟨.or,[16,17]⟩, ⟨.or,[27,18]⟩, ⟨.or,[8,9]⟩, ⟨.and,[28,29]⟩, ⟨.and,[9,19]⟩, ⟨.or,[30,31]⟩, ⟨.and,[7,15]⟩, ⟨.or,[32,33]⟩, ⟨.or,[26,34]⟩],35⟩
def c15 : Circuit := ⟨[⟨.or,[11,12]⟩, ⟨.or,[20,13]⟩, ⟨.or,[3,4]⟩, ⟨.and,[4,14]⟩, ⟨.or,[7,23]⟩, ⟨.and,[2,10]⟩, ⟨.or,[24,25]⟩, ⟨.or,[16,17]⟩, ⟨.or,[27,18]⟩, ⟨.or,[8,9]⟩, ⟨.and,[28,29]⟩, ⟨.and,[9,19]⟩, ⟨.or,[30,31]⟩, ⟨.and,[21,22]⟩, ⟨.or,[32,33]⟩, ⟨.or,[26,34]⟩],35⟩
def circuits : Fin 16 → Circuit := ![c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15]
def masks : Fin 16 → Nat := ![1048576,17179869184,17592186044416,37778931862957161709568,618970019642690137449562112,633825300114114700748351602688,2201170739200,4402341478400,8804682956800,79305533766719673860725145600,158611067533439347721450291200,317222135066878695442900582400,1091815046381568,77990222474978957318644826112,1071644672,1169966296130954601693184]

def fails (i : Fin 16) (p : Cell) := (masks i).testBit (10*p.1.val + p.2.val)
def allowed : GateOp → Bool
  | .and | .or => true
  | _ => false
def valid (c : Circuit) := c.gates.all fun g =>
  allowed g.op && decide (g.inputs.length ≤ 2)
theorem legality (i : Fin 16) : Monotone2 (circuits i) ∧ (circuits i).size ≤ 16 := by
  have h : ∀ j, valid (circuits j) = true ∧ (circuits j).size ≤ 16 := by decide +kernel
  refine ⟨?_,(h i).2⟩
  intro g hg
  have hg' := List.all_eq_true.mp (h i).1 g hg
  obtain ⟨op,ins⟩ := g
  cases op <;> simp_all [allowed]
set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16384 in
theorem tables (i : Fin 16) (p : Cell) :
    (output (circuits i) p != truth p) = fails i p := by
  revert p
  fin_cases i <;> decide +kernel

theorem distinct : ∀ i j : Fin 16, ∀ p : Cell, fails i p → fails j p → i = j := by decide +kernel
theorem nonempty_support : ∀ i : Fin 16, ∃ p : Cell, fails i p := by decide +kernel

/-- A suite that detects every incorrect circuit within budget needs at least 16 cells. -/
theorem lower (s : Finset Cell)
    (complete : ∀ c : Circuit, Monotone2 c → c.size ≤ 16 →
      (∀ p ∈ s, output c p = truth p) → ∀ p, output c p = truth p) : 16 ≤ s.card := by
  classical
  have hit (i : Fin 16) : ∃ p : s, fails i p.val := by
    by_contra! miss
    have ok (p : Cell) (hp : p ∈ s) : output (circuits i) p = truth p := by
      have h := tables i p
      by_contra ne
      exact miss ⟨p,hp⟩ (by cases h₁ : output (circuits i) p <;> cases h₂ : truth p <;> simp_all)
    obtain ⟨q,hq⟩ := nonempty_support i
    have eq := complete _ (legality i).1 (legality i).2 ok q
    rw [← tables,eq] at hq
    simp at hq
  choose f hf using hit
  have inj : Function.Injective f := by
    intro i j eq
    exact distinct i j (f j).val (eq ▸ hf i) (hf j)
  simpa using Fintype.card_le_of_injective f inj

#print axioms lower
end Alexrollo64.TestPacking
