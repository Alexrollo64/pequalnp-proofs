import EssentialCost
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Alexrollo64.GrowingMatching
open Alexrollo64.EssentialCost
open Alexrollo64.DeletedEdge (cost pack samples)

-- Each row chooses a distinct column. For equal finite sides this is a perfect matching.
def Perfect {V : Type} (g : V → V → Bool) : Prop :=
  ∃ p : V → V, Function.Injective p ∧ ∀ r, g r (p r) = true

def accepts {V : Type} {N : Nat} (enc : V × V ≃ Fin N) (x : Fin N → Bool) :=
  Perfect (fun r c => x (enc (r,c)))

theorem every_edge {V : Type} [DecidableEq V] {N : Nat} (enc : V × V ≃ Fin N)
    (j : Fin N) : Essential (accepts enc) j := by
  let a := (enc.symm j).1
  let b := (enc.symm j).2
  let p := Equiv.swap a b
  let x := fun t : Fin N => decide ((enc.symm t).2 = p (enc.symm t).1)
  let y := fun t => x t && decide (t ≠ j)
  refine ⟨x,y,⟨p,p.injective,?_⟩,?_,?_⟩
  · intro r; simp [x]
  · rintro ⟨q,_,h⟩
    have ha := h a
    simp [y,x] at ha
    have he : enc (a,b) = j := by simp [a,b]
    have eq : q a = b := by simpa [p] using ha.1
    exact ha.2 (by simpa [eq] using he)
  · intro t h; simp [y,h]

abbrev Vtx (m : Nat) := Fin 3 ⊕ Fin m

def core (s : Fin 6) (r c : Fin 3) : Bool :=
  (samples 0 s).testBit (3*r.val+c.val)

def liftGraph {m : Nat} (s : Fin 6) : Vtx m → Vtx m → Bool
  | .inl r,.inl c => core s r c
  | .inr r,.inr c => decide (r=c)
  | _,_ => false

theorem lift_perfect (m : Nat) (s : Fin 6) :
    Perfect (liftGraph (m := m) s) ↔ Perfect (core s) := by
  constructor
  · rintro ⟨p,inj,h⟩
    have inside (r : Fin 3) : ∃ c : Fin 3, p (.inl r) = .inl c := by
      cases e : p (.inl r) with
      | inl c => exact ⟨c,rfl⟩
      | inr t => have := h (.inl r); simp [e,liftGraph] at this
    choose q eq using inside
    refine ⟨q,?_,?_⟩
    · intro a b e
      have hh : p (.inl a) = p (.inl b) := by rw [eq,eq,e]
      exact Sum.inl.inj (inj hh)
    · intro a; simpa [eq,liftGraph] using h (.inl a)
  · rintro ⟨p,inj,h⟩
    refine ⟨Sum.map p id,Sum.map_injective.mpr ⟨inj,Function.injective_id⟩,?_⟩
    intro r; cases r <;> simp [liftGraph,h]

def outputBit (s : Fin 6) := Alexrollo64.DisjointMatching.target
  (fun j => (samples 0 s).testBit j.val)

theorem core_ok (s : Fin 6) : Perfect (core s) ↔ outputBit s = true := by
  unfold Perfect Function.Injective
  fin_cases s <;> decide +kernel

theorem core_cost : (∑ r : Fin 3, ∑ c : Fin 3, cost (pack (fun s => core s r c))) = 2 := by decide +kernel

theorem constants (b : Bool) : cost (pack (fun _ => b)) = 0 := by cases b <;> decide +kernel

theorem lift_cost (m : Nat) : (∑ r : Vtx m, ∑ c : Vtx m,
    cost (pack (fun s => liftGraph s r c))) = 2 := by
  simpa [Fintype.sum_sum_type,liftGraph,constants] using core_cost

theorem lower {m N : Nat} (enc : Vtx m × Vtx m ≃ Fin N) (c : Circuit) (fan : FanInTwo c)
    (correct : ∀ x, c.eval (List.ofFn x) = true ↔ accepts enc x)
    (legal : ∀ k : Fin c.gates.length, Saturation.normal (N+k.val) (c.gates.get k))
    (live : ∀ k : Fin c.gates.length, N+k.val = c.output ∨ ∃ g ∈ c.gates, N+k.val ∈ g.inputs) :
    (3+m)^2 ≤ c.size := by
  have card := Fintype.card_congr enc
  simp [Vtx,Fintype.card_sum,Fintype.card_prod] at card
  rw [pow_two,card]
  let x := fun (s : Fin 6) (j : Fin N) => liftGraph s (enc.symm j).1 (enc.symm j).2
  apply cost_lower _ (every_edge enc) c fan correct legal live x
  have outputs (s : Fin 6) : c.eval (List.ofFn (x s)) = outputBit s := by
    apply Bool.eq_iff_iff.mpr
    rw [correct,← core_ok,← lift_perfect m]
    simp [accepts,x]
  simp_rw [outputs]
  have rawCost : (∑ j : Fin N, cost (pack (fun s => x s j))) = 2 := by
    rw [← Equiv.sum_comp enc]
    simpa [x,Fintype.sum_prod_type] using lift_cost m
  rw [rawCost]
  decide +kernel
end Alexrollo64.GrowingMatching
#print axioms Alexrollo64.GrowingMatching.lower
