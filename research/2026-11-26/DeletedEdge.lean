import DisjointMatching

namespace Alexrollo64.DeletedEdge
open Alexrollo64.DisjointMatching (target)

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

inductive Formula where
  | var (j : Fin 9)
  | const (v : Bool)
  | neg (t : Formula)
  | bin (isAnd : Bool) (l r : Formula)

def leaves : Formula → List (Fin 9)
  | .var j => [j]
  | .const _ => []
  | .neg t => leaves t
  | .bin _ l r => leaves l ++ leaves r

def run (i : Fin 9) : Formula → Column
  | .var j => wire i j
  | .const b => if b then 63 else 0
  | .neg t => ~~~(run i t)
  | .bin p l r => if p then run i l &&& run i r else run i l ||| run i r

theorem bound (i : Fin 9) (t : Formula) :
    cost (run i t) ≤ ((leaves t).map (fun j => cost (wire i j))).sum := by
  induction t with
  | var j => simp [run,leaves]
  | const b =>
    cases b
    · exact (by decide +kernel : cost 0 ≤ 0)
    · exact (by decide +kernel : cost 63 ≤ 0)
  | neg t ih => simpa only [run,leaves,(laws _ 0).2.2] using ih
  | bin p l r hl hr =>
    have h := laws (run i l) (run i r)
    cases p <;> simp [run,leaves] <;> omega

theorem subSum {x y : List Nat} (h : x.Sublist y) : x.sum ≤ y.sum := by
  induction h <;> simp_all <;> omega

theorem impossible (i : Fin 9) (t : Formula) (h : (leaves t).Nodup) :
    run i t ≠ wanted i := by
  intro e
  have h₁ := bound i t
  rw [e,(data_ok i).2.1] at h₁
  have sub : List.Subperm (leaves t) (List.ofFn (fun j : Fin 9 => j)) := by
    apply List.subperm_of_subset h
    intro j _; fin_cases j <;> decide
  obtain ⟨l,perm,sl⟩ := sub
  have h₂ := subSum (sl.map (fun j => cost (wire i j)))
  have ep := (perm.map (fun j => cost (wire i j))).sum_eq
  rw [← ep] at h₁
  rw [List.map_ofFn] at h₂
  have h₃ := (data_ok i).2.2
  change _ ≤ (List.ofFn (fun j => cost (wire i j))).sum at h₂
  omega
end Alexrollo64.DeletedEdge
#print axioms Alexrollo64.DeletedEdge.impossible
