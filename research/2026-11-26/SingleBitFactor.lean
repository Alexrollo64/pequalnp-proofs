import Mathlib

namespace Alexrollo64.SingleBitFactor

variable {X A B : Type*} [Preorder A] [Preorder B]
variable (target : X → Prop) (inside : X → A) (outside : X → B)

/-- A positive and a negative sample that cannot be separated by the outside wires alone. -/
def conflict (p n : X) := target p ∧ ¬ target n ∧ outside p ≤ outside n

/-- The outside decoder receives one monotone bit about the private inputs. -/
def factors := ∃ h : A → Prop, Monotone h ∧ ∃ g : B × Prop → Prop,
  Monotone g ∧ ∀ x, g (outside x, h (inside x)) ↔ target x

theorem criterion : factors target inside outside ↔
    ∀ p n q m, conflict target outside p n → conflict target outside q m →
      ¬ inside p ≤ inside m := by
  classical
  constructor
  · rintro ⟨h,mh,g,mg,spec⟩
    have forced (a b : X) (hab : conflict target outside a b) :
        h (inside a) ∧ ¬ h (inside b) := by
      have impossible (le : h (inside a) → h (inside b)) : False :=
        hab.2.1 ((spec b).mp (mg (show (outside a,h (inside a)) ≤ (outside b,h (inside b))
          from ⟨hab.2.2,le⟩) ((spec a).mpr hab.1)))
      exact ⟨by by_contra ha; exact impossible (fun h' => (ha h').elim),
        fun hb => impossible (fun _ => hb)⟩
    intro p n q m hp hq le
    exact (forced q m hq).2 (mh le (forced p n hp).1)
  · intro separated
    let h (a : A) := ∃ p n, conflict target outside p n ∧ inside p ≤ a
    have mh : Monotone h := by
      rintro a b hab ⟨p,n,c,hp⟩
      exact ⟨p,n,c,hp.trans hab⟩
    let obs (x : X) := (outside x,h (inside x))
    let g (z : B × Prop) := ∃ p, target p ∧ obs p ≤ z
    refine ⟨h,mh,g,?_,?_⟩
    · rintro a b hab ⟨p,t,l⟩; exact ⟨p,t,l.trans hab⟩
    · intro x
      constructor
      · rintro ⟨p,t,l⟩
        by_contra nx
        have c : conflict target outside p x := ⟨t,nx,l.1⟩
        obtain ⟨q,m,c',sub⟩ := l.2 (show h (inside p) from ⟨p,x,c,le_rfl⟩)
        exact separated q m p x c' c sub
      · intro t; exact ⟨x,t,le_rfl⟩

#print axioms criterion
end Alexrollo64.SingleBitFactor
