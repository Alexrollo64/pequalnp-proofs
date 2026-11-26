import Lean
namespace Journal18919

def circuit (x : Fin 18 → Bool) : List Bool :=
  let w18 := (x 2 && x 17)
  let w19 := (x 0 && x 11)
  let w20 := (x 1 && x 14)
  let w21 := (w18 || w19)
  let w22 := (w21 || w20)
  let w23 := (x 0 && x 9)
  let w24 := (x 1 && x 12)
  let w25 := (x 2 && x 15)
  let w26 := (w23 || w24)
  let w27 := (w26 || w25)
  let w28 := (x 6 && x 11)
  let w29 := (x 7 && x 14)
  let w30 := (x 8 && x 17)
  let w31 := (w28 || w29)
  let w32 := (w31 || w30)
  let w33 := (x 4 && x 12)
  let w34 := (x 3 && x 9)
  let w35 := (x 5 && x 15)
  let w36 := (w33 || w34)
  let w37 := (w36 || w35)
  let w38 := (x 7 && x 13)
  let w39 := (x 8 && x 16)
  let w40 := (x 6 && x 10)
  let w41 := (w38 || w39)
  let w42 := (w41 || w40)
  let w43 := !(x 8)
  let w44 := (w43 || x 15)
  let w45 := (x 5 && x 16)
  let w46 := (w36 || w45)
  let w47 := (x 2 && x 16)
  let w48 := (x 0 && x 10)
  let w49 := (x 1 && x 13)
  let w50 := (w47 || w48)
  let w51 := (w50 || w49)
  let w52 := (x 7 && x 12)
  let w53 := (w44 && x 8)
  let w54 := (x 6 && x 9)
  let w55 := (w52 || w53)
  let w56 := (w55 || w54)
  let w57 := (x 3 && x 11)
  let w58 := (x 4 && x 14)
  let w59 := (x 5 && x 17)
  let w60 := (w57 || w58)
  let w61 := (w60 || w59)
  [w27, w51, w22, w37, w46, w61, w56, w42, w32]

def target (x : Fin 18 → Bool) := (x 3 && x 10) || (x 4 && x 13) || (x 5 && x 16)
def fp (i : Fin 18) := decide (i.val = 3 ∨ i.val = 9)
def fnn (i : Fin 18) := decide (i.val = 3 ∨ i.val = 10)

theorem candidate_fp : (circuit fp)[4]? = some true ∧ target fp = false := by decide +kernel
theorem candidate_fn : (circuit fnn)[4]? = some false ∧ target fnn = true := by decide +kernel
#print axioms candidate_fp
#print axioms candidate_fn
end Journal18919
