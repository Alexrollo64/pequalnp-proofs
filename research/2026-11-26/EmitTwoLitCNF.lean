import FiveGateCNF

open Std.Sat Alexrollo64.TwoLitTables Alexrollo64.FiveGateCNF

/-- Same variable allocation and gate blocks for each recorded six-input instance. -/
def instanceFormula (budget target : Nat) : CNF Nat :=
  let clauses :=
    (List.range 6).flatMap (fun k => (List.range 21).map (fun r =>
      unit (wireId k r) ((columnMasks.getD k 0).testBit r))) ++
    (List.range budget).flatMap Alexrollo64.FiveGateCNF.gateClauses ++
    (List.range 21).map (fun r => unit (zId (budget-1) r) (target.testBit r))
  ⟨clauses.toArray.map (fun c =>
    CNF.Clause.ofLiterals (c.map (fun i => (i.natAbs-1,decide (i>0)))))⟩

example : instanceFormula 5 1351679 = formula := rfl

def main (args : List String) : IO Unit := do
  let [b,t,path] := args | throw (IO.userError "expected budget target output.cnf")
  let some budget := b.toNat? | throw (IO.userError "invalid budget")
  let some target := t.toNat? | throw (IO.userError "invalid target")
  unless budget > 0 && target < 2^21 do throw (IO.userError "expected positive budget and 21-bit target")
  IO.FS.writeFile path (instanceFormula budget target).dimacs
