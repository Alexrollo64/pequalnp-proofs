import Std.Sat.CNF.Dimacs
import Std.Tactic.BVDecide.LRAT.Checker
import Std.Tactic.BVDecide.LRAT.Parser

open Std.Sat Std.Tactic.BVDecide

/-- Accept only inputs that round-trip byte for byte through Lean's official DIMACS writer. -/
def parseCanonical (s : String) : Except String (CNF Nat) := do
  let mut clauses := #[]
  for line in (s.splitOn "\n").drop 1 do
    if line.isEmpty then continue
    let tokens := line.splitOn " "
    if tokens.getLast? != some "0" then throw "missing clause terminator"
    let mut clause : CNF.Clause Nat := .empty
    for token in tokens.dropLast do
      let some i := token.toInt? | throw "invalid literal"
      if i == 0 then throw "zero literal"
      clause := clause.add (i.natAbs-1) (decide (0 < i))
    clauses := clauses.push clause
  let formula : CNF Nat := ⟨clauses⟩
  if formula.dimacs != s then throw "DIMACS round-trip mismatch"
  return formula

def main (args : List String) : IO Unit := do
  let [file, cert] := args | throw (IO.userError "expected CNF and LRAT paths")
  let formula ← IO.ofExcept (parseCanonical (← IO.FS.readFile file))
  let actions ← IO.ofExcept (LRAT.parseLRATProof (← IO.FS.readBinFile cert))
  unless LRAT.check actions formula do throw (IO.userError "rejected certificate")
  IO.println s!"verified {formula.clauses.size} clauses, {actions.size} LRAT actions"
