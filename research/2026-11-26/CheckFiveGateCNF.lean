import FiveGateCNF
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected DIMACS path")
  unless Alexrollo64.FiveGateCNF.formula.dimacs == (← IO.FS.readFile path) do
    throw (IO.userError "different formula")
  IO.println "identical DIMACS"
