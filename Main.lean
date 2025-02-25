import Export
open Lean

def semver := "0.1.2"

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let (imports, constants) := args.span (· != "--")
  let imports := imports.toArray.map fun mod => { module := Syntax.decodeNameLit ("`" ++ mod) |>.get! }
  let env ← importModules imports {}
  let constants := match constants.tail? with
    | some cs => cs.map fun c => Syntax.decodeNameLit ("`" ++ c) |>.get!
    | none    => env.constants.toList.map Prod.fst |>.filter (!·.isInternal)
  let n ← M.run env do
    let mut n := []
    for c in constants do
      let a ← dumpConstant c
      n := List.append n a
    return n
  let stdout ← IO.getStdout
  stdout.writeJson (toJson n)
  return 0
