/-
Declaring module and source line of given constants, as Lean records them.

Run from a built formal checkout (scripts/extract-lean-references.py does this):
  lake env lean --run <supplementary>/scripts/LeanDeclRanges.lean <modules.txt> <names.txt> <out.json>
Imports the listed modules, then writes {name: [module, line]} for every
listed constant with a declaration range; constants without one (kernel
built-ins such as `Quot`, generated injectivity lemmas) are omitted.
-/
import Lean

open Lean

def rangeOf (n : Name) : CoreM (Option (String × Json)) := do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? n | return none
  let some ranges ← findDeclarationRanges? n | return none
  return some (n.toString, Json.arr #[Json.str (env.header.moduleNames[idx.toNat]!).toString,
    Json.num ranges.range.pos.line])

def main (args : List String) : IO Unit := do
  let [modulesPath, namesPath, outPath] := args
    | throw (IO.userError "usage: LeanDeclRanges modules.txt names.txt out.json")
  initSearchPath (← findSysroot)
  let modules := ((← IO.FS.lines modulesPath).filter (· ≠ "")).map fun m => { module := m.toName }
  let env ← importModules modules {}
  let names := ((← IO.FS.lines namesPath).filter (· ≠ "")).map String.toName
  let ctx : Core.Context := { fileName := "<ranges>", fileMap := default }
  let (entries, _) ← (names.filterMapM rangeOf : CoreM (Array (String × Json))).toIO ctx { env }
  IO.FS.writeFile outPath (Json.mkObj entries.toList).compress
