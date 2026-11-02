/-
Raw dependency graph of a Lean project, as Lean's environment has it.

Run from a built formal checkout (scripts/build-lean-dag.py does this):
  lake env lean --run <supplementary>/scripts/LeanDag.lean <modules.txt> <roots.txt> <out.json>
Imports the modules listed in modules.txt. A constant belongs to the project
when the root of its module name is listed in roots.txt. For every project
constant the output lists its module, its kind and the constants used by its
type and value: project constants under `uses`, constants of other packages
under `external`; `externals` gives the module, kind and
instance-or-projection flag of each of those. scripts/build-lean-dag.py
contracts this graph to the key declarations of site.json.
-/
import Lean

open Lean

def kind : ConstantInfo → String
  | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque" | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec" | .quotInfo _ => "quot"

def main (args : List String) : IO Unit := do
  let [modulesPath, rootsPath, outPath] := args
    | throw (IO.userError "usage: LeanDag modules.txt roots.txt out.json")
  initSearchPath (← findSysroot)
  let imports := ((← IO.FS.lines modulesPath).filter (· ≠ "")).map fun m => { module := m.toName }
  let projectRoots := ((← IO.FS.lines rootsPath).filter (· ≠ "")).map String.toName |>.toList
  let env ← importModules imports {}
  let modules := env.header.moduleNames
  let moduleOf (c : Name) : Option Name := (env.getModuleIdxFor? c).map (modules[·.toNat]!)
  let isProject (c : Name) : Bool := match moduleOf c with
    | some m => projectRoots.contains m.getRoot
    | none => false
  let mut out : Array (String × Json) := #[]
  let mut seen : NameSet := {}
  for (c, info) in env.constants.toList do
    unless isProject c do continue
    let mut uses : Array Json := #[]
    let mut external : Array Json := #[]
    for d in info.getUsedConstantsAsSet do
      if d == c then continue
      if isProject d then uses := uses.push (Json.str d.toString)
      else
        external := external.push (Json.str d.toString)
        seen := seen.insert d
    out := out.push (c.toString, Json.mkObj [
      ("module", Json.str ((moduleOf c).getD .anonymous).toString),
      ("kind", Json.str (kind info)), ("uses", Json.arr uses), ("external", Json.arr external)])
  -- Instances and structure projections are plumbing, not results used.
  let externals := seen.toList.filterMap fun d => (env.find? d).map fun info =>
    (d.toString, Json.arr #[Json.str ((moduleOf d).getD .anonymous).toString, Json.str (kind info),
      Json.bool (Meta.isInstanceCore env d || env.isProjectionFn d)])
  IO.FS.writeFile outPath (Json.mkObj [("constants", Json.mkObj out.toList),
    ("externals", Json.mkObj externals)]).compress
