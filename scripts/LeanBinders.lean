/-
Leading binders of given constants, as Lean elaborated them.

Run from a built formal checkout (scripts/extract-lean-references.py does this):
  lake env lean --run <supplementary>/scripts/LeanBinders.lean <modules.txt> <names.txt> <out.json>
Imports the listed modules, then writes {name: [[binder name, binder info, type], ...]}
for every listed constant found, one entry per binder of its type's forall
telescope, types pretty-printed (long types may contain line breaks). Section variables that Lean included in a
theorem appear first, which is how the reader pages show only those.
-/
import Lean

open Lean Meta

def binderInfoName : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strict"
  | .instImplicit => "inst"

def bindersOf (n : Name) : MetaM (Option Json) := do
  let some ci := (← getEnv).find? n | return none
  forallTelescope ci.type fun xs _ => do
    let mut out := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      let t ← ppExpr d.type
      out := out.push (Json.arr #[Json.str d.userName.eraseMacroScopes.toString,
        Json.str (binderInfoName d.binderInfo), Json.str (toString t)])
    return some (Json.arr out)

def main (args : List String) : IO Unit := do
  let [modulesPath, namesPath, outPath] := args
    | throw (IO.userError "usage: LeanBinders modules.txt names.txt out.json")
  initSearchPath (← findSysroot)
  let modules := ((← IO.FS.lines modulesPath).filter (· ≠ "")).map fun m => { module := m.toName }
  let env ← importModules modules {}
  let names := ((← IO.FS.lines namesPath).filter (· ≠ "")).map String.toName
  let ctx : Core.Context := { fileName := "<binders>", fileMap := default }
  let act : MetaM (Array (String × Json)) := names.filterMapM fun n => do
    return (← bindersOf n).map (n.toString, ·)
  let (entries, _) ← (act.run' : CoreM _).toIO ctx { env }
  IO.FS.writeFile outPath (Json.mkObj entries.toList).compress
