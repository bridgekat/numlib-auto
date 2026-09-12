import Audit

open Lean Audit

/-- Parsed command line: positionals and `--flag[=value]` options. -/
structure Args where
  positional : Array String := #[]
  flags : Std.HashMap String String := {}

def valueFlags : List String := ["roots", "under", "from"]

def parseArgs (args : List String) : Args := Id.run do
  let mut a : Args := {}
  let mut rest := args
  while true do
    match rest with
    | [] => break
    | arg :: tl =>
      rest := tl
      if arg.startsWith "--" then
        let body := String.ofList (arg.toList.drop 2)
        match body.splitOn "=" with
        | [k, v] => a := { a with flags := a.flags.insert k v }
        | _ =>
          if valueFlags.contains body then
            match rest with
            | v :: tl' => a := { a with flags := a.flags.insert body v }; rest := tl'
            | [] => a := { a with flags := a.flags.insert body "" }
          else a := { a with flags := a.flags.insert body "" }
      else a := { a with positional := a.positional.push arg }
  return a

def usage : String := "\
audit — read a Lean project's compiled library and report what a refactor should look at

usage: audit [--roots A,B] [--under PREFIX] [--no-exts] <command>

  dead         user declarations with no consumer among the project's own declarations
  modules      backbone modules no other project module imports, with their declaration counts
               (a surface's last section is always a leaf; pass --under to see them)
  dups         pairs of project theorems with the same statement
  mathlib      project theorems whose statement matches one in Mathlib or core (slow)
  unreached    backbone declarations no surface reaches, even transitively (the README's test)
  all          every report above, in that order

The reports are read off the environment: a use is a reference in a type or a proof term, and a
statement is an expression up to binder names and universe levels. None of it is parsed from
source, so a mention in a doc comment is not a use and a permuted binder is not a match.

There is deliberately no report on unused instance binders. Whether a proof needs
`[CompleteSpace V]` is decided by typeclass resolution during elaboration, and the compiled term
does not record it in any form the environment can check: two formulations were tried and both
produced false positives in bulk. Mathlib's `linter.overlappingInstances` covers the conflicting
case at build time; for the merely-unneeded case, delete the binder and let the build decide.

Each report is a list of candidates, not a verdict. A dead declaration may be intended API; a
matching statement may be a deliberate delegating restatement; an unused instance may be needed
for another binder to elaborate. The build adjudicates; this tool says where to look.

  --roots A,B     root modules to import (default: lean_lib names in lakefile.toml)
  --under PREFIX  restrict every report to declarations under this module prefix
  --from A,B      for `unreached`: the consuming libraries (default: every root ending in Surface)
  --no-exts       skip the imported modules' initializers"

def commands : List String := ["dead", "modules", "dups", "mathlib", "unreached", "all"]

/-- Root modules from the project's `lakefile.toml`: the `name` of each `[[lean_lib]]`. -/
def rootsFromLakefile : IO (Array Name) := do
  let p : System.FilePath := "lakefile.toml"
  unless ← p.pathExists do return #[]
  let txt ← IO.FS.readFile p
  let mut out := #[]
  let mut inLib := false
  for line in txt.splitOn "\n" do
    let l := line.trimAscii.toString
    if l.startsWith "[[" then inLib := l == "[[lean_lib]]"
    else if inLib && l.startsWith "name" then
      match l.splitOn "\"" with
      | _ :: n :: _ => out := out.push n.toName
      | _ => pure ()
  return out

def underFilter (under : Option String) (n : Name) : Bool :=
  match under with
  | some p => p.toName.isPrefixOf n
  | none => true

unsafe def runDead (env : Environment) (roots : Array Name) (under : Option String) : IO Unit := do
  let ds := deadDecls env roots |>.filter fun (m, _) => underFilter under m
  IO.println s!"{ds.size} declarations with no project consumer"
  let mut lastM : Name := .anonymous
  for (m, c) in ds do
    if m != lastM then IO.println s!"\n{m}"; lastM := m
    IO.println s!"  {c}"

unsafe def runModules (env : Environment) (roots : Array Name) (under : Option String) : IO Unit := do
  -- a surface library is a chain of chapter sections, so its last section is a leaf by
  -- construction and says nothing; without `--under`, report the backbone roots only
  let under := under <|> (roots.find? fun r => !r.toString.endsWith "Surface").map (·.toString)
  let ms := unconsumedModules env roots |>.filter fun (m, _) => underFilter under m
  IO.println s!"{ms.size} project modules imported by no other project module"
  for (m, n) in ms do
    IO.println s!"  {m}  ({n} declarations)"

unsafe def runDups (env : Environment) (roots : Array Name) (under : Option String) : IO Unit := do
  let gs := duplicatesWithin env roots |>.filter fun g => g.any (underFilter under ·)
  IO.println s!"{gs.size} groups of project theorems with the same statement"
  for g in gs do
    IO.println ""
    for c in g do IO.println s!"  {c}"

unsafe def runMathlib (env : Environment) (roots : Array Name) (under : Option String) : IO Unit := do
  let hs := duplicatesOfMathlib env roots |>.filter fun (c, _) => underFilter under c
  IO.println s!"{hs.size} project theorems whose statement is already in Mathlib or core"
  for (c, d) in hs do
    IO.println s!"  {c}\n    = {d}"

unsafe def runUnreached (env : Environment) (roots : Array Name) (under : Option String)
    (fromFlag : Option String) : IO Unit := do
  let «from» := match fromFlag with
    | some f => f.splitOn "," |>.filter (!·.isEmpty) |>.map String.toName |>.toArray
    | none => roots.filter fun r => r.toString.endsWith "Surface"
  let target := match under with
    | some u => u.toName
    | none => (roots.find? fun r => !r.toString.endsWith "Surface").getD .anonymous
  let ds := unreachedFrom env roots «from» target
  let mods := ds.foldl (init := ({} : Std.HashMap Name Nat)) fun m (mod, _) =>
    m.alter mod fun n => some ((n.getD 0) + 1)
  IO.println s!"{ds.size} declarations under {target} that nothing under {«from»} reaches, in {mods.size} modules"
  let mut lastM : Name := .anonymous
  for (m, c) in ds do
    if m != lastM then IO.println s!"
{m}  ({mods.getD m 0})"; lastM := m
    IO.println s!"  {c}"

unsafe def run (a : Args) : IO UInt32 := do
  let some cmd := a.positional[0]? | IO.println usage; return 2
  if cmd == "help" || a.flags.contains "help" then IO.println usage; return 0
  unless commands.contains cmd do
    IO.eprintln s!"unknown command '{cmd}'\n"; IO.println usage; return 2
  let roots ← match a.flags.get? "roots" with
    | some r => pure (r.splitOn "," |>.filter (!·.isEmpty) |>.map String.toName |>.toArray)
    | none => rootsFromLakefile
  if roots.isEmpty then
    IO.eprintln "no root modules; pass --roots A,B or add a lean_lib to lakefile.toml"; return 1
  let env ← importProject roots (!a.flags.contains "no-exts")
  let under := a.flags.get? "under"
  let sep (title : String) : IO Unit := IO.println s!"\n=== {title} ===\n"
  match cmd with
  | "dead" => runDead env roots under
  | "modules" => runModules env roots under
  | "dups" => runDups env roots under
  | "mathlib" => runMathlib env roots under
  | "unreached" => runUnreached env roots under (a.flags.get? "from")
  | "all" =>
    sep "modules"; runModules env roots under
    sep "dead"; runDead env roots under
    sep "dups"; runDups env roots under
    sep "unreached"; runUnreached env roots under (a.flags.get? "from")
    sep "mathlib"; runMathlib env roots under
  | _ => return 2
  return 0

unsafe def main (argv : List String) : IO UInt32 := do
  try run (parseArgs argv)
  catch e =>
    IO.eprintln s!"error: {e}"
    return 1
