import Audit.Env

/-!
# Dead declarations and unconsumed modules

A declaration is *dead* when no other project constant refers to it. That is a fact about the
compiled library, not about the source: the reference graph is read off each constant's type
and value with `getUsedConstantsAsSet`, so a use inside a proof term counts and a mention in a
doc comment does not.

Two reports, at two granularities:

* `deadDecls`: every user-written project constant with no project consumer. Some of these are
  intended API — a backbone theorem no surface has reached for yet — and some are leftovers; the
  tool cannot tell them apart and does not try. It says what nobody uses, and the reader judges.
* `unconsumedModules`: every project module that no other project module imports. A module
  here with declarations in it is a library that nothing has consumed. The tracker's plan may
  still cite it as a deliberate phase; the report is the prompt to check.

The two are related but not the same. A module can be imported for one declaration while the
rest of it is dead, and a module can be imported by nobody while its declarations are all
reached transitively through re-exports — so both are reported.
-/

open Lean

namespace Audit

/-- The project constants each project constant uses, over user-written declarations only. -/
def useGraph (env : Environment) (roots : Array Name) (decls : Array Name) :
    Std.HashMap Name (Array Name) := Id.run do
  let isDecl : Std.HashSet Name := decls.foldl (init := {}) fun s d => s.insert d
  let mut g : Std.HashMap Name (Array Name) := {}
  for c in decls do
    let used := match env.find? c with
      | some ci => ci.getUsedConstantsAsSet.toArray
      | none => #[]
    -- pass through Lean-generated helpers to the user declaration that owns them
    let mut targets : Array Name := #[]
    for u in used do
      if u == c then continue
      if isDecl.contains u then targets := targets.push u
      else if let some m := moduleOf env u then
        if isProjectModule roots m then
          -- an auxiliary of some user declaration: attribute to its longest user-decl prefix
          let mut p := u.getPrefix
          while !p.isAnonymous do
            if isDecl.contains p then targets := targets.push p; break
            p := p.getPrefix
    g := g.insert c targets
  return g

/-- Reverse the use graph: who uses each declaration. -/
def consumers (g : Std.HashMap Name (Array Name)) : Std.HashMap Name (Array Name) :=
  g.fold (init := {}) fun acc c used =>
    used.foldl (init := acc) fun acc u => acc.alter u fun
      | some cs => some (cs.push c)
      | none => some #[c]

/-- Declarations with no consumer among the project's user-written declarations. -/
def deadDecls (env : Environment) (roots : Array Name) : Array (Name × Name) := Id.run do
  let decls := projectDecls env roots
  let g := useGraph env roots decls
  let cons := consumers g
  let mut out := #[]
  for c in decls do
    -- instances are consumed by typeclass resolution, invisible to the use graph; skip them
    if Meta.isInstanceCore env c then continue
    let cs := cons.getD c #[]
    -- a consumer from *another* declaration only; self-recursion does not count
    if cs.all (· == c) then
      if let some m := moduleOf env c then out := out.push (m, c)
  return out.qsort fun a b => a.1.toString < b.1.toString || (a.1 == b.1 && a.2.toString < b.2.toString)

/-- Project modules, and the project modules each one imports. -/
def moduleImports (env : Environment) (roots : Array Name) : Std.HashMap Name (Array Name) := Id.run do
  let mut g : Std.HashMap Name (Array Name) := {}
  for i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    unless isProjectModule roots m do continue
    let imps := (env.header.moduleData[i]!).imports.map (·.module)
      |>.filter (isProjectModule roots ·)
    g := g.insert m imps
  return g

/--
Project modules that no other project module imports, each with how many user declarations it
holds. The root modules (`Numlib.lean`, `NumlibSurface.lean`) re-export the whole library, so an
import from a root does not count as consumption, and the roots themselves are not listed.
-/
def unconsumedModules (env : Environment) (roots : Array Name) : Array (Name × Nat) := Id.run do
  let imps := moduleImports env roots
  -- the root modules re-export everything, so an import *from* a root is not a consumer
  let mut imported : Std.HashSet Name := {}
  for (m, is) in imps do
    if roots.contains m then continue
    for i in is do imported := imported.insert i
  let decls := projectDecls env roots
  let mut count : Std.HashMap Name Nat := {}
  for c in decls do
    if let some m := moduleOf env c then count := count.alter m fun n => some ((n.getD 0) + 1)
  let mut out := #[]
  for (m, _) in imps do
    if roots.contains m then continue
    if imported.contains m then continue
    out := out.push (m, count.getD m 0)
  return out.qsort (·.1.toString < ·.1.toString)

/-!
### Reach from a consumer library

The README's criterion for the backbone is that it is *driven by demands from the surface*. So
the sharper question than "who uses this" is "does any surface reach this, transitively". A
backbone declaration that no surface reaches, even through a chain of backbone lemmas, is one the
surface has not asked for.
-/

/--
Project declarations under `target` that no declaration under any of `from` reaches through the
use graph, following edges transitively. Returned grouped by module. A hit is a declaration the
consuming libraries do not demand, directly or indirectly.
-/
def unreachedFrom (env : Environment) (roots : Array Name) («from» : Array Name) (target : Name) :
    Array (Name × Name) := Id.run do
  let decls := projectDecls env roots
  let g := useGraph env roots decls
  -- BFS from every declaration of the consuming libraries
  let mut reached : Std.HashSet Name := {}
  let inFrom (d : Name) : Bool := match moduleOf env d with
    | some m => «from».any (·.isPrefixOf m)
    | none => false
  let mut queue : Array Name := decls.filter inFrom
  for d in queue do reached := reached.insert d
  while h : queue.size > 0 do
    let c := queue[queue.size - 1]
    queue := queue.pop
    for u in g.getD c #[] do
      unless reached.contains u do
        reached := reached.insert u
        queue := queue.push u
  let mut out := #[]
  for c in decls do
    -- a declaration's namespace need not match its module (`FloatingPoint.foo` lives in
    -- `Numlib.FloatingPoint`), so both the target and the start set select by *module*
    let some m := moduleOf env c | continue
    unless target.isPrefixOf m do continue
    if Meta.isInstanceCore env c then continue
    if reached.contains c then continue
    out := out.push (m, c)
  return out.qsort fun a b => a.1.toString < b.1.toString || (a.1 == b.1 && a.2.toString < b.2.toString)

end Audit
