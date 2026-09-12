import Lean

/-!
# The imported project, and the questions every audit asks of it

Import the project's root modules, then answer the two questions that all the audits share:
which module declared a constant, and whether that module belongs to the project. Everything
here is read off the environment; nothing is parsed from source.

`isUserDecl` is the filter that keeps an audit honest. Lean generates a large number of
auxiliary constants per declaration — equation lemmas, `match_` helpers, `proof_`
subterms, structure projections and instance-derived constants — and an audit that counts
them will report noise. What survives the filter is what a human wrote a name for.
-/

open Lean

namespace Audit

/-- The module a constant was declared in, if it was imported. -/
def moduleOf (env : Environment) (c : Name) : Option Name :=
  (env.getModuleIdxFor? c).bind fun i => env.allImportedModuleNames[i.toNat]?

/-- Whether a module belongs to the project, i.e. sits under one of the roots. -/
def isProjectModule (roots : Array Name) (m : Name) : Bool :=
  roots.any fun r => r.isPrefixOf m

/--
Whether a constant is one a person wrote, rather than one Lean generated on their behalf.
Rejects internal names (any component starting with `_` or a numeral), the auxiliary
declarations of `match`, `proof_`, equation lemmas and `sizeOf`, structure projections and
the constants that `deriving` and `instance` produce without a user-chosen name.
-/
def isUserDecl (env : Environment) (c : Name) : Bool := Id.run do
  if c.isInternal then return false
  let s := c.toString
  for frag in ["._", ".match_", ".proof_", ".eq_", "._eq_", ".sizeOf_spec", ".injEq", ".inj",
      ".noConfusion", ".rec", ".recOn", ".casesOn", ".brecOn", ".below", ".ibelow", ".binductionOn",
      ".mk.sizeOf_spec", ".ctorIdx", ".ofNat", ".toCtorIdx", ".congr_simp", ".congr_"] do
    if (s.splitOn frag).length > 1 then return false
  -- structure projections and instance projections carry `isProjectionFn`
  if env.isProjectionFn c then return false
  -- unnamed instances are `inst…` with a hash-like tail; named ones are user decls
  match env.find? c with
  | none => return false
  | some ci =>
    match ci with
    | .recInfo _ | .ctorInfo _ | .quotInfo _ => return false
    | .inductInfo _ => return true
    | _ => return true

/-- All constants of the project that a person wrote, sorted. -/
def projectDecls (env : Environment) (roots : Array Name) : Array Name :=
  let out := env.constants.fold (init := (#[] : Array Name)) fun acc c _ =>
    match moduleOf env c with
    | some m => if isProjectModule roots m && isUserDecl env c then acc.push c else acc
    | none => acc
  out.qsort (·.toString < ·.toString)

/-- Import the roots and hand back the environment. -/
unsafe def importProject (roots : Array Name) (loadExts : Bool) : IO Environment := do
  initSearchPath (← findSysroot)
  if loadExts then enableInitializersExecution
  let t0 ← IO.monoMsNow
  let env ← importModules (roots.map fun r => { module := r }) {} (trustLevel := 1024)
    (loadExts := loadExts)
  let t1 ← IO.monoMsNow
  IO.eprintln s!"imported {roots} in {t1 - t0} ms ({env.allImportedModuleNames.size} modules)"
  return env

end Audit
