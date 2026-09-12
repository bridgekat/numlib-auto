import Audit.Env

/-!
# Duplicate statements

Two theorems whose types are the same up to binder names and universe parameters are the same
theorem twice. This is the case a review reads for by hand and misses: the project restating a
Mathlib lemma under a book's name with the binders reordered, or two modules proving the same
fact because their authors could not see each other's file.

The comparison is on the *type* after `instantiateLevelParams` to a canonical set of universe
names, with the expression hashed structurally. `Expr`'s hash ignores binder names and binder
info, which is exactly the equivalence wanted; it does not ignore binder *order*, so a lemma
stated with its arguments permuted is not caught — that needs unification, which is a different
and much slower tool.

Two reports:

* `duplicatesWithin`: pairs of project declarations with the same type.
* `duplicatesOfMathlib`: project declarations whose type matches a declaration outside the
  project. A `def` is never reported — two definitions with the same type are two different
  things — only theorems, where the type *is* the content.
-/

open Lean

namespace Audit

/-- The type with universe parameters renamed to `u_1, u_2, …` in order, for comparison. -/
def canonicalType (ci : ConstantInfo) : Expr :=
  let ps := ci.levelParams
  let us := (List.range ps.length).map fun i => Level.param (Name.mkSimple s!"u_{i+1}")
  ci.type.instantiateLevelParams ps us

/-- Whether a constant is a theorem, so that its type is its whole content. -/
def isTheoremLike (ci : ConstantInfo) : Bool :=
  match ci with
  | .thmInfo _ => true
  | _ => false

/--
Project theorems grouped by canonical type. Only groups of size ≥ 2 are returned; the
declarations in each group are the same statement.
-/
def duplicatesWithin (env : Environment) (roots : Array Name) : Array (Array Name) := Id.run do
  let decls := projectDecls env roots
  let mut byType : Std.HashMap Expr (Array Name) := {}
  for c in decls do
    let some ci := env.find? c | continue
    unless isTheoremLike ci do continue
    let t := canonicalType ci
    byType := byType.alter t fun
      | some cs => some (cs.push c)
      | none => some #[c]
  let mut out := #[]
  for (_, cs) in byType do
    if cs.size ≥ 2 then out := out.push (cs.qsort (·.toString < ·.toString))
  return out.qsort (·[0]!.toString < ·[0]!.toString)

/--
Project theorems whose canonical type equals that of a theorem *outside* the project — in
Mathlib or core. Each hit is `(project decl, outside decl)`. The outside index is built over
every imported theorem, which is large; it is built once and this is the slow audit.
-/
def duplicatesOfMathlib (env : Environment) (roots : Array Name) : Array (Name × Name) := Id.run do
  -- index the theorems outside the project; on collision keep the shorter name, which is
  -- likelier to be the canonical one
  let outside : Std.HashMap Expr Name := env.constants.fold (init := {}) fun acc c ci =>
    if ci.isTheorem && !c.isInternal then
      match moduleOf env c with
      | some m =>
        if !isProjectModule roots m then
          acc.alter (canonicalType ci) fun
            | some d => some (if c.toString.length < d.toString.length then c else d)
            | none => some c
        else acc
      | none => acc
    else acc
  let decls := projectDecls env roots
  let mut hits := #[]
  for c in decls do
    let some ci := env.find? c | continue
    unless isTheoremLike ci do continue
    if let some d := outside[canonicalType ci]? then hits := hits.push (c, d)
  return hits.qsort (·.1.toString < ·.1.toString)

end Audit
