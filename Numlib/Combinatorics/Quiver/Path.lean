/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Combinatorics.Quiver.Path`, beside `Prefunctor.mapPath`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Combinatorics.Quiver.Path

/-!
# Prefunctors preserve the length of paths

`Prefunctor.length_mapPath`: the image of a path under a prefunctor has the same length.
-/

namespace Prefunctor

/-- A prefunctor preserves the length of a path. -/
@[simp]
theorem length_mapPath {U W : Type*} [Quiver U] [Quiver W] (F : U ⥤q W) {a b : U}
    (p : Quiver.Path a b) : (F.mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp [Prefunctor.mapPath_cons, Quiver.Path.length_cons, ih]

end Prefunctor
