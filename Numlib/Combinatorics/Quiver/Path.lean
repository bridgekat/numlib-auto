/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Combinatorics.Quiver.Path`, beside `Prefunctor.mapPath`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Combinatorics.Quiver.Path

/-!
# Prefunctors preserve the length of paths

A prefunctor $F$ between quivers maps each path $p$ to a path $F(p)$. This module shows that $F(p)$
has the same length as $p$.

## Main results

* `Prefunctor.length_mapPath`: the image of a path under a prefunctor has the same length.
-/

namespace Prefunctor

/-- Let $F \colon U \to W$ be a prefunctor between quivers, and let $p$ be a path from $a$ to $b$ in
$U$. Then the image path $F(p)$ from $F(a)$ to $F(b)$ has the same length as $p$. -/
@[simp]
theorem length_mapPath {U W : Type*} [Quiver U] [Quiver W] (F : U ⥤q W) {a b : U}
    (p : Quiver.Path a b) : (F.mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp [Prefunctor.mapPath_cons, Quiver.Path.length_cons, ih]

end Prefunctor
