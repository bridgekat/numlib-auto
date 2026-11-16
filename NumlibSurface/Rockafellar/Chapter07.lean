/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.Rockafellar.Chapter07.Section33
import NumlibSurface.Rockafellar.Chapter07.Section34
import NumlibSurface.Rockafellar.Chapter07.Section35
import NumlibSurface.Rockafellar.Chapter07.Section36
import NumlibSurface.Rockafellar.Chapter07.Section37

/-!
# Rockafellar, Part VII: Saddle-Functions and Minimax Theory

This module collects §§33–37 of [rockafellar1970convex], which the book prints as Part VII:
concave-convex functions and their two partial closures, the equivalence classes of closed
saddle-functions, their continuity and differentiability, minimax problems, and the conjugacy
correspondence that gives the existence theory of saddle-values. All 58 numbered results of Part VII
are formalized. Three orientations run through the Part, and each is stated in the section that
introduces it: $\operatorname{cl}_1$ closes the first (concave) argument and $\operatorname{cl}_2$
the second (convex) argument (§33); from §36 on, minimization takes place in the convex argument and
maximization in the concave argument; and in the lower conjugate the supremum over the convex
variable is outside, while in the upper conjugate the infimum over the concave variable is outside
(§37).

## Contents

| Source | Module | Subject |
|---|---|---|
| §33 Saddle-functions | `Chapter07.Section33` | 11 results |
| §34 Closures and equivalence classes | `Chapter07.Section34` | 10 results |
| §35 Continuity and differentiability of saddle-functions | `Chapter07.Section35` | 12 results |
| §36 Minimax problems | `Chapter07.Section36` | 7 results |
| §37 Conjugate saddle-functions and minimax theorems | `Chapter07.Section37` | 18 results |
-/
