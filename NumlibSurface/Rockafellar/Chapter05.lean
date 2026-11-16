/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.Rockafellar.Chapter05.Section23
import NumlibSurface.Rockafellar.Chapter05.Section24
import NumlibSurface.Rockafellar.Chapter05.Section25
import NumlibSurface.Rockafellar.Chapter05.Section26

/-!
# Rockafellar, Part V: Differential Theory

This module collects §§23–26 of [rockafellar1970convex], which the book prints as Part V:
directional derivatives and subgradients, the continuity and monotonicity of the subdifferential
mapping, the differentiability of convex functions, and the Legendre transformation. All 49 numbered
results of Part V are formalized. Theorems 24.1–24.3, which are about functions on the real line,
are stated over `ℝ` itself; the rest of the Part is stated over `Rockafellar.Rn n` with
`Rockafellar.pairing n`.

## Contents

| Source | Module | Subject |
|---|---|---|
| §23 Directional derivatives and subgradients | `Chapter05.Section23` | 16 results |
| §24 Differential continuity and monotonicity | `Chapter05.Section24` | 11 results |
| §25 Differentiability of convex functions | `Chapter05.Section25` | 11 results |
| §26 The Legendre transformation | `Chapter05.Section26` | 11 results |
-/
