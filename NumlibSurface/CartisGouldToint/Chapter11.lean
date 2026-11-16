/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.CartisGouldToint.Chapter11.Section01
import NumlibSurface.CartisGouldToint.Chapter11.Section02
import NumlibSurface.CartisGouldToint.Chapter11.Section03

/-!
# Cartis, Gould and Toint, Chapter 11: Variable Scaling and Other Practicalities

This module collects the formalization of Chapter 11 of [cartis2022evaluation]. The chapter has no
numbered results; the library states the displayed claims of the chapter that can be checked: the
modified absolute value and the ideal scaling of variables, the explicit solutions of the
subproblems for diagonal models, the asymptotics of the multipliers in terms of the trust-region
radius and the regularization weight, and least-squares models. The conventions are those of
Chapter 8. The module imports the section modules and adds nothing of its own.

## Contents

| Source | Module | Subject |
|---|---|---|
| §11.1 Variable scaling | `Chapter11.Section01` | (11.1.2)–(11.1.7), §§11.1.3–11.1.4 |
| §11.2 Radius and weight updates | `Chapter11.Section02` | (11.2.3)–(11.2.6) |
| §11.3 Least-squares models | `Chapter11.Section03` | (11.3.1)–(11.3.3) |
-/
