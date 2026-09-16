import NumlibSurface.Rockafellar.Chapter07.Section33
import NumlibSurface.Rockafellar.Chapter07.Section34
import NumlibSurface.Rockafellar.Chapter07.Section35
import NumlibSurface.Rockafellar.Chapter07.Section36
import NumlibSurface.Rockafellar.Chapter07.Section37

/-!
# Rockafellar, Part VII: Saddle-Functions and Minimax Theory

Sections 33–37: concave-convex functions and their two partial closures, the equivalence classes of
closed saddle-functions, continuity and differentiability, minimax problems, and the conjugacy
correspondence that carries the existence theory of saddle-values. This module imports the five
section modules and adds nothing of its own. All 58 numbered results of Part VII are formalized.

| § | module | subject |
|---|---|---|
| 33 | `Chapter07.Section33` | Saddle-Functions |
| 34 | `Chapter07.Section34` | Closures and Equivalence Classes |
| 35 | `Chapter07.Section35` | Continuity and Differentiability of Saddle-Functions |
| 36 | `Chapter07.Section36` | Minimax Problems |
| 37 | `Chapter07.Section37` | Conjugate Saddle-Functions and Minimax Theorems |

Three orientation conventions run through the Part and will invert statements if misread: `cl₁`
closes the concave — first — argument and `cl₂` the convex — second (§33); from §36 onward
minimisation takes place in the convex argument and maximisation in the concave; and the lower
conjugate is `sup_v inf_u` while the upper is `inf_u sup_v` (§37). Each is stated where it is
introduced.

## References

* [rockafellar1970convex] §§33–37.
-/
