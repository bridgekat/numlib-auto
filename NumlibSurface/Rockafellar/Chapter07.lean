import NumlibSurface.Rockafellar.Chapter07.Section33
import NumlibSurface.Rockafellar.Chapter07.Section34
import NumlibSurface.Rockafellar.Chapter07.Section35
import NumlibSurface.Rockafellar.Chapter07.Section36
import NumlibSurface.Rockafellar.Chapter07.Section37

/-!
# Rockafellar Part VII: saddle-functions and minimax theory

Surface file for R. Tyrrell Rockafellar, *Convex Analysis*, Princeton University Press, 1970,
§§33–37, which the book prints as Part VII: concave-convex functions and their two partial
closures, the equivalence classes of closed saddle-functions, continuity and differentiability,
minimax problems, and the conjugacy correspondence that carries the existence theory of
saddle-values.

All 58 numbered results of Part VII are formalized. This module imports the five section modules
and adds nothing of its own.

| § | module | subject |
|---|---|---|
| 33 | `Chapter07.Section33` | Saddle-functions |
| 34 | `Chapter07.Section34` | Closures and equivalence classes |
| 35 | `Chapter07.Section35` | Continuity and differentiability of saddle-functions |
| 36 | `Chapter07.Section36` | Minimax problems |
| 37 | `Chapter07.Section37` | Conjugate saddle-functions and minimax theorems |

Three orientation conventions run through the Part and will invert statements if misread: `cl₁`
closes the concave — first — argument and `cl₂` the convex — second (§33); from §36 onward
minimisation takes place in the convex argument and maximisation in the concave; and the lower
conjugate is `sup_v inf_u` while the upper is `inf_u sup_v` (§37). Each is stated where it is
introduced.
-/
