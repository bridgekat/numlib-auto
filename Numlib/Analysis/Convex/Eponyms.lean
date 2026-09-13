import Numlib.Analysis.Convex.Caratheodory
import Numlib.Analysis.Convex.Face
import Numlib.Analysis.Convex.Homogenize
import Numlib.Analysis.Convex.Optimization.Prox
import Numlib.Analysis.Convex.Polyhedral.Cone
import Numlib.Analysis.Convex.Subgradient.Gradient

/-!
# Eponyms

Named theorems of convex analysis, under the names people search for. Every declaration here is an
`alias`: the library's primary names are descriptive (`biconj_eq_clFn`, `convexHull_extremePoints`),
which is right for a library organised by subject but is not what a reader looks up first. Where the
eponym is already the primary name — `fenchel_duality`, `farkas`, `helly_finite` — no alias appears.

`perspective` aliases a definition rather than a theorem: `smulRight f a` is Rockafellar's `fa`, the
perspective function under its other name.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970.
-/

namespace ConvexAnalysis

/-- **Fenchel–Moreau**: a convex function's biconjugate is its closure. -/
alias fenchel_moreau := biconj_eq_clFn

/-- **Fenchel's inequality**: `⟨x, y⟩ ≤ f x + f* y`, for proper `f`. -/
alias fenchel_inequality := Proper.le_add_conj

/-- **Jensen's inequality** for a finite convex combination. -/
alias jensen := ConvexFn.sum_le

/-- **Carathéodory's theorem**: a point of `conv S` is a convex combination of at most `dim E + 1`
points of `S`. -/
alias caratheodory := mem_convexHull_iff_exists_fin_finrank_succ

/-- **Krein–Milman**, finite-dimensional form: a compact convex set is the convex hull of its
extreme points. -/
alias krein_milman := convexHull_extremePoints

/-- **Minkowski–Weyl**: a convex cone is polyhedral exactly when it is finitely generated. -/
alias minkowski_weyl := polyhedralCone_iff_finitelyGeneratedCone

/-- **Moreau's decomposition**: `(f □ q) z + (f* □ q) z = q z`, where `q z = ½ B z z`. -/
alias moreau_decomposition := moreau_add

/-- **Maximal monotonicity of the subdifferential** of a closed proper convex function. -/
alias subgradient_maximalMonotone := isMaximalMonotoneRel_subgradientRel

/-- **The perspective** of a convex function, `(f a) x = a · f (x / a)` for `a > 0`, defined through
the epigraph so that the `a = 0` and improper cases come out right. Rockafellar's `fa`. -/
alias perspective := smulRight

end ConvexAnalysis
