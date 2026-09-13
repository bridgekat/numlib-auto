import Numlib.Analysis.Convex.Bifunction.Algebra
import Numlib.Analysis.Convex.Bifunction.Cofinite
import Numlib.Analysis.Convex.Bifunction.LinearProcess
import Numlib.Analysis.Convex.Bifunction.Process
import Numlib.Analysis.Convex.Bifunction.ProcessDuality
import Numlib.Analysis.Convex.Caratheodory
import Numlib.Analysis.Convex.Closure
import Numlib.Analysis.Convex.Concave
import Numlib.Analysis.Convex.Continuity
import Numlib.Analysis.Convex.Convergence
import Numlib.Analysis.Convex.Duality.Barrier
import Numlib.Analysis.Convex.Duality.ConcaveConj
import Numlib.Analysis.Convex.Duality.ConcaveOps
import Numlib.Analysis.Convex.Duality.Conjugate
import Numlib.Analysis.Convex.Duality.Continuity
import Numlib.Analysis.Convex.Duality.Exact
import Numlib.Analysis.Convex.Duality.FiniteProduct
import Numlib.Analysis.Convex.Duality.Gauge
import Numlib.Analysis.Convex.Duality.GaugeLike
import Numlib.Analysis.Convex.Duality.HomConePolar
import Numlib.Analysis.Convex.Duality.InnerPairing
import Numlib.Analysis.Convex.Duality.Level
import Numlib.Analysis.Convex.Duality.Ops
import Numlib.Analysis.Convex.Duality.Pairing
import Numlib.Analysis.Convex.Duality.Polar
import Numlib.Analysis.Convex.Duality.PolarBounded
import Numlib.Analysis.Convex.Duality.Relint
import Numlib.Analysis.Convex.Duality.RelintSeparation
import Numlib.Analysis.Convex.Duality.Support
import Numlib.Analysis.Convex.Duality.SupportRelint
import Numlib.Analysis.Convex.Epigraph
import Numlib.Analysis.Convex.Eponyms
import Numlib.Analysis.Convex.EuclideanProd
import Numlib.Analysis.Convex.Exposed
import Numlib.Analysis.Convex.Face
import Numlib.Analysis.Convex.Gateaux
import Numlib.Analysis.Convex.Helly
import Numlib.Analysis.Convex.HellyRefined
import Numlib.Analysis.Convex.Homogeneous
import Numlib.Analysis.Convex.Homogenize
import Numlib.Analysis.Convex.HullDirections
import Numlib.Analysis.Convex.Indicator
import Numlib.Analysis.Convex.Lattice
import Numlib.Analysis.Convex.Line
import Numlib.Analysis.Convex.LinearInequalities
import Numlib.Analysis.Convex.Operations.Basic
import Numlib.Analysis.Convex.Operations.Closed
import Numlib.Analysis.Convex.Operations.Epi
import Numlib.Analysis.Convex.Operations.Hull
import Numlib.Analysis.Convex.Operations.Image
import Numlib.Analysis.Convex.Operations.InfConv
import Numlib.Analysis.Convex.Optimization.Adjoint
import Numlib.Analysis.Convex.Optimization.ConeDuality
import Numlib.Analysis.Convex.Optimization.Fenchel
import Numlib.Analysis.Convex.Optimization.Lagrangian
import Numlib.Analysis.Convex.Optimization.Maximum
import Numlib.Analysis.Convex.Optimization.Minimum
import Numlib.Analysis.Convex.Optimization.Moreau
import Numlib.Analysis.Convex.Optimization.MoreauGradient
import Numlib.Analysis.Convex.Optimization.Normal
import Numlib.Analysis.Convex.Optimization.Perturbation
import Numlib.Analysis.Convex.Optimization.Program
import Numlib.Analysis.Convex.Optimization.Projection
import Numlib.Analysis.Convex.Optimization.Prox
import Numlib.Analysis.Convex.Polyhedral.Closedness
import Numlib.Analysis.Convex.Polyhedral.Cone
import Numlib.Analysis.Convex.Polyhedral.Conjugate
import Numlib.Analysis.Convex.Polyhedral.Defs
import Numlib.Analysis.Convex.Polyhedral.Duality
import Numlib.Analysis.Convex.Polyhedral.Faces
import Numlib.Analysis.Convex.Polyhedral.Function
import Numlib.Analysis.Convex.Polyhedral.Homogeneous
import Numlib.Analysis.Convex.Polyhedral.NormalForm
import Numlib.Analysis.Convex.Polyhedral.Ops
import Numlib.Analysis.Convex.Polyhedral.Recession
import Numlib.Analysis.Convex.Polyhedral.Separation
import Numlib.Analysis.Convex.Polyhedral.Simplicial
import Numlib.Analysis.Convex.Recession.Closedness
import Numlib.Analysis.Convex.Recession.Cone
import Numlib.Analysis.Convex.Recession.ConeHull
import Numlib.Analysis.Convex.Recession.Conjugate
import Numlib.Analysis.Convex.Recession.Function
import Numlib.Analysis.Convex.Recession.PiSum
import Numlib.Analysis.Convex.RelativeInterior
import Numlib.Analysis.Convex.Representation
import Numlib.Analysis.Convex.Saddle.Closure
import Numlib.Analysis.Convex.Saddle.Conjugate
import Numlib.Analysis.Convex.Saddle.Continuity
import Numlib.Analysis.Convex.Saddle.Correspondence
import Numlib.Analysis.Convex.Saddle.Defs
import Numlib.Analysis.Convex.Saddle.Differential
import Numlib.Analysis.Convex.Saddle.Equiv
import Numlib.Analysis.Convex.Saddle.Existence
import Numlib.Analysis.Convex.Saddle.Kernel
import Numlib.Analysis.Convex.Saddle.Minimax
import Numlib.Analysis.Convex.Saddle.Monotone
import Numlib.Analysis.Convex.Saddle.Rademacher
import Numlib.Analysis.Convex.Saddle.Real
import Numlib.Analysis.Convex.Saddle.Subgradient
import Numlib.Analysis.Convex.Separation
import Numlib.Analysis.Convex.Simplicial
import Numlib.Analysis.Convex.StrictConvexSpace
import Numlib.Analysis.Convex.Subgradient.Approx
import Numlib.Analysis.Convex.Subgradient.BoundaryDirDeriv
import Numlib.Analysis.Convex.Subgradient.Bounded
import Numlib.Analysis.Convex.Subgradient.Calculus
import Numlib.Analysis.Convex.Subgradient.Cofinite
import Numlib.Analysis.Convex.Subgradient.Convergence
import Numlib.Analysis.Convex.Subgradient.Defs
import Numlib.Analysis.Convex.Subgradient.Differentiability
import Numlib.Analysis.Convex.Subgradient.EssentiallySmooth
import Numlib.Analysis.Convex.Subgradient.Existence
import Numlib.Analysis.Convex.Subgradient.Gradient
import Numlib.Analysis.Convex.Subgradient.GradientLimit
import Numlib.Analysis.Convex.Subgradient.Integral
import Numlib.Analysis.Convex.Subgradient.Legendre
import Numlib.Analysis.Convex.Subgradient.LegendreType
import Numlib.Analysis.Convex.Subgradient.Monotone
import Numlib.Analysis.Convex.Subgradient.OneDim
import Numlib.Analysis.Convex.Subgradient.Preservation
import Numlib.Analysis.Convex.Subgradient.Primitive
import Numlib.Analysis.Convex.Subgradient.Rademacher
import Numlib.Analysis.Convex.Subgradient.Reconstruction
import Numlib.Analysis.Convex.Subgradient.StrictlyConvex
import Numlib.Analysis.Convex.Subgradient.Uniqueness
import Numlib.Analysis.Convex.Tangent
import Numlib.Analysis.Convex.Uniform

/-!
# Convex analysis

The **backbone** for convex analysis: the theory of convex sets and of extended-real-valued convex
functions over real vector spaces, named for its subject and stated at the weakest hypotheses that
carry each proof. Nothing here is tied to a particular text. `NumlibSurface.Rockafellar` is the
surface that tests it against one.

This module imports the whole of `Numlib.Analysis.Convex` and adds nothing of its own. The
general theory described below was merged from the tdaf repository; beside it the directory
keeps this project's older, independent modules of convexity facts Mathlib lacks (natural home:
`Mathlib.Analysis.Convex`) — `Gateaux`, `StrictConvexSpace` and `Uniform` — which predate the merge
and are not part of the layout below. Where the two meet, the meeting is a bridge module:
`Optimization/Projection` reads the metric projection of `Numlib/Analysis/Normed/Module/BestApprox`
as a proximal mapping, `Saddle/Real` reads the real-valued saddle-point theory of Atkinson–Han
through `IsSaddlePointOn`, and `Numlib/Variational/Inequality/NormalCone` reads the elliptic
variational inequality as a normal-cone and subgradient condition.

## Four levels of generality

Every result is stated at the weakest of these that supports it, so a reader can see from a
declaration's hypotheses what its proof actually uses.

* **A real vector space**, `[AddCommGroup E] [Module ℝ E]` — convexity, epigraphs, the functional
  operations, and conjugacy against a dual pair.
* **A topological vector space**, adding `[TopologicalSpace E]` with continuous addition and
  scalar multiplication — closures, lower semicontinuity, continuity.
* **A locally convex space**, adding `[LocallyConvexSpace ℝ E]` — separation, and through it
  biconjugation and the existence of subgradients.
* **Finite-dimensional Euclidean space**, `[NormedAddCommGroup E] [NormedSpace ℝ E]`
  `[FiniteDimensional ℝ E]` — relative interiors, and everything that rests on `ri C` being
  non-empty for non-empty convex `C`.

A handful of results — proximal mappings, Moreau's decomposition, the gradient theory — additionally
want `[InnerProductSpace ℝ E]`, because they are about a self-pairing rather than a general one.

**Duality is stated for a dual pair**, a bilinear `B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ`, rather than for a
topological dual. `F` is then whatever the application supplies: the continuous dual of a locally
convex space, or `E` itself under an inner product. `Duality.Pairing` collects the two side
conditions a pairing may satisfy — that `⟨·, y⟩` is continuous, and that every continuous linear
functional is some `⟨·, y⟩` — and results ask for them only where they are needed.

## The modules

**The basics.** `Epigraph` introduces `ConvexFn` through the convexity of `epi f`, with `dom f` and
`Proper f`; `Concave` mirrors it. `Closure` builds the closure of a convex function and
`RelativeInterior` the relative interior `ri`. `Continuity` and `Convergence` give continuity on
`ri (dom f)` and the equi-Lipschitz behaviour of convergent families. `Separation` proves the
separation theorems the duality layer runs on. `Face`, `Exposed`, `Representation` and `Tangent`
describe a closed convex set from its boundary; `Caratheodory`, `HullDirections` and `Simplicial`
from its interior. `Helly`, `HellyRefined` and `LinearInequalities` are the theorems of the
alternative. `Homogeneous`, `Homogenize`, `Indicator`, `Lattice`, `Line` and `EuclideanProd` are
the small standing pieces, and `Eponyms` collects the results that have names.

**`Operations`.** Sums, suprema, images and inverse images, infimal convolution: which preserve
convexity, and which preserve closedness.

**`Duality`.** Conjugates and biconjugates, support functions, polars of sets and of functions,
gauges and obverses, and the dual operations table that matches each functional operation with its
conjugate. `Relint`, `Continuity` and `Exact` are the constraint qualifications under which a
closure may be dropped from a duality formula.

**`Recession`.** Recession cones and recession functions, lineality and constancy spaces, and the
closedness criteria for images and sums that they govern.

**`Subgradient`.** Subgradients, normal cones and directional derivatives; gradients and where a
convex function is differentiable; monotonicity and cyclic monotonicity of `∂f`; the Legendre
transformation, essential smoothness and essential strict convexity.

**`Polyhedral`.** Polyhedra by their two descriptions and the Minkowski–Weyl theorem relating them,
the polyhedral calculus, polyhedral functions and their conjugates, and the sharper qualifications
polyhedrality allows.

**`Optimization`.** The minimum and the maximum of a convex function, ordinary and generalized
convex programs, Lagrange multipliers, adjoint bifunctions and dual programs, normality and duality
gaps, Fenchel's duality theorem, and the Moreau envelope with its proximal mapping.

**`Saddle`.** Concave-convex functions, their two partial closures and the equivalence classes
these generate, continuity and differentiability, minimax problems, and the conjugacy that carries
the existence theory of saddle-values.

**`Bifunction`.** The algebra of convex bifunctions — addition, scalar multiplication, application,
composition, and their adjoints — and convex processes, the multivalued maps whose graphs are
convex cones containing the origin.

## Named results

`Eponyms` aliases the results that carry a name, and is the quickest way in: `fenchel_moreau`
(`f** = cl f`), `fenchel_inequality`, `jensen`, `caratheodory`, `krein_milman`, `minkowski_weyl`,
`moreau_decomposition`, `subgradient_maximalMonotone`, and `perspective`. Beyond those, the
headline theorems are `fenchel_duality` in `Optimization.Fenchel`, the separation theorems in
`Separation`, `helly_finite` in `Helly`, `polyhedral_iff_finitelyGenerated` in `Polyhedral.Defs`,
and `ae_differentiableAtFn` in `Subgradient.Rademacher`.

## Conventions

* A convex function is `E → EReal`, total, taking `⊤` off its effective domain and `⊥` only when
  improper. This makes the functional operations total and the lattice complete, at the cost of
  carrying properness as a hypothesis wherever `⊥` would spoil an identity.
* `ri` is scoped notation for `intrinsicInterior ℝ`.
* `f*` is `conj B f`, against an explicit pairing `B`; there is no ambient dual.
* Concave counterparts are separate definitions rather than `-f` rewrites, so that a statement about
  concave functions reads as one.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970.
-/
