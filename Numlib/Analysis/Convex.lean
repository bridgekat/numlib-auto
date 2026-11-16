/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Bifunction.Algebra
import Numlib.Analysis.Convex.Bifunction.Cofinite
import Numlib.Analysis.Convex.Caratheodory
import Numlib.Analysis.Convex.Closure
import Numlib.Analysis.Convex.Continuity
import Numlib.Analysis.Convex.Convergence
import Numlib.Analysis.Convex.Duality.Barrier
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
import Numlib.Analysis.Convex.Extremum.Adjoint
import Numlib.Analysis.Convex.Extremum.ConeDuality
import Numlib.Analysis.Convex.Extremum.Fenchel
import Numlib.Analysis.Convex.Extremum.Lagrangian
import Numlib.Analysis.Convex.Extremum.Maximum
import Numlib.Analysis.Convex.Extremum.Minimum
import Numlib.Analysis.Convex.Extremum.Moreau
import Numlib.Analysis.Convex.Extremum.MoreauGradient
import Numlib.Analysis.Convex.Extremum.Normal
import Numlib.Analysis.Convex.Extremum.Perturbation
import Numlib.Analysis.Convex.Extremum.Program
import Numlib.Analysis.Convex.Extremum.Projection
import Numlib.Analysis.Convex.Extremum.Prox
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
import Numlib.Analysis.Convex.Process.Basic
import Numlib.Analysis.Convex.Process.Duality
import Numlib.Analysis.Convex.Process.Linear
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
import Numlib.Analysis.Convex.Saddle.Subdifferential
import Numlib.Analysis.Convex.Separation
import Numlib.Analysis.Convex.Simplicial
import Numlib.Analysis.Convex.StrictConvexSpace
import Numlib.Analysis.Convex.Subdifferential.Approx
import Numlib.Analysis.Convex.Subdifferential.BoundaryDirDeriv
import Numlib.Analysis.Convex.Subdifferential.Bounded
import Numlib.Analysis.Convex.Subdifferential.Calculus
import Numlib.Analysis.Convex.Subdifferential.Cofinite
import Numlib.Analysis.Convex.Subdifferential.Convergence
import Numlib.Analysis.Convex.Subdifferential.Defs
import Numlib.Analysis.Convex.Subdifferential.Differentiability
import Numlib.Analysis.Convex.Subdifferential.EssentiallySmooth
import Numlib.Analysis.Convex.Subdifferential.Existence
import Numlib.Analysis.Convex.Subdifferential.Gradient
import Numlib.Analysis.Convex.Subdifferential.GradientLimit
import Numlib.Analysis.Convex.Subdifferential.Integral
import Numlib.Analysis.Convex.Subdifferential.Legendre
import Numlib.Analysis.Convex.Subdifferential.LegendreType
import Numlib.Analysis.Convex.Subdifferential.Monotone
import Numlib.Analysis.Convex.Subdifferential.OneDim
import Numlib.Analysis.Convex.Subdifferential.Preservation
import Numlib.Analysis.Convex.Subdifferential.Primitive
import Numlib.Analysis.Convex.Subdifferential.Rademacher
import Numlib.Analysis.Convex.Subdifferential.Reconstruction
import Numlib.Analysis.Convex.Subdifferential.StrictlyConvex
import Numlib.Analysis.Convex.Subdifferential.Uniqueness
import Numlib.Analysis.Convex.Tangent
import Numlib.Analysis.Convex.Uniform

/-!
# Convex analysis

This module imports the convex analysis of the backbone, the modules under `Numlib.Analysis.Convex`,
and adds no declaration. The library studies convex sets and extended-real-valued convex functions
$f : E \to [-\infty, +\infty]$ on a real vector space $E$: epigraphs and the functional operations,
closures and relative interiors, separation, conjugacy and polarity, recession, subgradients,
polyhedral convexity, convex programs and their duality, saddle-functions, convex bifunctions and
convex processes. The development follows [rockafellar1970convex], but each result is stated at the
weakest of four levels of generality that its proof uses, and duality is stated for an abstract dual
pair instead of $\mathbb{R}^n$ with its inner product. The surface library
`NumlibSurface.Rockafellar` instantiates the results with $\mathbb{R}^n$. The declarations are in
the namespace `ConvexAnalysis`, except in the four modules `Gateaux`, `StrictConvexSpace`, `Uniform`
and `Extremum.Projection`, which extend Mathlib's names. The natural place of the library in Mathlib
is `Mathlib.Analysis.Convex`, and no module of the library imports a numerical module of the
backbone.

The four levels of generality are a real vector space, `[AddCommGroup E] [Module ℝ E]` (convexity,
epigraphs, the functional operations, and conjugacy against a dual pair); a topological vector
space, with continuous addition and scalar multiplication (closures, lower semicontinuity,
continuity); a locally convex space, `[LocallyConvexSpace ℝ E]` (separation, and through it
biconjugation and the existence of subgradients); and a finite-dimensional real normed space,
`[NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]` (relative interiors, and every
result that uses that the relative interior of a nonempty convex set is nonempty). Some results,
such as those on proximal mappings, Moreau's decomposition and gradients, also need
`[InnerProductSpace ℝ E]`, because they are about the pairing of a space with itself. A dual pair is
a bilinear map $B : E \times F \to \mathbb{R}$, written `B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ`. In applications $F$
is the continuous dual of a locally convex space, or $E$ itself with an inner product.

## Contents

| Module | Subject |
|---|---|
| `Bifunction.Algebra` | the algebra of bifunctions |
| `Bifunction.Cofinite` | co-finite bifunctions |
| `Caratheodory` | Carathéodory's theorem and its variants |
| `Closure` | closures of convex functions |
| `Continuity` | continuity of a convex function on the relative interior of its domain |
| `Convergence` | equi-Lipschitz families and convergence of convex functions |
| `Duality.Barrier` | the barrier cone and the recession cone |
| `Duality.Conjugate` | conjugates of convex and concave functions |
| `Duality.Continuity` | the continuity constraint qualification |
| `Duality.Exact` | exact duality for sums and inverse images |
| `Duality.FiniteProduct` | convex analysis on a finite product |
| `Duality.Gauge` | gauges, polars of convex functions, and obverses |
| `Duality.GaugeLike` | monotone conjugacy on the half-line, convex functions of a gauge |
| `Duality.HomConePolar` | the conjugate read off the polar of the homogenized epigraph |
| `Duality.InnerPairing` | self-pairings of inner-product type |
| `Duality.Level` | support functions of level sets |
| `Duality.Ops` | the dual operations table |
| `Duality.Pairing` | dual pairs |
| `Duality.Polar` | polars of convex sets and convex cones |
| `Duality.PolarBounded` | boundedness of a polar |
| `Duality.Relint` | the relative-interior constraint qualification |
| `Duality.RelintSeparation` | when a subspace meets a relative interior |
| `Duality.Support` | support functions |
| `Duality.SupportRelint` | relative interior and affine hull from the support function |
| `Epigraph` | extended-real-valued convex and concave functions |
| `Eponyms` | the named theorems under their names |
| `EuclideanProd` | convexity along the concatenation of coordinates |
| `Exposed` | exposed directions and the exposed representation of a closed convex set |
| `Extremum.Adjoint` | adjoint bifunctions and dual programs |
| `Extremum.ConeDuality` | duality between a co-finite function and a closed convex cone |
| `Extremum.Fenchel` | Fenchel's duality theorem |
| `Extremum.Lagrangian` | Lagrangians of generalized convex programs |
| `Extremum.Maximum` | the maximum of a convex function |
| `Extremum.Minimum` | the minimum of a convex function |
| `Extremum.Moreau` | Moreau's decomposition |
| `Extremum.MoreauGradient` | the gradient formulas of Moreau's theorem |
| `Extremum.Normal` | normality of a dual pair of convex programs |
| `Extremum.Perturbation` | convex bifunctions and generalized convex programs |
| `Extremum.Program` | ordinary convex programs and Lagrange multipliers |
| `Extremum.Projection` | the metric projection onto a convex set as a proximal mapping |
| `Extremum.Prox` | proximal mappings and maximal monotonicity of the subdifferential |
| `Face` | faces of a convex set |
| `Gateaux` | convexity of a functional through its directional derivatives |
| `Helly` | systems of convex inequalities: theorems of the alternative |
| `HellyRefined` | the refined theorems of the alternative |
| `Homogeneous` | positively homogeneous convex functions |
| `Homogenize` | right scalar multiplication and homogenization |
| `HullDirections` | convex hulls of points and directions |
| `Indicator` | indicator functions |
| `Lattice` | the complete lattice of convex functions |
| `Line` | convexity along a line |
| `LinearInequalities` | finite systems of linear inequalities |
| `Operations.Basic` | convexity of suprema, sums, compositions and restrictions |
| `Operations.Closed` | closedness of inverse images under linear maps |
| `Operations.Epi` | the function determined by a set in $E \times \mathbb{R}$ |
| `Operations.Hull` | the convex hull of a family of functions |
| `Operations.Image` | images and inverse images of convex functions under a linear map |
| `Operations.InfConv` | infimal convolution |
| `Polyhedral.Closedness` | closedness of a sum with a polyhedral set |
| `Polyhedral.Cone` | polyhedral convex cones and the Minkowski–Weyl theorem |
| `Polyhedral.Conjugate` | conjugates of polyhedral convex functions |
| `Polyhedral.Defs` | polyhedral convex sets and the Minkowski–Weyl theorem |
| `Polyhedral.Duality` | polyhedral constraint qualifications |
| `Polyhedral.Faces` | finite generation and a finite set of faces |
| `Polyhedral.Function` | polyhedral convex functions |
| `Polyhedral.Homogeneous` | the homogeneous convex function generated by finitely many points |
| `Polyhedral.NormalForm` | the normal form of a polyhedral convex function |
| `Polyhedral.Ops` | the polyhedral calculus |
| `Polyhedral.Recession` | the recession cone of a polyhedral set |
| `Polyhedral.Separation` | proper separation from a polyhedral set |
| `Polyhedral.Simplicial` | polytopes, triangulation, and local simpliciality |
| `Process.Basic` | convex processes |
| `Process.Duality` | the two inner products of a convex process |
| `Process.Linear` | linear transformations inside the convex algebra |
| `Recession.Closedness` | closedness of linear images of convex sets and functions |
| `Recession.Cone` | recession cones and lineality spaces |
| `Recession.ConeHull` | the convex cone generated by a convex set |
| `Recession.Conjugate` | recession functions, conjugates and polar cones |
| `Recession.Function` | recession functions |
| `Recession.PiSum` | sums of finitely many convex sets |
| `RelativeInterior` | relative interiors of convex sets |
| `Representation` | internal representation of a closed convex set |
| `Saddle.Closure` | the lower and upper closures of a saddle-function |
| `Saddle.Conjugate` | the two conjugates of a saddle-function form a closure pair |
| `Saddle.Continuity` | continuity of finite saddle-functions |
| `Saddle.Correspondence` | the correspondence between saddle-functions and bifunctions |
| `Saddle.Defs` | saddle-functions and partial conjugacy |
| `Saddle.Differential` | directional derivatives and subgradients of a saddle-function |
| `Saddle.Equiv` | equivalence classes of saddle-functions |
| `Saddle.Existence` | existence of saddle-values and saddle-points |
| `Saddle.Kernel` | kernels of saddle-functions |
| `Saddle.Minimax` | minimax problems and conjugate saddle-functions |
| `Saddle.Monotone` | the subdifferential of a saddle-function as a monotone mapping |
| `Saddle.Rademacher` | differentiability almost everywhere of a saddle-function |
| `Saddle.Real` | saddle-points relative to a product set, and real-valued saddle-functions |
| `Saddle.Subdifferential` | subdifferentials of saddle-functions |
| `Separation` | separation theorems |
| `Simplicial` | simplices, locally simplicial sets, and upper semicontinuity |
| `StrictConvexSpace` | strict convexity of a normed space from a strictly convex norm power |
| `Subdifferential.Approx` | ε-subgradients |
| `Subdifferential.BoundaryDirDeriv` | essential smoothness in terms of directional derivatives |
| `Subdifferential.Bounded` | local boundedness of the subdifferential |
| `Subdifferential.Calculus` | subdifferential calculus |
| `Subdifferential.Cofinite` | co-finiteness and the growth of the gradient |
| `Subdifferential.Convergence` | convergence of directional derivatives and of subgradients |
| `Subdifferential.Defs` | subgradients, normal cones and directional derivatives |
| `Subdifferential.Differentiability` | points of differentiability of a convex function |
| `Subdifferential.EssentiallySmooth` | essential smoothness |
| `Subdifferential.Existence` | existence of subgradients |
| `Subdifferential.Gradient` | gradients and the subdifferential |
| `Subdifferential.GradientLimit` | convergence of gradients |
| `Subdifferential.Integral` | a convex function of one variable is the integral of its derivative |
| `Subdifferential.Legendre` | the Legendre transformation |
| `Subdifferential.LegendreType` | convex functions of Legendre type |
| `Subdifferential.Monotone` | monotonicity and cyclic monotonicity of the subdifferential |
| `Subdifferential.OneDim` | one-sided derivatives of a convex function on the line |
| `Subdifferential.Preservation` | preservation of essential smoothness |
| `Subdifferential.Primitive` | the convex primitive of a nondecreasing function on the line |
| `Subdifferential.Rademacher` | almost everywhere differentiability of a convex function |
| `Subdifferential.Reconstruction` | the subdifferential reconstructed from the gradient mapping |
| `Subdifferential.StrictlyConvex` | essential strict convexity |
| `Subdifferential.Uniqueness` | a unique subgradient forces differentiability |
| `Tangent` | tangent half-spaces of a convex set |
| `Uniform` | the Radon–Riesz property |

## Main results

* `ConvexAnalysis.fenchel_moreau`: the **Fenchel–Moreau theorem** $f^{**} = \operatorname{cl} f$ for
  a convex function on a locally convex space, paired compatibly with its topology.
* `ConvexAnalysis.fenchel_inequality`: **Fenchel's inequality**
  $\langle x, y \rangle \le f(x) + f^*(y)$ for a proper function $f$.
* `ConvexAnalysis.jensen`: **Jensen's inequality** for a finite convex combination.
* `ConvexAnalysis.caratheodory`: **Carathéodory's theorem**: in dimension $n$, a point of the convex
  hull of $S$ is a convex combination of $n + 1$ points of $S$.
* `ConvexAnalysis.krein_milman`: a compact convex set in a finite-dimensional space is the convex
  hull of its extreme points.
* `ConvexAnalysis.minkowski_weyl`: the **Minkowski–Weyl theorem**: a cone is polyhedral if and only
  if it is finitely generated.
* `ConvexAnalysis.moreau_decomposition`: **Moreau's decomposition** $(f \mathbin{\square} w) + (f^*
  \mathbin{\square} w) = w$ for a closed proper convex function $f$ and
  $w(z) = \tfrac12 \langle z, z \rangle$, where $\square$ is infimal convolution.
* `ConvexAnalysis.subdifferential_maximalMonotone`: in finite dimension, the subdifferential of a
  closed proper convex function is maximal monotone.
* `ConvexAnalysis.fenchel_duality`: **Fenchel's duality theorem** $\inf_x \{f(x) - g(x)\} = \sup_y
  \{g^*(y) - f^*(y)\}$ when $f$ and $-g$ add exactly.
* `ConvexAnalysis.helly_finite`: **Helly's theorem** for a finite family of convex sets in dimension
  $n$: if any $n + 1$ or fewer of the sets have a common point, then all of them do.
* `ConvexAnalysis.polyhedral_iff_finitelyGenerated`: in finite dimension, a set is polyhedral if and
  only if it is finitely generated (the Minkowski–Weyl theorem for sets).
* `ConvexAnalysis.ae_differentiableAtFn`: in finite dimension, a proper convex function is
  differentiable at almost every point of the interior of its effective domain.

## Implementation notes

* A convex function is a total function `E → EReal`. It takes the value $+\infty$ off its effective
  domain and the value $-\infty$ only when it is improper. With this convention the functional
  operations are total and the convex functions form a complete lattice, but properness is a
  hypothesis wherever $-\infty$ would spoil an identity. `ConvexAnalysis.ConvexFn f` says that
  $\operatorname{epi} f$ is convex, `ConvexAnalysis.convexDom f` is the effective domain
  $\operatorname{dom} f$, and `ConvexAnalysis.ProperConvex f` is properness.
* Concave functions have their own definitions, such as `ConvexAnalysis.ConcaveFn`, and are not
  written as $-f$ for a convex $f$, so that a statement about a concave function reads as one.
* `ri` is scoped notation for `intrinsicInterior ℝ`, the relative interior.
* The conjugate $f^*$ is `ConvexAnalysis.convexConj B f`, for an explicit pairing `B`; there is no
  ambient dual space. The classes `ConvexAnalysis.IsContinuousPairing` (each
  $x \mapsto \langle x, y \rangle$ is continuous) and `ConvexAnalysis.IsCompatiblePairing`
  (moreover, every continuous linear functional on $E$ is some $x \mapsto \langle x, y \rangle$) are
  assumed only where a result needs them.
* Three modules work with Mathlib's real-valued `ConvexOn` on a normed space instead of
  extended-real-valued functions, and they are the entry points from the numerical modules of the
  backbone. `Numlib.Analysis.Convex.Gateaux` characterizes convexity on a convex set by directional
  derivatives: the tangent functional is a global minorant if and only if the gradient is monotone
  if and only if $f$ is convex, and a constrained minimum is then a variational inequality.
  `Numlib.Analysis.Convex.StrictConvexSpace` derives `StrictConvexSpace ℝ V` from the strict
  convexity of a power of the norm, the form in which a uniqueness theorem for best approximation
  uses it. `Numlib.Analysis.Convex.Uniform` proves the Radon–Riesz property (weak convergence
  together with convergence of the norms gives norm convergence) for uniformly convex spaces, and as
  an equivalence for inner product spaces.
* Four modules connect the convex library with the rest of the backbone.
  `Numlib.Analysis.Convex.Extremum.Projection` reads the metric projection of
  `Numlib.Analysis.Normed.Module.BestApprox` as a proximal mapping, and
  `Numlib.Analysis.Convex.Saddle.Real` reads the real-valued saddle-point theory of
  [han2009theoretical] through `ConvexAnalysis.IsSaddlePointOn`. Outside this directory,
  `Numlib.Variational.Inequality.NormalCone` reads an elliptic variational inequality as a
  normal-cone and subgradient condition, and `Numlib.Variational.EnergyPairing` reads the energy
  inner product of a symmetric coercive operator as a `ConvexAnalysis.IsInnerPairing`.
* The modules under `Numlib.Analysis.Convex.Extremum` contain the theory of an extremum problem: the
  minimum and the maximum of a convex function, ordinary and generalized convex programs, Lagrange
  multipliers, dual programs, normality and duality gaps, Fenchel duality, and the Moreau envelope.
  Iterative methods for optimization (descent methods, line searches, nonlinear conjugate gradients,
  quasi-Newton updates) are in `Numlib.Optimization`. The two meet in the modules under
  `Numlib.Optimization.Constrained`.
* Many duality formulas hold without a closure operation, and with the infimum that defines the dual
  operation attained, under a constraint qualification. `Numlib.Analysis.Convex.Duality.Exact` names
  this conclusion for sums and inverse images (`ConvexAnalysis.IsExactSum`,
  `ConvexAnalysis.IsExactImage`). `Numlib.Analysis.Convex.Duality.Relint`,
  `Numlib.Analysis.Convex.Duality.Continuity` and `Numlib.Analysis.Convex.Polyhedral.Duality` prove
  it under the relative-interior, the continuity and the polyhedral qualifications.
* The convex bifunctions are introduced in `Numlib.Analysis.Convex.Extremum.Perturbation`, as the
  family of minimization problems of a generalized convex program. A convex process
  `ConvexAnalysis.ConvexProcess` is given by its graph, a `PointedCone`, because it is a cone and
  not a function; `ConvexAnalysis.ConvexProcess.indicatorBifun` embeds it in the convex bifunctions.
* `Numlib.Analysis.Convex.Eponyms` gives the named theorems their names as aliases of descriptive
  primary names.
* The modules `Numlib.Analysis.Convex.Function` (finite sums of functions convex in the sense of
  `ConvexOn`) and `Numlib.Analysis.Convex.Segment` (segments of the plane) are in the same directory
  but are not part of this library, and this module does not import them.
-/
