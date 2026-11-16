/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Caratheodory
import Numlib.Analysis.Convex.Face
import Numlib.Analysis.Convex.Homogenize
import Numlib.Analysis.Convex.Extremum.Prox
import Numlib.Analysis.Convex.Polyhedral.Cone
import Numlib.Analysis.Convex.Subdifferential.Gradient

/-!
# Eponyms

This module gives the named theorems of convex analysis under the names that readers search for,
following [rockafellar1970convex]. Every declaration here is an `alias`. The primary names of the
library are descriptive, such as `ConvexAnalysis.convexBiconj_eq_convexCl` and
`ConvexAnalysis.convexHull_extremePoints`, which suits a library organized by subject but is not
what a reader looks up first. Where the eponym is already the primary name, as for
`ConvexAnalysis.fenchel_duality`, `ConvexAnalysis.farkas` and `ConvexAnalysis.helly_finite`, no
alias appears.

## Implementation notes

* `ConvexAnalysis.perspective` is an alias of a definition, not of a theorem:
  `ConvexAnalysis.smulRight f a` is the right scalar multiple $fa$ of [rockafellar1970convex], the
  perspective function under its other name.
-/

namespace ConvexAnalysis

/-- The **Fenchel–Moreau theorem**. Let $E$ be a locally convex real topological vector space,
paired with $F$ compatibly with its topology. For every convex function
$f : E \to [-\infty, +\infty]$, the biconjugate is the closure:
$$f^{**} = \operatorname{cl} f.$$
This is an alias of `ConvexAnalysis.convexBiconj_eq_convexCl`. -/
alias fenchel_moreau := convexBiconj_eq_convexCl

/-- **Fenchel's inequality.** Let $f : E \to [-\infty, +\infty]$ be a proper function. Then for
every $x \in E$ and $y \in F$,
$$\langle x, y \rangle \le f(x) + f^*(y).$$
This is an alias of `ConvexAnalysis.ProperConvex.le_add_convexConj`. -/
alias fenchel_inequality := ProperConvex.le_add_convexConj

/-- **Jensen's inequality** for a finite convex combination. Let $f : E \to [-\infty, +\infty]$ be
convex, let $u_j \in E$ and $m_j \in \mathbb{R}$ with $f(u_j) \le m_j$ for $j \in t$, and let
$w_j \ge 0$ with $\sum_{j \in t} w_j = 1$. Then
$$f\Bigl(\sum_{j \in t} w_j u_j\Bigr) \le \sum_{j \in t} w_j m_j.$$
This is an alias of `ConvexAnalysis.ConvexFn.sum_le`. -/
alias jensen := ConvexFn.sum_le

/-- **Carathéodory's theorem.** Let $E$ be a finite-dimensional real normed space of dimension $n$,
and let $S \subseteq E$. A point $x$ lies in $\operatorname{conv} S$ if and only if it is a
convex combination $x = \sum_{i=0}^{n} w_i z_i$ of $n + 1$ points $z_i \in S$, with weights
$w_i \ge 0$ and $\sum_i w_i = 1$. Repetitions and zero weights are allowed, so this is the
statement "at most $n + 1$ points".

This is an alias of `ConvexAnalysis.mem_convexHull_iff_exists_fin_finrank_succ`. -/
alias caratheodory := mem_convexHull_iff_exists_fin_finrank_succ

/-- **Minkowski's theorem**, the finite-dimensional form of the **Krein–Milman theorem**. Let $E$ be
a finite-dimensional real normed space, and let $C \subseteq E$ be compact and convex. Then $C$
is the convex hull of its extreme points.

This is an alias of `ConvexAnalysis.convexHull_extremePoints`. Unlike Mathlib's Krein–Milman
theorem `closure_convexHull_extremePoints`, no closure is taken. -/
alias krein_milman := convexHull_extremePoints

/-- The **Minkowski–Weyl theorem** for cones. In a finite-dimensional real normed space, a set $K$
is a polyhedral convex cone, cut out by finitely many homogeneous linear inequalities, if and
only if it is a finitely generated cone.

This is an alias of `ConvexAnalysis.polyhedralCone_iff_finitelyGeneratedCone`. -/
alias minkowski_weyl := polyhedralCone_iff_finitelyGeneratedCone

/-- **Moreau's decomposition.** Let $E$ be a real normed space, and let $B$ be a symmetric positive
definite pairing of $E$ with itself whose quadratic form is continuous and which is compatible
with the topology of $E$. Let $w(z) = \tfrac12 B(z, z)$, and let $f$ be a closed proper convex
function on $E$. Then for every $z \in E$,
$$(f \mathbin{\square} w)(z) + (f^* \mathbin{\square} w)(z) = w(z).$$
This is an alias of `ConvexAnalysis.moreau_add`. -/
alias moreau_decomposition := moreau_add

/-- **Maximal monotonicity of the subdifferential.** Let $E$ be a finite-dimensional real normed
space, and let $B$ be a symmetric positive definite pairing of $E$ with itself whose quadratic
form is continuous and which is compatible with the topology of $E$. If $f$ is a closed proper
convex function on $E$, then the graph of its subdifferential $\partial f$ is a maximal monotone
relation.

This is an alias of `ConvexAnalysis.isMaximalMonotoneRel_subgradientRel`. -/
alias subdifferential_maximalMonotone := isMaximalMonotoneRel_subgradientRel

/-- The **perspective** $fa$ of a function $f : E \to [-\infty, +\infty]$ and a scalar $a$: the
function $(fa)(x) = \inf \{\mu \in \mathbb{R} \mid (x, \mu) \in a \cdot \operatorname{epi} f\}$,
whose epigraph is $a \cdot \operatorname{epi} f$ when $a > 0$. For $a > 0$ it is
$(fa)(x) = a f(a^{-1} x)$.

It is defined through the epigraph so that the case $a = 0$ and the improper cases come out
right: at $a = 0$, for $f$ not identically $+\infty$, it gives the value
$f0 = \delta(\cdot \mid 0)$ of [rockafellar1970convex]. This is an alias of
`ConvexAnalysis.smulRight`, the right scalar multiple $fa$ of [rockafellar1970convex]. -/
alias perspective := smulRight

end ConvexAnalysis
