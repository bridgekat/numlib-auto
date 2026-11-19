/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.Rockafellar.Chapter01
import NumlibSurface.Rockafellar.Chapter02
import NumlibSurface.Rockafellar.Chapter03
import NumlibSurface.Rockafellar.Chapter04
import NumlibSurface.Rockafellar.Chapter05
import NumlibSurface.Rockafellar.Chapter06
import NumlibSurface.Rockafellar.Chapter07
import NumlibSurface.Rockafellar.Chapter08

/-!
# Rockafellar, *Convex Analysis*

This library formalizes the numbered results of R. T. Rockafellar, *Convex Analysis*
[rockafellar1970convex] (Princeton University Press, 1970). The book develops the theory of convex
sets and convex functions in $\mathbb{R}^n$ in thirty-nine sections, grouped into eight Parts:
affine and convex sets and convex functions with values in $[-\infty, +\infty]$, relative interiors,
closures and recession cones, the duality of conjugate functions, support functions and polars,
Carathéodory's and Helly's theorems and polyhedral convexity, directional derivatives and
subgradients, convex programs and Fenchel duality, saddle-functions and minimax theorems, and the
algebra of bifunctions and convex processes. All eight Parts are formalized, with one module for
each section. The proofs specialize the backbone `Numlib.Analysis.Convex`, which states the duality
theory for an abstract dual pair of real vector spaces; this library instantiates it with
$\mathbb{R}^n$ and its inner product, and gives a Lean name to every formalized result of the book.

## Coverage

466 of the 471 numbered results of the book are formalized. By Part, the formalized results are:
Part I 49, Part II 84, Part III 77, Part IV 65 of 70, Part V 49, Part VI 63, Part VII 58, Part
VIII 21. The five results that are not formalized are in §22. Some formalized results are formalized
only in part, or under a stronger hypothesis than the book gives; the section `Not formalized` lists
them. Several modules also state unnumbered definitions, examples and remarks of the text.

## Contents

| Source | Module | Subject |
|---|---|---|
| not a section of the book | `Common.Euclidean` | the space $\mathbb{R}^n$ and its inner product |
| §1 Affine sets | `Chapter01.Section01` | 8 results |
| §2 Convex sets and cones | `Chapter01.Section02` | 13 results |
| §3 The algebra of convex sets | `Chapter01.Section03` | 9 results |
| §4 Convex functions | `Chapter01.Section04` | 11 results |
| §5 Functional operations | `Chapter01.Section05` | 8 results |
| §6 Relative interiors of convex sets | `Chapter02.Section06` | 18 results |
| §7 Closures of convex functions | `Chapter02.Section07` | 17 results |
| §8 Recession cones and unboundedness | `Chapter02.Section08` | 18 results |
| §9 Some closedness criteria | `Chapter02.Section09` | 18 results |
| §10 Continuity of convex functions | `Chapter02.Section10` | 13 results |
| §11 Separation theorems | `Chapter03.Section11` | 16 results |
| §12 Conjugates of convex functions | `Chapter03.Section12` | 9 results |
| §13 Support functions | `Chapter03.Section13` | 15 results |
| §14 Polars of convex sets | `Chapter03.Section14` | 11 results |
| §15 Polars of convex functions | `Chapter03.Section15` | 11 results |
| §16 Dual operations | `Chapter03.Section16` | 15 results |
| §17 Carathéodory's theorem | `Chapter04.Section17` | 10 results |
| §18 Extreme points and faces of convex sets | `Chapter04.Section18` | 16 results |
| §19 Polyhedral convex sets and functions | `Chapter04.Section19` | 17 results |
| §20 Some applications of polyhedral convexity | `Chapter04.Section20` | 8 results |
| §21 Helly's theorem and systems of inequalities | `Chapter04.Section21` | 10 results |
| §22 Linear inequalities | `Chapter04.Section22` | 4 of 9 results |
| §23 Directional derivatives and subgradients | `Chapter05.Section23` | 16 results |
| §24 Differential continuity and monotonicity | `Chapter05.Section24` | 11 results |
| §25 Differentiability of convex functions | `Chapter05.Section25` | 11 results |
| §26 The Legendre transformation | `Chapter05.Section26` | 11 results |
| §27 The minimum of a convex function | `Chapter06.Section27` | 9 results |
| §28 Ordinary convex programs and Lagrange multipliers | `Chapter06.Section28` | 9 results |
| §29 Bifunctions and generalized convex programs | `Chapter06.Section29` | 12 results |
| §30 Adjoint bifunctions and dual programs | `Chapter06.Section30` | 10 results |
| §31 Fenchel's duality theorem | `Chapter06.Section31` | 12 results |
| §32 The maximum of a convex function | `Chapter06.Section32` | 11 results |
| §33 Saddle-functions | `Chapter07.Section33` | 11 results |
| §34 Closures and equivalence classes | `Chapter07.Section34` | 10 results |
| §35 Continuity and differentiability of saddle-functions | `Chapter07.Section35` | 12 results |
| §36 Minimax problems | `Chapter07.Section36` | 7 results |
| §37 Conjugate saddle-functions and minimax theorems | `Chapter07.Section37` | 18 results |
| §38 The algebra of bifunctions | `Chapter08.Section38` | 12 results |
| §39 Convex processes | `Chapter08.Section39` | 9 results |

## Conventions

* A declaration is named after the result that it states: `Rockafellar.theorem_6_9` is Theorem 6.9,
  `Rockafellar.corollary_37_5_2` is Corollary 37.5.2, and `Rockafellar.lemma_36_1_on` states Lemma
  36.1. Where one numbered result needs several declarations, for its separate clauses or for the
  two directions of an equivalence, a trailing word tells them apart, as in
  `Rockafellar.theorem_37_5_a` and `Rockafellar.theorem_34_2_dom₁`.
* The declarations are in the namespace `Rockafellar`. The results of §28 about an ordinary convex
  program (Theorems 28.3 and 28.4 and Corollaries 28.3.1 and 28.4.1) are in the namespace
  `Rockafellar.OrdinaryConvexProgram`.
* The book numbers its sections 1–39 continuously across its Parts I–VIII. The directory `ChapterNN`
  holds Part NN, and the module `ChapterNN.SectionMM` holds §MM, so the section modules keep the
  numbers of the book: §33, in Part VII, is `Chapter07.Section33`.
* The space $\mathbb{R}^n$ is `Rockafellar.Rn n`, which is `EuclideanSpace ℝ (Fin n)`, and the inner
  product $\langle x, y \rangle$ is `Rockafellar.pairing n`, the inner product read as a bilinear
  map. Both are in `NumlibSurface.Rockafellar.Common.Euclidean`, the one module of the library that
  is not a section of the book. The book writes $x^*$ for a vector of the same space $\mathbb{R}^n$;
  here the star is a naming convention and not a distinction of types. The space $\mathbb{R}^{m+p}$
  is the product `Rn m × Rn p`.
* The backbone states its duality theory for an abstract pairing of two real vector spaces, and
  `Rockafellar.pairing` instantiates all of it. Where the backbone is more general still, for a real
  vector space or a topological vector space, the library states the case of $\mathbb{R}^n$.
* A function $f : \mathbb{R}^n \to [-\infty, +\infty]$ is `f : Rn n → EReal`, defined on all of
  $\mathbb{R}^n$. It is convex when its epigraph is convex (`ConvexAnalysis.ConvexFn`). Properness,
  `ConvexAnalysis.ProperConvex`, means that $f$ is finite somewhere and never $-\infty$; it does not
  include convexity.
* The arithmetic of $[-\infty, +\infty]$ is that of `EReal`. As in the book,
  $0 \cdot (\pm\infty) = 0$, $\inf \emptyset = +\infty$ and $\sup \emptyset = -\infty$. The book
  leaves $\infty - \infty$ undefined, while `EReal` gives $+\infty + (-\infty)$ the value $-\infty$;
  no statement depends on that value.
* The closure $\operatorname{cl} C$ and the interior $\operatorname{int} C$ are the Mathlib
  `closure C` and `interior C`. The relative interior $\operatorname{ri} C$ is the backbone notation
  `ri C` for the Mathlib `intrinsicInterior ℝ C`.
* Theorems 24.1–24.3 are about functions on the real line and are stated over `ℝ` itself, not over
  `Rockafellar.Rn 1`.
* Part VII uses three orientations, each stated in the section that introduces it. For a function
  $K(u, v)$ that is concave in $u$ and convex in $v$, $\operatorname{cl}_1$ closes the first
  (concave) argument and $\operatorname{cl}_2$ the second (convex) argument (§33). From §36 on,
  minimization takes place in the convex argument and maximization in the concave argument. In the
  lower conjugate the supremum over the convex variable is outside, and in the upper conjugate the
  infimum over the concave variable is outside (§37). Under the opposite orientations the statements
  of §§34–37 change.

## Deviations from the source

**Part I: Basic Concepts**

* **Dimension, Sections 1 and 2** (generalization). The book defines dimension for affine and
  convex sets. The definition uses the affine hull for every set. See `Rockafellar.dim`,
  `Rockafellar.dim_of_nonempty` and `Rockafellar.dim_eq_finrank_direction`.
* **Orthogonality test before Theorem 1.3** (generalization). Orthogonality to a subspace can be
  checked on any spanning set. See `Rockafellar.mem_orthogonal_span_iff`.
* **Theorem 1.3** (correction). The book states that every hyperplane is a set
  $\{x \mid \langle x, b \rangle = \beta\}$ with $b \neq 0$; this fails in $\mathbb{R}^0$, where the
  empty set is a hyperplane. The statement assumes $n > 0$. See `Rockafellar.theorem_1_3_exists`.
* **Theorem 1.6, uniqueness** (generalization). Agreement on an affine basis determines any affine
  map, including maps that fail to be bijective. See `Rockafellar.theorem_1_6_unique`.
* **Theorem 2.4** (correction). The book states the theorem for every convex set $C$; for
  $C = \emptyset$ the maximum does not exist. The statement assumes $C$ non-empty. See
  `Rockafellar.theorem_2_4`.
* **Theorem 2.7, smallest subspace** (generalization). Every set has a smallest containing
  subspace, and the subspace is the affine hull whenever the set contains $0$. See
  `Rockafellar.theorem_2_7_least` and `Rockafellar.theorem_2_7_aff`.
* **Section 3, direct sum by unique decomposition** (correction). Both summands must be nonempty
  for their difference sets to intersect in $\{0\}$. See `Rockafellar.directSum_iff_unique`.
* **Section 3, direct sum by unique decomposition** (generalization). The equivalence applies to
  arbitrary nonempty sets. See `Rockafellar.directSum_iff_unique`.
* **Section 3, partial addition** (generalization). The operation and its algebraic laws extend
  to sets in a product of arbitrary types with the relevant addition operations. See
  `Rockafellar.partialAdd`, `Rockafellar.partialAdd_comm`, `Rockafellar.partialAdd_assoc`,
  `Rockafellar.partialAdd_eq_add`, `Rockafellar.partialAdd_eq_inter`,
  `Rockafellar.theorem_3_6_add` and `Rockafellar.theorem_3_6_inter`.
* **Section 3, cone correspondence** (correction). The cone of a convex set contains the origin
  when the set is nonempty. The empty set has empty cone. See `Rockafellar.coneLift` and
  `Rockafellar.zero_mem_coneLift`.
* **Section 3, inverse sum** (generalization). The formula and its two membership descriptions
  apply to arbitrary sets. See `Rockafellar.invSum`, `Rockafellar.mem_invSum_iff_exists`,
  `Rockafellar.invSum_eq_iUnion_singleton` and `Rockafellar.invSum_eq_partialAdd_coneLift`.
* **Section 3, inverse sum along a ray** (generalization). The scalar formula also holds when
  the common direction vector is zero. See `Rockafellar.invSum_singleton_smul`.
* **Theorem 3.8** (generalization). The book assumes convex cones $K_1, K_2$;
  $K_1 \# K_2 = K_1 \cap K_2$ holds for cones that contain the origin. See
  `Rockafellar.theorem_3_8_invSum`.
* **Corollary 4.7.1** (reading). The book's $\lambda_1, \dots, \lambda_m$ implies $m \ge 1$; the
  statement assumes $m > 0$ explicitly. See `Rockafellar.corollary_4_7_1`.
* **Theorem 4.8**, last sentence (correction). The book says that it suffices to check
  $f(-b_i) = -f(b_i)$ on a basis of $L$; this fails for $L = \{0\}$ when $f(0) = +\infty$. The
  statement requires a non-empty set. See `Rockafellar.theorem_4_8_basis`.
* **Theorem 4.8**, last sentence (generalization). The statement uses an arbitrary non-empty
  spanning set of $L$ instead of a basis. See `Rockafellar.theorem_4_8_basis`.
* **Theorem 5.1** (generalization). The book takes $\varphi$ with values in $(-\infty, +\infty]$;
  the statement allows the value $-\infty$. See `Rockafellar.theorem_5_1`.
* **Section 5, infimal convolution** (generalization). With the epigraph definition, the domain
  sum and translation formulas also hold for improper and nonconvex functions. See
  `Rockafellar.convexDom_infimalConvolution` and
  `Rockafellar.infimalConvolution_indicatorFn_singleton`.
* **Section 5, right scalar multiplication** (generalization). The lower boundary of the scaled
  epigraph is convex for every real scale and the formulas at nonnegative scales hold for
  arbitrary functions. See `Rockafellar.convexFn_rightSMul`, `Rockafellar.rightSMul_apply_pos` and
  `Rockafellar.rightSMul_zero`.
* **Section 5, positively homogeneous convex generator** (generalization). The greatest-function
  property holds for arbitrary $h$, and the formula away from $0$ includes $h \equiv +\infty$.
  See `Rockafellar.isGreatest_posHomGen` and `Rockafellar.posHomGen_apply`.
* **Section 5, maximum coordinate and Tchebycheff norm** (generalization). The extended-real
  supremum equals $-\infty$ when there are no coordinates. See `Rockafellar.convexFn_maxCoord`
  and `Rockafellar.convexFn_tchebycheffNorm`.
* **Theorem 5.8**, functions $f$ and $h$ (generalization). The book assumes $f_1, \dots, f_m$
  proper; the statements do not. See `Rockafellar.theorem_5_8_f` and `Rockafellar.theorem_5_8_h`.

**Part II: Topological Properties**

* **Section 6, relative topology** (generalization). The relative boundary and relative openness
  are defined for arbitrary sets, and relative interior is contained in the original set, which
  is contained in its closure. See `Rockafellar.relbd`, `Rockafellar.IsRelativelyOpen` and
  `Rockafellar.relint_subset_subset_closure`.
* **Section 6, relative and ordinary interior** (generalization). They agree for every set whose
  affine hull is the whole space. See `Rockafellar.relint_eq_interior`.
* **Theorem 6.2**, affine hull and dimension of the closure (generalization). The book assumes $C$
  convex; the statements hold for every set. See `Rockafellar.theorem_6_2_aff_cl` and
  `Rockafellar.theorem_6_2_dim_cl`.
* **Theorem 6.6**, closure (generalization). The book assumes $C$ convex; $\operatorname{cl}(AC)
  \supseteq A(\operatorname{cl} C)$ holds for every set. See `Rockafellar.theorem_6_6_cl`.
* **Corollary 6.6.2**, closure (generalization). The book assumes $C_1, C_2$ convex; the inclusion
  holds for all sets. See `Rockafellar.corollary_6_6_2_cl`.
* **Section 6, direct sums** (generalization). Relative interior and closure commute with the
  Cartesian product of arbitrary sets. See `Rockafellar.relint_prod` and `Rockafellar.closure_prod`.
* **Section 6, closure of a cone** (generalization). The closure preserves the cone property
  without convexity. See `Rockafellar.isCone_closure`.
* **Definition of $\operatorname{cl} f$** (generalization). The book defines closure for convex
  functions and gives the epigraph-closure identity for proper convex functions. The Lean
  closure extends to arbitrary functions by testing whether the lower semicontinuous hull takes
  the value $-\infty$. See `ConvexAnalysis.convexCl`.
* **Closedness of a proper convex function** (generalization). Closedness is lower semicontinuity
  without convexity. See `Rockafellar.closedConvex_iff_lowerSemicontinuous_of_properConvex`.
* **Closed improper convex functions** (generalization). They are the constants $\pm\infty$ without
  convexity. See `Rockafellar.closed_improper_eq_const`.
* **Theorem 7.6, dimension argument** (generalization). The strict sublevel set restricted to
  the relative interior of the effective domain has the same affine hull as that domain
  without properness. See `Rockafellar.affineSpan_relint_convexDom_lt`.
* **Section 8, recession cone and lineality of sets** (generalization). The formulas for the
  recession cone, lineality subspace and orthogonal decomposition apply to arbitrary sets.
  Translation invariance characterizes lineality for every convex set, including the empty set.
  See `Rockafellar.mem_recessionCone_iff`, `Rockafellar.mem_linealitySpace_iff`,
  `Rockafellar.linealitySpace_eq_add_eq_surface`,
  `Rockafellar.linealitySubmodule_isGreatest_surface` and
  `Rockafellar.linealitySpace_add_inter_orthogonal`.
* **Section 8, recession function and its epigraph** (generalization). The epigraph identities
  hold for every $f$. The test at scale one holds for convex $f$, including the constant
  $+\infty$. See `Rockafellar.epi_recessionFn_surface`,
  `Rockafellar.mk_mem_recessionCone_epi_iff_surface` and
  `Rockafellar.recessionFn_le_coe_iff_surface`.
* **Section 8, recession cone and constancy space of functions** (generalization). The cone and
  subspace identities hold for arbitrary functions. See `Rockafellar.recessionConeFn_eq_slice`,
  `Rockafellar.recessionConeFn_cone`, `Rockafellar.mem_constancySpace_iff` and
  `Rockafellar.constancySubmodule_isGreatest_surface`.
* **Theorem 8.1**, first assertion (generalization). The book assumes $C$ non-empty and convex; the
  statement holds for every set. See `Rockafellar.theorem_8_1_cone`.
* **Theorem 8.1**, second assertion (generalization). The book assumes $C$ non-empty; only convexity
  is needed. See `Rockafellar.theorem_8_1_add_subset`.
* **Theorem 8.2**, first assertion (generalization). Convexity and non-emptiness of $C$ are dropped;
  only closedness is needed. See `Rockafellar.theorem_8_2_isClosed`.
* **Theorem 8.3** (generalization). The half-line condition also permits the zero direction, and
  the existence of the half-line implies nonemptiness. See `Rockafellar.theorem_8_3` and
  `Rockafellar.theorem_8_3_relint`.
* **Corollary 8.3.1** (generalization). The book assumes $C$ non-empty; the statement does not. See
  `Rockafellar.corollary_8_3_1`.
* **Theorem 8.5**, first assertion (generalization). The book assumes $f$ proper convex; positive
  homogeneity and convexity of $f0^+$ hold for every $f$, and properness of $f0^+$ needs only
  properness of $f$. See `Rockafellar.theorem_8_5_posHomogeneous`, `Rockafellar.theorem_8_5_convex`
  and `Rockafellar.theorem_8_5_proper`.
* **Theorem 8.6** (generalization). The book assumes $f$ proper; the monotonicity needs only
  convexity, and the equivalence holds for every $f$. See `Rockafellar.theorem_8_6_antitone` and
  `Rockafellar.theorem_8_6_iff`.
* **Corollary 8.6.1** (generalization). The book assumes $f$ proper convex; the statement holds for
  every $f$. See `Rockafellar.corollary_8_6_1`.
* **Corollary 8.6.2** (generalization). The book assumes $f$ finite on $M$; the statement does not.
  See `Rockafellar.corollary_8_6_2`.
* **Theorem 8.8**, (a) $\Leftrightarrow$ (b) (generalization). The book assumes $f$ proper convex;
  the statement holds for every $f$. See `Rockafellar.theorem_8_8_a_iff_b`.
* **Theorem 8.8**, (b) $\Leftrightarrow$ (c) and (a) $\Leftrightarrow$ (c) (generalization). The
  book assumes $f$ proper convex; only properness is needed. See `Rockafellar.theorem_8_8_b_iff_c`
  and `Rockafellar.theorem_8_8_a_iff_c`.
* **Section 8, lineality space of a function** (generalization). The linear subspace and
  projection formulas require properness without convexity. See
  `Rockafellar.linealitySpaceFn_eq_image_surface` and
  `Rockafellar.coe_linealitySubmoduleFn_surface`.
* **Theorem 9.1**, first and last conclusions (generalization). The book assumes $C$ nonempty.
  `Rockafellar.theorem_9_1_closure` and `Rockafellar.theorem_9_1_isClosed` also apply to the
  empty set.
* **Theorem 9.3**, closure formula (generalization). The two-function formula also applies when
  both functions are closed. See `Rockafellar.theorem_9_3_closure`.
* **Theorem 9.4**, closed case (generalization). Neither convexity nor properness of the $f_i$ is
  needed. See `Rockafellar.theorem_9_4_closed`.
* **Theorem 9.4**, second half (generalization). The formula is stated for lower semicontinuous
  hulls, for convex $f_i$ that need not be proper, and with only $f(\bar x) < +\infty$. See
  `Rockafellar.theorem_9_4_closure`.
* **Theorem 9.4**, properness (generalization). The book assumes the $f_i$ proper convex; only
  properness is needed. See `Rockafellar.theorem_9_4_proper`.
* **Theorem 9.4**, recession formula (generalization). The book assumes the $f_i$ closed proper
  convex; only convexity and closed epigraphs are needed. See `Rockafellar.theorem_9_4_recession`.
* **Theorem 9.5**, closed case (generalization). The book assumes $g$ proper convex; only a closed
  epigraph is needed. See `Rockafellar.theorem_9_5_closed`.
* **Theorem 9.5**, recession formula (generalization). The book assumes $g$ proper convex; only
  convexity and a closed epigraph are needed. See `Rockafellar.theorem_9_5_recession`.
* **Theorem 9.5**, closure formula (generalization). The formula also applies to closed $g$.
  See `Rockafellar.theorem_9_5_closure`.
* **Theorem 9.6 and Corollary 9.6.1** (reading). The generated cone includes zero. Its closure
  agrees with the closure of the cone of positive multiples, and the closedness conclusion
  for bounded $C$ uses the generator with zero adjoined. See `Rockafellar.theorem_9_6`,
  `Rockafellar.theorem_9_6_iUnion` and `Rockafellar.corollary_9_6_1`.
* **Section 9, extended coefficients** (reading). `Rockafellar.ExtCoeff.Nonneg` permits both
  ordinary zero and the recession symbol. In `Rockafellar.theorem_9_8`, the recession choice
  includes the contribution of ordinary zero, so the union is the one in the book.
* **Corollary 9.8.2** (generalization). The book assumes the sets are convex.
  `Rockafellar.corollary_9_8_2` needs only that the two sets are closed and bounded.
* **Theorem 10.3**, existence (reading). The result assumes $C$ nonempty and gives the closed
  proper convex ambient extension constructed in the proof. See `Rockafellar.theorem_10_3`.
* **Theorem 10.3**, uniqueness (generalization). Any two continuous restrictions that agree on
  $\operatorname{ri} C$ agree on $C$. See `Rockafellar.theorem_10_3_unique`.
* **Theorem 10.6**, hypotheses (a) and (b) (generalization). The pointwise bounds also admit the
  empty family, and hypothesis (a) uses the density condition described below. See
  `Rockafellar.theorem_10_6_ab`.

**Part III: Duality Correspondences**

* **Section 11, separation** (generalization). The separation predicates also admit empty
  inputs. See `Rockafellar.SeparatesRn`, `Rockafellar.SeparatesProperlyRn`,
  `Rockafellar.SeparatesStrictlyRn`, `Rockafellar.SeparatesStronglyRn`,
  `Rockafellar.SeparableProperly` and `Rockafellar.SeparableStrongly`.
* **Theorem 11.5 and Corollary 11.5.1** (reading). The intersection also includes inequalities
  with zero normal. The empty inequality covers empty inputs in dimension zero.
* **Corollary 11.5.2** (correction). The book assumes only $C \neq \mathbb{R}^n$; the statement also
  needs $C \neq \emptyset$, because for $n = 0$ the empty set is a counterexample. See
  `Rockafellar.corollary_11_5_2`.
* **Section 11, supporting half-space** (generalization). `Rockafellar.IsSupportingHalfSpace`
  also admits nonconvex sets.
* **Corollary 11.7.2** (reading). The generated cone includes zero, giving $\{0\}$ when the
  generating set is empty. See `Rockafellar.corollary_11_7_2`.
* **Corollary 11.7.3** (correction). The book assumes only $K \neq \mathbb{R}^n$; the statement also
  needs $K \neq \emptyset$, for the same reason. See `Rockafellar.corollary_11_7_3`.
* **Theorem 12.2**, convexity and closedness of $f^*$ and $(\operatorname{cl} f)^* = f^*$
  (generalization). These clauses hold for every $f$. See `Rockafellar.theorem_12_2_convex`,
  `Rockafellar.theorem_12_2_closed` and `Rockafellar.theorem_12_2_conj_clFn`.
* **Fenchel's inequality** (generalization). It holds for every proper $f$, not only for proper
  convex $f$. See `Rockafellar.fenchel_inequality`.
* **Theorem 12.3** (generalization). The function $h$ need not be convex. See
  `Rockafellar.theorem_12_3`.
* **Section 12, symmetry** (generalization). The symmetry predicate admits arbitrary linear
  bijections. Forward invariance of the conjugate under orthogonal transformations applies
  to any function. See `Rockafellar.SymmetricWrt` and `Rockafellar.convexConj_comp_orthogonal`.
* **Section 12, monotone conjugate** (reading). The operator acts on ambient functions and
  extends the result by $+\infty$ off the orthant. The book's formula holds when the input
  is also extended by $+\infty$. See `Rockafellar.monotoneConjOrthant` and
  `Rockafellar.monotoneConjOrthant_apply`.
* **Section 13, support and barrier cones** (generalization). The support and barrier formulas
  admit nonconvex inputs. See `Rockafellar.supportFn_apply_rn`, `Rockafellar.barrierCone` and
  `Rockafellar.supportFn_add_rn`.
* **Section 8, rank** (generalization). `Rockafellar.rankFn` extends the rank formula from
  proper convex functions to arbitrary ambient functions.
* **Theorem 13.1**, interior clause (correction). The book omits $C \neq \emptyset$; over
  $\mathbb{R}^0$ the stated condition holds for $C = \emptyset$, while
  $\operatorname{int} \emptyset = \emptyset$. See `Rockafellar.theorem_13_1_int`.
* **Theorem 13.1**, affine hull clause (generalization). The set $C$ need not be convex. See
  `Rockafellar.theorem_13_1_aff`.
* **Theorem 13.2**, $\delta(\cdot \mid C)^* = \delta^*(\cdot \mid C)$ (generalization). This holds
  for every set $C$. See `Rockafellar.theorem_13_2_conj_indicator`.
* **Corollary 13.2.2** (reading). The representing bounded set may be nonconvex, and the
  function is explicitly closed. Both formulations describe the same support functions.
  See `Rockafellar.corollary_13_2_2`.
* **Corollary 13.3.1** (reading). Properness is explicit so the full effective domain of the
  conjugate expresses finiteness everywhere. See `Rockafellar.corollary_13_3_1`.
* **Corollary 13.3.2**, affine characterization in proof (reading). In the support-function
  formulation, the convex set is nonempty. See `Rockafellar.affine_iff_forall_reversible`.
* **Theorem 13.5** (generalization). The first assertion needs $f$ closed convex but not proper, and
  the dual assertion needs no hypothesis. See `Rockafellar.theorem_13_5` and
  `Rockafellar.theorem_13_5_dual`.
* **Corollary 13.5.1** (reading). The three-case function $k$ of the book is stated as the closure
  of the homogenization `ConvexAnalysis.hom f`. See `Rockafellar.corollary_13_5_1`.
* **Corollary 13.5.1** (generalization). The function $f$ need only be convex with non-empty
  effective domain. See `Rockafellar.corollary_13_5_1`.
* **Section 14, polar membership** (generalization). Both polar membership formulas admit
  arbitrary sets. See `Rockafellar.mem_polarCone_rn` and `Rockafellar.mem_polarSet_rn`.
* **Section 14, compatibility of polars** (generalization). Positive scale invariance suffices
  for the two polars to agree. See `Rockafellar.polarCone_eq_polarSet_rn`.
* **Theorem 14.1**, first assertion (generalization). The polar of every set is a non-empty closed
  convex cone. See `Rockafellar.theorem_14_1_nonempty`, `Rockafellar.theorem_14_1_convex`,
  `Rockafellar.theorem_14_1_isCone` and `Rockafellar.theorem_14_1_isClosed`.
* **Theorem 14.1**, $\delta(\cdot \mid K)^* = \delta(\cdot \mid K^\circ)$ (generalization). This
  holds for every convex cone that contains the origin, closed or not. See
  `Rockafellar.theorem_14_1_conj`.
* **Section 14, polar of the closure** (generalization). Closure preserves the cone polar of
  any set. See `Rockafellar.polarCone_closure_rn`.
* **Section 14, generated-cone examples** (generalization). The generator family may be empty.
  See `Rockafellar.polarCone_hull_range_rn` and `Rockafellar.polarCone_setOf_forall_le_zero_rn`.
* **Theorem 14.5**, first assertion (generalization). The polar of every set is closed, convex and
  contains the origin. See `Rockafellar.theorem_14_5_isClosed`, `Rockafellar.theorem_14_5_convex`
  and `Rockafellar.theorem_14_5_zero_mem`.
* **Theorem 14.5**, gauge of $C^\circ$ (generalization). Only $0 \in C$ is needed. See
  `Rockafellar.theorem_14_5_gauge_dual`.
* **Section 8, rank of a set** (generalization). `Rockafellar.rankSet` also admits empty and
  nonconvex sets.
* **Theorem 14.7** (generalization). The inclusions need $f \ge 0$ convex with $f(0) = 0$ but not
  closed; $f^* \ge 0$ needs only $f(0) = 0$; $f^*(0) = 0$ needs only $f \ge 0$ and $f(0) = 0$. See
  `Rockafellar.theorem_14_7_left`, `Rockafellar.theorem_14_7_right`,
  `Rockafellar.theorem_14_7_conj_nonneg` and `Rockafellar.theorem_14_7_conj_zero`.
* **Section 15, gauge, polar and obverse formulas** (generalization). The formulas admit
  arbitrary sets or functions for gauges, polar gauges, and the obverse. The functional polar
  formula needs nonnegativity and vanishing at zero without convexity. See
  `Rockafellar.gaugeFn_apply_rn`, `Rockafellar.polarGauge_apply_rn`,
  `Rockafellar.polarFn_apply_rn` and `Rockafellar.obverse_apply_rn`.
* **Corollary 15.1.1**, polar sets and polar gauges (generalization). The set $C$ need not be
  closed. See `Rockafellar.corollary_15_1_1_sets`.
* **Corollary 15.1.2** (generalization). $\gamma(\cdot \mid C)^\circ = \delta^*(\cdot \mid C)$ holds
  for every convex set $C$ that contains the origin. See `Rockafellar.corollary_15_1_2`.
* **Theorem 15.2**, the gauge of $C$ is a norm (generalization). The set $C$ need not be closed. See
  `Rockafellar.theorem_15_2_isNorm`.
* **Theorem 15.3**, $f^* = g^+ \circ k^\circ$ (generalization). The function $g$ need not be
  non-constant. See `Rockafellar.theorem_15_3_conj`.
* **Theorem 15.4**, first assertion (generalization). The properties of $f^\circ$ need fewer
  hypotheses, and never the convexity of $f$. See `Rockafellar.theorem_15_4_nonneg`,
  `Rockafellar.theorem_15_4_map_zero`, `Rockafellar.theorem_15_4_convexFn` and
  `Rockafellar.theorem_15_4_closedFn`.
* **Theorem 16.1** (generalization). Both formulas for $\lambda > 0$ hold for every $f$,
  and the right multiplication formula at zero needs only properness. See
  `Rockafellar.theorem_16_1_left`, `Rockafellar.theorem_16_1_right` and
  `Rockafellar.theorem_16_1_right_zero`.
* **Corollary 16.1.1** (generalization). The book assumes $C$ convex; only non-emptiness is used.
  See `Rockafellar.corollary_16_1_1`.
* **Corollary 16.1.2** (generalization). The book assumes $C$ non-empty and convex; the formula
  holds for every set. See `Rockafellar.corollary_16_1_2`.
* **Theorem 16.3**, first formula (generalization). The book assumes $f$ convex; the formula holds
  for every $f$. See `Rockafellar.theorem_16_3_image`.
* **Theorem 16.3**, exact form and attainment (reading). The declarations assume $g$ proper.
  The improper case gives vacuous $+\infty$ values under the relative-interior hypothesis.
  See `Rockafellar.theorem_16_3_exact` and `Rockafellar.theorem_16_3_attained`.
* **Corollary 16.3.1**, first formula (generalization). The book assumes $C$ convex; the formula
  holds for every set. See `Rockafellar.corollary_16_3_1_image`.
* **Corollary 16.3.2**, first formula (generalization). The book assumes $C$ convex; the formula
  holds for every set. See `Rockafellar.corollary_16_3_2_image`.
* **Corollary 16.3.2**, second formula (correction). For $A = 0$ on $\mathbb{R}$ and $D = \{1\}$,
  the printed left side is $\mathbb{R}$ and the right side is $\{0\}$. The adjoint-image
  inclusion holds for all $D$. See `Rockafellar.corollary_16_3_2_preimage`.
* **Theorem 16.4**, first two formulas (generalization). The convolution formula admits
  arbitrary functions and the binary closure formula admits improper convex functions. See
  `Rockafellar.theorem_16_4_infConv_finset`, `Rockafellar.theorem_16_4_infConv` and
  `Rockafellar.theorem_16_4_closure`.
* **Corollary 16.4.1**, first two formulas (generalization). The sum formulas admit arbitrary
  sets, and the binary intersection formula admits empty convex sets. See
  `Rockafellar.corollary_16_4_1_add`, `Rockafellar.corollary_16_4_1_add_finset` and
  `Rockafellar.corollary_16_4_1_closure`.
* **Corollary 16.4.2** (generalization). The book assumes convex cones; convexity is not used. See
  `Rockafellar.corollary_16_4_2_add`.
* **Theorem 16.5**, first two formulas (generalization). The convex-hull formula admits
  arbitrary functions and the closure formula admits improper convex functions. See
  `Rockafellar.theorem_16_5_convFn` and `Rockafellar.theorem_16_5_closure`.
* **Corollaries 16.5.1 and 16.5.2**, first formulas (generalization). The hull formulas for
  support and polarity admit arbitrary sets. See `Rockafellar.corollary_16_5_1_hull`
  and `Rockafellar.corollary_16_5_2_hull`.
* **Corollary 16.5.1**, second formula (reading). The formula fails for an empty family, so the
  index set is assumed nonempty. Individual sets may be empty. See
  `Rockafellar.corollary_16_5_1_closure`.
* **Corollary 16.5.2**, second formula (correction). For $C_1 = \{1\}$ and $C_2 = \{2\}$ in
  $\mathbb{R}$, the printed left side is $\mathbb{R}$ and the right side is $(-\infty,1]$.
  `Rockafellar.corollary_16_5_2_inter` gives the inclusion of each polar.

**Part IV: Representation and Inequalities**

* **Theorem 17.1**, simplex decomposition (reading). The simplex formula assumes a nonempty
  point set so the dimension is a natural number. See `Rockafellar.theorem_17_1_simplex`
  and `Rockafellar.convexHullPD_empty_points`.
* **Corollary 17.1.2** (generalization). The book assumes $x \neq 0$ and $C_i \neq \emptyset$;
  neither is needed. See `Rockafellar.corollary_17_1_2`.
* **Corollary 17.1.4** (correction). The printed statement is false; a counterexample on
  $\mathbb{R}^1$ is `Rockafellar.corollary_17_1_4_false`.
* **Corollary 17.1.6** (correction). The printed statement is false; a counterexample on
  $\mathbb{R}^1$ is `Rockafellar.corollary_17_1_6_false`.
* **Theorem 17.3** (correction). The statement needs $0 \notin S^*$, which the book omits; the
  hypotheses $S^* \neq \emptyset$ and $x^* \neq 0$ of the book are not needed. See
  `Rockafellar.theorem_17_3`.
* **Section 18, faces and extreme points** (generalization). Face and extreme-point
  characterizations, transitivity and nonempty intersections of faces, and the intermediate-set
  property admit arbitrary ambient sets. See `Rockafellar.isFace_iff`,
  `Rockafellar.isFace_mono`, `Rockafellar.faces_isGLB` and `Rockafellar.mem_extremePoints_iff`.
* **Theorem 18.1 and Corollaries 18.1.2 and 18.1.3** (generalization). These face containment,
  equality and relative-boundary results also hold for nonconvex ambient sets.
  `Rockafellar.theorem_18_1` allows nonconvex $D$ as well.
* **Theorem 18.2**, covering and disjointness (generalization). The covering identity also
  applies to empty $C$. The relative interiors of distinct faces are disjoint even for
  nonconvex ambient sets. See `Rockafellar.theorem_18_2_union` and
  `Rockafellar.theorem_18_2_disjoint`.
* **Theorem 18.3** (generalization). The book assumes the face $C'$ non-empty; this is not needed.
  See `Rockafellar.theorem_18_3`.
* **Section 18, orthogonal reduction of faces** (generalization). The formulas apply to
  arbitrary ambient sets. See `Rockafellar.eq_add_inter_orthogonal_of_isFace` and
  `Rockafellar.facesEquivFacesInterOrthogonal`.
* **Section 18, extreme and exposed rays** (generalization). The ray predicates admit arbitrary
  sets. The correspondence with extreme directions uses nonnegative scaling and nonemptiness.
  See `Rockafellar.IsExtremeRay`, `Rockafellar.IsExposedRay` and
  `Rockafellar.isExtremeRay_iff_isExtremeDirection`.
* **Corollaries 18.5.2 and 18.7.1** (generalization). The book assumes that the cone contains more
  than the origin; this is not needed. See `Rockafellar.corollary_18_5_2` and
  `Rockafellar.corollary_18_7_1`.
* **Section 18, exposed faces and points** (reading). The empty set is always an exposed face,
  and the zero functional exposes a singleton even in dimension zero. See
  `Rockafellar.isExposed_iff_exists_vector` and `Rockafellar.mem_exposedPoints_iff`.
* **Section 18, tangency** (reading). The predicate uses uniqueness of the supporting half-space
  orientation, equivalent to uniqueness of the hyperplane for full-dimensional sets.
  See `Rockafellar.IsTangentHyperplaneAt`.
* **Section 19, polyhedral function normal form** (reading). The formula needs to exclude
  functions taking the value $-\infty$ under the extended-real addition convention. See
  `Rockafellar.polyhedralFn_iff_normalForm`.
* **Corollary 19.3.4** (generalization). Polyhedrality of the convolution and attainment at
  finite values need no properness hypotheses. See `Rockafellar.corollary_19_3_4` and
  `Rockafellar.corollary_19_3_4_attained`.
* **Theorem 19.5**, scalar multiples (generalization). The dilation result applies to empty
  polyhedral sets. See `Rockafellar.theorem_19_5_smul`.
* **Theorem 19.6**, finite-family formulas (reading). A sum with the recession cones gives
  the extended-coefficient union, and the indexing family may be empty. See
  `Rockafellar.theorem_19_6_biUnion` and `Rockafellar.theorem_19_6_biUnion_add`.
* **Section 20, proper separation excluding containment** (generalization). The predicate
  `Rockafellar.SeparableProperlyNotContaining` admits arbitrary input sets.
* **Theorem 20.4** (generalization). The book assumes $C$ non-empty and convex; neither is needed.
  See `Rockafellar.theorem_20_4`.
* **Section 21, systems of inequalities** (generalization). System data, solutions,
  consistency and normalization admit arbitrary functions. A weak system has a closed
  solution set under closedness alone. See `Rockafellar.ConvexSystem`,
  `Rockafellar.ConvexSystem.isClosed_solutions` and `Rockafellar.ConvexSystem.solutions_normalize`.
* **Theorems 21.1–21.3**, exclusivity (generalization). Exclusivity uses the weighted-sum
  premises without the other hypotheses of the alternatives. See
  `Rockafellar.theorem_21_1_exclusive`, `Rockafellar.theorem_21_2_exclusive` and
  `Rockafellar.theorem_21_3_exclusive`.
* **Comments and References for Part IV** (typo). The book cites a "Corollary 21.3.3", which does
  not exist; the intended reference is Corollary 21.3.2, Helly's theorem.
* **Theorem 22.2** (generalization). The strict family may be empty, so feasibility follows
  from the weak-system consistency hypothesis. See `Rockafellar.theorem_22_2`.
* **Section 22, interval data** (generalization). The generalized rectangle, weighted
  sums and positivity condition are defined for arbitrary real subsets. See
  `Rockafellar.rectangle`, `Rockafellar.intervalCombo` and `Rockafellar.posIntervalCombo`.

**Part V: Differential Theory**

* **Theorem 23.1** (generalization). The infimum definition and positive homogeneity of
  $f'(x; \cdot)$ apply for any $f$ and $x$, and $f'(x; 0) = 0$ holds without convexity.
  See `Rockafellar.theorem_23_1_iInf`, `Rockafellar.theorem_23_1_posHomogeneous` and
  `Rockafellar.theorem_23_1_zero`.
* **Theorem 23.2** (generalization). The equivalence holds without convexity of $f$. See
  `Rockafellar.theorem_23_2`.
* **Theorem 23.3**, properness (generalization). A subgradient at a finite point implies
  properness without convexity. See `Rockafellar.theorem_23_3_proper`.
* **Theorem 23.4**, first assertion (generalization). $\partial f(x) = \emptyset$ for
  $x \notin \operatorname{dom} f$ holds for every proper $f$. See
  `Rockafellar.theorem_23_4_notMem_dom`.
* **Theorem 23.5** (generalization). Conditions (a), (b) and (c) are equivalent for every $f$, and
  (d) needs only properness. Under agreement with the closure, (a*) and (b*) need only
  convexity and (a**) holds for any function. See `Rockafellar.theorem_23_5_b` and
  `Rockafellar.theorem_23_5_a_star_star`.
* **Corollary 23.5.1** (generalization). The book assumes $f$ closed proper convex; properness is
  not needed. See `Rockafellar.corollary_23_5_1`.
* **Corollary 23.5.2** (generalization). Properness is not needed. See
  `Rockafellar.corollary_23_5_2_clFn` and `Rockafellar.corollary_23_5_2_subdifferential`.
* **Corollary 23.5.4** (generalization). The three-condition characterization applies
  to nonclosed convex cones containing the origin. See `Rockafellar.corollary_23_5_4`.
* **Section 23, approximate subdifferentials** (generalization). The closedness, convexity
  and intersection statements permit nonconvex functions. See
  `Rockafellar.epsSubdifferential_convex_closed` and `Rockafellar.epsSubdifferential_iInter`.
* **Theorems 23.8 and 23.9**, inclusion clauses (generalization). The sum-rule and composition
  inclusions apply to arbitrary functions. See `Rockafellar.theorem_23_8_subset` and
  `Rockafellar.theorem_23_9_subset`.
* **Corollary 23.8.1** (reading). The hypothesis $x \in C_i$ is added, because the normal cone of
  the library is defined at every point, while the normal cone of the book is empty off $C$. See
  `Rockafellar.corollary_23_8_1`.
* **Theorem 24.1** (generalization). Monotonicity, finiteness and the interlacing inequalities hold
  without closedness of $f$, and the finiteness clause is an equivalence. See
  `Rockafellar.theorem_24_1_finite_iff`.
* **Remark after Theorem 24.1** (generalization). The formula for $\partial f(x)$ needs only
  properness of $f$. See `Rockafellar.theorem_24_1_subdifferential`.
* **Theorem 24.5** (generalization). A sequence converging to a point of the open set can
  start outside it. See `Rockafellar.theorem_24_5_limsup`.
* **Theorem 24.6** (generalization). Closedness of $f$ is not assumed. See
  `Rockafellar.theorem_24_6_lt`.
* **Section 24, subdifferential supporting sets** (generalization). The set
  $\partial f(x)_y$ is defined for arbitrary inputs. See `Rockafellar.subdifferentialNormal`.
* **Theorem 24.7** (reading). The Lipschitz constant is some bound $\alpha$ on the subgradients over
  $S$, not necessarily $\sup\{|x^*| \mid x^* \in \partial f(S)\}$. See
  `Rockafellar.theorem_24_7_bound`.
* **Theorem 24.7** (generalization). The bounds need no closedness of $f$, nonemptiness of
  $\partial f(S)$ needs no compactness of $S$, and the compactness claim admits empty $S$.
  See `Rockafellar.theorem_24_7_bound`, `Rockafellar.theorem_24_7_nonempty` and
  `Rockafellar.theorem_24_7_isCompact`.
* **Section 24, subdifferential monotonicity** (generalization). Properness without convexity
  suffices. See `Rockafellar.isMonotoneRel_subgradientRel_rn`.
* **Section 25, gradient vector** (reading). `Rockafellar.gradientVec` is defined everywhere
  from the derivative of the real trace.
* **Theorem 25.1** (reading). Lean uses an explicit properness hypothesis in the converse and both
  equivalences. See `Rockafellar.theorem_25_1`.
* **Corollary 25.1.3** (generalization). The support-set formula implies that $C$ is nonempty,
  closed and convex. See `Rockafellar.corollary_25_1_3`.
* **Theorem 25.3**, continuity and monotonicity (generalization). The right derivative, defined on
  all of $\mathbb{R}$, is continuous at each point of $D$ and non-decreasing on $\mathbb{R}$. See
  `Rockafellar.theorem_25_3_continuousAt` and `Rockafellar.theorem_25_3_monotone`.
  The continuity statement assumes closedness, as in the source's proof.
* **Theorem 25.4** (generalization). The three formalized assertions also allow $y = 0$.
  See `Rockafellar.theorem_25_4_continuousAt_iff`.
* **Theorem 25.6** (reading). The book sets $K(x) = \emptyset$ for $x \notin \operatorname{dom} f$;
  here $K(x)$ is the normal cone, defined at every $x$. See `Rockafellar.theorem_25_6`.
* **Section 23 recession-cone exercise** (generalization). The identity used in Theorem 25.6
  holds for a proper function with a subgradient even without convexity. See
  `Rockafellar.recessionCone_subdifferential_eq_normalCone`.
* **Theorem 25.7** (generalization). The book assumes differentiability on $C$; the pointwise
  statement uses differentiability at $x$ only. See `Rockafellar.theorem_25_7`.
* **Section 26, essential smoothness** (reading). `Rockafellar.EssentiallySmoothBook` isolates
  the defining conditions from properness and convexity.
* **Theorem 26.1**, interior formula (generalization). The gradient singleton formula holds
  without closedness. See `Rockafellar.theorem_26_1_gradient`.
* **Lemma 26.2** (reading). Lean assumes closedness, as in the proof, and extends the
  pointwise equivalence to any $x$. See `Rockafellar.lemma_26_2_at`.
* **Section 26, Legendre domain** (reading). `Rockafellar.legendreDomain` uses the domain
  interior and the total gradient of the real trace.
* **Theorem 26.4** (generalization). The book assumes $f$ closed proper and differentiable on a
  non-empty $C$; the well-definedness of $g$ and $g = f^*$ on $D$ need only convexity, and
  $D \subseteq \operatorname{dom} f^*$ needs in addition only differentiability on $C$. See
  `Rockafellar.theorem_26_4_wellDefined`, `Rockafellar.theorem_26_4_eq` and
  `Rockafellar.theorem_26_4_subset_dom_conj`.
* **Corollary 26.4.1**, value formula (generalization). The equality on $D$ holds without
  closedness. See `Rockafellar.corollary_26_4_1_eq`.
* **Section 26, upper-half-plane example** (reading). `Rockafellar.halfPlaneFn` extends the
  source formula by $+\infty$ outside the open half-plane.
* **Theorem 26.5** (reading). The book says closed convex function, and its proof needs a closed
  proper one. Here $f$ is assumed proper. The forward value formula and continuity of
  $\nabla f$ hold without closedness. See `Rockafellar.theorem_26_5`.
* **Theorem 26.6**, value formula (generalization). The value at $\nabla f(x)$ has the stated
  formula without gradient bijectivity. See `Rockafellar.theorem_26_6_apply`.

**Part VI: Constrained Extremum Problems**

* **Section 27, minimum-set criteria** (generalization). Convexity of the minimum set does
  not need properness. The zero-subgradient criterion holds for arbitrary functions and
  the directional-derivative criterion only needs finiteness at the given point. See
  `Rockafellar.convex_argmin_surface` and `Rockafellar.mem_argmin_iff_zero_le_dirDeriv`.
* **Theorem 27.1(a)** (generalization). The book assumes $f$ closed proper convex; clause (a) holds
  for every function. See `Rockafellar.theorem_27_1_a` and `Rockafellar.theorem_27_1_a_bddBelow`.
* **Theorem 27.1(b)**, first two sentences (generalization). Properness is not needed. See
  `Rockafellar.theorem_27_1_b` and `Rockafellar.theorem_27_1_b_attained`.
* **Theorem 27.1(g)**, first sentence (generalization). Properness is not needed. See
  `Rockafellar.theorem_27_1_g_setOf_le`.
* **Theorem 27.1(h)**, proof identity (generalization). Lean allows all real $\varepsilon$.
  See `Rockafellar.theorem_27_1_h_epsSubdifferential`.
* **Corollary 27.2.1** (generalization). Distance to the minimum set tends to zero along
  arbitrary minimizing filters. See `Rockafellar.corollary_27_2_1_infDist`.
* **Corollaries 27.3.1 and 27.3.2** (reading). Lean explicitly assumes a nonempty
  polyhedral constraint set.
* **Corollary 27.3.3**, polyhedral refinement (generalization). The finite polyhedral
  constraint functions need only polyhedral epigraphs. See
  `Rockafellar.corollary_27_3_3_polyhedral`.
* **Theorem 27.4**, sufficiency (generalization). No hypothesis on $h$ or $C$ is needed, and $x$
  need not lie in $C$. See `Rockafellar.theorem_27_4_sufficient`.
* **Section 28, affine extension** (generalization). The source chooses global affine
  extensions for all constraints affine on $C$. Lean requires this for equality constraints
  only. See `Rockafellar.OrdinaryConvexProgram`.
* **Section 28, optimal solutions** (generalization). The infimum-attainment definition also
  applies to infeasible programs, for which every point attains the objective value $+\infty$.
  See `Rockafellar.OrdinaryConvexProgram.optimalSolutions`.
* **Section 28, Lagrangian recovery** (reading). The recovery formulas determine the
  functions on $C$. See `Rockafellar.OrdinaryConvexProgram.eq_of_programLagrangian_eq`.
* **Corollary 28.3.1** (generalization). The book assumes the hypotheses of Theorem 28.2; the
  statement assumes only its conclusion, that a Kuhn–Tucker vector exists. See
  `Rockafellar.OrdinaryConvexProgram.corollary_28_3_1`.
* **Section 28, decomposition principle** (generalization). The product statements assume
  separability of $h$ in arbitrary linear block coordinates. See
  `Rockafellar.OrdinaryConvexProgram.decomposition_argmin_lagrangeFn`.
* **Section 29, graph domain** (generalization). The definition and projection formula
  apply to arbitrary bifunctions. See `Rockafellar.convexDomBifun_eq_image_graphDomain`.
* **Theorem 29.1** (generalization). $\operatorname{dom}(\inf F) = \operatorname{dom} F$ and the
  description of the Kuhn–Tucker vectors by $\partial(\inf F)(0)$ hold for every bifunction. See
  `Rockafellar.theorem_29_1` and `Rockafellar.theorem_29_1_dom`.
* **Corollaries 29.1.1 and 29.1.5** (generalization). Closedness and convexity of the
  Kuhn–Tucker set hold for arbitrary bifunctions with finite optimal value. See
  `Rockafellar.corollary_29_1_1_convex` and `Rockafellar.corollary_29_1_1_isClosed`.
* **Corollary 29.1.1**, directional derivative (reading). The source's right-hand limit
  is represented by an infimum of quotients. See `Rockafellar.corollary_29_1_1_iInf`.
* **Corollary 29.1.6**, the parenthesis (generalization). $(\inf F)(u) = +\infty$ for
  $u \notin \operatorname{dom} F$ holds for every bifunction. See
  `Rockafellar.corollary_29_1_6_top`.
* **Theorem 29.2** (generalization). Polyhedrality holds in every slice. Attainment holds
  when the optimal value exceeds $-\infty$, including the constant $+\infty$ slice. See
  `Rockafellar.theorem_29_2_argmin_nonempty`.
* **Section 29, closure of bifunctions** (generalization). Closedness of the closure
  holds for arbitrary bifunctions. See `Rockafellar.convexClBifun_closed`.
* **Corollary 29.4.1**, minimizers (generalization). The minimum-set inclusion also covers
  a negative infinite optimum. See `Rockafellar.corollary_29_4_1_argmin`.
* **Corollary 29.4.1**, perturbation clause (correction). The book states that the perturbation
  functions of $(P)$ and $(\operatorname{cl} P)$ agree near $0$ for every convex $F$ with $(P)$
  strongly consistent; this is false, with the counterexample
  `Rockafellar.corollary_29_4_1_perturbation_false`. The statement adds that $F$ is proper. See
  `Rockafellar.corollary_29_4_1_eventually`.
* **Theorem 30.1** (reading). The properness equivalence assumes closedness in Lean.
  Concavity and closedness of the convex adjoint hold for arbitrary bifunctions, and
  injectivity allows improper closed convex inputs. See `Rockafellar.theorem_30_1_proper`.
* **Theorem 30.2**, first formula and weak duality (generalization). These statements
  hold for arbitrary bifunctions. See `Rockafellar.theorem_30_2_first` and
  `Rockafellar.corollary_30_2_2_weak`.
* **Corollaries 30.2.1, 30.2.2 and 30.2.3**, first halves (generalization). The book assumes $F$
  closed; the statements do not. See `Rockafellar.corollary_30_2_1_dual`,
  `Rockafellar.corollary_30_2_2_first` and `Rockafellar.corollary_30_2_3_first`.
* **Theorem 30.3**, (a) if and only if (c) (generalization). The book assumes $F$ closed; the
  statement does not. See `Rockafellar.theorem_30_3_a_iff_c`.
* **Theorem 30.4(a), (c) and (e)** (generalization). Primal normality in these clauses
  holds without closedness of $F$.
* **Theorem 30.4(i) and (j)** (reading). The source defines optimal solutions through
  finite attainment. Lean pairs its extended-real optimizer sets with properness.
  See `Rockafellar.theorem_30_4_i` and `Rockafellar.theorem_30_4_j`.
* **Gale–Kuhn–Tucker duality** (generalization). Lean states the linear-program value
  equality for closed polyhedral convex bifunctions. See
  `Rockafellar.gale_kuhn_tucker_duality`.
* **Theorem 30.5** (reading). Lean uses extended-real optimizer sets and assumes
  finiteness explicitly. The primal-to-dual direction also drops closedness.
* **Corollary 30.5.1**, equivalences involving (a) (correction). Lean assumes properness
  to exclude improper saddle pairs with no finite-valued optima.
* **Corollary 30.5.2**, dual attainment (generalization). This direction holds without
  closedness. See `Rockafellar.corollary_30_5_2_dual`.
* **Theorem 31.1**, finiteness (generalization). The book assumes (a) and (b); the statement assumes
  only a point of $\operatorname{dom} f \cap \operatorname{dom} g$ and a point of
  $\operatorname{dom} g^* \cap \operatorname{dom} f^*$. See `Rockafellar.theorem_31_1_finite`.
* **Theorem 31.2**, properness (generalization). Only the domain and value conditions of
  properness are needed. See `Rockafellar.theorem_31_2_proper`.
* **Corollaries 31.2.1 and 31.4.1 and 31.4.2** under (a) (generalization). The book assumes $f$
  closed; the statements do not. See `Rockafellar.corollary_31_2_1_a`,
  `Rockafellar.corollary_31_4_1_a` and `Rockafellar.corollary_31_4_2_a`.
* **Theorem 31.3** (generalization). The book assumes $f$ and $g$ closed; the statement does not,
  and writes the second Kuhn–Tucker condition as $-u^* \in \partial(-g)(Ax)$. See
  `Rockafellar.theorem_31_3`.
* **Corollary 31.3.1** (generalization). The book assumes $f$ closed; the statement does not. See
  `Rockafellar.corollary_31_3_1`.
* **Theorem 31.4** under (a) (generalization). The book assumes $f$ and $K$ closed; the statement
  does not. See `Rockafellar.theorem_31_4_a`.
* **Corollary 31.4.3** (generalization). The book assumes $K$ closed; only the attainment of the
  first infimum needs it. See `Rockafellar.corollary_31_4_3` and
  `Rockafellar.corollary_31_4_3_attained`.
* **Theorem 32.1** (generalization). The book assumes $C$ convex; the statement holds for every
  $C \subseteq \operatorname{dom} f$. See `Rockafellar.theorem_32_1`.
* **Corollary 32.3.2**, finiteness of the supremum (correction). The book states that the supremum
  is finite; this fails for $f \equiv -\infty$. The statements assume $f$ proper. See
  `Rockafellar.corollary_32_3_2_finite`.
* **Corollary 32.3.2**, supremum comparison (generalization). Equality of suprema
  needs no domain containment or properness. See `Rockafellar.corollary_32_3_2_iSup`.
* **Theorem 32.4**, normality of subgradients (generalization). Neither the convexity of $f$, nor
  the convexity of $C$, nor $x \in \operatorname{ri}(\operatorname{dom} f)$ is needed. See
  `Rockafellar.theorem_32_4_normal`.
* **Corollary 32.4.1** (generalization). The pairing comparison only assumes $f$ proper
  and allows $x$ outside $S$. See `Rockafellar.corollary_32_4_1`.
* **Remark after Theorem 32.4** (correction). The full unit-ball normal cone includes zero.
  The maximizing subgradients described in the remark remain nonzero. See
  `Rockafellar.normalCone_closedBall`.

**Part VII: Saddle-Functions and Minimax Theory**

* **Theorem 33.1 and Corollary 33.1.1** (generalization). Partial conjugates and partial
  closures have the indicated closedness for arbitrary inputs.
* **Corollary 33.2.2**, exceptional case (generalization). The two infinite values require
  only failures of domain membership. See `Rockafellar.corollary_33_2_2_exceptional`.
* **Corollary 33.3.1** (generalization). Only the lower function needs an explicit
  concave-convex hypothesis for the bifunction representation.
* **Corollary 33.3.3** (generalization). The book assumes $K$ finite and jointly continuous on
  $C \times D$; the statements assume only that each section of $K$ is continuous. See
  `Rockafellar.corollary_33_3_3`.
* **Theorem 34.1** (generalization). The lower closure is lower closed and the upper closure is
  upper closed for every $K$. See `Rockafellar.theorem_34_1_lower`.
* **Theorem 34.2**, the domain clause (reading). The factor statements
  $\operatorname{dom}_1 K = \operatorname{dom} F$ and $\operatorname{dom}_2 K = \operatorname{dom}
  F^*$ assume that the other factor of $\operatorname{dom} K$ is non-empty, and $\operatorname{dom}
  K = \operatorname{dom} F \times \operatorname{dom} F^*$ assumes that $K$ is proper.
  The source also covers constant improper classes. See
  `Rockafellar.theorem_34_2_dom₁`.
* **Corollary 34.2.1**, the domain clause (reading). Lean allows nonclosed proper
  saddle-functions. The source assumes closedness and covers improper classes. See
  `Rockafellar.corollary_34_2_1_dom`.
* **Corollary 34.2.4** (generalization). The book assumes joint continuity on $C \times D$; only
  each one-variable section is assumed continuous. See `Rockafellar.corollary_34_2_4_equiv`.
* **Theorem 35.2** (reading). Lean assumes dense sampling sets in both coordinates. The
  printed qualification uses the convex hull of the closure of their product.
* **Theorems 35.6–35.10** (reading). Lean uses real-valued functions on an open product
  and tests subgradients on that product.
* **Theorem 35.7 and Corollary 35.7.1** (reading). Lean uses the maximum of the coordinate
  norms. The source uses the Euclidean product norm. See
  `Rockafellar.theorem_35_7_subdiff` and `Rockafellar.corollary_35_7_1_subdiff`.
* **Theorem 35.8 and Corollary 35.8.1** (correction). The source's §34 sign-of-$uv$
  example has a singleton subdifferential and finite partial derivatives at the origin,
  yet is infinite off the axes. Lean assumes a finite open product in Theorem 35.8 and
  omits the final clause of Corollary 35.8.1.
* **Theorem 35.10** (generalization). The book assumes differentiability on all of $C \times D$;
  only differentiability at the point is needed. See `Rockafellar.theorem_35_10`.
* **Lemma 36.1** (generalization). The book assumes $C$ and $D$ non-empty; the statement holds for
  arbitrary subsets. See `Rockafellar.lemma_36_1_on`.
* **Corollary 36.3.1** (generalization). The book assumes a closed proper saddle-function; only
  properness is needed. See `Rockafellar.corollary_36_3_1_mem_dom`.
* **Theorem 37.4** (generalization). The book assumes $K$ concave-convex; the statement has no
  hypothesis on $K$. See `Rockafellar.theorem_37_4`.
* **Corollaries 37.3.2 and 37.6.2** (reading). Concavity, convexity and continuity are read slice by
  slice, and separate continuity is weaker than joint continuity. See
  `Rockafellar.corollary_37_3_2_right` and `Rockafellar.corollary_37_6_2`.

**Part VIII: Convex Algebra**

* **Theorems 38.1 and 38.3** (generalization). The convolution domain and bracket formulas and
  the positive-scaling bracket, adjoint, and properness clauses extend beyond convex bifunctions.
  See `Rockafellar.theorem_38_1_dom` and `Rockafellar.theorem_38_3_bracket`.
* **Lemma 38.6 and the §38 cofinite criteria** (reading). The lemma assumes properness in place of
  convexity and concavity. The criteria put slice or graph properness in their hypotheses.
  See `Rockafellar.lemma_38_6` and `Rockafellar.cofinite_iff_forall_bracket_finite`.
* **Relative interior hypotheses of §38** (reading). Each condition of the form
  "$\operatorname{ri}(\operatorname{dom} \cdot)$ and $\operatorname{ri}(\operatorname{dom} \cdot)$
  have a point in common" is replaced by the conclusion of Theorem 16.4, an exact sum
  (`ConvexAnalysis.IsExactSum`), for each dual vector separately. This applies to Theorems 38.2,
  38.4, 38.5 and 38.7 and Corollaries 38.2.1, 38.4.1, 38.5.1, 38.7.1 and 38.7.2. See
  `Rockafellar.theorem_38_2`.
* **Commutativity and associativity of $\square$** (generalization). The book states them "to the
  extent that it is defined"; they hold for all bifunctions. See `Rockafellar.infConvBifun_comm'`
  and `Rockafellar.infConvBifun_assoc'`.
* **Theorem 39.3**, last assertion (generalization). The book assumes $A$ closed for both halves;
  the half for $u \in \operatorname{ri}(\operatorname{dom} A)$ does not need it. See
  `Rockafellar.theorem_39_3_relint_dom`.
* **Theorem 39.7** (generalization). The book assumes $f$ proper convex; the first assertion assumes
  only that $f$ is proper. See `Rockafellar.theorem_39_7` and `Rockafellar.theorem_39_7_attained`.
* **Theorem 39.7, attainment** (correction). Primal attainment needs a target with image
  value below $+\infty$. For the zero map and $f=0$, nonzero targets have empty fibers.
  See `Rockafellar.theorem_39_7_attained_image`.
* **Process algebra in §39** (reading). The indicator-sum image can differ from the fiber
  infimum for improperly convex functions. Oriented addition and composition allow mixed
  orientations. Theorems 39.5, 39.7, and 39.8 require exact sums in place of the source
  relative-interior conditions. See `Rockafellar.imageFn` and `Rockafellar.theorem_39_5`.

## Not formalized

**Part II: Topological Properties**

* **Theorem 6.9 for more than two sets.** Only the case of two sets is formalized, as
  `Rockafellar.theorem_6_9`.
* **Relative openness of the relative interior of an arbitrary set.**
  `Rockafellar.isRelativelyOpen_relint` assumes convexity.
* **Relative openness for a finite intersection that is empty.**
  `Rockafellar.isRelativelyOpen_iInter` assumes the intersection is nonempty.
* **Corollary 8.7.1 for an empty target sublevel.** The declaration uses the recession-cone
  characterization for a nonempty target sublevel. The empty set is bounded directly.
* **Closedness of the recession cone of an improper closed convex function.**
  `Rockafellar.isClosed_recessionConeFn_surface` uses properness.
* **Section 9, finite-family statements.** Corollaries 9.1.1, 9.1.3 and 9.2.1, Theorem 9.3,
  and Theorem 9.8 with its corollaries are stated for two inputs.
* **Corollary 9.1.3 for cones excluding the origin.** The statement uses `PointedCone`.
* **Theorem 9.2, recession formula.** The statement $(Ah)0^+ = A(h0^+)$ is omitted.
* **Section 9, attainment at $+\infty$.** Corollaries 9.2.1, 9.2.2 and 9.8.3 and Theorem 9.7
  assert attainment for each input. Their attainment declarations give witnesses at real upper
  bounds, which suffice on the effective domain.
* **Theorem 10.6, hypothesis (a) in the form of the book**, $\operatorname{conv}(\operatorname{cl}
  C') \supseteq C$. `Rockafellar.theorem_10_6_ab` assumes the stronger condition
  $\operatorname{cl} C' \supseteq C$.

**Part III: Duality Correspondences**

* **Corollary 13.3.3 for a nonclosed proper convex function.** The declarations assume $f$ closed.
* **Section 14, indicator conjugacy and bipolar closure for cones excluding zero.**
  `Rockafellar.theorem_14_1_conj` and `Rockafellar.polarCone_polarCone_rn` use `PointedCone`.
* **Section 15, existence of a norm inducing a given Minkowski metric.**
  `Rockafellar.minkowskiMetric_eq_sub` identifies the only possible norm.
* **Corollary 16.3.1**, attainment of the infimum in the exact form.
* **Corollary 16.3.2**, the equality under the relative-interior qualification.
* **Theorem 16.4 and Corollary 16.4.1**, the unconditional closure formulas for more than two
  inputs.
* **Corollary 16.4.2**, the first formula for more than two inputs and the formulas after it.
* **Theorem 16.5**, the formula without closure and attainment under the assumptions on a
  finite family with a common closed effective domain.

**Part IV: Representation and Inequalities**

* **Corollary 17.1.5**, the formula restricted to affinely independent tuples.
* **Corollary 17.2.1**, attainment of the infimum in the formula for $\operatorname{conv} f$. Only
  the closedness and properness of $\operatorname{conv} f$ are formalized.
* **Corollary 18.1.3, dimension inequality for the empty proper face.** The dimension statement
  assumes the face is nonempty.
* **Section 18, the meet of an empty family of faces.** `Rockafellar.faces_isGLB` uses
  the ambient intersection for a nonempty family. The relative meet of the empty family is $C$.
* **Corollary 19.3.4, attainment at $+\infty$.** The attainment declaration gives witnesses
  at finite values.
* **Lemmas 22.4 and 22.5, Corollary 22.4.1, and Theorems 22.6 and 22.7 (Tucker's complementarity
  theorem).** They rest on the elementary vectors of a subspace, a development of combinatorial
  matroid theory that the book presents as independent of the rest of its subject; Theorems 22.6 and
  22.7 rest also on Tucker representations, which the book describes only as a procedure.

**Part V: Differential Theory**

* **Theorem 23.4, bounded subdifferentials outside the relative interior.** The boundedness
  equivalence assumes the point lies in the relative interior.
* **The example after Theorem 23.4, the full subdifferentiability locus.** The formal example
  establishes nonconvexity.
* **Corollary 23.8.1, the weaker qualification for polyhedral sets.**
* **Theorem 24.2, the integral formula** $f(x) = \int_a^x \varphi(t)\,dt$. The existence and
  uniqueness of $f$ are formalized without it.
* **Theorem 25.4, decomposition of the exceptional set**, and the related $G_\delta$ remarks
  in Theorems 25.4 and 25.5.
* **Remark after Theorem 25.7, convergence on a dense subset.**
* **Example of p. 253, first claim**: that the function is essentially strictly convex, and in fact
  essentially smooth.

**Part VI: Constrained Extremum Problems**

* **Section 29, properness of the closure.** Only the implication from properness of $F$
  to properness of $\operatorname{cl} F$ is formalized in the surface.
* **Closedness, convexity and properness of the abnormal example** as named predicates.
* **Exact perturbation function of the normal example with no dual solution.**
  `Rockafellar.infBifun_noDualSolutionBifun_le` gives the upper bound at nonnegative inputs.

**Part VII: Saddle-Functions and Minimax Theory**

* **The exercise that every $K(u, x^*) = \langle Fu, x^* \rangle$ is simple**, for an arbitrary
  convex or concave bifunction $F$. Only the case of a closed convex $F$ with $K$ proper is
  formalized, as `Rockafellar.simpleSaddleFn_bifunBracket`.
* **Theorem 35.2, the hypothesis in the form of the book**,
  $\operatorname{conv}(\operatorname{cl}(C' \times D')) \supseteq C \times D$.
  `Rockafellar.theorem_35_2` assumes $\operatorname{cl} C' \supseteq C$ and
  $\operatorname{cl} D' \supseteq D$.
* **Corollary 35.8.1, the last clause**: finiteness of the $m + n$ two-sided partial derivatives
  implies differentiability.
* **Lemma 36.2 for a function on a general product $C \times D$.** Only the case
  $C \times D = \mathbb{R}^m \times \mathbb{R}^n$ is formalized.
* **Theorem 37.2, the formula for the support function of $C^*$.** No later result depends on it.
* **Corollary 37.4.1 for a function $K$ that is not closed.** The statements assume that $K$ is
  closed. See `Rockafellar.corollary_37_4_1_subdiff`.

**Part VIII: Convex Algebra**

* **The caveat on the product of bifunctions.** The restriction "to the extent that it is defined"
  for the multiplication of bifunctions is not discharged.
* **Lemma 38.6, the second assertion**: $\langle \operatorname{cl} f, \operatorname{cl} g \rangle$
  then exists and equals $\langle f, g \rangle$.
* **Theorem 38.7, the middle member** $-\langle f^*, F_* g \rangle$ of the chain of equalities.
* **Theorem 38.7, existence of the pairings.** The Lean equalities use selected sides of
  the Fenchel pairings.
* **Theorem 39.2, last assertion, for an infimum-oriented process.**
* **Theorem 39.3, reverse closure and relative-interior equalities**, and
  **Theorems 39.5 and 39.8, closure and adjoint-closure clauses**, for infimum-oriented
  processes.
* **The closing pages of the book.** They sketch an algebra of oriented processes and a duality for
  multivalued maps without proof; nothing there is numbered, and none of it is stated.
-/
