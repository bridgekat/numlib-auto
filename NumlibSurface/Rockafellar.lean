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

* **Theorem 1.3** (correction). The book states that every hyperplane is a set
  $\{x \mid \langle x, b \rangle = \beta\}$ with $b \neq 0$; this fails in $\mathbb{R}^0$, where the
  empty set is a hyperplane. The statement assumes $n > 0$. See `Rockafellar.theorem_1_3_exists`.
* **Theorem 2.4** (correction). The book states the theorem for every convex set $C$; for
  $C = \emptyset$ the maximum does not exist. The statement assumes $C$ non-empty. See
  `Rockafellar.theorem_2_4`.
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
* **Theorem 5.8**, functions $f$ and $h$ (generalization). The book assumes $f_1, \dots, f_m$
  proper; the statements do not. See `Rockafellar.theorem_5_8_f` and `Rockafellar.theorem_5_8_h`.

**Part II: Topological Properties**

* **Theorem 6.2**, affine hull and dimension of the closure (generalization). The book assumes $C$
  convex; the statements hold for every set. See `Rockafellar.theorem_6_2_aff_cl` and
  `Rockafellar.theorem_6_2_dim_cl`.
* **Theorem 6.6**, closure (generalization). The book assumes $C$ convex; $\operatorname{cl}(AC)
  \supseteq A(\operatorname{cl} C)$ holds for every set. See `Rockafellar.theorem_6_6_cl`.
* **Corollary 6.6.2**, closure (generalization). The book assumes $C_1, C_2$ convex; the inclusion
  holds for all sets. See `Rockafellar.corollary_6_6_2_cl`.
* **Definition of $\operatorname{cl} f$** (correction). The book asserts
  $\operatorname{epi}(\operatorname{cl} f) = \operatorname{cl}(\operatorname{epi} f)$ "by
  definition"; this fails for improper convex $f$. It holds for the lower semicontinuous hull
  without hypothesis (`ConvexAnalysis.epi_lscHull`), and for $\operatorname{cl} f$ when $f$ is
  proper. No statement uses the false identity.
* **Closedness of a proper convex function** (generalization). Closedness is lower semicontinuity
  without convexity. See `Rockafellar.closedConvex_iff_lowerSemicontinuous_of_properConvex`.
* **Closed improper convex functions** (generalization). They are the constants $\pm\infty$ without
  convexity. See `Rockafellar.closed_improper_eq_const`.
* **Theorem 8.1**, first assertion (generalization). The book assumes $C$ non-empty and convex; the
  statement holds for every set. See `Rockafellar.theorem_8_1_cone`.
* **Theorem 8.1**, second assertion (generalization). The book assumes $C$ non-empty; only convexity
  is needed. See `Rockafellar.theorem_8_1_add_subset`.
* **Theorem 8.2**, first assertion (generalization). Convexity and non-emptiness of $C$ are dropped;
  only closedness is needed. See `Rockafellar.theorem_8_2_isClosed`.
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
* **Theorem 9.1**, first conclusion (generalization). The book assumes $C$ non-empty; the statement
  does not. See `Rockafellar.theorem_9_1_closure`.
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
* **Corollary 9.8.2** (generalization). The book assumes $C_1, C_2$ non-empty and convex; only
  closedness and boundedness are needed. See `Rockafellar.corollary_9_8_2`.

**Part III: Duality Correspondences**

* **Corollary 11.5.2** (correction). The book assumes only $C \neq \mathbb{R}^n$; the statement also
  needs $C \neq \emptyset$, because for $n = 0$ the empty set is a counterexample. See
  `Rockafellar.corollary_11_5_2`.
* **Corollary 11.7.3** (correction). The book assumes only $K \neq \mathbb{R}^n$; the statement also
  needs $K \neq \emptyset$, for the same reason. See `Rockafellar.corollary_11_7_3`.
* **Theorem 12.2**, convexity and closedness of $f^*$ and $(\operatorname{cl} f)^* = f^*$
  (generalization). These clauses hold for every $f$. See `Rockafellar.theorem_12_2_convex`,
  `Rockafellar.theorem_12_2_closed` and `Rockafellar.theorem_12_2_conj_clFn`.
* **Fenchel's inequality** (generalization). It holds for every proper $f$, not only for proper
  convex $f$. See `Rockafellar.fenchel_inequality`.
* **Theorem 12.3** (generalization). The function $h$ need not be convex. See
  `Rockafellar.theorem_12_3`.
* **Theorem 13.1**, interior clause (correction). The book omits $C \neq \emptyset$; over
  $\mathbb{R}^0$ the stated condition holds for $C = \emptyset$, while
  $\operatorname{int} \emptyset = \emptyset$. See `Rockafellar.theorem_13_1_int`.
* **Theorem 13.1**, affine hull clause (generalization). The set $C$ need not be convex. See
  `Rockafellar.theorem_13_1_aff`.
* **Theorem 13.2**, $\delta(\cdot \mid C)^* = \delta^*(\cdot \mid C)$ (generalization). This holds
  for every set $C$. See `Rockafellar.theorem_13_2_conj_indicator`.
* **Theorem 13.5** (generalization). The first assertion needs $f$ closed convex but not proper, and
  the dual assertion needs no hypothesis. See `Rockafellar.theorem_13_5` and
  `Rockafellar.theorem_13_5_dual`.
* **Corollary 13.5.1** (reading). The three-case function $k$ of the book is stated as the closure
  of the homogenization `ConvexAnalysis.hom f`. See `Rockafellar.corollary_13_5_1`.
* **Corollary 13.5.1** (generalization). The function $f$ need only be convex with non-empty
  effective domain. See `Rockafellar.corollary_13_5_1`.
* **Theorem 14.1**, first assertion (generalization). The polar of every set is a non-empty closed
  convex cone. See `Rockafellar.theorem_14_1_nonempty`, `Rockafellar.theorem_14_1_convex`,
  `Rockafellar.theorem_14_1_isCone` and `Rockafellar.theorem_14_1_isClosed`.
* **Theorem 14.1**, $\delta(\cdot \mid K)^* = \delta(\cdot \mid K^\circ)$ (generalization). This
  holds for every convex cone that contains the origin, closed or not. See
  `Rockafellar.theorem_14_1_conj`.
* **Theorem 14.5**, first assertion (generalization). The polar of every set is closed, convex and
  contains the origin. See `Rockafellar.theorem_14_5_isClosed`, `Rockafellar.theorem_14_5_convex`
  and `Rockafellar.theorem_14_5_zero_mem`.
* **Theorem 14.5**, gauge of $C^\circ$ (generalization). Only $0 \in C$ is needed. See
  `Rockafellar.theorem_14_5_gauge_dual`.
* **Theorem 14.7** (generalization). The inclusions need $f \ge 0$ convex with $f(0) = 0$ but not
  closed; $f^* \ge 0$ needs only $f(0) = 0$; $f^*(0) = 0$ needs only $f \ge 0$ and $f(0) = 0$. See
  `Rockafellar.theorem_14_7_left`, `Rockafellar.theorem_14_7_right`,
  `Rockafellar.theorem_14_7_conj_nonneg` and `Rockafellar.theorem_14_7_conj_zero`.
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
* **Theorem 16.1** (generalization). For $\lambda > 0$ the book assumes $f$ proper convex; the
  formulas hold for every $f$. See `Rockafellar.theorem_16_1_left`.
* **Corollary 16.1.1** (generalization). The book assumes $C$ convex; only non-emptiness is used.
  See `Rockafellar.corollary_16_1_1`.
* **Corollary 16.1.2** (generalization). The book assumes $C$ non-empty and convex; the formula
  holds for every set. See `Rockafellar.corollary_16_1_2`.
* **Theorem 16.3**, first formula (generalization). The book assumes $f$ convex; the formula holds
  for every $f$. See `Rockafellar.theorem_16_3_image`.
* **Corollary 16.3.1**, first formula (generalization). The book assumes $C$ convex; the formula
  holds for every set. See `Rockafellar.corollary_16_3_1_image`.
* **Corollary 16.3.2**, first formula (generalization). The book assumes $C$ convex; the formula
  holds for every set. See `Rockafellar.corollary_16_3_2_image`.
* **Corollary 16.4.2** (generalization). The book assumes convex cones; convexity is not used. See
  `Rockafellar.corollary_16_4_2_add`.
* **Corollary 16.5.1**, second formula (reading). The formula fails for an empty family, so the
  index set is assumed non-empty. See `Rockafellar.corollary_16_5_1_closure`.

**Part IV: Representation and Inequalities**

* **Corollary 17.1.2** (generalization). The book assumes $x \neq 0$ and $C_i \neq \emptyset$;
  neither is needed. See `Rockafellar.corollary_17_1_2`.
* **Corollary 17.1.4** (correction). The printed statement is false; a counterexample on
  $\mathbb{R}^1$ is `Rockafellar.corollary_17_1_4_false`.
* **Corollary 17.1.6** (correction). The printed statement is false; a counterexample on
  $\mathbb{R}^1$ is `Rockafellar.corollary_17_1_6_false`.
* **Theorem 17.3** (correction). The statement needs $0 \notin S^*$, which the book omits; the
  hypotheses $S^* \neq \emptyset$ and $x^* \neq 0$ of the book are not needed. See
  `Rockafellar.theorem_17_3`.
* **Theorem 18.1** (generalization). The book assumes $D$ convex; this is not needed. See
  `Rockafellar.theorem_18_1`.
* **Theorem 18.3** (generalization). The book assumes the face $C'$ non-empty; this is not needed.
  See `Rockafellar.theorem_18_3`.
* **Corollaries 18.5.2 and 18.7.1** (generalization). The book assumes that the cone contains more
  than the origin; this is not needed. See `Rockafellar.corollary_18_5_2` and
  `Rockafellar.corollary_18_7_1`.
* **Corollary 19.3.4** (generalization). The book assumes the two functions proper; this is not
  needed. See `Rockafellar.corollary_19_3_4`.
* **Theorem 20.4** (generalization). The book assumes $C$ non-empty and convex; neither is needed.
  See `Rockafellar.theorem_20_4`.
* **Comments and References for Part IV** (typo). The book cites a "Corollary 21.3.3", which does
  not exist; the intended reference is Corollary 21.3.2, Helly's theorem.

**Part V: Differential Theory**

* **Theorem 23.1** (generalization). Positive homogeneity of $f'(x; \cdot)$ holds for every $f$ and
  $x$, and $f'(x; 0) = 0$ holds without convexity. See `Rockafellar.theorem_23_1_posHomogeneous` and
  `Rockafellar.theorem_23_1_zero`.
* **Theorem 23.2** (generalization). The equivalence holds without convexity of $f$. See
  `Rockafellar.theorem_23_2`.
* **Theorem 23.4**, first assertion (generalization). $\partial f(x) = \emptyset$ for
  $x \notin \operatorname{dom} f$ holds for every proper $f$. See
  `Rockafellar.theorem_23_4_notMem_dom`.
* **Theorem 23.5** (generalization). Conditions (a), (b) and (c) are equivalent for every $f$, and
  (d) needs only properness. See `Rockafellar.theorem_23_5_b`.
* **Corollary 23.5.1** (generalization). The book assumes $f$ closed proper convex; properness is
  not needed. See `Rockafellar.corollary_23_5_1`.
* **Corollary 23.5.2** (generalization). Properness is not needed. See
  `Rockafellar.corollary_23_5_2_clFn` and `Rockafellar.corollary_23_5_2_subdifferential`.
* **Corollary 23.5.4** (generalization). The book assumes $K$ non-empty and closed; neither is
  needed. See `Rockafellar.corollary_23_5_4`.
* **Corollary 23.8.1** (reading). The hypothesis $x \in C_i$ is added, because the normal cone of
  the library is defined at every point, while the normal cone of the book is empty off $C$. See
  `Rockafellar.corollary_23_8_1`.
* **Theorem 24.1** (generalization). Monotonicity, finiteness and the interlacing inequalities hold
  without closedness of $f$, and the finiteness clause is an equivalence. See
  `Rockafellar.theorem_24_1_finite_iff`.
* **Remark after Theorem 24.1** (generalization). The formula for $\partial f(x)$ needs only
  properness of $f$. See `Rockafellar.theorem_24_1_subdifferential`.
* **Theorem 24.6** (generalization). Closedness of $f$ is not assumed. See
  `Rockafellar.theorem_24_6_lt`.
* **Theorem 24.7** (reading). The Lipschitz constant is some bound $\alpha$ on the subgradients over
  $S$, not necessarily $\sup\{|x^*| \mid x^* \in \partial f(S)\}$. See
  `Rockafellar.theorem_24_7_bound`.
* **Theorem 25.3**, continuity and monotonicity (generalization). The right derivative, defined on
  all of $\mathbb{R}$, is continuous at each point of $D$ and non-decreasing on $\mathbb{R}$. See
  `Rockafellar.theorem_25_3_continuousAt` and `Rockafellar.theorem_25_3_monotone`.
* **Theorem 25.4**, first assertion (generalization). The book assumes $y \neq 0$; the statement
  also holds for $y = 0$. See `Rockafellar.theorem_25_4_continuousAt_iff`.
* **Theorem 25.6** (reading). The book sets $K(x) = \emptyset$ for $x \notin \operatorname{dom} f$;
  here $K(x)$ is the normal cone, defined at every $x$. See `Rockafellar.theorem_25_6`.
* **Theorem 25.7** (generalization). The book assumes differentiability on $C$; the pointwise
  statement uses differentiability at $x$ only. See `Rockafellar.theorem_25_7`.
* **Theorem 26.4** (generalization). The book assumes $f$ closed proper and differentiable on a
  non-empty $C$; the well-definedness of $g$ and $g = f^*$ on $D$ need only convexity, and
  $D \subseteq \operatorname{dom} f^*$ needs in addition only differentiability on $C$. See
  `Rockafellar.theorem_26_4_wellDefined`, `Rockafellar.theorem_26_4_eq` and
  `Rockafellar.theorem_26_4_subset_dom_conj`.
* **Theorem 26.5** (reading). The book says closed convex function, and its proof needs a closed
  proper one; here $f$ is assumed proper. See `Rockafellar.theorem_26_5`.

**Part VI: Constrained Extremum Problems**

* **Theorem 27.1(a)** (generalization). The book assumes $f$ closed proper convex; clause (a) holds
  for every function. See `Rockafellar.theorem_27_1_a` and `Rockafellar.theorem_27_1_a_bddBelow`.
* **Theorem 27.1(b)**, first two sentences (generalization). Properness is not needed. See
  `Rockafellar.theorem_27_1_b` and `Rockafellar.theorem_27_1_b_attained`.
* **Theorem 27.1(g)**, first sentence (generalization). Properness is not needed. See
  `Rockafellar.theorem_27_1_g_setOf_le`.
* **Theorem 27.4**, sufficiency (generalization). No hypothesis on $h$ or $C$ is needed, and $x$
  need not lie in $C$. See `Rockafellar.theorem_27_4_sufficient`.
* **Corollary 28.3.1** (generalization). The book assumes the hypotheses of Theorem 28.2; the
  statement assumes only its conclusion, that a Kuhn–Tucker vector exists. See
  `Rockafellar.OrdinaryConvexProgram.corollary_28_3_1`.
* **Theorem 29.1** (generalization). $\operatorname{dom}(\inf F) = \operatorname{dom} F$ and the
  description of the Kuhn–Tucker vectors by $\partial(\inf F)(0)$ hold for every bifunction. See
  `Rockafellar.theorem_29_1` and `Rockafellar.theorem_29_1_dom`.
* **Corollary 29.1.6**, the parenthesis (generalization). $(\inf F)(u) = +\infty$ for
  $u \notin \operatorname{dom} F$ holds for every bifunction. See
  `Rockafellar.corollary_29_1_6_top`.
* **Theorem 29.2**, existence of an optimal solution (generalization). The book assumes a finite
  optimal value; the statement assumes only that it is not $-\infty$. See
  `Rockafellar.theorem_29_2_argmin_nonempty`.
* **Corollary 29.4.1**, perturbation clause (correction). The book states that the perturbation
  functions of $(P)$ and $(\operatorname{cl} P)$ agree near $0$ for every convex $F$ with $(P)$
  strongly consistent; this is false, with the counterexample
  `Rockafellar.corollary_29_4_1_perturbation_false`. The statement adds that $F$ is proper. See
  `Rockafellar.corollary_29_4_1_eventually`.
* **Corollaries 30.2.1, 30.2.2 and 30.2.3**, first halves (generalization). The book assumes $F$
  closed; the statements do not. See `Rockafellar.corollary_30_2_1_dual`,
  `Rockafellar.corollary_30_2_2_first` and `Rockafellar.corollary_30_2_3_first`.
* **Theorem 30.3**, (a) if and only if (c) (generalization). The book assumes $F$ closed; the
  statement does not. See `Rockafellar.theorem_30_3_a_iff_c`.
* **Theorem 30.4(i)** (correction). The book obtains (i) from (g), which needs $F0$ proper; the
  statement assumes that $F0$ is proper. See `Rockafellar.theorem_30_4_i`.
* **Theorem 30.4(j)** (correction). The book obtains (j) from (h), which needs $F^* 0$ proper; the
  statement assumes that $F^* 0$ is proper. See `Rockafellar.theorem_30_4_j`.
* **Theorem 31.1**, finiteness (generalization). The book assumes (a) and (b); the statement assumes
  only a point of $\operatorname{dom} f \cap \operatorname{dom} g$ and a point of
  $\operatorname{dom} g^* \cap \operatorname{dom} f^*$. See `Rockafellar.theorem_31_1_finite`.
* **Theorem 31.2**, properness (generalization). No relative-interior hypothesis is needed. See
  `Rockafellar.theorem_31_2_proper`.
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
* **Theorem 32.4**, normality of subgradients (generalization). Neither the convexity of $f$, nor
  the convexity of $C$, nor $x \in \operatorname{ri}(\operatorname{dom} f)$ is needed. See
  `Rockafellar.theorem_32_4_normal`.
* **Corollary 32.4.1** (generalization). The function $f$ is assumed proper but not convex. See
  `Rockafellar.corollary_32_4_1`.

**Part VII: Saddle-Functions and Minimax Theory**

* **Corollary 33.3.3** (generalization). The book assumes $K$ finite and jointly continuous on
  $C \times D$; the statements assume only that each section of $K$ is continuous. See
  `Rockafellar.corollary_33_3_3`.
* **Theorem 34.1** (generalization). The lower closure is lower closed and the upper closure is
  upper closed for every $K$. See `Rockafellar.theorem_34_1_lower`.
* **Theorem 34.2**, the domain clause (correction). The factor statements
  $\operatorname{dom}_1 K = \operatorname{dom} F$ and $\operatorname{dom}_2 K = \operatorname{dom}
  F^*$ assume that the other factor of $\operatorname{dom} K$ is non-empty, and $\operatorname{dom}
  K = \operatorname{dom} F \times \operatorname{dom} F^*$ assumes that $K$ is proper. See
  `Rockafellar.theorem_34_2_dom₁`.
* **Corollary 34.2.1**, the domain clause (generalization). The book assumes $K$ closed; the
  equality of the effective domains does not need it. See `Rockafellar.corollary_34_2_1_dom`.
* **Corollary 34.2.4** (generalization). The book assumes joint continuity on $C \times D$; only
  each one-variable section is assumed continuous. See `Rockafellar.corollary_34_2_4_equiv`.
* **Theorems 35.6–35.10** (reading). The book takes $K$ with values in $[-\infty, +\infty]$, finite
  on the open set $C \times D$; here $K$ is real-valued and concave-convex on $C \times D$. See
  `Rockafellar.saddleSubdifferentialOn_univ_eq`.
* **Theorem 35.7 and Corollary 35.7.1** (reading). The ball $B$ is the unit ball of the supremum
  norm, not the Euclidean unit ball; the statements are equivalent. See
  `Rockafellar.theorem_35_7_subdiff` and `Rockafellar.corollary_35_7_1_subdiff`.
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

* **Theorem 38.1** (typo). The book prints $\operatorname{dom}(F_1 \cap F_2)$ on the left-hand side
  of the domain formula; the operation meant is $\square$. See `Rockafellar.theorem_38_1_dom`.
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

## Not formalized

**Part II: Topological Properties**

* **Theorem 6.9 for more than two sets.** Only the case of two sets is formalized, as
  `Rockafellar.theorem_6_9`.
* **Theorem 10.6, hypothesis (a) in the form of the book**, $\operatorname{conv}(\operatorname{cl}
  C') \supseteq C$. `Rockafellar.theorem_10_6_ab` assumes the stronger condition
  $\operatorname{cl} C' \supseteq C$.

**Part III: Duality Correspondences**

* **Corollary 16.3.1**, attainment of the infimum in the exact form.
* **Corollary 16.3.2**, second formula as an equality. Only the inclusion is formalized.
* **Corollary 16.4.2**, the formulas after the first.
* **Corollary 16.5.2**, second formula as an equality. Only the inclusion is formalized.

**Part IV: Representation and Inequalities**

* **Corollary 17.2.1**, attainment of the infimum in the formula for $\operatorname{conv} f$. Only
  the closedness and properness of $\operatorname{conv} f$ are formalized.
* **Lemmas 22.4 and 22.5, Corollary 22.4.1, and Theorems 22.6 and 22.7 (Tucker's complementarity
  theorem).** They rest on the elementary vectors of a subspace, a development of combinatorial
  matroid theory that the book presents as independent of the rest of its subject; Theorems 22.6 and
  22.7 rest also on Tucker representations, which the book describes only as a procedure.

**Part V: Differential Theory**

* **Theorem 24.2, the integral formula** $f(x) = \int_a^x \varphi(t)\,dt$. The existence and
  uniqueness of $f$ are formalized without it.
* **Example of p. 253, first claim**: that the function is essentially strictly convex, and in fact
  essentially smooth.

**Part VI: Constrained Extremum Problems**

* **Convexity of the abnormal example.** The book calls `Rockafellar.abnormalBifun` a closed proper
  convex bifunction; this is not proved.

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
* **Theorems 39.5, 39.7 and 39.8 under the relative-interior conditions of the book.** The
  formalized versions assume an exact-sum condition, which is strictly stronger.
* **Theorem 39.2, last assertion, for an infimum-oriented process.**
* **The closing pages of the book.** They sketch an algebra of oriented processes and a duality for
  multivalued maps without proof; nothing there is numbered, and none of it is stated.
-/
