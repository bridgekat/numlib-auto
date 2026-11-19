/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Module.HahnBanach
import Numlib.Analysis.Convex.Continuity
import Numlib.Analysis.Sobolev.Boundary.PolygonTrace
import Numlib.FiniteElement.BoundaryInterpolation
import Numlib.MeasureTheory.Function.LpSpace.Duality
import Numlib.Variational.Inequality.Approximation
import Numlib.Variational.Inequality.Multiplier
import NumlibSurface.AtkinsonHan.Chapter10.Section04
import NumlibSurface.AtkinsonHan.Chapter11.Section03

/-!
# Atkinson and Han, Section 11.4: Numerical approximation of elliptic variational inequalities

This module formalizes Section 11.4 of [han2009theoretical]. The discrete problem (11.4.3) is the
variational inequality (11.3.3) of Section 11.3 with the constraint set $K$ replaced by a set $K_h$,
so it uses the same predicate `AtkinsonHan.Chapter11.IsVariationalInequalitySolution`, and its
unique solvability is Theorem 11.3.1 again. The section adds the error analysis. With the residual
of the continuous solution $u$,
$$R(v, w) = (A u, v - w) + j(v) - j(w) - (f, v - w),$$
Falk's lemma (Theorem 11.4.2) bounds $\frac{c_0}{2} \|u - u_h\|^2$ by $\inf_{v \in K} R(v, u_h) +
\inf_{v_h \in K_h} \bigl[R(v_h, u) + \frac{M^2}{2 c_0} \|u - v_h\|^2\bigr]$. Theorem 11.4.1 and
Exercise 11.4.2 give convergence $u_h \to u$, Theorems 11.4.6 and 11.4.7 treat a discrete functional
$j_h$ that replaces $j$, and Exercise 11.4.3 bounds the error of a regularized functional.

Examples 11.4.3 and 11.4.4 apply Falk's lemma to the obstacle problem and to the simplified friction
problem, discretized with linear elements on a polygon, and give the estimate
$\|u - u_h\|_{H^1(\Omega)} \le c h$. Theorem 11.4.5 characterizes the solution of the friction
problem by a Lagrange multiplier $\lambda \in L^\infty(\Gamma)$ with $|\lambda| \le 1$. The abstract
results specialize `Numlib.Variational.Inequality.Approximation`, the multiplier specializes
`Numlib.Variational.Inequality.Multiplier`, and the examples use the linear element of
`Numlib.Geometry.Triangulation` and Theorem 10.3.9 (`AtkinsonHan.Chapter10.theorem_10_3_9_linear`).

## Main definitions

* Display before (11.4.7), `AtkinsonHan.Chapter11.residual`: the residual $R(v, w) = (A u, v - w) +
  j_1(v) - j_2(w) - (f, v - w)$.
* Example 11.4.3, `AtkinsonHan.Chapter11.discreteObstacleSet`: the continuous piecewise linear
  $v_h \in H^1_0(\Omega)$ with $v_h \ge \psi$ at every node.
* Example 11.4.4, `AtkinsonHan.Chapter11.weakLaplacian`,
  `AtkinsonHan.Chapter11.frictionResidualData` and `AtkinsonHan.Chapter11.normalTraceL`: the weak
  Laplacian $\Delta u$, the function $-\Delta u + u - f$, and the normal derivative
  $\partial u / \partial \nu \in L^2(\Gamma)$ of $u \in H^2(\Omega)$.

## Main results

* Theorem 11.4.1, `AtkinsonHan.Chapter11.theorem_11_4_1`: if the sets $K_h$ approximate $K$, the
  discrete solutions converge in norm to $u$.
* Theorem 11.4.2, `AtkinsonHan.Chapter11.theorem_11_4_2` (Falk's lemma): the squared error bound
  (11.4.7).
* Theorem 11.4.2, `AtkinsonHan.Chapter11.theorem_11_4_2_of_subset`: for $K_h \subseteq K$, $\|u -
  u_h\| \le c \inf_{v_h \in K_h} (\|u - v_h\| + |R(v_h, u)|^{1/2})$.
* Example 11.4.3, `AtkinsonHan.Chapter11.example_11_4_3`: the linear element approximation of the
  obstacle problem on a polygon has error $\|u - u_h\|_{H^1(\Omega)} \le c h$.
* Example 11.4.4, `AtkinsonHan.Chapter11.example_11_4_4`: the linear element approximation of the
  simplified friction problem on a polygon has error $\|u - u_h\|_{H^1(\Omega)} \le c h$.
* Theorem 11.4.5, `AtkinsonHan.Chapter11.theorem_11_4_5`: $u$ solves the friction problem (11.4.10)
  if and only if there is a multiplier $\lambda \in L^\infty(\Gamma)$, $|\lambda| \le 1$, with
  (11.4.21) and (11.4.22).
* Theorem 11.4.5, `AtkinsonHan.Chapter11.theorem_11_4_5_unique`: the multiplier is unique.
* Theorem 11.4.6, `AtkinsonHan.Chapter11.theorem_11_4_6`: the method of numerical integration
  (11.4.25) converges.
* Theorem 11.4.7, `AtkinsonHan.Chapter11.theorem_11_4_7`: if $j_h \ge j$ on $K_h$, the error bound
  (11.4.27) holds with the residual measured by $j_h$.
* Exercise 11.4.2, `AtkinsonHan.Chapter11.exercise_11_4_2`: internal approximations by nested
  subspaces with dense union converge, without weak compactness.
* Exercise 11.4.3, `AtkinsonHan.Chapter11.exercise_11_4_3`: the a priori bound (11.4.20) $\|u -
  u_\varepsilon\| \le \sqrt{2 c_1 \varepsilon / c_0}$ for a regularized functional.

## Implementation notes

* `AtkinsonHan.Chapter11.residual` keeps the functionals at its two arguments separate, so that it
  serves both the $R$ of (11.4.7) and the $R_h$ of (11.4.27).
* The boundedness of the discrete solutions in Theorems 11.4.1 and 11.4.6 is not a hypothesis. It
  follows from Falk's lemma at $v = u$ together with a continuous affine minorant of $j$.
* The source extends the functional $\ell - a(u, \cdot)$ in Theorem 11.4.5 from $H^{1/2}(\Gamma)$ to
  $L^1(\Gamma)$ by the Hahn–Banach theorem, and uses the density of $H^{1/2}(\Gamma)$ in
  $L^2(\Gamma)$ for the uniqueness. Here the functional is extended from the subspace of traces in
  $L^1(\Gamma)$, with the Riesz representation $(L^1)' = L^\infty$, and the uniqueness uses the
  traces of the smooth compactly supported functions. No fractional Sobolev space is used.
* In Example 11.4.4 each triangulation carries its own surface measure on $\Gamma$,
  `Triangulation.boundaryMeasure`, and its own trace. Therefore the friction functional and the
  continuous problem are stated for each mesh.

## Deviations from the source

* **Theorems 11.4.2 and 11.4.7** (reading). The square-root bounds give the explicit constant
  $c = \max\{M/c_0, \sqrt{2/c_0}\}$. Theorem 11.4.7 allows any discrete admissible set;
  the book uses a subspace. The squared estimate (11.4.7) retains the printed form.
* **Exercise 11.4.3** (generalization). The regularization estimate uses a strongly monotone
  operator in place of the elliptic bilinear form and assumes the uniform functional error bound.
* **Theorems 11.4.1 and 11.4.6** (restriction). The weak-limit hypotheses are required along
  every reindexing, including constant ones. The proofs need subsequences tending to infinity.
  Constant reindexing forces $K_n \subseteq K$ in Theorem 11.4.1 and $j \le j_n$ on $V_n$ in
  Theorem 11.4.6 for every $n$. See `AtkinsonHan.Chapter11.theorem_11_4_1`.
* **Theorem 11.4.6** (reading). The condition $\liminf_h j_h(v_h) \ge j(v)$ is stated as: for every
  $\alpha < j(v)$, eventually $j_h(v_h) > \alpha$. See `AtkinsonHan.Chapter11.theorem_11_4_6`.
* **Theorem 11.4.6** (generalization). The finite dimension of the spaces $V_h$ and the convexity
  and lower semicontinuity of the $j_h$, which only make the discrete problems solvable, are not
  assumed; the discrete solutions are given. See `AtkinsonHan.Chapter11.theorem_11_4_6`.
* **Exercise 11.4.2** (correction). The source asks only that the union of the subspaces $V_h$ be
  dense. This does not give a point of every $V_h$ near $u$, so the library also asks that the $V_h$
  be nested. See `AtkinsonHan.Chapter11.exercise_11_4_2`.
* **Example 11.4.3** (reading). The regularity $u, \psi \in H^2(\Omega)$, the boundary conditions
  $u = 0$ and $\psi \le 0$ on $\Gamma$, and $-\Delta u \in L^2(\Omega)$ are hypotheses on
  representatives continuous on $\overline\Omega$. The polygon is a triangulated domain whose
  boundary is a union of element edges. See `AtkinsonHan.Chapter11.example_11_4_3`.
* **Example 11.4.4** (reading). The regularity $u \in H^2(\Omega)$ and
  $u|_{\Gamma_k} \in H^2(\Gamma_k)$ on every side is stated through explicit representatives. The
  polygon is stated by the condition that every boundary edge lies on one of finitely many sides,
  and $\|\partial u/\partial\nu\|_{L^2(\Gamma)}$ and $\sqrt{\operatorname{meas} \Gamma}$ are assumed
  bounded uniformly in $h$. See `AtkinsonHan.Chapter11.example_11_4_4`.
* **Theorem 11.4.5** (reading). The Lipschitz domain of the source is a domain with a boundary trace
  in the sense of `BoundaryData.TraceFamily`, for example a bounded $C^1$ domain or a polygon
  without slits. See `AtkinsonHan.Chapter11.theorem_11_4_5`.

## Not formalized

* **Exercise 11.4.4** (the proof of Theorem 11.4.5 through the regularization (11.4.14)).
* **The analysis of (11.4.29)**, the method of numerical integration for the friction problem. It
  needs the quadrature functional $j_h$ on the boundary.
* **Exercises 11.4.1 and 11.4.5.** They name a domain.
-/

open Filter Set Topology
open scoped InnerProductSpace

namespace AtkinsonHan.Chapter11

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- **Display before (11.4.7)** of [han2009theoretical], the residual. Let $V$ be a real Hilbert
space, $A \colon V \to V$, $j_1, j_2 \colon V \to \mathbb{R}$ and $f, u \in V$. The **residual**
of $u$ at $(v, w)$ is
$$R(v, w) = (A u, v - w) + j_1(v) - j_2(w) - (f, v - w).$$

The $R$ of the source is the case $j_1 = j_2 = j$, and the $R_h$ of (11.4.27) is the case
$j_1 = j_h$, $j_2 = j$. For a variational equation, with $j = 0$, $K$ a subspace and
$v, w \in K$, the residual of the solution vanishes; this is why Falk's lemma contains Céa's
lemma. -/
def residual (A : V → V) (j₁ j₂ : V → ℝ) (f u v w : V) : ℝ :=
  ⟪A u, v - w⟫_ℝ + j₁ v - j₂ w - ⟪f, v - w⟫_ℝ

section

variable {A : V → V} {c₀ M : ℝ} {j jh : V → ℝ} {f u uh : V} {K Kh : Set V}

/-- The constant $c = \max\{M/c_0, \sqrt{2/c_0}\}$ of the square-rooted error bounds (11.4.7) and
(11.4.27). -/
private noncomputable def falkConst (c₀ M : ℝ) : ℝ := max (M / c₀) (Real.sqrt (2 / c₀))

/-- The constant $\max\{M/c_0, \sqrt{2/c_0}\}$ is nonnegative for $c_0 > 0$ and $M \ge 0$. -/
private theorem falkConst_nonneg (hc₀ : 0 < c₀) (hM : 0 ≤ M) : 0 ≤ falkConst c₀ M :=
  le_max_of_le_left (div_nonneg hM hc₀.le)

/-- If $e, d \ge 0$ and $\frac{c_0}{2} e^2 \le R + \frac{M^2}{2 c_0} d^2$, then
$e \le c (d + \sqrt{|R|})$ with $c = \max\{M/c_0, \sqrt{2/c_0}\}$. -/
private theorem norm_le_falkConst (hc₀ : 0 < c₀) (hM : 0 ≤ M) {e d R : ℝ} (he : 0 ≤ e)
    (hd : 0 ≤ d) (h : c₀ / 2 * e ^ 2 ≤ R + M ^ 2 / (2 * c₀) * d ^ 2) :
    e ≤ falkConst c₀ M * (d + Real.sqrt |R|) := by
  have hcM : M / c₀ ≤ falkConst c₀ M := le_max_left _ _
  have hcS : Real.sqrt (2 / c₀) ≤ falkConst c₀ M := le_max_right _ _
  have hS0 : (0 : ℝ) ≤ Real.sqrt (2 / c₀) := Real.sqrt_nonneg _
  have hSsq : Real.sqrt (2 / c₀) ^ 2 = 2 / c₀ := Real.sq_sqrt (by positivity)
  have hR : R ≤ |R| := le_abs_self R
  have hRs : Real.sqrt |R| ^ 2 = |R| := Real.sq_sqrt (abs_nonneg R)
  have hRs0 : (0 : ℝ) ≤ Real.sqrt |R| := Real.sqrt_nonneg _
  have hc : 0 ≤ falkConst c₀ M := falkConst_nonneg hc₀ hM
  -- `e² ≤ (2/c₀) |R| + (M/c₀)² d² ≤ c² (√|R| + d)²`
  have hsq : e ^ 2 ≤ (falkConst c₀ M * (d + Real.sqrt |R|)) ^ 2 := by
    have habs : c₀ / 2 * e ^ 2 ≤ |R| + M ^ 2 / (2 * c₀) * d ^ 2 := by linarith
    have h1 : e ^ 2 ≤ 2 / c₀ * |R| + (M / c₀) ^ 2 * d ^ 2 := by
      have hc0 : c₀ ≠ 0 := ne_of_gt hc₀
      have he2 : (2 / c₀) * (c₀ / 2 * e ^ 2) = e ^ 2 := by field_simp
      have hd2 : (2 / c₀) * (|R| + M ^ 2 / (2 * c₀) * d ^ 2)
          = 2 / c₀ * |R| + (M / c₀) ^ 2 * d ^ 2 := by field_simp
      calc e ^ 2 = (2 / c₀) * (c₀ / 2 * e ^ 2) := he2.symm
        _ ≤ (2 / c₀) * (|R| + M ^ 2 / (2 * c₀) * d ^ 2) :=
            mul_le_mul_of_nonneg_left habs (by positivity)
        _ = _ := hd2
    have h2 : 2 / c₀ * |R| ≤ falkConst c₀ M ^ 2 * Real.sqrt |R| ^ 2 := by
      rw [hRs, ← hSsq]
      exact mul_le_mul_of_nonneg_right (by nlinarith) (abs_nonneg R)
    have h3 : (M / c₀) ^ 2 * d ^ 2 ≤ falkConst c₀ M ^ 2 * d ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith [div_nonneg hM hc₀.le]) (sq_nonneg d)
    nlinarith [mul_nonneg (mul_nonneg hc hc) (mul_nonneg hd hRs0)]
  calc e = Real.sqrt (e ^ 2) := (Real.sqrt_sq he).symm
    _ ≤ Real.sqrt ((falkConst c₀ M * (d + Real.sqrt |R|)) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = falkConst c₀ M * (d + Real.sqrt |R|) :=
        Real.sqrt_sq (mul_nonneg hc (by positivity))

/-! ### Theorem 11.4.1: convergence for approximating constraint sets -/

/-- **Theorem 11.4.1** of [han2009theoretical]. Let $V$ be a real Hilbert space and let
$K \subseteq V$ be convex. Let $A \colon V \to V$ be strongly monotone with constant $c_0 > 0$
and Lipschitz continuous with constant $M \ge 0$, and let $j \colon V \to \mathbb{R}$ be convex
and continuous on $V$. Let $(K_n)_{n \in \mathbb{N}}$ be subsets of $V$ such that

* (a) every $v \in K$ is the limit of a sequence $w_n \in K_n$, and
* (b) for every $\sigma \colon \mathbb{N} \to \mathbb{N}$ and every sequence
  $v_k \in K_{\sigma(k)}$ that converges weakly to $z$, $z \in K$.

Let $u$ solve the variational inequality (11.3.3) over $K$ with datum $f$, and let $u_n$ solve
it over $K_n$, which is (11.4.3). Then $u_n \to u$ in norm.

**Reading.** Hypothesis (b) is required along every reindexing $\sigma$, because the proof
passes to a subsequence.

The source's (11.4.2) asks that $j$ be the restriction to $K$ of a convex continuous functional
on $V$; here $j$ is that functional. Weak convergence is written as $(v_k, y) \to (z, y)$ for
every $y \in V$. The source proves separately that the $u_n$ are bounded; here this follows from
Falk's lemma at $v = u$ and an affine minorant of $j$. For an internal approximation,
$K_n \subseteq K$, hypothesis (b) holds automatically and no weak compactness is needed; that is
`AtkinsonHan.Chapter11.exercise_11_4_2`. -/
theorem theorem_11_4_1 {Kh : ℕ → Set V} {uh : ℕ → V} (hc₀ : 0 < c₀) (hM : 0 ≤ M)
    (hmono : Chapter05.StronglyMonotoneWith A c₀)
    (hlip : ∀ v₁ v₂ : V, ‖A v₁ - A v₂‖ ≤ M * ‖v₁ - v₂‖) (hKcv : Convex ℝ K)
    (hjcv : ConvexOn ℝ univ j) (hjc : Continuous j)
    (happrox : ∀ v ∈ K, ∃ w : ℕ → V, (∀ n, w n ∈ Kh n) ∧ Tendsto w atTop (𝓝 v))
    (hweak : ∀ (σ : ℕ → ℕ) (v : ℕ → V) (z : V), (∀ k, v k ∈ Kh (σ k)) →
      (∀ y : V, Tendsto (fun k => ⟪v k, y⟫_ℝ) atTop (𝓝 ⟪z, y⟫_ℝ)) → z ∈ K)
    (hu : IsVariationalInequalitySolution A j f K u)
    (huh : ∀ n, IsVariationalInequalitySolution A j f (Kh n) (uh n)) :
    Tendsto uh atTop (𝓝 u) :=
  tendsto_of_isVariationalInequalitySolution hc₀ hmono
    ((Chapter05.lipschitzWith_toNNReal_iff hM).1 hlip) hKcv hjcv hjc happrox hweak hu huh

/-! ### Theorem 11.4.2: Falk's generalized Céa lemma -/

/-- **Theorem 11.4.2** of [han2009theoretical] (Falk's lemma), the estimate (11.4.7). Let $V$ be a
real Hilbert space and let $K, K_h \subseteq V$. Let $A \colon V \to V$ be strongly monotone
with constant $c_0 > 0$ and Lipschitz continuous with constant $M \ge 0$, and let
$j \colon V \to \mathbb{R}$ and $f \in V$. Let $u$ solve the variational inequality (11.3.3)
over $K$ and $u_h$ solve it over $K_h$. With the residual $R(v, w) = (A u, v - w) + j(v) -
j(w) - (f, v - w)$,
$$\frac{c_0}{2} \|u - u_h\|^2 \le \inf_{v \in K} R(v, u_h) + \inf_{v_h \in K_h} \Bigl[R(v_h,
  u) + \frac{M^2}{2 c_0} \|u - v_h\|^2\Bigr].$$

The displayed estimate is the book's squared form (11.4.7). The square-rooted
form for $K_h \subseteq K$ is `AtkinsonHan.Chapter11.theorem_11_4_2_of_subset`.

The proof adds the two variational inequalities to the strong monotonicity inequality and treats
the cross term by the Cauchy–Schwarz inequality, the Lipschitz bound and Young's inequality. It
uses no closedness, convexity or topology, and $K_h$ need not meet $K$. The infima are taken in
$\mathbb{R}$ over nonempty sets, and the two variational inequalities bound both sets from
below. For a variational equation, with $K$ a subspace, $j = 0$ and $K_h \subseteq K$, both
residuals vanish and the estimate is Céa's lemma, `AtkinsonHan.Chapter09.proposition_9_1_3`. -/
theorem theorem_11_4_2 (hc₀ : 0 < c₀) (hM : 0 ≤ M) (hmono : Chapter05.StronglyMonotoneWith A c₀)
    (hlip : ∀ v₁ v₂ : V, ‖A v₁ - A v₂‖ ≤ M * ‖v₁ - v₂‖)
    (hu : IsVariationalInequalitySolution A j f K u)
    (huh : IsVariationalInequalitySolution A j f Kh uh) :
    c₀ / 2 * ‖u - uh‖ ^ 2 ≤ (⨅ v : K, residual A j j f u v uh)
      + ⨅ vh : Kh, (residual A j j f u vh u + M ^ 2 / (2 * c₀) * ‖u - vh‖ ^ 2) := by
  have hKne : Nonempty K := ⟨⟨u, hu.1⟩⟩
  have hKhne : Nonempty Kh := ⟨⟨uh, huh.1⟩⟩
  have hfalk : ∀ (v : K) (vh : Kh), c₀ / 2 * ‖u - uh‖ ^ 2 ≤ residual A j j f u v uh
      + (residual A j j f u vh u + M ^ 2 / (2 * c₀) * ‖u - vh‖ ^ 2) := by
    intro v vh
    have h := norm_sub_le_of_isVariationalInequalitySolution hc₀ hmono
      ((Chapter05.lipschitzWith_toNNReal_iff hM).1 hlip) hu huh v.2 vh.2
    simp only [residual]
    linarith
  have h₁ : ∀ v : K, c₀ / 2 * ‖u - uh‖ ^ 2 - residual A j j f u v uh
      ≤ ⨅ vh : Kh, (residual A j j f u vh u + M ^ 2 / (2 * c₀) * ‖u - vh‖ ^ 2) :=
    fun v => le_ciInf fun vh => by linarith [hfalk v vh]
  have h₂ : c₀ / 2 * ‖u - uh‖ ^ 2
      - ⨅ vh : Kh, (residual A j j f u vh u + M ^ 2 / (2 * c₀) * ‖u - vh‖ ^ 2)
      ≤ ⨅ v : K, residual A j j f u v uh :=
    le_ciInf fun v => by linarith [h₁ v]
  linarith

/-- **Theorem 11.4.2** of [han2009theoretical], the internal approximation form after the theorem.
Under the hypotheses of `AtkinsonHan.Chapter11.theorem_11_4_2`, assume also $K_h \subseteq K$.
Then
$$\|u - u_h\| \le c \inf_{v_h \in K_h} \Bigl(\|u - v_h\| + |R(v_h, u)|^{1/2}\Bigr), \qquad c =
  \max\Bigl\{\frac{M}{c_0}, \sqrt{\frac{2}{c_0}}\Bigr\}.$$

The first residual of Falk's lemma vanishes at $v = u_h$. The source leaves the constant
unnamed; it is written out here because taking the square root of a sum of two squares fixes it.

**Reading.** Writes out the previously unspecified constant in the square-root bound.
-/
theorem theorem_11_4_2_of_subset (hc₀ : 0 < c₀) (hM : 0 ≤ M)
    (hmono : Chapter05.StronglyMonotoneWith A c₀)
    (hlip : ∀ v₁ v₂ : V, ‖A v₁ - A v₂‖ ≤ M * ‖v₁ - v₂‖) (hsub : Kh ⊆ K)
    (hu : IsVariationalInequalitySolution A j f K u)
    (huh : IsVariationalInequalitySolution A j f Kh uh) :
    ‖u - uh‖ ≤ max (M / c₀) (Real.sqrt (2 / c₀))
      * ⨅ vh : Kh, (‖u - vh‖ + Real.sqrt |residual A j j f u vh u|) := by
  have hKhne : Nonempty Kh := ⟨⟨uh, huh.1⟩⟩
  rw [show max (M / c₀) (Real.sqrt (2 / c₀)) = falkConst c₀ M from rfl,
    Real.mul_iInf_of_nonneg (falkConst_nonneg hc₀ hM)]
  refine le_ciInf fun vh => norm_le_falkConst hc₀ hM (norm_nonneg _) (norm_nonneg _) ?_
  have h := norm_sub_le_of_isVariationalInequalitySolution_of_subset hc₀
    hmono ((Chapter05.lipschitzWith_toNNReal_iff hM).1 hlip) hu huh
    (hsub huh.1) vh.2
  simp only [residual]
  linarith

/-! ### Exercise 11.4.2: internal approximations converge -/

/-- **Exercise 11.4.2** of [han2009theoretical]. Let $V$ be a real Hilbert space, let
$A \colon V \to V$ be strongly monotone with constant $c_0 > 0$ and Lipschitz continuous with
constant $M \ge 0$, and let $j \colon V \to \mathbb{R}$ be continuous. Let
$(V_n)_{n \in \mathbb{N}}$ be finite-dimensional subspaces of $V$ with $V_n \subseteq V_m$ for
$n \le m$ and with $\bigcup_n V_n$ dense in $V$. Let $u$ solve the variational inequality
(11.3.3) over $K = V$ with datum $f$, and let $u_n$ solve it over $V_n$, which is (11.4.12).
Then $u_n \to u$ in norm.

**Correction.** The source asks only that $\bigcup_n V_n$ be dense. This does not give, for
every $n$, a point of $V_n$ near $u$: if every second $V_n$ is $\{0\}$, then $u_n = 0$ for those
$n$. With nested subspaces the best approximations of $u$ in $V_n$ have nonincreasing errors,
and the density makes these errors tend to zero.

No weak compactness is used. The bound of `AtkinsonHan.Chapter11.theorem_11_4_2_of_subset` at
the best approximation $w_n$ of $u$ in $V_n$ tends to zero, because $\|u - w_n\|$ does and the
residual is continuous in its first argument. A finite element analysis can cite this result
instead of Theorem 11.4.1. -/
theorem exercise_11_4_2 {Vh : ℕ → Submodule ℝ V} [∀ n, FiniteDimensional ℝ (Vh n)]
    {uh : ℕ → V} (hc₀ : 0 < c₀) (hM : 0 ≤ M) (hmono : Chapter05.StronglyMonotoneWith A c₀)
    (hlip : ∀ v₁ v₂ : V, ‖A v₁ - A v₂‖ ≤ M * ‖v₁ - v₂‖) (hVmono : Monotone Vh)
    (hdense : Dense (⋃ n, (Vh n : Set V))) (hjc : Continuous j)
    (hu : IsVariationalInequalitySolution A j f univ u)
    (huh : ∀ n, IsVariationalInequalitySolution A j f (Vh n : Set V) (uh n)) :
    Tendsto uh atTop (𝓝 u) := by
  -- the best approximations to `u` in the `V_h`
  choose w hw using fun n => exists_isBestApprox_of_finiteDimensional (Vh n) u
  have hwmem : ∀ n, w n ∈ (Vh n : Set V) := fun n => (hw n).1
  have hwlim : Tendsto w atTop (𝓝 u) := by
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun n => norm_nonneg _)
      (fun n => le_of_eq (norm_sub_rev _ _)) ?_)
    refine NormedAddGroup.tendsto_nhds_zero.2 fun ε hε => ?_
    obtain ⟨z, hz, hzd⟩ := Metric.mem_closure_iff.1 (hdense u) ε hε
    obtain ⟨m, hm⟩ := mem_iUnion.1 hz
    refine eventually_atTop.2 ⟨m, fun n hn => ?_⟩
    have hzn : z ∈ (Vh n : Set V) := hVmono hn hm
    calc ‖‖u - w n‖‖ = ‖u - w n‖ := by rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      _ ≤ ‖u - z‖ := (hw n).2 z hzn
      _ < ε := by rwa [dist_eq_norm] at hzd
  exact tendsto_of_isVariationalInequalitySolution_of_subset hc₀ hmono
    ((Chapter05.lipschitzWith_toNNReal_iff hM).1 hlip) (fun n => subset_univ _) hjc.continuousOn hu
    huh hwmem hwlim

/-! ### Exercise 11.4.3: the regularized problem -/

omit [CompleteSpace V] in
/-- **Exercise 11.4.3** of [han2009theoretical], the a priori bound (11.4.20) with $\beta = 1/2$.
Let $V$ be a real inner product space and let $A \colon V \to V$ be strongly monotone with
constant $c_0 > 0$. Let $j, j_\varepsilon \colon V \to \mathbb{R}$ satisfy
$|j_\varepsilon(v) - j(v)| \le c_1 \varepsilon$ for every $v \in V$, which is (11.4.32). Let $u$
solve the variational inequality (11.3.3) over $K = V$ with $j$, and let $u_\varepsilon$ solve
it over $K = V$ with $j_\varepsilon$, both with datum $f$. Then
$$\|u - u_\varepsilon\| \le \sqrt{\frac{2 c_1 \varepsilon}{c_0}}.$$

The constant is sharp for this argument. At $v = u_\varepsilon$ and $v_h = u$ the cross term of
the core estimate vanishes, so neither a Lipschitz constant nor Young's inequality enters;
Falk's lemma would lose a factor of two.

**Reading.** General strongly monotone operator and already assumed uniform functional error; treats
the bound part.
-/
theorem exercise_11_4_3 {jeps : V → ℝ} {c₁ ε : ℝ} {ueps : V} (hc₀ : 0 < c₀)
    (hmono : Chapter05.StronglyMonotoneWith A c₀)
    (hu : IsVariationalInequalitySolution A j f univ u)
    (hueps : IsVariationalInequalitySolution A jeps f univ ueps)
    (hreg : ∀ v : V, |jeps v - j v| ≤ c₁ * ε) : ‖u - ueps‖ ≤ Real.sqrt (2 * c₁ * ε / c₀) :=
  norm_sub_le_of_regularization hc₀ hmono hu hueps hreg

/-! ### Theorem 11.4.6: the method of numerical integration -/

/-- **Theorem 11.4.6** of [han2009theoretical], convergence of the method of numerical integration
(11.4.25). Let $V$ be a real Hilbert space, let $A \colon V \to V$ be strongly monotone with
constant $c_0 > 0$ and Lipschitz continuous with constant $M \ge 0$, and let
$j \colon V \to \mathbb{R}$ be convex and lower semicontinuous. Let $(V_n)$ be subspaces of $V$
and $j_n \colon V \to \mathbb{R}$ functionals such that:

* the $j_n$ are uniformly proper: there are $\ell_0 \in V'$ and $c_1 \in \mathbb{R}$ with
  $\ell_0(v_n) + c_1 \le j_n(v_n)$ for all $n$ and all $v_n \in V_n$;
* for every $\sigma \colon \mathbb{N} \to \mathbb{N}$ and every sequence $v_k \in V_{\sigma(k)}$
  that converges weakly to $v$, and for every $\alpha < j(v)$, eventually
  $j_{\sigma(k)}(v_k) > \alpha$;
* there are a dense set $U \subseteq V$ and maps $r_n$ with $r_n v \in V_n$, $r_n v \to v$ and
  $j_n(r_n v) \to j(v)$ for every $v \in U$.

Let $u$ solve the variational inequality (11.3.3) over $K = V$ with $j$, and let $u_n$ solve it
over $V_n$ with $j_n$, both with datum $f$. Then $u_n \to u$ in norm.

**Reading.** The source writes the second condition as $\liminf j_n(v_n) \ge j(v)$ for
$v_n \rightharpoonup v$. In $\mathbb{R}$, `Filter.liminf` of a sequence that is unbounded below
is a junk value, not $-\infty$, so the inequality written with it would be a different
statement, false on such a sequence. The eventual form is the one that the proof uses. The
condition is also required along every reindexing $\sigma$, because the proof passes to
subsequences.

**Generalization.** The source assumes that the $V_n$ are finite-dimensional and that the $j_n$
are convex and lower semicontinuous. These hypotheses only make the discrete problems solvable
by Theorem 11.3.1, and here the solutions $u_n$ are given.

In the source, the discrete problem is posed on the whole finite element space $V_n$, and it
replaces the nondifferentiable term $j$ of (11.4.11) by a functional $j_n$ obtained from a
quadrature rule. This is the one result of the section in which the functional varies with $n$.
The theorem is `tendsto_of_isVariationalInequalitySolution_of_mosco` at $K = V$: the two
conditions on the family say that $j_n \to j$ in the sense of Mosco. The continuity of $j$,
which that theorem uses to pass from $U$ to $V$, follows from the hypotheses by
`ConvexOn.continuous_of_lowerSemicontinuous`, since $j$ is real-valued, convex and lower
semicontinuous on a Hilbert space. -/
theorem theorem_11_4_6 {jh : ℕ → V → ℝ} {uh : ℕ → V} {U : Set V} {Vh : ℕ → Submodule ℝ V}
    {r : ℕ → V → V} (hc₀ : 0 < c₀) (hM : 0 ≤ M) (hmono : Chapter05.StronglyMonotoneWith A c₀)
    (hlip : ∀ v₁ v₂ : V, ‖A v₁ - A v₂‖ ≤ M * ‖v₁ - v₂‖)
    (hjcv : ConvexOn ℝ univ j) (hjlsc : LowerSemicontinuous j)
    (hproper : ∃ (l₀ : V →L[ℝ] ℝ) (c₁ : ℝ), ∀ n, ∀ vh ∈ (Vh n : Set V), l₀ vh + c₁ ≤ jh n vh)
    (hliminf : ∀ (σ : ℕ → ℕ) (vh : ℕ → V) (v : V), (∀ k, vh k ∈ (Vh (σ k) : Set V)) →
      (∀ y : V, Tendsto (fun k => ⟪vh k, y⟫_ℝ) atTop (𝓝 ⟪v, y⟫_ℝ)) →
      ∀ α < j v, ∀ᶠ k in atTop, α < jh (σ k) (vh k))
    (hU : Dense U) (hrmem : ∀ v ∈ U, ∀ n, r n v ∈ (Vh n : Set V))
    (hr : ∀ v ∈ U, Tendsto (fun n => r n v) atTop (𝓝 v))
    (hjr : ∀ v ∈ U, Tendsto (fun n => jh n (r n v)) atTop (𝓝 (j v)))
    (hu : IsVariationalInequalitySolution A j f univ u)
    (huh : ∀ n, IsVariationalInequalitySolution A (jh n) f (Vh n : Set V) (uh n)) :
    Tendsto uh atTop (𝓝 u) :=
  tendsto_of_isVariationalInequalitySolution_of_mosco hc₀ hmono
    ((Chapter05.lipschitzWith_toNNReal_iff hM).1 hlip) convex_univ isClosed_univ hjcv
    (ConvexOn.continuous_of_lowerSemicontinuous hjcv hjlsc) (fun _ => subset_univ _) hproper
    hliminf (fun v _ => hU v)
    (fun v hv => ⟨fun n => r n v, fun n => hrmem v hv n, hr v hv, hjr v hv⟩) hu huh

/-! ### Theorem 11.4.7: a discrete functional that dominates $j$ -/

/-- **Theorem 11.4.7** of [han2009theoretical], the estimate (11.4.27). Let $V$ be a real Hilbert
space, let $A \colon V \to V$ be strongly monotone with constant $c_0 > 0$ and Lipschitz
continuous with constant $M \ge 0$, let $j, j_h \colon V \to \mathbb{R}$, $f \in V$ and
$K_h \subseteq V$, and let $j(v_h) \le j_h(v_h)$ for all $v_h \in K_h$, which is (11.4.26). Let
$u$ solve the variational inequality (11.3.3) over $K = V$ with $j$, and let $u_h$ solve it over
$K_h$ with $j_h$. Then
$$\|u - u_h\| \le c \inf_{v_h \in K_h} \Bigl(\|u - v_h\| + |R_h(v_h, u)|^{1/2}\Bigr), \qquad
  R_h(v_h, u) = (A u, v_h - u) + j_h(v_h) - j(u) - (f, v_h - u),$$
with $c = \max\{M/c_0, \sqrt{2/c_0}\}$ as in `AtkinsonHan.Chapter11.theorem_11_4_2_of_subset`.

The numerical-integration construction (11.4.28) satisfies (11.4.26). The proof is that of
Falk's lemma, with the inequality $j(u_h) \le j_h(u_h)$ inserted at $v = u_h$.

**Reading.** Arbitrary admissible sets rather than linear subspaces and an explicit square-root
error constant.
-/
theorem theorem_11_4_7 (hc₀ : 0 < c₀) (hM : 0 ≤ M)
    (hmono : Chapter05.StronglyMonotoneWith A c₀)
    (hlip : ∀ v₁ v₂ : V, ‖A v₁ - A v₂‖ ≤ M * ‖v₁ - v₂‖)
    (hu : IsVariationalInequalitySolution A j f univ u)
    (huh : IsVariationalInequalitySolution A jh f Kh uh) (hjle : ∀ vh ∈ Kh, j vh ≤ jh vh) :
    ‖u - uh‖ ≤ max (M / c₀) (Real.sqrt (2 / c₀))
      * ⨅ vh : Kh, (‖u - vh‖ + Real.sqrt |residual A jh j f u vh u|) := by
  have hKhne : Nonempty Kh := ⟨⟨uh, huh.1⟩⟩
  rw [show max (M / c₀) (Real.sqrt (2 / c₀)) = falkConst c₀ M from rfl,
    Real.mul_iInf_of_nonneg (falkConst_nonneg hc₀ hM)]
  refine le_ciInf fun vh => norm_le_falkConst hc₀ hM (norm_nonneg _) (norm_nonneg _) ?_
  have h := norm_sub_le_of_isVariationalInequalitySolution_of_le hc₀
    hmono ((Chapter05.lipschitzWith_toNNReal_iff hM).1 hlip) hu huh
    (mem_univ uh) (hjle uh huh.1) vh.2
  simp only [residual]
  linarith

end


/-!
### Example 11.4.3: the obstacle problem with linear elements

The finite element approximation of the obstacle problem of Example 11.1.1 on a polygon. The
discrete admissible set $K_h$ consists of the continuous piecewise linear functions that dominate
the obstacle at the nodes (`AtkinsonHan.Chapter11.discreteObstacleSet`), and Falk's lemma gives the
estimate $\|u - u_h\|_{H^1} \le c h$ (`AtkinsonHan.Chapter11.example_11_4_3`). The triangulations
are those of `Numlib.Geometry.Triangulation`, the interpolation estimates are Theorem 10.3.9 for the
linear element, and the finite element space is `Triangulation.polySpaceZero`. The specific
ingredients are the monotonicity of the linear interpolant, the membership
$\max\{u_h, \psi\} \in K$, and $\Pi_h u \in K_h$.
-/

section Example1143

open MeasureTheory TopologicalSpace EuclideanSpace
open scoped ENNReal

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-- The barycentric coordinates $\lambda_i$, $i = 0, 1, 2$, are nonnegative on the closed reference
triangle. -/
theorem baryCoord_nonneg {x : 𝔼₂} (hx : x ∈ closure (referenceTriangle : Set 𝔼₂)) (i : Fin 3) :
    0 ≤ baryCoord i x := by
  rw [closure_referenceTriangle_eq] at hx
  obtain ⟨h0, h1, h2⟩ := hx
  fin_cases i
  · simp only [baryCoord, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    linarith
  · simpa [baryCoord] using h0
  · simpa [baryCoord] using h1

/-- Each barycentric coordinate $\lambda_i$ on $\mathbb{R}^2$ is a polynomial of total degree at
most $1$. -/
theorem baryCoord_eq_eval (i : Fin 3) : ∃ q : MvPolynomial (Fin 2) ℝ, q.totalDegree ≤ 1 ∧
    ∀ x : 𝔼₂, baryCoord i x = MvPolynomial.eval (fun j ↦ x j) q := by
  fin_cases i
  · refine ⟨MvPolynomial.C 1 - MvPolynomial.X 0 - MvPolynomial.X 1, ?_, fun x ↦ ?_⟩
    · refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
      · refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
        · simp
        · exact (MvPolynomial.totalDegree_X _).le
      · exact (MvPolynomial.totalDegree_X _).le
    · simp [baryCoord]
  · refine ⟨MvPolynomial.X 0, (MvPolynomial.totalDegree_X _).le, fun x ↦ ?_⟩
    simp [baryCoord]
  · refine ⟨MvPolynomial.X 1, (MvPolynomial.totalDegree_X _).le, fun x ↦ ?_⟩
    simp [baryCoord]

/-- The linear element on the reference triangle is **edge unisolvent**: for the vertices as nodes
and the barycentric coordinates as shape functions, the interpolant of a function that vanishes
at the two ends of an edge vanishes on that whole edge.

This is `EuclideanSpace.IsEdgeUnisolvent` for `EuclideanSpace.referenceTriangleVertex` and
`EuclideanSpace.baryCoord`. It holds because the interpolant is affine along the edge. -/
theorem isEdgeUnisolvent_linear : IsEdgeUnisolvent referenceTriangleVertex baryCoord := by
  intro a b hab v hv y hy
  rw [segment_eq_image'] at hy
  obtain ⟨s, -, rfl⟩ := hy
  have hlin : ∀ (P Q : 𝔼₂) (t : ℝ),
      Approximation.nodalInterp referenceTriangleVertex baryCoord v (P + t • (Q - P))
        = Approximation.nodalInterp referenceTriangleVertex baryCoord v P
          + t * (Approximation.nodalInterp referenceTriangleVertex baryCoord v Q
            - Approximation.nodalInterp referenceTriangleVertex baryCoord v P) := by
    intro P Q t
    simp only [Approximation.nodalInterp_apply, baryCoord_lineMap, smul_eq_mul, add_mul, sub_mul,
      mul_assoc, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hnode : ∀ c : Fin 3, c ∈ ({a, b} : Set (Fin 3)) →
      Approximation.nodalInterp referenceTriangleVertex baryCoord v (referenceTriangleVertex c)
        = 0 := by
    intro c hc
    rw [isNodalBasis_baryCoord.nodalInterp_apply_node]
    refine hv c ?_
    rcases hc with rfl | rfl
    · exact left_mem_segment ℝ _ _
    · exact right_mem_segment ℝ _ _
  rw [hlin, hnode a (by simp), hnode b (by simp)]
  ring

/-- The linear interpolant is monotone. Let $\mathcal{T}$ be a triangulation of an open set
$\Omega \subseteq \mathbb{R}^2$ and let $v, w \colon \mathbb{R}^2 \to \mathbb{R}$ with
$v(x) \le w(x)$ at every vertex $x$ of $\mathcal{T}$. Then $\Pi_h v \le \Pi_h w$ on
$\overline\Omega$.

The proof uses that the barycentric coordinates are nonnegative on the closed elements. -/
theorem globalInterp_linear_mono {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) {v w : 𝔼₂ → ℝ}
    (hvw : ∀ x ∈ 𝒯.vertices, v x ≤ w x) {x : 𝔼₂} (hx : x ∈ closure (Ω : Set 𝔼₂)) :
    𝒯.globalInterp referenceTriangleVertex baryCoord v x
      ≤ 𝒯.globalInterp referenceTriangleVertex baryCoord w x := by
  rw [𝒯.closure_eq_iUnion_closedK, mem_iUnion] at hx
  obtain ⟨T, hxT⟩ := hx
  have hxT' := hxT
  rw [← 𝒯.image_closedReferenceTriangle] at hxT'
  obtain ⟨z, hz, rfl⟩ := hxT'
  rw [𝒯.globalInterp_eq_of_mem_closedK _ _ 𝒯.isConformingElement_linear T v hxT,
    𝒯.globalInterp_eq_of_mem_closedK _ _ 𝒯.isConformingElement_linear T w hxT]
  simp only [Triangulation.localInterp_apply, 𝒯.affine_referenceTriangleVertex, 𝒯.affine_symm]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  refine mul_le_mul_of_nonneg_left (hvw _ (𝒯.vertex_mem_vertices T i)) ?_
  refine baryCoord_nonneg ?_ i
  rw [closure_referenceTriangle_eq]
  exact hz

/-- Let $\Omega \subseteq \mathbb{R}^2$ be open, and let $v, w$ be continuous on $\overline\Omega$
with $v \le w$ almost everywhere on $\Omega$. Then $v \le w$ on $\overline\Omega$. -/
theorem le_on_closure_of_ae_le {Ω : Opens 𝔼₂} {v w : 𝔼₂ → ℝ}
    (h : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼₂)), v x ≤ w x)
    (hv : ContinuousOn v (closure (Ω : Set 𝔼₂))) (hw : ContinuousOn w (closure (Ω : Set 𝔼₂))) :
    ∀ x ∈ closure (Ω : Set 𝔼₂), v x ≤ w x := by
  have hmax : EqOn (fun x ↦ max (v x) (w x)) w (closure (Ω : Set 𝔼₂)) := by
    refine (hv.sup hw).eqOn_closure_of_ae_eq (μ := volume) Ω.isOpen hw ?_
    filter_upwards [h] with x hx
    exact max_eq_right hx
  intro x hx
  have := hmax hx
  simp only at this
  rw [← this]
  exact le_max_left _ _

/-- Let $\Omega \subseteq \mathbb{R}^2$ be open and let $f$ be in the Sobolev space of order $0$
over $L^2(\Omega)$. Then $\|f\|_{L^2(\Omega)}$ is at most the Sobolev norm of order $0$ of $f$. -/
theorem eLpNorm_le_sobolevNorm_zero {Ω : Opens 𝔼₂} {f : 𝔼₂ → ℝ}
    (hf : MemSobolev f 0 2 Ω volume) :
    eLpNorm f 2 (volume.restrict (Ω : Set 𝔼₂)) ≤ sobolevNorm f 0 2 Ω volume := by
  have hW := hasWeakIteratedFDerivOn_zero (μ := volume) (hf.memLp.locallyIntegrableOn one_le_two)
  have hae : ∀ᵐ x ∂volume.restrict (Ω : Set 𝔼₂),
      ‖weakIteratedFDeriv 0 f Ω volume x‖ = ‖f x‖ := by
    filter_upwards [(ae_restrict_iff' Ω.isOpen.measurableSet).2 hW.weakIteratedFDeriv_ae_eq]
      with x hx
    rw [hx]
    exact LinearIsometryEquiv.norm_map _ _
  rw [← eLpNorm_congr_norm_ae (hf.memLp_weakIteratedFDeriv le_rfl).aestronglyMeasurable
    hf.memLp.aestronglyMeasurable hae]
  exact eLpNorm_weakIteratedFDeriv_le_sobolevNorm one_le_two (by simp) le_rfl


/-- **Example 11.4.3** of [han2009theoretical], the discrete admissible set $K_h$. Let
$\mathcal{T}_h$ be a triangulation of an open set $\Omega \subseteq \mathbb{R}^2$ and let
$\psi' \colon \mathbb{R}^2 \to \mathbb{R}$ represent the obstacle. Then $K_h$ is the set of
$v_h \in H^1_0(\Omega)$ whose function is almost everywhere equal to a function $v$ that is
continuous on $\overline\Omega$, linear on every element of $\mathcal{T}_h$, zero on
$\partial\Omega$, and satisfies $v(x) \ge \psi'(x)$ at every vertex $x$ of $\mathcal{T}_h$.

In general $K_h \not\subseteq K$. The set lies in the finite element space
`Triangulation.polySpaceZero` by `AtkinsonHan.Chapter11.discreteObstacleSet_subset`. -/
def discreteObstacleSet {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) (ψ' : 𝔼₂ → ℝ) :
    Set (SobolevEuclideanZero 2 1 2 Ω) :=
  {vh | ∃ v : 𝔼₂ → ℝ, ContinuousOn v (closure (Ω : Set 𝔼₂)) ∧ 𝒯.IsPiecewisePoly 1 v ∧
    EqOn v 0 (frontier (Ω : Set 𝔼₂)) ∧
    SobolevMultiIndex.fn (vh : SobolevEuclidean 2 1 2 Ω) =ᵐ[volume.restrict (Ω : Set 𝔼₂)] v ∧
    ∀ x ∈ 𝒯.vertices, ψ' x ≤ v x}

/-- The discrete admissible set $K_h$ of Example 11.4.3 lies in the finite element space $V_h$ of
continuous piecewise linear functions in $H^1_0(\Omega)$, `Triangulation.polySpaceZero 2 1`. -/
theorem discreteObstacleSet_subset {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) (ψ' : 𝔼₂ → ℝ) :
    discreteObstacleSet 𝒯 ψ' ⊆ (𝒯.polySpaceZero 2 1 : Set (SobolevEuclideanZero 2 1 2 Ω)) := by
  rintro vh ⟨v, hvc, hvp, hv0, hvh, -⟩
  exact ⟨v, hvc, hvp, hv0, hvh⟩

/-- **Example 11.4.3** of [han2009theoretical], the function $u^{h,*} = \max\{u_h, \psi\}$ lies in
$K$. Let $\Omega \subseteq \mathbb{R}^2$ be open. Let the obstacle $\psi \in H^1(\Omega)$ have a
representative $\psi'$ that is continuous on $\overline\Omega$, lies in $H^1(\Omega)$ and
satisfies $\psi' \le 0$ on $\partial\Omega$. Let $v$ be continuous on $\overline\Omega$, in
$H^1(\Omega)$, and zero on $\partial\Omega$. Then there is $w \in K = \{v \in H^1_0(\Omega) : v
\ge \psi \text{ a.e.}\}$ whose function is almost everywhere equal to $\max\{v, \psi'\}$.

The function is $v + (\psi' - v)^+ \in H^1(\Omega)$. It is continuous on $\overline\Omega$ and
zero on $\partial\Omega$, hence in $H^1_0(\Omega)$ by Theorem 9.17 of [brezis2011functional],
(i) implies (ii).

**Reading.** Maximum with the obstacle gives a feasible function using explicit trace and
representative data.
-/
theorem exists_max_mem_obstacleSet {Ω : Opens 𝔼₂} {ψ : SobolevEuclidean 2 1 2 Ω} {ψ' : 𝔼₂ → ℝ}
    (hψ : SobolevMultiIndex.fn ψ =ᵐ[volume.restrict (Ω : Set 𝔼₂)] ψ')
    (hψc : ContinuousOn ψ' (closure (Ω : Set 𝔼₂))) (hψ1 : MemSobolev ψ' 1 2 Ω volume)
    (hψ0 : ∀ x ∈ frontier (Ω : Set 𝔼₂), ψ' x ≤ 0)
    {v : 𝔼₂ → ℝ} (hvc : ContinuousOn v (closure (Ω : Set 𝔼₂))) (hv1 : MemSobolev v 1 2 Ω volume)
    (hv0 : EqOn v 0 (frontier (Ω : Set 𝔼₂))) :
    ∃ w : SobolevEuclideanZero 2 1 2 Ω, w ∈ obstacleSet (d := 1) Ω ψ ∧
      SobolevMultiIndex.fn (w : SobolevEuclidean 2 1 2 Ω) =ᵐ[volume.restrict (Ω : Set 𝔼₂)]
        fun x ↦ max (v x) (ψ' x) := by
  have hmax : ∀ x, v x + max (ψ' x - v x) 0 = max (v x) (ψ' x) := fun x ↦ by
    rcases le_total (v x) (ψ' x) with h | h
    · rw [max_eq_left (sub_nonneg.2 h), max_eq_right h]
      ring
    · rw [max_eq_right (sub_nonpos.2 h), max_eq_left h, add_zero]
  -- `max (v, ψ') = v + (ψ' − v)⁺ ∈ H¹(Ω)`
  have hmem : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (fun x ↦ max (v x) (ψ' x)) 1 2 Ω volume := by
    have h1 := hv1.memSobolevMultiIndex (b := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis)
    have h2 := ((hψ1.sub hv1).memSobolevMultiIndex
      (b := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis)).posPart one_le_two
    have h3 := h1.add h2
    refine h3.congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    exact hmax x
  have hex := hmem.exists_sobolevMultiIndex
  obtain ⟨w', hw'⟩ := hex
  have hcont : ContinuousOn (fun x ↦ max (v x) (ψ' x)) (closure (Ω : Set 𝔼₂)) := hvc.sup hψc
  have h0 : EqOn (fun x ↦ max (v x) (ψ' x)) 0 (frontier (Ω : Set 𝔼₂)) := fun x hx ↦ by
    simp only [hv0 hx, Pi.zero_apply]
    exact max_eq_left (hψ0 x hx)
  have hw'0 : w' ∈ SobolevEuclideanZero 2 1 2 Ω :=
    SobolevEuclideanZero.mem_of_continuousOn_closure_of_eqOn_frontier (by simp) w' hw' hcont h0
  refine ⟨⟨w', hw'0⟩, ?_, hw'⟩
  rw [mem_obstacleSet_iff]
  filter_upwards [hψ, hw'] with x h1 h2
  rw [h1]
  exact (le_max_right _ _).trans_eq h2.symm

/-- **Example 11.4.3** of [han2009theoretical], the interpolant $\Pi_h u$ lies in $K_h$. Let
$\mathcal{T}$ be a triangulation of an open set $\Omega \subseteq \mathbb{R}^2$ whose boundary
$\partial\Omega$ is a union of element edges. Let $\psi', u' \colon \mathbb{R}^2 \to \mathbb{R}$
with $\psi' \le u'$ on $\overline\Omega$ and $u' = 0$ on $\partial\Omega$. Then there is
$v_h \in K_h$ whose function is almost everywhere equal to the linear interpolant $\Pi_h u'$.

The interpolant is continuous and piecewise linear, it vanishes on $\partial\Omega$ with $u'$ by
`Triangulation.globalInterp_eqOn_frontier`, and at every node $x$ it takes the value
$u'(x) \ge \psi'(x)$.

**Reading.** Uses closure comparison and the boundary-edge covering assumption for the admissible
interpolant.
-/
theorem exists_globalInterp_mem_discreteObstacleSet {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω)
    (hedge : 𝒯.FrontierSubsetEdges) {ψ' u' : 𝔼₂ → ℝ}
    (hψu : ∀ x ∈ closure (Ω : Set 𝔼₂), ψ' x ≤ u' x) (hu0 : EqOn u' 0 (frontier (Ω : Set 𝔼₂))) :
    ∃ vh ∈ discreteObstacleSet 𝒯 ψ',
      SobolevMultiIndex.fn (vh : SobolevEuclidean 2 1 2 Ω) =ᵐ[volume.restrict (Ω : Set 𝔼₂)]
        𝒯.globalInterp referenceTriangleVertex baryCoord u' := by
  have hcont := 𝒯.continuousOn_globalInterp referenceTriangleVertex baryCoord
    𝒯.isConformingElement_linear (fun i ↦ (contDiff_baryCoord i).continuous) u'
  have hpoly := 𝒯.globalInterp_isPiecewisePoly 𝒯.isConformingElement_linear baryCoord_eq_eval u'
  have h0 := 𝒯.globalInterp_eqOn_frontier referenceTriangleVertex baryCoord hedge
    𝒯.isConformingElement_linear isEdgeUnisolvent_linear hu0
  have hex := 𝒯.exists_mem_polySpaceZero 2 (by simp) hcont hpoly h0
  obtain ⟨w, -, hw⟩ := hex
  refine ⟨w, ⟨_, hcont, hpoly, h0, hw, fun x hx ↦ ?_⟩, hw⟩
  obtain ⟨T, a, rfl⟩ := 𝒯.exists_vertex_of_mem_vertices hx
  rw [𝒯.globalInterp_eq_of_mem_closedK _ _ 𝒯.isConformingElement_linear T u'
    (𝒯.vertex_mem_closedK T a), 𝒯.localInterp_linear_vertex]
  exact hψu _ (𝒯.closedK_subset_closure T (𝒯.vertex_mem_closedK T a))


/-- **Example 11.4.3** of [han2009theoretical], the residual. Let $\Omega \subseteq \mathbb{R}^2$ be
open, let $f, g \in L^2(\Omega)$, and let $u \in H^1_0(\Omega)$ satisfy $\int_\Omega \nabla u
\cdot \nabla v = \int_\Omega g v$ for all $v \in H^1_0(\Omega)$, that is $-\Delta u = g$ weakly.
Then for every $z \in H^1_0(\Omega)$,
$$\int_\Omega \nabla u \cdot \nabla z \, dx - \int_\Omega f z \, dx \le \|g - f\|_{L^2(\Omega)}
  \|z\|_{L^2(\Omega)}.$$

With $z = v - w$, the left side is the residual $R(v, w) = a(u, v - w) - \ell(v - w)$ of the
obstacle problem, which equals $\int_\Omega (g - f)(v - w)$.

**Reading.** Residual bound assumes the weak Laplacian's load representation explicitly.
-/
theorem residual_le_of_eq_load {Ω : Opens 𝔼₂}
    (f g : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼₂))) {u : SobolevEuclideanZero 2 1 2 Ω}
    (hΔ : ∀ v : SobolevEuclideanZero 2 1 2 Ω,
      dirichletBilinForm (d := 1) Ω u v = loadZero (d := 1) Ω g v)
    (z : SobolevEuclideanZero 2 1 2 Ω) :
    dirichletBilinForm (d := 1) Ω u z - loadZero (d := 1) Ω f z
      ≤ ‖g - f‖ * (eLpNorm (SobolevMultiIndex.fn (z : SobolevEuclidean 2 1 2 Ω)) 2
        (volume.restrict (Ω : Set 𝔼₂))).toReal := by
  rw [hΔ z, ← sub_apply, ← loadZero_sub]
  refine (le_abs_self _).trans ((Elliptic.abs_load_le Ω (g - f) z).trans_eq ?_)
  rw [Lp.norm_def]
  rfl

/-- Let $a, S \in [0, \infty]$ with $S \neq \infty$, and let $c \ge 0$ be real. If $a \le c S$ in
$[0, \infty]$, then the same inequality holds between the real numbers given by
`ENNReal.toReal`: `a.toReal ≤ c * S.toReal`. -/
theorem toReal_le_of_le_ofReal_mul {a S : ℝ≥0∞} {c : ℝ} (hc : 0 ≤ c) (hS : S ≠ ⊤)
    (h : a ≤ ENNReal.ofReal c * S) : a.toReal ≤ c * S.toReal := by
  have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS) h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] at h'

/-- Let $\mathcal{T}$ be a triangulation of an open set $\Omega \subseteq \mathbb{R}^2$ and let
$v \in H^2(\Omega)$. Then $v - \Pi_h v$ lies in the Sobolev space of order $0$ over
$L^2(\Omega)$, where $\Pi_h$ is the linear interpolant. -/
theorem memSobolev_sub_globalInterp_linear {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) {v : 𝔼₂ → ℝ}
    (hv : MemSobolev v 2 2 Ω volume) :
    MemSobolev (v - 𝒯.globalInterp referenceTriangleVertex baryCoord v) 0 2 Ω volume :=
  (hv.mono_order (by norm_num)).sub
    ((𝒯.memSobolev_globalInterp referenceTriangleVertex baryCoord 𝒯.isConformingElement_linear
      (fun j ↦ (contDiff_baryCoord j).of_le (by simp)) v 2).mono_order (by norm_num))

/-- **Example 11.4.3** of [han2009theoretical], the bound $\|u^{h,*} - u_h\|_0 \le \|\psi - \Pi_h
\psi\|_0$. Let $\mathcal{T}$ be a triangulation of an open set $\Omega \subseteq \mathbb{R}^2$,
let $\psi'$ and $v$ be continuous on $\overline\Omega$, let $v$ be linear on every element, and
let $v(x) \ge \psi'(x)$ at every vertex $x$. Then
$$\bigl\|\max\{v, \psi'\} - v\bigr\|_{L^2(\Omega)} \le \|\psi' - \Pi_h \psi'\|_{L^2(\Omega)}.$$

The proof uses $v = \Pi_h v \ge \Pi_h \psi'$ on $\overline\Omega$, by the monotonicity of the
linear interpolant. So $0 \le \psi' - v \le \psi' - \Pi_h \psi'$ where $v < \psi'$, and
$\max\{v, \psi'\} - v = 0$ elsewhere.

**Reading.** The feasible maximum estimate uses explicit continuous representatives and their
zero-boundary realization.
-/
theorem eLpNorm_max_sub_le {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) {ψ' v : 𝔼₂ → ℝ}
    (hψc : ContinuousOn ψ' (closure (Ω : Set 𝔼₂))) (hvc : ContinuousOn v (closure (Ω : Set 𝔼₂)))
    (hvp : 𝒯.IsPiecewisePoly 1 v) (hψv : ∀ x ∈ 𝒯.vertices, ψ' x ≤ v x) :
    eLpNorm (fun x ↦ max (v x) (ψ' x) - v x) 2 (volume.restrict (Ω : Set 𝔼₂))
      ≤ eLpNorm (ψ' - 𝒯.globalInterp referenceTriangleVertex baryCoord ψ') 2
        (volume.restrict (Ω : Set 𝔼₂)) := by
  have hrep : EqOn (𝒯.globalInterp referenceTriangleVertex baryCoord v) v
      (closure (Ω : Set 𝔼₂)) :=
    𝒯.globalInterp_eqOn_closure_of_isPiecewisePoly 𝒯.isConformingElement_linear
      referenceTriangleVertex_mem_closure (fun q hq x ↦ Chapter10.nodalInterp_baryCoord_eval q hq x)
      hvp
  have hge : ∀ x ∈ closure (Ω : Set 𝔼₂),
      𝒯.globalInterp referenceTriangleVertex baryCoord ψ' x ≤ v x := fun x hx ↦
    (globalInterp_linear_mono 𝒯 hψv hx).trans_eq (hrep hx)
  have hpt : ∀ x ∈ (Ω : Set 𝔼₂), ‖max (v x) (ψ' x) - v x‖
      ≤ ‖(ψ' - 𝒯.globalInterp referenceTriangleVertex baryCoord ψ') x‖ := by
    intro x hx
    have h1 := hge x (subset_closure hx)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Pi.sub_apply]
    rcases le_total (ψ' x) (v x) with h | h
    · rw [max_eq_left h, sub_self, abs_zero]
      exact abs_nonneg _
    · rw [max_eq_right h, abs_of_nonneg (sub_nonneg.2 h)]
      exact (sub_le_sub_left h1 _).trans (le_abs_self _)
  have hmeas : AEStronglyMeasurable (fun x ↦ max (v x) (ψ' x) - v x)
      (volume.restrict (Ω : Set 𝔼₂)) := by
    have hv' := (hvc.mono subset_closure).aestronglyMeasurable (μ := volume) Ω.isOpen.measurableSet
    have hψ' := (hψc.mono subset_closure).aestronglyMeasurable (μ := volume) Ω.isOpen.measurableSet
    exact (hv'.sup hψ').sub hv'
  exact eLpNorm_mono_ae hmeas
    ((ae_restrict_iff' Ω.isOpen.measurableSet).2 (Filter.Eventually.of_forall hpt))

/-- **Example 11.4.3** of [han2009theoretical] (the obstacle problem with linear elements). Let
$\Omega \subseteq \mathbb{R}^2$ be open with $\Omega \subseteq B(0, R)$ for some $R \ge 0$. Let
$(\mathcal{T}_i)_{i \in \iota}$ be a regular family of triangulations of $\Omega$ along a filter
$l$, with mesh sizes $h_i \le H$, such that $\partial\Omega$ is a union of element edges of
every $\mathcal{T}_i$. Let $f, g \in L^2(\Omega)$. Let the obstacle $\psi \in H^1(\Omega)$ have
a representative $\psi'$ that is continuous on $\overline\Omega$, lies in $H^2(\Omega)$ and
satisfies $\psi' \le 0$ on $\partial\Omega$. Let $u \in K = \{v \in H^1_0(\Omega) : v \ge \psi
\text{ a.e.}\}$ solve the obstacle problem
$$\int_\Omega \nabla u \cdot \nabla (v - u) \, dx \ge \int_\Omega f (v - u) \, dx \quad
  \text{for all } v \in K.$$
Let $u$ have a representative $u'$ that is continuous on $\overline\Omega$, lies in
$H^2(\Omega)$ and vanishes on $\partial\Omega$, and let $-\Delta u = g$ weakly: $\int_\Omega
\nabla u \cdot \nabla v = \int_\Omega g v$ for all $v \in H^1_0(\Omega)$. For every $i$, let
$u_{h,i} \in K_{h,i}$ solve the discrete problem
$$\int_\Omega \nabla u_{h,i} \cdot \nabla (v_h - u_{h,i}) \, dx \ge \int_\Omega f (v_h -
  u_{h,i}) \, dx \quad \text{for all } v_h \in K_{h,i},$$
where $K_{h,i}$ is the discrete admissible set of $\mathcal{T}_i$ for $\psi'$. Then there is a
constant $c$ with
$$\|u - u_{h,i}\|_{H^1(\Omega)} \le c h_i \quad \text{for all } i.$$

**Reading.** The source assumes $u, \psi \in H^2(\Omega)$. Here the regularity is stated on
representatives continuous on $\overline\Omega$, as in Theorem 10.3.9. The boundary conditions
$u = 0$ and $\psi \le 0$ on $\Gamma$ are stated on these representatives, because on a polygon
they do not follow from $u \in H^1_0(\Omega)$. The condition $-\Delta u \in L^2(\Omega)$ is the
hypothesis on $g$; on a $C^2$ domain it would follow from the regularity theorem for the
obstacle problem, but on a polygon it is assumed. The discrete set asks $v_h \ge \psi$ at every
vertex, including the boundary vertices, where it holds because $v_h = 0 \ge \psi$.

The discrete admissible set is `AtkinsonHan.Chapter11.discreteObstacleSet`, and the condition on
$\partial\Omega$ is `Triangulation.FrontierSubsetEdges`. The proof follows the source and gives
a constant that depends on $|u|_{2,\Omega}$, $|\psi|_{2,\Omega}$, $\|f\|_0$ and $\|g\|_0$. It
applies Falk's lemma (11.4.7), in the form `norm_sub_le_of_isVariationalInequalitySolution`,
with $v_h = \Pi_h u \in K_h$
(`AtkinsonHan.Chapter11.exists_globalInterp_mem_discreteObstacleSet`) and
$v = \max\{u_h, \psi\} \in K$ (`AtkinsonHan.Chapter11.exists_max_mem_obstacleSet`). The residual
is bounded by `AtkinsonHan.Chapter11.residual_le_of_eq_load`, the interpolation errors $\|u -
\Pi_h u\|_{m,\Omega} \le c h^{2-m} |u|_{2,\Omega}$ for $m = 0, 1$ by
`AtkinsonHan.Chapter10.theorem_10_3_9_linear`, and $\|\max\{u_h, \psi\} - u_h\|_0 \le \|\psi -
\Pi_h \psi\|_0 \le c h^2 |\psi|_{2,\Omega}$ by `AtkinsonHan.Chapter11.eLpNorm_max_sub_le`. -/
theorem example_11_4_3 {Ω : Opens 𝔼₂} {ι : Type*} {l : Filter ι} {𝒯 : ι → Triangulation Ω}
    (hreg : Chapter10.IsRegularFamily l fun i ↦ Set.range (𝒯 i).K)
    {H : ℝ} (hH : ∀ i, (𝒯 i).meshSize ≤ H) (hedge : ∀ i, (𝒯 i).FrontierSubsetEdges)
    {R : ℝ} (hR : 0 ≤ R) (hΩ : (Ω : Set 𝔼₂) ⊆ Metric.ball 0 R)
    (f g : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼₂))) {ψ : SobolevEuclidean 2 1 2 Ω} {ψ' : 𝔼₂ → ℝ}
    (hψ : SobolevMultiIndex.fn ψ =ᵐ[volume.restrict (Ω : Set 𝔼₂)] ψ')
    (hψc : ContinuousOn ψ' (closure (Ω : Set 𝔼₂))) (hψ2 : MemSobolev ψ' 2 2 Ω volume)
    (hψ0 : ∀ x ∈ frontier (Ω : Set 𝔼₂), ψ' x ≤ 0)
    {u : SobolevEuclideanZero 2 1 2 Ω}
    (hu : u ∈ obstacleSet (d := 1) Ω ψ ∧ ∀ v ∈ obstacleSet (d := 1) Ω ψ,
      dirichletBilinForm (d := 1) Ω u (v - u) ≥ loadZero (d := 1) Ω f (v - u))
    {u' : 𝔼₂ → ℝ} (hu' : SobolevMultiIndex.fn (u : SobolevEuclidean 2 1 2 Ω)
      =ᵐ[volume.restrict (Ω : Set 𝔼₂)] u')
    (hu'2 : MemSobolev u' 2 2 Ω volume) (hu'c : ContinuousOn u' (closure (Ω : Set 𝔼₂)))
    (hu'0 : EqOn u' 0 (frontier (Ω : Set 𝔼₂)))
    (hΔ : ∀ v : SobolevEuclideanZero 2 1 2 Ω,
      dirichletBilinForm (d := 1) Ω u v = loadZero (d := 1) Ω g v)
    {uh : ι → SobolevEuclideanZero 2 1 2 Ω}
    (huh : ∀ i, uh i ∈ discreteObstacleSet (𝒯 i) ψ' ∧ ∀ vh ∈ discreteObstacleSet (𝒯 i) ψ',
      dirichletBilinForm (d := 1) Ω (uh i) (vh - uh i) ≥ loadZero (d := 1) Ω f (vh - uh i)) :
    ∃ c : ℝ, ∀ i, ‖u - uh i‖ ≤ c * (𝒯 i).meshSize := by
  have hM := dirichletBilinForm_isBoundedWith (d := 1) Ω
  have hα := dirichletBilinForm_isEllipticWith (d := 1) Ω hR hΩ
  have hc₀ : (0 : ℝ) < (1 + (2 * R) ^ 2)⁻¹ := by positivity
  -- the variational inequalities in operator form
  have hmono := Chapter08.stronglyMonotone_toOperator hM hα
  have hlip := Chapter08.lipschitzWith_toOperator zero_le_one hM
  have huVI : IsVariationalInequalitySolution
      (BilinForm.toOperator (dirichletBilinForm (d := 1) Ω) hM) (fun _ ↦ (0 : ℝ))
      (SesqForm.rieszRep (loadZero (d := 1) Ω f)) (obstacleSet (d := 1) Ω ψ) u := by
    rw [Chapter11.isVariationalInequalitySolution_toOperator_iff]
    simpa only [add_zero, sub_zero] using hu
  -- the interpolation estimates of Theorem 10.3.9 for the linear element
  have h1 := Chapter10.theorem_10_3_9_linear (m := 1) le_rfl hreg hH
  obtain ⟨c₁, hc₁, hest₁⟩ := h1
  have h0 := Chapter10.theorem_10_3_9_linear (m := 0) (by norm_num) hreg hH
  obtain ⟨c₀', hc₀', hest₀⟩ := h0
  have hCC := FiniteElement.exists_norm_le_sobolevNorm Ω
  obtain ⟨C, hC0, hC⟩ := hCC
  -- the seminorms of the data
  obtain ⟨Su, hSu⟩ : ∃ Su : ℝ, Su = (sobolevSeminorm u' 2 2 Ω volume).toReal := ⟨_, rfl⟩
  obtain ⟨Sψ, hSψ⟩ : ∃ Sψ : ℝ, Sψ = (sobolevSeminorm ψ' 2 2 Ω volume).toReal := ⟨_, rfl⟩
  have hSu0 : 0 ≤ Su := hSu ▸ ENNReal.toReal_nonneg
  have hSψ0 : 0 ≤ Sψ := hSψ ▸ ENNReal.toReal_nonneg
  have hSufin : sobolevSeminorm u' 2 2 Ω volume ≠ ⊤ := hu'2.sobolevSeminorm_ne_top
  have hSψfin : sobolevSeminorm ψ' 2 2 Ω volume ≠ ⊤ := hψ2.sobolevSeminorm_ne_top
  -- the constant
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = ‖g - f‖ * (c₀' * Sψ) + ‖g - f‖ * (c₀' * Su)
      + 1 ^ 2 / (2 * (1 + (2 * R) ^ 2)⁻¹) * (C * (c₁ * Su)) ^ 2 := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨Real.sqrt (2 / (1 + (2 * R) ^ 2)⁻¹ * K), fun i ↦ ?_⟩
  have hh0 : 0 ≤ (𝒯 i).meshSize := (𝒯 i).meshSize_nonneg
  -- the discrete solution and its representative
  obtain ⟨hmem, hvi⟩ := huh i
  obtain ⟨v, hvc, hvp, hv0, hvh, hψv⟩ := hmem
  have hv1 : MemSobolev v 1 2 Ω volume := hvp.memSobolev hvc 2
  have huhVI : IsVariationalInequalitySolution
      (BilinForm.toOperator (dirichletBilinForm (d := 1) Ω) hM) (fun _ ↦ (0 : ℝ))
      (SesqForm.rieszRep (loadZero (d := 1) Ω f)) (discreteObstacleSet (𝒯 i) ψ') (uh i) := by
    rw [Chapter11.isVariationalInequalitySolution_toOperator_iff]
    simpa only [add_zero, sub_zero] using huh i
  -- `ψ ≤ u` on `Ω̄`
  have hψu : ∀ x ∈ closure (Ω : Set 𝔼₂), ψ' x ≤ u' x := by
    refine le_on_closure_of_ae_le ?_ hψc hu'c
    have hK' := (mem_obstacleSet_iff (d := 1) Ω).1 hu.1
    filter_upwards [hK', hψ, hu'] with x hx h1 h2
    rw [← h1, ← h2]
    exact hx
  -- `v_h = Π_h u ∈ K_h`
  obtain ⟨vh, hvhK, hfvh⟩ := exists_globalInterp_mem_discreteObstacleSet (𝒯 i) (hedge i) hψu hu'0
  -- `v = u^{h,*} = max (u_h, ψ) ∈ K`
  obtain ⟨w, hwK, hfw⟩ := exists_max_mem_obstacleSet hψ hψc (hψ2.mono_order (by norm_num)) hψ0
    hvc hv1 hv0
  -- Falk's lemma
  have hfalk := norm_sub_le_of_isVariationalInequalitySolution (L := 1) hc₀ hmono hlip huVI huhVI
    hwK hvhK
  simp only [sub_zero, add_zero, BilinForm.inner_toOperator, BilinForm.inner_rieszRep] at hfalk
  -- the two residuals
  have hres1 := residual_le_of_eq_load f g hΔ (w - uh i)
  have hres2 := residual_le_of_eq_load f g hΔ (vh - u)
  -- `‖u^{h,*} − u_h‖₀ ≤ ‖ψ − Π_h ψ‖₀ ≤ c h² |ψ|₂`
  have hL1 : (eLpNorm (SobolevMultiIndex.fn ((w - uh i : SobolevEuclideanZero 2 1 2 Ω)
      : SobolevEuclidean 2 1 2 Ω)) 2 (volume.restrict (Ω : Set 𝔼₂))).toReal
      ≤ c₀' * (𝒯 i).meshSize ^ 2 * Sψ := by
    have hae : SobolevMultiIndex.fn ((w - uh i : SobolevEuclideanZero 2 1 2 Ω)
        : SobolevEuclidean 2 1 2 Ω) =ᵐ[volume.restrict (Ω : Set 𝔼₂)]
        fun x ↦ max (v x) (ψ' x) - v x := by
      filter_upwards [SobolevMultiIndex.fn_sub (w : SobolevEuclidean 2 1 2 Ω) (uh i), hfw, hvh]
        with x h1 h2 h3
      have h1' : SobolevMultiIndex.fn ((w - uh i : SobolevEuclideanZero 2 1 2 Ω)
          : SobolevEuclidean 2 1 2 Ω) x
          = (SobolevMultiIndex.fn (w : SobolevEuclidean 2 1 2 Ω)
            - SobolevMultiIndex.fn (uh i : SobolevEuclidean 2 1 2 Ω)) x := h1
      rw [h1', Pi.sub_apply, h2, h3]
    have hest := hest₀ i ψ' hψ2 hψc
    simp only [Nat.sub_zero] at hest
    rw [eLpNorm_congr_ae hae, hSψ]
    exact toReal_le_of_le_ofReal_mul (by positivity) hSψfin
      ((eLpNorm_max_sub_le (𝒯 i) hψc hvc hvp hψv).trans
        ((eLpNorm_le_sobolevNorm_zero (memSobolev_sub_globalInterp_linear (𝒯 i) hψ2)).trans hest))
  -- `‖Π_h u − u‖₀ ≤ c h² |u|₂`
  have hL2 : (eLpNorm (SobolevMultiIndex.fn ((vh - u : SobolevEuclideanZero 2 1 2 Ω)
      : SobolevEuclidean 2 1 2 Ω)) 2 (volume.restrict (Ω : Set 𝔼₂))).toReal
      ≤ c₀' * (𝒯 i).meshSize ^ 2 * Su := by
    have hae : SobolevMultiIndex.fn ((vh - u : SobolevEuclideanZero 2 1 2 Ω)
        : SobolevEuclidean 2 1 2 Ω) =ᵐ[volume.restrict (Ω : Set 𝔼₂)]
        (𝒯 i).globalInterp referenceTriangleVertex baryCoord u' - u' := by
      filter_upwards [SobolevMultiIndex.fn_sub (vh : SobolevEuclidean 2 1 2 Ω) u, hfvh, hu']
        with x h1 h2 h3
      have h1' : SobolevMultiIndex.fn ((vh - u : SobolevEuclideanZero 2 1 2 Ω)
          : SobolevEuclidean 2 1 2 Ω) x
          = (SobolevMultiIndex.fn (vh : SobolevEuclidean 2 1 2 Ω)
            - SobolevMultiIndex.fn (u : SobolevEuclidean 2 1 2 Ω)) x := h1
      rw [h1', Pi.sub_apply, h2, h3, Pi.sub_apply]
    have hest := hest₀ i u' hu'2 hu'c
    simp only [Nat.sub_zero] at hest
    rw [eLpNorm_congr_ae hae, eLpNorm_sub_comm, hSu]
    exact toReal_le_of_le_ofReal_mul (by positivity) hSufin
      ((eLpNorm_le_sobolevNorm_zero (memSobolev_sub_globalInterp_linear (𝒯 i) hu'2)).trans hest)
  -- `‖u − Π_h u‖₁ ≤ C c h |u|₂`
  have hH1 : ‖u - vh‖ ≤ C * (c₁ * (𝒯 i).meshSize * Su) := by
    have h1 := FiniteElement.norm_sub_le_of_fn_ae_eq hC u vh hu' hfvh
    have hest := hest₁ i u' hu'2 hu'c
    simp only [Nat.add_one_sub_one, pow_one] at hest
    rw [hSu]
    exact h1.trans (mul_le_mul_of_nonneg_left
      (toReal_le_of_le_ofReal_mul (by positivity) hSufin hest) hC0)
  -- assemble: `(c₀/2) ‖u − u_h‖² ≤ K h²`
  have hG0 : 0 ≤ ‖g - f‖ := norm_nonneg _
  have hR1 := hres1.trans (mul_le_mul_of_nonneg_left hL1 hG0)
  have hR2 := hres2.trans (mul_le_mul_of_nonneg_left hL2 hG0)
  have hH1' : ‖u - vh‖ ^ 2 ≤ (C * (c₁ * (𝒯 i).meshSize * Su)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hH1 2
  have hmain : (1 + (2 * R) ^ 2)⁻¹ / 2 * ‖u - uh i‖ ^ 2 ≤ K * (𝒯 i).meshSize ^ 2 := by
    rw [hK]
    refine hfalk.trans ?_
    calc _ ≤ ‖g - f‖ * (c₀' * (𝒯 i).meshSize ^ 2 * Sψ) + ‖g - f‖ * (c₀' * (𝒯 i).meshSize ^ 2 * Su)
          + 1 ^ 2 / (2 * (1 + (2 * R) ^ 2)⁻¹) * (C * (c₁ * (𝒯 i).meshSize * Su)) ^ 2 :=
          add_le_add (add_le_add hR1 hR2) (mul_le_mul_of_nonneg_left hH1' (by positivity))
      _ = _ := by ring
  have key : ∀ e : ℝ, e = 2 / (1 + (2 * R) ^ 2)⁻¹ * ((1 + (2 * R) ^ 2)⁻¹ / 2 * e) := fun e ↦ by
    have hne : (1 + (2 * R) ^ 2 : ℝ) ≠ 0 := by positivity
    field_simp
  have hsq : ‖u - uh i‖ ^ 2 ≤ 2 / (1 + (2 * R) ^ 2)⁻¹ * K * (𝒯 i).meshSize ^ 2 :=
    calc ‖u - uh i‖ ^ 2
        = 2 / (1 + (2 * R) ^ 2)⁻¹ * ((1 + (2 * R) ^ 2)⁻¹ / 2 * ‖u - uh i‖ ^ 2) := key _
      _ ≤ 2 / (1 + (2 * R) ^ 2)⁻¹ * (K * (𝒯 i).meshSize ^ 2) :=
          mul_le_mul_of_nonneg_left hmain (by positivity)
      _ = _ := by ring
  calc ‖u - uh i‖ = Real.sqrt (‖u - uh i‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (2 / (1 + (2 * R) ^ 2)⁻¹ * K * (𝒯 i).meshSize ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (2 / (1 + (2 * R) ^ 2)⁻¹ * K) * (𝒯 i).meshSize := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hh0]


end Example1143

/-! ### Theorem 11.4.5: the Lagrange multiplier of the simplified friction problem -/

section LagrangeMultiplier

open MeasureTheory TopologicalSpace
open scoped ContDiff ENNReal

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))} (B : BoundaryData Ω) (𝒯 : B.TraceFamily)

/-- The Euclidean space $\mathbb{R}^N$, as local notation. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-- **Theorem 11.4.5** of [han2009theoretical] (the Lagrange multiplier of the simplified friction
problem). Let $\Omega \subseteq \mathbb{R}^N$ be open, with boundary data $B$ (a surface measure
$ds$ on $\Gamma = \partial\Omega$) and a boundary trace $\gamma$ given by `𝒯 : B.TraceFamily`.
Let $g > 0$, $f \in L^2(\Omega)$ and $u \in V = H^1(\Omega)$. Then $u$ solves the simplified
friction problem (11.4.10), which is (11.1.13),
$$\int_\Omega \bigl[\nabla u \cdot \nabla (v - u) + u (v - u)\bigr] dx + g \int_\Gamma
  \bigl(|\gamma v| - |\gamma u|\bigr) ds \ge \int_\Omega f (v - u) \, dx \quad \text{for all } v
  \in V,$$
if and only if there is $\lambda \in L^\infty(\Gamma)$ with $|\lambda| \le 1$ a.e. on $\Gamma$
such that
$$\int_\Omega (\nabla u \cdot \nabla v + u v) \, dx + g \int_\Gamma \lambda \, \gamma v \, ds =
  \int_\Omega f v \, dx \quad \text{for all } v \in V, \tag{11.4.21}$$
$$\lambda \, \gamma u = |\gamma u| \quad \text{a.e. on } \Gamma. \tag{11.4.22}$$

**Reading.** The source poses the problem on a Lipschitz domain. Here the domain is any open set
with a boundary trace in the sense of `BoundaryData.TraceFamily`, for example a bounded $C^1$
domain or a polygon without slits.

The multiplier is unique by `AtkinsonHan.Chapter11.theorem_11_4_5_unique`. The proof follows the
source, except that the extension of $L(v) = \ell(v) - a(u, v)$ from the traces to $L^1(\Gamma)$
by the Hahn–Banach theorem, and the duality $(L^1(\Gamma))' = L^\infty(\Gamma)$, need no
fractional space $H^{1/2}(\Gamma)$. It specializes
`forall_le_add_integral_abs_iff_exists_multiplier` with the trace as the operator. -/
theorem theorem_11_4_5 {g : ℝ} (hg : 0 < g) (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)))
    (u : SobolevEuclidean N 1 2 Ω) :
    (∀ v : SobolevEuclidean N 1 2 Ω,
      ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn (v - u) x
        ≤ (∫ x in (Ω : Set 𝔼), ((∑ i, SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
            * SobolevMultiIndex.weakDeriv (v - u) (MultiIndexLE.single i) x)
            + SobolevMultiIndex.fn u x * SobolevMultiIndex.fn (v - u) x))
          + g * ∫ x, (|(𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x|
            - |(𝒯.traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ) x|) ∂B.σ) ↔
      ∃ l : Lp ℝ ⊤ B.σ, (∀ᵐ x ∂B.σ, |l x| ≤ 1) ∧
        (∀ v : SobolevEuclidean N 1 2 Ω,
          (∫ x in (Ω : Set 𝔼), ((∑ i, SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
              * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x)
              + SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x))
            + g * ∫ x, l x * (𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x ∂B.σ
            = ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn v x) ∧
        ∀ᵐ x ∂B.σ, l x * (𝒯.traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ) x
          = |(𝒯.traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ) x| := by
  have h := forall_le_add_integral_abs_iff_exists_multiplier hg
    (𝒯.traceL 2 ENNReal.ofNat_ne_top).toLinearMap (Elliptic.laplaceForm Ω u).toLinearMap
    (Elliptic.load Ω f).toLinearMap u
  simp only [ContinuousLinearMap.coe_coe, Elliptic.laplaceForm_apply, Elliptic.load_apply] at h
  refine (forall_congr' fun v ↦ (friction_ineq_iff B 𝒯 g f u v).trans ?_).trans h
  rw [Elliptic.laplaceForm_apply, Elliptic.load_apply, frictionFunctional_apply,
    frictionFunctional_apply]

/-- **Theorem 11.4.5** of [han2009theoretical], uniqueness of the Lagrange multiplier. Under the
setting of `AtkinsonHan.Chapter11.theorem_11_4_5`, let $g > 0$, $f \in L^2(\Omega)$ and
$u \in H^1(\Omega)$. If $\lambda, \lambda' \in L^\infty(\Gamma)$ both satisfy (11.4.21) for $u$,
then $\lambda = \lambda'$.

The difference $\mu = \lambda - \lambda'$ satisfies $\int_\Gamma \mu \, \gamma v \, ds = 0$ for
all $v \in H^1(\Omega)$. This holds in particular for the restrictions of the smooth compactly
supported functions, whose traces are their boundary values by
`BoundaryData.TraceFamily.traceL_ae_eq`, so $\mu = 0$ almost everywhere on $\Gamma$ by
`ae_eq_zero_of_integral_contDiff_smul_eq_zero`. The density of $H^{1/2}(\Gamma)$ in
$L^2(\Gamma)$ is not needed.

**Reading.** Multiplier uniqueness with abstract trace data.
-/
theorem theorem_11_4_5_unique {g : ℝ} (hg : 0 < g) (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)))
    (u : SobolevEuclidean N 1 2 Ω) {l l' : Lp ℝ ⊤ B.σ}
    (hl : ∀ v : SobolevEuclidean N 1 2 Ω,
      (∫ x in (Ω : Set 𝔼), ((∑ i, SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
          * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x)
          + SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x))
        + g * ∫ x, l x * (𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x ∂B.σ
        = ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn v x)
    (hl' : ∀ v : SobolevEuclidean N 1 2 Ω,
      (∫ x in (Ω : Set 𝔼), ((∑ i, SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
          * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x)
          + SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x))
        + g * ∫ x, l' x * (𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x ∂B.σ
        = ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn v x) :
    l = l' := by
  have hIl : ∀ (l : Lp ℝ ⊤ B.σ) (k : Lp ℝ 2 B.σ), Integrable (fun x ↦ l x * k x) B.σ :=
    fun l k ↦ (Lp.memLp l).integrable_mul ((Lp.memLp k).mono_exponent one_le_two)
  -- `∫ (l − l') γ v dσ = 0` for all `v`
  have hdiff : ∀ v : SobolevEuclidean N 1 2 Ω,
      ∫ x, (l - l' : Lp ℝ ⊤ B.σ) x * (𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x ∂B.σ = 0 := by
    intro v
    have h1 := hl v
    have h2 := hl' v
    have e : ∫ x, (l - l' : Lp ℝ ⊤ B.σ) x * (𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x ∂B.σ
        = (∫ x, l x * (𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x ∂B.σ)
          - ∫ x, l' x * (𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x ∂B.σ := by
      rw [← integral_sub (hIl l _) (hIl l' _)]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub l l'] with x hx
      rw [hx, Pi.sub_apply, sub_mul]
    rw [e]
    have : g * ((∫ x, l x * (𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x ∂B.σ)
        - ∫ x, l' x * (𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x ∂B.σ) = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hg.ne'
  -- hence against every smooth compactly supported function
  have hsm : ∀ ψ : 𝔼 → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ x, ψ x • (l - l' : Lp ℝ ⊤ B.σ) x ∂B.σ = 0 := by
    intro ψ hψ hψc
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
    obtain ⟨W, hW⟩ : ∃ W : SobolevEuclidean N 1 2 Ω,
        SobolevMultiIndex.fn W =ᵐ[volume.restrict (Ω : Set 𝔼)] ψ :=
      hψ1.exists_sobolevMultiIndex_of_hasCompactSupport' hψc
    have hγW := 𝒯.traceL_ae_eq 2 ENNReal.ofNat_ne_top W ψ hW hψ.continuous.continuousOn
    rw [← hdiff W]
    refine integral_congr_ae ?_
    filter_upwards [hγW] with x hx
    rw [hx, smul_eq_mul, mul_comm]
  have hloc : LocallyIntegrable (l - l' : Lp ℝ ⊤ B.σ) B.σ :=
    ((Lp.memLp (l - l')).integrable le_top).locallyIntegrable
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc hsm
  rw [← sub_eq_zero]
  refine Lp.eq_zero_iff_ae_eq_zero.2 ?_
  filter_upwards [hae] with x hx
  exact hx

end LagrangeMultiplier

/-!
### Example 11.4.4: the friction problem with linear elements on a polygon

The error estimate $\|u - u_h\|_{H^1(\Omega)} \le c(u) h$ for the linear finite element solution of
the simplified friction problem (11.1.13), which is (11.4.10), on a polygon. The section has three
parts: the residual of the continuous solution, computed by Green's formula for any boundary data;
the $L^2(\Gamma)$ error of the linear interpolant on a triangulated polygon; and the assembly
through Falk's lemma.
-/

section Residual

open MeasureTheory TopologicalSpace SobolevMultiIndex

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))} {B : BoundaryData Ω} (𝒯 : B.TraceFamily)

/-- The Euclidean space $\mathbb{R}^N$, as local notation. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-- The standard basis of $\mathbb{R}^N$, as local notation. -/
local notation "𝔅" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin N) ℝ)

/-- **Example 11.4.4** of [han2009theoretical], the weak Laplacian. For $u \in H^2(\Omega)$,
$\Omega \subseteq \mathbb{R}^N$ open, the **weak Laplacian** is
$$\Delta u = \sum_{i} \partial_i (\partial_i u) \in L^2(\Omega),$$
with weak derivatives. -/
noncomputable def weakLaplacian (U : SobolevEuclidean N 2 2 Ω) :
    Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)) :=
  ∑ i, weakDeriv (partialDerivL ℝ 𝔅 2 Ω volume i U) (MultiIndexLE.single i)

/-- **Example 11.4.4** of [han2009theoretical], the datum of the residual. For $u \in H^2(\Omega)$
and $f \in L^2(\Omega)$, this is the function $-\Delta u + u - f \in L^2(\Omega)$, with the weak
Laplacian $\Delta u$. -/
noncomputable def frictionResidualData (U : SobolevEuclidean N 2 2 Ω)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)) :=
  -weakLaplacian U + weakDeriv U 0 - f

/-- **Example 11.4.4** of [han2009theoretical], Green's formula for the residual. Let
$\Omega \subseteq \mathbb{R}^N$ be open, with boundary data $B$ and a boundary trace $\gamma$
given by `𝒯 : B.TraceFamily`. Let $u \in H^2(\Omega)$, viewed in $H^1(\Omega)$, and
$f \in L^2(\Omega)$. Then for every $w \in H^1(\Omega)$,
$$a(u, w) - \ell(w) = \int_\Gamma \frac{\partial u}{\partial \nu} \, \gamma w \, ds +
  \int_\Omega (-\Delta u + u - f) \, w \, dx,$$
where $a(u, w) = \int_\Omega (\nabla u \cdot \nabla w + u w)$ and $\ell(w) = \int_\Omega f w$.

The normal derivative is `BoundaryData.TraceFamily.normalTrace`. The form is
`Elliptic.laplaceForm` and the load is `Elliptic.load`.

**Reading.** Green's identity with the supplied boundary trace and weak normal trace.
-/
theorem laplaceForm_sub_load_eq_normalTrace_add (U : SobolevEuclidean N 2 2 Ω)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) (w : SobolevEuclidean N 1 2 Ω) :
    Elliptic.laplaceForm Ω (toLowerOrderL ℝ 𝔅 2 Ω volume (by norm_num : (1 : ℕ) ≤ 2) U) w
        - Elliptic.load Ω f w
      = (∫ x, 𝒯.normalTrace U x * (𝒯.traceL 2 ENNReal.ofNat_ne_top w : 𝔼 → ℝ) x ∂B.σ)
        + Elliptic.load Ω (frictionResidualData U f) w := by
  have hgreen := 𝒯.green_laplacian U w
  have hI1 : Integrable (fun x ↦ ∑ i, (weakDeriv U (MultiIndexLE.singleLE i) : 𝔼 → ℝ) x
      * (weakDeriv w (MultiIndexLE.single i) : 𝔼 → ℝ) x)
      (volume.restrict (Ω : Set 𝔼)) :=
    integrable_finsetSum _ fun i _ ↦ (Lp.memLp _).integrable_mul (Lp.memLp _)
  have hI2 : Integrable (fun x ↦ fn U x * fn w x) (volume.restrict (Ω : Set 𝔼)) :=
    (Lp.memLp (weakDeriv U 0)).integrable_mul (Lp.memLp (weakDeriv w 0))
  have hI3 : Integrable (fun x ↦ f x * fn w x) (volume.restrict (Ω : Set 𝔼)) :=
    (Lp.memLp f).integrable_mul (Lp.memLp (weakDeriv w 0))
  have hI4 : Integrable (fun x ↦ (weakLaplacian U : 𝔼 → ℝ) x * fn w x)
      (volume.restrict (Ω : Set 𝔼)) :=
    (Lp.memLp _).integrable_mul (Lp.memLp (weakDeriv w 0))
  -- the weak Laplacian, as a function
  have hD : (weakLaplacian U : 𝔼 → ℝ) =ᵐ[volume.restrict (Ω : Set 𝔼)]
      fun x ↦ ∑ i, (weakDeriv (partialDerivL ℝ 𝔅 2 Ω volume i U) (MultiIndexLE.single i) :
        𝔼 → ℝ) x := by
    have h := Lp.coeFn_finsetSum Finset.univ
      (fun i ↦ weakDeriv (partialDerivL ℝ 𝔅 2 Ω volume i U) (MultiIndexLE.single i))
    rw [weakLaplacian]
    filter_upwards [h] with x hx
    rw [hx, Finset.sum_apply]
  have hgreen' : (∫ x in (Ω : Set 𝔼), (weakLaplacian U : 𝔼 → ℝ) x * fn w x)
      + ∫ x in (Ω : Set 𝔼), ∑ i, (weakDeriv U (MultiIndexLE.singleLE i) : 𝔼 → ℝ) x
          * (weakDeriv w (MultiIndexLE.single i) : 𝔼 → ℝ) x
      = ∫ x, 𝒯.normalTrace U x * (𝒯.traceL 2 ENNReal.ofNat_ne_top w : 𝔼 → ℝ) x ∂B.σ := by
    have e : ∫ x in (Ω : Set 𝔼), (weakLaplacian U : 𝔼 → ℝ) x * fn w x
        = ∫ x in (Ω : Set 𝔼), (∑ i, (weakDeriv (partialDerivL ℝ 𝔅 2 Ω volume i U)
            (MultiIndexLE.single i) : 𝔼 → ℝ) x) * fn w x :=
      integral_congr_ae (hD.mono fun x hx ↦ by dsimp only; rw [hx])
    rw [e, hgreen]
  -- the left-hand side
  have hlhs : Elliptic.laplaceForm Ω (toLowerOrderL ℝ 𝔅 2 Ω volume (by norm_num : (1 : ℕ) ≤ 2) U) w
      = (∫ x in (Ω : Set 𝔼), ∑ i, (weakDeriv U (MultiIndexLE.singleLE i) : 𝔼 → ℝ) x
          * (weakDeriv w (MultiIndexLE.single i) : 𝔼 → ℝ) x)
        + ∫ x in (Ω : Set 𝔼), fn U x * fn w x := by
    rw [Elliptic.laplaceForm_apply, ← integral_add hI1 hI2]
    rfl
  -- the residual datum, as a function
  have hR : (frictionResidualData U f : 𝔼 → ℝ) =ᵐ[volume.restrict (Ω : Set 𝔼)]
      fun x ↦ -(weakLaplacian U : 𝔼 → ℝ) x + fn U x - f x := by
    filter_upwards [Lp.coeFn_sub (-weakLaplacian U + weakDeriv U 0) f,
      Lp.coeFn_add (-weakLaplacian U) (weakDeriv U 0), Lp.coeFn_neg (weakLaplacian U)]
      with x h1 h2 h3
    simp only [frictionResidualData, h1, Pi.sub_apply, h2, Pi.add_apply, h3, Pi.neg_apply]
    rfl
  have hrhs : Elliptic.load Ω (frictionResidualData U f) w
      = -(∫ x in (Ω : Set 𝔼), (weakLaplacian U : 𝔼 → ℝ) x * fn w x)
        + (∫ x in (Ω : Set 𝔼), fn U x * fn w x) - ∫ x in (Ω : Set 𝔼), f x * fn w x := by
    have e : ∫ x in (Ω : Set 𝔼), (frictionResidualData U f : 𝔼 → ℝ) x * fn w x
        = ∫ x in (Ω : Set 𝔼), (-(weakLaplacian U : 𝔼 → ℝ) x + fn U x - f x) * fn w x :=
      integral_congr_ae (hR.mono fun x hx ↦ by dsimp only; rw [hx])
    have hI4' : Integrable (fun x ↦ -((weakLaplacian U : 𝔼 → ℝ) x * fn w x))
        (volume.restrict (Ω : Set 𝔼)) := hI4.neg
    have hI5 : Integrable (fun x ↦ -((weakLaplacian U : 𝔼 → ℝ) x * fn w x) + fn U x * fn w x)
        (volume.restrict (Ω : Set 𝔼)) := hI4'.add hI2
    have e2 : ∫ x in (Ω : Set 𝔼), (-(weakLaplacian U : 𝔼 → ℝ) x + fn U x - f x) * fn w x
        = (∫ x in (Ω : Set 𝔼), (-((weakLaplacian U : 𝔼 → ℝ) x * fn w x) + fn U x * fn w x))
          - ∫ x in (Ω : Set 𝔼), f x * fn w x := by
      rw [← integral_sub hI5 hI3]
      exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
    have e3 : (∫ x in (Ω : Set 𝔼), (-((weakLaplacian U : 𝔼 → ℝ) x * fn w x) + fn U x * fn w x))
        = -(∫ x in (Ω : Set 𝔼), (weakLaplacian U : 𝔼 → ℝ) x * fn w x)
          + ∫ x in (Ω : Set 𝔼), fn U x * fn w x := by
      rw [integral_add hI4' hI2, integral_neg]
    rw [Elliptic.load_apply, e, e2, e3]
  rw [hlhs, hrhs, Elliptic.load_apply, ← hgreen']
  ring

/-- **Example 11.4.4** of [han2009theoretical], the normal derivative $\partial u / \partial \nu$ of
$u \in H^2(\Omega)$ as an element of $L^2(\Gamma)$, so that
$\|\partial u / \partial \nu\|_{L^2(\Gamma)}$ is a norm.

**Reading.** Uses the boundary data's L² normal trace on the H² representative.
-/
noncomputable def normalTraceL (U : SobolevEuclidean N 2 2 Ω) : Lp ℝ 2 B.σ :=
  (𝒯.memLp_normalTrace U).toLp _

/-- **Example 11.4.4** of [han2009theoretical], the bound on the residual. Let
$\Omega \subseteq \mathbb{R}^N$ be open, with boundary data $B$ and a boundary trace $\gamma$
given by `𝒯 : B.TraceFamily`. Let $g \ge 0$, let $u \in H^1(\Omega)$ be the image of
$U \in H^2(\Omega)$, and let $f \in L^2(\Omega)$. With $a$, $\ell$ and
$j(v) = g \int_\Gamma |\gamma v| \, ds$ as in the friction problem, for every
$v \in H^1(\Omega)$,
$$|a(u, v - u) + j(v) - j(u) - \ell(v - u)| \le \Bigl(\Bigl\|\frac{\partial u}{\partial
  \nu}\Bigr\|_{L^2(\Gamma)} + g \sqrt{\operatorname{meas} \Gamma}\Bigr) \|\gamma(v -
  u)\|_{L^2(\Gamma)} + \|-\Delta u + u - f\|_{L^2(\Omega)} \|v - u\|_{L^2(\Omega)}.$$

The left side is the residual $R(v, u)$ of Falk's lemma. The number
$\sqrt{\operatorname{meas} \Gamma}$ is the $L^2$ norm of the constant $1$ for the surface
measure. The proof uses `AtkinsonHan.Chapter11.laplaceForm_sub_load_eq_normalTrace_add`, the
Cauchy–Schwarz inequality on $\Gamma$ and on $\Omega$, and $\bigl||\gamma v| - |\gamma u|\bigr|
\le |\gamma (v - u)|$.

**Reading.** Volume and boundary residual bound using supplied trace data and Sobolev
representative.
-/
theorem abs_residual_le {g : ℝ} (hg : 0 ≤ g) {U : SobolevEuclidean N 2 2 Ω}
    {u : SobolevEuclidean N 1 2 Ω}
    (hU : toLowerOrderL ℝ 𝔅 2 Ω volume (by norm_num : (1 : ℕ) ≤ 2) U = u)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) (v : SobolevEuclidean N 1 2 Ω) :
    |Elliptic.laplaceForm Ω u (v - u) + frictionFunctional B 𝒯 g v
        - frictionFunctional B 𝒯 g u - Elliptic.load Ω f (v - u)|
      ≤ (‖normalTraceL 𝒯 U‖ + g * (eLpNorm (fun _ : 𝔼 ↦ (1 : ℝ)) 2 B.σ).toReal)
          * ‖𝒯.traceL 2 ENNReal.ofNat_ne_top (v - u)‖
        + ‖frictionResidualData U f‖ * ‖weakDeriv (v - u) 0‖ := by
  have hI : ∀ k : Lp ℝ 2 B.σ, Integrable (fun x ↦ |k x|) B.σ := fun k ↦
    ((Lp.memLp k).integrable one_le_two).abs
  have hgreen := laplaceForm_sub_load_eq_normalTrace_add 𝒯 U f (v - u)
  rw [hU] at hgreen
  -- the boundary term
  have hnt : (∫ x, 𝒯.normalTrace U x * (𝒯.traceL 2 ENNReal.ofNat_ne_top (v - u) : 𝔼 → ℝ) x ∂B.σ)
      = ⟪normalTraceL 𝒯 U, 𝒯.traceL 2 ENNReal.ofNat_ne_top (v - u)⟫_ℝ := by
    rw [L2.inner_eq_integral_mul]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (𝒯.memLp_normalTrace U)] with x hx
    rw [normalTraceL, hx]
  have hnt' : |∫ x, 𝒯.normalTrace U x
      * (𝒯.traceL 2 ENNReal.ofNat_ne_top (v - u) : 𝔼 → ℝ) x ∂B.σ|
      ≤ ‖normalTraceL 𝒯 U‖ * ‖𝒯.traceL 2 ENNReal.ofNat_ne_top (v - u)‖ := by
    rw [hnt]
    exact abs_real_inner_le_norm _ _
  -- the friction term
  have hjdiff : |frictionFunctional B 𝒯 g v - frictionFunctional B 𝒯 g u|
      ≤ g * (eLpNorm (fun _ : 𝔼 ↦ (1 : ℝ)) 2 B.σ).toReal
        * ‖𝒯.traceL 2 ENNReal.ofNat_ne_top (v - u)‖ := by
    have hsub : (𝒯.traceL 2 ENNReal.ofNat_ne_top (v - u) : 𝔼 → ℝ)
        =ᵐ[B.σ] fun x ↦ (𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x
          - (𝒯.traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ) x := by
      rw [map_sub]
      filter_upwards [Lp.coeFn_sub (𝒯.traceL 2 ENNReal.ofNat_ne_top v)
        (𝒯.traceL 2 ENNReal.ofNat_ne_top u)] with x hx
      rw [hx, Pi.sub_apply]
    have hle : |(∫ x, |(𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x| ∂B.σ)
        - ∫ x, |(𝒯.traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ) x| ∂B.σ|
        ≤ ∫ x, |(𝒯.traceL 2 ENNReal.ofNat_ne_top (v - u) : 𝔼 → ℝ) x| ∂B.σ := by
      rw [← integral_sub (hI _) (hI _)]
      refine (abs_integral_le_integral_abs).trans (integral_mono_ae (((hI _).sub (hI _)).abs)
        (hI _) ?_)
      filter_upwards [hsub] with x hx
      rw [hx]
      exact abs_abs_sub_abs_le_abs_sub _ _
    have hfin := integral_abs_le_mul_norm B (𝒯.traceL 2 ENNReal.ofNat_ne_top (v - u))
    rw [frictionFunctional_apply, frictionFunctional_apply, ← mul_sub, abs_mul, abs_of_nonneg hg,
      mul_assoc]
    exact mul_le_mul_of_nonneg_left (hle.trans hfin) hg
  -- the interior term
  have hload : |Elliptic.load Ω (frictionResidualData U f) (v - u)|
      ≤ ‖frictionResidualData U f‖ * ‖weakDeriv (v - u) 0‖ :=
    Elliptic.abs_load_le Ω _ _
  have hsplit : Elliptic.laplaceForm Ω u (v - u) + frictionFunctional B 𝒯 g v
      - frictionFunctional B 𝒯 g u - Elliptic.load Ω f (v - u)
      = ((∫ x, 𝒯.normalTrace U x * (𝒯.traceL 2 ENNReal.ofNat_ne_top (v - u) : 𝔼 → ℝ) x ∂B.σ)
          + Elliptic.load Ω (frictionResidualData U f) (v - u))
        + (frictionFunctional B 𝒯 g v - frictionFunctional B 𝒯 g u) := by
    rw [← hgreen]; ring
  rw [hsplit]
  calc |((∫ x, 𝒯.normalTrace U x
        * (𝒯.traceL 2 ENNReal.ofNat_ne_top (v - u) : 𝔼 → ℝ) x ∂B.σ)
          + Elliptic.load Ω (frictionResidualData U f) (v - u))
        + (frictionFunctional B 𝒯 g v - frictionFunctional B 𝒯 g u)|
      ≤ (|∫ x, 𝒯.normalTrace U x * (𝒯.traceL 2 ENNReal.ofNat_ne_top (v - u) : 𝔼 → ℝ) x ∂B.σ|
          + |Elliptic.load Ω (frictionResidualData U f) (v - u)|)
        + |frictionFunctional B 𝒯 g v - frictionFunctional B 𝒯 g u| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (‖normalTraceL 𝒯 U‖ * ‖𝒯.traceL 2 ENNReal.ofNat_ne_top (v - u)‖
          + ‖frictionResidualData U f‖ * ‖weakDeriv (v - u) 0‖)
        + g * (eLpNorm (fun _ : 𝔼 ↦ (1 : ℝ)) 2 B.σ).toReal
          * ‖𝒯.traceL 2 ENNReal.ofNat_ne_top (v - u)‖ :=
        add_le_add (add_le_add hnt' hload) hjdiff
    _ = _ := by ring

end Residual


/-! ### Example 11.4.4: the error estimate -/

section Example1144

open MeasureTheory TopologicalSpace EuclideanSpace SobolevMultiIndex

/-- The Euclidean plane $\mathbb{R}^2$, as local notation. -/
local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-- The standard basis of $\mathbb{R}^2$, as local notation. -/
local notation "𝔅₂" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin 2) ℝ)

/-- **Example 11.4.4** of [han2009theoretical] (the friction problem with linear elements). Let
$\Omega \subseteq \mathbb{R}^2$ be open. Let $(\mathcal{T}_i)_{i \in \iota}$ be a regular family
of triangulations of $\Omega$ along a filter $l$, without slits, with mesh sizes $h_i \le H$.
Let $P_k \neq Q_k$, for $k$ in a finite set, be the ends of the sides of the polygon, and let
every boundary edge of every $\mathcal{T}_i$ lie in one of the segments $[P_k, Q_k]$. Let
$g > 0$ and $f \in L^2(\Omega)$. Let $u \in H^1(\Omega)$ be the image of $U \in H^2(\Omega)$,
let $u$ have a representative $\tilde u$ that is continuous on $\overline\Omega$ and lies in
$H^2(\Omega)$, and for every side let $r \mapsto \tilde u(P_k + r (Q_k - P_k))$ be almost
everywhere equal on $(0, 1)$ to an element of $H^2(0, 1)$. Let $M_\nu$ and $M_\sigma$ bound
$\|\partial u / \partial \nu\|_{L^2(\Gamma)}$ and $\sqrt{\operatorname{meas} \Gamma}$ for the
surface measure of every $\mathcal{T}_i$. Let $u$ solve the friction problem (11.4.10),
$$a(u, v - u) + j(v) - j(u) \ge \ell(v - u) \quad \text{for all } v \in H^1(\Omega),$$
with $a(u, v) = \int_\Omega (\nabla u \cdot \nabla v + u v)$, $\ell(v) = \int_\Omega f v$ and
$j(v) = g \int_\Gamma |\gamma v| \, ds$ for the trace of every $\mathcal{T}_i$. For every $i$,
let $u_{h,i}$ in the space $V_{h,i} \subseteq H^1(\Omega)$ of continuous piecewise linear
functions on $\mathcal{T}_i$ solve the same inequality for all $v_h \in V_{h,i}$. Then there is
a constant $c$ with
$$\|u - u_{h,i}\|_{H^1(\Omega)} \le c h_i \quad \text{for all } i.$$

**Reading.** The source assumes $u \in H^2(\Omega)$ and $u|_{\Gamma_k} \in H^2(\Gamma_k)$ on
every side; here these are the explicit representatives $U$, $\tilde u$ and the elements of
$H^2(0, 1)$. The source leaves two hypotheses implicit. The first is that every boundary edge
lies on one of finitely many sides, which is what a polygonal domain means for the boundary
terms. This condition takes the place of `Triangulation.FrontierSubsetEdges` of Example 11.4.3,
which this proof does not use. The second is that $\|\partial u / \partial \nu\|_{L^2(\Gamma)}$
and $\sqrt{\operatorname{meas} \Gamma}$ are bounded uniformly in $h$: each mesh carries its own
surface measure, and for a fixed polygon these numbers are the same for every mesh.

The space $V_{h,i}$ is `Triangulation.polySpace 2 1`, "without slits" is
`Triangulation.InteriorEdgesSubset`, and the boundary data and trace of a mesh are
`Triangulation.boundaryData` and `Triangulation.traceFamily`. The proof follows the source and
gives $c = \sqrt{2 K}$ with
$$K = (M_\nu + g M_\sigma) \Bigl(\sum_k \|Q_k - P_k\|^{-3} |u|^2_{H^2(\Gamma_k)}\Bigr)^{1/2} +
  \|-\Delta u + u - f\|_{L^2(\Omega)} c_0 |u|_{H^2(\Omega)} + \tfrac12 \bigl(C c_1
  |u|_{H^2(\Omega)}\bigr)^2,$$
where $c_0$ and $c_1$ are the interpolation constants of
`AtkinsonHan.Chapter10.theorem_10_3_9_linear`, in which the shape regularity enters, and $C$ is
the norm comparison of `FiniteElement.exists_norm_le_sobolevNorm`. It applies Falk's lemma at
$v_h = \Pi_h \tilde u$, in the internal-approximation form
`norm_sub_le_of_isVariationalInequalitySolution_of_subset` since $V_h \subseteq V$. The residual
is bounded by `AtkinsonHan.Chapter11.abs_residual_le`, the interpolation errors $\|u - \Pi_h
u\|_{m,\Omega} \le c h^{2-m} |u|_{2,\Omega}$ for $m = 0, 1$ by Theorem 10.3.9, and on the
boundary $\gamma(u - \Pi_h u) = \tilde u - \Pi_h \tilde u$ with $\|\tilde u - \Pi_h \tilde
u\|_{L^2(\Gamma)} \le h^2 \bigl(\sum_k \|Q_k - P_k\|^{-3} |u|^2_{H^2(\Gamma_k)}\bigr)^{1/2}$ by
`Triangulation.norm_traceL_sub_globalInterp_le`. -/
theorem example_11_4_4 {Ω : Opens 𝔼₂} {ι : Type*} {l : Filter ι} {𝒯 : ι → Triangulation Ω}
    (hreg : Chapter10.IsRegularFamily l fun i ↦ Set.range (𝒯 i).K) {H : ℝ}
    (hH : ∀ i, (𝒯 i).meshSize ≤ H) (hIe : ∀ i, (𝒯 i).InteriorEdgesSubset)
    {κ : Type*} [Finite κ] {P Q : κ → 𝔼₂} (hPQ : ∀ k, P k ≠ Q k)
    (hside : ∀ (i : ι) (T : (𝒯 i).elems) (a : Fin 3), (𝒯 i).IsBoundaryEdge T a →
      ∃ k, segment ℝ (T.1 a) (T.1 (a + 1)) ⊆ segment ℝ (P k) (Q k))
    {g : ℝ} (hg : 0 < g) (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼₂)))
    {U₂ : SobolevEuclidean 2 2 2 Ω} {u : SobolevEuclidean 2 1 2 Ω}
    (hU : toLowerOrderL ℝ 𝔅₂ 2 Ω volume (by norm_num : (1 : ℕ) ≤ 2) U₂ = u)
    {ũ : 𝔼₂ → ℝ} (hũ : fn u =ᵐ[volume.restrict (Ω : Set 𝔼₂)] ũ)
    (hũc : ContinuousOn ũ (closure (Ω : Set 𝔼₂))) (hũ2 : MemSobolev ũ 2 2 Ω volume)
    (Us : κ → SobolevInterval 2 0 1)
    (hUs : ∀ k, SobolevInterval.fn (Us k) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun r ↦ ũ (AffineMap.lineMap (P k) (Q k) r))
    {Mν Mσ : ℝ} (hMν : ∀ i, ‖normalTraceL ((𝒯 i).traceFamily (hIe i)) U₂‖ ≤ Mν)
    (hMσ : ∀ i, (eLpNorm (fun _ : 𝔼₂ ↦ (1 : ℝ)) 2 ((𝒯 i).boundaryData).σ).toReal ≤ Mσ)
    (hu : ∀ (i : ι) (v : SobolevEuclidean 2 1 2 Ω),
      Elliptic.load Ω f (v - u) ≤ Elliptic.laplaceForm Ω u (v - u)
        + frictionFunctional (𝒯 i).boundaryData ((𝒯 i).traceFamily (hIe i)) g v
        - frictionFunctional (𝒯 i).boundaryData ((𝒯 i).traceFamily (hIe i)) g u)
    {uh : ι → SobolevEuclidean 2 1 2 Ω}
    (huh : ∀ i, uh i ∈ (𝒯 i).polySpace 2 1 ∧ ∀ vh ∈ (𝒯 i).polySpace 2 1,
      Elliptic.load Ω f (vh - uh i) ≤ Elliptic.laplaceForm Ω (uh i) (vh - uh i)
        + frictionFunctional (𝒯 i).boundaryData ((𝒯 i).traceFamily (hIe i)) g vh
        - frictionFunctional (𝒯 i).boundaryData ((𝒯 i).traceFamily (hIe i)) g (uh i)) :
    ∃ c : ℝ, ∀ i, ‖u - uh i‖ ≤ c * (𝒯 i).meshSize := by
  classical
  have : Fintype κ := Fintype.ofFinite κ
  -- the interpolation constants of Theorem 10.3.9 and the norm comparison
  obtain ⟨c₁, hc₁, hest₁⟩ := Chapter10.theorem_10_3_9_linear (m := 1) le_rfl hreg hH
  obtain ⟨c₀', hc₀', hest₀⟩ := Chapter10.theorem_10_3_9_linear (m := 0) (by norm_num) hreg hH
  obtain ⟨C, hC0, hC⟩ := FiniteElement.exists_norm_le_sobolevNorm Ω
  obtain ⟨Su, hSu⟩ : ∃ Su : ℝ, Su = (sobolevSeminorm ũ 2 2 Ω volume).toReal := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℝ,
      S = ∑ k, ‖Q k - P k‖⁻¹ ^ 3 * SobolevInterval.seminorm 2 0 1 (Us k) ^ 2 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (Mν + g * Mσ) * Real.sqrt S
      + ‖frictionResidualData U₂ f‖ * (c₀' * Su) + 1 / 2 * (C * (c₁ * Su)) ^ 2 := ⟨_, rfl⟩
  have hSu0 : 0 ≤ Su := hSu ▸ ENNReal.toReal_nonneg
  have hSufin : sobolevSeminorm ũ 2 2 Ω volume ≠ ⊤ := hũ2.sobolevSeminorm_ne_top
  refine ⟨Real.sqrt (2 * K), fun i ↦ ?_⟩
  have hh0 : 0 ≤ (𝒯 i).meshSize := (𝒯 i).meshSize_nonneg
  have hMν0 : 0 ≤ Mν := (norm_nonneg _).trans (hMν i)
  have hMσ0 : 0 ≤ Mσ := ENNReal.toReal_nonneg.trans (hMσ i)
  have hK0 : 0 ≤ K := by
    have h1 : 0 ≤ (Mν + g * Mσ) * Real.sqrt S :=
      mul_nonneg (add_nonneg hMν0 (mul_nonneg hg.le hMσ0)) (Real.sqrt_nonneg _)
    have h2 : 0 ≤ ‖frictionResidualData U₂ f‖ * (c₀' * Su) :=
      mul_nonneg (norm_nonneg _) (mul_nonneg hc₀' hSu0)
    have h3 : 0 ≤ 1 / 2 * (C * (c₁ * Su)) ^ 2 := by positivity
    rw [hK]; linarith
  -- the interpolant `Π_h ũ ∈ V_h`
  have hcont := (𝒯 i).continuousOn_globalInterp referenceTriangleVertex baryCoord
    (𝒯 i).isConformingElement_linear (fun j ↦ (contDiff_baryCoord j).continuous) ũ
  have hpoly := (𝒯 i).globalInterp_isPiecewisePoly (𝒯 i).isConformingElement_linear
    baryCoord_eq_eval ũ
  obtain ⟨vh, hvhmem, hvhfn⟩ := (𝒯 i).exists_mem_polySpace 2 hcont hpoly
  have hvhsub : fn (vh - u) =ᵐ[volume.restrict (Ω : Set 𝔼₂)]
      (𝒯 i).globalInterp referenceTriangleVertex baryCoord ũ - ũ := by
    refine (fn_sub vh u).trans ?_
    filter_upwards [hvhfn, hũ] with x h1 h2
    simp only [Pi.sub_apply, h1, h2]
  have hsubfn : fn (u - vh) =ᵐ[volume.restrict (Ω : Set 𝔼₂)]
      ũ - (𝒯 i).globalInterp referenceTriangleVertex baryCoord ũ := by
    refine (fn_sub u vh).trans ?_
    filter_upwards [hvhfn, hũ] with x h1 h2
    simp only [Pi.sub_apply, h1, h2]
  -- the two variational inequalities in operator form, and Falk's lemma
  have hM := frictionBilinForm_isBoundedWith (Ω := Ω)
  have hα := frictionBilinForm_isEllipticWith (Ω := Ω)
  have hmono := Chapter08.stronglyMonotone_toOperator hM hα
  have hlip := Chapter08.lipschitzWith_toOperator zero_le_one hM
  have huVI : IsVariationalInequalitySolution
      (BilinForm.toOperator (frictionBilinForm (Ω := Ω)) hM)
      (frictionFunctional (𝒯 i).boundaryData ((𝒯 i).traceFamily (hIe i)) g)
      (SesqForm.rieszRep (Elliptic.load Ω f)) univ u := by
    rw [Chapter11.isVariationalInequalitySolution_toOperator_iff]
    exact ⟨mem_univ u, fun v _ ↦ hu i v⟩
  have huhVI : IsVariationalInequalitySolution
      (BilinForm.toOperator (frictionBilinForm (Ω := Ω)) hM)
      (frictionFunctional (𝒯 i).boundaryData ((𝒯 i).traceFamily (hIe i)) g)
      (SesqForm.rieszRep (Elliptic.load Ω f))
      ((𝒯 i).polySpace 2 1 : Set (SobolevEuclidean 2 1 2 Ω)) (uh i) := by
    rw [Chapter11.isVariationalInequalitySolution_toOperator_iff]
    exact ⟨(huh i).1, fun v hv ↦ (huh i).2 v hv⟩
  have hfalk := norm_sub_le_of_isVariationalInequalitySolution_of_subset (c := 1) (L := 1)
    one_pos hmono hlip huVI huhVI (mem_univ _) hvhmem
  simp only [BilinForm.inner_toOperator, BilinForm.inner_rieszRep, frictionBilinForm_apply]
    at hfalk
  -- the residual at `v_h = Π_h ũ`
  have hres := abs_residual_le ((𝒯 i).traceFamily (hIe i)) hg.le hU f vh
  -- the boundary error
  have hT := (𝒯 i).norm_traceL_sub_globalInterp_le (hIe i) hPQ (hside i) hũc Us hUs hvhsub
  rw [← hS] at hT
  -- the `L²(Ω)` error
  have hL2 : ‖weakDeriv (vh - u) 0‖ ≤ c₀' * (𝒯 i).meshSize ^ 2 * Su := by
    have hest := hest₀ i ũ hũ2 hũc
    simp only [Nat.sub_zero] at hest
    have hnorm : ‖weakDeriv (vh - u) 0‖
        = (eLpNorm (fn (vh - u)) 2 (volume.restrict (Ω : Set 𝔼₂))).toReal := Lp.norm_def _
    rw [hnorm, eLpNorm_congr_ae hvhsub, eLpNorm_sub_comm, hSu]
    exact toReal_le_of_le_ofReal_mul (by positivity) hSufin
      ((eLpNorm_le_sobolevNorm_zero (memSobolev_sub_globalInterp_linear (𝒯 i) hũ2)).trans hest)
  -- the `H¹(Ω)` error
  have hH1 : ‖u - vh‖ ≤ C * (c₁ * (𝒯 i).meshSize * Su) := by
    have h1 := hC (u - vh)
    rw [sobolevNorm_congr_ae hsubfn] at h1
    have hest := hest₁ i ũ hũ2 hũc
    simp only [Nat.add_one_sub_one, pow_one] at hest
    rw [hSu]
    exact h1.trans (mul_le_mul_of_nonneg_left
      (toReal_le_of_le_ofReal_mul (by positivity) hSufin hest) hC0)
  -- assemble
  have hR : Elliptic.laplaceForm Ω u (vh - u)
      + frictionFunctional (𝒯 i).boundaryData ((𝒯 i).traceFamily (hIe i)) g vh
      - frictionFunctional (𝒯 i).boundaryData ((𝒯 i).traceFamily (hIe i)) g u
      - Elliptic.load Ω f (vh - u)
      ≤ (Mν + g * Mσ) * ((𝒯 i).meshSize ^ 2 * Real.sqrt S)
        + ‖frictionResidualData U₂ f‖ * (c₀' * (𝒯 i).meshSize ^ 2 * Su) := by
    refine (le_abs_self _).trans (hres.trans (add_le_add ?_ ?_))
    · exact mul_le_mul (add_le_add (hMν i) (mul_le_mul_of_nonneg_left (hMσ i) hg.le)) hT
        (norm_nonneg _) (add_nonneg hMν0 (mul_nonneg hg.le hMσ0))
    · exact mul_le_mul_of_nonneg_left hL2 (norm_nonneg _)
  have hsq : ‖u - vh‖ ^ 2 ≤ (C * (c₁ * (𝒯 i).meshSize * Su)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hH1 2
  have hmain : 1 / 2 * ‖u - uh i‖ ^ 2 ≤ K * (𝒯 i).meshSize ^ 2 := by
    refine hfalk.trans ?_
    calc _ ≤ ((Mν + g * Mσ) * ((𝒯 i).meshSize ^ 2 * Real.sqrt S)
          + ‖frictionResidualData U₂ f‖ * (c₀' * (𝒯 i).meshSize ^ 2 * Su))
          + 1 ^ 2 / (2 * 1) * (C * (c₁ * (𝒯 i).meshSize * Su)) ^ 2 :=
          add_le_add hR (mul_le_mul_of_nonneg_left hsq (by norm_num))
      _ = K * (𝒯 i).meshSize ^ 2 := by rw [hK]; ring
  have hfin : ‖u - uh i‖ ^ 2 ≤ 2 * K * (𝒯 i).meshSize ^ 2 := by linarith
  calc ‖u - uh i‖ = Real.sqrt (‖u - uh i‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (2 * K * (𝒯 i).meshSize ^ 2) := Real.sqrt_le_sqrt hfin
    _ = Real.sqrt (2 * K) * (𝒯 i).meshSize := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hh0]

end Example1144

end AtkinsonHan.Chapter11
