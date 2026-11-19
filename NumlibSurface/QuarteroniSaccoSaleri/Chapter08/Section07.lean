/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Approximation.BSpline
import Numlib.Approximation.Bezier
import Numlib.Approximation.Spline
import NumlibSurface.QuarteroniSaccoSaleri.Chapter08.Section06

/-!
# Quarteroni, Sacco and Saleri, Section 8.7: Splines in parametric form

This module formalizes Section 8.7 of [quarteroni2000numerical]. A sequence of points
$P_0, \ldots, P_n$ of the plane is interpolated by a parametric cubic spline
$S_3(t) = (s_{3,x}(t), s_{3,y}(t))$, whose coordinates are cubic splines in a parameter $t$. With
the cumulative-length parametrization $t_i = \sum_{k \le i} l_k$, where $l_k$ is the length of the
segment $P_{k-1} P_k$, the spline is geometrically invariant: it commutes with the isometries of the
plane (a result that the book quotes from Späth). Section 8.7.1 states the Bernstein polynomials
$b_{n,k}(t) = \binom{n}{k} t^k (1 - t)^{n-k}$ with their recursion and basis property, the Bézier
curve $B_n(P_0, \ldots, P_n; t) = \sum_k P_k b_{n,k}(t)$ of (8.58), the construction of de
Casteljau, the reversal property, and two properties of parametric B-spline curves: a control point
acts locally, and the curve lies in the convex hull of the control polygon.

The proofs specialize the backbone modules `Numlib.Approximation.Spline` (the interpolatory cubic
spline `Spline.cubicInterpVec` of vector-valued data and its affine equivariance
`Spline.cubicInterpVec_affine`), `Numlib.Approximation.Bezier` (the Bézier curve `Bezier.curve`, the
construction `Bezier.casteljau` and the lemmas on Bernstein polynomials) and
`Numlib.Approximation.BSpline` (the parametric B-spline `BSpline.curve`).

## Main definitions

* Section 8.7, `QuarteroniSaccoSaleri.Chapter08.parametricCubicSpline`: the parametric cubic spline
  $S_3(t) = (s_{3,x}(t), s_{3,y}(t))$ of the points $P_0, \ldots, P_n$.
* Section 8.7, `QuarteroniSaccoSaleri.Chapter08.cumulativeLength`: the cumulative-length
  parametrization $t_i = \sum_{k=1}^i l_k$.
* (8.58), `QuarteroniSaccoSaleri.Chapter08.equation_8_58`: the Bézier curve
  $B_n(P_0, \ldots, P_n; t)$.
* Section 8.7.1, `QuarteroniSaccoSaleri.Chapter08.parametricBSpline`: the parametric B-spline curve
  $t \mapsto \sum_i B_{i,k+1}(t) P_i$.

## Main results

* Section 8.7, `QuarteroniSaccoSaleri.Chapter08.parametricCubicSpline_apply_node`: $S_3(t_i) = P_i$.
* Section 8.7, `QuarteroniSaccoSaleri.Chapter08.isPartition_cumulativeLength`: the cumulative
  lengths of distinct consecutive points form a partition of $[0, t_n]$.
* Section 8.7, `QuarteroniSaccoSaleri.Chapter08.cumulativeLengthSpline_invariant`: the
  cumulative-length spline commutes with the isometries of the plane.
* Section 8.7.1, `QuarteroniSaccoSaleri.Chapter08.bernsteinRecursion_zero` and
  `QuarteroniSaccoSaleri.Chapter08.bernsteinRecursion`: the recursion of the Bernstein polynomials.
* Section 8.7.1, `QuarteroniSaccoSaleri.Chapter08.bernstein_mem_polyLE` and
  `QuarteroniSaccoSaleri.Chapter08.bernsteinBasis`: the Bernstein polynomials
  $b_{n,0}, \ldots, b_{n,n}$ form a basis of $\mathbb{P}_n$.
* (8.58), `QuarteroniSaccoSaleri.Chapter08.equation_8_58_mem_convexHull`: the Bézier curve lies in
  the convex hull of its control points.
* Section 8.7.1, `QuarteroniSaccoSaleri.Chapter08.deCasteljau` and
  `QuarteroniSaccoSaleri.Chapter08.deCasteljau_succ`: the construction of de Casteljau computes the
  Bézier curve.
* Section 8.7.1, `QuarteroniSaccoSaleri.Chapter08.bezier_reverse` and
  `QuarteroniSaccoSaleri.Chapter08.bezier_reverse_image`: the reversed polygon gives the same curve
  with the opposite orientation.
* Section 8.7.1, `QuarteroniSaccoSaleri.Chapter08.bezier_endpoints`: $B_n(P; 0) = P_0$ and
  $B_n(P; 1) = P_n$.
* Section 8.7.1, property 1, `QuarteroniSaccoSaleri.Chapter08.parametricBSpline_local`: a change of
  one control point changes the B-spline curve only on the support of its B-spline.
* Section 8.7.1, property 2, `QuarteroniSaccoSaleri.Chapter08.parametricBSpline_mem_convexHull`: the
  B-spline curve lies in the convex hull of the control polygon.

## Conventions

* Points of the plane are elements of `EuclideanSpace ℝ (Fin 2)`, so the length of a segment is the
  Euclidean distance `dist`. The parameter partition is $0 = t_0 < t_1 < \cdots < t_n = T$, that is,
  `IsIntervalPartition 0 T n t`.
* Bézier and B-spline curves take control points in an arbitrary real vector space $E$. The plane of
  the book is the case $E$ = `EuclideanSpace ℝ (Fin 2)`.
* The Bernstein polynomial $b_{n,k}$ is `bernsteinPolynomial ℝ n k`, and $\mathbb{P}_n$ on $[0, 1]$
  is `polyLE (Icc 0 1) n`.
* The book's B-spline $B_{i,k+1}$, of degree $k$, is `BSpline.bspline x k i`.

## Deviations from the source

* **Specialization.** Parametric interpolation uses natural cubic splines in each coordinate. See
  `QuarteroniSaccoSaleri.Chapter08.parametricCubicSpline`,
  `QuarteroniSaccoSaleri.Chapter08.parametricCubicSpline_apply`,
  `QuarteroniSaccoSaleri.Chapter08.parametricCubicSpline_apply_node`.
* **Reading.** Strict cumulative parameter partitions require distinct neighbors, and the natural
  spline is equivariant under affine isometries. See
  `QuarteroniSaccoSaleri.Chapter08.isPartition_cumulativeLength`,
  `QuarteroniSaccoSaleri.Chapter08.cumulativeLength_comp`,
  `QuarteroniSaccoSaleri.Chapter08.cumulativeLengthSpline_invariant`.
* **Representation.** Bernstein formulas are polynomial identities, with the basis stated on the
  unit interval. See `QuarteroniSaccoSaleri.Chapter08.bernsteinPolynomial_eval`,
  `QuarteroniSaccoSaleri.Chapter08.bernsteinRecursion_zero`,
  `QuarteroniSaccoSaleri.Chapter08.bernsteinRecursion`,
  `QuarteroniSaccoSaleri.Chapter08.bernstein_mem_polyLE`,
  `QuarteroniSaccoSaleri.Chapter08.bernsteinBasis`.
* **Generalization.** Bézier formulas and the de Casteljau recursion generalize from planar points
  to a real vector space. See `QuarteroniSaccoSaleri.Chapter08.equation_8_58`,
  `QuarteroniSaccoSaleri.Chapter08.equation_8_58_apply`,
  `QuarteroniSaccoSaleri.Chapter08.equation_8_58_mem_convexHull`,
  `QuarteroniSaccoSaleri.Chapter08.deCasteljau_step`, `QuarteroniSaccoSaleri.Chapter08.deCasteljau`,
  `QuarteroniSaccoSaleri.Chapter08.deCasteljau_succ`,
  `QuarteroniSaccoSaleri.Chapter08.bezier_reverse`,
  `QuarteroniSaccoSaleri.Chapter08.bezier_reverse_image`,
  `QuarteroniSaccoSaleri.Chapter08.bezier_endpoints`.
* **Reading.** B-spline locality uses half-open support, and the convex-hull claim is restricted to
  the partition-of-unity interval. See `QuarteroniSaccoSaleri.Chapter08.parametricBSpline`,
  `QuarteroniSaccoSaleri.Chapter08.parametricBSpline_apply`,
  `QuarteroniSaccoSaleri.Chapter08.parametricBSpline_local`,
  `QuarteroniSaccoSaleri.Chapter08.parametricBSpline_mem_convexHull`.
* **The parametric cubic spline** (reading). The source does not fix the end conditions of the
  coordinate splines. The natural end conditions (8.45) are used. See
  `QuarteroniSaccoSaleri.Chapter08.parametricCubicSpline`.

## Not formalized

* **Programs 68–70**, which are code.
* **The comparison in property 2 of Section 8.7.1**, that the parametric B-spline "better
  approximates the control polygon than the corresponding Bézier curve does", which is not a
  mathematical statement.
-/

open Polynomial Set

namespace QuarteroniSaccoSaleri.Chapter08

/-! ### Parametric cubic splines and the cumulative-length parametrization -/

/-- **Section 8.7** of [quarteroni2000numerical], the parametric cubic spline. Let
$P_i = (x_i, y_i)$, $i = 0, \ldots, n$, be points of the plane, and let $t_0, \ldots, t_n$ be
parameter values. The **parametric cubic spline** of the points is
$$S_3(t) = (s_{3,x}(t), s_{3,y}(t)),$$
where $s_{3,x}$ and $s_{3,y}$ are the natural cubic splines that interpolate the data
$\{t_i, x_i\}$ and $\{t_i, y_i\}$.

**Reading.** The source does not fix the end conditions of $s_{3,x}$ and $s_{3,y}$. The natural
end conditions (8.45) are used.

The spline is the vector-valued natural spline `Spline.cubicInterpVec n t P 0 0 0 0`. Its
coordinates are the natural splines of the coordinates, by
`QuarteroniSaccoSaleri.Chapter08.parametricCubicSpline_apply`.

**Reading.** The source defines parametric splines of general degree with no fixed closure. The
declarations choose cubic natural splines in the two coordinates and prove the interpolation
conditions on a partition.
-/
noncomputable def parametricCubicSpline (t : ℕ → ℝ) (n : ℕ) (P : ℕ → EuclideanSpace ℝ (Fin 2)) :
    ℝ → EuclideanSpace ℝ (Fin 2) :=
  Spline.cubicInterpVec n t P 0 0 0 0

/-- **Section 8.7** of [quarteroni2000numerical], the coordinates. Let $P_0, \ldots, P_n$ be points
of the plane and $t_0, \ldots, t_n$ parameter values. For every $\tau \in \mathbb{R}$ and
$j \in \{0, 1\}$, the coordinate $j$ of $S_3(\tau)$ is $s_{3,j}(\tau)$, where $s_{3,j}$ is the
natural cubic spline `Spline.naturalInterp` that interpolates the data $\{t_i, (P_i)_j\}$.

**Reading.** The source defines parametric splines of general degree with no fixed closure. The
declarations choose cubic natural splines in the two coordinates and prove the interpolation
conditions on a partition.
-/
theorem parametricCubicSpline_apply (t : ℕ → ℝ) (n : ℕ) (P : ℕ → EuclideanSpace ℝ (Fin 2))
    (τ : ℝ) (j : Fin 2) :
    parametricCubicSpline t n P τ j = Spline.naturalInterp n t (fun i => P i j) τ := by
  have := Spline.cubicInterpVec_affine n t P 0 0 0 0 (EuclideanSpace.projₗ j) 0 τ
  simp only [add_zero, map_zero, EuclideanSpace.projₗ, PiLp.projₗ_apply] at this
  rw [parametricCubicSpline, Spline.naturalInterp, ← Spline.cubicInterpVec_real, ← this]

/-- **Section 8.7** of [quarteroni2000numerical], interpolation. Let
$0 = t_0 < t_1 < \cdots < t_n = T$ with $n \ge 1$, and let $P_0, \ldots, P_n$ be points of the
plane. Then $S_3(t_i) = P_i$ for $i = 0, \ldots, n$.

**Reading.** The source defines parametric splines of general degree with no fixed closure. The
declarations choose cubic natural splines in the two coordinates and prove the interpolation
conditions on a partition.
-/
theorem parametricCubicSpline_apply_node {T : ℝ} {t : ℕ → ℝ} {n : ℕ}
    (ht : IsIntervalPartition 0 T n t) (hn : 1 ≤ n) (P : ℕ → EuclideanSpace ℝ (Fin 2)) {i : ℕ}
    (hi : i ≤ n) :
    parametricCubicSpline t n P (t i) = P i := by
  ext j
  rw [parametricCubicSpline_apply, Spline.naturalInterp, Spline.cubicInterp_apply_node ht hn hi]

/-- **Section 8.7** of [quarteroni2000numerical], the cumulative-length parametrization. Let
$P_0, P_1, \ldots$ be points of the plane, and let $l_i = |P_{i-1} P_i|$ be the length of the
segment from $P_{i-1}$ to $P_i$. The **cumulative-length parametrization** is $t_0 = 0$ and
$$t_i = \sum_{k=1}^i l_k, \qquad i \ge 1,$$
"the cumulative length of the piecewise line that joins the points from $P_0$ to $P_i$". -/
noncomputable def cumulativeLength (P : ℕ → EuclideanSpace ℝ (Fin 2)) (i : ℕ) : ℝ :=
  ∑ k ∈ Finset.range i, dist (P k) (P (k + 1))

/-- **Section 8.7** of [quarteroni2000numerical], the cumulative-length parametrization. For all
points $P_0, P_1, \ldots$ of the plane, $t_0 = 0$. -/
@[simp]
theorem cumulativeLength_zero (P : ℕ → EuclideanSpace ℝ (Fin 2)) : cumulativeLength P 0 = 0 := by
  simp [cumulativeLength]

/-- **Section 8.7** of [quarteroni2000numerical], the cumulative-length parametrization. For all
points $P_i = (x_i, y_i)$ of the plane and every $i$,
$$t_{i+1} = t_i + \sqrt{(x_{i+1} - x_i)^2 + (y_{i+1} - y_i)^2},$$
the length of the segment $P_i P_{i+1}$ added to $t_i$. -/
theorem cumulativeLength_succ (P : ℕ → EuclideanSpace ℝ (Fin 2)) (i : ℕ) :
    cumulativeLength P (i + 1)
      = cumulativeLength P i + √((P (i + 1) 0 - P i 0) ^ 2 + (P (i + 1) 1 - P i 1) ^ 2) := by
  rw [cumulativeLength, Finset.sum_range_succ, dist_comm, EuclideanSpace.dist_eq, Fin.sum_univ_two,
    Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]
  rfl

/-- **Section 8.7** of [quarteroni2000numerical], the cumulative lengths form a partition. Let
$P_0, \ldots, P_n$ be points of the plane with $P_k \neq P_{k+1}$ for $k < n$. Then
$0 = t_0 < t_1 < \cdots < t_n = T$ with $T = t_n$.

Every $l_i$ is positive because consecutive points are distinct.

**Reading.** Partition strictness assumes consecutive points differ. Geometric invariance is stated
as equivariance for affine Euclidean isometries, with preservation of cumulative parameters.
-/
theorem isPartition_cumulativeLength {n : ℕ} {P : ℕ → EuclideanSpace ℝ (Fin 2)}
    (hP : ∀ k < n, P k ≠ P (k + 1)) :
    IsIntervalPartition 0 (cumulativeLength P n) n (cumulativeLength P) where
  step k hk := by
    rw [cumulativeLength, cumulativeLength, Finset.sum_range_succ]
    exact lt_add_of_pos_right _ (dist_pos.mpr (hP k hk))
  first := cumulativeLength_zero P
  last := rfl

/-- **Section 8.7** of [quarteroni2000numerical], invariance of the cumulative lengths. Let $Q$ be
an isometry of the plane, an affine isometric equivalence of `EuclideanSpace ℝ (Fin 2)`, and let
$P_0, P_1, \ldots$ be points of the plane. Then the cumulative lengths of the points $Q(P_i)$
are those of the points $P_i$.

**Reading.** Partition strictness assumes consecutive points differ. Geometric invariance is stated
as equivariance for affine Euclidean isometries, with preservation of cumulative parameters.
-/
theorem cumulativeLength_comp (Q : EuclideanSpace ℝ (Fin 2) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin 2))
    (P : ℕ → EuclideanSpace ℝ (Fin 2)) : cumulativeLength (Q ∘ P) = cumulativeLength P := by
  funext i
  simp only [cumulativeLength, Function.comp_apply, AffineIsometryEquiv.dist_map]

/-- **Section 8.7** of [quarteroni2000numerical], geometric invariance of the cumulative-length
spline (quoted by the book from Späth). Let $Q$ be an isometry of the plane and let
$P_0, \ldots, P_n$ be points of the plane. Let $S_3$ be the parametric cubic spline of the
points $P_i$ with the cumulative-length parameters of the $P_i$, and let $S_3^Q$ be the
parametric cubic spline of the points $Q(P_i)$ with the cumulative-length parameters of the
$Q(P_i)$. Then $S_3^Q(t) = Q(S_3(t))$ for every $t \in \mathbb{R}$.

The cumulative lengths do not change (`QuarteroniSaccoSaleri.Chapter08.cumulativeLength_comp`),
and the natural cubic spline commutes with affine maps of the data
(`Spline.cubicInterpVec_affine`, with $Q(P) = Q_{\mathrm{lin}}(P) + Q(0)$).

**Reading.** Partition strictness assumes consecutive points differ. Geometric invariance is stated
as equivariance for affine Euclidean isometries, with preservation of cumulative parameters.
-/
theorem cumulativeLengthSpline_invariant
    (Q : EuclideanSpace ℝ (Fin 2) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin 2)) (n : ℕ)
    (P : ℕ → EuclideanSpace ℝ (Fin 2)) :
    parametricCubicSpline (cumulativeLength (Q ∘ P)) n (Q ∘ P)
      = Q ∘ parametricCubicSpline (cumulativeLength P) n P := by
  have hQ : ∀ v, Q v = Q.linearIsometryEquiv v + Q 0 := fun v => by
    simpa [vadd_eq_add] using Q.map_vadd 0 v
  funext τ
  rw [cumulativeLength_comp, Function.comp_apply, parametricCubicSpline, parametricCubicSpline]
  have := Spline.cubicInterpVec_affine n (cumulativeLength P) P 0 0 0 0
    (Q.linearIsometryEquiv.toLinearEquiv : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2))
    (Q 0) τ
  simp only [map_zero, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv] at this
  rw [hQ (Spline.cubicInterpVec n (cumulativeLength P) P 0 0 0 0 τ), ← this]
  congr 1
  funext i
  rw [Function.comp_apply, hQ (P i)]

/-! ### Section 8.7.1: Bernstein polynomials and Bézier curves -/

/-- **Section 8.7.1** of [quarteroni2000numerical], the Bernstein polynomials. For
$n, k \in \mathbb{N}$ and $t \in \mathbb{R}$, the Bernstein polynomial $b_{n,k}$ over $[0, 1]$
satisfies
$$b_{n,k}(t) = \binom{n}{k} t^k (1 - t)^{n-k}.$$

The polynomial is `bernsteinPolynomial ℝ n k`. For $k > n$ the binomial coefficient is $0$.

**Reading.** The identities are for real polynomials on all real arguments, with coefficients
defined for all natural indices. The basis theorem restricts the polynomials to the unit interval
and uses precisely the degree-bounded indices.
-/
theorem bernsteinPolynomial_eval (n k : ℕ) (t : ℝ) :
    (bernsteinPolynomial ℝ n k).eval t = n.choose k * t ^ k * (1 - t) ^ (n - k) := by
  simp [bernsteinPolynomial]

/-- **Section 8.7.1** of [quarteroni2000numerical], the Bernstein recursion, first line. For
$n \in \mathbb{N}$ and $t \in \mathbb{R}$, $b_{n,0}(t) = (1 - t)^n$.

**Reading.** The identities are for real polynomials on all real arguments, with coefficients
defined for all natural indices. The basis theorem restricts the polynomials to the unit interval
and uses precisely the degree-bounded indices.
-/
theorem bernsteinRecursion_zero (n : ℕ) (t : ℝ) :
    (bernsteinPolynomial ℝ n 0).eval t = (1 - t) ^ n := by
  simp [bernsteinPolynomial]

/-- **Section 8.7.1** of [quarteroni2000numerical], the Bernstein recursion, second line. For all
$n, k \in \mathbb{N}$ and $t \in \mathbb{R}$,
$$b_{n+1,k+1}(t) = (1 - t) \, b_{n,k+1}(t) + t \, b_{n,k}(t).$$

The book writes the recursion $b_{n,k}(t) = (1 - t) b_{n-1,k}(t) + t b_{n-1,k-1}(t)$ for
$k = 1, \ldots, n$; it is stated here for $n + 1$ and $k + 1$, and for every $k$, since both
sides vanish when $k > n$. The proof is `bernsteinPolynomial.succ_succ`.

**Reading.** The identities are for real polynomials on all real arguments, with coefficients
defined for all natural indices. The basis theorem restricts the polynomials to the unit interval
and uses precisely the degree-bounded indices.
-/
theorem bernsteinRecursion (n k : ℕ) (t : ℝ) :
    (bernsteinPolynomial ℝ (n + 1) (k + 1)).eval t
      = (1 - t) * (bernsteinPolynomial ℝ n (k + 1)).eval t
        + t * (bernsteinPolynomial ℝ n k).eval t := by
  rw [bernsteinPolynomial.succ_succ]
  simp

/-- **Section 8.7.1** of [quarteroni2000numerical], the degree. For all $n, k \in \mathbb{N}$, the
Bernstein polynomial $b_{n,k}$, as a function on $[0, 1]$, lies in $\mathbb{P}_n$: "it is easily
seen that $b_{n,k} \in \mathbb{P}_n$ for $k = 0, \ldots, n$".

The proof is `bernsteinPolynomial.degree_le`.

**Reading.** The identities are for real polynomials on all real arguments, with coefficients
defined for all natural indices. The basis theorem restricts the polynomials to the unit interval
and uses precisely the degree-bounded indices.
-/
theorem bernstein_mem_polyLE (n k : ℕ) :
    (bernsteinPolynomial ℝ n k).toContinuousMapOn (Icc 0 1) ∈ polyLE (Icc (0 : ℝ) 1) n :=
  mem_polyLE_iff.mpr ⟨bernsteinPolynomial ℝ n k, bernsteinPolynomial.degree_le ℝ n k, fun _ => rfl⟩

/-- **Section 8.7.1** of [quarteroni2000numerical], the Bernstein basis. For $n \in \mathbb{N}$, the
functions $b_{n,0}, \ldots, b_{n,n}$ on $[0, 1]$ form a basis of the space $\mathbb{P}_n$ of
polynomials of degree at most $n$ on $[0, 1]$: "$\{b_{n,k}, k = 0, \ldots, n\}$ provides a basis
for $\mathbb{P}_n$".

The proof is `bernsteinPolynomial.exists_basis_polyLE`.

**Reading.** The identities are for real polynomials on all real arguments, with coefficients
defined for all natural indices. The basis theorem restricts the polynomials to the unit interval
and uses precisely the degree-bounded indices.
-/
theorem bernsteinBasis (n : ℕ) :
    ∃ B : Module.Basis (Fin (n + 1)) ℝ (polyLE (Icc (0 : ℝ) 1) n),
      ∀ (k : Fin (n + 1)) (t : Icc (0 : ℝ) 1),
        (B k : C(Icc (0 : ℝ) 1, ℝ)) t = (bernsteinPolynomial ℝ n k).eval (t : ℝ) :=
  bernsteinPolynomial.exists_basis_polyLE (Icc_infinite (by norm_num)) n

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}

/-- **Equation (8.58)** of [quarteroni2000numerical], the Bézier curve. Let $E$ be a real vector
space and let $P_0, P_1, \ldots, P_n \in E$ be $n + 1$ ordered points, the vertices of the
characteristic (or Bézier) polygon. The **Bézier curve** of the points is
$$B_n(P_0, P_1, \ldots, P_n; t) = \sum_{k=0}^n P_k b_{n,k}(t), \qquad 0 \le t \le 1.$$

The curve is `Bezier.curve P t`. It is defined for every $t \in \mathbb{R}$.

**Generalization.** The formulas and recursion use an arbitrary real vector space and all real
parameters. The convex-hull and orientation-independent image results restrict the parameter to the
unit interval.
-/
noncomputable def equation_8_58 (P : Fin (n + 1) → E) (t : ℝ) : E :=
  Bezier.curve P t

/-- **Equation (8.58)** of [quarteroni2000numerical], unfolded. For points $P_0, \ldots, P_n$ of a
real vector space and $t \in \mathbb{R}$, $B_n(P_0, \ldots, P_n; t) = \sum_{k=0}^n b_{n,k}(t)
P_k$.

**Generalization.** The formulas and recursion use an arbitrary real vector space and all real
parameters. The convex-hull and orientation-independent image results restrict the parameter to the
unit interval.
-/
theorem equation_8_58_apply (P : Fin (n + 1) → E) (t : ℝ) :
    equation_8_58 P t = ∑ k : Fin (n + 1), (bernsteinPolynomial ℝ n k).eval t • P k :=
  rfl

/-- **Equation (8.58)** of [quarteroni2000numerical], the convex hull. Let $P_0, \ldots, P_n$ be
points of a real vector space and $t \in [0, 1]$. Then $B_n(P_0, \ldots, P_n; t)$ lies in the
convex hull of $P_0, \ldots, P_n$.

The weights $b_{n,k}(t)$ are nonnegative and sum to $1$. The proof is
`Bezier.curve_mem_convexHull`.

**Generalization.** The formulas and recursion use an arbitrary real vector space and all real
parameters. The convex-hull and orientation-independent image results restrict the parameter to the
unit interval.
-/
theorem equation_8_58_mem_convexHull (P : Fin (n + 1) → E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    equation_8_58 P t ∈ convexHull ℝ (range P) :=
  Bezier.curve_mem_convexHull P ht

/-- **Section 8.7.1** of [quarteroni2000numerical], one step of the construction of de Casteljau.
Let $P_0, \ldots, P_{n+1}$ be points of a real vector space and $t \in \mathbb{R}$. One step of
the construction gives the new vertices
$$P_{i,1}(t) = (1 - t) P_i + t P_{i+1}, \qquad i = 0, \ldots, n,$$
of a polygon with one vertex less.

The step is `Bezier.casteljauStep`.

**Generalization.** The formulas and recursion use an arbitrary real vector space and all real
parameters. The convex-hull and orientation-independent image results restrict the parameter to the
unit interval.
-/
theorem deCasteljau_step (t : ℝ) (P : Fin (n + 2) → E) (i : Fin (n + 1)) :
    Bezier.casteljauStep t P i = (1 - t) • P i.castSucc + t • P i.succ :=
  rfl

/-- **Section 8.7.1** of [quarteroni2000numerical], the construction of de Casteljau. Let
$P_0, \ldots, P_n$ be points of a real vector space and $t \in \mathbb{R}$. Repeat the step
until the polygon has a single vertex $P_{0,n}(t)$. Then
$$P_{0,n}(t) = B_n(P_0, \ldots, P_n; t).$$

The construction is `Bezier.casteljau`, and the proof is `Bezier.casteljau_eq_curve`.

**Generalization.** The formulas and recursion use an arbitrary real vector space and all real
parameters. The convex-hull and orientation-independent image results restrict the parameter to the
unit interval.
-/
theorem deCasteljau (t : ℝ) (P : Fin (n + 1) → E) : Bezier.casteljau t P = equation_8_58 P t :=
  Bezier.casteljau_eq_curve P t

/-- **Section 8.7.1** of [quarteroni2000numerical], the last step of the construction of de
Casteljau. Let $P_0, \ldots, P_{n+1}$ be points of a real vector space and $t \in \mathbb{R}$.
Then
$$B_{n+1}(P_0, \ldots, P_{n+1}; t) = (1 - t) \, B_n(P_0, \ldots, P_n; t) + t \, B_n(P_1, \ldots,
  P_{n+1}; t).$$

The proof is `Bezier.curve_succ`.

**Generalization.** The formulas and recursion use an arbitrary real vector space and all real
parameters. The convex-hull and orientation-independent image results restrict the parameter to the
unit interval.
-/
theorem deCasteljau_succ (P : Fin (n + 2) → E) (t : ℝ) :
    equation_8_58 P t = (1 - t) • equation_8_58 (Fin.init P) t + t • equation_8_58 (Fin.tail P) t :=
  Bezier.curve_succ P t

/-- **Section 8.7.1** of [quarteroni2000numerical], reversal. Let $P_0, \ldots, P_n$ be points of a
real vector space and $t \in \mathbb{R}$. Then
$$B_n(P_n, P_{n-1}, \ldots, P_0; t) = B_n(P_0, P_1, \ldots, P_n; 1 - t).$$

The book says that the two curves coincide "apart from the orientation". The proof is
`Bezier.curve_rev`.

**Generalization.** The formulas and recursion use an arbitrary real vector space and all real
parameters. The convex-hull and orientation-independent image results restrict the parameter to the
unit interval.
-/
theorem bezier_reverse (P : Fin (n + 1) → E) (t : ℝ) :
    equation_8_58 (P ∘ Fin.rev) t = equation_8_58 P (1 - t) :=
  Bezier.curve_rev P t

/-- **Section 8.7.1** of [quarteroni2000numerical], reversal of the traces. Let $P_0, \ldots, P_n$
be points of a real vector space. The Bézier curves of $P_0, \ldots, P_n$ and of
$P_n, \ldots, P_0$ have the same image of $[0, 1]$.

**Generalization.** The formulas and recursion use an arbitrary real vector space and all real
parameters. The convex-hull and orientation-independent image results restrict the parameter to the
unit interval.
-/
theorem bezier_reverse_image (P : Fin (n + 1) → E) :
    equation_8_58 (P ∘ Fin.rev) '' Icc (0 : ℝ) 1 = equation_8_58 P '' Icc (0 : ℝ) 1 := by
  ext p
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, (bezier_reverse P t).symm⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    rw [bezier_reverse, sub_sub_cancel]

/-- **Section 8.7.1** of [quarteroni2000numerical], the endpoints. Let $P_0, \ldots, P_n$ be points
of a real vector space. Then $B_n(P_0, \ldots, P_n; 0) = P_0$ and
$B_n(P_0, \ldots, P_n; 1) = P_n$.

The proof is `Bezier.curve_zero` and `Bezier.curve_one`.

**Generalization.** The formulas and recursion use an arbitrary real vector space and all real
parameters. The convex-hull and orientation-independent image results restrict the parameter to the
unit interval.
-/
theorem bezier_endpoints (P : Fin (n + 1) → E) :
    equation_8_58 P 0 = P 0 ∧ equation_8_58 P 1 = P (Fin.last n) :=
  ⟨Bezier.curve_zero P, Bezier.curve_one P⟩

/-! ### Parametric B-splines -/

/-- **Section 8.7.1** of [quarteroni2000numerical], the parametric B-spline. Let $E$ be a real
vector space, let $x_0, x_1, \ldots$ be knots, let $k, N \in \mathbb{N}$, and let
$P_0, \ldots, P_{N-1} \in E$ be control points. The **parametric B-spline** is the curve
$$t \mapsto \sum_{i=0}^{N-1} B_{i,k+1}(t) P_i.$$

The book uses the B-splines on a nondecreasing knot sequence "in (8.58) instead of the Bernstein
polynomials". The curve is `BSpline.curve x k P N t`.

**Reading.** Changing a control point preserves the curve outside its half-open support. The
convex-hull assertion is made on the half-open interval where the selected basis functions form a
partition of unity. The formulas work in real vector spaces.
-/
noncomputable def parametricBSpline (x : ℕ → ℝ) (k : ℕ) (P : ℕ → E) (N : ℕ) (t : ℝ) : E :=
  BSpline.curve x k P N t

/-- **Section 8.7.1** of [quarteroni2000numerical], the parametric B-spline unfolded. The parametric
B-spline at $t$ is $\sum_{i=0}^{N-1} B_{i,k+1}(t) P_i$.

**Reading.** Changing a control point preserves the curve outside its half-open support. The
convex-hull assertion is made on the half-open interval where the selected basis functions form a
partition of unity. The formulas work in real vector spaces.
-/
theorem parametricBSpline_apply (x : ℕ → ℝ) (k : ℕ) (P : ℕ → E) (N : ℕ) (t : ℝ) :
    parametricBSpline x k P N t = ∑ i ∈ Finset.range N, BSpline.bspline x k i t • P i :=
  rfl

/-- **Section 8.7.1** of [quarteroni2000numerical], property 1 of parametric B-splines. Let
$x_0 \le x_1 \le \cdots$ be nondecreasing knots, let $P_0, P_1, \ldots \in E$, and let
$Q \in E$. If $P_j$ is replaced by $Q$, the parametric B-spline does not change at the
parameters $t \notin [x_j, x_{j+k+1})$, the support of $B_{j,k+1}$.

The book says that "perturbing a single vertex of the characteristic polygon yields a local
perturbation of the curve only around the vertex itself". The proof is
`BSpline.curve_update_eq_of_notMem`.

**Reading.** Changing a control point preserves the curve outside its half-open support. The
convex-hull assertion is made on the half-open interval where the selected basis functions form a
partition of unity. The formulas work in real vector spaces.
-/
theorem parametricBSpline_local {x : ℕ → ℝ} (hx : Monotone x) (k : ℕ) (P : ℕ → E) (j : ℕ) (Q : E)
    (N : ℕ) {t : ℝ} (ht : t ∉ Ico (x j) (x (j + k + 1))) :
    parametricBSpline x k (Function.update P j Q) N t = parametricBSpline x k P N t :=
  BSpline.curve_update_eq_of_notMem hx P j Q ht

/-- **Section 8.7.1** of [quarteroni2000numerical], property 2 of parametric B-splines. Let
$x_0 \le x_1 \le \cdots$ be nondecreasing knots, let $N \ge 1$, and let
$P_0, P_1, \ldots \in E$. Then for every $t \in [x_k, x_N)$, the parametric B-spline with
control points $P_0, \ldots, P_{N-1}$ at $t$ lies in the convex hull of $P_0, \ldots, P_{N-1}$.

The book says that the curve "is always contained within the convex hull of the polygon". On the
parameter range $[x_k, x_N)$ the coefficients $B_{i,k+1}(t)$ are nonnegative and sum to $1$. The
first half of the book's sentence, that the parametric B-spline "better approximates the control
polygon than the corresponding Bézier curve does", is not a mathematical statement and is not
formalized. The proof is `BSpline.curve_mem_convexHull`.

**Reading.** Changing a control point preserves the curve outside its half-open support. The
convex-hull assertion is made on the half-open interval where the selected basis functions form a
partition of unity. The formulas work in real vector spaces.
-/
theorem parametricBSpline_mem_convexHull {x : ℕ → ℝ} (hx : Monotone x) (k : ℕ) (P : ℕ → E) {N : ℕ}
    (hN : 1 ≤ N) {t : ℝ} (ht : t ∈ Ico (x k) (x N)) :
    parametricBSpline x k P N t ∈ convexHull ℝ (P '' Iio N) :=
  BSpline.curve_mem_convexHull hx P hN ht

end QuarteroniSaccoSaleri.Chapter08
