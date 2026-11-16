/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.VecNotation
import Numlib.Analysis.Sobolev.Triangulation
import Numlib.Approximation.NodalInterpolation
import Numlib.FiniteElement.Interpolation

/-!
# Atkinson and Han, Section 10.2: Affine-equivalent finite elements

This module formalizes Section 10.2 of [han2009theoretical] apart from its model boundary value
problem. The section builds the finite element setting on a polygon: triangulations, the local
spaces $\mathbb{P}_k$ on a triangle, barycentric coordinates, and the affine map (10.2.25)
$F_K(\hat x) = T_K \hat x + b_K$ of the reference element $\hat K$ onto an element $K$. Lemma 10.2.2
bounds the matrix norms by $\|T_K\| \le h_K / \hat\rho$ and $\|T_K^{-1}\| \le \hat h / \rho_K$,
where $h_K$ and $\hat h$ are the diameters of $K$ and $\hat K$, and $\rho_K$ and $\hat\rho$ are the
diameters of balls inscribed in them. On the reference triangle with the barycentric coordinates
$\hat\lambda_1, \hat\lambda_2, \hat\lambda_3$, a quadratic function is represented by its values at
the vertices $\hat a_i$ and at the side mid-points $\hat a_{ij}$ (10.2.23): $$\hat v = \sum_{i=1}^3
\hat v(\hat a_i) \, \hat\lambda_i (2 \hat\lambda_i - 1) + \sum_{1 \le i < j \le 3} 4 \hat v(\hat
a_{ij}) \, \hat\lambda_i \hat\lambda_j.$$ Exercises 10.2.1 and 10.2.3 give the same kind of
representation for cubic functions on the principal lattice $\hat N_3$ and for bilinear functions on
the reference square. Proposition 10.2.1 says that $\mathbb{P}_k$ is unisolvent on the principal
lattice $\hat N_k$, and Example 10.2.3 builds the continuous piecewise linear element space on a
triangulation. The results specialize `Numlib.FiniteElement.Interpolation`,
`Numlib.FiniteElement.LagrangeElement`, `Numlib.Approximation.NodalInterpolation` and
`Numlib.Analysis.Sobolev.Triangulation`.

## Main definitions

* Section 10.2, `AtkinsonHan.Chapter10.refBary`: the barycentric coordinates
  $\hat\lambda_1, \hat\lambda_2, \hat\lambda_3$ of the reference triangle.
* Equation (10.2.23), `AtkinsonHan.Chapter10.quadraticNode`: the three vertices and the three side
  mid-points of the reference triangle.
* Equation (10.2.23), `AtkinsonHan.Chapter10.quadraticShape`: the six shape functions
  $\hat\lambda_i (2 \hat\lambda_i - 1)$ and $4 \hat\lambda_i \hat\lambda_j$.
* Exercise 10.2.1, `AtkinsonHan.Chapter10.cubicNode`: the ten points of the principal lattice
  $\hat N_3$.
* Exercise 10.2.1, `AtkinsonHan.Chapter10.cubicShape`: the ten cubic shape functions dual to these
  points.
* Exercise 10.2.3, `AtkinsonHan.Chapter10.bilinearNode`: the four vertices of the reference square
  $[0, 1]^2$.
* Exercise 10.2.3, `AtkinsonHan.Chapter10.bilinearShape`: the four bilinear shape functions
  $(1 - \hat x_1)(1 - \hat x_2)$, $\hat x_1 (1 - \hat x_2)$, $(1 - \hat x_1) \hat x_2$,
  $\hat x_1 \hat x_2$.

## Main results

* Equation (10.2.23), `AtkinsonHan.Chapter10.quadraticShape_isNodalBasis`: the six quadratic shape
  functions are dual to the six nodes.
* Equation (10.2.23), `AtkinsonHan.Chapter10.equation_10_2_23`: the nodal representation of a
  quadratic function on the reference triangle.
* Proposition 10.2.1, `AtkinsonHan.Chapter10.proposition_10_2_1`: for $k \ge 1$, a polynomial in
  $\mathbb{P}_k$ is determined by its values on $\hat N_k$.
* Lemma 10.2.2, `AtkinsonHan.Chapter10.lemma_10_2_2`: $\|T_K\| \le h_K / \hat\rho$ and
  $\|T_K^{-1}\| \le \hat h / \rho_K$.
* Example 10.2.3, `AtkinsonHan.Chapter10.example_10_2_3`: the linear element is conforming, and the
  glued piecewise linear function is continuous on $\bar\Omega$ and lies in $H^1(\Omega)$.
* Exercise 10.2.1, `AtkinsonHan.Chapter10.cubicShape_isNodalBasis`: the ten cubic shape functions
  are dual to the ten nodes.
* Exercise 10.2.1, `AtkinsonHan.Chapter10.exercise_10_2_1`: the nodal representation of a cubic
  function on $\hat N_3$.
* Exercise 10.2.3, `AtkinsonHan.Chapter10.bilinearShape_isNodalBasis`: the four bilinear shape
  functions are dual to the four vertices.
* Exercise 10.2.3, `AtkinsonHan.Chapter10.exercise_10_2_3`: the nodal representation of a bilinear
  function on the reference square.

## Implementation notes

* The matrix norm of the source is the spectral norm, the operator norm induced by the Euclidean
  vector norm. So $T_K$ is a continuous linear equivalence of `EuclideanSpace ℝ (Fin d)`, and
  $\|T_K\|$ and $\|T_K^{-1}\|$ are operator norms.
* The proof of Lemma 10.2.2 uses only two facts about the sets: a ball of diameter $\hat\rho$ lies
  in $\hat K$, and $K$ has diameter $h_K$. So the hypothesis is the inclusion
  `Metric.closedBall cref (ρref / 2) ⊆ Kref` of one inscribed ball, and no inradius is defined;
  Mathlib has no inradius. The bound for the largest inscribed ball follows by taking $\hat\rho$ as
  large as the inclusion permits.
* The nodal representations are stated on `ℝ × ℝ`, the $\mathbb{R}^2$ of the source, and not on
  `EuclideanSpace ℝ (Fin 2)`. They are algebraic identities in which no norm, inner product or
  measure appears. The reference triangle has the vertices $(0, 0)$, $(1, 0)$ and $(0, 1)$, so that
  $\hat\lambda_1 = 1 - \hat x_1 - \hat x_2$, $\hat\lambda_2 = \hat x_1$ and
  $\hat\lambda_3 = \hat x_2$. The reference square is $[0, 1]^2$, as in Section 10.3.
* The triangulation axioms (1)–(4) of the source are the backbone structure `Triangulation`.
* The $\mathbb{P}_k$ Lagrange element on the principal lattice is nodal, reproduces $\mathbb{P}_k$,
  and is conforming on every triangulation. This is the remark after Example 10.2.3, and for $k = 2$
  it is Exercise 10.2.4. It is in the backbone as `LagrangeElement.node`, `LagrangeElement.shape`
  and `LagrangeElement.isConformingElement`.
* The $H^1$-conformity of a continuous piecewise $C^1$ function, on which Example 10.2.3 rests, is
  `Triangulation.memSobolev_of_piecewise`.
* Proposition 10.2.1 is proved in the backbone as `LagrangeElement.bijective_latticeEval`, with an
  explicit nodal basis and a count of dimensions. The proof needs neither an induction on $k$ nor
  the divisibility of a polynomial that vanishes on a line by the affine form of that line. Its
  cases $k = 2$ and $k = 3$ are `AtkinsonHan.Chapter10.equation_10_2_23` and
  `AtkinsonHan.Chapter10.exercise_10_2_1`, which are proved independently of it.

## Deviations from the source

* **Equation (10.2.23), Exercises 10.2.1 and 10.2.3** (reading). The source quantifies over the
  functions of the local space that are "determined by" their values at the nodes. The statements
  quantify over the coefficients of a general polynomial of the space. See
  `AtkinsonHan.Chapter10.equation_10_2_23`.

## Not formalized

* **The model Neumann problem (10.2.4)–(10.2.12).** Its boundary term needs the trace on $\Gamma$.
* **Exercise 10.2.5**, the $H(\operatorname{div})$-conformity of a piecewise $H^1$ vector field.
-/

namespace AtkinsonHan.Chapter10

variable {d : ℕ}

/-- **Lemma 10.2.2** of [han2009theoretical]. Let $\hat K, K \subseteq \mathbb{R}^d$ be bounded
sets, and let $F_K(\hat x) = T_K \hat x + b_K$ be an affine map with $T_K$ a linear isomorphism
of $\mathbb{R}^d$ and $F_K(\hat K) = K$ (10.2.25). Let $\hat\rho > 0$ and $\rho_K > 0$, and let
$\hat K$ contain a closed ball of diameter $\hat\rho$ and $K$ a closed ball of diameter
$\rho_K$. Write $h_K = \operatorname{diam} K$ and $\hat h = \operatorname{diam} \hat K$. Then
$$\|T_K\| \le \frac{h_K}{\hat\rho} \qquad \text{and} \qquad \|T_K^{-1}\| \le \frac{\hat
h}{\rho_K}.$$

The norms are the operator norms induced by the Euclidean norm. The two bounds are the same
statement with $\hat K$ and $K$ exchanged; the second applies the first to the inverse map
$y \mapsto T_K^{-1} y - T_K^{-1} b_K$, which carries $K$ onto $\hat K$. Both sets are assumed
bounded, as the closed triangles of the source are: `Metric.diam` of an unbounded set is $0$,
and the bounds would then be false. The proof specializes
`FiniteElement.opNorm_le_diam_div_of_image`. -/
theorem lemma_10_2_2 {Kref K : Set (EuclideanSpace ℝ (Fin d))}
    {T : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d)}
    {b cref c : EuclideanSpace ℝ (Fin d)} {ρref ρK : ℝ} (hρref : 0 < ρref) (hρK : 0 < ρK)
    (hKrefb : Bornology.IsBounded Kref) (hKb : Bornology.IsBounded K)
    (hballref : Metric.closedBall cref (ρref / 2) ⊆ Kref)
    (hballK : Metric.closedBall c (ρK / 2) ⊆ K)
    (hF : (fun x => T x + b) '' Kref = K) :
    ‖(T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))‖ ≤ Metric.diam K / ρref ∧
      ‖(T.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))‖
        ≤ Metric.diam Kref / ρK :=
  FiniteElement.opNorm_le_diam_div_of_image hρref hρK hKrefb hKb hballref hballK hF

/-! ### Nodal representations on the reference element -/

/-- **Section 10.2** of [han2009theoretical], the barycentric coordinates of the reference triangle
with the vertices $\hat a_1 = (0, 0)$, $\hat a_2 = (1, 0)$ and $\hat a_3 = (0, 1)$:
$$\hat\lambda_1 = 1 - \hat x_1 - \hat x_2, \qquad \hat\lambda_2 = \hat x_1, \qquad
\hat\lambda_3 = \hat x_2.$$

They are affine, they sum to $1$, and $\hat\lambda_i(\hat a_j) = \delta_{ij}$, so they are the
shape functions of the linear element. The indices run from $0$ to $2$.
`AtkinsonHan.Chapter10.example_10_3_2` states the last property for a general simplex, with
`AffineBasis.coord`. -/
noncomputable def refBary : Fin 3 → ℝ × ℝ → ℝ :=
  ![fun p => 1 - p.1 - p.2, fun p => p.1, fun p => p.2]

/-- **Equation (10.2.23)** of [han2009theoretical], the six nodes of the quadratic element: the
three vertices $\hat a_1, \hat a_2, \hat a_3$ of the reference triangle, followed by the three
side mid-points $\hat a_{ij} = (\hat a_i + \hat a_j) / 2$ in the order $\hat a_{12}$,
$\hat a_{13}$, $\hat a_{23}$. -/
noncomputable def quadraticNode : Fin 6 → ℝ × ℝ :=
  ![(0, 0), (1, 0), (0, 1), (1 / 2, 0), (0, 1 / 2), (1 / 2, 1 / 2)]

/-- **Equation (10.2.23)** of [han2009theoretical], the six shape functions of the quadratic
element: $\hat\lambda_i (2 \hat\lambda_i - 1)$ for the vertices $\hat a_i$ and
$4 \hat\lambda_i \hat\lambda_j$ for the side mid-points $\hat a_{ij}$, in the order of
`AtkinsonHan.Chapter10.quadraticNode`. -/
noncomputable def quadraticShape : Fin 6 → ℝ × ℝ → ℝ :=
  ![fun p => refBary 0 p * (2 * refBary 0 p - 1),
    fun p => refBary 1 p * (2 * refBary 1 p - 1),
    fun p => refBary 2 p * (2 * refBary 2 p - 1),
    fun p => 4 * refBary 0 p * refBary 1 p,
    fun p => 4 * refBary 0 p * refBary 2 p,
    fun p => 4 * refBary 1 p * refBary 2 p]

/-- **Equation (10.2.23)** of [han2009theoretical], the two observations from which the source
derives (10.2.23). The function $\hat\lambda_i (2 \hat\lambda_i - 1)$ is $1$ at $\hat a_i$ and
$0$ at the other vertices and at every side mid-point. The function
$4 \hat\lambda_i \hat\lambda_j$ is $1$ at $\hat a_{ij}$ and $0$ at every other node. Together
they say that the six shape functions are dual to the six nodes:
$\hat\phi_i(\hat x_j) = \delta_{ij}$.

The statement is `Approximation.IsNodalBasis`. -/
theorem quadraticShape_isNodalBasis : Approximation.IsNodalBasis quadraticNode quadraticShape where
  eval_self i := by
    fin_cases i <;> simp [quadraticNode, quadraticShape, refBary] <;> norm_num
  eval_of_ne i j hij := by
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | (simp [quadraticNode, quadraticShape, refBary] <;> norm_num)

/-- **Equation (10.2.23)** of [han2009theoretical], the nodal representation of a quadratic function
on the reference triangle. For every quadratic function $\hat v(\hat x) = c_0 + c_1 \hat x_1 +
c_2 \hat x_2 + c_3 \hat x_1^2 + c_4 \hat x_1 \hat x_2 + c_5 \hat x_2^2$, $$\hat v = \sum_{i=1}^3
\hat v(\hat a_i) \, \hat\lambda_i (2 \hat\lambda_i - 1) + \sum_{1 \le i < j \le 3} 4 \hat v(\hat
a_{ij}) \, \hat\lambda_i \hat\lambda_j.$$

**Reading.** The source states (10.2.23) for $\hat v$ in the space $\hat X_2$ of the functions
in $\mathbb{P}_2(\hat K)$ that are "determined by" their values at the six nodes. Since
$\mathbb{P}_2(\hat K)$ is the set of the functions above, the statement is an identity in the
six free coefficients. In this form it does not depend on Proposition 10.2.1: the representation
is proved directly, and the unisolvence on the space follows from it.

The right-hand side is `Approximation.nodalInterp` with the nodes
`AtkinsonHan.Chapter10.quadraticNode` and the shape functions
`AtkinsonHan.Chapter10.quadraticShape`. This is the case $k = 2$ of Proposition 10.2.1. -/
theorem equation_10_2_23 (c₀ c₁ c₂ c₃ c₄ c₅ : ℝ) :
    Approximation.nodalInterp quadraticNode quadraticShape
        (fun p : ℝ × ℝ => c₀ + c₁ * p.1 + c₂ * p.2 + c₃ * p.1 ^ 2 + c₄ * p.1 * p.2 + c₅ * p.2 ^ 2)
      = fun p : ℝ × ℝ =>
        c₀ + c₁ * p.1 + c₂ * p.2 + c₃ * p.1 ^ 2 + c₄ * p.1 * p.2 + c₅ * p.2 ^ 2 := by
  funext p
  simp [Approximation.nodalInterp_apply, Fin.sum_univ_succ, quadraticNode, quadraticShape, refBary]
  ring

/-- **Exercise 10.2.1** of [han2009theoretical], the ten points of the principal lattice $\hat N_3$
(10.2.24) for $k = 3$. They are the three vertices, the six points that divide the sides into
thirds, and the centroid. The point on a side is the one with the barycentric coordinate $2/3$
at $\hat a_i$ and $1/3$ at $\hat a_j$, for the ordered pairs $(i, j) = (1, 2), (2, 1), (1, 3),
(3, 1), (2, 3), (3, 2)$ in this order. -/
noncomputable def cubicNode : Fin 10 → ℝ × ℝ :=
  ![(0, 0), (1, 0), (0, 1), (1 / 3, 0), (2 / 3, 0), (0, 1 / 3), (0, 2 / 3), (2 / 3, 1 / 3),
    (1 / 3, 2 / 3), (1 / 3, 1 / 3)]

/-- **Exercise 10.2.1** of [han2009theoretical], the ten cubic shape functions dual to
`AtkinsonHan.Chapter10.cubicNode`: $\hat\lambda_i (3 \hat\lambda_i - 1)(3 \hat\lambda_i - 2) /
2$ for the vertices, $9 \hat\lambda_i \hat\lambda_j (3 \hat\lambda_i - 1) / 2$ for the side
points, and $27 \hat\lambda_1 \hat\lambda_2 \hat\lambda_3$ for the centroid. -/
noncomputable def cubicShape : Fin 10 → ℝ × ℝ → ℝ :=
  ![fun p => refBary 0 p * (3 * refBary 0 p - 1) * (3 * refBary 0 p - 2) / 2,
    fun p => refBary 1 p * (3 * refBary 1 p - 1) * (3 * refBary 1 p - 2) / 2,
    fun p => refBary 2 p * (3 * refBary 2 p - 1) * (3 * refBary 2 p - 2) / 2,
    fun p => 9 * refBary 0 p * refBary 1 p * (3 * refBary 0 p - 1) / 2,
    fun p => 9 * refBary 0 p * refBary 1 p * (3 * refBary 1 p - 1) / 2,
    fun p => 9 * refBary 0 p * refBary 2 p * (3 * refBary 0 p - 1) / 2,
    fun p => 9 * refBary 0 p * refBary 2 p * (3 * refBary 2 p - 1) / 2,
    fun p => 9 * refBary 1 p * refBary 2 p * (3 * refBary 1 p - 1) / 2,
    fun p => 9 * refBary 1 p * refBary 2 p * (3 * refBary 2 p - 1) / 2,
    fun p => 27 * refBary 0 p * refBary 1 p * refBary 2 p]

set_option maxHeartbeats 1000000 in
-- the duality is a hundred numeric evaluations, one for each ordered pair of the ten nodes
/-- **Exercise 10.2.1** of [han2009theoretical]. The ten cubic shape functions are dual to the ten
points of $\hat N_3$: $\hat\phi_i(\hat x_j) = \delta_{ij}$. -/
theorem cubicShape_isNodalBasis : Approximation.IsNodalBasis cubicNode cubicShape where
  eval_self i := by
    fin_cases i <;> simp [cubicNode, cubicShape, refBary] <;> norm_num
  eval_of_ne i j hij := by
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | (simp [cubicNode, cubicShape, refBary] <;> norm_num)

set_option maxHeartbeats 1000000 in
-- `ring` on a cubic identity in two variables with ten free coefficients
/-- **Exercise 10.2.1** of [han2009theoretical]. Every cubic function $\hat v$ on the reference
triangle is represented by its values at the ten points $\hat x_i$ of the principal lattice
$\hat N_3$: $$\hat v = \sum_{i=1}^{10} \hat v(\hat x_i) \, \hat\phi_i,$$ with the shape
functions $\hat\phi_i$ of `AtkinsonHan.Chapter10.cubicShape`.

**Reading.** As for (10.2.23), the statement is an identity in the ten coefficients of a general
cubic $\hat v$.

This is (10.2.23) one degree higher, and the case $k = 3$ of Proposition 10.2.1. -/
theorem exercise_10_2_1 (c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ : ℝ) :
    Approximation.nodalInterp cubicNode cubicShape
        (fun p : ℝ × ℝ => c₀ + c₁ * p.1 + c₂ * p.2 + c₃ * p.1 ^ 2 + c₄ * p.1 * p.2 + c₅ * p.2 ^ 2
          + c₆ * p.1 ^ 3 + c₇ * p.1 ^ 2 * p.2 + c₈ * p.1 * p.2 ^ 2 + c₉ * p.2 ^ 3)
      = fun p : ℝ × ℝ => c₀ + c₁ * p.1 + c₂ * p.2 + c₃ * p.1 ^ 2 + c₄ * p.1 * p.2 + c₅ * p.2 ^ 2
          + c₆ * p.1 ^ 3 + c₇ * p.1 ^ 2 * p.2 + c₈ * p.1 * p.2 ^ 2 + c₉ * p.2 ^ 3 := by
  funext p
  simp [Approximation.nodalInterp_apply, Fin.sum_univ_succ, cubicNode, cubicShape, refBary]
  ring

/-- **Exercise 10.2.3** of [han2009theoretical], the four vertices $(0, 0)$, $(1, 0)$, $(0, 1)$ and
$(1, 1)$ of the reference square $[0, 1]^2$. -/
noncomputable def bilinearNode : Fin 4 → ℝ × ℝ := ![(0, 0), (1, 0), (0, 1), (1, 1)]

/-- **Exercise 10.2.3** of [han2009theoretical], the nodal basis of $\mathbb{Q}_{1,1}$ on the
reference square: the four products $(1 - \hat x_1)(1 - \hat x_2)$, $\hat x_1 (1 - \hat x_2)$,
$(1 - \hat x_1) \hat x_2$ and $\hat x_1 \hat x_2$, in the order of
`AtkinsonHan.Chapter10.bilinearNode`. -/
noncomputable def bilinearShape : Fin 4 → ℝ × ℝ → ℝ :=
  ![fun p => (1 - p.1) * (1 - p.2), fun p => p.1 * (1 - p.2), fun p => (1 - p.1) * p.2,
    fun p => p.1 * p.2]

/-- **Exercise 10.2.3** of [han2009theoretical]. The four bilinear shape functions are dual to the
four vertices of the reference square: $\hat\phi_i(\hat a_j) = \delta_{ij}$. -/
theorem bilinearShape_isNodalBasis : Approximation.IsNodalBasis bilinearNode bilinearShape where
  eval_self i := by fin_cases i <;> simp [bilinearNode, bilinearShape]
  eval_of_ne i j hij := by
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | simp [bilinearNode, bilinearShape]

/-- **Exercise 10.2.3** of [han2009theoretical]. The nodes of $\mathbb{Q}_{1,1}(\hat K)$ on the
reference square are its four vertices $\hat a_i$, the parameters are the values there, and
every bilinear function $\hat v(\hat x) = a_0 + a_1 \hat x_1 + a_2 \hat x_2 + a_3 \hat x_1 \hat
x_2$ is represented by $$\hat v = \sum_{i=1}^4 \hat v(\hat a_i) \, \hat\phi_i,$$ with the
$\hat\phi_i$ of `AtkinsonHan.Chapter10.bilinearShape`.

**Reading.** As for (10.2.23), the statement is an identity in the four coefficients of a
general bilinear $\hat v$.

This is the analogue of (10.2.23) for quadrilaterals. The source treats it apart from the
triangles because the reference map of a general quadrilateral is bilinear and not affine. -/
theorem exercise_10_2_3 (a₀ a₁ a₂ a₃ : ℝ) :
    Approximation.nodalInterp bilinearNode bilinearShape
        (fun p : ℝ × ℝ => a₀ + a₁ * p.1 + a₂ * p.2 + a₃ * p.1 * p.2)
      = fun p : ℝ × ℝ => a₀ + a₁ * p.1 + a₂ * p.2 + a₃ * p.1 * p.2 := by
  funext p
  simp [Approximation.nodalInterp_apply, Fin.sum_univ_succ, bilinearNode, bilinearShape]
  ring

/-! ### Proposition 10.2.1: unisolvence of $\mathbb{P}_k$ on the principal lattice -/

/-- **Proposition 10.2.1** of [han2009theoretical]. Let $k \ge 1$. A polynomial of total degree at
most $k$ in two variables is determined by its values at the $(k+1)(k+2)/2$ points of the
principal lattice $\hat N_k$: the map $p \mapsto (p(\hat x))_{\hat x \in \hat N_k}$ on
$\mathbb{P}_k$ is bijective.

The map is `LagrangeElement.latticeEval`. The source quotes the proposition without proof. The
backbone theorem `LagrangeElement.bijective_latticeEval` proves it with Silvester's explicit
nodal basis and a count of dimensions. -/
theorem proposition_10_2_1 {k : ℕ} (hk : 0 < k) :
    Function.Bijective (LagrangeElement.latticeEval k) :=
  LagrangeElement.bijective_latticeEval hk

/-!
### Example 10.2.3: the linear element space on a triangulation

The triangulation is the backbone structure `Triangulation Ω`, which has the properties 1–4 of the
source. The local space $X_K = \mathbb{P}_1(K)$ is spanned by the barycentric coordinates
$\lambda_i = \hat\lambda_i \circ F_K^{-1}$ of the element. The local finite element function that
the values at the three vertices determine is `Triangulation.localInterp` at the vertices of the
reference triangle, with the shape functions `EuclideanSpace.baryCoord`, which are the
$\hat\lambda_i$ of `AtkinsonHan.Chapter10.refBary` on `EuclideanSpace ℝ (Fin 2)`.
-/

section Example1023

open MeasureTheory TopologicalSpace EuclideanSpace

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-- **Example 10.2.3** of [han2009theoretical] (the linear element space). Let $\mathcal{T}_h$ be a
triangulation of a plane domain $\Omega$, and let $v : \mathbb{R}^2 \to \mathbb{R}$. On each
element $K$, let the local function be the $\mathbb{P}_1(K)$ function determined by the values
of $v$ at the three vertices $a_i$ of $K$. Then:

* (10.2.28) on $K$, the local function is $\sum_i v(a_i) \lambda_i$, where
  $\lambda_i = \hat\lambda_i \circ F_K^{-1}$ are the barycentric coordinates of $K$;
* the element is conforming: the local functions of two elements agree at every point of their
  common closed elements, which is the condition (10.2.6);
* the piecewise linear function $v_h$ glued from the local functions is continuous on
  $\bar\Omega$;
* $v_h$ lies in $H^1(\Omega)$.

At a common vertex, both local functions take the value of $v$ there. Along a common edge, their
difference is a linear function of one variable that vanishes at the two end points. The last
two items are the argument of Section 10.2.3: $X_h \subseteq H^1(\Omega)$ because
$X_h \subseteq C(\bar\Omega)$.

The glued function is `Triangulation.globalInterp`, the inverse $F_K^{-1}$ is
$x \mapsto T_K^{-1}(x - a_0)$ with $T_K$ = `Triangulation.linearPart`, and membership of
$H^1(\Omega)$ is `MemSobolev` with $k = 1$ and $p = 2$. That the local space consists of the
$\mathbb{P}_1(K)$ functions determined by their values at the vertices is
`AtkinsonHan.Chapter10.nodalInterp_coord_affineMap` of Section 10.3: the interpolant reproduces
every affine function. The shape functions of the reference element are
`LagrangeElement.latticeShape` for $k = 1$. The source adds that $\mathbb{P}_k$ on the nodal set
$N_k(K)$ of (10.2.29) is conforming too; this is `LagrangeElement.isConformingElement`. -/
theorem example_10_2_3 {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) (v : 𝔼₂ → ℝ) :
    (∀ (T : 𝒯.elems) (x : 𝔼₂), 𝒯.localInterp referenceTriangleVertex baryCoord T v x
      = ∑ i, v (T.1 i) * baryCoord i ((𝒯.linearPart T).symm (x - T.1 0))) ∧
    𝒯.IsConformingElement referenceTriangleVertex baryCoord ∧
    ContinuousOn (𝒯.globalInterp referenceTriangleVertex baryCoord v) (closure (Ω : Set 𝔼₂)) ∧
    MemSobolev (𝒯.globalInterp referenceTriangleVertex baryCoord v) 1 2 Ω volume := by
  refine ⟨fun T x ↦ ?_, 𝒯.isConformingElement_linear, ?_, ?_⟩
  · rw [Triangulation.localInterp_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [𝒯.affine_referenceTriangleVertex T i, mul_comm]
  · exact 𝒯.continuousOn_globalInterp _ _ 𝒯.isConformingElement_linear
      (fun i ↦ (contDiff_baryCoord i).continuous) v
  · exact 𝒯.memSobolev_globalInterp _ _ 𝒯.isConformingElement_linear
      (fun i ↦ (contDiff_baryCoord i).of_le (by simp)) v 2

end Example1023

end AtkinsonHan.Chapter10
