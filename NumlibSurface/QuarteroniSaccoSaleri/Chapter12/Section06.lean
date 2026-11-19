/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Numlib.Analysis.Sobolev.Boundary.ContDiffDomain
import Numlib.Analysis.Sobolev.Boundary.Polygon
import Numlib.LinearAlgebra.Matrix.KroneckerSum
import Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz
import Numlib.FiniteElement.Triangle

/-!
# Quarteroni, Sacco and Saleri, Section 12.6: A quick glance at the two-dimensional case

This module formalizes Section 12.6 of [quarteroni2000numerical]. The two-dimensional counterpart of
the model problem of Section 12.1 is the Poisson problem $-\Delta u = f$ in $\Omega$ with $u = 0$ on
$\partial\Omega$ (12.90). On the unit square with the grid $x_{i,j} = (ih, jh)$, $h = 1/N$, the
finite difference approximation (12.91) uses the five-point discretization of the Laplacian (12.92),
$$L_h u_h(x_{i,j}) = h^{-2} (4 u_{i,j} - u_{i+1,j} - u_{i-1,j} - u_{i,j+1} - u_{i,j-1}).$$
On the $(N - 1)^2$ interior unknowns its matrix is the pentadiagonal matrix (12.93). Indexed by
pairs, this matrix is $h^{-2}$ times the Kronecker sum $T \oplus T$ of two copies of the
one-dimensional model matrix $T = \operatorname{tridiag}(-1, 2, -1)$. So it is symmetric positive
definite and an M-matrix (Exercise 12.14).

The module also proves Green's formula (12.95) of Exercise 12.15 on a rectangle, on a bounded $C^1$
domain and on a triangulated polygon. The finite element method of the section uses the space $V_h$
of (12.94) of continuous piecewise polynomials on a triangulation, and Property 12.2 gives its error
estimate (12.96) in $H^1$. The proofs specialize `Numlib.LinearAlgebra.Matrix.KroneckerSum`, the
boundary theory of `Numlib.Analysis.Sobolev.Boundary.ContDiffDomain` and
`Numlib.Analysis.Sobolev.Boundary.Polygon`, and the finite element estimates of
`Numlib.FiniteElement.Triangle`.

## Main definitions

* (12.92), `QuarteroniSaccoSaleri.Chapter12.equation_12_92`: the five-point discrete Laplacian
  $L_h$.
* (12.91), `QuarteroniSaccoSaleri.Chapter12.IsFivePointSolution`: the five-point finite difference
  problem.
* (12.93), `QuarteroniSaccoSaleri.Chapter12.fivePointMatrix`: the matrix $h^{-2}(T \oplus T)$ of the
  scheme.
* (12.94), `QuarteroniSaccoSaleri.Chapter12.equation_12_94`: the finite element space
  $V_h \subseteq H^1_0(\Omega)$.

## Main results

* (12.93), `QuarteroniSaccoSaleri.Chapter12.equation_12_93`: the entries of the five-point matrix.
* Exercise 12.14, `QuarteroniSaccoSaleri.Chapter12.exercise_12_14`: the five-point matrix is
  symmetric positive definite and an M-matrix.
* Exercise 12.15, `QuarteroniSaccoSaleri.Chapter12.exercise_12_15_rectangle`: Green's formula
  (12.95) on a rectangle.
* Exercise 12.15, `QuarteroniSaccoSaleri.Chapter12.exercise_12_15_of_boundaryData`: Green's formula
  (12.95) on a plane domain with boundary data.
* Exercise 12.15, `QuarteroniSaccoSaleri.Chapter12.exercise_12_15`: Green's formula (12.95) on a
  bounded $C^1$ plane domain.
* Exercise 12.15, `QuarteroniSaccoSaleri.Chapter12.exercise_12_15_polygon`: Green's formula (12.95)
  on a triangulated polygon.
* (12.94), `QuarteroniSaccoSaleri.Chapter12.exists_mem_equation_12_94`: every continuous piecewise
  polynomial that vanishes on $\partial\Omega$ is an element of $V_h$.
* (12.94), `QuarteroniSaccoSaleri.Chapter12.finiteDimensional_equation_12_94`: $V_h$ is
  finite-dimensional for $k \ge 1$.
* Property 12.2, `QuarteroniSaccoSaleri.Chapter12.property_12_2`: the $H^1$ estimate (12.96) on a
  polygon with a regular family of triangulations.

## Conventions

* Grid functions are functions `ℕ → ℕ → ℝ`. The five-point stencil is written at the indices $i$,
  $i + 1$, $i + 2$ in each direction, so that `QuarteroniSaccoSaleri.Chapter12.equation_12_92 N u i
  j` is $L_h u_h$ at the interior node $x_{i+1, j+1}$. This avoids the truncated subtraction of
  natural numbers, as in Section 12.5.
* The matrix of the scheme is indexed by pairs in `Fin m × Fin m` with $m = N - 1$, not by a
  flattened index in `Fin (m ^ 2)`. The offsets of (12.93) are the row-major reading of the pairs.

## Implementation notes

* A plane domain with a boundary is described by `BoundaryData`: a surface measure on
  $\partial\Omega$ (the arclength $d\gamma$), an outward unit normal $n$, and the divergence theorem
  $\int_\Omega \operatorname{div} F = \int_{\partial\Omega} F \cdot n \, d\gamma$ for
  $F \in C^1(\bar\Omega)$. There are two instances: a bounded $C^1$ domain
  (`IsContDiffDomain.boundaryData`) and a triangulated polygon (`Triangulation.boundaryData`).
* An element of $V_h$ is an element of $H^1_0(\Omega)$ whose function agrees almost everywhere with
  a continuous piecewise polynomial that vanishes on $\partial\Omega$. No trace theorem is needed: a
  function in $H^1(\Omega)$ that is continuous on $\bar\Omega$ and vanishes on $\partial\Omega$ lies
  in $H^1_0(\Omega)$ by Theorem 9.17 of [brezis2011functional]. The piecewise polynomial lies in
  $H^1(\Omega)$ by the characterization of Sobolev functions through lines
  (`Triangulation.memSobolev_of_piecewise`), not through Green's formula (12.95).
* The $L^2$ estimate (12.97) would follow from (12.96) and the abstract Aubin–Nitsche duality
  argument. The lemmas `norm_map_sq_le_of_dual` and `norm_map_le_of_dual_approx` give $\|u -
  u_h\|_{L^2} \le M \delta \|u - u_h\|_{H^1}$ when every dual solution $\varphi_g$, defined by
  $a(v, \varphi_g) = (g, v)_{L^2}$, is approximated from $V_h$ within $\delta \|g\|_{L^2}$. This
  holds with $\delta = Ch$ once the dual solutions satisfy $\|\varphi_g\|_{H^2} \le C \|g\|_{L^2}$.
  The interpolation part is available: $\|\varphi_g - \Pi_h \varphi_g\|_{H^1} \le C h
  |\varphi_g|_{H^2}$ is `LagrangeElement.sobolevNorm_sub_globalInterp_le` with $m = 1$ and $k = 1$,
  and $\Pi_h \varphi_g \in V_h$ by `LagrangeElement.exists_mem_polySpaceZero_globalInterp`. The
  missing part is the $H^2$ regularity of the Dirichlet problem. It holds on a convex polygon
  (Theorem 3.2.1.2 of [grisvard2011elliptic]). `Elliptic.regularity_dirichlet` (Theorem 9.25 of
  [brezis2011functional]) proves it only on $C^2$ domains with bounded boundary. Convexity is
  necessary: at a re-entrant corner of angle $\omega > \pi$ the solution has the singular part
  $r^{\pi/\omega} \sin(\pi\theta/\omega) \notin H^2$, so the bound is false without it.

## Deviations from the source

* **Equations (12.91)–(12.92)** (reading). The stencil is total on natural indices and $N$. The
  solution predicate imposes zero values on all four edges and leaves exterior values
  unrestricted. See `QuarteroniSaccoSaleri.Chapter12.IsFivePointSolution`.
* **Exercise 12.14** (generalization). The grid dimension and the positive scaling parameter may
  be chosen independently. The source uses dimension $N-1$ in each coordinate. See
  `QuarteroniSaccoSaleri.Chapter12.exercise_12_14`.
* **(12.93)** (typo). The source prints the offsets $\pm(N + 1)$; for the $(N - 1)^2$ interior
  unknowns they are $\pm(N - 1)$. See `QuarteroniSaccoSaleri.Chapter12.equation_12_93`.
* **Exercise 12.15** (reading). The domain and the functions that the source calls smooth enough are
  a bounded $C^1$ domain or a triangulated polygon, with $u \in C^2(\bar\Omega)$, $\nabla u$
  continuous on $\bar\Omega$ and $v \in C^1(\bar\Omega)$. See
  `QuarteroniSaccoSaleri.Chapter12.exercise_12_15_of_boundaryData`.
* **Property 12.2** (reading). The polygon is a domain whose boundary is a union of element edges,
  and the regularity $u \in H^{l+1}(\Omega)$ and the condition $u = 0$ on $\partial\Omega$ are
  hypotheses on a representative that is continuous on $\bar\Omega$. See
  `QuarteroniSaccoSaleri.Chapter12.property_12_2`.

## Not formalized

* **Property 12.2, the $L^2$ estimate (12.97).** The estimate is $\|u - u_h\|_{L^2(\Omega)} \le C
  h^{l+1} \|u\|_{H^{l+1}(\Omega)}$ under the hypotheses of (12.96); the book quotes it, like
  (12.96), from Theorem 6.2.1 of [quarteroni1994numerical] without proof. Its proof needs the $H^2$
  regularity of the Dirichlet problem on a convex polygon, which is not formalized.
* **Green's formula (12.95) on a general Lipschitz domain.** The formula is formalized on
  rectangles, on bounded $C^1$ domains and on triangulated polygons.
-/

open scoped Kronecker

namespace QuarteroniSaccoSaleri.Chapter12

/-! ### The five-point discretization (12.91)–(12.92) -/

/-- **Equation (12.92)** of [quarteroni2000numerical]. The **five-point discrete Laplacian** on the
uniform grid of step $h = 1/N$ on the unit square, at the interior node $x_{i+1, j+1}$:
$$L_h u_h(x_{i+1,j+1}) = h^{-2} (4 u_{i+1,j+1} - u_{i+2,j+1} - u_{i,j+1} - u_{i+1,j+2} -
  u_{i+1,j}).$$

It is the centred second difference (10.65) in each direction. The factor $h^{-2}$ is written
$N^2$.

**Reading.** The stencil is a total function of natural coordinates and $N$. The source
evaluates it only at interior nodes of a nondegenerate grid. -/
noncomputable def equation_12_92 (N : ℕ) (u : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  (N : ℝ) ^ 2 * (4 * u (i + 1) (j + 1) - u (i + 2) (j + 1) - u i (j + 1)
    - u (i + 1) (j + 2) - u (i + 1) j)

/-- **Equation (12.91)** of [quarteroni2000numerical]. A grid function $u$ **solves the five-point
problem** with the data $f$ if $u_{i,j} = 0$ at the boundary indices ($i, j \le N$ with
$i \in \{0, N\}$ or $j \in \{0, N\}$), and $L_h u_h(x_{i,j}) = f_{i,j}$ at every interior node
$x_{i,j}$, $1 \le i, j \le N - 1$.

**Reading.** Zero values are imposed along all four grid edges. The predicate leaves exterior
values unrestricted and permits $N=0$. -/
def IsFivePointSolution (N : ℕ) (f : ℕ → ℕ → ℝ) (u : ℕ → ℕ → ℝ) : Prop :=
  (∀ i j, i ≤ N → j ≤ N → (i = 0 ∨ i = N ∨ j = 0 ∨ j = N) → u i j = 0) ∧
    ∀ i j, i + 2 ≤ N → j + 2 ≤ N → equation_12_92 N u i j = f (i + 1) (j + 1)

/-! ### The matrix of the scheme (12.93) -/

/-- **Equation (12.93)** of [quarteroni2000numerical], the matrix of the five-point scheme. For $N$
and $m$, the matrix indexed by pairs $(i, j)$ with $0 \le i, j < m$,
$$A = h^{-2} (T \oplus T) = h^{-2} (T \otimes I + I \otimes T), \qquad T =
  \operatorname{tridiag}(-1, 2, -1) \in \mathbb{R}^{m \times m}, \quad h = 1/N.$$

The scheme has $m = N - 1$; the definition allows any $m$. The Kronecker sum is `⊕ₖ`, and $T$ is
`Matrix.symmTridiagonalToeplitz m (-1) 2`.

**Reading.** The scaling parameter $N$ and the common interior grid dimension $m$ are
independent. The physical grid uses $m=N-1$. -/
noncomputable def fivePointMatrix (N m : ℕ) : Matrix (Fin m × Fin m) (Fin m × Fin m) ℝ :=
  ((N : ℝ) ^ 2) • (Matrix.symmTridiagonalToeplitz m (-1) 2 ⊕ₖ
    Matrix.symmTridiagonalToeplitz m (-1) 2)

/-- **Equation (12.93)** of [quarteroni2000numerical], the entries. The five-point matrix has the
entry $4h^{-2}$ on the diagonal, the entry $-h^{-2}$ in the row of $(i, j)$ and the column of
each of the four grid neighbours $(i \pm 1, j)$ and $(i, j \pm 1)$, and $0$ elsewhere.

**Typo.** The source numbers the unknowns row by row and prints the off-diagonal entries at the
offsets $\pm 1$ and $\pm(N + 1)$. For the $(N - 1)^2$ interior unknowns, a grid row has $N - 1$
unknowns, so the second offset is $\pm(N - 1)$. The statement uses pairs as indices, so no
offset appears. -/
theorem equation_12_93 (N m : ℕ) (p q : Fin m × Fin m) :
    fivePointMatrix N m p q =
      if p = q then 4 * (N : ℝ) ^ 2
      else if (p.2 = q.2 ∧ ((p.1 : ℕ) + 1 = q.1 ∨ (q.1 : ℕ) + 1 = p.1))
          ∨ (p.1 = q.1 ∧ ((p.2 : ℕ) + 1 = q.2 ∨ (q.2 : ℕ) + 1 = p.2)) then -((N : ℝ) ^ 2)
      else 0 := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  rw [fivePointMatrix, Matrix.smul_apply, smul_eq_mul, Matrix.kroneckerSum_apply,
    Matrix.symmTridiagonalToeplitz_apply', Matrix.symmTridiagonalToeplitz_apply']
  simp only [Prod.mk.injEq, Fin.ext_iff]
  split_ifs <;> simp_all
  ring

/-! ### Exercise 12.14 -/

/-- Let $c > 0$, and let $A$ be a positive definite real matrix. Then $cA$ is positive definite. -/
theorem posDef_smul {m : Type*} [Finite m] {A : Matrix m m ℝ} (hA : A.PosDef) {c : ℝ}
    (hc : 0 < c) : (c • A).PosDef := by
  classical
  have := Fintype.ofFinite m
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (hA.1.smul (IsSelfAdjoint.all c)) fun x hx => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  exact mul_pos hc (hA.dotProduct_mulVec_pos hx)

/-- **Exercise 12.14** of [quarteroni2000numerical]. For $N \ge 1$ and every $m$, the five-point
matrix (12.93) is symmetric positive definite and an M-matrix.

Positive definiteness is `Matrix.posDef_kroneckerSum` for the matrix
$T = \operatorname{tridiag}(-1, 2, -1)$ with itself. The M-matrix property follows by the
Stieltjes criterion `Matrix.IsMMatrix.of_posDef_of_offDiag_nonpos`, since the off-diagonal
entries are nonpositive. So the discrete solution satisfies the maximum principle
$Au \ge 0 \Rightarrow u \ge 0$ of
`QuarteroniSaccoSaleri.Chapter12.exercise_12_13_maximumPrinciple`.

**Generalization.** The result allows an arbitrary square tensor-grid dimension and any
positive scaling parameter $N$. -/
theorem exercise_12_14 {N m : ℕ} (hN : N ≠ 0) :
    (fivePointMatrix N m).PosDef ∧ (fivePointMatrix N m).IsMMatrix := by
  have hc : (0 : ℝ) < (N : ℝ) ^ 2 := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero hN)
    positivity
  have hpd : (fivePointMatrix N m).PosDef :=
    posDef_smul (Matrix.posDef_kroneckerSum (Matrix.posDef_symmTridiagonalToeplitz_neg_one_two m)
      (Matrix.posDef_symmTridiagonalToeplitz_neg_one_two m)) hc
  refine ⟨hpd, Matrix.IsMMatrix.of_posDef_of_offDiag_nonpos hpd fun p q hpq => ?_⟩
  rw [equation_12_93]
  split_ifs with h1 h2
  · exact absurd h1 hpq
  · linarith
  · exact le_rfl

/-! ### Green's formula (12.95) on a rectangle -/

section Green

open Set MeasureTheory

/-- **Exercise 12.15** of [quarteroni2000numerical], Green's formula (12.95) on a rectangle. Let
$\Omega = (a_1, b_1) \times (a_2, b_2)$ with $a_1 \le b_1$ and $a_2 \le b_2$, let
$u \in C^2(\mathbb{R}^2)$ and $v \in C^1(\mathbb{R}^2)$. Then
$$\int_\Omega (-\Delta u) v \, dx = \int_\Omega \nabla u \cdot \nabla v \, dx -
  \int_{\partial\Omega} (\nabla u \cdot n) v \, d\gamma,$$
where the boundary integral is the sum over the four sides with the outward normals $n = (1, 0)$
on $x = b_1$, $(-1, 0)$ on $x = a_1$, $(0, 1)$ on $y = b_2$ and $(0, -1)$ on $y = a_2$:
$$\int_{a_2}^{b_2} (\partial_1 u \, v)(b_1, y) \, dy - \int_{a_2}^{b_2} (\partial_1 u \, v)(a_1,
  y) \, dy + \int_{a_1}^{b_1} (\partial_2 u \, v)(x, b_2) \, dx - \int_{a_1}^{b_1} (\partial_2 u
  \, v)(x, a_2) \, dx.$$

The proof follows the hint of the exercise: $\operatorname{div}(v \nabla u) = v \Delta u +
\nabla u \cdot \nabla v$, integrated over $\Omega$, with Mathlib's divergence theorem for a
rectangle `MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le`
applied to $(v \partial_1 u, v \partial_2 u)$. The partial derivatives are `fderiv ℝ w p (1, 0)`
and `fderiv ℝ w p (0, 1)`, and the integral over $\Omega$ is over the closed rectangle
`Icc a b`.

**Reading.** Specialization to a rectangle with explicit four-edge integral.
-/
theorem exercise_12_15_rectangle {u v : ℝ × ℝ → ℝ} (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 1 v)
    {a b : ℝ × ℝ} (hab : a ≤ b) :
    (∫ p in Icc a b,
        -(fderiv ℝ (fun q => fderiv ℝ u q (1, 0)) p (1, 0)
          + fderiv ℝ (fun q => fderiv ℝ u q (0, 1)) p (0, 1)) * v p)
      = (∫ p in Icc a b,
          fderiv ℝ u p (1, 0) * fderiv ℝ v p (1, 0)
            + fderiv ℝ u p (0, 1) * fderiv ℝ v p (0, 1))
        - ((∫ y in a.2..b.2, fderiv ℝ u (b.1, y) (1, 0) * v (b.1, y))
            - (∫ y in a.2..b.2, fderiv ℝ u (a.1, y) (1, 0) * v (a.1, y))
            + (∫ x in a.1..b.1, fderiv ℝ u (x, b.2) (0, 1) * v (x, b.2))
            - (∫ x in a.1..b.1, fderiv ℝ u (x, a.2) (0, 1) * v (x, a.2))) := by
  have hu1 : ContDiff ℝ 1 fun q => fderiv ℝ u q (1, 0) :=
    (hu.fderiv_right (m := 1) le_rfl).clm_apply contDiff_const
  have hu2 : ContDiff ℝ 1 fun q => fderiv ℝ u q (0, 1) :=
    (hu.fderiv_right (m := 1) le_rfl).clm_apply contDiff_const
  have hcv1 : Continuous fun p => fderiv ℝ v p (1, 0) :=
    (hv.fderiv_right (m := 0) le_rfl).continuous.clm_apply continuous_const
  have hcv2 : Continuous fun p => fderiv ℝ v p (0, 1) :=
    (hv.fderiv_right (m := 0) le_rfl).continuous.clm_apply continuous_const
  have hcu11 : Continuous fun p => fderiv ℝ (fun q => fderiv ℝ u q (1, 0)) p (1, 0) :=
    (hu1.fderiv_right (m := 0) le_rfl).continuous.clm_apply continuous_const
  have hcu22 : Continuous fun p => fderiv ℝ (fun q => fderiv ℝ u q (0, 1)) p (0, 1) :=
    (hu2.fderiv_right (m := 0) le_rfl).continuous.clm_apply continuous_const
  set f : ℝ × ℝ → ℝ := fun p => fderiv ℝ u p (1, 0) * v p with hf
  set g : ℝ × ℝ → ℝ := fun p => fderiv ℝ u p (0, 1) * v p with hg
  set f' : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ) := fun p =>
    fderiv ℝ u p (1, 0) • fderiv ℝ v p
      + v p • fderiv ℝ (fun q => fderiv ℝ u q (1, 0)) p with hf'
  set g' : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ) := fun p =>
    fderiv ℝ u p (0, 1) • fderiv ℝ v p
      + v p • fderiv ℝ (fun q => fderiv ℝ u q (0, 1)) p with hg'
  have hdf : ∀ p : ℝ × ℝ, HasFDerivAt f (f' p) p := fun p =>
    (hu1.differentiable one_ne_zero p).hasFDerivAt.mul
      (hv.differentiable one_ne_zero p).hasFDerivAt
  have hdg : ∀ p : ℝ × ℝ, HasFDerivAt g (g' p) p := fun p =>
    (hu2.differentiable one_ne_zero p).hasFDerivAt.mul
      (hv.differentiable one_ne_zero p).hasFDerivAt
  have hcf : Continuous f := hu1.continuous.mul hv.continuous
  have hcg : Continuous g := hu2.continuous.mul hv.continuous
  have hsplit : ∀ p : ℝ × ℝ, f' p (1, 0) + g' p (0, 1)
      = (fderiv ℝ u p (1, 0) * fderiv ℝ v p (1, 0)
          + fderiv ℝ u p (0, 1) * fderiv ℝ v p (0, 1))
        + (fderiv ℝ (fun q => fderiv ℝ u q (1, 0)) p (1, 0)
            + fderiv ℝ (fun q => fderiv ℝ u q (0, 1)) p (0, 1)) * v p := by
    intro p
    simp only [hf', hg', add_apply, smul_apply, smul_eq_mul]
    ring
  have hK : IsCompact (Icc a b) := isCompact_Icc
  have hGrad : IntegrableOn (fun p : ℝ × ℝ => fderiv ℝ u p (1, 0) * fderiv ℝ v p (1, 0)
      + fderiv ℝ u p (0, 1) * fderiv ℝ v p (0, 1)) (Icc a b) :=
    ((hu1.continuous.mul hcv1).add (hu2.continuous.mul hcv2)).continuousOn.integrableOn_compact hK
  have hLap : IntegrableOn (fun p : ℝ × ℝ =>
      (fderiv ℝ (fun q => fderiv ℝ u q (1, 0)) p (1, 0)
        + fderiv ℝ (fun q => fderiv ℝ u q (0, 1)) p (0, 1)) * v p) (Icc a b) :=
    ((hcu11.add hcu22).mul hv.continuous).continuousOn.integrableOn_compact hK
  have hi : IntegrableOn (fun p => f' p (1, 0) + g' p (0, 1)) (Icc a b) :=
    (hGrad.add hLap).congr_fun (fun p _ => (hsplit p).symm) measurableSet_Icc
  have hdiv := MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le
    f g f' g' a b hab ∅ Set.countable_empty hcf.continuousOn hcg.continuousOn
    (fun p _ => hdf p) (fun p _ => hdg p) hi
  have hI : (∫ p in Icc a b, (f' p (1, 0) + g' p (0, 1)))
      = (∫ p in Icc a b, fderiv ℝ u p (1, 0) * fderiv ℝ v p (1, 0)
          + fderiv ℝ u p (0, 1) * fderiv ℝ v p (0, 1))
        + ∫ p in Icc a b, (fderiv ℝ (fun q => fderiv ℝ u q (1, 0)) p (1, 0)
            + fderiv ℝ (fun q => fderiv ℝ u q (0, 1)) p (0, 1)) * v p := by
    rw [← integral_add hGrad hLap]
    exact setIntegral_congr_fun measurableSet_Icc fun p _ => hsplit p
  have hneg : (∫ p in Icc a b,
      -(fderiv ℝ (fun q => fderiv ℝ u q (1, 0)) p (1, 0)
        + fderiv ℝ (fun q => fderiv ℝ u q (0, 1)) p (0, 1)) * v p)
      = -∫ p in Icc a b, (fderiv ℝ (fun q => fderiv ℝ u q (1, 0)) p (1, 0)
          + fderiv ℝ (fun q => fderiv ℝ u q (0, 1)) p (0, 1)) * v p := by
    rw [← integral_neg]
    exact setIntegral_congr_fun measurableSet_Icc fun p _ => by ring
  rw [hneg]
  rw [hI] at hdiv
  simp only [hf, hg] at hdiv
  linarith

/-!
### Green's formula (12.95) on a bounded $C^1$ domain and on a triangulated polygon

These statements use a plane domain $\Omega$ with boundary data `B : BoundaryData Ω`. The data
consist of a surface measure `B.σ` on the boundary (the arclength), an outward unit normal `B.ν`
(the normal $n$ of the book), and the divergence theorem $\int_\Omega \operatorname{div} F =
\int_{\partial\Omega} F \cdot n \, d\gamma$ for $F \in C^1(\bar\Omega)$. The instance for a bounded
$C^1$ domain is `IsContDiffDomain.boundaryData`; its divergence theorem follows from Fubini's
theorem and the fundamental theorem of calculus on graph charts, glued by a partition of unity. The
instance for a triangulated polygon is `Triangulation.boundaryData`; its divergence theorem is the
sum over the elements, in which the integrals over interior edges cancel in pairs.
-/

open TopologicalSpace

open scoped InnerProductSpace Laplacian

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-- **Exercise 12.15** of [quarteroni2000numerical], Green's formula (12.95) for boundary data. Let
$\Omega \subseteq \mathbb{R}^2$ be open with boundary data $B$, that is, an arclength measure
$d\gamma$ on $\partial\Omega$, an outward unit normal $n$ and the divergence theorem. Let
$u \in C^2(\bar\Omega)$ with $\nabla u$ continuous on $\bar\Omega$, and let
$v \in C^1(\bar\Omega)$ be continuous on $\bar\Omega$. Then
$$\int_\Omega (-\Delta u) v \, dx = \int_\Omega \nabla u \cdot \nabla v \, dx -
  \int_{\partial\Omega} (\nabla u \cdot n) v \, d\gamma.$$

**Reading.** The source asks for $u$ and $v$ smooth enough. The statement reads this as
`ContDiffOnClosure ℝ 2 u Ω` and `ContinuousOn (fderiv ℝ u) (closure Ω)` for $u$, and
`ContinuousOn v (closure Ω)` and `ContDiffOnClosure ℝ 1 v Ω` for $v$. The continuity of
$\nabla u$ on $\bar\Omega$ gives a meaning to the boundary term $\nabla u \cdot n$: the class
`ContDiffOnClosure` says that the derivatives extend continuously to $\bar\Omega$, not that
`fderiv ℝ u` is that extension on $\partial\Omega$.

The proof follows the hint of the exercise, $\operatorname{div}(v \nabla u) = v \Delta u +
\nabla u \cdot \nabla v$ with the divergence theorem `BoundaryData.integral_div_eq`; it is
`BoundaryData.integral_laplacian_mul_add_eq_of_continuousOn_fderiv` with the terms rearranged.
The two instances are `QuarteroniSaccoSaleri.Chapter12.exercise_12_15` and
`QuarteroniSaccoSaleri.Chapter12.exercise_12_15_polygon`. -/
theorem exercise_12_15_of_boundaryData {Ω : Opens 𝔼₂} (B : BoundaryData Ω) {u v : 𝔼₂ → ℝ}
    (hu : ContDiffOnClosure ℝ 2 u Ω) (hu' : ContinuousOn (fderiv ℝ u) (closure (Ω : Set 𝔼₂)))
    (hv : ContinuousOn v (closure (Ω : Set 𝔼₂))) (hv' : ContDiffOnClosure ℝ 1 v Ω) :
    ∫ x in (Ω : Set 𝔼₂), -Δ u x * v x
      = (∫ x in (Ω : Set 𝔼₂), ⟪gradient u x, gradient v x⟫_ℝ)
        - ∫ x, ⟪gradient u x, B.ν x⟫_ℝ * v x ∂B.σ := by
  have h := B.integral_laplacian_mul_add_eq_of_continuousOn_fderiv hu' hu hv hv'
  simp only [neg_mul, integral_neg]
  linarith

/-- **Exercise 12.15** of [quarteroni2000numerical], Green's formula (12.95) on a bounded $C^1$
plane domain. Let $\Omega \subseteq \mathbb{R}^2$ be a bounded open set with $C^1$ boundary:
$\partial\Omega$ is locally the graph of a $C^1$ function after a rigid motion. Let $n$ be its
outward unit normal and $d\gamma$ the arclength measure on $\partial\Omega$. Let
$u \in C^2(\bar\Omega)$ with $\nabla u$ continuous on $\bar\Omega$, and let
$v \in C^1(\bar\Omega)$ be continuous on $\bar\Omega$. Then
$$\int_\Omega (-\Delta u) v \, dx = \int_\Omega \nabla u \cdot \nabla v \, dx -
  \int_{\partial\Omega} (\nabla u \cdot n) v \, d\gamma.$$

**Reading.** The source asks for a domain that is smooth enough. This statement takes a bounded
$C^1$ domain, `IsContDiffDomain 1 Ω`; `QuarteroniSaccoSaleri.Chapter12.exercise_12_15_polygon`
takes a triangulated polygon. The reading of the smoothness of $u$ and $v$ is that of
`QuarteroniSaccoSaleri.Chapter12.exercise_12_15_of_boundaryData`.

The normal is `IsContDiffDomain.outwardNormal` and the measure is
`IsContDiffDomain.boundaryMeasure`. This is
`QuarteroniSaccoSaleri.Chapter12.exercise_12_15_of_boundaryData` for
`IsContDiffDomain.boundaryData`, whose divergence theorem is `IsContDiffDomain.integral_div_eq`. -/
theorem exercise_12_15 {Ω : Opens 𝔼₂} (hΩ : IsContDiffDomain 1 (Ω : Set 𝔼₂))
    (hb : Bornology.IsBounded (Ω : Set 𝔼₂)) {u v : 𝔼₂ → ℝ}
    (hu : ContDiffOnClosure ℝ 2 u Ω) (hu' : ContinuousOn (fderiv ℝ u) (closure (Ω : Set 𝔼₂)))
    (hv : ContinuousOn v (closure (Ω : Set 𝔼₂))) (hv' : ContDiffOnClosure ℝ 1 v Ω) :
    ∫ x in (Ω : Set 𝔼₂), -Δ u x * v x
      = (∫ x in (Ω : Set 𝔼₂), ⟪gradient u x, gradient v x⟫_ℝ)
        - ∫ x, ⟪gradient u x, hΩ.outwardNormal hb x⟫_ℝ * v x ∂(hΩ.boundaryMeasure hb) :=
  exercise_12_15_of_boundaryData (hΩ.boundaryData hb) hu hu' hv hv'

/-- **Exercise 12.15** of [quarteroni2000numerical], Green's formula (12.95) on a triangulated
polygon. Let $\Omega \subseteq \mathbb{R}^2$ be open with a triangulation $\mathcal{T}$, let $n$
be the outward unit normal on the boundary edges and $d\gamma$ the arclength measure on them.
Let $u \in C^2(\bar\Omega)$ with $\nabla u$ continuous on $\bar\Omega$, and let
$v \in C^1(\bar\Omega)$ be continuous on $\bar\Omega$. Then
$$\int_\Omega (-\Delta u) v \, dx = \int_\Omega \nabla u \cdot \nabla v \, dx -
  \int_{\partial\Omega} (\nabla u \cdot n) v \, d\gamma.$$

**Reading.** The source asks for a domain that is smooth enough. This statement takes a
triangulated polygon; `QuarteroniSaccoSaleri.Chapter12.exercise_12_15` takes a bounded $C^1$
domain. The reading of the smoothness of $u$ and $v$ is that of
`QuarteroniSaccoSaleri.Chapter12.exercise_12_15_of_boundaryData`.

No hypothesis beyond the axioms of `Triangulation` is needed: the divergence theorem
`Triangulation.integral_div_eq` holds for every triangulation, because a field that is
continuous across an interior edge does not see it. The normal is `Triangulation.outwardNormal`
and the measure is `Triangulation.boundaryMeasure`. This is
`QuarteroniSaccoSaleri.Chapter12.exercise_12_15_of_boundaryData` for
`Triangulation.boundaryData`. -/
theorem exercise_12_15_polygon {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) {u v : 𝔼₂ → ℝ}
    (hu : ContDiffOnClosure ℝ 2 u Ω) (hu' : ContinuousOn (fderiv ℝ u) (closure (Ω : Set 𝔼₂)))
    (hv : ContinuousOn v (closure (Ω : Set 𝔼₂))) (hv' : ContDiffOnClosure ℝ 1 v Ω) :
    ∫ x in (Ω : Set 𝔼₂), -Δ u x * v x
      = (∫ x in (Ω : Set 𝔼₂), ⟪gradient u x, gradient v x⟫_ℝ)
        - ∫ x, ⟪gradient u x, 𝒯.outwardNormal x⟫_ℝ * v x ∂𝒯.boundaryMeasure :=
  exercise_12_15_of_boundaryData 𝒯.boundaryData hu hu' hv hv'

end Green


/-!
### The finite element space (12.94) and Property 12.2

The space $V_h$ of (12.94) is `Triangulation.polySpaceZero`. Property 12.2 specializes
`FiniteElement.norm_sub_le_of_isGalerkinSolution_dirichletForm`, Céa's lemma with the global
interpolation estimate, to the $\mathbb{P}_k$ Lagrange element on the principal lattice
(`LagrangeElement.node`, `LagrangeElement.shape`). This element has the Lagrange basis (8.36)–(8.37)
of Section 8.5.2 as its global basis.
-/

section FiniteElement

open MeasureTheory Set TopologicalSpace EuclideanSpace Filter
open scoped ENNReal

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-- **Equation (12.94)** of [quarteroni2000numerical]. For a triangulation $\mathcal{T}_h$ of a
plane domain $\Omega$ and a degree $k$, the **finite element space**
$$V_h = \{ v_h \in C^0(\bar\Omega) : v_h|_T \in \mathbb{P}_k(T) \text{ for all } T \in
  \mathcal{T}_h, \ v_h|_{\partial\Omega} = 0 \},$$
as a subspace of $H^1_0(\Omega)$. Its elements are the $w \in H^1_0(\Omega)$ whose function
agrees almost everywhere on $\Omega$ with a function that is continuous on $\bar\Omega$,
polynomial of degree at most $k$ on each closed element, and zero on $\partial\Omega$.

The definition is `Triangulation.polySpaceZero`, and the piecewise polynomial condition is
`Triangulation.IsPiecewisePoly`; a polynomial on an element is a polynomial in the reference
coordinates of the element. By `QuarteroniSaccoSaleri.Chapter12.exists_mem_equation_12_94`,
every function of the book's space is the function of an element of $V_h$. -/
noncomputable def equation_12_94 {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) (k : ℕ) :
    Submodule ℝ (SobolevEuclideanZero 2 1 2 Ω) :=
  𝒯.polySpaceZero 2 k

/-- **Equation (12.94)** of [quarteroni2000numerical], membership. An element $w \in H^1_0(\Omega)$
lies in $V_h$ if and only if there is a function $v$ that is continuous on $\bar\Omega$,
piecewise polynomial of degree at most $k$ on $\mathcal{T}$, zero on $\partial\Omega$, and equal
to the function of $w$ almost everywhere on $\Omega$. -/
theorem mem_equation_12_94_iff {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) (k : ℕ)
    {w : SobolevEuclideanZero 2 1 2 Ω} :
    w ∈ equation_12_94 𝒯 k ↔ ∃ v : 𝔼₂ → ℝ, ContinuousOn v (closure (Ω : Set 𝔼₂)) ∧
      𝒯.IsPiecewisePoly k v ∧ EqOn v 0 (frontier (Ω : Set 𝔼₂)) ∧
      SobolevMultiIndex.fn (w : SobolevEuclidean 2 1 2 Ω) =ᵐ[volume.restrict (Ω : Set 𝔼₂)] v :=
  Iff.rfl

/-- **Equation (12.94)** of [quarteroni2000numerical], the book's functions. Let $v$ be continuous
on $\bar\Omega$, piecewise polynomial of degree at most $k$ on $\mathcal{T}$, and zero on
$\partial\Omega$. Then there is $w \in V_h$ whose function equals $v$ almost everywhere on
$\Omega$. In particular, $v$ lies in $H^1_0(\Omega)$. -/
theorem exists_mem_equation_12_94 {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) {k : ℕ} {v : 𝔼₂ → ℝ}
    (hvc : ContinuousOn v (closure (Ω : Set 𝔼₂))) (hvp : 𝒯.IsPiecewisePoly k v)
    (hv0 : EqOn v 0 (frontier (Ω : Set 𝔼₂))) :
    ∃ w ∈ equation_12_94 𝒯 k,
      SobolevMultiIndex.fn (w : SobolevEuclidean 2 1 2 Ω) =ᵐ[volume.restrict (Ω : Set 𝔼₂)] v :=
  𝒯.exists_mem_polySpaceZero 2 (by simp) hvc hvp hv0

/-- **Equation (12.94)** of [quarteroni2000numerical], dimension. For $k \ge 1$, the space $V_h$ is
finite-dimensional.

Its elements are determined by their values at the nodes of the $\mathbb{P}_k$ Lagrange element.
This is `Triangulation.finiteDimensional_polySpaceZero`. -/
theorem finiteDimensional_equation_12_94 {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) {k : ℕ}
    (hk : 1 ≤ k) : FiniteDimensional ℝ (equation_12_94 𝒯 k) :=
  LagrangeElement.finiteDimensional_polySpaceZero hk 𝒯 2

/-- **Property 12.2** of [quarteroni2000numerical], the estimate (12.96). Let
$\Omega \subseteq \mathbb{R}^2$ be open with $\Omega \subseteq B(0, R)$, $R \ge 0$. Let
$\{\mathcal{T}_h\}$ be a regular family of triangulations of $\Omega$ with mesh sizes at most
$H$, such that $\partial\Omega$ is a union of element edges for each $\mathcal{T}_h$. Let
$1 \le l \le k$. Then there is a constant $C \ge 0$ with the following property. Let
$f \in L^2(\Omega)$, and let $u \in H^1_0(\Omega)$ solve the Poisson problem (12.90),
$\int_\Omega \nabla u \cdot \nabla v = \int_\Omega f v$ for all $v \in H^1_0(\Omega)$. For each
$h$, let $u_h$ be the Galerkin solution in the space $V_h$ of (12.94) of degree $k$. Let
$\tilde u$ be a function equal to $u$ almost everywhere, with $\tilde u \in H^{l+1}(\Omega)$,
$\tilde u$ continuous on $\bar\Omega$ and $\tilde u = 0$ on $\partial\Omega$. Then for every $h$
$$\|u - u_h\|_{H^1_0(\Omega)} \le \frac{M}{\alpha_0} C h^l \|\tilde u\|_{H^{l+1}(\Omega)},$$
where $M = 1$ is the continuity constant of the form and $\alpha_0 = (1 + (2R)^2)^{-1}$ is its
coercivity constant on $H^1_0(\Omega)$ by the Poincaré inequality. The constant $C$ does not
depend on $h$, $f$ or $u$.

**Reading.** The source states the estimate on a polygon for $u \in H^s(\Omega)$, $s \ge 2$,
with $l = \min(k, s - 1)$. The statement takes the polygon as a domain whose boundary is a union
of element edges (`Triangulation.FrontierSubsetEdges`), and it states the regularity
$u \in H^{l+1}(\Omega)$ and the boundary condition $u = 0$ on $\partial\Omega$ as hypotheses on
a representative $\tilde u$ that is continuous on $\bar\Omega$. On a $C^1$ domain the boundary
condition would follow from $u \in H^1_0(\Omega)$. The condition $k \ge 1$ of the source follows
from $1 \le l \le k$.

The book quotes the estimate from Theorem 6.2.1 of [quarteroni1994numerical]. The proof is
`FiniteElement.norm_sub_le_of_isGalerkinSolution_dirichletForm`: Céa's lemma
`IsGalerkinSolution.norm_sub_le` with $v_h = \Pi_h u$ and the global interpolation estimate for
the $\mathbb{P}_k$ Lagrange element. The interpolant $\Pi_h \tilde u$ lies in $V_h$ because the
Lagrange element is conforming, polynomial and edge unisolvent, so it vanishes on
$\partial\Omega$ with $\tilde u$ (`LagrangeElement.exists_mem_polySpaceZero_globalInterp`). A
regular family is `FiniteElement.IsRegularFamily`: the elements satisfy $h_K \le \sigma \rho_K$
for a fixed $\sigma$, and the mesh sizes tend to $0$ along the filter that indexes the family.
The factor $M / \alpha_0$ is `1 / (1 + (2 * R) ^ 2)⁻¹` in the code, and the exponent $l$ is `s`.
The $L^2$ estimate (12.97) is not formalized. -/
theorem property_12_2 {k : ℕ} {Ω : Opens 𝔼₂} {ι : Type*} {l : Filter ι}
    {𝒯 : ι → Triangulation Ω}
    (hreg : FiniteElement.IsRegularFamily l fun i ↦ Set.range (𝒯 i).K)
    {H : ℝ} (hH : ∀ i, (𝒯 i).meshSize ≤ H) (hedge : ∀ i, (𝒯 i).FrontierSubsetEdges)
    {R : ℝ} (hR : 0 ≤ R) (hΩ : (Ω : Set 𝔼₂) ⊆ Metric.ball 0 R) {s : ℕ} (hs : 1 ≤ s) (hsk : s ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼₂)))
      (u : SobolevEuclideanZero 2 1 2 Ω),
      (∀ v : SobolevEuclideanZero 2 1 2 Ω, Elliptic.dirichletForm Ω u v = Elliptic.load Ω f v) →
      ∀ uh : ι → SobolevEuclideanZero 2 1 2 Ω,
        (∀ i, IsGalerkinSolution
          ((Elliptic.dirichletForm Ω).restrict (SobolevEuclideanZero 2 1 2 Ω))
          ((Elliptic.load Ω f).comp (SobolevEuclideanZero 2 1 2 Ω).subtypeL)
          (equation_12_94 (𝒯 i) k) (uh i)) →
        ∀ ũ : 𝔼₂ → ℝ,
          SobolevMultiIndex.fn (u : SobolevEuclidean 2 1 2 Ω) =ᵐ[volume.restrict (Ω : Set 𝔼₂)] ũ →
          MemSobolev ũ (s + 1) 2 Ω volume → ContinuousOn ũ (closure (Ω : Set 𝔼₂)) →
          EqOn ũ 0 (frontier (Ω : Set 𝔼₂)) →
          ∀ i, ‖u - uh i‖ ≤ (1 / (1 + (2 * R) ^ 2)⁻¹) * C * (𝒯 i).meshSize ^ s
            * (sobolevNorm ũ (s + 1) 2 Ω volume).toReal :=
  FiniteElement.norm_sub_le_of_isGalerkinSolution_dirichletForm hs hsk hreg hH hedge hR hΩ

end FiniteElement

end QuarteroniSaccoSaleri.Chapter12
