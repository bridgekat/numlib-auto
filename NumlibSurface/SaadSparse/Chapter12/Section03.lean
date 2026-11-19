/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Numlib.Preconditioner.Chebyshev
import Numlib.Preconditioner.Polynomial
import Numlib.RingTheory.Polynomial.KernelPolynomial
import NumlibSurface.SaadSparse.Common

/-!
# Saad, Section 12.3: Polynomial preconditioners

This module formalizes Section 12.3 of [saad2003iterative]: preconditioners of the form
$M^{-1} = s(A)$ for a polynomial $s$ of low degree, so that the preconditioner is applied with
matrix-vector products alone. The section gives three ways to choose $s$: the Neumann series
(Section 12.3.1), Chebyshev acceleration (Section 12.3.2, Algorithm 12.1) and least-squares
polynomials (Section 12.3.3). For a symmetric matrix whose quadratic form lies in $[\alpha, \beta]$,
the preconditioned operator $s(A) A$ differs from the identity by at most $\max_{\lambda \in
[\alpha, \beta]} |1 - \lambda s(\lambda)|$ (12.5), and the shifted Chebyshev polynomial makes this
maximum as small as possible (12.4). Chebyshev acceleration produces the residuals
$r_k = T_k(A) r_0$ with the residual polynomial $T_k(t) = C_k((\theta - t)/\delta) /
C_k(\theta/\delta)$, $\theta = (\beta + \alpha)/2$, $\delta = (\beta - \alpha)/2$, without computing
inner products. A least-squares polynomial minimizes a weighted $L^2$ norm of
$1 - \lambda s(\lambda)$ instead, and the kernel polynomial (12.12) of an orthonormal family is the
minimizer.

The section has no numbered result, so the declarations are named for the displayed equations. The
proofs specialize `Numlib.Preconditioner.Polynomial`, `Numlib.Preconditioner.Chebyshev` and
`Numlib.RingTheory.Polynomial.KernelPolynomial`. The surface adds the real-matrix reading and the
identification of the residual polynomial $T_k$ with `Polynomial.Chebyshev.shifted k α β 0`
(`SaadSparse.Chapter12.T_k_eq_shifted`), where this chapter meets the Chebyshev min–max theorem of
Section 6.11.

## Main definitions

* Algorithm 12.1, `SaadSparse.Chapter12.chebyshevIterate`: the state of Chebyshev acceleration after
  $k$ steps.
* Equation (12.10), `SaadSparse.Chapter12.bilinFormOfWeight`: the weighted inner product $\langle p,
  q \rangle_w = \int_\alpha^\beta p q w$.
* Section 12.3.3, `SaadSparse.Chapter12.IsLeastSquaresResidual`: a least-squares residual polynomial
  of degree $k$.
* Equation (12.16), `SaadSparse.Chapter12.kappa_12_16`: the coefficients $\kappa_j^{(k)}$.
* Equation (12.16), `SaadSparse.Chapter12.equation_12_16`: the closed form of the residual
  polynomial for the Jacobi weight.

## Main results

* Equation (12.3), `SaadSparse.Chapter12.equation_12_3`: the Neumann preconditioner satisfies
  $M^{-1} A = \omega^{-1} (I - N^{s+1})$.
* Section 12.3.1, `SaadSparse.Chapter12.neumann_isSymmetric_withEnergy`: $s(D^{-1} A) D^{-1} A$ is
  self-adjoint for the $D$-inner product.
* Equation (12.5), `SaadSparse.Chapter12.equation_12_5`: $\|x - s(A) A x\| \le \max_{[\alpha,
  \beta]} |1 - \lambda s(\lambda)| \, \|x\|$.
* Equations (12.4)–(12.5), `SaadSparse.Chapter12.equation_12_4`: the lower bound
  $1 / C_{k+1}((\beta + \alpha)/(\beta - \alpha))$ for the min–max problem.
* Section 12.3.2, `SaadSparse.Chapter12.T_k_eq_shifted`: the residual polynomial $T_k$ is the
  shifted Chebyshev polynomial.
* Section 12.3.2, `SaadSparse.Chapter12.equation_12_7`: the three-term recurrence of
  $\sigma_k = C_k(\theta/\delta)$.
* Equation (12.7), `SaadSparse.Chapter12.equation_12_6`: $\rho_{k+1} = (2 \sigma_1 - \rho_k)^{-1}$.
* Equation (12.8), `SaadSparse.Chapter12.equation_12_8`: the three-term recurrence of the residual
  polynomials.
* Algorithm 12.1, `SaadSparse.Chapter12.equation_12_9`: the direction recurrence derived from
  (12.9).
* Section 12.3.2, `SaadSparse.Chapter12.chebyshev_residual_eq`: $r_k = T_k(A) r_0$.
* Section 12.3.2, `SaadSparse.Chapter12.norm_chebyshev_residual_le`: $\|r_k\| \le 2
  ((\sqrt{\kappa} - 1)/(\sqrt{\kappa} + 1))^k \|r_0\|$.
* Section 12.3.2, `SaadSparse.Chapter12.norm_residual_minRes_le_chebyshev`: a minimal-residual
  iterate is at least as good as Chebyshev acceleration.
* Equation (12.10), `SaadSparse.Chapter12.bilinFormOfWeight_isSymm`: the weighted form is symmetric.
* Section 12.3.3, `SaadSparse.Chapter12.bilinFormOfWeight_le`: $\langle p, p \rangle_w \le
  (\max_{[\alpha, \beta]} |p|)^2 \langle 1, 1 \rangle_w$.
* Equation (12.12), `SaadSparse.Chapter12.equation_12_12`: the kernel polynomial is the
  least-squares residual polynomial.
* Equations (12.13)–(12.14), `SaadSparse.Chapter12.equation_12_13`: the least-squares polynomial
  $s_{k-1}$ in closed form.
* Section 12.3.3, `SaadSparse.Chapter12.leastSquaresResidual_orthogonal`: the residual polynomials
  are orthogonal for the weight $\lambda w(\lambda)$.
* Section 12.3.3, `SaadSparse.Chapter12.norm_leastSquaresResidual_le`: the least-squares residual
  decays geometrically for $0 < \alpha < \beta$.
* Example 12.1, `SaadSparse.Chapter12.example_12_1`: the table of the least-squares polynomials
  $s_1, \dots, s_8$.

## Conventions

* Matrices are real, $A \in \mathbb{R}^{n \times n}$, and act on `EuclideanSpace ℝ (Fin n)`. A
  polynomial $s$ is applied to $A$ through `Polynomial.aeval` of `Matrix.toEuclideanLin A`.
* "The spectrum of $A$ lies in $[\alpha, \beta]$" is the quadratic-form bound
  `LinearMap.IsSymmetricBoundedBy α β`: $A$ is symmetric and
  $\alpha \|x\|^2 \le (Ax, x) \le \beta \|x\|^2$.
* $C_k$ is the Chebyshev polynomial `Polynomial.Chebyshev.T ℝ k`, and a maximum over
  $[\alpha, \beta]$ is `sSup` of the image of `Set.Icc α β`.

## Implementation notes

* The closed form (12.16) for the Jacobi weight (12.15) is a definition, and it is not identified
  with `SaadSparse.Chapter12.IsLeastSquaresResidual`: the identification needs Jacobi polynomials
  and their orthogonality, which Mathlib does not have. `SaadSparse.Chapter12.example_12_1` is what
  the book computes from it, the eight least-squares polynomials for $\mu = 1/2$ and $\nu = -1/2$,
  each identity cleared of the division by $\lambda$.
* The declaration `SaadSparse.Chapter12.equation_12_6` states (12.7), the recurrence of $\rho_k$;
  (12.6) is the definition of $\rho_k$, `Preconditioner.Chebyshev.rho`. The declaration
  `SaadSparse.Chapter12.equation_12_7` states the recurrence of $\sigma_k$, a display before (12.6)
  that has no number.

## Deviations from the source

* **(12.3)** (scope). `SaadSparse.Chapter12.equation_12_3` states the finite geometric
  identity in the display after the approximate-inverse formula. It requires $\omega\ne0$ and
  uses the total inverse of $D$. `SaadSparse.Chapter12.neumann_isSymmetric_withEnergy` uses any
  real polynomial and any positive definite $D$.
* **(12.4) and (12.5)** (scope). `SaadSparse.Chapter12.equation_12_4` gives a lower bound for
  the interval objective of (12.5) on a positive nondegenerate interval. Printed (12.4) uses the
  discrete spectrum. `SaadSparse.Chapter12.equation_12_5` bounds the operator error by the
  interval objective.
* **(12.6), (12.7), (12.9) and Algorithm 12.1** (source location and reading).
  `SaadSparse.Chapter12.equation_12_6` gives the recurrence printed as (12.7), and
  `SaadSparse.Chapter12.equation_12_7` gives the unnumbered $\sigma_k$ recurrence.
  `SaadSparse.Chapter12.equation_12_9` gives the direction recurrence in Algorithm 12.1. The
  printed (12.9) is the preceding scalar difference quotient.
  `SaadSparse.Chapter12.chebyshevIterate` takes a fixed step count and starts with the
  algorithm's $\rho_0=1/\sigma_1$.
* **§12.3.2** (extensions). `SaadSparse.Chapter12.norm_chebyshev_residual_le` makes the
  residual rate explicit using the Chebyshev interval bound, and
  `SaadSparse.Chapter12.norm_residual_minRes_le_chebyshev` compares it to Krylov minimal
  residuals.
* **(12.10)–(12.14)** (generalizations). `SaadSparse.Chapter12.bilinFormOfWeight` admits
  arbitrary integrable weights. The kernel optimality and orthogonality theorems use an abstract
  bilinear form with explicit hypotheses. `SaadSparse.Chapter12.equation_12_13` gives the
  polynomial identity $R_k=1-Xs_{k-1}$ and implements the quotient with `Polynomial.divX`, so
  evaluation at zero is defined.
* **(12.16)** (scope). `SaadSparse.Chapter12.equation_12_16` is the finite coefficient formula
  for all real parameters. The assertion that it minimizes the weighted norm for the Jacobi
  weight remains outside the statement.

## Not formalized

* **Section 12.3.4** (the nonsymmetric case). Its results are Lemma 6.26 and Theorem 6.27, and the
  case of a polygon is a numerical procedure with no theorem.
* **Example 12.2.** It is a table of measured iteration counts and timings and carries no
  mathematical claim.
* **The identification of (12.16) with the least-squares residual polynomial.** It needs Jacobi
  polynomials and their orthogonality, which Mathlib does not have.
* **The case $\alpha = 0$ of the decay of the least-squares residual.** The decay is only $1/k$ with
  a constant given by Gamma functions of the Jacobi weights, and Mathlib has no Jacobi polynomials.
-/

open Matrix Polynomial
open scoped SaadSparse

namespace SaadSparse.Chapter12

variable {n : ℕ}

/-- Over $\mathbb{R}$, mapping a polynomial by `algebraMap ℝ ℝ` does not change it. -/
private theorem map_algebraMap_real (p : Polynomial ℝ) : p.map (algebraMap ℝ ℝ) = p := by
  simp

/-! ### Section 12.3.1: Neumann polynomial preconditioners -/

/-- **Equation (12.3)** of [saad2003iterative]. Let $A, D \in \mathbb{R}^{n \times n}$, let
$\omega \neq 0$, let $s \in \mathbb{N}$, and let $N = I - \omega D^{-1} A$. Then the truncated
Neumann preconditioner $M^{-1} = (I + N + \dots + N^s) D^{-1}$ satisfies
$$M^{-1} A = \omega^{-1} \bigl(I - N^{s+1}\bigr).$$
So a Neumann polynomial preconditioner differs from the identity by the $(s+1)$-st power of the
iteration matrix of the underlying relaxation: it is $s + 1$ steps of that relaxation in one
preconditioner.

The sum $I + N + \dots + N^s$ is `Preconditioner.neumannPolyOf N s`. The inverse $D^{-1}$ is
Mathlib's matrix inverse, and the identity holds even when $D$ is singular.

**Scope.** The theorem is the finite product identity in the display after (12.3). That
equation introduces an approximate inverse, while the theorem needs only $\omega\ne0$ and uses
the total matrix inverse for $D$. -/
theorem equation_12_3 {ω : ℝ} (hω : ω ≠ 0) (A D : Matrix (Fin n) (Fin n) ℝ) (s : ℕ) :
    Preconditioner.neumannPolyOf (1 - ω • (D⁻¹ * A)) s * D⁻¹ * A =
      ω⁻¹ • (1 - (1 - ω • (D⁻¹ * A)) ^ (s + 1)) := by
  have h := Preconditioner.neumannPoly_mul_eq (ω • D⁻¹) A s
  rw [Matrix.smul_mul] at h
  rw [← h, mul_smul_comm, smul_smul, inv_mul_cancel₀ hω, one_smul, Matrix.mul_assoc]

/-- **Section 12.3.1** of [saad2003iterative], the closing remark. Let
$A, D \in \mathbb{R}^{n \times n}$ be symmetric positive definite and let $s$ be a real
polynomial. Then the preconditioned matrix $s(D^{-1} A) D^{-1} A$ is self-adjoint for the
$D$-inner product $(x, y)_D = (Dx, y)$, although it is not symmetric in general. So the
conjugate gradient method can still be used with it.

The book leaves the verification as Exercise 12.1. The $D$-inner product is that of
`WithEnergy`, and the statement conjugates the operator by `WithEnergy.equiv`.

**Reading.** Any real polynomial and any SPD D, rather than only the Neumann polynomial for a
diagonal or block diagonal D.
-/
theorem neumann_isSymmetric_withEnergy {A D : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (hD : D.PosDef) (s : Polynomial ℝ) :
    ((WithEnergy.equiv (Matrix.toEuclideanLin D)
        ((Matrix.posDef_iff_isSymmetricCoercive D).1 hD)).conj
      (aeval (Matrix.toEuclideanLin (D⁻¹ * A)) s *
        Matrix.toEuclideanLin (D⁻¹ * A))).IsSymmetric := by
  have hDc := (Matrix.posDef_iff_isSymmetricCoercive D).1 hD
  have hDinv : D * D⁻¹ = 1 :=
    Matrix.mul_nonsing_inv D (isUnit_iff_ne_zero.2 (Matrix.PosDef.det_pos hD).ne')
  have hcomp : Matrix.toEuclideanLin D ∘ₗ Matrix.toEuclideanLin (D⁻¹ * A)
      = Matrix.toEuclideanLin A := by
    rw [← Matrix.toEuclideanLin_mul, ← Matrix.mul_assoc, hDinv, Matrix.one_mul]
  have hB := Preconditioner.energyInner_comm_of_comp_eq hDc.isSymmetric
    (Matrix.isSymmetric_toEuclideanLin_iff.2 (Matrix.PosDef.isHermitian hA)) hcomp
  have h := Preconditioner.isSymmetric_withEnergy_aeval_mul hDc hB s
  rwa [map_algebraMap_real] at h

/-! ### Section 12.3.2: the optimality criterion (12.4)–(12.5) -/

/-- **Equation (12.5)** of [saad2003iterative], the criterion that selects the polynomial. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric with $\alpha \|x\|^2 \le (Ax, x) \le \beta \|x\|^2$
for all $x$, so that $[\alpha, \beta]$ contains the spectrum of $A$, and let $s$ be a real
polynomial. Then for every $x \in \mathbb{R}^n$
$$\|x - s(A) A x\| \le \max_{\lambda \in [\alpha, \beta]} |1 - \lambda s(\lambda)| \, \|x\|.$$
So the design problem of a polynomial preconditioner is to make this maximum small.

**Scope.** Equation (12.5) gives the minimization objective. The theorem bounds the pointwise
operator error by that objective for every polynomial under the symmetric interval hypothesis. -/
theorem equation_12_5 {A : Matrix (Fin n) (Fin n) ℝ} {α β : ℝ}
    (hA : (Matrix.toEuclideanLin A).IsSymmetricBoundedBy α β) (s : Polynomial ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖x - aeval (Matrix.toEuclideanLin A) s (A ⬝ x)‖ ≤
      sSup ((fun t => |1 - t * s.eval t|) '' Set.Icc α β) * ‖x‖ := by
  have h := Preconditioner.norm_sub_aeval_mul_apply_le hA s x
  rwa [map_algebraMap_real] at h

/-- **Equations (12.4)–(12.5)** of [saad2003iterative], the min–max problem on the interval
$E = [\alpha, \beta]$ of (12.5), with $\gamma = 0$. Let $0 < \alpha < \beta$, let
$k \in \mathbb{N}$, and let $s$ be a real polynomial of degree at most $k$. Then
$$\frac{1}{C_{k+1}\bigl((\beta + \alpha)/(\beta - \alpha)\bigr)} \le \max_{\lambda \in [\alpha,
  \beta]} |1 - \lambda s(\lambda)|.$$

The residual polynomials $1 - \lambda s(\lambda)$ are exactly the polynomials of degree at most
$k + 1$ with the value $1$ at $0$. The shifted Chebyshev polynomial of Theorem 6.25 attains the
bound; the formal statement is the lower bound.

**Scope.** The printed (12.4) uses the discrete spectrum. This theorem concerns the interval
replacement (12.5) and gives its lower bound. It does not state attainment by a particular
iteration polynomial. -/
theorem equation_12_4 {α β : ℝ} (hα : 0 < α) (hαβ : α < β) {k : ℕ} {s : Polynomial ℝ}
    (hs : s.degree ≤ (k : WithBot ℕ)) :
    1 / eval ((β + α) / (β - α)) (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)) ≤
      sSup ((fun t => |1 - t * s.eval t|) '' Set.Icc α β) := by
  have hdeg : ((1 : Polynomial ℝ) - X * s).degree ≤ ((k + 1 : ℕ) : WithBot ℕ) := by
    refine (degree_sub_le _ _).trans (max_le (degree_one_le.trans ?_) ?_)
    · exact_mod_cast Nat.zero_le (k + 1)
    · refine (degree_mul_le _ _).trans ?_
      refine le_trans (add_le_add degree_X_le hs) ?_
      exact_mod_cast le_of_eq (by ring)
  have h0 : eval 0 ((1 : Polynomial ℝ) - X * s) = 1 := by simp
  have h := Chebyshev.one_div_eval_T_le_sSup_abs_eval_of_eval_zero (k + 1) hα hαβ _ hdeg h0
  have himg : (fun t => |eval t ((1 : Polynomial ℝ) - X * s)|) = fun t => |1 - t * s.eval t| := by
    funext t
    simp
  rwa [himg] at h

/-! ### Section 12.3.2: Chebyshev acceleration, Algorithm 12.1 -/

/-- **Section 12.3.2** of [saad2003iterative], the residual polynomial. Let $\alpha < \beta$, let
$\theta = (\beta + \alpha)/2$ and $\delta = (\beta - \alpha)/2$, and let $k \in \mathbb{N}$.
Then the residual polynomial
$$T_k(t) = \frac{C_k((\theta - t)/\delta)}{C_k(\theta/\delta)}$$
is the shifted Chebyshev polynomial `Polynomial.Chebyshev.shifted k α β 0` of Section 6.11: the
two agree at every $t \in \mathbb{R}$.

Through this identification, Chebyshev acceleration inherits the min–max optimality proved for
the shifted Chebyshev polynomial. -/
theorem T_k_eq_shifted {α β : ℝ} (hαβ : α < β) (k : ℕ) (t : ℝ) :
    eval t (Chebyshev.shifted k α β 0) =
      eval (((β + α) / 2 - t) / ((β - α) / 2)) (Chebyshev.T ℝ (k : ℤ)) /
        eval ((β + α) / 2 / ((β - α) / 2)) (Chebyshev.T ℝ (k : ℤ)) := by
  have hd : β - α ≠ 0 := sub_ne_zero_of_ne hαβ.ne'
  have e1 : ((β + α) / 2 - t) / ((β - α) / 2) = (β + α) / (β - α) - 2 / (β - α) * t := by
    field_simp
  have e2 : (β + α) / 2 / ((β - α) / 2) = (β + α) / (β - α) := by
    field_simp
  rw [Chebyshev.shifted, e1, e2]
  simp only [eval_mul, eval_C, eval_comp, eval_sub, eval_X, mul_zero, sub_zero]
  ring

/-- **Algorithm 12.1** of [saad2003iterative], Chebyshev acceleration. For
$A \in \mathbb{R}^{n \times n}$, $b, x_0 \in \mathbb{R}^n$, an interval $[\alpha, \beta]$ that
contains the spectrum of $A$, and $k \in \mathbb{N}$, this is the state after $k$ steps: the
iterate $x_k$, the residual $r_k$, the direction $d_k$ and the scalar $\rho_k$. With
$\theta = (\beta + \alpha)/2$, $\delta = (\beta - \alpha)/2$ and $\sigma_1 = \theta/\delta$, the
algorithm starts with $r_0 = b - A x_0$, $d_0 = r_0 / \theta$ and $\rho_0 = \delta/\theta$, and
each step computes
$$x_{k+1} = x_k + d_k, \quad r_{k+1} = r_k - A d_k, \quad \rho_{k+1} = (2 \sigma_1 -
  \rho_k)^{-1}, \quad d_{k+1} = \rho_k \rho_{k+1} d_k + \frac{2 \rho_{k+1}}{\delta} r_{k+1}.$$
One step costs one matrix-vector product and no inner product, which is the practical point of
the method.

The definition is `Preconditioner.Chebyshev.iterate` with $\theta = (\beta + \alpha)/2$ and
$\delta = (\beta - \alpha)/2$. It is defined for all $\alpha, \beta$; the results below assume
$0 < \alpha < \beta$ where they need it.

**Reading.** The state uses the startup $\rho_0=1/\sigma_1$ of Algorithm 12.1 and a prescribed
number of steps. The discussion before the algorithm also gives $\rho_0=1/(2\sigma_1)$ when
starting the polynomial recurrence with $T_{-1}=\rho_{-1}=0$. -/
noncomputable abbrev chebyshevIterate (A : Matrix (Fin n) (Fin n) ℝ)
    (b x₀ : EuclideanSpace ℝ (Fin n)) (α β : ℝ) (k : ℕ) :
    Preconditioner.Chebyshev.State (EuclideanSpace ℝ (Fin n)) :=
  Preconditioner.Chebyshev.iterate (Matrix.toEuclideanLin A) b x₀ ((β + α) / 2) ((β - α) / 2) k

/-- **Section 12.3.2** of [saad2003iterative], the display before (12.6). For
$\theta, \delta \in \mathbb{R}$ and $k \in \mathbb{N}$, the Chebyshev values
$\sigma_k = C_k(\theta/\delta)$ satisfy the three-term recurrence of the Chebyshev polynomials,
$$\sigma_{k+2} = 2 \frac{\theta}{\delta} \sigma_{k+1} - \sigma_k.$$

The display has no number. The equation (12.7) is the recurrence of $\rho_k$,
`SaadSparse.Chapter12.equation_12_6`. The values $\sigma_k$ are
`Preconditioner.Chebyshev.sigma`.

**Reading.** Source (12.7) is the rho recurrence, not this sigma formula.
-/
theorem equation_12_7 (θ δ : ℝ) (k : ℕ) :
    Preconditioner.Chebyshev.sigma θ δ (k + 2) =
      2 * (θ / δ) * Preconditioner.Chebyshev.sigma θ δ (k + 1) -
        Preconditioner.Chebyshev.sigma θ δ k :=
  Preconditioner.Chebyshev.sigma_add_two θ δ k

/-- **Equation (12.7)** of [saad2003iterative]. Let $0 < \delta < \theta$ and $k \in \mathbb{N}$.
The scalar $\rho_k = \sigma_k / \sigma_{k+1}$ of (12.6), which the algorithm carries, satisfies
$$\rho_{k+1} = (2 \sigma_1 - \rho_k)^{-1}, \qquad \sigma_1 = \theta/\delta.$$
This recurrence removes the Chebyshev values from the implementation.

The equation (12.6) is the definition of $\rho_k$, `Preconditioner.Chebyshev.rho`; the
recurrence of the values $\sigma_k$ is `SaadSparse.Chapter12.equation_12_7`.

**Reading.** Uses rho recurrence with explicit positive interval hypotheses, while source (12.6) is
the ratio definition.
-/
theorem equation_12_6 {θ δ : ℝ} (hδ : 0 < δ) (hθδ : δ < θ) (k : ℕ) :
    Preconditioner.Chebyshev.rho θ δ (k + 1) =
      (2 * (θ / δ) - Preconditioner.Chebyshev.rho θ δ k)⁻¹ :=
  Preconditioner.Chebyshev.rho_succ hδ hθδ k

/-- **Equation (12.8)** of [saad2003iterative]. Let $0 < \delta < \theta$ and $k \in \mathbb{N}$.
The residual polynomials $T_k(t) = C_k((\theta - t)/\delta) / C_k(\theta/\delta)$ satisfy the
three-term recurrence
$$T_{k+2}(t) = \rho_{k+1} \Bigl(2 \Bigl(\sigma_1 - \frac{t}{\delta}\Bigr) T_{k+1}(t) - \rho_k
  T_k(t)\Bigr).$$
It is the Chebyshev recurrence divided by $\sigma_{k+2}$, and it makes the vector recurrence of
Algorithm 12.1 produce the Chebyshev residuals.

The polynomials $T_k$ are `Preconditioner.Chebyshev.resPoly`, and
$\sigma_1 - t/\delta = (\theta - t)/\delta$ is `Preconditioner.Chebyshev.shift`. -/
theorem equation_12_8 {θ δ : ℝ} (hδ : 0 < δ) (hθδ : δ < θ) (k : ℕ) :
    Preconditioner.Chebyshev.resPoly θ δ (k + 2) =
      C (2 * Preconditioner.Chebyshev.rho θ δ (k + 1)) *
          (Preconditioner.Chebyshev.shift θ δ * Preconditioner.Chebyshev.resPoly θ δ (k + 1)) -
        C (Preconditioner.Chebyshev.rho θ δ k * Preconditioner.Chebyshev.rho θ δ (k + 1)) *
          Preconditioner.Chebyshev.resPoly θ δ k :=
  Preconditioner.Chebyshev.resPoly_add_two hδ hθδ k

/-- **Equation (12.9)** of [saad2003iterative], the direction recurrence of Algorithm 12.1. For
$A \in \mathbb{R}^{n \times n}$, $b, x_0 \in \mathbb{R}^n$, $\alpha, \beta \in \mathbb{R}$ and
$k \in \mathbb{N}$,
$$d_{k+1} = \rho_k \rho_{k+1} d_k + \frac{2 \rho_{k+1}}{\delta} r_{k+1}, \qquad \delta =
  (\beta - \alpha)/2.$$

**Source location.** Printed (12.9) is the scalar difference-quotient identity for the residual
polynomials. This theorem states the vector direction update derived from it in Algorithm 12.1.

**Reading.** States recurrence for d, not the printed scalar difference quotient.
-/
theorem equation_12_9 (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : EuclideanSpace ℝ (Fin n))
    (α β : ℝ) (k : ℕ) :
    (chebyshevIterate A b x₀ α β (k + 1)).d =
      ((chebyshevIterate A b x₀ α β k).ρ * (chebyshevIterate A b x₀ α β (k + 1)).ρ : ℝ) •
          (chebyshevIterate A b x₀ α β k).d +
        (2 * (chebyshevIterate A b x₀ α β (k + 1)).ρ / ((β - α) / 2) : ℝ) •
          (chebyshevIterate A b x₀ α β (k + 1)).r := by
  simp only [chebyshevIterate, Preconditioner.Chebyshev.iterate_succ]
  exact Preconditioner.Chebyshev.step_d _

/-- **Section 12.3.2** of [saad2003iterative], the residual of Algorithm 12.1. Let
$A \in \mathbb{R}^{n \times n}$, let $b, x_0 \in \mathbb{R}^n$, let $0 < \alpha < \beta$ and let
$k \in \mathbb{N}$. Then the residual of Chebyshev acceleration is
$$r_k = T_k(A) r_0, \qquad r_0 = b - A x_0,$$
where $T_k$ is the shifted Chebyshev polynomial `Polynomial.Chebyshev.shifted k α β 0` of the
interval $[\alpha, \beta]$.

**Reading.** Verifies actual initialized iteration under positive endpoints for arbitrary real
matrix, no symmetry assumption needed.
-/
theorem chebyshev_residual_eq {A : Matrix (Fin n) (Fin n) ℝ} {b x₀ : EuclideanSpace ℝ (Fin n)}
    {α β : ℝ} (hα : 0 < α) (hαβ : α < β) (k : ℕ) :
    (chebyshevIterate A b x₀ α β k).r =
      aeval (Matrix.toEuclideanLin A) (Chebyshev.shifted k α β 0) (b - (A ⬝ x₀)) := by
  have h := Preconditioner.Chebyshev.residual_iterate_eq
    (A := Matrix.toEuclideanLin A) (b := b) (x₀ := x₀) hα hαβ k
  rwa [map_algebraMap_real] at h

/-- **Section 12.3.2** of [saad2003iterative], the convergence rate of Chebyshev acceleration. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric with $\alpha \|x\|^2 \le (Ax, x) \le \beta \|x\|^2$
for all $x$, where $0 < \alpha < \beta$, and let $b, x_0 \in \mathbb{R}^n$. Then for every
$k \in \mathbb{N}$
$$\|r_k\| \le 2 \left(\frac{\sqrt{\kappa} - 1}{\sqrt{\kappa} + 1}\right)^k \|b - A x_0\|, \qquad
  \kappa = \beta/\alpha,$$
where $\kappa$ is the condition number of the enclosing interval.

**Reading.** Supplies explicit residual rate from positive real symmetric spectral bounds.
-/
theorem norm_chebyshev_residual_le {A : Matrix (Fin n) (Fin n) ℝ}
    {b x₀ : EuclideanSpace ℝ (Fin n)} {α β : ℝ}
    (hA : (Matrix.toEuclideanLin A).IsSymmetricBoundedBy α β) (hα : 0 < α) (hαβ : α < β) (k : ℕ) :
    ‖(chebyshevIterate A b x₀ α β k).r‖ ≤
      2 * ((Real.sqrt (β / α) - 1) / (Real.sqrt (β / α) + 1)) ^ k * ‖b - (A ⬝ x₀)‖ :=
  Preconditioner.Chebyshev.norm_residual_iterate_le_pow hA hα hαβ k

/-- **Section 12.3.2** of [saad2003iterative], Chebyshev acceleration is not optimal among Krylov
methods. Let $A \in \mathbb{R}^{n \times n}$, let $b, x_0 \in \mathbb{R}^n$, let
$0 < \alpha < \beta$, and let $y$ be a minimal-residual iterate of step $k$:
$y \in x_0 + \mathcal{K}_k(A, r_0)$ minimizes $\|b - Ay\|$ there. Then
$$\|b - Ay\| \le \|r_k\|,$$
where $r_k$ is the residual of $k$ steps of Chebyshev acceleration for $[\alpha, \beta]$.

The Chebyshev residual polynomial is one competitor in the minimization. This comparison makes
CG or GMRES preferable wherever inner products are affordable, and Chebyshev acceleration
preferable where they are not. A minimal-residual iterate is `Krylov.IsMinResidualIterate`.

**Reading.** Combines iteration polynomial with Krylov minimal-residual optimality as an additional
consequence.
-/
theorem norm_residual_minRes_le_chebyshev {A : Matrix (Fin n) (Fin n) ℝ}
    {b x₀ y : EuclideanSpace ℝ (Fin n)} {α β : ℝ} (hα : 0 < α) (hαβ : α < β) {k : ℕ}
    (hy : Krylov.IsMinResidualIterate (Matrix.toEuclideanLin A) b x₀ k y) :
    ‖b - (A ⬝ y)‖ ≤ ‖(chebyshevIterate A b x₀ α β k).r‖ :=
  Preconditioner.Chebyshev.norm_residual_minRes_le_norm_residual_iterate hα hαβ hy

/-! ### Section 12.3.3: least-squares polynomials -/

section LeastSquares

open MeasureTheory

variable {α β : ℝ} {w : ℝ → ℝ}

/-- **Equation (12.10)** of [saad2003iterative], the weighted inner product. Let
$\alpha, \beta \in \mathbb{R}$ and let $w$ be integrable over the interval between $\alpha$ and
$\beta$. The weighted form on the real polynomials is the bilinear form
$$\langle p, q \rangle_w = \int_\alpha^\beta p(\lambda) q(\lambda) w(\lambda) \, d\lambda.$$

The form is a `LinearMap.BilinForm`, the shape of the statements of
`Numlib.RingTheory.Polynomial.KernelPolynomial`. Bilinearity needs only that $w$ is integrable
over the interval. The nonnegativity of $w$ is needed only where the form must be positive
semidefinite (`SaadSparse.Chapter12.bilinFormOfWeight_le`).

**Generalization.** The integral defines a symmetric bilinear form for any interval-integrable
weight. The source uses a nonnegative weight on the polynomial space of degree at most $k$. -/
noncomputable def bilinFormOfWeight (α β : ℝ) (w : ℝ → ℝ)
    (hw : IntervalIntegrable w volume α β) : LinearMap.BilinForm ℝ (Polynomial ℝ) :=
  LinearMap.mk₂ ℝ (fun p q => ∫ t in α..β, p.eval t * q.eval t * w t)
    (fun p₁ p₂ q => by
      have h1 : IntervalIntegrable (fun t => p₁.eval t * q.eval t * w t) volume α β :=
        hw.continuousOn_mul (p₁.continuous.mul q.continuous).continuousOn
      have h2 : IntervalIntegrable (fun t => p₂.eval t * q.eval t * w t) volume α β :=
        hw.continuousOn_mul (p₂.continuous.mul q.continuous).continuousOn
      rw [← intervalIntegral.integral_add h1 h2]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [eval_add]
      ring)
    (fun c p q => by
      rw [smul_eq_mul, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [eval_smul, smul_eq_mul]
      ring)
    (fun p q₁ q₂ => by
      have h1 : IntervalIntegrable (fun t => p.eval t * q₁.eval t * w t) volume α β :=
        hw.continuousOn_mul (p.continuous.mul q₁.continuous).continuousOn
      have h2 : IntervalIntegrable (fun t => p.eval t * q₂.eval t * w t) volume α β :=
        hw.continuousOn_mul (p.continuous.mul q₂.continuous).continuousOn
      rw [← intervalIntegral.integral_add h1 h2]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [eval_add]
      ring)
    (fun c p q => by
      rw [smul_eq_mul, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [eval_smul, smul_eq_mul]
      ring)

/-- The weighted form of (12.10) evaluated: $\langle p, q \rangle_w = \int_\alpha^\beta p(\lambda)
q(\lambda) w(\lambda) \, d\lambda$. -/
@[simp]
theorem bilinFormOfWeight_apply (hw : IntervalIntegrable w volume α β) (p q : Polynomial ℝ) :
    bilinFormOfWeight α β w hw p q = ∫ t in α..β, p.eval t * q.eval t * w t := rfl

/-- **Equation (12.10)** of [saad2003iterative]. The weighted form $\langle p, q \rangle_w$ is
symmetric.

**Generalization.** Symmetry of integral form extends to signed integrable weights.
-/
theorem bilinFormOfWeight_isSymm (hw : IntervalIntegrable w volume α β) :
    (bilinFormOfWeight α β w hw).IsSymm := by
  refine ⟨fun p q => ?_⟩
  simp only [bilinFormOfWeight_apply]
  refine intervalIntegral.integral_congr fun t _ => ?_
  ring

/-- **Section 12.3.3** of [saad2003iterative], the bound by the maximum on the interval. Let
$\alpha \le \beta$ and let $w$ be integrable over $[\alpha, \beta]$ and nonnegative on
$[\alpha, \beta]$. Then for every real polynomial $p$
$$\langle p, p \rangle_w \le \Bigl(\max_{\lambda \in [\alpha, \beta]} |p(\lambda)|\Bigr)^2
  \langle 1, 1 \rangle_w.$$
This is the sense in which the form is supported on $[\alpha, \beta]$ that the geometric bound
of Section 12.3.3 needs.

**Reading.** Abstract sup-norm comparison in squared form for all polynomials and explicit
nonnegative integrable weight.
-/
theorem bilinFormOfWeight_le (hw : IntervalIntegrable w volume α β) (hαβ : α ≤ β)
    (hw0 : ∀ t ∈ Set.Icc α β, 0 ≤ w t) (p : Polynomial ℝ) :
    bilinFormOfWeight α β w hw p p ≤
      sSup ((fun t => |p.eval t|) '' Set.Icc α β) ^ 2 * bilinFormOfWeight α β w hw 1 1 := by
  have hbdd : BddAbove ((fun t => |p.eval t|) '' Set.Icc α β) :=
    (isCompact_Icc.image p.continuous.abs).bddAbove
  have hi1 : IntervalIntegrable (fun t => p.eval t * p.eval t * w t) volume α β :=
    hw.continuousOn_mul ((p.continuous.mul p.continuous).continuousOn)
  have hi2 : IntervalIntegrable
      (fun t => sSup ((fun t => |p.eval t|) '' Set.Icc α β) ^ 2 * w t) volume α β :=
    hw.const_mul _
  have hpt : ∀ t ∈ Set.Icc α β,
      p.eval t * p.eval t * w t ≤ sSup ((fun t => |p.eval t|) '' Set.Icc α β) ^ 2 * w t := by
    intro t ht
    have hple : |p.eval t| ≤ sSup ((fun t => |p.eval t|) '' Set.Icc α β) :=
      le_csSup hbdd ⟨t, ht, rfl⟩
    have hsq : p.eval t * p.eval t ≤ sSup ((fun t => |p.eval t|) '' Set.Icc α β) ^ 2 := by
      rw [← sq, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hple 2
    exact mul_le_mul_of_nonneg_right hsq (hw0 t ht)
  refine (intervalIntegral.integral_mono_on hαβ hi1 hi2 hpt).trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul, bilinFormOfWeight_apply]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp

end LeastSquares

/-- **Section 12.3.3** of [saad2003iterative], the least-squares residual polynomial. Let $B$ be a
bilinear form on the real polynomials and let $k \in \mathbb{N}$. A polynomial $R$ is a
**least-squares residual polynomial of degree $k$** for $B$ if it is admissible, that is,
$\deg R \le k$ and $R(0) = 1$, and
$$B(R, R) \le B(p, p) \quad \text{for every admissible } p.$$

An admissible polynomial is one of the form $R(\lambda) = 1 - \lambda s(\lambda)$ with
$\deg s \le k - 1$, and the book's $s_{k-1}$ is $(1 - R)/\lambda$. For the weighted form of
(12.10), $B(R, R) = \|R\|_w^2$.

**Reading.** Treats arbitrary bilinear minimization and normalized residual degree at most k.
-/
def IsLeastSquaresResidual (B : LinearMap.BilinForm ℝ (Polynomial ℝ)) (k : ℕ)
    (R : Polynomial ℝ) : Prop :=
  R.degree ≤ (k : WithBot ℕ) ∧ R.eval 0 = 1 ∧
    ∀ p : Polynomial ℝ, p.degree ≤ (k : WithBot ℕ) → p.eval 0 = 1 →
      B R R ≤ B p p

/-- **Equation (12.12)** of [saad2003iterative], the kernel polynomial formula. Let $B$ be a
bilinear form on the real polynomials, and let $q_0, q_1, \dots$ be orthonormal for $B$,
$B(q_i, q_j) = \delta_{ij}$, with $\deg q_i = i$. Let $k \in \mathbb{N}$ with
$\sum_{i \le k} q_i(0)^2 \neq 0$. Then
$$R_k(\lambda) = \frac{\sum_{i \le k} q_i(0) q_i(\lambda)}{\sum_{i \le k} q_i(0)^2}$$
is a least-squares residual polynomial of degree $k$ for $B$.

The hypothesis on the sum says that some $q_i$ with $i \le k$ does not vanish at $0$. The
polynomial $R_k$ is `Polynomial.kernelPolynomial q 0 k`.

**Generalization.** Extends kernel optimality to abstract bilinear form with degree-indexed
orthonormal polynomials and explicit nonzero kernel denominator.
-/
theorem equation_12_12 {B : LinearMap.BilinForm ℝ (Polynomial ℝ)} {q : ℕ → Polynomial ℝ}
    (horth : ∀ i j, B (q i) (q j) = if i = j then 1 else 0) (hdeg : ∀ i, (q i).degree = i)
    {k : ℕ} (hS : ∑ i ∈ Finset.range (k + 1), (q i).eval 0 ^ 2 ≠ 0) :
    IsLeastSquaresResidual B k (kernelPolynomial q 0 k) := by
  refine ⟨kernelPolynomial_degree_le hdeg 0 k, kernelPolynomial_eval hS, fun p hp hp0 => ?_⟩
  rw [bilinForm_kernelPolynomial_self horth hS]
  exact (bilinForm_kernelPolynomial_le horth hdeg hS).2 ⟨p, hp, hp0, rfl⟩

/-- **Equations (12.13)–(12.14)** of [saad2003iterative], the least-squares polynomial. Let
$q_0, q_1, \dots$ be real polynomials, let $k \in \mathbb{N}$ with
$\sum_{i \le k} q_i(0)^2 \neq 0$, and let $t_i(\lambda) = (q_i(0) - q_i(\lambda))/\lambda$. Then
the kernel polynomial $R_k$ of (12.12) is
$$R_k(\lambda) = 1 - \lambda s_{k-1}(\lambda), \qquad s_{k-1} = \frac{\sum_{i \le k} q_i(0)
  t_i}{\sum_{i \le k} q_i(0)^2}.$$

The polynomial $t_i$ is `-(q i).divX`.

**Reading.** States polynomial identity for R=1−λs and interprets the quotient via divX even at
zero.
-/
theorem equation_12_13 (q : ℕ → Polynomial ℝ) (k : ℕ)
    (hS : ∑ i ∈ Finset.range (k + 1), (q i).eval 0 ^ 2 ≠ 0) :
    kernelPolynomial q 0 k =
      1 - X * ((∑ i ∈ Finset.range (k + 1), (q i).eval 0 ^ 2)⁻¹ •
        ∑ i ∈ Finset.range (k + 1), (q i).eval 0 • (-(q i).divX)) := by
  refine Polynomial.funext fun t => ?_
  have hdiv : ∀ i, t * (q i).divX.eval t + (q i).eval 0 = (q i).eval t := fun i => by
    have h := congrArg (Polynomial.eval t) (X_mul_divX_add (q i))
    simpa [coeff_zero_eq_eval_zero] using h
  have key : ∑ i ∈ Finset.range (k + 1), (q i).eval 0 * -(t * (q i).divX.eval t) =
      ∑ i ∈ Finset.range (k + 1), (q i).eval 0 ^ 2 -
        ∑ i ∈ Finset.range (k + 1), (q i).eval 0 * (q i).eval t := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ =>
      by linear_combination (-(q i).eval 0) * hdiv i
  have hrhs : ∑ i ∈ Finset.range (k + 1),
        t * ((∑ j ∈ Finset.range (k + 1), (q j).eval 0 ^ 2)⁻¹ *
          ((q i).eval 0 * -(q i).divX.eval t)) =
      (∑ j ∈ Finset.range (k + 1), (q j).eval 0 ^ 2)⁻¹ *
        ∑ i ∈ Finset.range (k + 1), (q i).eval 0 * -(t * (q i).divX.eval t) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [kernelPolynomial, eval_smul, eval_finsetSum, eval_sub, eval_one, eval_mul, eval_X,
    eval_neg, smul_eq_mul, Finset.mul_sum]
  rw [hrhs, key, mul_sub, inv_mul_cancel₀ hS, sub_sub_cancel, Finset.mul_sum]

/-- **Section 12.3.3** of [saad2003iterative], the orthogonality of the residual polynomials for the
weight $\lambda w(\lambda)$. Let $B$ be a symmetric bilinear form on the real polynomials, and
let $q_0, q_1, \dots$ be orthonormal for $B$ with $\deg q_i = i$. Let $k \in \mathbb{N}$ with
$\sum_{i \le k} q_i(0)^2 \neq 0$, and let $R_k$ be the kernel polynomial of (12.12). Then for
every polynomial $Q$ of degree less than $k$
$$B(\lambda Q, R_k) = 0.$$

These are the normal equations $\langle 1 - \lambda s_{k-1}(\lambda), \lambda Q(\lambda)
\rangle_w = 0$: the admissible directions are exactly those that keep both the degree bound and
the value $1$ at the origin. This is the second way of the book to the least-squares polynomial.

**Reading.** Tests against all lower-degree polynomials using abstract bilinear form and explicit
hypotheses.
-/
theorem leastSquaresResidual_orthogonal {B : LinearMap.BilinForm ℝ (Polynomial ℝ)}
    {q : ℕ → Polynomial ℝ} (hsymm : B.IsSymm)
    (horth : ∀ i j, B (q i) (q j) = if i = j then 1 else 0) (hdeg : ∀ i, (q i).degree = i)
    {k : ℕ} (hS : ∑ i ∈ Finset.range (k + 1), (q i).eval 0 ^ 2 ≠ 0)
    {p : Polynomial ℝ} (hp : p.degree < (k : WithBot ℕ)) :
    B (X * p) (kernelPolynomial q 0 k) = 0 :=
  bilinForm_kernelPolynomial_mul_X hsymm horth hdeg hS hp

/-- **Section 12.3.3** of [saad2003iterative], the theoretical consideration at the end. Let $B$ be
a bilinear form on the real polynomials, and let $q_0, q_1, \dots$ be orthonormal for $B$ with
$\deg q_i = i$. Let $0 < \alpha < \beta$, and assume that $B(p, p) \le (\max_{[\alpha, \beta]}
|p|)^2 B(1, 1)$ for every polynomial $p$. Let $k \in \mathbb{N}$ with
$\sum_{i \le k} q_i(0)^2 \neq 0$. Then the kernel polynomial $R_k$ of (12.12) satisfies
$$B(R_k, R_k) \le \left(\frac{\beta - \alpha}{\beta + \alpha}\right)^{2k} B(1, 1).$$
So the least-squares residual polynomial decays geometrically, because $(1 - \lambda/\theta)^k$
with $\theta = (\alpha + \beta)/2$ is an admissible competitor.

The hypothesis on $B$ is what `SaadSparse.Chapter12.bilinFormOfWeight_le` gives for a
nonnegative weight on $[\alpha, \beta]$. The case $\alpha = 0$, where the decay is only $1/k$
and the constant is a ratio of Gamma functions of the Jacobi weights, is not stated: Mathlib has
no Jacobi polynomials.

**Reading.** Geometric rate in squared form for an abstract bilinear form satisfying a sup-norm
comparison.
-/
theorem norm_leastSquaresResidual_le {B : LinearMap.BilinForm ℝ (Polynomial ℝ)}
    {q : ℕ → Polynomial ℝ} (horth : ∀ i j, B (q i) (q j) = if i = j then 1 else 0)
    (hdeg : ∀ i, (q i).degree = i) {α β : ℝ} (hα : 0 < α) (hαβ : α < β)
    (hB : ∀ p : Polynomial ℝ, B p p ≤ sSup ((fun t => |p.eval t|) '' Set.Icc α β) ^ 2 * B 1 1)
    {k : ℕ} (hS : ∑ i ∈ Finset.range (k + 1), (q i).eval 0 ^ 2 ≠ 0) :
    B (kernelPolynomial q 0 k) (kernelPolynomial q 0 k) ≤
      ((β - α) / (β + α)) ^ (2 * k) * B 1 1 :=
  bilinForm_kernelPolynomial_le_pow horth hdeg hα hαβ hB hS

/-! ### Section 12.3.3: the Jacobi weight (12.15)–(12.16) and Example 12.1 -/

/-- **Equation (12.16)** of [saad2003iterative], the coefficients. For $\mu, \nu \in \mathbb{R}$ and
$j, k \in \mathbb{N}$,
$$\kappa_j^{(k)} = \binom{k}{j} \prod_{i < j} \frac{k - i + \nu}{i + 1 + \mu}.$$

The book uses them for the Jacobi weight (12.15) with exponents $\mu > 0$ and $\nu \ge -1/2$;
the definition accepts all real $\mu$ and $\nu$.

**Generalization.** Coefficient formula extends to all real parameters, including where a
denominator vanishes.
-/
noncomputable def kappa_12_16 (mu nu : ℝ) (k j : ℕ) : ℝ :=
  (k.choose j : ℝ) * ∏ i ∈ Finset.range j, ((k : ℝ) - i + nu) / ((i : ℝ) + 1 + mu)

/-- **Equation (12.16)** of [saad2003iterative], the closed form of the least-squares residual
polynomial for the Jacobi weight (12.15) on $[0, 1]$. For $\mu, \nu \in \mathbb{R}$,
$k \in \mathbb{N}$ and $\lambda \in \mathbb{R}$,
$$R_k(\lambda) = \sum_{j \le k} \kappa_j^{(k)} (1 - \lambda)^{k - j} (-\lambda)^j.$$

This is a definition, not an identification. The book says that the formula can "be derived
easily from the explicit expression of the Jacobi polynomials and the fact that $\{R_k\}$ is
orthogonal with respect to the weight $\lambda w(\lambda)$". This derivation needs Jacobi
polynomials and their orthogonality, which Mathlib does not have, so $R_k$ is not shown to
satisfy `SaadSparse.Chapter12.IsLeastSquaresResidual`. What is stated is what the book computes
from the formula, Example 12.1.

**Scope.** The finite expression is defined for all real parameters. The source identifies it
with the Jacobi least-squares residual only in its weight setting. This declaration gives the
expression and leaves that characterization unproved. -/
noncomputable def equation_12_16 (mu nu : ℝ) (k : ℕ) (l : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), kappa_12_16 mu nu k j * (1 - l) ^ (k - j) * (-l) ^ j

/-- **Example 12.1** of [saad2003iterative]. For the Jacobi weight with $\mu = 1/2$ and
$\nu = -1/2$, let $R_k$ be the polynomial (12.16). Then for every $\lambda \in \mathbb{R}$ and
$k = 1, \dots, 8$
$$\frac{3 + 2k}{4} \bigl(1 - R_{k+1}(\lambda)\bigr) = \lambda \, s_k(4 \lambda),$$
where, with $t = 4\lambda$,
$$\begin{aligned}
  s_1(t) &= 5 - t, \\
  s_2(t) &= 14 - 7t + t^2, \\
  s_3(t) &= 30 - 27t + 9t^2 - t^3, \\
  s_4(t) &= 55 - 77t + 44t^2 - 11t^3 + t^4, \\
  s_5(t) &= 91 - 182t + 156t^2 - 65t^3 + 13t^4 - t^5, \\
  s_6(t) &= 140 - 378t + 450t^2 - 275t^3 + 90t^4 - 15t^5 + t^6, \\
  s_7(t) &= 204 - 714t + 1122t^2 - 935t^3 + 442t^4 - 119t^5 + 17t^6 - t^7, \\
  s_8(t) &= 285 - 1254t + 2508t^2 - 2717t^3 + 1729t^4 - 665t^5 + 152t^6 - 19t^7 + t^8.
\end{aligned}$$
These are the eight rows of the table of the book.

The table lists the polynomials on $[0, 4]$, "as this leads to integer coefficients", each
scaled by $(3 + 2k)/4$. On an interval $[0, \beta]$ the polynomial of degree $k$ is
$s_k(4\lambda/\beta)$, so at $\beta = 1$, the interval of the weight (12.15), the tabulated
$s_k$ at $4\lambda$ is $(3 + 2k)/4$ times $(1 - R_{k+1}(\lambda))/\lambda$. The identities are
cleared of the division by $\lambda$, so they also hold at $\lambda = 0$. As the book says, the
scaling factor does not matter for preconditioning; it is kept because it makes the printed
coefficients integers. -/
theorem example_12_1 (l : ℝ) :
      (5 / 4) * (1 - equation_12_16 (1 / 2) (-1 / 2) 2 l) =
        l * (5 - (4 * l)) ∧
      (7 / 4) * (1 - equation_12_16 (1 / 2) (-1 / 2) 3 l) =
        l * (14 - 7 * (4 * l) + (4 * l) ^ 2) ∧
      (9 / 4) * (1 - equation_12_16 (1 / 2) (-1 / 2) 4 l) =
        l * (30 - 27 * (4 * l) + 9 * (4 * l) ^ 2 - (4 * l) ^ 3) ∧
      (11 / 4) * (1 - equation_12_16 (1 / 2) (-1 / 2) 5 l) =
        l * (55 - 77 * (4 * l) + 44 * (4 * l) ^ 2 - 11 * (4 * l) ^ 3 + (4 * l) ^ 4) ∧
      (13 / 4) * (1 - equation_12_16 (1 / 2) (-1 / 2) 6 l) =
        l * (91 - 182 * (4 * l) + 156 * (4 * l) ^ 2 - 65 * (4 * l) ^ 3 + 13 * (4 * l) ^ 4
          - (4 * l) ^ 5) ∧
      (15 / 4) * (1 - equation_12_16 (1 / 2) (-1 / 2) 7 l) =
        l * (140 - 378 * (4 * l) + 450 * (4 * l) ^ 2 - 275 * (4 * l) ^ 3 + 90 * (4 * l) ^ 4
          - 15 * (4 * l) ^ 5 + (4 * l) ^ 6) ∧
      (17 / 4) * (1 - equation_12_16 (1 / 2) (-1 / 2) 8 l) =
        l * (204 - 714 * (4 * l) + 1122 * (4 * l) ^ 2 - 935 * (4 * l) ^ 3 + 442 * (4 * l) ^ 4
          - 119 * (4 * l) ^ 5 + 17 * (4 * l) ^ 6 - (4 * l) ^ 7) ∧
      (19 / 4) * (1 - equation_12_16 (1 / 2) (-1 / 2) 9 l) =
        l * (285 - 1254 * (4 * l) + 2508 * (4 * l) ^ 2 - 2717 * (4 * l) ^ 3 + 1729 * (4 * l) ^ 4
          - 665 * (4 * l) ^ 5 + 152 * (4 * l) ^ 6 - 19 * (4 * l) ^ 7 + (4 * l) ^ 8) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [equation_12_16, kappa_12_16, Finset.sum_range_succ, Finset.sum_range_zero,
      Finset.prod_range_succ, Finset.prod_range_zero, Nat.choose] <;>
    norm_num <;> ring

end SaadSparse.Chapter12
