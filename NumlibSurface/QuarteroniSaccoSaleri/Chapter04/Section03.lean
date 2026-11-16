/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Eigen.Pencil
import Numlib.Krylov.Convergence.CG
import Numlib.Krylov.Preconditioned
import Numlib.Krylov.ToEuclideanLin
import Numlib.Projection.ConjugateDirection
import Numlib.RingTheory.Polynomial.ChebyshevMinimax
import Numlib.Stationary.ADI
import Numlib.Stationary.Richardson
import NumlibSurface.QuarteroniSaccoSaleri.Chapter04.Section02

/-!
# Quarteroni, Sacco and Saleri, Section 4.3: Stationary and nonstationary iterative methods

This module formalizes §4.3 of [quarteroni2000numerical]: iterative methods for a linear system
$Ax = b$, $A \in \mathbb{R}^{n \times n}$, that are built from a preconditioner $P$ and a sequence
of parameters. It covers the stationary and nonstationary Richardson methods
$x^{(k+1)} = x^{(k)} + \alpha_k P^{-1} r^{(k)}$ with the residual $r^{(k)} = b - Ax^{(k)}$, their
convergence theory (Theorems 4.8–4.9, Corollary 4.1) and the bounds on the spectrum of $P^{-1}A$
(Remark 4.2, (4.33)). It then treats the gradient method, which minimizes the energy
$\Phi(y) = \frac12 y^T A y - y^T b$ along the residual (Theorem 4.10); the conjugate gradient
method, with its conjugacy and orthogonality relations, its finite termination and its Chebyshev
error bound (Definition 4.4, Theorems 4.11–4.12, Property 4.6); the preconditioned conjugate
gradient method (§4.3.5); and the alternating-direction method of Peaceman and Rachford (§4.3.6).

The proofs specialize the backbone modules `Numlib.Stationary.Richardson` and
`Numlib.Stationary.SPD` (the Richardson splitting and its optimal parameter), `Numlib.Eigen.Pencil`
(the generalized eigenvalue problem), `Numlib.Analysis.InnerProductSpace.Energy` (the energy
functional and its gradient), `Numlib.Projection.OneDimensional`, `Numlib.Projection.Optimality` and
`Numlib.Projection.ConjugateDirection` (steepest descent, optimality along a direction, conjugate
directions), `Numlib.Krylov.CG` and `Numlib.Krylov.Convergence.CG` (the conjugate gradient
recurrence, its invariants and its Chebyshev bound), `Numlib.RingTheory.Polynomial.ChebyshevMinimax`
(the minimax property of the Chebyshev polynomials), `Numlib.Krylov.Preconditioned` (the
preconditioned method) and `Numlib.Stationary.ADI` (the alternating-direction method).

## Main definitions

* Equation (4.23), `QuarteroniSaccoSaleri.Chapter04.richardsonStep`: one step
  $x \mapsto x + \alpha P^{-1}(b - Ax)$ of the stationary preconditioned Richardson method.
* Equation (4.24), `QuarteroniSaccoSaleri.Chapter04.nonstationaryRichardson`: the iterates of the
  nonstationary Richardson method with parameters $\alpha_k$.
* §4.3.3, `QuarteroniSaccoSaleri.Chapter04.energy`: the energy $\Phi(y) = \frac12 y^T A y - y^T b$
  of the system.
* Equations (4.36)–(4.37), `QuarteroniSaccoSaleri.Chapter04.gradientStep`: one step of the gradient
  method.
* Definition 4.4, `QuarteroniSaccoSaleri.Chapter04.definition_4_4` and
  `QuarteroniSaccoSaleri.Chapter04.IsOptimalWrtSubspace`: optimality of a point with respect to a
  direction and with respect to a subspace.
* Equations (4.39)–(4.41), `QuarteroniSaccoSaleri.Chapter04.cgStep` and
  `QuarteroniSaccoSaleri.Chapter04.cg`: the conjugate gradient method.
* §4.3.5, `QuarteroniSaccoSaleri.Chapter04.pcgStep` and `QuarteroniSaccoSaleri.Chapter04.pcg`: the
  preconditioned conjugate gradient method.
* Equation (4.50), `QuarteroniSaccoSaleri.Chapter04.adiStep`,
  `QuarteroniSaccoSaleri.Chapter04.adiMatrix` and `QuarteroniSaccoSaleri.Chapter04.adiConst`: the
  alternating-direction method, its iteration matrix $B$ and its vector $f$.

## Main results

* Equation (4.25), `QuarteroniSaccoSaleri.Chapter04.equation_4_25`: one nonstationary Richardson
  step solves $Pz^{(k)} = r^{(k)}$ and updates the solution and the residual.
* Theorem 4.8, `QuarteroniSaccoSaleri.Chapter04.theorem_4_8`: for nonsingular $P$, the stationary
  Richardson method converges if and only if $2 \operatorname{Re} \lambda_i / (\alpha
  |\lambda_i|^2) > 1$ for every eigenvalue $\lambda_i$ of $P^{-1}A$.
* Theorem 4.9, `QuarteroniSaccoSaleri.Chapter04.theorem_4_9`: if $P^{-1}A$ has real eigenvalues
  $\lambda_1 \ge \dots \ge \lambda_n > 0$, the method converges if and only if
  $0 < \alpha < 2/\lambda_1$.
* Theorem 4.9, `QuarteroniSaccoSaleri.Chapter04.theorem_4_9_optimal`: the optimal parameter
  $\alpha_{\mathrm{opt}} = 2/(\lambda_1 + \lambda_n)$ and the optimal spectral radius $(\lambda_1 -
  \lambda_n)/(\lambda_1 + \lambda_n)$ of (4.27)–(4.28).
* §4.3.1, `QuarteroniSaccoSaleri.Chapter04.richardson_monotone_of_posDef`: for symmetric positive
  definite $P^{-1}A$ the convergence is monotone in $\|\cdot\|_2$, and also in $\|\cdot\|_A$ when
  $A$ is symmetric positive definite and $P$ is symmetric.
* Equation (4.29), `QuarteroniSaccoSaleri.Chapter04.equation_4_29`: the optimal spectral radius and
  parameter in terms of $K_2(P^{-1}A)$.
* Corollary 4.1, `QuarteroniSaccoSaleri.Chapter04.corollary_4_1` and
  `QuarteroniSaccoSaleri.Chapter04.corollary_4_1_preconditioned`: convergence of the non
  preconditioned method for $0 < \alpha < 2/\lambda_{\max}(A)$, and the estimate (4.30)
  $\|e^{(k+1)}\|_A \le \rho(R_\alpha) \|e^{(k)}\|_A$.
* Remark 4.2, `QuarteroniSaccoSaleri.Chapter04.remark_4_2`: the eigenvalues of $P^{-1}A$ are the
  generalized eigenvalues of $Ax = \lambda Px$, they are real, and each is a generalized Rayleigh
  quotient.
* Equation (4.33), `QuarteroniSaccoSaleri.Chapter04.equation_4_33`:
  $\lambda_{\min}(A)/\lambda_{\max}(P) \le \lambda \le \lambda_{\max}(A)/\lambda_{\min}(P)$ for the
  eigenvalues $\lambda$ of $P^{-1}A$.
* Equation (4.34), `QuarteroniSaccoSaleri.Chapter04.equation_4_34`:
  $\nabla \Phi(y) = \frac12 (A^T + A) y - b$.
* Equation (4.35), `QuarteroniSaccoSaleri.Chapter04.equation_4_35`: for symmetric positive definite
  $A$, $\Phi(y) - \Phi(x) = \frac12 \|y - x\|_A^2$, so the solution $x$ minimizes $\Phi$.
* Equation (4.37), `QuarteroniSaccoSaleri.Chapter04.equation_4_37`: the gradient method is the
  nonstationary Richardson method with $P = I$ and the parameters of (4.37).
* Theorem 4.10, `QuarteroniSaccoSaleri.Chapter04.theorem_4_10`: the gradient method converges, with
  $\|e^{(k+1)}\|_A \le \frac{K_2(A) - 1}{K_2(A) + 1} \|e^{(k)}\|_A$ (4.38).
* §4.3.4, `QuarteroniSaccoSaleri.Chapter04.definition_4_4_iff` and
  `QuarteroniSaccoSaleri.Chapter04.optimal_preserved_iff_conjugate`: optimality with respect to $p$
  means $p^T r = 0$, and it is preserved by a step $q$ if and only if $p^T A q = 0$.
* §4.3.4, `QuarteroniSaccoSaleri.Chapter04.cg_eq_CG`: the conjugate gradient method is the backbone
  recurrence `CG.iterate`.
* Equation (4.42), `QuarteroniSaccoSaleri.Chapter04.equation_4_42`: the descent directions are
  $A$-conjugate.
* Equations (4.43)–(4.44), `QuarteroniSaccoSaleri.Chapter04.equation_4_44`: the residual is
  orthogonal to the earlier directions, and the directions and the residuals span the Krylov
  subspaces.
* Equation (4.45), `QuarteroniSaccoSaleri.Chapter04.equation_4_45`:
  $\alpha_k = \|r^{(k)}\|^2 / p^{(k)T} A p^{(k)}$ and $\beta_k = -\|r^{(k+1)}\|^2 / \|r^{(k)}\|^2$.
* Equation (4.46), `QuarteroniSaccoSaleri.Chapter04.equation_4_46`: the three-term recurrence of the
  residuals.
* Theorem 4.11, `QuarteroniSaccoSaleri.Chapter04.theorem_4_11`: a method with $A$-conjugate
  directions terminates after at most $n$ steps with the exact solution.
* Theorem 4.12, `QuarteroniSaccoSaleri.Chapter04.theorem_4_12_terminates`,
  `QuarteroniSaccoSaleri.Chapter04.theorem_4_12_orthogonal` and
  `QuarteroniSaccoSaleri.Chapter04.theorem_4_12_bound`: the conjugate gradient method terminates
  after at most $n$ steps, its error is $A$-orthogonal to the earlier directions, and it satisfies
  the bound (4.47).
* Equations (4.48)–(4.49), `QuarteroniSaccoSaleri.Chapter04.equation_4_49`: the $A$-norm of the
  error is the minimum of $\|q(A) e^{(0)}\|_A$ over the polynomials $q$ of degree at most $k$ with
  $q(0) = 1$.
* Property 4.6, `QuarteroniSaccoSaleri.Chapter04.property_4_6` and
  `QuarteroniSaccoSaleri.Chapter04.property_4_6_unique`: the shifted Chebyshev polynomial is the
  unique solution of the minimax problem on $[\lambda_n, \lambda_1]$.
* Exercise 12, `QuarteroniSaccoSaleri.Chapter04.exercise_4_12`: an example where the second gradient
  iterate is not optimal with respect to the first residual.
* §4.3.5, `QuarteroniSaccoSaleri.Chapter04.pcg_eq_PCG` and
  `QuarteroniSaccoSaleri.Chapter04.pcg_energyNorm_error_le`: the preconditioned method is the
  backbone recurrence `Krylov.PCG.iterate`, and its error estimate.
* §4.3.6, `QuarteroniSaccoSaleri.Chapter04.adiStep_eq_affineStep` and
  `QuarteroniSaccoSaleri.Chapter04.equation_4_50`: the alternating-direction method is the method
  (4.2) with the matrix $B$ and the vector $f$, which are the backbone's Peaceman–Rachford
  operators.
* §4.3.6, `QuarteroniSaccoSaleri.Chapter04.adi_spectralRadius_le`,
  `QuarteroniSaccoSaleri.Chapter04.adi_tendsto` and
  `QuarteroniSaccoSaleri.Chapter04.adi_spectralRadius_le_sq`: the estimate of $\rho(B)$, convergence
  for $\alpha_1 = \alpha_2 > 0$, and the bound for the parameter $1/\sqrt{\delta\gamma}$.

## Conventions

* Two models of $\mathbb{R}^n$ are used, as in the rest of the chapter. The Richardson methods of
  §4.3.1–4.3.2 and the alternating-direction method of §4.3.6 are stationary iterations on
  `Fin n → ℝ`, written with `A *ᵥ x` and `x ⬝ᵥ y`. They are identified with the splitting steps of
  §4.2 and with the step `QuarteroniSaccoSaleri.Chapter04.affineStep B f` of the method (4.2), and
  their convergence is read through Theorem 4.1 (`QuarteroniSaccoSaleri.Chapter04.theorem_4_1`) and
  the spectral radius `Matrix.complexSpectralRadius`.
* The gradient and conjugate gradient methods of §4.3.3–4.3.5, whose subject is an inner product,
  are stated on `EuclideanSpace ℝ (Fin n)`. There a matrix acts as `Matrix.toEuclideanLin A`, the
  inner product $(x, y)$ of the source is `inner ℝ x y` (the two orders agree over $\mathbb{R}$),
  and the energy norm $\|x\|_A = (x, Ax)^{1/2}$ of (1.28) is `energyNorm (toEuclideanLin A) x`. The
  two models are related by `WithLp.toLp 2`.
* Matrix norms are the spectral norm (Mathlib's scoped `Matrix.Norms.L2Operator`), so that
  $K_2(A) = \|A\|_2 \|A^{-1}\|_2$ is `NormedRing.condNumber A`, written `κ A`.
* "The eigenvalues of $P^{-1}A$" are `spectrum ℂ (complexify (P⁻¹ * A))`. "$P^{-1}A$ has real
  positive eigenvalues $\lambda_1 \ge \dots \ge \lambda_n > 0$" is the triple of hypotheses
  `spectrum ℂ (complexify (P⁻¹ * A)) ⊆ Complex.ofReal '' Set.Icc lmin lmax`,
  `lmin ∈ spectrum ℝ (P⁻¹ * A)` and `lmax ∈ spectrum ℝ (P⁻¹ * A)`, with `0 < lmin`; here `lmax` is
  $\lambda_1$ and `lmin` is $\lambda_n$. For a symmetric matrix the eigenvalues are Mathlib's
  `Matrix.IsHermitian.eigenvalues`.

## Implementation notes

* The conjugate gradient method is written in the letters of the source
  (`QuarteroniSaccoSaleri.Chapter04.cgStep`, `QuarteroniSaccoSaleri.Chapter04.cg`), with the
  direction update $p^{(k+1)} = r^{(k+1)} - \beta_k p^{(k)}$ of (4.41). Its $\beta_k$ is therefore
  the negative of the backbone's `CG.beta`. `QuarteroniSaccoSaleri.Chapter04.cg_eq_CG` identifies
  the method with the backbone recurrence `CG.iterate`, and every property of the method is read off
  this identification. The preconditioned method (`QuarteroniSaccoSaleri.Chapter04.pcgStep`,
  `QuarteroniSaccoSaleri.Chapter04.pcg`) is treated in the same way through `Krylov.PCG.iterate`
  (`QuarteroniSaccoSaleri.Chapter04.pcg_eq_PCG`).
* Inverses are Mathlib's matrix inverse, which is $0$ for a singular matrix. The algebraic
  identities, such as `QuarteroniSaccoSaleri.Chapter04.richardsonStep_eq_affineStep` and
  `QuarteroniSaccoSaleri.Chapter04.adiStep_eq_affineStep`, hold without a nonsingularity hypothesis.
  Quotients with a zero denominator are $0$.

## Deviations from the source

* **Corollary 4.1** (correction). The source states that the non preconditioned stationary
  Richardson method is convergent with no condition on $\alpha$; it needs
  $0 < \alpha < 2/\lambda_{\max}(A)$, the range of Theorem 4.9. See
  `QuarteroniSaccoSaleri.Chapter04.corollary_4_1`.
* **Corollary 4.1, the preconditioned method** (generalization). The source asks $P$, $A$ and
  $P^{-1}A$ to be symmetric positive definite; only $P$ and $A$ need to be, as the closing sentence
  of the corollary says. See `QuarteroniSaccoSaleri.Chapter04.corollary_4_1_preconditioned`.
* **The sentence after Theorem 4.9** (correction). Monotone convergence in $\|\cdot\|_A$ for
  symmetric positive definite $P^{-1}A$ needs $P$ symmetric as well. See
  `QuarteroniSaccoSaleri.Chapter04.richardson_monotone_of_posDef`.
* **Equation (4.33)** (reading). The printed lower bound presupposes $\lambda_{\min}(A) \ge 0$,
  which is assumed. See `QuarteroniSaccoSaleri.Chapter04.equation_4_33`.
* **Definition 4.4** (typo). The source calls the point $x^{(k)}$ a direction. See
  `QuarteroniSaccoSaleri.Chapter04.definition_4_4`.
* **Definition 4.4** (generalization). The source assumes $p \neq 0$; the definition does not. See
  `QuarteroniSaccoSaleri.Chapter04.definition_4_4`.
* **Equation (4.45)** (correction). The source prints $\beta_k = \|r^{(k+1)}\|^2 / \|r^{(k)}\|^2$;
  with the update (4.41) the sign is negative. See `QuarteroniSaccoSaleri.Chapter04.equation_4_45`.
* **Equation (4.46)** (typo). The source prints $\beta_k/\alpha_{k-1}$ for the coefficient of
  $r^{(k-1)}$; it is $\beta_{k-1}/\alpha_{k-1}$. See
  `QuarteroniSaccoSaleri.Chapter04.equation_4_46`.
* **Theorem 4.11** (reading). The conjugate directions are assumed nonzero. See
  `QuarteroniSaccoSaleri.Chapter04.theorem_4_11`.
* **Theorem 4.12** (correction). The source states that the error is orthogonal to the earlier
  directions; it is $A$-orthogonal to them. See
  `QuarteroniSaccoSaleri.Chapter04.theorem_4_12_orthogonal`.
* **Equation (4.49)** (generalization). The source takes $x^{(0)} = 0$; any $x^{(0)}$ is allowed.
  See `QuarteroniSaccoSaleri.Chapter04.equation_4_49`.
* **§4.3.6, the vector $f$** (correction). The display after (4.50) omits the leading factor
  $(I + \alpha_2 A_2)^{-1}$ of $f$. See `QuarteroniSaccoSaleri.Chapter04.adiConst`.
* **§4.3.6, the last display** (reading). The proviso that $\gamma/\delta$ tends to $0$ as the size
  of $A$ grows is not a hypothesis of the inequality. See
  `QuarteroniSaccoSaleri.Chapter04.adi_spectralRadius_le_sq`.

## Not formalized

* **The catalogue of preconditioners in §4.3.2.** It states no result.
* **Programs 17–18.** They are code.
* **Examples 4.4–4.7.** They are numerical experiments.
* **Remark 4.3.** It is prose on rounding.
* **Exercise 12, the general claim** that $x^{(k+1)}$ is optimal with respect to $r^{(k)}$ for every
  $k$.
-/

open Filter Finset Matrix Stationary Topology WithLp
open scoped ENNReal NNReal Matrix.Norms.L2Operator NormedRing

namespace QuarteroniSaccoSaleri.Chapter04

variable {n : ℕ}

/-! ### The Richardson methods (4.23)–(4.25) -/

section Richardson

variable (A P : Matrix (Fin n) (Fin n) ℝ)

/-- For a field $\mathbb{K}$, a scalar $c \neq 0$ and a square matrix $M$, Mathlib's inverse
satisfies $(cM)^{-1} = c^{-1} M^{-1}$; both sides are $0$ when $M$ is singular. -/
private theorem inv_smul_eq {𝕜 : Type*} [Field 𝕜] {c : 𝕜} (hc : c ≠ 0)
    (M : Matrix (Fin n) (Fin n) 𝕜) : (c • M)⁻¹ = c⁻¹ • M⁻¹ := by
  by_cases hM : IsUnit M.det
  · have h := inv_smul' M (Units.mk0 c hc) hM
    simpa [Units.smul_def] using h
  · have hcM : ¬ IsUnit (c • M).det := by
      rw [det_smul, isUnit_iff_ne_zero, not_not]
      rw [isUnit_iff_ne_zero, not_not] at hM
      simp [hM]
    rw [nonsing_inv_apply_not_isUnit _ hM, nonsing_inv_apply_not_isUnit _ hcM, smul_zero]

/-- **Equation (4.23)** of [quarteroni2000numerical]. Let $A, P \in \mathbb{R}^{n \times n}$,
$\alpha \in \mathbb{R}$ and $b \in \mathbb{R}^n$. One step of the **stationary preconditioned
Richardson method** with acceleration parameter $\alpha$ maps $x \in \mathbb{R}^n$ to
$$x + \alpha P^{-1} r, \qquad r = b - Ax.$$

The $k$-th iterate from $x^{(0)}$ is `(richardsonStep A P α b)^[k] x₀`, and $P^{-1}$ is
Mathlib's inverse, which is $0$ for a singular $P$. For $P$ nonsingular and $\alpha \neq 0$ the
step is that of the splitting $A = \alpha^{-1} P - (\alpha^{-1} P - A)$
(`QuarteroniSaccoSaleri.Chapter04.richardsonStep_eq`), its iteration matrix is
$R_\alpha = I - \alpha P^{-1} A$
(`QuarteroniSaccoSaleri.Chapter04.richardsonStep_eq_affineStep`), and the Jacobi and
Gauss–Seidel methods are the cases $\alpha = 1$ with $P = D$ and $P = D - E$
(`QuarteroniSaccoSaleri.Chapter04.richardsonStep_jacobi_gaussSeidel`). -/
noncomputable def richardsonStep (α : ℝ) (b x : Fin n → ℝ) : Fin n → ℝ :=
  x + α • (P⁻¹ *ᵥ (b - A *ᵥ x))

/-- **Section 4.3** of [quarteroni2000numerical], the display after (4.24). Let
$A, P \in \mathbb{R}^{n \times n}$, $\alpha \in \mathbb{R}$ and $b \in \mathbb{R}^n$. The
stationary Richardson step (4.23) is the linear iterative method (4.2), $x \mapsto Bx + f$, with
the **iteration matrix** $B = R_\alpha = I - \alpha P^{-1} A$ and the vector
$f = \alpha P^{-1} b$.

The method (4.2) is `QuarteroniSaccoSaleri.Chapter04.affineStep`. The identity is algebraic, so
it holds for every $\alpha$ and every $P$, also for a singular $P$, where Mathlib's $P^{-1}$ is
$0$. -/
theorem richardsonStep_eq_affineStep (α : ℝ) (b : Fin n → ℝ) :
    richardsonStep A P α b = affineStep (1 - α • (P⁻¹ * A)) (α • (P⁻¹ *ᵥ b)) := by
  funext x
  simp only [richardsonStep, affineStep, sub_mulVec, one_mulVec, smul_mulVec, mulVec_mulVec,
    mulVec_sub, smul_sub]
  abel

/-- Let $A, P \in \mathbb{R}^{n \times n}$ with $P$ nonsingular, and let $\alpha \neq 0$. The
Richardson step (4.23) is the step of the splitting $A = \alpha^{-1} P - (\alpha^{-1} P - A)$ of
§4.2, and the iteration matrix of this splitting is $R_\alpha = I - \alpha P^{-1} A$.

The splitting is the backbone's `Stationary.Splitting.preconditionedRichardson`, and its
iteration matrix is given by `Stationary.Splitting.preconditionedRichardson_iterationOperator`. -/
theorem richardsonStep_eq {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsUnit P) {α : ℝ} (hα : α ≠ 0)
    (b : Fin n → ℝ) :
    richardsonStep A P α b = (Splitting.preconditionedRichardson A hP hα).mulVecStep b ∧
      (Splitting.preconditionedRichardson A hP hα).iterationOperator = 1 - α • (P⁻¹ * A) := by
  refine ⟨funext fun x => ?_, Splitting.preconditionedRichardson_iterationOperator A hP hα⟩
  rw [Splitting.mulVecStep_eq_add_inv_mulVec, richardsonStep,
    Splitting.preconditionedRichardson_m, inv_smul_eq (inv_ne_zero hα), inv_inv, smul_mulVec]

/-- **Section 4.3** of [quarteroni2000numerical], the sentence after (4.24). Let
$A \in \mathbb{R}^{n \times n}$ have nonzero diagonal entries and let $b \in \mathbb{R}^n$. The
Jacobi and Gauss–Seidel methods of §4.2.1 are stationary Richardson methods with $\alpha = 1$
and $P = D$, respectively $P = D - E$: one Richardson step is one Jacobi sweep, respectively one
Gauss–Seidel sweep.

The matrices $D$ and $E$ are `QuarteroniSaccoSaleri.Chapter04.D` and
`QuarteroniSaccoSaleri.Chapter04.E`. The Jacobi sweep is `Matrix.jorSweep A 1` and the
Gauss–Seidel sweep is `Matrix.sorSweep A 1`. The hypothesis on the diagonal is
`IsUnit (diagPart A)`. -/
theorem richardsonStep_jacobi_gaussSeidel (h : IsUnit (diagPart A)) (b : Fin n → ℝ) :
    richardsonStep A (D A) 1 b = jorSweep A 1 b ∧
      richardsonStep A (D A - E A) 1 b = sorSweep A 1 b := by
  constructor
  · rw [jorSweep_one_eq_mulVecStep A h b, D, (richardsonStep_eq A h one_ne_zero b).1,
      Splitting.preconditionedRichardson_diagPart, jorSplitting_one]
  · have hDE : IsUnit (D A - E A) := by
      rw [D_sub_E]
      exact (gaussSeidelSplitting A h).isUnit
    rw [sorSweep_one_eq_mulVecStep A h b, (richardsonStep_eq A hDE one_ne_zero b).1]
    funext x
    rw [Splitting.mulVecStep_eq_add_inv_mulVec, Splitting.mulVecStep_eq_add_inv_mulVec,
      Splitting.preconditionedRichardson_m, inv_one, one_smul, D_sub_E]
    rfl

/-- **Equation (4.24)** of [quarteroni2000numerical]. Let $A, P \in \mathbb{R}^{n \times n}$, let
$\alpha_0, \alpha_1, \dots$ be real parameters and $b, x^{(0)} \in \mathbb{R}^n$. The
**nonstationary Richardson method** (semi-iterative method) is
$$x^{(k+1)} = x^{(k)} + \alpha_k P^{-1} r^{(k)}, \qquad r^{(k)} = b - Ax^{(k)},$$
with a parameter $\alpha_k$ that depends on the step.

Under `WithLp.toLp 2` it is the backbone's `Richardson.iterate`
(`QuarteroniSaccoSaleri.Chapter04.toLp_nonstationaryRichardson`). -/
noncomputable def nonstationaryRichardson (α : ℕ → ℝ) (b x₀ : Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => x₀
  | k + 1 => richardsonStep A P (α k) b (nonstationaryRichardson α b x₀ k)

/-- **Equation (4.25)** of [quarteroni2000numerical]. Let $P$ be nonsingular and let $x^{(k)}$ be
the iterates of the nonstationary Richardson method (4.24). With the preconditioned residual
$z^{(k)} = P^{-1} r^{(k)}$, one step solves $Pz^{(k)} = r^{(k)}$, updates the solution
$$x^{(k+1)} = x^{(k)} + \alpha_k z^{(k)},$$
and updates the residual
$$r^{(k+1)} = r^{(k)} - \alpha_k A z^{(k)}.$$

Only the first clause needs $P$ nonsingular. The residual update is the backbone's
`Richardson.residual_iterate_succ`. -/
theorem equation_4_25 (hP : IsUnit P) (α : ℕ → ℝ) (b x₀ : Fin n → ℝ) (k : ℕ) :
    P *ᵥ (P⁻¹ *ᵥ (b - A *ᵥ nonstationaryRichardson A P α b x₀ k)) =
        b - A *ᵥ nonstationaryRichardson A P α b x₀ k ∧
      nonstationaryRichardson A P α b x₀ (k + 1) = nonstationaryRichardson A P α b x₀ k +
        α k • (P⁻¹ *ᵥ (b - A *ᵥ nonstationaryRichardson A P α b x₀ k)) ∧
      b - A *ᵥ nonstationaryRichardson A P α b x₀ (k + 1) =
        (b - A *ᵥ nonstationaryRichardson A P α b x₀ k) -
          α k • (A *ᵥ (P⁻¹ *ᵥ (b - A *ᵥ nonstationaryRichardson A P α b x₀ k))) := by
  refine ⟨mulVec_nonsing_inv_mulVec hP _, rfl, ?_⟩
  simp only [nonstationaryRichardson, richardsonStep, mulVec_add, mulVec_smul]
  abel

/-- Under `WithLp.toLp 2`, the nonstationary Richardson method (4.24) is the backbone's
`Richardson.iterate` of the operators `toEuclideanLin A` and `toEuclideanLin P⁻¹` on
`EuclideanSpace ℝ (Fin n)`, with the same parameters, right-hand side and initial vector. -/
theorem toLp_nonstationaryRichardson (α : ℕ → ℝ) (b x₀ : Fin n → ℝ) (k : ℕ) :
    (toLp 2 (nonstationaryRichardson A P α b x₀ k) : EuclideanSpace ℝ (Fin n)) =
      Richardson.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) α (toLp 2 b) (toLp 2 x₀) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Richardson.iterate_succ, ← ih]
    rfl

end Richardson

/-! ### §4.3.1 Convergence analysis of the Richardson method -/

section Convergence

variable {A P : Matrix (Fin n) (Fin n) ℝ}

/-- Let $P \in \mathbb{R}^{n \times n}$ be nonsingular and $\alpha \in \mathbb{R}$, and let
$R_\alpha = I - \alpha P^{-1} A$. The stationary Richardson method (4.23) converges to
$A^{-1} b$ from every $x^{(0)}$ and for every $b$ if and only if $\rho(R_\alpha) < 1$. This is
Theorem 4.1 for the method (4.23), on which Theorems 4.8 and 4.9 rest.

For $\alpha \neq 0$ the proof is `QuarteroniSaccoSaleri.Chapter04.Splitting.forall_tendsto_iff`
for the splitting of `QuarteroniSaccoSaleri.Chapter04.richardsonStep_eq`. For $\alpha = 0$ the
method is the identity map, which is consistent with every system, and
`QuarteroniSaccoSaleri.Chapter04.theorem_4_1` applies directly. The spectral radius is
`Matrix.complexSpectralRadius`. -/
theorem forall_tendsto_richardsonStep_iff (hP : IsUnit P) (α : ℝ) :
    (∀ b x₀, Tendsto (fun k => (richardsonStep A P α b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b))) ↔
      complexSpectralRadius (1 - α • (P⁻¹ * A)) < 1 := by
  rcases eq_or_ne α 0 with rfl | hα
  · have hstep : ∀ b, richardsonStep A P 0 b = affineStep 1 0 := fun b => by
      rw [richardsonStep_eq_affineStep, zero_smul, sub_zero, zero_smul]
    have hc : ∀ b, definition_4_1 A b 1 0 := fun b => by
      rw [definition_4_1, one_mulVec, add_zero]
    simp only [hstep, zero_smul, sub_zero]
    exact ⟨fun h => (theorem_4_1 (hc 0)).1 (h 0), fun h b => (theorem_4_1 (hc b)).2 h⟩
  · simp only [(richardsonStep_eq A hP hα _).1]
    rw [Splitting.forall_tendsto_iff, Splitting.preconditionedRichardson_iterationOperator]

/-- **Theorem 4.8** of [quarteroni2000numerical]. Let $n \ge 1$, let
$A, P \in \mathbb{R}^{n \times n}$ with $P$ nonsingular, and let $\alpha \in \mathbb{R}$. The
stationary Richardson method (4.23) converges to $A^{-1} b$ from every $x^{(0)}$ and for every
$b$ if and only if every eigenvalue $\lambda_i \in \mathbb{C}$ of $P^{-1} A$ satisfies (4.26):
$$\frac{2 \operatorname{Re} \lambda_i}{\alpha |\lambda_i|^2} > 1.$$

The proof applies Theorem 4.1 to $R_\alpha = I - \alpha P^{-1} A$, whose eigenvalues are
$1 - \alpha \lambda_i$
(`Stationary.Splitting.complexSpectralRadius_one_sub_smul_lt_one_iff_forall`). At $\alpha = 0$
both sides are false: the iteration does not move, and Lean evaluates a quotient $t/0$ as $0$.
Both sides are also false when $P^{-1}A$ has the eigenvalue $\lambda_i = 0$. -/
theorem theorem_4_8 [NeZero n] (hP : IsUnit P) (α : ℝ) :
    (∀ b x₀, Tendsto (fun k => (richardsonStep A P α b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b))) ↔
      ∀ μ ∈ spectrum ℂ (complexify (P⁻¹ * A)), 1 < 2 * μ.re / (α * ‖μ‖ ^ 2) := by
  rw [forall_tendsto_richardsonStep_iff hP]
  exact Splitting.complexSpectralRadius_one_sub_smul_lt_one_iff_forall _ α

/-- **Theorem 4.9** of [quarteroni2000numerical], convergence. Let
$A, P \in \mathbb{R}^{n \times n}$ with $P$ nonsingular, and assume that $P^{-1} A$ has real
positive eigenvalues $\lambda_1 \ge \lambda_2 \ge \dots \ge \lambda_n > 0$. Then the stationary
Richardson method (4.23) converges from every $x^{(0)}$ and for every $b$ if and only if
$$0 < \alpha < \frac{2}{\lambda_1}.$$

The hypothesis on the eigenvalues says that the complex spectrum of $P^{-1}A$ lies in the real
interval $[\lambda_n, \lambda_1]$, that both endpoints are eigenvalues, and that
$\lambda_n > 0$; `lmax` and `lmin` stand for $\lambda_1$ and $\lambda_n$. The eigenvalues of
$R_\alpha$ are $1 - \alpha \lambda_i$, and the proof uses
`Stationary.Splitting.complexSpectralRadius_one_sub_smul_lt_one_iff`. -/
theorem theorem_4_9 (hP : IsUnit P) {lmin lmax : ℝ}
    (hsub : spectrum ℂ (complexify (P⁻¹ * A)) ⊆ Complex.ofReal '' Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ (P⁻¹ * A)) (hmax : lmax ∈ spectrum ℝ (P⁻¹ * A)) (hpos : 0 < lmin)
    (α : ℝ) :
    (∀ b x₀, Tendsto (fun k => (richardsonStep A P α b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b))) ↔
      0 < α ∧ α < 2 / lmax := by
  rw [forall_tendsto_richardsonStep_iff hP]
  exact Splitting.complexSpectralRadius_one_sub_smul_lt_one_iff hsub hmin hmax hpos α

/-- **Theorem 4.9** of [quarteroni2000numerical], equations (4.27)–(4.28). Let
$A, P \in \mathbb{R}^{n \times n}$ and assume that $P^{-1} A$ has real positive eigenvalues
$\lambda_1 \ge \dots \ge \lambda_n > 0$. Then, among all $\alpha > 0$, the spectral radius of
$R_\alpha = I - \alpha P^{-1} A$ is smallest at
$$\alpha_{\mathrm{opt}} = \frac{2}{\lambda_1 + \lambda_n},$$
and its value there is
$$\rho_{\mathrm{opt}} = \rho(R_{\alpha_{\mathrm{opt}}}) = \frac{\lambda_1 -
  \lambda_n}{\lambda_1 + \lambda_n}.$$

The hypothesis on the eigenvalues is encoded as in
`QuarteroniSaccoSaleri.Chapter04.theorem_4_9`; no separate hypothesis that $P$ is nonsingular is
needed. The proof uses `Stationary.Splitting.isMinOn_complexSpectralRadius_one_sub_smul` and
`Stationary.Splitting.complexSpectralRadius_one_sub_smul_optimal_eq`. -/
theorem theorem_4_9_optimal {lmin lmax : ℝ}
    (hsub : spectrum ℂ (complexify (P⁻¹ * A)) ⊆ Complex.ofReal '' Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ (P⁻¹ * A)) (hmax : lmax ∈ spectrum ℝ (P⁻¹ * A)) (hpos : 0 < lmin) :
    IsMinOn (fun α : ℝ => complexSpectralRadius (1 - α • (P⁻¹ * A))) (Set.Ioi 0)
        (2 / (lmax + lmin)) ∧
      complexSpectralRadius (1 - (2 / (lmax + lmin)) • (P⁻¹ * A)) =
        ENNReal.ofReal ((lmax - lmin) / (lmax + lmin)) := by
  have h1 := Splitting.isMinOn_complexSpectralRadius_one_sub_smul hsub hmin hmax hpos
  have h2 := Splitting.complexSpectralRadius_one_sub_smul_optimal_eq hsub hmin hmax hpos
  rw [add_comm lmin lmax] at h1 h2
  exact ⟨h1, h2⟩

/-- Let $M \in \mathbb{R}^{n \times n}$ be symmetric, with all its eigenvalues in
$[\lambda_{\min}, \lambda_{\max}]$. Then the complex spectrum of $M$ lies in the real interval
$[\lambda_{\min}, \lambda_{\max}]$. This gives the hypothesis of
`QuarteroniSaccoSaleri.Chapter04.theorem_4_9` for a symmetric matrix.

The eigenvalues are `Matrix.IsHermitian.eigenvalues`. The endpoints need not be eigenvalues. -/
theorem spectrum_complexify_subset_of_eigenvalues {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.IsHermitian) {lmin lmax : ℝ} (h : ∀ i, hM.eigenvalues i ∈ Set.Icc lmin lmax) :
    spectrum ℂ (complexify M) ⊆ Complex.ofReal '' Set.Icc lmin lmax := by
  refine hM.spectrum_complexify_subset ?_
  rw [hM.spectrum_real_eq_range_eigenvalues]
  rintro _ ⟨i, rfl⟩
  exact h i

/-- Let $M \in \mathbb{R}^{n \times n}$. If the complex spectrum of $M$ lies in the real interval
$[\lambda_{\min}, \lambda_{\max}]$, then the real spectrum of $M$ lies in
$[\lambda_{\min}, \lambda_{\max}]$. This recovers the real spectrum from the hypothesis of
`QuarteroniSaccoSaleri.Chapter04.theorem_4_9`. -/
theorem spectrum_real_subset_of_spectrum_complexify_subset {M : Matrix (Fin n) (Fin n) ℝ}
    {lmin lmax : ℝ} (hsub : spectrum ℂ (complexify M) ⊆ Complex.ofReal '' Set.Icc lmin lmax) :
    spectrum ℝ M ⊆ Set.Icc lmin lmax := by
  intro μ hμ
  obtain ⟨t, ht, hte⟩ := hsub ((ofReal_mem_spectrum_complexify_iff M μ).mpr hμ)
  rwa [Complex.ofReal_inj.mp hte] at ht

/-- **Section 4.3.1** of [quarteroni2000numerical], the sentence after Theorem 4.9. Let
$A, P \in \mathbb{R}^{n \times n}$ with $P$ nonsingular, let $P^{-1} A$ be symmetric positive
definite with eigenvalues $\lambda_1 \ge \dots \ge \lambda_n > 0$, and let
$0 < \alpha < 2/\lambda_1$. Then $\rho(R_\alpha) < 1$, and the convergence of the Richardson
method is monotone with respect to $\|\cdot\|_2$:
$$\|R_\alpha e\|_2 \le \rho(R_\alpha) \|e\|_2 \quad \text{for every } e \in \mathbb{R}^n.$$
If moreover $A$ is symmetric positive definite and $P$ is symmetric, the convergence is also
monotone with respect to $\|\cdot\|_A$: $\|R_\alpha e\|_A^2 \le \rho(R_\alpha)^2 \|e\|_A^2$ for
every $e$.

**Correction.** The source states that the convergence is monotone with respect to $\|\cdot\|_A$
when $P^{-1}A$ is symmetric positive definite. This clause needs $P$ symmetric, which the
symmetry of $P^{-1}A$ does not imply: for $A = \operatorname{diag}(1, 4)$, $P^{-1}A =
\begin{bmatrix} 2 & 1 \\ 1 & 2 \end{bmatrix}$ and $\alpha = 3/5$, the matrix $R_\alpha$
increases the $A$-norm of $(1, 0)$. The clause is stated here with the hypothesis that $P$ is
symmetric.

The bound in $\|\cdot\|_2$ holds because $R_\alpha$ is symmetric and
$\|R_\alpha\|_2 = \rho(R_\alpha)$ (`Matrix.l2_opNorm_eq_complexSpectralRadius_of_isHermitian`).
The bound in $\|\cdot\|_A$ is
`Stationary.Splitting.energyNorm_mulVec_iterationOperator_le_complexSpectralRadius`, written
with $\|v\|_A^2 = (Av)^T v$. The hypothesis on the eigenvalues is encoded as in
`QuarteroniSaccoSaleri.Chapter04.theorem_4_9`. -/
theorem richardson_monotone_of_posDef (hP : IsUnit P) (hM : (P⁻¹ * A).PosDef) {lmin lmax : ℝ}
    (hsub : spectrum ℂ (complexify (P⁻¹ * A)) ⊆ Complex.ofReal '' Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ (P⁻¹ * A)) (hmax : lmax ∈ spectrum ℝ (P⁻¹ * A)) (hpos : 0 < lmin)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 2 / lmax) :
    complexSpectralRadius (1 - α • (P⁻¹ * A)) < 1 ∧
      (∀ e : Fin n → ℝ, ‖(toLp 2 ((1 - α • (P⁻¹ * A)) *ᵥ e) : EuclideanSpace ℝ (Fin n))‖ ≤
        (complexSpectralRadius (1 - α • (P⁻¹ * A))).toReal *
          ‖(toLp 2 e : EuclideanSpace ℝ (Fin n))‖) ∧
      (A.PosDef → P.IsSymm → ∀ e : Fin n → ℝ,
        (A *ᵥ ((1 - α • (P⁻¹ * A)) *ᵥ e)) ⬝ᵥ ((1 - α • (P⁻¹ * A)) *ᵥ e) ≤
          (complexSpectralRadius (1 - α • (P⁻¹ * A))).toReal ^ 2 * ((A *ᵥ e) ⬝ᵥ e)) := by
  refine ⟨(Splitting.complexSpectralRadius_one_sub_smul_lt_one_iff hsub hmin hmax hpos α).2
    ⟨hα0, hα1⟩, fun e => ?_, fun hA hPs e => ?_⟩
  · have hR : (1 - α • (P⁻¹ * A)).IsHermitian := by
      refine IsHermitian.sub ?_ (hM.1.smul (IsSelfAdjoint.all α))
      exact isHermitian_one
    rw [← l2_opNorm_eq_complexSpectralRadius_of_isHermitian hR, ← toEuclideanCLM_toLp,
      ← l2_opNorm_toEuclideanCLM]
    exact ContinuousLinearMap.le_opNorm _ _
  · have hm : (Splitting.preconditionedRichardson A hP hα0.ne').m.IsHermitian := by
      rw [Splitting.preconditionedRichardson_m, IsHermitian, conjTranspose_smul,
        conjTranspose_eq_transpose_of_trivial, hPs.eq]
      simp
    have h := Splitting.energyNorm_mulVec_iterationOperator_le_complexSpectralRadius
      (Splitting.preconditionedRichardson A hP hα0.ne') hA hm e
    rwa [Splitting.preconditionedRichardson_iterationOperator] at h

/-- **Equation (4.29)** of [quarteroni2000numerical]. Let $A, P \in \mathbb{R}^{n \times n}$ and let
$P^{-1} A$ be symmetric positive definite with eigenvalues
$\lambda_1 \ge \dots \ge \lambda_n > 0$. In terms of the spectral condition number
$K_2(P^{-1}A) = \|P^{-1}A\|_2 \|A^{-1}P\|_2$, the optimal spectral radius and the optimal
parameter of Theorem 4.9 are
$$\rho_{\mathrm{opt}} = \frac{K_2(P^{-1}A) - 1}{K_2(P^{-1}A) + 1}, \qquad
  \alpha_{\mathrm{opt}} = \frac{2 \|A^{-1} P\|_2}{K_2(P^{-1}A) + 1}.$$

The condition number is `NormedRing.condNumber` for the spectral norm, and
$(P^{-1}A)^{-1} = A^{-1} P$. The hypothesis on the eigenvalues is encoded as in
`QuarteroniSaccoSaleri.Chapter04.theorem_4_9`. The proof uses
`Stationary.Splitting.complexSpectralRadius_one_sub_smul_optimal_eq_condNumber` and
`Stationary.Splitting.two_div_add_eq_mul_norm_inv_div_condNumber`. -/
theorem equation_4_29 (hM : (P⁻¹ * A).PosDef) {lmin lmax : ℝ}
    (hsub : spectrum ℂ (complexify (P⁻¹ * A)) ⊆ Complex.ofReal '' Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ (P⁻¹ * A)) (hmax : lmax ∈ spectrum ℝ (P⁻¹ * A)) (hpos : 0 < lmin) :
    complexSpectralRadius (1 - (2 / (lmax + lmin)) • (P⁻¹ * A)) =
        ENNReal.ofReal ((κ (P⁻¹ * A) - 1) / (κ (P⁻¹ * A) + 1)) ∧
      2 / (lmax + lmin) = 2 * ‖A⁻¹ * P‖ / (κ (P⁻¹ * A) + 1) := by
  have hsub' := spectrum_real_subset_of_spectrum_complexify_subset hsub
  have hP : IsUnit P.det := by
    have h := isUnit_of_mul_isUnit_left hM.isUnit
    rwa [isUnit_nonsing_inv_iff, isUnit_iff_isUnit_det] at h
  have hinv : A⁻¹ * P = (P⁻¹ * A)⁻¹ := by
    rw [Matrix.mul_inv_rev, nonsing_inv_nonsing_inv P hP]
  rw [add_comm lmax lmin, hinv]
  exact ⟨Splitting.complexSpectralRadius_one_sub_smul_optimal_eq_condNumber hM.1 hsub' hmin hmax
    hpos, Splitting.two_div_add_eq_mul_norm_inv_div_condNumber hM.1 hsub' hmin hmax hpos⟩

/-- **Corollary 4.1** of [quarteroni2000numerical], the non preconditioned method. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite, with real spectrum in
$[\lambda_{\min}, \lambda_{\max}]$ and both endpoints eigenvalues, and let
$\alpha \in \mathbb{R}$. Consider the non preconditioned stationary Richardson method ($P = I$).
If $0 < \alpha < 2/\lambda_{\max}$, the method converges to $A^{-1} b$ from every $x^{(0)}$ and
for every $b$. For every $\alpha$, the method is the method (4.2) with
$B = R_\alpha = I - \alpha A$ and $f = \alpha b$, so that the error satisfies
$e^{(k+1)} = R_\alpha e^{(k)}$; and $\|R_\alpha e\|_A \le \rho(R_\alpha) \|e\|_A$ for every
$e \in \mathbb{R}^n$, which gives (4.30):
$$\|e^{(k+1)}\|_A \le \rho(R_\alpha) \|e^{(k)}\|_A.$$

**Correction.** The source states that the non preconditioned stationary Richardson method is
convergent, with no condition on $\alpha$. Convergence needs the range
$0 < \alpha < 2/\lambda_{\max}(A)$ of Theorem 4.9: for $\alpha = 3/\lambda_{\max}(A)$ the method
diverges. The estimate (4.30) holds for every $\alpha$.

The error relation is `QuarteroniSaccoSaleri.Chapter04.equation_4_4`. The bound in $\|\cdot\|_A$
is stated as $(AR_\alpha e)^T R_\alpha e \le \rho(R_\alpha)^2 (Ae)^T e$, and it is
`Stationary.Splitting.energyNorm_preconditionedRichardson_mulVec_le` at $P = I$. -/
theorem corollary_4_1 (hA : A.PosDef) {lmin lmax : ℝ} (hsub : spectrum ℝ A ⊆ Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ A) (hmax : lmax ∈ spectrum ℝ A) (α : ℝ) :
    (0 < α → α < 2 / lmax →
        ∀ b x₀, Tendsto (fun k => (richardsonStep A 1 α b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b))) ∧
      (richardsonStep A 1 α = fun b => affineStep (1 - α • A) (α • b)) ∧
      ∀ e : Fin n → ℝ, (A *ᵥ ((1 - α • A) *ᵥ e)) ⬝ᵥ ((1 - α • A) *ᵥ e) ≤
        (complexSpectralRadius (1 - α • A)).toReal ^ 2 * ((A *ᵥ e) ⬝ᵥ e) := by
  have hpos : 0 < lmin := (open scoped MatrixOrder in hA.isStrictlyPositive.spectrum_pos hmin)
  refine ⟨fun hα0 hα1 => ?_, ?_, fun e => ?_⟩
  · rw [forall_tendsto_richardsonStep_iff isUnit_one, inv_one, Matrix.one_mul]
    exact (Splitting.complexSpectralRadius_one_sub_smul_lt_one_iff
      (hA.1.spectrum_complexify_subset hsub) hmin hmax hpos α).2 ⟨hα0, hα1⟩
  · funext b
    rw [richardsonStep_eq_affineStep, inv_one, Matrix.one_mul, one_mulVec]
  · rcases eq_or_ne α 0 with rfl | hα
    · simp only [zero_smul, sub_zero, one_mulVec]
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simp
      · have : NeZero n := ⟨hn.ne'⟩
        rw [(theorem_4_7_zero (A := A) hA.diagPart.isUnit).2, ENNReal.toReal_one, one_pow,
          one_mul]
    · have h := Splitting.energyNorm_preconditionedRichardson_mulVec_le hA Matrix.PosDef.one hα e
      rwa [inv_one, Matrix.one_mul] at h

/-- **Corollary 4.1** of [quarteroni2000numerical], the preconditioned method. Let
$A, P \in \mathbb{R}^{n \times n}$ be symmetric positive definite, let $\alpha \neq 0$ and
$R_\alpha = I - \alpha P^{-1} A$. Then the estimate (4.30) holds for the preconditioned method:
$$\|R_\alpha e\|_A^2 \le \rho(R_\alpha)^2 \|e\|_A^2 \quad \text{for every } e \in
  \mathbb{R}^n.$$

**Generalization.** The corollary also asks $P^{-1}A$ to be symmetric positive definite, and
$P^{-1}A$ is symmetric only when $P$ and $A$ commute. The estimate needs only $P$ and $A$
symmetric positive definite, as the closing sentence of the corollary in the source says.

The proof is `Stationary.Splitting.energyNorm_preconditionedRichardson_mulVec_le`: $R_\alpha$ is
self-adjoint for the $A$-inner product, because $AR_\alpha = A - \alpha A P^{-1} A$ is
symmetric. -/
theorem corollary_4_1_preconditioned (hA : A.PosDef) (hP : P.PosDef) {α : ℝ} (hα : α ≠ 0)
    (e : Fin n → ℝ) :
    (A *ᵥ ((1 - α • (P⁻¹ * A)) *ᵥ e)) ⬝ᵥ ((1 - α • (P⁻¹ * A)) *ᵥ e) ≤
      (complexSpectralRadius (1 - α • (P⁻¹ * A))).toReal ^ 2 * ((A *ᵥ e) ⬝ᵥ e) :=
  Splitting.energyNorm_preconditionedRichardson_mulVec_le hA hP hα e

end Convergence

/-! ### §4.3.2 Preconditioning: Remark 4.2 and (4.33) -/

section Preconditioning

variable {A P : Matrix (Fin n) (Fin n) ℝ}

/-- **Remark 4.2** of [quarteroni2000numerical], equation (4.32). Let
$A, P \in \mathbb{R}^{n \times n}$ be symmetric, with $P$ positive definite. A complex number
$\lambda$ is an eigenvalue of $P^{-1} A$ if and only if the generalized eigenvalue problem
$Ax = \lambda Px$ has a solution $x \in \mathbb{C}^n$, $x \neq 0$. Every eigenvalue of $P^{-1}A$
is real. If $\lambda \in \mathbb{R}$ and $x \in \mathbb{R}^n$, $x \neq 0$, satisfy
$Ax = \lambda Px$, then $\lambda$ is the generalized Rayleigh quotient
$$\lambda = \frac{(Ax, x)}{(Px, x)}.$$

The real matrices act on $\mathbb{C}^n$ through `Matrix.complexify`. The first clause is
`Matrix.mem_spectrum_inv_mul_iff_exists_mulVec_eq_smul`, and the second is
`Matrix.pencilSpectrum_subset_range_ofReal_of_posDef` (Theorem 5.7 of the source). -/
theorem remark_4_2 (hA : A.IsHermitian) (hP : P.PosDef) :
    (∀ μ : ℂ, μ ∈ spectrum ℂ (complexify (P⁻¹ * A)) ↔
        ∃ x : Fin n → ℂ, x ≠ 0 ∧ complexify A *ᵥ x = μ • (complexify P *ᵥ x)) ∧
      (∀ μ ∈ spectrum ℂ (complexify (P⁻¹ * A)), μ.im = 0) ∧
      ∀ (μ : ℝ) (x : Fin n → ℝ), x ≠ 0 → A *ᵥ x = μ • (P *ᵥ x) →
        μ = ((A *ᵥ x) ⬝ᵥ x) / ((P *ᵥ x) ⬝ᵥ x) := by
  refine ⟨fun μ => mem_spectrum_inv_mul_iff_exists_mulVec_eq_smul A hP.isUnit μ,
    fun μ hμ => ?_, fun μ x hx hμ => ?_⟩
  · rw [complexify_mul, complexify_inv,
      ← pencilSpectrum_eq_spectrum_of_isUnit _ ((isUnit_complexify_iff P).mpr hP.isUnit)] at hμ
    obtain ⟨t, ht⟩ := pencilSpectrum_subset_range_ofReal_of_posDef
      ((isHermitian_complexify_iff A).mpr hA) (posDef_complexify_iff.mpr hP) hμ
    rw [← ht]
    exact Complex.ofReal_im t
  · have hpos : 0 < (P *ᵥ x) ⬝ᵥ x := by
      have := hP.dotProduct_mulVec_pos hx
      rwa [star_trivial, dotProduct_comm] at this
    rw [hμ, smul_dotProduct, smul_eq_mul, mul_div_cancel_right₀ _ hpos.ne']

/-- **Equation (4.33)** of [quarteroni2000numerical]. Let $A, P \in \mathbb{R}^{n \times n}$ be
symmetric with $P$ positive definite. Let $a \le \lambda_i(A) \le a'$ and
$p \le \lambda_i(P) \le p'$ for all eigenvalues $\lambda_i(A)$ of $A$ and $\lambda_i(P)$ of $P$,
with $0 \le a$ and $0 < p$. Then every eigenvalue $\lambda$ of $P^{-1} A$ is real and
$$\frac{a}{p'} \le \lambda \le \frac{a'}{p}.$$
The source states this for $a = \lambda_{\min}(A)$, $a' = \lambda_{\max}(A)$,
$p = \lambda_{\min}(P)$ and $p' = \lambda_{\max}(P)$.

**Reading.** The source does not state the sign of $\lambda_{\min}(A)$. The printed lower bound
presupposes $\lambda_{\min}(A) \ge 0$, as $A$ is positive definite in the context of the source,
and the declaration assumes $0 \le a$.

The eigenvalues are `Matrix.IsHermitian.eigenvalues`. The proof is
`Matrix.spectrum_inv_mul_subset_Icc_div`, which uses the generalized Rayleigh quotient of Remark
4.2 in place of the Courant–Fischer theorem. -/
theorem equation_4_33 (hA : A.IsHermitian) (hP : P.PosDef) {a a' p p' : ℝ}
    (haA : ∀ i, hA.eigenvalues i ∈ Set.Icc a a') (hpP : ∀ i, hP.1.eigenvalues i ∈ Set.Icc p p')
    (ha : 0 ≤ a) (hp : 0 < p) :
    spectrum ℂ (complexify (P⁻¹ * A)) ⊆ Complex.ofReal '' Set.Icc (a / p') (a' / p) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [spectrum.of_subsingleton]
    exact Set.empty_subset _
  have hA' := hA.isSymmetricBoundedBy_toEuclideanLin haA
  have hP' := hP.1.isSymmetricBoundedBy_toEuclideanLin hpP
  have hinner : ∀ (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ),
      RCLike.re (inner ℝ (toEuclideanLin M (toLp 2 x)) (toLp 2 x)) = (M *ᵥ x) ⬝ᵥ x := by
    intro M x
    rw [RCLike.re_to_real, toEuclideanLin_toLp, EuclideanSpace.inner_toLp_toLp, star_trivial,
      dotProduct_comm]
  have hnorm : ∀ x : Fin n → ℝ, ‖(toLp 2 x : EuclideanSpace ℝ (Fin n))‖ ^ 2 = x ⬝ᵥ x := by
    intro x
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp, star_trivial]
  have hp' : 0 < p' := by
    obtain ⟨h1, h2⟩ := hpP ⟨0, hn⟩
    exact hp.trans_le (h1.trans h2)
  refine spectrum_inv_mul_subset_Icc_div hA hP ha hp hp' (fun x => ?_) (fun x => ?_) (fun x => ?_)
    fun x => ?_
  · rw [← hinner, ← hnorm]; exact hA'.le_re_inner _
  · rw [← hinner, ← hnorm]; exact hA'.re_inner_le _
  · rw [← hinner, ← hnorm]; exact hP'.le_re_inner _
  · rw [← hinner, ← hnorm]; exact hP'.re_inner_le _

end Preconditioning

/-! ### §4.3.3 The gradient method -/

section Gradient

variable (A : Matrix (Fin n) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin n))

/-- **Section 4.3.3** of [quarteroni2000numerical], the energy of the system $Ax = b$. For
$A \in \mathbb{R}^{n \times n}$ and $b \in \mathbb{R}^n$, the **energy** is the quadratic
function
$$\Phi(y) = \frac12 y^T A y - y^T b, \qquad y \in \mathbb{R}^n.$$

It is the backbone's `energyFunctional (toEuclideanLin A) b`
(`QuarteroniSaccoSaleri.Chapter04.energy_eq_energyFunctional`). -/
noncomputable def energy (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  1 / 2 * inner ℝ (toEuclideanLin A y) y - inner ℝ y b

/-- The energy $\Phi$ of §4.3.3 is the backbone's energy functional
$y \mapsto \frac12 (Ay, y) - (b, y)$, that is `energyFunctional (toEuclideanLin A) b`. -/
theorem energy_eq_energyFunctional (y : EuclideanSpace ℝ (Fin n)) :
    energy A b y = energyFunctional (toEuclideanLin A) b y := by
  simp only [energy, energyFunctional, RCLike.re_to_real, real_inner_comm b y]
  ring

/-- The energy of $A$ equals the energy of its symmetric part $\frac12 (A^T + A)$. -/
private theorem energy_eq_energy_symm (y : EuclideanSpace ℝ (Fin n)) :
    energy A b y = energy ((1 / 2 : ℝ) • (Aᵀ + A)) b y := by
  have h : inner ℝ (toEuclideanLin Aᵀ y) y = inner ℝ (toEuclideanLin A y) y := by
    rw [← conjTranspose_eq_transpose_of_trivial, toEuclideanLin_conjTranspose_inner_left,
      real_inner_comm]
  simp only [energy, map_smul, map_add, LinearMap.smul_apply, LinearMap.add_apply, inner_smul_left,
    inner_add_left, h, RCLike.conj_to_real]
  ring

/-- **Equation (4.34)** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ and
$b \in \mathbb{R}^n$. The energy $\Phi$ has at every $y$ the gradient
$$\nabla \Phi(y) = \frac12 (A^T + A) y - b,$$
which is $Ay - b$ when $A$ is symmetric. Consequently a critical point $x$ of $\Phi$,
$\nabla \Phi(x) = Ax - b = 0$, solves the system $Ax = b$.

The gradient is Mathlib's `HasGradientAt` on `EuclideanSpace ℝ (Fin n)`. The proof uses
`hasGradientAt_energyFunctional_of_finiteDimensional`. -/
theorem equation_4_34 (y : EuclideanSpace ℝ (Fin n)) :
    HasGradientAt (energy A b) (toEuclideanLin ((1 / 2 : ℝ) • (Aᵀ + A)) y - b) y ∧
      (A.IsSymm → HasGradientAt (energy A b) (toEuclideanLin A y - b) y) ∧
      ∀ x, toEuclideanLin A x - b = 0 → toEuclideanLin A x = b := by
  have hgrad : ∀ M : Matrix (Fin n) (Fin n) ℝ, M.IsSymm →
      HasGradientAt (energy M b) (toEuclideanLin M y - b) y := fun M hM => by
    rw [funext (energy_eq_energyFunctional M b)]
    exact hasGradientAt_energyFunctional_of_finiteDimensional hM.isSymmetric_toEuclideanLin b y
  refine ⟨?_, hgrad A, fun x hx => sub_eq_zero.mp hx⟩
  rw [funext (energy_eq_energy_symm A b)]
  refine hgrad _ ?_
  rw [IsSymm, transpose_smul, transpose_add, transpose_transpose, add_comm]

/-- **Equation (4.35)** of [quarteroni2000numerical] and the display before it. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite and let $x$ solve $Ax = b$. Then
for every $y \in \mathbb{R}^n$
$$\Phi(y) = \Phi(x) + \frac12 (y - x)^T A (y - x),$$
that is $\frac12 \|y - x\|_A^2 = \Phi(y) - \Phi(x)$. Hence $\Phi(y) > \Phi(x)$ for every
$y \neq x$, and $x$ is the unique minimizer of the energy.

The energy norm is `energyNorm (toEuclideanLin A)`. The proof uses
`LinearMap.IsSymmetricCoercive.energyFunctional_sub_eq`. -/
theorem equation_4_35 (hA : A.PosDef) {x : EuclideanSpace ℝ (Fin n)} (hx : toEuclideanLin A x = b)
    (y : EuclideanSpace ℝ (Fin n)) :
    energy A b y = energy A b x + 1 / 2 * inner ℝ (toEuclideanLin A (y - x)) (y - x) ∧
      1 / 2 * energyNorm (toEuclideanLin A) (y - x) ^ 2 = energy A b y - energy A b x ∧
      (y ≠ x → energy A b x < energy A b y) := by
  have hA' := (posDef_iff_isSymmetricCoercive A).1 hA
  have h := hA'.energyFunctional_sub_eq hx y
  rw [← energy_eq_energyFunctional, ← energy_eq_energyFunctional] at h
  have hsq := hA'.energyNorm_sq (y - x)
  rw [RCLike.re_to_real] at hsq
  refine ⟨by rw [← hsq]; linarith, by linarith, fun hy => ?_⟩
  have := hA'.energyNorm_pos (sub_ne_zero.mpr hy)
  nlinarith

/-- **Equations (4.36)–(4.37)** of [quarteroni2000numerical], the gradient (steepest descent)
method. Let $A \in \mathbb{R}^{n \times n}$ and $b \in \mathbb{R}^n$. One step of the **gradient
method** takes the residual $r = b - Ax$ as the descent direction and maps $x$ to
$$x + \alpha r, \qquad \alpha = \frac{r^T r}{r^T A r}.$$
For symmetric positive definite $A$ this dynamic parameter $\alpha$ minimizes $\Phi$ along the
line through $x$ in the direction $r$.

The $k$-th iterate from $x^{(0)}$ is `(gradientStep A b)^[k] x₀`. If $r = 0$, the quotient is
$0/0$, which Lean evaluates as $0$, and the step leaves $x$ unchanged. The step is the
backbone's `Projection.steepestDescentStep` (`QuarteroniSaccoSaleri.Chapter04.gradientStep_eq`). -/
noncomputable def gradientStep (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  x + (inner ℝ (b - toEuclideanLin A x) (b - toEuclideanLin A x) /
    inner ℝ (b - toEuclideanLin A x) (toEuclideanLin A (b - toEuclideanLin A x))) •
      (b - toEuclideanLin A x)

/-- The gradient step of (4.37) is the backbone's steepest-descent step
`Projection.steepestDescentStep (toEuclideanLin A) b`. -/
theorem gradientStep_eq (x : EuclideanSpace ℝ (Fin n)) :
    gradientStep A b x = Projection.steepestDescentStep (toEuclideanLin A) b x := rfl

/-- **Equation (4.37)** of [quarteroni2000numerical], the sentence after it. The gradient method is
the nonstationary Richardson method (4.24) with $P = I$ and the parameters
$$\alpha_j = \frac{r^{(j)T} r^{(j)}}{r^{(j)T} A r^{(j)}}, \qquad r^{(j)} = b - Ax^{(j)},$$
computed along its own iterates $x^{(j)}$. That is, for every $x^{(0)}$ and every $k$, the
$k$-th gradient iterate is the $k$-th iterate of the backbone's `Richardson.iterate` with
$P^{-1} = I$ and these parameters, and it is also the $k$-th iterate of
`QuarteroniSaccoSaleri.Chapter04.nonstationaryRichardson A 1` on coordinates.

The first identity is `Richardson.iterate_gradient_eq_steepestDescentStep`, and the second
follows from `QuarteroniSaccoSaleri.Chapter04.toLp_nonstationaryRichardson`. The coordinate
vectors of $b$ and $x^{(0)}$ are `WithLp.ofLp b` and `WithLp.ofLp x₀`. -/
theorem equation_4_37 (x₀ : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    (gradientStep A b)^[k] x₀ = Richardson.iterate (toEuclideanLin A) LinearMap.id
        (fun j => inner ℝ (b - toEuclideanLin A ((gradientStep A b)^[j] x₀))
            (b - toEuclideanLin A ((gradientStep A b)^[j] x₀)) /
          inner ℝ (b - toEuclideanLin A ((gradientStep A b)^[j] x₀))
            (toEuclideanLin A (b - toEuclideanLin A ((gradientStep A b)^[j] x₀)))) b x₀ k ∧
      (gradientStep A b)^[k] x₀ = toLp 2 (nonstationaryRichardson A 1
        (fun j => inner ℝ (b - toEuclideanLin A ((gradientStep A b)^[j] x₀))
            (b - toEuclideanLin A ((gradientStep A b)^[j] x₀)) /
          inner ℝ (b - toEuclideanLin A ((gradientStep A b)^[j] x₀))
            (toEuclideanLin A (b - toEuclideanLin A ((gradientStep A b)^[j] x₀))))
        (ofLp b) (ofLp x₀) k) := by
  have h := Richardson.iterate_gradient_eq_steepestDescentStep (toEuclideanLin A) b
    (fun k => (gradientStep A b)^[k] x₀) (fun k => Function.iterate_succ_apply' _ _ _) k
  simp only [Function.iterate_zero, id_eq] at h
  refine ⟨h, ?_⟩
  rw [toLp_nonstationaryRichardson, inv_one, toEuclideanLin_one, WithLp.toLp_ofLp,
    WithLp.toLp_ofLp]
  exact h

/-- Let $n \ge 1$ and let $A \in \mathbb{R}^{n \times n}$ be symmetric. Then $A$ has extreme
eigenvalues $\lambda_{\min}$ and $\lambda_{\max}$: the real spectrum of $A$ lies in
$[\lambda_{\min}, \lambda_{\max}]$, both endpoints are eigenvalues, and all of
`Matrix.IsHermitian.eigenvalues` lie in $[\lambda_{\min}, \lambda_{\max}]$. This supplies the
hypotheses on the spectrum in Theorem 4.9 and Corollary 4.1. -/
theorem exists_extreme_eigenvalues [NeZero n] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) :
    ∃ lmin lmax : ℝ, spectrum ℝ A ⊆ Set.Icc lmin lmax ∧ lmin ∈ spectrum ℝ A ∧
      lmax ∈ spectrum ℝ A ∧ ∀ i, hA.eigenvalues i ∈ Set.Icc lmin lmax := by
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image univ hA.eigenvalues univ_nonempty
  obtain ⟨i₁, -, hi₁⟩ := Finset.exists_max_image univ hA.eigenvalues univ_nonempty
  have hIcc : ∀ i, hA.eigenvalues i ∈ Set.Icc (hA.eigenvalues i₀) (hA.eigenvalues i₁) :=
    fun i => ⟨hi₀ i (mem_univ i), hi₁ i (mem_univ i)⟩
  refine ⟨hA.eigenvalues i₀, hA.eigenvalues i₁, ?_, ?_, ?_, hIcc⟩
  · rw [hA.spectrum_real_eq_range_eigenvalues]
    rintro _ ⟨i, rfl⟩
    exact hIcc i
  · rw [hA.spectrum_real_eq_range_eigenvalues]
    exact ⟨i₀, rfl⟩
  · rw [hA.spectrum_real_eq_range_eigenvalues]
    exact ⟨i₁, rfl⟩

/-- Let $A \in \mathbb{R}^{n \times n}$ be symmetric positive definite, with real spectrum in
$[\lambda_{\min}, \lambda_{\max}]$ and both endpoints eigenvalues. Then the spectral condition
number of $A$ is
$$K_2(A) = \frac{\lambda_{\max}}{\lambda_{\min}}.$$
This is the sentence after Theorem 4.10.

The condition number is `NormedRing.condNumber A` for the spectral norm. The proof is
`Stationary.Splitting.condNumber_eq_div_of_spectrum`. -/
theorem condNumber_eq_div_of_posDef {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) {lmin lmax : ℝ}
    (hsub : spectrum ℝ A ⊆ Set.Icc lmin lmax) (hmin : lmin ∈ spectrum ℝ A)
    (hmax : lmax ∈ spectrum ℝ A) : κ A = lmax / lmin :=
  Splitting.condNumber_eq_div_of_spectrum hA.1 hsub hmin hmax
    (open scoped MatrixOrder in hA.isStrictlyPositive.spectrum_pos hmin)

/-- **Theorem 4.10** of [quarteroni2000numerical]. Let $n \ge 1$, let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite and let $x$ solve $Ax = b$. Then
the gradient method converges to $x$ for any initial datum $x^{(0)}$. Moreover, if $y'$ is the
gradient step from any $y \in \mathbb{R}^n$, then
$$\|x - y'\|_A \le \frac{K_2(A) - 1}{K_2(A) + 1} \|x - y\|_A,$$
where $K_2(A) = \lambda_{\max}/\lambda_{\min}$ is the spectral condition number. For
$y = x^{(k)}$ this is (4.38): $\|e^{(k+1)}\|_A \le \frac{K_2(A) - 1}{K_2(A) + 1} \|e^{(k)}\|_A$.

The one-step estimate is the backbone's `Projection.energyNorm_steepestDescentStep_le`. The
argument of the source is that the gradient step does at least as well in the $A$-norm as the
optimal Richardson step of Corollary 4.1. The convergence is
`Projection.tendsto_iterate_steepestDescentStep`. The condition number is
`NormedRing.condNumber A`. -/
theorem theorem_4_10 [NeZero n] (hA : A.PosDef) {x : EuclideanSpace ℝ (Fin n)}
    (hx : toEuclideanLin A x = b) :
    (∀ x₀, Tendsto (fun k => (gradientStep A b)^[k] x₀) atTop (𝓝 x)) ∧
      ∀ y, energyNorm (toEuclideanLin A) (x - gradientStep A b y) ≤
        (κ A - 1) / (κ A + 1) * energyNorm (toEuclideanLin A) (x - y) := by
  obtain ⟨lmin, lmax, hsub, hmin, hmax, hIcc⟩ := exists_extreme_eigenvalues hA.1
  have hpos : 0 < lmin := (open scoped MatrixOrder in hA.isStrictlyPositive.spectrum_pos hmin)
  have hB := hA.1.isSymmetricBoundedBy_toEuclideanLin hIcc
  have hκ : (κ A - 1) / (κ A + 1) = (lmax - lmin) / (lmax + lmin) := by
    rw [condNumber_eq_div_of_posDef hA hsub hmin hmax]
    field_simp
  exact ⟨fun x₀ => Projection.tendsto_iterate_steepestDescentStep hpos hB hx x₀,
    fun y => hκ ▸ Projection.energyNorm_steepestDescentStep_le hpos hB hx y⟩

end Gradient

/-! ### §4.3.4 The conjugate gradient method -/

section ConjugateGradient

variable (A : Matrix (Fin n) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin n))

/-- **Definition 4.4** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ and
$b \in \mathbb{R}^n$, with the energy $\Phi$. A point $x \in \mathbb{R}^n$ is **optimal with
respect to the direction** $p \in \mathbb{R}^n$ if (4.40) holds:
$$\Phi(x) \le \Phi(x + \lambda p) \quad \text{for every } \lambda \in \mathbb{R}.$$

**Typo.** The source writes "direction $x^{(k)}$" for the point $x^{(k)}$.

**Generalization.** The source assumes $p \neq 0$. The definition does not, and no result below
needs it.

The energy $\Phi$ is `QuarteroniSaccoSaleri.Chapter04.energy A b`. -/
def definition_4_4 (x p : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ t : ℝ, energy A b x ≤ energy A b (x + t • p)

/-- **Definition 4.4** of [quarteroni2000numerical], the second sentence. A point
$x \in \mathbb{R}^n$ is **optimal with respect to a vector space** $V \subseteq \mathbb{R}^n$ if
it is optimal with respect to every direction $p \in V$. -/
def IsOptimalWrtSubspace (x : EuclideanSpace ℝ (Fin n))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ p ∈ V, definition_4_4 A b x p

variable {A b}

/-- **Section 4.3.4** of [quarteroni2000numerical], the displays after Definition 4.4. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite, let
$x, p, x^{(0)} \in \mathbb{R}^n$, let $V$ be a subspace of $\mathbb{R}^n$, and let $r = b - Ax$.
Then $x$ is optimal with respect to $p$ if and only if $p^T r = 0$, and $x$ is optimal with
respect to $V$ if and only if $r \in V^\perp$. If moreover $x \in x^{(0)} + V$, then $x$ is
optimal with respect to $V$ if and only if $x$ satisfies the Galerkin condition for $V$:
$x - x^{(0)} \in V$ and $r \perp V$.

The first equivalence holds because $\frac{\partial \Phi}{\partial \lambda}(x + \lambda p) = p^T
(Ax - b) + \lambda p^T A p$ vanishes at $\lambda = 0$ exactly when $p^T r = 0$
(`inner_residual_eq_zero_iff_forall_quadratic_add_smul_le`). The Galerkin condition is the
backbone's `IsGalerkin (toEuclideanLin A) b x₀ V x`, which the proof of Theorem 4.11 uses. -/
theorem definition_4_4_iff (hA : A.PosDef) (x p : EuclideanSpace ℝ (Fin n))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (x₀ : EuclideanSpace ℝ (Fin n)) :
    (definition_4_4 A b x p ↔ inner ℝ p (b - toEuclideanLin A x) = 0) ∧
      (IsOptimalWrtSubspace A b x V ↔ b - toEuclideanLin A x ∈ Vᗮ) ∧
      (x - x₀ ∈ V → (IsOptimalWrtSubspace A b x V ↔ IsGalerkin (toEuclideanLin A) b x₀ V x)) := by
  have hA' := (posDef_iff_isSymmetricCoercive A).1 hA
  have hdir : ∀ p, definition_4_4 A b x p ↔ inner ℝ p (b - toEuclideanLin A x) = 0 := by
    intro p
    rw [definition_4_4, real_inner_comm,
      inner_residual_eq_zero_iff_forall_quadratic_add_smul_le hA'.isSymmetric
        (hA'.isPositive.re_inner_nonneg_left p) b x]
    simp only [energy_eq_energyFunctional]
  have hsub : IsOptimalWrtSubspace A b x V ↔ b - toEuclideanLin A x ∈ Vᗮ := by
    rw [Submodule.mem_orthogonal]
    exact forall₂_congr fun p _ => hdir p
  exact ⟨hdir p, hsub, fun hmem => ⟨fun h => ⟨hmem, hsub.1 h⟩, fun h => hsub.2 h.orth⟩⟩

/-- **Section 4.3.4** of [quarteroni2000numerical], the display $0 = p^T r^{(k+1)} = p^T (r^{(k)} -
Aq) = -p^T A q$. Let $A \in \mathbb{R}^{n \times n}$ be symmetric positive definite, let $x$ be
optimal with respect to $p$, and let $q \in \mathbb{R}^n$. Then $x + q$ is optimal with respect
to $p$ if and only if $p^T A q = 0$. Hence the descent directions must be $A$-orthogonal, or
$A$-conjugate, to preserve optimality. -/
theorem optimal_preserved_iff_conjugate (hA : A.PosDef) {x p : EuclideanSpace ℝ (Fin n)}
    (hx : definition_4_4 A b x p) (q : EuclideanSpace ℝ (Fin n)) :
    definition_4_4 A b (x + q) p ↔ inner ℝ p (toEuclideanLin A q) = 0 := by
  rw [(definition_4_4_iff hA x p ⊥ 0).1] at hx
  rw [(definition_4_4_iff hA (x + q) p ⊥ 0).1, map_add, sub_add_eq_sub_sub, inner_sub_right, hx,
    zero_sub, neg_eq_zero]

variable (A b)

/-- **Equation (4.39)** of [quarteroni2000numerical]. On a state $(x, r, p)$ of the conjugate
gradient method, the step length is
$$\alpha = \frac{p^T r}{p^T A p}.$$
When $r = b - Ax$ and $A$ is symmetric positive definite, this $\alpha$ minimizes
$\Phi(x + \alpha p)$.

The state is the backbone's record `CG.State`. If $p^T A p = 0$, Lean gives $\alpha = 0$. -/
noncomputable def cgAlphaStep (s : CG.State (EuclideanSpace ℝ (Fin n))) : ℝ :=
  inner ℝ s.p s.r / inner ℝ s.p (toEuclideanLin A s.p)

/-- **Equations (4.39)–(4.41)** of [quarteroni2000numerical], the conjugate gradient iteration. One
step maps the state $(x^{(k)}, r^{(k)}, p^{(k)})$ to $(x^{(k+1)}, r^{(k+1)}, p^{(k+1)})$, where
$$\alpha_k = \frac{p^{(k)T} r^{(k)}}{p^{(k)T} A p^{(k)}}, \qquad x^{(k+1)} = x^{(k)} + \alpha_k
  p^{(k)}, \qquad r^{(k+1)} = r^{(k)} - \alpha_k A p^{(k)},$$
$$\beta_k = \frac{(A p^{(k)})^T r^{(k+1)}}{(A p^{(k)})^T p^{(k)}}, \qquad p^{(k+1)} =
  r^{(k+1)} - \beta_k p^{(k)}.$$

The direction update has the minus sign of the source, so that this $\beta_k$ is the negative of
the backbone's `CG.beta`. The state type is the backbone's record `CG.State`, and
`QuarteroniSaccoSaleri.Chapter04.cg_eq_CG` identifies the iteration with `CG.step`. A quotient
with zero denominator is $0$. -/
noncomputable def cgStep (s : CG.State (EuclideanSpace ℝ (Fin n))) :
    CG.State (EuclideanSpace ℝ (Fin n)) :=
  let α := cgAlphaStep A s
  let r' := s.r - α • toEuclideanLin A s.p
  let β := inner ℝ (toEuclideanLin A s.p) r' / inner ℝ (toEuclideanLin A s.p) s.p
  { x := s.x + α • s.p, r := r', p := r' - β • s.p }

/-- **Equation (4.41)** of [quarteroni2000numerical]. On a state $(x, r, p)$, the coefficient
$$\beta = \frac{(Ap)^T r'}{(Ap)^T p},$$
where $r'$ is the residual after one step of `QuarteroniSaccoSaleri.Chapter04.cgStep`. -/
noncomputable def cgBetaStep (s : CG.State (EuclideanSpace ℝ (Fin n))) : ℝ :=
  inner ℝ (toEuclideanLin A s.p) (cgStep A s).r / inner ℝ (toEuclideanLin A s.p) s.p

/-- **Section 4.3.4** of [quarteroni2000numerical], the **conjugate gradient method**. Start from
$x^{(0)}$ with $r^{(0)} = b - Ax^{(0)}$ and $p^{(0)} = r^{(0)}$. Then `cg A b x₀ k` is the state
$(x^{(k)}, r^{(k)}, p^{(k)})$ after $k$ steps of `QuarteroniSaccoSaleri.Chapter04.cgStep`. -/
noncomputable def cg (x₀ : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    CG.State (EuclideanSpace ℝ (Fin n)) :=
  (cgStep A)^[k] { x := x₀, r := b - toEuclideanLin A x₀, p := b - toEuclideanLin A x₀ }

variable (x₀ : EuclideanSpace ℝ (Fin n))

/-- The $k$-th iterate $x^{(k)}$ of the conjugate gradient method of §4.3.4. -/
noncomputable def cgX (k : ℕ) : EuclideanSpace ℝ (Fin n) := (cg A b x₀ k).x

/-- The $k$-th residual $r^{(k)}$ of the conjugate gradient method of §4.3.4. -/
noncomputable def cgR (k : ℕ) : EuclideanSpace ℝ (Fin n) := (cg A b x₀ k).r

/-- The $k$-th descent direction $p^{(k)}$ of the conjugate gradient method of §4.3.4. -/
noncomputable def cgP (k : ℕ) : EuclideanSpace ℝ (Fin n) := (cg A b x₀ k).p

/-- The step length $\alpha_k$ of (4.39) at step $k$ of the conjugate gradient method. -/
noncomputable def cgAlpha (k : ℕ) : ℝ := cgAlphaStep A (cg A b x₀ k)

/-- The coefficient $\beta_k$ of (4.41) at step $k$ of the conjugate gradient method, with the sign
of the source. -/
noncomputable def cgBeta (k : ℕ) : ℝ := cgBetaStep A (cg A b x₀ k)

/-- The state of the conjugate gradient method after $k + 1$ steps is one step of
`QuarteroniSaccoSaleri.Chapter04.cgStep` from the state after $k$ steps. -/
theorem cg_succ (k : ℕ) : cg A b x₀ (k + 1) = cgStep A (cg A b x₀ k) :=
  Function.iterate_succ_apply' _ _ _

/-- The conjugate gradient method starts at $x^{(0)}$. -/
@[simp] theorem cgX_zero : cgX A b x₀ 0 = x₀ := rfl

/-- The initial residual of the conjugate gradient method is $r^{(0)} = b - Ax^{(0)}$. -/
@[simp] theorem cgR_zero : cgR A b x₀ 0 = b - toEuclideanLin A x₀ := rfl

/-- The initial direction of the conjugate gradient method is $p^{(0)} = r^{(0)}$. -/
@[simp] theorem cgP_zero : cgP A b x₀ 0 = cgR A b x₀ 0 := rfl

/-- **Equation (4.39)** of [quarteroni2000numerical]. The step length of the conjugate gradient
method is
$$\alpha_k = \frac{p^{(k)T} r^{(k)}}{p^{(k)T} A p^{(k)}}.$$
-/
theorem cgAlpha_eq (k : ℕ) : cgAlpha A b x₀ k =
    inner ℝ (cgP A b x₀ k) (cgR A b x₀ k) /
      inner ℝ (cgP A b x₀ k) (toEuclideanLin A (cgP A b x₀ k)) :=
  rfl

/-- The conjugate gradient iterates satisfy $x^{(k+1)} = x^{(k)} + \alpha_k p^{(k)}$. -/
theorem cgX_succ (k : ℕ) :
    cgX A b x₀ (k + 1) = cgX A b x₀ k + cgAlpha A b x₀ k • cgP A b x₀ k := by
  rw [cgX, cg_succ]
  rfl

/-- The conjugate gradient residuals satisfy $r^{(k+1)} = r^{(k)} - \alpha_k A p^{(k)}$. -/
theorem cgR_succ (k : ℕ) :
    cgR A b x₀ (k + 1) = cgR A b x₀ k - cgAlpha A b x₀ k • toEuclideanLin A (cgP A b x₀ k) := by
  rw [cgR, cg_succ]
  rfl

/-- The coefficient of (4.41) is
$$\beta_k = \frac{(A p^{(k)})^T r^{(k+1)}}{(A p^{(k)})^T p^{(k)}}.$$
-/
theorem cgBeta_eq (k : ℕ) : cgBeta A b x₀ k =
    inner ℝ (toEuclideanLin A (cgP A b x₀ k)) (cgR A b x₀ (k + 1)) /
      inner ℝ (toEuclideanLin A (cgP A b x₀ k)) (cgP A b x₀ k) := by
  rw [cgBeta, cgBetaStep, cgR, cg_succ]
  rfl

/-- **Equation (4.41)** of [quarteroni2000numerical]. The conjugate gradient directions satisfy
$p^{(k+1)} = r^{(k+1)} - \beta_k p^{(k)}$. -/
theorem cgP_succ (k : ℕ) :
    cgP A b x₀ (k + 1) = cgR A b x₀ (k + 1) - cgBeta A b x₀ k • cgP A b x₀ k := by
  rw [cgP, cg_succ, cgBeta_eq, cgR, cg_succ]
  rfl

variable {A b x₀}

/-- A symmetric positive definite matrix $A \in \mathbb{R}^{n \times n}$ acts on
`EuclideanSpace ℝ (Fin n)` as a symmetric coercive operator, in the sense of
`LinearMap.IsSymmetricCoercive`. -/
theorem posDef_isSymmetricCoercive_toEuclideanLin (hA : A.PosDef) :
    (toEuclideanLin A).IsSymmetricCoercive :=
  (posDef_iff_isSymmetricCoercive A).1 hA

/-- On the backbone's conjugate gradient iterates, the step length (4.39) is `CG.alpha`, because
$p^{(k)T} r^{(k)} = \|r^{(k)}\|^2$ (`CG.inner_residual_direction_eq`). -/
private theorem cgAlphaStep_iterate (hA : A.PosDef) (k : ℕ) :
    cgAlphaStep A (CG.iterate (toEuclideanLin A) b x₀ k) =
      CG.alpha (toEuclideanLin A) (CG.iterate (toEuclideanLin A) b x₀ k) := by
  have h := CG.inner_residual_direction_eq b x₀ (posDef_isSymmetricCoercive_toEuclideanLin hA)
    (le_refl k)
  rw [RCLike.ofReal_real_eq_id, id_eq] at h
  rw [cgAlphaStep, CG.alpha, real_inner_comm (CG.iterate (toEuclideanLin A) b x₀ k).r, h,
    real_inner_self_eq_norm_sq,
    real_inner_comm (toEuclideanLin A (CG.iterate (toEuclideanLin A) b x₀ k).p)]

/-- On the backbone's conjugate gradient iterates, one step of
`QuarteroniSaccoSaleri.Chapter04.cgStep` produces the backbone's next residual. -/
private theorem cgStep_r_iterate (hA : A.PosDef) (k : ℕ) :
    (cgStep A (CG.iterate (toEuclideanLin A) b x₀ k)).r =
      (CG.iterate (toEuclideanLin A) b x₀ (k + 1)).r := by
  rw [CG.iterate_succ_r, cgStep, cgAlphaStep_iterate hA]

/-- On the backbone's conjugate gradient iterates, the coefficient $\beta_k$ of (4.41) is the
negative of `CG.beta`, by the computation $(Ap^{(k)})^T r^{(k+1)} = -\|r^{(k+1)}\|^2/\alpha_k$
and $(Ap^{(k)})^T p^{(k)} = \|r^{(k)}\|^2/\alpha_k$ of the solution of Exercise 13. -/
private theorem cgBetaStep_iterate (hA : A.PosDef) (k : ℕ) :
    cgBetaStep A (CG.iterate (toEuclideanLin A) b x₀ k) =
      -CG.beta (toEuclideanLin A) (CG.iterate (toEuclideanLin A) b x₀ k) := by
  have hA' := posDef_isSymmetricCoercive_toEuclideanLin hA
  rw [cgBetaStep, cgStep_r_iterate hA, CG.beta_iterate]
  rcases eq_or_ne (CG.iterate (toEuclideanLin A) b x₀ k).r 0 with hr | hr
  · have hp : (CG.iterate (toEuclideanLin A) b x₀ k).p = 0 :=
      CG.direction_eq_zero_of_residual_eq_zero _ b x₀ hr
    have hr' : (CG.iterate (toEuclideanLin A) b x₀ (k + 1)).r = 0 :=
      CG.residual_succ_eq_zero_of_eq_zero _ b x₀ hr
    rw [hp, hr, hr']
    simp
  · have hα := CG.alpha_smul_apply_direction (toEuclideanLin A) b x₀ k
    have hpos := CG.re_inner_apply_direction_pos b x₀ hA' hr
    rw [RCLike.re_to_real] at hpos
    have hrpos : 0 < inner ℝ (CG.iterate (toEuclideanLin A) b x₀ k).r
        (CG.iterate (toEuclideanLin A) b x₀ k).r := real_inner_self_pos.mpr hr
    have hαne : CG.alpha (toEuclideanLin A) (CG.iterate (toEuclideanLin A) b x₀ k) ≠ 0 := by
      rw [CG.alpha]
      exact div_ne_zero hrpos.ne' hpos.ne'
    have hAp : toEuclideanLin A (CG.iterate (toEuclideanLin A) b x₀ k).p =
        (CG.alpha (toEuclideanLin A) (CG.iterate (toEuclideanLin A) b x₀ k))⁻¹ •
          ((CG.iterate (toEuclideanLin A) b x₀ k).r -
            (CG.iterate (toEuclideanLin A) b x₀ (k + 1)).r) := by
      rw [← hα, smul_smul, inv_mul_cancel₀ hαne, one_smul]
    have h1 : inner ℝ (CG.iterate (toEuclideanLin A) b x₀ k).r
        (CG.iterate (toEuclideanLin A) b x₀ (k + 1)).r = 0 :=
      CG.inner_residual_eq_zero b x₀ hA' (Nat.ne_of_lt (Nat.lt_succ_self k))
    have h2 : inner ℝ (CG.iterate (toEuclideanLin A) b x₀ (k + 1)).r
        (CG.iterate (toEuclideanLin A) b x₀ k).p = 0 :=
      CG.inner_residual_direction_eq_zero b x₀ hA' (Nat.lt_succ_self k)
    have h3 : inner ℝ (CG.iterate (toEuclideanLin A) b x₀ k).r
        (CG.iterate (toEuclideanLin A) b x₀ k).p =
          ‖(CG.iterate (toEuclideanLin A) b x₀ k).r‖ ^ 2 := by
      have := CG.inner_residual_direction_eq b x₀ hA' (le_refl k)
      rwa [RCLike.ofReal_real_eq_id, id_eq] at this
    rw [hAp, inner_smul_left, inner_smul_left, inner_sub_left, inner_sub_left, h1, h2, h3,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, RCLike.conj_to_real]
    have hn : ‖(CG.iterate (toEuclideanLin A) b x₀ k).r‖ ≠ 0 := norm_ne_zero_iff.mpr hr
    field_simp
    ring

/-- On the backbone's conjugate gradient iterates, `QuarteroniSaccoSaleri.Chapter04.cgStep` is the
backbone's `CG.step`. -/
private theorem cgStep_iterate (hA : A.PosDef) (k : ℕ) :
    cgStep A (CG.iterate (toEuclideanLin A) b x₀ k) =
      CG.step (toEuclideanLin A) (CG.iterate (toEuclideanLin A) b x₀ k) := by
  have hβ := cgBetaStep_iterate hA (b := b) (x₀ := x₀) k
  have hr := cgStep_r_iterate hA (b := b) (x₀ := x₀) k
  rw [cgBetaStep] at hβ
  set s := CG.iterate (toEuclideanLin A) b x₀ k with hs
  refine CG.State.ext ?_ ?_ ?_
  · rw [CG.step_x, cgStep, cgAlphaStep_iterate hA]
  · rw [CG.step_r, cgStep, cgAlphaStep_iterate hA]
  · rw [CG.step_p, ← CG.iterate_succ, ← hr]
    change (cgStep A s).r - (inner ℝ (toEuclideanLin A s.p) (cgStep A s).r /
      inner ℝ (toEuclideanLin A s.p) s.p) • s.p = _
    rw [hβ, neg_smul, sub_neg_eq_add]

/-- Let $A \in \mathbb{R}^{n \times n}$ be symmetric positive definite. For every $k$, the state of
the conjugate gradient method of §4.3.4 after $k$ steps is the backbone's state
`CG.iterate (toEuclideanLin A) b x₀ k`, the step length of (4.39) is `CG.alpha` of that state,
and the coefficient of (4.41) is the negative of `CG.beta` of that state. All results on the
method in this module are read off this identification.

The step lengths agree because $p^{(k)T} r^{(k)} = \|r^{(k)}\|^2$
(`CG.inner_residual_direction_eq`). The coefficients agree up to sign by the computation of
Exercise 13 (see `QuarteroniSaccoSaleri.Chapter04.equation_4_45`). -/
theorem cg_eq_CG (hA : A.PosDef) (k : ℕ) :
    cg A b x₀ k = CG.iterate (toEuclideanLin A) b x₀ k ∧
      cgAlpha A b x₀ k = CG.alpha (toEuclideanLin A) (CG.iterate (toEuclideanLin A) b x₀ k) ∧
      cgBeta A b x₀ k = -CG.beta (toEuclideanLin A) (CG.iterate (toEuclideanLin A) b x₀ k) := by
  have hcg : cg A b x₀ k = CG.iterate (toEuclideanLin A) b x₀ k := by
    induction k with
    | zero => rfl
    | succ k ih => rw [cg_succ, ih, cgStep_iterate hA, CG.iterate_succ]
  exact ⟨hcg, by rw [cgAlpha, hcg, cgAlphaStep_iterate hA],
    by rw [cgBeta, hcg, cgBetaStep_iterate hA]⟩

/-- Let $A$ be symmetric positive definite. The conjugate gradient iterate $x^{(k)}$ is the `x`
component of the backbone's state `CG.iterate (toEuclideanLin A) b x₀ k`. -/
theorem cgX_eq_CG (hA : A.PosDef) (k : ℕ) :
    cgX A b x₀ k = (CG.iterate (toEuclideanLin A) b x₀ k).x := by
  rw [cgX, (cg_eq_CG hA k).1]

/-- Let $A$ be symmetric positive definite. The conjugate gradient residual $r^{(k)}$ is the `r`
component of the backbone's state `CG.iterate (toEuclideanLin A) b x₀ k`. -/
theorem cgR_eq_CG (hA : A.PosDef) (k : ℕ) :
    cgR A b x₀ k = (CG.iterate (toEuclideanLin A) b x₀ k).r := by
  rw [cgR, (cg_eq_CG hA k).1]

/-- Let $A$ be symmetric positive definite. The conjugate gradient direction $p^{(k)}$ is the `p`
component of the backbone's state `CG.iterate (toEuclideanLin A) b x₀ k`. -/
theorem cgP_eq_CG (hA : A.PosDef) (k : ℕ) :
    cgP A b x₀ k = (CG.iterate (toEuclideanLin A) b x₀ k).p := by
  rw [cgP, (cg_eq_CG hA k).1]

/-- Let $A$ be symmetric positive definite. The residual $r^{(k)}$ carried by the conjugate gradient
method is the true residual $b - Ax^{(k)}$. -/
theorem cgR_eq_residual (hA : A.PosDef) (k : ℕ) :
    cgR A b x₀ k = b - toEuclideanLin A (cgX A b x₀ k) := by
  rw [cgR_eq_CG hA, cgX_eq_CG hA, CG.residual_eq]

/-- **Equation (4.42)** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ be
symmetric positive definite. The descent directions of the conjugate gradient method are
$A$-conjugate:
$$(A p^{(j)})^T p^{(k+1)} = 0 \quad \text{for } j = 0, \dots, k,$$
and more generally $(A p^{(i)})^T p^{(j)} = 0$ for all $i \neq j$.

The induction of the source is the backbone's `CG.inner_apply_direction_eq_zero`. -/
theorem equation_4_42 (hA : A.PosDef) :
    (∀ k, ∀ j ≤ k, inner ℝ (toEuclideanLin A (cgP A b x₀ j)) (cgP A b x₀ (k + 1)) = 0) ∧
      ∀ i j, i ≠ j → inner ℝ (toEuclideanLin A (cgP A b x₀ i)) (cgP A b x₀ j) = 0 := by
  have h : ∀ i j, i ≠ j → inner ℝ (toEuclideanLin A (cgP A b x₀ i)) (cgP A b x₀ j) = 0 := by
    intro i j hij
    rw [cgP_eq_CG hA, cgP_eq_CG hA]
    exact CG.inner_apply_direction_eq_zero b x₀ (posDef_isSymmetricCoercive_toEuclideanLin hA) hij
  exact ⟨fun k j hj => h j (k + 1) (by omega), h⟩

/-- **Equations (4.43)–(4.44)** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ be
symmetric positive definite. The conjugate gradient residual $r^{(k)}$ is orthogonal to the
earlier directions, $p^{(j)T} r^{(k)} = 0$ for $j < k$, and hence to their span $V_k =
\operatorname{span}(p^{(0)}, \dots, p^{(k-1)})$. For every $k$, the space $V_k$ equals
$\operatorname{span}(r^{(0)}, \dots, r^{(k-1)})$ and the Krylov subspace $K_k(A; r^{(0)})$ of
§4.4. The residuals are mutually orthogonal: $r^{(i)T} r^{(j)} = 0$ for $i \neq j$.

The Krylov subspace is `Krylov.subspace (toEuclideanLin A) (b - toEuclideanLin A x₀) k`. The
four clauses are the backbone's `CG.inner_residual_direction_eq_zero`, `CG.span_direction_eq`,
`CG.span_residual_eq` and `CG.inner_residual_eq_zero`. -/
theorem equation_4_44 (hA : A.PosDef) :
    (∀ k j, j < k → inner ℝ (cgP A b x₀ j) (cgR A b x₀ k) = 0) ∧
      (∀ k, Submodule.span ℝ (Set.range fun i : Fin k => cgP A b x₀ i) =
        Krylov.subspace (toEuclideanLin A) (b - toEuclideanLin A x₀) k) ∧
      (∀ k, Submodule.span ℝ (Set.range fun i : Fin k => cgR A b x₀ i) =
        Krylov.subspace (toEuclideanLin A) (b - toEuclideanLin A x₀) k) ∧
      ∀ i j, i ≠ j → inner ℝ (cgR A b x₀ i) (cgR A b x₀ j) = 0 := by
  have hA' := (posDef_isSymmetricCoercive_toEuclideanLin hA)
  simp only [cgP_eq_CG hA, cgR_eq_CG hA]
  exact ⟨fun k j hj => by
      rw [real_inner_comm]; exact CG.inner_residual_direction_eq_zero b x₀ hA' hj,
    CG.span_direction_eq b x₀ hA', CG.span_residual_eq b x₀ hA',
    fun i j hij => CG.inner_residual_eq_zero b x₀ hA' hij⟩

/-- **Equation (4.45)** of [quarteroni2000numerical] and Exercise 13. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite. For every $k$ the parameters of
the conjugate gradient method satisfy
$$\alpha_k = \frac{\|r^{(k)}\|^2}{p^{(k)T} A p^{(k)}}, \qquad \beta_k =
  -\frac{\|r^{(k+1)}\|^2}{\|r^{(k)}\|^2}.$$

**Correction.** The source prints $\beta_k = \|r^{(k+1)}\|^2 / \|r^{(k)}\|^2$. With the update
$p^{(k+1)} = r^{(k+1)} - \beta_k p^{(k)}$ of (4.41) the sign is negative, because $(A p^{(k)})^T
r^{(k+1)} = -\|r^{(k+1)}\|^2/\alpha_k$ and $\alpha_k (A p^{(k)})^T p^{(k)} = \|r^{(k)}\|^2$. The
solution of Exercise 13 prints a minus sign in the second identity, which compensates.

Both identities hold at every step: when a residual vanishes, both sides are $0$, since Lean
evaluates a quotient $t/0$ as $0$. -/
theorem equation_4_45 (hA : A.PosDef) (k : ℕ) :
    cgAlpha A b x₀ k =
        ‖cgR A b x₀ k‖ ^ 2 / inner ℝ (cgP A b x₀ k) (toEuclideanLin A (cgP A b x₀ k)) ∧
      cgBeta A b x₀ k = -(‖cgR A b x₀ (k + 1)‖ ^ 2 / ‖cgR A b x₀ k‖ ^ 2) := by
  obtain ⟨-, hα, hβ⟩ := cg_eq_CG (b := b) (x₀ := x₀) hA k
  constructor
  · rw [hα, CG.alpha, cgR_eq_CG hA, cgP_eq_CG hA, real_inner_self_eq_norm_sq, real_inner_comm]
  · rw [hβ, CG.beta_iterate, cgR_eq_CG hA, cgR_eq_CG hA, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq]

/-- Let $A$ be symmetric positive definite. If $r^{(k)} \neq 0$, then the conjugate gradient step
length satisfies $\alpha_k \neq 0$, because $\alpha_k = \|r^{(k)}\|^2 / p^{(k)T} A p^{(k)}$ with
$p^{(k)T} A p^{(k)} > 0$ (`CG.re_inner_apply_direction_pos`). -/
theorem cgAlpha_ne_zero (hA : A.PosDef) {k : ℕ} (hr : cgR A b x₀ k ≠ 0) :
    cgAlpha A b x₀ k ≠ 0 := by
  rw [(equation_4_45 hA k).1]
  have hpos := CG.re_inner_apply_direction_pos b x₀ (posDef_isSymmetricCoercive_toEuclideanLin hA)
    (cgR_eq_CG hA k ▸ hr)
  rw [RCLike.re_to_real, ← cgP_eq_CG hA, real_inner_comm] at hpos
  exact div_ne_zero (pow_ne_zero 2 (norm_ne_zero_iff.mpr hr)) hpos.ne'

/-- Let $A$ be symmetric positive definite. If the conjugate gradient residual $r^{(k)}$ vanishes,
then $r^{(k+1)} = 0$ (`CG.residual_succ_eq_zero_of_eq_zero`). -/
theorem cgR_succ_eq_zero_of_eq_zero (hA : A.PosDef) {k : ℕ} (hr : cgR A b x₀ k = 0) :
    cgR A b x₀ (k + 1) = 0 := by
  rw [cgR_eq_CG hA] at hr ⊢
  exact CG.residual_succ_eq_zero_of_eq_zero _ b x₀ hr

/-- **Equation (4.46)** of [quarteroni2000numerical] and Exercise 14, the three-term recurrence of
the residuals. Let $A \in \mathbb{R}^{n \times n}$ be symmetric positive definite, let $k \ge 1$
and let $r^{(k)} \neq 0$. Then the conjugate gradient residuals satisfy
$$A r^{(k)} = -\frac{1}{\alpha_k} r^{(k+1)} + \Big(\frac{1}{\alpha_k} -
  \frac{\beta_{k-1}}{\alpha_{k-1}}\Big) r^{(k)} + \frac{\beta_{k-1}}{\alpha_{k-1}} r^{(k-1)}.$$

**Typo.** The source prints $\beta_k/\alpha_{k-1}$ for the coefficient of $r^{(k-1)}$. The
coefficient is $\beta_{k-1}/\alpha_{k-1}$.

The Lean statement writes $k + 1$ for the index $k \ge 1$ of the source. The proof eliminates
the directions from $r^{(k+1)} = r^{(k)} - \alpha_k A p^{(k)}$ through
$A p^{(k)} = (r^{(k)} - r^{(k+1)})/\alpha_k$ and $p^{(k)} = r^{(k)} - \beta_{k-1} p^{(k-1)}$, as
the solution of Exercise 14 does. -/
theorem equation_4_46 (hA : A.PosDef) {k : ℕ} (hr : cgR A b x₀ (k + 1) ≠ 0) :
    toEuclideanLin A (cgR A b x₀ (k + 1)) =
      -(1 / cgAlpha A b x₀ (k + 1)) • cgR A b x₀ (k + 2) +
        (1 / cgAlpha A b x₀ (k + 1) - cgBeta A b x₀ k / cgAlpha A b x₀ k) • cgR A b x₀ (k + 1) +
        (cgBeta A b x₀ k / cgAlpha A b x₀ k) • cgR A b x₀ k := by
  have hr0 : cgR A b x₀ k ≠ 0 := fun h => hr (cgR_succ_eq_zero_of_eq_zero hA h)
  have hα0 := cgAlpha_ne_zero hA hr0
  have hα1 := cgAlpha_ne_zero hA hr
  have hAp : ∀ j, cgAlpha A b x₀ j ≠ 0 → toEuclideanLin A (cgP A b x₀ j) =
      (cgAlpha A b x₀ j)⁻¹ • (cgR A b x₀ j - cgR A b x₀ (j + 1)) := by
    intro j hj
    rw [cgR_succ, sub_sub_cancel, smul_smul, inv_mul_cancel₀ hj, one_smul]
  have hp : cgP A b x₀ (k + 1) = cgR A b x₀ (k + 1) - cgBeta A b x₀ k • cgP A b x₀ k :=
    cgP_succ A b x₀ k
  have hApk := hAp k hα0
  have hApk1 := hAp (k + 1) hα1
  rw [hp, map_sub, map_smul, hApk] at hApk1
  have h : toEuclideanLin A (cgR A b x₀ (k + 1)) =
      (cgAlpha A b x₀ (k + 1))⁻¹ • (cgR A b x₀ (k + 1) - cgR A b x₀ (k + 1 + 1)) +
        cgBeta A b x₀ k • ((cgAlpha A b x₀ k)⁻¹ • (cgR A b x₀ k - cgR A b x₀ (k + 1))) := by
    rw [← hApk1]
    abel
  rw [h]
  module

/-- **Theorem 4.11** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric
positive definite and let $x$ solve $Ax = b$. Let $p^{(0)}, p^{(1)}, \dots$ be mutually
$A$-conjugate directions, $(A p^{(i)})^T p^{(j)} = 0$ for $i \neq j$, with $p^{(i)} \neq 0$ for
$i < n$. Consider the method $x^{(k+1)} = x^{(k)} + \alpha_k p^{(k)}$ with the step length
(4.39) and any $x^{(0)}$. Then for every $k$ the iterate $x^{(k)}$ satisfies the Galerkin
condition over $\operatorname{span}(p^{(0)}, \dots, p^{(k-1)})$ with start $x^{(0)}$, and
$x^{(k)} = x$ for every $k \ge n$: the method terminates after at most $n$ steps with the exact
solution.

**Reading.** The source speaks of any method that employs conjugate directions. The declaration
makes explicit that the first $n$ directions are nonzero.

The method is the backbone's `ConjugateDirection.iterate`, the conjugacy is
`ConjugateDirection.IsConjugateFamily`, and the Galerkin condition is `IsGalerkin`. The proof of
the source is the expanding subspace theorem: $x^{(k)}$ is optimal with respect to
$p^{(0)}, \dots, p^{(k-1)}$ (`ConjugateDirection.isGalerkin_iterate`), so $r^{(n)}$ is
orthogonal to $\mathbb{R}^n$ and $x^{(n)} = x$ (`ConjugateDirection.iterate_eq_of_finrank_le`). -/
theorem theorem_4_11 (hA : A.PosDef) {p : ℕ → EuclideanSpace ℝ (Fin n)}
    (hp : ConjugateDirection.IsConjugateFamily (toEuclideanLin A) p) (h0 : ∀ i < n, p i ≠ 0)
    {x : EuclideanSpace ℝ (Fin n)} (hx : toEuclideanLin A x = b) :
    (∀ k, IsGalerkin (toEuclideanLin A) b x₀ (Submodule.span ℝ (Set.range fun i : Fin k => p i))
        (ConjugateDirection.iterate (toEuclideanLin A) b p x₀ k)) ∧
      ∀ k, n ≤ k → ConjugateDirection.iterate (toEuclideanLin A) b p x₀ k = x := by
  have hA' := (posDef_isSymmetricCoercive_toEuclideanLin hA).isCoercive
  refine ⟨fun k => ConjugateDirection.isGalerkin_iterate b x₀ hA' hp k, fun k hk => ?_⟩
  refine ConjugateDirection.iterate_eq_of_finrank_le b x₀ hA' hp ?_ hx ?_
  · rwa [finrank_euclideanSpace_fin]
  · rwa [finrank_euclideanSpace_fin]

/-- **Theorem 4.12** of [quarteroni2000numerical], finite termination. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite and let $x$ solve $Ax = b$. Then
the conjugate gradient method converges after at most $n$ steps: $r^{(k)} = 0$ as soon as $k$
reaches the grade of $r^{(0)}$, this grade is at most $n$, and $x^{(k)} = x$ for every
$k \ge n$.

The grade of $r^{(0)}$ is `Krylov.grade`, the dimension of the span of all vectors
$A^j r^{(0)}$. The first clause is the backbone's `CG.residual_eq_zero_of_grade_le`, and the
bound on the grade is `Krylov.grade_le_finrank`. The source derives the theorem from Theorem
4.11, of which the conjugate gradient method is an instance
(`CG.iterate_x_eq_conjugateDirection_iterate`). -/
theorem theorem_4_12_terminates (hA : A.PosDef) {x : EuclideanSpace ℝ (Fin n)}
    (hx : toEuclideanLin A x = b) :
    (∀ k, Krylov.grade (toEuclideanLin A) (b - toEuclideanLin A x₀) ≤ k → cgR A b x₀ k = 0) ∧
      Krylov.grade (toEuclideanLin A) (b - toEuclideanLin A x₀) ≤ n ∧
      ∀ k, n ≤ k → cgX A b x₀ k = x := by
  have hA' := (posDef_isSymmetricCoercive_toEuclideanLin hA)
  have hr : ∀ k, Krylov.grade (toEuclideanLin A) (b - toEuclideanLin A x₀) ≤ k →
      cgR A b x₀ k = 0 := fun k hk => by
    rw [cgR_eq_CG hA]
    exact CG.residual_eq_zero_of_grade_le b x₀ hA' hk
  have hgrade : Krylov.grade (toEuclideanLin A) (b - toEuclideanLin A x₀) ≤ n := by
    have := Krylov.grade_le_finrank (toEuclideanLin A) (b - toEuclideanLin A x₀)
    rwa [finrank_euclideanSpace_fin] at this
  refine ⟨hr, hgrade, fun k hk => ?_⟩
  have h := hr k (hgrade.trans hk)
  rw [cgR_eq_residual hA, sub_eq_zero] at h
  exact hA'.isCoercive.injective (h.symm.trans hx.symm)

/-- **Theorem 4.12** of [quarteroni2000numerical], orthogonality of the error. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite, let $x$ solve $Ax = b$, and let
$j < k$. Then the conjugate gradient error $e^{(k)} = x^{(k)} - x$ is $A$-orthogonal to the
direction $p^{(j)}$:
$$(A e^{(k)})^T p^{(j)} = 0.$$

**Correction.** The source states that the error is orthogonal to the directions $p^{(j)}$,
$j < k$. It is $A$-orthogonal to them: $(A e^{(k)})^T p^{(j)} = -r^{(k)T} p^{(j)} = 0$ by
(4.44). -/
theorem theorem_4_12_orthogonal (hA : A.PosDef) {x : EuclideanSpace ℝ (Fin n)}
    (hx : toEuclideanLin A x = b) {k j : ℕ} (hj : j < k) :
    inner ℝ (toEuclideanLin A (cgX A b x₀ k - x)) (cgP A b x₀ j) = 0 := by
  have h := (equation_4_44 (b := b) (x₀ := x₀) hA).1 k j hj
  rw [map_sub, hx, ← neg_sub, ← cgR_eq_residual hA, inner_neg_left, real_inner_comm, h, neg_zero]

/-- **Theorem 4.12** of [quarteroni2000numerical], equation (4.47). Let $n \ge 1$, let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite with spectral condition number
$K_2(A) = \lambda_{\max}/\lambda_{\min}$, and let $x$ solve $Ax = b$. Let
$$c = \frac{\sqrt{K_2(A)} - 1}{\sqrt{K_2(A)} + 1}.$$
Then for every $k$ the error of the conjugate gradient method satisfies
$$\|e^{(k)}\|_A \le \frac{2 c^k}{1 + c^{2k}} \|e^{(0)}\|_A.$$

The errors are written $x - x^{(k)}$ and $x - x^{(0)}$, and $K_2(A)$ is
`NormedRing.condNumber A`. The $k$-th iterate is the Galerkin iterate over the Krylov space
(`CG.isGalerkinIterate`), which minimizes the $A$-norm of the error among all $q(A) e^{(0)}$
with $q \in \mathbb{P}_k^{0,1}$ ((4.49), `QuarteroniSaccoSaleri.Chapter04.equation_4_49`).
Property 4.6 bounds that minimum by $1/T_k((\lambda_1 + \lambda_n)/(\lambda_1 - \lambda_n))$
(`Krylov.IsGalerkinIterate.energyNorm_error_le_div_eval_T`), and
$1/T_k((K_2 + 1)/(K_2 - 1)) = 2c^k/(1 + c^{2k})$
(`Polynomial.Chebyshev.one_div_eval_T_eq_two_mul_pow_div`). When
$\lambda_{\min} = \lambda_{\max}$, so that $K_2(A) = 1$ and $c = 0$, the bound is $1$ at $k = 0$
and $0$ for $k \ge 1$. It holds because $A$ is then a multiple of the identity and the first
step is exact (`Krylov.IsGalerkinIterate.energyNorm_error_le`). -/
theorem theorem_4_12_bound [NeZero n] (hA : A.PosDef) {x : EuclideanSpace ℝ (Fin n)}
    (hx : toEuclideanLin A x = b) (k : ℕ) :
    energyNorm (toEuclideanLin A) (x - cgX A b x₀ k) ≤
      2 * ((√(κ A) - 1) / (√(κ A) + 1)) ^ k / (1 + ((√(κ A) - 1) / (√(κ A) + 1)) ^ (2 * k)) *
        energyNorm (toEuclideanLin A) (x - x₀) := by
  have hA' := (posDef_isSymmetricCoercive_toEuclideanLin hA)
  obtain ⟨lmin, lmax, hsub, hmin, hmax, hIcc⟩ := exists_extreme_eigenvalues hA.1
  have hpos : 0 < lmin := (open scoped MatrixOrder in hA.isStrictlyPositive.spectrum_pos hmin)
  have hle : lmin ≤ lmax := (hsub hmin).2
  have hB := hA.1.isSymmetricBoundedBy_toEuclideanLin hIcc
  have hκ : κ A = lmax / lmin := condNumber_eq_div_of_posDef hA hsub hmin hmax
  have hgal := CG.isGalerkinIterate b x₀ hA' k
  rw [cgX_eq_CG hA]
  rcases hle.lt_or_eq with hlt | heq
  · have hκ1 : 1 < κ A := by
      rw [hκ, lt_div_iff₀ hpos, one_mul]
      exact hlt
    have h := hgal.energyNorm_error_le_div_eval_T hpos hlt hB hx
    have hT := Polynomial.Chebyshev.one_div_eval_T_eq_two_mul_pow_div hκ1 k
    rw [show (κ A + 1) / (κ A - 1) = (lmax + lmin) / (lmax - lmin) by
      rw [hκ]; field_simp] at hT
    rw [div_eq_mul_one_div, hT, mul_comm] at h
    exact h
  · subst heq
    have hκ1 : κ A = 1 := by rw [hκ, div_self hpos.ne']
    rw [hκ1, Real.sqrt_one, sub_self, zero_div]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [pow_zero, mul_one, mul_zero, CG.iterate_zero, CG.init_x]
      norm_num
    · have h := hgal.energyNorm_error_le hpos le_rfl hB hx
      rw [div_self hpos.ne', Real.sqrt_one, sub_self, zero_div, zero_pow hk.ne', mul_zero,
        zero_mul] at h
      rw [zero_pow hk.ne', mul_zero, zero_div, zero_mul]
      exact h

/-- **Equations (4.48)–(4.49)** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ be
symmetric positive definite and let $x$ solve $Ax = b$. For every $k \ge 1$ the $A$-norm of the
conjugate gradient error is
$$\|e^{(k)}\|_A = \min_{q \in \mathbb{P}_k^{0,1}} \|q(A) e^{(0)}\|_A,$$
where $\mathbb{P}_k^{0,1}$ is the set of real polynomials $q$ of degree at most $k$ with
$q(0) = 1$.

**Generalization.** The source takes $x^{(0)} = 0$, so that $e^{(0)} = x$. The declaration
allows any $x^{(0)}$.

The Lean statement writes $k + 1$ for $k \ge 1$, the errors as $x - x^{(k)}$, and the minimum as
the infimum `⨅` over the subtype of these polynomials. The proof combines `CG.isGalerkinIterate`
with the polynomial characterization `Krylov.IsGalerkinIterate.energyNorm_error_eq_iInf`. -/
theorem equation_4_49 (hA : A.PosDef) {x : EuclideanSpace ℝ (Fin n)}
    (hx : toEuclideanLin A x = b) (k : ℕ) :
    energyNorm (toEuclideanLin A) (x - cgX A b x₀ (k + 1)) =
      ⨅ q : {q : Polynomial ℝ // q.degree ≤ (k + 1 : ℕ) ∧ q.eval 0 = 1},
        energyNorm (toEuclideanLin A) (Polynomial.aeval (toEuclideanLin A) q.1 (x - x₀)) := by
  rw [cgX_eq_CG hA]
  exact (CG.isGalerkinIterate b x₀ (posDef_isSymmetricCoercive_toEuclideanLin hA)
    (k + 1)).energyNorm_error_eq_iInf (posDef_isSymmetricCoercive_toEuclideanLin hA) hx

end ConjugateGradient

/-! ### Property 4.6 -/

section Chebyshev

open Polynomial

/-- **Property 4.6** of [quarteroni2000numerical], the value and the minimizer. Let
$0 < \lambda_n < \lambda_1$ and $k \ge 0$, let $T_{k+1}$ be the Chebyshev polynomial of degree
$k + 1$, and let
$$C_{k+1} = T_{k+1}\Big(\frac{\lambda_1 + \lambda_n}{\lambda_1 - \lambda_n}\Big).$$
Every real polynomial $q$ of degree at most $k + 1$ with $q(0) = 1$ satisfies
$$\frac{1}{C_{k+1}} \le \max_{\lambda_n \le z \le \lambda_1} |q(z)|.$$
The polynomial
$$p_{k+1}(\xi) = \frac{1}{C_{k+1}} T_{k+1}\Big(\frac{\lambda_1 + \lambda_n - 2\xi}{\lambda_1 -
  \lambda_n}\Big)$$
has degree at most $k + 1$, satisfies $p_{k+1}(0) = 1$, and attains the bound: $\max_{\lambda_n
\le z \le \lambda_1} |p_{k+1}(z)| = 1/C_{k+1}$. So the problem of minimizing
$\max_{\lambda_n \le z \le \lambda_1} |q(z)|$ over $q \in \mathbb{P}_{k+1}^{0,1}$ has the value
$1/C_{k+1}$, attained at $p_{k+1}$.

The maximum is the supremum `sSup` of the image of the interval. The polynomial $p_{k+1}$ is the
backbone's `Polynomial.Chebyshev.shifted (k + 1) lmin lmax 0`, and $T_{k+1}$ is Mathlib's
`Polynomial.Chebyshev.T`. The proof uses
`Polynomial.Chebyshev.one_div_eval_T_le_sSup_abs_eval_of_eval_zero` and
`Polynomial.Chebyshev.sSup_abs_eval_shifted`. -/
theorem property_4_6 {lmin lmax : ℝ} (hpos : 0 < lmin) (hlt : lmin < lmax) (k : ℕ) :
    (∀ q : ℝ[X], q.degree ≤ (k + 1 : ℕ) → q.eval 0 = 1 →
        1 / (Chebyshev.T ℝ (k + 1 : ℕ)).eval ((lmax + lmin) / (lmax - lmin)) ≤
          sSup ((fun t => |q.eval t|) '' Set.Icc lmin lmax)) ∧
      (Chebyshev.shifted (k + 1) lmin lmax 0).degree ≤ (k + 1 : ℕ) ∧
      (Chebyshev.shifted (k + 1) lmin lmax 0).eval 0 = 1 ∧
      (∀ ξ, (Chebyshev.shifted (k + 1) lmin lmax 0).eval ξ =
        (Chebyshev.T ℝ (k + 1 : ℕ)).eval ((lmax + lmin - 2 * ξ) / (lmax - lmin)) /
          (Chebyshev.T ℝ (k + 1 : ℕ)).eval ((lmax + lmin) / (lmax - lmin))) ∧
      sSup ((fun t => |(Chebyshev.shifted (k + 1) lmin lmax 0).eval t|) '' Set.Icc lmin lmax) =
        1 / (Chebyshev.T ℝ (k + 1 : ℕ)).eval ((lmax + lmin) / (lmax - lmin)) := by
  have hγ : (0 : ℝ) ∉ Set.Icc lmin lmax := fun h => absurd h.1 (not_le.mpr hpos)
  have hu : 1 ≤ (lmax + lmin) / (lmax - lmin) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  refine ⟨fun q hq hq0 =>
      Chebyshev.one_div_eval_T_le_sSup_abs_eval_of_eval_zero (k + 1) hpos hlt q hq hq0,
    Chebyshev.shifted_degree_le _ _ _ _, Chebyshev.shifted_eval_self _ hlt hγ, fun ξ => ?_, ?_⟩
  · have hne : lmax - lmin ≠ 0 := by linarith
    have harg : (lmax + lmin) / (lmax - lmin) - 2 / (lmax - lmin) * ξ =
        (lmax + lmin - 2 * ξ) / (lmax - lmin) := by
      field_simp
    simp only [Chebyshev.shifted, eval_mul, eval_C, eval_comp, eval_sub, eval_X, mul_zero,
      sub_zero, harg]
    ring
  · rw [Chebyshev.sSup_abs_eval_shifted _ hlt hγ, mul_zero, sub_zero,
      abs_of_nonneg (zero_le_one.trans (Chebyshev.one_le_eval_T hu _))]

/-- **Property 4.6** of [quarteroni2000numerical], uniqueness. Let $0 < \lambda_n < \lambda_1$ and
$k \ge 0$. If a real polynomial $q$ of degree at most $k + 1$ with $q(0) = 1$ satisfies
$$\max_{\lambda_n \le z \le \lambda_1} |q(z)| = \frac{1}{C_{k+1}},$$
then $q = p_{k+1}$, with $C_{k+1}$ and $p_{k+1}$ as in
`QuarteroniSaccoSaleri.Chapter04.property_4_6`. So the minimizer of Property 4.6 is unique.

The source states Property 4.6 without proof. The proof is the backbone's
`Polynomial.Chebyshev.eq_shifted_of_sSup_abs_eval_eq`. -/
theorem property_4_6_unique {lmin lmax : ℝ} (hpos : 0 < lmin) (hlt : lmin < lmax) (k : ℕ)
    {q : ℝ[X]} (hq : q.degree ≤ (k + 1 : ℕ)) (hq0 : q.eval 0 = 1)
    (hsup : sSup ((fun t => |q.eval t|) '' Set.Icc lmin lmax) =
      1 / (Chebyshev.T ℝ (k + 1 : ℕ)).eval ((lmax + lmin) / (lmax - lmin))) :
    q = Chebyshev.shifted (k + 1) lmin lmax 0 :=
  Chebyshev.eq_shifted_of_sSup_abs_eval_eq (by omega) hpos hlt (natDegree_le_iff_degree_le.mpr hq)
    hq0 hsup

end Chebyshev


/-! ### Exercise 12 -/

section Exercise

/-- The gradient step of (4.37) on coordinates: for $b, x \in \mathbb{R}^n$ given as `Fin n → ℝ`,
with $r = b - Ax$, the gradient step from `toLp 2 x` is `toLp 2` of $x + (r^T r / r^T A r)\, r$.
This supports the computation of Exercise 12. -/
theorem gradientStep_toLp (A : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) :
    gradientStep A (toLp 2 b) (toLp 2 x) =
      toLp 2 (x + ((b - A *ᵥ x) ⬝ᵥ (b - A *ᵥ x) / ((b - A *ᵥ x) ⬝ᵥ (A *ᵥ (b - A *ᵥ x)))) •
        (b - A *ᵥ x)) := by
  simp only [gradientStep, toEuclideanLin_toLp, ← toLp_sub, EuclideanSpace.inner_toLp_toLp,
    star_trivial, ← toLp_smul, ← toLp_add]
  rw [dotProduct_comm (A *ᵥ (b - A *ᵥ x))]

/-- The matrix $\operatorname{diag}(1, 3)$ of Exercise 12 is symmetric positive definite. -/
private theorem posDef_diag_one_three : (!![1, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  have h : (!![1, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℝ) = diagonal ![1, 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [h, posDef_diagonal_iff]
  intro i
  fin_cases i <;> norm_num

/-- **Exercise 12** of [quarteroni2000numerical], Chapter 4, cited after Definition 4.4. The source
asks to show that the iterate $x^{(k+1)}$ of the gradient method is optimal with respect to
$r^{(k)}$, but that $x^{(k+2)}$ in general is not. The declaration proves this for
$A = \operatorname{diag}(1, 3)$, $b = 0$ and $x^{(0)} = (1, 1)$: the gradient iterate $x^{(1)}$
is optimal with respect to $r^{(0)} = b - Ax^{(0)}$, and the gradient iterate $x^{(2)}$ is not
optimal with respect to $r^{(0)}$.

In this example $r^{(0)} = -(1, 3)$, $x^{(1)} = (9/14, -1/14)$, $x^{(2)} = (3/28, 3/28)$ and
$r^{(2)} = -(3/28, 9/28)$. Then $r^{(1)T} r^{(0)} = 0$ while $r^{(2)T} r^{(0)} = 30/28 \neq 0$,
and optimality follows from `QuarteroniSaccoSaleri.Chapter04.definition_4_4_iff`. The general
claim of the exercise is not formalized. -/
theorem exercise_4_12 :
    definition_4_4 (!![1, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℝ) 0
        (gradientStep !![1, 0; 0, 3] 0 (toLp 2 ![1, 1]))
        (0 - toEuclideanLin !![1, 0; 0, 3] (toLp 2 ![1, 1])) ∧
      ¬ definition_4_4 (!![1, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℝ) 0
        ((gradientStep !![1, 0; 0, 3] 0)^[2] (toLp 2 ![1, 1]))
        (0 - toEuclideanLin !![1, 0; 0, 3] (toLp 2 ![1, 1])) := by
  have h0 : (0 : EuclideanSpace ℝ (Fin 2)) = toLp 2 0 := rfl
  have hx₁ : gradientStep (!![1, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℝ) (toLp 2 0) (toLp 2 ![1, 1]) =
      toLp 2 ![9 / 14, -1 / 14] := by
    rw [gradientStep_toLp]
    congr 1
    ext i
    fin_cases i <;>
    · simp [dotProduct, Fin.sum_univ_two]
      norm_num
  have hx₂ : gradientStep (!![1, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℝ) (toLp 2 0)
      (toLp 2 ![9 / 14, -1 / 14]) = toLp 2 ![3 / 28, 3 / 28] := by
    rw [gradientStep_toLp]
    congr 1
    ext i
    fin_cases i <;>
    · simp [dotProduct, Fin.sum_univ_two]
      norm_num
  have hiter : (gradientStep (!![1, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℝ) (toLp 2 0))^[2]
      (toLp 2 ![1, 1]) = toLp 2 ![3 / 28, 3 / 28] := by
    rw [Function.iterate_succ_apply', Function.iterate_one, hx₁, hx₂]
  rw [h0, hx₁, hiter, (definition_4_4_iff posDef_diag_one_three _ _ ⊥ 0).1,
    (definition_4_4_iff posDef_diag_one_three _ _ ⊥ 0).1]
  simp only [toEuclideanLin_toLp, ← toLp_sub, EuclideanSpace.inner_toLp_toLp, star_trivial]
  constructor
  · simp [dotProduct, Fin.sum_univ_two]
    norm_num
  · simp [dotProduct, Fin.sum_univ_two]
    norm_num

end Exercise

/-! ### §4.3.5 The preconditioned conjugate gradient method -/

section PCG

variable (A P : Matrix (Fin n) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin n))

/-- **Section 4.3.5** of [quarteroni2000numerical], the preconditioned conjugate gradient iteration.
Let $A, P \in \mathbb{R}^{n \times n}$. One step maps the state $(x^{(k)}, r^{(k)}, p^{(k)})$ to
$(x^{(k+1)}, r^{(k+1)}, p^{(k+1)})$, where
$$\alpha_k = \frac{p^{(k)T} r^{(k)}}{p^{(k)T} A p^{(k)}}, \qquad x^{(k+1)} = x^{(k)} + \alpha_k
  p^{(k)}, \qquad r^{(k+1)} = r^{(k)} - \alpha_k A p^{(k)},$$
$$P z^{(k+1)} = r^{(k+1)}, \qquad \beta_k = \frac{(A p^{(k)})^T z^{(k+1)}}{(A p^{(k)})^T
  p^{(k)}}, \qquad p^{(k+1)} = z^{(k+1)} - \beta_k p^{(k)}.$$

The vector $z^{(k+1)}$ is computed as $P^{-1} r^{(k+1)}$ with Mathlib's inverse. As in
`QuarteroniSaccoSaleri.Chapter04.cgStep`, this $\beta_k$ is the negative of the backbone's
`Krylov.PCG.beta`. The state type is the backbone's record `Krylov.PCG.State`, and the
identification with the backbone is `QuarteroniSaccoSaleri.Chapter04.pcg_eq_PCG`. -/
noncomputable def pcgStep (s : Krylov.PCG.State (EuclideanSpace ℝ (Fin n))) :
    Krylov.PCG.State (EuclideanSpace ℝ (Fin n)) :=
  let α := inner ℝ s.p s.r / inner ℝ s.p (toEuclideanLin A s.p)
  let r' := s.r - α • toEuclideanLin A s.p
  let z' := toEuclideanLin P⁻¹ r'
  let β := inner ℝ (toEuclideanLin A s.p) z' / inner ℝ (toEuclideanLin A s.p) s.p
  { x := s.x + α • s.p, r := r', p := z' - β • s.p }

/-- **Section 4.3.5** of [quarteroni2000numerical], the **preconditioned conjugate gradient
method**. Start from $x^{(0)}$ with $r^{(0)} = b - Ax^{(0)}$, $z^{(0)} = P^{-1} r^{(0)}$ and
$p^{(0)} = z^{(0)}$. Then `pcg A P b x₀ k` is the state $(x^{(k)}, r^{(k)}, p^{(k)})$ after $k$
steps of `QuarteroniSaccoSaleri.Chapter04.pcgStep`. -/
noncomputable def pcg (x₀ : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    Krylov.PCG.State (EuclideanSpace ℝ (Fin n)) :=
  (pcgStep A P)^[k]
    { x := x₀, r := b - toEuclideanLin A x₀, p := toEuclideanLin P⁻¹ (b - toEuclideanLin A x₀) }

variable (x₀ : EuclideanSpace ℝ (Fin n))

/-- The step length $\alpha_k = p^{(k)T} r^{(k)} / p^{(k)T} A p^{(k)}$ of the preconditioned
conjugate gradient method at step $k$. -/
noncomputable def pcgAlpha (k : ℕ) : ℝ :=
  inner ℝ (pcg A P b x₀ k).p (pcg A P b x₀ k).r /
    inner ℝ (pcg A P b x₀ k).p (toEuclideanLin A (pcg A P b x₀ k).p)

/-- The coefficient $\beta_k = (A p^{(k)})^T z^{(k+1)} / (A p^{(k)})^T p^{(k)}$ of the
preconditioned conjugate gradient method at step $k$, with $z^{(k+1)} = P^{-1} r^{(k+1)}$. -/
noncomputable def pcgBeta (k : ℕ) : ℝ :=
  inner ℝ (toEuclideanLin A (pcg A P b x₀ k).p) (toEuclideanLin P⁻¹ (pcg A P b x₀ (k + 1)).r) /
    inner ℝ (toEuclideanLin A (pcg A P b x₀ k).p) (pcg A P b x₀ k).p

/-- The state of the preconditioned conjugate gradient method after $k + 1$ steps is one step of
`QuarteroniSaccoSaleri.Chapter04.pcgStep` from the state after $k$ steps. -/
theorem pcg_succ (k : ℕ) : pcg A P b x₀ (k + 1) = pcgStep A P (pcg A P b x₀ k) :=
  Function.iterate_succ_apply' _ _ _

/-- The preconditioned conjugate gradient iterates satisfy $x^{(k+1)} = x^{(k)} + \alpha_k p^{(k)}$.
-/
theorem pcg_succ_x (k : ℕ) :
    (pcg A P b x₀ (k + 1)).x = (pcg A P b x₀ k).x + pcgAlpha A P b x₀ k • (pcg A P b x₀ k).p := by
  rw [pcg_succ]
  rfl

/-- The preconditioned conjugate gradient residuals satisfy
$r^{(k+1)} = r^{(k)} - \alpha_k A p^{(k)}$. -/
theorem pcg_succ_r (k : ℕ) :
    (pcg A P b x₀ (k + 1)).r =
      (pcg A P b x₀ k).r - pcgAlpha A P b x₀ k • toEuclideanLin A (pcg A P b x₀ k).p := by
  rw [pcg_succ]
  rfl

/-- The preconditioned conjugate gradient directions satisfy
$p^{(k+1)} = z^{(k+1)} - \beta_k p^{(k)}$, with $z^{(k+1)} = P^{-1} r^{(k+1)}$. -/
theorem pcg_succ_p (k : ℕ) :
    (pcg A P b x₀ (k + 1)).p =
      toEuclideanLin P⁻¹ (pcg A P b x₀ (k + 1)).r - pcgBeta A P b x₀ k • (pcg A P b x₀ k).p := by
  rw [pcgBeta, pcg_succ]
  rfl

variable {A P b x₀}

/-- Let $P \in \mathbb{R}^{n \times n}$ be symmetric positive definite. Then $P$ with its inverse
$P^{-1}$ is a preconditioner in the sense of the backbone's `Krylov.IsPreconditioner`: $P$ is
symmetric coercive and $P P^{-1} x = x$ for every $x$. The proof is
`Matrix.PosDef.isPreconditioner_toEuclideanLin`. -/
theorem isPreconditioner_of_posDef (hP : P.PosDef) :
    Krylov.IsPreconditioner (toEuclideanLin P) (toEuclideanLin P⁻¹) :=
  hP.isPreconditioner_toEuclideanLin

/-- Let $A, P \in \mathbb{R}^{n \times n}$ be symmetric positive definite. The preconditioned
operator $P^{-1} A$ is symmetric and coercive for the $P$-inner product $(x, y)_P = (Px, y)$.

It is symmetric there because $A$ is symmetric, and coercive because
$(P^{-1} A x, x)_P = (Ax, x) > 0$ for $x \neq 0$ in finite dimension
(`LinearMap.isCoercive_iff_forall_pos`). The operator on the space with the $P$-inner product is
`Krylov.IsPreconditioner.energyEnd`. -/
theorem isSymmetricCoercive_energyEnd_of_posDef (hA : A.PosDef) (hP : P.PosDef) :
    ((isPreconditioner_of_posDef hP).energyEnd
      (toEuclideanLin P⁻¹ ∘ₗ toEuclideanLin A)).IsSymmetricCoercive := by
  have hM := isPreconditioner_of_posDef hP
  have hA' := posDef_isSymmetricCoercive_toEuclideanLin hA
  have : FiniteDimensional ℝ hM.EnergySpace := hM.toEnergy.finiteDimensional
  refine ⟨fun y y' => ?_, (LinearMap.isCoercive_iff_forall_pos _).2 fun y hy => ?_⟩
  · obtain ⟨x, rfl⟩ := hM.toEnergy.surjective y
    obtain ⟨x', rfl⟩ := hM.toEnergy.surjective y'
    rw [hM.inner_energyEnd_left, hM.inner_energyEnd_right]
    exact hA'.isSymmetric x x'
  · obtain ⟨x, rfl⟩ := hM.toEnergy.surjective y
    rw [hM.inner_energyEnd_left]
    exact hA'.isCoercive.inner_self_pos fun h => hy (by rw [h, map_zero])

/-- For symmetric positive definite $P$, the $P$-inner product of $P^{-1} u$ and $w$ is $(u, w)$. -/
private theorem inner_toEnergy_inv_left (hP : P.PosDef) (u w : EuclideanSpace ℝ (Fin n)) :
    inner ℝ ((isPreconditioner_of_posDef hP).toEnergy (toEuclideanLin P⁻¹ u))
      ((isPreconditioner_of_posDef hP).toEnergy w) = inner ℝ u w := by
  rw [WithEnergy.inner_equiv, energyInner, (isPreconditioner_of_posDef hP).apply_inv]

/-- On the backbone's preconditioned conjugate gradient iterates,
$p^{(k)T} r^{(k)} = r^{(k)T} P^{-1} r^{(k)}$. -/
private theorem pcg_inner_direction_residual (hA : A.PosDef) (hP : P.PosDef) (k : ℕ) :
    inner ℝ (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k).p
        (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k).r =
      inner ℝ (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k).r
        (toEuclideanLin P⁻¹
          (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k).r) := by
  have hM := isPreconditioner_of_posDef hP
  have hB := isSymmetricCoercive_energyEnd_of_posDef hA hP
  obtain ⟨-, hr, hp, -⟩ := Krylov.PCG.iterate_eq_CG_iterate_withEnergy (toEuclideanLin A)
    (toEuclideanLin P⁻¹) b x₀ hM k
  have h := CG.inner_residual_direction_eq (hM.toEnergy (toEuclideanLin P⁻¹ b)) (hM.toEnergy x₀)
    hB (le_refl k)
  rw [RCLike.ofReal_real_eq_id, id_eq, ← hr, ← hp, inner_toEnergy_inv_left hP,
    ← real_inner_self_eq_norm_sq, inner_toEnergy_inv_left hP] at h
  rw [real_inner_comm, h, real_inner_comm]

/-- On the backbone's preconditioned conjugate gradient iterates, the step length of
`QuarteroniSaccoSaleri.Chapter04.pcgStep` is `Krylov.PCG.alpha`. -/
private theorem pcgAlpha_iterate (hA : A.PosDef) (hP : P.PosDef) (k : ℕ) :
    inner ℝ (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k).p
        (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k).r /
      inner ℝ (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k).p
        (toEuclideanLin A (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k).p) =
      Krylov.PCG.alpha (toEuclideanLin A) (toEuclideanLin P⁻¹)
        (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k) := by
  rw [Krylov.PCG.alpha, pcg_inner_direction_residual hA hP,
    real_inner_comm (toEuclideanLin A (Krylov.PCG.iterate _ _ b x₀ k).p)]

/-- On the backbone's preconditioned conjugate gradient iterates, one step of
`QuarteroniSaccoSaleri.Chapter04.pcgStep` produces the backbone's next residual. -/
private theorem pcgStep_r_iterate (hA : A.PosDef) (hP : P.PosDef) (k : ℕ) :
    (pcgStep A P (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k)).r =
      (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ (k + 1)).r := by
  rw [Krylov.PCG.iterate_succ, Krylov.PCG.step_r, pcgStep, pcgAlpha_iterate hA hP]

/-- On the backbone's preconditioned conjugate gradient iterates, the coefficient $\beta_k$ of
`QuarteroniSaccoSaleri.Chapter04.pcgStep` is the negative of `Krylov.PCG.beta`, by
$\alpha_k A p^{(k)} = r^{(k)} - r^{(k+1)}$ and the orthogonality relations
$r^{(k)T} P^{-1} r^{(k+1)} = 0$ and $r^{(k+1)T} p^{(k)} = 0$. -/
private theorem pcgBeta_iterate (hA : A.PosDef) (hP : P.PosDef) (k : ℕ) :
    inner ℝ
        (toEuclideanLin A (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k).p)
        (toEuclideanLin P⁻¹
          (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ (k + 1)).r) /
      inner ℝ
        (toEuclideanLin A (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k).p)
        (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k).p =
      -Krylov.PCG.beta (toEuclideanLin A) (toEuclideanLin P⁻¹)
        (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k) := by
  have hM := isPreconditioner_of_posDef hP
  have hB := isSymmetricCoercive_energyEnd_of_posDef hA hP
  set A' := toEuclideanLin A with hA'def
  set Minv := toEuclideanLin P⁻¹ with hMinv
  set S := Krylov.PCG.iterate A' Minv b x₀ with hS
  set T := CG.iterate (hM.energyEnd (Minv ∘ₗ A')) (hM.toEnergy (Minv b)) (hM.toEnergy x₀) with hT
  obtain ⟨-, hr, hp, -⟩ := Krylov.PCG.iterate_eq_CG_iterate_withEnergy A' Minv b x₀ hM k
  obtain ⟨-, hr1, -, -⟩ := Krylov.PCG.iterate_eq_CG_iterate_withEnergy A' Minv b x₀ hM (k + 1)
  have hstep : (S (k + 1)).r = (S k).r - Krylov.PCG.alpha A' Minv (S k) • A' (S k).p := by
    rw [hS, Krylov.PCG.iterate_succ, Krylov.PCG.step_r]
  rw [Krylov.PCG.beta, ← Krylov.PCG.iterate_succ]
  rcases eq_or_ne (S k).r 0 with hr0 | hr0
  · have hTr : (T k).r = 0 := by rw [← hr, hr0, map_zero, map_zero]
    have hTp : (T k).p = 0 := CG.direction_eq_zero_of_residual_eq_zero _ _ _ hTr
    have hp0 : (S k).p = 0 := by
      rw [← hp] at hTp
      exact hM.toEnergy.map_eq_zero_iff.mp hTp
    rw [hstep, hr0, hp0]
    simp
  · have hTr : (T k).r ≠ 0 := by
      rw [← hr]
      intro h
      have h' : Minv (S k).r = 0 := hM.toEnergy.map_eq_zero_iff.mp h
      exact hr0 (by rw [← hM.apply_inv (S k).r, h', map_zero])
    have hpos := CG.re_inner_apply_direction_pos (hM.toEnergy (Minv b)) (hM.toEnergy x₀) hB hTr
    rw [← hp, hM.inner_energyEnd_left, RCLike.re_to_real] at hpos
    have hrpos : 0 < inner ℝ (S k).r (Minv (S k).r) := by
      have h := real_inner_self_pos.mpr hTr
      rwa [← hr, inner_toEnergy_inv_left hP] at h
    have hαne : Krylov.PCG.alpha A' Minv (S k) ≠ 0 := by
      rw [Krylov.PCG.alpha]
      exact div_ne_zero hrpos.ne' hpos.ne'
    have hAp : A' (S k).p = (Krylov.PCG.alpha A' Minv (S k))⁻¹ • ((S k).r - (S (k + 1)).r) := by
      rw [hstep, sub_sub_cancel, smul_smul, inv_mul_cancel₀ hαne, one_smul]
    have h1 : inner ℝ (S k).r (Minv (S (k + 1)).r) = 0 := by
      have h := CG.inner_residual_eq_zero (hM.toEnergy (Minv b)) (hM.toEnergy x₀) hB
        (Nat.ne_of_lt (Nat.lt_succ_self k))
      rwa [← hr, ← hr1, inner_toEnergy_inv_left hP] at h
    have h2 : inner ℝ (S (k + 1)).r (S k).p = 0 := by
      have h := CG.inner_residual_direction_eq_zero (hM.toEnergy (Minv b)) (hM.toEnergy x₀) hB
        (Nat.lt_succ_self k)
      rwa [← hr1, ← hp, inner_toEnergy_inv_left hP] at h
    have h3 : inner ℝ (S k).r (S k).p = inner ℝ (S k).r (Minv (S k).r) := by
      rw [real_inner_comm]
      exact pcg_inner_direction_residual hA hP k
    have hN := hrpos.ne'
    rw [hAp, inner_smul_left, inner_smul_left, inner_sub_left, inner_sub_left, h1, h2, h3,
      RCLike.conj_to_real]
    simp only [← hS]
    field_simp
    ring

/-- Two states of the backbone's preconditioned conjugate gradient method are equal if their three
components are equal. -/
private theorem PCG.State.ext' {E : Type*} {s t : Krylov.PCG.State E} (hx : s.x = t.x)
    (hr : s.r = t.r) (hp : s.p = t.p) : s = t := by
  cases s
  cases t
  simp only at hx hr hp
  rw [hx, hr, hp]

/-- On the backbone's preconditioned conjugate gradient iterates,
`QuarteroniSaccoSaleri.Chapter04.pcgStep` is the backbone's `Krylov.PCG.step`. -/
private theorem pcgStep_iterate (hA : A.PosDef) (hP : P.PosDef) (k : ℕ) :
    pcgStep A P (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k) =
      Krylov.PCG.step (toEuclideanLin A) (toEuclideanLin P⁻¹)
        (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k) := by
  have hβ := pcgBeta_iterate hA hP (b := b) (x₀ := x₀) k
  have hr := pcgStep_r_iterate hA hP (b := b) (x₀ := x₀) k
  set s := Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k with hs
  refine PCG.State.ext' ?_ ?_ ?_
  · rw [Krylov.PCG.step_x, pcgStep, pcgAlpha_iterate hA hP]
  · rw [Krylov.PCG.step_r, pcgStep, pcgAlpha_iterate hA hP]
  · rw [Krylov.PCG.step_p, ← Krylov.PCG.iterate_succ, ← hr]
    change toEuclideanLin P⁻¹ (pcgStep A P s).r -
      (inner ℝ (toEuclideanLin A s.p) (toEuclideanLin P⁻¹ (pcgStep A P s).r) /
        inner ℝ (toEuclideanLin A s.p) s.p) • s.p = _
    rw [hr, hβ, neg_smul, sub_neg_eq_add]

/-- Let $A, P \in \mathbb{R}^{n \times n}$ be symmetric positive definite. For every $k$, the state
of the preconditioned conjugate gradient method of §4.3.5 after $k$ steps is the backbone's
state `Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k`, the step length is
`Krylov.PCG.alpha` of that state, and the coefficient of the direction update is the negative of
`Krylov.PCG.beta` of that state.

The identities behind the step length and the coefficient are
$p^{(k)T} r^{(k)} = r^{(k)T} P^{-1} r^{(k)}$ and $(A p^{(k)})^T P^{-1} r^{(k+1)} = -r^{(k+1)T}
P^{-1} r^{(k+1)} / \alpha_k$. They are those of the conjugate gradient method for $P^{-1} A$ in
the $P$-inner product (`Krylov.PCG.iterate_eq_CG_iterate_withEnergy`). -/
theorem pcg_eq_PCG (hA : A.PosDef) (hP : P.PosDef) (k : ℕ) :
    pcg A P b x₀ k = Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k ∧
      pcgAlpha A P b x₀ k = Krylov.PCG.alpha (toEuclideanLin A) (toEuclideanLin P⁻¹)
        (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k) ∧
      pcgBeta A P b x₀ k = -Krylov.PCG.beta (toEuclideanLin A) (toEuclideanLin P⁻¹)
        (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k) := by
  have hpcg : ∀ k, pcg A P b x₀ k =
      Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [pcg_succ, ih, pcgStep_iterate hA hP, Krylov.PCG.iterate_succ]
  refine ⟨hpcg k, ?_, ?_⟩
  · rw [pcgAlpha, hpcg, pcgAlpha_iterate hA hP]
  · rw [pcgBeta, hpcg, hpcg, pcgBeta_iterate hA hP]

/-- **Section 4.3.5** of [quarteroni2000numerical], the error estimate. Let
$A, P \in \mathbb{R}^{n \times n}$ be symmetric positive definite and let $x$ solve $Ax = b$.
Let $0 < \lambda_n \le \lambda_1$ enclose the generalized eigenvalues of $Ay = \lambda Py$ in
the sense that
$$\lambda_n (Py, y) \le (Ay, y) \le \lambda_1 (Py, y) \quad \text{for all } y \in
  \mathbb{R}^n,$$
and let $K = \lambda_1/\lambda_n$. Then for every $k$ the error of the preconditioned conjugate
gradient method satisfies
$$\|e^{(k)}\|_A \le 2 \Big(\frac{\sqrt{K} - 1}{\sqrt{K} + 1}\Big)^k \|e^{(0)}\|_A.$$
The source states that the error estimate is the same as for the non preconditioned method, with
$A$ replaced by $P^{-1} A$.

The errors are written $x - x^{(k)}$ and $x - x^{(0)}$. By Remark 4.2 the numbers $\lambda_n$
and $\lambda_1$ bound the eigenvalues of $P^{-1}A$. The proof is the backbone's
`Krylov.PCG.energyNorm_error_le` through `QuarteroniSaccoSaleri.Chapter04.pcg_eq_PCG`. The bound
has the factor $2c^k$, which is weaker than the factor $2c^k/(1 + c^{2k})$ of (4.47). -/
theorem pcg_energyNorm_error_le (hA : A.PosDef) (hP : P.PosDef) {x : EuclideanSpace ℝ (Fin n)}
    (hx : toEuclideanLin A x = b) {lmin lmax : ℝ} (hpos : 0 < lmin) (hle : lmin ≤ lmax)
    (hlo : ∀ y, lmin * inner ℝ (toEuclideanLin P y) y ≤ inner ℝ (toEuclideanLin A y) y)
    (hhi : ∀ y, inner ℝ (toEuclideanLin A y) y ≤ lmax * inner ℝ (toEuclideanLin P y) y) (k : ℕ) :
    energyNorm (toEuclideanLin A) (x - (pcg A P b x₀ k).x) ≤
      2 * ((√(lmax / lmin) - 1) / (√(lmax / lmin) + 1)) ^ k *
        energyNorm (toEuclideanLin A) (x - x₀) := by
  rw [(pcg_eq_PCG hA hP k).1]
  exact Krylov.PCG.energyNorm_error_le (isPreconditioner_of_posDef hP)
    (posDef_isSymmetricCoercive_toEuclideanLin hA).isSymmetric hpos hle
    (fun y => by simpa using hlo y) (fun y => by simpa using hhi y) hx k

end PCG


/-! ### §4.3.6 The alternating-direction method -/

section ADI

variable (A₁ A₂ : Matrix (Fin n) (Fin n) ℝ) (α₁ α₂ : ℝ)

/-- **Equation (4.50)** of [quarteroni2000numerical], the **alternating-direction method** of
Peaceman and Rachford. Let $A = A_1 + A_2$ with $A_1, A_2 \in \mathbb{R}^{n \times n}$, let
$\alpha_1, \alpha_2 \in \mathbb{R}$ and $b \in \mathbb{R}^n$. One step from $x^{(k)}$ solves
$$(I + \alpha_1 A_1) x^{(k+1/2)} = (I - \alpha_1 A_2) x^{(k)} + \alpha_1 b$$
for the half step, and then
$$(I + \alpha_2 A_2) x^{(k+1)} = (I - \alpha_2 A_1) x^{(k+1/2)} + \alpha_2 b.$$

The two solves are written with Mathlib's matrix inverse, which is $0$ for a singular matrix.
The $k$-th iterate from $x^{(0)}$ is `(adiStep A₁ A₂ α₁ α₂ b)^[k] x₀`. -/
noncomputable def adiStep (b x : Fin n → ℝ) : Fin n → ℝ :=
  (1 + α₂ • A₂)⁻¹ *ᵥ ((1 - α₂ • A₁) *ᵥ ((1 + α₁ • A₁)⁻¹ *ᵥ ((1 - α₁ • A₂) *ᵥ x + α₁ • b)) + α₂ • b)

/-- **Section 4.3.6** of [quarteroni2000numerical], the display after (4.50). The **iteration
matrix** of the alternating-direction method is
$$B = (I + \alpha_2 A_2)^{-1} (I - \alpha_2 A_1) (I + \alpha_1 A_1)^{-1} (I - \alpha_1 A_2).$$
-/
noncomputable def adiMatrix : Matrix (Fin n) (Fin n) ℝ :=
  (1 + α₂ • A₂)⁻¹ * (1 - α₂ • A₁) * (1 + α₁ • A₁)⁻¹ * (1 - α₁ • A₂)

/-- **Section 4.3.6** of [quarteroni2000numerical], the display after (4.50). The vector $f$ of the
alternating-direction method is
$$f = (I + \alpha_2 A_2)^{-1} \big[\alpha_1 (I - \alpha_2 A_1) (I + \alpha_1 A_1)^{-1} +
  \alpha_2 I\big] b.$$

**Correction.** The source prints $f = [\alpha_1 (I - \alpha_2 A_1) (I + \alpha_1 A_1)^{-1} +
\alpha_2 I] b$, without the leading factor $(I + \alpha_2 A_2)^{-1}$. The composition of the two
half steps of (4.50) produces this factor, the same inverse that opens $B$
(`QuarteroniSaccoSaleri.Chapter04.adiStep_eq_affineStep`). -/
noncomputable def adiConst (b : Fin n → ℝ) : Fin n → ℝ :=
  ((1 + α₂ • A₂)⁻¹ * (α₁ • ((1 - α₂ • A₁) * (1 + α₁ • A₁)⁻¹) + α₂ • 1)) *ᵥ b

/-- **Section 4.3.6** of [quarteroni2000numerical], the display after (4.50). For all
$A_1, A_2 \in \mathbb{R}^{n \times n}$ and all parameters $\alpha_1, \alpha_2$, the
alternating-direction method is the linear iterative method (4.2), $x \mapsto Bx + f$, with the
matrix $B$ of `QuarteroniSaccoSaleri.Chapter04.adiMatrix` and the vector $f$ of
`QuarteroniSaccoSaleri.Chapter04.adiConst`.

The identity is algebraic. It holds with Mathlib's inverses also when a shifted matrix
$I + \alpha_i A_i$ is singular. -/
theorem adiStep_eq_affineStep (b : Fin n → ℝ) :
    adiStep A₁ A₂ α₁ α₂ b = affineStep (adiMatrix A₁ A₂ α₁ α₂) (adiConst A₁ A₂ α₁ α₂ b) := by
  funext x
  simp only [adiStep, affineStep, adiMatrix, adiConst, mulVec_add, mulVec_smul, mulVec_mulVec,
    Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, add_mulVec, smul_mulVec, Matrix.mul_assoc]
  abel

/-- Over any field, for $\alpha_1, \alpha_2 \neq 0$ and $r_i = 1/\alpha_i$, the iteration matrix of
the alternating-direction method is $B = (A_2 + r_2 I)^{-1} (A_1 - r_2 I) (A_1 + r_1 I)^{-1}
(A_2 - r_1 I)$. -/
private theorem adiMatrix_eq_general {𝕜 : Type*} [Field 𝕜] (A₁ A₂ : Matrix (Fin n) (Fin n) 𝕜)
    {α₁ α₂ : 𝕜} (h₁ : α₁ ≠ 0) (h₂ : α₂ ≠ 0) :
    (1 + α₂ • A₂)⁻¹ * (1 - α₂ • A₁) * (1 + α₁ • A₁)⁻¹ * (1 - α₁ • A₂) =
      (A₂ + α₂⁻¹ • 1)⁻¹ * (A₁ - α₂⁻¹ • 1) * (A₁ + α₁⁻¹ • 1)⁻¹ * (A₂ - α₁⁻¹ • 1) := by
  have e1 : (1 : Matrix (Fin n) (Fin n) 𝕜) + α₂ • A₂ = α₂ • (A₂ + α₂⁻¹ • 1) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ h₂, one_smul, add_comm]
  have e2 : (1 : Matrix (Fin n) (Fin n) 𝕜) - α₂ • A₁ = (-α₂) • (A₁ - α₂⁻¹ • 1) := by
    rw [smul_sub, smul_smul, neg_mul, mul_inv_cancel₀ h₂]
    module
  have e3 : (1 : Matrix (Fin n) (Fin n) 𝕜) + α₁ • A₁ = α₁ • (A₁ + α₁⁻¹ • 1) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ h₁, one_smul, add_comm]
  have e4 : (1 : Matrix (Fin n) (Fin n) 𝕜) - α₁ • A₂ = (-α₁) • (A₂ - α₁⁻¹ • 1) := by
    rw [smul_sub, smul_smul, neg_mul, mul_inv_cancel₀ h₁]
    module
  rw [e1, e2, e3, e4, inv_smul_eq h₂, inv_smul_eq h₁]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [show -α₁ * (α₁⁻¹ * (-α₂ * α₂⁻¹)) = 1 by field_simp, one_smul]

/-- Over any field, for $\alpha_1, \alpha_2 \neq 0$ and $r_i = 1/\alpha_i$, the matrix of the vector
$f$ of the alternating-direction method is $(A_2 + r_2 I)^{-1} (I - (A_1 - r_2 I)(A_1 + r_1
I)^{-1})$. -/
private theorem adiConst_eq_general {𝕜 : Type*} [Field 𝕜] (A₁ A₂ : Matrix (Fin n) (Fin n) 𝕜)
    {α₁ α₂ : 𝕜} (h₁ : α₁ ≠ 0) (h₂ : α₂ ≠ 0) :
    (1 + α₂ • A₂)⁻¹ * (α₁ • ((1 - α₂ • A₁) * (1 + α₁ • A₁)⁻¹) + α₂ • 1) =
      (A₂ + α₂⁻¹ • 1)⁻¹ * (1 - (A₁ - α₂⁻¹ • 1) * (A₁ + α₁⁻¹ • 1)⁻¹) := by
  have e1 : (1 : Matrix (Fin n) (Fin n) 𝕜) + α₂ • A₂ = α₂ • (A₂ + α₂⁻¹ • 1) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ h₂, one_smul, add_comm]
  have e2 : (1 : Matrix (Fin n) (Fin n) 𝕜) - α₂ • A₁ = (-α₂) • (A₁ - α₂⁻¹ • 1) := by
    rw [smul_sub, smul_smul, neg_mul, mul_inv_cancel₀ h₂]
    module
  have e3 : (1 : Matrix (Fin n) (Fin n) 𝕜) + α₁ • A₁ = α₁ • (A₁ + α₁⁻¹ • 1) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ h₁, one_smul, add_comm]
  rw [e1, e2, e3, inv_smul_eq h₂, inv_smul_eq h₁]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_add, Matrix.mul_sub,
    Matrix.mul_one]
  rw [show α₁ * (α₁⁻¹ * -α₂) * α₂⁻¹ = -1 by field_simp, show α₂ * α₂⁻¹ = 1 by field_simp]
  module

/-- Over $\mathbb{R}$ or $\mathbb{C}$, if $r_1, r_2 \neq 0$ and $A_i + r_i I$ is nonsingular for
$i = 1, 2$, then the iteration matrix with $\alpha_i = 1/r_i$ acts on Euclidean space as the
backbone's `Stationary.peacemanRachfordTwo` with the parameters $r_1$ and $r_2$. -/
private theorem toEuclideanCLM_adiMatrix_general {𝕜 : Type*} [RCLike 𝕜]
    (A₁ A₂ : Matrix (Fin n) (Fin n) 𝕜) {r₁ r₂ : ℝ} (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0)
    (hu₁ : IsUnit (A₁ + (r₁ : 𝕜) • (1 : Matrix (Fin n) (Fin n) 𝕜)))
    (hu₂ : IsUnit (A₂ + (r₂ : 𝕜) • (1 : Matrix (Fin n) (Fin n) 𝕜))) :
    toEuclideanCLM (n := Fin n) (𝕜 := 𝕜) ((1 + (r₂ : 𝕜)⁻¹ • A₂)⁻¹ * (1 - (r₂ : 𝕜)⁻¹ • A₁) *
        (1 + (r₁ : 𝕜)⁻¹ • A₁)⁻¹ * (1 - (r₁ : 𝕜)⁻¹ • A₂)) =
      peacemanRachfordTwo (toEuclideanCLM (n := Fin n) (𝕜 := 𝕜) A₁)
        (toEuclideanCLM (n := Fin n) (𝕜 := 𝕜) A₂) r₁ r₂ := by
  have h₁' : ((r₁ : 𝕜))⁻¹ ≠ 0 := inv_ne_zero (RCLike.ofReal_ne_zero.mpr h₁)
  have h₂' : ((r₂ : 𝕜))⁻¹ ≠ 0 := inv_ne_zero (RCLike.ofReal_ne_zero.mpr h₂)
  rw [adiMatrix_eq_general A₁ A₂ h₁' h₂', inv_inv, inv_inv, peacemanRachfordTwo, map_mul, map_mul,
    map_mul, toEuclideanCLM_nonsing_inv hu₂, toEuclideanCLM_nonsing_inv hu₁,
    toEuclideanCLM_add_smul_one, toEuclideanCLM_add_smul_one, toEuclideanCLM_sub_smul_one,
    toEuclideanCLM_sub_smul_one]

/-- Over $\mathbb{R}$ or $\mathbb{C}$, under the hypotheses of the previous lemma, the vector $f$
with $\alpha_i = 1/r_i$ is the backbone's `Stationary.peacemanRachfordTwoConst` applied to $b$. -/
private theorem toEuclideanCLM_adiConst_general {𝕜 : Type*} [RCLike 𝕜]
    (A₁ A₂ : Matrix (Fin n) (Fin n) 𝕜) {r₁ r₂ : ℝ} (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0)
    (hu₁ : IsUnit (A₁ + (r₁ : 𝕜) • (1 : Matrix (Fin n) (Fin n) 𝕜)))
    (hu₂ : IsUnit (A₂ + (r₂ : 𝕜) • (1 : Matrix (Fin n) (Fin n) 𝕜))) (b : Fin n → 𝕜) :
    toEuclideanCLM (n := Fin n) (𝕜 := 𝕜) ((1 + (r₂ : 𝕜)⁻¹ • A₂)⁻¹ *
        ((r₁ : 𝕜)⁻¹ • ((1 - (r₂ : 𝕜)⁻¹ • A₁) * (1 + (r₁ : 𝕜)⁻¹ • A₁)⁻¹) + (r₂ : 𝕜)⁻¹ • 1))
        (toLp 2 b) =
      peacemanRachfordTwoConst (toEuclideanCLM (n := Fin n) (𝕜 := 𝕜) A₁)
        (toEuclideanCLM (n := Fin n) (𝕜 := 𝕜) A₂) r₁ r₂ (toLp 2 b) := by
  have h₁' : ((r₁ : 𝕜))⁻¹ ≠ 0 := inv_ne_zero (RCLike.ofReal_ne_zero.mpr h₁)
  have h₂' : ((r₂ : 𝕜))⁻¹ ≠ 0 := inv_ne_zero (RCLike.ofReal_ne_zero.mpr h₂)
  rw [adiConst_eq_general A₁ A₂ h₁' h₂', inv_inv, inv_inv, peacemanRachfordTwoConst, map_mul,
    map_sub, map_mul, map_one, toEuclideanCLM_nonsing_inv hu₂, toEuclideanCLM_nonsing_inv hu₁,
    toEuclideanCLM_add_smul_one, toEuclideanCLM_add_smul_one, toEuclideanCLM_sub_smul_one,
    mul_apply_eq_comp]

/-- For a symmetric positive definite matrix $A$ and $r > 0$, the matrix $A + rI$ is nonsingular. -/
private theorem isUnit_add_smul_one_of_posDef {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {r : ℝ} (hr : 0 < r) : IsUnit (A + r • (1 : Matrix (Fin n) (Fin n) ℝ)) :=
  (hA.add (Matrix.PosDef.one.smul hr)).isUnit

/-- **Equation (4.50)** of [quarteroni2000numerical], the identification with the backbone. Let
$A_1, A_2 \in \mathbb{R}^{n \times n}$ be symmetric positive definite and let
$\alpha_1, \alpha_2 > 0$. Then the iteration matrix $B$ of the alternating-direction method acts
on `EuclideanSpace ℝ (Fin n)` as the backbone's two-parameter Peaceman–Rachford operator with
the parameters $r_i = 1/\alpha_i$, and the vector $f$ is the affine part of that operator
applied to $b$.

The operator is `Stationary.peacemanRachfordTwo` and its affine part is
`Stationary.peacemanRachfordTwoConst`. The matrices act through `Matrix.toEuclideanCLM`. -/
theorem equation_4_50 (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    (b : Fin n → ℝ) :
    toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (adiMatrix A₁ A₂ α₁ α₂) =
        peacemanRachfordTwo (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A₁)
          (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A₂) (1 / α₁) (1 / α₂) ∧
      (toLp 2 (adiConst A₁ A₂ α₁ α₂ b) : EuclideanSpace ℝ (Fin n)) =
        peacemanRachfordTwoConst (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A₁)
          (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A₂) (1 / α₁) (1 / α₂) (toLp 2 b) := by
  have h₁ : (1 / α₁ : ℝ) ≠ 0 := one_div_ne_zero hα₁.ne'
  have h₂ : (1 / α₂ : ℝ) ≠ 0 := one_div_ne_zero hα₂.ne'
  have hu₁ := isUnit_add_smul_one_of_posDef hA₁ (one_div_pos.mpr hα₁)
  have hu₂ := isUnit_add_smul_one_of_posDef hA₂ (one_div_pos.mpr hα₂)
  have hinv : ∀ α : ℝ, ((1 / α : ℝ) : ℝ)⁻¹ = α := fun α => by rw [one_div, inv_inv]
  constructor
  · have h := toEuclideanCLM_adiMatrix_general A₁ A₂ h₁ h₂ hu₁ hu₂
    rw [RCLike.ofReal_real_eq_id, id_eq, id_eq, hinv, hinv] at h
    exact h
  · have h := toEuclideanCLM_adiConst_general A₁ A₂ h₁ h₂ hu₁ hu₂ b
    rw [RCLike.ofReal_real_eq_id, id_eq, id_eq, hinv, hinv] at h
    rw [adiConst, ← toEuclideanCLM_toLp]
    exact h

/-- For $t, \alpha_1, \alpha_2 > 0$: $|t - 1/\alpha_2| / (t + 1/\alpha_1) = (\alpha_1/\alpha_2) \,
|1 - \alpha_2 t| / (1 + \alpha_1 t)$.
-/
private theorem abs_sub_div_add_eq {t : ℝ} (ht : 0 < t) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    |t - 1 / α₂| / (t + 1 / α₁) = α₁ / α₂ * (|1 - α₂ * t| / (1 + α₁ * t)) := by
  have h1 : |t - 1 / α₂| * α₂ = |1 - α₂ * t| := by
    have h : |t - 1 / α₂| * α₂ = |(t - 1 / α₂) * α₂| := by
      rw [abs_mul, abs_of_pos hα₂]
    rw [h, abs_sub_comm 1 (α₂ * t)]
    congr 1
    field_simp
  have ht1 : t + 1 / α₁ ≠ 0 := by positivity
  have ht2 : 1 + α₁ * t ≠ 0 := by positivity
  rw [← h1]
  field_simp
  ring

/-- **Section 4.3.6** of [quarteroni2000numerical], the estimate of $\rho(B)$. Let $n \ge 1$, let
$A_1, A_2 \in \mathbb{R}^{n \times n}$ be symmetric positive definite with eigenvalues
$\lambda_i^{(1)}$ and $\lambda_i^{(2)}$, and let $\alpha_1, \alpha_2 > 0$. Then the iteration
matrix $B$ of the alternating-direction method satisfies
$$\rho(B) \le \max_i \frac{|1 - \alpha_2 \lambda_i^{(1)}|}{1 + \alpha_1 \lambda_i^{(1)}} \cdot
  \max_i \frac{|1 - \alpha_1 \lambda_i^{(2)}|}{1 + \alpha_2 \lambda_i^{(2)}}.$$

The eigenvalues are `Matrix.IsHermitian.eigenvalues`, and the maxima are `Finset.sup'`. The
proof is the backbone's `Matrix.PosDef.complexSpectralRadius_peacemanRachfordTwo_le` at
$r_i = 1/\alpha_i$, which needs no commutativity of $A_1$ and $A_2$. Its two factors differ from
those here by the constants $\alpha_1/\alpha_2$ and $\alpha_2/\alpha_1$, which cancel in the
product. -/
theorem adi_spectralRadius_le [NeZero n] (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef) (hα₁ : 0 < α₁)
    (hα₂ : 0 < α₂) :
    complexSpectralRadius (adiMatrix A₁ A₂ α₁ α₂) ≤ ENNReal.ofReal
      (univ.sup' univ_nonempty
          (fun i => |1 - α₂ * hA₁.1.eigenvalues i| / (1 + α₁ * hA₁.1.eigenvalues i)) *
        univ.sup' univ_nonempty
          (fun i => |1 - α₁ * hA₂.1.eigenvalues i| / (1 + α₂ * hA₂.1.eigenvalues i))) := by
  set M₁ := univ.sup' univ_nonempty
    fun i => |1 - α₂ * hA₁.1.eigenvalues i| / (1 + α₁ * hA₁.1.eigenvalues i) with hM₁
  set M₂ := univ.sup' univ_nonempty
    fun i => |1 - α₁ * hA₂.1.eigenvalues i| / (1 + α₂ * hA₂.1.eigenvalues i) with hM₂
  have hM₁0 : 0 ≤ M₁ := by
    refine le_trans ?_ (Finset.le_sup'
      (fun i => |1 - α₂ * hA₁.1.eigenvalues i| / (1 + α₁ * hA₁.1.eigenvalues i))
      (mem_univ (0 : Fin n)))
    exact div_nonneg (abs_nonneg _) (by linarith [mul_pos hα₁ (hA₁.eigenvalues_pos 0)])
  have hM₂0 : 0 ≤ M₂ := by
    refine le_trans ?_ (Finset.le_sup'
      (fun i => |1 - α₁ * hA₂.1.eigenvalues i| / (1 + α₂ * hA₂.1.eigenvalues i))
      (mem_univ (0 : Fin n)))
    exact div_nonneg (abs_nonneg _) (by linarith [mul_pos hα₂ (hA₂.eigenvalues_pos 0)])
  have hbound : ∀ {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) {β γ : ℝ}, 0 < β → 0 < γ →
      ∀ t ∈ spectrum ℝ A, |t - γ⁻¹| / (t + β⁻¹) ≤ β / γ * univ.sup' univ_nonempty
          (fun i => |1 - γ * hA.1.eigenvalues i| / (1 + β * hA.1.eigenvalues i)) := by
    intro A hA β γ hβ hγ t ht
    rw [hA.1.spectrum_real_eq_range_eigenvalues] at ht
    obtain ⟨i, rfl⟩ := ht
    rw [← one_div, ← one_div, abs_sub_div_add_eq β γ (hA.eigenvalues_pos i) hβ hγ]
    exact mul_le_mul_of_nonneg_left (Finset.le_sup'
      (fun i => |1 - γ * hA.1.eigenvalues i| / (1 + β * hA.1.eigenvalues i)) (mem_univ i))
      (div_pos hβ hγ).le
  rw [adiMatrix, adiMatrix_eq_general A₁ A₂ hα₁.ne' hα₂.ne',
    show M₁ * M₂ = (α₁ / α₂ * M₁) * (α₂ / α₁ * M₂) by field_simp]
  exact hA₁.complexSpectralRadius_peacemanRachfordTwo_le hA₂ (inv_pos.mpr hα₁)
    (inv_pos.mpr hα₂) (mul_nonneg (div_pos hα₁ hα₂).le hM₁0) (mul_nonneg (div_pos hα₂ hα₁).le hM₂0)
    (hbound hA₁ hα₁ hα₂) (hbound hA₂ hα₂ hα₁)

/-- **Section 4.3.6** of [quarteroni2000numerical], convergence for equal parameters. Let
$A_1, A_2 \in \mathbb{R}^{n \times n}$ be symmetric positive definite, let $\alpha > 0$, and let
$(A_1 + A_2) x = b$. Then the alternating-direction method with $\alpha_1 = \alpha_2 = \alpha$
converges to $x$ from every $x^{(0)}$. The source states that the method converges if
$\rho(B) < 1$, which always holds if $\alpha_1 = \alpha_2 = \alpha > 0$.

The proof is the backbone's `Stationary.tendsto_peacemanRachford` through
`QuarteroniSaccoSaleri.Chapter04.equation_4_50`. The backbone uses only the coercivity of $A_1$
and $A_2$, neither their symmetry nor their commutativity. -/
theorem adi_tendsto (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef) {α : ℝ} (hα : 0 < α)
    {b x : Fin n → ℝ} (hx : (A₁ + A₂) *ᵥ x = b) (x₀ : Fin n → ℝ) :
    Tendsto (fun k => (adiStep A₁ A₂ α α b)^[k] x₀) atTop (𝓝 x) := by
  obtain ⟨hB, hf⟩ := equation_4_50 A₁ A₂ α α hA₁ hA₂ hα hα b
  rw [peacemanRachfordTwo_self] at hB
  rw [peacemanRachfordTwoConst_self] at hf
  have hH : ((toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A₁ :
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsCoercive := by
    rw [coe_toEuclideanCLM_eq_toEuclideanLin]
    exact (posDef_isSymmetricCoercive_toEuclideanLin hA₁).isCoercive
  have hV : ((toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A₂ :
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsCoercive := by
    rw [coe_toEuclideanCLM_eq_toEuclideanLin]
    exact (posDef_isSymmetricCoercive_toEuclideanLin hA₂).isCoercive
  have hx' : (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A₁ + toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A₂)
      (toLp 2 x) = toLp 2 b := by
    rw [← map_add, toEuclideanCLM_toLp, hx]
  have h := tendsto_peacemanRachford hH hV (one_div_pos.mpr hα) hx' (toLp 2 x₀)
  simp only [← hB, ← hf, ← toLp_affineStep_iterate, ← adiStep_eq_affineStep] at h
  have h' := (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin n => ℝ)).tendsto _ |>.comp h
  simpa [Function.comp_def] using h'

/-- **Section 4.3.6** of [quarteroni2000numerical], the last display. Let
$A_1, A_2 \in \mathbb{R}^{n \times n}$ be symmetric positive definite with all their eigenvalues
in $[\gamma, \delta]$, where $0 < \gamma \le \delta$. With
$\alpha_1 = \alpha_2 = 1/\sqrt{\delta\gamma}$, the iteration matrix of the alternating-direction
method satisfies
$$\rho(B) \le \Big(\frac{1 - \sqrt{\gamma/\delta}}{1 + \sqrt{\gamma/\delta}}\Big)^2.$$

**Reading.** The source adds the proviso "provided $\gamma/\delta$ tends to $0$ as the size of
$A$ grows". The proviso is not a hypothesis of the inequality.

The eigenvalues are `Matrix.IsHermitian.eigenvalues`. The proof is the backbone's
`Matrix.IsHermitian.complexSpectralRadius_peacemanRachford_le_of_spectrum_subset`. -/
theorem adi_spectralRadius_le_sq (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef) {γ δ : ℝ} (hγ : 0 < γ)
    (hγδ : γ ≤ δ) (h₁ : ∀ i, hA₁.1.eigenvalues i ∈ Set.Icc γ δ)
    (h₂ : ∀ i, hA₂.1.eigenvalues i ∈ Set.Icc γ δ) :
    complexSpectralRadius (adiMatrix A₁ A₂ (1 / √(δ * γ)) (1 / √(δ * γ))) ≤
      ENNReal.ofReal (((1 - √(γ / δ)) / (1 + √(γ / δ))) ^ 2) := by
  have hr : 0 < 1 / √(δ * γ) := one_div_pos.mpr (Real.sqrt_pos.mpr (mul_pos (hγ.trans_le hγδ) hγ))
  have hsub : ∀ {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian),
      (∀ i, hA.eigenvalues i ∈ Set.Icc γ δ) → spectrum ℝ A ⊆ Set.Icc γ δ := by
    intro A hA h
    rw [hA.spectrum_real_eq_range_eigenvalues]
    rintro _ ⟨i, rfl⟩
    exact h i
  have hc : (1 / √(δ * γ))⁻¹ = √(γ * δ) := by rw [one_div, inv_inv, mul_comm]
  rw [adiMatrix, adiMatrix_eq_general A₁ A₂ hr.ne' hr.ne', hc]
  exact hA₁.1.complexSpectralRadius_peacemanRachford_le_of_spectrum_subset hA₂.1 hγ hγδ
    (hsub hA₁.1 h₁) (hsub hA₂.1 h₂)

end ADI


end QuarteroniSaccoSaleri.Chapter04
