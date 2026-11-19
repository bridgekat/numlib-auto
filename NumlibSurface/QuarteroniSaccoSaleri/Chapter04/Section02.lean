/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Direct.Substitution
import Numlib.FloatingPoint.Stationary
import Numlib.LinearAlgebra.Matrix.HermitianPart
import Numlib.LinearAlgebra.Matrix.PosDef
import Numlib.Stationary.Block
import Numlib.Stationary.ConsistentlyOrdered
import Numlib.Stationary.DiagDominant
import Numlib.Stationary.SPD
import Numlib.Stationary.Sweep
import NumlibSurface.QuarteroniSaccoSaleri.Chapter04.Section01

/-!
# Quarteroni, Sacco and Saleri, Section 4.2: Linear iterative methods

This module formalizes Section 4.2 of [quarteroni2000numerical], on the linear iterative methods
that come from a splitting $A = P - N$ of a matrix $A \in \mathbb{R}^{n \times n}$ with $P$
nonsingular: $P x^{(k+1)} = N x^{(k)} + b$ (4.6), with iteration matrix $B = P^{-1} N$. With
$A = D - E - F$, where $D$ is the diagonal part of $A$ and $-E$ and $-F$ are its strictly lower and
strictly upper parts, the Jacobi, JOR, Gauss–Seidel and SOR methods are the splittings $P = D$,
$P = \omega^{-1} D$, $P = D - E$ and $P = \omega^{-1} D - E$ (Section 4.2.1). Properties 4.1 and 4.2
give conditions on $P$ for the convergence of the iteration of a splitting of a symmetric positive
definite matrix. Sections 4.2.2 and 4.2.3 give convergence results: for strictly diagonally dominant
matrices (Theorem 4.2), for symmetric positive definite matrices (Theorems 4.3 to 4.5 and Property
4.3), for consistently ordered matrices (relation (4.18) and Property 4.4, with the optimal
relaxation parameter), and Kahan's bound $\rho(B(\omega)) \ge |\omega - 1|$ (Theorem 4.7). Section
4.2.4 decomposes the error of an iteration with rounding errors (4.20), Section 4.2.5 extends
Theorem 4.3 to block Jacobi, and Section 4.2.6 treats the symmetric Gauss–Seidel and SSOR methods.

The proofs specialize the backbone modules `Numlib.Stationary.Splitting` (splittings $A = P - N$ and
the Jacobi, JOR, Gauss–Seidel, SOR and SSOR splittings), `Numlib.Stationary.Sweep` (the
componentwise sweeps and their identification with the splitting steps), `Numlib.Stationary.SPD`
(the Householder–John theorem, the energy-norm theory for symmetric positive definite matrices, and
Kahan's bound), `Numlib.Stationary.DiagDominant` (strict diagonal dominance),
`Numlib.Stationary.ConsistentlyOrdered` (Young's theory of SOR) and `Numlib.Stationary.Block` (block
Jacobi).

## Main definitions

* Section 4.2, `QuarteroniSaccoSaleri.Chapter04.Splitting`: a splitting $A = P - N$ with $P$
  nonsingular.
* Section 4.2.1, `QuarteroniSaccoSaleri.Chapter04.D`, `QuarteroniSaccoSaleri.Chapter04.E`,
  `QuarteroniSaccoSaleri.Chapter04.F`: the diagonal part of $A$ and the negatives of its strictly
  lower and strictly upper parts.
* Definition 4.3, `QuarteroniSaccoSaleri.Chapter04.definition_4_3`: the $A$-property.
* Example 4.3, `QuarteroniSaccoSaleri.Chapter04.example_4_3_matrix`: the lower bidiagonal matrix of
  the example.
* Equation (4.20), `QuarteroniSaccoSaleri.Chapter04.perturbedIterate`: the sequence computed with
  rounding errors $\zeta_k$.

## Main results

* Equation (4.6), `QuarteroniSaccoSaleri.Chapter04.equation_4_6`: the iteration of a splitting is
  the method (4.2) with $B = P^{-1} N$ and $f = P^{-1} b$.
* Equations (4.7) and (4.8), `QuarteroniSaccoSaleri.Chapter04.equation_4_7`: the step is
  $x + P^{-1} r$, and its fixed points are the solutions of $Ax = b$.
* Section 4.2, `QuarteroniSaccoSaleri.Chapter04.Splitting.consistent`: the iteration of a splitting
  is consistent.
* Theorem 4.1, `QuarteroniSaccoSaleri.Chapter04.Splitting.tendsto` and
  `QuarteroniSaccoSaleri.Chapter04.Splitting.forall_tendsto_iff`: the iteration of a splitting
  converges for all $b$ and $x^{(0)}$ if and only if $\rho(P^{-1} N) < 1$.
* Property 4.1, `QuarteroniSaccoSaleri.Chapter04.property_4_1_spectralRadius_lt_one`,
  `QuarteroniSaccoSaleri.Chapter04.property_4_1_energyNorm`,
  `QuarteroniSaccoSaleri.Chapter04.property_4_1_monotone`: for $A$, $P$ and $2P - A$ symmetric
  positive definite, $\rho(B) < 1$, $\rho(B) = \|B\|_A = \|B\|_P$, and the convergence is monotone
  in both energy norms.
* Property 4.2, `QuarteroniSaccoSaleri.Chapter04.property_4_2_isUnit`,
  `QuarteroniSaccoSaleri.Chapter04.property_4_2`,
  `QuarteroniSaccoSaleri.Chapter04.property_4_2_monotone`: for $A$ and $P + P^T - A$ positive
  definite, $P$ is nonsingular, $\rho(B) \le \|B\|_A < 1$, and the convergence is monotone in
  $\|\cdot\|_A$.
* Section 4.2.1, `QuarteroniSaccoSaleri.Chapter04.decomp`: $A = D - E - F$.
* Equations (4.9) to (4.11), `QuarteroniSaccoSaleri.Chapter04.equation_4_10`: the Jacobi method.
* Equation (4.12), `QuarteroniSaccoSaleri.Chapter04.equation_4_12`: the JOR method.
* Equations (4.13) and (4.14), `QuarteroniSaccoSaleri.Chapter04.equation_4_13`: the Gauss–Seidel
  method.
* Equation (4.15), `QuarteroniSaccoSaleri.Chapter04.equation_4_15`: the SOR method, componentwise.
* Equation (4.16), `QuarteroniSaccoSaleri.Chapter04.equation_4_16`: the SOR method in vector form.
* Equation (4.17), `QuarteroniSaccoSaleri.Chapter04.equation_4_17`: the SOR iteration matrix
  $B(\omega)$.
* Section 4.2.1, `QuarteroniSaccoSaleri.Chapter04.sor_step_eq_add_inv_mulVec`: the SOR method in the
  form (4.7).
* Theorem 4.2, `QuarteroniSaccoSaleri.Chapter04.theorem_4_2_jacobi`,
  `QuarteroniSaccoSaleri.Chapter04.theorem_4_2_jacobi_linfty`,
  `QuarteroniSaccoSaleri.Chapter04.theorem_4_2_gaussSeidel`: for a strictly diagonally dominant $A$,
  the Jacobi and the Gauss–Seidel methods converge.
* Theorem 4.3, `QuarteroniSaccoSaleri.Chapter04.theorem_4_3` and
  `QuarteroniSaccoSaleri.Chapter04.theorem_4_3_energyNorm`: for $A$ and $2D - A$ symmetric positive
  definite, the Jacobi method converges, and $\rho(B_J) = \|B_J\|_A = \|B_J\|_D$.
* Theorem 4.4, `QuarteroniSaccoSaleri.Chapter04.theorem_4_4` and
  `QuarteroniSaccoSaleri.Chapter04.theorem_4_4_iff`: for $A$ symmetric positive definite, the JOR
  method converges if and only if $0 < \omega < 2 / \rho(D^{-1} A)$.
* Theorem 4.5, `QuarteroniSaccoSaleri.Chapter04.theorem_4_5`: for $A$ symmetric positive definite,
  the Gauss–Seidel method converges monotonically in $\|\cdot\|_A$.
* Equation (4.18), `QuarteroniSaccoSaleri.Chapter04.equation_4_18`: for $A$ positive definite and
  tridiagonal, the Jacobi method converges and $\rho(B_{GS}) = \rho(B_J)^2$.
* Definition 4.3, `QuarteroniSaccoSaleri.Chapter04.definition_4_3_iff`: the consistent-ordering
  clause in the letters of the book.
* Equation (4.18), `QuarteroniSaccoSaleri.Chapter04.equation_4_18_of_hasAProperty`:
  $\rho(B_{GS}) = \rho(B_J)^2$ for a matrix with the $A$-property.
* Theorem 4.6, `QuarteroniSaccoSaleri.Chapter04.theorem_4_6`: if the Jacobi method converges, then
  JOR converges for $0 < \omega \le 1$.
* Theorem 4.7, `QuarteroniSaccoSaleri.Chapter04.theorem_4_7` and
  `QuarteroniSaccoSaleri.Chapter04.theorem_4_7_zero`: $\rho(B(\omega)) \ge |\omega - 1|$, so SOR
  diverges for $\omega \le 0$ or $\omega \ge 2$.
* Property 4.3, `QuarteroniSaccoSaleri.Chapter04.property_4_3` and
  `QuarteroniSaccoSaleri.Chapter04.property_4_3_diagDominant`: for $A$ symmetric positive definite,
  SOR converges if and only if $0 < \omega < 2$; for $A$ strictly diagonally dominant, SOR converges
  for $0 < \omega \le 1$.
* Property 4.4, `QuarteroniSaccoSaleri.Chapter04.property_4_4` and
  `QuarteroniSaccoSaleri.Chapter04.property_4_4_optimal`: for a matrix with the $A$-property and a
  Jacobi matrix with real eigenvalues, SOR converges if and only if $\rho(B_J) < 1$ and
  $0 < \omega < 2$, and (4.19) gives the optimal parameter.
* Example 4.3, `QuarteroniSaccoSaleri.Chapter04.example_4_3_solution` and
  `QuarteroniSaccoSaleri.Chapter04.example_4_3_spectralRadius`: the exact solution of the system,
  and $\rho(B(3/2)) = 1/2$.
* Equation (4.20), `QuarteroniSaccoSaleri.Chapter04.toLp_perturbedIterate`,
  `QuarteroniSaccoSaleri.Chapter04.equation_4_20_iterate`,
  `QuarteroniSaccoSaleri.Chapter04.equation_4_20`,
  `QuarteroniSaccoSaleri.Chapter04.equation_4_20_bound`: the closed form of the computed sequence,
  the error decomposition, and a bound on the rounding-error term.
* Section 4.2.5, `QuarteroniSaccoSaleri.Chapter04.theorem_4_3_block`: Theorem 4.3 for the block
  Jacobi method.
* Section 4.2.6, `QuarteroniSaccoSaleri.Chapter04.backwardGaussSeidel_step`: the backward
  Gauss–Seidel method.
* Equation (4.21), `QuarteroniSaccoSaleri.Chapter04.equation_4_21`: the symmetric Gauss–Seidel
  method.
* Property 4.5, `QuarteroniSaccoSaleri.Chapter04.property_4_5`: for $A$ symmetric positive definite,
  the symmetric Gauss–Seidel method converges, and $A B_{SGS}$ is symmetric positive semidefinite.
* Equation (4.22), `QuarteroniSaccoSaleri.Chapter04.equation_4_22`: the SSOR method.
* Section 4.2.6, `QuarteroniSaccoSaleri.Chapter04.ssor_tendsto`: for $A$ symmetric positive
  definite, SSOR converges for $0 < \omega < 2$.

## Conventions

* A splitting $A = P - N$ with $P$ nonsingular is `QuarteroniSaccoSaleri.Chapter04.Splitting A`, the
  backbone `Stationary.Splitting A`, with $P$ = `s.m` and $N$ = `s.n`. The iteration (4.6) is the
  step `Stationary.Splitting.mulVecStep s b`, and its iteration matrix is `s.iterationOperator`.
* The letters of Section 4.2.1 are `D A = diagPart A`, `E A = -strictLower A` and
  `F A = -strictUpper A`, so that $A = D - E - F$. The hypothesis "the diagonal entries of $A$ are
  nonzero" is `IsUnit (diagPart A)` (`Matrix.isUnit_diagPart_iff`).
* The Jacobi, JOR, Gauss–Seidel and SOR methods are the backbone sweeps `Matrix.jorSweep A 1 b`,
  `Matrix.jorSweep A ω b`, `Matrix.sorSweep A 1 b` and `Matrix.sorSweep A ω b`. The sweeps are
  defined by their matrix formulas. Their componentwise recursions (4.10), (4.13) and (4.15) are
  theorems, and each sweep is the step of its splitting.
* A convergence statement says: for every right-hand side $b$ and every $x^{(0)}$, the iterates tend
  to $A^{-1} b$. It is obtained from a bound on the spectral radius of the real iteration matrix
  (`Matrix.complexSpectralRadius`) through Theorem 4.1
  (`QuarteroniSaccoSaleri.Chapter04.Splitting.tendsto` and
  `QuarteroniSaccoSaleri.Chapter04.Splitting.forall_tendsto_iff`).
* Energy norms are written through the quadratic forms $\|e\|_A^2 = (Ae) \cdot e$.
  "$\|B\|_A = \rho(B)$" is the pair of statements $\|Be\|_A^2 \le \rho(B)^2 \|e\|_A^2$ for all $e$,
  with equality for some $e \neq 0$. "Monotone convergence in $\|\cdot\|_A$" is the strict decrease
  $\|Be\|_A < \|e\|_A$ for $e \neq 0$ along the error recursion $e^{(k+1)} = B e^{(k)}$ of (4.4).
* The matrices of the book have positive order. This is the hypothesis `[NeZero n]` of the
  statements whose existence clauses need it.

## Deviations from the source

* **Generalization.** Convergence of the splitting is characterized by spectral radius without
  separately assuming a nonsingular coefficient matrix. See
  `QuarteroniSaccoSaleri.Chapter04.Splitting.tendsto`,
  `QuarteroniSaccoSaleri.Chapter04.Splitting.forall_tendsto_iff`.
* **Generalization.** The energy-norm equalities do not need the extra contraction hypothesis. See
  `QuarteroniSaccoSaleri.Chapter04.property_4_1_energyNorm`,
  `QuarteroniSaccoSaleri.Chapter04.theorem_4_3_energyNorm`.
* **Correction.** The strict energy decreases are conditional on nonzero error. See
  `QuarteroniSaccoSaleri.Chapter04.property_4_1_monotone`,
  `QuarteroniSaccoSaleri.Chapter04.property_4_2_monotone`,
  `QuarteroniSaccoSaleri.Chapter04.theorem_4_5`, `QuarteroniSaccoSaleri.Chapter04.property_4_3`.
* **Scope.** The JOR and SOR splitting identities assume nonzero relaxation. See
  `QuarteroniSaccoSaleri.Chapter04.equation_4_12`, `QuarteroniSaccoSaleri.Chapter04.equation_4_15`,
  `QuarteroniSaccoSaleri.Chapter04.equation_4_17`.
* **Generalization.** The JOR convergence interval is also necessary for convergence for all data.
  See `QuarteroniSaccoSaleri.Chapter04.theorem_4_4_iff`.
* **Reading.** The A-property uses complex spectra and a contiguous two-block partition. See
  `QuarteroniSaccoSaleri.Chapter04.definition_4_3`,
  `QuarteroniSaccoSaleri.Chapter04.definition_4_3_iff`.
* **Reading.** Zero relaxation has a separate SOR identity, since the splitting is undefined there.
  See `QuarteroniSaccoSaleri.Chapter04.theorem_4_7`,
  `QuarteroniSaccoSaleri.Chapter04.theorem_4_7_zero`,
  `QuarteroniSaccoSaleri.Chapter04.property_4_4`.
* **Scope.** The optimal relaxation minimizes the spectral radius on the convergence interval. See
  `QuarteroniSaccoSaleri.Chapter04.property_4_4_optimal`.
* **Generalization.** The example bidiagonal matrix is available in arbitrary dimension. See
  `QuarteroniSaccoSaleri.Chapter04.example_4_3_matrix`.
* **Generalization.** The exact bidiagonal solution formula holds in every size. See
  `QuarteroniSaccoSaleri.Chapter04.example_4_3_mulVec`.
* **Scope.** The perturbed iterates use an abstract forcing sequence. See
  `QuarteroniSaccoSaleri.Chapter04.perturbedIterate`,
  `QuarteroniSaccoSaleri.Chapter04.equation_4_20_iterate`,
  `QuarteroniSaccoSaleri.Chapter04.equation_4_20`.
* **Derivation.** The forcing decomposition yields a geometric bound under Euclidean contraction.
  See `QuarteroniSaccoSaleri.Chapter04.equation_4_20_bound`.
* **Scope.** The block Jacobi result gives convergence for a general partition. See
  `QuarteroniSaccoSaleri.Chapter04.theorem_4_3_block`.
* **Correction.** The SGS matrix is self-adjoint and positive semidefinite in the coefficient energy
  inner product. See `QuarteroniSaccoSaleri.Chapter04.property_4_5`.
* **Property 4.1** (generalization). The energy-norm clauses need only $A$ and $P$ symmetric
  positive definite, not $2P - A$, and they are stated so. See
  `QuarteroniSaccoSaleri.Chapter04.property_4_1_energyNorm`.
* **Definition 4.3** (reading). The definition takes both consistent ordering and the printed
  $2 \times 2$ block form with diagonal blocks as hypotheses. It differs from Property A of Saad and
  Young. Only the first clause is used by (4.18) and Property 4.4. See
  `QuarteroniSaccoSaleri.Chapter04.definition_4_3`.
* **Theorem 4.7** (reading). The book states the theorem for any $\omega \in \mathbb{R}$. The SOR
  splitting needs $\omega \neq 0$; at $\omega = 0$ the SOR matrix is the identity, with spectral
  radius $1 = |0 - 1|$. See `QuarteroniSaccoSaleri.Chapter04.theorem_4_7` and
  `QuarteroniSaccoSaleri.Chapter04.theorem_4_7_zero`.
* **Property 4.5** (correction). The book says that $B_{SGS}$ is symmetric positive definite. This
  is false: for a diagonal $A$, $B_{SGS} = 0$, and in general $B_{SGS}$ is not symmetric. The
  statement is that $A B_{SGS}$ is symmetric positive semidefinite. See
  `QuarteroniSaccoSaleri.Chapter04.property_4_5`.

## Not formalized

* **Example 4.2**, a table of numerically computed spectral radii.
* **Programs 15 and 16.** The sweeps that they implement are `Matrix.jorSweep` and
  `Matrix.sorSweep`.
* **Example 4.3, the divergence of Program 16** in floating-point arithmetic. It is a numerical
  experiment.
* **Section 4.2.4, the analysis of the propagated rounding error**, which the book leaves to a paper
  of Higham. Only its simplest form, `QuarteroniSaccoSaleri.Chapter04.equation_4_20_bound`, is
  formalized.
* **Section 4.2.6, the comparison of SSOR with SOR and the choice of $\omega$.** They are prose.
-/

open Filter Finset Matrix Stationary Topology WithLp
open scoped ENNReal NNReal

namespace QuarteroniSaccoSaleri.Chapter04

variable {n : ℕ}

/-! ### Splittings, equations (4.6) and (4.7), and Theorem 4.1 for them -/

/-- **Section 4.2** of [quarteroni2000numerical], the splitting. A **splitting** $A = P - N$ of
$A \in \mathbb{R}^{n \times n}$ consists of a nonsingular matrix $P$, the preconditioning matrix
or preconditioner, and $N = P - A$.

This is the backbone `Stationary.Splitting A`, with $P$ = `s.m` and $N$ = `s.n`. -/
abbrev Splitting (A : Matrix (Fin n) (Fin n) ℝ) := Stationary.Splitting A

variable {A : Matrix (Fin n) (Fin n) ℝ}

/-- **Equation (4.6)** of [quarteroni2000numerical]. Let $A = P - N$ be a splitting, and let
$b, x \in \mathbb{R}^n$. The step $y$ of the iteration $P x^{(k+1)} = N x^{(k)} + b$ from $x$
satisfies $Py = Nx + b$. It is the step of the method (4.2) with iteration matrix $B = P^{-1} N$
and $f = P^{-1} b$.

The step is `Stationary.Splitting.mulVecStep s b`, and $B$ is `s.iterationOperator`. -/
theorem equation_4_6 (s : Splitting A) (b x : Fin n → ℝ) :
    A = s.m - s.n ∧ s.m *ᵥ (s.mulVecStep b x) = s.n *ᵥ x + b ∧
      s.mulVecStep b x = affineStep s.iterationOperator (s.m⁻¹ *ᵥ b) x ∧
      s.iterationOperator = s.m⁻¹ * s.n := by
  refine ⟨s.m_sub_n.symm, mulVec_nonsing_inv_mulVec s.isUnit _,
    s.mulVecStep_eq_iterationOperator_mulVec_add b x, ?_⟩
  rw [s.iterationOperator_eq, nonsing_inv_eq_ringInverse]

/-- **Equations (4.7) and (4.8)** of [quarteroni2000numerical]. Let $A = P - N$ be a splitting, and
let $b, x \in \mathbb{R}^n$. The step of (4.6) from $x$ is the update
$$x + P^{-1} r, \qquad r = b - Ax,$$
by the preconditioned residual. The method is consistent: $x$ is a fixed point of the step if
and only if $Ax = b$. -/
theorem equation_4_7 (s : Splitting A) (b x : Fin n → ℝ) :
    s.mulVecStep b x = x + s.m⁻¹ *ᵥ (b - A *ᵥ x) ∧ (s.mulVecStep b x = x ↔ A *ᵥ x = b) :=
  ⟨s.mulVecStep_eq_add_inv_mulVec b x, s.mulVecStep_fixed_iff b x⟩

/-- **Section 4.2** of [quarteroni2000numerical], consistency of a splitting. Let $A = P - N$ be a
splitting with $A$ nonsingular, and let $b \in \mathbb{R}^n$. Then the iteration
$x \mapsto P^{-1} N x + P^{-1} b$ is consistent with $Ax = b$ in the sense of Definition 4.1:
$A^{-1} b$ is a fixed point. -/
theorem Splitting.consistent (s : Splitting A) (hA : IsUnit A) (b : Fin n → ℝ) :
    definition_4_1 A b s.iterationOperator (s.m⁻¹ *ᵥ b) := by
  have h := (s.mulVecStep_fixed_iff b (A⁻¹ *ᵥ b)).mpr (mulVec_nonsing_inv_mulVec hA b)
  rw [s.mulVecStep_eq_iterationOperator_mulVec_add] at h
  exact h.symm

/-- **Theorem 4.1** of [quarteroni2000numerical] for a splitting, the sufficiency. Let $A = P - N$
be a splitting with $\rho(P^{-1} N) < 1$. Then for every $b, x^{(0)} \in \mathbb{R}^n$ the
iteration (4.6) converges to $A^{-1} b$.

The matrix $A$ is then nonsingular, so the hypothesis of Theorem 4.1 that $A$ is nonsingular is
not needed.

**Generalization.** The convergence criterion applies directly to a splitting, including without a
separate nonsingularity hypothesis on $A$. Spectral radius below one already implies nonsingularity
for such a splitting. The equivalence quantifies over all right-hand sides and starting vectors.
-/
theorem Splitting.tendsto (s : Splitting A) (hs : complexSpectralRadius s.iterationOperator < 1)
    (b x₀ : Fin n → ℝ) :
    Tendsto (fun k => (s.mulVecStep b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) := by
  have hstep : s.mulVecStep b = affineStep s.iterationOperator (s.m⁻¹ *ᵥ b) :=
    funext fun x => s.mulVecStep_eq_iterationOperator_mulVec_add b x
  rw [hstep]
  exact (theorem_4_1 (s.consistent (s.isUnit_of_complexSpectralRadius_lt_one hs) b)).2 hs x₀

/-- **Theorem 4.1** of [quarteroni2000numerical] for a splitting. Let $A = P - N$ be a splitting.
The iteration (4.6) converges to $A^{-1} b$ for every $b$ and every $x^{(0)}$ if and only if
$\rho(P^{-1} N) < 1$.

**Generalization.** The convergence criterion applies directly to a splitting, including without a
separate nonsingularity hypothesis on $A$. Spectral radius below one already implies nonsingularity
for such a splitting. The equivalence quantifies over all right-hand sides and starting vectors.
-/
theorem Splitting.forall_tendsto_iff (s : Splitting A) :
    (∀ b x₀, Tendsto (fun k => (s.mulVecStep b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b))) ↔
      complexSpectralRadius s.iterationOperator < 1 := by
  refine ⟨fun h => ?_, fun hs b x₀ => s.tendsto hs b x₀⟩
  have hstep : s.mulVecStep 0 = affineStep s.iterationOperator (s.m⁻¹ *ᵥ 0) :=
    funext fun x => s.mulVecStep_eq_iterationOperator_mulVec_add 0 x
  refine complexSpectralRadius_lt_one_of_forall_tendsto (x := A⁻¹ *ᵥ 0) (f := s.m⁻¹ *ᵥ 0)
    fun x₀ => ?_
  rw [← hstep]
  exact h 0 x₀

/-! ### Properties 4.1 and 4.2 -/

section SPD

/-- For a symmetric $P$, the Householder–John matrix $P + P^T - A$ is $2P - A$. -/
private theorem add_transpose_sub_of_isHermitian {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : P.IsHermitian) : P + Pᵀ - A = 2 • P - A := by
  rw [← conjTranspose_eq_transpose_of_trivial, hP.eq, two_smul]

/-- **Property 4.1** of [quarteroni2000numerical], convergence. Let $A = P - N$ be a splitting with
$A$ and $P$ symmetric positive definite. If $2P - A$ is positive definite, then $\rho(B) < 1$
for $B = P^{-1} N$, and the iteration (4.7) converges to $A^{-1} b$ for every $b$ and every
$x^{(0)}$.

The proof specializes the Householder–John theorem
`Stationary.Splitting.complexSpectralRadius_lt_one_of_posDef`, with $P + P^T - A = 2P - A$. -/
theorem property_4_1_spectralRadius_lt_one (hA : A.PosDef) (s : Splitting A) (hP : s.m.PosDef)
    (h2 : (2 • s.m - A).PosDef) :
    complexSpectralRadius s.iterationOperator < 1 ∧
      ∀ b x₀, Tendsto (fun k => (s.mulVecStep b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) := by
  have hρ := s.complexSpectralRadius_lt_one_of_posDef hA
    (by rwa [add_transpose_sub_of_isHermitian hP.1])
  exact ⟨hρ, fun b x₀ => s.tendsto hρ b x₀⟩

/-- If $Be = \mu e$, then $(X B e) \cdot (B e) = \mu^2 \, (X e) \cdot e$ for every matrix $X$. -/
private theorem energy_of_mulVec_eq_smul {B X : Matrix (Fin n) (Fin n) ℝ} {e : Fin n → ℝ} {μ : ℝ}
    (h : B *ᵥ e = μ • e) : (X *ᵥ (B *ᵥ e)) ⬝ᵥ (B *ᵥ e) = μ ^ 2 * ((X *ᵥ e) ⬝ᵥ e) := by
  rw [h, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  ring

/-- **Property 4.1** of [quarteroni2000numerical], $\rho(B) = \|B\|_A = \|B\|_P$. Let $n \ge 1$, and
let $A = P - N$ be a splitting with $A$ and $P$ symmetric positive definite, and $B = P^{-1} N$.
Then the operator norms of $B$ induced by the energy norms $\|\cdot\|_A$ and $\|\cdot\|_P$ are
both $\rho(B)$:

* $\|Be\|_A^2 \le \rho(B)^2 \|e\|_A^2$ for every $e \in \mathbb{R}^n$, with equality for some
  $e \neq 0$;
* $\|Be\|_P^2 \le \rho(B)^2 \|e\|_P^2$ for every $e \in \mathbb{R}^n$, with equality for some
  $e \neq 0$.

**Generalization.** The book states Property 4.1 under the hypothesis that $2P - A$ is positive
definite. These clauses do not need it.

The squared norms are $\|e\|_A^2 = (Ae) \cdot e$ and $\|e\|_P^2 = (Pe) \cdot e$. The proof
specializes `Stationary.Splitting.energyNorm_mulVec_iterationOperator_le_complexSpectralRadius`
and `Stationary.Splitting.energyNorm_m_mulVec_iterationOperator_le_complexSpectralRadius`.
Equality holds at a real eigenvector for an eigenvalue of modulus $\rho(B)$
(`Stationary.Splitting.exists_mulVec_iterationOperator_eq_smul`).

**Generalization.** The equalities of the norms with the spectral radius hold under positive
definiteness of the coefficient and preconditioning matrices alone. Lean expresses the equalities as
squared bounds with attainment in positive dimension. The additional source hypothesis gives
contraction.
-/
theorem property_4_1_energyNorm [NeZero n] (hA : A.PosDef) (s : Splitting A) (hP : s.m.PosDef) :
    (∀ e, (A *ᵥ (s.iterationOperator *ᵥ e)) ⬝ᵥ (s.iterationOperator *ᵥ e) ≤
        (complexSpectralRadius s.iterationOperator).toReal ^ 2 * ((A *ᵥ e) ⬝ᵥ e)) ∧
      (∃ e ≠ 0, (A *ᵥ (s.iterationOperator *ᵥ e)) ⬝ᵥ (s.iterationOperator *ᵥ e) =
        (complexSpectralRadius s.iterationOperator).toReal ^ 2 * ((A *ᵥ e) ⬝ᵥ e)) ∧
      (∀ e, (s.m *ᵥ (s.iterationOperator *ᵥ e)) ⬝ᵥ (s.iterationOperator *ᵥ e) ≤
        (complexSpectralRadius s.iterationOperator).toReal ^ 2 * ((s.m *ᵥ e) ⬝ᵥ e)) ∧
      ∃ e ≠ 0, (s.m *ᵥ (s.iterationOperator *ᵥ e)) ⬝ᵥ (s.iterationOperator *ᵥ e) =
        (complexSpectralRadius s.iterationOperator).toReal ^ 2 * ((s.m *ᵥ e) ⬝ᵥ e) := by
  obtain ⟨e, he, μ, hμ, hBe⟩ := s.exists_mulVec_iterationOperator_eq_smul hA hP.1
  refine ⟨s.energyNorm_mulVec_iterationOperator_le_complexSpectralRadius hA hP.1,
    ⟨e, he, ?_⟩, s.energyNorm_m_mulVec_iterationOperator_le_complexSpectralRadius hA.1 hP,
    ⟨e, he, ?_⟩⟩ <;>
  · rw [energy_of_mulVec_eq_smul hBe, ← hμ, sq_abs]

/-- **Property 4.1** of [quarteroni2000numerical], monotone convergence. Let $A = P - N$ be a
splitting with $A$, $P$ and $2P - A$ symmetric positive definite, and $B = P^{-1} N$. Then for
every $e \neq 0$
$$\|Be\|_A < \|e\|_A, \qquad \|Be\|_P < \|e\|_P.$$
So along the error recursion $e^{(k+1)} = B e^{(k)}$ the convergence is monotone in both energy
norms.

The clause for $A$ is `Stationary.Splitting.energyNorm_mulVec_iterationOperator_lt`. The clause
for $P$ follows from $\|Be\|_P \le \rho(B) \|e\|_P$ and $\rho(B) < 1$.

**Correction.** Strict contraction is stated for a nonzero error. Once the iterate reaches the
solution, both consecutive errors are zero, so the strict monotonicity written in Property 4.1
cannot hold for every index.
-/
theorem property_4_1_monotone (hA : A.PosDef) (s : Splitting A) (hP : s.m.PosDef)
    (h2 : (2 • s.m - A).PosDef) {e : Fin n → ℝ} (he : e ≠ 0) :
    (A *ᵥ (s.iterationOperator *ᵥ e)) ⬝ᵥ (s.iterationOperator *ᵥ e) < (A *ᵥ e) ⬝ᵥ e ∧
      (s.m *ᵥ (s.iterationOperator *ᵥ e)) ⬝ᵥ (s.iterationOperator *ᵥ e) < (s.m *ᵥ e) ⬝ᵥ e := by
  have hQ : (s.m + s.mᵀ - A).PosDef := by rwa [add_transpose_sub_of_isHermitian hP.1]
  refine ⟨s.energyNorm_mulVec_iterationOperator_lt hA hQ he, ?_⟩
  have hρ := (property_4_1_spectralRadius_lt_one hA s hP h2).1
  have hρ' : (complexSpectralRadius s.iterationOperator).toReal < 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_strict_mono ENNReal.one_ne_top hρ
  have hle := s.energyNorm_m_mulVec_iterationOperator_le_complexSpectralRadius hA.1 hP e
  have hpos : 0 < (s.m *ᵥ e) ⬝ᵥ e := by
    have := hP.dotProduct_mulVec_pos he
    rwa [star_trivial, dotProduct_comm] at this
  have hsq : (complexSpectralRadius s.iterationOperator).toReal ^ 2 < 1 :=
    (pow_lt_one_iff_of_nonneg ENNReal.toReal_nonneg two_ne_zero).mpr hρ'
  nlinarith

/-- **Property 4.2** of [quarteroni2000numerical], $P$ is nonsingular. Let
$A, P \in \mathbb{R}^{n \times n}$, with $A$ symmetric positive definite and $P + P^T - A$
positive definite. Then $P$ is nonsingular, so $A = P - N$ is a splitting in the sense of
Section 4.2.

The reason is that $P + P^T = (P + P^T - A) + A$ is positive definite. -/
theorem property_4_2_isUnit (hA : A.PosDef) {P : Matrix (Fin n) (Fin n) ℝ}
    (hQ : (P + Pᵀ - A).PosDef) : IsUnit P :=
  isUnit_of_posDef_add_transpose (by simpa using hQ.add hA)

/-- **Property 4.2** of [quarteroni2000numerical]. Let $A = P - N$ be a splitting with $A$ symmetric
positive definite and $P + P^T - A$ positive definite, and let $B = P^{-1} N$. Then
$\rho(B) < 1$, the iteration (4.7) converges to $A^{-1} b$ for every $b$ and every $x^{(0)}$,
and $\rho(B) \le \|B\|_A < 1$: there is a $q < 1$ with $\rho(B) \le q$ and
$$\|Be\|_A \le q \|e\|_A \quad \text{for every } e \in \mathbb{R}^n.$$

That $P$ is nonsingular is `QuarteroniSaccoSaleri.Chapter04.property_4_2_isUnit`. The proof
specializes the Householder–John theorem
`Stationary.Splitting.complexSpectralRadius_lt_one_of_posDef` and the uniform energy contraction
`Stationary.Splitting.exists_complexSpectralRadius_le_and_energyNorm_mulVec_le`. -/
theorem property_4_2 (hA : A.PosDef) (s : Splitting A) (hQ : (s.m + s.mᵀ - A).PosDef) :
    complexSpectralRadius s.iterationOperator < 1 ∧
      (∀ b x₀, Tendsto (fun k => (s.mulVecStep b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b))) ∧
      ∃ q : ℝ, q < 1 ∧ (complexSpectralRadius s.iterationOperator).toReal ≤ q ∧
        ∀ e : Fin n → ℝ, (A *ᵥ (s.iterationOperator *ᵥ e)) ⬝ᵥ (s.iterationOperator *ᵥ e) ≤
          q ^ 2 * ((A *ᵥ e) ⬝ᵥ e) := by
  have hρ := s.complexSpectralRadius_lt_one_of_posDef hA hQ
  exact ⟨hρ, fun b x₀ => s.tendsto hρ b x₀,
    s.exists_complexSpectralRadius_le_and_energyNorm_mulVec_le hA hQ⟩

/-- **Property 4.2** of [quarteroni2000numerical], monotone convergence in $\|\cdot\|_A$. Let
$A = P - N$ be a splitting with $A$ symmetric positive definite and $P + P^T - A$ positive
definite, and let $B = P^{-1} N$. Then $\|Be\|_A < \|e\|_A$ for every $e \neq 0$.

The proof specializes `Stationary.Splitting.energyNorm_mulVec_iterationOperator_lt`.

**Correction.** Strict contraction is stated for a nonzero error. Once the iterate reaches the
solution, both consecutive errors are zero, so the strict monotonicity written in Property 4.1
cannot hold for every index.
-/
theorem property_4_2_monotone (hA : A.PosDef) (s : Splitting A) (hQ : (s.m + s.mᵀ - A).PosDef)
    {e : Fin n → ℝ} (he : e ≠ 0) :
    (A *ᵥ (s.iterationOperator *ᵥ e)) ⬝ᵥ (s.iterationOperator *ᵥ e) < (A *ᵥ e) ⬝ᵥ e :=
  s.energyNorm_mulVec_iterationOperator_lt hA hQ he

end SPD

/-! ### Section 4.2.1: Jacobi, Gauss–Seidel and relaxation methods -/

section Classical

/-- **Section 4.2.1** of [quarteroni2000numerical], the letter $D$. For
$A \in \mathbb{R}^{n \times n}$, $D$ is the diagonal matrix of the diagonal entries of $A$. -/
def D (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := diagPart A

/-- **Section 4.2.1** of [quarteroni2000numerical], the letter $E$. For
$A \in \mathbb{R}^{n \times n}$, $E$ is the lower triangular matrix with entries
$e_{ij} = -a_{ij}$ for $i > j$ and $e_{ij} = 0$ for $i \le j$. -/
def E (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := -strictLower A

/-- **Section 4.2.1** of [quarteroni2000numerical], the letter $F$. For
$A \in \mathbb{R}^{n \times n}$, $F$ is the upper triangular matrix with entries
$f_{ij} = -a_{ij}$ for $j > i$ and $f_{ij} = 0$ for $j \le i$. -/
def F (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := -strictUpper A

/-- **Section 4.2.1** of [quarteroni2000numerical]. Every $A \in \mathbb{R}^{n \times n}$ satisfies
$A = D - E - F$: it is the sum of its diagonal, its strictly lower and its strictly upper parts. -/
theorem decomp (A : Matrix (Fin n) (Fin n) ℝ) : A = D A - E A - F A :=
  (diagPart_sub_neg_strictLower_sub_neg_strictUpper A).symm

/-- For $A \in \mathbb{R}^{n \times n}$, $D - E$ is the sum of the diagonal and the strictly lower
part of $A$, the matrix that the forward sweeps invert. -/
theorem D_sub_E (A : Matrix (Fin n) (Fin n) ℝ) : D A - E A = diagPart A + strictLower A := by
  rw [D, E, sub_neg_eq_add]

/-- For $A \in \mathbb{R}^{n \times n}$, $D - F$ is the sum of the diagonal and the strictly upper
part of $A$, the matrix that the backward sweeps invert. -/
theorem D_sub_F (A : Matrix (Fin n) (Fin n) ℝ) : D A - F A = diagPart A + strictUpper A := by
  rw [D, F, sub_neg_eq_add]

/-- For $A \in \mathbb{R}^{n \times n}$ and $\omega \in \mathbb{R}$, $D - \omega E$ is the diagonal
of $A$ plus $\omega$ times the strictly lower part of $A$. -/
theorem D_sub_smul_E (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) :
    D A - ω • E A = diagPart A + ω • strictLower A := by
  rw [D, E, smul_neg, sub_neg_eq_add]

/-- For $A \in \mathbb{R}^{n \times n}$ and $\omega \in \mathbb{R}$, $D - \omega F$ is the diagonal
of $A$ plus $\omega$ times the strictly upper part of $A$. -/
theorem D_sub_smul_F (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) :
    D A - ω • F A = diagPart A + ω • strictUpper A := by
  rw [D, F, smul_neg, sub_neg_eq_add]

/-- **Equations (4.9) to (4.11)** of [quarteroni2000numerical], the Jacobi method. Let
$A \in \mathbb{R}^{n \times n}$ have nonzero diagonal entries, and let $b, x \in \mathbb{R}^n$.
The Jacobi step from $x$ computes
$$x_i^{\mathrm{new}} = \frac{1}{a_{ii}} \Big( b_i - \sum_{j \neq i} a_{ij} x_j \Big) \qquad
  \text{(4.10)}$$
for every $i$. It is the step of the splitting $P = D$, $N = E + F$, whose iteration matrix is
$$B_J = D^{-1} (E + F) = I - D^{-1} A. \qquad \text{(4.11)}$$

The splitting is `Matrix.jacobiSplitting`, and the step identity specializes
`Matrix.jorSweep_one_eq_mulVecStep`. -/
theorem equation_4_10 (h : IsUnit (diagPart A)) (b x : Fin n → ℝ) :
    (∀ i, jorSweep A 1 b x i = (b i - ∑ j ∈ univ.erase i, A i j * x j) / A i i) ∧
      jorSweep A 1 b x = (jacobiSplitting A h).mulVecStep b x ∧
      (jacobiSplitting A h).m = D A ∧ (jacobiSplitting A h).n = E A + F A ∧
      (jacobiSplitting A h).iterationOperator = (D A)⁻¹ * (E A + F A) ∧
      (jacobiSplitting A h).iterationOperator = 1 - (D A)⁻¹ * A := by
  refine ⟨fun i => ?_, congrFun (jorSweep_one_eq_mulVecStep A h b) x, rfl, ?_, ?_, ?_⟩
  · rw [jorSweep, sub_self, zero_mul, add_zero, div_mul_eq_mul_div, one_mul]
  · rw [jacobiSplitting_n, E, F, neg_add]
  · rw [jacobiSplitting_iterationOperator, D, E, F, ← neg_add, mul_neg, neg_mul]
  · rw [D, nonsing_inv_eq_ringInverse]
    rfl

/-- The inverse of $cM$, for $c \neq 0$ and $M$ nonsingular, is $c^{-1} M^{-1}$. -/
private theorem inv_smul_of_isUnit {c : ℝ} (hc : c ≠ 0) {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsUnit M) : (c • M)⁻¹ = c⁻¹ • M⁻¹ := by
  refine inv_eq_left_inv ?_
  rw [smul_mul_smul_comm, inv_mul_cancel₀ hc, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hM),
    one_smul]

/-- **Equation (4.12)** of [quarteroni2000numerical], the JOR method. Let
$A \in \mathbb{R}^{n \times n}$ have nonzero diagonal entries, let $\omega \neq 0$ be a
relaxation parameter, and let $b, x \in \mathbb{R}^n$. The JOR step from $x$ computes
$$x_i^{\mathrm{new}} = \frac{\omega}{a_{ii}} \Big( b_i - \sum_{j \neq i} a_{ij} x_j \Big) + (1 -
  \omega) x_i$$
for every $i$. It is the step of the splitting $P = \omega^{-1} D$, whose iteration matrix is
$B_{J_\omega} = \omega B_J + (1 - \omega) I$. In the form (4.7) the step is
$x + \omega D^{-1} (b - Ax)$, its fixed points are the solutions of $Ax = b$, so that the method
is consistent, and for $\omega = 1$ the splitting is the Jacobi splitting.

The splitting is `Matrix.jorSplitting`, and the step identity specializes
`Matrix.jorSweep_eq_mulVecStep`.

**Reading.** The displayed coordinate or iteration-matrix identities are bundled with a splitting
that requires nonzero relaxation. The source formulas for the sweep also make sense at zero, where
the sweep is the identity.
-/
theorem equation_4_12 (h : IsUnit (diagPart A)) {ω : ℝ} (hω : ω ≠ 0) (b x : Fin n → ℝ) :
    (∀ i, jorSweep A ω b x i =
        ω / A i i * (b i - ∑ j ∈ univ.erase i, A i j * x j) + (1 - ω) * x i) ∧
      jorSweep A ω b x = (jorSplitting A h hω).mulVecStep b x ∧
      (jorSplitting A h hω).iterationOperator =
        ω • (jacobiSplitting A h).iterationOperator + (1 - ω) • 1 ∧
      jorSweep A ω b x = x + ω • ((D A)⁻¹ *ᵥ (b - A *ᵥ x)) ∧
      (jorSweep A ω b x = x ↔ A *ᵥ x = b) ∧ jorSplitting A h one_ne_zero = jacobiSplitting A h := by
  have hstep := congrFun (jorSweep_eq_mulVecStep A h hω b) x
  refine ⟨fun i => rfl, hstep, by rw [jorSplitting_iterationOperator, add_comm], ?_,
    by rw [hstep, Splitting.mulVecStep_fixed_iff], jorSplitting_one A h⟩
  rw [hstep, Splitting.mulVecStep_eq_add_inv_mulVec]
  have hm : (jorSplitting A h hω).m = ω⁻¹ • diagPart A := rfl
  rw [hm, inv_smul_of_isUnit (inv_ne_zero hω) h, inv_inv, smul_mulVec, D]

/-- **Equations (4.13) and (4.14)** of [quarteroni2000numerical], the Gauss–Seidel method. Let
$A \in \mathbb{R}^{n \times n}$ have nonzero diagonal entries, and let $b, x \in \mathbb{R}^n$.
The Gauss–Seidel step $y$ from $x$ uses the components already updated:
$$y_i = \frac{1}{a_{ii}} \Big( b_i - \sum_{j < i} a_{ij} y_j - \sum_{j > i} a_{ij} x_j \Big)
  \qquad \text{(4.13)}$$
for every $i$. It is the step of the splitting $P = D - E$, $N = F$, whose iteration matrix is
$$B_{GS} = (D - E)^{-1} F. \qquad \text{(4.14)}$$

The splitting is `Matrix.gaussSeidelSplitting`. The proof specializes `Matrix.sorSweep_apply` at
$\omega = 1$ and `Matrix.sorSweep_one_eq_mulVecStep`. -/
theorem equation_4_13 (h : IsUnit (diagPart A)) (b x : Fin n → ℝ) :
    (∀ i, sorSweep A 1 b x i = (b i - ∑ j ∈ univ.filter (· < i), A i j * sorSweep A 1 b x j
        - ∑ j ∈ univ.filter (i < ·), A i j * x j) / A i i) ∧
      sorSweep A 1 b x = (gaussSeidelSplitting A h).mulVecStep b x ∧
      (gaussSeidelSplitting A h).m = D A - E A ∧ (gaussSeidelSplitting A h).n = F A ∧
      (gaussSeidelSplitting A h).iterationOperator = (D A - E A)⁻¹ * F A := by
  refine ⟨fun i => ?_, congrFun (sorSweep_one_eq_mulVecStep A h b) x, ?_, ?_, ?_⟩
  · rw [sorSweep_apply A h 1 b x i, sub_self, zero_mul, add_zero, div_mul_eq_mul_div, one_mul]
  · rw [D_sub_E]
    rfl
  · rw [gaussSeidelSplitting_n]
    rfl
  · rw [Splitting.iterationOperator_eq, gaussSeidelSplitting_n, ← nonsing_inv_eq_ringInverse,
      D_sub_E]
    rfl

/-- **Equation (4.15)** of [quarteroni2000numerical], the SOR method. Let
$A \in \mathbb{R}^{n \times n}$ have nonzero diagonal entries, let $\omega \neq 0$, and let
$b, x \in \mathbb{R}^n$. The successive over-relaxation step $y$ from $x$ computes
$$y_i = \frac{\omega}{a_{ii}} \Big( b_i - \sum_{j < i} a_{ij} y_j - \sum_{j > i} a_{ij} x_j
  \Big) + (1 - \omega) x_i$$
for every $i$, and it is the step of the splitting $P = \omega^{-1} D - E$.

The splitting is `Matrix.sorSplitting`. The proof specializes `Matrix.sorSweep_apply` and
`Matrix.sorSweep_eq_mulVecStep`.

**Reading.** The displayed coordinate or iteration-matrix identities are bundled with a splitting
that requires nonzero relaxation. The source formulas for the sweep also make sense at zero, where
the sweep is the identity.
-/
theorem equation_4_15 (h : IsUnit (diagPart A)) {ω : ℝ} (hω : ω ≠ 0) (b x : Fin n → ℝ) :
    (∀ i, sorSweep A ω b x i =
        ω / A i i * (b i - ∑ j ∈ univ.filter (· < i), A i j * sorSweep A ω b x j
          - ∑ j ∈ univ.filter (i < ·), A i j * x j) + (1 - ω) * x i) ∧
      sorSweep A ω b x = (sorSplitting A h hω).mulVecStep b x :=
  ⟨sorSweep_apply A h ω b x, congrFun (sorSweep_eq_mulVecStep A h hω b) x⟩

/-- The two sides of (4.16) multiplied by $D$: $I - \omega D^{-1} E = D^{-1}(D + \omega L)$ and
$(1 - \omega) I + \omega D^{-1} F = D^{-1}((1 - \omega) D - \omega U)$, where $L$ and $U$ are
the strictly lower and strictly upper parts of $A$. -/
private theorem one_sub_smul_inv_D_mul_E (h : IsUnit (diagPart A)) (ω : ℝ) :
    (1 : Matrix (Fin n) (Fin n) ℝ) - ω • ((D A)⁻¹ * E A) =
        (diagPart A)⁻¹ * (diagPart A + ω • strictLower A) ∧
      (1 - ω) • (1 : Matrix (Fin n) (Fin n) ℝ) + ω • ((D A)⁻¹ * F A) =
        (diagPart A)⁻¹ * ((1 - ω) • diagPart A - ω • strictUpper A) := by
  have hD : (diagPart A)⁻¹ * diagPart A = 1 :=
    nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp h)
  constructor
  · rw [D, E, mul_neg, smul_neg, sub_neg_eq_add, mul_add, hD, Matrix.mul_smul]
  · rw [D, F, mul_neg, smul_neg, ← sub_eq_add_neg, mul_sub, Matrix.mul_smul, Matrix.mul_smul, hD]

/-- **Equation (4.16)** of [quarteroni2000numerical], the SOR method in vector form. Let
$A \in \mathbb{R}^{n \times n}$ have nonzero diagonal entries, let $\omega \in \mathbb{R}$, and
let $b, x \in \mathbb{R}^n$. The SOR step $y$ from $x$ satisfies
$$(I - \omega D^{-1} E)\, y = [(1 - \omega) I + \omega D^{-1} F]\, x + \omega D^{-1} b.$$

The sweep solves the triangular system $(D + \omega L) y = ((1 - \omega) D - \omega U) x +
\omega b$, where $L$ and $U$ are the strictly lower and strictly upper parts of $A$
(`Matrix.diagPart_add_smul_strictLower_mulVec_sorSweep`). Multiplication by $D^{-1}$ gives the
statement. -/
theorem equation_4_16 (h : IsUnit (diagPart A)) (ω : ℝ) (b x : Fin n → ℝ) :
    (1 - ω • ((D A)⁻¹ * E A)) *ᵥ sorSweep A ω b x =
      ((1 - ω) • 1 + ω • ((D A)⁻¹ * F A)) *ᵥ x + ω • ((D A)⁻¹ *ᵥ b) := by
  obtain ⟨h1, h2⟩ := one_sub_smul_inv_D_mul_E h ω
  rw [h1, h2, ← mulVec_mulVec, ← mulVec_mulVec, diagPart_add_smul_strictLower_mulVec_sorSweep A h,
    mulVec_add, mulVec_smul, D]

/-- **Equation (4.17)** of [quarteroni2000numerical], the SOR iteration matrix. Let
$A \in \mathbb{R}^{n \times n}$ have nonzero diagonal entries, and let $\omega \neq 0$. The
iteration matrix of the SOR splitting is
$$B(\omega) = (I - \omega D^{-1} E)^{-1} [(1 - \omega) I + \omega D^{-1} F],$$
and it equals `Matrix.sorIterationMatrix A ω`.

The proof specializes `Matrix.sorSplitting_iterationOperator` and
`Matrix.sorSplitting_iterationOperator_eq`.

**Reading.** The displayed coordinate or iteration-matrix identities are bundled with a splitting
that requires nonzero relaxation. The source formulas for the sweep also make sense at zero, where
the sweep is the identity.
-/
theorem equation_4_17 (h : IsUnit (diagPart A)) {ω : ℝ} (hω : ω ≠ 0) :
    (sorSplitting A h hω).iterationOperator =
        (1 - ω • ((D A)⁻¹ * E A))⁻¹ * ((1 - ω) • 1 + ω • ((D A)⁻¹ * F A)) ∧
      (sorSplitting A h hω).iterationOperator = sorIterationMatrix A ω := by
  refine ⟨?_, sorSplitting_iterationOperator_eq A h hω⟩
  obtain ⟨h1, h2⟩ := one_sub_smul_inv_D_mul_E h ω
  have hDdet : IsUnit (diagPart A).det := (isUnit_iff_isUnit_det _).mp h
  rw [sorSplitting_iterationOperator, h1, h2, Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ hDdet,
    Matrix.mul_assoc, ← Matrix.mul_assoc (diagPart A), mul_nonsing_inv _ hDdet, Matrix.one_mul]

/-- **Section 4.2.1** of [quarteroni2000numerical], the display after (4.17). Let
$A \in \mathbb{R}^{n \times n}$ have nonzero diagonal entries, let $\omega \neq 0$, and let
$b, x \in \mathbb{R}^n$. In the form (4.7), the SOR step from $x$ is
$$x + (\omega^{-1} D - E)^{-1} (b - Ax).$$
Its fixed points are the solutions of $Ax = b$, so that the method is consistent, and for
$\omega = 1$ the SOR splitting is the Gauss–Seidel splitting (`Matrix.sorSplitting_one`). -/
theorem sor_step_eq_add_inv_mulVec (h : IsUnit (diagPart A)) {ω : ℝ} (hω : ω ≠ 0)
    (b x : Fin n → ℝ) :
    sorSweep A ω b x = x + (ω⁻¹ • D A - E A)⁻¹ *ᵥ (b - A *ᵥ x) ∧
      (sorSweep A ω b x = x ↔ A *ᵥ x = b) ∧
      sorSplitting A h one_ne_zero = gaussSeidelSplitting A h := by
  have hstep := congrFun (sorSweep_eq_mulVecStep A h hω b) x
  refine ⟨?_, by rw [hstep, Splitting.mulVecStep_fixed_iff], sorSplitting_one A h⟩
  rw [hstep, Splitting.mulVecStep_eq_add_inv_mulVec, D, E, sub_neg_eq_add]
  rfl

end Classical

/-! ### Section 4.2.2: Convergence results for the Jacobi and Gauss–Seidel methods -/

section Convergence

/-- **Theorem 4.2** of [quarteroni2000numerical], Jacobi. Let $A \in \mathbb{R}^{n \times n}$ be
strictly diagonally dominant by rows. Then the Jacobi method converges to $A^{-1} b$, for every
$b$ and every $x^{(0)}$.

The proof specializes `Matrix.jacobi_complexSpectralRadius_lt_one` and Theorem 4.1. -/
theorem theorem_4_2_jacobi (hA : A.IsStrictDiagDominant) (b x₀ : Fin n → ℝ) :
    Tendsto (fun k => (jorSweep A 1 b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) := by
  rw [jorSweep_one_eq_mulVecStep A hA.isUnit_diagPart b]
  exact Splitting.tendsto _ (jacobi_complexSpectralRadius_lt_one hA _) b x₀

open scoped Matrix.Norms.Operator in
/-- **Theorem 4.2** of [quarteroni2000numerical], the book's proof for Jacobi. Let $n \ge 1$, and
let $A \in \mathbb{R}^{n \times n}$ be strictly diagonally dominant by rows. Then
$$\|B_J\|_\infty = \max_i \frac{\sum_{j \neq i} |a_{ij}|}{|a_{ii}|} < 1.$$

The norm is the operator norm induced by the sup norm (`Matrix.Norms.Operator`). The proof
specializes `Matrix.linfty_opNorm_jacobi_iterMatrix` and
`Matrix.IsStrictDiagDominant.jacobiContraction_lt_one`. -/
theorem theorem_4_2_jacobi_linfty [NeZero n] (hA : A.IsStrictDiagDominant) :
    ‖(jacobiSplitting A hA.isUnit_diagPart).iterationOperator‖ =
        univ.sup' univ_nonempty (fun i => (∑ j ∈ univ.erase i, ‖A i j‖) / ‖A i i‖) ∧
      ‖(jacobiSplitting A hA.isUnit_diagPart).iterationOperator‖ < 1 := by
  rw [linfty_opNorm_jacobi_iterMatrix]
  exact ⟨rfl, hA.jacobiContraction_lt_one⟩

/-- **Theorem 4.2** of [quarteroni2000numerical], Gauss–Seidel. Let $A \in \mathbb{R}^{n \times n}$
be strictly diagonally dominant by rows. Then the Gauss–Seidel method converges to $A^{-1} b$,
for every $b$ and every $x^{(0)}$.

The book leaves this half of the proof to a book of Axelsson and to Exercise 2. The proof
specializes `Matrix.gaussSeidel_complexSpectralRadius_lt_one` and Theorem 4.1. -/
theorem theorem_4_2_gaussSeidel (hA : A.IsStrictDiagDominant) (b x₀ : Fin n → ℝ) :
    Tendsto (fun k => (sorSweep A 1 b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) := by
  rw [sorSweep_one_eq_mulVecStep A hA.isUnit_diagPart b]
  exact Splitting.tendsto _ (gaussSeidel_complexSpectralRadius_lt_one hA _) b x₀

/-- **Theorem 4.3** of [quarteroni2000numerical], convergence. Let $A \in \mathbb{R}^{n \times n}$
be symmetric positive definite, and let $2D - A$ be positive definite. Then the Jacobi method
converges to $A^{-1} b$, for every $b$ and every $x^{(0)}$.

This is Property 4.1 with $P = D$; the proof specializes
`Matrix.jacobiSplitting_complexSpectralRadius_lt_one_of_posDef`. -/
theorem theorem_4_3 (hA : A.PosDef) (h2 : (2 • D A - A).PosDef) (b x₀ : Fin n → ℝ) :
    Tendsto (fun k => (jorSweep A 1 b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) := by
  rw [jorSweep_one_eq_mulVecStep A hA.diagPart.isUnit b]
  exact Splitting.tendsto _ (jacobiSplitting_complexSpectralRadius_lt_one_of_posDef hA h2 _) b x₀

/-- **Theorem 4.3** of [quarteroni2000numerical], $\rho(B_J) = \|B_J\|_A = \|B_J\|_D$. Let
$n \ge 1$, and let $A \in \mathbb{R}^{n \times n}$ be symmetric positive definite. Then the
operator norms of the Jacobi matrix $B_J$ induced by the energy norms $\|\cdot\|_A$ and
$\|\cdot\|_D$ are both $\rho(B_J)$, in the sense of
`QuarteroniSaccoSaleri.Chapter04.property_4_1_energyNorm` with $P = D$:

* $\|B_J e\|_A^2 \le \rho(B_J)^2 \|e\|_A^2$ for every $e$, with equality for some $e \neq 0$;
* $\|B_J e\|_D^2 \le \rho(B_J)^2 \|e\|_D^2$ for every $e$, with equality for some $e \neq 0$.

**Generalization.** The equalities of the norms with the spectral radius hold under positive
definiteness of the coefficient and preconditioning matrices alone. Lean expresses the equalities as
squared bounds with attainment in positive dimension. The additional source hypothesis gives
contraction.
-/
theorem theorem_4_3_energyNorm [NeZero n] (hA : A.PosDef) :
    (∀ e, (A *ᵥ ((jacobiSplitting A hA.diagPart.isUnit).iterationOperator *ᵥ e)) ⬝ᵥ
          ((jacobiSplitting A hA.diagPart.isUnit).iterationOperator *ᵥ e) ≤
        (complexSpectralRadius (jacobiSplitting A hA.diagPart.isUnit).iterationOperator).toReal ^ 2
          * ((A *ᵥ e) ⬝ᵥ e)) ∧
      (∃ e ≠ 0, (A *ᵥ ((jacobiSplitting A hA.diagPart.isUnit).iterationOperator *ᵥ e)) ⬝ᵥ
          ((jacobiSplitting A hA.diagPart.isUnit).iterationOperator *ᵥ e) =
        (complexSpectralRadius (jacobiSplitting A hA.diagPart.isUnit).iterationOperator).toReal ^ 2
          * ((A *ᵥ e) ⬝ᵥ e)) ∧
      (∀ e, (D A *ᵥ ((jacobiSplitting A hA.diagPart.isUnit).iterationOperator *ᵥ e)) ⬝ᵥ
          ((jacobiSplitting A hA.diagPart.isUnit).iterationOperator *ᵥ e) ≤
        (complexSpectralRadius (jacobiSplitting A hA.diagPart.isUnit).iterationOperator).toReal ^ 2
          * ((D A *ᵥ e) ⬝ᵥ e)) ∧
      ∃ e ≠ 0, (D A *ᵥ ((jacobiSplitting A hA.diagPart.isUnit).iterationOperator *ᵥ e)) ⬝ᵥ
          ((jacobiSplitting A hA.diagPart.isUnit).iterationOperator *ᵥ e) =
        (complexSpectralRadius (jacobiSplitting A hA.diagPart.isUnit).iterationOperator).toReal ^ 2
          * ((D A *ᵥ e) ⬝ᵥ e) :=
  property_4_1_energyNorm hA (jacobiSplitting A hA.diagPart.isUnit) hA.diagPart

/-- **Theorem 4.4** of [quarteroni2000numerical]. Let $n \ge 1$, and let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite. If
$$0 < \omega < \frac{2}{\rho(D^{-1} A)},$$
then the JOR method with parameter $\omega$ converges to $A^{-1} b$, for every $b$ and every
$x^{(0)}$.

The proof specializes `Matrix.jorSplitting_complexSpectralRadius_lt_one_iff_of_posDef`, whose
proof is the book's: $B_{J_\omega} = I - \omega D^{-1} A$, and $D^{-1} A$ has real positive
eigenvalues. -/
theorem theorem_4_4 [NeZero n] (hA : A.PosDef) {ω : ℝ} (hω0 : 0 < ω)
    (hω2 : ω < 2 / (complexSpectralRadius ((D A)⁻¹ * A)).toReal) (b x₀ : Fin n → ℝ) :
    Tendsto (fun k => (jorSweep A ω b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) := by
  rw [jorSweep_eq_mulVecStep A hA.diagPart.isUnit hω0.ne' b]
  exact Splitting.tendsto _
    ((jorSplitting_complexSpectralRadius_lt_one_iff_of_posDef hA _ hω0.ne').mpr ⟨hω0, hω2⟩) b x₀

/-- **Theorem 4.4** of [quarteroni2000numerical], as an equivalence. Let $n \ge 1$, let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite, and let $\omega \neq 0$. Then
the JOR method converges to $A^{-1} b$ for every $b$ and every $x^{(0)}$ if and only if
$$0 < \omega < \frac{2}{\rho(D^{-1} A)}.$$

**Generalization.** The printed statement gives a sufficient interval. Lean proves an equivalence
for convergence to the solution for every right-hand side and start under nonzero relaxation.
-/
theorem theorem_4_4_iff [NeZero n] (hA : A.PosDef) {ω : ℝ} (hω : ω ≠ 0) :
    (∀ b x₀, Tendsto (fun k => (jorSweep A ω b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b))) ↔
      0 < ω ∧ ω < 2 / (complexSpectralRadius ((D A)⁻¹ * A)).toReal := by
  simp only [jorSweep_eq_mulVecStep A hA.diagPart.isUnit hω]
  rw [Splitting.forall_tendsto_iff, jorSplitting_complexSpectralRadius_lt_one_iff_of_posDef hA _ hω]
  rfl

/-- **Theorem 4.5** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric
positive definite. Then the Gauss–Seidel method is monotonically convergent with respect to
$\|\cdot\|_A$: it converges to $A^{-1} b$ for every $b$ and every $x^{(0)}$, and
$\|B_{GS} e\|_A < \|e\|_A$ for every $e \neq 0$.

This is Property 4.2 with $P = D - E$, for which $P + P^T - A = D$ is positive definite, because
the diagonal of a positive definite matrix is positive. The proof specializes
`Matrix.gaussSeidelSplitting_complexSpectralRadius_lt_one_of_posDef` and
`Stationary.Splitting.energyNorm_mulVec_iterationOperator_lt`.

**Correction.** Strict contraction is stated for a nonzero error. Once the iterate reaches the
solution, both consecutive errors are zero, so the strict monotonicity written in Property 4.1
cannot hold for every index.
-/
theorem theorem_4_5 (hA : A.PosDef) :
    (∀ b x₀, Tendsto (fun k => (sorSweep A 1 b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b))) ∧
      ∀ e ≠ 0, (A *ᵥ ((gaussSeidelSplitting A hA.diagPart.isUnit).iterationOperator *ᵥ e)) ⬝ᵥ
          ((gaussSeidelSplitting A hA.diagPart.isUnit).iterationOperator *ᵥ e) <
        (A *ᵥ e) ⬝ᵥ e := by
  have h := hA.diagPart.isUnit
  refine ⟨fun b x₀ => ?_, fun e he => ?_⟩
  · rw [sorSweep_one_eq_mulVecStep A h b]
    exact Splitting.tendsto _ (gaussSeidelSplitting_complexSpectralRadius_lt_one_of_posDef hA _)
      b x₀
  · refine Splitting.energyNorm_mulVec_iterationOperator_lt _ hA ?_ he
    rw [← sorSplitting_one A h]
    exact sorSplitting_m_add_transpose_sub_posDef hA.1 (fun i => hA.diag_pos) h one_pos one_lt_two

/-- The spectral radii of the real Jacobi and Gauss–Seidel matrices equal those of the Jacobi and
Gauss–Seidel matrices of the complexification of $A$. -/
private theorem complexSpectralRadius_jacobi_gaussSeidel (h : IsUnit (diagPart A)) :
    complexSpectralRadius (jacobiSplitting A h).iterationOperator =
        spectralRadius ℂ
          (jacobiSplitting (complexify A) (isUnit_diagPart_complexify h)).iterationOperator ∧
      complexSpectralRadius (gaussSeidelSplitting A h).iterationOperator =
        spectralRadius ℂ
          (gaussSeidelSplitting (complexify A)
            (isUnit_diagPart_complexify h)).iterationOperator := by
  constructor
  · rw [complexSpectralRadius, complexify_jacobi_iterationOperator A h]
  · rw [complexSpectralRadius, complexify_gaussSeidel_iterationOperator A h]

/-- **Equation (4.18)** of [quarteroni2000numerical] and the sentence before it. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite and tridiagonal. Then the Jacobi
method converges to $A^{-1} b$ for every $b$ and every $x^{(0)}$, and
$$\rho(B_{GS}) = \rho(B_J)^2,$$
so that the Gauss–Seidel method converges faster than the Jacobi method.

A tridiagonal matrix is consistently ordered (`Matrix.IsTridiagonal.isConsistentlyOrdered`), and
the identity is `Matrix.IsConsistentlyOrdered.spectralRadius_gaussSeidel_eq_sq` for the
complexification. The Jacobi method then converges because $\rho(B_J)^2 = \rho(B_{GS}) < 1$
(Theorem 4.5). -/
theorem equation_4_18 (hA : A.PosDef) (ht : A.IsTridiagonal) :
    (∀ b x₀, Tendsto (fun k => (jorSweep A 1 b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b))) ∧
      complexSpectralRadius (gaussSeidelSplitting A hA.diagPart.isUnit).iterationOperator =
        complexSpectralRadius (jacobiSplitting A hA.diagPart.isUnit).iterationOperator ^ 2 := by
  have h := hA.diagPart.isUnit
  have hsq : complexSpectralRadius (gaussSeidelSplitting A h).iterationOperator =
      complexSpectralRadius (jacobiSplitting A h).iterationOperator ^ 2 := by
    rw [(complexSpectralRadius_jacobi_gaussSeidel h).1,
      (complexSpectralRadius_jacobi_gaussSeidel h).2]
    exact (ht.complexify.isConsistentlyOrdered (isUnit_diagPart_complexify h))
      |>.spectralRadius_gaussSeidel_eq_sq _
  refine ⟨fun b x₀ => ?_, hsq⟩
  rw [jorSweep_one_eq_mulVecStep A h b]
  refine Splitting.tendsto _ ?_ b x₀
  have hGS := gaussSeidelSplitting_complexSpectralRadius_lt_one_of_posDef hA h
  rw [hsq] at hGS
  by_contra hge
  exact absurd hGS (not_lt.mpr (one_le_pow₀ (not_lt.mp hge)))

/-- **Definition 4.3** of [quarteroni2000numerical], as printed. A matrix
$M \in \mathbb{R}^{n \times n}$, with $M = D - E - F$ as in Section 4.2.1, **enjoys the
$A$-property** if both of the following hold:

* $M$ is consistently ordered: the eigenvalues of $\alpha D^{-1} E + \alpha^{-1} D^{-1} F$ do
  not depend on $\alpha \neq 0$;
* $M$ has the $2 \times 2$ block form $\begin{bmatrix} \tilde D_1 & M_{12} \\ M_{21} & \tilde
  D_2 \end{bmatrix}$ with $\tilde D_1$ and $\tilde D_2$ diagonal: for some $k \le n$, every
  off-diagonal entry $m_{ij}$ with both indices less than $k$, or both indices at least $k$, is
  zero.

**Reading.** The partition is the printed contiguous one, and both clauses are hypotheses.
Property A of Saad and Young is the second clause, up to a permutation. Only the first clause is
used by (4.18) and Property 4.4.

The first clause is `Matrix.IsConsistentlyOrdered` of the complexification of $M$; see
`QuarteroniSaccoSaleri.Chapter04.definition_4_3_iff`. The indices are $0$-based.

**Reading.** Consistent ordering means independence of the complex spectrum as a set over nonzero
complex parameters. The two diagonal blocks are contiguous in the given matrix order. The displayed
inverses are total in Lean, so the predicate is also defined for a zero diagonal entry.
-/
def definition_4_3 (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsConsistentlyOrdered (complexify M) ∧
    ∃ k ≤ n, ∀ i j : Fin n, i ≠ j →
      (((i : ℕ) < k ∧ (j : ℕ) < k) ∨ (k ≤ (i : ℕ) ∧ k ≤ (j : ℕ))) → M i j = 0

/-- **Definition 4.3** of [quarteroni2000numerical], the consistent-ordering clause in the letters
of the book. For $M \in \mathbb{R}^{n \times n}$, the complexification of $M$ is consistently
ordered if and only if, for every $\alpha \in \mathbb{C}$ with $\alpha \neq 0$, the spectrum of
$\alpha D^{-1} E + \alpha^{-1} D^{-1} F$ over $\mathbb{C}$ equals the spectrum of
$D^{-1} E + D^{-1} F$.

The backbone `Matrix.jacobiLower` and `Matrix.jacobiUpper` are exactly $D^{-1} E$ and
$D^{-1} F$.

**Reading.** Consistent ordering means independence of the complex spectrum as a set over nonzero
complex parameters. The two diagonal blocks are contiguous in the given matrix order. The displayed
inverses are total in Lean, so the predicate is also defined for a zero diagonal entry.
-/
theorem definition_4_3_iff (M : Matrix (Fin n) (Fin n) ℝ) :
    IsConsistentlyOrdered (complexify M) ↔ ∀ α : ℂ, α ≠ 0 →
      spectrum ℂ (α • ((complexify (D M))⁻¹ * complexify (E M)) +
          α⁻¹ • ((complexify (D M))⁻¹ * complexify (F M))) =
        spectrum ℂ ((complexify (D M))⁻¹ * complexify (E M) +
          (complexify (D M))⁻¹ * complexify (F M)) := by
  have hL : (complexify (D M))⁻¹ * complexify (E M) = jacobiLower (complexify M) := by
    rw [D, E, complexify_neg, complexify_strictLower, complexify_diagPart, jacobiLower, mul_neg,
      neg_mul]
  have hU : (complexify (D M))⁻¹ * complexify (F M) = jacobiUpper (complexify M) := by
    rw [D, F, complexify_neg, complexify_strictUpper, complexify_diagPart, jacobiUpper, mul_neg,
      neg_mul]
  rw [hL, hU]
  rfl

/-- **Equation (4.18)** of [quarteroni2000numerical] for a matrix with the $A$-property: "relation
(4.18) holds even if $A$ enjoys the $A$-property". Let $A \in \mathbb{R}^{n \times n}$ enjoy the
$A$-property and have nonzero diagonal entries. Then
$$\rho(B_{GS}) = \rho(B_J)^2.$$

Only the consistent-ordering clause of Definition 4.3 is used. The proof specializes
`Matrix.IsConsistentlyOrdered.spectralRadius_gaussSeidel_eq_sq`. -/
theorem equation_4_18_of_hasAProperty (hP : definition_4_3 A) (h : IsUnit (diagPart A)) :
    complexSpectralRadius (gaussSeidelSplitting A h).iterationOperator =
      complexSpectralRadius (jacobiSplitting A h).iterationOperator ^ 2 := by
  rw [(complexSpectralRadius_jacobi_gaussSeidel h).1,
    (complexSpectralRadius_jacobi_gaussSeidel h).2]
  exact hP.1.spectralRadius_gaussSeidel_eq_sq _

/-- **Theorem 4.6** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ have nonzero
diagonal entries, and let the Jacobi method be convergent, $\rho(B_J) < 1$. Then for
$0 < \omega \le 1$ the JOR method converges to $A^{-1} b$, for every $b$ and every $x^{(0)}$.

The eigenvalues of $B_{J_\omega} = \omega B_J + (1 - \omega) I$ are
$\omega \lambda + 1 - \omega$, of modulus at most $\omega |\lambda| + 1 - \omega < 1$. The proof
specializes `Matrix.jorSplitting_complexSpectralRadius_lt_one_of_le_one`. -/
theorem theorem_4_6 (h : IsUnit (diagPart A))
    (hJ : complexSpectralRadius (jacobiSplitting A h).iterationOperator < 1) {ω : ℝ}
    (hω0 : 0 < ω) (hω1 : ω ≤ 1) (b x₀ : Fin n → ℝ) :
    Tendsto (fun k => (jorSweep A ω b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) := by
  rw [jorSweep_eq_mulVecStep A h hω0.ne' b]
  exact Splitting.tendsto _ (jorSplitting_complexSpectralRadius_lt_one_of_le_one h hJ hω0 hω1) b x₀

end Convergence

/-! ### Section 4.2.3: Convergence results for the relaxation method -/

section Relaxation

/-- **Theorem 4.7** of [quarteroni2000numerical] (Kahan). Let $n \ge 1$, let
$A \in \mathbb{R}^{n \times n}$ have nonzero diagonal entries, and let $\omega \neq 0$. Then
$$\rho(B(\omega)) \ge |\omega - 1|.$$
Therefore, if $\omega \le 0$ or $\omega \ge 2$, then $\rho(B(\omega)) \ge 1$ and the SOR method
does not converge.

**Reading.** The book states the theorem for any $\omega \in \mathbb{R}$. The SOR splitting
needs $\omega \neq 0$. The case $\omega = 0$ is
`QuarteroniSaccoSaleri.Chapter04.theorem_4_7_zero`.

The product of the eigenvalues of $B(\omega)$ is $\det B(\omega) = (1 - \omega)^n$. The proof
specializes `Matrix.abs_one_sub_le_sorSplitting_complexSpectralRadius` and
`Matrix.lt_two_of_sorSplitting_complexSpectralRadius_lt_one`.

**Reading.** The split SOR matrix requires nonzero relaxation. The unsplit iteration matrix is
handled separately at zero, where it is the identity. The convergence criterion concerns convergence
to the solution for all input states.
-/
theorem theorem_4_7 [NeZero n] (h : IsUnit (diagPart A)) {ω : ℝ} (hω : ω ≠ 0) :
    ENNReal.ofReal |ω - 1| ≤ complexSpectralRadius (sorSplitting A h hω).iterationOperator ∧
      (ω ≤ 0 ∨ 2 ≤ ω → ¬ complexSpectralRadius (sorSplitting A h hω).iterationOperator < 1) := by
  refine ⟨by rw [abs_sub_comm]; exact abs_one_sub_le_sorSplitting_complexSpectralRadius h hω,
    fun hout hρ => ?_⟩
  obtain ⟨h0, h2⟩ := lt_two_of_sorSplitting_complexSpectralRadius_lt_one h hω hρ
  rcases hout with hle | hge
  · exact absurd h0 (not_lt.mpr hle)
  · exact absurd h2 (not_lt.mpr hge)

/-- **Theorem 4.7** of [quarteroni2000numerical] at $\omega = 0$. Let $n \ge 1$, and let
$A \in \mathbb{R}^{n \times n}$ have nonzero diagonal entries. Then the SOR matrix (4.17) at
$\omega = 0$ is $B(0) = I$, and $\rho(I) = 1 = |0 - 1|$. The method is then the trivial
iteration $x^{(k+1)} = x^{(k)}$, which does not converge to the solution in general.

**Reading.** The split SOR matrix requires nonzero relaxation. The unsplit iteration matrix is
handled separately at zero, where it is the identity. The convergence criterion concerns convergence
to the solution for all input states.
-/
theorem theorem_4_7_zero [NeZero n] (h : IsUnit (diagPart A)) :
    sorIterationMatrix A 0 = 1 ∧ complexSpectralRadius (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  have hDdet : IsUnit (diagPart A).det := (isUnit_iff_isUnit_det _).mp h
  refine ⟨?_, ?_⟩
  · rw [sorIterationMatrix, zero_smul, add_zero, sub_zero, zero_smul, sub_zero, one_smul,
      nonsing_inv_mul _ hDdet]
  · rw [complexSpectralRadius, complexify_one]
    have : Nontrivial (Matrix (Fin n) (Fin n) ℂ) := inferInstance
    exact spectrum.spectralRadius_one

/-- **Property 4.3** of [quarteroni2000numerical] (Ostrowski). Let $n \ge 1$, let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite, and let $\omega \neq 0$. Then:

* the SOR method converges to $A^{-1} b$ for every $b$ and every $x^{(0)}$ if and only if
  $0 < \omega < 2$;
* if $0 < \omega < 2$, the convergence is monotone with respect to $\|\cdot\|_A$:
  $\|B(\omega) e\|_A < \|e\|_A$ for every $e \neq 0$.

The equivalence specializes `Matrix.sorSplitting_complexSpectralRadius_lt_one_iff`
(Householder–John and Kahan) and Theorem 4.1. The monotonicity is Property 4.2 for
$P = \omega^{-1} D - E$, for which $P + P^T - A = (2/\omega - 1) D$ is positive definite when
$0 < \omega < 2$ (`Matrix.sorSplitting_m_add_transpose_sub_posDef`,
`Stationary.Splitting.energyNorm_mulVec_iterationOperator_lt`).

**Correction.** Strict contraction is stated for a nonzero error. Once the iterate reaches the
solution, both consecutive errors are zero, so the strict monotonicity written in Property 4.1
cannot hold for every index.
-/
theorem property_4_3 [NeZero n] (hA : A.PosDef) {ω : ℝ} (hω : ω ≠ 0) :
    ((∀ b x₀, Tendsto (fun k => (sorSweep A ω b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b))) ↔
        0 < ω ∧ ω < 2) ∧
      (0 < ω → ω < 2 → ∀ e ≠ 0,
        (A *ᵥ ((sorSplitting A hA.diagPart.isUnit hω).iterationOperator *ᵥ e)) ⬝ᵥ
            ((sorSplitting A hA.diagPart.isUnit hω).iterationOperator *ᵥ e) <
          (A *ᵥ e) ⬝ᵥ e) := by
  have h := hA.diagPart.isUnit
  refine ⟨?_, fun hω0 hω2 e he => ?_⟩
  · simp only [sorSweep_eq_mulVecStep A h hω]
    rw [Splitting.forall_tendsto_iff, sorSplitting_complexSpectralRadius_lt_one_iff hA h hω]
  · exact Splitting.energyNorm_mulVec_iterationOperator_lt _ hA
      (sorSplitting_m_add_transpose_sub_posDef hA.1 (fun i => hA.diag_pos) h hω0 hω2) he

/-- **Property 4.3** of [quarteroni2000numerical], last sentence. Let
$A \in \mathbb{R}^{n \times n}$ be strictly diagonally dominant by rows, and let
$0 < \omega \le 1$. Then the SOR method converges to $A^{-1} b$, for every $b$ and every
$x^{(0)}$.

The proof specializes `Matrix.sorSplitting_complexSpectralRadius_lt_one_of_le_one`. -/
theorem property_4_3_diagDominant (hA : A.IsStrictDiagDominant) {ω : ℝ} (hω0 : 0 < ω)
    (hω1 : ω ≤ 1) (b x₀ : Fin n → ℝ) :
    Tendsto (fun k => (sorSweep A ω b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) := by
  rw [sorSweep_eq_mulVecStep A hA.isUnit_diagPart hω0.ne' b]
  exact Splitting.tendsto _ (sorSplitting_complexSpectralRadius_lt_one_of_le_one hA _ hω0 hω1) b x₀

/-- The real Jacobi matrix has only real eigenvalues if and only if the Jacobi matrix of the
complexification of $A$ has only real eigenvalues. -/
private theorem forall_im_eq_zero_iff (h : IsUnit (diagPart A)) :
    (∀ μ ∈ spectrum ℂ (complexify (jacobiSplitting A h).iterationOperator), μ.im = 0) ↔
      ∀ μ ∈ spectrum ℂ
        (jacobiSplitting (complexify A) (isUnit_diagPart_complexify h)).iterationOperator,
        μ.im = 0 := by
  rw [complexify_jacobi_iterationOperator A h]

/-- The spectral radius of the real SOR matrix $B(\omega)$ equals that of the SOR matrix of the
complexification of $A$. -/
private theorem complexSpectralRadius_sorIterationMatrix (ω : ℝ) :
    complexSpectralRadius (sorIterationMatrix A ω) =
      spectralRadius ℂ (sorIterationMatrix (complexify A) ω) := by
  rw [complexSpectralRadius, complexify_sorIterationMatrix]

/-- **Property 4.4** of [quarteroni2000numerical], the equivalence. Let $n \ge 1$, let
$A \in \mathbb{R}^{n \times n}$ enjoy the $A$-property and have nonzero diagonal entries, let
the Jacobi matrix $B_J$ have only real eigenvalues, and let $\omega \neq 0$. Then the SOR method
converges to $A^{-1} b$ for every $b$ and every $x^{(0)}$ if and only if $\rho(B_J) < 1$ and
$0 < \omega < 2$.

Only the consistent-ordering clause of Definition 4.3 is used. The proof combines Young's theory
(`Matrix.IsConsistentlyOrdered.spectralRadius_sor_lt_one`,
`Matrix.IsConsistentlyOrdered.spectralRadius_jacobi_lt_one_of_sor`) with Kahan's condition and
Theorem 4.1.

**Reading.** The split SOR matrix requires nonzero relaxation. The unsplit iteration matrix is
handled separately at zero, where it is the identity. The convergence criterion concerns convergence
to the solution for all input states.
-/
theorem property_4_4 [NeZero n] (hP : definition_4_3 A) (h : IsUnit (diagPart A))
    (hreal : ∀ μ ∈ spectrum ℂ (complexify (jacobiSplitting A h).iterationOperator), μ.im = 0)
    {ω : ℝ} (hω : ω ≠ 0) :
    (∀ b x₀, Tendsto (fun k => (sorSweep A ω b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b))) ↔
      complexSpectralRadius (jacobiSplitting A h).iterationOperator < 1 ∧ 0 < ω ∧ ω < 2 := by
  have hreal' := (forall_im_eq_zero_iff h).mp hreal
  have hJ := (complexSpectralRadius_jacobi_gaussSeidel h).1
  have hS : complexSpectralRadius (sorSplitting A h hω).iterationOperator =
      spectralRadius ℂ (sorIterationMatrix (complexify A) ω) := by
    rw [sorSplitting_iterationOperator_eq A h hω, complexSpectralRadius_sorIterationMatrix]
  simp only [sorSweep_eq_mulVecStep A h hω]
  rw [Splitting.forall_tendsto_iff]
  constructor
  · intro hρ
    obtain ⟨hω0, hω2⟩ := lt_two_of_sorSplitting_complexSpectralRadius_lt_one h hω hρ
    rw [hS] at hρ
    refine ⟨?_, hω0, hω2⟩
    rw [hJ]
    exact hP.1.spectralRadius_jacobi_lt_one_of_sor _ hreal' hω0 hω2 hρ
  · rintro ⟨hlt, hω0, hω2⟩
    rw [hS]
    rw [hJ] at hlt
    exact hP.1.spectralRadius_sor_lt_one _ hreal' hlt hω0 hω2

/-- **Property 4.4** of [quarteroni2000numerical], equation (4.19) and the optimal spectral radius.
Let $n \ge 1$, let $A \in \mathbb{R}^{n \times n}$ enjoy the $A$-property and have nonzero
diagonal entries, let $B_J$ have only real eigenvalues, and let $\rho_J = \rho(B_J) < 1$. Then
the relaxation parameter
$$\omega_{\mathrm{opt}} = \frac{2}{1 + \sqrt{1 - \rho_J^2}}$$
minimizes $\rho(B(\omega))$ over $0 < \omega < 2$, and the corresponding asymptotic convergence
factor is
$$\rho(B(\omega_{\mathrm{opt}})) = \frac{1 - \sqrt{1 - \rho_J^2}}{1 + \sqrt{1 - \rho_J^2}} =
  \omega_{\mathrm{opt}} - 1.$$

The SOR matrix $B(\omega)$ of (4.17) is `Matrix.sorIterationMatrix A ω`. The proof specializes
`Matrix.IsConsistentlyOrdered.isMinOn_complexSpectralRadius_sor` and
`Matrix.IsConsistentlyOrdered.spectralRadius_sor_optimalRelaxation`.

**Reading.** The optimizing formula is stated on the interval of convergent SOR parameters when the
Jacobi spectral radius is below one. This makes the convergence assumption of the printed
optimization explicit.
-/
theorem property_4_4_optimal [NeZero n] (hP : definition_4_3 A) (h : IsUnit (diagPart A))
    (hreal : ∀ μ ∈ spectrum ℂ (complexify (jacobiSplitting A h).iterationOperator), μ.im = 0)
    (hlt : complexSpectralRadius (jacobiSplitting A h).iterationOperator < 1) :
    IsMinOn (fun ω : ℝ => complexSpectralRadius (sorIterationMatrix A ω)) (Set.Ioo 0 2)
        (2 / (1 + √(1 -
          (complexSpectralRadius (jacobiSplitting A h).iterationOperator).toReal ^ 2))) ∧
      complexSpectralRadius (sorIterationMatrix A (2 / (1 + √(1 -
          (complexSpectralRadius (jacobiSplitting A h).iterationOperator).toReal ^ 2)))) =
        ENNReal.ofReal
          ((1 - √(1 - (complexSpectralRadius (jacobiSplitting A h).iterationOperator).toReal ^ 2))
            / (1 + √(1 -
              (complexSpectralRadius (jacobiSplitting A h).iterationOperator).toReal ^ 2))) := by
  have hreal' := (forall_im_eq_zero_iff h).mp hreal
  have hJ := (complexSpectralRadius_jacobi_gaussSeidel h).1
  rw [hJ] at hlt ⊢
  set r := (spectralRadius ℂ
    (jacobiSplitting (complexify A) (isUnit_diagPart_complexify h)).iterationOperator).toReal
    with hr
  have hopt : (2 / (1 + √(1 - r ^ 2))) = optimalRelaxation r := rfl
  simp only [complexSpectralRadius_sorIterationMatrix, hopt]
  refine ⟨hP.1.isMinOn_complexSpectralRadius_sor _ hreal' hlt, ?_⟩
  rw [hP.1.spectralRadius_sor_optimalRelaxation _ hreal' hlt]
  congr 1
  have hs : 0 ≤ √(1 - r ^ 2) := Real.sqrt_nonneg _
  rw [optimalRelaxation]
  field_simp
  ring

end Relaxation

/-! ### Section 4.2.4: A priori forward analysis -/

section Forward

/-- **Example 4.3** of [quarteroni2000numerical], the matrix. For $m \in \mathbb{N}$, the **matrix
of Example 4.3** is the lower bidiagonal matrix of order $m$ with $a_{ii} = 3/2$,
$a_{i,i-1} = 1$, and all other entries $0$. The book takes $m = 100$.

**Generalization.** The bidiagonal matrix is defined in all finite sizes. The example uses size 100.
-/
noncomputable def example_4_3_matrix (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => if i = j then 3 / 2 else if (j : ℕ) + 1 = i then 1 else 0

/-- An entry of the matrix of Example 4.3 is the sum of its diagonal part and its subdiagonal part.
-/
private theorem example_4_3_matrix_apply (m : ℕ) (i j : Fin m) :
    example_4_3_matrix m i j =
      (if i = j then 3 / 2 else 0) + (if (j : ℕ) + 1 = i then 1 else 0) := by
  simp only [example_4_3_matrix, of_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]

/-- For every order $m$, the matrix $A$ of Example 4.3 satisfies $Ax = b$ with $b_i = 5/2$ and
$x_i = 1 - (-2/3)^i$, with $1$-based indices.

**Generalization.** The formula for the exact solution is proved in every finite size before
specializing to 100.
-/
private theorem example_4_3_mulVec (m : ℕ) :
    example_4_3_matrix m *ᵥ (fun i : Fin m => 1 - (-2 / 3 : ℝ) ^ ((i : ℕ) + 1)) =
      fun _ => 5 / 2 := by
  funext i
  simp only [mulVec, dotProduct, example_4_3_matrix_apply, add_mul, sum_add_distrib, ite_mul,
    zero_mul, one_mul, sum_ite_eq, mem_univ, ite_true]
  rcases i with ⟨i, hi⟩
  cases i with
  | zero =>
    rw [sum_eq_zero fun j _ => by simp]
    norm_num
  | succ k =>
    rw [sum_eq_single ⟨k, by omega⟩]
    · simp only [ite_true]
      ring
    · intro j _ hj
      split_ifs with hjk
      · exact absurd (Fin.ext (by simpa using hjk)) hj
      · rfl
    · intro habs
      exact absurd (mem_univ _) habs

/-- **Example 4.3** of [quarteroni2000numerical], the exact solution. Let
$A \in \mathbb{R}^{100 \times 100}$ be the matrix of Example 4.3, and let $b_i = 5/2$ for all
$i$. Then the solution of $Ax = b$ has the components
$$x_i = 1 - \left(-\tfrac{2}{3}\right)^i, \qquad i = 1, \dots, 100.$$

With $0$-based indices the components are $x_i = 1 - (-2/3)^{i+1}$. -/
theorem example_4_3_solution :
    example_4_3_matrix 100 *ᵥ (fun i : Fin 100 => 1 - (-2 / 3 : ℝ) ^ ((i : ℕ) + 1)) =
      fun _ => 5 / 2 :=
  example_4_3_mulVec 100

/-- The matrix of Example 4.3 is lower triangular. -/
private theorem example_4_3_matrix_isLowerTriangular (m : ℕ) :
    (example_4_3_matrix m).IsLowerTriangular := by
  intro i j hij
  have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
  have h1 : i ≠ j := hij'.ne
  have h2 : (j : ℕ) + 1 ≠ i := by
    have := Fin.lt_def.mp hij'
    omega
  simp [example_4_3_matrix, h1, h2]

/-- The matrix of Example 4.3 has nonzero diagonal entries. -/
private theorem example_4_3_matrix_isUnit_diagPart (m : ℕ) :
    IsUnit (diagPart (example_4_3_matrix m)) :=
  (isUnit_diagPart_iff _).mpr fun i => by simp [example_4_3_matrix]

/-- **Example 4.3** of [quarteroni2000numerical], $\rho(B(1.5)) = 0.5$. For the matrix
$A \in \mathbb{R}^{100 \times 100}$ of Example 4.3, the SOR matrix with $\omega = 3/2$ has
spectral radius
$$\rho(B(3/2)) = 1/2.$$
So the SOR method "should be convergent, working in exact arithmetic".

The matrix is lower triangular, so $\rho(B(\omega)) = |1 - \omega|$ for every $\omega$
(`Matrix.complexSpectralRadius_sorSplitting_of_isLowerTriangular`). -/
theorem example_4_3_spectralRadius :
    complexSpectralRadius (sorSplitting (example_4_3_matrix 100)
        (example_4_3_matrix_isUnit_diagPart 100) (by norm_num : (3 / 2 : ℝ) ≠ 0)).iterationOperator
      = ENNReal.ofReal (1 / 2) := by
  rw [complexSpectralRadius_sorSplitting_of_isLowerTriangular
    (example_4_3_matrix_isLowerTriangular 100)]
  norm_num

/-- **Equation (4.20)** of [quarteroni2000numerical], the computed sequence. Let $A = P - N$ be a
splitting, let $b, x^{(0)} \in \mathbb{R}^n$, and let $\zeta_k \in \mathbb{R}^n$ be the vector
of the rounding errors of step $k$. The **computed sequence** is
$$\hat x^{(0)} = x^{(0)}, \qquad \hat x^{(k+1)} = P^{-1} (N \hat x^{(k)} + b - \zeta_k),$$
that is, $P \hat x^{(k+1)} = N \hat x^{(k)} + b - \zeta_k$.

It is the backbone `Stationary.forcedIterate` with forcing terms $P^{-1} b - P^{-1} \zeta_k$;
see `QuarteroniSaccoSaleri.Chapter04.toLp_perturbedIterate`.

**Reading.** The perturbation sequence is an arbitrary input. This formalizes the recurrence and its
consequences without requiring the printed decomposition of the perturbation into a backward
solution error and a right-hand-side error.
-/
noncomputable def perturbedIterate (s : Splitting A) (b : Fin n → ℝ) (ζ : ℕ → Fin n → ℝ)
    (x₀ : Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => x₀
  | k + 1 => s.m⁻¹ *ᵥ (s.n *ᵥ perturbedIterate s b ζ x₀ k + b - ζ k)

/-- **Equation (4.20)** of [quarteroni2000numerical], the backbone form. Under `WithLp.toLp 2`, the
computed sequence of (4.20) is the forced iteration `Stationary.forcedIterate` of $B = P^{-1} N$
with forcing terms $P^{-1} b - P^{-1} \zeta_k$. -/
theorem toLp_perturbedIterate (s : Splitting A) (b : Fin n → ℝ) (ζ : ℕ → Fin n → ℝ)
    (x₀ : Fin n → ℝ) (k : ℕ) :
    (toLp 2 (perturbedIterate s b ζ x₀ k) : EuclideanSpace ℝ (Fin n)) =
      Stationary.forcedIterate (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) s.iterationOperator)
        (fun j => toLp 2 (s.m⁻¹ *ᵥ b) - toLp 2 (s.m⁻¹ *ᵥ ζ j)) (toLp 2 x₀) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Stationary.forcedIterate_succ, ← ih, perturbedIterate, toEuclideanCLM_toLp, ← toLp_sub,
      ← toLp_add, mulVec_sub, mulVec_add, mulVec_mulVec, s.iterationOperator_eq,
      nonsing_inv_eq_ringInverse, add_sub_assoc]

/-- **Section 4.2.4** of [quarteroni2000numerical], the closed form of the computed sequence. Let
$A = P - N$ be a splitting with $B = P^{-1} N$, and let $\hat x^{(k)}$ be the computed sequence
of (4.20). Then for every $k$
$$\hat x^{(k+1)} = B^{k+1} x^{(0)} + \sum_{j=0}^{k} B^j P^{-1} (b - \zeta_{k-j}).$$

The proof specializes `Stationary.forcedIterate_eq`.

**Reading.** The perturbation sequence is an arbitrary input. This formalizes the recurrence and its
consequences without requiring the printed decomposition of the perturbation into a backward
solution error and a right-hand-side error.
-/
theorem equation_4_20_iterate (s : Splitting A) (b : Fin n → ℝ) (ζ : ℕ → Fin n → ℝ)
    (x₀ : Fin n → ℝ) (k : ℕ) :
    perturbedIterate s b ζ x₀ (k + 1) =
      (s.iterationOperator ^ (k + 1)) *ᵥ x₀ +
        ∑ j ∈ range (k + 1), (s.iterationOperator ^ j) *ᵥ (s.m⁻¹ *ᵥ (b - ζ (k - j))) := by
  have h := Stationary.forcedIterate_eq (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) s.iterationOperator)
    (fun j => toLp 2 (s.m⁻¹ *ᵥ b) - toLp 2 (s.m⁻¹ *ᵥ ζ j)) (toLp 2 x₀) (k + 1)
  rw [← toLp_perturbedIterate] at h
  simp only [Nat.add_sub_cancel, ← toLp_sub, ← mulVec_sub, ← map_pow, toEuclideanCLM_toLp,
    ← toLp_sum, ← toLp_add] at h
  exact toLp_injective 2 h

/-- **Equation (4.20)** of [quarteroni2000numerical], the error decomposition. Let $A = P - N$ be a
splitting with $A$ nonsingular and $B = P^{-1} N$, let $x = A^{-1} b$, and let $\hat x^{(k)}$ be
the computed sequence with rounding errors $\zeta_k$. Then for every $k$ the absolute error
$\hat e^{(k+1)} = x - \hat x^{(k+1)}$ is
$$\hat e^{(k+1)} = B^{k+1} e^{(0)} + \sum_{j=0}^{k} B^j P^{-1} \zeta_{k-j}, \qquad e^{(0)} = x -
  x^{(0)}.$$
The first term is the error of the exact method, which is small for large $k$ when the method
converges. The second term is the propagated rounding error.

The book leaves the analysis of the second term to a paper of Higham;
`QuarteroniSaccoSaleri.Chapter04.equation_4_20_bound` is its simplest form. The proof
specializes `Stationary.sub_forcedIterate_eq`.

**Reading.** The perturbation sequence is an arbitrary input. This formalizes the recurrence and its
consequences without requiring the printed decomposition of the perturbation into a backward
solution error and a right-hand-side error.
-/
theorem equation_4_20 (s : Splitting A) (hA : IsUnit A) (b : Fin n → ℝ) (ζ : ℕ → Fin n → ℝ)
    (x₀ : Fin n → ℝ) (k : ℕ) :
    A⁻¹ *ᵥ b - perturbedIterate s b ζ x₀ (k + 1) =
      (s.iterationOperator ^ (k + 1)) *ᵥ (A⁻¹ *ᵥ b - x₀) +
        ∑ j ∈ range (k + 1), (s.iterationOperator ^ j) *ᵥ (s.m⁻¹ *ᵥ ζ (k - j)) := by
  have hfix : toEuclideanCLM (n := Fin n) (𝕜 := ℝ) s.iterationOperator (toLp 2 (A⁻¹ *ᵥ b)) +
      toLp 2 (s.m⁻¹ *ᵥ b) = (toLp 2 (A⁻¹ *ᵥ b) : EuclideanSpace ℝ (Fin n)) := by
    rw [toEuclideanCLM_toLp, ← toLp_add, ← s.consistent hA b]
  have h := Stationary.sub_forcedIterate_eq
    (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) s.iterationOperator) (toLp 2 (s.m⁻¹ *ᵥ b)) hfix
    (fun j => toLp 2 (s.m⁻¹ *ᵥ ζ j)) (toLp 2 x₀) k
  rw [← toLp_perturbedIterate] at h
  simp only [← toLp_sub, ← map_pow, toEuclideanCLM_toLp, ← toLp_sum, ← toLp_add] at h
  exact toLp_injective 2 h

open scoped Matrix.Norms.L2Operator in
/-- **Section 4.2.4** of [quarteroni2000numerical], a bound on the rounding-error term of (4.20).
Let $A = P - N$ be a splitting with $A$ nonsingular and $B = P^{-1} N$ with $\|B\|_2 < 1$, let
$x = A^{-1} b$, and let $\varepsilon \in \mathbb{R}$ with $\|P^{-1} \zeta_k\|_2 \le \varepsilon$
for all $k$. Then for every $k$ the computed sequence satisfies
$$\|\hat x^{(k)} - x\|_2 \le \|B\|_2^k \|x^{(0)} - x\|_2 + \frac{\varepsilon}{1 - \|B\|_2}.$$
This is the error of the exact method plus a floor proportional to the rounding errors.

This is the simplest form of the analysis that the book cites from a paper of Higham. The norm
of $B$ is the spectral norm (`Matrix.Norms.L2Operator`). The proof specializes
`Stationary.norm_perturbed_iterate_sub_le`.

**Reading.** The book gives the error decomposition and refers elsewhere for propagation analysis.
Lean derives a uniform forcing bound in the Euclidean norm when the iteration operator is a strict
Euclidean contraction.
-/
theorem equation_4_20_bound (s : Splitting A) (hA : IsUnit A) (hB : ‖s.iterationOperator‖ < 1)
    (b : Fin n → ℝ) {ζ : ℕ → Fin n → ℝ} {ε : ℝ}
    (hζ : ∀ k, ‖(toLp 2 (s.m⁻¹ *ᵥ ζ k) : EuclideanSpace ℝ (Fin n))‖ ≤ ε) (x₀ : Fin n → ℝ)
    (k : ℕ) :
    ‖(toLp 2 (perturbedIterate s b ζ x₀ k - A⁻¹ *ᵥ b) : EuclideanSpace ℝ (Fin n))‖ ≤
      ‖s.iterationOperator‖ ^ k * ‖(toLp 2 (x₀ - A⁻¹ *ᵥ b) : EuclideanSpace ℝ (Fin n))‖ +
        ε / (1 - ‖s.iterationOperator‖) := by
  have hfix : toEuclideanCLM (n := Fin n) (𝕜 := ℝ) s.iterationOperator (toLp 2 (A⁻¹ *ᵥ b)) +
      toLp 2 (s.m⁻¹ *ᵥ b) = (toLp 2 (A⁻¹ *ᵥ b) : EuclideanSpace ℝ (Fin n)) := by
    rw [toEuclideanCLM_toLp, ← toLp_add, ← s.consistent hA b]
  have hstep : ∀ j, (toLp 2 (perturbedIterate s b ζ x₀ (j + 1)) : EuclideanSpace ℝ (Fin n)) =
      toEuclideanCLM (n := Fin n) (𝕜 := ℝ) s.iterationOperator
          (toLp 2 (perturbedIterate s b ζ x₀ j)) +
        toLp 2 (s.m⁻¹ *ᵥ b) + -toLp 2 (s.m⁻¹ *ᵥ ζ j) := by
    intro j
    rw [toLp_perturbedIterate, toLp_perturbedIterate, Stationary.forcedIterate_succ,
      sub_eq_add_neg, add_assoc]
  have hξ : ∀ j, ‖(-toLp 2 (s.m⁻¹ *ᵥ ζ j) : EuclideanSpace ℝ (Fin n))‖ ≤ ε := fun j => by
    rw [norm_neg]
    exact hζ j
  have hG : ‖toEuclideanCLM (n := Fin n) (𝕜 := ℝ) s.iterationOperator‖ < 1 := by
    rwa [l2_opNorm_toEuclideanCLM]
  have h := Stationary.norm_perturbed_iterate_sub_le
    (x := fun j => toLp 2 (perturbedIterate s b ζ x₀ j)) hstep hξ hG hfix k
  rwa [l2_opNorm_toEuclideanCLM, ← toLp_sub, ← toLp_sub, perturbedIterate] at h

end Forward

/-! ### Section 4.2.5: Block matrices -/

section Block

variable {ι : Type*} [LinearOrder ι]

/-- The block diagonal part of a symmetric matrix is symmetric. -/
private theorem blockDiagPart_transpose_of_isHermitian (π : Fin n → ι) (hA : A.IsHermitian) :
    (blockDiagPart π A)ᵀ = blockDiagPart π A := by
  have hsymm : ∀ i j, A j i = A i j := fun i j => by
    simpa using congrFun (congrFun hA.eq i) j
  ext i j
  rw [transpose_apply, blockDiagPart_apply, blockDiagPart_apply, hsymm]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · rfl

/-- **Section 4.2.5** of [quarteroni2000numerical]: "Theorem 4.3 is still valid provided $D$ is
substituted by the block diagonal matrix". Let $\pi$ assign a block label to each index, let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite, and let $D$ be the block
diagonal part of $A$ for $\pi$. If $D$ is nonsingular and $2D - A$ is positive definite, then
the block Jacobi method $P = D$, $N = D - A$ converges to $A^{-1} b$, for every $b$ and every
$x^{(0)}$.

The block diagonal part is `Matrix.blockDiagPart π A`, and the splitting is
`Matrix.blockJacobiSplitting`. The proof is the Householder–John theorem with $P = D$ symmetric.
The block Gauss–Seidel and block SOR methods, "introduced in a similar manner", are
`Matrix.blockGaussSeidelSplitting` and `Matrix.blockSORSplitting`.

**Reading.** The block version states convergence with any index partition and invertible block
diagonal, including uneven blocks. The source transfers Theorem 4.3 in full, including its energy
norm equalities.
-/
theorem theorem_4_3_block (π : Fin n → ι) (hA : A.PosDef) (h : IsUnit (blockDiagPart π A))
    (h2 : (2 • blockDiagPart π A - A).PosDef) (b x₀ : Fin n → ℝ) :
    Tendsto (fun k => ((blockJacobiSplitting π A h).mulVecStep b)^[k] x₀) atTop
      (𝓝 (A⁻¹ *ᵥ b)) := by
  refine Splitting.tendsto _ (Splitting.complexSpectralRadius_lt_one_of_posDef _ hA ?_) b x₀
  have hm : (blockJacobiSplitting π A h).m = blockDiagPart π A := rfl
  rw [hm, blockDiagPart_transpose_of_isHermitian π hA.1, ← two_smul ℕ]
  exact h2

end Block

/-! ### Section 4.2.6: Symmetric form of the Gauss–Seidel and SOR methods -/

section Symmetric

/-- Two steps of (4.2) compose into one: $B_2 (B_1 x + f_1) + f_2 = (B_2 B_1) x + (B_2 f_1 + f_2)$.
-/
private theorem affineStep_affineStep (B₁ B₂ : Matrix (Fin n) (Fin n) ℝ) (f₁ f₂ x : Fin n → ℝ) :
    affineStep B₂ f₂ (affineStep B₁ f₁ x) = affineStep (B₂ * B₁) (B₂ *ᵥ f₁ + f₂) x := by
  simp only [affineStep, mulVec_add, mulVec_mulVec, add_assoc]

/-- **Section 4.2.6** of [quarteroni2000numerical], the backward Gauss–Seidel method
$(D - F) x^{(k+1)} = E x^{(k)} + b$, obtained by exchanging $E$ and $F$. Let
$A \in \mathbb{R}^{n \times n}$ have nonzero diagonal entries, and let $b, x \in \mathbb{R}^n$.
The backward Gauss–Seidel step $y$ from $x$ computes
$$y_i = \frac{1}{a_{ii}} \Big( b_i - \sum_{j > i} a_{ij} y_j - \sum_{j < i} a_{ij} x_j \Big)$$
for every $i$. It is the step of the splitting $P = D - F$, $N = E$, it satisfies
$(D - F) y = Ex + b$, and its iteration matrix is $B_{GSb} = (D - F)^{-1} E$.

The sweep is `Matrix.backwardSorSweep A 1 b`, and the splitting is
`Matrix.backwardGaussSeidelSplitting`. The componentwise formula specializes
`Matrix.backwardSorSweep_apply`. -/
theorem backwardGaussSeidel_step (h : IsUnit (diagPart A)) (b x : Fin n → ℝ) :
    (∀ i, backwardSorSweep A 1 b x i =
        (b i - ∑ j ∈ univ.filter (i < ·), A i j * backwardSorSweep A 1 b x j
          - ∑ j ∈ univ.filter (· < i), A i j * x j) / A i i) ∧
      backwardSorSweep A 1 b x = (backwardGaussSeidelSplitting A h).mulVecStep b x ∧
      (backwardGaussSeidelSplitting A h).m = D A - F A ∧
      (backwardGaussSeidelSplitting A h).n = E A ∧
      (D A - F A) *ᵥ backwardSorSweep A 1 b x = E A *ᵥ x + b ∧
      (backwardGaussSeidelSplitting A h).iterationOperator = (D A - F A)⁻¹ * E A := by
  have hm : (backwardGaussSeidelSplitting A h).m = D A - F A := by
    rw [D_sub_F]
    rfl
  have hn : (backwardGaussSeidelSplitting A h).n = E A := by
    change diagPart A + strictUpper A - A = -strictLower A
    rw [eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, add_right_comm,
      diagPart_add_strictLower_add_strictUpper, sub_self]
  have hstep := congrFun (backwardSorSweep_one_eq_mulVecStep A h b) x
  refine ⟨fun i => ?_, hstep, hm, hn, ?_, ?_⟩
  · rw [backwardSorSweep_apply A h 1 b x i, sub_self, zero_mul, add_zero, div_mul_eq_mul_div,
      one_mul]
  · rw [hstep, ← hm, ← hn]
    exact mulVec_nonsing_inv_mulVec (backwardGaussSeidelSplitting A h).isUnit _
  · rw [Splitting.iterationOperator_eq, hm, hn, nonsing_inv_eq_ringInverse]

/-- The Gauss–Seidel step is the step of (4.2) with $B = (D - E)^{-1} F$ and $f = (D - E)^{-1} b$.
-/
private theorem sorSweep_one_eq_affineStep (h : IsUnit (diagPart A)) (b x : Fin n → ℝ) :
    sorSweep A 1 b x = affineStep ((D A - E A)⁻¹ * F A) ((D A - E A)⁻¹ *ᵥ b) x := by
  obtain ⟨-, h1, h2, -, h3⟩ := equation_4_13 h b x
  rw [h1, Splitting.mulVecStep_eq_iterationOperator_mulVec_add, h2, h3]
  rfl

/-- The backward Gauss–Seidel step is the step of (4.2) with $B = (D - F)^{-1} E$ and
$f = (D - F)^{-1} b$. -/
private theorem backwardSorSweep_one_eq_affineStep (h : IsUnit (diagPart A)) (b x : Fin n → ℝ) :
    backwardSorSweep A 1 b x = affineStep ((D A - F A)⁻¹ * E A) ((D A - F A)⁻¹ *ᵥ b) x := by
  obtain ⟨-, h1, h2, -, -, h3⟩ := backwardGaussSeidel_step h b x
  rw [h1, Splitting.mulVecStep_eq_iterationOperator_mulVec_add, h2, h3]
  rfl

/-- **Equation (4.21)** of [quarteroni2000numerical], the symmetric Gauss–Seidel method. Let
$A \in \mathbb{R}^{n \times n}$ have nonzero diagonal entries, and let $b, x \in \mathbb{R}^n$.
One Gauss–Seidel step followed by one backward Gauss–Seidel step,
$$(D - E) x^{(k+1/2)} = F x^{(k)} + b, \qquad (D - F) x^{(k+1)} = E x^{(k+1/2)} + b,$$
is the iteration $x^{(k+1)} = B_{SGS} x^{(k)} + b_{SGS}$ with
$$B_{SGS} = (D - F)^{-1} E (D - E)^{-1} F, \qquad b_{SGS} = (D - F)^{-1} [E (D - E)^{-1} + I]\,
  b.$$
Its preconditioning matrix is $P_{SGS} = (D - E) D^{-1} (D - F)$: the composite step is the step
of the SSOR splitting at $\omega = 1$, whose iteration matrix is $B_{SGS}$.

The proof specializes `Matrix.ssorSplitting_iterationOperator_eq_mul`,
`Matrix.ssorSplitting_one_m` and `Matrix.ssorSweep_eq_mulVecStep`. -/
theorem equation_4_21 (h : IsUnit (diagPart A)) (b x : Fin n → ℝ) :
    backwardSorSweep A 1 b (sorSweep A 1 b x) =
        affineStep ((D A - F A)⁻¹ * E A * (D A - E A)⁻¹ * F A)
          ((D A - F A)⁻¹ *ᵥ ((E A * (D A - E A)⁻¹ + 1) *ᵥ b)) x ∧
      (ssorSplitting A h one_ne_zero one_lt_two.ne).iterationOperator =
        (D A - F A)⁻¹ * E A * (D A - E A)⁻¹ * F A ∧
      (ssorSplitting A h one_ne_zero one_lt_two.ne).m = (D A - E A) * (D A)⁻¹ * (D A - F A) ∧
      backwardSorSweep A 1 b (sorSweep A 1 b x) =
        (ssorSplitting A h one_ne_zero one_lt_two.ne).mulVecStep b x := by
  refine ⟨?_, ?_, ?_, ssorSweep_eq_mulVecStep A h one_ne_zero one_lt_two.ne b x⟩
  · rw [sorSweep_one_eq_affineStep h, backwardSorSweep_one_eq_affineStep h, affineStep_affineStep]
    congr 1
    · simp only [Matrix.mul_assoc]
    · rw [add_mulVec, one_mulVec, mulVec_add, ← mulVec_mulVec, ← mulVec_mulVec]
  · rw [ssorSplitting_iterationOperator_eq_mul, backwardSorSplitting_one, sorSplitting_one,
      (equation_4_13 h b x).2.2.2.2, (backwardGaussSeidel_step h b x).2.2.2.2.2]
    simp only [Matrix.mul_assoc]
  · rw [ssorSplitting_one_m, D_sub_E, D_sub_F, D]

/-- **Property 4.5** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric
positive definite. Then the symmetric Gauss–Seidel method converges to $A^{-1} b$, for every $b$
and every $x^{(0)}$, and the matrix $A B_{SGS}$ is symmetric positive semidefinite.
Equivalently, $B_{SGS}$ is self-adjoint and positive semidefinite in the $A$-inner product.

**Correction.** The book says that $B_{SGS}$ is symmetric positive definite. This is false as
printed: for a diagonal $A$, $B_{SGS} = 0$, and in general $B_{SGS}$ is not symmetric in the
Euclidean sense. Its source, a book of Hackbusch, proves the statement above. The reason is that
$B_{SGS} = I - P_{SGS}^{-1} A$, with $P_{SGS}$ symmetric and $P_{SGS} - A = E D^{-1} F$ positive
semidefinite. Hence the eigenvalues of $B_{SGS}$ lie in $[0, 1)$.

The proof specializes `Matrix.ssorSplitting_complexSpectralRadius_lt_one` and
`Matrix.ssorSplitting_iterationOperator_posSemidef_energy` at $\omega = 1$.

**Correction.** The source claims Euclidean symmetry and positive definiteness of $B_{SGS}$. Lean
proves that $A B_{SGS}$ is symmetric positive semidefinite. Diagonal $A$ gives a zero iteration
matrix, disproving the strict definiteness claim even in the symmetric case.
-/
theorem property_4_5 (hA : A.PosDef) :
    (∀ b x₀, Tendsto (fun k => (fun y => backwardSorSweep A 1 b (sorSweep A 1 b y))^[k] x₀) atTop
        (𝓝 (A⁻¹ *ᵥ b))) ∧
      (A * ((D A - F A)⁻¹ * E A * (D A - E A)⁻¹ * F A)).IsSymm ∧
      (A * ((D A - F A)⁻¹ * E A * (D A - E A)⁻¹ * F A)).PosSemidef := by
  have h := hA.diagPart.isUnit
  have hB := (equation_4_21 h 0 0).2.1
  have hpsd := ssorSplitting_iterationOperator_posSemidef_energy hA h one_pos one_lt_two
  rw [hB] at hpsd
  refine ⟨fun b x₀ => ?_, isHermitian_iff_isSymm.mp hpsd.1, hpsd⟩
  have hsweep : (fun y => backwardSorSweep A 1 b (sorSweep A 1 b y)) =
      (ssorSplitting A h one_ne_zero one_lt_two.ne).mulVecStep b :=
    funext fun y => ssorSweep_eq_mulVecStep A h one_ne_zero one_lt_two.ne b y
  rw [hsweep]
  exact Splitting.tendsto _ (ssorSplitting_complexSpectralRadius_lt_one hA h one_pos one_lt_two)
    b x₀

/-- The SOR step is the step of (4.2) with $B(\omega) = (D - \omega E)^{-1} (\omega F + (1 - \omega)
D)$ and $f = \omega (D - \omega E)^{-1} b$, for $\omega \neq 0$. -/
private theorem sorSweep_eq_affineStep (h : IsUnit (diagPart A)) {ω : ℝ} (hω : ω ≠ 0)
    (b x : Fin n → ℝ) :
    sorSweep A ω b x = affineStep ((D A - ω • E A)⁻¹ * (ω • F A + (1 - ω) • D A))
      (ω • ((D A - ω • E A)⁻¹ *ᵥ b)) x := by
  rw [(equation_4_15 h hω b x).2, Splitting.mulVecStep_eq_iterationOperator_mulVec_add,
    sorSplitting_iterationOperator, D_sub_smul_E, F, smul_neg, neg_add_eq_sub, D]
  have hm : (sorSplitting A h hω).m = ω⁻¹ • (diagPart A + ω • strictLower A) := by
    change ω⁻¹ • diagPart A + strictLower A = _
    rw [smul_add, smul_smul, inv_mul_cancel₀ hω, one_smul]
  rw [hm, inv_smul_of_isUnit (inv_ne_zero hω) (isUnit_diagPart_add_smul_strictLower h ω), inv_inv,
    smul_mulVec]
  rfl

/-- The backward SOR step is the step of (4.2) with $B = (D - \omega F)^{-1} (\omega E + (1 -
\omega) D)$ and $f = \omega (D - \omega F)^{-1} b$, for $\omega \neq 0$. -/
private theorem backwardSorSweep_eq_affineStep (h : IsUnit (diagPart A)) {ω : ℝ} (hω : ω ≠ 0)
    (b x : Fin n → ℝ) :
    backwardSorSweep A ω b x = affineStep ((D A - ω • F A)⁻¹ * (ω • E A + (1 - ω) • D A))
      (ω • ((D A - ω • F A)⁻¹ *ᵥ b)) x := by
  rw [congrFun (backwardSorSweep_eq_mulVecStep A h hω b) x,
    Splitting.mulVecStep_eq_iterationOperator_mulVec_add, backwardSorSplitting_iterationOperator,
    D_sub_smul_F, E, smul_neg, neg_add_eq_sub, D]
  have hm : (backwardSorSplitting A h hω).m = ω⁻¹ • (diagPart A + ω • strictUpper A) := by
    change ω⁻¹ • diagPart A + strictUpper A = _
    rw [smul_add, smul_smul, inv_mul_cancel₀ hω, one_smul]
  rw [hm, inv_smul_of_isUnit (inv_ne_zero hω) (isUnit_diagPart_add_smul_strictUpper h ω), inv_inv,
    smul_mulVec]
  rfl

/-- $(\omega E + (1 - \omega) D)(D - \omega E)^{-1} + I = (2 - \omega) D (D - \omega E)^{-1}$, the
identity behind the vector $b_\omega$ of (4.22). -/
private theorem smul_E_add_smul_D_mul_inv_add_one (h : IsUnit (diagPart A)) (ω : ℝ) :
    (ω • E A + (1 - ω) • D A) * (D A - ω • E A)⁻¹ + 1 = (2 - ω) • (D A * (D A - ω • E A)⁻¹) := by
  have hu : IsUnit (D A - ω • E A) := by
    rw [D_sub_smul_E]
    exact isUnit_diagPart_add_smul_strictLower h ω
  rw [← mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hu), ← add_mul, ← Matrix.smul_mul]
  congr 1
  module

/-- **Equation (4.22)** of [quarteroni2000numerical], the SSOR method. Let
$A \in \mathbb{R}^{n \times n}$ have nonzero diagonal entries, let $\omega \neq 0$ and
$\omega \neq 2$, and let $b, x \in \mathbb{R}^n$. One SOR step followed by one backward SOR step
$(D - \omega F) x^{(k+1)} = [\omega E + (1 - \omega) D] x^{(k+1/2)} + \omega b$ is the iteration
$x^{(k+1)} = B_s(\omega) x^{(k)} + b_\omega$ with
$$B_s(\omega) = (D - \omega F)^{-1} (\omega E + (1 - \omega) D) (D - \omega E)^{-1} (\omega F +
  (1 - \omega) D),$$
$$b_\omega = \omega (2 - \omega) (D - \omega F)^{-1} D (D - \omega E)^{-1} b.$$
Its preconditioning matrix is
$$P_{SSOR}(\omega) = \Big(\frac{1}{\omega} D - E\Big) \frac{\omega}{2 - \omega} D^{-1}
  \Big(\frac{1}{\omega} D - F\Big),$$
that is, the composite step is the step of the SSOR splitting, whose iteration matrix is
$B_s(\omega)$.

The splitting is `Matrix.ssorSplitting`. The proof specializes
`Matrix.ssorSplitting_iterationOperator_eq_mul` and `Matrix.ssorSweep_eq_mulVecStep`. -/
theorem equation_4_22 (h : IsUnit (diagPart A)) {ω : ℝ} (hω : ω ≠ 0) (hω2 : ω ≠ 2)
    (b x : Fin n → ℝ) :
    backwardSorSweep A ω b (sorSweep A ω b x) =
        affineStep ((D A - ω • F A)⁻¹ * (ω • E A + (1 - ω) • D A) * (D A - ω • E A)⁻¹ *
            (ω • F A + (1 - ω) • D A))
          ((ω * (2 - ω)) • ((D A - ω • F A)⁻¹ *ᵥ (D A *ᵥ ((D A - ω • E A)⁻¹ *ᵥ b)))) x ∧
      (ssorSplitting A h hω hω2).iterationOperator =
        (D A - ω • F A)⁻¹ * (ω • E A + (1 - ω) • D A) * (D A - ω • E A)⁻¹ *
          (ω • F A + (1 - ω) • D A) ∧
      (ssorSplitting A h hω hω2).m =
        (ω⁻¹ • D A - E A) * ((ω / (2 - ω)) • (D A)⁻¹) * (ω⁻¹ • D A - F A) ∧
      backwardSorSweep A ω b (sorSweep A ω b x) = (ssorSplitting A h hω hω2).mulVecStep b x := by
  refine ⟨?_, ?_, ?_, ssorSweep_eq_mulVecStep A h hω hω2 b x⟩
  · rw [sorSweep_eq_affineStep h hω, backwardSorSweep_eq_affineStep h hω, affineStep_affineStep]
    congr 1
    · simp only [Matrix.mul_assoc]
    · have key : (ω • E A + (1 - ω) • D A) *ᵥ ((D A - ω • E A)⁻¹ *ᵥ b) + b =
          (2 - ω) • (D A *ᵥ ((D A - ω • E A)⁻¹ *ᵥ b)) := by
        have := congrArg (· *ᵥ b) (smul_E_add_smul_D_mul_inv_add_one h ω)
        simpa only [add_mulVec, one_mulVec, ← mulVec_mulVec, smul_mulVec] using this
      rw [mulVec_smul, ← smul_add, ← mulVec_mulVec, ← mulVec_add, key, mulVec_smul, smul_smul]
  · rw [ssorSplitting_iterationOperator_eq_mul, backwardSorSplitting_iterationOperator,
      sorSplitting_iterationOperator, D_sub_smul_E, D_sub_smul_F, E, F, D, smul_neg, smul_neg,
      neg_add_eq_sub, neg_add_eq_sub]
    simp only [Matrix.mul_assoc]
  · have hD : (D A)⁻¹ = (diagPart A)⁻¹ := rfl
    rw [hD, show ω⁻¹ • D A - E A = ω⁻¹ • (diagPart A + ω • strictLower A) by
        rw [D, E, sub_neg_eq_add, smul_add, smul_smul, inv_mul_cancel₀ hω, one_smul],
      show ω⁻¹ • D A - F A = ω⁻¹ • (diagPart A + ω • strictUpper A) by
        rw [D, F, sub_neg_eq_add, smul_add, smul_smul, inv_mul_cancel₀ hω, one_smul]]
    change (ω * (2 - ω))⁻¹ • ((diagPart A + ω • strictLower A) * (diagPart A)⁻¹ *
      (diagPart A + ω • strictUpper A)) = _
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    have h2 : (2 : ℝ) - ω ≠ 0 := sub_ne_zero_of_ne hω2.symm
    field_simp

/-- **Section 4.2.6** of [quarteroni2000numerical]: "if $A$ is symmetric and positive definite, the
SSOR method is convergent if $0 < \omega < 2$". Let $A \in \mathbb{R}^{n \times n}$ be symmetric
positive definite, and let $0 < \omega < 2$. Then the SSOR method converges to $A^{-1} b$, for
every $b$ and every $x^{(0)}$.

The proof specializes `Matrix.ssorSplitting_complexSpectralRadius_lt_one`: the Householder–John
theorem for the symmetric positive definite matrix $P_{SSOR}(\omega)$, which dominates $A$. The
comparison with SOR and the choice of $\omega$ in the book are prose and are not formalized. -/
theorem ssor_tendsto (hA : A.PosDef) {ω : ℝ} (hω0 : 0 < ω) (hω2 : ω < 2) (b x₀ : Fin n → ℝ) :
    Tendsto (fun k => (fun y => backwardSorSweep A ω b (sorSweep A ω b y))^[k] x₀) atTop
      (𝓝 (A⁻¹ *ᵥ b)) := by
  have h := hA.diagPart.isUnit
  have hsweep : (fun y => backwardSorSweep A ω b (sorSweep A ω b y)) =
      (ssorSplitting A h hω0.ne' hω2.ne).mulVecStep b :=
    funext fun y => ssorSweep_eq_mulVecStep A h hω0.ne' hω2.ne b y
  rw [hsweep]
  exact Splitting.tendsto _ (ssorSplitting_complexSpectralRadius_lt_one hA h hω0 hω2) b x₀

end Symmetric

end QuarteroniSaccoSaleri.Chapter04
