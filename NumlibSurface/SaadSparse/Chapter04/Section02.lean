/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Unbundled.AlgebraNorm
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Numlib.Eigen.Perturbation
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.LinearAlgebra.Matrix.MMatrix
import Numlib.LinearAlgebra.Sparse.Pattern
import Numlib.Stationary.ConsistentlyOrdered
import Numlib.Stationary.DiagDominant
import Numlib.Stationary.RegularSplitting
import Numlib.Stationary.SPD
import Numlib.Stationary.Splitting
import NumlibSurface.SaadSparse.Chapter01.Section08
import NumlibSurface.SaadSparse.Chapter01.Section13
import NumlibSurface.SaadSparse.Chapter04.Section01

/-!
# Saad, Section 4.2: Convergence

This module formalizes §4.2 of [saad2003iterative], the convergence theory of the basic iterative
methods. For $G \in \mathbb{R}^{n \times n}$ and $f \in \mathbb{R}^n$, the affine iteration
$x_{k+1} = Gx_k + f$ (4.28) converges for every $f$ and every $x_0$ if and only if the spectral
radius satisfies $\rho(G) < 1$ (Theorem 4.1), and $\|G\| < 1$ in a consistent matrix norm is
sufficient (Corollary 4.2). Example 4.1 applies this to Richardson's iteration
$x_{k+1} = x_k + \alpha(b - Ax_k)$. Regular splittings (Definition 4.3) converge exactly when
$A^{-1} \ge 0$ (Theorem 4.4).

For diagonally dominant matrices (§4.2.3), the module proves Gershgorin's theorem (Theorem 4.6) and
its refinement for irreducible matrices (Theorem 4.7), the nonsingularity of strictly and
irreducibly diagonally dominant matrices (Corollary 4.8), and the convergence of the Jacobi and
Gauss–Seidel iterations for them (Theorem 4.9). For symmetric positive definite matrices and Young's
theory (§4.2.4–4.2.5), it proves that SOR with $0 < \omega < 2$ converges exactly for positive
definite $A$ (Theorem 4.10), treats Property A, consistent orderings and T-matrices (Definitions
4.11 and 4.13, Propositions 4.12, 4.14 and 4.15), the relation between the eigenvalues of the SOR
and Jacobi iteration matrices (Theorem 4.16), and the optimal relaxation parameter (4.47). The
proofs specialize `Numlib.LinearAlgebra.Matrix.Complexify`, `Numlib.Stationary.DiagDominant`,
`Numlib.Stationary.RegularSplitting`, `Numlib.Stationary.SPD` and
`Numlib.Stationary.ConsistentlyOrdered`.

## Main definitions

* Definition 4.3, `SaadSparse.Chapter04.IsRegularSplitting`: $A = M - N$ with $M$ nonsingular,
  $M^{-1} \ge 0$ and $N \ge 0$.
* Definition 4.5, `SaadSparse.Chapter04.definition_4_5`,
  `SaadSparse.Chapter04.definition_4_5_strict`, `SaadSparse.Chapter04.definition_4_5_irreducible`:
  weak, strict and irreducible diagonal dominance, by columns as printed.
* Example 4.1, `SaadSparse.Chapter04.richardsonStep`: the Richardson step
  $x \mapsto x + \alpha(b - Ax)$.
* Definition 4.11, `SaadSparse.Chapter04.HasPropertyA`: Property A.
* Proposition 4.12, `SaadSparse.Chapter04.antiDiag`: the block anti-diagonal matrix $B$, with its
  parts `SaadSparse.Chapter04.antiDiagL` and `SaadSparse.Chapter04.antiDiagU`.
* Definition 4.13, `SaadSparse.Chapter04.IsConsistentlyOrdered`: a consistent ordering, as a
  labelling of the indices.
* Example 4.2, `SaadSparse.Chapter04.IsTMatrix`: block tridiagonal matrices with diagonal
  matrices as diagonal blocks.

## Main results

* Theorem 4.1, `SaadSparse.Chapter04.theorem_4_1`: the iteration (4.28) converges for every $f$ and
  $x_0$ if and only if $\rho(G) < 1$.
* Corollary 4.2, `SaadSparse.Chapter04.corollary_4_2` and `SaadSparse.Chapter04.corollary_4_2_lp`:
  if $\|G\| < 1$ for a consistent matrix norm, or for an induced $p$-norm, then (4.28) converges to
  $(I - G)^{-1}f$.
* Example 4.1, `SaadSparse.Chapter04.example_4_1_tendsto_iff` and
  `SaadSparse.Chapter04.example_4_1_opt`: for symmetric positive definite $A$, Richardson's
  iteration converges exactly when $0 < \alpha < 2/\lambda_{\max}$, and $\alpha_{opt} =
  2/(\lambda_{\min} + \lambda_{\max})$.
* Theorem 4.4, `SaadSparse.Chapter04.theorem_4_4`: a regular splitting has $\rho(M^{-1}N) < 1$ if
  and only if $A$ is nonsingular with $A^{-1} \ge 0$.
* Definition 4.5, `SaadSparse.Chapter04.definition_4_5_iff`: the column conditions of Definition 4.5
  are the row conditions of the backbone at $A^T$.
* Theorem 4.6, `SaadSparse.Chapter04.theorem_4_6` and `SaadSparse.Chapter04.theorem_4_6_col`: every
  eigenvalue lies in a Gershgorin disc of the rows, and in one of the columns.
* Theorem 4.7, `SaadSparse.Chapter04.theorem_4_7`: for an irreducible matrix, an eigenvalue on the
  boundary of the union of the discs lies on the boundary of every disc.
* Corollary 4.8, `SaadSparse.Chapter04.corollary_4_8_strict`,
  `SaadSparse.Chapter04.corollary_4_8_col`, `SaadSparse.Chapter04.corollary_4_8_irred`,
  `SaadSparse.Chapter04.corollary_4_8_irred_col`: strictly or irreducibly diagonally dominant
  matrices are nonsingular.
* Theorem 4.9, `SaadSparse.Chapter04.theorem_4_9_jacobi`, `SaadSparse.Chapter04.theorem_4_9_gs` and
  their irreducible and column forms: for such matrices the Jacobi and Gauss–Seidel iterations
  converge.
* Theorem 4.10, `SaadSparse.Chapter04.theorem_4_10` and `SaadSparse.Chapter04.theorem_4_10_tendsto`:
  for symmetric $A$ with positive diagonal and $0 < \omega < 2$, SOR converges if and only if $A$ is
  positive definite.
* Proposition 4.12, `SaadSparse.Chapter04.proposition_4_12_neg` and
  `SaadSparse.Chapter04.proposition_4_12_alpha`: the spectrum of a block anti-diagonal matrix is
  symmetric about $0$, and the spectrum of $\alpha L + \alpha^{-1}U$ does not depend on
  $\alpha \neq 0$.
* Equation (4.42), `SaadSparse.Chapter04.hasPropertyA_iff_toBlocks_isDiag`: Property A is the block
  form with diagonal diagonal blocks.
* Proposition 4.14, `SaadSparse.Chapter04.proposition_4_14`: a consistently ordered matrix is
  permuted to a T-matrix, and the permutation commutes with the strict triangular parts.
* Proposition 4.15, `SaadSparse.Chapter04.proposition_4_15`: for a consistently ordered matrix, the
  spectrum of $\alpha L + \alpha^{-1}U$ does not depend on $\alpha \neq 0$.
* §4.2.5, `SaadSparse.Chapter04.hasPropertyA_iff_exists_isConsistentlyOrdered`: $A$ has Property A
  if and only if some symmetric permutation of $A$ is consistently ordered.
* Theorem 4.16, `SaadSparse.Chapter04.theorem_4_16_mp` and `SaadSparse.Chapter04.theorem_4_16_mpr`:
  the relation $(\lambda + \omega - 1)^2 = \lambda \omega^2 \mu^2$ between the eigenvalues of the
  SOR and Jacobi iteration matrices.
* Equation (4.47), `SaadSparse.Chapter04.equation_4_47`: the optimal relaxation parameter
  $\omega_{opt} = 2/(1 + \sqrt{1 - \rho(B)^2})$, at which $\rho = \omega_{opt} - 1$.

## Conventions

* $\rho(G)$ of a real matrix is `Matrix.complexSpectralRadius G`, the spectral radius of $G$ as a
  complex matrix, a value in $[0, \infty]$.
* The induced norm $\|G\|_p$ is `Matrix.lpOpNorm p G`, for $1 \le p \le \infty$. A consistent matrix
  norm is an `AlgebraNorm ℝ` on the matrices.
* Strict row diagonal dominance is `Matrix.IsStrictDiagDominant`, strict column dominance is
  `Matrix.IsStrictColDiagDominant`, and irreducible diagonal dominance by rows and by columns is
  `Matrix.IsIrreduciblyDiagDominant` and `Matrix.IsIrreduciblyColDiagDominant`. Irreducibility is
  `Matrix.IsPatternIrreducible`.

## Implementation notes

* The irreducible clause of Definition 4.5 asks for weak dominance at every index and strict
  dominance at one index or more. Corollary 4.8 and Theorem 4.9 are false without the second
  condition: the matrix $\begin{bmatrix} 1 & -1 \\ -1 & 1 \end{bmatrix}$ is irreducible and weakly
  diagonally dominant, but singular, and its Jacobi iteration matrix
  $\begin{bmatrix} 0 & 1 \\ 1 & 0 \end{bmatrix}$ has spectral radius $1$. The backbone keeps this
  condition as the field `Matrix.IsIrreduciblyDiagDominant.exists_strict`.
* Definition 4.13 is a labelling of the indices, and the surface takes it as
  `SaadSparse.Chapter04.IsConsistentlyOrdered`. The backbone predicate
  `Matrix.IsConsistentlyOrdered` is the spectral property that Young's theory uses (the definition
  of Kress). Proposition 4.15,
  `SaadSparse.Chapter04.IsConsistentlyOrdered.matrix_isConsistentlyOrdered`, is the implication
  between them.
* Proposition 4.12 is proved by the similarity argument of the book: conjugation by
  $\operatorname{diag}(I, -I)$ maps $B$ to $-B$, and conjugation by
  $\operatorname{diag}(I, \alpha I)$ maps $B$ to $\alpha L + \alpha^{-1}U$.
* The matrices of Young's theory (from Definition 4.11 on) are complex.

## Deviations from the source

* **Reading.** The $p$-norm versions of Corollary 4.2 use the induced vector $p$-norms. See
  `SaadSparse.Chapter04.corollary_4_2_lp`,
  `SaadSparse.Chapter04.complexSpectralRadius_lt_one_of_lpOpNorm_lt_one`.
* **Generalization.** The algebra-norm spectral bound allows non-induced norms on real matrices. See
  `SaadSparse.Chapter04.complexSpectralRadius_le_algebraNorm`.
* **Reading.** The complex eigenvalue bound before Theorem 4.6 is specialized to induced vector
  $p$-norms. See `SaadSparse.Chapter04.norm_le_lpOpNorm_of_mem_spectrum`.
* **Reading.** The convergence-factor theorem expresses attainment by a nonzero initial error using
  a limit superior. See `SaadSparse.Chapter04.exists_specific_eq`.
* **Generalization.** The Richardson step and its affine representation allow signed parameters. See
  `SaadSparse.Chapter04.richardsonStep`, `SaadSparse.Chapter04.richardsonStep_eq_affine`.
* **Generalization.** The splitting and convergence criterion for Richardson use all nonzero signed
  parameters. See `SaadSparse.Chapter04.richardsonStep_eq`,
  `SaadSparse.Chapter04.richardson_tendsto_iff`.
* **Reading.** The Richardson spectral-radius formula assumes symmetry and a signed nonzero
  parameter. See `SaadSparse.Chapter04.example_4_1_spectralRadius`.
* **Reading.** The Richardson convergence interval uses a symmetric matrix and the strict bound from
  the final display. See `SaadSparse.Chapter04.example_4_1_tendsto_iff`.
* **Correction.** The indefinite Richardson result excludes the identity step at zero and assumes
  symmetry. See `SaadSparse.Chapter04.example_4_1_diverges`.
* **Reading.** The Richardson optimum uses symmetry and minimizes on the positive parameter range.
  See `SaadSparse.Chapter04.example_4_1_opt`.
* **Reading.** The row readings of Corollary 4.8 follow the Gershgorin argument. See
  `SaadSparse.Chapter04.corollary_4_8_strict`, `SaadSparse.Chapter04.corollary_4_8_irred`.
* **Reading.** The row readings of Theorem 4.9 follow the proof. See
  `SaadSparse.Chapter04.theorem_4_9_jacobi`, `SaadSparse.Chapter04.theorem_4_9_gs`,
  `SaadSparse.Chapter04.theorem_4_9_jacobi_irred`, `SaadSparse.Chapter04.theorem_4_9_gs_irred`.
* **Reading.** The strict column readings of Theorem 4.9 use the printed definition and make
  diagonal nonsingularity explicit. See `SaadSparse.Chapter04.theorem_4_9_jacobi_col`,
  `SaadSparse.Chapter04.theorem_4_9_gs_col`.
* **Reading.** The spectral reading of Theorem 4.10 encodes convergence for every right-hand side
  and starting vector. See `SaadSparse.Chapter04.theorem_4_10`.
* **Reading.** The converse of Theorem 4.16 also excludes a zero SOR eigenvalue. See
  `SaadSparse.Chapter04.theorem_4_16_mpr`.
* **Reading.** The optimal SOR parameter makes the real Jacobi spectrum, radius bound and nonempty
  size explicit. See `SaadSparse.Chapter04.equation_4_47`.

* **Corollary 4.2** (generalization). The norm can be any submultiplicative norm on the real
  matrix space, including norms outside the induced class of §1.5. See
  `SaadSparse.Chapter04.corollary_4_2`.
* **Definition 4.5** (reading). The book prints all three conditions with column sums, while the
  proofs of Theorems 4.6 and 4.9 use row sums. Both forms are stated. See
  `SaadSparse.Chapter04.definition_4_5_iff`.
* **Theorem 4.10** (reading). The convergence criterion quantifies over the right-hand side as
  well as the starting vector. See `SaadSparse.Chapter04.theorem_4_10_tendsto`.
* **Theorem 4.16** (reading). The book uses the name $M_{SOR}$ for the SOR iteration matrix, while
  (4.26) uses it for the preconditioner. The two are named apart. See
  `SaadSparse.Chapter04.theorem_4_16_mp`.

## Not formalized

* **The specific convergence factor of §4.2.1 for a general $d_0$.** The book derives it
  heuristically from the Jordan form.
* **Theorem 4.9 for irreducible column diagonal dominance.** The irreducible case is stated with
  the row sums used in the proof of the book.
-/

open Matrix

namespace SaadSparse.Chapter04

/-! ### §4.2–4.2.2: The affine iteration and its convergence -/

section AffineIteration

open Filter Topology Stationary

open scoped SaadSparse ENNReal

variable {n : ℕ} {A G : Matrix (Fin n) (Fin n) ℝ}

/-! ### Elementary limits of matrices and matrix–vector products -/

/-- If every entry of a sequence of matrices $M_k$ tends to $0$, then $M_k \to 0$. -/
theorem tendsto_zero_of_entries {M : ℕ → Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ i j, Tendsto (fun k => M k i j) atTop (𝓝 0)) : Tendsto M atTop (𝓝 0) := by
  have key : Tendsto (fun k => (fun i j => M k i j : Fin n → Fin n → ℝ)) atTop
      (𝓝 (fun _ _ => (0 : ℝ))) :=
    tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => h i j
  exact key

/-- If $M_k \to 0$, then $M_k v \to 0$ for every fixed vector $v$. This specializes
`Matrix.tendsto_zero_iff_forall_mulVec_tendsto_zero`. -/
theorem tendsto_mulVec_zero {M : ℕ → Matrix (Fin n) (Fin n) ℝ} (h : Tendsto M atTop (𝓝 0))
    (v : Fin n → ℝ) : Tendsto (fun k => M k *ᵥ v) atTop (𝓝 0) :=
  Matrix.tendsto_zero_iff_forall_mulVec_tendsto_zero.mp h v

/-- If $M_k v \to 0$ for every vector $v$, then $M_k \to 0$. This specializes
`Matrix.tendsto_zero_iff_forall_mulVec_tendsto_zero`. -/
theorem tendsto_zero_of_forall_mulVec {M : ℕ → Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ v, Tendsto (fun k => M k *ᵥ v) atTop (𝓝 0)) : Tendsto M atTop (𝓝 0) :=
  Matrix.tendsto_zero_iff_forall_mulVec_tendsto_zero.mpr h

/-! ### The affine iteration (4.28)–(4.30) -/

/-- The affine step $x \mapsto Gx + f$ is continuous. -/
theorem continuous_affineStep (G : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → ℝ) :
    Continuous (affineStep G f) :=
  (Continuous.matrix_mulVec continuous_const continuous_id).add continuous_const

/-- Equation (4.29) of [saad2003iterative]: $x$ is a fixed point of $x \mapsto Gx + f$ if and only
if $(I - G)x = f$. -/
theorem affineStep_fixed_iff (G : Matrix (Fin n) (Fin n) ℝ) (f x : Fin n → ℝ) :
    affineStep G f x = x ↔ (1 - G) *ᵥ x = f := by
  rw [affineStep, sub_mulVec, one_mulVec, sub_eq_iff_eq_add', eq_comm]

/-- Equation (4.29) of [saad2003iterative]: if the iterates of $x \mapsto Gx + f$ from $x_0$
converge to $x$, then $x$ is a fixed point. -/
theorem tendsto_affineStep_fixed {G : Matrix (Fin n) (Fin n) ℝ} {f x₀ x : Fin n → ℝ}
    (h : Tendsto (fun k => (affineStep G f)^[k] x₀) atTop (𝓝 x)) : affineStep G f x = x := by
  have h1 : Tendsto (fun k => (affineStep G f)^[k + 1] x₀) atTop (𝓝 x) := by
    simpa [Function.comp_def] using h.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun k => (affineStep G f)^[k + 1] x₀) atTop (𝓝 (affineStep G f x)) := by
    simpa only [Function.iterate_succ_apply', Function.comp_def] using
      ((continuous_affineStep G f).tendsto x).comp h
  exact tendsto_nhds_unique h2 h1

/-- Equation (4.29) of [saad2003iterative]: if the iterates of the step of a splitting $A = M - N$
from $x_0$ converge to $x$, then $Ax = b$. -/
theorem tendsto_step_solves (s : Splitting A) {b x₀ x : Fin n → ℝ}
    (h : Tendsto (fun k => (Splitting.step s b)^[k] x₀) atTop (𝓝 x)) : A *ᵥ x = b :=
  (step_fixed_iff s b x).mp (tendsto_affineStep_fixed h)

/-- Equation (4.30) of [saad2003iterative]: if $x^*$ is a fixed point of $x \mapsto Gx + f$, the
iterates from $x_0$ satisfy $x_k - x^* = G^k (x_0 - x^*)$. -/
theorem affineStep_iterate_sub {G : Matrix (Fin n) (Fin n) ℝ} {f x' : Fin n → ℝ}
    (hfix : affineStep G f x' = x') (x₀ : Fin n → ℝ) (k : ℕ) :
    (affineStep G f)^[k] x₀ - x' = (G ^ k) *ᵥ (x₀ - x') := by
  have hfix' : G *ᵥ x' + f = x' := hfix
  have hf : f = x' - G *ᵥ x' := eq_sub_of_add_eq' hfix'
  have key : ∀ a : Fin n → ℝ, affineStep G f a - x' = G *ᵥ (a - x') := by
    intro a
    rw [affineStep, mulVec_sub, hf]
    abel
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', key, ih, pow_succ', ← mulVec_mulVec]

/-- Equation (4.30) of [saad2003iterative]: the iterates of $x \mapsto Gx + f$ from $x_0$ satisfy
$x_{k+1} - x_k = G^k (f - (I - G)x_0)$. -/
theorem affineStep_iterate_succ_sub (G : Matrix (Fin n) (Fin n) ℝ) (f x₀ : Fin n → ℝ) (k : ℕ) :
    (affineStep G f)^[k + 1] x₀ - (affineStep G f)^[k] x₀ = (G ^ k) *ᵥ (f - (1 - G) *ᵥ x₀) := by
  have key : ∀ a c : Fin n → ℝ, affineStep G f a - affineStep G f c = G *ᵥ (a - c) := by
    intro a c
    rw [affineStep, affineStep, add_sub_add_right_eq_sub, ← mulVec_sub]
  induction k with
  | zero =>
    change affineStep G f x₀ - x₀ = (G ^ 0) *ᵥ (f - (1 - G) *ᵥ x₀)
    rw [affineStep, pow_zero, one_mulVec, sub_mulVec, one_mulVec]
    abel
  | succ k ih =>
    have h1 : (affineStep G f)^[k + 1 + 1] x₀ = affineStep G f ((affineStep G f)^[k + 1] x₀) :=
      Function.iterate_succ_apply' _ _ _
    have h2 : (affineStep G f)^[k + 1] x₀ = affineStep G f ((affineStep G f)^[k] x₀) :=
      Function.iterate_succ_apply' _ _ _
    rw [h1]
    nth_rewrite 2 [h2]
    rw [key, ih, mulVec_mulVec, ← pow_succ']

/-! ### Theorem 4.1 -/

/-- If $\rho(G) < 1$, the iterates of $x \mapsto Gx + f$ converge from every $x_0$ to every fixed
point $x^*$ of the map. This is the first half of Theorem 4.1 of [saad2003iterative]. -/
theorem tendsto_affineStep_of_complexSpectralRadius_lt_one (hG : complexSpectralRadius G < 1)
    (f x₀ : Fin n → ℝ) {x' : Fin n → ℝ} (hfix : affineStep G f x' = x') :
    Tendsto (fun k => (affineStep G f)^[k] x₀) atTop (𝓝 x') := by
  have hpow : Tendsto (fun k => G ^ k) atTop (𝓝 0) :=
    (tendsto_pow_iff_complexSpectralRadius_lt_one G).mpr hG
  rw [← tendsto_sub_nhds_zero_iff]
  simpa only [affineStep_iterate_sub hfix] using tendsto_mulVec_zero hpow (x₀ - x')

/-- **Theorem 4.1** of [saad2003iterative], forward direction. Let $G \in \mathbb{R}^{n \times n}$
with $\rho(G) < 1$. Then $I - G$ is nonsingular, and for every $f, x_0 \in \mathbb{R}^n$ the
iterates $x_{k+1} = Gx_k + f$ of (4.28) satisfy
$$x_k \to (I - G)^{-1} f.$$

Here $\rho(G)$ is `Matrix.complexSpectralRadius G`. -/
theorem theorem_4_1_mp (hG : complexSpectralRadius G < 1) :
    IsUnit (1 - G) ∧ ∀ f x₀ : Fin n → ℝ,
      Tendsto (fun k => (affineStep G f)^[k] x₀) atTop (𝓝 ((1 - G)⁻¹ *ᵥ f)) := by
  have hu := Chapter01.theorem_1_11_isUnit hG
  refine ⟨hu, fun f x₀ => tendsto_affineStep_of_complexSpectralRadius_lt_one hG f x₀ ?_⟩
  rw [affineStep_fixed_iff]
  exact mulVec_nonsing_inv_mulVec hu f

/-- **Theorem 4.1** of [saad2003iterative], converse direction. Let $G \in \mathbb{R}^{n \times n}$.
If for every $f, x_0 \in \mathbb{R}^n$ the iterates $x_{k+1} = Gx_k + f$ of (4.28) converge,
then $\rho(G) < 1$. -/
theorem theorem_4_1_mpr (h : ∀ f x₀ : Fin n → ℝ,
    ∃ x, Tendsto (fun k => (affineStep G f)^[k] x₀) atTop (𝓝 x)) :
    complexSpectralRadius G < 1 := by
  rw [← tendsto_pow_iff_complexSpectralRadius_lt_one]
  refine tendsto_zero_of_forall_mulVec fun w => ?_
  obtain ⟨x, hx⟩ := h w 0
  have hx1 : Tendsto (fun k => (affineStep G w)^[k + 1] 0) atTop (𝓝 x) := by
    simpa [Function.comp_def] using hx.comp (tendsto_add_atTop_nat 1)
  have hd : Tendsto
      (fun k => (affineStep G w)^[k + 1] 0 - (affineStep G w)^[k] 0) atTop (𝓝 0) := by
    simpa using hx1.sub hx
  simpa only [affineStep_iterate_succ_sub, mulVec_zero, sub_zero] using hd

/-- **Theorem 4.1** of [saad2003iterative]. Let $G \in \mathbb{R}^{n \times n}$. The iterates
$x_{k+1} = Gx_k + f$ of (4.28) converge for every $f \in \mathbb{R}^n$ and every
$x_0 \in \mathbb{R}^n$ if and only if $\rho(G) < 1$. -/
theorem theorem_4_1 (G : Matrix (Fin n) (Fin n) ℝ) :
    (∀ f x₀ : Fin n → ℝ, ∃ x, Tendsto (fun k => (affineStep G f)^[k] x₀) atTop (𝓝 x)) ↔
      complexSpectralRadius G < 1 :=
  ⟨theorem_4_1_mpr, fun hG f x₀ => ⟨_, (theorem_4_1_mp hG).2 f x₀⟩⟩

/-! ### Corollary 4.2 -/

section Lp

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The operator `Matrix.lpCLM p` is multiplicative on powers: the operator of $A^k$ is the $k$-th
power of the operator of $A$. -/
theorem lpCLM_pow (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : lpCLM p (A ^ k) = lpCLM p A ^ k := by
  induction k with
  | zero => simpa using lpCLM_one p
  | succ k ih => rw [pow_succ, pow_succ, lpCLM_mul, ih]

/-- For every $k \ge 0$, including $k = 0$, the induced $p$-norm satisfies
$\|A^k\|_p \le \|A\|_p^k$. -/
theorem lpOpNorm_pow_le (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    lpOpNorm p (A ^ k) ≤ lpOpNorm p A ^ k := by
  simp only [lpOpNorm, lpCLM_pow]
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    exact ContinuousLinearMap.norm_id_le
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg _))

/-- Corollary 4.2 of [saad2003iterative] for an induced norm: if $\|G\|_p < 1$ for some
$1 \le p \le \infty$, then $\rho(G) < 1$.

**Reading.** This is the induced vector $p$-norm case. The source allows any induced matrix norm
under the convention of §1.5.
-/
theorem complexSpectralRadius_lt_one_of_lpOpNorm_lt_one {G : Matrix (Fin n) (Fin n) ℝ}
    (hG : lpOpNorm p G < 1) : complexSpectralRadius G < 1 := by
  have hnn : (0 : ℝ) ≤ lpOpNorm p G := norm_nonneg _
  rw [← tendsto_pow_iff_complexSpectralRadius_lt_one]
  refine tendsto_zero_of_forall_mulVec fun v => ?_
  set y : PiLp p (fun _ : Fin n => ℝ) := WithLp.toLp p v with hy
  have hbound : ∀ k, ‖(WithLp.toLp p ((G ^ k) *ᵥ v) : PiLp p (fun _ : Fin n => ℝ))‖
      ≤ lpOpNorm p G ^ k * ‖y‖ := by
    intro k
    have h1 : (WithLp.toLp p ((G ^ k) *ᵥ v) : PiLp p (fun _ : Fin n => ℝ)) = lpCLM p (G ^ k) y :=
      rfl
    rw [h1]
    exact (lpCLM p (G ^ k)).le_opNorm y |>.trans
      (mul_le_mul_of_nonneg_right (lpOpNorm_pow_le p G k) (norm_nonneg y))
  have hlim : Tendsto (fun k => lpOpNorm p G ^ k * ‖y‖) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hnn hG).mul_const ‖y‖
  have hL : Tendsto (fun k => (WithLp.toLp p ((G ^ k) *ᵥ v) : PiLp p (fun _ : Fin n => ℝ)))
      atTop (𝓝 0) := squeeze_zero_norm hbound hlim
  have hc : Continuous (WithLp.ofLp : PiLp p (fun _ : Fin n => ℝ) → (Fin n → ℝ)) :=
    PiLp.continuous_ofLp p _
  simpa [Function.comp_def] using (hc.tendsto 0).comp hL

/-- **Corollary 4.2** of [saad2003iterative], for the norm induced by a vector $p$-norm. Let
$G \in \mathbb{R}^{n \times n}$ and $1 \le p \le \infty$ with $\|G\|_p < 1$. Then $I - G$ is
nonsingular, and for every $f, x_0$ the iterates of (4.28) converge to $(I - G)^{-1} f$.

The norm $\|G\|_p$ is `Matrix.lpOpNorm p G`.

**Reading.** This is the induced vector $p$-norm case. The source allows any induced matrix norm
under the convention of §1.5.
-/
theorem corollary_4_2_lp {G : Matrix (Fin n) (Fin n) ℝ} (hG : lpOpNorm p G < 1) :
    IsUnit (1 - G) ∧ ∀ f x₀ : Fin n → ℝ,
      Tendsto (fun k => (affineStep G f)^[k] x₀) atTop (𝓝 ((1 - G)⁻¹ *ᵥ f)) :=
  theorem_4_1_mp (complexSpectralRadius_lt_one_of_lpOpNorm_lt_one p hG)

/-- §4.2 of [saad2003iterative], the remark before Theorem 4.6: for $A \in \mathbb{C}^{n \times n}$
and $1 \le p \le \infty$, every eigenvalue $\lambda$ of $A$ satisfies $|\lambda| \le \|A\|_p$.

**Reading.** This complex eigenvalue bound uses an induced vector $p$-norm. The source states the
bound for any induced matrix norm.
-/
theorem norm_le_lpOpNorm_of_mem_spectrum (A : Matrix (Fin n) (Fin n) ℂ) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ A) : ‖μ‖ ≤ lpOpNorm p A := by
  rw [← Matrix.spectrum_toLin'] at hμ
  obtain ⟨v, hv, hv0⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ).exists_hasEigenvector
  have hAv : A *ᵥ v = μ • v := Module.End.mem_eigenspace_iff.mp hv
  set y : PiLp p (fun _ : Fin n => ℂ) := WithLp.toLp p v with hy
  have hy0 : ‖y‖ ≠ 0 := by
    simp only [ne_eq, norm_eq_zero, hy]
    intro hc
    exact hv0 (by simpa using congrArg WithLp.ofLp hc)
  have h1 : lpCLM p A y = μ • y := by
    rw [lpCLM_apply]
    simp [hy, hAv]
  have h2 : ‖μ‖ * ‖y‖ ≤ lpOpNorm p A * ‖y‖ := by
    have h3 := (lpCLM p A).le_opNorm y
    rw [h1, norm_smul] at h3
    exact h3
  exact le_of_mul_le_mul_right (by simpa using h2)
    (lt_of_le_of_ne (norm_nonneg y) (Ne.symm hy0))

end Lp

/-! ### Example 4.1: Richardson's iteration -/

/-- Example 4.1 of [saad2003iterative]: the **Richardson step** with parameter $\alpha$ is
$x \mapsto x + \alpha(b - Ax)$.

**Generalization.** Lean allows signed $\alpha$. The source introduces Richardson iteration with
$\alpha \ge 0$.
-/
def richardsonStep (A : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (b x : Fin n → ℝ) : Fin n → ℝ :=
  x + α • (b - A *ᵥ x)

/-- Example 4.1 of [saad2003iterative]: the Richardson step is the affine map
$x \mapsto G_\alpha x + \alpha b$ with iteration matrix $G_\alpha = I - \alpha A$.

**Generalization.** Lean allows signed $\alpha$. The source introduces Richardson iteration with
$\alpha \ge 0$.
-/
theorem richardsonStep_eq_affine (A : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (b : Fin n → ℝ) :
    richardsonStep A α b = affineStep (1 - α • A) (α • b) := by
  funext x
  rw [richardsonStep, affineStep, sub_mulVec, one_mulVec, smul_mulVec, smul_sub]
  abel

/-- Example 4.1 of [saad2003iterative]: for $\alpha \neq 0$, the Richardson step is the step of the
splitting with $M = \alpha^{-1} I$, `Stationary.Splitting.richardson`.

**Generalization.** Lean allows either sign of the nonzero parameter $\alpha$. The source introduces
$\alpha \ge 0$. At $\alpha=0$ the step is the identity, so convergence in the sense of existence of
a limit need not give a solution.
-/
theorem richardsonStep_eq (A : Matrix (Fin n) (Fin n) ℝ) {α : ℝ} (hα : α ≠ 0) (b : Fin n → ℝ) :
    richardsonStep A α b = Splitting.step (Stationary.Splitting.richardson A hα) b := by
  funext x
  refine (Splitting.step_eq_of_mulVec _ b x _ ?_).symm
  have hm : (Stationary.Splitting.richardson A hα).m = α⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ) := rfl
  have hx : richardsonStep A α b x - x = α • (b - A *ᵥ x) := by
    rw [richardsonStep]; abel
  rw [hm, hx, smul_mulVec, one_mulVec, smul_smul, inv_mul_cancel₀ hα, one_smul]

/-- Example 4.1 of [saad2003iterative]: for $\alpha \neq 0$, Richardson's iteration converges for
every $b$ and every $x_0$ if and only if $\rho(I - \alpha A) < 1$.

**Generalization.** Lean allows either sign of the nonzero parameter $\alpha$. The source introduces
$\alpha \ge 0$. At $\alpha=0$ the step is the identity, so convergence in the sense of existence of
a limit need not give a solution.
-/
theorem richardson_tendsto_iff (A : Matrix (Fin n) (Fin n) ℝ) {α : ℝ} (hα : α ≠ 0) :
    (∀ b x₀ : Fin n → ℝ, ∃ x, Tendsto (fun k => (richardsonStep A α b)^[k] x₀) atTop (𝓝 x)) ↔
      complexSpectralRadius (1 - α • A) < 1 := by
  constructor
  · intro h
    refine theorem_4_1_mpr fun f x₀ => ?_
    obtain ⟨x, hx⟩ := h (α⁻¹ • f) x₀
    refine ⟨x, ?_⟩
    rw [richardsonStep_eq_affine, smul_smul, mul_inv_cancel₀ hα, one_smul] at hx
    exact hx
  · intro hG b x₀
    rw [richardsonStep_eq_affine]
    exact ⟨_, (theorem_4_1_mp hG).2 (α • b) x₀⟩

end AffineIteration

/-! ### §4.2.3: Diagonally dominant matrices -/

section DiagonallyDominant

open Filter Topology Finset Stationary

open scoped SaadSparse

variable {n : ℕ}

/-! ### Definition 4.5 -/

/-- **Definition 4.5** of [saad2003iterative], first condition. A matrix
$A \in \mathbb{K}^{n \times n}$, with $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, is **weakly
diagonally dominant** if
$$|a_{jj}| \ge \sum_{i \neq j} |a_{ij}|, \qquad j = 1, \dots, n.$$

The sum runs down column $j$. This is how the book prints all three conditions of the
definition, while the proofs of Theorems 4.6 and 4.9 use the row form; both forms are stated in
this module. The backbone has no separate predicate for weak dominance: it is the field
`Matrix.IsIrreduciblyDiagDominant.dominant`. -/
def definition_4_5 {𝕜 : Type*} [RCLike 𝕜] (A : Matrix (Fin n) (Fin n) 𝕜) : Prop :=
  ∀ j, ∑ i ∈ univ.erase j, ‖A i j‖ ≤ ‖A j j‖

/-- **Definition 4.5** of [saad2003iterative], second condition. A matrix
$A \in \mathbb{K}^{n \times n}$ is **strictly diagonally dominant** if
$$|a_{jj}| > \sum_{i \neq j} |a_{ij}|, \qquad j = 1, \dots, n.$$
-/
def definition_4_5_strict {𝕜 : Type*} [RCLike 𝕜] (A : Matrix (Fin n) (Fin n) 𝕜) : Prop :=
  ∀ j, ∑ i ∈ univ.erase j, ‖A i j‖ < ‖A j j‖

/-- **Definition 4.5** of [saad2003iterative], third condition. A matrix
$A \in \mathbb{K}^{n \times n}$ is **irreducibly diagonally dominant** if $A$ is irreducible,
$A$ is weakly diagonally dominant, and
$$|a_{jj}| > \sum_{i \neq j} |a_{ij}|$$
for at least one $j$.

Irreducibility is `Matrix.IsPatternIrreducible` of §3.3.4. Neither Corollary 4.8 nor Theorem 4.9
holds without the strict inequality at one $j$: the matrix
$\begin{bmatrix} 1 & -1 \\ -1 & 1 \end{bmatrix}$ is irreducible and weakly diagonally dominant,
but singular. -/
def definition_4_5_irreducible {𝕜 : Type*} [RCLike 𝕜] (A : Matrix (Fin n) (Fin n) 𝕜) : Prop :=
  A.IsPatternIrreducible ∧ definition_4_5 A ∧ ∃ j, ∑ i ∈ univ.erase j, ‖A i j‖ < ‖A j j‖

/-- **Definition 4.5** of [saad2003iterative], read as the predicates of the backbone. For
$A \in \mathbb{K}^{n \times n}$:
* $A$ is weakly diagonally dominant by columns if and only if
  $\sum_{j \neq i} |(A^T)_{ij}| \le |(A^T)_{ii}|$ for every $i$;
* $A$ is strictly diagonally dominant by columns if and only if
  `Matrix.IsStrictColDiagDominant A`;
* $A$ is irreducibly diagonally dominant by columns if and only if
  `Matrix.IsIrreduciblyColDiagDominant A`.

**Reading.** The book prints the three conditions with column sums, while the proofs of Theorems
4.6 and 4.9 use row sums. This module states both forms: the row forms are
`Matrix.IsStrictDiagDominant` and `Matrix.IsIrreduciblyDiagDominant`, and Corollary 4.8 and
Theorem 4.9 are stated for each.

The column predicates of the backbone are the row predicates at $A^T$ by definition, and weak
dominance is the field `Matrix.IsIrreduciblyDiagDominant.dominant` at $A^T$. -/
theorem definition_4_5_iff {𝕜 : Type*} [RCLike 𝕜] (A : Matrix (Fin n) (Fin n) 𝕜) :
    (definition_4_5 A ↔ ∀ i, ∑ j ∈ univ.erase i, ‖Aᵀ i j‖ ≤ ‖Aᵀ i i‖) ∧
      (definition_4_5_strict A ↔ A.IsStrictColDiagDominant) ∧
      (definition_4_5_irreducible A ↔ A.IsIrreduciblyColDiagDominant) :=
  ⟨Iff.rfl, Iff.rfl,
    ⟨fun h => ⟨isPatternIrreducible_transpose_iff.2 h.1, h.2.1, h.2.2⟩,
      fun h => ⟨isPatternIrreducible_transpose_iff.1 h.irreducible, h.dominant, h.exists_strict⟩⟩⟩

/-! ### Theorem 4.6 (Gershgorin) -/

/-- **Theorem 4.6** of [saad2003iterative] (Gershgorin), row form. Let
$A \in \mathbb{C}^{n \times n}$. Every eigenvalue $\lambda$ of $A$ lies in one of the discs
$$|\lambda - a_{ii}| \le \sum_{j \neq i} |a_{ij}|, \qquad i = 1, \dots, n.$$
-/
theorem theorem_4_6 (A : Matrix (Fin n) (Fin n) ℂ) {μ : ℂ} (hμ : μ ∈ spectrum ℂ A) :
    ∃ i, ‖μ - A i i‖ ≤ ∑ j ∈ univ.erase i, ‖A i j‖ := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (spectrum_subset_iUnion_closedBall A hμ)
  exact ⟨i, by simpa [Metric.mem_closedBall, dist_eq_norm] using hi⟩

/-- For $A \in \mathbb{C}^{n \times n}$, the spectrum of $A^T$ is the spectrum of $A$. It supports
the column form of Theorem 4.6.

This is `Matrix.spectrum_transpose` of Mathlib, stated at $\mathbb{C}$ because it is the step
from the row form of Gershgorin's theorem to the column form. -/
theorem spectrum_transpose (A : Matrix (Fin n) (Fin n) ℂ) : spectrum ℂ Aᵀ = spectrum ℂ A :=
  Matrix.spectrum_transpose A

/-- **Theorem 4.6** of [saad2003iterative] (Gershgorin), column form. Let
$A \in \mathbb{C}^{n \times n}$. Every eigenvalue $\lambda$ of $A$ lies in one of the discs
$$|\lambda - a_{jj}| \le \sum_{i \neq j} |a_{ij}|, \qquad j = 1, \dots, n.$$

The proof applies the row form to $A^T$. -/
theorem theorem_4_6_col (A : Matrix (Fin n) (Fin n) ℂ) {μ : ℂ} (hμ : μ ∈ spectrum ℂ A) :
    ∃ j, ‖μ - A j j‖ ≤ ∑ i ∈ univ.erase j, ‖A i j‖ := by
  obtain ⟨j, hj⟩ := theorem_4_6 Aᵀ (by rwa [spectrum_transpose])
  exact ⟨j, hj⟩

/-! ### Corollary 4.8 -/

/-- **Corollary 4.8** of [saad2003iterative], strict dominance by rows. Let
$A \in \mathbb{K}^{n \times n}$ satisfy $|a_{ii}| > \sum_{j \neq i} |a_{ij}|$ for every $i$.
Then $A$ is nonsingular.

**Reading.** These hypotheses use row dominance, as in the Gershgorin argument. The printed
Definition 4.5 gives column dominance.
-/
theorem corollary_4_8_strict {𝕜 : Type*} [RCLike 𝕜] {A : Matrix (Fin n) (Fin n) 𝕜}
    (h : A.IsStrictDiagDominant) : IsUnit A :=
  h.isUnit

/-- **Corollary 4.8** of [saad2003iterative], strict dominance by columns. Let
$A \in \mathbb{K}^{n \times n}$ satisfy $|a_{jj}| > \sum_{i \neq j} |a_{ij}|$ for every $j$.
Then $A$ is nonsingular. -/
theorem corollary_4_8_col {𝕜 : Type*} [RCLike 𝕜] {A : Matrix (Fin n) (Fin n) 𝕜}
    (h : A.IsStrictColDiagDominant) : IsUnit A := by
  have hT : IsUnit Aᵀ := ((IsStrictColDiagDominant.transpose_iff A).mpr h).isUnit
  rwa [isUnit_iff_isUnit_det, det_transpose, ← isUnit_iff_isUnit_det] at hT

/-! ### Theorem 4.9 -/

variable {A : Matrix (Fin n) (Fin n) ℝ}

/-- **Theorem 4.9** of [saad2003iterative], Jacobi, strict dominance by rows. Let
$A \in \mathbb{R}^{n \times n}$ be strictly diagonally dominant by rows. Then for every $b$ and
every $x_0$ the Jacobi iterates converge to the solution $A^{-1}b$.

**Reading.** The Lean theorem uses row dominance, as in the proof. Definition 4.5 prints dominance
by columns.
-/
theorem theorem_4_9_jacobi (h : A.IsStrictDiagDominant) (b x₀ : Fin n → ℝ) :
    Tendsto (fun k => (jacobiStep A b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) := by
  have hd := h.isUnit_diagPart
  rw [jacobiStep_eq hd]
  exact Stationary.Splitting.tendsto_iterate_of_complexSpectralRadius_lt_one _
    (jacobi_complexSpectralRadius_lt_one h hd) b x₀

/-- **Theorem 4.9** of [saad2003iterative], Gauss–Seidel, strict dominance by rows. Let
$A \in \mathbb{R}^{n \times n}$ be strictly diagonally dominant by rows. Then for every $b$ and
every $x_0$ the Gauss–Seidel iterates converge to the solution $A^{-1}b$.

**Reading.** The Lean theorem uses row dominance, as in the proof. Definition 4.5 prints dominance
by columns.
-/
theorem theorem_4_9_gs (h : A.IsStrictDiagDominant) (b x₀ : Fin n → ℝ) :
    Tendsto (fun k => (gsStep A b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) := by
  have hd := h.isUnit_diagPart
  rw [gsStep_eq hd]
  exact Stationary.Splitting.tendsto_iterate_of_complexSpectralRadius_lt_one _
    (gaussSeidel_complexSpectralRadius_lt_one h hd) b x₀

/-- **Theorem 4.9** of [saad2003iterative], Jacobi, strict dominance by columns. Let
$A \in \mathbb{R}^{n \times n}$ be strictly diagonally dominant by columns, with nonsingular
diagonal $D$. Then for every $b$ and every $x_0$ the Jacobi iterates converge to the solution
$A^{-1}b$.

This is the variant of Kress. The proof specializes
`Matrix.jacobi_spectralRadius_lt_one_of_col`.

**Reading.** This is the strict case with column sums, as in the printed Definition 4.5. The proof
in the source instead uses row sums. The explicit nonsingularity of $D$ follows from strict
dominance.
-/
theorem theorem_4_9_jacobi_col (h : A.IsStrictColDiagDominant) (hd : IsUnit (diagPart A))
    (b x₀ : Fin n → ℝ) : Tendsto (fun k => (jacobiStep A b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) := by
  rw [jacobiStep_eq hd]
  exact Stationary.Splitting.tendsto_iterate_of_complexSpectralRadius_lt_one _
    (jacobi_complexSpectralRadius_lt_one_of_col h hd) b x₀

end DiagonallyDominant

/-! ### §4.2.4–4.2.5: Symmetric positive definite matrices and Young's theory -/

section SymmetricPositiveDefinite

/-- `I n₁, n₂` abbreviates `Fin n₁ ⊕ Fin n₂`, the index type of the partition into two blocks over
which Proposition 4.12 is stated. -/
local notation "I" n₁ ", " n₂ => Fin n₁ ⊕ Fin n₂

variable {n₁ n₂ : ℕ}

/-- **Proposition 4.12** of [saad2003iterative], the matrix. For
$B_{12} \in \mathbb{C}^{n_1 \times n_2}$ and $B_{21} \in \mathbb{C}^{n_2 \times n_1}$, the
**block anti-diagonal matrix** is
$$B = \begin{bmatrix} 0 & B_{12} \\ B_{21} & 0 \end{bmatrix}.$$
-/
def antiDiag (B₁₂ : Matrix (Fin n₁) (Fin n₂) ℂ) (B₂₁ : Matrix (Fin n₂) (Fin n₁) ℂ) :
    Matrix (I n₁, n₂) (I n₁, n₂) ℂ :=
  fromBlocks 0 B₁₂ B₂₁ 0

/-- **Proposition 4.12** of [saad2003iterative], the strictly lower block $L = \begin{bmatrix} 0 & 0
\\ B_{21} & 0 \end{bmatrix}$ of $B$. -/
def antiDiagL (B₂₁ : Matrix (Fin n₂) (Fin n₁) ℂ) : Matrix (I n₁, n₂) (I n₁, n₂) ℂ :=
  fromBlocks 0 0 B₂₁ 0

/-- **Proposition 4.12** of [saad2003iterative], the strictly upper block $U = \begin{bmatrix} 0 &
B_{12} \\ 0 & 0 \end{bmatrix}$ of $B$. -/
def antiDiagU (B₁₂ : Matrix (Fin n₁) (Fin n₂) ℂ) : Matrix (I n₁, n₂) (I n₁, n₂) ℂ :=
  fromBlocks 0 B₁₂ 0 0

/-- A block anti-diagonal matrix is the sum $B = L + U$ of its strictly lower and strictly upper
blocks. It supports Proposition 4.12: the family $B(\alpha) = \alpha L + \alpha^{-1}U$ of
`SaadSparse.Chapter04.proposition_4_12_alpha` passes through $B$ at $\alpha = 1$. -/
theorem antiDiag_eq_add (B₁₂ : Matrix (Fin n₁) (Fin n₂) ℂ) (B₂₁ : Matrix (Fin n₂) (Fin n₁) ℂ) :
    antiDiag B₁₂ B₂₁ = antiDiagL B₂₁ + antiDiagU B₁₂ := by
  rw [antiDiag, antiDiagL, antiDiagU, fromBlocks_add]
  simp

/-- The sign-flip matrix $\operatorname{diag}(I, -I)$, an involution. -/
private def signFlip (n₁ n₂ : ℕ) : Matrix (I n₁, n₂) (I n₁, n₂) ℂ := fromBlocks 1 0 0 (-1)

private theorem signFlip_mul_self (n₁ n₂ : ℕ) : signFlip n₁ n₂ * signFlip n₁ n₂ = 1 := by
  rw [signFlip, fromBlocks_multiply]
  simp [← fromBlocks_one]

/-- The matrix $\operatorname{diag}(I, -I)$ as a unit. -/
private def signFlipUnit (n₁ n₂ : ℕ) : (Matrix (I n₁, n₂) (I n₁, n₂) ℂ)ˣ where
  val := signFlip n₁ n₂
  inv := signFlip n₁ n₂
  val_inv := signFlip_mul_self n₁ n₂
  inv_val := signFlip_mul_self n₁ n₂

/-- **Proposition 4.12** of [saad2003iterative], first part. Let $B$ be block anti-diagonal. If
$\mu$ is an eigenvalue of $B$, then $-\mu$ is an eigenvalue of $B$.

The proof conjugates $B$ by $\operatorname{diag}(I, -I)$, which maps $B$ to $-B$. -/
theorem proposition_4_12_neg (B₁₂ : Matrix (Fin n₁) (Fin n₂) ℂ) (B₂₁ : Matrix (Fin n₂) (Fin n₁) ℂ)
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ (antiDiag B₁₂ B₂₁)) :
    -μ ∈ spectrum ℂ (antiDiag B₁₂ B₂₁) := by
  have hconj : ((signFlipUnit n₁ n₂ : (Matrix (I n₁, n₂) (I n₁, n₂) ℂ)ˣ) :
        Matrix (I n₁, n₂) (I n₁, n₂) ℂ) * antiDiag B₁₂ B₂₁ *
      (((signFlipUnit n₁ n₂)⁻¹ : (Matrix (I n₁, n₂) (I n₁, n₂) ℂ)ˣ) :
        Matrix (I n₁, n₂) (I n₁, n₂) ℂ) = -antiDiag B₁₂ B₂₁ := by
    change signFlip n₁ n₂ * antiDiag B₁₂ B₂₁ * signFlip n₁ n₂ = _
    rw [signFlip, antiDiag, fromBlocks_multiply, fromBlocks_multiply]
    simp [fromBlocks_neg]
  have hspec : spectrum ℂ (-antiDiag B₁₂ B₂₁) = spectrum ℂ (antiDiag B₁₂ B₂₁) := by
    rw [← hconj]
    exact spectrum.units_conjugate
  have hneg : -spectrum ℂ (antiDiag B₁₂ B₂₁) = spectrum ℂ (antiDiag B₁₂ B₂₁) := by
    rw [spectrum.neg_eq, hspec]
  rw [← hneg, Set.mem_neg, neg_neg]
  exact hμ

/-- The scaling matrix $\operatorname{diag}(I, \alpha I)$. -/
private def scaleBlock (n₁ n₂ : ℕ) (α : ℂ) : Matrix (I n₁, n₂) (I n₁, n₂) ℂ :=
  fromBlocks 1 0 0 (α • 1)

private theorem scaleBlock_mul_inv (n₁ n₂ : ℕ) {α : ℂ} (hα : α ≠ 0) :
    scaleBlock n₁ n₂ α * scaleBlock n₁ n₂ α⁻¹ = 1 := by
  rw [scaleBlock, scaleBlock, fromBlocks_multiply]
  simp [smul_smul, inv_mul_cancel₀ hα, ← fromBlocks_one]

/-- The matrix $\operatorname{diag}(I, \alpha I)$ as a unit, for $\alpha \neq 0$. -/
private noncomputable def scaleBlockUnit (n₁ n₂ : ℕ) {α : ℂ} (hα : α ≠ 0) :
    (Matrix (I n₁, n₂) (I n₁, n₂) ℂ)ˣ where
  val := scaleBlock n₁ n₂ α
  inv := scaleBlock n₁ n₂ α⁻¹
  val_inv := scaleBlock_mul_inv n₁ n₂ hα
  inv_val := by
    have h := scaleBlock_mul_inv n₁ n₂ (α := α⁻¹) (inv_ne_zero hα)
    rwa [inv_inv] at h

/-- **Proposition 4.12** of [saad2003iterative], second part. Let $B = L + U$ be block anti-diagonal
and let $\alpha \in \mathbb{C}$ with $\alpha \neq 0$. Then
$$\sigma(\alpha L + \alpha^{-1} U) = \sigma(B).$$

The proof conjugates by $\operatorname{diag}(I, \alpha I)$. -/
theorem proposition_4_12_alpha (B₁₂ : Matrix (Fin n₁) (Fin n₂) ℂ) (B₂₁ : Matrix (Fin n₂) (Fin n₁) ℂ)
    {α : ℂ} (hα : α ≠ 0) :
    spectrum ℂ (α • antiDiagL B₂₁ + α⁻¹ • antiDiagU B₁₂) =
      spectrum ℂ (antiDiag B₁₂ B₂₁) := by
  have hconj : ((scaleBlockUnit n₁ n₂ hα : (Matrix (I n₁, n₂) (I n₁, n₂) ℂ)ˣ) :
        Matrix (I n₁, n₂) (I n₁, n₂) ℂ) * antiDiag B₁₂ B₂₁ *
      (((scaleBlockUnit n₁ n₂ hα)⁻¹ : (Matrix (I n₁, n₂) (I n₁, n₂) ℂ)ˣ) :
        Matrix (I n₁, n₂) (I n₁, n₂) ℂ)
      = α • antiDiagL B₂₁ + α⁻¹ • antiDiagU B₁₂ := by
    change scaleBlock n₁ n₂ α * antiDiag B₁₂ B₂₁ * scaleBlock n₁ n₂ α⁻¹ = _
    rw [scaleBlock, scaleBlock, antiDiag, antiDiagL, antiDiagU, fromBlocks_multiply,
      fromBlocks_multiply, fromBlocks_smul, fromBlocks_smul, fromBlocks_add]
    simp [Matrix.smul_mul, Matrix.mul_smul]
  rw [← hconj]
  exact spectrum.units_conjugate

end SymmetricPositiveDefinite

/-! ### §4.2.1: The convergence factors, and Corollary 4.2 for a general matrix norm -/

section Factors

open Filter Topology Stationary

open scoped SaadSparse ENNReal NNReal

variable {n : ℕ}

/-- §1.5 and §4.2 of [saad2003iterative]: let $N$ be a consistent matrix norm on
$\mathbb{R}^{n \times n}$, that is a norm that is submultiplicative, absolutely homogeneous and
positive definite. Then $\rho(G) \le N(G)$ for every $G$. This is the remark
$|\lambda| \le \|A\|$ before Theorem 4.6, for a norm that need not be an induced $p$-norm.

The norm $N$ is an `AlgebraNorm ℝ` on `Matrix (Fin n) (Fin n) ℝ`.

**Generalization.** Lean allows every submultiplicative real algebra norm on these real matrices,
including norms outside the induced class of §1.5. The pre-Gershgorin statement in the source also
applies to complex matrices.
-/
theorem complexSpectralRadius_le_algebraNorm (N : AlgebraNorm ℝ (Matrix (Fin n) (Fin n) ℝ))
    (G : Matrix (Fin n) (Fin n) ℝ) : complexSpectralRadius G ≤ ENNReal.ofReal (N G) := by
  have hnn : ∀ B : Matrix (Fin n) (Fin n) ℝ, 0 ≤ N B := fun B => apply_nonneg N B
  set f : Matrix (Fin n) (Fin n) ℝ → ℝ≥0 := fun B => ⟨N B, hnn B⟩ with hf
  have hcoe : ∀ B : Matrix (Fin n) (Fin n) ℝ, ((f B : ℝ≥0) : ℝ) = N B := fun _ => rfl
  have hmul : ∀ B C : Matrix (Fin n) (Fin n) ℝ, f (B * C) ≤ f B * f C := by
    intro B C
    rw [← NNReal.coe_le_coe, NNReal.coe_mul, hcoe, hcoe, hcoe]
    exact map_mul_le_mul N B C
  have hsmul : ∀ (r : ℝ) (B : Matrix (Fin n) (Fin n) ℝ), f (r • B) = ‖r‖₊ * f B := by
    intro r B
    refine NNReal.coe_injective ?_
    rw [NNReal.coe_mul, coe_nnnorm, hcoe, hcoe]
    exact map_smul_eq_mul N r B
  have hzero : ∀ B : Matrix (Fin n) (Fin n) ℝ, f B = 0 → B = 0 := by
    intro B hB
    refine eq_zero_of_map_eq_zero N ?_
    rw [← hcoe B, hB, NNReal.coe_zero]
  rw [ENNReal.ofReal_eq_coe_nnreal (hnn G)]
  exact Matrix.complexSpectralRadius_le_of_norm f G hmul hsmul hzero

/-- **Corollary 4.2** of [saad2003iterative]. Let $N$ be a consistent matrix norm on
$\mathbb{R}^{n \times n}$, and let $G \in \mathbb{R}^{n \times n}$ with $N(G) < 1$. Then $I - G$
is nonsingular, and for every $f, x_0$ the iterates of (4.28) converge to $(I - G)^{-1} f$.

**Generalization.** The book uses its convention of induced matrix norms from §1.5. The statement
allows any submultiplicative norm on the real matrix space, because each such norm bounds the
spectral radius.

The norm $N$ is an `AlgebraNorm ℝ`. The case of an induced $p$-norm is
`SaadSparse.Chapter04.corollary_4_2_lp`. -/
theorem corollary_4_2 (N : AlgebraNorm ℝ (Matrix (Fin n) (Fin n) ℝ))
    {G : Matrix (Fin n) (Fin n) ℝ} (hG : N G < 1) :
    IsUnit (1 - G) ∧ ∀ f x₀ : Fin n → ℝ,
      Tendsto (fun k => (affineStep G f)^[k] x₀) atTop (𝓝 ((1 - G)⁻¹ *ᵥ f)) := by
  refine theorem_4_1_mp ((complexSpectralRadius_le_algebraNorm N G).trans_lt ?_)
  exact ENNReal.ofReal_lt_one.mpr hG

/-- **Section 4.2.1** of [saad2003iterative], the general convergence factor. Let
$G \in \mathbb{R}^{n \times n}$ with $n \ge 1$. Some initial error $d_0 \neq 0$ has the specific
convergence factor $\rho(G)$:
$$\limsup_{k \to \infty} \left( \frac{\|G^k d_0\|_2}{\|d_0\|_2} \right)^{1/k} = \rho(G).$$
So the general convergence factor $\rho(G)$ is attained.

**Reading.** Lean formulates attainment at a nonzero initial error using a limit superior. The
source defines the specific factor by an ordinary limit and obtains the general factor by maximizing
the ratio over initial errors at each step.
-/
theorem exists_specific_eq [NeZero n] (G : Matrix (Fin n) (Fin n) ℝ) :
    ∃ d₀ : Fin n → ℝ, d₀ ≠ 0 ∧
      limsup (fun k : ℕ => (‖(WithLp.toLp 2 ((G ^ k) *ᵥ d₀) : EuclideanSpace ℝ (Fin n))‖ /
          ‖(WithLp.toLp 2 d₀ : EuclideanSpace ℝ (Fin n))‖) ^ (1 / k : ℝ)) atTop =
        (complexSpectralRadius G).toReal :=
  Matrix.exists_limsup_norm_pow_mulVec_rpow_eq G

end Factors

/-! ### Example 4.1: The spectral analysis of Richardson's iteration -/

section Richardson

open Filter Topology Stationary

open scoped SaadSparse ENNReal

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {lmin lmax : ℝ}

/-- **Example 4.1** of [saad2003iterative], the spectral radius. Let $A \in \mathbb{R}^{n \times n}$
be symmetric, and let $\lambda_{\min}$ and $\lambda_{\max}$ be eigenvalues of $A$ such that
every eigenvalue of $A$ lies in $[\lambda_{\min}, \lambda_{\max}]$. Then for $\alpha \neq 0$ the
iteration matrix $G_\alpha = I - \alpha A$ of Richardson's iteration has
$$\rho(G_\alpha) = \max\{|1 - \alpha \lambda_{\min}|, |1 - \alpha \lambda_{\max}|\}.$$

**Reading.** The source assumes real eigenvalues, and the formula applies at $\alpha=0$. Lean
assumes the stronger condition of symmetry and takes signed nonzero $\alpha$.
-/
theorem example_4_1_spectralRadius (hA : A.IsHermitian) (hsub : spectrum ℝ A ⊆ Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ A) (hmax : lmax ∈ spectrum ℝ A) {α : ℝ} (hα : α ≠ 0) :
    complexSpectralRadius (1 - α • A) = ENNReal.ofReal (max |1 - α * lmin| |1 - α * lmax|) := by
  rw [← Splitting.richardson_iterationOperator A hα]
  exact Splitting.richardson_complexSpectralRadius_eq hA hsub hmin hmax hα

/-- **Example 4.1** of [saad2003iterative], convergence. Let $A \in \mathbb{R}^{n \times n}$ be
symmetric with smallest and largest eigenvalues $\lambda_{\min}$ and $\lambda_{\max}$, as in
`SaadSparse.Chapter04.example_4_1_spectralRadius`, and let $\lambda_{\min} > 0$. For
$\alpha \neq 0$, Richardson's iteration converges for every right-hand side $b$ and every
starting vector $x_0$ if and only if
$$0 < \alpha < \frac{2}{\lambda_{\max}}.$$

**Reading.** Lean assumes symmetry, whereas the source assumes real eigenvalues. It also allows
signed nonzero $\alpha$ when stating the equivalence. The strict upper bound in the final interval
of the source is used. The preceding sentence prints a weak inequality.
-/
theorem example_4_1_tendsto_iff (hA : A.IsHermitian) (hsub : spectrum ℝ A ⊆ Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ A) (hmax : lmax ∈ spectrum ℝ A) (hpos : 0 < lmin) {α : ℝ}
    (hα : α ≠ 0) :
    (∀ b x₀ : Fin n → ℝ, ∃ x, Tendsto (fun k => (richardsonStep A α b)^[k] x₀) atTop (𝓝 x)) ↔
      0 < α ∧ α < 2 / lmax := by
  rw [richardson_tendsto_iff A hα, ← Splitting.richardson_iterationOperator A hα]
  exact Splitting.richardson_complexSpectralRadius_lt_one_iff hA hsub hmin hmax hpos hα

/-- **Example 4.1** of [saad2003iterative], indefinite case. Let $A \in \mathbb{R}^{n \times n}$ be
symmetric with smallest and largest eigenvalues $\lambda_{\min} < 0 < \lambda_{\max}$. Then for
every $\alpha \neq 0$ there are a right-hand side $b$ and a starting vector $x_0$ for which
Richardson's iteration does not converge.

**Correction.** At $\alpha=0$ the iterates are constant, although the source says divergence occurs
for some initial guess for any $\alpha$. Lean assumes symmetry, which is stronger than the source's
real-spectrum hypothesis, and proves divergence for some right-hand side and initial vector for
either sign of nonzero $\alpha$.
-/
theorem example_4_1_diverges (hA : A.IsHermitian) (hsub : spectrum ℝ A ⊆ Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ A) (hmax : lmax ∈ spectrum ℝ A) (hneg : lmin < 0) (hpos : 0 < lmax)
    {α : ℝ} (hα : α ≠ 0) :
    ∃ b x₀ : Fin n → ℝ, ¬ ∃ x, Tendsto (fun k => (richardsonStep A α b)^[k] x₀) atTop (𝓝 x) := by
  have hge : (1 : ℝ) ≤ max |1 - α * lmin| |1 - α * lmax| := by
    rcases lt_or_gt_of_ne hα with hlt | hlt
    · refine le_max_of_le_right ?_
      rw [le_abs]
      exact Or.inl (by nlinarith)
    · refine le_max_of_le_left ?_
      rw [le_abs]
      exact Or.inl (by nlinarith)
  have hρ : ¬ complexSpectralRadius (1 - α • A) < 1 := by
    rw [example_4_1_spectralRadius hA hsub hmin hmax hα, not_lt, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hge
  by_contra hcon
  push Not at hcon
  exact hρ ((richardson_tendsto_iff A hα).mp fun b x₀ => hcon b x₀)

/-- **Example 4.1** of [saad2003iterative], the optimal parameter. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric with smallest and largest eigenvalues
$0 < \lambda_{\min} \le \lambda_{\max}$. Over $\alpha > 0$, the spectral radius
$\rho(I - \alpha A)$ is smallest at $\alpha_{opt} = 2/(\lambda_{\min} + \lambda_{\max})$, and
$$\rho(I - \alpha_{opt} A) = \frac{\lambda_{\max} - \lambda_{\min}}{\lambda_{\max} +
  \lambda_{\min}}.$$

**Reading.** Lean assumes symmetry, which is stronger than having real eigenvalues, and states the
minimization over $\alpha>0$. Including zero gives the same optimizer in the source's nonnegative
parameter range.
-/
theorem example_4_1_opt (hA : A.IsHermitian) (hsub : spectrum ℝ A ⊆ Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ A) (hmax : lmax ∈ spectrum ℝ A) (hpos : 0 < lmin) :
    IsMinOn (fun α : ℝ => complexSpectralRadius (1 - α • A)) (Set.Ioi 0)
        (2 / (lmin + lmax)) ∧
      complexSpectralRadius (1 - (2 / (lmin + lmax)) • A) =
        ENNReal.ofReal ((lmax - lmin) / (lmax + lmin)) :=
  ⟨Splitting.isMinOn_richardson_complexSpectralRadius hA hsub hmin hmax hpos,
    Splitting.richardson_complexSpectralRadius_optimal_eq hA hsub hmin hmax hpos⟩

end Richardson

/-! ### Definition 4.3 and Theorem 4.4: Regular splittings -/

section Regular

open Filter Topology Stationary

open scoped SaadSparse ENNReal

variable {n : ℕ} {A M N : Matrix (Fin n) (Fin n) ℝ}

/-- **Definition 4.3** of [saad2003iterative]. For $A, M, N \in \mathbb{R}^{n \times n}$, the
decomposition $A = M - N$ is a **regular splitting** of $A$ if $M$ is nonsingular, $M^{-1}$ is
entrywise nonnegative and $N$ is entrywise nonnegative. -/
def IsRegularSplitting (A M N : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  A = M - N ∧ IsUnit M ∧ (∀ i j, 0 ≤ M⁻¹ i j) ∧ ∀ i j, 0 ≤ N i j

/-- For a regular splitting $A = M - N$, the complementary part of the splitting
`Stationary.Splitting A` with matrix $M$ is $N$. -/
theorem splitting_n_eq (h : IsRegularSplitting A M N) :
    (⟨M, h.2.1⟩ : Splitting A).n = N := by
  have h1 : (⟨M, h.2.1⟩ : Splitting A).n = M - A := rfl
  rw [h1, h.1]
  abel

/-- **Definition 4.3** of [saad2003iterative], as the backbone predicate. If $A = M - N$ and $M$ is
nonsingular, then $A = M - N$ is a regular splitting if and only if the splitting with matrix
$M$ satisfies `Stationary.Splitting.IsRegular`. -/
theorem isRegularSplitting_iff (hMN : A = M - N) (hM : IsUnit M) :
    IsRegularSplitting A M N ↔ (⟨M, hM⟩ : Splitting A).IsRegular := by
  have hn : (⟨M, hM⟩ : Splitting A).n = N := by
    have h1 : (⟨M, hM⟩ : Splitting A).n = M - A := rfl
    rw [h1, hMN]; abel
  have hinv : Ring.inverse (⟨M, hM⟩ : Splitting A).m = M⁻¹ :=
    (nonsing_inv_eq_ringInverse M).symm
  rw [Stationary.Splitting.IsRegular, hinv, hn]
  simp only [Matrix.entrywiseNonneg_iff, IsRegularSplitting]
  exact ⟨fun h => ⟨h.2.2.1, h.2.2.2⟩, fun h => ⟨hMN, hM, h.1, h.2⟩⟩

/-- **Theorem 4.4** of [saad2003iterative]. Let $A = M - N$ be a regular splitting of
$A \in \mathbb{R}^{n \times n}$. Then $\rho(M^{-1}N) < 1$ if and only if $A$ is nonsingular and
$A^{-1}$ is entrywise nonnegative. -/
theorem theorem_4_4 (h : IsRegularSplitting A M N) :
    complexSpectralRadius (M⁻¹ * N) < 1 ↔ IsUnit A ∧ ∀ i j, 0 ≤ A⁻¹ i j := by
  have hreg : (⟨M, h.2.1⟩ : Splitting A).IsRegular :=
    (isRegularSplitting_iff h.1 h.2.1).mp h
  have hiter : (⟨M, h.2.1⟩ : Splitting A).iterationOperator = M⁻¹ * N := by
    rw [Stationary.Splitting.iterationOperator_eq, splitting_n_eq h,
      ← nonsing_inv_eq_ringInverse]
  rw [← hiter, hreg.complexSpectralRadius_lt_one_iff]
  simp [Matrix.entrywiseNonneg_iff]

/-- **Theorem 4.4** of [saad2003iterative], the remark after it. Let $A \in \mathbb{R}^{n \times n}$
be an M-matrix and let $A = M - N$ be a regular splitting. Then for every $b$ and every $x_0$
the iterates of (4.34), $x_{k+1} = M^{-1}Nx_k + M^{-1}b$, converge to $A^{-1}b$.

The M-matrix is `Matrix.IsMMatrix`. -/
theorem theorem_4_4_mmatrix (h : IsRegularSplitting A M N) (hA : A.IsMMatrix) (b x₀ : Fin n → ℝ) :
    Tendsto (fun k => (affineStep (M⁻¹ * N) (M⁻¹ *ᵥ b))^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) := by
  have hreg : (⟨M, h.2.1⟩ : Splitting A).IsRegular :=
    (isRegularSplitting_iff h.1 h.2.1).mp h
  have hiter : (⟨M, h.2.1⟩ : Splitting A).iterationOperator = M⁻¹ * N := by
    rw [Stationary.Splitting.iterationOperator_eq, splitting_n_eq h,
      ← nonsing_inv_eq_ringInverse]
  have hstep : affineStep (M⁻¹ * N) (M⁻¹ *ᵥ b) = Splitting.step (⟨M, h.2.1⟩ : Splitting A) b := by
    rw [Splitting.step, hiter]
  rw [hstep]
  exact Stationary.Splitting.tendsto_iterate_of_complexSpectralRadius_lt_one _
    (hiter ▸ hreg.complexSpectralRadius_lt_one_of_isMMatrix hA) b x₀

end Regular

/-! ### Theorem 4.7, and the irreducible parts of Corollary 4.8 and Theorem 4.9 -/

section Irreducible

open Filter Topology Finset Stationary

open scoped SaadSparse

variable {n : ℕ}

/-- **Theorem 4.7** of [saad2003iterative]. Let $A \in \mathbb{C}^{n \times n}$ be irreducible, and
let $\lambda$ be an eigenvalue of $A$ on the boundary of the union of the Gershgorin discs $\{z
: |z - a_{ii}| \le \sum_{j \neq i} |a_{ij}|\}$. Then $\lambda$ lies on the boundary of every
disc:
$$|\lambda - a_{ii}| = \sum_{j \neq i} |a_{ij}|, \qquad i = 1, \dots, n.$$
-/
theorem theorem_4_7 {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsPatternIrreducible) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ A)
    (hfr : μ ∈ frontier (⋃ i, Metric.closedBall (A i i) (∑ j ∈ univ.erase i, ‖A i j‖)))
    (i : Fin n) : ‖μ - A i i‖ = ∑ j ∈ univ.erase i, ‖A i j‖ :=
  hA.norm_sub_eq_of_mem_frontier hμ hfr i

/-- **Corollary 4.8** of [saad2003iterative], irreducible dominance by rows. Let
$A \in \mathbb{K}^{n \times n}$ be irreducibly diagonally dominant by rows. Then $A$ is
nonsingular.

**Reading.** These hypotheses use row dominance, as in the Gershgorin argument. The printed
Definition 4.5 gives column dominance.
-/
theorem corollary_4_8_irred {𝕜 : Type*} [RCLike 𝕜] {A : Matrix (Fin n) (Fin n) 𝕜}
    (h : A.IsIrreduciblyDiagDominant) : IsUnit A :=
  h.isUnit

/-- **Corollary 4.8** of [saad2003iterative], irreducible dominance by columns, the reading of
Definition 4.5 as printed. Let $A \in \mathbb{K}^{n \times n}$ be irreducibly diagonally
dominant by columns. Then $A$ is nonsingular. -/
theorem corollary_4_8_irred_col {𝕜 : Type*} [RCLike 𝕜] {A : Matrix (Fin n) (Fin n) 𝕜}
    (h : A.IsIrreduciblyColDiagDominant) : IsUnit A := by
  have hT : IsUnit Aᵀ := Matrix.IsIrreduciblyDiagDominant.isUnit h
  rwa [isUnit_iff_isUnit_det, det_transpose, ← isUnit_iff_isUnit_det] at hT

variable {A : Matrix (Fin n) (Fin n) ℝ}

/-- **Theorem 4.9** of [saad2003iterative], Jacobi, irreducible dominance by rows. Let
$A \in \mathbb{R}^{n \times n}$ be irreducibly diagonally dominant by rows. Then for every $b$
and every $x_0$ the Jacobi iterates converge to the solution $A^{-1}b$.

**Reading.** The Lean theorem uses row dominance, as in the proof. Definition 4.5 prints dominance
by columns.
-/
theorem theorem_4_9_jacobi_irred (h : A.IsIrreduciblyDiagDominant) (b x₀ : Fin n → ℝ) :
    Tendsto (fun k => (jacobiStep A b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) := by
  rw [jacobiStep_eq h.isUnit_diagPart]
  exact Stationary.Splitting.tendsto_iterate_of_complexSpectralRadius_lt_one _
    (h.jacobi_complexSpectralRadius_lt_one h.isUnit_diagPart) b x₀

/-- **Theorem 4.9** of [saad2003iterative], Gauss–Seidel, irreducible dominance by rows. Let
$A \in \mathbb{R}^{n \times n}$ be irreducibly diagonally dominant by rows. Then for every $b$
and every $x_0$ the Gauss–Seidel iterates converge to the solution $A^{-1}b$.

**Reading.** The Lean theorem uses row dominance, as in the proof. Definition 4.5 prints dominance
by columns.
-/
theorem theorem_4_9_gs_irred (h : A.IsIrreduciblyDiagDominant) (b x₀ : Fin n → ℝ) :
    Tendsto (fun k => (gsStep A b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) := by
  rw [gsStep_eq h.isUnit_diagPart]
  exact Stationary.Splitting.tendsto_iterate_of_complexSpectralRadius_lt_one _
    (h.gaussSeidel_complexSpectralRadius_lt_one h.isUnit_diagPart) b x₀

/-- **Theorem 4.9** of [saad2003iterative], Gauss–Seidel, strict dominance by columns, the reading
of Definition 4.5 as printed. Let $A \in \mathbb{R}^{n \times n}$ be strictly diagonally
dominant by columns, with nonsingular diagonal $D$. Then for every $b$ and every $x_0$ the
Gauss–Seidel iterates converge to the solution $A^{-1}b$.

**Reading.** This is the strict case with column sums, as in the printed Definition 4.5. The proof
in the source instead uses row sums. The explicit nonsingularity of $D$ follows from strict
dominance.
-/
theorem theorem_4_9_gs_col (h : A.IsStrictColDiagDominant) (hd : IsUnit (diagPart A))
    (b x₀ : Fin n → ℝ) : Tendsto (fun k => (gsStep A b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) := by
  rw [gsStep_eq hd]
  exact Stationary.Splitting.tendsto_iterate_of_complexSpectralRadius_lt_one _
    (gaussSeidel_complexSpectralRadius_lt_one_of_col h hd) b x₀

end Irreducible

/-! ### Theorem 4.10: SOR for symmetric positive definite matrices -/

section SOR

open Filter Topology Stationary

open scoped SaadSparse

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}

/-- **Theorem 4.10** of [saad2003iterative], spectral form. Let $A \in \mathbb{R}^{n \times n}$ be
symmetric with positive diagonal entries, and let $0 < \omega < 2$. Then the SOR iteration
matrix $G_\omega$ satisfies $\rho(G_\omega) < 1$ if and only if $A$ is positive definite.

The iteration matrix is the iteration operator of `Matrix.sorSplitting`. The positive diagonal
is stated twice in Lean, as $a_{ii} > 0$ and as the nonsingularity of $D$.

**Reading.** The source states convergence. Lean states the equivalent spectral criterion for
convergence for every right-hand side and starting vector.
-/
theorem theorem_4_10 (hA : A.IsSymm) (hd : ∀ i, 0 < A i i) (h : IsUnit (diagPart A)) {ω : ℝ}
    (hω0 : 0 < ω) (hω2 : ω < 2) :
    complexSpectralRadius (A.sorSplitting h hω0.ne').iterationOperator < 1 ↔ A.PosDef :=
  Matrix.sorSplitting_complexSpectralRadius_lt_one_iff_posDef
    (Matrix.isHermitian_iff_isSymm.2 hA) hd h hω0 hω2

/-- **Theorem 4.10** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric with
positive diagonal entries, and let $0 < \omega < 2$. Then SOR converges for every right-hand
side $b$ and every starting vector $x_0$ if and only if $A$ is positive definite.

**Reading.** The book quantifies explicitly over $x_0$. The declaration also quantifies over $b$,
as in the stationary convergence criterion of Theorem 4.1. For the $2 \times 2$ all-ones matrix,
$b = 0$ and $\omega = 1$, one SOR step sends $(x_1,x_2)$ to $(-x_2,x_2)$ and the iterates stay
there, even though the matrix is singular.

The proof combines `SaadSparse.Chapter04.theorem_4_10` with Theorem 4.1. -/
theorem theorem_4_10_tendsto (hA : A.IsSymm) (hd : ∀ i, 0 < A i i) (h : IsUnit (diagPart A))
    {ω : ℝ} (hω0 : 0 < ω) (hω2 : ω < 2) :
    (∀ b x₀ : Fin n → ℝ, ∃ x, Tendsto (fun k => (sorStep A ω b)^[k] x₀) atTop (𝓝 x)) ↔
      A.PosDef := by
  rw [← theorem_4_10 hA hd h hω0 hω2]
  constructor
  · intro hconv
    refine theorem_4_1_mpr fun f x₀ => ?_
    obtain ⟨x, hx⟩ := hconv ((A.sorSplitting h hω0.ne').m *ᵥ f) x₀
    refine ⟨x, ?_⟩
    rw [sorStep_eq h hω0.ne', Splitting.step,
      nonsing_inv_mulVec_mulVec (A.sorSplitting h hω0.ne').isUnit f] at hx
    exact hx
  · intro hρ b x₀
    rw [sorStep_eq h hω0.ne']
    exact ⟨_, Stationary.Splitting.tendsto_iterate_of_complexSpectralRadius_lt_one _ hρ b x₀⟩

end SOR

/-! ### §4.2.5: Property A, consistent orderings and Young's theory -/

section Young

open Filter Topology Finset Stationary

open scoped SaadSparse ENNReal

variable {n : ℕ}

/-! ### Definition 4.11: Property A -/

/-- **Definition 4.11** of [saad2003iterative]. A matrix $A \in \mathbb{C}^{n \times n}$ has
**Property A** if there is a set $S \subseteq \{1, \dots, n\}$ such that every nonzero
off-diagonal entry $a_{ij}$ couples $S$ and its complement: $a_{ij} \neq 0$ and $i \neq j$ imply
that exactly one of $i$, $j$ is in $S$. -/
def HasPropertyA (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ S : Finset (Fin n), ∀ i j, A i j ≠ 0 → i ≠ j → (i ∈ S ↔ j ∉ S)

/-- **Equation (4.42)** of [saad2003iterative]. A matrix $A \in \mathbb{C}^{n \times n}$ has
Property A if and only if there is a set $S$ such that the symmetric permutation that lists $S$
before its complement brings $A$ to the form
$$\begin{bmatrix} D_1 & A_{12} \\ A_{21} & D_2 \end{bmatrix}$$
with diagonal matrices $D_1$ and $D_2$.

The permutation is `Equiv.sumCompl` for the predicate of membership in $S$. -/
theorem hasPropertyA_iff_toBlocks_isDiag (A : Matrix (Fin n) (Fin n) ℂ) :
    HasPropertyA A ↔ ∃ S : Finset (Fin n),
      Matrix.IsDiag (A.submatrix (Equiv.sumCompl (· ∈ S))
          (Equiv.sumCompl (· ∈ S))).toBlocks₁₁ ∧
        Matrix.IsDiag (A.submatrix (Equiv.sumCompl (· ∈ S))
          (Equiv.sumCompl (· ∈ S))).toBlocks₂₂ := by
  have hb₁ : ∀ (S : Finset (Fin n)) (i j : {x : Fin n // x ∈ S}),
      (A.submatrix (Equiv.sumCompl (· ∈ S)) (Equiv.sumCompl (· ∈ S))).toBlocks₁₁ i j =
        A (i : Fin n) (j : Fin n) := fun _ _ _ => rfl
  have hb₂ : ∀ (S : Finset (Fin n)) (i j : {x : Fin n // x ∉ S}),
      (A.submatrix (Equiv.sumCompl (· ∈ S)) (Equiv.sumCompl (· ∈ S))).toBlocks₂₂ i j =
        A (i : Fin n) (j : Fin n) := fun _ _ _ => rfl
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨S, fun i j hij => ?_, fun i j hij => ?_⟩
    · dsimp only
      rw [hb₁]
      by_contra hA
      exact ((hS _ _ hA fun h => hij (Subtype.ext h)).mp i.2) j.2
    · dsimp only
      rw [hb₂]
      by_contra hA
      exact i.2 ((hS _ _ hA fun h => hij (Subtype.ext h)).mpr j.2)
  · rintro ⟨S, h₁, h₂⟩
    refine ⟨S, fun i j hA hij => ?_⟩
    constructor
    · intro hi hj
      refine hA ?_
      rw [← hb₁ S ⟨i, hi⟩ ⟨j, hj⟩]
      exact h₁ fun h => hij (congrArg Subtype.val h)
    · intro hj
      by_contra hi
      refine hA ?_
      rw [← hb₂ S ⟨i, hi⟩ ⟨j, hj⟩]
      exact h₂ fun h => hij (congrArg Subtype.val h)

/-- Property A is invariant under symmetric permutations: for every permutation $\sigma$, the matrix
$P^TAP$ with entries $a_{\sigma(i)\sigma(j)}$ has Property A if and only if $A$ has it. It
supports §4.2.5 of [saad2003iterative]. -/
theorem hasPropertyA_reindex (A : Matrix (Fin n) (Fin n) ℂ) (σ : Equiv.Perm (Fin n)) :
    HasPropertyA (A.submatrix σ σ) ↔ HasPropertyA A := by
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨S.map σ.toEmbedding, fun a b hA hab => ?_⟩
    have h := hS (σ.symm a) (σ.symm b) (by simpa using hA)
      (fun h => hab (by simpa using congrArg σ h))
    simpa [Finset.mem_map_equiv] using h
  · rintro ⟨S, hS⟩
    refine ⟨S.map σ.symm.toEmbedding, fun i j hA hij => ?_⟩
    have h := hS (σ i) (σ j) hA fun h => hij (σ.injective h)
    simpa [Finset.mem_map_equiv] using h

/-! ### Definition 4.13: Consistent orderings and T-matrices -/

/-- **Definition 4.13** of [saad2003iterative]. A matrix $A \in \mathbb{C}^{n \times n}$ is
**consistently ordered** if there is a labelling $c : \{1, \dots, n\} \to \mathbb{N}$ of the
indices such that
$$a_{ij} \neq 0,\ j < i \implies c(j) = c(i) - 1, \qquad a_{ij} \neq 0,\ i < j \implies c(j) =
  c(i) + 1.$$
The sets $S_k = c^{-1}(k)$ are the partition of the book.

The first condition is written $c(i) = c(j) + 1$, so that no subtraction of natural numbers
occurs. -/
def IsConsistentlyOrdered (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ c : Fin n → ℕ, (∀ i j, j < i → A i j ≠ 0 → c i = c j + 1) ∧
    ∀ i j, i < j → A i j ≠ 0 → c j = c i + 1

/-- **Section 4.2.5** of [saad2003iterative], T-matrices. A matrix $A \in \mathbb{C}^{n \times n}$
is a **T-matrix** of the form in Example 4.2 if there is a nondecreasing labelling
$c : \{1, \dots, n\} \to \mathbb{N}$ such that every nonzero off-diagonal entry $a_{ij}$
joins two neighbouring blocks: $c(i) = c(j) + 1$ or $c(j) = c(i) + 1$. -/
def IsTMatrix (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ c : Fin n → ℕ, Monotone c ∧ ∀ i j, i ≠ j → A i j ≠ 0 → c i = c j + 1 ∨ c j = c i + 1

/-- **Section 4.2.5** of [saad2003iterative]. Every T-matrix is consistently ordered.

The block labelling of a T-matrix is a consistent ordering, because it is nondecreasing along
the order of the indices. -/
theorem isConsistentlyOrdered_of_isTMatrix {A : Matrix (Fin n) (Fin n) ℂ} (h : IsTMatrix A) :
    IsConsistentlyOrdered A := by
  obtain ⟨c, hmono, hstep⟩ := h
  refine ⟨c, fun i j hji hA => ?_, fun i j hij hA => ?_⟩
  · have hle : c j ≤ c i := hmono hji.le
    rcases hstep i j hji.ne' hA with h1 | h1
    · exact h1
    · omega
  · have hle : c i ≤ c j := hmono hij.le
    rcases hstep i j hij.ne hA with h1 | h1
    · omega
    · exact h1

/-- **Section 4.2.5** of [saad2003iterative]. Every consistently ordered matrix has Property A.

The set $S$ is the set of indices with even label $c$; a nonzero off-diagonal entry changes $c$
by one. -/
theorem hasPropertyA_of_isConsistentlyOrdered {A : Matrix (Fin n) (Fin n) ℂ}
    (h : IsConsistentlyOrdered A) : HasPropertyA A := by
  classical
  obtain ⟨c, hlow, hupp⟩ := h
  refine ⟨Finset.univ.filter fun i => Even (c i), fun i j hA hij => ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · rw [hupp i j hlt hA, Nat.even_add_one]
    tauto
  · rw [hlow i j hgt hA, Nat.even_add_one]

/-- **Section 4.2.5** of [saad2003iterative], the second item after Proposition 4.15, repeated as
Problem P-4.6. A matrix $A \in \mathbb{C}^{n \times n}$ has Property A if and only if some
symmetric permutation $P^TAP$ of $A$ is consistently ordered.

For the converse direction, the permuted matrix has Property A by
`SaadSparse.Chapter04.hasPropertyA_of_isConsistentlyOrdered`, and Property A is invariant under
symmetric permutations. For the forward direction, a stable sort of the labelling $c(i) = 0$ for
$i \in S$ and $c(i) = 1$ otherwise puts $S$ before its complement, and the sorted labelling is a
consistent ordering. -/
theorem hasPropertyA_iff_exists_isConsistentlyOrdered (A : Matrix (Fin n) (Fin n) ℂ) :
    HasPropertyA A ↔ ∃ σ : Equiv.Perm (Fin n), IsConsistentlyOrdered (A.submatrix σ σ) := by
  classical
  constructor
  · rintro ⟨S, hS⟩
    set c : Fin n → ℕ := fun i => if i ∈ S then 0 else 1 with hc
    set σ := Tuple.sort c with hσ
    have hmono : Monotone (c ∘ σ) := Tuple.monotone_sort c
    have key : ∀ i j : Fin n, i ≠ j → A (σ i) (σ j) ≠ 0 →
        ((c ∘ σ) i = 0 ∧ (c ∘ σ) j = 1) ∨ ((c ∘ σ) i = 1 ∧ (c ∘ σ) j = 0) := by
      intro i j hij hA
      have h := hS (σ i) (σ j) hA fun h => hij (σ.injective h)
      by_cases hi : σ i ∈ S
      · exact Or.inl ⟨by simp [hc, hi], by simp [hc, h.mp hi]⟩
      · exact Or.inr ⟨by simp [hc, hi], by simp [hc, not_not.mp fun hj => hi (h.mpr hj)]⟩
    refine ⟨σ, c ∘ σ, fun i j hji hA => ?_, fun i j hij hA => ?_⟩
    · have hle := hmono hji.le
      rcases key i j hji.ne' hA with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · have hle := hmono hij.le
      rcases key i j hij.ne hA with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · rintro ⟨σ, hσ⟩
    exact (hasPropertyA_reindex A σ).mp (hasPropertyA_of_isConsistentlyOrdered hσ)

/-- **Proposition 4.15** of [saad2003iterative], the backbone form. Let
$A \in \mathbb{C}^{n \times n}$ be consistently ordered with nonsingular diagonal $D$. Then $A$
has the spectral property `Matrix.IsConsistentlyOrdered` that Young's theory uses: the spectrum
of $\alpha L + \alpha^{-1}U$ does not depend on $\alpha \neq 0$, where $L = D^{-1}E$ and
$U = D^{-1}F$ are the strict parts of the Jacobi iteration matrix. -/
theorem IsConsistentlyOrdered.matrix_isConsistentlyOrdered {A : Matrix (Fin n) (Fin n) ℂ}
    (h : IsConsistentlyOrdered A) (hd : IsUnit (diagPart A)) : A.IsConsistentlyOrdered := by
  obtain ⟨c, hlow, hupp⟩ := h
  exact Matrix.isConsistentlyOrdered_of_labelling hd c hlow hupp

/-- **Proposition 4.15** of [saad2003iterative]. Let $A \in \mathbb{C}^{n \times n}$ be consistently
ordered with nonsingular diagonal $D$, and let $L = D^{-1}E$ and $U = D^{-1}F$, so that
$B = L + U$ is the Jacobi iteration matrix. Then for every $\alpha \in \mathbb{C}$ with
$\alpha \neq 0$,
$$\sigma(\alpha L + \alpha^{-1} U) = \sigma(B).$$

The matrices $L$ and $U$ are `Matrix.jacobiLower A` and `Matrix.jacobiUpper A`, and $B$ is the
iteration operator of `Matrix.jacobiSplitting`. -/
theorem proposition_4_15 {A : Matrix (Fin n) (Fin n) ℂ} (h : IsConsistentlyOrdered A)
    (hd : IsUnit (diagPart A)) {α : ℂ} (hα : α ≠ 0) :
    spectrum ℂ (α • Matrix.jacobiLower A + α⁻¹ • Matrix.jacobiUpper A) =
      spectrum ℂ (Matrix.jacobiSplitting A hd).iterationOperator := by
  have hCO := IsConsistentlyOrdered.matrix_isConsistentlyOrdered h hd
  rw [← Matrix.jacobiLower_add_jacobiUpper A hd]
  exact hCO α hα

/-- **Proposition 4.14** of [saad2003iterative]. Let $A \in \mathbb{C}^{n \times n}$ be consistently
ordered. Then there is a permutation $\sigma$ such that $P^TAP$, the matrix with entries
$a_{\sigma(i)\sigma(j)}$, is a T-matrix, and the permutation commutes with taking the strict
triangular parts:
$$(P^TAP)_L = P^T A_L P, \qquad (P^TAP)_U = P^T A_U P.$$

The permutation is the stable sort `Tuple.sort` of the indices by their label. The two
identities hold because an entry that the sort moves across the diagonal would join two blocks
in the wrong order, which the monotonicity of the sorted labelling forbids. -/
theorem proposition_4_14 {A : Matrix (Fin n) (Fin n) ℂ} (h : IsConsistentlyOrdered A) :
    ∃ σ : Equiv.Perm (Fin n), IsTMatrix (A.submatrix σ σ) ∧
      strictLower (A.submatrix σ σ) = (strictLower A).submatrix σ σ ∧
        strictUpper (A.submatrix σ σ) = (strictUpper A).submatrix σ σ := by
  obtain ⟨c, hlow, hupp⟩ := h
  refine ⟨Tuple.sort c, ⟨c ∘ Tuple.sort c, Tuple.monotone_sort c, fun i j hij hA => ?_⟩, ?_, ?_⟩
  · have hne : Tuple.sort c i ≠ Tuple.sort c j := fun hc => hij ((Tuple.sort c).injective hc)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inr (hupp _ _ hlt hA)
    · exact Or.inl (hlow _ _ hgt hA)
  · ext i j
    have hmono := Tuple.monotone_sort c
    rcases lt_trichotomy j i with hji | rfl | hij
    · by_cases hσ : Tuple.sort c j < Tuple.sort c i
      · simp [hji, hσ]
      · have hne : Tuple.sort c i ≠ Tuple.sort c j :=
          fun hc => absurd ((Tuple.sort c).injective hc) hji.ne'
        have hlt : Tuple.sort c i < Tuple.sort c j := lt_of_le_of_ne (not_lt.mp hσ) hne
        have hz : A (Tuple.sort c i) (Tuple.sort c j) = 0 := by
          by_contra hA
          have h1 := hupp _ _ hlt hA
          have h2 : (c ∘ Tuple.sort c) j ≤ (c ∘ Tuple.sort c) i := hmono hji.le
          simp only [Function.comp_apply] at h2
          omega
        simp [hji, hσ, hz]
    · simp
    · by_cases hσ : Tuple.sort c j < Tuple.sort c i
      · have hz : A (Tuple.sort c i) (Tuple.sort c j) = 0 := by
          by_contra hA
          have h1 := hlow _ _ hσ hA
          have h2 : (c ∘ Tuple.sort c) i ≤ (c ∘ Tuple.sort c) j := hmono hij.le
          simp only [Function.comp_apply] at h2
          omega
        simp [asymm hij, hσ, hz]
      · simp [asymm hij, hσ]
  · ext i j
    have hmono := Tuple.monotone_sort c
    rcases lt_trichotomy i j with hij | rfl | hji
    · by_cases hσ : Tuple.sort c i < Tuple.sort c j
      · simp [hij, hσ]
      · have hne : Tuple.sort c j ≠ Tuple.sort c i :=
          fun hc => absurd ((Tuple.sort c).injective hc) hij.ne'
        have hlt : Tuple.sort c j < Tuple.sort c i := lt_of_le_of_ne (not_lt.mp hσ) hne
        have hz : A (Tuple.sort c i) (Tuple.sort c j) = 0 := by
          by_contra hA
          have h1 := hlow _ _ hlt hA
          have h2 : (c ∘ Tuple.sort c) i ≤ (c ∘ Tuple.sort c) j := hmono hij.le
          simp only [Function.comp_apply] at h2
          omega
        simp [hij, hσ, hz]
    · simp
    · by_cases hσ : Tuple.sort c i < Tuple.sort c j
      · have hz : A (Tuple.sort c i) (Tuple.sort c j) = 0 := by
          by_contra hA
          have h1 := hupp _ _ hσ hA
          have h2 : (c ∘ Tuple.sort c) j ≤ (c ∘ Tuple.sort c) i := hmono hji.le
          simp only [Function.comp_apply] at h2
          omega
        simp [asymm hji, hσ, hz]
      · simp [asymm hji, hσ]

/-! ### Theorem 4.16 and the optimal relaxation parameter (4.47) -/

variable {A : Matrix (Fin n) (Fin n) ℂ}

/-- **Theorem 4.16** of [saad2003iterative], first direction. Let $A \in \mathbb{C}^{n \times n}$ be
consistently ordered with nonsingular diagonal, and let $\omega \neq 0$. Let $\lambda \neq 0$
and $\mu$ satisfy
$$(\lambda + \omega - 1)^2 = \lambda \omega^2 \mu^2.$$
If $\lambda$ is an eigenvalue of the SOR iteration matrix, then $\mu$ is an eigenvalue of the
Jacobi iteration matrix $B$.

**Reading.** The book writes $M_{SOR}$ for the SOR iteration matrix, while (4.26) uses that name
for the SOR preconditioner. Here the iteration matrix is the iteration operator of
`Matrix.sorSplitting`, and the preconditioner is `SaadSparse.Chapter04.M_sor`. -/
theorem theorem_4_16_mp (h : IsConsistentlyOrdered A) (hd : IsUnit (diagPart A)) {ω : ℂ}
    (hω : ω ≠ 0) {l μ : ℂ} (hl : l ≠ 0) (hrel : (l + ω - 1) ^ 2 = l * ω ^ 2 * μ ^ 2)
    (hlG : l ∈ spectrum ℂ (Matrix.sorSplitting A hd hω).iterationOperator) :
    μ ∈ spectrum ℂ (Matrix.jacobiSplitting A hd).iterationOperator :=
  ((IsConsistentlyOrdered.matrix_isConsistentlyOrdered h hd).mem_spectrum_jacobi_iff_sor hd hω hl
    hrel).mpr hlG

/-- **Theorem 4.16** of [saad2003iterative], second direction. Let $A \in \mathbb{C}^{n \times n}$
be consistently ordered with nonsingular diagonal, and let $\omega \neq 0$. Let $\lambda \neq 0$
and $\mu$ satisfy $(\lambda + \omega - 1)^2 = \lambda \omega^2 \mu^2$. If $\mu$ is an eigenvalue
of the Jacobi iteration matrix $B$, then $\lambda$ is an eigenvalue of the SOR iteration matrix.

The iteration matrices are the iteration operators of `Matrix.jacobiSplitting` and
`Matrix.sorSplitting`.

**Reading.** Lean requires $\lambda \ne 0$ in this direction as well, while the printed converse
allows any root of (4.46). A zero root forces $\omega=1$. On a nonempty matrix that Gauss–Seidel
iteration matrix is singular because its strict upper factor is singular.
-/
theorem theorem_4_16_mpr (h : IsConsistentlyOrdered A) (hd : IsUnit (diagPart A)) {ω : ℂ}
    (hω : ω ≠ 0) {l μ : ℂ} (hl : l ≠ 0) (hrel : (l + ω - 1) ^ 2 = l * ω ^ 2 * μ ^ 2)
    (hμB : μ ∈ spectrum ℂ (Matrix.jacobiSplitting A hd).iterationOperator) :
    l ∈ spectrum ℂ (Matrix.sorSplitting A hd hω).iterationOperator :=
  ((IsConsistentlyOrdered.matrix_isConsistentlyOrdered h hd).mem_spectrum_jacobi_iff_sor hd hω hl
    hrel).mp hμB

/-- **Equation (4.47)** of [saad2003iterative]. Let $A \in \mathbb{C}^{n \times n}$, $n \ge 1$, be
consistently ordered with nonsingular diagonal, and let the Jacobi iteration matrix $B$ have
real eigenvalues and $\rho(B) < 1$. Then over $0 < \omega < 2$ the spectral radius of the SOR
iteration matrix is smallest at
$$\omega_{opt} = \frac{2}{1 + \sqrt{1 - \rho(B)^2}},$$
and its value there is $\omega_{opt} - 1$.

The SOR iteration matrix for a real $\omega$ is `Matrix.sorIterationMatrix A ω`, and the
spectral radii are values of `spectralRadius ℂ` in $[0, \infty]$.

**Reading.** The source gives the formula without listing these hypotheses at (4.47). Lean makes
explicit that the Jacobi spectrum is real, $\rho(B)<1$, and the matrix is nonempty. The theorem also
gives the attained spectral radius.
-/
theorem equation_4_47 [NeZero n] (h : IsConsistentlyOrdered A) (hd : IsUnit (diagPart A))
    (hreal : ∀ μ ∈ spectrum ℂ (Matrix.jacobiSplitting A hd).iterationOperator, μ.im = 0)
    (hlt : spectralRadius ℂ (Matrix.jacobiSplitting A hd).iterationOperator < 1) :
    IsMinOn (fun ω : ℝ => spectralRadius ℂ (Matrix.sorIterationMatrix A (ω : ℂ)))
        (Set.Ioo 0 2)
        (2 / (1 + Real.sqrt (1 -
          (spectralRadius ℂ (Matrix.jacobiSplitting A hd).iterationOperator).toReal ^ 2))) ∧
      spectralRadius ℂ (Matrix.sorIterationMatrix A
          ((2 / (1 + Real.sqrt (1 -
            (spectralRadius ℂ (Matrix.jacobiSplitting A hd).iterationOperator).toReal ^ 2))
            : ℝ) : ℂ)) =
        ENNReal.ofReal (2 / (1 + Real.sqrt (1 -
          (spectralRadius ℂ (Matrix.jacobiSplitting A hd).iterationOperator).toReal ^ 2)) - 1) := by
  have hCO := IsConsistentlyOrdered.matrix_isConsistentlyOrdered h hd
  exact ⟨hCO.isMinOn_complexSpectralRadius_sor hd hreal hlt,
    hCO.spectralRadius_sor_optimalRelaxation hd hreal hlt⟩

end Young

end SaadSparse.Chapter04
