/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Matrix.SpectralNorm
import Numlib.Analysis.Normed.Ring.CondNumber
import Numlib.Krylov.Subspace
import Numlib.Projection.OneDimensional
import Numlib.Stationary.SPD

/-!
# Richardson's iteration

**Richardson's iteration** with a preconditioner $P$ for the system $A x = b$ is
$$x_{k+1} = x_k + \alpha_k P^{-1} (b - A x_k).$$
It is stationary when $\alpha_k = \alpha$ is fixed and nonstationary otherwise. The presentation
follows [quarteroni2000numerical], §4.3.1, (4.23)–(4.30). The case $P = I$ is Example 4.1 of
[saad2003iterative], and the unpreconditioned case is also in [kress1998numerical], §4.4, and
[han2009theoretical], Exercise 5.2.3.

The stationary method is the splitting with $m = \alpha^{-1} P$, and its iteration matrix is
$R_\alpha = I - \alpha P^{-1} A$. For a real matrix $M$, standing for $P^{-1} A$, the iteration
converges if and only if $2 \operatorname{Re} \lambda / (\alpha |\lambda|^2) > 1$ for every complex
eigenvalue $\lambda$ of $M$. For positive definite $P$ and $A$, the error contracts in the energy
norm of $A$ by the factor $\rho(R_\alpha)$. For a symmetric positive definite $M$, the optimal
spectral radius is $(\kappa_2(M) - 1)/(\kappa_2(M) + 1)$. The nonstationary iteration is defined on
any vector space; its residuals are $r_k = p_k(A) r_0$ for a polynomial $p_k$ of degree at most $k$
with $p_k(0) = 1$, its iterates lie in $x_0 + \mathcal{K}_k(A, r_0)$, and the gradient method is its
instance with $\alpha_k = \langle r_k, r_k \rangle / \langle r_k, A r_k \rangle$.

## Main definitions

* `Stationary.Splitting.preconditionedRichardson`: the splitting $m = \alpha^{-1} P$.
* `Richardson.iterate`: the nonstationary preconditioned Richardson iteration.
* `Richardson.residualPoly`: the residual polynomial $p_k = \prod_{j < k} (1 - \alpha_j X)$.

## Main results

* `Stationary.Splitting.preconditionedRichardson_iterationOperator`: the iteration matrix is
  $I - \alpha P^{-1} A$.
* `Stationary.Splitting.complexSpectralRadius_one_sub_smul_lt_one_iff_forall`: Theorem 4.8 of
  [quarteroni2000numerical], $\rho(I - \alpha M) < 1$ if and only if $2 \operatorname{Re} \lambda /
  (\alpha |\lambda|^2) > 1$ for every eigenvalue $\lambda$ of $M$.
* `Stationary.Splitting.energyNorm_preconditionedRichardson_mulVec_le`: Corollary 4.1 of
  [quarteroni2000numerical], $\|R_\alpha e\|_A \le \rho(R_\alpha) \|e\|_A$ for positive definite $P$
  and $A$.
* `Stationary.Splitting.complexSpectralRadius_one_sub_smul_optimal_eq_condNumber`: (4.29) of
  [quarteroni2000numerical], the optimal spectral radius is $(\kappa_2(M) - 1)/(\kappa_2(M) + 1)$.
* `Stationary.Splitting.two_div_add_eq_mul_norm_inv_div_condNumber`: (4.29) of
  [quarteroni2000numerical], the optimal parameter is $2 \|M^{-1}\|_2 / (\kappa_2(M) + 1)$.
* `Richardson.residual_iterate_succ`: the residual update (4.25).
* `Richardson.residual_iterate_eq_prod`: the residuals are $r_k = p_k(A) r_0$, which is (4.51).
* `Richardson.iterate_sub_mem_subspace`: the iterates lie in $x_0 + \mathcal{K}_k(A, r_0)$, which is
  (4.53).
* `Richardson.iterate_gradient_eq_steepestDescentStep`: the gradient method of §4.3.3 is the
  nonstationary iteration with $\alpha_k = \langle r_k, r_k \rangle / \langle r_k, A r_k \rangle$.

## Implementation notes

* The splitting `Stationary.Splitting.preconditionedRichardson` specializes to
  `Stationary.Splitting.richardson` at $P = I$ and to `Matrix.jorSplitting` at $P = D$, the diagonal
  part of $A$.
* Theorem 4.9 of [quarteroni2000numerical] is in `Numlib.Stationary.SPD`: for a real positive
  spectrum in $[\lambda_{\min}, \lambda_{\max}]$, convergence holds if and only if
  $0 < \alpha < 2/\lambda_{\max}$
  (`Stationary.Splitting.complexSpectralRadius_one_sub_smul_lt_one_iff`), and the optimal parameter
  is $2/(\lambda_{\min} + \lambda_{\max})$
  (`Stationary.Splitting.isMinOn_complexSpectralRadius_one_sub_smul`).
* The spectral results are stated for a real matrix $M$, which stands for $P^{-1} A$, and the
  spectral radius is `Matrix.complexSpectralRadius`.
* The nonstationary iteration takes the inverse of the preconditioner as a linear map `Pinv`, so no
  invertibility hypothesis is needed. The step of the gradient method is
  `Projection.steepestDescentStep`.
-/

open Filter Topology
open scoped ENNReal NNReal ComplexOrder

namespace Stationary

namespace Splitting

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*} [Field 𝕜]

/-- The **preconditioned Richardson splitting** of a square matrix $A$ over a field, for an
invertible preconditioner $P$ and a parameter $\alpha \neq 0$: the splitting $A = m - n$ with
$$m = \alpha^{-1} P, \qquad n = \alpha^{-1} P - A.$$
This is (4.23) of [quarteroni2000numerical]. -/
noncomputable def preconditionedRichardson (A : Matrix n n 𝕜) {P : Matrix n n 𝕜} (hP : IsUnit P)
    {α : 𝕜} (hα : α ≠ 0) : Splitting A :=
  ⟨α⁻¹ • P, by
    rw [Algebra.smul_def]
    exact ((isUnit_iff_ne_zero.mpr (inv_ne_zero hα)).map (algebraMap 𝕜 (Matrix n n 𝕜))).mul hP⟩

/-- The part $m$ of the preconditioned Richardson splitting is $\alpha^{-1} P$. -/
@[simp]
theorem preconditionedRichardson_m (A : Matrix n n 𝕜) {P : Matrix n n 𝕜} (hP : IsUnit P) {α : 𝕜}
    (hα : α ≠ 0) : (preconditionedRichardson A hP hα).m = α⁻¹ • P := rfl

/-- **The Richardson iteration matrix.** The iteration matrix of the preconditioned Richardson
splitting of $A$, with an invertible preconditioner $P$ and $\alpha \neq 0$, is
$$R_\alpha = I - \alpha P^{-1} A.$$

This is the matrix of [quarteroni2000numerical], §4.3. At $\alpha = 1$ it is
$R_P = I - P^{-1} A$. -/
theorem preconditionedRichardson_iterationOperator (A : Matrix n n 𝕜) {P : Matrix n n 𝕜}
    (hP : IsUnit P) {α : 𝕜} (hα : α ≠ 0) :
    (preconditionedRichardson A hP hα).iterationOperator = 1 - α • (P⁻¹ * A) := by
  rw [Splitting.iterationOperator, preconditionedRichardson_m,
    Matrix.ringInverse_smul (inv_ne_zero hα) hP, inv_inv, smul_mul_assoc,
    nonsing_inv_eq_ringInverse]

/-- The preconditioned Richardson splitting with $P = I$ is the unpreconditioned Richardson
splitting `Stationary.Splitting.richardson`, for every $\alpha \neq 0$. -/
theorem preconditionedRichardson_one (A : Matrix n n 𝕜) {α : 𝕜} (hα : α ≠ 0) :
    preconditionedRichardson A isUnit_one hα = richardson A hα := rfl

/-- JOR is Richardson with $P = D$ and $\alpha = \omega$. For a square matrix $A$ with invertible
diagonal part $D$ and $\omega \neq 0$, the preconditioned Richardson splitting with
preconditioner $D$ and parameter $\omega$ is the JOR splitting `Matrix.jorSplitting`
([quarteroni2000numerical], the sentence after (4.24)). -/
theorem preconditionedRichardson_diagPart (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) {ω : 𝕜}
    (hω : ω ≠ 0) : preconditionedRichardson A h hω = jorSplitting A h hω := rfl

/-- For real $\alpha \neq 0$, $r$ and $i$, $(1 - \alpha r)^2 + (\alpha i)^2 < 1$ if and only if
$1 < 2 r / (\alpha (r^2 + i^2))$, where the right side is false at $r = i = 0$ because division
by zero gives $0$. -/
private theorem sq_lt_one_iff_one_lt_div {α r i : ℝ} (hα : α ≠ 0) :
    (1 - α * r) ^ 2 + (α * i) ^ 2 < 1 ↔ 1 < 2 * r / (α * (r ^ 2 + i ^ 2)) := by
  rcases eq_or_ne (r ^ 2 + i ^ 2) 0 with h0 | h0
  · have hr : r = 0 := by nlinarith [sq_nonneg r, sq_nonneg i]
    have hi : i = 0 := by nlinarith [sq_nonneg r, sq_nonneg i]
    subst hr hi
    simp
  · have hpos : 0 < r ^ 2 + i ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
    rcases lt_or_gt_of_ne hα with hneg | hposα
    · rw [one_lt_div_of_neg (mul_neg_of_neg_of_pos hneg hpos)]
      constructor
      · intro h
        nlinarith [mul_pos (neg_pos.mpr hneg) hpos]
      · intro h
        nlinarith [mul_pos (neg_pos.mpr hneg) hpos]
    · rw [one_lt_div (mul_pos hposα hpos)]
      constructor
      · intro h
        nlinarith [mul_pos hposα hpos]
      · intro h
        nlinarith [mul_pos hposα hpos]

/-- **Theorem 4.8** of [quarteroni2000numerical]. Let $M$ be a real $n \times n$ matrix with
$n \ge 1$, and let $\alpha$ be real. Then the stationary Richardson iteration with iteration
matrix $I - \alpha M$ converges, that is $\rho(I - \alpha M) < 1$, if and only if
$$\frac{2 \operatorname{Re} \lambda}{\alpha |\lambda|^2} > 1$$
for every complex eigenvalue $\lambda$ of $M$.

With $M = P^{-1} A$ and `Stationary.Splitting.preconditionedRichardson_iterationOperator`, this
is the statement of the source for any nonsingular $P$. In Lean, division by zero gives $0$, so
the condition on the right is false at $\alpha = 0$ and at $\lambda = 0$; in both cases the left
side is also false. The spectral radius is `Matrix.complexSpectralRadius`, and the eigenvalues
are the spectrum of the complexification of $M$. -/
theorem complexSpectralRadius_one_sub_smul_lt_one_iff_forall [Nonempty n] (M : Matrix n n ℝ)
    (α : ℝ) :
    complexSpectralRadius (1 - α • M) < 1 ↔
      ∀ μ ∈ spectrum ℂ (Matrix.complexify M), 1 < 2 * μ.re / (α * ‖μ‖ ^ 2) := by
  obtain ⟨μ₀, v, hv, hμ₀v, -⟩ := exists_eigenvector_norm_eq_complexSpectralRadius M
  have hμ₀ : μ₀ ∈ spectrum ℂ (Matrix.complexify M) :=
    (mem_spectrum_iff_exists_mulVec_eq_smul _ _).mpr ⟨v, hv, hμ₀v⟩
  rw [complexSpectralRadius_lt_one_iff_forall_norm_lt]
  rcases eq_or_ne α 0 with rfl | hα
  · simp only [zero_smul, sub_zero, zero_mul, div_zero]
    constructor
    · intro h
      exfalso
      have h1 : ((1 : ℝ) : ℂ) ∈ spectrum ℂ (Matrix.complexify (1 : Matrix n n ℝ)) := by
        have : Nontrivial (Matrix n n ℂ) := by
          by_contra hcon
          rw [not_nontrivial_iff_subsingleton] at hcon
          exact spectrum.mem_iff.mp hμ₀ (isUnit_of_subsingleton _)
        rw [Matrix.complexify_one, Complex.ofReal_one, spectrum.mem_iff, map_one, sub_self]
        exact not_isUnit_zero
      have := h _ h1
      simp at this
    · intro h
      exact absurd (h μ₀ hμ₀) (by norm_num)
  · have hspec : spectrum ℂ (Matrix.complexify (1 - α • M)) =
        (fun μ : ℂ => ((1 : ℝ) : ℂ) + ((-α : ℝ) : ℂ) * μ) '' spectrum ℂ (Matrix.complexify M) := by
      rw [← spectrum_complexify_affine M (neg_ne_zero.mpr hα)]
      congr 2
      module
    rw [hspec, Set.forall_mem_image]
    refine forall₂_congr fun μ _ => ?_
    have hnorm : ‖((1 : ℝ) : ℂ) + ((-α : ℝ) : ℂ) * μ‖ ^ 2
        = (1 - α * μ.re) ^ 2 + (α * μ.im) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul,
        sub_zero, Complex.add_im, Complex.mul_im, zero_add]
      ring
    rw [← pow_lt_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, hnorm, Complex.sq_norm,
      Complex.normSq_apply, ← sq, ← sq]
    exact sq_lt_one_iff_one_lt_div hα

/-- **Corollary 4.1** of [quarteroni2000numerical], in the generality of its closing remark. Let $A$
and $P$ be real symmetric positive definite matrices, and let $\alpha \neq 0$ be real. Let
$R_\alpha = I - \alpha P^{-1} A$ be the iteration matrix of the preconditioned Richardson
iteration. Then for every vector $e$,
$$\|R_\alpha e\|_A^2 \le \rho(R_\alpha)^2 \, \|e\|_A^2,$$
where $\|e\|_A^2 = (A e) \cdot e$. No hypothesis on $P^{-1} A$ is needed.

The convergence clause of the corollary needs in addition $0 < \alpha < 2/\lambda_{\max}$
(`Stationary.Splitting.complexSpectralRadius_one_sub_smul_lt_one_iff`), which the source omits.
The spectral radius is the real number `(Matrix.complexSpectralRadius _).toReal`. -/
theorem energyNorm_preconditionedRichardson_mulVec_le {A P : Matrix n n ℝ} (hA : A.PosDef)
    (hP : P.PosDef) {α : ℝ} (hα : α ≠ 0) (e : n → ℝ) :
    (A *ᵥ ((1 - α • (P⁻¹ * A)) *ᵥ e)) ⬝ᵥ ((1 - α • (P⁻¹ * A)) *ᵥ e) ≤
      (complexSpectralRadius (1 - α • (P⁻¹ * A))).toReal ^ 2 * ((A *ᵥ e) ⬝ᵥ e) := by
  have hM : (preconditionedRichardson A hP.isUnit hα).m.IsHermitian := by
    rw [preconditionedRichardson_m, IsHermitian, conjTranspose_smul, hP.1.eq]
    simp
  have h := energyNorm_mulVec_iterationOperator_le_complexSpectralRadius
    (preconditionedRichardson A hP.isUnit hα) hA hM e
  rwa [preconditionedRichardson_iterationOperator] at h

section CondNumber

open scoped Matrix.Norms.L2Operator NormedRing

/-- For a real symmetric matrix $M$ with eigenvalues in $[\lambda_{\min}, \lambda_{\max}]$,
$0 < \lambda_{\min}$ and $\lambda_{\max}$ an eigenvalue, the $\ell^2$ operator norm of $M$ is
$\lambda_{\max}$. -/
private theorem l2_opNorm_eq_of_spectrum {M : Matrix n n ℝ} (hM : M.IsHermitian) {lmin lmax : ℝ}
    (hsub : spectrum ℝ M ⊆ Set.Icc lmin lmax) (hmax : lmax ∈ spectrum ℝ M) (hpos : 0 < lmin) :
    ‖M‖ = lmax := by
  refine hM.l2_opNorm_eq (fun μ hμ => ?_) ⟨lmax, ?_, ?_⟩
  · rw [hasEigenvalue_toEuclideanLin_iff] at hμ
    have := hsub hμ
    rw [RCLike.re_to_real, abs_of_pos (by linarith [this.1])]
    exact this.2
  · exact (hasEigenvalue_toEuclideanLin_iff M lmax).mpr hmax
  · rw [RCLike.re_to_real, abs_of_pos (by linarith [(hsub hmax).1])]

/-- For a real symmetric matrix $M$ with eigenvalues in $[\lambda_{\min}, \lambda_{\max}]$ and
$0 < \lambda_{\min}$ an eigenvalue, the $\ell^2$ operator norm of $M^{-1}$ is
$\lambda_{\min}^{-1}$. -/
private theorem l2_opNorm_inv_eq_of_spectrum {M : Matrix n n ℝ} (hM : M.IsHermitian)
    {lmin lmax : ℝ} (hsub : spectrum ℝ M ⊆ Set.Icc lmin lmax) (hmin : lmin ∈ spectrum ℝ M)
    (hpos : 0 < lmin) : ‖M⁻¹‖ = lmin⁻¹ := by
  refine hM.l2_opNorm_inv_eq hpos (fun μ hμ => ?_) ⟨lmin, ?_, ?_⟩
  · rw [hasEigenvalue_toEuclideanLin_iff] at hμ
    have := hsub hμ
    rw [RCLike.re_to_real, abs_of_pos (by linarith [this.1])]
    exact this.1
  · exact (hasEigenvalue_toEuclideanLin_iff M lmin).mpr hmin
  · rw [RCLike.re_to_real, abs_of_pos hpos]

/-- Let $M$ be a real symmetric matrix whose eigenvalues lie in $[\lambda_{\min}, \lambda_{\max}]$,
where $\lambda_{\min}$ and $\lambda_{\max}$ are eigenvalues and $0 < \lambda_{\min}$. Then the
$\ell^2$ condition number of $M$ is
$$\kappa_2(M) = \frac{\lambda_{\max}}{\lambda_{\min}}.$$

The condition number is `NormedRing.condNumber` for the $\ell^2$ operator norm of
`Matrix.Norms.L2Operator`. -/
theorem condNumber_eq_div_of_spectrum {M : Matrix n n ℝ} (hM : M.IsHermitian) {lmin lmax : ℝ}
    (hsub : spectrum ℝ M ⊆ Set.Icc lmin lmax) (hmin : lmin ∈ spectrum ℝ M)
    (hmax : lmax ∈ spectrum ℝ M) (hpos : 0 < lmin) : κ M = lmax / lmin := by
  rw [NormedRing.condNumber, ← nonsing_inv_eq_ringInverse,
    l2_opNorm_eq_of_spectrum hM hsub hmax hpos, l2_opNorm_inv_eq_of_spectrum hM hsub hmin hpos,
    div_eq_mul_inv]

/-- **Equation (4.29)** of [quarteroni2000numerical], the optimal spectral radius. Let $M$ be a real
symmetric matrix whose eigenvalues lie in $[\lambda_{\min}, \lambda_{\max}]$, where
$\lambda_{\min}$ and $\lambda_{\max}$ are eigenvalues and $0 < \lambda_{\min}$. Then
$$\rho\Bigl(I - \frac{2}{\lambda_{\min} + \lambda_{\max}} M\Bigr) = \frac{\kappa_2(M) -
  1}{\kappa_2(M) + 1},$$
where $\kappa_2(M)$ is the $\ell^2$ condition number of $M$.

In the source, $M$ is $P^{-1} A$ when this matrix is symmetric. The spectral radius is
`Matrix.complexSpectralRadius`, and the condition number is `NormedRing.condNumber` for the
$\ell^2$ operator norm. -/
theorem complexSpectralRadius_one_sub_smul_optimal_eq_condNumber {M : Matrix n n ℝ}
    (hM : M.IsHermitian) {lmin lmax : ℝ} (hsub : spectrum ℝ M ⊆ Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ M) (hmax : lmax ∈ spectrum ℝ M) (hpos : 0 < lmin) :
    complexSpectralRadius (1 - (2 / (lmin + lmax)) • M)
      = ENNReal.ofReal ((κ M - 1) / (κ M + 1)) := by
  rw [complexSpectralRadius_one_sub_smul_optimal_eq (hM.spectrum_complexify_subset hsub) hmin hmax
    hpos, condNumber_eq_div_of_spectrum hM hsub hmin hmax hpos]
  congr 1
  field_simp

/-- **Equation (4.29)** of [quarteroni2000numerical], the optimal parameter. Let $M$ be a real
symmetric matrix whose eigenvalues lie in $[\lambda_{\min}, \lambda_{\max}]$, where
$\lambda_{\min}$ and $\lambda_{\max}$ are eigenvalues and $0 < \lambda_{\min}$. Then
$$\frac{2}{\lambda_{\min} + \lambda_{\max}} = \frac{2 \|M^{-1}\|_2}{\kappa_2(M) + 1}.$$

The source writes $\|A^{-1} P\|_2$ for $\|(P^{-1} A)^{-1}\|_2$. The norm is the $\ell^2$
operator norm, and the condition number is `NormedRing.condNumber` for this norm. -/
theorem two_div_add_eq_mul_norm_inv_div_condNumber {M : Matrix n n ℝ} (hM : M.IsHermitian)
    {lmin lmax : ℝ} (hsub : spectrum ℝ M ⊆ Set.Icc lmin lmax) (hmin : lmin ∈ spectrum ℝ M)
    (hmax : lmax ∈ spectrum ℝ M) (hpos : 0 < lmin) :
    2 / (lmin + lmax) = 2 * ‖M⁻¹‖ / (κ M + 1) := by
  rw [condNumber_eq_div_of_spectrum hM hsub hmin hmax hpos,
    l2_opNorm_inv_eq_of_spectrum hM hsub hmin hpos]
  field_simp
  ring

end CondNumber

end Splitting

end Stationary

/-! ### The nonstationary iteration -/

namespace Richardson

open Polynomial

section Module

variable {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- **The nonstationary preconditioned Richardson iteration** ([quarteroni2000numerical], (4.24)).
Let $E$ be a vector space over a field $\mathbb{K}$, let $A$ and $P^{-1}$ be linear maps on $E$,
let $(\alpha_k)$ be a sequence of scalars, and let $b, x_0 \in E$. The iterates are defined by
$$x_{k+1} = x_k + \alpha_k P^{-1} (b - A x_k).$$

The linear map $P^{-1}$ is the argument `Pinv`; it need not be the inverse of anything. The
choice `Pinv = LinearMap.id` gives the unpreconditioned method. The stationary case, with
constant $\alpha_k$, is `Stationary.step` for the operator $1 - \alpha P^{-1} A$. -/
noncomputable def iterate (A Pinv : E →ₗ[𝕜] E) (α : ℕ → 𝕜) (b x₀ : E) : ℕ → E
  | 0 => x₀
  | k + 1 => iterate A Pinv α b x₀ k + α k • Pinv (b - A (iterate A Pinv α b x₀ k))

variable (A Pinv : E →ₗ[𝕜] E) (α : ℕ → 𝕜) (b x₀ : E)

/-- The nonstationary Richardson iteration starts at $x_0$. -/
@[simp]
theorem iterate_zero : iterate A Pinv α b x₀ 0 = x₀ := rfl

/-- One step of the nonstationary Richardson iteration: $x_{k+1} = x_k + \alpha_k z_k$, where
$z_k = P^{-1} (b - A x_k)$ is the preconditioned residual. -/
theorem iterate_succ (k : ℕ) :
    iterate A Pinv α b x₀ (k + 1)
      = iterate A Pinv α b x₀ k + α k • Pinv (b - A (iterate A Pinv α b x₀ k)) := rfl

/-- **The residual update** ([quarteroni2000numerical], (4.25)). For the nonstationary Richardson
iteration, the residuals $r_k = b - A x_k$ satisfy
$$r_{k+1} = r_k - \alpha_k A z_k, \qquad z_k = P^{-1} r_k.$$
-/
theorem residual_iterate_succ (k : ℕ) :
    b - A (iterate A Pinv α b x₀ (k + 1)) =
      (b - A (iterate A Pinv α b x₀ k)) - α k • A (Pinv (b - A (iterate A Pinv α b x₀ k))) := by
  rw [iterate_succ, map_add, map_smul]
  abel

/-- The **residual polynomial** of the unpreconditioned nonstationary Richardson iteration with
parameters $(\alpha_j)$:
$$p_k = \prod_{j < k} (1 - \alpha_j X) \in \mathbb{K}[X].$$
-/
noncomputable def residualPoly (k : ℕ) : 𝕜[X] := ∏ j ∈ Finset.range k, (1 - C (α j) * X)

/-- The residual polynomial $p_0$ is $1$. -/
@[simp]
theorem residualPoly_zero : residualPoly α 0 = 1 := by simp [residualPoly]

/-- The residual polynomials satisfy $p_{k+1} = p_k \, (1 - \alpha_k X)$. -/
theorem residualPoly_succ (k : ℕ) :
    residualPoly α (k + 1) = residualPoly α k * (1 - C (α k) * X) := by
  rw [residualPoly, residualPoly, Finset.prod_range_succ]

/-- Every residual polynomial takes the value $1$ at $0$: $p_k(0) = 1$. -/
@[simp]
theorem residualPoly_eval_zero (k : ℕ) : (residualPoly α k).eval 0 = 1 := by
  simp [residualPoly, eval_prod]

/-- The residual polynomial $p_k$ has degree at most $k$. -/
theorem natDegree_residualPoly_le (k : ℕ) : (residualPoly α k).natDegree ≤ k := by
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ j ∈ Finset.range k, (1 - C (α j) * X : 𝕜[X]).natDegree
      ≤ ∑ _j ∈ Finset.range k, 1 := Finset.sum_le_sum fun j _ => by
        refine (natDegree_sub_le _ _).trans ?_
        rw [natDegree_one, max_eq_right (Nat.zero_le _)]
        exact (natDegree_C_mul_le _ _).trans natDegree_X_le
    _ = k := by simp

/-- **The residuals of the unpreconditioned Richardson iteration are polynomials in $A$**
([quarteroni2000numerical], (4.51)). Let $x_k$ be the nonstationary Richardson iteration with
$P^{-1} = I$. Then
$$b - A x_k = p_k(A) (b - A x_0), \qquad p_k = \prod_{j < k} (1 - \alpha_j X).$$
The polynomial $p_k$ has degree at most $k$ and satisfies $p_k(0) = 1$.

This observation opens the chapter of the source on Krylov methods. The polynomial is evaluated
at the linear map $A$ by `Polynomial.aeval`. -/
theorem residual_iterate_eq_prod (k : ℕ) :
    b - A (iterate A LinearMap.id α b x₀ k) = aeval A (residualPoly α k) (b - A x₀) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : aeval A (1 - C (α k) * X) = 1 - α k • A := by
      rw [map_sub, map_one, map_mul, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one,
        smul_mul_assoc, one_mul]
    rw [residual_iterate_succ, residualPoly_succ, mul_comm, map_mul, Module.End.mul_apply, hp, ih,
      LinearMap.id_apply, LinearMap.sub_apply, Module.End.one_apply, LinearMap.smul_apply]

/-- **The Richardson iterates lie in the affine Krylov space** ([quarteroni2000numerical], (4.53)).
Let $x_k$ be the nonstationary Richardson iteration with $P^{-1} = I$, and let
$r_0 = b - A x_0$. Then
$$x_k - x_0 \in \mathcal{K}_k(A, r_0) = \operatorname{span}\{r_0, A r_0, \dots, A^{k-1} r_0\}.$$

The reason is that $x_k - x_0 = \sum_{j < k} \alpha_j r_j$ and
$r_j \in \mathcal{K}_{j+1}(A, r_0)$. The Krylov space is `Krylov.subspace`. -/
theorem iterate_sub_mem_subspace (k : ℕ) :
    iterate A LinearMap.id α b x₀ k - x₀ ∈ Krylov.subspace A (b - A x₀) k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ, LinearMap.id_apply, add_sub_right_comm]
    refine Submodule.add_mem _ (Krylov.subspace_mono A (b - A x₀) (Nat.le_succ k) ih)
      (Submodule.smul_mem _ _ ?_)
    rw [residual_iterate_eq_prod]
    refine Krylov.aeval_apply_mem_subspace A _ ?_
    exact (degree_le_natDegree.trans
      (WithBot.coe_le_coe.mpr (natDegree_residualPoly_le α k))).trans_lt
        (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self k))

end Module

section Gradient

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **The gradient method is nonstationary Richardson** ([quarteroni2000numerical], (4.36)–(4.37)).
Let $E$ be an inner product space over $\mathbb{R}$ or $\mathbb{C}$, let $A$ be a linear map on
$E$, and let $b \in E$. Let $(x_k)$ be a sequence with $x_{k+1} = \mathrm{SD}(x_k)$ for every
$k$, where $\mathrm{SD}$ is the steepest descent step `Projection.steepestDescentStep` for
$A x = b$. Then $(x_k)$ is the unpreconditioned nonstationary Richardson iteration from $x_0$
with the parameters
$$\alpha_k = \frac{\langle r_k, r_k \rangle}{\langle r_k, A r_k \rangle}, \qquad r_k = b - A
  x_k,$$
read off along the sequence.

No hypothesis on $A$ is needed, because the steepest descent step is $x_k + \alpha_k r_k$ with
the same quotient $\alpha_k$, including the value $0$ of a division by zero. -/
theorem iterate_gradient_eq_steepestDescentStep (A : E →ₗ[𝕜] E) (b : E) (x : ℕ → E)
    (hsucc : ∀ k, x (k + 1) = Projection.steepestDescentStep A b (x k)) (k : ℕ) :
    x k = iterate A LinearMap.id
      (fun j => inner 𝕜 (b - A (x j)) (b - A (x j)) / inner 𝕜 (b - A (x j)) (A (b - A (x j))))
      b (x 0) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ, hsucc, Projection.steepestDescentStep, Projection.step1, LinearMap.id_apply,
      ← ih]

end Gradient

end Richardson
