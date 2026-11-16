/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Normed.Operator.Banach
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Eigen.Pencil
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.Stationary.Splitting

/-!
# Stationary iterations for symmetric positive definite systems

This module gives the convergence theory of the classical splittings $A = M - N$ when $A$ is
symmetric positive definite. The central result is the **Householder–John theorem**, also called the
Ostrowski–Reich theorem ([saad2003iterative], Theorem 4.10; [kress1998numerical], Theorem 4.12;
[quarteroni2000numerical], Property 4.2): if $A$ is symmetric positive definite and
$Q = M + M^H - A$ is positive definite, then the iteration operator $G = M^{-1} N$ has spectral
radius $\rho(G) < 1$. Its converse also holds: if $Q$ is positive definite and $\rho(G) < 1$, then
the symmetric matrix $A$ is positive definite. The proofs rest on the **energy identity** $\|G
e\|_A^2 = \|e\|_A^2 - \langle Q y, y \rangle$ with $y = M^{-1} A e$, where
$\|e\|_A^2 = \langle A e, e \rangle$. The identity gives a strict decrease of the energy norm of the
error in each step, and a uniform contraction factor $q < 1$. When $M$ is also symmetric, $G$ is
self-adjoint for the inner products of $A$ and of $M$, so that $\|G e\|_A \le \rho(G) \|e\|_A$ with
equality at an eigenvector ([quarteroni2000numerical], Property 4.1). The results are stated for
operators on a finite-dimensional complex inner product space and then for real matrices.

The criteria for the classical methods are instances. Jacobi converges if $A$ and $2D - A$ are
positive definite; Gauss–Seidel converges for positive definite $A$; SOR converges for positive
definite $A$ if and only if $0 < \omega < 2$; and SSOR converges for positive definite $A$ and
$0 < \omega < 2$. For Richardson's iteration $I - \alpha M$ with a real spectrum in
$[\lambda_{\min}, \lambda_{\max}]$, $0 < \lambda_{\min}$, the spectral radius is $\max\{|1 - \alpha
\lambda_{\min}|, |1 - \alpha \lambda_{\max}|\}$, convergence holds exactly for
$0 < \alpha < 2/\lambda_{\max}$, and $\alpha = 2/(\lambda_{\min} + \lambda_{\max})$ is optimal with
spectral radius $(\lambda_{\max} - \lambda_{\min})/(\lambda_{\max} + \lambda_{\min})$
([quarteroni2000numerical], Theorem 4.9). The determinant of the SOR iteration matrix is
$(1 - \omega)^n$, which gives **Kahan's bound** $|1 - \omega| \le \rho(G_\omega)$. The SSOR
preconditioner is symmetric, positive definite and larger than $A$ in the order of positive
semidefinite matrices.

## Main definitions

* `Stationary.Splitting.energyIterationOperator`: the iteration operator on the space with the
  energy inner product of a symmetric coercive operator.
* `Stationary.Splitting.euclidean`: the splitting of the complex Euclidean operator that a splitting
  of a real matrix induces.

## Main results

* `Stationary.Splitting.spectralRadius_lt_one_of_isSymmetricCoercive`: the Householder–John theorem
  for operators.
* `Stationary.Splitting.isCoercive_of_spectralRadius_lt_one`: its converse.
* `Stationary.Splitting.complexSpectralRadius_lt_one_of_posDef`,
  `Stationary.Splitting.posDef_of_complexSpectralRadius_lt_one`: the two directions for real
  matrices, with $Q = M + M^T - A$.
* `Stationary.Splitting.energyNorm_sq_iterationOperator_apply`: the energy identity.
* `Stationary.Splitting.energyNorm_iterationOperator_apply_lt`: one step strictly decreases the
  energy norm of a nonzero error.
* `Stationary.Splitting.exists_energyNorm_iterationOperator_apply_le`: a uniform contraction factor
  $q < 1$ in the energy norm.
* `Stationary.Splitting.energyNorm_iterationOperator_apply_le_spectralRadius`,
  `Stationary.Splitting.norm_m_iterationOperator_apply_le_spectralRadius`,
  `Stationary.Splitting.exists_energyNorm_iterationOperator_apply_eq_spectralRadius`: for symmetric
  $M$, the operator norms of $G$ for $A$ and for $M$ are $\rho(G)$.
* `Stationary.Splitting.energyNorm_mulVec_iterationOperator_lt`,
  `Stationary.Splitting.exists_energyNorm_mulVec_iterationOperator_le`,
  `Stationary.Splitting.energyNorm_mulVec_iterationOperator_le_complexSpectralRadius`: the same
  three results for real matrices.
* `Stationary.Splitting.complexSpectralRadius_one_sub_smul_eq`,
  `Stationary.Splitting.complexSpectralRadius_one_sub_smul_lt_one_iff`,
  `Stationary.Splitting.isMinOn_complexSpectralRadius_one_sub_smul`,
  `Stationary.Splitting.complexSpectralRadius_one_sub_smul_optimal_eq`: Theorem 4.9 of
  [quarteroni2000numerical] for Richardson's iteration.
* `Stationary.Splitting.richardson_complexSpectralRadius_eq`: the case $M = A$ symmetric
  ([saad2003iterative], Example 4.1; [han2009theoretical], Exercise 5.2.3).
* `Matrix.jorSplitting_isMinOn_complexSpectralRadius`: the optimal JOR parameter
  $2/(2 - \lambda_{\max} - \lambda_{\min})$ for a Jacobi matrix with real eigenvalues
  ([kress1998numerical], Theorem 4.9).
* `Matrix.jorSplitting_complexSpectralRadius_lt_one_of_le_one`: JOR converges for $0 < \omega \le 1$
  whenever Jacobi converges ([quarteroni2000numerical], Theorem 4.6).
* `Matrix.jorSplitting_complexSpectralRadius_lt_one_iff_of_posDef`: for positive definite $A$, JOR
  converges exactly for $0 < \omega < 2/\rho(D^{-1} A)$ ([quarteroni2000numerical], Theorem 4.4).
* `Matrix.det_sorSplitting_iterationOperator`: $\det G_\omega = (1 - \omega)^n$.
* `Matrix.abs_one_sub_le_sorSplitting_complexSpectralRadius`: Kahan's bound
  $|1 - \omega| \le \rho(G_\omega)$ ([quarteroni2000numerical], Theorem 4.7).
* `Matrix.lt_two_of_sorSplitting_complexSpectralRadius_lt_one`: SOR can converge only for
  $0 < \omega < 2$ ([kress1998numerical], Theorem 4.11).
* `Matrix.sorSplitting_complexSpectralRadius_lt_one_iff`: for positive definite $A$, SOR converges
  if and only if $0 < \omega < 2$ ([quarteroni2000numerical], Property 4.3).
* `Matrix.gaussSeidelSplitting_complexSpectralRadius_lt_one_of_posDef`: Gauss–Seidel converges for
  positive definite $A$ ([quarteroni2000numerical], Theorem 4.5).
* `Matrix.jacobiSplitting_complexSpectralRadius_lt_one_of_posDef`: Jacobi converges if $A$ and
  $2D - A$ are positive definite ([quarteroni2000numerical], Theorem 4.3).
* `Matrix.ssorSplitting_m_isSymm`, `Matrix.ssorSplitting_m_posDef_of_diag_pos`,
  `Matrix.ssorSplitting_m_sub_posSemidef`: the SSOR preconditioner $P$ is symmetric, positive
  definite for a symmetric $A$ with positive diagonal and $0 < \omega < 2$ ([golub2013matrix],
  (11.2.24)), and $P - A$ is positive semidefinite.
* `Matrix.ssorSplitting_complexSpectralRadius_lt_one`: SSOR converges for positive definite $A$ and
  $0 < \omega < 2$ ([quarteroni2000numerical], §4.2.6).
* `Matrix.ssorSplitting_iterationOperator_posSemidef_energy`: the SSOR iteration matrix is
  self-adjoint and positive semidefinite for the inner product of $A$.

## Implementation notes

* All spectral statements are over $\mathbb{C}$, because the real spectrum of a real matrix does not
  control convergence. The spectral radius of a real matrix is `Matrix.complexSpectralRadius`, the
  spectral radius of its complexification.
* The operator statements are for a finite-dimensional complex inner product space. "Positive
  definite" is `LinearMap.IsCoercive`, that is $\operatorname{Re} \langle A x, x \rangle \ge c
  \|x\|^2$ for some $c > 0$, and "symmetric positive definite" is `LinearMap.IsSymmetricCoercive`.
  The energy norm is `energyNorm`, $\|x\|_A = \sqrt{\operatorname{Re} \langle A x, x \rangle}$.
* A real splitting reaches the operator statements through `Stationary.Splitting.euclidean`, the
  splitting of `Matrix.toEuclideanCLM (Matrix.complexify A)` on `EuclideanSpace ℂ n`. For real
  matrices the energy norm is written as $\|e\|_A^2 = (A e) \cdot e$.
* The parts $D$, $L$, $U$ of $A$ are `Matrix.diagPart A`, `Matrix.strictLower A` and
  `Matrix.strictUpper A`.
* Property 4.5 of [quarteroni2000numerical] says that $B_{SGS}$ is symmetric positive definite. This
  is false as printed: for a diagonal $A$, $B_{SGS} = 0$, and $B_{SGS}$ is in general not symmetric
  for the Euclidean inner product. The correct statement is
  `Matrix.ssorSplitting_iterationOperator_posSemidef_energy`.
-/

open Filter Topology
open scoped ENNReal NNReal ComplexOrder

namespace Stationary

namespace Splitting

section Comm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {A : E →L[ℂ] E}
  (s : Splitting A)

/-- For a splitting $A = M - N$ of a continuous linear operator on a complex inner product space,
the iteration operator satisfies
$$G x = x - M^{-1} A x.$$
-/
theorem iterationOperator_apply (x : E) :
    s.iterationOperator x = x - Ring.inverse s.m (A x) := by
  rw [iterationOperator, sub_apply, one_apply_eq_self, mul_apply_eq_comp]

/-- For a splitting $A = M - N$ of an operator and every vector $w$, $M (M^{-1} w) = w$. -/
theorem m_ringInverse_apply (w : E) : s.m (Ring.inverse s.m w) = w := by
  rw [← mul_apply_eq_comp, Ring.mul_inverse_cancel _ s.isUnit, one_apply_eq_self]

/-- For a splitting $A = M - N$ of an operator and every vector $w$, $M^{-1} (M w) = w$. -/
theorem ringInverse_m_apply (w : E) : Ring.inverse s.m (s.m w) = w := by
  rw [← mul_apply_eq_comp, Ring.inverse_mul_cancel _ s.isUnit, one_apply_eq_self]

/-- For a splitting with symmetric $M$, $\langle M^{-1} u, v \rangle = \langle u, M^{-1} v \rangle$.
-/
private theorem inner_ringInverse_m_comm (hM : (s.m : E →ₗ[ℂ] E).IsSymmetric) (u v : E) :
    inner ℂ (Ring.inverse s.m u) v = inner ℂ u (Ring.inverse s.m v) := by
  have hM' : ∀ x y, inner ℂ (s.m x) y = inner ℂ x (s.m y) := fun x y => hM x y
  conv_lhs => rw [← m_ringInverse_apply s v]
  rw [← hM', m_ringInverse_apply]

/-- **The iteration operator is self-adjoint for the inner product of $A$.** Let $A = M - N$ be a
splitting of a continuous linear operator on a complex inner product space, with $A$ and $M$
symmetric. Then for all $x$, $y$,
$$\langle A G x, y \rangle = \langle A x, G y \rangle.$$

The reason is that $A G = A - A M^{-1} A$ is symmetric. This property makes the operator norm of
$G$ for $A$ equal to its spectral radius ([quarteroni2000numerical], Property 4.1). -/
theorem energyInner_iterationOperator_comm (hA : (A : E →ₗ[ℂ] E).IsSymmetric)
    (hM : (s.m : E →ₗ[ℂ] E).IsSymmetric) (x y : E) :
    inner ℂ (A (s.iterationOperator x)) y = inner ℂ (A x) (s.iterationOperator y) := by
  have hA' : ∀ u v, inner ℂ (A u) v = inner ℂ u (A v) := fun u v => hA u v
  rw [iterationOperator_apply, iterationOperator_apply, map_sub, inner_sub_left, inner_sub_right,
    hA' (Ring.inverse s.m (A x)) y, inner_ringInverse_m_comm s hM, hA']

/-- **The iteration operator is self-adjoint for the inner product of $M$.** Let $A = M - N$ be a
splitting of a continuous linear operator on a complex inner product space, with $A$ and $M$
symmetric. Then for all $x$, $y$,
$$\langle M G x, y \rangle = \langle M x, G y \rangle.$$

The reason is that $M G = M - A$ is symmetric. -/
theorem inner_m_iterationOperator_comm (hA : (A : E →ₗ[ℂ] E).IsSymmetric)
    (hM : (s.m : E →ₗ[ℂ] E).IsSymmetric) (x y : E) :
    inner ℂ (s.m (s.iterationOperator x)) y = inner ℂ (s.m x) (s.iterationOperator y) := by
  have hA' : ∀ u v, inner ℂ (A u) v = inner ℂ u (A v) := fun u v => hA u v
  have hM' : ∀ u v, inner ℂ (s.m u) v = inner ℂ u (s.m v) := fun u v => hM u v
  rw [iterationOperator_apply, iterationOperator_apply, map_sub, m_ringInverse_apply,
    inner_sub_left, inner_sub_right, hM' x y, hA' x y, ← inner_ringInverse_m_comm s hM,
    ringInverse_m_apply]

/-- Let $A = M - N$ be a splitting of a continuous linear operator on a complex inner product space,
with $A$ coercive. Then for every $e \neq 0$, the increment $e - G e = M^{-1} A e$ of one step
is nonzero. -/
theorem sub_iterationOperator_apply_ne_zero (hA : (A : E →ₗ[ℂ] E).IsCoercive) {e : E}
    (he : e ≠ 0) : e - s.iterationOperator e ≠ 0 := by
  rw [iterationOperator_apply, sub_sub_cancel]
  intro h
  have hAe : A e = 0 := by
    have := congrArg s.m h
    rwa [m_ringInverse_apply, map_zero] at this
  exact he (hA.injective (by simp [hAe]))

end Comm

section Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- For operators $M$, $A$ on a finite-dimensional complex inner product space, $\operatorname{Re}
\langle (M + M^H - A) x, x \rangle = 2 \operatorname{Re} \langle M x, x \rangle -
\operatorname{Re} \langle A x, x \rangle$. -/
private theorem re_inner_hermitianSum (M A : E →L[ℂ] E) (x : E) :
    (inner ℂ ((M + ContinuousLinearMap.adjoint M - A) x) x : ℂ).re
      = 2 * (inner ℂ (M x) x : ℂ).re - (inner ℂ (A x) x : ℂ).re := by
  have h1 : (inner ℂ (ContinuousLinearMap.adjoint M x) x : ℂ)
      = starRingEnd ℂ (inner ℂ (M x) x : ℂ) := by
    rw [ContinuousLinearMap.adjoint_inner_left, ← inner_conj_symm]
  rw [sub_apply, add_apply, inner_sub_left, inner_add_left, h1, Complex.sub_re, Complex.add_re,
    Complex.conj_re]
  ring

omit [FiniteDimensional ℂ E] in
/-- For a splitting $A = M - N$ of an operator, $M (e - G e) = A e$. -/
private theorem apply_sub_iterationOperator {A : E →L[ℂ] E} (s : Splitting A) (e : E) :
    s.m (e - s.iterationOperator e) = A e := by
  have hop : s.iterationOperator e = e - (Ring.inverse s.m) (A e) := by
    rw [Splitting.iterationOperator, sub_apply, one_apply_eq_self, mul_apply_eq_comp]
  have hd : e - s.iterationOperator e = (Ring.inverse s.m) (A e) := by rw [hop]; abel
  rw [hd, ← mul_apply_eq_comp, Ring.mul_inverse_cancel _ s.isUnit, one_apply_eq_self]

/-- **The energy identity of a splitting.** For a splitting $A = M - N$ with $A$ symmetric and
$Q = M + M^H - A$, $\langle A e, e \rangle - \langle A G e, G e \rangle = \langle Q (e - G e),
e - G e \rangle$; both halves of the Householder–John theorem follow from it. -/
private theorem energy_identity {A : E →L[ℂ] E} (s : Splitting A)
    (hA : (A : E →ₗ[ℂ] E).IsSymmetric) (e : E) :
    (inner ℂ (A e) e : ℂ) - (inner ℂ (A (s.iterationOperator e)) (s.iterationOperator e) : ℂ)
      = (inner ℂ ((s.m + ContinuousLinearMap.adjoint s.m - A) (e - s.iterationOperator e))
          (e - s.iterationOperator e) : ℂ) := by
  set d : E := e - s.iterationOperator e with hd
  have hmd : s.m d = A e := apply_sub_iterationOperator s e
  have hGe : s.iterationOperator e = e - d := by rw [hd]; abel
  rw [hGe]
  have h1 : (inner ℂ (A (e - d)) (e - d) : ℂ)
      = inner ℂ (A e) e - inner ℂ (A e) d - inner ℂ (A d) e + inner ℂ (A d) d := by
    simp only [map_sub, inner_sub_left, inner_sub_right]
    ring
  have h2 : (inner ℂ (A e) d : ℂ) = inner ℂ (s.m d) d := by rw [hmd]
  have h3 : (inner ℂ (A d) e : ℂ) = inner ℂ (ContinuousLinearMap.adjoint s.m d) d := by
    rw [ContinuousLinearMap.adjoint_inner_left, hmd]
    exact hA d e
  rw [h1, h2, h3, sub_apply, add_apply, inner_sub_left, inner_add_left]
  ring

/-- The **Householder–John theorem**, also called the **Ostrowski–Reich theorem**, for operators.
Let $E$ be a finite-dimensional complex inner product space, and let $A = M - N$ be a splitting
of a continuous linear operator $A$ on $E$. Suppose that $A$ is symmetric and coercive, and that
$$Q = M + M^H - A$$
is coercive. Then the iteration operator $G = M^{-1} N$ satisfies $\rho(G) < 1$, so the
stationary iteration converges.

This is Theorem 4.10 of [saad2003iterative]. Theorem 4.12 of [kress1998numerical] is the case
$M = \omega^{-1} D - E$. Coercive means $\operatorname{Re} \langle A x, x \rangle \ge c \|x\|^2$
for some $c > 0$, and $M^H$ is the adjoint `ContinuousLinearMap.adjoint`. The proof uses an
eigenpair $G x = \mu x$: it gives $A x = (1 - \mu) M x$, and the comparison of the forms of $A$
and $Q$ at $x$ gives $(1 - |\mu|^2) \langle A x, x \rangle = |1 - \mu|^2 \langle Q x, x
\rangle$, where both forms are positive. -/
theorem spectralRadius_lt_one_of_isSymmetricCoercive {A : E →L[ℂ] E} (s : Splitting A)
    (hA : (A : E →ₗ[ℂ] E).IsSymmetricCoercive)
    (hQ : ((s.m + ContinuousLinearMap.adjoint s.m - A : E →L[ℂ] E) : E →ₗ[ℂ] E).IsCoercive) :
    spectralRadius ℂ s.iterationOperator < 1 := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have : Subsingleton (E →L[ℂ] E) := ⟨fun _ _ => by ext x; exact Subsingleton.elim _ _⟩
    simp
  · suffices h : ∀ μ ∈ spectrum ℂ s.iterationOperator, ‖μ‖₊ < (1 : ℝ≥0) by
      simpa using spectrum.spectralRadius_lt_of_forall_lt _ h
    intro μ hμ
    rw [ContinuousLinearMap.spectrum_eq] at hμ
    obtain ⟨x, hxmem, hx0⟩ :=
      (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ).exists_hasEigenvector
    rw [Module.End.mem_eigenspace_iff] at hxmem
    have hGx : s.iterationOperator x = μ • x := hxmem
    have hAx : A x = (1 - μ) • s.m x := by
      have hop : s.iterationOperator x = x - (Ring.inverse s.m) (A x) := by
        rw [Splitting.iterationOperator, sub_apply, one_apply_eq_self, mul_apply_eq_comp]
      have h1 : (Ring.inverse s.m) (A x) = (1 - μ) • x := by
        rw [sub_smul, one_smul, ← hGx, hop]
        abel
      calc A x = s.m ((Ring.inverse s.m) (A x)) := by
            rw [← mul_apply_eq_comp, Ring.mul_inverse_cancel _ s.isUnit, one_apply_eq_self]
        _ = (1 - μ) • s.m x := by rw [h1, map_smul]
    have hp : 0 < (inner ℂ (A x) x : ℂ).re := hA.isCoercive.inner_self_pos hx0
    have hQpos : 0 < (inner ℂ ((s.m + ContinuousLinearMap.adjoint s.m - A) x) x : ℂ).re :=
      hQ.inner_self_pos hx0
    rw [re_inner_hermitianSum] at hQpos
    have hz0 : (1 : ℂ) - μ ≠ 0 := by
      intro h
      rw [hAx, h, zero_smul] at hp
      simp at hp
    have haw : (inner ℂ (A x) x : ℂ)
        = starRingEnd ℂ (1 - μ) * (inner ℂ (s.m x) x : ℂ) := by
      rw [hAx, inner_smul_left]
    have hconj : starRingEnd ℂ (inner ℂ (A x) x : ℂ) = (inner ℂ (A x) x : ℂ) := by
      rw [inner_conj_symm]
      exact (hA.isSymmetric x x).symm
    have hre : (inner ℂ (A x) x : ℂ).re
        = (1 - μ).re * (inner ℂ (s.m x) x : ℂ).re
          + (1 - μ).im * (inner ℂ (s.m x) x : ℂ).im := by
      rw [haw, Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    have him : (1 - μ).re * (inner ℂ (s.m x) x : ℂ).im
        = (1 - μ).im * (inner ℂ (s.m x) x : ℂ).re := by
      have h : (starRingEnd ℂ (1 - μ) * (inner ℂ (s.m x) x : ℂ)).im = 0 := by
        rw [← haw]
        exact Complex.conj_eq_iff_im.mp hconj
      rw [Complex.mul_im, Complex.conj_re, Complex.conj_im] at h
      linarith
    have hnormz : (0 : ℝ) < (1 - μ).re ^ 2 + (1 - μ).im ^ 2 := by
      have h := Complex.normSq_pos.mpr hz0
      rw [Complex.normSq_apply] at h
      nlinarith
    have key : (1 - μ).re * (inner ℂ (A x) x : ℂ).re
        = ((1 - μ).re ^ 2 + (1 - μ).im ^ 2) * (inner ℂ (s.m x) x : ℂ).re := by
      calc (1 - μ).re * (inner ℂ (A x) x : ℂ).re
          = (1 - μ).re ^ 2 * (inner ℂ (s.m x) x : ℂ).re
            + (1 - μ).im * ((1 - μ).re * (inner ℂ (s.m x) x : ℂ).im) := by
            rw [hre]; ring
        _ = ((1 - μ).re ^ 2 + (1 - μ).im ^ 2) * (inner ℂ (s.m x) x : ℂ).re := by
            rw [him]; ring
    have hprodpos : 0 < (inner ℂ (A x) x : ℂ).re
        * (2 * (1 - μ).re - ((1 - μ).re ^ 2 + (1 - μ).im ^ 2)) := by
      have h : ((1 - μ).re ^ 2 + (1 - μ).im ^ 2)
          * (2 * (inner ℂ (s.m x) x : ℂ).re - (inner ℂ (A x) x : ℂ).re)
          = (inner ℂ (A x) x : ℂ).re
            * (2 * (1 - μ).re - ((1 - μ).re ^ 2 + (1 - μ).im ^ 2)) := by
        linear_combination (-2 : ℝ) * key
      rw [← h]
      exact mul_pos hnormz hQpos
    have hlast : 0 < 2 * (1 - μ).re - ((1 - μ).re ^ 2 + (1 - μ).im ^ 2) := by
      rcases le_or_gt (2 * (1 - μ).re - ((1 - μ).re ^ 2 + (1 - μ).im ^ 2)) 0 with hcon | hcon
      · nlinarith [mul_nonneg hp.le (neg_nonneg.mpr hcon)]
      · exact hcon
    have hmu : ‖μ‖ < 1 := by
      have hn : ‖μ‖ ^ 2 = μ.re ^ 2 + μ.im ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        ring
      have hs : (1 - μ).re = 1 - μ.re := by simp
      have hi : (1 - μ).im = -μ.im := by simp
      rw [hs, hi] at hlast
      nlinarith [norm_nonneg μ]
    exact_mod_cast hmu

/-- **The converse of the Householder–John theorem** ([saad2003iterative], Theorem 4.10, the "only
if" part). Let $E$ be a finite-dimensional complex inner product space, and let $A = M - N$ be a
splitting of a continuous linear operator $A$ on $E$. Suppose that $A$ is symmetric, that
$Q = M + M^H - A$ is coercive, and that $\rho(G) < 1$. Then $A$ is coercive, that is, positive
definite.

Along the error sequence $e_{k+1} = G e_k$, the energy identity makes
$k \mapsto \langle A e_k, e_k \rangle$ nonincreasing, and this sequence tends to $0$ because
$e_k \to 0$. So $\langle A e_0, e_0 \rangle \ge \langle A e_1, e_1 \rangle \ge 0$, and the first
inequality is strict unless $e_1 = e_0$, which would contradict $e_k \to 0$. -/
theorem isCoercive_of_spectralRadius_lt_one {A : E →L[ℂ] E} (s : Splitting A)
    (hA : (A : E →ₗ[ℂ] E).IsSymmetric)
    (hQ : ((s.m + ContinuousLinearMap.adjoint s.m - A : E →L[ℂ] E) : E →ₗ[ℂ] E).IsCoercive)
    (hρ : spectralRadius ℂ s.iterationOperator < 1) :
    (A : E →ₗ[ℂ] E).IsCoercive := by
  rw [LinearMap.isCoercive_iff_forall_pos]
  intro e₀ he₀
  change 0 < (inner ℂ (A e₀) e₀ : ℂ).re
  have hQ0 : ∀ e : E,
      0 ≤ (inner ℂ ((s.m + ContinuousLinearMap.adjoint s.m - A) e) e : ℂ).re := by
    intro e
    rcases eq_or_ne e 0 with rfl | he
    · simp
    · exact (hQ.inner_self_pos he).le
  have htend0 : Tendsto (fun k => (s.iterationOperator ^ k) e₀) atTop (𝓝 0) := by
    have hfix : s.iterationOperator 0 + (0 : E) = 0 := by simp
    have h := Stationary.tendsto_of_spectralRadius_lt_one s.iterationOperator hρ 0 e₀
    rw [show Ring.inverse ((1 : E →L[ℂ] E) - s.iterationOperator) (0 : E) = 0 from map_zero _] at h
    have hiter : ∀ k, (Stationary.step s.iterationOperator (0 : E))^[k] e₀
        = (s.iterationOperator ^ k) e₀ := fun k => by
      simpa using Stationary.step_iterate_sub s.iterationOperator (0 : E) hfix e₀ k
    simpa only [hiter] using h
  have hcont : Continuous fun y : E => (inner ℂ (A y) y : ℂ).re :=
    Complex.continuous_re.comp (A.continuous.inner continuous_id)
  have htendf : Tendsto
      (fun k => (inner ℂ (A ((s.iterationOperator ^ k) e₀)) ((s.iterationOperator ^ k) e₀) : ℂ).re)
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using (hcont.tendsto 0).comp htend0
  have hstep : ∀ e : E,
      (inner ℂ (A (s.iterationOperator e)) (s.iterationOperator e) : ℂ).re
        ≤ (inner ℂ (A e) e : ℂ).re := by
    intro e
    have hre := congrArg Complex.re (energy_identity s hA e)
    rw [Complex.sub_re] at hre
    linarith [hQ0 (e - s.iterationOperator e)]
  have hanti : ∀ k,
      (inner ℂ (A ((s.iterationOperator ^ (k + 1)) e₀)) ((s.iterationOperator ^ (k + 1)) e₀) :
          ℂ).re
        ≤ (inner ℂ (A ((s.iterationOperator ^ k) e₀)) ((s.iterationOperator ^ k) e₀) : ℂ).re := by
    intro k
    rw [show (s.iterationOperator ^ (k + 1)) e₀ = s.iterationOperator ((s.iterationOperator ^ k) e₀)
      from by rw [pow_succ', mul_apply_eq_comp]]
    exact hstep _
  have hanti' : Antitone fun k =>
      (inner ℂ (A ((s.iterationOperator ^ k) e₀)) ((s.iterationOperator ^ k) e₀) : ℂ).re :=
    antitone_nat_of_succ_le hanti
  have hnonneg : ∀ k,
      0 ≤ (inner ℂ (A ((s.iterationOperator ^ k) e₀)) ((s.iterationOperator ^ k) e₀) : ℂ).re := by
    intro k
    refine le_of_tendsto htendf (eventually_atTop.2 ⟨k, fun j hj => ?_⟩)
    exact hanti' hj
  rcases eq_or_ne (e₀ - s.iterationOperator e₀) 0 with hd0 | hd0
  · exfalso
    have hGe : s.iterationOperator e₀ = e₀ := by
      rw [sub_eq_zero] at hd0
      exact hd0.symm
    have hpow : ∀ k, (s.iterationOperator ^ k) e₀ = e₀ := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, mul_apply_eq_comp, hGe, ih]
    exact he₀ (tendsto_nhds_unique tendsto_const_nhds (by simpa only [hpow] using htend0))
  · have hre := congrArg Complex.re (energy_identity s hA e₀)
    rw [Complex.sub_re] at hre
    have h1 := hnonneg 1
    rw [pow_one] at h1
    have hpos : 0 < (inner ℂ ((s.m + ContinuousLinearMap.adjoint s.m - A)
        (e₀ - s.iterationOperator e₀)) (e₀ - s.iterationOperator e₀) : ℂ).re :=
      hQ.inner_self_pos hd0
    linarith


/-- **The energy identity of a splitting.** Let $E$ be a finite-dimensional complex inner product
space, and let $A = M - N$ be a splitting of a continuous linear operator $A$ on $E$ with $A$
symmetric. Let $Q = M + M^H - A$. Then for every $e \in E$,
$$\operatorname{Re} \langle A G e, G e \rangle = \operatorname{Re} \langle A e, e \rangle -
  \operatorname{Re} \langle Q (e - G e), e - G e \rangle.$$

Since $e - G e = M^{-1} A e$, this is $\|G e\|_A^2 = \|e\|_A^2 - \langle Q y, y \rangle$ with
$y = M^{-1} A e$. Both halves of the Householder–John theorem and the monotonicity of the energy
norm follow from it. -/
theorem energyNorm_sq_iterationOperator_apply {A : E →L[ℂ] E} (s : Splitting A)
    (hA : (A : E →ₗ[ℂ] E).IsSymmetric) (e : E) :
    (inner ℂ (A (s.iterationOperator e)) (s.iterationOperator e)).re =
      (inner ℂ (A e) e).re -
        (inner ℂ ((s.m + ContinuousLinearMap.adjoint s.m - A) (e - s.iterationOperator e))
          (e - s.iterationOperator e)).re := by
  have h := congrArg Complex.re (energy_identity s hA e)
  rw [Complex.sub_re] at h
  linarith

/-- **Monotone convergence in the energy norm** ([quarteroni2000numerical], Property 4.2 and the
monotonicity clause of Theorem 4.5). Let $E$ be a finite-dimensional complex inner product
space, and let $A = M - N$ be a splitting of a continuous linear operator $A$ on $E$. Suppose
that $A$ is symmetric and coercive and that $Q = M + M^H - A$ is coercive. Then for every
$e \neq 0$,
$$\|G e\|_A < \|e\|_A.$$

This follows from the energy identity, since $\langle Q y, y \rangle > 0$ for
$y = M^{-1} A e \neq 0$. The norm is `energyNorm`, $\|x\|_A = \sqrt{\operatorname{Re} \langle A
x, x \rangle}$. -/
theorem energyNorm_iterationOperator_apply_lt {A : E →L[ℂ] E} (s : Splitting A)
    (hA : (A : E →ₗ[ℂ] E).IsSymmetricCoercive)
    (hQ : ((s.m + ContinuousLinearMap.adjoint s.m - A : E →L[ℂ] E) : E →ₗ[ℂ] E).IsCoercive)
    {e : E} (he : e ≠ 0) :
    energyNorm (A : E →ₗ[ℂ] E) (s.iterationOperator e) < energyNorm (A : E →ₗ[ℂ] E) e := by
  have hQpos := hQ.inner_self_pos (sub_iterationOperator_apply_ne_zero s hA.isCoercive he)
  have hid : RCLike.re (inner ℂ ((A : E →ₗ[ℂ] E) (s.iterationOperator e)) (s.iterationOperator e))
      = RCLike.re (inner ℂ ((A : E →ₗ[ℂ] E) e) e) -
        RCLike.re (inner ℂ (((s.m + ContinuousLinearMap.adjoint s.m - A : E →L[ℂ] E) : E →ₗ[ℂ] E)
          (e - s.iterationOperator e)) (e - s.iterationOperator e)) :=
    energyNorm_sq_iterationOperator_apply s hA.isSymmetric e
  have h0 : 0 ≤ RCLike.re (inner ℂ ((A : E →ₗ[ℂ] E) (s.iterationOperator e))
      (s.iterationOperator e)) := hA.isPositive.re_inner_nonneg_left _
  unfold energyNorm
  exact Real.sqrt_lt_sqrt h0 (by linarith)

section EnergySpace

variable {A : E →L[ℂ] E} (s : Splitting A) {B : E →ₗ[ℂ] E} (hB : B.IsSymmetricCoercive)

/-- For a splitting of $A$ and a symmetric coercive operator $B$ on a finite-dimensional complex
inner product space, the iteration operator $G$ viewed as an operator on the space
`WithEnergy B hB`, which carries the inner product $\langle B x, y \rangle$.

The operator is transported along `WithEnergy.equiv`; it is continuous because the space is
finite-dimensional. -/
noncomputable def energyIterationOperator :
    WithEnergy B hB →L[ℂ] WithEnergy B hB :=
  LinearMap.toContinuousLinearMap
    ((WithEnergy.equiv B hB).conjAlgEquiv (R := ℂ) (s.iterationOperator : E →ₗ[ℂ] E))

/-- The iteration operator on the energy space of $B$ acts on a transported vector as $G$ acts on
the vector. -/
theorem energyIterationOperator_apply (x : E) :
    energyIterationOperator s hB (WithEnergy.equiv B hB x)
      = WithEnergy.equiv B hB (s.iterationOperator x) := by
  simp [energyIterationOperator]

/-- The iteration operator on the energy space of $B$ has the same spectrum as $G$. -/
theorem spectrum_energyIterationOperator :
    spectrum ℂ (energyIterationOperator s hB) = spectrum ℂ s.iterationOperator := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ _
  rw [ContinuousLinearMap.spectrum_eq, ContinuousLinearMap.spectrum_eq, energyIterationOperator,
    LinearMap.coe_toContinuousLinearMap, AlgEquiv.spectrum_eq]

/-- The iteration operator on the energy space of $B$ has the same spectral radius as $G$. -/
theorem spectralRadius_energyIterationOperator :
    spectralRadius ℂ (energyIterationOperator s hB) = spectralRadius ℂ s.iterationOperator := by
  simp only [spectralRadius_eq_of_unital, spectrum_energyIterationOperator]

/-- Let $B$ be a symmetric coercive operator. If $\langle B G x, y \rangle = \langle B x, G y
\rangle$ for all $x$, $y$, then the iteration operator on the energy space of $B$ is
self-adjoint. -/
theorem isSelfAdjoint_energyIterationOperator
    (hcomm : ∀ x y, inner ℂ (B (s.iterationOperator x)) y = inner ℂ (B x) (s.iterationOperator y)) :
    IsSelfAdjoint (energyIterationOperator s hB) :=
  LinearMap.IsSymmetric.isSelfAdjoint hcomm

include hB in
/-- **The operator norm of a $B$-symmetric iteration operator for $B$ is its spectral radius.** Let
$E$ be a finite-dimensional complex inner product space, let $A = M - N$ be a splitting of a
continuous linear operator on $E$, and let $B$ be a symmetric coercive operator on $E$. If
$\langle B G x, y \rangle = \langle B x, G y \rangle$ for all $x$, $y$, then for every
$e \in E$,
$$\|G e\|_B \le \rho(G) \, \|e\|_B.$$

On the energy space of $B$ the operator $G$ is self-adjoint, and a self-adjoint operator on a
Hilbert space has norm equal to its spectral radius (`IsSelfAdjoint.spectralRadius_eq_nnnorm`).
The spectral radius is the real number `(spectralRadius ℂ _).toReal`. -/
theorem energyNorm_iterationOperator_apply_le_spectralRadius_of_comm
    (hcomm : ∀ x y, inner ℂ (B (s.iterationOperator x)) y = inner ℂ (B x) (s.iterationOperator y))
    (e : E) :
    energyNorm B (s.iterationOperator e) ≤
      (spectralRadius ℂ s.iterationOperator).toReal * energyNorm B e := by
  have hρ : (spectralRadius ℂ s.iterationOperator).toReal = ‖energyIterationOperator s hB‖ := by
    rw [← spectralRadius_energyIterationOperator s hB,
      (isSelfAdjoint_energyIterationOperator s hB hcomm).spectralRadius_eq_nnnorm]
    simp
  rw [hρ, ← WithEnergy.norm_equiv, ← WithEnergy.norm_equiv, ← energyIterationOperator_apply]
  exact (energyIterationOperator s hB).le_opNorm _

include hB in
/-- **The spectral radius is attained in every energy norm.** Let $E$ be a nontrivial
finite-dimensional complex inner product space, let $A = M - N$ be a splitting of a continuous
linear operator on $E$, and let $B$ be a symmetric coercive operator on $E$. Then there is
$e \neq 0$ with
$$\|G e\|_B = \rho(G) \, \|e\|_B.$$

Such an $e$ is an eigenvector for an eigenvalue of maximal modulus. No symmetry of $G$ is
needed. -/
theorem exists_energyNorm_iterationOperator_apply_eq_spectralRadius [Nontrivial E] :
    ∃ e : E, e ≠ 0 ∧ energyNorm B (s.iterationOperator e) =
      (spectralRadius ℂ s.iterationOperator).toReal * energyNorm B e := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ _
  obtain ⟨μ, hμ, hμρ⟩ := spectrum.exists_nnnorm_eq_spectralRadius s.iterationOperator
  rw [ContinuousLinearMap.spectrum_eq] at hμ
  obtain ⟨e, he, he0⟩ :=
    (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ).exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff] at he
  have hGe : s.iterationOperator e = μ • e := he
  refine ⟨e, he0, ?_⟩
  rw [hGe, ← WithEnergy.norm_equiv B hB, ← WithEnergy.norm_equiv B hB, map_smul, norm_smul, ← hμρ]
  simp

end EnergySpace

/-- **The uniform contraction in the energy norm** ([quarteroni2000numerical], Property 4.2,
$\rho(B) \le \|B\|_A < 1$). Let $E$ be a finite-dimensional complex inner product space, and let
$A = M - N$ be a splitting of a continuous linear operator $A$ on $E$. Suppose that $A$ is
symmetric and coercive and that $Q = M + M^H - A$ is coercive. Then there is $q < 1$ such that
for every $e \in E$,
$$\|G e\|_A \le q \, \|e\|_A.$$

The strict decrease of `Stationary.Splitting.energyNorm_iterationOperator_apply_lt` becomes
uniform on the compact unit sphere of the energy space, where $\|G e\|_A$ attains its maximum. -/
theorem exists_energyNorm_iterationOperator_apply_le {A : E →L[ℂ] E} (s : Splitting A)
    (hA : (A : E →ₗ[ℂ] E).IsSymmetricCoercive)
    (hQ : ((s.m + ContinuousLinearMap.adjoint s.m - A : E →L[ℂ] E) : E →ₗ[ℂ] E).IsCoercive) :
    ∃ q : ℝ, q < 1 ∧ ∀ e : E, energyNorm (A : E →ₗ[ℂ] E) (s.iterationOperator e) ≤
      q * energyNorm (A : E →ₗ[ℂ] E) e := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact ⟨0, zero_lt_one, fun e => by simp [Subsingleton.elim e 0, energyNorm]⟩
  set T := energyIterationOperator s hA with hT
  have hne : (Metric.sphere (0 : WithEnergy (A : E →ₗ[ℂ] E) hA) 1).Nonempty := by
    obtain ⟨e₀, he₀⟩ := exists_ne (0 : E)
    have h0 : ‖WithEnergy.equiv (A : E →ₗ[ℂ] E) hA e₀‖ ≠ 0 := by
      rw [WithEnergy.norm_equiv]
      exact (hA.energyNorm_pos he₀).ne'
    refine ⟨‖WithEnergy.equiv (A : E →ₗ[ℂ] E) hA e₀‖⁻¹ • WithEnergy.equiv (A : E →ₗ[ℂ] E) hA e₀, ?_⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ h0]
  obtain ⟨u₀, hu₀, hmax⟩ := (isCompact_sphere (0 : WithEnergy (A : E →ₗ[ℂ] E) hA) 1).exists_isMaxOn
    hne (continuous_norm.comp T.continuous).continuousOn
  have hu₀' : ‖u₀‖ = 1 := mem_sphere_zero_iff_norm.mp hu₀
  refine ⟨‖T u₀‖, ?_, fun e => ?_⟩
  · obtain ⟨x₀, rfl⟩ := (WithEnergy.equiv (A : E →ₗ[ℂ] E) hA).surjective u₀
    have hx₀ : x₀ ≠ 0 := by
      rintro rfl
      simp at hu₀'
    have := energyNorm_iterationOperator_apply_lt s hA hQ hx₀
    rwa [← WithEnergy.norm_equiv (A : E →ₗ[ℂ] E) hA, ← WithEnergy.norm_equiv (A : E →ₗ[ℂ] E) hA,
      ← energyIterationOperator_apply, hu₀'] at this
  · rcases eq_or_ne e 0 with rfl | he
    · simp [energyNorm]
    · set u := WithEnergy.equiv (A : E →ₗ[ℂ] E) hA e with hu
      have hu0 : ‖u‖ ≠ 0 := by
        rw [hu, WithEnergy.norm_equiv]
        exact (hA.energyNorm_pos he).ne'
      have hnc : ‖((‖u‖⁻¹ : ℝ) : ℂ)‖ = ‖u‖⁻¹ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
      have hv : ((‖u‖⁻¹ : ℝ) : ℂ) • u ∈ Metric.sphere (0 : WithEnergy (A : E →ₗ[ℂ] E) hA) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, hnc, inv_mul_cancel₀ hu0]
      have h1 : ‖T (((‖u‖⁻¹ : ℝ) : ℂ) • u)‖ ≤ ‖T u₀‖ := hmax hv
      rw [map_smul, norm_smul, hnc] at h1
      have h2 : ‖T u‖ ≤ ‖T u₀‖ * ‖u‖ := by
        have := mul_le_mul_of_nonneg_left h1 (norm_nonneg u)
        rwa [← mul_assoc, mul_inv_cancel₀ hu0, one_mul, mul_comm] at this
      rwa [hu, energyIterationOperator_apply, WithEnergy.norm_equiv, WithEnergy.norm_equiv] at h2

/-- **The operator norm of $G$ for $A$ is $\rho(G)$** ([quarteroni2000numerical], Property 4.1, the
clause for the norm of $A$). Let $E$ be a finite-dimensional complex inner product space, and
let $A = M - N$ be a splitting of a continuous linear operator $A$ on $E$, with $A$ symmetric
and coercive and $M$ symmetric. Then for every $e \in E$,
$$\|G e\|_A \le \rho(G) \, \|e\|_A.$$

This is the inequality half of $\rho(G) = \|G\|_A$. The equality is attained by
`Stationary.Splitting.exists_energyNorm_iterationOperator_apply_eq_spectralRadius`. -/
theorem energyNorm_iterationOperator_apply_le_spectralRadius {A : E →L[ℂ] E} (s : Splitting A)
    (hA : (A : E →ₗ[ℂ] E).IsSymmetricCoercive) (hM : (s.m : E →ₗ[ℂ] E).IsSymmetric) (e : E) :
    energyNorm (A : E →ₗ[ℂ] E) (s.iterationOperator e) ≤
      (spectralRadius ℂ s.iterationOperator).toReal * energyNorm (A : E →ₗ[ℂ] E) e :=
  energyNorm_iterationOperator_apply_le_spectralRadius_of_comm s hA
    (energyInner_iterationOperator_comm s hA.isSymmetric hM) e

/-- **The operator norm of $G$ for $M$ is $\rho(G)$** ([quarteroni2000numerical], Property 4.1, the
clause for the norm of the preconditioner). Let $E$ be a finite-dimensional complex inner
product space, and let $A = M - N$ be a splitting of a continuous linear operator $A$ on $E$,
with $A$ symmetric and $M$ symmetric and coercive. Then for every $e \in E$,
$$\|G e\|_M \le \rho(G) \, \|e\|_M.$$
-/
theorem norm_m_iterationOperator_apply_le_spectralRadius {A : E →L[ℂ] E} (s : Splitting A)
    (hA : (A : E →ₗ[ℂ] E).IsSymmetric) (hM : (s.m : E →ₗ[ℂ] E).IsSymmetricCoercive) (e : E) :
    energyNorm (s.m : E →ₗ[ℂ] E) (s.iterationOperator e) ≤
      (spectralRadius ℂ s.iterationOperator).toReal * energyNorm (s.m : E →ₗ[ℂ] E) e :=
  energyNorm_iterationOperator_apply_le_spectralRadius_of_comm s hM
    (inner_m_iterationOperator_comm s hA hM.isSymmetric) e

end Operator

section Euclidean

/-!
### Real matrices

A splitting of a real matrix $A$ reaches the operator statements through
`Stationary.Splitting.euclidean`. This is the splitting of the operator
`Matrix.toEuclideanCLM (Matrix.complexify A)` on `EuclideanSpace ℂ n`, obtained by complexification
and transport along the star algebra equivalence `Matrix.toEuclideanCLM`.
-/

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (s : Splitting A)

/-- The splitting of the operator of the complex matrix $A$ on `EuclideanSpace ℂ n` that a splitting
of a real square matrix $A$ induces: its part $m$ is the operator of the complex matrix $m$. -/
noncomputable def euclidean : Splitting (toEuclideanCLM (n := n) (𝕜 := ℂ) (Matrix.complexify A)) :=
  s.complexify.map (toEuclideanCLM (n := n) (𝕜 := ℂ))

/-- The part $m$ of the induced Euclidean splitting is the operator `Matrix.toEuclideanCLM` of the
complexification of $m$. -/
theorem euclidean_m :
    s.euclidean.m = toEuclideanCLM (n := n) (𝕜 := ℂ) (Matrix.complexify s.m) := rfl

/-- The iteration operator of the induced Euclidean splitting is the operator
`Matrix.toEuclideanCLM` of the complexification of the real iteration matrix. -/
theorem euclidean_iterationOperator :
    s.euclidean.iterationOperator
      = toEuclideanCLM (n := n) (𝕜 := ℂ) (Matrix.complexify s.iterationOperator) := by
  rw [euclidean, map_iterationOperator, Splitting.complexify_iterationOperator]

/-- The spectral radius of the iteration operator of the induced Euclidean splitting is the spectral
radius $\rho(G)$ of the real iteration matrix $G$, computed over $\mathbb{C}$. -/
theorem spectralRadius_euclidean_iterationOperator :
    spectralRadius ℂ s.euclidean.iterationOperator = complexSpectralRadius s.iterationOperator := by
  rw [euclidean_iterationOperator, complexSpectralRadius_eq_iSup, spectralRadius_eq_of_unital,
    AlgEquiv.spectrum_eq (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ))]

/-- For the induced Euclidean splitting of a splitting $A = M - N$ of a real matrix, the operator
$M + M^H - A$ is the operator of the complexification of the real matrix $M + M^T - A$. -/
theorem euclidean_m_add_adjoint_sub :
    s.euclidean.m + ContinuousLinearMap.adjoint s.euclidean.m
      - toEuclideanCLM (n := n) (𝕜 := ℂ) (Matrix.complexify A)
      = toEuclideanCLM (n := n) (𝕜 := ℂ) (Matrix.complexify (s.m + s.mᵀ - A)) := by
  rw [euclidean_m, ← ContinuousLinearMap.star_eq_adjoint, ← map_star, ← map_add, ← map_sub,
    Matrix.complexify_sub, Matrix.complexify_add, ← conjTranspose_eq_transpose_of_trivial s.m,
    Matrix.complexify_conjTranspose, Matrix.star_eq_conjTranspose]

/-- **The Householder–John theorem for real matrices** ([saad2003iterative], Theorem 4.10;
[quarteroni2000numerical], Properties 4.1–4.2). Let $A = M - N$ be a splitting of a real
symmetric positive definite matrix $A$, and suppose that $M + M^T - A$ is symmetric positive
definite. Then
$$\rho(M^{-1} N) < 1.$$

This is `Stationary.Splitting.spectralRadius_lt_one_of_isSymmetricCoercive` for the induced
Euclidean splitting. The spectral radius is `Matrix.complexSpectralRadius`. -/
theorem complexSpectralRadius_lt_one_of_posDef (hA : A.PosDef) (hQ : (s.m + s.mᵀ - A).PosDef) :
    complexSpectralRadius s.iterationOperator < 1 := by
  rw [← spectralRadius_euclidean_iterationOperator]
  refine spectralRadius_lt_one_of_isSymmetricCoercive s.euclidean
    hA.isSymmetricCoercive_toEuclideanCLM_complexify ?_
  rw [euclidean_m_add_adjoint_sub]
  exact hQ.isSymmetricCoercive_toEuclideanCLM_complexify.isCoercive

/-- **The converse of the Householder–John theorem for real matrices** ([saad2003iterative], Theorem
4.10, the "only if" part). Let $A = M - N$ be a splitting of a real symmetric matrix $A$, and
suppose that $M + M^T - A$ is symmetric positive definite. If $\rho(M^{-1} N) < 1$, then $A$ is
positive definite. -/
theorem posDef_of_complexSpectralRadius_lt_one (hA : A.IsHermitian) (hQ : (s.m + s.mᵀ - A).PosDef)
    (hρ : complexSpectralRadius s.iterationOperator < 1) : A.PosDef := by
  rw [← spectralRadius_euclidean_iterationOperator] at hρ
  have hco := isCoercive_of_spectralRadius_lt_one s.euclidean
    hA.isSymmetric_toEuclideanCLM_complexify
    (by rw [euclidean_m_add_adjoint_sub]
        exact hQ.isSymmetricCoercive_toEuclideanCLM_complexify.isCoercive) hρ
  rw [← posDef_complexify_iff, posDef_iff_isSymmetricCoercive]
  have hsym := hA.isSymmetric_toEuclideanCLM_complexify
  rw [coe_toEuclideanCLM_eq_toEuclideanLin] at hsym hco
  exact ⟨hsym, hco⟩

end Euclidean

end Splitting

end Stationary

namespace Matrix

open Stationary

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- If every complex eigenvalue of a real matrix $X$ has modulus at most $K$ and one of them has
modulus $K$, then $\rho(X) = K$. -/
private theorem complexSpectralRadius_eq_of_forall_le {X : Matrix n n ℝ} {K : ℝ}
    (hle : ∀ μ ∈ spectrum ℂ (complexify X), ‖μ‖ ≤ K)
    (hmem : ∃ μ ∈ spectrum ℂ (complexify X), ‖μ‖ = K) :
    complexSpectralRadius X = ENNReal.ofReal K := by
  obtain ⟨μ₀, hμ₀, hμ₀K⟩ := hmem
  rw [complexSpectralRadius_eq_iSup]
  refine le_antisymm (iSup₂_le fun μ hμ => ?_) ?_
  · calc (‖μ‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖μ‖ := by rw [ofReal_norm]; rfl
      _ ≤ ENNReal.ofReal K := ENNReal.ofReal_le_ofReal (hle μ hμ)
  · calc ENNReal.ofReal K = (‖μ₀‖₊ : ℝ≥0∞) := by rw [← hμ₀K, ofReal_norm]; rfl
      _ ≤ _ := le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ (complexify X)) => (‖k‖₊ : ℝ≥0∞)) μ₀ hμ₀

/-- For a real matrix $X$ and real $c$, $d$ with $d \neq 0$, the complex eigenvalues of $c I + d X$
are the numbers $c + d \nu$ for the complex eigenvalues $\nu$ of $X$. -/
private theorem mem_spectrum_complexify_affine_iff (X : Matrix n n ℝ) {c d : ℝ} (hd : d ≠ 0)
    (μ : ℂ) :
    μ ∈ spectrum ℂ (complexify (c • 1 + d • X)) ↔
      ∃ ν ∈ spectrum ℂ (complexify X), μ = (c : ℂ) + (d : ℂ) * ν := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  rw [complexify_add, complexify_smul, complexify_smul, complexify_one,
    mem_spectrum_affine_iff hd']
  refine ⟨fun h => ⟨_, h, by rw [mul_div_cancel₀ _ hd']; ring⟩, ?_⟩
  rintro ⟨ν, hν, rfl⟩
  have hcancel : ((c : ℂ) + (d : ℂ) * ν - (c : ℂ)) / (d : ℂ) = ν := by
    field_simp
    ring
  rwa [hcancel]

/-- **The spectral radius of an affine function of a real matrix.** Let $X$ be a real square matrix
whose complex eigenvalues are real and lie in $[\lambda_{\min}, \lambda_{\max}]$, where
$\lambda_{\min}$ and $\lambda_{\max}$ are eigenvalues of $X$. Then for all real $c$ and
$d \neq 0$,
$$\rho(c I + d X) = \max\{|c + d \lambda_{\min}|, |c + d \lambda_{\max}|\}.$$

The absolute value is convex, so the largest $|c + d t|$ for
$t \in [\lambda_{\min}, \lambda_{\max}]$ is at an endpoint. This result is used for the choice
of the relaxation parameter of Richardson's iteration and of JOR. The spectral radius is
`Matrix.complexSpectralRadius`. -/
theorem complexSpectralRadius_affine {X : Matrix n n ℝ} {lmin lmax : ℝ}
    (hsub : spectrum ℂ (complexify X) ⊆ Complex.ofReal '' Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ X) (hmax : lmax ∈ spectrum ℝ X) {c d : ℝ} (hd : d ≠ 0) :
    complexSpectralRadius (c • 1 + d • X)
      = ENNReal.ofReal (max |c + d * lmin| |c + d * lmax|) := by
  have hminC : ((lmin : ℝ) : ℂ) ∈ spectrum ℂ (complexify X) :=
    (ofReal_mem_spectrum_complexify_iff X lmin).mpr hmin
  have hmaxC : ((lmax : ℝ) : ℂ) ∈ spectrum ℂ (complexify X) :=
    (ofReal_mem_spectrum_complexify_iff X lmax).mpr hmax
  have hmem : ∀ r : ℝ, ((r : ℝ) : ℂ) ∈ spectrum ℂ (complexify X) →
      ((c + d * r : ℝ) : ℂ) ∈ spectrum ℂ (complexify (c • 1 + d • X)) := by
    intro r hr
    rw [mem_spectrum_complexify_affine_iff X hd]
    exact ⟨(r : ℂ), hr, by push_cast; ring⟩
  refine complexSpectralRadius_eq_of_forall_le (fun μ hμ => ?_) ?_
  · rw [mem_spectrum_complexify_affine_iff X hd] at hμ
    obtain ⟨ν, hν, rfl⟩ := hμ
    obtain ⟨r, hr, rfl⟩ := hsub hν
    have h : ((c : ℂ) + (d : ℂ) * (r : ℂ)) = ((c + d * r : ℝ) : ℂ) := by push_cast; ring
    rw [h, Complex.norm_real, Real.norm_eq_abs]
    rcases le_or_gt 0 d with hd0 | hd0
    · exact abs_le_max_abs_abs (by nlinarith [hr.1]) (by nlinarith [hr.2])
    · rw [max_comm]
      exact abs_le_max_abs_abs (by nlinarith [hr.2]) (by nlinarith [hr.1])
  · rcases max_cases |c + d * lmin| |c + d * lmax| with ⟨he, -⟩ | ⟨he, -⟩
    · exact ⟨_, hmem lmin hminC, by rw [he, Complex.norm_real, Real.norm_eq_abs]⟩
    · exact ⟨_, hmem lmax hmaxC, by rw [he, Complex.norm_real, Real.norm_eq_abs]⟩

/-- The complex eigenvalues of a real symmetric matrix are its real eigenvalues. -/
private theorem IsHermitian.spectrum_complexify_eq {X : Matrix n n ℝ} (hX : X.IsHermitian) :
    spectrum ℂ (complexify X) = Complex.ofReal '' spectrum ℝ X := by
  have hC : (complexify X).IsHermitian := (isHermitian_complexify_iff X).mpr hX
  refine Set.Subset.antisymm (fun μ hμ => ?_) ?_
  · obtain ⟨r, rfl⟩ : ∃ r : ℝ, (r : ℂ) = μ := by
      have := hμ
      rw [hC.spectrum_eq_image_range] at this
      obtain ⟨r, -, rfl⟩ := this
      exact ⟨r, rfl⟩
    exact ⟨r, (ofReal_mem_spectrum_complexify_iff X r).mp hμ, rfl⟩
  · rintro _ ⟨r, hr, rfl⟩
    exact (ofReal_mem_spectrum_complexify_iff X r).mpr hr
/-- If the complex spectrum of a real matrix lies in $[\lambda_{\min}, \lambda_{\max}]$ and
$\lambda_{\min}$ is an eigenvalue, then $\lambda_{\min} \le \lambda_{\max}$. -/
private theorem le_of_spectrum_subset {X : Matrix n n ℝ} {lmin lmax : ℝ}
    (hsub : spectrum ℂ (complexify X) ⊆ Complex.ofReal '' Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ X) : lmin ≤ lmax := by
  obtain ⟨r, hr, hre⟩ := hsub ((ofReal_mem_spectrum_complexify_iff X lmin).mpr hmin)
  rw [Complex.ofReal_inj] at hre
  exact hre ▸ hr.2

/-- For real numbers $0 < a \le b$ and every real $t$,
$$\frac{b - a}{b + a} \le \max\{|1 - t a|, |1 - t b|\}.$$

The combination of $1 - t a$ and $-(1 - t b)$ with the weights $b/(a + b)$ and $a/(a + b)$ is
this constant, whatever $t$ is. -/
theorem le_max_abs_one_sub_mul {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (t : ℝ) :
    (b - a) / (b + a) ≤ max |1 - t * a| |1 - t * b| := by
  have hb : 0 < b := ha.trans_le hab
  have hA : 1 - t * a ≤ max |1 - t * a| |1 - t * b| := (le_abs_self _).trans (le_max_left _ _)
  have hB : -(1 - t * b) ≤ max |1 - t * a| |1 - t * b| := (neg_le_abs _).trans (le_max_right _ _)
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < b + a)]
  nlinarith [mul_le_mul_of_nonneg_left hA hb.le, mul_le_mul_of_nonneg_left hB ha.le]

/-- For real numbers $0 < a \le b$, at $t = 2/(a + b)$ the two terms of
$\max\{|1 - t a|, |1 - t b|\}$ are equal, and
$$\max\Bigl\{\Bigl|1 - \frac{2a}{a + b}\Bigr|, \Bigl|1 - \frac{2b}{a + b}\Bigr|\Bigr\} =
  \frac{b - a}{b + a}.$$

By `Matrix.le_max_abs_one_sub_mul`, this is the minimum over $t$. -/
theorem max_abs_one_sub_mul_optimal {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    max |1 - 2 / (a + b) * a| |1 - 2 / (a + b) * b| = (b - a) / (b + a) := by
  have hb : 0 < b := ha.trans_le hab
  have h1 : 1 - 2 / (a + b) * a = (b - a) / (b + a) := by field_simp; ring
  have h2 : 1 - 2 / (a + b) * b = -((b - a) / (b + a)) := by field_simp; ring
  rw [h1, h2, abs_neg, abs_of_nonneg (div_nonneg (by linarith) (by linarith)), max_self]

end Matrix

/-! ### Richardson's iteration -/

namespace Stationary

namespace Splitting

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The spectral radius of Richardson's iteration matrix.** Let $M$ be a real square matrix whose
complex eigenvalues are real and lie in $[\lambda_{\min}, \lambda_{\max}]$, where
$\lambda_{\min}$ and $\lambda_{\max}$ are eigenvalues of $M$. Then for every real
$\alpha \neq 0$,
$$\rho(I - \alpha M) = \max\{|1 - \alpha \lambda_{\min}|, |1 - \alpha \lambda_{\max}|\}.$$

This is the first step of Theorem 4.9 of [quarteroni2000numerical], for $M = P^{-1} A$. The
eigenvalues of $I - \alpha M$ are the images of those of $M$ under $t \mapsto 1 - \alpha t$, and
the absolute value is convex. -/
theorem complexSpectralRadius_one_sub_smul_eq {M : Matrix n n ℝ} {lmin lmax : ℝ}
    (hsub : spectrum ℂ (Matrix.complexify M) ⊆ Complex.ofReal '' Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ M) (hmax : lmax ∈ spectrum ℝ M) {α : ℝ} (hα : α ≠ 0) :
    complexSpectralRadius (1 - α • M) = ENNReal.ofReal (max |1 - α * lmin| |1 - α * lmax|) := by
  have hrw : (1 : Matrix n n ℝ) - α • M = (1 : ℝ) • 1 + (-α) • M := by module
  rw [hrw, complexSpectralRadius_affine hsub hmin hmax (neg_ne_zero.mpr hα)]
  ring_nf

/-- **Richardson's iteration converges exactly for $0 < \alpha < 2/\lambda_{\max}$**
([quarteroni2000numerical], Theorem 4.9, the convergence clause). Let $M$ be a real square
matrix whose complex eigenvalues are real and lie in $[\lambda_{\min}, \lambda_{\max}]$, where
$\lambda_{\min}$ and $\lambda_{\max}$ are eigenvalues of $M$ and $0 < \lambda_{\min}$. Then for
every real $\alpha$,
$$\rho(I - \alpha M) < 1 \iff 0 < \alpha < \frac{2}{\lambda_{\max}}.$$

With $M = P^{-1} A$ this is the preconditioned statement of the source. -/
theorem complexSpectralRadius_one_sub_smul_lt_one_iff {M : Matrix n n ℝ} {lmin lmax : ℝ}
    (hsub : spectrum ℂ (Matrix.complexify M) ⊆ Complex.ofReal '' Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ M) (hmax : lmax ∈ spectrum ℝ M) (hpos : 0 < lmin) (α : ℝ) :
    complexSpectralRadius (1 - α • M) < 1 ↔ 0 < α ∧ α < 2 / lmax := by
  have hle : lmin ≤ lmax := le_of_spectrum_subset hsub hmin
  have hmaxpos : 0 < lmax := hpos.trans_le hle
  rcases eq_or_ne α 0 with rfl | hα
  · simp only [zero_smul, sub_zero, lt_self_iff_false, false_and, iff_false, not_lt]
    have h1 : ((1 : ℝ) : ℂ) ∈ spectrum ℂ (Matrix.complexify (1 : Matrix n n ℝ)) := by
      have hne : (spectrum ℂ (Matrix.complexify M)).Nonempty :=
        ⟨_, (ofReal_mem_spectrum_complexify_iff M lmin).mpr hmin⟩
      have : Nontrivial (Matrix n n ℂ) := by
        obtain ⟨z, hz⟩ := hne
        by_contra hcon
        rw [not_nontrivial_iff_subsingleton] at hcon
        exact spectrum.mem_iff.mp hz (isUnit_of_subsingleton _)
      rw [Matrix.complexify_one, Complex.ofReal_one, spectrum.mem_iff, map_one, sub_self]
      exact not_isUnit_zero
    calc (1 : ℝ≥0∞) = (‖((1 : ℝ) : ℂ)‖₊ : ℝ≥0∞) := by simp
      _ ≤ complexSpectralRadius (1 : Matrix n n ℝ) := Matrix.nnnorm_le_complexSpectralRadius h1
  rw [complexSpectralRadius_one_sub_smul_eq hsub hmin hmax hα, ENNReal.ofReal_lt_one, max_lt_iff,
    abs_lt, abs_lt, lt_div_iff₀ hmaxpos]
  constructor
  · rintro ⟨-, h3, h4⟩
    constructor
    · nlinarith
    · nlinarith
  · rintro ⟨h1, h2⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith

/-- **The optimal Richardson parameter** ([quarteroni2000numerical], (4.27); [saad2003iterative],
Example 4.1). Let $M$ be a real square matrix whose complex eigenvalues are real and lie in
$[\lambda_{\min}, \lambda_{\max}]$, where $\lambda_{\min}$ and $\lambda_{\max}$ are eigenvalues
of $M$ and $0 < \lambda_{\min}$. Then the parameter
$$\alpha_{\mathrm{opt}} = \frac{2}{\lambda_{\min} + \lambda_{\max}}$$
minimizes $\rho(I - \alpha M)$ over $\alpha > 0$.

The minimum value is `Stationary.Splitting.complexSpectralRadius_one_sub_smul_optimal_eq`. -/
theorem isMinOn_complexSpectralRadius_one_sub_smul {M : Matrix n n ℝ} {lmin lmax : ℝ}
    (hsub : spectrum ℂ (Matrix.complexify M) ⊆ Complex.ofReal '' Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ M) (hmax : lmax ∈ spectrum ℝ M) (hpos : 0 < lmin) :
    IsMinOn (fun α : ℝ => complexSpectralRadius (1 - α • M)) (Set.Ioi 0)
      (2 / (lmin + lmax)) := by
  have hle : lmin ≤ lmax := le_of_spectrum_subset hsub hmin
  have hsum : (0 : ℝ) < lmin + lmax := by linarith
  refine isMinOn_iff.2 fun α hα => ?_
  rw [complexSpectralRadius_one_sub_smul_eq hsub hmin hmax (ne_of_gt (div_pos two_pos hsum)),
    complexSpectralRadius_one_sub_smul_eq hsub hmin hmax (ne_of_gt hα),
    max_abs_one_sub_mul_optimal hpos hle]
  exact ENNReal.ofReal_le_ofReal (le_max_abs_one_sub_mul hpos hle α)

/-- **The optimal Richardson spectral radius** ([quarteroni2000numerical], (4.28)). Let $M$ be a
real square matrix whose complex eigenvalues are real and lie in
$[\lambda_{\min}, \lambda_{\max}]$, where $\lambda_{\min}$ and $\lambda_{\max}$ are eigenvalues
of $M$ and $0 < \lambda_{\min}$. Then
$$\rho\Bigl(I - \frac{2}{\lambda_{\min} + \lambda_{\max}} M\Bigr) = \frac{\lambda_{\max} -
  \lambda_{\min}}{\lambda_{\max} + \lambda_{\min}}.$$
-/
theorem complexSpectralRadius_one_sub_smul_optimal_eq {M : Matrix n n ℝ} {lmin lmax : ℝ}
    (hsub : spectrum ℂ (Matrix.complexify M) ⊆ Complex.ofReal '' Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ M) (hmax : lmax ∈ spectrum ℝ M) (hpos : 0 < lmin) :
    complexSpectralRadius (1 - (2 / (lmin + lmax)) • M)
      = ENNReal.ofReal ((lmax - lmin) / (lmax + lmin)) := by
  have hle : lmin ≤ lmax := le_of_spectrum_subset hsub hmin
  have hsum : (0 : ℝ) < lmin + lmax := by linarith
  rw [complexSpectralRadius_one_sub_smul_eq hsub hmin hmax (ne_of_gt (div_pos two_pos hsum)),
    max_abs_one_sub_mul_optimal hpos hle]

/-- If the real eigenvalues of a real symmetric matrix $A$ lie in
$[\lambda_{\min}, \lambda_{\max}]$, then its complex eigenvalues are real and lie in
$[\lambda_{\min}, \lambda_{\max}]$. -/
theorem _root_.Matrix.IsHermitian.spectrum_complexify_subset {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {lmin lmax : ℝ} (hsub : spectrum ℝ A ⊆ Set.Icc lmin lmax) :
    spectrum ℂ (Matrix.complexify A) ⊆ Complex.ofReal '' Set.Icc lmin lmax := by
  rw [hA.spectrum_complexify_eq]
  exact Set.image_mono hsub

/-- **The spectral radius of Richardson's iteration for a symmetric matrix** ([saad2003iterative],
Example 4.1). Let $A$ be a real symmetric matrix whose eigenvalues lie in
$[\lambda_{\min}, \lambda_{\max}]$, where $\lambda_{\min}$ and $\lambda_{\max}$ are eigenvalues
of $A$. Then for every real $\alpha \neq 0$, the iteration matrix $G_\alpha = I - \alpha A$ of
Richardson's splitting satisfies
$$\rho(G_\alpha) = \max\{|1 - \alpha \lambda_{\min}|, |1 - \alpha \lambda_{\max}|\}.$$

This is the symmetric case of `Stationary.Splitting.complexSpectralRadius_one_sub_smul_eq`. -/
theorem richardson_complexSpectralRadius_eq {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {lmin lmax : ℝ} (hsub : spectrum ℝ A ⊆ Set.Icc lmin lmax) (hmin : lmin ∈ spectrum ℝ A)
    (hmax : lmax ∈ spectrum ℝ A) {α : ℝ} (hα : α ≠ 0) :
    complexSpectralRadius (richardson A hα).iterationOperator
      = ENNReal.ofReal (max |1 - α * lmin| |1 - α * lmax|) := by
  rw [richardson_iterationOperator,
    complexSpectralRadius_one_sub_smul_eq (hA.spectrum_complexify_subset hsub) hmin hmax hα]

/-- Let $A$ be a real symmetric matrix whose eigenvalues lie in $[\lambda_{\min}, \lambda_{\max}]$,
where $\lambda_{\min}$ and $\lambda_{\max}$ are eigenvalues of $A$ and $0 < \lambda_{\min}$.
Then for every real $\alpha \neq 0$, Richardson's iteration with parameter $\alpha$ converges if
and only if $0 < \alpha < 2/\lambda_{\max}$ ([saad2003iterative], Example 4.1;
[han2009theoretical], Exercise 5.2.3). -/
theorem richardson_complexSpectralRadius_lt_one_iff {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {lmin lmax : ℝ} (hsub : spectrum ℝ A ⊆ Set.Icc lmin lmax) (hmin : lmin ∈ spectrum ℝ A)
    (hmax : lmax ∈ spectrum ℝ A) (hpos : 0 < lmin) {α : ℝ} (hα : α ≠ 0) :
    complexSpectralRadius (richardson A hα).iterationOperator < 1 ↔ 0 < α ∧ α < 2 / lmax := by
  rw [richardson_iterationOperator]
  exact complexSpectralRadius_one_sub_smul_lt_one_iff (hA.spectrum_complexify_subset hsub) hmin
    hmax hpos α

/-- **The optimal Richardson parameter for a symmetric positive definite matrix**
([saad2003iterative], Example 4.1). Let $A$ be a real symmetric matrix whose eigenvalues lie in
$[\lambda_{\min}, \lambda_{\max}]$, where $\lambda_{\min}$ and $\lambda_{\max}$ are eigenvalues
of $A$ and $0 < \lambda_{\min}$. Then $\alpha = 2/(\lambda_{\min} + \lambda_{\max})$ minimizes
$\rho(I - \alpha A)$ over $\alpha > 0$.

The iteration matrix of Richardson's splitting is $I - \alpha A$ by
`Stationary.Splitting.richardson_iterationOperator`. The minimum value is
`Stationary.Splitting.richardson_complexSpectralRadius_optimal_eq`. -/
theorem isMinOn_richardson_complexSpectralRadius {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {lmin lmax : ℝ} (hsub : spectrum ℝ A ⊆ Set.Icc lmin lmax) (hmin : lmin ∈ spectrum ℝ A)
    (hmax : lmax ∈ spectrum ℝ A) (hpos : 0 < lmin) :
    IsMinOn (fun α : ℝ => complexSpectralRadius (1 - α • A)) (Set.Ioi 0)
      (2 / (lmin + lmax)) :=
  isMinOn_complexSpectralRadius_one_sub_smul (hA.spectrum_complexify_subset hsub) hmin hmax hpos

/-- The optimal Richardson spectral radius for a symmetric positive definite matrix
([saad2003iterative], Example 4.1). Let $A$ be a real symmetric matrix whose eigenvalues lie in
$[\lambda_{\min}, \lambda_{\max}]$, where $\lambda_{\min}$ and $\lambda_{\max}$ are eigenvalues
of $A$ and $0 < \lambda_{\min}$. Then
$$\rho\Bigl(I - \frac{2}{\lambda_{\min} + \lambda_{\max}} A\Bigr) = \frac{\lambda_{\max} -
  \lambda_{\min}}{\lambda_{\max} + \lambda_{\min}}.$$

The right side is $1 - 2/(\kappa + 1)$, where $\kappa = \lambda_{\max}/\lambda_{\min}$ is the
condition number of $A$. -/
theorem richardson_complexSpectralRadius_optimal_eq {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {lmin lmax : ℝ} (hsub : spectrum ℝ A ⊆ Set.Icc lmin lmax) (hmin : lmin ∈ spectrum ℝ A)
    (hmax : lmax ∈ spectrum ℝ A) (hpos : 0 < lmin) :
    complexSpectralRadius (1 - (2 / (lmin + lmax)) • A)
      = ENNReal.ofReal ((lmax - lmin) / (lmax + lmin)) :=
  complexSpectralRadius_one_sub_smul_optimal_eq (hA.spectrum_complexify_subset hsub) hmin hmax hpos

end Splitting

end Stationary

/-! ### Jacobi over-relaxation, the SOR determinant, and Kahan's bound -/

namespace Matrix

open Stationary

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The optimal relaxation parameter of JOR** ([kress1998numerical], Theorem 4.9). Let $A$ be a
real square matrix with invertible diagonal, and let $G_J$ be its Jacobi iteration matrix.
Suppose that the complex eigenvalues of $G_J$ are real and lie in
$[\lambda_{\min}, \lambda_{\max}]$, where $\lambda_{\min}$ and $\lambda_{\max}$ are eigenvalues
of $G_J$, and that $\lambda_{\max} < 1$. Then the parameter
$$\omega_{\mathrm{opt}} = \frac{2}{2 - \lambda_{\max} - \lambda_{\min}}$$
minimizes $\rho((1 - \omega) I + \omega G_J)$ over $\omega > 0$.

Only $\lambda_{\max} < 1$ is used, which is half of the convergence of the Jacobi iteration. The
matrix $(1 - \omega) I + \omega G_J$ is the JOR iteration matrix by
`Matrix.jorSplitting_iterationOperator`. -/
theorem jorSplitting_isMinOn_complexSpectralRadius {A : Matrix n n ℝ} (h : IsUnit (diagPart A))
    {lmin lmax : ℝ}
    (hsub : spectrum ℂ (complexify (jacobiSplitting A h).iterationOperator) ⊆
      Complex.ofReal '' Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ (jacobiSplitting A h).iterationOperator)
    (hmax : lmax ∈ spectrum ℝ (jacobiSplitting A h).iterationOperator) (hlt : lmax < 1) :
    IsMinOn (fun ω : ℝ => complexSpectralRadius
        ((1 - ω) • 1 + ω • (jacobiSplitting A h).iterationOperator)) (Set.Ioi 0)
      (2 / (2 - lmax - lmin)) := by
  have hle : lmin ≤ lmax := le_of_spectrum_subset hsub hmin
  have ha : (0 : ℝ) < 1 - lmax := by linarith
  have hab : 1 - lmax ≤ 1 - lmin := by linarith
  have key : ∀ ω : ℝ, ω ≠ 0 →
      complexSpectralRadius ((1 - ω) • 1 + ω • (jacobiSplitting A h).iterationOperator)
        = ENNReal.ofReal (max |1 - ω * (1 - lmax)| |1 - ω * (1 - lmin)|) := by
    intro ω hω
    have e1 : 1 - ω + ω * lmin = 1 - ω * (1 - lmin) := by ring
    have e2 : 1 - ω + ω * lmax = 1 - ω * (1 - lmax) := by ring
    rw [complexSpectralRadius_affine hsub hmin hmax hω, e1, e2, max_comm]
  have hopt : (2 : ℝ) - lmax - lmin = 1 - lmax + (1 - lmin) := by ring
  have hoptpos : (0 : ℝ) < 2 / (2 - lmax - lmin) := div_pos two_pos (by linarith)
  refine isMinOn_iff.2 fun ω hω => ?_
  rw [key _ (ne_of_gt hoptpos), key _ (ne_of_gt hω), hopt,
    max_abs_one_sub_mul_optimal ha hab]
  exact ENNReal.ofReal_le_ofReal (le_max_abs_one_sub_mul ha hab ω)

variable [LinearOrder n]

/-- **The determinant of the SOR iteration matrix.** Let $A$ be an $n \times n$ matrix over a field
with invertible diagonal part $D$, and let $\omega \neq 0$. Then the SOR iteration matrix
$G_\omega$ satisfies
$$\det G_\omega = (1 - \omega)^n.$$

The matrix $G_\omega$ is the inverse of the lower triangular matrix $D + \omega L$, whose
diagonal is that of $A$, times the upper triangular matrix $(1 - \omega) D - \omega U$, whose
diagonal is $1 - \omega$ times that of $A$ ([kress1998numerical], proof of Theorem 4.11). -/
theorem det_sorSplitting_iterationOperator {𝕜 : Type*} [Field 𝕜] (A : Matrix n n 𝕜)
    (h : IsUnit (diagPart A)) {ω : 𝕜} (hω : ω ≠ 0) :
    (A.sorSplitting h hω).iterationOperator.det = (1 - ω) ^ Fintype.card n := by
  have hne : ∀ i, A i i ≠ 0 := (isUnit_diagPart_iff A).mp h
  have hprod : (∏ i, A i i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hne i
  have hL : (diagPart A + ω • strictLower A).IsLowerTriangular := by
    intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
    simp [hij'.ne, asymm hij']
  have hU : ((1 - ω) • diagPart A - ω • strictUpper A).IsUpperTriangular := by
    intro i j hij
    have hij' : j < i := hij
    simp [hij'.ne', asymm hij']
  rw [sorSplitting_iterationOperator, det_mul, det_nonsing_inv, Ring.inverse_eq_inv,
    det_of_isLowerTriangular _ hL, det_of_isUpperTriangular hU]
  have hLd : ∀ i, (diagPart A + ω • strictLower A) i i = A i i := fun i => by simp
  have hUd : ∀ i, ((1 - ω) • diagPart A - ω • strictUpper A) i i = (1 - ω) * A i i :=
    fun i => by simp
  simp only [hLd, hUd, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  field_simp

/-- **Kahan's necessary condition** ([kress1998numerical], Theorem 4.11). Let $A$ be a real
$n \times n$ matrix with $n \ge 1$ and invertible diagonal, and let $\omega \neq 0$. If the SOR
iteration matrix $G_\omega$ satisfies $\rho(G_\omega) < 1$, then
$$0 < \omega < 2.$$

The powers of $G_\omega$ tend to $0$, so its determinant $(1 - \omega)^n$ has modulus less than
$1$, and this forces $|1 - \omega| < 1$ when $n \ge 1$. -/
theorem lt_two_of_sorSplitting_complexSpectralRadius_lt_one [Nonempty n] {A : Matrix n n ℝ}
    (h : IsUnit (diagPart A)) {ω : ℝ} (hω : ω ≠ 0)
    (hρ : complexSpectralRadius (A.sorSplitting h hω).iterationOperator < 1) :
    0 < ω ∧ ω < 2 := by
  have hpow : Tendsto (fun k => (A.sorSplitting h hω).iterationOperator ^ k) atTop (𝓝 0) :=
    (tendsto_pow_iff_complexSpectralRadius_lt_one _).mpr hρ
  have hcont : Continuous fun M : Matrix n n ℝ => M.det := continuous_id.matrix_det
  have hdet := (hcont.tendsto 0).comp hpow
  rw [det_zero] at hdet
  simp only [Function.comp_def, det_pow, det_sorSplitting_iterationOperator,
    tendsto_pow_atTop_nhds_zero_iff, abs_pow] at hdet
  rw [pow_lt_one_iff_of_nonneg (abs_nonneg _) Fintype.card_ne_zero, abs_lt] at hdet
  exact ⟨by linarith [hdet.2], by linarith [hdet.1]⟩

/-- **The SOR matrix of a lower triangular matrix has the single eigenvalue $1 - \omega$.** Let $A$
be a real lower triangular $n \times n$ matrix with $n \ge 1$ and invertible diagonal, and let
$\omega \neq 0$. Then
$$\rho(G_\omega) = |1 - \omega|,$$
which is the case of equality in Kahan's bound.

Here $U = 0$, so $G_\omega = (D + \omega L)^{-1} (1 - \omega) D$ is lower triangular with
diagonal $1 - \omega$, and its characteristic polynomial is $(\lambda - (1 - \omega))^n$. -/
theorem complexSpectralRadius_sorSplitting_of_isLowerTriangular [Nonempty n] {A : Matrix n n ℝ}
    (hA : A.IsLowerTriangular) (h : IsUnit (diagPart A)) {ω : ℝ} (hω : ω ≠ 0) :
    complexSpectralRadius (sorSplitting A h hω).iterationOperator = ENNReal.ofReal |1 - ω| := by
  set M : Matrix n n ℝ := diagPart A + ω • strictLower A with hMdef
  set B := (sorSplitting A h hω).iterationOperator with hBdef
  have hd := (isUnit_diagPart_iff A).mp h
  have hU : strictUpper A = 0 := by
    ext i j
    rw [strictUpper_apply, Matrix.zero_apply]
    split_ifs with hij
    · exact hA (OrderDual.toDual_lt_toDual.mpr hij)
    · rfl
  have hMtri : M.IsLowerTriangular := by
    intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
    simp [hMdef, diagPart_apply, strictLower_apply, hij'.ne, asymm hij']
  have hMii : ∀ i, M i i = A i i := fun i => by simp [hMdef, diagPart_apply, strictLower_apply]
  have hMunit : IsUnit M := isUnit_diagPart_add_smul_strictLower h ω
  have hMinv : M⁻¹.IsLowerTriangular := hMtri.inv
  have hMinvii : ∀ i, M⁻¹ i i = (A i i)⁻¹ := fun i => by
    have h1 := hMinv.mul_apply_self hMtri i
    rw [nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hMunit), one_apply_eq, hMii] at h1
    exact eq_inv_of_mul_eq_one_left h1.symm
  have hDtri : ((1 - ω) • diagPart A).IsLowerTriangular := by
    rw [diagPart, ← diagonal_smul]
    exact blockTriangular_diagonal _
  have hB : B = M⁻¹ * ((1 - ω) • diagPart A) := by
    rw [hBdef, sorSplitting_iterationOperator, hU, smul_zero, sub_zero]
  have hBtri : B.IsLowerTriangular := by
    rw [hB]
    exact hMinv.mul hDtri
  have hBii : ∀ i, B i i = 1 - ω := fun i => by
    rw [hB, hMinv.mul_apply_self hDtri i, hMinvii]
    simp only [Matrix.smul_apply, diagPart_apply, ite_true, smul_eq_mul]
    rw [mul_comm (1 - ω), ← mul_assoc, inv_mul_cancel₀ (hd i), one_mul]
  have hchar : B.charpoly = (Polynomial.X - Polynomial.C (1 - ω)) ^ Fintype.card n := by
    rw [charpoly_of_isLowerTriangular B hBtri]
    simp only [hBii, Finset.prod_const, Finset.card_univ]
  refine complexSpectralRadius_eq_of_forall_mem_spectrum_iff fun μ => ?_
  rw [mem_spectrum_complexify_iff, hchar, Polynomial.IsRoot.def]
  simp only [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    pow_eq_zero_iff Fintype.card_ne_zero, sub_eq_zero]
  push_cast
  rfl

/-- Let $A$ be a real symmetric matrix with invertible diagonal part $D$, and let $\omega \neq 0$.
The SOR splitting $A = M - N$ satisfies
$$M + M^T - A = \Bigl(\frac{2}{\omega} - 1\Bigr) D.$$

The strictly lower part of $M$ and the strictly upper part of $M^T$ together give $A - D$. -/
theorem sorSplitting_m_add_transpose_sub {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (h : IsUnit (diagPart A)) {ω : ℝ} (hω : ω ≠ 0) :
    (A.sorSplitting h hω).m + ((A.sorSplitting h hω).m)ᵀ - A = (2 / ω - 1) • diagPart A := by
  have hm : (A.sorSplitting h hω).m = ω⁻¹ • diagPart A + strictLower A := rfl
  have hsymm : ∀ i j, A j i = A i j := fun i j => by
    have := congrFun (congrFun hA.eq i) j
    simpa using this
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hij
  · simp [hm, hij, hij.ne, hij.ne', asymm hij, hsymm i j]
  · have hMii : (A.sorSplitting h hω).m i i = ω⁻¹ * A i i := by simp [hm]
    have hlhs : ((A.sorSplitting h hω).m + ((A.sorSplitting h hω).m)ᵀ - A) i i
        = ω⁻¹ * A i i + ω⁻¹ * A i i - A i i := by
      rw [Matrix.sub_apply, Matrix.add_apply, transpose_apply, hMii]
    have hrhs : ((2 / ω - 1) • diagPart A) i i = (2 / ω - 1) * A i i := by simp
    rw [hlhs, hrhs, show (2 / ω - 1) = 2 * ω⁻¹ - 1 from by rw [div_eq_mul_inv]]
    ring
  · simp [hm, hij, hij.ne, hij.ne', asymm hij, hsymm j i]

/-- Let $A$ be a real symmetric matrix with positive diagonal entries, and let $0 < \omega < 2$.
Then the matrix $M + M^T - A = (2/\omega - 1) D$ of the SOR splitting is positive definite. -/
theorem sorSplitting_m_add_transpose_sub_posDef {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (hd : ∀ i, 0 < A i i) (h : IsUnit (diagPart A)) {ω : ℝ} (hω0 : 0 < ω) (hω2 : ω < 2) :
    ((A.sorSplitting h hω0.ne').m + ((A.sorSplitting h hω0.ne').m)ᵀ - A).PosDef := by
  rw [sorSplitting_m_add_transpose_sub hA h hω0.ne']
  have hcpos : 0 < 2 / ω - 1 := by
    rw [sub_pos, lt_div_iff₀ hω0]
    linarith
  have hdiag : (2 / ω - 1) • diagPart A = diagonal fun i => (2 / ω - 1) * A i i := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [hdiag, posDef_diagonal_iff]
  exact fun i => mul_pos hcpos (hd i)

/-- **The Ostrowski–Reich theorem for SOR** ([saad2003iterative], Theorem 4.10;
[kress1998numerical], Theorem 4.12). Let $A$ be a real symmetric matrix with positive diagonal
entries, and let $0 < \omega < 2$. Then the SOR iteration converges, $\rho(G_\omega) < 1$, if
and only if $A$ is positive definite.

The two directions are `Stationary.Splitting.complexSpectralRadius_lt_one_of_posDef` and
`Stationary.Splitting.posDef_of_complexSpectralRadius_lt_one`, with
$M + M^T - A = (2/\omega - 1) D$, which is positive definite because $0 < \omega < 2$. -/
theorem sorSplitting_complexSpectralRadius_lt_one_iff_posDef {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (hd : ∀ i, 0 < A i i) (h : IsUnit (diagPart A)) {ω : ℝ}
    (hω0 : 0 < ω) (hω2 : ω < 2) :
    complexSpectralRadius (A.sorSplitting h hω0.ne').iterationOperator < 1 ↔ A.PosDef :=
  ⟨Splitting.posDef_of_complexSpectralRadius_lt_one _ hA
      (sorSplitting_m_add_transpose_sub_posDef hA hd h hω0 hω2),
    fun hP => Splitting.complexSpectralRadius_lt_one_of_posDef _ hP
      (sorSplitting_m_add_transpose_sub_posDef hA hd h hω0 hω2)⟩

/-- **Ostrowski's theorem as the source states it** ([quarteroni2000numerical], Property 4.3). Let
$A$ be a real symmetric positive definite $n \times n$ matrix with $n \ge 1$, and let
$\omega \neq 0$. Then the SOR iteration converges if and only if
$$0 < \omega < 2.$$

The direction "if" is `Matrix.sorSplitting_complexSpectralRadius_lt_one_iff_posDef`. The
direction "only if" is Kahan's condition
`Matrix.lt_two_of_sorSplitting_complexSpectralRadius_lt_one`, which needs $n \ge 1$. The
invertibility of the diagonal is a hypothesis, although it follows from positive definiteness. -/
theorem sorSplitting_complexSpectralRadius_lt_one_iff [Nonempty n] {A : Matrix n n ℝ}
    (hA : A.PosDef) (h : IsUnit (diagPart A)) {ω : ℝ} (hω : ω ≠ 0) :
    complexSpectralRadius (sorSplitting A h hω).iterationOperator < 1 ↔ 0 < ω ∧ ω < 2 := by
  refine ⟨lt_two_of_sorSplitting_complexSpectralRadius_lt_one h hω, fun ⟨h0, h2⟩ => ?_⟩
  exact (sorSplitting_complexSpectralRadius_lt_one_iff_posDef hA.1 (fun i => hA.diag_pos) h h0
    h2).mpr hA

/-- **Gauss–Seidel converges for a positive definite matrix** ([quarteroni2000numerical], Theorem
4.5, the convergence clause). Let $A$ be a real symmetric positive definite matrix with
invertible diagonal. Then the Gauss–Seidel iteration matrix $G$ satisfies $\rho(G) < 1$.

This is SOR at $\omega = 1$. The monotonicity clause of the theorem is
`Stationary.Splitting.energyNorm_mulVec_iterationOperator_lt`. -/
theorem gaussSeidelSplitting_complexSpectralRadius_lt_one_of_posDef {A : Matrix n n ℝ}
    (hA : A.PosDef) (h : IsUnit (diagPart A)) :
    complexSpectralRadius (gaussSeidelSplitting A h).iterationOperator < 1 := by
  rw [← sorSplitting_one]
  exact (sorSplitting_complexSpectralRadius_lt_one_iff_posDef hA.1 (fun i => hA.diag_pos) h
    one_pos one_lt_two).mpr hA

omit [LinearOrder n] in
/-- **Jacobi converges when $A$ and $2D - A$ are positive definite** ([quarteroni2000numerical],
Theorem 4.3). Let $A$ be a real symmetric positive definite matrix with invertible diagonal part
$D$, and suppose that $2D - A$ is symmetric positive definite. Then the Jacobi iteration matrix
$G_J$ satisfies $\rho(G_J) < 1$.

This is the Householder–John theorem with $M = D$, for which $M + M^T - A = 2D - A$. -/
theorem jacobiSplitting_complexSpectralRadius_lt_one_of_posDef {A : Matrix n n ℝ} (hA : A.PosDef)
    (h2 : (2 • diagPart A - A).PosDef) (h : IsUnit (diagPart A)) :
    complexSpectralRadius (jacobiSplitting A h).iterationOperator < 1 := by
  refine Splitting.complexSpectralRadius_lt_one_of_posDef _ hA ?_
  have hm : (jacobiSplitting A h).m = diagPart A := rfl
  rw [hm, diagPart, diagonal_transpose, ← diagPart, ← two_smul ℕ (diagPart A)]
  exact h2

omit [LinearOrder n] in
/-- **JOR converges for $0 < \omega \le 1$ whenever Jacobi converges** ([quarteroni2000numerical],
Theorem 4.6). Let $A$ be a real square matrix with invertible diagonal whose Jacobi iteration
matrix $G_J$ satisfies $\rho(G_J) < 1$, and let $0 < \omega \le 1$. Then the JOR iteration
matrix with parameter $\omega$ has spectral radius less than $1$.

The JOR matrix $(1 - \omega) I + \omega G_J$ has spectral radius at most
$(1 - \omega) + \omega \rho(G_J) < 1$ (`Matrix.complexSpectralRadius_affine_lt_one`). -/
theorem jorSplitting_complexSpectralRadius_lt_one_of_le_one {A : Matrix n n ℝ}
    (h : IsUnit (diagPart A))
    (hJ : complexSpectralRadius (jacobiSplitting A h).iterationOperator < 1) {ω : ℝ}
    (hω0 : 0 < ω) (hω1 : ω ≤ 1) :
    complexSpectralRadius (jorSplitting A h hω0.ne').iterationOperator < 1 := by
  rw [jorSplitting_iterationOperator]
  exact complexSpectralRadius_affine_lt_one _ hω0 hω1 hJ


/-- **Kahan's bound** ([quarteroni2000numerical], Theorem 4.7). Let $A$ be a real $n \times n$
matrix with $n \ge 1$ and invertible diagonal, and let $\omega \neq 0$. Then the SOR iteration
matrix $G_\omega$ satisfies
$$|1 - \omega| \le \rho(G_\omega).$$

The determinant of $G_\omega$ is $(1 - \omega)^n$ (`Matrix.det_sorSplitting_iterationOperator`),
and it is the product of the $n$ complex eigenvalues, each of modulus at most $\rho(G_\omega)$.
The consequence $0 < \omega < 2$ for a convergent SOR iteration is
`Matrix.lt_two_of_sorSplitting_complexSpectralRadius_lt_one`. -/
theorem abs_one_sub_le_sorSplitting_complexSpectralRadius [Nonempty n] {A : Matrix n n ℝ}
    (h : IsUnit (diagPart A)) {ω : ℝ} (hω : ω ≠ 0) :
    ENNReal.ofReal |1 - ω| ≤ complexSpectralRadius (sorSplitting A h hω).iterationOperator := by
  set G := (sorSplitting A h hω).iterationOperator with hG
  set ρ := complexSpectralRadius G with hρ
  have hρtop : ρ ≠ ⊤ := complexSpectralRadius_ne_top G
  have hdet : (complexify G).det = (complexify G).charpoly.roots.prod :=
    det_eq_prod_roots_charpoly _
  have hcard : Multiset.card (complexify G).charpoly.roots = Fintype.card n := by
    rw [← (IsAlgClosed.splits (complexify G).charpoly).natDegree_eq_card_roots,
      charpoly_natDegree_eq_dim]
  have hle : ∀ μ ∈ (complexify G).charpoly.roots, ‖μ‖₊ ≤ ρ.toNNReal := by
    intro μ hμ
    have hmem : μ ∈ spectrum ℂ (complexify G) :=
      mem_spectrum_iff_isRoot_charpoly.mpr ((Polynomial.mem_roots (charpoly_monic _).ne_zero).mp hμ)
    have : (‖μ‖₊ : ℝ≥0∞) ≤ ρ := Matrix.nnnorm_le_complexSpectralRadius hmem
    rwa [← ENNReal.coe_toNNReal hρtop, ENNReal.coe_le_coe] at this
  have hprod : ‖(complexify G).det‖₊ ≤ ρ.toNNReal ^ Fintype.card n := by
    rw [hdet, ← nnnormHom_apply, map_multiset_prod]
    refine (Multiset.prod_le_pow_card (α := NNReal) _ ρ.toNNReal fun x hx => ?_).trans_eq ?_
    · obtain ⟨μ, hμ, rfl⟩ := Multiset.mem_map.mp hx
      exact hle μ hμ
    · rw [Multiset.card_map, hcard]
  rw [det_complexify, det_sorSplitting_iterationOperator, Complex.nnnorm_real, nnnorm_pow] at hprod
  have hcardne : Fintype.card n ≠ 0 := Fintype.card_ne_zero
  have h1 : ‖1 - ω‖₊ ≤ ρ.toNNReal :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) hcardne).mp hprod
  calc ENNReal.ofReal |1 - ω| = (‖1 - ω‖₊ : ℝ≥0∞) := by
        rw [← Real.norm_eq_abs, ofReal_norm, enorm_eq_nnnorm]
    _ ≤ (ρ.toNNReal : ℝ≥0∞) := ENNReal.coe_le_coe.mpr h1
    _ = ρ := ENNReal.coe_toNNReal hρtop

end Matrix


/-! ### The energy norms of a real matrix -/

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- For a real symmetric positive definite matrix $A$ and a real vector $e$, the energy norm of $e$,
viewed in `EuclideanSpace ℂ n`, for the operator of the complexification of $A$ satisfies
$\|e\|_A^2 = (A e) \cdot e$. -/
theorem energyNorm_toEuclideanCLM_complexify_sq {A : Matrix n n ℝ} (hA : A.PosDef) (e : n → ℝ) :
    energyNorm ((toEuclideanCLM (n := n) (𝕜 := ℂ) (complexify A) :
      EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n)
        (toEuclideanComplex e) ^ 2 = (A *ᵥ e) ⬝ᵥ e := by
  rw [hA.isSymmetricCoercive_toEuclideanCLM_complexify.energyNorm_sq, ContinuousLinearMap.coe_coe,
    re_inner_toEuclideanCLM_complexify_toEuclideanComplex]

end Matrix

namespace Stationary.Splitting

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (s : Splitting A)

/-- **Monotone convergence in the energy norm, for real matrices** ([quarteroni2000numerical],
Properties 4.1–4.2, and the monotonicity clauses of Theorem 4.5 and Property 4.3). Let
$A = M - N$ be a splitting of a real symmetric positive definite matrix $A$ such that
$M + M^T - A$ is symmetric positive definite. Then for every real vector $e \neq 0$,
$$(A G e) \cdot (G e) < (A e) \cdot e,$$
that is, $\|G e\|_A < \|e\|_A$. -/
theorem energyNorm_mulVec_iterationOperator_lt (hA : A.PosDef) (hQ : (s.m + s.mᵀ - A).PosDef)
    {e : n → ℝ} (he : e ≠ 0) :
    (A *ᵥ (s.iterationOperator *ᵥ e)) ⬝ᵥ (s.iterationOperator *ᵥ e) < (A *ᵥ e) ⬝ᵥ e := by
  have hA' := hA.isSymmetricCoercive_toEuclideanCLM_complexify
  have hQ' := hQ.isSymmetricCoercive_toEuclideanCLM_complexify.isCoercive
  rw [← euclidean_m_add_adjoint_sub] at hQ'
  have he' : toEuclideanComplex e ≠ 0 := fun h => he (toEuclideanComplex_eq_zero_iff.mp h)
  have h := energyNorm_iterationOperator_apply_lt s.euclidean hA' hQ' he'
  rw [euclidean_iterationOperator, toEuclideanCLM_complexify_toEuclideanComplex] at h
  have h2 := pow_lt_pow_left₀ h (energyNorm_nonneg _ _) two_ne_zero
  rwa [energyNorm_toEuclideanCLM_complexify_sq hA, energyNorm_toEuclideanCLM_complexify_sq hA] at h2

/-- **The uniform contraction in the energy norm bounds the spectral radius.** Let $A = M - N$ be a
splitting of a real symmetric positive definite matrix $A$ such that $M + M^T - A$ is symmetric
positive definite. Then there is $q < 1$ with $\rho(G) \le q$ and
$$(A G e) \cdot (G e) \le q^2 \, (A e) \cdot e$$
for every real vector $e$.

The bound $\|G\|_A \le q$ for the operator norm on the complex energy space
(`Stationary.Splitting.exists_energyNorm_iterationOperator_apply_le`) gives
$\rho(G) \le \|G\|_A \le q$, and the bound on real vectors follows. -/
theorem exists_complexSpectralRadius_le_and_energyNorm_mulVec_le (hA : A.PosDef)
    (hQ : (s.m + s.mᵀ - A).PosDef) :
    ∃ q : ℝ, q < 1 ∧ (complexSpectralRadius s.iterationOperator).toReal ≤ q ∧
      ∀ e : n → ℝ, (A *ᵥ (s.iterationOperator *ᵥ e)) ⬝ᵥ (s.iterationOperator *ᵥ e) ≤
        q ^ 2 * ((A *ᵥ e) ⬝ᵥ e) := by
  have hA' := hA.isSymmetricCoercive_toEuclideanCLM_complexify
  have hQ' := hQ.isSymmetricCoercive_toEuclideanCLM_complexify.isCoercive
  rw [← euclidean_m_add_adjoint_sub] at hQ'
  obtain ⟨q, hq1, hq⟩ := exists_energyNorm_iterationOperator_apply_le s.euclidean hA' hQ'
  set T := energyIterationOperator s.euclidean hA' with hT
  have hTle : ‖T‖ ≤ max q 0 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (le_max_right _ _) fun u => ?_
    obtain ⟨x, rfl⟩ := (WithEnergy.equiv _ hA').surjective u
    rw [hT, energyIterationOperator_apply, WithEnergy.norm_equiv, WithEnergy.norm_equiv]
    exact (hq x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (energyNorm_nonneg _ _))
  have hρ : (complexSpectralRadius s.iterationOperator).toReal ≤ max q 0 := by
    rw [← spectralRadius_euclidean_iterationOperator,
      ← spectralRadius_energyIterationOperator s.euclidean hA', ← hT]
    rcases subsingleton_or_nontrivial (WithEnergy _ hA') with hsub | hnt
    · have : Subsingleton (WithEnergy _ hA' →L[ℂ] WithEnergy _ hA') :=
        ⟨fun f g => by ext x; exact Subsingleton.elim _ _⟩
      rw [spectrum.SpectralRadius.of_subsingleton, ENNReal.toReal_zero]
      exact le_max_right _ _
    · refine le_trans ?_ hTle
      refine ENNReal.toReal_le_of_le_ofReal (norm_nonneg _) ?_
      rw [ofReal_norm, enorm_eq_nnnorm]
      exact spectralRadius_le_nnnorm T
  refine ⟨max q 0, max_lt hq1 zero_lt_one, hρ, fun e => ?_⟩
  have h := hq (toEuclideanComplex e)
  rw [euclidean_iterationOperator, toEuclideanCLM_complexify_toEuclideanComplex] at h
  have h' := h.trans (mul_le_mul_of_nonneg_right (le_max_left q 0) (energyNorm_nonneg _ _))
  have h2 := pow_le_pow_left₀ (energyNorm_nonneg _ _) h' 2
  rwa [energyNorm_toEuclideanCLM_complexify_sq hA, mul_pow,
    energyNorm_toEuclideanCLM_complexify_sq hA] at h2

/-- **The uniform contraction in the energy norm, for real matrices.** Let $A = M - N$ be a
splitting of a real symmetric positive definite matrix $A$ such that $M + M^T - A$ is symmetric
positive definite. Then there is $q < 1$ with
$$(A G e) \cdot (G e) \le q^2 \, (A e) \cdot e$$
for every real vector $e$.

This is the second half of
`Stationary.Splitting.exists_complexSpectralRadius_le_and_energyNorm_mulVec_le`. -/
theorem exists_energyNorm_mulVec_iterationOperator_le (hA : A.PosDef)
    (hQ : (s.m + s.mᵀ - A).PosDef) :
    ∃ q : ℝ, q < 1 ∧ ∀ e : n → ℝ, (A *ᵥ (s.iterationOperator *ᵥ e)) ⬝ᵥ (s.iterationOperator *ᵥ e)
      ≤ q ^ 2 * ((A *ᵥ e) ⬝ᵥ e) := by
  obtain ⟨q, hq1, -, hq⟩ := exists_complexSpectralRadius_le_and_energyNorm_mulVec_le s hA hQ
  exact ⟨q, hq1, hq⟩

/-- **The bound $\|G e\|_A \le \rho(G) \|e\|_A$ for real matrices** ([quarteroni2000numerical],
Property 4.1, and Corollary 4.1 in the generality of its closing remark). Let $A = M - N$ be a
splitting of a real symmetric positive definite matrix $A$ with $M$ symmetric. Then for every
real vector $e$,
$$(A G e) \cdot (G e) \le \rho(G)^2 \, (A e) \cdot e.$$

No hypothesis on $M^{-1} A$ is needed. -/
theorem energyNorm_mulVec_iterationOperator_le_complexSpectralRadius (hA : A.PosDef)
    (hM : s.m.IsHermitian) (e : n → ℝ) :
    (A *ᵥ (s.iterationOperator *ᵥ e)) ⬝ᵥ (s.iterationOperator *ᵥ e)
      ≤ (complexSpectralRadius s.iterationOperator).toReal ^ 2 * ((A *ᵥ e) ⬝ᵥ e) := by
  have hA' := hA.isSymmetricCoercive_toEuclideanCLM_complexify
  have hM' : (s.euclidean.m : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n).IsSymmetric := by
    rw [euclidean_m]
    exact hM.isSymmetric_toEuclideanCLM_complexify
  have h := energyNorm_iterationOperator_apply_le_spectralRadius s.euclidean hA' hM'
    (toEuclideanComplex e)
  rw [spectralRadius_euclidean_iterationOperator, euclidean_iterationOperator,
    toEuclideanCLM_complexify_toEuclideanComplex] at h
  have h2 := pow_le_pow_left₀ (energyNorm_nonneg _ _) h 2
  rwa [energyNorm_toEuclideanCLM_complexify_sq hA, mul_pow,
    energyNorm_toEuclideanCLM_complexify_sq hA] at h2

/-- **The bound $\|G e\|_M \le \rho(G) \|e\|_M$ for real matrices** ([quarteroni2000numerical],
Property 4.1, the clause for the norm of the preconditioner). Let $A = M - N$ be a splitting of
a real symmetric matrix $A$ with $M$ symmetric positive definite. Then for every real vector
$e$,
$$(M G e) \cdot (G e) \le \rho(G)^2 \, (M e) \cdot e.$$
-/
theorem energyNorm_m_mulVec_iterationOperator_le_complexSpectralRadius (hA : A.IsHermitian)
    (hM : s.m.PosDef) (e : n → ℝ) :
    (s.m *ᵥ (s.iterationOperator *ᵥ e)) ⬝ᵥ (s.iterationOperator *ᵥ e)
      ≤ (complexSpectralRadius s.iterationOperator).toReal ^ 2 * ((s.m *ᵥ e) ⬝ᵥ e) := by
  have hA' := hA.isSymmetric_toEuclideanCLM_complexify
  have hM' : (s.euclidean.m : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n).IsSymmetricCoercive := by
    rw [euclidean_m]
    exact hM.isSymmetricCoercive_toEuclideanCLM_complexify
  have h := norm_m_iterationOperator_apply_le_spectralRadius s.euclidean hA' hM'
    (toEuclideanComplex e)
  rw [spectralRadius_euclidean_iterationOperator, euclidean_iterationOperator,
    toEuclideanCLM_complexify_toEuclideanComplex, euclidean_m] at h
  have h2 := pow_le_pow_left₀ (energyNorm_nonneg _ _) h 2
  rwa [energyNorm_toEuclideanCLM_complexify_sq hM, mul_pow,
    energyNorm_toEuclideanCLM_complexify_sq hM] at h2

/-- Let $A = M - N$ be a splitting of a real symmetric positive definite $n \times n$ matrix $A$
with $n \ge 1$ and $M$ symmetric. Then the iteration matrix $G$ has a real eigenvector
$e \neq 0$ for a real eigenvalue $\mu$ with $|\mu| = \rho(G)$.

The matrix $G$ is self-adjoint for the inner product of $A$, so an eigenvalue of maximal modulus
is real, and a real eigenvalue of a real matrix has a real eigenvector. -/
theorem exists_mulVec_iterationOperator_eq_smul [Nonempty n] (hA : A.PosDef)
    (hM : s.m.IsHermitian) :
    ∃ e : n → ℝ, e ≠ 0 ∧ ∃ μ : ℝ, |μ| = (complexSpectralRadius s.iterationOperator).toReal ∧
      s.iterationOperator *ᵥ e = μ • e := by
  set G := s.iterationOperator with hG
  obtain ⟨μ, v, hv, hμv, hμρ⟩ := exists_eigenvector_norm_eq_complexSpectralRadius G
  have hμmem : μ ∈ spectrum ℂ (Matrix.complexify G) :=
    (mem_spectrum_iff_exists_mulVec_eq_smul _ _).mpr ⟨v, hv, hμv⟩
  have hA' := hA.isSymmetricCoercive_toEuclideanCLM_complexify
  have hM' : (s.euclidean.m : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n).IsSymmetric := by
    rw [euclidean_m]
    exact hM.isSymmetric_toEuclideanCLM_complexify
  have hsa := isSelfAdjoint_energyIterationOperator s.euclidean hA'
    (energyInner_iterationOperator_comm s.euclidean hA'.isSymmetric hM')
  have hμmem' : μ ∈ spectrum ℂ (energyIterationOperator s.euclidean hA') := by
    rw [spectrum_energyIterationOperator, euclidean_iterationOperator,
      AlgEquiv.spectrum_eq (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ))]
    exact hμmem
  have hreal : μ = (μ.re : ℂ) := hsa.mem_spectrum_eq_re hμmem'
  have hmemR : μ.re ∈ spectrum ℝ G := by
    rw [← ofReal_mem_spectrum_complexify_iff, ← hreal]
    exact hμmem
  rw [spectrum.mem_iff, isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    ← exists_mulVec_eq_zero_iff] at hmemR
  obtain ⟨e, he, hGe⟩ := hmemR
  rw [sub_mulVec, Algebra.algebraMap_eq_smul_one, smul_mulVec, one_mulVec, sub_eq_zero] at hGe
  refine ⟨e, he, μ.re, ?_, hGe.symm⟩
  rw [← hμρ, hreal, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]

/-- **The spectral radius is attained in the real energy norm** ([quarteroni2000numerical], Property
4.1, the equality $\rho(B) = \|B\|_A$ on real vectors). Let $A = M - N$ be a splitting of a real
symmetric positive definite $n \times n$ matrix $A$ with $n \ge 1$ and $M$ symmetric. Then some
real vector $e \neq 0$ satisfies
$$(A G e) \cdot (G e) = \rho(G)^2 \, (A e) \cdot e.$$

Such an $e$ is the real eigenvector of
`Stationary.Splitting.exists_mulVec_iterationOperator_eq_smul`. -/
theorem exists_energyNorm_mulVec_iterationOperator_eq_complexSpectralRadius [Nonempty n]
    (hA : A.PosDef) (hM : s.m.IsHermitian) :
    ∃ e : n → ℝ, e ≠ 0 ∧ (A *ᵥ (s.iterationOperator *ᵥ e)) ⬝ᵥ (s.iterationOperator *ᵥ e)
      = (complexSpectralRadius s.iterationOperator).toReal ^ 2 * ((A *ᵥ e) ⬝ᵥ e) := by
  obtain ⟨e, he, μ, hμ, hGe⟩ := s.exists_mulVec_iterationOperator_eq_smul hA hM
  refine ⟨e, he, ?_⟩
  rw [hGe, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← hμ, sq_abs]
  ring

end Stationary.Splitting


/-! ### The matrix $P^{-1} A$ and Jacobi over-relaxation for a positive definite matrix -/

namespace Matrix

open Stationary

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- A complex vector $z \neq 0$ has a nonzero real part or a nonzero imaginary part. -/
private theorem re_ne_zero_or_im_ne_zero {z : n → ℂ} (hz : z ≠ 0) :
    (fun i => (z i).re) ≠ 0 ∨ (fun i => (z i).im) ≠ 0 := by
  by_contra h
  rw [not_or, not_not, not_not] at h
  exact hz (funext fun i => Complex.ext (by simpa using congrFun h.1 i)
    (by simpa using congrFun h.2 i))

/-- For a real symmetric $A$ and a real symmetric positive definite $P$, every eigenvalue $\mu$ of
$P^{-1} A$ is the real number $(x \cdot A x + y \cdot A y)/(x \cdot P x + y \cdot P y)$ for the
real part $x$ and the imaginary part $y$ of an eigenvector. -/
private theorem exists_eq_div_of_mem_spectrum_inv_mul {A P : Matrix n n ℝ} (hA : A.IsHermitian)
    (hP : P.PosDef) {μ : ℂ} (hμ : μ ∈ spectrum ℂ (complexify (P⁻¹ * A))) :
    ∃ x y : n → ℝ, (x ≠ 0 ∨ y ≠ 0) ∧ 0 < x ⬝ᵥ (P *ᵥ x) + y ⬝ᵥ (P *ᵥ y) ∧
      μ = ((x ⬝ᵥ (A *ᵥ x) + y ⬝ᵥ (A *ᵥ y)) / (x ⬝ᵥ (P *ᵥ x) + y ⬝ᵥ (P *ᵥ y)) : ℝ) := by
  obtain ⟨z, hz, hAz⟩ := (mem_spectrum_inv_mul_iff_exists_mulVec_eq_smul A hP.isUnit μ).mp hμ
  have hform := congrArg (fun w => star z ⬝ᵥ w) hAz
  simp only [dotProduct_smul] at hform
  rw [star_dotProduct_complexify_mulVec_of_isHermitian hA,
    star_dotProduct_complexify_mulVec_of_isHermitian hP.1] at hform
  set x : n → ℝ := fun i => (z i).re
  set y : n → ℝ := fun i => (z i).im
  have hxy := re_ne_zero_or_im_ne_zero hz
  have hPx : 0 ≤ x ⬝ᵥ (P *ᵥ x) := by simpa using hP.posSemidef.dotProduct_mulVec_nonneg x
  have hPy : 0 ≤ y ⬝ᵥ (P *ᵥ y) := by simpa using hP.posSemidef.dotProduct_mulVec_nonneg y
  have hp : 0 < x ⬝ᵥ (P *ᵥ x) + y ⬝ᵥ (P *ᵥ y) := by
    rcases hxy with hx | hy
    · have := hP.dotProduct_mulVec_pos hx
      simp only [star_trivial] at this
      linarith
    · have := hP.dotProduct_mulVec_pos hy
      simp only [star_trivial] at this
      linarith
  refine ⟨x, y, hxy, hp, ?_⟩
  rw [Complex.ofReal_div, eq_div_iff (by exact_mod_cast hp.ne'), hform, smul_eq_mul, mul_comm]

/-- Let $A$ and $P$ be real symmetric positive definite matrices. Then every complex eigenvalue of
$P^{-1} A$ is a positive real number. -/
theorem exists_pos_ofReal_eq_of_mem_spectrum_inv_mul {A P : Matrix n n ℝ} (hA : A.PosDef)
    (hP : P.PosDef) {μ : ℂ} (hμ : μ ∈ spectrum ℂ (complexify (P⁻¹ * A))) :
    ∃ t : ℝ, 0 < t ∧ μ = t := by
  obtain ⟨x, y, hxy, hp, rfl⟩ := exists_eq_div_of_mem_spectrum_inv_mul hA.1 hP hμ
  refine ⟨_, div_pos ?_ hp, rfl⟩
  have hAx : 0 ≤ x ⬝ᵥ (A *ᵥ x) := by simpa using hA.posSemidef.dotProduct_mulVec_nonneg x
  have hAy : 0 ≤ y ⬝ᵥ (A *ᵥ y) := by simpa using hA.posSemidef.dotProduct_mulVec_nonneg y
  rcases hxy with hx | hy
  · have := hA.dotProduct_mulVec_pos hx
    simp only [star_trivial] at this
    linarith
  · have := hA.dotProduct_mulVec_pos hy
    simp only [star_trivial] at this
    linarith

/-- **The iteration matrix of a splitting that dominates $A$ has its eigenvalues in $[0, 1)$.** Let
$A = M - N$ be a splitting of a real symmetric positive definite matrix $A$ such that $M - A$ is
symmetric positive semidefinite, so that $M$ is symmetric positive definite. Then every complex
eigenvalue of $G = M^{-1} N$ is real and lies in $[0, 1)$.

This is Theorem 11.2.4 of [golub2013matrix] for the SSOR splitting, for which $M - A$ is
positive semidefinite by `Matrix.ssorSplitting_m_sub_posSemidef`. The proof writes
$G = I - M^{-1} A$. Every eigenvalue of $M^{-1} A$ is the quotient $(x \cdot A x + y \cdot A
y)/(x \cdot M x + y \cdot M y)$ for the real part $x$ and the imaginary part $y$ of an
eigenvector, and it lies in $(0, 1]$ because $0 < x \cdot A x \le x \cdot M x$. -/
theorem _root_.Stationary.Splitting.spectrum_complexify_iterationOperator_subset {A : Matrix n n ℝ}
    (s : Splitting A) (hA : A.PosDef) (hmA : (s.m - A).PosSemidef) :
    spectrum ℂ (complexify s.iterationOperator) ⊆ Complex.ofReal '' Set.Ico 0 1 := by
  have hM : s.m.PosDef := by
    simpa using hA.add_posSemidef hmA
  have hG : s.iterationOperator = (1 : ℝ) • 1 + (-1 : ℝ) • (s.m⁻¹ * A) := by
    rw [Splitting.iterationOperator, ← nonsing_inv_eq_ringInverse]
    module
  rw [hG, spectrum_complexify_affine _ (by norm_num : (-1 : ℝ) ≠ 0)]
  rintro _ ⟨μ, hμ, rfl⟩
  obtain ⟨x, y, hxy, hp, rfl⟩ := exists_eq_div_of_mem_spectrum_inv_mul hA.1 hM hμ
  have hAx : 0 ≤ x ⬝ᵥ (A *ᵥ x) := by simpa using hA.posSemidef.dotProduct_mulVec_nonneg x
  have hAy : 0 ≤ y ⬝ᵥ (A *ᵥ y) := by simpa using hA.posSemidef.dotProduct_mulVec_nonneg y
  have hApos : 0 < x ⬝ᵥ (A *ᵥ x) + y ⬝ᵥ (A *ᵥ y) := by
    rcases hxy with hx | hy
    · have := hA.dotProduct_mulVec_pos hx
      simp only [star_trivial] at this
      linarith
    · have := hA.dotProduct_mulVec_pos hy
      simp only [star_trivial] at this
      linarith
  have hdx : 0 ≤ x ⬝ᵥ ((s.m - A) *ᵥ x) := by simpa using hmA.dotProduct_mulVec_nonneg x
  have hdy : 0 ≤ y ⬝ᵥ ((s.m - A) *ᵥ y) := by simpa using hmA.dotProduct_mulVec_nonneg y
  rw [sub_mulVec, dotProduct_sub] at hdx hdy
  set a := x ⬝ᵥ (A *ᵥ x) + y ⬝ᵥ (A *ᵥ y)
  set b := x ⬝ᵥ (s.m *ᵥ x) + y ⬝ᵥ (s.m *ᵥ y)
  refine ⟨1 - a / b, ⟨?_, ?_⟩, ?_⟩
  · rw [sub_nonneg, div_le_one hp]
    linarith
  · have : 0 < a / b := div_pos hApos hp
    linarith
  · push_cast
    ring

omit [Fintype n] in
/-- The diagonal part of a real symmetric positive definite matrix is positive definite. -/
theorem _root_.Matrix.PosDef.diagPart {A : Matrix n n ℝ} (hA : A.PosDef) :
    (diagPart A).PosDef := by
  rw [Matrix.diagPart, posDef_diagonal_iff]
  exact fun i => hA.diag_pos

/-- **JOR converges for a positive definite matrix exactly for $0 < \omega < 2/\rho(D^{-1} A)$**
([quarteroni2000numerical], Theorem 4.4). Let $A$ be a real symmetric positive definite
$n \times n$ matrix with $n \ge 1$ and diagonal part $D$, and let $\omega \neq 0$. Then the JOR
iteration with parameter $\omega$ converges if and only if
$$0 < \omega < \frac{2}{\rho(D^{-1} A)}.$$

The JOR matrix is Richardson's $I - \omega D^{-1} A$
(`Matrix.jorSplitting_iterationOperator_eq_one_sub`). The eigenvalues of $D^{-1} A$ are real and
positive (`Matrix.exists_pos_ofReal_eq_of_mem_spectrum_inv_mul`), the largest of them is
$\rho(D^{-1} A)$, and $|1 - \omega t| < 1$ for an eigenvalue $t$ exactly when
$0 < \omega t < 2$. The hypothesis $n \ge 1$ is necessary: for $n = 0$ the left side holds and
the right side does not. -/
theorem jorSplitting_complexSpectralRadius_lt_one_iff_of_posDef [Nonempty n] {A : Matrix n n ℝ}
    (hA : A.PosDef) (h : IsUnit (diagPart A)) {ω : ℝ} (hω : ω ≠ 0) :
    complexSpectralRadius (jorSplitting A h hω).iterationOperator < 1 ↔
      0 < ω ∧ ω < 2 / (complexSpectralRadius ((diagPart A)⁻¹ * A)).toReal := by
  set M := (diagPart A)⁻¹ * A with hM
  have hpos : ∀ μ ∈ spectrum ℂ (complexify M), ∃ t : ℝ, 0 < t ∧ μ = t := fun μ hμ =>
    exists_pos_ofReal_eq_of_mem_spectrum_inv_mul hA hA.diagPart hμ
  obtain ⟨μ₀, v, hv, hμ₀v, hμ₀⟩ := exists_eigenvector_norm_eq_complexSpectralRadius M
  have hμ₀mem : μ₀ ∈ spectrum ℂ (complexify M) :=
    (mem_spectrum_iff_exists_mulVec_eq_smul _ _).mpr ⟨v, hv, hμ₀v⟩
  obtain ⟨t₀, ht₀, rfl⟩ := hpos μ₀ hμ₀mem
  have hρ : (complexSpectralRadius M).toReal = t₀ := by
    rw [← hμ₀, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht₀]
  have hle : ∀ t : ℝ, (t : ℂ) ∈ spectrum ℂ (complexify M) →
      t ≤ (complexSpectralRadius M).toReal := fun t ht => by
    have h1 : (‖(t : ℂ)‖₊ : ℝ≥0∞) ≤ complexSpectralRadius M :=
      Matrix.nnnorm_le_complexSpectralRadius ht
    have h2 := ENNReal.toReal_mono (complexSpectralRadius_ne_top M) h1
    rw [ENNReal.coe_toReal, coe_nnnorm, Complex.norm_real, Real.norm_eq_abs] at h2
    exact (le_abs_self t).trans h2
  have hnorm : ∀ t : ℝ, ‖((1 : ℝ) : ℂ) + ((-ω : ℝ) : ℂ) * (t : ℂ)‖ = |1 - ω * t| := by
    intro t
    rw [show ((1 : ℝ) : ℂ) + ((-ω : ℝ) : ℂ) * (t : ℂ) = ((1 - ω * t : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  have hspec : spectrum ℂ (complexify (1 - ω • M)) =
      (fun μ : ℂ => ((1 : ℝ) : ℂ) + ((-ω : ℝ) : ℂ) * μ) '' spectrum ℂ (complexify M) := by
    rw [← spectrum_complexify_affine M (neg_ne_zero.mpr hω)]
    congr 2
    module
  rw [jorSplitting_iterationOperator_eq_one_sub, complexSpectralRadius_lt_one_iff_forall_norm_lt,
    hspec]
  constructor
  · intro hall
    have h1 := hall _ ⟨_, hμ₀mem, rfl⟩
    rw [hnorm, abs_lt] at h1
    have hω0 : 0 < ω := by nlinarith
    refine ⟨hω0, ?_⟩
    rw [hρ, lt_div_iff₀ ht₀]
    linarith
  · rintro ⟨hω0, hω2⟩ μ ⟨ν, hν, rfl⟩
    obtain ⟨t, ht, rfl⟩ := hpos ν hν
    have htρ := hle t hν
    rw [hρ, lt_div_iff₀ ht₀] at hω2
    rw [hnorm, abs_lt]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left htρ hω0.le]
    · nlinarith

end Matrix

/-! ### The symmetric successive over-relaxation -/

namespace Matrix

open Stationary

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

section Parts

variable {𝕜 : Type*} [Field 𝕜]

omit [Fintype n] in
/-- For a symmetric square matrix $A$ over a field and every scalar $\omega$,
$(D + \omega L)^T = D + \omega U$, where $D$, $L$ and $U$ are the diagonal, the strictly lower
triangular and the strictly upper triangular parts of $A$. -/
theorem diagPart_add_smul_strictLower_transpose {A : Matrix n n 𝕜} (hA : A.IsSymm) (ω : 𝕜) :
    (diagPart A + ω • strictLower A)ᵀ = diagPart A + ω • strictUpper A := by
  rw [transpose_add, transpose_smul, diagPart_transpose, strictLower_transpose, hA.eq]

/-- **The SSOR preconditioner is symmetric** ([quarteroni2000numerical], (4.22), and (4.21) at
$\omega = 1$). Let $A$ be a symmetric square matrix over a field with invertible diagonal, and
let $\omega \notin \{0, 2\}$. Then the part $M = \frac{1}{\omega(2 - \omega)} (D + \omega L)
D^{-1} (D + \omega U)$ of the SSOR splitting is symmetric.

The reason is that $(D + \omega L)^T = D + \omega U$. -/
theorem ssorSplitting_m_isSymm {A : Matrix n n 𝕜} (hA : A.IsSymm) (h : IsUnit (diagPart A))
    {ω : 𝕜} (hω : ω ≠ 0) (hω2 : ω ≠ 2) : (ssorSplitting A h hω hω2).m.IsSymm := by
  have hU : (diagPart A + ω • strictUpper A)ᵀ = diagPart A + ω • strictLower A := by
    rw [← diagPart_add_smul_strictLower_transpose hA ω, transpose_transpose]
  change ((ω * (2 - ω))⁻¹ • ((diagPart A + ω • strictLower A) * (diagPart A)⁻¹ *
    (diagPart A + ω • strictUpper A)))ᵀ = (ω * (2 - ω))⁻¹ • ((diagPart A + ω • strictLower A) *
      (diagPart A)⁻¹ * (diagPart A + ω • strictUpper A))
  rw [transpose_smul, transpose_mul, transpose_mul, transpose_nonsing_inv, diagPart_transpose,
    hA.eq, hU, diagPart_add_smul_strictLower_transpose hA ω, Matrix.mul_assoc]

end Parts

variable {A : Matrix n n ℝ}

/-- **The SSOR preconditioner is positive definite** ([golub2013matrix], §11.2.7, after (11.2.24)).
Let $A$ be a real symmetric matrix with positive diagonal entries, not necessarily positive
definite, and let $0 < \omega < 2$. Then the part $M$ of the SSOR splitting is positive
definite.

The matrix $M$ is the positive multiple $(\omega (2 - \omega))^{-1}$ of $X D^{-1} X^T$, where
$D^{-1}$ is positive definite and $X = D + \omega L$ is invertible. -/
theorem ssorSplitting_m_posDef_of_diag_pos (hA : A.IsHermitian) (hd : ∀ i, 0 < A i i)
    (h : IsUnit (diagPart A)) {ω : ℝ} (hω0 : 0 < ω) (hω2 : ω < 2) :
    (ssorSplitting A h hω0.ne' hω2.ne).m.PosDef := by
  have hsymm : A.IsSymm := isHermitian_iff_isSymm.mp hA
  have hX : IsUnit (diagPart A + ω • strictLower A) := isUnit_diagPart_add_smul_strictLower h ω
  have hDi : (diagPart A)⁻¹.PosDef := by
    refine PosDef.inv ?_
    rw [diagPart, posDef_diagonal_iff]
    exact hd
  change ((ω * (2 - ω))⁻¹ • ((diagPart A + ω • strictLower A) * (diagPart A)⁻¹ *
    (diagPart A + ω • strictUpper A))).PosDef
  rw [← diagPart_add_smul_strictLower_transpose hsymm, ← conjTranspose_eq_transpose_of_trivial]
  refine PosDef.smul (hDi.mul_mul_conjTranspose_same ?_) ?_
  · exact (vecMul_injective_iff_isUnit).mpr hX
  · exact inv_pos.mpr (mul_pos hω0 (by linarith))

/-- **The SSOR preconditioner is positive definite** for a real symmetric positive definite matrix
$A$ and $0 < \omega < 2$.

This is the case of `Matrix.ssorSplitting_m_posDef_of_diag_pos` in which the diagonal is
positive because $A$ is positive definite. -/
theorem ssorSplitting_m_posDef (hA : A.PosDef) (h : IsUnit (diagPart A)) {ω : ℝ} (hω0 : 0 < ω)
    (hω2 : ω < 2) : (ssorSplitting A h hω0.ne' hω2.ne).m.PosDef :=
  ssorSplitting_m_posDef_of_diag_pos hA.1 (fun _ => hA.diag_pos) h hω0 hω2

/-- For real $a$, $b$, $(a D + b L) D^{-1} (a D + b U) = a^2 D + a b L + a b U + b^2 L D^{-1} U$. -/
private theorem expand_mul_inv_mul (h : IsUnit (diagPart A)) (a b : ℝ) :
    (a • diagPart A + b • strictLower A) * (diagPart A)⁻¹ * (a • diagPart A + b • strictUpper A)
      = (a * a) • diagPart A + (a * b) • strictLower A + (a * b) • strictUpper A
        + (b * b) • (strictLower A * (diagPart A)⁻¹ * strictUpper A) := by
  have hdet : IsUnit (diagPart A).det := (isUnit_iff_isUnit_det _).mp h
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hdet, nonsing_inv_mul _ hdet, Matrix.mul_one]
  module

/-- **The SSOR preconditioner dominates $A$.** Let $A$ be a real symmetric matrix with positive
diagonal entries, and let $0 < \omega < 2$. Then $P - A$ is positive semidefinite, where $P$ is
the part $m$ of the SSOR splitting.

The proof is the factorization
$$P - A = \frac{1}{\omega(2 - \omega)} \bigl((1 - \omega) D - \omega L\bigr) D^{-1} \bigl((1 -
  \omega) D - \omega U\bigr).$$
At $\omega = 1$ it reads $P_{SGS} - A = L D^{-1} U$. The inequality $P \ge A$ makes the SSOR
iteration matrix positive semidefinite for the inner product of $A$. -/
theorem ssorSplitting_m_sub_posSemidef (hA : A.IsHermitian) (hd : ∀ i, 0 < A i i)
    (h : IsUnit (diagPart A)) {ω : ℝ} (hω0 : 0 < ω) (hω2 : ω < 2) :
    ((ssorSplitting A h hω0.ne' hω2.ne).m - A).PosSemidef := by
  have hsymm : A.IsSymm := isHermitian_iff_isSymm.mp hA
  have hc : 0 < ω * (2 - ω) := mul_pos hω0 (by linarith)
  have hDi : (diagPart A)⁻¹.PosDef := by
    refine PosDef.inv ?_
    rw [diagPart, posDef_diagonal_iff]
    exact hd
  have hkey : (ssorSplitting A h hω0.ne' hω2.ne).m - A =
      (ω * (2 - ω))⁻¹ • (((1 - ω) • diagPart A - ω • strictLower A) * (diagPart A)⁻¹ *
        ((1 - ω) • diagPart A - ω • strictUpper A)) := by
    change (ω * (2 - ω))⁻¹ • ((diagPart A + ω • strictLower A) * (diagPart A)⁻¹ *
      (diagPart A + ω • strictUpper A)) - A = _
    have e1 := expand_mul_inv_mul h 1 ω
    have e2 := expand_mul_inv_mul h (1 - ω) (-ω)
    simp only [one_smul, neg_smul, ← sub_eq_add_neg] at e1 e2
    have hAeq : A = diagPart A + strictLower A + strictUpper A :=
      (diagPart_add_strictLower_add_strictUpper A).symm
    have hc' : (ω * (2 - ω))⁻¹ * (ω * (2 - ω)) = 1 := inv_mul_cancel₀ hc.ne'
    have hdiff : (diagPart A + ω • strictLower A) * (diagPart A)⁻¹ *
        (diagPart A + ω • strictUpper A) - ((1 - ω) • diagPart A - ω • strictLower A) *
          (diagPart A)⁻¹ * ((1 - ω) • diagPart A - ω • strictUpper A) = (ω * (2 - ω)) • A := by
      rw [e1, e2]
      conv_rhs => rw [hAeq]
      module
    calc (ω * (2 - ω))⁻¹ • ((diagPart A + ω • strictLower A) * (diagPart A)⁻¹ *
          (diagPart A + ω • strictUpper A)) - A
        = (ω * (2 - ω))⁻¹ • ((diagPart A + ω • strictLower A) * (diagPart A)⁻¹ *
            (diagPart A + ω • strictUpper A)) - (ω * (2 - ω))⁻¹ • ((ω * (2 - ω)) • A) := by
          rw [smul_smul, hc', one_smul]
      _ = _ := by rw [← smul_sub, ← hdiff, sub_sub_cancel]
  rw [hkey]
  have hYt : ((1 - ω) • diagPart A - ω • strictLower A)ᴴ
      = (1 - ω) • diagPart A - ω • strictUpper A := by
    rw [conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_smul, transpose_smul,
      diagPart_transpose, strictLower_transpose, hsymm.eq]
  rw [← hYt]
  exact (hDi.posSemidef.mul_mul_conjTranspose_same _).smul (inv_pos.mpr hc).le

/-- **SSOR converges for a positive definite matrix and $0 < \omega < 2$**
([quarteroni2000numerical], §4.2.6, and Property 4.5 at $\omega = 1$). Let $A$ be a real
symmetric positive definite matrix with invertible diagonal, and let $0 < \omega < 2$. Then the
SSOR iteration matrix $G$ satisfies $\rho(G) < 1$.

This is the Householder–John theorem with $M = P_{SSOR}$, for which $M + M^T - A = M + (M - A)$
is positive definite as the sum of a positive definite matrix (`Matrix.ssorSplitting_m_posDef`)
and a positive semidefinite one (`Matrix.ssorSplitting_m_sub_posSemidef`). -/
theorem ssorSplitting_complexSpectralRadius_lt_one (hA : A.PosDef) (h : IsUnit (diagPart A))
    {ω : ℝ} (hω0 : 0 < ω) (hω2 : ω < 2) :
    complexSpectralRadius (ssorSplitting A h hω0.ne' hω2.ne).iterationOperator < 1 := by
  refine Splitting.complexSpectralRadius_lt_one_of_posDef _ hA ?_
  have hsymm : A.IsSymm := isHermitian_iff_isSymm.mp hA.1
  rw [(ssorSplitting_m_isSymm hsymm h hω0.ne' hω2.ne).eq, add_sub_assoc]
  exact (ssorSplitting_m_posDef hA h hω0 hω2).add_posSemidef
    (ssorSplitting_m_sub_posSemidef hA.1 (fun i => hA.diag_pos) h hω0 hω2)

end Matrix

namespace Stationary.Splitting

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (s : Splitting A)

/-- For a splitting $A = M - N$ of a real square matrix with iteration matrix $G = I - M^{-1} A$,
$$A G = A - A M^{-1} A.$$
-/
theorem mul_iterationOperator_eq : A * s.iterationOperator = A - A * s.m⁻¹ * A := by
  rw [iterationOperator, Matrix.mul_sub, Matrix.mul_one, nonsing_inv_eq_ringInverse,
    Matrix.mul_assoc]

/-- **The iteration matrix is self-adjoint for the inner product of $A$.** Let $A = M - N$ be a
splitting of a real square matrix, with $A$ and $M$ symmetric. Then $A G$ is symmetric.

The reason is that $A G = A - A M^{-1} A$. -/
theorem mul_iterationOperator_isSymm (hA : A.IsSymm) (hm : s.m.IsSymm) :
    (A * s.iterationOperator).IsSymm := by
  rw [mul_iterationOperator_eq, IsSymm, transpose_sub, transpose_mul, transpose_mul,
    transpose_nonsing_inv, hA.eq, hm.eq, Matrix.mul_assoc]

/-- **The iteration matrix is positive semidefinite for the inner product of $A$.** Let $A = M - N$
be a splitting of a real symmetric positive definite matrix $A$, with $M$ symmetric and $M - A$
positive semidefinite. Then $A G$ is positive semidefinite.

With $y = M^{-1} A x$, one has $x \cdot A G x = x \cdot A x - y \cdot M y \ge (x - y) \cdot A
(x - y) \ge 0$, because $y \cdot A y \le y \cdot M y$ and $x \cdot A y = y \cdot M y$. -/
theorem mul_iterationOperator_posSemidef (hA : A.PosDef) (hm : s.m.IsSymm)
    (hsub : (s.m - A).PosSemidef) : (A * s.iterationOperator).PosSemidef := by
  have hsymm : A.IsSymm := isHermitian_iff_isSymm.mp hA.1
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    exact mul_iterationOperator_isSymm s hsymm hm
  · rw [star_trivial, mul_iterationOperator_eq, sub_mulVec, dotProduct_sub, ← mulVec_mulVec,
      ← mulVec_mulVec]
    set y := s.m⁻¹ *ᵥ (A *ᵥ x) with hy
    have hmy : s.m *ᵥ y = A *ᵥ x := mulVec_nonsing_inv_mulVec s.isUnit _
    have h1 : x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (s.m *ᵥ y) := by
      rw [hsymm.dotProduct_mulVec_comm, ← hmy]
    have h2 : 0 ≤ y ⬝ᵥ ((s.m - A) *ᵥ y) := by simpa using hsub.dotProduct_mulVec_nonneg y
    have h3 : 0 ≤ (x - y) ⬝ᵥ (A *ᵥ (x - y)) := by
      simpa using hA.posSemidef.dotProduct_mulVec_nonneg (x - y)
    rw [sub_mulVec, dotProduct_sub] at h2
    rw [mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct,
      hsymm.dotProduct_mulVec_comm (x := y) (y := x)] at h3
    linarith

end Stationary.Splitting

namespace Matrix

open Stationary

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n] {A : Matrix n n ℝ}

/-- **Property 4.5 of [quarteroni2000numerical], in its correct form.** Let $A$ be a real symmetric
positive definite matrix with invertible diagonal, and let $0 < \omega < 2$. Then the SSOR
iteration matrix $B_s(\omega)$ satisfies: $A B_s(\omega)$ is positive semidefinite. That is,
$B_s(\omega)$ is self-adjoint and positive semidefinite for the inner product of $A$, so its
eigenvalues are real and lie in $[0, 1)$. At $\omega = 1$ the matrix is $B_{SGS}$.

The source states that $B_{SGS}$ is symmetric positive definite. This is false as printed: for a
diagonal $A$, $B_{SGS} = 0$, and $B_{SGS}$ is in general not symmetric for the Euclidean inner
product. -/
theorem ssorSplitting_iterationOperator_posSemidef_energy (hA : A.PosDef) (h : IsUnit (diagPart A))
    {ω : ℝ} (hω0 : 0 < ω) (hω2 : ω < 2) :
    (A * (ssorSplitting A h hω0.ne' hω2.ne).iterationOperator).PosSemidef := by
  have hsymm : A.IsSymm := isHermitian_iff_isSymm.mp hA.1
  exact Splitting.mul_iterationOperator_posSemidef _ hA (ssorSplitting_m_isSymm hsymm h _ _)
    (ssorSplitting_m_sub_posSemidef hA.1 (fun i => hA.diag_pos) h hω0 hω2)

end Matrix
