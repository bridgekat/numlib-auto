/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Projection
import Numlib.LinearAlgebra.Eigenspace.Spectral
import Numlib.Analysis.InnerProductSpace.Projection.Gap
import Numlib.Analysis.Normed.Module.BestApprox
import Numlib.Analysis.Normed.Module.FiniteDimension
import Numlib.Eigen.MinMax
import Numlib.LinearAlgebra.Span.Basic

/-!
# The power method and subspace iteration

Let $A$ be an endomorphism of a normed space $E$ over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and
let $x_0 \in E$. The power iteration $q_{k+1} = A q_k / \|A q_k\|$ has the closed form
$q_k = \|A^k x_0\|^{-1} A^k x_0$ (`Krylov.powerIterate`). This module proves that the power
iteration converges to the dominant eigendirection ([saad2011numerical], Theorem 4.1;
[kress1998numerical], §7.2). It also proves the convergence of inverse iteration, which is the power
iteration of $(A - \sigma I)^{-1}$, and of subspace iteration, the block form that carries a whole
subspace along and captures as many dominant eigenvectors as the subspace has dimensions
([saad2011numerical], Theorem 5.2; [kress1998numerical], Lemma 7.18).

For a scalar $\mu$, let $G_\mu(A) = \{w : (A - \mu I)^N w = 0 \text{ for some } N\}$ be the maximal
generalized eigenspace. For a predicate $p$ on scalars, the spectral subspace
$G_p(A) = \sum_{p(\mu)} G_\mu(A)$ is the sum of the generalized eigenspaces of the selected scalars,
and $G_{\neq\lambda}(A)$ is the sum over the scalars $\mu \neq \lambda$. The main theorem is the
following. Write $x_0 = u + w$ with $Au = \lambda u$ and $w \in G_{\neq\lambda}(A)$. If
$\lambda \neq 0$ and every eigenvalue $\mu \neq \lambda$ satisfies $|\mu| < |\lambda|$, then
$\lambda^{-k} A^k x_0 \to u$, and the error is $O((r/|\lambda|)^k)$ for every $r$ above the moduli
of the other eigenvalues. This is the classical rate $|\lambda_2/\lambda_1|^k$, weakened to a strict
bound because a subdominant Jordan block contributes a polynomial factor. The normalized iterates
converge up to factors of modulus one, and their Rayleigh quotients $\langle q_k, A q_k \rangle$
converge to $\lambda$ ([quarteroni2000numerical], Theorem 5.6 and (5.28)). With an eigenbasis the
rate is exactly $(\rho/|\lambda|)^k$, where $\rho$ bounds the other eigenvalues, and for a symmetric
operator the Rayleigh quotient converges at the square of this rate.

## Main definitions

* `Krylov.powerIterate`: the power iterate $q_k = \|A^k x_0\|^{-1} A^k x_0$.
* `Module.End.IsStrictlyDominant`: $\lambda$ is strictly dominant for $A$ if every eigenvalue
  $\mu \neq \lambda$ of $A$ has $|\mu| < |\lambda|$.
* `Krylov.inverseIterate`: inverse iteration with shift $\sigma$, the power iteration of
  $(A - \sigma I)^{-1}$.
* `Krylov.subspaceIterate`: the $k$-th iterate $A^k S$ of subspace iteration from a subspace $S$.

## Main results

* `Krylov.exists_norm_pow_apply_le_of_mem_maxGenEigenspace`: a generalized eigenvector $w$ for $\mu$
  has $\|A^k w\| \le C r^k$ for every $r > |\mu|$.
* `Krylov.powerIterate_tendsto`: if $\lambda \neq 0$ is strictly dominant, $x_0 = u + w$,
  $Au = \lambda u$ and $w \in G_{\neq\lambda}(A)$, then $\lambda^{-k} A^k x_0 \to u$.
* `Krylov.exists_norm_inv_pow_smul_pow_apply_sub_le`: the error of $\lambda^{-k} A^k x_0$ is
  $O((r/|\lambda|)^k)$ for every $r$ above the moduli of the other eigenvalues.
* `Krylov.tendsto_smul_powerIterate`: for $u \neq 0$, $(|\lambda|/\lambda)^k q_k \to u/\|u\|$.
* `Krylov.exists_norm_eq_one_tendsto_smul_powerIterate`: the power iterates converge essentially to
  $u/\|u\|$.
* `Krylov.tendsto_norm_sub_smul_powerIterate`: the residual $\|A q_k - \lambda q_k\|$ tends to $0$.
* `Krylov.exists_eq_add_tendsto`: in finite dimension over $\mathbb{C}$, if $\lambda \neq 0$ is
  semi-simple and strictly dominant, then every $x_0$ splits as $u + w$ with
  $\lambda^{-k} A^k x_0 \to u$.
* `Krylov.tendsto_smul_inverseIterate`: inverse iteration converges essentially to an eigenvector of
  the eigenvalue that is strictly closest to the shift.
* `Krylov.tendsto_inner_powerIterate` and `Krylov.tendsto_inner_inverseIterate`: the Rayleigh
  quotients of the power iterates and of the inverse iterates converge to the eigenvalue.
* `Krylov.norm_inv_pow_smul_pow_apply_sub_le_of_eigenbasis`: with an eigenbasis, the error of the
  scaled iterate is at most $(\sum_{i \neq i_0} |\alpha_i/\alpha_{i_0}|) (\rho/|\lambda_{i_0}|)^k$
  ([quarteroni2000numerical], Theorem 5.6).
* `Krylov.exists_norm_sub_smul_powerIterate_le_of_eigenbasis` and
  `Krylov.exists_norm_inner_powerIterate_sub_le_of_eigenbasis`: with an eigenbasis, the
  eigendirection and the Rayleigh quotient converge at the rate $(\rho/|\lambda_{i_0}|)^k$
  ([golub2013matrix], (7.3.5) and the display before it).
* `Krylov.sinAngle_powerIterate_le_of_eigenbasis`: with an orthonormal eigenbasis, $\sin\theta_k \le
  \tan\theta_0 \, (\rho/|\lambda_{i_0}|)^k$ ([golub2013matrix], Theorem 8.2.1, (8.2.4)).
* `Krylov.abs_sub_rayleigh_powerIterate_le_of_eigenbasis`: with an orthonormal eigenbasis and real
  eigenvalues, the Rayleigh quotient has error at most $\max_{i \neq i_0} |\lambda_{i_0} -
  \lambda_i| \tan^2\theta_0 \, (\rho/|\lambda_{i_0}|)^{2k}$ ([golub2013matrix], Theorem 8.2.1,
  (8.2.5)).
* `LinearMap.IsSymmetric.abs_sub_rayleigh_powerIterate_le`: for a symmetric operator with
  eigenvalues in $[a, b]$, the Rayleigh quotient has error at most $(b - a) \tan^2\theta_0 \,
  (\rho/|\lambda_{i_0}|)^{2k}$ ([quarteroni2000numerical], (5.23)).
* `Krylov.powerIterate_conj_linearIsometryEquiv` and
  `Krylov.inverseIterate_conj_linearIsometryEquiv`: both iterations commute with a change of
  orthonormal coordinates, so they may be run on a Hessenberg or tridiagonal form
  ([quarteroni2000numerical], §5.8.1).
* `Krylov.norm_sub_starProjection_subspaceIterate_le`: if $Au = \lambda u$, $s \in S$ and
  $\|A^k (s - u)\| \le C r^k$, then $\|u - P_{A^k S} u\| \le C (r/|\lambda|)^k$.
* `Krylov.exists_norm_sub_starProjection_subspaceIterate_le` and
  `Krylov.tendsto_starProjection_subspaceIterate`: the convergence of subspace iteration to each
  dominant eigenvector ([saad2011numerical], Theorem 5.2).
* `Krylov.gap_subspaceIterate_le`, `Krylov.exists_gap_subspaceIterate_le` and
  `Krylov.exists_gap_subspaceIterate_span_image_le`: the gap between the dominant invariant subspace
  and $A^k S$ is $O((r/\rho)^k)$ ([kress1998numerical], Lemma 7.18).

## Proof outline

The decay of the subdominant part is `Krylov.exists_norm_pow_apply_le_of_mem_maxGenEigenspace`: if
$(A - \mu I)^N w = 0$ and $|\mu| < r$, then $\|A^k w\| \le C r^k$, by induction on $N$ from the
scalar recursion $a_{k+1} \le |\mu| a_k + C r^k$. Since
$\lambda^{-k} A^k x_0 - u = \lambda^{-k} A^k w$, this gives the convergence of the power method. For
subspace iteration, the single candidate $\lambda^{-k} A^k s \in A^k S$ proves the bound: the
orthogonal projection is the best approximation from $A^k S$, and the error of the candidate is
$\lambda^{-k} A^k (s - u)$. The gap form follows from `Submodule.gap_le_of_forall_norm_sub_le`: the
scaled iterates $\lambda_j^{-k} A^k s_j$ span $A^k S$ and converge to the eigenvectors $x_j$ one at
a time, and the gap is small because the whole family converges at once.

## Implementation notes

* The main theorems need no finite dimension and no algebraically closed field. These enter only
  through `Krylov.exists_eq_add_mem_maxGenEigenspace`, which splits every $x_0$ as $u + w$, and are
  packaged in `Krylov.exists_eq_add_tendsto`.
* Semi-simplicity is local to $x_0$. The cited sources assume that the dominant eigenvalue $\lambda$
  is semi-simple, that is, that its generalized eigenspace is its eigenspace. The proof uses only
  that the $\lambda$-component of this particular $x_0$ is an eigenvector, the hypothesis
  $Au = \lambda u$. Semi-simplicity gives this for every $x_0$, and it is the hypothesis of
  `Krylov.exists_eq_add_tendsto`. A simple eigenvalue is semi-simple by
  `Krylov.maxGenEigenspace_eq_eigenspace_of_finrank_eq_one`.
* No Jordan form and no Gelfand formula is used. The proofs never compute the spectrum of a
  restriction of $A$, $E$ need not be complete, and $A$ need not be continuous, except in the
  statements about residuals and Rayleigh quotients.
* `Krylov.powerIterate` normalizes by a norm. So it is unchanged by a positive rescaling of $x_0$
  (`Krylov.powerIterate_ofReal_smul`), and it satisfies the normalize-at-every-step recurrence
  exactly, with no scalar left over (`Krylov.powerIterate_succ`;
  `Krylov.eq_powerIterate_of_recurrence` is the converse). With the Lean convention $0^{-1} = 0$ the
  definition is total: the degenerate case $A^k x_0 = 0$ gives $q_k = 0$, and no statement has to
  exclude it.
* A norm-normalized iterate does not converge in general, because each step multiplies the
  eigendirection by the scalar $\lambda/|\lambda|$ of modulus one. The algorithm of
  [saad2011numerical] avoids this by dividing by the entry of largest modulus, which is a complex
  scalar. For the general case the source says that $x_k$ **converges essentially** to $x$ if
  $c_k x_k \to x$ for some scalars $c_k$ of modulus one. This is what holds here, with an explicit
  sequence: `Krylov.tendsto_smul_powerIterate` divides out $(\lambda/|\lambda|)^k$, and
  `Krylov.exists_norm_eq_one_tendsto_smul_powerIterate` is the existential form. The alternative
  without phases is `Krylov.tendsto_norm_sub_smul_powerIterate`: the residual
  $\|A q_k - \lambda q_k\|$ tends to $0$, so the iterates are approximate eigenvectors for
  $\lambda$. A factor of modulus one does not change a Rayleigh quotient
  $\langle q_k, A q_k \rangle$.
* The constant $\sum_{i \neq i_0} |\alpha_i/\alpha_{i_0}|$ of
  `Krylov.norm_inv_pow_smul_pow_apply_sub_le_of_eigenbasis` is the one that the triangle inequality
  gives. The constant $(\sum_i (\alpha_i/\alpha_1)^2)^{1/2}$ of [quarteroni2000numerical], Theorem
  5.6, needs an orthonormal eigenbasis. The two bounds of [golub2013matrix], Theorem 8.2.1, are
  stated for an arbitrary orthonormal eigenbasis, so that a given Schur decomposition applies
  without matching it to `LinearMap.IsSymmetric.eigenvectorBasis`. The form with the spread $b - a$
  of the spectrum, `LinearMap.IsSymmetric.abs_sub_rayleigh_powerIterate_le`, is a corollary of the
  bound with the constant $\max_{i \neq i_0} |\lambda_{i_0} - \lambda_i|$.
* `Krylov.inverseIterate A σ x₀ k` is the power method for $(A - \sigma I)^{-1}$, the
  shift-and-invert iteration of [saad2011numerical], §4.1.2–4.1.3. The map
  $\mu \mapsto (\mu - \sigma)^{-1}$ makes the eigenvalue of $A$ nearest the shift the dominant one.
  So `Krylov.tendsto_smul_inverseIterate` has a hypothesis about distances to $\sigma$ instead of
  moduli, and its rate $(|\lambda - \sigma|/|\mu_2 - \sigma|)^k$ is fast for a shift close to
  $\lambda$. The inverse is `Ring.inverse`, so `Krylov.inverseIterate` is total, and the
  invertibility of $A - \sigma I$ (in finite dimension: $\sigma$ is not an eigenvalue) is a
  hypothesis of the theorems, not of the definition.
* The spectral correspondence for inverse iteration is proved directly, without a spectral mapping
  theorem. An eigenvector of $A$ for $\mu \neq \sigma$ is an eigenvector of the shifted inverse for
  $(\mu - \sigma)^{-1}$ (`Krylov.inverse_apply_eq_smul`). A generalized eigenvector is one too, of
  the same index (`Krylov.maxGenEigenspace_le_maxGenEigenspace_inverse`), by the factorization $(A -
  \sigma I)^{-1} - (\mu - \sigma)^{-1} I = -(\mu - \sigma)^{-1} (A - \sigma I)^{-1} (A - \mu I)$
  into commuting factors. Every eigenvalue of the shifted inverse arises in this way
  (`Krylov.hasEigenvalue_of_hasEigenvalue_inverse`).
* Rayleigh quotient iteration updates the shift at every step to the Rayleigh quotient of the
  current vector. [saad2011numerical] describes it without a theorem. It is
  `Krylov.rayleighQuotientIterate` in `Numlib.Eigen.RayleighQuotientIteration`, with its local
  quadratic convergence at a simple eigenvalue of a nonsymmetric operator
  (`Krylov.norm_rayleighQuotientIterate_sub_le`).
* `Krylov.subspaceIterate A S k` is $A^k S$. Bauer's Treppeniteration reorthonormalizes its block of
  vectors at every step. This replaces the basis but not the subspace that it spans, so in closed
  form the $k$-th iterate is again a power of $A$ applied to the starting data. What converges is
  the subspace. The theorem of [saad2011numerical], Theorem 5.2, measures the distance
  $\|u - P_{S_k} u\|$ from a dominant eigenvector $u$ to the iterate $S_k$, where $P_{S_k}$ is the
  orthogonal projection onto $S_k$. It is not a statement about a gap between subspaces. Its rate
  $(|\lambda_{m+1}/\lambda_i| + \varepsilon_k)^k$ becomes $C (r/|\lambda|)^k$ for every $r$ above
  the moduli of the unselected eigenvalues. This is the same trade as for the power method: a
  constant in place of a vanishing perturbation of the base of the power.
* The gap of `Numlib.Analysis.InnerProductSpace.Projection.Gap` gives more than the bounds for
  single eigenvectors: `Submodule.sinAngle_le_gap` turns a bound on $\operatorname{gap}(M, S_k)$
  into the same distance bound for every vector of the dominant invariant subspace $M$. That
  stronger statement is [kress1998numerical], Lemma 7.18, and it is `Krylov.gap_subspaceIterate_le`,
  with `Krylov.exists_gap_subspaceIterate_le` as its spectral form. There $M$ must be spanned by
  eigenvectors, which is the diagonalizability of [kress1998numerical]. A Jordan block among the
  selected eigenvalues costs a polynomial factor and breaks the rate $(r/\rho)^k$. For a symmetric
  operator the constant is explicit, $\operatorname{gap}(D, A^k S) \le (r/\rho)^k d_0/\sqrt{1 -
  d_0^2}$ ([golub2013matrix], Theorem 8.2.2). That is `LinearMap.IsSymmetric.gap_subspaceIterate_le`
  in `Numlib.Eigen.InvariantSubspace`, next to the nonsymmetric Theorem 7.3.1 of [golub2013matrix],
  with which it shares the graph transport.
* The projector onto the invariant subspace of the selected eigenvalues turns the starting subspace
  $S$ into the data that the bound needs. `Module.End.isCompl_spectralSubspace` splits $E$ as
  $M \oplus W$, with $M = G_p(A)$ and $W = G_{\neg p}(A)$, and `Module.End.spectralProjector` is the
  resulting oblique projection, `Submodule.projection` of that decomposition.
  `Submodule.starProjection` is the wrong object here, because the splitting is not orthogonal
  unless $A$ is normal. The kernel of the projector is $W$. So the hypothesis of the source that the
  projections of a basis of $S$ are linearly independent is `Disjoint S W`
  (`Module.End.injOn_spectralProjector_iff`), and if moreover $\dim S = \dim M$, every $u \in M$ is
  the projection of exactly one $s \in S$ (`Module.End.existsUnique_mem_spectralProjector_eq`).
* In Lean the eigenvalue $\lambda$ is `l`, and the modulus $|\mu|$ of a scalar is its norm. The
  Rayleigh quotient $\langle q, A q \rangle$ is `inner 𝕜 q (A q)`; the inner product is
  conjugate-linear in its first argument.
-/

open Filter Topology

/-- Let $R$ be a commutative semiring, let $M$ and $M_2$ be $R$-modules, let $e : M \to M_2$ be a
linear equivalence and let $A$ be an endomorphism of $M$. Conjugation by $e$ commutes with the
ring inverse: $$e \, A^{-1} e^{-1} = (e A e^{-1})^{-1},$$ where $A^{-1}$ is `Ring.inverse A`,
the inverse of $A$ if $A$ is invertible and $0$ otherwise.

Conjugation by $e$ is the ring isomorphism `LinearEquiv.conjRingEquiv`. So it carries invertible
elements to invertible elements and the inverse of an element to the inverse of its image, and
both sides are $0$ for an element that is not invertible. The fact holds for `Ring.inverse` and
every ring isomorphism, and it would belong in `Mathlib.Algebra.Module.Equiv.Basic`. -/
theorem LinearEquiv.conj_ringInverse {R M M₂ : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] [AddCommMonoid M₂] [Module R M₂] (e : M ≃ₗ[R] M₂) (A : Module.End R M) :
    e.conj (Ring.inverse A) = Ring.inverse (e.conj A) := by
  have hmul : ∀ f g : Module.End R M, e.conj (f * g) = e.conj f * e.conj g := fun f g =>
    LinearEquiv.conj_comp e g f
  have hone : e.conj 1 = 1 := LinearEquiv.conj_id e
  have hconj : ∀ f, e.conjRingEquiv f = e.conj f := fun f => rfl
  by_cases hA : IsUnit A
  · have h1 : e.conj A * e.conj (Ring.inverse A) = 1 := by
      rw [← hmul, Ring.mul_inverse_cancel _ hA, hone]
    have h2 : e.conj (Ring.inverse A) * e.conj A = 1 := by
      rw [← hmul, Ring.inverse_mul_cancel _ hA, hone]
    exact (Ring.inverse_unit ⟨e.conj A, e.conj (Ring.inverse A), h1, h2⟩).symm
  · have hB : ¬ IsUnit (e.conj A) := fun h => by
      have := h.map e.conjRingEquiv.symm
      rw [← hconj, RingEquiv.symm_apply_apply] at this
      exact hA this
    rw [Ring.inverse_non_unit _ hA, Ring.inverse_non_unit _ hB, map_zero]

namespace Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-! ### The power iteration -/

/-- The **power iteration** in closed form. Let $A$ be an endomorphism of a normed space $E$ over
$\mathbb{K}$, let $x_0 \in E$ and $k \in \mathbb{N}$. The $k$-th power iterate is $$q_k = \|A^k
x_0\|^{-1} A^k x_0.$$ This is the iteration $q_{k+1} = A q_k / \|A q_k\|$, started at
$\|x_0\|^{-1} x_0$ (`Krylov.powerIterate_succ`).

The scalar is $\|A^k x_0\|^{-1}$ with the Lean convention $0^{-1} = 0$. So the definition is
total and gives $q_k = 0$ when $A^k x_0 = 0$, and no statement about the iterates needs a
hypothesis that excludes this case. -/
noncomputable def powerIterate (A : Module.End 𝕜 E) (x₀ : E) (k : ℕ) : E :=
  (‖(A ^ k) x₀‖ : 𝕜)⁻¹ • (A ^ k) x₀

variable (A : Module.End 𝕜 E) (x₀ : E) (k : ℕ)

/-- The power iteration starts at the normalized starting vector: $q_0 = \|x_0\|^{-1} x_0$. -/
@[simp]
theorem powerIterate_zero : powerIterate A x₀ 0 = (‖x₀‖ : 𝕜)⁻¹ • x₀ := by
  simp [powerIterate]

/-- The $k$-th power iterate is the scalar multiple $q_k = \|A^k x_0\|^{-1} A^k x_0$ of $A^k x_0$.

Hence $q_k$ spans the same line as $A^k x_0$ (or is $0$), and it lies in the Krylov subspace
$\mathcal{K}_{k+1}(A, x_0)$. -/
theorem powerIterate_eq_smul :
    powerIterate A x₀ k = (‖(A ^ k) x₀‖ : 𝕜)⁻¹ • (A ^ k) x₀ := rfl

/-- The power iterate vanishes exactly in the degenerate case: $q_k = 0$ if and only if
$A^k x_0 = 0$. -/
theorem powerIterate_eq_zero_iff : powerIterate A x₀ k = 0 ↔ (A ^ k) x₀ = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [powerIterate, h]⟩
  by_contra hne
  rw [powerIterate, smul_eq_zero, inv_eq_zero, RCLike.ofReal_eq_zero, norm_eq_zero] at h
  exact h.elim hne hne

/-- If $A^k x_0 \neq 0$, then the power iterate $q_k$ is a unit vector: $\|q_k\| = 1$. -/
theorem norm_powerIterate_of_ne_zero (h : (A ^ k) x₀ ≠ 0) : ‖powerIterate A x₀ k‖ = 1 := by
  rw [powerIterate, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]

/-- Every power iterate satisfies $\|q_k\| \le 1$, with equality unless $A^k x_0 = 0$. -/
theorem norm_powerIterate_le_one : ‖powerIterate A x₀ k‖ ≤ 1 := by
  rcases eq_or_ne ((A ^ k) x₀) 0 with h | h
  · simp [(powerIterate_eq_zero_iff A x₀ k).mpr h]
  · exact (norm_powerIterate_of_ne_zero A x₀ k h).le

/-- Rescaling the starting vector by a scalar $c$ multiplies every power iterate by the phase of
$c$: $$q_k(c x_0) = \frac{c}{|c|} \, q_k(x_0),$$ where $c/|c|$ means $0$ for $c = 0$. -/
theorem powerIterate_smul (c : 𝕜) :
    powerIterate A (c • x₀) k = ((‖c‖ : 𝕜)⁻¹ * c) • powerIterate A x₀ k := by
  rw [powerIterate, powerIterate, map_smul, norm_smul, smul_smul, smul_smul]
  push_cast
  rw [mul_inv]
  congr 1
  ring

/-- Let $c > 0$ be real. The power iterates from $c x_0$ are the power iterates from $x_0$:
$q_k(c x_0) = q_k(x_0)$ for every $k$. -/
theorem powerIterate_ofReal_smul {c : ℝ} (hc : 0 < c) :
    powerIterate A ((c : 𝕜) • x₀) k = powerIterate A x₀ k := by
  rw [powerIterate_smul, RCLike.norm_ofReal, abs_of_pos hc,
    inv_mul_cancel₀ (RCLike.ofReal_ne_zero.mpr hc.ne'), one_smul]

/-- The power iterates satisfy the normalize-at-every-step recurrence exactly: $$q_{k+1} = \|A
q_k\|^{-1} A q_k,$$ with $0^{-1} = 0$.

No positive scalar is left over, because the normalization divides by a norm and not by a
coordinate. -/
theorem powerIterate_succ :
    powerIterate A x₀ (k + 1) =
      (‖A (powerIterate A x₀ k)‖ : 𝕜)⁻¹ • A (powerIterate A x₀ k) := by
  have hA : A ((A ^ k) x₀) = (A ^ (k + 1)) x₀ := by rw [pow_succ', Module.End.mul_apply]
  rcases eq_or_ne ((A ^ k) x₀) 0 with h | h
  · have h1 : (A ^ (k + 1)) x₀ = 0 := by rw [← hA, h, map_zero]
    simp [powerIterate, h, h1]
  · have ht : (0 : ℝ) < ‖(A ^ k) x₀‖ := norm_pos_iff.mpr h
    have hx : A (powerIterate A x₀ k) = (‖(A ^ k) x₀‖ : 𝕜)⁻¹ • (A ^ (k + 1)) x₀ := by
      rw [powerIterate, map_smul, hA]
    rw [hx, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos ht, smul_smul, powerIterate]
    congr 1
    have hne : (‖(A ^ k) x₀‖ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr ht.ne'
    push_cast
    field_simp

/-- The power iteration is determined by its recurrence. Let $(y_j)$ be a sequence in $E$ with
$y_0 = \|x_0\|^{-1} x_0$ and $y_{j+1} = \|A y_j\|^{-1} A y_j$ for every $j$, with $0^{-1} = 0$.
Then $y_j = q_j$ for every $j$.

Together with `Krylov.powerIterate_succ`, this shows that the closed form `Krylov.powerIterate`
specifies the algorithm. -/
theorem eq_powerIterate_of_recurrence {y : ℕ → E} (h0 : y 0 = (‖x₀‖ : 𝕜)⁻¹ • x₀)
    (hs : ∀ j, y (j + 1) = (‖A (y j)‖ : 𝕜)⁻¹ • A (y j)) (j : ℕ) :
    y j = powerIterate A x₀ j := by
  induction j with
  | zero => simpa using h0
  | succ j ih => rw [hs j, ih, ← powerIterate_succ]

/-!
### Geometric decay off the dominant eigenvector

The vectors $w$ with $\|A^k w\| = O(r^k)$ form a subspace. It contains every generalized eigenspace
whose eigenvalue has modulus less than $r$, and hence the sum of these generalized eigenspaces.
-/

variable {A x₀}

/-- The subspace of the vectors $w$ such that $\|A^k w\| \le C r^k$ for some $C$ and all $k$. -/
private def geomBounded (A : Module.End 𝕜 E) (r : ℝ) : Submodule 𝕜 E where
  carrier := {w | ∃ C : ℝ, ∀ k, ‖(A ^ k) w‖ ≤ C * r ^ k}
  add_mem' := by
    rintro v w ⟨C₁, h₁⟩ ⟨C₂, h₂⟩
    refine ⟨C₁ + C₂, fun k => ?_⟩
    calc ‖(A ^ k) (v + w)‖ ≤ ‖(A ^ k) v‖ + ‖(A ^ k) w‖ := by rw [map_add]; exact norm_add_le _ _
      _ ≤ C₁ * r ^ k + C₂ * r ^ k := add_le_add (h₁ k) (h₂ k)
      _ = (C₁ + C₂) * r ^ k := by ring
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro c w ⟨C, hC⟩
    refine ⟨‖c‖ * C, fun k => ?_⟩
    calc ‖(A ^ k) (c • w)‖ = ‖c‖ * ‖(A ^ k) w‖ := by rw [map_smul, norm_smul]
      _ ≤ ‖c‖ * (C * r ^ k) := by gcongr; exact hC k
      _ = ‖c‖ * C * r ^ k := by ring

/-- If $|\mu| < r$ and $(A - \mu I)^N w = 0$, then $\|A^k w\| \le C r^k$ for some $C$ and all $k$.
-/
private theorem exists_norm_pow_apply_le_of_pow_sub_smul_eq_zero {μ : 𝕜} {r : ℝ} (hr : ‖μ‖ < r)
    (N : ℕ) (w : E) (hw : ((A - μ • (1 : Module.End 𝕜 E)) ^ N) w = 0) :
    ∃ C : ℝ, ∀ k, ‖(A ^ k) w‖ ≤ C * r ^ k := by
  induction N generalizing w with
  | zero => exact ⟨0, by simp_all⟩
  | succ N ih =>
    have hr0 : (0 : ℝ) < r := lt_of_le_of_lt (norm_nonneg μ) hr
    have hgap : (0 : ℝ) < r - ‖μ‖ := sub_pos.mpr hr
    rw [pow_succ, Module.End.mul_apply] at hw
    obtain ⟨C, hC⟩ := ih _ hw
    have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (by simpa using hC 0)
    have hAw : A w = μ • w + (A - μ • (1 : Module.End 𝕜 E)) w := by
      simp [LinearMap.sub_apply, LinearMap.smul_apply]
    set D : ℝ := ‖w‖ + C / (r - ‖μ‖) with hD
    have hDw : ‖w‖ ≤ D := le_add_of_nonneg_right (div_nonneg hC0 hgap.le)
    have hDgap : C ≤ D * (r - ‖μ‖) := by
      rw [hD, add_mul, div_mul_cancel₀ _ hgap.ne']
      nlinarith [norm_nonneg w]
    refine ⟨D, fun k => ?_⟩
    induction k with
    | zero => simpa using hDw
    | succ k ihk =>
      have hstep : ‖(A ^ (k + 1)) w‖ ≤ ‖μ‖ * ‖(A ^ k) w‖ + C * r ^ k := by
        rw [pow_succ, Module.End.mul_apply, hAw, map_add, map_smul]
        calc ‖μ • (A ^ k) w + (A ^ k) ((A - μ • (1 : Module.End 𝕜 E)) w)‖
            ≤ ‖μ • (A ^ k) w‖ + ‖(A ^ k) ((A - μ • (1 : Module.End 𝕜 E)) w)‖ := norm_add_le _ _
          _ ≤ ‖μ‖ * ‖(A ^ k) w‖ + C * r ^ k := by rw [norm_smul]; gcongr; exact hC k
      have hmul : ‖μ‖ * (D * r ^ k) + C * r ^ k ≤ D * r ^ (k + 1) := by
        have : (‖μ‖ * D + C) * r ^ k ≤ (D * r) * r ^ k := by
          gcongr
          nlinarith
        rw [pow_succ]
        nlinarith
      refine hstep.trans (le_trans ?_ hmul)
      gcongr

/-- The **decay estimate**. Let $A$ be an endomorphism of a normed space $E$ over $\mathbb{K}$, let
$\mu \in \mathbb{K}$, and let $w \in G_\mu(A)$ be a generalized eigenvector of $A$ for $\mu$,
that is, $(A - \mu I)^N w = 0$ for some $N$. Then for every real $r > |\mu|$ there is a constant
$C$ with $$\|A^k w\| \le C r^k \quad \text{for all } k \in \mathbb{N}.$$

The excess $r - |\mu|$ pays for the polynomial factor that a Jordan block of $\mu$ contributes.
The proof is an induction on $N$. With $v = (A - \mu I) w$, the orbit satisfies
$A^{k+1} w = \mu A^k w + A^k v$, so a bound $\|A^k v\| \le C r^k$ gives
$\|A^k w\| \le (\|w\| + C/(r - |\mu|)) r^k$. The proof uses neither continuity of $A$ nor
completeness of $E$, and it computes no spectrum of a restriction of $A$. -/
theorem exists_norm_pow_apply_le_of_mem_maxGenEigenspace {μ : 𝕜} {w : E} {r : ℝ}
    (hw : w ∈ A.maxGenEigenspace μ) (hr : ‖μ‖ < r) : ∃ C : ℝ, ∀ k, ‖(A ^ k) w‖ ≤ C * r ^ k := by
  obtain ⟨N, hN⟩ := (Module.End.mem_maxGenEigenspace A μ w).mp hw
  exact exists_norm_pow_apply_le_of_pow_sub_smul_eq_zero hr N w hN

/-- Geometric decay on a spectral subspace. Let $p$ be a predicate on scalars, and let
$w \in G_p(A)$, the sum of the maximal generalized eigenspaces of $A$ for the scalars $\mu$ with
$p(\mu)$. Let $r$ be real with $|\mu| < r$ for every eigenvalue $\mu$ of $A$ with $p(\mu)$. Then
there is a constant $C$ with $$\|A^k w\| \le C r^k \quad \text{for all } k \in \mathbb{N}.$$

The rate $r$ only has to exceed the moduli of the eigenvalues that occur: a scalar that is not
an eigenvalue has the generalized eigenspace $0$. The spectral subspace $G_p(A)$ is
`Module.End.spectralSubspace A p`. -/
theorem exists_norm_pow_apply_le_of_mem_iSup {p : 𝕜 → Prop} {w : E} {r : ℝ}
    (hw : w ∈ A.spectralSubspace p)
    (hr : ∀ μ, p μ → A.HasEigenvalue μ → ‖μ‖ < r) :
    ∃ C : ℝ, ∀ k, ‖(A ^ k) w‖ ≤ C * r ^ k := by
  have key : A.spectralSubspace p ≤ geomBounded A r := by
    refine iSup₂_le fun μ hμ => ?_
    rcases eq_or_ne (A.maxGenEigenspace μ) ⊥ with h | h
    · rw [h]; exact bot_le
    · exact fun x hx => exists_norm_pow_apply_le_of_mem_maxGenEigenspace hx
        (hr μ hμ (Module.End.HasUnifEigenvalue.lt zero_lt_one h))
  exact key hw

/-- The subspace of the vectors $v$ with $\lambda^{-k} A^k v \to 0$. -/
private def tendstoZero (A : Module.End 𝕜 E) (l : 𝕜) : Submodule 𝕜 E where
  carrier := {v | Tendsto (fun k => (l ^ k)⁻¹ • (A ^ k) v) atTop (𝓝 0)}
  add_mem' := by
    intro v v' hv hv'
    have h : Tendsto (fun k => (l ^ k)⁻¹ • (A ^ k) v + (l ^ k)⁻¹ • (A ^ k) v') atTop
        (𝓝 ((0 : E) + 0)) := Filter.Tendsto.add hv hv'
    rw [add_zero] at h
    exact h.congr fun k => by rw [map_add, smul_add]
  zero_mem' := by simp
  smul_mem' := by
    intro c v hv
    have h : Tendsto (fun k => c • ((l ^ k)⁻¹ • (A ^ k) v)) atTop (𝓝 (c • (0 : E))) :=
      Filter.Tendsto.const_smul hv c
    rw [smul_zero] at h
    exact h.congr fun k => by rw [map_smul, smul_comm]

private theorem mem_tendstoZero {l : 𝕜} {v : E} :
    v ∈ tendstoZero A l ↔ Tendsto (fun k => (l ^ k)⁻¹ • (A ^ k) v) atTop (𝓝 0) := Iff.rfl

/-- If $\lambda \neq 0$ and $\|A^k x\| \le C r^k$ for all $k$, then
$\|\lambda^{-k} A^k x\| \le C (r/|\lambda|)^k$ for all $k$. -/
private theorem norm_inv_pow_smul_pow_apply_le {l : 𝕜} {x : E} {C r : ℝ} (hl : l ≠ 0)
    (hC : ∀ k, ‖(A ^ k) x‖ ≤ C * r ^ k) (k : ℕ) :
    ‖(l ^ k)⁻¹ • (A ^ k) x‖ ≤ C * (r / ‖l‖) ^ k := by
  calc ‖(l ^ k)⁻¹ • (A ^ k) x‖ = (‖l‖ ^ k)⁻¹ * ‖(A ^ k) x‖ := by
        rw [norm_smul, norm_inv, norm_pow]
    _ ≤ (‖l‖ ^ k)⁻¹ * (C * r ^ k) := by gcongr; exact hC k
    _ = C * (r / ‖l‖) ^ k := by rw [div_pow]; ring

private theorem tendsto_inv_pow_smul_pow_apply_of_norm_le {l : 𝕜} {x : E} {C r : ℝ} (hl : l ≠ 0)
    (hr0 : 0 ≤ r) (hrl : r < ‖l‖) (hC : ∀ k, ‖(A ^ k) x‖ ≤ C * r ^ k) :
    Tendsto (fun k => (l ^ k)⁻¹ • (A ^ k) x) atTop (𝓝 0) := by
  have hl0 : (0 : ℝ) < ‖l‖ := norm_pos_iff.mpr hl
  have hbound : Tendsto (fun k : ℕ => C * (r / ‖l‖) ^ k) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => (r / ‖l‖) ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hr0 hl0.le) ((div_lt_one hl0).mpr hrl)
    simpa using h1.const_mul C
  exact squeeze_zero_norm (norm_inv_pow_smul_pow_apply_le hl hC) hbound

/-- If $x \in G_\mu(A)$, $\lambda \neq 0$ and $|\mu| < |\lambda|$, then $\lambda^{-k} A^k x \to 0$.
-/
private theorem mem_tendstoZero_of_mem_maxGenEigenspace {l μ : 𝕜} {x : E}
    (hx : x ∈ A.maxGenEigenspace μ) (hl : l ≠ 0) (hμl : ‖μ‖ < ‖l‖) : x ∈ tendstoZero A l := by
  have hμr : ‖μ‖ < (‖μ‖ + ‖l‖) / 2 := by linarith
  obtain ⟨C, hC⟩ := exists_norm_pow_apply_le_of_mem_maxGenEigenspace hx hμr
  exact mem_tendstoZero.mpr (tendsto_inv_pow_smul_pow_apply_of_norm_le hl
    (le_trans (norm_nonneg μ) hμr.le) (by linarith) hC)

/-- A scalar $\lambda$ is **strictly dominant** for $A$ if every eigenvalue $\mu \neq \lambda$ of
$A$ satisfies $|\mu| < |\lambda|$.

This is the hypothesis of the convergence theorems for the power method. It does not require
that $\lambda$ is an eigenvalue, and it does not require a uniform gap between $|\lambda|$ and
the moduli of the other eigenvalues. -/
def _root_.Module.End.IsStrictlyDominant (A : Module.End 𝕜 E) (l : 𝕜) : Prop :=
  ∀ μ, μ ≠ l → A.HasEigenvalue μ → ‖μ‖ < ‖l‖

/-- A scalar $\lambda$ is strictly dominant for $A$ if and only if $|\mu| < |\lambda|$ for every
eigenvalue $\mu \neq \lambda$ of $A$. -/
theorem _root_.Module.End.isStrictlyDominant_iff {A : Module.End 𝕜 E} {l : 𝕜} :
    A.IsStrictlyDominant l ↔ ∀ μ, μ ≠ l → A.HasEigenvalue μ → ‖μ‖ < ‖l‖ :=
  Iff.rfl

/-- If $\lambda$ is strictly dominant for $A$ and $\mu \neq \lambda$ is an eigenvalue of $A$, then
$|\mu| < |\lambda|$. -/
theorem _root_.Module.End.IsStrictlyDominant.norm_lt {A : Module.End 𝕜 E} {l μ : 𝕜}
    (h : A.IsStrictlyDominant l) (hμ : μ ≠ l) (hev : A.HasEigenvalue μ) : ‖μ‖ < ‖l‖ :=
  h μ hμ hev

/-- Let $\lambda \neq 0$ be strictly dominant for $A$, and let $w \in G_{\neq\lambda}(A)$, the sum
of the generalized eigenspaces of $A$ for the scalars other than $\lambda$. Then
$\lambda^{-k} A^k w \to 0$ as $k \to \infty$.

This is the only analytic input to the convergence theorem `Krylov.powerIterate_tendsto`. It
holds under the strict dominance $|\mu| < |\lambda|$ without a uniform gap. -/
theorem tendsto_inv_pow_smul_pow_apply_of_mem_iSup {l : 𝕜} {w : E} (hl : l ≠ 0)
    (hw : w ∈ A.spectralSubspace (· ≠ l))
    (hdom : A.IsStrictlyDominant l) :
    Tendsto (fun k => (l ^ k)⁻¹ • (A ^ k) w) atTop (𝓝 0) := by
  have key : A.spectralSubspace (· ≠ l) ≤ tendstoZero A l := by
    refine iSup₂_le fun μ hμ => ?_
    rcases eq_or_ne (A.maxGenEigenspace μ) ⊥ with h | h
    · rw [h]; exact bot_le
    · exact fun x hx => mem_tendstoZero_of_mem_maxGenEigenspace hx hl
        (hdom.norm_lt hμ (Module.End.HasUnifEigenvalue.lt zero_lt_one h))
  exact mem_tendstoZero.mp (key hw)

/-! ### Convergence of the power method -/

variable {l : 𝕜} {u w : E} {C r : ℝ}

private theorem pow_apply_of_apply_eq_smul (hu : A u = l • u) (k : ℕ) :
    (A ^ k) u = l ^ k • u := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, hu, smul_smul, ← pow_succ]

private theorem inv_pow_smul_pow_apply_add (hl : l ≠ 0) (hu : A u = l • u) (k : ℕ) :
    (l ^ k)⁻¹ • (A ^ k) (u + w) = u + (l ^ k)⁻¹ • (A ^ k) w := by
  rw [map_add, pow_apply_of_apply_eq_smul hu, smul_add, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero k hl), one_smul]

/-- Let $\lambda \neq 0$, let $Au = \lambda u$, and let $\|A^k w\| \le C r^k$ for all $k$. Then for
every $k$, $$\|\lambda^{-k} A^k (u + w) - u\| \le C \left(\frac{r}{|\lambda|}\right)^k.$$
-/
theorem norm_inv_pow_smul_pow_apply_sub_le (hl : l ≠ 0) (hu : A u = l • u)
    (hw : ∀ k, ‖(A ^ k) w‖ ≤ C * r ^ k) (k : ℕ) :
    ‖(l ^ k)⁻¹ • (A ^ k) (u + w) - u‖ ≤ C * (r / ‖l‖) ^ k := by
  rw [inv_pow_smul_pow_apply_add hl hu, add_sub_cancel_left]
  exact norm_inv_pow_smul_pow_apply_le hl hw k

/-- **Convergence of the power method.** Let $A$ be an endomorphism of a normed space $E$ over
$\mathbb{K}$, and let $\lambda \neq 0$ be strictly dominant for $A$. Let $x_0 = u + w$, where
$Au = \lambda u$ and $w \in G_{\neq\lambda}(A)$ lies in the sum of the generalized eigenspaces
for the scalars other than $\lambda$. Then $$\lambda^{-k} A^k x_0 \to u \quad (k \to \infty).$$
This is Theorem 4.1 of [saad2011numerical], with the semi-simplicity of $\lambda$ replaced by
the hypothesis $Au = \lambda u$ on this particular $x_0$.

The limit $u$ is the component of $x_0$ in the generalized eigenspace $G_\lambda(A)$, so
$\lambda^{-k} A^k x_0$ converges to the spectral projection of $x_0$. The splitting
$x_0 = u + w$ is unique by `Krylov.eq_of_add_eq_add_mem_maxGenEigenspace`. -/
theorem powerIterate_tendsto {x₀ : E} (hl : l ≠ 0) (hu : A u = l • u)
    (hw : w ∈ A.spectralSubspace (· ≠ l))
    (hdom : A.IsStrictlyDominant l) (hx₀ : x₀ = u + w) :
    Tendsto (fun k => (l ^ k)⁻¹ • (A ^ k) x₀) atTop (𝓝 u) := by
  subst hx₀
  have h := tendsto_inv_pow_smul_pow_apply_of_mem_iSup hl hw hdom
  have : Tendsto (fun k => u + (l ^ k)⁻¹ • (A ^ k) w) atTop (𝓝 (u + 0)) :=
    tendsto_const_nhds.add h
  simpa only [inv_pow_smul_pow_apply_add hl hu, add_zero] using this

/-- The **rate of convergence of the power method**. Let $\lambda \neq 0$, let $x_0 = u + w$ with
$Au = \lambda u$ and $w \in G_{\neq\lambda}(A)$, and let $r$ be real with $|\mu| < r$ for every
eigenvalue $\mu \neq \lambda$ of $A$. Then there is a constant $C$ with $$\|\lambda^{-k} A^k
x_0 - u\| \le C \left(\frac{r}{|\lambda|}\right)^k \quad \text{for all } k.$$

The classical rate is $|\lambda_2/\lambda_1|^k$. Here it is weakened to every $r$ strictly above
the moduli of the other eigenvalues, because a Jordan block of a subdominant eigenvalue
contributes a polynomial factor. The bound is informative when $r < |\lambda|$. -/
theorem exists_norm_inv_pow_smul_pow_apply_sub_le {x₀ : E} (hl : l ≠ 0) (hu : A u = l • u)
    (hw : w ∈ A.spectralSubspace (· ≠ l))
    (hr : ∀ μ, μ ≠ l → A.HasEigenvalue μ → ‖μ‖ < r) (hx₀ : x₀ = u + w) :
    ∃ C : ℝ, ∀ k, ‖(l ^ k)⁻¹ • (A ^ k) x₀ - u‖ ≤ C * (r / ‖l‖) ^ k := by
  obtain ⟨C, hC⟩ := exists_norm_pow_apply_le_of_mem_iSup hw hr
  exact ⟨C, fun k => hx₀ ▸ norm_inv_pow_smul_pow_apply_sub_le hl hu hC k⟩

/-!
### The normalized iterate

The power iterate $q_k$ itself converges only up to the factor $(\lambda/|\lambda|)^k$ of modulus
one. The statements below handle this factor in two ways: they divide it out, or they measure the
eigenvalue residual, which does not see it.
-/

private theorem norm_ofReal_norm_div_pow (hl : l ≠ 0) (k : ℕ) :
    ‖(((‖l‖ : 𝕜) / l) ^ k)‖ = 1 := by
  have hl0 : (0 : ℝ) < ‖l‖ := norm_pos_iff.mpr hl
  rw [norm_pow, norm_div, RCLike.norm_ofReal, abs_of_pos hl0, div_self hl0.ne', one_pow]

/-- If $\lambda \neq 0$, $u \neq 0$ and $\lambda^{-k} A^k x_0 \to u$, then
$(|\lambda|/\lambda)^k q_k \to u/\|u\|$. -/
private theorem tendsto_smul_powerIterate_of_tendsto {x₀ : E} (hl : l ≠ 0) (hu0 : u ≠ 0)
    (hzt : Tendsto (fun k => (l ^ k)⁻¹ • (A ^ k) x₀) atTop (𝓝 u)) :
    Tendsto (fun k => (((‖l‖ : 𝕜) / l) ^ k) • powerIterate A x₀ k) atTop
      (𝓝 ((‖u‖ : 𝕜)⁻¹ • u)) := by
  have hl0 : (0 : ℝ) < ‖l‖ := norm_pos_iff.mpr hl
  have hlk : ∀ k : ℕ, (l ^ k) ≠ 0 := fun k => pow_ne_zero k hl
  set z : ℕ → E := fun k => (l ^ k)⁻¹ • (A ^ k) x₀ with hz
  have hApp : ∀ k, (A ^ k) x₀ = l ^ k • z k := fun k => by
    rw [hz]; rw [smul_smul, mul_inv_cancel₀ (hlk k), one_smul]
  have heq : ∀ k, (((‖l‖ : 𝕜) / l) ^ k) • powerIterate A x₀ k = (‖z k‖ : 𝕜)⁻¹ • z k := by
    intro k
    rw [powerIterate, hApp k, norm_smul, norm_pow, smul_smul, smul_smul]
    congr 1
    have h1 : ((‖l‖ : 𝕜)) ≠ 0 := RCLike.ofReal_ne_zero.mpr hl0.ne'
    push_cast
    rw [div_pow]
    field_simp
  have hnorm : Tendsto (fun k => ((‖z k‖ : 𝕜))⁻¹) atTop (𝓝 ((‖u‖ : 𝕜)⁻¹)) := by
    refine Tendsto.inv₀ ?_ (RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hu0))
    exact (RCLike.continuous_ofReal.tendsto _).comp hzt.norm
  simpa only [heq] using hnorm.smul hzt

/-- **Convergence of the normalized power iterates.** Let $\lambda \neq 0$ be strictly dominant for
$A$, and let $x_0 = u + w$ with $Au = \lambda u$, $u \neq 0$ and $w \in G_{\neq\lambda}(A)$.
Then the power iterates $q_k$, multiplied by the factors $(|\lambda|/\lambda)^k$ of modulus one,
converge to the normalized eigenvector: $$\left(\frac{|\lambda|}{\lambda}\right)^k q_k \to
\frac{u}{\|u\|}.$$
-/
theorem tendsto_smul_powerIterate {x₀ : E} (hl : l ≠ 0) (hu : A u = l • u) (hu0 : u ≠ 0)
    (hw : w ∈ A.spectralSubspace (· ≠ l))
    (hdom : A.IsStrictlyDominant l) (hx₀ : x₀ = u + w) :
    Tendsto (fun k => (((‖l‖ : 𝕜) / l) ^ k) • powerIterate A x₀ k) atTop
      (𝓝 ((‖u‖ : 𝕜)⁻¹ • u)) :=
  tendsto_smul_powerIterate_of_tendsto hl hu0 (powerIterate_tendsto hl hu hw hdom hx₀)

/-- **Essential convergence** of the power iterates. Let $\lambda \neq 0$ be strictly dominant for
$A$, and let $x_0 = u + w$ with $Au = \lambda u$, $u \neq 0$ and $w \in G_{\neq\lambda}(A)$.
Then there are scalars $c_k$ with $|c_k| = 1$ and $$c_k q_k \to \frac{u}{\|u\|}.$$ In the terms
of [saad2011numerical], §5.1, the iterates $q_k$ converge essentially to $u/\|u\|$.

`Krylov.tendsto_smul_powerIterate` is the same statement with the explicit sequence
$c_k = (|\lambda|/\lambda)^k$. -/
theorem exists_norm_eq_one_tendsto_smul_powerIterate {x₀ : E} (hl : l ≠ 0) (hu : A u = l • u)
    (hu0 : u ≠ 0) (hw : w ∈ A.spectralSubspace (· ≠ l))
    (hdom : A.IsStrictlyDominant l) (hx₀ : x₀ = u + w) :
    ∃ c : ℕ → 𝕜, (∀ k, ‖c k‖ = 1) ∧
      Tendsto (fun k => c k • powerIterate A x₀ k) atTop (𝓝 ((‖u‖ : 𝕜)⁻¹ • u)) :=
  ⟨fun k => ((‖l‖ : 𝕜) / l) ^ k, norm_ofReal_norm_div_pow hl,
    tendsto_smul_powerIterate hl hu hu0 hw hdom hx₀⟩

/-- Let $A$ be continuous, let $\lambda \neq 0$ be strictly dominant for $A$, and let $x_0 = u + w$
with $Au = \lambda u$, $u \neq 0$ and $w \in G_{\neq\lambda}(A)$. Then the eigenvalue residual
of the power iterates tends to zero: $$\|A q_k - \lambda q_k\| \to 0.$$

This form does not see the factors of modulus one. It says that the iterates $q_k$ become
approximate eigenvectors for $\lambda$. -/
theorem tendsto_norm_sub_smul_powerIterate {x₀ : E} (hA : Continuous A) (hl : l ≠ 0)
    (hu : A u = l • u) (hu0 : u ≠ 0) (hw : w ∈ A.spectralSubspace (· ≠ l))
    (hdom : A.IsStrictlyDominant l) (hx₀ : x₀ = u + w) :
    Tendsto (fun k => ‖A (powerIterate A x₀ k) - l • powerIterate A x₀ k‖) atTop (𝓝 0) := by
  have hres : Continuous fun v : E => A v - l • v := hA.sub (continuous_const_smul l)
  have hlim := (hres.tendsto _).comp (tendsto_smul_powerIterate hl hu hu0 hw hdom hx₀)
  have hzero : A ((‖u‖ : 𝕜)⁻¹ • u) - l • (‖u‖ : 𝕜)⁻¹ • u = 0 := by
    rw [map_smul, hu, smul_comm, sub_self]
  rw [Function.comp_def, hzero] at hlim
  have heq : ∀ k, ‖A (powerIterate A x₀ k) - l • powerIterate A x₀ k‖ =
      ‖A ((((‖l‖ : 𝕜) / l) ^ k) • powerIterate A x₀ k) -
        l • (((‖l‖ : 𝕜) / l) ^ k) • powerIterate A x₀ k‖ := by
    intro k
    rw [map_smul, smul_comm l, ← smul_sub, norm_smul, norm_ofReal_norm_div_pow hl, one_mul]
  simpa only [heq, norm_zero] using hlim.norm

/-!
### The splitting of the starting vector

Over an algebraically closed field and in finite dimension the generalized eigenspaces span the
space. So every starting vector splits as $x_0 = u + w$ with $u \in G_\lambda(A)$ and
$w \in G_{\neq\lambda}(A)$, and the splitting is unique.
-/

section Splitting

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Let $K$ be an algebraically closed field, let $V$ be a finite-dimensional vector space over $K$,
let $B$ be an endomorphism of $V$ and let $\lambda \in K$. Then the generalized eigenspace
$G_\lambda(B)$ and the sum $G_{\neq\lambda}(B)$ of the other generalized eigenspaces are
complementary subspaces: $$V = G_\lambda(B) \oplus G_{\neq\lambda}(B).$$

This is the case of one eigenvalue of `Module.End.isCompl_spectralSubspace`. The power method
uses it for the splitting $x_0 = u + w$. -/
theorem isCompl_maxGenEigenspace [IsAlgClosed K] [FiniteDimensional K V] (B : Module.End K V)
    (l : K) : IsCompl (B.maxGenEigenspace l) (B.spectralSubspace (· ≠ l)) := by
  have h := B.isCompl_spectralSubspace (· = l)
  rwa [Module.End.spectralSubspace_eq] at h

/-- Let $K$ be an algebraically closed field, let $V$ be a finite-dimensional vector space over $K$,
let $B$ be an endomorphism of $V$ and let $\lambda \in K$. Then every $x \in V$ can be written
as $x = u + w$ with $u \in G_\lambda(B)$ and $w \in G_{\neq\lambda}(B)$. -/
theorem exists_eq_add_mem_maxGenEigenspace [IsAlgClosed K] [FiniteDimensional K V]
    (B : Module.End K V) (l : K) (x : V) :
    ∃ u ∈ B.maxGenEigenspace l, ∃ w ∈ B.spectralSubspace (· ≠ l), x = u + w := by
  have htop := codisjoint_iff.mp (isCompl_maxGenEigenspace B l).codisjoint
  obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp (htop.ge (Submodule.mem_top (x := x)))
  exact ⟨u, hu, w, hw, huw.symm⟩

/-- The splitting along a generalized eigenspace is unique. Let $K$ be a field, let $V$ be a vector
space over $K$, let $B$ be an endomorphism of $V$ and let $\lambda \in K$. If
$u, u' \in G_\lambda(B)$, $w, w' \in G_{\neq\lambda}(B)$ and $u + w = u' + w'$, then $u = u'$
and $w = w'$.

The uniqueness makes the limit in `Krylov.powerIterate_tendsto` a function of $x_0$ alone: it is
the spectral projection of $x_0$ onto $G_\lambda(A)$. -/
theorem eq_of_add_eq_add_mem_maxGenEigenspace {B : Module.End K V} {l : K} {u u' w w' : V}
    (hu : u ∈ B.maxGenEigenspace l) (hu' : u' ∈ B.maxGenEigenspace l)
    (hw : w ∈ B.spectralSubspace (· ≠ l))
    (hw' : w' ∈ B.spectralSubspace (· ≠ l)) (h : u + w = u' + w') :
    u = u' ∧ w = w' := by
  have hdisj : Disjoint (B.maxGenEigenspace l) (B.spectralSubspace (· ≠ l)) :=
    B.independent_maxGenEigenspace l
  have hmem : u - u' ∈ B.maxGenEigenspace l ⊓ B.spectralSubspace (· ≠ l) := by
    refine ⟨sub_mem hu hu', ?_⟩
    have : u - u' = w' - w := by linear_combination (norm := module) h
    rw [this]
    exact sub_mem hw' hw
  rw [disjoint_iff.mp hdisj] at hmem
  have h1 : u = u' := sub_eq_zero.mp (Submodule.mem_bot K |>.mp hmem)
  exact ⟨h1, by rw [h1] at h; exact add_left_cancel h⟩

/-- A simple eigenvalue is semi-simple. Let $K$ be a field, let $V$ be a vector space over $K$, let
$B$ be an endomorphism of $V$ and let $\lambda \in K$. If the maximal generalized eigenspace
$G_\lambda(B)$ has dimension $1$, then it equals the eigenspace $\ker(B - \lambda I)$. So every
generalized eigenvector for $\lambda$ is an eigenvector. -/
theorem maxGenEigenspace_eq_eigenspace_of_finrank_eq_one {B : Module.End K V} {l : K}
    (h : Module.finrank K (B.maxGenEigenspace l) = 1) :
    B.maxGenEigenspace l = B.eigenspace l := by
  have hfin : FiniteDimensional K (B.maxGenEigenspace l) :=
    Module.finite_of_finrank_pos (by omega)
  have hne : B.maxGenEigenspace l ≠ ⊥ := fun hbot => by
    rw [hbot] at h; simp at h
  have hev : B.HasEigenvalue l := Module.End.HasUnifEigenvalue.lt zero_lt_one hne
  have hle : B.eigenspace l ≤ B.maxGenEigenspace l := Module.End.eigenspace_le_maxGenEigenspace
  have : FiniteDimensional K (B.eigenspace l) := Submodule.finiteDimensional_of_le hle
  refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  rw [h]
  exact Submodule.one_le_finrank_iff.mpr (Module.End.hasEigenvalue_iff.mp hev)

end Splitting

/-- **Convergence of the power method** at its usual hypotheses. Let $\mathbb{K}$ be algebraically
closed (that is, $\mathbb{K} = \mathbb{C}$), let $E$ be finite-dimensional, and let
$\lambda \neq 0$ be strictly dominant for $A$ and semi-simple, in the sense that
$G_\lambda(A) = \ker(A - \lambda I)$. Then every $x_0 \in E$ can be written as $x_0 = u + w$
with $Au = \lambda u$ and $w \in G_{\neq\lambda}(A)$, and $$\lambda^{-k} A^k x_0 \to u.$$

So the power method converges from every $x_0$ whose component $u$ is nonzero. The starting
vectors with $u = 0$ form the subspace $G_{\neq\lambda}(A)$, which is a hyperplane when
$\lambda$ is a simple eigenvalue. A simple eigenvalue is semi-simple by
`Krylov.maxGenEigenspace_eq_eigenspace_of_finrank_eq_one`. -/
theorem exists_eq_add_tendsto [IsAlgClosed 𝕜] [FiniteDimensional 𝕜 E] (hl : l ≠ 0)
    (hss : A.maxGenEigenspace l = A.eigenspace l)
    (hdom : A.IsStrictlyDominant l) (x₀ : E) :
    ∃ u w, A u = l • u ∧ w ∈ A.spectralSubspace (· ≠ l) ∧ x₀ = u + w ∧
      Tendsto (fun k => (l ^ k)⁻¹ • (A ^ k) x₀) atTop (𝓝 u) := by
  obtain ⟨u, hu, w, hw, huw⟩ := exists_eq_add_mem_maxGenEigenspace A l x₀
  rw [hss, Module.End.mem_eigenspace_iff] at hu
  exact ⟨u, w, hu, hw, huw, powerIterate_tendsto hl hu hw hdom huw⟩

/-!
### Inverse iteration

Inverse iteration with shift $\sigma$ is the power method for $(A - \sigma I)^{-1}$. The eigenvalues
of this operator are the numbers $(\mu - \sigma)^{-1}$, so the eigenvalue of $A$ closest to the
shift becomes the dominant one.
-/

section InverseIteration

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **Inverse iteration** with shift $\sigma$, also called the shift-and-invert power method: the
power iteration `Krylov.powerIterate` for the operator $(A - \sigma I)^{-1}$, $$q_k = \|(A -
\sigma I)^{-k} x_0\|^{-1} (A - \sigma I)^{-k} x_0.$$ This is the shift-and-invert iteration of
[saad2011numerical], §4.1.2–4.1.3.

The inverse is `Ring.inverse`, so the definition is total. If $A - \sigma I$ is not invertible,
`Ring.inverse` gives $0$, and the iterates are the power iterates of the zero operator. Every
convergence theorem assumes that $A - \sigma I$ is invertible (`IsUnit (A - σ • 1)`), which in
finite dimension means that $\sigma$ is not an eigenvalue of $A$. -/
noncomputable def inverseIterate (A : Module.End 𝕜 E) (σ : 𝕜) (x₀ : E) (k : ℕ) : E :=
  powerIterate (Ring.inverse (A - σ • (1 : Module.End 𝕜 E))) x₀ k

/-- Inverse iteration with shift $\sigma$ is the power iteration of $(A - \sigma I)^{-1}$:
`Krylov.inverseIterate A σ x₀ k` equals `Krylov.powerIterate (Ring.inverse (A - σ • 1)) x₀ k`. -/
@[simp]
theorem inverseIterate_eq_powerIterate (A : Module.End 𝕜 E) (σ : 𝕜) (x₀ : E) (k : ℕ) :
    inverseIterate A σ x₀ k
      = powerIterate (Ring.inverse (A - σ • (1 : Module.End 𝕜 E))) x₀ k := rfl

variable {A : Module.End 𝕜 E} {σ : 𝕜}

private theorem sub_smul_one_apply (μ : 𝕜) (x : E) :
    (A - μ • (1 : Module.End 𝕜 E)) x = A x - μ • x := by
  simp

private theorem commute_inverse_sub_smul_one
    (hσ : IsUnit (A - σ • (1 : Module.End 𝕜 E))) (μ : 𝕜) :
    Commute (Ring.inverse (A - σ • (1 : Module.End 𝕜 E))) (A - μ • (1 : Module.End 𝕜 E)) := by
  have hT : Commute (Ring.inverse (A - σ • (1 : Module.End 𝕜 E)))
      (A - σ • (1 : Module.End 𝕜 E)) :=
    (Ring.inverse_mul_cancel _ hσ).trans (Ring.mul_inverse_cancel _ hσ).symm
  have hone := (Commute.one_right (Ring.inverse (A - σ • (1 : Module.End 𝕜 E)))).smul_right (μ - σ)
  have := hT.sub_right hone
  have heq : A - σ • (1 : Module.End 𝕜 E) - (μ - σ) • (1 : Module.End 𝕜 E)
      = A - μ • (1 : Module.End 𝕜 E) := by module
  rwa [heq] at this

/-- The shifted inverse has the same eigenvectors, with inverted shifted eigenvalues. Let
$A - \sigma I$ be invertible, let $\mu \neq \sigma$, and let $Ax = \mu x$. Then $$(A - \sigma
I)^{-1} x = (\mu - \sigma)^{-1} x.$$
-/
theorem inverse_apply_eq_smul {μ : 𝕜} {x : E} (hσ : IsUnit (A - σ • (1 : Module.End 𝕜 E)))
    (hμ : μ ≠ σ) (hx : A x = μ • x) :
    Ring.inverse (A - σ • (1 : Module.End 𝕜 E)) x = (μ - σ)⁻¹ • x := by
  have hT : (A - σ • (1 : Module.End 𝕜 E)) x = (μ - σ) • x := by
    rw [sub_smul_one_apply, hx, sub_smul]
  have h := congrArg (fun f : Module.End 𝕜 E => f x) (Ring.inverse_mul_cancel _ hσ)
  simp only [Module.End.mul_apply, Module.End.one_apply, hT, map_smul] at h
  conv_rhs => rw [← h]
  rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hμ), one_smul]

/-- If $A - \sigma I$ is invertible, then the maximal generalized eigenspace $G_\sigma(A)$ of $A$
for the shift is $0$. -/
theorem maxGenEigenspace_eq_bot_of_isUnit (hσ : IsUnit (A - σ • (1 : Module.End 𝕜 E))) :
    A.maxGenEigenspace σ = ⊥ := by
  refine le_bot_iff.1 fun x hx => ?_
  obtain ⟨N, hN⟩ := (Module.End.mem_maxGenEigenspace A σ x).1 hx
  exact Submodule.mem_bot _ |>.2
    (((Module.End.isUnit_iff _).1 (hσ.pow N)).injective (hN.trans (map_zero _).symm))

/-- The shifted inverse keeps the generalized eigenspaces. Let $A - \sigma I$ be invertible and let
$\mu \neq \sigma$. Then the maximal generalized eigenspace of $A$ for $\mu$ is contained in the
maximal generalized eigenspace of $(A - \sigma I)^{-1}$ for $(\mu - \sigma)^{-1}$: $$G_\mu(A)
\subseteq G_{(\mu - \sigma)^{-1}}\bigl((A - \sigma I)^{-1}\bigr).$$

The proof gives a generalized eigenvector of the same index. It uses the factorization $(A -
\sigma I)^{-1} - (\mu - \sigma)^{-1} I = -(\mu - \sigma)^{-1} (A - \sigma I)^{-1} (A - \mu I)$
and the fact that the two factors commute. -/
theorem maxGenEigenspace_le_maxGenEigenspace_inverse {μ : 𝕜}
    (hσ : IsUnit (A - σ • (1 : Module.End 𝕜 E))) (hμ : μ ≠ σ) :
    A.maxGenEigenspace μ ≤
      (Ring.inverse (A - σ • (1 : Module.End 𝕜 E))).maxGenEigenspace (μ - σ)⁻¹ := by
  have hμσ : μ - σ ≠ 0 := sub_ne_zero.2 hμ
  have hkey : Ring.inverse (A - σ • (1 : Module.End 𝕜 E)) - (μ - σ)⁻¹ • (1 : Module.End 𝕜 E)
      = (-(μ - σ)⁻¹) •
        (Ring.inverse (A - σ • (1 : Module.End 𝕜 E)) * (A - μ • (1 : Module.End 𝕜 E))) := by
    have heq : A - μ • (1 : Module.End 𝕜 E)
        = (A - σ • (1 : Module.End 𝕜 E)) - (μ - σ) • (1 : Module.End 𝕜 E) := by module
    rw [heq, mul_sub, Ring.inverse_mul_cancel _ hσ, mul_smul_comm, mul_one, smul_sub, smul_smul,
      show (-(μ - σ)⁻¹) * (μ - σ) = -1 by rw [neg_mul, inv_mul_cancel₀ hμσ]]
    module
  intro x hx
  obtain ⟨N, hN⟩ := (Module.End.mem_maxGenEigenspace A μ x).1 hx
  refine (Module.End.mem_maxGenEigenspace _ _ x).2 ⟨N, ?_⟩
  rw [hkey, smul_pow, (commute_inverse_sub_smul_one hσ μ).mul_pow]
  simp [Module.End.mul_apply, hN]

/-- Every eigenvalue of the shifted inverse comes from an eigenvalue of $A$. Let $A - \sigma I$ be
invertible, and let $\nu$ be an eigenvalue of $(A - \sigma I)^{-1}$. Then $\nu \neq 0$, and
$\sigma + \nu^{-1}$ is an eigenvalue of $A$. -/
theorem hasEigenvalue_of_hasEigenvalue_inverse {ν : 𝕜}
    (hσ : IsUnit (A - σ • (1 : Module.End 𝕜 E)))
    (hν : (Ring.inverse (A - σ • (1 : Module.End 𝕜 E))).HasEigenvalue ν) :
    ν ≠ 0 ∧ A.HasEigenvalue (σ + ν⁻¹) := by
  obtain ⟨x, hx, hx0⟩ := hν.exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff] at hx
  have hround := congrArg (fun f : Module.End 𝕜 E => f x) (Ring.mul_inverse_cancel _ hσ)
  simp only [Module.End.mul_apply, Module.End.one_apply, hx, map_smul] at hround
  have hν0 : ν ≠ 0 := by
    rintro rfl
    simp only [zero_smul] at hround
    exact hx0 hround.symm
  refine ⟨hν0, Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.2 ?_, hx0⟩⟩
  have hT : (A - σ • (1 : Module.End 𝕜 E)) x = ν⁻¹ • x := by
    conv_rhs => rw [← hround]
    rw [smul_smul, inv_mul_cancel₀ hν0, one_smul]
  rw [sub_smul_one_apply] at hT
  rw [add_smul, ← hT]
  abel

/-- **Convergence of inverse iteration.** Let $A - \sigma I$ be invertible, and let $\lambda$ be
strictly closer to the shift than every other eigenvalue of $A$:
$|\lambda - \sigma| < |\mu - \sigma|$ for every eigenvalue $\mu \neq \lambda$. Let $x_0 = u + w$
with $Au = \lambda u$, $u \neq 0$ and $w \in G_{\neq\lambda}(A)$. Then the inverse iterates
$q_k$ converge essentially to the normalized eigenvector: $$\left(\frac{\lambda -
\sigma}{|\lambda - \sigma|}\right)^k q_k \to \frac{u}{\|u\|}.$$

The proof shows that $(\lambda - \sigma)^{-1}$ is strictly dominant for $(A - \sigma I)^{-1}$.
The rate of `Krylov.exists_norm_inv_pow_smul_pow_apply_sub_le` then reads
$(|\lambda - \sigma|/|\mu_2 - \sigma|)^k$, where $\mu_2$ is the next eigenvalue in distance from
$\sigma$. So the closer the shift is to $\lambda$, relative to the rest of the spectrum, the
faster the convergence. This is why shifting is worth its cost: the dominance hypothesis is
about distances to the shift, not about moduli. -/
theorem tendsto_smul_inverseIterate {l : 𝕜} {u w x₀ : E}
    (hσ : IsUnit (A - σ • (1 : Module.End 𝕜 E))) (hu : A u = l • u) (hu0 : u ≠ 0)
    (hw : w ∈ A.spectralSubspace (· ≠ l))
    (hdom : ∀ μ, μ ≠ l → A.HasEigenvalue μ → ‖l - σ‖ < ‖μ - σ‖) (hx₀ : x₀ = u + w) :
    Tendsto (fun k => (((l - σ) / (‖l - σ‖ : 𝕜)) ^ k) • inverseIterate A σ x₀ k) atTop
      (𝓝 ((‖u‖ : 𝕜)⁻¹ • u)) := by
  set B : Module.End 𝕜 E := Ring.inverse (A - σ • (1 : Module.End 𝕜 E)) with hB
  have hlσ : l ≠ σ := by
    rintro rfl
    refine hu0 (((Module.End.isUnit_iff _).1 hσ).injective ?_)
    rw [map_zero, sub_smul_one_apply, hu, sub_self]
  have hlσ0 : l - σ ≠ 0 := sub_ne_zero.2 hlσ
  have hl' : (l - σ)⁻¹ ≠ 0 := inv_ne_zero hlσ0
  have hu' : B u = (l - σ)⁻¹ • u := inverse_apply_eq_smul hσ hlσ hu
  have hw' : w ∈ ⨆ ν, ⨆ _ : ν ≠ (l - σ)⁻¹, B.maxGenEigenspace ν := by
    refine (iSup₂_le fun μ hμ => ?_ : A.spectralSubspace (· ≠ l) ≤ _) hw
    rcases eq_or_ne μ σ with rfl | hμσ
    · rw [maxGenEigenspace_eq_bot_of_isUnit hσ]; exact bot_le
    · refine le_trans (maxGenEigenspace_le_maxGenEigenspace_inverse hσ hμσ) ?_
      exact le_iSup₂ (f := fun ν (_ : ν ≠ (l - σ)⁻¹) => B.maxGenEigenspace ν) _
        (fun h => hμ (by simpa [sub_left_inj] using inv_inj.1 h))
  have hdom' : B.IsStrictlyDominant (l - σ)⁻¹ := by
    intro ν hν hνe
    obtain ⟨hν0, hA⟩ := hasEigenvalue_of_hasEigenvalue_inverse hσ hνe
    have hμ : σ + ν⁻¹ ≠ l := by
      rintro rfl
      exact hν (by rw [add_sub_cancel_left, inv_inv])
    have hlt := hdom _ hμ hA
    rw [add_sub_cancel_left, norm_inv] at hlt
    have h1 : (0 : ℝ) < ‖ν‖ := norm_pos_iff.2 hν0
    have h2 : (0 : ℝ) < ‖l - σ‖ := norm_pos_iff.2 hlσ0
    rw [inv_eq_one_div, lt_div_iff₀ h1] at hlt
    rw [norm_inv, inv_eq_one_div, lt_div_iff₀ h2, mul_comm]
    exact hlt
  have hfac : ((‖(l - σ)⁻¹‖ : 𝕜)) / (l - σ)⁻¹ = (l - σ) / (‖l - σ‖ : 𝕜) := by
    rw [norm_inv, RCLike.ofReal_inv, inv_div_inv]
  have hlim := tendsto_smul_powerIterate hl' hu' hu0 hw' hdom' hx₀
  rw [hfac, hB] at hlim
  exact hlim

end InverseIteration

/-!
### Subspace iteration

Subspace iteration is the block form of the power method: $A$ carries a whole subspace along, and
the dominant eigenvectors come close to it. The distance is measured with the orthogonal projection
`Submodule.starProjection`, so this part of the module needs an inner product.
-/

section SubspaceIteration

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable (A : Module.End 𝕜 E) (S : Submodule 𝕜 E)

/-- **Simple subspace iteration** in closed form. For a subspace $S$ of $E$, the $k$-th iterate is
the subspace $$A^k S = \{A^k y : y \in S\}.$$

The algorithm of [saad2011numerical], Algorithm 5.1 (Bauer's Treppeniteration),
reorthonormalizes its block of vectors after every multiplication by $A$. This changes the basis
but not the subspace that it spans. So the subspace after $k$ steps is $A^k S$, whatever
normalization the algorithm uses, just as `Krylov.powerIterate` is a normalization of $A^k x_0$. -/
def subspaceIterate (k : ℕ) : Submodule 𝕜 E := S.map (A ^ k)

/-- If the starting subspace $S$ is finite-dimensional, then so is every iterate $A^k S$. This gives
the orthogonal projection onto $A^k S$ without a completeness assumption on $E$. -/
instance [FiniteDimensional 𝕜 S] (k : ℕ) : FiniteDimensional 𝕜 (subspaceIterate A S k) :=
  inferInstanceAs (FiniteDimensional 𝕜 (S.map (A ^ k)))

variable {A S}

/-- A vector $x$ lies in $A^k S$ if and only if $x = A^k y$ for some $y \in S$. -/
theorem mem_subspaceIterate {k : ℕ} {x : E} :
    x ∈ subspaceIterate A S k ↔ ∃ y ∈ S, (A ^ k) y = x := Submodule.mem_map

/-- If $y \in S$, then $A^k y \in A^k S$ for every $k$. These vectors are the candidates in the
proof of the convergence bound. -/
theorem apply_pow_mem_subspaceIterate {y : E} (hy : y ∈ S) (k : ℕ) :
    (A ^ k) y ∈ subspaceIterate A S k := Submodule.mem_map_of_mem hy

/-- Subspace iteration starts at the given subspace: $A^0 S = S$. -/
@[simp]
theorem subspaceIterate_zero : subspaceIterate A S 0 = S := by
  rw [subspaceIterate, pow_zero, Module.End.one_eq_id, Submodule.map_id]

/-- One step of subspace iteration applies $A$ to the subspace: $A^{k+1} S = A(A^k S)$. This is the
recurrence that the algorithm runs. -/
theorem subspaceIterate_succ (k : ℕ) :
    subspaceIterate A S (k + 1) = (subspaceIterate A S k).map A := by
  rw [subspaceIterate, subspaceIterate, pow_succ', Module.End.mul_eq_comp, Submodule.map_comp]

/-- The **subspace-iteration bound** in its basic form, with no spectral hypothesis and no finite
dimension of $E$. Let $E$ be an inner product space, let $S$ be a finite-dimensional subspace,
and let $Au = \lambda u$ with $\lambda \neq 0$. Let $s \in S$, and suppose that
$\|A^k (s - u)\| \le C r^k$ for all $k$. Then for every $k$, $$\|u - P_{A^k S} u\| \le C
\left(\frac{r}{|\lambda|}\right)^k,$$ where $P_{A^k S}$ is the orthogonal projection onto
$A^k S$.

The proof uses one candidate, $\lambda^{-k} A^k s \in A^k S$, whose error is
$\lambda^{-k} A^k (s - u)$. The orthogonal projection is the best approximation from $A^k S$, so
it does at least as well. Compare `Krylov.norm_inv_pow_smul_pow_apply_sub_le`, the same estimate
for the power method: there the approximant is the scaled iterate itself, and here it is the
best approximant from a subspace that contains it, so the block bound is the sharper one. -/
theorem norm_sub_starProjection_subspaceIterate_le [FiniteDimensional 𝕜 S] {u s : E} {l : 𝕜}
    {C r : ℝ} (hl : l ≠ 0) (hu : A u = l • u) (hs : s ∈ S)
    (hC : ∀ k, ‖(A ^ k) (s - u)‖ ≤ C * r ^ k) (k : ℕ) :
    ‖u - (subspaceIterate A S k).starProjection u‖ ≤ C * (r / ‖l‖) ^ k := by
  have hy : (l ^ k)⁻¹ • (A ^ k) s ∈ subspaceIterate A S k :=
    Submodule.smul_mem _ _ (apply_pow_mem_subspaceIterate hs k)
  have key : (l ^ k)⁻¹ • (A ^ k) s = u + (l ^ k)⁻¹ • (A ^ k) (s - u) := by
    have h := inv_pow_smul_pow_apply_add (w := s - u) hl hu k
    rwa [add_sub_cancel] at h
  have heq : ‖u - (l ^ k)⁻¹ • (A ^ k) s‖ = ‖(l ^ k)⁻¹ • (A ^ k) (s - u)‖ := by
    rw [key, sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg]
  refine ((isBestApprox_starProjection _ u).2 _ hy).trans ?_
  rw [heq]
  exact norm_inv_pow_smul_pow_apply_le hl hC k

/-- **Convergence of subspace iteration.** Let $E$ be a finite-dimensional inner product space over
$\mathbb{K}$, with $\mathbb{K}$ algebraically closed. Let a predicate $p$ select a set of
eigenvalues, let $M = G_p(A)$ be the sum of their generalized eigenspaces, and let
$W = G_{\neg p}(A)$ be the sum of the other ones. Let the starting subspace $S$ satisfy
$S \cap W = 0$ and $\dim S = \dim M$. Let $u \in M$ with $Au = \lambda u$ and $\lambda \neq 0$,
and let $r$ be real with $|\mu| < r$ for every eigenvalue $\mu$ of $A$ with $\neg p(\mu)$. Then
there is a constant $C$ with $$\|u - P_{A^k S} u\| \le C \left(\frac{r}{|\lambda|}\right)^k
\quad \text{for all } k.$$ This is Theorem 5.2 of [saad2011numerical].

The source requires that the projections of a spanning family of $S$ onto $M$ along $W$ are
linearly independent. This is the condition $S \cap W = 0$, because $W$ is the kernel of the
spectral projector (`Module.End.injOn_spectralProjector_iff`). The source states the constant as
$\|u - s\|$ and the rate as $(|\lambda_{m+1}/\lambda_i| + \varepsilon_k)^k$ with
$\varepsilon_k \to 0$. Here the constant is $C$ and the base of the power does not move, the
same trade as for the power method. The bound is informative when $r < |\lambda|$, that is, when
the selected eigenvalues dominate; `Krylov.tendsto_starProjection_subspaceIterate` is the
convergence statement. -/
theorem exists_norm_sub_starProjection_subspaceIterate_le [IsAlgClosed 𝕜] [FiniteDimensional 𝕜 E]
    {p : 𝕜 → Prop} {u : E} {l : 𝕜} {r : ℝ}
    (hdisj : Disjoint S (A.spectralSubspace fun μ => ¬ p μ))
    (hrank : Module.finrank 𝕜 S = Module.finrank 𝕜 (A.spectralSubspace p))
    (hl : l ≠ 0) (hu : A u = l • u) (hmem : u ∈ A.spectralSubspace p)
    (hr : ∀ μ, ¬ p μ → A.HasEigenvalue μ → ‖μ‖ < r) :
    ∃ C : ℝ, ∀ k, ‖u - (subspaceIterate A S k).starProjection u‖ ≤ C * (r / ‖l‖) ^ k := by
  obtain ⟨s, ⟨hs, hsu⟩, -⟩ := Module.End.existsUnique_mem_spectralProjector_eq hdisj hrank hmem
  have hw : s - u ∈ A.spectralSubspace fun μ => ¬ p μ := by
    rw [← hsu]; exact Module.End.sub_spectralProjector_mem s
  obtain ⟨C, hC⟩ := exists_norm_pow_apply_le_of_mem_iSup hw hr
  exact ⟨C, fun k => norm_sub_starProjection_subspaceIterate_le hl hu hs hC k⟩

/-- The iterated subspaces capture the dominant eigenvectors in the limit. Let $E$ be a
finite-dimensional inner product space over $\mathbb{K}$, with $\mathbb{K}$ algebraically
closed. Let $p$ select a set of eigenvalues, let $M = G_p(A)$ and $W = G_{\neg p}(A)$, and let
$S \cap W = 0$ and $\dim S = \dim M$. Let $u \in M$ with $Au = \lambda u$ and $\lambda \neq 0$,
and let $0 \le r < |\lambda|$ with $|\mu| < r$ for every eigenvalue $\mu$ of $A$ with
$\neg p(\mu)$. Then the orthogonal projections of $u$ onto the iterates converge to $u$:
$$P_{A^k S} u \to u.$$
-/
theorem tendsto_starProjection_subspaceIterate [IsAlgClosed 𝕜] [FiniteDimensional 𝕜 E]
    {p : 𝕜 → Prop} {u : E} {l : 𝕜} {r : ℝ}
    (hdisj : Disjoint S (A.spectralSubspace fun μ => ¬ p μ))
    (hrank : Module.finrank 𝕜 S = Module.finrank 𝕜 (A.spectralSubspace p))
    (hl : l ≠ 0) (hu : A u = l • u) (hmem : u ∈ A.spectralSubspace p)
    (hr0 : 0 ≤ r) (hrl : r < ‖l‖) (hr : ∀ μ, ¬ p μ → A.HasEigenvalue μ → ‖μ‖ < r) :
    Tendsto (fun k => (subspaceIterate A S k).starProjection u) atTop (𝓝 u) := by
  obtain ⟨C, hC⟩ := exists_norm_sub_starProjection_subspaceIterate_le hdisj hrank hl hu hmem hr
  have hl0 : (0 : ℝ) < ‖l‖ := norm_pos_iff.mpr hl
  have hbound : Tendsto (fun k : ℕ => C * (r / ‖l‖) ^ k) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => (r / ‖l‖) ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hr0 hl0.le) ((div_lt_one hl0).mpr hrl)
    simpa using h1.const_mul C
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm (fun k => ?_) hbound
  rw [norm_norm, norm_sub_rev]
  exact hC k

/-!
### The gap form of the subspace-iteration bound

`Krylov.norm_sub_starProjection_subspaceIterate_le` measures the convergence one eigenvector at a
time. The QR algorithm and orthogonal iteration need the gap $\|P_M - P_{A^k S}\|$ instead. The gap
bounds the distance to $A^k S$ of every vector of $M$ at once (`Submodule.sinAngle_le_gap`), so it
is the stronger statement.
-/

/-- The **gap form of the subspace-iteration bound**, with no spectral hypothesis, no algebraically
closed field and no finite dimension of $E$. Let $E$ be an inner product space, and let $\iota$
be a finite index set. Let $(x_j)_{j \in \iota}$ be linearly independent eigenvectors,
$Ax_j = \lambda_j x_j$, with $\lambda_j \neq 0$ and $|\lambda_j| \ge \rho > 0$, and let $M$ be
their span. Let $S$ be the span of a family $(s_j)_{j \in \iota}$, and suppose that
$\|A^k (s_j - x_j)\| \le C r^k$ for all $j$ and $k$, where $0 \le r < \rho$. Then there is a
constant $D$ with $$\operatorname{gap}(M, A^k S) \le D \left(\frac{r}{\rho}\right)^k \quad
\text{for all } k,$$ where $\operatorname{gap}(M, L) = \|P_M - P_L\|$ is `Submodule.gap`. This
is Lemma 7.18 of [kress1998numerical].

The hypotheses are those that the proof of [kress1998numerical] uses, not those of its
statement. The source assumes that $A$ is diagonalizable and that $S \cap U = 0$ for the
invariant complement $U$ of $M$; these give the family $(s_j)$, through the spectral projector,
and the decay $C r^k$. The spectral form is `Krylov.exists_gap_subspaceIterate_le`. The proof
applies `Submodule.gap_le_of_forall_norm_sub_le` to the spanning families $(x_j)$ and
$(\lambda_j^{-k} A^k s_j)$. The second family spans $A^k S$, and it converges to the first at
the stated rate by `Krylov.norm_inv_pow_smul_pow_apply_sub_le`. The smallness hypothesis of
`Submodule.gap_le_of_forall_norm_sub_le` holds only from some step on, and the constant $D$
absorbs the earlier steps, where the gap is at most $1$ (`Submodule.gap_le_one`). The case
$r = 0$ is separate, because then $(r/\rho)^k$ vanishes and leaves nothing to absorb; in that
case $A^k S = M$ for $k \ge 1$. -/
theorem gap_subspaceIterate_le {ι : Type*} [Finite ι] {M : Submodule 𝕜 E}
    [FiniteDimensional 𝕜 M] [FiniteDimensional 𝕜 S] {x s : ι → E} {l : ι → 𝕜} {C r ρ : ℝ}
    (hxli : LinearIndependent 𝕜 x) (hM : M = Submodule.span 𝕜 (Set.range x))
    (hS : S = Submodule.span 𝕜 (Set.range s)) (heig : ∀ j, A (x j) = l j • x j)
    (hl0 : ∀ j, l j ≠ 0) (hρ : 0 < ρ) (hlρ : ∀ j, ρ ≤ ‖l j‖) (hr : 0 ≤ r) (hrρ : r < ρ)
    (hC : ∀ j k, ‖(A ^ k) (s j - x j)‖ ≤ C * r ^ k) :
    ∃ D : ℝ, ∀ k, M.gap (subspaceIterate A S k) ≤ D * (r / ρ) ^ k := by
  cases nonempty_fintype ι
  have hq0 : 0 ≤ r / ρ := div_nonneg hr hρ.le
  have hq1 : r / ρ < 1 := (div_lt_one hρ).2 hrρ
  have hC'0 : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  set w : ℕ → ι → E := fun k j => (l j ^ k)⁻¹ • (A ^ k) (s j) with hwdef
  have hwx : ∀ k j, ‖w k j - x j‖ ≤ max C 0 * (r / ρ) ^ k := by
    intro k j
    have hCj : ∀ n, ‖(A ^ n) (s j - x j)‖ ≤ max C 0 * r ^ n := fun n =>
      (hC j n).trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (pow_nonneg hr n))
    have h1 := norm_inv_pow_smul_pow_apply_sub_le (A := A) (hl0 j) (heig j) hCj k
    rw [add_sub_cancel] at h1
    refine h1.trans ?_
    gcongr
    exact hlρ j
  have hspan : ∀ k, subspaceIterate A S k = Submodule.span 𝕜 (Set.range (w k)) := by
    intro k
    rw [subspaceIterate, hS, Submodule.map_span, ← Set.range_comp]
    exact (Submodule.span_range_smul_of_ne_zero _
      (fun j => inv_ne_zero (pow_ne_zero k (hl0 j))) _).symm
  obtain ⟨κ, hκ, hκb⟩ := hxli.exists_forall_sum_norm_le
  have main : ∀ k, κ * (max C 0 * (r / ρ) ^ k) ≤ 1 / 2 →
      M.gap (subspaceIterate A S k) ≤ 3 * (κ * (max C 0 * (r / ρ) ^ k)) := fun k hk =>
    (Submodule.gap_le_of_forall_norm_sub_le M _ hM (hspan k) hκ.le (by positivity) hκb (hwx k)
      hk).trans (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
  have htriv : ∀ k, M.gap (subspaceIterate A S k) ≤ 1 := fun k => M.gap_le_one _
  rcases eq_or_lt_of_le hr with hr0 | hrpos
  · refine ⟨3 * κ * max C 0 + 1, fun k => ?_⟩
    have hqz : r / ρ = 0 := by rw [← hr0, zero_div]
    match k with
    | 0 => simpa using (htriv 0).trans (by nlinarith)
    | (n + 1) =>
      have hz : (r / ρ) ^ (n + 1) = 0 := by rw [hqz]; simp
      rw [hz, mul_zero]
      have h := main (n + 1) (by rw [hz]; norm_num)
      rw [hz, mul_zero, mul_zero, mul_zero] at h
      exact h
  · have htend : Tendsto (fun k : ℕ => κ * (max C 0 * (r / ρ) ^ k)) atTop (𝓝 0) := by
      have h := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
      simpa using ((h.const_mul (max C 0)).const_mul κ)
    obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.1
      (htend.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2))
    refine ⟨3 * κ * max C 0 + (ρ / r) ^ k₀, fun k => ?_⟩
    rcases le_or_gt k₀ k with hk | hk
    · have h := main k (hk₀ k hk).le
      have hpow : (0 : ℝ) ≤ (r / ρ) ^ k := pow_nonneg hq0 k
      nlinarith [pow_nonneg (div_nonneg hρ.le hrpos.le) k₀]
    · have hge : (1 : ℝ) ≤ ρ / r := (one_le_div hrpos).2 hrρ.le
      have h2 : (ρ / r) ^ k ≤ (ρ / r) ^ k₀ := pow_le_pow_right₀ hge hk.le
      have h3 : (ρ / r) ^ k * (r / ρ) ^ k = 1 := by
        rw [← mul_pow, div_mul_div_comm, mul_comm ρ r, div_self (by positivity), one_pow]
      have hpow : (0 : ℝ) ≤ (r / ρ) ^ k := pow_nonneg hq0 k
      have h1 : (1 : ℝ) ≤ (ρ / r) ^ k₀ * (r / ρ) ^ k := by nlinarith
      have hgap := htriv k
      nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hκ.le) hC'0]

/-- The **gap form of the subspace-iteration bound** at the spectral hypotheses of
[saad2011numerical], Theorem 5.2, and [kress1998numerical], Lemma 7.18. Let $E$ be a
finite-dimensional inner product space over $\mathbb{K}$, with $\mathbb{K}$ algebraically
closed. Let $p$ select a set of eigenvalues, let $M = G_p(A)$ and $W = G_{\neg p}(A)$, and let
the starting subspace $S$ satisfy $S \cap W = 0$ and $\dim S = \dim M$. Suppose that $M$ is
spanned by linearly independent eigenvectors $(x_j)_{j \in \iota}$, $\iota$ finite, with
$Ax_j = \lambda_j x_j$ and $|\lambda_j| \ge \rho > 0$. Let $0 \le r < \rho$ with $|\mu| < r$ for
every eigenvalue $\mu$ of $A$ with $\neg p(\mu)$. Then there is a constant $D$ with
$$\operatorname{gap}(M, A^k S) \le D \left(\frac{r}{\rho}\right)^k \quad \text{for all } k.$$

The hypothesis that eigenvectors span $M$ says that the selected eigenvalues are semi-simple;
this is the diagonalizability of [kress1998numerical], required only on $M$. A nontrivial Jordan
block among the selected eigenvalues would contribute a polynomial factor $k^{N-1}$ and make the
rate $(r/\rho)^k$ false when $r$ is exactly the subdominant modulus;
`Krylov.exists_norm_pow_apply_le_of_mem_maxGenEigenspace` handles the same effect with a strict
$r$. The family $(x_j)$ is data and not a conclusion, because nothing in this module constructs
a basis of a sum of eigenspaces. The proof takes the preimages $s_j \in S$ of the $x_j$ under
the spectral projector (`Module.End.existsUnique_mem_spectralProjector_eq`), shows by a
dimension count that they span $S$, and bounds the orbit of each $s_j - x_j \in W$ by
`Krylov.exists_norm_pow_apply_le_of_mem_iSup`. -/
theorem exists_gap_subspaceIterate_le [IsAlgClosed 𝕜] [FiniteDimensional 𝕜 E] {p : 𝕜 → Prop}
    {ι : Type*} [Finite ι] {x : ι → E} {l : ι → 𝕜} {r ρ : ℝ}
    (hdisj : Disjoint S (A.spectralSubspace fun μ => ¬ p μ))
    (hrank : Module.finrank 𝕜 S = Module.finrank 𝕜 (A.spectralSubspace p))
    (hxli : LinearIndependent 𝕜 x)
    (hM : A.spectralSubspace p = Submodule.span 𝕜 (Set.range x))
    (heig : ∀ j, A (x j) = l j • x j) (hρ : 0 < ρ) (hlρ : ∀ j, ρ ≤ ‖l j‖)
    (hr : 0 ≤ r) (hrρ : r < ρ) (hspec : ∀ μ, ¬ p μ → A.HasEigenvalue μ → ‖μ‖ < r) :
    ∃ D : ℝ, ∀ k, (A.spectralSubspace p).gap (subspaceIterate A S k)
      ≤ D * (r / ρ) ^ k := by
  cases nonempty_fintype ι
  have hxM : ∀ j, x j ∈ A.spectralSubspace p := fun j => by
    rw [hM]; exact Submodule.subset_span ⟨j, rfl⟩
  choose s hs using fun j =>
    (Module.End.existsUnique_mem_spectralProjector_eq hdisj hrank (hxM j)).exists
  have hsS : ∀ j, s j ∈ S := fun j => (hs j).1
  have hsP : ∀ j, A.spectralProjector p (s j) = x j := fun j => (hs j).2
  have hsli : LinearIndependent 𝕜 s := by
    have hcomp : LinearIndependent 𝕜 fun j => A.spectralProjector p (s j) := by
      simpa only [hsP] using hxli
    exact hcomp.of_comp (A.spectralProjector p)
  have hcard : Module.finrank 𝕜 ↥(Submodule.span 𝕜 (Set.range s)) = Fintype.card ι :=
    finrank_span_eq_card hsli
  have hSspan : S = Submodule.span 𝕜 (Set.range s) := by
    refine (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm
    · exact Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hsS j)
    · rw [hcard, hrank, hM, finrank_span_eq_card hxli]
  have hC : ∀ j, ∃ C : ℝ, ∀ k, ‖(A ^ k) (s j - x j)‖ ≤ C * r ^ k := by
    intro j
    refine exists_norm_pow_apply_le_of_mem_iSup ?_ hspec
    rw [← hsP j]
    exact Module.End.sub_spectralProjector_mem (s j)
  choose Cf hCf using hC
  refine gap_subspaceIterate_le hxli hM hSspan heig (fun j => ?_) hρ hlρ hr hrρ
    (C := ∑ j, max (Cf j) 0) (fun j k => ?_)
  · exact norm_pos_iff.1 (hρ.trans_le (hlρ j))
  · refine (hCf j k).trans (mul_le_mul_of_nonneg_right ?_ (pow_nonneg hr k))
    exact (le_max_left _ _).trans
      (Finset.single_le_sum (fun i _ => le_max_right (Cf i) 0) (Finset.mem_univ j))

/-- A basis splits the space along every set of indices. Let $(x_i)_{i \in \iota}$ be a linearly
independent family that spans $E$, and let $J \subseteq \iota$. Then
$\operatorname{span}\{x_j : j \in J\}$ and $\operatorname{span}\{x_j : j \notin J\}$ are
complementary subspaces of $E$. -/
theorem isCompl_span_image {ι : Type*} {x : ι → E}
    (hx : LinearIndependent 𝕜 x) (hxtop : Submodule.span 𝕜 (Set.range x) = ⊤) (J : Set ι) :
    IsCompl (Submodule.span 𝕜 (x '' J)) (Submodule.span 𝕜 (x '' Jᶜ)) where
  disjoint := hx.disjoint_span_image disjoint_compl_right
  codisjoint := by
    rw [codisjoint_iff, ← Submodule.span_union, ← Set.image_union, Set.union_compl_self,
      Set.image_univ, hxtop]

/-- If $S$ meets $\operatorname{span}\{x_j : j \notin J\}$ only in $0$ and has the dimension of
$\operatorname{span}\{x_j : j \in J\}$, then the projection onto the second span along the first
maps $S$ onto $\operatorname{span}\{x_j : j \in J\}$. -/
private theorem map_projection_eq [FiniteDimensional 𝕜 E] {ι : Type*} {x : ι → E}
    (hx : LinearIndependent 𝕜 x) (hxtop : Submodule.span 𝕜 (Set.range x) = ⊤) {J : Set ι}
    {S : Submodule 𝕜 E} (hdisj : Disjoint S (Submodule.span 𝕜 (x '' Jᶜ)))
    (hrank : Module.finrank 𝕜 S = Module.finrank 𝕜 ↥(Submodule.span 𝕜 (x '' J))) :
    S.map (Submodule.projection _ _ (isCompl_span_image hx hxtop J))
      = Submodule.span 𝕜 (x '' J) := by
  set Q := Submodule.projection (Submodule.span 𝕜 (x '' J)) (Submodule.span 𝕜 (x '' Jᶜ))
    (isCompl_span_image hx hxtop J) with hQ
  have hker : LinearMap.ker Q = Submodule.span 𝕜 (x '' Jᶜ) := Submodule.ker_projection _
  have hinj : Set.InjOn Q S :=
    LinearMap.injOn_of_disjoint_ker (le_refl (S : Set E)) (by rw [hker]; exact hdisj)
  have hkerc : LinearMap.ker (Q ∘ₗ S.subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    rintro ⟨v, hv⟩ hv0
    simpa using hinj hv (Submodule.zero_mem S) (by simpa using hv0)
  have hrange : LinearMap.range (Q ∘ₗ S.subtype) = S.map Q := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hfin : Module.finrank 𝕜 ↥(S.map Q) = Module.finrank 𝕜 S := by
    have h := (Q ∘ₗ S.subtype).finrank_range_add_finrank_ker
    rw [hkerc, hrange] at h
    simpa using h
  have hle : S.map Q ≤ Submodule.span 𝕜 (x '' J) := by
    rw [← Submodule.range_projection (isCompl_span_image hx hxtop J)]
    exact LinearMap.map_le_range
  exact Submodule.eq_of_le_of_finrank_le hle (by rw [hfin, hrank])

/-- The **subspace-iteration bound** in the form of [kress1998numerical], Lemma 7.18. Let $E$ be a
finite-dimensional inner product space, and let $A$ have an eigenbasis $(x_i)_{i \in \iota}$,
$\iota$ finite, with $Ax_i = \lambda_i x_i$. Let $J \subseteq \iota$ and $0 \le r < \rho$ with
$\rho > 0$, and suppose that $|\lambda_j| \ge \rho$ for $j \in J$ and $|\lambda_j| \le r$ for
$j \notin J$. Let $M = \operatorname{span}\{x_j : j \in J\}$ and
$U = \operatorname{span}\{x_j : j \notin J\}$, and let the starting subspace $S$ satisfy
$S \cap U = 0$ and $\dim S = \dim M$. Then there is a constant $D$ with $$\operatorname{gap}(M,
A^k S) \le D \left(\frac{r}{\rho}\right)^k \quad \text{for all } k.$$

This is `Krylov.gap_subspaceIterate_le` with the data that the hypotheses of
[kress1998numerical] determine. The projection along $U$ carries $S$ bijectively onto $M$
(`Krylov.isCompl_span_image` and a dimension count). So each $x_j$ with $j \in J$ has a unique
preimage $s_j \in S$, the family $(s_j)$ spans $S$, and each $s_j - x_j$ lies in $U$, where the
orbit of $A$ decays like $r^k$ because $U$ is spanned by eigenvectors. Unlike
`Krylov.exists_gap_subspaceIterate_le`, this form needs no spectral projector and no
algebraically closed field: diagonalizability is the given eigenbasis. -/
theorem exists_gap_subspaceIterate_span_image_le [FiniteDimensional 𝕜 E]
    {ι : Type*} [Finite ι] {A : Module.End 𝕜 E} {x : ι → E} {l : ι → 𝕜}
    {J : Set ι} {S : Submodule 𝕜 E} {r ρ : ℝ}
    (hx : LinearIndependent 𝕜 x) (hxtop : Submodule.span 𝕜 (Set.range x) = ⊤)
    (heig : ∀ j, A (x j) = l j • x j)
    (hρ : 0 < ρ) (hJρ : ∀ j ∈ J, ρ ≤ ‖l j‖) (hr : 0 ≤ r) (hrρ : r < ρ)
    (hJr : ∀ k ∉ J, ‖l k‖ ≤ r)
    (hdisj : Disjoint S (Submodule.span 𝕜 (x '' Jᶜ)))
    (hrank : Module.finrank 𝕜 S = Module.finrank 𝕜 ↥(Submodule.span 𝕜 (x '' J))) :
    ∃ D : ℝ, ∀ ν, (Submodule.span 𝕜 (x '' J)).gap (subspaceIterate A S ν) ≤ D * (r / ρ) ^ ν := by
  classical
  cases nonempty_fintype ι
  have hpow : ∀ (i : ι) (ν : ℕ), (A ^ ν) (x i) = l i ^ ν • x i := by
    intro i ν
    induction ν with
    | zero => simp
    | succ ν ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, heig i, smul_smul, ← pow_succ]
  set Q := Submodule.projection (Submodule.span 𝕜 (x '' J)) (Submodule.span 𝕜 (x '' Jᶜ))
    (isCompl_span_image hx hxtop J) with hQ
  have hker : LinearMap.ker Q = Submodule.span 𝕜 (x '' Jᶜ) := Submodule.ker_projection _
  have hmapeq : S.map Q = Submodule.span 𝕜 (x '' J) := map_projection_eq hx hxtop hdisj hrank
  -- the family indexed by `J`
  have hxJ : ∀ j : ↥J, x ↑j ∈ Submodule.span 𝕜 (x '' J) := fun j =>
    Submodule.subset_span ⟨↑j, j.2, rfl⟩
  choose s hsS hsQ using fun j : ↥J => Submodule.mem_map.1 (hmapeq ▸ hxJ j)
  have hxli : LinearIndependent 𝕜 fun j : ↥J => x ↑j := hx.comp _ Subtype.val_injective
  have hrangex : Set.range (fun j : ↥J => x ↑j) = x '' J := by
    rw [← Set.image_eq_range]
  have hsli : LinearIndependent 𝕜 s := by
    have hcomp : LinearIndependent 𝕜 fun j : ↥J => Q (s j) := by
      simpa only [hsQ] using hxli
    exact hcomp.of_comp Q
  have hcardJ : Module.finrank 𝕜 ↥(Submodule.span 𝕜 (Set.range s)) = Fintype.card ↥J :=
    finrank_span_eq_card hsli
  have hSspan : S = Submodule.span 𝕜 (Set.range s) := by
    refine (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm
    · exact Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hsS j)
    · rw [hcardJ, hrank, ← hrangex, finrank_span_eq_card hxli]
  -- the decay of each discrepancy
  have hdecay : ∀ j : ↥J, ∃ C : ℝ, ∀ ν, ‖(A ^ ν) (s j - x ↑j)‖ ≤ C * r ^ ν := by
    intro j
    have hmem : s j - x ↑j ∈ Submodule.span 𝕜 (x '' Jᶜ) := by
      rw [← hker, LinearMap.mem_ker, map_sub, hsQ j,
        Submodule.projection_apply_of_mem_left _ (hxJ j), sub_self]
    have hrangec : Submodule.span 𝕜 (Set.range fun k : ↥(Jᶜ) => x ↑k)
        = Submodule.span 𝕜 (x '' Jᶜ) := by
      rw [← Set.image_eq_range]
    rw [← hrangec] at hmem
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).1 hmem
    refine ⟨∑ k : ↥(Jᶜ), ‖c k‖ * ‖x ↑k‖, fun ν => ?_⟩
    rw [← hc, map_sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [map_smul, hpow ↑k ν, smul_smul, norm_smul, norm_mul, norm_pow]
    calc ‖c k‖ * ‖l ↑k‖ ^ ν * ‖x ↑k‖ ≤ ‖c k‖ * r ^ ν * ‖x ↑k‖ := by
          gcongr
          exact hJr ↑k k.2
      _ = ‖c k‖ * ‖x ↑k‖ * r ^ ν := by ring
  choose Cf hCf using hdecay
  refine gap_subspaceIterate_le hxli (congrArg (Submodule.span 𝕜) hrangex.symm) hSspan
    (fun j => heig ↑j) (fun j => ?_) hρ (fun j => hJρ ↑j j.2) hr hrρ
    (C := ∑ j : ↥J, max (Cf j) 0) (fun j ν => ?_)
  · exact norm_pos_iff.1 (hρ.trans_le (hJρ ↑j j.2))
  · refine (hCf j ν).trans (mul_le_mul_of_nonneg_right ?_ (pow_nonneg hr ν))
    exact (le_max_left _ _).trans
      (Finset.single_le_sum (fun i _ => le_max_right (Cf i) 0) (Finset.mem_univ j))

end SubspaceIteration

section Conjugation

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The power method commutes with a change of orthonormal coordinates. Let $U : F \to E$ be a
linear isometric equivalence of normed spaces, let $A$ be an endomorphism of $E$ and let
$x_0 \in E$. Then the power iterates of $U^{-1} A U$ from $U^{-1} x_0$ are the images under
$U^{-1}$ of the power iterates of $A$ from $x_0$: $$q_k(U^{-1} A U, U^{-1} x_0) = U^{-1} q_k(A,
x_0).$$

The reason is that $(U^{-1} A U)^k = U^{-1} A^k U$ and that $U$ preserves norms. This is what
lets [quarteroni2000numerical], §5.8.1, run the iteration on the Hessenberg form $H = Q^H A Q$
and recover the eigenvector of $A$ as $x = Qq$. The operator $U^{-1} A U$ is
`U.symm.toLinearEquiv.conj A`. -/
theorem powerIterate_conj_linearIsometryEquiv (U : F ≃ₗᵢ[𝕜] E) (A : Module.End 𝕜 E) (x₀ : E)
    (k : ℕ) :
    powerIterate (U.symm.toLinearEquiv.conj A) (U.symm x₀) k = U.symm (powerIterate A x₀ k) := by
  have hpow : ∀ j : ℕ, ((U.symm.toLinearEquiv.conj A) ^ j) (U.symm x₀) = U.symm ((A ^ j) x₀) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply,
        LinearEquiv.conj_apply_apply]
      simp
  rw [powerIterate, powerIterate, hpow, map_smul, LinearIsometryEquiv.norm_map]

/-- Inverse iteration commutes with a change of orthonormal coordinates. Let $U : F \to E$ be a
linear isometric equivalence of normed spaces, let $A$ be an endomorphism of $E$, let $\sigma$
be a scalar and let $x_0 \in E$. Then the inverse iterates of $U^{-1} A U$ with shift $\sigma$
from $U^{-1} x_0$ are the images under $U^{-1}$ of the inverse iterates of $A$ with shift
$\sigma$ from $x_0$.

The shifted inverse is conjugated along by `LinearEquiv.conj_ringInverse`. This justifies
inverse iteration on a Hessenberg or tridiagonal form, as in [quarteroni2000numerical], §5.8.1. -/
theorem inverseIterate_conj_linearIsometryEquiv (U : F ≃ₗᵢ[𝕜] E) (A : Module.End 𝕜 E) (σ : 𝕜)
    (x₀ : E) (k : ℕ) :
    inverseIterate (U.symm.toLinearEquiv.conj A) σ (U.symm x₀) k
      = U.symm (inverseIterate A σ x₀ k) := by
  have h1 : U.symm.toLinearEquiv.conj (1 : Module.End 𝕜 E) = 1 := LinearEquiv.conj_id _
  rw [inverseIterate, inverseIterate, ← powerIterate_conj_linearIsometryEquiv,
    LinearEquiv.conj_ringInverse, map_sub, map_smul, h1]

end Conjugation

section Eigenbasis

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The **rate of the power method for a diagonalizable operator**. Let $E$ be a normed space, and
let $(x_i)_{i \in \iota}$ be a finite family of unit vectors with $Ax_i = \lambda_i x_i$. Let
$i_0 \in \iota$ with $\lambda_{i_0} \neq 0$, and let $|\lambda_i| \le \rho$ for $i \neq i_0$.
Let $x_0 = \sum_i \alpha_i x_i$ with $\alpha_{i_0} \neq 0$. Then for every $k$, $$\left\|
(\alpha_{i_0} \lambda_{i_0}^k)^{-1} A^k x_0 - x_{i_0} \right\| \le \Bigl(\sum_{i \neq i_0}
\Bigl|\frac{\alpha_i}{\alpha_{i_0}}\Bigr|\Bigr) \left(\frac{\rho}{|\lambda_{i_0}|}\right)^k.$$
This is Theorem 5.6 of [quarteroni2000numerical].

The constant is the one that the triangle inequality gives. The constant
$(\sum_i (\alpha_i/\alpha_1)^2)^{1/2}$ of the source needs the $x_i$ orthonormal, that is, a
normal $A$. The family $(x_i)$ need not be linearly independent.
`Krylov.exists_norm_inv_pow_smul_pow_apply_sub_le` gives the same rate with any $r > \rho$ in
place of $\rho$ and without an eigenbasis. -/
theorem norm_inv_pow_smul_pow_apply_sub_le_of_eigenbasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Module.End 𝕜 E} {x : ι → E} {l : ι → 𝕜} (hx : ∀ i, A (x i) = l i • x i)
    (hx1 : ∀ i, ‖x i‖ = 1) {i₀ : ι} (hl₀ : l i₀ ≠ 0) {ρ : ℝ} (hρ : ∀ i, i ≠ i₀ → ‖l i‖ ≤ ρ)
    {α : ι → 𝕜} (hα : α i₀ ≠ 0) {x₀ : E} (hx₀ : x₀ = ∑ i, α i • x i) (k : ℕ) :
    ‖(α i₀ * l i₀ ^ k)⁻¹ • (A ^ k) x₀ - x i₀‖
      ≤ (∑ i ∈ Finset.univ.erase i₀, ‖α i / α i₀‖) * (ρ / ‖l i₀‖) ^ k := by
  have hpow : ∀ i, (A ^ k) (x i) = l i ^ k • x i := fun i => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, hx, smul_smul, ← pow_succ]
  have hne : α i₀ * l i₀ ^ k ≠ 0 := mul_ne_zero hα (pow_ne_zero k hl₀)
  have hexp : (α i₀ * l i₀ ^ k)⁻¹ • (A ^ k) x₀ - x i₀
      = ∑ i ∈ Finset.univ.erase i₀, ((α i / α i₀) * (l i / l i₀) ^ k) • x i := by
    rw [hx₀, map_sum, Finset.smul_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀),
      map_smul, hpow, smul_smul, smul_smul, mul_assoc, inv_mul_cancel₀ hne, one_smul,
      add_sub_cancel_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hpow, smul_smul, smul_smul]
    congr 1
    rw [div_pow, mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [hexp, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [norm_smul, hx1, mul_one, norm_mul, norm_pow, norm_div, norm_div]
  gcongr
  exact hρ i (Finset.ne_of_mem_erase hi)

end Eigenbasis

section RayleighQuotient

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Let $E$ be an inner product space, let $A$ be continuous, and let $u$ be a unit eigenvector:
$Au = \lambda u$ and $\|u\| = 1$. Let $(q_k)$ be vectors and $(c_k)$ scalars with $|c_k| = 1$
and $c_k q_k \to u$. Then the Rayleigh quotients converge to the eigenvalue: $$\langle q_k, A
q_k \rangle \to \lambda.$$

A factor of modulus one does not change $\langle q, A q \rangle$, and
$\langle u, A u \rangle = \lambda$ for a unit eigenvector. -/
theorem tendsto_inner_apply_of_tendsto_smul {A : Module.End 𝕜 E} (hA : Continuous A) {l : 𝕜}
    {u : E} (hu : A u = l • u) (hu1 : ‖u‖ = 1) {q : ℕ → E} {c : ℕ → 𝕜} (hc : ∀ k, ‖c k‖ = 1)
    (hq : Tendsto (fun k => c k • q k) atTop (𝓝 u)) :
    Tendsto (fun k => (inner 𝕜 (q k) (A (q k)) : 𝕜)) atTop (𝓝 l) := by
  have hcont : Continuous fun v : E => (inner 𝕜 v (A v) : 𝕜) := continuous_id.inner hA
  have hlim := (hcont.tendsto u).comp hq
  have hval : (inner 𝕜 u (A u) : 𝕜) = l := by
    rw [hu, inner_smul_right, inner_self_eq_norm_sq_to_K, hu1]
    simp
  have heq : ∀ k, (inner 𝕜 (c k • q k) (A (c k • q k)) : 𝕜) = inner 𝕜 (q k) (A (q k)) := by
    intro k
    rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, RCLike.conj_mul, hc k]
    simp
  simpa only [Function.comp_def, heq, hval] using hlim

/-- **Convergence of the Rayleigh quotients of the power method.** Let $E$ be an inner product
space, let $A$ be continuous, let $\lambda \neq 0$ be strictly dominant for $A$, and let
$x_0 = u + w$ with $Au = \lambda u$, $u \neq 0$ and $w \in G_{\neq\lambda}(A)$. Then the
Rayleigh quotients of the power iterates converge to $\lambda$: $$\langle q_k, A q_k \rangle \to
\lambda.$$ This is Theorem 5.6 of [quarteroni2000numerical] and the remark after it. -/
theorem tendsto_inner_powerIterate {A : Module.End 𝕜 E} (hA : Continuous A) {l : 𝕜} {u w x₀ : E}
    (hl : l ≠ 0) (hu : A u = l • u) (hu0 : u ≠ 0)
    (hw : w ∈ A.spectralSubspace (· ≠ l))
    (hdom : A.IsStrictlyDominant l) (hx₀ : x₀ = u + w) :
    Tendsto (fun k => (inner 𝕜 (powerIterate A x₀ k) (A (powerIterate A x₀ k)) : 𝕜)) atTop
      (𝓝 l) := by
  obtain ⟨c, hc, hlim⟩ := exists_norm_eq_one_tendsto_smul_powerIterate hl hu hu0 hw hdom hx₀
  have hun : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu0
  refine tendsto_inner_apply_of_tendsto_smul hA (u := (‖u‖ : 𝕜)⁻¹ • u) ?_ ?_ hc hlim
  · rw [map_smul, hu, smul_comm]
  · rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg u),
      inv_mul_cancel₀ hun]

/-- **Essential convergence of the power method, with dominance only over the components present.**
Let $E$ be an inner product space, let $A$ be continuous, and let $p$ be a predicate on scalars.
Let $x_0 = u + w$ with $Au = \lambda u$, $u \neq 0$, $\lambda \neq 0$ and $w \in G_p(A)$. Let
$0 \le r < |\lambda|$ with $|\mu| < r$ for every eigenvalue $\mu$ of $A$ with $p(\mu)$. Then
$$\left(\frac{|\lambda|}{\lambda}\right)^k q_k \to \frac{u}{\|u\|} \quad \text{and} \quad
\langle q_k, A q_k \rangle \to \lambda.$$

Unlike `Krylov.tendsto_smul_powerIterate` and `Krylov.tendsto_inner_powerIterate`, the dominance
hypothesis quantifies only over the eigenvalues whose generalized eigenvectors occur in $w$.
This is the form for a starting vector with no component along the eigenvectors of the dominant
eigenvalues of $A$. -/
theorem tendsto_smul_powerIterate_of_mem_iSup {A : Module.End 𝕜 E} (hA : Continuous A) {l : 𝕜}
    {u w x₀ : E} {p : 𝕜 → Prop} (hl : l ≠ 0) (hu : A u = l • u) (hu0 : u ≠ 0)
    (hw : w ∈ A.spectralSubspace p) {r : ℝ} (hr0 : 0 ≤ r) (hrl : r < ‖l‖)
    (hdom : ∀ μ, p μ → A.HasEigenvalue μ → ‖μ‖ < r) (hx₀ : x₀ = u + w) :
    Tendsto (fun k => ((‖l‖ : 𝕜) / l) ^ k • powerIterate A x₀ k) atTop
        (𝓝 ((‖u‖ : 𝕜)⁻¹ • u)) ∧
      Tendsto (fun k => (inner 𝕜 (powerIterate A x₀ k) (A (powerIterate A x₀ k)) : 𝕜))
        atTop (𝓝 l) := by
  have hl0 : (0 : ℝ) < ‖l‖ := norm_pos_iff.mpr hl
  obtain ⟨C, hC⟩ := exists_norm_pow_apply_le_of_mem_iSup hw hdom
  set z : ℕ → E := fun k => (l ^ k)⁻¹ • (A ^ k) x₀ with hz
  -- the scaled iterates converge to `u`
  have hzt : Tendsto z atTop (𝓝 u) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (g := fun k => C * (r / ‖l‖) ^ k) (fun k => norm_nonneg _)
      (fun k => ?_) ?_
    · change ‖(l ^ k)⁻¹ • (A ^ k) x₀ - u‖ ≤ C * (r / ‖l‖) ^ k
      rw [hx₀]
      exact norm_inv_pow_smul_pow_apply_sub_le hl hu hC k
    · rw [← mul_zero C]
      exact (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hr0 hl0.le)
        ((div_lt_one hl0).mpr hrl)).const_mul C
  -- normalizing
  have hcnorm : ∀ k, ‖((‖l‖ : 𝕜) / l) ^ k‖ = 1 := fun k => by
    rw [norm_pow, norm_div, RCLike.norm_ofReal, abs_norm, div_self hl0.ne', one_pow]
  have hlim := tendsto_smul_powerIterate_of_tendsto hl hu0 hzt
  refine ⟨hlim, ?_⟩
  have hun : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu0
  refine tendsto_inner_apply_of_tendsto_smul hA (u := (‖u‖ : 𝕜)⁻¹ • u) ?_ ?_ hcnorm hlim
  · rw [map_smul, hu, smul_comm]
  · rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg u),
      inv_mul_cancel₀ hun]

/-- **Convergence of the Rayleigh quotients of inverse iteration** to the eigenvalue nearest the
shift. Let $E$ be an inner product space, let $A$ be continuous, and let $A - \sigma I$ be
invertible. Let $|\lambda - \sigma| < |\mu - \sigma|$ for every eigenvalue $\mu \neq \lambda$ of
$A$, and let $x_0 = u + w$ with $Au = \lambda u$, $u \neq 0$ and $w \in G_{\neq\lambda}(A)$.
Then the Rayleigh quotients of $A$ at the inverse iterates $q_k$ converge to $\lambda$:
$$\langle q_k, A q_k \rangle \to \lambda.$$ This is (5.28) of [quarteroni2000numerical],
$\sigma^{(k)} \to \lambda_m$.

The Rayleigh quotients are computed with $A$ itself, not with the shifted inverse. -/
theorem tendsto_inner_inverseIterate {A : Module.End 𝕜 E} (hA : Continuous A) {σ l : 𝕜}
    {u w x₀ : E} (hσ : IsUnit (A - σ • (1 : Module.End 𝕜 E))) (hu : A u = l • u) (hu0 : u ≠ 0)
    (hw : w ∈ A.spectralSubspace (· ≠ l))
    (hdom : ∀ μ, μ ≠ l → A.HasEigenvalue μ → ‖l - σ‖ < ‖μ - σ‖) (hx₀ : x₀ = u + w) :
    Tendsto (fun k => (inner 𝕜 (inverseIterate A σ x₀ k) (A (inverseIterate A σ x₀ k)) : 𝕜))
      atTop (𝓝 l) := by
  have hlim := tendsto_smul_inverseIterate hσ hu hu0 hw hdom hx₀
  have hlσ : l - σ ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    subst h
    obtain ⟨V, hV⟩ := hσ.exists_left_inv
    have h0 : (A - l • (1 : Module.End 𝕜 E)) u = 0 := by simp [hu]
    have := congrArg V h0
    rw [← Module.End.mul_apply, hV, Module.End.one_apply, map_zero] at this
    exact hu0 this
  have hun : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu0
  have hc : ∀ k : ℕ, ‖((l - σ) / (‖l - σ‖ : 𝕜)) ^ k‖ = 1 := fun k => by
    rw [norm_pow, norm_div, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.mpr hlσ), one_pow]
  refine tendsto_inner_apply_of_tendsto_smul hA (u := (‖u‖ : 𝕜)⁻¹ • u) ?_ ?_ hc hlim
  · rw [map_smul, hu, smul_comm]
  · rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg u),
      inv_mul_cancel₀ hun]

end RayleighQuotient

end Krylov

namespace LinearMap.IsSymmetric

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
include hA

/-- Let $A$ be a symmetric operator on an inner product space $E$ of finite dimension $n$, with the
orthonormal eigenvector basis $(u_i)$ and the eigenvalues $\lambda_i$ of
`LinearMap.IsSymmetric.eigenvectorBasis` and `LinearMap.IsSymmetric.eigenvalues`. Then the
coordinates of $A^k x$ in this basis are those of $x$ multiplied by $\lambda_i^k$: $$[A^k x]_i =
\lambda_i^k \, [x]_i.$$
-/
theorem repr_pow_apply {n : ℕ} (hn : Module.finrank 𝕜 E = n) (x : E) (k : ℕ) (i : Fin n) :
    (hA.eigenvectorBasis hn).repr ((A ^ k) x) i
      = (hA.eigenvalues hn i : 𝕜) ^ k * (hA.eigenvectorBasis hn).repr x i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, hA.eigenvectorBasis_apply_self_apply hn, ih, pow_succ']
    ring

omit [FiniteDimensional 𝕜 E] in
/-- Let $A$ be a symmetric operator on an inner product space $E$. The Rayleigh quotient of the
power iterate $q_k$ is the Rayleigh quotient of $A^k x_0$: $$\operatorname{Re} \langle q_k, A
q_k \rangle = \frac{\operatorname{Re} \langle A^{k+1} x_0, A^k x_0 \rangle}{\|A^k x_0\|^2}.$$
Both sides are $0$ when $A^k x_0 = 0$, and $E$ need not be finite-dimensional. -/
theorem re_inner_powerIterate_eq_div (x₀ : E) (k : ℕ) :
    RCLike.re (inner 𝕜 (Krylov.powerIterate A x₀ k) (A (Krylov.powerIterate A x₀ k)))
      = RCLike.re (inner 𝕜 (A ((A ^ k) x₀)) ((A ^ k) x₀)) / ‖(A ^ k) x₀‖ ^ 2 := by
  set y := (A ^ k) x₀ with hy
  rcases eq_or_ne y 0 with h0 | h0
  · rw [(Krylov.powerIterate_eq_zero_iff A x₀ k).mpr h0, h0]
    simp
  have hq : Krylov.powerIterate A x₀ k = ((‖y‖⁻¹ : ℝ) : 𝕜) • y := by
    rw [Krylov.powerIterate, RCLike.ofReal_inv]
  rw [hq, map_smul, inner_smul_left, inner_smul_right, RCLike.conj_ofReal, ← mul_assoc,
    ← RCLike.ofReal_mul, RCLike.re_ofReal_mul, ← hA y y, div_eq_mul_inv, sq, mul_inv]
  ring

end LinearMap.IsSymmetric

namespace Krylov

section EigenbasisRate

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Normalizing a vector at most doubles its distance to a unit vector. If $\|u\| = 1$, then for
every $v$, $$\bigl\| \|v\|^{-1} v - u \bigr\| \le 2 \|v - u\|,$$ where $\|v\|^{-1} v = 0$ for
$v = 0$. -/
theorem _root_.norm_inv_norm_smul_sub_le {u v : E} (hu : ‖u‖ = 1) :
    ‖((‖v‖⁻¹ : ℝ) : 𝕜) • v - u‖ ≤ 2 * ‖v - u‖ := by
  have h1 : ‖((‖v‖⁻¹ : ℝ) : 𝕜) • v - v‖ ≤ ‖v - u‖ := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv
    have h : ((‖v‖⁻¹ : ℝ) : 𝕜) • v - v = ((‖v‖⁻¹ - 1 : ℝ) : 𝕜) • v := by
      rw [RCLike.ofReal_sub, sub_smul, RCLike.ofReal_one, one_smul]
    rw [h, norm_smul, RCLike.norm_ofReal,
      show ‖v‖⁻¹ - 1 = (1 - ‖v‖) / ‖v‖ by field_simp, abs_div, abs_of_pos hv',
      div_mul_cancel₀ _ hv'.ne', ← hu, norm_sub_rev v u]
    exact abs_norm_sub_norm_le u v
  calc ‖((‖v‖⁻¹ : ℝ) : 𝕜) • v - u‖ ≤ ‖((‖v‖⁻¹ : ℝ) : 𝕜) • v - v‖ + ‖v - u‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * ‖v - u‖ := by linarith

/-- Let $a \neq 0$ and $A^k x_0 = a v$. Then the power iterate multiplied by $|a|/a$ is the
normalization of $v$: $$\frac{|a|}{a} q_k = \|v\|^{-1} v.$$ It is used with
$a = \alpha_{i_0} \lambda_{i_0}^k$. -/
theorem smul_powerIterate_eq_of_eq_smul {A : Module.End 𝕜 E} {x₀ v : E} {a : 𝕜} {k : ℕ}
    (ha : a ≠ 0) (h : (A ^ k) x₀ = a • v) :
    ((‖a‖ : 𝕜) / a) • powerIterate A x₀ k = ((‖v‖⁻¹ : ℝ) : 𝕜) • v := by
  rw [powerIterate_eq_smul, h, smul_smul, smul_smul, norm_smul]
  congr 1
  have ha' : (‖a‖ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 (norm_ne_zero_iff.2 ha)
  rcases eq_or_ne ‖v‖ 0 with hv | hv
  · simp [hv]
  have hv' : (‖v‖ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hv
  push_cast
  field_simp

/-- Let $(x_i)$, $i_0$, $\rho$ and $x_0 = \sum_i \alpha_i x_i$ satisfy the hypotheses of
`Krylov.norm_inv_pow_smul_pow_apply_sub_le_of_eigenbasis`, and let $c_k = |\alpha_{i_0}
\lambda_{i_0}^k| / (\alpha_{i_0} \lambda_{i_0}^k)$, a scalar of modulus one. Then for every $k$,
$$\|c_k q_k - x_{i_0}\| \le 2 \Bigl(\sum_{i \neq i_0}
\Bigl|\frac{\alpha_i}{\alpha_{i_0}}\Bigr|\Bigr) \left(\frac{\rho}{|\lambda_{i_0}|}\right)^k.$$
The factor $2$ is the cost of the normalization (`norm_inv_norm_smul_sub_le`). -/
theorem norm_smul_powerIterate_sub_le_of_eigenbasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Module.End 𝕜 E} {x : ι → E} {l : ι → 𝕜} (hx : ∀ i, A (x i) = l i • x i)
    (hx1 : ∀ i, ‖x i‖ = 1) {i₀ : ι} (hl₀ : l i₀ ≠ 0) {ρ : ℝ} (hρ : ∀ i, i ≠ i₀ → ‖l i‖ ≤ ρ)
    {α : ι → 𝕜} (hα : α i₀ ≠ 0) {x₀ : E} (hx₀ : x₀ = ∑ i, α i • x i) (k : ℕ) :
    ‖((‖α i₀ * l i₀ ^ k‖ : 𝕜) / (α i₀ * l i₀ ^ k)) • powerIterate A x₀ k - x i₀‖
      ≤ 2 * (∑ i ∈ Finset.univ.erase i₀, ‖α i / α i₀‖) * (ρ / ‖l i₀‖) ^ k := by
  have hne : α i₀ * l i₀ ^ k ≠ 0 := mul_ne_zero hα (pow_ne_zero k hl₀)
  set v := (α i₀ * l i₀ ^ k)⁻¹ • (A ^ k) x₀ with hv
  have hAv : (A ^ k) x₀ = (α i₀ * l i₀ ^ k) • v := by
    rw [hv, smul_smul, mul_inv_cancel₀ hne, one_smul]
  rw [smul_powerIterate_eq_of_eq_smul hne hAv, mul_assoc]
  refine (_root_.norm_inv_norm_smul_sub_le (hx1 i₀)).trans ?_
  gcongr
  exact norm_inv_pow_smul_pow_apply_sub_le_of_eigenbasis hx hx1 hl₀ hρ hα hx₀ k

end EigenbasisRate

section EigenbasisInner

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Let $q$ be a unit vector, let $u$ be a vector, and let $c$ be a scalar with $|c| = 1$. Then the
sine of the angle between $q$ and the line $\mathbb{K} u$ is at most $\|c q - u\|$. The reason
is that $P_{\mathbb{K} u} q$ is the best approximation of $q$ from the line, and $c^{-1} u$ lies
on the line. -/
theorem _root_.Submodule.sinAngle_span_singleton_le_norm_smul_sub {u q : E} (hq : ‖q‖ = 1) {c : 𝕜}
    (hc : ‖c‖ = 1) : (𝕜 ∙ u).sinAngle q ≤ ‖c • q - u‖ := by
  have hc0 : c ≠ 0 := norm_ne_zero_iff.1 (by rw [hc]; exact one_ne_zero)
  have hmem : c⁻¹ • u ∈ (𝕜 ∙ u) := Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
  have h := (isBestApprox_starProjection (𝕜 ∙ u) q).2 _ hmem
  have heq : ‖q - c⁻¹ • u‖ = ‖c • q - u‖ := by
    rw [← one_mul ‖q - c⁻¹ • u‖, ← hc, ← norm_smul, smul_sub, smul_smul, mul_inv_cancel₀ hc0,
      one_smul]
  have hs := (𝕜 ∙ u).sinAngle_mul_norm q
  rw [hq, mul_one] at hs
  rw [hs]
  exact h.trans heq.le

/-- The **rate of convergence of the eigendirection** in the power method with an eigenbasis. Let
$E$ be an inner product space, and let $(x_i)_{i \in \iota}$ be a finite family of unit vectors
with $Ax_i = \lambda_i x_i$. Let $i_0 \in \iota$ with $\lambda_{i_0} \neq 0$, and let
$|\lambda_i| \le \rho$ for $i \neq i_0$. Let $x_0 = \sum_i \alpha_i x_i$ with
$\alpha_{i_0} \neq 0$, and let $c_k = |\alpha_{i_0} \lambda_{i_0}^k| / (\alpha_{i_0}
\lambda_{i_0}^k)$. Then there is a constant $C$ such that for every $k$, $$\|c_k q_k - x_{i_0}\|
\le C \left(\frac{\rho}{|\lambda_{i_0}|}\right)^k \quad \text{and} \quad \sin\theta(q_k,
\mathbb{K} x_{i_0}) \le C \left(\frac{\rho}{|\lambda_{i_0}|}\right)^k.$$ This is the bound
$\operatorname{dist}(\operatorname{span}\{q^{(k)}\}, \operatorname{span}\{x_1\}) =
O(|\lambda_2/\lambda_1|^k)$ of [golub2013matrix], §7.3.1.

The sine of the angle between a vector and a subspace is `Submodule.sinAngle`. The constant is
$C = 2 \sum_{i \neq i_0} |\alpha_i/\alpha_{i_0}|$
(`Krylov.norm_smul_powerIterate_sub_le_of_eigenbasis`). -/
theorem exists_norm_sub_smul_powerIterate_le_of_eigenbasis {ι : Type*} [Fintype ι]
    {A : Module.End 𝕜 E} {x : ι → E} {l : ι → 𝕜}
    (hx : ∀ i, A (x i) = l i • x i) (hx1 : ∀ i, ‖x i‖ = 1) {i₀ : ι} (hl₀ : l i₀ ≠ 0) {ρ : ℝ}
    (hρ : ∀ i, i ≠ i₀ → ‖l i‖ ≤ ρ) {α : ι → 𝕜} (hα : α i₀ ≠ 0) {x₀ : E}
    (hx₀ : x₀ = ∑ i, α i • x i) :
    ∃ C : ℝ, ∀ k,
      ‖((‖α i₀ * l i₀ ^ k‖ : 𝕜) / (α i₀ * l i₀ ^ k)) • powerIterate A x₀ k - x i₀‖
          ≤ C * (ρ / ‖l i₀‖) ^ k ∧
        (𝕜 ∙ x i₀).sinAngle (powerIterate A x₀ k) ≤ C * (ρ / ‖l i₀‖) ^ k := by
  classical
  refine ⟨2 * ∑ i ∈ Finset.univ.erase i₀, ‖α i / α i₀‖, fun k => ?_⟩
  have h := norm_smul_powerIterate_sub_le_of_eigenbasis hx hx1 hl₀ hρ hα hx₀ k
  refine ⟨h, ?_⟩
  rcases eq_or_ne ((A ^ k) x₀) 0 with h0 | h0
  · rw [(powerIterate_eq_zero_iff A x₀ k).2 h0, Submodule.sinAngle_zero]
    rw [(powerIterate_eq_zero_iff A x₀ k).2 h0, smul_zero, zero_sub, norm_neg, hx1] at h
    linarith
  have hne : α i₀ * l i₀ ^ k ≠ 0 := mul_ne_zero hα (pow_ne_zero k hl₀)
  have hc : ‖((‖α i₀ * l i₀ ^ k‖ : 𝕜) / (α i₀ * l i₀ ^ k))‖ = 1 := by
    rw [norm_div, RCLike.norm_ofReal, abs_norm, div_self (norm_ne_zero_iff.2 hne)]
  exact (Submodule.sinAngle_span_singleton_le_norm_smul_sub (norm_powerIterate_of_ne_zero A x₀ k h0)
    hc).trans h

/-- The **rate of convergence of the Rayleigh quotient** in the power method with an eigenbasis. Let
$E$ be an inner product space, let $A$ be continuous, and let $(x_i)_{i \in \iota}$ be a finite
family of unit vectors with $Ax_i = \lambda_i x_i$. Let $i_0 \in \iota$ with
$\lambda_{i_0} \neq 0$, let $|\lambda_i| \le \rho$ for $i \neq i_0$, and let
$x_0 = \sum_i \alpha_i x_i$ with $\alpha_{i_0} \neq 0$. Then there is a constant $C$ with
$$|\langle q_k, A q_k \rangle - \lambda_{i_0}| \le C \left(\frac{\rho}{|\lambda_{i_0}|}\right)^k
\quad \text{for all } k.$$ This is a rigorous form of (7.3.5) of [golub2013matrix]; the bound
$O(|\lambda_2/\lambda_1|^k)$ of the source is the case $\rho = |\lambda_2|$.

The Rayleigh quotient does not change under a factor of modulus one, and it is Lipschitz in $q$
near the unit eigenvector $x_{i_0}$, by $\langle q, A q \rangle - \langle x, A x \rangle =
\langle q - x, A q \rangle + \langle x, A (q - x) \rangle$. -/
theorem exists_norm_inner_powerIterate_sub_le_of_eigenbasis {ι : Type*} [Fintype ι]
    {A : Module.End 𝕜 E} (hA : Continuous A) {x : ι → E} {l : ι → 𝕜}
    (hx : ∀ i, A (x i) = l i • x i) (hx1 : ∀ i, ‖x i‖ = 1) {i₀ : ι} (hl₀ : l i₀ ≠ 0) {ρ : ℝ}
    (hρ : ∀ i, i ≠ i₀ → ‖l i‖ ≤ ρ) {α : ι → 𝕜} (hα : α i₀ ≠ 0) {x₀ : E}
    (hx₀ : x₀ = ∑ i, α i • x i) :
    ∃ C : ℝ, ∀ k, ‖(inner 𝕜 (powerIterate A x₀ k) (A (powerIterate A x₀ k)) : 𝕜) - l i₀‖
      ≤ C * (ρ / ‖l i₀‖) ^ k := by
  classical
  set A' : E →L[𝕜] E := { toLinearMap := A, cont := hA }
  have hA' : ∀ y, ‖A y‖ ≤ ‖A'‖ * ‖y‖ := fun y => A'.le_opNorm y
  set C₁ := 2 * ∑ i ∈ Finset.univ.erase i₀, ‖α i / α i₀‖
  refine ⟨2 * ‖A'‖ * C₁, fun k => ?_⟩
  set q := powerIterate A x₀ k
  set c : 𝕜 := (‖α i₀ * l i₀ ^ k‖ : 𝕜) / (α i₀ * l i₀ ^ k)
  set u := x i₀
  have hne : α i₀ * l i₀ ^ k ≠ 0 := mul_ne_zero hα (pow_ne_zero k hl₀)
  have hc : ‖c‖ = 1 := by
    rw [norm_div, RCLike.norm_ofReal, abs_norm, div_self (norm_ne_zero_iff.2 hne)]
  have hd : ‖c • q - u‖ ≤ C₁ * (ρ / ‖l i₀‖) ^ k :=
    norm_smul_powerIterate_sub_le_of_eigenbasis hx hx1 hl₀ hρ hα hx₀ k
  set w := c • q
  have hw : ‖w‖ ≤ 1 := by
    rw [norm_smul, hc, one_mul]; exact norm_powerIterate_le_one A x₀ k
  have hu1 : ‖u‖ = 1 := hx1 i₀
  -- invariance of the Rayleigh quotient under the unimodular factor
  have hinv : (inner 𝕜 w (A w) : 𝕜) = inner 𝕜 q (A q) := by
    rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, RCLike.conj_mul, hc]
    simp
  have hval : (inner 𝕜 u (A u) : 𝕜) = l i₀ := by
    rw [hx, inner_smul_right, inner_self_eq_norm_sq_to_K, hu1]
    simp
  have hsplit : (inner 𝕜 w (A w) : 𝕜) - inner 𝕜 u (A u)
      = inner 𝕜 (w - u) (A w) + inner 𝕜 u (A (w - u)) := by
    rw [inner_sub_left, map_sub, inner_sub_right]
    ring
  have heq : (inner 𝕜 q (A q) : 𝕜) - l i₀ = inner 𝕜 (w - u) (A w) + inner 𝕜 u (A (w - u)) := by
    rw [← hinv, ← hval, hsplit]
  rw [heq]
  calc ‖(inner 𝕜 (w - u) (A w) : 𝕜) + inner 𝕜 u (A (w - u))‖
      ≤ ‖w - u‖ * ‖A w‖ + ‖u‖ * ‖A (w - u)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _))
    _ ≤ ‖w - u‖ * (‖A'‖ * 1) + 1 * (‖A'‖ * ‖w - u‖) := by
        gcongr
        · exact (hA' w).trans (by gcongr)
        · exact hu1.le
        · exact hA' _
    _ = 2 * ‖A'‖ * ‖w - u‖ := by ring
    _ ≤ 2 * ‖A'‖ * (C₁ * (ρ / ‖l i₀‖) ^ k) := by gcongr
    _ = 2 * ‖A'‖ * C₁ * (ρ / ‖l i₀‖) ^ k := by ring

/-! ### An orthonormal eigenbasis -/

variable {ι : Type*} [Fintype ι] {A : Module.End 𝕜 E}

/-- The **angle bound of the power method**. Let $E$ be an inner product space, let
$(v_i)_{i \in \iota}$ be an orthonormal basis of $E$ with $Av_i = \lambda_i v_i$, let
$i_0 \in \iota$ with $\lambda_{i_0} \neq 0$, and let $|\lambda_i| \le \rho$ for $i \neq i_0$.
Let $x_0$ be a unit vector with $c = |\langle v_{i_0}, x_0 \rangle| \neq 0$, so that
$c = \cos\theta_0$. Then for every $k$, $$\sin\theta(q_k, \mathbb{K} v_{i_0}) \le
\frac{\sqrt{1 - c^2}}{c} \left(\frac{\rho}{|\lambda_{i_0}|}\right)^k,$$ which is
$\tan\theta_0 \, |\lambda_2/\lambda_1|^k$ in the notation of the source. This is (8.2.4) in
Theorem 8.2.1 of [golub2013matrix].

The eigenvalues may be complex, so $A$ may be any normal operator with an orthonormal
eigenbasis; the source treats the symmetric case, where they are real. The proof follows the
source: $A^k x_0 = \sum_i a_i \lambda_i^k v_i$, and its distance to the line is at most its
distance to $a_{i_0} \lambda_{i_0}^k v_{i_0}$, which is $(\sum_{i \neq i_0} |a_i|^2
|\lambda_i|^{2k})^{1/2} \le \rho^k \sqrt{1 - c^2}$, while $\|A^k x_0\| \ge |\lambda_{i_0}|^k c$.
-/
theorem sinAngle_powerIterate_le_of_eigenbasis (v : OrthonormalBasis ι 𝕜 E) {l : ι → 𝕜}
    (hv : ∀ i, A (v i) = l i • v i) {i₀ : ι} (hl₀ : l i₀ ≠ 0) {ρ : ℝ}
    (hρ : ∀ i, i ≠ i₀ → ‖l i‖ ≤ ρ) {x₀ : E} (hx₀ : ‖x₀‖ = 1)
    (hc : (inner 𝕜 (v i₀) x₀ : 𝕜) ≠ 0) (k : ℕ) :
    (𝕜 ∙ v i₀).sinAngle (powerIterate A x₀ k)
      ≤ Real.sqrt (1 - ‖(inner 𝕜 (v i₀) x₀ : 𝕜)‖ ^ 2) / ‖(inner 𝕜 (v i₀) x₀ : 𝕜)‖
        * (ρ / ‖l i₀‖) ^ k := by
  classical
  set a : ι → 𝕜 := fun i => inner 𝕜 (v i) x₀ with ha
  set c := ‖a i₀‖ with hcdef
  have hc0 : 0 < c := norm_pos_iff.2 hc
  have hl0 : 0 < ‖l i₀‖ := norm_pos_iff.2 hl₀
  set y := (A ^ k) x₀ with hy
  have hyi : ∀ i, (inner 𝕜 (v i) y : 𝕜) = l i ^ k * a i := fun i =>
    v.inner_pow_apply_of_apply_eq_smul hv k x₀ i
  have hpars : ∑ i, ‖a i‖ ^ 2 = 1 := by rw [ha, v.sum_sq_norm_inner_right, hx₀, one_pow]
  have hrest : ∑ i ∈ Finset.univ.erase i₀, ‖a i‖ ^ 2 = 1 - c ^ 2 := by
    rw [← hpars, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]; ring
  have hc1 : 0 ≤ 1 - c ^ 2 := by
    rw [← hrest]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
  -- the lower bound on `‖y‖`
  have hy2 : ‖y‖ ^ 2 = ∑ i, ‖l i‖ ^ (2 * k) * ‖a i‖ ^ 2 := by
    rw [← v.sum_sq_norm_inner_right y]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hyi, norm_mul, norm_pow, mul_pow, ← pow_mul, mul_comm k 2]
  have hylow : ‖l i₀‖ ^ k * c ≤ ‖y‖ := by
    refine le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
    rw [hy2, mul_pow, ← pow_mul, mul_comm k 2]
    exact Finset.single_le_sum (f := fun i => ‖l i‖ ^ (2 * k) * ‖a i‖ ^ 2)
      (fun i _ => by positivity) (Finset.mem_univ i₀)
  have hypos : 0 < ‖y‖ := lt_of_lt_of_le (by positivity) hylow
  have hy0 : y ≠ 0 := norm_pos_iff.1 hypos
  -- the candidate on the line
  set z := (l i₀ ^ k * a i₀) • v i₀ with hz
  have hzi : ∀ i, (inner 𝕜 (v i) (y - z) : 𝕜) = if i = i₀ then 0 else l i ^ k * a i := by
    intro i
    rw [inner_sub_right, hyi, hz, inner_smul_right, orthonormal_iff_ite.mp v.orthonormal i i₀]
    split_ifs with h
    · subst h; ring
    · ring
  have hyz2 : ‖y - z‖ ^ 2 = ∑ i ∈ Finset.univ.erase i₀, ‖l i‖ ^ (2 * k) * ‖a i‖ ^ 2 := by
    have h0 : (inner 𝕜 (v i₀) (y - z) : 𝕜) = 0 := by rw [hzi]; simp
    rw [← v.sum_sq_norm_inner_right (y - z), ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀),
      h0, norm_zero, zero_pow two_ne_zero, zero_add]
    refine Finset.sum_congr rfl fun i hi => ?_
    have h1 : (inner 𝕜 (v i) (y - z) : 𝕜) = l i ^ k * a i := by
      rw [hzi]; simp [Finset.ne_of_mem_erase hi]
    rw [h1, norm_mul, norm_pow, mul_pow, ← pow_mul, mul_comm k 2]
  -- the two cases of the sign of `ρ`
  rcases lt_or_ge ρ 0 with hρ0 | hρ0
  · -- no other index: the iterate is on the line
    have hall : ∀ i, i = i₀ := fun i => by
      by_contra h; exact absurd ((norm_nonneg _).trans (hρ i h)) (not_le.2 hρ0)
    have hyz : y - z = 0 := by
      rw [← norm_eq_zero, ← pow_eq_zero_iff two_ne_zero, hyz2]
      refine Finset.sum_eq_zero fun i hi => ?_
      exact absurd (hall i) (Finset.ne_of_mem_erase hi)
    have hmem : powerIterate A x₀ k ∈ (𝕜 ∙ v i₀) := by
      rw [powerIterate_eq_smul, ← hy, sub_eq_zero.1 hyz, hz, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    rw [Submodule.sinAngle_of_mem _ hmem]
    have h1 : 1 - c ^ 2 = 0 := by
      rw [← hrest]
      exact Finset.sum_eq_zero fun i hi => absurd (hall i) (Finset.ne_of_mem_erase hi)
    rw [h1, Real.sqrt_zero, zero_div, zero_mul]
  -- the main case
  have hyz : ‖y - z‖ ≤ ρ ^ k * Real.sqrt (1 - c ^ 2) := by
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    rw [hyz2, mul_pow, Real.sq_sqrt hc1, ← pow_mul, mul_comm k 2, ← hrest, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    gcongr
    exact hρ i (Finset.ne_of_mem_erase hi)
  have hq1 : ‖powerIterate A x₀ k‖ = 1 := norm_powerIterate_of_ne_zero A x₀ k hy0
  have hs := (𝕜 ∙ v i₀).sinAngle_mul_norm (powerIterate A x₀ k)
  rw [hq1, mul_one] at hs
  have hmem : ((‖y‖⁻¹ : ℝ) : 𝕜) • z ∈ (𝕜 ∙ v i₀) := by
    rw [hz, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hbest := (isBestApprox_starProjection (𝕜 ∙ v i₀) (powerIterate A x₀ k)).2 _ hmem
  have hdist : ‖powerIterate A x₀ k - ((‖y‖⁻¹ : ℝ) : 𝕜) • z‖ = ‖y - z‖ / ‖y‖ := by
    rw [powerIterate, ← hy, ← RCLike.ofReal_inv, ← smul_sub, norm_smul, RCLike.norm_ofReal,
      abs_of_pos (inv_pos.2 hypos), inv_mul_eq_div]
  rw [hs]
  refine hbest.trans ?_
  rw [hdist, div_le_iff₀ hypos]
  calc ‖y - z‖ ≤ ρ ^ k * Real.sqrt (1 - c ^ 2) := hyz
    _ = Real.sqrt (1 - c ^ 2) / c * (ρ / ‖l i₀‖) ^ k * (‖l i₀‖ ^ k * c) := by
        have hl0' : ‖l i₀‖ ^ k ≠ 0 := (pow_pos hl0 k).ne'
        rw [div_pow]
        field_simp
    _ ≤ Real.sqrt (1 - c ^ 2) / c * (ρ / ‖l i₀‖) ^ k * ‖y‖ := by gcongr

/-- The **Rayleigh-quotient bound of the power method**, with the constant of the source. Let $E$ be
an inner product space, and let $(v_i)_{i \in \iota}$ be an orthonormal basis of $E$ with
$Av_i = \lambda_i v_i$ and real $\lambda_i$, so that $A$ is symmetric
(`OrthonormalBasis.isSymmetric_of_apply_eq_ofReal_smul`). Let $i_0 \in \iota$ with
$\lambda_{i_0} \neq 0$, and let $|\lambda_i| \le \rho$ and
$|\lambda_{i_0} - \lambda_i| \le \delta$ for $i \neq i_0$. Let $x_0$ be a unit vector with
$c = |\langle v_{i_0}, x_0 \rangle| \neq 0$. Then for every $k$, $$|\lambda_{i_0} -
\operatorname{Re} \langle q_k, A q_k \rangle| \le \delta \, \frac{1 - c^2}{c^2}
\left(\frac{\rho}{|\lambda_{i_0}|}\right)^{2k}.$$ This is (8.2.5) in Theorem 8.2.1 of
[golub2013matrix].

The constant $\max_{i \neq i_0} |\lambda_{i_0} - \lambda_i|$ of the source is the least
admissible $\delta$. The spread of the spectrum is another, which gives
`LinearMap.IsSymmetric.abs_sub_rayleigh_powerIterate_le`. In eigencoordinates, $\nu_k =
\operatorname{Re} \langle q_k, A q_k \rangle = \sum_i \lambda_i^{2k+1} |a_i|^2 / \sum_i
\lambda_i^{2k} |a_i|^2$, so $\lambda_{i_0} - \nu_k = \sum_{i \neq i_0} (\lambda_{i_0} -
\lambda_i) \lambda_i^{2k} |a_i|^2 / \sum_i \lambda_i^{2k} |a_i|^2$. -/
theorem abs_sub_rayleigh_powerIterate_le_of_eigenbasis (v : OrthonormalBasis ι 𝕜 E) {l : ι → ℝ}
    (hv : ∀ i, A (v i) = (l i : 𝕜) • v i) {i₀ : ι} (hl₀ : l i₀ ≠ 0) {ρ : ℝ}
    (hρ : ∀ i, i ≠ i₀ → |l i| ≤ ρ) {δ : ℝ} (hδ : ∀ i, i ≠ i₀ → |l i₀ - l i| ≤ δ) {x₀ : E}
    (hx₀ : ‖x₀‖ = 1) (hc : (inner 𝕜 (v i₀) x₀ : 𝕜) ≠ 0) (k : ℕ) :
    |l i₀ - RCLike.re (inner 𝕜 (powerIterate A x₀ k) (A (powerIterate A x₀ k)))|
      ≤ δ * ((1 - ‖(inner 𝕜 (v i₀) x₀ : 𝕜)‖ ^ 2) / ‖(inner 𝕜 (v i₀) x₀ : 𝕜)‖ ^ 2)
        * (ρ / |l i₀|) ^ (2 * k) := by
  classical
  have hA := v.isSymmetric_of_apply_eq_ofReal_smul hv
  set wgt : ι → ℝ := fun i => ‖(inner 𝕜 (v i) x₀ : 𝕜)‖ ^ 2 with hwgt
  have hw0 : ∀ i, 0 ≤ wgt i := fun i => sq_nonneg _
  have hwpos : 0 < wgt i₀ := pow_pos (norm_pos_iff.mpr hc) 2
  have hsum : ∑ i, wgt i = 1 := by rw [hwgt, v.sum_sq_norm_inner_right, hx₀, one_pow]
  have hrest : ∑ i ∈ Finset.univ.erase i₀, wgt i = 1 - wgt i₀ := by
    rw [← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]; ring
  set y := (A ^ k) x₀ with hy
  have hyi : ∀ i, (inner 𝕜 (v i) y : 𝕜) = (l i : 𝕜) ^ k * inner 𝕜 (v i) x₀ := fun i =>
    v.inner_pow_apply_of_apply_eq_smul hv k x₀ i
  set D := ∑ i, l i ^ (2 * k) * wgt i with hD
  set N := ∑ i, l i ^ (2 * k + 1) * wgt i with hN
  have hrepr : ∀ i, ‖(inner 𝕜 (v i) y : 𝕜)‖ ^ 2 = l i ^ (2 * k) * wgt i := fun i => by
    rw [hyi, norm_mul, norm_pow, RCLike.norm_ofReal, mul_pow, ← pow_mul, mul_comm k 2, pow_mul,
      sq_abs, ← pow_mul]
  have hnorm : ‖y‖ ^ 2 = D := by
    rw [← v.sum_sq_norm_inner_right y, hD]
    exact Finset.sum_congr rfl fun i _ => hrepr i
  have hform : RCLike.re (inner 𝕜 (A y) y) = N := by
    rw [← v.sum_inner_mul_inner (A y) y, map_sum, hN]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := v.inner_pow_apply_of_apply_eq_smul hv 1 y i
    simp only [pow_one] at h1
    rw [← inner_conj_symm (A y), h1, map_mul (starRingEnd 𝕜), RCLike.conj_ofReal, mul_assoc,
      RCLike.conj_mul, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re, hrepr i]
    ring
  have hlow : l i₀ ^ (2 * k) * wgt i₀ ≤ D :=
    Finset.single_le_sum (f := fun i => l i ^ (2 * k) * wgt i)
      (fun i _ => mul_nonneg ((even_two_mul k).pow_nonneg _) (hw0 i)) (Finset.mem_univ i₀)
  have hl2 : 0 < l i₀ ^ (2 * k) := (even_two_mul k).pow_pos hl₀
  have hDpos : 0 < D := lt_of_lt_of_le (mul_pos hl2 hwpos) hlow
  have hnum : l i₀ * D - N = ∑ i ∈ Finset.univ.erase i₀, (l i₀ - l i) * l i ^ (2 * k)
      * wgt i := by
    rw [hD, hN, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), pow_succ]
    rw [show l i₀ * (l i₀ ^ (2 * k) * wgt i₀) - l i₀ ^ (2 * k) * l i₀ * wgt i₀ = 0 by ring,
      zero_add]
    exact Finset.sum_congr rfl fun i _ => by rw [pow_succ]; ring
  have habs : |l i₀| ^ (2 * k) = l i₀ ^ (2 * k) := by
    rw [pow_mul, sq_abs, ← pow_mul]
  rw [hA.re_inner_powerIterate_eq_div, hform, hnorm, div_pow, habs]
  have hkey : l i₀ - N / D = (l i₀ * D - N) / D := by field_simp
  rw [hkey, abs_div, abs_of_pos hDpos, div_le_iff₀ hDpos]
  rcases (Finset.univ.erase i₀).eq_empty_or_nonempty with he | ⟨j, hj⟩
  · -- a single eigenvalue: the quotient is exact
    rw [hnum, he, Finset.sum_empty, abs_zero]
    rw [he, Finset.sum_empty] at hrest
    rw [← hrest]
    simp
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ j (Finset.ne_of_mem_erase hj))
  have hρk : 0 ≤ ρ ^ (2 * k) := (even_two_mul k).pow_nonneg ρ
  have hnum_le : |l i₀ * D - N| ≤ δ * ρ ^ (2 * k) * (1 - wgt i₀) := by
    rw [hnum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [← hrest, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' := Finset.ne_of_mem_erase hi
    rw [abs_mul, abs_mul, abs_of_nonneg (hw0 i), abs_pow]
    have hρi : |l i| ^ (2 * k) ≤ ρ ^ (2 * k) := pow_le_pow_left₀ (abs_nonneg _) (hρ i hi') _
    exact mul_le_mul (mul_le_mul (hδ i hi') hρi (by positivity) hδ0) le_rfl (hw0 i)
      (mul_nonneg hδ0 hρk)
  have hw1 : 0 ≤ 1 - wgt i₀ := by rw [← hrest]; exact Finset.sum_nonneg fun i _ => hw0 i
  calc |l i₀ * D - N| ≤ δ * ρ ^ (2 * k) * (1 - wgt i₀) := hnum_le
    _ = δ * ((1 - wgt i₀) / wgt i₀) * (ρ ^ (2 * k) / l i₀ ^ (2 * k))
          * (l i₀ ^ (2 * k) * wgt i₀) := by
        field_simp
    _ ≤ δ * ((1 - wgt i₀) / wgt i₀) * (ρ ^ (2 * k) / l i₀ ^ (2 * k)) * D := by
        gcongr

end EigenbasisInner

end Krylov

namespace LinearMap.IsSymmetric

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
include hA

/-- **Quadratic convergence of the Rayleigh quotient in the symmetric power method.** Let $A$ be a
symmetric operator on an inner product space $E$ of finite dimension $n$, with eigenvalues
$\lambda_i$ and orthonormal eigenvectors $u_i$ given by `LinearMap.IsSymmetric.eigenvalues` and
`LinearMap.IsSymmetric.eigenvectorBasis`. Let $i_0$ be an index with $\lambda_{i_0} \neq 0$, let
$|\lambda_i| \le \rho$ for $i \neq i_0$, and let $a \le \lambda_i \le b$ for all $i$. Let $x_0$
be a unit vector with $c = |\langle u_{i_0}, x_0 \rangle| \neq 0$. Then the Rayleigh quotients
$\nu_k = \operatorname{Re} \langle q_k, A q_k \rangle$ of the power iterates satisfy, for every
$k$, $$|\lambda_{i_0} - \nu_k| \le (b - a) \, \frac{1 - c^2}{c^2}
\left(\frac{\rho}{|\lambda_{i_0}|}\right)^{2k}.$$ This is (5.23) of [quarteroni2000numerical]
and Theorem 8.2.1 of the 1989 edition of Golub and Van Loan, *Matrix Computations*.

Here $c = \cos\theta_0$ in the source, so $(1 - c^2)/c^2 = \tan^2\theta_0$. The source states
the bound for the dominant index $i_0$, with $a$ and $b$ the extreme eigenvalues
(`LinearMap.IsSymmetric.eigenvalues_antitone`). The bound does not need
$\rho < |\lambda_{i_0}|$, which only makes the rate a contraction. In the eigenbasis, with
$\beta_i = \langle u_i, x_0 \rangle$, $\nu_k = \sum_i \lambda_i^{2k+1} |\beta_i|^2 / \sum_i
\lambda_i^{2k} |\beta_i|^2$, so $\lambda_{i_0} - \nu_k = \sum_{i \neq i_0} (\lambda_{i_0} -
\lambda_i) \lambda_i^{2k} |\beta_i|^2 / \sum_i \lambda_i^{2k} |\beta_i|^2$. The numerator is at
most $(b - a) \rho^{2k} (1 - c^2)$ and the denominator is at least $\lambda_{i_0}^{2k} c^2$. -/
theorem abs_sub_rayleigh_powerIterate_le {n : ℕ} (hn : Module.finrank 𝕜 E = n) {i₀ : Fin n}
    (hl₀ : hA.eigenvalues hn i₀ ≠ 0) {ρ : ℝ} (hρ : ∀ i, i ≠ i₀ → |hA.eigenvalues hn i| ≤ ρ)
    {a b : ℝ} (hab : ∀ i, hA.eigenvalues hn i ∈ Set.Icc a b) {x₀ : E} (hx₀ : ‖x₀‖ = 1)
    (hc : (inner 𝕜 (hA.eigenvectorBasis hn i₀) x₀ : 𝕜) ≠ 0) (k : ℕ) :
    |hA.eigenvalues hn i₀ - RCLike.re (inner 𝕜 (Krylov.powerIterate A x₀ k)
        (A (Krylov.powerIterate A x₀ k)))|
      ≤ (b - a) * ((1 - ‖(inner 𝕜 (hA.eigenvectorBasis hn i₀) x₀ : 𝕜)‖ ^ 2)
          / ‖(inner 𝕜 (hA.eigenvectorBasis hn i₀) x₀ : 𝕜)‖ ^ 2)
        * (ρ / |hA.eigenvalues hn i₀|) ^ (2 * k) := by
  have hab' : ∀ i, i ≠ i₀ → |hA.eigenvalues hn i₀ - hA.eigenvalues hn i| ≤ b - a := fun i _ => by
    have h1 := hab i₀
    have h2 := hab i
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  exact Krylov.abs_sub_rayleigh_powerIterate_le_of_eigenbasis (hA.eigenvectorBasis hn)
    (fun i => hA.apply_eigenvectorBasis hn i) hl₀ hρ hab' hx₀ hc k

end LinearMap.IsSymmetric
