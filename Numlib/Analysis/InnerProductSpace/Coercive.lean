/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.Positive`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Coercive and symmetric coercive operators

Let $E$ be an inner product space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, with the inner
product $\langle x, y \rangle$ conjugate-linear in $x$. An operator $A$ on $E$ is **coercive with
constant $c$** if its quadratic form satisfies $c \|x\|^2 \le \operatorname{Re} \langle Ax, x
\rangle$ for all $x$. This module defines the hypothesis in three strengths: with a named constant,
with some constant $c > 0$, and in a two-sided form that encloses the quadratic form between
$l_{\min} \|x\|^2$ and $l_{\max} \|x\|^2$. It proves what each strength gives: injectivity,
positivity in the sense of Mathlib, the equivalence between the quadratic-form bounds and bounds on
the eigenvalues in finite dimension, invertibility on a Hilbert space (the Lax–Milgram theorem), the
location of the real spectrum, and the reduction of coercivity of a nonsymmetric $A$ to coercivity
of its Hermitian part $\frac{1}{2}(A + A^*)$.

## Main definitions

* `LinearMap.IsCoerciveWith`: $c \|x\|^2 \le \operatorname{Re} \langle Ax, x \rangle$ for all $x$.
* `LinearMap.IsCoercive`: coercivity with some constant $c > 0$. The numerical linear algebra
  literature calls such a matrix "positive definite" when no symmetry is required; it is the linear
  case of a strongly monotone operator.
* `LinearMap.IsSymmetricCoercive`: symmetric and coercive. In finite dimension these are the
  symmetric or Hermitian positive definite matrices (`Matrix.PosDef`); on a Hilbert space they are
  the strongly positive self-adjoint operators.
* `LinearMap.IsSymmetricBoundedBy`: $A$ is symmetric and $l_{\min} \|x\|^2 \le \operatorname{Re}
  \langle Ax, x \rangle \le l_{\max} \|x\|^2$ for all $x$. This is the quadratic-form way to say
  that the spectrum lies in $[l_{\min}, l_{\max}]$, and it is the hypothesis of the Kantorovich
  inequality and of the Chebyshev-type convergence bounds for symmetric positive definite operators.

## Main results

* `LinearMap.IsSymmetric.isCoerciveWith_iff_forall_hasEigenvalue` and
  `LinearMap.IsSymmetric.isSymmetricBoundedBy_iff_forall_hasEigenvalue`: in finite dimension, the
  quadratic-form bounds of a symmetric operator are exactly bounds on its eigenvalues.
* `ContinuousLinearMap.exists_equiv_of_isCoerciveWith`: the **Lax–Milgram theorem** for a bounded
  coercive operator on a Hilbert space, not necessarily symmetric: $A$ is invertible and
  $\|A^{-1}\| \le 1/c$.
* `ContinuousLinearMap.isCoerciveWith_iff_hermitianPart`: $A$ is coercive with constant $c$ if and
  only if $\frac{1}{2}(A + A^*)$ is.
* `ContinuousLinearMap.mem_Icc_of_mem_spectrum_real_of_isSymmetricBoundedBy`: on a complex Hilbert
  space, the real spectrum of a symmetric operator with quadratic form enclosed in
  $[\gamma, \delta]$ lies in $[\gamma, \delta]$.
* `Matrix.posDef_iff_isSymmetricCoercive`: a matrix is positive definite if and only if its
  Euclidean operator is symmetric coercive.
* `LinearMap.isSymmetric_iff_of_inner_map_eq`, `LinearMap.isPositive_iff_of_inner_map_eq` and
  `LinearMap.isSymmetricCoercive_iff_of_inner_map_eq`: symmetry, positivity and symmetric coercivity
  are transported along a linear equivalence $\Phi$, not necessarily an isometry, with $\langle
  T(\Phi x), \Phi y \rangle = \langle Sx, y \rangle$.

## Implementation notes

* Mathlib's `IsCoercive` is the same notion for a real bilinear form `V →L[ℝ] V →L[ℝ] ℝ`. The
  definitions here are for an operator over an `RCLike` field, which is the form that the
  convergence analysis of iterative methods uses.
-/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace LinearMap

/-- An operator $A$ on $E$ is **coercive with constant $c$** if $c \|x\|^2 \le \operatorname{Re}
\langle Ax, x \rangle$ for all $x \in E$.

No sign condition on $c$ is part of the definition. -/
def IsCoerciveWith (A : E →ₗ[𝕜] E) (c : ℝ) : Prop :=
  ∀ x, c * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (A x) x)

/-- An operator $A$ on $E$ is **coercive** if it is coercive with some constant $c > 0$, that is, $c
\|x\|^2 \le \operatorname{Re} \langle Ax, x \rangle$ for all $x \in E$. -/
def IsCoercive (A : E →ₗ[𝕜] E) : Prop := ∃ c : ℝ, 0 < c ∧ A.IsCoerciveWith c

/-- An operator $A$ on $E$ is **symmetric coercive** if it is symmetric and coercive. In finite
dimension these are the symmetric or Hermitian positive definite matrices; on a Hilbert space
they are the strongly positive self-adjoint operators. -/
structure IsSymmetricCoercive (A : E →ₗ[𝕜] E) : Prop where
  /-- The operator is symmetric: $\langle Ax, y \rangle = \langle x, Ay \rangle$ for all $x, y$. -/
  isSymmetric : A.IsSymmetric
  /-- The operator is coercive. -/
  isCoercive : A.IsCoercive

section Aux

/-- The quadratic form of $A$ is homogeneous of degree $2$ for real scalars: $\operatorname{Re}
\langle A(tx), tx \rangle = t^2 \operatorname{Re} \langle Ax, x \rangle$. -/
private theorem re_inner_apply_smul (A : E →ₗ[𝕜] E) (t : ℝ) (x : E) :
    RCLike.re (inner 𝕜 (A ((t : 𝕜) • x)) ((t : 𝕜) • x)) = t ^ 2 * RCLike.re (inner 𝕜 (A x) x) := by
  rw [map_smul, inner_smul_left, inner_smul_right, RCLike.conj_ofReal, RCLike.re_ofReal_mul,
    RCLike.re_ofReal_mul]
  ring

/-- If $Ax = \mu x$, then $\operatorname{Re} \langle Ax, x \rangle = \operatorname{Re}(\mu)
\|x\|^2$. -/
theorem re_inner_apply_self_of_eq_smul {A : E →ₗ[𝕜] E} {μ : 𝕜} {x : E} (h : A x = μ • x) :
    RCLike.re (inner 𝕜 (A x) x) = RCLike.re μ * ‖x‖ ^ 2 := by
  rw [h, inner_smul_left, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.mul_re]
  simp

/-- Coercivity with constant $c$ follows from $c \le \operatorname{Re} \langle Ax, x \rangle$ on the
unit sphere. -/
private theorem isCoerciveWith_of_forall_sphere {A : E →ₗ[𝕜] E} {c : ℝ}
    (h : ∀ x : E, ‖x‖ = 1 → c ≤ RCLike.re (inner 𝕜 (A x) x)) : A.IsCoerciveWith c := by
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hn : (0 : ℝ) < ‖x‖ := norm_pos_iff.2 hx
  have h1 : ‖((‖x‖⁻¹ : ℝ) : 𝕜) • x‖ = 1 := by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.2 hn), inv_mul_cancel₀ hn.ne']
  have h2 := h _ h1
  rw [re_inner_apply_smul] at h2
  have h3 := mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖x‖)
  have h4 : ‖x‖⁻¹ ^ 2 * RCLike.re (inner 𝕜 (A x) x) * ‖x‖ ^ 2
      = RCLike.re (inner 𝕜 (A x) x) := by field_simp
  rwa [h4] at h3

/-- Let $A$ be a bounded operator on $E$. Then $|\operatorname{Re} \langle Ax, x \rangle| \le \|A\|
\|x\|^2$ for all $x \in E$. -/
theorem _root_.ContinuousLinearMap.abs_re_inner_apply_self_le (A : E →L[𝕜] E) (x : E) :
    |RCLike.re (inner 𝕜 (A x) x)| ≤ ‖A‖ * ‖x‖ ^ 2 :=
  calc |RCLike.re (inner 𝕜 (A x) x)| ≤ ‖inner 𝕜 (A x) x‖ := RCLike.abs_re_le_norm _
    _ ≤ ‖A x‖ * ‖x‖ := norm_inner_le_norm _ _
    _ ≤ ‖A‖ * ‖x‖ * ‖x‖ := by gcongr; exact A.le_opNorm x
    _ = ‖A‖ * ‖x‖ ^ 2 := by ring

end Aux

variable {A : E →ₗ[𝕜] E}

/-- Let $A$ be a coercive operator on $E$ and let $x \neq 0$. Then
$\operatorname{Re} \langle Ax, x \rangle > 0$. -/
theorem IsCoercive.inner_self_pos (hA : A.IsCoercive) {x : E} (hx : x ≠ 0) :
    0 < RCLike.re (inner 𝕜 (A x) x) := by
  obtain ⟨c, hc, h⟩ := hA
  exact lt_of_lt_of_le (mul_pos hc (pow_pos (norm_pos_iff.2 hx) 2)) (h x)

/-- A coercive operator on $E$ is injective.

The quadratic form of a nonzero vector is strictly positive, so $A$ cannot annihilate it.
Neither completeness nor finite dimension is needed. -/
theorem IsCoercive.injective (hA : A.IsCoercive) : Function.Injective A := by
  refine (injective_iff_map_eq_zero A).2 fun x hx => ?_
  by_contra hx0
  simpa [hx] using hA.inner_self_pos hx0

/-- A coercive operator on $E$ has trivial kernel, $\ker A = \{0\}$.

This is the submodule form of `LinearMap.IsCoercive.injective`. -/
theorem IsCoercive.ker_eq_bot (hA : A.IsCoercive) : LinearMap.ker A = ⊥ :=
  LinearMap.ker_eq_bot.2 hA.injective

/-- If $A$ is coercive with constant $c$, then $c \|x\|^2 \le \operatorname{Re} \langle Ax, x
\rangle$ for every $x \in E$. This is the defining inequality of `LinearMap.IsCoerciveWith`,
stated as a lemma that can be applied by name. -/
theorem IsCoerciveWith.re_inner_apply_self {c : ℝ} (h : A.IsCoerciveWith c) (x : E) :
    c * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (A x) x) := h x

/-- If $A$ is coercive with constant $c$, then $A$ is bounded below: $c \|x\| \le \|Ax\|$ for every
$x \in E$. No sign condition on $c$ is needed.

The Cauchy–Schwarz inequality turns the quadratic-form bound into a bound on the norm. So the
error of an approximate solution is controlled by its residual, $c \|x - x^*\| \le \|b - Ax\|$,
and a coercivity constant bounds the inverse, $\|A^{-1} y\| \le \|y\| / c$. -/
theorem IsCoerciveWith.norm_le_norm_apply {c : ℝ} (h : A.IsCoerciveWith c) (x : E) :
    c * ‖x‖ ≤ ‖A x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h1 := h x
  have h2 : RCLike.re (inner 𝕜 (A x) x) ≤ ‖A x‖ * ‖x‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
  nlinarith

/-- Let $E$ be finite-dimensional and let $A$ be an operator on $E$. Then $A$ is coercive if and
only if
$$\operatorname{Re} \langle Ax, x \rangle > 0 \quad \text{for all } x \neq 0.$$

The unit sphere is compact, so the quadratic form attains a positive minimum on it, which is a
uniform constant $c > 0$. -/
theorem isCoercive_iff_forall_pos [FiniteDimensional 𝕜 E] (A : E →ₗ[𝕜] E) :
    A.IsCoercive ↔ ∀ x ≠ 0, 0 < RCLike.re (inner 𝕜 (A x) x) := by
  refine ⟨fun hA x hx => hA.inner_self_pos hx, fun h => ?_⟩
  rcases subsingleton_or_nontrivial E with _ | _
  · exact ⟨1, one_pos, fun x => by rw [Subsingleton.elim x 0]; simp⟩
  have : ProperSpace E := FiniteDimensional.proper_rclike 𝕜 E
  have hcont : Continuous fun x : E => RCLike.re (inner 𝕜 (A x) x) :=
    RCLike.continuous_re.comp (A.continuous_of_finiteDimensional.inner continuous_id)
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hvn : (0 : ℝ) < ‖v‖ := norm_pos_iff.2 hv
  have hsne : (Metric.sphere (0 : E) 1).Nonempty := by
    refine ⟨((‖v‖⁻¹ : ℝ) : 𝕜) • v, ?_⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.2 hvn),
      inv_mul_cancel₀ hvn.ne']
  obtain ⟨x₀, hx₀, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hsne hcont.continuousOn
  have hx₀1 : ‖x₀‖ = 1 := by simpa using hx₀
  refine ⟨_, h x₀ fun hz => by simp [hz] at hx₀1, isCoerciveWith_of_forall_sphere fun x hx1 => ?_⟩
  exact isMinOn_iff.1 hmin x (by simpa using hx1)

/-- A symmetric coercive operator is positive in the sense of Mathlib, `LinearMap.IsPositive`.

So the positive-operator API of Mathlib applies to it. The converse fails: a positive operator
need not have a strictly positive coercivity constant. -/
theorem IsSymmetricCoercive.isPositive (hA : A.IsSymmetricCoercive) : A.IsPositive :=
  ⟨hA.isSymmetric, fun x => by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · exact (hA.isCoercive.inner_self_pos hx).le⟩

section Rayleigh

variable [FiniteDimensional 𝕜 E]

/-- In finite dimension the Rayleigh quotients $\operatorname{Re} \langle Ay, y \rangle / \|y\|^2$,
$y \neq 0$, are bounded below. -/
private theorem bddBelow_rayleigh (A : E →ₗ[𝕜] E) :
    BddBelow (Set.range fun y : {y : E // y ≠ 0} =>
      RCLike.re (inner 𝕜 (A y) y) / ‖(y : E)‖ ^ 2) := by
  refine ⟨-‖LinearMap.toContinuousLinearMap A‖, ?_⟩
  rintro _ ⟨y, rfl⟩
  have h := (LinearMap.toContinuousLinearMap A).rayleighQuotient_le_norm (y : E)
  rw [abs_le] at h
  simpa [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf] using h.1

/-- In finite dimension the Rayleigh quotients $\operatorname{Re} \langle Ay, y \rangle / \|y\|^2$,
$y \neq 0$, are bounded above. -/
private theorem bddAbove_rayleigh (A : E →ₗ[𝕜] E) :
    BddAbove (Set.range fun y : {y : E // y ≠ 0} =>
      RCLike.re (inner 𝕜 (A y) y) / ‖(y : E)‖ ^ 2) := by
  refine ⟨‖LinearMap.toContinuousLinearMap A‖, ?_⟩
  rintro _ ⟨y, rfl⟩
  have h := (LinearMap.toContinuousLinearMap A).rayleighQuotient_le_norm (y : E)
  rw [abs_le] at h
  simpa [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf] using h.2

/-- In finite dimension, if every eigenvalue $\mu$ of a symmetric $A$ has
$c \le \operatorname{Re} \mu$, then $c \|x\|^2 \le \operatorname{Re} \langle Ax, x \rangle$ for
all $x$. -/
private theorem le_re_inner_of_forall_hasEigenvalue (hA : A.IsSymmetric) {c : ℝ}
    (h : ∀ μ : 𝕜, Module.End.HasEigenvalue A μ → c ≤ RCLike.re μ) (x : E) :
    c * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (A x) x) := by
  rcases subsingleton_or_nontrivial E with _ | _
  · rw [Subsingleton.elim x 0]; simp
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hc : c ≤ ⨅ y : {y : E // y ≠ 0}, RCLike.re (inner 𝕜 (A y) y) / ‖(y : E)‖ ^ 2 := by
    simpa using h _ hA.hasEigenvalue_iInf_of_finiteDimensional
  rw [← le_div_iff₀ (pow_pos (norm_pos_iff.2 hx) 2)]
  exact hc.trans (ciInf_le (bddBelow_rayleigh A) ⟨x, hx⟩)

/-- In finite dimension, if every eigenvalue $\mu$ of a symmetric $A$ has
$\operatorname{Re} \mu \le c$, then $\operatorname{Re} \langle Ax, x \rangle \le c \|x\|^2$ for
all $x$. -/
private theorem re_inner_le_of_forall_hasEigenvalue (hA : A.IsSymmetric) {c : ℝ}
    (h : ∀ μ : 𝕜, Module.End.HasEigenvalue A μ → RCLike.re μ ≤ c) (x : E) :
    RCLike.re (inner 𝕜 (A x) x) ≤ c * ‖x‖ ^ 2 := by
  rcases subsingleton_or_nontrivial E with _ | _
  · rw [Subsingleton.elim x 0]; simp
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hc : (⨆ y : {y : E // y ≠ 0}, RCLike.re (inner 𝕜 (A y) y) / ‖(y : E)‖ ^ 2) ≤ c := by
    simpa using h _ hA.hasEigenvalue_iSup_of_finiteDimensional
  rw [← div_le_iff₀ (pow_pos (norm_pos_iff.2 hx) 2)]
  exact (le_ciSup (bddAbove_rayleigh A) (⟨x, hx⟩ : {y : E // y ≠ 0})).trans hc

end Rayleigh

/-- Let $E$ be finite-dimensional, let $A$ be a symmetric operator on $E$, and let
$c \in \mathbb{R}$. Then $A$ is coercive with constant $c$ if and only if every eigenvalue $\mu$
of $A$ satisfies $c \le \operatorname{Re} \mu$.

So the best coercivity constant is the smallest eigenvalue. The eigenvalues of a symmetric
operator are real, so $\operatorname{Re} \mu = \mu$. -/
theorem IsSymmetric.isCoerciveWith_iff_forall_hasEigenvalue [FiniteDimensional 𝕜 E]
    (hA : A.IsSymmetric) (c : ℝ) :
    A.IsCoerciveWith c ↔ ∀ μ : 𝕜, Module.End.HasEigenvalue A μ → c ≤ RCLike.re μ := by
  refine ⟨fun hc μ hμ => ?_, fun h => le_re_inner_of_forall_hasEigenvalue hA h⟩
  obtain ⟨x, hx, hx0⟩ := hμ.exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff] at hx
  have h1 := hc x
  rw [re_inner_apply_self_of_eq_smul hx] at h1
  exact le_of_mul_le_mul_right (by linarith) (pow_pos (norm_pos_iff.2 hx0) 2)

/-- Every eigenvalue $\mu$ of a symmetric coercive operator satisfies $\operatorname{Re} \mu > 0$.
-/
theorem IsSymmetricCoercive.re_pos_of_hasEigenvalue (hA : A.IsSymmetricCoercive) {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue A μ) : 0 < RCLike.re μ := by
  obtain ⟨x, hx, hx0⟩ := hμ.exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff] at hx
  have h1 := hA.isCoercive.inner_self_pos hx0
  rw [re_inner_apply_self_of_eq_smul hx] at h1
  exact (mul_pos_iff_of_pos_right (pow_pos (norm_pos_iff.2 hx0) 2)).mp h1

/-- An operator $A$ on $E$ is **symmetric and bounded by $l_{\min}$ and $l_{\max}$** if $A$ is
symmetric and
$$l_{\min} \|x\|^2 \le \operatorname{Re} \langle Ax, x \rangle \le l_{\max} \|x\|^2 \quad
  \text{for all } x \in E.$$

This states through the quadratic form that the spectrum of $A$ lies in $[l_{\min}, l_{\max}]$.
For a symmetric positive definite matrix one can take $l_{\min} = \lambda_{\min}$ and
$l_{\max} = \lambda_{\max}$. In finite dimension the condition is equivalent to all eigenvalues
lying in $[l_{\min}, l_{\max}]$
(`LinearMap.IsSymmetric.isSymmetricBoundedBy_iff_forall_hasEigenvalue`). The condition makes
sense in any inner product space, passes to compressions, and is the hypothesis of the
Chebyshev-type convergence bounds. -/
structure IsSymmetricBoundedBy (A : E →ₗ[𝕜] E) (lmin lmax : ℝ) : Prop where
  /-- The operator is symmetric. -/
  isSymmetric : A.IsSymmetric
  /-- The quadratic form is bounded below: $l_{\min} \|x\|^2 \le \operatorname{Re} \langle Ax, x
  \rangle$ for all $x$. -/
  le_re_inner : ∀ x, lmin * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (A x) x)
  /-- The quadratic form is bounded above: $\operatorname{Re} \langle Ax, x \rangle \le l_{\max}
  \|x\|^2$ for all $x$. -/
  re_inner_le : ∀ x, RCLike.re (inner 𝕜 (A x) x) ≤ lmax * ‖x‖ ^ 2

namespace IsSymmetricBoundedBy

variable {lmin lmax : ℝ} (hA : A.IsSymmetricBoundedBy lmin lmax)
include hA

/-- If $A$ is symmetric and bounded by $l_{\min}$ and $l_{\max}$, then $A$ is coercive with constant
$l_{\min}$. -/
theorem isCoerciveWith : A.IsCoerciveWith lmin := hA.le_re_inner

/-- If $A$ is symmetric and bounded by $l_{\min}$ and $l_{\max}$, and $l_{\min} > 0$, then $A$ is
symmetric coercive, that is, symmetric positive definite. -/
theorem isSymmetricCoercive (hl : 0 < lmin) : A.IsSymmetricCoercive :=
  ⟨hA.isSymmetric, lmin, hl, hA.le_re_inner⟩

/-- If $A$ is symmetric and bounded by $l_{\min}$ and $l_{\max}$, then the Rayleigh quotient of
every $x \neq 0$ lies in the interval:
$$\frac{\operatorname{Re} \langle Ax, x \rangle}{\|x\|^2} \in [l_{\min}, l_{\max}].$$
-/
theorem rayleigh_mem_Icc {x : E} (hx : x ≠ 0) :
    RCLike.re (inner 𝕜 (A x) x) / ‖x‖ ^ 2 ∈ Set.Icc lmin lmax := by
  have hx2 : (0 : ℝ) < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.2 hx) 2
  exact ⟨(le_div_iff₀ hx2).2 (hA.le_re_inner x), (div_le_iff₀ hx2).2 (hA.re_inner_le x)⟩

/-- If $A$ is symmetric and bounded by $l_{\min}$ and $l_{\max}$, then every eigenvalue $\mu$ of $A$
satisfies $\operatorname{Re} \mu \in [l_{\min}, l_{\max}]$. -/
theorem re_mem_Icc_of_hasEigenvalue {μ : 𝕜} (hμ : Module.End.HasEigenvalue A μ) :
    RCLike.re μ ∈ Set.Icc lmin lmax := by
  obtain ⟨x, hx, hx0⟩ := hμ.exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff] at hx
  have h := hA.rayleigh_mem_Icc hx0
  rwa [re_inner_apply_self_of_eq_smul hx, mul_div_assoc,
    div_self (pow_pos (norm_pos_iff.2 hx0) 2).ne', mul_one] at h

/-- If $A$ is symmetric and bounded by $l_{\min}$ and $l_{\max}$, and $l'_{\min} \le l_{\min}$ and
$l_{\max} \le l'_{\max}$, then $A$ is symmetric and bounded by $l'_{\min}$ and $l'_{\max}$.

So a convergence estimate stated for a wider interval is weaker. This is what makes $l_{\min}$
and $l_{\max}$ usable as computable estimates of the extreme eigenvalues. -/
theorem mono {lmin' lmax' : ℝ} (h₁ : lmin' ≤ lmin) (h₂ : lmax ≤ lmax') :
    A.IsSymmetricBoundedBy lmin' lmax' :=
  ⟨hA.isSymmetric,
    fun x => (mul_le_mul_of_nonneg_right h₁ (sq_nonneg _)).trans (hA.le_re_inner x),
    fun x => (hA.re_inner_le x).trans (mul_le_mul_of_nonneg_right h₂ (sq_nonneg _))⟩

/-- Let $A$ be symmetric and bounded by $l_{\min}$ and $l_{\max}$ on $E$. Let $F$ be an inner
product space with a linear isometry $\iota : F \to E$, and let $B$ be a symmetric operator on
$F$ with $\langle Bx, x \rangle = \langle A(\iota x), \iota x \rangle$ for all $x \in F$. Then
$B$ is symmetric and bounded by $l_{\min}$ and $l_{\max}$.

This covers restrictions to invariant subspaces and compressions. -/
theorem of_inner_eq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] {B : F →ₗ[𝕜] F}
    (hB : B.IsSymmetric) (ι : F →ₗᵢ[𝕜] E)
    (h : ∀ x, inner 𝕜 (B x) x = inner 𝕜 (A (ι x)) (ι x)) : B.IsSymmetricBoundedBy lmin lmax := by
  refine ⟨hB, fun x => ?_, fun x => ?_⟩
  · rw [h x, ← ι.norm_map x]; exact hA.le_re_inner _
  · rw [h x, ← ι.norm_map x]; exact hA.re_inner_le _

end IsSymmetricBoundedBy

/-- Let $E$ be finite-dimensional, let $A$ be a symmetric operator on $E$, and let
$l_{\min}, l_{\max} \in \mathbb{R}$. Then $A$ is symmetric and bounded by $l_{\min}$ and
$l_{\max}$ if and only if every eigenvalue $\mu$ of $A$ satisfies
$\operatorname{Re} \mu \in [l_{\min}, l_{\max}]$.

The proof uses the Rayleigh characterization of the extreme eigenvalues,
`LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional` and
`LinearMap.IsSymmetric.hasEigenvalue_iInf_of_finiteDimensional`. -/
theorem IsSymmetric.isSymmetricBoundedBy_iff_forall_hasEigenvalue [FiniteDimensional 𝕜 E]
    (hA : A.IsSymmetric) (lmin lmax : ℝ) :
    A.IsSymmetricBoundedBy lmin lmax ↔
      ∀ μ : 𝕜, Module.End.HasEigenvalue A μ → RCLike.re μ ∈ Set.Icc lmin lmax :=
  ⟨fun h _ hμ => h.re_mem_Icc_of_hasEigenvalue hμ, fun h =>
    ⟨hA, le_re_inner_of_forall_hasEigenvalue hA fun μ hμ => (h μ hμ).1,
      re_inner_le_of_forall_hasEigenvalue hA fun μ hμ => (h μ hμ).2⟩⟩

/-- Let $A$ be a bounded symmetric operator on $E$. Then $A$ is symmetric and bounded by $-\|A\|$
and $\|A\|$. -/
theorem IsSymmetric.isSymmetricBoundedBy_neg_norm_norm {A : E →L[𝕜] E}
    (hA : (A : E →ₗ[𝕜] E).IsSymmetric) : (A : E →ₗ[𝕜] E).IsSymmetricBoundedBy (-‖A‖) ‖A‖ := by
  refine ⟨hA, fun x => ?_, fun x => ?_⟩
  · rw [neg_mul]
    exact (abs_le.1 (A.abs_re_inner_apply_self_le x)).1
  · exact (abs_le.1 (A.abs_re_inner_apply_self_le x)).2

/-- **Adjoint pairs for the inner products.** Let $F$ be a second inner product space, and let
$A : E \to F$ and $A^\star : F \to E$ be maps. Then $A$ and $A^\star$ form an adjoint pair for
the inner products of $E$ and $F$ if and only if
$$\langle A^\star u, x \rangle = \langle u, Ax \rangle \quad \text{for all } u \in F, \ x \in
  E.$$

An adjoint pair is `LinearMap.IsAdjointPair` for the flipped forms `innerₛₗ`, the form of
Mathlib's `LinearMap.isAdjointPair_inner`. Here $A^\star$ is any map with the adjoint property;
the adjoint `LinearMap.adjoint` itself needs finite dimension. -/
theorem isAdjointPair_inner_iff {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    {A : E → F} {Astar : F → E} :
    IsAdjointPair (innerₛₗ 𝕜 (E := E)).flip (innerₛₗ 𝕜 (E := F)).flip A Astar ↔
      ∀ u x, inner 𝕜 (Astar u) x = inner 𝕜 u (A x) := by
  simp only [IsAdjointPair, flip_apply, innerₛₗ_apply_apply]
  exact ⟨fun h u x => (h x u).symm, fun h x u => (h u x).symm⟩

/-- **Adjoint pairs for the inner products**, with $A$ moved to the left. Let $F$ be a second inner
product space, and let $A : E \to F$ and $A^\star : F \to E$ be maps. Then $A$ and $A^\star$
form an adjoint pair for the inner products of $E$ and $F$ if and only if
$$\langle Ax, u \rangle = \langle x, A^\star u \rangle \quad \text{for all } x \in E, \ u \in
  F.$$

An adjoint pair is `LinearMap.IsAdjointPair` for the flipped forms `innerₛₗ`. -/
theorem isAdjointPair_inner_iff' {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    {A : E → F} {Astar : F → E} :
    IsAdjointPair (innerₛₗ 𝕜 (E := E)).flip (innerₛₗ 𝕜 (E := F)).flip A Astar ↔
      ∀ x u, inner 𝕜 (A x) u = inner 𝕜 x (Astar u) := by
  rw [isAdjointPair_inner_iff]
  refine ⟨fun h x u => ?_, fun h u x => ?_⟩
  · rw [← inner_conj_symm, ← h, inner_conj_symm]
  · rw [← inner_conj_symm, ← h, inner_conj_symm]

/-- Let $F$ be a second inner product space, and let $A : E \to F$ and $A^\star : F \to E$ form an
adjoint pair for the inner products. Then $\langle A^\star u, x \rangle = \langle u, Ax \rangle$
for all $u \in F$ and $x \in E$.

An adjoint pair is `LinearMap.IsAdjointPair` for the flipped forms `innerₛₗ`. -/
theorem IsAdjointPair.inner_apply_eq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    {A : E → F} {Astar : F → E}
    (hadj : IsAdjointPair (innerₛₗ 𝕜 (E := E)).flip (innerₛₗ 𝕜 (E := F)).flip A Astar) (u : F)
    (x : E) : inner 𝕜 (Astar u) x = inner 𝕜 u (A x) :=
  isAdjointPair_inner_iff.1 hadj u x

/-- Let $F$ be a second inner product space, and let the linear maps $A : E \to F$ and
$A^\star : F \to E$ form an adjoint pair for the inner products. Then $\langle Ax, u \rangle =
\langle x, A^\star u \rangle$ for all $x \in E$ and $u \in F$.

Mathlib's `LinearMap.adjoint_inner_right` is the case of the adjoint `LinearMap.adjoint`, which
needs finite dimension. Here $A^\star$ is any map with the adjoint property. -/
theorem inner_apply_eq_inner_apply_of_adjoint {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] {A : E →ₗ[𝕜] F} {Astar : F →ₗ[𝕜] E}
    (hadj : IsAdjointPair (innerₛₗ 𝕜 (E := E)).flip (innerₛₗ 𝕜 (E := F)).flip A Astar) (x : E)
    (u : F) : inner 𝕜 (A x) u = inner 𝕜 x (Astar u) := by
  rw [← inner_conj_symm, ← hadj.inner_apply_eq, inner_conj_symm]

/-- Let $F$ be a second inner product space, and let $A : E \to F$ and $A^\star : F \to E$ form an
adjoint pair for the inner products of $E$ and $F$. Then $A^\star$ and $A$ form an adjoint pair
for the inner products of $F$ and $E$. -/
theorem IsAdjointPair.swap_inner {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    {A : E → F} {Astar : F → E}
    (h : IsAdjointPair (innerₛₗ 𝕜 (E := E)).flip (innerₛₗ 𝕜 (E := F)).flip A Astar) :
    IsAdjointPair (innerₛₗ 𝕜 (E := F)).flip (innerₛₗ 𝕜 (E := E)).flip Astar A :=
  isAdjointPair_inner_iff.2 (isAdjointPair_inner_iff'.1 h)

end LinearMap

section Richardson

/-- The **contraction estimate of the damped Richardson iteration**. Let $A$ be a bounded operator
on $E$ that is coercive with constant $c$, and let $\theta \ge 0$. Then for every $x \in E$
$$\|x - \theta A x\|^2 \le (1 - 2 \theta c + \theta^2 \|A\|^2) \|x\|^2.$$

For $c > 0$ and $0 < \theta < 2c / \|A\|^2$ the factor on the right is less than $1$. This is
the standard convergence proof for the Richardson iteration $x \mapsto x - \theta (Ax - b)$. -/
theorem ContinuousLinearMap.norm_sub_smul_apply_sq_le {A : E →L[𝕜] E} {c : ℝ}
    (hA : (A : E →ₗ[𝕜] E).IsCoerciveWith c) {θ : ℝ} (hθ : 0 ≤ θ) (x : E) :
    ‖x - (θ : 𝕜) • A x‖ ^ 2 ≤ (1 - 2 * θ * c + θ ^ 2 * ‖A‖ ^ 2) * ‖x‖ ^ 2 := by
  have h1 : RCLike.re (inner 𝕜 x ((θ : 𝕜) • A x)) = θ * RCLike.re (inner 𝕜 (A x) x) := by
    rw [inner_smul_right, RCLike.re_ofReal_mul, ← inner_conj_symm, RCLike.conj_re]
  have h2 : ‖(θ : 𝕜) • A x‖ ^ 2 = θ ^ 2 * ‖A x‖ ^ 2 := by
    rw [norm_smul, RCLike.norm_ofReal, mul_pow, sq_abs]
  have h3 : ‖A x‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖x‖ ^ 2 := by
    have h := A.le_opNorm x
    nlinarith [norm_nonneg (A x), norm_nonneg x, norm_nonneg A]
  have h4 : c * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (A x) x) := hA x
  rw [norm_sub_sq (𝕜 := 𝕜), h1, h2]
  nlinarith [mul_le_mul_of_nonneg_left h4 hθ, mul_le_mul_of_nonneg_left h3 (sq_nonneg θ)]

end Richardson

namespace ContinuousLinearMap

/-- Let $T$ be a bounded operator on $E$, let $M \ge 0$, and let $T$ be symmetric and bounded by
$-M$ and $M$. Then $\|T\| \le M$.

The norm of a symmetric operator is the supremum of the absolute values of its Rayleigh
quotients (`ContinuousLinearMap.norm_eq_iSup_rayleighQuotient`), and each of them lies in
$[-M, M]$. -/
theorem norm_le_of_isSymmetricBoundedBy {T : E →L[𝕜] E} {M : ℝ} (hM : 0 ≤ M)
    (hb : (T : E →ₗ[𝕜] E).IsSymmetricBoundedBy (-M) M) : ‖T‖ ≤ M := by
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient T hb.isSymmetric]
  refine ciSup_le fun x => ?_
  rcases eq_or_ne x 0 with rfl | hx
  · simpa [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf] using hM
  · have h := hb.rayleigh_mem_Icc hx
    rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf, abs_le]
    exact ⟨h.1, h.2⟩

variable [CompleteSpace E]

/-- The **Lax–Milgram theorem** for an operator. Let $E$ be a Hilbert space, let $c > 0$, and let
$A$ be a bounded operator on $E$ that is coercive with constant $c$. Then $A$ is invertible as a
bounded operator, and its inverse satisfies
$$\|A^{-1}\| \le \frac{1}{c}.$$

The operator $A$ need not be symmetric. The conclusion is stated as the existence of a
continuous linear equivalence $e$ of $E$ whose underlying operator is $A$ and whose inverse has
norm at most $1/c$. -/
theorem exists_equiv_of_isCoerciveWith {A : E →L[𝕜] E} {c : ℝ} (hc : 0 < c)
    (hA : (A : E →ₗ[𝕜] E).IsCoerciveWith c) :
    ∃ e : E ≃L[𝕜] E, (e : E →L[𝕜] E) = A ∧ ‖(e.symm : E →L[𝕜] E)‖ ≤ 1 / c := by
  have hlb : ∀ x : E, c * ‖x‖ ≤ ‖A x‖ := hA.norm_le_norm_apply
  have hanti : AntilipschitzWith (Real.toNNReal c⁻¹) (A : E → E) := by
    refine AddMonoidHomClass.antilipschitz_of_bound A fun x => ?_
    rw [Real.coe_toNNReal _ (by positivity), inv_mul_eq_div, le_div_iff₀ hc]
    linarith [hlb x]
  have hker : LinearMap.ker (A : E →ₗ[𝕜] E) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact hanti.injective
  have hclosed : IsClosed (LinearMap.range (A : E →ₗ[𝕜] E) : Set E) := by
    exact hanti.isClosed_range A.uniformContinuous
  have : CompleteSpace (LinearMap.range (A : E →ₗ[𝕜] E)) := hclosed.completeSpace_coe
  have hrange : LinearMap.range (A : E →ₗ[𝕜] E) = ⊤ := by
    rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
    intro y hy
    have h0 : inner 𝕜 ((A : E →ₗ[𝕜] E) y) y = 0 := hy _ ⟨y, rfl⟩
    have h1 := hA y
    rw [h0, map_zero] at h1
    have : ‖y‖ ^ 2 ≤ 0 := nonpos_of_mul_nonpos_right (by linarith) hc
    simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm this (sq_nonneg _))
  refine ⟨ContinuousLinearEquiv.ofBijective A hker hrange,
    ContinuousLinearEquiv.coe_ofBijective A hker hrange, ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  set e := ContinuousLinearEquiv.ofBijective A hker hrange with he
  have hAe : A ((e.symm : E →L[𝕜] E) y) = y := by
    conv_rhs => rw [← e.apply_symm_apply y]
    rw [he]
    simp
  have h := hlb ((e.symm : E →L[𝕜] E) y)
  rw [hAe] at h
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc]
  linarith [h]

/-- Let $E$ be a Hilbert space and let $A$ be a bounded operator on $E$. The Hermitian part
$\frac{1}{2}(A + A^*)$ has the same quadratic form as $A$:
$$\operatorname{Re} \left\langle \tfrac{1}{2}(A + A^*) x, x \right\rangle = \operatorname{Re}
  \langle Ax, x \rangle \quad \text{for all } x \in E.$$
-/
theorem re_inner_hermitianPart_apply (A : E →L[𝕜] E) (x : E) :
    RCLike.re (inner 𝕜 (((2⁻¹ : 𝕜) • (A + adjoint A)) x) x) = RCLike.re (inner 𝕜 (A x) x) := by
  have h2 : (2⁻¹ : 𝕜) = ((2⁻¹ : ℝ) : 𝕜) := by rw [RCLike.ofReal_inv, RCLike.ofReal_ofNat]
  have h1 : inner 𝕜 ((adjoint A) x) x = starRingEnd 𝕜 (inner 𝕜 (A x) x) := by
    rw [ContinuousLinearMap.adjoint_inner_left, ← inner_conj_symm]
  rw [smul_apply, add_apply, inner_smul_left, inner_add_left, h1, h2, RCLike.conj_ofReal,
    RCLike.re_ofReal_mul, map_add, RCLike.conj_re]
  ring

/-- Let $E$ be a Hilbert space, let $A$ be a bounded operator on $E$, and let $c \in \mathbb{R}$.
Then $A$ is coercive with constant $c$ if and only if its Hermitian part $\frac{1}{2}(A + A^*)$
is coercive with constant $c$.

So the best coercivity constant of $A$ is $\lambda_{\min}\bigl(\frac{1}{2}(A + A^*)\bigr)$. This
constant governs the convergence rate of the Richardson and steepest-descent iterations for a
nonsymmetric $A$. -/
theorem isCoerciveWith_iff_hermitianPart (A : E →L[𝕜] E) (c : ℝ) :
    (A : E →ₗ[𝕜] E).IsCoerciveWith c ↔
      (((2⁻¹ : 𝕜) • (A + adjoint A) : E →L[𝕜] E) : E →ₗ[𝕜] E).IsCoerciveWith c := by
  simp only [LinearMap.IsCoerciveWith, ContinuousLinearMap.coe_coe,
    re_inner_hermitianPart_apply]

omit [CompleteSpace E] in
/-- Let $A$ be a bounded operator on $E$ that is coercive with constant $c$, and let
$r \in \mathbb{R}$. Then $A + rI$ is coercive with constant $c + r$, because the shift adds
$r \|x\|^2$ to the quadratic form. -/
theorem isCoerciveWith_add_smul_one {A : E →L[𝕜] E} {c : ℝ}
    (hA : (A : E →ₗ[𝕜] E).IsCoerciveWith c) {r : ℝ} :
    ((A + (r : 𝕜) • (1 : E →L[𝕜] E) : E →L[𝕜] E) : E →ₗ[𝕜] E).IsCoerciveWith (c + r) := by
  intro x
  have happ : (A + (r : 𝕜) • (1 : E →L[𝕜] E)) x = A x + (r : 𝕜) • x := by simp
  have h1 : RCLike.re (inner 𝕜 ((r : 𝕜) • x) x) = r * ‖x‖ ^ 2 := by
    rw [inner_smul_left, RCLike.conj_ofReal, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow,
      ← RCLike.ofReal_mul, RCLike.ofReal_re]
  have hq : c * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (A x) x) := hA x
  rw [ContinuousLinearMap.coe_coe, happ, inner_add_left, map_add, h1, add_mul]
  linarith

section Complex

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Let $F$ be a complex Hilbert space and let $A$ be a bounded operator on $F$ that is coercive
with constant $c$. Then every real number $t$ in the spectrum of $A$ satisfies $c \le t$.

For $t < c$ the shift $A - tI$ is coercive with the constant $c - t > 0$, so it is invertible by
the Lax–Milgram theorem (`ContinuousLinearMap.exists_equiv_of_isCoerciveWith`). The spectrum is
`spectrum ℝ A`, the real spectrum. -/
theorem le_of_mem_spectrum_real_of_isCoerciveWith {A : F →L[ℂ] F} {c : ℝ}
    (hA : (A : F →ₗ[ℂ] F).IsCoerciveWith c) {t : ℝ} (ht : t ∈ spectrum ℝ A) : c ≤ t := by
  by_contra hlt
  rw [not_le] at hlt
  have hcoer := isCoerciveWith_add_smul_one hA (r := -t)
  obtain ⟨e, he, -⟩ :=
    ContinuousLinearMap.exists_equiv_of_isCoerciveWith (by linarith : (0 : ℝ) < c + -t) hcoer
  have hu : IsUnit (e : F →L[ℂ] F) :=
    ⟨(ContinuousLinearEquiv.unitsEquiv ℂ F).symm e, by
      ext x
      rw [← ContinuousLinearEquiv.unitsEquiv_apply ℂ F, MulEquiv.apply_symm_apply]
      rfl⟩
  rw [he] at hu
  refine spectrum.notMem_iff.mpr ?_ ht
  have : algebraMap ℝ (F →L[ℂ] F) t - A = -(A + ((-t : ℝ) : ℂ) • (1 : F →L[ℂ] F)) := by
    rw [Algebra.algebraMap_eq_smul_one, Complex.coe_smul]
    module
  rw [this]
  exact hu.neg

/-- Let $F$ be a complex Hilbert space and let $A$ be a bounded operator on $F$ that is symmetric
and bounded by $\gamma$ and $\delta$. Then every real number $t$ in the spectrum of $A$
satisfies $\gamma \le t \le \delta$. No finite dimension is needed.

Both bounds come from `ContinuousLinearMap.le_of_mem_spectrum_real_of_isCoerciveWith`; the upper
bound applies it to $-A$. -/
theorem mem_Icc_of_mem_spectrum_real_of_isSymmetricBoundedBy {A : F →L[ℂ] F} {γ δ : ℝ}
    (hA : (A : F →ₗ[ℂ] F).IsSymmetricBoundedBy γ δ) {t : ℝ} (ht : t ∈ spectrum ℝ A) :
    t ∈ Set.Icc γ δ := by
  refine ⟨le_of_mem_spectrum_real_of_isCoerciveWith hA.isCoerciveWith ht, ?_⟩
  have hneg : ((-A : F →L[ℂ] F) : F →ₗ[ℂ] F).IsCoerciveWith (-δ) := fun x => by
    have := hA.re_inner_le x
    simp only [ContinuousLinearMap.coe_coe, neg_apply, inner_neg_left, map_neg] at this ⊢
    linarith
  have h := le_of_mem_spectrum_real_of_isCoerciveWith hneg (t := -t) (by
    rw [← spectrum.neg_eq, Set.mem_neg, neg_neg]; exact ht)
  linarith

end Complex

end ContinuousLinearMap

namespace Matrix

open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The quadratic form of `Matrix.toEuclideanLin M` is $\operatorname{Re}(x^H M x)$. -/
private theorem re_inner_toEuclideanLin (M : Matrix n n 𝕜) (x : EuclideanSpace 𝕜 n) :
    RCLike.re (inner 𝕜 (Matrix.toEuclideanLin M x) x)
      = RCLike.re (star (WithLp.ofLp x) ⬝ᵥ (M *ᵥ WithLp.ofLp x)) := by
  have h1 : WithLp.ofLp (Matrix.toEuclideanLin M x) = M *ᵥ WithLp.ofLp x := by
    simp [Matrix.toEuclideanLin]
  have h2 : ∀ v w : n → 𝕜, v ⬝ᵥ star w = starRingEnd 𝕜 (star v ⬝ᵥ w) := fun v w => by
    simp [dotProduct, map_sum, RCLike.star_def, mul_comm]
  rw [EuclideanSpace.inner_eq_star_dotProduct, h1, h2, RCLike.conj_re]

/-- Let $M \in \mathbb{K}^{n \times n}$. Then $M$ is positive definite if and only if its Euclidean
operator $x \mapsto Mx$ on $\mathbb{K}^n$ is symmetric coercive.

Positive definiteness is `Matrix.PosDef`, and the Euclidean operator is
`Matrix.toEuclideanLin M`. -/
theorem posDef_iff_isSymmetricCoercive (M : Matrix n n 𝕜) :
    M.PosDef ↔ (Matrix.toEuclideanLin M).IsSymmetricCoercive := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · rintro ⟨hH, hpos⟩
    refine ⟨isSymmetric_toEuclideanLin_iff.2 hH, ?_⟩
    rw [LinearMap.isCoercive_iff_forall_pos]
    intro x hx
    rw [re_inner_toEuclideanLin]
    exact (RCLike.pos_iff.1 (hpos (x := WithLp.ofLp x) (by simpa using hx))).1
  · rintro ⟨hs, hc⟩
    have hH := isSymmetric_toEuclideanLin_iff.1 hs
    refine ⟨hH, fun y hy => ?_⟩
    rw [RCLike.pos_iff]
    refine ⟨?_, hH.im_star_dotProduct_mulVec_self y⟩
    have h := (LinearMap.isCoercive_iff_forall_pos _).1 hc (WithLp.toLp 2 y) (by simpa using hy)
    rw [re_inner_toEuclideanLin] at h
    simpa using h

/-- The Euclidean operator $x \mapsto Mx$ of a positive definite matrix
$M \in \mathbb{K}^{n \times n}$ is symmetric coercive. This is one direction of
`Matrix.posDef_iff_isSymmetricCoercive`, in a form usable with dot notation. -/
theorem PosDef.isSymmetricCoercive_toEuclideanLin {M : Matrix n n 𝕜} (hM : M.PosDef) :
    (toEuclideanLin M).IsSymmetricCoercive :=
  (Matrix.posDef_iff_isSymmetricCoercive M).1 hM

end Matrix

/-! ### Real shifted operators -/

section RealShift

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

open scoped RealInnerProductSpace

namespace ContinuousLinearMap

/-- Let $F$ be a real inner product space and let $H$ be a bounded symmetric operator on $F$. Then
$H + \mu I$ is symmetric for every $\mu \in \mathbb{R}$. -/
theorem isSymmetric_add_smul_one {H : F →L[ℝ] F} (hH : (H : F →ₗ[ℝ] F).IsSymmetric) (μ : ℝ) :
    ((H + μ • (1 : F →L[ℝ] F) : F →L[ℝ] F) : F →ₗ[ℝ] F).IsSymmetric := by
  intro x y
  simp only [ContinuousLinearMap.coe_coe, add_apply, smul_apply, one_apply_eq_self,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, conj_trivial]
  rw [show ⟪H x, y⟫ = ⟪x, H y⟫ from hH x y]

/-- Let $F$ be a real inner product space, let $H$ be a bounded symmetric operator on $F$, and let
$\mu \in \mathbb{R}$. Then $H + \mu I$ is positive semidefinite if and only if
$\langle v, (H + \mu I) v \rangle \ge 0$ for all $v \in F$. -/
theorem isPositive_add_smul_one_iff {H : F →L[ℝ] F} (hH : (H : F →ₗ[ℝ] F).IsSymmetric) (μ : ℝ) :
    ((H + μ • (1 : F →L[ℝ] F) : F →L[ℝ] F) : F →ₗ[ℝ] F).IsPositive ↔
      ∀ v, 0 ≤ ⟪v, (H + μ • (1 : F →L[ℝ] F)) v⟫ := by
  refine ⟨fun h v => ?_, fun h => ⟨isSymmetric_add_smul_one hH μ, fun v => ?_⟩⟩
  · rw [real_inner_comm]; exact h.inner_nonneg_left v
  · simpa [real_inner_comm] using h v

/-- Let $F$ be a real inner product space and let $H$ be a bounded operator on $F$ such that
$H + \mu I$ is positive semidefinite. Then $\langle v, (H + \mu I) v \rangle \ge 0$ for every
$v \in F$. -/
theorem inner_apply_nonneg_of_isPositive {H : F →L[ℝ] F} {μ : ℝ}
    (h : ((H + μ • (1 : F →L[ℝ] F) : F →L[ℝ] F) : F →ₗ[ℝ] F).IsPositive) (v : F) :
    0 ≤ ⟪v, (H + μ • (1 : F →L[ℝ] F)) v⟫ := by
  rw [real_inner_comm]; exact h.inner_nonneg_left v

end ContinuousLinearMap

/-- Let $F$ be a real inner product space and let $T$ be a positive semidefinite operator on $F$. If
$\langle Td, d \rangle = 0$, then $Td = 0$. -/
theorem LinearMap.IsPositive.apply_eq_zero_of_inner_eq_zero {T : F →ₗ[ℝ] F} (hT : T.IsPositive)
    {d : F} (hd : ⟪T d, d⟫ = 0) : T d = 0 := by
  have key : ∀ w : F, ∀ t : ℝ, 0 ≤ 2 * t * ⟪T d, w⟫ + t ^ 2 * ⟪T w, w⟫ := by
    intro w t
    have h := hT.inner_nonneg_left (d + t • w)
    have hs : ⟪T w, d⟫ = ⟪T d, w⟫ := by rw [hT.isSymmetric w d, real_inner_comm]
    simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, conj_trivial, hd, hs] at h
    nlinarith
  have hw : ⟪T d, T d⟫ = 0 := by
    set a := ⟪T d, T d⟫
    set b := ⟪T (T d), T d⟫
    have hb : 0 ≤ b := hT.inner_nonneg_left _
    have ha : 0 ≤ a := real_inner_self_nonneg
    by_contra hne
    have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm hne)
    have := key (T d) (-a / (b + 1))
    have hb1 : 0 < b + 1 := by linarith
    have e : 2 * (-a / (b + 1)) * a + (-a / (b + 1)) ^ 2 * b
        = -a ^ 2 * (b + 2) / (b + 1) ^ 2 := by field_simp; ring
    rw [e] at this
    have : 0 < a ^ 2 * (b + 2) / (b + 1) ^ 2 := by positivity
    linarith [show -a ^ 2 * (b + 2) / (b + 1) ^ 2
      = -(a ^ 2 * (b + 2) / (b + 1) ^ 2) by ring]
  exact inner_self_eq_zero.mp hw

end RealShift

/-! ### Transport of quadratic forms along a linear equivalence -/

namespace LinearMap

section Transport

open scoped RealInnerProductSpace

variable {F F' : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [NormedAddCommGroup F']
  [InnerProductSpace ℝ F'] {S : F →ₗ[ℝ] F} {T : F' →ₗ[ℝ] F'} (Φ : F ≃ₗ[ℝ] F')
  (hST : ∀ x y, ⟪T (Φ x), Φ y⟫ = ⟪S x, y⟫)
include hST

/-- Let $F$ and $F'$ be real inner product spaces, let $S$ be an operator on $F$, let $T$ be an
operator on $F'$, and let $\Phi : F \to F'$ be a linear equivalence with $\langle T(\Phi x),
\Phi y \rangle = \langle Sx, y \rangle$ for all $x, y \in F$. Then $S$ is symmetric if and only
if $T$ is symmetric. -/
theorem isSymmetric_iff_of_inner_map_eq : S.IsSymmetric ↔ T.IsSymmetric := by
  constructor
  · intro hS u v
    obtain ⟨x, rfl⟩ := Φ.surjective u
    obtain ⟨y, rfl⟩ := Φ.surjective v
    rw [hST, real_inner_comm (T (Φ y)), hST, hS]
    exact real_inner_comm _ _
  · intro hT x y
    rw [← hST, hT, real_inner_comm (T (Φ y)), hST]
    exact real_inner_comm _ _

/-- Let $F$ and $F'$ be real inner product spaces, let $S$ be an operator on $F$, let $T$ be an
operator on $F'$, and let $\Phi : F \to F'$ be a linear equivalence with $\langle T(\Phi x),
\Phi y \rangle = \langle Sx, y \rangle$ for all $x, y \in F$. Then $S$ is positive if and only
if $T$ is positive. -/
theorem isPositive_iff_of_inner_map_eq : S.IsPositive ↔ T.IsPositive := by
  rw [isPositive_iff, isPositive_iff, isSymmetric_iff_of_inner_map_eq Φ hST]
  refine and_congr_right fun _ => ⟨fun h u => ?_, fun h x => ?_⟩
  · obtain ⟨x, rfl⟩ := Φ.surjective u
    rw [hST]; exact h x
  · rw [← hST]; exact h (Φ x)

/-- Let $F$ and $F'$ be finite-dimensional real inner product spaces, let $S$ be an operator on $F$,
let $T$ be an operator on $F'$, and let $\Phi : F \to F'$ be a linear equivalence with $\langle
T(\Phi x), \Phi y \rangle = \langle Sx, y \rangle$ for all $x, y \in F$. Then $S$ is symmetric
coercive if and only if $T$ is symmetric coercive.

The map $\Phi$ need not be an isometry, so a coercivity constant is not transported; finite
dimension supplies one through `LinearMap.isCoercive_iff_forall_pos`. -/
theorem isSymmetricCoercive_iff_of_inner_map_eq [FiniteDimensional ℝ F] [FiniteDimensional ℝ F'] :
    S.IsSymmetricCoercive ↔ T.IsSymmetricCoercive := by
  have hc : S.IsCoercive ↔ T.IsCoercive := by
    rw [isCoercive_iff_forall_pos, isCoercive_iff_forall_pos]
    simp only [RCLike.re_to_real]
    refine ⟨fun h u hu => ?_, fun h x hx => ?_⟩
    · obtain ⟨x, rfl⟩ := Φ.surjective u
      rw [hST]; exact h x (fun hx => hu (by rw [hx, map_zero]))
    · rw [← hST]; exact h (Φ x) (fun h0 => hx (Φ.injective (by rw [h0, map_zero])))
  exact ⟨fun h => ⟨(isSymmetric_iff_of_inner_map_eq Φ hST).1 h.isSymmetric, hc.1 h.isCoercive⟩,
    fun h => ⟨(isSymmetric_iff_of_inner_map_eq Φ hST).2 h.isSymmetric, hc.2 h.isCoercive⟩⟩

end Transport

end LinearMap
