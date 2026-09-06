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

An operator `A` on an inner product space is *coercive* when its quadratic form is bounded below
by a positive multiple of `‖x‖²`. This module defines the hypothesis in three strengths — a named
constant, an unnamed one, and a two-sided version enclosing the quadratic form in an interval —
and proves what each buys: injectivity, positivity in Mathlib's sense, the Rayleigh dictionary
between the bounds and the eigenvalues in finite dimension, invertibility on a Hilbert space
(Lax–Milgram), and the reduction of coercivity of a nonsymmetric `A` to coercivity of its
Hermitian part.

Mathlib's own `IsCoercive` is the same notion for a *bilinear form* `V →L[ℝ] V →L[ℝ] ℝ` over the
reals; the definitions here are for an operator, over an `RCLike` field, and are the form the
convergence analysis of iterative methods uses.

## Main definitions

* `LinearMap.IsCoerciveWith A c`: `c ‖x‖² ≤ re ⟪A x, x⟫` for all `x`.
* `LinearMap.IsCoercive A`: `IsCoerciveWith A c` for some `c > 0`. This is what the numerical
  linear algebra literature calls a "positive definite" matrix when no symmetry is required, and
  the linear case of a "strongly monotone" operator.
* `LinearMap.IsSymmetricCoercive A`: symmetric and coercive — SPD/HPD in finite dimension
  (`Matrix.PosDef`), strongly positive self-adjoint operators on Hilbert spaces.
* `LinearMap.IsSymmetricBoundedBy A lmin lmax`: symmetric with
  `lmin ‖x‖² ≤ re ⟪A x, x⟫ ≤ lmax ‖x‖²` — the quadratic-form way of saying "the spectrum lies in
  `[lmin, lmax]`", the hypothesis of the Kantorovich inequality and of every Chebyshev-type
  convergence bound for a symmetric positive definite operator.

## Main statements

* `LinearMap.IsSymmetric.isCoerciveWith_iff_forall_hasEigenvalue` and
  `LinearMap.IsSymmetric.isSymmetricBoundedBy_iff_forall_hasEigenvalue`: in finite dimension the
  quadratic-form bounds are exactly bounds on the eigenvalues;
* `ContinuousLinearMap.exists_equiv_of_isCoerciveWith`: **Lax–Milgram** for a not necessarily
  symmetric bounded coercive operator on a Hilbert space, with `‖A⁻¹‖ ≤ 1 / c`;
* `ContinuousLinearMap.isCoerciveWith_iff_hermitianPart`: coercivity of `A` is coercivity of
  `½ (A + A†)`;
* `Matrix.posDef_iff_isSymmetricCoercive`: `Matrix.PosDef` is symmetric coercivity of the
  Euclidean operator.
-/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace LinearMap

/-- `c ‖x‖² ≤ re ⟪A x, x⟫` for all `x`. -/
def IsCoerciveWith (A : E →ₗ[𝕜] E) (c : ℝ) : Prop :=
  ∀ x, c * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (A x) x)

/-- Coercive: `IsCoerciveWith A c` for some `c > 0`. -/
def IsCoercive (A : E →ₗ[𝕜] E) : Prop := ∃ c : ℝ, 0 < c ∧ A.IsCoerciveWith c

/-- Symmetric and coercive (SPD / HPD / strongly positive self-adjoint). -/
structure IsSymmetricCoercive (A : E →ₗ[𝕜] E) : Prop where
  /-- The operator is symmetric. -/
  isSymmetric : A.IsSymmetric
  /-- The operator is coercive. -/
  isCoercive : A.IsCoercive

section Aux

/-- The quadratic form of `A` is `2`-homogeneous for real scalars. -/
private theorem re_inner_apply_smul (A : E →ₗ[𝕜] E) (t : ℝ) (x : E) :
    RCLike.re (inner 𝕜 (A ((t : 𝕜) • x)) ((t : 𝕜) • x)) = t ^ 2 * RCLike.re (inner 𝕜 (A x) x) := by
  rw [map_smul, inner_smul_left, inner_smul_right, RCLike.conj_ofReal, RCLike.re_ofReal_mul,
    RCLike.re_ofReal_mul]
  ring

/-- The quadratic form of `A` at an eigenvector. -/
private theorem re_inner_apply_self_of_eq_smul {A : E →ₗ[𝕜] E} {μ : 𝕜} {x : E} (h : A x = μ • x) :
    RCLike.re (inner 𝕜 (A x) x) = RCLike.re μ * ‖x‖ ^ 2 := by
  rw [h, inner_smul_left, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.mul_re]
  simp

/-- Coercivity only has to be checked on the unit sphere. -/
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

/-- `|re ⟪A x, x⟫| ≤ ‖A‖ ‖x‖²` for a bounded operator. -/
private theorem abs_re_inner_apply_self_le (A : E →L[𝕜] E) (x : E) :
    |RCLike.re (inner 𝕜 (A x) x)| ≤ ‖A‖ * ‖x‖ ^ 2 :=
  calc |RCLike.re (inner 𝕜 (A x) x)| ≤ ‖inner 𝕜 (A x) x‖ := RCLike.abs_re_le_norm _
    _ ≤ ‖A x‖ * ‖x‖ := norm_inner_le_norm _ _
    _ ≤ ‖A‖ * ‖x‖ * ‖x‖ := by gcongr; exact A.le_opNorm x
    _ = ‖A‖ * ‖x‖ ^ 2 := by ring

end Aux

variable {A : E →ₗ[𝕜] E}

/-- The quadratic form of a coercive operator is strictly positive away from the origin. -/
theorem IsCoercive.inner_self_pos (hA : A.IsCoercive) {x : E} (hx : x ≠ 0) :
    0 < RCLike.re (inner 𝕜 (A x) x) := by
  obtain ⟨c, hc, h⟩ := hA
  exact lt_of_lt_of_le (mul_pos hc (pow_pos (norm_pos_iff.2 hx) 2)) (h x)

/-- A coercive operator is injective: it cannot annihilate a nonzero vector, whose quadratic
form is strictly positive. No completeness or finite dimension is needed. -/
theorem IsCoercive.injective (hA : A.IsCoercive) : Function.Injective A := by
  refine (injective_iff_map_eq_zero A).2 fun x hx => ?_
  by_contra hx0
  simpa [hx] using hA.inner_self_pos hx0

/-- A coercive operator has trivial kernel, the submodule form of `IsCoercive.injective`. -/
theorem IsCoercive.ker_eq_bot (hA : A.IsCoercive) : LinearMap.ker A = ⊥ :=
  LinearMap.ker_eq_bot.2 hA.injective

/-- The defining inequality of `IsCoerciveWith`, as a lemma: `c ‖x‖² ≤ re ⟪A x, x⟫`. Useful where
the bundled hypothesis is more convenient to apply by name than to unfold. -/
theorem IsCoerciveWith.re_inner_apply_self {c : ℝ} (h : A.IsCoerciveWith c) (x : E) :
    c * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (A x) x) := h x

/-- A coercive operator is bounded below: `c ‖x‖ ≤ ‖A x‖`. Cauchy–Schwarz turns the quadratic-form
bound into a bound on the norm, so that the error of an approximate solution is controlled by its
residual, `c ‖x - x*‖ ≤ ‖b - A x‖`, and a coercivity constant bounds the inverse,
`‖A⁻¹ y‖ ≤ ‖y‖ / c`. No sign condition on `c` is needed. -/
theorem IsCoerciveWith.norm_le_norm_apply {c : ℝ} (h : A.IsCoerciveWith c) (x : E) :
    c * ‖x‖ ≤ ‖A x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h1 := h x
  have h2 : RCLike.re (inner 𝕜 (A x) x) ≤ ‖A x‖ * ‖x‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
  nlinarith

/-- In finite dimension, coercive iff `re ⟪A x, x⟫ > 0` for all `x ≠ 0`: compactness of the unit
sphere supplies a uniform constant `c > 0`. -/
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

/-- A symmetric coercive operator is positive in Mathlib's sense, `LinearMap.IsPositive`, so
the whole positive-operator API applies to it. The converse fails: a positive operator need not
have a strictly positive coercivity constant. -/
theorem IsSymmetricCoercive.isPositive (hA : A.IsSymmetricCoercive) : A.IsPositive :=
  ⟨hA.isSymmetric, fun x => by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · exact (hA.isCoercive.inner_self_pos hx).le⟩

section Rayleigh

variable [FiniteDimensional 𝕜 E]

/-- The Rayleigh quotients of a linear map in finite dimension are bounded below. -/
private theorem bddBelow_rayleigh (A : E →ₗ[𝕜] E) :
    BddBelow (Set.range fun y : {y : E // y ≠ 0} =>
      RCLike.re (inner 𝕜 (A y) y) / ‖(y : E)‖ ^ 2) := by
  refine ⟨-‖LinearMap.toContinuousLinearMap A‖, ?_⟩
  rintro _ ⟨y, rfl⟩
  have h := (LinearMap.toContinuousLinearMap A).rayleighQuotient_le_norm (y : E)
  rw [abs_le] at h
  simpa [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf] using h.1

/-- The Rayleigh quotients of a linear map in finite dimension are bounded above. -/
private theorem bddAbove_rayleigh (A : E →ₗ[𝕜] E) :
    BddAbove (Set.range fun y : {y : E // y ≠ 0} =>
      RCLike.re (inner 𝕜 (A y) y) / ‖(y : E)‖ ^ 2) := by
  refine ⟨‖LinearMap.toContinuousLinearMap A‖, ?_⟩
  rintro _ ⟨y, rfl⟩
  have h := (LinearMap.toContinuousLinearMap A).rayleighQuotient_le_norm (y : E)
  rw [abs_le] at h
  simpa [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf] using h.2

/-- A lower eigenvalue bound is a lower quadratic-form bound (Rayleigh, finite dimension). -/
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

/-- An upper eigenvalue bound is an upper quadratic-form bound (Rayleigh, finite dimension). -/
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

/-- For symmetric `A`, coercivity is equivalent to all eigenvalues being `≥ c` (finite
dimension); the best constant is the smallest eigenvalue. -/
theorem IsSymmetric.isCoerciveWith_iff_forall_hasEigenvalue [FiniteDimensional 𝕜 E]
    (hA : A.IsSymmetric) (c : ℝ) :
    A.IsCoerciveWith c ↔ ∀ μ : 𝕜, Module.End.HasEigenvalue A μ → c ≤ RCLike.re μ := by
  refine ⟨fun hc μ hμ => ?_, fun h => le_re_inner_of_forall_hasEigenvalue hA h⟩
  obtain ⟨x, hx, hx0⟩ := hμ.exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff] at hx
  have h1 := hc x
  rw [re_inner_apply_self_of_eq_smul hx] at h1
  exact le_of_mul_le_mul_right (by linarith) (pow_pos (norm_pos_iff.2 hx0) 2)

/-- Symmetric coercive operators have positive real eigenvalues. -/
theorem IsSymmetricCoercive.re_pos_of_hasEigenvalue (hA : A.IsSymmetricCoercive) {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue A μ) : 0 < RCLike.re μ := by
  obtain ⟨x, hx, hx0⟩ := hμ.exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff] at hx
  have h1 := hA.isCoercive.inner_self_pos hx0
  rw [re_inner_apply_self_of_eq_smul hx] at h1
  exact (mul_pos_iff_of_pos_right (pow_pos (norm_pos_iff.2 hx0) 2)).mp h1

/-- `lmin ‖x‖² ≤ re ⟪A x, x⟫ ≤ lmax ‖x‖²` for symmetric `A`: "the spectrum of `A` lies in
`[lmin, lmax]`" stated through the quadratic form; for a symmetric positive definite matrix one
may take `lmin = λmin` and `lmax = λmax`. In finite dimension it is equivalent to all eigenvalues
lying in `[lmin, lmax]` (`IsSymmetric.isSymmetricBoundedBy_iff_forall_hasEigenvalue`); it makes
sense in any inner product space, passes to compressions, and is the hypothesis of all
Chebyshev-type convergence bounds. -/
structure IsSymmetricBoundedBy (A : E →ₗ[𝕜] E) (lmin lmax : ℝ) : Prop where
  /-- The operator is symmetric. -/
  isSymmetric : A.IsSymmetric
  /-- The quadratic form is bounded below by `lmin ‖x‖²`. -/
  le_re_inner : ∀ x, lmin * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (A x) x)
  /-- The quadratic form is bounded above by `lmax ‖x‖²`. -/
  re_inner_le : ∀ x, RCLike.re (inner 𝕜 (A x) x) ≤ lmax * ‖x‖ ^ 2

namespace IsSymmetricBoundedBy

variable {lmin lmax : ℝ} (hA : A.IsSymmetricBoundedBy lmin lmax)
include hA

/-- The lower bound of the enclosing interval is a coercivity constant. -/
theorem isCoerciveWith : A.IsCoerciveWith lmin := hA.le_re_inner

/-- An operator whose quadratic form is enclosed in `[lmin, lmax]` with `lmin > 0` is symmetric
coercive, i.e. symmetric positive definite. -/
theorem isSymmetricCoercive (hl : 0 < lmin) : A.IsSymmetricCoercive :=
  ⟨hA.isSymmetric, lmin, hl, hA.le_re_inner⟩

/-- Rayleigh quotients lie in `[lmin, lmax]`. -/
theorem rayleigh_mem_Icc {x : E} (hx : x ≠ 0) :
    RCLike.re (inner 𝕜 (A x) x) / ‖x‖ ^ 2 ∈ Set.Icc lmin lmax := by
  have hx2 : (0 : ℝ) < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.2 hx) 2
  exact ⟨(le_div_iff₀ hx2).2 (hA.le_re_inner x), (div_le_iff₀ hx2).2 (hA.re_inner_le x)⟩

/-- Eigenvalues lie in `[lmin, lmax]`. -/
theorem re_mem_Icc_of_hasEigenvalue {μ : 𝕜} (hμ : Module.End.HasEigenvalue A μ) :
    RCLike.re μ ∈ Set.Icc lmin lmax := by
  obtain ⟨x, hx, hx0⟩ := hμ.exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff] at hx
  have h := hA.rayleigh_mem_Icc hx0
  rwa [re_inner_apply_self_of_eq_smul hx, mul_div_assoc,
    div_self (pow_pos (norm_pos_iff.2 hx0) 2).ne', mul_one] at h

/-- The enclosing interval may be widened: bounds valid on `[lmin, lmax]` hold on any larger
interval. Convergence estimates stated for a wider interval are therefore weaker, which is what
makes `lmin`, `lmax` usable as computable estimates of the extreme eigenvalues. -/
theorem mono {lmin' lmax' : ℝ} (h₁ : lmin' ≤ lmin) (h₂ : lmax ≤ lmax') :
    A.IsSymmetricBoundedBy lmin' lmax' :=
  ⟨hA.isSymmetric,
    fun x => (mul_le_mul_of_nonneg_right h₁ (sq_nonneg _)).trans (hA.le_re_inner x),
    fun x => (hA.re_inner_le x).trans (mul_le_mul_of_nonneg_right h₂ (sq_nonneg _))⟩

/-- The bounds pass to any symmetric `B` on a space isometrically embedded in `E` whose
quadratic form agrees with that of `A` (restrictions to invariant subspaces, compressions). -/
theorem of_inner_eq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] {B : F →ₗ[𝕜] F}
    (hB : B.IsSymmetric) (ι : F →ₗᵢ[𝕜] E)
    (h : ∀ x, inner 𝕜 (B x) x = inner 𝕜 (A (ι x)) (ι x)) : B.IsSymmetricBoundedBy lmin lmax := by
  refine ⟨hB, fun x => ?_, fun x => ?_⟩
  · rw [h x, ← ι.norm_map x]; exact hA.le_re_inner _
  · rw [h x, ← ι.norm_map x]; exact hA.re_inner_le _

end IsSymmetricBoundedBy

/-- In finite dimension the quadratic-form bounds are equivalent to eigenvalue bounds
(Rayleigh: `LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional` and `_iInf_`). -/
theorem IsSymmetric.isSymmetricBoundedBy_iff_forall_hasEigenvalue [FiniteDimensional 𝕜 E]
    (hA : A.IsSymmetric) (lmin lmax : ℝ) :
    A.IsSymmetricBoundedBy lmin lmax ↔
      ∀ μ : 𝕜, Module.End.HasEigenvalue A μ → RCLike.re μ ∈ Set.Icc lmin lmax :=
  ⟨fun h _ hμ => h.re_mem_Icc_of_hasEigenvalue hμ, fun h =>
    ⟨hA, le_re_inner_of_forall_hasEigenvalue hA fun μ hμ => (h μ hμ).1,
      re_inner_le_of_forall_hasEigenvalue hA fun μ hμ => (h μ hμ).2⟩⟩

/-- A bounded symmetric operator is bounded by `± ‖A‖`. -/
theorem IsSymmetric.isSymmetricBoundedBy_neg_norm_norm {A : E →L[𝕜] E}
    (hA : (A : E →ₗ[𝕜] E).IsSymmetric) : (A : E →ₗ[𝕜] E).IsSymmetricBoundedBy (-‖A‖) ‖A‖ := by
  refine ⟨hA, fun x => ?_, fun x => ?_⟩
  · rw [neg_mul]
    exact (abs_le.1 (abs_re_inner_apply_self_le A x)).1
  · exact (abs_le.1 (abs_re_inner_apply_self_le A x)).2

end LinearMap

section Richardson

/-- The damped-Richardson contraction estimate for a bounded operator with
`c ‖x‖² ≤ re ⟪A x, x⟫`: `‖x - θ A x‖² ≤ (1 - 2θc + θ²‖A‖²) ‖x‖²`. For `0 < θ < 2c/‖A‖²` the
factor on the right is `< 1`, which is the standard convergence proof for the Richardson
iteration `x ↦ x - θ (A x - b)`. -/
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

variable [CompleteSpace E]

/-- A bounded coercive operator on a Hilbert space is invertible with `‖A⁻¹‖ ≤ 1 / c`. This is
the Lax–Milgram theorem, for an operator that need not be symmetric. -/
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

/-- The Hermitian part `½ (A + A†)` has the same quadratic form as `A`. -/
theorem re_inner_hermitianPart_apply (A : E →L[𝕜] E) (x : E) :
    RCLike.re (inner 𝕜 (((2⁻¹ : 𝕜) • (A + adjoint A)) x) x) = RCLike.re (inner 𝕜 (A x) x) := by
  have h2 : (2⁻¹ : 𝕜) = ((2⁻¹ : ℝ) : 𝕜) := by rw [RCLike.ofReal_inv, RCLike.ofReal_ofNat]
  have h1 : inner 𝕜 ((adjoint A) x) x = starRingEnd 𝕜 (inner 𝕜 (A x) x) := by
    rw [ContinuousLinearMap.adjoint_inner_left, ← inner_conj_symm]
  rw [smul_apply, add_apply, inner_smul_left, inner_add_left, h1, h2, RCLike.conj_ofReal,
    RCLike.re_ofReal_mul, map_add, RCLike.conj_re]
  ring

/-- Coercivity of `A` is coercivity of its Hermitian part; in particular the best coercivity
constant of `A` is `λmin(½ (A + A†))`, the constant that governs the convergence rate of the
Richardson and steepest-descent iterations for a nonsymmetric `A`. -/
theorem isCoerciveWith_iff_hermitianPart (A : E →L[𝕜] E) (c : ℝ) :
    (A : E →ₗ[𝕜] E).IsCoerciveWith c ↔
      (((2⁻¹ : 𝕜) • (A + adjoint A) : E →L[𝕜] E) : E →ₗ[𝕜] E).IsCoerciveWith c := by
  simp only [LinearMap.IsCoerciveWith, ContinuousLinearMap.coe_coe,
    re_inner_hermitianPart_apply]

end ContinuousLinearMap

namespace Matrix

open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The quadratic form of `toEuclideanLin M` is `xᴴ M x`. -/
private theorem re_inner_toEuclideanLin (M : Matrix n n 𝕜) (x : EuclideanSpace 𝕜 n) :
    RCLike.re (inner 𝕜 (Matrix.toEuclideanLin M x) x)
      = RCLike.re (star (WithLp.ofLp x) ⬝ᵥ (M *ᵥ WithLp.ofLp x)) := by
  have h1 : WithLp.ofLp (Matrix.toEuclideanLin M x) = M *ᵥ WithLp.ofLp x := by
    simp [Matrix.toEuclideanLin]
  have h2 : ∀ v w : n → 𝕜, v ⬝ᵥ star w = starRingEnd 𝕜 (star v ⬝ᵥ w) := fun v w => by
    simp [dotProduct, map_sum, RCLike.star_def, mul_comm]
  rw [EuclideanSpace.inner_eq_star_dotProduct, h1, h2, RCLike.conj_re]

/-- `Matrix.PosDef` is symmetric coercivity of the Euclidean operator. -/
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

end Matrix
