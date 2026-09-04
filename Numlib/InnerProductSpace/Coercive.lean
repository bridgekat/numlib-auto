/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.Positive`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Coercive and symmetric coercive operators

* `LinearMap.IsCoerciveWith A c`: `c ‖x‖² ≤ re ⟪A x, x⟫` for all `x`.
* `LinearMap.IsCoercive A`: `IsCoerciveWith A c` for some `c > 0` — Saad's "positive definite"
  (no symmetry required), Atkinson–Han's "strongly monotone" (linear case), Kress's positive
  definiteness for Hermitian matrices.
* `LinearMap.IsSymmetricCoercive A`: symmetric and coercive — SPD/HPD in finite dimension
  (`Matrix.PosDef`), strongly positive self-adjoint operators on Hilbert spaces.
* `LinearMap.IsSymmetricBoundedBy A lmin lmax`: symmetric with
  `lmin ‖x‖² ≤ re ⟪A x, x⟫ ≤ lmax ‖x‖²` — the quadratic-form way of saying "the spectrum lies in
  `[lmin, lmax]`", the hypothesis of every Chebyshev-type convergence bound (Atkinson–Han
  Thm 5.6.1, Saad Thm 6.29, Kantorovich).
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
  isSymmetric : A.IsSymmetric
  isCoercive : A.IsCoercive

variable {A : E →ₗ[𝕜] E}

theorem IsCoercive.inner_self_pos (hA : A.IsCoercive) {x : E} (hx : x ≠ 0) :
    0 < RCLike.re (inner 𝕜 (A x) x) := by
  sorry

theorem IsCoercive.injective (hA : A.IsCoercive) : Function.Injective A := by
  sorry

theorem IsCoercive.ker_eq_bot (hA : A.IsCoercive) : LinearMap.ker A = ⊥ := by
  sorry

/-- Coercivity of `A` is coercivity of its symmetric part `(A + A†)/2`, for bounded `A`;
here in the form that only uses the quadratic form. -/
theorem IsCoerciveWith.re_inner_apply_self (h : A.IsCoerciveWith c) (x : E) :
    c * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (A x) x) := h x

/-- Saad Thm 1.34 (finite dimension): coercive iff `re ⟪A x, x⟫ > 0` for all `x ≠ 0`. -/
theorem isCoercive_iff_forall_pos [FiniteDimensional 𝕜 E] (A : E →ₗ[𝕜] E) :
    A.IsCoercive ↔ ∀ x ≠ 0, 0 < RCLike.re (inner 𝕜 (A x) x) := by
  sorry

theorem IsSymmetricCoercive.isPositive (hA : A.IsSymmetricCoercive) : A.IsPositive := by
  sorry

/-- For symmetric `A`, coercivity is equivalent to all eigenvalues being `≥ c` (finite
dimension); the best constant is the smallest eigenvalue. -/
theorem IsSymmetric.isCoerciveWith_iff_forall_hasEigenvalue [FiniteDimensional 𝕜 E]
    (hA : A.IsSymmetric) (c : ℝ) :
    A.IsCoerciveWith c ↔ ∀ μ : 𝕜, Module.End.HasEigenvalue A μ → c ≤ RCLike.re μ := by
  sorry

/-- Symmetric coercive operators have positive real eigenvalues. -/
theorem IsSymmetricCoercive.re_pos_of_hasEigenvalue (hA : A.IsSymmetricCoercive) {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue A μ) : 0 < RCLike.re μ := by
  sorry

/-- `lmin ‖x‖² ≤ re ⟪A x, x⟫ ≤ lmax ‖x‖²` for symmetric `A`: "the spectrum of `A` lies in
`[lmin, lmax]`" stated through the quadratic form (the hypothesis of Atkinson–Han Thm 5.6.1;
Saad's `λmin, λmax` of an SPD matrix). In finite dimension it is equivalent to all eigenvalues
lying in `[lmin, lmax]` (`IsSymmetric.isSymmetricBoundedBy_iff_forall_hasEigenvalue`); it makes
sense in any inner product space, passes to compressions, and is the hypothesis of all
Chebyshev-type convergence bounds. -/
structure IsSymmetricBoundedBy (A : E →ₗ[𝕜] E) (lmin lmax : ℝ) : Prop where
  isSymmetric : A.IsSymmetric
  le_re_inner : ∀ x, lmin * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (A x) x)
  re_inner_le : ∀ x, RCLike.re (inner 𝕜 (A x) x) ≤ lmax * ‖x‖ ^ 2

namespace IsSymmetricBoundedBy

variable {lmin lmax : ℝ} (hA : A.IsSymmetricBoundedBy lmin lmax)
include hA

theorem isCoerciveWith : A.IsCoerciveWith lmin := hA.le_re_inner

theorem isSymmetricCoercive (hl : 0 < lmin) : A.IsSymmetricCoercive :=
  ⟨hA.isSymmetric, lmin, hl, hA.le_re_inner⟩

/-- Rayleigh quotients lie in `[lmin, lmax]`. -/
theorem rayleigh_mem_Icc {x : E} (hx : x ≠ 0) :
    RCLike.re (inner 𝕜 (A x) x) / ‖x‖ ^ 2 ∈ Set.Icc lmin lmax := by
  sorry

/-- Eigenvalues lie in `[lmin, lmax]`. -/
theorem re_mem_Icc_of_hasEigenvalue {μ : 𝕜} (hμ : Module.End.HasEigenvalue A μ) :
    RCLike.re μ ∈ Set.Icc lmin lmax := by
  sorry

theorem mono {lmin' lmax' : ℝ} (h₁ : lmin' ≤ lmin) (h₂ : lmax ≤ lmax') :
    A.IsSymmetricBoundedBy lmin' lmax' := by
  sorry

/-- The bounds pass to any symmetric `B` on a space isometrically embedded in `E` whose
quadratic form agrees with that of `A` (restrictions to invariant subspaces, compressions). -/
theorem of_inner_eq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] {B : F →ₗ[𝕜] F}
    (hB : B.IsSymmetric) (ι : F →ₗᵢ[𝕜] E)
    (h : ∀ x, inner 𝕜 (B x) x = inner 𝕜 (A (ι x)) (ι x)) : B.IsSymmetricBoundedBy lmin lmax := by
  sorry

end IsSymmetricBoundedBy

/-- In finite dimension the quadratic-form bounds are equivalent to eigenvalue bounds
(Rayleigh: `LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional` and `_iInf_`). -/
theorem IsSymmetric.isSymmetricBoundedBy_iff_forall_hasEigenvalue [FiniteDimensional 𝕜 E]
    (hA : A.IsSymmetric) (lmin lmax : ℝ) :
    A.IsSymmetricBoundedBy lmin lmax ↔
      ∀ μ : 𝕜, Module.End.HasEigenvalue A μ → RCLike.re μ ∈ Set.Icc lmin lmax := by
  sorry

/-- A bounded symmetric operator is bounded by `± ‖A‖`. -/
theorem IsSymmetric.isSymmetricBoundedBy_neg_norm_norm {A : E →L[𝕜] E}
    (hA : (A : E →ₗ[𝕜] E).IsSymmetric) : (A : E →ₗ[𝕜] E).IsSymmetricBoundedBy (-‖A‖) ‖A‖ := by
  sorry

end LinearMap

section Richardson

/-- The damped-Richardson contraction estimate for a bounded operator with
`c ‖x‖² ≤ re ⟪A x, x⟫`: `‖x - θ A x‖² ≤ (1 - 2θc + θ²‖A‖²) ‖x‖²` (Atkinson–Han proof #1 of
Thm 8.3.4 and of Thm 5.1.4; Saad Thm 5.10 / 6.30 proofs; Kress Richardson iteration). -/
theorem ContinuousLinearMap.norm_sub_smul_apply_sq_le {A : E →L[𝕜] E} {c : ℝ}
    (hA : (A : E →ₗ[𝕜] E).IsCoerciveWith c) {θ : ℝ} (hθ : 0 ≤ θ) (x : E) :
    ‖x - (θ : 𝕜) • A x‖ ^ 2 ≤ (1 - 2 * θ * c + θ ^ 2 * ‖A‖ ^ 2) * ‖x‖ ^ 2 := by
  sorry

end Richardson

namespace ContinuousLinearMap

variable [CompleteSpace E]

/-- A bounded coercive operator on a Hilbert space is invertible with `‖A⁻¹‖ ≤ 1 / c`
(linear case of Atkinson–Han Thm 5.1.4; Saad Prop 5.1 in Hilbert spaces). -/
theorem exists_equiv_of_isCoerciveWith {A : E →L[𝕜] E} {c : ℝ} (hc : 0 < c)
    (hA : (A : E →ₗ[𝕜] E).IsCoerciveWith c) :
    ∃ e : E ≃L[𝕜] E, (e : E →L[𝕜] E) = A ∧ ‖(e.symm : E →L[𝕜] E)‖ ≤ 1 / c := by
  sorry

/-- The Hermitian part `½ (A + A†)` has the same quadratic form as `A` (Saad §1.8.3). -/
theorem re_inner_hermitianPart_apply (A : E →L[𝕜] E) (x : E) :
    RCLike.re (inner 𝕜 (((2⁻¹ : 𝕜) • (A + adjoint A)) x) x) = RCLike.re (inner 𝕜 (A x) x) := by
  sorry

/-- Coercivity of `A` is coercivity of its Hermitian part; in particular the best coercivity
constant of `A` is `λmin(½ (A + A†))` (the `μ` of Saad Thm 6.30 / (5.15)). -/
theorem isCoerciveWith_iff_hermitianPart (A : E →L[𝕜] E) (c : ℝ) :
    (A : E →ₗ[𝕜] E).IsCoerciveWith c ↔
      (((2⁻¹ : 𝕜) • (A + adjoint A) : E →L[𝕜] E) : E →ₗ[𝕜] E).IsCoerciveWith c := by
  sorry

end ContinuousLinearMap

namespace Matrix

open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `Matrix.PosDef` is symmetric coercivity of the Euclidean operator. -/
theorem posDef_iff_isSymmetricCoercive (M : Matrix n n 𝕜) :
    M.PosDef ↔ (Matrix.toEuclideanLin M).IsSymmetricCoercive := by
  sorry

end Matrix
