import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# The eigenvalue problem as a nonlinear system: Newton corrections and Jacobi–Davidson

The eigenpairs of an operator are the zeros of a residual map, and the Jacobi orthogonal component
correction, Davidson and Jacobi–Davidson methods are (approximate) Newton steps for it
([golub2013matrix] §10.6, after Sorensen 2002 and Stewart; [saad2011numerical] Ch. 8 treats the same
methods). This module holds what has a precise statement:

* the residual maps whose zeros are normalized eigenpairs, for a linear normalization `ℓ x = 1`
  (`ContinuousLinearMap.eigenpairResidual`, any nontrivially normed field) and for the spherical one
  `(‖x‖² − 1)/2` over `ℝ` (`ContinuousLinearMap.eigenpairResidualSphere`), with their Fréchet
  derivatives: "(10.6.5) is the Jacobian system of Newton's method" is
  `ContinuousLinearMap.hasFDerivAt_eigenpairResidual`;
* the closed form of the bordered Newton correction ((10.6.6)–(10.6.7)), stated for an arbitrary
  endomorphism over a field, so that it covers the approximate operator `M` of (10.6.8)–(10.6.10)
  by the same lemma (`JacobiDavidson.newtonCorrection_eq`);
* the equivalence of the bordered system with the projected correction equation of Jacobi–Davidson
  ((10.6.17) ⇔ (10.6.18), `JacobiDavidson.newtonStep_iff_projected`). The book derives only one
  direction; "the correction is obtained by solving the projected system" needs the other.

The methods themselves are algorithms whose specification is a Ritz–Galerkin condition; no
convergence theorem is claimed. The residual maps are general Newton maps for eigenpairs of any
bounded operator and live in the namespace of the type.

## References

* [golub2013matrix] §10.6.
-/

open scoped InnerProductSpace

namespace ContinuousLinearMap

section Linear

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] (A : E →L[𝕜] E) (ℓ : E →L[𝕜] 𝕜)

/-- The eigenpair residual with the linear normalization `ℓ x = 1`:
`F (x, μ) = (A x − μ x, ℓ x − 1)`, the book's `F([x; λ]) = [A x − λ x; wᵀ x − 1]`
([golub2013matrix] §10.6.1). Its zeros are the eigenpairs `(x, μ)` with `ℓ x = 1`. -/
def eigenpairResidual (p : E × 𝕜) : E × 𝕜 :=
  (A p.1 - p.2 • p.1, ℓ p.1 - 1)

/-- The zeros of the residual are exactly the normalized eigenpairs. -/
theorem eigenpairResidual_eq_zero_iff (x : E) (μ : 𝕜) :
    A.eigenpairResidual ℓ (x, μ) = 0 ↔ A x = μ • x ∧ ℓ x = 1 := by
  simp [eigenpairResidual, Prod.ext_iff, sub_eq_zero]

/-- The derivative of the eigen-residual `(x, μ) ↦ A x − μ x`, the first component of both
eigenpair residuals: `(δx, δμ) ↦ A δx − μ δx − δμ x`. -/
theorem hasFDerivAt_apply_sub_smul (x : E) (μ : 𝕜) :
    HasFDerivAt (fun p : E × 𝕜 => A p.1 - p.2 • p.1)
      ((A - μ • ContinuousLinearMap.id 𝕜 E).comp (ContinuousLinearMap.fst 𝕜 E 𝕜) -
        (ContinuousLinearMap.snd 𝕜 E 𝕜).smulRight x) (x, μ) := by
  have hA := (A.comp (ContinuousLinearMap.fst 𝕜 E 𝕜)).hasFDerivAt (x := (x, μ))
  have hs := (hasFDerivAt_snd (𝕜 := 𝕜) (p := (x, μ))).smul
    (hasFDerivAt_fst (𝕜 := 𝕜) (p := (x, μ)))
  refine (hA.sub hs).congr_fderiv ?_
  ext p <;> simp

/-- **The Jacobian of the eigenpair residual** ([golub2013matrix] (10.6.5): "precisely the Jacobian
system that arises if Newton's method is used"): at `(x, μ)` the derivative is the bordered operator
`(δx, δμ) ↦ (A δx − μ δx − δμ x, ℓ δx)`. -/
theorem hasFDerivAt_eigenpairResidual (x : E) (μ : 𝕜) :
    HasFDerivAt (A.eigenpairResidual ℓ)
      (((A - μ • ContinuousLinearMap.id 𝕜 E).comp (ContinuousLinearMap.fst 𝕜 E 𝕜) -
          (ContinuousLinearMap.snd 𝕜 E 𝕜).smulRight x).prod
        (ℓ.comp (ContinuousLinearMap.fst 𝕜 E 𝕜))) (x, μ) := by
  have h2 : HasFDerivAt (fun p : E × 𝕜 => ℓ p.1 - 1) (ℓ.comp (ContinuousLinearMap.fst 𝕜 E 𝕜))
      (x, μ) :=
    (ℓ.comp (ContinuousLinearMap.fst 𝕜 E 𝕜)).hasFDerivAt.sub_const 1
  exact (A.hasFDerivAt_apply_sub_smul x μ).prodMk h2

end Linear

section Sphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : E →L[ℝ] E)

/-- The eigenpair residual with the spherical normalization, over `ℝ`:
`F (x, μ) = (A x − μ x, (‖x‖² − 1)/2)`, the function of [golub2013matrix] (10.6.17). -/
noncomputable def eigenpairResidualSphere (p : E × ℝ) : E × ℝ :=
  (A p.1 - p.2 • p.1, (‖p.1‖ ^ 2 - 1) / 2)

/-- The zeros of the spherical residual are exactly the unit eigenpairs. -/
theorem eigenpairResidualSphere_eq_zero_iff (x : E) (μ : ℝ) :
    A.eigenpairResidualSphere (x, μ) = 0 ↔ A x = μ • x ∧ ‖x‖ = 1 := by
  simp only [eigenpairResidualSphere, Prod.mk_eq_zero, sub_eq_zero, div_eq_zero_iff,
    two_ne_zero, or_false]
  refine and_congr Iff.rfl ⟨fun h => ?_, fun h => by rw [h, one_pow]⟩
  have h0 : 0 ≤ ‖x‖ := norm_nonneg x
  nlinarith

/-- **The Jacobian of the spherical residual** ([golub2013matrix] (10.6.17)): at `(x, μ)` the
derivative is `(δx, δμ) ↦ (A δx − μ δx − δμ x, ⟪x, δx⟫)`. -/
theorem hasFDerivAt_eigenpairResidualSphere (x : E) (μ : ℝ) :
    HasFDerivAt A.eigenpairResidualSphere
      (((A - μ • ContinuousLinearMap.id ℝ E).comp (ContinuousLinearMap.fst ℝ E ℝ) -
          (ContinuousLinearMap.snd ℝ E ℝ).smulRight x).prod
        ((innerSL ℝ x).comp (ContinuousLinearMap.fst ℝ E ℝ))) (x, μ) := by
  have h2 : HasFDerivAt (fun p : E × ℝ => (‖p.1‖ ^ 2 - 1) / 2)
      ((innerSL ℝ x).comp (ContinuousLinearMap.fst ℝ E ℝ)) (x, μ) := by
    have hn := (((hasFDerivAt_fst (𝕜 := ℝ) (p := (x, μ))).norm_sq).sub_const 1).const_smul
      (1 / 2 : ℝ)
    have hf : (fun p : E × ℝ => (‖p.1‖ ^ 2 - 1) / 2) =
        fun p => (1 / 2 : ℝ) • (‖p.1‖ ^ 2 - 1) := by
      funext p
      rw [smul_eq_mul]
      ring
    rw [hf]
    refine hn.congr_fderiv ?_
    ext p <;> simp
  exact (A.hasFDerivAt_apply_sub_smul x μ).prodMk h2

end Sphere

end ContinuousLinearMap

namespace JacobiDavidson

section Field

variable {𝕜 : Type*} [Field 𝕜] {E : Type*} [AddCommGroup E] [Module 𝕜 E]

/-- **The bordered Newton correction in closed form** ([golub2013matrix] (10.6.6)–(10.6.7), and with
the approximate operator `M` for `A`, (10.6.9)–(10.6.10)). Let `A − μ` be invertible, write
`R = (A − μ)⁻¹`, and let `ℓ (R x) ≠ 0`. For every right-hand side `r`, the bordered system
`(A − μ) δx − δμ x = −r`, `ℓ δx = 0` has exactly one solution,
`δμ = ℓ (R r) / ℓ (R x)`, `δx = −R (r − δμ x)`. With `r = A x − μ x` and `ℓ x = 1` it is the
Newton step for `ContinuousLinearMap.eigenpairResidual` ((10.6.4)). Pure algebra. -/
theorem newtonCorrection_eq {A : Module.End 𝕜 E} {μ : 𝕜} (hA : IsUnit (A - μ • 1))
    (ℓ : E →ₗ[𝕜] 𝕜) {x : E} (hx : ℓ (Ring.inverse (A - μ • 1) x) ≠ 0) (r δx : E) (δμ : 𝕜) :
    ((A - μ • 1) δx - δμ • x = -r ∧ ℓ δx = 0) ↔
      (δμ = ℓ (Ring.inverse (A - μ • 1) r) / ℓ (Ring.inverse (A - μ • 1) x) ∧
        δx = -Ring.inverse (A - μ • 1) (r - δμ • x)) := by
  set T := A - μ • 1
  set R := Ring.inverse T
  have hTR : ∀ y, T (R y) = y := fun y => by
    rw [← Module.End.mul_apply, Ring.mul_inverse_cancel T hA, Module.End.one_apply]
  have hRT : ∀ y, R (T y) = y := fun y => by
    rw [← Module.End.mul_apply, Ring.inverse_mul_cancel T hA, Module.End.one_apply]
  constructor
  · rintro ⟨h1, h2⟩
    have hT : T δx = δμ • x - r := by
      rw [sub_eq_add_neg, ← h1]
      abel
    have hδx : δx = -R (r - δμ • x) := by
      rw [← hRT δx, hT, ← neg_sub, map_neg]
    refine ⟨?_, hδx⟩
    rw [hδx, map_neg, map_sub, map_smul, map_sub, map_smul, smul_eq_mul, neg_eq_zero,
      sub_eq_zero] at h2
    rw [h2, mul_div_assoc, div_self hx, mul_one]
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [h2, map_neg, hTR]
      abel
    · rw [h2, map_neg, map_sub, map_smul, map_sub, map_smul, smul_eq_mul, h1, div_mul_cancel₀ _ hx,
        sub_self, neg_zero]

end Field

section InnerProduct

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **The Jacobi–Davidson correction equation** ([golub2013matrix] (10.6.17) ⇒ (10.6.18), and
conversely). Let `‖x‖ = 1`, `μ = ⟪x, A x⟫` (the Rayleigh quotient), `r = A x − μ x` and `P` the
orthogonal projection onto `x^⊥`. A correction `δx ⊥ x` solves the bordered Newton system
`(A − μ) δx − δμ x = −r` for some `δμ` iff it solves the projected equation
`P (A − μ) P δx = −r`; the multiplier is then `δμ = ⟪x, (A − μ) δx⟫`. -/
theorem newtonStep_iff_projected (A : E →ₗ[𝕜] E) {x : E} (hx : ‖x‖ = 1) (δx : E) :
    (∃ δμ : 𝕜, (A - ⟪x, A x⟫_𝕜 • 1) δx - δμ • x = -(A x - ⟪x, A x⟫_𝕜 • x) ∧ ⟪x, δx⟫_𝕜 = 0) ↔
      (⟪x, δx⟫_𝕜 = 0 ∧
        (𝕜 ∙ x)ᗮ.starProjection ((A - ⟪x, A x⟫_𝕜 • 1) ((𝕜 ∙ x)ᗮ.starProjection δx)) =
          -(A x - ⟪x, A x⟫_𝕜 • x)) := by
  have hxx : ⟪x, x⟫_𝕜 = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hx]
    simp
  have hmem : ∀ y, y ∈ (𝕜 ∙ x)ᗮ ↔ ⟪x, y⟫_𝕜 = 0 := fun y =>
    Submodule.mem_orthogonal_singleton_iff_inner_right
  have hr : ⟪x, A x - ⟪x, A x⟫_𝕜 • x⟫_𝕜 = 0 := by
    rw [inner_sub_right, inner_smul_right, hxx, mul_one, sub_self]
  have hPr : (𝕜 ∙ x)ᗮ.starProjection (A x - ⟪x, A x⟫_𝕜 • x) = A x - ⟪x, A x⟫_𝕜 • x :=
    Submodule.starProjection_eq_self_iff.2 ((hmem _).2 hr)
  have hPx : (𝕜 ∙ x)ᗮ.starProjection x = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff (K := (𝕜 ∙ x)ᗮ)).2
      (Submodule.le_orthogonal_orthogonal _ (Submodule.mem_span_singleton_self x))
  constructor
  · rintro ⟨δμ, h1, h2⟩
    refine ⟨h2, ?_⟩
    have hT : (A - ⟪x, A x⟫_𝕜 • 1) δx = -(A x - ⟪x, A x⟫_𝕜 • x) + δμ • x := by
      rw [← h1]
      abel
    rw [Submodule.starProjection_eq_self_iff.2 ((hmem δx).2 h2), hT, map_add, map_neg, map_smul,
      hPr, hPx, smul_zero, add_zero]
  · rintro ⟨h2, h1⟩
    rw [Submodule.starProjection_eq_self_iff.2 ((hmem δx).2 h2)] at h1
    refine ⟨⟪x, (A - ⟪x, A x⟫_𝕜 • 1) δx⟫_𝕜, ?_, h2⟩
    have hz : ⟪x, (A - ⟪x, A x⟫_𝕜 • 1) δx - ⟪x, (A - ⟪x, A x⟫_𝕜 • 1) δx⟫_𝕜 • x +
        (A x - ⟪x, A x⟫_𝕜 • x)⟫_𝕜 = 0 := by
      rw [inner_add_right, inner_sub_right, inner_smul_right, hxx, mul_one, sub_self, zero_add, hr]
    have hz0 := Submodule.starProjection_eq_self_iff.2 ((hmem _).2 hz)
    rw [map_add, map_sub, map_smul, h1, hPx, smul_zero, sub_zero, hPr, neg_add_cancel] at hz0
    rw [← sub_eq_zero, sub_neg_eq_add]
    exact hz0.symm

end InnerProduct

end JacobiDavidson
