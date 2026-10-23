/-
Upstreaming candidate: general material with no numerical-analysis-specific content.
Natural home: `Mathlib.Analysis.InnerProductSpace.Positive`.
-/
import Numlib.Analysis.InnerProductSpace.Coercive
import Mathlib.Tactic
/-!
# Norm comparison between actual shifted-system solutions

Numerical positivity of the unshifted operator gives a nonnegative cross term
between the solution difference and the more strongly shifted solution.
Cauchy–Schwarz then compares their norms, with no inverse, symmetry,
completeness or finite-dimensional assumption.
-/

namespace LinearMap
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
/-- A positive real scalar shift decreases the norm of an actual solution,
when the unshifted linear operator has a nonnegative real quadratic form. -/
theorem norm_le_norm_of_shifted_solve {A : E →ₗ[𝕜] E}
    (hA : ∀ v, 0 ≤ RCLike.re (inner 𝕜 (A v) v)) {δ : ℝ} (hδ : 0 < δ)
    {x y : E} (he : A x = A y + (δ : 𝕜) • y) : ‖y‖ ≤ ‖x‖ := by
  have hz : A (x - y) = (δ : 𝕜) • y := by rw [map_sub, he]; abel
  have hpos := hA (x - y)
  rw [hz, inner_smul_left, RCLike.conj_ofReal, RCLike.re_ofReal_mul,
    inner_sub_right, map_sub, inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow] at hpos
  have hi : ‖y‖ ^ 2 ≤ RCLike.re (inner 𝕜 y x) := by nlinarith
  have hc := re_inner_le_norm (𝕜 := 𝕜) y x
  rcases (norm_nonneg y).eq_or_lt with hy | hy
  · rw [←hy]; exact norm_nonneg _
  · nlinarith
/-- A positive real shift strictly decreases the norm of every nonzero actual solution. -/
theorem norm_lt_norm_of_shifted_solve {A : E →ₗ[𝕜] E}
    (hA : ∀ v, 0 ≤ RCLike.re (inner 𝕜 (A v) v)) {δ : ℝ} (hδ : 0 < δ)
    {x y : E} (hy : y ≠ 0) (he : A x = A y + (δ : 𝕜) • y) : ‖y‖ < ‖x‖ := by
  have hz : A (x - y) = (δ : 𝕜) • y := by rw [map_sub, he]; abel
  have hδK : (δ : 𝕜) ≠ 0 := by exact_mod_cast hδ.ne'
  have hxy : x - y ≠ 0 := by
    intro hh
    rw [hh, map_zero] at hz
    exact (smul_ne_zero hδK hy) hz.symm
  have hp := hA (x - y)
  rw [hz, inner_smul_left, RCLike.conj_ofReal, RCLike.re_ofReal_mul] at hp
  have hi : 0 ≤ RCLike.re (inner 𝕜 y (x - y)) := by nlinarith
  have heq := norm_add_sq (𝕜 := 𝕜) y (x - y)
  rw [add_sub_cancel] at heq
  have hn := sq_pos_of_pos (norm_pos_iff.mpr hxy)
  nlinarith [norm_nonneg x, norm_nonneg y]

end LinearMap
