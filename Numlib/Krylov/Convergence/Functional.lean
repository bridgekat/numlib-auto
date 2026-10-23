import Numlib.Krylov.Convergence.CG
import Mathlib.Tactic

/-!
# Krylov decay estimates for annihilating linear functionals

An actual minimal-residual iterate lies in the Krylov space where the
functional vanishes. Coercivity turns its Chebyshev residual bound into an
error bound, and the functional norm gives the desired scalar estimate.
-/

namespace Krylov
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- An actual solution and a bounded linear functional annihilating its first
Krylov directions satisfy the sharp Chebyshev decay bound. The zero-step and
single-eigenvalue cases are included. -/
theorem functional_solution_decay {A : E →ₗ[𝕜] E} {lo hi C : ℝ}
    (hlo : 0 < lo) (hle : lo ≤ hi) (hC : 0 ≤ C)
    (hA : A.IsSymmetricBoundedBy lo hi) (φ : E →ₗ[𝕜] 𝕜)
    (hφ : ∀ v : E, ‖φ v‖ ≤ C * ‖v‖) (b z : E) (hsolve : A z = b) (m : ℕ)
    (hvan : ∀ v ∈ subspace A b m, φ v = 0) :
    ‖φ z‖ ≤ 2 * C / lo * ((Real.sqrt (hi / lo) - 1) / (Real.sqrt (hi / lo) + 1)) ^ m *
      ‖b‖ := by
  obtain ⟨x, hx⟩ := exists_isMinResidualIterate A b 0 m
  have hxmem : x ∈ subspace A b m := by simpa only [map_zero, sub_zero] using hx.mem
  have hres := hx.norm_residual_le hlo hle hA
  rw [map_zero, sub_zero] at hres
  have herr := hA.isCoerciveWith.norm_le_norm_apply (z - x)
  rw [map_sub, hsolve] at herr
  have hcoord : ‖φ z‖ ≤ C * ‖z - x‖ := by
    simpa only [map_sub, hvan x hxmem, sub_zero] using hφ (z - x)
  have hout : lo * ‖φ z‖ ≤ C * (2 * ((Real.sqrt (hi / lo) - 1) / (Real.sqrt (hi / lo) + 1))
    ^ m * ‖b‖) := by
    calc _ ≤ lo * (C * ‖z - x‖) := mul_le_mul_of_nonneg_left hcoord hlo.le
      _ = C * (lo * ‖z - x‖) := by ring
      _ ≤ C * ‖b - A x‖ := mul_le_mul_of_nonneg_left herr hC
      _ ≤ _ := mul_le_mul_of_nonneg_left hres hC
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (le_div_iff₀ hlo).mpr
  convert hout using 1 <;> ring

end Krylov
