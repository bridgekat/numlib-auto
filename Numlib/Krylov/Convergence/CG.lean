import Numlib.Krylov.Iterate
import Numlib.Krylov.Convergence.Polynomial
import Numlib.Polynomial.ChebyshevMinimax
import Numlib.LinearSolve.Projection.OneDimensional

/-!
# Chebyshev convergence bounds for Galerkin (CG) and minimal-residual iterates

For symmetric `A` with `λmin ‖x‖² ≤ re ⟪A x, x⟫ ≤ λmax ‖x‖²` (`LinearMap.IsSymmetricBoundedBy`,
in any inner product space: the proofs go through the compression of `A` to `𝒦_{m+1}`) and *any*
sequence of Galerkin iterates (CG, D-Lanczos, …):
`‖x* - x_m‖_A ≤ ‖x* - x₀‖_A / T_m((λmax + λmin)/(λmax - λmin)) ≤ 2 ((√κ-1)/(√κ+1))^m ‖x* - x₀‖_A`
(Saad Thm 6.29, (6.123)–(6.128); Atkinson–Han Thm 5.6.1; Meurant (3.9)). The minimal-residual
analogue for the residual norm, and Saad Thm 6.30 (restarted minimal-residual iterations converge
for coercive `A`).
-/

open Polynomial Polynomial.Chebyshev Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {A : E →ₗ[𝕜] E} {b x₀ : E}

namespace Krylov

section Symmetric

variable {lmin lmax : ℝ} (hl : 0 < lmin) (hll : lmin < lmax) (hA : A.IsSymmetricBoundedBy lmin lmax)
include hl hll hA

/-- Sharp Chebyshev form (Saad (6.123)):
`‖x* - x_m‖_A ≤ ‖x* - x₀‖_A / T_m((λmax+λmin)/(λmax-λmin))`. -/
theorem IsGalerkinIterate.energyNorm_error_le_div_eval_T {m : ℕ} {x xstar : E}
    (hx : IsGalerkinIterate A b x₀ m x) (hstar : A xstar = b) :
    energyNorm A (xstar - x) ≤
      energyNorm A (xstar - x₀) / (T ℝ m).eval ((lmax + lmin) / (lmax - lmin)) := by
  sorry

/-- Saad Thm 6.29 / Atkinson–Han (5.6.5): with `κ = λmax / λmin`,
`‖x* - x_m‖_A ≤ 2 ((√κ - 1)/(√κ + 1))^m ‖x* - x₀‖_A`. -/
theorem IsGalerkinIterate.energyNorm_error_le {m : ℕ} {x xstar : E}
    (hx : IsGalerkinIterate A b x₀ m x) (hstar : A xstar = b) :
    energyNorm A (xstar - x) ≤
      2 * ((Real.sqrt (lmax / lmin) - 1) / (Real.sqrt (lmax / lmin) + 1)) ^ m *
        energyNorm A (xstar - x₀) := by
  sorry

/-- Minimal-residual iterates on symmetric coercive systems: the same Chebyshev bound for the
residual norm. -/
theorem IsMinResIterate.norm_residual_le {m : ℕ} {x : E} (hx : IsMinResIterate A b x₀ m x) :
    ‖b - A x‖ ≤
      2 * ((Real.sqrt (lmax / lmin) - 1) / (Real.sqrt (lmax / lmin) + 1)) ^ m * ‖b - A x₀‖ := by
  sorry

end Symmetric

/-- One-step comparison (Atkinson–Han (5.6.6)): `(√κ - 1)/(√κ + 1) ≤ (κ - 1)/(κ + 1)`. -/
theorem sqrt_ratio_le_ratio {κ : ℝ} (hκ : 1 ≤ κ) :
    (Real.sqrt κ - 1) / (Real.sqrt κ + 1) ≤ (κ - 1) / (κ + 1) := by
  sorry

/-- Saad Thm 6.30: for a bounded coercive `A`, restarted minimal-residual iterations (each cycle
a minimal-residual iterate over `𝒦_m`, `m ≥ 1`) converge: each cycle contracts the residual by
at least `√(1 - c²/‖A‖²)`. -/
theorem IsMinResIterate.norm_residual_le_of_isCoerciveWith {A : E →L[𝕜] E} {c : ℝ} (hc : 0 < c)
    (hA : (A : E →ₗ[𝕜] E).IsCoerciveWith c) {b x₀ x : E} {m : ℕ} (hm : 1 ≤ m)
    (hx : IsMinResIterate (A : E →ₗ[𝕜] E) b x₀ m x) :
    ‖b - A x‖ ≤ Real.sqrt (1 - c ^ 2 / ‖A‖ ^ 2) * ‖b - A x₀‖ := by
  sorry

theorem restarted_minRes_tendsto {A : E →L[𝕜] E} {c : ℝ} (hc : 0 < c)
    (hA : (A : E →ₗ[𝕜] E).IsCoerciveWith c) {b : E} {m : ℕ} (hm : 1 ≤ m) (x : ℕ → E)
    (hx : ∀ k, IsMinResIterate (A : E →ₗ[𝕜] E) b (x k) m (x (k + 1))) :
    Filter.Tendsto (fun k => ‖b - A (x k)‖) Filter.atTop (nhds 0) := by
  sorry

end Krylov
