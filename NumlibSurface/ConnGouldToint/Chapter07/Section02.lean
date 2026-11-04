/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Subproblem.TrustRegion

/-!
# Characterization of the Euclidean model minimizer

Section 7.2 of [conn2000trust].
-/

namespace ConnGouldToint.Chapter07

open Metric
open Subproblem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quadratic objective of the Euclidean trust-region subproblem (7.2.1). -/
noncomputable abbrev q (g : E) (H : E →L[ℝ] E) : E → ℝ := quadModel g H

/-- Theorem 7.2.1. A global minimizer on the Euclidean sphere solves a shifted
system with a positive semidefinite Hessian. Coercivity of the shifted Hessian,
equivalent to positive definiteness in finite dimension, implies uniqueness.

A positive radius is required for the stationary system when the gradient is nonzero. -/
theorem theorem_7_2_1 {g : E} {H : E →L[ℝ] E} {Δ : ℝ} {s : E}
    (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hΔ : 0 < Δ)
    (hs : ‖s‖ = Δ) (hmin : IsMinOn (q g H) (sphere 0 Δ) s) :
    ∃ μ : ℝ, (H + μ • (1 : E →L[ℝ] E)) s = -g ∧
      ((H + μ • (1 : E →L[ℝ] E) : E →L[ℝ] E) : E →ₗ[ℝ] E).IsPositive ∧
      (((H + μ • (1 : E →L[ℝ] E) : E →L[ℝ] E) : E →ₗ[ℝ] E).IsCoercive →
        ∀ u : E, ‖u‖ = Δ → IsMinOn (q g H) (sphere 0 Δ) u → u = s) :=
  exists_shift_of_isMinOn_sphere hH hΔ hs hmin

/-- Corollary 7.2.2. A global minimizer on the closed ball satisfies the shifted system with
a nonnegative complementary multiplier and positive semidefinite shifted Hessian.
Coercivity of the shifted Hessian implies uniqueness.

The radius must be positive. At radius zero, the unique feasible point is zero, and the
shifted system has no solution for a nonzero gradient. -/
theorem corollary_7_2_2 {g : E} {H : E →L[ℝ] E} {Δ : ℝ} {s : E}
    (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hΔ : 0 < Δ)
    (hs : ‖s‖ ≤ Δ) (hmin : IsMinOn (q g H) (closedBall 0 Δ) s) :
    ∃ μ, IsTrustRegionMultiplier g H Δ s μ ∧
      (((H + μ • (1 : E →L[ℝ] E) : E →L[ℝ] E) : E →ₗ[ℝ] E).IsCoercive →
        ∀ u : E, ‖u‖ ≤ Δ → IsMinOn (q g H) (closedBall 0 Δ) u → u = s) := by
  obtain ⟨μ, hμ⟩ := (isMinOn_closedBall_iff hH hΔ hs).mp hmin
  exact ⟨μ, hμ, fun hc _ hu hmin' => eq_of_isMinOn_closedBall_of_posDef hH hμ hs hc hu hmin'⟩

end ConnGouldToint.Chapter07
