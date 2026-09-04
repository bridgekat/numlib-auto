import Numlib.LinearSolve.Projection.Basic
import Numlib.InnerProductSpace.Energy

/-!
# Optimality properties of projection methods

* Saad Prop 5.2 / Hestenes–Stiefel Thm 4:3: for symmetric coercive `A`, Galerkin iterates are
  exactly the minimizers of the energy norm of the error over `x₀ + K`.
* Saad Prop 5.5: the Galerkin error is the `A`-orthogonal projection of `d₀ = x* - x₀`.
* Nested subspaces give monotone residual / error norms.
* Fong–Saunders §2.1: the Galerkin iterate minimizes the quadratic `½⟪A x, x⟫ - re⟪b, x⟫`.
-/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {A : E →ₗ[𝕜] E} {b x₀ : E} {K : Submodule 𝕜 E} {x xstar : E}

namespace IsGalerkin

/-- Saad Prop 5.2 (⇒): Galerkin iterates minimize the energy norm of the error. -/
theorem energyNorm_le (hA : A.IsSymmetricCoercive) (hx : IsGalerkin A b x₀ K x)
    (hstar : A xstar = b) {y : E} (hy : y - x₀ ∈ K) :
    energyNorm A (xstar - x) ≤ energyNorm A (xstar - y) := by
  sorry

/-- Saad Prop 5.2 (⇔), finite-dimensional `K`. -/
theorem iff_energyNorm_min (hA : A.IsSymmetricCoercive) (hstar : A xstar = b)
    [FiniteDimensional 𝕜 K] :
    IsGalerkin A b x₀ K x ↔
      x - x₀ ∈ K ∧ ∀ y, y - x₀ ∈ K → energyNorm A (xstar - x) ≤ energyNorm A (xstar - y) := by
  sorry

/-- Galerkin error is energy-orthogonal to `K`. -/
theorem energyInner_error_eq_zero (hA : A.IsSymmetricCoercive) (hx : IsGalerkin A b x₀ K x)
    (hstar : A xstar = b) {z : E} (hz : z ∈ K) : energyInner A (xstar - x) z = 0 := by
  sorry

/-- Pythagoras in the energy norm: `‖x* - y‖_A² = ‖x* - x‖_A² + ‖x - y‖_A²` for `y ∈ x₀ + K`. -/
theorem energyNorm_sq_add (hA : A.IsSymmetricCoercive) (hx : IsGalerkin A b x₀ K x)
    (hstar : A xstar = b) {y : E} (hy : y - x₀ ∈ K) :
    energyNorm A (xstar - y) ^ 2 = energyNorm A (xstar - x) ^ 2 + energyNorm A (x - y) ^ 2 := by
  sorry

/-- Nested subspaces: energy-norm errors are nonincreasing. -/
theorem energyNorm_le_of_le (hA : A.IsSymmetricCoercive) {K' : Submodule 𝕜 E} {x' : E}
    (hx : IsGalerkin A b x₀ K x) (hx' : IsGalerkin A b x₀ K' x') (hKK' : K ≤ K')
    (hstar : A xstar = b) : energyNorm A (xstar - x') ≤ energyNorm A (xstar - x) := by
  sorry

/-- Fong–Saunders (2.1): the Galerkin iterate minimizes `φ(x) = ½ re⟪A x, x⟫ - re⟪b, x⟫`
over `x₀ + K`. -/
theorem quadratic_le (hA : A.IsSymmetricCoercive) (hx : IsGalerkin A b x₀ K x) {y : E}
    (hy : y - x₀ ∈ K) :
    RCLike.re (inner 𝕜 (A x) x) / 2 - RCLike.re (inner 𝕜 b x) ≤
      RCLike.re (inner 𝕜 (A y) y) / 2 - RCLike.re (inner 𝕜 b y) := by
  sorry

/-- Saad Prop 5.5: the Galerkin error is the energy-orthogonal projection of `d₀ = x* - x₀`
onto the energy-orthogonal complement of `K`. -/
theorem error_eq_starProjection (hA : A.IsSymmetricCoercive) (hx : IsGalerkin A b x₀ K x)
    (hstar : A xstar = b) [FiniteDimensional 𝕜 K] :
    WithEnergy.equiv A hA (xstar - x) =
      (WithEnergy.submoduleMap A hA K)ᗮ.starProjection (WithEnergy.equiv A hA (xstar - x₀)) := by
  sorry

end IsGalerkin

namespace IsMinError

/-- Minimal-error iterates on nested subspaces have nonincreasing error. -/
theorem norm_error_le_of_le {K' : Submodule 𝕜 E} {x' : E} (hx : IsMinError xstar x₀ K x)
    (hx' : IsMinError xstar x₀ K' x') (hKK' : K ≤ K') : ‖xstar - x'‖ ≤ ‖xstar - x‖ := by
  sorry

/-- The minimal-error iterate is the orthogonal projection of `x*` onto `x₀ + K`. -/
theorem eq_starProjection [K.HasOrthogonalProjection] (hx : IsMinError xstar x₀ K x) :
    x - x₀ = K.starProjection (xstar - x₀) := by
  sorry

theorem unique {x' : E} (hx : IsMinError xstar x₀ K x) (hx' : IsMinError xstar x₀ K x') :
    x = x' := by
  sorry

/-- The error is orthogonal to `K`. -/
theorem sub_mem_orthogonal (hx : IsMinError xstar x₀ K x) : xstar - x ∈ Kᗮ := by
  sorry

/-- Saad §8.3 / Choi: minimal error over `x₀ + A† K` is Petrov–Galerkin with `L = K`
(CGNE / Craig's method as a Petrov–Galerkin method). -/
theorem isPetrovGalerkin_of_map_adjoint [FiniteDimensional 𝕜 E] {L : Submodule 𝕜 E}
    (hK : K = L.map (LinearMap.adjoint A)) (hstar : A xstar = b) (hx : IsMinError xstar x₀ K x) :
    IsPetrovGalerkin A b x₀ K L x := by
  sorry

end IsMinError

/-- Existence and characterization: `x₀ + P_K (x* - x₀)` is the minimal-error point. -/
theorem isMinError_add_starProjection [K.HasOrthogonalProjection] (xstar x₀ : E) :
    IsMinError xstar x₀ K (x₀ + K.starProjection (xstar - x₀)) := by
  sorry
