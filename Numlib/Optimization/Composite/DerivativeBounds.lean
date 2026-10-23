import Numlib.Optimization.Composite.Regularization
import Numlib.Optimization.Composite.TaylorDecrease
import Numlib.Optimization.Regularization.ModelSharp
import Numlib.Analysis.Calculus.ContDiff.Lipschitz

/-!
# Actual residual tensor bounds from componentwise Lipschitz derivatives

Bounds on the preceding positive derivative give uniform higher tensor norms.
Scalar coordinate projections commute with actual iterated derivatives, and
Euclidean norm comparison gives the exact square-root dimension factor.
-/

namespace Composite
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A Lipschitz bound for the preceding positive derivative bounds each higher tensor. -/
theorem norm_iteratedFDeriv_le_of_lipschitz_lower {f : E → F} {p : ℕ} {L : ℝ}
    (hL : 0 ≤ L)
    (hlip : ∀ a, 1 ≤ a → a < p → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    {a : ℕ} (ha : 2 ≤ a) (hap : a ≤ p) (x : E) :
    ‖iteratedFDeriv ℝ a f x‖ ≤ L := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
  rw [← norm_fderiv_iteratedFDeriv]
  exact norm_fderiv_le_of_lip' ℝ hL
    (Filter.Eventually.of_forall (fun u => hlip b (by omega) (by omega) u x))

/-- Coordinate tensor bounds give the exact square-root dimension operator bound. -/
theorem norm_multilinear_le_sqrt_dim_mul {m a : ℕ}
    (A : E [×a]→L[ℝ] EuclideanSpace ℝ (Fin m)) {B : ℝ} (hB : 0 ≤ B)
    (hA : ∀ i, ‖(EuclideanSpace.proj (𝕜 := ℝ) i).compContinuousMultilinearMap A‖ ≤ B) :
    ‖A‖ ≤ Real.sqrt m * B := by
  apply A.opNorm_le_bound (by positivity)
  intro v
  have hcoord (i : Fin m) : |A v i| ≤ B * ∏ j, ‖v j‖ := by
    exact (((EuclideanSpace.proj (𝕜 := ℝ) i).compContinuousMultilinearMap A).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hA i) (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
  have hn := norm_le_sqrt_dim_mul (mul_nonneg hB (Finset.prod_nonneg
    (fun _ _ => norm_nonneg _))) hcoord
  nlinarith only [hn]

/-- Componentwise lower-derivative Lipschitz bounds control the actual residual jet. -/
theorem norm_iteratedFDeriv_le_componentwise {m p : ℕ}
    {c : E → EuclideanSpace ℝ (Fin m)} (hc : ContDiff ℝ p c) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ i a, 1 ≤ a → a < p → ∀ u v,
      ‖iteratedFDeriv ℝ a (fun z => c z i) u -
        iteratedFDeriv ℝ a (fun z => c z i) v‖ ≤ L * ‖u - v‖)
    {a : ℕ} (ha : 2 ≤ a) (hap : a ≤ p) (x : E) :
    ‖iteratedFDeriv ℝ a c x‖ ≤ Real.sqrt m * L := by
  apply norm_multilinear_le_sqrt_dim_mul _ hL
  intro i
  have he := (EuclideanSpace.proj (𝕜 := ℝ) i).iteratedFDeriv_comp_left
    (x := x) (hc.of_le (by exact_mod_cast hap)).contDiffAt le_rfl
  rw [← he]
  exact norm_iteratedFDeriv_le_of_lipschitz_lower hL (hlip i) ha hap x
end Composite
