import Numlib.Optimization.SecularResolvent
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Scaled resolvent limits

The squared resolvent decays quadratically with the shift. Its leading coefficient is the
squared norm of the right-hand side, derived from the finite spectral representation.
-/

noncomputable section
namespace Optimization.SecularResolvent
open Filter Topology

/-- A fixed additive shift does not change the leading linear behavior at positive infinity. -/
theorem tendsto_div_add_atTop (a : ℝ) :
    Tendsto (fun t : ℝ => t / (t + a)) atTop (𝓝 1) := by
  have h : Tendsto (fun t : ℝ => 1 - a / (t + a)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub
    ((tendsto_atTop_add_const_right atTop a tendsto_id).const_div_atTop a)
  have he : (fun t : ℝ => t / (t + a)) =ᶠ[atTop] (fun t => 1 - a / (t + a)) := by
    filter_upwards [eventually_gt_atTop (-a)] with t ht
    have hn : t + a ≠ 0 := by linarith
    field_simp
    ring
  apply Tendsto.congr' he.symm
  simpa using h

/-- The finite spectral squared resolvent has its expected leading coefficient. -/
theorem tendsto_mul_sq_spectralNormSq {ι : Type*} [Fintype ι] (e γ : ι → ℝ) :
    Tendsto (fun t : ℝ => t ^ 2 * spectralNormSq e γ t) atTop
      (𝓝 (∑ i, γ i ^ 2)) := by
  have h := tendsto_finsetSum Finset.univ (fun i _ =>
    ((tendsto_div_add_atTop (e i)).pow 2).const_mul (γ i ^ 2))
  convert h using 1
  · funext t
    simp only [spectralNormSq, Finset.mul_sum, div_pow]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · simp

section Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : E →ₗ[ℝ] E}

/-- The actual squared resolvent has the squared right-hand-side norm as leading coefficient. -/
theorem tendsto_mul_sq_normSqResolvent (hH : H.IsSymmetric) (g : E) :
    Tendsto (fun t : ℝ => t ^ 2 * normSqResolvent H g t) atTop (𝓝 (‖g‖ ^ 2)) := by
  have he : (fun t : ℝ => t ^ 2 * normSqResolvent H g t) =ᶠ[atTop]
      (fun t => t ^ 2 * spectralNormSq (hH.eigenvalues rfl)
        (fun i => (hH.eigenvectorBasis rfl).repr g i) t) := by
    have hreg : ∀ᶠ t : ℝ in atTop, ∀ i, t + hH.eigenvalues rfl i ≠ 0 := by
      rw [Filter.eventually_all]
      intro i
      filter_upwards [eventually_gt_atTop (-hH.eigenvalues rfl i)] with t ht
      exact ne_of_gt (by linarith)
    filter_upwards [hreg] with t ht
    rw [normSqResolvent_eq_spectralNormSq hH g t ht]
  have hn : (∑ i, ((hH.eigenvectorBasis rfl).repr g i) ^ 2) = ‖g‖ ^ 2 := by
    rw [← EuclideanSpace.real_norm_sq_eq, (hH.eigenvectorBasis rfl).repr.norm_map]
  apply Tendsto.congr' he.symm
  simpa only [hn] using tendsto_mul_sq_spectralNormSq
    (hH.eigenvalues rfl) (fun i => (hH.eigenvectorBasis rfl).repr g i)

/-- The norm of the actual resolvent has the right-hand-side norm as leading coefficient. -/
theorem tendsto_mul_norm_inverse_shift (hH : H.IsSymmetric) (g : E) :
    Tendsto (fun t : ℝ => t * ‖Ring.inverse (H + t • (1 : E →ₗ[ℝ] E)) g‖)
      atTop (𝓝 ‖g‖) := by
  have hs := (tendsto_mul_sq_normSqResolvent hH g).sqrt
  rw [Real.sqrt_sq (norm_nonneg g)] at hs
  apply Tendsto.congr' _ hs
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [normSqResolvent, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq ht.le, Real.sqrt_sq (norm_nonneg _)]

end Operator
end Optimization.SecularResolvent
