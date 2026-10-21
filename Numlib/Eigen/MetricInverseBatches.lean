import Numlib.Eigen.ShiftedInverseBatches
import Numlib.Optimization.WeightedSecularResolvent

/-!
# Inverse iteration in an energy metric

Energy coordinates transport normalized shifted inverse batches to the actual original
system `(H + t M) w = M v`. Normalization uses the metric norm, and the Rayleigh numerator
is the original Hessian quadratic form. No factorization or eigenbasis is supplied as data.
-/

noncomputable section
open scoped InnerProductSpace
open Optimization.QuadraticSubproblem Optimization.SecularResolvent
namespace Krylov
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {M Minv : E →ₗ[ℝ] E}
variable (hM : IsPreconditioner M Minv) (H : E →L[ℝ] E)

/-- An actual normalized inverse batch transported from the energy coordinates. -/
noncomputable def metricInverseBatch (t : ℝ) (x : E) (m : ℕ) : E :=
  hM.toEnergy.symm (shiftedInverseBatch (energyHessian hM H).toLinearMap t
    (hM.toEnergy x) m)

/-- The metric batch is exactly the usual inverse batch in energy coordinates. -/
@[simp] theorem toEnergy_metricInverseBatch (t : ℝ) (x : E) (m : ℕ) :
    hM.toEnergy (metricInverseBatch hM H t x m) =
      shiftedInverseBatch (energyHessian hM H).toLinearMap t (hM.toEnergy x) m := by
  exact hM.toEnergy.apply_symm_apply _

/-- The original metric norm equals the ordinary norm in energy coordinates. -/
theorem energyNorm_metricInverseBatch (t : ℝ) (x : E) (m : ℕ) :
    energyNorm M (metricInverseBatch hM H t x m) =
      ‖shiftedInverseBatch (energyHessian hM H).toLinearMap t (hM.toEnergy x) m‖ := by
  rw [← toEnergy_metricInverseBatch hM H]
  rfl

/-- A batch initially normalizes by the metric norm. -/
@[simp] theorem metricInverseBatch_zero (t : ℝ) (x : E) :
    metricInverseBatch hM H t x 0 = (energyNorm M x)⁻¹ • x := by
  apply hM.toEnergy.injective
  rw [toEnergy_metricInverseBatch, shiftedInverseBatch_zero, map_smul]
  rfl

/-- One inner step is the actual metric-shifted solve followed by metric normalization. -/
theorem metricInverseBatch_succ (t : ℝ) (x : E) (m : ℕ)
    (ht : IsUnit ((energyHessian hM H).toLinearMap + t • 1)) :
    metricInverseBatch hM H t x (m + 1) =
      let w := Ring.inverse (H.toLinearMap + t • M) (M (metricInverseBatch hM H t x m))
      (energyNorm M w)⁻¹ • w := by
  apply hM.toEnergy.injective
  rw [toEnergy_metricInverseBatch, shiftedInverseBatch_succ]
  have he := inverse_energy_shift hM H (M (metricInverseBatch hM H t x m)) ht
  rw [hM.inv_apply, toEnergy_metricInverseBatch] at he
  rw [he, map_smul]
  rfl

/-- Nonsingular metric batches with nonzero inputs are metric-unit vectors. -/
theorem energyNorm_metricInverseBatch_eq_one {t : ℝ}
    (ht : IsUnit ((energyHessian hM H).toLinearMap + t • 1))
    {x : E} (hx : x ≠ 0) (m : ℕ) :
    energyNorm M (metricInverseBatch hM H t x m) = 1 := by
  rw [energyNorm_metricInverseBatch]
  apply norm_shiftedInverseBatch ht
  exact fun hz => hx (hM.toEnergy.injective (hz.trans (map_zero _).symm))

/-- The energy Rayleigh numerator is the actual original Hessian quadratic form. -/
theorem inner_energyHessian_toEnergy (x : E) :
    inner ℝ (hM.toEnergy x) (energyHessian hM H (hM.toEnergy x)) =
      inner ℝ x (H x) := by
  rw [energyHessian_apply, hM.inner_toEnergy_inv]

end Krylov
