import Numlib.Optimization.SecularResolvent
import Numlib.Optimization.WeightedQuadraticSubproblem

/-!
# Resolvents in a positive definite metric

The actual inverse of `H + t M` is transported to the self-adjoint resolvent in the energy
inner product. In particular the spectral formula, Taylor estimates, and secular root theorem
apply to arbitrary positive definite metrics, without assuming a diagonalization as extra data.
-/

open scoped InnerProductSpace Topology
open Set Filter
open Optimization.QuadraticSubproblem

namespace Optimization.SecularResolvent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {M Minv : E →ₗ[ℝ] E}

/-- Squared metric norm of the actual inverse of the metric-shifted operator. -/
noncomputable def weightedNormSqResolvent (H M : E →ₗ[ℝ] E) (g : E) (t : ℝ) : ℝ :=
  energyNorm M (Ring.inverse (H + t • M) g) ^ 2

variable (hM : Krylov.IsPreconditioner M Minv) (H : E →L[ℝ] E)

/-- Applying the shifted energy operator amounts to preconditioning the shifted equation. -/
theorem energy_shift_apply (t : ℝ) (x : E) :
    ((energyHessian hM H).toLinearMap + t • (1 : hM.EnergySpace →ₗ[ℝ] hM.EnergySpace))
      (hM.toEnergy x) = hM.toEnergy (Minv ((H.toLinearMap + t • M) x)) := by
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    ContinuousLinearMap.coe_coe, energyHessian_apply, map_add, map_smul, hM.inv_apply]

/-- Invertibility of the energy shift implies invertibility of the original metric shift. -/
theorem isUnit_metric_shift {t : ℝ}
    (ht : IsUnit ((energyHessian hM H).toLinearMap +
      t • (1 : hM.EnergySpace →ₗ[ℝ] hM.EnergySpace))) :
    IsUnit (H.toLinearMap + t • M) := by
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have he : ((energyHessian hM H).toLinearMap +
      t • (1 : hM.EnergySpace →ₗ[ℝ] hM.EnergySpace)) (hM.toEnergy x) = 0 := by
    rw [energy_shift_apply, hx, map_zero, map_zero]
  have hh := (LinearMap.ker_eq_bot'.mp ((LinearMap.isUnit_iff_ker_eq_bot _).mp ht)) _ he
  exact hM.toEnergy.injective (by simpa using hh)

/-- The inverse in energy coordinates is the actual inverse of the original metric shift. -/
theorem inverse_energy_shift (g : E) {t : ℝ}
    (ht : IsUnit ((energyHessian hM H).toLinearMap +
      t • (1 : hM.EnergySpace →ₗ[ℝ] hM.EnergySpace))) :
    Ring.inverse ((energyHessian hM H).toLinearMap +
      t • (1 : hM.EnergySpace →ₗ[ℝ] hM.EnergySpace)) (hM.toEnergy (Minv g)) =
      hM.toEnergy (Ring.inverse (H.toLinearMap + t • M) g) := by
  let A := (energyHessian hM H).toLinearMap +
    t • (1 : hM.EnergySpace →ₗ[ℝ] hM.EnergySpace)
  have hA : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot]
    exact (LinearMap.isUnit_iff_ker_eq_bot _).mp ht
  apply hA
  have hleft := congrArg (fun B : hM.EnergySpace →ₗ[ℝ] hM.EnergySpace =>
    B (hM.toEnergy (Minv g))) (Ring.mul_inverse_cancel A ht)
  have hright := congrArg (fun B : E →ₗ[ℝ] E => B g)
    (Ring.mul_inverse_cancel (H.toLinearMap + t • M) (isUnit_metric_shift hM H ht))
  change A (Ring.inverse A (hM.toEnergy (Minv g))) = _
  rw [show A (Ring.inverse A (hM.toEnergy (Minv g))) = hM.toEnergy (Minv g) from hleft]
  symm
  change ((energyHessian hM H).toLinearMap + t • 1)
    (hM.toEnergy (Ring.inverse (H.toLinearMap + t • M) g)) = _
  rw [energy_shift_apply, show (H.toLinearMap + t • M)
    (Ring.inverse (H.toLinearMap + t • M) g) = g from hright]

/-- Equality of the genuine metric resolvent norm and its self-adjoint energy-space version. -/
theorem weightedNormSqResolvent_eq (g : E) {t : ℝ}
    (ht : IsUnit ((energyHessian hM H).toLinearMap +
      t • (1 : hM.EnergySpace →ₗ[ℝ] hM.EnergySpace))) :
    weightedNormSqResolvent H.toLinearMap M g t =
      normSqResolvent (energyHessian hM H).toLinearMap (hM.toEnergy (Minv g)) t := by
  rw [normSqResolvent, inverse_energy_shift hM H g ht]
  simp only [weightedNormSqResolvent, WithEnergy.norm_equiv]

omit [FiniteDimensional ℝ E] in
/-- A nonzero original right-hand side remains nonzero after metric transport. -/
theorem toEnergy_inv_ne_zero {g : E} (hg : g ≠ 0) : hM.toEnergy (Minv g) ≠ 0 := by
  intro h
  have hh : Minv g = 0 := hM.toEnergy.injective (by simpa using h)
  have := congrArg M hh
  rw [hM.apply_inv, map_zero] at this
  exact hg this

variable (hH : H.IsSymmetric)

include hH in
/-- The preconditioned Hessian is self-adjoint in the metric space. -/
theorem energyHessian_isSymmetric : (energyHessian hM H).toLinearMap.IsSymmetric :=
  isSymmetric_energyHessian hM hH

/-- Equality with the energy resolvent holds near any nonsingular shift. -/
theorem eventuallyEq_weightedNormSqResolvent (g : E) {t : ℝ}
    (ht : ∀ i, t + (energyHessian_isSymmetric hM H hH).eigenvalues rfl i ≠ 0) :
    weightedNormSqResolvent H.toLinearMap M g =ᶠ[𝓝 t]
      normSqResolvent (energyHessian hM H).toLinearMap (hM.toEnergy (Minv g)) := by
  have he : ∀ᶠ x in 𝓝 t, ∀ i,
      x + (energyHessian_isSymmetric hM H hH).eigenvalues rfl i ≠ 0 := by
    rw [eventually_all]
    intro i
    exact (continuousAt_id.add continuousAt_const).eventually_ne (ht i)
  filter_upwards [he] with x hx
  exact weightedNormSqResolvent_eq hM H g
    (isUnit_shift (energyHessian_isSymmetric hM H hH) x hx)

/-- Taylor polynomials for the metric resolvent, using its actual derivatives. -/
noncomputable def weightedTaylorApprox (g : E) (k : ℕ) (c x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1),
    iteratedDeriv j (weightedNormSqResolvent H.toLinearMap M g) c * (x - c) ^ j /
      j.factorial

/-- Transport preserves the entire Taylor polynomial at every regular center. -/
theorem weightedTaylorApprox_eq (g : E) (k : ℕ) {c : ℝ} (x : ℝ)
    (hc : ∀ i, c + (energyHessian_isSymmetric hM H hH).eigenvalues rfl i ≠ 0) :
    weightedTaylorApprox (M := M) H g k c x =
      taylorApprox (energyHessian hM H).toLinearMap (hM.toEnergy (Minv g)) k c x := by
  rw [weightedTaylorApprox, taylorApprox_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [(eventuallyEq_weightedNormSqResolvent hM H hH g hc).iteratedDeriv_eq j]

end Optimization.SecularResolvent
