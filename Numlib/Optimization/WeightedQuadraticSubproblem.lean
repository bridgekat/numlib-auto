import Numlib.Optimization.QuadraticSubproblem
import Numlib.Krylov.Preconditioned

/-!
# Quadratic subproblems in an SPD metric

An invertible symmetric coercive operator equips the original vector space with its energy
inner product. Preconditioning both coefficients transports the original quadratic objective
unchanged. Consequently the global optimality characterizations apply to arbitrary SPD metrics.
Positive definite matrices supply this structure through their actual matrix inverse.
-/

open scoped InnerProductSpace
open Set Metric

namespace Optimization.QuadraticSubproblem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {M Minv : E →ₗ[ℝ] E}

/-- The power-regularized quadratic in the norm induced by `M`. -/
noncomputable def weightedPowerQuadratic (g : E) (H : E →L[ℝ] E)
    (M : E →ₗ[ℝ] E) (sigma r : ℝ) (s : E) : ℝ :=
  quadratic g H s + sigma / r * energyNorm M s ^ r

variable (hM : Krylov.IsPreconditioner M Minv)

/-- The preconditioned Hessian acting on the energy inner product space. -/
noncomputable def energyHessian (H : E →L[ℝ] E) : hM.EnergySpace →L[ℝ] hM.EnergySpace :=
  (hM.energyEnd (Minv ∘ₗ H.toLinearMap)).toContinuousLinearMap

/-- The energy Hessian applies the original Hessian followed by the inverse metric. -/
@[simp] theorem energyHessian_apply (H : E →L[ℝ] E) (s : E) :
    energyHessian hM H (hM.toEnergy s) = hM.toEnergy (Minv (H s)) := rfl

/-- Eigenvectors in the metric inner product correspond to generalized eigenvectors of the
original operator pair. -/
theorem energy_eigenvector_iff (H : E →L[ℝ] E) (x : E) (mu : ℝ) :
    energyHessian hM H (hM.toEnergy x) = mu • hM.toEnergy x ↔ H x = mu • M x := by
  rw [energyHessian_apply, ← map_smul, hM.toEnergy.injective.eq_iff]
  constructor
  · intro h
    have hh := congrArg M h
    simpa only [hM.apply_inv, map_smul] using hh
  · intro h
    have hh := congrArg Minv h
    simpa only [map_smul, hM.inv_apply] using hh

/-- Preconditioning the coefficients preserves every value of the quadratic objective. -/
@[simp] theorem quadratic_energy (g : E) (H : E →L[ℝ] E) (s : E) :
    quadratic (hM.toEnergy (Minv g)) (energyHessian hM H) (hM.toEnergy s) =
      quadratic g H s := by
  simp only [quadratic, energyHessian_apply]
  have hg := hM.inner_toEnergy_inv s g
  rw [real_inner_comm] at hg
  rw [hg, hM.inner_toEnergy_inv, real_inner_comm s g]

/-- The preconditioned Hessian is symmetric in the energy inner product. -/
theorem isSymmetric_energyHessian {H : E →L[ℝ] E} (hH : H.IsSymmetric) :
    (energyHessian hM H).IsSymmetric := by
  intro x y
  obtain ⟨x, rfl⟩ := hM.toEnergy.surjective x
  obtain ⟨y, rfl⟩ := hM.toEnergy.surjective y
  change inner ℝ (hM.energyEnd (Minv ∘ₗ H.toLinearMap) (hM.toEnergy x))
    (hM.toEnergy y) = inner ℝ (hM.toEnergy x)
      (hM.energyEnd (Minv ∘ₗ H.toLinearMap) (hM.toEnergy y))
  rw [hM.inner_energyEnd_left, hM.inner_energyEnd_right]
  exact hH x y

/-- The weighted regularization also transports without changing its values. -/
@[simp] theorem powerRegularized_energy (g : E) (H : E →L[ℝ] E) (sigma r : ℝ) (s : E) :
    powerRegularizedQuadratic (hM.toEnergy (Minv g)) (energyHessian hM H)
      sigma r (hM.toEnergy s) = weightedPowerQuadratic g H M sigma r s := by
  simp [powerRegularizedQuadratic, weightedPowerQuadratic, WithEnergy.norm_equiv]

/-- Shifted stationarity in the energy space is the original `M`-shifted system. -/
theorem energy_stationary_iff (g : E) (H : E →L[ℝ] E) (s : E) (lambda : ℝ) :
    hM.toEnergy (Minv g) + energyHessian hM H (hM.toEnergy s) +
      lambda • hM.toEnergy s = 0 ↔ g + H s + lambda • M s = 0 := by
  rw [energyHessian_apply, ← map_smul, ← map_add, ← map_add,
    LinearEquiv.map_eq_zero_iff]
  constructor
  · intro h
    have hh := congrArg M h
    simpa only [map_add, map_smul, hM.apply_inv, map_zero] using hh
  · intro h
    have hh := congrArg Minv h
    simpa only [map_add, map_smul, hM.inv_apply, map_zero] using hh

/-- The shifted quadratic form in energy coordinates is the original shifted quadratic form. -/
theorem inner_energy_shift (H : E →L[ℝ] E) (lambda : ℝ) (d : E) :
    inner ℝ (hM.toEnergy d)
      ((energyHessian hM H + lambda • ContinuousLinearMap.id ℝ hM.EnergySpace)
        (hM.toEnergy d)) = inner ℝ d ((H.toLinearMap + lambda • M) d) := by
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.id_apply, energyHessian_apply, inner_add_right, inner_smul_right,
    hM.inner_toEnergy_inv, LinearMap.add_apply, LinearMap.smul_apply]
  congr 1
  rw [WithEnergy.inner_equiv, energyInner, hM.isSymmetricCoercive.isSymmetric]

/-- Positive semidefiniteness of the shifted Hessian is preserved by the metric transport. -/
theorem isPositive_energy_shift_iff {H : E →L[ℝ] E} (hH : H.IsSymmetric) (lambda : ℝ) :
    (energyHessian hM H + lambda • ContinuousLinearMap.id ℝ hM.EnergySpace).IsPositive ↔
      (H.toLinearMap + lambda • M).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff, LinearMap.isPositive_iff]
  have hs : (energyHessian hM H + lambda •
      ContinuousLinearMap.id ℝ hM.EnergySpace).IsSymmetric := by
    intro x y
    change inner ℝ (energyHessian hM H x + lambda • x) y =
      inner ℝ x (energyHessian hM H y + lambda • y)
    simp only [
      inner_add_left, inner_add_right, real_inner_smul_left, inner_smul_right]
    exact congrArg (fun t => t + lambda * inner ℝ x y)
      (isSymmetric_energyHessian hM hH x y)
  have ht : (H.toLinearMap + lambda • M).IsSymmetric := by
    intro x y
    simp only [LinearMap.add_apply, LinearMap.smul_apply, inner_add_left, inner_add_right,
      real_inner_smul_left, inner_smul_right]
    rw [hH x y, hM.isSymmetricCoercive.isSymmetric x y]
  constructor
  · rintro ⟨_, hp⟩
    refine ⟨ht, fun x => ?_⟩
    simpa only [inner_energy_shift hM, real_inner_comm] using hp (hM.toEnergy x)
  · rintro ⟨_, hp⟩
    refine ⟨hs, fun x => ?_⟩
    obtain ⟨x, rfl⟩ := hM.toEnergy.surjective x
    simpa only [inner_energy_shift hM, real_inner_comm] using hp x

/-- Global minimization on an energy ball is unchanged by transport. -/
theorem isMinOn_energy_ball_iff (g : E) (H : E →L[ℝ] E) (s : E) (delta : ℝ) :
    IsMinOn (quadratic (hM.toEnergy (Minv g)) (energyHessian hM H))
      (closedBall 0 delta) (hM.toEnergy s) ↔
    IsMinOn (quadratic g H) {x | energyNorm M x ≤ delta} s := by
  constructor
  · intro hm y hy
    have hh := hm (show hM.toEnergy y ∈ closedBall 0 delta by
      simpa only [mem_closedBall_zero_iff, WithEnergy.norm_equiv, mem_ofPred_eq] using hy)
    simpa only [mem_ofPred_eq, quadratic_energy] using hh
  · intro hm y hy
    obtain ⟨y, rfl⟩ := hM.toEnergy.surjective y
    have hh := hm (show y ∈ {x | energyNorm M x ≤ delta} by
      simpa only [mem_closedBall_zero_iff, WithEnergy.norm_equiv, mem_ofPred_eq] using hy)
    simpa only [mem_ofPred_eq, quadratic_energy] using hh

/-- Global weighted power minimization is unchanged by transport. -/
theorem isMinOn_energy_power_iff (g : E) (H : E →L[ℝ] E) (sigma r : ℝ) (s : E) :
    IsMinOn (powerRegularizedQuadratic (hM.toEnergy (Minv g)) (energyHessian hM H)
      sigma r) univ (hM.toEnergy s) ↔
    IsMinOn (weightedPowerQuadratic g H M sigma r) univ s := by
  constructor
  · intro hm y _
    simpa only [mem_ofPred_eq, powerRegularized_energy] using hm (mem_univ (hM.toEnergy y))
  · intro hm y _
    obtain ⟨y, rfl⟩ := hM.toEnergy.surjective y
    simpa only [mem_ofPred_eq, powerRegularized_energy] using hm (mem_univ y)

include hM

/-- Weighted trust-region global optimality, including feasibility and complementarity. -/
theorem isMinOn_energy_ball_iff_shift {g : E} {H : E →L[ℝ] E} (hH : H.IsSymmetric)
    {s : E} {delta : ℝ} (hdelta : 0 < delta) :
    (energyNorm M s ≤ delta ∧ IsMinOn (quadratic g H)
      {x | energyNorm M x ≤ delta} s) ↔
    energyNorm M s ≤ delta ∧ ∃ lambda : ℝ, 0 ≤ lambda ∧
      g + H s + lambda • M s = 0 ∧ (H.toLinearMap + lambda • M).IsPositive ∧
        lambda * (energyNorm M s ^ 2 - delta ^ 2) = 0 := by
  have hh := isMinOn_ball_iff_shift (isSymmetric_energyHessian hM hH)
    (g := hM.toEnergy (Minv g)) (s := hM.toEnergy s) hdelta
  simpa only [WithEnergy.norm_equiv, isMinOn_energy_ball_iff,
    energy_stationary_iff, isPositive_energy_shift_iff hM hH] using hh

/-- Weighted power-regularized global optimality. -/
theorem isMinOn_energy_power_iff_shift {g : E} {H : E →L[ℝ] E} (hH : H.IsSymmetric)
    {sigma r : ℝ} (hsigma : 0 ≤ sigma) (hr : 2 < r) {s : E} :
    IsMinOn (weightedPowerQuadratic g H M sigma r) univ s ↔
      g + H s + (sigma * energyNorm M s ^ (r - 2)) • M s = 0 ∧
        (H.toLinearMap + (sigma * energyNorm M s ^ (r - 2)) • M).IsPositive := by
  have hh := isMin_powerRegularized_iff_shift (isSymmetric_energyHessian hM hH)
    hsigma hr (g := hM.toEnergy (Minv g)) (s := hM.toEnergy s)
  simpa only [isMinOn_energy_power_iff, WithEnergy.norm_equiv, energy_stationary_iff,
    isPositive_energy_shift_iff hM hH] using hh

/-- A positive definite `M`-shift gives uniqueness of the weighted trust-region minimizer. -/
theorem eq_of_energy_ball_shift_pos {g : E} {H : E →L[ℝ] E} (hH : H.IsSymmetric)
    {s y : E} {delta lambda : ℝ} (hy : energyNorm M y ≤ delta)
    (hlambda : 0 ≤ lambda) (hstat : g + H s + lambda • M s = 0)
    (hpos : ∀ d : E, d ≠ 0 → 0 < inner ℝ d ((H.toLinearMap + lambda • M) d))
    (hcomp : lambda * (energyNorm M s ^ 2 - delta ^ 2) = 0)
    (hval : quadratic g H y ≤ quadratic g H s) : y = s := by
  apply hM.toEnergy.injective
  apply eq_of_isMinOn_closedBall_of_shift_pos (isSymmetric_energyHessian hM hH)
    (delta := delta) (lambda := lambda)
  · exact hy
  · exact hlambda
  · exact (energy_stationary_iff hM g H s lambda).mpr hstat
  · intro d hd
    obtain ⟨d, rfl⟩ := hM.toEnergy.surjective d
    rw [inner_energy_shift]
    apply hpos d
    intro hd0
    apply hd
    simp [hd0]
  · exact hcomp
  · simpa only [quadratic_energy] using hval

/-- A positive definite radial `M`-shift gives uniqueness of the weighted power minimizer. -/
theorem eq_of_energy_power_shift_pos {g : E} {H : E →L[ℝ] E} (hH : H.IsSymmetric)
    {sigma r : ℝ} (hsigma : 0 ≤ sigma) (hr : 2 < r) {s y : E}
    (hstat : g + H s + (sigma * energyNorm M s ^ (r - 2)) • M s = 0)
    (hpos : ∀ d : E, d ≠ 0 → 0 < inner ℝ d
      ((H.toLinearMap + (sigma * energyNorm M s ^ (r - 2)) • M) d))
    (hval : weightedPowerQuadratic g H M sigma r y ≤
      weightedPowerQuadratic g H M sigma r s) : y = s := by
  apply hM.toEnergy.injective
  apply eq_of_isMinOn_powerRegularized_of_shift_pos (isSymmetric_energyHessian hM hH)
    hsigma hr
  · exact (energy_stationary_iff hM g H s _).mpr hstat
  · intro d hd
    obtain ⟨d, rfl⟩ := hM.toEnergy.surjective d
    rw [inner_energy_shift]
    apply hpos d
    intro hd0
    apply hd
    simp [hd0]
  · simpa only [powerRegularized_energy] using hval

end Optimization.QuadraticSubproblem
