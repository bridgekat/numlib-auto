import Numlib.Optimization.QuadraticMinimizerCompletion
import Numlib.Optimization.WeightedQuadraticSubproblem

/-!
# Complete minimizer families for radial quadratic models

All power-regularized minimizers have the same radius and radial multiplier. At this multiplier,
the entire affine kernel completion of a minimum-norm particular solution, intersected with
that sphere, gives exactly all minimizers. For trust regions the zero multiplier retains the
whole feasible ball in the kernel. No simple-eigenvalue assumption is required.
-/

noncomputable section
open scoped InnerProductSpace
open Set Metric
namespace Optimization.QuadraticSubproblem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Increasing a positive semidefinite stationary shift cannot increase the solution norm. -/
theorem norm_le_of_stationary_shift_lt {g s t : E} {H : E →L[ℝ] E} {a b : ℝ}
    (hs : g + H s + a • s = 0) (ht : g + H t + b • t = 0)
    (hp : (H + a • ContinuousLinearMap.id ℝ E).IsPositive) (hab : a < b) :
    ‖t‖ ≤ ‖s‖ := by
  have he : (H + a • ContinuousLinearMap.id ℝ E) (t - s) = (a - b) • t := by
    calc
      _ = (g + H t + b • t) - (g + H s + a • s) + (a - b) • t := by
        simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply, map_sub]
        module
      _ = _ := by rw [ht, hs]; simp
  have h := hp.inner_nonneg_right (t - s)
  rw [he, real_inner_smul_right, inner_sub_left, real_inner_self_eq_norm_sq] at h
  have hi : ‖t‖ ^ 2 ≤ ⟪s, t⟫_ℝ := by nlinarith
  have hc := real_inner_le_norm s t
  by_contra hn
  have hn' : ‖s‖ < ‖t‖ := lt_of_not_ge hn
  have htn : 0 < ‖t‖ := lt_of_le_of_lt (norm_nonneg s) hn'
  nlinarith

/-- All global minimizers of a positively regularized superquadratic have the same norm. -/
theorem norm_eq_of_power_minimizers {g s t : E} {H : E →L[ℝ] E}
    (hH : H.IsSymmetric) {sigma r : ℝ} (hsigma : 0 < sigma) (hr : 2 < r)
    (hs : IsMinOn (powerRegularizedQuadratic g H sigma r) univ s)
    (ht : IsMinOn (powerRegularizedQuadratic g H sigma r) univ t) : ‖s‖ = ‖t‖ := by
  obtain ⟨hsstat, hspos⟩ := (isMin_powerRegularized_iff_shift hH hsigma.le hr).mp hs
  obtain ⟨htstat, htpos⟩ := (isMin_powerRegularized_iff_shift hH hsigma.le hr).mp ht
  have aux (u v : E) (hu : g + H u + (sigma * ‖u‖ ^ (r - 2)) • u = 0)
      (hv : g + H v + (sigma * ‖v‖ ^ (r - 2)) • v = 0)
      (hp : (H + (sigma * ‖u‖ ^ (r - 2)) • ContinuousLinearMap.id ℝ E).IsPositive)
      (hn : ‖u‖ < ‖v‖) : False := by
    have hl : sigma * ‖u‖ ^ (r - 2) < sigma * ‖v‖ ^ (r - 2) :=
      mul_lt_mul_of_pos_left (Real.rpow_lt_rpow (norm_nonneg u) hn (by linarith)) hsigma
    exact (not_lt_of_ge (norm_le_of_stationary_shift_lt hu hv hp hl)) hn
  rcases lt_trichotomy ‖s‖ ‖t‖ with hn | hn | hn
  · exact (aux s t hsstat htstat hspos hn).elim
  · exact hn
  · exact (aux t s htstat hsstat htpos hn).elim

omit [InnerProductSpace ℝ E] in
/-- The radius is recovered from its nonnegative radial multiplier, including radius zero. -/
theorem norm_eq_radial_target (s : E) {sigma r : ℝ} (hsigma : 0 < sigma) (hr : 2 < r) :
    ‖s‖ = (sigma * ‖s‖ ^ (r - 2) / sigma) ^ (1 / (r - 2)) := by
  rw [mul_div_cancel_left₀ _ hsigma.ne', one_div,
    Real.rpow_rpow_inv (norm_nonneg s) (by linarith : r - 2 ≠ 0)]

/-- Exact all-minimizer kernel sphere and value formula for any real exponent greater than two.
The particular solution is orthogonal to the full shifted kernel and uniquely minimizes norm. -/
theorem power_minimizers_kernel_completion {g s : E} {H : E →L[ℝ] E}
    (hH : H.IsSymmetric) {sigma r : ℝ} (hsigma : 0 < sigma) (hr : 2 < r)
    (hs : IsMinOn (powerRegularizedQuadratic g H sigma r) univ s)
    [(H + (sigma * ‖s‖ ^ (r - 2)) • ContinuousLinearMap.id ℝ E).ker.HasOrthogonalProjection] :
    let lambda := sigma * ‖s‖ ^ (r - 2)
    ∃ ss : E, g + H ss + lambda • ss = 0 ∧
      ss ∈ (H + lambda • ContinuousLinearMap.id ℝ E).kerᗮ ∧
      (∀ t : E, IsMinOn (powerRegularizedQuadratic g H sigma r) univ t ↔
        ∃ z ∈ (H + lambda • ContinuousLinearMap.id ℝ E).ker,
          t = ss + z ∧ ‖t‖ = (lambda / sigma) ^ (1 / (r - 2))) ∧
      (∀ t : E, g + H t + lambda • t = 0 →
        ‖ss‖ ≤ ‖t‖ ∧ (‖ss‖ = ‖t‖ ↔ ss = t)) ∧
      powerRegularizedQuadratic g H sigma r s =
        (1 / 2 : ℝ) * (⟪g, ss⟫_ℝ - (r - 2) / r * lambda *
          (lambda / sigma) ^ (2 / (r - 2))) := by
  dsimp only
  let lambda := sigma * ‖s‖ ^ (r - 2)
  obtain ⟨hstat, hpos⟩ := (isMin_powerRegularized_iff_shift hH hsigma.le hr).mp hs
  obtain ⟨ss, hss, horth, hall⟩ := minimizer_eigenspace_completion hstat
  have htarget := norm_eq_radial_target s hsigma hr
  refine ⟨ss, hss, horth, ?_, ?_, ?_⟩
  · intro t
    constructor
    · intro ht
      have hn := norm_eq_of_power_minimizers hH hsigma hr ht hs
      have htstat := (isMin_powerRegularized_iff_shift hH hsigma.le hr).mp ht |>.1
      rw [hn] at htstat
      obtain ⟨z, hz, htz, _⟩ := (hall t).mp htstat
      exact ⟨z, hz, htz, hn.trans htarget⟩
    · rintro ⟨z, hz, htz, hn⟩
      have hn' : ‖t‖ = ‖s‖ := hn.trans htarget.symm
      apply (isMin_powerRegularized_iff_shift hH hsigma.le hr).mpr
      rw [hn']
      refine ⟨(hall t).mpr ⟨z, hz, htz, ?_⟩, hpos⟩
      have hi := (H + lambda • ContinuousLinearMap.id ℝ E).ker.mem_orthogonal' ss |>.mp horth
      rw [htz]
      simpa only [sq] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero ss z (hi z hz)
  · intro t ht
    apply norm_le_of_orthogonal_particular horth
    have h1 := (hall t).mp ht
    obtain ⟨z, hz, htz, _⟩ := h1
    rw [htz, map_add, show (H + lambda • ContinuousLinearMap.id ℝ E) z = 0 from hz,
      add_zero]
  · obtain ⟨z, hz, hsz, _⟩ := (hall s).mp hstat
    have hq := quadratic_kernel_completion_value hH hss hz
    rw [← hsz] at hq
    have hp : ‖s‖ ^ r = ‖s‖ ^ (r - 2) * ‖s‖ ^ (2 : ℕ) := by
      rw [← Real.rpow_two, ← Real.rpow_add' (norm_nonneg s) (by linarith : (r - 2) + 2 ≠ 0)]
      congr 1; ring
    have ht2 : (sigma * ‖s‖ ^ (r - 2) / sigma) ^ (2 / (r - 2)) = ‖s‖ ^ (2 : ℕ) := by
      rw [show 2 / (r - 2) = (1 / (r - 2)) * 2 by ring,
        Real.rpow_mul (by positivity), Real.rpow_two, ← htarget]
    rw [powerRegularizedQuadratic, hq, hp, ht2]
    field_simp
    ring

/-- A vector with zero energy for a positive operator belongs to its kernel. -/
theorem apply_eq_zero_of_positive_inner_eq_zero {A : E →L[ℝ] E} (hA : A.IsPositive)
    {d : E} (hd : ⟪d, A d⟫_ℝ = 0) : A d = 0 := by
  have hm : IsMinOn (quadratic (0 : E) A) univ d := by
    intro y _
    change quadratic 0 A d ≤ quadratic 0 A y
    simp only [quadratic, inner_zero_left, zero_add, hd, mul_zero]
    exact mul_nonneg (by norm_num) (hA.inner_nonneg_right y)
  simpa using (isMinOn_univ_quadratic_iff hA.isSymmetric).mp hm |>.1

/-- The entire trust-region minimizer family at a valid multiplier. Zero multiplier permits
interior kernel completions, while a positive multiplier requires the boundary sphere. -/
theorem ball_minimizers_kernel_completion {g s : E} {H : E →L[ℝ] E}
    (hH : H.IsSymmetric) {delta lambda : ℝ} (hs : ‖s‖ ≤ delta) (hl : 0 ≤ lambda)
    (hstat : g + H s + lambda • s = 0)
    (hpos : (H + lambda • ContinuousLinearMap.id ℝ E).IsPositive)
    (hcomp : lambda * (‖s‖ ^ 2 - delta ^ 2) = 0)
    [(H + lambda • ContinuousLinearMap.id ℝ E).ker.HasOrthogonalProjection] :
    ∃ ss : E, g + H ss + lambda • ss = 0 ∧
      ss ∈ (H + lambda • ContinuousLinearMap.id ℝ E).kerᗮ ∧
      (∀ t : E, (‖t‖ ≤ delta ∧ IsMinOn (quadratic g H) (closedBall 0 delta) t) ↔
        ∃ z ∈ (H + lambda • ContinuousLinearMap.id ℝ E).ker, t = ss + z ∧
          ((lambda = 0 ∧ ‖t‖ ≤ delta) ∨ (0 < lambda ∧ ‖t‖ = delta))) ∧
      (∀ t : E, g + H t + lambda • t = 0 →
        ‖ss‖ ≤ ‖t‖ ∧ (‖ss‖ = ‖t‖ ↔ ss = t)) ∧
      quadratic g H s = (1 / 2 : ℝ) * (⟪g, ss⟫_ℝ - lambda * delta ^ 2) := by
  obtain ⟨ss, hss, horth, hall⟩ := minimizer_eigenspace_completion hstat
  have hmins := isMinOn_closedBall_of_shift hH hs hl hstat hpos hcomp
  refine ⟨ss, hss, horth, ?_, ?_, ?_⟩
  · intro t
    constructor
    · rintro ⟨ht, hmint⟩
      have hval : quadratic g H t = quadratic g H s :=
        le_antisymm (hmint (mem_closedBall_zero_iff.mpr hs))
          (hmins (mem_closedBall_zero_iff.mpr ht))
      have hd := quadratic_sub_of_stationary hH hstat t
      have hp := hpos.inner_nonneg_right (t - s)
      have ht2 : ‖t‖ ^ 2 ≤ delta ^ 2 := by
        nlinarith [norm_nonneg t, (norm_nonneg s).trans hs]
      have hgap : 0 ≤ lambda * (delta ^ 2 - ‖t‖ ^ 2) := mul_nonneg hl (sub_nonneg.mpr ht2)
      have hzero : ⟪t - s, (H + lambda • ContinuousLinearMap.id ℝ E) (t - s)⟫_ℝ = 0 := by
        rw [hval] at hd
        nlinarith
      have hz := apply_eq_zero_of_positive_inner_eq_zero hpos hzero
      have htstat : g + H t + lambda • t = 0 := by
        have he : (H + lambda • ContinuousLinearMap.id ℝ E) (t - s) =
            (g + H t + lambda • t) - (g + H s + lambda • s) := by
          simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply, map_sub]
          abel
        rw [he, hstat, sub_zero] at hz
        exact hz
      obtain ⟨z, hz, htz, _⟩ := (hall t).mp htstat
      refine ⟨z, hz, htz, (feasible_complementarity_iff hl).mp ⟨ht, ?_⟩⟩
      rw [hval] at hd
      nlinarith
    · rintro ⟨z, hz, htz, hc⟩
      obtain ⟨ht, hct⟩ := (feasible_complementarity_iff hl).mpr hc
      have hi := (H + lambda • ContinuousLinearMap.id ℝ E).ker.mem_orthogonal' ss |>.mp horth
      have hn : ‖t‖ ^ 2 = ‖ss‖ ^ 2 + ‖z‖ ^ 2 := by
        rw [htz]
        simpa only [sq] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero ss z (hi z hz)
      exact ⟨ht, isMinOn_closedBall_of_shift hH ht hl
        ((hall t).mpr ⟨z, hz, htz, hn⟩) hpos hct⟩
  · intro t ht
    obtain ⟨z, hz, htz, _⟩ := (hall t).mp ht
    apply norm_le_of_orthogonal_particular horth
    rw [htz, map_add, show (H + lambda • ContinuousLinearMap.id ℝ E) z = 0 from hz,
      add_zero]
  · obtain ⟨z, hz, hsz, _⟩ := (hall s).mp hstat
    have hq := quadratic_kernel_completion_value hH hss hz
    rw [← hsz] at hq
    nlinarith

section Weighted
variable [FiniteDimensional ℝ E] {M Minv : E →ₗ[ℝ] E}
variable (hM : Krylov.IsPreconditioner M Minv)

/-- A zero shifted energy vector is exactly a generalized shifted null vector. -/
theorem energy_kernel_iff (H : E →L[ℝ] E) (z : E) (lambda : ℝ) :
    hM.toEnergy z ∈ (energyHessian hM H +
      lambda • ContinuousLinearMap.id ℝ hM.EnergySpace).ker ↔ H z + lambda • M z = 0 := by
  change energyHessian hM H (hM.toEnergy z) + lambda • hM.toEnergy z = 0 ↔ _
  simpa only [zero_add, map_zero] using energy_stationary_iff hM (0 : E) H z lambda

include hM

/-- All minimizers and their value in an arbitrary positive definite metric. The distinguished
particular solution is the unique minimum metric norm solution of the shifted system. -/
theorem weighted_power_minimizers_kernel_completion {g s : E} {H : E →L[ℝ] E}
    (hH : H.IsSymmetric) {sigma r : ℝ} (hsigma : 0 < sigma) (hr : 2 < r)
    (hs : IsMinOn (weightedPowerQuadratic g H M sigma r) univ s) :
    let lambda := sigma * energyNorm M s ^ (r - 2)
    ∃ ss : E, g + H ss + lambda • M ss = 0 ∧
      (∀ t : E, IsMinOn (weightedPowerQuadratic g H M sigma r) univ t ↔
        ∃ z : E, H z + lambda • M z = 0 ∧ t = ss + z ∧
          energyNorm M t = (lambda / sigma) ^ (1 / (r - 2))) ∧
      (∀ t : E, g + H t + lambda • M t = 0 →
        energyNorm M ss ≤ energyNorm M t ∧
          (energyNorm M ss = energyNorm M t ↔ ss = t)) ∧
      weightedPowerQuadratic g H M sigma r s =
        (1 / 2 : ℝ) * (⟪g, ss⟫_ℝ - (r - 2) / r * lambda *
          (lambda / sigma) ^ (2 / (r - 2))) := by
  have hm := (isMinOn_energy_power_iff hM g H sigma r s).mpr hs
  obtain ⟨ss, hss, _, hall, hnorm, hval⟩ :=
    power_minimizers_kernel_completion (isSymmetric_energyHessian hM hH) hsigma hr hm
  obtain ⟨ss, rfl⟩ := hM.toEnergy.surjective ss
  dsimp only
  simp only [WithEnergy.norm_equiv, energy_stationary_iff hM] at hss hnorm
  refine ⟨ss, hss, ?_, ?_, ?_⟩
  · intro t
    have hh := hall (hM.toEnergy t)
    rw [isMinOn_energy_power_iff] at hh
    constructor
    · intro ht
      obtain ⟨z, hz, heq, hn⟩ := hh.mp ht
      obtain ⟨z, rfl⟩ := hM.toEnergy.surjective z
      refine ⟨z, (energy_kernel_iff hM H z _).mp hz, ?_, hn⟩
      exact hM.toEnergy.injective (by simpa only [map_add] using heq)
    · rintro ⟨z, hz, heq, hn⟩
      exact hh.mpr ⟨hM.toEnergy z, (energy_kernel_iff hM H z _).mpr hz,
        by simpa only [map_add] using congrArg hM.toEnergy heq, hn⟩
  · intro t ht
    simpa only [WithEnergy.norm_equiv, hM.toEnergy.injective.eq_iff] using
      hnorm (hM.toEnergy t) ((energy_stationary_iff hM g H t _).mpr ht)
  · have hi : ⟪hM.toEnergy (Minv g), hM.toEnergy ss⟫_ℝ = ⟪g, ss⟫_ℝ := by
      rw [real_inner_comm, hM.inner_toEnergy_inv, real_inner_comm]
    simpa only [powerRegularized_energy, WithEnergy.norm_equiv, hi] using hval

/-- Full feasible kernel completion and minimum value for trust regions in an SPD metric. -/
theorem weighted_ball_minimizers_kernel_completion {g s : E} {H : E →L[ℝ] E}
    (hH : H.IsSymmetric) {delta lambda : ℝ} (hs : energyNorm M s ≤ delta) (hl : 0 ≤ lambda)
    (hstat : g + H s + lambda • M s = 0) (hpos : (H.toLinearMap + lambda • M).IsPositive)
    (hcomp : lambda * (energyNorm M s ^ 2 - delta ^ 2) = 0) :
    ∃ ss : E, g + H ss + lambda • M ss = 0 ∧
      (∀ t : E, (energyNorm M t ≤ delta ∧
          IsMinOn (quadratic g H) {x | energyNorm M x ≤ delta} t) ↔
        ∃ z : E, H z + lambda • M z = 0 ∧ t = ss + z ∧
          ((lambda = 0 ∧ energyNorm M t ≤ delta) ∨
            (0 < lambda ∧ energyNorm M t = delta))) ∧
      (∀ t : E, g + H t + lambda • M t = 0 →
        energyNorm M ss ≤ energyNorm M t ∧
          (energyNorm M ss = energyNorm M t ↔ ss = t)) ∧
      quadratic g H s = (1 / 2 : ℝ) * (⟪g, ss⟫_ℝ - lambda * delta ^ 2) := by
  obtain ⟨ss, hss, _, hall, hnorm, hval⟩ :=
    ball_minimizers_kernel_completion (isSymmetric_energyHessian hM hH)
      (s := hM.toEnergy s) hs hl ((energy_stationary_iff hM g H s _).mpr hstat)
      ((isPositive_energy_shift_iff hM hH _).mpr hpos) hcomp
  obtain ⟨ss, rfl⟩ := hM.toEnergy.surjective ss
  refine ⟨ss, (energy_stationary_iff hM g H ss _).mp hss, ?_, ?_, ?_⟩
  · intro t
    have hh := hall (hM.toEnergy t)
    rw [isMinOn_energy_ball_iff] at hh
    constructor
    · intro ht
      obtain ⟨z, hz, heq, hn⟩ := hh.mp ht
      obtain ⟨z, rfl⟩ := hM.toEnergy.surjective z
      refine ⟨z, (energy_kernel_iff hM H z _).mp hz, ?_, hn⟩
      exact hM.toEnergy.injective (by simpa only [map_add] using heq)
    · rintro ⟨z, hz, heq, hn⟩
      exact hh.mpr ⟨hM.toEnergy z, (energy_kernel_iff hM H z _).mpr hz,
        by simpa only [map_add] using congrArg hM.toEnergy heq, hn⟩
  · intro t ht
    simpa only [WithEnergy.norm_equiv, hM.toEnergy.injective.eq_iff] using
      hnorm (hM.toEnergy t) ((energy_stationary_iff hM g H t _).mpr ht)
  · have hi : ⟪hM.toEnergy (Minv g), hM.toEnergy ss⟫_ℝ = ⟪g, ss⟫_ℝ := by
      rw [real_inner_comm, hM.inner_toEnergy_inv, real_inner_comm]
    simpa only [quadratic_energy, hi] using hval
end Weighted

end Optimization.QuadraticSubproblem
