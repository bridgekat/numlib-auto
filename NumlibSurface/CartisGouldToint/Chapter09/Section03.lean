import Numlib.Analysis.InnerProductSpace.SpectralNormBounds
import Numlib.Optimization.PowerShiftBracket
import Numlib.Eigen.PencilGershgorin
import NumlibSurface.CartisGouldToint.Chapter08.Section03

/-!
# Chapter 9, Section 3: spectral bounds for regularization

Generalized Gershgorin regions provide computable outer bounds for the generalized
spectrum. Both positive denominators are retained, so the bounds apply to indefinite
Hessians as well as positive ones.
-/

namespace CartisGouldToint.Chapter09.Section03
open Matrix
variable {n : ℕ} {H M : Matrix (Fin n) (Fin n) ℝ}

/-- The generalized Gershgorin enclosure (9.3.6)–(9.3.7), including the exact two-denominator
outer bounds printed after (9.3.7). The inclusion needs only positive strict row dominance
of `M`; symmetry and positive definiteness are not needed once a real eigenvalue is given. -/
theorem generalizedGershgorinBounds {μ : ℝ} (hμ : μ ∈ pencilSpectrum H M)
    (hM : ∀ k, offDiagonalRowSum M k < M k k) :
    (∃ k, |H k k - μ * M k k| ≤ offDiagonalRowSum H k + |μ| * offDiagonalRowSum M k) ∧
    (⨅ k : Fin n, min ((H k k - offDiagonalRowSum H k) / (M k k - offDiagonalRowSum M k))
      ((H k k - offDiagonalRowSum H k) / (M k k + offDiagonalRowSum M k))) ≤ μ ∧
    μ ≤ ⨆ k : Fin n, max ((H k k + offDiagonalRowSum H k) / (M k k - offDiagonalRowSum M k))
      ((H k k + offDiagonalRowSum H k) / (M k k + offDiagonalRowSum M k)) := by
  refine ⟨exists_row_abs_sub_le_of_mem_pencilSpectrum hμ, ?_⟩
  obtain ⟨k, hlo, hup⟩ := exists_row_interval_of_mem_pencilSpectrum hM hμ
  have : Nonempty (Fin n) := ⟨k⟩
  constructor
  · exact (ciInf_le (Set.finite_range _).bddBelow k).trans hlo
  · refine hup.trans ?_
    exact le_ciSup (f := fun j : Fin n => max
      ((H j j + offDiagonalRowSum H j) / (M j j - offDiagonalRowSum M j))
      ((H j j + offDiagonalRowSum H j) / (M j j + offDiagonalRowSum M j)))
      (Set.finite_range _).bddAbove k

open scoped InnerProductSpace
open CartisGouldToint.Chapter08.Section01 CartisGouldToint.Chapter08.Section02
open Optimization.QuadraticSubproblem

/-- The dual source norm is the energy norm of the preconditioned vector. -/
theorem weightedDualNorm_eq_norm_toEnergy (hM : M.PosDef) (g : EuclideanSpace ℝ (Fin n)) :
    weightedNorm M⁻¹ g =
      ‖hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)‖ := by
  unfold weightedNorm
  have hs := hM.isPreconditioner_toEuclideanLin.norm_toEnergy_inv_sq g
  simp only [RCLike.re_to_real] at hs
  rw [← hs]
  exact Real.sqrt_sq_eq_abs _ |>.trans (abs_of_nonneg (norm_nonneg _))

/-- Positive semidefinite shifts make all generalized spectral shifts nonnegative. -/
theorem secularEigenvalues_shift_nonneg (hH : H.IsSymm) (hM : M.PosDef) {t : ℝ}
    (hp : (H + t • M).PosSemidef) : ∀ i, 0 ≤ t + secularEigenvalues hH hM i := by
  intro i
  have hv : secularEigenvector hH hM i ≠ 0 := by
    intro hz
    have horth := secularEigenvector_orthonormal hH hM i i
    simp [hz] at horth
  have hh := CartisGouldToint.Chapter08.Section03.generalized_eigenvalue_lower_bound hM
    hp hv (secularEigenvector_equation hH hM i)
  linarith

/-- A nonnegative positive semidefinite shift lies above the source spectral cutoff,
including the zero-dimensional case. -/
theorem secularThreshold_le_of_posSemidef (hH : H.IsSymm) (hM : M.PosDef) {t : ℝ}
    (ht : 0 ≤ t) (hp : (H + t • M).PosSemidef) : secularThreshold hH hM ≤ t := by
  have hh : (Finset.univ.sup fun i =>
      (⟨max 0 (-secularEigenvalues hH hM i), le_max_left _ _⟩ : NNReal)) ≤
      (⟨t, ht⟩ : NNReal) := by
    apply Finset.sup_le
    intro i _
    change max 0 (-secularEigenvalues hH hM i) ≤ t
    exact max_le ht (by linarith [secularEigenvalues_shift_nonneg hH hM hp i])
  exact hh

/-- A positive semidefinite shifted stationarity equation bounds the dual gradient norm
by the shifted generalized spectral endpoints times the actual step norm. This includes
singular shifts and does not replace nullspace components by a totalized inverse. -/
theorem stationary_weightedNorm_bounds (hH : H.IsSymm) (hM : M.PosDef)
    {g s : EuclideanSpace ℝ (Fin n)} {t a b : ℝ}
    (hstat : Matrix.toEuclideanLin (H + t • M) s = -g)
    (hp : (H + t • M).PosSemidef)
    (hlo : ∀ i, a ≤ secularEigenvalues hH hM i)
    (hup : ∀ i, secularEigenvalues hH hM i ≤ b) :
    (t + a) * weightedNorm M s ≤ weightedNorm M⁻¹ g ∧
      weightedNorm M⁻¹ g ≤ (t + b) * weightedNorm M s := by
  have hpos := secularEigenvalues_shift_nonneg hH hM hp
  have he := (energy_stationary_iff hM.isPreconditioner_toEuclideanLin g
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H) s t).mpr
      ((metric_shift_stationary_iff t).mpr hstat)
  have heq : secularHessian H hM (hM.isPreconditioner_toEuclideanLin.toEnergy s) +
      t • hM.isPreconditioner_toEuclideanLin.toEnergy s =
      -hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g) := by
    apply eq_neg_of_add_eq_zero_right
    rw [← add_assoc]
    exact he
  have hb := (secularHessian_isSymmetric hH hM).norm_shift_bounds_of_eigenvalue_bounds
    hpos hlo hup (hM.isPreconditioner_toEuclideanLin.toEnergy s)
  rw [heq, norm_neg, ← weightedDualNorm_eq_norm_toEnergy hM] at hb
  simpa only [WithEnergy.norm_equiv, ← weightedNorm_eq_energyNorm] using hb

/-- The regularization spectral inequalities (9.3.3)–(9.3.4) for an actual global
minimizer and its radial multiplier. All powers are valid at zero; the zero multiplier
forces both the step and gradient to vanish. -/
theorem regularizationMultiplierBracket (hH : H.IsSymm) (hM : M.PosDef)
    {g s : EuclideanSpace ℝ (Fin n)} {sigma r a b : ℝ}
    (hsigma : 0 < sigma) (hr : 2 < r)
    (hs : regularizedMinimizer g H M sigma r s)
    (hlo : ∀ i, a ≤ secularEigenvalues hH hM i)
    (hup : ∀ i, secularEigenvalues hH hM i ≤ b) :
    ∃ t : ℝ, t = sigma * weightedNorm M s ^ (r - 2) ∧ 0 ≤ t ∧
      Matrix.toEuclideanLin (H + t • M) s = -g ∧ (H + t • M).PosSemidef ∧
      (t + a) * t ^ (1 / (r - 2)) ≤ sigma ^ (1 / (r - 2)) * weightedNorm M⁻¹ g ∧
      sigma ^ (1 / (r - 2)) * weightedNorm M⁻¹ g ≤ (t + b) * t ^ (1 / (r - 2)) ∧
      secularThreshold hH hM ≤ t ∧ (t = 0 → s = 0 ∧ g = 0) := by
  obtain ⟨t, hrad, hstat, hp⟩ := (theorem_8_2_8 hH hM hsigma hr).1.mp hs
  have hn : 0 ≤ weightedNorm M s := Real.sqrt_nonneg _
  have hpσ : 0 < sigma ^ (1 / (r - 2)) := Real.rpow_pos_of_pos hsigma _
  have ht : 0 ≤ t := by rw [hrad]; positivity
  have hpower : t ^ (1 / (r - 2)) = sigma ^ (1 / (r - 2)) * weightedNorm M s := by
    rw [hrad, Real.mul_rpow hsigma.le (Real.rpow_nonneg hn _), ← Real.rpow_mul hn]
    have hexp : (r - 2) * (1 / (r - 2)) = 1 := by field_simp [ne_of_gt (sub_pos.mpr hr)]
    rw [hexp, Real.rpow_one]
  have hb := stationary_weightedNorm_bounds hH hM hstat hp hlo hup
  refine ⟨t, hrad, ht, hstat, hp, ?_, ?_,
    secularThreshold_le_of_posSemidef hH hM ht hp, ?_⟩
  · rw [hpower]
    nlinarith [mul_le_mul_of_nonneg_left hb.1 hpσ.le]
  · rw [hpower]
    nlinarith [mul_le_mul_of_nonneg_left hb.2 hpσ.le]
  · intro ht0
    have hz : weightedNorm M s = 0 := by
      have hmul : sigma * weightedNorm M s ^ (r - 2) = 0 := hrad.symm.trans ht0
      have hpow := (mul_eq_zero.mp hmul).resolve_left hsigma.ne'
      exact ((Real.rpow_eq_zero_iff_of_nonneg hn).mp hpow).1
    have hs0 : s = 0 := by
      by_contra h
      have hh := hM.isSymmetricCoercive_toEuclideanLin.energyNorm_pos h
      rw [← weightedNorm_eq_energyNorm, hz] at hh
      exact (lt_irrefl 0) hh
    refine ⟨hs0, ?_⟩
    simpa only [hs0, map_zero, neg_eq_zero] using hstat.symm

/-- Solving (9.3.5) on the nonnegative branches gives the actual multiplier bracket.
The roots are supplied as scalar equation solutions; no root-selection or existence oracle
is assumed. Positive dimension is used only to infer the upper shifted endpoint is nonnegative. -/
theorem regularizationMultiplierRootBracket [NeZero n] (hH : H.IsSymm) (hM : M.PosDef)
    {g s : EuclideanSpace ℝ (Fin n)} {sigma r a b L U : ℝ}
    (hsigma : 0 < sigma) (hr : 2 < r)
    (hs : regularizedMinimizer g H M sigma r s)
    (hlo : ∀ i, a ≤ secularEigenvalues hH hM i)
    (hup : ∀ i, secularEigenvalues hH hM i ≤ b)
    (hL : max 0 (-b) ≤ L) (hU : max 0 (-a) ≤ U)
    (hLeq : Optimization.shiftPower b (1 / (r - 2)) L =
      sigma ^ (1 / (r - 2)) * weightedNorm M⁻¹ g)
    (hUeq : Optimization.shiftPower a (1 / (r - 2)) U =
      sigma ^ (1 / (r - 2)) * weightedNorm M⁻¹ g) :
    ∃ t : ℝ, t = sigma * weightedNorm M s ^ (r - 2) ∧ L ≤ t ∧ t ≤ U := by
  obtain ⟨t, hrad, ht, _, hp, hl, hu, _⟩ :=
    regularizationMultiplierBracket hH hM hsigma hr hs hlo hup
  have : Nontrivial hM.isPreconditioner_toEuclideanLin.EnergySpace :=
    hM.isPreconditioner_toEuclideanLin.toEnergy.symm.toEquiv.nontrivial
  let i : Fin (Module.finrank ℝ hM.isPreconditioner_toEuclideanLin.EnergySpace) :=
    ⟨0, Module.finrank_pos⟩
  have htb : 0 ≤ t + b := by
    linarith [secularEigenvalues_shift_nonneg hH hM hp i, hup i]
  exact ⟨t, hrad, Optimization.shiftPower_root_bracket (by positivity : 0 < 1 / (r - 2))
    ht htb hl hu hL hU hLeq hUeq⟩

end CartisGouldToint.Chapter09.Section03
