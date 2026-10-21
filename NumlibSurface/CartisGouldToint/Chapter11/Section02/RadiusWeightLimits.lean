import Numlib.Optimization.StationaryAsymptotics
import NumlibSurface.CartisGouldToint.Chapter11.Section02.SecularLimits

/-!
# Chapter 11: radius and regularization weight asymptotics

The boundary and regularized families satisfy the actual shifted equations in the original
coordinates. The multiplier divergence follows from those equations. The reciprocal expressions
in the supplied transcription of (11.2.3) and (11.2.5) are corrected: the products tend to the
dual gradient norm. This agrees with the fidelity column of Table 11.2.1.
-/

namespace CartisGouldToint.Chapter11.Section02
open Filter Topology
open Chapter08.Section01 Chapter08.Section02 Optimization.QuadraticSubproblem
open Optimization.StationaryAsymptotics

variable {α : Type*} {l : Filter α} {n : ℕ}
  {g : EuclideanSpace ℝ (Fin n)} {H M : Matrix (Fin n) (Fin n) ℝ}

/-- Transport to the metric space identifies its norm with the source weighted norm. -/
theorem norm_toEnergy_eq_weightedNorm (hM : M.PosDef) (s : EuclideanSpace ℝ (Fin n)) :
    ‖hM.isPreconditioner_toEuclideanLin.toEnergy s‖ = weightedNorm M s := by
  rw [WithEnergy.norm_equiv, weightedNorm_eq_energyNorm]

/-- A nonzero vector has strictly positive norm in the source positive definite metric. -/
theorem weightedNorm_pos_of_ne_zero (hM : M.PosDef) {s : EuclideanSpace ℝ (Fin n)}
    (hs : s ≠ 0) : 0 < weightedNorm M s := by
  rw [← norm_toEnergy_eq_weightedNorm hM]
  apply norm_pos_iff.mpr
  intro h
  apply hs
  exact hM.isPreconditioner_toEuclideanLin.toEnergy.injective (by simpa using h)

/-- Along arbitrary shrinking boundary solutions, the multiplier diverges and its radius
product tends to the dual norm. The corresponding regularization weight has the same product
limit for every real order. -/
theorem boundary_radius_weight_limits (hM : M.PosDef) (hg : g ≠ 0)
    {s : α → EuclideanSpace ℝ (Fin n)} {δ lam : α → ℝ} (r : ℝ)
    (hδ : Tendsto δ l (𝓝 0)) (hlam : ∀ᶠ a in l, 0 ≤ lam a)
    (hboundary : ∀ᶠ a in l, weightedNorm M (s a) = δ a)
    (hstat : ∀ᶠ a in l, g + Matrix.toEuclideanLin H (s a) +
      lam a • Matrix.toEuclideanLin M (s a) = 0) :
    Tendsto lam l atTop ∧
    Tendsto (fun a => lam a * δ a) l (𝓝 (weightedNorm M⁻¹ g)) ∧
    Tendsto (fun a => (lam a / δ a ^ (r - 2)) * δ a ^ (r - 1)) l
      (𝓝 (weightedNorm M⁻¹ g)) := by
  let P := hM.isPreconditioner_toEuclideanLin
  let A := energyHessian P (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H)
  let b := P.toEnergy (Matrix.toEuclideanLin M⁻¹ g)
  let x := fun a => P.toEnergy (s a)
  have hb : b ≠ 0 := Optimization.SecularResolvent.toEnergy_inv_ne_zero P hg
  have hn : ∀ a, ‖x a‖ = weightedNorm M (s a) := fun a => norm_toEnergy_eq_weightedNorm hM (s a)
  have he : ∀ᶠ a in l, b + A (x a) + lam a • x a = 0 := by
    filter_upwards [hstat] with a ha
    exact (energy_stationary_iff P g _ (s a) (lam a)).mpr ha
  have hx : Tendsto x l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply hδ.congr'
    filter_upwards [hboundary] with a ha
    exact ha.symm.trans (hn a).symm
  have hprod := tendsto_mul_norm_of_stationary he hlam hx
  have hprod' : Tendsto (fun a => lam a * δ a) l (𝓝 (weightedNorm M⁻¹ g)) := by
    rw [show ‖b‖ = weightedNorm M⁻¹ g from secular_rightHandSide_norm hM] at hprod
    apply hprod.congr'
    filter_upwards [hboundary] with a ha
    rw [hn, ha]
  refine ⟨tendsto_atTop_of_stationary hb he hlam hx, hprod', ?_⟩
  apply hprod'.congr'
  filter_upwards [he, hboundary] with a ha hba
  have hpos : 0 < δ a := by
    rw [← hba, ← hn]
    exact norm_pos_iff.mpr (stationary_ne_zero hb ha)
  simpa only [show r - 1 - 1 = r - 2 by ring] using
    (div_rpow_mul_rpow (y := lam a) (p := r - 1) hpos).symm

/-- Arbitrary actual regularized stationary solutions have the inverse-parameter asymptotic
coefficient displayed in Section 11.2, with nonnegative quadratic curvature. -/
theorem regularized_multiplier_limit (hH : H.PosSemidef) (hM : M.PosDef) (hg : g ≠ 0)
    {s : α → EuclideanSpace ℝ (Fin n)} {σ : α → ℝ} {r : ℝ} (hr : 1 < r)
    (hσ : Tendsto σ l atTop)
    (hstat : ∀ᶠ a in l, g + Matrix.toEuclideanLin H (s a) +
      (σ a * weightedNorm M (s a) ^ (r - 2)) • Matrix.toEuclideanLin M (s a) = 0) :
    Tendsto (fun a => (σ a * weightedNorm M (s a) ^ (r - 2)) /
      (σ a ^ (1 / (r - 1)) * weightedNorm M⁻¹ g ^ ((r - 2) / (r - 1)))) l (𝓝 1) := by
  let P := hM.isPreconditioner_toEuclideanLin
  let A := energyHessian P (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H)
  let b := P.toEnergy (Matrix.toEuclideanLin M⁻¹ g)
  let x := fun a => P.toEnergy (s a)
  have hb : b ≠ 0 := Optimization.SecularResolvent.toEnergy_inv_ne_zero P hg
  have hn : ∀ a, ‖x a‖ = weightedNorm M (s a) := fun a => norm_toEnergy_eq_weightedNorm hM (s a)
  have hA : ∀ᶠ a in l, 0 ≤ inner ℝ (x a) (A (x a)) := by
    apply Eventually.of_forall
    intro a
    change 0 ≤ inner ℝ (P.toEnergy (s a))
      (P.toEnergy (Matrix.toEuclideanLin M⁻¹ (Matrix.toEuclideanLin H (s a))))
    rw [P.inner_toEnergy_inv]
    exact (Matrix.isPositive_toEuclideanLin_iff.mpr hH).inner_nonneg_right _
  have he : ∀ᶠ a in l, b + A (x a) + (σ a * ‖x a‖ ^ (r - 2)) • x a = 0 := by
    filter_upwards [hstat] with a ha
    rw [hn]
    exact (energy_stationary_iff P g _ (s a) _).mpr ha
  have hlim := tendsto_normalized_regularized_multiplier hb hr hσ hA he
  simpa only [hn, show ‖b‖ = weightedNorm M⁻¹ g from secular_rightHandSide_norm hM]
    using hlim

/-- Arbitrary actual regularized stationary solutions have the inverse-parameter asymptotic
coefficient displayed in Section 11.2, for every fixed quadratic Hessian. -/
theorem superquadratic_multiplier_limit (hM : M.PosDef) (hg : g ≠ 0)
    {s : α → EuclideanSpace ℝ (Fin n)} {σ : α → ℝ} {r : ℝ} (hr : 2 < r)
    (hσ : Tendsto σ l atTop)
    (hstat : ∀ᶠ a in l, g + Matrix.toEuclideanLin H (s a) +
      (σ a * weightedNorm M (s a) ^ (r - 2)) • Matrix.toEuclideanLin M (s a) = 0) :
    Tendsto (fun a => (σ a * weightedNorm M (s a) ^ (r - 2)) /
      (σ a ^ (1 / (r - 1)) * weightedNorm M⁻¹ g ^ ((r - 2) / (r - 1)))) l (𝓝 1) := by
  let P := hM.isPreconditioner_toEuclideanLin
  let A := energyHessian P (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H)
  let b := P.toEnergy (Matrix.toEuclideanLin M⁻¹ g)
  let x := fun a => P.toEnergy (s a)
  have hb : b ≠ 0 := Optimization.SecularResolvent.toEnergy_inv_ne_zero P hg
  have hn : ∀ a, ‖x a‖ = weightedNorm M (s a) := fun a => norm_toEnergy_eq_weightedNorm hM (s a)
  have he : ∀ᶠ a in l, b + A (x a) + (σ a * ‖x a‖ ^ (r - 2)) • x a = 0 := by
    filter_upwards [hstat] with a ha
    rw [hn]
    exact (energy_stationary_iff P g _ (s a) _).mpr ha
  have hlim := tendsto_normalized_superquadratic_multiplier hb hr hσ he
  simpa only [hn, show ‖b‖ = weightedNorm M⁻¹ g from secular_rightHandSide_norm hM]
    using hlim

/-- Actual regularized solutions with nonzero gradient have nonzero metric norm;
the weight and radial multiplier are eventually strictly positive at large weights. -/
theorem eventually_regularized_positive (hM : M.PosDef) (hg : g ≠ 0)
    {s : α → EuclideanSpace ℝ (Fin n)} {σ : α → ℝ} (r : ℝ)
    (hσ : Tendsto σ l atTop)
    (hstat : ∀ᶠ a in l, g + Matrix.toEuclideanLin H (s a) +
      (σ a * weightedNorm M (s a) ^ (r - 2)) • Matrix.toEuclideanLin M (s a) = 0) :
    ∀ᶠ a in l, 0 < weightedNorm M (s a) ∧ 0 < σ a ∧
      0 < σ a * weightedNorm M (s a) ^ (r - 2) := by
  filter_upwards [hσ.eventually_gt_atTop 0, hstat] with a hsa ha
  have hs : s a ≠ 0 := by
    intro hz
    simp only [hz, map_zero, smul_zero, add_zero] at ha
    exact hg ha
  have hn := weightedNorm_pos_of_ne_zero hM hs
  exact ⟨hn, hsa, mul_pos hsa (Real.rpow_pos_of_pos hn _)⟩

/-- The dual metric norm of a nonzero gradient is strictly positive. -/
theorem weightedNorm_inverse_pos (hM : M.PosDef) (hg : g ≠ 0) :
    0 < weightedNorm M⁻¹ g := by
  rw [← secular_rightHandSide_norm hM]
  exact norm_pos_iff.mpr
    (Optimization.SecularResolvent.toEnergy_inv_ne_zero hM.isPreconditioner_toEuclideanLin hg)

/-- The corrected radius-to-weight relation has fidelity tending to one, as in Table 11.2.1. -/
theorem boundary_weight_fidelity (hM : M.PosDef) (hg : g ≠ 0)
    {s : α → EuclideanSpace ℝ (Fin n)} {δ lam : α → ℝ} (r : ℝ)
    (hδ : Tendsto δ l (𝓝 0)) (hlam : ∀ᶠ a in l, 0 ≤ lam a)
    (hboundary : ∀ᶠ a in l, weightedNorm M (s a) = δ a)
    (hstat : ∀ᶠ a in l, g + Matrix.toEuclideanLin H (s a) +
      lam a • Matrix.toEuclideanLin M (s a) = 0) :
    Tendsto (fun a => ((lam a / δ a ^ (r - 2)) * δ a ^ (r - 1)) /
      weightedNorm M⁻¹ g) l (𝓝 1) := by
  have h := (boundary_radius_weight_limits hM hg r hδ hlam hboundary hstat).2.2
  simpa only [div_self (weightedNorm_inverse_pos hM hg).ne'] using
    h.div_const (weightedNorm M⁻¹ g)

/-- Halving a shrinking trust-region boundary radius asymptotically multiplies its
corresponding regularization weight by `2^(r-1)`. Both families solve the actual systems. -/
theorem halving_radius_weight_limit (hM : M.PosDef) (hg : g ≠ 0)
    {s shalf : α → EuclideanSpace ℝ (Fin n)} {δ lam lamhalf : α → ℝ} (r : ℝ)
    (hδ : Tendsto δ l (𝓝 0))
    (hlam : ∀ᶠ a in l, 0 ≤ lam a) (hlamhalf : ∀ᶠ a in l, 0 ≤ lamhalf a)
    (hboundary : ∀ᶠ a in l, weightedNorm M (s a) = δ a)
    (hhalfboundary : ∀ᶠ a in l, weightedNorm M (shalf a) = δ a / 2)
    (hstat : ∀ᶠ a in l, g + Matrix.toEuclideanLin H (s a) +
      lam a • Matrix.toEuclideanLin M (s a) = 0)
    (hhalfstat : ∀ᶠ a in l, g + Matrix.toEuclideanLin H (shalf a) +
      lamhalf a • Matrix.toEuclideanLin M (shalf a) = 0) :
    Tendsto (fun a => (lamhalf a / (δ a / 2) ^ (r - 2)) /
      (lam a / δ a ^ (r - 2))) l (𝓝 ((2 : ℝ) ^ (r - 1))) := by
  have hfirst := (boundary_radius_weight_limits hM hg r hδ hlam hboundary hstat).2.2
  have hδhalf : Tendsto (fun a => δ a / 2) l (𝓝 0) := by simpa using hδ.div_const 2
  have hsecond := (boundary_radius_weight_limits hM hg r hδhalf hlamhalf
    hhalfboundary hhalfstat).2.2
  have hdpos : ∀ᶠ a in l, 0 < δ a := by
    filter_upwards [hstat, hboundary] with a ha hb
    rw [← hb]
    apply weightedNorm_pos_of_ne_zero hM
    intro hz
    simp only [hz, map_zero, smul_zero, add_zero] at ha
    exact hg ha
  exact tendsto_weight_ratio (weightedNorm_inverse_pos hM hg).ne' (by norm_num) hdpos
    hfirst hsecond

/-- The full radius/weight asymptotics of (11.2.3)–(11.2.5), with the two
transcribed reciprocal formulas corrected. The boundary, large-weight, and halved-boundary
families all satisfy their actual shifted systems. The fidelity is the ratio used in
Table 11.2.1; no claim about finite numerical entries or computational efficiency is made. -/
theorem radiusWeightAsymptotics {β : Type*} {k : Filter β}
    (hH : H.IsSymm) (hM : M.PosDef) (hg : g ≠ 0) {r : ℝ} (hr : 2 < r)
    {s shalf : α → EuclideanSpace ℝ (Fin n)} {δ lam lamhalf : α → ℝ}
    {u : β → EuclideanSpace ℝ (Fin n)} {σ : β → ℝ}
    (hδ : Tendsto δ l (𝓝 0)) (hlam : ∀ᶠ a in l, 0 ≤ lam a)
    (hlamhalf : ∀ᶠ a in l, 0 ≤ lamhalf a)
    (hboundary : ∀ᶠ a in l, weightedNorm M (s a) = δ a)
    (hhalfboundary : ∀ᶠ a in l, weightedNorm M (shalf a) = δ a / 2)
    (hstat : ∀ᶠ a in l, g + Matrix.toEuclideanLin H (s a) +
      lam a • Matrix.toEuclideanLin M (s a) = 0)
    (hhalfstat : ∀ᶠ a in l, g + Matrix.toEuclideanLin H (shalf a) +
      lamhalf a • Matrix.toEuclideanLin M (shalf a) = 0)
    (hσ : Tendsto σ k atTop)
    (hreg : ∀ᶠ a in k, g + Matrix.toEuclideanLin H (u a) +
      (σ a * weightedNorm M (u a) ^ (r - 2)) • Matrix.toEuclideanLin M (u a) = 0) :
    Tendsto (fun t : ℝ => t ^ 2 * secularData g H M t) atTop
      (𝓝 (weightedNorm M⁻¹ g ^ 2)) ∧
    Tendsto lam l atTop ∧
    Tendsto (fun a => lam a * δ a) l (𝓝 (weightedNorm M⁻¹ g)) ∧
    Tendsto (fun a => (lam a / δ a ^ (r - 2)) * δ a ^ (r - 1)) l
      (𝓝 (weightedNorm M⁻¹ g)) ∧
    Tendsto (fun a => (σ a * weightedNorm M (u a) ^ (r - 2)) /
      (σ a ^ (1 / (r - 1)) * weightedNorm M⁻¹ g ^ ((r - 2) / (r - 1)))) k (𝓝 1) ∧
    Tendsto (fun a => (lamhalf a / (δ a / 2) ^ (r - 2)) /
      (lam a / δ a ^ (r - 2))) l (𝓝 ((2 : ℝ) ^ (r - 1))) ∧
    Tendsto (fun a => ((lam a / δ a ^ (r - 2)) * δ a ^ (r - 1)) /
      weightedNorm M⁻¹ g) l (𝓝 1) ∧
    (∀ᶠ a in k, 0 < weightedNorm M (u a) ∧ 0 < σ a ∧
      0 < σ a * weightedNorm M (u a) ^ (r - 2)) := by
  have hb := boundary_radius_weight_limits hM hg r hδ hlam hboundary hstat
  exact ⟨tendsto_mul_sq_secularData hH hM, hb.1, hb.2.1, hb.2.2,
    superquadratic_multiplier_limit hM hg hr hσ hreg,
    halving_radius_weight_limit hM hg r hδ hlam hlamhalf hboundary hhalfboundary
      hstat hhalfstat,
    boundary_weight_fidelity hM hg r hδ hlam hboundary hstat,
    eventually_regularized_positive hM hg r hσ hreg⟩

end CartisGouldToint.Chapter11.Section02
