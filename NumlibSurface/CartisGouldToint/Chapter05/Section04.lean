import Numlib.Optimization.LocalCurvature
import NumlibSurface.CartisGouldToint.Chapter03.Section03

/-!
# Chapter 5, Section 4: the local convexity region

The source's closed ball and the smaller gradient region use the actual least Hessian
curvature at the reference minimizer. The constants in (5.4.5) are definitions: no quadratic
convergence conclusion is assumed. When its last denominator vanishes, that bound is omitted.
The remaining phase-convergence and iteration-count statements retain their full plans.
-/

noncomputable section
namespace CartisGouldToint.Chapter05.Section04
open Optimization

variable {n : ℕ}

/-- The radius q_* in (5.4.1), for the actual reference Hessian. -/
def localConvexityRadius (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (xstar : EuclideanSpace ℝ (Fin n)) (L : ℝ) : ℝ :=
  leastCurvature (fderiv ℝ (fderiv ℝ f) xstar) / (4 * L)

/-- The closed local convexity region Q_* in (5.4.1). -/
def localConvexityRegion (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (xstar : EuclideanSpace ℝ (Fin n)) (L : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  Metric.closedBall xstar (localConvexityRadius f xstar L)

/-- Membership in Q_* is the stated displacement norm bound. -/
@[simp] theorem mem_localConvexityRegion {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {xstar x : EuclideanSpace ℝ (Fin n)} {L : ℝ} :
    x ∈ localConvexityRegion f xstar L ↔ ‖x - xstar‖ ≤ localConvexityRadius f xstar L := by
  simp [localConvexityRegion, dist_eq_norm]

/-- Positive reference curvature and L>0 give a positive local radius. -/
theorem localConvexityRadius_pos {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {xstar : EuclideanSpace ℝ (Fin n)} {L : ℝ} (hL : 0 < L)
    (hstar : 0 < leastCurvature (fderiv ℝ (fderiv ℝ f) xstar)) :
    0 < localConvexityRadius f xstar L := by
  exact div_pos hstar (by positivity)

/-- Q_* is a neighborhood of its reference point under the positive-curvature assumptions. -/
theorem localConvexityRegion_mem_nhds {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {xstar : EuclideanSpace ℝ (Fin n)} {L : ℝ} (hL : 0 < L)
    (hstar : 0 < leastCurvature (fderiv ℝ (fderiv ℝ f) xstar)) :
    localConvexityRegion f xstar L ∈ nhds xstar :=
  Metric.closedBall_mem_nhds xstar (localConvexityRadius_pos hL hstar)

/-- The common positive factor in the source's five threshold bounds (5.4.5). -/
def phaseCurvatureScale (lambda theta sigmaMin : ℝ) : ℝ :=
  (lambda + sigmaMin / 2) / (1 + theta)

/-- The first four finite bounds in (5.4.5). -/
def phaseBaseThreshold (lambda L theta sigmaMin sigmaMax eta2 : ℝ) : ℝ :=
  min (2 / (L + theta + sigmaMax) * phaseCurvatureScale lambda theta sigmaMin ^ 2)
    (min (lambda / (4 * L) * phaseCurvatureScale lambda theta sigmaMin)
      (min (lambda ^ 2 / (16 * L))
        (3 * (1 - eta2) * lambda / (4 * L) * phaseCurvatureScale lambda theta sigmaMin)))

/-- The threshold zeta_* in (5.4.5); a zero last denominator imposes no upper bound. -/
def phaseGradientThreshold (lambda L theta sigmaMin sigmaMax eta2 : ℝ) : ℝ :=
  if theta ≤ sigmaMin then phaseBaseThreshold lambda L theta sigmaMin sigmaMax eta2
  else min (phaseBaseThreshold lambda L theta sigmaMin sigmaMax eta2)
    (lambda / (4 * (theta - sigmaMin)) * phaseCurvatureScale lambda theta sigmaMin)

/-- If theta≤sigma_min, the last source bound is absent. -/
theorem phaseGradientThreshold_of_le {lambda L theta sigmaMin sigmaMax eta2 : ℝ}
    (h : theta ≤ sigmaMin) :
    phaseGradientThreshold lambda L theta sigmaMin sigmaMax eta2 =
      phaseBaseThreshold lambda L theta sigmaMin sigmaMax eta2 := ite_eq_left h

/-- If theta>sigma_min, the last bound has a strictly positive denominator. -/
theorem phaseGradientThreshold_of_lt {lambda L theta sigmaMin sigmaMax eta2 : ℝ}
    (h : sigmaMin < theta) :
    phaseGradientThreshold lambda L theta sigmaMin sigmaMax eta2 =
      min (phaseBaseThreshold lambda L theta sigmaMin sigmaMax eta2)
        (lambda / (4 * (theta - sigmaMin)) * phaseCurvatureScale lambda theta sigmaMin) :=
  ite_eq_right (not_le.mpr h)

/-- The common factor in the source threshold is positive for admissible parameters. -/
theorem phaseCurvatureScale_pos {lambda theta sigmaMin : ℝ}
    (hlambda : 0 < lambda) (htheta : 0 ≤ theta) (hmin : 0 ≤ sigmaMin) :
    0 < phaseCurvatureScale lambda theta sigmaMin := by
  unfold phaseCurvatureScale
  positivity

/-- The first four bounds define a positive threshold for admissible parameters. -/
theorem phaseBaseThreshold_pos {lambda L theta sigmaMin sigmaMax eta2 : ℝ}
    (hlambda : 0 < lambda) (hL : 0 < L) (htheta : 0 ≤ theta)
    (hmin : 0 ≤ sigmaMin) (hmax : 0 ≤ sigmaMax) (heta : eta2 < 1) :
    0 < phaseBaseThreshold lambda L theta sigmaMin sigmaMax eta2 := by
  have hs := phaseCurvatureScale_pos hlambda htheta hmin
  unfold phaseBaseThreshold
  positivity

/-- Omitting a vacuous bound preserves strict positivity, including theta=sigma_min. -/
theorem phaseGradientThreshold_pos {lambda L theta sigmaMin sigmaMax eta2 : ℝ}
    (hlambda : 0 < lambda) (hL : 0 < L) (htheta : 0 ≤ theta)
    (hmin : 0 ≤ sigmaMin) (hmax : 0 ≤ sigmaMax) (heta : eta2 < 1) :
    0 < phaseGradientThreshold lambda L theta sigmaMin sigmaMax eta2 := by
  have hb := phaseBaseThreshold_pos hlambda hL htheta hmin hmax heta
  have hs := phaseCurvatureScale_pos hlambda htheta hmin
  unfold phaseGradientThreshold
  split_ifs with h
  · exact hb
  · have hd : 0 < theta - sigmaMin := sub_pos.mpr (lt_of_not_ge h)
    exact lt_min hb (mul_pos (div_pos hlambda (by positivity)) hs)

/-- The smaller local region Q_*^1 in (5.4.6), with actual objective gradient. -/
def quadraticConvergenceRegion (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (xstar : EuclideanSpace ℝ (Fin n)) (L theta sigmaMin sigmaMax eta2 : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  localConvexityRegion f xstar L ∩ {x | ‖gradient f x‖ ≤
    phaseGradientThreshold (leastCurvature (fderiv ℝ (fderiv ℝ f) xstar))
      L theta sigmaMin sigmaMax eta2}

/-- Q_*^1 requires both the source radius and its source gradient threshold. -/
@[simp] theorem mem_quadraticConvergenceRegion {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {xstar x : EuclideanSpace ℝ (Fin n)} {L theta sigmaMin sigmaMax eta2 : ℝ} :
    x ∈ quadraticConvergenceRegion f xstar L theta sigmaMin sigmaMax eta2 ↔
      x ∈ localConvexityRegion f xstar L ∧ ‖gradient f x‖ ≤
        phaseGradientThreshold (leastCurvature (fderiv ℝ (fderiv ℝ f) xstar))
          L theta sigmaMin sigmaMax eta2 := Iff.rfl

/-- The smaller gradient region lies in the local convexity region. -/
theorem quadraticConvergenceRegion_subset (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (xstar : EuclideanSpace ℝ (Fin n)) (L theta sigmaMin sigmaMax eta2 : ℝ) :
    quadraticConvergenceRegion f xstar L theta sigmaMin sigmaMax eta2 ⊆
      localConvexityRegion f xstar L := Set.inter_subset_left

/-- The reference minimizer belongs to Q_*^1 for all admissible phase parameters. -/
theorem reference_mem_quadraticConvergenceRegion
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {xstar : EuclideanSpace ℝ (Fin n)}
    {L theta sigmaMin sigmaMax eta2 : ℝ}
    (hf : Chapter03.Section01.hessianLipschitz f L) (hmin : IsLocalMin f xstar)
    (hstar : 0 < leastCurvature (fderiv ℝ (fderiv ℝ f) xstar))
    (htheta : 0 ≤ theta) (hsmin : 0 ≤ sigmaMin) (hsmax : 0 ≤ sigmaMax)
    (heta : eta2 < 1) :
    xstar ∈ quadraticConvergenceRegion f xstar L theta sigmaMin sigmaMax eta2 := by
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hf.one_le
  have hg : gradient f xstar = 0 :=
    (Chapter01.Section01.theorem_1_1_1 f xstar).1
      (hf.smooth.of_le (by norm_num)) hmin
  rw [mem_quadraticConvergenceRegion, mem_localConvexityRegion, sub_self, norm_zero,
    hg, norm_zero]
  exact ⟨(localConvexityRadius_pos hL hstar).le,
    (phaseGradientThreshold_pos hstar hL htheta hsmin hsmax heta).le⟩

/-- Lemma 5.4.1: on Q_*, the actual Hessian has at least half the reference curvature.
The source convention L≥1 ensures a positive denominator; local minimality is retained. -/
theorem lemma_5_4_1 [NeZero n] {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {xstar x : EuclideanSpace ℝ (Fin n)} {L : ℝ}
    (hf : Chapter03.Section01.hessianLipschitz f L)
    (_hmin : IsLocalMin f xstar)
    (hstar : 0 < leastCurvature (fderiv ℝ (fderiv ℝ f) xstar))
    (hx : x ∈ localConvexityRegion f xstar L) :
    leastCurvature (fderiv ℝ (fderiv ℝ f) xstar) / 2 ≤
      leastCurvature (fderiv ℝ (fderiv ℝ f) x) := by
  have hL := hf.one_le
  apply hf.toHessianLipschitz.leastCurvature_ge_half (by linarith) xstar
  have hden : 0 < L := by linarith
  have hrad : localConvexityRadius f xstar L ≤
      leastCurvature (fderiv ℝ (fderiv ℝ f) xstar) / (2 * L) := by
    unfold localConvexityRadius
    apply div_le_div_of_nonneg_left hstar.le (by positivity)
    linarith
  exact Metric.closedBall_subset_closedBall hrad hx

end CartisGouldToint.Chapter05.Section04
