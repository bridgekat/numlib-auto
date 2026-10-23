import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Optimization.Descent
import Mathlib.Analysis.Calculus.LagrangeMultipliers
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Tactic

/-!
# Global optimality for trust-region quadratic subproblems

The multiplier and shifted semidefiniteness are derived from actual global
minimality. Boundary curvature follows by a sphere reflection and a limit;
interior curvature follows by a small feasible step. No spectral assumption
or second-order optimality certificate is assumed.
-/

open scoped BigOperators Topology
namespace QuadraticOptimality
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual quadratic with linear coefficient g and bounded Hessian H. -/
noncomputable def model (H : E →L[ℝ] E) (g x : E) : ℝ :=
  energyFunctional H.toLinearMap (-g) x

/-- Expand the energy functional as the usual linear-plus-quadratic expression. -/
theorem model_eq (H : E →L[ℝ] E) (g x : E) :
    model H g x = inner ℝ g x + inner ℝ (H x) x / 2 := by
  change inner ℝ (H x) x / 2 - inner ℝ (-g) x = _
  rw [inner_neg_left]
  ring

/-- The exact quadratic increment for a symmetric Hessian. -/
theorem model_add {H : E →L[ℝ] E} (hH : H.toLinearMap.IsSymmetric) (g x v : E) :
    model H g (x + v) - model H g x = 
      inner ℝ (g + H x) v + inner ℝ (H v) v / 2 := by
  have hh := hH.energyFunctional_add (-g) x v
  rw [show H.toLinearMap x - -g = g + H x by simp [add_comm]] at hh
  change model H g (x + v) = _ at hh
  rw [hh]
  change model H g x + inner ℝ (g + H x) v + inner ℝ (H v) v / 2 - model H g x = _
  ring

/-- The exact increment under radial stationarity, separated into the shifted quadratic and the
squared-radius difference. -/
theorem shifted_gap {H : E →L[ℝ] E} (hH : H.toLinearMap.IsSymmetric) (g s v : E)
    {τ : ℝ} (hsolve : g + H s = -τ • s) :
    model H g (s + v) - model H g s = 
      inner ℝ ((H + τ • ContinuousLinearMap.id ℝ E) v) v / 2 -
        τ / 2 * (‖s + v‖ ^ 2 - ‖s‖ ^ 2) := by
  rw [model_add hH, hsolve, norm_add_sq_real]
  simp only [inner_add_left, real_inner_smul_left, add_apply, smul_apply,
    ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq]
  ring

/-- A nonnegative shift, radial stationarity, shifted semidefiniteness and complementarity imply
global minimality on the norm ball. -/
theorem sufficient_trust_region {H : E →L[ℝ] E} (hH : H.toLinearMap.IsSymmetric)
    (g s : E) {τ Δ : ℝ} (hτ : 0 ≤ τ)
    (hsolve : g + H s = -τ • s)
    (hPSD : ∀ v, 0 ≤ inner ℝ ((H + τ • ContinuousLinearMap.id ℝ E) v) v)
    (hcomp : τ * (‖s‖ ^ 2 - Δ ^ 2) = 0) :
    ∀ t : E, ‖t‖ ≤ Δ → model H g s ≤ model H g t := by
  intro t ht
  have hg := shifted_gap hH g s (t - s) hsolve
  rw [add_sub_cancel] at hg
  have hnorm : ‖t‖ ^ 2 ≤ Δ ^ 2 := pow_le_pow_left₀ (norm_nonneg t) ht 2
  have hh : τ * (‖t‖ ^ 2 - ‖s‖ ^ 2) ≤ 0 := by
    have := mul_nonpos_of_nonneg_of_nonpos hτ (by linarith : ‖t‖ ^ 2 - Δ ^ 2 ≤ 0)
    nlinarith
  nlinarith [hPSD (t - s)]

end QuadraticOptimality

namespace QuadraticOptimality
open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual first derivative of the quadratic is represented by g+Hs. -/
theorem hasFDerivAt_model {H : E →L[ℝ] E} (hH : H.toLinearMap.IsSymmetric)
    (g s : E) : HasFDerivAt (model H g) (innerSL ℝ (g + H s)) s := by
  have hh := hasFDerivAt_energyFunctional hH (-g) s
  change HasFDerivAt (energyFunctional H.toLinearMap (-g)) _ s
  simpa only [sub_neg_eq_add, add_comm] using hh

/-- A bounded quadratic has every finite order of continuous differentiability. -/
theorem contDiff_model (H : E →L[ℝ] E) (g : E) (n : ℕ) :
    ContDiff ℝ n (model H g) := by
  change ContDiff ℝ n (fun x : E => inner ℝ (H x) x / 2 - inner ℝ (-g) x)
  exact ((H.contDiff.inner ℝ contDiff_id).div_const 2).sub
    (contDiff_const.inner ℝ contDiff_id)

/-- The quadratic has its actual strict first derivative. -/
theorem hasStrictFDerivAt_model {H : E →L[ℝ] E} (hH : H.toLinearMap.IsSymmetric)
    (g s : E) : HasStrictFDerivAt (model H g) (innerSL ℝ (g + H s)) s :=
  (contDiff_model H g 1).contDiffAt.hasStrictFDerivAt' (hasFDerivAt_model hH g s) (by decide)

/-- At a nonzero global sphere minimizer, the exact quadratic gradient is radial. Derive the
multiplier by the Lagrange multiplier theorem. -/
theorem radial_multiplier_of_sphere_min [CompleteSpace E] {H : E →L[ℝ] E}
    (hH : H.toLinearMap.IsSymmetric) (g s : E) (hs : s ≠ 0)
    (hmin : ∀ t : E, ‖t‖ ^ 2 = ‖s‖ ^ 2 → model H g s ≤ model H g t) :
    ∃ τ : ℝ, g + H s = -τ • s := by
  have hm : IsLocalExtrOn (model H g) {t : E | ‖t‖ ^ 2 = ‖s‖ ^ 2} s :=
    (show IsMinOn (model H g) {t : E | ‖t‖ ^ 2 = ‖s‖ ^ 2} s from hmin).isLocalMinOn.isExtrFilter
  obtain ⟨a, b, hab, hlin⟩ := hm.exists_multipliers_of_hasStrictFDerivAt_1d
    (hasStrictFDerivAt_norm_sq s) (hasStrictFDerivAt_model hH g s)
  have hpair (v : E) : a * (2 * inner ℝ s v) + b * inner ℝ (g + H s) v = 0 := by
    have hh := congrArg (fun f : E →L[ℝ] ℝ => f v) hlin
    simpa only [add_apply, smul_apply, innerSL_apply_apply, smul_eq_mul,
      zero_apply, nsmul_eq_mul, Nat.cast_ofNat] using hh
  have hb : b ≠ 0 := by
    intro hb
    have ha : a ≠ 0 := by
      intro ha
      exact hab (by simp [ha, hb])
    have hh := hpair s
    rw [hb, zero_mul, add_zero, real_inner_self_eq_norm_sq] at hh
    have hn : ‖s‖ ≠ 0 := norm_ne_zero_iff.mpr hs
    exact mul_ne_zero ha (mul_ne_zero (by norm_num) (pow_ne_zero 2 hn)) hh
  refine ⟨2 * a / b, ?_⟩
  have hv (v : E) : inner ℝ (g + H s + (2 * a / b) • s) v = 0 := by
    rw [inner_add_left, real_inner_smul_left]
    have hh := hpair v
    field_simp [hb]
    nlinarith
  have hh := hv (g + H s + (2 * a / b) • s)
  have heq := inner_self_eq_zero.mp hh
  simpa only [neg_smul] using eq_neg_of_add_eq_zero_left heq

end QuadraticOptimality

namespace QuadraticOptimality
open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Reflect across a sphere chord to derive shifted curvature nonnegativity in every direction not
orthogonal to the minimizer. -/
theorem shifted_nonneg_of_nonorthogonal {H : E →L[ℝ] E}
    (hH : H.toLinearMap.IsSymmetric) (g s v : E) {τ : ℝ}
    (hsolve : g + H s = -τ • s)
    (hmin : ∀ t : E, ‖t‖ ^ 2 = ‖s‖ ^ 2 → model H g s ≤ model H g t)
    (hv : inner ℝ s v ≠ 0) :
    0 ≤ inner ℝ ((H + τ • ContinuousLinearMap.id ℝ E) v) v := by
  have hv0 : v ≠ 0 := by intro hh; exact hv (by simp [hh])
  have hn : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hv0)
  let c : ℝ := -2 * inner ℝ s v / ‖v‖ ^ 2
  have hc0 : c ≠ 0 := div_ne_zero (mul_ne_zero (by norm_num) hv) hn
  have hc : c * ‖v‖ ^ 2 = -2 * inner ℝ s v := div_mul_cancel₀ _ hn
  have hnorm : ‖s + c • v‖ ^ 2 = ‖s‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, real_inner_smul_right, mul_pow,
      Real.norm_eq_abs, sq_abs]
    nlinarith [congrArg (fun x : ℝ => c * x) hc]
  have hgap := shifted_gap hH g s (c • v) hsolve
  rw [hnorm, sub_self, mul_zero, sub_zero] at hgap
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right] at hgap
  have hm := hmin (s + c • v) hnorm
  have hp := sq_pos_of_ne_zero hc0
  nlinarith

/-- Continuity extends the reflected-chord curvature test to all directions, including orthogonal
directions. -/
theorem shifted_psd_of_sphere_min {H : E →L[ℝ] E}
    (hH : H.toLinearMap.IsSymmetric) (g s : E) {τ : ℝ}
    (hs : s ≠ 0) (hsolve : g + H s = -τ • s)
    (hmin : ∀ t : E, ‖t‖ ^ 2 = ‖s‖ ^ 2 → model H g s ≤ model H g t) :
    ∀ v, 0 ≤ inner ℝ ((H + τ • ContinuousLinearMap.id ℝ E) v) v := by
  intro v
  by_cases hv : inner ℝ s v ≠ 0
  · exact shifted_nonneg_of_nonorthogonal hH g s v hsolve hmin hv
  have hsv : inner ℝ s v = 0 := not_ne_iff.mp hv
  have hn : 0 < ‖s‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hs)
  have hlim : Tendsto (fun t : ℝ => inner ℝ
      ((H + τ • ContinuousLinearMap.id ℝ E) (v + t • s)) (v + t • s))
      (𝓝[Set.Ioi 0] 0) (𝓝 (inner ℝ ((H + τ • ContinuousLinearMap.id ℝ E) v) v)) := by
    have hh : ContinuousAt (fun t : ℝ => inner ℝ
      ((H + τ • ContinuousLinearMap.id ℝ E) (v + t • s)) (v + t • s)) 0 := by fun_prop
    simpa only [zero_smul, add_zero] using hh.tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  apply shifted_nonneg_of_nonorthogonal hH g s (v + t • s) hsolve hmin
  rw [inner_add_right, real_inner_smul_right, hsv, zero_add, real_inner_self_eq_norm_sq]
  exact ne_of_gt (mul_pos ht hn)

end QuadraticOptimality

namespace QuadraticOptimality
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An interior ball minimizer with zero gradient has a positive-semidefinite quadratic Hessian.
-/
theorem interior_psd {H : E →L[ℝ] E} (hH : H.toLinearMap.IsSymmetric)
    (g s : E) {Δ : ℝ} (hs : ‖s‖ < Δ) (hgrad : g + H s = 0)
    (hmin : ∀ t : E, ‖t‖ ≤ Δ → model H g s ≤ model H g t) :
    ∀ v, 0 ≤ inner ℝ (H v) v := by
  intro v
  let t : ℝ := (Δ - ‖s‖) / (2 * (‖v‖ + 1))
  have ht : 0 < t := div_pos (sub_pos.mpr hs) (by positivity)
  have hbound : t * ‖v‖ ≤ Δ - ‖s‖ := by
    have he : t * (2 * (‖v‖ + 1)) = Δ - ‖s‖ := div_mul_cancel₀ _ (by positivity)
    nlinarith [norm_nonneg v]
  have hfeas : ‖s + t • v‖ ≤ Δ := by
    calc
      ‖s + t • v‖ ≤ ‖s‖ + ‖t • v‖ := norm_add_le _ _
      _ = ‖s‖ + t * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      _ ≤ Δ := by linarith
  have hg := model_add hH g s (t • v)
  rw [hgrad, inner_zero_left, zero_add] at hg
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right] at hg
  have hm := hmin (s + t • v) hfeas
  have := sq_pos_of_pos ht
  nlinarith

/-- Every feasible global minimizer on a positive-radius ball admits a nonnegative radial
multiplier, shifted semidefiniteness, and complementarity. Include both boundary and interior
cases. -/
theorem necessary_trust_region [CompleteSpace E] {H : E →L[ℝ] E}
    (hH : H.toLinearMap.IsSymmetric) (g s : E) {Δ : ℝ} (hΔ : 0 < Δ)
    (hs : ‖s‖ ≤ Δ)
    (hmin : ∀ t : E, ‖t‖ ≤ Δ → model H g s ≤ model H g t) :
    ∃ τ : ℝ, 0 ≤ τ ∧ g + H s = -τ • s ∧
      (∀ v, 0 ≤ inner ℝ ((H + τ • ContinuousLinearMap.id ℝ E) v) v) ∧
      τ * (‖s‖ ^ 2 - Δ ^ 2) = 0 := by
  by_cases hboundary : ‖s‖ = Δ
  · have hs0 : s ≠ 0 := by intro hh; simpa [hh] using hboundary.trans_gt hΔ
    have hsphere : ∀ t : E, ‖t‖ ^ 2 = ‖s‖ ^ 2 → model H g s ≤ model H g t := by
      intro t ht
      apply hmin t
      have := sq_le_sq₀ (norm_nonneg t) (norm_nonneg s)
      have hn : ‖t‖ ≤ ‖s‖ := this.mp (le_of_eq ht)
      exact hn.trans hs
    obtain ⟨τ, hsolve⟩ := radial_multiplier_of_sphere_min hH g s hs0 hsphere
    have hlocal : IsLocalMinOn (model H g) (Metric.closedBall 0 Δ) s :=
      (show IsMinOn (model H g) (Metric.closedBall 0 Δ) s from
        fun t ht => hmin t
          (by simpa only [Metric.mem_closedBall, dist_zero_right] using ht)).isLocalMinOn
    have hv := Descent.fderiv_apply_sub_nonneg_of_isLocalMinOn
      (f' := fun x => innerSL ℝ (g + H x))
      (convex_closedBall (0:E) Δ) (by simpa using hs) hlocal
      (hasFDerivAt_model hH g s) 0 (by simpa using hΔ.le)
    simp only [zero_sub, innerSL_apply_apply, hsolve, inner_neg_right,
      real_inner_smul_left, real_inner_self_eq_norm_sq] at hv
    have hτ : 0 ≤ τ := by
      have hp := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hs0)
      nlinarith
    exact ⟨τ, hτ, hsolve, shifted_psd_of_sphere_min hH g s hs0 hsolve hsphere,
      by rw [hboundary]; ring⟩
  · have hinterior : ‖s‖ < Δ := lt_of_le_of_ne hs hboundary
    have hm : IsLocalMin (model H g) s :=
      (show IsMinOn (model H g) (Metric.closedBall 0 Δ) s from
        fun t ht => hmin t
          (by simpa only [Metric.mem_closedBall, dist_zero_right] using ht)).isLocalMin
          (Metric.closedBall_mem_nhds_of_mem (by simpa using hinterior))
    have hz := congrArg (fun f : E →L[ℝ] ℝ => f (g + H s))
      (hm.hasFDerivAt_eq_zero (hasFDerivAt_model hH g s))
    have hgrad : g + H s = 0 := inner_self_eq_zero.mp
      (by simpa only [innerSL_apply_apply, zero_apply] using hz)
    refine ⟨0, le_rfl, by simpa using hgrad, ?_, by simp⟩
    simpa only [zero_smul, add_zero] using interior_psd hH g s hinterior hgrad hmin

end QuadraticOptimality

namespace QuadraticOptimality
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The nonnegative multiplier certificate is equivalent to actual global minimality on a
positive-radius ball, for every feasible point. -/
theorem trust_region_iff [CompleteSpace E] {H : E →L[ℝ] E}
    (hH : H.toLinearMap.IsSymmetric) (g s : E) {Δ : ℝ} (hΔ : 0 < Δ) (hs : ‖s‖ ≤ Δ) :
    (∀ t : E, ‖t‖ ≤ Δ → model H g s ≤ model H g t) ↔
    ∃ τ : ℝ, 0 ≤ τ ∧ g + H s = -τ • s ∧
      (∀ v, 0 ≤ inner ℝ ((H + τ • ContinuousLinearMap.id ℝ E) v) v) ∧
      τ * (‖s‖ ^ 2 - Δ ^ 2) = 0 := by
  constructor
  · exact necessary_trust_region hH g s hΔ hs
  · rintro ⟨τ, hτ, hsolve, hPSD, hcomp⟩
    exact sufficient_trust_region hH g s hτ hsolve hPSD hcomp

/-- Positive definiteness of the shifted Hessian makes a feasible global minimizer unique. -/
theorem unique_trust_region {H : E →L[ℝ] E} (hH : H.toLinearMap.IsSymmetric)
    (g s : E) {τ Δ : ℝ} (hτ : 0 ≤ τ)
    (hsolve : g + H s = -τ • s)
    (hPD : ∀ v, v ≠ 0 → 0 < inner ℝ ((H + τ • ContinuousLinearMap.id ℝ E) v) v)
    (hcomp : τ * (‖s‖ ^ 2 - Δ ^ 2) = 0) :
    ∀ t : E, ‖t‖ ≤ Δ → model H g t ≤ model H g s → t = s := by
  intro t ht hm
  by_contra hne
  have hp := hPD (t - s) (sub_ne_zero.mpr hne)
  have hg := shifted_gap hH g s (t - s) hsolve
  rw [add_sub_cancel] at hg
  have hnorm : ‖t‖ ^ 2 ≤ Δ ^ 2 := pow_le_pow_left₀ (norm_nonneg t) ht 2
  have hh : τ * (‖t‖ ^ 2 - ‖s‖ ^ 2) ≤ 0 := by
    have := mul_nonpos_of_nonneg_of_nonpos hτ (by linarith : ‖t‖ ^ 2 - Δ ^ 2 ≤ 0)
    nlinarith
  nlinarith

end QuadraticOptimality

