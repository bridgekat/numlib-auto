import Numlib.Analysis.Calculus.TaylorModel
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Asymptotics.Ring
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-!
# First-order necessary optimality for convex composite objectives

The composite Taylor model retains the possibly nonsmooth outer function and expands
only the smooth scalar and residual maps. At a minimum of the true objective, its convex
first-order model is minimized at zero. Lipschitz continuity of the outer function controls
the linearization error; subadditivity of the outer function is unnecessary.
-/

open Set Filter Asymptotics
open scoped Topology

namespace Composite
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The generalized composite Taylor model, retaining the entire outer function. -/
noncomputable def taylorModel (f : E → ℝ) (c : E → F) (h : F → ℝ)
    (p : ℕ) (x s : E) : ℝ :=
  TaylorModel.eval f p x s + h (TaylorModel.eval c p x s)

/-- The composite model is exact at zero displacement. -/
@[simp] theorem taylorModel_zero (f : E → ℝ) (c : E → F) (h : F → ℝ)
    (p : ℕ) (x : E) : taylorModel f c h p x 0 = f x + h (c x) := by
  simp [taylorModel]

/-- The degree-one composite model uses the actual first derivatives. -/
theorem taylorModel_one (f : E → ℝ) (c : E → F) (h : F → ℝ) (x s : E) :
    taylorModel f c h 1 x s =
      f x + fderiv ℝ f x s + h (c x + fderiv ℝ c x s) := by
  simp [taylorModel, TaylorModel.eval_eq_sum, Finset.sum_range_succ,
    iteratedFDeriv_one_apply]

/-- A minimum of a Lipschitz convex composite objective minimizes its genuine
first-order model globally. Only differentiability at the point is needed. -/
theorem linearized_isMinOn_of_isMinOn {f : E → ℝ} {c : E → F} {h : F → ℝ}
    {f' : E →L[ℝ] ℝ} {c' : E →L[ℝ] F} {x : E} {K : NNReal}
    (hf : HasFDerivAt f f' x) (hc : HasFDerivAt c c' x)
    (hh : LipschitzWith K h) (hconv : ConvexOn ℝ univ h)
    (hmin : IsMinOn (fun z => f z + h (c z)) univ x) :
    ∀ s : E, f x + h (c x) ≤ f x + f' s + h (c x + c' s) := by
  intro s
  by_contra hnot
  have hgap : 0 < f x + h (c x) - (f x + f' s + h (c x + c' s)) :=
    sub_pos.mpr (lt_of_not_ge hnot)
  let a := f x + h (c x) - (f x + f' s + h (c x + c' s))
  have hline : HasDerivAt (fun t : ℝ => x + t • s) s 0 := by
    simpa only [Pi.add_def, id_eq, zero_add, one_smul] using
      (hasDerivAt_const (0 : ℝ) x).add ((hasDerivAt_id (0 : ℝ)).smul_const s)
  have hrf : (fun t : ℝ => f (x + t • s) - f x - t * f' s) =o[𝓝 0] (fun t => t) := by
    simpa using (hf.comp_hasDerivAt_of_eq 0 hline (by simp)).isLittleO
  have hrc : (fun t : ℝ => c (x + t • s) - c x - t • c' s) =o[𝓝 0] (fun t => t) := by
    simpa using (hc.comp_hasDerivAt_of_eq 0 hline (by simp)).isLittleO
  have herr : (fun t : ℝ => ‖f (x + t • s) - f x - t * f' s‖ +
      (K : ℝ) * ‖c (x + t • s) - c x - t • c' s‖) =o[𝓝 0] (fun t => t) :=
    hrf.norm_left.add (hrc.norm_left.const_mul_left (K : ℝ))
  have hsmall := herr.bound (show 0 < a / 2 by dsimp [a]; positivity)
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Ioo 0 1 := Ioo_mem_nhdsGT (by norm_num)
  obtain ⟨t, ht, he⟩ := (hpos.and (hsmall.filter_mono nhdsWithin_le_nhds)).exists
  have he' : ‖f (x + t • s) - f x - t * f' s‖ +
      (K : ℝ) * ‖c (x + t • s) - c x - t • c' s‖ ≤ a / 2 * t := by
    simpa only [Real.norm_of_nonneg (add_nonneg (norm_nonneg _)
      (mul_nonneg K.coe_nonneg (norm_nonneg _))), Real.norm_of_nonneg ht.1.le] using he
  have hcv := hconv.2 (mem_univ (c x)) (mem_univ (c x + c' s))
    (show 0 ≤ 1 - t by linarith [ht.2]) ht.1.le (by ring : 1 - t + t = 1)
  have hpoint : (1 - t) • c x + t • (c x + c' s) = c x + t • c' s := by module
  rw [hpoint] at hcv
  simp only [smul_eq_mul] at hcv
  have hl := hh.dist_le_mul (c (x + t • s)) (c x + t • c' s)
  rw [Real.dist_eq, dist_eq_norm] at hl
  have hsub : c (x + t • s) - (c x + t • c' s) =
      c (x + t • s) - c x - t • c' s := by abel
  rw [hsub] at hl
  have houter : h (c (x + t • s)) ≤ h (c x + t • c' s) +
      (K : ℝ) * ‖c (x + t • s) - c x - t • c' s‖ := by
    linarith [(le_abs_self (h (c (x + t • s)) - h (c x + t • c' s))).trans hl]
  have hferror := le_abs_self (f (x + t • s) - f x - t * f' s)
  have htrue := hmin (mem_univ (x + t • s))
  change f x + h (c x) ≤ f (x + t • s) + h (c (x + t • s)) at htrue
  have hprod := mul_pos hgap ht.1
  dsimp [a] at he'
  nlinarith

/-- A true composite minimum gives a global minimum of the degree-one model at zero. -/
theorem taylorModel_one_isMinOn_of_isMinOn {f : E → ℝ} {c : E → F} {h : F → ℝ}
    {x : E} {K : NNReal} (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x)
    (hh : LipschitzWith K h) (hconv : ConvexOn ℝ univ h)
    (hmin : IsMinOn (fun z => f z + h (c z)) univ x) :
    IsMinOn (taylorModel f c h 1 x) univ 0 := by
  intro s _
  change taylorModel f c h 1 x 0 ≤ taylorModel f c h 1 x s
  rw [taylorModel_zero, taylorModel_one]
  exact linearized_isMinOn_of_isMinOn hf.hasFDerivAt hc.hasFDerivAt hh hconv hmin s

/-- Composite criticality is the supremum of the actual generalized Taylor decrement
on the displacement ball. The nonsmooth outer function remains unexpanded. -/
noncomputable def criticality (f : E → ℝ) (c : E → F) (h : F → ℝ)
    (p : ℕ) (x : E) (δ : ℝ) : ℝ :=
  sSup ((fun s => taylorModel f c h p x 0 - taylorModel f c h p x s) ''
    Metric.closedBall 0 δ)

/-- A continuous outer function makes the composite Taylor model continuous. -/
theorem continuous_taylorModel (f : E → ℝ) (c : E → F) {h : F → ℝ}
    (hh : Continuous h) (p : ℕ) (x : E) : Continuous (taylorModel f c h p x) := by
  unfold taylorModel TaylorModel.eval TaylorModel.ofJet
  exact (FormalMultilinearSeries.partialSum_continuous _ _).add
    (hh.comp (FormalMultilinearSeries.partialSum_continuous _ _))

/-- In a proper space the composite criticality is an attained maximum. -/
theorem exists_decrement_eq_criticality [ProperSpace E] (f : E → ℝ) (c : E → F)
    {h : F → ℝ} (hh : Continuous h) (p : ℕ) (x : E) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ s : E, ‖s‖ ≤ δ ∧ taylorModel f c h p x 0 - taylorModel f c h p x s =
      criticality f c h p x δ := by
  obtain ⟨s, hs, heq⟩ := (isCompact_closedBall (0 : E) δ).exists_sSup_image_eq
    ⟨0, by simpa using hδ⟩ (continuous_const.sub (continuous_taylorModel f c hh p x)).continuousOn
  exact ⟨s, by simpa using hs, heq.symm⟩

/-- Every feasible model decrement lies below the actual composite criticality. -/
theorem decrement_le_criticality [ProperSpace E] (f : E → ℝ) (c : E → F)
    {h : F → ℝ} (hh : Continuous h) (p : ℕ) (x : E) {δ : ℝ} {s : E} (hs : ‖s‖ ≤ δ) :
    taylorModel f c h p x 0 - taylorModel f c h p x s ≤ criticality f c h p x δ := by
  exact le_csSup ((isCompact_closedBall (0 : E) δ).image
    (continuous_const.sub (continuous_taylorModel f c hh p x))).bddAbove
      ⟨s, by simpa using hs, rfl⟩

/-- Zero displacement makes composite criticality nonnegative. -/
theorem criticality_nonneg [ProperSpace E] (f : E → ℝ) (c : E → F)
    {h : F → ℝ} (hh : Continuous h) (p : ℕ) (x : E) {δ : ℝ} (hδ : 0 ≤ δ) :
    0 ≤ criticality f c h p x δ := by
  simpa using decrement_le_criticality f c hh p x (s := 0) (by simpa using hδ)

/-- A globally minimal zero displacement makes composite criticality vanish at every
nonnegative radius. This uses the actual supremum and the feasible zero displacement. -/
theorem criticality_eq_zero_of_model_min (f : E → ℝ) (c : E → F) (h : F → ℝ)
    (p : ℕ) (x : E) {δ : ℝ} (hδ : 0 ≤ δ)
    (hmin : IsMinOn (taylorModel f c h p x) univ 0) : criticality f c h p x δ = 0 := by
  let A := (fun s => taylorModel f c h p x 0 - taylorModel f c h p x s) ''
    Metric.closedBall 0 δ
  have hzero : (0 : ℝ) ∈ A := by
    exact ⟨0, by simpa using hδ, sub_self _⟩
  have hmax : IsGreatest A 0 := by
    refine ⟨hzero, ?_⟩
    rintro a ⟨s, _, rfl⟩
    exact sub_nonpos.mpr (hmin (mem_univ s))
  exact hmax.isLUB.csSup_eq ⟨0, hzero⟩

end Composite
