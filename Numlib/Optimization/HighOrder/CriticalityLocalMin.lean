import Numlib.Optimization.HighOrder.Criticality
import Numlib.Analysis.Calculus.TaylorModel.Peano
import Numlib.Optimization.Unconstrained.Optimality

/-!
# Taylor criticality at local minima

First- and second-order criticality vanish at local minima under the corresponding
regularity. At every positive finite order, criticality divided by the radius to that
order tends to zero as the positive radius tends to zero. The proof uses the actual
Taylor polynomial and the Peano remainder derived from precisely `C^k` smoothness.
-/

open Set
open Filter
open scoped Topology
namespace TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
/-- Near a local minimum, the degree-`k` criticality is uniformly small relative to the
radius power. Compactness gives a maximizing displacement, to which the uniform Peano
bound and the local minimizing inequality both apply. -/
theorem exists_pos_criticality_le_mul_pow {f : E → ℝ} {k : ℕ} (hk : 0 < k)
    (hf : ContDiff ℝ k f) {x : E} (hmin : IsLocalMin f x) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ δ : ℝ, 0 ≤ δ → δ < r → criticality f k x δ ≤ ε * δ ^ k := by
  obtain ⟨rR,hrR,hR⟩ := exists_pos_abs_sub_eval_le hk hf x hε
  obtain ⟨rL,hrL,hL⟩ := Metric.eventually_nhds_iff.1 hmin
  refine ⟨min rR rL, lt_min hrR hrL, ?_⟩
  intro δ hδ hδr
  obtain ⟨s,hs,heq⟩ := exists_decrement_eq_criticality f k x hδ
  have hsR : ‖s‖ < rR := hs.trans_lt (hδr.trans_le (min_le_left _ _))
  have hsL : dist (x + s) x < rL := by
    rw [dist_eq_norm, add_sub_cancel_left]
    exact hs.trans_lt (hδr.trans_le (min_le_right _ _))
  have hlocal := hL hsL
  have herr := (abs_le.1 (hR s hsR)).2
  have hpow : ε * ‖s‖ ^ k ≤ ε * δ ^ k := by gcongr
  rw [← heq, decrement_eq]
  linarith
/-- At a local minimum, Taylor criticality divided by the radius power tends to zero
as the positive radius tends to zero. The Peano estimate is derived from `C^k` regularity. -/
theorem tendsto_criticality_div_pow {f : E → ℝ} {k : ℕ} (hk : 0 < k)
    (hf : ContDiff ℝ k f) {x : E} (hmin : IsLocalMin f x) :
    Tendsto (fun δ : ℝ => criticality f k x δ / δ ^ k) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨r,hr,hbound⟩ := exists_pos_criticality_le_mul_pow hk hf hmin (half_pos hε)
  have hsmall : ∀ᶠ δ : ℝ in nhdsWithin 0 (Ioi 0), δ < r :=
    (eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with δ hδ hδr
  have hδ0 : 0 < δ := hδ
  have hnonneg : 0 ≤ criticality f k x δ / δ ^ k :=
    div_nonneg (criticality_nonneg f k x hδ0.le) (pow_nonneg hδ0.le k)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  have hratio : criticality f k x δ / δ ^ k ≤ ε / 2 :=
    (div_le_iff₀ (pow_pos hδ0 k)).2 (hbound δ hδ0.le hδr)
  linarith
end TaylorModel
namespace TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
/-- First-order Taylor criticality vanishes at a local minimum. -/
theorem criticality_one_eq_zero_of_isLocalMin {f : E → ℝ} {x : E}
    (hmin : IsLocalMin f x) {δ : ℝ} (hδ : 0 ≤ δ) : criticality f 1 x δ = 0 := by
  apply (criticality_eq_zero_iff f 1 x hδ).2
  intro s _
  rw [decrement_eq, eval_eq_sum]
  simp [Finset.sum_range_succ, iteratedFDeriv_one_apply, hmin.fderiv_eq_zero]
/-- Second-order Taylor criticality vanishes at a `C²` local minimum. -/
theorem criticality_two_eq_zero_of_isLocalMin {f : E → ℝ} {x : E}
    (hf : ContDiff ℝ 2 f) (hmin : IsLocalMin f x) {δ : ℝ} (hδ : 0 ≤ δ) :
    criticality f 2 x δ = 0 := by
  apply (criticality_eq_zero_iff f 2 x hδ).2
  intro s _
  have h1 : iteratedFDeriv ℝ 1 f x (fun _ => s) = 0 := by
    simp [iteratedFDeriv_one_apply, hmin.fderiv_eq_zero]
  have h2 : 0 ≤ iteratedFDeriv ℝ 2 f x (fun _ => s) := by
    simpa [iteratedFDeriv_two_apply] using Descent.hessian_nonneg_of_isLocalMin hmin hf s
  have hexp := eval_two f x s
  rw [decrement_eq]
  linarith
end TaylorModel
