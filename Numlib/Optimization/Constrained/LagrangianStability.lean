import Numlib.Optimization.HighOrder.RestrictedCriticality
import Mathlib.Analysis.InnerProductSpace.Calculus
/-!
# Objective stability from actual Lagrangian Taylor criticality

The true multiplier functional controls all Lagrangian derivative errors.
The augmented multiplier norm gives the exact square-root-two Lipschitz
coefficient; a local Taylor bound then transfers to objective stability with
the precise loss from approximate equality feasibility.
-/

namespace Constrained
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
/-- The actual vector equality Lagrangian, with the minus-multiplier convention. -/
noncomputable def vectorLagrangian (f : E → ℝ) (c : E → F) (y : F) : E → ℝ :=
  fun x => f x - inner ℝ y (c x)
/-- The Euclidean norm of the augmented multiplier vector `(1,y)`. -/
noncomputable def multiplierNorm (y : F) : ℝ := Real.sqrt (1 + ‖y‖ ^ 2)
omit [InnerProductSpace ℝ F] in
/-- The augmented multiplier norm is strictly positive, including at zero multiplier. -/
theorem multiplierNorm_pos (y : F) : 0 < multiplierNorm y := by unfold multiplierNorm; positivity
omit [InnerProductSpace ℝ F] in
/-- The sum of the two multiplier weights is at most the augmented norm times square root two. -/
theorem one_add_norm_le_sqrt_two_mul_multiplierNorm (y : F) :
    1 + ‖y‖ ≤ Real.sqrt 2 * multiplierNorm y := by
  have hm : (multiplierNorm y) ^ 2 = 1 + ‖y‖ ^ 2 := Real.sq_sqrt (by positivity)
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp := multiplierNorm_pos y
  have hsp : 0 ≤ Real.sqrt 2 * multiplierNorm y := by positivity
  nlinarith [sq_nonneg (‖y‖ - 1), sq_nonneg (Real.sqrt 2 * multiplierNorm y)]
/-- Smooth objective and constraint maps give a smooth actual Lagrangian. -/
theorem contDiffOn_vectorLagrangian {f : E → ℝ} {c : E → F} {j : ℕ} {D : Set E}
    (hf : ContDiffOn ℝ j f D) (hc : ContDiffOn ℝ j c D) (y : F) :
    ContDiffOn ℝ j (vectorLagrangian f c y) D := by
  exact hf.sub ((innerSL ℝ y).contDiff.comp_contDiffOn hc)
/-- Actual objective and constraint derivative errors control the actual Lagrangian derivative
error. -/
theorem norm_iteratedFDeriv_vectorLagrangian_sub_le {f : E → ℝ} {c : E → F}
    {j : ℕ} {D : Set E} (hD : IsOpen D) (hf : ContDiffOn ℝ j f D)
    (hc : ContDiffOn ℝ j c D) (y : F) {u v : E} (hu : u ∈ D) (hv : v ∈ D)
    {Lf Lc : ℝ} (hLf : 0 ≤ Lf) (_hLc : 0 ≤ Lc)
    (hlf : ‖iteratedFDeriv ℝ j f u - iteratedFDeriv ℝ j f v‖ ≤ Lf * ‖u - v‖)
    (hlc : ‖iteratedFDeriv ℝ j c u - iteratedFDeriv ℝ j c v‖ ≤ Lc * ‖u - v‖) :
    ‖iteratedFDeriv ℝ j (vectorLagrangian f c y) u -
      iteratedFDeriv ℝ j (vectorLagrangian f c y) v‖ ≤
      (Real.sqrt 2 * max Lf Lc * multiplierNorm y) * ‖u - v‖ := by
  let L := innerSL ℝ y
  have hfu := hf.contDiffAt (hD.mem_nhds hu)
  have hfv := hf.contDiffAt (hD.mem_nhds hv)
  have hcu := hc.contDiffAt (hD.mem_nhds hu)
  have hcv := hc.contDiffAt (hD.mem_nhds hv)
  have hder : ∀ z ∈ D, iteratedFDeriv ℝ j (vectorLagrangian f c y) z =
      iteratedFDeriv ℝ j f z - L.compContinuousMultilinearMap (iteratedFDeriv ℝ j c z) := by
    intro z hz
    have hfz := hf.contDiffAt (hD.mem_nhds hz)
    have hcz := hc.contDiffAt (hD.mem_nhds hz)
    change iteratedFDeriv ℝ j (f - L ∘ c) z = _
    rw [iteratedFDeriv_sub_apply hfz (L.contDiff.contDiffAt.comp z hcz),
      L.iteratedFDeriv_comp_left hcz le_rfl]
  rw [hder u hu, hder v hv]
  have he : (iteratedFDeriv ℝ j f u - L.compContinuousMultilinearMap
      (iteratedFDeriv ℝ j c u)) - (iteratedFDeriv ℝ j f v -
      L.compContinuousMultilinearMap (iteratedFDeriv ℝ j c v)) =
      (iteratedFDeriv ℝ j f u - iteratedFDeriv ℝ j f v) -
      L.compContinuousMultilinearMap (iteratedFDeriv ℝ j c u - iteratedFDeriv ℝ j c v) := by
    ext w
    simp only [sub_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply, map_sub]
    ring
  rw [he]
  have hn := L.norm_compContinuousMultilinearMap_le
    (iteratedFDeriv ℝ j c u - iteratedFDeriv ℝ j c v)
  rw [show ‖L‖ = ‖y‖ from by simp only [L, innerSL_apply_norm]] at hn
  have h1 := norm_sub_le (iteratedFDeriv ℝ j f u - iteratedFDeriv ℝ j f v)
    (L.compContinuousMultilinearMap (iteratedFDeriv ℝ j c u - iteratedFDeriv ℝ j c v))
  have h2 := mul_le_mul_of_nonneg_left hlc (norm_nonneg y)
  have hbase : Lf + ‖y‖ * Lc ≤ max Lf Lc * (1 + ‖y‖) := by
    have h := mul_le_mul_of_nonneg_left (le_max_right Lf Lc) (norm_nonneg y)
    linarith [le_max_left Lf Lc]
  have hcoef := mul_le_mul_of_nonneg_left (one_add_norm_le_sqrt_two_mul_multiplierNorm y)
    (hLf.trans (le_max_left Lf Lc))
  have ht : Lf + ‖y‖ * Lc ≤ Real.sqrt 2 * max Lf Lc * multiplierNorm y := by
    nlinarith only [hbase, hcoef]
  exact (h1.trans (add_le_add hlf (hn.trans h2))).trans (by
    have h := mul_le_mul_of_nonneg_right ht (norm_nonneg (u - v))
    nlinarith only [h])
end Constrained

namespace Constrained
open TaylorModel
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
/-- Approximate restricted Taylor criticality controls the actual Lagrangian on the source
stability radius. -/
theorem value_ge_of_lagrangian_criticality {f : E → ℝ} {c : E → F} {j : ℕ}
    (hj : 0 < j) {D V : Set E} (hD : IsOpen D) (hf : ContDiffOn ℝ j f D)
    (hc : ContDiffOn ℝ j c D) (x : E) (y : F) {δ ε η Lf Lc : ℝ}
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hLf : 0 ≤ Lf) (hLc : 0 ≤ Lc)
    (hball : Metric.closedBall x δ ⊆ D)
    (hlf : ∀ u ∈ Metric.closedBall x δ, ∀ v ∈ Metric.closedBall x δ,
      ‖iteratedFDeriv ℝ j f u - iteratedFDeriv ℝ j f v‖ ≤ Lf * ‖u - v‖)
    (hlc : ∀ u ∈ Metric.closedBall x δ, ∀ v ∈ Metric.closedBall x δ,
      ‖iteratedFDeriv ℝ j c u - iteratedFDeriv ℝ j c v‖ ≤ Lc * ‖u - v‖)
    (hcrit : restrictedCriticality (vectorLagrangian f c y) j V x δ ≤
      ε * multiplierNorm y * δ ^ j / j.factorial + η)
    {d : E} (hdV : d ∈ V)
    (hd : ‖d‖ ≤ δ ∧ (max Lf Lc = 0 ∨
      ‖d‖ ≤ (j + 1 : ℕ) * ε / (Real.sqrt 2 * max Lf Lc))) :
    vectorLagrangian f c y x - 2 * ε * multiplierNorm y * δ ^ j / j.factorial - η ≤
      vectorLagrangian f c y (x + d) := by
  let L := Real.sqrt 2 * max Lf Lc * multiplierNorm y
  have hM := (multiplierNorm_pos y).le
  have hmax : 0 ≤ max Lf Lc := hLf.trans (le_max_left _ _)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hε' : 0 ≤ ε * multiplierNorm y := mul_nonneg hε (multiplierNorm_pos y).le
  have hdδ := hd.1
  have hsmall : L * ‖d‖ ≤ (j + 1 : ℕ) * (ε * multiplierNorm y) := by
    rcases eq_or_lt_of_le hmax with hz | hp
    · have hz' : max Lf Lc = 0 := hz.symm
      dsimp [L]
      rw [hz', mul_zero, zero_mul, zero_mul]
      positivity
    · have hden : 0 < Real.sqrt 2 * max Lf Lc := mul_pos (by positivity) hp
      have hs := (le_div_iff₀ hden).mp (hd.2.resolve_left hp.ne')
      have hm := mul_le_mul_of_nonneg_right hs (multiplierNorm_pos y).le
      dsimp [L]
      nlinarith only [hm]
  have hb := TaylorModel.value_ge_of_decrement_le hj hD
    (contDiffOn_vectorLagrangian hf hc y) x hδ hball hL
    (fun u hu v hv => norm_iteratedFDeriv_vectorLagrangian_sub_le hD hf hc y
      (hball hu) (hball hv) hLf hLc (hlf u hu v hv) (hlc u hu v hv)) hdδ
    ((decrement_le_restrictedCriticality (vectorLagrangian f c y) j V x hdV hdδ).trans hcrit)
  have herr := TaylorModel.lipschitz_error_le_tolerance j (norm_nonneg d) hε' hdδ hsmall
  have he : 2 * ε * multiplierNorm y * δ ^ j / (j.factorial : ℝ) =
      2 * (ε * multiplierNorm y * δ ^ j / j.factorial) := by ring
  rw [he]
  linarith only [hb, herr]

omit [NormedSpace ℝ E] [ProperSpace E] in
/-- Approximate feasibility at both endpoints costs at most twice the feasibility tolerance
times multiplier norm. -/
theorem objective_bound_of_lagrangian_bound (f : E → ℝ) (c : E → F) (x d : E) (y : F)
    {ε₀ b : ℝ} (hc0 : ‖c x‖ ≤ ε₀) (hcd : ‖c (x + d)‖ ≤ ε₀)
    (hL : vectorLagrangian f c y x - b ≤ vectorLagrangian f c y (x + d)) :
    f x - 2 * ε₀ * ‖y‖ - b ≤ f (x + d) := by
  have h0 := (abs_le.mp (abs_real_inner_le_norm y (c x))).2
  have hd := (abs_le.mp (abs_real_inner_le_norm y (c (x + d)))).1
  have hn0 := mul_le_mul_of_nonneg_left hc0 (norm_nonneg y)
  have hnd := mul_le_mul_of_nonneg_left hcd (norm_nonneg y)
  dsimp [vectorLagrangian] at hL
  nlinarith only [hL, h0, hd, hn0, hnd]

omit [NormedSpace ℝ E] [ProperSpace E] in
/-- Exact constraint matching or compatible exact endpoint feasibility eliminates the objective
transfer loss. -/
theorem objective_bound_of_lagrangian_bound_no_loss (f : E → ℝ) (c : E → F)
    (x d : E) (y : F) {b : ℝ}
    (hL : vectorLagrangian f c y x - b ≤ vectorLagrangian f c y (x + d))
    (hc : (c (x + d) = 0 ∧ inner ℝ y (c x) ≤ 0) ∨ c (x + d) = c x) :
    f x - b ≤ f (x + d) := by
  dsimp [vectorLagrangian] at hL
  rcases hc with ⟨hz, hi⟩ | he
  · rw [hz, inner_zero_right, sub_zero] at hL
    linarith
  · rw [he] at hL
    linarith
end Constrained
