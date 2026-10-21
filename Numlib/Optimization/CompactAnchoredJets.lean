import Numlib.Optimization.ConstrainedTaylorGaps
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Bounded anchored jets on compact neighborhoods

A function smooth through one more derivative has bounded diagonal jets and Lipschitz jet
comparisons on bounded balls in a proper normed space. Compactness bounds the actual derivative
maps, and the mean value inequality supplies comparisons throughout the neighborhood.
-/

noncomputable section
open Set Metric
open scoped ContDiff
namespace Optimization.ConstrainedTaylorCriticality

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

omit [ProperSpace E] in
/-- Restricting the model centers preserves the actual bounded and anchored Lipschitz jets. -/
theorem HasAnchoredBoundedJets.mono_centers {f : E → ℝ} {r : ℕ} {A A' U : Set E}
    {includeValue : Bool} {L B : ℕ → ℝ}
    (hf : HasAnchoredBoundedJets f r A U includeValue L B) (hA : A' ⊆ A) :
    HasAnchoredBoundedJets f r A' U includeValue L B :=
  ⟨hf.isOpen, hf.convex, hA.trans hf.centers_subset, hf.contDiffOn,
    hf.lipschitz_nonneg, hf.bound_nonneg,
    fun j hj hjr x hx => hf.bound j hj hjr x (hA hx),
    fun j hj hjr x hx => hf.lipschitz j hj hjr x (hA hx)⟩

/-- Smooth functions have anchored bounded jets on concentric bounded balls, with constants
at least one. Comparisons cover every point of the larger open ball. -/
theorem exists_anchoredBoundedJets_of_contDiff
    (r : ℕ) {f : E → ℝ} (hf : ContDiff ℝ (r + 1) f) {a b : ℝ} (hab : a < b) :
    ∃ L B : ℕ → ℝ, (∀ j, 1 ≤ L j) ∧ (∀ j, 1 ≤ B j) ∧
      HasAnchoredBoundedJets f r (closedBall 0 a) (ball 0 b) false L B := by
  have hj (j : ℕ) (hjr : j ≤ r) : ContDiff ℝ 1 (iteratedFDeriv ℝ j f) :=
    hf.iteratedFDeriv_right (by exact_mod_cast (show 1 + j ≤ r + 1 by omega))
  have hb (j : ℕ) : ∃ L B : ℝ, 1 ≤ L ∧ 1 ≤ B ∧
      (j ≤ r → ∀ x ∈ closedBall (0 : E) b, ‖iteratedFDeriv ℝ j f x‖ ≤ B) ∧
      (j ≤ r → ∀ x ∈ closedBall (0 : E) b,
        ‖fderiv ℝ (iteratedFDeriv ℝ j f) x‖ ≤ L) := by
    by_cases hjr : j ≤ r
    · obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : E) b).exists_bound_of_continuousOn
        (hj j hjr).continuous.continuousOn
      obtain ⟨L, hL⟩ := (isCompact_closedBall (0 : E) b).exists_bound_of_continuousOn
        ((hj j hjr).fderiv_right (m := 0) (by norm_num)).continuous.continuousOn
      exact ⟨max 1 L, max 1 B, le_max_left _ _, le_max_left _ _,
        fun _ x hx => (hB x hx).trans (le_max_right _ _),
        fun _ x hx => (hL x hx).trans (le_max_right _ _)⟩
    · exact ⟨1, 1, le_rfl, le_rfl, fun h => (hjr h).elim, fun h => (hjr h).elim⟩
  choose L B hL hB hnorm hderiv using hb
  refine ⟨L, B, hL, hB, isOpen_ball, convex_ball _ _, ?_,
    (hf.of_le (by exact_mod_cast Nat.le_succ r)).contDiffOn, ?_, ?_, ?_, ?_⟩
  · exact closedBall_subset_ball hab
  · intro j _ _
    exact zero_le_one.trans (hL j)
  · intro j _ _
    exact zero_le_one.trans (hB j)
  · intro j _ hjr x hx d
    have hx' : x ∈ closedBall (0 : E) b := closedBall_subset_closedBall hab.le hx
    exact ((iteratedFDeriv ℝ j f x).le_opNorm (fun _ => d)).trans (by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        mul_le_mul_of_nonneg_right (hnorm j hjr x hx') (pow_nonneg (norm_nonneg d) j))
  · intro j _ hjr x hx y hy d
    have hx' : x ∈ closedBall (0 : E) b := closedBall_subset_closedBall hab.le hx
    have hy' : y ∈ closedBall (0 : E) b := ball_subset_closedBall hy
    have hLip := (convex_closedBall (0 : E) b).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (hj j hjr).differentiable (by norm_num) z) (hderiv j hjr) hx' hy'
    exact ((iteratedFDeriv ℝ j f y - iteratedFDeriv ℝ j f x).le_opNorm
      (fun _ => d)).trans (by
        simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
          mul_le_mul_of_nonneg_right hLip (pow_nonneg (norm_nonneg d) j))

end Optimization.ConstrainedTaylorCriticality
