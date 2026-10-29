import Numlib.Optimization.Constrained.TargetResidual

/-!
# Taylor decrements of the target merit function on the target

For the target merit function `μ(x, t) = ½ (‖c(x)‖² + (f(x) - t)²)` (`Constrained.targetMerit`)
and the feasibility merit `ν(x) = ½ ‖c(x)‖²` (`Constrained.halfSqNorm`, the case `f = 0`,
`t = 0`), this file compares the Taylor decrements and measures of `μ(·, t)` and `ν` at a point
where `f(x) = t` ([cartis2022evaluation], §14.3.2.2, the case `f(x_ε) = t_ε` of Lemma 14.3.5):
they agree at first order, while at orders `2` and `3` they differ by terms in `∇f(x)[d]`, so the
measures agree on `ker ∇f(x)` and differ by explicit amounts on the whole set.

## Main definitions

* `Constrained.halfSqNorm`: `ν(x) = ½ ‖c(x)‖²`.

## Main results

* `Constrained.taylorMeasure_one_targetMerit_of_eq`: the first-order measures agree;
* `Constrained.taylorDecrement_two_targetMerit_of_eq`,
  `Constrained.taylorDecrement_three_targetMerit_of_eq`: the decrements of orders `2` and `3`;
* `Constrained.taylorMeasure_halfSqNorm_two_le_of_eq`,
  `Constrained.taylorMeasure_halfSqNorm_three_le_of_eq`: the measures of `ν` from those of `μ`.
-/

open Set Metric

namespace Constrained

section HalfSqNorm

variable {E F : Type*} [NormedAddCommGroup F]

/-- The feasibility merit function `ν(x) = ½ ‖c(x)‖²` (`Φ₂` of [cartis2022evaluation],
(14.3.16)). -/
noncomputable def halfSqNorm (c : E → F) (x : E) : ℝ := ‖c x‖ ^ 2 / 2

theorem halfSqNorm_apply (c : E → F) (x : E) : halfSqNorm c x = ‖c x‖ ^ 2 / 2 := rfl

/-- `ν` is the merit function of the zero objective with target `0`. -/
theorem halfSqNorm_eq_targetMerit (c : E → F) :
    halfSqNorm c = targetMerit (fun _ => (0 : ℝ)) c 0 := by
  funext z
  simp [halfSqNorm]

theorem halfSqNorm_nonneg (c : E → F) (x : E) : 0 ≤ halfSqNorm c x := by
  rw [halfSqNorm_apply]; positivity

/-- `ν(y) ≤ ν(x)` iff `‖c(y)‖ ≤ ‖c(x)‖`. -/
theorem halfSqNorm_le_halfSqNorm_iff {c : E → F} {x y : E} :
    halfSqNorm c y ≤ halfSqNorm c x ↔ ‖c y‖ ≤ ‖c x‖ := by
  rw [halfSqNorm_apply, halfSqNorm_apply, div_le_div_iff_of_pos_right two_pos]
  exact pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero

end HalfSqNorm

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F]

variable {f : E → ℝ} {c : E → F} {t : ℝ} {x : E}

/-- The first-order Taylor measures of `μ(·, t)` and `ν` agree at a point where `f(x) = t`. -/
theorem taylorMeasure_one_targetMerit_of_eq (hf : DifferentiableAt ℝ f x)
    (hc : DifferentiableAt ℝ c x) (ht : f x = t) (δ : ℝ) (S : Set E) :
    Optimization.taylorMeasure (ftaylorSeries ℝ (targetMerit f c t) x) 1 δ S =
      Optimization.taylorMeasure (ftaylorSeries ℝ (halfSqNorm c) x) 1 δ S := by
  simp only [Optimization.taylorMeasure_eq_sSup]
  congr 2
  funext d
  rw [FormalMultilinearSeries.taylorDecrement_one_apply,
    FormalMultilinearSeries.taylorDecrement_one_apply]
  simp only [ftaylorSeries, iteratedFDeriv_one_apply]
  rw [fderiv_targetMerit_of_eq hf hc ht, halfSqNorm_eq_targetMerit,
    fderiv_targetMerit_of_eq (differentiableAt_const _) hc rfl]

/-- At a point where `f(x) = t`: `ΔT_{μ,2}(d) = ΔT_{ν,2}(d) - ½ (∇f(x)[d])²`. -/
theorem taylorDecrement_two_targetMerit_of_eq (hf : ContDiffAt ℝ 2 f x)
    (hc : ContDiffAt ℝ 2 c x) (ht : f x = t) (d : E) :
    (ftaylorSeries ℝ (targetMerit f c t) x).taylorDecrement 2 d =
      (ftaylorSeries ℝ (halfSqNorm c) x).taylorDecrement 2 d - (fderiv ℝ f x d) ^ 2 / 2 := by
  have hf1 : DifferentiableAt ℝ f x := hf.differentiableAt two_ne_zero
  have hc1 : DifferentiableAt ℝ c x := hc.differentiableAt two_ne_zero
  rw [FormalMultilinearSeries.taylorDecrement_two, FormalMultilinearSeries.taylorDecrement_two]
  simp only [ftaylorSeries, iteratedFDeriv_one_apply]
  rw [fderiv_targetMerit_of_eq hf1 hc1 ht, iteratedFDeriv_two_targetMerit_apply hf hc,
    halfSqNorm_eq_targetMerit, iteratedFDeriv_two_targetMerit_apply contDiffAt_const hc,
    fderiv_targetMerit_of_eq (differentiableAt_const _) hc1 rfl, ← ht]
  simp
  ring

/-- At a point where `f(x) = t`: `ΔT_{μ,3}(d) = ΔT_{ν,3}(d) - ½ (∇f(x)[d])² -
½ ∇f(x)[d] ∇²f(x)[d]²`. -/
theorem taylorDecrement_three_targetMerit_of_eq (hf : ContDiffAt ℝ 3 f x)
    (hc : ContDiffAt ℝ 3 c x) (ht : f x = t) (d : E) :
    (ftaylorSeries ℝ (targetMerit f c t) x).taylorDecrement 3 d =
      (ftaylorSeries ℝ (halfSqNorm c) x).taylorDecrement 3 d - (fderiv ℝ f x d) ^ 2 / 2 -
        fderiv ℝ f x d * iteratedFDeriv ℝ 2 f x (fun _ => d) / 2 := by
  have hf2 : ContDiffAt ℝ 2 f x := hf.of_le (by norm_num)
  have hc2 : ContDiffAt ℝ 2 c x := hc.of_le (by norm_num)
  have h2 := taylorDecrement_two_targetMerit_of_eq hf2 hc2 ht d
  rw [FormalMultilinearSeries.taylorDecrement_three, FormalMultilinearSeries.taylorDecrement_three]
  rw [FormalMultilinearSeries.taylorDecrement_two, FormalMultilinearSeries.taylorDecrement_two]
    at h2
  have h3 : iteratedFDeriv ℝ 3 (targetMerit f c t) x (fun _ => d) =
      iteratedFDeriv ℝ 3 (halfSqNorm c) x (fun _ => d) +
        3 * iteratedFDeriv ℝ 2 f x (fun _ => d) * fderiv ℝ f x d := by
    rw [iteratedFDeriv_three_targetMerit_apply hf hc, halfSqNorm_eq_targetMerit,
      iteratedFDeriv_three_targetMerit_apply contDiffAt_const hc, ← ht]
    simp
  simp only [ftaylorSeries] at h2 ⊢
  rw [h3]
  linarith

omit [InnerProductSpace ℝ F] in
private theorem abs_fderiv_le {d : E} {δ : ℝ} (hd : d ∈ closedBall (0 : E) δ) :
    |fderiv ℝ f x d| ≤ ‖fderiv ℝ f x‖ * δ := by
  rw [← Real.norm_eq_abs]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left
    (mem_closedBall_zero_iff.1 hd) (norm_nonneg _))

omit [InnerProductSpace ℝ F] in
private theorem abs_iteratedFDeriv_two_le {d : E} {δ : ℝ} (hd : d ∈ closedBall (0 : E) δ) :
    |iteratedFDeriv ℝ 2 f x (fun _ => d)| ≤ ‖iteratedFDeriv ℝ 2 f x‖ * δ ^ 2 := by
  rw [← Real.norm_eq_abs]
  refine ((iteratedFDeriv ℝ 2 f x).le_opNorm _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
    (mem_closedBall_zero_iff.1 hd) 2) (norm_nonneg _)

/-- Second-order measures of `ν` from those of `μ` at a point where `f(x) = t`: on
`S ∩ ker ∇f(x)` they agree, and on `S` they differ by at most `(‖∇f(x)‖ δ)²/2`. -/
theorem taylorMeasure_halfSqNorm_two_le_of_eq {δ B : ℝ} (hf : ContDiffAt ℝ 2 f x)
    (hc : ContDiffAt ℝ 2 c x) (ht : f x = t) (hδ : 0 ≤ δ) {S : Set E} (hS : (0 : E) ∈ S)
    (hμ : Optimization.taylorMeasure (ftaylorSeries ℝ (targetMerit f c t) x) 2 δ S ≤ B) :
    Optimization.taylorMeasure (ftaylorSeries ℝ (halfSqNorm c) x) 2 δ
        (S ∩ {d | fderiv ℝ f x d = 0}) ≤ B ∧
      Optimization.taylorMeasure (ftaylorSeries ℝ (halfSqNorm c) x) 2 δ S ≤
        B + (‖fderiv ℝ f x‖ * δ) ^ 2 / 2 := by
  constructor
  · rw [Optimization.taylorMeasure]
    refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self hδ, hS, by simp⟩
      fun d hd => ?_
    have h := taylorDecrement_two_targetMerit_of_eq hf hc ht d
    have hd0 : fderiv ℝ f x d = 0 := hd.2.2
    have hμd := Optimization.taylorDecrement_le_taylorMeasure
      (ftaylorSeries ℝ (targetMerit f c t) x) 2 (S := S) ⟨hd.1, hd.2.1⟩
    rw [hd0] at h
    linarith
  · rw [Optimization.taylorMeasure]
    refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self hδ, hS⟩ fun d hd => ?_
    have h := taylorDecrement_two_targetMerit_of_eq hf hc ht d
    have hμd := Optimization.taylorDecrement_le_taylorMeasure
      (ftaylorSeries ℝ (targetMerit f c t) x) 2 (S := S) hd
    have hg : (fderiv ℝ f x d) ^ 2 ≤ (‖fderiv ℝ f x‖ * δ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_fderiv_le hd.1) 2
    linarith

/-- Third-order measures of `ν` from those of `μ` at a point where `f(x) = t`: on
`S ∩ ker ∇f(x)` they agree, and on `S` they differ by at most
`(‖∇f(x)‖ δ)²/2 + ‖∇f(x)‖ δ ‖∇²f(x)‖ δ²/2`. -/
theorem taylorMeasure_halfSqNorm_three_le_of_eq {δ B : ℝ} (hf : ContDiffAt ℝ 3 f x)
    (hc : ContDiffAt ℝ 3 c x) (ht : f x = t) (hδ : 0 ≤ δ) {S : Set E} (hS : (0 : E) ∈ S)
    (hμ : Optimization.taylorMeasure (ftaylorSeries ℝ (targetMerit f c t) x) 3 δ S ≤ B) :
    Optimization.taylorMeasure (ftaylorSeries ℝ (halfSqNorm c) x) 3 δ
        (S ∩ {d | fderiv ℝ f x d = 0}) ≤ B ∧
      Optimization.taylorMeasure (ftaylorSeries ℝ (halfSqNorm c) x) 3 δ S ≤
        B + (‖fderiv ℝ f x‖ * δ) ^ 2 / 2 +
          ‖fderiv ℝ f x‖ * δ * (‖iteratedFDeriv ℝ 2 f x‖ * δ ^ 2) / 2 := by
  constructor
  · rw [Optimization.taylorMeasure]
    refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self hδ, hS, by simp⟩
      fun d hd => ?_
    have h := taylorDecrement_three_targetMerit_of_eq hf hc ht d
    have hd0 : fderiv ℝ f x d = 0 := hd.2.2
    have hμd := Optimization.taylorDecrement_le_taylorMeasure
      (ftaylorSeries ℝ (targetMerit f c t) x) 3 (S := S) ⟨hd.1, hd.2.1⟩
    rw [hd0] at h
    linarith
  · rw [Optimization.taylorMeasure]
    refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self hδ, hS⟩ fun d hd => ?_
    have h := taylorDecrement_three_targetMerit_of_eq hf hc ht d
    have hμd := Optimization.taylorDecrement_le_taylorMeasure
      (ftaylorSeries ℝ (targetMerit f c t) x) 3 (S := S) hd
    have h1 := abs_fderiv_le (f := f) (x := x) hd.1
    have h2 := abs_iteratedFDeriv_two_le (f := f) (x := x) hd.1
    have hg : (fderiv ℝ f x d) ^ 2 ≤ (‖fderiv ℝ f x‖ * δ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have hgh : fderiv ℝ f x d * iteratedFDeriv ℝ 2 f x (fun _ => d) ≤
        ‖fderiv ℝ f x‖ * δ * (‖iteratedFDeriv ℝ 2 f x‖ * δ ^ 2) := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
    linarith

end Constrained
