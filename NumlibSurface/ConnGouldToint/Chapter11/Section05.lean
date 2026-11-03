import NumlibSurface.ConnGouldToint.Chapter11.Section02

/-! # Taylor models of composite objectives -/

open Metric
open scoped NNReal

namespace ConnGouldToint.Chapter11

variable {E Y I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The models (11.5.1)–(11.5.3), with quadratic terms represented by their
values. Set both to zero for (11.5.1), use the Taylor terms for (11.5.2),
and keep just the objective quadratic for (11.5.3). -/
noncomputable def compositeTaylorModel (f : E → ℝ) (c : E → Y) (h : Y → ℝ)
    (q : E → I → E → ℝ) (r : E → I → E → Y) (x : E) (i : I) (s : E) : ℝ :=
  f x + fderiv ℝ f x s + q x i s + h (c x + fderiv ℝ c x s + r x i s)

/-- Quantitative accuracy in Theorem 11.5.1. The outer function needs a common
Lipschitz bound on the actual and modeled residuals. Taylor remainder and
quadratic bounds supply the uniform constant. -/
theorem compositeTaylorModel_error {f : E → ℝ} {c : E → Y} {h : Y → ℝ}
    {q : E → I → E → ℝ} {r : E → I → E → Y} {x s : E} {i : I} {D : Set Y}
    {L : ℝ≥0} {A B C F : ℝ} (hL : LipschitzOnWith L h D)
    (hcD : c (x + s) ∈ D) (hmD : c x + fderiv ℝ c x s + r x i s ∈ D)
    (hf : |f (x + s) - (f x + fderiv ℝ f x s)| ≤ A * ‖s‖ ^ 2)
    (hc : ‖c (x + s) - (c x + fderiv ℝ c x s)‖ ≤ B * ‖s‖ ^ 2)
    (hq : |q x i s| ≤ C * ‖s‖ ^ 2) (hr : ‖r x i s‖ ≤ F * ‖s‖ ^ 2) :
    |f (x + s) + h (c (x + s)) - compositeTaylorModel f c h q r x i s| ≤
      (A + C + (L : ℝ) * (B + F)) * ‖s‖ ^ 2 := by
  have hres : ‖c (x + s) - (c x + fderiv ℝ c x s + r x i s)‖ ≤
      (B + F) * ‖s‖ ^ 2 := by
    rw [← sub_sub, add_mul]
    exact (norm_sub_le _ _).trans (add_le_add hc hr)
  have hh := hL.dist_le_mul _ hcD _ hmD
  rw [Real.dist_eq, dist_eq_norm] at hh
  have houter := hh.trans (mul_le_mul_of_nonneg_left hres L.coe_nonneg)
  unfold compositeTaylorModel
  rw [show f (x + s) + h (c (x + s)) -
      (f x + fderiv ℝ f x s + q x i s + h (c x + fderiv ℝ c x s + r x i s)) =
      (f (x + s) - (f x + fderiv ℝ f x s) - q x i s) +
        (h (c (x + s)) - h (c x + fderiv ℝ c x s + r x i s)) by ring]
  exact (abs_add_le _ _).trans ((add_le_add ((abs_sub _ _).trans (add_le_add hf hq))
    houter).trans_eq (by ring))

omit [NormedSpace ℝ E] in
/-- Uniform normalized agreement in Theorem 11.5.1 for all three Taylor
models, whenever the quadratic remainder estimate holds uniformly. -/
theorem theorem_11_5_1_uniform_agreement {f : E → ℝ} {m : E → I → E → ℝ}
    {x : E} {ε δ K : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hK : 0 ≤ K)
    (herr : ∀ y ∈ ball x ε, ∀ i s, ‖s‖ ≤ δ →
      |f (y + s) - m y i s| ≤ K * ‖s‖ ^ 2) :
    UniformNormalizedModelAgreementAt f m x := by
  intro a ha
  let R := min δ (a / (K + 1))
  have hK₁ : 0 < K + 1 := by positivity
  refine ⟨ε, R, hε, lt_min hδ (div_pos ha hK₁), ?_⟩
  intro y hy i s hs
  by_cases hz : s = 0
  · simp [normalizedModelError, hz, ha.le]
  have hn := norm_pos_iff.mpr hz
  have hb := (le_div_iff₀ hK₁).mp (hs.trans (min_le_right _ _))
  have hmul : K * ‖s‖ ≤ a := by nlinarith only [hb, hn.le]
  rw [normalizedModelError, abs_div, abs_of_nonneg hn.le]
  apply (div_le_iff₀ hn).mpr
  calc
    _ ≤ K * ‖s‖ ^ 2 := herr y hy i s (hs.trans (min_le_left _ _))
    _ = (K * ‖s‖) * ‖s‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hmul hn.le

/-- The residual can stay in the domain of the outer function while its
affine model leaves that domain at arbitrarily small steps. -/
theorem compositeTaylorModel_domain_counterexample :
    ∀ ε > (0 : ℝ), ∃ x s : ℝ, |x| < ε ∧ |s| < ε ∧
      0 ≤ (x + s) ^ 2 ∧ x ^ 2 + (2 * x) * s < 0 := by
  intro ε hε
  refine ⟨ε / 2, -(ε / 2), ?_, ?_, sq_nonneg _, ?_⟩
  · rw [abs_of_pos (half_pos hε)]
    linarith
  · rw [abs_neg, abs_of_pos (half_pos hε)]
    linarith
  · nlinarith only [sq_pos_of_pos (half_pos hε)]

end ConnGouldToint.Chapter11
