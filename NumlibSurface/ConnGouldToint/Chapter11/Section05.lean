import NumlibSurface.ConnGouldToint.Chapter11.Section02
import NumlibSurface.ConnGouldToint.Chapter03.Section01

/-! # Taylor models of composite objectives -/

open Filter Metric Optimization ConvexAnalysis
open scoped NNReal Topology

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

/-- Theorem 11.5.1's uniform accuracy conclusion from Lipschitz derivatives
on the trial segments and a Lipschitz outer function on the two residual images. -/
theorem theorem_11_5_1_of_lipschitz_derivatives
    {f : E → ℝ} {c : E → Y} {h : Y → ℝ}
    {q : E → I → E → ℝ} {r : E → I → E → Y} {x : E}
    {S : Set E} {D : Set Y} {ε δ C F : ℝ} {L Lf Lc : ℝ≥0}
    (hε : 0 < ε) (hδ : 0 < δ) (hC : 0 ≤ C) (hF : 0 ≤ F)
    (hS : IsOpen S) (hf : ContDiffOn ℝ 1 f S) (hc : ContDiffOn ℝ 1 c S)
    (hLf : LipschitzOnWith Lf (fderiv ℝ f) S)
    (hLc : LipschitzOnWith Lc (fderiv ℝ c) S) (hL : LipschitzOnWith L h D)
    (hseg : ∀ y ∈ ball x ε, ∀ s, ‖s‖ ≤ δ → ∀ t ∈ Set.Icc (0 : ℝ) 1, y + t • s ∈ S)
    (hactual : ∀ y ∈ ball x ε, ∀ s, ‖s‖ ≤ δ → c (y + s) ∈ D)
    (hmodel : ∀ y ∈ ball x ε, ∀ i s, ‖s‖ ≤ δ →
      c y + fderiv ℝ c y s + r y i s ∈ D)
    (hq : ∀ y ∈ ball x ε, ∀ i s, ‖s‖ ≤ δ → |q y i s| ≤ C * ‖s‖ ^ 2)
    (hr : ∀ y ∈ ball x ε, ∀ i s, ‖s‖ ≤ δ → ‖r y i s‖ ≤ F * ‖s‖ ^ 2) :
    UniformNormalizedModelAgreementAt (fun y ↦ f y + h (c y))
      (compositeTaylorModel f c h q r) x := by
  apply theorem_11_5_1_uniform_agreement (K := (1 / 2 : ℝ) * Lf + C +
    (L : ℝ) * ((1 / 2 : ℝ) * Lc + F)) hε hδ (by positivity)
  intro y hy i s hs
  have htrial := hseg y hy s hs
  have hyS : y ∈ S := by simpa using htrial 0 (by norm_num)
  have hTaylorF := Chapter03.theorem_3_1_4 hS hf htrial (γ := Lf)
    (fun z hz ↦ by simpa only [dist_eq_norm] using hLf.dist_le_mul z hz y hyS)
  have hTaylorC := Chapter03.theorem_3_1_6 hS hc htrial (γ := Lc)
    (fun z hz ↦ by simpa only [dist_eq_norm] using hLc.dist_le_mul z hz y hyS)
  exact compositeTaylorModel_error hL (hactual y hy s hs) (hmodel y hy i s hs)
    hTaylorF hTaylorC (hq y hy i s hs) (hr y hy i s hs)

/-- AM.2n and AM.3n in Theorem 11.5.1 follow from the uniform accuracy
estimate once the objective and model satisfy local Lipschitz regularity. -/
theorem theorem_11_5_1_value_and_directional_agreement
    {V₀ : Type*} [NormedAddCommGroup V₀] [InnerProductSpace ℝ V₀]
    [FiniteDimensional ℝ V₀] [Nontrivial V₀]
    {f : V₀ → ℝ} {m : V₀ → I → V₀ → ℝ} {x : V₀} {i : I}
    {U V : Set V₀} {Lf Lm : ℝ≥0}
    (hacc : UniformNormalizedModelAgreementAt f m x)
    (hU : U ∈ 𝓝 x) (hLf : LipschitzOnWith Lf f U)
    (hV : V ∈ 𝓝 (0 : V₀)) (hLm : LipschitzOnWith Lm (m x i) V)
    (hf : ∀ d : V₀, Tendsto (fun t : ℝ ↦ (f (x + t • d) - f x) / t)
      (𝓝[>] 0) (𝓝 (clarkeDerivative f x d)))
    (hm : ∀ d : V₀, Tendsto (fun t : ℝ ↦ (m x i (t • d) - m x i 0) / t)
      (𝓝[>] 0) (𝓝 (clarkeDerivative (m x i) 0 d))) :
    m x i 0 = f x ∧ ∀ d : V₀, d ≠ 0 →
      clarkeDerivative (m x i) 0 d = clarkeDerivative f x d := by
  apply (lemma_11_2_1 hU hLf hV hLm hf hm).mpr
  apply Metric.tendsto_nhds.mpr
  intro a ha
  obtain ⟨ε, Δ, hε, hΔ, h⟩ := hacc (a / 2) (half_pos ha)
  filter_upwards [ball_mem_nhds (0 : V₀) hΔ] with s hs
  rw [dist_zero_right, Real.norm_eq_abs]
  have hnorm : ‖s‖ ≤ Δ := by
    exact (by simpa only [mem_ball, dist_zero_right] using hs : ‖s‖ < Δ).le
  exact (h x (mem_ball_self hε) i s hnorm).trans_lt (half_lt_self ha)

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
