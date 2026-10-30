import Numlib.Analysis.Calculus.MultivariateTaylor.Remainder
import Numlib.Optimization.ModelBased.RatioTest
import Numlib.Optimization.Optimality.Approximate
import Numlib.Optimization.Subproblem.TrustRegion

/-!
# Quadratic models of trust-region methods

Trust-region methods of [cartis2022evaluation] (Algorithms 2.3.1 TR1, 3.2.1 TR2) use the
quadratic model `m(s) = f(x) + q(s)`, `q(s) = ⟪g, s⟫ + ½ ⟪s, H s⟫` (2.3.1), written with the shared
`Subproblem.quadModel g H` (`H : E →L[ℝ] E`, `‖H‖` its operator norm). For a `C²` function and
`H = Optimization.hessianOperator f x` this is the second-order Taylor polynomial
(`Optimization.taylorPolynomial_two_eq_quadModel`).

* `Optimization.IsCauchyStep g H Δ t`: `t` is a Cauchy step (2.3.5), a minimizer of the model
  along `-g` within the trust region, with existence `Optimization.exists_isCauchyStep`;
* `Optimization.neg_quadModel_cauchy_ge`: the Cauchy decrease (Lemma 2.3.2);
* `Optimization.quadModel_smul_le_of_curvature`, `Optimization.le_neg_quadModel_smul_of_curvature`:
  the eigenpoint decrease (Lemma 3.2.3);
* `Optimization.abs_reductionRatio_sub_one_le_trust_first`,
  `Optimization.le_reductionRatio_trust_first`: Lemma 2.3.3 for one iteration with the predicted
  decrease as a hypothesis, and its book form
  `Optimization.le_reductionRatio_trust_first_of_isCauchyStep`;
* `Optimization.abs_reductionRatio_sub_one_le_trust_second`,
  `Optimization.le_reductionRatio_trust_second`: Lemma 3.2.4 likewise, with book form
  `Optimization.le_reductionRatio_trust_second_of_curvature`;
* `Optimization.exists_isMinOn_quadModel_ball`: a global model minimizer in the trust region
  exists in finite dimension and satisfies both the Cauchy and the eigenpoint conditions.

The trust-region constraints on the Cauchy and eigenpoint steps are `‖t g‖ ≤ Δ_k`,
`‖t u‖ ≤ Δ_k` (written `x_k - t g ∈ 𝓡_k`, `x_k + t u ∈ 𝓑_{Δ_k}` in [cartis2022evaluation]).
-/

open Set Metric
open scoped RealInnerProductSpace Nat

namespace Optimization

open Subproblem

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `|⟪s, H s⟫| ≤ ‖H‖ ‖s‖²` (the real case of `ContinuousLinearMap.abs_re_inner_apply_self_le`). -/
private theorem abs_inner_self_apply_le (H : E →L[ℝ] E) (s : E) : |⟪s, H s⟫| ≤ ‖H‖ * ‖s‖ ^ 2 := by
  simpa [real_inner_comm] using H.abs_re_inner_apply_self_le s

/-- The model along the ray `-t g`: `q(-t g) = -t ‖g‖² + t²/2 ⟪g, H g⟫`. -/
theorem quadModel_neg_smul (g : E) (H : E →L[ℝ] E) (t : ℝ) :
    quadModel g H (-(t • g)) = -t * ‖g‖ ^ 2 + t ^ 2 / 2 * ⟪g, H g⟫ := by
  rw [quadModel_def, map_neg, map_smul, inner_neg_right, inner_neg_left, inner_neg_right,
    inner_smul_right, inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq]
  simp only [conj_trivial]
  ring

/-- The model along the ray `t u`: `q(t u) = t ⟪g, u⟫ + t²/2 ⟪u, H u⟫`. -/
theorem quadModel_smul (g : E) (H : E →L[ℝ] E) (t : ℝ) (u : E) :
    quadModel g H (t • u) = t * ⟪g, u⟫ + t ^ 2 / 2 * ⟪u, H u⟫ := by
  rw [quadModel_def, map_smul, inner_smul_right, inner_smul_left, inner_smul_right]
  simp only [conj_trivial]
  ring

/-- `t` is a **Cauchy step** of the model `q = Subproblem.quadModel g H` for the radius `Δ`
([cartis2022evaluation], (2.3.5)): `t ≥ 0`, the point `-t g` lies in the trust region
(`t ‖g‖ ≤ Δ`), and `-t g` minimizes `q` along `-g` within the region. The Cauchy step is
`s^C = -t g`. -/
def IsCauchyStep (g : E) (H : E →L[ℝ] E) (Δ t : ℝ) : Prop :=
  0 ≤ t ∧ t * ‖g‖ ≤ Δ ∧
    ∀ τ, 0 ≤ τ → τ * ‖g‖ ≤ Δ → quadModel g H (-(t • g)) ≤ quadModel g H (-(τ • g))

theorem isCauchyStep_iff {g : E} {H : E →L[ℝ] E} {Δ t : ℝ} :
    IsCauchyStep g H Δ t ↔ 0 ≤ t ∧ t * ‖g‖ ≤ Δ ∧
      ∀ τ, 0 ≤ τ → τ * ‖g‖ ≤ Δ → quadModel g H (-(t • g)) ≤ quadModel g H (-(τ • g)) :=
  Iff.rfl

/-- A Cauchy step exists for every radius `Δ ≥ 0` (a continuous function on a compact interval;
any `t` works if `g = 0`, e.g. `t = 0`). -/
theorem exists_isCauchyStep (g : E) (H : E →L[ℝ] E) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    ∃ t, IsCauchyStep g H Δ t := by
  rcases eq_or_ne g 0 with rfl | hg
  · exact ⟨0, le_rfl, by simpa using hΔ, fun τ _ _ => by simp [quadModel_def]⟩
  have hgpos : 0 < ‖g‖ := norm_pos_iff.2 hg
  have hcont : Continuous fun t : ℝ => quadModel g H (-(t • g)) :=
    (continuous_quadModel g H).comp (continuous_id.smul continuous_const).neg
  obtain ⟨t, ht, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := Δ / ‖g‖)).exists_isMinOn
    (nonempty_Icc.2 (div_nonneg hΔ hgpos.le)) hcont.continuousOn
  refine ⟨t, ht.1, (le_div_iff₀ hgpos).1 ht.2, fun τ hτ hτΔ => ?_⟩
  exact hmin ⟨hτ, (le_div_iff₀ hgpos).2 hτΔ⟩

/-- **Lemma 2.3.2** ([cartis2022evaluation], (2.3.12)): the decrease at a Cauchy step satisfies
`m(0) - m(s^C) = -q(-t g) ≥ ‖g‖/2 · min(‖g‖ / (1 + ‖H‖), Δ)`. The comparison step is
`τ = min(1/(1 + ‖H‖), Δ/‖g‖)`, along which `q(-τ g) ≤ -τ ‖g‖²/2`. -/
theorem neg_quadModel_cauchy_ge {g : E} {H : E →L[ℝ] E} {Δ t : ℝ} (ht : IsCauchyStep g H Δ t) :
    ‖g‖ / 2 * min (‖g‖ / (1 + ‖H‖)) Δ ≤ -quadModel g H (-(t • g)) := by
  have hΔ : 0 ≤ Δ := (mul_nonneg ht.1 (norm_nonneg g)).trans ht.2.1
  rcases eq_or_ne g 0 with rfl | hg
  · have := ht.2.2 0 le_rfl (by simpa using hΔ)
    simp only [zero_smul, neg_zero, quadModel_zero] at this
    simp only [norm_zero, zero_div, zero_mul]
    linarith
  have hgpos : 0 < ‖g‖ := norm_pos_iff.2 hg
  have hH : 0 ≤ ‖H‖ := norm_nonneg H
  set τ := min (1 / (1 + ‖H‖)) (Δ / ‖g‖) with hτ
  have hτ0 : 0 ≤ τ := le_min (by positivity) (div_nonneg hΔ hgpos.le)
  have hτg : τ * ‖g‖ ≤ Δ := (le_div_iff₀ hgpos).1 (min_le_right _ _)
  have hτH : τ * ‖H‖ ≤ 1 := by
    calc τ * ‖H‖ ≤ 1 / (1 + ‖H‖) * ‖H‖ := by gcongr; exact min_le_left _ _
      _ ≤ 1 := by rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith
  have hq : quadModel g H (-(τ • g)) ≤ -(τ * ‖g‖ ^ 2) / 2 := by
    rw [quadModel_neg_smul]
    have h1 := (le_abs_self _).trans (abs_inner_self_apply_le H g)
    have h2 : τ ^ 2 / 2 * ⟪g, H g⟫ ≤ τ ^ 2 / 2 * (‖H‖ * ‖g‖ ^ 2) := by gcongr
    have h3 : τ ^ 2 / 2 * (‖H‖ * ‖g‖ ^ 2) ≤ τ / 2 * ‖g‖ ^ 2 := by
      have : τ ^ 2 / 2 * (‖H‖ * ‖g‖ ^ 2) = (τ * ‖H‖) * (τ / 2 * ‖g‖ ^ 2) := by ring
      rw [this]
      exact mul_le_of_le_one_left (by positivity) hτH
    linarith
  have hmin := ht.2.2 τ hτ0 hτg
  have hτeq : ‖g‖ * τ = min (‖g‖ / (1 + ‖H‖)) Δ := by
    rw [hτ, mul_min_of_nonneg _ _ hgpos.le, mul_one_div, mul_div_cancel₀ _ hgpos.ne']
  calc ‖g‖ / 2 * min (‖g‖ / (1 + ‖H‖)) Δ = τ * ‖g‖ ^ 2 / 2 := by rw [← hτeq]; ring
    _ ≤ -quadModel g H (-(τ • g)) := by linarith
    _ ≤ -quadModel g H (-(t • g)) := neg_le_neg hmin

/-- **Lemma 3.2.3** core ([cartis2022evaluation], (3.2.5), (3.2.15)): along a unit direction `u`
of nonpositive curvature `⟪u, H u⟫ = λ ≤ 0` with `⟪g, u⟫ ≤ 0`, the model at the boundary point
`Δ u` satisfies `q(Δ u) ≤ λ Δ² / 2`, and `t = Δ` minimizes `t ↦ q(t u)` over `[0, Δ]` (the
eigenpoint lies on the trust-region boundary). -/
theorem quadModel_smul_le_of_curvature {g : E} {H : E →L[ℝ] E} {u : E} {lam Δ : ℝ}
    (hHu : ⟪u, H u⟫ = lam) (hlam : lam ≤ 0) (hgu : ⟪g, u⟫ ≤ 0) (hΔ : 0 ≤ Δ) :
    quadModel g H (Δ • u) ≤ lam * Δ ^ 2 / 2 ∧
      ∀ τ ∈ Icc 0 Δ, quadModel g H (Δ • u) ≤ quadModel g H (τ • u) := by
  refine ⟨?_, fun τ hτ => ?_⟩
  · rw [quadModel_smul, hHu]
    nlinarith
  · rw [quadModel_smul, quadModel_smul, hHu]
    obtain ⟨hτ0, hτΔ⟩ := hτ
    nlinarith [mul_nonneg (sub_nonneg.2 hτΔ) (add_nonneg hτ0 hΔ)]

/-- **Lemma 3.2.3** ([cartis2022evaluation], (3.2.15)): under the hypotheses of
`Optimization.quadModel_smul_le_of_curvature`, the eigenpoint decrease is
`m(0) - m(Δ u) = -q(Δ u) ≥ |λ| Δ² / 2`. -/
theorem le_neg_quadModel_smul_of_curvature {g : E} {H : E →L[ℝ] E} {u : E} {lam Δ : ℝ}
    (hHu : ⟪u, H u⟫ = lam) (hlam : lam ≤ 0) (hgu : ⟪g, u⟫ ≤ 0) (hΔ : 0 ≤ Δ) :
    |lam| * Δ ^ 2 / 2 ≤ -quadModel g H (Δ • u) := by
  have h := (quadModel_smul_le_of_curvature hHu hlam hgu hΔ).1
  rw [abs_of_nonpos hlam]
  linarith

end Inner

section Taylor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The second-order Taylor polynomial is the quadratic model with the gradient and the Hessian
operator ([cartis2022evaluation], (2.3.1), (3.1.2)):
`T_{f,2}(x, s) = f(x) + ⟪∇f(x), s⟫ + ½ ⟪s, ∇²f(x) s⟫`. -/
theorem taylorPolynomial_two_eq_quadModel {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (s : E) :
    taylorPolynomial f 2 x s = f x + quadModel (gradient f x) (hessianOperator f x) s := by
  rw [taylorPolynomial_two_apply, quadModel_def, inner_gradient_left,
    inner_hessianOperator_apply hf, ← apply_diag_eq_vec]
  ring

/-- The first-order Taylor polynomial: `T_{f,1}(x, s) = f(x) + ⟪∇f(x), s⟫`. -/
theorem taylorPolynomial_one_eq_inner (f : E → ℝ) (x s : E) :
    taylorPolynomial f 1 x s = f x + ⟪gradient f x, s⟫ := by
  rw [taylorPolynomial_apply, inner_gradient_left]
  simp [Finset.sum_range_succ, iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply]

variable {f : E → ℝ} {x s : E} {H : E →L[ℝ] E} {C : Set E} {L κB Δ : ℝ}

/-- **Lemma 2.3.3** for one iteration ([cartis2022evaluation]): the ratio of a trust-region
iteration with model `f(x) + q(s)`, `q = Subproblem.quadModel (∇f(x)) H` (any `H`, `‖H‖ ≤ κB`).
Let `∇f` be `L`-Lipschitz on a convex set `C` containing `x` and `x + s` (`f` `C¹` there),
`‖s‖ ≤ Δ` with `Δ > 0`, `g = ∇f(x) ≠ 0`, and let the predicted decrease `-q(s)` be at least
`‖g‖ Δ / 2` (the Cauchy decrease (2.3.16)). Then `|ρ - 1| ≤ (L + κB) Δ / ‖g‖`. (The book's
mean-value argument gives the constant `2(L + κB)`; (A.19) gives `L + κB`.) -/
theorem abs_reductionRatio_sub_one_le_trust_first (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ 1 f y) (hL : IteratedFDerivLipschitzOn f 1 L C) (hx : x ∈ C)
    (hxs : x + s ∈ C) (hH : ‖H‖ ≤ κB) (hs : ‖s‖ ≤ Δ) (hΔ : 0 < Δ) (hg : 0 < ‖gradient f x‖)
    (hpred : ‖gradient f x‖ * Δ / 2 ≤ -quadModel (gradient f x) H s) :
    |reductionRatio f x s (-quadModel (gradient f x) H s) - 1| ≤
      (L + κB) * Δ / ‖gradient f x‖ := by
  set g := gradient f x
  have hpredpos : 0 < -quadModel g H s := lt_of_lt_of_le (by positivity) hpred
  have hs0 : s ≠ 0 := by rintro rfl; simp at hpredpos
  have hspos : 0 < ‖s‖ := norm_pos_iff.2 hs0
  have hT := abs_sub_taylorPolynomial_le_of_lipschitz (p := 1) hC (by simpa using hf) hL hx hxs
  rw [taylorPolynomial_one_eq_inner] at hT
  have hL0 : 0 ≤ L := nonneg_of_abs_le_div_mul_pow (by positivity) hspos hT
  have hLκ : 0 ≤ L + κB := by linarith [norm_nonneg H]
  refine abs_reductionRatio_sub_one_le hpredpos ?_
  have hq : |(1 / 2 : ℝ) * ⟪s, H s⟫| ≤ κB / 2 * ‖s‖ ^ 2 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have := abs_inner_self_apply_le H s
    have : ‖H‖ * ‖s‖ ^ 2 ≤ κB * ‖s‖ ^ 2 := by gcongr
    linarith
  have heq : f (x + s) - (f x - -quadModel g H s) =
      (f (x + s) - (f x + ⟪g, s⟫)) - (1 / 2) * ⟪s, H s⟫ := by
    rw [quadModel_def]; ring
  rw [heq]
  calc _ ≤ |f (x + s) - (f x + ⟪g, s⟫)| + |(1 / 2 : ℝ) * ⟪s, H s⟫| := abs_sub _ _
    _ ≤ L / ((1 + 1)! : ℝ) * ‖s‖ ^ (1 + 1) + κB / 2 * ‖s‖ ^ 2 := add_le_add hT hq
    _ = (L + κB) / 2 * ‖s‖ ^ 2 := by norm_num; ring
    _ ≤ (L + κB) / 2 * Δ ^ 2 := by gcongr
    _ = (L + κB) * Δ / ‖g‖ * (‖g‖ * Δ / 2) := by field_simp
    _ ≤ (L + κB) * Δ / ‖g‖ * -quadModel g H s := by gcongr

/-- **Lemma 2.3.3** ([cartis2022evaluation]): under the hypotheses of
`Optimization.abs_reductionRatio_sub_one_le_trust_first`, a radius with
`(L + κB) Δ ≤ (1 - η) ‖∇f(x)‖` gives `ρ ≥ η`. (The book-form statement, which derives the
predicted-decrease hypothesis from the Cauchy condition and (2.3.15), is
`Optimization.le_reductionRatio_trust_first_of_isCauchyStep`.) -/
theorem le_reductionRatio_trust_first (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ 1 f y) (hL : IteratedFDerivLipschitzOn f 1 L C) (hx : x ∈ C)
    (hxs : x + s ∈ C) (hH : ‖H‖ ≤ κB) (hs : ‖s‖ ≤ Δ) (hΔ : 0 < Δ) (hg : 0 < ‖gradient f x‖)
    (hpred : ‖gradient f x‖ * Δ / 2 ≤ -quadModel (gradient f x) H s) {η : ℝ}
    (hηΔ : (L + κB) * Δ ≤ (1 - η) * ‖gradient f x‖) :
    η ≤ reductionRatio f x s (-quadModel (gradient f x) H s) := by
  have h := abs_reductionRatio_sub_one_le_trust_first hC hf hL hx hxs hH hs hΔ hg hpred
  have : (L + κB) * Δ / ‖gradient f x‖ ≤ 1 - η := (div_le_iff₀ hg).2 hηΔ
  linarith [neg_abs_le (reductionRatio f x s (-quadModel (gradient f x) H s) - 1)]

/-- **Lemma 3.2.4** for one iteration ([cartis2022evaluation]): with the exact second-order model
`H = ∇²f(x)`, `∇²f` `L`-Lipschitz on a convex `C ∋ x, x + s` (`f` `C²` there), `‖s‖ ≤ Δ`, `λ < 0`
and the predicted decrease at least `|λ| Δ² / 2` (the eigenpoint decrease (3.2.15)):
`|ρ - 1| ≤ L Δ / (3 |λ|)`. -/
theorem abs_reductionRatio_sub_one_le_trust_second (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ 2 f y) (hL : IteratedFDerivLipschitzOn f 2 L C) (hx : x ∈ C)
    (hxs : x + s ∈ C) (hs : ‖s‖ ≤ Δ) (hΔ : 0 < Δ) {lam : ℝ} (hlam : lam < 0)
    (hpred : |lam| * Δ ^ 2 / 2 ≤ -quadModel (gradient f x) (hessianOperator f x) s) :
    |reductionRatio f x s (-quadModel (gradient f x) (hessianOperator f x) s) - 1| ≤
      L * Δ / (3 * |lam|) := by
  set q := quadModel (gradient f x) (hessianOperator f x) s
  have habs : 0 < |lam| := abs_pos.2 hlam.ne
  have hpredpos : 0 < -q := lt_of_lt_of_le (by have := mul_pos habs (pow_pos hΔ 2); linarith) hpred
  have hs0 : s ≠ 0 := by rintro rfl; simp [q] at hpredpos
  have hspos : 0 < ‖s‖ := norm_pos_iff.2 hs0
  have hT := abs_sub_taylorPolynomial_le_of_lipschitz (p := 2) hC (by simpa using hf) hL hx hxs
  rw [taylorPolynomial_two_eq_quadModel (hf x hx)] at hT
  have hL0 : 0 ≤ L := nonneg_of_abs_le_div_mul_pow (by positivity) hspos hT
  refine abs_reductionRatio_sub_one_le hpredpos ?_
  have heq : f (x + s) - (f x - -q) = f (x + s) - (f x + q) := by ring
  rw [heq]
  calc |f (x + s) - (f x + q)| ≤ L / ((2 + 1)! : ℝ) * ‖s‖ ^ (2 + 1) := hT
    _ ≤ L / 6 * Δ ^ 3 := by norm_num [Nat.factorial]; gcongr
    _ = L * Δ / (3 * |lam|) * (|lam| * Δ ^ 2 / 2) := by field_simp; ring
    _ ≤ L * Δ / (3 * |lam|) * -q := by gcongr

/-- **Lemma 3.2.4** ([cartis2022evaluation], (3.2.16)): under the hypotheses of
`Optimization.abs_reductionRatio_sub_one_le_trust_second`, `L Δ ≤ 3 (1 - η) |λ|` gives `ρ ≥ η`.
(The book-form statement from the eigenpoint condition is
`Optimization.le_reductionRatio_trust_second_of_curvature`.) -/
theorem le_reductionRatio_trust_second (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ 2 f y) (hL : IteratedFDerivLipschitzOn f 2 L C) (hx : x ∈ C)
    (hxs : x + s ∈ C) (hs : ‖s‖ ≤ Δ) (hΔ : 0 < Δ) {lam : ℝ} (hlam : lam < 0)
    (hpred : |lam| * Δ ^ 2 / 2 ≤ -quadModel (gradient f x) (hessianOperator f x) s) {η : ℝ}
    (hηΔ : L * Δ ≤ 3 * (1 - η) * |lam|) :
    η ≤ reductionRatio f x s (-quadModel (gradient f x) (hessianOperator f x) s) := by
  have h := abs_reductionRatio_sub_one_le_trust_second hC hf hL hx hxs hs hΔ hlam hpred
  have habs : 0 < 3 * |lam| := mul_pos three_pos (abs_pos.2 hlam.ne)
  have : L * Δ / (3 * |lam|) ≤ 1 - η := (div_le_iff₀ habs).2 (by linarith)
  linarith [neg_abs_le (reductionRatio f x s
    (-quadModel (gradient f x) (hessianOperator f x) s) - 1)]

/-- **Lemma 2.3.3** ([cartis2022evaluation]), book form. Let `∇f` be `L`-Lipschitz (`L ≥ 1`) on a
convex `C ∋ x, x + s` (`f` `C¹` there), `‖H‖ ≤ κB`, `∇f(x) ≠ 0`, and let the step `s` lie in the
trust region (`‖s‖ ≤ Δ`, `Δ > 0`) and satisfy the Cauchy condition (2.3.4)
`q(s) ≤ q(s^C)` for a Cauchy step `t`. If (2.3.15) `Δ < (1 - η) ‖∇f(x)‖ / (2 (L + κB))` with
`η ≥ 0`, then `ρ ≥ η` (with `η = η₂`: the iteration is very successful). -/
theorem le_reductionRatio_trust_first_of_isCauchyStep (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ 1 f y) (hL : IteratedFDerivLipschitzOn f 1 L C) (hL1 : 1 ≤ L)
    (hx : x ∈ C) (hxs : x + s ∈ C) (hH : ‖H‖ ≤ κB) {t : ℝ}
    (ht : IsCauchyStep (gradient f x) H Δ t)
    (hsC : quadModel (gradient f x) H s ≤ quadModel (gradient f x) H (-(t • gradient f x)))
    (hs : ‖s‖ ≤ Δ) (hΔ : 0 < Δ) (hg : 0 < ‖gradient f x‖) {η : ℝ} (hη : 0 ≤ η)
    (hΔη : Δ < (1 - η) * ‖gradient f x‖ / (2 * (L + κB))) :
    η ≤ reductionRatio f x s (-quadModel (gradient f x) H s) := by
  set g := gradient f x
  have hκ : 0 ≤ κB := (norm_nonneg H).trans hH
  have hLκ : 0 < L + κB := by linarith
  rw [lt_div_iff₀ (by positivity)] at hΔη
  have hΔg : Δ ≤ ‖g‖ / (1 + ‖H‖) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hcau := neg_quadModel_cauchy_ge ht
  rw [min_eq_right hΔg] at hcau
  refine le_reductionRatio_trust_first hC hf hL hx hxs hH hs hΔ hg (by linarith) ?_
  nlinarith

/-- **Lemma 3.2.4** ([cartis2022evaluation]), book form. Let `∇²f` be `L`-Lipschitz (`L > 0`) on a
convex `C ∋ x, x + s` (`f` `C²` there), let `u` be a direction of negative curvature
`⟪u, ∇²f(x) u⟫ = λ < 0` (e.g. a unit eigenvector of `λ_min[∇²f(x)]`) with `⟪∇f(x), u⟫ ≤ 0`, and let
the step lie in the trust region (`‖s‖ ≤ Δ`, `Δ > 0`) and satisfy the eigenpoint condition
(3.2.10) `T_{f,2}(x, s) ≤ T_{f,2}(x, Δ u)`. If (3.2.16) `Δ < 3 (1 - η) |λ| / L`, then `ρ ≥ η`. -/
theorem le_reductionRatio_trust_second_of_curvature (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ 2 f y) (hL : IteratedFDerivLipschitzOn f 2 L C) (hL0 : 0 < L)
    (hx : x ∈ C) (hxs : x + s ∈ C) {u : E} {lam : ℝ}
    (hHu : ⟪u, hessianOperator f x u⟫ = lam) (hlam : lam < 0) (hgu : ⟪gradient f x, u⟫ ≤ 0)
    (hsE : quadModel (gradient f x) (hessianOperator f x) s ≤
      quadModel (gradient f x) (hessianOperator f x) (Δ • u))
    (hs : ‖s‖ ≤ Δ) (hΔ : 0 < Δ) {η : ℝ} (hΔη : Δ < 3 * (1 - η) * |lam| / L) :
    η ≤ reductionRatio f x s (-quadModel (gradient f x) (hessianOperator f x) s) := by
  have hE := le_neg_quadModel_smul_of_curvature hHu hlam.le hgu hΔ.le
  rw [lt_div_iff₀ hL0] at hΔη
  exact le_reductionRatio_trust_second hC hf hL hx hxs hs hΔ hlam (by linarith) (by linarith)

end Taylor

section Existence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A global minimizer of the model on the trust region satisfies the Cauchy decrease condition
(2.3.4) for every Cauchy step and the eigenpoint condition (3.2.10) for every unit direction. -/
theorem quadModel_le_of_isMinOn_ball {g : E} {H : E →L[ℝ] E} {Δ : ℝ} {s : E}
    (hmin : IsMinOn (quadModel g H) (closedBall 0 Δ) s) :
    (∀ t, IsCauchyStep g H Δ t → quadModel g H s ≤ quadModel g H (-(t • g))) ∧
      (0 ≤ Δ → ∀ u, ‖u‖ = 1 → quadModel g H s ≤ quadModel g H (Δ • u)) := by
  refine ⟨fun t ht => hmin ?_, fun hΔ u hu => hmin ?_⟩
  · rw [mem_closedBall_zero_iff, norm_neg, norm_smul, Real.norm_of_nonneg ht.1]
    exact ht.2.1
  · rw [mem_closedBall_zero_iff, norm_smul, hu, mul_one, Real.norm_of_nonneg hΔ]

/-- In finite dimension the model attains its minimum on the trust region `‖s‖ ≤ Δ`, `Δ ≥ 0`,
and the minimizer satisfies the Cauchy and eigenpoint conditions (existence of the steps of
TR1, TR2; [cartis2022evaluation], Section 3.2.1). -/
theorem exists_isMinOn_quadModel_ball [FiniteDimensional ℝ E] (g : E) (H : E →L[ℝ] E) {Δ : ℝ}
    (hΔ : 0 ≤ Δ) :
    ∃ s, ‖s‖ ≤ Δ ∧ IsMinOn (quadModel g H) (closedBall 0 Δ) s ∧
      (∀ t, IsCauchyStep g H Δ t → quadModel g H s ≤ quadModel g H (-(t • g))) ∧
      (∀ u, ‖u‖ = 1 → quadModel g H s ≤ quadModel g H (Δ • u)) := by
  obtain ⟨s, hs, hmin⟩ := exists_isMinOn_closedBall g H hΔ
  exact ⟨s, hs, hmin, (quadModel_le_of_isMinOn_ball hmin).1,
    (quadModel_le_of_isMinOn_ball hmin).2 hΔ⟩

end Existence

end Optimization
