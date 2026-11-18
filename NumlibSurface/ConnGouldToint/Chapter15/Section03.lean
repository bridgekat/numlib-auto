/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter11.Section03
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import NumlibSurface.ConnGouldToint.Chapter15.Section02
import NumlibSurface.ConnGouldToint.Chapter06.Section01

/-!
# Conn, Gould and Toint, Section 15.3: SQP with an exact penalty function

This module formalizes Section 15.3 of [conn2000trust], which globalizes SQP with the nonsmooth
exact penalty function
$$\phi(x) = f(x) + \sigma\, \operatorname{dist}(c(x), C) \quad (15.3.3)$$
and the model $m(s) = f(x) + \langle g(x), s\rangle + \frac12 \langle s, H s\rangle + \sigma\,
\operatorname{dist}(c(x) + A(x) s, C)$ (15.3.4). Here $C$ is the set of feasible constraint values,
so that $\operatorname{dist}(c(x), C)$ is the norm of the constraint violation in the Euclidean
case. The global theory runs the nonsmooth trust-region algorithm of Chapter 11 on these functions:
the models agree uniformly with the merit function, and a limit point of a run is first-order
critical (Theorem 15.3.1). For a large enough penalty, first- and second-order criticality for the
penalty problem agree with those of the constrained problem (Theorem 15.3.2). The local theory shows
that SQP steps are quadratically accurate (Lemma 15.3.3), that the penalty function grows
quadratically near a strict solution (Lemma 15.3.4), and that the merit ratio of a step with a
second-order correction tends to one (Lemmas 15.3.5–15.3.6 and Theorem 15.3.7). The nonsmooth
algorithm is in `NumlibSurface.ConnGouldToint.Chapter11.Section03`, and the SQP equations are those
of `NumlibSurface.ConnGouldToint.Chapter15.Section02`.

## Main definitions

* Equation (15.3.3), `ConnGouldToint.Chapter15.sqpDistanceMerit`: the exact penalty function in
  distance form.
* Equation (15.3.4), `ConnGouldToint.Chapter15.sqpDistanceModel`: the model in distance form.
* Algorithm 15.3.1, Step 2a, `ConnGouldToint.Chapter15.sqpDistanceCorrectionModel`: the model of the
  second-order correction.
* Algorithm 15.3.1, `ConnGouldToint.Chapter15.algorithm_15_3_1`: Step 2 of the nonsmooth algorithm
  with the exact-penalty models and an optional correction.

## Main results

* Theorem 15.3.1, `ConnGouldToint.Chapter15.sqpDistanceModel_uniform_agreement`: quadratic Taylor
  bounds give uniform agreement of the models with the merit function.
* Theorem 15.3.1, `ConnGouldToint.Chapter15.theorem_15_3_1`: a limit point of a run is first-order
  critical for the constrained problem.
* Equations (15.3.7)–(15.3.8), `ConnGouldToint.Chapter15.sqp_penalty_support_iff`: the supporting
  functionals of the penalty term at a feasible point are the normal functionals of norm at most
  $\sigma$.
* Theorem 15.3.2, `ConnGouldToint.Chapter15.theorem_15_3_2_first_order`: first-order criticality for
  the penalty problem and for the constrained problem agree.
* Theorem 15.3.2, `ConnGouldToint.Chapter15.theorem_15_3_2_second_order`: under strict exactness,
  the second-order conditions agree.
* Lemma 15.3.3, `ConnGouldToint.Chapter15.lemma_15_3_3`: the SQP step has primal error of order
  (primal error) $\times$ (joint error).
* Lemma 15.3.3, `ConnGouldToint.Chapter15.sqp_C2_newton_counterexample`: twice continuous
  differentiability alone does not give the quadratic estimate.
* Lemma 15.3.4, `ConnGouldToint.Chapter15.lemma_15_3_4`: the penalty function grows quadratically
  near a strict solution.
* Equations (15.3.35) and (15.3.45), `ConnGouldToint.Chapter15.sqp_model_target_error`: stationarity
  cancels the linear term of the model error.
* Lemma 15.3.5, `ConnGouldToint.Chapter15.lemma_15_3_5`: the predicted and the actual reduction to
  the solution agree up to (primal error)$^2 \times$ (joint error).
* Lemma 15.3.6, `ConnGouldToint.Chapter15.lemma_15_3_6`: the same for the step with a second-order
  correction.
* Theorem 15.3.7, `ConnGouldToint.Chapter15.theorem_15_3_7`: at positive primal error, the corrected
  merit ratio differs from one by order of the joint error.
* Algorithm 15.3.1, `ConnGouldToint.Chapter15.infDist_eq_mixed_violation_norm`: in the Euclidean
  case the distance to $C$ is the norm of the violation vector.

## Implementation notes

* The quantitative Taylor hypotheses supply the remainder orders used in the source. Continuity of
  the second derivatives alone gives second-order remainders of order $o(\|s\|^2)$, and locally
  Lipschitz second derivatives give the cubic remainders used for the reduction ratio.
* The local estimates are stated for real numbers and vectors that stand for the values of the
  functions at the current point, the trial and the solution. Their relation to a run is not part of
  the statements.
* The norm on a product $E \times Y$ is the maximum of the norms of the two components.

## Deviations from the source

* **Equations (15.3.3)–(15.3.4)** (generalization). The penalty is the distance of the constraint
  value to a set $C$ of feasible values. For Euclidean equality and one-sided inequality residuals,
  this is the norm of the violation vector. See `ConnGouldToint.Chapter15.sqpDistanceMerit` and
  `ConnGouldToint.Chapter15.infDist_eq_mixed_violation_norm`.
* **Theorem 15.3.1** (reading). The Clarke chain-rule inclusion for the merit function at the limit
  point is a hypothesis. A multiplier is not assumed to exist. See
  `ConnGouldToint.Chapter15.theorem_15_3_1`.
* **Theorem 15.3.2** (reading). The two parts are stated in normal-functional and in tangent-cone
  form. See `ConnGouldToint.Chapter15.theorem_15_3_2_first_order` and
  `ConnGouldToint.Chapter15.theorem_15_3_2_second_order`.
* **Lemma 15.3.3** (correction). Twice continuous differentiability does not give the quadratic
  estimate. The Taylor expansion of the KKT residual is a quantitative hypothesis. See
  `ConnGouldToint.Chapter15.lemma_15_3_3` and
  `ConnGouldToint.Chapter15.sqp_C2_newton_counterexample`.
* **Lemma 15.3.4** (reading). The hypotheses are a local feasible restoration with a linear residual
  bound and strict exactness of the penalty. See `ConnGouldToint.Chapter15.lemma_15_3_4`.
* **Lemmas 15.3.5 and 15.3.6** (reading). The Taylor remainders are quantitative hypotheses. See
  `ConnGouldToint.Chapter15.lemma_15_3_5` and `ConnGouldToint.Chapter15.lemma_15_3_6`.
* **Theorem 15.3.7** (correction). The ratio estimate needs positive primal error, since the
  reduction can vanish at the solution. See `ConnGouldToint.Chapter15.theorem_15_3_7`.
-/

open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter15

variable {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- **Lemma 15.3.3** of [conn2000trust], quantitative form. Let $E$ be a real inner product space
and $Y$ a real normed space. Let $(x, y) \in E \times Y$ with $K(x, y)$ invertible and
$\|K(x, y)^{-1}\| \le M$ for some $M \ge 0$, and let $(s, y + \delta y)$ satisfy the SQP
equations at $(x, y)$. Let $(x_*, y_*) \in E \times Y$, write $e = \|(x, y) - (x_*, y_*)\|$, and
suppose that
$$\|R(x, y_*) + K(x, y)(x_* - x, 0)\| \le L \|x - x_*\|\, e.$$
Then
$$\|x + s - x_*\| \le M L \|x - x_*\|\, e, \qquad \|s\| \le (1 + M L e) \|x - x_*\|, \qquad
  \|\delta y\| \le (1 + M L \|x - x_*\|)\, e.$$

**Correction.** The source derives the quadratic estimate from twice continuously differentiable
data. This is not enough: `ConnGouldToint.Chapter15.sqp_C2_newton_counterexample` gives a $C^2$
example without a quadratic bound on the Newton error. Here the Taylor expansion of the KKT
residual is a hypothesis.

The residual is expanded at the solution multiplier $y_*$, which makes the defect proportional
to the primal error times the joint error. $R$ and $K$ are
`ConnGouldToint.Chapter15.sqpResidual` and `ConnGouldToint.Chapter15.sqpKKT`, and the
invertibility is a continuous linear equivalence `B` equal to $K(x, y)$. -/
theorem lemma_15_3_3
    (g : E → E) (c : E → Y) (H : E × Y → E →L[ℝ] E)
    (A : E → E →L[ℝ] Y) (AT : E → Y →L[ℝ] E)
    (x xstar s : E) (y ystar dy : Y)
    (B : (E × Y) ≃L[ℝ] (E × Y))
    (hB : (B : E × Y →L[ℝ] E × Y) = sqpKKT H A AT (x, y))
    (hstep : IsSQPCorrection g c H A AT (x, y) s (y + dy))
    {M L : ℝ} (hM : 0 ≤ M)
    (hinv : ‖(B.symm : E × Y →L[ℝ] E × Y)‖ ≤ M)
    (hTaylor :
      ‖sqpResidual g c AT (x, ystar) + B (xstar - x, 0)‖ ≤
        L * (‖x - xstar‖ * ‖(x, y) - (xstar, ystar)‖)) :
    ‖x + s - xstar‖ ≤ M * L * (‖x - xstar‖ * ‖(x, y) - (xstar, ystar)‖) ∧
    ‖s‖ ≤ (1 + M * L * ‖(x, y) - (xstar, ystar)‖) * ‖x - xstar‖ ∧
    ‖dy‖ ≤ (1 + M * L * ‖x - xstar‖) * ‖(x, y) - (xstar, ystar)‖ := by
  let z : E × Y := (x + s - xstar, y + dy - ystar)
  have hnewton := (isSQPCorrection_iff_newton g c H A AT (x, y) s dy).mp hstep
  have hdelta : B z = -(sqpResidual g c AT (x, ystar) + B (xstar - x, 0)) := by
    have hstep' : B (s, dy) = -sqpResidual g c AT (x, y) := by
      change (B : E × Y →L[ℝ] E × Y) (s, dy) = _
      rwa [hB]
    have hshift : B (0, y - ystar) =
        sqpResidual g c AT (x, y) - sqpResidual g c AT (x, ystar) := by
      change (B : E × Y →L[ℝ] E × Y) (0, y - ystar) = _
      rw [hB]
      ext
      · simp [sqpKKT, sqpResidual]
      · simp [sqpKKT, sqpResidual]
    have hz : z = (s, dy) - (xstar - x, 0) + (0, y - ystar) := by
      apply Prod.ext <;> dsimp [z] <;> abel
    rw [hz, map_add, map_sub, hstep', hshift]
    abel
  have hnorm : ‖z‖ ≤ M * L * (‖x - xstar‖ * ‖(x, y) - (xstar, ystar)‖) := by
    calc
      _ = ‖B.symm (B z)‖ := by rw [B.symm_apply_apply]
      _ ≤ ‖(B.symm : E × Y →L[ℝ] E × Y)‖ * ‖B z‖ :=
        (B.symm : E × Y →L[ℝ] E × Y).le_opNorm _
      _ ≤ M * ‖B z‖ := mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
      _ ≤ _ := by rw [hdelta, norm_neg, mul_assoc]; exact mul_le_mul_of_nonneg_left hTaylor hM
  have hx : ‖x + s - xstar‖ ≤ ‖z‖ := norm_fst_le z
  have hy : ‖y + dy - ystar‖ ≤ ‖z‖ := norm_snd_le z
  refine ⟨hx.trans hnorm, ?_, ?_⟩
  · calc
      _ = ‖(x + s - xstar) - (x - xstar)‖ := by congr 1; abel
      _ ≤ ‖x + s - xstar‖ + ‖x - xstar‖ := norm_sub_le _ _
      _ ≤ _ := by linarith only [hx.trans hnorm,
        show (1 + M * L * ‖(x, y) - (xstar, ystar)‖) * ‖x - xstar‖ =
          M * L * (‖x - xstar‖ * ‖(x, y) - (xstar, ystar)‖) + ‖x - xstar‖ by ring]
  · have hys : ‖y - ystar‖ ≤ ‖(x, y) - (xstar, ystar)‖ :=
      norm_snd_le ((x, y) - (xstar, ystar))
    calc
      _ = ‖(y + dy - ystar) - (y - ystar)‖ := by congr 1; abel
      _ ≤ ‖y + dy - ystar‖ + ‖y - ystar‖ := norm_sub_le _ _
      _ ≤ _ := by linarith only [hy.trans hnorm, hys,
        show (1 + M * L * ‖x - xstar‖) * ‖(x, y) - (xstar, ystar)‖ =
          M * L * (‖x - xstar‖ * ‖(x, y) - (xstar, ystar)‖) +
            ‖(x, y) - (xstar, ystar)‖ by ring]

omit [InnerProductSpace ℝ E] [NormedSpace ℝ Y] in
/-- **Lemma 15.3.4** of [conn2000trust], local restoration form. Let $E$ and $Y$ be normed groups,
$f : E \to \mathbb{R}$, $c : E \to Y$ and $x_* \in E$. Let $r, \kappa, K, L, \sigma$ be real
numbers with $\kappa > 0$, $K \ge 0$ and $L K < \sigma$. Suppose that:

* for every $x$ with $\|x - x_*\| < r$ there is $p$ with $c(p) = 0$, $\|p - x_*\| < r$,
  $\|x - p\| \le K \|c(x)\|$, $\|x - p\| \le 1$ and $f(p) - f(x) \le L K \|c(x)\|$;
* $\kappa \|p - x_*\|^2 \le f(p) - f(x_*)$ for every $p$ with $c(p) = 0$ and $\|p - x_*\| < r$.

Then there is $a > 0$ with
$$a \|x - x_*\|^2 \le f(x) + \sigma \|c(x)\| - f(x_*)$$
for every $x$ with $\|x - x_*\| < r$.

**Reading.** The hypotheses are a local feasible restoration with a linear residual bound and
the strict exactness $LK < \sigma$ of the penalty, which controls the restoration displacement. -/
theorem lemma_15_3_4 (f : E → ℝ) (c : E → Y) (xstar : E)
    {r κ K L σ : ℝ} (hκ : 0 < κ) (hK : 0 ≤ K)
    (hσ : L * K < σ)
    (hrest : ∀ x, ‖x - xstar‖ < r → ∃ p, c p = 0 ∧ ‖p - xstar‖ < r ∧
      ‖x - p‖ ≤ K * ‖c x‖ ∧ ‖x - p‖ ≤ 1 ∧ f p - f x ≤ L * ‖c x‖ * K)
    (hgrowth : ∀ p, c p = 0 → ‖p - xstar‖ < r → κ * ‖p - xstar‖ ^ 2 ≤ f p - f xstar) :
    ∃ a > 0, ∀ x, ‖x - xstar‖ < r → a * ‖x - xstar‖ ^ 2 ≤ f x + σ * ‖c x‖ - f xstar := by
  let a := min (κ / 2) ((σ - L * K) / (2 * (K + 1)))
  have ha : 0 < a := lt_min (half_pos hκ) (div_pos (sub_pos.mpr hσ) (by positivity))
  refine ⟨a, ha, fun x hx => ?_⟩
  obtain ⟨p, hp, hpr, hxp, hsmall, hf⟩ := hrest x hx
  have hdist : ‖x - xstar‖ ≤ ‖x - p‖ + ‖p - xstar‖ := by
    rw [← show (x - p) + (p - xstar) = x - xstar by abel]
    exact norm_add_le _ _
  have hsq : ‖x - xstar‖ ^ 2 ≤ 2 * (‖x - p‖ ^ 2 + ‖p - xstar‖ ^ 2) :=
    (pow_le_pow_left₀ (norm_nonneg _) hdist 2).trans (by
      nlinarith only [sq_nonneg (‖x - p‖ - ‖p - xstar‖)])
  have hlin : ‖x - p‖ ^ 2 ≤ (K + 1) * ‖c x‖ := by
    calc
      _ ≤ ‖x - p‖ := by nlinarith only [mul_nonneg (norm_nonneg (x - p)) (sub_nonneg.mpr hsmall)]
      _ ≤ K * ‖c x‖ := hxp
      _ ≤ _ := by linarith only [norm_nonneg (c x)]
  have ha₁ : 2 * a ≤ κ := by
    have := min_le_left (κ / 2) ((σ - L * K) / (2 * (K + 1)))
    linarith only [this]
  have ha₂ : (2 * a) * (K + 1) ≤ σ - L * K := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * (K + 1))).mp
      (min_le_right (κ / 2) ((σ - L * K) / (2 * (K + 1))))
    linarith only [show (2 * a) * (K + 1) = a * (2 * (K + 1)) by ring, h]
  have h₁ := mul_le_mul_of_nonneg_right ha₁ (sq_nonneg ‖p - xstar‖)
  have h₂ := mul_le_mul_of_nonneg_left hlin (show 0 ≤ 2 * a by positivity)
  have h₃ := mul_le_mul_of_nonneg_right ha₂ (norm_nonneg (c x))
  have h₄ := mul_le_mul_of_nonneg_left hsq ha.le
  nlinarith only [h₁, h₂, h₃, h₄, hf, hgrowth p hp hpr]

/-! ### Local model estimates -/

section Taylor

variable {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]

/-- **Equations (15.3.35) and (15.3.45)** of [conn2000trust], cancellation. Let $E$ and $Z$ be real
inner product spaces, $H : E \to E$ symmetric, $A : E \to Z$, $g, s, t \in E$,
$c_0, c_z, y \in Z$ and $f_0, f_z, \sigma, T \in \mathbb{R}$ with $\|y\| \le \sigma$. Let
$q(t) = f_0 + \langle g, t\rangle + \frac12 \langle t, H t\rangle$. Suppose that
$c_0 + A s = 0$, that $\langle g + H s, d\rangle = \langle y, A d\rangle$ for all $d \in E$, and
that
$$\big|f_z - \langle y, c_z\rangle - \big(q(t) - \langle y, c_0 + A t\rangle\big)\big| \le T.$$
Then
$$|f_z + \sigma \|c_z\| - q(s)| \le T + \tfrac12 \|H\| \|t - s\|^2 + 2\sigma \|c_z\|.$$
KKT stationarity at the model step $s$ cancels the linear part of the difference between $q(s)$
and $q(t)$ at a nearby target $t$. -/
theorem sqp_model_target_error (f₀ fz : ℝ) (g s t : E) (H : E →L[ℝ] E)
    (A : E →L[ℝ] Z) (c₀ cz y : Z) {σ T : ℝ}
    (hH : H.toLinearMap.IsSymmetric) (hσ : ‖y‖ ≤ σ)
    (hfeas : c₀ + A s = 0)
    (hstat : ∀ d : E, ⟪g + H s, d⟫ = ⟪y, A d⟫)
    (hTaylor : |fz - ⟪y, cz⟫ -
      (Chapter06.quadraticModel f₀ g H.toLinearMap t - ⟪y, c₀ + A t⟫)| ≤ T) :
    |fz + σ * ‖cz‖ - Chapter06.quadraticModel f₀ g H.toLinearMap s| ≤
      T + (1 / 2) * ‖H‖ * ‖t - s‖ ^ 2 + 2 * σ * ‖cz‖ := by
  let d := t - s
  let q := Chapter06.quadraticModel f₀ g H.toLinearMap
  have ht : t = s + d := by dsimp [d]; abel
  have hmodel : q t - ⟪y, c₀ + A t⟫ = q s + (1 / 2) * ⟪d, H d⟫ := by
    have hc : c₀ + A t = A d := by rw [ht, map_add, ← add_assoc, hfeas, zero_add]
    have hs : ⟪s, H d⟫ = ⟪H s, d⟫ := (hH s d).symm
    have h := hstat d
    rw [inner_add_left] at h
    rw [hc, ht]
    dsimp only [q, Chapter06.quadraticModel, ContinuousLinearMap.coe_coe]
    simp only [map_add, inner_add_right, inner_add_left, hs, real_inner_comm d (H s)]
    rw [real_inner_comm d (H s)] at h
    linarith only [h]
  change |fz - ⟪y, cz⟫ - (q t - ⟪y, c₀ + A t⟫)| ≤ T at hTaylor
  rw [hmodel] at hTaylor
  have hcurv : |(1 / 2 : ℝ) * ⟪d, H d⟫| ≤ (1 / 2) * ‖H‖ * ‖d‖ ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    calc
      _ ≤ (1 / 2) * (‖d‖ * ‖H d‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num)
      _ ≤ (1 / 2) * (‖d‖ * (‖H‖ * ‖d‖)) := by gcongr; exact H.le_opNorm d
      _ = _ := by ring
  have hpen : |⟪y, cz⟫ + σ * ‖cz‖| ≤ 2 * σ * ‖cz‖ := by
    have hσ₀ := (norm_nonneg y).trans hσ
    have hy := (abs_real_inner_le_norm y cz).trans
      (mul_le_mul_of_nonneg_right hσ (norm_nonneg cz))
    calc
      _ ≤ |⟪y, cz⟫| + |σ * ‖cz‖| := abs_add_le _ _
      _ ≤ _ := by rw [abs_of_nonneg (mul_nonneg hσ₀ (norm_nonneg cz))]; linarith only [hy]
  change |fz + σ * ‖cz‖ - q s| ≤ _
  rw [show fz + σ * ‖cz‖ - q s =
    (fz - ⟪y, cz⟫ - (q s + (1 / 2) * ⟪d, H d⟫)) +
      (1 / 2) * ⟪d, H d⟫ + (⟪y, cz⟫ + σ * ‖cz‖) by ring]
  exact (abs_add_le _ _).trans
    (add_le_add ((abs_add_le _ _).trans (add_le_add hTaylor hcurv)) hpen)

private theorem sqp_curvature_error {d : E} {H : E →L[ℝ] E} {D B ex e : ℝ}
    (he : e ∈ Set.Icc (0 : ℝ) 1)
    (hstep : ‖d‖ ≤ D * ex * e) (hB : ‖H‖ ≤ B) :
    (1 / 2) * ‖H‖ * ‖d‖ ^ 2 ≤ (1 / 2) * B * D ^ 2 * (ex ^ 2 * e) := by
  have hsq : ‖d‖ ^ 2 ≤ D ^ 2 * (ex ^ 2 * e) := calc
    _ ≤ (D * ex * e) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hstep 2
    _ = (D ^ 2 * ex ^ 2) * (e * e) := by ring
    _ ≤ (D ^ 2 * ex ^ 2) * e :=
      mul_le_mul_of_nonneg_left (mul_le_of_le_one_right he.1 he.2) (by positivity)
    _ = _ := by ring
  have hb := mul_le_mul hB hsq (sq_nonneg _) ((norm_nonneg H).trans hB)
  linarith only [hb, show (1 / 2 : ℝ) * B * D ^ 2 * (ex ^ 2 * e) =
    (1 / 2) * (B * (D ^ 2 * (ex ^ 2 * e))) by ring]

/-- **Lemma 15.3.5** of [conn2000trust], with quantitative Taylor remainders. Let $E$, $Z$, $H$,
$A$, $g$, $s$, $t$, $c_0$, $y$, $f_0$, $\sigma$, $T$ and $q$ be as in
`ConnGouldToint.Chapter15.sqp_model_target_error`, with $H$ symmetric, $\|y\| \le \sigma$,
$c_0 + A s = 0$ and $\langle g + H s, d\rangle = \langle y, A d\rangle$ for all $d \in E$. Let
$\varphi, \varphi_*, D, B, e_x \in \mathbb{R}$ and $e \in [0, 1]$, and suppose that
$\|t - s\| \le D e_x e$, $\|H\| \le B$ and
$$\big|\varphi_* - \big(q(t) - \langle y, c_0 + A t\rangle\big)\big| \le T e_x^2 e.$$
Then
$$\big|(\varphi - \varphi_*) - (\varphi - q(s))\big| \le \big(T + \tfrac12 B D^2\big)\, e_x^2
  e.$$

**Reading.** The Taylor remainder is a quantitative hypothesis.

In the application, $\varphi$ is the merit value at the current point, $\varphi_*$ the merit
value at the solution, $t$ the displacement to the solution, $e_x$ the primal error and $e$ the
joint error. The conclusion compares the actual reduction $\varphi - \varphi_*$ with the
predicted reduction $\varphi - q(s)$. -/
theorem lemma_15_3_5 (φ φstar f₀ : ℝ) (g s t : E) (H : E →L[ℝ] E)
    (A : E →L[ℝ] Z) (c₀ y : Z) {σ T D B ex e : ℝ}
    (hH : H.toLinearMap.IsSymmetric) (hσ : ‖y‖ ≤ σ)
    (hfeas : c₀ + A s = 0)
    (hstat : ∀ d : E, ⟪g + H s, d⟫ = ⟪y, A d⟫)
    (he : e ∈ Set.Icc (0 : ℝ) 1)
    (hstep : ‖t - s‖ ≤ D * ex * e) (hB : ‖H‖ ≤ B)
    (hTaylor : |φstar -
      (Chapter06.quadraticModel f₀ g H.toLinearMap t - ⟪y, c₀ + A t⟫)| ≤ T * (ex ^ 2 * e)) :
    |(φ - φstar) - (φ - Chapter06.quadraticModel f₀ g H.toLinearMap s)| ≤
      (T + (1 / 2) * B * D ^ 2) * (ex ^ 2 * e) := by
  have h := sqp_model_target_error f₀ φstar g s t H A c₀ 0 y hH hσ hfeas hstat
    (by simpa only [inner_zero_right, sub_zero] using hTaylor)
  simp only [norm_zero, mul_zero, add_zero] at h
  rw [show (φ - φstar) - (φ - Chapter06.quadraticModel f₀ g H.toLinearMap s) =
    -(φstar - Chapter06.quadraticModel f₀ g H.toLinearMap s) by ring, abs_neg]
  exact h.trans (by
    linarith only [sqp_curvature_error he hstep hB,
      show (T + (1 / 2) * B * D ^ 2) * (ex ^ 2 * e) =
        T * (ex ^ 2 * e) + (1 / 2) * B * D ^ 2 * (ex ^ 2 * e) by ring])

/-- **Lemma 15.3.6** of [conn2000trust], with quantitative Taylor remainders. Let $E$, $Z$, $H$,
$A$, $g$, $s$, $c_0$, $c_z$, $y$, $f_0$, $f_z$, $\sigma$, $T$ and $q$ be as in
`ConnGouldToint.Chapter15.sqp_model_target_error`, with $H$ symmetric, $\|y\| \le \sigma$,
$c_0 + A s = 0$ and $\langle g + H s, d\rangle = \langle y, A d\rangle$ for all $d \in E$. Let
$u \in E$ be a correction, $A_p, A_s : E \to Z$, $c_s \in Z$, and
$\varphi, D, B, R, J, e_x \in \mathbb{R}$ with $e_x \ge 0$, $J \ge 0$ and $e \in [0, 1]$.
Suppose that $\|u\| \le D e_x e$, $\|H\| \le B$, $c_s + A_p u = 0$, $\|A_s - A_p\| \le J e_x$,
$\|c_z - (c_s + A_s u)\| \le R e_x^2 e$ and
$$\big|f_z - \langle y, c_z\rangle - \big(q(s + u) - \langle y, c_0 + A(s + u)\rangle\big)\big|
  \le T e_x^2 e.$$
Then
$$\big|(\varphi - (f_z + \sigma\|c_z\|)) - (\varphi - q(s))\big| \le \big(T + \tfrac12 B D^2 +
  2\sigma (R + J D)\big)\, e_x^2 e.$$

**Reading.** The Taylor remainders are quantitative hypotheses.

The correction solves the linearized constraint at the trial with the Jacobian $A_p$, which
differs from the Jacobian $A_s$ at the corrected point by $O(e_x)$. The value
$f_z + \sigma\|c_z\|$ is the merit value at the corrected point. -/
theorem lemma_15_3_6 (φ f₀ fz : ℝ) (g s u : E) (H : E →L[ℝ] E)
    (A Ap As : E →L[ℝ] Z) (c₀ cs cz y : Z) {σ T D B R J ex e : ℝ}
    (hH : H.toLinearMap.IsSymmetric) (hσ : ‖y‖ ≤ σ)
    (hfeas : c₀ + A s = 0)
    (hstat : ∀ d : E, ⟪g + H s, d⟫ = ⟪y, A d⟫)
    (hex : 0 ≤ ex) (he : e ∈ Set.Icc (0 : ℝ) 1) (hJ : 0 ≤ J)
    (hstep : ‖u‖ ≤ D * ex * e) (hB : ‖H‖ ≤ B)
    (hCS : cs + Ap u = 0)
    (hJac : ‖As - Ap‖ ≤ J * ex)
    (hTaylorC : ‖cz - (cs + As u)‖ ≤ R * (ex ^ 2 * e))
    (hTaylor : |fz - ⟪y, cz⟫ -
      (Chapter06.quadraticModel f₀ g H.toLinearMap (s + u) - ⟪y, c₀ + A (s + u)⟫)| ≤
      T * (ex ^ 2 * e)) :
    |(φ - (fz + σ * ‖cz‖)) - (φ - Chapter06.quadraticModel f₀ g H.toLinearMap s)| ≤
      (T + (1 / 2) * B * D ^ 2 + 2 * σ * (R + J * D)) * (ex ^ 2 * e) := by
  have h := sqp_model_target_error f₀ fz g s (s + u) H A c₀ cz y hH hσ hfeas hstat hTaylor
  rw [add_sub_cancel_left] at h
  rw [show (φ - (fz + σ * ‖cz‖)) - (φ - Chapter06.quadraticModel f₀ g H.toLinearMap s) =
    -(fz + σ * ‖cz‖ - Chapter06.quadraticModel f₀ g H.toLinearMap s) by ring, abs_neg]
  have hcz : ‖cz‖ ≤ (R + J * D) * (ex ^ 2 * e) := by
    have hc : cs + As u = (As - Ap) u := by
      rw [sub_apply]
      rw [show cs = -(Ap u) by exact eq_neg_of_add_eq_zero_left hCS]
      abel
    calc
      _ = ‖(cz - (cs + As u)) + (cs + As u)‖ := by rw [sub_add_cancel]
      _ ≤ ‖cz - (cs + As u)‖ + ‖cs + As u‖ := norm_add_le _ _
      _ ≤ R * (ex ^ 2 * e) + (J * ex) * (D * ex * e) := by
        apply add_le_add hTaylorC
        rw [hc]
        exact ((As - Ap).le_opNorm _).trans
          (mul_le_mul hJac hstep (norm_nonneg _) (mul_nonneg hJ hex))
      _ = _ := by ring
  exact h.trans (by
    have hp := mul_le_mul_of_nonneg_left hcz
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ((norm_nonneg y).trans hσ))
    linarith only [sqp_curvature_error he hstep hB, hp,
      show (T + (1 / 2) * B * D ^ 2 + 2 * σ * (R + J * D)) * (ex ^ 2 * e) =
        T * (ex ^ 2 * e) + (1 / 2) * B * D ^ 2 * (ex ^ 2 * e) +
          2 * σ * ((R + J * D) * (ex ^ 2 * e)) by ring])

end Taylor

/-- **Theorem 15.3.7** of [conn2000trust]. Let $a > 0$, $T \ge 0$, $e_x > 0$, $e \ge 0$ and $K$ be
real numbers with $K e \le a/2$, and let $\varphi, \varphi_*, \varphi_c, \mathrm{pred} \in
\mathbb{R}$. Suppose that
$$a e_x^2 \le \varphi - \varphi_*, \qquad |(\varphi - \varphi_*) - \mathrm{pred}| \le K e_x^2 e,
  \qquad |(\varphi - \varphi_c) - \mathrm{pred}| \le T e_x^2 e.$$
Then $\mathrm{pred} > 0$ and
$$\Big|\frac{\varphi - \varphi_c}{\mathrm{pred}} - 1\Big| \le \frac{2T}{a}\, e.$$

**Correction.** The estimate needs positive primal error $e_x > 0$. At the solution the
reduction can vanish, and the ratio is then not controlled.

In the application, $\varphi_c$ is the merit value at the corrected trial, $e_x$ the primal
error and $e$ the joint error. The first hypothesis is a quadratic growth bound such as that of
`ConnGouldToint.Chapter15.lemma_15_3_4`, and the other two have the form of the conclusions of
`ConnGouldToint.Chapter15.lemma_15_3_5` and `ConnGouldToint.Chapter15.lemma_15_3_6`. -/
theorem theorem_15_3_7 {φ φstar φcorrected predicted a K T ex e : ℝ}
    (ha : 0 < a) (hT : 0 ≤ T) (hex : 0 < ex) (he : 0 ≤ e)
    (hsmall : K * e ≤ a / 2)
    (hgrowth : a * ex ^ 2 ≤ φ - φstar)
    (hmodel : |(φ - φstar) - predicted| ≤ K * (ex ^ 2 * e))
    (hcorrected : |(φ - φcorrected) - predicted| ≤ T * (ex ^ 2 * e)) :
    0 < predicted ∧ |(φ - φcorrected) / predicted - 1| ≤ (2 * T / a) * e := by
  have hhalf : (a / 2) * ex ^ 2 ≤ predicted := by
    have h₁ := (le_abs_self ((φ - φstar) - predicted)).trans hmodel
    have h₂ := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ex)
    nlinarith only [h₁, h₂, hgrowth]
  have hpred : 0 < predicted := (mul_pos (half_pos ha) (pow_pos hex _)).trans_le hhalf
  refine ⟨hpred, ?_⟩
  rw [show (φ - φcorrected) / predicted - 1 = (φ - φcorrected - predicted) / predicted by
    field_simp, abs_div, abs_of_pos hpred]
  apply (div_le_iff₀ hpred).mpr
  refine hcorrected.trans ?_
  have h := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ (2 * T / a) * e by positivity)
  refine le_trans ?_ h
  apply le_of_eq
  field_simp

/-- **Lemma 15.3.3** of [conn2000trust], counterexample under $C^2$ alone. There is a twice
continuously differentiable $f : \mathbb{R} \to \mathbb{R}$ with $f'(0) = 0$ and $f''(0) = 1$
such that for every $C \ge 0$ and $\delta > 0$ there is $x \in (0, \delta)$ with $f''(x) > 0$
and
$$C x^2 < x - \frac{f'(x)}{f''(x)}.$$
The error of the Newton step from $x$ to the minimizer $0$ is therefore not $O(x^2)$. With a
zero-dimensional constraint space, this refutes the quadratic estimate of Lemma 15.3.3 under
$C^2$ data. -/
theorem sqp_C2_newton_counterexample :
    ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧ deriv f 0 = 0 ∧ deriv (deriv f) 0 = 1 ∧
      ∀ C δ : ℝ, 0 ≤ C → 0 < δ → ∃ x : ℝ, 0 < x ∧ x < δ ∧
        0 < deriv (deriv f) x ∧ C * x ^ 2 < x - deriv f x / deriv (deriv f) x := by
  let f (x : ℝ) := (1 / 2 : ℝ) * x ^ (2 : ℕ) + x ^ (5 / 2 : ℝ)
  have hf : ContDiff ℝ 2 f :=
    (contDiff_const.mul (contDiff_id.pow 2)).add
      (Real.contDiff_rpow_const_of_le (n := 2) (by norm_num))
  have hg : deriv f = fun x => x + (5 / 2 : ℝ) * x ^ (3 / 2 : ℝ) := by
    funext x
    have h₁ : HasDerivAt (fun z : ℝ => z ^ (2 : ℕ)) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have h₂ : HasDerivAt (fun z : ℝ => z ^ (5 / 2 : ℝ))
        ((5 / 2 : ℝ) * x ^ (3 / 2 : ℝ)) x := by
      convert (Real.hasDerivAt_rpow_const (x := x) (p := 5 / 2) (Or.inr (by norm_num))) using 1
      norm_num
    have h := ((h₁.const_mul (1 / 2 : ℝ)).fun_add h₂).deriv
    simpa only [f, one_div, inv_mul_cancel_left₀ (by norm_num : (2 : ℝ) ≠ 0)] using h
  have hH : deriv (deriv f) = fun x => 1 + (15 / 4 : ℝ) * x ^ (1 / 2 : ℝ) := by
    rw [hg]
    funext x
    have h₂ : HasDerivAt (fun z : ℝ => z ^ (3 / 2 : ℝ))
        ((3 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) x := by
      convert (Real.hasDerivAt_rpow_const (x := x) (p := 3 / 2) (Or.inr (by norm_num))) using 1
      norm_num
    have h := ((hasDerivAt_id x).fun_add (h₂.const_mul (5 / 2 : ℝ))).deriv
    rw [show (15 / 4 : ℝ) * x ^ (1 / 2 : ℝ) =
      (5 / 2 : ℝ) * ((3 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) by ring]
    exact h
  refine ⟨f, hf, ?_, ?_, ?_⟩
  · rw [hg]
    norm_num [Real.zero_rpow]
  · rw [hH]
    norm_num [Real.zero_rpow]
  intro C δ hC hδ
  let t := min (min 1 (δ / 2)) (1 / (8 * (C + 1)))
  have ht : 0 < t := lt_min (lt_min zero_lt_one (half_pos hδ)) (by positivity)
  have ht₁ : t ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have htδ : t ≤ δ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have htC : t ≤ 1 / (8 * (C + 1)) := min_le_right _ _
  have hr (p : ℝ) : (t ^ (2 : ℕ)) ^ p = t ^ ((2 : ℝ) * p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    norm_num
  have hr₁ : (t ^ (2 : ℕ)) ^ (1 / 2 : ℝ) = t := by rw [hr]; norm_num
  have hr₃ : (t ^ (2 : ℕ)) ^ (3 / 2 : ℝ) = t ^ (3 : ℕ) := by
    rw [hr, ← Real.rpow_natCast]
    norm_num
  refine ⟨t ^ (2 : ℕ), sq_pos_of_pos ht, ?_, ?_, ?_⟩
  · nlinarith only [htδ, hδ, mul_nonneg ht.le (sub_nonneg.mpr ht₁)]
  · simp only [hH, hr₁]
    positivity
  · rw [hH, hg]
    simp only [hr₁, hr₃]
    have hden : 0 < 1 + (15 / 4 : ℝ) * t := by positivity
    have hformula :
        t ^ (2 : ℕ) - (t ^ (2 : ℕ) + (5 / 2 : ℝ) * t ^ (3 : ℕ)) /
          (1 + (15 / 4 : ℝ) * t) =
        ((5 / 4 : ℝ) * t ^ (3 : ℕ)) / (1 + (15 / 4 : ℝ) * t) := by
      field_simp
      ring
    rw [hformula]
    apply (lt_div_iff₀ hden).mpr
    have hCt : C * t ≤ 1 / 8 := by
      have h := (le_div_iff₀ (by positivity : 0 < 8 * (C + 1))).mp htC
      nlinarith only [h, ht.le]
    have hmul := mul_le_mul hCt (show 1 + (15 / 4 : ℝ) * t ≤ 5 by linarith)
      hden.le (by norm_num : (0 : ℝ) ≤ 1 / 8)
    have hh := mul_lt_mul_of_pos_right
      (hmul.trans_lt (by norm_num : (1 / 8 : ℝ) * 5 < 5 / 4)) (pow_pos ht 3)
    nlinarith only [hh]

/-! ### Exactness of the penalty function -/

section ExactPenalty

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

omit [InnerProductSpace ℝ E] in
/-- **Equations (15.3.7)–(15.3.8)** of [conn2000trust], subgradients of the penalty term at a
feasible point. Let $Z$ be a real normed space, $C \subseteq Z$, $r \in C$, $\ell$ a continuous
linear functional on $Z$ and $\sigma \ge 0$. Then $\ell(z - r) \le \sigma \operatorname{dist}(z,
C)$ for all $z \in Z$ if and only if $\|\ell\| \le \sigma$ and $\ell(c - r) \le 0$ for all
$c \in C$. -/
theorem sqp_penalty_support_iff {C : Set Z} {r : Z} (hr : r ∈ C)
    (ell : Z →L[ℝ] ℝ) {σ : ℝ} (hσ : 0 ≤ σ) :
    (∀ z, ell (z - r) ≤ σ * Metric.infDist z C) ↔
      ‖ell‖ ≤ σ ∧ ∀ c ∈ C, ell (c - r) ≤ 0 := by
  constructor
  · intro h
    refine ⟨ell.opNorm_le_bound hσ fun z => ?_, fun c hc => ?_⟩
    · have hpos : ell z ≤ σ * ‖z‖ := calc
        _ = ell ((z + r) - r) := by rw [add_sub_cancel_right]
        _ ≤ σ * Metric.infDist (z + r) C := h _
        _ ≤ _ := by
          have hd := Metric.infDist_le_dist_of_mem (x := z + r) hr
          rw [dist_eq_norm, add_sub_cancel_right] at hd
          exact mul_le_mul_of_nonneg_left hd hσ
      have hneg : -ell z ≤ σ * ‖z‖ := calc
        _ = ell ((-z + r) - r) := by rw [add_sub_cancel_right, map_neg]
        _ ≤ σ * Metric.infDist (-z + r) C := h _
        _ ≤ _ := by
          have hd := Metric.infDist_le_dist_of_mem (x := -z + r) hr
          rw [dist_eq_norm, add_sub_cancel_right, norm_neg] at hd
          exact mul_le_mul_of_nonneg_left hd hσ
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith, hpos⟩
    · simpa only [Metric.infDist_zero_of_mem hc, mul_zero] using h c
  · rintro ⟨hbound, hnormal⟩ z
    have hdist (c : Z) (hc : c ∈ C) : ell (z - r) ≤ σ * dist z c := by
      rw [dist_eq_norm]
      calc
        _ = ell (z - c) + ell (c - r) := by rw [← map_add, sub_add_sub_cancel]
        _ ≤ ell (z - c) := add_le_of_nonpos_right (hnormal c hc)
        _ ≤ |ell (z - c)| := le_abs_self _
        _ ≤ ‖ell‖ * ‖z - c‖ := by simpa only [Real.norm_eq_abs] using ell.le_opNorm (z - c)
        _ ≤ _ := mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
    rcases hσ.eq_or_lt with rfl | hpos
    · simpa only [zero_mul] using hdist r hr
    · rw [mul_comm]
      apply (div_le_iff₀ hpos).mp
      exact (Metric.le_infDist ⟨r, hr⟩).mpr fun c hc =>
        (div_le_iff₀ hpos).mpr (by simpa only [mul_comm σ] using hdist c hc)

/-- **Theorem 15.3.2** of [conn2000trust], first-order part. Let $E$ be a real inner product space,
$Z$ a real normed space, $C \subseteq Z$ the set of feasible constraint values, $r \in C$,
$A : E \to Z$ continuous linear, $g$ and $\nu$ continuous linear functionals on $E$, and
$\sigma \ge 0$. Then there is a continuous linear functional $\ell$ on $Z$ with
$$\|\ell\| \le \sigma, \qquad \ell(c - r) \le 0 \ (c \in C), \qquad g + \ell \circ A + \nu = 0$$
if and only if there is $\ell$ with $\ell(z - r) \le \sigma \operatorname{dist}(z, C)$ for all
$z \in Z$ and $g + \ell \circ A + \nu = 0$.

**Reading.** The theorem is stated in normal-functional form. The set $C$ encodes the equality
and inequality constraints, the distance to $C$ is the violation penalty, and $\nu$ is a normal
of the trust-region constraint, common to the two systems. -/
theorem theorem_15_3_2_first_order {C : Set Z} {r : Z} (hr : r ∈ C)
    (A : E →L[ℝ] Z) (g radiusNormal : E →L[ℝ] ℝ) {σ : ℝ} (hσ : 0 ≤ σ) :
    (∃ ell : Z →L[ℝ] ℝ, ‖ell‖ ≤ σ ∧ (∀ c ∈ C, ell (c - r) ≤ 0) ∧
      g + ell.comp A + radiusNormal = 0) ↔
    (∃ ell : Z →L[ℝ] ℝ, (∀ z, ell (z - r) ≤ σ * Metric.infDist z C) ∧
      g + ell.comp A + radiusNormal = 0) := by
  constructor
  · rintro ⟨ell, hb, hn, hs⟩
    exact ⟨ell, (sqp_penalty_support_iff hr ell hσ).mpr ⟨hb, hn⟩, hs⟩
  · rintro ⟨ell, hp, hs⟩
    obtain ⟨hb, hn⟩ := (sqp_penalty_support_iff hr ell hσ).mp hp
    exact ⟨ell, hb, hn, hs⟩

/-- **Theorem 15.3.2** of [conn2000trust], second-order part. Let $E$ be a real inner product space
and $Z$ a real normed space. Let $K \subseteq Z$ be closed with $0 \in K$, $A : E \to Z$
continuous linear, $g$ a continuous linear functional on $E$ and $H : E \to E$ continuous
linear. Let $\ell$ be a continuous linear functional on $Z$ with $\|\ell\| < \sigma$,
$\ell(z) \le 0$ for all $z \in K$, and $g + \ell \circ A = 0$. Then $\langle d, H d\rangle > 0$
for every $d \ne 0$ with $A d \in K$ and $g(d) = 0$ if and only if $\langle d, H d\rangle > 0$
for every $d \ne 0$ with $g(d) + \sigma \operatorname{dist}(A d, K) = 0$.

**Reading.** The theorem is stated in tangent-cone form, for an inactive trust region, with $K$
in the role of the tangent cone of the feasible constraint values. Strict exactness
$\|\ell\| < \sigma$ makes the cone of directions with zero directional derivative of the penalty
model equal to the critical cone, so the same Hessian is tested on both. -/
theorem theorem_15_3_2_second_order {K : Set Z} (hK : IsClosed K) (h0 : (0 : Z) ∈ K)
    (A : E →L[ℝ] Z) (g : E →L[ℝ] ℝ) (H : E →L[ℝ] E)
    (ell : Z →L[ℝ] ℝ) {σ : ℝ} (hσ : ‖ell‖ < σ)
    (hnormal : ∀ z ∈ K, ell z ≤ 0) (hstat : g + ell.comp A = 0) :
    (∀ d ≠ (0 : E), A d ∈ K → g d = 0 → 0 < ⟪d, H d⟫) ↔
    (∀ d ≠ (0 : E), g d + σ * Metric.infDist (A d) K = 0 → 0 < ⟪d, H d⟫) := by
  have hsupport := (sqp_penalty_support_iff h0 ell (norm_nonneg _)).mpr
    ⟨le_rfl, by simpa only [sub_zero] using hnormal⟩
  have hcritical (d : E) :
      g d + σ * Metric.infDist (A d) K = 0 ↔ A d ∈ K ∧ g d = 0 := by
    constructor
    · intro hd
      have hs := congrArg (fun a : E →L[ℝ] ℝ => a d) hstat
      simp only [add_apply, ContinuousLinearMap.comp_apply,
        zero_apply] at hs
      have h := hsupport (A d)
      rw [sub_zero] at h
      have he : Metric.infDist (A d) K = 0 := by
        by_contra! hne
        have hp := lt_of_le_of_ne Metric.infDist_nonneg (Ne.symm hne)
        have hlt := mul_lt_mul_of_pos_right hσ hp
        linarith only [hs, h, hd, hlt]
      exact ⟨(hK.mem_iff_infDist_zero ⟨0, h0⟩).mpr he,
        by simpa only [he, mul_zero, add_zero] using hd⟩
    · rintro ⟨hK', hg⟩
      rw [hg, Metric.infDist_zero_of_mem hK', mul_zero, add_zero]
  constructor
  · intro h d hd hdir
    obtain ⟨hk, hg⟩ := (hcritical d).mp hdir
    exact h d hd hk hg
  · intro h d hd hk hg
    exact h d hd ((hcritical d).mpr ⟨hk, hg⟩)

end ExactPenalty

/-! ### Global convergence with the exact penalty function -/

section Global

open Filter
open scoped Topology NNReal


/-- **Algorithm 15.3.1** of [conn2000trust], Euclidean mixed violation. Let $\iota$ be a finite
index set in which each index is marked as an equality or an inequality, and let
$c \in \mathbb{R}^\iota$ with the Euclidean norm. Let
$$C = \{z : z_i = 0 \text{ for equality } i, \ z_i \ge 0 \text{ otherwise}\}$$
and let $r_i = c_i$ for an equality index and $r_i = \min\{c_i, 0\}$ otherwise. Then
$\operatorname{dist}(c, C) = \|r\|$. -/
theorem infDist_eq_mixed_violation_norm {ι : Type*} [Fintype ι] (equality : ι → Bool)
    (c : EuclideanSpace ℝ ι) :
    let C : Set (EuclideanSpace ℝ ι) := {z | ∀ i, if equality i then z i = 0 else 0 ≤ z i}
    let r : EuclideanSpace ℝ ι := WithLp.toLp 2
      (fun i ↦ if equality i then c i else min (c i) 0)
    Metric.infDist c C = ‖r‖ := by
  intro C r
  let z : EuclideanSpace ℝ ι := WithLp.toLp 2
    (fun i ↦ if equality i then 0 else max (c i) 0)
  have hz : z ∈ C := by
    intro i
    cases h : equality i <;> simp [z, h]
  have hzr : c - z = r := by
    ext i
    cases h : equality i
    · by_cases hi : 0 ≤ c i
      · simp [z, r, h, PiLp.sub_apply, max_eq_left hi, min_eq_right hi]
      · simp [z, r, h, PiLp.sub_apply, max_eq_right (le_of_not_ge hi),
          min_eq_left (le_of_not_ge hi)]
    · simp [z, r, h, PiLp.sub_apply]
  refine le_antisymm ?_ ?_
  · simpa only [dist_eq_norm, hzr] using Metric.infDist_le_dist_of_mem (x := c) hz
  · apply (Metric.le_infDist ⟨z, hz⟩).mpr
    intro w hw
    rw [dist_eq_norm]
    have hsum : ‖r‖ ^ 2 ≤ ‖c - w‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
      apply Finset.sum_le_sum
      intro i _
      have hwi := hw i
      cases h : equality i
      · have hwi' : 0 ≤ w i := by simpa [h] using hwi
        by_cases hi : 0 ≤ c i
        · simpa [r, h, PiLp.sub_apply, min_eq_right hi] using sq_nonneg (c i - w i)
        · change (if equality i then c i else min (c i) 0) ^ 2 ≤ (c i - w i) ^ 2
          simp only [h, Bool.false_eq_true, ite_false, min_eq_left (le_of_not_ge hi)]
          nlinarith only [mul_nonneg hwi' (show 0 ≤ w i - 2 * c i by linarith)]
      · have hwi' : w i = 0 := by simpa [h] using hwi
        simp [r, h, hwi', PiLp.sub_apply]
    nlinarith only [hsum, norm_nonneg r, norm_nonneg (c - w)]

/-- **Equation (15.3.3)** of [conn2000trust], distance form. For $f : E \to \mathbb{R}$,
$c : E \to Y$, a set $C \subseteq Y$ of feasible constraint values and $\sigma \in \mathbb{R}$,
the **exact penalty function** is
$$\phi(x) = f(x) + \sigma \operatorname{dist}(c(x), C).$$

**Generalization.** The source penalizes the norm of the violation vector. The distance to $C$
is this norm for Euclidean equality and one-sided inequality residuals, by
`ConnGouldToint.Chapter15.infDist_eq_mixed_violation_norm`. -/
noncomputable def sqpDistanceMerit (f : E → ℝ) (c : E → Y) (C : Set Y) (σ : ℝ)
    (x : E) : ℝ := f x + σ * Metric.infDist (c x) C

/-- **Equation (15.3.4)** of [conn2000trust], distance form. At $x$ with a Hessian approximation
$H$, the **model** of the exact penalty function is
$$m(s) = f(x) + \langle g(x), s\rangle + \tfrac12 \langle s, H s\rangle + \sigma
  \operatorname{dist}(c(x) + A(x) s, C).$$

**Generalization.** As in `ConnGouldToint.Chapter15.sqpDistanceMerit`, the violation norm is
replaced by the distance to $C$. -/
noncomputable def sqpDistanceModel (f : E → ℝ) (g : E → E) (c : E → Y)
    (A : E → E →L[ℝ] Y) (C : Set Y) (σ : ℝ)
    (x : E) (H : E →L[ℝ] E) (s : E) : ℝ :=
  Chapter06.quadraticModel (f x) (g x) H.toLinearMap s +
    σ * Metric.infDist (c x + A x s) C

/-- **Algorithm 15.3.1** of [conn2000trust], Step 2a. For a trial step $s$, a shift $v$, a
correction gradient $g^{CS}$ and a correction Hessian $H^{CS}$, the **correction model** is
$$m^{CS}(d) = f(x) + \langle g^{CS}, d\rangle + \tfrac12 \langle d, H^{CS} d\rangle + \sigma
  \operatorname{dist}\big(c(x + s) + A(x + v) d, C\big).$$
It linearizes the constraints at the shifted Jacobian point $x + v$ and uses the constraint
value at the original trial. -/
noncomputable def sqpDistanceCorrectionModel (f : E → ℝ) (c : E → Y)
    (A : E → E →L[ℝ] Y) (C : Set Y) (σ : ℝ) (x s shift gCS : E)
    (HCS : E →L[ℝ] E) (d : E) : ℝ :=
  Chapter06.quadraticModel (f x) gCS HCS.toLinearMap d +
    σ * Metric.infDist (c (x + s) + A (x + shift) d) C

/-- **Algorithm 15.3.1** of [conn2000trust]. Step 2 of the nonsmooth trust-region Algorithm 11.3.1
with the exact-penalty function $\phi$, the model $m$ and the correction model $m^{CS}$. The
conditions are $\Delta \ge 0$, $\tau > 1$, $p(s) \le \Delta$,
$0 \le \mathrm{req} \le m(0) - m(s)$ for the required decrease $\mathrm{req}$, and
$m^{CS}(d) \le m^{CS}(0)$ and $p(s + d) \le \tau \Delta$ for a proposed correction $d$. The
correction is $d$ if $\phi(x + s + d) \le \phi(x + s)$, and $0$ if this fails or no correction
is proposed.

The step is `ConnGouldToint.Chapter11.OptionalCorrectionStep`. -/
def algorithm_15_3_1 (f : E → ℝ) (g : E → E) (c : E → Y) (A : E → E →L[ℝ] Y)
    (C : Set Y) (σ : ℝ) (p : Seminorm ℝ E) (x s shift gCS : E)
    (H HCS : E →L[ℝ] E) (Δ τ required : ℝ) (proposal : Option E) (correction : E) : Prop :=
  Chapter11.OptionalCorrectionStep (sqpDistanceMerit f c C σ)
    (sqpDistanceModel f g c A C σ x H) (sqpDistanceCorrectionModel f c A C σ x s shift gCS HCS)
    p x s Δ τ required proposal correction

/-- Model agreement for **Theorem 15.3.1** of [conn2000trust]. Let $\sigma \ge 0$, $x_* \in E$ and
$\varepsilon, \Delta > 0$, $F, K, B \ge 0$. Suppose that for every $x \in B(x_*, \varepsilon)$
and every $s$ with $\|s\| \le \Delta$,
$$|f(x + s) - f(x) - \langle g(x), s\rangle| \le F \|s\|^2, \qquad \|c(x + s) - c(x) - A(x) s\|
  \le K \|s\|^2.$$
Then the models with $\|H\| \le B$ agree uniformly with the exact penalty function near $x_*$:
for every $a > 0$ there are $\varepsilon', \Delta' > 0$ with
$$\frac{|\phi(y + s) - m_{y, H}(s)|}{\|s\|} \le a$$
for all $y \in B(x_*, \varepsilon')$, all $H$ with $\|H\| \le B$ and all $s$ with
$\|s\| \le \Delta'$.

This is `ConnGouldToint.Chapter11.UniformNormalizedModelAgreementAt`. The quotient is $0$ at
$s = 0$. -/
theorem sqpDistanceModel_uniform_agreement (f : E → ℝ) (g : E → E) (c : E → Y)
    (A : E → E →L[ℝ] Y) (C : Set Y) {σ : ℝ} (hσ : 0 ≤ σ) {xstar : E}
    {ε Δ F K B : ℝ} (hε : 0 < ε) (hΔ : 0 < Δ)
    (hF : 0 ≤ F) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hf : ∀ x ∈ Metric.ball xstar ε, ∀ s, ‖s‖ ≤ Δ →
      |f (x + s) - (f x + ⟪g x, s⟫)| ≤ F * ‖s‖ ^ 2)
    (hc : ∀ x ∈ Metric.ball xstar ε, ∀ s, ‖s‖ ≤ Δ →
      ‖c (x + s) - (c x + A x s)‖ ≤ K * ‖s‖ ^ 2) :
    Chapter11.UniformNormalizedModelAgreementAt (sqpDistanceMerit f c C σ)
      (fun x (H : {H : E →L[ℝ] E // ‖H‖ ≤ B}) s => sqpDistanceModel f g c A C σ x H s) xstar := by
  let D := F + (1 / 2) * B + σ * K
  have hD : 0 ≤ D := by dsimp [D]; positivity
  intro a ha
  let r := min Δ (a / (D + 1))
  refine ⟨ε, r, hε, lt_min hΔ (by positivity), fun x hx H s hs => ?_⟩
  have hsΔ := hs.trans (min_le_left _ _)
  have habs :
      |sqpDistanceMerit f c C σ (x + s) - sqpDistanceModel f g c A C σ x H s| ≤ D * ‖s‖ ^ 2 := by
    have hd : |Metric.infDist (c (x + s)) C - Metric.infDist (c x + A x s) C| ≤
        K * ‖s‖ ^ 2 := by
      refine (abs_le.mpr ⟨?_, ?_⟩).trans (hc x hx s hsΔ)
      · have h := Metric.infDist_le_infDist_add_dist (x := c x + A x s) (y := c (x + s)) (s := C)
        rw [dist_comm, dist_eq_norm] at h
        linarith only [h]
      · have h := Metric.infDist_le_infDist_add_dist (x := c (x + s)) (y := c x + A x s) (s := C)
        rw [dist_eq_norm] at h
        linarith only [h]
    have hcurv : |(1 / 2 : ℝ) * ⟪s, (H : E →L[ℝ] E) s⟫| ≤ (1 / 2) * B * ‖s‖ ^ 2 := by
      rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
      calc
        _ ≤ (1 / 2) * (‖s‖ * ‖(H : E →L[ℝ] E) s‖) :=
          mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num)
        _ ≤ (1 / 2) * (‖s‖ * (B * ‖s‖)) := by
          gcongr
          exact ((H : E →L[ℝ] E).le_opNorm s).trans
            (mul_le_mul_of_nonneg_right H.property (norm_nonneg _))
        _ = _ := by ring
    unfold sqpDistanceMerit sqpDistanceModel Chapter06.quadraticModel
    simp only [ContinuousLinearMap.coe_coe]
    rw [show f (x + s) + σ * Metric.infDist (c (x + s)) C -
        (f x + ⟪g x, s⟫ + 1 / 2 * ⟪s, (H : E →L[ℝ] E) s⟫ + σ * Metric.infDist (c x + A x s) C) =
        (f (x + s) - (f x + ⟪g x, s⟫) - 1 / 2 * ⟪s, (H : E →L[ℝ] E) s⟫) +
          σ * (Metric.infDist (c (x + s)) C - Metric.infDist (c x + A x s) C) by ring]
    have hp : |σ * (Metric.infDist (c (x + s)) C - Metric.infDist (c x + A x s) C)| ≤
        σ * (K * ‖s‖ ^ 2) := by
      rw [abs_mul, abs_of_nonneg hσ]
      exact mul_le_mul_of_nonneg_left hd hσ
    refine ((abs_add_le _ _).trans (add_le_add
      ((abs_sub _ _).trans (add_le_add (hf x hx s hsΔ) hcurv)) hp)).trans ?_
    dsimp [D]
    ring_nf
    rfl
  by_cases hz : s = 0
  · simpa [Chapter11.normalizedModelError, hz] using ha.le
  have hp := norm_pos_iff.mpr hz
  rw [Chapter11.normalizedModelError, abs_div, abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  have hh := (le_div_iff₀ (by positivity : 0 < D + 1)).mp (hs.trans (min_le_right _ _))
  have hmul : D * ‖s‖ ≤ a := by nlinarith only [hh, hp.le]
  exact habs.trans (by simpa only [pow_two, ← mul_assoc] using
    mul_le_mul_of_nonneg_right hmul hp.le)

/-- **Theorem 15.3.1** of [conn2000trust], for the monotone nonsmooth trust-region algorithm. Let
$E$ be a real Hilbert space and $\sigma \ge 0$, and let $(x_k)$ be a run of the nonsmooth
trust-region algorithm for the exact penalty function $\phi$ and the models $m_{x, H}$ with
$\|H\| \le B$. Let $x_* \in E$ and suppose that:

* $\phi$ is Lipschitz on a neighborhood of $x_*$, and the models agree uniformly with $\phi$
  near $x_*$;
* the run has the local sufficient decrease property at every point;
* a subsequence $x_{j(k)}$ converges to $x_*$, and $c(x_*) \in C$;
* every Clarke subgradient $w$ of $\phi$ at $x_*$ has the form $\langle w, d\rangle = \langle
  g(x_*), d\rangle + \ell(A(x_*) d)$ for a functional $\ell$ with $\ell(z - c(x_*)) \le \sigma
  \operatorname{dist}(z, C)$ for all $z$.

Then there is a continuous linear functional $\ell$ on $Y$ with $\|\ell\| \le \sigma$,
$\ell(z - c(x_*)) \le 0$ for all $z \in C$, and
$$\langle g(x_*), d\rangle + \ell(A(x_*) d) = 0 \quad \text{for all } d \in E.$$
Thus $x_*$ is a first-order critical point of the constrained problem.

**Reading.** The Clarke chain-rule inclusion at the limit is a hypothesis. It gives a normal
multiplier from stationarity of the penalty function, without assuming that a multiplier exists.

The run is `ConnGouldToint.Chapter11.NonsmoothTRRun`, and the local sufficient decrease is
`ConnGouldToint.Chapter11.NonsmoothTRRun.HasLocalSufficientDecrease`. -/
theorem theorem_15_3_1 [CompleteSpace E] (f : E → ℝ) (g : E → E) (c : E → Y)
    (A : E → E →L[ℝ] Y) (C : Set Y) {σ B : ℝ} (hσ : 0 ≤ σ)
    {Q : Chapter11.NonsmoothTRParams}
    (R : Chapter11.NonsmoothTRRun Q (sqpDistanceMerit f c C σ)
      (fun x (H : {H : E →L[ℝ] E // ‖H‖ ≤ B}) s => sqpDistanceModel f g c A C σ x H s))
    {xstar : E} {U : Set E} {L : NNReal} (hU : U ∈ 𝓝 xstar)
    (hL : LipschitzOnWith L (sqpDistanceMerit f c C σ) U)
    (herr : Chapter11.UniformNormalizedModelAgreementAt (sqpDistanceMerit f c C σ)
      (fun x (H : {H : E →L[ℝ] E // ‖H‖ ≤ B}) s => sqpDistanceModel f g c A C σ x H s) xstar)
    (hAA : ∀ y, R.HasLocalSufficientDecrease y)
    {j : ℕ → ℕ} (hj : StrictMono j) (hx : Tendsto (R.x ∘ j) atTop (𝓝 xstar))
    (hfeas : c xstar ∈ C)
    (hchain : ∀ w ∈ Optimization.clarkeSubgradient (sqpDistanceMerit f c C σ) xstar,
      ∃ ell : Y →L[ℝ] ℝ,
        (∀ z, ell (z - c xstar) ≤ σ * Metric.infDist z C) ∧
        ∀ d, ⟪w, d⟫ = ⟪g xstar, d⟫ + ell (A xstar d)) :
    ∃ ell : Y →L[ℝ] ℝ, ‖ell‖ ≤ σ ∧ (∀ z ∈ C, ell (z - c xstar) ≤ 0) ∧
      ∀ d, ⟪g xstar, d⟫ + ell (A xstar d) = 0 := by
  have hmatch : Chapter11.modelValueMatches (sqpDistanceMerit f c C σ)
      (fun x (H : {H : E →L[ℝ] E // ‖H‖ ≤ B}) s => sqpDistanceModel f g c A C σ x H s) := by
    intro x H
    simp [sqpDistanceModel, sqpDistanceMerit, Chapter06.quadraticModel]
  have hstat := Chapter11.theorem_11_2_5 R hU hL hmatch herr hAA hj hx
  obtain ⟨ell, hs, he⟩ := hchain 0 hstat
  obtain ⟨hb, hn⟩ := (sqp_penalty_support_iff hfeas ell hσ).mp hs
  exact ⟨ell, hb, hn, fun d => by simpa only [inner_zero_left] using (he d).symm⟩

end Global

end ConnGouldToint.Chapter15
