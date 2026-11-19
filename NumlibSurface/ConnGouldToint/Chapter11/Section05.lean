/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter11.Section02
import NumlibSurface.ConnGouldToint.Chapter03.Section01

/-!
# Conn, Gould and Toint, Section 11.5: Taylor models of composite objectives

This module formalizes Theorem 11.5.1 of [conn2000trust] on the accuracy of Taylor models of a
composite objective $\phi(x) = f(x) + h(c(x))$, with $f : E \to \mathbb{R}$ and $c : E \to Y$ smooth
and $h : Y \to \mathbb{R}$ Lipschitz. The models (11.5.1)–(11.5.3) linearize $f$ and $c$ and add
quadratic terms $q$ and $r$:
$$m(x, i, s) = f(x) + f'(x) s + q(x, i, s) + h\bigl(c(x) + c'(x) s + r(x, i, s)\bigr).$$
Quadratic remainder bounds give $|\phi(x + s) - m(x, i, s)| = O(\|s\|^2)$ uniformly near $x$, hence
uniform normalized agreement (11.2.1), and for regular objectives and models also the matching
conditions AM.2n and AM.3n. The estimate needs both the actual residual $c(x + s)$ and the modeled
residual in the domain where $h$ is Lipschitz.

The uniform agreement is `ConnGouldToint.Chapter11.UniformNormalizedModelAgreementAt` of
`NumlibSurface.ConnGouldToint.Chapter11.Section02`, and the matching conditions follow from Lemma
11.2.1.

## Main definitions

* Equations (11.5.1)–(11.5.3), `ConnGouldToint.Chapter11.compositeTaylorModel`: the Taylor model of
  the composite objective.

## Main results

* Theorem 11.5.1, model accuracy, `ConnGouldToint.Chapter11.compositeTaylorModel_error`: $|\phi(x +
  s) - m(x, i, s)| \le (A + C + L(B + F)) \|s\|^2$.
* Theorem 11.5.1, uniform agreement, `ConnGouldToint.Chapter11.theorem_11_5_1_uniform_agreement`: a
  uniform quadratic error bound gives uniform normalized agreement.
* Theorem 11.5.1, `ConnGouldToint.Chapter11.theorem_11_5_1_of_lipschitz_derivatives`: Lipschitz
  derivatives of $f$ and $c$ and a Lipschitz $h$ on both residual images give uniform normalized
  agreement.
* Theorem 11.5.1, AM.2n and AM.3n,
  `ConnGouldToint.Chapter11.theorem_11_5_1_value_and_directional_agreement`: for regular objectives
  and models, uniform agreement gives the value and Clarke derivative matching.
* Theorem 11.5.1, counterexample,
  `ConnGouldToint.Chapter11.compositeTaylorModel_domain_counterexample`: the modeled residual can
  leave the domain of $h$ at arbitrarily small steps.

## Implementation notes

* The quadratic terms are represented by their values $q(x, i, s) \in \mathbb{R}$ and
  $r(x, i, s) \in Y$, indexed by a parameter $i$. Model (11.5.1) takes $q = r = 0$, model (11.5.2)
  takes the second-order Taylor terms of $f$ and $c$, and model (11.5.3) keeps only the quadratic
  term of $f$.

## Deviations from the source

* **Theorem 11.5.1** (correction). The accuracy estimate also assumes that the modeled residual
  $c(x) + c'(x) s + r(x, i, s)$ lies in the domain where $h$ is Lipschitz. See
  `ConnGouldToint.Chapter11.compositeTaylorModel_domain_counterexample`.
* **Theorem 11.5.1** (partial translation). The error estimates use uniform quadratic bounds
  on the added terms. The value and directional agreement result assumes regularity of the
  objective and model. The book also asserts continuity of the model family and compactness
  of the model parameter set.
-/

open Filter Metric Optimization ConvexAnalysis
open scoped NNReal Topology

namespace ConnGouldToint.Chapter11

variable {E Y I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- **Equations (11.5.1)–(11.5.3)** of [conn2000trust]. For $f : E \to \mathbb{R}$, $c : E \to Y$,
$h : Y \to \mathbb{R}$ and quadratic terms $q(x, i, s) \in \mathbb{R}$ and $r(x, i, s) \in Y$,
the **composite Taylor model** of $\phi = f + h \circ c$ at $x$ is
$$m(x, i, s) = f(x) + f'(x) s + q(x, i, s) + h\bigl(c(x) + c'(x) s + r(x, i, s)\bigr).$$

The quadratic terms are represented by their values. Both are zero for (11.5.1), they are the
second-order Taylor terms of $f$ and $c$ for (11.5.2), and only the quadratic term of $f$ is
kept for (11.5.3). The derivatives are `fderiv`.

**Reading.** Unified model with arbitrary parameter and term values on normed spaces.
-/
noncomputable def compositeTaylorModel (f : E → ℝ) (c : E → Y) (h : Y → ℝ)
    (q : E → I → E → ℝ) (r : E → I → E → Y) (x : E) (i : I) (s : E) : ℝ :=
  f x + fderiv ℝ f x s + q x i s + h (c x + fderiv ℝ c x s + r x i s)

/-- **Theorem 11.5.1** of [conn2000trust], model accuracy. Let $h$ be $L$-Lipschitz on a set
$D \subseteq Y$, and let both the actual residual $c(x + s)$ and the modeled residual
$c(x) + c'(x) s + r(x, i, s)$ lie in $D$. Assume
$$|f(x + s) - f(x) - f'(x) s| \le A \|s\|^2, \qquad \|c(x + s) - c(x) - c'(x) s\| \le B
  \|s\|^2,$$
$$|q(x, i, s)| \le C \|s\|^2, \qquad \|r(x, i, s)\| \le F \|s\|^2.$$
Then
$$|f(x + s) + h(c(x + s)) - m(x, i, s)| \le \bigl(A + C + L (B + F)\bigr) \|s\|^2.$$

**Correction.** The source does not require the modeled residual to lie in the domain where $h$
is Lipschitz. Without this, the outer function can be evaluated where no Lipschitz bound is
available (see `ConnGouldToint.Chapter11.compositeTaylorModel_domain_counterexample`). -/
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
/-- **Theorem 11.5.1** of [conn2000trust], uniform normalized agreement. Let $f : E \to \mathbb{R}$
and let $m(y, i, \cdot)$ be a family of models. If there are $\varepsilon, \delta > 0$ and
$K \ge 0$ with
$$|f(y + s) - m(y, i, s)| \le K \|s\|^2$$
for every $y$ in the open ball of radius $\varepsilon$ about $x$, every parameter $i$ and every
$\|s\| \le \delta$, then the models have uniform normalized agreement with $f$ at $x$.

This applies to all three Taylor models (11.5.1)–(11.5.3).

**Reading.** Derives uniform normalized agreement from a supplied quadratic error estimate.
-/
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

/-- **Theorem 11.5.1** of [conn2000trust]. Let $S \subseteq E$ be open, let $f$ and $c$ be
continuously differentiable on $S$ with derivatives that are Lipschitz on $S$, and let $h$ be
Lipschitz on $D \subseteq Y$. Let $\varepsilon, \delta > 0$ and $C, F \ge 0$, and assume that
for every $y$ in the open ball of radius $\varepsilon$ about $x$, every parameter $i$ and every
$\|s\| \le \delta$:
* the segment from $y$ to $y + s$ lies in $S$;
* $c(y + s) \in D$ and $c(y) + c'(y) s + r(y, i, s) \in D$;
* $|q(y, i, s)| \le C \|s\|^2$ and $\|r(y, i, s)\| \le F \|s\|^2$.

Then the composite Taylor models have uniform normalized agreement with $\phi = f + h \circ c$
at $x$.

**Correction.** As in `ConnGouldToint.Chapter11.compositeTaylorModel_error`, the modeled
residual must lie in the domain $D$ where $h$ is Lipschitz. -/
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

/-- **Theorem 11.5.1** of [conn2000trust], conditions AM.2n and AM.3n. Let $V$ be a
finite-dimensional real inner product space of dimension at least $1$, and let the models
$m(y, i, \cdot)$ have uniform normalized agreement with $f$ at $x$. Let $f$ be Lipschitz on a
neighborhood of $x$, let $m(x, i, \cdot)$ be Lipschitz on a neighborhood of $0$, and let both be
regular: their one-sided directional derivatives along positive rays exist and equal their
Clarke derivatives. Then $m(x, i, 0) = f(x)$ and $m(x, i, \cdot)^\circ(0; d) = f^\circ(x; d)$
for every $d \neq 0$.

The proof applies `ConnGouldToint.Chapter11.lemma_11_2_1`.

**Reading.** Deduces center value and directional agreement under explicit local regularity; it does
not establish all four source assumptions.
-/
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

/-- **Theorem 11.5.1** of [conn2000trust], counterexample for the model domain. For every
$\varepsilon > 0$ there are $x, s \in \mathbb{R}$ with $|x| < \varepsilon$ and
$|s| < \varepsilon$ such that $(x + s)^2 \ge 0$ but $x^2 + 2 x s < 0$.

For $c(x) = x^2$ and an outer function that is Lipschitz only on $[0, \infty)$, the actual
residual $c(x + s)$ stays in this domain, while its affine model $c(x) + c'(x) s$ leaves it at
arbitrarily small steps.

**Reading.** Modeled residual can leave the Lipschitz domain arbitrarily close to the base point.
-/
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
