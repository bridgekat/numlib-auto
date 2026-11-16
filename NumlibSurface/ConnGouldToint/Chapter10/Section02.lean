/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter06.Section04
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Conn, Gould and Toint, Section 10.2: Structured trust regions

This module formalizes the structured trust-region method of Section 10.2 of [conn2000trust] for a
partially separable objective $f = \sum_{i=1}^{p} f_i$ on a real Hilbert space $E$. Each element
$f_i$ and its model $m_i$ are invariant along a nontrivial subspace $N_i$, so they depend only on
the component of the point in $N_i^\perp$. Each element has its own radius $\Delta_i$, and its trust
region is the cylinder $\{y : p_k(P_{N_i^\perp}(y - x)) \le \Delta_i\}$ (10.2.3), where $p_k$ is the
trust-region seminorm. The cylinder constrains only the projected component of the step. The overall
trust region is the intersection of the cylinders. Algorithm 10.2.1 updates each radius from a fit
test that compares the predicted decrease $d_i$ and the achieved decrease $a_i$ of element $i$, with
a separate test for the negligible elements (10.2.8), and Algorithm 10.2.2 accepts a step by the
total test $\eta_1 \sum_i d_i \le \sum_i a_i$ (10.2.10). The module proves the bounds of Lemmas
10.2.1, 10.2.2 and 10.2.4, the element error bound of Theorem 10.2.3, the floor on the radii of
Theorem 10.2.5, and the criticality result of Theorem 10.2.6 for a run with finitely many successful
iterations.

Theorem 10.2.6 needs the uniform norm comparison $\|v\| \le K p_k(v)$ of AN.1. A counterexample with
a single element shows that without it every trial can be rejected at a fixed noncritical iterate.
The parameters and the error constant come from the basic trust-region algorithm in
`NumlibSurface.ConnGouldToint.Chapter06.Section01` and
`NumlibSurface.ConnGouldToint.Chapter06.Section04`.

## Main definitions

* Section 10.2.1, `ConnGouldToint.Chapter10.InvariantAlong`: a function is invariant under
  translations along a subspace.
* Equation (10.2.2), `ConnGouldToint.Chapter10.PartiallySeparable`: $f$ is a sum of elements, each
  invariant along a nontrivial subspace.
* Equation (10.2.1), `ConnGouldToint.Chapter10.separableObjective`: the fully separable objective
  $\sum_i f_i(x_i)$.
* Equation (10.2.3), `ConnGouldToint.Chapter10.elementTrustRegion`: the cylinder of one element.
* Section 10.2.1, `ConnGouldToint.Chapter10.structuredTrustRegion`: the intersection of the element
  cylinders.
* Equation (10.2.4), `ConnGouldToint.Chapter10.minimumRadius`: the smallest element radius.
* Equation (10.2.5), `ConnGouldToint.Chapter10.StructuredTRParams`: the parameters of the structured
  algorithm and their compatibility condition.
* Equation (10.2.8), `ConnGouldToint.Chapter10.negligibleElements`: the elements with a small
  predicted change.
* `ConnGouldToint.Chapter10.meaningfulElements`: the elements that are not negligible.
* Equations (10.2.9) and (10.2.12), `ConnGouldToint.Chapter10.elementFit`: the fit test of a
  meaningful element.
* Equation (10.2.10), `ConnGouldToint.Chapter10.structuredSuccessful`: the total acceptance test.
* Equation (10.2.13), `ConnGouldToint.Chapter10.negligibleFit`: the fit test of a negligible
  element.
* Algorithm 10.2.1, `ConnGouldToint.Chapter10.StructuredRadiusUpdate`: the seven cases of the update
  of the element radii.
* AA.1s, `ConnGouldToint.Chapter10.structuredSufficientDecrease`: the sufficient decrease condition
  of the structured method.
* Algorithm 10.2.2, `ConnGouldToint.Chapter10.StructuredTRRun`: an infinite run of the structured
  algorithm.
* `ConnGouldToint.Chapter10.StructuredTRRun.predictedDrop`,
  `ConnGouldToint.Chapter10.StructuredTRRun.actualDrop`,
  `ConnGouldToint.Chapter10.StructuredTRRun.modelGradient`,
  `ConnGouldToint.Chapter10.StructuredTRRun.objectiveGradient` and
  `ConnGouldToint.Chapter10.StructuredTRRun.successful`: the element decreases, the gradients and
  the successful iterations of a run.
* Equation (10.2.24), `ConnGouldToint.Chapter10.structuredRadiusFloor`: the corrected lower bound
  for the radii.
* Equation (6.3.1), `ConnGouldToint.Chapter10.StructuredTRRun.aggregateCurvature`: the curvature
  constant of the total model on the structured trust region.

## Main results

* Equations (10.2.6)–(10.2.7), `ConnGouldToint.Chapter10.elementRatio_iff_fit`: for a positive
  predicted decrease, the ratio test is equivalent to the fit test.
* Equations (10.2.6)–(10.2.7), `ConnGouldToint.Chapter10.elementRatio_zero_counterexample`: at zero
  predicted decrease the two tests disagree.
* Equation (10.2.10), `ConnGouldToint.Chapter10.structuredSuccessful_iff_ratio`: for a positive
  total predicted decrease, the total test is the ratio test.
* Lemma 10.2.1(ii), `ConnGouldToint.Chapter10.lemma_10_2_1_ii`: every radius keeps at least the
  fraction $\gamma_1$.
* Lemma 10.2.1(i), `ConnGouldToint.Chapter10.lemma_10_2_1_i`: there is a meaningful element, and the
  meaningful decreases satisfy (10.2.14).
* Lemma 10.2.2, `ConnGouldToint.Chapter10.lemma_10_2_2`: the element fit tests imply the total
  acceptance test.
* `ConnGouldToint.Chapter10.StructuredTRRun.delta_pos`: all radii of a run are positive.
* Theorem 10.2.3, `ConnGouldToint.Chapter10.theorem_10_2_3`: the error of each element model is
  quadratic in the radius of the element.
* Lemma 10.2.4, `ConnGouldToint.Chapter10.lemma_10_2_4`: for a small radius, the model change of an
  element is linear in its radius.
* Theorem 10.2.5, `ConnGouldToint.Chapter10.structuredRadiusFloor_pos_and_le`: on a tail with
  gradients bounded away from zero, the radii stay above the floor (10.2.24).
* Theorem 10.2.5, `ConnGouldToint.Chapter10.theorem_10_2_5_of_error_bound`: under a quadratic error
  bound, gradients bounded away from zero keep the radii bounded away from zero.
* Theorem 10.2.6, `ConnGouldToint.Chapter10.theorem_10_2_6_of_error_bound`: under a quadratic error
  bound, a run with finitely many successful iterations ends at a first-order critical point.
* Equation (6.3.2), `ConnGouldToint.Chapter10.StructuredTRRun.aggregateCurvature_le`: element
  Hessian bounds bound the curvature of the total model.
* Theorem 10.2.5, `ConnGouldToint.Chapter10.theorem_10_2_5`: the same floor under the smoothness
  assumptions.
* Theorem 10.2.6, `ConnGouldToint.Chapter10.theorem_10_2_6`: the same criticality result under the
  smoothness assumptions and AN.1.
* Theorem 10.2.6, `ConnGouldToint.Chapter10.theorem_10_2_6_without_norm_bound_counterexample`:
  without AN.1, every trial can be rejected at a noncritical point.

## Conventions

* The number of elements is $p = |\iota| \ge 1$, and $\iota$ is a finite type. The element decreases
  are $d_i = m_i(x) - m_i(x + s)$ and $a_i = f_i(x) - f_i(x + s)$.
* $P_{N^\perp}$ is the orthogonal projection onto $N^\perp$, `Submodule.starProjection`. The
  gradient $\nabla f(x)$ is `gradient f x`.
* The assumptions AF.5s, AM.4s, AN.1 and AA.1s of the source appear as explicit hypotheses: a bound
  on the element gradients, a bound on the model Hessians on the structured trust region, the norm
  comparison $\|v\| \le K p_k(v)$, and `ConnGouldToint.Chapter10.structuredSufficientDecrease`.

## Deviations from the source

* **Equations (10.2.6)–(10.2.7)** (reading). The ratio test and the fit test are equivalent only for
  a positive predicted decrease. At zero predicted decrease they can disagree. The module uses the
  fit test. See `ConnGouldToint.Chapter10.elementRatio_zero_counterexample`.
* **Equation (10.2.24)** (correction). The floor on the radii compares the model error directly with
  the two fit tolerances, and the curvature bound uses the sum of the element curvature bounds. See
  `ConnGouldToint.Chapter10.structuredRadiusFloor`.
* **Theorem 10.2.6** (correction). The theorem needs the uniform norm comparison AN.1. Without it,
  every trial can be rejected at a fixed noncritical iterate. See
  `ConnGouldToint.Chapter10.theorem_10_2_6_without_norm_bound_counterexample`.
-/

open scoped BigOperators Topology
open Set

namespace ConnGouldToint.Chapter10

open Chapter06

section Geometry

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Section 10.2.1** of [conn2000trust], invariant subspace. Let $N$ be a subspace of $E$ and $f$
a function on $E$. Then $f$ is **invariant along** $N$ if $f(x + w) = f(x)$ for all $x \in E$
and $w \in N$. -/
def InvariantAlong {F : Type*} (N : Submodule ℝ E) (f : E → F) : Prop :=
  ∀ x w, w ∈ N → f (x + w) = f x

/-- **Equation (10.2.2)** of [conn2000trust]. The function $f : E \to \mathbb{R}$ is **partially
separable** with elements $f_i$ and invariant subspaces $N_i$, for $i$ in a finite index set, if
$f(x) = \sum_i f_i(x)$ for all $x$, every $N_i$ is nonzero, and every $f_i$ is invariant along
$N_i$.

The range subspace of element $i$ is the orthogonal complement $N_i^\perp$. -/
structure PartiallySeparable [Fintype ι] (f : E → ℝ)
    (elements : ι → E → ℝ) (N : ι → Submodule ℝ E) : Prop where
  /-- Every $x$ satisfies $f(x) = \sum_i f_i(x)$. -/
  sum_elements : ∀ x, f x = ∑ i, elements i x
  /-- Every invariant subspace $N_i$ is nonzero. -/
  nontrivial : ∀ i, N i ≠ ⊥
  /-- Every element $f_i$ is invariant along $N_i$. -/
  invariant : ∀ i, InvariantAlong (N i) (elements i)

/-- **Equation (10.2.1)** of [conn2000trust]. For element functions $f_i : X_i \to \mathbb{R}$ on
the factors of a finite product, the **separable objective** is $f(x) = \sum_i f_i(x_i)$. -/
def separableObjective [Fintype ι] {X : ι → Type*} (elements : ∀ i, X i → ℝ)
    (x : ∀ i, X i) : ℝ :=
  ∑ i, elements i (x i)

/-- **Equation (10.2.3)** of [conn2000trust]. For a seminorm $p$ on $E$, a subspace $N$, a center
$x$ and a radius $\Delta$, the **element trust region** is the cylinder
$$\{y \in E : p(P_{N^\perp}(y - x)) \le \Delta\},$$
where $P_{N^\perp}$ is the orthogonal projection onto $N^\perp$. -/
def elementTrustRegion (p : Seminorm ℝ E) (N : Submodule ℝ E)
    [Nᗮ.HasOrthogonalProjection] (x : E) (Δ : ℝ) : Set E :=
  {y | p (Nᗮ.starProjection (y - x)) ≤ Δ}

/-- **Section 10.2.1** of [conn2000trust], the overall trust region. For a seminorm $p$, subspaces
$N_i$, a center $x$ and radii $\Delta_i$, the **structured trust region** is the intersection
over $i$ of the element trust regions (10.2.3) of $N_i$ with radius $\Delta_i$. -/
def structuredTrustRegion [CompleteSpace E] (p : Seminorm ℝ E) (N : ι → Submodule ℝ E)
    (x : E) (Δ : ι → ℝ) : Set E :=
  ⋂ i, elementTrustRegion p (N i) x (Δ i)

/-- **Equation (10.2.4)** of [conn2000trust]. For radii $\Delta_i$ indexed by a finite nonempty set,
the **minimum radius** is $\Delta_{\min} = \min_i \Delta_i$. -/
noncomputable def minimumRadius [Fintype ι] [Nonempty ι] (Δ : ι → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty Δ

private theorem structuredTrustRegion_convex [CompleteSpace E]
    (p : Seminorm ℝ E) (N : ι → Submodule ℝ E) (x : E) (Δ : ι → ℝ) :
    Convex ℝ (structuredTrustRegion p N x Δ) := by
  apply convex_iInter
  intro i
  exact ((p.comp (N i)ᗮ.starProjection.toLinearMap).convex_closedBall x (Δ i))

end Geometry

/-- **Equation (10.2.5)** of [conn2000trust]. The **structured parameters** are the parameters
$\eta_1, \eta_2, \gamma_1, \gamma_2$ of the basic trust-region algorithm together with $\eta_3$,
$\mu_1$ and $\mu_2$, such that $\eta_2 < \eta_3 < 1$, $0 < \mu_1 < \mu_2 < 1$ and
$$\mu_1 + \mu_2 \le \eta_2 - \eta_1.$$
-/
structure StructuredTRParams extends BTRParams where
  /-- The threshold $\eta_3$ of the fit test at which a meaningful element does not shrink its
  radius. -/
  η₃ : ℝ
  /-- The constant $\mu_1$ that defines the negligible elements (10.2.8). -/
  μ₁ : ℝ
  /-- The constant $\mu_2$ of the negligible fit test (10.2.13). -/
  μ₂ : ℝ
  /-- The threshold $\eta_3$ is above $\eta_2$. -/
  eta₂_lt_eta₃ : η₂ < η₃
  /-- The threshold $\eta_3$ is below $1$. -/
  eta₃_lt_one : η₃ < 1
  /-- The negligibility constant $\mu_1$ is positive. -/
  mu₁_pos : 0 < μ₁
  /-- The constants satisfy $\mu_1 < \mu_2$. -/
  mu₁_lt_mu₂ : μ₁ < μ₂
  /-- The constant $\mu_2$ is below $1$. -/
  mu₂_lt_one : μ₂ < 1
  /-- The compatibility condition $\mu_1 + \mu_2 \le \eta_2 - \eta_1$ (10.2.5). -/
  compatible : μ₁ + μ₂ ≤ η₂ - η₁

/-- **Equations (10.2.6)–(10.2.7)** of [conn2000trust], positive predicted decrease. Let
$a, d, \eta \in \mathbb{R}$ with $d > 0$. Then
$$\eta \le \frac{a}{d} \iff d - (1 - \eta) |d| \le a.$$

At $d = 0$ the ratio test has no such meaning; see
`ConnGouldToint.Chapter10.elementRatio_zero_counterexample`. -/
theorem elementRatio_iff_fit {a d η : ℝ} (hd : 0 < d) :
    η ≤ a / d ↔ d - (1 - η) * |d| ≤ a := by
  rw [le_div_iff₀ hd, abs_of_pos hd]
  have h : d - (1 - η) * d = η * d := by ring
  rw [h]

/-- **Equations (10.2.6)–(10.2.7)** of [conn2000trust], zero predicted decrease. For $a = d = 0$ and
$\eta = 1/2$, the ratio test $\eta \le a / d$ and the fit test $d - (1 - \eta)|d| \le a$
disagree.

**Reading.** In Lean $0 / 0 = 0$, so the ratio test fails while the fit test holds. The module
uses the fit test. -/
theorem elementRatio_zero_counterexample :
    ¬ ((1 / 2 : ℝ) ≤ 0 / 0 ↔ (0 : ℝ) - (1 - 1 / 2) * |0| ≤ 0) := by norm_num

section Radii

variable {ι : Type*} [Fintype ι]

/-- **Equation (10.2.8)** of [conn2000trust]. For $\mu \in \mathbb{R}$ and predicted decreases $d_i$
of the $p$ elements, the set of **negligible elements** is
$$\{i : |d_i| \le \tfrac{\mu}{p} \textstyle\sum_j d_j\}.$$

The set is defined with the total predicted change $\sum_j d_j$. -/
noncomputable def negligibleElements (μ : ℝ) (d : ι → ℝ) : Finset ι :=
  open Classical in
  Finset.univ.filter fun i ↦ |d i| ≤ μ / Fintype.card ι * ∑ j, d j

/-- The **meaningful elements** are the elements that are not negligible (10.2.8). -/
noncomputable def meaningfulElements (μ : ℝ) (d : ι → ℝ) : Finset ι :=
  open Classical in
  Finset.univ \ negligibleElements μ d

/-- **Equations (10.2.9) and (10.2.12)** of [conn2000trust]. Element $i$ passes the **fit test**
with threshold $\eta$ if
$$d_i - \frac{1 - \eta}{p} \sum_j d_j \le a_i.$$
The threshold $\eta_2$ gives (10.2.9), and the threshold $\eta_3$ gives (10.2.12). -/
def elementFit (η : ℝ) (d a : ι → ℝ) (i : ι) : Prop :=
  d i - (1 - η) / Fintype.card ι * ∑ j, d j ≤ a i

/-- **Equation (10.2.10)** of [conn2000trust]. The iteration is **successful** if
$\eta_1 \sum_i d_i \le \sum_i a_i$. -/
def structuredSuccessful (η₁ : ℝ) (d a : ι → ℝ) : Prop :=
  η₁ * (∑ i, d i) ≤ ∑ i, a i

/-- **Equation (10.2.10)** of [conn2000trust] and Algorithm 10.2.2. If $\sum_i d_i > 0$, the
iteration is successful if and only if
$$\eta_1 \le \frac{\sum_i a_i}{\sum_i d_i},$$
which is the ratio test in Step 3 of Algorithm 10.2.2. -/
theorem structuredSuccessful_iff_ratio (η₁ : ℝ) {d a : ι → ℝ} (hd : 0 < ∑ i, d i) :
    structuredSuccessful η₁ d a ↔ η₁ ≤ (∑ i, a i) / ∑ i, d i :=
  (le_div_iff₀ hd).symm

/-- **Equation (10.2.13)** of [conn2000trust]. A negligible element $i$ passes the **negligible fit
test** if $|a_i| \le \frac{\mu_2}{p} \sum_j d_j$. -/
def negligibleFit (μ₂ : ℝ) (d a : ι → ℝ) (i : ι) : Prop :=
  |a i| ≤ μ₂ / Fintype.card ι * ∑ j, d j

/-- **Algorithm 10.2.1** of [conn2000trust] and (10.2.11). Let $P$ be structured parameters, $d_i$
and $a_i$ the predicted and achieved element decreases, and $\Delta_i$, $\Delta'_i$ the old and
new radii. The radii satisfy the **structured radius update** if, with the meaningful and
negligible elements taken for $\mu_1$:

* a meaningful element that passes the fit test with $\eta_3$ has $\Delta'_i \ge \Delta_i$ if
  the iteration is successful, and $\Delta'_i = \Delta_i$ otherwise;
* a meaningful element that fails the fit test with $\eta_3$ and passes it with $\eta_2$ has
  $\gamma_2 \Delta_i \le \Delta'_i \le \Delta_i$;
* a meaningful element that fails the fit test with $\eta_2$ has $\gamma_1 \Delta_i \le
  \Delta'_i \le \gamma_2 \Delta_i$;
* a negligible element that passes the negligible fit test with $\mu_2$ has
  $\Delta'_i \ge \Delta_i$ if the iteration is successful, and $\Delta'_i = \Delta_i$ otherwise;
* a negligible element that fails the negligible fit test has $\gamma_1 \Delta_i \le \Delta'_i
  \le \gamma_2 \Delta_i$. -/
structure StructuredRadiusUpdate (P : StructuredTRParams) (d a Δ Δ' : ι → ℝ) : Prop where
  /-- A meaningful element that passes the fit test with $\eta_3$ at a successful iteration does not
  shrink. -/
  meaningful_expand : ∀ i ∈ meaningfulElements P.μ₁ d,
    elementFit P.η₃ d a i → structuredSuccessful P.η₁ d a → Δ i ≤ Δ' i
  /-- A meaningful element that passes the fit test with $\eta_3$ at an unsuccessful iteration keeps
  its radius. -/
  meaningful_hold : ∀ i ∈ meaningfulElements P.μ₁ d,
    elementFit P.η₃ d a i → ¬ structuredSuccessful P.η₁ d a → Δ' i = Δ i
  /-- A meaningful element that passes the fit test with $\eta_2$ but not with $\eta_3$ has
  $\gamma_2 \Delta_i \le \Delta'_i \le \Delta_i$. -/
  meaningful_moderate : ∀ i ∈ meaningfulElements P.μ₁ d,
    ¬ elementFit P.η₃ d a i → elementFit P.η₂ d a i →
      P.γ₂ * Δ i ≤ Δ' i ∧ Δ' i ≤ Δ i
  /-- A meaningful element that fails the fit test with $\eta_2$ has $\gamma_1 \Delta_i \le
  \Delta'_i \le \gamma_2 \Delta_i$. -/
  meaningful_contract : ∀ i ∈ meaningfulElements P.μ₁ d,
    ¬ elementFit P.η₂ d a i → P.γ₁ * Δ i ≤ Δ' i ∧ Δ' i ≤ P.γ₂ * Δ i
  /-- A negligible element that passes the negligible fit test at a successful iteration does not
  shrink. -/
  negligible_expand : ∀ i ∈ negligibleElements P.μ₁ d,
    negligibleFit P.μ₂ d a i → structuredSuccessful P.η₁ d a → Δ i ≤ Δ' i
  /-- A negligible element that passes the negligible fit test at an unsuccessful iteration keeps
  its radius. -/
  negligible_hold : ∀ i ∈ negligibleElements P.μ₁ d,
    negligibleFit P.μ₂ d a i → ¬ structuredSuccessful P.η₁ d a → Δ' i = Δ i
  /-- A negligible element that fails the negligible fit test has $\gamma_1 \Delta_i \le \Delta'_i
  \le \gamma_2 \Delta_i$. -/
  negligible_contract : ∀ i ∈ negligibleElements P.μ₁ d,
    ¬ negligibleFit P.μ₂ d a i → P.γ₁ * Δ i ≤ Δ' i ∧ Δ' i ≤ P.γ₂ * Δ i

private theorem mem_negligibleElements {μ : ℝ} {d : ι → ℝ} {i : ι} :
    i ∈ negligibleElements μ d ↔ |d i| ≤ μ / Fintype.card ι * ∑ j, d j := by
  classical
  simp [negligibleElements]

private theorem mem_meaningfulElements {μ : ℝ} {d : ι → ℝ} {i : ι} :
    i ∈ meaningfulElements μ d ↔ i ∉ negligibleElements μ d := by
  classical
  simp [meaningfulElements]

/-- **Lemma 10.2.1(ii)** of [conn2000trust] and (10.2.15). If the radii satisfy the structured
radius update and $\Delta_i \ge 0$, then $\gamma_1 \Delta_i \le \Delta'_i$. -/
theorem lemma_10_2_1_ii {P : StructuredTRParams} {d a Δ Δ' : ι → ℝ}
    (hu : StructuredRadiusUpdate P d a Δ Δ') (hΔ : ∀ i, 0 ≤ Δ i) (i : ι) :
    P.γ₁ * Δ i ≤ Δ' i := by
  have h₁₂ : P.γ₁ * Δ i ≤ P.γ₂ * Δ i :=
    mul_le_mul_of_nonneg_right P.gamma₁_le_gamma₂ (hΔ i)
  have h₁ : P.γ₁ * Δ i ≤ Δ i :=
    h₁₂.trans (mul_le_of_le_one_left (hΔ i) P.gamma₂_lt_one.le)
  by_cases hn : i ∈ negligibleElements P.μ₁ d
  · by_cases hfit : negligibleFit P.μ₂ d a i
    · by_cases hs : structuredSuccessful P.η₁ d a
      · exact h₁.trans (hu.negligible_expand i hn hfit hs)
      · rwa [hu.negligible_hold i hn hfit hs]
    · exact (hu.negligible_contract i hn hfit).1
  · have hm := mem_meaningfulElements.mpr hn
    by_cases hfit : elementFit P.η₃ d a i
    · by_cases hs : structuredSuccessful P.η₁ d a
      · exact h₁.trans (hu.meaningful_expand i hm hfit hs)
      · rwa [hu.meaningful_hold i hm hfit hs]
    · by_cases hmoderate : elementFit P.η₂ d a i
      · exact h₁₂.trans (hu.meaningful_moderate i hm hfit hmoderate).1
      · exact (hu.meaningful_contract i hm hmoderate).1

private theorem sum_meaningful_add_sum_negligible (μ : ℝ) (d a : ι → ℝ) :
    (∑ i ∈ meaningfulElements μ d, a i) + (∑ i ∈ negligibleElements μ d, a i) = ∑ i, a i := by
  classical
  exact Finset.sum_sdiff (Finset.subset_univ _)

private theorem card_meaningful_add_card_negligible (μ : ℝ) (d : ι → ℝ) :
    (meaningfulElements μ d).card + (negligibleElements μ d).card = Fintype.card ι := by
  classical
  simpa only [meaningfulElements, Finset.card_univ] using Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (negligibleElements μ d))

variable [Nonempty ι]

private theorem negligible_card_bound {μ : ℝ} {d : ι → ℝ} (hμ : μ < 1)
    (hd : 0 < ∑ i, d i) :
    (meaningfulElements μ d).Nonempty ∧
      ((negligibleElements μ d).card : ℝ) ≤ (Fintype.card ι : ℝ) - 1 := by
  classical
  have hp : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hM : (meaningfulElements μ d).Nonempty := by
    by_contra hn
    have hsmall (i : ι) : |d i| ≤ μ / Fintype.card ι * ∑ j, d j :=
      mem_negligibleElements.mp (by
        by_contra hi
        exact hn ⟨i, mem_meaningfulElements.mpr hi⟩)
    have hle : (∑ i, d i) ≤ μ * ∑ i, d i := calc
      _ ≤ ∑ _i : ι, μ / Fintype.card ι * ∑ j, d j :=
        Finset.sum_le_sum fun i _ ↦ (le_abs_self _).trans (hsmall i)
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
    exact ((mul_lt_mul_of_pos_right hμ hd).not_ge (by simpa using hle))
  have hcard := card_meaningful_add_card_negligible μ d
  have hMpos : 1 ≤ (meaningfulElements μ d).card := Finset.card_pos.mpr hM
  refine ⟨hM, ?_⟩
  have hle : (negligibleElements μ d).card + 1 ≤ Fintype.card ι := by omega
  have hle' : ((negligibleElements μ d).card : ℝ) + 1 ≤ Fintype.card ι := by exact_mod_cast hle
  linarith

omit [Nonempty ι] in
private theorem sum_abs_le_card_bound {d a : ι → ℝ} {μ c : ℝ}
    (hcard : ((negligibleElements μ d).card : ℝ) ≤ (Fintype.card ι : ℝ) - 1)
    (hc : 0 ≤ c) (ha : ∀ i ∈ negligibleElements μ d, |a i| ≤ c) :
    (∑ i ∈ negligibleElements μ d, |a i|) ≤ ((Fintype.card ι : ℝ) - 1) * c := calc
  _ ≤ ∑ _i ∈ negligibleElements μ d, c := Finset.sum_le_sum ha
  _ ≤ _ := by
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard hc

/-- **Lemma 10.2.1(i)** of [conn2000trust] and (10.2.14). Let $0 \le \mu < 1$ and let the predicted
decreases satisfy $\sum_i d_i > 0$, with $p \ge 1$ elements. Then there is a meaningful element,
and
$$\left(1 - \tfrac{p - 1}{p} \mu\right) \sum_i d_i \le \sum_{i \text{ meaningful}} d_i \le
  \left(1 + \tfrac{p - 1}{p} \mu\right) \sum_i d_i.$$
-/
theorem lemma_10_2_1_i {μ : ℝ} {d : ι → ℝ} (hμ₀ : 0 ≤ μ) (hμ₁ : μ < 1)
    (hd : 0 < ∑ i, d i) :
    (meaningfulElements μ d).Nonempty ∧
      (1 - ((Fintype.card ι : ℝ) - 1) / Fintype.card ι * μ) * (∑ i, d i) ≤
        (∑ i ∈ meaningfulElements μ d, d i) ∧
      (∑ i ∈ meaningfulElements μ d, d i) ≤
        (1 + ((Fintype.card ι : ℝ) - 1) / Fintype.card ι * μ) * (∑ i, d i) := by
  obtain ⟨hm, hcard⟩ := negligible_card_bound hμ₁ hd
  have hsum := sum_meaningful_add_sum_negligible μ d d
  have habs := sum_abs_le_card_bound (a := d) hcard
    (show 0 ≤ μ / Fintype.card ι * ∑ i, d i by positivity)
    (fun _ hi ↦ mem_negligibleElements.mp hi)
  have hnegligible := (Finset.abs_sum_le_sum_abs _ _).trans habs
  have hscale :
      ((Fintype.card ι : ℝ) - 1) * (μ / Fintype.card ι * ∑ i, d i) =
      (((Fintype.card ι : ℝ) - 1) / Fintype.card ι * μ) * ∑ i, d i := by ring
  rw [hscale] at hnegligible
  refine ⟨hm, ?_, ?_⟩ <;> nlinarith [(abs_le.mp hnegligible).1, (abs_le.mp hnegligible).2]

/-- **Lemma 10.2.2** of [conn2000trust] and (10.2.16)–(10.2.17). Let $P$ be structured parameters
and $\sum_i d_i > 0$, with $p \ge 1$ elements. Suppose that every meaningful element passes the
fit test with $\eta_2$ and every negligible element passes the negligible fit test with $\mu_2$.
Then
$$\left(\eta_2 - \tfrac{p - 1}{p} \mu_1\right) \sum_i d_i \le \sum_{i \text{ meaningful}} a_i,
  \qquad \sum_{i \text{ negligible}} |a_i| \le \tfrac{p - 1}{p} \mu_2 \sum_i d_i,$$
and the iteration is successful (10.2.10). -/
theorem lemma_10_2_2 (P : StructuredTRParams) {d a : ι → ℝ}
    (hd : 0 < ∑ i, d i)
    (hm : ∀ i ∈ meaningfulElements P.μ₁ d, elementFit P.η₂ d a i)
    (hn : ∀ i ∈ negligibleElements P.μ₁ d, negligibleFit P.μ₂ d a i) :
    (P.η₂ - ((Fintype.card ι : ℝ) - 1) / Fintype.card ι * P.μ₁) * (∑ i, d i) ≤
        (∑ i ∈ meaningfulElements P.μ₁ d, a i) ∧
      (∑ i ∈ negligibleElements P.μ₁ d, |a i|) ≤
        ((Fintype.card ι : ℝ) - 1) / Fintype.card ι * P.μ₂ * (∑ i, d i) ∧
      structuredSuccessful P.η₁ d a := by
  classical
  have hμ₁ := P.mu₁_lt_mu₂.trans P.mu₂_lt_one
  have hμ₂ := P.mu₁_pos.trans P.mu₁_lt_mu₂
  have hp : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have ⟨_, hcard⟩ := negligible_card_bound hμ₁ hd
  have ⟨_, hlower, _⟩ := lemma_10_2_1_i P.mu₁_pos.le hμ₁ hd
  let c := (1 - P.η₂) / Fintype.card ι * ∑ i, d i
  have hc : 0 ≤ c := mul_nonneg (div_nonneg (sub_nonneg.mpr P.eta₂_lt_one.le) hp.le) hd.le
  have hcardM : ((meaningfulElements P.μ₁ d).card : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast Finset.card_le_univ (meaningfulElements P.μ₁ d)
  have hfit :
      (∑ i ∈ meaningfulElements P.μ₁ d, d i) - (1 - P.η₂) * (∑ i, d i) ≤
        ∑ i ∈ meaningfulElements P.μ₁ d, a i := by
    have hsum : (∑ i ∈ meaningfulElements P.μ₁ d, (d i - c)) ≤
        ∑ i ∈ meaningfulElements P.μ₁ d, a i :=
      Finset.sum_le_sum hm
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
    have hscale : (Fintype.card ι : ℝ) * c = (1 - P.η₂) * (∑ i, d i) := by
      dsimp [c]
      field_simp
    rw [← hscale]
    exact (sub_le_sub_left (mul_le_mul_of_nonneg_right hcardM hc) _).trans hsum
  have hM : (P.η₂ - ((Fintype.card ι : ℝ) - 1) / Fintype.card ι * P.μ₁) * (∑ i, d i) ≤
      ∑ i ∈ meaningfulElements P.μ₁ d, a i := by
    nlinarith only [hlower, hfit]
  have hN : (∑ i ∈ negligibleElements P.μ₁ d, |a i|) ≤
      ((Fintype.card ι : ℝ) - 1) / Fintype.card ι * P.μ₂ * (∑ i, d i) :=
    (sum_abs_le_card_bound hcard (show 0 ≤ P.μ₂ / Fintype.card ι * ∑ i, d i by positivity)
      hn).trans_eq (by ring)
  refine ⟨hM, hN, ?_⟩
  have hsplit := sum_meaningful_add_sum_negligible P.μ₁ d a
  have habs := Finset.abs_sum_le_sum_abs a (negligibleElements P.μ₁ d)
  have hneg := (abs_le.mp (habs.trans hN)).1
  let α := ((Fintype.card ι : ℝ) - 1) / Fintype.card ι
  have hα : α ≤ 1 := (div_le_iff₀ hp).mpr (by linarith)
  have hsuccess : P.η₁ ≤ P.η₂ - α * P.μ₁ - α * P.μ₂ := by
    linarith [P.compatible, mul_le_of_le_one_left P.mu₁_pos.le hα,
      mul_le_of_le_one_left hμ₂.le hα]
  have hscaled := mul_le_mul_of_nonneg_right hsuccess hd.le
  change P.η₁ * (∑ i, d i) ≤ ∑ i, a i
  dsimp only [α] at hscaled
  nlinarith only [hsplit, hM, hneg, hscaled]

end Radii

section Run

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype ι] [Nonempty ι]

/-- **AA.1s** of [conn2000trust]. A step $s$ from $x$ for the model $m$, with seminorm $p$, element
radii $\Delta_i$, curvature constant $\beta$ and constant $\kappa$, satisfies the **structured
sufficient decrease** condition if
$$\kappa \|\nabla m(x)\| \min\left\{\frac{\|\nabla m(x)\|}{\beta}, \max\{\Delta_{\min},
  p(s)\}\right\} \le m(x) - m(x + s).$$

For a nonzero step, $p(s)$ stands for the ratio of $\|s\|$ to the conversion factor between the
norms in the source. -/
def structuredSufficientDecrease (model : E → ℝ) (x s : E) (p : Seminorm ℝ E)
    (Δ : ι → ℝ) (β κ : ℝ) : Prop :=
  κ * ‖gradient model x‖ * min (‖gradient model x‖ / β) (max (minimumRadius Δ) (p s)) ≤
    model x - model (x + s)

open Classical in
/-- **Algorithm 10.2.2** of [conn2000trust], an infinite run. Let $E$ be a real Hilbert space, $P$
structured parameters, $f_i : E \to \mathbb{R}$ elements with invariant subspaces $N_i$,
$\beta_k$ curvature constants and $\kappa$ a constant. A **structured trust-region run**
consists of iterates $x_k$, steps $s_k$, seminorms $p_k$ that vanish only at $0$, element models
$m_{k,i}$ and element radii $\Delta_{k,i}$, such that every $N_i$ is nonzero, every $f_i$ and
every $m_{k,i}$ is invariant along $N_i$, $\Delta_{0,i} > 0$, $\beta_k > 0$, $\kappa > 0$, and
for every $k$:

* $x_k + s_k$ lies in the structured trust region of $p_k$, $x_k$ and the radii $\Delta_{k,i}$;
* $s_k$ satisfies the structured sufficient decrease condition for the total model
  $\sum_i m_{k,i}$, and $\sum_i (m_{k,i}(x_k) - m_{k,i}(x_k + s_k)) > 0$;
* the radii $\Delta_{k+1,i}$ satisfy the structured radius update for the predicted decreases
  $m_{k,i}(x_k) - m_{k,i}(x_k + s_k)$ and the achieved decreases $f_i(x_k) - f_i(x_k + s_k)$;
* $x_{k+1} = x_k + s_k$ if the iteration is successful (10.2.10), and $x_{k+1} = x_k$ otherwise. -/
structure StructuredTRRun (P : StructuredTRParams) (elements : ι → E → ℝ)
    (N : ι → Submodule ℝ E) (β : ℕ → ℝ) (κ : ℝ) where
  /-- The iterate $x_k$. -/
  x : ℕ → E
  /-- The step $s_k$. -/
  s : ℕ → E
  /-- The trust-region seminorm $p_k$. -/
  p : ℕ → Seminorm ℝ E
  /-- The model $m_{k,i}$ of element $i$ at iteration $k$. -/
  model : ℕ → ι → E → ℝ
  /-- The radius $\Delta_{k,i}$ of element $i$ at iteration $k$. -/
  Δ : ℕ → ι → ℝ
  /-- Each seminorm $p_k$ vanishes only at $0$. -/
  norm_separates : ∀ k v, p k v = 0 → v = 0
  /-- Every invariant subspace $N_i$ is nonzero. -/
  invariant_nontrivial : ∀ i, N i ≠ ⊥
  /-- Every element $f_i$ is invariant along $N_i$. -/
  objective_invariant : ∀ i, InvariantAlong (N i) (elements i)
  /-- Every element model $m_{k,i}$ is invariant along $N_i$. -/
  model_invariant : ∀ k i, InvariantAlong (N i) (model k i)
  /-- The initial radii are positive. -/
  initial_pos : ∀ i, 0 < Δ 0 i
  /-- Each curvature constant is positive: $\beta_k > 0$. -/
  β_pos : ∀ k, 0 < β k
  /-- The decrease constant is positive: $\kappa > 0$. -/
  κ_pos : 0 < κ
  /-- The trial point lies in the structured trust region. -/
  feasible : ∀ k, x k + s k ∈ structuredTrustRegion (p k) N (x k) (Δ k)
  /-- The step satisfies the structured sufficient decrease condition AA.1s for the total model. -/
  sufficient : ∀ k, structuredSufficientDecrease (fun z ↦ ∑ i, model k i z)
    (x k) (s k) (p k) (Δ k) (β k) κ
  /-- The total predicted decrease is positive. -/
  predicted_pos : ∀ k, 0 < ∑ i, (model k i (x k) - model k i (x k + s k))
  /-- The radii follow the structured radius update for the element decreases. -/
  radius_update : ∀ k,
    StructuredRadiusUpdate P (fun i ↦ model k i (x k) - model k i (x k + s k))
      (fun i ↦ elements i (x k) - elements i (x k + s k)) (Δ k) (Δ (k + 1))
  /-- The iterate moves to $x_k + s_k$ exactly at a successful iteration. -/
  iterate_update : ∀ k, x (k + 1) =
    if structuredSuccessful P.η₁ (fun i ↦ model k i (x k) - model k i (x k + s k))
        (fun i ↦ elements i (x k) - elements i (x k + s k))
    then x k + s k else x k

/-- Every radius of a structured trust-region run is positive: $\Delta_{k,i} > 0$. This follows from
Lemma 10.2.1(ii). -/
theorem StructuredTRRun.delta_pos {P : StructuredTRParams} {elements : ι → E → ℝ}
    {N : ι → Submodule ℝ E} {β : ℕ → ℝ} {κ : ℝ}
    (run : StructuredTRRun P elements N β κ) (k : ℕ) (i : ι) : 0 < run.Δ k i := by
  induction k generalizing i with
  | zero => exact run.initial_pos i
  | succ k ih =>
    exact (mul_pos P.gamma₁_pos (ih i)).trans_le
      (lemma_10_2_1_ii (run.radius_update k) (fun j ↦ (ih j).le) i)

end Run

section Accuracy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem InvariantAlong.fderiv_invariant {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {N : Submodule ℝ E} {f : E → F} (hf : InvariantAlong N f) :
    InvariantAlong N (fderiv ℝ f) := by
  intro x w hw
  rw [← fderiv_comp_add_right]
  rw [show (fun y ↦ f (y + w)) = f from funext fun y ↦ hf y w hw]

private theorem InvariantAlong.differentiableAt_add_iff {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {N : Submodule ℝ E} {f : E → F} (hf : InvariantAlong N f)
    {x w : E} (hw : w ∈ N) :
    DifferentiableAt ℝ f (x + w) ↔ DifferentiableAt ℝ f x := by
  rw [← differentiableAt_comp_add_right]
  rw [show (fun y ↦ f (y + w)) = f from funext fun y ↦ hf y w hw]

private theorem element_taylor_bound {N : Submodule ℝ E} [N.HasOrthogonalProjection]
    {f : E → ℝ} {x s : E} {C : ℝ} (hf : InvariantAlong N f)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ f (x + t • s))
    (hdd : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ (fderiv ℝ f) (x + t • s))
    (hC : ∀ t ∈ Icc (0 : ℝ) 1, ‖fderiv ℝ (fderiv ℝ f) (x + t • s)‖ ≤ C) :
    |f (x + s) - (f x + fderiv ℝ f x (Nᗮ.starProjection s))| ≤
      (1 / 2 : ℝ) * C * ‖Nᗮ.starProjection s‖ ^ 2 := by
  let q := Nᗮ.starProjection s
  let n := N.starProjection s
  have hn : n ∈ N := N.starProjection_apply_mem s
  have hq : n + q = s := N.starProjection_add_starProjection_orthogonal s
  have hshift (t : ℝ) : (x + t • q) + t • n = x + t • s := by
    rw [add_assoc, ← smul_add, add_comm q n, hq]
  have hsegment (z : E) (hz : z ∈ segment ℝ x (x + q)) :
      ∃ t ∈ Icc (0 : ℝ) 1, x + t • q = z := by
    rw [segment_eq_image', add_sub_cancel_left] at hz
    exact hz
  have hbound := norm_sub_firstOrder_le_of_hessian_bound
    (convex_segment (𝕜 := ℝ) x (x + q)) (left_mem_segment ℝ x (x + q))
    (right_mem_segment ℝ x (x + q))
    (f := f) (s := q)
    (fun z hz ↦ by
      obtain ⟨t, ht, rfl⟩ := hsegment z hz
      apply (hf.differentiableAt_add_iff (N.smul_mem t hn)).mp
      rw [hshift]
      exact hd t ht)
    (fun z hz ↦ by
      obtain ⟨t, ht, rfl⟩ := hsegment z hz
      apply (hf.fderiv_invariant.differentiableAt_add_iff (N.smul_mem t hn)).mp
      rw [hshift]
      exact hdd t ht)
    (fun z hz ↦ by
      obtain ⟨t, ht, rfl⟩ := hsegment z hz
      rw [← hf.fderiv_invariant.fderiv_invariant (x + t • q) (t • n) (N.smul_mem t hn), hshift]
      exact hC t ht)
  have hval : f (x + s) = f (x + q) := by
    have h := hshift 1
    simp only [one_smul] at h
    rw [← h]
    exact hf (x + q) n hn
  rw [Real.norm_eq_abs] at hbound
  rwa [hval]

private theorem InvariantAlong.value_at_projection {F : Type*}
    {N : Submodule ℝ E} [N.HasOrthogonalProjection] {f : E → F}
    (hf : InvariantAlong N f) (z : E) : f z = f (Nᗮ.starProjection z) := by
  have hz : Nᗮ.starProjection z + N.starProjection z = z := by
    rw [add_comm]
    exact N.starProjection_add_starProjection_orthogonal z
  conv_lhs => rw [← hz]
  exact hf (Nᗮ.starProjection z) (N.starProjection z) (N.starProjection_apply_mem z)

variable {ι : Type*} [Fintype ι] [Nonempty ι] [CompleteSpace E]
  {P : StructuredTRParams} {elements : ι → E → ℝ} {N : ι → Submodule ℝ E}
  {β : ℕ → ℝ} {κ : ℝ} [∀ i, (N i).HasOrthogonalProjection]

private theorem StructuredTRRun.segment_mem (run : StructuredTRRun P elements N β κ)
    (k : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    run.x k + t • run.s k ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) := by
  have hx : run.x k ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) := by
    rw [structuredTrustRegion, mem_iInter]
    intro i
    simpa [elementTrustRegion] using (run.delta_pos k i).le
  simpa only [add_sub_cancel_left] using
    (structuredTrustRegion_convex (run.p k) N (run.x k) (run.Δ k)).add_smul_sub_mem
      hx (run.feasible k) ht

private theorem StructuredTRRun.projected_step_le (run : StructuredTRRun P elements N β κ)
    {K : ℝ} (hK : 0 ≤ K) (hnorm : ∀ k v, ‖v‖ ≤ K * run.p k v) (k : ℕ) (i : ι) :
    ‖(N i)ᗮ.starProjection (run.s k)‖ ≤ K * run.Δ k i := by
  have h := run.feasible k
  rw [structuredTrustRegion, mem_iInter] at h
  have hi : run.p k ((N i)ᗮ.starProjection (run.s k)) ≤ run.Δ k i := by
    simpa [elementTrustRegion] using h i
  exact (hnorm k _).trans (mul_le_mul_of_nonneg_left hi hK)

/-- **Theorem 10.2.3** of [conn2000trust] and (10.2.18). Let a structured trust-region run be given,
with $K \ge 1$, $\kappa_f \ge 1$, $\kappa_m \ge 1$ and $\|v\| \le K p_k(v)$ for all $k$ and $v$.
Suppose that every $f_i$ is twice continuously differentiable with
$\|\nabla^2 f_i(z)\| \le \kappa_f$ for $z \in N_i^\perp$, that every model $m_{k,i}$ and its
derivative are differentiable on the structured trust region with
$\|\nabla^2 m_{k,i}(z)\| \le \kappa_m - 1$ there, and that $m_{k,i}(x_k) = f_i(x_k)$ and
$\nabla m_{k,i}(x_k) = \nabla f_i(x_k)$. Then $C = K^2 \max\{\kappa_f, \kappa_m\} \ge 1$ and
$$|f_i(x_k + s_k) - m_{k,i}(x_k + s_k)| \le C \Delta_{k,i}^2.$$

The constant is `ConnGouldToint.Chapter06.uniformHessianConstant`. The model Hessian bound is
needed on the whole structured trust region. By translation invariance, the estimate uses the
projected step without requiring the projected trial point to lie in that region. -/
theorem theorem_10_2_3 (run : StructuredTRRun P elements N β κ)
    {K κf κm : ℝ} (hK : 1 ≤ K) (hκf : 1 ≤ κf) (hκm : 1 ≤ κm)
    (hnorm : ∀ k v, ‖v‖ ≤ K * run.p k v)
    (hf : ∀ i, ContDiff ℝ 2 (elements i))
    (hF : ∀ i z, z ∈ (N i)ᗮ → ‖fderiv ℝ (fderiv ℝ (elements i)) z‖ ≤ κf)
    (hm : ∀ k i z, z ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) →
      DifferentiableAt ℝ (run.model k i) z)
    (hDm : ∀ k i z, z ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) →
      DifferentiableAt ℝ (fderiv ℝ (run.model k i)) z)
    (hM : ∀ k i z, z ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) →
      ‖fderiv ℝ (fderiv ℝ (run.model k i)) z‖ ≤ κm - 1)
    (hval : ∀ k i, run.model k i (run.x k) = elements i (run.x k))
    (hgrad : ∀ k i, fderiv ℝ (run.model k i) (run.x k) = fderiv ℝ (elements i) (run.x k))
    (k : ℕ) (i : ι) :
    1 ≤ uniformHessianConstant K κf κm ∧
      |elements i (run.x k + run.s k) - run.model k i (run.x k + run.s k)| ≤
        uniformHessianConstant K κf κm * (run.Δ k i) ^ 2 := by
  refine ⟨?_, ?_⟩
  · have hK₂ : 1 ≤ K ^ 2 := by nlinarith
    exact one_le_mul_of_one_le_of_one_le hK₂ (hκm.trans (le_max_right _ _))
  let q := (N i)ᗮ.starProjection (run.s k)
  let C := max κf κm
  have hC : 0 ≤ C := (zero_le_one.trans hκf).trans (le_max_left _ _)
  have hq := run.projected_step_le (zero_le_one.trans hK) hnorm k i
  have hfun := element_taylor_bound (run.objective_invariant i) (C := C)
    (x := run.x k) (s := run.s k)
    (fun t _ ↦ (hf i).differentiable (by norm_num) _)
    (fun t _ ↦ ((hf i).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) _)
    (fun t _ ↦ by
      rw [(run.objective_invariant i).fderiv_invariant.fderiv_invariant.value_at_projection]
      exact (hF i _ ((N i)ᗮ.starProjection_apply_mem _)).trans (le_max_left _ _))
  have hmod := element_taylor_bound (run.model_invariant k i) (C := C)
    (fun t ht ↦ hm k i _ (run.segment_mem k ht))
    (fun t ht ↦ hDm k i _ (run.segment_mem k ht))
    (fun t ht ↦ (hM k i _ (run.segment_mem k ht)).trans
      ((by linarith : κm - 1 ≤ κm).trans (le_max_right _ _)))
  rw [hval k i, hgrad k i] at hmod
  have herr :
      |elements i (run.x k + run.s k) - run.model k i (run.x k + run.s k)| ≤ C * ‖q‖ ^ 2 := by
    have h₁ := abs_le.mp hfun
    have h₂ := abs_le.mp hmod
    change _ ≤ (1 / 2 : ℝ) * C * ‖q‖ ^ 2 at hfun hmod
    apply abs_le.mpr
    constructor <;> linarith only [h₁.1, h₁.2, h₂.1, h₂.2]
  calc
    _ ≤ C * ‖q‖ ^ 2 := herr
    _ ≤ C * (K * run.Δ k i) ^ 2 := by gcongr
    _ = _ := by unfold uniformHessianConstant C; ring

/-- **Lemma 10.2.4** of [conn2000trust] and (10.2.19)–(10.2.22). Let a structured trust-region run
be given, with $K \ge 1$, $\kappa_{fg} > 0$, $\kappa_m \ge 1$ and $\|v\| \le K p_k(v)$ for all
$k$ and $v$. Suppose that $\|\nabla f_i(z)\| \le \kappa_{fg}$ for $z \in N_i^\perp$ (AF.5s),
that every model $m_{k,i}$ and its derivative are differentiable on the structured trust region
with $\|\nabla^2 m_{k,i}(z)\| \le \kappa_m - 1$ there (AM.4s), and that
$\nabla m_{k,i}(x_k) = \nabla f_i(x_k)$. If $K \Delta_{k,i} \le 1$, then $K \Delta_{\min} \le 1$
for the radii of iteration $k$, and
$$|m_{k,i}(x_k) - m_{k,i}(x_k + s_k)| \le K \left(\kappa_{fg} + \tfrac{1}{2} \kappa_m\right)
  \Delta_{k,i}.$$
-/
theorem lemma_10_2_4 (run : StructuredTRRun P elements N β κ)
    {K κfg κm : ℝ} (hK : 1 ≤ K) (hκfg : 0 < κfg) (hκm : 1 ≤ κm)
    (hnorm : ∀ k v, ‖v‖ ≤ K * run.p k v)
    (hF : ∀ i z, z ∈ (N i)ᗮ → ‖gradient (elements i) z‖ ≤ κfg)
    (hm : ∀ k i z, z ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) →
      DifferentiableAt ℝ (run.model k i) z)
    (hDm : ∀ k i z, z ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) →
      DifferentiableAt ℝ (fderiv ℝ (run.model k i)) z)
    (hM : ∀ k i z, z ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) →
      ‖fderiv ℝ (fderiv ℝ (run.model k i)) z‖ ≤ κm - 1)
    (hgrad : ∀ k i, fderiv ℝ (run.model k i) (run.x k) = fderiv ℝ (elements i) (run.x k))
    (k : ℕ) (i : ι) (hsmall : K * run.Δ k i ≤ 1) :
    K * minimumRadius (run.Δ k) ≤ 1 ∧
    |run.model k i (run.x k) - run.model k i (run.x k + run.s k)| ≤
      K * (κfg + κm / 2) * run.Δ k i := by
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  have hκm₀ : 0 ≤ κm := zero_le_one.trans hκm
  refine ⟨?_, ?_⟩
  · have hmin : minimumRadius (run.Δ k) ≤ run.Δ k i := Finset.inf'_le _ (Finset.mem_univ i)
    exact (mul_le_mul_of_nonneg_left hmin hK₀).trans hsmall
  let q := (N i)ᗮ.starProjection (run.s k)
  have hq : ‖q‖ ≤ K * run.Δ k i := run.projected_step_le hK₀ hnorm k i
  have hq₁ : ‖q‖ ≤ 1 := hq.trans hsmall
  have hmodel := element_taylor_bound (run.model_invariant k i) (C := κm)
    (fun t ht ↦ hm k i _ (run.segment_mem k ht))
    (fun t ht ↦ hDm k i _ (run.segment_mem k ht))
    (fun t ht ↦ (hM k i _ (run.segment_mem k ht)).trans (by linarith))
  have hD : ‖fderiv ℝ (run.model k i) (run.x k)‖ ≤ κfg := by
    rw [hgrad k i, (run.objective_invariant i).fderiv_invariant.value_at_projection]
    have h := hF i _ ((N i)ᗮ.starProjection_apply_mem (run.x k))
    simpa only [gradient, LinearIsometryEquiv.norm_map] using h
  have hlin : |fderiv ℝ (run.model k i) (run.x k) q| ≤ κfg * ‖q‖ := by
    rw [← Real.norm_eq_abs]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg _))
  let r := run.model k i (run.x k + run.s k) -
    (run.model k i (run.x k) + fderiv ℝ (run.model k i) (run.x k) q)
  have hr : |r| ≤ (1 / 2 : ℝ) * κm * ‖q‖ ^ 2 := hmodel
  have hsum : |run.model k i (run.x k) - run.model k i (run.x k + run.s k)| ≤
      |r| + |fderiv ℝ (run.model k i) (run.x k) q| := by
    rw [abs_sub_comm]
    have heq : run.model k i (run.x k + run.s k) - run.model k i (run.x k) =
        r + fderiv ℝ (run.model k i) (run.x k) q := by dsimp [r]; ring
    rw [heq]
    exact abs_add_le _ _
  have hsq : ‖q‖ ^ 2 ≤ ‖q‖ := by nlinarith [mul_nonneg (norm_nonneg q) (sub_nonneg.mpr hq₁)]
  calc
    _ ≤ |r| + |fderiv ℝ (run.model k i) (run.x k) q| := hsum
    _ ≤ (1 / 2 : ℝ) * κm * ‖q‖ ^ 2 + κfg * ‖q‖ := add_le_add hr hlin
    _ ≤ (κfg + κm / 2) * ‖q‖ := by nlinarith [mul_le_mul_of_nonneg_left hsq hκm₀]
    _ ≤ (κfg + κm / 2) * (K * run.Δ k i) :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    _ = _ := by ring

end Accuracy

section Convergence

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype ι] [Nonempty ι] {P : StructuredTRParams} {elements : ι → E → ℝ}
  {N : ι → Submodule ℝ E} {β : ℕ → ℝ} {κ : ℝ}

/-- The **predicted decrease** of element $i$ at iteration $k$ of a structured run:
$m_{k,i}(x_k) - m_{k,i}(x_k + s_k)$. -/
noncomputable def StructuredTRRun.predictedDrop (run : StructuredTRRun P elements N β κ)
    (k : ℕ) (i : ι) : ℝ :=
  run.model k i (run.x k) - run.model k i (run.x k + run.s k)

/-- The **achieved decrease** of element $i$ at iteration $k$ of a structured run:
$f_i(x_k) - f_i(x_k + s_k)$. -/
noncomputable def StructuredTRRun.actualDrop (run : StructuredTRRun P elements N β κ)
    (k : ℕ) (i : ι) : ℝ :=
  elements i (run.x k) - elements i (run.x k + run.s k)

/-- The gradient $\nabla m_k(x_k)$ of the total model $m_k = \sum_i m_{k,i}$ at the current iterate.
-/
noncomputable def StructuredTRRun.modelGradient (run : StructuredTRRun P elements N β κ)
    (k : ℕ) : E :=
  gradient (fun x ↦ ∑ i, run.model k i x) (run.x k)

/-- The gradient $\nabla f(x_k)$ of the total objective $f = \sum_i f_i$ at the current iterate. -/
noncomputable def StructuredTRRun.objectiveGradient (run : StructuredTRRun P elements N β κ)
    (k : ℕ) : E :=
  gradient (fun x ↦ ∑ i, elements i x) (run.x k)

/-- The **successful iterations** of a structured run: the $k$ at which the total test (10.2.10)
holds for the element decreases. -/
def StructuredTRRun.successful (run : StructuredTRRun P elements N β κ) : Set ℕ :=
  {k | structuredSuccessful P.η₁ (run.predictedDrop k) (run.actualDrop k)}

private theorem minimumRadius_le (Δ : ι → ℝ) (i : ι) : minimumRadius Δ ≤ Δ i :=
  Finset.inf'_le _ (Finset.mem_univ i)

private theorem le_minimumRadius {Δ : ι → ℝ} {b : ℝ} (h : ∀ i, b ≤ Δ i) :
    b ≤ minimumRadius Δ :=
  Finset.le_inf' _ _ fun i _ ↦ h i

private theorem exists_eq_minimumRadius (Δ : ι → ℝ) : ∃ i, Δ i = minimumRadius Δ := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty Δ
  exact ⟨i, hi.symm⟩

private theorem minimumRadius_pos (Δ : ι → ℝ) (h : ∀ i, 0 < Δ i) :
    0 < minimumRadius Δ := by
  obtain ⟨i, hi⟩ := exists_eq_minimumRadius Δ
  simpa only [← hi] using h i

omit [Nonempty ι] in
private theorem StructuredRadiusUpdate.noncontract_of_scaled_error
    {d a Δ Δ' : ι → ℝ} (hu : StructuredRadiusUpdate P d a Δ Δ') (i : ι)
    (hgood : |a i - d i| ≤ (1 - P.η₃) / Fintype.card ι * ∑ j, d j)
    (hsmall : |a i - d i| ≤ (P.μ₂ - P.μ₁) / Fintype.card ι * ∑ j, d j) :
    Δ i ≤ Δ' i := by
  by_cases hn : i ∈ negligibleElements P.μ₁ d
  · have hN : negligibleFit P.μ₂ d a i := by
      have hd := mem_negligibleElements.mp hn
      have hsum : |a i| ≤ |a i - d i| + |d i| := by
        simpa only [sub_add_cancel] using abs_add_le (a i - d i) (d i)
      unfold negligibleFit
      calc
        _ ≤ |a i - d i| + |d i| := hsum
        _ ≤ (P.μ₂ - P.μ₁) / Fintype.card ι * (∑ j, d j) +
            P.μ₁ / Fintype.card ι * ∑ j, d j := add_le_add hsmall hd
        _ = _ := by rw [← add_mul, ← add_div, sub_add_cancel]
    by_cases hs : structuredSuccessful P.η₁ d a
    · exact hu.negligible_expand i hn hN hs
    · rw [hu.negligible_hold i hn hN hs]
  · have hm := mem_meaningfulElements.mpr hn
    have hM : elementFit P.η₃ d a i := by
      unfold elementFit
      linarith only [(abs_le.mp hgood).1]
    by_cases hs : structuredSuccessful P.η₁ d a
    · exact hu.meaningful_expand i hm hM hs
    · rw [hu.meaningful_hold i hm hM hs]

private theorem StructuredTRRun.predicted_total_ge (run : StructuredTRRun P elements N β κ)
    {B ε : ℝ} {k : ℕ} (hβ : β k ≤ B) (hε : 0 < ε)
    (hg : ε ≤ ‖run.modelGradient k‖) :
    κ * ε * min (ε / B) (minimumRadius (run.Δ k)) ≤ ∑ i, run.predictedDrop k i := by
  have hB : 0 < B := (run.β_pos k).trans_le hβ
  have hmin : 0 < minimumRadius (run.Δ k) := minimumRadius_pos _ (run.delta_pos k)
  have hs := run.sufficient k
  unfold structuredSufficientDecrease at hs
  change κ * ‖run.modelGradient k‖ *
      min (‖run.modelGradient k‖ / β k) (max (minimumRadius (run.Δ k)) (run.p k (run.s k))) ≤
      (∑ i, run.model k i (run.x k)) - (∑ i, run.model k i (run.x k + run.s k)) at hs
  rw [← Finset.sum_sub_distrib] at hs
  refine le_trans (mul_le_mul (mul_le_mul_of_nonneg_left hg run.κ_pos.le) ?_
    (le_min (div_nonneg hε.le hB.le) hmin.le) (mul_nonneg run.κ_pos.le (norm_nonneg _))) hs
  exact min_le_min (div_le_div₀ (norm_nonneg _) hg (run.β_pos k) hβ) (le_max_left _ _)

/-- **Equation (10.2.24)** of [conn2000trust], corrected. For structured parameters $P$, $p$
elements, constants $\kappa$, $\varepsilon$, $B$, $C$ and an initial radius $\Delta^0$, let
$e = \gamma_1 \kappa \varepsilon$. The **structured radius floor** is
$$\min\left\{\Delta^0, \; \gamma_1 \min\left\{\frac{\varepsilon}{B}, \; \frac{1 - \eta_3}{p}
  \frac{e}{C}, \; \frac{\mu_2 - \mu_1}{p} \frac{e}{C}\right\}\right\}.$$

**Correction.** This floor replaces the sufficient threshold printed in (10.2.24). The two error
terms come from the fit test of the meaningful elements and the test of the negligible elements. -/
noncomputable def structuredRadiusFloor (P : StructuredTRParams) (p : ℕ)
    (κ ε B C initial : ℝ) : ℝ :=
  let e := P.γ₁ * (κ * ε)
  min initial (P.γ₁ * min (ε / B)
    (min (((1 - P.η₃) / p) * e / C) (((P.μ₂ - P.μ₁) / p) * e / C)))

/-- **Theorem 10.2.5** of [conn2000trust], on a tail. Let a structured trust-region run be given,
with $\beta_k \le B$ for all $k$, $C > 0$ and $\varepsilon > 0$. Suppose that
$|a_{k,i} - d_{k,i}| \le C \Delta_{k,i}^2$ for all $k$ and $i$, and that
$\|\nabla m_k(x_k)\| \ge \varepsilon$ for all $k \ge n$. Then the structured radius floor with
initial radius $\Delta_{\min}$ at iteration $n$ is positive, and it is at most $\Delta_{\min}$
at every iteration $k \ge n$.

**Correction.** The floor is the corrected bound (10.2.24); see
`ConnGouldToint.Chapter10.structuredRadiusFloor`. -/
theorem structuredRadiusFloor_pos_and_le (run : StructuredTRRun P elements N β κ)
    {B C ε : ℝ} (hβ : ∀ k, β k ≤ B) (hC : 0 < C) (hε : 0 < ε) (n : ℕ)
    (hg : ∀ k ≥ n, ε ≤ ‖run.modelGradient k‖)
    (herr : ∀ k i, |run.actualDrop k i - run.predictedDrop k i| ≤ C * (run.Δ k i) ^ 2) :
    0 < structuredRadiusFloor P (Fintype.card ι) κ ε B C (minimumRadius (run.Δ n)) ∧
      ∀ k ≥ n, structuredRadiusFloor P (Fintype.card ι) κ ε B C (minimumRadius (run.Δ n)) ≤
        minimumRadius (run.Δ k) := by
  have hB : 0 < B := (run.β_pos 0).trans_le (hβ 0)
  have hp : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  let e := P.γ₁ * (κ * ε)
  have he : 0 < e := mul_pos P.gamma₁_pos (mul_pos run.κ_pos hε)
  let a := (1 - P.η₃) / (Fintype.card ι : ℝ)
  let b := (P.μ₂ - P.μ₁) / (Fintype.card ι : ℝ)
  have ha : 0 < a := div_pos (sub_pos.mpr P.eta₃_lt_one) hp
  have hb : 0 < b := div_pos (sub_pos.mpr P.mu₁_lt_mu₂) hp
  let θ := min (ε / B) (min (a * e / C) (b * e / C))
  have hθ : 0 < θ := lt_min (div_pos hε hB)
    (lt_min (div_pos (mul_pos ha he) hC) (div_pos (mul_pos hb he) hC))
  let δ := min (minimumRadius (run.Δ n)) (P.γ₁ * θ)
  have hδ : 0 < δ := lt_min (minimumRadius_pos _ (run.delta_pos n))
    (mul_pos P.gamma₁_pos hθ)
  change 0 < δ ∧ ∀ k ≥ n, δ ≤ minimumRadius (run.Δ k)
  refine ⟨hδ, fun k hk ↦ ?_⟩
  induction k, hk using Nat.le_induction with
  | base => exact min_le_left _ _
  | succ k hk ih =>
    apply le_minimumRadius
    intro i
    by_contra! hnext
    have hr := lemma_10_2_1_ii (run.radius_update k) (fun j ↦ (run.delta_pos k j).le) i
    have hiθ : run.Δ k i ≤ θ := by
      have h := hr.trans (hnext.le.trans (min_le_right _ _))
      exact le_of_mul_le_mul_left h P.gamma₁_pos
    have hminθ := (minimumRadius_le (run.Δ k) i).trans hiθ
    have hm := run.predicted_total_ge (hβ k) hε (hg k hk)
    rw [min_eq_right (hminθ.trans (min_le_left _ _))] at hm
    have hnextmin : run.Δ (k + 1) i ≤ minimumRadius (run.Δ k) := hnext.le.trans ih
    have hpred : e * run.Δ k i ≤ ∑ j, run.predictedDrop k j := by
      calc
        e * run.Δ k i = (κ * ε) * (P.γ₁ * run.Δ k i) := by dsimp [e]; ring
        _ ≤ (κ * ε) * minimumRadius (run.Δ k) :=
          mul_le_mul_of_nonneg_left (hr.trans hnextmin) (mul_nonneg run.κ_pos.le hε.le)
        _ ≤ _ := hm
    have hscale {c : ℝ} (hc : 0 ≤ c) (hic : run.Δ k i ≤ c * e / C) :
        |run.actualDrop k i - run.predictedDrop k i| ≤ c * ∑ j, run.predictedDrop k j := by
      have hmul : C * run.Δ k i ≤ c * e := by
        simpa only [mul_comm C] using (le_div_iff₀ hC).mp hic
      calc
        _ ≤ C * (run.Δ k i) ^ 2 := herr k i
        _ = (C * run.Δ k i) * run.Δ k i := by ring
        _ ≤ (c * e) * run.Δ k i :=
          mul_le_mul_of_nonneg_right hmul (run.delta_pos k i).le
        _ = c * (e * run.Δ k i) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hpred hc
    have haup : run.Δ k i ≤ a * e / C :=
      (hiθ.trans (min_le_right _ _)).trans (min_le_left _ _)
    have hbup : run.Δ k i ≤ b * e / C :=
      (hiθ.trans (min_le_right _ _)).trans (min_le_right _ _)
    have hu : StructuredRadiusUpdate P (run.predictedDrop k) (run.actualDrop k)
        (run.Δ k) (run.Δ (k + 1)) := run.radius_update k
    have hkeep := hu.noncontract_of_scaled_error i (hscale ha.le haup) (hscale hb.le hbup)
    exact hnext.not_ge ((ih.trans (minimumRadius_le (run.Δ k) i)).trans hkeep)

/-- **Theorem 10.2.5** of [conn2000trust], form with a model error bound. Let a structured
trust-region run be given, with $\beta_k \le B$ for all $k$, $C > 0$ and $\varepsilon > 0$.
Suppose that $|a_{k,i} - d_{k,i}| \le C \Delta_{k,i}^2$ and
$\|\nabla m_k(x_k)\| \ge \varepsilon$ for all $k$ and $i$. Then there is $\delta > 0$ with
$\delta \le \Delta_{\min}$ at every iteration.

**Correction.** The proof compares the model error directly with the two fit tolerances, as in
the corrected (10.2.24), and uses no bound on the element gradients. -/
theorem theorem_10_2_5_of_error_bound (run : StructuredTRRun P elements N β κ)
    {B C ε : ℝ} (hβ : ∀ k, β k ≤ B) (hC : 0 < C) (hε : 0 < ε)
    (hg : ∀ k, ε ≤ ‖run.modelGradient k‖)
    (herr : ∀ k i, |run.actualDrop k i - run.predictedDrop k i| ≤ C * (run.Δ k i) ^ 2) :
    ∃ δ > 0, ∀ k, δ ≤ minimumRadius (run.Δ k) := by
  obtain ⟨hδ, hr⟩ := structuredRadiusFloor_pos_and_le run hβ hC hε 0 (fun k _ ↦ hg k) herr
  exact ⟨_, hδ, fun k ↦ hr k (Nat.zero_le k)⟩

omit [Nonempty ι] in
private theorem StructuredRadiusUpdate.le_of_unsuccessful
    {d a Δ Δ' : ι → ℝ} (hu : StructuredRadiusUpdate P d a Δ Δ') (i : ι)
    (hΔ : 0 ≤ Δ i) (hs : ¬ structuredSuccessful P.η₁ d a) :
    Δ' i ≤ Δ i := by
  have hγ : P.γ₂ * Δ i ≤ Δ i := mul_le_of_le_one_left hΔ P.gamma₂_lt_one.le
  by_cases hn : i ∈ negligibleElements P.μ₁ d
  · by_cases hfit : negligibleFit P.μ₂ d a i
    · rw [hu.negligible_hold i hn hfit hs]
    · exact (hu.negligible_contract i hn hfit).2.trans hγ
  · have hm := mem_meaningfulElements.mpr hn
    by_cases hfit : elementFit P.η₃ d a i
    · rw [hu.meaningful_hold i hm hfit hs]
    · by_cases hfit₂ : elementFit P.η₂ d a i
      · exact (hu.meaningful_moderate i hm hfit hfit₂).2
      · exact (hu.meaningful_contract i hm hfit₂).2.trans hγ

private theorem StructuredRadiusUpdate.exists_contraction_of_unsuccessful
    {d a Δ Δ' : ι → ℝ} (hu : StructuredRadiusUpdate P d a Δ Δ')
    (hd : 0 < ∑ i, d i) (hs : ¬ structuredSuccessful P.η₁ d a) :
    ∃ i, Δ' i ≤ P.γ₂ * Δ i := by
  by_contra! hn
  apply hs
  exact (lemma_10_2_2 P hd
    (fun i hi ↦ by
      by_contra h
      exact (hn i).not_ge (hu.meaningful_contract i hi h).2)
    (fun i hi ↦ by
      by_contra h
      exact (hn i).not_ge (hu.negligible_contract i hi h).2)).2.2

/-- **Theorem 10.2.6** of [conn2000trust], form with a model error bound. Let a structured
trust-region run be given, with $\beta_k \le B$ for all $k$ and $C > 0$. Suppose that
$|a_{k,i} - d_{k,i}| \le C \Delta_{k,i}^2$ for all $k$ and $i$, that
$\nabla m_k(x_k) = \nabla f(x_k)$ for all $k$, and that there are only finitely many successful
iterations. Then there is $x$ with $x_k = x$ for all large $k$ and $\nabla f(x) = 0$, where
$f = \sum_i f_i$.

After the last successful iteration the iterate is constant. At every unsuccessful iteration at
least one radius contracts and none grows. A nonzero gradient would give a positive floor on the
radii, which contradicts the resulting uniform decrease of the sum of the radii. -/
theorem theorem_10_2_6_of_error_bound (run : StructuredTRRun P elements N β κ)
    {B C : ℝ} (hβ : ∀ k, β k ≤ B) (hC : 0 < C)
    (herr : ∀ k i, |run.actualDrop k i - run.predictedDrop k i| ≤ C * (run.Δ k i) ^ 2)
    (hgrad : ∀ k, run.modelGradient k = run.objectiveGradient k)
    (hfinite : run.successful.Finite) :
    ∃ x, (∀ᶠ k in Filter.atTop, run.x k = x) ∧ gradient (fun z ↦ ∑ i, elements i z) x = 0 := by
  obtain ⟨J, hJ⟩ := hfinite.bddAbove
  let n := J + 1
  have hfail (k : ℕ) (hk : n ≤ k) : k ∉ run.successful := by
    intro h
    have hle := hJ h
    change J + 1 ≤ k at hk
    omega
  have hx (k : ℕ) (hk : n ≤ k) : run.x k = run.x n := by
    induction k, hk using Nat.le_induction with
    | base => rfl
    | succ k hk ih =>
      have hs : ¬ structuredSuccessful P.η₁
          (fun i ↦ run.model k i (run.x k) - run.model k i (run.x k + run.s k))
          (fun i ↦ elements i (run.x k) - elements i (run.x k + run.s k)) := hfail k hk
      rw [run.iterate_update, ite_eq_right hs, ih]
  refine ⟨run.x n, Filter.eventually_atTop.mpr ⟨n, hx⟩, ?_⟩
  change run.objectiveGradient n = 0
  by_contra hn
  let ε := ‖run.objectiveGradient n‖
  have hε : 0 < ε := norm_pos_iff.mpr hn
  have hg (k : ℕ) (hk : n ≤ k) : ε ≤ ‖run.modelGradient k‖ := by
    rw [hgrad k]
    unfold StructuredTRRun.objectiveGradient
    rw [hx k hk]
    exact le_rfl
  let δ := structuredRadiusFloor P (Fintype.card ι) κ ε B C (minimumRadius (run.Δ n))
  obtain ⟨hδ, hfloor⟩ := structuredRadiusFloor_pos_and_le run hβ hC hε n hg herr
  let c := (1 - P.γ₂) * δ
  have hc : 0 < c := mul_pos (sub_pos.mpr P.gamma₂_lt_one) hδ
  let total (k : ℕ) := ∑ i, run.Δ k i
  have htotal (k : ℕ) : 0 ≤ total k := Finset.sum_nonneg (fun i _ ↦ (run.delta_pos k i).le)
  have hdrop (k : ℕ) (hk : n ≤ k) : c ≤ total k - total (k + 1) := by
    have hu : StructuredRadiusUpdate P (run.predictedDrop k) (run.actualDrop k)
        (run.Δ k) (run.Δ (k + 1)) := run.radius_update k
    have hfailed : ¬ structuredSuccessful P.η₁ (run.predictedDrop k) (run.actualDrop k) :=
      hfail k hk
    obtain ⟨i, hi⟩ := hu.exists_contraction_of_unsuccessful (run.predicted_pos k) hfailed
    have hδi := (hfloor k hk).trans (minimumRadius_le (run.Δ k) i)
    have hstep : c ≤ run.Δ k i - run.Δ (k + 1) i := calc
      _ ≤ (1 - P.γ₂) * run.Δ k i :=
        mul_le_mul_of_nonneg_left hδi (sub_nonneg.mpr P.gamma₂_lt_one.le)
      _ = run.Δ k i - P.γ₂ * run.Δ k i := by ring
      _ ≤ _ := sub_le_sub_left hi _
    have hsum : run.Δ k i - run.Δ (k + 1) i ≤ ∑ j, (run.Δ k j - run.Δ (k + 1) j) :=
      Finset.single_le_sum
        (fun j _ ↦ sub_nonneg.mpr (hu.le_of_unsuccessful j (run.delta_pos k j).le hfailed))
        (Finset.mem_univ i)
    rw [Finset.sum_sub_distrib] at hsum
    exact hstep.trans hsum
  have hdec (j : ℕ) : total (n + j) + (j : ℝ) * c ≤ total n := by
    induction j with
    | zero => simp
    | succ j ih =>
      have h := hdrop (n + j) (Nat.le_add_right _ _)
      push_cast
      rw [← Nat.add_assoc]
      linarith only [h, ih]
  obtain ⟨j, hj⟩ := exists_nat_gt (total n / c)
  exact (not_lt_of_ge (by linarith [hdec j, htotal (n + j)] : (j : ℝ) * c ≤ total n))
    ((div_lt_iff₀ hc).mp hj)

variable [∀ i, (N i).HasOrthogonalProjection]

/-- **Equation (6.3.1)** of [conn2000trust], for the total model of a structured run. The
**aggregate curvature** at iteration $k$ is
$$1 + \sup\{\|\nabla^2 m_k(z)\| : z \text{ in the structured trust region of iteration } k\},$$
where $m_k = \sum_i m_{k,i}$.

The supremum is `sSup`, which is $0$ for a set that is not bounded above. -/
noncomputable def StructuredTRRun.aggregateCurvature (run : StructuredTRRun P elements N β κ)
    (k : ℕ) : ℝ :=
  1 + sSup ((fun z ↦ ‖fderiv ℝ (fderiv ℝ (fun x ↦ ∑ i, run.model k i x)) z‖) ''
    structuredTrustRegion (run.p k) N (run.x k) (run.Δ k))

/-- **Equation (6.3.2)** of [conn2000trust], with the aggregate bound under AM.4s. Let a structured
trust-region run be given. Suppose that every model $m_{k,i}$ is twice continuously
differentiable at every point of the structured trust region, with
$\|\nabla^2 m_{k,i}(z)\| \le \kappa_m - 1$ there. Then the aggregate curvature at every
iteration $k$ is at most $1 + p (\kappa_m - 1)$.

The factor $p$ allows the Hessians of the elements to overlap. -/
theorem StructuredTRRun.aggregateCurvature_le (run : StructuredTRRun P elements N β κ)
    {κm : ℝ}
    (hmodel : ∀ k i z, z ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) →
      ContDiffAt ℝ 2 (run.model k i) z)
    (hM : ∀ k i z, z ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) →
      ‖fderiv ℝ (fderiv ℝ (run.model k i)) z‖ ≤ κm - 1)
    (k : ℕ) : run.aggregateCurvature k ≤ 1 + Fintype.card ι * (κm - 1) := by
  have hx : run.x k ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) := by
    simpa only [zero_smul, add_zero] using run.segment_mem k (show (0 : ℝ) ∈ Icc 0 1 by simp)
  unfold StructuredTRRun.aggregateCurvature
  apply add_le_add le_rfl
  apply csSup_le (Set.Nonempty.image _ ⟨run.x k, hx⟩)
  rintro _ ⟨z, hz, rfl⟩
  dsimp only
  have hloc : ∀ᶠ y in 𝓝 z, ∀ i, DifferentiableAt ℝ (run.model k i) y :=
    Filter.eventually_all.mpr fun i ↦ ((hmodel k i z hz).eventually (by norm_num)).mono
      (fun _ h ↦ h.differentiableAt (by norm_num))
  have hsum :
      fderiv ℝ (fun x ↦ ∑ i, run.model k i x) =ᶠ[𝓝 z]
        (fun y ↦ ∑ i, fderiv ℝ (run.model k i) y) :=
    hloc.mono fun _ hy ↦ fderiv_fun_sum (fun i _ ↦ hy i)
  have hsecond :
      fderiv ℝ (fun y ↦ ∑ i, fderiv ℝ (run.model k i) y) z =
        ∑ i, fderiv ℝ (fderiv ℝ (run.model k i)) z :=
    fderiv_fun_sum (fun i _ ↦
      ((hmodel k i z hz).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  rw [hsum.fderiv_eq (𝕜 := ℝ), hsecond]
  let H : ι → E →L[ℝ] E →L[ℝ] ℝ := fun i ↦ fderiv ℝ (fderiv ℝ (run.model k i)) z
  have hnorm : ‖∑ i, H i‖ ≤ ∑ i, ‖H i‖ := norm_sum_le Finset.univ H
  have hsumBound : (∑ i, ‖H i‖) ≤ ∑ _i : ι, (κm - 1) :=
    Finset.sum_le_sum (fun i _ ↦ hM k i z hz)
  have hconst : (∑ _i : ι, (κm - 1)) = Fintype.card ι * (κm - 1) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change ‖∑ i, H i‖ ≤ Fintype.card ι * (κm - 1)
  exact hnorm.trans (hsumBound.trans_eq hconst)

private theorem StructuredTRRun.gradients_agree (run : StructuredTRRun P elements N β κ)
    (hf : ∀ i, ContDiff ℝ 2 (elements i))
    (hmodel : ∀ k i z, z ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) →
      ContDiffAt ℝ 2 (run.model k i) z)
    (hgrad : ∀ k i, fderiv ℝ (run.model k i) (run.x k) = fderiv ℝ (elements i) (run.x k))
    (k : ℕ) : run.modelGradient k = run.objectiveGradient k := by
  have hx : run.x k ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) := by
    simpa only [zero_smul, add_zero] using run.segment_mem k (show (0 : ℝ) ∈ Icc 0 1 by simp)
  unfold StructuredTRRun.modelGradient StructuredTRRun.objectiveGradient gradient
  rw [fderiv_fun_sum (fun i _ ↦ (hmodel k i _ hx).differentiableAt (by norm_num)),
    fderiv_fun_sum (fun i _ ↦ (hf i).differentiable (by norm_num) _)]
  simp only [hgrad]

private theorem StructuredTRRun.drop_error (run : StructuredTRRun P elements N β κ)
    {K κf κm : ℝ} (hK : 1 ≤ K) (hκf : 1 ≤ κf) (hκm : 1 ≤ κm)
    (hnorm : ∀ k v, ‖v‖ ≤ K * run.p k v)
    (hf : ∀ i, ContDiff ℝ 2 (elements i))
    (hF : ∀ i z, z ∈ (N i)ᗮ → ‖fderiv ℝ (fderiv ℝ (elements i)) z‖ ≤ κf)
    (hmodel : ∀ k i z, z ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) →
      ContDiffAt ℝ 2 (run.model k i) z)
    (hM : ∀ k i z, z ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) →
      ‖fderiv ℝ (fderiv ℝ (run.model k i)) z‖ ≤ κm - 1)
    (hval : ∀ k i, run.model k i (run.x k) = elements i (run.x k))
    (hgrad : ∀ k i, fderiv ℝ (run.model k i) (run.x k) = fderiv ℝ (elements i) (run.x k))
    (k : ℕ) (i : ι) :
    |run.actualDrop k i - run.predictedDrop k i| ≤
      uniformHessianConstant K κf κm * (run.Δ k i) ^ 2 := by
  have heq : run.actualDrop k i - run.predictedDrop k i =
      -(elements i (run.x k + run.s k) - run.model k i (run.x k + run.s k)) := by
    unfold StructuredTRRun.actualDrop StructuredTRRun.predictedDrop
    rw [hval k i]
    ring
  rw [heq, abs_neg]
  exact (theorem_10_2_3 run hK hκf hκm hnorm hf hF
    (fun j l z hz ↦ (hmodel j l z hz).differentiableAt (by norm_num))
    (fun j l z hz ↦ ((hmodel j l z hz).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)) hM hval hgrad k i).2

private theorem uniformHessianConstant_pos {K κf κm : ℝ} (hK : 1 ≤ K) (hκf : 1 ≤ κf) :
    0 < uniformHessianConstant K κf κm :=
  mul_pos (pow_pos (zero_lt_one.trans_le hK) 2)
    ((zero_lt_one.trans_le hκf).trans_le (le_max_left _ _))

/-- **Theorem 10.2.5** of [conn2000trust]. Let a structured trust-region run be given, with
$K \ge 1$, $\kappa_f \ge 1$, $\kappa_m \ge 1$ and $\|v\| \le K p_k(v)$ for all $k$ and $v$.
Suppose that every $f_i$ is twice continuously differentiable with
$\|\nabla^2 f_i(z)\| \le \kappa_f$ for $z \in N_i^\perp$, that every model $m_{k,i}$ is twice
continuously differentiable on the structured trust region with
$\|\nabla^2 m_{k,i}(z)\| \le \kappa_m - 1$ there, that $m_{k,i}(x_k) = f_i(x_k)$ and
$\nabla m_{k,i}(x_k) = \nabla f_i(x_k)$, and that $\beta_k$ is the aggregate curvature at
iteration $k$. If $\varepsilon > 0$ and $\|\nabla m_k(x_k)\| \ge \varepsilon$ for all $k$, then
there is $\delta > 0$ with $\delta \le \Delta_{\min}$ at every iteration.

The element error bound comes from Theorem 10.2.3, and the proof applies
`ConnGouldToint.Chapter10.theorem_10_2_5_of_error_bound`. -/
theorem theorem_10_2_5 (run : StructuredTRRun P elements N β κ)
    {K κf κm ε : ℝ} (hK : 1 ≤ K) (hκf : 1 ≤ κf) (hκm : 1 ≤ κm)
    (hnorm : ∀ k v, ‖v‖ ≤ K * run.p k v)
    (hf : ∀ i, ContDiff ℝ 2 (elements i))
    (hF : ∀ i z, z ∈ (N i)ᗮ → ‖fderiv ℝ (fderiv ℝ (elements i)) z‖ ≤ κf)
    (hmodel : ∀ k i z, z ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) →
      ContDiffAt ℝ 2 (run.model k i) z)
    (hM : ∀ k i z, z ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) →
      ‖fderiv ℝ (fderiv ℝ (run.model k i)) z‖ ≤ κm - 1)
    (hval : ∀ k i, run.model k i (run.x k) = elements i (run.x k))
    (hgrad : ∀ k i, fderiv ℝ (run.model k i) (run.x k) = fderiv ℝ (elements i) (run.x k))
    (hβ : ∀ k, β k = run.aggregateCurvature k)
    (hε : 0 < ε) (hg : ∀ k, ε ≤ ‖run.modelGradient k‖) :
    ∃ δ > 0, ∀ k, δ ≤ minimumRadius (run.Δ k) :=
  theorem_10_2_5_of_error_bound run
    (fun k ↦ (hβ k).le.trans (run.aggregateCurvature_le hmodel hM k))
    (uniformHessianConstant_pos hK hκf) hε hg
    (run.drop_error hK hκf hκm hnorm hf hF hmodel hM hval hgrad)

/-- **Theorem 10.2.6** of [conn2000trust]. Let a structured trust-region run satisfy the hypotheses
of `ConnGouldToint.Chapter10.theorem_10_2_5` except the gradient bound, including
$\|v\| \le K p_k(v)$ for all $k$ and $v$ (AN.1). If there are only finitely many successful
iterations, then there is $x$ with $x_k = x$ for all large $k$ and $\nabla f(x) = 0$, where
$f = \sum_i f_i$.

**Correction.** The theorem needs the uniform norm comparison AN.1. Without it, every trial can
be rejected at a fixed noncritical iterate; see
`ConnGouldToint.Chapter10.theorem_10_2_6_without_norm_bound_counterexample`.

The proof uses the lower norm comparison of AN.1 and does not need the bound AF.5s on the
element gradients. It applies `ConnGouldToint.Chapter10.theorem_10_2_6_of_error_bound`. -/
theorem theorem_10_2_6 (run : StructuredTRRun P elements N β κ)
    {K κf κm : ℝ} (hK : 1 ≤ K) (hκf : 1 ≤ κf) (hκm : 1 ≤ κm)
    (hnorm : ∀ k v, ‖v‖ ≤ K * run.p k v)
    (hf : ∀ i, ContDiff ℝ 2 (elements i))
    (hF : ∀ i z, z ∈ (N i)ᗮ → ‖fderiv ℝ (fderiv ℝ (elements i)) z‖ ≤ κf)
    (hmodel : ∀ k i z, z ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) →
      ContDiffAt ℝ 2 (run.model k i) z)
    (hM : ∀ k i z, z ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) →
      ‖fderiv ℝ (fderiv ℝ (run.model k i)) z‖ ≤ κm - 1)
    (hval : ∀ k i, run.model k i (run.x k) = elements i (run.x k))
    (hgrad : ∀ k i, fderiv ℝ (run.model k i) (run.x k) = fderiv ℝ (elements i) (run.x k))
    (hβ : ∀ k, β k = run.aggregateCurvature k) (hfinite : run.successful.Finite) :
    ∃ x, (∀ᶠ k in Filter.atTop, run.x k = x) ∧ gradient (fun z ↦ ∑ i, elements i z) x = 0 :=
  theorem_10_2_6_of_error_bound run
    (fun k ↦ (hβ k).le.trans (run.aggregateCurvature_le hmodel hM k))
    (uniformHessianConstant_pos hK hκf)
    (run.drop_error hK hκf hκm hnorm hf hF hmodel hM hval hgrad)
    (run.gradients_agree hf hmodel hgrad) hfinite

end Convergence

section MissingNormEquivalence

open scoped NNReal

private abbrev CounterSpace := EuclideanSpace ℝ (Fin 2)
private noncomputable def counterCoord : CounterSpace →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0

private noncomputable def counterNull (_ : Unit) : Submodule ℝ CounterSpace :=
  LinearMap.ker counterCoord.toLinearMap

private noncomputable def counterObjective (_ : Unit) (x : CounterSpace) : ℝ :=
  Real.sin (counterCoord x)

private noncomputable def counterStep : CounterSpace := EuclideanSpace.single 0 (-Real.pi)

private noncomputable def counterRadius (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ k

private theorem counterRadius_pos (k : ℕ) : 0 < counterRadius k := by
  unfold counterRadius
  positivity

private noncomputable def counterNorm (k : ℕ) : Seminorm ℝ CounterSpace :=
  (counterRadius k / Real.pi).toNNReal • normSeminorm ℝ CounterSpace

private theorem counterNorm_apply (k : ℕ) (x : CounterSpace) :
    counterNorm k x = (counterRadius k / Real.pi) * ‖x‖ := by
  rw [counterNorm, smul_apply, NNReal.smul_def,
    Real.coe_toNNReal _ (div_nonneg (counterRadius_pos k).le Real.pi_pos.le)]
  rfl

private theorem counterCoord_step : counterCoord counterStep = -Real.pi := by
  simp [counterCoord, counterStep, PiLp.proj_apply]

private theorem counterStep_norm : ‖counterStep‖ = Real.pi := by
  rw [counterStep, PiLp.norm_single, Real.norm_eq_abs, abs_neg, abs_of_pos Real.pi_pos]

private theorem counterCoord_norm_le : ‖counterCoord‖ ≤ 1 :=
  counterCoord.opNorm_le_bound zero_le_one fun x ↦ by
    simpa only [counterCoord, PiLp.proj_apply, one_mul] using PiLp.norm_apply_le x (0 : Fin 2)

private theorem counterCoord_ne_zero : counterCoord ≠ 0 := by
  intro h
  have hc := DFunLike.congr_fun h counterStep
  rw [counterCoord_step] at hc
  simpa using (Real.pi_ne_zero (neg_eq_zero.mp hc))

private theorem counterNull_ne_bot (i : Unit) : counterNull i ≠ ⊥ := by
  let y : CounterSpace := EuclideanSpace.single 1 1
  have hy : y ∈ counterNull i := by
    change counterCoord y = 0
    simp [y, counterCoord, PiLp.proj_apply]
  intro h
  rw [h, Submodule.mem_bot] at hy
  have he := congrArg (fun v : CounterSpace ↦ v 1) hy
  simp [y] at he

private noncomputable def counterParams : StructuredTRParams where
  η₁ := 1 / 10
  η₂ := 1 / 2
  η₃ := 3 / 4
  μ₁ := 1 / 10
  μ₂ := 1 / 5
  γ₁ := 1 / 2
  γ₂ := 1 / 2
  eta₁_pos := by norm_num
  eta₁_le_eta₂ := by norm_num
  eta₂_lt_one := by norm_num
  gamma₁_pos := by norm_num
  gamma₁_le_gamma₂ := le_rfl
  gamma₂_lt_one := by norm_num
  eta₂_lt_eta₃ := by norm_num
  eta₃_lt_one := by norm_num
  mu₁_pos := by norm_num
  mu₁_lt_mu₂ := by norm_num
  mu₂_lt_one := by norm_num
  compatible := by norm_num

private theorem counter_not_successful :
    ¬ structuredSuccessful counterParams.η₁ (fun _ : Unit ↦ Real.pi) (fun _ ↦ 0) := by
  simp [structuredSuccessful, counterParams, Real.pi_pos]

private theorem counter_no_fit₂ (i : Unit) :
    ¬ elementFit counterParams.η₂ (fun _ : Unit ↦ Real.pi) (fun _ ↦ 0) i := by
  simp [elementFit, counterParams]
  linarith [Real.pi_pos]

private theorem counter_no_fit₃ (i : Unit) :
    ¬ elementFit counterParams.η₃ (fun _ : Unit ↦ Real.pi) (fun _ ↦ 0) i := by
  simp [elementFit, counterParams]
  linarith [Real.pi_pos]

private theorem counter_not_negligible (i : Unit) :
    i ∉ negligibleElements counterParams.μ₁ (fun _ : Unit ↦ Real.pi) := by
  classical
  have hp : ¬ Real.pi ≤ (1 / 10 : ℝ) * Real.pi := by linarith [Real.pi_pos]
  simp only [negligibleElements, Finset.mem_filter, Finset.mem_univ, true_and]
  simpa [counterParams, abs_of_pos Real.pi_pos] using hp

private theorem counter_update (k : ℕ) :
    StructuredRadiusUpdate counterParams (fun _ : Unit ↦ Real.pi) (fun _ ↦ 0)
      (fun _ ↦ counterRadius k) (fun _ ↦ counterRadius (k + 1)) := by
  have hr : counterRadius (k + 1) = (1 / 2) * counterRadius k := by
    simp only [counterRadius, pow_succ, mul_comm]
  constructor
  · exact fun i _ hf _ ↦ (counter_no_fit₃ i hf).elim
  · exact fun i _ hf _ ↦ (counter_no_fit₃ i hf).elim
  · exact fun i _ _ hf ↦ (counter_no_fit₂ i hf).elim
  · intro i _ _
    constructor <;> simpa only [counterParams, hr] using le_rfl
  · exact fun i hi _ _ ↦ (counter_not_negligible i hi).elim
  · exact fun i hi _ _ ↦ (counter_not_negligible i hi).elim
  · exact fun i hi _ ↦ (counter_not_negligible i hi).elim

private theorem counterObjectives_drop :
    counterObjective () 0 - counterObjective () (0 + counterStep) = 0 := by
  simp [counterObjective, counterCoord_step, Real.sin_neg]

private theorem counterPredictedDrop :
    (fun _ : Unit ↦ counterCoord 0 - counterCoord (0 + counterStep)) = fun _ ↦ Real.pi := by
  funext i
  simp [counterCoord_step]

private theorem counterActualDrop :
    (fun i : Unit ↦ counterObjective i 0 - counterObjective i (0 + counterStep)) = fun _ ↦ 0 :=
  funext fun i ↦ by cases i; exact counterObjectives_drop

private noncomputable def counterRun :
    StructuredTRRun counterParams counterObjective counterNull (fun _ ↦ 1) (Real.pi / 2) where
  x := fun _ ↦ 0
  s := fun _ ↦ counterStep
  p := counterNorm
  model := fun _ _ ↦ counterCoord
  Δ := fun k _ ↦ counterRadius k
  norm_separates := by
    intro k v h
    rw [counterNorm_apply] at h
    exact norm_eq_zero.mp ((mul_eq_zero.mp h).resolve_left
      (div_pos (counterRadius_pos k) Real.pi_pos).ne')
  invariant_nontrivial := counterNull_ne_bot
  objective_invariant := by
    intro i x w hw
    change counterCoord w = 0 at hw
    simp [counterObjective, map_add, hw]
  model_invariant := by
    intro k i x w hw
    change counterCoord w = 0 at hw
    simp [map_add, hw]
  initial_pos := fun _ ↦ counterRadius_pos 0
  β_pos := fun _ ↦ zero_lt_one
  κ_pos := half_pos Real.pi_pos
  feasible := by
    intro k
    rw [structuredTrustRegion, mem_iInter]
    intro i
    change counterNorm k ((counterNull i)ᗮ.starProjection (0 + counterStep - 0)) ≤ counterRadius k
    rw [zero_add, sub_zero, counterNorm_apply]
    have h := ((counterNull i)ᗮ.norm_starProjection_apply_le counterStep).trans_eq counterStep_norm
    calc
      _ ≤ counterRadius k / Real.pi * Real.pi :=
        mul_le_mul_of_nonneg_left h (div_nonneg (counterRadius_pos k).le Real.pi_pos.le)
      _ = _ := div_mul_cancel₀ _ Real.pi_ne_zero
  sufficient := by
    intro k
    unfold structuredSufficientDecrease
    simp only [Fintype.sum_unique, div_one, zero_add, map_zero, counterCoord_step,
      zero_sub, neg_neg]
    let g := ‖gradient (counterCoord : CounterSpace → ℝ) 0‖
    have hg : g ≤ 1 := by
      simpa only [g, gradient, LinearIsometryEquiv.norm_map, counterCoord.fderiv] using
        counterCoord_norm_le
    change Real.pi / 2 * g * min g _ ≤ Real.pi
    have hp : 0 ≤ Real.pi / 2 * g := mul_nonneg (half_pos Real.pi_pos).le (norm_nonneg _)
    calc
      _ ≤ Real.pi / 2 * g * g := mul_le_mul_of_nonneg_left (min_le_left _ _) hp
      _ ≤ Real.pi / 2 * 1 * 1 := by gcongr
      _ ≤ _ := by linarith [Real.pi_pos]
  predicted_pos := by simp [counterCoord_step, Real.pi_pos]
  radius_update := by
    intro k
    rw [counterPredictedDrop, counterActualDrop]
    exact counter_update k
  iterate_update := by
    intro k
    rw [counterPredictedDrop, counterActualDrop, ite_eq_right counter_not_successful]

private theorem counterObjective_fderiv (i : Unit) (x : CounterSpace) :
    fderiv ℝ (counterObjective i) x = Real.cos (counterCoord x) • counterCoord :=
  ((Real.hasDerivAt_sin (counterCoord x)).comp_hasFDerivAt x counterCoord.hasFDerivAt).fderiv

private theorem counterObjective_hessian_norm_le (i : Unit) (x : CounterSpace) :
    ‖fderiv ℝ (fderiv ℝ (counterObjective i)) x‖ ≤ 1 := by
  have hcos : HasFDerivAt (fun y ↦ Real.cos (counterCoord y))
      ((-Real.sin (counterCoord x)) • counterCoord) x :=
    (Real.hasDerivAt_cos (counterCoord x)).comp_hasFDerivAt x counterCoord.hasFDerivAt
  rw [show fderiv ℝ (counterObjective i) =
    fun y ↦ Real.cos (counterCoord y) • counterCoord from funext (counterObjective_fderiv i),
    (hcos.smul_const counterCoord).fderiv,
    ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_eq_abs, abs_neg]
  calc
    |Real.sin (counterCoord x)| * ‖counterCoord‖ * ‖counterCoord‖ ≤ 1 * 1 * 1 := by
      exact mul_le_mul
        (mul_le_mul (Real.abs_sin_le_one _) counterCoord_norm_le (norm_nonneg _) zero_le_one)
        counterCoord_norm_le (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

private theorem counterModel_hessian (z : CounterSpace) :
    fderiv ℝ (fderiv ℝ (counterCoord : CounterSpace → ℝ)) z = 0 := by
  rw [show fderiv ℝ (counterCoord : CounterSpace → ℝ) = fun _ ↦ counterCoord from
    funext fun _ ↦ counterCoord.fderiv]
  exact fderiv_const_apply _

/-- **Theorem 10.2.6** of [conn2000trust], counterexample without AN.1. There are structured
parameters, a single element $f$ on $\mathbb{R}^2$ with an invariant subspace, and a structured
trust-region run with $\beta_k = 1$ and $\kappa = \pi / 2$, such that:

* $f$ is twice continuously differentiable with $\|\nabla^2 f(z)\| \le 1$ and
  $\|\nabla f(z)\| \le 1$ for all $z$;
* every model is twice continuously differentiable with zero Hessian, and agrees with $f$ in
  value and derivative at the iterate;
* the aggregate curvature is $1$ at every iteration;
* no iteration is successful, and $x_k = 0$ with $\nabla f(x_k) \neq 0$ for all $k$;
* for every $K$ there are $k$ and $v$ with $K p_k(v) < \|v\|$.

So all trials are rejected at a fixed noncritical iterate, although the element and the models
satisfy uniform smoothness and gradient bounds. This shows that the hypothesis AN.1 of
`ConnGouldToint.Chapter10.theorem_10_2_6` is needed. The construction has $f(x) = \sin x_1$, the
model $x \mapsto x_1$, the step $-\pi e_1$ and the seminorms $p_k = (2^{-k} / \pi) \|\cdot\|$. -/
theorem theorem_10_2_6_without_norm_bound_counterexample :
    ∃ (P : StructuredTRParams)
      (f : Unit → EuclideanSpace ℝ (Fin 2) → ℝ)
      (N : Unit → Submodule ℝ (EuclideanSpace ℝ (Fin 2)))
      (run : StructuredTRRun P f N (fun _ ↦ 1) (Real.pi / 2)),
      (∀ i, ContDiff ℝ 2 (f i)) ∧
      (∀ i z, ‖fderiv ℝ (fderiv ℝ (f i)) z‖ ≤ 1) ∧
      (∀ i z, ‖gradient (f i) z‖ ≤ 1) ∧
      (∀ k i z, ContDiffAt ℝ 2 (run.model k i) z) ∧
      (∀ k i z, fderiv ℝ (fderiv ℝ (run.model k i)) z = 0) ∧
      (∀ k i, run.model k i (run.x k) = f i (run.x k) ∧
        fderiv ℝ (run.model k i) (run.x k) = fderiv ℝ (f i) (run.x k)) ∧
      (∀ k, run.aggregateCurvature k = 1) ∧
      run.successful = ∅ ∧
      (∀ k, run.x k = 0 ∧ run.objectiveGradient k ≠ 0) ∧
      ∀ K : ℝ, ∃ k v, K * run.p k v < ‖v‖ := by
  refine ⟨counterParams, counterObjective, counterNull, counterRun, ?_,
    counterObjective_hessian_norm_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Real.contDiff_sin.comp counterCoord.contDiff
  · intro i z
    rw [gradient, LinearIsometryEquiv.norm_map, counterObjective_fderiv,
      norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ 1 * 1 := mul_le_mul (Real.abs_cos_le_one _) counterCoord_norm_le
        (norm_nonneg _) zero_le_one
      _ = _ := by norm_num
  · intro k i z
    exact counterCoord.contDiff.contDiffAt
  · intro k i z
    exact counterModel_hessian z
  · intro k i
    change counterCoord 0 = counterObjective i 0 ∧
      fderiv ℝ (counterCoord : CounterSpace → ℝ) 0 = fderiv ℝ (counterObjective i) 0
    simp [counterObjective, counterObjective_fderiv, counterCoord.fderiv]
  · intro k
    unfold StructuredTRRun.aggregateCurvature
    have hfun : (fun x : CounterSpace ↦ ∑ i, counterRun.model k i x) = counterCoord := by
      funext x
      simp only [Fintype.sum_unique]
      rfl
    rw [hfun]
    simp only [counterModel_hessian]
    have hmem : (0 : CounterSpace) ∈ structuredTrustRegion (counterRun.p k) counterNull
        (counterRun.x k) (counterRun.Δ k) := by
      rw [structuredTrustRegion, mem_iInter]
      intro i
      change counterNorm k ((counterNull i)ᗮ.starProjection (0 - 0)) ≤ counterRadius k
      simp [(counterRadius_pos k).le]
    rw [Set.Nonempty.image_const ⟨0, hmem⟩, csSup_singleton]
    have hzero : ‖(0 : CounterSpace →L[ℝ] CounterSpace →L[ℝ] ℝ)‖ = 0 :=
      ContinuousLinearMap.opNorm_zero
    rw [hzero, add_zero]
  · ext k
    have ha : counterRun.actualDrop k = (fun _ : Unit ↦ 0) := counterActualDrop
    have hd : counterRun.predictedDrop k = (fun _ : Unit ↦ Real.pi) := counterPredictedDrop
    simp only [StructuredTRRun.successful, mem_ofPred_eq, ha, hd, mem_empty_iff_false, iff_false]
    exact counter_not_successful
  · intro k
    refine ⟨rfl, ?_⟩
    unfold StructuredTRRun.objectiveGradient gradient
    simp only [Fintype.sum_unique]
    change (InnerProductSpace.toDual ℝ CounterSpace).symm
      (fderiv ℝ (counterObjective ()) 0) ≠ 0
    rw [counterObjective_fderiv, map_zero, Real.cos_zero, one_smul]
    intro h
    apply counterCoord_ne_zero
    exact (InnerProductSpace.toDual ℝ CounterSpace).symm.injective (h.trans (map_zero _).symm)
  · intro K
    have hnorm (k : ℕ) : counterRun.p k counterStep = counterRadius k := by
      change counterNorm k counterStep = counterRadius k
      rw [counterNorm_apply, counterStep_norm, div_mul_cancel₀ _ Real.pi_ne_zero]
    have ht : Filter.Tendsto (fun k ↦ K * counterRun.p k counterStep) Filter.atTop (𝓝 0) := by
      simp only [hnorm, counterRadius]
      simpa only [mul_zero] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
          (by norm_num)).const_mul K
    obtain ⟨k, hk⟩ := (ht.eventually (gt_mem_nhds Real.pi_pos)).exists
    exact ⟨k, counterStep, by simpa only [counterStep_norm] using hk⟩

end MissingNormEquivalence

end ConnGouldToint.Chapter10
