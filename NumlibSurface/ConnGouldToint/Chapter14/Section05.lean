/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter14.Section02
import NumlibSurface.ConnGouldToint.Chapter15.Section03
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Conn, Gould and Toint, Section 14.5: Nonsmooth exact penalties

This module formalizes the nonsmooth exact penalty function of [conn2000trust], Section 14.5. The
constraints are $c(x) \in C$ for a set $C$ of feasible residuals in a normed space $Z$, which can
encode both equalities and inequalities. The penalty function is $\phi(x, \sigma) = f(x) + \sigma
\operatorname{dist}(c(x), C)$. Theorem 14.5.1 shows that, for a penalty weight $\sigma$ strictly
larger than the norm of the multiplier, the second-order sufficient conditions of the constrained
problem and of the penalty function agree. Theorem 14.5.2 shows that a weight below the norm of the
multiplier fails to make a KKT point a local minimizer of the penalty function, when the constraint
derivative is surjective. Counterexamples show that both hypotheses are needed.

## Main definitions

* Equation (14.5.1), `ConnGouldToint.Chapter14.nonsmoothExactPenalty`: the penalty function
  $f(x) + \sigma \operatorname{dist}(c(x), C)$.

## Main results

* Theorem 14.5.1, `ConnGouldToint.Chapter14.theorem_14_5_1`: equivalence of the second-order tests
  for $\sigma > \|\ell\|$.
* Theorem 14.5.1, `ConnGouldToint.Chapter14.theorem_14_5_1_threshold_counterexample`: the
  equivalence fails at the threshold $\sigma = \|\ell\|$.
* Theorem 14.5.2, `ConnGouldToint.Chapter14.theorem_14_5_2`: for $\sigma < \|\ell\|$ and a
  surjective constraint derivative, a stationary point is not a local minimizer of the penalty
  function.
* Theorem 14.5.2, `ConnGouldToint.Chapter14.theorem_14_5_2_redundant_constraint_counterexample`:
  without surjectivity, the conclusion fails.

## Conventions

* Stationarity is written $g + \ell \circ A = 0$, with a multiplier functional $\ell$ on $Z$; for
  equality constraints, $\ell = -\langle y, \cdot \rangle$ in terms of the multiplier $y$ of
  (14.2.3).

## Deviations from the source

* **Theorem 14.5.1** (correction). The penalty weight must be strictly larger than the threshold
  (14.5.2). At the nonstrict threshold the equivalence fails. See
  `ConnGouldToint.Chapter14.theorem_14_5_1` and
  `ConnGouldToint.Chapter14.theorem_14_5_1_threshold_counterexample`.
* **Theorem 14.5.2** (correction). The constraint derivative must be surjective. With a redundant
  constraint, a multiplier can exceed the penalty weight at a minimizer of the penalty function. See
  `ConnGouldToint.Chapter14.theorem_14_5_2` and
  `ConnGouldToint.Chapter14.theorem_14_5_2_redundant_constraint_counterexample`.
-/

open Filter Topology Set
open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter14

variable {E Z : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- **Equation (14.5.1)** of [conn2000trust]. Let $C \subseteq Z$ be the set of feasible residuals
and $\sigma \in \mathbb{R}$ the penalty weight. The **nonsmooth exact penalty function** is
$$\phi(x, \sigma) = f(x) + \sigma \operatorname{dist}(c(x), C).$$

The set $C$ encodes equalities and inequalities. For a monotonic norm and the orthant of
feasible coordinate residuals, the distance is the norm of the clipped residual. -/
noncomputable def nonsmoothExactPenalty
    (f : E → ℝ) (c : E → Z) (C : Set Z) (σ : ℝ) (x : E) : ℝ :=
  f x + σ * Metric.infDist (c x) C

/-- **Theorem 14.5.1** of [conn2000trust]. Let $K \subseteq Z$ be closed with $0 \in K$, let
$A : E \to Z$, $g : E \to \mathbb{R}$, $H : E \to E$ and $\ell : Z \to \mathbb{R}$ be bounded
linear maps, with $\ell(z) \le 0$ for all $z \in K$ and $g + \ell \circ A = 0$. Let
$\sigma > \|\ell\|$. Then the following are equivalent:

* $\langle d, H d \rangle > 0$ for every $d \neq 0$ with $A d \in K$ and $g(d) = 0$;
* $g(d) + \sigma \operatorname{dist}(A d, K) \ge 0$ for every $d$, and
  $\langle d, H d \rangle > 0$ for every $d \neq 0$ with
  $g(d) + \sigma \operatorname{dist}(A d, K) = 0$.

**Correction.** The source allows the weight at the threshold (14.5.2). There the equivalence
fails; see `ConnGouldToint.Chapter14.theorem_14_5_1_threshold_counterexample`. Here the weight
is strictly larger than $\|\ell\|$.

Here $H$ stands for the Hessian of the Lagrangian, $K$ for the tangent cone to the residual set
at $c(x)$, $g$ for $f'(x)$ and $A$ for $c'(x)$. -/
theorem theorem_14_5_1 {K : Set Z} (hK : IsClosed K) (h0 : (0 : Z) ∈ K)
    (A : E →L[ℝ] Z) (g : E →L[ℝ] ℝ) (H : E →L[ℝ] E) (ell : Z →L[ℝ] ℝ)
    {σ : ℝ} (hσ : ‖ell‖ < σ) (hnormal : ∀ z ∈ K, ell z ≤ 0)
    (hstat : g + ell.comp A = 0) :
    (∀ d ≠ (0 : E), A d ∈ K → g d = 0 → 0 < ⟪d, H d⟫) ↔
    (∀ d, 0 ≤ g d + σ * Metric.infDist (A d) K) ∧
      (∀ d ≠ (0 : E), g d + σ * Metric.infDist (A d) K = 0 → 0 < ⟪d, H d⟫) := by
  have hs := (Chapter15.sqp_penalty_support_iff h0 ell (norm_nonneg _)).mpr
    ⟨le_rfl, by simpa only [sub_zero] using hnormal⟩
  have hfirst (d : E) : 0 ≤ g d + σ * Metric.infDist (A d) K := by
    have h := hs (A d)
    rw [sub_zero] at h
    have hg := congrArg (fun T : E →L[ℝ] ℝ ↦ T d) hstat
    simp only [add_apply, ContinuousLinearMap.comp_apply, zero_apply] at hg
    have hmul := mul_le_mul_of_nonneg_right hσ.le (Metric.infDist_nonneg (x := A d) (s := K))
    linarith only [h, hg, hmul]
  have hiff := Chapter15.theorem_15_3_2_second_order hK h0 A g H ell hσ hnormal hstat
  exact ⟨fun h ↦ ⟨hfirst, hiff.mp h⟩, fun h ↦ hiff.mpr h.2⟩

/-- Counterexample to Theorem 14.5.1 of [conn2000trust] at the nonstrict threshold (14.5.2). For the
problem of minimizing $x - x^2$ subject to $x = 0$ on $\mathbb{R}$, the point $0$ with
multiplier $1$ satisfies the first-order conditions (14.2.3), and there is no nonzero critical
direction $d$ with $c'(0) d = 0$. But $0$ is not a local minimizer of the penalty function
$x - x^2 + |x|$ with weight $1$, which equals $-x^2 < 0$ for every $x < 0$. -/
theorem theorem_14_5_1_threshold_counterexample :
    IsEqualityKKT (fun x : ℝ ↦ x - x ^ 2) id 0 (1 : ℝ) ∧
      (∀ d : ℝ, d ≠ 0 → fderiv ℝ (id : ℝ → ℝ) 0 d = 0 → False) ∧
      ¬ IsLocalMin (nonsmoothExactPenalty (fun x : ℝ ↦ x - x ^ 2) id {0} 1) 0 := by
  have hf : HasDerivAt (fun x : ℝ ↦ x - x ^ 2) 1 0 := by
    convert (hasDerivAt_id (0 : ℝ)).sub ((hasDerivAt_id (0 : ℝ)).pow 2) using 1
    · rfl
    · norm_num [id]
  have hc := (hasDerivAt_id (0 : ℝ)).hasFDerivAt
  refine ⟨⟨rfl, ?_⟩, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro d
    rw [hf.hasFDerivAt.fderiv, hc.fderiv]
    simp
  · intro d hd hA
    rw [hc.fderiv] at hA
    exact hd (by simpa using hA)
  · intro h
    have he : ∀ᶠ t : ℝ in 𝓝[<] (0 : ℝ), (0 : ℝ) ≤ t - t ^ 2 + |t| := by
      have hh := h.filter_mono (nhdsWithin_le_nhds : 𝓝[<] (0 : ℝ) ≤ 𝓝 0)
      change ∀ᶠ t : ℝ in 𝓝[<] (0 : ℝ),
        nonsmoothExactPenalty (fun x : ℝ ↦ x - x ^ 2) id {0} 1 0 ≤
          nonsmoothExactPenalty (fun x : ℝ ↦ x - x ^ 2) id {0} 1 t at hh
      simpa [nonsmoothExactPenalty, Metric.infDist_singleton, Real.dist_eq, id] using hh
    have hneg : ∀ᶠ t : ℝ in 𝓝[<] (0 : ℝ), t < 0 := self_mem_nhdsWithin
    obtain ⟨t, ht, hle⟩ := (hneg.and he).exists
    rw [abs_of_neg (show t < 0 from ht)] at hle
    nlinarith only [hle, sq_pos_of_ne_zero (ne_of_lt ht)]

/-- Counterexample to the printed Theorem 14.5.2 of [conn2000trust] with a nonunique multiplier. For
the problem of minimizing $x^2$ subject to the redundant constraint $0 = 0$ on $\mathbb{R}$, the
point $0$ with multiplier $2$ satisfies the first-order conditions (14.2.3), and $1 < |2|$. But
$0$ is a local minimizer of the penalty function with weight $1$, which is $x^2$. -/
theorem theorem_14_5_2_redundant_constraint_counterexample :
    IsEqualityKKT (fun x : ℝ ↦ x ^ 2) (fun _ ↦ 0) 0 (2 : ℝ) ∧
      (1 : ℝ) < ‖(2 : ℝ)‖ ∧
      IsLocalMin (nonsmoothExactPenalty (fun x : ℝ ↦ x ^ 2) (fun _ ↦ (0 : ℝ)) {0} 1) 0 := by
  have hf : HasDerivAt (fun x : ℝ ↦ x ^ 2) 0 0 := by
    convert (hasDerivAt_id (0 : ℝ)).pow 2 using 1
    · rfl
    · norm_num [id]
  refine ⟨⟨rfl, ?_⟩, by norm_num, ?_⟩
  · apply ContinuousLinearMap.ext
    intro d
    rw [hf.hasFDerivAt.fderiv]
    simp
  · apply Eventually.of_forall
    intro x
    simpa [nonsmoothExactPenalty, Metric.infDist_singleton] using sq_nonneg x

omit [InnerProductSpace ℝ E] in
/-- **Theorem 14.5.2** of [conn2000trust]. Let $E$ and $Z$ be real normed spaces, let $c(x) \in C$,
let $f$ have the derivative $g$ and $c$ the derivative $A$ at $x$, with $A$ surjective, and let
$g + \ell \circ A = 0$ for a bounded linear functional $\ell$ on $Z$. If
$0 \le \sigma < \|\ell\|$, then $x$ is not a local minimizer of the penalty function
$f + \sigma \operatorname{dist}(c(\cdot), C)$.

**Correction.** The source does not assume that $A$ is surjective. With a redundant constraint,
the multiplier is not unique and can be arbitrarily large; see
`ConnGouldToint.Chapter14.theorem_14_5_2_redundant_constraint_counterexample`.

If $A$ is surjective, a direction $d$ with $\ell(A d)$ close to $\|\ell\| \|A d\|$ is a descent
direction of the penalty function. -/
theorem theorem_14_5_2 [NormedSpace ℝ E] {f : E → ℝ} {c : E → Z} {C : Set Z} {x : E}
    (hx : c x ∈ C) {g : E →L[ℝ] ℝ} {A : E →L[ℝ] Z}
    (hf : HasFDerivAt f g x) (hc : HasFDerivAt c A x) (hA : Function.Surjective A)
    (ell : Z →L[ℝ] ℝ) (hstat : g + ell.comp A = 0) {σ : ℝ} (hσ : 0 ≤ σ) (hsmall : σ < ‖ell‖) :
    ¬ IsLocalMin (nonsmoothExactPenalty f c C σ) x := by
  have hz : ∃ z : Z, σ * ‖z‖ < ell z := by
    by_contra! h
    have hs := (Chapter15.sqp_penalty_support_iff (Set.mem_singleton (0 : Z)) ell hσ).mp
      (by simpa only [sub_zero, Metric.infDist_singleton, dist_zero_right] using h)
    exact (not_le.mpr hsmall) hs.1
  obtain ⟨z, hz⟩ := hz
  obtain ⟨d, hd⟩ := hA z
  have hg : g d + σ * ‖A d‖ < 0 := by
    have he := congrArg (fun T : E →L[ℝ] ℝ ↦ T d) hstat
    simp only [add_apply, ContinuousLinearMap.comp_apply, zero_apply, hd] at he
    rw [hd]
    linarith only [hz, he]
  let ray := fun t : ℝ ↦ x + t • d
  have hray : HasDerivAt ray d 0 := by
    have h := (((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x)
    simpa [ray, id] using h
  have hfRay : HasDerivAt (f ∘ ray) (g d) 0 := by
    exact (show HasFDerivAt f g (ray 0) by simpa [ray] using hf).comp_hasDerivAt 0 hray
  have hcRay : HasDerivAt (c ∘ ray) (A d) 0 := by
    exact (show HasFDerivAt c A (ray 0) by simpa [ray] using hc).comp_hasDerivAt 0 hray
  have hl := hfRay.tendsto_slope_zero_right.add (hcRay.tendsto_slope_zero_right.norm.const_mul σ)
  intro hmin
  have hr := hray.continuousAt.tendsto
  have hminRay :=
    ((show Tendsto ray (𝓝 0) (𝓝 x) by simpa [ray] using hr).eventually hmin).filter_mono
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hupper : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      0 ≤ slope (f ∘ ray) 0 t + σ * ‖slope (c ∘ ray) 0 t‖ := by
    filter_upwards [self_mem_nhdsWithin, hminRay] with t ht hm
    have ht' : 0 < t := ht
    have hd := Metric.infDist_le_dist_of_mem (x := c (ray t)) hx
    rw [dist_eq_norm] at hd
    have hbound := mul_le_mul_of_nonneg_left hd hσ
    have hp : 0 ≤ f (ray t) - f x + σ * ‖c (ray t) - c x‖ := by
      change nonsmoothExactPenalty f c C σ x ≤ nonsmoothExactPenalty f c C σ (ray t) at hm
      unfold nonsmoothExactPenalty at hm
      rw [Metric.infDist_zero_of_mem hx, mul_zero, add_zero] at hm
      linarith only [hm, hbound]
    have hscaled := mul_nonneg (inv_nonneg.mpr ht'.le) hp
    simpa only [slope_def_module, sub_zero, Function.comp_apply, ray, zero_smul, add_zero,
      smul_eq_mul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht'.le), mul_add,
      mul_left_comm t⁻¹ σ] using hscaled
  refine (not_le.mpr hg) (le_of_tendsto_of_tendsto tendsto_const_nhds hl ?_)
  filter_upwards [hupper] with t ht
  simpa only [slope_def_module, sub_zero, zero_add] using ht

end ConnGouldToint.Chapter14
