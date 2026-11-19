/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Variational.EllipticInterval.MaximumPrinciple
import NumlibSurface.Brezis.Chapter08.Section04

/-!
# Brezis, Section 8.5: The maximum principle

This module formalizes Section 8.5 of [brezis2011functional]. Let $I = (0, 1)$ and
$\bar I = [0, 1]$, and let $f \in L^2(I)$. Theorem 8.19, the maximum principle, says that the
solution $u \in H^2(I)$ of the Dirichlet problem (32), $-u'' + u = f$ on $I$, $u(0) = \alpha$,
$u(1) = \beta$, satisfies (33):
$$\min\{\alpha, \beta, \inf_I f\} \le u(x) \le \max\{\alpha, \beta, \sup_I f\} \quad \text{for all }
  x \in \bar I.$$
The source proves it by Stampacchia's truncation method, and Remark 26 gives the classical proof for
$f \in C(\bar I)$. Corollary 8.20 derives, for a solution $u$ of the weak equation (34), positivity,
the bound $\|u\|_{L^\infty(I)} \le \|f\|_{L^\infty(I)}$ when $u = 0$ on $\partial I$, and the bound
$\|u\|_{L^\infty(I)} \le \|u\|_{L^\infty(\partial I)}$ when $f = 0$. Proposition 8.21 gives the
bounds (35), $\inf_I f \le u \le \sup_I f$, for the Neumann problem, with the classical proof in
Remark 27. Remark 28 gives the same bounds for the problem on $\mathbb{R}$ of Example 8.

The proofs specialize the backbone module `Numlib.Variational.EllipticInterval.MaximumPrinciple`.

## Main results

* Theorem 8.19, the upper bound, `Brezis.Chapter08.theorem_8_19_le`: $u \le K$ on $\bar I$ for every
  $K$ with $\alpha \le K$, $\beta \le K$ and $f \le K$ almost everywhere.
* Theorem 8.19, the lower bound, `Brezis.Chapter08.theorem_8_19_ge`: $K \le u$ on $\bar I$ for every
  $K$ with $K \le \alpha$, $K \le \beta$ and $K \le f$ almost everywhere.
* Theorem 8.19, `Brezis.Chapter08.theorem_8_19`: the maximum principle (33).
* Remark 26, `Brezis.Chapter08.remark_8_26`: the classical maximum principle for $v \in C^2([0, 1])$
  with $-v'' + v = f$.
* Corollary 8.20(i), `Brezis.Chapter08.corollary_8_20_i`: if $u \ge 0$ on $\partial I$ and
  $f \ge 0$, then $u \ge 0$ on $\bar I$.
* Corollary 8.20(ii), `Brezis.Chapter08.corollary_8_20_ii` and
  `Brezis.Chapter08.corollary_8_20_ii'`: if $u = 0$ on $\partial I$, then
  $|u| \le \|f\|_{L^\infty(I)}$ on $\bar I$.
* Corollary 8.20(iii), `Brezis.Chapter08.corollary_8_20_iii`: if $f = 0$, then
  $|u(x)| \le \max\{|u(0)|, |u(1)|\}$ on $\bar I$.
* Corollary 8.20, `Brezis.Chapter08.corollary_8_20`: the three parts together.
* Proposition 8.21, `Brezis.Chapter08.proposition_8_21_le`, `Brezis.Chapter08.proposition_8_21_ge`
  and `Brezis.Chapter08.proposition_8_21`: the bounds (35) for the Neumann problem.
* Remark 27, `Brezis.Chapter08.remark_8_27`: the classical maximum principle for the Neumann
  problem.
* Remark 28, `Brezis.Chapter08.remark_8_28`: the bounds $\inf_{\mathbb{R}} f \le u \le
  \sup_{\mathbb{R}} f$ for the problem on $\mathbb{R}$.

## Conventions

* "$u \in H^2(I)$ is the solution of (32)" is `Φ : SobolevInterval 2 0 1` with $\Phi'' = \Phi - f$
  almost everywhere and $\Phi(0) = \alpha$, $\Phi(1) = \beta$, the object of Proposition 8.16. The
  backbone uses the weak equation (34) on $H_0^1$, which follows by Green's formula
  (`EllipticInterval.modelForm_inclusionCLM_eq_load_of_mem`).
* The value $u(x)$ for $x \in [0, 1]$ is the value of the continuous representative,
  `SobolevInterval.rep u x`.

## Deviations from the source

* **Theorem 8.19, Proposition 8.21 and Remark 28** (reading). The source's $\sup_I f$ and $\inf_I f$
  are the essential supremum and infimum (footnote 16), which can be infinite. The bounds (33) and
  (35) are stated for every essential bound of $f$: "$f \le K$ a.e." gives
  $u \le \max\{\alpha, \beta, K\}$. This is the statement of the source with $K = \sup_I f$ when
  $\sup_I f < \infty$, and the statement of the source is vacuous otherwise. See
  `Brezis.Chapter08.theorem_8_19`, `Brezis.Chapter08.proposition_8_21` and
  `Brezis.Chapter08.remark_8_28`.
* **Theorem 8.19 and Corollary 8.20** (reading). The estimates apply to the continuous
  representative on the closed interval, and the norm estimates are stated pointwise.
  The alternative to (ii) uses any essential bound of $|f|$. See
  `Brezis.Chapter08.theorem_8_19` and `Brezis.Chapter08.corollary_8_20_ii'`.
* **Remarks 26 and 27** (reading and typo). The classical statements give the upper-bound
  argument for a $C^2$ solution satisfying the closed-interval equation. In Remark 26 the identity
  at a maximum follows from (32), cited in the source as (33). See
  `Brezis.Chapter08.remark_8_26` and `Brezis.Chapter08.remark_8_27`.
-/

open Filter MeasureTheory Set TopologicalSpace EllipticInterval
open scoped ENNReal Topology

noncomputable section

namespace Brezis.Chapter08

/-- The constant coefficient $1$, as an element of $L^\infty(0, 1)$, is at least $1$ almost
everywhere. -/
private theorem one_le_constLinf_ae' :
    ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), 1 ≤ constLinf 0 1 1 x :=
  (coeFn_constLinf 0 1 1).mono fun x hx ↦ by rw [hx]

/-! ### Theorem 8.19 -/

/-- **Theorem 8.19** of [brezis2011functional], the upper bound. Let $I = (0, 1)$, $f \in L^2(I)$
and $\alpha, \beta \in \mathbb{R}$, and let $u \in H^2(I)$ be the solution of the Dirichlet
problem (32):
$$-u'' + u = f \text{ a.e. on } I, \qquad u(0) = \alpha, \quad u(1) = \beta.$$
Let $K \in \mathbb{R}$ with $\alpha \le K$, $\beta \le K$ and $f \le K$ almost everywhere on
$I$. Then $u(x) \le K$ for every $x \in [0, 1]$.

When $\sup_I f < \infty$, the choice $K = \max\{\alpha, \beta, \sup_I f\}$ gives the upper bound
of (33). The proof is Stampacchia's truncation method,
`EllipticInterval.rep_le_of_le_of_isWeakSolution` with both coefficients equal to $1$, applied
to the weak equation (34) on $H_0^1$ that follows from Green's formula.

**Reading.** The library states a bound on the closed interval. The endpoint inequalities
 are among the hypotheses. -/
theorem theorem_8_19_le (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) {α β : ℝ}
    {Φ : SobolevInterval 2 0 1}
    (hΦ : (SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x ↦ SobolevInterval.fn Φ x - f x)
    (h0 : SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) 0 = α)
    (h1 : SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) 1 = β) {K : ℝ}
    (hα : α ≤ K) (hβ : β ≤ K) (hf : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), f x ≤ K) :
    ∀ x ∈ Icc (0 : ℝ) 1, SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) x ≤ K :=
  rep_le_of_le_of_isWeakSolution (zero_lt_one' ℝ) (constLinf 0 1 1) (constLinf 0 1 1) one_pos
    one_le_constLinf_ae' (one_le_constLinf_ae'.mono fun _ hx ↦ zero_le_one.trans hx) f
    (fun v hv ↦ modelForm_inclusionCLM_eq_load_of_mem (zero_lt_one' ℝ) f hΦ hv)
    (h0 ▸ hα) (h1 ▸ hβ) (by
      filter_upwards [hf, coeFn_constLinf 0 1 1] with x hx hx1
      rw [hx1, mul_one]; exact hx)

/-- **Theorem 8.19** of [brezis2011functional], the lower bound. Let $I = (0, 1)$, $f \in L^2(I)$
and $\alpha, \beta \in \mathbb{R}$, and let $u \in H^2(I)$ be the solution of (32). Let
$K \in \mathbb{R}$ with $K \le \alpha$, $K \le \beta$ and $K \le f$ almost everywhere on $I$.
Then $K \le u(x)$ for every $x \in [0, 1]$.

When $\inf_I f > -\infty$, the choice $K = \min\{\alpha, \beta, \inf_I f\}$ gives the lower
bound of (33). The proof applies the upper bound to $-u$.

**Reading.** The library states a bound on the closed interval. The endpoint inequalities
 are among the hypotheses. -/
theorem theorem_8_19_ge (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) {α β : ℝ}
    {Φ : SobolevInterval 2 0 1}
    (hΦ : (SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x ↦ SobolevInterval.fn Φ x - f x)
    (h0 : SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) 0 = α)
    (h1 : SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) 1 = β) {K : ℝ}
    (hα : K ≤ α) (hβ : K ≤ β) (hf : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), K ≤ f x) :
    ∀ x ∈ Icc (0 : ℝ) 1, K ≤ SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) x :=
  rep_ge_of_ge_of_isWeakSolution (zero_lt_one' ℝ) (constLinf 0 1 1) (constLinf 0 1 1) one_pos
    one_le_constLinf_ae' (one_le_constLinf_ae'.mono fun _ hx ↦ zero_le_one.trans hx) f
    (fun v hv ↦ modelForm_inclusionCLM_eq_load_of_mem (zero_lt_one' ℝ) f hΦ hv)
    (h0 ▸ hα) (h1 ▸ hβ) (by
      filter_upwards [hf, coeFn_constLinf 0 1 1] with x hx hx1
      rw [hx1, mul_one]; exact hx)

/-- **Theorem 8.19** of [brezis2011functional] (the maximum principle). Let $I = (0, 1)$,
$f \in L^2(I)$ and $\alpha, \beta \in \mathbb{R}$, and let $u \in H^2(I)$ be the solution of the
Dirichlet problem (32), $-u'' + u = f$ on $I$, $u(0) = \alpha$, $u(1) = \beta$. Then (33) holds
in the following form, for every $x \in [0, 1]$:
* $u(x) \le \max\{\alpha, \beta, M\}$ for every $M$ with $f \le M$ almost everywhere on $I$;
* $\min\{\alpha, \beta, m\} \le u(x)$ for every $m$ with $m \le f$ almost everywhere on $I$.

**Reading.** The source states (33) as $\min\{\alpha, \beta, \inf_I f\} \le u(x) \le
\max\{\alpha, \beta, \sup_I f\}$, with the essential infimum and supremum of $f$ (footnote 16),
which can be infinite. The statement here quantifies over the essential bounds $M$ and $m$ of
$f$; it is the statement of the source with $M = \sup_I f$ and $m = \inf_I f$ when these are
finite. -/
theorem theorem_8_19 (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) {α β : ℝ}
    {Φ : SobolevInterval 2 0 1}
    (hΦ : (SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x ↦ SobolevInterval.fn Φ x - f x)
    (h0 : SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) 0 = α)
    (h1 : SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) 1 = β) :
    (∀ M : ℝ, (∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), f x ≤ M) → ∀ x ∈ Icc (0 : ℝ) 1,
      SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) x ≤ max (max α β) M) ∧
    ∀ m : ℝ, (∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), m ≤ f x) → ∀ x ∈ Icc (0 : ℝ) 1,
      min (min α β) m ≤ SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) x :=
  ⟨fun M hM ↦ theorem_8_19_le f hΦ h0 h1 ((le_max_left α β).trans (le_max_left _ M))
    ((le_max_right α β).trans (le_max_left _ M)) (hM.mono fun _ hx ↦ hx.trans (le_max_right _ M)),
    fun m hm ↦ theorem_8_19_ge f hΦ h0 h1 ((min_le_left _ m).trans (min_le_left α β))
      ((min_le_left _ m).trans (min_le_right α β)) (hm.mono fun _ hx ↦ (min_le_right _ m).trans hx)⟩

/-- **Remark 26** in Chapter 8 of [brezis2011functional]. Let $v \in C^2([0, 1])$,
$f : \mathbb{R} \to \mathbb{R}$ and $K \in \mathbb{R}$, with
$$-v'' + v = f \text{ on } [0, 1], \qquad v(0) \le K, \quad v(1) \le K, \quad f \le K \text{ on
  } [0, 1].$$
Then $v \le K$ on $[0, 1]$.

The source remarks that when $f \in C(\bar I)$ the solution $u$ of (32) lies in $C^2(\bar I)$,
and (33) follows from the classical approach to the maximum principle. Let $x_0 \in [0, 1]$ be a
point where $u$ attains its maximum. If $x_0 = 0$ or $x_0 = 1$ the conclusion is obvious.
Otherwise $u'(x_0) = 0$ and $u''(x_0) \le 0$, so $u(x_0) = f(x_0) + u''(x_0) \le f(x_0) \le K$.
The proof specializes `EllipticInterval.le_of_contDiffMapIcc_classical`, which uses the
second-derivative test `IsLocalMax.deriv_deriv_nonpos`.

**Reading.** The upper-bound argument starts with an arbitrary $C^2$ classical solution whose
 equation is assumed on the closed interval. The source starts with the solution for continuous
 $f$ and appeals to its classical regularity.

**Typo.** The displayed identity at the maximum follows from (32). The source cites (33). -/
theorem remark_8_26 (v : ContDiffMapIcc (zero_lt_one' ℝ).le 2) {f : ℝ → ℝ}
    (hode : ∀ x : Icc (0 : ℝ) 1, -v.deriv 2 x + v x = f x) {K : ℝ}
    (hK0 : v ⟨0, left_mem_Icc.2 zero_le_one⟩ ≤ K) (hK1 : v ⟨1, right_mem_Icc.2 zero_le_one⟩ ≤ K)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, f x ≤ K) : ∀ x : Icc (0 : ℝ) 1, v x ≤ K :=
  le_of_contDiffMapIcc_classical (zero_lt_one' ℝ) v hode hK0 hK1 hf

/-! ### Corollary 8.20 -/

/-- **Corollary 8.20(i)** of [brezis2011functional]. Let $I = (0, 1)$ and $f \in L^2(I)$, and let
$u \in H^1(I)$ be a solution of (34):
$$\int_I u'v' + \int_I uv = \int_I fv \quad \text{for all } v \in H_0^1(I),$$
with any boundary values. If $u(0) \ge 0$, $u(1) \ge 0$ and $f \ge 0$ almost everywhere on $I$,
then $u \ge 0$ on $[0, 1]$.

The proof specializes `EllipticInterval.rep_nonneg_of_isWeakSolution`. -/
theorem corollary_8_20_i (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) {u : SobolevInterval 1 0 1}
    (hu : ∀ v ∈ SobolevIntervalZero 0 1, modelForm 0 1 u v = load 0 1 f v)
    (h0 : 0 ≤ SobolevInterval.rep u 0) (h1 : 0 ≤ SobolevInterval.rep u 1)
    (hf : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), 0 ≤ f x) :
    ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ SobolevInterval.rep u x :=
  rep_nonneg_of_isWeakSolution (zero_lt_one' ℝ) f hu h0 h1 hf

/-- **Corollary 8.20(ii)** of [brezis2011functional]. Let $I = (0, 1)$ and $f \in L^2(I)$, and let
$u \in H^1(I)$ be a solution of (34). If $u(0) = u(1) = 0$ and $f \in L^\infty(I)$, then
$\|u\|_{L^\infty(I)} \le \|f\|_{L^\infty(I)}$:
$$|u(x)| \le \|f\|_{L^\infty(I)} \quad \text{for every } x \in [0, 1].$$

The proof specializes `EllipticInterval.abs_rep_le_of_isWeakSolution` with the essential bound
$M = \|f\|_{L^\infty(I)}$. -/
theorem corollary_8_20_ii (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) {u : SobolevInterval 1 0 1}
    (hu : ∀ v ∈ SobolevIntervalZero 0 1, modelForm 0 1 u v = load 0 1 f v)
    (h0 : SobolevInterval.rep u 0 = 0) (h1 : SobolevInterval.rep u 1 = 0)
    (hf : MemLp f ∞ (volume.restrict (Ioo (0 : ℝ) 1))) :
    ∀ x ∈ Icc (0 : ℝ) 1,
      |SobolevInterval.rep u x| ≤ (eLpNorm f ∞ (volume.restrict (Ioo (0 : ℝ) 1))).toReal := by
  refine abs_rep_le_of_isWeakSolution (zero_lt_one' ℝ) f hu h0 h1 ?_
  have hne : eLpNorm f ∞ (volume.restrict (Ioo (0 : ℝ) 1)) ≠ ⊤ := hf.eLpNorm_ne_top
  filter_upwards [ae_le_eLpNormEssSup (f := ⇑f) (μ := volume.restrict (Ioo (0 : ℝ) 1))] with x hx
  rw [Real.enorm_eq_ofReal_abs] at hx
  rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable f)]
  rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable f)] at hne
  have := ENNReal.toReal_mono hne hx
  rwa [ENNReal.toReal_ofReal (abs_nonneg _)] at this

/-- **Corollary 8.20(ii)** of [brezis2011functional], with an explicit essential bound. Let
$I = (0, 1)$ and $f \in L^2(I)$, let $u \in H^1(I)$ be a solution of (34) with
$u(0) = u(1) = 0$, and let $M \in \mathbb{R}$ with $|f| \le M$ almost everywhere on $I$. Then
$|u(x)| \le M$ for every $x \in [0, 1]$.

**Reading.** The source states the estimate using the essential supremum norm. This version
 uses an arbitrary almost-everywhere bound of $|f|$. -/
theorem corollary_8_20_ii' (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    {u : SobolevInterval 1 0 1}
    (hu : ∀ v ∈ SobolevIntervalZero 0 1, modelForm 0 1 u v = load 0 1 f v)
    (h0 : SobolevInterval.rep u 0 = 0) (h1 : SobolevInterval.rep u 1 = 0) {M : ℝ}
    (hf : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), |f x| ≤ M) :
    ∀ x ∈ Icc (0 : ℝ) 1, |SobolevInterval.rep u x| ≤ M :=
  abs_rep_le_of_isWeakSolution (zero_lt_one' ℝ) f hu h0 h1 hf

/-- **Corollary 8.20(iii)** of [brezis2011functional]. Let $I = (0, 1)$, and let $u \in H^1(I)$ be a
solution of (34) with $f = 0$. Then $\|u\|_{L^\infty(I)} \le \|u\|_{L^\infty(\partial I)}$:
$$|u(x)| \le \max\{|u(0)|, |u(1)|\} \quad \text{for every } x \in [0, 1].$$

The proof specializes `EllipticInterval.abs_rep_le_max_of_isWeakSolution`. -/
theorem corollary_8_20_iii {u : SobolevInterval 1 0 1}
    (hu : ∀ v ∈ SobolevIntervalZero 0 1, modelForm 0 1 u v = load 0 1 0 v) :
    ∀ x ∈ Icc (0 : ℝ) 1,
      |SobolevInterval.rep u x| ≤ max |SobolevInterval.rep u 0| |SobolevInterval.rep u 1| :=
  abs_rep_le_max_of_isWeakSolution (zero_lt_one' ℝ) hu

/-- **Corollary 8.20** of [brezis2011functional]. Let $I = (0, 1)$ and $f \in L^2(I)$, and let
$u \in H^1(I)$ be a solution of (34), $\int_I u'v' + \int_I uv = \int_I fv$ for all
$v \in H_0^1(I)$. Then:
* (i) if $u(0) \ge 0$, $u(1) \ge 0$ and $f \ge 0$ almost everywhere on $I$, then $u \ge 0$ on
  $[0, 1]$;
* (ii) if $u(0) = u(1) = 0$ and $f \in L^\infty(I)$, then $|u(x)| \le \|f\|_{L^\infty(I)}$ for
  every $x \in [0, 1]$;
* (iii) if $f = 0$, then $|u(x)| \le \max\{|u(0)|, |u(1)|\}$ for every $x \in [0, 1]$. -/
theorem corollary_8_20 (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) {u : SobolevInterval 1 0 1}
    (hu : ∀ v ∈ SobolevIntervalZero 0 1, modelForm 0 1 u v = load 0 1 f v) :
    (0 ≤ SobolevInterval.rep u 0 → 0 ≤ SobolevInterval.rep u 1 →
      (∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), 0 ≤ f x) →
      ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ SobolevInterval.rep u x) ∧
    (SobolevInterval.rep u 0 = 0 → SobolevInterval.rep u 1 = 0 →
      MemLp f ∞ (volume.restrict (Ioo (0 : ℝ) 1)) → ∀ x ∈ Icc (0 : ℝ) 1,
        |SobolevInterval.rep u x| ≤ (eLpNorm f ∞ (volume.restrict (Ioo (0 : ℝ) 1))).toReal) ∧
    (f = 0 → ∀ x ∈ Icc (0 : ℝ) 1,
      |SobolevInterval.rep u x| ≤ max |SobolevInterval.rep u 0| |SobolevInterval.rep u 1|) :=
  ⟨fun h0 h1 hf ↦ corollary_8_20_i f hu h0 h1 hf, fun h0 h1 hf ↦ corollary_8_20_ii f hu h0 h1 hf,
    fun hf ↦ corollary_8_20_iii (hf ▸ hu)⟩

/-! ### Proposition 8.21: the Neumann problem -/

/-- **Proposition 8.21** of [brezis2011functional], the upper bound. Let $I = (0, 1)$ and
$f \in L^2(I)$, and let $u \in H^2(I)$ be the solution of the Neumann problem of Proposition
8.17,
$$-u'' + u = f \text{ a.e. on } I, \qquad u'(0) = u'(1) = 0.$$
Let $K \in \mathbb{R}$ with $f \le K$ almost everywhere on $I$. Then $u(x) \le K$ for every
$x \in [0, 1]$.

When $\sup_I f$ is finite, $K = \sup_I f$ is allowed. The proof puts the truncation $G(u - K)$
into the weak formulation (36) on $H^1(I)$; it specializes
`EllipticInterval.rep_le_of_le_of_isWeakSolution_neumann`.

**Reading.** States the estimate for every finite real essential upper bound.
-/
theorem proposition_8_21_le (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    {Φ : SobolevInterval 2 0 1}
    (hΦ : (SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x ↦ SobolevInterval.fn Φ x - f x)
    (h0 : SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 0 = 0)
    (h1 : SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 1 = 0) {K : ℝ}
    (hf : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), f x ≤ K) :
    ∀ x ∈ Icc (0 : ℝ) 1, SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) x ≤ K :=
  rep_le_of_le_of_isWeakSolution_neumann (zero_lt_one' ℝ) f
    (proposition_8_17_min f hΦ h0 h1).1 hf

/-- **Proposition 8.21** of [brezis2011functional], the lower bound. Let $I = (0, 1)$ and
$f \in L^2(I)$, and let $u \in H^2(I)$ be the solution of the Neumann problem $-u'' + u = f$
a.e. on $I$, $u'(0) = u'(1) = 0$. Let $K \in \mathbb{R}$ with $K \le f$ almost everywhere on
$I$. Then $K \le u(x)$ for every $x \in [0, 1]$.

**Reading.** States the estimate for every finite real essential lower bound.
-/
theorem proposition_8_21_ge (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    {Φ : SobolevInterval 2 0 1}
    (hΦ : (SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x ↦ SobolevInterval.fn Φ x - f x)
    (h0 : SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 0 = 0)
    (h1 : SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 1 = 0) {K : ℝ}
    (hf : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), K ≤ f x) :
    ∀ x ∈ Icc (0 : ℝ) 1, K ≤ SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) x :=
  rep_ge_of_ge_of_isWeakSolution_neumann (zero_lt_one' ℝ) f
    (proposition_8_17_min f hΦ h0 h1).1 hf

/-- **Proposition 8.21** of [brezis2011functional]. Let $I = (0, 1)$ and $f \in L^2(I)$, and let
$u \in H^2(I)$ be the solution of the Neumann problem $-u'' + u = f$ on $I$,
$u'(0) = u'(1) = 0$. Then (35) holds in the following form, for every $x \in [0, 1]$:
* $u(x) \le M$ for every $M$ with $f \le M$ almost everywhere on $I$;
* $m \le u(x)$ for every $m$ with $m \le f$ almost everywhere on $I$.

**Reading.** The source states (35) as $\inf_I f \le u(x) \le \sup_I f$, with the essential
infimum and supremum of $f$, which can be infinite. The statement here quantifies over the
essential bounds of $f$; it is the statement of the source when these bounds are finite. -/
theorem proposition_8_21 (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    {Φ : SobolevInterval 2 0 1}
    (hΦ : (SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x ↦ SobolevInterval.fn Φ x - f x)
    (h0 : SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 0 = 0)
    (h1 : SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 1 = 0) :
    (∀ M : ℝ, (∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), f x ≤ M) → ∀ x ∈ Icc (0 : ℝ) 1,
      SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) x ≤ M) ∧
    ∀ m : ℝ, (∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), m ≤ f x) → ∀ x ∈ Icc (0 : ℝ) 1,
      m ≤ SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) x :=
  ⟨fun _ hM ↦ proposition_8_21_le f hΦ h0 h1 hM, fun _ hm ↦ proposition_8_21_ge f hΦ h0 h1 hm⟩

/-- **Remark 27** in Chapter 8 of [brezis2011functional]. Let $v \in C^2([0, 1])$,
$f : \mathbb{R} \to \mathbb{R}$ and $K \in \mathbb{R}$, with
$$-v'' + v = f \text{ on } [0, 1], \qquad v'(0) = v'(1) = 0, \qquad f \le K \text{ on } [0,
  1].$$
Then $v \le K$ on $[0, 1]$.

The source remarks that when $f \in C(\bar I)$ the solution of the Neumann problem lies in
$C^2(\bar I)$, and (35) follows along the lines of Remark 26. If $u$ attains its maximum on
$\partial I$, say at $0$, then $u''(0) \le 0$: extend $u$ by reflection to the left of $0$ and
use $u'(0) = 0$. The proof specializes
`EllipticInterval.le_of_contDiffMapIcc_classical_neumann`, which uses the one-sided
second-derivative test at the endpoints.

**Reading.** The statement isolates the upper-bound argument for arbitrary $C^2$ classical
 solutions of the closed-interval equation. The lower bound follows by applying it to $-v$. -/
theorem remark_8_27 (v : ContDiffMapIcc (zero_lt_one' ℝ).le 2) {f : ℝ → ℝ}
    (hode : ∀ x : Icc (0 : ℝ) 1, -v.deriv 2 x + v x = f x)
    (hv0 : v.deriv 1 ⟨0, left_mem_Icc.2 zero_le_one⟩ = 0)
    (hv1 : v.deriv 1 ⟨1, right_mem_Icc.2 zero_le_one⟩ = 0) {K : ℝ}
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, f x ≤ K) : ∀ x : Icc (0 : ℝ) 1, v x ≤ K :=
  le_of_contDiffMapIcc_classical_neumann (zero_lt_one' ℝ) v hode hv0 hv1 hf

/-! ### Remark 28: the problem on $\mathbb{R}$ -/

/-- **Remark 28** in Chapter 8 of [brezis2011functional]. Let $f \in L^2(\mathbb{R})$, and let
$u \in H^2(\mathbb{R})$ be the solution of $-u'' + u = f$ on $\mathbb{R}$, $u(x) \to 0$ as
$|x| \to \infty$, of Example 8. Then $\inf_{\mathbb{R}} f \le u(x) \le \sup_{\mathbb{R}} f$ for
all $x \in \mathbb{R}$, in the following form:
* $u(x) \le K$ for every $K \ge 0$ with $f \le K$ almost everywhere;
* $k \le u(x)$ for every $k \le 0$ with $k \le f$ almost everywhere.

**Reading.** As in Theorem 8.19, the essential supremum and infimum of $f$ are replaced by
essential bounds of $f$.

The sign conditions $K \ge 0$ and $k \le 0$ are no restriction, because a function of
$L^2(\mathbb{R})$ satisfies $\operatorname{ess\,sup} f \ge 0 \ge \operatorname{ess\,inf} f$.
They are needed in the proof, because the truncation $G(u - K)$ lies in $H^1(\mathbb{R})$ only
for $K \ge 0$; the sketch of the source does not remark on this. The solution $u$ is
`EllipticInterval.Line.solution f`. The proof specializes `EllipticInterval.Line.rep_le_of_le`
and `EllipticInterval.Line.le_rep_of_le`. -/
theorem remark_8_28 (f : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) :
    (∀ K : ℝ, 0 ≤ K → (∀ᵐ x ∂(volume.restrict ((⊤ : Opens ℝ) : Set ℝ)), f x ≤ K) →
      ∀ x, (Line.solution f).rep x ≤ K) ∧
    ∀ k : ℝ, k ≤ 0 → (∀ᵐ x ∂(volume.restrict ((⊤ : Opens ℝ) : Set ℝ)), k ≤ f x) →
      ∀ x, k ≤ (Line.solution f).rep x :=
  ⟨fun _ hK hf ↦ Line.rep_le_of_le f hK hf, fun _ hk hf ↦ Line.le_rep_of_le f hk hf⟩

end Brezis.Chapter08
