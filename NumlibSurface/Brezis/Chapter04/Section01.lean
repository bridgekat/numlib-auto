/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Egorov
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Brezis, Section 4.1: Some results about integration that everyone must know

This module formalizes Section 4.1 of [brezis2011functional] for real-valued functions on a measure
space $(\Omega, \mathcal{M}, \mu)$. It states the monotone convergence theorem of Beppo Levi
(Theorem 4.1), the dominated convergence theorem of Lebesgue (Theorem 4.2), Fatou's lemma (Lemma
4.1), the density of $C_c(\mathbb{R}^N)$ in $L^1(\mathbb{R}^N)$ (Theorem 4.3), and the theorems of
Tonelli and Fubini on a product of σ-finite measure spaces (Theorems 4.4 and 4.5). It also states
Egorov's theorem (Theorem 4.29), from the Comments on Chapter 4. All these results are in Mathlib;
this module restates them in the form of the source.

## Main results

* Theorem 4.1 (monotone convergence), `Brezis.Chapter04.theorem_4_1`: an a.e. increasing sequence of
  integrable functions with bounded integrals converges a.e. and in $L^1$ to an integrable function.
* Theorem 4.2 (dominated convergence), `Brezis.Chapter04.theorem_4_2`: an a.e. convergent sequence
  dominated by an integrable function converges in $L^1$.
* Lemma 4.1 (Fatou), `Brezis.Chapter04.lemma_4_1`: for nonnegative integrable functions with bounded
  integrals, $\liminf f_n$ is integrable and $\int \liminf f_n \le \liminf \int f_n$.
* Theorem 4.3, `Brezis.Chapter04.theorem_4_3`: $C_c(\mathbb{R}^N)$ is dense in $L^1(\mathbb{R}^N)$.
* Theorem 4.4 (Tonelli), `Brezis.Chapter04.theorem_4_4`: a measurable function on
  $\Omega_1 \times \Omega_2$ whose iterated integral of $|F|$ is finite is integrable.
* Theorem 4.5 (Fubini), `Brezis.Chapter04.theorem_4_5`: for an integrable function on
  $\Omega_1 \times \Omega_2$, both iterated integrals exist and equal the integral on the product.
* Theorem 4.29 (Egorov), `Brezis.Chapter04.theorem_4_29`: on a finite measure space, a.e.
  convergence is uniform outside a set of arbitrarily small measure.

## Conventions

* The measure space $(\Omega, \mathcal{M}, \mu)$ is a type `α` with a `MeasurableSpace` and a
  measure `μ`.
* The space $C_c(\mathbb{R}^N)$ of continuous functions with compact support is the condition
  `Continuous g ∧ HasCompactSupport g` on `EuclideanSpace ℝ (Fin N)`, with Lebesgue measure
  `volume`.
* The $L^1$ distance $\|f - g\|_1$ is written as the integral $\int |f - g|$.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

namespace Brezis.Chapter04

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-! ### Theorem 4.2: the dominated convergence theorem -/

/-- **Theorem 4.2** of [brezis2011functional] (dominated convergence theorem, Lebesgue). Let $(f_n)$
be a sequence of integrable functions on $\Omega$ such that $f_n(x) \to f(x)$ for a.e.
$x \in \Omega$. Suppose that there is an integrable function $g$ with $|f_n(x)| \le g(x)$ for
a.e. $x$ and every $n$. Then $f$ is integrable and
$$\|f_n - f\|_1 = \int_\Omega |f_n - f| \, d\mu \to 0.$$

In the Lean statement the limit is `g` and the dominating function is `bound`. -/
theorem theorem_4_2 {f : ℕ → α → ℝ} {g : α → ℝ} (hf : ∀ n, Integrable (f n) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) {bound : α → ℝ}
    (hbound : Integrable bound μ) (hfb : ∀ n, ∀ᵐ x ∂μ, |f n x| ≤ bound x) :
    Integrable g μ ∧ Tendsto (fun n => ∫ x, |f n x - g x| ∂μ) atTop (𝓝 0) := by
  have hg_meas : AEStronglyMeasurable g μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hf n).aestronglyMeasurable) hlim
  have hgb : ∀ᵐ x ∂μ, |g x| ≤ bound x := by
    filter_upwards [hlim, ae_all_iff.2 hfb] with x hx hxb
    exact le_of_tendsto hx.abs (Eventually.of_forall hxb)
  have hg : Integrable g μ :=
    ⟨hg_meas, hasFiniteIntegral_of_dominated_convergence hbound.2 hfb hlim⟩
  refine ⟨hg, ?_⟩
  have := tendsto_integral_of_dominated_convergence (fun x => 2 * bound x)
    (fun n => ((hf n).sub hg).norm.aestronglyMeasurable) (hbound.const_mul 2)
    (fun n => ?_) (f := fun _ => (0 : ℝ)) ?_
  · simpa using this
  · filter_upwards [hfb n, hgb] with x hx hgx
    simp only [Real.norm_eq_abs, abs_abs, Pi.sub_apply]
    calc |f n x - g x| ≤ |f n x| + |g x| := abs_sub _ _
      _ ≤ 2 * bound x := by linarith
  · filter_upwards [hlim] with x hx
    simpa using (hx.sub_const (g x)).abs

/-! ### Theorem 4.1: the monotone convergence theorem -/

/-- **Theorem 4.1** of [brezis2011functional] (monotone convergence theorem, Beppo Levi). Let
$(f_n)$ be a sequence of integrable functions on $\Omega$ that is increasing for a.e. $x$, with
$\sup_n \int f_n < \infty$. Then there is an integrable function $f$ such that $f_n(x) \to f(x)$
for a.e. $x \in \Omega$, and
$$\|f_n - f\|_1 = \int_\Omega |f_n - f| \, d\mu \to 0.$$

In the Lean statement the limit is `g`. -/
theorem theorem_4_1 {f : ℕ → α → ℝ} (hf : ∀ n, Integrable (f n) μ)
    (hmono : ∀ᵐ x ∂μ, Monotone fun n => f n x)
    (hbdd : BddAbove (Set.range fun n => ∫ x, f n x ∂μ)) :
    ∃ g : α → ℝ, Integrable g μ ∧ (∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) ∧
      Tendsto (fun n => ∫ x, |f n x - g x| ∂μ) atTop (𝓝 0) := by
  obtain ⟨B, hB⟩ := hbdd
  -- the increments `F n = f n - f 0 ≥ 0` and their supremum `S`
  set F : ℕ → α → ℝ := fun n x => f n x - f 0 x with hF_def
  have hF_int : ∀ n, Integrable (F n) μ := fun n => (hf n).sub (hf 0)
  have hF_nn : ∀ n, ∀ᵐ x ∂μ, 0 ≤ F n x := fun n =>
    hmono.mono fun x hx => sub_nonneg.2 (hx (Nat.zero_le n))
  have hF_mono : ∀ᵐ x ∂μ, Monotone fun n => ENNReal.ofReal (F n x) :=
    hmono.mono fun x hx m n hmn => ENNReal.ofReal_le_ofReal (sub_le_sub_right (hx hmn) _)
  have hF_meas : ∀ n, AEMeasurable (fun x => ENNReal.ofReal (F n x)) μ := fun n =>
    ENNReal.measurable_ofReal.comp_aemeasurable (hF_int n).aemeasurable
  set L : α → ℝ≥0∞ := fun x => ⨆ n, ENNReal.ofReal (F n x) with hL_def
  have hL_meas : AEMeasurable L μ := AEMeasurable.iSup hF_meas
  have hL_int : ∫⁻ x, L x ∂μ ≠ ∞ := by
    rw [hL_def, lintegral_iSup' hF_meas hF_mono]
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := B - ∫ x, f 0 x ∂μ))
      (iSup_le fun n => ?_)
    rw [← ofReal_integral_eq_lintegral_ofReal (hF_int n) (hF_nn n)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hF_def]
    simp only [integral_sub (hf n) (hf 0)]
    linarith [hB ⟨n, rfl⟩]
  have hL_fin : ∀ᵐ x ∂μ, L x < ∞ := ae_lt_top' hL_meas hL_int
  set S : α → ℝ := fun x => (L x).toReal with hS_def
  have hS_int : Integrable S μ := integrable_toReal_of_lintegral_ne_top hL_meas hL_int
  have hS_nn : ∀ x, 0 ≤ S x := fun x => ENNReal.toReal_nonneg
  -- `F n → S` a.e., hence `f n → f 0 + S`
  have hFS : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (S x)) := by
    filter_upwards [hL_fin, hF_mono, ae_all_iff.2 hF_nn] with x hx hmx hnn
    have h1 : Tendsto (fun n => ENNReal.ofReal (F n x)) atTop (𝓝 (L x)) := tendsto_atTop_iSup hmx
    have h2 := (ENNReal.tendsto_toReal hx.ne).comp h1
    refine h2.congr fun n => ?_
    simp only [Function.comp_apply, ENNReal.toReal_ofReal (hnn n)]
  have hFS_le : ∀ n, ∀ᵐ x ∂μ, F n x ≤ S x := fun n => by
    filter_upwards [hL_fin, hF_nn n] with x hx hnn
    rw [hS_def, ← ENNReal.toReal_ofReal hnn]
    exact ENNReal.toReal_mono hx.ne (le_iSup (fun n => ENNReal.ofReal (F n x)) n)
  refine ⟨fun x => f 0 x + S x, (hf 0).add hS_int, ?_, ?_⟩
  · filter_upwards [hFS] with x hx
    simpa [hF_def] using (tendsto_const_nhds (x := f 0 x)).add hx
  · -- dominated convergence with the bound `|f 0| + S`
    refine (theorem_4_2 hf ?_ ((hf 0).norm.add hS_int) fun n => ?_).2
    · filter_upwards [hFS] with x hx
      simpa [hF_def] using (tendsto_const_nhds (x := f 0 x)).add hx
    · filter_upwards [hFS_le n, hF_nn n] with x hx hnn
      simp only [Pi.add_apply, Real.norm_eq_abs]
      calc |f n x| = |f 0 x + F n x| := by rw [hF_def]; ring_nf
        _ ≤ |f 0 x| + |F n x| := abs_add_le _ _
        _ = |f 0 x| + F n x := by rw [abs_of_nonneg hnn]
        _ ≤ |f 0 x| + S x := by linarith

/-! ### Lemma 4.1: Fatou's lemma -/

/-- **Lemma 4.1** of [brezis2011functional] (Fatou's lemma). Let $(f_n)$ be a sequence of integrable
functions on $\Omega$ such that $f_n \ge 0$ a.e. for every $n$ and $\sup_n \int f_n < \infty$.
For $x \in \Omega$ let $f(x) = \liminf_{n \to \infty} f_n(x) \le +\infty$. Then $f(x) < \infty$
for a.e. $x$, $f$ is integrable, and
$$\int_\Omega f \, d\mu \le \liminf_{n \to \infty} \int_\Omega f_n \, d\mu.$$

The limit inferior $f(x)$ is taken in $[0, +\infty]$, as the source allows, through
`ENNReal.ofReal`. The function that is integrated is its real part `toReal`, which equals $f$
where $f$ is finite. -/
theorem lemma_4_1 {f : ℕ → α → ℝ} (hf : ∀ n, Integrable (f n) μ)
    (hnn : ∀ n, ∀ᵐ x ∂μ, 0 ≤ f n x) (hbdd : BddAbove (Set.range fun n => ∫ x, f n x ∂μ)) :
    (∀ᵐ x ∂μ, liminf (fun n => ENNReal.ofReal (f n x)) atTop < ∞) ∧
      Integrable (fun x => (liminf (fun n => ENNReal.ofReal (f n x)) atTop).toReal) μ ∧
      ∫ x, (liminf (fun n => ENNReal.ofReal (f n x)) atTop).toReal ∂μ ≤
        liminf (fun n => ∫ x, f n x ∂μ) atTop := by
  obtain ⟨B, hB⟩ := hbdd
  have hf_meas : ∀ n, AEMeasurable (fun x => ENNReal.ofReal (f n x)) μ := fun n =>
    ENNReal.measurable_ofReal.comp_aemeasurable (hf n).aemeasurable
  set L : α → ℝ≥0∞ := fun x => liminf (fun n => ENNReal.ofReal (f n x)) atTop with hL_def
  have hL_meas : AEMeasurable L μ := AEMeasurable.liminf hf_meas
  have hI_nn : ∀ n, 0 ≤ ∫ x, f n x ∂μ := fun n => integral_nonneg_of_ae (hnn n)
  -- the integrals form a bounded sequence, so `ofReal` commutes with their `liminf`
  have hcobdd : IsCoboundedUnder (· ≥ ·) atTop fun n => ∫ x, f n x ∂μ :=
    (isBoundedUnder_of ⟨B, fun n => hB ⟨n, rfl⟩⟩).isCoboundedUnder_ge
  have hbdd_below : IsBoundedUnder (· ≥ ·) atTop fun n => ∫ x, f n x ∂μ :=
    isBoundedUnder_of ⟨0, hI_nn⟩
  have hmono_ofReal : Monotone ENNReal.ofReal := fun _ _ h => ENNReal.ofReal_le_ofReal h
  have hofReal : ENNReal.ofReal (liminf (fun n => ∫ x, f n x ∂μ) atTop) =
      liminf (fun n => ENNReal.ofReal (∫ x, f n x ∂μ)) atTop :=
    hmono_ofReal.map_liminf_of_continuousAt _ ENNReal.continuous_ofReal.continuousAt
      hcobdd hbdd_below
  -- `∫⁻ L ≤ liminf ∫⁻ ofReal (f n) = ofReal (liminf ∫ f n) < ∞`
  have hL_le : ∫⁻ x, L x ∂μ ≤ ENNReal.ofReal (liminf (fun n => ∫ x, f n x ∂μ) atTop) := by
    rw [hofReal]
    refine (lintegral_liminf_le' hf_meas).trans (le_of_eq ?_)
    congr 1
    ext n
    exact (ofReal_integral_eq_lintegral_ofReal (hf n) (hnn n)).symm
  have hL_int : ∫⁻ x, L x ∂μ ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hL_le
  have hL_fin : ∀ᵐ x ∂μ, L x < ∞ := ae_lt_top' hL_meas hL_int
  refine ⟨hL_fin, integrable_toReal_of_lintegral_ne_top hL_meas hL_int, ?_⟩
  rw [integral_toReal hL_meas hL_fin]
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top hL_le).trans (le_of_eq ?_)
  exact ENNReal.toReal_ofReal (le_liminf_of_le hcobdd (Eventually.of_forall hI_nn))

/-! ### Theorem 4.3: density of $C_c(\mathbb{R}^N)$ in $L^1(\mathbb{R}^N)$ -/

/-- **Theorem 4.3** of [brezis2011functional] (density). The space $C_c(\mathbb{R}^N)$ is dense in
$L^1(\mathbb{R}^N)$: for every integrable $f : \mathbb{R}^N \to \mathbb{R}$ and every
$\varepsilon > 0$ there is a continuous function $g$ with compact support such that
$\int |f - g| \le \varepsilon$.

The space $\mathbb{R}^N$ is `EuclideanSpace ℝ (Fin N)` with Lebesgue measure. -/
theorem theorem_4_3 {N : ℕ} {f : EuclideanSpace ℝ (Fin N) → ℝ} (hf : Integrable f) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ g : EuclideanSpace ℝ (Fin N) → ℝ, Continuous g ∧ HasCompactSupport g ∧
      ∫ x, |f x - g x| ≤ ε := by
  obtain ⟨g, hgs, hgε, hgc, -⟩ := hf.exists_hasCompactSupport_integral_sub_le hε
  exact ⟨g, hgc, hgs, by simpa [Real.norm_eq_abs] using hgε⟩

/-! ### Theorems 4.4 and 4.5: Tonelli and Fubini -/

variable {α₁ α₂ : Type*} [MeasurableSpace α₁] [MeasurableSpace α₂] {μ₁ : Measure α₁}
  {μ₂ : Measure α₂}

/-- **Theorem 4.4** of [brezis2011functional] (Tonelli). Let $(\Omega_1, \mu_1)$ and
$(\Omega_2, \mu_2)$ be σ-finite measure spaces, and let
$F : \Omega_1 \times \Omega_2 \to \mathbb{R}$ be measurable. Suppose that

1. for a.e. $x \in \Omega_1$, $\int_{\Omega_2} |F(x, y)| \, d\mu_2 < \infty$, and
2. $\int_{\Omega_1} d\mu_1 \int_{\Omega_2} |F(x, y)| \, d\mu_2 < \infty$.

Then $F$ is integrable on $\Omega_1 \times \Omega_2$.

Clause (1) is the integrability of the section $y \mapsto F(x, y)$ for a.e. $x$, and clause (2)
is the integrability of $x \mapsto \int |F(x, y)| \, d\mu_2$. Measurability of $F$ is
`AEStronglyMeasurable` for the product measure. -/
theorem theorem_4_4 [SigmaFinite μ₁] [SigmaFinite μ₂] {F : α₁ × α₂ → ℝ}
    (hF : AEStronglyMeasurable F (μ₁.prod μ₂))
    (ha : ∀ᵐ x ∂μ₁, Integrable (fun y => F (x, y)) μ₂)
    (hb : Integrable (fun x => ∫ y, |F (x, y)| ∂μ₂) μ₁) : Integrable F (μ₁.prod μ₂) :=
  (integrable_prod_iff hF).2 ⟨ha, by simpa [Real.norm_eq_abs] using hb⟩

/-- **Theorem 4.5** of [brezis2011functional] (Fubini). Let $(\Omega_1, \mu_1)$ and
$(\Omega_2, \mu_2)$ be σ-finite measure spaces, and let $F \in L^1(\Omega_1 \times \Omega_2)$.
Then for a.e. $x \in \Omega_1$ the function $y \mapsto F(x, y)$ is integrable on $\Omega_2$, and
$x \mapsto \int_{\Omega_2} F(x, y) \, d\mu_2$ is integrable on $\Omega_1$. The same holds with
the roles of $x$ and $y$ exchanged. Moreover
$$\int_{\Omega_1} d\mu_1 \int_{\Omega_2} F(x, y) \, d\mu_2 = \int_{\Omega_2} d\mu_2
  \int_{\Omega_1} F(x, y) \, d\mu_1 = \iint_{\Omega_1 \times \Omega_2} F \, d\mu_1 \, d\mu_2.$$
-/
theorem theorem_4_5 [SigmaFinite μ₁] [SigmaFinite μ₂] {F : α₁ × α₂ → ℝ}
    (hF : Integrable F (μ₁.prod μ₂)) :
    ((∀ᵐ x ∂μ₁, Integrable (fun y => F (x, y)) μ₂) ∧
        Integrable (fun x => ∫ y, F (x, y) ∂μ₂) μ₁) ∧
      ((∀ᵐ y ∂μ₂, Integrable (fun x => F (x, y)) μ₁) ∧
        Integrable (fun y => ∫ x, F (x, y) ∂μ₁) μ₂) ∧
      ∫ x, ∫ y, F (x, y) ∂μ₂ ∂μ₁ = ∫ z, F z ∂(μ₁.prod μ₂) ∧
      ∫ y, ∫ x, F (x, y) ∂μ₁ ∂μ₂ = ∫ z, F z ∂(μ₁.prod μ₂) :=
  ⟨⟨hF.prod_right_ae, hF.integral_prod_left⟩, ⟨hF.prod_left_ae, hF.integral_prod_right⟩,
    (integral_prod F hF).symm, (integral_prod_symm F hF).symm⟩

/-! ### Theorem 4.29: Egorov's theorem -/

/-- **Theorem 4.29** of [brezis2011functional] (Egorov). Let $\Omega$ have finite measure, and let
$(f_n)$ be a sequence of measurable functions that converges a.e. to a measurable function $f$.
Then for every $\varepsilon > 0$ there is a measurable set $A \subseteq \Omega$ with
$\mu(\Omega \setminus A) < \varepsilon$ such that $f_n \to f$ uniformly on $A$.

The source states this theorem in the Comments on Chapter 4. The number $\varepsilon$ lies in
$(0, +\infty]$. The measurability of the limit is a hypothesis, but the proof does not use it. -/
theorem theorem_4_29 [IsFiniteMeasure μ] {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf : ∀ n, StronglyMeasurable (f n)) (_hg : StronglyMeasurable g)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ A : Set α, MeasurableSet A ∧ μ Aᶜ < ε ∧ TendstoUniformlyOn f g atTop A := by
  obtain ⟨t, ht, hμt, hunif⟩ :=
    tendstoUniformlyOn_of_ae_tendsto' (fun n => (hf n).aestronglyMeasurable) hfg
      (lt_min (ENNReal.half_pos hε.ne') one_pos)
  refine ⟨tᶜ, ht.compl, ?_, hunif⟩
  rw [compl_compl]
  refine hμt.trans_lt ?_
  by_cases hε' : ε = ∞
  · rw [hε']
    exact (min_le_right _ _).trans_lt ENNReal.one_lt_top
  · exact (min_le_left _ _).trans_lt (ENNReal.half_lt_self hε.ne' hε')

end Brezis.Chapter04
