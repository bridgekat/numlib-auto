/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp`, which has the two-factor
Hölder inequality and the comparison of exponents on a finite measure.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Hölder's inequality for finitely many factors, and interpolation between $L^p$ spaces

This file proves two consequences of Hölder's inequality that Mathlib states only in special forms.
The first is **Hölder's inequality for finitely many factors**: if $1/r = \sum_i 1/p_i$, then
$$\Big\|\prod_i f_i\Big\|_r \le \prod_i \|f_i\|_{p_i}.$$
The second is the **interpolation inequality**: if $1/r = \theta/p + (1 - \theta)/q$ with
$0 \le \theta \le 1$, then
$$\|f\|_r \le \|f\|_p^\theta \, \|f\|_q^{1 - \theta}.$$
Hence $L^p \cap L^q \subseteq L^r$ for every $r$ between $p$ and $q$. The Sobolev embedding theorems
use this inequality to pass from the endpoint exponents to the intermediate ones. The presentation
follows Remark 2 and Exercise 4.4 in Chapter 4 of [brezis2011functional].

The file also states $\int^- \|f\|^p \, d\mu = \|f\|_p^p$ for $0 < p < \infty$. Every module of this
directory that works with $p$-th powers of the $L^p$ seminorm uses it.

## Main results

* `MeasureTheory.lintegral_rpow_enorm_eq_rpow_eLpNorm`: $\int^- \|f\|^p \, d\mu = \|f\|_p^p$ for
  $0 < p < \infty$.
* `MeasureTheory.eLpNorm_finset_prod_le`: Hölder's inequality for finitely many factors.
* `MeasureTheory.eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow`: the interpolation inequality.
* `MeasureTheory.exists_inv_eq_ofReal_mul_inv_add`: every exponent $r$ with $0 < p \le r \le q$
  satisfies $1/r = \theta/p + (1 - \theta)/q$ for some $\theta \in [0, 1]$.
* `MeasureTheory.MemLp.interpolate`: for $p > 0$, $L^p \cap L^q \subseteq L^r$ for every $r$ between
  $p$ and $q$.

## Proof outline

Hölder's inequality for a product is proved by induction on the number of factors, with the
two-factor inequality `MeasureTheory.eLpNorm_smul_le_mul_eLpNorm` in each step. This is the
induction of Mathlib's `MeasureTheory.MemLp.prod`, with the inequality in place of
`MeasureTheory.MemLp.mul`. The interpolation inequality is the two-factor Hölder inequality for the
factorization $\|f\| = \|f\|^\theta \, \|f\|^{1 - \theta}$ with the exponents $p/\theta$ and
$q/(1 - \theta)$.

## Implementation notes

* The exponents are in $[0, \infty]$, so the endpoints $p = \infty$ and $q = \infty$ are included.
  The arithmetic is that of `ℝ≥0∞`, with $1/0 = \infty$ and $1/\infty = 0$.
* The $L^p$ seminorm is the `ℝ≥0∞`-valued `MeasureTheory.eLpNorm`.
-/

open Filter Function Set
open scoped ENNReal NNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Let $F$ be a normed group, let $0 < p < \infty$, and let $f \colon \alpha \to F$ be almost
everywhere strongly measurable. Then
$$\int^- \|f(a)\|^p \, d\mu(a) = \|f\|_p^p.$$

This is the form without a prime of Mathlib's
`MeasureTheory.lintegral_rpow_enorm_eq_rpow_eLpNorm'`. The power is taken with the real exponent
`p.toReal`. -/
theorem lintegral_rpow_enorm_eq_rpow_eLpNorm {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞}
    (hp₀ : p ≠ 0) (hp : p ≠ ∞) {f : α → F} (hf : AEStronglyMeasurable f μ) :
    ∫⁻ a, ‖f a‖ₑ ^ p.toReal ∂μ = eLpNorm f p μ ^ p.toReal := by
  rw [eLpNorm_eq_eLpNorm' hp₀ hp hf,
    lintegral_rpow_enorm_eq_rpow_eLpNorm' (ENNReal.toReal_pos hp₀ hp)]

/-! ### Hölder's inequality for finitely many factors -/

section Prod

variable {ι R : Type*} [NormedCommRing R] [NormOneClass R] {f : ι → α → R} {p : ι → ℝ≥0∞}
  {s : Finset ι}

/-- **Hölder's inequality for finitely many factors**, with the exponent of the product written as
$(\sum_{i \in s} p_i^{-1})^{-1}$. Let $R$ be a normed commutative ring with $\|1\| = 1$, let $s$
be a finite index set, and let $f_i \colon \alpha \to R$ be almost everywhere strongly
measurable and $p_i \in [0, \infty]$ for $i \in s$. Then
$$\Big\|\prod_{i \in s} f_i\Big\|_r \le \prod_{i \in s} \|f_i\|_{p_i}, \qquad r = \Big(\sum_{i
  \in s} p_i^{-1}\Big)^{-1}.$$

The inverses are taken in `ℝ≥0∞`. This is the inequality behind Mathlib's
`MeasureTheory.MemLp.prod`. -/
theorem eLpNorm_finset_prod_le_of_inv (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) :
    eLpNorm (∏ i ∈ s, f i) (∑ i ∈ s, (p i)⁻¹)⁻¹ μ ≤ ∏ i ∈ s, eLpNorm (f i) (p i) μ := by
  induction s using Finset.cons_induction with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty, ENNReal.inv_zero]
    rw [eLpNorm_exponent_top aestronglyMeasurable_one]
    exact eLpNormEssSup_le_of_ae_enorm_bound (Eventually.of_forall fun x => by simp)
  | cons i s hi ih =>
    have hi' : AEStronglyMeasurable (f i) μ := hf i (Finset.mem_cons_self ..)
    have hs : ∀ j ∈ s, AEStronglyMeasurable (f j) μ := fun j hj =>
      hf j (Finset.mem_cons_of_mem hj)
    have : ENNReal.HolderTriple (p i) (∑ j ∈ s, (p j)⁻¹)⁻¹ ((p i)⁻¹ + ∑ j ∈ s, (p j)⁻¹)⁻¹ :=
      ⟨by simp⟩
    rw [Finset.prod_cons, Finset.sum_cons, Finset.prod_cons]
    calc eLpNorm (f i * ∏ j ∈ s, f j) ((p i)⁻¹ + ∑ j ∈ s, (p j)⁻¹)⁻¹ μ
        ≤ eLpNorm (f i) (p i) μ * eLpNorm (∏ j ∈ s, f j) (∑ j ∈ s, (p j)⁻¹)⁻¹ μ :=
          eLpNorm_smul_le_mul_eLpNorm hi' (Finset.aestronglyMeasurable_prod s hs)
      _ ≤ eLpNorm (f i) (p i) μ * ∏ j ∈ s, eLpNorm (f j) (p j) μ := by gcongr; exact ih hs

/-- **Hölder's inequality for finitely many factors.** Let $R$ be a normed commutative ring with
$\|1\| = 1$, let $s$ be a finite index set, and let $f_i \colon \alpha \to R$ be almost
everywhere strongly measurable and $p_i \in [0, \infty]$ for $i \in s$. If $r \in [0, \infty]$
satisfies $1/r = \sum_{i \in s} 1/p_i$, then
$$\Big\|\prod_{i \in s} f_i\Big\|_r \le \prod_{i \in s} \|f_i\|_{p_i}.$$
This is Remark 2 in Chapter 4 of [brezis2011functional].

The inverses are taken in `ℝ≥0∞`. The statement $\prod_i f_i \in L^r$ is Mathlib's
`MeasureTheory.MemLp.prod`. -/
theorem eLpNorm_finset_prod_le (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) {r : ℝ≥0∞}
    (hr : r⁻¹ = ∑ i ∈ s, (p i)⁻¹) :
    eLpNorm (∏ i ∈ s, f i) r μ ≤ ∏ i ∈ s, eLpNorm (f i) (p i) μ := by
  rw [← inv_inv r, hr]
  exact eLpNorm_finset_prod_le_of_inv hf

/-- The form of `MeasureTheory.eLpNorm_finset_prod_le` for the pointwise product
$x \mapsto \prod_{i \in s} f_i(x)$: if $1/r = \sum_{i \in s} 1/p_i$, then $\|x \mapsto \prod_{i
\in s} f_i(x)\|_r \le \prod_{i \in s} \|f_i\|_{p_i}$. -/
theorem eLpNorm_finset_fun_prod_le (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) {r : ℝ≥0∞}
    (hr : r⁻¹ = ∑ i ∈ s, (p i)⁻¹) :
    eLpNorm (fun x => ∏ i ∈ s, f i x) r μ ≤ ∏ i ∈ s, eLpNorm (f i) (p i) μ := by
  simpa only [Finset.prod_fn] using eLpNorm_finset_prod_le hf hr

end Prod

/-! ### The interpolation inequality -/

section Interpolation

variable {E : Type*} [NormedAddCommGroup E] {f : α → E} {p q r : ℝ≥0∞}

/-- **The interpolation inequality.** Let $E$ be a normed group, let $f \colon \alpha \to E$ be
almost everywhere strongly measurable, let $p, q, r \in [0, \infty]$, and let
$0 \le \theta \le 1$. If
$$\frac{1}{r} = \frac{\theta}{p} + \frac{1 - \theta}{q},$$
then
$$\|f\|_r \le \|f\|_p^\theta \, \|f\|_q^{1 - \theta}.$$
This is Remark 2 and Exercise 4.4 in Chapter 4 of [brezis2011functional].

The arithmetic is that of `ℝ≥0∞`, so $p = \infty$ or $q = \infty$ is allowed. The inequality is
trivial for $\theta = 0$, where $r = q$, and for $\theta = 1$, where $r = p$. For
$0 < \theta < 1$ it is Hölder's inequality `MeasureTheory.eLpNorm_smul_le_mul_eLpNorm` for the
factorization $\|f\| = \|f\|^\theta \, \|f\|^{1 - \theta}$ with the exponents $p/\theta$ and
$q/(1 - \theta)$. -/
theorem eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow (hf : AEStronglyMeasurable f μ) {θ : ℝ}
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hr : r⁻¹ = ENNReal.ofReal θ * p⁻¹ + ENNReal.ofReal (1 - θ) * q⁻¹) :
    eLpNorm f r μ ≤ eLpNorm f p μ ^ θ * eLpNorm f q μ ^ (1 - θ) := by
  rcases hθ₀.eq_or_lt with rfl | hθ₀'
  · obtain rfl : r = q := by rw [← inv_inj, hr]; simp
    simp
  rcases hθ₁.eq_or_lt with rfl | hθ₁'
  · obtain rfl : r = p := by rw [← inv_inj, hr]; simp
    simp
  have h1θ : 0 < 1 - θ := by linarith
  have ha0 : ENNReal.ofReal θ ≠ 0 := by simpa [ENNReal.ofReal_eq_zero] using hθ₀'
  have hb0 : ENNReal.ofReal (1 - θ) ≠ 0 := by simpa [ENNReal.ofReal_eq_zero] using h1θ
  have hpq : ENNReal.HolderTriple (p / ENNReal.ofReal θ) (q / ENNReal.ofReal (1 - θ)) r := ⟨by
    rw [ENNReal.inv_div (Or.inl ENNReal.ofReal_ne_top) (Or.inl ha0),
      ENNReal.inv_div (Or.inl ENNReal.ofReal_ne_top) (Or.inl hb0), hr, div_eq_mul_inv,
      div_eq_mul_inv]⟩
  have hφ : AEStronglyMeasurable (fun x => ‖f x‖ ^ θ) μ :=
    (hf.norm.aemeasurable.pow_const θ).aestronglyMeasurable
  have hψ : AEStronglyMeasurable (fun x => ‖f x‖ ^ (1 - θ)) μ :=
    (hf.norm.aemeasurable.pow_const (1 - θ)).aestronglyMeasurable
  have key := eLpNorm_smul_le_mul_eLpNorm (μ := μ) hφ hψ (hpqr := hpq)
  have hprod : ((fun x => ‖f x‖ ^ θ) • fun x => ‖f x‖ ^ (1 - θ)) = fun x => ‖f x‖ := by
    funext x
    change ‖f x‖ ^ θ * ‖f x‖ ^ (1 - θ) = ‖f x‖
    rw [← Real.rpow_add' (norm_nonneg _) (by norm_num), add_sub_cancel, Real.rpow_one]
  rwa [hprod, eLpNorm_norm f hf, eLpNorm_norm_rpow f hf hθ₀', eLpNorm_norm_rpow f hf h1θ,
    ENNReal.div_mul_cancel ha0 ENNReal.ofReal_ne_top,
    ENNReal.div_mul_cancel hb0 ENNReal.ofReal_ne_top] at key

/-- Let $p, q, r \in [0, \infty]$ with $p \neq 0$ and $p \le r \le q$. Then there is
$\theta \in [0, 1]$ with
$$\frac{1}{r} = \frac{\theta}{p} + \frac{1 - \theta}{q},$$
in the arithmetic of `ℝ≥0∞`. -/
theorem exists_inv_eq_ofReal_mul_inv_add (hp : p ≠ 0) (hpr : p ≤ r) (hrq : r ≤ q) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧
      r⁻¹ = ENNReal.ofReal θ * p⁻¹ + ENNReal.ofReal (1 - θ) * q⁻¹ := by
  rcases eq_or_ne p q with rfl | hpq
  · obtain rfl : r = p := le_antisymm hrq hpr
    exact ⟨1, zero_le_one, le_rfl, by simp⟩
  have hqp : q⁻¹ < p⁻¹ := ENNReal.inv_lt_inv.2 (lt_of_le_of_ne (hpr.trans hrq) hpq)
  have hcr : q⁻¹ ≤ r⁻¹ := ENNReal.inv_le_inv.2 hrq
  have hrp : r⁻¹ ≤ p⁻¹ := ENNReal.inv_le_inv.2 hpr
  have hpt : p⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hp
  have hrt : r⁻¹ ≠ ∞ := ne_top_of_le_ne_top hpt hrp
  have hqt : q⁻¹ ≠ ∞ := ne_top_of_le_ne_top hrt hcr
  set A := p⁻¹.toReal with hA
  set B := q⁻¹.toReal with hB
  set C := r⁻¹.toReal with hC
  have hBA : B < A := ENNReal.toReal_strict_mono hpt hqp
  have hBC : B ≤ C := ENNReal.toReal_mono hrt hcr
  have hCA : C ≤ A := ENNReal.toReal_mono hpt hrp
  have hAB : 0 < A - B := sub_pos.2 hBA
  refine ⟨(C - B) / (A - B), div_nonneg (sub_nonneg.2 hBC) hAB.le,
    (div_le_one hAB).2 (sub_le_sub_right hCA B), ?_⟩
  have h1 : 1 - (C - B) / (A - B) = (A - C) / (A - B) := by
    field_simp
    ring
  rw [h1, ← ENNReal.ofReal_toReal hpt, ← ENNReal.ofReal_toReal hqt, ← ENNReal.ofReal_toReal hrt,
    ← hA, ← hB, ← hC, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  field_simp
  ring

/-- **Interpolation of $L^p$ spaces.** Let $p, q, r \in [0, \infty]$ with $p \neq 0$ and
$p \le r \le q$. If $f \in L^p(\mu) \cap L^q(\mu)$, then $f \in L^r(\mu)$. This is Remark 2 in
Chapter 4 of [brezis2011functional].

The condition $p \neq 0$ is needed because `MemLp f 0 μ` says only that $f$ is almost everywhere
strongly measurable. -/
theorem MemLp.interpolate (hp : p ≠ 0) (hfp : MemLp f p μ) (hfq : MemLp f q μ) (hpr : p ≤ r)
    (hrq : r ≤ q) : MemLp f r μ := by
  obtain ⟨θ, hθ₀, hθ₁, hr⟩ := exists_inv_eq_ofReal_mul_inv_add hp hpr hrq
  refine memLp_iff.2
    ((eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow hfp.aestronglyMeasurable hθ₀ hθ₁ hr).trans_lt ?_)
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hθ₀ hfp.eLpNorm_ne_top)
    (ENNReal.rpow_lt_top_of_nonneg (by linarith) hfq.eLpNorm_ne_top)

end Interpolation

end MeasureTheory
