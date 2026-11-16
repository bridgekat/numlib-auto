/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Numlib.Analysis.Normed.Lp.SmoothApprox

/-!
# Atkinson and Han, Section 1.5: The $L^p$ spaces

This module formalizes §1.5 of [han2009theoretical]: Young's inequality $ab \le a^p/p + b^q/q$ and
its $\varepsilon$-weighted form, Hölder's and Minkowski's inequalities, the completeness of
$L^p(\Omega)$, the almost everywhere convergence of a subsequence of a Cauchy sequence in
$L^p(\Omega)$, the inclusions $L^q(\Omega) \subseteq L^p(\Omega)$ for $p \le q$ on a set of finite
measure with the constant $\operatorname{meas}(\Omega)^{1/p - 1/q}$, and the density of
$C_0^\infty(\Omega)$ in $L^p(\Omega)$ for $1 \le p < \infty$.

All of this is in Mathlib, and the density theorem is in the backbone module
`Numlib.Analysis.Normed.Lp.SmoothApprox`. The section is restated because it is the book's account
of the spaces over which every later chapter integrates. Theorem 1.5.5(c) is the one statement whose
Mathlib form is not obviously the book's.

## Main results

* Lemma 1.5.1, `AtkinsonHan.Chapter01.lemma_1_5_1`: Young's inequality.
* Lemma 1.5.2, `AtkinsonHan.Chapter01.lemma_1_5_2`: the modified Young inequality with a weight
  $\varepsilon > 0$.
* Lemma 1.5.3, `AtkinsonHan.Chapter01.lemma_1_5_3`: Hölder's inequality.
* Lemma 1.5.4, `AtkinsonHan.Chapter01.lemma_1_5_4`: Minkowski's inequality.
* Theorem 1.5.5(a), `AtkinsonHan.Chapter01.theorem_1_5_5_a`: $L^p(\Omega)$ is a Banach space.
* Theorem 1.5.5(b), `AtkinsonHan.Chapter01.theorem_1_5_5_b`: a Cauchy sequence in $L^p(\Omega)$ has
  a subsequence that converges almost everywhere.
* Theorem 1.5.5(c), `AtkinsonHan.Chapter01.theorem_1_5_5_c`: on a set of finite measure,
  $L^q(\Omega) \subseteq L^p(\Omega)$ for $p \le q$, with $\|v\|_{L^p} \le
  \operatorname{meas}(\Omega)^{1/p - 1/q} \|v\|_{L^q}$.
* Theorem 1.5.6, `AtkinsonHan.Chapter01.theorem_1_5_6` and
  `AtkinsonHan.Chapter01.theorem_1_5_6_open`: $C_0^\infty(\mathbb{R}^d)$ is dense in
  $L^p(\mathbb{R}^d)$, and for an open $\Omega \subseteq \mathbb{R}^d$, $C_0^\infty(\Omega)$ is
  dense in $L^p(\Omega)$, for $1 \le p < \infty$. The second statement also covers Example 1.2.19,
  the same density for a bounded open set.

## Conventions

* The book's exponent $p \in [1, \infty]$ is `p : ℝ≥0∞` with `Fact (1 ≤ p)` or a hypothesis `1 ≤ p`.
* The book's norm $\|\cdot\|_{L^p}$ is `MeasureTheory.eLpNorm`, the $L^p$ norm with values in
  $[0, \infty]$.
* The functions are real valued.

## Deviations from the source

* **Lemmas 1.5.3 and 1.5.4 and Theorem 1.5.5** (generalization). The book works on a set
  $\Omega \subseteq \mathbb{R}^d$ with Lebesgue measure. The statements hold on an arbitrary measure
  space, and Theorem 1.5.5(c) on an arbitrary finite measure space and without the assumption
  $p \ge 1$. See `AtkinsonHan.Chapter01.lemma_1_5_3`, `AtkinsonHan.Chapter01.lemma_1_5_4`,
  `AtkinsonHan.Chapter01.theorem_1_5_5_a`, `AtkinsonHan.Chapter01.theorem_1_5_5_b` and
  `AtkinsonHan.Chapter01.theorem_1_5_5_c`.

## Not formalized

* **The Clarkson inequalities (1.5.5)–(1.5.6).** The book states them without proof for Exercise
  2.7.4(b), that $L^p$ is uniformly convex; they are not in Mathlib, and nothing else uses them.
-/

open Filter MeasureTheory Topology
open scoped ENNReal ContDiff

namespace AtkinsonHan.Chapter01

/-! ### Young's inequality -/

/-- **Lemma 1.5.1** of [han2009theoretical] (Young's inequality). Let $a, b \ge 0$, and let
$p, q > 1$ be conjugate exponents, $1/p + 1/q = 1$. Then $$ab \le \frac{a^p}{p} +
\frac{b^q}{q}.$$

The conjugacy of $p$ and $q$ is `Real.HolderConjugate p q`, and the powers are real powers. -/
theorem lemma_1_5_1 {a b p q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hpq : p.HolderConjugate q) :
    a * b ≤ a ^ p / p + b ^ q / q :=
  Real.young_inequality_of_nonneg ha hb hpq

/-- **Lemma 1.5.2** of [han2009theoretical] (modified Young inequality). Let $a, b \ge 0$, let
$p, q > 1$ be conjugate exponents, $1/p + 1/q = 1$, and let $\varepsilon > 0$. Then $$ab \le
\varepsilon \frac{a^p}{p} + \varepsilon^{1 - q} \frac{b^q}{q}.$$

The proof applies Lemma 1.5.1 to $\varepsilon^{1/p} a$ and $\varepsilon^{-1/p} b$. -/
theorem lemma_1_5_2 {a b p q ε : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hpq : p.HolderConjugate q)
    (hε : 0 < ε) : a * b ≤ ε * a ^ p / p + ε ^ (1 - q) * b ^ q / q := by
  have hp := hpq.pos
  have hq := hpq.symm.pos
  have hεp : (0 : ℝ) < ε ^ (1 / p) := Real.rpow_pos_of_pos hε _
  have hεm : (0 : ℝ) < ε ^ (-(1 / p)) := Real.rpow_pos_of_pos hε _
  -- `q / p = q - 1`, from `p⁻¹ + q⁻¹ = 1`.
  have hqp : q * (1 / p) = q - 1 := by
    have h := hpq.inv_add_inv_eq_one
    field_simp at h ⊢
    linarith
  have key := lemma_1_5_1 (mul_nonneg hεp.le ha) (mul_nonneg hεm.le hb) hpq
  have hmul : ε ^ (1 / p) * a * (ε ^ (-(1 / p)) * b) = a * b := by
    rw [show ε ^ (1 / p) * a * (ε ^ (-(1 / p)) * b)
        = ε ^ (1 / p) * ε ^ (-(1 / p)) * (a * b) by ring, ← Real.rpow_add hε]
    simp
  have hfst : (ε ^ (1 / p) * a) ^ p = ε * a ^ p := by
    rw [Real.mul_rpow hεp.le ha, ← Real.rpow_mul hε.le, one_div, inv_mul_cancel₀ hp.ne',
      Real.rpow_one]
  have hsnd : (ε ^ (-(1 / p)) * b) ^ q = ε ^ (1 - q) * b ^ q := by
    rw [Real.mul_rpow hεm.le hb, ← Real.rpow_mul hε.le]
    congr 2
    rw [neg_mul, ← mul_comm q (1 / p), hqp]
    ring
  rw [hmul, hfst, hsnd] at key
  exact key

section Lp

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-! ### Hölder's and Minkowski's inequalities -/

/-- **Lemma 1.5.3** of [han2009theoretical] (Hölder's inequality). Let $\mu$ be a measure, and let
$p, q \in [1, \infty]$ be conjugate exponents, $1/p + 1/q = 1$. If $u \in L^p(\mu)$ and
$v \in L^q(\mu)$, then $uv \in L^1(\mu)$ and $$\|uv\|_{L^1} \le \|u\|_{L^p} \, \|v\|_{L^q}.$$

**Generalization.** The book states the inequality for Lebesgue measure on a set
$\Omega \subseteq \mathbb{R}^d$. The statement holds for an arbitrary measure.

The conjugacy of $p$ and $q$ is `ENNReal.HolderConjugate p q`, membership in $L^p$ is
`MeasureTheory.MemLp`, and the norms are `MeasureTheory.eLpNorm`. -/
theorem lemma_1_5_3 {p q : ℝ≥0∞} [ENNReal.HolderConjugate p q] {u v : α → ℝ} (hu : MemLp u p μ)
    (hv : MemLp v q μ) :
    MemLp (u * v) 1 μ ∧ eLpNorm (u * v) 1 μ ≤ eLpNorm u p μ * eLpNorm v q μ :=
  ⟨hu.mul hv, by
    simpa using eLpNorm_smul_le_mul_eLpNorm hu.aestronglyMeasurable hv.aestronglyMeasurable⟩

/-- **Lemma 1.5.4** of [han2009theoretical] (Minkowski's inequality). Let $\mu$ be a measure and
$1 \le p \le \infty$. For all functions $u, v$, $$\|u + v\|_{L^p} \le \|u\|_{L^p} +
\|v\|_{L^p}.$$ This is the triangle inequality for the $L^p$ norm.

**Generalization.** The book states the inequality for Lebesgue measure on a set
$\Omega \subseteq \mathbb{R}^d$. The statement holds for an arbitrary measure.

The norms are `MeasureTheory.eLpNorm`, with values in $[0, \infty]$, so the statement needs no
hypothesis that $u$ and $v$ lie in $L^p$. -/
theorem lemma_1_5_4 {p : ℝ≥0∞} (hp : 1 ≤ p) {u v : α → ℝ} :
    eLpNorm (u + v) p μ ≤ eLpNorm u p μ + eLpNorm v p μ :=
  eLpNorm_add_le hp

/-! ### Theorem 1.5.5 -/

/-- **Theorem 1.5.5(a)** of [han2009theoretical]. Let $\mu$ be a measure and $1 \le p \le \infty$.
Then $L^p(\mu)$ is a Banach space: it is complete for the $L^p$ norm.

**Generalization.** The book states the theorem for Lebesgue measure on a set
$\Omega \subseteq \mathbb{R}^d$. The statement holds for an arbitrary measure. -/
theorem theorem_1_5_5_a {p : ℝ≥0∞} [Fact (1 ≤ p)] : CompleteSpace (Lp ℝ p μ) :=
  inferInstance

/-- **Theorem 1.5.5(b)** of [han2009theoretical]. Let $\mu$ be a measure and $1 \le p \le \infty$.
Every Cauchy sequence $\{f_n\}$ in $L^p(\mu)$ has a subsequence $\{f_{\varphi(n)}\}$, with
$\varphi$ strictly increasing, that converges almost everywhere to a function $g$.

**Generalization.** The book states the theorem for Lebesgue measure on a set
$\Omega \subseteq \mathbb{R}^d$. The statement holds for an arbitrary measure.

The proof takes for $g$ a representative of the limit of $\{f_n\}$ in $L^p(\mu)$, but the
statement does not record this. -/
theorem theorem_1_5_5_b {p : ℝ≥0∞} [Fact (1 ≤ p)] {f : ℕ → Lp ℝ p μ} (hf : CauchySeq f) :
    ∃ (g : α → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ᵐ x ∂μ, Tendsto (fun n => f (φ n) x) atTop (𝓝 (g x)) := by
  obtain ⟨F, hF⟩ := cauchySeq_tendsto_of_complete hf
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hmeas : TendstoInMeasure μ (fun n => ⇑(f n)) atTop ⇑F :=
    tendstoInMeasure_of_tendsto_eLpNorm hp0 ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' f F).mp hF)
  obtain ⟨φ, hφ, hae⟩ := hmeas.exists_seq_tendsto_ae
  exact ⟨⇑F, φ, hφ, hae⟩

/-- **Theorem 1.5.5(c)** of [han2009theoretical]. Let $\mu$ be a finite measure on $\Omega$, and let
$p \le q$ in $[0, \infty]$. Every $v \in L^q(\Omega)$ lies in $L^p(\Omega)$, and $$\|v\|_{L^p}
\le \operatorname{meas}(\Omega)^{1/p - 1/q} \, \|v\|_{L^q},$$ with the conventions
$1/\infty = 0$ and $1/0 = 0$.

**Generalization.** The book states the inclusion for $1 \le p \le q \le \infty$ on a set
$\Omega \subseteq \mathbb{R}^d$ of finite Lebesgue measure. The statement holds for an arbitrary
finite measure and does not assume $p \ge 1$.

The measure $\operatorname{meas}(\Omega)$ is `μ Set.univ`. The exponent is
`1 / p.toReal - 1 / q.toReal`, and `p.toReal` is $0$ for $p = 0$ and for $p = \infty$, so $1/p$
is $0$ in both cases. For $p = 0$ the bound is trivial, because the $L^0$ norm `eLpNorm v 0 μ`
of a measurable function is $0$. -/
theorem theorem_1_5_5_c [IsFiniteMeasure μ] {p q : ℝ≥0∞} (hpq : p ≤ q) {v : α → ℝ}
    (hv : MemLp v q μ) :
    MemLp v p μ ∧ eLpNorm v p μ ≤ μ Set.univ ^ (1 / p.toReal - 1 / q.toReal) * eLpNorm v q μ :=
  ⟨hv.mono_exponent hpq, by
    rw [mul_comm]
    exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq hv.aestronglyMeasurable⟩

end Lp

/-! ### Theorem 1.5.6 -/

/-- **Theorem 1.5.6** of [han2009theoretical], the case $\Omega = \mathbb{R}^d$. Let
$1 \le p < \infty$. Then $C_0^\infty(\mathbb{R}^d)$ is dense in $L^p(\mathbb{R}^d)$: the classes
of the smooth functions with compact support form a dense subset of $L^p(\mathbb{R}^d)$.

The space $\mathbb{R}^d$ is `EuclideanSpace ℝ (Fin d)` with Lebesgue measure. The general case
is `AtkinsonHan.Chapter01.theorem_1_5_6_open`. -/
theorem theorem_1_5_6 {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    Dense {f : Lp ℝ p (volume : Measure (EuclideanSpace ℝ (Fin d))) |
      ∃ g : EuclideanSpace ℝ (Fin d) → ℝ,
        f =ᵐ[volume] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g} :=
  MeasureTheory.Lp.dense_hasCompactSupport_contDiff hp

/-- **Theorem 1.5.6** of [han2009theoretical]. Let $\Omega \subseteq \mathbb{R}^d$ be open and
$1 \le p < \infty$. Then $C_0^\infty(\Omega)$ is dense in $L^p(\Omega)$: the classes of the
smooth functions whose support is a compact subset of $\Omega$ form a dense subset of
$L^p(\Omega)$.

The book's form, "there is a sequence $\{v_n\} \subseteq C_0^\infty(\Omega)$ with
$\|v - v_n\|_{L^p(\Omega)} \to 0$", is the sequential reading of `Dense`. For a bounded $\Omega$
this is also Example 1.2.19. The case $\Omega = \mathbb{R}^d$ is
`AtkinsonHan.Chapter01.theorem_1_5_6`. The proof is in `Numlib.Analysis.Normed.Lp.SmoothApprox`:
the function is first localized to a compact subset of $\Omega$, and a smooth approximation of
the localized function is then multiplied by a smooth cut-off function with support in $\Omega$. -/
theorem theorem_1_5_6_open {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    Dense {f : Lp ℝ p ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict Ω) |
      ∃ g : EuclideanSpace ℝ (Fin d) → ℝ, f =ᵐ[volume.restrict Ω] g ∧
        HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧ tsupport g ⊆ Ω} :=
  MeasureTheory.Lp.dense_contDiff_tsupport_subset hΩ hp

end AtkinsonHan.Chapter01
