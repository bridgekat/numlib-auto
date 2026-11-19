/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.MeasureTheory.Function.LpInterpolation
import Numlib.MeasureTheory.Function.LpSpace.Convergence
import NumlibSurface.Brezis.Chapter04.Section01

/-!
# Brezis, Section 4.2: Definition and elementary properties of $L^p$ spaces

This module formalizes Section 4.2 of [brezis2011functional] for real-valued functions on a measure
space $(\Omega, \mathcal{M}, \mu)$. For $1 \le p < \infty$, the space $L^p(\Omega)$ consists of the
measurable functions $f$ with $|f|^p$ integrable, with the norm $\|f\|_p = (\int |f|^p)^{1/p}$. The
space $L^\infty(\Omega)$ consists of the measurable functions that are a.e. bounded, with the norm
$\|f\|_\infty = \inf\{C : |f| \le C \text{ a.e.}\}$. Elements of these spaces are classes of a.e.
equal functions. The module states Hölder's inequality (Theorem 4.6) and its extensions (Remark 2),
the facts that $L^p$ is a normed space (Theorem 4.7, Minkowski) and a Banach space (Theorem 4.8,
Fischer–Riesz) for $1 \le p \le \infty$, and that a convergent sequence in $L^p$ has a dominated
subsequence that converges a.e. (Theorem 4.9).

The proofs use Mathlib's `MeasureTheory.Lp`, and the backbone modules
`Numlib.MeasureTheory.Function.LpInterpolation` (Remark 2) and
`Numlib.MeasureTheory.Function.LpSpace.Convergence` (the domination in Theorem 4.9).

## Main definitions

* Section 4.2, definition of $L^p$ for $1 \le p < \infty$,
  `Brezis.Chapter04.lpNorm_eq_integral_rpow`: $f \in L^p$ if and only if $|f|^p$ is integrable, and
  $\|f\|_p = (\int |f|^p)^{1/p}$.
* Section 4.2, definition of $L^\infty$, `Brezis.Chapter04.lInftyNorm_eq_sInf`: $f \in L^\infty$ if
  and only if $|f| \le C$ a.e. for some $C$, and $\|f\|_\infty = \inf\{C : |f| \le C \text{
  a.e.}\}$.

## Main results

* Remark 1, `Brezis.Chapter04.remark_4_1`: $|f| \le \|f\|_\infty$ a.e. for $f \in L^\infty$.
* Theorem 4.6 (Hölder's inequality), `Brezis.Chapter04.theorem_4_6`: for conjugate exponents,
  $\int |fg| \le \|f\|_p \|g\|_{p'}$.
* Remark 2, `Brezis.Chapter04.remark_4_2`: the Hölder inequality for $k$ functions, and the
  interpolation inequality $\|f\|_r \le \|f\|_p^\alpha \|f\|_q^{1 - \alpha}$.
* Theorem 4.7, `Brezis.Chapter04.theorem_4_7`: $L^p$ is a vector space and $\|\cdot\|_p$ is a norm,
  for $1 \le p \le \infty$.
* Theorem 4.8 (Fischer–Riesz), `Brezis.Chapter04.theorem_4_8`: $L^p$ is a Banach space for
  $1 \le p \le \infty$.
* Theorem 4.9, `Brezis.Chapter04.theorem_4_9`: a convergent sequence in $L^p$ has a subsequence that
  converges a.e. and is dominated by a function of $L^p$.

## Conventions

* The space $L^p(\Omega)$ is Mathlib's `MeasureTheory.Lp ℝ p μ`, with the exponent `p : ℝ≥0∞`. That
  a function $f$ belongs to $L^p$ is `MemLp f p μ`, and its norm in $[0, +\infty]$ is
  `eLpNorm f p μ`.
* Conjugate exponents $p$ and $p'$, with $1/p + 1/p' = 1$, are `p.HolderConjugate q`.

## Deviations from the source

* **Measure hypotheses** (generalization). The results allow arbitrary measures. The source
  assumes $\sigma$-finiteness at the start of Chapter 4.
* **Definitions of the $L^p$ norms** (reading). The formulas allow a.e. measurable representatives.
  The finite-exponent formula includes $p=1$, and the $L^\infty$ formula uses the real `sInf`
  convention for the zero measure. See `Brezis.Chapter04.lpNorm_eq_integral_rpow` and
  `Brezis.Chapter04.lInftyNorm_eq_sInf`.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

namespace Brezis.Chapter04

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-! ### The definitions -/

/-- **Section 4.2** of [brezis2011functional], definition of $L^p$ and $\|\cdot\|_p$ for
$1 \le p < \infty$. Let $1 \le p < \infty$. A measurable function $f : \Omega \to \mathbb{R}$
belongs to $L^p(\Omega)$ if and only if $|f|^p$ is integrable. For $f \in L^p(\Omega)$,
$$\|f\|_p = \Bigl(\int_\Omega |f|^p \, d\mu\Bigr)^{1/p}.$$

The source takes these formulas as the definition. Here they are proved for Mathlib's `MemLp`
and the norm of `MeasureTheory.Lp`.

**Generalization.** The formulas apply to any measure and use a.e. measurable representatives.
They include $p=1$, given separately at the start of Chapter 4 in the source. -/
theorem lpNorm_eq_integral_rpow {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    (∀ f : α → ℝ, AEStronglyMeasurable f μ →
      (MemLp f p μ ↔ Integrable (fun x => |f x| ^ p.toReal) μ)) ∧
    ∀ f : Lp ℝ p μ, ‖f‖ = (∫ x, |f x| ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hP : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  refine ⟨fun f hf => ?_, fun f => ?_⟩
  · rw [← memLp_norm_rpow_iff hf hp0 hp, ENNReal.div_self hp0 hp, memLp_one_iff_integrable]
    simp only [Real.norm_eq_abs]
  · have hint : Integrable (fun x => |f x| ^ p.toReal) μ := by
      simpa only [Real.norm_eq_abs] using (Lp.memLp f).integrable_norm_rpow hp0 hp
    rw [Lp.norm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp (Lp.aestronglyMeasurable f),
      ← ENNReal.toReal_rpow]
    congr 1
    rw [← ENNReal.toReal_ofReal (integral_nonneg fun x => by positivity),
      ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => by positivity)]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hP.le, ← Real.norm_eq_abs, ofReal_norm]

/-- **Section 4.2** of [brezis2011functional], definition of $L^\infty$ and $\|\cdot\|_\infty$. A
measurable function $f : \Omega \to \mathbb{R}$ belongs to $L^\infty(\Omega)$ if and only if
there is a constant $C$ with $|f(x)| \le C$ for a.e. $x \in \Omega$. For
$f \in L^\infty(\Omega)$,
$$\|f\|_\infty = \inf\{C : |f(x)| \le C \text{ for a.e. } x \in \Omega\}.$$

The source takes these formulas as the definition. Here they are proved for Mathlib's `MemLp`
with exponent $\infty$ and the norm of `MeasureTheory.Lp`.

**Reading.** The formulas apply to any measure and use a.e. measurable representatives. For
the zero measure all real constants qualify, and the real `sInf` convention gives norm zero. -/
theorem lInftyNorm_eq_sInf :
    (∀ f : α → ℝ, AEStronglyMeasurable f μ → (MemLp f ∞ μ ↔ ∃ C : ℝ, ∀ᵐ x ∂μ, |f x| ≤ C)) ∧
    ∀ f : Lp ℝ ∞ μ, ‖f‖ = sInf {C : ℝ | ∀ᵐ x ∂μ, |f x| ≤ C} := by
  refine ⟨fun f hf => ⟨fun h => ⟨‖h.toLp f‖, ?_⟩, fun ⟨C, hC⟩ => memLp_top_of_bound hf C hC⟩,
    fun f => ?_⟩
  · filter_upwards [Lp.ae_norm_le_norm_top (h.toLp f), h.coeFn_toLp] with x hx hx'
    rw [← Real.norm_eq_abs, ← hx']
    exact hx
  · rcases eq_or_ne μ 0 with rfl | hμ
    · -- on the zero measure every constant works and both sides are `0`
      have h1 : {C : ℝ | ∀ᵐ x ∂(0 : Measure α), |f x| ≤ C} = Set.univ :=
        Set.eq_univ_of_forall fun C => by simp
      rw [h1, Real.sInf_of_not_bddBelow (not_bddBelow_univ (α := ℝ)), Lp.norm_def]
      simp
    · refine (IsLeast.csInf_eq ⟨?_, fun C hC => ?_⟩).symm
      · simpa only [Set.mem_ofPred_eq, Real.norm_eq_abs] using Lp.ae_norm_le_norm_top f
      · rw [Set.mem_ofPred_eq] at hC
        by_cases hC0 : 0 ≤ C
        · rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable f),
            ← ENNReal.toReal_ofReal hC0]
          refine ENNReal.toReal_mono ENNReal.ofReal_ne_top ?_
          exact eLpNormEssSup_le_of_ae_bound (by simpa only [Real.norm_eq_abs] using hC)
        · exfalso
          have : ∀ᵐ x ∂μ, False := hC.mono fun x hx => hC0 ((abs_nonneg _).trans hx)
          rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at this
          exact hμ this

/-- **Remark 1** in Chapter 4 of [brezis2011functional]. For $f \in L^\infty(\Omega)$,
$|f(x)| \le \|f\|_\infty$ for a.e. $x \in \Omega$.

**Generalization.** The bound holds for any measure. -/
theorem remark_4_1 (f : Lp ℝ ∞ μ) : ∀ᵐ x ∂μ, |f x| ≤ ‖f‖ := by
  simpa only [Real.norm_eq_abs] using Lp.ae_norm_le_norm_top f

/-! ### Hölder's inequality -/

/-- **Theorem 4.6** of [brezis2011functional] (Hölder's inequality). Let $1 \le p \le \infty$ and
let $p'$ be the conjugate exponent, $1/p + 1/p' = 1$. Let $f \in L^p(\Omega)$ and
$g \in L^{p'}(\Omega)$. Then $fg$ is integrable and
$$\int_\Omega |fg| \, d\mu \le \|f\|_p \|g\|_{p'}.$$

The conjugate exponent $p'$ is `q`. The norms are the real parts of `eLpNorm`, which are finite
here.

**Generalization.** The theorem allows arbitrary measures. -/
theorem theorem_4_6 {p q : ℝ≥0∞} [p.HolderConjugate q] {f g : α → ℝ} (hf : MemLp f p μ)
    (hg : MemLp g q μ) :
    Integrable (f * g) μ ∧
      ∫ x, |f x * g x| ∂μ ≤ (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal := by
  refine ⟨hf.integrable_mul hg, ?_⟩
  have hfg : AEStronglyMeasurable (f * g) μ := hf.aestronglyMeasurable.mul hg.aestronglyMeasurable
  have h : eLpNorm (f * g) 1 μ ≤ eLpNorm f p μ * eLpNorm g q μ := by
    have := eLpNorm_smul_le_mul_eLpNorm_of_pos (φ := f) (f := g) (μ := μ) (r := 1) (p := p)
      (q := q) one_pos
    rwa [show f • g = f * g from funext fun x => smul_eq_mul _ _] at this
  calc ∫ x, |f x * g x| ∂μ = ∫ x, ‖(f * g) x‖ ∂μ := by simp only [Real.norm_eq_abs, Pi.mul_apply]
    _ = (eLpNorm (f * g) 1 μ).toReal := by
        rw [integral_norm_eq_lintegral_enorm hfg, eLpNorm_one_eq_lintegral_enorm hfg]
    _ ≤ (eLpNorm f p μ * eLpNorm g q μ).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top) h
    _ = (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal := ENNReal.toReal_mul

/-- **Remark 2** in Chapter 4 of [brezis2011functional].

1. The Hölder inequality for several functions. Let $f_i \in L^{p_i}(\Omega)$ for $i$ in a
   finite index set $s$, and let $1/r = \sum_{i \in s} 1/p_i$ with $r \ge 1$. Then
   $f = \prod_{i \in s} f_i$ belongs to $L^r(\Omega)$ and
$$\|f\|_r \le \prod_{i \in s} \|f_i\|_{p_i}.$$
2. The interpolation inequality. Let $1 \le p \le r \le q \le \infty$ and
   $f \in L^p(\Omega) \cap L^q(\Omega)$, and let $0 \le \alpha \le 1$ with
   $1/r = \alpha/p + (1 - \alpha)/q$. Then $f \in L^r(\Omega)$ and
$$\|f\|_r \le \|f\|_p^\alpha \|f\|_q^{1 - \alpha}.$$

The exponents are in $[1, +\infty]$, and the norms are `eLpNorm`, with values in $[0, +\infty]$.
The source writes $1/p = 1/p_1 + \dots + 1/p_k \le 1$; the condition $r \ge 1$ is the same. In
(2) the number $\alpha$ is `θ`. The proofs are in
`Numlib.MeasureTheory.Function.LpInterpolation`.

**Generalization.** The inequalities hold for any measure, and the indexed product can be empty. -/
theorem remark_4_2 :
    (∀ {ι : Type*} (s : Finset ι) (f : ι → α → ℝ) (p : ι → ℝ≥0∞) (r : ℝ≥0∞),
      (∀ i ∈ s, MemLp (f i) (p i) μ) → r⁻¹ = ∑ i ∈ s, (p i)⁻¹ → 1 ≤ r →
        MemLp (∏ i ∈ s, f i) r μ ∧
          eLpNorm (∏ i ∈ s, f i) r μ ≤ ∏ i ∈ s, eLpNorm (f i) (p i) μ) ∧
    ∀ (f : α → ℝ) (p q r : ℝ≥0∞) (θ : ℝ), 1 ≤ p → p ≤ r → r ≤ q → MemLp f p μ → MemLp f q μ →
      0 ≤ θ → θ ≤ 1 → r⁻¹ = ENNReal.ofReal θ * p⁻¹ + ENNReal.ofReal (1 - θ) * q⁻¹ →
        MemLp f r μ ∧ eLpNorm f r μ ≤ eLpNorm f p μ ^ θ * eLpNorm f q μ ^ (1 - θ) := by
  refine ⟨fun s f p r hf hr _ => ?_, fun f p q r θ hp hpr hrq hfp hfq hθ₀ hθ₁ hr => ?_⟩
  · have h := eLpNorm_finset_prod_le (fun i hi => (hf i hi).aestronglyMeasurable) hr
    refine ⟨memLp_iff.2 (h.trans_lt (ENNReal.prod_lt_top fun i hi => (hf i hi).eLpNorm_lt_top)), h⟩
  · exact ⟨hfp.interpolate (zero_lt_one.trans_le hp).ne' hfq hpr hrq,
      eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow hfp.aestronglyMeasurable hθ₀ hθ₁ hr⟩

/-! ### $L^p$ is a Banach space -/

/-- **Theorem 4.7** of [brezis2011functional]. Let $1 \le p \le \infty$. Then $L^p(\Omega)$ is a
vector space and $\|\cdot\|_p$ is a norm on it. Precisely:

1. if $f, g \in L^p$, then $f + g \in L^p$;
2. if $f \in L^p$ and $c \in \mathbb{R}$, then $cf \in L^p$;
3. $\|f + g\|_p \le \|f\|_p + \|g\|_p$ (Minkowski's inequality);
4. $\|cf\|_p = |c| \|f\|_p$;
5. $\|f\|_p = 0$ if and only if $f = 0$.

Parts (1) and (2) are about functions, with `MemLp`. Parts (3) to (5) are about elements of
`MeasureTheory.Lp ℝ p μ`, that is, classes of a.e. equal functions.

**Generalization.** The theorem allows arbitrary measures. -/
theorem theorem_4_7 {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    (∀ f g : α → ℝ, MemLp f p μ → MemLp g p μ → MemLp (f + g) p μ) ∧
    (∀ (c : ℝ) (f : α → ℝ), MemLp f p μ → MemLp (c • f) p μ) ∧
    (∀ f g : Lp ℝ p μ, ‖f + g‖ ≤ ‖f‖ + ‖g‖) ∧
    (∀ (c : ℝ) (f : Lp ℝ p μ), ‖c • f‖ = |c| * ‖f‖) ∧
    ∀ f : Lp ℝ p μ, ‖f‖ = 0 ↔ f = 0 :=
  ⟨fun _ _ hf hg => hf.add hg, fun c _ hf => hf.const_smul c, fun f g => norm_add_le f g,
    fun c f => by rw [norm_smul, Real.norm_eq_abs], fun f => norm_eq_zero⟩

/-- **Theorem 4.8** of [brezis2011functional] (Fischer–Riesz). Let $1 \le p \le \infty$. Then
$L^p(\Omega)$ is a Banach space.

**Generalization.** The theorem allows arbitrary measures. -/
theorem theorem_4_8 {p : ℝ≥0∞} [Fact (1 ≤ p)] : CompleteSpace (Lp ℝ p μ) := inferInstance

/-- **Theorem 4.9** of [brezis2011functional]. Let $1 \le p \le \infty$, and let $(f_n)$ be a
sequence in $L^p(\Omega)$ with $f_n \to f$ in $L^p(\Omega)$. Then there are a subsequence
$(f_{n_k})$ and a function $h \in L^p(\Omega)$ such that

1. $f_{n_k}(x) \to f(x)$ for a.e. $x \in \Omega$, and
2. $|f_{n_k}(x)| \le h(x)$ for every $k$ and a.e. $x \in \Omega$.

The limit is `g` in the Lean statement, and the subsequence is `f ∘ ns` with `ns` strictly
increasing.

**Generalization.** The theorem allows arbitrary measures. -/
theorem theorem_4_9 {p : ℝ≥0∞} [Fact (1 ≤ p)] {f : ℕ → Lp ℝ p μ} {g : Lp ℝ p μ}
    (hfg : Tendsto f atTop (𝓝 g)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ h : Lp ℝ p μ,
      (∀ᵐ x ∂μ, Tendsto (fun k => f (ns k) x) atTop (𝓝 (g x))) ∧
        ∀ k, ∀ᵐ x ∂μ, |f (ns k) x| ≤ h x := by
  obtain ⟨ns, hns, h, h1, h2⟩ := Lp.exists_subseq_tendsto_ae_ae_le_of_tendsto hfg
  exact ⟨ns, hns, h, h1, fun k => by simpa only [Real.norm_eq_abs] using h2 k⟩

end Brezis.Chapter04
