/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw

/-!
# Monte Carlo integration

Monte Carlo integration estimates an integral by an average of random samples
([quarteroni2000numerical], §9.9.3). Let $\Omega \subseteq \mathbb{R}^d$ be measurable with
$0 < |\Omega| < \infty$. Then $\int_\Omega f$ is $|\Omega|$ times the mean of $f(X)$ for a random
variable $X$ with the uniform distribution on $\Omega$. For samples $X_0, X_1, \dots$ that are
pairwise independent and identically distributed, the sample mean
$$I_N(f) = \frac{1}{N} \sum_{i<N} f(X_i)$$
converges to the mean of $f(X_0)$ almost surely, and its variance is
$\operatorname{Var}(f(X_0)) / N$. Chebyshev's inequality then gives a confidence bound of order
$N^{-1/2}$. No estimate depends on the dimension $d$, which is the point of the method.

## Main definitions

* `MonteCarlo.sampleMean`: the Monte Carlo estimate $I_N(f)$ of (9.60) of [quarteroni2000numerical].

## Main results

* `MonteCarlo.setIntegral_eq_volume_mul_integral_cond`: $\int_\Omega f = |\Omega|$ times the mean of
  $f$ for the uniform distribution on $\Omega$.
* `MonteCarlo.tendsto_sampleMean_ae`: the strong law of large numbers for the sample mean.
* `MonteCarlo.integral_sampleMean`: the sample mean is unbiased.
* `MonteCarlo.variance_sampleMean`: $\operatorname{Var}(I_N(f)) = \operatorname{Var}(f(X_0)) / N$,
  which is (9.61) of [quarteroni2000numerical].
* `MonteCarlo.meas_ge_le_sampleMean`: Chebyshev's bound $\mu\{|I_N(f) - E f(X_0)| \ge c\} \le
  \operatorname{Var}(f(X_0)) / (N c^2)$.

## Implementation notes

* The samples are random variables $X_i \colon \Omega \to \mathbb{R}^d$ on an abstract measure space
  $(\Omega, \mu)$, where $\mathbb{R}^d$ is `Fin d → ℝ`. The identification of the mean of $f(X_0)$
  with $|\Omega|^{-1} \int_\Omega f$ is the separate result
  `MonteCarlo.setIntegral_eq_volume_mul_integral_cond`. It applies when the distribution of $X_0$ is
  the uniform distribution on $\Omega$.
* The uniform distribution on a set $s$ is Mathlib's conditional measure `volume[|s]`
  (`ProbabilityTheory.cond`), which is $|s|^{-1}$ times the restriction of the Lebesgue measure to
  $s$.
* Only `MonteCarlo.meas_ge_le_sampleMean` assumes that $\mu$ is a probability measure. The other
  results are stated for every measure $\mu$, as Mathlib's `ProbabilityTheory.strong_law_ae` and
  `ProbabilityTheory.IndepFun.variance_sum` are.
* The strong law is Mathlib's `ProbabilityTheory.strong_law_ae`, applied to the sequence
  $f \circ X_i$. It is the version of Etemadi, for which pairwise independence suffices.
-/

open MeasureTheory ProbabilityTheory Filter Topology Function

namespace MonteCarlo

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : ℕ}

/-- The **sample mean** of the Monte Carlo method ([quarteroni2000numerical], (9.60)). For an
integrand $f \colon \mathbb{R}^d \to \mathbb{R}$, samples $X_i \colon \Omega \to \mathbb{R}^d$,
$i \in \mathbb{N}$, and $N \in \mathbb{N}$, it is the function
$$I_N(f)(\omega) = \frac{1}{N} \sum_{i<N} f(X_i(\omega)).$$

For $N = 0$ the value is $0$, since $0^{-1} = 0$ in Lean. -/
noncomputable def sampleMean (f : (Fin d → ℝ) → ℝ) (X : ℕ → Ω → (Fin d → ℝ)) (N : ℕ) (ω : Ω) :
    ℝ :=
  (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, f (X i ω)

omit [MeasurableSpace Ω] in
/-- The sample mean is the function $I_N(f) = N^{-1} \sum_{i<N} f \circ X_i$. -/
theorem sampleMean_eq (f : (Fin d → ℝ) → ℝ) (X : ℕ → Ω → (Fin d → ℝ)) (N : ℕ) :
    sampleMean f X N = (N : ℝ)⁻¹ • ∑ i ∈ Finset.range N, f ∘ X i := by
  funext ω
  simp [sampleMean]

/-- The **integral as a mean value** ([quarteroni2000numerical], §9.9.3). Let
$s \subseteq \mathbb{R}^d$ with $0 < |s| < \infty$, where $|s|$ is the Lebesgue measure of $s$,
and let $f \colon \mathbb{R}^d \to \mathbb{R}$. Then
$$\int_s f(x) \, dx = |s| \int f \, d\nu_s,$$
where $\nu_s$ is the uniform distribution on $s$. The second factor is the mean of $f(X)$ for a
random variable $X$ with the uniform distribution on $s$, which has the density
$|s|^{-1} \chi_s$.

The uniform distribution $\nu_s$ is the conditional measure `volume[|s]`, which is $|s|^{-1}$
times the restriction of the Lebesgue measure to $s$. The set $s$ need not be measurable. -/
theorem setIntegral_eq_volume_mul_integral_cond {s : Set (Fin d → ℝ)} (h0 : volume s ≠ 0)
    (htop : volume s ≠ ⊤) (f : (Fin d → ℝ) → ℝ) :
    ∫ x in s, f x = (volume s).toReal * ∫ x, f x ∂(volume[|s]) := by
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ (ENNReal.toReal_ne_zero.2 ⟨h0, htop⟩), one_mul]

/-- The **strong law of large numbers for Monte Carlo integration** ([quarteroni2000numerical],
§9.9.3). Let $(\Omega, \mu)$ be a measure space, let $f \colon \mathbb{R}^d \to \mathbb{R}$ be
measurable, and let $X_i \colon \Omega \to \mathbb{R}^d$, $i \in \mathbb{N}$, be pairwise
independent and identically distributed, with $f(X_0)$ integrable. Then for $\mu$-almost every
$\omega$,
$$I_N(f)(\omega) \to E[f(X_0)] \quad \text{as } N \to \infty.$$

The mean $E[f(X_0)]$ is the integral of $f \circ X_0$ with respect to $\mu$. The proof applies
Mathlib's `ProbabilityTheory.strong_law_ae` to the sequence $f \circ X_i$. -/
theorem tendsto_sampleMean_ae (f : (Fin d → ℝ) → ℝ) (hf : Measurable f)
    (X : ℕ → Ω → (Fin d → ℝ)) (hint : Integrable (f ∘ X 0) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun N => sampleMean f X N ω) atTop (𝓝 (μ[f ∘ X 0])) := by
  have h := strong_law_ae (μ := μ) (fun i => f ∘ X i) hint
    (fun i j hij => (hindep hij).comp hf hf) (fun i => (hident i).comp hf)
  filter_upwards [h] with ω hω
  simpa [sampleMean] using hω

section Variance

variable {f : (Fin d → ℝ) → ℝ} {X : ℕ → Ω → (Fin d → ℝ)}

/-- The **sample mean is unbiased**. Let $(\Omega, \mu)$ be a measure space, let
$f \colon \mathbb{R}^d \to \mathbb{R}$ be measurable, and let
$X_i \colon \Omega \to \mathbb{R}^d$ be identically distributed, with $f(X_0)$ integrable. Then
for $N \ge 1$,
$$E[I_N(f)] = E[f(X_0)].$$
-/
theorem integral_sampleMean (hf : Measurable f)
    (hint : Integrable (f ∘ X 0) μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) {N : ℕ} (hN : 0 < N) :
    μ[sampleMean f X N] = μ[f ∘ X 0] := by
  have hint' : ∀ i, Integrable (f ∘ X i) μ := fun i =>
    ((hident i).comp hf).symm.integrable_snd hint
  rw [sampleMean_eq]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [integral_const_mul, integral_finsetSum _ fun i _ => hint' i]
  rw [Finset.sum_congr rfl fun i _ => ((hident i).comp hf).integral_eq, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), one_mul]

/-- **Equation (9.61)** of [quarteroni2000numerical]. Let $(\Omega, \mu)$ be a measure space, let
$f \colon \mathbb{R}^d \to \mathbb{R}$ be measurable, and let
$X_i \colon \Omega \to \mathbb{R}^d$ be pairwise independent and identically distributed, with
$f(X_0) \in L^2$. Then for $N \ge 1$,
$$\operatorname{Var}(I_N(f)) = \frac{\operatorname{Var}(f(X_0))}{N}.$$
So the standard deviation of $I_N(f)$ is $\sigma(f) / \sqrt{N}$, and the statistical error is
$O(N^{-1/2})$ in every dimension.

The proof uses `ProbabilityTheory.IndepFun.variance_sum` and `ProbabilityTheory.variance_smul`.
The variances of the terms are equal because the samples are identically distributed. -/
theorem variance_sampleMean (hf : Measurable f) (hL2 : MemLp (f ∘ X 0) 2 μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    {N : ℕ} (hN : 0 < N) :
    variance (sampleMean f X N) μ = variance (f ∘ X 0) μ / N := by
  have hL2' : ∀ i, MemLp (f ∘ X i) 2 μ := fun i => ((hident i).comp hf).symm.memLp_snd hL2
  rw [sampleMean_eq, variance_smul, IndepFun.variance_sum (fun i _ => hL2' i)
    (fun i _ j _ hij => (hindep hij).comp hf hf)]
  rw [Finset.sum_congr rfl fun i _ => ((hident i).comp hf).variance_eq, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  field_simp

/-- **Chebyshev's inequality for the Monte Carlo error**. Let $(\Omega, \mu)$ be a probability
space, let $f \colon \mathbb{R}^d \to \mathbb{R}$ be measurable, and let
$X_i \colon \Omega \to \mathbb{R}^d$ be pairwise independent and identically distributed, with
$f(X_0) \in L^2$. Then for $N \ge 1$ and $c > 0$,
$$\mu\bigl\{\omega : |I_N(f)(\omega) - E[f(X_0)]| \ge c\bigr\} \le
  \frac{\operatorname{Var}(f(X_0))}{N c^2}.$$
This is the statistical error of order $N^{-1/2}$ that [quarteroni2000numerical] reads off
(9.61).

The proof applies `ProbabilityTheory.meas_ge_le_variance_div_sq` to the sample mean, whose mean
is $E[f(X_0)]$ by `MonteCarlo.integral_sampleMean` and whose variance is
$\operatorname{Var}(f(X_0)) / N$ by `MonteCarlo.variance_sampleMean`. -/
theorem meas_ge_le_sampleMean [IsProbabilityMeasure μ] (hf : Measurable f)
    (hL2 : MemLp (f ∘ X 0) 2 μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    {N : ℕ} (hN : 0 < N) {c : ℝ} (hc : 0 < c) :
    μ {ω | c ≤ |sampleMean f X N ω - μ[f ∘ X 0]|}
      ≤ ENNReal.ofReal (variance (f ∘ X 0) μ / (N * c ^ 2)) := by
  have hL2' : ∀ i, MemLp (f ∘ X i) 2 μ := fun i => ((hident i).comp hf).symm.memLp_snd hL2
  have hmem : MemLp (sampleMean f X N) 2 μ := by
    rw [sampleMean_eq]
    exact (memLp_finsetSum' _ fun i _ => hL2' i).const_smul _
  have h := meas_ge_le_variance_div_sq hmem hc
  rw [integral_sampleMean hf (hL2.integrable one_le_two) hident hN] at h
  refine h.trans (le_of_eq ?_)
  rw [variance_sampleMean hf hL2 hindep hident hN, div_div]

end Variance

end MonteCarlo
