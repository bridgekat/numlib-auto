import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw

/-!
# Monte Carlo integration

Monte Carlo integration ([quarteroni2000numerical] §9.9.3): the integral over a measurable
`Ω ⊆ ℝ^d` of positive finite volume is `|Ω|` times the mean of `f(X)` for `X` uniform on `Ω`, the
uniform law being Mathlib's conditional measure `volume[|Ω]` (`ProbabilityTheory.cond`); the
sample mean `I_N(f) = (1/N) ∑_{i<N} f(X_i)` of pairwise independent identically distributed samples
converges to the mean almost surely — Mathlib's strong law `ProbabilityTheory.strong_law_ae`
(Etemadi's version, pairwise independence suffices) applied to `f ∘ X_i` — and its variance is
`Var(f(X))/N`, so that Chebyshev's inequality gives the `N^{-1/2}` confidence bound. Nothing is
dimension-dependent, which is the book's point.

## Main definitions

* `MonteCarlo.sampleMean f X N` — the Monte Carlo estimate `I_N(f)` of (9.60).

## Main results

* `MonteCarlo.setIntegral_eq_volume_mul_integral_cond` — `∫_Ω f = |Ω| ∫ f d(volume[|Ω])`, the
  integral as `|Ω|` times a mean value.
* `MonteCarlo.tendsto_sampleMean_ae` — the strong law of large numbers for the sample mean.
* `MonteCarlo.integral_sampleMean`, `MonteCarlo.variance_sampleMean` — the sample mean is
  unbiased and `Var(I_N(f)) = Var(f(X))/N` (9.61).
* `MonteCarlo.meas_ge_le_sampleMean` — Chebyshev's bound
  `μ{|I_N(f) - E f(X)| ≥ c} ≤ Var(f(X))/(N c²)`.

Everything is stated on an abstract probability space `(Ω, μ)` with samples
`X i : Ω → (Fin d → ℝ)`; the identification of `μ[f ∘ X 0]` with `|Ω|⁻¹ ∫_Ω f` is the separate
lemma `setIntegral_eq_volume_mul_integral_cond`, under the hypothesis that the law of `X 0` is
`volume[|Ω]`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Function

namespace MonteCarlo

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : ℕ}

/-- **The sample mean** `I_N(f) = (1/N) ∑_{i<N} f(X_i)` of the Monte Carlo method, for an
integrand `f` on `ℝ^d` and samples `X : ℕ → Ω → ℝ^d`.

Reference: [quarteroni2000numerical], (9.60). -/
noncomputable def sampleMean (f : (Fin d → ℝ) → ℝ) (X : ℕ → Ω → (Fin d → ℝ)) (N : ℕ) (ω : Ω) :
    ℝ :=
  (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, f (X i ω)

omit [MeasurableSpace Ω] in
/-- The sample mean as a scalar multiple of a finite sum of the functions `f ∘ X i`. -/
theorem sampleMean_eq (f : (Fin d → ℝ) → ℝ) (X : ℕ → Ω → (Fin d → ℝ)) (N : ℕ) :
    sampleMean f X N = (N : ℝ)⁻¹ • ∑ i ∈ Finset.range N, f ∘ X i := by
  funext ω
  simp [sampleMean]

/-- **The integral as a mean value** ([quarteroni2000numerical] §9.9.3, first display): for `s`
measurable with `0 < |s| < ∞`, `∫_s f = |s| ∫ f d(volume[|s])`, the second factor being the mean
of `f(X)` for `X` uniform on `s` (density `|s|⁻¹ χ_s`). The conditional measure is
`|s|⁻¹ • volume.restrict s`. -/
theorem setIntegral_eq_volume_mul_integral_cond {s : Set (Fin d → ℝ)} (h0 : volume s ≠ 0)
    (htop : volume s ≠ ⊤) (f : (Fin d → ℝ) → ℝ) :
    ∫ x in s, f x = (volume s).toReal * ∫ x, f x ∂(volume[|s]) := by
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ (ENNReal.toReal_ne_zero.2 ⟨h0, htop⟩), one_mul]

/-- **The strong law of large numbers for Monte Carlo integration**
([quarteroni2000numerical] §9.9.3): for measurable `f`, samples `X` with `f(X 0)` integrable,
pairwise independent and identically distributed, the sample mean `I_N(f)` converges almost
surely to the mean `E[f(X 0)]` as `N → ∞`. Mathlib's `ProbabilityTheory.strong_law_ae` applied
to the sequence `f ∘ X i`. -/
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

/-- **The sample mean is unbiased**: `E[I_N(f)] = E[f(X 0)]` for identically distributed
integrable samples and `N ≥ 1`. -/
theorem integral_sampleMean [IsProbabilityMeasure μ] (hf : Measurable f)
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

/-- **(9.61)**: for pairwise independent identically distributed samples with `f(X 0) ∈ L²`,
`Var(I_N(f)) = Var(f(X 0))/N` for `N ≥ 1`, i.e. `σ(I_N(f)) = σ(f)/√N` — the statistical error
is `O(N^{-1/2})`, whatever the dimension. `ProbabilityTheory.IndepFun.variance_sum` and
`ProbabilityTheory.variance_smul`, the variances of the terms being equal by identical
distribution.

Reference: [quarteroni2000numerical], (9.61). -/
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

/-- **Chebyshev's inequality for the Monte Carlo error**: under the hypotheses of
`variance_sampleMean`, for `c > 0`,
`μ{ω : |I_N(f)(ω) - E[f(X 0)]| ≥ c} ≤ Var(f(X 0))/(N c²)` — the `O(N^{-1/2})` statistical error
the book reads off (9.61). `ProbabilityTheory.meas_ge_le_variance_div_sq` for the sample mean,
whose mean is `E[f(X 0)]` and whose variance is `Var(f(X 0))/N`. -/
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
