/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside Mathlib's Bessel potential spaces.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Convolution.Lp
import Numlib.Analysis.Sobolev.Tempered

/-!
# The Fourier characterization of `H^s` on the whole space

For an `L²` function `v` on a finite-dimensional real inner product space `E` and `s ≥ 0`, the
Bessel potential space `H^s(E)` of Mathlib (`TemperedDistribution.MemSobolev s 2`) is described
on the Fourier side: `v ∈ H^s(E)` exactly when `(1 + |ξ|²)^{s/2} ℱv ∈ L²(E)`, and then the `L²`
norm of the Bessel potential of `v` *is* `‖(1 + |ξ|²)^{s/2} ℱv‖_{L²}`. At an integer order `k`
the Sobolev norm `[∑_{|α| ≤ k} ‖∂^α v‖²_{L²}]^{1/2}` of the weak derivatives in an orthonormal
basis `b` is equivalent to that Fourier norm.

## Main statements

* `TemperedDistribution.memSobolev_two_iff_memLp_symbol_mul_fourier`: the membership criterion,
  Mathlib's `TemperedDistribution.memSobolev_iff_exists_smulLeftCLM_fourier` with the
  multiplication by the symbol read pointwise on the `L²` representative
  (`MeasureTheory.Lp.ae_eq_symbol_mul_of_smulLeftCLM_eq`; `s ≥ 0` makes the inverse symbol
  bounded).
* `TemperedDistribution.norm_eq_eLpNorm_symbol_mul_fourier_of_besselPotential_eq`: the norm
  identity, by Plancherel.
* `OrthonormalBasis.exists_bounds_rpow_one_add_norm_sq`: the symbol inequality
  `c₁ (∑_{|α| ≤ k} |ξ^α|²)^{1/2} ≤ (1 + |ξ|²)^{k/2} ≤ c₂ (∑_{|α| ≤ k} |ξ^α|²)^{1/2}` for the
  monomials `ξ^α = ∏ᵢ ⟪ξ, bᵢ⟫^{αᵢ}` (`OrthonormalBasis.coordMonomial`). The lower bound needs no
  multinomial expansion, only a coordinate of largest absolute value.
* `OrthonormalBasis.exists_norm_equiv_eLpNorm_symbol_mul_fourier`: the norm equivalence. The
  Fourier transform of a weak derivative is `ℱ(∂^α v) = (2πiξ)^α ℱv` (`fourier_weakDeriv_aeEq`),
  so Plancherel turns `∑_{|α| ≤ k} ‖∂^α v‖²_{L²}` into `∫ (∑_{|α| ≤ k} (2π)^{2|α|} |ξ^α|²) |ℱv|²`
  (`OrthonormalBasis.sq_eLpNorm_sum_eq_lintegral`), and the symbol inequality compares this with
  `∫ (1 + |ξ|²)^k |ℱv|²`.

## References

[han2009theoretical], §7.4: Theorem 7.4.1, the display (7.4.2) defining `H^s(ℝ^d)`, the norm
equivalence (7.4.1) and Exercise 7.4.2.
-/

open FourierTransform LineDeriv MeasureTheory TemperedDistribution TopologicalSpace

open scoped ENNReal NNReal RealInnerProductSpace SchwartzMap

noncomputable section

/-! ### Multiplying an `L²` function by the symbol `(1 + |ξ|²)^{s/2}` -/

section Symbol

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The symbol `(1 + |ξ|^2)^{s/2}` has temperate growth. -/
private theorem hasTemperateGrowth_symbol (s : ℝ) :
    (fun ξ : E ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop

/-- **Reading the symbol off the `L²` representative.** If an `L²` function `w` is, as a tempered
distribution, the product of the symbol `(1 + |ξ|²)^{s/2}` with an `L²` function `u`, and
`s ≥ 0`, then `w` is that product almost everywhere. The hypothesis `s ≥ 0` is what makes the
inverse symbol `(1 + |ξ|²)^{-s/2}` bounded, so that multiplying the identity by it stays inside
`L²`. -/
theorem MeasureTheory.Lp.ae_eq_symbol_mul_of_smulLeftCLM_eq {s : ℝ} (hs : 0 ≤ s)
    {u w : Lp ℂ 2 (volume : Measure E)}
    (h : smulLeftCLM ℂ (fun ξ : E ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) (u : 𝓢'(E, ℂ)) =
      (w : 𝓢'(E, ℂ))) :
    (w : E → ℂ) =ᵐ[volume] fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * (u : E → ℂ) ξ := by
  set g : E → ℂ := fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) with hgdef
  set g' : E → ℂ := fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ) with hg'def
  have hpos : ∀ ξ : E, (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := fun ξ ↦ by positivity
  have hg : g.HasTemperateGrowth := hasTemperateGrowth_symbol s
  have hg' : g'.HasTemperateGrowth := hasTemperateGrowth_symbol (-s)
  have hmul : ∀ ξ : E, g ξ * g' ξ = 1 := by
    intro ξ
    simp only [hgdef, hg'def, ← Complex.ofReal_mul, ← Real.rpow_add (hpos ξ)]
    rw [show s / 2 + -s / 2 = (0 : ℝ) by ring, Real.rpow_zero, Complex.ofReal_one]
  have hbdd : ∀ ξ : E, ‖g' ξ‖ ≤ 1 := by
    intro ξ
    simp only [hg'def, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (hpos ξ).le _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [norm_nonneg ξ]) (by linarith)
  have hb : MemLp (fun ξ ↦ g' ξ * (w : E → ℂ) ξ) 2 (volume : Measure E) := by
    refine (Lp.memLp w).mono (hg'.1.continuous.aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable w)) ?_
    filter_upwards with ξ
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hbdd ξ)
  have hu : (hb.toLp _ : 𝓢'(E, ℂ)) = (u : 𝓢'(E, ℂ)) := by
    rw [toTemperedDistribution_eq_smulLeftCLM hg' hb.coeFn_toLp, ← h,
      smulLeftCLM_smulLeftCLM_apply hg hg', show g * g' = fun _ : E ↦ (1 : ℂ) from funext hmul,
      smulLeftCLM_const, one_smul]
  have hinj : Function.Injective (Lp.toTemperedDistributionCLM ℂ (volume : Measure E) 2) :=
    LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot
  have hueq : hb.toLp _ = u := hinj hu
  have huae : (u : E → ℂ) =ᵐ[volume] fun ξ ↦ g' ξ * (w : E → ℂ) ξ := by
    rw [← hueq]; exact hb.coeFn_toLp
  filter_upwards [huae] with ξ hξ
  rw [hξ, ← mul_assoc, hmul ξ, one_mul]

/-- **The Fourier characterization of `H^s` for `s ≥ 0`**: an `L²` function `v` lies in the
Bessel potential space of order `s` exactly when `(1 + |ξ|²)^{s/2} ℱv` lies in `L²`, where `ℱv` is
the `L²` Fourier transform of `v`.

This is `TemperedDistribution.memSobolev_iff_exists_smulLeftCLM_fourier` with the multiplication by
the symbol made concrete: Mathlib states it as an equality of tempered distributions, and here the
`L²` representative is identified pointwise almost everywhere. -/
theorem TemperedDistribution.memSobolev_two_iff_memLp_symbol_mul_fourier {s : ℝ} (hs : 0 ≤ s)
    (v : Lp ℂ 2 (volume : Measure E)) :
    MemSobolev s 2 (v : 𝓢'(E, ℂ)) ↔
      MemLp (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * (𝓕 v) ξ) 2
        (volume : Measure E) := by
  rw [memSobolev_iff_exists_smulLeftCLM_fourier, Lp.fourier_toTemperedDistribution_eq]
  refine ⟨fun ⟨w, hw⟩ ↦ (Lp.memLp w).ae_eq (Lp.ae_eq_symbol_mul_of_smulLeftCLM_eq hs hw),
    fun hm ↦ ⟨hm.toLp _, ?_⟩⟩
  exact (toTemperedDistribution_eq_smulLeftCLM (hasTemperateGrowth_symbol s) hm.coeFn_toLp).symm

/-- **The Fourier transform of the Bessel potential.** If the Bessel potential of order `s ≥ 0` of
an `L²` function `v` is the `L²` function `w`, then `ℱw = (1 + |ξ|²)^{s/2} ℱv` almost
everywhere. -/
theorem TemperedDistribution.fourier_ae_eq_symbol_mul_fourier_of_besselPotential_eq {s : ℝ}
    (hs : 0 ≤ s) {v w : Lp ℂ 2 (volume : Measure E)}
    (hw : besselPotential E ℂ s (v : 𝓢'(E, ℂ)) = (w : 𝓢'(E, ℂ))) :
    ((𝓕 w : Lp ℂ 2 (volume : Measure E)) : E → ℂ) =ᵐ[volume]
      fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * (𝓕 v) ξ := by
  refine Lp.ae_eq_symbol_mul_of_smulLeftCLM_eq hs ?_
  rw [← Lp.fourier_toTemperedDistribution_eq, ← Lp.fourier_toTemperedDistribution_eq, ← hw,
    fourier_besselPotential_eq_smulLeftCLM_fourier_apply]

/-- **The `H^s` norm on the Fourier side**: if the Bessel potential of order `s ≥ 0` of an `L²`
function `v` is the `L²` function `w`, so that `‖w‖_{L²}` is the norm of `v` in `H^s`, then
`‖w‖_{L²} = ‖(1 + |ξ|²)^{s/2} ℱv‖_{L²}`, by Plancherel. -/
theorem TemperedDistribution.norm_eq_eLpNorm_symbol_mul_fourier_of_besselPotential_eq {s : ℝ}
    (hs : 0 ≤ s) {v w : Lp ℂ 2 (volume : Measure E)}
    (hw : besselPotential E ℂ s (v : 𝓢'(E, ℂ)) = (w : 𝓢'(E, ℂ))) :
    ‖w‖ = (eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * (𝓕 v) ξ) 2 volume).toReal := by
  rw [← Lp.norm_fourier_eq w, Lp.norm_def]
  exact congrArg ENNReal.toReal
    (eLpNorm_congr_ae (fourier_ae_eq_symbol_mul_fourier_of_besselPotential_eq hs hw))

/-- **The derivatives of order at most `k` of an element of `H^k` are `L²` functions**: Mathlib's
`TemperedDistribution.MemSobolev.lineDerivOp`, iterated
(`TemperedDistribution.MemSobolev.iteratedLineDerivOp`), at the order `0 ≤ k - n`. -/
theorem TemperedDistribution.MemSobolev.exists_iteratedLineDerivOp_eq {k n : ℕ} (hn : n ≤ k)
    {f : 𝓢'(E, ℂ)} (hf : MemSobolev (k : ℝ) 2 f) (m : Fin n → E) :
    ∃ w : Lp ℂ 2 (volume : Measure E), (∂^{m} f) = (w : 𝓢'(E, ℂ)) :=
  memSobolev_zero_iff.1 <| (hf.iteratedLineDerivOp n m).mono <| by
    have : (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast hn
    linarith

/-- Plancherel's identity in the form of `eLpNorm`: the Fourier transform preserves the `L²`
seminorm of the representative. -/
theorem MeasureTheory.Lp.eLpNorm_fourier_eq (w : Lp ℂ 2 (volume : Measure E)) :
    eLpNorm ((𝓕 w : Lp ℂ 2 (volume : Measure E)) : E → ℂ) 2 volume
      = eLpNorm (w : E → ℂ) 2 volume := by
  have h := Lp.norm_fourier_eq w
  rw [Lp.norm_def, Lp.norm_def] at h
  exact (ENNReal.toReal_eq_toReal_iff' (Lp.eLpNorm_ne_top _) (Lp.eLpNorm_ne_top _)).1 h

end Symbol

/-- Complexification preserves the `L^p` norm. -/
theorem MeasureTheory.Lp.norm_ofRealCLM_compLp {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {p : ℝ≥0∞} (f : Lp ℝ p μ) : ‖Complex.ofRealCLM.compLp f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  refine eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) ?_
  filter_upwards [Complex.ofRealCLM.coeFn_compLp f] with x hx
  rw [hx]
  simp

/-! ### Real powers with half-integer exponents -/

/-- `(x ^ (k/2))² = x^k` for `x ≥ 0`. -/
private theorem sq_rpow_half_natCast {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    (x ^ ((k : ℝ) / 2)) ^ 2 = x ^ k := by
  rw [← Real.rpow_natCast (x ^ ((k : ℝ) / 2)) 2, ← Real.rpow_mul hx, div_mul_eq_mul_div,
    mul_comm, mul_div_assoc, show ((2 : ℕ) : ℝ) * ((k : ℝ) / 2) = ((k : ℕ) : ℝ) by
      push_cast; ring, Real.rpow_natCast]

/-- `x ^ (k/2) = √(x^k)` for `x ≥ 0`. -/
private theorem rpow_half_eq_sqrt_pow {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    x ^ ((k : ℝ) / 2) = Real.sqrt (x ^ k) := by
  rw [← sq_rpow_half_natCast hx k, Real.sqrt_sq (Real.rpow_nonneg hx _)]

/-! ### The monomials of an orthonormal basis, and the symbol inequality -/

namespace OrthonormalBasis

section Monomial

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (b : OrthonormalBasis ι ℝ E) {k : ℕ}

/-- The monomial `ξ^α = ∏ᵢ ⟪ξ, bᵢ⟫^{αᵢ}` of the multi-index `α` in the coordinates of the
orthonormal basis `b`. -/
def coordMonomial (α : ι → ℕ) (ξ : E) : ℝ := ∏ i, ⟪ξ, b i⟫ ^ α i

/-- `ξ^α` is continuous in `ξ`. -/
theorem continuous_coordMonomial (α : ι → ℕ) : Continuous (b.coordMonomial α) :=
  continuous_finsetProd _ fun _ _ ↦ (continuous_id.inner continuous_const).pow _

/-- A coordinate in an orthonormal basis is at most the norm. -/
theorem abs_inner_le_norm (ξ : E) (i : ι) : |⟪ξ, b i⟫| ≤ ‖ξ‖ := by
  have h := abs_real_inner_le_norm ξ (b i)
  rwa [b.orthonormal.1 i, mul_one] at h

/-- `|ξ^α|² ≤ (1 + |ξ|²)^{|α|}`, because every coordinate is bounded by the norm. -/
theorem sq_coordMonomial_le (α : ι → ℕ) (ξ : E) :
    b.coordMonomial α ξ ^ 2 ≤ (1 + ‖ξ‖ ^ 2) ^ (∑ i, α i) := by
  rw [coordMonomial, ← Finset.prod_pow, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod₀ (fun i _ ↦ by positivity) fun i _ ↦ ?_
  rw [← pow_mul, mul_comm (α i) 2, pow_mul]
  refine pow_le_pow_left₀ (by positivity) ?_ _
  have := b.abs_inner_le_norm ξ i
  nlinarith [abs_nonneg ⟪ξ, b i⟫, sq_abs ⟪ξ, b i⟫, norm_nonneg ξ]

/-- `|ξ^α|² ≤ (1 + |ξ|²)^k` for `|α| ≤ k`. -/
theorem sq_coordMonomial_le_pow {α : ι → ℕ} (hα : ∑ i, α i ≤ k) (ξ : E) :
    b.coordMonomial α ξ ^ 2 ≤ (1 + ‖ξ‖ ^ 2) ^ k :=
  (b.sq_coordMonomial_le α ξ).trans (pow_le_pow_right₀ (by nlinarith [norm_nonneg ξ]) hα)

/-- `|ξ^α| ≤ (1 + |ξ|²)^{k/2}` for `|α| ≤ k`: the bound that puts `ξ^α ℱv` in `L²` whenever
`(1 + |ξ|²)^{k/2} ℱv` is. -/
theorem abs_coordMonomial_le_rpow {α : ι → ℕ} (hα : ∑ i, α i ≤ k) (ξ : E) :
    |b.coordMonomial α ξ| ≤ (1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) := by
  have hb : (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2 := by positivity
  have h2 : |b.coordMonomial α ξ| ^ 2 ≤ ((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2)) ^ 2 := by
    rw [sq_rpow_half_natCast hb k, sq_abs]
    exact b.sq_coordMonomial_le_pow hα ξ
  exact le_of_pow_le_pow_left₀ two_ne_zero (Real.rpow_nonneg hb _) h2

variable (k) in
/-- The sum `∑_{|α| ≤ k} |ξ^α|²` of the squared monomials of order at most `k`. -/
def sumSqCoordMonomial (ξ : E) : ℝ :=
  ∑ α : MultiIndexLE ι k, b.coordMonomial α.1 ξ ^ 2

/-- The term of `∑_{|α| ≤ k} |ξ^α|²` at `α = 0` is `1`, so the sum is at least `1`. -/
theorem one_le_sumSqCoordMonomial (ξ : E) : 1 ≤ b.sumSqCoordMonomial k ξ := by
  have h0 : b.coordMonomial (0 : MultiIndexLE ι k).1 ξ ^ 2 = 1 := by simp [coordMonomial]
  rw [sumSqCoordMonomial, ← h0]
  exact Finset.single_le_sum (f := fun α : MultiIndexLE ι k ↦ b.coordMonomial α.1 ξ ^ 2)
    (fun α _ ↦ sq_nonneg _) (Finset.mem_univ 0)

/-- Each of the `#{α : |α| ≤ k}` terms of `∑_{|α| ≤ k} |ξ^α|²` is at most `(1 + |ξ|²)^k`. -/
theorem sumSqCoordMonomial_le (ξ : E) :
    b.sumSqCoordMonomial k ξ ≤ (Fintype.card (MultiIndexLE ι k) : ℝ) * (1 + ‖ξ‖ ^ 2) ^ k := by
  rw [sumSqCoordMonomial, ← Finset.card_univ, ← nsmul_eq_mul, ← Finset.sum_const]
  exact Finset.sum_le_sum fun α _ ↦ b.sq_coordMonomial_le_pow α.2 ξ

/-- For `k ≥ 1` the sum `∑_{|α| ≤ k} |ξ^α|²` dominates its terms at `α = 0` and at
`α = k eᵢ₀`, which are `1` and `⟪ξ, bᵢ₀⟫^{2k}`. -/
theorem one_add_sq_pow_le_sumSqCoordMonomial (hk : k ≠ 0) (i₀ : ι) (ξ : E) :
    1 + (⟪ξ, b i₀⟫ ^ k) ^ 2 ≤ b.sumSqCoordMonomial k ξ := by
  classical
  let top : MultiIndexLE ι k := ⟨Pi.single i₀ k, by simp⟩
  have htop : b.coordMonomial top.1 ξ = ⟪ξ, b i₀⟫ ^ k := by
    rw [coordMonomial, Finset.prod_eq_single i₀ (fun i _ hi ↦ by simp [top, hi]) (by simp)]
    simp [top]
  have hne : (0 : MultiIndexLE ι k) ≠ top := by
    intro h
    have hval := congrFun (congrArg Subtype.val h) i₀
    simp [top] at hval
    exact hk hval.symm
  have hle := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun α : MultiIndexLE ι k ↦ b.coordMonomial α.1 ξ ^ 2)
    (Finset.subset_univ ({0, top} : Finset (MultiIndexLE ι k))) (fun α _ _ ↦ sq_nonneg _)
  have h0 : b.coordMonomial (0 : MultiIndexLE ι k).1 ξ ^ 2 = 1 := by simp [coordMonomial]
  rw [Finset.sum_pair hne, h0, htop] at hle
  exact hle

variable (k) in
/-- **The hard half of the symbol inequality**: `(1 + |ξ|²)^k ≤ (1 + n)^k ∑_{|α| ≤ k} |ξ^α|²`,
`n` the dimension. With `a = ⟪ξ, bᵢ₀⟫²` at a coordinate of largest absolute value, `|ξ|² ≤ n a`,
and `(1 + n a)^k ≤ (1 + n)^k max(1, a)^k ≤ (1 + n)^k (1 + a^k)`, whose two summands are the terms
of the sum at `α = 0` and at `α = k eᵢ₀`. No multinomial expansion is needed. -/
theorem pow_one_add_norm_sq_le (ξ : E) :
    (1 + ‖ξ‖ ^ 2) ^ k ≤ ((1 : ℝ) + Fintype.card ι) ^ k * b.sumSqCoordMonomial k ξ := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simpa using b.one_le_sumSqCoordMonomial (k := 0) ξ
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hξ : ‖ξ‖ ^ 2 = 0 := by rw [← b.sum_sq_inner_left ξ]; simp
    rw [hξ]
    have h1 := b.one_le_sumSqCoordMonomial (k := k) ξ
    have h2 : (1 : ℝ) ≤ ((1 : ℝ) + Fintype.card ι) ^ k :=
      one_le_pow₀ (by linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ Fintype.card ι)])
    rw [add_zero, one_pow]
    nlinarith
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image (Finset.univ : Finset ι)
    (fun i ↦ ⟪ξ, b i⟫ ^ 2) Finset.univ_nonempty
  have hnorm : ‖ξ‖ ^ 2 ≤ (Fintype.card ι : ℝ) * ⟪ξ, b i₀⟫ ^ 2 := by
    rw [← b.sum_sq_inner_left ξ]
    calc ∑ i, ⟪ξ, b i⟫ ^ 2 ≤ ∑ _i : ι, ⟪ξ, b i₀⟫ ^ 2 :=
          Finset.sum_le_sum fun i _ ↦ hi₀ i (Finset.mem_univ i)
      _ = (Fintype.card ι : ℝ) * ⟪ξ, b i₀⟫ ^ 2 := by simp
  have hmax : 1 + (Fintype.card ι : ℝ) * ⟪ξ, b i₀⟫ ^ 2
      ≤ (1 + Fintype.card ι) * max 1 (⟪ξ, b i₀⟫ ^ 2) := by
    have h1 : (1 : ℝ) ≤ max 1 (⟪ξ, b i₀⟫ ^ 2) := le_max_left _ _
    have h2 : ⟪ξ, b i₀⟫ ^ 2 ≤ max 1 (⟪ξ, b i₀⟫ ^ 2) := le_max_right _ _
    have h3 : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
    nlinarith
  have hmaxk : (max 1 (⟪ξ, b i₀⟫ ^ 2)) ^ k ≤ 1 + (⟪ξ, b i₀⟫ ^ 2) ^ k := by
    rcases le_total (⟪ξ, b i₀⟫ ^ 2) 1 with h | h
    · rw [max_eq_left h, one_pow]
      have : (0 : ℝ) ≤ (⟪ξ, b i₀⟫ ^ 2) ^ k := by positivity
      linarith
    · rw [max_eq_right h]
      linarith [zero_le_one (α := ℝ)]
  have hlow : 1 + (⟪ξ, b i₀⟫ ^ 2) ^ k ≤ b.sumSqCoordMonomial k ξ := by
    calc 1 + (⟪ξ, b i₀⟫ ^ 2) ^ k = 1 + (⟪ξ, b i₀⟫ ^ k) ^ 2 := by
          rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ b.sumSqCoordMonomial k ξ := b.one_add_sq_pow_le_sumSqCoordMonomial hk.ne' i₀ ξ
  calc (1 + ‖ξ‖ ^ 2) ^ k ≤ (1 + (Fintype.card ι : ℝ) * ⟪ξ, b i₀⟫ ^ 2) ^ k :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
    _ ≤ ((1 + (Fintype.card ι : ℝ)) * max 1 (⟪ξ, b i₀⟫ ^ 2)) ^ k :=
        pow_le_pow_left₀ (by positivity) hmax _
    _ = (1 + (Fintype.card ι : ℝ)) ^ k * (max 1 (⟪ξ, b i₀⟫ ^ 2)) ^ k := by rw [mul_pow]
    _ ≤ (1 + (Fintype.card ι : ℝ)) ^ k * b.sumSqCoordMonomial k ξ :=
        mul_le_mul_of_nonneg_left (hmaxk.trans hlow) (by positivity)

variable (k) in
/-- **The symbol inequality** ([han2009theoretical] Exercise 7.4.2): there are `c₁, c₂ > 0` with
`c₁ (∑_{|α| ≤ k} |ξ^α|²)^{1/2} ≤ (1 + |ξ|²)^{k/2} ≤ c₂ (∑_{|α| ≤ k} |ξ^α|²)^{1/2}` for every
`ξ`. The constants are `c₁ = #{α : |α| ≤ k}^{-1/2}` and `c₂ = (1 + n)^{k/2}`, `n` the
dimension. -/
theorem exists_bounds_rpow_one_add_norm_sq :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ ξ : E,
      c₁ * Real.sqrt (b.sumSqCoordMonomial k ξ) ≤ (1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) ∧
        (1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) ≤ c₂ * Real.sqrt (b.sumSqCoordMonomial k ξ) := by
  have hne : Nonempty (MultiIndexLE ι k) := ⟨0⟩
  have hMpos : (0 : ℝ) < (Fintype.card (MultiIndexLE ι k) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  refine ⟨(Real.sqrt (Fintype.card (MultiIndexLE ι k) : ℝ))⁻¹,
    Real.sqrt (((1 : ℝ) + Fintype.card ι) ^ k), inv_pos.2 (Real.sqrt_pos.2 hMpos),
    Real.sqrt_pos.2 (by positivity), fun ξ ↦ ?_⟩
  have hb : (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2 := by positivity
  rw [rpow_half_eq_sqrt_pow hb k]
  refine ⟨?_, ?_⟩
  · rw [inv_mul_le_iff₀ (Real.sqrt_pos.2 hMpos), ← Real.sqrt_mul hMpos.le]
    exact Real.sqrt_le_sqrt (b.sumSqCoordMonomial_le ξ)
  · rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (b.pow_one_add_norm_sq_le k ξ)

variable (k) in
/-- The Fourier symbol `∑_{|α| ≤ k} |(2π ξ)^α|²` of the Sobolev norm of order `k`: by Plancherel,
`∑_{|α| ≤ k} ‖∂^α v‖²_{L²} = ∫ (∑_{|α| ≤ k} (2π)^{2|α|} |ξ^α|²) |ℱv|²`. -/
def sobolevSymbol (ξ : E) : ℝ :=
  ∑ α : MultiIndexLE ι k, (2 * Real.pi) ^ (2 * (∑ i, α.1 i)) * b.coordMonomial α.1 ξ ^ 2

private theorem one_le_two_pi : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.two_le_pi]

variable (k) in
/-- The Sobolev symbol is continuous. -/
theorem continuous_sobolevSymbol : Continuous (b.sobolevSymbol k) :=
  continuous_finsetSum _ fun α _ ↦ continuous_const.mul ((b.continuous_coordMonomial α.1).pow 2)

/-- Every factor `(2π)^{2|α|}` is at least `1`, so the Sobolev symbol dominates
`∑_{|α| ≤ k} |ξ^α|²`. -/
theorem sumSqCoordMonomial_le_sobolevSymbol (ξ : E) :
    b.sumSqCoordMonomial k ξ ≤ b.sobolevSymbol k ξ := by
  refine Finset.sum_le_sum fun α _ ↦ ?_
  nlinarith [one_le_pow₀ (n := 2 * (∑ i, α.1 i)) one_le_two_pi, sq_nonneg (b.coordMonomial α.1 ξ)]

/-- Every factor `(2π)^{2|α|}` is at most `(2π)^{2k}`. -/
theorem sobolevSymbol_le_sumSqCoordMonomial (ξ : E) :
    b.sobolevSymbol k ξ ≤ (2 * Real.pi) ^ (2 * k) * b.sumSqCoordMonomial k ξ := by
  rw [sumSqCoordMonomial, Finset.mul_sum]
  refine Finset.sum_le_sum fun α _ ↦ ?_
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ one_le_two_pi (Nat.mul_le_mul_left 2 α.2)) (sq_nonneg _)

/-- One half of the comparison of symbols: `(1 + |ξ|²)^k ≤ (1 + n)^k ∑_{|α| ≤ k} |(2π ξ)^α|²`. -/
theorem pow_le_sobolevSymbol (ξ : E) :
    (1 + ‖ξ‖ ^ 2) ^ k ≤ ((1 : ℝ) + Fintype.card ι) ^ k * b.sobolevSymbol k ξ :=
  (b.pow_one_add_norm_sq_le k ξ).trans
    (mul_le_mul_of_nonneg_left (b.sumSqCoordMonomial_le_sobolevSymbol ξ) (by positivity))

/-- The other half of the comparison of symbols:
`∑_{|α| ≤ k} |(2π ξ)^α|² ≤ (2π)^{2k} #{α : |α| ≤ k} (1 + |ξ|²)^k`. -/
theorem sobolevSymbol_le_pow (ξ : E) :
    b.sobolevSymbol k ξ ≤ ((2 * Real.pi) ^ (2 * k)
      * (Fintype.card (MultiIndexLE ι k) : ℝ)) * (1 + ‖ξ‖ ^ 2) ^ k := by
  rw [mul_assoc]
  exact (b.sobolevSymbol_le_sumSqCoordMonomial ξ).trans
    (mul_le_mul_of_nonneg_left (b.sumSqCoordMonomial_le ξ) (by positivity))

end Monomial

/-! ### The norm equivalence -/

section NormEquivalence

variable {ι E : Type*} [Fintype ι] [LinearOrder ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (b : OrthonormalBasis ι ℝ E) {k : ℕ}

/-- The `ℝ≥0∞` norm of a real multiple of a complex number, squared. -/
private theorem enorm_sq_ofReal_mul (r : ℝ) (z : ℂ) :
    ‖(r : ℂ) * z‖ₑ ^ 2 = ENNReal.ofReal (r ^ 2) * ‖z‖ₑ ^ 2 := by
  rw [enorm_mul, mul_pow]
  congr 1
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Complex.norm_real, Real.norm_eq_abs,
    sq_abs]

/-- The `ℝ≥0∞` norm of a scalar multiple of a real multiple of a complex number, squared. -/
private theorem enorm_sq_mul_ofReal_mul (c : ℂ) (r : ℝ) (z : ℂ) :
    ‖c * ((r : ℂ) * z)‖ₑ ^ 2 = ENNReal.ofReal (‖c‖ ^ 2 * r ^ 2) * ‖z‖ₑ ^ 2 := by
  rw [enorm_mul, enorm_mul, mul_pow, mul_pow, ENNReal.ofReal_mul (by positivity), mul_assoc]
  congr 2
  · rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg c)]
  · rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Complex.norm_real, Real.norm_eq_abs,
      sq_abs]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The symbol of `∂^α` in the orthonormal basis `b` is the monomial `ξ^α`: the tuple of directions
naming `α` lists `bᵢ` exactly `αᵢ` times. -/
theorem lineSymbol_multiIndexTuple (α : ι → ℕ) (ξ : E) :
    lineSymbol (multiIndexTuple b.toBasis α) ξ = ((b.coordMonomial α ξ : ℝ) : ℂ) := by
  rw [lineSymbol_apply,
    prod_multiIndexTuple (M := ℂ) b.toBasis α fun e ↦ ((inner ℝ ξ e : ℝ) : ℂ), coordMonomial,
    Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [OrthonormalBasis.coe_toBasis, Complex.ofReal_pow]

/-- If `(1 + |ξ|²)^{k/2} ℱv` lies in `L²` then so does `ξ^α ℱv` for every `|α| ≤ k`. -/
theorem memLp_lineSymbol_mul_fourier {v : Lp ℂ 2 (volume : Measure E)}
    (hF : MemLp (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (𝓕 v) ξ) 2
      (volume : Measure E))
    {α : ι → ℕ} (hα : ∑ i, α i ≤ k) :
    MemLp (fun ξ ↦ lineSymbol (multiIndexTuple b.toBasis α) ξ * (𝓕 v) ξ) 2
      (volume : Measure E) := by
  refine hF.mono ?_ ?_
  · exact ((hasTemperateGrowth_lineSymbol
      (multiIndexTuple b.toBasis α)).1.continuous.aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable _)
  · filter_upwards with ξ
    rw [norm_mul, norm_mul, b.lineSymbol_multiIndexTuple, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2) _)]
    exact mul_le_mul_of_nonneg_right (b.abs_coordMonomial_le_rpow hα ξ) (norm_nonneg _)

/-- **Plancherel for one weak derivative.** For `v ∈ H^k` and `|α| ≤ k`,
`‖∂^α v‖²_{L²} = ∫ (2π)^{2|α|} |ξ^α|² |ℱv(ξ)|² dξ`. -/
theorem sq_eLpNorm_eq_lintegral_of_hasWeakIteratedLineDerivOn
    {v w : Lp ℂ 2 (volume : Measure E)} {α : ι → ℕ} (hα : ∑ i, α i ≤ k)
    (hF : MemLp (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (𝓕 v) ξ) 2
      (volume : Measure E))
    (hvw : HasWeakIteratedLineDerivOn (multiIndexTuple b.toBasis α) (v : E → ℂ) (w : E → ℂ) ⊤
      volume) :
    eLpNorm (w : E → ℂ) 2 volume ^ 2
      = ∫⁻ ξ, ENNReal.ofReal ((2 * Real.pi) ^ (2 * (∑ i, α i)) * b.coordMonomial α ξ ^ 2)
          * ‖(𝓕 v) ξ‖ₑ ^ 2 ∂(volume : Measure E) := by
  have hae := fourier_weakDeriv_aeEq (multiIndexTuple b.toBasis α)
    (Lp.iteratedLineDerivOp_eq_of_hasWeakIteratedLineDerivOn hvw)
    (b.memLp_lineSymbol_mul_fourier hF hα)
  rw [← Lp.eLpNorm_fourier_eq w, sq_eLpNorm_two (Lp.aestronglyMeasurable _)]
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with ξ hξ
  rw [hξ, b.lineSymbol_multiIndexTuple, enorm_sq_mul_ofReal_mul]
  congr 2
  rw [norm_pow, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg Real.pi_pos.le, mul_one, ← pow_mul]
  ring

omit [LinearOrder ι] in
/-- The integrand of the Fourier-side quadratic form is a.e.-measurable. -/
private theorem aemeasurable_symbol_mul {g : E → ℝ} (hg : Continuous g)
    (v : Lp ℂ 2 (volume : Measure E)) :
    AEMeasurable (fun ξ ↦ ENNReal.ofReal (g ξ) * ‖(𝓕 v) ξ‖ₑ ^ 2) (volume : Measure E) :=
  (ENNReal.measurable_ofReal.comp hg.measurable).aemeasurable.mul
    ((Lp.aestronglyMeasurable (𝓕 v)).enorm.pow_const 2)

omit [Fintype ι] [LinearOrder ι] in
/-- `‖(1 + |ξ|²)^{k/2} ℱv‖²_{L²} = ∫ (1 + |ξ|²)^k |ℱv|²`. -/
theorem _root_.sq_eLpNorm_symbol_mul_fourier (v : Lp ℂ 2 (volume : Measure E)) :
    eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (𝓕 v) ξ) 2 volume ^ 2
      = ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ k) * ‖(𝓕 v) ξ‖ₑ ^ 2 ∂(volume : Measure E) := by
  have hcont : Continuous fun ξ : E ↦ (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((continuous_const.add (continuous_norm.pow 2)).rpow_const
      fun _ ↦ Or.inr (by positivity))
  have hmeas : AEStronglyMeasurable
      (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (𝓕 v) ξ) (volume : Measure E) :=
    hcont.aestronglyMeasurable.mul (Lp.aestronglyMeasurable _)
  rw [sq_eLpNorm_two hmeas]
  refine lintegral_congr fun ξ ↦ ?_
  rw [enorm_sq_ofReal_mul, sq_rpow_half_natCast (by positivity : (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2) k]

/-- **Plancherel for the whole Sobolev norm**: `∑_{|α| ≤ k} ‖∂^α v‖²_{L²}` is the integral of the
Sobolev symbol against `|ℱv|²`. -/
theorem sq_eLpNorm_sum_eq_lintegral {v : Lp ℂ 2 (volume : Measure E)}
    {w : MultiIndexLE ι k → Lp ℂ 2 (volume : Measure E)}
    (hF : MemLp (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (𝓕 v) ξ) 2
      (volume : Measure E))
    (hw : ∀ α : MultiIndexLE ι k, HasWeakIteratedLineDerivOn
      (multiIndexTuple b.toBasis α.1) (v : E → ℂ) (w α : E → ℂ) ⊤ volume) :
    ∑ α : MultiIndexLE ι k, eLpNorm (w α : E → ℂ) 2 volume ^ 2
      = ∫⁻ ξ, ENNReal.ofReal (b.sobolevSymbol k ξ) * ‖(𝓕 v) ξ‖ₑ ^ 2 ∂(volume : Measure E) := by
  rw [Finset.sum_congr rfl
      (fun α _ ↦ b.sq_eLpNorm_eq_lintegral_of_hasWeakIteratedLineDerivOn α.2 hF (hw α)),
    ← lintegral_finsetSum' _ (fun α _ ↦ aemeasurable_symbol_mul
      (continuous_const.mul ((b.continuous_coordMonomial α.1).pow 2)) v)]
  refine lintegral_congr fun ξ ↦ ?_
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun α _ ↦ by positivity)]
  rfl

variable (k) in
/-- **The Sobolev norm of order `k` and the Fourier norm are equivalent** ([han2009theoretical]
(7.4.1)): there are `c₁, c₂ > 0` with

`c₁ [∑_{|α| ≤ k} ‖∂^α v‖²_{L²}]^{1/2} ≤ ‖(1 + |ξ|²)^{k/2} ℱv‖_{L²}
  ≤ c₂ [∑_{|α| ≤ k} ‖∂^α v‖²_{L²}]^{1/2}`

for every `v ∈ L²(E)` whose weak derivatives `∂^α v` in the basis `b`, `|α| ≤ k`, are the `L²`
functions `w α`. The proof is Plancherel applied to each `∂^α v`, whose Fourier transform is
`(2πi ξ)^α ℱv` (`OrthonormalBasis.sq_eLpNorm_sum_eq_lintegral`), followed by the symbol
inequality (`OrthonormalBasis.exists_bounds_rpow_one_add_norm_sq`). The constants are
`c₁ = ((2π)^{2k} #{α : |α| ≤ k})^{-1/2}` and `c₂ = (1 + n)^{k/2}`, `n` the dimension. -/
theorem exists_norm_equiv_eLpNorm_symbol_mul_fourier :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ (v : Lp ℂ 2 (volume : Measure E)) (w : MultiIndexLE ι k → Lp ℂ 2 (volume : Measure E)),
        (∀ α : MultiIndexLE ι k, HasWeakIteratedLineDerivOn
            (multiIndexTuple b.toBasis α.1) (v : E → ℂ) (w α : E → ℂ) ⊤ volume) →
        c₁ * (∑ α, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2)
            ≤ (eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (𝓕 v) ξ) 2
                volume).toReal
          ∧ (eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (𝓕 v) ξ) 2
                volume).toReal ≤ c₂ * (∑ α, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2) := by
  have hne : Nonempty (MultiIndexLE ι k) := ⟨0⟩
  have hMpos : (0 : ℝ) < (Fintype.card (MultiIndexLE ι k) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have ha1 : (0 : ℝ) < ((2 * Real.pi) ^ (2 * k)
      * (Fintype.card (MultiIndexLE ι k) : ℝ))⁻¹ := by positivity
  have ha2 : (0 : ℝ) < ((1 : ℝ) + Fintype.card ι) ^ k := by positivity
  refine ⟨Real.sqrt (((2 * Real.pi) ^ (2 * k)
      * (Fintype.card (MultiIndexLE ι k) : ℝ))⁻¹), Real.sqrt (((1 : ℝ) + Fintype.card ι) ^ k),
    Real.sqrt_pos.2 ha1, Real.sqrt_pos.2 ha2, ?_⟩
  intro v w hw
  obtain ⟨N, hN⟩ : ∃ N : ℝ≥0∞, N = eLpNorm
      (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (𝓕 v) ξ) 2 volume := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ≥0∞, A = ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ k) * ‖(𝓕 v) ξ‖ₑ ^ 2
      ∂(volume : Measure E) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ≥0∞, B = ∫⁻ ξ, ENNReal.ofReal (b.sobolevSymbol k ξ) * ‖(𝓕 v) ξ‖ₑ ^ 2
      ∂(volume : Measure E) := ⟨_, rfl⟩
  rw [← hN]
  have hres : ((⊤ : Opens E) : Set E) = Set.univ := rfl
  have hv : MemSobolevMultiIndex b.toBasis (v : E → ℂ) k 2 ⊤ volume := by
    refine ⟨?_, fun α hα ↦ ⟨(w ⟨α, hα⟩ : E → ℂ), hw ⟨α, hα⟩, ?_⟩⟩
    · rw [hres, Measure.restrict_univ]; exact Lp.memLp v
    · rw [hres, Measure.restrict_univ]; exact Lp.memLp (w ⟨α, hα⟩)
  have hF : MemLp (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (𝓕 v) ξ) 2 volume :=
    (memSobolev_two_iff_memLp_symbol_mul_fourier (Nat.cast_nonneg k) v).1
      ((memSobolev_iff_memSobolevMultiIndex b).2 hv)
  have hA : N ^ 2 = A := by rw [hN, hAdef]; exact sq_eLpNorm_symbol_mul_fourier v
  have hB : ∑ α : MultiIndexLE ι k, eLpNorm (w α : E → ℂ) 2 volume ^ 2 = B := by
    rw [hBdef]; exact b.sq_eLpNorm_sum_eq_lintegral hF hw
  have hcomp1 : ENNReal.ofReal (((2 * Real.pi) ^ (2 * k)
      * (Fintype.card (MultiIndexLE ι k) : ℝ))⁻¹) * B ≤ A := by
    rw [hAdef, hBdef, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun ξ ↦ ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul ha1.le]
    gcongr
    calc ((2 * Real.pi) ^ (2 * k) * (Fintype.card (MultiIndexLE ι k) : ℝ))⁻¹
          * b.sobolevSymbol k ξ
        ≤ ((2 * Real.pi) ^ (2 * k) * (Fintype.card (MultiIndexLE ι k) : ℝ))⁻¹
          * (((2 * Real.pi) ^ (2 * k) * (Fintype.card (MultiIndexLE ι k) : ℝ))
            * (1 + ‖ξ‖ ^ 2) ^ k) :=
          mul_le_mul_of_nonneg_left (b.sobolevSymbol_le_pow ξ) ha1.le
      _ = (1 + ‖ξ‖ ^ 2) ^ k := by field_simp
  have hcomp2 : A ≤ ENNReal.ofReal (((1 : ℝ) + Fintype.card ι) ^ k) * B := by
    rw [hAdef, hBdef, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun ξ ↦ ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul ha2.le]
    gcongr
    exact b.pow_le_sobolevSymbol ξ
  have hAfin : A ≠ ⊤ := by rw [← hA, hN]; exact ENNReal.pow_ne_top hF.eLpNorm_lt_top.ne
  have hBfin : B ≠ ⊤ := by
    rw [← hB]
    exact (ENNReal.sum_lt_top.2 fun α _ ↦
      ENNReal.pow_lt_top (Lp.eLpNorm_ne_top (w α)).lt_top).ne
  have hPsum : ∑ α : MultiIndexLE ι k, ‖w α‖ ^ 2 = B.toReal := by
    rw [← hB, ENNReal.toReal_sum fun α _ ↦ ENNReal.pow_ne_top (Lp.eLpNorm_ne_top (w α))]
    exact Finset.sum_congr rfl fun α _ ↦ by rw [Lp.norm_def, ← ENNReal.toReal_pow]
  have hNsq : N.toReal ^ 2 = A.toReal := by rw [← ENNReal.toReal_pow, hA]
  have hsumnn : (0 : ℝ) ≤ ∑ α : MultiIndexLE ι k, ‖w α‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hP2 : ((∑ α : MultiIndexLE ι k, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2)) ^ 2
      = ∑ α : MultiIndexLE ι k, ‖w α‖ ^ 2 := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hsumnn]
    norm_num
  constructor
  · refine le_of_pow_le_pow_left₀ two_ne_zero ENNReal.toReal_nonneg ?_
    rw [mul_pow, Real.sq_sqrt ha1.le, hP2, hPsum, hNsq]
    have h := ENNReal.toReal_mono hAfin hcomp1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha1.le] at h
  · refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    rw [mul_pow, Real.sq_sqrt ha2.le, hP2, hPsum, hNsq]
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBfin) hcomp2
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha2.le] at h

end NormEquivalence

end OrthonormalBasis
