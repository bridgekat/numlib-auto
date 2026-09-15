import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Numlib.Analysis.Calculus.ContDiffMapIcc
import Numlib.Analysis.Calculus.RootMultiplicity
import Numlib.Approximation.CompositeQuadrature
import Numlib.Approximation.NewtonForm
import Numlib.Topology.Order.IntermediateValue

/-!
# Newton–Cotes quadrature

The interpolatory quadrature rules at equispaced nodes: the *closed* rules with nodes
`x_i = a + i h`, `h = (b - a)/n`, `i = 0, …, n`, and the *open* rules with nodes
`x_i = a + (i + 1) h`, `h = (b - a)/(n + 2)`. Their weights are `h w_i`, where the `w_i` are the
integrals over `[0, n]` (closed) or `[-1, n + 1]` (open) of the *cardinal polynomials*
`φ_i(t) = ∏_{k ≠ i} (t - k)/(i - k)` at the integer nodes — numbers that depend on `n` alone.
The midpoint, trapezoidal and Simpson rules are the cases `n = 0` (open), `n = 1` and `n = 2`.

## Main definitions

* `Quadrature.midpointRule`, `Quadrature.midpointSum` — the midpoint rule and its composite form,
  in the style of `Quadrature.trapezoidSum` of `Numlib/Approximation/CompositeQuadrature`.
* `Quadrature.intNode`, `Quadrature.cardinalPoly`, `Quadrature.intNodal` — the integer nodes
  `0, …, n`, the cardinal polynomials `φ_i` and the nodal polynomial `π_{n+1}(t) = ∏ (t - i)`.
* `Quadrature.newtonCotesWeight`, `Quadrature.openNewtonCotesWeight` — the weights `w_i`.
* `Quadrature.closedNewtonCotes`, `Quadrature.openNewtonCotes`, `Quadrature.compositeNewtonCotes`
  — the rules, as real functions of the integrand and the endpoints.
* `Quadrature.newtonCotesM`, `Quadrature.newtonCotesK` (and the open versions) — the constants
  `M_n = ∫_0^n t π_{n+1}`, `K_n = ∫_0^n π_{n+1}` of the error formulae.
* `Quadrature.hermiteBasisL`, `Quadrature.hermiteBasisM`, `Quadrature.hermiteQuadrature`,
  `Quadrature.correctedTrapezoid`, `Quadrature.correctedTrapezoidSum` — Hermite quadrature and
  the corrected trapezoidal rule.

## Main results

* `Quadrature.exists_sub_midpoint_eq`, `Quadrature.sub_composite_midpoint_eq`,
  `Quadrature.tendsto_midpointSum` — the midpoint error `h³ f''(ξ)/3`, its composite form
  `(b - a) H² f''(ξ)/24`, and convergence for continuous integrands.
* `Quadrature.newtonCotesWeight_symm`, `Quadrature.sum_newtonCotesWeight`,
  `Quadrature.closedNewtonCotes_eq_sum_integral_basis` — the weights are symmetric, sum to the
  length of the reference interval, and do not depend on `[a, b]`: the closed rule *is* the
  Lagrange quadrature formula at the equispaced nodes.
* `Quadrature.integral_eq_closedNewtonCotes_of_degree_le`,
  `Quadrature.integral_eq_closedNewtonCotes_of_even`, `Quadrature.isExactOn_closedNewtonCotes` —
  exactness to degree `n`, to degree `n + 1` for even `n` (by symmetry alone), and the bridge to
  `Quadrature.IsExactOn`/`Quadrature.IsInterpolatory` on `C([a, b], ℝ)`.
* `Quadrature.integral_intNodal_pos_of_even`, `Quadrature.newtonCotesM_neg` — the sign facts
  behind the sharp error formula: `W(x) = ∫_0^x π_{n+1} > 0` on `(0, n)` and `M_n < 0` for even
  `n`.
* `Quadrature.exists_sub_closedNewtonCotes_eq_of_even` — **the error of the closed rules with
  even `n`**, `∫_a^b f - I_n(f) = M_n/(n + 2)! h^{n+3} f^{(n+2)}(ξ)`, and
  `Quadrature.not_integral_eq_closedNewtonCotes_of_even`, the exactness of the degree `n + 1`.
* `Quadrature.integral_sub_closedNewtonCotes_pow_eq`,
  `Quadrature.not_integral_eq_closedNewtonCotes_of_odd`,
  `Quadrature.abs_sub_closedNewtonCotes_le_of_contDiffOn` — for odd `n`, where the sharp error
  formula is still open: the error at `x^{n+1}` is exactly `h^{n+2} K_n ≠ 0`, so the degree of
  exactness is `n`, and the `O(h^{n+2})` bound that the interpolation error gives for every `n`.
* `Quadrature.openNewtonCotesM_pos`, `Quadrature.integral_intNodal_neg_one_mul_nonneg`,
  `Quadrature.exists_sub_openNewtonCotes_eq_of_even` — the same for the *open* rules with even
  `n`: `W̃(x) = ∫_{-1}^x π_{n+1} ≤ 0` on `[-1, n + 1]` with `M̃_n > 0`, and the error
  `∫_a^b f - Ĩ_n(f) = M̃_n/(n + 2)! h^{n+3} f^{(n+2)}(ξ)`, `h = (b - a)/(n + 2)`, which for
  `n = 0` is the midpoint formula.
* `Quadrature.exists_sub_compositeNewtonCotes_eq_of_even`,
  `Quadrature.abs_sub_compositeNewtonCotes_le`,
  `Quadrature.abs_sub_compositeNewtonCotes_le_of_contDiffOn`,
  `Quadrature.tendsto_compositeNewtonCotes_of_contDiffOn` — the composite error, the Riemann-sum
  bound for rules with nonnegative weights, and the `O(H^{n+1})` bound and convergence for a
  `C^{n+1}` integrand, which need no sign hypothesis on the weights.
* `Quadrature.integral_eq_hermiteQuadrature_of_degree_le`,
  `Quadrature.exists_sub_correctedTrapezoid_eq`, `Quadrature.sub_correctedTrapezoidSum_eq` — the
  degree `2n + 1` of Hermite quadrature and the corrected trapezoidal error `h⁵ f⁗(ξ)/720`.
* `Quadrature.abs_sub_simpson_add_estimate_le` — the a posteriori error estimate of adaptive
  Simpson quadrature, with an explicit remainder.

## The route to the error formula

The error of the closed rule is `∫_a^b (f - Π_n f)`, and `f - Π_n f = φ ω` with
`ω = ∏ (X - x_i)` the nodal polynomial and `φ(x) = f[x_0, …, x_n, x]` the divided difference with
`x` appended. Integrating by parts against `W(x) = ∫_a^x ω`, which vanishes at both endpoints
because `ω` is odd about the midpoint when `n` is even, gives `-∫_a^b W φ'`; the derivative
`φ'(x) = f[x_0, …, x_n, x, x]` is the leading coefficient of a Hermite interpolant of `f`, so it
lies between the extreme values of `f^{(n+2)}/(n+2)!`, and `W > 0` inside `(a, b)` makes the
intermediate value theorem applicable. The function `φ` is made smooth across the nodes as the
iterated `dslope` of `f - Π_n f` at the nodes (Hadamard's lemma,
`Numlib/Analysis/Calculus/RootMultiplicity`), and `φ'` is identified with the Hermite coefficient
away from the nodes by `DividedDifference.hasDerivAt_newton_snoc`. The positivity of `W` is the
fact that the unit-panel integrals of `π_{n+1}` alternate in sign with decreasing modulus up to the
midpoint, through the identity `π_{n+1}(t + 1)(t - n) = π_{n+1}(t)(t + 1)`.

## References

[quarteroni2000numerical] §9.2–9.5 and §9.7; the sign argument is that of Isaacson–Keller,
*Analysis of Numerical Methods*, pp. 308–314; the one-variable Hadamard lemma is the route to the
smoothness of the divided difference across the nodes.
-/

open Filter Polynomial Set Topology intervalIntegral
open MeasureTheory (volume)

namespace Quadrature

/-! ### Mean value lemmas -/

section MeanValue

variable {a b : ℝ} {K f : ℝ → ℝ}

/-- **The weighted mean value theorem for integrals.** For `K ≥ 0` and `f` continuous on
`[a, b]`, `∫_a^b K f = f(ξ) ∫_a^b K` for some `ξ ∈ [a, b]`: the integral lies between the
extreme values of `f` times `∫ K`, and the intermediate value theorem supplies `ξ`. -/
theorem exists_integral_mul_eq_mul_integral (hab : a ≤ b) (hK : ContinuousOn K (Icc a b))
    (hf : ContinuousOn f (Icc a b)) (hKnn : ∀ t ∈ Icc a b, 0 ≤ K t) :
    ∃ ξ ∈ Icc a b, ∫ t in a..b, K t * f t = f ξ * ∫ t in a..b, K t := by
  have hne : (Icc a b).Nonempty := ⟨a, left_mem_Icc.2 hab⟩
  obtain ⟨p, hp, hmin⟩ := isCompact_Icc.exists_isMinOn hne hf
  obtain ⟨q, hq, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hf
  have hKf : IntervalIntegrable (fun t => K t * f t) volume a b :=
    (hK.mul hf).intervalIntegrable_of_Icc hab
  have hKc : ∀ c, IntervalIntegrable (fun t => K t * c) volume a b := fun c =>
    (hK.mul continuousOn_const).intervalIntegrable_of_Icc hab
  have hlow : f p * ∫ t in a..b, K t ≤ ∫ t in a..b, K t * f t := by
    have := integral_mono_on hab (hKc (f p)) hKf fun t ht =>
      mul_le_mul_of_nonneg_left (hmin ht) (hKnn t ht)
    rwa [integral_mul_const, mul_comm] at this
  have hhigh : (∫ t in a..b, K t * f t) ≤ f q * ∫ t in a..b, K t := by
    have := integral_mono_on hab hKf (hKc (f q)) fun t ht =>
      mul_le_mul_of_nonneg_left (hmax ht) (hKnn t ht)
    rwa [integral_mul_const, mul_comm] at this
  have hpq : uIcc p q ⊆ Icc a b := uIcc_subset_Icc hp hq
  obtain ⟨ξ, hξ, hξval⟩ := intermediate_value_uIcc
    ((hf.mono hpq).mul continuousOn_const) (mem_uIcc_of_le hlow hhigh)
  exact ⟨ξ, hpq hξ, hξval.symm⟩

/-- A continuous nonnegative function on `[a, b]`, positive at an interior point, has a positive
integral. -/
theorem integral_pos_of_continuousOn_of_nonneg (hab : a < b) (hK : ContinuousOn K (Icc a b))
    (hKnn : ∀ t ∈ Icc a b, 0 ≤ K t) {c : ℝ} (hc : c ∈ Ioo a b) (hKc : 0 < K c) :
    0 < ∫ t in a..b, K t := by
  have hcont : ContinuousAt K c :=
    hK.continuousAt (Icc_mem_nhds hc.1 hc.2)
  obtain ⟨δ, hδ, hδpos⟩ : ∃ δ > 0, ∀ t, |t - c| < δ → 0 < K t := by
    have := (hcont.eventually (lt_mem_nhds hKc))
    rw [Metric.eventually_nhds_iff] at this
    obtain ⟨δ, hδ, h⟩ := this
    exact ⟨δ, hδ, fun t ht => h (by rwa [Real.dist_eq])⟩
  set ε := min δ (min (c - a) (b - c)) with hε
  have hε0 : 0 < ε := lt_min hδ (lt_min (by linarith [hc.1]) (by linarith [hc.2]))
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεa : ε ≤ c - a := (min_le_right _ _).trans (min_le_left _ _)
  have hεb : ε ≤ b - c := (min_le_right _ _).trans (min_le_right _ _)
  have hKint : IntervalIntegrable K volume a b := hK.intervalIntegrable_of_Icc hab.le
  have hsub : ∀ u v, a ≤ u → u ≤ v → v ≤ b → IntervalIntegrable K volume u v :=
    fun u v hu huv hv => hKint.mono_set
      (by rw [uIcc_of_le huv, uIcc_of_le hab.le]; exact Icc_subset_Icc hu hv)
  have h1 : IntervalIntegrable K volume a (c - ε) := hsub _ _ le_rfl (by linarith) (by linarith)
  have h2 : IntervalIntegrable K volume (c - ε) (c + ε) :=
    hsub _ _ (by linarith) (by linarith) (by linarith)
  have h3 : IntervalIntegrable K volume (c + ε) b := hsub _ _ (by linarith) (by linarith) le_rfl
  rw [← integral_add_adjacent_intervals (h1.trans h2) h3,
    ← integral_add_adjacent_intervals h1 h2]
  have hmid : 0 < ∫ t in c - ε..c + ε, K t := by
    refine intervalIntegral_pos_of_pos_on h2 (fun t ht => hδpos t ?_) (by linarith)
    rw [abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hleft : 0 ≤ ∫ t in a..c - ε, K t :=
    integral_nonneg (by linarith) fun t ht => hKnn t ⟨ht.1, by linarith [ht.2]⟩
  have hright : 0 ≤ ∫ t in c + ε..b, K t :=
    integral_nonneg (by linarith) fun t ht => hKnn t ⟨by linarith [ht.1], ht.2⟩
  linarith

/-- **The weighted mean value theorem, with `ξ` inside the open interval.** For `K ≥ 0` with
`∫_a^b K > 0` and `f` continuous, `∫ K f = f(ξ) ∫ K` with `ξ ∈ (a, b)`: if the mean value of `f`
lies strictly between its extreme values, the intermediate value theorem gives an interior `ξ`;
if it equals an extreme value, `f` takes that value wherever `K ≠ 0`, and `K ≠ 0` somewhere
inside because its integral is positive. -/
theorem exists_mem_Ioo_integral_mul_eq_mul_integral (hab : a < b)
    (hK : ContinuousOn K (Icc a b)) (hf : ContinuousOn f (Icc a b))
    (hKnn : ∀ t ∈ Icc a b, 0 ≤ K t) (hKpos : 0 < ∫ t in a..b, K t) :
    ∃ ξ ∈ Ioo a b, ∫ t in a..b, K t * f t = f ξ * ∫ t in a..b, K t := by
  set I : ℝ := ∫ t in a..b, K t with hI
  have hne : (Icc a b).Nonempty := ⟨a, left_mem_Icc.2 hab.le⟩
  obtain ⟨p, hp, hmin⟩ := isCompact_Icc.exists_isMinOn hne hf
  obtain ⟨q, hq, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hf
  have hKf : IntervalIntegrable (fun t => K t * f t) volume a b :=
    (hK.mul hf).intervalIntegrable_of_Icc hab.le
  have hKc : ∀ c, IntervalIntegrable (fun t => K t * c) volume a b := fun c =>
    (hK.mul continuousOn_const).intervalIntegrable_of_Icc hab.le
  have hlow : f p * I ≤ ∫ t in a..b, K t * f t := by
    have := integral_mono_on hab.le (hKc (f p)) hKf fun t ht =>
      mul_le_mul_of_nonneg_left (hmin ht) (hKnn t ht)
    rwa [integral_mul_const, mul_comm] at this
  have hhigh : (∫ t in a..b, K t * f t) ≤ f q * I := by
    have := integral_mono_on hab.le hKf (hKc (f q)) fun t ht =>
      mul_le_mul_of_nonneg_left (hmax ht) (hKnn t ht)
    rwa [integral_mul_const, mul_comm] at this
  -- a continuous nonnegative function with zero integral vanishes inside
  have hvanish : ∀ g : ℝ → ℝ, ContinuousOn g (Icc a b) → (∀ t ∈ Icc a b, 0 ≤ g t) →
      (∫ t in a..b, g t) = 0 → ∀ t ∈ Ioo a b, g t = 0 := by
    intro g hgc hg hgint t ht
    by_contra hne
    have hpos : 0 < g t := lt_of_le_of_ne (hg t (Ioo_subset_Icc_self ht)) (Ne.symm hne)
    exact absurd hgint (integral_pos_of_continuousOn_of_nonneg hab hgc hg ht hpos).ne'
  -- `K` is nonzero at some interior point, because its integral is positive
  obtain ⟨ξ₀, hξ₀, hKξ₀⟩ : ∃ ξ ∈ Ioo a b, K ξ ≠ 0 := by
    by_contra hall
    push Not at hall
    have : (∫ t in a..b, K t) = 0 := by
      rw [integral_of_le hab.le, MeasureTheory.integral_Ioc_eq_integral_Ioo,
        MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (0 : ℝ))
          fun t ht => hall t ht]
      simp
    exact absurd this hKpos.ne'
  -- an extreme value is attained where `K` does not vanish
  have hextreme : ∀ c, (∫ t in a..b, K t * f t) = f c * I → c ∈ Icc a b →
      ((∀ t ∈ Icc a b, f c ≤ f t) ∨ ∀ t ∈ Icc a b, f t ≤ f c) →
      ∃ ξ ∈ Ioo a b, ∫ t in a..b, K t * f t = f ξ * I := by
    intro c hc hcmem hext
    refine ⟨ξ₀, hξ₀, ?_⟩
    suffices hfξ : f ξ₀ = f c by rw [hfξ, hc]
    rcases hext with hext | hext
    · have e : (fun t => K t * (f t - f c)) = fun t => K t * f t - K t * f c := by
        funext t; ring
      have h := hvanish (fun t => K t * (f t - f c)) (hK.mul (hf.sub continuousOn_const))
        (fun t ht => mul_nonneg (hKnn t ht) (by linarith [hext t ht]))
        (by rw [e, integral_sub hKf (hKc (f c)), integral_mul_const, hc]; ring) ξ₀ hξ₀
      rcases mul_eq_zero.1 h with h | h
      · exact absurd h hKξ₀
      · linarith
    · have e : (fun t => K t * (f c - f t)) = fun t => K t * f c - K t * f t := by
        funext t; ring
      have h := hvanish (fun t => K t * (f c - f t)) (hK.mul (continuousOn_const.sub hf))
        (fun t ht => mul_nonneg (hKnn t ht) (by linarith [hext t ht]))
        (by rw [e, integral_sub (hKc (f c)) hKf, integral_mul_const, hc]; ring) ξ₀ hξ₀
      rcases mul_eq_zero.1 h with h | h
      · exact absurd h hKξ₀
      · linarith
  -- the mean value of `f` is either strictly between the extremes or one of them
  set μ : ℝ := (∫ t in a..b, K t * f t) / I with hμ
  have hμI : (∫ t in a..b, K t * f t) = μ * I := by
    rw [hμ, div_mul_cancel₀ _ hKpos.ne']
  have hpμ : f p ≤ μ := by rw [hμ, le_div_iff₀ hKpos]; exact hlow
  have hμq : μ ≤ f q := by rw [hμ, div_le_iff₀ hKpos]; exact hhigh
  rcases eq_or_lt_of_le hpμ with hpμ' | hpμ'
  · exact hextreme p (by rw [hμI, hpμ']) hp (Or.inl fun t ht => hmin ht)
  rcases eq_or_lt_of_le hμq with hμq' | hμq'
  · exact hextreme q (by rw [hμI, hμq']) hq (Or.inr fun t ht => hmax ht)
  -- strictly between: the intermediate value theorem on the open interval between `p` and `q`
  have hpq : p ≠ q := fun h => by rw [h] at hpμ'; linarith
  rcases lt_or_gt_of_ne hpq with hlt | hlt
  · obtain ⟨ξ, hξ, hξval⟩ := intermediate_value_Ioo hlt.le
      (hf.mono (Icc_subset_Icc hp.1 hq.2)) ⟨hpμ', hμq'⟩
    exact ⟨ξ, ⟨lt_of_le_of_lt hp.1 hξ.1, lt_of_lt_of_le hξ.2 hq.2⟩, by rw [hμI, hξval]⟩
  · obtain ⟨ξ, hξ, hξval⟩ := intermediate_value_Ioo' hlt.le
      (hf.mono (Icc_subset_Icc hq.1 hp.2)) ⟨hpμ', hμq'⟩
    exact ⟨ξ, ⟨lt_of_le_of_lt hq.1 hξ.1, lt_of_lt_of_le hξ.2 hp.2⟩, by rw [hμI, hξval]⟩

/-- The nonpositive-kernel form of `Quadrature.exists_mem_Ioo_integral_mul_eq_mul_integral`. -/
theorem exists_mem_Ioo_integral_mul_eq_mul_integral_of_nonpos (hab : a < b)
    (hK : ContinuousOn K (Icc a b)) (hf : ContinuousOn f (Icc a b))
    (hKnp : ∀ t ∈ Icc a b, K t ≤ 0) (hKneg : (∫ t in a..b, K t) < 0) :
    ∃ ξ ∈ Ioo a b, ∫ t in a..b, K t * f t = f ξ * ∫ t in a..b, K t := by
  have hKint : IntervalIntegrable K volume a b := hK.intervalIntegrable_of_Icc hab.le
  obtain ⟨ξ, hξ, h⟩ := exists_mem_Ioo_integral_mul_eq_mul_integral (K := fun t => -K t) hab
    hK.neg hf (fun t ht => neg_nonneg.2 (hKnp t ht)) (by rw [integral_neg]; linarith)
  refine ⟨ξ, hξ, ?_⟩
  have e : (fun t => -K t * f t) = fun t => -(K t * f t) := by funext t; ring
  rw [e, integral_neg, integral_neg] at h
  linarith

/-- **Collecting panel errors.** If each of `m` panel errors is `c * u (ξ j)` with `ξ j ∈ [a, b]`
and `u` continuous, their sum is `m * c * u ξ` for one `ξ ∈ [a, b]`: the discrete mean value
theorem `ContinuousOn.exists_sum_mul_eq_mul_sum` with unit weights. -/
theorem exists_sum_mul_eq_of_forall_mem (hab : a ≤ b) {u : ℝ → ℝ} (hu : ContinuousOn u (Icc a b))
    {m : ℕ} {ξ : ℕ → ℝ} (hξ : ∀ j < m, ξ j ∈ Icc a b) (c : ℝ) :
    ∃ η ∈ Icc a b, ∑ j ∈ Finset.range m, c * u (ξ j) = m * c * u η := by
  obtain ⟨η, hη, h⟩ := hu.exists_sum_mul_eq_mul_sum hab (ι := Fin m)
    (x := fun j => ξ j) (fun j => hξ j j.2) (δ := fun _ => (1 : ℝ)) fun _ => zero_le_one
  refine ⟨η, hη, ?_⟩
  simp only [one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at h
  rw [Finset.sum_range (fun j => c * u (ξ j)), ← Finset.mul_sum, h]
  ring

end MeanValue

/-! ### The midpoint rule -/

section Midpoint

variable {a b : ℝ} {g g' g'' : ℝ → ℝ}

/-- **The midpoint (rectangle) rule** `(b - a) f((a + b)/2)`: the integral of the constant
interpolant at the midpoint.

Reference: [quarteroni2000numerical], (9.5). -/
noncomputable def midpointRule (f : ℝ → ℝ) (a b : ℝ) : ℝ := (b - a) * f ((a + b) / 2)

/-- **The composite midpoint sum** on the uniform mesh of `m` panels of width `H`,
`H ∑_{k < m} g(a + (k + 1/2) H)`.

Reference: [quarteroni2000numerical], (9.7). -/
noncomputable def midpointSum (g : ℝ → ℝ) (a H : ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range m, H * g (a + (k + 1 / 2) * H)

/-- **The Peano kernel of the midpoint rule** on `[α, β]`: `(t - α)²/2` on the left half of the
panel and `(β - t)²/2` on the right half. It is continuous, nonnegative, and integrates to
`(β - α)³/24`. -/
noncomputable def midpointKernel (α β t : ℝ) : ℝ :=
  if t ≤ (α + β) / 2 then (t - α) ^ 2 / 2 else (β - t) ^ 2 / 2

/-- The midpoint kernel is continuous: its two branches agree at the midpoint. -/
theorem continuous_midpointKernel (α β : ℝ) : Continuous (midpointKernel α β) := by
  unfold midpointKernel
  refine Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const
    fun t ht => ?_
  have ht' : t = (α + β) / 2 := ht
  rw [ht']
  ring

/-- The midpoint kernel is nonnegative. -/
theorem midpointKernel_nonneg (α β t : ℝ) : 0 ≤ midpointKernel α β t := by
  unfold midpointKernel
  split_ifs <;> positivity

/-- The midpoint kernel on the left half of the panel. -/
theorem midpointKernel_of_le {α β t : ℝ} (ht : t ≤ (α + β) / 2) :
    midpointKernel α β t = (t - α) ^ 2 / 2 := by
  simp [midpointKernel, ht]

/-- The midpoint kernel on the right half of the panel. -/
theorem midpointKernel_of_ge {α β t : ℝ} (ht : (α + β) / 2 ≤ t) :
    midpointKernel α β t = (β - t) ^ 2 / 2 := by
  rcases eq_or_lt_of_le ht with h | h
  · rw [midpointKernel_of_le h.ge, ← h]
    ring
  · simp [midpointKernel, not_le.2 h]

/-- The telescoping identity behind a second order Peano kernel: if `p'' = 1`, then
`p g'' - g` is the derivative of `p g' - p' g`. -/
private theorem integral_quadratic_kernel_sub {p p₁ : ℝ → ℝ} {u v : ℝ}
    (hp : ∀ x : ℝ, HasDerivAt p (p₁ x) x) (hp₁ : ∀ x : ℝ, HasDerivAt p₁ 1 x)
    (hg : ∀ x ∈ uIcc u v, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ uIcc u v, HasDerivAt g' (g'' x) x)
    (hg'' : IntervalIntegrable g'' volume u v) :
    (∫ t in u..v, p t * g'' t) - ∫ t in u..v, g t
      = (p v * g' v - p₁ v * g v) - (p u * g' u - p₁ u * g u) := by
  have hdp : Differentiable ℝ p := fun y => (hp y).differentiableAt
  have hcg : ContinuousOn g (uIcc u v) := fun y hy =>
    (hg y hy).continuousAt.continuousWithinAt
  have hpg : IntervalIntegrable (fun t => p t * g'' t) volume u v :=
    hg''.continuousOn_mul hdp.continuous.continuousOn
  have hgi : IntervalIntegrable g volume u v := hcg.intervalIntegrable
  have hΦ : ∀ y ∈ uIcc u v,
      HasDerivAt (fun t => p t * g' t - p₁ t * g t) (p y * g'' y - g y) y := by
    intro y hy
    exact (((hp y).mul (hg' y hy)).sub ((hp₁ y).mul (hg y hy))).congr_deriv (by ring)
  rw [← integral_sub hpg hgi]
  exact integral_eq_sub_of_hasDerivAt hΦ (hpg.sub hgi)

/-- **The Peano identity for the midpoint rule on one panel**: for `α ≤ β`,
`∫_α^β g - (β - α) g((α + β)/2) = ∫_α^β K(t) g''(t) dt` with `K` the midpoint kernel. One
telescoping identity on each half panel; the boundary terms at the midpoint cancel because the
two branches of the kernel agree there to first order with opposite first derivatives.

Reference: [quarteroni2000numerical], §9.2.1. -/
theorem sub_midpoint_eq_integral_peanoKernel {α β : ℝ} (hαβ : α ≤ β)
    (hg : ∀ x ∈ Icc α β, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Icc α β, HasDerivAt g' (g'' x) x)
    (hg'' : IntervalIntegrable g'' volume α β) :
    (∫ t in α..β, g t) - midpointRule g α β
      = ∫ t in α..β, midpointKernel α β t * g'' t := by
  set c := (α + β) / 2 with hc
  have hαc : α ≤ c := by linarith
  have hcβ : c ≤ β := by linarith
  have hsubL : uIcc α c ⊆ Icc α β := by
    rw [uIcc_of_le hαc]; exact Icc_subset_Icc le_rfl hcβ
  have hsubR : uIcc c β ⊆ Icc α β := by
    rw [uIcc_of_le hcβ]; exact Icc_subset_Icc hαc le_rfl
  have hint : IntervalIntegrable g'' volume α β := hg''
  have hL := integral_quadratic_kernel_sub (u := α) (v := c) (g := g) (g' := g') (g'' := g'')
    (p := fun t => (t - α) ^ 2 / 2) (p₁ := fun t => t - α)
    (fun y => ((((hasDerivAt_id' y).sub_const α).pow 2).div_const 2).congr_deriv
      (by push_cast; ring))
    (fun y => (hasDerivAt_id' y).sub_const α)
    (fun y hy => hg y (hsubL hy)) (fun y hy => hg' y (hsubL hy))
    (hint.mono_set (by rw [uIcc_of_le hαβ]; exact hsubL))
  have hR := integral_quadratic_kernel_sub (u := c) (v := β) (g := g) (g' := g') (g'' := g'')
    (p := fun t => (β - t) ^ 2 / 2) (p₁ := fun t => t - β)
    (fun y => ((((hasDerivAt_id' y).const_sub β).pow 2).div_const 2).congr_deriv
      (by push_cast; ring))
    (fun y => (hasDerivAt_id' y).sub_const β)
    (fun y hy => hg y (hsubR hy)) (fun y hy => hg' y (hsubR hy))
    (hint.mono_set (by rw [uIcc_of_le hαβ]; exact hsubR))
  have hgL : IntervalIntegrable g volume α c := ContinuousOn.intervalIntegrable fun y hy =>
    (hg y (hsubL hy)).continuousAt.continuousWithinAt
  have hgR : IntervalIntegrable g volume c β := ContinuousOn.intervalIntegrable fun y hy =>
    (hg y (hsubR hy)).continuousAt.continuousWithinAt
  have hKL : IntervalIntegrable (fun t => midpointKernel α β t * g'' t) volume α c :=
    (hint.mono_set (by rw [uIcc_of_le hαβ]; exact hsubL)).continuousOn_mul
      (continuous_midpointKernel α β).continuousOn
  have hKR : IntervalIntegrable (fun t => midpointKernel α β t * g'' t) volume c β :=
    (hint.mono_set (by rw [uIcc_of_le hαβ]; exact hsubR)).continuousOn_mul
      (continuous_midpointKernel α β).continuousOn
  have eL : (∫ t in α..c, midpointKernel α β t * g'' t)
      = ∫ t in α..c, (t - α) ^ 2 / 2 * g'' t := by
    refine integral_congr fun t ht => ?_
    rw [uIcc_of_le hαc] at ht
    rw [midpointKernel_of_le ht.2]
  have eR : (∫ t in c..β, midpointKernel α β t * g'' t)
      = ∫ t in c..β, (β - t) ^ 2 / 2 * g'' t := by
    refine integral_congr fun t ht => ?_
    rw [uIcc_of_le hcβ] at ht
    rw [midpointKernel_of_ge ht.1]
  rw [← integral_add_adjacent_intervals hKL hKR, ← integral_add_adjacent_intervals hgL hgR,
    eL, eR, midpointRule, ← hc]
  simp only [sub_self, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_div,
    zero_mul, sub_zero] at hL hR
  have hcα : c - α = β - c := by rw [hc]; ring
  have hsq : (c - α) ^ 2 = (β - c) ^ 2 := by rw [hcα]
  linear_combination -hL - hR - (g' c / 2) * hsq

/-- **The midpoint kernel integrates to `(β - α)³/24`** over the panel. -/
theorem integral_midpointKernel {α β : ℝ} (hαβ : α ≤ β) :
    (∫ t in α..β, midpointKernel α β t) = (β - α) ^ 3 / 24 := by
  set c := (α + β) / 2 with hc
  have hαc : α ≤ c := by linarith
  have hcβ : c ≤ β := by linarith
  have hK : ∀ u v, IntervalIntegrable (midpointKernel α β) volume u v := fun u v =>
    (continuous_midpointKernel α β).intervalIntegrable u v
  rw [← integral_add_adjacent_intervals (hK α c) (hK c β)]
  have eL : (∫ t in α..c, midpointKernel α β t) = ∫ t in α..c, (t - α) ^ 2 / 2 := by
    refine integral_congr fun t ht => ?_
    rw [uIcc_of_le hαc] at ht
    exact midpointKernel_of_le ht.2
  have eR : (∫ t in c..β, midpointKernel α β t) = ∫ t in c..β, (β - t) ^ 2 / 2 := by
    refine integral_congr fun t ht => ?_
    rw [uIcc_of_le hcβ] at ht
    exact midpointKernel_of_ge ht.1
  have vL : (∫ t in α..c, (t - α) ^ 2 / 2) = (c - α) ^ 3 / 6 := by
    have hF : ∀ x ∈ uIcc α c, HasDerivAt (fun t : ℝ => (t - α) ^ 3 / 6) ((x - α) ^ 2 / 2) x :=
      fun x _ => ((((hasDerivAt_id' x).sub_const α).pow 3).div_const 6).congr_deriv
        (by push_cast; ring)
    rw [integral_eq_sub_of_hasDerivAt hF (Continuous.intervalIntegrable (by fun_prop) _ _)]
    ring
  have vR : (∫ t in c..β, (β - t) ^ 2 / 2) = (β - c) ^ 3 / 6 := by
    have hF : ∀ x ∈ uIcc c β,
        HasDerivAt (fun t : ℝ => -((β - t) ^ 3 / 6)) ((β - x) ^ 2 / 2) x :=
      fun x _ => (((((hasDerivAt_id' x).const_sub β).pow 3).div_const 6).neg).congr_deriv
        (by push_cast; ring)
    rw [integral_eq_sub_of_hasDerivAt hF (Continuous.intervalIntegrable (by fun_prop) _ _)]
    ring
  rw [eL, eR, vL, vR, hc]
  ring

/-- **The midpoint error in mean value form**: for `a < b` and `g` twice differentiable with
continuous second derivative on `[a, b]`,
`∫_a^b g - (b - a) g((a + b)/2) = ((b - a)/2)³/3 · g''(ξ)` for some `ξ ∈ [a, b]`. The kernel is
nonnegative and integrates to `(b - a)³/24 = h³/3` with `h = (b - a)/2`.

Reference: [quarteroni2000numerical], (9.6). -/
theorem exists_sub_midpoint_eq (hab : a ≤ b) (hg : ∀ x ∈ Icc a b, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Icc a b, HasDerivAt g' (g'' x) x) (hg'' : ContinuousOn g'' (Icc a b)) :
    ∃ ξ ∈ Icc a b, (∫ t in a..b, g t) - midpointRule g a b = ((b - a) / 2) ^ 3 / 3 * g'' ξ := by
  rw [sub_midpoint_eq_integral_peanoKernel hab hg hg' (hg''.intervalIntegrable_of_Icc hab)]
  obtain ⟨ξ, hξ, h⟩ := exists_integral_mul_eq_mul_integral hab
    (continuous_midpointKernel a b).continuousOn hg'' fun t _ => midpointKernel_nonneg a b t
  refine ⟨ξ, hξ, ?_⟩
  rw [h, integral_midpointKernel hab]
  ring

/-- **The composite midpoint error in mean value form**: for `a < b`, `0 < m`, `H = (b - a)/m`
and `g` of class `C²` on `[a, b]`,
`∫_a^b g - midpointSum g a H m = (b - a) H² g''(ξ)/24` for some `ξ ∈ [a, b]`. The panel errors
`H³ g''(ξ_k)/24` are collected by the discrete mean value theorem.

Reference: [quarteroni2000numerical], (9.8). -/
theorem sub_composite_midpoint_eq (hab : a < b) {m : ℕ} (hm : 0 < m) {H : ℝ}
    (hH : H = (b - a) / m) (hg : ∀ x ∈ Icc a b, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Icc a b, HasDerivAt g' (g'' x) x) (hg'' : ContinuousOn g'' (Icc a b)) :
    ∃ ξ ∈ Icc a b, (∫ t in a..b, g t) - midpointSum g a H m = (b - a) / 24 * H ^ 2 * g'' ξ := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hHpos : 0 < H := by rw [hH]; positivity
  set x : ℕ → ℝ := fun j => a + j * H with hxdef
  have hx0 : x 0 = a := by simp [hxdef]
  have hxm : x m = b := by
    have hc : (m : ℝ) * ((b - a) / m) = b - a := by field_simp
    simp only [hxdef, hH, hc]
    ring
  have hxstep : ∀ j : ℕ, x (j + 1) - x j = H := by
    intro j; rw [hxdef]; push_cast; ring
  have hxmono : ∀ j : ℕ, x j ≤ x (j + 1) := fun j => by linarith [hxstep j, hHpos]
  have hxmem : ∀ j ≤ m, x j ∈ Icc a b := by
    intro j hj
    refine ⟨?_, ?_⟩
    · simp only [hxdef]; nlinarith [hHpos.le, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    · have hjm : (j : ℝ) ≤ m := by exact_mod_cast hj
      simp only [hxdef, hH]
      rw [← sub_nonneg]
      have : b - (a + j * ((b - a) / m)) = (m - j) * ((b - a) / m) := by field_simp; ring
      rw [this]
      exact mul_nonneg (by linarith) (by positivity)
  have hxsub : ∀ j < m, Icc (x j) (x (j + 1)) ⊆ Icc a b := fun j hj =>
    Icc_subset_Icc (hxmem j hj.le).1 (hxmem (j + 1) hj).2
  -- the panel errors
  have hpanel : ∀ j < m, ∃ ξ ∈ Icc (x j) (x (j + 1)),
      (∫ t in (x j)..(x (j + 1)), g t) - H * g (a + (j + 1 / 2) * H) = H ^ 3 / 24 * g'' ξ := by
    intro j hj
    obtain ⟨ξ, hξ, h⟩ := exists_sub_midpoint_eq (hxmono j) (fun y hy => hg y (hxsub j hj hy))
      (fun y hy => hg' y (hxsub j hj hy)) (hg''.mono (hxsub j hj))
    refine ⟨ξ, hξ, ?_⟩
    have hmid : (x j + x (j + 1)) / 2 = a + (j + 1 / 2) * H := by
      simp only [hxdef]; push_cast; ring
    rw [midpointRule, hmid, hxstep j] at h
    rw [h]
    ring
  choose! ξ hξmem hξeq using hpanel
  have hint : ∀ j < m, IntervalIntegrable g volume (x j) (x (j + 1)) := by
    intro j hj
    refine ContinuousOn.intervalIntegrable fun y hy => ?_
    exact (hg y (hxsub j hj (by rwa [uIcc_of_le (hxmono j)] at hy))).continuousAt
      |>.continuousWithinAt
  have hsplit : (∫ t in a..b, g t) - midpointSum g a H m
      = ∑ j ∈ Finset.range m, H ^ 3 / 24 * g'' (ξ j) := by
    have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
    rw [hx0, hxm] at hsum
    rw [midpointSum, ← hsum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j hj => hξeq j (Finset.mem_range.mp hj)
  obtain ⟨η, hη, hsum⟩ := exists_sum_mul_eq_of_forall_mem hab.le hg''
    (fun j hj => hxsub j hj (hξmem j hj)) (H ^ 3 / 24)
  refine ⟨η, hη, ?_⟩
  rw [hsplit, hsum]
  have hmH : (m : ℝ) * H = b - a := by rw [hH]; field_simp
  calc (m : ℝ) * (H ^ 3 / 24) * g'' η = (m * H) * H ^ 2 / 24 * g'' η := by ring
    _ = (b - a) / 24 * H ^ 2 * g'' η := by rw [hmH]; ring

/-- **The composite midpoint rule converges** for every continuous integrand as the mesh of the
uniform partitions tends to zero: an instance of the Riemann sum theorem
`Quadrature.tendsto_compositeSum` with the one-node panel rule at the panel midpoint.

Reference: [quarteroni2000numerical], Property 9.1 for `n = 0`. -/
theorem tendsto_midpointSum {N : ℕ → ℕ} {hs : ℕ → ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b)) (hN : ∀ n, 0 < N n) (hhs : ∀ n, hs n = (b - a) / N n)
    (hlim : Tendsto hs atTop (𝓝 0)) :
    Tendsto (fun n => midpointSum g a (hs n) (N n)) atTop (𝓝 (∫ t in a..b, g t)) := by
  have h := tendsto_uniformMesh (g := g) (ω := ![1]) (c := ![1 / 2]) hab hg hN hhs hlim
    (by intro i; fin_cases i; norm_num) (by simp) (by intro i; fin_cases i; norm_num)
  refine h.congr fun n => ?_
  rw [midpointSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Fin.sum_univ_one, Matrix.cons_val_zero]
  ring_nf

end Midpoint

/-! ### Integer nodes, cardinal polynomials and the nodal polynomial -/

section Nodes

variable {n : ℕ}

/-- **A polynomial with the values of a Lagrange basis polynomial is that polynomial**: if
`p` has degree less than the number of nodes, `p (v i) = 1` and `p (v j) = 0` for the other nodes
`j ∈ s`, then `p = Lagrange.basis s v i`. -/
theorem _root_.Lagrange.eq_basis_of_eval {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {v : ι → F} (hvs : Set.InjOn v s) {p : F[X]} (hp : p.degree < s.card)
    {i : ι} (hi : i ∈ s) (h : ∀ j ∈ s, p.eval (v j) = if j = i then 1 else 0) :
    p = Lagrange.basis s v i := by
  refine Polynomial.eq_of_degrees_lt_of_eval_index_eq s hvs hp ?_ fun j hj => ?_
  · rw [Lagrange.degree_basis hvs hi]
    exact_mod_cast Nat.sub_lt (Finset.card_pos.2 ⟨i, hi⟩) one_pos
  · rw [h j hj]
    split_ifs with hji
    · rw [hji, Lagrange.eval_basis_self hvs hi]
    · rw [Lagrange.eval_basis_of_ne (Ne.symm hji) hj]

/-- **The integer nodes** `0, 1, …, n`, the reference nodes of every Newton–Cotes rule. -/
def intNode (n : ℕ) (i : Fin (n + 1)) : ℝ := (i : ℕ)

@[simp]
theorem intNode_apply (i : Fin (n + 1)) : intNode n i = (i : ℕ) := rfl

/-- The integer nodes are distinct. -/
theorem intNode_injective (n : ℕ) : Function.Injective (intNode n) := fun _ _ h =>
  Fin.ext (Nat.cast_injective (R := ℝ) h)

/-- The reflected node: `intNode n (Fin.rev i) = n - intNode n i`. -/
theorem intNode_rev (i : Fin (n + 1)) : intNode n (Fin.rev i) = n - intNode n i := by
  simp only [intNode_apply, Fin.val_rev]
  have hi : (i : ℕ) + 1 ≤ n + 1 := i.2
  rw [Nat.cast_sub hi]
  push_cast
  ring

/-- **The cardinal polynomials** at the integer nodes,
`φ_i(t) = ∏_{k ≠ i} (t - k)/(i - k)`: the Lagrange basis polynomials of `0, …, n`. -/
noncomputable def cardinalPoly (n : ℕ) (i : Fin (n + 1)) : ℝ[X] :=
  Lagrange.basis Finset.univ (intNode n) i

/-- The cardinal polynomial has degree at most `n`. -/
theorem degree_cardinalPoly_lt (i : Fin (n + 1)) : (cardinalPoly n i).degree < n + 1 := by
  rw [cardinalPoly, Lagrange.degree_basis (intNode_injective n).injOn (Finset.mem_univ i)]
  simp only [Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel]
  exact_mod_cast Nat.lt_succ_self n

/-- The cardinal polynomial `φ_i` takes the value `1` at `i` and `0` at the other integer nodes. -/
theorem cardinalPoly_eval_intNode (i j : Fin (n + 1)) :
    (cardinalPoly n i).eval (intNode n j) = if j = i then 1 else 0 := by
  split_ifs with h
  · rw [h, cardinalPoly, Lagrange.eval_basis_self (intNode_injective n).injOn (Finset.mem_univ i)]
  · rw [cardinalPoly, Lagrange.eval_basis_of_ne (Ne.symm h) (Finset.mem_univ j)]

/-- The reflection `t ↦ n - t` carries `φ_i` to `φ_{n-i}`. -/
theorem cardinalPoly_comp_sub (i : Fin (n + 1)) :
    (cardinalPoly n i).comp (C (n : ℝ) - X) = cardinalPoly n (Fin.rev i) := by
  refine Lagrange.eq_basis_of_eval (intNode_injective n).injOn ?_ (Finset.mem_univ _)
    fun j _ => ?_
  · refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
    have h1 : (cardinalPoly n i).natDegree ≤ n :=
      Polynomial.natDegree_le_of_degree_le (Order.le_of_lt_succ (degree_cardinalPoly_lt i))
    have h2 : (C (n : ℝ) - X).natDegree ≤ 1 := by
      rw [show C (n : ℝ) - X = C (-1) * X + C (n : ℝ) by simp; ring]
      exact Polynomial.natDegree_linear_le
    have := Polynomial.natDegree_comp_le (p := cardinalPoly n i) (q := C (n : ℝ) - X)
    simp only [Finset.card_univ, Fintype.card_fin]
    exact_mod_cast lt_of_le_of_lt this (by nlinarith)
  · rw [Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X,
      ← intNode_rev, cardinalPoly_eval_intNode]
    simp only [Fin.rev_eq_iff]

/-- The value of `φ_i` at `n - t` is the value of `φ_{n-i}` at `t`. -/
theorem cardinalPoly_eval_sub (i : Fin (n + 1)) (t : ℝ) :
    (cardinalPoly n i).eval (n - t) = (cardinalPoly n (Fin.rev i)).eval t := by
  rw [← cardinalPoly_comp_sub, Polynomial.eval_comp]
  simp

/-- The cardinal polynomials sum to `1`. -/
theorem sum_cardinalPoly (n : ℕ) : ∑ i, cardinalPoly n i = 1 :=
  Lagrange.sum_basis (intNode_injective n).injOn Finset.univ_nonempty

/-- **The nodal polynomial at the integer nodes**, `π_{n+1}(t) = ∏_{i ≤ n} (t - i)`. -/
noncomputable def intNodal (n : ℕ) : ℝ[X] := ∏ i : Fin (n + 1), (X - C (intNode n i))

/-- The nodal polynomial as a product of real factors. -/
theorem intNodal_eval (t : ℝ) : (intNodal n).eval t = ∏ i : Fin (n + 1), (t - (i : ℕ)) := by
  simp [intNodal, Polynomial.eval_prod]

/-- The nodal polynomial as a product over `Finset.range (n + 1)`. -/
theorem intNodal_eval_eq_prod_range (t : ℝ) :
    (intNodal n).eval t = ∏ i ∈ Finset.range (n + 1), (t - (i : ℕ)) := by
  rw [intNodal_eval, Finset.prod_range]

/-- The nodal polynomial vanishes at the integer nodes. -/
theorem intNodal_eval_intNode (i : Fin (n + 1)) : (intNodal n).eval (intNode n i) = 0 := by
  rw [intNodal_eval]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

/-- The nodal polynomial vanishes at every natural number `k ≤ n`. -/
theorem intNodal_eval_natCast {k : ℕ} (hk : k ≤ n) : (intNodal n).eval (k : ℝ) = 0 :=
  intNodal_eval_intNode ⟨k, Nat.lt_succ_of_le hk⟩

/-- **Antisymmetry of the nodal polynomial about the midpoint** `n/2`:
`π_{n+1}(n - t) = (-1)^{n+1} π_{n+1}(t)`; for even `n` it is odd about the midpoint, for odd `n`
even. -/
theorem intNodal_comp_sub (t : ℝ) :
    (intNodal n).eval (n - t) = (-1) ^ (n + 1) * (intNodal n).eval t := by
  rw [intNodal_eval, intNodal_eval]
  have e : ∀ i : Fin (n + 1), ((n : ℝ) - t - i) = -(t - ((Fin.rev i : ℕ) : ℝ)) := by
    intro i
    rw [Fin.val_rev, Nat.cast_sub i.2]
    push_cast
    ring
  rw [Finset.prod_congr rfl fun i _ => e i, Finset.prod_neg, Finset.card_univ, Fintype.card_fin]
  congr 1
  exact Equiv.prod_comp Fin.revPerm (fun i : Fin (n + 1) => t - (i : ℕ))

/-- **The shift identity** `π_{n+1}(t + 1) (t - n) = π_{n+1}(t) (t + 1)`: shifting the
argument by one moves the factor `t + 1` in and the factor `t - n` out. -/
theorem intNodal_eval_add_one_mul (t : ℝ) :
    (intNodal n).eval (t + 1) * (t - n) = (intNodal n).eval t * (t + 1) := by
  rw [intNodal_eval, intNodal_eval, Fin.prod_univ_succ, Fin.prod_univ_castSucc]
  simp only [Fin.val_zero, Nat.cast_zero, sub_zero, Fin.val_succ, Fin.val_castSucc, Fin.val_last]
  have e : ∀ i : Fin n, (t + 1 - ((i : ℕ) + 1 : ℕ)) = t - (i : ℕ) := by
    intro i; push_cast; ring
  rw [Finset.prod_congr rfl fun i _ => e i]
  ring

end Nodes

/-! ### The weights -/

section Weights

variable {n : ℕ}

/-- **The closed Newton–Cotes weights** `w_i = ∫_0^n φ_i(t) dt`.

Reference: [quarteroni2000numerical], §9.3 (Table 9.2, left). -/
noncomputable def newtonCotesWeight (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  ∫ t in (0 : ℝ)..n, (cardinalPoly n i).eval t

/-- **The open Newton–Cotes weights** `w_i = ∫_{-1}^{n+1} φ_i(t) dt`.

Reference: [quarteroni2000numerical], §9.3 (Table 9.2, right). -/
noncomputable def openNewtonCotesWeight (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  ∫ t in (-1 : ℝ)..(n + 1), (cardinalPoly n i).eval t

/-- **Symmetry of the closed weights**, `w_{n-i} = w_i`: the substitution `t ↦ n - t` carries
`φ_i` to `φ_{n-i}` and `[0, n]` to itself. -/
theorem newtonCotesWeight_symm (i : Fin (n + 1)) :
    newtonCotesWeight n (Fin.rev i) = newtonCotesWeight n i := by
  unfold newtonCotesWeight
  have h := integral_comp_sub_left (fun t => (cardinalPoly n i).eval t) (a := 0) (b := n) (n : ℝ)
  simp only [sub_self, sub_zero] at h
  rw [← h]
  exact integral_congr fun t _ => (cardinalPoly_eval_sub i t).symm

/-- **Symmetry of the open weights**, `w_{n-i} = w_i`. -/
theorem openNewtonCotesWeight_symm (i : Fin (n + 1)) :
    openNewtonCotesWeight n (Fin.rev i) = openNewtonCotesWeight n i := by
  unfold openNewtonCotesWeight
  have h := integral_comp_sub_left (fun t => (cardinalPoly n i).eval t) (a := -1) (b := n + 1)
    (n : ℝ)
  rw [show (n : ℝ) - (n + 1) = -1 by ring, show (n : ℝ) - (-1) = n + 1 by ring] at h
  rw [← h]
  exact integral_congr fun t _ => (cardinalPoly_eval_sub i t).symm

/-- The sum of the cardinal polynomials integrates to the length of the interval. -/
private theorem sum_integral_cardinalPoly (n : ℕ) (u v : ℝ) :
    ∑ i, ∫ t in u..v, (cardinalPoly n i).eval t = v - u := by
  rw [← integral_finsetSum fun i _ => (Polynomial.continuous _).intervalIntegrable _ _]
  have e : ∀ t, ∑ i, (cardinalPoly n i).eval t = 1 := by
    intro t
    rw [← Polynomial.eval_finsetSum, sum_cardinalPoly, Polynomial.eval_one]
  simp [e]

/-- **The closed weights sum to `n`**: the cardinal polynomials sum to `1`. -/
theorem sum_newtonCotesWeight (n : ℕ) : ∑ i, newtonCotesWeight n i = n := by
  unfold newtonCotesWeight
  rw [sum_integral_cardinalPoly, sub_zero]

/-- **The open weights sum to `n + 2`**. -/
theorem sum_openNewtonCotesWeight (n : ℕ) : ∑ i, openNewtonCotesWeight n i = n + 2 := by
  unfold openNewtonCotesWeight
  rw [sum_integral_cardinalPoly]
  ring

end Weights

/-! ### The rules -/

section Rules

variable {n : ℕ} {a b : ℝ} {f : ℝ → ℝ}

/-- **The closed Newton–Cotes rule** with `n + 1` nodes on `[a, b]`,
`h ∑_{i ≤ n} w_i f(a + i h)`, `h = (b - a)/n`. It is meaningful for `n ≥ 1`; for `n = 0` it is
the junk value `0`.

Reference: [quarteroni2000numerical], §9.3. -/
noncomputable def closedNewtonCotes (n : ℕ) (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (b - a) / n * ∑ i : Fin (n + 1), newtonCotesWeight n i * f (a + i * ((b - a) / n))

/-- **The open Newton–Cotes rule** with `n + 1` interior nodes on `[a, b]`,
`h ∑_{i ≤ n} w_i f(a + (i + 1) h)`, `h = (b - a)/(n + 2)`.

Reference: [quarteroni2000numerical], §9.3. -/
noncomputable def openNewtonCotes (n : ℕ) (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (b - a) / (n + 2) * ∑ i : Fin (n + 1),
    openNewtonCotesWeight n i * f (a + (i + 1) * ((b - a) / (n + 2)))

/-- **The composite closed Newton–Cotes rule** on `m` panels of `[a, b]`: the closed rule applied
on each panel `[a + j H, a + (j + 1) H]`, `H = (b - a)/m`.

Reference: [quarteroni2000numerical], (9.25). -/
noncomputable def compositeNewtonCotes (n : ℕ) (f : ℝ → ℝ) (a b : ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range m,
    closedNewtonCotes n f (a + j * ((b - a) / m)) (a + (j + 1) * ((b - a) / m))

/-- The Lagrange basis polynomial of an affine image of nodes is the basis polynomial of the
nodes composed with the affine map: `l_i(c + h t) = φ_i(t)` for `x_i = c + h v_i`, `h ≠ 0`. -/
theorem _root_.Lagrange.basis_comp_affine {v : Fin (n + 1) → ℝ} (hv : Function.Injective v)
    {c h : ℝ} (hh : h ≠ 0) (i : Fin (n + 1)) :
    (Lagrange.basis Finset.univ (fun k => c + h * v k) i).comp (C h * X + C c)
      = Lagrange.basis Finset.univ v i := by
  have hinj : Function.Injective fun k => c + h * v k := fun k l hkl => by
    have : h * v k = h * v l := by simpa using hkl
    exact hv (mul_left_cancel₀ hh this)
  refine Lagrange.eq_basis_of_eval hv.injOn ?_ (Finset.mem_univ _) fun j _ => ?_
  · refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
    have h1 : (Lagrange.basis Finset.univ (fun k => c + h * v k) i).natDegree ≤ n := by
      rw [Lagrange.natDegree_basis hinj.injOn (Finset.mem_univ i)]
      simp
    have h2 : (C h * X + C c).natDegree ≤ 1 := Polynomial.natDegree_linear_le
    have := Polynomial.natDegree_comp_le (p := Lagrange.basis Finset.univ (fun k => c + h * v k) i)
      (q := C h * X + C c)
    simp only [Finset.card_univ, Fintype.card_fin]
    exact_mod_cast lt_of_le_of_lt this (by nlinarith)
  · rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_C, add_comm (h * v j) c]
    split_ifs with hji
    · rw [hji]
      exact Lagrange.eval_basis_self (v := fun k => c + h * v k) hinj.injOn (Finset.mem_univ i)
    · exact Lagrange.eval_basis_of_ne (v := fun k => c + h * v k) (Ne.symm hji)
        (Finset.mem_univ j)

/-- The integral over `[a, b]` of a Lagrange basis polynomial at the equispaced nodes
`a + i h`, `h = (b - a)/n`, is `h` times the closed Newton–Cotes weight. -/
theorem integral_basis_eq_mul_newtonCotesWeight (hn : 0 < n) (hab : a < b) (i : Fin (n + 1)) :
    (∫ t in a..b,
        (Lagrange.basis Finset.univ (fun k : Fin (n + 1) => a + k * ((b - a) / n)) i).eval t)
      = (b - a) / n * newtonCotesWeight n i := by
  set h := (b - a) / n with hh
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hpos : 0 < h := by rw [hh]; positivity
  have hcomp := Lagrange.basis_comp_affine (intNode_injective n) (c := a) (h := h) hpos.ne' i
  have hnodes : (fun k : Fin (n + 1) => a + h * intNode n k)
      = fun k : Fin (n + 1) => a + k * ((b - a) / n) := by
    funext k; simp only [intNode_apply, hh]; ring
  rw [hnodes] at hcomp
  have hcov := integral_comp_mul_add
    (fun t => (Lagrange.basis Finset.univ (fun k : Fin (n + 1) => a + k * ((b - a) / n)) i).eval t)
    (a := 0) (b := n) hpos.ne' a
  simp only [mul_zero, zero_add, smul_eq_mul] at hcov
  have hend : h * n + a = b := by rw [hh, div_mul_cancel₀ _ hnR.ne']; ring
  rw [hend] at hcov
  have hcomp' : (Lagrange.basis Finset.univ (fun k : Fin (n + 1) => a + k * ((b - a) / n)) i).comp
      (C h * X + C a) = cardinalPoly n i := hcomp
  rw [newtonCotesWeight, ← hcomp']
  rw [show (∫ t in (0 : ℝ)..n, ((Lagrange.basis Finset.univ
      (fun k : Fin (n + 1) => a + k * ((b - a) / n)) i).comp (C h * X + C a)).eval t)
      = ∫ t in (0 : ℝ)..n, (Lagrange.basis Finset.univ
        (fun k : Fin (n + 1) => a + k * ((b - a) / n)) i).eval (h * t + a) from
      integral_congr fun t _ => by simp [Polynomial.eval_comp]]
  rw [hcov, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]

/-- **The closed rule is the Lagrange quadrature formula at the equispaced nodes**: for `0 < n`
and `a < b`, `closedNewtonCotes n f a b = ∑ i, (∫_a^b l_i) f(x_i)` with `x_i = a + i h` and
`l_i` the Lagrange basis polynomials of the `x_i`. The weights `∫ l_i = h w_i` depend on the
interval only through the factor `h`.

Reference: [quarteroni2000numerical], §9.3, the unnumbered display for `α_i`. -/
theorem closedNewtonCotes_eq_sum_integral_basis (hn : 0 < n) (hab : a < b) (f : ℝ → ℝ) :
    closedNewtonCotes n f a b
      = ∑ i : Fin (n + 1), (∫ t in a..b,
          (Lagrange.basis Finset.univ (fun k : Fin (n + 1) => a + k * ((b - a) / n)) i).eval t)
        * f (a + i * ((b - a) / n)) := by
  rw [closedNewtonCotes, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [integral_basis_eq_mul_newtonCotesWeight hn hab i]; ring

/-- The integral over `[a, b]` of a Lagrange basis polynomial at the open equispaced nodes
`a + (i + 1) h`, `h = (b - a)/(n + 2)`, is `h` times the open Newton–Cotes weight. -/
theorem integral_basis_eq_mul_openNewtonCotesWeight (hab : a < b) (i : Fin (n + 1)) :
    (∫ t in a..b, (Lagrange.basis Finset.univ
        (fun k : Fin (n + 1) => a + (k + 1) * ((b - a) / (n + 2))) i).eval t)
      = (b - a) / (n + 2) * openNewtonCotesWeight n i := by
  set h := (b - a) / (n + 2) with hh
  have hpos : 0 < h := by rw [hh]; positivity
  have hcomp := Lagrange.basis_comp_affine (intNode_injective n) (c := a + h) (h := h) hpos.ne' i
  have hnodes : (fun k : Fin (n + 1) => a + h + h * intNode n k)
      = fun k : Fin (n + 1) => a + (k + 1) * ((b - a) / (n + 2)) := by
    funext k; simp only [intNode_apply, hh]; ring
  rw [hnodes] at hcomp
  have hcov := integral_comp_mul_add
    (fun t => (Lagrange.basis Finset.univ
      (fun k : Fin (n + 1) => a + (k + 1) * ((b - a) / (n + 2))) i).eval t)
    (a := -1) (b := n + 1) hpos.ne' (a + h)
  simp only [smul_eq_mul] at hcov
  have hstart : h * (-1) + (a + h) = a := by ring
  have hend : h * (n + 1) + (a + h) = b := by rw [hh]; field_simp; ring
  rw [hstart, hend] at hcov
  have hcomp' : (Lagrange.basis Finset.univ
      (fun k : Fin (n + 1) => a + (k + 1) * ((b - a) / (n + 2))) i).comp
      (C h * X + C (a + h)) = cardinalPoly n i := hcomp
  rw [openNewtonCotesWeight, ← hcomp']
  rw [show (∫ t in (-1 : ℝ)..(n + 1), ((Lagrange.basis Finset.univ
      (fun k : Fin (n + 1) => a + (k + 1) * ((b - a) / (n + 2))) i).comp
        (C h * X + C (a + h))).eval t)
      = ∫ t in (-1 : ℝ)..(n + 1), (Lagrange.basis Finset.univ
        (fun k : Fin (n + 1) => a + (k + 1) * ((b - a) / (n + 2))) i).eval (h * t + (a + h)) from
      integral_congr fun t _ => by simp [Polynomial.eval_comp]]
  rw [hcov, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]

/-- **The open rule is the Lagrange quadrature formula at the interior equispaced nodes.** -/
theorem openNewtonCotes_eq_sum_integral_basis (hab : a < b) (f : ℝ → ℝ) :
    openNewtonCotes n f a b
      = ∑ i : Fin (n + 1), (∫ t in a..b, (Lagrange.basis Finset.univ
          (fun k : Fin (n + 1) => a + (k + 1) * ((b - a) / (n + 2))) i).eval t)
        * f (a + (i + 1) * ((b - a) / (n + 2))) := by
  rw [openNewtonCotes, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [integral_basis_eq_mul_openNewtonCotesWeight hab i]; ring

/-- A Lagrange quadrature formula integrates the polynomials of degree at most `n` exactly: such a
polynomial is its own interpolant. -/
theorem integral_eq_sum_integral_basis_mul {v : Fin (n + 1) → ℝ} (hv : Function.Injective v)
    (u w : ℝ) {p : ℝ[X]} (hp : p.degree ≤ n) :
    (∫ t in u..w, p.eval t)
      = ∑ i, (∫ t in u..w, (Lagrange.basis Finset.univ v i).eval t) * p.eval (v i) := by
  have hdeg : p.degree < (Finset.univ : Finset (Fin (n + 1))).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt hp (by exact_mod_cast Nat.lt_succ_self n)
  have heq := Lagrange.eq_interpolate hv.injOn hdeg
  conv_lhs => rw [heq]
  simp only [Lagrange.interpolate_apply, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C]
  rw [integral_finsetSum fun i _ =>
    ((Polynomial.continuous _).const_mul _).intervalIntegrable _ _]
  exact Finset.sum_congr rfl fun i _ => by rw [integral_const_mul]; ring

/-- **Exactness of the closed rule to degree `n`**: for `0 < n`, `a < b` and a polynomial `p` of
degree at most `n`, `∫_a^b p = closedNewtonCotes n p a b`.

Reference: [quarteroni2000numerical], §9.1 and §9.3. -/
theorem integral_eq_closedNewtonCotes_of_degree_le (hn : 0 < n) (hab : a < b) {p : ℝ[X]}
    (hp : p.degree ≤ n) :
    (∫ t in a..b, p.eval t) = closedNewtonCotes n (fun t => p.eval t) a b := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hinj : Function.Injective fun k : Fin (n + 1) => a + k * ((b - a) / n) := by
    intro k l hkl
    have : (k : ℝ) = l := by
      have h := hkl
      simp only at h
      have hne : (b - a) / n ≠ 0 := by positivity
      exact mul_right_cancel₀ hne (by linarith)
    exact Fin.ext (by exact_mod_cast this)
  rw [closedNewtonCotes_eq_sum_integral_basis hn hab]
  exact integral_eq_sum_integral_basis_mul hinj a b hp

/-- **Exactness of the open rule to degree `n`**. -/
theorem integral_eq_openNewtonCotes_of_degree_le (hab : a < b) {p : ℝ[X]} (hp : p.degree ≤ n) :
    (∫ t in a..b, p.eval t) = openNewtonCotes n (fun t => p.eval t) a b := by
  have hinj : Function.Injective fun k : Fin (n + 1) => a + (k + 1) * ((b - a) / (n + 2)) := by
    intro k l hkl
    have : (k : ℝ) = l := by
      have h := hkl
      simp only at h
      have hne : (b - a) / (n + 2) ≠ 0 := by positivity
      exact mul_right_cancel₀ hne (by linarith)
    exact Fin.ext (by exact_mod_cast this)
  rw [openNewtonCotes_eq_sum_integral_basis hab]
  exact integral_eq_sum_integral_basis_mul hinj a b hp

/-- **Exactness on the reference interval**: `∫_0^n p = ∑ w_i p(i)` for `p` of degree at most
`n` — the closed weights are the solution of the moment equations. -/
theorem integral_eq_sum_newtonCotesWeight_mul (hn : 0 < n) {p : ℝ[X]} (hp : p.degree ≤ n) :
    (∫ t in (0 : ℝ)..n, p.eval t)
      = ∑ i : Fin (n + 1), newtonCotesWeight n i * p.eval (intNode n i) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [integral_eq_closedNewtonCotes_of_degree_le hn hnR hp, closedNewtonCotes]
  simp only [sub_zero, div_self hnR.ne', one_mul, mul_one, zero_add, intNode_apply]

/-- **Exactness on the reference interval, open rules**: `∫_{-1}^{n+1} p = ∑ w_i p(i)` for `p`
of degree at most `n`. -/
theorem integral_eq_sum_openNewtonCotesWeight_mul {p : ℝ[X]} (hp : p.degree ≤ n) :
    (∫ t in (-1 : ℝ)..(n + 1), p.eval t)
      = ∑ i : Fin (n + 1), openNewtonCotesWeight n i * p.eval (intNode n i) := by
  rw [integral_eq_openNewtonCotes_of_degree_le (by linarith) hp, openNewtonCotes]
  have h : ((n : ℝ) + 1 - -1) / (n + 2) = 1 := by field_simp; ring
  simp only [h, one_mul, mul_one, intNode_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  ring

/-- The rule is linear in the integrand. -/
theorem closedNewtonCotes_add_mul (f g : ℝ → ℝ) (c a b : ℝ) :
    closedNewtonCotes n (fun t => f t + c * g t) a b
      = closedNewtonCotes n f a b + c * closedNewtonCotes n g a b := by
  simp only [closedNewtonCotes, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The open rule is linear in the integrand. -/
theorem openNewtonCotes_add_mul (f g : ℝ → ℝ) (c a b : ℝ) :
    openNewtonCotes n (fun t => f t + c * g t) a b
      = openNewtonCotes n f a b + c * openNewtonCotes n g a b := by
  simp only [openNewtonCotes, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The nodes of the closed rule lie in `[a, b]`. -/
theorem closedNewtonCotes_node_mem (hn : 0 < n) (hab : a ≤ b) (i : Fin (n + 1)) :
    a + i * ((b - a) / n) ∈ Icc a b := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hi : (i : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp i.2
  have h0 : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _
  have hh : 0 ≤ (b - a) / n := by
    have : 0 ≤ b - a := by linarith
    positivity
  refine ⟨by nlinarith, ?_⟩
  have : (i : ℝ) * ((b - a) / n) ≤ n * ((b - a) / n) := mul_le_mul_of_nonneg_right hi hh
  rw [mul_div_cancel₀ _ hnR.ne'] at this
  linarith

/-- The nodes of the closed rule are distinct. -/
theorem closedNewtonCotes_node_injective (hn : 0 < n) (hab : a < b) :
    Function.Injective fun k : Fin (n + 1) => a + k * ((b - a) / n) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  intro k l hkl
  have : (k : ℝ) = l := by
    have h := hkl
    simp only at h
    have hne : (b - a) / n ≠ 0 := by positivity
    exact mul_right_cancel₀ hne (by linarith)
  exact Fin.ext (by exact_mod_cast this)

/-- **The closed rule in the functional vocabulary of `Numlib/Approximation/Quadrature`**: on
`X = [a, b]` with the integral functional `ContinuousMap.integralIccCLM`, the weights `h w_i` at
the nodes `a + i h` are exact to degree `n`, `Quadrature.IsExactOn`. -/
theorem isExactOn_closedNewtonCotes (hn : 0 < n) (hab : a < b) :
    IsExactOn (ContinuousMap.integralIccCLM hab.le b)
      (fun i : Fin (n + 1) => (b - a) / n * newtonCotesWeight n i)
      (fun i : Fin (n + 1) =>
        (⟨a + i * ((b - a) / n), closedNewtonCotes_node_mem hn hab.le i⟩ : Icc a b)) n := by
  intro q hq
  obtain ⟨p, hp, hqp⟩ := mem_polyLE_iff.mp hq
  rw [functional_apply, ContinuousMap.integralIccCLM_apply]
  have hlhs : ∑ i : Fin (n + 1), (b - a) / n * newtonCotesWeight n i
      * q ⟨a + i * ((b - a) / n), closedNewtonCotes_node_mem hn hab.le i⟩
      = closedNewtonCotes n (fun t => p.eval t) a b := by
    rw [closedNewtonCotes, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hqp]; ring
  rw [hlhs, ← integral_eq_closedNewtonCotes_of_degree_le hn hab hp]
  refine integral_congr fun t ht => ?_
  rw [uIcc_of_le hab.le] at ht
  rw [ContinuousMap.coe_IccExtend, IccExtend_of_mem hab.le _ ht, hqp]

/-- **The closed rule is interpolatory**, `Quadrature.IsInterpolatory`, for the integral
functional on `C([a, b], ℝ)`: its weights are the integrals of the Lagrange basis functions of
its nodes. -/
theorem isInterpolatory_closedNewtonCotes (hn : 0 < n) (hab : a < b) :
    IsInterpolatory (ContinuousMap.integralIccCLM hab.le b)
      (fun i : Fin (n + 1) => (b - a) / n * newtonCotesWeight n i)
      (fun i : Fin (n + 1) =>
        (⟨a + i * ((b - a) / n), closedNewtonCotes_node_mem hn hab.le i⟩ : Icc a b)) := by
  have hinj : Function.Injective fun i : Fin (n + 1) =>
      (⟨a + i * ((b - a) / n), closedNewtonCotes_node_mem hn hab.le i⟩ : Icc a b) :=
    fun i j h => closedNewtonCotes_node_injective hn hab (congrArg Subtype.val h)
  exact (isInterpolatory_iff_isExactOn hinj).2 (isExactOn_closedNewtonCotes hn hab)

/-- The nodes of the open rule lie in `[a, b]`. -/
theorem openNewtonCotes_node_mem (hab : a ≤ b) (i : Fin (n + 1)) :
    a + ((i : ℕ) + 1) * ((b - a) / (n + 2)) ∈ Icc a b := by
  have hnR : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hi : ((i : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp i.2
  have h0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
  have hh : 0 ≤ (b - a) / ((n : ℝ) + 2) := by
    have : 0 ≤ b - a := by linarith
    positivity
  refine ⟨by nlinarith, ?_⟩
  have h1 : (((i : ℕ) : ℝ) + 1) * ((b - a) / ((n : ℝ) + 2))
      ≤ ((n : ℝ) + 2) * ((b - a) / ((n : ℝ) + 2)) :=
    mul_le_mul_of_nonneg_right (by linarith) hh
  rw [mul_div_cancel₀ _ hnR.ne'] at h1
  linarith

/-- The nodes of the open rule are distinct. -/
theorem openNewtonCotes_node_injective (hab : a < b) :
    Function.Injective fun k : Fin (n + 1) => a + ((k : ℕ) + 1) * ((b - a) / (n + 2)) := by
  intro k l hkl
  have hne : (b - a) / ((n : ℝ) + 2) ≠ 0 := by positivity
  have h := hkl
  simp only at h
  have : ((k : ℕ) : ℝ) + 1 = ((l : ℕ) : ℝ) + 1 := mul_right_cancel₀ hne (by linarith)
  exact Fin.ext (by exact_mod_cast (by linarith : ((k : ℕ) : ℝ) = ((l : ℕ) : ℝ)))

/-- An odd power about the midpoint of `[a, b]` integrates to zero over `[a, b]`. -/
theorem integral_pow_sub_midpoint_of_odd {k : ℕ} (hk : Odd k) (a b : ℝ) :
    (∫ t in a..b, (t - (a + b) / 2) ^ k) = 0 := by
  rw [integral_comp_sub_right (fun t => t ^ k), integral_pow]
  have hab : a - (a + b) / 2 = -(b - (a + b) / 2) := by ring
  rw [hab, Even.neg_pow (hk.add_one), sub_self, zero_div]

/-- **Even `n`: the closed rule is exact to degree `n + 1`**, by symmetry alone. A polynomial of
degree at most `n + 1` is one of degree at most `n` plus a multiple of `(x - (a + b)/2)^{n+1}`,
an odd power about the midpoint, which integrates to zero and which the rule also sends to zero
because its nodes are symmetric about the midpoint and its weights satisfy
`newtonCotesWeight_symm`.

Reference: [quarteroni2000numerical], Theorem 9.2 (the degree of exactness `n + 1`). -/
theorem integral_eq_closedNewtonCotes_of_even (hn : Even n) (hn0 : 0 < n) (hab : a < b)
    {p : ℝ[X]} (hp : p.degree ≤ n + 1) :
    (∫ t in a..b, p.eval t) = closedNewtonCotes n (fun t => p.eval t) a b := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  set c : ℝ := (a + b) / 2 with hc
  set r : ℝ[X] := (X - C c) ^ (n + 1) with hr
  set q : ℝ[X] := p - C (p.coeff (n + 1)) * r with hq
  have hrmonic : r.Monic := (monic_X_sub_C c).pow _
  have hrnat : r.natDegree = n + 1 := by rw [hr, natDegree_pow, natDegree_X_sub_C, mul_one]
  have hqdeg : q.degree ≤ n := by
    rw [degree_le_iff_coeff_zero]
    intro m hm
    have hm' : n + 1 ≤ m := by
      have : n < m := by exact_mod_cast hm
      omega
    rw [hq, coeff_sub, coeff_C_mul]
    rcases eq_or_lt_of_le hm' with h | h
    · rw [← h, ← hrnat, hrmonic.coeff_natDegree, hrnat, mul_one, sub_self]
    · have hpm : p.coeff m = 0 :=
        coeff_eq_zero_of_degree_lt (lt_of_le_of_lt hp (by exact_mod_cast h))
      have hrm : r.coeff m = 0 := coeff_eq_zero_of_natDegree_lt (by rw [hrnat]; exact h)
      rw [hpm, hrm, mul_zero, sub_self]
  have hpq : ∀ t, p.eval t = q.eval t + p.coeff (n + 1) * r.eval t := by
    intro t
    simp only [hq, eval_sub, eval_mul, eval_C]
    ring
  have hodd : Odd (n + 1) := hn.add_one
  -- the odd power integrates to zero
  have hrint : (∫ t in a..b, r.eval t) = 0 := by
    have : (fun t => r.eval t) = fun t => (t - (a + b) / 2) ^ (n + 1) := by
      funext t; simp [hr, hc]
    rw [this, integral_pow_sub_midpoint_of_odd hodd]
  -- and the rule sends it to zero, by symmetry
  have hrrule : closedNewtonCotes n (fun t => r.eval t) a b = 0 := by
    have hnodes : ∀ i : Fin (n + 1),
        a + (Fin.rev i : ℕ) * ((b - a) / n) - c = -(a + i * ((b - a) / n) - c) := by
      intro i
      rw [Fin.val_rev, Nat.cast_sub i.2, hc]
      push_cast
      field_simp
      ring
    have hsum : ∑ i : Fin (n + 1), newtonCotesWeight n i * r.eval (a + i * ((b - a) / n))
        = -∑ i : Fin (n + 1), newtonCotesWeight n i * r.eval (a + i * ((b - a) / n)) := by
      conv_lhs => rw [← Equiv.sum_comp Fin.revPerm]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Fin.revPerm_apply, newtonCotesWeight_symm, hr, eval_pow, eval_sub, eval_X,
        eval_C]
      rw [hnodes i, Odd.neg_pow hodd]
      ring
    have : ∑ i : Fin (n + 1), newtonCotesWeight n i * r.eval (a + i * ((b - a) / n)) = 0 := by
      linarith
    rw [closedNewtonCotes, this, mul_zero]
  have hint : (fun t => p.eval t) = fun t => q.eval t + p.coeff (n + 1) * r.eval t := by
    funext t; exact hpq t
  rw [hint, closedNewtonCotes_add_mul, ← integral_eq_closedNewtonCotes_of_degree_le hn0 hab hqdeg,
    hrrule, mul_zero, add_zero, integral_add ((Polynomial.continuous _).intervalIntegrable _ _)
      (((Polynomial.continuous _).const_mul _).intervalIntegrable _ _),
    integral_const_mul, hrint, mul_zero, add_zero]

/-- **Even `n`: the open rule is exact to degree `n + 1`**, by symmetry alone, exactly as
`Quadrature.integral_eq_closedNewtonCotes_of_even`: a polynomial of degree at most `n + 1` is one
of degree at most `n` plus a multiple of `(x - (a + b)/2)^{n+1}`, an odd power about the midpoint,
which integrates to zero and which the rule sends to zero because its nodes `a + (i + 1) h`,
`h = (b - a)/(n + 2)`, are symmetric about the midpoint and its weights satisfy
`Quadrature.openNewtonCotesWeight_symm`.

Reference: [quarteroni2000numerical], Theorem 9.2 (the degree of exactness `n + 1`). -/
theorem integral_eq_openNewtonCotes_of_even (hn : Even n) (hab : a < b) {p : ℝ[X]}
    (hp : p.degree ≤ n + 1) :
    (∫ t in a..b, p.eval t) = openNewtonCotes n (fun t => p.eval t) a b := by
  set c : ℝ := (a + b) / 2 with hc
  set r : ℝ[X] := (X - C c) ^ (n + 1) with hr
  set q : ℝ[X] := p - C (p.coeff (n + 1)) * r with hq
  have hrmonic : r.Monic := (monic_X_sub_C c).pow _
  have hrnat : r.natDegree = n + 1 := by rw [hr, natDegree_pow, natDegree_X_sub_C, mul_one]
  have hqdeg : q.degree ≤ n := by
    rw [degree_le_iff_coeff_zero]
    intro m hm
    have hm' : n + 1 ≤ m := by
      have : n < m := by exact_mod_cast hm
      omega
    rw [hq, coeff_sub, coeff_C_mul]
    rcases eq_or_lt_of_le hm' with h | h
    · rw [← h, ← hrnat, hrmonic.coeff_natDegree, hrnat, mul_one, sub_self]
    · have hpm : p.coeff m = 0 :=
        coeff_eq_zero_of_degree_lt (lt_of_le_of_lt hp (by exact_mod_cast h))
      have hrm : r.coeff m = 0 := coeff_eq_zero_of_natDegree_lt (by rw [hrnat]; exact h)
      rw [hpm, hrm, mul_zero, sub_self]
  have hpq : ∀ t, p.eval t = q.eval t + p.coeff (n + 1) * r.eval t := by
    intro t
    simp only [hq, eval_sub, eval_mul, eval_C]
    ring
  have hodd : Odd (n + 1) := hn.add_one
  -- the odd power integrates to zero
  have hrint : (∫ t in a..b, r.eval t) = 0 := by
    have : (fun t => r.eval t) = fun t => (t - (a + b) / 2) ^ (n + 1) := by
      funext t; simp [hr, hc]
    rw [this, integral_pow_sub_midpoint_of_odd hodd]
  -- and the rule sends it to zero, by symmetry
  have hrrule : openNewtonCotes n (fun t => r.eval t) a b = 0 := by
    have hnodes : ∀ i : Fin (n + 1),
        a + (((Fin.rev i : Fin (n + 1)) : ℕ) + 1) * ((b - a) / (n + 2)) - c
          = -(a + ((i : ℕ) + 1) * ((b - a) / (n + 2)) - c) := by
      intro i
      rw [Fin.val_rev, Nat.cast_sub i.2, hc]
      push_cast
      field_simp
      ring
    have hsum : ∑ i : Fin (n + 1),
        openNewtonCotesWeight n i * r.eval (a + ((i : ℕ) + 1) * ((b - a) / (n + 2)))
          = -∑ i : Fin (n + 1),
            openNewtonCotesWeight n i * r.eval (a + ((i : ℕ) + 1) * ((b - a) / (n + 2))) := by
      conv_lhs => rw [← Equiv.sum_comp Fin.revPerm]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Fin.revPerm_apply, openNewtonCotesWeight_symm, hr, eval_pow, eval_sub, eval_X,
        eval_C]
      rw [hnodes i, Odd.neg_pow hodd]
      ring
    have hz : ∑ i : Fin (n + 1),
        openNewtonCotesWeight n i * r.eval (a + ((i : ℕ) + 1) * ((b - a) / (n + 2))) = 0 := by
      linarith
    rw [openNewtonCotes, hz, mul_zero]
  have hint : (fun t => p.eval t) = fun t => q.eval t + p.coeff (n + 1) * r.eval t := by
    funext t; exact hpq t
  rw [hint, openNewtonCotes_add_mul, ← integral_eq_openNewtonCotes_of_degree_le hab hqdeg,
    hrrule, mul_zero, add_zero, integral_add ((Polynomial.continuous _).intervalIntegrable _ _)
      (((Polynomial.continuous _).const_mul _).intervalIntegrable _ _),
    integral_const_mul, hrint, mul_zero, add_zero]

/-- **The moment equations of the closed weights**: `∑ w_i i^k = n^{k+1}/(k + 1)` for `k ≤ n`. -/
theorem sum_newtonCotesWeight_mul_pow (hn : 0 < n) {k : ℕ} (hk : k ≤ n) :
    ∑ i : Fin (n + 1), newtonCotesWeight n i * ((i : ℕ) : ℝ) ^ k = (n : ℝ) ^ (k + 1) / (k + 1) := by
  have h := integral_eq_sum_newtonCotesWeight_mul hn (p := X ^ k)
    (by rw [degree_X_pow]; exact_mod_cast hk)
  simp only [eval_pow, eval_X, intNode_apply] at h
  rw [← h, integral_pow, zero_pow (Nat.succ_ne_zero k), sub_zero]

/-- **The moment equations of the open weights**:
`∑ w_i i^k = ((n + 1)^{k+1} - (-1)^{k+1})/(k + 1)` for `k ≤ n`. -/
theorem sum_openNewtonCotesWeight_mul_pow {k : ℕ} (hk : k ≤ n) :
    ∑ i : Fin (n + 1), openNewtonCotesWeight n i * ((i : ℕ) : ℝ) ^ k
      = (((n : ℝ) + 1) ^ (k + 1) - (-1) ^ (k + 1)) / (k + 1) := by
  have h := integral_eq_sum_openNewtonCotesWeight_mul (n := n) (p := X ^ k)
    (by rw [degree_X_pow]; exact_mod_cast hk)
  simp only [eval_pow, eval_X, intNode_apply] at h
  rw [← h, integral_pow]

/-- **Table 9.2, the trapezoidal weights**: `newtonCotesWeight 1 = ![1/2, 1/2]`. -/
theorem newtonCotesWeight_one : newtonCotesWeight 1 = ![1 / 2, 1 / 2] := by
  have h0 := sum_newtonCotesWeight_mul_pow (n := 1) one_pos (k := 0) (by norm_num)
  change ∑ i : Fin 2, newtonCotesWeight 1 i * ((i : ℕ) : ℝ) ^ 0 = _ at h0
  have h1 := sum_newtonCotesWeight_mul_pow (n := 1) one_pos (k := 1) (by norm_num)
  change ∑ i : Fin 2, newtonCotesWeight 1 i * ((i : ℕ) : ℝ) ^ 1 = _ at h1
  norm_num [Fin.sum_univ_two] at h0 h1
  funext i
  fin_cases i <;> simp <;> linarith

/-- **Table 9.2, Simpson's weights**: `newtonCotesWeight 2 = ![1/3, 4/3, 1/3]`. -/
theorem newtonCotesWeight_two : newtonCotesWeight 2 = ![1 / 3, 4 / 3, 1 / 3] := by
  have h0 := sum_newtonCotesWeight_mul_pow (n := 2) two_pos (k := 0) (by norm_num)
  change ∑ i : Fin 3, newtonCotesWeight 2 i * ((i : ℕ) : ℝ) ^ 0 = _ at h0
  have h1 := sum_newtonCotesWeight_mul_pow (n := 2) two_pos (k := 1) (by norm_num)
  change ∑ i : Fin 3, newtonCotesWeight 2 i * ((i : ℕ) : ℝ) ^ 1 = _ at h1
  have h2 := sum_newtonCotesWeight_mul_pow (n := 2) two_pos (k := 2) (by norm_num)
  change ∑ i : Fin 3, newtonCotesWeight 2 i * ((i : ℕ) : ℝ) ^ 2 = _ at h2
  norm_num [Fin.sum_univ_three] at h0 h1 h2
  funext i
  fin_cases i <;> simp <;> linarith

/-- **Table 9.2, the `3/8` rule**: `newtonCotesWeight 3 = ![3/8, 9/8, 9/8, 3/8]`. -/
theorem newtonCotesWeight_three : newtonCotesWeight 3 = ![3 / 8, 9 / 8, 9 / 8, 3 / 8] := by
  have h0 := sum_newtonCotesWeight_mul_pow (n := 3) three_pos (k := 0) (by norm_num)
  change ∑ i : Fin 4, newtonCotesWeight 3 i * ((i : ℕ) : ℝ) ^ 0 = _ at h0
  have h1 := sum_newtonCotesWeight_mul_pow (n := 3) three_pos (k := 1) (by norm_num)
  change ∑ i : Fin 4, newtonCotesWeight 3 i * ((i : ℕ) : ℝ) ^ 1 = _ at h1
  have h2 := sum_newtonCotesWeight_mul_pow (n := 3) three_pos (k := 2) (by norm_num)
  change ∑ i : Fin 4, newtonCotesWeight 3 i * ((i : ℕ) : ℝ) ^ 2 = _ at h2
  have h3 := sum_newtonCotesWeight_mul_pow (n := 3) three_pos (k := 3) (by norm_num)
  change ∑ i : Fin 4, newtonCotesWeight 3 i * ((i : ℕ) : ℝ) ^ 3 = _ at h3
  norm_num [Fin.sum_univ_four] at h0 h1 h2 h3
  funext i
  fin_cases i <;> simp <;> linarith

/-- **Table 9.2, the midpoint weight**: `openNewtonCotesWeight 0 = ![2]`. -/
theorem openNewtonCotesWeight_zero : openNewtonCotesWeight 0 = ![2] := by
  have h0 := sum_openNewtonCotesWeight_mul_pow (n := 0) (k := 0) le_rfl
  change ∑ i : Fin 1, openNewtonCotesWeight 0 i * ((i : ℕ) : ℝ) ^ 0 = _ at h0
  norm_num [Fin.sum_univ_one] at h0
  funext i
  fin_cases i
  simpa using h0

/-- **Table 9.2, the open rule with three nodes**: `openNewtonCotesWeight 2 = ![8/3, -4/3, 8/3]`,
the first Newton–Cotes rule with a negative weight. -/
theorem openNewtonCotesWeight_two : openNewtonCotesWeight 2 = ![8 / 3, -4 / 3, 8 / 3] := by
  have h0 := sum_openNewtonCotesWeight_mul_pow (n := 2) (k := 0) (by norm_num)
  change ∑ i : Fin 3, openNewtonCotesWeight 2 i * ((i : ℕ) : ℝ) ^ 0 = _ at h0
  have h1 := sum_openNewtonCotesWeight_mul_pow (n := 2) (k := 1) (by norm_num)
  change ∑ i : Fin 3, openNewtonCotesWeight 2 i * ((i : ℕ) : ℝ) ^ 1 = _ at h1
  have h2 := sum_openNewtonCotesWeight_mul_pow (n := 2) (k := 2) (by norm_num)
  change ∑ i : Fin 3, openNewtonCotesWeight 2 i * ((i : ℕ) : ℝ) ^ 2 = _ at h2
  norm_num [Fin.sum_univ_three] at h0 h1 h2
  funext i
  fin_cases i <;> simp <;> linarith

/-- **The closed rule with `n = 1` is the trapezoidal rule**, `(b - a)/2 (f(a) + f(b))`.

Reference: [quarteroni2000numerical], (9.11). -/
theorem closedNewtonCotes_one (f : ℝ → ℝ) (a b : ℝ) :
    closedNewtonCotes 1 f a b = (b - a) / 2 * (f a + f b) := by
  simp [closedNewtonCotes, newtonCotesWeight_one, Fin.sum_univ_succ]
  ring_nf

/-- The closed rule with `n = 1` is the one-panel trapezoidal sum. -/
theorem closedNewtonCotes_one_eq_trapezoidSum (f : ℝ → ℝ) (a b : ℝ) :
    closedNewtonCotes 1 f a b = trapezoidSum f a (b - a) 1 := by
  rw [closedNewtonCotes_one, trapezoidSum, Finset.sum_range_one]
  simp

/-- **The closed rule with `n = 2` is Simpson's rule**,
`(b - a)/6 (f(a) + 4 f((a + b)/2) + f(b))`.

Reference: [quarteroni2000numerical], (9.15). -/
theorem closedNewtonCotes_two (f : ℝ → ℝ) (a b : ℝ) :
    closedNewtonCotes 2 f a b = (b - a) / 6 * (f a + 4 * f ((a + b) / 2) + f b) := by
  simp [closedNewtonCotes, newtonCotesWeight_two, Fin.sum_univ_succ]
  ring_nf

/-- The closed rule with `n = 2` is the one-panel Simpson sum. -/
theorem closedNewtonCotes_two_eq_simpsonSum (f : ℝ → ℝ) (a b : ℝ) :
    closedNewtonCotes 2 f a b = simpsonSum f a (b - a) 1 := by
  rw [closedNewtonCotes_two, simpsonSum, Finset.sum_range_one]
  simp only [Nat.cast_zero, zero_mul, add_zero, zero_add, one_mul]
  ring_nf

/-- **The open rule with `n = 0` is the midpoint rule.**

Reference: [quarteroni2000numerical], §9.3 (`w_0 = 2`). -/
theorem openNewtonCotes_zero (f : ℝ → ℝ) (a b : ℝ) :
    openNewtonCotes 0 f a b = midpointRule f a b := by
  simp [openNewtonCotes, openNewtonCotesWeight_zero, midpointRule]
  ring_nf

end Rules

/-! ### The constants of the error formulae -/

section Constants

/-- **The constant `M_n = ∫_0^n t π_{n+1}(t) dt`** of the error formula of the closed rules with
even `n`.

Reference: [quarteroni2000numerical], (9.19). -/
noncomputable def newtonCotesM (n : ℕ) : ℝ := ∫ t in (0 : ℝ)..n, t * (intNodal n).eval t

/-- **The constant `K_n = ∫_0^n π_{n+1}(t) dt`** of the error formula of the closed rules with
odd `n`.

Reference: [quarteroni2000numerical], (9.20). -/
noncomputable def newtonCotesK (n : ℕ) : ℝ := ∫ t in (0 : ℝ)..n, (intNodal n).eval t

/-- **The constant `M_n = ∫_{-1}^{n+1} t π_{n+1}(t) dt`** of the error formula of the open rules
with even `n`.

Reference: [quarteroni2000numerical], (9.19). -/
noncomputable def openNewtonCotesM (n : ℕ) : ℝ :=
  ∫ t in (-1 : ℝ)..(n + 1), t * (intNodal n).eval t

/-- **The constant `K_n = ∫_{-1}^{n+1} π_{n+1}(t) dt`** of the error formula of the open rules
with odd `n`.

Reference: [quarteroni2000numerical], (9.20). -/
noncomputable def openNewtonCotesK (n : ℕ) : ℝ := ∫ t in (-1 : ℝ)..(n + 1), (intNodal n).eval t

end Constants

/-! ### The sign of the nodal polynomial, and the positivity of `W` -/

section Sign

variable {n : ℕ}

/-- The nodal polynomial with one more node: `π_{n+2}(t) = π_{n+1}(t) (t - (n + 1))`. -/
theorem intNodal_succ_eval (n : ℕ) (t : ℝ) :
    (intNodal (n + 1)).eval t = (intNodal n).eval t * (t - (n + 1)) := by
  rw [intNodal_eval, intNodal_eval, Fin.prod_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  push_cast
  ring

/-- The nodal polynomial is positive beyond its last node. -/
theorem intNodal_eval_pos_of_lt {t : ℝ} (ht : (n : ℝ) < t) : 0 < (intNodal n).eval t := by
  rw [intNodal_eval]
  refine Finset.prod_pos fun i _ => ?_
  have hi : ((i : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp i.2
  linarith

/-- **The sign of the nodal polynomial between two nodes**: on `(k, k + 1)` with `k ≤ n` it is
`(-1)^{n-k}`, the number of nodes to the right. -/
theorem intNodal_eval_mul_neg_one_pow_pos :
    ∀ (n k : ℕ), k ≤ n → ∀ t : ℝ, (k : ℝ) < t → t < k + 1 →
      0 < (-1) ^ (n - k) * (intNodal n).eval t := by
  intro n
  induction n with
  | zero =>
    intro k hk t hkt _
    obtain rfl : k = 0 := Nat.le_zero.mp hk
    simpa [intNodal_eval] using hkt
  | succ n ih =>
    intro k hk t hkt htk
    rw [intNodal_succ_eval]
    rcases Nat.lt_or_ge k (n + 1) with hlt | hge
    · have hk' : k ≤ n := Nat.lt_succ_iff.mp hlt
      have h := ih k hk' t hkt htk
      have hneg : t - (n + 1) < 0 := by
        have : (k : ℝ) + 1 ≤ n + 1 := by exact_mod_cast Nat.add_le_add_right hk' 1
        linarith
      have hsucc : n + 1 - k = (n - k) + 1 := by omega
      rw [hsucc, pow_succ]
      nlinarith
    · obtain rfl : k = n + 1 := le_antisymm hk hge
      rw [Nat.sub_self, pow_zero, one_mul]
      push_cast at hkt
      have := intNodal_eval_pos_of_lt (n := n) (t := t) (by linarith)
      nlinarith

/-- For even `n`, the nodal polynomial is positive on `(k, k + 1)` for even `k ≤ n`. -/
theorem intNodal_eval_pos_of_even (hn : Even n) {k : ℕ} (hk : k ≤ n) (hke : Even k) {t : ℝ}
    (hkt : (k : ℝ) < t) (htk : t < k + 1) : 0 < (intNodal n).eval t := by
  have h := intNodal_eval_mul_neg_one_pow_pos n k hk t hkt htk
  have he : Even (n - k) := (Nat.even_sub hk).2 ⟨fun _ => hke, fun _ => hn⟩
  rwa [he.neg_one_pow, one_mul] at h

/-- For even `n`, the nodal polynomial is negative on `(k, k + 1)` for odd `k ≤ n`. -/
theorem intNodal_eval_neg_of_even (hn : Even n) {k : ℕ} (hk : k ≤ n) (hko : Odd k) {t : ℝ}
    (hkt : (k : ℝ) < t) (htk : t < k + 1) : (intNodal n).eval t < 0 := by
  have h := intNodal_eval_mul_neg_one_pow_pos n k hk t hkt htk
  have ho : Odd (n - k) := by
    refine Nat.not_even_iff_odd.1 fun h' => ?_
    rw [Nat.even_sub hk] at h'
    exact (Nat.not_even_iff_odd.2 hko) (h'.1 hn)
  rw [ho.neg_one_pow] at h
  linarith

/-- **The modulus of the nodal polynomial decreases under a unit shift** on the left half of
`[0, n]`: for `t ∈ (k, k + 1)` with `2t + 1 < n`, `|π_{n+1}(t + 1)| < |π_{n+1}(t)|`. From the shift
identity `π(t + 1)(t - n) = π(t)(t + 1)`, since `t + 1 < n - t`. -/
theorem abs_intNodal_eval_add_one_lt {t : ℝ} (ht0 : -1 < t) (ht : 2 * t + 1 < n)
    (hne : (intNodal n).eval t ≠ 0) :
    |(intNodal n).eval (t + 1)| < |(intNodal n).eval t| := by
  have hid := intNodal_eval_add_one_mul (n := n) t
  have h1 : |(intNodal n).eval (t + 1)| * (n - t) = |(intNodal n).eval t| * (t + 1) := by
    have := congrArg abs hid
    rw [abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < t + 1),
      abs_of_neg (by linarith : t - n < 0)] at this
    linarith [this]
  have hpos : 0 < |(intNodal n).eval t| := abs_pos.2 hne
  have hnt : 0 < (n : ℝ) - t := by linarith
  by_contra hle
  push Not at hle
  have : |(intNodal n).eval t| * (n - t) ≤ |(intNodal n).eval (t + 1)| * (n - t) :=
    mul_le_mul_of_nonneg_right hle hnt.le
  nlinarith

/-- The nodal polynomial is continuous, hence interval integrable. -/
theorem intervalIntegrable_intNodal (n : ℕ) (u v : ℝ) :
    IntervalIntegrable (fun t => (intNodal n).eval t) volume u v :=
  (Polynomial.continuous _).intervalIntegrable u v

/-- On an even unit panel `(2l, 2l + 1)` with `4l + 4 ≤ n`, the sum `π(t) + π(t + 1)` is
positive: `π(t) > 0` there and `|π(t + 1)| < π(t)`. -/
theorem intNodal_eval_add_eval_add_one_pos (hn : Even n) {l : ℕ} (hl : 4 * l + 4 ≤ n) {t : ℝ}
    (hlt : (2 * l : ℕ) < t) (htl : t < (2 * l : ℕ) + 1) :
    0 < (intNodal n).eval t + (intNodal n).eval (t + 1) := by
  have hpos : 0 < (intNodal n).eval t :=
    intNodal_eval_pos_of_even hn (by omega) (even_two_mul l) hlt htl
  have hn' : 2 * t + 1 < n := by
    have : ((4 * l + 4 : ℕ) : ℝ) ≤ n := by exact_mod_cast hl
    push_cast at this hlt htl
    linarith
  have ht0 : -1 < t := by
    have : (0 : ℝ) ≤ ((2 * l : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hlt' := abs_intNodal_eval_add_one_lt ht0 hn' hpos.ne'
  rw [abs_of_pos hpos] at hlt'
  linarith [neg_abs_le ((intNodal n).eval (t + 1))]

/-- The integral of the nodal polynomial over an even unit panel `[k, k + 1]`, `k < n` even, is
positive. -/
theorem integral_intNodal_panel_pos (hn : Even n) {k : ℕ} (hk : k < n) (hke : Even k) :
    0 < ∫ t in (k : ℝ)..(k + 1), (intNodal n).eval t :=
  intervalIntegral_pos_of_pos_on (intervalIntegrable_intNodal n _ _)
    (fun t ht => intNodal_eval_pos_of_even hn hk.le hke ht.1 ht.2) (by linarith)

/-- The integral of the nodal polynomial over an odd unit panel `[k, k + 1]`, `k < n` odd, is
negative. -/
theorem integral_intNodal_panel_neg (hn : Even n) {k : ℕ} (hk : k < n) (hko : Odd k) :
    (∫ t in (k : ℝ)..(k + 1), (intNodal n).eval t) < 0 := by
  have h := intervalIntegral_pos_of_pos_on (f := fun t => -(intNodal n).eval t)
    (intervalIntegrable_intNodal n _ _).neg
    (fun t ht => neg_pos.2 (intNodal_eval_neg_of_even hn hk.le hko ht.1 ht.2))
    (by linarith : (k : ℝ) < k + 1)
  rw [integral_neg] at h
  linarith

/-- The integral of the nodal polynomial over a double panel `[2l, 2l + 2]` with `4l + 4 ≤ n` is
positive: the two unit panels combine into one integral of `π(t) + π(t + 1)`. -/
theorem integral_intNodal_double_panel_pos (hn : Even n) {l : ℕ} (hl : 4 * l + 4 ≤ n) :
    0 < ∫ t in ((2 * l : ℕ) : ℝ)..((2 * l : ℕ) + 2), (intNodal n).eval t := by
  have hsplit := integral_add_adjacent_intervals (intervalIntegrable_intNodal n ((2 * l : ℕ) : ℝ)
    ((2 * l : ℕ) + 1)) (intervalIntegrable_intNodal n ((2 * l : ℕ) + 1) ((2 * l : ℕ) + 2))
  have hshift : (∫ t in ((2 * l : ℕ) : ℝ) + 1..((2 * l : ℕ) + 2), (intNodal n).eval t)
      = ∫ t in ((2 * l : ℕ) : ℝ)..((2 * l : ℕ) + 1), (intNodal n).eval (t + 1) := by
    rw [integral_comp_add_right (fun t => (intNodal n).eval t) 1]
    congr 1
    ring
  have hc1 : Continuous fun t : ℝ => (intNodal n).eval (t + 1) := by fun_prop
  rw [← hsplit, hshift, ← integral_add (f := fun t => (intNodal n).eval t)
    (g := fun t => (intNodal n).eval (t + 1)) (intervalIntegrable_intNodal n _ _)
    (hc1.intervalIntegrable _ _)]
  exact intervalIntegral_pos_of_pos_on
    ((by fun_prop : Continuous fun t : ℝ => (intNodal n).eval t + (intNodal n).eval (t + 1))
      |>.intervalIntegrable _ _)
    (fun t ht => intNodal_eval_add_eval_add_one_pos hn hl ht.1 ht.2) (by linarith)

/-- `W(k) = ∫_0^k π_{n+1} ≥ 0` for `2k ≤ n`, and `> 0` for `1 ≤ k` with `2k ≤ n`: the
partial sums of the alternating panel integrals with decreasing moduli. -/
theorem integral_intNodal_natCast_pos (hn : Even n) :
    ∀ k : ℕ, 2 * k ≤ n →
      0 ≤ (∫ t in (0 : ℝ)..k, (intNodal n).eval t) ∧
        (1 ≤ k → 0 < ∫ t in (0 : ℝ)..k, (intNodal n).eval t) := by
  -- even `k = 2l`, by induction on `l`
  have heven : ∀ l : ℕ, 4 * l ≤ n →
      0 ≤ (∫ t in (0 : ℝ)..((2 * l : ℕ) : ℝ), (intNodal n).eval t) ∧
        (1 ≤ l → 0 < ∫ t in (0 : ℝ)..((2 * l : ℕ) : ℝ), (intNodal n).eval t) := by
    intro l
    induction l with
    | zero => intro _; simp
    | succ l ih =>
      intro hl
      have ih' := ih (by omega)
      have hdouble := integral_intNodal_double_panel_pos hn (l := l) (by omega)
      have hsplit := integral_add_adjacent_intervals (intervalIntegrable_intNodal n 0
        ((2 * l : ℕ) : ℝ)) (intervalIntegrable_intNodal n ((2 * l : ℕ) : ℝ) ((2 * l : ℕ) + 2))
      have hcast : ((2 * (l + 1) : ℕ) : ℝ) = ((2 * l : ℕ) : ℝ) + 2 := by push_cast; ring
      rw [hcast, ← hsplit]
      exact ⟨by linarith [ih'.1], fun _ => by linarith [ih'.1]⟩
  intro k hk
  rcases Nat.even_or_odd k with ⟨l, hl⟩ | ⟨l, hl⟩
  · have hl' : k = 2 * l := by omega
    subst hl'
    exact ⟨(heven l (by omega)).1, fun h1 => (heven l (by omega)).2 (by omega)⟩
  · subst hl
    have h2l := heven l (by omega)
    have hpanel := integral_intNodal_panel_pos hn (k := 2 * l) (by omega) (even_two_mul l)
    have hsplit := integral_add_adjacent_intervals (intervalIntegrable_intNodal n 0
      ((2 * l : ℕ) : ℝ)) (intervalIntegrable_intNodal n ((2 * l : ℕ) : ℝ) ((2 * l : ℕ) + 1))
    have hcast : ((2 * l + 1 : ℕ) : ℝ) = ((2 * l : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [hcast, ← hsplit]
    exact ⟨by linarith [h2l.1], fun _ => by linarith [h2l.1]⟩

/-- `W(x) = ∫_0^x π_{n+1} > 0` for `0 < x` with `2x ≤ n`: between two consecutive nodes `W` is
monotone, so its value lies between two values at integers, both nonnegative and at least one
positive. -/
theorem integral_intNodal_pos_of_le_half (hn : Even n) {x : ℝ} (hx0 : 0 < x) (hxn : 2 * x ≤ n) :
    0 < ∫ t in (0 : ℝ)..x, (intNodal n).eval t := by
  set k := ⌊x⌋₊ with hk
  have hkx : (k : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxk : x < k + 1 := Nat.lt_floor_add_one x
  have hkn : 2 * k ≤ n := by
    have : (2 * k : ℝ) ≤ n := by linarith
    exact_mod_cast this
  rcases eq_or_lt_of_le hkx with heq | hlt
  · -- `x` is an integer
    have hk1 : 1 ≤ k := by
      by_contra h
      push Not at h
      have : k = 0 := by omega
      rw [this] at heq
      simp at heq
      linarith
    rw [← heq]
    exact (integral_intNodal_natCast_pos hn k hkn).2 hk1
  · have hsplit := integral_add_adjacent_intervals (intervalIntegrable_intNodal n 0 k)
      (intervalIntegrable_intNodal n k x)
    rcases Nat.even_or_odd k with hke | hko
    · -- even `k`: `π > 0` on `(k, x)`
      have hkn' : k < n := by
        rcases Nat.eq_zero_or_pos k with h0 | hpos
        · rw [h0]
          have : (0 : ℝ) < n := by linarith
          exact_mod_cast this
        · omega
      have hint : 0 < ∫ t in (k : ℝ)..x, (intNodal n).eval t :=
        intervalIntegral_pos_of_pos_on (intervalIntegrable_intNodal n _ _)
          (fun t ht => intNodal_eval_pos_of_even hn hkn'.le hke ht.1 (by linarith [ht.2])) hlt
      rw [← hsplit]
      linarith [(integral_intNodal_natCast_pos hn k hkn).1]
    · -- odd `k`: `π < 0` on `(x, k + 1)`, and `W(k + 1) > 0`
      have hkn2 : 2 * (k + 1) ≤ n := by
        have h1 : (2 * k : ℝ) < n := by linarith
        have h2 : 2 * k < n := by exact_mod_cast h1
        obtain ⟨m, hm⟩ := hn
        omega
      have hsplit' := integral_add_adjacent_intervals (intervalIntegrable_intNodal n 0 x)
        (intervalIntegrable_intNodal n x (k + 1))
      have hneg : (∫ t in x..((k : ℝ) + 1), (intNodal n).eval t) < 0 := by
        have h := intervalIntegral_pos_of_pos_on (f := fun t => -(intNodal n).eval t)
          (intervalIntegrable_intNodal n _ _).neg
          (fun t ht => neg_pos.2 (intNodal_eval_neg_of_even hn (by omega) hko
            (by linarith [ht.1]) ht.2)) hxk
        rw [integral_neg] at h
        linarith
      have hW := (integral_intNodal_natCast_pos hn (k + 1) hkn2).2 (by omega)
      push_cast at hW
      linarith

/-- **The symmetry `W(n - x) = W(x)`** of `W(x) = ∫_0^x π_{n+1}` for even `n`: the nodal
polynomial is odd about the midpoint, so `W(n) = 0` and `∫_x^n π = -W(n - x)`. -/
theorem integral_intNodal_sub_eq (hn : Even n) (x : ℝ) :
    (∫ t in (0 : ℝ)..(n - x), (intNodal n).eval t) = ∫ t in (0 : ℝ)..x, (intNodal n).eval t := by
  have hodd : ∀ t : ℝ, (intNodal n).eval (n - t) = -(intNodal n).eval t := by
    intro t
    rw [intNodal_comp_sub, hn.add_one.neg_one_pow]
    ring
  -- `∫_u^v π(n - s) ds = -∫_u^v π`, transported to `∫_{n-v}^{n-u} π`
  have hrefl : ∀ u v : ℝ, (∫ s in (n - v)..(n - u), (intNodal n).eval s)
      = -∫ s in u..v, (intNodal n).eval s := by
    intro u v
    rw [← integral_comp_sub_left (fun s => (intNodal n).eval s) (n : ℝ), ← integral_neg]
    exact integral_congr fun s _ => hodd s
  have hWn : (∫ t in (0 : ℝ)..n, (intNodal n).eval t) = 0 := by
    have h := hrefl 0 n
    rw [sub_self, sub_zero] at h
    linarith
  have hsplit := integral_add_adjacent_intervals (intervalIntegrable_intNodal n 0 x)
    (intervalIntegrable_intNodal n x n)
  have h := hrefl x n
  rw [sub_self] at h
  linarith

/-- **Positivity of `W`** ([quarteroni2000numerical] Theorem 9.2, the fact cited from
Isaacson–Keller p. 309): for even `n > 0` and `0 < x < n`,
`W(x) = ∫_0^x π_{n+1}(t) dt > 0`.

The unit-panel integrals of `π_{n+1}` alternate in sign, starting positive, with strictly
decreasing modulus up to the midpoint `n/2` (`abs_intNodal_eval_add_one_lt`), so `W` is positive
at the integers `1, …, n/2`; `W` is monotone between consecutive integers, which gives positivity
on `(0, n/2]`; and the antisymmetry of `π_{n+1}` about the midpoint gives `W(n - x) = W(x)`. -/
theorem integral_intNodal_pos_of_even (hn : Even n) {x : ℝ} (hx0 : 0 < x) (hxn : x < n) :
    0 < ∫ t in (0 : ℝ)..x, (intNodal n).eval t := by
  rcases le_or_gt (2 * x) n with h | h
  · exact integral_intNodal_pos_of_le_half hn hx0 h
  · rw [← integral_intNodal_sub_eq hn]
    exact integral_intNodal_pos_of_le_half hn (by linarith) (by linarith)

/-- `W(x) = ∫_0^x π_{n+1}` is nonnegative on `[0, n]` for even `n`. -/
theorem integral_intNodal_nonneg_of_even (hn : Even n) {x : ℝ} (hx0 : 0 ≤ x) (hxn : x ≤ n) :
    0 ≤ ∫ t in (0 : ℝ)..x, (intNodal n).eval t := by
  rcases eq_or_lt_of_le hx0 with rfl | hx0'
  · simp
  rcases eq_or_lt_of_le hxn with rfl | hxn'
  · rw [← integral_intNodal_sub_eq hn, sub_self]
    simp
  · exact (integral_intNodal_pos_of_even hn hx0' hxn').le

/-- **`M_n < 0` for even `n > 0`** ([quarteroni2000numerical] Theorem 9.2): integrating by parts,
`M_n = ∫_0^n t π_{n+1}(t) dt = [t W(t)]_0^n - ∫_0^n W = -∫_0^n W`, since `W(n) = 0`, and `W > 0`
inside `(0, n)`. -/
theorem newtonCotesM_neg (hn : Even n) (hn0 : 0 < n) : newtonCotesM n < 0 := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  set W : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, (intNodal n).eval t with hW
  have hWd : ∀ x, HasDerivAt W ((intNodal n).eval x) x := fun x =>
    ((Polynomial.continuous _).integral_hasStrictDerivAt 0 x).hasDerivAt
  have hWc : Continuous W := continuous_iff_continuousAt.2 fun x => (hWd x).continuousAt
  have hparts := integral_mul_deriv_eq_deriv_mul (a := 0) (b := n) (u := fun t => t)
    (u' := fun _ => (1 : ℝ)) (v := W) (v' := fun t => (intNodal n).eval t)
    (fun x _ => hasDerivAt_id' x) (fun x _ => hWd x) intervalIntegrable_const
    (intervalIntegrable_intNodal n _ _)
  have hWn : W n = 0 := by
    have h := integral_intNodal_sub_eq hn (n : ℝ)
    rw [sub_self] at h
    simp only [hW, integral_same] at h ⊢
    exact h.symm
  rw [newtonCotesM, hparts, hWn]
  simp only [mul_zero, zero_mul, sub_zero, one_mul, zero_sub, neg_lt_zero]
  refine integral_pos_of_continuousOn_of_nonneg hnR hWc.continuousOn
    (fun t ht => integral_intNodal_nonneg_of_even hn ht.1 ht.2) (c := n / 2)
    ⟨by positivity, by linarith⟩ ?_
  exact integral_intNodal_pos_of_even hn (by positivity) (by linarith)

/-- **`K_n = 0` for even `n`**: the nodal polynomial is odd about the midpoint. -/
theorem newtonCotesK_eq_zero_of_even (hn : Even n) : newtonCotesK n = 0 := by
  have h := integral_intNodal_sub_eq hn (n : ℝ)
  rw [sub_self, integral_same] at h
  exact h.symm

/-- **The sign of the nodal polynomial to the left of its first node**: `(-1)^{n+1} π_{n+1}(t) > 0`
for `t < 0`, since all `n + 1` factors `t - i` are negative there. This is the panel `(-1, 0)` of
the open rules, which the `ℕ`-indexed `intNodal_eval_mul_neg_one_pow_pos` does not reach. -/
theorem intNodal_eval_mul_neg_one_pow_pos_of_neg {t : ℝ} (ht : t < 0) :
    0 < (-1) ^ (n + 1) * (intNodal n).eval t := by
  have hcard : ((-1 : ℝ)) ^ (n + 1) = ∏ _i : Fin (n + 1), (-1 : ℝ) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [intNodal_eval, hcard, ← Finset.prod_mul_distrib]
  refine Finset.prod_pos fun i _ => ?_
  have : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- `W(x) = ∫_0^x π_{n+1} > 0` beyond the last node, for even `n`: `W(n) = 0` and the integrand is
positive on `(n, x)`. -/
theorem integral_intNodal_pos_of_even_of_lt (hn : Even n) {x : ℝ} (hx : (n : ℝ) < x) :
    0 < ∫ t in (0 : ℝ)..x, (intNodal n).eval t := by
  have hsplit := integral_add_adjacent_intervals (intervalIntegrable_intNodal n 0 (n : ℝ))
    (intervalIntegrable_intNodal n (n : ℝ) x)
  have h0 : (∫ t in (0 : ℝ)..(n : ℝ), (intNodal n).eval t) = 0 := by
    have := newtonCotesK_eq_zero_of_even hn
    rwa [newtonCotesK] at this
  have hlast : 0 < ∫ t in (n : ℝ)..x, (intNodal n).eval t :=
    intervalIntegral_pos_of_pos_on (intervalIntegrable_intNodal n _ _)
      (fun t ht => intNodal_eval_pos_of_lt ht.1) hx
  rw [← hsplit, h0]
  linarith

/-- `W(x) = ∫_0^x π_{n+1} ≥ 0` on the whole half-line, for even `n`. -/
theorem integral_intNodal_nonneg_of_even' (hn : Even n) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ ∫ t in (0 : ℝ)..x, (intNodal n).eval t := by
  rcases le_or_gt x n with h | h
  · exact integral_intNodal_nonneg_of_even hn hx h
  · exact (integral_intNodal_pos_of_even_of_lt hn h).le

/-- **The recursion for the primitive of the nodal polynomial**: integrating
`π_{n+2}(t) = π_{n+1}(t) (t - (n + 1))` by parts against the primitive `V(t) = ∫_u^t π_{n+1}`,

  `∫_u^x π_{n+2} = (x - (n + 1)) V(x) - ∫_u^x V`,

with no boundary term at `u` because `V(u) = 0`. Both the open and the closed sign analyses come
from this identity: for `x ≤ n + 1` the two terms on the right have the sign of `-V`. -/
private theorem integral_intNodal_succ_eq (p : ℕ) (u x : ℝ) :
    (∫ t in u..x, (intNodal (p + 1)).eval t)
      = (x - ((p : ℝ) + 1)) * (∫ t in u..x, (intNodal p).eval t)
        - ∫ t in u..x, ∫ s in u..t, (intNodal p).eval s := by
  have hVd : ∀ t : ℝ, HasDerivAt (fun y => ∫ s in u..y, (intNodal p).eval s)
      ((intNodal p).eval t) t := fun t =>
    ((Polynomial.continuous _).integral_hasStrictDerivAt u t).hasDerivAt
  have hparts := integral_mul_deriv_eq_deriv_mul (a := u) (b := x)
    (u := fun t => t - ((p : ℝ) + 1)) (u' := fun _ => (1 : ℝ))
    (v := fun y => ∫ s in u..y, (intNodal p).eval s) (v' := fun t => (intNodal p).eval t)
    (fun t _ => (hasDerivAt_id t).sub_const _) (fun t _ => hVd t) intervalIntegrable_const
    (intervalIntegrable_intNodal p u x)
  simp only [integral_same, mul_zero, sub_zero, one_mul] at hparts
  rw [integral_congr (g := fun t => (t - ((p : ℝ) + 1)) * (intNodal p).eval t)
    fun t _ => by rw [intNodal_succ_eval]; ring]
  rw [hparts]

/-- **`W(x) = ∫_0^x π_{n+1} ≤ 0` on `[0, n]` for odd `n`**, the odd-`n` companion of
`integral_intNodal_nonneg_of_even`: writing `n = p + 1` with `p` even and integrating by parts
(`integral_intNodal_succ_eq`), both terms are nonpositive because the primitive of `π_{p+1}` is
nonnegative and `x ≤ p + 1`. -/
theorem integral_intNodal_nonpos_of_odd (hn : Odd n) {x : ℝ} (hx0 : 0 ≤ x) (hxn : x ≤ n) :
    (∫ t in (0 : ℝ)..x, (intNodal n).eval t) ≤ 0 := by
  obtain ⟨m, rfl⟩ := hn
  have hpe : Even (2 * m) := even_two_mul m
  have hcast : ((2 * m + 1 : ℕ) : ℝ) = ((2 * m : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [integral_intNodal_succ_eq (2 * m) 0 x]
  rw [hcast] at hxn
  have h1 : (x - (((2 * m : ℕ) : ℝ) + 1)) *
      (∫ t in (0 : ℝ)..x, (intNodal (2 * m)).eval t) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (integral_intNodal_nonneg_of_even' hpe hx0)
  have h2 : 0 ≤ ∫ t in (0 : ℝ)..x, ∫ s in (0 : ℝ)..t, (intNodal (2 * m)).eval s :=
    integral_nonneg hx0 fun t ht => integral_intNodal_nonneg_of_even' hpe ht.1
  linarith

/-- **`K_n < 0` for odd `n`** ([quarteroni2000numerical] Theorem 9.2, (9.20), stated there without
proof): `K_n = ∫_0^n π_{n+1}(t) dt` is negative. With `n = p + 1` and `p` even, integration by parts
(`integral_intNodal_succ_eq`) gives `K_n = -∫_0^{p+1} W_p` with `W_p(x) = ∫_0^x π_{p+1} ≥ 0`, and
`W_p` is positive at `p + 1/2`. -/
theorem newtonCotesK_neg (hn : Odd n) : newtonCotesK n < 0 := by
  obtain ⟨m, rfl⟩ := hn
  have hpe : Even (2 * m) := even_two_mul m
  have hcast : ((2 * m + 1 : ℕ) : ℝ) = ((2 * m : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [newtonCotesK, hcast, integral_intNodal_succ_eq (2 * m) 0, sub_self, zero_mul, zero_sub,
    neg_lt_zero]
  have hWc : Continuous fun y : ℝ => ∫ s in (0 : ℝ)..y, (intNodal (2 * m)).eval s :=
    continuous_iff_continuousAt.2 fun y =>
      (((Polynomial.continuous _).integral_hasStrictDerivAt 0 y).hasDerivAt).continuousAt
  refine integral_pos_of_continuousOn_of_nonneg (by positivity) hWc.continuousOn
    (fun t ht => integral_intNodal_nonneg_of_even' hpe ht.1) (c := ((2 * m : ℕ) : ℝ) + 1 / 2)
    ⟨by positivity, by linarith⟩ ?_
  exact integral_intNodal_pos_of_even_of_lt hpe (by linarith)

/-- For even `n` the nodal polynomial integrates to zero over the interval `[-1, n+1]` of the open
rules: it is odd about the midpoint `n/2`, which is also the midpoint of `[-1, n + 1]`. -/
theorem integral_intNodal_neg_one_eq_zero_of_even (hn : Even n) :
    (∫ t in (-1 : ℝ)..((n : ℝ) + 1), (intNodal n).eval t) = 0 := by
  have h := integral_intNodal_sub_eq hn ((n : ℝ) + 1)
  rw [show (n : ℝ) - ((n : ℝ) + 1) = -1 by ring] at h
  have hsym : (∫ t in (-1 : ℝ)..(0 : ℝ), (intNodal n).eval t)
      = -∫ t in (0 : ℝ)..(-1 : ℝ), (intNodal n).eval t := integral_symm _ _
  have hsplit := integral_add_adjacent_intervals (intervalIntegrable_intNodal n (-1) 0)
    (intervalIntegrable_intNodal n 0 ((n : ℝ) + 1))
  rw [← hsplit, hsym, h]
  ring

/-- **The sign of `W̃(x) = ∫_{-1}^x π_{n+1}` on `[-1, n + 1]`**, the interval of the open
Newton–Cotes rules: `(-1)^{n+1} W̃ ≥ 0`, that is, `W̃ ≤ 0` for even `n` and `W̃ ≥ 0` for odd `n`.

The proof is an induction on `n` through `integral_intNodal_succ_eq`: on `[-1, n + 1]` the two
terms of that identity both carry the sign opposite to the previous `W̃`, and the last panel
`[n + 1, n + 2]` is handled by the positivity of `π_{n+2}` beyond its last node when `n + 1` is
odd, and by `integral_intNodal_neg_one_eq_zero_of_even` when `n + 1` is even. -/
theorem integral_intNodal_neg_one_mul_nonneg :
    ∀ (n : ℕ) (x : ℝ), -1 ≤ x → x ≤ (n : ℝ) + 1 →
      0 ≤ (-1) ^ (n + 1) * ∫ t in (-1 : ℝ)..x, (intNodal n).eval t := by
  intro n
  induction n with
  | zero =>
    intro x hx1 hx2
    have hval : (∫ t in (-1 : ℝ)..x, (intNodal 0).eval t) = (x ^ 2 - 1) / 2 := by
      rw [integral_congr (g := fun t : ℝ => t) fun t _ => by
        simp [intNodal_eval], integral_id]
      norm_num
    rw [hval]
    push_cast at hx2
    nlinarith
  | succ p ih =>
    have hmain : ∀ x : ℝ, -1 ≤ x → x ≤ (p : ℝ) + 1 →
        0 ≤ (-1) ^ (p + 2) * ∫ t in (-1 : ℝ)..x, (intNodal (p + 1)).eval t := by
      intro x hx1 hx2
      rw [integral_intNodal_succ_eq p (-1) x]
      have hterm1 : 0 ≤ (-1 : ℝ) ^ (p + 2) *
          ((x - ((p : ℝ) + 1)) * ∫ t in (-1 : ℝ)..x, (intNodal p).eval t) := by
        have h := ih x hx1 hx2
        have hrw : (-1 : ℝ) ^ (p + 2) *
            ((x - ((p : ℝ) + 1)) * ∫ t in (-1 : ℝ)..x, (intNodal p).eval t)
            = (((p : ℝ) + 1) - x) *
              ((-1) ^ (p + 1) * ∫ t in (-1 : ℝ)..x, (intNodal p).eval t) := by
          rw [pow_succ]; ring
        rw [hrw]
        exact mul_nonneg (by linarith) h
      have hterm2 : 0 ≤ (-1 : ℝ) ^ (p + 2) *
          (-∫ t in (-1 : ℝ)..x, ∫ s in (-1 : ℝ)..t, (intNodal p).eval s) := by
        have hrw : (-1 : ℝ) ^ (p + 2) *
            (-∫ t in (-1 : ℝ)..x, ∫ s in (-1 : ℝ)..t, (intNodal p).eval s)
            = ∫ t in (-1 : ℝ)..x, (-1) ^ (p + 1) * ∫ s in (-1 : ℝ)..t, (intNodal p).eval s := by
          rw [integral_const_mul, pow_succ]; ring
        rw [hrw]
        exact integral_nonneg hx1 fun t ht => ih t ht.1 (by linarith [ht.2])
      have hsum := add_nonneg hterm1 hterm2
      linarith [hsum]
    intro x hx1 hx2
    rcases le_or_gt x ((p : ℝ) + 1) with hx | hx
    · exact hmain x hx1 hx
    · have hcast : (((p + 1 : ℕ) : ℝ)) = (p : ℝ) + 1 := by push_cast; ring
      push_cast at hx2
      rcases Nat.even_or_odd (p + 1) with hpe | hpo
      · have hzero := integral_intNodal_neg_one_eq_zero_of_even hpe
        rw [hcast] at hzero
        have hsplit2 := integral_add_adjacent_intervals
          (intervalIntegrable_intNodal (p + 1) (-1) x)
          (intervalIntegrable_intNodal (p + 1) x ((p : ℝ) + 1 + 1))
        have htail : 0 ≤ ∫ t in x..((p : ℝ) + 1 + 1), (intNodal (p + 1)).eval t := by
          refine integral_nonneg (by linarith) fun t ht => ?_
          rcases eq_or_lt_of_le (le_trans hx.le ht.1) with heq | hlt
          · rw [← heq, ← hcast, intNodal_eval_natCast le_rfl]
          · exact (intNodal_eval_pos_of_lt (by rwa [hcast])).le
        have hev : (-1 : ℝ) ^ (p + 1 + 1) = -1 := hpe.add_one.neg_one_pow
        rw [hev, neg_one_mul, neg_nonneg]
        linarith
      · have hhead := hmain ((p : ℝ) + 1) (by linarith) le_rfl
        have hsplit := integral_add_adjacent_intervals
          (intervalIntegrable_intNodal (p + 1) (-1) ((p : ℝ) + 1))
          (intervalIntegrable_intNodal (p + 1) ((p : ℝ) + 1) x)
        have htail : 0 ≤ ∫ t in ((p : ℝ) + 1)..x, (intNodal (p + 1)).eval t := by
          refine integral_nonneg hx.le fun t ht => ?_
          rcases eq_or_lt_of_le ht.1 with heq | hlt
          · rw [← heq, ← hcast, intNodal_eval_natCast le_rfl]
          · exact (intNodal_eval_pos_of_lt (by rwa [hcast])).le
        have hsign : (0 : ℝ) ≤ (-1) ^ (p + 1 + 1) := by
          rcases Nat.even_or_odd p with h | h
          · rw [(h.add_one.add_one).neg_one_pow]; norm_num
          · exact absurd h.add_one (Nat.not_even_iff_odd.2 hpo)
        rw [← hsplit, mul_add]
        exact add_nonneg hhead (mul_nonneg hsign htail)

/-- **`M̃_n > 0` for even `n`** ([quarteroni2000numerical] Theorem 9.2, (9.19), stated there without
proof): the constant `M̃_n = ∫_{-1}^{n+1} t π_{n+1}(t) dt` of the open rules with even `n` is
positive. Integrating by parts, `M̃_n = -∫_{-1}^{n+1} W̃` because `W̃(-1) = 0` and
`W̃(n + 1) = 0` (`integral_intNodal_neg_one_eq_zero_of_even`), and `W̃ ≤ 0` by
`integral_intNodal_neg_one_mul_nonneg`, strictly on the first panel. -/
theorem openNewtonCotesM_pos (hn : Even n) : 0 < openNewtonCotesM n := by
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  set W : ℝ → ℝ := fun y => ∫ s in (-1 : ℝ)..y, (intNodal n).eval s with hW
  have hWd : ∀ t : ℝ, HasDerivAt W ((intNodal n).eval t) t := fun t =>
    ((Polynomial.continuous _).integral_hasStrictDerivAt (-1) t).hasDerivAt
  have hWc : Continuous W := continuous_iff_continuousAt.2 fun y => (hWd y).continuousAt
  have hparts := integral_mul_deriv_eq_deriv_mul (a := (-1 : ℝ)) (b := (n : ℝ) + 1)
    (u := fun t => t) (u' := fun _ => (1 : ℝ)) (v := W) (v' := fun t => (intNodal n).eval t)
    (fun t _ => hasDerivAt_id' t) (fun t _ => hWd t) intervalIntegrable_const
    (intervalIntegrable_intNodal n _ _)
  have hWtop : W ((n : ℝ) + 1) = 0 := integral_intNodal_neg_one_eq_zero_of_even hn
  have hWbot : W (-1) = 0 := by simp [hW]
  have hWnonpos : ∀ t ∈ Icc (-1 : ℝ) ((n : ℝ) + 1), 0 ≤ -W t := by
    intro t ht
    have h := integral_intNodal_neg_one_mul_nonneg n t ht.1 ht.2
    rw [hn.add_one.neg_one_pow, neg_one_mul] at h
    simpa [hW] using h
  have hneg : 0 < -W (-(1 / 2) : ℝ) := by
    have h := intervalIntegral_pos_of_pos_on (f := fun t => -(intNodal n).eval t)
      (intervalIntegrable_intNodal n (-1) (-(1 / 2))).neg
      (fun t ht => by
        have h2 := intNodal_eval_mul_neg_one_pow_pos_of_neg (n := n) (t := t)
          (by linarith [ht.2])
        rw [hn.add_one.neg_one_pow] at h2
        linarith)
      (by norm_num)
    rw [integral_neg] at h
    simpa [hW] using h
  have hpos : 0 < ∫ t in (-1 : ℝ)..((n : ℝ) + 1), -W t :=
    integral_pos_of_continuousOn_of_nonneg (by linarith) hWc.neg.continuousOn hWnonpos
      (c := -(1 / 2)) ⟨by norm_num, by linarith⟩ hneg
  rw [integral_neg] at hpos
  have hone : (∫ x in (-1 : ℝ)..((n : ℝ) + 1), 1 * W x)
      = ∫ x in (-1 : ℝ)..((n : ℝ) + 1), W x := integral_congr fun x _ => one_mul _
  rw [openNewtonCotesM, hparts, hWtop, hWbot, hone]
  linarith

/-- **`K̃_n > 0` for odd `n`** ([quarteroni2000numerical] Theorem 9.2, (9.20)): the constant
`K̃_n = ∫_{-1}^{n+1} π_{n+1}(t) dt` of the open rules with odd `n` is positive. The integral over
`[-1, n]` is nonnegative by `integral_intNodal_neg_one_mul_nonneg`, and the last panel `[n, n + 1]`
contributes a positive amount because `π_{n+1} > 0` beyond its last node. -/
theorem openNewtonCotesK_pos (hn : Odd n) : 0 < openNewtonCotesK n := by
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hhead : 0 ≤ ∫ t in (-1 : ℝ)..(n : ℝ), (intNodal n).eval t := by
    have h := integral_intNodal_neg_one_mul_nonneg n (n : ℝ) (by linarith) (by linarith)
    rwa [hn.add_one.neg_one_pow, one_mul] at h
  have htail : 0 < ∫ t in (n : ℝ)..((n : ℝ) + 1), (intNodal n).eval t :=
    intervalIntegral_pos_of_pos_on (intervalIntegrable_intNodal n _ _)
      (fun t ht => intNodal_eval_pos_of_lt ht.1) (by linarith)
  have hsplit := integral_add_adjacent_intervals (intervalIntegrable_intNodal n (-1) (n : ℝ))
    (intervalIntegrable_intNodal n (n : ℝ) ((n : ℝ) + 1))
  rw [openNewtonCotesK, ← hsplit]
  linarith

end Sign

/-! ### The error of the closed rules with even `n` -/

section Error

variable {n : ℕ} {a b : ℝ} {f : ℝ → ℝ}

/-- A real polynomial function is smooth. -/
private theorem contDiff_eval (p : ℝ[X]) (m : WithTop ℕ∞) : ContDiff ℝ m fun x => p.eval x := by
  simpa [Polynomial.coe_aeval_eq_eval] using p.contDiff_aeval (𝕜 := ℝ) m

/-- **Hadamard's lemma, globally**: if `g` is `C^{m+1}` then `dslope g c` is `C^m`. At `c` this is
`ContDiffAt.dslope_same`; elsewhere `dslope g c` is the quotient `(g y - g c)/(y - c)`. -/
theorem _root_.ContDiff.dslope {g : ℝ → ℝ} {m : ℕ} (hg : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) g)
    (c : ℝ) : ContDiff ℝ m (dslope g c) := by
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  rcases eq_or_ne x c with rfl | hxc
  · exact hg.contDiffAt.dslope_same
  · refine ContDiffAt.congr_of_eventuallyEq ?_ (dslope_eventuallyEq_slope_of_ne g hxc)
    rw [slope_fun_def_field]
    have hg' : ContDiffAt ℝ m g x := hg.contDiffAt.of_le (by exact_mod_cast Nat.le_succ m)
    exact (hg'.sub contDiffAt_const).div (contDiffAt_id.sub contDiffAt_const)
      (sub_ne_zero.2 hxc)

/-- A continuous function is the `k`-th derivative of a `C^k` function: integrate it `k` times. -/
theorem exists_contDiff_iteratedDeriv_eq (k : ℕ) {ψ : ℝ → ℝ} (hψ : Continuous ψ) :
    ∃ g : ℝ → ℝ, ContDiff ℝ k g ∧ iteratedDeriv k g = ψ := by
  induction k with
  | zero => exact ⟨ψ, contDiff_zero.2 hψ, iteratedDeriv_zero⟩
  | succ k ih =>
    obtain ⟨g, hg, hgψ⟩ := ih
    have hgc : Continuous g := hg.continuous
    refine ⟨fun x => ∫ t in (0 : ℝ)..x, g t, ?_, ?_⟩
    · have hd : ∀ x, HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, g t) (g x) x := fun x =>
        (hgc.integral_hasStrictDerivAt 0 x).hasDerivAt
      have hderiv : deriv (fun x => ∫ t in (0 : ℝ)..x, g t) = g := funext fun x => (hd x).deriv
      rw [show ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 by push_cast; rfl,
        contDiff_succ_iff_deriv, hderiv]
      exact ⟨fun x => (hd x).differentiableAt, fun h => absurd h (WithTop.natCast_ne_top k), hg⟩
    · rw [iteratedDeriv_succ']
      have hderiv : deriv (fun x => ∫ t in (0 : ℝ)..x, g t) = g := funext fun x =>
        ((hgc.integral_hasStrictDerivAt 0 x).hasDerivAt).deriv
      rw [hderiv, hgψ]

/-- The truncated power `(y - t)_+^m` is continuous in `t` for `m ≥ 1`. -/
theorem continuous_truncPow {m : ℕ} (hm : 1 ≤ m) (y : ℝ) : Continuous (truncPow m y) := by
  unfold truncPow
  refine Continuous.if_le (by fun_prop) continuous_const continuous_id continuous_const
    fun t ht => ?_
  have ht' : t = y := ht
  rw [ht', sub_self, zero_pow (by omega)]

/-- The Peano kernel of order `m ≥ 1` is continuous on the panel. -/
theorem continuousOn_peanoKernel {k : ℕ} (w z : Fin k → ℝ) {m : ℕ} (hm : 1 ≤ m) :
    ContinuousOn (peanoKernel a b w z m) (Icc a b) := by
  have hclosed : ∀ t ∈ Icc a b, peanoKernel a b w z m t
      = (b - t) ^ (m + 1) / ((m + 1).factorial : ℝ)
        - ∑ i, w i * truncPow m (z i) t / (m.factorial : ℝ) := fun t ht => peanoKernel_eq w z m ht
  refine ContinuousOn.congr ?_ hclosed
  refine (by fun_prop : Continuous fun t : ℝ => (b - t) ^ (m + 1) / ((m + 1).factorial : ℝ))
    |>.continuousOn.sub (continuousOn_finsetSum _ fun i _ => ?_)
  exact (((continuous_truncPow hm (z i)).const_mul (w i)).div_const _).continuousOn

/-- The nodes of the closed rule, `ℕ`-indexed, are distinct. -/
private theorem node_injective (hn : 0 < n) (hab : a < b) {j k : ℕ}
    (h : a + j * ((b - a) / n) = a + k * ((b - a) / n)) : j = k := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hpos : (b - a) / n ≠ 0 := by positivity
  exact_mod_cast mul_right_cancel₀ hpos (by linarith : (j : ℝ) * ((b - a) / n) = k * ((b - a) / n))

/-- **The error of the closed rule with even `n` is nonpositive for an integrand with
nonnegative `(n+2)`-nd derivative.** This is the sign half of the error formula, proved on the
divided-difference route: `f - Π_n f = φ ω` with `φ(x) = f[x_0, …, x_n, x]`, made `C¹` across the
nodes as an iterated `dslope`; integrating by parts against `W(x) = ∫_a^x ω ≥ 0`, which vanishes
at both endpoints, gives `∫_a^b (f - Π_n f) = -∫_a^b φ' W`; and `φ'(x) = f[x_0, …, x_n, x, x]`
is the leading coefficient of a Hermite interpolant of `f`, hence a value of `f^{(n+2)}/(n+2)!`
by Rolle's theorem with multiplicities. -/
theorem sub_closedNewtonCotes_nonpos_of_even (hn : Even n) (hn0 : 0 < n) (hab : a < b)
    (hf : ContDiff ℝ ((n + 2 : ℕ) : WithTop ℕ∞) f) (hf' : ∀ t, 0 ≤ iteratedDeriv (n + 2) f t) :
    (∫ t in a..b, f t) - closedNewtonCotes n f a b ≤ 0 := by
  classical
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  set h : ℝ := (b - a) / n with hh
  have hpos : 0 < h := by rw [hh]; positivity
  have hnh : (n : ℝ) * h = b - a := by rw [hh]; field_simp
  set x : ℕ → ℝ := fun k => a + k * h with hxdef
  set v : Fin (n + 1) → ℝ := fun i => x i with hvdef
  have hv : Function.Injective v := fun i j hij => Fin.ext (node_injective hn0 hab hij)
  have hxa : x 0 = a := by simp [hxdef]
  have hxb : x n = b := by simp only [hxdef]; linarith
  have hxmem : ∀ k ≤ n, x k ∈ Icc a b := by
    intro k hk
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
    have h0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    refine ⟨by simp only [hxdef]; nlinarith, ?_⟩
    simp only [hxdef]
    have : (k : ℝ) * h ≤ n * h := mul_le_mul_of_nonneg_right hk' hpos.le
    linarith
  set P : ℝ[X] := Lagrange.interpolate Finset.univ v fun i => f (v i) with hP
  set g₀ : ℝ → ℝ := fun t => f t - P.eval t with hg₀
  have hg₀node : ∀ k ≤ n, g₀ (x k) = 0 := by
    intro k hk
    have : x k = v ⟨k, Nat.lt_succ_of_le hk⟩ := rfl
    simp only [hg₀, this, hP, Lagrange.eval_interpolate_at_node _ hv.injOn (Finset.mem_univ _),
      sub_self]
  -- the error is the integral of `f - Π_n f`
  have hE : (∫ t in a..b, f t) - closedNewtonCotes n f a b = ∫ t in a..b, g₀ t := by
    have hNC : closedNewtonCotes n f a b = ∫ t in a..b, P.eval t := by
      rw [closedNewtonCotes_eq_sum_integral_basis hn0 hab]
      simp only [hP, Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C]
      rw [integral_finsetSum fun i _ =>
        ((Polynomial.continuous _).const_mul _).intervalIntegrable _ _]
      exact Finset.sum_congr rfl fun i _ => by rw [integral_const_mul]; ring
    rw [hNC, ← integral_sub ((hf.continuous).intervalIntegrable _ _)
      ((Polynomial.continuous _).intervalIntegrable _ _)]
  -- the divided difference `f[x_0, …, x_n, ·]`, smooth across the nodes as an iterated `dslope`
  let G : ℕ → ℝ → ℝ := fun k => Nat.rec g₀ (fun k Gk => dslope Gk (x k)) k
  have hGsucc : ∀ k, G (k + 1) = dslope (G k) (x k) := fun k => rfl
  have hGsmooth : ∀ k ≤ n + 1, ContDiff ℝ ((n + 2 - k : ℕ) : WithTop ℕ∞) (G k) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact hf.sub (contDiff_eval P _)
    | succ k ih =>
      intro hk
      have e : n + 2 - k = (n + 2 - (k + 1)) + 1 := by omega
      have := ih (by omega)
      rw [e] at this
      rw [hGsucc]
      exact this.dslope (x k)
  have hGeq : ∀ k ≤ n + 1, ∀ t, (∀ j < k, t ≠ x j) →
      G k t = g₀ t / ∏ j ∈ Finset.range k, (t - x j) := by
    intro k
    induction k with
    | zero => intro _ t _; change g₀ t = _; simp
    | succ k ih =>
      intro hk t ht
      have hGk0 : G k (x k) = 0 := by
        rw [ih (by omega) (x k) fun j hj hjk => absurd (node_injective hn0 hab hjk) (by omega)]
        rw [hg₀node k (by omega), zero_div]
      rw [hGsucc, dslope_of_ne _ (ht k (Nat.lt_succ_self k)), slope_def_field, hGk0, sub_zero,
        ih (by omega) t fun j hj => ht j (Nat.lt_succ_of_lt hj), Finset.prod_range_succ, div_div]
  set φ : ℝ → ℝ := G (n + 1) with hφ
  have hφC1 : ContDiff ℝ 1 φ := by
    have := hGsmooth (n + 1) le_rfl
    rwa [show n + 2 - (n + 1) = 1 by omega] at this
  set D : ℝ → ℝ := deriv φ with hD
  have hφD : ∀ t, HasDerivAt φ (D t) t := fun t =>
    (hφC1.differentiable one_ne_zero t).hasDerivAt
  have hDc : Continuous D := hφC1.continuous_deriv le_rfl
  -- the nodal polynomial and its primitive `W`
  set ω : ℝ → ℝ := fun t => ∏ j ∈ Finset.range (n + 1), (t - x j) with hω
  have hωc : Continuous ω := by fun_prop
  have hφω : ∀ t, g₀ t = φ t * ω t := by
    intro t
    by_cases hnode : ∃ j < n + 1, t = x j
    · obtain ⟨j, hj, rfl⟩ := hnode
      rw [hg₀node j (by omega), hω]
      simp only
      rw [Finset.prod_eq_zero (Finset.mem_range.2 hj) (sub_self _), mul_zero]
    · push Not at hnode
      have hne : ω t ≠ 0 := by
        simp only [hω]
        exact Finset.prod_ne_zero_iff.2 fun j hj => sub_ne_zero.2 (hnode j (Finset.mem_range.1 hj))
      rw [hφ, hGeq (n + 1) le_rfl t hnode]
      simp only [hω] at hne ⊢
      rw [div_mul_cancel₀ _ hne]
  set W : ℝ → ℝ := fun t => ∫ s in a..t, ω s with hW
  have hWd : ∀ t, HasDerivAt W (ω t) t := fun t =>
    (hωc.integral_hasStrictDerivAt a t).hasDerivAt
  -- `W` is the scaled reference primitive `h^{n+2} ∫_0^{(t - a)/h} π_{n+1}`
  have hωπ : ∀ s : ℝ, ω (h * s + a) = h ^ (n + 1) * (intNodal n).eval s := by
    intro s
    simp only [hω, hxdef, intNodal_eval_eq_prod_range]
    have e : ∀ j ∈ Finset.range (n + 1), h * s + a - (a + j * h) = h * (s - j) := fun j _ => by
      ring
    rw [Finset.prod_congr rfl e, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have hWval : ∀ t, W t = h ^ (n + 2) * ∫ s in (0 : ℝ)..((t - a) / h), (intNodal n).eval s := by
    intro t
    have hcov := integral_comp_mul_add (fun s => ω s) (a := 0) (b := (t - a) / h) hpos.ne' a
    simp only [mul_zero, zero_add, smul_eq_mul] at hcov
    rw [mul_div_cancel₀ _ hpos.ne', sub_add_cancel] at hcov
    have hI : (∫ s in (0 : ℝ)..((t - a) / h), ω (h * s + a))
        = h ^ (n + 1) * ∫ s in (0 : ℝ)..((t - a) / h), (intNodal n).eval s := by
      rw [← integral_const_mul]
      exact integral_congr fun s _ => hωπ s
    rw [hI] at hcov
    calc W t = h * (h⁻¹ * W t) := by field_simp
      _ = h * (h ^ (n + 1) * ∫ s in (0 : ℝ)..((t - a) / h), (intNodal n).eval s) := by
          rw [← hcov]
      _ = _ := by ring
  have hWnn : ∀ t ∈ Icc a b, 0 ≤ W t := by
    intro t ht
    rw [hWval]
    refine mul_nonneg (by positivity) (integral_intNodal_nonneg_of_even hn ?_ ?_)
    · exact div_nonneg (by linarith [ht.1]) hpos.le
    · rw [div_le_iff₀ hpos]
      linarith [ht.2]
  have hWa : W a = 0 := by simp [hW]
  have hWb : W b = 0 := by
    have hba : (b - a) / h = n := by
      have : b - a ≠ 0 := by linarith
      rw [hh]
      field_simp
    rw [hWval, hba]
    have := newtonCotesK_eq_zero_of_even hn
    rw [newtonCotesK] at this
    rw [this, mul_zero]
  -- integration by parts
  have hparts := integral_mul_deriv_eq_deriv_mul (a := a) (b := b) (u := φ) (u' := D) (v := W)
    (v' := ω) (fun t _ => hφD t) (fun t _ => hWd t) (hDc.intervalIntegrable _ _)
    (hωc.intervalIntegrable _ _)
  -- `φ' ≥ 0` away from the nodes: it is a Hermite coefficient, a value of `f^{(n+2)}/(n+2)!`
  have hDnn : ∀ t ∈ Ioo a b, t ∉ Set.range v → 0 ≤ D t := by
    intro t ht htv
    have hopen : IsOpen (Set.range v)ᶜ := (Set.finite_range v).isClosed.isOpen_compl
    have hφloc : φ =ᶠ[𝓝 t] fun y => DividedDifference.newton f (Fin.snoc v y) := by
      filter_upwards [hopen.mem_nhds htv] with y hy
      have hy' : Function.Injective (Fin.snoc v y : Fin (n + 2) → ℝ) :=
        Fin.snoc_injective_iff.2 ⟨hv, hy⟩
      rw [DividedDifference.eval_interpolate_snoc_sub f hy', hφ, hGeq (n + 1) le_rfl y
        fun j hj hyj => hy ⟨⟨j, hj⟩, hyj.symm⟩]
      congr 1
      exact (Fin.prod_univ_eq_prod_range (fun j => y - x j) (n + 1)).symm
    have hdiff : DifferentiableAt ℝ f t :=
      hf.differentiable (by exact_mod_cast Nat.succ_ne_zero (n + 1)) t
    have hnd := DividedDifference.hasDerivAt_newton_snoc hv htv hdiff
    have hDt : D t = (Hermite.interpolate (Fin.snoc v t) (Fin.snoc (fun _ => 0) 1) f).coeff
        (n + 2) := (hφD t).unique (hnd.congr_of_eventuallyEq hφloc)
    -- Rolle with multiplicities for `f - H`
    set w : Fin (n + 2) → ℝ := Fin.snoc v t with hw
    set μ : Fin (n + 2) → ℕ := Fin.snoc (fun _ => 0) 1 with hμ
    set H : ℝ[X] := Hermite.interpolate w μ f with hH
    have hwinj : Function.Injective w := Fin.snoc_injective_iff.2 ⟨hv, htv⟩
    have hwmem : ∀ i, w i ∈ Icc a b := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [hw, Fin.snoc_last]
        exact Ioo_subset_Icc_self ht
      · simp only [hw, Fin.snoc_castSucc]
        exact hxmem j (Nat.lt_succ_iff.1 j.2)
    have hμsum : ∑ i, (μ i + 1) = n + 1 + 2 := by
      rw [Fin.sum_univ_castSucc]
      simp [hμ, Fin.snoc_castSucc, Fin.snoc_last]
    have hHdeg : H.natDegree ≤ n + 2 := by
      have := Hermite.degree_interpolate_lt hwinj μ f
      rw [hμsum] at this
      exact natDegree_le_of_degree_le (Order.le_of_lt_succ (by exact_mod_cast this))
    set g : ℝ → ℝ := f - fun y => H.eval y with hg
    have hgC : ContDiff ℝ ((n + 1 + 1 : ℕ) : WithTop ℕ∞) g := hf.sub (contDiff_eval H _)
    have hzero : ∀ i, ∀ j ≤ μ i, iteratedDeriv j g (w i) = 0 := by
      intro i j hj
      have hj2 : j ≤ n + 2 := by
        have : μ i ≤ 1 := by
          refine Fin.lastCases ?_ (fun k => ?_) i <;> simp [hμ, Fin.snoc_last, Fin.snoc_castSucc]
        omega
      rw [hg, iteratedDeriv_sub (hf.contDiffAt.of_le (by exact_mod_cast hj2))
        (contDiff_eval H _).contDiffAt]
      simp only [Polynomial.iteratedDeriv_eval]
      rw [Hermite.eval_iterate_derivative_interpolate hwinj i hj, sub_self]
    obtain ⟨ξ, hξ, hξ0⟩ := Hermite.exists_iteratedDeriv_eq_zero (N := n + 1) hgC hwinj hwmem
      hμsum hzero
    rw [hg, iteratedDeriv_sub hf.contDiffAt (contDiff_eval H _).contDiffAt] at hξ0
    simp only [Polynomial.iteratedDeriv_eval,
      Polynomial.iterate_derivative_eq_C_of_natDegree_le hHdeg, eval_C] at hξ0
    rw [hDt]
    have hfac : (0 : ℝ) < (n + 2).factorial := by positivity
    have := hf' ξ
    exact (mul_nonneg_iff_of_pos_left hfac).1 (by linarith)
  -- hence `∫ φ' W ≥ 0`, and the error is `-∫ φ' W`
  have hint : 0 ≤ ∫ t in a..b, D t * W t := by
    refine integral_nonneg_of_ae_restrict hab.le ?_
    have hfin : ∀ᵐ t ∂volume, t ∉ Set.range v :=
      (Set.finite_range v).countable.ae_notMem volume
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc,
      MeasureTheory.ae_restrict_of_ae hfin] with t ht htv
    have hta : t ≠ a := fun h => htv ⟨0, by simp [hvdef, hxdef, h]⟩
    have htb : t ≠ b := fun h => htv ⟨Fin.last n, by simp only [hvdef, Fin.val_last, hxb, h]⟩
    exact mul_nonneg (hDnn t ⟨lt_of_le_of_ne ht.1 (Ne.symm hta), lt_of_le_of_ne ht.2 htb⟩ htv)
      (hWnn t ht)
  rw [hE, integral_congr fun t _ => hφω t, hparts, hWa, hWb]
  linarith

/-- The Peano kernel of the closed rule with even `n`, at order `n + 1`: the notation for the
next three statements. -/
private theorem closedNewtonCotes_exact_aux (hn : Even n) (hn0 : 0 < n) (hab : a < b) :
    ∀ p : ℝ[X], p.degree ≤ ((n + 1 : ℕ) : WithBot ℕ) →
      (∫ t in a..b, p.eval t) = ∑ i : Fin (n + 1),
        (b - a) / n * newtonCotesWeight n i * p.eval (a + i * ((b - a) / n)) := by
  intro p hp
  rw [integral_eq_closedNewtonCotes_of_even hn hn0 hab (by exact_mod_cast hp), closedNewtonCotes,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Sign constancy of the Peano kernel of the closed rule with even `n`** (Steffensen): with the
weights `h w_i`, the nodes `a + i h` and the order `n + 1`, `K_{n+1}(t) ≤ 0` on `[a, b]`.

If `K_{n+1}(t₀) > 0` at an interior point, then for a `C^{n+2}` integrand whose `(n+2)`-nd
derivative is a bump concentrated where `K_{n+1} > 0`, Peano's theorem gives a positive error, while
`sub_closedNewtonCotes_nonpos_of_even` gives a nonpositive one. The endpoints follow by
continuity. -/
theorem peanoKernel_closedNewtonCotes_nonpos_of_even (hn : Even n) (hn0 : 0 < n) (hab : a < b)
    {t : ℝ} (ht : t ∈ Icc a b) :
    peanoKernel a b (fun i : Fin (n + 1) => (b - a) / n * newtonCotesWeight n i)
      (fun i : Fin (n + 1) => a + i * ((b - a) / n)) (n + 1) t ≤ 0 := by
  set w' : Fin (n + 1) → ℝ := fun i => (b - a) / n * newtonCotesWeight n i with hw'
  set z : Fin (n + 1) → ℝ := fun i => a + i * ((b - a) / n) with hz
  set K : ℝ → ℝ := peanoKernel a b w' z (n + 1) with hK
  have hKc : ContinuousOn K (Icc a b) := continuousOn_peanoKernel w' z (by omega)
  have hzmem : ∀ i, z i ∈ Icc a b := fun i => closedNewtonCotes_node_mem hn0 hab.le i
  have hexact := closedNewtonCotes_exact_aux hn hn0 hab
  -- the interior
  have hIoo : ∀ t ∈ Ioo a b, K t ≤ 0 := by
    intro t ht
    by_contra hpos
    push Not at hpos
    have hcont : ContinuousAt K t := hKc.continuousAt (Icc_mem_nhds ht.1 ht.2)
    obtain ⟨r, hr, hball⟩ : ∃ r > 0, ∀ s, |s - t| < r → 0 < K s := by
      obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff.1 (hcont.eventually (lt_mem_nhds hpos))
      exact ⟨r, hr, fun s hs => h (by rwa [Real.dist_eq])⟩
    let ψ : ContDiffBump t := ⟨r / 2, r, by positivity, by linarith⟩
    obtain ⟨g, hg, hgψ⟩ := exists_contDiff_iteratedDeriv_eq (n + 2) ψ.continuous
    -- Peano's theorem for `g`
    have hF : ∀ k ≤ n + 1, ∀ s ∈ Icc a b,
        HasDerivAt (iteratedDeriv k g) (iteratedDeriv (k + 1) g s) s := by
      intro k hk s _
      have hd := hg.differentiable_iteratedDeriv k (by exact_mod_cast (by omega : k < n + 2))
      rw [iteratedDeriv_succ]
      exact (hd s).hasDerivAt
    have hc : ContinuousOn (iteratedDeriv (n + 1 + 1) g) (Icc a b) := by
      rw [hgψ]
      exact ψ.continuous.continuousOn
    have hpeano := error_eq_integral_peanoKernel (F := fun k => iteratedDeriv k g) (m := n + 1)
      hab.le hzmem hF hc hexact
    simp only [iteratedDeriv_zero, hgψ] at hpeano
    have hNC : ∑ i, w' i * g (z i) = closedNewtonCotes n g a b := by
      rw [closedNewtonCotes, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by simp only [hw', hz]; ring
    rw [hNC] at hpeano
    -- the kernel integral against the bump is positive
    have hprod : ∀ s ∈ Icc a b, 0 ≤ K s * ψ s := by
      intro s _
      by_cases hs : |s - t| < r
      · exact mul_nonneg (hball s hs).le ψ.nonneg
      · rw [ψ.zero_of_le_dist (by rw [Real.dist_eq]; exact not_lt.1 hs), mul_zero]
    have hpos' : 0 < ∫ s in a..b, K s * ψ s :=
      integral_pos_of_continuousOn_of_nonneg hab (hKc.mul ψ.continuous.continuousOn) hprod ht
        (mul_pos hpos (ψ.pos_of_mem_ball (Metric.mem_ball_self hr)))
    -- but the error is nonpositive
    have hnonpos := sub_closedNewtonCotes_nonpos_of_even hn hn0 hab hg fun s => by
      rw [hgψ]; exact ψ.nonneg
    rw [hpeano] at hnonpos
    exact absurd hpos' (not_lt.2 hnonpos)
  -- the endpoints, by continuity
  rcases eq_or_lt_of_le ht.1 with hta | hta
  · rw [← hta]
    have hlim : Tendsto K (𝓝[Ioo a b] a) (𝓝 (K a)) :=
      (hKc a (left_mem_Icc.2 hab.le)).mono_left (nhdsWithin_mono _ Ioo_subset_Icc_self)
    have := left_nhdsWithin_Ioo_neBot hab
    exact le_of_tendsto hlim (eventually_nhdsWithin_of_forall hIoo)
  rcases eq_or_lt_of_le ht.2 with htb | htb
  · rw [htb]
    have hlim : Tendsto K (𝓝[Ioo a b] b) (𝓝 (K b)) :=
      (hKc b (right_mem_Icc.2 hab.le)).mono_left (nhdsWithin_mono _ Ioo_subset_Icc_self)
    have := right_nhdsWithin_Ioo_neBot hab
    exact le_of_tendsto hlim (eventually_nhdsWithin_of_forall hIoo)
  exact hIoo t ⟨hta, htb⟩

/-- **The kernel integral is the error at one monomial**: for even `n > 0`,
`∫_a^b K_{n+1} = M_n/(n + 2)! · h^{n+3}`, `h = (b - a)/n`. Peano's theorem at
`x^{n+2}/(n+2)!` identifies `∫ K_{n+1}` with the error at that monomial; since the rule is exact to
degree `n + 1` and `x^{n+2} = ω_{n+1}(x)(x - b) + (\text{degree} ≤ n + 1)`, that error is
`∫_a^b ω_{n+1}(x)(x - b) dx`, which the substitution `x = a + τ h`, `t = n - τ` turns into
`h^{n+3} ∫_0^n t π_{n+1}(t) dt`.

Reference: [quarteroni2000numerical], the computation after (9.23). -/
theorem integral_peanoKernel_closedNewtonCotes_of_even (hn : Even n) (hn0 : 0 < n) (hab : a < b) :
    (∫ t in a..b, peanoKernel a b (fun i : Fin (n + 1) => (b - a) / n * newtonCotesWeight n i)
        (fun i : Fin (n + 1) => a + i * ((b - a) / n)) (n + 1) t)
      = newtonCotesM n / (n + 2).factorial * ((b - a) / n) ^ (n + 3) := by
  classical
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  set h : ℝ := (b - a) / n with hh
  have hpos : 0 < h := by rw [hh]; positivity
  have hnh : (n : ℝ) * h = b - a := by rw [hh]; field_simp
  set w' : Fin (n + 1) → ℝ := fun i => h * newtonCotesWeight n i with hw'
  set z : Fin (n + 1) → ℝ := fun i => a + i * h with hz
  have hzmem : ∀ i, z i ∈ Icc a b := fun i => closedNewtonCotes_node_mem hn0 hab.le i
  have hexact : ∀ p : ℝ[X], p.degree ≤ ((n + 1 : ℕ) : WithBot ℕ) →
      (∫ t in a..b, p.eval t) = ∑ i, w' i * p.eval (z i) :=
    closedNewtonCotes_exact_aux hn hn0 hab
  -- Peano's theorem at `q = x^{n+2}/(n+2)!`
  set c : ℝ := ((n + 1 + 1).factorial : ℝ)⁻¹ with hc
  set q : ℝ[X] := C c * X ^ (n + 1 + 1) with hq
  have hqnat : q.natDegree ≤ n + 1 + 1 := natDegree_C_mul_X_pow_le c (n + 1 + 1)
  set F : ℕ → ℝ → ℝ := fun k t => (derivative^[k] q).eval t with hF
  have hFd : ∀ k ≤ n + 1, ∀ t ∈ Icc a b, HasDerivAt (F k) (F (k + 1) t) t := by
    intro k _ t _
    have := (derivative^[k] q).hasDerivAt t
    simpa only [hF, Function.iterate_succ_apply'] using this
  have hFtop : F (n + 1 + 1) = fun _ => 1 := by
    funext t
    change (derivative^[n + 1 + 1] q).eval t = 1
    rw [Polynomial.iterate_derivative_eq_C_of_natDegree_le hqnat, eval_C, hq, coeff_C_mul,
      coeff_X_pow]
    simp only [ite_true, mul_one, hc]
    field_simp
  have hpeano := error_eq_integral_peanoKernel (F := F) (m := n + 1) hab.le hzmem hFd
    (by rw [hFtop]; exact continuousOn_const) hexact
  rw [hFtop] at hpeano
  simp only [mul_one] at hpeano
  rw [← hpeano]
  -- the error at `x^{n+2}`
  set ω : ℝ[X] := ∏ i : Fin (n + 1), (X - C (z i)) with hω
  have hωmonic : ω.Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (z i)
  have hωnat : ω.natDegree = n + 1 := by
    rw [hω, natDegree_prod _ _ fun i _ => (monic_X_sub_C (z i)).ne_zero]
    simp
  have hωz : ∀ i, ω.eval (z i) = 0 := fun i => by
    rw [hω, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  set r : ℝ[X] := X ^ (n + 1 + 1) - ω * (X - C b) with hr
  have hrdeg : r.degree ≤ ((n + 1 : ℕ) : WithBot ℕ) := by
    have hmon : (ω * (X - C b)).Monic := hωmonic.mul (monic_X_sub_C b)
    have hdeg : (ω * (X - C b)).natDegree = n + 1 + 1 := by
      rw [natDegree_mul hωmonic.ne_zero (monic_X_sub_C b).ne_zero, hωnat, natDegree_X_sub_C]
    have h1 : (X ^ (n + 1 + 1) : ℝ[X]).degree = (ω * (X - C b)).degree := by
      rw [degree_X_pow, degree_eq_natDegree hmon.ne_zero, hdeg]
    have hlt := degree_sub_lt_left h1 (by simp) (by rw [leadingCoeff_X_pow, hmon.leadingCoeff])
    rw [degree_X_pow] at hlt
    exact Order.le_of_lt_succ (by exact_mod_cast hlt)
  have hsplit : ∀ t, F 0 t = c * (ω.eval t * (t - b) + r.eval t) := by
    intro t
    simp only [hF, Function.iterate_zero, id, hq, eval_mul, eval_C, eval_pow, eval_X, hr,
      eval_sub]
    ring
  have hrexact := hexact r hrdeg
  have hωint : IntervalIntegrable (fun t => ω.eval t * (t - b)) volume a b :=
    (by fun_prop : Continuous fun t => ω.eval t * (t - b)).intervalIntegrable _ _
  have hrint : IntervalIntegrable (fun t => r.eval t) volume a b :=
    (Polynomial.continuous _).intervalIntegrable _ _
  have hlhs : (∫ t in a..b, F 0 t) - ∑ i, w' i * F 0 (z i)
      = c * ∫ t in a..b, ω.eval t * (t - b) := by
    have h1 : (∫ t in a..b, F 0 t)
        = c * ((∫ t in a..b, ω.eval t * (t - b)) + ∫ t in a..b, r.eval t) := by
      rw [← integral_add hωint hrint, ← integral_const_mul]
      exact integral_congr fun t _ => hsplit t
    have h2 : ∑ i, w' i * F 0 (z i) = c * ∑ i, w' i * r.eval (z i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hsplit, hωz]; ring
    rw [h1, h2, ← hrexact]
    ring
  rw [hlhs]
  -- the substitution `x = a + τ h`, `t = n - τ`
  have hωπ : ∀ s : ℝ, ω.eval (h * s + a) = h ^ (n + 1) * (intNodal n).eval s := by
    intro s
    rw [hω, eval_prod, intNodal_eval]
    have e : ∀ i : Fin (n + 1), (X - C (z i)).eval (h * s + a) = h * (s - i) := fun i => by
      simp only [eval_sub, eval_X, eval_C, hz]; ring
    rw [Finset.prod_congr rfl fun i _ => e i, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  have hcov := integral_comp_mul_add (fun t => ω.eval t * (t - b)) (a := 0) (b := n) hpos.ne' a
  simp only [mul_zero, zero_add, smul_eq_mul] at hcov
  rw [show h * n + a = b by linarith] at hcov
  have hI : (∫ s in (0 : ℝ)..n, ω.eval (h * s + a) * (h * s + a - b))
      = h ^ (n + 2) * ∫ s in (0 : ℝ)..n, (intNodal n).eval s * (s - n) := by
    rw [← integral_const_mul]
    refine integral_congr fun s _ => ?_
    rw [hωπ, show h * s + a - b = h * (s - n) by linarith]
    ring
  have hM : (∫ s in (0 : ℝ)..n, (intNodal n).eval s * (s - n)) = newtonCotesM n := by
    have h := integral_comp_sub_left (fun s => (intNodal n).eval s * (s - n)) (a := 0) (b := n)
      (n : ℝ)
    simp only [sub_self, sub_zero] at h
    rw [← h, newtonCotesM]
    refine integral_congr fun s _ => ?_
    rw [intNodal_comp_sub, hn.add_one.neg_one_pow]
    ring
  rw [hI, hM] at hcov
  have hint : (∫ t in a..b, ω.eval t * (t - b)) = h ^ (n + 3) * newtonCotesM n := by
    calc (∫ t in a..b, ω.eval t * (t - b)) = h * (h⁻¹ * ∫ t in a..b, ω.eval t * (t - b)) := by
          field_simp
      _ = h * (h ^ (n + 2) * newtonCotesM n) := by rw [← hcov]
      _ = _ := by ring
  rw [hint, hc]
  ring

/-- **The error of the closed Newton–Cotes rules with even `n`** ([quarteroni2000numerical]
Theorem 9.2, (9.19)): for even `n > 0`, `a < b` and `f` of class `C^{n+2}` on an open set
containing `[a, b]`,
`∫_a^b f - I_n(f) = M_n/(n + 2)! · h^{n+3} · f^{(n+2)}(ξ)` for some `ξ ∈ (a, b)`, with
`h = (b - a)/n` and `M_n = ∫_0^n t π_{n+1}(t) dt < 0` (`newtonCotesM_neg`).

Peano's theorem at order `n + 1` (the rule is exact to degree `n + 1`), the sign constancy of the
kernel, its integral, and the weighted mean value theorem for integrals. -/
theorem exists_sub_closedNewtonCotes_eq_of_even (hn : Even n) (hn0 : 0 < n) (hab : a < b)
    {U : Set ℝ} (hU : IsOpen U) (hUab : Icc a b ⊆ U)
    (hf : ContDiffOn ℝ ((n + 2 : ℕ) : WithTop ℕ∞) f U) :
    ∃ ξ ∈ Ioo a b, (∫ t in a..b, f t) - closedNewtonCotes n f a b
      = newtonCotesM n / (n + 2).factorial * ((b - a) / n) ^ (n + 3)
        * iteratedDeriv (n + 2) f ξ := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  set w' : Fin (n + 1) → ℝ := fun i => (b - a) / n * newtonCotesWeight n i with hw'
  set z : Fin (n + 1) → ℝ := fun i => a + i * ((b - a) / n) with hz
  set K : ℝ → ℝ := peanoKernel a b w' z (n + 1) with hK
  have hzmem : ∀ i, z i ∈ Icc a b := fun i => closedNewtonCotes_node_mem hn0 hab.le i
  have hF : ∀ k ≤ n + 1, ∀ t ∈ Icc a b,
      HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f t) t := fun k hk t ht =>
    hf.hasDerivAt_iteratedDeriv_of_isOpen hU (by omega) (hUab ht)
  have hc : ContinuousOn (iteratedDeriv (n + 1 + 1) f) (Icc a b) :=
    (hf.continuousOn_iteratedDeriv_of_isOpen hU le_rfl).mono hUab
  have hpeano := error_eq_integral_peanoKernel (F := fun k => iteratedDeriv k f) (m := n + 1)
    hab.le hzmem hF hc (closedNewtonCotes_exact_aux hn hn0 hab)
  simp only [iteratedDeriv_zero] at hpeano
  have hNC : ∑ i, w' i * f (z i) = closedNewtonCotes n f a b := by
    rw [closedNewtonCotes, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp only [hw', hz]; ring
  rw [hNC] at hpeano
  have hKint := integral_peanoKernel_closedNewtonCotes_of_even hn hn0 hab
  have hKneg : (∫ t in a..b, K t) < 0 := by
    rw [hK, hKint]
    have := newtonCotesM_neg hn hn0
    have hfac : (0 : ℝ) < (n + 2).factorial := by positivity
    have hpow : (0 : ℝ) < ((b - a) / n) ^ (n + 3) := by positivity
    have : newtonCotesM n / (n + 2).factorial < 0 := div_neg_of_neg_of_pos this hfac
    exact mul_neg_of_neg_of_pos this hpow
  obtain ⟨ξ, hξ, hξval⟩ := exists_mem_Ioo_integral_mul_eq_mul_integral_of_nonpos hab
    (continuousOn_peanoKernel w' z (by omega)) hc
    (fun t ht => peanoKernel_closedNewtonCotes_nonpos_of_even hn hn0 hab ht) hKneg
  refine ⟨ξ, hξ, ?_⟩
  rw [hpeano, hξval, hKint]
  ring

/-- **The degree of exactness of the closed rule with even `n` is exactly `n + 1`**: the rule is
not exact on the monomial `x^{n+2}`, whose `(n+2)`-nd derivative is the nonzero constant
`(n+2)!`, while `M_n ≠ 0`.

Reference: [quarteroni2000numerical], Theorem 9.2 ("the degree of exactness is equal to
`n + 1`"). -/
theorem not_integral_eq_closedNewtonCotes_of_even (hn : Even n) (hn0 : 0 < n) (hab : a < b) :
    (∫ t in a..b, t ^ (n + 2)) ≠ closedNewtonCotes n (fun t => t ^ (n + 2)) a b := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have hcd : ContDiffOn ℝ ((n + 2 : ℕ) : WithTop ℕ∞) (fun t : ℝ => t ^ (n + 2)) univ :=
    (contDiff_id.pow _).contDiffOn
  obtain ⟨ξ, -, hξ⟩ := exists_sub_closedNewtonCotes_eq_of_even hn hn0 hab isOpen_univ
    (subset_univ _) hcd
  have hder : iteratedDeriv (n + 2) (fun t : ℝ => t ^ (n + 2)) ξ = (n + 2).factorial := by
    have e : (fun t : ℝ => t ^ (n + 2)) = fun t => (X ^ (n + 2) : ℝ[X]).eval t := by
      funext t; simp
    rw [e, Polynomial.iteratedDeriv_eval,
      Polynomial.iterate_derivative_eq_C_of_natDegree_le (natDegree_X_pow_le (R := ℝ) (n + 2))]
    simp
  rw [hder] at hξ
  intro heq
  rw [heq, sub_self] at hξ
  have hM := newtonCotesM_neg hn hn0
  have hfac : (0 : ℝ) < (n + 2).factorial := by positivity
  have hpow : (0 : ℝ) < ((b - a) / n) ^ (n + 3) := by positivity
  have : newtonCotesM n / (n + 2).factorial * ((b - a) / n) ^ (n + 3) * (n + 2).factorial
      = newtonCotesM n * ((b - a) / n) ^ (n + 3) := by field_simp
  rw [this] at hξ
  exact absurd hξ.symm (mul_neg_of_neg_of_pos hM hpow).ne

/-- **The error of the closed rule at the monomial `x^{n+1}`**: for `0 < n` and `a < b`,
`∫_a^b x^{n+1} - I_n(x^{n+1}) = h^{n+2} K_n`, `h = (b - a)/n`.

The rule is exact to degree `n` and `x^{n+1} = ω_{n+1}(x) + (\text{degree} ≤ n)` with `ω_{n+1}` the
nodal polynomial, which the rule annihilates; so the error is `∫_a^b ω_{n+1}`, which the
substitution `x = a + τ h` turns into `h^{n+2} ∫_0^n π_{n+1}`. -/
theorem integral_sub_closedNewtonCotes_pow_eq (hn : 0 < n) (hab : a < b) :
    (∫ t in a..b, t ^ (n + 1)) - closedNewtonCotes n (fun t => t ^ (n + 1)) a b
      = ((b - a) / n) ^ (n + 2) * newtonCotesK n := by
  classical
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set h : ℝ := (b - a) / n with hh
  have hpos : 0 < h := by rw [hh]; positivity
  have hnh : (n : ℝ) * h = b - a := by rw [hh]; field_simp
  set z : Fin (n + 1) → ℝ := fun i => a + ((i : ℕ) : ℝ) * h with hz
  set ω : ℝ[X] := ∏ i : Fin (n + 1), (X - C (z i)) with hω
  have hωmonic : ω.Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (z i)
  have hωnat : ω.natDegree = n + 1 := by
    rw [hω, natDegree_prod _ _ fun i _ => (monic_X_sub_C (z i)).ne_zero]
    simp
  have hωz : ∀ i, ω.eval (z i) = 0 := fun i => by
    rw [hω, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  set r : ℝ[X] := X ^ (n + 1) - ω with hr
  have hrdeg : r.degree ≤ (n : WithBot ℕ) := by
    have h1 : (X ^ (n + 1) : ℝ[X]).degree = ω.degree := by
      rw [degree_X_pow, degree_eq_natDegree hωmonic.ne_zero, hωnat]
    have hlt := degree_sub_lt_left h1 (by simp) (by rw [leadingCoeff_X_pow, hωmonic.leadingCoeff])
    rw [degree_X_pow] at hlt
    exact Order.le_of_lt_succ (by exact_mod_cast hlt)
  have hsplit : ∀ t : ℝ, t ^ (n + 1) = ω.eval t + r.eval t := by
    intro t
    simp only [hr, eval_sub, eval_pow, eval_X]
    ring
  have hωint : IntervalIntegrable (fun t => ω.eval t) volume a b :=
    (Polynomial.continuous _).intervalIntegrable _ _
  have hrint : IntervalIntegrable (fun t => r.eval t) volume a b :=
    (Polynomial.continuous _).intervalIntegrable _ _
  have hrexact := integral_eq_closedNewtonCotes_of_degree_le hn hab hrdeg
  -- split the error
  have hlhs : (∫ t in a..b, t ^ (n + 1)) - closedNewtonCotes n (fun t => t ^ (n + 1)) a b
      = ∫ t in a..b, ω.eval t := by
    have h1 : (∫ t in a..b, t ^ (n + 1))
        = (∫ t in a..b, ω.eval t) + ∫ t in a..b, r.eval t := by
      rw [← integral_add hωint hrint]
      exact integral_congr fun t _ => hsplit t
    have h2 : closedNewtonCotes n (fun t => t ^ (n + 1)) a b
        = closedNewtonCotes n (fun t => r.eval t) a b := by
      rw [closedNewtonCotes, closedNewtonCotes]
      refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
      rw [hsplit, show a + ((i : ℕ) : ℝ) * ((b - a) / n) = z i from rfl, hωz, zero_add]
    rw [h1, h2, ← hrexact]
    ring
  rw [hlhs]
  -- the substitution `x = a + τ h`
  have hωπ : ∀ s : ℝ, ω.eval (h * s + a) = h ^ (n + 1) * (intNodal n).eval s := by
    intro s
    rw [hω, eval_prod, intNodal_eval]
    have e : ∀ i : Fin (n + 1), (X - C (z i)).eval (h * s + a) = h * (s - i) := fun i => by
      simp only [eval_sub, eval_X, eval_C, hz]; ring
    rw [Finset.prod_congr rfl fun i _ => e i, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  have hcov := integral_comp_mul_add (fun t => ω.eval t) (a := (0 : ℝ)) (b := (n : ℝ)) hpos.ne' a
  simp only [smul_eq_mul, mul_zero, zero_add] at hcov
  rw [show h * (n : ℝ) + a = b by linarith] at hcov
  have hI : (∫ s in (0 : ℝ)..(n : ℝ), ω.eval (h * s + a))
      = h ^ (n + 1) * ∫ s in (0 : ℝ)..(n : ℝ), (intNodal n).eval s := by
    rw [← integral_const_mul]
    exact integral_congr fun s _ => hωπ s
  rw [hI, ← newtonCotesK] at hcov
  calc (∫ t in a..b, ω.eval t) = h * (h⁻¹ * ∫ t in a..b, ω.eval t) := by field_simp
    _ = h * (h ^ (n + 1) * newtonCotesK n) := by rw [← hcov]
    _ = _ := by ring

/-- **The degree of exactness of the closed rule with odd `n` is exactly `n`**: the rule is not
exact on the monomial `x^{n+1}`, whose error is `h^{n+2} K_n` with `K_n < 0`
(`Quadrature.newtonCotesK_neg`).

Reference: [quarteroni2000numerical], Theorem 9.2 ("the degree of exactness is thus equal to
`n`"). -/
theorem not_integral_eq_closedNewtonCotes_of_odd (hn : Odd n) (hab : a < b) :
    (∫ t in a..b, t ^ (n + 1)) ≠ closedNewtonCotes n (fun t => t ^ (n + 1)) a b := by
  have hn0 : 0 < n := hn.pos
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have h := integral_sub_closedNewtonCotes_pow_eq hn0 hab
  have hK := newtonCotesK_neg hn
  have hpow : (0 : ℝ) < ((b - a) / n) ^ (n + 2) := by
    have : (0 : ℝ) < (b - a) / n := by
      have : (0 : ℝ) < b - a := by linarith
      positivity
    positivity
  intro heq
  rw [heq, sub_self] at h
  exact absurd h.symm (mul_neg_of_pos_of_neg hpow hK).ne

/-- **The `O(h^{n+2})` error bound of the closed rules**, for every `n ≥ 1` and every integrand of
class `C^{n+1}`: with `h = (b - a)/n` and `|f^{(n+1)}| ≤ M` on `[a, b]`,

  `|∫_a^b f - I_n(f)| ≤ M/(n + 1)! · h^{n+2} · ∫_0^n |π_{n+1}|`.

The error is the integral of the interpolation error `f - Π_n f`, which the Lagrange error formula
bounds by `M/(n+1)! |ω_{n+1}|`; the substitution `x = a + τ h` scales `∫_a^b |ω_{n+1}|` to
`h^{n+2} ∫_0^n |π_{n+1}|`. For odd `n` this is the order of infinitesimal `n + 2` of the error;
the sharp constant `K_n/(n + 1)!` is the content of the (still open)
`Quadrature.exists_sub_closedNewtonCotes_eq_of_odd`. -/
theorem abs_sub_closedNewtonCotes_le_of_contDiffOn (hn : 0 < n) (hab : a < b) {U : Set ℝ}
    (hU : IsOpen U) (hUab : Icc a b ⊆ U)
    (hf : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f U) {M : ℝ}
    (hM : ∀ t ∈ Icc a b, |iteratedDeriv (n + 1) f t| ≤ M) :
    |(∫ t in a..b, f t) - closedNewtonCotes n f a b|
      ≤ M / (n + 1).factorial * ((b - a) / n) ^ (n + 2)
        * ∫ s in (0 : ℝ)..(n : ℝ), |(intNodal n).eval s| := by
  classical
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set h : ℝ := (b - a) / n with hh
  have hpos : 0 < h := by rw [hh]; positivity
  have hnh : (n : ℝ) * h = b - a := by rw [hh]; field_simp
  set v : Fin (n + 1) → ℝ := fun i => a + ((i : ℕ) : ℝ) * h with hv
  have hvinj : Function.Injective v := closedNewtonCotes_node_injective hn hab
  have hvmem : ∀ i, v i ∈ Icc a b := fun i => closedNewtonCotes_node_mem hn hab.le i
  set P : ℝ[X] := Lagrange.interpolate Finset.univ v fun i => f (v i) with hP
  set ω : ℝ → ℝ := fun t => ∏ i : Fin (n + 1), (t - v i) with hω
  have hωc : Continuous ω := by fun_prop
  have hfc : ContinuousOn f (Icc a b) := (hf.continuousOn).mono hUab
  -- the error is the integral of the interpolation error
  have hE : (∫ t in a..b, f t) - closedNewtonCotes n f a b = ∫ t in a..b, (f t - P.eval t) := by
    have hNC : closedNewtonCotes n f a b = ∫ t in a..b, P.eval t := by
      rw [closedNewtonCotes_eq_sum_integral_basis hn hab]
      simp only [hP, Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C]
      rw [integral_finsetSum fun i _ =>
        ((Polynomial.continuous _).const_mul _).intervalIntegrable _ _]
      exact Finset.sum_congr rfl fun i _ => by rw [integral_const_mul]; ring
    rw [hNC, ← integral_sub (hfc.intervalIntegrable_of_Icc hab.le)
      ((Polynomial.continuous _).intervalIntegrable _ _)]
  -- the pointwise bound
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (hM a (left_mem_Icc.2 hab.le))
  have hbound : ∀ t ∈ Icc a b,
      |f t - P.eval t| ≤ M / (n + 1).factorial * |ω t| := by
    intro t ht
    obtain ⟨ξ, hξ, hξeq⟩ :=
      Lagrange.exists_sub_interpolate_eq_of_contDiffOn hab hU hUab hf hvinj hvmem ht
    rw [hξeq, abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((n + 1).factorial : ℝ))]
    gcongr
    exact hM ξ (Ioo_subset_Icc_self hξ)
  -- integrate the bound
  have hint1 : IntervalIntegrable (fun t => |f t - P.eval t|) volume a b :=
    ((hfc.sub (Polynomial.continuous _).continuousOn).abs).intervalIntegrable_of_Icc hab.le
  have hint2 : IntervalIntegrable (fun t => M / (n + 1).factorial * |ω t|) volume a b :=
    ((hωc.abs.const_mul _)).intervalIntegrable _ _
  have hstep : |(∫ t in a..b, f t) - closedNewtonCotes n f a b|
      ≤ M / (n + 1).factorial * ∫ t in a..b, |ω t| := by
    rw [hE]
    refine le_trans (abs_integral_le_integral_abs hab.le) ?_
    rw [← integral_const_mul]
    exact integral_mono_on hab.le hint1 hint2 hbound
  -- the substitution `x = a + τ h`
  have hωπ : ∀ s : ℝ, ω (h * s + a) = h ^ (n + 1) * (intNodal n).eval s := by
    intro s
    simp only [hω, hv, intNodal_eval]
    have e : ∀ i : Fin (n + 1), h * s + a - (a + ((i : ℕ) : ℝ) * h) = h * (s - i) := fun i => by
      ring
    rw [Finset.prod_congr rfl fun i _ => e i, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  have hcov := integral_comp_mul_add (fun t => |ω t|) (a := (0 : ℝ)) (b := (n : ℝ)) hpos.ne' a
  simp only [smul_eq_mul, mul_zero, zero_add] at hcov
  rw [show h * (n : ℝ) + a = b by linarith] at hcov
  have hI : (∫ s in (0 : ℝ)..(n : ℝ), |ω (h * s + a)|)
      = h ^ (n + 1) * ∫ s in (0 : ℝ)..(n : ℝ), |(intNodal n).eval s| := by
    rw [← integral_const_mul]
    refine integral_congr fun s _ => ?_
    rw [hωπ, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < h ^ (n + 1))]
  rw [hI] at hcov
  have habs : (∫ t in a..b, |ω t|)
      = h ^ (n + 2) * ∫ s in (0 : ℝ)..(n : ℝ), |(intNodal n).eval s| := by
    calc (∫ t in a..b, |ω t|) = h * (h⁻¹ * ∫ t in a..b, |ω t|) := by field_simp
      _ = h * (h ^ (n + 1) * ∫ s in (0 : ℝ)..(n : ℝ), |(intNodal n).eval s|) := by rw [← hcov]
      _ = _ := by ring
  rw [habs] at hstep
  calc |(∫ t in a..b, f t) - closedNewtonCotes n f a b|
      ≤ M / (n + 1).factorial
        * (h ^ (n + 2) * ∫ s in (0 : ℝ)..(n : ℝ), |(intNodal n).eval s|) := hstep
    _ = _ := by ring

end Error

/-! ### The error of the open rules with even `n` -/

section OpenError

variable {n : ℕ} {a b : ℝ} {f : ℝ → ℝ}

/-- The `ℕ`-indexed nodes of the open rule, `a + (j + 1) h` with `h = (b - a)/(n + 2)`, are
distinct. -/
private theorem open_node_injective (hab : a < b) {j k : ℕ}
    (h : a + ((j : ℝ) + 1) * ((b - a) / (n + 2)) = a + ((k : ℝ) + 1) * ((b - a) / (n + 2))) :
    j = k := by
  have hne : (b - a) / ((n : ℝ) + 2) ≠ 0 := by positivity
  have h1 : ((j : ℝ) + 1) * ((b - a) / ((n : ℝ) + 2))
      = ((k : ℝ) + 1) * ((b - a) / ((n : ℝ) + 2)) := by linarith
  have h2 := mul_right_cancel₀ hne h1
  exact_mod_cast (by linarith : (j : ℝ) = (k : ℝ))

/-- **The error of the open rule with even `n` is nonnegative for an integrand with nonnegative
`(n+2)`-nd derivative**, the open counterpart of
`Quadrature.sub_closedNewtonCotes_nonpos_of_even` and the sign half of the error formula.

The route is the same: `f - Π_n f = φ ω` with `φ(x) = f[x_0, …, x_n, x]`, made `C¹` across the
nodes as an iterated `dslope`; integrating by parts against `W(x) = ∫_a^x ω`, which vanishes at
both endpoints of `[a, b]` because the nodal polynomial of the open rule is odd about the
midpoint for even `n`, gives `∫_a^b (f - Π_n f) = -∫_a^b φ' W`; and `φ'(x) = f[x_0, …, x_n, x, x]`
is a value of `f^{(n+2)}/(n+2)!`. The sign is opposite to the closed case because here `W ≤ 0`
(`Quadrature.integral_intNodal_neg_one_mul_nonneg`). -/
theorem sub_openNewtonCotes_nonneg_of_even (hn : Even n) (hab : a < b)
    (hf : ContDiff ℝ ((n + 2 : ℕ) : WithTop ℕ∞) f) (hf' : ∀ t, 0 ≤ iteratedDeriv (n + 2) f t) :
    0 ≤ (∫ t in a..b, f t) - openNewtonCotes n f a b := by
  classical
  set h : ℝ := (b - a) / (n + 2) with hh
  have hpos : 0 < h := by rw [hh]; positivity
  have hnh : ((n : ℝ) + 2) * h = b - a := by rw [hh]; field_simp
  set x : ℕ → ℝ := fun k => a + ((k : ℝ) + 1) * h with hxdef
  set v : Fin (n + 1) → ℝ := fun i => x i with hvdef
  have hv : Function.Injective v := fun i j hij => Fin.ext (open_node_injective hab hij)
  have hxmem : ∀ k ≤ n, x k ∈ Icc a b := by
    intro k hk
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
    have h0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    refine ⟨by simp only [hxdef]; nlinarith, ?_⟩
    simp only [hxdef]
    have hle : ((k : ℝ) + 1) * h ≤ ((n : ℝ) + 2) * h := by nlinarith
    linarith
  set P : ℝ[X] := Lagrange.interpolate Finset.univ v fun i => f (v i) with hP
  set g₀ : ℝ → ℝ := fun t => f t - P.eval t with hg₀
  have hg₀node : ∀ k ≤ n, g₀ (x k) = 0 := by
    intro k hk
    have hxv : x k = v ⟨k, Nat.lt_succ_of_le hk⟩ := rfl
    simp only [hg₀, hxv, hP, Lagrange.eval_interpolate_at_node _ hv.injOn (Finset.mem_univ _),
      sub_self]
  -- the error is the integral of `f - Π_n f`
  have hE : (∫ t in a..b, f t) - openNewtonCotes n f a b = ∫ t in a..b, g₀ t := by
    have hNC : openNewtonCotes n f a b = ∫ t in a..b, P.eval t := by
      rw [openNewtonCotes_eq_sum_integral_basis hab]
      simp only [hP, Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C]
      rw [integral_finsetSum fun i _ =>
        ((Polynomial.continuous _).const_mul _).intervalIntegrable _ _]
      exact Finset.sum_congr rfl fun i _ => by rw [integral_const_mul]; ring
    rw [hNC, ← integral_sub ((hf.continuous).intervalIntegrable _ _)
      ((Polynomial.continuous _).intervalIntegrable _ _)]
  -- the divided difference `f[x_0, …, x_n, ·]`, smooth across the nodes as an iterated `dslope`
  let G : ℕ → ℝ → ℝ := fun k => Nat.rec g₀ (fun k Gk => dslope Gk (x k)) k
  have hGsucc : ∀ k, G (k + 1) = dslope (G k) (x k) := fun k => rfl
  have hGsmooth : ∀ k ≤ n + 1, ContDiff ℝ ((n + 2 - k : ℕ) : WithTop ℕ∞) (G k) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact hf.sub (contDiff_eval P _)
    | succ k ih =>
      intro hk
      have e : n + 2 - k = (n + 2 - (k + 1)) + 1 := by omega
      have hik := ih (by omega)
      rw [e] at hik
      rw [hGsucc]
      exact hik.dslope (x k)
  have hGeq : ∀ k ≤ n + 1, ∀ t, (∀ j < k, t ≠ x j) →
      G k t = g₀ t / ∏ j ∈ Finset.range k, (t - x j) := by
    intro k
    induction k with
    | zero => intro _ t _; change g₀ t = _; simp
    | succ k ih =>
      intro hk t ht
      have hGk0 : G k (x k) = 0 := by
        rw [ih (by omega) (x k) fun j hj hjk => absurd (open_node_injective hab hjk) (by omega)]
        rw [hg₀node k (by omega), zero_div]
      rw [hGsucc, dslope_of_ne _ (ht k (Nat.lt_succ_self k)), slope_def_field, hGk0, sub_zero,
        ih (by omega) t fun j hj => ht j (Nat.lt_succ_of_lt hj), Finset.prod_range_succ, div_div]
  set φ : ℝ → ℝ := G (n + 1) with hφ
  have hφC1 : ContDiff ℝ 1 φ := by
    have hs := hGsmooth (n + 1) le_rfl
    rwa [show n + 2 - (n + 1) = 1 by omega] at hs
  set D : ℝ → ℝ := deriv φ with hD
  have hφD : ∀ t, HasDerivAt φ (D t) t := fun t =>
    (hφC1.differentiable one_ne_zero t).hasDerivAt
  have hDc : Continuous D := hφC1.continuous_deriv le_rfl
  -- the nodal polynomial and its primitive `W`
  set ω : ℝ → ℝ := fun t => ∏ j ∈ Finset.range (n + 1), (t - x j) with hω
  have hωc : Continuous ω := by fun_prop
  have hφω : ∀ t, g₀ t = φ t * ω t := by
    intro t
    by_cases hnode : ∃ j < n + 1, t = x j
    · obtain ⟨j, hj, rfl⟩ := hnode
      rw [hg₀node j (by omega), hω]
      simp only
      rw [Finset.prod_eq_zero (Finset.mem_range.2 hj) (sub_self _), mul_zero]
    · push Not at hnode
      have hne : ω t ≠ 0 := by
        simp only [hω]
        exact Finset.prod_ne_zero_iff.2 fun j hj => sub_ne_zero.2 (hnode j (Finset.mem_range.1 hj))
      rw [hφ, hGeq (n + 1) le_rfl t hnode]
      simp only [hω] at hne ⊢
      rw [div_mul_cancel₀ _ hne]
  set W : ℝ → ℝ := fun t => ∫ s in a..t, ω s with hW
  have hWd : ∀ t, HasDerivAt W (ω t) t := fun t =>
    (hωc.integral_hasStrictDerivAt a t).hasDerivAt
  -- `W` is the scaled reference primitive `h^{n+2} ∫_{-1}^{(t - a - h)/h} π_{n+1}`
  have hωπ : ∀ s : ℝ, ω (h * s + (a + h)) = h ^ (n + 1) * (intNodal n).eval s := by
    intro s
    simp only [hω, hxdef, intNodal_eval_eq_prod_range]
    have e : ∀ j ∈ Finset.range (n + 1),
        h * s + (a + h) - (a + ((j : ℝ) + 1) * h) = h * (s - j) := fun j _ => by ring
    rw [Finset.prod_congr rfl e, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have hWval : ∀ t, W t
      = h ^ (n + 2) * ∫ s in (-1 : ℝ)..((t - a - h) / h), (intNodal n).eval s := by
    intro t
    have hcov := integral_comp_mul_add (fun s => ω s) (a := (-1 : ℝ)) (b := (t - a - h) / h)
      hpos.ne' (a + h)
    simp only [smul_eq_mul] at hcov
    rw [show h * (-1) + (a + h) = a by ring, mul_div_cancel₀ _ hpos.ne',
      show t - a - h + (a + h) = t by ring] at hcov
    have hI : (∫ s in (-1 : ℝ)..((t - a - h) / h), ω (h * s + (a + h)))
        = h ^ (n + 1) * ∫ s in (-1 : ℝ)..((t - a - h) / h), (intNodal n).eval s := by
      rw [← integral_const_mul]
      exact integral_congr fun s _ => hωπ s
    rw [hI] at hcov
    calc W t = h * (h⁻¹ * W t) := by field_simp
      _ = h * (h ^ (n + 1) * ∫ s in (-1 : ℝ)..((t - a - h) / h), (intNodal n).eval s) := by
          rw [← hcov]
      _ = _ := by ring
  have hWnp : ∀ t ∈ Icc a b, W t ≤ 0 := by
    intro t ht
    rw [hWval]
    have hsign := integral_intNodal_neg_one_mul_nonneg n ((t - a - h) / h) ?_ ?_
    · rw [hn.add_one.neg_one_pow, neg_one_mul, neg_nonneg] at hsign
      have hpow : (0 : ℝ) < h ^ (n + 2) := by positivity
      nlinarith
    · rw [le_div_iff₀ hpos]
      linarith [ht.1]
    · rw [div_le_iff₀ hpos]
      nlinarith [ht.2]
  have hWa : W a = 0 := by simp [hW]
  have hWb : W b = 0 := by
    have hba : (b - a - h) / h = (n : ℝ) + 1 := by
      field_simp
      linarith
    rw [hWval, hba, integral_intNodal_neg_one_eq_zero_of_even hn, mul_zero]
  -- integration by parts
  have hparts := integral_mul_deriv_eq_deriv_mul (a := a) (b := b) (u := φ) (u' := D) (v := W)
    (v' := ω) (fun t _ => hφD t) (fun t _ => hWd t) (hDc.intervalIntegrable _ _)
    (hωc.intervalIntegrable _ _)
  -- `φ' ≥ 0` away from the nodes: it is a Hermite coefficient, a value of `f^{(n+2)}/(n+2)!`
  have hDnn : ∀ t ∈ Ioo a b, t ∉ Set.range v → 0 ≤ D t := by
    intro t ht htv
    have hopen : IsOpen (Set.range v)ᶜ := (Set.finite_range v).isClosed.isOpen_compl
    have hφloc : φ =ᶠ[𝓝 t] fun y => DividedDifference.newton f (Fin.snoc v y) := by
      filter_upwards [hopen.mem_nhds htv] with y hy
      have hy' : Function.Injective (Fin.snoc v y : Fin (n + 2) → ℝ) :=
        Fin.snoc_injective_iff.2 ⟨hv, hy⟩
      rw [DividedDifference.eval_interpolate_snoc_sub f hy', hφ, hGeq (n + 1) le_rfl y
        fun j hj hyj => hy ⟨⟨j, hj⟩, hyj.symm⟩]
      congr 1
      exact (Fin.prod_univ_eq_prod_range (fun j => y - x j) (n + 1)).symm
    have hdiff : DifferentiableAt ℝ f t :=
      hf.differentiable (by exact_mod_cast Nat.succ_ne_zero (n + 1)) t
    have hnd := DividedDifference.hasDerivAt_newton_snoc hv htv hdiff
    have hDt : D t = (Hermite.interpolate (Fin.snoc v t) (Fin.snoc (fun _ => 0) 1) f).coeff
        (n + 2) := (hφD t).unique (hnd.congr_of_eventuallyEq hφloc)
    -- Rolle with multiplicities for `f - H`
    set w : Fin (n + 2) → ℝ := Fin.snoc v t with hw
    set μ : Fin (n + 2) → ℕ := Fin.snoc (fun _ => 0) 1 with hμ
    set H : ℝ[X] := Hermite.interpolate w μ f with hH
    have hwinj : Function.Injective w := Fin.snoc_injective_iff.2 ⟨hv, htv⟩
    have hwmem : ∀ i, w i ∈ Icc a b := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [hw, Fin.snoc_last]
        exact Ioo_subset_Icc_self ht
      · simp only [hw, Fin.snoc_castSucc]
        exact hxmem j (Nat.lt_succ_iff.1 j.2)
    have hμsum : ∑ i, (μ i + 1) = n + 1 + 2 := by
      rw [Fin.sum_univ_castSucc]
      simp [hμ, Fin.snoc_castSucc, Fin.snoc_last]
    have hHdeg : H.natDegree ≤ n + 2 := by
      have hd := Hermite.degree_interpolate_lt hwinj μ f
      rw [hμsum] at hd
      exact natDegree_le_of_degree_le (Order.le_of_lt_succ (by exact_mod_cast hd))
    set g : ℝ → ℝ := f - fun y => H.eval y with hg
    have hgC : ContDiff ℝ ((n + 1 + 1 : ℕ) : WithTop ℕ∞) g := hf.sub (contDiff_eval H _)
    have hzero : ∀ i, ∀ j ≤ μ i, iteratedDeriv j g (w i) = 0 := by
      intro i j hj
      have hj2 : j ≤ n + 2 := by
        have hle : μ i ≤ 1 := by
          refine Fin.lastCases ?_ (fun k => ?_) i <;> simp [hμ, Fin.snoc_last, Fin.snoc_castSucc]
        omega
      rw [hg, iteratedDeriv_sub (hf.contDiffAt.of_le (by exact_mod_cast hj2))
        (contDiff_eval H _).contDiffAt]
      simp only [Polynomial.iteratedDeriv_eval]
      rw [Hermite.eval_iterate_derivative_interpolate hwinj i hj, sub_self]
    obtain ⟨ξ, hξ, hξ0⟩ := Hermite.exists_iteratedDeriv_eq_zero (N := n + 1) hgC hwinj hwmem
      hμsum hzero
    rw [hg, iteratedDeriv_sub hf.contDiffAt (contDiff_eval H _).contDiffAt] at hξ0
    simp only [Polynomial.iteratedDeriv_eval,
      Polynomial.iterate_derivative_eq_C_of_natDegree_le hHdeg, eval_C] at hξ0
    rw [hDt]
    have hfac : (0 : ℝ) < (n + 2).factorial := by positivity
    have hfξ := hf' ξ
    exact (mul_nonneg_iff_of_pos_left hfac).1 (by linarith)
  -- hence `∫ φ' W ≤ 0`, and the error is `-∫ φ' W`
  have hint : (∫ t in a..b, D t * W t) ≤ 0 := by
    rw [← neg_nonneg, ← integral_neg]
    refine integral_nonneg_of_ae_restrict hab.le ?_
    have hfinset : ((({a, b} : Set ℝ) ∪ Set.range v)).Finite :=
      ((Set.finite_singleton b).insert a).union (Set.finite_range v)
    have hfin : ∀ᵐ t ∂volume, t ∉ (({a, b} : Set ℝ) ∪ Set.range v) :=
      hfinset.countable.ae_notMem volume
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc,
      MeasureTheory.ae_restrict_of_ae hfin] with t ht htv
    have hta : t ≠ a := fun he => htv (Or.inl (by simp [he]))
    have htb : t ≠ b := fun he => htv (Or.inl (by simp [he]))
    have htv' : t ∉ Set.range v := fun hr => htv (Or.inr hr)
    have hDt := hDnn t ⟨lt_of_le_of_ne ht.1 (Ne.symm hta), lt_of_le_of_ne ht.2 htb⟩ htv'
    have hWt := hWnp t ht
    change (0 : ℝ) ≤ -(D t * W t)
    nlinarith
  rw [hE, integral_congr fun t _ => hφω t, hparts, hWa, hWb]
  linarith

/-- The exactness of the open rule with even `n` to degree `n + 1`, in the summation form that
Peano's theorem takes as a hypothesis. -/
private theorem openNewtonCotes_exact_aux (hn : Even n) (hab : a < b) :
    ∀ p : ℝ[X], p.degree ≤ ((n + 1 : ℕ) : WithBot ℕ) →
      (∫ t in a..b, p.eval t) = ∑ i : Fin (n + 1),
        (b - a) / (n + 2) * openNewtonCotesWeight n i
          * p.eval (a + ((i : ℕ) + 1) * ((b - a) / (n + 2))) := by
  intro p hp
  rw [integral_eq_openNewtonCotes_of_even hn hab (by exact_mod_cast hp), openNewtonCotes,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Sign constancy of the Peano kernel of the open rule with even `n`** (Steffensen): with the
weights `h w_i`, the nodes `a + (i + 1) h`, `h = (b - a)/(n + 2)`, and the order `n + 1`,
`K_{n+1}(t) ≥ 0` on `[a, b]`.

If `K_{n+1}(t₀) < 0` at an interior point, then for a `C^{n+2}` integrand whose `(n+2)`-nd
derivative is a bump concentrated where `K_{n+1} < 0`, Peano's theorem gives a negative error,
while `sub_openNewtonCotes_nonneg_of_even` gives a nonnegative one. The endpoints follow by
continuity. -/
theorem peanoKernel_openNewtonCotes_nonneg_of_even (hn : Even n) (hab : a < b) {t : ℝ}
    (ht : t ∈ Icc a b) :
    0 ≤ peanoKernel a b (fun i : Fin (n + 1) => (b - a) / (n + 2) * openNewtonCotesWeight n i)
      (fun i : Fin (n + 1) => a + ((i : ℕ) + 1) * ((b - a) / (n + 2))) (n + 1) t := by
  set w' : Fin (n + 1) → ℝ := fun i => (b - a) / (n + 2) * openNewtonCotesWeight n i with hw'
  set z : Fin (n + 1) → ℝ := fun i => a + ((i : ℕ) + 1) * ((b - a) / (n + 2)) with hz
  set K : ℝ → ℝ := peanoKernel a b w' z (n + 1) with hK
  have hKc : ContinuousOn K (Icc a b) := continuousOn_peanoKernel w' z (by omega)
  have hzmem : ∀ i, z i ∈ Icc a b := fun i => openNewtonCotes_node_mem hab.le i
  have hexact := openNewtonCotes_exact_aux hn hab
  -- the interior
  have hIoo : ∀ t ∈ Ioo a b, 0 ≤ K t := by
    intro t ht
    by_contra hneg
    push Not at hneg
    have hcont : ContinuousAt K t := hKc.continuousAt (Icc_mem_nhds ht.1 ht.2)
    obtain ⟨r, hr, hball⟩ : ∃ r > 0, ∀ s, |s - t| < r → K s < 0 := by
      obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff.1 (hcont.eventually (gt_mem_nhds hneg))
      exact ⟨r, hr, fun s hs => h (by rwa [Real.dist_eq])⟩
    let ψ : ContDiffBump t := ⟨r / 2, r, by positivity, by linarith⟩
    obtain ⟨g, hg, hgψ⟩ := exists_contDiff_iteratedDeriv_eq (n + 2) ψ.continuous
    -- Peano's theorem for `g`
    have hF : ∀ k ≤ n + 1, ∀ s ∈ Icc a b,
        HasDerivAt (iteratedDeriv k g) (iteratedDeriv (k + 1) g s) s := by
      intro k hk s _
      have hd := hg.differentiable_iteratedDeriv k (by exact_mod_cast (by omega : k < n + 2))
      rw [iteratedDeriv_succ]
      exact (hd s).hasDerivAt
    have hc : ContinuousOn (iteratedDeriv (n + 1 + 1) g) (Icc a b) := by
      rw [hgψ]
      exact ψ.continuous.continuousOn
    have hpeano := error_eq_integral_peanoKernel (F := fun k => iteratedDeriv k g) (m := n + 1)
      hab.le hzmem hF hc hexact
    simp only [iteratedDeriv_zero, hgψ] at hpeano
    have hNC : ∑ i, w' i * g (z i) = openNewtonCotes n g a b := by
      rw [openNewtonCotes, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by simp only [hw', hz]; ring
    rw [hNC] at hpeano
    -- the kernel integral against the bump is negative
    have hprod : ∀ s ∈ Icc a b, 0 ≤ -(K s * ψ s) := by
      intro s _
      by_cases hs : |s - t| < r
      · exact neg_nonneg.2 (mul_nonpos_of_nonpos_of_nonneg (hball s hs).le ψ.nonneg)
      · rw [ψ.zero_of_le_dist (by rw [Real.dist_eq]; exact not_lt.1 hs), mul_zero, neg_zero]
    have hpos' : 0 < ∫ s in a..b, -(K s * ψ s) :=
      integral_pos_of_continuousOn_of_nonneg hab (hKc.mul ψ.continuous.continuousOn).neg hprod ht
        (neg_pos.2 (mul_neg_of_neg_of_pos hneg (ψ.pos_of_mem_ball (Metric.mem_ball_self hr))))
    rw [integral_neg] at hpos'
    -- but the error is nonnegative
    have hnn := sub_openNewtonCotes_nonneg_of_even hn hab hg fun s => by
      rw [hgψ]; exact ψ.nonneg
    rw [hpeano] at hnn
    linarith
  -- the endpoints, by continuity
  rcases eq_or_lt_of_le ht.1 with hta | hta
  · rw [← hta]
    have hlim : Tendsto K (𝓝[Ioo a b] a) (𝓝 (K a)) :=
      (hKc a (left_mem_Icc.2 hab.le)).mono_left (nhdsWithin_mono _ Ioo_subset_Icc_self)
    have := left_nhdsWithin_Ioo_neBot hab
    exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall hIoo)
  rcases eq_or_lt_of_le ht.2 with htb | htb
  · rw [htb]
    have hlim : Tendsto K (𝓝[Ioo a b] b) (𝓝 (K b)) :=
      (hKc b (right_mem_Icc.2 hab.le)).mono_left (nhdsWithin_mono _ Ioo_subset_Icc_self)
    have := right_nhdsWithin_Ioo_neBot hab
    exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall hIoo)
  exact hIoo t ⟨hta, htb⟩

/-- **The kernel integral is the error at one monomial**: for even `n`,
`∫_a^b K_{n+1} = M̃_n/(n + 2)! · h^{n+3}`, `h = (b - a)/(n + 2)`. Peano's theorem at
`x^{n+2}/(n+2)!` identifies `∫ K_{n+1}` with the error at that monomial; since the rule is exact
to degree `n + 1` and `x^{n+2} = ω_{n+1}(x)(x - b) + (\text{degree} ≤ n + 1)`, that error is
`∫_a^b ω_{n+1}(x)(x - b) dx`, which the substitution `x = a + (τ + 1) h` turns into
`h^{n+3} ∫_{-1}^{n+1} π_{n+1}(τ)(τ - (n + 1)) dτ`, and that is `M̃_n` because `π_{n+1}` integrates
to zero over `[-1, n + 1]` for even `n`.

Reference: [quarteroni2000numerical], the computation after (9.23), in the open case. -/
theorem integral_peanoKernel_openNewtonCotes_of_even (hn : Even n) (hab : a < b) :
    (∫ t in a..b, peanoKernel a b
        (fun i : Fin (n + 1) => (b - a) / (n + 2) * openNewtonCotesWeight n i)
        (fun i : Fin (n + 1) => a + ((i : ℕ) + 1) * ((b - a) / (n + 2))) (n + 1) t)
      = openNewtonCotesM n / (n + 2).factorial * ((b - a) / (n + 2)) ^ (n + 3) := by
  classical
  set h : ℝ := (b - a) / (n + 2) with hh
  have hpos : 0 < h := by rw [hh]; positivity
  have hnh : ((n : ℝ) + 2) * h = b - a := by rw [hh]; field_simp
  set w' : Fin (n + 1) → ℝ := fun i => h * openNewtonCotesWeight n i with hw'
  set z : Fin (n + 1) → ℝ := fun i => a + (((i : ℕ) : ℝ) + 1) * h with hz
  have hzmem : ∀ i, z i ∈ Icc a b := fun i => openNewtonCotes_node_mem hab.le i
  have hexact : ∀ p : ℝ[X], p.degree ≤ ((n + 1 : ℕ) : WithBot ℕ) →
      (∫ t in a..b, p.eval t) = ∑ i, w' i * p.eval (z i) :=
    openNewtonCotes_exact_aux hn hab
  -- Peano's theorem at `q = x^{n+2}/(n+2)!`
  set c : ℝ := ((n + 1 + 1).factorial : ℝ)⁻¹ with hc
  set q : ℝ[X] := C c * X ^ (n + 1 + 1) with hq
  have hqnat : q.natDegree ≤ n + 1 + 1 := natDegree_C_mul_X_pow_le c (n + 1 + 1)
  set F : ℕ → ℝ → ℝ := fun k t => (derivative^[k] q).eval t with hF
  have hFd : ∀ k ≤ n + 1, ∀ t ∈ Icc a b, HasDerivAt (F k) (F (k + 1) t) t := by
    intro k _ t _
    have := (derivative^[k] q).hasDerivAt t
    simpa only [hF, Function.iterate_succ_apply'] using this
  have hFtop : F (n + 1 + 1) = fun _ => 1 := by
    funext t
    change (derivative^[n + 1 + 1] q).eval t = 1
    rw [Polynomial.iterate_derivative_eq_C_of_natDegree_le hqnat, eval_C, hq, coeff_C_mul,
      coeff_X_pow]
    simp only [ite_true, mul_one, hc]
    field_simp
  have hpeano := error_eq_integral_peanoKernel (F := F) (m := n + 1) hab.le hzmem hFd
    (by rw [hFtop]; exact continuousOn_const) hexact
  rw [hFtop] at hpeano
  simp only [mul_one] at hpeano
  rw [← hpeano]
  -- the error at `x^{n+2}`
  set ω : ℝ[X] := ∏ i : Fin (n + 1), (X - C (z i)) with hω
  have hωmonic : ω.Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (z i)
  have hωnat : ω.natDegree = n + 1 := by
    rw [hω, natDegree_prod _ _ fun i _ => (monic_X_sub_C (z i)).ne_zero]
    simp
  have hωz : ∀ i, ω.eval (z i) = 0 := fun i => by
    rw [hω, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  set r : ℝ[X] := X ^ (n + 1 + 1) - ω * (X - C b) with hr
  have hrdeg : r.degree ≤ ((n + 1 : ℕ) : WithBot ℕ) := by
    have hmon : (ω * (X - C b)).Monic := hωmonic.mul (monic_X_sub_C b)
    have hdeg : (ω * (X - C b)).natDegree = n + 1 + 1 := by
      rw [natDegree_mul hωmonic.ne_zero (monic_X_sub_C b).ne_zero, hωnat, natDegree_X_sub_C]
    have h1 : (X ^ (n + 1 + 1) : ℝ[X]).degree = (ω * (X - C b)).degree := by
      rw [degree_X_pow, degree_eq_natDegree hmon.ne_zero, hdeg]
    have hlt := degree_sub_lt_left h1 (by simp) (by rw [leadingCoeff_X_pow, hmon.leadingCoeff])
    rw [degree_X_pow] at hlt
    exact Order.le_of_lt_succ (by exact_mod_cast hlt)
  have hsplit : ∀ t, F 0 t = c * (ω.eval t * (t - b) + r.eval t) := by
    intro t
    simp only [hF, Function.iterate_zero, id, hq, eval_mul, eval_C, eval_pow, eval_X, hr,
      eval_sub]
    ring
  have hrexact := hexact r hrdeg
  have hωint : IntervalIntegrable (fun t => ω.eval t * (t - b)) volume a b :=
    (by fun_prop : Continuous fun t => ω.eval t * (t - b)).intervalIntegrable _ _
  have hrint : IntervalIntegrable (fun t => r.eval t) volume a b :=
    (Polynomial.continuous _).intervalIntegrable _ _
  have hlhs : (∫ t in a..b, F 0 t) - ∑ i, w' i * F 0 (z i)
      = c * ∫ t in a..b, ω.eval t * (t - b) := by
    have h1 : (∫ t in a..b, F 0 t)
        = c * ((∫ t in a..b, ω.eval t * (t - b)) + ∫ t in a..b, r.eval t) := by
      rw [← integral_add hωint hrint, ← integral_const_mul]
      exact integral_congr fun t _ => hsplit t
    have h2 : ∑ i, w' i * F 0 (z i) = c * ∑ i, w' i * r.eval (z i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hsplit, hωz]; ring
    rw [h1, h2, ← hrexact]
    ring
  rw [hlhs]
  -- the substitution `x = a + (τ + 1) h`
  have hωπ : ∀ s : ℝ, ω.eval (h * s + (a + h)) = h ^ (n + 1) * (intNodal n).eval s := by
    intro s
    rw [hω, eval_prod, intNodal_eval]
    have e : ∀ i : Fin (n + 1), (X - C (z i)).eval (h * s + (a + h)) = h * (s - i) := fun i => by
      simp only [eval_sub, eval_X, eval_C, hz]; ring
    rw [Finset.prod_congr rfl fun i _ => e i, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  have hcov := integral_comp_mul_add (fun t => ω.eval t * (t - b)) (a := (-1 : ℝ))
    (b := (n : ℝ) + 1) hpos.ne' (a + h)
  simp only [smul_eq_mul] at hcov
  rw [show h * (-1) + (a + h) = a by ring, show h * ((n : ℝ) + 1) + (a + h) = b by linarith]
    at hcov
  have hI : (∫ s in (-1 : ℝ)..((n : ℝ) + 1), ω.eval (h * s + (a + h)) * (h * s + (a + h) - b))
      = h ^ (n + 2) * ∫ s in (-1 : ℝ)..((n : ℝ) + 1),
          (intNodal n).eval s * (s - ((n : ℝ) + 1)) := by
    rw [← integral_const_mul]
    refine integral_congr fun s _ => ?_
    rw [hωπ, show h * s + (a + h) - b = h * (s - ((n : ℝ) + 1)) by linarith]
    ring
  have hM : (∫ s in (-1 : ℝ)..((n : ℝ) + 1), (intNodal n).eval s * (s - ((n : ℝ) + 1)))
      = openNewtonCotesM n := by
    have hz0 := integral_intNodal_neg_one_eq_zero_of_even hn
    have hd : (∫ s in (-1 : ℝ)..((n : ℝ) + 1), (intNodal n).eval s * (s - ((n : ℝ) + 1)))
        = (∫ s in (-1 : ℝ)..((n : ℝ) + 1), s * (intNodal n).eval s)
          - ((n : ℝ) + 1) * ∫ s in (-1 : ℝ)..((n : ℝ) + 1), (intNodal n).eval s := by
      rw [← integral_const_mul, ← integral_sub
        ((by fun_prop : Continuous fun s : ℝ => s * (intNodal n).eval s).intervalIntegrable _ _)
        ((by fun_prop : Continuous fun s : ℝ =>
          ((n : ℝ) + 1) * (intNodal n).eval s).intervalIntegrable _ _)]
      exact integral_congr fun s _ => by ring
    rw [hd, hz0, mul_zero, sub_zero, openNewtonCotesM]
  rw [hI, hM] at hcov
  have hint : (∫ t in a..b, ω.eval t * (t - b)) = h ^ (n + 3) * openNewtonCotesM n := by
    calc (∫ t in a..b, ω.eval t * (t - b)) = h * (h⁻¹ * ∫ t in a..b, ω.eval t * (t - b)) := by
          field_simp
      _ = h * (h ^ (n + 2) * openNewtonCotesM n) := by rw [← hcov]
      _ = _ := by ring
  rw [hint, hc]
  ring

/-- **The error of the open Newton–Cotes rules with even `n`** ([quarteroni2000numerical]
Theorem 9.2, (9.19)): for even `n`, `a < b` and `f` of class `C^{n+2}` on an open set containing
`[a, b]`, `∫_a^b f - I_n(f) = M̃_n/(n + 2)! · h^{n+3} · f^{(n+2)}(ξ)` for some `ξ ∈ (a, b)`, with
`h = (b - a)/(n + 2)` and `M̃_n = ∫_{-1}^{n+1} t π_{n+1}(t) dt > 0`
(`Quadrature.openNewtonCotesM_pos`). For `n = 0` this is the midpoint error
`Quadrature.exists_sub_midpoint_eq`.

Peano's theorem at order `n + 1` (the rule is exact to degree `n + 1`), the sign constancy of the
kernel, its integral, and the weighted mean value theorem for integrals. -/
theorem exists_sub_openNewtonCotes_eq_of_even (hn : Even n) (hab : a < b) {U : Set ℝ}
    (hU : IsOpen U) (hUab : Icc a b ⊆ U)
    (hf : ContDiffOn ℝ ((n + 2 : ℕ) : WithTop ℕ∞) f U) :
    ∃ ξ ∈ Ioo a b, (∫ t in a..b, f t) - openNewtonCotes n f a b
      = openNewtonCotesM n / (n + 2).factorial * ((b - a) / (n + 2)) ^ (n + 3)
        * iteratedDeriv (n + 2) f ξ := by
  set w' : Fin (n + 1) → ℝ := fun i => (b - a) / (n + 2) * openNewtonCotesWeight n i with hw'
  set z : Fin (n + 1) → ℝ := fun i => a + ((i : ℕ) + 1) * ((b - a) / (n + 2)) with hz
  set K : ℝ → ℝ := peanoKernel a b w' z (n + 1) with hK
  have hzmem : ∀ i, z i ∈ Icc a b := fun i => openNewtonCotes_node_mem hab.le i
  have hF : ∀ k ≤ n + 1, ∀ t ∈ Icc a b,
      HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f t) t := fun k hk t ht =>
    hf.hasDerivAt_iteratedDeriv_of_isOpen hU (by omega) (hUab ht)
  have hc : ContinuousOn (iteratedDeriv (n + 1 + 1) f) (Icc a b) :=
    (hf.continuousOn_iteratedDeriv_of_isOpen hU le_rfl).mono hUab
  have hpeano := error_eq_integral_peanoKernel (F := fun k => iteratedDeriv k f) (m := n + 1)
    hab.le hzmem hF hc (openNewtonCotes_exact_aux hn hab)
  simp only [iteratedDeriv_zero] at hpeano
  have hNC : ∑ i, w' i * f (z i) = openNewtonCotes n f a b := by
    rw [openNewtonCotes, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp only [hw', hz]; ring
  rw [hNC] at hpeano
  have hKint := integral_peanoKernel_openNewtonCotes_of_even hn hab
  have hKpos : 0 < ∫ t in a..b, K t := by
    rw [hK, hKint]
    have hM := openNewtonCotesM_pos hn
    have hfac : (0 : ℝ) < (n + 2).factorial := by positivity
    have hpow : (0 : ℝ) < ((b - a) / ((n : ℝ) + 2)) ^ (n + 3) := by
      have : (0 : ℝ) < (b - a) / ((n : ℝ) + 2) := by
        have : (0 : ℝ) < b - a := by linarith
        positivity
      positivity
    exact mul_pos (div_pos hM hfac) hpow
  obtain ⟨ξ, hξ, hξval⟩ := exists_mem_Ioo_integral_mul_eq_mul_integral hab
    (continuousOn_peanoKernel w' z (by omega)) hc
    (fun t ht => peanoKernel_openNewtonCotes_nonneg_of_even hn hab ht) hKpos
  refine ⟨ξ, hξ, ?_⟩
  rw [hpeano, hξval, hKint]
  ring

end OpenError

/-! ### Composite rules -/

section Composite

variable {n : ℕ} {a b : ℝ} {f : ℝ → ℝ}

/-- The uniform mesh `x_j = a + j H`, `H = (b - a)/m`, lies in `[a, b]`. -/
private theorem mesh_mem (hab : a ≤ b) {m : ℕ} (hm : 0 < m) {j : ℕ} (hj : j ≤ m) :
    a + j * ((b - a) / m) ∈ Icc a b := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hj' : (j : ℝ) ≤ m := by exact_mod_cast hj
  have h0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hH : 0 ≤ (b - a) / m := by
    have : 0 ≤ b - a := by linarith
    positivity
  refine ⟨by nlinarith, ?_⟩
  have : (j : ℝ) * ((b - a) / m) ≤ m * ((b - a) / m) := mul_le_mul_of_nonneg_right hj' hH
  rw [mul_div_cancel₀ _ hmR.ne'] at this
  linarith

/-- **The composite Newton–Cotes error, even `n`** ([quarteroni2000numerical] Theorem 9.3,
(9.26), with the constant corrected). For even `n > 0`, `a < b`, `0 < m`, `H = (b - a)/m` and `f`
of class `C^{n+2}` on an open set containing `[a, b]`,
`∫_a^b f - I_{n,m}(f) = (b - a)/(n + 2)! · M_n/n^{n+3} · H^{n+2} · f^{(n+2)}(ξ)`
for some `ξ ∈ [a, b]`.

The book prints `M_n/(n + 2)^{n+3}`; the panel spacing of the closed rule is `h = H/n`, so the
panel errors are `M_n/(n + 2)! (H/n)^{n+3} f^{(n+2)}(ξ_j)`, and `n = 2` must return the composite
Simpson constant `-(b - a) H⁴/2880`. The `m` panel values are collected by the discrete mean
value theorem. -/
theorem exists_sub_compositeNewtonCotes_eq_of_even (hn : Even n) (hn0 : 0 < n) (hab : a < b)
    {m : ℕ} (hm : 0 < m) {U : Set ℝ} (hU : IsOpen U) (hUab : Icc a b ⊆ U)
    (hf : ContDiffOn ℝ ((n + 2 : ℕ) : WithTop ℕ∞) f U) :
    ∃ ξ ∈ Icc a b, (∫ t in a..b, f t) - compositeNewtonCotes n f a b m
      = (b - a) / (n + 2).factorial * (newtonCotesM n / (n : ℝ) ^ (n + 3))
        * ((b - a) / m) ^ (n + 2) * iteratedDeriv (n + 2) f ξ := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  set H : ℝ := (b - a) / m with hH
  have hHpos : 0 < H := by rw [hH]; positivity
  have hmH : (m : ℝ) * H = b - a := by rw [hH]; field_simp
  set x : ℕ → ℝ := fun j => a + j * H with hxdef
  have hx0 : x 0 = a := by simp [hxdef]
  have hxm : x m = b := by simp only [hxdef]; linarith
  have hxstep : ∀ j : ℕ, x (j + 1) - x j = H := by
    intro j; simp only [hxdef]; push_cast; ring
  have hxlt : ∀ j : ℕ, x j < x (j + 1) := fun j => by linarith [hxstep j, hHpos]
  have hxmem : ∀ j ≤ m, x j ∈ Icc a b := fun j hj => mesh_mem hab.le hm hj
  have hxsub : ∀ j < m, Icc (x j) (x (j + 1)) ⊆ Icc a b := fun j hj =>
    Icc_subset_Icc (hxmem j hj.le).1 (hxmem (j + 1) hj).2
  have hcont : ContinuousOn (iteratedDeriv (n + 2) f) (Icc a b) :=
    (hf.continuousOn_iteratedDeriv_of_isOpen hU le_rfl).mono hUab
  -- the panel errors
  set c : ℝ := newtonCotesM n / (n + 2).factorial * (H / n) ^ (n + 3) with hc
  have hpanel : ∀ j < m, ∃ ξ ∈ Icc (x j) (x (j + 1)),
      (∫ t in (x j)..(x (j + 1)), f t) - closedNewtonCotes n f (x j) (x (j + 1))
        = c * iteratedDeriv (n + 2) f ξ := by
    intro j hj
    obtain ⟨ξ, hξ, h⟩ := exists_sub_closedNewtonCotes_eq_of_even hn hn0 (hxlt j) hU
      ((hxsub j hj).trans hUab) hf
    exact ⟨ξ, Ioo_subset_Icc_self hξ, by rw [h, hxstep j]⟩
  choose! ξ hξmem hξeq using hpanel
  have hint : ∀ j < m, IntervalIntegrable f volume (x j) (x (j + 1)) := fun j hj =>
    ((hf.continuousOn.mono ((hxsub j hj).trans hUab)).mono
      (by rw [uIcc_of_le (hxlt j).le])).intervalIntegrable
  have hcomp : compositeNewtonCotes n f a b m
      = ∑ j ∈ Finset.range m, closedNewtonCotes n f (x j) (x (j + 1)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hxdef, hH]
    push_cast
    rfl
  have hsplit : (∫ t in a..b, f t) - compositeNewtonCotes n f a b m
      = ∑ j ∈ Finset.range m, c * iteratedDeriv (n + 2) f (ξ j) := by
    have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
    rw [hx0, hxm] at hsum
    rw [hcomp, ← hsum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j hj => hξeq j (Finset.mem_range.mp hj)
  obtain ⟨η, hη, hsum⟩ := exists_sum_mul_eq_of_forall_mem hab.le hcont
    (fun j hj => hxsub j hj (hξmem j hj)) c
  refine ⟨η, hη, ?_⟩
  have hn' : (n : ℝ) ≠ 0 := hnR.ne'
  rw [hsplit, hsum, hc, ← hmH, div_pow]
  field_simp
  ring

/-- **The Riemann-sum bound for composite Newton–Cotes rules with nonnegative weights**
([quarteroni2000numerical] Property 9.1, with the constant `1` in place of the book's `2`). For
`0 < n` with nonnegative weights `w_i`, `f` continuous on `[a, b]`, `0 < m`, `H = (b - a)/m` and
`ε` bounding the oscillation of `f` over distances at most `H`,
`|∫_a^b f - I_{n,m}(f)| ≤ (b - a) ε`. An instance of `Quadrature.abs_sub_compositeSum_le` with the
panel weights `w_i/n`. -/
theorem abs_sub_compositeNewtonCotes_le (hn : 0 < n) (hw : ∀ i, 0 ≤ newtonCotesWeight n i)
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) {m : ℕ} (hm : 0 < m) {ε : ℝ}
    (hosc : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, |u - v| ≤ (b - a) / m → |f u - f v| ≤ ε) :
    |(∫ t in a..b, f t) - compositeNewtonCotes n f a b m| ≤ (b - a) * ε := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  set H : ℝ := (b - a) / m with hH
  have hHnn : 0 ≤ H := by
    have : 0 ≤ b - a := by linarith
    rw [hH]; positivity
  have hmH : (m : ℝ) * H = b - a := by rw [hH]; field_simp
  have hbound := abs_sub_compositeSum_le (g := f) (N := m) (t := fun j => a + j * H) hf
    (by simp) (by linarith) (fun j _ => by push_cast; nlinarith)
    (fun j _ => by push_cast; rw [hH]; ring_nf; exact le_rfl) (h := H)
    (ω := fun i : Fin (n + 1) => newtonCotesWeight n i / n) (fun i => div_nonneg (hw i) hnR.le)
    (by rw [← Finset.sum_div, sum_newtonCotesWeight, div_self hnR.ne'])
    (y := fun j i => a + j * H + i * (H / n)) (fun j _ i => ?_) hosc
  · convert hbound using 3
    rw [compositeNewtonCotes]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [closedNewtonCotes, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 : a + ((j : ℝ) + 1) * ((b - a) / m) - (a + j * ((b - a) / m)) = H := by
      rw [hH]; ring
    have e2 : a + j * H + i * (H / n) = a + j * ((b - a) / m) + i * (H / n) := by rw [hH]
    rw [e1, e2]
    push_cast
    ring_nf
  · have hi : (i : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp i.2
    have h0 : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _
    have hHn : 0 ≤ H / n := by positivity
    refine ⟨by nlinarith, ?_⟩
    have : (i : ℝ) * (H / n) ≤ n * (H / n) := mul_le_mul_of_nonneg_right hi hHn
    rw [mul_div_cancel₀ _ hnR.ne'] at this
    push_cast
    linarith

/-- **Convergence of the composite Newton–Cotes rules with nonnegative weights**
([quarteroni2000numerical] Property 9.1): for `0 < n`, `w_i ≥ 0`, `a ≤ b` and `f` continuous on
`[a, b]`, `I_{n,m}(f) → ∫_a^b f` as `m → ∞`. An instance of `Quadrature.tendsto_uniformMesh`. -/
theorem tendsto_compositeNewtonCotes (hn : 0 < n) (hw : ∀ i, 0 ≤ newtonCotesWeight n i)
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    Tendsto (fun m => compositeNewtonCotes n f a b m) atTop (𝓝 (∫ t in a..b, f t)) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  have hlim : Tendsto (fun m : ℕ => (b - a) / ((m : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (b - a)
  have h := tendsto_uniformMesh (g := f) (N := fun m => m + 1)
    (hs := fun m : ℕ => (b - a) / ((m : ℝ) + 1))
    (ω := fun i : Fin (n + 1) => newtonCotesWeight n i / n)
    (c := fun i : Fin (n + 1) => (i : ℝ) / n) hab hf (fun m => Nat.succ_pos m)
    (fun m => by push_cast; rfl) hlim (fun i => div_nonneg (hw i) hnR.le)
    (by rw [← Finset.sum_div, sum_newtonCotesWeight, div_self hnR.ne'])
    (fun i => ⟨by positivity, by
      rw [div_le_one hnR]
      exact_mod_cast Nat.lt_succ_iff.mp i.2⟩)
  refine h.congr fun m => ?_
  rw [compositeNewtonCotes]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [closedNewtonCotes, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  have e : a + ((j : ℝ) + 1) * ((b - a) / ((m : ℝ) + 1)) - (a + j * ((b - a) / ((m : ℝ) + 1)))
      = (b - a) / ((m : ℝ) + 1) := by ring
  rw [e]
  ring_nf

/-- **The `O(H^{n+1})` error bound of the composite closed rules**, for every `n ≥ 1` and every
integrand of class `C^{n+1}`, with no sign hypothesis on the weights: with `H = (b - a)/m` and
`|f^{(n+1)}| ≤ M` on `[a, b]`,

  `|∫_a^b f - I_{n,m}(f)| ≤ (b - a)/n · M/(n + 1)! · (H/n)^{n+1} · ∫_0^n |π_{n+1}|`.

The `m` panel errors are bounded by `Quadrature.abs_sub_closedNewtonCotes_le_of_contDiffOn` and
added. Unlike `Quadrature.abs_sub_compositeNewtonCotes_le`, this needs no nonnegativity of the
weights — which fails from `n = 8` on — but asks for a smooth integrand. -/
theorem abs_sub_compositeNewtonCotes_le_of_contDiffOn (hn : 0 < n) (hab : a < b) {m : ℕ}
    (hm : 0 < m) {U : Set ℝ} (hU : IsOpen U) (hUab : Icc a b ⊆ U)
    (hf : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f U) {M : ℝ}
    (hM : ∀ t ∈ Icc a b, |iteratedDeriv (n + 1) f t| ≤ M) :
    |(∫ t in a..b, f t) - compositeNewtonCotes n f a b m|
      ≤ (b - a) / n * (M / (n + 1).factorial) * ((b - a) / m / n) ^ (n + 1)
        * ∫ s in (0 : ℝ)..(n : ℝ), |(intNodal n).eval s| := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  set H : ℝ := (b - a) / m with hH
  have hHpos : 0 < H := by rw [hH]; positivity
  have hmH : (m : ℝ) * H = b - a := by rw [hH]; field_simp
  set C : ℝ := ∫ s in (0 : ℝ)..(n : ℝ), |(intNodal n).eval s| with hC
  set x : ℕ → ℝ := fun j => a + j * H with hxdef
  have hx0 : x 0 = a := by simp [hxdef]
  have hxm : x m = b := by simp only [hxdef]; linarith
  have hxstep : ∀ j : ℕ, x (j + 1) - x j = H := by
    intro j; simp only [hxdef]; push_cast; ring
  have hxlt : ∀ j : ℕ, x j < x (j + 1) := fun j => by linarith [hxstep j, hHpos]
  have hxmem : ∀ j ≤ m, x j ∈ Icc a b := by
    intro j hj
    have hj' : (j : ℝ) ≤ m := by exact_mod_cast hj
    have h0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    refine ⟨by simp only [hxdef]; nlinarith, ?_⟩
    simp only [hxdef]
    nlinarith
  have hxsub : ∀ j < m, Icc (x j) (x (j + 1)) ⊆ Icc a b := fun j hj =>
    Icc_subset_Icc (hxmem j hj.le).1 (hxmem (j + 1) hj).2
  -- the panel bound
  set c : ℝ := M / (n + 1).factorial * (H / n) ^ (n + 2) * C with hc
  have hpanel : ∀ j < m,
      |(∫ t in (x j)..(x (j + 1)), f t) - closedNewtonCotes n f (x j) (x (j + 1))| ≤ c := by
    intro j hj
    have h := abs_sub_closedNewtonCotes_le_of_contDiffOn hn (hxlt j) hU
      ((hxsub j hj).trans hUab) hf (M := M) fun t ht => hM t (hxsub j hj ht)
    rw [hxstep j] at h
    rw [hc]
    calc _ ≤ M / (n + 1).factorial * (H / n) ^ (n + 2) * C := h
      _ = _ := rfl
  have hint : ∀ j < m, IntervalIntegrable f volume (x j) (x (j + 1)) := fun j hj =>
    ((hf.continuousOn.mono ((hxsub j hj).trans hUab)).mono
      (by rw [uIcc_of_le (hxlt j).le])).intervalIntegrable
  have hcomp : compositeNewtonCotes n f a b m
      = ∑ j ∈ Finset.range m, closedNewtonCotes n f (x j) (x (j + 1)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hxdef, hH]
    push_cast
    rfl
  have hsplit : (∫ t in a..b, f t) - compositeNewtonCotes n f a b m
      = ∑ j ∈ Finset.range m,
        ((∫ t in (x j)..(x (j + 1)), f t) - closedNewtonCotes n f (x j) (x (j + 1))) := by
    have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
    rw [hx0, hxm] at hsum
    rw [hcomp, ← hsum, ← Finset.sum_sub_distrib]
  rw [hsplit]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun j hj => hpanel j (Finset.mem_range.mp hj)) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hc]
  have hpow : (H / n) ^ (n + 2) = H / n * (H / n) ^ (n + 1) := by ring
  rw [hpow]
  have hmul : (m : ℝ) * (M / (n + 1).factorial * (H / n * (H / n) ^ (n + 1)) * C)
      = ((m : ℝ) * H) / n * (M / (n + 1).factorial) * (H / n) ^ (n + 1) * C := by
    field_simp
  rw [hmul, hmH, hH]

/-- **Convergence of the composite closed rules for a smooth integrand**: for `0 < n`, `a < b` and
`f` of class `C^{n+1}` on an open set containing `[a, b]`, `I_{n,m}(f) → ∫_a^b f` as `m → ∞`.

The bound of `Quadrature.abs_sub_compositeNewtonCotes_le_of_contDiffOn` is `O(m^{-(n+1)})`. This
complements `Quadrature.tendsto_compositeNewtonCotes`, which asks only for continuity of `f` but
needs nonnegative weights. -/
theorem tendsto_compositeNewtonCotes_of_contDiffOn (hn : 0 < n) (hab : a < b) {U : Set ℝ}
    (hU : IsOpen U) (hUab : Icc a b ⊆ U)
    (hf : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f U) :
    Tendsto (fun m => compositeNewtonCotes n f a b m) atTop (𝓝 (∫ t in a..b, f t)) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    ((hf.continuousOn_iteratedDeriv_of_isOpen hU le_rfl).mono hUab)
  set C : ℝ := ∫ s in (0 : ℝ)..(n : ℝ), |(intNodal n).eval s| with hC
  set A : ℝ := (b - a) / n * (M / (n + 1).factorial) * ((b - a) / n) ^ (n + 1) * C with hA
  have hbound : ∀ m : ℕ, 0 < m →
      ‖compositeNewtonCotes n f a b m - ∫ t in a..b, f t‖ ≤ A * (1 / (m : ℝ)) ^ (n + 1) := by
    intro m hm
    have h := abs_sub_compositeNewtonCotes_le_of_contDiffOn hn hab hm hU hUab hf
      (M := M) fun t ht => by simpa [Real.norm_eq_abs] using hM t ht
    rw [Real.norm_eq_abs, abs_sub_comm]
    refine le_trans h (le_of_eq ?_)
    rw [hA, ← hC]
    rw [show (b - a) / (m : ℝ) / n = ((b - a) / n) * (1 / (m : ℝ)) by ring, mul_pow]
    ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun m => norm_nonneg _)
    (eventually_atTop.2 ⟨1, fun m hm => hbound m hm⟩) ?_
  have hlim : Tendsto (fun m : ℕ => (1 / (m : ℝ)) ^ (n + 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => (1 : ℝ) / (m : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have h2 := h1.pow (n + 1)
    rwa [zero_pow (Nat.succ_ne_zero n)] at h2
  simpa using hlim.const_mul A

end Composite

/-! ### Hermite quadrature and the corrected trapezoidal rule -/

section Hermite

variable {n : ℕ} {a b : ℝ}

/-- **The Hermite cardinal polynomials `𝓛_k`** of the nodes `x`:
`𝓛_k = (1 - (ω''(x_k)/ω'(x_k)) (X - x_k)) l_k²`, with `l_k` the Lagrange basis polynomial and `ω`
the nodal polynomial. They take the value `1` at `x_k`, `0` at the other nodes, and have vanishing
derivative at every node.

Reference: [quarteroni2000numerical], (9.28). -/
noncomputable def hermiteBasisL (x : Fin (n + 1) → ℝ) (k : Fin (n + 1)) : ℝ[X] :=
  (1 - C ((derivative (derivative (Lagrange.nodal Finset.univ x))).eval (x k)
      / (derivative (Lagrange.nodal Finset.univ x)).eval (x k)) * (X - C (x k)))
    * Lagrange.basis Finset.univ x k ^ 2

/-- **The Hermite cardinal polynomials `𝓜_k`** of the nodes `x`: `𝓜_k = (X - x_k) l_k²`. They
vanish at every node, and their derivative is `1` at `x_k` and `0` at the other nodes.

Reference: [quarteroni2000numerical], (9.28). -/
noncomputable def hermiteBasisM (x : Fin (n + 1) → ℝ) (k : Fin (n + 1)) : ℝ[X] :=
  (X - C (x k)) * Lagrange.basis Finset.univ x k ^ 2

/-- The derivative of the Lagrange basis polynomial at its own node is `ω''(x_k)/(2 ω'(x_k))`:
with `ω = (X - x_k) ω_k` and `l_k = ω_k/ω_k(x_k)`, one has `ω'(x_k) = ω_k(x_k)` and
`ω''(x_k) = 2 ω_k'(x_k)`. -/
theorem _root_.Lagrange.eval_derivative_basis_self {x : Fin (n + 1) → ℝ}
    (hx : Function.Injective x) (k : Fin (n + 1)) :
    (derivative (Lagrange.basis Finset.univ x k)).eval (x k)
      = (derivative (derivative (Lagrange.nodal Finset.univ x))).eval (x k)
        / (2 * (derivative (Lagrange.nodal Finset.univ x)).eval (x k)) := by
  classical
  set ωk : ℝ[X] := Lagrange.nodal (Finset.univ.erase k) x with hωk
  have hbasis : Lagrange.basis Finset.univ x k = C (Lagrange.nodalWeight Finset.univ x k) * ωk := by
    rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div (Finset.mem_univ k),
      ← Lagrange.nodal_erase_eq_nodal_div (Finset.mem_univ k)]
  have hnodal : Lagrange.nodal Finset.univ x = (X - C (x k)) * ωk :=
    Lagrange.nodal_eq_mul_nodal_erase (Finset.mem_univ k)
  have hW : Lagrange.nodalWeight Finset.univ x k = (ωk.eval (x k))⁻¹ :=
    Lagrange.nodalWeight_eq_eval_nodal_erase_inv
  have hωk0 : ωk.eval (x k) ≠ 0 := by
    rw [hωk, Lagrange.eval_nodal]
    exact Finset.prod_ne_zero_iff.2 fun j hj =>
      sub_ne_zero.2 fun h => (Finset.mem_erase.1 hj).1 (hx h).symm
  have hd1 : derivative (Lagrange.nodal Finset.univ x) = ωk + (X - C (x k)) * derivative ωk := by
    rw [hnodal, derivative_mul, derivative_X_sub_C, one_mul]
  have hd2 : derivative (derivative (Lagrange.nodal Finset.univ x))
      = 2 * derivative ωk + (X - C (x k)) * derivative (derivative ωk) := by
    rw [hd1, derivative_add, derivative_mul, derivative_X_sub_C, one_mul]
    ring
  rw [hbasis, derivative_mul, derivative_C, zero_mul, zero_add, eval_mul, eval_C, hW, hd2, hd1]
  simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, eval_ofNat, sub_self, zero_mul,
    add_zero]
  field_simp

/-- **`𝓛_k` at the nodes**: `𝓛_k(x_j) = δ_{jk}`. -/
theorem hermiteBasisL_eval_node {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (k j : Fin (n + 1)) : (hermiteBasisL x k).eval (x j) = if j = k then 1 else 0 := by
  simp only [hermiteBasisL, eval_mul, eval_sub, eval_one, eval_C, eval_X, eval_pow]
  split_ifs with h
  · rw [h, Lagrange.eval_basis_self hx.injOn (Finset.mem_univ k), sub_self, mul_zero, sub_zero,
      one_pow, mul_one]
  · rw [Lagrange.eval_basis_of_ne (Ne.symm h) (Finset.mem_univ j)]
    ring

/-- **`𝓛_k'` at the nodes**: `𝓛_k'(x_j) = 0`. -/
theorem eval_derivative_hermiteBasisL {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (k j : Fin (n + 1)) : (derivative (hermiteBasisL x k)).eval (x j) = 0 := by
  have hnodal_ne : (derivative (Lagrange.nodal Finset.univ x)).eval (x k) ≠ 0 := by
    rw [Lagrange.eval_nodal_derivative_eval_node_eq (Finset.mem_univ k), Lagrange.eval_nodal]
    exact Finset.prod_ne_zero_iff.2 fun j hj =>
      sub_ne_zero.2 fun h => (Finset.mem_erase.1 hj).1 (hx h).symm
  simp only [hermiteBasisL, derivative_mul, derivative_sub, derivative_one, derivative_C,
    derivative_X, derivative_pow, eval_add, eval_mul, eval_sub, eval_one, eval_C, eval_X,
    eval_pow, eval_neg, eval_zero, zero_mul, zero_sub, mul_one, sub_zero, neg_mul]
  by_cases h : j = k
  · rw [h, Lagrange.eval_basis_self hx.injOn (Finset.mem_univ k),
      Lagrange.eval_derivative_basis_self hx k, sub_self, mul_zero, sub_zero]
    field_simp
    ring
  · rw [Lagrange.eval_basis_of_ne (Ne.symm h) (Finset.mem_univ j)]
    ring

/-- **`𝓜_k` at the nodes**: `𝓜_k(x_j) = 0`. -/
theorem hermiteBasisM_eval_node (x : Fin (n + 1) → ℝ) (k j : Fin (n + 1)) :
    (hermiteBasisM x k).eval (x j) = 0 := by
  simp only [hermiteBasisM, eval_mul, eval_sub, eval_X, eval_C, eval_pow]
  by_cases h : j = k
  · rw [h, sub_self, zero_mul]
  · rw [Lagrange.eval_basis_of_ne (Ne.symm h) (Finset.mem_univ j)]
    ring

/-- **`𝓜_k'` at the nodes**: `𝓜_k'(x_j) = δ_{jk}`. -/
theorem eval_derivative_hermiteBasisM {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (k j : Fin (n + 1)) : (derivative (hermiteBasisM x k)).eval (x j) = if j = k then 1 else 0 := by
  simp only [hermiteBasisM, derivative_mul, derivative_X_sub_C, one_mul, derivative_pow,
    eval_add, eval_mul, eval_sub, eval_X, eval_C, eval_pow]
  split_ifs with h
  · rw [h, Lagrange.eval_basis_self hx.injOn (Finset.mem_univ k), sub_self, zero_mul]
    ring
  · rw [Lagrange.eval_basis_of_ne (Ne.symm h) (Finset.mem_univ j)]
    ring

/-- The Hermite cardinal polynomials have degree at most `2n + 1`. -/
theorem natDegree_hermiteBasisL_le {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (k : Fin (n + 1)) : (hermiteBasisL x k).natDegree ≤ 2 * n + 1 := by
  have hb : (Lagrange.basis Finset.univ x k ^ 2).natDegree ≤ 2 * n := by
    rw [natDegree_pow, Lagrange.natDegree_basis hx.injOn (Finset.mem_univ k)]
    simp
  have hl : (1 - C ((derivative (derivative (Lagrange.nodal Finset.univ x))).eval (x k)
      / (derivative (Lagrange.nodal Finset.univ x)).eval (x k)) * (X - C (x k))).natDegree ≤ 1 := by
    refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
    exact (natDegree_C_mul_le _ _).trans (natDegree_X_sub_C_le _)
  exact (natDegree_mul_le).trans (by omega)

/-- The Hermite cardinal polynomials have degree at most `2n + 1`. -/
theorem natDegree_hermiteBasisM_le {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (k : Fin (n + 1)) : (hermiteBasisM x k).natDegree ≤ 2 * n + 1 := by
  have hb : (Lagrange.basis Finset.univ x k ^ 2).natDegree ≤ 2 * n := by
    rw [natDegree_pow, Lagrange.natDegree_basis hx.injOn (Finset.mem_univ k)]
    simp
  exact (natDegree_mul_le).trans (by linarith [natDegree_X_sub_C_le (x k)])

/-- **The Hermite quadrature rule** at the nodes `x`,
`∑_k α_k f(x_k) + ∑_k β_k f'(x_k)` with `α_k = ∫_a^b 𝓛_k` and `β_k = ∫_a^b 𝓜_k`: the integral of
the Hermite interpolant of `f` at the nodes.

Reference: [quarteroni2000numerical], (9.29). -/
noncomputable def hermiteQuadrature (x : Fin (n + 1) → ℝ) (a b : ℝ) (f f' : ℝ → ℝ) : ℝ :=
  ∑ k, (∫ t in a..b, (hermiteBasisL x k).eval t) * f (x k)
    + ∑ k, (∫ t in a..b, (hermiteBasisM x k).eval t) * f' (x k)

/-- **A polynomial of degree at most `2n + 1` is its own Hermite interpolant**:
`p = ∑ p(x_k) 𝓛_k + ∑ p'(x_k) 𝓜_k`. Both sides have degree at most `2n + 1` and agree with
multiplicity two at every node, so both are the Hermite interpolant of `p`. -/
theorem eq_sum_hermiteBasis_of_degree_le {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    {p : ℝ[X]} (hp : p.degree ≤ (2 * n + 1 : ℕ)) :
    p = ∑ k, C (p.eval (x k)) * hermiteBasisL x k
      + ∑ k, C ((derivative p).eval (x k)) * hermiteBasisM x k := by
  have hsum : ∑ i : Fin (n + 1), ((fun _ => 1 : Fin (n + 1) → ℕ) i + 1) = 2 * n + 2 := by
    simp; ring
  have hdeg : ∀ q : ℝ[X], q.degree ≤ (2 * n + 1 : ℕ) →
      q.degree < ((∑ i : Fin (n + 1), ((fun _ => 1 : Fin (n + 1) → ℕ) i + 1) : ℕ) : WithBot ℕ) := by
    intro q hq
    rw [hsum]
    exact lt_of_le_of_lt hq (by exact_mod_cast (by omega : 2 * n + 1 < 2 * n + 2))
  set q : ℝ[X] := ∑ k, C (p.eval (x k)) * hermiteBasisL x k
      + ∑ k, C ((derivative p).eval (x k)) * hermiteBasisM x k with hq
  have hqdeg : q.degree ≤ (2 * n + 1 : ℕ) := by
    refine degree_le_of_natDegree_le ?_
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
      exact (natDegree_C_mul_le _ _).trans (natDegree_hermiteBasisL_le hx k)
    · refine natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
      exact (natDegree_C_mul_le _ _).trans (natDegree_hermiteBasisM_le hx k)
  -- both `p` and `q` are the Hermite interpolant of `p`
  have hp' := Hermite.eq_interpolate hx (m := fun _ => 1) (f := fun t => p.eval t) (hdeg p hp)
    fun i j hj => by rw [Polynomial.iteratedDeriv_eval]
  have hq' := Hermite.eq_interpolate hx (m := fun _ => 1) (f := fun t => p.eval t) (hdeg q hqdeg)
    fun i j hj => by
      rw [Polynomial.iteratedDeriv_eval]
      simp only
      interval_cases j
      · simp only [Function.iterate_zero, id, hq, eval_add, eval_finsetSum, eval_mul, eval_C,
          hermiteBasisL_eval_node hx, hermiteBasisM_eval_node, mul_zero, Finset.sum_const_zero,
          add_zero, mul_ite, mul_one, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      · simp only [Function.iterate_one, hq, derivative_add, derivative_sum, derivative_mul,
          derivative_C, zero_mul, zero_add, eval_add, eval_finsetSum, eval_mul, eval_C,
          eval_derivative_hermiteBasisL hx, eval_derivative_hermiteBasisM hx, mul_zero,
          Finset.sum_const_zero, mul_ite, mul_one, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [hp', hq']

/-- **Hermite quadrature has degree of exactness `2n + 1`** ([quarteroni2000numerical] §9.5):
for distinct nodes and a polynomial `p` of degree at most `2n + 1`,
`∫_a^b p = hermiteQuadrature x a b p p'`. -/
theorem integral_eq_hermiteQuadrature_of_degree_le {x : Fin (n + 1) → ℝ}
    (hx : Function.Injective x) (a b : ℝ) {p : ℝ[X]} (hp : p.degree ≤ (2 * n + 1 : ℕ)) :
    (∫ t in a..b, p.eval t)
      = hermiteQuadrature x a b (fun t => p.eval t) (fun t => (derivative p).eval t) := by
  have hrep := eq_sum_hermiteBasis_of_degree_le hx hp
  conv_lhs => rw [hrep]
  simp only [eval_add, eval_finsetSum, eval_mul, eval_C]
  rw [integral_add
    ((by fun_prop : Continuous fun t => ∑ k, p.eval (x k) * (hermiteBasisL x k).eval t)
      |>.intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t => ∑ k, (derivative p).eval (x k) * (hermiteBasisM x k).eval t)
      |>.intervalIntegrable _ _),
    integral_finsetSum fun k _ => ((Polynomial.continuous _).const_mul _).intervalIntegrable _ _,
    integral_finsetSum fun k _ => ((Polynomial.continuous _).const_mul _).intervalIntegrable _ _,
    hermiteQuadrature]
  simp only [integral_const_mul]
  congr 1 <;> exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- **The corrected trapezoidal rule**
`(b - a)/2 (f(a) + f(b)) + (b - a)²/12 (f'(a) - f'(b))`: the Hermite rule at the two nodes `a, b`.

Reference: [quarteroni2000numerical], (9.30). -/
noncomputable def correctedTrapezoid (f f' : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (b - a) / 2 * (f a + f b) + (b - a) ^ 2 / 12 * (f' a - f' b)

/-- **The composite corrected trapezoidal rule** on `m` panels of width `H = (b - a)/m`:
the composite trapezoidal sum plus the end correction `H²/12 (f'(a) - f'(b))`; the corrections at
the interior nodes cancel (`correctedTrapezoidSum_eq_sum`).

Reference: [quarteroni2000numerical], (9.32) (whose printed `(b - a)²/12` should read `H²/12`,
as in the book's Program 75). -/
noncomputable def correctedTrapezoidSum (f f' : ℝ → ℝ) (a b : ℝ) (m : ℕ) : ℝ :=
  trapezoidSum f a ((b - a) / m) m + ((b - a) / m) ^ 2 / 12 * (f' a - f' b)

/-- **The Hermite rule at the two nodes `a, b` is the corrected trapezoidal rule**: its weights are
`α_0 = α_1 = (b - a)/2`, `β_0 = -β_1 = (b - a)²/12`. They are read off the moment equations of
the rule, which is exact to degree `3`, at the polynomials `(x - a)^k`, `k ≤ 3`. -/
theorem hermiteQuadrature_two_eq_correctedTrapezoid (hab : a ≠ b) (f f' : ℝ → ℝ) :
    hermiteQuadrature ![a, b] a b f f' = correctedTrapezoid f f' a b := by
  have hinj : Function.Injective ![a, b] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [hab.symm]
  have hrule : ∀ g g' : ℝ → ℝ, hermiteQuadrature ![a, b] a b g g'
      = (∫ t in a..b, (hermiteBasisL ![a, b] 0).eval t) * g a
        + (∫ t in a..b, (hermiteBasisL ![a, b] 1).eval t) * g b
        + (∫ t in a..b, (hermiteBasisM ![a, b] 0).eval t) * g' a
        + (∫ t in a..b, (hermiteBasisM ![a, b] 1).eval t) * g' b := by
    intro g g'
    simp only [hermiteQuadrature, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
      Fin.succ_zero_eq_one, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  set A : ℝ := ∫ t in a..b, (hermiteBasisL ![a, b] 0).eval t with hA
  set B : ℝ := ∫ t in a..b, (hermiteBasisL ![a, b] 1).eval t with hB
  set C' : ℝ := ∫ t in a..b, (hermiteBasisM ![a, b] 0).eval t with hC
  set D : ℝ := ∫ t in a..b, (hermiteBasisM ![a, b] 1).eval t with hD
  set h : ℝ := b - a with hh
  have hne : h ≠ 0 := sub_ne_zero.2 hab.symm
  -- the moment equations at `(x - a)^k`, `1 ≤ k ≤ 3`
  have hmom : ∀ k : ℕ, 1 ≤ k → k ≤ 3 → h ^ (k + 1) / (k + 1)
      = B * h ^ k + C' * (if k = 1 then 1 else 0) + D * (k * h ^ (k - 1)) := by
    intro k hk1 hk
    have hdeg : ((X - C a) ^ k : ℝ[X]).degree ≤ (2 * 1 + 1 : ℕ) := by
      refine degree_le_of_natDegree_le ?_
      rw [natDegree_pow, natDegree_X_sub_C, mul_one]
      omega
    have h1 := integral_eq_hermiteQuadrature_of_degree_le hinj a b hdeg
    rw [hrule] at h1
    simp only [eval_pow, eval_sub, eval_X, eval_C, derivative_pow, derivative_X_sub_C, mul_one,
      eval_mul, sub_self] at h1
    rw [integral_comp_sub_right (fun t => t ^ k), sub_self, integral_pow, zero_pow
      (Nat.succ_ne_zero k), sub_zero, ← hh, zero_pow (by omega : k ≠ 0), mul_zero, zero_add]
      at h1
    rw [h1]
    congr 2
    rcases eq_or_ne k 1 with rfl | hk1'
    · simp
    · simp only [hk1', ite_false]
      rw [zero_pow (by omega : k - 1 ≠ 0), mul_zero]
  have E1 := hmom 1 le_rfl (by norm_num)
  have E2 := hmom 2 (by norm_num) (by norm_num)
  have E3 := hmom 3 (by norm_num) (by norm_num)
  norm_num at E1 E2 E3
  -- the exactness at `1` gives `A + B = h`
  have hA' : A + B = h := by
    have h1 := integral_eq_hermiteQuadrature_of_degree_le hinj a b (p := 1)
      (by rw [degree_one]; exact_mod_cast Nat.zero_le _)
    rw [hrule] at h1
    simp only [eval_one, derivative_one, eval_zero, mul_one, mul_zero, add_zero,
      integral_const, smul_eq_mul] at h1
    linarith
  have hD' : D = -h ^ 2 / 12 := by
    have : h ^ 2 * D = h ^ 2 * (-h ^ 2 / 12) := by linear_combination -E3 + h * E2
    exact mul_left_cancel₀ (pow_ne_zero 2 hne) this
  have hB' : B = h / 2 := by
    have : h ^ 2 * B = h ^ 2 * (h / 2) := by
      rw [hD'] at E2
      linear_combination -E2
    exact mul_left_cancel₀ (pow_ne_zero 2 hne) this
  have hC' : C' = h ^ 2 / 12 := by
    rw [hB', hD'] at E1
    linarith
  have hA'' : A = h / 2 := by rw [hB'] at hA'; linarith
  rw [hrule, hA'', hB', hC', hD', correctedTrapezoid, hh]
  ring

/-- **The corrected trapezoidal error** ([quarteroni2000numerical] (9.31)): for `a ≤ b` and `g`
of class `C⁴` on `[a, b]` (a chain of derivatives `g', g'', g₃, g₄`, the last continuous),
`∫_a^b g - correctedTrapezoid g g' a b = (b - a)⁵/720 · g⁗(ξ)` for some `ξ ∈ [a, b]`.

`Quadrature.integral_peanoKernel_mul_eq` writes the trapezoidal error as
`-((b - a)²/12)(g'(b) - g'(a)) + ∫ (t - a)²(t - b)² g⁗(t)/24 dt`, so the corrected trapezoidal
error is the last integral; its kernel is nonnegative and integrates to `(b - a)⁵/720`. -/
theorem exists_sub_correctedTrapezoid_eq (hab : a ≤ b) {g g' g'' g₃ g₄ : ℝ → ℝ}
    (hg : ∀ x ∈ Icc a b, HasDerivAt g (g' x) x) (hg' : ∀ x ∈ Icc a b, HasDerivAt g' (g'' x) x)
    (hg'' : ∀ x ∈ Icc a b, HasDerivAt g'' (g₃ x) x)
    (hg₃ : ∀ x ∈ Icc a b, HasDerivAt g₃ (g₄ x) x) (hc₄ : ContinuousOn g₄ (Icc a b)) :
    ∃ ξ ∈ Icc a b,
      (∫ t in a..b, g t) - correctedTrapezoid g g' a b = (b - a) ^ 5 / 720 * g₄ ξ := by
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hcg'' : ContinuousOn g'' (Icc a b) := fun x hx =>
    (hg'' x hx).continuousAt.continuousWithinAt
  have hpe := sub_trapezoid_eq_integral_peanoKernel (g := g) (g' := g') (g'' := g'')
    (by rw [huIcc]; exact hg) (by rw [huIcc]; exact hg') (hcg''.intervalIntegrable_of_Icc hab)
  have hem := integral_peanoKernel_mul_eq (α := a) (β := b) (g' := g') (g'' := g'') (g₃ := g₃)
    (g₄ := g₄) (by rw [huIcc]; exact hg') (by rw [huIcc]; exact hg'') (by rw [huIcc]; exact hg₃)
    (hc₄.intervalIntegrable_of_Icc hab)
  obtain ⟨ξ, hξ, hξval⟩ := exists_integral_mul_eq_mul_integral hab
    (by fun_prop : Continuous fun t => (t - a) ^ 2 * (t - b) ^ 2 / 24).continuousOn hc₄
    fun t _ => by positivity
  refine ⟨ξ, hξ, ?_⟩
  rw [correctedTrapezoid]
  rw [integral_peanoKernel_sq] at hξval
  linarith

/-- The uniform mesh points `a + j H`, `H = (b - a)/m`, `j ≤ m`, lie in `[a, b]`. -/
private theorem mesh_mem' (hab : a ≤ b) {m : ℕ} (hm : 0 < m) {j : ℕ} (hj : j ≤ m) :
    a + j * ((b - a) / m) ∈ Icc a b := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hj' : (j : ℝ) ≤ m := by exact_mod_cast hj
  have h0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hH : 0 ≤ (b - a) / m := by
    have : 0 ≤ b - a := by linarith
    positivity
  refine ⟨by nlinarith, ?_⟩
  have : (j : ℝ) * ((b - a) / m) ≤ m * ((b - a) / m) := mul_le_mul_of_nonneg_right hj' hH
  rw [mul_div_cancel₀ _ hmR.ne'] at this
  linarith

/-- **The composite corrected trapezoidal rule is the sum of the panel rules**: the derivative
corrections at the interior nodes telescope away.

Reference: [quarteroni2000numerical], the remark after (9.32). -/
theorem correctedTrapezoidSum_eq_sum (f f' : ℝ → ℝ) (a b : ℝ) (m : ℕ) :
    correctedTrapezoidSum f f' a b m
      = ∑ j ∈ Finset.range m,
          correctedTrapezoid f f' (a + j * ((b - a) / m)) (a + (j + 1) * ((b - a) / m)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [correctedTrapezoidSum, trapezoidSum]
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  set H : ℝ := (b - a) / m with hH
  have hb : a + (m : ℝ) * H = b := by rw [hH, mul_div_cancel₀ _ hmR.ne']; ring
  have hstep : ∀ j : ℕ, a + ((j : ℝ) + 1) * H - (a + j * H) = H := fun j => by ring
  have htel : ∑ j ∈ Finset.range m, (f' (a + j * H) - f' (a + (j + 1) * H)) = f' a - f' b := by
    have := Finset.sum_range_sub' (fun j : ℕ => f' (a + j * H)) m
    simp only [Nat.cast_zero, zero_mul, add_zero, Nat.cast_succ] at this
    rw [this, hb]
  simp only [correctedTrapezoid, hstep]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum (Finset.range m) _ (H ^ 2 / 12), htel,
    correctedTrapezoidSum, trapezoidSum]

/-- **The composite corrected trapezoidal error in mean value form**: for `a < b`, `0 < m`,
`H = (b - a)/m` and `g` of class `C⁴` on `[a, b]`,
`∫_a^b g - correctedTrapezoidSum g g' a b m = (b - a) H⁴/720 · g⁗(ξ)` for some `ξ ∈ [a, b]` —
the order `4` behaviour observed in [quarteroni2000numerical] Example 9.5. -/
theorem sub_correctedTrapezoidSum_eq (hab : a < b) {m : ℕ} (hm : 0 < m) {g g' g'' g₃ g₄ : ℝ → ℝ}
    (hg : ∀ x ∈ Icc a b, HasDerivAt g (g' x) x) (hg' : ∀ x ∈ Icc a b, HasDerivAt g' (g'' x) x)
    (hg'' : ∀ x ∈ Icc a b, HasDerivAt g'' (g₃ x) x)
    (hg₃ : ∀ x ∈ Icc a b, HasDerivAt g₃ (g₄ x) x) (hc₄ : ContinuousOn g₄ (Icc a b)) :
    ∃ ξ ∈ Icc a b, (∫ t in a..b, g t) - correctedTrapezoidSum g g' a b m
      = (b - a) * ((b - a) / m) ^ 4 / 720 * g₄ ξ := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  set H : ℝ := (b - a) / m with hH
  have hHpos : 0 < H := by rw [hH]; positivity
  have hmH : (m : ℝ) * H = b - a := by rw [hH]; field_simp
  set x : ℕ → ℝ := fun j => a + j * H with hxdef
  have hx0 : x 0 = a := by simp [hxdef]
  have hxm : x m = b := by simp only [hxdef]; linarith
  have hxstep : ∀ j : ℕ, x (j + 1) - x j = H := by
    intro j; simp only [hxdef]; push_cast; ring
  have hxle : ∀ j : ℕ, x j ≤ x (j + 1) := fun j => by linarith [hxstep j, hHpos]
  have hxmem : ∀ j ≤ m, x j ∈ Icc a b := fun j hj => mesh_mem' hab.le hm hj
  have hxsub : ∀ j < m, Icc (x j) (x (j + 1)) ⊆ Icc a b := fun j hj =>
    Icc_subset_Icc (hxmem j hj.le).1 (hxmem (j + 1) hj).2
  have hpanel : ∀ j < m, ∃ ξ ∈ Icc (x j) (x (j + 1)),
      (∫ t in (x j)..(x (j + 1)), g t) - correctedTrapezoid g g' (x j) (x (j + 1))
        = H ^ 5 / 720 * g₄ ξ := by
    intro j hj
    obtain ⟨ξ, hξ, h⟩ := exists_sub_correctedTrapezoid_eq (hxle j)
      (fun y hy => hg y (hxsub j hj hy)) (fun y hy => hg' y (hxsub j hj hy))
      (fun y hy => hg'' y (hxsub j hj hy)) (fun y hy => hg₃ y (hxsub j hj hy))
      (hc₄.mono (hxsub j hj))
    exact ⟨ξ, hξ, by rw [h, hxstep j]⟩
  choose! ξ hξmem hξeq using hpanel
  have hint : ∀ j < m, IntervalIntegrable g volume (x j) (x (j + 1)) := by
    intro j hj
    refine ContinuousOn.intervalIntegrable fun y hy => ?_
    exact (hg y (hxsub j hj (by rwa [uIcc_of_le (hxle j)] at hy))).continuousAt
      |>.continuousWithinAt
  have hcomp : correctedTrapezoidSum g g' a b m
      = ∑ j ∈ Finset.range m, correctedTrapezoid g g' (x j) (x (j + 1)) := by
    rw [correctedTrapezoidSum_eq_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hxdef, hH]
    push_cast
    rfl
  have hsplit : (∫ t in a..b, g t) - correctedTrapezoidSum g g' a b m
      = ∑ j ∈ Finset.range m, H ^ 5 / 720 * g₄ (ξ j) := by
    have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
    rw [hx0, hxm] at hsum
    rw [hcomp, ← hsum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j hj => hξeq j (Finset.mem_range.mp hj)
  obtain ⟨η, hη, hsum⟩ := exists_sum_mul_eq_of_forall_mem hab.le hc₄
    (fun j hj => hxsub j hj (hξmem j hj)) (H ^ 5 / 720)
  refine ⟨η, hη, ?_⟩
  rw [hsplit, hsum, ← hmH]
  ring

end Hermite

/-! ### The a posteriori estimate of adaptive Simpson quadrature -/

section Adaptive

variable {α β : ℝ} {g g' g'' g₃ g₄ : ℝ → ℝ}

/-- **The adaptive Simpson error estimator, made rigorous** ([quarteroni2000numerical]
(9.42)–(9.44)). For `α < β`, `h₀ = (β - α)/2`, `g` of class `C⁴` on `[α, β]` with
`|g⁗(u) - g⁗(v)| ≤ ω` for all `u, v ∈ [α, β]`, the one-panel Simpson value `S` and the two-panel
value `S₂` satisfy `|(∫_α^β g - S₂) + (S - S₂)/15| ≤ h₀⁵ ω/1350`.

From the two mean value formulae `∫ g - S = -(2h₀)⁵/2880 · g⁗(ξ)` and
`∫ g - S₂ = -(2h₀)⁵/(16 · 2880) · g⁗(ξ₂)`, the combination is `(2h₀)⁵ (g⁗(ξ) - g⁗(ξ₂))/43200`.
The book's `|I - S₂| ≃ |S - S₂|/15` is this with `ω` neglected; note the sign,
`I - S₂ ≈ -(S - S₂)/15`. -/
theorem abs_sub_simpson_add_estimate_le (hαβ : α < β)
    (hg : ∀ x ∈ Icc α β, HasDerivAt g (g' x) x) (hg' : ∀ x ∈ Icc α β, HasDerivAt g' (g'' x) x)
    (hg'' : ∀ x ∈ Icc α β, HasDerivAt g'' (g₃ x) x)
    (hg₃ : ∀ x ∈ Icc α β, HasDerivAt g₃ (g₄ x) x) (hc₄ : ContinuousOn g₄ (Icc α β)) {ω : ℝ}
    (hω : ∀ u ∈ Icc α β, ∀ v ∈ Icc α β, |g₄ u - g₄ v| ≤ ω) :
    |((∫ t in α..β, g t) - simpsonSum g α ((β - α) / 2) 2)
        + (simpsonSum g α (β - α) 1 - simpsonSum g α ((β - α) / 2) 2) / 15|
      ≤ ((β - α) / 2) ^ 5 / 1350 * ω := by
  obtain ⟨ξ, hξ, h1⟩ := sub_composite_simpson_eq hαβ one_pos (by simp : β - α = (β - α) / (1 : ℕ))
    hg hg' hg'' hg₃ hc₄
  obtain ⟨ξ₂, hξ₂, h2⟩ := sub_composite_simpson_eq hαβ two_pos
    (by push_cast; rfl : (β - α) / 2 = (β - α) / (2 : ℕ)) hg hg' hg'' hg₃ hc₄
  have hcomb : ((∫ t in α..β, g t) - simpsonSum g α ((β - α) / 2) 2)
      + (simpsonSum g α (β - α) 1 - simpsonSum g α ((β - α) / 2) 2) / 15
      = ((β - α) / 2) ^ 5 / 1350 * (g₄ ξ - g₄ ξ₂) := by
    have e : simpsonSum g α (β - α) 1 - simpsonSum g α ((β - α) / 2) 2
        = ((∫ t in α..β, g t) - simpsonSum g α ((β - α) / 2) 2)
          - ((∫ t in α..β, g t) - simpsonSum g α (β - α) 1) := by ring
    rw [e, h1, h2]
    ring
  rw [hcomb, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((β - α) / 2) ^ 5 / 1350)]
  exact mul_le_mul_of_nonneg_left (hω ξ hξ ξ₂ hξ₂) (by positivity)

end Adaptive

end Quadrature
