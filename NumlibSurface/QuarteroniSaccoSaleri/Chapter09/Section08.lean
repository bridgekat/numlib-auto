import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Numlib.Approximation.OrthogonalPolynomial.Classical
import Numlib.Approximation.SingularIntegral
import NumlibSurface.QuarteroniSaccoSaleri.Chapter09.Section04
import NumlibSurface.QuarteroniSaccoSaleri.Chapter09.Section07

/-!
# Quarteroni–Sacco–Saleri §9.8: singular integrals

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §9.8.

Three kinds of singular integral. A *finite jump* at a known interior point `c` (§9.8.1) is
handled by (9.46), `∫_a^b f = ∫_a^c f + ∫_c^b f`, and any of the formulae of the previous sections
applied to the two pieces. An *integrable endpoint singularity* (§9.8.2), `f(x) = φ(x)/(x - a)^μ`
with `0 ≤ μ < 1` and `|φ| ≤ M`, obeys the a priori bound `|I(f)| ≤ M (b - a)^{1-μ}/(1 - μ)` and is
approximated in two ways: Method 1 truncates the singular piece `I_1 = ∫_a^{a+ε} f` to the closed
form of its Taylor expansion (9.47)–(9.48) and applies a composite Newton–Cotes rule to the
remaining `I_2 = ∫_{a+ε}^b f` (9.49); Method 2 subtracts the Taylor polynomial `Φ_p` once and for
all, integrating `Φ_p/(x - a)^μ` exactly (9.51) and leaving the regularized integrand (9.52).
Example 9.10 evaluates the Fresnel integral `∫_0^{π/2} cos x/√x` by integrating its Taylor series
term by term. Finally (§9.8.3) an *unbounded interval*: (9.53)–(9.54) define the improper
integral, the decay criterion `x^{1+ρ} f(x) → 0` makes a continuous `f` integrable, Method 2 is
the substitution `x = 1/t` (9.55), and Method 3 is Gauss–Laguerre and Gauss–Hermite quadrature.

The backbone is `Numlib/Approximation/SingularIntegral` (the whole of §9.8.2–9.8.3, in the
namespace `Quadrature`), `Numlib/Approximation/NewtonCotes` through §9.4's `theorem_9_3_even`, and
the Laguerre and Hermite weights of `Numlib/Approximation/OrthogonalPolynomial/Classical` with
`Quadrature.exists_gauss`.

## Main results

* `equation_9_46` — the additivity (9.46), together with the interval integrability of a function
  continuous and bounded on `[a, c)` and on `(c, b]`.
* `singularIntegral_bound` — the a priori bound of §9.8.2.
* `equation_9_47`, `equation_9_48` — Taylor's formula with the Lagrange remainder, and the
  truncation error of Method 1: the closed form of the truncated sum, and the bound on `|E_1|`.
* `equation_9_49` — the a priori bound on `|E_2|`, Theorem 9.3 on `[a + ε, b]`.
* `example_9_10` — the Fresnel series.
* `equation_9_51`, `equation_9_52` — Method 2: the exact singular part, and the regularized
  integrand `g(x) = (x - a)^{p+1-μ} φ^{(p+1)}(ξ(x))/(p + 1)!`.
* `equation_9_53`, `equation_9_54` — the improper integral as a limit, and its splitting at an
  arbitrary `c`.
* `integrable_of_tendsto_rpow_mul` — the decay criterion.
* `equation_9_55` — the substitution `x = 1/t`.
* `gaussLaguerre`, `gaussHermite` — Method 3.

## Not formalized

The sentence after (9.52) — that the regularized integrand `g`, extended by `0` at `a`, is of
class `C^p` on `[a, b]`, which is what makes the composite Newton–Cotes error formula applicable
to it when `p ≥ n + 2` (`n` even) or `p ≥ n + 1` (`n` odd) — rests on the open backbone node
`Quadrature.contDiffOn_taylorRemainder_div_rpow`; its own node `equation_9_52_regularity` is open
in the plan. Examples 9.11 and 9.12 are numerical runs and are not formalized.

## Conventions

As in §9.2–9.4: `f ∈ C^k([a, b])` is `ContDiffOn ℝ (k : ℕ) f U` for an open `U ⊇ Icc a b`, so that
the derivatives `iteratedDeriv k f` are the two-sided ones. The Taylor polynomial `Φ_p` of (9.47)
is written as the explicit sum `∑_{k ≤ p} φ^{(k)}(a)(x - a)^k/k!`; the backbone knows it as
`taylorWithinEval φ p Set.univ a` (`Quadrature.taylorWithinEval_univ_eq_sum`). The exponent `μ` of
the singularity is a real number and `(x - a)^μ` is `Real.rpow`. Erratum: (9.55) prints
`I_2 = ∫_0^{1/c} f(t) t^{-2} dt`, which should read `f(1/t)`.
-/

open MeasureTheory Real Set Filter Topology

namespace QuarteroniSaccoSaleri.Chapter09

variable {a b c ε ρ μ : ℝ} {f φ : ℝ → ℝ} {U : Set ℝ} {n p m : ℕ}

/-! ### §9.8.1 Functions with finite jump discontinuities -/

/-- **(9.46).** Let `c` be a known point of `[a, b]` and let `f` be continuous and bounded on
`[a, c)` and on `(c, b]`, with a finite jump `f(c⁺) - f(c⁻)` at `c`. Then `f` is interval
integrable on `[a, c]` and on `[c, b]` and

`I(f) = ∫_a^b f(x) dx = ∫_a^c f(x) dx + ∫_c^b f(x) dx`,

so any integration formula of the previous sections can be used on `[a, c⁻]` and on `[c⁺, b]` to
furnish an approximation of `I(f)`. -/
theorem equation_9_46 (hac : a ≤ c) (hcb : c ≤ b) {M : ℝ} (hf₁ : ContinuousOn f (Ico a c))
    (hf₂ : ContinuousOn f (Ioc c b)) (hM : ∀ x ∈ Icc a b, ‖f x‖ ≤ M) :
    IntervalIntegrable f volume a c ∧ IntervalIntegrable f volume c b ∧
      ∫ x in a..b, f x = (∫ x in a..c, f x) + ∫ x in c..b, f x := by
  have h₁ : IntervalIntegrable f volume a c := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hac,
      ← integrableOn_congr_set_ae Ioo_ae_eq_Ioc]
    refine IntegrableOn.of_bound measure_Ioo_lt_top
      ((hf₁.mono Ioo_subset_Ico_self).aestronglyMeasurable measurableSet_Ioo) M ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hM x ⟨hx.1.le, hx.2.le.trans hcb⟩
  have h₂ : IntervalIntegrable f volume c b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hcb]
    refine IntegrableOn.of_bound measure_Ioc_lt_top
      (hf₂.aestronglyMeasurable measurableSet_Ioc) M ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hM x ⟨hac.trans hx.1.le, hx.2⟩
  exact ⟨h₁, h₂, (intervalIntegral.integral_add_adjacent_intervals h₁ h₂).symm⟩

/-! ### §9.8.2 Integrals of infinite functions: the a priori bound -/

/-- **The a priori bound of §9.8.2.** For `f(x) = φ(x)/(x - a)^μ` with `0 ≤ μ < 1` and `φ`
continuous on `(a, b]` with `|φ| ≤ M` there, `f` is integrable on `[a, b]` and

`|I(f)| ≤ M lim_{t → a⁺} ∫_t^b (x - a)^{-μ} dx = M (b - a)^{1-μ}/(1 - μ)`. -/
theorem singularIntegral_bound (hab : a < b) (hμ0 : 0 ≤ μ) (hμ1 : μ < 1)
    (hφ : ContinuousOn φ (Ioc a b)) {M : ℝ} (hM : ∀ x ∈ Ioc a b, |φ x| ≤ M) :
    IntervalIntegrable (fun x => φ x / (x - a) ^ μ) volume a b ∧
      |∫ x in a..b, φ x / (x - a) ^ μ| ≤ M * (b - a) ^ (1 - μ) / (1 - μ) :=
  ⟨Quadrature.intervalIntegrable_div_rpow hab hμ0 hμ1
      (hφ.aestronglyMeasurable measurableSet_Ioc) hM,
    Quadrature.abs_integral_div_rpow_le hab hμ1 hM⟩

/-! ### The Taylor expansion (9.47) and its exact contribution -/

/-- **(9.47), Taylor's formula with the Lagrange remainder.** For `φ` of class `C^{p+1}` on an
open set containing `[a, b]` and `x ∈ (a, b]`,

`φ(x) = Φ_p(x) + (x - a)^{p+1}/(p + 1)! φ^{(p+1)}(ξ(x))`, `ξ(x) ∈ (a, x)`,

with `Φ_p(x) = ∑_{k=0}^p φ^{(k)}(a)(x - a)^k/k!`. -/
theorem equation_9_47 (hU : IsOpen U) (hUab : Icc a b ⊆ U)
    (hφ : ContDiffOn ℝ ((p + 1 : ℕ) : WithTop ℕ∞) φ U) {x : ℝ} (hx : x ∈ Ioc a b) :
    ∃ ξ ∈ Ioo a x, φ x = (∑ k ∈ Finset.range (p + 1),
        iteratedDeriv k φ a * (x - a) ^ k / (Nat.factorial k : ℝ))
      + (x - a) ^ (p + 1) / (Nat.factorial (p + 1) : ℝ) * iteratedDeriv (p + 1) φ ξ := by
  have hsub : uIcc a x ⊆ U := by
    rw [uIcc_of_le hx.1.le]
    exact (Icc_subset_Icc_right hx.2).trans hUab
  obtain ⟨ξ, hξ, h⟩ := Quadrature.exists_sub_taylorWithinEval_univ_eq hx.1.ne hU hsub hφ
  rw [uIoo_of_le hx.1.le] at hξ
  rw [Quadrature.taylorWithinEval_univ_eq_sum] at h
  exact ⟨ξ, hξ, by linear_combination h⟩

/-- The Taylor polynomial `Φ_p` of `φ` at `a`, divided by the weight, integrates in closed form:

`∫_a^b Φ_p(x)/(x - a)^μ dx = (b - a)^{1-μ} ∑_{k=0}^p (b - a)^k φ^{(k)}(a)/(k!(k + 1 - μ))`.

The backbone's `Quadrature.integral_sum_mul_pow_div_rpow` with `c_k = φ^{(k)}(a)/k!`; it is the
truncated sum of Method 1 at `b = a + ε`, and the exact part (9.51) of Method 2. -/
theorem integral_taylorSum_div_rpow (hab : a ≤ b) (hμ1 : μ < 1) (φ : ℝ → ℝ) (p : ℕ) :
    (∫ x in a..b, (∑ k ∈ Finset.range (p + 1),
        iteratedDeriv k φ a * (x - a) ^ k / (Nat.factorial k : ℝ)) / (x - a) ^ μ)
      = (b - a) ^ (1 - μ) * ∑ k ∈ Finset.range (p + 1),
          (b - a) ^ k * iteratedDeriv k φ a / ((Nat.factorial k : ℝ) * ((k : ℝ) + 1 - μ)) := by
  have e : ∀ x : ℝ, (∑ k ∈ Finset.range (p + 1),
      iteratedDeriv k φ a * (x - a) ^ k / (Nat.factorial k : ℝ))
      = ∑ k ∈ Finset.range (p + 1),
        iteratedDeriv k φ a / (Nat.factorial k : ℝ) * (x - a) ^ k :=
    fun x => Finset.sum_congr rfl fun k _ => by ring
  simp_rw [e]
  rw [Quadrature.integral_sum_mul_pow_div_rpow hab hμ1
    (fun k => iteratedDeriv k φ a / (Nat.factorial k : ℝ)) p]
  exact congrArg _ (Finset.sum_congr rfl fun k _ => by rw [mul_div_assoc', div_div])

/-! ### Method 1: truncation (9.48)–(9.49) -/

/-- **(9.48), the truncation error of Method 1.** Write `I(f) = I_1 + I_2` with
`I_1 = ∫_a^{a+ε} φ(x)/(x - a)^μ dx`. Replacing `φ` by its `p`-th order Taylor expansion (9.47)
around `a` gives the closed form

`∫_a^{a+ε} Φ_p(x)/(x - a)^μ dx = ε^{1-μ} ∑_{k=0}^p ε^k φ^{(k)}(a)/(k!(k + 1 - μ))`,

and replacing `I_1` by that finite sum makes an error bounded by

`|E_1| ≤ ε^{p+2-μ}/((p + 1)!(p + 2 - μ)) max_{a ≤ x ≤ a+ε} |φ^{(p+1)}(x)|`. -/
theorem equation_9_48 (hε : 0 < ε) (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) (hU : IsOpen U)
    (hUab : Icc a (a + ε) ⊆ U) (hφ : ContDiffOn ℝ ((p + 1 : ℕ) : WithTop ℕ∞) φ U) {M : ℝ}
    (hM : ∀ x ∈ Icc a (a + ε), |iteratedDeriv (p + 1) φ x| ≤ M) :
    (∫ x in a..(a + ε), (∑ k ∈ Finset.range (p + 1),
          iteratedDeriv k φ a * (x - a) ^ k / (Nat.factorial k : ℝ)) / (x - a) ^ μ)
        = ε ^ (1 - μ) * ∑ k ∈ Finset.range (p + 1),
            ε ^ k * iteratedDeriv k φ a / ((Nat.factorial k : ℝ) * ((k : ℝ) + 1 - μ)) ∧
      |(∫ x in a..(a + ε), φ x / (x - a) ^ μ) - ε ^ (1 - μ) * ∑ k ∈ Finset.range (p + 1),
            ε ^ k * iteratedDeriv k φ a / ((Nat.factorial k : ℝ) * ((k : ℝ) + 1 - μ))|
        ≤ ε ^ ((p : ℝ) + 2 - μ) / ((Nat.factorial (p + 1) : ℝ) * ((p : ℝ) + 2 - μ)) * M := by
  have hle : a ≤ a + ε := by linarith
  have hclosed := integral_taylorSum_div_rpow (a := a) (b := a + ε) hle hμ1 φ p
  rw [add_sub_cancel_left] at hclosed
  refine ⟨hclosed, ?_⟩
  set S : ℝ → ℝ := fun x => ∑ k ∈ Finset.range (p + 1),
    iteratedDeriv k φ a * (x - a) ^ k / (Nat.factorial k : ℝ) with hSdef
  have hScont : Continuous S := by
    refine continuous_finsetSum _ fun k _ => ?_
    fun_prop
  have hφc : ContinuousOn φ (Icc a (a + ε)) := hφ.continuousOn.mono hUab
  obtain ⟨Mφ, hMφ⟩ := isCompact_Icc.exists_bound_of_continuousOn hφc
  obtain ⟨MS, hMS⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := S) (s := Icc a (a + ε)) hScont.continuousOn
  have hint₁ : IntervalIntegrable (fun x => φ x / (x - a) ^ μ) volume a (a + ε) :=
    Quadrature.intervalIntegrable_div_rpow (by linarith) hμ0 hμ1
      ((hφc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
      fun x hx => by simpa [Real.norm_eq_abs] using hMφ x (Ioc_subset_Icc_self hx)
  have hint₂ : IntervalIntegrable (fun x => S x / (x - a) ^ μ) volume a (a + ε) :=
    Quadrature.intervalIntegrable_div_rpow (by linarith) hμ0 hμ1
      (hScont.continuousOn.aestronglyMeasurable measurableSet_Ioc)
      fun x hx => by simpa [Real.norm_eq_abs] using hMS x (Ioc_subset_Icc_self hx)
  have hbound := Quadrature.abs_integral_taylorRemainder_div_rpow_le hε hμ1 hU hUab hφ hM
  have hS : ∀ x, taylorWithinEval φ p univ a x = S x := fun x =>
    Quadrature.taylorWithinEval_univ_eq_sum φ p a x
  simp_rw [hS] at hbound
  have hsplit : (∫ x in a..(a + ε), (φ x - S x) / (x - a) ^ μ)
      = (∫ x in a..(a + ε), φ x / (x - a) ^ μ) - ∫ x in a..(a + ε), S x / (x - a) ^ μ := by
    simp_rw [sub_div]
    exact intervalIntegral.integral_sub hint₁ hint₂
  rwa [hsplit, hclosed] at hbound

-- TODO(backbone): belongs beside `Quadrature.intervalIntegrable_div_rpow` in
-- `Numlib/Approximation/SingularIntegral`.
/-- `φ(x)/(x - a)^μ` is as smooth as `φ` away from the singularity `a`. -/
theorem contDiffOn_div_rpow {k : WithTop ℕ∞} (hφ : ContDiffOn ℝ k φ U) (a μ : ℝ) :
    ContDiffOn ℝ k (fun x => φ x / (x - a) ^ μ) (U ∩ Ioi a) := by
  refine (hφ.mono inter_subset_left).div ?_ fun x hx =>
    ne_of_gt (rpow_pos_of_pos (by simpa [sub_pos] using hx.2) μ)
  intro x hx
  have hne : x - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hx.2)
  exact ((Real.contDiffAt_rpow_const_of_ne (p := μ) hne).comp x
    (contDiffAt_id.sub contDiffAt_const)).contDiffWithinAt

/-- **(9.49), the a priori bound on `I_2`.** Approximating `I_2 = ∫_{a+ε}^b φ(x)/(x - a)^μ dx` by
the composite closed Newton–Cotes formula with `m` subintervals and `n + 1` nodes on each, `n`
even, Theorem 9.3 on `[a + ε, b]` gives

`|E_2| ≤ 𝓜^{(n+2)}(ε) (b - a - ε)/(n + 2)! |M_n|/n^{n+3} ((b - a - ε)/m)^{n+2}`,

where `𝓜^{(n+2)}(ε) = max_{a+ε ≤ x ≤ b} |d^{n+2}/dx^{n+2} (φ(x)/(x - a)^μ)|`. The constant is the
one of the corrected (9.26) (see `theorem_9_3_even`). -/
theorem equation_9_49 (hn : Even n) (hn0 : 0 < n) (hε : 0 < ε) (hab : a + ε < b) (hm : 1 ≤ m)
    (hU : IsOpen U) (hUab : Icc a b ⊆ U) (hφ : ContDiffOn ℝ ((n + 2 : ℕ) : WithTop ℕ∞) φ U)
    {Mn : ℝ} (hM : ∀ x ∈ Icc (a + ε) b,
      |iteratedDeriv (n + 2) (fun y => φ y / (y - a) ^ μ) x| ≤ Mn) :
    |(∫ x in (a + ε)..b, φ x / (x - a) ^ μ)
        - Quadrature.compositeNewtonCotes n (fun x => φ x / (x - a) ^ μ) (a + ε) b m|
      ≤ Mn * ((b - a - ε) / (Nat.factorial (n + 2) : ℝ))
          * (|Quadrature.newtonCotesM n| / (n : ℝ) ^ (n + 3))
          * ((b - a - ε) / m) ^ (n + 2) := by
  have hsub : Icc (a + ε) b ⊆ U ∩ Ioi a := fun x hx =>
    ⟨hUab ⟨by linarith [hx.1], hx.2⟩, by simp only [mem_Ioi]; linarith [hx.1]⟩
  obtain ⟨ξ, hξ, h⟩ := theorem_9_3_even hn hn0 hab hm (hU.inter isOpen_Ioi) hsub
    (contDiffOn_div_rpow hφ a μ)
  have hba : (0 : ℝ) ≤ b - (a + ε) := by linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnpow : (0 : ℝ) < (n : ℝ) ^ (n + 3) := by positivity
  have hA : (0 : ℝ) ≤ (b - (a + ε)) / (Nat.factorial (n + 2) : ℝ) :=
    div_nonneg hba (by positivity)
  have hB : (0 : ℝ) ≤ |Quadrature.newtonCotesM n| / (n : ℝ) ^ (n + 3) :=
    div_nonneg (abs_nonneg _) hnpow.le
  have hC : (0 : ℝ) ≤ ((b - (a + ε)) / (m : ℝ)) ^ (n + 2) :=
    pow_nonneg (div_nonneg hba (by positivity)) _
  rw [show b - a - ε = b - (a + ε) by ring, h, abs_mul, abs_mul, abs_mul, abs_of_nonneg hA,
    abs_of_nonneg hC, abs_div, abs_of_pos hnpow]
  calc (b - (a + ε)) / (Nat.factorial (n + 2) : ℝ)
          * (|Quadrature.newtonCotesM n| / (n : ℝ) ^ (n + 3))
          * ((b - (a + ε)) / (m : ℝ)) ^ (n + 2)
          * |iteratedDeriv (n + 2) (fun y => φ y / (y - a) ^ μ) ξ|
      ≤ (b - (a + ε)) / (Nat.factorial (n + 2) : ℝ)
          * (|Quadrature.newtonCotesM n| / (n : ℝ) ^ (n + 3))
          * ((b - (a + ε)) / (m : ℝ)) ^ (n + 2) * Mn :=
        mul_le_mul_of_nonneg_left (hM ξ hξ) (mul_nonneg (mul_nonneg hA hB) hC)
    _ = Mn * ((b - (a + ε)) / (Nat.factorial (n + 2) : ℝ))
          * (|Quadrature.newtonCotesM n| / (n : ℝ) ^ (n + 3))
          * ((b - (a + ε)) / (m : ℝ)) ^ (n + 2) := by ring

/-! ### Example 9.10, the Fresnel integral -/

/-- **Example 9.10, the Fresnel integral (9.50).** Expanding the integrand in a Taylor series
around the origin and applying the theorem of integration by series,

`∫_0^{π/2} cos(x)/√x dx = ∑_{k=0}^∞ (-1)^k/(2k)! (π/2)^{2k+1/2}/(2k + 1/2)`.

Dominated convergence with the summable bound `(π/2)^{2k}/(2k)! · x^{-1/2}`. -/
theorem example_9_10 :
    HasSum (fun k : ℕ => (-1) ^ k / (Nat.factorial (2 * k) : ℝ) *
        ((π / 2) ^ (2 * (k : ℝ) + 1 / 2) / (2 * (k : ℝ) + 1 / 2)))
      (∫ x in (0 : ℝ)..(π / 2), cos x / √x) := by
  have hπ : (0 : ℝ) < π / 2 := by positivity
  have hinj : Function.Injective fun k : ℕ => 2 * k := fun i j h => by
    have h' : 2 * i = 2 * j := h
    omega
  have hsum₀ : Summable fun k : ℕ => (π / 2) ^ (2 * k) / (Nat.factorial (2 * k) : ℝ) := by
    simpa [Function.comp_def] using
      (Real.summable_pow_div_factorial (π / 2)).comp_injective hinj
  have key : HasSum (fun k : ℕ => ∫ x in (0 : ℝ)..(π / 2),
      (-1) ^ k / (Nat.factorial (2 * k) : ℝ) * (x ^ (2 * k) / √x))
      (∫ x in (0 : ℝ)..(π / 2), cos x / √x) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun k x => (π / 2) ^ (2 * k) / (Nat.factorial (2 * k) : ℝ) * x ^ (-(1 / 2) : ℝ))
      (fun k => (Measurable.aestronglyMeasurable (by fun_prop)).restrict) (fun k => ?_) ?_ ?_ ?_
    · filter_upwards with x hx
      rw [uIoc_of_le hπ.le] at hx
      have hx0 : 0 < x := hx.1
      have hsx : 0 < √x := Real.sqrt_pos.2 hx0
      have hfac : (0 : ℝ) < (Nat.factorial (2 * k) : ℝ) := by positivity
      have hneg : |(-1 : ℝ) ^ k| = 1 := by simp
      have hrpow : x ^ (-(1 / 2) : ℝ) = 1 / √x := by
        rw [Real.rpow_neg hx0.le, Real.sqrt_eq_rpow]
        exact (one_div _).symm
      calc ‖(-1 : ℝ) ^ k / (Nat.factorial (2 * k) : ℝ) * (x ^ (2 * k) / √x)‖
          = x ^ (2 * k) / ((Nat.factorial (2 * k) : ℝ) * √x) := by
            rw [Real.norm_eq_abs, abs_mul, abs_div, abs_div, hneg, abs_of_pos hfac,
              abs_of_nonneg (pow_nonneg hx0.le (2 * k)), abs_of_nonneg (Real.sqrt_nonneg x)]
            ring
        _ ≤ (π / 2) ^ (2 * k) / ((Nat.factorial (2 * k) : ℝ) * √x) :=
            div_le_div_of_nonneg_right (pow_le_pow_left₀ hx0.le hx.2 _) (by positivity)
        _ = (π / 2) ^ (2 * k) / (Nat.factorial (2 * k) : ℝ) * x ^ (-(1 / 2) : ℝ) := by
            rw [hrpow]; ring
    · filter_upwards with x _
      exact hsum₀.mul_right _
    · have heq : (fun t : ℝ => ∑' k : ℕ,
          (π / 2) ^ (2 * k) / (Nat.factorial (2 * k) : ℝ) * t ^ (-(1 / 2) : ℝ))
          = fun t : ℝ => (∑' k : ℕ, (π / 2) ^ (2 * k) / (Nat.factorial (2 * k) : ℝ))
              * t ^ (-(1 / 2) : ℝ) := funext fun t => tsum_mul_right
      rw [heq]
      exact (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _
    · filter_upwards with x _
      have h := (Real.hasSum_cos x).div_const (√x)
      refine h.congr_fun fun k => ?_
      ring
  have hterm : ∀ k : ℕ, (∫ x in (0 : ℝ)..(π / 2),
      (-1) ^ k / (Nat.factorial (2 * k) : ℝ) * (x ^ (2 * k) / √x))
      = (-1) ^ k / (Nat.factorial (2 * k) : ℝ) *
        ((π / 2) ^ (2 * (k : ℝ) + 1 / 2) / (2 * (k : ℝ) + 1 / 2)) := by
    intro k
    have h : ∀ x : ℝ, x ^ (2 * k) / √x = (x - 0) ^ (2 * k) / (x - 0) ^ (1 / 2 : ℝ) := by
      intro x
      rw [sub_zero, ← Real.sqrt_eq_rpow]
    have hexp : ((2 * k : ℕ) : ℝ) + 1 - 1 / 2 = 2 * (k : ℝ) + 1 / 2 := by push_cast; ring
    simp_rw [h]
    rw [intervalIntegral.integral_const_mul,
      Quadrature.integral_pow_div_rpow hπ.le (by norm_num) (2 * k), sub_zero, hexp]
  simpa only [hterm] using key

/-! ### Method 2: subtraction of the Taylor polynomial (9.51)–(9.52) -/

/-- **(9.51), the exact singular part of Method 2.** Splitting
`I(f) = ∫_a^b (φ - Φ_p)/(x - a)^μ + ∫_a^b Φ_p/(x - a)^μ = I_1 + I_2`, the second integral is
computed exactly:

`I_2 = (b - a)^{1-μ} ∑_{k=0}^p (b - a)^k φ^{(k)}(a)/(k!(k + 1 - μ))`. -/
theorem equation_9_51 (hab : a ≤ b) (hμ1 : μ < 1) (φ : ℝ → ℝ) (p : ℕ) :
    (∫ x in a..b, (∑ k ∈ Finset.range (p + 1),
        iteratedDeriv k φ a * (x - a) ^ k / (Nat.factorial k : ℝ)) / (x - a) ^ μ)
      = (b - a) ^ (1 - μ) * ∑ k ∈ Finset.range (p + 1),
          (b - a) ^ k * iteratedDeriv k φ a / ((Nat.factorial k : ℝ) * ((k : ℝ) + 1 - μ)) :=
  integral_taylorSum_div_rpow hab hμ1 φ p

/-- **(9.52), the regularized integrand of Method 2.** For `φ` of class `C^{p+1}` on an open set
containing `[a, b]` there is a choice `ξ(x) ∈ (a, x)` of the Lagrange point of (9.47) with

`(φ(x) - Φ_p(x))/(x - a)^μ = (x - a)^{p+1-μ} φ^{(p+1)}(ξ(x))/(p + 1)!` for every `x ∈ (a, b]`,

so that `I_1 = ∫_a^b (x - a)^{p+1-μ} φ^{(p+1)}(ξ(x))/(p + 1)! dx = ∫_a^b g(x) dx`. -/
theorem equation_9_52 (hab : a < b) (hU : IsOpen U) (hUab : Icc a b ⊆ U)
    (hφ : ContDiffOn ℝ ((p + 1 : ℕ) : WithTop ℕ∞) φ U) (μ : ℝ) :
    ∃ ξ : ℝ → ℝ, (∀ x ∈ Ioc a b, ξ x ∈ Ioo a x) ∧
      (∀ x ∈ Ioc a b, (φ x - ∑ k ∈ Finset.range (p + 1),
          iteratedDeriv k φ a * (x - a) ^ k / (Nat.factorial k : ℝ)) / (x - a) ^ μ
        = (x - a) ^ ((p : ℝ) + 1 - μ) * iteratedDeriv (p + 1) φ (ξ x)
            / (Nat.factorial (p + 1) : ℝ)) ∧
      (∫ x in a..b, (φ x - ∑ k ∈ Finset.range (p + 1),
          iteratedDeriv k φ a * (x - a) ^ k / (Nat.factorial k : ℝ)) / (x - a) ^ μ)
        = ∫ x in a..b, (x - a) ^ ((p : ℝ) + 1 - μ) * iteratedDeriv (p + 1) φ (ξ x)
            / (Nat.factorial (p + 1) : ℝ) := by
  have step : ∀ x ∈ Ioc a b, ∃ t ∈ Ioo a x,
      (φ x - ∑ k ∈ Finset.range (p + 1),
          iteratedDeriv k φ a * (x - a) ^ k / (Nat.factorial k : ℝ)) / (x - a) ^ μ
        = (x - a) ^ ((p : ℝ) + 1 - μ) * iteratedDeriv (p + 1) φ t
            / (Nat.factorial (p + 1) : ℝ) := by
    intro x hx
    obtain ⟨t, ht, h⟩ := equation_9_47 hU hUab hφ hx
    refine ⟨t, ht, ?_⟩
    have hxa : (0 : ℝ) < x - a := by linarith [hx.1]
    have hpow : (x - a) ^ (p + 1) / (x - a) ^ μ = (x - a) ^ ((p : ℝ) + 1 - μ) := by
      rw [show ((p : ℝ) + 1 - μ) = ((p + 1 : ℕ) : ℝ) - μ by push_cast; ring,
        Real.rpow_sub hxa, Real.rpow_natCast]
    rw [h, add_sub_cancel_left, ← hpow]
    ring
  choose! ξ hξmem hξeq using step
  refine ⟨ξ, hξmem, hξeq, intervalIntegral.integral_congr_ae ?_⟩
  rw [uIoc_of_le hab.le]
  filter_upwards with x hx using hξeq x hx

/-! ### §9.8.3 Integrals over unbounded intervals -/

/-- **(9.53).** For `f` integrable over `[a, ∞)` the improper integral is the limit of the proper
ones, `I(f) = ∫_a^∞ f(x) dx = lim_{t → +∞} ∫_a^t f(x) dx`. -/
theorem equation_9_53 (hf : IntegrableOn f (Ioi a)) :
    Tendsto (fun t => ∫ x in a..t, f x) atTop (𝓝 (∫ x in Ioi a, f x)) :=
  intervalIntegral_tendsto_integral_Ioi a hf tendsto_id

/-- **(9.54).** For `f : ℝ → ℝ` integrable over every bounded interval and over `ℝ`,
`∫_{-∞}^∞ f = ∫_{-∞}^c f + ∫_c^∞ f` for every real `c`; the definition is correct because the
value does not depend on the choice of `c`. -/
theorem equation_9_54 (hf : Integrable f) (c : ℝ) :
    (∫ x in Iic c, f x) + (∫ x in Ioi c, f x) = ∫ x, f x :=
  intervalIntegral.integral_Iic_add_Ioi hf.integrableOn hf.integrableOn

/-- **The sufficient condition for integrability of §9.8.3.** If `f` is continuous on `[a, +∞)`
and there is `ρ > 0` with `lim_{x → +∞} x^{1+ρ} f(x) = 0` — `f` infinitesimal of order `> 1` with
respect to `1/x` — then `f` is integrable over `[a, +∞)`. -/
theorem integrable_of_tendsto_rpow_mul (hf : ContinuousOn f (Ici a)) (hρ : 0 < ρ)
    (hlim : Tendsto (fun x => x ^ (1 + ρ) * f x) atTop (𝓝 0)) : IntegrableOn f (Ioi a) :=
  Quadrature.integrableOn_Ioi_of_tendsto_rpow_mul hf hρ hlim

/-- **(9.55), Method 2 for unbounded intervals.** The change of variable `x = 1/t` transforms
`I_2 = ∫_c^∞ f(x) dx`, `c > 0`, into an integral over the bounded interval `[0, 1/c]`:

`I_2 = ∫_0^{1/c} f(1/t) t^{-2} dt = ∫_0^{1/c} g(t) dt`.

Erratum: the book prints `f(t)` where it means `f(1/t)`. -/
theorem equation_9_55 (hc : 0 < c) (f : ℝ → ℝ) :
    ∫ x in Ioi c, f x = ∫ t in Ioo 0 (1 / c), f (1 / t) / t ^ 2 :=
  Quadrature.integral_Ioi_eq_integral_Ioo_inv hc f

/-! ### Method 3: Gauss–Laguerre and Gauss–Hermite -/

/-- **Method 3 of §9.8.3, Gauss–Laguerre.** For every `n` there are `n` distinct nodes — the zeros
of the `n`-th orthogonal polynomial of the weight `e^{-x}` on `(0, ∞)`, the Laguerre polynomial
`ℒ_n` of §10.5 — and positive weights with

`∑_{k<n} α_k p(x_k) = ∫_0^∞ e^{-x} p(x) dx` for every `p ∈ ℙ_{2n-1}`. -/
theorem gaussLaguerre (n : ℕ) :
    ∃ x w : Fin n → ℝ, Function.Injective x ∧ (∀ i, 0 < w i) ∧
      ∀ P : Polynomial ℝ, P.degree < (2 * n : ℕ) →
        ∑ i, w i * P.eval (x i) = ∫ t in Ioi (0 : ℝ), exp (-t) * P.eval t := by
  obtain ⟨x, w, hx, hw, h⟩ :=
    Quadrature.exists_gauss OrthogonalPolynomial.isWeight_laguerreMeasure n
  exact ⟨x, w, hx, hw, fun P hP =>
    (h P hP).trans (OrthogonalPolynomial.integral_laguerreMeasure _)⟩

/-- **Method 3 of §9.8.3, Gauss–Hermite.** The same for the weight `e^{-x²}` on `ℝ`, whose
orthogonal polynomials are the Hermite polynomials of §10.5:

`∑_{k<n} α_k p(x_k) = ∫_{-∞}^∞ e^{-x²} p(x) dx` for every `p ∈ ℙ_{2n-1}`. -/
theorem gaussHermite (n : ℕ) :
    ∃ x w : Fin n → ℝ, Function.Injective x ∧ (∀ i, 0 < w i) ∧
      ∀ P : Polynomial ℝ, P.degree < (2 * n : ℕ) →
        ∑ i, w i * P.eval (x i) = ∫ t : ℝ, exp (-t ^ 2) * P.eval t := by
  obtain ⟨x, w, hx, hw, h⟩ :=
    Quadrature.exists_gauss OrthogonalPolynomial.isWeight_hermiteMeasure n
  exact ⟨x, w, hx, hw, fun P hP =>
    (h P hP).trans (OrthogonalPolynomial.integral_hermiteMeasure _)⟩

end QuarteroniSaccoSaleri.Chapter09
