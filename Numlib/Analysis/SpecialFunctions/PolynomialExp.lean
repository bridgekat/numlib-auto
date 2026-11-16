/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.SpecialFunctions.PolynomialExp`, beside
`Polynomial.tendsto_div_exp_atTop`, for the limits; the integrability lemmas need more than that
file imports, so `integrableOn_eval_mul_exp_neg` belongs in a file importing
`Mathlib.Analysis.SpecialFunctions.Gamma.Basic` and `integrable_eval_mul_exp_neg_sq` in one
importing `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.PolynomialExp

/-!
# Polynomials against the weights $e^{-x}$ and $e^{-x^2}$

This file proves the integrability and decay facts behind the orthogonality of the Laguerre and
Hermite polynomials. For a real polynomial $p$, the function $p(x) e^{-x}$ is integrable on
$(0, \infty)$, and $p(x) e^{-x^2}$ is integrable on $\mathbb{R}$ and tends to $0$ at $\pm\infty$.
These results are companions of Mathlib's `Polynomial.tendsto_div_exp_atTop`. Each proof reduces to
monomials through `Polynomial.eval_eq_sum_range`.

## Main results

* `Polynomial.integrableOn_eval_mul_exp_neg`: $p(x) e^{-x}$ is integrable on $(0, \infty)$.
* `Polynomial.integrable_eval_mul_exp_neg_sq`: $p(x) e^{-x^2}$ is integrable on $\mathbb{R}$.
* `Real.tendsto_pow_mul_exp_neg_sq_atTop_nhds_zero`: $x^i e^{-x^2} \to 0$ as $x \to +\infty$.
* `Polynomial.tendsto_eval_mul_exp_neg_sq_atTop`, `Polynomial.tendsto_eval_mul_exp_neg_sq_atBot`:
  $p(x) e^{-x^2} \to 0$ as $x \to \pm\infty$.
-/

open MeasureTheory Polynomial Real Set Filter Topology

namespace Polynomial

/-- For every real polynomial $p$, the function $x \mapsto p(x) e^{-x}$ is integrable on
$(0, \infty)$ with respect to the Lebesgue measure.

Each monomial $x^i e^{-x}$ is the integrand of the Gamma function at $i + 1$. -/
theorem integrableOn_eval_mul_exp_neg (p : ℝ[X]) :
    IntegrableOn (fun x => p.eval x * exp (-x)) (Ioi 0) := by
  have hmono : ∀ i : ℕ, IntegrableOn (fun x : ℝ => x ^ i * exp (-x)) (Ioi 0) := by
    intro i
    have h := Real.GammaIntegral_convergent (s := (i : ℝ) + 1) (by positivity)
    refine (h.congr_fun (fun x hx => ?_) measurableSet_Ioi)
    simp only [add_sub_cancel_right, rpow_natCast]
    ring
  have heq : (fun x => p.eval x * exp (-x)) =
      fun x => ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (x ^ i * exp (-x)) := by
    funext x
    rw [eval_eq_sum_range, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [heq]
  exact integrable_finsetSum _ fun i _ => (hmono i).const_mul _

/-- For every real polynomial $p$, the function $x \mapsto p(x) e^{-x^2}$ is integrable on
$\mathbb{R}$ with respect to the Lebesgue measure. -/
theorem integrable_eval_mul_exp_neg_sq (p : ℝ[X]) :
    Integrable fun x => p.eval x * exp (-x ^ 2) := by
  have hmono : ∀ i : ℕ, Integrable fun x : ℝ => x ^ i * exp (-x ^ 2) := by
    intro i
    have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1) one_pos (s := i) (by
      exact_mod_cast (by omega : -1 < (i : ℤ)))
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp [rpow_natCast]
  have heq : (fun x => p.eval x * exp (-x ^ 2)) =
      fun x => ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (x ^ i * exp (-x ^ 2)) := by
    funext x
    rw [eval_eq_sum_range, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [heq]
  exact integrable_finsetSum _ fun i _ => (hmono i).const_mul _

/-- For every natural number $i$, $x^i e^{-x^2} \to 0$ as $x \to +\infty$. -/
theorem _root_.Real.tendsto_pow_mul_exp_neg_sq_atTop_nhds_zero (i : ℕ) :
    Tendsto (fun x : ℝ => x ^ i * exp (-x ^ 2)) atTop (𝓝 0) := by
  have hhalf : Tendsto (fun x : ℝ => (1 / 2) * x) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) tendsto_id
  have hexp : Tendsto (fun x : ℝ => exp (-(1 / 2) * x)) atTop (𝓝 0) := by
    have := tendsto_exp_neg_atTop_nhds_zero.comp hhalf
    refine this.congr fun x => ?_
    simp only [Function.comp_apply, neg_mul]
  have h := (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg one_pos (i : ℝ)).trans_tendsto hexp
  refine h.congr' (Eventually.of_forall fun x => ?_)
  simp [rpow_natCast]

/-- For every real polynomial $p$, $p(x) e^{-x^2} \to 0$ as $x \to +\infty$. -/
theorem tendsto_eval_mul_exp_neg_sq_atTop (p : ℝ[X]) :
    Tendsto (fun x => p.eval x * exp (-x ^ 2)) atTop (𝓝 0) := by
  have heq : (fun x => p.eval x * exp (-x ^ 2)) =
      fun x => ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (x ^ i * exp (-x ^ 2)) := by
    funext x
    rw [eval_eq_sum_range, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [heq]
  have h : Tendsto (fun x => ∑ i ∈ Finset.range (p.natDegree + 1),
      p.coeff i * (x ^ i * exp (-x ^ 2))) atTop (𝓝 (∑ i ∈ Finset.range (p.natDegree + 1),
      p.coeff i * 0)) :=
    tendsto_finsetSum _ fun i _ => (Real.tendsto_pow_mul_exp_neg_sq_atTop_nhds_zero i).const_mul _
  simpa using h

/-- For every real polynomial $p$, $p(x) e^{-x^2} \to 0$ as $x \to -\infty$.

The proof applies the limit at $+\infty$ to the polynomial $p(-x)$. -/
theorem tendsto_eval_mul_exp_neg_sq_atBot (p : ℝ[X]) :
    Tendsto (fun x => p.eval x * exp (-x ^ 2)) atBot (𝓝 0) := by
  have h := (tendsto_eval_mul_exp_neg_sq_atTop (p.comp (-X))).comp tendsto_neg_atBot_atTop
  refine h.congr fun x => ?_
  simp [eval_comp]

end Polynomial
