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
# Polynomials against the weights `e^{-x}` and `e^{-x²}`

The integrability and decay facts behind the orthogonality of the Laguerre and Hermite
polynomials, the companions of Mathlib's `Polynomial.tendsto_div_exp_atTop`:

* `Polynomial.integrableOn_eval_mul_exp_neg`: `p(x) e^{-x}` is integrable on `(0, ∞)`;
* `Polynomial.integrable_eval_mul_exp_neg_sq`: `p(x) e^{-x²}` is integrable on `ℝ`;
* `Real.tendsto_pow_mul_exp_neg_sq_atTop_nhds_zero`, `Polynomial.tendsto_eval_mul_exp_neg_sq_atTop`
  and `Polynomial.tendsto_eval_mul_exp_neg_sq_atBot`: `xⁱ e^{-x²}` and `p(x) e^{-x²}` tend to `0`
  at `±∞`.

Each is reduced to monomials through `Polynomial.eval_eq_sum_range`.
-/

open MeasureTheory Polynomial Real Set Filter Topology

namespace Polynomial

/-- A polynomial times `e^{-x}` is integrable on `(0, ∞)`: each monomial is a Gamma integrand. -/
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

/-- A polynomial times `e^{-x²}` is integrable on `ℝ`. -/
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

/-- `x^i e^{-x²}` tends to `0` at `+∞`. -/
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

/-- A polynomial times `e^{-x²}` tends to `0` at `+∞`. -/
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

/-- A polynomial times `e^{-x²}` tends to `0` at `-∞`, by symmetry. -/
theorem tendsto_eval_mul_exp_neg_sq_atBot (p : ℝ[X]) :
    Tendsto (fun x => p.eval x * exp (-x ^ 2)) atBot (𝓝 0) := by
  have h := (tendsto_eval_mul_exp_neg_sq_atTop (p.comp (-X))).comp tendsto_neg_atBot_atTop
  refine h.congr fun x => ?_
  simp [eval_comp]

end Polynomial
