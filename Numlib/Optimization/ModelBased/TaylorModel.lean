import Numlib.Optimization.ModelBased.PowRegularizedModel
import Numlib.Optimization.ModelBased.QuadraticModel

/-!
# Regularized Taylor models

Adaptive-regularization methods of [cartis2022evaluation] (AR1 (2.4.1), AR2 (3.3.1), ARp (4.1.2),
ARqp (12.2.23), and their inexact variants of Chapter 13) minimize, at each iteration, the model
`m(s) = T_p(s) + σ/(p+1)! ‖s‖^{p+1}`,
where `T_p = D.taylorSum p` is the Taylor sum of derivative data `D` (the exact jet
`ftaylorSeries ℝ f x` of the objective, or inexact data). This is
`Optimization.regularizedModel D p σ`, the case `r = p + 1` of the real-power model
`Optimization.powRegularizedModel` (`regularizedModel_eq_powRegularizedModel`).

All estimates are for one iteration (point `x`, weight `σ`, step `s`), with explicit constants,
under a Lipschitz condition on `∇^p f` on a convex set `C` containing `x` and `x + s`:

* `Optimization.lt_taylorDecrement_of_regularizedModel_lt`: Lemmas 3.3.1, 4.1.1;
* `Optimization.abs_reductionRatio_sub_one_le_of_lipschitz`,
  `Optimization.le_reductionRatio_of_lipschitz`: the ratio estimate behind Lemmas 2.4.2, 3.3.2,
  4.1.2, with a parameter `c` in the decrease `T_p(0) - T_p(s) ≥ c σ ‖s‖^{p+1}` (`c = 1/(p+1)!` from
  Lemma 4.1.1, `c = 1` for the exact AR1 step);
* `Optimization.norm_gradient_add_le_of_lipschitz`: `‖∇f(x+s)‖ ≤ L/2 ‖s‖² + ‖∇f(x) + ∇²f(x) s‖`;
* `Optimization.norm_fderiv_le_of_regularizedModel`,
  `Optimization.minCurvature_ge_of_regularizedModel`: the step bounds of Lemmas 3.3.3, 3.3.8 and
  4.1.3 ((4.1.24)–(4.1.29));
* `Optimization.abs_iteratedFDeriv_apply_le_of_regularizedModel`: the derivative comparison
  (4.1.30), (6.2.23) for every order `j ≤ p`;
* `Optimization.exists_isMinOn_regularizedModel`: global minimizers of the model exist in finite
  dimension;
* `Optimization.regularizedModel_two_eq_regModel`: for `p = 2` the model is the cubic
  regularization model `Subproblem.regModel` of Chapters 8–10.
-/

open Set Filter
open scoped Nat RealInnerProductSpace

namespace Optimization

section Model

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The regularized Taylor model of adaptive-regularization methods ([cartis2022evaluation],
(2.4.1), (3.3.1), (4.1.2), (12.2.23)): `m(s) = T_p(s) + σ/(p+1)! ‖s‖^{p+1}`, with
`T_p = D.taylorSum p` the Taylor sum of the derivative data `D`. -/
noncomputable def regularizedModel (D : FormalMultilinearSeries ℝ E ℝ) (p : ℕ) (σ : ℝ) (s : E) :
    ℝ :=
  D.taylorSum p s + σ / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1)

variable (D : FormalMultilinearSeries ℝ E ℝ) (p : ℕ) (σ : ℝ)

theorem regularizedModel_def (s : E) :
    regularizedModel D p σ s = D.taylorSum p s + σ / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) := rfl

/-- The model at the zero step is `T_p(0)`. -/
@[simp]
theorem regularizedModel_zero_right : regularizedModel D p σ 0 = D.taylorSum p 0 := by
  simp [regularizedModel_def]

/-- For the exact jet the model at the zero step is `f(x)`. -/
theorem regularizedModel_ftaylorSeries_zero_right (f : E → ℝ) (x : E) :
    regularizedModel (ftaylorSeries ℝ f x) p σ 0 = f x := by
  rw [regularizedModel_zero_right, ← taylorPolynomial_eq_taylorSum, taylorPolynomial_zero_right]

/-- The model is the real-power model with `r = p + 1`. -/
theorem regularizedModel_eq_powRegularizedModel :
    regularizedModel D p σ = powRegularizedModel D p σ ((p : ℝ) + 1) := by
  funext s
  rw [regularizedModel_def, powRegularizedModel_def, realFactorial_natCast_add_one,
    show ((p : ℝ) + 1) = ((p + 1 : ℕ) : ℝ) by push_cast; rfl, Real.rpow_natCast]

/-- The model as a sum of the Taylor sum and the regularization term. -/
theorem regularizedModel_eq_add :
    regularizedModel D p σ =
      D.taylorSum p + fun s : E => (σ / ((p + 1)! : ℝ)) • ‖s‖ ^ (p + 1) := by
  funext s
  simp [regularizedModel_def, smul_eq_mul]

theorem continuous_regularizedModel : Continuous (regularizedModel D p σ) :=
  ((D.contDiff_taylorSum p (n := 0)).continuous).add (continuous_const.mul (by fun_prop))

variable {D p σ}

/-- **Lemmas 3.3.1 and 4.1.1** ([cartis2022evaluation], (4.1.18)): `m(s) ≤ m(0)` gives
`T_p(0) - T_p(s) ≥ σ/(p+1)! ‖s‖^{p+1}`. -/
theorem taylorDecrement_ge_of_regularizedModel_le {s : E}
    (h : regularizedModel D p σ s ≤ regularizedModel D p σ 0) :
    σ / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) ≤ D.taylorDecrement p s := by
  rw [regularizedModel_zero_right, regularizedModel_def] at h
  rw [FormalMultilinearSeries.taylorDecrement]
  linarith

/-- **Lemmas 3.3.1 and 4.1.1**, strict form: `m(s) < m(0)` (condition (4.1.10)) gives
`T_p(0) - T_p(s) > σ/(p+1)! ‖s‖^{p+1}`. -/
theorem lt_taylorDecrement_of_regularizedModel_lt {s : E}
    (h : regularizedModel D p σ s < regularizedModel D p σ 0) :
    σ / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) < D.taylorDecrement p s := by
  rw [regularizedModel_zero_right, regularizedModel_def] at h
  rw [FormalMultilinearSeries.taylorDecrement]
  linarith

/-- A step strictly decreasing the model is nonzero. -/
theorem ne_zero_of_regularizedModel_lt {s : E}
    (h : regularizedModel D p σ s < regularizedModel D p σ 0) : s ≠ 0 := by
  rintro rfl
  exact lt_irrefl _ h

/-- `‖·‖^{p+1}` is `C^j` at `s` if `j ≤ p` or `s ≠ 0`. -/
theorem contDiffAt_norm_pow_succ {j : ℕ} {s : E} (hj : j ≤ p ∨ s ≠ 0) :
    ContDiffAt ℝ j (fun y : E => ‖y‖ ^ (p + 1)) s := by
  rcases hj with hj | hs
  · have := (contDiff_norm_pow (E := E) (r := p + 1) (by omega)).contDiffAt (x := s)
    rw [Nat.add_sub_cancel] at this
    exact this.of_le (by exact_mod_cast hj)
  · exact (contDiffAt_norm_pow (p + 1) hs).of_le le_top

/-- The model is `C^p`. -/
theorem contDiff_regularizedModel : ContDiff ℝ p (regularizedModel D p σ) := by
  rw [regularizedModel_eq_add]
  have := contDiff_norm_pow (E := E) (r := p + 1) (by omega)
  rw [Nat.add_sub_cancel] at this
  exact (D.contDiff_taylorSum p).add (this.const_smul _)

/-- **Derivatives of the model** ([cartis2022evaluation], proof of Lemma 4.1.3): for `j ≤ p`, or
for every `j` at `s ≠ 0`, `∇^j m(s) = ∇^j T_p(s) + σ/(p+1)! ∇^j(‖·‖^{p+1})(s)`. -/
theorem iteratedFDeriv_regularizedModel {j : ℕ} {s : E} (hj : j ≤ p ∨ s ≠ 0) :
    iteratedFDeriv ℝ j (regularizedModel D p σ) s =
      iteratedFDeriv ℝ j (D.taylorSum p) s +
        (σ / ((p + 1)! : ℝ)) • iteratedFDeriv ℝ j (fun y : E => ‖y‖ ^ (p + 1)) s := by
  have hN := contDiffAt_norm_pow_succ (p := p) hj
  rw [regularizedModel_eq_add, iteratedFDeriv_add_apply (D.contDiff_taylorSum p).contDiffAt
    (hN.const_smul _), iteratedFDeriv_const_smul_apply' hN]

/-- **Gradient of the model** ([cartis2022evaluation], (3.3.2), proof of Lemma 4.1.3): for
`p ≥ 1`, `∇m(s) = ∇T_p(s) + σ/p! ‖s‖^{p-1} s`. -/
theorem hasFDerivAt_regularizedModel (hp : 1 ≤ p) (s : E) :
    HasFDerivAt (regularizedModel D p σ)
      (fderiv ℝ (D.taylorSum p) s + (σ / (p ! : ℝ) * ‖s‖ ^ (p - 1)) • innerSL ℝ s) s := by
  rw [regularizedModel_eq_powRegularizedModel]
  have h := hasFDerivAt_powRegularizedModel (D := D) (p := p) (σ := σ)
    (r := (p : ℝ) + 1) (by have : (1 : ℝ) ≤ p := (by exact_mod_cast hp); linarith) s
  have h1 : (p : ℝ) + 1 - 1 = (p : ℕ) := by ring
  have h2 : (p : ℝ) + 1 - 2 = ((p - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hp]; push_cast; ring
  rwa [h1, h2, realFactorial_natCast, Real.rpow_natCast] at h

/-- The gradient of the model ([cartis2022evaluation], (3.3.2), (4.1.26)): for `p ≥ 1`,
`∇m(s) = ∇T_p(s) + σ/p! ‖s‖^{p-1} s`. -/
theorem fderiv_regularizedModel (hp : 1 ≤ p) (s : E) :
    fderiv ℝ (regularizedModel D p σ) s =
      fderiv ℝ (D.taylorSum p) s + (σ / (p ! : ℝ) * ‖s‖ ^ (p - 1)) • innerSL ℝ s :=
  (hasFDerivAt_regularizedModel hp s).fderiv

/-- For the exact jet of a function `C^p` at `x`, `p ≥ 1`, the model has the gradient of `f` at
the zero step: `∇m(0) = ∇f(x)`. -/
theorem fderiv_regularizedModel_ftaylorSeries_zero {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ p f x) (hp : 1 ≤ p) :
    fderiv ℝ (regularizedModel (ftaylorSeries ℝ f x) p σ) 0 = fderiv ℝ f x := by
  rw [fderiv_regularizedModel hp, map_zero, smul_zero, add_zero]
  ext v
  have h := congrArg (fun A => A (fun _ => v)) (iteratedFDeriv_taylorPolynomial_zero hf hp)
  simpa [iteratedFDeriv_one_apply, taylorPolynomial_eq_taylorSum] using h

/-- For the exact jet of a function `C^p` at `x`, `p ≥ 2`, the model has the Hessian of `f` at the
zero step: `∇²m(0) = ∇²f(x)` (the regularization term has zero Hessian at `0` since `p + 1 > 2`). -/
theorem iteratedFDeriv_two_regularizedModel_ftaylorSeries_zero {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ p f x) (hp : 2 ≤ p) :
    iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ f x) p σ) 0 =
      iteratedFDeriv ℝ 2 f x := by
  have h2 : ((2 : ℕ) : ℝ) < ((p + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_of_le hp
  rw [iteratedFDeriv_regularizedModel (Or.inl hp), ← taylorPolynomial_eq_taylorSum,
    iteratedFDeriv_taylorPolynomial_zero hf hp, NormPowIteratedFDeriv.norm_pow_eq_normRpow,
    iteratedFDeriv_normRpow_zero h2, smul_zero, add_zero]

end Model

section Estimates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {f : E → ℝ} {p : ℕ} {L σ : ℝ} {C : Set E} {x s : E}

/-- **The ratio estimate** behind Lemmas 2.4.2, 3.3.2 and 4.1.2 ([cartis2022evaluation]): let
`f` be `C^p` on a convex set `C ∋ x, x + s` with `L`-Lipschitz `p`-th derivative there, `c, σ > 0`,
`s ≠ 0`, and let the Taylor decrement satisfy `T_p(x, 0) - T_p(x, s) ≥ c σ ‖s‖^{p+1}`. Then the
ratio `ρ = (f(x) - f(x + s)) / (T_p(x, 0) - T_p(x, s))` satisfies
`|ρ - 1| ≤ L / ((p+1)! c σ)`. Lemma 4.1.1 gives `c = 1/(p+1)!` (so `|ρ - 1| ≤ L/σ`); the exact AR1
step gives `c = 1`. -/
theorem abs_reductionRatio_sub_one_le_of_lipschitz (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hL : IteratedFDerivLipschitzOn f p L C) (hx : x ∈ C)
    (hxs : x + s ∈ C) (hs : s ≠ 0) {c : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    (hdec : c * σ * ‖s‖ ^ (p + 1) ≤ (ftaylorSeries ℝ f x).taylorDecrement p s) :
    |reductionRatio f x s ((ftaylorSeries ℝ f x).taylorDecrement p s) - 1| ≤
      L / ((p + 1)! * c * σ) := by
  set Δ := (ftaylorSeries ℝ f x).taylorDecrement p s
  have hspos : 0 < ‖s‖ := norm_pos_iff.2 hs
  have hΔ : 0 < Δ := lt_of_lt_of_le (by positivity) hdec
  have hT := abs_sub_taylorPolynomial_le_of_lipschitz hC hf hL hx hxs
  have hL0 : 0 ≤ L := nonneg_of_abs_le_div_mul_pow (by positivity) hspos hT
  refine abs_reductionRatio_sub_one_le hΔ ?_
  have heq : f (x + s) - (f x - Δ) = f (x + s) - taylorPolynomial f p x s := by
    simp only [Δ, FormalMultilinearSeries.taylorDecrement, ← taylorPolynomial_eq_taylorSum,
      taylorPolynomial_zero_right]
    ring
  rw [heq]
  calc |f (x + s) - taylorPolynomial f p x s| ≤ L / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) := hT
    _ = L / ((p + 1)! * c * σ) * (c * σ * ‖s‖ ^ (p + 1)) := by
        field_simp
    _ ≤ L / ((p + 1)! * c * σ) * Δ := by gcongr

/-- **Very successful iterations** (the forcing step of Lemmas 2.4.2, 3.3.2, 4.1.2,
[cartis2022evaluation]): under the hypotheses of
`Optimization.abs_reductionRatio_sub_one_le_of_lipschitz`, `L ≤ (p+1)! c σ (1 - η)` gives
`ρ ≥ η`. With `c = 1/(p+1)!` this is `σ ≥ L / (1 - η)`. -/
theorem le_reductionRatio_of_lipschitz (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hL : IteratedFDerivLipschitzOn f p L C) (hx : x ∈ C)
    (hxs : x + s ∈ C) (hs : s ≠ 0) {c : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    (hdec : c * σ * ‖s‖ ^ (p + 1) ≤ (ftaylorSeries ℝ f x).taylorDecrement p s) {η : ℝ}
    (hη : L ≤ (p + 1)! * c * σ * (1 - η)) :
    η ≤ reductionRatio f x s ((ftaylorSeries ℝ f x).taylorDecrement p s) := by
  have h := abs_reductionRatio_sub_one_le_of_lipschitz hC hf hL hx hxs hs hc hσ hdec
  have hpos : (0 : ℝ) < (p + 1)! * c * σ := by positivity
  have : L / ((p + 1)! * c * σ) ≤ 1 - η := by
    rw [div_le_iff₀ hpos]; linarith
  linarith [neg_abs_le (reductionRatio f x s ((ftaylorSeries ℝ f x).taylorDecrement p s) - 1)]

/-- The model gradient of the Taylor part (Lemma 3.3.7, [cartis2022evaluation], with the step
condition (3.3.23) on `∇T_p` rather than `∇m`): `‖∇f(x + s)‖ ≤ L/p! ‖s‖^p + ‖∇_s T_p(x, s)‖`. -/
theorem norm_fderiv_le_of_taylorPolynomial (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hp : 1 ≤ p) (hL : IteratedFDerivLipschitzOn f p L C)
    (hx : x ∈ C) (hxs : x + s ∈ C) :
    ‖fderiv ℝ f (x + s)‖ ≤ L / (p ! : ℝ) * ‖s‖ ^ p + ‖fderiv ℝ (taylorPolynomial f p x) s‖ := by
  have hT := norm_iteratedFDeriv_sub_taylorPolynomial_le_of_lipschitz hC hf hL hx hxs hp
  rw [norm_iteratedFDeriv_one_sub, Nat.sub_add_cancel hp] at hT
  calc ‖fderiv ℝ f (x + s)‖ = ‖(fderiv ℝ f (x + s) - fderiv ℝ (taylorPolynomial f p x) s) +
        fderiv ℝ (taylorPolynomial f p x) s‖ := by rw [sub_add_cancel]
    _ ≤ _ := (norm_add_le _ _).trans (by gcongr)

/-- The gradient at the trial point for `p = 2` in vector form: if `f` is `C²` on a convex
`C ∋ x, x + s` with `L`-Lipschitz Hessian there, then
`‖∇f(x + s)‖ ≤ L/2 ‖s‖² + ‖∇f(x) + ∇²f(x) s‖` (the step bounds behind Lemmas 3.4.3, 3.4.9 and
3.5.2 of [cartis2022evaluation]). -/
theorem norm_gradient_add_le_of_lipschitz [CompleteSpace E] (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ 2 f y) (hL : IteratedFDerivLipschitzOn f 2 L C) (hx : x ∈ C)
    (hxs : x + s ∈ C) :
    ‖gradient f (x + s)‖ ≤ L / 2 * ‖s‖ ^ 2 + ‖gradient f x + hessianOperator f x s‖ := by
  have hfx := hf x hx
  have h := norm_fderiv_le_of_taylorPolynomial hC hf (by norm_num : 1 ≤ 2) hL hx hxs
  have hT : taylorPolynomial f 2 x =
      fun s => f x + Subproblem.quadModel (gradient f x) (hessianOperator f x) s :=
    funext fun s => taylorPolynomial_two_eq_quadModel hfx s
  have hd : fderiv ℝ (taylorPolynomial f 2 x) s =
      innerSL ℝ (gradient f x + hessianOperator f x s) := by
    rw [hT]
    exact ((Subproblem.hasFDerivAt_quadModel (hessianOperator_isSymmetric hfx) s).const_add
      (f x)).fderiv
  rw [hd, innerSL_apply_norm, ← norm_gradient_eq] at h
  norm_num [Nat.factorial] at h
  rw [norm_gradient_eq]
  linarith [norm_gradient_eq f (x + s)]

/-- **Step bound, first order** ([cartis2022evaluation], (4.1.24)–(4.1.26), Lemma 3.3.3): for
`p ≥ 1`, `σ ≥ 0`, `f` `C^p` on a convex `C ∋ x, x + s` with `L`-Lipschitz `∇^p f` there, and
`m = regularizedModel (ftaylorSeries ℝ f x) p σ`:
`‖∇f(x + s)‖ ≤ (L + σ)/p! ‖s‖^p + ‖∇m(s)‖`. -/
theorem norm_fderiv_le_of_regularizedModel (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hp : 1 ≤ p) (hL : IteratedFDerivLipschitzOn f p L C)
    (hx : x ∈ C) (hxs : x + s ∈ C) (hσ : 0 ≤ σ) :
    ‖fderiv ℝ f (x + s)‖ ≤ (L + σ) / (p ! : ℝ) * ‖s‖ ^ p +
      ‖fderiv ℝ (regularizedModel (ftaylorSeries ℝ f x) p σ) s‖ := by
  have hp' : (1 : ℝ) < (p : ℝ) + 1 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have h := norm_fderiv_le_of_powRegularizedModel hC hf hp zero_le_one hL.holderOn hx hxs hσ hp'
  rw [← regularizedModel_eq_powRegularizedModel] at h
  have h1 : holderFactorial (p - 1) 1 = (p ! : ℝ) := by
    rw [holderFactorial_one_right, Nat.sub_add_cancel hp]
  have h2 : ‖s‖ ^ (((p - 1 : ℕ) : ℝ) + 1) = ‖s‖ ^ p := by
    rw [show ((p - 1 : ℕ) : ℝ) + 1 = ((p : ℕ) : ℝ) by rw [Nat.cast_sub hp]; push_cast; ring,
      Real.rpow_natCast]
  have h3 : realFactorial ((p : ℝ) + 1 - 1) = (p ! : ℝ) := by
    rw [add_sub_cancel_right, realFactorial_natCast]
  have h4 : ‖s‖ ^ ((p : ℝ) + 1 - 1) = ‖s‖ ^ p := by
    rw [add_sub_cancel_right, Real.rpow_natCast]
  rw [h1, h2, h3, h4] at h
  calc ‖fderiv ℝ f (x + s)‖ ≤ L / (p ! : ℝ) * ‖s‖ ^ p + σ / (p ! : ℝ) * ‖s‖ ^ p +
        ‖fderiv ℝ (regularizedModel (ftaylorSeries ℝ f x) p σ) s‖ := h
    _ = _ := by ring

/-- **Step bound, second order** ([cartis2022evaluation], (4.1.27)–(4.1.29), Lemma 3.3.8): for
`p ≥ 2`, `σ ≥ 0` and the hypotheses of `Optimization.norm_fderiv_le_of_regularizedModel`,
`λ_min[∇²f(x + s)] ≥ λ_min[∇²m(s)] - (L + σ)/(p-1)! ‖s‖^{p-1}`. -/
theorem minCurvature_ge_of_regularizedModel (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hp : 2 ≤ p) (hL : IteratedFDerivLipschitzOn f p L C)
    (hx : x ∈ C) (hxs : x + s ∈ C) (hσ : 0 ≤ σ) :
    minCurvature (iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ f x) p σ) s) -
        (L + σ) / ((p - 1)! : ℝ) * ‖s‖ ^ (p - 1) ≤
      minCurvature (iteratedFDeriv ℝ 2 f (x + s)) := by
  have hp' : (2 : ℝ) ≤ (p : ℝ) + 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have h := minCurvature_ge_of_powRegularizedModel hC hf hp zero_le_one hL.holderOn hx hxs hσ hp'
  rw [← regularizedModel_eq_powRegularizedModel] at h
  have hc : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  have h1 : holderFactorial (p - 2) 1 = ((p - 1)! : ℝ) := by
    rw [holderFactorial_one_right]; congr 2; omega
  have h2 : ‖s‖ ^ (((p - 2 : ℕ) : ℝ) + 1) = ‖s‖ ^ (p - 1) := by
    rw [show ((p - 2 : ℕ) : ℝ) + 1 = ((p - 1 : ℕ) : ℝ) by
      rw [Nat.cast_sub hp, hc]; push_cast; ring, Real.rpow_natCast]
  have h3 : realFactorial ((p : ℝ) + 1 - 2) = ((p - 1)! : ℝ) := by
    rw [show (p : ℝ) + 1 - 2 = ((p - 1 : ℕ) : ℝ) by rw [hc]; ring, realFactorial_natCast]
  have h4 : ‖s‖ ^ ((p : ℝ) + 1 - 2) = ‖s‖ ^ (p - 1) := by
    rw [show (p : ℝ) + 1 - 2 = ((p - 1 : ℕ) : ℝ) by rw [hc]; ring, Real.rpow_natCast]
  rw [h1, h2, h3, h4] at h
  have : (L + σ) / ((p - 1)! : ℝ) * ‖s‖ ^ (p - 1) =
      L / ((p - 1)! : ℝ) * ‖s‖ ^ (p - 1) + σ / ((p - 1)! : ℝ) * ‖s‖ ^ (p - 1) := by ring
  linarith

/-- **Model-versus-function derivatives, anchored** ([cartis2022evaluation], (4.1.30)): as
`abs_iteratedFDeriv_apply_le_of_regularizedModel`, with `∇^p f` only Lipschitz anchored at `x`:
`‖∇^p f(y) - ∇^p f(x)‖ ≤ L ‖y - x‖` for `y ∈ C`. -/
theorem abs_iteratedFDeriv_apply_le_of_regularizedModel_anchored (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y)
    (hL : ∀ y ∈ C, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f x‖ ≤ L * ‖y - x‖)
    (hx : x ∈ C) (hxs : x + s ∈ C) (hσ : 0 ≤ σ) {j : ℕ} (hj : j ≤ p) (d : E) :
    |iteratedFDeriv ℝ j f (x + s) (fun _ => d) -
        iteratedFDeriv ℝ j (regularizedModel (ftaylorSeries ℝ f x) p σ) s (fun _ => d)| ≤
      (L + σ) / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) * ‖d‖ ^ j := by
  rw [iteratedFDeriv_regularizedModel (Or.inl hj)]
  have hT := norm_iteratedFDeriv_sub_taylorPolynomial_le_of_lipschitzAnchored hC hf hL hx hxs hj
  set A := iteratedFDeriv ℝ j f (x + s)
  set T := iteratedFDeriv ℝ j ((ftaylorSeries ℝ f x).taylorSum p) s
  set N := iteratedFDeriv ℝ j (fun y : E => ‖y‖ ^ (p + 1)) s
  have hN := abs_iteratedFDeriv_norm_pow_apply_le (r := p + 1) (ℓ := j) (by omega)
    (s := s) (Or.inr (by omega)) d
  have hfac : (p + 1 - j) = p - j + 1 := by omega
  rw [hfac] at hN
  have hAT : |(A - T) (fun _ => d)| ≤ ‖A - T‖ * ‖d‖ ^ j := by
    rw [← Real.norm_eq_abs]
    refine ((A - T).le_opNorm _).trans_eq ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsplit : A (fun _ => d) - (T + (σ / ((p + 1)! : ℝ)) • N) (fun _ => d) =
      (A - T) (fun _ => d) - σ / ((p + 1)! : ℝ) * N (fun _ => d) := by
    simp only [sub_apply, add_apply, smul_apply, smul_eq_mul]
    ring
  rw [hsplit]
  have hc : 0 ≤ σ / ((p + 1)! : ℝ) := by positivity
  calc |(A - T) (fun _ => d) - σ / ((p + 1)! : ℝ) * N (fun _ => d)|
      ≤ |(A - T) (fun _ => d)| + σ / ((p + 1)! : ℝ) * |N (fun _ => d)| := by
        refine (abs_sub _ _).trans_eq ?_
        rw [abs_mul, abs_of_nonneg hc]
    _ ≤ L / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) * ‖d‖ ^ j +
          σ / ((p + 1)! : ℝ) *
            (((p + 1)! : ℝ) / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) * ‖d‖ ^ j) := by
        exact add_le_add (hAT.trans (mul_le_mul_of_nonneg_right hT (by positivity)))
          (mul_le_mul_of_nonneg_left hN hc)
    _ = (L + σ) / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) * ‖d‖ ^ j := by
        field_simp

/-- **Model-versus-function derivatives** ([cartis2022evaluation], (4.1.30), (6.2.20)–(6.2.23)):
for `j ≤ p`, `σ ≥ 0` and `f` `C^p` on a convex `C ∋ x, x + s` with `L`-Lipschitz `∇^p f` there,
`|∇^j f(x + s)[d]^j - ∇^j m(s)[d]^j| ≤ (L + σ)/(p - j + 1)! ‖s‖^{p-j+1} ‖d‖^j` for every `d`
(using the diagonal bound of Lemma B.4.1 for `‖·‖^{p+1}`, which holds for natural exponents). -/
theorem abs_iteratedFDeriv_apply_le_of_regularizedModel (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hL : IteratedFDerivLipschitzOn f p L C)
    (hx : x ∈ C) (hxs : x + s ∈ C) (hσ : 0 ≤ σ) {j : ℕ} (hj : j ≤ p) (d : E) :
    |iteratedFDeriv ℝ j f (x + s) (fun _ => d) -
        iteratedFDeriv ℝ j (regularizedModel (ftaylorSeries ℝ f x) p σ) s (fun _ => d)| ≤
      (L + σ) / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) * ‖d‖ ^ j :=
  abs_iteratedFDeriv_apply_le_of_regularizedModel_anchored hC hf
    (fun y hy => iteratedFDerivLipschitzOn_iff.1 hL y hy x hx) hx hxs hσ hj d

end Estimates

section Existence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {D : FormalMultilinearSeries ℝ E ℝ} {p : ℕ} {σ : ℝ}

/-- **Global minimizers of the model** ([cartis2022evaluation], Sections 3.3.1, 4.1.1): in finite
dimension, for `σ > 0` and `p ≥ 1`, the model (bounded below because the regularization term
dominates) has a global minimizer `s*`, at which `∇m(s*) = 0`, `λ_min[∇²m(s*)] ≥ 0`, and
`m(s*) < m(0)` unless `0` is itself a global minimizer. -/
theorem exists_isMinOn_regularizedModel [FiniteDimensional ℝ E] (hσ : 0 < σ) (hp : 1 ≤ p) :
    ∃ s, IsMinOn (regularizedModel D p σ) univ s ∧
      fderiv ℝ (regularizedModel D p σ) s = 0 ∧
      0 ≤ minCurvature (iteratedFDeriv ℝ 2 (regularizedModel D p σ) s) ∧
      (¬ IsMinOn (regularizedModel D p σ) univ 0 →
        regularizedModel D p σ s < regularizedModel D p σ 0) := by
  have h1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  obtain ⟨s, hmin, hd, hc, hlt⟩ := exists_isMinOn_powRegularizedModel (D := D) (p := p)
    (σ := σ) (r := (p : ℝ) + 1) hσ (by linarith) (by linarith)
  rw [← regularizedModel_eq_powRegularizedModel] at hmin hd hc hlt
  exact ⟨s, hmin, hd, hc (by linarith), hlt⟩

/-- A model whose gradient at `0` is nonzero is decreased by any global minimizer. -/
theorem regularizedModel_lt_of_isMinOn_of_fderiv_ne_zero {s : E}
    (hmin : IsMinOn (regularizedModel D p σ) univ s)
    (h0 : fderiv ℝ (regularizedModel D p σ) 0 ≠ 0) :
    regularizedModel D p σ s < regularizedModel D p σ 0 := by
  refine lt_of_le_of_ne (hmin (mem_univ 0)) fun heq => h0 ?_
  refine IsLocalMin.fderiv_eq_zero (IsMinOn.isLocalMin (fun y _ => ?_) univ_mem)
  rw [← heq]
  exact hmin (mem_univ y)

/-- A model with negative curvature at `0` is decreased by any global minimizer (for `p ≥ 2`, so
that the model is `C²`). -/
theorem regularizedModel_lt_of_isMinOn_of_minCurvature_neg {s : E} (hp : 2 ≤ p)
    (hmin : IsMinOn (regularizedModel D p σ) univ s)
    (h0 : minCurvature (iteratedFDeriv ℝ 2 (regularizedModel D p σ) 0) < 0) :
    regularizedModel D p σ s < regularizedModel D p σ 0 := by
  refine lt_of_le_of_ne (hmin (mem_univ 0)) fun heq => ?_
  have hmin0 : IsMinOn (regularizedModel D p σ) univ 0 := fun y _ => by
    rw [← heq]; exact hmin (mem_univ y)
  exact (not_le.2 h0) (IsLocalMin.minCurvature_iteratedFDeriv_two_nonneg
    (hmin0.isLocalMin univ_mem)
    ((contDiff_regularizedModel (D := D) (σ := σ)).contDiffAt.of_le (by exact_mod_cast hp)))

end Existence

section Cubic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **The AR2 model is the cubic regularization model** ([cartis2022evaluation], (3.3.1),
Theorem 8.2.8): for `f` `C²` at `x`,
`m(s) = T_{f,2}(x, s) + σ/6 ‖s‖³ = f(x) + Subproblem.regModel (∇f(x)) (∇²f(x)) (σ/2) 3 s`
(`regModel`'s regularization is `σ'/r ‖s‖^r`, here `σ' = σ/2`, `r = 3`). This transfers the
characterization of global minimizers (`Subproblem.isMinOn_regModel_iff`) to AR2 steps. -/
theorem regularizedModel_two_eq_regModel {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (σ : ℝ)
    (s : E) :
    regularizedModel (ftaylorSeries ℝ f x) 2 σ s =
      f x + Subproblem.regModel (gradient f x) (hessianOperator f x) (σ / 2) 3 s := by
  rw [regularizedModel_def, ← taylorPolynomial_eq_taylorSum,
    taylorPolynomial_two_eq_quadModel hf, Subproblem.regModel_def,
    show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num [Nat.factorial]
  ring

end Cubic

end Optimization
