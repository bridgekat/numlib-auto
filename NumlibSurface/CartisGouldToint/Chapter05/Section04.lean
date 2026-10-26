import NumlibSurface.CartisGouldToint.Chapter03.Section03
import Numlib.Optimization.Complexity.GapRecurrence

/-!
# Cartis–Gould–Toint §5.4: Phase complexity under strict local convexity

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §5.4. The second-order
adaptive-regularization algorithm AR2 (`Chapter03.algorithm_3_3_1`, first-order version
`ε₂ = +∞`) is run with the more stringent model-termination test (5.4.3)
`‖∇m_k(s_k)‖ ≤ θ₁ min(‖∇f(x_k)‖, ½ ‖s_k‖²)` (`IsAR2StrictRun`). Near a local minimizer `x_*`
with `λ_* = λ_min[∇²f(x_*)] > 0` the gradient then converges `Q`-quadratically, which gives a
`log₂ log₂` local iteration count and an additive global bound.

Notation: `L = L_{f,2}` (f.HL, `Chapter03.AssumptionHL f L`), `q_* = λ_*/(4L)` (5.4.1),
`σ_max = Chapter03.sigmaMaxAR2 P L` (3.3.14), `κ_s = kappaStep P λ_* = 2(1 + θ₁)/λ_*`,
`ζ_* = zetaStar P L λ_*` (5.4.5) and `𝒬_*¹ = quadRegion f P L x_*` (5.4.6).

## Main definitions

* `IsAR2StrictRun f P ε₁ x s σ`: AR2 with the model-termination test (5.4.3);
  `exists_isAR2StrictRun`.
* `kappaStep`, `zetaStar`, `quadRegion`: the constants and the region of Lemma 5.4.2.

## Main results

* `lemma_5_4_1`: `λ_min[∇²f(x)] ≥ λ_*/2` on `𝒬_* = {x | ‖x - x_*‖ ≤ q_*}`.
* `lemma_5_4_2`: quadratic decrease of the gradient (5.4.4) and invariance of `𝒬_*¹`, along which
  every iteration is very successful.
* `lemma_5_4_3`: termination within `⌈log₂ log₂(ζ_*/ε)⌉` (successful) iterations once in `𝒬_*¹`.
* `theorem_5_4_4`: the global bounds (5.4.16)–(5.4.17).

## Fixes with respect to the book

* **Lemma 5.4.2, step bound (5.4.8).** The book proves
  `‖s_k‖ ≤ (1 + θ₁)/(λ_* + σ_min/2) ‖∇f(x_k)‖` from
  `(λ_* + σ_min/2) ‖s_k‖² ≤ ⟨s_k, (∇²f(x_k) + σ_k/2 I) s_k⟩`, which uses
  `λ_min[∇²f(x_k)] ≥ λ_*` (only `λ_*/2` is available on `𝒬_*`, (5.4.7)) and drops the factor
  `‖s_k‖` of the regularization term of the model gradient `∇f(x_k) + ∇²f(x_k) s_k +
  σ_k/2 ‖s_k‖ s_k` (3.3.2). The printed constant is false (e.g. `θ₁ < 1`, `σ_min → 0`,
  `∇²f(x_k) = (λ_*/2) I` and an exact model minimizer, for which `‖s_k‖ ≈ 2‖∇f(x_k)‖/λ_*`). The
  correct constant is `κ_s = 2(1 + θ₁)/λ_*` (`norm_step_le_of_strict`); accordingly every factor
  `(λ_* + σ_min/2)/(1 + θ₁)` of (5.4.5) is `1/κ_s` in `zetaStar`, and the last term of (5.4.5),
  `λ_*/(4 max(θ₁ - σ_min, 0)) · 1/κ_s`, is absent when `θ₁ ≤ σ_min`.
* **Lemma 5.4.3, count (5.4.14).** `log₂ log₂(ζ/ε)` is too small by one in the worst case
  (`‖∇f(x_{k₀})‖ = ζ = ζ_*/2`, `‖∇f(x_{k+1})‖ = ‖∇f(x_k)‖²/ζ_*`, `ε = ζ 2^{-2^m}` needs `m + 1`
  steps), lacks a ceiling and is undefined for `ε ≥ ζ`; the count here is
  `⌈log₂ log₂(ζ_*/ε)⌉₊`, also in Theorem 5.4.4.
* The neighbourhood statements only use `∇f(x_*) = 0` and `λ_* > 0` (Lemma 5.4.1 uses neither);
  the strong-convexity argument for `x_{k+1} ∈ 𝒬_*` is replaced by the first-order Taylor bound
  `⟨∇f(y), y - x_*⟩ ≥ ¾ λ_* ‖y - x_*‖²` for `‖y - x_*‖ ≤ 2q_*`
  (`mul_norm_sub_le_norm_gradient`).
* Theorem 5.4.4 (ii) is stated, like Lemma 3.3.4, as a bound on `|𝒮_k|` for every iteration `k`
  before termination, under (5.4.18) restricted to iterations before termination.
-/

open Set Finset Optimization Subproblem
open Optimization hiding ARParams
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter05

open Chapter03

variable {n : ℕ}

/-! ### The AR2 model in inner-product form -/

section Model

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}

@[deprecated Chapter03.hasFDerivAt_ar2Model (since := "2026-10-26")]
alias hasFDerivAt_ar2Model := Chapter03.hasFDerivAt_ar2Model

@[deprecated Chapter03.norm_fderiv_ar2Model (since := "2026-10-26")]
alias norm_fderiv_ar2Model := Chapter03.norm_fderiv_ar2Model

@[deprecated Chapter03.taylorDecrement_two_eq (since := "2026-10-26")]
alias taylorDecrement_two_eq := Chapter03.taylorDecrement_two_eq

@[deprecated Chapter03.sub_taylorDecrement_eq (since := "2026-10-26")]
alias sub_taylorDecrement_eq := Chapter03.sub_taylorDecrement_eq

@[deprecated Chapter03.hessianMinEig_mul_le_inner (since := "2026-10-26")]
alias hessianMinEig_mul_le_inner := Chapter03.hessianMinEig_mul_le_inner

@[deprecated Chapter03.inner_ar2ModelGrad_self (since := "2026-10-26")]
alias inner_ar2ModelGrad_self := Chapter03.inner_ar2ModelGrad_self

/-- **The step bound (5.4.8), corrected** ([cartis2022evaluation], Lemma 5.4.2): if
`λ_min[∇²f(x)] ≥ μ > 0`, `σ ≥ 0` and the step satisfies `‖∇m(s)‖ ≤ θ ‖∇f(x)‖` (part of (5.4.3)),
then `‖s‖ ≤ (1 + θ)/μ ‖∇f(x)‖` (`θ ≥ 0`). With `μ = λ_*/2` this is `κ_s = 2(1 + θ₁)/λ_*`. -/
theorem norm_step_le_of_strict (hf : ContDiffAt ℝ 2 f x) {σ μ θ : ℝ} (hσ : 0 ≤ σ) (hθ : 0 ≤ θ)
    (hμ : 0 < μ)
    (hH : μ ≤ Chapter01.hessianMinEig f x) {s : EuclideanSpace ℝ (Fin n)}
    (hm : ‖fderiv ℝ (ar2Model f x σ) s‖ ≤ θ * ‖gradient f x‖) :
    ‖s‖ ≤ (1 + θ) / μ * ‖gradient f x‖ := by
  set v := gradient f x + hessianOperator f x s + (σ / 2 * ‖s‖) • s
  rw [Chapter03.norm_fderiv_ar2Model hf] at hm
  have hv := Chapter03.inner_ar2ModelGrad_self (f := f) (x := x) σ s
  have hcurv := Chapter03.hessianMinEig_mul_le_inner hf s
  have h1 : ⟪v, s⟫ ≤ ‖v‖ * ‖s‖ := real_inner_le_norm _ _
  have h2 : -⟪gradient f x, s⟫ ≤ ‖gradient f x‖ * ‖s‖ := by
    have := abs_real_inner_le_norm (gradient f x) s
    linarith [neg_abs_le ⟪gradient f x, s⟫]
  have h3 : 0 ≤ σ / 2 * ‖s‖ ^ 3 := by positivity
  have h4 : μ * ‖s‖ ^ 2 ≤ Chapter01.hessianMinEig f x * ‖s‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hH (sq_nonneg _)
  -- `μ ‖s‖² ≤ (1 + θ) ‖∇f(x)‖ ‖s‖`
  have key : μ * ‖s‖ ^ 2 ≤ (1 + θ) * ‖gradient f x‖ * ‖s‖ := by
    have : ‖v‖ * ‖s‖ ≤ θ * ‖gradient f x‖ * ‖s‖ :=
      mul_le_mul_of_nonneg_right hm (norm_nonneg _)
    nlinarith
  rcases (norm_nonneg s).eq_or_lt with h0 | hpos
  · rw [← h0]; have := norm_nonneg (gradient f x); positivity
  · rw [div_mul_eq_mul_div, le_div_iff₀ hμ]
    nlinarith

/-- **The model decrease (5.4.10)** ([cartis2022evaluation], proof of Lemma 5.4.2): if
`λ_min[∇²f(x)] ≥ μ` and `‖∇m(s)‖ ≤ θ/2 ‖s‖²` ((3.3.5), implied by (5.4.3)), then
`T_{f,2}(x, 0) - T_{f,2}(x, s) ≥ μ/2 ‖s‖² + (σ - θ)/2 ‖s‖³`. -/
theorem taylorDecrement_ge_of_ar2Model (hf : ContDiffAt ℝ 2 f x) {σ μ θ : ℝ}
    (hH : μ ≤ Chapter01.hessianMinEig f x) {s : EuclideanSpace ℝ (Fin n)}
    (hm : ‖fderiv ℝ (ar2Model f x σ) s‖ ≤ θ / 2 * ‖s‖ ^ 2) :
    μ / 2 * ‖s‖ ^ 2 + (σ - θ) / 2 * ‖s‖ ^ 3 ≤ (ftaylorSeries ℝ f x).taylorDecrement 2 s := by
  set v := gradient f x + hessianOperator f x s + (σ / 2 * ‖s‖) • s
  rw [Chapter03.norm_fderiv_ar2Model hf] at hm
  rw [Chapter03.taylorDecrement_two_eq hf]
  have hv := Chapter03.inner_ar2ModelGrad_self (f := f) (x := x) σ s
  have hcurv := Chapter03.hessianMinEig_mul_le_inner hf s
  have h1 : ⟪v, s⟫ ≤ ‖v‖ * ‖s‖ := real_inner_le_norm _ _
  have h2 : ‖v‖ * ‖s‖ ≤ θ / 2 * ‖s‖ ^ 2 * ‖s‖ := mul_le_mul_of_nonneg_right hm (norm_nonneg _)
  have h4 : μ * ‖s‖ ^ 2 ≤ Chapter01.hessianMinEig f x * ‖s‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hH (sq_nonneg _)
  have h5 : θ / 2 * ‖s‖ ^ 2 * ‖s‖ = θ / 2 * ‖s‖ ^ 3 := by ring
  linarith

end Model

/-! ### Lemma 5.4.1 -/

section Convexity

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ}

/-- The eigenvalue perturbation bound under f.HL ((A.5)):
`λ_min[∇²f(y)] ≥ λ_min[∇²f(x)] - L ‖y - x‖`. -/
theorem hessianMinEig_sub_le (hf : AssumptionHL f L) (x y : EuclideanSpace ℝ (Fin n)) :
    Chapter01.hessianMinEig f x - L * ‖y - x‖ ≤ Chapter01.hessianMinEig f y := by
  have h1 := abs_minCurvature_sub_le (A := iteratedFDeriv ℝ 2 f x) (B := iteratedFDeriv ℝ 2 f y)
  have h2 := hf.lipschitz x y
  rw [norm_sub_rev x y] at h2
  have := (le_abs_self _).trans (h1.trans h2)
  unfold Chapter01.hessianMinEig
  linarith

/-- **Lemma 5.4.1** of [cartis2022evaluation] (region of local strong convexity). Under f.HL, on
`𝒬_* = {x | ‖x - x_*‖ ≤ q_*}`, `q_* = λ_*/(4L)` (5.4.1), with `λ_* = λ_min[∇²f(x_*)]`:
`λ_min[∇²f(x)] ≥ λ_*/2`. (The book assumes `x_*` to be a local minimizer with `λ_* > 0`; the
bound holds for any `x_*`, `𝒬_*` being empty if `λ_* < 0`.) -/
theorem lemma_5_4_1 (hf : AssumptionHL f L) {xs x : EuclideanSpace ℝ (Fin n)}
    (hx : ‖x - xs‖ ≤ Chapter01.hessianMinEig f xs / (4 * L)) :
    Chapter01.hessianMinEig f xs / 2 ≤ Chapter01.hessianMinEig f x := by
  have hL := hf.pos
  have h := hessianMinEig_sub_le hf xs x
  have h' : L * ‖x - xs‖ ≤ Chapter01.hessianMinEig f xs / 4 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * L)] at hx
    linarith
  have h0 : 0 ≤ Chapter01.hessianMinEig f xs := by
    have := mul_nonneg hL.le (norm_nonneg (x - xs)); linarith
  linarith

/-- **The gradient near a nondegenerate critical point** (replacing the strong-convexity
argument in the proof of Lemma 5.4.2 of [cartis2022evaluation]): under f.HL, if `∇f(x_*) = 0` and
`‖y - x_*‖ ≤ 2 q_* = λ_*/(2L)`, then `¾ λ_* ‖y - x_*‖ ≤ ‖∇f(y)‖`. -/
theorem mul_norm_sub_le_norm_gradient (hf : AssumptionHL f L) {xs y : EuclideanSpace ℝ (Fin n)}
    (hcrit : gradient f xs = 0)
    (hy : ‖y - xs‖ ≤ Chapter01.hessianMinEig f xs / (2 * L)) :
    3 / 4 * Chapter01.hessianMinEig f xs * ‖y - xs‖ ≤ ‖gradient f y‖ := by
  set d := y - xs
  set lam := Chapter01.hessianMinEig f xs
  have hL := hf.pos
  have hyd : y = xs + d := by simp [d]
  have hc := hf.contDiffAt xs
  -- the first-order Taylor error of the gradient
  have hT := norm_iteratedFDeriv_sub_taylorPolynomial_le_of_lipschitz convex_univ
    (fun z _ => hf.contDiffAt z) hf.iteratedFDerivLipschitzOn (mem_univ xs) (mem_univ (xs + d))
    (j := 1) (by norm_num)
  rw [norm_iteratedFDeriv_one_sub] at hT
  norm_num [Nat.factorial] at hT
  -- the derivative of the Taylor polynomial
  have hTd : HasFDerivAt (taylorPolynomial f 2 xs)
      (innerSL ℝ (gradient f xs + hessianOperator f xs d)) d := by
    have heq : taylorPolynomial f 2 xs =
        fun s => f xs + quadModel (gradient f xs) (hessianOperator f xs) s := by
      funext s; exact taylorPolynomial_two_eq_quadModel hc s
    rw [heq]
    exact (hasFDerivAt_quadModel (hessianOperator_isSymmetric hc) d).const_add _
  rw [hTd.fderiv] at hT
  have happ : fderiv ℝ f (xs + d) d ≥
      ⟪gradient f xs + hessianOperator f xs d, d⟫ - L / 2 * ‖d‖ ^ 2 * ‖d‖ := by
    have h1 :=
      (fderiv ℝ f (xs + d) - innerSL ℝ (gradient f xs + hessianOperator f xs d)).le_opNorm d
    have h2 : |(fderiv ℝ f (xs + d) - innerSL ℝ (gradient f xs + hessianOperator f xs d)) d| ≤
        L / 2 * ‖d‖ ^ 2 * ‖d‖ :=
      (Real.norm_eq_abs _ ▸ h1).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
    rw [sub_apply, innerSL_apply_apply] at h2
    linarith [neg_abs_le (fderiv ℝ f (xs + d) d - ⟪gradient f xs + hessianOperator f xs d, d⟫)]
  rw [hcrit, zero_add, real_inner_comm] at happ
  have hcurv := Chapter03.hessianMinEig_mul_le_inner hc d
  have hup : fderiv ℝ f (xs + d) d ≤ ‖gradient f y‖ * ‖d‖ := by
    rw [← hyd, norm_gradient_eq]
    exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ (fderiv ℝ f y).le_opNorm d)
  have hLd : L / 2 * ‖d‖ ≤ lam / 4 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * L)] at hy
    linarith
  have key : 3 / 4 * lam * ‖d‖ ^ 2 ≤ ‖gradient f y‖ * ‖d‖ := by
    have : L / 2 * ‖d‖ ^ 2 * ‖d‖ ≤ lam / 4 * ‖d‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_right hLd (sq_nonneg ‖d‖)
      nlinarith [norm_nonneg d]
    linarith
  rcases (norm_nonneg d).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; exact norm_nonneg _
  · nlinarith

end Convexity

/-! ### The constants of Lemma 5.4.2 -/

section Constants

/-- The step-bound constant `κ_s = 2(1 + θ₁)/λ_*` of (5.4.8), corrected
(`norm_step_le_of_strict` with `μ = λ_*/2`; the book prints `(1 + θ₁)/(λ_* + σ_min/2)`). -/
noncomputable def kappaStep (P : AR2Params) (lam : ℝ) : ℝ := 2 * (1 + P.θ₁) / lam

theorem kappaStep_pos (P : AR2Params) {lam : ℝ} (hlam : 0 < lam) : 0 < kappaStep P lam := by
  have := P.θ₁_pos; unfold kappaStep; positivity

/-- The first four terms of the radius (5.4.5), corrected (factors `1/κ_s`):
`min [2/((L + θ₁ + σ_max) κ_s²), λ_*/(4L κ_s), λ_*²/(16 L), 3(1 - η₂)λ_*/(4L κ_s)]`. -/
noncomputable def zetaStarBase (P : AR2Params) (L lam : ℝ) : ℝ :=
  min (2 / ((L + P.θ₁ + sigmaMaxAR2 P L) * kappaStep P lam ^ 2))
    (min (lam / (4 * L * kappaStep P lam))
      (min (lam ^ 2 / (16 * L)) (3 * (1 - P.η₂) * lam / (4 * L * kappaStep P lam))))

/-- **The radius `ζ_*` of quadratic convergence** ([cartis2022evaluation], (5.4.5), corrected):
`zetaStarBase P L λ_*`, further `min`-ed with `λ_*/(4(θ₁ - σ_min) κ_s)` when `σ_min < θ₁` (the
book's last term `λ_*/(4 max(θ₁ - σ_min, 0)) · …` is absent when `θ₁ ≤ σ_min`). -/
noncomputable def zetaStar (P : AR2Params) (L lam : ℝ) : ℝ :=
  if P.σmin < P.θ₁ then
    min (zetaStarBase P L lam) (lam / (4 * (P.θ₁ - P.σmin) * kappaStep P lam))
  else zetaStarBase P L lam

variable {P : AR2Params} {L lam : ℝ}

theorem zetaStar_le_base : zetaStar P L lam ≤ zetaStarBase P L lam := by
  unfold zetaStar; split_ifs <;> simp

theorem zetaStar_pos (hL : 0 < L) (hlam : 0 < lam) : 0 < zetaStar P L lam := by
  have hκ := kappaStep_pos P hlam
  have := P.θ₁_pos; have := arSigmaMax_pos P.ar L; have := P.ar.one_sub_η₂_pos
  have hb : 0 < zetaStarBase P L lam := by
    unfold zetaStarBase
    have : 0 < L + P.θ₁ + sigmaMaxAR2 P L := by linarith
    refine lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) ?_))
    have : 0 < 1 - P.η₂ := P.ar.one_sub_η₂_pos
    positivity
  unfold zetaStar
  split_ifs with h
  · exact lt_min hb (by have : 0 < P.θ₁ - P.σmin := sub_pos.2 h; positivity)
  · exact hb

/-- `ζ_* (L + θ₁ + σ_max) κ_s² ≤ 2` (first term of (5.4.5)). -/
theorem zetaStar_mul_le_newton (hL : 0 < L) (hlam : 0 < lam) :
    zetaStar P L lam * ((L + P.θ₁ + sigmaMaxAR2 P L) * kappaStep P lam ^ 2) ≤ 2 := by
  have hκ := kappaStep_pos P hlam
  have := P.θ₁_pos; have := arSigmaMax_pos P.ar L
  have hC : 0 < (L + P.θ₁ + sigmaMaxAR2 P L) * kappaStep P lam ^ 2 := by
    have : 0 < L + P.θ₁ + sigmaMaxAR2 P L := by linarith
    positivity
  rw [← le_div_iff₀ hC]
  exact zetaStar_le_base.trans (min_le_left _ _)

/-- `κ_s ζ_* ≤ λ_*/(4L) = q_*` (second term of (5.4.5)). -/
theorem kappaStep_mul_zetaStar_le_region (hL : 0 < L) (hlam : 0 < lam) :
    kappaStep P lam * zetaStar P L lam ≤ lam / (4 * L) := by
  have hκ := kappaStep_pos P hlam
  have h : zetaStar P L lam ≤ lam / (4 * L * kappaStep P lam) :=
    zetaStar_le_base.trans ((min_le_right _ _).trans (min_le_left _ _))
  rw [le_div_iff₀ (by positivity)] at h
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- `ζ_* ≤ λ_*²/(16 L)` (third term of (5.4.5)). -/
theorem zetaStar_le_sq : zetaStar P L lam ≤ lam ^ 2 / (16 * L) :=
  zetaStar_le_base.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))

/-- `κ_s ζ_* ≤ 3(1 - η₂)λ_*/(4L)` (fourth term of (5.4.5)). -/
theorem kappaStep_mul_zetaStar_le_ratio (hL : 0 < L) (hlam : 0 < lam) :
    kappaStep P lam * zetaStar P L lam ≤ 3 * (1 - P.η₂) * lam / (4 * L) := by
  have hκ := kappaStep_pos P hlam
  have h : zetaStar P L lam ≤ 3 * (1 - P.η₂) * lam / (4 * L * kappaStep P lam) :=
    zetaStar_le_base.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _)))
  rw [le_div_iff₀ (by positivity)] at h
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- `κ_s ζ_* ≤ λ_*/(4(θ₁ - σ_min))` when `σ_min < θ₁` (last term of (5.4.5)). -/
theorem kappaStep_mul_zetaStar_le_reg (hlam : 0 < lam) (h : P.σmin < P.θ₁) :
    kappaStep P lam * zetaStar P L lam ≤ lam / (4 * (P.θ₁ - P.σmin)) := by
  have hκ := kappaStep_pos P hlam
  have hθ : 0 < P.θ₁ - P.σmin := sub_pos.2 h
  have h' : zetaStar P L lam ≤ lam / (4 * (P.θ₁ - P.σmin) * kappaStep P lam) := by
    unfold zetaStar; simp only [h, ↓reduceIte]; exact min_le_right _ _
  rw [le_div_iff₀ (by positivity)] at h'
  rw [le_div_iff₀ (by positivity)]
  linarith

end Constants

/-- The neighbourhood `𝒬_*¹ = 𝒬_* ∩ {x | ‖∇f(x)‖ ≤ ζ_*}` of (5.4.6) ([cartis2022evaluation]),
with `𝒬_* = {x | ‖x - x_*‖ ≤ λ_*/(4L)}` (5.4.1), `λ_* = λ_min[∇²f(x_*)]`. -/
def quadRegion (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : AR2Params) (L : ℝ)
    (xs : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ‖x - xs‖ ≤ Chapter01.hessianMinEig f xs / (4 * L) ∧
    ‖gradient f x‖ ≤ zetaStar P L (Chapter01.hessianMinEig f xs)}

theorem mem_quadRegion {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : AR2Params} {L : ℝ}
    {xs x : EuclideanSpace ℝ (Fin n)} :
    x ∈ quadRegion f P L xs ↔ ‖x - xs‖ ≤ Chapter01.hessianMinEig f xs / (4 * L) ∧
      ‖gradient f x‖ ≤ zetaStar P L (Chapter01.hessianMinEig f xs) :=
  Iff.rfl

/-! ### AR2 with the model-termination test (5.4.3) -/

/-- AR2 (`Chapter03.algorithm_3_3_1`, first-order version `ε₂ = +∞`) with the more stringent
model-termination test (5.4.3) of [cartis2022evaluation]: besides (3.3.5)
`‖∇m_k(s_k)‖ ≤ θ₁/2 ‖s_k‖²`, every step computed before termination satisfies
`‖∇m_k(s_k)‖ ≤ θ₁ ‖∇f(x_k)‖`; together, `‖∇m_k(s_k)‖ ≤ θ₁ min(‖∇f(x_k)‖, ½ ‖s_k‖²)`. -/
structure IsAR2StrictRun (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : AR2Params) (ε₁ : ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ) : Prop where
  /-- The run is an AR2 run. -/
  toAlgorithm_3_3_1 : algorithm_3_3_1 f P ε₁ none x s σ
  /-- The additional part `‖∇m_k(s_k)‖ ≤ θ₁ ‖∇f(x_k)‖` of (5.4.3). -/
  strict : ∀ k, (∀ j ≤ k, ¬ stopTest f ε₁ none (x j)) →
    ‖fderiv ℝ (ar2Model f (x k) (σ k)) (s k)‖ ≤ P.θ₁ * ‖gradient f (x k)‖

/-- **Existence of AR2 runs with the test (5.4.3)**: for a `C²` function, every `ε₁ ∈ (0, 1]` and
every starting point there is such a run (global model minimizers have `∇m_k(s_k) = 0`). -/
theorem exists_isAR2StrictRun {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 2 f)
    (P : AR2Params) {ε₁ : ℝ} (hε₁ : 0 < ε₁) (hε₁1 : ε₁ ≤ 1) (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ x s σ, x 0 = x₀ ∧ IsAR2StrictRun f P ε₁ x s σ := by
  obtain ⟨x, s, σ, hx0, hrun, -⟩ := exists_isARRun P.ar (Inv := fun _ => True)
    (test := stopTest f ε₁ none)
    (stepOK := fun y σ s => ar2Step f P none y σ s ∧
      ‖fderiv ℝ (ar2Model f y σ) s‖ ≤ P.θ₁ * ‖gradient f y‖)
    (fun y _ t => reductionRatio f y t ((ftaylorSeries ℝ f y).taylorDecrement 2 t))
    (fun y σ _ _ hσ hnot => by
      obtain ⟨s, hmin, hd, -, -⟩ := exists_isMinOn_regularizedModel
        (D := ftaylorSeries ℝ f y) (p := 2) hσ (by norm_num)
      have hg : gradient f y ≠ 0 := by
        intro h0
        exact hnot (stopTest_none.2 (by rw [h0, norm_zero]; exact hε₁.le))
      have hdec : ar2Model f y σ s < ar2Model f y σ 0 := by
        refine regularizedModel_lt_of_isMinOn_of_fderiv_ne_zero hmin ?_
        rw [fderiv_regularizedModel_ftaylorSeries_zero hf.contDiffAt (by norm_num)]
        intro h0
        exact hg (by rw [← norm_eq_zero, norm_gradient_eq, h0, norm_zero])
      refine ⟨s, ⟨ar2Step_of_isMinOn P none hmin hdec, ?_⟩, trivial⟩
      change ‖fderiv ℝ (regularizedModel (ftaylorSeries ℝ f y) 2 σ) s‖ ≤ _
      rw [hd, norm_zero]
      have := P.θ₁_pos
      positivity) trivial
  refine ⟨x, s, σ, hx0, ⟨⟨hε₁, hε₁1, (fun e he => by cases he), hrun.mono fun _ h => h.1⟩,
    fun k hk => (hrun.step_of_forall_le (IsARRun.forall_le_not_stop_iff.2 hk)).2⟩⟩

/-! ### Lemma 5.4.2 -/

section Lemma542

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : AR2Params} {ε₁ L : ℝ}
  {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ} {xs : EuclideanSpace ℝ (Fin n)}

/-- A local minimizer is a critical point. -/
theorem gradient_eq_zero_of_isLocalMin (hmin : IsLocalMin f xs) : gradient f xs = 0 := by
  rw [← norm_eq_zero, norm_gradient_eq, hmin.fderiv_eq_zero, norm_zero]

namespace IsAR2StrictRun

/-- **The step bound (5.4.8)**, corrected, along a run: before termination, if
`‖x_k - x_*‖ ≤ q_*` then `‖s_k‖ ≤ κ_s ‖∇f(x_k)‖`, `κ_s = 2(1 + θ₁)/λ_*`. -/
theorem norm_step_le (hf : AssumptionHL f L) (h : IsAR2StrictRun f P ε₁ x s σ)
    (hlam : 0 < Chapter01.hessianMinEig f xs) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopTest f ε₁ none (x j))
    (hx : ‖x k - xs‖ ≤ Chapter01.hessianMinEig f xs / (4 * L)) :
    ‖s k‖ ≤ kappaStep P (Chapter01.hessianMinEig f xs) * ‖gradient f (x k)‖ := by
  have hσ := h.toAlgorithm_3_3_1.sigma_pos (fun j hj => hk j hj.le)
  have h1 := norm_step_le_of_strict (hf.contDiffAt (x k)) hσ.le P.θ₁_pos.le
    (by linarith : 0 < Chapter01.hessianMinEig f xs / 2) (lemma_5_4_1 hf hx) (h.strict k hk)
  have : (1 + P.θ₁) / (Chapter01.hessianMinEig f xs / 2) =
      kappaStep P (Chapter01.hessianMinEig f xs) := by
    unfold kappaStep; field_simp
  rwa [this] at h1

/-- **Quadratic decrease (5.4.4)** ([cartis2022evaluation], Lemma 5.4.2, first part): under
f.HL and `λ_* > 0`, if iteration `k` (before termination) is successful and
`‖x_k - x_*‖ ≤ q_*`, then `‖∇f(x_{k+1})‖ ≤ ‖∇f(x_k)‖²/ζ_*`. -/
theorem norm_gradient_succ_le (hf : AssumptionHL f L) (h : IsAR2StrictRun f P ε₁ x s σ)
    (hlam : 0 < Chapter01.hessianMinEig f xs) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopTest f ε₁ none (x j))
    (hx : ‖x k - xs‖ ≤ Chapter01.hessianMinEig f xs / (4 * L))
    (hs : P.η₁ ≤ taylorRatio f 2 x s k) :
    ‖gradient f (x (k + 1))‖ ≤
      ‖gradient f (x k)‖ ^ 2 / zetaStar P L (Chapter01.hessianMinEig f xs) := by
  set lam := Chapter01.hessianMinEig f xs
  set κ := kappaStep P lam
  set ζ := zetaStar P L lam
  set C := L + P.θ₁ + sigmaMaxAR2 P L
  have hL := hf.pos
  have hζ : 0 < ζ := zetaStar_pos hL hlam
  have hC : 0 < C := by have := P.θ₁_pos; have := arSigmaMax_pos P.ar L; simp only [C]; linarith
  have h3 := lemma_3_3_3 hf h.toAlgorithm_3_3_1 hk hs
  have hst := h.norm_step_le hf hlam hk hx
  have hst2 : ‖s k‖ ^ 2 ≤ κ ^ 2 * ‖gradient f (x k)‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hst 2
  have hN : ζ * (C * κ ^ 2) ≤ 2 := zetaStar_mul_le_newton hL hlam
  have e1 : 2 * ‖gradient f (x (k + 1))‖ ≤ C * ‖s k‖ ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hC] at h3; linarith
  rw [le_div_iff₀ hζ]
  have : 2 * (‖gradient f (x (k + 1))‖ * ζ) ≤ 2 * ‖gradient f (x k)‖ ^ 2 :=
    calc 2 * (‖gradient f (x (k + 1))‖ * ζ) = (2 * ‖gradient f (x (k + 1))‖) * ζ := by ring
      _ ≤ (C * ‖s k‖ ^ 2) * ζ := by gcongr
      _ ≤ (C * (κ ^ 2 * ‖gradient f (x k)‖ ^ 2)) * ζ := by gcongr
      _ = (ζ * (C * κ ^ 2)) * ‖gradient f (x k)‖ ^ 2 := by ring
      _ ≤ 2 * ‖gradient f (x k)‖ ^ 2 := by gcongr
  linarith

/-- **One iteration in `𝒬_*¹`** ([cartis2022evaluation], proof of Lemma 5.4.2): under f.HL,
`∇f(x_*) = 0` and `λ_* > 0`, if `x_k ∈ 𝒬_*¹` and `k` is before termination, then iteration `k` is
very successful (`ρ_k ≥ η₂`, via (5.4.9)–(5.4.12)) and `x_{k+1} ∈ 𝒬_*¹`. -/
theorem succ_mem_quadRegion (hf : AssumptionHL f L) (h : IsAR2StrictRun f P ε₁ x s σ)
    (hcrit : gradient f xs = 0) (hlam : 0 < Chapter01.hessianMinEig f xs) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopTest f ε₁ none (x j)) (hx : x k ∈ quadRegion f P L xs) :
    P.η₂ ≤ taylorRatio f 2 x s k ∧ x (k + 1) ∈ quadRegion f P L xs := by
  set lam := Chapter01.hessianMinEig f xs
  set κ := kappaStep P lam
  set ζ := zetaStar P L lam
  obtain ⟨hxk, hgk⟩ := hx
  have hL := hf.pos
  have hκ : 0 < κ := kappaStep_pos P hlam
  have hζ : 0 < ζ := zetaStar_pos hL hlam
  have hA := h.toAlgorithm_3_3_1
  have hσ := hA.sigma_pos (fun j hj => hk j hj.le)
  have hσmin := hA.sigmaMin_le (fun j hj => hk j hj.le)
  have hst := h.norm_step_le hf hlam hk hxk
  have hsz : ‖s k‖ ≤ κ * ζ := hst.trans (mul_le_mul_of_nonneg_left hgk hκ.le)
  have hc := hf.contDiffAt (x k)
  have hdec := taylorDecrement_ge_of_ar2Model hc (lemma_5_4_1 hf hxk) (hA.step hk).2.1
  set Δ := (ftaylorSeries ℝ f (x k)).taylorDecrement 2 (s k)
  have hs0 := norm_nonneg (s k)
  -- (5.4.12): `Δ ≥ λ_*/8 ‖s_k‖²`
  have hΔ8 : lam / 8 * ‖s k‖ ^ 2 ≤ Δ := by
    have hs3 : ‖s k‖ ^ 3 = ‖s k‖ * ‖s k‖ ^ 2 := by ring
    by_cases hθ : P.σmin < P.θ₁
    · have hr := kappaStep_mul_zetaStar_le_reg (L := L) hlam hθ
      have hθ' : 0 < P.θ₁ - P.σmin := sub_pos.2 hθ
      rw [le_div_iff₀ (by positivity)] at hr
      have h1 : (P.θ₁ - σ k) * ‖s k‖ ≤ (P.θ₁ - P.σmin) * ‖s k‖ :=
        mul_le_mul_of_nonneg_right (by linarith) hs0
      have h2 : (P.θ₁ - P.σmin) * ‖s k‖ ≤ (P.θ₁ - P.σmin) * (κ * ζ) :=
        mul_le_mul_of_nonneg_left hsz hθ'.le
      have h3 : (P.θ₁ - σ k) * ‖s k‖ ≤ lam / 4 := by nlinarith
      have h4 : (P.θ₁ - σ k) * ‖s k‖ * ‖s k‖ ^ 2 ≤ lam / 4 * ‖s k‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
      nlinarith
    · push Not at hθ
      have : 0 ≤ (σ k - P.θ₁) / 2 * ‖s k‖ ^ 3 :=
        mul_nonneg (by linarith) (by positivity)
      nlinarith
  have hΔpos : 0 < Δ := lt_of_le_of_lt (by positivity) (lemma_3_3_1 hA hk)
  -- (5.4.9)
  have hT := abs_sub_taylorPolynomial_le_of_lipschitz convex_univ (fun y _ => hf.contDiffAt y)
    hf.iteratedFDerivLipschitzOn (mem_univ (x k)) (mem_univ (x k + s k))
  norm_num [Nat.factorial] at hT
  have hLs : L * ‖s k‖ ≤ 3 * (1 - P.η₂) * lam / 4 := by
    have hr := kappaStep_mul_zetaStar_le_ratio (P := P) hL hlam
    rw [le_div_iff₀ (by positivity)] at hr
    nlinarith
  have hη := P.ar.one_sub_η₂_pos
  have hratio : P.η₂ ≤ taylorRatio f 2 x s k := by
    have hle : |f (x k + s k) - (f (x k) - Δ)| ≤ (1 - P.η₂) * Δ := by
      rw [show f (x k) - Δ = taylorPolynomial f 2 (x k) (s k) from
        Chapter03.sub_taylorDecrement_eq 2 (s k)]
      calc |f (x k + s k) - taylorPolynomial f 2 (x k) (s k)| ≤ L / 6 * ‖s k‖ ^ 3 := hT
        _ = (L * ‖s k‖) / 6 * ‖s k‖ ^ 2 := by ring
        _ ≤ (3 * (1 - P.η₂) * lam / 4) / 6 * ‖s k‖ ^ 2 := by gcongr
        _ = (1 - P.η₂) * (lam / 8 * ‖s k‖ ^ 2) := by ring
        _ ≤ (1 - P.η₂) * Δ := by gcongr
    have := le_reductionRatio_of_abs_sub_le hΔpos hle
    rw [taylorRatio_def]
    linarith
  have hsucc : P.η₁ ≤ taylorRatio f 2 x s k := P.η₁_le_η₂.trans hratio
  have hxs : x (k + 1) = x k + s k :=
    hA.run.eq_add_of_succ (IsARRun.forall_le_not_stop_iff.2 hk) hsucc
  have hg' := h.norm_gradient_succ_le hf hlam hk hxk hsucc
  have hg'ζ : ‖gradient f (x (k + 1))‖ ≤ ζ := by
    refine hg'.trans ?_
    rw [div_le_iff₀ hζ]
    have := norm_nonneg (gradient f (x k))
    nlinarith
  have hdist : ‖x (k + 1) - xs‖ ≤ lam / (2 * L) := by
    have hreg := kappaStep_mul_zetaStar_le_region (P := P) hL hlam
    calc ‖x (k + 1) - xs‖ = ‖(x k - xs) + s k‖ := by rw [hxs]; congr 1; abel
      _ ≤ ‖x k - xs‖ + ‖s k‖ := norm_add_le _ _
      _ ≤ lam / (4 * L) + lam / (4 * L) := add_le_add hxk (hsz.trans hreg)
      _ = lam / (2 * L) := by field_simp; ring
  have hm := mul_norm_sub_le_norm_gradient hf hcrit hdist
  refine ⟨hratio, ?_, hg'ζ⟩
  have hsq : ζ ≤ lam ^ 2 / (16 * L) := zetaStar_le_sq
  have h1 : 3 / 4 * lam * ‖x (k + 1) - xs‖ * (16 * L) ≤ lam ^ 2 :=
    (le_div_iff₀ (by positivity)).1 ((hm.trans hg'ζ).trans hsq)
  have h2 : 12 * L * ‖x (k + 1) - xs‖ ≤ lam :=
    le_of_mul_le_mul_right (by nlinarith) hlam
  rw [le_div_iff₀ (by positivity)]
  nlinarith [norm_nonneg (x (k + 1) - xs)]

/-- **Invariance of `𝒬_*¹`** ([cartis2022evaluation], Lemma 5.4.2, second part): if
`x_{k₀} ∈ 𝒬_*¹` then `x_k ∈ 𝒬_*¹` for every `k ≥ k₀` up to (and including) termination. -/
theorem mem_quadRegion_of_ge (hf : AssumptionHL f L) (h : IsAR2StrictRun f P ε₁ x s σ)
    (hcrit : gradient f xs = 0) (hlam : 0 < Chapter01.hessianMinEig f xs) {k₀ : ℕ}
    (h₀ : x k₀ ∈ quadRegion f P L xs) :
    ∀ k, k₀ ≤ k → (∀ j < k, ¬ stopTest f ε₁ none (x j)) → x k ∈ quadRegion f P L xs := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact fun _ => h₀
  | succ k _ ih =>
    intro hlt
    exact (h.succ_mem_quadRegion hf hcrit hlam (fun j hj => hlt j (Nat.lt_succ_of_le hj))
      (ih fun j hj => hlt j (hj.trans k.lt_succ_self))).2

end IsAR2StrictRun

/-- **Lemma 5.4.2** of [cartis2022evaluation] (region of quadratic convergence). Assume f.HL,
`x_*` a local minimizer of `f` with `λ_* = λ_min[∇²f(x_*)] > 0`, and an AR2 run with the
model-termination test (5.4.3). Then
(i) for every successful iteration `k` before termination with `‖x_k - x_*‖ ≤ q_*`,
`‖∇f(x_{k+1})‖ ≤ ‖∇f(x_k)‖²/ζ_*` (5.4.4);
(ii) if `x_{k₀} ∈ 𝒬_*¹` (5.4.6), then for every `k ≥ k₀` before termination, `x_k ∈ 𝒬_*¹`,
iteration `k` is (very) successful and (5.4.4) holds.
Here `q_* = λ_*/(4L)` and `ζ_* = zetaStar P L λ_*` is the corrected radius (5.4.5). -/
theorem lemma_5_4_2 (hf : AssumptionHL f L) (hmin : IsLocalMin f xs)
    (hlam : 0 < Chapter01.hessianMinEig f xs) (h : IsAR2StrictRun f P ε₁ x s σ) :
    (∀ k, (∀ j ≤ k, ¬ stopTest f ε₁ none (x j)) →
        ‖x k - xs‖ ≤ Chapter01.hessianMinEig f xs / (4 * L) →
        P.η₁ ≤ taylorRatio f 2 x s k →
        ‖gradient f (x (k + 1))‖ ≤
          ‖gradient f (x k)‖ ^ 2 / zetaStar P L (Chapter01.hessianMinEig f xs)) ∧
      ∀ k₀, x k₀ ∈ quadRegion f P L xs → ∀ k, k₀ ≤ k →
        (∀ j ≤ k, ¬ stopTest f ε₁ none (x j)) →
        x k ∈ quadRegion f P L xs ∧ P.η₂ ≤ taylorRatio f 2 x s k ∧
          ‖gradient f (x (k + 1))‖ ≤
            ‖gradient f (x k)‖ ^ 2 / zetaStar P L (Chapter01.hessianMinEig f xs) := by
  have hcrit := gradient_eq_zero_of_isLocalMin hmin
  refine ⟨fun k hk hx hs => h.norm_gradient_succ_le hf hlam hk hx hs,
    fun k₀ h₀ k hk hle => ?_⟩
  have hmem := h.mem_quadRegion_of_ge hf hcrit hlam h₀ k hk fun j hj => hle j hj.le
  have hstep := h.succ_mem_quadRegion hf hcrit hlam hle hmem
  exact ⟨hmem, hstep.1, h.norm_gradient_succ_le hf hlam hle hmem.1
    (P.η₁_le_η₂.trans hstep.1)⟩

end Lemma542

/-! ### Lemma 5.4.3 -/

section Lemma543

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : AR2Params} {ε₁ L : ℝ}
  {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ} {xs : EuclideanSpace ℝ (Fin n)}

/-- **Lemma 5.4.3** of [cartis2022evaluation] (asymptotic evaluation count, corrected). Assume
f.HL, `x_*` a local minimizer with `λ_* > 0`, an AR2 run with the test (5.4.3) that has not
terminated before `k₀`, and (5.4.13): `‖x_{k₀} - x_*‖ ≤ q_*` and `‖∇f(x_{k₀})‖ ≤ ζ ≤ ζ_*/2`.
Then the run terminates (first `j` with `‖∇f(x_j)‖ ≤ ε₁`) at some `j` with
`k₀ ≤ j ≤ k₀ + ⌈log₂ log₂(ζ_*/ε₁)⌉₊`, every iteration `k₀ ≤ k < j` being (very) successful.
(The book's count `log₂ log₂(ζ/ε)` (5.4.14) is too small by one in the worst case and lacks the
ceiling.) -/
theorem lemma_5_4_3 (hf : AssumptionHL f L) (hmin : IsLocalMin f xs)
    (hlam : 0 < Chapter01.hessianMinEig f xs) (h : IsAR2StrictRun f P ε₁ x s σ) {k₀ : ℕ}
    {ζ : ℝ} (hk₀ : ∀ j < k₀, ¬ stopTest f ε₁ none (x j))
    (hx : ‖x k₀ - xs‖ ≤ Chapter01.hessianMinEig f xs / (4 * L))
    (hg : ‖gradient f (x k₀)‖ ≤ ζ) (hζ : ζ ≤ zetaStar P L (Chapter01.hessianMinEig f xs) / 2) :
    ∃ j, IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε₁) j ∧ k₀ ≤ j ∧
      j ≤ k₀ + ⌈Real.logb 2 (Real.logb 2 (zetaStar P L (Chapter01.hessianMinEig f xs) / ε₁))⌉₊ ∧
      ∀ k, k₀ ≤ k → k < j → P.η₂ ≤ taylorRatio f 2 x s k := by
  classical
  set ζs := zetaStar P L (Chapter01.hessianMinEig f xs)
  set N := ⌈Real.logb 2 (Real.logb 2 (ζs / ε₁))⌉₊
  have hζs : 0 < ζs := zetaStar_pos hf.pos hlam
  have hε := h.toAlgorithm_3_3_1.ε₁_pos
  have h₀ : x k₀ ∈ quadRegion f P L xs := ⟨hx, by linarith⟩
  have hloc := (lemma_5_4_2 hf hmin hlam h).2 k₀ h₀
  -- the test holds at some `j ≤ k₀ + N`
  have hex : ∃ j ≤ k₀ + N, ‖gradient f (x j)‖ ≤ ε₁ := by
    by_contra hne
    push Not at hne
    have hnot : ∀ j ≤ k₀ + N, ¬ stopTest f ε₁ none (x j) := fun j hj hs =>
      (hne j hj).not_ge (stopTest_none.1 hs)
    let u : ℕ → ℝ := fun m => if m ≤ N then ‖gradient f (x (k₀ + m))‖ else 0
    have hu : ∀ m, 0 ≤ u m := fun m => by
      simp only [u]; split_ifs
      · exact norm_nonneg _
      · exact le_rfl
    have hrec : ∀ m, u (m + 1) ≤ u m ^ 2 / ζs := by
      intro m
      by_cases hm : m + 1 ≤ N
      · simp only [u, hm, Nat.le_of_succ_le hm, ↓reduceIte]
        rw [← add_assoc]
        exact (hloc (k₀ + m) (Nat.le_add_right _ _) fun j hj => hnot j (by omega)).2.2
      · simp only [u, hm, ↓reduceIte]
        exact div_nonneg (sq_nonneg _) hζs.le
    have h0 : u 0 ≤ ζs / 2 := by simp only [u, zero_le, ↓reduceIte, add_zero]; linarith
    have := (le_two_pow_two_pow_of_sq hζs hu hrec h0).2 ε₁ hε N (Or.inr le_rfl)
    simp only [u, le_rfl, ↓reduceIte] at this
    exact (hne _ le_rfl).not_ge this
  obtain ⟨j₁, hj₁, hj₁t⟩ := hex
  obtain ⟨j, hjj₁, hj⟩ := exists_isFirstHit_le (p := fun k => ‖gradient f (x k)‖ ≤ ε₁) hj₁t
  have hk₀j : k₀ ≤ j := by
    by_contra hlt
    push Not at hlt
    exact hk₀ j hlt (stopTest_none.2 hj.test)
  refine ⟨j, hj, hk₀j, hjj₁.trans hj₁, fun k hk hkj => ?_⟩
  exact (hloc k hk fun i hi => fun hs =>
    hj.not_test_of_lt (hi.trans_lt hkj) (stopTest_none.1 hs)).2.1

end Lemma543

/-! ### Theorem 5.4.4 -/

section Theorem544

@[deprecated IsARRun.eq_of_forall_not_succ (since := "2026-10-26")]
alias arRun_eq_of_forall_not_succ := IsARRun.eq_of_forall_not_succ

@[deprecated IsARRun.card_successSet_le_card_succ_add_one (since := "2026-10-26")]
alias arRun_card_successSet_le_card_succ_add_one := IsARRun.card_successSet_le_card_succ_add_one

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : AR2Params} {ε₁ L flow : ℝ} {ε₂ : Option ℝ}
  {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ} {xs : EuclideanSpace ℝ (Fin n)}

@[deprecated Chapter03.ar2_decrease_of_le (since := "2026-10-26")]
alias ar2_decrease_of_le := Chapter03.ar2_decrease_of_le

/-- **(5.4.16)** ([cartis2022evaluation], Theorem 5.4.4, first part) for any AR2 run (with
`ε₂ = +∞`) under f.Bb and f.HL, and any `ζ > 0`: at every iteration `k` before termination, the
number of successful iterations `j ≤ k` with `‖∇f(x_j)‖ > ζ` is at most
`κ^S_AR2 (f(x₀) - f_low)/ζ^{3/2} + 1`. -/
theorem card_succ_norm_gradient_gt_le (hb : Chapter02.AssumptionBb f flow)
    (hf : AssumptionHL f L) (h : algorithm_3_3_1 f P ε₁ none x s σ) {ζ : ℝ} (hζ : 0 < ζ)
    {k : ℕ} (hk : ∀ j ≤ k, ¬ stopTest f ε₁ none (x j)) :
    ((successSet (fun j => P.η₁ ≤ taylorRatio f 2 x s j ∧ ζ < ‖gradient f (x j)‖) k).card : ℝ) ≤
      kappaSAR2 P L * (f (x 0) - flow) / ζ ^ (3 / 2 : ℝ) + 1 := by
  have hκ := kappaSAR2_pos (P := P) hf.nonneg
  set δ := ζ ^ (3 / 2 : ℝ) / kappaSAR2 P L
  have hδ : 0 < δ := by positivity
  have hcard := h.run.card_successSet_le_card_succ_add_one (fun y => ζ < ‖gradient f y‖) hk
  have hT' := card_mul_le_of_decrease (φ := fun j => f (x j)) (k := k) (c := δ)
    (T := successSet (fun j => P.η₁ ≤ taylorRatio f 2 x s j ∧ ζ < ‖gradient f (x (j + 1))‖) k)
    successSet_subset_range
    (fun j hj =>
      (h.run.accept j (IsARRun.forall_le_not_stop_iff.2 fun i hi => hk i (hi.trans hj))).le
      (w := f) rfl (lt_of_le_of_lt (by
        have := h.sigma_pos (k := j) fun i hi => hk i (hi.le.trans hj)
        positivity) (lemma_3_3_1 h fun i hi => hk i (hi.trans hj))))
    (fun j hj => by
      rw [mem_successSet] at hj
      exact Chapter03.ar2_decrease_of_le hf h (fun i hi => hk i (hi.trans hj.1)) hj.2.1 hζ
        hj.2.2.le)
    (hb _)
  have hNδ : (f (x 0) - flow) / δ = kappaSAR2 P L * (f (x 0) - flow) / ζ ^ (3 / 2 : ℝ) := by
    simp only [δ]; field_simp
  have hcard' : ((successSet (fun j => P.η₁ ≤ taylorRatio f 2 x s j ∧
      ζ < ‖gradient f (x j)‖) k).card : ℝ) ≤ (successSet (fun j => P.η₁ ≤ taylorRatio f 2 x s j ∧
      ζ < ‖gradient f (x (j + 1))‖) k).card + 1 := by exact_mod_cast hcard
  have h2 : ((successSet (fun j => P.η₁ ≤ taylorRatio f 2 x s j ∧
      ζ < ‖gradient f (x (j + 1))‖) k).card : ℝ) ≤ (f (x 0) - flow) / δ := by
    rw [le_div_iff₀ hδ]; linarith
  rw [← hNδ]
  linarith

/-- **(5.4.17)** ([cartis2022evaluation], Theorem 5.4.4, second part, with the corrected local
count): under f.Bb, f.HL, `x_*` a local minimizer with `λ_* > 0`, `0 < ζ ≤ ζ_*/2`, and (5.4.18)
(no iterate before termination with `‖x_k - x_*‖ > q_*` and `ε₁ < ‖∇f(x_k)‖ ≤ ζ`), at every
iteration `k` before termination
`|𝒮_k| ≤ κ^S_AR2 (f(x₀) - f_low)/ζ^{3/2} + ⌈log₂ log₂(ζ_*/ε₁)⌉₊ + 1`. -/
theorem card_successSet_le_of_local (hb : Chapter02.AssumptionBb f flow)
    (hf : AssumptionHL f L) (hmin : IsLocalMin f xs) (hlam : 0 < Chapter01.hessianMinEig f xs)
    (h : IsAR2StrictRun f P ε₁ x s σ) {ζ : ℝ} (hζ : 0 < ζ)
    (hζs : ζ ≤ zetaStar P L (Chapter01.hessianMinEig f xs) / 2)
    (hreg : ∀ k, (∀ j ≤ k, ¬ stopTest f ε₁ none (x j)) → ‖gradient f (x k)‖ ≤ ζ →
      ‖x k - xs‖ ≤ Chapter01.hessianMinEig f xs / (4 * L))
    {k : ℕ} (hk : ∀ j ≤ k, ¬ stopTest f ε₁ none (x j)) :
    ((successSet (fun j => P.η₁ ≤ taylorRatio f 2 x s j) k).card : ℝ) ≤
      kappaSAR2 P L * (f (x 0) - flow) / ζ ^ (3 / 2 : ℝ) +
        ⌈Real.logb 2 (Real.logb 2 (zetaStar P L (Chapter01.hessianMinEig f xs) / ε₁))⌉₊ + 1 := by
  classical
  set N := ⌈Real.logb 2 (Real.logb 2 (zetaStar P L (Chapter01.hessianMinEig f xs) / ε₁))⌉₊
  set S := successSet (fun j => P.η₁ ≤ taylorRatio f 2 x s j) k
  set T := successSet (fun j => P.η₁ ≤ taylorRatio f 2 x s j ∧ ζ < ‖gradient f (x j)‖) k
  have hT := card_succ_norm_gradient_gt_le hb hf h.toAlgorithm_3_3_1 hζ hk
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  by_cases hex : ∃ j, j ≤ k ∧ ‖gradient f (x j)‖ ≤ ζ
  · obtain ⟨hk1k, hk1g⟩ := Nat.find_spec hex
    have hmin1 : ∀ j < Nat.find hex, ζ < ‖gradient f (x j)‖ := fun j hj => by
      have := Nat.find_min hex hj
      push Not at this
      exact this (by omega)
    obtain ⟨jt, hjt, -, hjtN, -⟩ := lemma_5_4_3 hf hmin hlam h (k₀ := Nat.find hex)
      (fun j hj => hk j (by omega))
      (hreg _ (fun j hj => hk j (hj.trans hk1k)) hk1g) hk1g hζs
    have hkjt : k < jt := by
      by_contra hle
      push Not at hle
      exact hk jt hle (stopTest_none.2 hjt.test)
    have hsub : S ⊆ T ∪ Icc (Nat.find hex) k := by
      intro j hj
      rw [mem_successSet] at hj
      rw [Finset.mem_union, Finset.mem_Icc]
      by_cases hj1 : j < Nat.find hex
      · exact Or.inl (mem_successSet.2 ⟨hj.1, hj.2, hmin1 j hj1⟩)
      · exact Or.inr ⟨by omega, hj.1⟩
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [Nat.card_Icc] at hc
    have hc' : S.card ≤ T.card + N := by omega
    have : (S.card : ℝ) ≤ T.card + N := by exact_mod_cast hc'
    linarith
  · have hsub : S ⊆ T := by
      intro j hj
      rw [mem_successSet] at hj ⊢
      refine ⟨hj.1, hj.2, ?_⟩
      by_contra hle
      exact hex ⟨j, hj.1, not_lt.1 hle⟩
    have : (S.card : ℝ) ≤ T.card := by exact_mod_cast Finset.card_le_card hsub
    linarith

/-- **Theorem 5.4.4** of [cartis2022evaluation] (global complexity bound for locally convex
functions). Assume f.Bb and f.HL, `x_*` a local minimizer with `λ_* = λ_min[∇²f(x_*)] > 0`, an
AR2 run with the model-termination test (5.4.3), and `0 < ζ ≤ ζ_*/2`. Then
(i) (5.4.16) at every iteration `k` before termination, the number of successful iterations
`j ≤ k` with `‖∇f(x_j)‖ > ζ` is at most `κ^S_AR2 (f(x₀) - f_low)/ζ^{3/2} + 1`;
(ii) (5.4.17) if no iterate `x_k` before termination satisfies (5.4.18)
(`‖x_k - x_*‖ > q_*` and `‖∇f(x_k)‖ ≤ ζ`), then at every iteration `k` before termination
`|𝒮_k| ≤ κ^S_AR2 (f(x₀) - f_low)/ζ^{3/2} + ⌈log₂ log₂(ζ_*/ε₁)⌉₊ + 1`
(the book's second term `log₂ log₂(ζ/ε)` corrected as in Lemma 5.4.3). -/
theorem theorem_5_4_4 (hb : Chapter02.AssumptionBb f flow) (hf : AssumptionHL f L)
    (hmin : IsLocalMin f xs) (hlam : 0 < Chapter01.hessianMinEig f xs)
    (h : IsAR2StrictRun f P ε₁ x s σ) {ζ : ℝ} (hζ : 0 < ζ)
    (hζs : ζ ≤ zetaStar P L (Chapter01.hessianMinEig f xs) / 2) :
    (∀ k, (∀ j ≤ k, ¬ stopTest f ε₁ none (x j)) →
      ((successSet (fun j => P.η₁ ≤ taylorRatio f 2 x s j ∧ ζ < ‖gradient f (x j)‖) k).card :
          ℝ) ≤ kappaSAR2 P L * (f (x 0) - flow) / ζ ^ (3 / 2 : ℝ) + 1) ∧
    ((∀ k, (∀ j ≤ k, ¬ stopTest f ε₁ none (x j)) → ‖gradient f (x k)‖ ≤ ζ →
        ‖x k - xs‖ ≤ Chapter01.hessianMinEig f xs / (4 * L)) →
      ∀ k, (∀ j ≤ k, ¬ stopTest f ε₁ none (x j)) →
        ((successSet (fun j => P.η₁ ≤ taylorRatio f 2 x s j) k).card : ℝ) ≤
          kappaSAR2 P L * (f (x 0) - flow) / ζ ^ (3 / 2 : ℝ) +
            ⌈Real.logb 2 (Real.logb 2 (zetaStar P L (Chapter01.hessianMinEig f xs) / ε₁))⌉₊ +
              1) :=
  ⟨fun _ hk => card_succ_norm_gradient_gt_le hb hf h.toAlgorithm_3_3_1 hζ hk,
    fun hreg _ hk => card_successSet_le_of_local hb hf hmin hlam h hζ hζs hreg hk⟩

end Theorem544

end CartisGouldToint.Chapter05
