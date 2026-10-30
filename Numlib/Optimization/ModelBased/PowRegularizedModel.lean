import Numlib.Analysis.InnerProductSpace.NormPowHessian
import Numlib.Optimization.ModelBased.RatioTest
import Numlib.Optimization.Optimality.Unconstrained

/-!
# Taylor models regularized by a real power

The universal adaptive-regularization method ARp-H of [cartis2022evaluation] (Algorithm 5.5.1)
uses the model
`m(s) = T_p(x, s) + σ / r! ‖s‖^r` (5.5.1)
with a real power `r > p` and the generalized factorial
`r! = ∏_{ℓ=1}^{⌊r⌋} (ℓ + r - ⌊r⌋)` (5.5.2), and analyses it for objectives whose `p`-th derivative
is Hölder continuous (assumption f.DpH). With `r = p + 1` this is the model of ARp
(`Optimization.regularizedModel`).

## Main definitions

* `Optimization.realFactorial r`: the generalized factorial (5.5.2), defined as
  `holderFactorial ⌊r⌋₊ (Int.fract r)`.
* `Optimization.powRegularizedModel D p σ r`: the model for derivative data `D` (the jet
  `ftaylorSeries ℝ f x` of the objective in ARp-H).

## Main statements

* `Optimization.realFactorial_eq_mul_sub_one`: `r! = r (r-1)!` for `r ≥ 1`;
  `Optimization.realFactorial_mono`: the generalized factorial is monotone;
  `Optimization.realFactorial_natCast`, `Optimization.realFactorial_add_holder`: the conventions
  agree with `n!` and with the book's `(k + β)!` (`holderFactorial k β`, `β ∈ [0, 1]`).
* `Optimization.lt_taylorDecrement_of_powRegularizedModel_lt`: Lemma 5.5.1.
* `Optimization.fderiv_powRegularizedModel`, `Optimization.iteratedFDeriv_powRegularizedModel`:
  derivatives of the model.
* `Optimization.norm_fderiv_le_of_powRegularizedModel`,
  `Optimization.minCurvature_ge_of_powRegularizedModel`: Lemma 5.5.2 ((5.5.13), (5.5.14)).
* `Optimization.abs_reductionRatio_sub_one_le_of_holder_sharp`,
  `Optimization.abs_reductionRatio_sub_one_le_of_holder`: the ratio estimate (5.5.22).
* `Optimization.exists_isMinOn_powRegularizedModel`: in finite dimension the model has a global
  minimizer, at which the first- and second-order necessary conditions hold.

All statements are for one iteration (point `x`, weight `σ`, step `s`), with the Hölder
condition on an arbitrary convex set `C` containing `x` and `x + s`.
-/

open Set Filter Topology Metric
open scoped Nat RealInnerProductSpace

namespace Optimization

section RealFactorial

/-- The generalized factorial of a real number ([cartis2022evaluation], (5.5.2)):
`r! = ∏_{ℓ=1}^{⌊r⌋} (ℓ + r - ⌊r⌋)` for `r ≥ 0`, defined through `holderFactorial` as
`holderFactorial ⌊r⌋₊ (Int.fract r)`. It is the usual factorial on natural numbers
(`realFactorial_natCast`) and satisfies `r! = r (r - 1)!` for `r ≥ 1`
(`realFactorial_eq_mul_sub_one`). (For `r < 0` the value is `1`.) -/
noncomputable def realFactorial (r : ℝ) : ℝ := holderFactorial ⌊r⌋₊ (Int.fract r)

theorem realFactorial_def (r : ℝ) : realFactorial r = holderFactorial ⌊r⌋₊ (Int.fract r) := rfl

/-- The generalized factorial is positive. -/
theorem realFactorial_pos (r : ℝ) : 0 < realFactorial r :=
  holderFactorial_pos _ (by linarith [Int.fract_nonneg r])

/-- On natural numbers the generalized factorial is the factorial. -/
@[simp]
theorem realFactorial_natCast (n : ℕ) : realFactorial n = (n ! : ℝ) := by
  rw [realFactorial_def, Nat.floor_natCast, Int.fract_natCast, holderFactorial_zero_right]

@[simp]
theorem realFactorial_zero : realFactorial 0 = 1 := by
  simpa using realFactorial_natCast 0

@[simp]
theorem realFactorial_one : realFactorial 1 = 1 := by
  simpa using realFactorial_natCast 1

/-- `r! = r (r - 1)!` for `r ≥ 1` ([cartis2022evaluation], footnote 44). -/
theorem realFactorial_eq_mul_sub_one {r : ℝ} (hr : 1 ≤ r) :
    realFactorial r = r * realFactorial (r - 1) := by
  have ha : 0 ≤ r - 1 := by linarith
  have hfl : ⌊r⌋₊ = ⌊r - 1⌋₊ + 1 := by
    rw [← Nat.floor_add_one ha, sub_add_cancel]
  have hfr : Int.fract r = Int.fract (r - 1) := (Int.fract_sub_one r).symm
  have hsum : ((⌊r - 1⌋₊ : ℕ) : ℝ) + Int.fract (r - 1) = r - 1 := by
    rw [natCast_floor_eq_intCast_floor ha, Int.floor_add_fract]
  rw [realFactorial_def, realFactorial_def, hfl, hfr, holderFactorial_succ]
  have : (⌊r - 1⌋₊ : ℝ) + 1 + Int.fract (r - 1) = r := by linarith
  rw [this, mul_comm]

/-- `r! = r (r - 1) (r - 2)!` for `r ≥ 2`. -/
theorem realFactorial_eq_mul_mul_sub_two {r : ℝ} (hr : 2 ≤ r) :
    realFactorial r = r * (r - 1) * realFactorial (r - 2) := by
  rw [realFactorial_eq_mul_sub_one (by linarith), realFactorial_eq_mul_sub_one (by linarith),
    sub_sub, one_add_one_eq_two, mul_assoc]

/-- `(r - 1)! ≤ r!` for `r ≥ 1`. -/
theorem realFactorial_sub_one_le {r : ℝ} (hr : 1 ≤ r) :
    realFactorial (r - 1) ≤ realFactorial r := by
  rw [realFactorial_eq_mul_sub_one hr]
  exact le_mul_of_one_le_left (realFactorial_pos _).le hr

/-- `(k + β)!` is monotone in `β ∈ (-1, ∞)`. -/
theorem holderFactorial_le_holderFactorial (k : ℕ) {β β' : ℝ} (hβ : -1 < β) (h : β ≤ β') :
    holderFactorial k β ≤ holderFactorial k β' := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [holderFactorial_succ, holderFactorial_succ]
    have : (0 : ℝ) ≤ k := k.cast_nonneg
    exact mul_le_mul ih (by linarith) (by linarith) (holderFactorial_pos _ (by linarith)).le

/-- The generalized factorial is at least `1`. -/
theorem one_le_realFactorial (r : ℝ) : 1 ≤ realFactorial r := by
  rw [realFactorial_def]
  calc (1 : ℝ) ≤ (⌊r⌋₊ ! : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
    _ = holderFactorial ⌊r⌋₊ 0 := (holderFactorial_zero_right _).symm
    _ ≤ _ := holderFactorial_le_holderFactorial _ (by norm_num) (Int.fract_nonneg r)

/-- The generalized factorial is monotone (it is `1` on `(-∞, 1]`). -/
theorem realFactorial_mono : Monotone realFactorial := by
  intro r r' h
  rcases lt_or_ge r 0 with hr | hr
  · rw [realFactorial_def, Nat.floor_eq_zero.2 (hr.trans one_pos), holderFactorial_zero]
    exact one_le_realFactorial r'
  have hfl : ⌊r⌋₊ ≤ ⌊r'⌋₊ := Nat.floor_le_floor h
  rw [realFactorial_def, realFactorial_def]
  rcases hfl.lt_or_eq with hlt | heq
  · -- `r! ≤ (⌊r⌋ + 1)! ≤ ⌊r'⌋! ≤ r'!`
    calc holderFactorial ⌊r⌋₊ (Int.fract r) ≤ holderFactorial ⌊r⌋₊ 1 :=
          holderFactorial_le_holderFactorial _ (by linarith [Int.fract_nonneg r])
            (Int.fract_lt_one r).le
      _ = ((⌊r⌋₊ + 1)! : ℝ) := holderFactorial_one_right _
      _ ≤ (⌊r'⌋₊ ! : ℝ) := by exact_mod_cast Nat.factorial_le hlt
      _ = holderFactorial ⌊r'⌋₊ 0 := (holderFactorial_zero_right _).symm
      _ ≤ _ := holderFactorial_le_holderFactorial _ (by norm_num) (Int.fract_nonneg r')
  · rw [heq]
    refine holderFactorial_le_holderFactorial _ (by linarith [Int.fract_nonneg r]) ?_
    have h1 := Int.floor_add_fract r
    have h2 := Int.floor_add_fract r'
    rw [← natCast_floor_eq_intCast_floor hr] at h1
    rw [← natCast_floor_eq_intCast_floor (hr.trans h), ← heq] at h2
    linarith

/-- The generalized factorial agrees with the book's `(k + β)! = ∏_{ℓ=1}^k (ℓ + β)` of Section
A.8 for `β ∈ [0, 1]`, including `β = 1` where both are `(k + 1)!`. -/
theorem realFactorial_add_holder (k : ℕ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    realFactorial (k + β) = holderFactorial k β := by
  rcases hβ1.lt_or_eq with hβ1 | rfl
  · have hfl : ⌊(k : ℝ) + β⌋₊ = k := by
      rw [Nat.floor_eq_iff (by positivity)]
      constructor <;> linarith
    have hfr : Int.fract ((k : ℝ) + β) = β := by
      rw [Int.fract_natCast_add, Int.fract_eq_self.2 ⟨hβ0, hβ1⟩]
    rw [realFactorial_def, hfl, hfr]
  · rw [holderFactorial_one_right, ← realFactorial_natCast]
    push_cast
    rfl

/-- `realFactorial (k + 1) = (k + 1)!`, with the natural number cast as a real sum. -/
theorem realFactorial_natCast_add_one (k : ℕ) : realFactorial ((k : ℝ) + 1) = ((k + 1)! : ℝ) := by
  rw [← realFactorial_natCast]
  push_cast
  rfl

end RealFactorial

section Model

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Taylor model regularized by a real power ([cartis2022evaluation], (5.5.1)):
`m(s) = T_p(s) + σ / r! ‖s‖^r`, with `T_p = D.taylorSum p` the Taylor sum of the derivative data
`D` and `r!` the generalized factorial `Optimization.realFactorial`. -/
noncomputable def powRegularizedModel (D : FormalMultilinearSeries ℝ E ℝ) (p : ℕ) (σ r : ℝ)
    (s : E) : ℝ :=
  D.taylorSum p s + σ / realFactorial r * ‖s‖ ^ r

variable (D : FormalMultilinearSeries ℝ E ℝ) (p : ℕ) (σ r : ℝ)

theorem powRegularizedModel_def (s : E) :
    powRegularizedModel D p σ r s = D.taylorSum p s + σ / realFactorial r * ‖s‖ ^ r := rfl

/-- The model at the zero step is the constant term of the data. -/
theorem powRegularizedModel_zero_right (hr : r ≠ 0) :
    powRegularizedModel D p σ r 0 = D.taylorSum p 0 := by
  simp [powRegularizedModel_def, Real.zero_rpow hr]

/-- The regularization term `s ↦ σ / r! ‖s‖^r`. -/
theorem powRegularizedModel_eq_add :
    powRegularizedModel D p σ r =
      D.taylorSum p + fun s : E => (σ / realFactorial r) • ‖s‖ ^ r := by
  funext s
  simp [powRegularizedModel_def, smul_eq_mul]

theorem continuous_powRegularizedModel (hr : 0 ≤ r) : Continuous (powRegularizedModel D p σ r) :=
  ((D.contDiff_taylorSum p (n := 0)).continuous).add
    (continuous_const.mul (continuous_norm.rpow_const fun _ => Or.inr hr))

variable {D p σ r}

/-- **Lemma 5.5.1** ([cartis2022evaluation], (5.5.12)): a step decreasing the model decreases the
Taylor sum by more than the regularization term: `m(s) < m(0)` gives
`σ / r! ‖s‖^r < T_p(0) - T_p(s)`. -/
theorem lt_taylorDecrement_of_powRegularizedModel_lt (hr : r ≠ 0) {s : E}
    (h : powRegularizedModel D p σ r s < powRegularizedModel D p σ r 0) :
    σ / realFactorial r * ‖s‖ ^ r < D.taylorDecrement p s := by
  rw [powRegularizedModel_zero_right D p σ r hr, powRegularizedModel_def] at h
  rw [FormalMultilinearSeries.taylorDecrement]
  linarith

/-- The non-strict form of Lemma 5.5.1: `m(s) ≤ m(0)` gives `σ / r! ‖s‖^r ≤ T_p(0) - T_p(s)`. -/
theorem taylorDecrement_ge_of_powRegularizedModel_le (hr : r ≠ 0) {s : E}
    (h : powRegularizedModel D p σ r s ≤ powRegularizedModel D p σ r 0) :
    σ / realFactorial r * ‖s‖ ^ r ≤ D.taylorDecrement p s := by
  rw [powRegularizedModel_zero_right D p σ r hr, powRegularizedModel_def] at h
  rw [FormalMultilinearSeries.taylorDecrement]
  linarith

/-- The gradient of the regularization term: for `r > 1`,
`∇(σ/r! ‖·‖^r)(s) = σ/(r-1)! ‖s‖^{r-2} s`. -/
theorem hasFDerivAt_regTerm (hr : 1 < r) (s : E) :
    HasFDerivAt (fun s : E => σ / realFactorial r * ‖s‖ ^ r)
      ((σ / realFactorial (r - 1) * ‖s‖ ^ (r - 2)) • innerSL ℝ s) s := by
  refine ((hasFDerivAt_norm_rpow s hr).const_mul (σ / realFactorial r)).congr_fderiv ?_
  rw [smul_smul, realFactorial_eq_mul_sub_one hr.le]
  congr 1
  have h1 := (realFactorial_pos (r - 1)).ne'
  have h2 : r ≠ 0 := by linarith
  field_simp

/-- The norm of the gradient of the regularization term: `σ/(r-1)! ‖s‖^{r-1}` (for `σ ≥ 0`,
`r > 1`). -/
theorem norm_regTerm_grad (hσ : 0 ≤ σ) (hr : 1 < r) (s : E) :
    ‖(σ / realFactorial (r - 1) * ‖s‖ ^ (r - 2)) • innerSL ℝ s‖ =
      σ / realFactorial (r - 1) * ‖s‖ ^ (r - 1) := by
  rw [norm_smul, innerSL_apply_norm, Real.norm_eq_abs,
    abs_of_nonneg (by have := realFactorial_pos (r - 1); positivity)]
  rcases eq_or_ne s 0 with rfl | hs
  · simp [Real.zero_rpow (show r - 1 ≠ 0 by linarith)]
  · rw [mul_assoc, ← Real.rpow_add_one (norm_ne_zero_iff.2 hs)]
    ring_nf

/-- **Derivative of the model** ([cartis2022evaluation], proof of Lemma 5.5.2): for `r > 1`,
`∇m(s) = ∇T_p(s) + σ/(r-1)! ‖s‖^{r-2} s`. -/
theorem hasFDerivAt_powRegularizedModel (hr : 1 < r) (s : E) :
    HasFDerivAt (powRegularizedModel D p σ r)
      (fderiv ℝ (D.taylorSum p) s + (σ / realFactorial (r - 1) * ‖s‖ ^ (r - 2)) • innerSL ℝ s)
      s :=
  (((D.contDiff_taylorSum p (n := 1)).differentiable one_ne_zero s).hasFDerivAt).add
    (hasFDerivAt_regTerm hr s)

/-- The gradient of the model (5.5.13): for `r > 1`,
`∇m(s) = ∇T_p(s) + σ/(r-1)! ‖s‖^{r-2} s`. -/
theorem fderiv_powRegularizedModel (hr : 1 < r) (s : E) :
    fderiv ℝ (powRegularizedModel D p σ r) s =
      fderiv ℝ (D.taylorSum p) s + (σ / realFactorial (r - 1) * ‖s‖ ^ (r - 2)) • innerSL ℝ s :=
  (hasFDerivAt_powRegularizedModel hr s).fderiv

/-- **Higher derivatives of the model**: wherever `‖·‖^r` is `C^j` (for instance `j < r`, or
`s ≠ 0`), `∇^j m(s) = ∇^j T_p(s) + σ/r! ∇^j (‖·‖^r)(s)`. -/
theorem iteratedFDeriv_powRegularizedModel {j : ℕ} {s : E}
    (hN : ContDiffAt ℝ j (fun y : E => ‖y‖ ^ r) s) :
    iteratedFDeriv ℝ j (powRegularizedModel D p σ r) s =
      iteratedFDeriv ℝ j (D.taylorSum p) s +
        (σ / realFactorial r) • iteratedFDeriv ℝ j (fun y : E => ‖y‖ ^ r) s := by
  rw [powRegularizedModel_eq_add, iteratedFDeriv_add_apply (D.contDiff_taylorSum p).contDiffAt
    (hN.const_smul _), iteratedFDeriv_const_smul_apply' hN]

/-- The model is `C²` for `r ≥ 2`. -/
theorem contDiff_two_powRegularizedModel (hr : 2 ≤ r) :
    ContDiff ℝ 2 (powRegularizedModel D p σ r) := by
  rw [powRegularizedModel_eq_add]
  exact (D.contDiff_taylorSum p).add ((contDiff_two_norm_rpow hr).const_smul _)

end Model

section Estimates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {f : E → ℝ} {p : ℕ} {H β σ r : ℝ} {C : Set E} {x s : E}

/-- **Lemma 5.5.2, (5.5.13)** ([cartis2022evaluation]): let `p ≥ 1`, `β ≥ 0`, `f` be `C^p` on a
convex set `C ∋ x, x + s` with `(H, β)`-Hölder `p`-th derivative there, `σ ≥ 0`, `r > 1`, and
`m = powRegularizedModel (ftaylorSeries ℝ f x) p σ r`. Then
`‖∇f(x + s)‖ ≤ H/(p - 1 + β)! ‖s‖^{p - 1 + β} + σ/(r-1)! ‖s‖^{r-1} + ‖∇m(s)‖`,
where `(p - 1 + β)! = holderFactorial (p - 1) β`; `∇m(s)` is the model gradient at the step. -/
theorem norm_fderiv_le_of_powRegularizedModel (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hp : 1 ≤ p) (hβ : 0 ≤ β)
    (hH : IteratedFDerivHolderOn f p H β C) (hx : x ∈ C) (hxs : x + s ∈ C) (hσ : 0 ≤ σ)
    (hr : 1 < r) :
    ‖fderiv ℝ f (x + s)‖ ≤
      H / holderFactorial (p - 1) β * ‖s‖ ^ (((p - 1 : ℕ) : ℝ) + β) +
        σ / realFactorial (r - 1) * ‖s‖ ^ (r - 1) +
          ‖fderiv ℝ (powRegularizedModel (ftaylorSeries ℝ f x) p σ r) s‖ := by
  have hT := norm_iteratedFDeriv_sub_taylorPolynomial_le_of_holder hC hf hβ hH hx hxs hp
  rw [norm_iteratedFDeriv_one_sub] at hT
  rw [fderiv_powRegularizedModel hr]
  set a := fderiv ℝ f (x + s)
  set b := fderiv ℝ ((ftaylorSeries ℝ f x).taylorSum p) s
  set c := (σ / realFactorial (r - 1) * ‖s‖ ^ (r - 2)) • innerSL ℝ s
  have hc := norm_regTerm_grad hσ hr s
  have hb : b = fderiv ℝ (taylorPolynomial f p x) s := rfl
  rw [← hb] at hT
  calc ‖a‖ = ‖(a - b) - c + (b + c)‖ := by congr 1; abel
    _ ≤ ‖a - b‖ + ‖c‖ + ‖b + c‖ := (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
    _ ≤ _ := by rw [hc]; gcongr

/-- **Lemma 5.5.2, (5.5.14)** ([cartis2022evaluation]): with `p ≥ 2`, `r ≥ 2` and the hypotheses
of `Optimization.norm_fderiv_le_of_powRegularizedModel`,
`-λ_min[∇²f(x + s)] ≤ H/(p - 2 + β)! ‖s‖^{p - 2 + β} + σ/(r-2)! ‖s‖^{r-2} - λ_min[∇²m(s)]`.
(Only the `j = 2` case of Lemma B.4.1 is used: the Hessian of `‖·‖^r` is positive semidefinite
with `D²(‖·‖^r)(s)[d, d] ≤ r (r - 1) ‖s‖^{r-2} ‖d‖²`.) -/
theorem minCurvature_ge_of_powRegularizedModel (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hp : 2 ≤ p) (hβ : 0 ≤ β)
    (hH : IteratedFDerivHolderOn f p H β C) (hx : x ∈ C) (hxs : x + s ∈ C) (hσ : 0 ≤ σ)
    (hr : 2 ≤ r) :
    -minCurvature (iteratedFDeriv ℝ 2 f (x + s)) ≤
      H / holderFactorial (p - 2) β * ‖s‖ ^ (((p - 2 : ℕ) : ℝ) + β) +
        σ / realFactorial (r - 2) * ‖s‖ ^ (r - 2) -
          minCurvature
            (iteratedFDeriv ℝ 2 (powRegularizedModel (ftaylorSeries ℝ f x) p σ r) s) := by
  have hT := norm_iteratedFDeriv_sub_taylorPolynomial_le_of_holder hC hf hβ hH hx hxs hp
  rw [iteratedFDeriv_powRegularizedModel ((contDiff_two_norm_rpow hr).contDiffAt)]
  set c := σ / realFactorial r
  have hc : 0 ≤ c := div_nonneg hσ (realFactorial_pos r).le
  have hK : 0 ≤ r * (r - 1) * ‖s‖ ^ (r - 2) := by
    have : 0 ≤ r - 1 := by linarith
    positivity
  have key := minCurvature_ge_of_add_smul (iteratedFDeriv ℝ 2 f (x + s))
    (iteratedFDeriv ℝ 2 ((ftaylorSeries ℝ f x).taylorSum p) s)
    (iteratedFDeriv ℝ 2 (fun y : E => ‖y‖ ^ r) s) hc hK
    (fun d => by
      rw [apply_diag_eq_vec]
      exact (iteratedFDeriv_two_norm_rpow_bounds hr s d).2)
  have hcK : c * (r * (r - 1) * ‖s‖ ^ (r - 2)) = σ / realFactorial (r - 2) * ‖s‖ ^ (r - 2) := by
    have h1 := (realFactorial_pos (r - 2)).ne'
    have h2 : r ≠ 0 := by linarith
    have h3 : r - 1 ≠ 0 := by linarith
    simp only [c, realFactorial_eq_mul_mul_sub_two hr]
    field_simp
  have hT' : ‖iteratedFDeriv ℝ 2 f (x + s) -
      iteratedFDeriv ℝ 2 ((ftaylorSeries ℝ f x).taylorSum p) s‖ ≤
      H / holderFactorial (p - 2) β * ‖s‖ ^ (((p - 2 : ℕ) : ℝ) + β) := hT
  linarith

/-- **The ratio estimate (5.5.22), sharp form** ([cartis2022evaluation], proof of Lemma 5.5.3):
let `β ≥ 0`, `f` be `C^p` on a convex `C ∋ x, x + s` with `(H, β)`-Hölder `p`-th derivative there,
and let the Taylor decrement dominate the regularization term,
`0 < σ / r! ‖s‖^r ≤ T_p(x, 0) - T_p(x, s)` (Lemma 5.5.1). Then for the ratio
`ρ = (f(x) - f(x + s)) / (T_p(x, 0) - T_p(x, s))`,
`|ρ - 1| ≤ r! H / ((p + β)! σ) ‖s‖^{p + β - r}`, with `(p + β)! = holderFactorial p β`. -/
theorem abs_reductionRatio_sub_one_le_of_holder_sharp (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hβ : 0 ≤ β)
    (hH : IteratedFDerivHolderOn f p H β C) (hx : x ∈ C) (hxs : x + s ∈ C)
    (hdec : 0 < σ / realFactorial r * ‖s‖ ^ r)
    (hdec' : σ / realFactorial r * ‖s‖ ^ r ≤ (ftaylorSeries ℝ f x).taylorDecrement p s) :
    |reductionRatio f x s ((ftaylorSeries ℝ f x).taylorDecrement p s) - 1| ≤
      realFactorial r * H / (holderFactorial p β * σ) * ‖s‖ ^ ((p : ℝ) + β - r) := by
  set Δ := (ftaylorSeries ℝ f x).taylorDecrement p s
  have hrf := realFactorial_pos r
  have hΔ : 0 < Δ := hdec.trans_le hdec'
  have hs : s ≠ 0 := by
    rintro rfl
    simp [Δ] at hΔ
  have hspos : 0 < ‖s‖ := norm_pos_iff.2 hs
  have hσ : 0 < σ := by
    have := (div_pos_iff.1 (pos_of_mul_pos_left hdec (Real.rpow_nonneg hspos.le r)))
    rcases this with h | h
    · exact h.1
    · exact absurd h.2 (not_lt.2 hrf.le)
  have hT := abs_sub_taylorPolynomial_le_of_holder hC hf hβ hH hx hxs
  have hfac0 : 0 < holderFactorial p β := holderFactorial_pos _ (by linarith)
  have hH0 : 0 ≤ H := nonneg_of_abs_le_div_mul_rpow hfac0 hspos hT
  refine abs_reductionRatio_sub_one_le hΔ ?_
  have heq : f (x + s) - (f x - Δ) = f (x + s) - taylorPolynomial f p x s := by
    simp only [Δ, FormalMultilinearSeries.taylorDecrement, ← taylorPolynomial_eq_taylorSum,
      taylorPolynomial_zero_right]
    ring
  rw [heq]
  have hpow : ‖s‖ ^ ((p : ℝ) + β - r) * ‖s‖ ^ r = ‖s‖ ^ ((p : ℝ) + β) := by
    rw [← Real.rpow_add hspos]; ring_nf
  calc |f (x + s) - taylorPolynomial f p x s|
      ≤ H / holderFactorial p β * ‖s‖ ^ ((p : ℝ) + β) := hT
    _ = realFactorial r * H / (holderFactorial p β * σ) * ‖s‖ ^ ((p : ℝ) + β - r) *
          (σ / realFactorial r * ‖s‖ ^ r) := by
        rw [← hpow]; field_simp
    _ ≤ _ := by gcongr

/-- **The ratio estimate (5.5.22)** ([cartis2022evaluation], proof of Lemma 5.5.3): under
the hypotheses of `Optimization.abs_reductionRatio_sub_one_le_of_holder_sharp` and `p ≥ 1`,
`|ρ - 1| ≤ r! H / ((p - 1 + β)! σ) ‖s‖^{p + β - r}` (using `(p + β)! ≥ (p - 1 + β)!`). -/
theorem abs_reductionRatio_sub_one_le_of_holder (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hp : 1 ≤ p) (hβ : 0 ≤ β)
    (hH : IteratedFDerivHolderOn f p H β C) (hx : x ∈ C) (hxs : x + s ∈ C)
    (hdec : 0 < σ / realFactorial r * ‖s‖ ^ r)
    (hdec' : σ / realFactorial r * ‖s‖ ^ r ≤ (ftaylorSeries ℝ f x).taylorDecrement p s) :
    |reductionRatio f x s ((ftaylorSeries ℝ f x).taylorDecrement p s) - 1| ≤
      realFactorial r * H / (holderFactorial (p - 1) β * σ) * ‖s‖ ^ ((p : ℝ) + β - r) := by
  have h := abs_reductionRatio_sub_one_le_of_holder_sharp hC hf hβ hH hx hxs hdec hdec'
  have hs : s ≠ 0 := by
    rintro rfl
    have := hdec.trans_le hdec'
    simp at this
  have hspos : 0 < ‖s‖ := norm_pos_iff.2 hs
  have hrf := realFactorial_pos r
  have hσ : 0 < σ := by
    rcases div_pos_iff.1 (pos_of_mul_pos_left hdec (Real.rpow_nonneg hspos.le r)) with h | h
    · exact h.1
    · exact absurd h.2 (not_lt.2 hrf.le)
  have hH0 : 0 ≤ H := nonneg_of_abs_le_div_mul_rpow (holderFactorial_pos p (by linarith)) hspos
    (abs_sub_taylorPolynomial_le_of_holder hC hf hβ hH hx hxs)
  have hfac0 : 0 < holderFactorial (p - 1) β := holderFactorial_pos _ (by linarith)
  have hfac : holderFactorial (p - 1) β ≤ holderFactorial p β := by
    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le' hp
    rw [Nat.add_sub_cancel, holderFactorial_succ]
    refine le_mul_of_one_le_right hfac0.le ?_
    have : (0 : ℝ) ≤ q := q.cast_nonneg
    linarith
  refine h.trans ?_
  gcongr

end Estimates

section Existence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {D : FormalMultilinearSeries ℝ E ℝ} {p : ℕ} {σ r : ℝ}

/-- The Taylor sum is bounded below by `D₀ - K ‖s‖^p` outside the unit ball, with
`K = ∑_{i=1}^p ‖D_i‖ / i!`. -/
theorem taylorSum_ge_of_one_le_norm (D : FormalMultilinearSeries ℝ E ℝ) (p : ℕ) {s : E}
    (hs : 1 ≤ ‖s‖) :
    D 0 0 - (∑ i ∈ Finset.Icc 1 p, ‖D i‖ / (i ! : ℝ)) * ‖s‖ ^ p ≤ D.taylorSum p s := by
  have h1 := D.abs_taylorDecrement_le p s
  have h2 : ∑ i ∈ Finset.Icc 1 p, ‖D i‖ * ‖s‖ ^ i / i ! ≤
      (∑ i ∈ Finset.Icc 1 p, ‖D i‖ / (i ! : ℝ)) * ‖s‖ ^ p := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_assoc]
    have : ‖s‖ ^ i ≤ ‖s‖ ^ p := pow_le_pow_right₀ hs (Finset.mem_Icc.1 hi).2
    gcongr
  have h3 : D.taylorSum p s = D 0 0 - D.taylorDecrement p s := by
    rw [FormalMultilinearSeries.taylorDecrement, FormalMultilinearSeries.taylorSum_zero_right]
    ring
  rw [h3]
  linarith [le_abs_self (D.taylorDecrement p s)]

/-- **Coercivity of the model**: for `σ > 0` and `r > p`, `m(s) → ∞` as `‖s‖ → ∞`. -/
theorem tendsto_powRegularizedModel_cocompact [ProperSpace E] (hσ : 0 < σ) (hpr : (p : ℝ) < r) :
    Tendsto (powRegularizedModel D p σ r) (cocompact E) atTop := by
  set K := ∑ i ∈ Finset.Icc 1 p, ‖D i‖ / (i ! : ℝ)
  set c := σ / realFactorial r
  have hc : 0 < c := div_pos hσ (realFactorial_pos r)
  have hp0 : (0 : ℝ) ≤ p := p.cast_nonneg
  -- the lower bound `g(t) = D₀ + (c t^{r-p} - K)` for `t ≥ 1` with `c t^{r-p} ≥ K`
  have hg : Tendsto (fun t : ℝ => D 0 0 + (c * t ^ (r - p) - K)) atTop atTop :=
    tendsto_atTop_add_const_left _ _
      (tendsto_atTop_add_const_right _ _
        ((tendsto_rpow_atTop (by linarith)).const_mul_atTop hc))
  have hev : ∀ᶠ t in atTop, 1 ≤ t ∧ K ≤ c * t ^ (r - p) :=
    (eventually_ge_atTop 1).and
      (((tendsto_rpow_atTop (by linarith)).const_mul_atTop hc).eventually (eventually_ge_atTop K))
  have hlow : ∀ᶠ s in cocompact E,
      D 0 0 + (c * ‖s‖ ^ (r - p) - K) ≤ powRegularizedModel D p σ r s := by
    filter_upwards [tendsto_norm_cocompact_atTop.eventually hev] with s ⟨hs1, hsK⟩
    have hT := taylorSum_ge_of_one_le_norm D p hs1
    have hspos : 0 < ‖s‖ := one_pos.trans_le hs1
    have hpow : ‖s‖ ^ r = ‖s‖ ^ p * ‖s‖ ^ (r - p) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hspos]; ring_nf
    have hsp : 1 ≤ ‖s‖ ^ p := one_le_pow₀ hs1
    rw [powRegularizedModel_def, hpow]
    have : (c * ‖s‖ ^ (r - p) - K) ≤ ‖s‖ ^ p * (c * ‖s‖ ^ (r - p) - K) :=
      le_mul_of_one_le_left (by linarith) hsp
    change D 0 0 + (c * ‖s‖ ^ (r - p) - K) ≤ D.taylorSum p s + c * (‖s‖ ^ p * ‖s‖ ^ (r - p))
    nlinarith
  exact tendsto_atTop_mono' _ hlow (hg.comp tendsto_norm_cocompact_atTop)

/-- **Global minimizers of the model** ([cartis2022evaluation], Algorithm 5.5.1, Step 1): in
finite dimension, for `σ > 0` and `r > max p 1`, the model has a global minimizer `s*`, at which
`∇m(s*) = 0`, `λ_min[∇²m(s*)] ≥ 0` if `r ≥ 2`, and `m(s*) < m(0)` unless `0` is itself a global
minimizer. -/
theorem exists_isMinOn_powRegularizedModel [FiniteDimensional ℝ E] (hσ : 0 < σ)
    (hpr : (p : ℝ) < r) (hr : 1 < r) :
    ∃ s, IsMinOn (powRegularizedModel D p σ r) univ s ∧
      fderiv ℝ (powRegularizedModel D p σ r) s = 0 ∧
      (2 ≤ r → 0 ≤ minCurvature (iteratedFDeriv ℝ 2 (powRegularizedModel D p σ r) s)) ∧
      (¬ IsMinOn (powRegularizedModel D p σ r) univ 0 →
        powRegularizedModel D p σ r s < powRegularizedModel D p σ r 0) := by
  have := FiniteDimensional.proper_real E
  obtain ⟨s, hs⟩ := (continuous_powRegularizedModel D p σ r (by linarith)).exists_forall_le
    (tendsto_powRegularizedModel_cocompact hσ hpr)
  have hmin : IsMinOn (powRegularizedModel D p σ r) univ s := fun y _ => hs y
  refine ⟨s, hmin, (hmin.isLocalMin univ_mem).fderiv_eq_zero, fun h2 =>
    IsLocalMin.minCurvature_iteratedFDeriv_two_nonneg (hmin.isLocalMin univ_mem)
      (contDiff_two_powRegularizedModel h2).contDiffAt,
    fun h0 => ?_⟩
  refine lt_of_le_of_ne (hs 0) fun heq => h0 fun y _ => ?_
  rw [← heq]
  exact hs y

end Existence

end Optimization
