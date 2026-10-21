import Numlib.Optimization.HigherOrderRegularizationSmoothness
import Numlib.Analysis.Calculus.NormPowDerivatives
import Numlib.Optimization.HigherOrderRegularizationRun
import Numlib.Optimization.RegularizedTaylorCurvature

/-!
# Derivative transfer and decrease for regularized Taylor steps

The actual model derivative residuals transfer to the objective by subtracting the
Taylor remainder and the radial regularizer. The resulting criticality bounds imply
real-power objective decrease estimates on every accepted executed trial.
-/

noncomputable section
open scoped Nat ContDiff
namespace Optimization.HigherOrderRegularization
open RegularizedTaylorModel ParameterUpdates

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Coefficient controlling a derivative of order `j` at an accepted trial point. -/
def criticalityConstant (p j : ℕ) (L S theta : ℝ) : ℝ :=
  (L + S) / ((p - j + 1)! : ℝ) + theta

/-- The reciprocal coefficient has the factorial fraction used for step lower bounds. -/
theorem inv_criticalityConstant (p j : ℕ) (L S theta : ℝ) :
    (criticalityConstant p j L S theta)⁻¹ =
      ((p - j + 1)! : ℝ) / (L + S + theta * ((p - j + 1)! : ℝ)) := by
  unfold criticalityConstant
  rw [div_add', inv_div]
  all_goals positivity

/-- A positive residual allowance makes the criticality coefficient positive. -/
theorem criticalityConstant_pos {p j : ℕ} {L S theta : ℝ}
    (hL : 0 ≤ L) (hS : 0 ≤ S) (ht : 0 < theta) :
    0 < criticalityConstant p j L S theta := by
  unfold criticalityConstant
  exact add_pos_of_nonneg_of_pos (div_nonneg (add_nonneg hL hS) (by positivity)) ht

/-- The model derivative is the Taylor derivative plus the actual radial derivative.
Only smoothness of the radial power at the nonzero computed step is used. -/
theorem iteratedFDeriv_model {f : E → ℝ} {p j : ℕ} {x s : E} {sigma : ℝ}
    (hs : s ≠ 0) :
    iteratedFDeriv ℝ j (model f p x sigma) s =
      iteratedFDeriv ℝ j (taylorModel f p x) s +
      (sigma / ((p + 1)! : ℝ)) •
        iteratedFDeriv ℝ j (fun z : E ↦ ‖z‖ ^ (p + 1)) s := by
  have hrad : ContDiffAt ℝ j (fun z : E ↦ ‖z‖ ^ (p + 1)) s :=
    (contDiffAt_norm ℝ hs).pow _
  unfold model
  change iteratedFDeriv ℝ j (taylorModel f p x +
    (sigma / ((p + 1)! : ℝ)) • (fun z : E ↦ ‖z‖ ^ (p + 1))) s = _
  calc
    _ = iteratedFDeriv ℝ j (taylorModel f p x) s +
        iteratedFDeriv ℝ j ((sigma / ((p + 1)! : ℝ)) •
          (fun z : E ↦ ‖z‖ ^ (p + 1))) s :=
      iteratedFDeriv_add_apply (contDiff_taylorModel f p x j).contDiffAt
        (hrad.const_smul (sigma / ((p + 1)! : ℝ)))
    _ = _ := by rw [iteratedFDeriv_const_smul_apply hrad]

/-- Factorial form of the sharp radial tensor estimates through order three. -/
theorem norm_iteratedFDeriv_norm_pow_le {p j : ℕ} {s : E}
    (hj : 1 ≤ j) (hj3 : j ≤ 3) (hp : j ≤ p) (hs : s ≠ 0) :
    ‖iteratedFDeriv ℝ j (fun z : E ↦ ‖z‖ ^ (p + 1)) s‖ ≤
      ((p + 1)! : ℝ) / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) := by
  interval_cases j
  · have h := norm_iteratedFDeriv_one_norm_pow_le hp s
    have he : p - 1 + 1 = p := by omega
    rw [he, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      mul_div_cancel_right₀ _ (by positivity : (p ! : ℝ) ≠ 0)]
    exact h
  · obtain ⟨n, rfl⟩ : ∃ n, p = n + 2 := ⟨p - 2, by omega⟩
    have h := norm_iteratedFDeriv_two_norm_pow_le (by omega : 2 ≤ n + 2) s
    have he : n + 2 - 2 + 1 = n + 1 := by omega
    have he' : n + 2 - 1 = n + 1 := by omega
    rw [he, Nat.factorial_succ (n + 2), Nat.factorial_succ (n + 1)]
    push_cast
    rw [he'] at h
    push_cast at h
    convert h using 1
    field_simp
    ring
  · obtain ⟨n, rfl⟩ : ∃ n, p = n + 3 := ⟨p - 3, by omega⟩
    have h := norm_iteratedFDeriv_three_norm_pow_le (by omega : 3 ≤ n + 3) hs
    have he : n + 3 - 3 + 1 = n + 1 := by omega
    have he' : n + 3 - 2 = n + 1 := by omega
    rw [he, Nat.factorial_succ (n + 3), Nat.factorial_succ (n + 2),
      Nat.factorial_succ (n + 1)]
    push_cast
    rw [he'] at h
    push_cast at h
    convert h using 1
    field_simp
    ring

/-- Remainder and radial operator bounds control the difference between the actual
objective and actual regularized model derivatives. -/
theorem norm_derivative_sub_model_le {f : E → ℝ} {p j : ℕ} {x s : E}
    {L sigma S : ℝ} (hs : s ≠ 0) (hsigma : 0 ≤ sigma) (hS : sigma ≤ S)
    (hrem : ‖iteratedFDeriv ℝ j f (x + s) -
      iteratedFDeriv ℝ j (taylorModel f p x) s‖ ≤
        L / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1))
    (hrad : ‖iteratedFDeriv ℝ j (fun z : E ↦ ‖z‖ ^ (p + 1)) s‖ ≤
      ((p + 1)! : ℝ) / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1)) :
    ‖iteratedFDeriv ℝ j f (x + s) - iteratedFDeriv ℝ j (model f p x sigma) s‖ ≤
      (L + S) / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) := by
  rw [iteratedFDeriv_model hs, ← sub_sub]
  have hn : 0 ≤ sigma / ((p + 1)! : ℝ) := div_nonneg hsigma (by positivity)
  calc
    _ ≤ ‖iteratedFDeriv ℝ j f (x + s) -
      iteratedFDeriv ℝ j (taylorModel f p x) s‖ +
      ‖(sigma / ((p + 1)! : ℝ)) •
        iteratedFDeriv ℝ j (fun z : E ↦ ‖z‖ ^ (p + 1)) s‖ := norm_sub_le _ _
    _ ≤ L / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) +
      sigma / ((p + 1)! : ℝ) *
        (((p + 1)! : ℝ) / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1)) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hn]
      exact add_le_add hrem (mul_le_mul_of_nonneg_left hrad hn)
    _ = (L + sigma) / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (add_le_add_right hS L) (by positivity)) (by positivity)

/-- A diagonal evaluation at a unit vector is bounded by the tensor operator norm. -/
theorem abs_diagonal_le_norm {j : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ E) ℝ) {d : E} (hd : ‖d‖ = 1) :
    |A (fun _ ↦ d)| ≤ ‖A‖ := by
  simpa [Real.norm_eq_abs, hd] using A.le_opNorm (fun _ ↦ d)

/-- An actual tensor difference bound transfers an absolute residual in any unit direction. -/
theorem abs_diagonal_le_of_model {f g : E → ℝ} {j : ℕ} {y s d : E} {B R : ℝ}
    (hd : ‖d‖ = 1)
    (hB : ‖iteratedFDeriv ℝ j f y - iteratedFDeriv ℝ j g s‖ ≤ B)
    (hR : |iteratedFDeriv ℝ j g s (fun _ ↦ d)| ≤ R) :
    |iteratedFDeriv ℝ j f y (fun _ ↦ d)| ≤ B + R := by
  have hdiff := (abs_diagonal_le_norm
    (iteratedFDeriv ℝ j f y - iteratedFDeriv ℝ j g s) hd).trans hB
  have htri : |iteratedFDeriv ℝ j f y (fun _ ↦ d)| ≤
      |iteratedFDeriv ℝ j f y (fun _ ↦ d) - iteratedFDeriv ℝ j g s (fun _ ↦ d)| +
      |iteratedFDeriv ℝ j g s (fun _ ↦ d)| := by
    simpa using abs_add_le (iteratedFDeriv ℝ j f y (fun _ ↦ d) -
      iteratedFDeriv ℝ j g s (fun _ ↦ d)) (iteratedFDeriv ℝ j g s (fun _ ↦ d))
  exact htri.trans (add_le_add hdiff hR)

/-- Tensor error and a model curvature lower bound transfer to least objective curvature. -/
theorem neg_leastCurvature_le_of_model [Nontrivial E]
    {f g : E → ℝ} {y s : E} {B R : ℝ}
    (hdiff : ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 g s‖ ≤ B)
    (hmodel : -R ≤ leastCurvature (fderiv ℝ (fderiv ℝ g) s)) :
    -leastCurvature (fderiv ℝ (fderiv ℝ f) y) ≤ B + R := by
  have hh : -(B + R) ≤ leastCurvature (fderiv ℝ (fderiv ℝ f) y) := by
    apply (le_leastCurvature_iff _ _).mpr
    intro u
    have hM := (le_leastCurvature_iff _ _).mp hmodel u
    have hA := (iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 g s).le_opNorm (fun _ ↦ u)
    have hA' : |fderiv ℝ (fderiv ℝ f) y u u - fderiv ℝ (fderiv ℝ g) s u u| ≤
        B * ‖u‖ ^ 2 := by
      simpa [sub_apply, iteratedFDeriv_two_apply,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, Real.norm_eq_abs] using
        hA.trans (mul_le_mul_of_nonneg_right hdiff (by positivity))
    have hl := (abs_le.mp hA').1
    nlinarith
  linarith

section Finite
variable [FiniteDimensional ℝ E]
variable {params : RegularizationParameters} {q p N : ℕ} {theta epsilon : Fin 3 → ℝ}
  {f : E → ℝ} {x s : ℕ → E} {sigma : ℕ → ℝ} {L S : ℝ}

/-- The actual model and objective tensors differ by the sharp factorial coefficient. -/
theorem RunPrefix.derivative_difference (h : RunPrefix params q p theta epsilon f x s sigma N)
    (hf : DiagonalLipschitz f p L) {j k : ℕ} (hj : 1 ≤ j) (hj3 : j ≤ 3)
    (hp : j ≤ p) (hk : k < N) (hS : sigma k ≤ S) :
    ‖iteratedFDeriv ℝ j f (x k + s k) -
      iteratedFDeriv ℝ j (model f p (x k) (sigma k)) (s k)‖ ≤
      (L + S) / ((p - j + 1)! : ℝ) * ‖s k‖ ^ (p - j + 1) :=
  norm_derivative_sub_model_le (h.toTrialPrefix.step_ne_zero hk)
    (h.toTrialPrefix.toRegularizationPrefix.pos (by omega)).le hS
    (hf.derivative_remainder (h.order_pos.trans h.degree_ge_order) hp _ _)
    (norm_iteratedFDeriv_norm_pow_le hj hj3 hp (h.toTrialPrefix.step_ne_zero hk))

/-- Every accepted executed step controls the successor first derivative. -/
theorem RunPrefix.gradient_bound (h : RunPrefix params q p theta epsilon f x s sigma N)
    (hf : DiagonalLipschitz f p L) {k : ℕ} (hk : k < N)
    (hs : params.eta1 ≤ ratio f p (x k) (s k)) (hS : sigma k ≤ S) :
    ‖fderiv ℝ f (x (k + 1))‖ ≤ criticalityConstant p 1 L S (theta 0) * ‖s k‖ ^ p := by
  have hp : 1 ≤ p := h.order_pos.trans h.degree_ge_order
  have he : p - 1 + 1 = p := by omega
  have hd := h.derivative_difference hf (j := 1) (by omega) (by omega) hp hk hS
  have hb : ‖iteratedFDeriv ℝ 1 f (x k + s k)‖ ≤
      (L + S) / (p ! : ℝ) * ‖s k‖ ^ p + theta 0 * ‖s k‖ ^ p := by
    have hh : ‖iteratedFDeriv ℝ 1 f (x k + s k)‖ ≤
        ‖iteratedFDeriv ℝ 1 f (x k + s k) -
        iteratedFDeriv ℝ 1 (model f p (x k) (sigma k)) (s k)‖ +
        ‖iteratedFDeriv ℝ 1 (model f p (x k) (sigma k)) (s k)‖ := by
      simpa using norm_add_le
        (iteratedFDeriv ℝ 1 f (x k + s k) -
          iteratedFDeriv ℝ 1 (model f p (x k) (sigma k)) (s k))
        (iteratedFDeriv ℝ 1 (model f p (x k) (sigma k)) (s k))
    exact hh.trans (add_le_add (by simpa [he] using hd)
      (by simpa using (h.residuals k hk).first))
  rw [h.iterate k hk, ite_eq_left hs]
  simpa [criticalityConstant, he, add_mul] using hb

/-- Activated second-order residuals control negative successor Hessian curvature. -/
theorem RunPrefix.curvature_bound [Nontrivial E]
    (h : RunPrefix params q p theta epsilon f x s sigma N)
    (hf : DiagonalLipschitz f p L) (hq : 2 ≤ q) {k : ℕ} (hk : k < N)
    (hs : params.eta1 ≤ ratio f p (x k) (s k)) (hS : sigma k ≤ S) :
    max 0 (-leastCurvature (fderiv ℝ (fderiv ℝ f) (x (k + 1)))) ≤
      criticalityConstant p 2 L S (theta 1) * ‖s k‖ ^ (p - 1) := by
  have hp : 2 ≤ p := hq.trans h.degree_ge_order
  have he : p - 2 + 1 = p - 1 := by omega
  have hd := h.derivative_difference hf (j := 2) (by omega) (by omega) hp hk hS
  have ht := neg_leastCurvature_le_of_model hd ((h.residuals k hk).second hq)
  have hS0 : 0 ≤ S := (h.toTrialPrefix.toRegularizationPrefix.pos (by omega)).le.trans hS
  have hC := (criticalityConstant_pos (p := p) (j := 2) hf.nonneg hS0 (h.theta_pos 1)).le
  rw [h.iterate k hk, ite_eq_left hs]
  apply max_le (mul_nonneg hC (by positivity))
  simpa [criticalityConstant, he, add_mul] using ht

/-- Along every model flat direction both the cubic objective derivative and the
absolute objective Hessian are small, with their respective sharp constants. -/
theorem RunPrefix.flat_direction_bounds
    (h : RunPrefix params q p theta epsilon f x s sigma N)
    (hf : DiagonalLipschitz f p L) (hq : 3 ≤ q) {k : ℕ} (hk : k < N)
    (hs : params.eta1 ≤ ratio f p (x k) (s k)) (hS : sigma k ≤ S)
    {d : E} (hd : d ∈ smallCurvatureDirections (model f p (x k) (sigma k)) (s k)
      (theta 1 * ‖s k‖ ^ (p - 1))) :
    |iteratedFDeriv ℝ 3 f (x (k + 1)) (fun _ ↦ d)| ≤
      criticalityConstant p 3 L S (theta 2) * ‖s k‖ ^ (p - 2) ∧
    |iteratedFDeriv ℝ 2 f (x (k + 1)) (fun _ ↦ d)| ≤
      criticalityConstant p 2 L S (theta 1) * ‖s k‖ ^ (p - 1) := by
  have hp : 3 ≤ p := hq.trans h.degree_ge_order
  have he2 : p - 2 + 1 = p - 1 := by omega
  have he3 : p - 3 + 1 = p - 2 := by omega
  rw [h.iterate k hk, ite_eq_left hs]
  constructor
  · have hb := abs_diagonal_le_of_model hd.1
      (h.derivative_difference hf (j := 3) (by omega) (by omega) hp hk hS)
      ((h.residuals k hk).third hq d hd)
    simpa [criticalityConstant, he3, add_mul] using hb
  · have hb := abs_diagonal_le_of_model hd.1
      (h.derivative_difference hf (j := 2) (by omega) (by omega) (by omega) hk hS) hd.2
    simpa [criticalityConstant, he2, add_mul] using hb

end Finite

/-- The successful decrease coefficient associated with derivative order `j`. -/
def decreaseConstant (params : RegularizationParameters) (p j : ℕ)
    (L S theta : ℝ) : ℝ :=
  params.eta1 * params.sigmaMin / ((p + 1)! : ℝ) *
    (criticalityConstant p j L S theta)⁻¹ ^ (((p + 1 : ℕ) : ℝ) / (p - j + 1 : ℕ))

/-- The decrease coefficient is exactly the factorial-normalized source expression. -/
theorem decreaseConstant_eq_factorial (params : RegularizationParameters) (p j : ℕ)
    (L S theta : ℝ) :
    decreaseConstant params p j L S theta =
      params.eta1 * params.sigmaMin / ((p + 1)! : ℝ) *
      (((p - j + 1)! : ℝ) / (L + S + theta * ((p - j + 1)! : ℝ))) ^
        (((p + 1 : ℕ) : ℝ) / (p - j + 1 : ℕ)) := by
  rw [decreaseConstant, inv_criticalityConstant]

/-- Raising a positive-integer step bound gives the real-power decrease estimate. -/
theorem rpow_measure_le_step_power {a C t : ℝ} {m r : ℕ}
    (ha : 0 ≤ a) (hC : 0 < C) (ht : 0 ≤ t) (hm : 0 < m)
    (h : a ≤ C * t ^ m) :
    C⁻¹ ^ ((r : ℝ) / m) * a ^ ((r : ℝ) / m) ≤ t ^ r := by
  have hdiv : C⁻¹ * a ≤ t ^ m := by
    rw [← div_eq_inv_mul, div_le_iff₀ hC]
    simpa [mul_comm] using h
  have hpow := Real.rpow_le_rpow (mul_nonneg (inv_nonneg.mpr hC.le) ha) hdiv
    (by positivity : 0 ≤ (r : ℝ) / m)
  rw [Real.mul_rpow (inv_nonneg.mpr hC.le) ha,
    ← Real.rpow_natCast t m, ← Real.rpow_mul ht] at hpow
  have he : (m : ℝ) * ((r : ℝ) / m) = r := by
    field_simp
  simpa [he, Real.rpow_natCast] using hpow

/-- Actual acceptance and the regularization floor imply a positive multiple of step power. -/
theorem TrialPrefix.accepted_decrease_step {params : RegularizationParameters}
    {p N : ℕ} {f : E → ℝ} {x s : ℕ → E} {sigma : ℕ → ℝ}
    (h : TrialPrefix params p f x s sigma N) {k : ℕ} (hk : k < N)
    (hs : params.eta1 ≤ ratio f p (x k) (s k)) :
    params.eta1 * params.sigmaMin / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) ≤
      f (x k) - f (x (k + 1)) := by
  have hfloor := h.toRegularizationPrefix.lower (by omega : k ≤ N)
  have hp := h.predicted_decrease hk
  have ha := h.accepted_decrease hk hs
  calc
    _ ≤ params.eta1 * (sigma k / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1)) := by
      rw [mul_div_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right hfloor (by positivity)) (by positivity)) params.eta1_pos.le
    _ ≤ _ := (mul_le_mul_of_nonneg_left hp params.eta1_pos.le).trans ha

/-- Every criticality decrease coefficient is strictly positive. -/
theorem decreaseConstant_pos (params : RegularizationParameters) (p j : ℕ)
    {L S theta : ℝ} (hL : 0 ≤ L) (hS : 0 ≤ S) (ht : 0 < theta) :
    0 < decreaseConstant params p j L S theta := by
  unfold decreaseConstant
  exact mul_pos (div_pos (mul_pos params.eta1_pos params.sigmaMin_pos) (by positivity))
    (Real.rpow_pos_of_pos (inv_pos.mpr (criticalityConstant_pos hL hS ht)) _)

/-- Criticality transfer converts actual accepted step decrease into a real-power bound. -/
theorem TrialPrefix.accepted_decrease_of_criticality {params : RegularizationParameters}
    {p j N : ℕ} {f : E → ℝ} {x s : ℕ → E} {sigma : ℕ → ℝ}
    (h : TrialPrefix params p f x s sigma N) {k : ℕ} (hk : k < N)
    (hs : params.eta1 ≤ ratio f p (x k) (s k)) {L S theta a : ℝ}
    (ha : 0 ≤ a) (hC : 0 < criticalityConstant p j L S theta)
    (hb : a ≤ criticalityConstant p j L S theta * ‖s k‖ ^ (p - j + 1)) :
    decreaseConstant params p j L S theta * a ^
      (((p + 1 : ℕ) : ℝ) / (p - j + 1 : ℕ)) ≤ f (x k) - f (x (k + 1)) := by
  have hp := rpow_measure_le_step_power ha hC (norm_nonneg (s k))
    (by omega : 0 < p - j + 1) hb (r := p + 1)
  calc
    _ = params.eta1 * params.sigmaMin / ((p + 1)! : ℝ) *
      ((criticalityConstant p j L S theta)⁻¹ ^ (((p + 1 : ℕ) : ℝ) / (p - j + 1 : ℕ)) *
      a ^ (((p + 1 : ℕ) : ℝ) / (p - j + 1 : ℕ))) := by
      unfold decreaseConstant
      ring
    _ ≤ params.eta1 * params.sigmaMin / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) :=
      mul_le_mul_of_nonneg_left hp
        (div_nonneg (mul_nonneg params.eta1_pos.le params.sigmaMin_pos.le) (by positivity))
    _ ≤ _ := h.accepted_decrease_step hk hs

section FiniteDecrease
variable [FiniteDimensional ℝ E]
variable {params : RegularizationParameters} {q p N : ℕ} {theta epsilon : Fin 3 → ℝ}
  {f : E → ℝ} {x s : ℕ → E} {sigma : ℕ → ℝ} {L S : ℝ}

/-- Accepted objective decrease in terms of the successor first derivative. -/
theorem RunPrefix.gradient_decrease
    (h : RunPrefix params q p theta epsilon f x s sigma N)
    (hf : DiagonalLipschitz f p L) {k : ℕ} (hk : k < N)
    (hs : params.eta1 ≤ ratio f p (x k) (s k)) (hS : sigma k ≤ S) :
    decreaseConstant params p 1 L S (theta 0) *
      ‖fderiv ℝ f (x (k + 1))‖ ^ (((p + 1 : ℕ) : ℝ) / p) ≤
        f (x k) - f (x (k + 1)) := by
  have hp : 1 ≤ p := h.order_pos.trans h.degree_ge_order
  have he : p - 1 + 1 = p := by omega
  have hS0 : 0 ≤ S := (h.toRegularizationPrefix.pos (by omega)).le.trans hS
  have hC := criticalityConstant_pos (p := p) (j := 1) hf.nonneg hS0 (h.theta_pos 0)
  have hb := h.gradient_bound hf hk hs hS
  simpa only [he] using h.toTrialPrefix.accepted_decrease_of_criticality hk hs
    (j := 1) (L := L) (S := S) (theta := theta 0) (norm_nonneg _) hC
    (by simpa only [he] using hb)

/-- Accepted objective decrease in terms of successor negative curvature. -/
theorem RunPrefix.curvature_decrease [Nontrivial E]
    (h : RunPrefix params q p theta epsilon f x s sigma N)
    (hf : DiagonalLipschitz f p L) (hq : 2 ≤ q) {k : ℕ} (hk : k < N)
    (hs : params.eta1 ≤ ratio f p (x k) (s k)) (hS : sigma k ≤ S) :
    decreaseConstant params p 2 L S (theta 1) *
      (max 0 (-leastCurvature (fderiv ℝ (fderiv ℝ f) (x (k + 1))))) ^
        (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ)) ≤ f (x k) - f (x (k + 1)) := by
  have hp : 2 ≤ p := hq.trans h.degree_ge_order
  have he : p - 2 + 1 = p - 1 := by omega
  have hS0 : 0 ≤ S := (h.toRegularizationPrefix.pos (by omega)).le.trans hS
  have hC := criticalityConstant_pos (p := p) (j := 2) hf.nonneg hS0 (h.theta_pos 1)
  have hb := h.curvature_bound hf hq hk hs hS
  simpa only [he] using h.toTrialPrefix.accepted_decrease_of_criticality hk hs
    (j := 2) (L := L) (S := S) (theta := theta 1) (le_max_left _ _) hC
    (by simpa only [he] using hb)

/-- Accepted objective decrease in terms of each cubic derivative on model flat directions. -/
theorem RunPrefix.cubic_decrease
    (h : RunPrefix params q p theta epsilon f x s sigma N)
    (hf : DiagonalLipschitz f p L) (hq : 3 ≤ q) {k : ℕ} (hk : k < N)
    (hs : params.eta1 ≤ ratio f p (x k) (s k)) (hS : sigma k ≤ S)
    {d : E} (hd : d ∈ smallCurvatureDirections (model f p (x k) (sigma k)) (s k)
      (theta 1 * ‖s k‖ ^ (p - 1))) :
    decreaseConstant params p 3 L S (theta 2) *
      |iteratedFDeriv ℝ 3 f (x (k + 1)) (fun _ ↦ d)| ^
        (((p + 1 : ℕ) : ℝ) / (p - 2 : ℕ)) ≤ f (x k) - f (x (k + 1)) := by
  have hp : 3 ≤ p := hq.trans h.degree_ge_order
  have he : p - 3 + 1 = p - 2 := by omega
  have hS0 : 0 ≤ S := (h.toRegularizationPrefix.pos (by omega)).le.trans hS
  have hC := criticalityConstant_pos (p := p) (j := 3) hf.nonneg hS0 (h.theta_pos 2)
  have hb := (h.flat_direction_bounds hf hq hk hs hS hd).1
  simpa only [he] using h.toTrialPrefix.accepted_decrease_of_criticality hk hs
    (j := 3) (L := L) (S := S) (theta := theta 2) (abs_nonneg _) hC
    (by simpa only [he] using hb)

/-- Accepted objective decrease in terms of absolute Hessian curvature on model flat directions. -/
theorem RunPrefix.flat_hessian_decrease
    (h : RunPrefix params q p theta epsilon f x s sigma N)
    (hf : DiagonalLipschitz f p L) (hq : 3 ≤ q) {k : ℕ} (hk : k < N)
    (hs : params.eta1 ≤ ratio f p (x k) (s k)) (hS : sigma k ≤ S)
    {d : E} (hd : d ∈ smallCurvatureDirections (model f p (x k) (sigma k)) (s k)
      (theta 1 * ‖s k‖ ^ (p - 1))) :
    decreaseConstant params p 2 L S (theta 1) *
      |iteratedFDeriv ℝ 2 f (x (k + 1)) (fun _ ↦ d)| ^
        (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ)) ≤ f (x k) - f (x (k + 1)) := by
  have hp : 3 ≤ p := hq.trans h.degree_ge_order
  have he : p - 2 + 1 = p - 1 := by omega
  have hS0 : 0 ≤ S := (h.toRegularizationPrefix.pos (by omega)).le.trans hS
  have hC := criticalityConstant_pos (p := p) (j := 2) hf.nonneg hS0 (h.theta_pos 1)
  have hb := (h.flat_direction_bounds hf hq hk hs hS hd).2
  simpa only [he] using h.toTrialPrefix.accepted_decrease_of_criticality hk hs
    (j := 2) (L := L) (S := S) (theta := theta 1) (abs_nonneg _) hC
    (by simpa only [he] using hb)

end FiniteDecrease

end Optimization.HigherOrderRegularization
