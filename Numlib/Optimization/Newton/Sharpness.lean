import Numlib.Approximation.Hermite.OrderBounds
import Numlib.Analysis.Calculus.TaylorModel.Scalar
import Numlib.Optimization.Sharpness.Curvature
import Mathlib.Tactic

/-!
# Positive-curvature lower bounds for Newton and second-order trust-region methods

A fixed-width Hermite chain has gradient `-2` and Hessian `1` at each
nonterminal node. Its last gradient is `-1`. Scaling its argument by `1/ε` and
its value by `ε²` gives steps `2ε`, preterminal gradient magnitude `2ε`, and a
terminal gradient magnitude `ε`. Positive derivative bounds are independent of
the unscaled function values, so the scaled Hessian and objective budgets are
uniform before the accuracy is chosen.

The actual objective drop is `4ε²`, twice the true quadratic prediction.
Every Newton step is therefore a legal very successful TR2 step with fixed
radius two. The construction uses one real dimension and includes both finite
and disabled second-order stopping tests. The Hessian is globally Lipschitz for
each objective; its Lipschitz constant may depend on the accuracy.
-/

open Polynomial Set
namespace NewtonMinimization

/-- A genuine finite Newton trace with the actual gradient and Hessian. -/
structure Run {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (x s : ℕ → E) (ε : ℝ) (N : ℕ) : Prop where
  accuracy_pos : 0 < ε
  not_terminated : ∀ k < N, ε < ‖gradient f (x k)‖
  positive_hessian : ∀ k < N, ∀ v : E, v ≠ 0 →
    0 < inner ℝ (TaylorModel.hessianOperator f (x k) v) v
  newton_equation : ∀ k < N, TaylorModel.hessianOperator f (x k) (s k) = -gradient f (x k)
  step : ∀ k < N, x (k + 1) = x k + s k

/-- Objective values are returned at initialization and each accepted Newton endpoint. -/
def functionEvaluations (N : ℕ) : ℕ := N + 1

/-- Newton checks the gradient at every iterate, including the terminal one. -/
def gradientEvaluations (N : ℕ) : ℕ := N + 1

/-- Newton evaluates a Hessian only when its gradient stopping test fails. -/
def hessianEvaluations (N : ℕ) : ℕ := N

namespace Sharpness

/-- Number of trials: one more than the source ceiling. -/
noncomputable def horizon (ε : ℝ) : ℕ := ⌈1 / ε ^ 2⌉₊ + 1

/-- Unscaled interpolation nodes at a fixed spacing of two. -/
def basePoint (k : ℕ) : ℝ := 2 * k

/-- Actual Newton and TR2 iterates, starting at the origin. -/
def point (ε : ℝ) (k : ℕ) : ℝ := 2 * k * ε

/-- Unscaled prescribed values, first derivatives, and second derivatives. -/
noncomputable def baseJet (N k j : ℕ) : ℝ :=
  if j = 0 then 4 * (N - k : ℕ) else
    if j = 1 then if k<N then - 2 else - 1 else if j = 2 then 1 else 0

/-- Each nonterminal initial Hermite polynomial is the prescribed convex quadratic. -/
theorem initialPolynomial_baseJet {N k : ℕ} (hk : k < N) :
    Hermite.initialPolynomial 2 (baseJet N k) =
      C (baseJet N k 0) + C (-2) * X + C (1 / 2) * X ^ 2 := by
  norm_num [Hermite.initialPolynomial, Hermite.jetPoly, Finset.sum_range_succ, baseJet, hk]

/-- Every endpoint residual has the same fixed normalized bound. -/
theorem baseJet_residual {N k j : ℕ} (hk : k < N) (hj : j ≤ 2) :
    |baseJet N (k + 1) j - (derivative^[j] (Hermite.initialPolynomial 2 (baseJet N k))).eval 2| ≤
      2 * (2: ℝ) ^ (2 - j + 1) := by
  have hn : ((N - k : ℕ) : ℝ) = ((N - (k + 1) : ℕ) : ℝ) + 1 := by
    have hh : N - k = N - (k + 1) + 1 := by omega
    exact_mod_cast hh
  rw [initialPolynomial_baseJet hk]
  interval_cases j
  · norm_num [baseJet]
    rw [hn]
    ring_nf
    norm_num
  · by_cases hk1 : k + 1<N <;> norm_num [baseJet, hk1]
  · norm_num [baseJet]

/-- All positive jets, steps, and endpoint residuals have bounds independent of the chain length. -/
theorem uniform_base_data (N : ℕ) :
    (∀ i j, i<j → j ≤ N → basePoint i<basePoint j) ∧
    (∀ k ≤ N, ∀ j, 1 ≤ j → j ≤ 2 → |baseJet N k j| ≤ 2) ∧
    (∀ k<N, basePoint (k + 1) - basePoint k ≤ 2) ∧
    (∀ k<N, ∀ j ≤ 2,
      |baseJet N (k + 1) j - (derivative^[j] (Hermite.initialPolynomial 2 (baseJet N k))).eval
        (basePoint (k + 1) - basePoint k)| ≤
          2 * (basePoint (k + 1) - basePoint k) ^ (2 - j + 1)) ∧
    (∀ k ≤ N, |baseJet N k 0| ≤ 4 * N) := by
  have hstep (k : ℕ) : basePoint (k + 1) - basePoint k = 2 := by
    simp only [basePoint, Nat.cast_add, Nat.cast_one]
    ring
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i j hij _
    dsimp [basePoint]
    exact mul_lt_mul_of_pos_left (by exact_mod_cast hij) (by norm_num)
  · intro k hk j hj hj2
    interval_cases j <;> by_cases hkn : k<N <;> norm_num [baseJet, hkn]
  · intro k _
    rw [hstep]
  · intro k hk j hj
    rw [hstep]
    exact baseJet_residual hk hj
  · intro k hk
    simp only [baseJet, ite_true]
    rw [abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast (Nat.sub_le N k)) (by norm_num)

/-- Scale arguments and values so positive Hessians remain unchanged. -/
noncomputable def scaleObjective (ε : ℝ) (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  ε ^ 2 * F (ε⁻¹ * x)

/-- Exact scaling of every actual finite derivative. -/
theorem iteratedDeriv_scaleObjective {F : ℝ → ℝ} {p j : ℕ} (hf : ContDiff ℝ p F)
    (hj : j ≤ p) (ε x : ℝ) :
    iteratedDeriv j (scaleObjective ε F) x =
      ε ^ 2 * ε⁻¹ ^ j * iteratedDeriv j F (ε⁻¹ * x) := by
  unfold scaleObjective
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_comp_const_mul
    (hf.of_le (by exact_mod_cast hj))]
  ring

/-- Scalar rescaling preserves finite continuous differentiability. -/
theorem scaleObjective_contDiff {F : ℝ → ℝ} {p : ℕ} (hf : ContDiff ℝ p F) (ε : ℝ) :
    ContDiff ℝ p (scaleObjective ε F) :=
  contDiff_const.mul (hf.comp (contDiff_const.mul contDiff_id))


/-- Actual values and derivatives used by the positive-curvature lower-bound family. -/
structure Data (f : ℝ → ℝ) (ε : ℝ) (N : ℕ) : Prop where
  regularity : ContDiff ℝ 2 f
  values : ∀ k ≤ N, f (point ε k) = 4 * ε ^ 2 * (N - k : ℕ)
  first : ∀ k ≤ N, deriv f (point ε k) = if k<N then - 2 * ε else - ε
  second : ∀ k ≤ N, iteratedDeriv 2 f (point ε k) = 1

/-- A scalar Hessian is multiplication by its actual second derivative. -/
theorem hessianOperator_real (f : ℝ → ℝ) (x v : ℝ) :
    TaylorModel.hessianOperator f x v = v * iteratedDeriv 2 f x := by
  apply ext_inner_right ℝ
  intro w
  rw [TaylorModel.inner_hessianOperator, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    RCLike.inner_apply, smul_eq_mul, conj_trivial]
  ring

namespace Data
variable {f : ℝ → ℝ} {ε : ℝ} {N : ℕ}

/-- The actual scalar gradient agrees with the prescribed first derivative. -/
theorem gradient_eq (h : Data f ε N) {k : ℕ} (hk : k ≤ N) :
    gradient f (point ε k) = if k<N then - 2 * ε else - ε := by
  rw [gradient_eq_deriv', h.first k hk]

/-- All Hessians at interpolation nodes are the identity operator. -/
theorem hessian_eq (h : Data f ε N) {k : ℕ} (hk : k ≤ N) (v : ℝ) :
    TaylorModel.hessianOperator f (point ε k) v = v := by
  rw [hessianOperator_real, h.second k hk, mul_one]

/-- Every nonterminal true Taylor model is the stated positive-definite quadratic. -/
theorem eval_two (h : Data f ε N) {k : ℕ} (hk : k<N) (t : ℝ) :
    TaylorModel.eval f 2 (point ε k) t = f (point ε k) - 2 * ε * t + t ^ 2 / 2 := by
  rw [TaylorModel.eval_eq_sum_iteratedDeriv]
  norm_num [Finset.sum_range_succ, iteratedDeriv_one, h.first k hk.le, h.second k hk.le, hk]
  ring

/-- The Newton step is the global minimizer of the actual quadratic Taylor model. -/
theorem model_minimum (h : Data f ε N) {k : ℕ} (hk : k<N) (t : ℝ) :
    TaylorModel.eval f 2 (point ε k) (2 * ε) ≤ TaylorModel.eval f 2 (point ε k) t := by
  rw [h.eval_two hk, h.eval_two hk]
  nlinarith [sq_nonneg (t - 2 * ε)]

/-- The interpolation nodes follow the genuine Newton recurrence, with positive Hessians. -/
theorem newton_run (h : Data f ε N) (hε : 0<ε) :
    Run f (point ε) (fun _ => 2 * ε) ε N := by
  refine ⟨hε,?_,?_,?_,?_⟩
  · intro k hk
    rw [h.gradient_eq hk.le, ite_eq_left hk, Real.norm_eq_abs,
      abs_of_neg (by linarith)]
    linarith
  · intro k hk v hv
    rw [h.hessian_eq hk.le]
    change 0<v * v
    exact mul_self_pos.mpr hv
  · intro k hk
    rw [h.hessian_eq hk.le, h.gradient_eq hk.le, ite_eq_left hk]
    ring
  · intro k _hk
    simp only [point, Nat.cast_add, Nat.cast_one]
    ring

/-- The first true gradient stopping condition occurs precisely at the last node. -/
theorem first_stop (h : Data f ε N) (hε : 0<ε) :
    (∀ k<N, ε<‖gradient f (point ε k)‖) ∧ ‖gradient f (point ε N)‖ ≤ ε := by
  refine ⟨(h.newton_run hε).not_terminated,?_⟩
  rw [h.gradient_eq le_rfl, ite_eq_right (by omega : ¬N<N), norm_neg,
    Real.norm_eq_abs, abs_of_pos hε]


/-- The Newton step is also a genuine minimizer on the negative-gradient Cauchy ray. -/
theorem cauchyPoint (h : Data f ε N) (hε : 0<ε) (hε1 : ε ≤ 1)
    {k : ℕ} (hk : k<N) :
    SecondOrderTrustRegion.IsCauchyPoint f (point ε k) 2 (2 * ε) := by
  refine ⟨1, by norm_num, ?_, ?_, ?_⟩
  · rw [one_smul, h.gradient_eq hk.le, ite_eq_left hk, Real.norm_eq_abs,
      abs_of_neg (by linarith)]
    linarith
  · rw [one_smul, h.gradient_eq hk.le, ite_eq_left hk]
    ring
  · intro r _hr
    simpa [h.gradient_eq hk.le, hk]
      using h.model_minimum hk (-(r • gradient f (point ε k)))

/-- The actual objective decrease is twice its strictly positive quadratic prediction. -/
theorem actual_ratio (h : Data f ε N) (hε : 0<ε) {k : ℕ} (hk : k<N) :
    (f (point ε k) - f (point ε k + 2 * ε)) /
      (TaylorModel.eval f 2 (point ε k) 0 - TaylorModel.eval f 2 (point ε k) (2 * ε)) = 2 := by
  have hd : TaylorModel.eval f 2 (point ε k) 0-
      TaylorModel.eval f 2 (point ε k) (2 * ε) = 2 * ε ^ 2 := by
    rw [h.eval_two hk, h.eval_two hk]
    ring
  have hp : point ε k + 2 * ε = point ε (k + 1) := by
    simp only [point, Nat.cast_add, Nat.cast_one]
    ring
  have hn : ((N - k : ℕ) : ℝ) = ((N - (k + 1) : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show N - k = N - (k + 1) + 1 by omega)
  rw [hd, hp, h.values k hk.le, h.values (k + 1) (by omega)]
  apply (div_eq_iff (by positivity : 2 * ε ^ 2 ≠ 0)).mpr
  rw [hn]
  ring

/-- Positive curvature gives the actual least Hessian eigenpair `(1,1)`. -/
theorem leastEigenpair (h : Data f ε N) {k : ℕ} (hk : k ≤ N) :
    SecondOrderTrustRegion.IsLeastEigenpair f (point ε k) 1 1 := by
  have hh := CurvatureSharpness.leastEigenpair f (point ε k)
  rwa [h.second k hk] at hh

/-- The same objective and steps satisfy the full operational TR2 algorithm,
for every legal acceptance/update choice and every finite positive curvature tolerance. -/
theorem trustRegion_run (h : Data f ε N) (hε : 0<ε) (hε1 : ε ≤ 1)
    {η₁ η₂ γ₁ γ₂ γ₃ ε₂ : ℝ}
    (hη₁ : 0<η₁) (hη : η₁ ≤ η₂) (hη₂ : η₂<1)
    (hγ₁ : 0<γ₁) (hγ : γ₁ ≤ γ₂) (hγ₂ : γ₂<1) (hγ₃ : 1<γ₃)
    (hε₂ : 0<ε₂) :
    SecondOrderTrustRegion.Run f (point ε) (fun _ => 2 * ε) (fun _ => 2 * ε)
      (fun _ => 0) (fun _ => 1) (fun _ => 1) (fun _ => 2) (fun _ => 2)
      η₁ η₂ γ₁ γ₂ γ₃ ε ε₂ N := by
  have hη12 : η₁ ≤ 2 := by linarith
  have hη22 : η₂ ≤ 2 := by linarith
  refine ⟨?_,hε,hε₂,(fun k hk => h.leastEigenpair hk),?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · refine ⟨by norm_num,hη₁,hη,hη₂,hγ₁,hγ,hγ₂,hγ₃,?_⟩
    intro k _hk
    simp only [ite_eq_left hη22, mem_Icc, le_refl, true_and]
    linarith
  · intro k hk
    rw [h.gradient_eq hk.le, ite_eq_left hk]
    simp only [RCLike.inner_apply, conj_trivial]
    linarith
  · intro k hk
    exact Or.inl ((h.newton_run hε).not_terminated k hk)
  · intro k hk
    exact h.cauchyPoint hε hε1 hk
  · intro k _hk
    norm_num
  · intro k _hk
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith
  · intro k _hk
    exact le_rfl
  · intro k hk
    exact h.model_minimum hk 0
  · intro k hk
    exact (h.actual_ratio hε hk).symm
  · intro k _hk
    rw [ite_eq_left hη12]
    simp only [point, Nat.cast_add, Nat.cast_one]
    ring

/-- Disabling the curvature test gives a legal first-order-only TR2 run as well. -/
theorem trustRegion_firstOrderRun (h : Data f ε N) (hε : 0<ε) (hε1 : ε ≤ 1)
    {η₁ η₂ γ₁ γ₂ γ₃ : ℝ}
    (hη₁ : 0<η₁) (hη : η₁ ≤ η₂) (hη₂ : η₂<1)
    (hγ₁ : 0<γ₁) (hγ : γ₁ ≤ γ₂) (hγ₂ : γ₂<1) (hγ₃ : 1<γ₃) :
    SecondOrderTrustRegion.FirstOrderRun f (point ε) (fun _ => 2 * ε) (fun _ => 2 * ε)
      (fun _ => 2) (fun _ => 2) η₁ η₂ γ₁ γ₂ γ₃ ε ⊤ N := by
  have hr := h.trustRegion_run hε hε1 hη₁ hη hη₂ hγ₁ hγ hγ₂ hγ₃
    (by norm_num : (0: ℝ)<1)
  exact ⟨rfl,hr.updates,hε,(h.newton_run hε).not_terminated,hr.cauchy,
    hr.feasible_step,hr.model_cauchy,hr.ratio,hr.step⟩

/-- Every actual objective step decreases strictly, including the last step. -/
theorem strict_decrease (h : Data f ε N) (hε : 0<ε) {k : ℕ} (hk : k<N) :
    f (point ε (k + 1))<f (point ε k) := by
  rw [h.values k hk.le, h.values (k + 1) (by omega)]
  have hn : ((N - k : ℕ): ℝ) = ((N - (k + 1): ℕ): ℝ) + 1 := by
    exact_mod_cast (show N - k = N - (k + 1) + 1 by omega)
  rw [hn]
  nlinarith [sq_pos_of_pos hε]

end Data


/-- The interpolation and scaling constants precede the accuracy. Hessian norms and
objective ranges are uniform; the Hessian Lipschitz constant is allowed to depend on it. -/
theorem exists_uniform_objectives :
    ∃ H ≥ 1, ∃ G>0, ∀ ε : ℝ, 0<ε → ε ≤ 1 → ∃ f : ℝ → ℝ,
      Data f ε (horizon ε) ∧ (∀ z, |f z| ≤ G) ∧
      (∀ z, ‖SecondOrderTrustRegion.hessian f z‖ ≤ H) ∧
      (∀ z w, ‖gradient f z - gradient f w‖ ≤ H * ‖z - w‖) ∧
      ∃ L ≥ 1, ∀ z w,
        ‖iteratedFDeriv ℝ 2 f z - iteratedFDeriv ℝ 2 f w‖ ≤ L * ‖z - w‖ := by
  obtain ⟨L₀,hL₀,B,hB,H⟩ := Hermite.exists_uniform_interpolant_positive 2 2 (by norm_num)
  refine ⟨max 1 B, le_max_left _ _, 12 + B, by positivity, ?_⟩
  intro ε hε hε1
  let N := horizon ε
  obtain ⟨hgrid,hjets,hstep,hres,hval⟩ := uniform_base_data N
  obtain ⟨F,hF,hFL,hFjet,hFval,hFpos⟩ := H N basePoint (baseJet N) hgrid hjets hstep hres
    (4 * N) (by positivity) hval
  let f := scaleObjective ε F
  have hf : ContDiff ℝ 2 f := scaleObjective_contDiff hF ε
  have harg (k : ℕ) : ε⁻¹ * point ε k = basePoint k := by
    dsimp [point, basePoint]
    field_simp
  have hcoef : ε ^ 2 * ε⁻¹ ^ 2 = 1 := by
    rw [←mul_pow, mul_inv_cancel₀ hε.ne', one_pow]
  have hsecond (z : ℝ) : iteratedDeriv 2 f z = iteratedDeriv 2 F (ε⁻¹ * z) := by
    rw [iteratedDeriv_scaleObjective hF le_rfl, hcoef, one_mul]
  have hdata : Data f ε N := by
    refine ⟨hf,?_,?_,?_⟩
    · intro k hk
      change ε ^ 2 * F (ε⁻¹ * point ε k) = _
      rw [harg]
      have hh := hFjet k hk 0 (by omega)
      have hh' : F (basePoint k) = 4 * (N - k : ℕ) := by
        simpa only [iteratedDeriv_zero, baseJet, ite_true] using hh
      rw [hh']
      ring
    · intro k hk
      rw [←iteratedDeriv_one, iteratedDeriv_scaleObjective hF (by omega), harg,
        hFjet k hk 1 (by omega)]
      by_cases hkn : k<N <;> norm_num [baseJet, hkn]
      all_goals field_simp
    · intro k hk
      rw [hsecond, harg, hFjet k hk 2 le_rfl]
      norm_num [baseJet]
  have hHess (z : ℝ) : ‖SecondOrderTrustRegion.hessian f z‖ ≤ max 1 B := by
    rw [SecondOrderTrustRegion.norm_hessian, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      Real.norm_eq_abs, hsecond]
    exact (hFpos 2 (by omega) le_rfl _).trans (le_max_right _ _)
  refine ⟨f,hdata,?_,hHess,
    SecondOrderTrustRegion.gradient_lipschitz_of_hessian_bound hf (by positivity) hHess,
    max 1 (L₀ / ε), le_max_left _ _, ?_⟩
  · intro z
    have hN : (N: ℝ) < 1 / ε ^ 2 + 2 := by
      have hh := Nat.ceil_lt_add_one (show 0 ≤ 1 / ε ^ 2 by positivity)
      dsimp [N, horizon]
      push_cast
      linarith
    have hNs : ε ^ 2 * (N: ℝ) < 1 + 2 * ε ^ 2 := by
      have hh := mul_lt_mul_of_pos_left hN (sq_pos_of_pos hε)
      have he : ε ^ 2 * (1 / ε ^ 2 + 2) = 1 + 2 * ε ^ 2 := by field_simp
      exact hh.trans_eq he
    have hεsq : ε ^ 2 ≤ 1 := by nlinarith
    have hh : |f z| ≤ ε ^ 2 * (4 * (N: ℝ) + B) := by
      change |ε ^ 2 * F (ε⁻¹ * z)| ≤ _
      rw [abs_mul, abs_of_nonneg (sq_nonneg ε)]
      exact mul_le_mul_of_nonneg_left (hFval _) (sq_nonneg ε)
    have hBε := mul_le_mul_of_nonneg_right hεsq hB.le
    nlinarith
  · intro z w
    rw [norm_iteratedFDeriv_sub_eq_norm_iteratedDeriv_sub, hsecond, hsecond]
    have hh := hFL.norm_sub_le (ε⁻¹ * z) (ε⁻¹ * w)
    change ‖iteratedDeriv 2 F (ε⁻¹ * z) - iteratedDeriv 2 F (ε⁻¹ * w)‖ ≤
      L₀ * ‖ε⁻¹ * z - ε⁻¹ * w‖ at hh
    have he : L₀ * ‖ε⁻¹ * z - ε⁻¹ * w‖ = (L₀ / ε) * ‖z - w‖ := by
      rw [←mul_sub, norm_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε)]
      rw [div_eq_mul_inv]
      ring
    exact hh.trans (he.le.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)))


/-- The witness has strictly more trials than the ceiling appearing in the source. -/
theorem horizon_gt_ceil (ε : ℝ) : ⌈1 / ε ^ 2⌉₊ < horizon ε := by
  simp only [horizon, Nat.lt_add_one]

/-- Every Newton evaluation count, including Hessian calls only at nonterminal
points, strictly exceeds the source ceiling. -/
theorem newton_counts_lower (ε : ℝ) :
    ⌈1 / ε ^ 2⌉₊ < functionEvaluations (horizon ε) ∧
    ⌈1 / ε ^ 2⌉₊ < gradientEvaluations (horizon ε) ∧
    ⌈1 / ε ^ 2⌉₊ < hessianEvaluations (horizon ε) := by
  dsimp [functionEvaluations, gradientEvaluations, hessianEvaluations]
  have hh := horizon_gt_ceil ε
  omega

/-- Every TR2 trial is accepted, so all initialized evaluation counters are exact. -/
theorem trustRegion_counts {η₁ : ℝ} (hη : η₁ ≤ 2) (N : ℕ) :
    SecondOrderTrustRegion.functionEvaluations N = N + 1 ∧
    SecondOrderTrustRegion.gradientEvaluations (fun _ => 2) η₁ N = N + 1 ∧
    SecondOrderTrustRegion.hessianEvaluations (fun _ => 2) η₁ N = N + 1 := by
  simp [SecondOrderTrustRegion.functionEvaluations, SecondOrderTrustRegion.gradientEvaluations,
    SecondOrderTrustRegion.hessianEvaluations, SecondOrderTrustRegion.derivativeEvaluations,
    EvaluationComplexity.successfulIterations, hη]

/-- Uniformly bounded and uniformly gradient-Lipschitz objectives force the full
Newton lower bound, despite positive Hessians at every node and strict descent.
Each objective also has a globally Lipschitz Hessian. -/
theorem exists_slow_newton_objective :
    ∃ H ≥ 1, ∃ G>0, ∀ ε : ℝ, 0<ε → ε ≤ 1 → ∃ f : ℝ → ℝ,
      ContDiff ℝ 2 f ∧ (∀ z, -G ≤ f z) ∧ f 0 - (-G) ≤ 2 * G ∧
      (∀ z, ‖SecondOrderTrustRegion.hessian f z‖ ≤ H) ∧
      (∀ z w, ‖gradient f z - gradient f w‖ ≤ H * ‖z - w‖) ∧
      (∃ L ≥ 1, ∀ z w,
        ‖iteratedFDeriv ℝ 2 f z - iteratedFDeriv ℝ 2 f w‖ ≤ L * ‖z - w‖) ∧
      Run f (point ε) (fun _ => 2 * ε) ε (horizon ε) ∧ point ε 0 = 0 ∧
      (∀ k<horizon ε, f (point ε (k + 1))<f (point ε k)) ∧
      ‖gradient f (point ε (horizon ε))‖ ≤ ε ∧
      ⌈1 / ε ^ 2⌉₊ < horizon ε ∧
      ⌈1 / ε ^ 2⌉₊ < functionEvaluations (horizon ε) ∧
      ⌈1 / ε ^ 2⌉₊ < gradientEvaluations (horizon ε) ∧
      ⌈1 / ε ^ 2⌉₊ < hessianEvaluations (horizon ε) := by
  obtain ⟨H,hH,G,hG,hu⟩ := exists_uniform_objectives
  refine ⟨H,hH,G,hG,?_⟩
  intro ε hε hε1
  obtain ⟨f,hf,hval,hHess,hgrad,hLip⟩ := hu ε hε hε1
  refine ⟨f,hf.regularity,(fun z => (abs_le.mp (hval z)).1),?_,hHess,hgrad,hLip,
    hf.newton_run hε,by simp [point],(fun k hk => hf.strict_decrease hε hk),
    (hf.first_stop hε).2,horizon_gt_ceil ε,?_⟩
  · linarith [(abs_le.mp (hval 0)).2]
  · exact newton_counts_lower ε

/-- The same uniform objective family produces full second-order trust-region
runs for every legal fixed update rule and every positive curvature tolerance.
The disabled curvature branch is included explicitly. -/
theorem exists_slow_trustRegion_objective {η₁ η₂ γ₁ γ₂ γ₃ : ℝ}
    (hη₁ : 0<η₁) (hη : η₁ ≤ η₂) (hη₂ : η₂<1)
    (hγ₁ : 0<γ₁) (hγ : γ₁ ≤ γ₂) (hγ₂ : γ₂<1) (hγ₃ : 1<γ₃) :
    ∃ H ≥ 1, ∃ G>0, ∀ ε : ℝ, 0<ε → ε ≤ 1 → ∃ f : ℝ → ℝ,
      ContDiff ℝ 2 f ∧ (∀ z, -G ≤ f z) ∧ f 0 - (-G) ≤ 2 * G ∧
      (∀ z, ‖SecondOrderTrustRegion.hessian f z‖ ≤ H) ∧
      (∀ ε₂>0, SecondOrderTrustRegion.Run f (point ε) (fun _ => 2 * ε) (fun _ => 2 * ε)
        (fun _ => 0) (fun _ => 1) (fun _ => 1) (fun _ => 2) (fun _ => 2)
        η₁ η₂ γ₁ γ₂ γ₃ ε ε₂ (horizon ε)) ∧
      SecondOrderTrustRegion.FirstOrderRun f (point ε) (fun _ => 2 * ε) (fun _ => 2 * ε)
        (fun _ => 2) (fun _ => 2) η₁ η₂ γ₁ γ₂ γ₃ ε ⊤ (horizon ε) ∧
      point ε 0 = 0 ∧ ‖gradient f (point ε (horizon ε))‖ ≤ ε ∧
      (∀ ε₂>0, ∀ v : ℝ, ‖v‖ = 1 → -ε₂ ≤
        iteratedFDeriv ℝ 2 f (point ε (horizon ε)) (fun _ => v)) ∧
      ⌈1 / ε ^ 2⌉₊ < horizon ε ∧
      SecondOrderTrustRegion.functionEvaluations (horizon ε) = horizon ε + 1 ∧
      SecondOrderTrustRegion.gradientEvaluations (fun _ => 2) η₁ (horizon ε) =
        horizon ε + 1 ∧
      SecondOrderTrustRegion.hessianEvaluations (fun _ => 2) η₁ (horizon ε) = horizon ε + 1 ∧
      ⌈1 / ε ^ 2⌉₊ < SecondOrderTrustRegion.functionEvaluations (horizon ε) ∧
      ⌈1 / ε ^ 2⌉₊ < SecondOrderTrustRegion.gradientEvaluations
        (fun _ => 2) η₁ (horizon ε) ∧
      ⌈1 / ε ^ 2⌉₊ < SecondOrderTrustRegion.hessianEvaluations
        (fun _ => 2) η₁ (horizon ε) := by
  obtain ⟨H,hH,G,hG,hu⟩ := exists_uniform_objectives
  refine ⟨H,hH,G,hG,?_⟩
  intro ε hε hε1
  obtain ⟨f,hf,hval,hHess,_hgrad,_hLip⟩ := hu ε hε hε1
  have hη12 : η₁ ≤ 2 := by linarith
  obtain ⟨hF,hD,hHc⟩ := trustRegion_counts hη12 (horizon ε)
  refine ⟨f,hf.regularity,(fun z => (abs_le.mp (hval z)).1),?_,hHess,
    (fun ε₂ hε₂ =>
      hf.trustRegion_run hε hε1 hη₁ hη hη₂ hγ₁ hγ hγ₂ hγ₃ hε₂),
    hf.trustRegion_firstOrderRun hε hε1 hη₁ hη hη₂ hγ₁ hγ hγ₂ hγ₃,
    by simp [point],(hf.first_stop hε).2,
    (by
      intro ε₂ hε₂ v hv
      exact (show - ε₂ ≤ (1: ℝ) by linarith).trans ((hf.leastEigenpair le_rfl).least v hv)),
    horizon_gt_ceil ε,hF,hD,hHc,?_⟩
  · linarith [(abs_le.mp (hval 0)).2]
  · rw [hF,hD,hHc]
    have hh := horizon_gt_ceil ε
    omega

end Sharpness
end NewtonMinimization
