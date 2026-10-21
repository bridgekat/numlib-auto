import Numlib.Optimization.ExactLineSearch
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Tactic.FinCases

/-!
# Sharpness of exact negative-gradient line searches

A family of two-dimensional diagonal quadratics has a uniformly Lipschitz gradient and
uniform initial objective gap, but needs order inverse-square accuracy iterations under
actual global exact ray minimization. The small eigenvalue depends on the accuracy.
-/

open InnerProductSpace

noncomputable section

namespace Optimization.ExactLineSearchSharpness

/-- Two-dimensional real Euclidean space. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A diagonal quadratic translated so its initial point can be the origin. -/
def objective (μ a b : ℝ) (x : Plane) : ℝ :=
  μ / 2 * (x 0 + a) ^ 2 + 1 / 2 * (x 1 + b) ^ 2

/-- The gradient of the translated diagonal quadratic. -/
def grad (μ a b : ℝ) (x : Plane) : Plane :=
  WithLp.toLp 2 ![μ * (x 0 + a), x 1 + b]

private theorem norm_sq (x : Plane) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

/-- The displayed vector is the actual Fréchet gradient. -/
theorem hasFDerivAt_objective (μ a b : ℝ) (x : Plane) :
    HasFDerivAt (objective μ a b) (innerSL ℝ (grad μ a b x)) x := by
  have h := ((((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt
    (x := x)).add_const a).pow 2).const_mul (μ / 2)
  have h' := ((((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt
    (x := x)).add_const b).pow 2).const_mul (1 / 2 : ℝ)
  convert h.add h' using 1
  · rfl
  · ext y
    simp [grad, innerSL_apply_apply, PiLp.inner_apply, Fin.sum_univ_two, smul_eq_mul]
    ring

/-- The gradient is globally nonexpansive when both eigenvalues lie in `[0,1]`. -/
theorem grad_lipschitz {μ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) (a b : ℝ) (x y : Plane) :
    ‖grad μ a b x - grad μ a b y‖ ≤ ‖x - y‖ := by
  have hs : μ ^ 2 ≤ 1 := by nlinarith
  have hz := mul_le_mul_of_nonneg_right hs (sq_nonneg (x 0 - y 0))
  have hsq : ‖grad μ a b x - grad μ a b y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    simp only [norm_sq, grad, PiLp.sub_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    nlinarith [sq_nonneg (x 0 - y 0)]
  nlinarith [norm_nonneg (grad μ a b x - grad μ a b y), norm_nonneg (x - y)]

/-- Positive-semidefinite diagonal quadratics have global lower bound zero. -/
theorem objective_nonneg {μ : ℝ} (hμ : 0 ≤ μ) (a b : ℝ) (x : Plane) :
    0 ≤ objective μ a b x := by unfold objective; positivity

/-- The geometric contraction in the slow quadratic trajectory. -/
def ratio (μ : ℝ) : ℝ := (1 - μ) / (1 + μ)

/-- Closed form of the exact-search iterates starting at zero. -/
def iterate (μ ε : ℝ) (k : ℕ) : Plane :=
  WithLp.toLp 2 ![2 * ε / μ * (ratio μ ^ k - 1),
    2 * ε * ((-ratio μ) ^ k - 1)]

/-- The constant exact-search step on the slow trajectory. -/
def step (μ : ℝ) : ℝ := 2 / (1 + μ)

/-- The trajectory starts at the origin. -/
@[simp] theorem iterate_zero (μ ε : ℝ) : iterate μ ε 0 = 0 := by
  ext i
  fin_cases i <;> simp [iterate]

/-- Exact formula for the gradients along the trajectory. -/
theorem grad_iterate {μ : ℝ} (hμ : μ ≠ 0) (ε : ℝ) (k : ℕ) :
    grad μ (2 * ε / μ) (2 * ε) (iterate μ ε k) =
      WithLp.toLp 2 ![2 * ε * ratio μ ^ k, 2 * ε * (-ratio μ) ^ k] := by
  ext i
  fin_cases i <;> simp [grad, iterate]
  all_goals
    field_simp
    ring

/-- The closed trajectory takes the displayed negative-gradient steps. -/
theorem iterate_succ {μ : ℝ} (hμ : 0 < μ) (ε : ℝ) (k : ℕ) :
    iterate μ ε (k + 1) = iterate μ ε k -
      step μ • grad μ (2 * ε / μ) (2 * ε) (iterate μ ε k) := by
  rw [grad_iterate hμ.ne']
  ext i
  fin_cases i <;> simp [iterate, step, ratio, pow_succ]
  all_goals field_simp
  all_goals ring

private theorem objective_line (μ a b t : ℝ) (x : Plane) :
    objective μ a b (x - t • grad μ a b x) = objective μ a b x -
      t * ((μ * (x 0 + a)) ^ 2 + (x 1 + b) ^ 2) +
      t ^ 2 / 2 * (μ * (μ * (x 0 + a)) ^ 2 + (x 1 + b) ^ 2) := by
  simp [objective, grad]
  ring

/-- Equal squared gradient components make the constant step a global ray minimizer. -/
theorem isExact_of_balance {μ : ℝ} (hμ : 0 < μ) (a b : ℝ) (x : Plane)
    (hb : (μ * (x 0 + a)) ^ 2 = (x 1 + b) ^ 2) :
    LineSearch.IsExact (objective μ a b) x (-grad μ a b x) (step μ) := by
  refine ⟨by unfold step; positivity, ?_⟩
  intro t _
  change objective μ a b (x + step μ • (-grad μ a b x)) ≤
    objective μ a b (x + t • (-grad μ a b x))
  simp only [smul_neg, ← sub_eq_add_neg]
  rw [objective_line, objective_line, ← hb]
  have hd : (1 + μ) ≠ 0 := by positivity
  have he : objective μ a b x - step μ *
      ((μ * (x 0 + a)) ^ 2 + (μ * (x 0 + a)) ^ 2) +
      step μ ^ 2 / 2 * (μ * (μ * (x 0 + a)) ^ 2 + (μ * (x 0 + a)) ^ 2) +
      (1 + μ) / 2 * (μ * (x 0 + a)) ^ 2 * (t - step μ) ^ 2 =
      objective μ a b x - t * ((μ * (x 0 + a)) ^ 2 + (μ * (x 0 + a)) ^ 2) +
      t ^ 2 / 2 * (μ * (μ * (x 0 + a)) ^ 2 + (μ * (x 0 + a)) ^ 2) := by
    unfold step
    field_simp
    ring
  have hp : 0 ≤ (1 + μ) / 2 * (μ * (x 0 + a)) ^ 2 * (t - step μ) ^ 2 := by positivity
  linarith

/-- Every displayed step globally minimizes the entire nonnegative search ray. -/
theorem iterate_isExact {μ : ℝ} (hμ : 0 < μ) (ε : ℝ) (k : ℕ) :
    LineSearch.IsExact (objective μ (2 * ε / μ) (2 * ε)) (iterate μ ε k)
      (-grad μ (2 * ε / μ) (2 * ε) (iterate μ ε k)) (step μ) := by
  apply isExact_of_balance hμ
  have hg := congrArg (fun v : Plane => (v 0) ^ 2 - (v 1) ^ 2) (grad_iterate hμ.ne' ε k)
  have hn : ((-ratio μ) ^ k) ^ 2 = (ratio μ ^ k) ^ 2 := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm k 2, pow_mul, pow_mul, neg_sq]
  simp only [grad, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at hg
  simp only [mul_pow, hn] at hg
  linarith

/-- Bernoulli's inequality keeps the slow gradient above tolerance for inverse-square time. -/
theorem gradient_large {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (k : ℕ)
    (hk : (k : ℝ) * ε ^ 2 ≤ 2) :
    ε < ‖grad (ε ^ 2 / 100) (2 * ε / (ε ^ 2 / 100)) (2 * ε)
      (iterate (ε ^ 2 / 100) ε k)‖ := by
  let μ := ε ^ 2 / 100
  have hm : 0 < μ := by dsimp [μ]; positivity
  have hm1 : μ ≤ 1 / 100 := by dsimp [μ]; nlinarith
  have hq : 0 ≤ ratio μ := by
    unfold ratio
    exact div_nonneg (by linarith) (by positivity)
  have hq1 : 1 - ratio μ ≤ ε ^ 2 / 50 := by
    calc
      1 - ratio μ = 2 * μ / (1 + μ) := by
        unfold ratio
        field_simp
        ring
      _ ≤ 2 * μ := div_le_self (by positivity) (by linarith)
      _ = ε ^ 2 / 50 := by dsimp [μ]; ring
  have hb := one_add_mul_sub_le_pow (by linarith : -1 ≤ ratio μ) k
  have ht := mul_le_mul_of_nonneg_left hq1 (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hp : (24 / 25 : ℝ) ≤ ratio μ ^ k := by nlinarith
  rw [grad_iterate (by positivity : ε ^ 2 / 100 ≠ 0)]
  have hn := PiLp.norm_apply_le
    (WithLp.toLp 2 ![2 * ε * ratio μ ^ k, 2 * ε * (-ratio μ) ^ k] : Plane) (0 : Fin 2)
  simp only [Matrix.cons_val_zero, Real.norm_eq_abs] at hn
  have hfirst : ε < 2 * ε * ratio μ ^ k := by nlinarith
  exact hfirst.trans_le ((le_abs_self _).trans hn)

/-- The uniform initial objective gap of the quadratic family is at most `202`. -/
theorem initial_gap {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    objective (ε ^ 2 / 100) (2 * ε / (ε ^ 2 / 100)) (2 * ε) 0 ≤ 202 := by
  have he : objective (ε ^ 2 / 100) (2 * ε / (ε ^ 2 / 100)) (2 * ε) 0 =
      200 + 2 * ε ^ 2 := by
    simp [objective]
    field_simp
    ring
  rw [he]
  nlinarith

/-- Diagonal quadratics are smooth of every order. -/
theorem contDiff_objective (μ a b : ℝ) : ContDiff ℝ ⊤ (objective μ a b) := by
  unfold objective
  fun_prop

/-- The canonical gradient agrees with the displayed vector field. -/
theorem gradient_objective (μ a b : ℝ) : gradient (objective μ a b) = grad μ a b := by
  apply gradient_eq
  intro x
  exact hasGradientAt_iff_hasFDerivAt.mpr (hasFDerivAt_objective μ a b x)

/-- Uniformly smooth, bounded-below objectives with actual exact-search trajectories whose
first successful gradient test comes strictly after the inverse-square ceiling. -/
theorem exists_slow_exactLineSearch :
    ∃ L B : ℝ, 1 ≤ L ∧ 0 ≤ B ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (f : Plane → ℝ) (x : ℕ → Plane) (t : ℕ → ℝ) (K : ℕ),
        ContDiff ℝ 1 f ∧
        (∀ u v, ‖gradient f u - gradient f v‖ ≤ L * ‖u - v‖) ∧
        (∀ u, 0 ≤ f u) ∧ f (x 0) ≤ B ∧ x 0 = 0 ∧
        (∀ k, LineSearch.IsExact f (x k) (-gradient f (x k)) (t k)) ∧
        (∀ k, x (k + 1) = x k - t k • gradient f (x k)) ∧
        ‖gradient f (x K)‖ ≤ ε ∧ (∀ j < K, ε < ‖gradient f (x j)‖) ∧
        ⌈ε⁻¹ ^ 2⌉₊ < K := by
  refine ⟨1, 202, le_rfl, by norm_num, ?_⟩
  intro ε he he1
  let μ := ε ^ 2 / 100
  let f := objective μ (2 * ε / μ) (2 * ε)
  let x := iterate μ ε
  let t : ℕ → ℝ := fun _ => step μ
  have hm : 0 < μ := by dsimp [μ]; positivity
  have hm1 : μ ≤ 1 := by dsimp [μ]; nlinarith
  have hg : gradient f = grad μ (2 * ε / μ) (2 * ε) :=
    gradient_objective _ _ _
  have hf : ∀ y, HasFDerivAt f (innerSL ℝ (gradient f y)) y := by
    rw [hg]
    exact hasFDerivAt_objective _ _ _
  have hLip : ∀ u v, ‖gradient f u - gradient f v‖ ≤ 1 * ‖u - v‖ := by
    rw [hg]
    simpa only [one_mul] using grad_lipschitz hm.le hm1 (2 * ε / μ) (2 * ε)
  have hlow : ∀ u, 0 ≤ f u := objective_nonneg hm.le _ _
  have hsearch : ∀ k, LineSearch.IsExact f (x k) (-gradient f (x k)) (t k) := by
    rw [hg]
    exact iterate_isExact hm ε
  have hstep : ∀ k, x (k + 1) = x k - t k • gradient f (x k) := by
    rw [hg]
    exact iterate_succ hm ε
  have hseq : SmoothDescent.IsExactSequence f (gradient f) ε x t :=
    ⟨fun k _ => hsearch k, fun k _ => hstep k⟩
  obtain ⟨K, hK, hfirst, _⟩ := SmoothDescent.exists_stationary_of_exactLineSearch
    hf hLip zero_lt_one he hseq (fun k => hlow (x k))
  refine ⟨f, x, t, K, (contDiff_objective _ _ _).of_le (by simp), hLip, hlow, ?_,
    iterate_zero _ _, hsearch, hstep, hK, hfirst, ?_⟩
  · change f (iterate μ ε 0) ≤ 202
    rw [iterate_zero]
    exact initial_gap he he1
  · by_contra! hn
    have hc : (⌈ε⁻¹ ^ 2⌉₊ : ℝ) < ε⁻¹ ^ 2 + 1 := Nat.ceil_lt_add_one (sq_nonneg _)
    have hk : (K : ℝ) * ε ^ 2 ≤ 2 := by
      have hkn : (K : ℝ) ≤ ⌈ε⁻¹ ^ 2⌉₊ := by exact_mod_cast hn
      have hh := mul_le_mul_of_nonneg_right (hkn.trans hc.le) (sq_nonneg ε)
      have hi : ε⁻¹ ^ 2 * ε ^ 2 = 1 := by field_simp
      nlinarith
    have hl := gradient_large he he1 K hk
    rw [hg] at hK
    exact (not_lt_of_ge hK) hl

end Optimization.ExactLineSearchSharpness
