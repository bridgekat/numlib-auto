import Numlib.Analysis.Calculus.NormRpowHessian
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Quadratic subproblems

Quadratic models and radial power regularizations on real inner product spaces. Global
optimality is characterized by shifted stationarity and positive semidefiniteness, both for
closed balls and for power regularization. These characterizations require neither finite
dimension nor completeness.
-/

open scoped InnerProductSpace
open Set Metric

namespace Optimization.QuadraticSubproblem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quadratic model with linear coefficient `g` and operator coefficient `H`. -/
noncomputable def quadratic (g : E) (H : E →L[ℝ] E) (s : E) : ℝ :=
  ⟪g, s⟫_ℝ + (1 / 2 : ℝ) * ⟪s, H s⟫_ℝ

@[simp] theorem quadratic_zero (g : E) (H : E →L[ℝ] E) : quadratic g H 0 = 0 := by
  simp [quadratic]

/-- Exact expansion around any point for a symmetric quadratic model. -/
theorem quadratic_add (g : E) {H : E →L[ℝ] E} (hH : H.IsSymmetric) (s d : E) :
    quadratic g H (s + d) = quadratic g H s + ⟪g + H s, d⟫_ℝ +
      (1 / 2 : ℝ) * ⟪d, H d⟫_ℝ := by
  simp only [quadratic, map_add, inner_add_left, inner_add_right]
  rw [← hH.apply_clm s d, real_inner_comm d (H s)]
  ring

/-- The derivative is the Riesz functional represented by `g + H s`. -/
theorem hasFDerivAt_quadratic (g : E) {H : E →L[ℝ] E} (hH : H.IsSymmetric) (s : E) :
    HasFDerivAt (quadratic g H) (innerSL ℝ (g + H s)) s := by
  have h := ((innerSL ℝ g).hasFDerivAt.add
    (((hasFDerivAt_id s).inner ℝ H.hasFDerivAt).const_mul (1 / 2 : ℝ)))
  have heq : innerSL ℝ (g + H s) =
      innerSL ℝ g + (1 / 2 : ℝ) •
        (fderivInnerCLM ℝ (s, H s)).comp ((ContinuousLinearMap.id ℝ E).prod H) := by
    ext d
    simp [fderivInnerCLM_apply, ← hH.apply_clm s d, real_inner_comm d (H s)]
    ring
  rw [heq]
  exact h

/-- The power-regularized quadratic model, with a real radial exponent. -/
noncomputable def powerRegularizedQuadratic (g : E) (H : E →L[ℝ] E)
    (sigma r : ℝ) (s : E) : ℝ := quadratic g H s + sigma / r * ‖s‖ ^ r

@[simp] theorem powerRegularizedQuadratic_zero (g : E) (H : E →L[ℝ] E) (sigma : ℝ)
    {r : ℝ} (hr : 0 < r) : powerRegularizedQuadratic g H sigma r 0 = 0 := by
  simp [powerRegularizedQuadratic, Real.zero_rpow hr.ne']

/-- The regularized derivative formula includes the origin when the exponent exceeds one. -/
theorem hasFDerivAt_powerRegularizedQuadratic (g : E) {H : E →L[ℝ] E}
    (hH : H.IsSymmetric) (sigma : ℝ) {r : ℝ} (hr : 1 < r) (s : E) :
    HasFDerivAt (powerRegularizedQuadratic g H sigma r)
      (innerSL ℝ (g + H s + (sigma * ‖s‖ ^ (r - 2)) • s)) s := by
  have h := (hasFDerivAt_quadratic g hH s).add
    ((hasFDerivAt_norm_rpow s hr).const_mul (sigma / r))
  have heq : innerSL ℝ (g + H s + (sigma * ‖s‖ ^ (r - 2)) • s) =
      innerSL ℝ (g + H s) + (sigma / r) • ((r * ‖s‖ ^ (r - 2)) • innerSL ℝ s) := by
    ext d
    simp only [innerSL_apply_apply, inner_add_left, inner_smul_left, RCLike.conj_to_real,
      add_apply, smul_apply, smul_eq_mul]
    field_simp
  rw [heq]
  exact h

/-- Stationarity is necessary for a local minimum of the power-regularized model. -/
theorem stationary_of_isLocalMin_powerRegularizedQuadratic {g : E} {H : E →L[ℝ] E}
    (hH : H.IsSymmetric) {sigma r : ℝ} (hr : 1 < r) {s : E}
    (hs : IsLocalMin (powerRegularizedQuadratic g H sigma r) s) :
    g + H s + (sigma * ‖s‖ ^ (r - 2)) • s = 0 := by
  have h := hs.hasFDerivAt_eq_zero (hasFDerivAt_powerRegularizedQuadratic g hH sigma hr s)
  have hi := congrArg (fun f : E →L[ℝ] ℝ => f
    (g + H s + (sigma * ‖s‖ ^ (r - 2)) • s)) h
  simpa only [innerSL_apply_apply, zero_apply,
    inner_self_eq_zero] using hi

/-- Restriction to the negative-gradient ray is an exact scalar quadratic. -/
theorem quadratic_neg_smul (g : E) (H : E →L[ℝ] E) (t : ℝ) :
    quadratic g H (-(t • g)) = -t * ‖g‖ ^ 2 +
      (1 / 2 : ℝ) * t ^ 2 * ⟪g, H g⟫_ℝ := by
  simp [quadratic, inner_smul_left, inner_smul_right]
  ring

/-- The operator norm bounds the quadratic curvature from above; symmetry is unnecessary. -/
theorem inner_self_apply_le (H : E →L[ℝ] E) (g : E) :
    ⟪g, H g⟫_ℝ ≤ ‖H‖ * ‖g‖ ^ 2 := by
  calc
    ⟪g, H g⟫_ℝ ≤ ‖g‖ * ‖H g‖ := real_inner_le_norm _ _
    _ ≤ ‖g‖ * (‖H‖ * ‖g‖) := mul_le_mul_of_nonneg_left (H.le_opNorm g) (norm_nonneg g)
    _ = _ := by ring

/-- Any sufficiently short negative-gradient step delivers half its linear predicted decrease. -/
theorem quadratic_neg_smul_decrease (g : E) (H : E →L[ℝ] E) {t : ℝ}
    (ht : 0 ≤ t) (htH : t * ‖H‖ ≤ 1) :
    (1 / 2 : ℝ) * t * ‖g‖ ^ 2 ≤ quadratic g H 0 - quadratic g H (-(t • g)) := by
  rw [quadratic_zero, quadratic_neg_smul]
  have hcurv := mul_le_mul_of_nonneg_left (inner_self_apply_le H g) (sq_nonneg t)
  have hshort := mul_le_mul_of_nonneg_right htH (mul_nonneg ht (sq_nonneg ‖g‖))
  nlinarith

/-- Cauchy decrease for every step whose value is no larger than every feasible negative-gradient
ray step. In particular this applies to a Cauchy point and to a global trust-region minimizer. -/
theorem cauchy_decrease (g : E) (H : E →L[ℝ] E) {delta : ℝ} (hdelta : 0 ≤ delta)
    {s : E} (hs : ∀ t : ℝ, 0 ≤ t → t * ‖g‖ ≤ delta →
      quadratic g H s ≤ quadratic g H (-(t • g))) :
    (1 / 2 : ℝ) * ‖g‖ * min (‖g‖ / (1 + ‖H‖)) delta ≤
      quadratic g H 0 - quadratic g H s := by
  by_cases hg : g = 0
  · subst g
    have h := hs 0 le_rfl (by simpa using hdelta)
    simp only [norm_zero, zero_div, mul_zero, zero_mul, quadratic_zero,
      smul_zero, neg_zero] at *
    linarith
  have hgpos : 0 < ‖g‖ := norm_pos_iff.mpr hg
  have hHpos : 0 < 1 + ‖H‖ := by positivity
  let t := min (1 / (1 + ‖H‖)) (delta / ‖g‖)
  have ht : 0 ≤ t := le_min (by positivity) (div_nonneg hdelta hgpos.le)
  have htH : t * ‖H‖ ≤ 1 := by
    calc
      t * ‖H‖ ≤ (1 / (1 + ‖H‖)) * ‖H‖ :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg H)
      _ ≤ 1 := by rw [one_div_mul_eq_div, div_le_one hHpos]; linarith [norm_nonneg H]
  have htfeas : t * ‖g‖ ≤ delta := by
    calc
      t * ‖g‖ ≤ (delta / ‖g‖) * ‖g‖ :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hgpos.le
      _ = delta := div_mul_cancel₀ _ hgpos.ne'
  have hval := (quadratic_neg_smul_decrease g H ht htH).trans
    (sub_le_sub_left (hs t ht htfeas) _)
  have htval : t * ‖g‖ = min (‖g‖ / (1 + ‖H‖)) delta := by
    dsimp [t]
    rw [min_mul_of_nonneg _ _ hgpos.le, div_mul_cancel₀ _ hgpos.ne']
    congr 1
    ring
  nlinarith [htval]

/-- Nonzero gradient and positive radius give a strictly positive predicted decrease. -/
theorem cauchy_decrease_pos {g : E} (H : E →L[ℝ] E) {delta : ℝ} (hdelta : 0 < delta)
    (hg : g ≠ 0) {s : E} (hs : ∀ t : ℝ, 0 ≤ t → t * ‖g‖ ≤ delta →
      quadratic g H s ≤ quadratic g H (-(t • g))) :
    0 < quadratic g H 0 - quadratic g H s := by
  exact lt_of_lt_of_le (by have := norm_pos_iff.mpr hg; positivity)
    (cauchy_decrease g H hdelta.le hs)

/-- Exact model difference at a point satisfying shifted stationarity. -/
theorem quadratic_sub_of_stationary {g : E} {H : E →L[ℝ] E} (hH : H.IsSymmetric)
    {s : E} {lambda : ℝ} (hstat : g + H s + lambda • s = 0) (y : E) :
    quadratic g H y - quadratic g H s =
      (1 / 2 : ℝ) * ⟪y - s, (H + lambda • ContinuousLinearMap.id ℝ E) (y - s)⟫_ℝ +
      lambda / 2 * (‖s‖ ^ 2 - ‖y‖ ^ 2) := by
  have hexp := quadratic_add g hH s (y - s)
  rw [add_sub_cancel] at hexp
  have hgs : g + H s = -(lambda • s) := eq_neg_of_add_eq_zero_left hstat
  rw [hgs, inner_neg_left, inner_smul_left, RCLike.conj_to_real] at hexp
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply, inner_add_right,
    inner_smul_right, real_inner_self_eq_norm_sq]
  rw [norm_sub_sq_real, inner_sub_right] at *
  rw [real_inner_self_eq_norm_sq, real_inner_comm y s] at hexp
  nlinarith

/-- Shifted positive semidefiniteness, stationarity and complementarity suffice for global
trust-region optimality. Feasibility is kept as a separate hypothesis. -/
theorem isMinOn_closedBall_of_shift {g : E} {H : E →L[ℝ] E} (hH : H.IsSymmetric)
    {s : E} {delta lambda : ℝ} (hs : ‖s‖ ≤ delta) (hlambda : 0 ≤ lambda)
    (hstat : g + H s + lambda • s = 0)
    (hpos : (H + lambda • ContinuousLinearMap.id ℝ E).IsPositive)
    (hcomp : lambda * (‖s‖ ^ 2 - delta ^ 2) = 0) :
    IsMinOn (quadratic g H) (closedBall 0 delta) s := by
  intro y hy
  change quadratic g H s ≤ quadratic g H y
  rw [mem_closedBall_zero_iff] at hy
  have hy2 : ‖y‖ ^ 2 ≤ delta ^ 2 := sq_le_sq₀ (norm_nonneg _) ((norm_nonneg s).trans hs) |>.mpr hy
  have hcurv := hpos.inner_nonneg_right (y - s)
  have hnorm := mul_nonneg hlambda (sub_nonneg.mpr hy2)
  have hd := quadratic_sub_of_stationary hH hstat y
  nlinarith

/-- A strictly positive shifted quadratic form makes the trust-region minimizer unique. -/
theorem eq_of_isMinOn_closedBall_of_shift_pos {g : E} {H : E →L[ℝ] E}
    (hH : H.IsSymmetric) {s y : E} {delta lambda : ℝ} (hy : ‖y‖ ≤ delta)
    (hlambda : 0 ≤ lambda) (hstat : g + H s + lambda • s = 0)
    (hpos : ∀ d : E, d ≠ 0 → 0 < ⟪d, (H + lambda • ContinuousLinearMap.id ℝ E) d⟫_ℝ)
    (hcomp : lambda * (‖s‖ ^ 2 - delta ^ 2) = 0)
    (hval : quadratic g H y ≤ quadratic g H s) : y = s := by
  by_contra hne
  have hcurv := hpos (y - s) (sub_ne_zero.mpr hne)
  have hy2 : ‖y‖ ^ 2 ≤ delta ^ 2 :=
    sq_le_sq₀ (norm_nonneg _) ((norm_nonneg y).trans hy) |>.mpr hy
  have hnorm := mul_nonneg hlambda (sub_nonneg.mpr hy2)
  have hd := quadratic_sub_of_stationary hH hstat y
  nlinarith

/-- An unconstrained quadratic is globally minimized exactly at stationary points with
positive semidefinite operator. This statement also covers singular operators. -/
theorem isMinOn_univ_quadratic_iff {g : E} {H : E →L[ℝ] E} (hH : H.IsSymmetric) {s : E} :
    IsMinOn (quadratic g H) univ s ↔ g + H s = 0 ∧ H.IsPositive := by
  constructor
  · intro hmin
    have hderiv := (hmin.isLocalMin (by simp)).hasFDerivAt_eq_zero
      (hasFDerivAt_quadratic g hH s)
    have hstat : g + H s = 0 := by
      have hi := congrArg (fun f : E →L[ℝ] ℝ => f (g + H s)) hderiv
      simpa only [innerSL_apply_apply, zero_apply, inner_self_eq_zero] using hi
    refine ⟨hstat, (ContinuousLinearMap.isPositive_iff H).mpr ⟨hH, fun d => ?_⟩⟩
    have h := hmin (mem_univ (s + d))
    change quadratic g H s ≤ quadratic g H (s + d) at h
    rw [quadratic_add g hH s d, hstat, inner_zero_left] at h
    rw [real_inner_comm d (H d)]
    linarith
  · rintro ⟨hstat, hpos⟩ y _
    change quadratic g H s ≤ quadratic g H y
    have h := quadratic_add g hH s (y - s)
    rw [add_sub_cancel, hstat, inner_zero_left] at h
    have hcurv := hpos.inner_nonneg_right (y - s)
    linarith

/-- The exact minimizer of a linearly perturbed squared norm. This is the first-order
regularization step, including the constant term in the model. -/
theorem isMinOn_univ_linear_add_norm_sq (c : ℝ) (g : E) {sigma : ℝ} (hsigma : 0 < sigma) :
    IsMinOn (fun s : E => c + ⟪g, s⟫_ℝ + sigma / 2 * ‖s‖ ^ 2) univ
      (-(sigma⁻¹ • g)) := by
  have hsym : (sigma • ContinuousLinearMap.id ℝ E).IsSymmetric := by
    intro x y
    simp [inner_smul_left, inner_smul_right]
  have hstat : g + (sigma • ContinuousLinearMap.id ℝ E) (-(sigma⁻¹ • g)) = 0 := by
    simp [smul_smul, hsigma.ne']
  have hpos : (sigma • ContinuousLinearMap.id ℝ E).IsPositive :=
    ContinuousLinearMap.isPositive_id.smul_of_nonneg hsigma.le
  have hq := (isMinOn_univ_quadratic_iff (g := g) hsym).mpr ⟨hstat, hpos⟩
  intro y _
  have h := hq (mem_univ y)
  change quadratic g (sigma • ContinuousLinearMap.id ℝ E) (-(sigma⁻¹ • g)) ≤
    quadratic g (sigma • ContinuousLinearMap.id ℝ E) y at h
  simp only [quadratic, smul_apply, ContinuousLinearMap.id_apply, inner_smul_right,
    real_inner_self_eq_norm_sq] at h
  change c + ⟪g, -(sigma⁻¹ • g)⟫_ℝ + sigma / 2 * ‖-(sigma⁻¹ • g)‖ ^ 2 ≤
    c + ⟪g, y⟫_ℝ + sigma / 2 * ‖y‖ ^ 2
  linarith

/-- Comparing a stationary point with its reflection on the same sphere detects curvature
in every direction not perpendicular to that point. -/
theorem inner_shift_nonneg_of_sphere_min {g : E} {H : E →L[ℝ] E}
    (hH : H.IsSymmetric) {s : E} {lambda : ℝ}
    (hstat : g + H s + lambda • s = 0)
    (hmin : ∀ y : E, ‖y‖ = ‖s‖ → quadratic g H s ≤ quadratic g H y)
    {d : E} (hd : ⟪s, d⟫_ℝ ≠ 0) :
    0 ≤ ⟪d, (H + lambda • ContinuousLinearMap.id ℝ E) d⟫_ℝ := by
  have hd0 : d ≠ 0 := by intro h; simp [h] at hd
  have hn : ‖d‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hd0)
  let t : ℝ := -2 * ⟪s, d⟫_ℝ / ‖d‖ ^ 2
  have ht : t ≠ 0 := div_ne_zero (mul_ne_zero (by norm_num) hd) hn
  have hnorm : ‖s + t • d‖ = ‖s‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      inner_smul_right]
    dsimp [t]
    field_simp
    ring
  have hval := hmin (s + t • d) hnorm
  have hexp := quadratic_sub_of_stationary hH hstat (s + t • d)
  rw [hnorm, sub_self, mul_zero, add_zero, add_sub_cancel_left] at hexp
  simp only [map_smul, inner_smul_left, inner_smul_right, RCLike.conj_to_real] at hexp
  have hmul : 0 ≤ t ^ 2 * ⟪d, (H + lambda • ContinuousLinearMap.id ℝ E) d⟫_ℝ := by
    nlinarith
  exact nonneg_of_mul_nonneg_right hmul (sq_pos_of_ne_zero ht)

/-- A nonzero stationary point that minimizes the quadratic on its sphere has a positive
semidefinite shifted operator. Orthogonal directions follow by continuity of the quadratic form. -/
theorem isPositive_shift_of_sphere_min {g : E} {H : E →L[ℝ] E}
    (hH : H.IsSymmetric) {s : E} (hs : s ≠ 0) {lambda : ℝ}
    (hstat : g + H s + lambda • s = 0)
    (hmin : ∀ y : E, ‖y‖ = ‖s‖ → quadratic g H s ≤ quadratic g H y) :
    (H + lambda • ContinuousLinearMap.id ℝ E).IsPositive := by
  have hsym : (H + lambda • ContinuousLinearMap.id ℝ E).IsSymmetric := by
    intro x y
    change ⟪H x + lambda • x, y⟫_ℝ = ⟪x, H y + lambda • y⟫_ℝ
    simp only [inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right, RCLike.conj_to_real]
    exact congrArg (· + lambda * ⟪x, y⟫_ℝ) (hH.apply_clm x y)
  refine (ContinuousLinearMap.isPositive_iff _).mpr ⟨hsym, fun d => ?_⟩
  rw [real_inner_comm]
  by_cases hd : ⟪s, d⟫_ℝ ≠ 0
  · exact inner_shift_nonneg_of_sphere_min hH hstat hmin hd
  have hd' : ⟪s, d⟫_ℝ = 0 := not_ne_iff.mp hd
  let A := H + lambda • ContinuousLinearMap.id ℝ E
  have hc : Continuous (fun t : ℝ => ⟪d + t • s, A (d + t • s)⟫_ℝ) := by
    fun_prop
  have ht : Filter.Tendsto (fun t : ℝ => ⟪d + t • s, A (d + t • s)⟫_ℝ)
      (nhdsWithin 0 ({0}ᶜ)) (nhds ⟪d, A d⟫_ℝ) := by
    simpa using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with t ht
  apply inner_shift_nonneg_of_sphere_min hH hstat hmin
  rw [inner_add_right, inner_smul_right, hd', zero_add, real_inner_self_eq_norm_sq]
  exact mul_ne_zero (by simpa using ht) (pow_ne_zero _ (norm_ne_zero_iff.mpr hs))

/-- The tangent line to a nonnegative real power lies below its graph. -/
theorem rpow_tangent_le {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 1 ≤ p) :
    a ^ p + p * a ^ (p - 1) * (b - a) ≤ b ^ p := by
  have hc := convexOn_rpow hp
  have hd := Real.hasDerivAt_rpow_const (x := a) (Or.inr hp)
  rcases lt_trichotomy a b with hab | hab | hab
  · have h := hc.le_slope_of_hasDerivAt ha hb hab hd
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hab)] at h
    linarith
  · subst b; simp
  · have h := hc.slope_le_of_hasDerivAt hb ha hab hd
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hab)] at h
    nlinarith

/-- The radial power term dominates its quadratic tangent at every radius. -/
theorem radial_power_sub_ge {x y r : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hr : 2 < r) :
    r / 2 * x ^ (r - 2) * (y ^ 2 - x ^ 2) ≤ y ^ r - x ^ r := by
  have h := rpow_tangent_le (a := x ^ 2) (b := y ^ 2) (p := r / 2)
    (sq_nonneg x) (sq_nonneg y) (by linarith)
  have hxpow : (x ^ 2) ^ (r / 2) = x ^ r := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; congr 1; ring
  have hypow : (y ^ 2) ^ (r / 2) = y ^ r := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy]; congr 1; ring
  have hxp : (x ^ 2) ^ (r / 2 - 1) = x ^ (r - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; congr 1; ring
  rw [hxpow, hypow, hxp] at h
  linarith

/-- The model difference is bounded below by the quadratic form of the radial shift. -/
theorem inner_shift_le_powerRegularized_sub {g : E} {H : E →L[ℝ] E}
    (hH : H.IsSymmetric) {sigma r : ℝ} (hsigma : 0 ≤ sigma) (hr : 2 < r) {s : E}
    (hstat : g + H s + (sigma * ‖s‖ ^ (r - 2)) • s = 0) (y : E) :
    (1 / 2 : ℝ) *
        ⟪y - s, (H + (sigma * ‖s‖ ^ (r - 2)) • ContinuousLinearMap.id ℝ E) (y - s)⟫_ℝ ≤
      powerRegularizedQuadratic g H sigma r y - powerRegularizedQuadratic g H sigma r s := by
  have hd := quadratic_sub_of_stationary hH hstat y
  have hrpow := radial_power_sub_ge (norm_nonneg s) (norm_nonneg y) hr
  have hmul := mul_le_mul_of_nonneg_left hrpow (div_nonneg hsigma (by linarith : 0 ≤ r))
  have hr0 : r ≠ 0 := by linarith
  have heq : sigma / r * (r / 2 * ‖s‖ ^ (r - 2) * (‖y‖ ^ 2 - ‖s‖ ^ 2)) =
      (sigma * ‖s‖ ^ (r - 2)) / 2 * (‖y‖ ^ 2 - ‖s‖ ^ 2) := by
    field_simp
  rw [heq] at hmul
  unfold powerRegularizedQuadratic
  nlinarith

/-- Positive shifted curvature and stationarity suffice for global power-regularized optimality. -/
theorem isMinOn_univ_powerRegularized_of_shift {g : E} {H : E →L[ℝ] E}
    (hH : H.IsSymmetric) {sigma r : ℝ} (hsigma : 0 ≤ sigma) (hr : 2 < r) {s : E}
    (hstat : g + H s + (sigma * ‖s‖ ^ (r - 2)) • s = 0)
    (hpos : (H + (sigma * ‖s‖ ^ (r - 2)) • ContinuousLinearMap.id ℝ E).IsPositive) :
    IsMinOn (powerRegularizedQuadratic g H sigma r) univ s := by
  intro y _
  have hd := inner_shift_le_powerRegularized_sub hH hsigma hr hstat y
  have hp := hpos.inner_nonneg_right (y - s)
  change powerRegularizedQuadratic g H sigma r s ≤
    powerRegularizedQuadratic g H sigma r y
  linarith

/-- The normal cone of a positive-radius Hilbert ball is generated by its outward radius. -/
theorem exists_nonneg_mul_of_ball_first_order {a s : E} {delta : ℝ} (hdelta : 0 < delta)
    (hs : ‖s‖ ≤ delta)
    (hfirst : ∀ y : E, ‖y‖ ≤ delta → 0 ≤ ⟪a, y - s⟫_ℝ) :
    ∃ lambda : ℝ, 0 ≤ lambda ∧ a + lambda • s = 0 ∧
      lambda * (‖s‖ ^ 2 - delta ^ 2) = 0 := by
  by_cases ha : a = 0
  · exact ⟨0, le_rfl, by simp [ha], by simp⟩
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hy : ‖-(delta / ‖a‖) • a‖ ≤ delta := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (div_pos hdelta hn),
      div_mul_cancel₀ _ hn.ne']
  have h := hfirst (-(delta / ‖a‖) • a) hy
  rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq] at h
  have hm : -(delta / ‖a‖) * ‖a‖ ^ 2 = -delta * ‖a‖ := by field_simp
  rw [hm] at h
  have hc := real_inner_le_norm (-a) s
  rw [inner_neg_left, norm_neg] at hc
  have hs' : ‖s‖ = delta := by nlinarith
  have hi : ⟪a, s⟫_ℝ = -delta * ‖a‖ := by nlinarith
  refine ⟨‖a‖ / delta, (div_pos hn hdelta).le, ?_, by simp [hs']⟩
  apply norm_eq_zero.mp
  apply (sq_eq_zero_iff).mp
  rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos hn hdelta), inner_smul_right, hi, hs']
  field_simp
  ring

/-- First-order constrained optimality supplies stationarity and complementarity on a ball. -/
theorem exists_shift_of_isMinOn_closedBall {g : E} {H : E →L[ℝ] E}
    (hH : H.IsSymmetric) {s : E} {delta : ℝ} (hdelta : 0 < delta) (hs : ‖s‖ ≤ delta)
    (hmin : IsMinOn (quadratic g H) (closedBall 0 delta) s) :
    ∃ lambda : ℝ, 0 ≤ lambda ∧ g + H s + lambda • s = 0 ∧
      lambda * (‖s‖ ^ 2 - delta ^ 2) = 0 := by
  apply exists_nonneg_mul_of_ball_first_order hdelta hs
  intro y hy
  have ht := sub_mem_posTangentConeAt_of_segment_subset
    ((convex_closedBall (0 : E) delta).segment_subset
      (mem_closedBall_zero_iff.mpr hs) (mem_closedBall_zero_iff.mpr hy))
  exact hmin.isLocalMinOn.hasFDerivWithinAt_nonneg
    (hasFDerivAt_quadratic g hH s).hasFDerivWithinAt ht

/-- A quadratic minimized at the center of a positive ball has nonnegative curvature. -/
theorem isPositive_of_isMinOn_closedBall_zero {H : E →L[ℝ] E} (hH : H.IsSymmetric)
    {delta : ℝ} (hdelta : 0 < delta)
    (hmin : IsMinOn (quadratic (0 : E) H) (closedBall 0 delta) 0) : H.IsPositive := by
  refine (ContinuousLinearMap.isPositive_iff H).mpr ⟨hH, fun d => ?_⟩
  let t : ℝ := delta / (‖d‖ + 1)
  have ht : 0 < t := div_pos hdelta (by positivity)
  have hfeas : ‖t • d‖ ≤ delta := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    dsimp [t]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < ‖d‖ + 1)]
    nlinarith
  have h := hmin (mem_closedBall_zero_iff.mpr hfeas)
  change quadratic (0 : E) H 0 ≤ quadratic 0 H (t • d) at h
  simp only [quadratic, inner_zero_left, zero_add, map_smul,
    inner_smul_left, inner_smul_right, RCLike.conj_to_real] at h
  have hmul : 0 ≤ t ^ 2 * ⟪d, H d⟫_ℝ := by nlinarith
  rw [real_inner_comm]
  exact nonneg_of_mul_nonneg_right hmul (sq_pos_of_pos ht)

/-- Global trust-region optimality is equivalent to feasible shifted stationarity,
positive semidefiniteness, and complementarity. -/
theorem isMinOn_ball_iff_shift {g : E} {H : E →L[ℝ] E} (hH : H.IsSymmetric)
    {s : E} {delta : ℝ} (hdelta : 0 < delta) :
    (‖s‖ ≤ delta ∧ IsMinOn (quadratic g H) (closedBall 0 delta) s) ↔
      ‖s‖ ≤ delta ∧ ∃ lambda : ℝ, 0 ≤ lambda ∧ g + H s + lambda • s = 0 ∧
        (H + lambda • ContinuousLinearMap.id ℝ E).IsPositive ∧
        lambda * (‖s‖ ^ 2 - delta ^ 2) = 0 := by
  constructor
  · rintro ⟨hs, hmin⟩
    obtain ⟨lambda, hl, hstat, hcomp⟩ := exists_shift_of_isMinOn_closedBall hH hdelta hs hmin
    refine ⟨hs, lambda, hl, hstat, ?_, hcomp⟩
    by_cases hs0 : s = 0
    · subst s
      have hg : g = 0 := by simpa using hstat
      have hl0 : lambda = 0 := by
        simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_sub, mul_neg,
          neg_eq_zero, mul_eq_zero] at hcomp
        exact hcomp.resolve_right (pow_ne_zero _ hdelta.ne')
      subst lambda; subst g
      simpa using isPositive_of_isMinOn_closedBall_zero hH hdelta hmin
    · apply isPositive_shift_of_sphere_min hH hs0 hstat
      intro y hy
      exact hmin (mem_closedBall_zero_iff.mpr (hy.trans_le hs))
  · rintro ⟨hs, lambda, hl, hstat, hpos, hcomp⟩
    exact ⟨hs, isMinOn_closedBall_of_shift hH hs hl hstat hpos hcomp⟩

/-- At the origin, powers of order strictly greater than two cannot hide negative
quadratic curvature. The proof divides the actual model along rays by the squared step length. -/
theorem isPositive_of_isMinOn_powerRegularized_zero {H : E →L[ℝ] E}
    (hH : H.IsSymmetric) {sigma r : ℝ} (hr : 2 < r)
    (hmin : IsMinOn (powerRegularizedQuadratic (0 : E) H sigma r) univ 0) : H.IsPositive := by
  refine (ContinuousLinearMap.isPositive_iff H).mpr ⟨hH, fun d => ?_⟩
  let F : ℝ → ℝ := fun t => (1 / 2 : ℝ) * ⟪d, H d⟫_ℝ +
    sigma / r * t ^ (r - 2) * ‖d‖ ^ r
  have hc : Continuous F := continuous_const.add
    ((continuous_const.mul (Real.continuous_rpow_const (by linarith))).mul continuous_const)
  have htend : Filter.Tendsto F (nhdsWithin 0 (Ioi 0))
      (nhds ((1 / 2 : ℝ) * ⟪d, H d⟫_ℝ)) := by
    simpa [F, Real.zero_rpow (by linarith : r - 2 ≠ 0)] using
      (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have hcurv : 0 ≤ (1 / 2 : ℝ) * ⟪d, H d⟫_ℝ := by
    apply ge_of_tendsto htend
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : 0 < t := ht
    have h := hmin (mem_univ (t • d))
    change powerRegularizedQuadratic 0 H sigma r 0 ≤
      powerRegularizedQuadratic 0 H sigma r (t • d) at h
    rw [powerRegularizedQuadratic_zero _ _ _ (by linarith : 0 < r)] at h
    have hp : t ^ r = t ^ 2 * t ^ (r - 2) := by
      calc
        t ^ r = t ^ ((2 : ℝ) + (r - 2)) := by congr 1; ring
        _ = t ^ 2 * t ^ (r - 2) := by rw [Real.rpow_add htpos, Real.rpow_two]
    have heq : powerRegularizedQuadratic (0 : E) H sigma r (t • d) = t ^ 2 * F t := by
      simp only [powerRegularizedQuadratic, quadratic, inner_zero_left,
        map_smul, inner_smul_left, inner_smul_right, RCLike.conj_to_real, norm_smul,
        Real.norm_eq_abs, abs_of_pos htpos, Real.mul_rpow htpos.le (norm_nonneg d), hp]
      dsimp [F]
      ring
    rw [heq] at h
    exact nonneg_of_mul_nonneg_right h (sq_pos_of_pos htpos)
  rw [real_inner_comm]
  linarith

/-- A global power-regularized minimizer has a positive semidefinite shifted operator,
including a zero minimizer. -/
theorem isPositive_shift_of_isMinOn_powerRegularized {g : E} {H : E →L[ℝ] E}
    (hH : H.IsSymmetric) {sigma r : ℝ} (hr : 2 < r) {s : E}
    (hmin : IsMinOn (powerRegularizedQuadratic g H sigma r) univ s) :
    (H + (sigma * ‖s‖ ^ (r - 2)) • ContinuousLinearMap.id ℝ E).IsPositive := by
  have hstat := stationary_of_isLocalMin_powerRegularizedQuadratic hH
    (by linarith : 1 < r) (hmin.isLocalMin (by simp))
  by_cases hs : s = 0
  · subst s
    have hg : g = 0 := by simpa using hstat
    subst g
    simpa [Real.zero_rpow (by linarith : r - 2 ≠ 0)] using
      isPositive_of_isMinOn_powerRegularized_zero hH hr hmin
  · apply isPositive_shift_of_sphere_min hH hs hstat
    intro y hy
    have h := hmin (mem_univ y)
    change powerRegularizedQuadratic g H sigma r s ≤
      powerRegularizedQuadratic g H sigma r y at h
    unfold powerRegularizedQuadratic at h
    rw [hy] at h
    linarith

/-- A power-regularized quadratic is globally minimized exactly at stationary points
with a positive semidefinite radial shift. -/
theorem isMin_powerRegularized_iff_shift {g : E} {H : E →L[ℝ] E}
    (hH : H.IsSymmetric) {sigma r : ℝ} (hsigma : 0 ≤ sigma) (hr : 2 < r) {s : E} :
    IsMinOn (powerRegularizedQuadratic g H sigma r) univ s ↔
      g + H s + (sigma * ‖s‖ ^ (r - 2)) • s = 0 ∧
        (H + (sigma * ‖s‖ ^ (r - 2)) • ContinuousLinearMap.id ℝ E).IsPositive := by
  constructor
  · intro hmin
    exact ⟨stationary_of_isLocalMin_powerRegularizedQuadratic hH (by linarith)
      (hmin.isLocalMin (by simp)), isPositive_shift_of_isMinOn_powerRegularized hH hr hmin⟩
  · rintro ⟨hstat, hpos⟩
    exact isMinOn_univ_powerRegularized_of_shift hH hsigma hr hstat hpos

/-- Strict positivity of the radial shift makes a power-regularized global minimizer unique. -/
theorem eq_of_isMinOn_powerRegularized_of_shift_pos {g : E} {H : E →L[ℝ] E}
    (hH : H.IsSymmetric) {sigma r : ℝ} (hsigma : 0 ≤ sigma) (hr : 2 < r) {s y : E}
    (hstat : g + H s + (sigma * ‖s‖ ^ (r - 2)) • s = 0)
    (hpos : ∀ d : E, d ≠ 0 →
      0 < ⟪d, (H + (sigma * ‖s‖ ^ (r - 2)) • ContinuousLinearMap.id ℝ E) d⟫_ℝ)
    (hval : powerRegularizedQuadratic g H sigma r y ≤
      powerRegularizedQuadratic g H sigma r s) : y = s := by
  by_contra hne
  have hd := inner_shift_le_powerRegularized_sub hH hsigma hr hstat y
  have hp := hpos (y - s) (sub_ne_zero.mpr hne)
  linarith

end Optimization.QuadraticSubproblem


noncomputable section
open Set Metric
namespace Optimization.QuadraticSubproblem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A minimizer of the quadratic model on its feasible negative-gradient ray. -/
def IsCauchyPoint (g : E) (H : E →L[ℝ] E) (delta : ℝ) (s : E) : Prop :=
  s ∈ closedBall 0 delta ∩ (fun t : ℝ => -(t • g)) '' Ici 0 ∧
    IsMinOn (quadratic g H) (closedBall 0 delta ∩ (fun t : ℝ => -(t • g)) '' Ici 0) s

/-- A Cauchy point is feasible for the trust-region ball. -/
theorem IsCauchyPoint.norm_le {g : E} {H : E →L[ℝ] E} {delta : ℝ} {s : E}
    (hs : IsCauchyPoint g H delta s) : ‖s‖ ≤ delta :=
  mem_closedBall_zero_iff.mp hs.1.1

/-- Scalar characterization of the feasible negative-gradient ray. -/
theorem mem_feasible_ray_iff {g s : E} {delta : ℝ} :
    s ∈ closedBall 0 delta ∩ (fun t : ℝ => -(t • g)) '' Ici 0 ↔
      ∃ t : ℝ, 0 ≤ t ∧ t * ‖g‖ ≤ delta ∧ s = -(t • g) := by
  constructor
  · rintro ⟨hball, t, ht, rfl⟩
    change 0 ≤ t at ht
    refine ⟨t, ht, ?_, rfl⟩
    simpa only [mem_closedBall_zero_iff, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht] using hball
  · rintro ⟨t, ht, hfeas, rfl⟩
    refine ⟨?_, ⟨t, ht, rfl⟩⟩
    simpa only [mem_closedBall_zero_iff, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht] using hfeas

/-- A Cauchy point has no larger value than every feasible negative-gradient step. -/
theorem IsCauchyPoint.le_ray {g : E} {H : E →L[ℝ] E} {delta : ℝ} {s : E}
    (hs : IsCauchyPoint g H delta s) {t : ℝ} (ht : 0 ≤ t) (hfeas : t * ‖g‖ ≤ delta) :
    quadratic g H s ≤ quadratic g H (-(t • g)) :=
  hs.2 (mem_feasible_ray_iff.mpr ⟨t, ht, hfeas, rfl⟩)

/-- A scalar ray minimizer gives a Cauchy point. -/
theorem isCauchyPoint_iff {g : E} {H : E →L[ℝ] E} {delta : ℝ} {s : E} :
    IsCauchyPoint g H delta s ↔
      (∃ t : ℝ, 0 ≤ t ∧ t * ‖g‖ ≤ delta ∧ s = -(t • g)) ∧
      ∀ t : ℝ, 0 ≤ t → t * ‖g‖ ≤ delta →
        quadratic g H s ≤ quadratic g H (-(t • g)) := by
  constructor
  · intro hs
    exact ⟨mem_feasible_ray_iff.mp hs.1, fun _ ht hf => hs.le_ray ht hf⟩
  · rintro ⟨hmem, hmin⟩
    refine ⟨mem_feasible_ray_iff.mpr hmem, ?_⟩
    intro y hy
    obtain ⟨t, ht, hf, rfl⟩ := mem_feasible_ray_iff.mp hy
    exact hmin t ht hf

/-- Every nonnegative radius admits a genuine Cauchy point, in any real inner-product space.
Only a compact scalar interval is minimized, so no dimension or completeness assumption
is needed. -/
theorem exists_isCauchyPoint (g : E) (H : E →L[ℝ] E) {delta : ℝ}
    (hdelta : 0 ≤ delta) : ∃ s : E, IsCauchyPoint g H delta s := by
  by_cases hg : g = 0
  · subst g
    refine ⟨0, isCauchyPoint_iff.mpr ⟨⟨0, le_rfl, by simpa using hdelta, by simp⟩, ?_⟩⟩
    intro t ht hf
    simp
  have hgn : 0 < ‖g‖ := norm_pos_iff.mpr hg
  have hinterval : (Icc (0 : ℝ) (delta / ‖g‖)).Nonempty :=
    nonempty_Icc.mpr (div_nonneg hdelta hgn.le)
  have hcont : Continuous (fun t : ℝ => quadratic g H (-(t • g))) := by
    simp_rw [quadratic_neg_smul]
    exact ((continuous_id.neg).mul continuous_const).add
      (((continuous_const.mul (continuous_id.pow 2))).mul continuous_const)
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn hinterval hcont.continuousOn
  refine ⟨-(t • g), isCauchyPoint_iff.mpr ⟨⟨t, ht.1, ?_, rfl⟩, ?_⟩⟩
  · exact (le_div_iff₀ hgn).mp ht.2
  · intro u hu huf
    exact hmin ⟨hu, (le_div_iff₀ hgn).mpr huf⟩

/-- Giving at least Cauchy decrease is equivalent to dominating one actual Cauchy point. -/
theorem le_all_ray_iff_exists_isCauchyPoint {g : E} {H : E →L[ℝ] E}
    {delta : ℝ} (hdelta : 0 ≤ delta) (s : E) :
    (∀ t : ℝ, 0 ≤ t → t * ‖g‖ ≤ delta →
      quadratic g H s ≤ quadratic g H (-(t • g))) ↔
      ∃ sC : E, IsCauchyPoint g H delta sC ∧ quadratic g H s ≤ quadratic g H sC := by
  constructor
  · intro hs
    obtain ⟨sC, hsC⟩ := exists_isCauchyPoint g H hdelta
    obtain ⟨t, ht, hf, heq⟩ := mem_feasible_ray_iff.mp hsC.1
    refine ⟨sC, hsC, ?_⟩
    rw [heq]
    exact hs t ht hf
  · rintro ⟨sC, hsC, hle⟩ t ht hf
    exact hle.trans (hsC.le_ray ht hf)

/-- Positive superquadratic regularization dominates every linear and quadratic term at infinity. -/
theorem tendsto_powerRegularizedQuadratic_cocompact [FiniteDimensional ℝ E]
    (g : E) (H : E →L[ℝ] E) {sigma r : ℝ} (hsigma : 0 < sigma) (hr : 2 < r) :
    Filter.Tendsto (powerRegularizedQuadratic g H sigma r) (Filter.cocompact E)
      Filter.atTop := by
  have hn := tendsto_norm_cocompact_atTop (E := E)
  have hc : Filter.Tendsto
      (fun s : E ↦ sigma / r * ‖s‖ ^ (r - 2) - (‖g‖ + ‖H‖ / 2))
      (Filter.cocompact E) Filter.atTop := by
    simpa only [sub_eq_add_neg, Function.comp_def] using Filter.tendsto_atTop_add_const_right _
      (-(‖g‖ + ‖H‖ / 2)) (Filter.Tendsto.const_mul_atTop
        (div_pos hsigma (by linarith : 0 < r))
        ((tendsto_rpow_atTop (by linarith : 0 < r - 2)).comp hn))
  apply Filter.tendsto_atTop_mono' _ ?_
    ((Filter.tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hn)
  filter_upwards [hn.eventually_ge_atTop 1, hc.eventually_ge_atTop 1] with s hs hcs
  have hsn : 0 < ‖s‖ := lt_of_lt_of_le zero_lt_one hs
  have hp : ‖s‖ ^ r = ‖s‖ ^ (r - 2) * ‖s‖ ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hsn]
    congr 1
    ring
  have hlin : -(‖g‖ * ‖s‖) ≤ ⟪g, s⟫_ℝ := by
    have := real_inner_le_norm (-g) s
    simp only [inner_neg_left, norm_neg] at this
    linarith
  have hquad : -(‖H‖ * ‖s‖ ^ (2 : ℕ)) ≤ ⟪s, H s⟫_ℝ := by
    have := inner_self_apply_le (-H) s
    simp only [neg_apply, inner_neg_right, norm_neg] at this
    linarith
  have hsq : ‖g‖ * ‖s‖ ≤ ‖g‖ * ‖s‖ ^ (2 : ℕ) := by
    exact mul_le_mul_of_nonneg_left (by nlinarith) (norm_nonneg g)
  have hcsm := mul_le_mul_of_nonneg_right hcs (sq_nonneg ‖s‖)
  dsimp [powerRegularizedQuadratic, quadratic]
  rw [hp]
  nlinarith

/-- In finite dimension, a positively regularized superquadratic model attains its minimum. -/
theorem exists_isMinOn_powerRegularizedQuadratic [FiniteDimensional ℝ E]
    (g : E) (H : E →L[ℝ] E) {sigma r : ℝ} (hsigma : 0 < sigma) (hr : 2 < r) :
    ∃ s : E, IsMinOn (powerRegularizedQuadratic g H sigma r) Set.univ s := by
  have hc : Continuous (powerRegularizedQuadratic g H sigma r) := by
    unfold powerRegularizedQuadratic quadratic
    fun_prop (discharger := positivity)
  obtain ⟨s, hs⟩ := hc.exists_forall_le
    (tendsto_powerRegularizedQuadratic_cocompact g H hsigma hr)
  exact ⟨s, fun y _ ↦ hs y⟩

/-- The genuine Hessian is the quadratic operator plus the radial Hessian,
including the zero step. -/
theorem hasFDerivAt_fderiv_powerRegularizedQuadratic (g : E) {H : E →L[ℝ] E}
    (hH : H.IsSymmetric) (sigma : ℝ) {r : ℝ} (hr : 2 < r) (s : E) :
    HasFDerivAt (fderiv ℝ (powerRegularizedQuadratic g H sigma r))
      (((innerSL ℝ).restrictScalars ℝ).comp H + (sigma / r) • normRpowHessian r s) s := by
  have heq : fderiv ℝ (powerRegularizedQuadratic g H sigma r) =
      fun z ↦ innerSL ℝ g + innerSL ℝ (H z) +
        (sigma / r) • fderiv ℝ (fun y : E ↦ ‖y‖ ^ r) z := by
    funext z
    rw [(hasFDerivAt_powerRegularizedQuadratic g hH sigma (by linarith) z).fderiv,
      fderiv_norm_rpow z (by linarith)]
    ext u
    simp only [innerSL_apply_apply, inner_add_left, inner_smul_left, RCLike.conj_to_real,
      add_apply, smul_apply, smul_eq_mul]
    field_simp
  rw [heq]
  convert ((hasFDerivAt_const (innerSL ℝ g) s).add
    ((((innerSL ℝ).restrictScalars ℝ).comp H).hasFDerivAt)).add
      ((hasFDerivAt_fderiv_norm_rpow hr s).const_smul (sigma / r)) using 1 <;>
      first | rfl | simp only [zero_add]

/-- A boundary point globally minimizes a negative scalar quadratic on its closed ball. -/
theorem quadratic_zero_negative_scalar_min {a δ : ℝ} (ha : a ≤ 0) {s : E}
    (hs : ‖s‖ = δ) (y : E) (hy : ‖y‖ ≤ δ) :
    quadratic (0 : E) (a • ContinuousLinearMap.id ℝ E) s ≤
      quadratic (0 : E) (a • ContinuousLinearMap.id ℝ E) y := by
  simp only [quadratic, inner_zero_left, zero_add, smul_apply,
    ContinuousLinearMap.id_apply, real_inner_smul_right, real_inner_self_eq_norm_sq, hs]
  have hh : ‖y‖ ^ 2 ≤ δ ^ 2 := sq_le_sq₀ (norm_nonneg y) (by rw [← hs]; positivity) |>.mpr hy
  nlinarith [mul_nonpos_of_nonpos_of_nonneg ha (sub_nonneg.mpr hh)]

end Optimization.QuadraticSubproblem
