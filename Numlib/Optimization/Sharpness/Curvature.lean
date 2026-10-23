import Numlib.Optimization.Regularization.Cubic.Finite
import Numlib.Optimization.TrustRegion.SecondOrder.Finite
import Numlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Negative-curvature interpolation data for actual optimization executions

Only objective values and actual derivative jets are specified. Algorithm traces,
model improvement, acceptance ratios and evaluation counts are proved from these
jets. Global smooth interpolant existence and its uniform regularity bounds are
separate from these execution lemmas.
-/

namespace CurvatureSharpness
open TaylorModel Set

/-- Equally spaced interpolation points. -/
def grid (t : ℝ) (i : ℕ) : ℝ := (i : ℝ) * t

/-- Prescribed values decrease by the actual quadratic-model reduction. -/
def value (ε t : ℝ) (N i : ℕ) : ℝ := ((N : ℝ) - i) * ε * t ^ 2

/-- Negative curvature persists until the final zero-curvature endpoint. -/
def curvature (ε : ℝ) (N i : ℕ) : ℝ := if i < N then -2 * ε else 0

/-- The interpolation jet consists of actual value, zero gradient and prescribed curvature. -/
def jet (ε t : ℝ) (N i j : ℕ) : ℝ :=
  if j = 0 then value ε t N i else if j = 1 then 0 else if j = 2 then curvature ε N i else 0

/-- Compatibility with a genuine twice continuously differentiable scalar objective.
No algorithmic behavior or objective/iteration bound is assumed. -/
structure Data (f : ℝ → ℝ) (ε t : ℝ) (N : ℕ) : Prop where
  regularity : ContDiff ℝ 2 f
  values : ∀ i ≤ N, f (grid t i) = value ε t N i
  first : ∀ i ≤ N, deriv f (grid t i) = 0
  second : ∀ i ≤ N, iteratedDeriv 2 f (grid t i) = curvature ε N i

/-- In one real dimension the actual curried Hessian is the ordinary second derivative. -/
theorem secondDerivative_apply (f : ℝ → ℝ) (x v w : ℝ) :
    fderiv ℝ (fderiv ℝ f) x v w = v * w * iteratedDeriv 2 f x := by
  have hh := iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod
    (f := f) (x := x) (m := ![v,w])
  simpa only [iteratedFDeriv_two_apply, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, smul_eq_mul] using hh

/-- Every actual one-dimensional Hessian has its ordinary second derivative
as a least eigenvalue. -/
theorem leastEigenpair (f : ℝ → ℝ) (x : ℝ) :
    SecondOrderTrustRegion.IsLeastEigenpair f x (iteratedDeriv 2 f x) 1 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · apply ext_inner_right ℝ
    intro w
    rw [TaylorModel.inner_hessianOperator,
      iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
    simp [Fin.prod_univ_two, RCLike.inner_apply, smul_eq_mul, mul_comm]
  · intro v hv
    have hv2 : v ^ 2 = 1 := by
      rw [Real.norm_eq_abs] at hv
      nlinarith [sq_abs v]
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
    simp only [Fin.prod_const, smul_eq_mul, hv2, one_mul]
    exact le_rfl

/-- Positive spacing gives a strictly increasing grid, with its exact step difference. -/
theorem grid_strictMono {t : ℝ} (ht : 0 < t) : StrictMono (grid t) := by
  intro i j hij
  exact mul_lt_mul_of_pos_right (by exact_mod_cast hij) ht

/-- The finite Taylor polynomial prescribed by the interpolation jets. -/
noncomputable def initialTaylor (ε t : ℝ) (N i : ℕ) (s : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 3, jet ε t N i j * s ^ j / j.factorial

/-- Every nonterminal prescribed Taylor polynomial is the actual concave quadratic form. -/
theorem initialTaylor_eq {ε t : ℝ} {N i : ℕ} (hi : i < N) (s : ℝ) :
    initialTaylor ε t N i s = value ε t N i - ε * s ^ 2 := by
  norm_num [initialTaylor, Finset.sum_range_succ, jet, curvature, hi]
  ring

/-- The exact derivatives through order two of the prescribed initial Taylor polynomial. -/
theorem initialTaylor_derivative {ε t : ℝ} {N i j : ℕ} (hi : i < N) (hj : j ≤ 2) (s : ℝ) :
    iteratedDeriv j (initialTaylor ε t N i) s =
      if j = 0 then value ε t N i - ε * s ^ 2 else if j = 1 then -2 * ε * s else -2 * ε := by
  have hd (z : ℝ) : HasDerivAt (initialTaylor ε t N i) (-2 * ε * z) z := by
    have heq : initialTaylor ε t N i = fun w => value ε t N i - ε * w ^ 2 :=
      funext (initialTaylor_eq hi)
    rw [heq]
    convert (hasDerivAt_const z (value ε t N i)).sub ((hasDerivAt_pow 2 z).const_mul ε) using 1
    ring
  interval_cases j
  · simpa only [iteratedDeriv_zero, ite_true] using initialTaylor_eq hi s
  · simpa [iteratedDeriv_succ, iteratedDeriv_zero] using (hd s).deriv
  · have heq : deriv (initialTaylor ε t N i) = fun z => -2 * ε * z :=
      funext (fun z => (hd z).deriv)
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero, heq]
    simp

/-- All actual Taylor-jet residuals have the uniform normalized bound needed for Hermite gluing. -/
theorem jet_residual_le {ε t : ℝ} {N i j : ℕ} (hε : 0 ≤ ε) (ht : 0 < t)
    (hi : i < N) (hj : j ≤ 2) :
    |jet ε t N (i + 1) j - iteratedDeriv j (initialTaylor ε t N i) t| ≤
      (2 * ε / t) * t ^ (2 - j + 1) := by
  rw [initialTaylor_derivative hi hj]
  interval_cases j
  · simp only [jet, ite_true]
    have hh : value ε t N (i + 1) - (value ε t N i - ε * t ^ 2) = 0 := by
      simp only [value, Nat.cast_add, Nat.cast_one]
      ring
    rw [hh, abs_zero]
    positivity
  · norm_num only [jet, ite_false, ite_true]
    have he : |-2 * ε * t| = 2 * ε * t := by
      rw [abs_of_nonpos (by nlinarith : -2 * ε * t ≤ 0)]
      ring
    rw [zero_sub, abs_neg, he]
    apply le_of_eq
    field_simp
  · norm_num only [jet, ite_false, ite_true]
    have he : (2 * ε / t) * t ^ (2 - 2 + 1) = 2 * ε := by norm_num; field_simp
    rw [he]
    by_cases hin : i + 1 < N
    · simp [curvature, hin, hε]
    · simp [curvature, hin, abs_of_nonneg hε]

/-- The integer iteration horizon is the ceiling required for an inverse-cube lower bound. -/
noncomputable def horizon (ε : ℝ) : ℕ := ⌈1 / ε ^ 3⌉₊

/-- The ceiling gives `ε³N ≤ 2`, correcting the source's invalid bound by one.
The lower count is exact and the objective gap therefore stays uniformly bounded. -/
theorem horizon_bounds {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 < horizon ε ∧ 1 / ε ^ 3 ≤ (horizon ε : ℝ) ∧ ε ^ 3 * horizon ε ≤ 2 := by
  have hp : 0 < ε ^ 3 := pow_pos hε 3
  have hu : ε ^ 3 ≤ 1 := pow_le_one₀ hε.le hε1
  have hh : (horizon ε : ℝ) < 1 / ε ^ 3 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hm := mul_lt_mul_of_pos_left hh hp
  rw [mul_add, mul_one, mul_div_cancel₀ _ hp.ne'] at hm
  exact ⟨Nat.ceil_pos.mpr (by positivity), Nat.le_ceil _, by linarith⟩

/-- A single fixed bound for all jets, step lengths and normalized residuals. -/
noncomputable def dataBound (σ : ℝ) : ℝ :=
  max (max (32 / σ ^ 2) 2) (max (4 / σ) (σ / 2))

/-- The prescribed step has exactly the scale needed by cubic-model stationarity. -/
theorem step_scale {σ ε : ℝ} (hσ : 0 < σ) : σ * (4 * ε / σ) = 4 * ε := by field_simp

/-- Every jet in the ceiling-length curvature grid has an accuracy-independent bound. -/
theorem uniform_jet_bounds {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let t := 4 * ε / σ
    let N := horizon ε
    0 < dataBound σ ∧ 0 < t ∧ t ≤ dataBound σ ∧
      (∀ i ≤ N, ∀ j ≤ 2, |jet ε t N i j| ≤ dataBound σ) ∧
      (∀ i < N, ∀ j ≤ 2,
        |jet ε t N (i + 1) j - iteratedDeriv j (initialTaylor ε t N i) t| ≤
          dataBound σ * t ^ (2 - j + 1)) := by
  let t := 4 * ε / σ
  let N := horizon ε
  have hκ₂ : (2 : ℝ) ≤ dataBound σ := (le_max_right _ _).trans (le_max_left _ _)
  have hκf : 32 / σ ^ 2 ≤ dataBound σ := (le_max_left _ _).trans (le_max_left _ _)
  have hκt : 4 / σ ≤ dataBound σ := (le_max_left _ _).trans (le_max_right _ _)
  have hκr : σ / 2 ≤ dataBound σ := (le_max_right _ _).trans (le_max_right _ _)
  have ht : 0 < t := by dsimp [t]; positivity
  have hs : σ * t = 4 * ε := step_scale hσ
  have hpow := (horizon_bounds hε hε1).2.2
  have hvalue : ∀ i ≤ N, 0 ≤ value ε t N i ∧ value ε t N i ≤ 32 / σ ^ 2 := by
    intro i hi
    have hin : (i : ℝ) ≤ N := by exact_mod_cast hi
    constructor
    · unfold value
      positivity
    · have he : value ε t N i * σ ^ 2 = 16 * ((N : ℝ) - i) * ε ^ 3 := by
        dsimp [value, t]
        field_simp
        ring
      apply (le_div_iff₀ (sq_pos_of_pos hσ)).mpr
      have hni : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
      nlinarith [mul_nonneg hni (pow_nonneg hε.le 3)]
  refine ⟨by linarith, ht, ?_, ?_, ?_⟩
  · apply le_trans _ hκt
    exact div_le_div_of_nonneg_right (by nlinarith) hσ.le
  · intro i hi j hj
    change |jet ε t N i j| ≤ dataBound σ
    interval_cases j
    · change |value ε t N i| ≤ _
      rw [abs_of_nonneg (hvalue i hi).1]
      exact (hvalue i hi).2.trans hκf
    · simpa [jet] using (by linarith : (0 : ℝ) ≤ dataBound σ)
    · change |curvature ε N i| ≤ _
      unfold curvature
      split_ifs
      · rw [abs_of_neg (by linarith : -2 * ε < 0)]
        linarith
      · simpa using (by linarith : (0 : ℝ) ≤ dataBound σ)
  · intro i hi j hj
    have he : 2 * ε / t = σ / 2 := by
      apply (div_eq_iff ht.ne').mpr
      nlinarith [hs]
    exact (jet_residual_le hε.le ht hi hj).trans
      (by rw [he]; exact mul_le_mul_of_nonneg_right hκr (pow_nonneg ht.le _))

/-- A single fixed regularization parameter `σ = 4` gives step `ε` and Hermite
bound `2`, independent of every accuracy and the ceiling-length grid. -/
theorem unit_step_uniform_bounds {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 < horizon ε ∧ StrictMono (grid ε) ∧
      (∀ i ≤ horizon ε, ∀ j ≤ 2, |jet ε ε (horizon ε) i j| ≤ 2) ∧
      (∀ i < horizon ε, ∀ j ≤ 2,
        |jet ε ε (horizon ε) (i + 1) j -
          iteratedDeriv j (initialTaylor ε ε (horizon ε) i) ε| ≤
            2 * ε ^ (2 - j + 1)) := by
  have hh := uniform_jet_bounds (σ := 4) (by norm_num) hε hε1
  norm_num [dataBound] at hh
  exact ⟨(horizon_bounds hε hε1).1, grid_strictMono hε, hh.2.2.1, hh.2.2.2⟩

namespace Data
variable {f : ℝ → ℝ} {ε t : ℝ} {N : ℕ}

/-- A genuine Hermite jet interpolant provides precisely the compatibility data. -/
theorem of_jets (hf : ContDiff ℝ 2 f)
    (hjets : ∀ i ≤ N, ∀ j ≤ 2, iteratedDeriv j f (grid t i) = jet ε t N i j) :
    Data f ε t N where
  regularity := hf
  values := fun i hi => by simpa [jet] using hjets i hi 0 (by omega)
  first := fun i hi => by
    simpa [jet, iteratedDeriv_succ, iteratedDeriv_zero] using hjets i hi 1 (by omega)
  second := fun i hi => by simpa [jet] using hjets i hi 2 (by omega)

/-- Prescribed zero first derivatives are actual zero Fréchet derivatives. -/
theorem fderiv_eq_zero (h : Data f ε t N) {i : ℕ} (hi : i ≤ N) :
    fderiv ℝ f (grid t i) = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  rw [fderiv_eq_deriv_mul, h.first i hi]
  simp

/-- The prescribed curvature is a genuine least Hessian eigenvalue at every grid point. -/
theorem leastEigenpair (h : Data f ε t N) {i : ℕ} (hi : i ≤ N) :
    SecondOrderTrustRegion.IsLeastEigenpair f (grid t i) (curvature ε N i) 1 := by
  rw [←h.second i hi]
  exact CurvatureSharpness.leastEigenpair f (grid t i)

/-- The actual nonterminal quadratic Taylor model is the prescribed concave quadratic. -/
theorem eval_two (h : Data f ε t N) {i : ℕ} (hi : i < N) (s : ℝ) :
    TaylorModel.eval f 2 (grid t i) s = value ε t N i - ε * s ^ 2 := by
  rw [TaylorModel.eval_two_eq, h.values i hi.le, h.fderiv_eq_zero hi.le,
    secondDerivative_apply, h.second i hi.le]
  simp only [curvature, ite_eq_left hi, zero_apply, add_zero]
  ring

/-- Consecutive prescribed values attain exactly the actual Taylor decrease. -/
theorem actual_ratio (h : Data f ε t N) (hε : 0 < ε) (ht : 0 < t)
    {i : ℕ} (hi : i < N) :
    (f (grid t i) - f (grid t i + t)) /
      (TaylorModel.eval f 2 (grid t i) 0 - TaylorModel.eval f 2 (grid t i) t) = 1 := by
  have hx : grid t i + t = grid t (i + 1) := by simp [grid, Nat.cast_add]; ring
  rw [hx, h.values i hi.le, h.values (i + 1) (by omega), h.eval_two hi 0, h.eval_two hi t]
  have hnum : value ε t N i - value ε t N (i + 1) = ε * t ^ 2 := by
    simp only [value, Nat.cast_add, Nat.cast_one]
    ring
  rw [hnum]
  have hden : value ε t N i - ε * (0 : ℝ) ^ 2 - (value ε t N i - ε * t ^ 2) = ε * t ^ 2 := by ring
  rw [hden, div_self (by positivity : ε * t ^ 2 ≠ 0)]

/-- The cubic step has exact first-order stationarity for the actual model. -/
theorem cubic_stationary {σ : ℝ} (h : Data f ε t N) (ht : 0 < t)
    (hscale : σ * t = 4 * ε) {i : ℕ} (hi : i < N) :
    fderiv ℝ (CubicRegularization.model f (grid t i) σ) t = 0 := by
  rw [CubicRegularization.fderiv_model h.regularity.contDiffAt, quadraticDerivative,
    h.fderiv_eq_zero hi.le, zero_add]
  apply ContinuousLinearMap.ext
  intro v
  simp only [add_apply, smul_apply, innerSL_apply_apply, RCLike.inner_apply,
    conj_trivial, smul_eq_mul, zero_apply]
  rw [secondDerivative_apply, h.second i hi.le, curvature, ite_eq_left hi,
    Real.norm_of_nonneg ht.le]
  nlinarith [congrArg (fun z : ℝ => z * t * v) hscale]

/-- The actual cubic-model Hessian at the computed step is positive semidefinite. -/
theorem cubic_curvature {σ : ℝ} (h : Data f ε t N) (ht : 0 < t)
    (hscale : σ * t = 4 * ε) {i : ℕ} (hi : i < N) (v : ℝ) :
    iteratedFDeriv ℝ 2 (CubicRegularization.model f (grid t i) σ) t (fun _ => v) =
      2 * ε * v ^ 2 := by
  rw [iteratedFDeriv_two_apply, CubicRegularization.fderiv_fderiv_model h.regularity.contDiffAt]
  simp only [add_apply]
  rw [secondDerivative_apply, h.second i hi.le, curvature, ite_eq_left hi,
    CubicRegularization.penaltySecondDerivative_apply]
  simp only [Real.norm_of_nonneg ht.le, RCLike.inner_apply, conj_trivial]
  field_simp
  nlinarith [congrArg (fun z : ℝ => z * v ^ 2 * t) hscale]

/-- These actual jets generate a genuine finite-tolerance AR2 run. -/
theorem cubic_finiteRun {η₁ η₂ γ₁ γ₂ γ₃ θ₁ θ₂ σ ε₁ : ℝ}
    (h : Data f ε t N)
    (hη₁ : 0 < η₁) (hη : η₁ ≤ η₂) (hη₂ : η₂ < 1)
    (hγ₁ : 0 < γ₁) (hγ₁1 : γ₁ < 1) (hγ₂ : 1 < γ₂) (hγ₃ : γ₂ < γ₃)
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (hσ : 0 < σ)
    (hε₁ : 0 < ε₁) (hε₁1 : ε₁ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ht : 0 < t) (hscale : σ * t = 4 * ε) :
    CubicRegularization.FiniteRun f (grid t) (fun _ => t) (fun _ => 1)
      (curvature ε N) (fun _ => σ) (fun _ => 1)
      η₁ η₂ γ₁ γ₂ γ₃ σ θ₁ θ₂ ε₁ ε N := by
  have hη₁1 : η₁ ≤ 1 := hη.trans hη₂.le
  refine ⟨⟨?_, ?_, ?_⟩, hθ₁, hθ₂, hε₁, hε₁1, hε, hε1,
    (fun i hi => h.leastEigenpair hi), ?_, ?_, ?_, ?_⟩
  · refine ⟨hσ, le_rfl, hη₁, hη, hη₂, hγ₁, hγ₁1, hγ₂, hγ₃, ?_⟩
    intro i hi
    rw [ite_eq_left hη₂.le]
    exact ⟨max_le le_rfl (by nlinarith), le_rfl⟩
  · intro i hi
    unfold CubicRegularization.model ModelDecrease.penalized
    norm_num only [Nat.reduceAdd, Nat.factorial, Nat.cast_ofNat]
    rw [h.eval_two hi t, h.eval_two hi 0, Real.norm_of_nonneg ht.le, norm_zero]
    have hs : σ * t ^ 3 = 4 * ε * t ^ 2 := by nlinarith [congrArg (fun z : ℝ => z * t ^ 2) hscale]
    nlinarith [mul_pos hε (sq_pos_of_pos ht)]
  · intro i hi
    exact (h.actual_ratio hε ht hi).symm
  · intro i hi
    exact Or.inr (by simp only [curvature, ite_eq_left hi]; linarith)
  · intro i hi
    rw [h.cubic_stationary ht hscale hi, norm_zero]
    positivity
  · intro i hi v hv
    rw [h.cubic_curvature ht hscale hi v]
    exact (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hθ₂.le) (norm_nonneg t)).trans
      (by positivity)
  · intro i hi
    rw [ite_eq_left hη₁1]
    simp [grid, Nat.cast_add]
    ring

/-- The prescribed zero derivative is the actual zero Riesz gradient. -/
theorem gradient_eq_zero (h : Data f ε t N) {i : ℕ} (hi : i ≤ N) :
    gradient f (grid t i) = 0 := by
  apply (InnerProductSpace.toDual ℝ ℝ).injective
  rw [toDual_gradient, map_zero, h.fderiv_eq_zero hi]

/-- With zero gradient, the actual Cauchy-ray model is constant. -/
theorem cauchyPoint (h : Data f ε t N) (ht : 0 ≤ t) {i : ℕ} (hi : i < N) :
    SecondOrderTrustRegion.IsCauchyPoint f (grid t i) t 0 := by
  refine ⟨0, le_rfl, by simpa using ht, by simp, ?_⟩
  intro r hr
  simp [h.gradient_eq_zero hi.le]

/-- A concave actual quadratic attains its eigen-ray minimum at the radius boundary. -/
theorem eigenPoint (h : Data f ε t N) (hε : 0 ≤ ε) (ht : 0 ≤ t)
    {i : ℕ} (hi : i < N) :
    TaylorModel.IsEigenPoint f (grid t i) 1 t t := by
  refine ⟨t, ⟨ht, le_rfl⟩, by simp, ?_⟩
  intro r hr
  change TaylorModel.eval f 2 (grid t i) (t • (1 : ℝ)) ≤
    TaylorModel.eval f 2 (grid t i) (r • (1 : ℝ))
  simp only [smul_eq_mul, mul_one]
  rw [h.eval_two hi t, h.eval_two hi r]
  nlinarith [sq_le_sq₀ hr.1 ht |>.mpr hr.2,
    mul_nonneg hε (sub_nonneg.mpr (sq_le_sq₀ hr.1 ht |>.mpr hr.2))]

/-- The actual interpolation jets generate every operational TR2 rule, with a constant
positive radius and acceptance ratio one. No algorithm rule is included in `Data`. -/
theorem trustRegion_run (h : Data f ε t N)
    {η₁ η₂ γ₁ γ₂ γ₃ ε₁ : ℝ}
    (hη₁ : 0 < η₁) (hη : η₁ ≤ η₂) (hη₂ : η₂ < 1)
    (hγ₁ : 0 < γ₁) (hγ : γ₁ ≤ γ₂) (hγ₂ : γ₂ < 1) (hγ₃ : 1 < γ₃)
    (hε₁ : 0 < ε₁) (hε : 0 < ε) (ht : 0 < t) :
    SecondOrderTrustRegion.Run f (grid t) (fun _ => t) (fun _ => 0) (fun _ => t)
      (fun _ => 1) (curvature ε N) (fun _ => t) (fun _ => 1)
      η₁ η₂ γ₁ γ₂ γ₃ ε₁ ε N := by
  have hη₁1 : η₁ ≤ 1 := hη.trans hη₂.le
  refine ⟨?_, hε₁, hε, (fun i hi => h.leastEigenpair hi), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨ht, hη₁, hη, hη₂, hγ₁, hγ, hγ₂, hγ₃, ?_⟩
    intro i hi
    rw [ite_eq_left hη₂.le]
    exact ⟨le_rfl, by nlinarith⟩
  · intro i hi
    simp [h.gradient_eq_zero hi.le]
  · intro i hi
    exact Or.inr (by simp only [curvature, ite_eq_left hi]; linarith)
  · intro i hi
    exact h.cauchyPoint ht.le hi
  · intro i hi
    have hm : curvature ε N i < 0 := by simp [curvature, hi]; linarith
    rw [ite_eq_left hm]
    exact h.eigenPoint hε.le ht.le hi
  · intro i hi
    exact le_of_eq (Real.norm_of_nonneg ht.le)
  · intro i hi
    rw [h.eval_two hi t, h.eval_two hi 0]
    nlinarith [sq_nonneg t]
  · intro i hi
    exact le_rfl
  · intro i hi
    exact (h.actual_ratio hε ht hi).symm
  · intro i hi
    rw [ite_eq_left hη₁1]
    simp [grid, Nat.cast_add]
    ring

/-- All accepted curvature trials are genuinely necessary before either algorithm can stop. -/
theorem first_stopping_index (h : Data f ε t N) (hε : 0 < ε) {ε₁ : ℝ}
    (hε₁ : 0 ≤ ε₁) :
    (∀ i < N, ¬(‖fderiv ℝ f (grid t i)‖ ≤ ε₁ ∧ -ε ≤ curvature ε N i)) ∧
      (‖fderiv ℝ f (grid t N)‖ ≤ ε₁ ∧ -ε ≤ curvature ε N N) := by
  constructor
  · intro i hi hh
    have hc := hh.2
    simp only [curvature, ite_eq_left hi] at hc
    linarith
  · simp only [h.fderiv_eq_zero le_rfl, norm_zero, curvature, lt_self_iff_false, ite_false]
    exact ⟨hε₁, by linarith⟩

/-- Because every actual ratio equals one, objective and derivative counts include exactly
one initial evaluation and every one of the `N` accepted curvature trials. -/
theorem successful_count {η₁ : ℝ} (hη : η₁ ≤ 1) :
    (EvaluationComplexity.successfulIterations
      {i : ℕ | η₁ ≤ (fun _ : ℕ => (1 : ℝ)) i} N).card = N := by
  simp [EvaluationComplexity.successfulIterations, hη]

/-- Both algorithms make exactly one initialized function, gradient and Hessian call
per accepted interpolation point. -/
theorem initialized_counts {η₁ : ℝ} (hη : η₁ ≤ 1) :
    SecondOrderTrustRegion.functionEvaluations N = N + 1 ∧
      SecondOrderTrustRegion.gradientEvaluations (fun _ => 1) η₁ N = N + 1 ∧
      SecondOrderTrustRegion.hessianEvaluations (fun _ => 1) η₁ N = N + 1 ∧
      CubicRegularization.functionEvaluations N = N + 1 ∧
      CubicRegularization.gradientEvaluations (fun _ => 1) η₁ N = N + 1 ∧
      CubicRegularization.hessianEvaluations (fun _ => 1) η₁ N = N + 1 := by
  simp [SecondOrderTrustRegion.functionEvaluations, SecondOrderTrustRegion.gradientEvaluations,
    SecondOrderTrustRegion.hessianEvaluations, SecondOrderTrustRegion.derivativeEvaluations,
    CubicRegularization.functionEvaluations, CubicRegularization.gradientEvaluations,
    CubicRegularization.hessianEvaluations, CubicRegularization.derivativeEvaluations,
    EvaluationComplexity.successfulIterations, hη]

/-- A uniformly bounded Hermite interpolant supplies a global lower bound and an
accuracy-independent initial objective budget. -/
theorem initial_objective_gap {σ B : ℝ} (hσ : 0 < σ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (h : Data f ε (4 * ε / σ) (horizon ε)) (hbound : ∀ y, |f y| ≤ B) :
    (∀ y, -B ≤ f y) ∧ f 0 - (-B) ≤ dataBound σ + B := by
  have hv := (uniform_jet_bounds hσ hε hε1).2.2.2.1 0 (Nat.zero_le _) 0 (by omega)
  have hvalue := h.values 0 (Nat.zero_le _)
  simp only [grid, Nat.cast_zero, zero_mul] at hvalue
  change |value ε (4 * ε / σ) (horizon ε) 0| ≤ dataBound σ at hv
  constructor
  · intro y
    exact (abs_le.mp (hbound y)).1
  · rw [←hvalue] at hv
    linarith [(abs_le.mp hv).2]

/-- Both actual stopping tests hold at the terminal grid point. -/
theorem terminal (h : Data f ε t N) :
    ‖fderiv ℝ f (grid t N)‖ = 0 ∧ curvature ε N N = 0 := by
  simp [h.fderiv_eq_zero le_rfl, curvature]
end Data
end CurvatureSharpness
