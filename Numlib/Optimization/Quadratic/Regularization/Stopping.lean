import Numlib.Analysis.InnerProductSpace.NormPow.Second
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Numlib.Analysis.InnerProductSpace.Energy

/-!
# Constructive stopping tests for regularized quadratic models
-/

namespace QuadraticRegularization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A constant-free quadratic plus an actual real norm-power penalty. -/
noncomputable def model (ℓ : E →L[ℝ] ℝ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (σ r : ℝ) (s : E) : ℝ := ℓ s + B s s / 2 + σ / r * ‖s‖ ^ r

/-- The genuine first derivative of the regularized quadratic. -/
theorem hasFDerivAt_model (ℓ : E →L[ℝ] ℝ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) {r : ℝ} (hr : 2 < r) (σ : ℝ) (s : E) :
    HasFDerivAt (model ℓ B σ r)
      (ℓ + B s + (σ / r) • NormPower.first r s) s := by
  have hq : HasFDerivAt (fun z : E => B z z / 2) (B s) s := by
    have hh := (B.hasFDerivAt.clm_apply (hasFDerivAt_id s)).const_mul (1 / 2 : ℝ)
    convert hh using 1
    · funext z
      simp only [id_eq]
      ring
    · ext v
      simp only [add_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.flip_apply, ContinuousLinearMap.id_apply, id_eq,
        smul_apply, smul_eq_mul]
      rw [hB v s]
      ring
  exact (ℓ.hasFDerivAt.add hq).add
    ((NormPower.hasFDerivAt_normPower (by linarith : 1 < r) s).const_mul (σ / r))

/-- The actual continuous linear first derivative has its explicit formula. -/
theorem fderiv_model (ℓ : E →L[ℝ] ℝ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) {r : ℝ} (hr : 2 < r) (σ : ℝ) (s : E) :
    fderiv ℝ (model ℓ B σ r) s = ℓ + B s + (σ / r) • NormPower.first r s :=
  (hasFDerivAt_model ℓ B hB hr σ s).fderiv

/-- The actual curried Hessian includes the complete norm-power Hessian. -/
theorem fderiv_fderiv_model (ℓ : E →L[ℝ] ℝ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) {r : ℝ} (hr : 2 < r) (σ : ℝ) (s : E) :
    fderiv ℝ (fderiv ℝ (model ℓ B σ r)) s = B + (σ / r) • NormPower.second r s := by
  have he : fderiv ℝ (model ℓ B σ r) =
      fun z => ℓ + B z + (σ / r) • NormPower.first r z :=
    funext (fderiv_model ℓ B hB hr σ)
  rw [he]
  have hh := ((hasFDerivAt_const ℓ s).add B.hasFDerivAt).add
    ((NormPower.hasFDerivAt_first_of_two_lt hr s).const_smul (σ / r))
  have hfun : ((fun _ : E => ℓ) + ⇑B + (σ / r) • NormPower.first r) =
      (fun z => ℓ + B z + (σ / r) • NormPower.first r z) := by funext z; rfl
  rw [← hfun]
  simpa only [zero_add] using hh.fderiv

/-- At a shifted linear-system solution, the true model derivative is radial. -/
theorem fderiv_model_eq_radial (ℓ : E →L[ℝ] ℝ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) {r : ℝ} (hr : 2 < r)
    {σ τ : ℝ} {s : E} (hsolve : ℓ + B s = -τ • innerSL ℝ s) :
    fderiv ℝ (model ℓ B σ r) s =
      (σ * ‖s‖ ^ (r - 2) - τ) • innerSL ℝ s := by
  rw [fderiv_model ℓ B hB hr, hsolve, NormPower.first, smul_smul, ← add_smul]
  have hr0 : r ≠ 0 := by linarith
  congr 1
  field_simp
  ring

/-- The actual weighted-dual derivative norm is the scalar secular residual times the radius. -/
theorem norm_fderiv_model (ℓ : E →L[ℝ] ℝ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) {r : ℝ} (hr : 2 < r)
    {σ τ : ℝ} {s : E} (hsolve : ℓ + B s = -τ • innerSL ℝ s) :
    ‖fderiv ℝ (model ℓ B σ r) s‖ = |σ * ‖s‖ ^ (r - 2) - τ| * ‖s‖ := by
  rw [fderiv_model_eq_radial ℓ B hB hr hsolve, norm_smul,
    Real.norm_eq_abs, innerSL_apply_norm]

/-- The constant-free model vanishes at zero. -/
@[simp] theorem model_zero (ℓ : E →L[ℝ] ℝ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    {r : ℝ} (hr : 2 < r) (σ : ℝ) : model ℓ B σ r 0 = 0 := by
  simp [model, Real.zero_rpow (by linarith : r ≠ 0)]

omit [InnerProductSpace ℝ E] in
/-- Rewriting the secular power in terms of the actual radius. -/
theorem sq_rpow_half (s : E) (a : ℝ) : (‖s‖ ^ 2) ^ (a / 2) = ‖s‖ ^ a := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg s)]
  congr 1
  ring

omit [InnerProductSpace ℝ E] in
/-- The upper secular test implies the radius inequality needed for model decrease. -/
theorem radius_bound {r σ τ : ℝ} (hr : 2 < r) (hσ : 0 < σ) (hτ : 0 ≤ τ)
    {s : E} (hu : ‖s‖ ^ 2 ≤
      (r / 2) ^ (2 / (r - 2)) * (τ / σ) ^ (2 / (r - 2))) :
    σ / r * ‖s‖ ^ (r - 2) ≤ τ / 2 := by
  have hr0 : 0 < r := by linarith
  have hd : 0 < r - 2 := by linarith
  have he : 2 / (r - 2) * ((r - 2) / 2) = 1 := by field_simp
  have hh := Real.rpow_le_rpow (sq_nonneg ‖s‖) hu (by positivity : 0 ≤ (r - 2) / 2)
  rw [sq_rpow_half, Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul (by positivity : 0 ≤ r / 2),
    ← Real.rpow_mul (div_nonneg hτ hσ.le), he, Real.rpow_one, Real.rpow_one] at hh
  have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ σ / r)
  calc
    σ / r * ‖s‖ ^ (r - 2) ≤ σ / r * (r / 2 * (τ / σ)) := hm
    _ = τ / 2 := by field_simp

/-- A genuine shifted-system solution satisfies the model-value identity. -/
theorem model_eq_shifted (ℓ : E →L[ℝ] ℝ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    {r : ℝ} (hr : 2 < r) {σ τ : ℝ} {s : E}
    (hsolve : ℓ + B s = -τ • innerSL ℝ s) :
    model ℓ B σ r s = -(B s s + τ * ‖s‖ ^ 2) / 2 +
      ‖s‖ ^ 2 * (σ / r * ‖s‖ ^ (r - 2) - τ / 2) := by
  have hs := congrArg (fun L : E →L[ℝ] ℝ => L s) hsolve
  simp only [add_apply, smul_apply, innerSL_apply_apply, smul_eq_mul,
    real_inner_self_eq_norm_sq] at hs
  have hp : ‖s‖ ^ r = ‖s‖ ^ 2 * ‖s‖ ^ (r - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add' (norm_nonneg s) (by linarith)]
    congr 1
    ring
  dsimp [model]
  rw [hp]
  nlinarith

/-- The upper test and shifted positive semidefiniteness give actual model decrease. -/
theorem model_nonpos (ℓ : E →L[ℝ] ℝ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    {r : ℝ} (hr : 2 < r) {σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 ≤ τ) {s : E}
    (hsolve : ℓ + B s = -τ • innerSL ℝ s)
    (hpsd : ∀ v, 0 ≤ B v v + τ * ‖v‖ ^ 2)
    (hu : ‖s‖ ^ 2 ≤ (r / 2) ^ (2 / (r - 2)) * (τ / σ) ^ (2 / (r - 2))) :
    model ℓ B σ r s ≤ 0 := by
  rw [model_eq_shifted ℓ B hr hsolve]
  have hv := radius_bound hr hσ hτ hu
  have hm := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg ‖s‖) (sub_nonpos.mpr hv)
  linarith [hpsd s]

/-- The central secular test controls the actual derivative norm. -/
theorem norm_fderiv_model_le (ℓ : E →L[ℝ] ℝ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) {r : ℝ} (hr : 2 < r)
    {σ τ θ : ℝ} (hσ : 0 < σ) {s : E}
    (hsolve : ℓ + B s = -τ • innerSL ℝ s)
    (hc : |(‖s‖ ^ 2) ^ ((r - 2) / 2) - τ / σ| ≤
      θ / (2 * σ) * (‖s‖ ^ 2) ^ (1 / 2 : ℝ)) :
    ‖fderiv ℝ (model ℓ B σ r) s‖ ≤ θ / 2 * ‖s‖ ^ 2 := by
  rw [norm_fderiv_model ℓ B hB hr hsolve]
  rw [sq_rpow_half, sq_rpow_half] at hc
  norm_num at hc
  have hi : σ * ‖s‖ ^ (r - 2) - τ =
      σ * (‖s‖ ^ (r - 2) - τ / σ) := by field_simp
  rw [hi, abs_mul, abs_of_pos hσ]
  have hh := mul_le_mul_of_nonneg_left hc hσ.le
  have he : σ * (θ / (2 * σ) * ‖s‖) = θ / 2 * ‖s‖ := by field_simp
  rw [he] at hh
  have hm := mul_le_mul_of_nonneg_right hh (norm_nonneg s)
  nlinarith

/-- The actual Hessian separates its nonnegative rank-one correction. -/
theorem fderiv_fderiv_model_apply (ℓ : E →L[ℝ] ℝ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ v w, B v w = B w v)
    {r : ℝ} (hr : 2 < r) (σ : ℝ) (s v : E) :
    fderiv ℝ (fderiv ℝ (model ℓ B σ r)) s v v =
      B v v + σ * ‖s‖ ^ (r - 2) * ‖v‖ ^ 2 +
        (r - 2) * σ * ‖s‖ ^ (r - 4) * (inner ℝ s v) ^ 2 := by
  rw [fderiv_fderiv_model ℓ B hB hr]
  simp only [add_apply, smul_apply, smul_eq_mul, NormPower.second_apply,
    real_inner_self_eq_norm_sq]
  have hr0 : r ≠ 0 := by linarith
  field_simp
  ring

/-- The one-sided secular test bounds every genuine unit-direction Hessian value. -/
theorem hessian_lower (ℓ : E →L[ℝ] ℝ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) {r : ℝ} (hr : 2 < r)
    {σ τ θ : ℝ} (hσ : 0 < σ) {s : E}
    (hpsd : ∀ v, 0 ≤ B v v + τ * ‖v‖ ^ 2)
    (hl : -θ / σ * (‖s‖ ^ 2) ^ (1 / 2 : ℝ) ≤
      (‖s‖ ^ 2) ^ ((r - 2) / 2) - τ / σ)
    {v : E} (hv : ‖v‖ = 1) :
    -θ * ‖s‖ ≤ fderiv ℝ (fderiv ℝ (model ℓ B σ r)) s v v := by
  rw [sq_rpow_half, sq_rpow_half] at hl
  norm_num at hl
  have hm := mul_le_mul_of_nonneg_left hl hσ.le
  have hleft : σ * (-θ / σ * ‖s‖) = -θ * ‖s‖ := by field_simp
  have hright : σ * (‖s‖ ^ (r - 2) - τ / σ) =
      σ * ‖s‖ ^ (r - 2) - τ := by field_simp
  rw [hleft, hright] at hm
  rw [fderiv_fderiv_model_apply ℓ B hB hr, hv]
  have hp : 0 ≤ (r - 2) * σ * ‖s‖ ^ (r - 4) * (inner ℝ s v) ^ 2 := by
    positivity
  have hh := hpsd v
  rw [hv] at hh
  norm_num at hh ⊢
  linarith

/-- All three source secular tests certify the actual model stopping inequalities. -/
theorem stopping_tests (ℓ : E →L[ℝ] ℝ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) {r : ℝ} (hr : 2 < r)
    {σ τ θ₁ θ₂ : ℝ} (hσ : 0 < σ) (hτ : 0 ≤ τ) {s : E}
    (hsolve : ℓ + B s = -τ • innerSL ℝ s)
    (hpsd : ∀ v, 0 ≤ B v v + τ * ‖v‖ ^ 2)
    (hu : ‖s‖ ^ 2 ≤ (r / 2) ^ (2 / (r - 2)) * (τ / σ) ^ (2 / (r - 2)))
    (hc : |(‖s‖ ^ 2) ^ ((r - 2) / 2) - τ / σ| ≤
      θ₁ / (2 * σ) * (‖s‖ ^ 2) ^ (1 / 2 : ℝ))
    (hl : -θ₂ / σ * (‖s‖ ^ 2) ^ (1 / 2 : ℝ) ≤
      (‖s‖ ^ 2) ^ ((r - 2) / 2) - τ / σ) :
    model ℓ B σ r s ≤ model ℓ B σ r 0 ∧
      ‖fderiv ℝ (model ℓ B σ r) s‖ ≤ θ₁ / 2 * ‖s‖ ^ 2 ∧
      ∀ v : E, ‖v‖ = 1 →
        -θ₂ * ‖s‖ ≤ fderiv ℝ (fderiv ℝ (model ℓ B σ r)) s v v := by
  rw [model_zero ℓ B hr]
  exact ⟨model_nonpos ℓ B hr hσ hτ hsolve hpsd hu,
    norm_fderiv_model_le ℓ B hB hr hσ hsolve hc,
    fun _ hv => hessian_lower ℓ B hB hr hσ hpsd hl hv⟩

namespace Metric

variable (M : E →L[ℝ] E) (hM : M.toLinearMap.IsSymmetricCoercive)

/-- The identity from the metric inner product space to the original space, bundled continuously. -/
noncomputable def toOriginal : WithEnergy M.toLinearMap hM →L[ℝ] E :=
  ⟨(WithEnergy.equiv M.toLinearMap hM).symm.toLinearMap,
    (WithEnergy.continuous_equiv hM).2⟩

/-- The original linear term, expressed in metric coordinates. -/
noncomputable def linearTerm (g : E) : WithEnergy M.toLinearMap hM →L[ℝ] ℝ :=
  (innerSL ℝ g).comp (toOriginal M hM)

/-- The original symmetric quadratic form, expressed in metric coordinates. -/
noncomputable def quadraticTerm (H : E →L[ℝ] E) :
    WithEnergy M.toLinearMap hM →L[ℝ] WithEnergy M.toLinearMap hM →L[ℝ] ℝ :=
  ((ContinuousLinearMap.precompR _ ((innerSL ℝ).comp H)).flip (toOriginal M hM)).comp
    (toOriginal M hM)

/-- Evaluation of the transported linear term. -/
@[simp] theorem linearTerm_apply (g : E) (s : WithEnergy M.toLinearMap hM) :
    linearTerm M hM g s = inner ℝ g (toOriginal M hM s) := rfl

/-- Evaluation of the transported bilinear form. -/
@[simp] theorem quadraticTerm_apply (H : E →L[ℝ] E)
    (s v : WithEnergy M.toLinearMap hM) :
    quadraticTerm M hM H s v = inner ℝ (H (toOriginal M hM s)) (toOriginal M hM v) := rfl

/-- A symmetric original Hessian remains symmetric in metric coordinates. -/
theorem quadraticTerm_symmetric (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (v w : WithEnergy M.toLinearMap hM) :
    quadraticTerm M hM H v w = quadraticTerm M hM H w v := by
  simp only [quadraticTerm_apply]
  exact (hH _ _).trans (real_inner_comm _ _)

/-- The metric-coordinate model is the actual original weighted quadratic expression. -/
theorem model_eq (g : E) (H : E →L[ℝ] E) (σ r : ℝ) (s : E) :
    model (linearTerm M hM g) (quadraticTerm M hM H) σ r
      (WithEnergy.equiv M.toLinearMap hM s) =
      inner ℝ g s + inner ℝ (H s) s / 2 + σ / r * energyNorm M.toLinearMap s ^ r := rfl

/-- An original shifted linear-system equation gives the true metric radial equation. -/
theorem radial_equation (g : E) (H : E →L[ℝ] E) {τ : ℝ} {s : E}
    (hsolve : (H + τ • M) s = -g) :
    linearTerm M hM g + quadraticTerm M hM H (WithEnergy.equiv M.toLinearMap hM s) =
      -τ • innerSL ℝ (WithEnergy.equiv M.toLinearMap hM s) := by
  ext v
  change inner ℝ g (toOriginal M hM v) + inner ℝ (H s) (toOriginal M hM v) =
    -τ * inner ℝ (M s) (toOriginal M hM v)
  have hs : H s + τ • M s = -g := hsolve
  have hv := congrArg (fun z : E => inner ℝ z (toOriginal M hM v)) hs
  simp only [inner_add_left, inner_smul_left, inner_neg_left, conj_trivial] at hv
  linarith

/-- Positive semidefiniteness of the actual shifted pencil transports to metric coordinates. -/
theorem shifted_nonneg (H : E →L[ℝ] E) {τ : ℝ}
    (hpsd : ∀ v, 0 ≤ inner ℝ ((H + τ • M) v) v)
    (v : WithEnergy M.toLinearMap hM) :
    0 ≤ quadraticTerm M hM H v v + τ * ‖v‖ ^ 2 := by
  have hh := hpsd (toOriginal M hM v)
  have he : ‖v‖ ^ 2 = inner ℝ (M (toOriginal M hM v)) (toOriginal M hM v) := by
    exact (real_inner_self_eq_norm_sq v).symm
  rw [he]
  simpa only [quadraticTerm_apply, add_apply, smul_apply, inner_add_left,
    inner_smul_left, conj_trivial] using hh

/-- The actual weighted quadratic expression viewed as a function on the metric space. -/
noncomputable def coordinateModel (g : E) (H : E →L[ℝ] E) (σ r : ℝ)
    (z : WithEnergy M.toLinearMap hM) : ℝ :=
  inner ℝ g (toOriginal M hM z) +
    inner ℝ (H (toOriginal M hM z)) (toOriginal M hM z) / 2 +
    σ / r * energyNorm M.toLinearMap (toOriginal M hM z) ^ r

/-- The transported weighted expression agrees with the genuine inner product model. -/
theorem coordinateModel_eq_model (g : E) (H : E →L[ℝ] E) (σ r : ℝ) :
    coordinateModel M hM g H σ r = model (linearTerm M hM g) (quadraticTerm M hM H) σ r :=
  rfl

/-- The three secular tests certify the actual weighted model and both of its actual derivatives.
The Hessian conclusion is its lower bound on every metric-unit direction. -/
theorem stopping_tests (g : E) (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    {r : ℝ} (hr : 2 < r) {σ τ θ₁ θ₂ : ℝ} (hσ : 0 < σ) (hτ : 0 ≤ τ) {s : E}
    (hsolve : (H + τ • M) s = -g)
    (hpsd : ∀ v, 0 ≤ inner ℝ ((H + τ • M) v) v)
    (hu : energyNorm M.toLinearMap s ^ 2 ≤
      (r / 2) ^ (2 / (r - 2)) * (τ / σ) ^ (2 / (r - 2)))
    (hc : |(energyNorm M.toLinearMap s ^ 2) ^ ((r - 2) / 2) - τ / σ| ≤
      θ₁ / (2 * σ) * (energyNorm M.toLinearMap s ^ 2) ^ (1 / 2 : ℝ))
    (hl : -θ₂ / σ * (energyNorm M.toLinearMap s ^ 2) ^ (1 / 2 : ℝ) ≤
      (energyNorm M.toLinearMap s ^ 2) ^ ((r - 2) / 2) - τ / σ) :
    let m := coordinateModel M hM g H σ r
    let z := WithEnergy.equiv M.toLinearMap hM s
    m z ≤ m 0 ∧ ‖fderiv ℝ m z‖ ≤ θ₁ / 2 * energyNorm M.toLinearMap s ^ 2 ∧
      ∀ v : WithEnergy M.toLinearMap hM, ‖v‖ = 1 →
        -θ₂ * energyNorm M.toLinearMap s ≤ fderiv ℝ (fderiv ℝ m) z v v := by
  dsimp only
  rw [coordinateModel_eq_model]
  exact QuadraticRegularization.stopping_tests _ _ (quadraticTerm_symmetric M hM H hH)
    hr hσ hτ (radial_equation M hM g H hsolve) (shifted_nonneg M hM H hpsd) hu hc hl

end Metric
end QuadraticRegularization
