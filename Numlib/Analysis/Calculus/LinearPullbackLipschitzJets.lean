import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Tactic

/-!
# Lipschitz jets under bounded linear pullback

The actual order-`n` derivative tensor changes by at most the `n`th power of the
linear map norm under pullback. Its Lipschitz constant includes one further power
for the movement of the base point. Scalar iterated derivatives transport to the
full ambient tensor norm, and sums preserve the resulting estimates.
-/

open scoped NNReal

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Pulling back the difference of actual derivative tensors costs one linear-map norm
for each direction slot. -/
theorem ContinuousLinearMap.norm_iteratedFDeriv_comp_sub_le
    (K : E →L[ℝ] F) {f : F → G} {n : ℕ} (hf : ContDiff ℝ n f) (x y : E) :
    ‖iteratedFDeriv ℝ n (f ∘ K) x - iteratedFDeriv ℝ n (f ∘ K) y‖ ≤
      ‖iteratedFDeriv ℝ n f (K x) - iteratedFDeriv ℝ n f (K y)‖ * ‖K‖ ^ n := by
  rw [K.iteratedFDeriv_comp_right hf x le_rfl,
    K.iteratedFDeriv_comp_right hf y le_rfl]
  have hsub :
      (iteratedFDeriv ℝ n f (K x)).compContinuousLinearMap (fun _ => K) -
        (iteratedFDeriv ℝ n f (K y)).compContinuousLinearMap (fun _ => K) =
      (iteratedFDeriv ℝ n f (K x) - iteratedFDeriv ℝ n f (K y)).compContinuousLinearMap
        (fun _ => K) := by
    ext v
    rfl
  rw [hsub]
  simpa using ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ n f (K x) - iteratedFDeriv ℝ n f (K y)) (fun _ => K)

/-- Scalar iterated derivatives capture exactly the norm of a scalar derivative-tensor
 difference, including derivative order zero. -/
theorem norm_iteratedFDeriv_scalar_sub (f : ℝ → G) (n : ℕ) (x y : ℝ) :
    ‖iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n f y‖ =
      ‖iteratedDeriv n f x - iteratedDeriv n f y‖ := by
  simp only [iteratedFDeriv_eq_equiv_comp, Function.comp_apply, ← map_sub,
    LinearIsometryEquiv.norm_map]

/-- A derivative's global Lipschitz constant gains one power of the linear-map norm
for the base point and one for each direction slot. -/
theorem ContinuousLinearMap.lipschitzWith_iteratedFDeriv_comp
    (K : E →L[ℝ] F) {f : F → G} {n : ℕ} (hf : ContDiff ℝ n f) {L : ℝ≥0}
    (hL : LipschitzWith L (iteratedFDeriv ℝ n f)) :
    LipschitzWith (L * ‖K‖₊ ^ (n + 1)) (iteratedFDeriv ℝ n (f ∘ K)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n f (K x) - iteratedFDeriv ℝ n f (K y)‖ * ‖K‖ ^ n :=
      K.norm_iteratedFDeriv_comp_sub_le hf x y
    _ ≤ ((L : ℝ) * ‖K x - K y‖) * ‖K‖ ^ n := by
      gcongr
      simpa only [dist_eq_norm] using hL.dist_le_mul (K x) (K y)
    _ ≤ ((L : ℝ) * (‖K‖ * ‖x - y‖)) * ‖K‖ ^ n := by
      gcongr
      simpa only [map_sub] using K.le_opNorm (x - y)
    _ = _ := by
      simp only [NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm]
      rw [pow_succ]
      ring

/-- A scalar iterated derivative bound controls the full tensor after a bounded linear
functional, without restricting any ambient direction. -/
theorem ContinuousLinearMap.lipschitzWith_iteratedFDeriv_scalar_comp
    (K : E →L[ℝ] ℝ) {f : ℝ → G} {n : ℕ} (hf : ContDiff ℝ n f) {L : ℝ≥0}
    (hL : LipschitzWith L (iteratedDeriv n f)) :
    LipschitzWith (L * ‖K‖₊ ^ (n + 1)) (iteratedFDeriv ℝ n (f ∘ K)) := by
  apply K.lipschitzWith_iteratedFDeriv_comp hf
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, norm_iteratedFDeriv_scalar_sub]
  simpa only [dist_eq_norm] using hL.dist_le_mul x y

/-- The actual derivative tensors of a sum have the sum of the two global Lipschitz
constants. -/
theorem lipschitzWith_iteratedFDeriv_add {f g : E → F} {n : ℕ}
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) {L M : ℝ≥0}
    (hL : LipschitzWith L (iteratedFDeriv ℝ n f))
    (hM : LipschitzWith M (iteratedFDeriv ℝ n g)) :
    LipschitzWith (L + M) (iteratedFDeriv ℝ n (fun x => f x + g x)) := by
  simpa only [fun_iteratedFDeriv_add hf hg] using hL.add hM

/-- Any specified first and second scalar derivatives determine the actual second
iterated derivative, independently of how those functions are defined. -/
theorem iteratedDeriv_two_eq_of_hasDerivAt {f f₁ f₂ : ℝ → ℝ}
    (h₁ : ∀ x, HasDerivAt f (f₁ x) x) (h₂ : ∀ x, HasDerivAt f₁ (f₂ x) x) :
    iteratedDeriv 2 f = f₂ := by
  have hd : deriv f = f₁ := funext (fun x => (h₁ x).deriv)
  funext x
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, hd]
  exact (h₂ x).deriv

/-- Specified scalar first and second derivatives with global Lipschitz bounds control
both positive-order tensors of their bounded linear pullback. -/
theorem ContinuousLinearMap.lipschitzWith_twoJets_scalar_comp
    (K : E →L[ℝ] ℝ) {f f₁ f₂ : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (h₁ : ∀ x, HasDerivAt f (f₁ x) x) (h₂ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    {L₁ L₂ : ℝ≥0} (hL₁ : LipschitzWith L₁ f₁) (hL₂ : LipschitzWith L₂ f₂) :
    LipschitzWith (L₁ * ‖K‖₊ ^ 2) (iteratedFDeriv ℝ 1 (f ∘ K)) ∧
      LipschitzWith (L₂ * ‖K‖₊ ^ 3) (iteratedFDeriv ℝ 2 (f ∘ K)) := by
  have hd : iteratedDeriv 1 f = f₁ := by
    simpa only [iteratedDeriv_one] using funext (fun x => (h₁ x).deriv)
  have hdd := iteratedDeriv_two_eq_of_hasDerivAt h₁ h₂
  constructor
  · exact K.lipschitzWith_iteratedFDeriv_scalar_comp
      (hf.of_le (by norm_num)) (hd ▸ hL₁)
  · exact K.lipschitzWith_iteratedFDeriv_scalar_comp hf (hdd ▸ hL₂)

/-- The actual derivative of a scalar pullback applies its scalar slope to the linear
image of the direction. -/
theorem ContinuousLinearMap.fderiv_scalar_comp_apply
    (K : E →L[ℝ] ℝ) {f f₁ : ℝ → ℝ} (h₁ : ∀ x, HasDerivAt f (f₁ x) x)
    (x d : E) : fderiv ℝ (f ∘ K) x d = f₁ (K x) * K d := by
  have h := (h₁ (K x)).hasFDerivAt.comp x K.hasFDerivAt
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply,
    toSpanSingleton_apply,
    one_apply_eq_self, smul_eq_mul, mul_comm] using
      congrArg (fun A : E →L[ℝ] ℝ => A d) h.fderiv

/-- The actual bilinear second derivative of a scalar pullback multiplies the two
linear direction images by the scalar curvature. -/
theorem ContinuousLinearMap.secondFDeriv_scalar_comp_apply
    (K : E →L[ℝ] ℝ) {f f₁ f₂ : ℝ → ℝ}
    (h₁ : ∀ x, HasDerivAt f (f₁ x) x) (h₂ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (x a b : E) : fderiv ℝ (fderiv ℝ (f ∘ K)) x a b =
      f₂ (K x) * K a * K b := by
  have heq : fderiv ℝ (f ∘ K) = fun y => f₁ (K y) • K := by
    funext y
    ext d
    simp only [K.fderiv_scalar_comp_apply h₁, smul_apply, smul_eq_mul]
  rw [heq]
  have h := ((h₂ (K x)).hasFDerivAt.comp x K.hasFDerivAt).smul_const K
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply,
    toSpanSingleton_apply,
    one_apply_eq_self, smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      congrArg (fun A : E →L[ℝ] (E →L[ℝ] ℝ) => A a b) h.fderiv
