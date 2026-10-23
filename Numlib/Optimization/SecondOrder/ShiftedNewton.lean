import Numlib.Optimization.TrustRegion.SecondOrder.Finite
import Numlib.Analysis.Calculus.TaylorModel.SecondOrder

/-!
# Inexact shifted Newton steps

The residual equation and its two norm controls use the actual gradient and
Riesz Hessian. A multiplier proportional to the step gives a spectral bound
and a lower bound on the step in terms of the actual trial gradient.
-/

namespace ShiftedNewton
open SecondOrderTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual shifted Newton equation with relative and quadratic residual controls. -/
structure Step (f : E → ℝ) (x s r : E) (ℓ κg κs : ℝ) : Prop where
  relative_nonneg : 0 ≤ κg
  relative_lt_one : κg < 1
  quadratic_pos : 0 < κs
  multiplier_nonneg : 0 ≤ ℓ
  equation : hessian f x s + ℓ • s = -gradient f x + r
  residual_relative : ‖r‖ ≤ κg * ‖gradient f x‖
  residual_quadratic : ‖r‖ ≤ κs * ‖s‖ ^ 2

/-- Positive semidefiniteness of the actual shifted Hessian quadratic form. -/
def ShiftedPSD (f : E → ℝ) (x : E) (ℓ : ℝ) : Prop :=
  ∀ v : E, 0 ≤ inner ℝ (hessian f x v + ℓ • v) v

/-- The shifted Hessian is PSD precisely when its actual quadratic form is nonnegative. -/
theorem shiftedPSD_iff (f : E → ℝ) (x : E) (ℓ : ℝ) :
    ShiftedPSD f x ℓ ↔ ∀ v : E, 0 ≤ inner ℝ (hessian f x v + ℓ • v) v := Iff.rfl

/-- Accepted finite shifted-Newton traces. These are residual equations and
point updates, without a spectral bound or a convergence conclusion. -/
structure Trace (f : E → ℝ) (x s r : ℕ → E) (ℓ : ℕ → ℝ)
    (κg κs : ℝ) (N : ℕ) : Prop where
  relative_nonneg : 0 ≤ κg
  relative_lt_one : κg < 1
  quadratic_pos : 0 < κs
  step : ∀ i < N, Step f (x i) (s i) (r i) (ℓ i) κg κs
  point_update : ∀ i < N, x (i + 1) = x i + s i

/-- Accepted finite traces in the second-order method class, including its
spectral rule and genuine least-eigenvalue certificates. -/
structure MethodClass (f : E → ℝ) (x s r u : ℕ → E) (ℓ μ : ℕ → ℝ)
    (κg κs κℓ : ℝ) (N : ℕ) : Prop extends Trace f x s r ℓ κg κs N where
  spectral_factor : 1 < κℓ
  nonzero : ∀ i < N, s i ≠ 0
  shifted_psd : ∀ i < N, ShiftedPSD f (x i) (ℓ i)
  least_eigenpair : ∀ i < N, IsLeastEigenpair f (x i) (μ i) (u i)
  spectral_bound : ∀ i < N, μ i + ℓ i ≤
    κℓ * max |μ i| (Real.sqrt ‖gradient f (x i)‖)

/-- Riesz duality identifies the quadratic Taylor derivative with the gradient
plus the actual Hessian applied to the step. -/
theorem quadraticDerivative_eq (f : E → ℝ) (x s : E) :
    TaylorModel.quadraticDerivative f x s =
      (InnerProductSpace.toDual ℝ E) (gradient f x + hessian f x s) := by
  rw [map_add, toDual_gradient]
  unfold TaylorModel.quadraticDerivative
  congr 1
  exact ((InnerProductSpace.toDual ℝ E).apply_symm_apply _).symm

/-- A sharp Hessian Lipschitz bound controls the actual trial gradient by the
quadratic residual and the actual shift term. -/
theorem Step.trial_gradient_le {f : E → ℝ} {x s r : E} {ℓ κg κs L : ℝ}
    (h : Step f x s r ℓ κg κs) (hf : ContDiff ℝ 2 f)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) :
    ‖gradient f (x + s)‖ ≤ (L / 2 + κs) * ‖s‖ ^ 2 + ℓ * ‖s‖ := by
  have hid : gradient f x + hessian f x s = r - ℓ • s := by
    calc
      _ = (hessian f x s + ℓ • s) - ℓ • s + gradient f x := by abel
      _ = (-gradient f x + r) - ℓ • s + gradient f x := by rw [h.equation]
      _ = _ := by abel
  have hn : ‖gradient f (x + s)‖ = ‖fderiv ℝ f (x + s)‖ := by
    rw [← toDual_gradient, (InnerProductSpace.toDual ℝ E).norm_map]
  have hq : ‖TaylorModel.quadraticDerivative f x s‖ ≤ ‖r‖ + ℓ * ‖s‖ := by
    rw [quadraticDerivative_eq, (InnerProductSpace.toDual ℝ E).norm_map, hid]
    simpa only [norm_smul, Real.norm_of_nonneg h.multiplier_nonneg] using
      norm_sub_le r (ℓ • s)
  have hb := TaylorModel.norm_fderiv_sub_quadraticDerivative_le hf hlip x s
  have ht := norm_le_norm_sub_add (fderiv ℝ f (x + s))
    (TaylorModel.quadraticDerivative f x s)
  rw [hn]
  nlinarith [h.residual_quadratic]

/-- A multiplier proportional to the step gives the squared step estimate. -/
theorem Step.trial_gradient_le_sq {f : E → ℝ} {x s r : E} {ℓ κg κs L B : ℝ}
    (h : Step f x s r ℓ κg κs) (hf : ContDiff ℝ 2 f)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) (hℓ : ℓ ≤ B * ‖s‖) :
    ‖gradient f (x + s)‖ ≤ (L / 2 + κs + B) * ‖s‖ ^ 2 := by
  have hb := h.trial_gradient_le hf hlip
  nlinarith [mul_le_mul_of_nonneg_right hℓ (norm_nonneg s)]

/-- The printed reciprocal coefficient is valid when the bracket is at least one. -/
theorem sqrt_step_lower {G t A : ℝ} (hG : 0 ≤ G) (ht : 0 ≤ t)
    (hA : 1 ≤ A) (hbound : G ≤ A * t ^ 2) : A⁻¹ * Real.sqrt G ≤ t := by
  have hApos : 0 < A := by linarith
  have hs := Real.sq_sqrt hG
  have hAsq : A * t ^ 2 ≤ (A * t) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ A * (A - 1) by positivity) (sq_nonneg t)]
  have hsqrt : Real.sqrt G ≤ A * t := by
    nlinarith [Real.sqrt_nonneg G, mul_nonneg hApos.le ht]
  calc
    A⁻¹ * Real.sqrt G ≤ A⁻¹ * (A * t) :=
      mul_le_mul_of_nonneg_left hsqrt (inv_nonneg.mpr hApos.le)
    _ = t := by rw [← mul_assoc, inv_mul_cancel₀ hApos.ne', one_mul]

/-- A proportional multiplier gives the source's lower bound on the step. -/
theorem Step.step_lower {f : E → ℝ} {x s r : E} {ℓ κg κs L B : ℝ}
    (h : Step f x s r ℓ κg κs) (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hB : 1 < B)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) (hℓ : ℓ ≤ B * ‖s‖) :
    (L / 2 + κs + B)⁻¹ * Real.sqrt ‖gradient f (x + s)‖ ≤ ‖s‖ := by
  apply sqrt_step_lower (norm_nonneg _) (norm_nonneg _)
    (by linarith [h.quadratic_pos])
  exact h.trial_gradient_le_sq hf hlip hℓ

/-- A certified least eigenvalue bounds the actual Hessian quadratic form on
all vectors, including zero. -/
theorem least_rayleigh_lower {f : E → ℝ} {x u : E} {μ : ℝ}
    (h : IsLeastEigenpair f x μ u) (v : E) :
    μ * ‖v‖ ^ 2 ≤ inner ℝ (hessian f x v) v := by
  by_cases hv : v = 0
  · simp [hv]
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := by
    simp [w, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hvn.le), hvn.ne']
  have ht : iteratedFDeriv ℝ 2 f x (fun _ => w) =
      inner ℝ (hessian f x w) w := by
    have ht := TaylorModel.inner_hessianOperator f x w w
    have he : (![w, w] : Fin 2 → E) = (fun _ => w) := by
      ext i; fin_cases i <;> rfl
    simpa only [he, hessian_apply] using ht.symm
  have hh := h.least w hw
  rw [ht] at hh
  have hs : inner ℝ (hessian f x w) w = inner ℝ (hessian f x v) v / ‖v‖ ^ 2 := by
    simp only [w, map_smul, real_inner_smul_left, real_inner_smul_right]
    field_simp
  rw [hs] at hh
  exact (le_div_iff₀ (sq_pos_of_pos hvn)).mp hh

/-- Positive semidefiniteness controls the least shifted eigenvalue. -/
theorem least_shift_nonneg {f : E → ℝ} {x u : E} {μ ℓ : ℝ}
    (he : IsLeastEigenpair f x μ u) (hpsd : ShiftedPSD f x ℓ) : 0 ≤ μ + ℓ := by
  have hh := hpsd u
  rw [hessian_apply, he.eigenvector, inner_add_left, real_inner_smul_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq, he.unit] at hh
  simpa using hh

/-- The shifted residual equation controls step length times the least
shifted eigenvalue, without requiring an invertible Hessian. -/
theorem Step.shift_mul_norm_le {f : E → ℝ} {x s r u : E} {ℓ μ κg κs : ℝ}
    (h : Step f x s r ℓ κg κs) (hs : s ≠ 0)
    (he : IsLeastEigenpair f x μ u) :
    (μ + ℓ) * ‖s‖ ≤ (1 + κg) * ‖gradient f x‖ := by
  have hl := least_rayleigh_lower he s
  have hi : (μ + ℓ) * ‖s‖ ^ 2 ≤
      inner ℝ (hessian f x s + ℓ • s) s := by
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    nlinarith
  rw [h.equation] at hi
  have hb : inner ℝ (-gradient f x + r) s ≤
      ((1 + κg) * ‖gradient f x‖) * ‖s‖ := by
    calc
      _ ≤ ‖-gradient f x + r‖ * ‖s‖ := real_inner_le_norm _ _
      _ ≤ (‖gradient f x‖ + ‖r‖) * ‖s‖ := by
        gcongr
        simpa only [norm_neg] using norm_add_le (-gradient f x) r
      _ ≤ _ := by
        nlinarith [mul_le_mul_of_nonneg_right h.residual_relative (norm_nonneg s)]
  have hn : 0 < ‖s‖ := norm_pos_iff.mpr hs
  apply (mul_le_mul_iff_left₀ hn).mp
  nlinarith [hi.trans hb]

/-- A scalar quadratic inequality bounds the shifted least eigenvalue by
the larger of its unshifted magnitude and the square root of the gradient norm. -/
theorem spectral_bound_of_quadratic {μ ℓ G A : ℝ} (hG : 0 ≤ G) (hA : 1 ≤ A)
    (hbound : ℓ * (μ + ℓ) ≤ A * G) :
    μ + ℓ ≤ 2 * Real.sqrt A * max |μ| (Real.sqrt G) := by
  let S := Real.sqrt A
  let M := max |μ| (Real.sqrt G)
  have hS : 1 ≤ S := by simpa [S] using Real.one_le_sqrt.mpr hA
  have hM : 0 ≤ M := (abs_nonneg μ).trans (le_max_left _ _)
  have hμ : μ ≤ M := (le_abs_self μ).trans (le_max_left _ _)
  have hGsq : G ≤ M ^ 2 := by
    have hh : Real.sqrt G ≤ M := le_max_right _ _
    nlinarith [Real.sq_sqrt hG, Real.sqrt_nonneg G]
  have hSsq : S ^ 2 = A := Real.sq_sqrt (by linarith)
  have hSM : M ≤ S * M := by nlinarith
  by_contra hbad
  have hg : 2 * S * M < μ + ℓ := lt_of_not_ge hbad
  have hg' : S * M < μ + ℓ := by nlinarith
  have hℓ : S * M < ℓ := by nlinarith
  have hmpos : 0 ≤ S * M := by positivity
  have hprod : (S * M) * (S * M) < ℓ * (μ + ℓ) :=
    (mul_le_mul_of_nonneg_left hg'.le hmpos).trans_lt
      (mul_lt_mul_of_pos_right hℓ (hmpos.trans_lt hg'))
  have hAG : A * G ≤ (S * M) * (S * M) := by
    have hh := mul_le_mul_of_nonneg_left hGsq (show 0 ≤ A by linarith)
    nlinarith [hSsq]
  linarith

/-- A multiplier proportional to the step implies the method-class spectral
condition, with an accuracy-independent explicit coefficient. -/
theorem Step.spectral_bound {f : E → ℝ} {x s r u : E} {ℓ μ κg κs B : ℝ}
    (h : Step f x s r ℓ κg κs) (hs : s ≠ 0)
    (he : IsLeastEigenpair f x μ u) (hpsd : ShiftedPSD f x ℓ)
    (hB : 1 < B) (hℓ : ℓ ≤ B * ‖s‖) :
    1 < 2 * Real.sqrt (B * (1 + κg)) ∧
      μ + ℓ ≤ 2 * Real.sqrt (B * (1 + κg)) *
        max |μ| (Real.sqrt ‖gradient f x‖) := by
  have hA : 1 ≤ B * (1 + κg) := by nlinarith [h.relative_nonneg]
  have hgap := least_shift_nonneg he hpsd
  have hb := h.shift_mul_norm_le hs he
  have hquad : ℓ * (μ + ℓ) ≤ B * (1 + κg) * ‖gradient f x‖ := by
    have hmul := mul_le_mul_of_nonneg_right hℓ hgap
    have hmul' := mul_le_mul_of_nonneg_left hb (show 0 ≤ B by linarith)
    nlinarith
  constructor
  · have hh := Real.one_le_sqrt.mpr hA
    linarith
  · exact spectral_bound_of_quadratic (norm_nonneg _) hA hquad

/-- A proportional-shift trace with PSD shifted Hessians belongs to the
spectrally bounded second-order method class. -/
theorem Trace.to_methodClass {f : E → ℝ} {x s r u : ℕ → E}
    {ℓ μ : ℕ → ℝ} {κg κs B : ℝ} {N : ℕ}
    (h : Trace f x s r ℓ κg κs N) (hB : 1 < B)
    (hs : ∀ i < N, s i ≠ 0)
    (he : ∀ i < N, IsLeastEigenpair f (x i) (μ i) (u i))
    (hpsd : ∀ i < N, ShiftedPSD f (x i) (ℓ i))
    (hℓ : ∀ i < N, ℓ i ≤ B * ‖s i‖) :
    MethodClass f x s r u ℓ μ κg κs (2 * Real.sqrt (B * (1 + κg))) N where
  toTrace := h
  spectral_factor := by
    have hA : 1 ≤ B * (1 + κg) := by nlinarith [h.relative_nonneg]
    have hh := Real.one_le_sqrt.mpr hA
    linarith
  nonzero := hs
  shifted_psd := hpsd
  least_eigenpair := he
  spectral_bound := fun i hi =>
    ((h.step i hi).spectral_bound (hs i hi) (he i hi) (hpsd i hi) hB (hℓ i hi)).2

/-- The accepted trace update transfers the trial-gradient step bound to the
actual next iterate. -/
theorem Trace.step_lower {f : E → ℝ} {x s r : ℕ → E} {ℓ : ℕ → ℝ}
    {κg κs L B : ℝ} {N : ℕ} (h : Trace f x s r ℓ κg κs N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L) (hB : 1 < B)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) (hℓ : ∀ i < N, ℓ i ≤ B * ‖s i‖) :
    ∀ i < N, (L / 2 + κs + B)⁻¹ * Real.sqrt ‖gradient f (x (i + 1))‖ ≤ ‖s i‖ := by
  intro i hi
  rw [h.point_update i hi]
  exact (h.step i hi).step_lower hf hL hB hlip (hℓ i hi)

end ShiftedNewton
