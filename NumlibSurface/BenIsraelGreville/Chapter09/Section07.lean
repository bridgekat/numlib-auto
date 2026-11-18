/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter09.Section03
import Numlib.Analysis.Normed.Algebra.SpectralRadius
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Series and integral representations of generalized inverses

Section 9.7 of [benIsrael2003generalized] studies approximation of an
operator's maximal inverse by an integral and by a Neumann series.
The finite sums start with exponent zero. Their residuals therefore use
exponent `N + 1` when the sum ends at exponent `N`.
The objective derivative in Equation (86) is nonpositive, with equality
at stationary points.

The spectral-radius test in Exercise 49 uses the complex spectrum.
The splitting formulas in Exercise 50 preserve the common kernel's
orthogonal complement. For convergence to the Moore–Penrose solution,
the preconditioner must also annihilate that solution's residual.
-/

noncomputable section

namespace BenIsraelGreville.Chapter09

open Filter MeasureTheory Topology
open scoped InnerProductSpace

section ContinuousApproximation

open ContinuousLinearMap Filter MeasureTheory Set Topology
open scoped InnerProductSpace Nat

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

local instance : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal 𝕜 E
local instance : InnerProductSpace ℝ F := InnerProductSpace.rclikeToReal 𝕜 F
local instance : NormedAlgebra ℝ (E →L[𝕜] E) :=
  NormedAlgebra.restrictScalars ℝ 𝕜 (E →L[𝕜] E)
local instance : IsScalarTower ℝ 𝕜 E := IsScalarTower.restrictScalars ℝ 𝕜 E
local instance : IsScalarTower ℝ 𝕜 F := IsScalarTower.restrictScalars ℝ 𝕜 F
local instance : IsScalarTower ℝ 𝕜 (E →L[𝕜] E) :=
  IsScalarTower.restrictScalars ℝ 𝕜 (E →L[𝕜] E)
local instance : NormedSpace ℝ (E →L[𝕜] F) := NormedSpace.restrictScalars ℝ 𝕜 _

/-- **Equations (83)–(85)** of [benIsrael2003generalized], Chapter 9.
The least-squares gradient flow starts at zero and moves against the
normal-equation residual. -/
def leastSquaresGradientFlow (A : E →L[𝕜] F) (y : F) (x : ℝ → E) : Prop :=
  x 0 = 0 ∧ ∀ t : ℝ, 0 ≤ t → HasDerivAt x (-(A.adjoint (A (x t) - y))) t

/-- **Equations (83)–(84)** of [benIsrael2003generalized], Chapter 9.
The derivative of the squared least-squares residual pairs the
normal-equation residual with the velocity. -/
theorem leastSquaresResidual_hasDerivAt (A : E →L[𝕜] F) (y : F) {x : ℝ → E}
    {v : E} {t : ℝ} (hx : HasDerivAt x v t) :
    HasDerivAt (fun s => ‖A (x s) - y‖ ^ 2)
      (2 * RCLike.re (inner 𝕜 (A.adjoint (A (x t) - y)) v)) t := by
  have h := (((A.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hx).sub_const y).norm_sq
  simpa only [Function.comp_apply, coe_restrictScalars', real_inner_eq_re_inner,
    A.adjoint_inner_left] using h

/-- **Equation (86)** of [benIsrael2003generalized], Chapter 9.
The squared residual along the flow has derivative minus twice the squared
norm of the normal-equation residual. -/
theorem leastSquaresGradientFlow_hasDerivAt (A : E →L[𝕜] F) (y : F) (x : ℝ → E)
    (hx : leastSquaresGradientFlow A y x) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => ‖A (x s) - y‖ ^ 2) (-2 * ‖A.adjoint (A (x t) - y)‖ ^ 2) t := by
  simpa only [inner_neg_right, map_neg, inner_self_eq_norm_sq, mul_neg, neg_mul] using
    leastSquaresResidual_hasDerivAt A y (hx.2 t ht)

/-- The derivative in Equation (86) is strictly negative exactly where the
normal-equation residual is nonzero. -/
theorem leastSquaresGradientFlow_deriv_neg_iff (A : E →L[𝕜] F) (y : F) (x : ℝ → E)
    (hx : leastSquaresGradientFlow A y x) {t : ℝ} (ht : 0 ≤ t) :
    deriv (fun s => ‖A (x s) - y‖ ^ 2) t < 0 ↔ A.adjoint (A (x t) - y) ≠ 0 := by
  rw [(leastSquaresGradientFlow_hasDerivAt A y x hx ht).deriv]
  constructor
  · intro h he
    simp [he] at h
  · intro he
    exact mul_neg_of_neg_of_pos (by norm_num) (sq_pos_of_pos (norm_pos_iff.mpr he))

/-- Along the gradient flow the least-squares objective is nonincreasing. -/
theorem leastSquaresGradientFlow_antitoneOn (A : E →L[𝕜] F) (y : F) (x : ℝ → E)
    (hx : leastSquaresGradientFlow A y x) :
    AntitoneOn (fun t => ‖A (x t) - y‖ ^ 2) (Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · intro t ht
    exact (leastSquaresGradientFlow_hasDerivAt A y x hx ht).continuousAt.continuousWithinAt
  · intro t ht
    have h := leastSquaresGradientFlow_hasDerivAt A y x hx (interior_subset ht)
    exact h.differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(leastSquaresGradientFlow_hasDerivAt A y x hx (interior_subset ht)).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg _)

/-- Exponential decay operator with bounded generator `-D`. -/
def gradientSemigroup (D : E →L[𝕜] E) (t : ℝ) : E →L[𝕜] E :=
  NormedSpace.exp (t • (-D))

omit [CompleteSpace E] in
/-- At time zero the semigroup is the identity. -/
@[simp] theorem gradientSemigroup_zero (D : E →L[𝕜] E) : gradientSemigroup D 0 = 1 := by
  simp [gradientSemigroup]

private theorem gradientSemigroup_hasDerivAt_left (D : E →L[𝕜] E) (t : ℝ) :
    HasDerivAt (gradientSemigroup D) (-(D * gradientSemigroup D t)) t := by
  unfold gradientSemigroup
  simpa only [neg_mul] using
    (hasDerivAt_exp_smul_const' (-D) t)

private theorem gradientSemigroup_hasDerivAt_right (D : E →L[𝕜] E) (t : ℝ) :
    HasDerivAt (gradientSemigroup D) (-(gradientSemigroup D t * D)) t := by
  unfold gradientSemigroup
  simpa only [mul_neg] using
    (hasDerivAt_exp_smul_const (-D) t)

private theorem continuous_gradientSemigroup (D : E →L[𝕜] E) :
    Continuous (gradientSemigroup D) :=
  continuous_iff_continuousAt.mpr fun t => (gradientSemigroup_hasDerivAt_left D t).continuousAt

private theorem gradientSemigroup_intertwine {D : E →L[𝕜] E} {C : F →L[𝕜] F}
    (T : E →L[𝕜] F) (h : T.comp D = C.comp T) (t : ℝ) :
    T.comp (gradientSemigroup D t) = (gradientSemigroup C t).comp T := by
  let U := t • (-D)
  let V := t • (-C)
  have huv : T.comp U = V.comp T := by
    apply ContinuousLinearMap.ext
    intro x
    change T (t • (-D x)) = t • (-(C (T x)))
    have hx := DFunLike.congr_fun h x
    change T (D x) = C (T x) at hx
    rw [ContinuousLinearMap.map_smul_of_tower, map_neg, hx]
  have hp (n : ℕ) : T.comp (U ^ n) = (V ^ n).comp T := by
    induction n with
    | zero =>
      ext x
      simp only [pow_zero, ContinuousLinearMap.comp_apply, one_apply_eq_self]
    | succ n ih =>
      rw [pow_succ', pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def,
        ← ContinuousLinearMap.comp_assoc, huv, ContinuousLinearMap.comp_assoc, ih,
        ← ContinuousLinearMap.comp_assoc]
  let L := ContinuousLinearMap.compL 𝕜 E E F T
  let R := (ContinuousLinearMap.compL 𝕜 E F F).flip T
  have hL := L.hasSum (NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕜) U)
  have hR := R.hasSum (NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕜) V)
  have hh (n : ℕ) : L ((n !⁻¹ : 𝕜) • U ^ n) = R ((n !⁻¹ : 𝕜) • V ^ n) := by
    simp only [map_smul, L, R, ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply, hp]
  have hL' : HasSum (fun n : ℕ => R ((n !⁻¹ : 𝕜) • V ^ n)) (L (NormedSpace.exp U)) := by
    simpa only [hh] using hL
  exact hL'.unique hR

/-- **Equation (94)** of [benIsrael2003generalized], Chapter 9.
The integrated semigroup uses the time variable `s`. The substitution
`s ↦ t - s` recovers the source's formula. -/
def gradientSemigroupIntegral (D : E →L[𝕜] E) (t : ℝ) : E →L[𝕜] E :=
  ∫ s in (0 : ℝ)..t, gradientSemigroup D s

omit [CompleteSpace E] in
/-- The translated integration variable gives the kernel in Equation (94). -/
theorem gradientSemigroupIntegral_eq_translated (D : E →L[𝕜] E) (t : ℝ) :
    gradientSemigroupIntegral D t = ∫ s in (0 : ℝ)..t, gradientSemigroup D (t - s) := by
  rw [gradientSemigroupIntegral, intervalIntegral.integral_comp_sub_left, sub_self, sub_zero]

private theorem gradientSemigroupIntegral_intertwine {D : E →L[𝕜] E} {C : F →L[𝕜] F}
    (T : E →L[𝕜] F) (h : T.comp D = C.comp T) (t : ℝ) :
    T.comp (gradientSemigroupIntegral D t) = (gradientSemigroupIntegral C t).comp T := by
  let L := ContinuousLinearMap.compL 𝕜 E E F T
  let R := (ContinuousLinearMap.compL 𝕜 E F F).flip T
  change L (∫ s in (0 : ℝ)..t, gradientSemigroup D s) =
    R (∫ s in (0 : ℝ)..t, gradientSemigroup C s)
  rw [← L.intervalIntegral_comp_comm ((continuous_gradientSemigroup D).intervalIntegrable ..),
    ← R.intervalIntegral_comp_comm ((continuous_gradientSemigroup C).intervalIntegrable ..)]
  apply intervalIntegral.integral_congr
  exact fun s _ => gradientSemigroup_intertwine T h s

private theorem gradientSemigroupIntegral_mul (D : E →L[𝕜] E) (t : ℝ) :
    gradientSemigroupIntegral D t * D = 1 - gradientSemigroup D t := by
  let R := (ContinuousLinearMap.compL 𝕜 E E E).flip D
  change R (∫ s in (0 : ℝ)..t, gradientSemigroup D s) = _
  rw [← R.intervalIntegral_comp_comm ((continuous_gradientSemigroup D).intervalIntegrable ..)]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := t) (fun s _ => gradientSemigroup_hasDerivAt_right D s)
    ((continuous_gradientSemigroup D).mul continuous_const |>.neg.intervalIntegrable ..)
  rw [intervalIntegral.integral_neg, gradientSemigroup_zero] at h
  exact neg_eq_iff_eq_neg.mp h |>.trans (neg_sub _ _)

private theorem mul_gradientSemigroupIntegral (D : E →L[𝕜] E) (t : ℝ) :
    D * gradientSemigroupIntegral D t = 1 - gradientSemigroup D t := by
  have h := gradientSemigroupIntegral_intertwine D rfl t
  exact h.trans (gradientSemigroupIntegral_mul D t)

/-- **Equations (87) and (94)** of [benIsrael2003generalized], Chapter 9.
The approximation is the time integral of the left normal-equation
semigroup followed by the adjoint. -/
def pinvSemigroupApproximation (A : E →L[𝕜] F) (t : ℝ) : F →L[𝕜] E :=
  (gradientSemigroupIntegral (A.adjoint.comp A) t).comp A.adjoint

/-- The left and right semigroup integrals give the same approximation. -/
theorem pinvSemigroupApproximation_eq_right (A : E →L[𝕜] F) (t : ℝ) :
    pinvSemigroupApproximation A t =
      A.adjoint.comp (gradientSemigroupIntegral (A.comp A.adjoint) t) :=
  (gradientSemigroupIntegral_intertwine A.adjoint
    (ContinuousLinearMap.comp_assoc _ _ _).symm t).symm

/-- **Equation (88)** of [benIsrael2003generalized], Chapter 9.
The approximation is the integral of the composition of the delayed
semigroup with the adjoint. -/
theorem pinvSemigroupApproximation_eq_integral (A : E →L[𝕜] F) (t : ℝ) :
    pinvSemigroupApproximation A t =
      ∫ s in (0 : ℝ)..t, (gradientSemigroup (A.adjoint.comp A) (t - s)).comp A.adjoint := by
  let L := (ContinuousLinearMap.compL 𝕜 F E E).flip A.adjoint
  let _ : NormedSpace ℝ (F →L[𝕜] E) := NormedSpace.restrictScalars ℝ 𝕜 _
  change L (gradientSemigroupIntegral (A.adjoint.comp A) t) = _
  rw [gradientSemigroupIntegral_eq_translated]
  have h : IntervalIntegrable (fun s : ℝ => gradientSemigroup (A.adjoint.comp A) (t - s))
      volume 0 t :=
    ((continuous_gradientSemigroup (A.adjoint.comp A)).comp
      (continuous_const.sub continuous_id)).intervalIntegrable _ _
  exact (L.intervalIntegral_comp_comm h).symm

/-- **Equation (87)** of [benIsrael2003generalized], Chapter 9.
The operator integral evaluates to the vector-valued solution formula. -/
theorem pinvSemigroupApproximation_apply_integral (A : E →L[𝕜] F) (y : F) (t : ℝ) :
    pinvSemigroupApproximation A t y =
      ∫ s in (0 : ℝ)..t, gradientSemigroup (A.adjoint.comp A) (t - s) (A.adjoint y) := by
  let L := ContinuousLinearMap.apply 𝕜 E (A.adjoint y)
  change L (gradientSemigroupIntegral (A.adjoint.comp A) t) = _
  rw [gradientSemigroupIntegral_eq_translated]
  have h : IntervalIntegrable (fun s : ℝ => gradientSemigroup (A.adjoint.comp A) (t - s))
      volume 0 t :=
    ((continuous_gradientSemigroup (A.adjoint.comp A)).comp
      (continuous_const.sub continuous_id)).intervalIntegrable _ _
  exact (L.intervalIntegral_comp_comm h).symm

/-- The flow residual after applying the approximation on the range of
the original operator is the left exponential. -/
theorem pinvSemigroupApproximation_comp (A : E →L[𝕜] F) (t : ℝ) :
    (pinvSemigroupApproximation A t).comp A =
      1 - gradientSemigroup (A.adjoint.comp A) t :=
  (ContinuousLinearMap.comp_assoc _ _ _).trans (gradientSemigroupIntegral_mul _ _)

/-- The range residual after applying the original operator to the
approximation is the right exponential. -/
theorem comp_pinvSemigroupApproximation (A : E →L[𝕜] F) (t : ℝ) :
    A.comp (pinvSemigroupApproximation A t) =
      1 - gradientSemigroup (A.comp A.adjoint) t := by
  rw [pinvSemigroupApproximation_eq_right, ← ContinuousLinearMap.comp_assoc]
  exact mul_gradientSemigroupIntegral _ _

/-- **Equations (85) and (87)** of [benIsrael2003generalized], Chapter 9.
The operator integral solves the least-squares flow with zero initial value. -/
theorem leastSquaresGradientFlow_pinvSemigroupApproximation (A : E →L[𝕜] F) (y : F) :
    leastSquaresGradientFlow A y (fun t => pinvSemigroupApproximation A t y) := by
  constructor
  · simp [pinvSemigroupApproximation, gradientSemigroupIntegral]
  · intro t _
    let D := A.adjoint.comp A
    have hcont := continuous_gradientSemigroup D
    have h := intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable 0 t)
      hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
    let L := (ContinuousLinearMap.apply 𝕜 E (A.adjoint y)).restrictScalars ℝ
    have he : -(A.adjoint (A (pinvSemigroupApproximation A t y) - y)) =
        gradientSemigroup D t (A.adjoint y) := by
      have hD := mul_gradientSemigroupIntegral D t
      have q := DFunLike.congr_fun hD (A.adjoint y)
      change D (gradientSemigroupIntegral D t (A.adjoint y)) =
        A.adjoint y - gradientSemigroup D t (A.adjoint y) at q
      rw [map_sub, neg_sub]
      change A.adjoint y - D (gradientSemigroupIntegral D t (A.adjoint y)) = _
      rw [q, sub_sub_cancel]
    rw [he]
    exact L.hasFDerivAt.comp_hasDerivAt t h

private theorem gradientSemigroup_apply_hasDerivAt (D : E →L[𝕜] E) (x : E) (t : ℝ) :
    HasDerivAt (fun s => gradientSemigroup D s x) (-(D (gradientSemigroup D t x))) t := by
  let L := (ContinuousLinearMap.apply 𝕜 E x).restrictScalars ℝ
  exact L.hasFDerivAt.comp_hasDerivAt t (gradientSemigroup_hasDerivAt_left D t)

private theorem normalSolution_norm_sq_hasDerivAt (A : E →L[𝕜] F) {x : ℝ → E} {t : ℝ}
    (hx : HasDerivAt x (-(A.adjoint (A (x t)))) t) :
    HasDerivAt (fun s => ‖x s‖ ^ 2) (-2 * ‖A (x t)‖ ^ 2) t := by
  have h := hx.norm_sq
  rw [real_inner_eq_re_inner, inner_neg_right, ← A.adjoint.adjoint_inner_left,
    ContinuousLinearMap.adjoint_adjoint, map_neg, inner_self_eq_norm_sq] at h
  simpa only [mul_neg, neg_mul] using h

private theorem normalSolution_norm_sq_antitoneOn (A : E →L[𝕜] F) {x : ℝ → E}
    (hx : ∀ t : ℝ, 0 ≤ t → HasDerivAt x (-(A.adjoint (A (x t)))) t) :
    AntitoneOn (fun t => ‖x t‖ ^ 2) (Ici 0) := by
  have h t (ht : 0 ≤ t) := normalSolution_norm_sq_hasDerivAt A (hx t ht)
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · exact fun t ht => (h t ht).continuousAt.continuousWithinAt
  · exact fun t ht => (h t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(h t (interior_subset ht)).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg _)

private theorem normalSemigroup_norm_sq_hasDerivAt (A : E →L[𝕜] F) (x : E) (t : ℝ) :
    HasDerivAt (fun s => ‖gradientSemigroup (A.adjoint.comp A) s x‖ ^ 2)
      (-2 * ‖A (gradientSemigroup (A.adjoint.comp A) t x)‖ ^ 2) t :=
  normalSolution_norm_sq_hasDerivAt A (gradientSemigroup_apply_hasDerivAt (A.adjoint.comp A) x t)

/-- The squared norm of the normal-equation semigroup is nonincreasing. -/
theorem normalSemigroup_norm_sq_antitoneOn (A : E →L[𝕜] F) (x : E) :
    AntitoneOn (fun t => ‖gradientSemigroup (A.adjoint.comp A) t x‖ ^ 2) (Ici 0) :=
  normalSolution_norm_sq_antitoneOn A
    (fun t _ => gradientSemigroup_apply_hasDerivAt (A.adjoint.comp A) x t)

/-- **Equation (87)** of [benIsrael2003generalized], Chapter 9.
The integral solution is unique for nonnegative time. -/
theorem leastSquaresGradientFlow_eqOn_pinvSemigroupApproximation (A : E →L[𝕜] F) (y : F)
    {x : ℝ → E} (hx : leastSquaresGradientFlow A y x) :
    EqOn x (fun t => pinvSemigroupApproximation A t y) (Ici 0) := by
  let w (t : ℝ) := pinvSemigroupApproximation A t y
  let d (t : ℝ) := x t - w t
  have hw := leastSquaresGradientFlow_pinvSemigroupApproximation A y
  have hd (t : ℝ) (ht : 0 ≤ t) : HasDerivAt d (-(A.adjoint (A (d t)))) t := by
    have h := (hx.2 t ht).sub (hw.2 t ht)
    convert h using 1
    simp only [d, w, map_sub]
    abel
  have hd0 : d 0 = 0 := sub_eq_zero.mpr (hx.1.trans hw.1.symm)
  intro t ht
  have h := normalSolution_norm_sq_antitoneOn A hd (le_refl (0 : ℝ)) ht ht
  have hzero : d t = 0 := by
    have hn : ‖d t‖ ^ 2 = 0 := le_antisymm (by simpa [hd0] using h) (sq_nonneg _)
    by_contra hne
    exact (sq_pos_of_pos (norm_pos_iff.mpr hne)).ne' hn
  exact sub_eq_zero.mp hzero

/-- The normal-equation semigroup is contractive at nonnegative times. -/
theorem normalSemigroup_norm_le (A : E →L[𝕜] F) (x : E) {t : ℝ} (ht : 0 ≤ t) :
    ‖gradientSemigroup (A.adjoint.comp A) t x‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa only [gradientSemigroup_zero, one_apply_eq_self] using
    normalSemigroup_norm_sq_antitoneOn A x (le_refl (0 : ℝ)) ht ht

private theorem riccati_rational_bound (f : ℝ → ℝ) (hcont : Continuous f)
    (hderiv : Differentiable ℝ f) (hnonneg : ∀ t, 0 ≤ f t)
    (hanti : AntitoneOn f (Ici 0)) {c t : ℝ} (hc : 0 < c) (ht : 0 ≤ t)
    (hd : ∀ s : ℝ, 0 ≤ s → deriv f s ≤ -2 * (f s) ^ 2 / c) :
    f t ≤ f 0 * c / (c + 2 * f 0 * t) := by
  have h0nonneg := hnonneg 0
  have hden : 0 < c + 2 * f 0 * t := by positivity
  by_cases hzero : f t = 0
  · rw [hzero]
    positivity
  have hf (s : ℝ) (hs : s ∈ Icc 0 t) : 0 < f s :=
    (lt_of_le_of_ne (hnonneg t) (Ne.symm hzero)).trans_le (hanti hs.1 ht hs.2)
  let g (s : ℝ) := (f s)⁻¹ - 2 * s / c
  have hg : MonotoneOn g (Icc 0 t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 t)
    · exact (hcont.continuousOn.inv₀ (fun s hs => (hf s hs).ne')).sub
        ((continuous_const.mul continuous_id).div_const _).continuousOn
    · intro s hs
      exact ((((hderiv s).hasDerivAt.inv (hf s (interior_subset hs)).ne').sub
        ((hasDerivAt_id s).const_mul 2 |>.div_const c)).differentiableAt).differentiableWithinAt
    · intro s hs
      have hs' := interior_subset hs
      have hspos := hf s hs'
      have h : HasDerivAt g (-deriv f s / f s ^ 2 - (2 * 1) / c) s :=
        ((hderiv s).hasDerivAt.inv hspos.ne').sub ((hasDerivAt_id s).const_mul 2 |>.div_const c)
      have hg' : deriv g s = -deriv f s / f s ^ 2 - 2 / c := by
        simpa only [mul_one] using h.deriv
      rw [hg']
      apply sub_nonneg.mpr
      apply (le_div_iff₀ (sq_pos_of_pos hspos)).mpr
      calc
        2 / c * f s ^ 2 = -(-2 * f s ^ 2 / c) := by ring
        _ ≤ -deriv f s := neg_le_neg (hd s hs'.1)
  have h0 := hf 0 ⟨le_rfl, ht⟩
  have hT := hf t ⟨ht, le_rfl⟩
  have h := hg ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
  dsimp only [g] at h
  rw [mul_zero, zero_div, sub_zero] at h
  apply (le_div_iff₀ hden).mpr
  have h' := (le_sub_iff_add_le.mp h)
  have hm := mul_le_mul_of_nonneg_right h' (show 0 ≤ f 0 * f t * c by positivity)
  calc
    f t * (c + 2 * f 0 * t) = ((f 0)⁻¹ + 2 * t / c) * (f 0 * f t * c) := by
      field_simp
    _ ≤ (f t)⁻¹ * (f 0 * f t * c) := hm
    _ = f 0 * c := by field_simp

set_option maxHeartbeats 1000000 in
-- The differential estimate expands norms for both the semigroup and its adjoint image.
/-- Rational decay of the normal-equation semigroup on the range of the adjoint. -/
theorem normalSemigroup_norm_sq_le_rational (A : E →L[𝕜] F) (z : F) {t : ℝ} (ht : 0 ≤ t) :
    ‖gradientSemigroup (A.adjoint.comp A) t (A.adjoint z)‖ ^ 2 ≤
      ‖A.adjoint z‖ ^ 2 * ‖z‖ ^ 2 / (‖z‖ ^ 2 + 2 * ‖A.adjoint z‖ ^ 2 * t) := by
  by_cases hz : z = 0
  · simp [hz]
  let x := A.adjoint z
  let f (s : ℝ) := ‖gradientSemigroup (A.adjoint.comp A) s x‖ ^ 2
  have hf (s) := normalSemigroup_norm_sq_hasDerivAt A x s
  have hnorm : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hr (s : ℝ) (hs : 0 ≤ s) : deriv f s ≤ -2 * f s ^ 2 / ‖z‖ ^ 2 := by
    let u := gradientSemigroup (A.adjoint.comp A) s x
    let v := gradientSemigroup (A.comp A.adjoint) s z
    have huv : u = A.adjoint v := by
      have h : A.adjoint.comp (A.comp A.adjoint) =
          (A.adjoint.comp A).comp A.adjoint :=
        (ContinuousLinearMap.comp_assoc A.adjoint A A.adjoint).symm
      have h' := DFunLike.congr_fun (gradientSemigroup_intertwine A.adjoint h s) z
      change A.adjoint v = u at h'
      exact h'.symm
    have hzv : ‖v‖ ≤ ‖z‖ := by
      simpa only [ContinuousLinearMap.adjoint_adjoint] using normalSemigroup_norm_le A.adjoint z hs
    have hu : f s ≤ ‖A u‖ * ‖z‖ := by
      calc
        f s = RCLike.re (inner 𝕜 u u) := norm_sq_eq_re_inner (𝕜 := 𝕜) u
        _ = RCLike.re (inner 𝕜 (A u) v) := by
          rw [congrArg (fun w : E => inner 𝕜 u w) huv, A.adjoint_inner_right]
        _ ≤ ‖A u‖ * ‖v‖ := re_inner_le_norm _ _
        _ ≤ ‖A u‖ * ‖z‖ := mul_le_mul_of_nonneg_left hzv (norm_nonneg _)
    have hsq : f s ^ 2 ≤ ‖A u‖ ^ 2 * ‖z‖ ^ 2 := by
      rw [← mul_pow]
      exact (sq_le_sq₀ (sq_nonneg _) (by positivity)).mpr hu
    rw [(hf s).deriv]
    apply (le_div_iff₀ hnorm).mpr
    change -2 * ‖A u‖ ^ 2 * ‖z‖ ^ 2 ≤ -2 * f s ^ 2
    linarith only [hsq]
  have hb := riccati_rational_bound f (continuous_iff_continuousAt.mpr fun s => (hf s).continuousAt)
    (fun s => (hf s).differentiableAt) (fun s => sq_nonneg _)
    (normalSemigroup_norm_sq_antitoneOn A x) hnorm ht hr
  simpa only [f, gradientSemigroup_zero, one_apply_eq_self, x] using hb

/-- The normal-equation semigroup converges strongly to zero on the closure
of the adjoint range. -/
theorem normalSemigroup_tendsto_zero (A : E →L[𝕜] F) (x : E)
    (hx : x ∈ A.adjoint.range.topologicalClosure) :
    Tendsto (fun t : ℝ => gradientSemigroup (A.adjoint.comp A) t x) atTop (𝓝 0) := by
  let S := gradientSemigroup (A.adjoint.comp A)
  have hr (z : F) : Tendsto (fun t : ℝ => S t (A.adjoint z)) atTop (𝓝 0) := by
    by_cases hz : A.adjoint z = 0
    · simp only [hz, map_zero, tendsto_const_nhds]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hh : Tendsto (fun t : ℝ => ‖z‖ ^ 2 + 2 * ‖A.adjoint z‖ ^ 2 * t) atTop atTop := by
      exact tendsto_atTop_add_const_left _ _
        (tendsto_id.const_mul_atTop (mul_pos (by norm_num) (sq_pos_of_pos (norm_pos_iff.mpr hz))))
    have hzero : Tendsto
        (fun t : ℝ => ‖A.adjoint z‖ ^ 2 * ‖z‖ ^ 2 / (‖z‖ ^ 2 + 2 * ‖A.adjoint z‖ ^ 2 * t))
        atTop (𝓝 0) := tendsto_const_nhds.div_atTop hh
    have hs := squeeze_zero' (Eventually.of_forall (fun (t : ℝ) => sq_nonneg ‖S t (A.adjoint z)‖))
      ((eventually_ge_atTop (0 : ℝ)).mono (fun _ ht => normalSemigroup_norm_sq_le_rational A z ht))
      hzero
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hs
    change Tendsto (fun t : ℝ => Real.sqrt (‖S t (A.adjoint z)‖ ^ 2))
      atTop (𝓝 (Real.sqrt 0)) at h
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨_, ⟨z, rfl⟩, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 2) (by positivity)
  obtain ⟨T, hT⟩ := Metric.tendsto_atTop.mp (hr z) (ε / 2) (by positivity)
  refine ⟨max T 0, fun t ht => ?_⟩
  have hle := normalSemigroup_norm_le A (x - A.adjoint z) ((le_max_right _ _).trans ht)
  have hb := hT t ((le_max_left _ _).trans ht)
  rw [dist_zero_right] at hb ⊢
  rw [dist_eq_norm] at hxy
  change ‖S t x‖ < ε
  calc
    ‖S t x‖ = ‖S t (x - A.adjoint z) + S t (A.adjoint z)‖ := by
      rw [map_sub, sub_add_cancel]
    _ ≤ ‖S t (x - A.adjoint z)‖ + ‖S t (A.adjoint z)‖ := norm_add_le _ _
    _ ≤ ‖x - A.adjoint z‖ + ‖S t (A.adjoint z)‖ := add_le_add hle le_rfl
    _ < ε := by
      change ‖x - A.adjoint z‖ < ε / 2 at hxy
      linarith only [hxy, hb]

/-- For every solution of the normal equations the approximation error
is the left exponential applied to that solution. -/
theorem pinvSemigroupApproximation_error (A : E →L[𝕜] F) (t : ℝ)
    {x : E} {y : F} (h : A.adjoint (A x) = A.adjoint y) :
    x - pinvSemigroupApproximation A t y = gradientSemigroup (A.adjoint.comp A) t x := by
  have he : pinvSemigroupApproximation A t y = pinvSemigroupApproximation A t (A x) := by
    simp only [pinvSemigroupApproximation, ContinuousLinearMap.comp_apply, h]
  rw [he, ← ContinuousLinearMap.comp_apply, pinvSemigroupApproximation_comp, sub_apply,
    one_apply_eq_self, sub_sub_cancel]

/-- The unprojected fitted-value residual is the right exponential. -/
theorem pinvSemigroupApproximation_range_error (A : E →L[𝕜] F) (t : ℝ) (y : F) :
    y - A (pinvSemigroupApproximation A t y) = gradientSemigroup (A.comp A.adjoint) t y := by
  rw [← ContinuousLinearMap.comp_apply, comp_pinvSemigroupApproximation,
    sub_apply, one_apply_eq_self, sub_sub_cancel]

/-- For any datum the projected residual starts from the projection onto
the closure of the range. -/
theorem pinvSemigroupApproximation_projected_error (A : E →L[𝕜] F) (t : ℝ) (y : F) :
    let p := A.range.topologicalClosure.starProjection y
    p - A (pinvSemigroupApproximation A t y) = gradientSemigroup (A.comp A.adjoint) t p := by
  intro p
  have hres : y - p ∈ A.rangeᗮ := by
    rw [← A.range.orthogonal_closure]
    exact A.range.topologicalClosure.sub_starProjection_mem_orthogonal y
  rw [A.orthogonal_range] at hres
  have he : A.adjoint y = A.adjoint p := by
    change A.adjoint (y - p) = 0 at hres
    rwa [map_sub, sub_eq_zero] at hres
  have hp : pinvSemigroupApproximation A t y = pinvSemigroupApproximation A t p := by
    simp only [pinvSemigroupApproximation, ContinuousLinearMap.comp_apply, he]
  rw [hp, pinvSemigroupApproximation_range_error]

/-- **Theorem 9(d)** of [benIsrael2003generalized], for arbitrary data.
The fitted values converge strongly
to the orthogonal projection onto the closure of the range. -/
theorem comp_pinvSemigroupApproximation_tendsto (A : E →L[𝕜] F) (y : F) :
    Tendsto (fun t : ℝ => A (pinvSemigroupApproximation A t y)) atTop
      (𝓝 (A.range.topologicalClosure.starProjection y)) := by
  let p := A.range.topologicalClosure.starProjection y
  have hp : p ∈ A.adjoint.adjoint.range.topologicalClosure := by
    rw [ContinuousLinearMap.adjoint_adjoint]
    exact A.range.topologicalClosure.starProjection_apply_mem y
  have h := normalSemigroup_tendsto_zero A.adjoint p hp
  have he := (tendsto_const_nhds (x := p)).sub h
  have hErr (t : ℝ) : p - A (pinvSemigroupApproximation A t y) =
      gradientSemigroup (A.comp A.adjoint) t p := pinvSemigroupApproximation_projected_error A t y
  simpa only [ContinuousLinearMap.adjoint_adjoint, ← hErr, sub_sub_cancel, sub_zero, p] using he

/-- The gradient flow drives the least-squares objective to its infimum,
including when the infimum is unattained. -/
theorem leastSquaresGradientFlow_tendsto_iInf (A : E →L[𝕜] F) (y : F)
    {x : ℝ → E} (hx : leastSquaresGradientFlow A y x) :
    Tendsto (fun t : ℝ => ‖A (x t) - y‖ ^ 2) atTop (𝓝 (⨅ u : E, ‖A u - y‖ ^ 2)) := by
  let U := A.range.topologicalClosure
  let p := U.starProjection y
  have hlim : Tendsto (fun t : ℝ => ‖A (pinvSemigroupApproximation A t y) - y‖ ^ 2)
      atTop (𝓝 (‖p - y‖ ^ 2)) :=
    ((comp_pinvSemigroupApproximation_tendsto A y).sub_const y).norm.pow 2
  have hle (u : E) : ‖p - y‖ ^ 2 ≤ ‖A u - y‖ ^ 2 := by
    have hu : A u ∈ U := A.range.le_topologicalClosure ⟨u, rfl⟩
    have hbd : BddBelow (Set.range (fun v : U => ‖y - (v : F)‖)) :=
      ⟨0, by rintro _ ⟨v, rfl⟩; exact norm_nonneg _⟩
    have hdist : ‖y - p‖ ≤ ‖y - A u‖ := by
      rw [U.starProjection_minimal y]
      exact ciInf_le hbd ⟨A u, hu⟩
    rw [norm_sub_rev p y, norm_sub_rev (A u) y]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hdist
  have hval : (⨅ u : E, ‖A u - y‖ ^ 2) = ‖p - y‖ ^ 2 := by
    have hb : BddBelow (Set.range (fun u : E => ‖A u - y‖ ^ 2)) :=
      ⟨0, by rintro _ ⟨u, rfl⟩; exact sq_nonneg _⟩
    exact le_antisymm
      (ge_of_tendsto' hlim (fun t => ciInf_le hb (pinvSemigroupApproximation A t y)))
      (le_ciInf hle)
  rw [hval]
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [leastSquaresGradientFlow_eqOn_pinvSemigroupApproximation A y hx ht]

/-- **Theorem 9(d)** of [benIsrael2003generalized], for arbitrary data.
The squared projected residual is nonincreasing and tends to zero. -/
theorem theorem_9_d (A : E →L[𝕜] F) (y : F) :
    let p := A.range.topologicalClosure.starProjection y
    let f := fun t : ℝ => ‖p - A (pinvSemigroupApproximation A t y)‖ ^ 2
    AntitoneOn f (Ici 0) ∧ Tendsto f atTop (𝓝 0) := by
  intro p f
  have hErr (t : ℝ) : p - A (pinvSemigroupApproximation A t y) =
      gradientSemigroup (A.comp A.adjoint) t p := pinvSemigroupApproximation_projected_error A t y
  refine ⟨?_, ?_⟩
  · simpa only [ContinuousLinearMap.adjoint_adjoint, ← hErr, f] using
      normalSemigroup_norm_sq_antitoneOn A.adjoint p
  · have h := (tendsto_const_nhds (x := p)).sub (comp_pinvSemigroupApproximation_tendsto A y)
    have h' : Tendsto (fun t : ℝ => p - A (pinvSemigroupApproximation A t y)) atTop (𝓝 0) := by
      simpa only [p, sub_self] using h
    simpa [f] using
      h'.norm.pow 2

private theorem maximalInverse_normal_data (A : E →L[𝕜] F)
    (y : (maximalTsengInverse (A.toLinearMap.toPMap ⊤)).domain) :
    let x := maximalTsengInverse (A.toLinearMap.toPMap ⊤) y
    x ∈ A.adjoint.range.topologicalClosure ∧ A.adjoint (A x) = A.adjoint y ∧
      A x = A.range.topologicalClosure.starProjection y := by
  intro x
  let T := A.toLinearMap.toPMap ⊤
  let S := maximalTsengInverse T
  have hT : T.IsClosed := A.isClosed_toPMap (by simp)
  have h := isTsengInverse_maximalTsengInverse_of_isClosed hT
  have hR : T.toFun.range = A.range := LinearMap.range_toPMap_top A.toLinearMap
  have hk : T.ker = A.ker := by rw [LinearMap.toPMap_ker, top_inf_eq]
  refine ⟨?_, ?_, ?_⟩
  · have he : x ∈ S.toFun.range := ⟨y, rfl⟩
    rw [← (lemma_3 h).2] at he
    have ho : x ∈ T.kerᗮ := he.2
    rwa [hk, A.orthogonal_ker] at ho
  · have he := h.right y
    change (y : F) - A x ∈ T.toFun.rangeᗮ at he
    rw [hR, A.orthogonal_range] at he
    change A.adjoint ((y : F) - A x) = 0 at he
    rw [map_sub, sub_eq_zero] at he
    exact he.symm
  · have he := h.projections.2 y
    change A x = T.toFun.range.topologicalClosure.starProjection y at he
    rwa [hR] at he

/-- The domain condition for the maximal inverse is exactly the union of
the first two classes in Equation (93). -/
theorem maximalInverse_mem_domain_iff_projection_mem_range (A : E →L[𝕜] F) (y : F) :
    y ∈ (maximalTsengInverse (A.toLinearMap.toPMap ⊤)).domain ↔
      A.range.topologicalClosure.starProjection y ∈ A.range := by
  let T := A.toLinearMap.toPMap ⊤
  let S := maximalTsengInverse T
  let p := A.range.topologicalClosure.starProjection y
  constructor
  · intro hy
    exact ⟨S ⟨y, hy⟩, (maximalInverse_normal_data A ⟨y, hy⟩).2.2⟩
  · intro hp
    have hT : T.IsClosed := A.isClosed_toPMap (by simp)
    have h := isTsengInverse_maximalTsengInverse_of_isClosed hT
    have hR : T.toFun.range = A.range := LinearMap.range_toPMap_top A.toLinearMap
    have hp' : p ∈ S.domain := h.range_le_domain (hR.symm ▸ hp)
    have horth : y - p ∈ A.rangeᗮ := by
      rw [← A.range.orthogonal_closure]
      exact A.range.topologicalClosure.sub_starProjection_mem_orthogonal y
    have hker : y - p ∈ S.ker := by
      rw [maximalTsengInverse_ker, hR]
      exact horth
    have hy := S.domain.add_mem (S.ker_le_domain hker) hp'
    rwa [sub_add_cancel] at hy

/-- **Equations (88)–(90)** of [benIsrael2003generalized], Chapter 9.
The integral representations converge strongly on the actual domain of
the maximal inverse, including when its domain is proper. -/
theorem pinvSemigroupApproximation_tendsto (A : E →L[𝕜] F)
    (y : (maximalTsengInverse (A.toLinearMap.toPMap ⊤)).domain) :
    Tendsto (fun t : ℝ => pinvSemigroupApproximation A t y) atTop
      (𝓝 (maximalTsengInverse (A.toLinearMap.toPMap ⊤) y)) := by
  let x := maximalTsengInverse (A.toLinearMap.toPMap ⊤) y
  have hx := maximalInverse_normal_data A y
  have h := normalSemigroup_tendsto_zero A x hx.1
  have he := (tendsto_const_nhds (x := x)).sub h
  have hErr (t : ℝ) : x - pinvSemigroupApproximation A t y =
      gradientSemigroup (A.adjoint.comp A) t x := pinvSemigroupApproximation_error A t hx.2.1
  simpa only [← hErr, sub_sub_cancel, sub_zero, x] using he

/-- **Equation (90)** of [benIsrael2003generalized], Chapter 9.
The inverse approximation error tends to zero in norm on the inverse domain. -/
theorem pinvSemigroupApproximation_error_norm_tendsto_zero (A : E →L[𝕜] F)
    (y : (maximalTsengInverse (A.toLinearMap.toPMap ⊤)).domain) :
    Tendsto (fun t : ℝ =>
      ‖maximalTsengInverse (A.toLinearMap.toPMap ⊤) y - pinvSemigroupApproximation A t y‖)
      atTop (𝓝 0) := by
  let x := maximalTsengInverse (A.toLinearMap.toPMap ⊤) y
  have h := (tendsto_const_nhds (x := x)).sub (pinvSemigroupApproximation_tendsto A y)
  simpa only [x, sub_self, norm_zero] using h.norm

/-- **Theorem 9(b)** of [benIsrael2003generalized], for the full domain of the maximal inverse. -/
theorem theorem_9_b (A : E →L[𝕜] F)
    (y : (maximalTsengInverse (A.toLinearMap.toPMap ⊤)).domain) :
    let x := maximalTsengInverse (A.toLinearMap.toPMap ⊤) y
    let f := fun t : ℝ => ‖x - pinvSemigroupApproximation A t y‖ ^ 2
    AntitoneOn f (Ici 0) ∧ Tendsto f atTop (𝓝 0) := by
  intro x f
  have hx := maximalInverse_normal_data A y
  have hErr (t : ℝ) : x - pinvSemigroupApproximation A t y =
      gradientSemigroup (A.adjoint.comp A) t x := pinvSemigroupApproximation_error A t hx.2.1
  refine ⟨?_, ?_⟩
  · simpa only [← hErr, f] using normalSemigroup_norm_sq_antitoneOn A x
  · have h := (tendsto_const_nhds (x := x)).sub (pinvSemigroupApproximation_tendsto A y)
    have h' : Tendsto (fun t : ℝ => x - pinvSemigroupApproximation A t y) atTop (𝓝 0) := by
      simpa only [x, sub_self] using h
    simpa [f] using h'.norm.pow 2

private theorem closure_range_comp_adjoint (A : E →L[𝕜] F) :
    (A.comp A.adjoint).range.topologicalClosure = A.range.topologicalClosure := by
  have hself : (A.comp A.adjoint).adjoint = A.comp A.adjoint := by
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
  have hk : (A.comp A.adjoint).ker = A.adjoint.ker := by
    simpa only [ContinuousLinearMap.adjoint_adjoint] using A.adjoint.ker_adjoint_comp_self
  calc
    _ = (A.comp A.adjoint).kerᗮ := by rw [(A.comp A.adjoint).orthogonal_ker, hself]
    _ = _ := by rw [hk, A.adjoint.orthogonal_ker, ContinuousLinearMap.adjoint_adjoint]

private theorem starProjection_closure_range_comp_adjoint (A : E →L[𝕜] F) (y : F) :
    (A.comp A.adjoint).range.topologicalClosure.starProjection y =
      A.range.topologicalClosure.starProjection y := by
  have h := closure_range_comp_adjoint A
  symm
  apply A.range.topologicalClosure.eq_starProjection_of_mem_orthogonal
  · rw [← h]
    exact (A.comp A.adjoint).range.topologicalClosure.starProjection_apply_mem y
  · rw [← h]
    exact (A.comp A.adjoint).range.topologicalClosure.sub_starProjection_mem_orthogonal y

/-- Membership in Class I of Equation (93) is the domain of `(AA*)†`. -/
theorem maximalGramInverse_mem_domain_iff_projection_mem_range (A : E →L[𝕜] F) (y : F) :
    y ∈ (maximalTsengInverse ((A.comp A.adjoint).toLinearMap.toPMap ⊤)).domain ↔
      A.range.topologicalClosure.starProjection y ∈ (A.comp A.adjoint).range := by
  rw [maximalInverse_mem_domain_iff_projection_mem_range, starProjection_closure_range_comp_adjoint]

/-- Class I data always belong to the domain of the left maximal inverse. -/
theorem maximalInverse_mem_domain_of_maximalGramInverse_mem_domain (A : E →L[𝕜] F) {y : F}
    (hy : y ∈ (maximalTsengInverse ((A.comp A.adjoint).toLinearMap.toPMap ⊤)).domain) :
    y ∈ (maximalTsengInverse (A.toLinearMap.toPMap ⊤)).domain := by
  obtain ⟨z, hz⟩ := (maximalGramInverse_mem_domain_iff_projection_mem_range A y).mp hy
  exact (maximalInverse_mem_domain_iff_projection_mem_range A y).mpr ⟨A.adjoint z, hz⟩

/-- Closed range rules out Class III in Equation (93). -/
theorem maximalInverse_domain_eq_top_of_isClosed_range (A : E →L[𝕜] F)
    (hR : IsClosed (A.range : Set F)) :
    (maximalTsengInverse (A.toLinearMap.toPMap ⊤)).domain = ⊤ := by
  apply top_unique
  intro y _
  apply (maximalInverse_mem_domain_iff_projection_mem_range A y).mpr
  exact (le_of_eq hR.submodule_topologicalClosure_eq)
    (A.range.topologicalClosure.starProjection_apply_mem y)

/-- In Class I, the left maximal-inverse value is the adjoint applied
to the maximal-inverse value for `AA*`. -/
theorem maximalInverse_apply_eq_adjoint_maximalGramInverse (A : E →L[𝕜] F) {y : F}
    (hy : y ∈ (maximalTsengInverse (A.toLinearMap.toPMap ⊤)).domain)
    (hz : y ∈ (maximalTsengInverse ((A.comp A.adjoint).toLinearMap.toPMap ⊤)).domain) :
    maximalTsengInverse (A.toLinearMap.toPMap ⊤) ⟨y, hy⟩ =
      A.adjoint (maximalTsengInverse ((A.comp A.adjoint).toLinearMap.toPMap ⊤) ⟨y, hz⟩) := by
  let x := maximalTsengInverse (A.toLinearMap.toPMap ⊤) ⟨y, hy⟩
  let z := maximalTsengInverse ((A.comp A.adjoint).toLinearMap.toPMap ⊤) ⟨y, hz⟩
  have hx := maximalInverse_normal_data A ⟨y, hy⟩
  have hz' := (maximalInverse_normal_data (A.comp A.adjoint) ⟨y, hz⟩).2.2
  rw [starProjection_closure_range_comp_adjoint A] at hz'
  have hk : x - A.adjoint z ∈ A.ker := by
    change A (x - A.adjoint z) = 0
    rw [map_sub, sub_eq_zero]
    exact hx.2.2.trans hz'.symm
  have ho : x - A.adjoint z ∈ A.kerᗮ := by
    rw [A.orthogonal_ker]
    exact A.adjoint.range.topologicalClosure.sub_mem hx.1
      (A.adjoint.range.le_topologicalClosure ⟨z, rfl⟩)
  exact sub_eq_zero.mp (Submodule.disjoint_def.mp A.ker.orthogonal_disjoint _ hk ho)

/-- **Theorem 9(a)** of [benIsrael2003generalized]. On Class I data the inverse error satisfies the
rational bound with the two maximal-inverse values. -/
theorem theorem_9_a (A : E →L[𝕜] F) {y : F}
    (hy : y ∈ (maximalTsengInverse (A.toLinearMap.toPMap ⊤)).domain)
    (hz : y ∈ (maximalTsengInverse ((A.comp A.adjoint).toLinearMap.toPMap ⊤)).domain)
    {t : ℝ} (ht : 0 ≤ t) :
    let x := maximalTsengInverse (A.toLinearMap.toPMap ⊤) ⟨y, hy⟩
    let z := maximalTsengInverse ((A.comp A.adjoint).toLinearMap.toPMap ⊤) ⟨y, hz⟩
    ‖x - pinvSemigroupApproximation A t y‖ ^ 2 ≤
      ‖x‖ ^ 2 * ‖z‖ ^ 2 / (‖z‖ ^ 2 + 2 * ‖x‖ ^ 2 * t) := by
  intro x z
  have hx := maximalInverse_normal_data A ⟨y, hy⟩
  have he : x - pinvSemigroupApproximation A t y =
      gradientSemigroup (A.adjoint.comp A) t x := pinvSemigroupApproximation_error A t hx.2.1
  have hxz : x = A.adjoint z := maximalInverse_apply_eq_adjoint_maximalGramInverse A hy hz
  rw [he, hxz]
  exact normalSemigroup_norm_sq_le_rational A z ht

private theorem rational_rate_monotone {u v c t : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hc : 0 < c) (ht : 0 ≤ t) :
    u * c / (c + 2 * u * t) ≤ v * c / (c + 2 * v * t) := by
  have hv := hu.trans huv
  have hdenU : 0 < c + 2 * u * t := by positivity
  have hdenV : 0 < c + 2 * v * t := by positivity
  apply (div_le_div_iff₀ hdenU hdenV).mpr
  nlinarith only [mul_nonneg (sq_nonneg c) (sub_nonneg.mpr huv)]

/-- **Theorem 9(c)** of [benIsrael2003generalized]. On the domain of the maximal inverse the squared
projected residual has the source's rational bound. -/
theorem theorem_9_c (A : E →L[𝕜] F)
    (y : (maximalTsengInverse (A.toLinearMap.toPMap ⊤)).domain) {t : ℝ} (ht : 0 ≤ t) :
    let x := maximalTsengInverse (A.toLinearMap.toPMap ⊤) y
    let p := A.range.topologicalClosure.starProjection y
    ‖p - A (pinvSemigroupApproximation A t y)‖ ^ 2 ≤
      ‖(y : F)‖ ^ 2 * ‖x‖ ^ 2 / (‖x‖ ^ 2 + 2 * ‖(y : F)‖ ^ 2 * t) := by
  intro x p
  have hp : A x = p := (maximalInverse_normal_data A y).2.2
  have hErr : p - A (pinvSemigroupApproximation A t y) =
      gradientSemigroup (A.comp A.adjoint) t p := pinvSemigroupApproximation_projected_error A t y
  by_cases hx : x = 0
  · have hp' : p = 0 := by rw [← hp, hx, map_zero]
    rw [hErr, hp', hx, map_zero]
    simp
  have hb := normalSemigroup_norm_sq_le_rational A.adjoint x ht
  rw [ContinuousLinearMap.adjoint_adjoint, hp] at hb
  rw [hErr]
  have hpy := (sq_le_sq₀ (norm_nonneg p) (norm_nonneg (y : F))).mpr
    (A.range.topologicalClosure.norm_starProjection_apply_le y)
  exact hb.trans (rational_rate_monotone (sq_nonneg _) hpy (sq_pos_of_pos (norm_pos_iff.mpr hx)) ht)

end ContinuousApproximation


section Neumann

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The left residual operator in **Equation (95)**. -/
def leftNeumannResidual (A : E →L[𝕜] F) (α : ℝ) : E →L[𝕜] E :=
  1 - (α : 𝕜) • A.adjoint.comp A

/-- The right residual operator in **Theorem 10**. -/
def rightNeumannResidual (A : E →L[𝕜] F) (α : ℝ) : F →L[𝕜] F :=
  1 - (α : 𝕜) • A.comp A.adjoint

/-- **Equations (91) and (95)** of [benIsrael2003generalized], Chapter 9.
The `N`th Neumann approximation sums the terms through exponent `N`. -/
def pinvNeumannApproximation (A : E →L[𝕜] F) (α : ℝ) (N : ℕ) : F →L[𝕜] E :=
  ∑ k ∈ Finset.range (N + 1), ((leftNeumannResidual A α) ^ k).comp ((α : 𝕜) • A.adjoint)

/-- The zero operator has zero Neumann approximations for every step size. -/
theorem pinvNeumannApproximation_zero (α : ℝ) (N : ℕ) :
    pinvNeumannApproximation (0 : E →L[𝕜] F) α N = 0 := by
  simp [pinvNeumannApproximation]

/-- **Equation (92)** of [benIsrael2003generalized], Chapter 9.
The normalized step for Theorem 10, with zero step for the zero operator. -/
def neumannStepsize (A : E →L[𝕜] F) (c : ℝ) : ℝ := c / ‖A‖ ^ 2

/-- **Equation (93)** of [benIsrael2003generalized], Chapter 9.
Classes I, II, III place the projection of `y` in the range of `AA*`,
in the range of `A` alone, or outside the range of `A`. -/
def pinvApproximationDomainClass (A : E →L[𝕜] F) (y : F) : Fin 3 := by
  classical
  let z := A.range.topologicalClosure.starProjection y
  exact if z ∈ (A.comp A.adjoint).range then 0 else if z ∈ A.range then 1 else 2

/-- Class I consists of data in the domain of the Gram inverse. Classes I
and II together consist of data in the domain of the maximal inverse. -/
theorem pinvApproximationDomainClass_iff (A : E →L[𝕜] F) (y : F) :
    (pinvApproximationDomainClass A y = 0 ↔
      y ∈ (maximalTsengInverse ((A.comp A.adjoint).toLinearMap.toPMap ⊤)).domain) ∧
    (pinvApproximationDomainClass A y ≠ 2 ↔
      y ∈ (maximalTsengInverse (A.toLinearMap.toPMap ⊤)).domain) := by
  classical
  rw [maximalGramInverse_mem_domain_iff_projection_mem_range,
    maximalInverse_mem_domain_iff_projection_mem_range]
  dsimp only [pinvApproximationDomainClass]
  split_ifs with hG hA
  · have hy : A.range.topologicalClosure.starProjection y ∈ A.range := by
      obtain ⟨z, hz⟩ := hG
      exact ⟨A.adjoint z, hz⟩
    exact ⟨iff_of_true rfl hG, iff_of_true (by decide) hy⟩
  all_goals simp_all

private theorem neumann_intertwine (A : E →L[𝕜] F) (α : ℝ) :
    A.comp (leftNeumannResidual A α) = (rightNeumannResidual A α).comp A := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [leftNeumannResidual, rightNeumannResidual,
    ContinuousLinearMap.comp_apply, sub_apply, one_apply_eq_self, smul_apply, map_sub, map_smul]

/-- `A` intertwines the left and right residual powers. -/
theorem neumann_intertwine_pow (A : E →L[𝕜] F) (α : ℝ) (n : ℕ) :
    A.comp ((leftNeumannResidual A α) ^ n) = (rightNeumannResidual A α ^ n).comp A := by
  induction n with
  | zero =>
    apply ContinuousLinearMap.ext
    intro x
    simp only [pow_zero, ContinuousLinearMap.comp_apply, one_apply_eq_self]
  | succ n ih =>
    simp only [pow_succ', ContinuousLinearMap.mul_def]
    calc
      _ = (A.comp (leftNeumannResidual A α)).comp (leftNeumannResidual A α ^ n) :=
        (ContinuousLinearMap.comp_assoc _ _ _).symm
      _ = (rightNeumannResidual A α).comp (A.comp (leftNeumannResidual A α ^ n)) := by
        rw [neumann_intertwine, ContinuousLinearMap.comp_assoc]
      _ = _ := by rw [ih, ContinuousLinearMap.comp_assoc]

omit [CompleteSpace E] in
private theorem geom_sum_comp (Q : E →L[𝕜] E) (n : ℕ) :
    (∑ k ∈ Finset.range n, Q ^ k).comp (1 - Q) = 1 - Q ^ n :=
  geom_sum_mul_neg Q n

omit [CompleteSpace E] [CompleteSpace F] in
private theorem sum_comp_clm {ι G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (s : Finset ι) (f : ι → F →L[𝕜] G) (A : E →L[𝕜] F) :
    (∑ i ∈ s, f i).comp A = ∑ i ∈ s, (f i).comp A := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, sum_apply]

omit [CompleteSpace E] [CompleteSpace F] in
private theorem comp_sum_clm {ι G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (s : Finset ι) (A : F →L[𝕜] G) (f : ι → E →L[𝕜] F) :
    A.comp (∑ i ∈ s, f i) = ∑ i ∈ s, A.comp (f i) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, sum_apply, map_sum]

/-- The Neumann sum satisfies the first-order update in **Equation (95)**. -/
theorem pinvNeumannApproximation_succ (A : E →L[𝕜] F) (α : ℝ) (N : ℕ) (y : F) :
    pinvNeumannApproximation A α (N + 1) y =
      pinvNeumannApproximation A α N y -
        (α : 𝕜) • A.adjoint (A (pinvNeumannApproximation A α N y) - y) := by
  let Q := leftNeumannResidual A α
  let L := (α : 𝕜) • A.adjoint
  have hs : pinvNeumannApproximation A α (N + 1) =
      Q.comp (pinvNeumannApproximation A α N) + L := by
    change (∑ k ∈ Finset.range (N + 1 + 1), (Q ^ k).comp L) =
      Q.comp (∑ k ∈ Finset.range (N + 1), (Q ^ k).comp L) + L
    rw [Finset.sum_range_succ', comp_sum_clm]
    simp only [pow_zero, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
  rw [hs]
  simp only [Q, L, leftNeumannResidual, add_apply, ContinuousLinearMap.comp_apply, sub_apply,
    one_apply_eq_self, smul_apply, map_sub, smul_sub]
  abel

/-- The left product with the Neumann approximation is the identity
minus one power of the left residual. -/
theorem pinvNeumannApproximation_comp (A : E →L[𝕜] F) (α : ℝ) (N : ℕ) :
    (pinvNeumannApproximation A α N).comp A = 1 - leftNeumannResidual A α ^ (N + 1) := by
  let Q := leftNeumannResidual A α
  have hQ : 1 - Q = ((α : 𝕜) • A.adjoint).comp A := by
    change 1 - (1 - (α : 𝕜) • A.adjoint.comp A) = _
    rw [sub_sub_cancel, ContinuousLinearMap.smul_comp]
  calc
    _ = ∑ k ∈ Finset.range (N + 1), (Q ^ k).comp (1 - Q) := by
      rw [pinvNeumannApproximation, sum_comp_clm]
      apply Finset.sum_congr rfl
      intro k _
      rw [ContinuousLinearMap.comp_assoc, hQ]
    _ = _ := by rw [← sum_comp_clm, geom_sum_comp]

/-- The right product with the Neumann approximation is the identity
minus one power of the right residual. -/
theorem comp_pinvNeumannApproximation (A : E →L[𝕜] F) (α : ℝ) (N : ℕ) :
    A.comp (pinvNeumannApproximation A α N) = 1 - rightNeumannResidual A α ^ (N + 1) := by
  let Q := rightNeumannResidual A α
  have hQ : 1 - Q = A.comp ((α : 𝕜) • A.adjoint) := by
    change 1 - (1 - (α : 𝕜) • A.comp A.adjoint) = _
    rw [sub_sub_cancel, ContinuousLinearMap.comp_smul]
  calc
    _ = ∑ k ∈ Finset.range (N + 1), (Q ^ k).comp (1 - Q) := by
      rw [pinvNeumannApproximation, comp_sum_clm]
      apply Finset.sum_congr rfl
      intro k _
      rw [← ContinuousLinearMap.comp_assoc, neumann_intertwine_pow,
        ContinuousLinearMap.comp_assoc, hQ]
    _ = _ := by rw [← sum_comp_clm, geom_sum_comp]

/-- For any solution of the normal equations, the error after the
Neumann sum is the corresponding power of the left residual. -/
theorem pinvNeumannApproximation_error (A : E →L[𝕜] F) (α : ℝ) (N : ℕ)
    {x : E} {y : F} (h : A.adjoint (A x) = A.adjoint y) :
    x - pinvNeumannApproximation A α N y = (leftNeumannResidual A α ^ (N + 1)) x := by
  have he : pinvNeumannApproximation A α N y = pinvNeumannApproximation A α N (A x) := by
    simp only [pinvNeumannApproximation, sum_apply, ContinuousLinearMap.comp_apply, smul_apply, h]
  rw [he, ← ContinuousLinearMap.comp_apply, pinvNeumannApproximation_comp,
    sub_apply, one_apply_eq_self]
  abel

/-- The corresponding right residual after the finite Neumann sum. -/
theorem pinvNeumannApproximation_range_error (A : E →L[𝕜] F) (α : ℝ) (N : ℕ) (y : F) :
    y - A (pinvNeumannApproximation A α N y) = (rightNeumannResidual A α ^ (N + 1)) y := by
  rw [← ContinuousLinearMap.comp_apply, comp_pinvNeumannApproximation,
    sub_apply, one_apply_eq_self]
  abel

/-- One left-residual step decreases squared norm by at least the squared
image norm times the effective step factor. -/
theorem leftNeumannResidual_norm_sq_le (A : E →L[𝕜] F) {α : ℝ} (hα : 0 ≤ α) (x : E) :
    ‖leftNeumannResidual A α x‖ ^ 2 ≤
      ‖x‖ ^ 2 - (α * (2 - α * ‖A‖ ^ 2)) * ‖A x‖ ^ 2 := by
  have hA : ‖A.adjoint‖ = ‖A‖ := LinearIsometryEquiv.norm_map _ _
  have hnorm : ‖A.adjoint (A x)‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖A x‖ ^ 2 := by
    rw [← mul_pow, ← hA]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (A.adjoint.le_opNorm (A x))
  change ‖x - (α : 𝕜) • A.adjoint (A x)‖ ^ 2 ≤ _
  rw [norm_sub_sq (𝕜 := 𝕜), inner_smul_right, A.adjoint_inner_right, RCLike.re_ofReal_mul,
    inner_self_eq_norm_sq, norm_smul, RCLike.norm_ofReal, abs_of_nonneg hα,
    mul_pow]
  calc
    _ ≤ ‖x‖ ^ 2 - 2 * (α * ‖A x‖ ^ 2) + α ^ 2 * (‖A‖ ^ 2 * ‖A x‖ ^ 2) := by
      gcongr
    _ = _ := by ring

/-- The right residual satisfies the corresponding squared-norm estimate. -/
theorem rightNeumannResidual_norm_sq_le (A : E →L[𝕜] F) {α : ℝ} (hα : 0 ≤ α) (y : F) :
    ‖rightNeumannResidual A α y‖ ^ 2 ≤
      ‖y‖ ^ 2 - (α * (2 - α * ‖A‖ ^ 2)) * ‖A.adjoint y‖ ^ 2 := by
  have hadj : ‖A.adjoint‖ = ‖A‖ := LinearIsometryEquiv.norm_map _ _
  simpa only [leftNeumannResidual, rightNeumannResidual, ContinuousLinearMap.adjoint_adjoint,
    hadj] using leftNeumannResidual_norm_sq_le A.adjoint hα y

omit [CompleteSpace E] in
private theorem pow_apply_norm_le_of_step_norm_le (Q : E →L[𝕜] E)
    (hQ : ∀ x, ‖Q x‖ ≤ ‖x‖) (n : ℕ) (x : E) : ‖(Q ^ n) x‖ ≤ ‖x‖ := by
  induction n with
  | zero => simp only [pow_zero, one_apply_eq_self, le_refl]
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
    exact (hQ _).trans ih

private theorem leftNeumannResidual_contractive (A : E →L[𝕜] F) {α : ℝ}
    (hα : 0 ≤ α) (hκ : 0 ≤ α * (2 - α * ‖A‖ ^ 2)) (x : E) :
    ‖leftNeumannResidual A α x‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact (leftNeumannResidual_norm_sq_le A hα x).trans
    (sub_le_self _ (mul_nonneg hκ (sq_nonneg _)))

private theorem rightNeumannResidual_contractive (A : E →L[𝕜] F) {α : ℝ}
    (hα : 0 ≤ α) (hκ : 0 ≤ α * (2 - α * ‖A‖ ^ 2)) (y : F) :
    ‖rightNeumannResidual A α y‖ ≤ ‖y‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact (rightNeumannResidual_norm_sq_le A hα y).trans
    (sub_le_self _ (mul_nonneg hκ (sq_nonneg _)))

private theorem recurrence_rational_rate (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) {κ : ℝ}
    (hκ : 0 ≤ κ) (h : ∀ n, a (n + 1) ≤ a n - κ * a n ^ 2) (n : ℕ) :
    a n ≤ a 0 / (1 + κ * (n : ℝ) * a 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ha₀ := ha 0
    have han := ha n
    have ha' : a (n + 1) ≤ a n :=
      (h n).trans (sub_le_self _ (mul_nonneg hκ (sq_nonneg _)))
    have hmono := mul_le_mul_of_nonneg_left ha' (mul_nonneg hκ (ha n))
    have hb₀ : 0 < 1 + κ * (n : ℝ) * a 0 := by positivity
    let b := a 0 / (1 + κ * (n : ℝ) * a 0)
    have hb : 0 ≤ b := div_nonneg (ha 0) hb₀.le
    have hu : 0 < 1 + κ * a n := by positivity
    have hv : 0 < 1 + κ * b := by positivity
    calc
      _ ≤ a n / (1 + κ * a n) := (le_div_iff₀ hu).mpr (by nlinarith [h n])
      _ ≤ b / (1 + κ * b) := by
        apply (div_le_div_iff₀ hu hv).mpr
        change a n ≤ b at ih
        nlinarith only [ih]
      _ = _ := by
        let d := 1 + κ * (n : ℝ) * a 0
        have hd : d ≠ 0 := hb₀.ne'
        have hden : 1 + κ * b = (d + κ * a 0) / d := by
          change 1 + κ * (a 0 / d) = _
          field_simp [hd]
        rw [hden, show b = a 0 / d from rfl, div_div_div_cancel_right₀ hd]
        congr 1
        dsimp only [d]
        push_cast
        ring

/-- **Theorem 10(a)** of [benIsrael2003generalized], in range coordinates.
The left residual powers on the image of the adjoint satisfy the rational
squared-error bound. -/
theorem leftNeumannResidual_pow_norm_sq_rate (A : E →L[𝕜] F) {α : ℝ}
    (hα : 0 ≤ α) (hκ : 0 ≤ α * (2 - α * ‖A‖ ^ 2)) (z : F) (n : ℕ) :
    let κ := α * (2 - α * ‖A‖ ^ 2)
    ‖(leftNeumannResidual A α ^ n) (A.adjoint z)‖ ^ 2 ≤
      ‖A.adjoint z‖ ^ 2 * ‖z‖ ^ 2 / (‖z‖ ^ 2 + κ * (n : ℝ) * ‖A.adjoint z‖ ^ 2) := by
  intro κ
  by_cases hz : z = 0
  · simp [hz]
  have hz₂ : 0 < ‖z‖ ^ 2 := pow_pos (norm_pos_iff.mpr hz) _
  let Q := leftNeumannResidual A α
  let R := rightNeumannResidual A α
  let v (j : ℕ) := (Q ^ j) (A.adjoint z)
  let a (j : ℕ) := ‖v j‖ ^ 2
  have hQR (j : ℕ) : v j = A.adjoint ((R ^ j) z) := by
    have hi : A.adjoint.comp (R ^ j) = (Q ^ j).comp A.adjoint := by
      simpa only [R, Q, leftNeumannResidual, rightNeumannResidual,
        ContinuousLinearMap.adjoint_adjoint] using neumann_intertwine_pow A.adjoint α j
    exact (DFunLike.congr_fun hi z).symm
  have henergy (j : ℕ) : a (j + 1) ≤ a j - (κ / ‖z‖ ^ 2) * a j ^ 2 := by
    have hinner : RCLike.re (inner 𝕜 (v j) (v j)) =
        RCLike.re (inner 𝕜 ((R ^ j) z) (A (v j))) := by
      calc
        _ = RCLike.re (inner 𝕜 (A.adjoint ((R ^ j) z)) (v j)) :=
          congrArg (fun u => RCLike.re (inner 𝕜 u (v j))) (hQR j)
        _ = _ := by rw [A.adjoint_inner_left]
    have hR : ‖(R ^ j) z‖ ≤ ‖z‖ := pow_apply_norm_le_of_step_norm_le R
      (rightNeumannResidual_contractive A hα hκ) j z
    have hs : a j ≤ ‖z‖ * ‖A (v j)‖ := calc
      a j = RCLike.re (inner 𝕜 (v j) (v j)) := (inner_self_eq_norm_sq _).symm
      _ = _ := hinner
      _ ≤ ‖(R ^ j) z‖ * ‖A (v j)‖ := re_inner_le_norm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hR (norm_nonneg _)
    have hc : a j ^ 2 ≤ ‖z‖ ^ 2 * ‖A (v j)‖ ^ 2 := by
      rw [← mul_pow]
      exact (sq_le_sq₀ (sq_nonneg _) (by positivity)).mpr hs
    have hd : (κ / ‖z‖ ^ 2) * a j ^ 2 ≤ κ * ‖A (v j)‖ ^ 2 := by
      rw [div_mul_eq_mul_div]
      exact (div_le_iff₀ hz₂).mpr (by
        nlinarith [mul_le_mul_of_nonneg_left hc hκ])
    calc
      a (j + 1) = ‖Q (v j)‖ ^ 2 := by
        have hstep : (Q ^ (j + 1)) (A.adjoint z) = Q (v j) := by
          rw [pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
        exact congrArg (fun u : E => ‖u‖ ^ 2) hstep
      _ ≤ a j - κ * ‖A (v j)‖ ^ 2 := leftNeumannResidual_norm_sq_le A hα (v j)
      _ ≤ _ := sub_le_sub_left hd _
  have ha := recurrence_rational_rate a (fun _ => sq_nonneg _) (div_nonneg hκ hz₂.le) henergy n
  have hzero : a 0 = ‖A.adjoint z‖ ^ 2 := by
    simp only [a, v, pow_zero, one_apply_eq_self]
  rw [hzero] at ha
  calc
    _ = a n := rfl
    _ ≤ _ := ha.trans_eq (by
      field_simp
      ring)

/-- **Theorem 10(c)** of [benIsrael2003generalized], in range coordinates.
The right residual powers on the image of the operator satisfy the same
rational squared-error bound. -/
theorem rightNeumannResidual_pow_norm_sq_rate (A : E →L[𝕜] F) {α : ℝ}
    (hα : 0 ≤ α) (hκ : 0 ≤ α * (2 - α * ‖A‖ ^ 2)) (x : E) (n : ℕ) :
    let κ := α * (2 - α * ‖A‖ ^ 2)
    ‖(rightNeumannResidual A α ^ n) (A x)‖ ^ 2 ≤
      ‖A x‖ ^ 2 * ‖x‖ ^ 2 / (‖x‖ ^ 2 + κ * (n : ℝ) * ‖A x‖ ^ 2) := by
  have hd : ‖A.adjoint‖ = ‖A‖ := LinearIsometryEquiv.norm_map _ _
  have hκ' : 0 ≤ α * (2 - α * ‖A.adjoint‖ ^ 2) := hd.symm ▸ hκ
  simpa only [hd, leftNeumannResidual, rightNeumannResidual, ContinuousLinearMap.adjoint_adjoint]
    using leftNeumannResidual_pow_norm_sq_rate A.adjoint hα hκ' x n

omit [CompleteSpace E] in
private theorem tendsto_pow_apply_of_dense_subset (Q : E →L[𝕜] E) (s : Set E)
    (hQ : ∀ x, ‖Q x‖ ≤ ‖x‖) (hs : ∀ y ∈ s, Tendsto (fun n : ℕ => (Q ^ n) y) atTop (𝓝 0))
    (x : E) (hx : x ∈ closure s) : Tendsto (fun n : ℕ => (Q ^ n) x) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hs y hy) (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hle : ‖(Q ^ n) (x - y)‖ ≤ ‖x - y‖ := pow_apply_norm_le_of_step_norm_le Q hQ n _
  have hz := hN n hn
  rw [dist_zero_right] at hz ⊢
  rw [dist_eq_norm] at hxy
  calc
    ‖(Q ^ n) x‖ = ‖(Q ^ n) (x - y) + (Q ^ n) y‖ := by rw [map_sub, sub_add_cancel]
    _ ≤ ‖(Q ^ n) (x - y)‖ + ‖(Q ^ n) y‖ := norm_add_le _ _
    _ ≤ ‖x - y‖ + ‖(Q ^ n) y‖ := add_le_add hle le_rfl
    _ < ε := by linarith

/-- **Theorem 10(b)** of [benIsrael2003generalized]. The left residual
converges strongly to zero on the closure of the adjoint range. -/
theorem leftNeumannResidual_pow_tendsto_zero (A : E →L[𝕜] F) {α : ℝ}
    (hα : 0 ≤ α) (hκ : 0 < α * (2 - α * ‖A‖ ^ 2)) (x : E)
    (hx : x ∈ A.adjoint.range.topologicalClosure) :
    Tendsto (fun n : ℕ => (leftNeumannResidual A α ^ n) x) atTop (𝓝 0) := by
  apply tendsto_pow_apply_of_dense_subset _ (A.adjoint.range : Set E)
    (leftNeumannResidual_contractive A hα hκ.le) _ x hx
  rintro y ⟨z, rfl⟩
  change Tendsto (fun n : ℕ => (leftNeumannResidual A α ^ n) (A.adjoint z)) atTop (𝓝 0)
  by_cases hz : A.adjoint z = 0
  · simp only [hz, map_zero, tendsto_const_nhds]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let κ := α * (2 - α * ‖A‖ ^ 2)
  have hh : Tendsto (fun n : ℕ => ‖z‖ ^ 2 + κ * (n : ℝ) * ‖A.adjoint z‖ ^ 2) atTop atTop := by
    apply tendsto_atTop_add_const_left
    exact ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hκ).atTop_mul_const
      (pow_pos (norm_pos_iff.mpr hz) _)
  have hzero : Tendsto (fun n : ℕ =>
      ‖A.adjoint z‖ ^ 2 * ‖z‖ ^ 2 / (‖z‖ ^ 2 + κ * (n : ℝ) * ‖A.adjoint z‖ ^ 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hh
  have hs := squeeze_zero (fun _ => sq_nonneg _)
    (leftNeumannResidual_pow_norm_sq_rate A hα hκ.le z) hzero
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  change Tendsto (fun n : ℕ => Real.sqrt (‖(leftNeumannResidual A α ^ n) (A.adjoint z)‖ ^ 2))
    atTop (𝓝 (Real.sqrt 0)) at h
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h

/-- **Theorem 10(d)** of [benIsrael2003generalized]. The right residual
converges strongly to zero on the closure of the range. -/
theorem rightNeumannResidual_pow_tendsto_zero (A : E →L[𝕜] F) {α : ℝ}
    (hα : 0 ≤ α) (hκ : 0 < α * (2 - α * ‖A‖ ^ 2)) (y : F)
    (hy : y ∈ A.range.topologicalClosure) :
    Tendsto (fun n : ℕ => (rightNeumannResidual A α ^ n) y) atTop (𝓝 0) := by
  have ha : ‖A.adjoint‖ = ‖A‖ := LinearIsometryEquiv.norm_map _ _
  have hκ' : 0 < α * (2 - α * ‖A.adjoint‖ ^ 2) := ha.symm ▸ hκ
  have hy' : y ∈ A.adjoint.adjoint.range.topologicalClosure := by
    rw [ContinuousLinearMap.adjoint_adjoint]
    exact hy
  simpa only [leftNeumannResidual, rightNeumannResidual, ContinuousLinearMap.adjoint_adjoint]
    using leftNeumannResidual_pow_tendsto_zero A.adjoint hα hκ' y hy'

/-- The projected residual starts from the projection of the datum onto
the closure of the range, even for data outside the inverse domain. -/
theorem pinvNeumannApproximation_projected_error (A : E →L[𝕜] F)
    (α : ℝ) (N : ℕ) (y : F) :
    let z := A.range.topologicalClosure.starProjection y
    z - A (pinvNeumannApproximation A α N y) = (rightNeumannResidual A α ^ (N + 1)) z := by
  intro z
  have hres : y - z ∈ A.rangeᗮ := by
    rw [← A.range.orthogonal_closure]
    exact A.range.topologicalClosure.sub_starProjection_mem_orthogonal y
  rw [A.orthogonal_range] at hres
  have he : A.adjoint y = A.adjoint z := by
    change A.adjoint (y - z) = 0 at hres
    rwa [map_sub, sub_eq_zero] at hres
  have hp : pinvNeumannApproximation A α N y = pinvNeumannApproximation A α N z := by
    simp only [pinvNeumannApproximation, sum_apply, ContinuousLinearMap.comp_apply, smul_apply, he]
  rw [hp, pinvNeumannApproximation_range_error]

/-- **Theorem 10(d)** of [benIsrael2003generalized], including data
outside the domain of the maximal inverse. The fitted values converge to
the orthogonal projection onto the closure of the range. -/
theorem comp_pinvNeumannApproximation_tendsto (A : E →L[𝕜] F) {α : ℝ}
    (hα : 0 ≤ α) (hκ : 0 < α * (2 - α * ‖A‖ ^ 2)) (y : F) :
    Tendsto (fun N : ℕ => A (pinvNeumannApproximation A α N y)) atTop
      (𝓝 (A.range.topologicalClosure.starProjection y)) := by
  let z := A.range.topologicalClosure.starProjection y
  have hz := rightNeumannResidual_pow_tendsto_zero A hα hκ z
    (A.range.topologicalClosure.starProjection_apply_mem y)
  have he := (tendsto_const_nhds (x := z)).sub (hz.comp (tendsto_add_atTop_nat 1))
  have hErr (N : ℕ) : z - A (pinvNeumannApproximation A α N y) =
      (rightNeumannResidual A α ^ (N + 1)) z := pinvNeumannApproximation_projected_error A α N y
  simpa only [Function.comp_apply, ← hErr, sub_sub_cancel, sub_zero, z] using he

/-- **Theorem 10(b)** of [benIsrael2003generalized]. The finite Neumann
sums converge on the domain of the maximal generalized inverse. -/
theorem pinvNeumannApproximation_tendsto (A : E →L[𝕜] F) {α : ℝ}
    (hα : 0 ≤ α) (hκ : 0 < α * (2 - α * ‖A‖ ^ 2))
    (y : (maximalTsengInverse (A.toLinearMap.toPMap ⊤)).domain) :
    Tendsto (fun N : ℕ => pinvNeumannApproximation A α N y) atTop
      (𝓝 (maximalTsengInverse (A.toLinearMap.toPMap ⊤) y)) := by
  let x := maximalTsengInverse (A.toLinearMap.toPMap ⊤) y
  have hx := maximalInverse_normal_data A y
  have hh := leftNeumannResidual_pow_tendsto_zero A hα hκ x hx.1
  have he := (tendsto_const_nhds (x := x)).sub (hh.comp (tendsto_add_atTop_nat 1))
  have hErr (N : ℕ) : x - pinvNeumannApproximation A α N y =
      (leftNeumannResidual A α ^ (N + 1)) x := pinvNeumannApproximation_error A α N hx.2.1
  simpa only [Function.comp_apply, ← hErr, sub_sub_cancel, sub_zero] using he

/-- **Theorem 10(a)** of [benIsrael2003generalized], for class I. The
rate uses a solution of the projected Gram equation, which may be chosen
as its least-norm solution. -/
theorem pinvNeumannApproximation_error_bound (A : E →L[𝕜] F) {α : ℝ}
    (hα : 0 ≤ α) (hκ : 0 ≤ α * (2 - α * ‖A‖ ^ 2)) (N : ℕ)
    (y : (maximalTsengInverse (A.toLinearMap.toPMap ⊤)).domain) (z : F)
    (hz : A (A.adjoint z) = A.range.topologicalClosure.starProjection y) :
    let x := maximalTsengInverse (A.toLinearMap.toPMap ⊤) y
    ‖x - pinvNeumannApproximation A α N y‖ ^ 2 ≤
      ‖x‖ ^ 2 * ‖z‖ ^ 2 /
        (‖z‖ ^ 2 + (α * (2 - α * ‖A‖ ^ 2)) * (↑N + 1) * ‖x‖ ^ 2) := by
  intro x
  obtain ⟨hx, hN, hAx⟩ := maximalInverse_normal_data A y
  have hxo : x ∈ A.kerᗮ := by rw [A.orthogonal_ker]; exact hx
  have hzo : A.adjoint z ∈ A.kerᗮ := by
    rw [A.orthogonal_ker]
    exact A.adjoint.range.le_topologicalClosure ⟨z, rfl⟩
  have he : x = A.adjoint z := by
    have hK : x - A.adjoint z ∈ A.ker := by
      change A (x - A.adjoint z) = 0
      rw [map_sub, hAx, hz, sub_self]
    have hmem : x - A.adjoint z ∈ A.ker ⊓ A.kerᗮ := ⟨hK, A.kerᗮ.sub_mem hxo hzo⟩
    rw [A.ker.inf_orthogonal_eq_bot, Submodule.mem_bot, sub_eq_zero] at hmem
    exact hmem
  change ‖x - pinvNeumannApproximation A α N y‖ ^ 2 ≤ _
  rw [pinvNeumannApproximation_error A α N hN]
  change ‖(leftNeumannResidual A α ^ (N + 1)) x‖ ^ 2 ≤ _
  rw [he]
  simpa only [Nat.cast_add, Nat.cast_one] using
    leftNeumannResidual_pow_norm_sq_rate A hα hκ z (N + 1)

/-- **Theorem 10(c)** of [benIsrael2003generalized], for classes I and II.
The fitted-value error has the rational bound, with `N + 1` residual steps. -/
theorem pinvNeumannApproximation_projected_error_bound (A : E →L[𝕜] F) {α : ℝ}
    (hα : 0 ≤ α) (hκ : 0 ≤ α * (2 - α * ‖A‖ ^ 2)) (N : ℕ)
    (y : (maximalTsengInverse (A.toLinearMap.toPMap ⊤)).domain) :
    let x := maximalTsengInverse (A.toLinearMap.toPMap ⊤) y
    let z := A.range.topologicalClosure.starProjection (y : F)
    ‖z - A (pinvNeumannApproximation A α N y)‖ ^ 2 ≤
      ‖(y : F)‖ ^ 2 * ‖x‖ ^ 2 /
        (‖x‖ ^ 2 + (α * (2 - α * ‖A‖ ^ 2)) * (↑N + 1) * ‖(y : F)‖ ^ 2) := by
  intro x z
  have hAx : A x = z := (maximalInverse_normal_data A y).2.2
  let κ := α * (2 - α * ‖A‖ ^ 2)
  have he : z - A (pinvNeumannApproximation A α N y) =
      (rightNeumannResidual A α ^ (N + 1)) z := pinvNeumannApproximation_projected_error A α N y
  have hbound : ‖z - A (pinvNeumannApproximation A α N y)‖ ^ 2 ≤
      ‖z‖ ^ 2 * ‖x‖ ^ 2 / (‖x‖ ^ 2 + κ * (↑N + 1) * ‖z‖ ^ 2) := by
    rw [he, ← hAx]
    simpa only [Nat.cast_add, Nat.cast_one] using
      rightNeumannResidual_pow_norm_sq_rate A hα hκ x (N + 1)
  refine hbound.trans ?_
  by_cases hx : x = 0
  · simp [hx]
  have hz : ‖z‖ ≤ ‖(y : F)‖ := A.range.topologicalClosure.norm_starProjection_apply_le y.val
  have hx₂ := pow_pos (norm_pos_iff.mpr hx) 2
  have hκ' : 0 ≤ κ := hκ
  have h₁ : 0 < ‖x‖ ^ 2 + κ * (↑N + 1) * ‖z‖ ^ 2 := by positivity
  have h₂ : 0 < ‖x‖ ^ 2 + κ * (↑N + 1) * ‖(y : F)‖ ^ 2 := by positivity
  apply (div_le_div_iff₀ h₁ h₂).mpr
  have hzz := (sq_le_sq₀ (norm_nonneg z) (norm_nonneg (y : F))).mpr hz
  nlinarith only [mul_le_mul_of_nonneg_right hzz (sq_nonneg (‖x‖ ^ 2))]

omit [CompleteSpace E] in
private theorem antitone_pow_apply_norm_sq (Q : E →L[𝕜] E) (x : E)
    (hQ : ∀ z, ‖Q z‖ ≤ ‖z‖) : Antitone fun n : ℕ => ‖(Q ^ n) x‖ ^ 2 := by
  apply antitone_nat_of_succ_le
  intro n
  have hstep : (Q ^ (n + 1)) x = Q ((Q ^ n) x) := by
    rw [pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
  rw [hstep]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hQ _)

/-- **Theorem 10(b,d)** of [benIsrael2003generalized]. The inverse error
on its domain and the fitted-value error on all inputs decrease
monotonically as the number of terms grows. -/
theorem pinvNeumannApproximation_error_antitone (A : E →L[𝕜] F) {α : ℝ}
    (hα : 0 ≤ α) (hκ : 0 ≤ α * (2 - α * ‖A‖ ^ 2)) :
    (∀ y : (maximalTsengInverse (A.toLinearMap.toPMap ⊤)).domain,
      Antitone (fun N : ℕ => ‖maximalTsengInverse (A.toLinearMap.toPMap ⊤) y -
        pinvNeumannApproximation A α N y‖ ^ 2)) ∧
    (∀ y : F, Antitone (fun N : ℕ => ‖A.range.topologicalClosure.starProjection y -
      A (pinvNeumannApproximation A α N y)‖ ^ 2)) := by
  constructor
  · intro y
    let x := maximalTsengInverse (A.toLinearMap.toPMap ⊤) y
    have hN := (maximalInverse_normal_data A y).2.1
    have hE (N : ℕ) : x - pinvNeumannApproximation A α N y =
        (leftNeumannResidual A α ^ (N + 1)) x := pinvNeumannApproximation_error A α N hN
    intro m n hmn
    change ‖x - pinvNeumannApproximation A α n y‖ ^ 2 ≤
      ‖x - pinvNeumannApproximation A α m y‖ ^ 2
    rw [hE, hE]
    exact antitone_pow_apply_norm_sq _ x (leftNeumannResidual_contractive A hα hκ)
      (Nat.add_le_add_right hmn 1)
  · intro y m n hmn
    change ‖A.range.topologicalClosure.starProjection y - A (pinvNeumannApproximation A α n y)‖
      ^ 2 ≤ ‖A.range.topologicalClosure.starProjection y - A (pinvNeumannApproximation A α m y)‖ ^ 2
    rw [pinvNeumannApproximation_projected_error A α n y,
      pinvNeumannApproximation_projected_error A α m y]
    exact antitone_pow_apply_norm_sq _ (A.range.topologicalClosure.starProjection y)
      (rightNeumannResidual_contractive A hα hκ) (Nat.add_le_add_right hmn 1)

omit [CompleteSpace E] [CompleteSpace F] in
private theorem neumannStepsize_pos_effective (A : E →L[𝕜] F) (hA : A ≠ 0) {c : ℝ}
    (hc₀ : 0 < c) (hc₁ : c < 2) :
    let α := neumannStepsize A c
    0 < α ∧ 0 < α * (2 - α * ‖A‖ ^ 2) ∧ α * (2 - α * ‖A‖ ^ 2) = (2 - c) * c / ‖A‖ ^ 2 := by
  intro α
  have hA₀ : 0 < ‖A‖ ^ 2 := pow_pos (norm_pos_iff.mpr hA) _
  have hα : 0 < α := div_pos hc₀ hA₀
  have he : α * ‖A‖ ^ 2 = c := div_mul_cancel₀ _ hA₀.ne'
  rw [he]
  refine ⟨hα, mul_pos hα (sub_pos.mpr hc₁), ?_⟩
  change (c / ‖A‖ ^ 2) * (2 - c) = (2 - c) * c / ‖A‖ ^ 2
  rw [div_mul_eq_mul_div, mul_comm c]

/-- **Theorem 10** of [benIsrael2003generalized], Chapter 9. With the
normalized step, the approximations converge on the inverse domain and
their fitted values converge for every input. -/
theorem theorem_10 (A : E →L[𝕜] F) (hA : A ≠ 0) {c : ℝ} (hc₀ : 0 < c) (hc₁ : c < 2) :
    let α := neumannStepsize A c
    (∀ y : (maximalTsengInverse (A.toLinearMap.toPMap ⊤)).domain,
      Tendsto (fun N : ℕ => pinvNeumannApproximation A α N y) atTop
        (𝓝 (maximalTsengInverse (A.toLinearMap.toPMap ⊤) y))) ∧
    (∀ y : F, Tendsto (fun N : ℕ => A (pinvNeumannApproximation A α N y)) atTop
      (𝓝 (A.range.topologicalClosure.starProjection y))) := by
  intro α
  obtain ⟨hα, hκ, _⟩ := neumannStepsize_pos_effective A hA hc₀ hc₁
  exact ⟨pinvNeumannApproximation_tendsto A hα.le hκ,
    comp_pinvNeumannApproximation_tendsto A hα.le hκ⟩

/-- **Theorem 10(a)** with the normalized step and both maximal inverse
values. The coefficient counts all `N + 1` terms. -/
theorem theorem_10_a (A : E →L[𝕜] F) (hA : A ≠ 0) {c : ℝ} (hc₀ : 0 < c) (hc₁ : c < 2)
    (N : ℕ) {y : F} (hy : y ∈ (maximalTsengInverse (A.toLinearMap.toPMap ⊤)).domain)
    (hG : y ∈ (maximalTsengInverse ((A.comp A.adjoint).toLinearMap.toPMap ⊤)).domain) :
    let x := maximalTsengInverse (A.toLinearMap.toPMap ⊤) ⟨y, hy⟩
    let z := maximalTsengInverse ((A.comp A.adjoint).toLinearMap.toPMap ⊤) ⟨y, hG⟩
    ‖x - pinvNeumannApproximation A (neumannStepsize A c) N y‖ ^ 2 ≤
      ‖x‖ ^ 2 * ‖z‖ ^ 2 /
        (‖z‖ ^ 2 + ((2 - c) * c / ‖A‖ ^ 2) * (↑N + 1) * ‖x‖ ^ 2) := by
  intro x z
  have hz : A (A.adjoint z) = A.range.topologicalClosure.starProjection y := by
    have h := (maximalInverse_normal_data (A.comp A.adjoint) ⟨y, hG⟩).2.2
    rwa [starProjection_closure_range_comp_adjoint] at h
  obtain ⟨hα, hκ, he⟩ := neumannStepsize_pos_effective A hA hc₀ hc₁
  simpa only [he] using pinvNeumannApproximation_error_bound A hα.le hκ.le N ⟨y, hy⟩ z hz

/-- **Theorem 10(c)** with the normalized step, for data in the maximal
inverse domain. -/
theorem theorem_10_c (A : E →L[𝕜] F) (hA : A ≠ 0) {c : ℝ} (hc₀ : 0 < c) (hc₁ : c < 2)
    (N : ℕ) (y : (maximalTsengInverse (A.toLinearMap.toPMap ⊤)).domain) :
    let x := maximalTsengInverse (A.toLinearMap.toPMap ⊤) y
    let p := A.range.topologicalClosure.starProjection (y : F)
    ‖p - A (pinvNeumannApproximation A (neumannStepsize A c) N y)‖ ^ 2 ≤
      ‖(y : F)‖ ^ 2 * ‖x‖ ^ 2 /
        (‖x‖ ^ 2 + ((2 - c) * c / ‖A‖ ^ 2) * (↑N + 1) * ‖(y : F)‖ ^ 2) := by
  obtain ⟨hα, hκ, he⟩ := neumannStepsize_pos_effective A hA hc₀ hc₁
  simpa only [he] using pinvNeumannApproximation_projected_error_bound A hα.le hκ.le N y

/-- Closed range gives operator-norm convergence of the Neumann
approximations to the bounded Moore–Penrose inverse. -/
theorem pinvNeumann_tendsto_of_closedRange (A : E →L[𝕜] F)
    (hR : IsClosed (A.range : Set F)) {α : ℝ} (hα : 0 ≤ α)
    (hκ : 0 < α * (2 - α * ‖A‖ ^ 2)) :
    Tendsto (pinvNeumannApproximation A α) atTop (𝓝 (boundedMoorePenroseInverse A hR)) := by
  let B := boundedMoorePenroseInverse A hR
  let Q := leftNeumannResidual A α
  let κ := α * (2 - α * ‖A‖ ^ 2)
  let C := max ‖B‖ 1
  have hC : 0 < C := zero_lt_one.trans_le (le_max_right _ _)
  have hC₂ : 0 < C ^ 2 := pow_pos hC 2
  have hκ' : 0 < κ := hκ
  obtain ⟨hAB, hBA⟩ := boundedMoorePenroseInverse_projections A hR
  have hB (y : F) : B y ∈ A.kerᗮ := by
    rw [← (boundedMoorePenroseInverse_range_ker A hR).1]
    exact ⟨y, rfl⟩
  have hN (y : F) : A.adjoint (A (B y)) = A.adjoint y := by
    have he := DFunLike.congr_fun hAB y
    change A (B y) = A.range.topologicalClosure.starProjection y at he
    have ho : y - A (B y) ∈ A.rangeᗮ := by
      rw [he, ← A.range.orthogonal_closure]
      exact A.range.topologicalClosure.sub_starProjection_mem_orthogonal y
    rw [A.orthogonal_range] at ho
    change A.adjoint (y - A (B y)) = 0 at ho
    rw [map_sub, sub_eq_zero] at ho
    exact ho.symm
  have hQ_mem (x : E) (hx : x ∈ A.kerᗮ) : Q x ∈ A.kerᗮ := by
    change x - (α : 𝕜) • A.adjoint (A x) ∈ A.kerᗮ
    apply A.kerᗮ.sub_mem hx
    apply A.kerᗮ.smul_mem
    rw [A.orthogonal_ker]
    exact A.adjoint.range.le_topologicalClosure ⟨A x, rfl⟩
  let d := max (1 - κ / C ^ 2) 0
  have hd₀ : 0 ≤ d := le_max_right _ _
  have hd₁ : d < 1 := max_lt_iff.mpr
    ⟨sub_lt_self _ (div_pos hκ' hC₂), zero_lt_one⟩
  let q := Real.sqrt d
  have hq₀ : 0 ≤ q := Real.sqrt_nonneg _
  have hq₁ : q < 1 := by
    apply (sq_lt_sq₀ hq₀ zero_le_one).mp
    change (Real.sqrt d) ^ 2 < 1 ^ 2
    rw [Real.sq_sqrt hd₀, one_pow]
    exact hd₁
  have hQ (x : E) (hx : x ∈ A.kerᗮ) : ‖Q x‖ ≤ q * ‖x‖ := by
    have he : B (A x) = x := by
      have hh := DFunLike.congr_fun hBA x
      exact hh.trans (A.kerᗮ.starProjection_eq_self_iff.mpr hx)
    have hAx : ‖x‖ ≤ C * ‖A x‖ := by
      calc
        ‖x‖ = ‖B (A x)‖ := congrArg norm he.symm
        _ ≤ ‖B‖ * ‖A x‖ := B.le_opNorm (A x)
        _ ≤ C * ‖A x‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    have hx₂ : ‖x‖ ^ 2 ≤ C ^ 2 * ‖A x‖ ^ 2 := by
      rw [← mul_pow]
      exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hAx
    have hκx : (κ / C ^ 2) * ‖x‖ ^ 2 ≤ κ * ‖A x‖ ^ 2 := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hC₂).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hx₂ hκ'.le]
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hq₀ (norm_nonneg _))).mp
    calc
      _ ≤ ‖x‖ ^ 2 - κ * ‖A x‖ ^ 2 := leftNeumannResidual_norm_sq_le A hα x
      _ ≤ ‖x‖ ^ 2 - (κ / C ^ 2) * ‖x‖ ^ 2 := sub_le_sub_left hκx _
      _ = (1 - κ / C ^ 2) * ‖x‖ ^ 2 := by ring
      _ ≤ d * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
      _ = (q * ‖x‖) ^ 2 := by rw [mul_pow, show q ^ 2 = d from Real.sq_sqrt hd₀]
  have hpow (m : ℕ) (x : E) (hx : x ∈ A.kerᗮ) :
      (Q ^ m) x ∈ A.kerᗮ ∧ ‖(Q ^ m) x‖ ≤ q ^ m * ‖x‖ := by
    induction m with
    | zero => simpa only [pow_zero, one_apply_eq_self, one_mul, le_refl, and_true] using hx
    | succ m ih =>
      have hstep : (Q ^ (m + 1)) x = Q ((Q ^ m) x) := by
        rw [pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
      rw [hstep, pow_succ' q]
      exact ⟨hQ_mem _ ih.1, by
        rw [mul_assoc]
        exact (hQ _ ih.1).trans (mul_le_mul_of_nonneg_left ih.2 hq₀)⟩
  have hErr (N : ℕ) : B - pinvNeumannApproximation A α N = (Q ^ (N + 1)).comp B := by
    apply ContinuousLinearMap.ext
    intro y
    exact pinvNeumannApproximation_error A α N (hN y)
  have hn (N : ℕ) : ‖B - pinvNeumannApproximation A α N‖ ≤ q ^ (N + 1) * ‖B‖ := by
    rw [hErr]
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro y
    change ‖(Q ^ (N + 1)) (B y)‖ ≤ _
    rw [mul_assoc]
    exact ((hpow _ _ (hB y)).2).trans
      (mul_le_mul_of_nonneg_left (B.le_opNorm y) (pow_nonneg hq₀ _))
  rw [← tendsto_sub_nhds_zero_iff]
  have hh := ((tendsto_pow_atTop_nhds_zero_of_lt_one hq₀ hq₁).comp
    (tendsto_add_atTop_nat 1)).mul_const ‖B‖
  refine squeeze_zero_norm' (a := fun N : ℕ => q ^ (N + 1) * ‖B‖) (Eventually.of_forall ?_) ?_
  · intro N
    exact (norm_sub_rev _ _).trans_le (hn N)
  · simpa only [Function.comp_apply, zero_mul] using hh

private theorem pinvNeumannApproximation_right_sum (A : E →L[𝕜] F) (α : ℝ) (N : ℕ) :
    pinvNeumannApproximation A α N = ((α : 𝕜) • A.adjoint).comp
      (∑ j ∈ Finset.range (N + 1), rightNeumannResidual A α ^ j) := by
  rw [pinvNeumannApproximation, comp_sum_clm]
  apply Finset.sum_congr rfl
  intro j _
  have he : A.adjoint.comp (rightNeumannResidual A α ^ j) =
      (leftNeumannResidual A α ^ j).comp A.adjoint := by
    simpa only [leftNeumannResidual, rightNeumannResidual, ContinuousLinearMap.adjoint_adjoint]
      using neumann_intertwine_pow A.adjoint α j
  rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp, he]

private theorem geometric_sum_blocks {R : Type*} [Semiring R] (q : R) (m p : ℕ) :
    (∑ j ∈ Finset.range m, q ^ j) * (∑ k ∈ Finset.range p, q ^ (m * k)) =
      ∑ i ∈ Finset.range (m * p), q ^ i := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Finset.sum_range_succ, mul_add, ih, Nat.mul_succ, Finset.sum_range_add, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [← pow_add, add_comm]

private theorem sum_choose_prefix (p k : ℕ) :
    (∑ j ∈ Finset.range p, j.choose k) = p.choose (k + 1) := by
  induction p with
  | zero => simp
  | succ p ih => rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ, add_comm]

private theorem geometric_sum_binomial {R : Type*} [Semiring R] (q : R) (p : ℕ) :
    (∑ j ∈ Finset.range p, (q + 1) ^ j) =
      ∑ k ∈ Finset.range p, p.choose (k + 1) • q ^ k := by
  have hbin (j : ℕ) (hj : j ∈ Finset.range p) :
      (q + 1) ^ j = ∑ k ∈ Finset.range p, j.choose k • q ^ k := by
    have hsub : Finset.range (j + 1) ⊆ Finset.range p :=
      Finset.range_mono (Nat.succ_le_of_lt (Finset.mem_range.mp hj))
    have he : (q + 1) ^ j = ∑ k ∈ Finset.range (j + 1), j.choose k • q ^ k := by
      simpa only [one_pow, mul_one, nsmul_eq_mul'] using (Commute.one_right q).add_pow j
    rw [he]
    apply Finset.sum_subset hsub
    intro k _ hk
    rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_succ_le (Nat.le_of_not_lt
      (fun he => hk (Finset.mem_range.mpr he)))), zero_nsmul]
  simp_rw [Finset.sum_congr rfl hbin]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_smul, sum_choose_prefix]

/-- **Equation (96)** of [benIsrael2003generalized], Chapter 9.
One order-`p` update multiplies the inverse estimate by the geometric sum
of its current right residual. -/
def neumannHyperpowerStep (A : E →L[𝕜] F) (B : F →L[𝕜] E) (p : ℕ) : F →L[𝕜] E :=
  B.comp (∑ j ∈ Finset.range p, (1 - A.comp B) ^ j)

/-- **Equation (97)** of [benIsrael2003generalized], Chapter 9.
The binomial form starts at the coefficient `p.choose 1`, so the
term with exponent minus one is omitted. -/
def neumannBinomialStep (A : E →L[𝕜] F) (B : F →L[𝕜] E) (p : ℕ) : F →L[𝕜] E :=
  B.comp (∑ j ∈ Finset.range p, p.choose (j + 1) • (-(A.comp B)) ^ j)

omit [CompleteSpace E] [CompleteSpace F] in
/-- Both higher-order formulas give the same update. -/
theorem neumannBinomialStep_eq_hyperpower (A : E →L[𝕜] F) (B : F →L[𝕜] E) (p : ℕ) :
    neumannBinomialStep A B p = neumannHyperpowerStep A B p := by
  unfold neumannBinomialStep neumannHyperpowerStep
  rw [sub_eq_add_neg, add_comm 1 _, geometric_sum_binomial]

/-- The sequence of geometric-sum updates in **Equation (96)**. -/
def neumannHyperpowerIterate (A : E →L[𝕜] F) (α : ℝ) (p : ℕ) : ℕ → F →L[𝕜] E
  | 0 => (α : 𝕜) • A.adjoint
  | n + 1 => neumannHyperpowerStep A (neumannHyperpowerIterate A α p n) p

/-- The sequence of binomial updates in **Equation (97)**. -/
def neumannBinomialIterate (A : E →L[𝕜] F) (α : ℝ) (p : ℕ) : ℕ → F →L[𝕜] E
  | 0 => (α : 𝕜) • A.adjoint
  | n + 1 => neumannBinomialStep A (neumannBinomialIterate A α p n) p

private theorem neumannHyperpowerStep_approximation (A : E →L[𝕜] F) (α : ℝ)
    (m p : ℕ) (hm : 0 < m) (hp : 0 < p) :
    neumannHyperpowerStep A (pinvNeumannApproximation A α (m - 1)) p =
      pinvNeumannApproximation A α (m * p - 1) := by
  let R := rightNeumannResidual A α
  have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have hmp : m * p - 1 + 1 = m * p := Nat.sub_add_cancel (Nat.mul_pos hm hp)
  have hprod : A.comp (pinvNeumannApproximation A α (m - 1)) = 1 - R ^ m := by
    rw [comp_pinvNeumannApproximation, hm']
  unfold neumannHyperpowerStep
  rw [hprod, sub_sub_cancel, pinvNeumannApproximation_right_sum, hm',
    pinvNeumannApproximation_right_sum, hmp, ContinuousLinearMap.comp_assoc]
  congr 1
  change (∑ j ∈ Finset.range m, R ^ j) * (∑ k ∈ Finset.range p, (R ^ m) ^ k) = _
  simp only [← pow_mul]
  exact geometric_sum_blocks R m p

/-- **Theorem 11**, Equations (96)–(98) of [benIsrael2003generalized].
After `N` higher-order updates both formulas equal the Neumann
approximation with `p^N` terms. -/
theorem theorem_11 (A : E →L[𝕜] F) (α : ℝ) (p : ℕ) (hp : 0 < p) (N : ℕ) :
    neumannHyperpowerIterate A α p N = pinvNeumannApproximation A α (p ^ N - 1) ∧
    neumannBinomialIterate A α p N = pinvNeumannApproximation A α (p ^ N - 1) := by
  induction N with
  | zero =>
    have he : pinvNeumannApproximation A α 0 = (α : 𝕜) • A.adjoint := by
      simp only [pinvNeumannApproximation, zero_add, Finset.sum_range_one, pow_zero]
      rfl
    simp only [pow_zero, Nat.sub_self, neumannHyperpowerIterate, neumannBinomialIterate,
      he, and_self]
  | succ n ih =>
    have he := neumannHyperpowerStep_approximation A α (p ^ n) p (Nat.pow_pos hp) hp
    rw [neumannHyperpowerIterate, neumannBinomialIterate, ih.1, ih.2,
      neumannBinomialStep_eq_hyperpower, pow_succ]
    exact ⟨he, he⟩

/-- The class-I rate following **Theorem 11**, with the actual number
of Neumann terms after `N` higher-order updates. -/
theorem neumannHyperpowerIterate_error_bound (A : E →L[𝕜] F) (hA : A ≠ 0) {c : ℝ}
    (hc₀ : 0 < c) (hc₁ : c < 2) (p : ℕ) (hp : 0 < p) (N : ℕ) {y : F}
    (hy : y ∈ (maximalTsengInverse (A.toLinearMap.toPMap ⊤)).domain)
    (hG : y ∈ (maximalTsengInverse ((A.comp A.adjoint).toLinearMap.toPMap ⊤)).domain) :
    let x := maximalTsengInverse (A.toLinearMap.toPMap ⊤) ⟨y, hy⟩
    let z := maximalTsengInverse ((A.comp A.adjoint).toLinearMap.toPMap ⊤) ⟨y, hG⟩
    ‖x - neumannHyperpowerIterate A (neumannStepsize A c) p N y‖ ^ 2 ≤
      ‖x‖ ^ 2 * ‖z‖ ^ 2 /
        (‖z‖ ^ 2 + ((2 - c) * c / ‖A‖ ^ 2) * (↑(p ^ N) : ℝ) * ‖x‖ ^ 2) := by
  intro x z
  have hpN : (↑(p ^ N - 1) : ℝ) + 1 = (↑(p ^ N) : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel (Nat.pow_pos hp : 1 ≤ p ^ N)
  rw [(theorem_11 A (neumannStepsize A c) p hp N).1, ← hpN]
  exact theorem_10_a A hA hc₀ hc₁ (p ^ N - 1) hy hG

end Neumann

section StationaryIteration

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The stationary iteration of **Equation (99)** starts at `x₀`. -/
def inverseStationaryIterate (A : E →L[𝕜] F) (B : F →L[𝕜] E) (b : F) (x₀ : E) : ℕ → E
  | 0 => x₀
  | k + 1 => inverseStationaryIterate A B b x₀ k - B (A (inverseStationaryIterate A B b x₀ k) - b)

/-- With preconditioner `α A*` and a zero start, Exercise 49 produces
the finite Neumann sums in Equation (95). -/
theorem inverseStationaryIterate_adjoint (A : E →L[𝕜] F) (α : ℝ) (b : F) (k : ℕ) :
    inverseStationaryIterate A ((α : 𝕜) • A.adjoint) b 0 (k + 1) =
      pinvNeumannApproximation A α k b := by
  induction k with
  | zero =>
    simp [inverseStationaryIterate, pinvNeumannApproximation, ContinuousLinearMap.one_def]
  | succ k ih =>
    rw [inverseStationaryIterate, ih, pinvNeumannApproximation_succ]
    rfl

omit [CompleteSpace F] in
private theorem inverseStationaryIterate_error
    (A : E →L[𝕜] F) (B : F →L[𝕜] E) (b : F) {x₀ x : E}
    (h₀ : x₀ ∈ A.kerᗮ) (hx : x ∈ A.kerᗮ) (hB : B.range ≤ A.kerᗮ)
    (hfix : B (A x - b) = 0) (k : ℕ) :
    inverseStationaryIterate A B b x₀ k ∈ A.kerᗮ ∧
    inverseStationaryIterate A B b x₀ k - x =
      ((A.kerᗮ.starProjection - B.comp A) ^ k) (x₀ - x) := by
  induction k with
  | zero => exact ⟨h₀, by simp [inverseStationaryIterate]⟩
  | succ k ih =>
    let u := inverseStationaryIterate A B b x₀ k
    change u - B (A u - b) ∈ A.kerᗮ ∧ u - B (A u - b) - x =
      ((A.kerᗮ.starProjection - B.comp A) ^ (k + 1)) (x₀ - x)
    refine ⟨A.kerᗮ.sub_mem ih.1 (hB ⟨_, rfl⟩), ?_⟩
    rw [pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, ← ih.2]
    change u - B (A u - b) - x = A.kerᗮ.starProjection (u - x) - B (A (u - x))
    rw [A.kerᗮ.starProjection_eq_self_iff.mpr (A.kerᗮ.sub_mem ih.1 hx)]
    have he : B (A u - b) = B (A (u - x)) := by
      have hBx : B (A x) = B b := sub_eq_zero.mp (by simpa only [map_sub] using hfix)
      rw [map_sub, map_sub, map_sub, hBx]
    rw [he]
    abel

/-- **Exercise 49** of [benIsrael2003generalized]. For a closed-range
operator and the indicated two-sided class of preconditioners, the
spectral-radius test yields convergence to the Moore–Penrose solution
from every point of the perpendicular complement of the kernel. -/
theorem exercise_9_49
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : H →L[ℂ] K) (hR : IsClosed (A.range : Set K)) (W : H →L[ℂ] K)
    (b : K) (x₀ : H) (h₀ : x₀ ∈ A.kerᗮ) :
    let B := A.adjoint.comp (W.comp A.adjoint)
    spectralRadius ℂ (A.kerᗮ.starProjection - B.comp A) < 1 →
      Tendsto (inverseStationaryIterate A B b x₀) atTop
        (𝓝 (boundedMoorePenroseInverse A hR b)) := by
  intro B hρ
  let x := boundedMoorePenroseInverse A hR b
  have hx : x ∈ A.kerᗮ := by
    rw [← (boundedMoorePenroseInverse_range_ker A hR).1]
    exact ⟨b, rfl⟩
  have hB : B.range ≤ A.kerᗮ := by
    rw [A.orthogonal_ker]
    rintro _ ⟨z, rfl⟩
    exact A.adjoint.range.le_topologicalClosure ⟨W (A.adjoint z), rfl⟩
  have hfix : B (A x - b) = 0 := by
    have hAx : A x = A.range.topologicalClosure.starProjection b :=
      DFunLike.congr_fun (boundedMoorePenroseInverse_projections A hR).1 b
    have hk : b - A x ∈ A.adjoint.ker := by
      rw [← A.orthogonal_range, ← A.range.orthogonal_closure, hAx]
      exact A.range.topologicalClosure.sub_starProjection_mem_orthogonal b
    change A.adjoint (b - A x) = 0 at hk
    have hz : A.adjoint (A x - b) = 0 := by rw [← neg_sub, map_neg, hk, neg_zero]
    change A.adjoint (W (A.adjoint (A x - b))) = 0
    rw [hz, map_zero, map_zero]
  rw [← tendsto_sub_nhds_zero_iff]
  change Tendsto (fun k => inverseStationaryIterate A B b x₀ k - x) atTop (𝓝 0)
  have he : (fun k => inverseStationaryIterate A B b x₀ k - x) =
      fun k => ((A.kerᗮ.starProjection - B.comp A) ^ k) (x₀ - x) :=
    funext fun k => (inverseStationaryIterate_error A B b h₀ hx hB hfix k).2
  rw [he]
  have hpow := tendsto_pow_of_spectralRadius_lt_one hρ
  simpa only [Function.comp_def, ContinuousLinearMap.apply_apply, zero_apply]
    using ((ContinuousLinearMap.apply ℂ H (x₀ - x)).continuous.tendsto 0).comp hpow

/-- **Exercise 50**, Equations (100)–(102) of [benIsrael2003generalized].
The splitting iteration preserves the perpendicular complement of the
common kernel. The choice `w = 1` gives the unrelaxed update. -/
theorem exercise_9_50 (A M N : E →L[𝕜] F) (hA : A = M + N)
    (hM : IsClosed (M.range : Set F)) (hK : A.ker = M.ker)
    (b : F) (x₀ : E) (h₀ : x₀ ∈ A.kerᗮ) (w : 𝕜) :
    let C := boundedMoorePenroseInverse M hM
    let x := inverseStationaryIterate A (w • C) b x₀
    (∀ k, x k ∈ A.kerᗮ) ∧
      (∀ k, x (k + 1) = (1 - w) • x k - w • C (N (x k)) + w • C b) := by
  intro C x
  have hC (y : F) : C y ∈ A.kerᗮ := by
    rw [hK, ← (boundedMoorePenroseInverse_range_ker M hM).1]
    exact ⟨y, rfl⟩
  have hx (k : ℕ) : x k ∈ A.kerᗮ := by
    induction k with
    | zero => exact h₀
    | succ k ih =>
      change x k - w • C (A (x k) - b) ∈ A.kerᗮ
      exact A.kerᗮ.sub_mem ih (A.kerᗮ.smul_mem _ (hC _))
  refine ⟨hx, fun k => ?_⟩
  have hCM : C (M (x k)) = x k :=
    (DFunLike.congr_fun (boundedMoorePenroseInverse_projections M hM).2 (x k)).trans
      (M.kerᗮ.starProjection_eq_self_iff.mpr (hK ▸ hx k))
  change x k - w • C (A (x k) - b) = _
  rw [hA, add_apply, map_sub, map_add, hCM, smul_sub, smul_add,
    sub_smul, one_smul]
  abel

/-- The unrelaxed split from **Equation (102)**. -/
theorem exercise_9_50_unrelaxed (A M N : E →L[𝕜] F) (hA : A = M + N)
    (hM : IsClosed (M.range : Set F)) (hK : A.ker = M.ker)
    (b : F) (x₀ : E) (h₀ : x₀ ∈ A.kerᗮ) (k : ℕ) :
    let C := boundedMoorePenroseInverse M hM
    let x := inverseStationaryIterate A C b x₀
    x (k + 1) = -C (N (x k)) + C b := by
  simpa only [sub_self, zero_smul, zero_sub, one_smul] using
    (exercise_9_50 A M N hA hM hK b x₀ h₀ 1).2 k

end StationaryIteration

end BenIsraelGreville.Chapter09
