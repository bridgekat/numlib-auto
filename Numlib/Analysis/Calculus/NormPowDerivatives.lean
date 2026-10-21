import Numlib.Analysis.Calculus.NormRpowHessian
import Numlib.Analysis.InnerProductSpace.NormPow

/-!
# Third derivatives of radial powers

Sharp operator bounds for the first three derivatives of powers of the norm.
The third order bound holds for real exponents at least four.
-/

open scoped Topology ContDiff
open Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The radial Hessian is differentiable away from the origin. -/
theorem differentiableAt_normRpowHessian_of_ne_zero (r : ℝ) {x : E} (hx : x ≠ 0) :
    DifferentiableAt ℝ (normRpowHessian r : E → E →L[ℝ] E →L[ℝ] ℝ) x := by
  have hs : Differentiable ℝ (fun z : E ↦ (innerSL ℝ z).smulRight (innerSL ℝ z)) :=
    ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)).differentiable.comp
      (innerSL ℝ).differentiable).clm_apply (innerSL ℝ).differentiable
  unfold normRpowHessian
  exact (((hasFDerivAt_norm_rpow_of_ne_zero hx (r - 2)).differentiableAt.const_mul
    r).smul_const _).add
    (((hasFDerivAt_norm_rpow_of_ne_zero hx (r - 4)).differentiableAt.const_mul
      (r * (r - 2))).smul hs.differentiableAt)

/-- Evaluation of the genuine derivative of the radial Hessian away from zero. -/
theorem fderiv_normRpowHessian_apply (r : ℝ) {x : E} (hx : x ≠ 0) (u v w : E) :
    fderiv ℝ (normRpowHessian r) x u v w =
      r * (r - 2) * ‖x‖ ^ (r - 4) *
        (inner ℝ x u * inner ℝ v w + inner ℝ x v * inner ℝ u w +
          inner ℝ x w * inner ℝ u v) +
      r * (r - 2) * (r - 4) * ‖x‖ ^ (r - 6) *
        (inner ℝ x u * inner ℝ x v * inner ℝ x w) := by
  have hd := differentiableAt_normRpowHessian_of_ne_zero r hx
  have he : fderiv ℝ (fun z : E ↦ normRpowHessian r z v w) x u =
      fderiv ℝ (normRpowHessian r) x u v w := by
    rw [fderiv_clm_apply (hd.clm_apply (differentiableAt_const v))
      (differentiableAt_const w), fderiv_clm_apply hd (differentiableAt_const v)]
    simp
  rw [← he]
  have hi (a : E) : HasFDerivAt (fun z : E ↦ inner ℝ z a) (innerSL ℝ a) x := by
    convert (innerSL ℝ a).hasFDerivAt (x := x) using 1
    funext z
    exact (real_inner_comm z a).symm
  have h1 := ((hasFDerivAt_norm_rpow_of_ne_zero hx (r - 2)).const_mul r).mul_const
    (inner ℝ v w)
  have h2 := ((hasFDerivAt_norm_rpow_of_ne_zero hx (r - 4)).const_mul
    (r * (r - 2))).mul ((hi v).mul (hi w))
  have h := h1.add h2
  change HasFDerivAt (fun z : E ↦ r * ‖z‖ ^ (r - 2) * inner ℝ v w +
    r * (r - 2) * ‖z‖ ^ (r - 4) * (inner ℝ z v * inner ℝ z w)) _ x at h
  rw [show (fun z : E ↦ normRpowHessian r z v w) =
    (fun z : E ↦ r * ‖z‖ ^ (r - 2) * inner ℝ v w +
      r * (r - 2) * ‖z‖ ^ (r - 4) * (inner ℝ z v * inner ℝ z w)) from
      funext (fun z ↦ normRpowHessian_apply r z v w), h.fderiv]
  simp only [add_apply, smul_apply,
    innerSL_apply_apply, smul_eq_mul, Pi.mul_apply]
  rw [show r - 2 - 2 = r - 4 by ring, show r - 4 - 2 = r - 6 by ring]
  simp only [real_inner_comm v u, real_inner_comm w u]
  ring

/-- The sharp trilinear bound for the derivative of the radial Hessian. -/
theorem abs_fderiv_normRpowHessian_apply_le {r : ℝ} (hr : 4 ≤ r)
    {x : E} (hx : x ≠ 0) (u v w : E) :
    |fderiv ℝ (normRpowHessian r) x u v w| ≤
      r * (r - 1) * (r - 2) * ‖x‖ ^ (r - 3) * ‖u‖ * ‖v‖ * ‖w‖ := by
  have hr0 : 0 ≤ r := by linarith
  have hr2 : 0 ≤ r - 2 := by linarith
  have hr4 : 0 ≤ r - 4 := by linarith
  rw [fderiv_normRpowHessian_apply r hx]
  have hA : 0 ≤ r * (r - 2) * ‖x‖ ^ (r - 4) := by positivity
  have hB : 0 ≤ r * (r - 2) * (r - 4) * ‖x‖ ^ (r - 6) := by positivity
  have hp1 : ‖x‖ ^ (r - 4) * ‖x‖ = ‖x‖ ^ (r - 3) := by
    rw [← Real.rpow_add_one (norm_ne_zero_iff.mpr hx)]
    congr 1
    ring
  have hp3 : ‖x‖ ^ (r - 6) * ‖x‖ ^ (3 : ℕ) = ‖x‖ ^ (r - 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (norm_pos_iff.mpr hx)]
    congr 1
    ring
  calc
    _ ≤ r * (r - 2) * ‖x‖ ^ (r - 4) *
        (|inner ℝ x u| * |inner ℝ v w| + |inner ℝ x v| * |inner ℝ u w| +
          |inner ℝ x w| * |inner ℝ u v|) +
      r * (r - 2) * (r - 4) * ‖x‖ ^ (r - 6) *
        (|inner ℝ x u| * |inner ℝ x v| * |inner ℝ x w|) := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul (r * (r - 2) * ‖x‖ ^ (r - 4)) _,
        abs_mul (r * (r - 2) * (r - 4) * ‖x‖ ^ (r - 6)) _,
        abs_of_nonneg hA, abs_of_nonneg hB]
      simp only [abs_mul]
      gcongr
      have ht : |inner ℝ x u * inner ℝ v w + inner ℝ x v * inner ℝ u w +
          inner ℝ x w * inner ℝ u v| ≤ |inner ℝ x u * inner ℝ v w| +
          |inner ℝ x v * inner ℝ u w| + |inner ℝ x w * inner ℝ u v| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      simpa only [abs_mul] using ht
    _ ≤ r * (r - 2) * ‖x‖ ^ (r - 4) *
        ((‖x‖ * ‖u‖) * (‖v‖ * ‖w‖) + (‖x‖ * ‖v‖) * (‖u‖ * ‖w‖) +
          (‖x‖ * ‖w‖) * (‖u‖ * ‖v‖)) +
      r * (r - 2) * (r - 4) * ‖x‖ ^ (r - 6) *
        ((‖x‖ * ‖u‖) * (‖x‖ * ‖v‖) * (‖x‖ * ‖w‖)) := by
      gcongr <;> exact abs_real_inner_le_norm _ _
    _ = (3 * r * (r - 2) * (‖x‖ ^ (r - 4) * ‖x‖) +
        r * (r - 2) * (r - 4) * (‖x‖ ^ (r - 6) * ‖x‖ ^ (3 : ℕ))) *
        ‖u‖ * ‖v‖ * ‖w‖ := by ring
    _ = _ := by rw [hp1, hp3]; ring

/-- The sharp operator bound for the third derivative of a radial power away from zero. -/
theorem norm_fderiv_normRpowHessian_le {r : ℝ} (hr : 4 ≤ r)
    {x : E} (hx : x ≠ 0) :
    ‖fderiv ℝ (normRpowHessian r) x‖ ≤
      r * (r - 1) * (r - 2) * ‖x‖ ^ (r - 3) := by
  have hr0 : 0 ≤ r := by linarith
  have hr1 : 0 ≤ r - 1 := by linarith
  have hr2 : 0 ≤ r - 2 := by linarith
  have hC : 0 ≤ r * (r - 1) * (r - 2) * ‖x‖ ^ (r - 3) := by positivity
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (norm_nonneg u))
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg hC (norm_nonneg u)) (norm_nonneg v))
  intro w
  exact abs_fderiv_normRpowHessian_apply_le hr hx u v w

/-- The norm of the first derivative tensor of a radial power. -/
theorem norm_iteratedFDeriv_one_norm_rpow {r : ℝ} (hr : 1 < r) (x : E) :
    ‖iteratedFDeriv ℝ 1 (fun z : E ↦ ‖z‖ ^ r) x‖ = r * ‖x‖ ^ (r - 1) := by
  rw [norm_iteratedFDeriv_one, norm_fderiv_norm_id_rpow x hr]

/-- The sharp second derivative tensor bound for a radial power. -/
theorem norm_iteratedFDeriv_two_norm_rpow_le {r : ℝ} (hr : 2 < r) (x : E) :
    ‖iteratedFDeriv ℝ 2 (fun z : E ↦ ‖z‖ ^ r) x‖ ≤
      r * (r - 1) * ‖x‖ ^ (r - 2) := by
  rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one,
    fderiv_fderiv_norm_rpow hr]
  exact norm_normRpowHessian_le hr x

/-- The sharp third derivative tensor bound for a radial power away from the origin. -/
theorem norm_iteratedFDeriv_three_norm_rpow_le {r : ℝ} (hr : 4 ≤ r)
    {x : E} (hx : x ≠ 0) :
    ‖iteratedFDeriv ℝ 3 (fun z : E ↦ ‖z‖ ^ r) x‖ ≤
      r * (r - 1) * (r - 2) * ‖x‖ ^ (r - 3) := by
  rw [← norm_iteratedFDeriv_fderiv (n := 2),
    ← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
  have he : fderiv ℝ (fderiv ℝ (fun z : E ↦ ‖z‖ ^ r)) = normRpowHessian r :=
    funext (fderiv_fderiv_norm_rpow (by linarith : 2 < r))
  rw [he]
  exact norm_fderiv_normRpowHessian_le hr hx

/-- Sharp first derivative bound for the integer regularizing power. -/
theorem norm_iteratedFDeriv_one_norm_pow_le {p : ℕ} (hp : 1 ≤ p) (x : E) :
    ‖iteratedFDeriv ℝ 1 (fun z : E ↦ ‖z‖ ^ (p + 1)) x‖ ≤
      (p + 1 : ℝ) * ‖x‖ ^ p := by
  have hr : (1 : ℝ) < ((p + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < p + 1)
  have h := (norm_iteratedFDeriv_one_norm_rpow (E := E) hr x).le
  have he : ((p + 1 : ℕ) : ℝ) - 1 = (p : ℝ) := by push_cast; ring
  rw [he] at h
  simp only [Real.rpow_natCast] at h
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- Sharp second derivative bound for the integer regularizing power. -/
theorem norm_iteratedFDeriv_two_norm_pow_le {p : ℕ} (hp : 2 ≤ p) (x : E) :
    ‖iteratedFDeriv ℝ 2 (fun z : E ↦ ‖z‖ ^ (p + 1)) x‖ ≤
      (p + 1 : ℝ) * p * ‖x‖ ^ (p - 1) := by
  have hr : (2 : ℝ) < ((p + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 < p + 1)
  have he : ((p + 1 : ℕ) : ℝ) - 2 = ((p - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_add, Nat.cast_one]
    ring
  have hc : ((p + 1 : ℕ) : ℝ) - 1 = (p : ℝ) := by push_cast; ring
  have h := norm_iteratedFDeriv_two_norm_rpow_le (E := E) hr x
  rw [he, hc] at h
  simp only [Real.rpow_natCast] at h
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- Sharp third derivative bound for the integer regularizing power away from zero. -/
theorem norm_iteratedFDeriv_three_norm_pow_le {p : ℕ} (hp : 3 ≤ p)
    {x : E} (hx : x ≠ 0) :
    ‖iteratedFDeriv ℝ 3 (fun z : E ↦ ‖z‖ ^ (p + 1)) x‖ ≤
      (p + 1 : ℝ) * p * (p - 1 : ℝ) * ‖x‖ ^ (p - 2) := by
  have hr : (4 : ℝ) ≤ ((p + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 4 ≤ p + 1)
  have he : ((p + 1 : ℕ) : ℝ) - 3 = ((p - 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 2 ≤ p), Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    ring
  have hc1 : ((p + 1 : ℕ) : ℝ) - 1 = (p : ℝ) := by push_cast; ring
  have hc2 : ((p + 1 : ℕ) : ℝ) - 2 = (p - 1 : ℝ) := by push_cast; ring
  have h := norm_iteratedFDeriv_three_norm_rpow_le (E := E) hr hx
  rw [he, hc1, hc2] at h
  simp only [Real.rpow_natCast] at h
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- Exponents greater than three have zero third derivative at the origin. -/
theorem hasFDerivAt_normRpowHessian_zero {r : ℝ} (hr : 3 < r) :
    HasFDerivAt (normRpowHessian r : E → E →L[ℝ] E →L[ℝ] ℝ)
      (0 : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (0 : E) := by
  have hr2 : 2 < r := by linarith
  apply HasFDerivAt.of_isLittleO
  simp only [normRpowHessian_zero r hr2, sub_zero, zero_apply]
  have hb : (normRpowHessian r : E → E →L[ℝ] E →L[ℝ] ℝ) =O[𝓝 0]
      (fun z : E ↦ r * (r - 1) * ‖z‖ ^ (r - 2)) :=
    IsBigO.of_norm_le (fun z ↦ norm_normRpowHessian_le hr2 z)
  apply hb.trans_isLittleO
  rw [← isLittleO_norm_right]
  have he : (fun z : E ↦ r * (r - 1) * ‖z‖ ^ (r - 2)) =
      (fun z : E ↦ ‖z‖ * (r * (r - 1) * ‖z‖ ^ (r - 3))) := by
    funext z
    rw [show r - 2 = (r - 3) + 1 by ring,
      Real.rpow_add_one' (norm_nonneg z) (by linarith : r - 3 + 1 ≠ 0)]
    ring
  rw [he]
  have hc : ContinuousAt (fun z : E ↦ r * (r - 1) * ‖z‖ ^ (r - 3)) 0 := by
    fun_prop (discharger := positivity)
  have ht : Filter.Tendsto (fun z : E ↦ r * (r - 1) * ‖z‖ ^ (r - 3)) (𝓝 0) (𝓝 0) := by
    simpa [Real.zero_rpow (by linarith : r - 3 ≠ 0)] using hc.tendsto
  simpa using (isBigO_refl (fun z : E ↦ ‖z‖) (𝓝 0)).mul_isLittleO
    ((isLittleO_const_iff (by norm_num : (1 : ℝ) ≠ 0)).mpr ht)

/-- The third derivative tensor of a radial power vanishes at the origin. -/
@[simp] theorem iteratedFDeriv_three_norm_rpow_zero {r : ℝ} (hr : 3 < r) :
    iteratedFDeriv ℝ 3 (fun z : E ↦ ‖z‖ ^ r) 0 = 0 := by
  apply norm_eq_zero.mp
  rw [← norm_iteratedFDeriv_fderiv (n := 2),
    ← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
  have he : fderiv ℝ (fderiv ℝ (fun z : E ↦ ‖z‖ ^ r)) = normRpowHessian r :=
    funext (fderiv_fderiv_norm_rpow (by linarith : 2 < r))
  rw [he, (hasFDerivAt_normRpowHessian_zero hr).fderiv, norm_zero]
