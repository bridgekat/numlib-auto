import Numlib.Analysis.InnerProductSpace.NormPow.Derivatives

/-!
# Hessians of real norm powers strictly above two

The radial first derivative has a genuine zero derivative at the origin for
every real exponent strictly above two. Away from zero the usual product rule
gives the explicit Hessian. Together these yield the actual curried Hessian
including fractional powers between two and three, and its positivity.
-/

namespace NormPower
open Asymptotics Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Away from zero, differentiation of the radial first derivative needs no exponent restriction. -/
theorem hasFDerivAt_first_of_ne_zero (a : ℝ) {s : E} (hs : s ≠ 0) :
    HasFDerivAt (first a) (second a s) s := by
  let J : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
  have hn := hasFDerivAt_norm_rpow_of_ne_zero hs (a - 2)
  have hh := (hn.smul J.hasFDerivAt).const_smul a
  convert hh using 1
  · funext z
    change (a * ‖z‖ ^ (a - 2)) • innerSL ℝ z = a • (‖z‖ ^ (a - 2) • innerSL ℝ z)
    rw [smul_smul]
  · apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    simp only [second, smul_apply, smul_eq_mul, add_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
    rw [show a - 2 - 2 = a - 4 by ring]
    change a * (‖s‖ ^ (a - 2) * inner ℝ v w +
      (a - 2) * ‖s‖ ^ (a - 4) * (inner ℝ s v * inner ℝ s w)) =
      a * (‖s‖ ^ (a - 2) * inner ℝ v w +
        ((a - 2) * ‖s‖ ^ (a - 4) * inner ℝ s v) * inner ℝ s w)
    ring

/-- The radial first derivative vanishes at the origin, for every exponent. -/
@[simp] theorem first_zero (a : ℝ) : first a (0 : E) = 0 := by simp [first]

/-- Its derivative at zero is zero whenever the original norm power is greater than two. -/
theorem hasFDerivAt_first_zero {a : ℝ} (ha : 2 < a) :
    HasFDerivAt (first a) (0 : E →L[ℝ] E →L[ℝ] ℝ) 0 := by
  have hc : Tendsto (fun z : E => a * ‖z‖ ^ (a - 2)) (nhds 0) (nhds 0) := by
    have hcont : ContinuousAt (fun z : E => a * ‖z‖ ^ (a - 2)) (0 : E) :=
      continuousAt_const.mul
        ((continuousAt_id : ContinuousAt (fun z : E => z) 0).norm.rpow_const
          (Or.inr (by linarith : 0 ≤ a - 2)))
    have hh := hcont.tendsto
    simpa only [norm_zero, Real.zero_rpow (by linarith : a - 2 ≠ 0), mul_zero] using hh
  have hs : (fun z : E => a * ‖z‖ ^ (a - 2)) =o[nhds 0] (fun _ : E => (1 : ℝ)) :=
    (isLittleO_const_iff (by norm_num : (1 : ℝ) ≠ 0)).mpr hc
  have hJ : (fun z : E => innerSL ℝ z) =O[nhds 0] (fun z : E => z) := by
    apply IsBigO.of_bound 1
    exact Eventually.of_forall (fun z => by simp only [innerSL_apply_norm, one_mul, le_refl])
  have hh := hs.smul_isBigO hJ
  have ho : (fun z : E => first a z) =o[nhds 0] (fun z : E => z) := by
    simpa only [one_smul, first] using hh
  apply HasFDerivAt.of_isLittleO
  simpa only [first_zero, zero_apply, sub_zero] using ho

/-- The explicit Hessian is zero at the origin for every exponent strictly above two. -/
theorem second_zero_of_two_lt {a : ℝ} (ha : 2 < a) : second a (0 : E) = 0 := by
  ext v w
  rw [second_apply]
  simp [Real.zero_rpow (by linarith : a - 2 ≠ 0)]

/-- The radial derivative is differentiable with the actual Hessian for all exponents above two. -/
theorem hasFDerivAt_first_of_two_lt {a : ℝ} (ha : 2 < a) (s : E) :
    HasFDerivAt (first a) (second a s) s := by
  by_cases hs : s = 0
  · subst s
    rw [second_zero_of_two_lt ha]
    exact hasFDerivAt_first_zero ha
  · exact hasFDerivAt_first_of_ne_zero a hs

/-- The actual curried Hessian of a norm power, including the origin and powers in `(2,3]`. -/
theorem fderiv_fderiv_normPower_of_two_lt {a : ℝ} (ha : 2 < a) (s : E) :
    fderiv ℝ (fderiv ℝ (fun z : E => ‖z‖ ^ a)) s = second a s := by
  have heq : fderiv ℝ (fun z : E => ‖z‖ ^ a) = first a :=
    funext (fun z => (hasFDerivAt_normPower (by linarith : 1 < a) z).fderiv)
  rw [heq]
  exact (hasFDerivAt_first_of_two_lt ha s).fderiv

/-- The actual radial Hessian is positive semidefinite for every exponent above two. -/
theorem second_self_nonneg_of_two_lt {a : ℝ} (ha : 2 < a) (s v : E) :
    0 ≤ second a s v v := by
  rw [second_apply, real_inner_self_eq_norm_sq]
  have ha0 : 0 ≤ a := by linarith
  have ha2 : 0 ≤ a - 2 := by linarith
  convert mul_nonneg ha0 (add_nonneg
    (mul_nonneg (Real.rpow_nonneg (norm_nonneg s) (a - 2)) (sq_nonneg ‖v‖))
    (mul_nonneg (mul_nonneg ha2 (Real.rpow_nonneg (norm_nonneg s) (a - 4)))
      (sq_nonneg (inner ℝ s v)))) using 1
  ring

end NormPower
