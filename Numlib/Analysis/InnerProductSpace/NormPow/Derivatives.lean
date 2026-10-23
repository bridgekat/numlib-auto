import Numlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic

/-!
# Low derivatives of sufficiently high norm powers

Actual first and second derivatives of a radial norm power admit explicit formulas.
The second derivative has the sharp radial norm bound, and the third derivative
on a repeated unit direction has the corresponding sharp factorial bound.
-/

namespace NormPower
open Asymptotics Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual first derivative of a real norm power. -/
noncomputable def first (a : ℝ) (s : E) : E →L[ℝ] ℝ :=
  (a * ‖s‖ ^ (a - 2)) • innerSL ℝ s

/-- Evaluation of the radial first derivative on a direction. -/
theorem first_apply (a : ℝ) (s v : E) :
    first a s v = a * ‖s‖ ^ (a - 2) * inner ℝ s v := by
  simp only [first, smul_apply, smul_eq_mul, innerSL_apply_apply]

/-- The explicit second derivative, expressed through the inner product and its rank-one square. -/
noncomputable def second (a : ℝ) (s : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  let J : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
  a • (‖s‖ ^ (a - 2) • J +
    ((a - 2) * ‖s‖ ^ (a - 4)) • (innerSL ℝ s).smulRight (innerSL ℝ s))

/-- The actual norm-power derivative has the given radial formula, including zero. -/
theorem hasFDerivAt_normPower {a : ℝ} (ha : 1 < a) (s : E) :
    HasFDerivAt (fun z : E => ‖z‖ ^ a) (first a s) s :=
  hasFDerivAt_norm_rpow s ha

/-- Differentiation of the radial first derivative gives the explicit Hessian globally. -/
theorem hasFDerivAt_first {a : ℝ} (ha : 3 < a) (s : E) :
    HasFDerivAt (first a) (second a s) s := by
  let J : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
  have hn := hasFDerivAt_norm_rpow s (p := a - 2) (by linarith)
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

/-- The actual curried Hessian is exactly the explicit second derivative. -/
theorem fderiv_fderiv_normPower {a : ℝ} (ha : 3 < a) (s : E) :
    fderiv ℝ (fderiv ℝ (fun z : E => ‖z‖ ^ a)) s = second a s := by
  have heq : fderiv ℝ (fun z : E => ‖z‖ ^ a) = first a :=
    funext (fun z => (hasFDerivAt_normPower (by linarith : 1 < a) z).fderiv)
  rw [heq]
  exact (hasFDerivAt_first ha s).fderiv

/-- Evaluation of the radial Hessian on two actual directions. -/
theorem second_apply (a : ℝ) (s v w : E) :
    second a s v w = a * (‖s‖ ^ (a - 2) * inner ℝ v w +
      (a - 2) * ‖s‖ ^ (a - 4) * inner ℝ s v * inner ℝ s w) := by
  simp only [second, smul_apply, add_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  change a * (‖s‖ ^ (a - 2) * inner ℝ v w +
    (a - 2) * ‖s‖ ^ (a - 4) * (inner ℝ s v * inner ℝ s w)) = _
  ring

/-- The Hessian is zero at zero for all real powers strictly greater than three. -/
@[simp] theorem second_zero (a : ℝ) (ha : 3 < a) : second a (0 : E) = 0 := by
  ext v w
  rw [second_apply]
  simp [Real.zero_rpow (by linarith : a - 2 ≠ 0)]

/-- The exact radial Hessian norm bound has coefficient `a(a-1)`. -/
theorem norm_second_le {a : ℝ} (ha : 4 ≤ a) (s : E) :
    ‖second a s‖ ≤ a * (a - 1) * ‖s‖ ^ (a - 2) := by
  by_cases hs : s = 0
  · subst s
    rw [second_zero a (by linarith)]
    simp only [ContinuousLinearMap.opNorm_zero, norm_zero,
      Real.zero_rpow (by linarith : a - 2 ≠ 0), mul_zero, le_refl]
  have hr : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have hpow : ‖s‖ ^ (a - 4) * ‖s‖ ^ 2 = ‖s‖ ^ (a - 2) := by
    rw [←Real.rpow_natCast, ←Real.rpow_add hr]
    congr 1
    norm_num
    ring
  let J : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
  have hJ : ‖J‖ ≤ 1 := norm_innerSL_le ℝ
  have hR : ‖(innerSL ℝ s).smulRight (innerSL ℝ s)‖ = ‖s‖ ^ 2 := by
    rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
    ring
  have houter := ContinuousLinearMap.opNorm_smul_le a
    (‖s‖ ^ (a - 2) • J +
      ((a - 2) * ‖s‖ ^ (a - 4)) • (innerSL ℝ s).smulRight (innerSL ℝ s))
  rw [Real.norm_of_nonneg (by linarith : 0 ≤ a)] at houter
  change ‖a • (‖s‖ ^ (a - 2) • J +
    ((a - 2) * ‖s‖ ^ (a - 4)) • (innerSL ℝ s).smulRight (innerSL ℝ s))‖ ≤ _
  have hA := ContinuousLinearMap.opNorm_smul_le (‖s‖ ^ (a - 2)) J
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg s) _)] at hA
  have hA' : ‖‖s‖ ^ (a - 2) • J‖ ≤ ‖s‖ ^ (a - 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hJ (Real.rpow_nonneg (norm_nonneg s) (a - 2))]
  have hR' := ContinuousLinearMap.opNorm_smul_le ((a - 2) * ‖s‖ ^ (a - 4))
    ((innerSL ℝ s).smulRight (innerSL ℝ s))
  rw [Real.norm_of_nonneg
    (mul_nonneg (by linarith) (Real.rpow_nonneg (norm_nonneg s) _)), hR] at hR'
  have hsum := norm_add_le (‖s‖ ^ (a - 2) • J)
    (((a - 2) * ‖s‖ ^ (a - 4)) • (innerSL ℝ s).smulRight (innerSL ℝ s))
  have he : (a - 2) * ‖s‖ ^ (a - 4) * ‖s‖ ^ 2 = (a - 2) * ‖s‖ ^ (a - 2) := by
    rw [mul_assoc, hpow]
  rw [he] at hR'
  have hsum' : ‖‖s‖ ^ (a - 2) • J +
      ((a - 2) * ‖s‖ ^ (a - 4)) • (innerSL ℝ s).smulRight (innerSL ℝ s)‖ ≤
        (a - 1) * ‖s‖ ^ (a - 2) := by linarith
  nlinarith [houter, mul_le_mul_of_nonneg_left hsum' (by linarith : 0 ≤ a)]

/-- The genuine third derivative on a repeated direction has the radial formula
at every nonzero point. No third derivative is supplied as a hypothesis. -/
theorem iteratedFDeriv_three_apply_of_ne_zero {a : ℝ} (ha : 3 < a)
    {s : E} (hs : s ≠ 0) (v : E) :
    iteratedFDeriv ℝ 3 (fun z : E => ‖z‖ ^ a) s (fun _ => v) =
      a * (3 * (a - 2) * ‖s‖ ^ (a - 4) * inner ℝ s v * inner ℝ v v +
        (a - 2) * (a - 4) * ‖s‖ ^ (a - 6) * (inner ℝ s v) ^ 3) := by
  let f : E → ℝ := fun z => ‖z‖ ^ a
  have hc : ContDiffAt ℝ 3 f s :=
    (contDiffOn_normRpow a 3).contDiffAt (isOpen_compl_singleton.mem_nhds hs)
  have hch : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ f)) s :=
    (hc.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
  have hactual := ((hch.differentiableAt one_ne_zero).hasFDerivAt.clm_apply
    (hasFDerivAt_const v s)).clm_apply (hasFDerivAt_const v s)
  have hn2 := hasFDerivAt_norm_rpow_of_ne_zero hs (a - 2)
  have hn4 := hasFDerivAt_norm_rpow_of_ne_zero hs (a - 4)
  have hi : HasFDerivAt (fun z : E => inner ℝ z v) (innerSL ℝ v) s := by
    convert (innerSL ℝ v).hasFDerivAt using 1
    funext z
    exact (real_inner_comm z v).symm
  have hcalc := ((hn2.mul_const (inner ℝ v v)).add
    ((hn4.mul (hi.pow 2)).const_mul (a - 2))).const_mul a
  have heq : (fun z => fderiv ℝ (fderiv ℝ f) z v v) =
      (fun z => a * (‖z‖ ^ (a - 2) * inner ℝ v v +
        (a - 2) * (‖z‖ ^ (a - 4) * (inner ℝ z v) ^ 2))) := by
    funext z
    rw [fderiv_fderiv_normPower ha, second_apply]
    ring
  simp only [Pi.add_apply, Pi.mul_apply] at hcalc
  rw [←heq] at hcalc
  have hh := congrArg (fun T : E →L[ℝ] ℝ => T v) (hactual.unique hcalc)
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    zero_apply, ContinuousLinearMap.flip_apply,
    smul_apply, smul_eq_mul, innerSL_apply_apply] at hh
  simp only [map_zero, _root_.zero_apply, zero_add,
    nsmul_eq_mul, Nat.reduceSub, pow_one, Nat.cast_ofNat] at hh
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_two_apply]
  change fderiv ℝ (fderiv ℝ (fderiv ℝ f)) s v v v = _
  rw [hh]
  rw [show a - 2 - 2 = a - 4 by ring, show a - 4 - 2 = a - 6 by ring]
  ring

/-- The actual radial Hessian of an integer norm power has derivative zero at zero.
Its order-`p-1` norm bound is strictly higher than one. -/
theorem hasFDerivAt_second_zero {p : ℕ} (hp : 3 ≤ p) :
    HasFDerivAt (second (p + 1 : ℝ)) (0 : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) 0 := by
  have ha : 4 ≤ (p + 1 : ℝ) := by exact_mod_cast (show 4 ≤ p + 1 by omega)
  have he : (p + 1 : ℝ) - 2 = ((p - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
    ring
  have hO : (fun z : E => second (p + 1 : ℝ) z) =O[nhds 0]
      (fun z : E => ‖z‖ ^ (p - 1)) := by
    apply IsBigO.of_bound ((p + 1 : ℝ) * ((p + 1 : ℝ) - 1))
      (Filter.Eventually.of_forall (fun z => ?_))
    simpa only [he, Real.rpow_natCast, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (norm_nonneg z) _)] using norm_second_le ha z
  have ho := hO.trans_isLittleO (isLittleO_norm_pow_id (E' := E) (by omega : 1 < p - 1))
  refine HasFDerivAt.of_isLittleO (𝕜 := ℝ) (f := fun z : E => second (p + 1 : ℝ) z)
    (f' := (0 : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) (x := (0 : E)) ?_
  have heq : (fun z : E => second (p + 1 : ℝ) z - second (p + 1 : ℝ) 0 -
      (0 : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (z - 0)) =
      (fun z : E => second (p + 1 : ℝ) z) := by
    funext z
    rw [second_zero (p + 1 : ℝ) (by linarith : 3 < (p + 1 : ℝ))]
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    simp
  rw [heq]
  simpa only [sub_zero] using ho

/-- The genuine third derivative at the origin is zero for every integer norm
power at least four. -/
theorem iteratedFDeriv_three_zero {p : ℕ} (hp : 3 ≤ p) (v : E) :
    iteratedFDeriv ℝ 3 (fun z : E => ‖z‖ ^ (p + 1 : ℝ)) 0 (fun _ => v) = 0 := by
  have ha : 3 < (p + 1 : ℝ) := by exact_mod_cast (show 3 < p + 1 by omega)
  have heq : fderiv ℝ (fderiv ℝ (fun z : E => ‖z‖ ^ (p + 1 : ℝ))) =
      second (p + 1 : ℝ) := funext (fun s => fderiv_fderiv_normPower ha s)
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_two_apply]
  change fderiv ℝ (fderiv ℝ (fderiv ℝ (fun z : E => ‖z‖ ^ (p + 1 : ℝ)))) 0 v v v = 0
  rw [heq, (hasFDerivAt_second_zero hp).fderiv]
  simp

/-- The sharp third directional bound away from the origin, for real powers at
least four. -/
theorem abs_iteratedFDeriv_three_le_of_ne_zero {a : ℝ} (ha : 4 ≤ a)
    {s v : E} (hs : s ≠ 0) (hv : ‖v‖ = 1) :
    |iteratedFDeriv ℝ 3 (fun z : E => ‖z‖ ^ a) s (fun _ => v)| ≤
      a * (a - 1) * (a - 2) * ‖s‖ ^ (a - 3) := by
  have hr : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have ha0 : 0 ≤ a := by linarith
  have ha2 : 0 ≤ a - 2 := by linarith
  have ha4 : 0 ≤ a - 4 := by linarith
  have hb : |inner ℝ s v| ≤ ‖s‖ := by
    simpa only [hv, mul_one] using abs_real_inner_le_norm s v
  have hp1 : ‖s‖ ^ (a - 4) * ‖s‖ = ‖s‖ ^ (a - 3) := by
    rw [←Real.rpow_add_one hr.ne']
    congr 1
    ring
  have hp3 : ‖s‖ ^ (a - 6) * ‖s‖ ^ 3 = ‖s‖ ^ (a - 3) := by
    rw [←Real.rpow_natCast, ←Real.rpow_add hr]
    congr 1
    norm_num
    ring
  have hA : |3 * (a - 2) * ‖s‖ ^ (a - 4) * inner ℝ s v| ≤
      3 * (a - 2) * ‖s‖ ^ (a - 3) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 3 * (a - 2) * ‖s‖ ^ (a - 4))]
    calc _ ≤ 3 * (a - 2) * ‖s‖ ^ (a - 4) * ‖s‖ :=
           mul_le_mul_of_nonneg_left hb (by positivity)
         _ = _ := by rw [mul_assoc, hp1]
  have hB : |(a - 2) * (a - 4) * ‖s‖ ^ (a - 6) * (inner ℝ s v) ^ 3| ≤
      (a - 2) * (a - 4) * ‖s‖ ^ (a - 3) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (a - 2) * (a - 4) * ‖s‖ ^ (a - 6)),
      abs_pow]
    calc _ ≤ (a - 2) * (a - 4) * ‖s‖ ^ (a - 6) * ‖s‖ ^ 3 :=
           mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hb 3) (by positivity)
         _ = _ := by rw [mul_assoc, hp3]
  rw [iteratedFDeriv_three_apply_of_ne_zero (by linarith : 3 < a) hs v,
    real_inner_self_eq_norm_sq, hv, one_pow, mul_one, abs_mul, abs_of_nonneg ha0]
  have hab := (abs_add_le _ _).trans (add_le_add hA hB)
  calc _ ≤ a * (3 * (a - 2) * ‖s‖ ^ (a - 3) +
      (a - 2) * (a - 4) * ‖s‖ ^ (a - 3)) := mul_le_mul_of_nonneg_left hab ha0
       _ = _ := by ring

/-- The sharp repeated-unit-direction third derivative bound is valid also at
zero for every integer power at least four. -/
theorem abs_iteratedFDeriv_three_norm_pow_le {p : ℕ} (hp : 3 ≤ p)
    (s v : E) (hv : ‖v‖ = 1) :
    |iteratedFDeriv ℝ 3 (fun z : E => ‖z‖ ^ (p + 1)) s (fun _ => v)| ≤
      (p + 1 : ℝ) * p * (p - 1 : ℕ) * ‖s‖ ^ (p - 2) := by
  have ha : 4 ≤ (p + 1 : ℝ) := by exact_mod_cast (show 4 ≤ p + 1 by omega)
  have he : (p + 1 : ℝ) - 3 = ((p - 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 2 ≤ p), Nat.cast_ofNat]
    ring
  by_cases hs : s = 0
  · subst s
    have hz := iteratedFDeriv_three_zero (E := E) hp v
    simp only [show (p + 1 : ℝ) = ((p + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast] at hz
    rw [hz, abs_zero]
    positivity
  · have hh := abs_iteratedFDeriv_three_le_of_ne_zero ha hs hv
    simp only [show (p + 1 : ℝ) = ((p + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast] at hh
    convert hh using 1
    rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
    norm_num only [Nat.cast_add, Nat.cast_one]
    rw [he, Real.rpow_natCast]
    ring

/-- The actual gradient norm of an integer norm power has its exact radial value. -/
theorem norm_fderiv_norm_pow {p : ℕ} (hp : 1 ≤ p) (s : E) :
    ‖fderiv ℝ (fun z : E => ‖z‖ ^ (p + 1)) s‖ = (p + 1 : ℝ) * ‖s‖ ^ p := by
  have ha : 1 < (p + 1 : ℝ) := by exact_mod_cast (show 1 < p + 1 by omega)
  have hh := norm_fderiv_norm_id_rpow s ha
  simp only [show (p + 1 : ℝ) = ((p + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast] at hh
  convert hh using 1
  norm_num only [Nat.cast_add, Nat.cast_one]
  rw [show (p + 1 : ℝ) - 1 = (p : ℝ) by ring, Real.rpow_natCast]

/-- The actual Hessian in a repeated unit direction obeys its sharp radial bound. -/
theorem abs_iteratedFDeriv_two_norm_pow_le {p : ℕ} (hp : 3 ≤ p)
    (s v : E) (hv : ‖v‖ = 1) :
    |iteratedFDeriv ℝ 2 (fun z : E => ‖z‖ ^ (p + 1)) s (fun _ => v)| ≤
      (p + 1 : ℝ) * p * ‖s‖ ^ (p - 1) := by
  have ha : 4 ≤ (p + 1 : ℝ) := by exact_mod_cast (show 4 ≤ p + 1 by omega)
  have ha' : 3 < (p + 1 : ℝ) := by linarith
  have he : (p + 1 : ℝ) - 2 = ((p - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
    ring
  have hfun : (fun z : E => ‖z‖ ^ (p + 1)) = (fun z : E => ‖z‖ ^ (p + 1 : ℝ)) := by
    funext z
    rw [show (p + 1 : ℝ) = ((p + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  rw [hfun, iteratedFDeriv_two_apply, fderiv_fderiv_normPower ha']
  have h1 := (second (p + 1 : ℝ) s v).le_opNorm v
  have h2 := (second (p + 1 : ℝ) s).le_opNorm v
  rw [hv, mul_one, Real.norm_eq_abs] at h1
  rw [hv, mul_one] at h2
  have hh := h1.trans (h2.trans (norm_second_le ha s))
  simpa only [he, Real.rpow_natCast, add_sub_cancel_right] using hh

end NormPower
