import Numlib.Analysis.InnerProductSpace.NormPow.Second
import Numlib.Analysis.InnerProductSpace.BilinearNorm
import Numlib.Analysis.Calculus.FDeriv.Punctured

/-!
# Sharp derivatives of the cubic norm power

The actual cubic Hessian has a radial formula. Its repeated-unit-direction
values have derivatives of norm at most six away from zero and linear growth
with the same constant. A sharp punctured mean-value estimate and symmetric
bilinear polarization give the global Hessian Lipschitz estimate, including
segments through zero. The derivative norm bounds use the full operator norm.
-/

namespace NormPower
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual cubic norm Hessian on a repeated direction has this radial formula,
including at the origin. -/
theorem cubic_second_diagonal (s v : E) : second 3 s v v =
    3 * (‖s‖ * ‖v‖ ^ 2 + ‖s‖⁻¹ * (inner ℝ s v) ^ 2) := by
  rw [second_apply, real_inner_self_eq_norm_sq]
  norm_num [Real.rpow_neg_one]
  ring

/-- The vector defining the derivative of a unit-direction Hessian diagonal
has norm at most two. -/
theorem norm_cubic_diagonal_gradient_le {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖(1 - (inner ℝ u v) ^ 2) • u + (2 * inner ℝ u v) • v‖ ≤ 2 := by
  have hiu : inner ℝ u u = 1 := by simp [hu]
  have hiv : inner ℝ v v = 1 := by simp [hv]
  have hid : ‖(1 - (inner ℝ u v) ^ 2) • u + (2 * inner ℝ u v) • v‖ ^ 2 =
      1 + 6 * (inner ℝ u v) ^ 2 - 3 * (inner ℝ u v) ^ 4 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hiu, hiv, real_inner_comm v u]
    ring
  nlinarith [sq_nonneg ((inner ℝ u v) ^ 2 - 1), norm_nonneg
    ((1 - (inner ℝ u v) ^ 2) • u + (2 * inner ℝ u v) • v)]

/-- The actual derivative of a cubic Hessian diagonal at a nonzero point,
expressed by a norming vector. -/
theorem hasFDerivAt_cubic_second_diagonal {s : E} (hs : s ≠ 0)
    (v : E) (hv : ‖v‖ = 1) :
    HasFDerivAt (fun z : E => second 3 z v v)
      ((3 : ℝ) • innerSL ℝ
        ((1 - (inner ℝ (‖s‖⁻¹ • s) v) ^ 2) • (‖s‖⁻¹ • s) +
        (2 * inner ℝ (‖s‖⁻¹ • s) v) • v)) s := by
  have hn := hasFDerivAt_norm_rpow_of_ne_zero hs (1 : ℝ)
  have hm := hasFDerivAt_norm_rpow_of_ne_zero hs (-1 : ℝ)
  have hi : HasFDerivAt (fun z : E => inner ℝ z v) (innerSL ℝ v) s := by
    convert (innerSL ℝ v).hasFDerivAt using 1
    funext z
    exact (real_inner_comm z v).symm
  have hcalc := ((hn.mul_const (‖v‖ ^ 2)).add (hm.mul (hi.pow 2))).const_mul 3
  have heq : (fun z : E => 3 * (‖z‖ ^ (1 : ℝ) * ‖v‖ ^ 2 +
      ‖z‖ ^ (-1 : ℝ) * (inner ℝ z v) ^ 2)) = (fun z : E => second 3 z v v) := by
    funext z
    rw [second_apply, real_inner_self_eq_norm_sq]
    norm_num
    ring
  simp only [Pi.add_apply, Pi.mul_apply] at hcalc
  rw [heq] at hcalc
  convert hcalc using 1
  ext w
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply,
    inner_add_left, real_inner_smul_left, add_apply]
  norm_num [hv, real_inner_comm v w, Real.rpow_neg_one]
  field_simp
  ring

/-- The actual cubic Hessian on a repeated unit direction has the sharp
linear growth bound with coefficient six. -/
theorem abs_cubic_second_diagonal_le (s v : E) (hv : ‖v‖ = 1) :
    |second 3 s v v| ≤ 6 * ‖s‖ := by
  by_cases hs : s = 0
  · subst s
    simp [second_zero_of_two_lt (by norm_num : (2 : ℝ) < 3)]
  have hr : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have hb : |inner ℝ s v| ≤ ‖s‖ := by
    simpa only [hv, mul_one] using abs_real_inner_le_norm s v
  have hb2 : (inner ℝ s v) ^ 2 ≤ ‖s‖ ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (inner ℝ s v)) hb 2
  rw [cubic_second_diagonal, hv, one_pow, mul_one,
    abs_of_nonneg (by positivity : 0 ≤ 3 * (‖s‖ + ‖s‖⁻¹ * inner ℝ s v ^ 2))]
  have hpow : ‖s‖⁻¹ * ‖s‖ ^ 2 = ‖s‖ := by field_simp
  have hh := mul_le_mul_of_nonneg_left hb2 (inv_nonneg.mpr hr.le)
  rw [hpow] at hh
  linarith

/-- Every unit-direction diagonal of the actual cubic Hessian is globally
Lipschitz with constant six. -/
theorem abs_cubic_second_diagonal_sub_le (x y v : E) (hv : ‖v‖ = 1) :
    |second 3 x v v - second 3 y v v| ≤ 6 * ‖x - y‖ := by
  have hu (s : E) (hs : s ≠ 0) : ‖‖s‖⁻¹ • s‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hs)
  have hd (s : E) (hs : s ≠ 0) := hasFDerivAt_cubic_second_diagonal hs v hv
  have hb (s : E) (hs : s ≠ 0) :
      ‖fderiv ℝ (fun z : E => second 3 z v v) s‖ ≤ 6 := by
    rw [(hd s hs).fderiv, norm_smul, innerSL_apply_norm]
    norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    have hh := norm_cubic_diagonal_gradient_le (hu s hs) hv
    linarith
  have hg (s : E) : ‖second 3 s v v - second 3 (0 : E) v v‖ ≤ 6 * ‖s‖ := by
    simpa only [second_zero_of_two_lt (by norm_num : (2 : ℝ) < 3), zero_apply,
      sub_zero, Real.norm_eq_abs] using abs_cubic_second_diagonal_le s v hv
  exact norm_sub_le_of_punctured_fderiv_bound hg (fun s hs => (hd s hs).differentiableAt)
    hb x y

/-- The actual curried cubic Hessian is globally Lipschitz in operator norm
with the sharp constant six. -/
theorem norm_cubic_second_sub_le (x y : E) :
    ‖second 3 x - second 3 y‖ ≤ 6 * ‖x - y‖ := by
  apply norm_bilinear_le_of_unit_diagonal_bound _ (by positivity)
  · intro v w
    simp only [sub_apply, second_apply]
    rw [real_inner_comm v w]
    ring
  · intro v hv
    simpa only [sub_apply] using abs_cubic_second_diagonal_sub_le x y v hv

/-- The genuine second Fréchet derivative of the cubic norm power is globally
Lipschitz with the exact degree-factorial constant six. -/
theorem norm_sub_iteratedFDeriv_norm_pow_three_le (x y : E) :
    ‖iteratedFDeriv ℝ 2 (fun z : E => ‖z‖ ^ 3) x -
      iteratedFDeriv ℝ 2 (fun z : E => ‖z‖ ^ 3) y‖ ≤ 6 * ‖x - y‖ := by
  have heq : (fun z : E => ‖z‖ ^ 3) = (fun z : E => ‖z‖ ^ (3 : ℝ)) := by
    funext z
    norm_num
  rw [heq]
  have hb := norm_cubic_second_sub_le x y
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  simp only [sub_apply, iteratedFDeriv_two_apply,
    fderiv_fderiv_normPower_of_two_lt (by norm_num : (2 : ℝ) < 3)]
  have hh := ContinuousLinearMap.le_opNorm₂ (second 3 x - second 3 y) (v 0) (v 1)
  calc ‖second 3 x (v 0) (v 1) - second 3 y (v 0) (v 1)‖ ≤
      ‖second 3 x - second 3 y‖ * ‖v 0‖ * ‖v 1‖ := hh
    _ ≤ (6 * ‖x - y‖) * ‖v 0‖ * ‖v 1‖ := by gcongr
    _ = _ := by simp [Fin.prod_univ_succ]; ring

/-- At a nonzero point, the genuine third Fréchet derivative of the cubic
norm power has operator norm at most six. -/
theorem norm_iteratedFDeriv_norm_pow_three_top_le {x : E} (hx : x ≠ 0) :
    ‖iteratedFDeriv ℝ 3 (fun z : E => ‖z‖ ^ 3) x‖ ≤ 6 := by
  have hLip : LipschitzWith 6 (iteratedFDeriv ℝ 2 (fun z : E => ‖z‖ ^ 3)) :=
    lipschitzWith_iff_norm_sub_le.mpr norm_sub_iteratedFDeriv_norm_pow_three_le
  have heq : (fun z : E => ‖z‖ ^ 3) = (fun z : E => ‖z‖ ^ (3 : ℝ)) := by
    funext z
    norm_num
  have hc : ContDiffAt ℝ 3 (fun z : E => ‖z‖ ^ 3) x := by
    rw [heq]
    exact (contDiffOn_normRpow 3 3).contDiffAt (isOpen_compl_singleton.mem_nhds hx)
  have hd := hc.differentiableAt_iteratedFDeriv (m := 2) (by norm_num)
  have hh := hd.hasFDerivAt.le_of_lipschitz hLip
  simpa only [norm_fderiv_iteratedFDeriv, Nat.reduceAdd, NNReal.coe_ofNat] using hh

/-- The actual cubic norm Hessian has operator norm at most six times the
point norm, including at the origin. -/
theorem norm_iteratedFDeriv_norm_pow_three_two_le (x : E) :
    ‖iteratedFDeriv ℝ 2 (fun z : E => ‖z‖ ^ 3) x‖ ≤ 6 * ‖x‖ := by
  have hzero : iteratedFDeriv ℝ 2 (fun z : E => ‖z‖ ^ 3) (0 : E) = 0 := by
    ext v
    have heq : (fun z : E => ‖z‖ ^ 3) = (fun z : E => ‖z‖ ^ (3 : ℝ)) := by
      funext z
      norm_num
    simp [heq, iteratedFDeriv_two_apply,
      fderiv_fderiv_normPower_of_two_lt (by norm_num : (2 : ℝ) < 3),
      second_zero_of_two_lt (by norm_num : (2 : ℝ) < 3)]
  simpa only [hzero, sub_zero] using norm_sub_iteratedFDeriv_norm_pow_three_le x 0

/-- The actual first derivative of the cubic norm power has norm exactly
three times the squared point norm. -/
theorem norm_iteratedFDeriv_norm_pow_three_one (x : E) :
    ‖iteratedFDeriv ℝ 1 (fun z : E => ‖z‖ ^ 3) x‖ = 3 * ‖x‖ ^ 2 := by
  have heq : (fun z : E => ‖z‖ ^ 3) = (fun z : E => ‖z‖ ^ (3 : ℝ)) := by
    funext z
    norm_num
  rw [norm_iteratedFDeriv_one, heq,
    (hasFDerivAt_normPower (by norm_num : (1 : ℝ) < 3) x).fderiv]
  simp only [first, norm_smul, innerSL_apply_norm]
  norm_num [abs_of_nonneg (norm_nonneg x)]
  ring

/-- All derivative orders through three of the cubic norm power satisfy the
sharp falling-factorial operator bound at every nonzero point. -/
theorem norm_iteratedFDeriv_norm_pow_three_le (j : ℕ) (hj : j ≤ 3)
    {x : E} (hx : x ≠ 0) :
    ‖iteratedFDeriv ℝ j (fun z : E => ‖z‖ ^ 3) x‖ ≤
      (Nat.descFactorial 3 j : ℝ) * ‖x‖ ^ (3 - j) := by
  interval_cases j
  · simp [norm_iteratedFDeriv_zero, Nat.descFactorial_zero]
  · simpa [Nat.descFactorial] using (norm_iteratedFDeriv_norm_pow_three_one x).le
  · simpa [Nat.descFactorial] using norm_iteratedFDeriv_norm_pow_three_two_le x
  · simpa [Nat.descFactorial] using norm_iteratedFDeriv_norm_pow_three_top_le hx

end NormPower
