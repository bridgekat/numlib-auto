import Numlib.Analysis.InnerProductSpace.NormPow.Smoothness
import Numlib.Analysis.Calculus.FDeriv.Punctured
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

open scoped Topology

/-!
# Exact scalar absolute-power derivatives

The actual scalar derivatives of a natural absolute power have the exact
falling-factorial magnitude away from zero. Below the degree they extend
continuously through zero with zero value. The derivative one order below the
degree has the sharp factorial Lipschitz constant across the origin.
-/

namespace Real

/-- The actual scalar derivative of a natural absolute power on the positive half-line. -/
theorem iteratedDeriv_abs_pow_of_pos (m j : ℕ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv j (fun u : ℝ => |u| ^ m) t =
      (m.descFactorial j : ℝ) * t ^ (m - j) := by
  have he : (fun u : ℝ => |u| ^ m) =ᶠ[𝓝 t] (fun u : ℝ => u ^ m) :=
    Filter.eventually_of_mem (Ioi_mem_nhds ht) fun u hu => by
      change |u| ^ m = u ^ m
      rw [abs_of_pos hu]
  rw [he.iteratedDeriv_eq, iteratedDeriv_pow]

/-- The actual scalar derivative of a natural absolute power on the negative half-line. -/
theorem iteratedDeriv_abs_pow_of_neg (m j : ℕ) {t : ℝ} (ht : t < 0) :
    iteratedDeriv j (fun u : ℝ => |u| ^ m) t =
      (-1 : ℝ) ^ m * (m.descFactorial j : ℝ) * t ^ (m - j) := by
  have he : (fun u : ℝ => |u| ^ m) =ᶠ[𝓝 t]
      (fun u : ℝ => (-1 : ℝ) ^ m * u ^ m) :=
    Filter.eventually_of_mem (Iio_mem_nhds ht) fun u hu => by
      change |u| ^ m = (-1 : ℝ) ^ m * u ^ m
      rw [abs_of_neg hu, neg_pow]
  rw [he.iteratedDeriv_eq, iteratedDeriv_const_mul _ (contDiff_id.pow m).contDiffAt,
    iteratedDeriv_pow]
  ring

/-- Every actual scalar absolute-power derivative has the exact falling-factorial
magnitude at a nonzero point. -/
theorem abs_iteratedDeriv_abs_pow_of_ne_zero (m j : ℕ) {t : ℝ} (ht : t ≠ 0) :
    |iteratedDeriv j (fun u : ℝ => |u| ^ m) t| =
      (m.descFactorial j : ℝ) * |t| ^ (m - j) := by
  obtain ht | ht := lt_or_gt_of_ne ht
  · rw [iteratedDeriv_abs_pow_of_neg m j ht]
    simp [abs_mul, abs_pow]
  · rw [iteratedDeriv_abs_pow_of_pos m j ht]
    simp [abs_mul, abs_pow]

/-- Every actual derivative below the degree of a natural absolute power
vanishes at the origin. -/
theorem iteratedDeriv_abs_pow_zero {m j : ℕ} (hj : j < m) :
    iteratedDeriv j (fun u : ℝ => |u| ^ m) 0 = 0 := by
  have hz := iteratedFDeriv_normRpow_zero_of_lt (E := ℝ)
    (lam := (m : ℝ)) (n := j) (by exact_mod_cast hj)
  have hh := congrArg (fun T : ℝ [×j]→L[ℝ] ℝ => T (fun _ => (1 : ℝ))) hz
  simpa only [Real.rpow_natCast, Real.norm_eq_abs,
    ← iteratedDeriv_eq_iteratedFDeriv, zero_apply] using hh

/-- Below the degree, the exact scalar absolute-power derivative magnitude
is valid also at the origin. -/
theorem abs_iteratedDeriv_abs_pow {m j : ℕ} (hj : j < m) (t : ℝ) :
    |iteratedDeriv j (fun u : ℝ => |u| ^ m) t| =
      (m.descFactorial j : ℝ) * |t| ^ (m - j) := by
  by_cases ht : t = 0
  · subst t
    rw [iteratedDeriv_abs_pow_zero hj]
    simp [Nat.ne_of_gt (Nat.sub_pos_of_lt hj)]
  · exact abs_iteratedDeriv_abs_pow_of_ne_zero m j ht

/-- A natural absolute power is globally finitely smooth through every order
strictly below its degree. -/
theorem contDiff_abs_pow {m j : ℕ} (hj : j < m) :
    ContDiff ℝ j (fun u : ℝ => |u| ^ m) := by
  simpa only [Real.rpow_natCast, Real.norm_eq_abs] using
    contDiff_normRpow_of_nat_lt (E := ℝ) (lam := (m : ℝ)) (n := j)
      (by exact_mod_cast hj)

/-- The actual derivative one order below the degree of a natural absolute
power is globally Lipschitz with the exact degree-factorial constant. -/
theorem abs_sub_iteratedDeriv_abs_pow_le (p : ℕ) (x y : ℝ) :
    |iteratedDeriv p (fun u : ℝ => |u| ^ (p + 1)) x -
      iteratedDeriv p (fun u : ℝ => |u| ^ (p + 1)) y| ≤
        ((p + 1).factorial : ℝ) * |x - y| := by
  let g := iteratedDeriv p (fun u : ℝ => |u| ^ (p + 1))
  have hdesc : (p + 1).descFactorial p = (p + 1).factorial := by
    have hh := Nat.factorial_mul_descFactorial (show p ≤ p + 1 by omega)
    rw [show p + 1 - p = 1 by omega] at hh
    simpa only [Nat.factorial_one, one_mul] using hh
  have hzero : g 0 = 0 := iteratedDeriv_abs_pow_zero (Nat.lt_succ_self p)
  have hg (t : ℝ) : ‖g t - g 0‖ ≤ ((p + 1).factorial : ℝ) * ‖t‖ := by
    rw [hzero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs]
    have hh := abs_iteratedDeriv_abs_pow (Nat.lt_succ_self p) t
    simpa only [g, hdesc, show p + 1 - p = 1 by omega, pow_one] using hh.le
  have hd (t : ℝ) (ht : t ≠ 0) : DifferentiableAt ℝ g t := by
    have hc : ContDiffAt ℝ (p + 1 : ℕ) (fun u : ℝ => |u| ^ (p + 1)) t := by
      simpa only [Real.norm_eq_abs, Real.rpow_natCast] using
        (contDiffOn_normRpow ((p + 1 : ℕ) : ℝ) (p + 1)).contDiffAt
          (isOpen_compl_singleton.mem_nhds ht)
    change DifferentiableAt ℝ (iteratedDeriv p (fun u : ℝ => |u| ^ (p + 1))) t
    rw [iteratedDeriv_eq_equiv_comp]
    exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin p) ℝ).symm.differentiableAt.comp t
      (hc.differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self p))
  have hb (t : ℝ) (ht : t ≠ 0) : ‖fderiv ℝ g t‖ ≤ ((p + 1).factorial : ℝ) := by
    rw [← norm_deriv_eq_norm_fderiv]
    change |deriv (iteratedDeriv p (fun u : ℝ => |u| ^ (p + 1))) t| ≤ _
    rw [← iteratedDeriv_succ]
    have hh := abs_iteratedDeriv_abs_pow_of_ne_zero (p + 1) (p + 1) ht
    simpa only [Nat.descFactorial_self, Nat.sub_self, pow_zero, mul_one] using hh.le
  exact norm_sub_le_of_punctured_fderiv_bound hg hd hb x y

/-- Differentiating the actual scalar jet of an absolute power gives the next
actual scalar jet whenever that next order is below the degree. -/
theorem hasDerivAt_iteratedDeriv_abs_pow {m j : ℕ} (hj : j + 1 < m) (t : ℝ) :
    HasDerivAt (iteratedDeriv j (fun u : ℝ => |u| ^ m))
      (iteratedDeriv (j + 1) (fun u : ℝ => |u| ^ m) t) t := by
  have hc := contDiff_abs_pow hj
  have hd := (hc.differentiable_iteratedDeriv' j t).hasDerivAt
  simpa only [← iteratedDeriv_succ] using hd

end Real
