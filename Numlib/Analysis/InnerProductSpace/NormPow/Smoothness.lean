import Numlib.Analysis.InnerProductSpace.NormPow
import Numlib.Analysis.Calculus.FDeriv.NormGrowth

/-!
# Finite smoothness of real norm powers at the origin

Off-origin operator-norm bounds for each actual derivative imply its zero value
at the origin, by induction and superlinear growth. The same bounds make every
required derivative continuous at the origin. This establishes global finite
smoothness without assuming it for the assembled norm-power function.
-/

open Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual order-`n` derivative of a norm power vanishes at the origin
when its real exponent is strictly greater than `n`. -/
theorem iteratedFDeriv_normRpow_zero_of_lt {lam : ℝ} {n : ℕ} (hn : (n : ℝ) < lam) :
    iteratedFDeriv ℝ n (fun x : E => ‖x‖ ^ lam) 0 = 0 := by
  induction n with
  | zero =>
    apply norm_eq_zero.mp
    have hpos : (0 : ℝ) < lam := by simpa only [Nat.cast_zero] using hn
    simp only [norm_iteratedFDeriv_zero, norm_zero, Real.zero_rpow hpos.ne', norm_zero]
  | succ n ih =>
    have hn' : (n : ℝ) < lam := by push_cast at hn; linarith
    have hzero := ih hn'
    obtain ⟨C, hC, hbound⟩ := exists_norm_iteratedFDeriv_normRpow_le (E := E) lam n
    have hall : ∀ x : E, ‖iteratedFDeriv ℝ n (fun y : E => ‖y‖ ^ lam) x‖ ≤
        C * ‖x‖ ^ (lam - n) := by
      intro x
      by_cases hx : x = 0
      · subst x
        rw [hzero, norm_zero]
        positivity
      · exact hbound x hx
    have hd := hasFDerivAt_zero_of_norm_le_rpow (by push_cast at hn; linarith : 1 < lam - n)
      hall
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hd.fderiv]
    simp only [LinearIsometryEquiv.map_zero]

/-- A real norm power is globally `C^n` on a finite-dimensional real inner
product space whenever its exponent is strictly greater than `n`. -/
theorem contDiff_normRpow_of_nat_lt {lam : ℝ} {n : ℕ} (hn : (n : ℝ) < lam) :
    ContDiff ℝ n (fun x : E => ‖x‖ ^ lam) := by
  apply contDiff_nat_iff_continuous_differentiable.mpr
  constructor
  · intro m hm
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x = 0
    · subst x
      obtain ⟨C, hC, hbound⟩ := exists_norm_iteratedFDeriv_normRpow_le (E := E) lam m
      have hml : (m : ℝ) < lam := lt_of_le_of_lt (by exact_mod_cast hm) hn
      have hzero := iteratedFDeriv_normRpow_zero_of_lt (E := E) hml
      apply continuousAt_zero_of_norm_le_rpow (sub_pos.mpr hml) (C := C)
      intro y
      by_cases hy : y = 0
      · subst y
        rw [hzero, norm_zero]
        positivity
      · exact hbound y hy
    · exact (ContinuousOn.continuousOn_iteratedFDeriv (contDiffOn_normRpow lam m)
        isOpen_compl_singleton le_rfl).continuousAt
          (isOpen_compl_singleton.mem_nhds hx)
  · intro m hm x
    by_cases hx : x = 0
    · subst x
      obtain ⟨C, hC, hbound⟩ := exists_norm_iteratedFDeriv_normRpow_le (E := E) lam m
      have hml : (m : ℝ) < lam := lt_of_lt_of_le (by exact_mod_cast hm) hn.le
      have hzero := iteratedFDeriv_normRpow_zero_of_lt (E := E) hml
      have hmn : (m : ℝ) + 1 ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr hm)
      apply (hasFDerivAt_zero_of_norm_le_rpow (by linarith : 1 < lam - m)
        (C := C) ?_).differentiableAt
      intro y
      by_cases hy : y = 0
      · subst y
        rw [hzero, norm_zero]
        positivity
      · exact hbound y hy
    · exact ((contDiffOn_normRpow lam (m + 1)).contDiffAt
        (isOpen_compl_singleton.mem_nhds hx)).differentiableAt_iteratedFDeriv
          (by exact_mod_cast Nat.lt_succ_self m)
