import Numlib.Analysis.Calculus.DerivativeTest
import Mathlib.Topology.Order.Compact

/-!
# A maximum principle for scalar second-order equations

A positive leading coefficient and positive zeroth-order eigenvalue prevent a
positive interior maximum. Compactness then bounds solutions by their endpoint data.
-/

open Set Topology

/-- A solution of a scalar second-order equation with positive leading coefficient
and positive eigenvalue is bounded by any nonnegative upper bound on its endpoints. -/
theorem le_of_second_order_ode {f A B : ℝ → ℝ} {l r c M : ℝ}
    (hlr : l ≤ r) (hc : ContinuousOn f (Icc l r)) (hpos : 0 < c)
    (hA : ∀ x ∈ Ioo l r, 0 < A x)
    (hode : ∀ x ∈ Ioo l r,
      A x * deriv (deriv f) x + B x * deriv f x = c * f x)
    (hl : f l ≤ M) (hr : f r ≤ M) (hM : 0 ≤ M) :
    ∀ x ∈ Icc l r, f x ≤ M := by
  obtain ⟨y, hy, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨l, left_mem_Icc.mpr hlr⟩ hc
  intro x hx
  apply (hmax hx).trans
  by_cases hyl : y = l
  · simpa [hyl] using hl
  by_cases hyr : y = r
  · simpa [hyr] using hr
  have hyi : y ∈ Ioo l r := ⟨lt_of_le_of_ne hy.1 (Ne.symm hyl),
    lt_of_le_of_ne hy.2 hyr⟩
  have hn : Icc l r ∈ 𝓝 y := Icc_mem_nhds hyi.1 hyi.2
  have hm := hmax.isLocalMax hn
  have hd := hm.deriv_eq_zero
  have hdd := hm.deriv_deriv_nonpos (hc.continuousAt hn)
  have he := hode y hyi
  rw [hd, mul_zero, add_zero] at he
  have : c * f y ≤ 0 := by
    rw [← he]
    exact mul_nonpos_of_nonneg_of_nonpos (hA y hyi).le hdd
  have : f y ≤ 0 := by nlinarith
  exact this.trans hM

/-- The absolute value of a solution is bounded by the larger endpoint magnitude
when the leading coefficient and eigenvalue are positive in the interval. -/
theorem abs_le_of_second_order_ode {f A B : ℝ → ℝ} {l r c M : ℝ}
    (hlr : l ≤ r) (hc : ContinuousOn f (Icc l r)) (hpos : 0 < c)
    (hA : ∀ x ∈ Ioo l r, 0 < A x)
    (hode : ∀ x ∈ Ioo l r,
      A x * deriv (deriv f) x + B x * deriv f x = c * f x)
    (hl : |f l| ≤ M) (hr : |f r| ≤ M) :
    ∀ x ∈ Icc l r, |f x| ≤ M := by
  have hM : 0 ≤ M := (abs_nonneg _).trans hl
  have hu := le_of_second_order_ode hlr hc hpos hA hode
    ((le_abs_self _).trans hl) ((le_abs_self _).trans hr) hM
  have hneg : ∀ x ∈ Ioo l r,
      A x * deriv (deriv (-f)) x + B x * deriv (-f) x = c * (-f) x := by
    intro x hx
    simp only [deriv.neg', deriv.fun_neg, Pi.neg_apply]
    linear_combination -(hode x hx)
  have hd := le_of_second_order_ode hlr hc.neg hpos hA hneg
    ((neg_le_abs _).trans hl) ((neg_le_abs _).trans hr) hM
  intro x hx
  exact abs_le.mpr ⟨by simpa only [Pi.neg_apply] using neg_le.mp (hd x hx), hu x hx⟩
