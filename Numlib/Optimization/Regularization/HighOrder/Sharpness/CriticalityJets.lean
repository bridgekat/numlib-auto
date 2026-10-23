import Numlib.Optimization.Regularization.HighOrder.Sharpness.CriticalityModel
import Numlib.Optimization.HighOrder.Criticality

/-!
# Actual all-order Taylor criticality of monomial sharpness jets

Every lower Taylor degree is constant; the critical degree is a negative
monomial. Its actual supremum over the scalar unit ball is attained at one.
The terminal halving of the prescribed derivative gives the requested target.
-/

namespace HighOrderRegularization.Sharpness
open Set

/-- Every degree of the actual Taylor polynomial has the prescribed single
monomial, with the critical derivative halved at the terminal interpolation node. -/
theorem eval_order_of_matches {f : ℝ → ℝ} {p r N k j : ℕ} {A t : ℝ}
    (hr : 0 < r) (h : MatchesJets f p r N A t) (hk : k ≤ N) (hjp : j ≤ p) (u : ℝ) :
    TaylorModel.eval f j (point t k) u = jet p r N A t k 0 -
      if r ≤ j then ((if k < N then A else A / 2) * t ^ balance p r / r.factorial) * u ^ r
      else 0 := by
  rw [TaylorModel.eval_eq_sum_iteratedDeriv]
  have heq : ∀ i ∈ Finset.range (j + 1),
      u ^ i * iteratedDeriv i f (point t k) / (i.factorial : ℝ) =
      (if i = 0 then jet p r N A t k 0 else 0) -
        (if i = r then
          ((if k < N then A else A / 2) * t ^ balance p r / r.factorial) * u ^ r else 0) := by
    intro i hi
    have hip : i ≤ p := by have := Finset.mem_range.mp hi; omega
    rw [h k hk i hip]
    by_cases hi0 : i = 0
    · subst i
      simp [hr.ne]
    · by_cases hir : i = r
      · subst i
        simp only [jet, ite_eq_right hr.ne', ite_true]
        ring
      · simp only [jet, ite_eq_right hi0, ite_eq_right hir, mul_zero, zero_div, sub_zero]
  calc _ = ∑ i ∈ Finset.range (j + 1),
      ((if i = 0 then jet p r N A t k 0 else 0) -
        (if i = r then
          ((if k < N then A else A / 2) * t ^ balance p r / r.factorial) * u ^ r else 0)) :=
        Finset.sum_congr rfl heq
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_iff, Nat.zero_le, ite_true]

/-- The genuine Taylor decrement is exactly the single surviving positive monomial. -/
theorem decrement_order_of_matches {f : ℝ → ℝ} {p r N k j : ℕ} {A t : ℝ}
    (hr : 0 < r) (h : MatchesJets f p r N A t) (hk : k ≤ N) (hjp : j ≤ p) (u : ℝ) :
    TaylorModel.decrement f j (point t k) u =
      if r ≤ j then ((if k < N then A else A / 2) * t ^ balance p r / r.factorial) * u ^ r
      else 0 := by
  rw [TaylorModel.decrement_eq, eval_order_of_matches hr h hk hjp, h.value_eq hk]
  ring

/-- All actual lower-order Taylor criticalities vanish at every interpolation node. -/
theorem criticality_lower_eq_zero {f : ℝ → ℝ} {p r N k j : ℕ} {A t : ℝ}
    (hr : 0 < r) (h : MatchesJets f p r N A t) (hk : k ≤ N) (hjp : j ≤ p)
    (hjr : j < r) {δ : ℝ} (hδ : 0 ≤ δ) :
    TaylorModel.criticality f j (point t k) δ = 0 := by
  apply (TaylorModel.criticality_eq_zero_iff f j (point t k) hδ).mpr
  intro u _
  rw [decrement_order_of_matches hr h hk hjp, ite_eq_right (not_le.mpr hjr)]

/-- The actual critical-order Taylor supremum on the unit ball has its exact
monomial value, including the terminal derivative halving. -/
theorem criticality_order_eq {f : ℝ → ℝ} {p r N k : ℕ} {A t : ℝ}
    (hr : 0 < r) (hrp : r ≤ p) (h : MatchesJets f p r N A t) (hk : k ≤ N)
    (hA : 0 ≤ A) (ht : 0 ≤ t) :
    TaylorModel.criticality f r (point t k) 1 =
      (if k < N then A else A / 2) * t ^ balance p r / r.factorial := by
  let a := (if k < N then A else A / 2) * t ^ balance p r / r.factorial
  have ha : 0 ≤ a := by dsimp [a]; split_ifs <;> positivity
  have hdec : ∀ u, TaylorModel.decrement f r (point t k) u = a * u ^ r := by
    intro u
    rw [decrement_order_of_matches hr h hk hrp, ite_eq_left le_rfl]
  apply le_antisymm
  · obtain ⟨u, hu, heq⟩ := TaylorModel.exists_decrement_eq_criticality f r (point t k)
      (by norm_num : (0 : ℝ) ≤ 1)
    rw [←heq, hdec]
    have hup : u ^ r ≤ 1 := by
      apply (show u ^ r ≤ |u| ^ r by simpa only [abs_pow] using le_abs_self (u ^ r)).trans
      exact pow_le_one₀ (abs_nonneg _) hu
    exact mul_le_of_le_one_right ha hup
  · have hh := TaylorModel.decrement_le_criticality f r (point t k)
      (s := 1) (by norm_num : ‖(1 : ℝ)‖ ≤ 1)
    simpa only [hdec, one_pow, mul_one] using hh

/-- Balanced accuracy scaling gives exact preterminal and terminal criticality. -/
theorem criticality_order_eq_accuracy {f : ℝ → ℝ} {p r N k : ℕ} {ε : ℝ}
    (hr : 0 < r) (hrp : r ≤ p) (hε : 0 ≤ ε)
    (h : MatchesJets f p r N (amplitude p r) (step p r ε)) (hk : k ≤ N) :
    TaylorModel.criticality f r (point (step p r ε) k) 1 =
      (if k < N then 2 * ε else ε) / r.factorial := by
  have ht : 0 ≤ step p r ε :=
    mul_nonneg (scale_pos p r).le (Real.rpow_nonneg hε _)
  rw [criticality_order_eq hr hrp h hk (amplitude_pos p r).le ht]
  have hh := amplitude_step_power (p := p) (r := r) hε
  split_ifs with hkn
  · rw [hh]
  · have he : amplitude p r / 2 * step p r ε ^ balance p r = ε := by nlinarith
    rw [he]

/-- The direction one attains every unit-radius criticality through the
critical order; lower Taylor degrees are constant. -/
theorem decrement_one_eq_criticality {f : ℝ → ℝ} {p r N k j : ℕ} {A t : ℝ}
    (hr : 0 < r) (hrp : r ≤ p) (h : MatchesJets f p r N A t) (hk : k ≤ N)
    (hjr : j ≤ r) (hA : 0 ≤ A) (ht : 0 ≤ t) :
    TaylorModel.decrement f j (point t k) 1 = TaylorModel.criticality f j (point t k) 1 := by
  by_cases hj : j = r
  · subst j
    rw [criticality_order_eq hr hrp h hk hA ht,
      decrement_order_of_matches hr h hk hrp, ite_eq_left le_rfl, one_pow, mul_one]
  · rw [criticality_lower_eq_zero hr h hk (hjr.trans hrp) (lt_of_le_of_ne hjr hj)
      zero_le_one, decrement_order_of_matches hr h hk (hjr.trans hrp),
      ite_eq_right (by omega)]

end HighOrderRegularization.Sharpness
