import Numlib.Optimization.TaylorCriticalityCriteria

/-!
# Taylor gaps at local minima

The first two Taylor gaps vanish on every ball. Higher-order gaps at a smooth local minimum
are smaller than any prescribed positive scaled tolerance on a sufficiently small ball.
Each order can have its own radius, with unit radii for the first two orders.
-/

noncomputable section
open scoped Nat
open Set Metric
namespace Optimization.TaylorCriticality
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- At a smooth local minimum the first two actual Taylor gaps vanish at every positive radius. -/
theorem gapOn_taylorDecrement_eq_zero_of_isLocalMin {f : E → ℝ} {x : E} {j : ℕ}
    (hj : j = 1 ∨ j = 2) (hf : ContDiff ℝ j f) (hmin : IsLocalMin f x)
    {δ : ℝ} (hδ : 0 < δ) :
    gapOn (taylorDecrement f j x) (closedBall 0 δ) = 0 := by
  rcases hj with rfl | rfl
  · apply (gapOn_eq_zero_iff (isCompact_closedBall 0 δ)
      (continuous_taylorDecrement f 1 x).continuousOn
      (by simpa using hδ.le) (taylorDecrement_zero f 1 x)).mpr
    intro d _
    simp [taylorDecrement_one, hmin.fderiv_eq_zero]
  · apply (gapOn_taylorDecrement_two_eq_zero_iff hf.contDiffAt hδ).mpr
    refine ⟨hmin.fderiv_eq_zero, ?_⟩
    intro d
    have hf' : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
    exact Descent.nonneg_apply_apply_of_isLocalMin hmin
      (Filter.Eventually.of_forall fun y => (hf.differentiable (by norm_num) y).hasFDerivAt)
      (hf'.differentiable (by norm_num) x).hasFDerivAt d

/-- A smooth local minimum admits a positive radius at each requested order. The first two
radii may be one, while all gaps have their prescribed factorial-scaled tolerances. -/
theorem exists_radii_taylorDecrement_le_of_isLocalMin {f : E → ℝ} {x : E} {p q : ℕ}
    (hqp : q ≤ p) (hf : ContDiff ℝ p f) (hmin : IsLocalMin f x)
    (ε : ℕ → ℝ) (hε : ∀ j, 1 ≤ j → j ≤ q → 0 < ε j) :
    ∃ δ : ℕ → ℝ, (∀ j, 1 ≤ j → j ≤ q → 0 < δ j ∧ δ j ≤ 1) ∧
      (∀ j, 1 ≤ j → j ≤ q → j ≤ 2 → δ j = 1) ∧
      ∀ j, 1 ≤ j → j ≤ q →
        gapOn (taylorDecrement f j x) (closedBall 0 (δ j)) ≤ ε j * δ j ^ j / (j ! : ℝ) := by
  classical
  have hex : ∀ j : ℕ, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      (1 ≤ j → j ≤ q → j ≤ 2 → δ = 1) ∧
      (1 ≤ j → j ≤ q →
        gapOn (taylorDecrement f j x) (closedBall 0 δ) ≤ ε j * δ ^ j / (j ! : ℝ)) := by
    intro j
    by_cases hj : 1 ≤ j ∧ j ≤ q
    · have hfj : ContDiff ℝ j f := hf.of_le (by exact_mod_cast (hj.2.trans hqp))
      by_cases hlow : j ≤ 2
      · refine ⟨1, by norm_num, le_rfl, fun _ _ _ => rfl, ?_⟩
        intro _ _
        rw [gapOn_taylorDecrement_eq_zero_of_isLocalMin
          (by omega : j = 1 ∨ j = 2) hfj hmin (by norm_num)]
        exact div_nonneg (mul_nonneg (hε j hj.1 hj.2).le (by positivity)) (by positivity)
      · obtain ⟨r, hr, hb⟩ := exists_gapOn_taylorDecrement_le_pow hj.1 hfj.contDiffAt hmin
          (div_pos (hε j hj.1 hj.2) (by positivity : (0 : ℝ) < (j ! : ℝ)))
        refine ⟨min 1 (r / 2), lt_min (by norm_num) (by positivity), min_le_left _ _,
          fun _ _ h => (hlow h).elim, ?_⟩
        intro _ _
        have hd : 0 ≤ min 1 (r / 2) := (lt_min (by norm_num) (by positivity)).le
        have hlt : min 1 (r / 2) < r := (min_le_right _ _).trans_lt (by linarith)
        simpa only [div_mul_eq_mul_div] using hb _ hd hlt
    · exact ⟨1, by norm_num, le_rfl, fun _ _ _ => rfl,
        fun h1 hq => (hj ⟨h1, hq⟩).elim⟩
  choose δ hδ using hex
  exact ⟨δ, fun j _ _ => ⟨(hδ j).1, (hδ j).2.1⟩,
    fun j hj hjq hlow => (hδ j).2.2.1 hj hjq hlow,
    fun j hj hjq => (hδ j).2.2.2 hj hjq⟩

end Optimization.TaylorCriticality
