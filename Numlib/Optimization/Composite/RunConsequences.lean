import Numlib.Optimization.Composite.Run

/-!
# Decrease and parameter bounds for actual composite executions

The strict actual model improvement makes the ratio denominator positive.
Actual accepted point updates give composite objective decrease; rejected
updates preserve the objective. Sharp value remainders derive very successful
acceptance and the uniform regularization bound.
-/

namespace Composite
open InexactTrustRegion
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
namespace Run
variable {p q : ℕ} {f : E → ℝ} {c : E → F} {h : F → ℝ}
  {P : Settings p q} {ε : Fin q → ℝ} {D : ExecutionData E q} {N : ℕ}

/-- Every continuing trial has a strict norm-power composite prediction floor. -/
theorem model_decrease (hr : Run f c h P ε D N) {k : ℕ} (hk : k < N) :
    D.parameter k / ((p + 1).factorial : ℝ) * ‖D.step k‖ ^ (p + 1) <
      decrement f c h p (D.point k) (D.step k) :=
  ModelDecrease.penalty_lt_decrement _ _ _ _ (hr.modelTrace.improvement k hk)

/-- Every actual continued-trial ratio has a strictly positive denominator. -/
theorem denominator_pos (hr : Run f c h P ε D N) {k : ℕ} (hk : k < N) :
    0 < decrement f c h p (D.point k) (D.step k) := by
  have hσ := hr.modelTrace.updates.pos hk.le
  exact lt_of_le_of_lt (by positivity) (hr.model_decrease hk)

/-- A successful actual ratio and point update give the composite objective
norm-power decrease, including the fixed positive minimum parameter. -/
theorem successful_decrease (hr : Run f c h P ε D N) {k : ℕ} (hk : k < N)
    (ha : P.eta1 ≤ D.ratio k) :
    P.eta1 * P.sigmaMin / ((p + 1).factorial : ℝ) * ‖D.step k‖ ^ (p + 1) ≤
      f (D.point k) + h (c (D.point k)) -
        (f (D.point (k + 1)) + h (c (D.point (k + 1)))) := by
  have hratio := ha
  rw [hr.modelTrace.ratio k hk] at hratio
  have hdrop := (le_div_iff₀ (hr.denominator_pos hk)).mp hratio
  have hmin := hr.modelTrace.updates.min_le hk.le
  have hscale := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hmin (Nat.cast_nonneg (p + 1).factorial))
    (pow_nonneg (norm_nonneg (D.step k)) (p + 1))
  have hb := mul_le_mul_of_nonneg_left (hscale.trans (hr.model_decrease hk).le)
    P.eta1_pos.le
  rw [hr.point_update k hk, ite_eq_left ha]
  apply le_trans _ hdrop
  convert hb using 1
  ring

/-- Rejected actual point updates preserve the composite objective exactly. -/
theorem objective_eq_of_unsuccessful (hr : Run f c h P ε D N) {k : ℕ} (hk : k < N)
    (ha : ¬P.eta1 ≤ D.ratio k) :
    f (D.point (k + 1)) + h (c (D.point (k + 1))) =
      f (D.point k) + h (c (D.point k)) := by
  rw [hr.point_update k hk, ite_eq_right ha]

/-- The actual composite objective never increases during continuing trials. -/
theorem objective_mono (hr : Run f c h P ε D N) {k : ℕ} (hk : k < N) :
    f (D.point (k + 1)) + h (c (D.point (k + 1))) ≤
      f (D.point k) + h (c (D.point k)) := by
  by_cases ha : P.eta1 ≤ D.ratio k
  · have hh := hr.successful_decrease hk ha
    have hb : 0 ≤ P.eta1 * P.sigmaMin / ((p + 1).factorial : ℝ) *
        ‖D.step k‖ ^ (p + 1) :=
      mul_nonneg (div_nonneg (mul_nonneg P.eta1_pos.le P.sigmaMin_pos.le)
        (Nat.cast_nonneg _)) (pow_nonneg (norm_nonneg _) _)
    linarith
  · exact (hr.objective_eq_of_unsuccessful hk ha).le

/-- The sharp genuine composite remainder makes a sufficiently large parameter
very successful. This uses actual ratios rather than an acceptance assumption. -/
theorem very_successful (hr : Run f c h P ε D N)
    (hf : ContDiff ℝ p f) (hc : ContDiff ℝ p c) {Lf Lc : ℝ} {K : NNReal}
    (hLf : 0 ≤ Lf) (hLc : 0 ≤ Lc) (hh : LipschitzWith K h)
    (hlipf : ∀ u v,
      ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ Lf * ‖u - v‖)
    (hlipc : ∀ u v,
      ‖iteratedFDeriv ℝ p c u - iteratedFDeriv ℝ p c v‖ ≤ Lc * ‖u - v‖)
    {k : ℕ} (hk : k < N)
    (hlarge : (Lf + (K : ℝ) * Lc) / (1 - P.eta2) ≤ D.parameter k) :
    P.eta2 ≤ D.ratio k := by
  have hη : 0 < 1 - P.eta2 := sub_pos.mpr P.eta2_lt_one
  have hp : 0 < p := P.order_pos.trans_le P.order_le
  have herr := abs_sub_taylorModel_le_lipschitz hp hf hc hLf hLc hlipf hlipc hh
    (D.point k) (D.step k)
  have hd := mul_le_mul_of_nonneg_left (hr.model_decrease hk).le hη.le
  have hm := mul_le_mul_of_nonneg_right ((div_le_iff₀ hη).mp hlarge)
    (show 0 ≤ ‖D.step k‖ ^ (p + 1) / ((p + 1).factorial : ℝ) by positivity)
  have he : f (D.point k + D.step k) + h (c (D.point k + D.step k)) -
      taylorModel f c h p (D.point k) (D.step k) ≤
      (1 - P.eta2) * decrement f c h p (D.point k) (D.step k) := by
    calc
      _ ≤ (Lf + (K : ℝ) * Lc) * ‖D.step k‖ ^ (p + 1) / (p + 1).factorial :=
        (abs_le.mp herr).2
      _ ≤ D.parameter k * (1 - P.eta2) * ‖D.step k‖ ^ (p + 1) /
          (p + 1).factorial := by convert hm using 1 <;> ring
      _ ≤ _ := by convert hd using 1; ring
  rw [hr.modelTrace.ratio k hk]
  apply (le_div_iff₀ (hr.denominator_pos hk)).mpr
  rw [decrement_eq] at he ⊢
  linarith

/-- Exact three-case updates and actual value remainders derive the fixed
parameter cap at every index, including the endpoint. -/
theorem parameter_le (hr : Run f c h P ε D N)
    (hf : ContDiff ℝ p f) (hc : ContDiff ℝ p c) {Lf Lc : ℝ} {K : NNReal}
    (hLf : 0 ≤ Lf) (hLc : 0 ≤ Lc) (hh : LipschitzWith K h)
    (hlipf : ∀ u v,
      ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ Lf * ‖u - v‖)
    (hlipc : ∀ u v,
      ‖iteratedFDeriv ℝ p c u - iteratedFDeriv ℝ p c v‖ ≤ Lc * ‖u - v‖)
    {k : ℕ} (hk : k ≤ N) :
    D.parameter k ≤ max P.sigmaInitial
      (P.gamma3 * (Lf + (K : ℝ) * Lc) / (1 - P.eta2)) := by
  have hb := hr.modelTrace.updates.le_max_initial_threshold
    (fun j hj hlarge => hr.very_successful hf hc hLf hLc hh hlipf hlipc hj hlarge) hk
  simpa only [hr.initial_parameter, mul_div_assoc] using hb

/-- Failure of a true target forces a true generalized criticality failure;
a computed failing direction alone is not used as this premise. -/
theorem not_optimality_of_not_target (hr : Run f c h P ε D N) {k : ℕ} (hk : k ≤ N)
    (hn : ¬TargetAt f c h P ε D k) :
    ¬∀ a, criticality f c h (modelOrder a) (D.point k) (D.radius k a) ≤
      ε a * D.radius k a ^ modelOrder a / (modelOrder a).factorial := by
  intro ha
  exact hn (Or.inl ⟨hr.radius_mem hk, ha⟩)

/-- Every true-certificate or literal zero-return target gives actual objective
optimality at some legal radii. The zero-return case uses its genuine global-gap
rule to derive global model minimality, rather than assuming optimality. -/
theorem target_optimality [FiniteDimensional ℝ E] (hr : Run f c h P ε D N)
    {k : ℕ} (hk : k ≤ N) (ht : TargetAt f c h P ε D k)
    (hf : ContDiffAt ℝ p f (D.point k)) (hc : ContDiffAt ℝ p c (D.point k))
    {Df Dc : ℝ} {K : NNReal} (hDf : 0 ≤ Df) (hDc : 0 ≤ Dc)
    (hh : LipschitzWith K h)
    (hAf : ∀ a, 2 ≤ a → a ≤ p → ‖iteratedFDeriv ℝ a f (D.point k)‖ ≤ Df)
    (hAc : ∀ a, 2 ≤ a → a ≤ p → ‖iteratedFDeriv ℝ a c (D.point k)‖ ≤ Dc) :
    ∃ δ : Fin q → ℝ, OptimalityAt f c h ε (D.point k) δ := by
  rcases ht with ht | ⟨hsel, hzero⟩
  · exact ⟨D.radius k, ht⟩
  · have ho := hr.step_two k hk hsel
    have hfailed : ∃ a, P.zeta * ε a * D.radius k a ^ (a.val + 1) /
        (a.val + 1).factorial <
          decrement f c h (a.val + 1) (D.point k) (D.direction k a) := by
      cases he : D.selected k with
      | none => exact (hsel he).elim
      | some a => exact ⟨a, (hr.check k hk).failed a he⟩
    exact (zero_step_termination P.order_le hf hc hDf hDc
      (hr.modelTrace.updates.pos hk) ho.fraction_pos P.zeta_pos hh hAf hAc
      ho.global_gap hzero ε (D.radius k) hr.accuracy_pos
      (fun a => (hr.radius_mem hk a).1) (D.direction k)
      (hr.check k hk).feasible hfailed).2

end Run
end Composite
