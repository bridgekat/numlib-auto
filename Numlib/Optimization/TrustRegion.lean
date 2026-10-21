import Numlib.Optimization.SmoothDescent
import Numlib.Optimization.ParameterUpdates
import Numlib.Optimization.QuadraticSubproblem

/-!
# First-order trust-region complexity

The run interface retains the actual quadratic model, trial objective and interval updates.
No approximation to the objective Hessian is required. A step must be feasible and give at least
the Cauchy decrease on the feasible negative-gradient ray.
-/

noncomputable section
namespace Optimization.TrustRegion
open QuadraticSubproblem

/-- The ordered parameters for three-way trust-region updates. -/
structure Parameters where
  eta1 : ℝ
  eta2 : ℝ
  gamma1 : ℝ
  gamma2 : ℝ
  gamma3 : ℝ
  eta1_pos : 0 < eta1
  eta_le : eta1 ≤ eta2
  eta2_lt_one : eta2 < 1
  gamma1_pos : 0 < gamma1
  gamma_le : gamma1 ≤ gamma2
  gamma2_lt_one : gamma2 < 1
  one_lt_gamma3 : 1 < gamma3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual reduction divided by predicted quadratic reduction. The totalized value at zero
predicted reduction is immaterial before a positive gradient tolerance is reached. -/
def ratio (f : E → ℝ) (g : E) (H : E →L[ℝ] E) (x s : E) : ℝ :=
  (f x - f (x + s)) / (quadratic g H 0 - quadratic g H s)

/-- A lawful trace with positive initial radius, feasible Cauchy-dominating trial steps,
acceptance using the objective, and all three radius update intervals. -/
structure IsRun (p : Parameters) (f : E → ℝ) (g : E → E)
    (H : ℕ → E →L[ℝ] E) (x s : ℕ → E) (delta : ℕ → ℝ) : Prop where
  initial_pos : 0 < delta 0
  feasible : ∀ k, ‖s k‖ ≤ delta k
  cauchy : ∀ k t, 0 ≤ t → t * ‖g (x k)‖ ≤ delta k →
    quadratic (g (x k)) (H k) (s k) ≤ quadratic (g (x k)) (H k) (-(t • g (x k)))
  iterate : ∀ k, x (k + 1) = if p.eta1 ≤ ratio f (g (x k)) (H k) (x k) (s k)
    then x k + s k else x k
  update : ∀ k, if p.eta2 ≤ ratio f (g (x k)) (H k) (x k) (s k)
    then delta (k + 1) ∈ Set.Icc (delta k) (p.gamma3 * delta k)
    else if p.eta1 ≤ ratio f (g (x k)) (H k) (x k) (s k)
    then delta (k + 1) ∈ Set.Icc (p.gamma2 * delta k) (delta k)
    else delta (k + 1) ∈ Set.Icc (p.gamma1 * delta k) (p.gamma2 * delta k)

variable {p : Parameters} {f : E → ℝ} {g : E → E} {H : ℕ → E →L[ℝ] E}
    {x s : ℕ → E} {delta : ℕ → ℝ}

/-- Every update retains at least the smallest permitted contraction factor. -/
theorem IsRun.radius_update_lower (h : IsRun p f g H x s delta) (k : ℕ)
    (hk : 0 ≤ delta k) : p.gamma1 * delta k ≤ delta (k + 1) := by
  have hu := h.update k
  split_ifs at hu
  · exact (mul_le_of_le_one_left hk (p.gamma_le.trans p.gamma2_lt_one.le)).trans hu.1
  · exact (mul_le_mul_of_nonneg_right p.gamma_le hk).trans hu.1
  · exact hu.1

/-- Radius positivity follows from initialization and the update intervals. -/
theorem IsRun.radius_pos (h : IsRun p f g H x s delta) (k : ℕ) : 0 < delta k := by
  induction k with
  | zero => exact h.initial_pos
  | succ k ih => exact (mul_pos p.gamma1_pos ih).trans_le (h.radius_update_lower k ih.le)

/-- Cauchy-dominating steps have the standard explicit model decrease. -/
theorem IsRun.predicted_decrease (h : IsRun p f g H x s delta) (k : ℕ) :
    (1 / 2 : ℝ) * ‖g (x k)‖ * min (‖g (x k)‖ / (1 + ‖H k‖)) (delta k) ≤
      quadratic (g (x k)) (H k) 0 - quadratic (g (x k)) (H k) (s k) :=
  cauchy_decrease _ _ (h.radius_pos k).le (h.cauchy k)

/-- Predicted reduction is always nonnegative. -/
theorem IsRun.predicted_nonneg (h : IsRun p f g H x s delta) (k : ℕ) :
    0 ≤ quadratic (g (x k)) (H k) 0 - quadratic (g (x k)) (H k) (s k) := by
  have hc := h.cauchy k 0 le_rfl (by simpa using (h.radius_pos k).le)
  simpa using sub_nonneg.mpr hc

/-- A nonzero gradient makes the predicted reduction strictly positive. -/
theorem IsRun.predicted_pos (h : IsRun p f g H x s delta) (k : ℕ) (hg : g (x k) ≠ 0) :
    0 < quadratic (g (x k)) (H k) 0 - quadratic (g (x k)) (H k) (s k) :=
  cauchy_decrease_pos _ (h.radius_pos k) hg (h.cauchy k)

/-- An accepted trial realizes its guaranteed fraction of the predicted reduction. -/
theorem IsRun.accepted_decrease (h : IsRun p f g H x s delta) (k : ℕ)
    (hk : p.eta1 ≤ ratio f (g (x k)) (H k) (x k) (s k)) :
    p.eta1 * (quadratic (g (x k)) (H k) 0 - quadratic (g (x k)) (H k) (s k)) ≤
      f (x k) - f (x (k + 1)) := by
  rw [h.iterate k, ite_eq_left hk]
  have hp := h.predicted_nonneg k
  by_cases hz : quadratic (g (x k)) (H k) 0 - quadratic (g (x k)) (H k) (s k) = 0
  · change p.eta1 ≤ (f (x k) - f (x k + s k)) / _ at hk
    rw [hz, div_zero] at hk
    exact (not_le_of_gt p.eta1_pos hk).elim
  · exact (le_div_iff₀ (lt_of_le_of_ne hp (Ne.symm hz))).mp hk

/-- The objective values cannot increase. -/
theorem IsRun.objective_nonincrease (h : IsRun p f g H x s delta) (k : ℕ) :
    f (x (k + 1)) ≤ f (x k) := by
  by_cases hk : p.eta1 ≤ ratio f (g (x k)) (H k) (x k) (s k)
  · have hd := h.accepted_decrease k hk
    have hn := mul_nonneg p.eta1_pos.le (h.predicted_nonneg k)
    linarith
  · rw [h.iterate k, ite_eq_right hk]

/-- Multiplicative radius updates bound the total number of trials. -/
theorem IsRun.total_count_le (h : IsRun p f g H x s delta) (n : ℕ) {m : ℝ}
    (hm : 0 < m) (hmin : m ≤ delta n) :
    (n : ℝ) ≤ (ParameterUpdates.successCount
      (fun k => p.eta1 ≤ ratio f (g (x k)) (H k) (x k) (s k)) n : ℝ) *
      (1 + Real.log p.gamma3 / |Real.log p.gamma2|) +
      Real.log (delta 0 / m) / |Real.log p.gamma2| := by
  apply ParameterUpdates.total_count_le_of_lower_bound h.radius_pos
    (zero_lt_one.trans p.one_lt_gamma3) ⟨p.gamma1_pos.trans_le p.gamma_le, p.gamma2_lt_one⟩
    ?_ ?_ n hm hmin
  · intro k hk
    have hu := h.update k
    split_ifs at hu
    · exact hu.2
    · exact hu.2.trans (le_mul_of_one_le_left (h.radius_pos k).le p.one_lt_gamma3.le)
  · intro k hk
    have hn : ¬p.eta2 ≤ ratio f (g (x k)) (H k) (x k) (s k) :=
      fun h2 => hk (p.eta_le.trans h2)
    have hu := h.update k
    simp only [ite_eq_right hn, ite_eq_right hk] at hu
    exact hu.2

/-- The sharp Lipschitz-gradient remainder bounds the error of any bounded quadratic model. -/
theorem abs_model_error_le {f : E → ℝ} {g : E → E} {L B : ℝ}
    (hf : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) {H : E →L[ℝ] E}
    (hB : ‖H‖ ≤ B) (x s : E) :
    |f (x + s) - (f x + quadratic (g x) H s)| ≤ (L + B) / 2 * ‖s‖ ^ 2 := by
  have ht := Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le
    (convex_univ : Convex ℝ (Set.univ : Set E)) (fun y _ => hf y)
    (x := x) (y := x + s) (Set.mem_univ _) (Set.mem_univ _)
    (fun y _ => by simpa only [← map_sub, innerSL_apply_norm] using hL y x)
  simp only [add_sub_cancel_left, innerSL_apply_apply, Real.norm_eq_abs] at ht
  have hcurv : |inner ℝ s (H s)| ≤ B * ‖s‖ ^ 2 := by
    calc
      |inner ℝ s (H s)| ≤ ‖s‖ * ‖H s‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖s‖ * (‖H‖ * ‖s‖) := mul_le_mul_of_nonneg_left (H.le_opNorm s) (norm_nonneg _)
      _ ≤ B * ‖s‖ ^ 2 := by nlinarith [norm_nonneg s]
  calc
    _ = |(f (x + s) - f x - inner ℝ (g x) s) - (1 / 2 : ℝ) * inner ℝ s (H s)| := by
      congr 1
      simp [quadratic]
      ring
    _ ≤ |f (x + s) - f x - inner ℝ (g x) s| + |(1 / 2 : ℝ) * inner ℝ s (H s)| := abs_sub _ _
    _ ≤ L / 2 * ‖s‖ ^ 2 + (1 / 2 : ℝ) * (B * ‖s‖ ^ 2) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      gcongr
    _ = _ := by ring

/-- A sufficiently small radius guarantees a very successful trial. -/
theorem IsRun.ratio_ge_of_radius_lt (h : IsRun p f g H x s delta) {L B : ℝ}
    (hf : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLp : 1 ≤ L)
    (hB : ∀ k, ‖H k‖ ≤ B) (k : ℕ)
    (hsmall : delta k < (1 - p.eta2) / (2 * (L + B)) * ‖g (x k)‖) :
    p.eta2 ≤ ratio f (g (x k)) (H k) (x k) (s k) := by
  have hBn : 0 ≤ B := (norm_nonneg _).trans (hB k)
  have hsum : 0 < L + B := by linarith
  have heta : 0 < p.eta2 := p.eta1_pos.trans_le p.eta_le
  have hdel := h.radius_pos k
  have hscaled : delta k * (2 * (L + B)) < (1 - p.eta2) * ‖g (x k)‖ := by
    apply (lt_div_iff₀ (by positivity : 0 < 2 * (L + B))).mp
    convert hsmall using 1
    ring
  have hshort : delta k ≤ ‖g (x k)‖ / (1 + ‖H k‖) := by
    apply (le_div_iff₀ (by positivity : 0 < 1 + ‖H k‖)).mpr
    have h1 := mul_le_mul_of_nonneg_left (hB k) hdel.le
    have h2 := mul_nonneg heta.le (norm_nonneg (g (x k)))
    nlinarith
  have hhalf := h.predicted_decrease k
  rw [min_eq_right hshort] at hhalf
  have hg : g (x k) ≠ 0 := by
    intro hz
    simp only [hz, norm_zero, mul_zero] at hsmall
    linarith
  have hp := h.predicted_pos k hg
  change p.eta2 ≤ (f (x k) - f (x k + s k)) /
    (quadratic (g (x k)) (H k) 0 - quadratic (g (x k)) (H k) (s k))
  rw [le_div_iff₀ hp]
  have he := (abs_le.mp (abs_model_error_le hf hL (hB k) (x k) (s k))).2
  have hsquare : ‖s k‖ ^ 2 ≤ delta k ^ 2 := by
    nlinarith [h.feasible k, norm_nonneg (s k)]
  have he' := mul_le_mul_of_nonneg_left hsquare (by positivity : 0 ≤ (L + B) / 2)
  have hh := mul_le_mul_of_nonneg_left hhalf (by linarith [p.eta2_lt_one] : 0 ≤ 1 - p.eta2)
  have hd := mul_le_mul_of_nonneg_right hscaled.le hdel.le
  simp only [quadratic_zero] at *
  nlinarith

/-- Very successful iterations do not contract the radius. -/
theorem IsRun.radius_nondecrease_of_small (h : IsRun p f g H x s delta) {L B : ℝ}
    (hf : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLp : 1 ≤ L)
    (hB : ∀ k, ‖H k‖ ≤ B) (k : ℕ)
    (hsmall : delta k < (1 - p.eta2) / (2 * (L + B)) * ‖g (x k)‖) :
    delta k ≤ delta (k + 1) := by
  have hr := h.ratio_ge_of_radius_lt hf hL hLp hB k hsmall
  have hu := h.update k
  simp only [ite_eq_left hr] at hu
  exact hu.1

/-- Minimum of the first `n+1` scalar values. -/
def runningMin (u : ℕ → ℝ) : ℕ → ℝ
  | 0 => u 0
  | n + 1 => min (runningMin u n) (u (n + 1))

/-- A running minimum is below every value of its prefix. -/
theorem runningMin_le (u : ℕ → ℝ) {n j : ℕ} (hj : j ≤ n) : runningMin u n ≤ u j := by
  induction n with
  | zero => simp [show j = 0 by omega, runningMin]
  | succ n ih =>
    by_cases he : j = n + 1
    · simp [he, runningMin]
    · exact (min_le_left _ _).trans (ih (by omega))

/-- A uniform lower bound on a prefix bounds its running minimum. -/
theorem le_runningMin {u : ℕ → ℝ} {a : ℝ} {n : ℕ} (h : ∀ j ≤ n, a ≤ u j) :
    a ≤ runningMin u n := by
  induction n with
  | zero => exact h 0 le_rfl
  | succ n ih => exact le_min (ih (fun j hj => h j (by omega))) (h _ le_rfl)

/-- Any coefficient compatible with initialization and the small-radius threshold gives a
running-gradient lower bound for the radius. -/
theorem IsRun.radius_lower (h : IsRun p f g H x s delta) {L B c : ℝ}
    (hf : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLp : 1 ≤ L)
    (hB : ∀ k, ‖H k‖ ≤ B) (hc : 0 ≤ c) (hinit : c * ‖g (x 0)‖ ≤ delta 0)
    (hct : c ≤ p.gamma1 * ((1 - p.eta2) / (2 * (L + B)))) (n : ℕ) :
    c * runningMin (fun j => ‖g (x j)‖) n ≤ delta n := by
  induction n with
  | zero => exact hinit
  | succ n ih =>
    by_cases hn : delta n < (1 - p.eta2) / (2 * (L + B)) * ‖g (x n)‖
    · exact (mul_le_mul_of_nonneg_left (min_le_left _ _) hc).trans
        (ih.trans (h.radius_nondecrease_of_small hf hL hLp hB n hn))
    · have hm : 0 ≤ runningMin (fun j => ‖g (x j)‖) (n + 1) :=
        le_runningMin (fun j _ => norm_nonneg _)
      calc
        c * runningMin (fun j => ‖g (x j)‖) (n + 1) ≤
            (p.gamma1 * ((1 - p.eta2) / (2 * (L + B)))) *
              runningMin (fun j => ‖g (x j)‖) (n + 1) :=
          mul_le_mul_of_nonneg_right hct hm
        _ ≤ (p.gamma1 * ((1 - p.eta2) / (2 * (L + B)))) * ‖g (x n)‖ :=
          mul_le_mul_of_nonneg_left (runningMin_le _ (by omega))
            (by positivity [p.gamma1_pos, p.eta2_lt_one,
              (norm_nonneg (H n)).trans (hB n)])
        _ ≤ p.gamma1 * delta n := by
          have hh := mul_le_mul_of_nonneg_left (le_of_not_gt hn) p.gamma1_pos.le
          nlinarith only [hh]
        _ ≤ delta (n + 1) := h.radius_update_lower n (h.radius_pos n).le

/-- The uniform decrease coefficient obtained from a radius coefficient. -/
def decreaseCoefficient (B c : ℝ) : ℝ := (1 / 2 : ℝ) * min (1 / (1 + B)) c

/-- The Cauchy estimate and radius lower bound give a model decrease in terms of the current
and smallest preceding gradient. -/
theorem IsRun.predicted_decrease_of_radius_lower (h : IsRun p f g H x s delta)
    {B c : ℝ} (hB : ∀ k, ‖H k‖ ≤ B) (hc : 0 ≤ c) (n : ℕ)
    (hradius : c * runningMin (fun j => ‖g (x j)‖) n ≤ delta n) :
    decreaseCoefficient B c * ‖g (x n)‖ * runningMin (fun j => ‖g (x j)‖) n ≤
      quadratic (g (x n)) (H n) 0 - quadratic (g (x n)) (H n) (s n) := by
  have hBn : 0 ≤ B := (norm_nonneg _).trans (hB n)
  have hm : 0 ≤ runningMin (fun j => ‖g (x j)‖) n :=
    le_runningMin (fun j _ => norm_nonneg _)
  have hcoef : 0 ≤ min (1 / (1 + B)) c := le_min (by positivity) hc
  have hfirst : min (1 / (1 + B)) c * runningMin (fun j => ‖g (x j)‖) n ≤
      ‖g (x n)‖ / (1 + ‖H n‖) := by
    calc
      _ ≤ (1 / (1 + B)) * ‖g (x n)‖ :=
        mul_le_mul (min_le_left _ _) (runningMin_le _ le_rfl) hm (by positivity)
      _ = ‖g (x n)‖ / (1 + B) := by ring
      _ ≤ _ := div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
        (by linarith [hB n])
  have hsecond := (mul_le_mul_of_nonneg_right (min_le_right (1 / (1 + B)) c) hm).trans hradius
  have hh := mul_le_mul_of_nonneg_left (le_min hfirst hsecond)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (norm_nonneg (g (x n))))
  dsimp [decreaseCoefficient]
  nlinarith only [hh, h.predicted_decrease n]

/-- The radius bound at the endpoint of a prefix only uses gradient tests before that endpoint. -/
theorem IsRun.radius_lower_before_test (h : IsRun p f g H x s delta) {L B c epsilon : ℝ}
    (hf : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLp : 1 ≤ L)
    (hB : ∀ k, ‖H k‖ ≤ B) (hc : 0 ≤ c) (he : 0 ≤ epsilon)
    (hinit : c * epsilon ≤ delta 0)
    (hct : c ≤ p.gamma1 * ((1 - p.eta2) / (2 * (L + B))))
    (n : ℕ) (htest : ∀ j < n, epsilon ≤ ‖g (x j)‖) : c * epsilon ≤ delta n := by
  induction n with
  | zero => exact hinit
  | succ n ih =>
    have hi := ih (fun j hj => htest j (by omega))
    by_cases hn : delta n < (1 - p.eta2) / (2 * (L + B)) * ‖g (x n)‖
    · exact hi.trans (h.radius_nondecrease_of_small hf hL hLp hB n hn)
    · calc
        c * epsilon ≤ (p.gamma1 * ((1 - p.eta2) / (2 * (L + B)))) * ‖g (x n)‖ :=
          mul_le_mul hct (htest n (by omega)) he (hc.trans hct)
        _ ≤ p.gamma1 * delta n := by
          have hh := mul_le_mul_of_nonneg_left (le_of_not_gt hn) p.gamma1_pos.le
          nlinarith only [hh]
        _ ≤ _ := h.radius_update_lower n (h.radius_pos n).le

/-- Positive radius coefficients give positive uniform decrease coefficients. -/
theorem decreaseCoefficient_pos {B c : ℝ} (hB : 0 ≤ B) (hc : 0 < c) :
    0 < decreaseCoefficient B c := by
  dsimp [decreaseCoefficient]
  exact mul_pos (by norm_num) (lt_min (by positivity) hc)

/-- Accepted steps before termination consume a fixed positive amount of objective gap. -/
theorem IsRun.success_count_le (h : IsRun p f g H x s delta) {L B c low epsilon : ℝ}
    (hf : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLp : 1 ≤ L)
    (hB : ∀ k, ‖H k‖ ≤ B) (hc : 0 < c) (he : 0 < epsilon)
    (hinit : c * ‖g (x 0)‖ ≤ delta 0)
    (hct : c ≤ p.gamma1 * ((1 - p.eta2) / (2 * (L + B))))
    (n : ℕ) (hlow : low ≤ f (x n)) (htest : ∀ j < n, epsilon < ‖g (x j)‖) :
    (ParameterUpdates.successCount
      (fun k => p.eta1 ≤ ratio f (g (x k)) (H k) (x k) (s k)) n : ℝ) ≤
      (f (x 0) - low) / (p.eta1 * decreaseCoefficient B c * epsilon ^ 2) := by
  classical
  have hD := decreaseCoefficient_pos ((norm_nonneg _).trans (hB 0)) hc
  have hdec : 0 < p.eta1 * decreaseCoefficient B c * epsilon ^ 2 :=
    mul_pos (mul_pos p.eta1_pos hD) (sq_pos_of_pos he)
  apply (le_div_iff₀ hdec).mpr
  unfold ParameterUpdates.successCount
  apply EvaluationComplexity.card_mul_le_gap (u := fun k => f (x k))
    (Finset.filter_subset _ _) hlow (fun k _ => h.objective_nonincrease k)
  intro k hk
  obtain ⟨hkn, hks⟩ := Finset.mem_filter.mp hk
  have hkn' := Finset.mem_range.mp hkn
  have hm : epsilon ≤ runningMin (fun j => ‖g (x j)‖) k :=
    le_runningMin (fun j hj => (htest j (by omega)).le)
  have hg := (htest k hkn').le
  have hprod := mul_le_mul hg hm he.le (norm_nonneg (g (x k)))
  have hpred := h.predicted_decrease_of_radius_lower hB hc.le k
    (h.radius_lower hf hL hLp hB hc.le hinit hct k)
  have hh := mul_le_mul_of_nonneg_left hprod hD.le
  have hh' : decreaseCoefficient B c * epsilon ^ 2 ≤
      quadratic (g (x k)) (H k) 0 - quadratic (g (x k)) (H k) (s k) := by
    nlinarith only [hh, hpred]
  have hh'' := mul_le_mul_of_nonneg_left hh' p.eta1_pos.le
  nlinarith only [hh'', h.accepted_decrease k hks]

/-- Every unterminated prefix has an explicit total trial bound. Absolute logarithms retain
nonnegative bounds even when the initial point already passes a large tolerance. -/
theorem IsRun.prefix_count_le (h : IsRun p f g H x s delta) {L B c low epsilon : ℝ}
    (hf : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLp : 1 ≤ L)
    (hB : ∀ k, ‖H k‖ ≤ B) (hc : 0 < c) (he : 0 < epsilon)
    (hinit : c * ‖g (x 0)‖ ≤ delta 0)
    (hct : c ≤ p.gamma1 * ((1 - p.eta2) / (2 * (L + B))))
    (n : ℕ) (hlow : low ≤ f (x n)) (htest : ∀ j < n, epsilon < ‖g (x j)‖) :
    (n : ℝ) ≤ (f (x 0) - low) / (p.eta1 * decreaseCoefficient B c * epsilon ^ 2) *
      (1 + Real.log p.gamma3 / |Real.log p.gamma2|) +
      (|Real.log (c / delta 0)| + |Real.log epsilon|) / |Real.log p.gamma2| := by
  have hlog2 : 0 < |Real.log p.gamma2| := abs_pos.mpr
    (Real.log_neg (p.gamma1_pos.trans_le p.gamma_le) p.gamma2_lt_one).ne
  have hC : 0 ≤ 1 + Real.log p.gamma3 / |Real.log p.gamma2| :=
    add_nonneg zero_le_one (div_nonneg (Real.log_pos p.one_lt_gamma3).le hlog2.le)
  have hS := h.success_count_le hf hL hLp hB hc he hinit hct n hlow htest
  by_cases hn : n = 0
  · subst n
    have hgap : 0 ≤ f (x 0) - low := sub_nonneg.mpr hlow
    have hD := decreaseCoefficient_pos ((norm_nonneg _).trans (hB 0)) hc
    have hb : 0 ≤ (f (x 0) - low) /
        (p.eta1 * decreaseCoefficient B c * epsilon ^ 2) :=
      div_nonneg hgap (mul_pos (mul_pos p.eta1_pos hD) (sq_pos_of_pos he)).le
    simpa only [Nat.cast_zero] using add_nonneg (mul_nonneg hb hC)
      (div_nonneg (add_nonneg (abs_nonneg (Real.log (c / delta 0)))
        (abs_nonneg (Real.log epsilon))) hlog2.le)
  have hr := h.radius_lower_before_test hf hL hLp hB hc.le he.le
    ((mul_le_mul_of_nonneg_left (htest 0 (Nat.pos_of_ne_zero hn)).le hc.le).trans hinit)
    hct n (fun j hj => (htest j hj).le)
  have ht := h.total_count_le n (mul_pos hc he) hr
  have hlogeq : Real.log (delta 0 / (c * epsilon)) =
      -(Real.log (c / delta 0) + Real.log epsilon) := by
    rw [Real.log_div (h.radius_pos 0).ne' (mul_pos hc he).ne',
      Real.log_mul hc.ne' he.ne', Real.log_div hc.ne' (h.radius_pos 0).ne']
    ring
  have hlogbound : Real.log (delta 0 / (c * epsilon)) ≤
      |Real.log (c / delta 0)| + |Real.log epsilon| := by
    rw [hlogeq]
    linarith only [neg_le_abs (Real.log (c / delta 0)), neg_le_abs (Real.log epsilon)]
  have h1 := mul_le_mul_of_nonneg_right hS hC
  have h2 := div_le_div_of_nonneg_right hlogbound hlog2.le
  linarith only [ht, h1, h2]

/-- First successful gradient test with complete function and gradient oracle budgets. -/
theorem IsRun.exists_stationary_with_cost (h : IsRun p f g H x s delta)
    {L B c low epsilon : ℝ}
    (hf : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLp : 1 ≤ L)
    (hB : ∀ k, ‖H k‖ ≤ B) (hc : 0 < c) (he : 0 < epsilon)
    (hinit : c * ‖g (x 0)‖ ≤ delta 0)
    (hct : c ≤ p.gamma1 * ((1 - p.eta2) / (2 * (L + B))))
    (hlow : ∀ y, low ≤ f y) :
    ∃ K : ℕ, ‖g (x K)‖ ≤ epsilon ∧ (∀ j < K, epsilon < ‖g (x j)‖) ∧
      (K : ℝ) + 1 ≤ (f (x 0) - low) / (p.eta1 * decreaseCoefficient B c * epsilon ^ 2) *
        (1 + Real.log p.gamma3 / |Real.log p.gamma2|) +
        (|Real.log (c / delta 0)| + |Real.log epsilon|) / |Real.log p.gamma2| + 1 ∧
      (ParameterUpdates.successCount
        (fun k => p.eta1 ≤ ratio f (g (x k)) (H k) (x k) (s k)) K : ℝ) + 1 ≤
        (f (x 0) - low) / (p.eta1 * decreaseCoefficient B c * epsilon ^ 2) + 1 := by
  classical
  obtain ⟨K, _, hk, hfirst⟩ := EvaluationComplexity.exists_first_of_prefix_bound
    (P := fun k => ‖g (x k)‖ ≤ epsilon)
    (fun n hn => h.prefix_count_le hf hL hLp hB hc he hinit hct n (hlow _)
      (fun j hj => lt_of_not_ge (hn j hj)))
  have htest : ∀ j < K, epsilon < ‖g (x j)‖ := fun j hj => lt_of_not_ge (hfirst j hj)
  refine ⟨K, hk, htest, ?_, ?_⟩
  · linarith only [h.prefix_count_le hf hL hLp hB hc he hinit hct K (hlow _) htest]
  · linarith only [h.success_count_le hf hL hLp hB hc he hinit hct K (hlow _) htest]

/-- The radius coefficient used by the first-order trust-region complexity bound. -/
def radiusCoefficient (p : Parameters) (L B delta0 g0 : ℝ) : ℝ :=
  p.gamma1 * ((1 - p.eta2) / (2 * (L + B))) * min 1 (delta0 / g0)

/-- The coefficient is positive and compatible with both initialization and the success threshold
whenever the initial gradient has not already vanished. -/
theorem radiusCoefficient_spec (p : Parameters) {L B delta0 g0 : ℝ}
    (hL : 1 ≤ L) (hB : 0 ≤ B) (hd : 0 < delta0) (hg : 0 < g0) :
    0 < radiusCoefficient p L B delta0 g0 ∧
      radiusCoefficient p L B delta0 g0 * g0 ≤ delta0 ∧
      radiusCoefficient p L B delta0 g0 ≤ p.gamma1 * ((1 - p.eta2) / (2 * (L + B))) := by
  let T := (1 - p.eta2) / (2 * (L + B))
  have hden : 0 < 2 * (L + B) := by linarith
  have hT : 0 < T := div_pos (sub_pos.mpr p.eta2_lt_one) hden
  have heta : 0 < p.eta2 := p.eta1_pos.trans_le p.eta_le
  have hTone : T ≤ 1 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  have hgamma : p.gamma1 ≤ 1 := p.gamma_le.trans p.gamma2_lt_one.le
  have hgt : 0 < p.gamma1 * T := mul_pos p.gamma1_pos hT
  have hgtone : p.gamma1 * T ≤ 1 := by nlinarith
  have hmin : 0 < min (1 : ℝ) (delta0 / g0) := lt_min zero_lt_one (div_pos hd hg)
  have hct : radiusCoefficient p L B delta0 g0 ≤ p.gamma1 * T := by
    dsimp [radiusCoefficient, T]
    exact mul_le_of_le_one_right hgt.le (min_le_left _ _)
  refine ⟨mul_pos hgt hmin, ?_, hct⟩
  calc
    radiusCoefficient p L B delta0 g0 * g0 =
        (p.gamma1 * T) * (min 1 (delta0 / g0) * g0) := by
      dsimp [radiusCoefficient, T]
      ring
    _ ≤ 1 * (min 1 (delta0 / g0) * g0) :=
      mul_le_mul_of_nonneg_right hgtone (mul_nonneg hmin.le hg.le)
    _ ≤ delta0 := by
      simpa only [one_mul, div_mul_cancel₀ _ hg.ne'] using
        mul_le_mul_of_nonneg_right (min_le_right (1 : ℝ) (delta0 / g0)) hg.le

/-- Constants independent of the stopping tolerance give the first-order function and gradient
budgets. The already-stationary initial point is included explicitly. -/
theorem IsRun.exists_complexity_constants (h : IsRun p f g H x s delta)
    {L B low : ℝ} (hf : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLp : 1 ≤ L)
    (hB : ∀ k, ‖H k‖ ≤ B) (hlow : ∀ y, low ≤ f y) :
    ∃ kS kA kB kC : ℝ, 0 < kS ∧ 0 < kA ∧ 0 < kB ∧ 0 < kC ∧
      ∀ epsilon : ℝ, 0 < epsilon → ∃ K : ℕ,
        ‖g (x K)‖ ≤ epsilon ∧ (∀ j < K, epsilon < ‖g (x j)‖) ∧
        (K : ℝ) + 1 ≤ kA * ((f (x 0) - low) / epsilon ^ 2) +
          kB * |Real.log epsilon| + kC ∧
        (ParameterUpdates.successCount
          (fun k => p.eta1 ≤ ratio f (g (x k)) (H k) (x k) (s k)) K : ℝ) + 1 ≤
          kS * ((f (x 0) - low) / epsilon ^ 2) + 1 := by
  classical
  by_cases hg : g (x 0) = 0
  · refine ⟨1, 1, 1, 1, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    intro epsilon he
    have hb : 0 ≤ (f (x 0) - low) / epsilon ^ 2 :=
      div_nonneg (sub_nonneg.mpr (hlow _)) (sq_nonneg _)
    refine ⟨0, by simpa [hg] using he.le, by simp, ?_, ?_⟩
    · simp only [Nat.cast_zero, zero_add, one_mul]
      linarith only [hb, abs_nonneg (Real.log epsilon)]
    · simpa [ParameterUpdates.successCount] using hb
  let c := radiusCoefficient p L B (delta 0) ‖g (x 0)‖
  have hspec := radiusCoefficient_spec p hLp ((norm_nonneg _).trans (hB 0))
    (h.radius_pos 0) (norm_pos_iff.mpr hg)
  have hc : 0 < c := hspec.1
  have hinit : c * ‖g (x 0)‖ ≤ delta 0 := hspec.2.1
  have hct : c ≤ p.gamma1 * ((1 - p.eta2) / (2 * (L + B))) := hspec.2.2
  have hD := decreaseCoefficient_pos ((norm_nonneg _).trans (hB 0)) hc
  have hZ : 0 < |Real.log p.gamma2| := abs_pos.mpr
    (Real.log_neg (p.gamma1_pos.trans_le p.gamma_le) p.gamma2_lt_one).ne
  let C := 1 + Real.log p.gamma3 / |Real.log p.gamma2|
  have hC : 0 < C := add_pos_of_pos_of_nonneg zero_lt_one
    (div_nonneg (Real.log_pos p.one_lt_gamma3).le hZ.le)
  have hkS : 0 < 1 / (p.eta1 * decreaseCoefficient B c) :=
    div_pos zero_lt_one (mul_pos p.eta1_pos hD)
  refine ⟨1 / (p.eta1 * decreaseCoefficient B c),
    1 / (p.eta1 * decreaseCoefficient B c) * C, 1 / |Real.log p.gamma2|,
    |Real.log (c / delta 0)| / |Real.log p.gamma2| + 1,
    hkS, mul_pos hkS hC, div_pos zero_lt_one hZ,
    add_pos_of_nonneg_of_pos (div_nonneg (abs_nonneg _) hZ.le) zero_lt_one, ?_⟩
  intro epsilon he
  obtain ⟨K, hk, hfirst, hfun, hgrad⟩ :=
    h.exists_stationary_with_cost hf hL hLp hB hc he hinit hct hlow
  have hbudget : (f (x 0) - low) / (p.eta1 * decreaseCoefficient B c * epsilon ^ 2) =
      (1 / (p.eta1 * decreaseCoefficient B c)) * ((f (x 0) - low) / epsilon ^ 2) := by
    ring
  refine ⟨K, hk, hfirst, ?_, ?_⟩
  · rw [hbudget] at hfun
    convert hfun using 1
    dsimp [C]
    ring
  · rwa [hbudget] at hgrad

end Optimization.TrustRegion

namespace Optimization.TrustRegion
open QuadraticSubproblem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every lawful trial has model value no larger than some genuine Cauchy point. -/
theorem IsRun.exists_cauchyPoint {p : Parameters} {f : E → ℝ} {g : E → E}
    {H : ℕ → E →L[ℝ] E} {x s : ℕ → E} {delta : ℕ → ℝ}
    (h : IsRun p f g H x s delta) (k : ℕ) :
    ∃ sC : E, IsCauchyPoint (g (x k)) (H k) (delta k) sC ∧
      quadratic (g (x k)) (H k) (s k) ≤ quadratic (g (x k)) (H k) sC :=
  (le_all_ray_iff_exists_isCauchyPoint (h.radius_pos k).le (s k)).mp (h.cauchy k)

/-- Every objective, gradient map and model sequence admits a lawful infinite trace, obtained
by taking an actual Cauchy point and retaining the radius after acceptance or multiplying by
`gamma2` after rejection. In particular, the run specification has recursive witnesses
without any smoothness or complexity hypotheses. -/
theorem exists_isRun (p : Parameters) (f : E → ℝ) (g : E → E)
    (H : ℕ → E →L[ℝ] E) (x0 : E) {delta0 : ℝ} (hdelta0 : 0 < delta0) :
    ∃ (x s : ℕ → E) (delta : ℕ → ℝ), x 0 = x0 ∧ delta 0 = delta0 ∧
      IsRun p f g H x s delta := by
  classical
  let cauchy (v : E) (B : E →L[ℝ] E) (d : {r : ℝ // 0 < r}) : E :=
    Classical.choose (exists_isCauchyPoint v B d.property.le)
  have hcauchy (v : E) (B : E →L[ℝ] E) (d : {r : ℝ // 0 < r}) :
      IsCauchyPoint v B d.val (cauchy v B d) :=
    Classical.choose_spec (exists_isCauchyPoint v B d.property.le)
  have hgamma : 0 < p.gamma2 := p.gamma1_pos.trans_le p.gamma_le
  let next (k : ℕ) (z : E × {r : ℝ // 0 < r}) : E × {r : ℝ // 0 < r} :=
    let s := cauchy (g z.1) (H k) z.2
    if p.eta1 ≤ ratio f (g z.1) (H k) z.1 s then
      (z.1 + s, z.2)
    else (z.1, ⟨p.gamma2 * z.2.val, mul_pos hgamma z.2.property⟩)
  let state : ℕ → E × {r : ℝ // 0 < r} := Nat.rec (x0, ⟨delta0, hdelta0⟩) next
  let x (k : ℕ) : E := (state k).1
  let delta (k : ℕ) : ℝ := (state k).2.val
  let s (k : ℕ) : E := cauchy (g (x k)) (H k) (state k).2
  have hnext (k : ℕ) : state (k + 1) = next k (state k) := rfl
  have hrad (k : ℕ) : 0 < delta k := (state k).2.property
  refine ⟨x, s, delta, rfl, rfl, ⟨hdelta0, ?_, ?_, ?_, ?_⟩⟩
  · intro k
    exact (hcauchy (g (x k)) (H k) (state k).2).norm_le
  · intro k t ht hf
    exact (hcauchy (g (x k)) (H k) (state k).2).le_ray ht hf
  · intro k
    change (state (k + 1)).1 = _
    rw [hnext]
    dsimp only [next]
    split_ifs <;> rfl
  · intro k
    have hd := hrad k
    have hdnext : delta (k + 1) =
        if p.eta1 ≤ ratio f (g (x k)) (H k) (x k) (s k)
        then delta k else p.gamma2 * delta k := by
      change (state (k + 1)).2.val = _
      rw [hnext]
      dsimp only [next]
      split_ifs <;> rfl
    rw [hdnext]
    split_ifs with h2 h1
    · exact ⟨le_rfl, le_mul_of_one_le_left hd.le p.one_lt_gamma3.le⟩
    · exact (h1 (p.eta_le.trans h2)).elim
    · exact ⟨mul_le_of_le_one_left hd.le p.gamma2_lt_one.le, le_rfl⟩
    · exact ⟨mul_le_mul_of_nonneg_right p.gamma_le hd.le, le_rfl⟩

end Optimization.TrustRegion
