import Numlib.Optimization.TrustRegionSecondOrder

/-!
# Quadratically regularized trust-region trials

The objective is regularized only in the subproblem; acceptance uses unregularized Taylor
reduction. Traces are finite, so strict model decrease is required only before termination.
Interior steps use the actual derivative of the regularized Taylor polynomial.
-/

noncomputable section
namespace Optimization.RegularizedTrustRegion
open RegularizedTaylorModel
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Quadratic Taylor polynomial with a positive quadratic norm regularizer. -/
def model (f : E → ℝ) (x : E) (epsilon : ℝ) (s : E) : ℝ :=
  regularizedModel f 2 x epsilon 2 2 s

/-- Polynomial expression for the regularized model. -/
theorem model_eq (f : E → ℝ) (x : E) (epsilon : ℝ) (s : E) :
    model f x epsilon s = taylorModel f 2 x s + epsilon / 2 * ‖s‖ ^ 2 := by
  simp [model, regularizedModel]

/-- Actual reduction divided by the unregularized Taylor reduction. -/
def ratio (f : E → ℝ) (x s : E) : ℝ :=
  (f x - f (x + s)) / (taylorModel f 2 x 0 - taylorModel f 2 x s)

/-- Legal trials before a finite stopping index, with actual acceptance and radius updates. -/
structure TrialTrace (p : TrustRegion.Parameters) (theta epsilon : ℝ) (f : E → ℝ)
    (x s : ℕ → E) (delta : ℕ → ℝ) (N : ℕ) : Prop where
  epsilon_pos : 0 < epsilon
  theta_pos : 0 < theta
  initial : epsilon < delta 0
  feasible : ∀ k < N, ‖s k‖ ≤ delta k
  decrease : ∀ k < N, model f (x k) epsilon (s k) < model f (x k) epsilon 0
  residual : ∀ k < N, ‖s k‖ < delta k →
    ‖fderiv ℝ (model f (x k) epsilon) (s k)‖ ≤ theta / 2 * ‖s k‖ ^ 2
  iterate : ∀ k < N, x (k + 1) = if p.eta1 ≤ ratio f (x k) (s k)
    then x k + s k else x k
  update : ∀ k < N, if p.eta2 ≤ ratio f (x k) (s k)
    then delta (k + 1) ∈ Set.Icc (delta k) (p.gamma3 * delta k)
    else if p.eta1 ≤ ratio f (x k) (s k)
    then delta (k + 1) ∈ Set.Icc (p.gamma2 * delta k) (delta k)
    else delta (k + 1) ∈ Set.Icc (p.gamma1 * delta k) (p.gamma2 * delta k)

variable {p : TrustRegion.Parameters} {theta epsilon : ℝ} {f : E → ℝ}
    {x s : ℕ → E} {delta : ℕ → ℝ} {N : ℕ}

/-- Strict regularized decrease forces a nonzero trial. -/
theorem TrialTrace.step_ne_zero (h : TrialTrace p theta epsilon f x s delta N)
    {k : ℕ} (hk : k < N) : s k ≠ 0 := by
  intro hz
  have hd := h.decrease k hk
  rw [hz] at hd
  exact (lt_irrefl _ hd)

/-- The Taylor decrease pays for the quadratic regularizer. -/
theorem TrialTrace.predicted_decrease (h : TrialTrace p theta epsilon f x s delta N)
    {k : ℕ} (hk : k < N) :
    epsilon / 2 * ‖s k‖ ^ 2 ≤ taylorModel f 2 (x k) 0 - taylorModel f 2 (x k) (s k) := by
  have hd := h.decrease k hk
  simp only [model_eq, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero] at hd
  linarith

/-- Every computed trial has positive unregularized predicted decrease. -/
theorem TrialTrace.predicted_pos (h : TrialTrace p theta epsilon f x s delta N)
    {k : ℕ} (hk : k < N) :
    0 < taylorModel f 2 (x k) 0 - taylorModel f 2 (x k) (s k) :=
  (mul_pos (div_pos h.epsilon_pos (by norm_num))
    (sq_pos_of_pos (norm_pos_iff.mpr (h.step_ne_zero hk)))).trans_le (h.predicted_decrease hk)

/-- Accepted objective decrease dominates the acceptance fraction of Taylor decrease. -/
theorem TrialTrace.accepted_decrease (h : TrialTrace p theta epsilon f x s delta N)
    {k : ℕ} (hk : k < N) (hs : p.eta1 ≤ ratio f (x k) (s k)) :
    p.eta1 * (taylorModel f 2 (x k) 0 - taylorModel f 2 (x k) (s k)) ≤
      f (x k) - f (x (k + 1)) := by
  rw [h.iterate k hk, ite_eq_left hs]
  exact (le_div_iff₀ (h.predicted_pos hk)).mp hs

/-- Every radius update retains at least its smallest contraction factor. -/
theorem TrialTrace.radius_update_lower (h : TrialTrace p theta epsilon f x s delta N)
    {k : ℕ} (hk : k < N) (hd : 0 ≤ delta k) : p.gamma1 * delta k ≤ delta (k + 1) := by
  have hu := h.update k hk
  split_ifs at hu
  · exact (mul_le_of_le_one_left hd (p.gamma_le.trans p.gamma2_lt_one.le)).trans hu.1
  · exact (mul_le_mul_of_nonneg_right p.gamma_le hd).trans hu.1
  · exact hu.1

/-- All radii through the stopping index are positive. -/
theorem TrialTrace.radius_pos (h : TrialTrace p theta epsilon f x s delta N)
    {k : ℕ} (hk : k ≤ N) : 0 < delta k := by
  induction k with
  | zero => exact h.epsilon_pos.trans h.initial
  | succ k ih =>
    exact (mul_pos p.gamma1_pos (ih (by omega))).trans_le
      (h.radius_update_lower (by omega) (ih (by omega)).le)

/-- A sufficiently small radius guarantees a very successful trial. -/
theorem TrialTrace.ratio_ge_of_radius (h : TrialTrace p theta epsilon f x s delta N)
    {L : ℝ} (hf : CubicRegularization.HessianLipschitz f L) {k : ℕ} (hk : k < N)
    (hsmall : L * delta k ≤ 3 * (1 - p.eta2) * epsilon) :
    p.eta2 ≤ ratio f (x k) (s k) := by
  unfold ratio
  rw [le_div_iff₀ (h.predicted_pos hk)]
  have ht := (abs_le.mp (hf.value_remainder (x k) (s k))).2
  have hc := h.predicted_decrease hk
  have hs := h.feasible k hk
  have hstep := mul_le_mul_of_nonneg_left hs hf.nonneg
  have hsc := mul_le_mul_of_nonneg_right (hstep.trans hsmall) (sq_nonneg ‖s k‖)
  have hpc := mul_le_mul_of_nonneg_left hc (sub_nonneg.mpr p.eta2_lt_one.le)
  simp only [taylorModel_zero] at *
  nlinarith only [ht, hsc, hpc]

/-- A positive coefficient below initialization and the success threshold bounds every radius. -/
theorem TrialTrace.radius_lower (h : TrialTrace p theta epsilon f x s delta N)
    {L c : ℝ} (hf : CubicRegularization.HessianLipschitz f L)
    (hinit : c * epsilon ≤ delta 0) (hc : L * c ≤ 3 * p.gamma1 * (1 - p.eta2))
    {k : ℕ} (hk : k ≤ N) : c * epsilon ≤ delta k := by
  induction k with
  | zero => exact hinit
  | succ k ih =>
    have hi := ih (by omega)
    by_cases hs : p.eta2 ≤ ratio f (x k) (s k)
    · have hu := h.update k (by omega)
      rw [ite_eq_left hs] at hu
      exact hi.trans hu.1
    · by_contra hn
      have hu := h.radius_update_lower (k := k) (by omega) (h.radius_pos (k := k) (by omega)).le
      have hsmall : L * delta k ≤ 3 * (1 - p.eta2) * epsilon := by
        have h1 := mul_le_mul_of_nonneg_left (le_of_not_ge hn) hf.nonneg
        have h2 := mul_le_mul_of_nonneg_right hc h.epsilon_pos.le
        have h3 := mul_le_mul_of_nonneg_left hu hf.nonneg
        nlinarith only [h1, h2, h3, p.gamma1_pos]
      exact hs (h.ratio_ge_of_radius hf (by omega) hsmall)

/-- Normalizing the Hessian Lipschitz bound to at least one yields the standard radius bound. -/
theorem TrialTrace.radius_lower_normalized (h : TrialTrace p theta epsilon f x s delta N)
    {L : ℝ} (hf : CubicRegularization.HessianLipschitz f L) (hL : 1 ≤ L)
    {k : ℕ} (hk : k ≤ N) :
    ((1 - p.eta2) * p.gamma1 / L) * epsilon ≤ delta k := by
  have hp : 0 < L := by linarith
  have heta : 0 < p.eta2 := p.eta1_pos.trans_le p.eta_le
  have hg : p.gamma1 < 1 := p.gamma_le.trans_lt p.gamma2_lt_one
  apply h.radius_lower hf _ _ hk
  · have hc : (1 - p.eta2) * p.gamma1 / L ≤ 1 := by
      apply (div_le_iff₀ hp).mpr
      nlinarith only [p.eta2_lt_one, p.gamma1_pos, hg, hL, heta]
    exact (mul_le_of_le_one_left h.epsilon_pos.le hc).trans h.initial.le
  · field_simp
    nlinarith only [p.eta2_lt_one, p.gamma1_pos]

/-- An interior step controls the actual trial gradient by a quadratic plus a linear term. -/
theorem TrialTrace.trial_derivative_bound (h : TrialTrace p theta epsilon f x s delta N)
    {L : ℝ} (hf : CubicRegularization.HessianLipschitz f L) {k : ℕ} (hk : k < N)
    (hint : ‖s k‖ < delta k) :
    ‖fderiv ℝ f (x k + s k)‖ ≤ (L + theta) / 2 * ‖s k‖ ^ 2 + epsilon * ‖s k‖ := by
  have hh := fderiv_step_lower_bound (p := 2) (beta := 1) (r := 2)
    (sigma := epsilon) (c := 2) (A := L / 2) (theta := theta / 2 * ‖s k‖)
    h.epsilon_pos.le (by norm_num) (by norm_num)
    (by simpa using hf.derivative_remainder (x k) (s k))
    (by
      norm_num
      change ‖fderiv ℝ (model f (x k) epsilon) (s k)‖ ≤ _
      convert h.residual k hk hint using 1; ring)
  norm_num at hh
  nlinarith only [hh]

/-- A mixed quadratic-linear upper bound gives a tolerance-scaled square lower bound. -/
theorem min_sq_le_of_quadratic_bound {A e z t : ℝ} (hA : 0 ≤ A) (he : 0 < e)
    (hz : 0 ≤ z) (ht : 0 ≤ t) (hb : z ≤ A / 2 * t ^ 2 + e * t) :
    (min e (z / e)) ^ 2 ≤ (1 + 2 * A) * t ^ 2 := by
  let m := min e (z / e)
  have hm : 0 ≤ m := le_min he.le (div_nonneg hz he.le)
  have hme : m ≤ e := min_le_left _ _
  have hmz : e * m ≤ z := by
    have hh := mul_le_mul_of_nonneg_left (min_le_right e (z / e)) he.le
    simpa [mul_div_cancel₀ _ he.ne'] using hh
  change m ^ 2 ≤ _
  by_cases hmt : m ≤ t
  · have hh : m ^ 2 ≤ t ^ 2 := by nlinarith only [hm, ht, hmt]
    nlinarith only [hh, mul_nonneg hA (sq_nonneg t)]
  · have hh := mul_le_mul_of_nonneg_right hme (sub_nonneg.mpr (le_of_not_ge hmt))
    nlinarith only [hb, hmz, hh, sq_nonneg (m - t), mul_nonneg hA (sq_nonneg t)]

/-- Successful interior steps satisfy the standard tolerance-scaled length bound. -/
theorem TrialTrace.interior_step_lower [CompleteSpace E]
    (h : TrialTrace p theta epsilon f x s delta N)
    {L : ℝ} (hf : CubicRegularization.HessianLipschitz f L) {k : ℕ} (hk : k < N)
    (hs : p.eta1 ≤ ratio f (x k) (s k)) (hint : ‖s k‖ < delta k) :
    min epsilon (‖gradient f (x (k + 1))‖ / epsilon) /
      Real.sqrt (1 + 2 * (L + theta)) ≤ ‖s k‖ := by
  have hg : ‖gradient f (x (k + 1))‖ = ‖fderiv ℝ f (x k + s k)‖ := by
    rw [h.iterate k hk, ite_eq_left hs]
    simp [gradient]
  have hb := h.trial_derivative_bound hf hk hint
  rw [← hg] at hb
  have hA : 0 ≤ L + theta := add_nonneg hf.nonneg h.theta_pos.le
  have hh := min_sq_le_of_quadratic_bound hA h.epsilon_pos
    (norm_nonneg _) (norm_nonneg _) hb
  have hD : 0 < 1 + 2 * (L + theta) := by linarith only [hA]
  have hsqrt := Real.sqrt_pos.mpr hD
  apply (div_le_iff₀ hsqrt).mpr
  have heq : (‖s k‖ * Real.sqrt (1 + 2 * (L + theta))) ^ 2 =
      (1 + 2 * (L + theta)) * ‖s k‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hD.le]
    ring
  have hnon : 0 ≤ ‖s k‖ * Real.sqrt (1 + 2 * (L + theta)) := by positivity
  nlinarith only [hh, heq, hnon]

/-- The common sufficient-decrease coefficient, combining boundary and interior cases. -/
def decreaseCoefficient (p : TrustRegion.Parameters) (L theta : ℝ) : ℝ :=
  p.eta1 / 2 * min (((1 - p.eta2) * p.gamma1 / L) ^ 2) (1 / (1 + 2 * (L + theta)))

/-- Positive normalized Lipschitz constants and residual parameters give positive decrease. -/
theorem decreaseCoefficient_pos (p : TrustRegion.Parameters) {L theta : ℝ}
    (hL : 1 ≤ L) (htheta : 0 < theta) : 0 < decreaseCoefficient p L theta := by
  unfold decreaseCoefficient
  apply mul_pos (div_pos p.eta1_pos (by norm_num))
  apply lt_min
  · exact sq_pos_of_pos (div_pos (mul_pos (sub_pos.mpr p.eta2_lt_one) p.gamma1_pos)
      (by linarith))
  · positivity

/-- Multiplication by the regularization weight turns the squared minimum into the two scales. -/
theorem mul_min_sq (e z : ℝ) (he : 0 < e) (hz : 0 ≤ z) :
    e * (min e (z / e)) ^ 2 = min (e ^ 3) (z ^ 2 / e) := by
  rcases le_total e (z / e) with hh | hh
  · rw [min_eq_left hh, min_eq_left]
    · ring
    · have hm : e * e ≤ z := (le_div_iff₀ he).mp hh
      apply (le_div_iff₀ he).mpr
      nlinarith only [mul_le_mul hm hm (mul_self_nonneg e) hz]
  · rw [min_eq_right hh, min_eq_right]
    · field_simp
    · have hm : z ≤ e * e := (div_le_iff₀ he).mp hh
      apply (div_le_iff₀ he).mpr
      nlinarith only [mul_le_mul hm hm hz (mul_self_nonneg e)]

/-- Successful strictly interior trials decrease the objective on the mixed gradient scale. -/
theorem TrialTrace.interior_decrease [CompleteSpace E]
    (h : TrialTrace p theta epsilon f x s delta N) {L : ℝ}
    (hf : CubicRegularization.HessianLipschitz f L)
    {k : ℕ} (hk : k < N) (hs : p.eta1 ≤ ratio f (x k) (s k))
    (hint : ‖s k‖ < delta k) :
    decreaseCoefficient p L theta *
        min (epsilon ^ 3) (‖gradient f (x (k + 1))‖ ^ 2 / epsilon) ≤
      f (x k) - f (x (k + 1)) := by
  have hA : 0 ≤ L + theta := add_nonneg hf.nonneg h.theta_pos.le
  have hD : 0 < 1 + 2 * (L + theta) := by positivity
  have hg : ‖gradient f (x (k + 1))‖ = ‖fderiv ℝ f (x k + s k)‖ := by
    rw [h.iterate k hk, ite_eq_left hs]
    simp [gradient]
  have hb := h.trial_derivative_bound hf hk hint
  rw [← hg] at hb
  have hm := min_sq_le_of_quadratic_bound hA h.epsilon_pos
    (norm_nonneg _) (norm_nonneg _) hb
  have hsq : (min epsilon (‖gradient f (x (k + 1))‖ / epsilon)) ^ 2 /
      (1 + 2 * (L + theta)) ≤ ‖s k‖ ^ 2 := (div_le_iff₀ hD).mpr (by nlinarith only [hm])
  have hscale := mul_min_sq epsilon ‖gradient f (x (k + 1))‖ h.epsilon_pos (norm_nonneg _)
  have hmin : 0 ≤ min (epsilon ^ 3) (‖gradient f (x (k + 1))‖ ^ 2 / epsilon) :=
    le_min (pow_nonneg h.epsilon_pos.le _) (div_nonneg (sq_nonneg _) h.epsilon_pos.le)
  have hc : decreaseCoefficient p L theta ≤ p.eta1 / 2 / (1 + 2 * (L + theta)) := by
    unfold decreaseCoefficient
    convert mul_le_mul_of_nonneg_left
      (min_le_right (((1 - p.eta2) * p.gamma1 / L) ^ 2)
        (1 / (1 + 2 * (L + theta)))) (div_nonneg p.eta1_pos.le (by norm_num : (0 : ℝ) ≤ 2)) using 1
    ring
  have h1 := mul_le_mul_of_nonneg_right hc hmin
  have h2 := mul_le_mul_of_nonneg_left hsq
    (mul_nonneg (div_nonneg p.eta1_pos.le (by norm_num : (0 : ℝ) ≤ 2)) h.epsilon_pos.le)
  have h3 := mul_le_mul_of_nonneg_left (h.predicted_decrease hk) p.eta1_pos.le
  have h4 := h.accepted_decrease hk hs
  rw [← hscale] at h1 ⊢
  calc
    _ ≤ p.eta1 / 2 / (1 + 2 * (L + theta)) *
        (epsilon * (min epsilon (‖gradient f (x (k + 1))‖ / epsilon)) ^ 2) := h1
    _ = (p.eta1 / 2 * epsilon) *
        ((min epsilon (‖gradient f (x (k + 1))‖ / epsilon)) ^ 2 /
          (1 + 2 * (L + theta))) := by ring
    _ ≤ (p.eta1 / 2 * epsilon) * ‖s k‖ ^ 2 := h2
    _ ≤ f (x k) - f (x (k + 1)) := by nlinarith only [h3, h4]

/-- Successful boundary trials decrease the objective on the cubic regularization scale. -/
theorem TrialTrace.boundary_decrease (h : TrialTrace p theta epsilon f x s delta N)
    {L : ℝ} (hf : CubicRegularization.HessianLipschitz f L) (hL : 1 ≤ L)
    {k : ℕ} (hk : k < N) (hs : p.eta1 ≤ ratio f (x k) (s k))
    (hboundary : ‖s k‖ = delta k) :
    decreaseCoefficient p L theta * epsilon ^ 3 ≤ f (x k) - f (x (k + 1)) := by
  let c := (1 - p.eta2) * p.gamma1 / L
  have hc : 0 ≤ c := div_nonneg
    (mul_nonneg (sub_nonneg.mpr p.eta2_lt_one.le) p.gamma1_pos.le) (by linarith)
  have hr := h.radius_lower_normalized hf hL (k := k) (by omega)
  change c * epsilon ≤ delta k at hr
  have hsq : (c * epsilon) ^ 2 ≤ delta k ^ 2 := by
    nlinarith only [hr, h.radius_pos (k := k) (by omega), mul_nonneg hc h.epsilon_pos.le]
  have h1 := mul_le_mul_of_nonneg_left hsq
    (mul_nonneg (div_nonneg p.eta1_pos.le (by norm_num : (0 : ℝ) ≤ 2)) h.epsilon_pos.le)
  have h2 := mul_le_mul_of_nonneg_left (h.predicted_decrease hk) p.eta1_pos.le
  rw [hboundary] at h2
  have h3 := h.accepted_decrease hk hs
  have h4 := mul_le_mul_of_nonneg_left
    (min_le_left (c ^ 2) (1 / (1 + 2 * (L + theta))))
    (div_nonneg p.eta1_pos.le (by norm_num : (0 : ℝ) ≤ 2))
  have h5 := mul_le_mul_of_nonneg_right h4 (pow_nonneg h.epsilon_pos.le 3)
  change decreaseCoefficient p L theta * epsilon ^ 3 ≤ _ at h5
  nlinarith only [h1, h2, h3, h5]

/-- Finite traces retain objective monotonicity, including rejected trials. -/
theorem TrialTrace.objective_nonincrease (h : TrialTrace p theta epsilon f x s delta N)
    {k : ℕ} (hk : k < N) : f (x (k + 1)) ≤ f (x k) := by
  by_cases hs : p.eta1 ≤ ratio f (x k) (s k)
  · have hh := h.accepted_decrease hk hs
    have hp := mul_nonneg p.eta1_pos.le (h.predicted_pos hk).le
    linarith only [hh, hp]
  · rw [h.iterate k hk, ite_eq_right hs]

/-- Three-way radius updates bound total trials in a finite trace. -/
theorem TrialTrace.total_count_le (h : TrialTrace p theta epsilon f x s delta N)
    {m : ℝ} (hm : 0 < m) (hmin : m ≤ delta N) :
    (N : ℝ) ≤ (ParameterUpdates.successCount
      (fun k => p.eta1 ≤ ratio f (x k) (s k)) N : ℝ) *
      (1 + Real.log p.gamma3 / |Real.log p.gamma2|) +
      Real.log (delta 0 / m) / |Real.log p.gamma2| := by
  classical
  let d := fun j => delta (min j N)
  let success := fun j => j < N → p.eta1 ≤ ratio f (x j) (s j)
  have hcount : ParameterUpdates.successCount success N =
      ParameterUpdates.successCount (fun j => p.eta1 ≤ ratio f (x j) (s j)) N := by
    unfold ParameterUpdates.successCount
    congr 1
    ext j
    by_cases hj : j < N <;> simp [success, hj]
  have ht := ParameterUpdates.total_count_le_of_lower_bound (u := d) (success := success)
    (fun j => h.radius_pos (min_le_right _ _))
    (zero_lt_one.trans p.one_lt_gamma3)
    ⟨p.gamma1_pos.trans_le p.gamma_le, p.gamma2_lt_one⟩
    (by
      intro j hj
      by_cases hjN : j < N
      · have hu := h.update j hjN
        have hs := hj hjN
        dsimp [d]
        rw [min_eq_left (by omega : j + 1 ≤ N), min_eq_left hjN.le]
        split_ifs at hu
        · exact hu.2
        · exact hu.2.trans
            (le_mul_of_one_le_left (h.radius_pos hjN.le).le p.one_lt_gamma3.le)
      · simp only [d, min_eq_right (by omega : N ≤ j + 1),
          min_eq_right (by omega : N ≤ j)]
        exact le_mul_of_one_le_left (h.radius_pos le_rfl).le p.one_lt_gamma3.le)
    (by
      intro j hj
      have hjN : j < N := by by_contra hn; exact hj (by simp [success, hn])
      have hs : ¬p.eta1 ≤ ratio f (x j) (s j) := fun hs => hj (fun _ => hs)
      have h2 : ¬p.eta2 ≤ ratio f (x j) (s j) := fun hh => hs (p.eta_le.trans hh)
      have hu := h.update j hjN
      rw [ite_eq_right h2, ite_eq_right hs] at hu
      simpa only [d, min_eq_left (by omega : j + 1 ≤ N), min_eq_left hjN.le] using hu.2)
    N hm (by simpa [d] using hmin)
  simpa only [hcount, d, min_self, zero_min] using ht

/-- Every accepted trial before a failed successor gradient test pays the common decrease. -/
theorem TrialTrace.accepted_budget [CompleteSpace E]
    (h : TrialTrace p theta epsilon f x s delta N) {L tolerance : ℝ}
    (hf : CubicRegularization.HessianLipschitz f L) (hL : 1 ≤ L) (ht : 0 < tolerance)
    {k : ℕ} (hk : k < N) (hs : p.eta1 ≤ ratio f (x k) (s k))
    (hnext : tolerance ≤ ‖gradient f (x (k + 1))‖) :
    decreaseCoefficient p L theta * min (epsilon ^ 3) (tolerance ^ 2 / epsilon) ≤
      f (x k) - f (x (k + 1)) := by
  have hc := (decreaseCoefficient_pos p hL h.theta_pos).le
  rcases lt_or_eq_of_le (h.feasible k hk) with hint | hboundary
  · have hh : tolerance ^ 2 ≤ ‖gradient f (x (k + 1))‖ ^ 2 := by
      nlinarith only [hnext, ht, norm_nonneg (gradient f (x (k + 1)))]
    exact (mul_le_mul_of_nonneg_left
      (min_le_min_left (epsilon ^ 3) (div_le_div_of_nonneg_right hh h.epsilon_pos.le)) hc).trans
      (h.interior_decrease hf hk hs hint)
  · exact (mul_le_mul_of_nonneg_left
      (min_le_left (epsilon ^ 3) (tolerance ^ 2 / epsilon)) hc).trans
      (h.boundary_decrease hf hL hk hs hboundary)

/-- A finite prefix with all its successor gradient tests failing has bounded successes. -/
theorem TrialTrace.success_count_le [CompleteSpace E]
    (h : TrialTrace p theta epsilon f x s delta N) {L tolerance low : ℝ}
    (hf : CubicRegularization.HessianLipschitz f L) (hL : 1 ≤ L) (ht : 0 < tolerance)
    (hlow : low ≤ f (x N))
    (htest : ∀ j ≤ N, tolerance < ‖gradient f (x j)‖) :
    (ParameterUpdates.successCount (fun k => p.eta1 ≤ ratio f (x k) (s k)) N : ℝ) ≤
      (f (x 0) - low) /
        (decreaseCoefficient p L theta * min (epsilon ^ 3) (tolerance ^ 2 / epsilon)) := by
  classical
  have hd : 0 < decreaseCoefficient p L theta *
      min (epsilon ^ 3) (tolerance ^ 2 / epsilon) :=
    mul_pos (decreaseCoefficient_pos p hL h.theta_pos)
      (lt_min (pow_pos h.epsilon_pos _) (div_pos (sq_pos_of_pos ht) h.epsilon_pos))
  apply (le_div_iff₀ hd).mpr
  unfold ParameterUpdates.successCount
  apply EvaluationComplexity.card_mul_le_gap (u := fun k => f (x k))
    (Finset.filter_subset _ _) hlow (fun k hk => h.objective_nonincrease hk)
  intro k hk
  obtain ⟨hkn, hs⟩ := Finset.mem_filter.mp hk
  exact h.accepted_budget hf hL ht (Finset.mem_range.mp hkn) hs
    (htest (k + 1) (by have := Finset.mem_range.mp hkn; omega)).le

/-- The radius lower bound gives logarithmic tolerance overhead in total trial count. -/
theorem TrialTrace.total_count_le_logarithmic
    (h : TrialTrace p theta epsilon f x s delta N) {L : ℝ}
    (hf : CubicRegularization.HessianLipschitz f L) (hL : 1 ≤ L) :
    (N : ℝ) ≤ (ParameterUpdates.successCount (fun k => p.eta1 ≤ ratio f (x k) (s k)) N : ℝ) *
        (1 + Real.log p.gamma3 / |Real.log p.gamma2|) +
      (|Real.log (((1 - p.eta2) * p.gamma1 / L) / delta 0)| + |Real.log epsilon|) /
        |Real.log p.gamma2| := by
  let c := (1 - p.eta2) * p.gamma1 / L
  have hc : 0 < c := div_pos
    (mul_pos (sub_pos.mpr p.eta2_lt_one) p.gamma1_pos) (by linarith)
  have hZ : 0 < |Real.log p.gamma2| := abs_pos.mpr
    (Real.log_neg (p.gamma1_pos.trans_le p.gamma_le) p.gamma2_lt_one).ne
  have ht' := h.total_count_le (mul_pos hc h.epsilon_pos)
    (h.radius_lower_normalized hf hL le_rfl)
  have hlogeq : Real.log (delta 0 / (c * epsilon)) =
      -(Real.log (c / delta 0) + Real.log epsilon) := by
    rw [Real.log_div (h.radius_pos (k := 0) (by omega)).ne' (mul_pos hc h.epsilon_pos).ne',
      Real.log_mul hc.ne' h.epsilon_pos.ne',
      Real.log_div hc.ne' (h.radius_pos (k := 0) (by omega)).ne']
    ring
  have hlog : Real.log (delta 0 / (c * epsilon)) ≤
      |Real.log (c / delta 0)| + |Real.log epsilon| := by
    rw [hlogeq]
    linarith only [neg_le_abs (Real.log (c / delta 0)), neg_le_abs (Real.log epsilon)]
  have h2 := div_le_div_of_nonneg_right hlog hZ.le
  change (N : ℝ) ≤ _ + (|Real.log (c / delta 0)| + |Real.log epsilon|) / _
  linarith only [ht', h2]

/-- An explicit total trial budget for every prefix whose endpoint still fails the gradient
stopping test. This is independent of any assumption that a terminal index exists. -/
theorem TrialTrace.prefix_count_le [CompleteSpace E]
    (h : TrialTrace p theta epsilon f x s delta N) {L tolerance low : ℝ}
    (hf : CubicRegularization.HessianLipschitz f L) (hL : 1 ≤ L) (ht : 0 < tolerance)
    (hlow : low ≤ f (x N))
    (htest : ∀ j ≤ N, tolerance < ‖gradient f (x j)‖) :
    (N : ℝ) ≤ (f (x 0) - low) /
      (decreaseCoefficient p L theta * min (epsilon ^ 3) (tolerance ^ 2 / epsilon)) *
        (1 + Real.log p.gamma3 / |Real.log p.gamma2|) +
      (|Real.log (((1 - p.eta2) * p.gamma1 / L) / delta 0)| + |Real.log epsilon|) /
        |Real.log p.gamma2| := by
  have hZ : 0 < |Real.log p.gamma2| := abs_pos.mpr
    (Real.log_neg (p.gamma1_pos.trans_le p.gamma_le) p.gamma2_lt_one).ne
  have hC : 0 ≤ 1 + Real.log p.gamma3 / |Real.log p.gamma2| :=
    add_nonneg zero_le_one (div_nonneg (Real.log_pos p.one_lt_gamma3).le hZ.le)
  exact (h.total_count_le_logarithmic hf hL).trans
    (add_le_add (mul_le_mul_of_nonneg_right
      (h.success_count_le hf hL ht hlow htest) hC) le_rfl)

/-- Negative regularized curvature admits a legal signed unit eigen-direction boundary trial.
The existential choice allows all ties in the least eigenspace, with its sign chosen for descent. -/
theorem exists_boundary_model_decrease [CompleteSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
    {f : E → ℝ} {x : E} {epsilon delta : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hd : 0 < delta)
    (hc : TrustRegionSecondOrder.curvature f x < -epsilon) :
    ∃ u : E, ‖u‖ = 1 ∧
      fderiv ℝ (fderiv ℝ f) x u u = TrustRegionSecondOrder.curvature f x ∧
      inner ℝ (gradient f x) u ≤ 0 ∧ ‖delta • u‖ = delta ∧
      model f x epsilon (delta • u) < model f x epsilon 0 := by
  obtain ⟨u, hu, he, hg⟩ := TrustRegionSecondOrder.exists_signed_unit hf
  have hn : ‖delta • u‖ = delta := by simp [norm_smul, hu, abs_of_pos hd]
  refine ⟨u, hu, he, hg, hn, ?_⟩
  rw [model_eq, model_eq, TrustRegionSecondOrder.taylorModel_eq,
    TrustRegionSecondOrder.taylorModel_eq, hn]
  have hi : inner ℝ u (TrustRegionSecondOrder.hessianOperator f x u) =
      TrustRegionSecondOrder.curvature f x := by
    rw [real_inner_comm, TrustRegionSecondOrder.hessianOperator,
      InnerProductSpace.continuousLinearMapOfBilin_apply, he]
  simp only [QuadraticSubproblem.quadratic, map_smul, real_inner_smul_left,
    real_inner_smul_right, map_zero, inner_zero_right, mul_zero, add_zero, norm_zero,
    zero_pow (by norm_num : 2 ≠ 0)]
  rw [hi]
  have hlin := mul_nonpos_of_nonneg_of_nonpos hd.le hg
  have hquad := mul_neg_of_neg_of_pos (by linarith only [hc] :
    TrustRegionSecondOrder.curvature f x + epsilon < 0) (sq_pos_of_pos hd)
  nlinarith only [hlin, hquad]

/-- The selected gradient and optional full-Hessian curvature stopping test. -/
def Stationary [CompleteSpace E] (second : Bool) (f : E → ℝ)
    (epsilon1 epsilon2 : ℝ) (y : E) : Prop :=
  ‖gradient f y‖ ≤ epsilon1 ∧
    (second = true → -epsilon2 ≤ TrustRegionSecondOrder.curvature f y)

/-- A complete finite execution with its first successful stopping test. Curvature forcing
uses the Hessian at the current iterate, exactly as in step computation. -/
structure IsRun [CompleteSpace E] (p : TrustRegion.Parameters) (second : Bool)
    (theta epsilon epsilon1 epsilon2 : ℝ) (f : E → ℝ)
    (x s : ℕ → E) (delta : ℕ → ℝ) (N : ℕ) : Prop extends
    TrialTrace p theta epsilon f x s delta N where
  epsilon_le_one : epsilon ≤ 1
  epsilon1_pos : 0 < epsilon1
  epsilon1_le_one : epsilon1 ≤ 1
  epsilon2_domain : second = true → 0 < epsilon2 ∧ epsilon2 ≤ 1
  coupling : epsilon = if second then epsilon2 else Real.sqrt epsilon1
  boundary : second = true → ∀ k < N,
    TrustRegionSecondOrder.curvature f (x k) < -epsilon2 → ‖s k‖ = delta k
  terminal : Stationary second f epsilon1 epsilon2 (x N)
  first : ∀ k < N, ¬Stationary second f epsilon1 epsilon2 (x k)

/-- The initial objective and one new trial objective at each executed iteration. -/
def functionEvaluations (N : ℕ) : ℕ := N + 1

/-- The initial derivatives and fresh gradient/Hessian values only after accepted trials.
Rejected trials retain the cached current derivatives. -/
def derivativeEvaluations (p : TrustRegion.Parameters) (f : E → ℝ)
    (x s : ℕ → E) (N : ℕ) : ℕ :=
  ParameterUpdates.successCount (fun k => p.eta1 ≤ ratio f (x k) (s k)) N + 1

/-- Coupling the gradient tolerance to the square of the regularization weight gives the
cubic decrease scale used for first-order complexity. -/
theorem coupled_scale (e : ℝ) (he : 0 < e) :
    min (e ^ 3) ((e ^ 2) ^ 2 / e) = e ^ 3 := by
  have hh : (e ^ 2) ^ 2 / e = e ^ 3 := by field_simp
  rw [hh, min_self]

/-- A lawful algorithm that can supply every still-required finite prefix reaches its first
gradient test within the explicit evaluation budgets. The premise contains only trial laws,
not termination or complexity estimates. -/
theorem exists_firstOrder_with_cost [CompleteSpace E] {L low : ℝ}
    (he : 0 < epsilon) (htheta : 0 < theta)
    (hf : CubicRegularization.HessianLipschitz f L) (hL : 1 ≤ L)
    (hlow : ∀ y, low ≤ f y)
    (hprefix : ∀ n, (∀ j < n, epsilon ^ 2 < ‖gradient f (x j)‖) →
      TrialTrace p theta epsilon f x s delta n) :
    ∃ K : ℕ, ‖gradient f (x K)‖ ≤ epsilon ^ 2 ∧
      (∀ j < K, epsilon ^ 2 < ‖gradient f (x j)‖) ∧
      (functionEvaluations K : ℝ) ≤
        (f (x 0) - low) / (decreaseCoefficient p L theta * epsilon ^ 3) *
          (1 + Real.log p.gamma3 / |Real.log p.gamma2|) +
        (|Real.log (((1 - p.eta2) * p.gamma1 / L) / delta 0)| +
          |Real.log epsilon|) / |Real.log p.gamma2| + 2 ∧
      (derivativeEvaluations p f x s K : ℝ) ≤
        (f (x 0) - low) / (decreaseCoefficient p L theta * epsilon ^ 3) + 2 := by
  classical
  let D := (f (x 0) - low) / (decreaseCoefficient p L theta * epsilon ^ 3)
  let B := D * (1 + Real.log p.gamma3 / |Real.log p.gamma2|) +
    (|Real.log (((1 - p.eta2) * p.gamma1 / L) / delta 0)| +
      |Real.log epsilon|) / |Real.log p.gamma2|
  have hD : 0 ≤ D := div_nonneg (sub_nonneg.mpr (hlow _))
    (mul_pos (decreaseCoefficient_pos p hL htheta) (pow_pos he _)).le
  have hB : 0 ≤ B := by
    dsimp [B]
    exact add_nonneg (mul_nonneg hD (add_nonneg zero_le_one
      (div_nonneg (Real.log_pos p.one_lt_gamma3).le (abs_nonneg _))))
      (div_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _))
  have hbound : ∀ n, (∀ j < n, epsilon ^ 2 < ‖gradient f (x j)‖) → (n : ℝ) ≤ B + 1 := by
    intro n hn
    cases n with
    | zero => simp only [Nat.cast_zero]; linarith only [hB]
    | succ n =>
      have h := hprefix n (fun j hj => hn j (by omega))
      have hh := h.prefix_count_le hf hL (sq_pos_of_pos he) (hlow _)
        (fun j hj => hn j (by omega))
      rw [coupled_scale epsilon he] at hh
      change (n : ℝ) ≤ B at hh
      push_cast
      linarith only [hh]
  obtain ⟨K, _, hK, hfirst⟩ := EvaluationComplexity.exists_first_of_prefix_bound
    (P := fun j => ‖gradient f (x j)‖ ≤ epsilon ^ 2)
    (fun n hn => hbound n (fun j hj => lt_of_not_ge (hn j hj)))
  have htest : ∀ j < K, epsilon ^ 2 < ‖gradient f (x j)‖ :=
    fun j hj => lt_of_not_ge (hfirst j hj)
  refine ⟨K, hK, htest, ?_, ?_⟩
  · have hh := hbound K htest
    simp only [functionEvaluations, Nat.cast_add, Nat.cast_one]
    change (K : ℝ) + 1 ≤ B + 2
    linarith only [hh]
  · cases K with
    | zero => simpa [derivativeEvaluations, ParameterUpdates.successCount, D] using
        (by linarith only [hD] : (1 : ℝ) ≤ D + 2)
    | succ n =>
      have h := hprefix n (fun j hj => htest j (by omega))
      have hh := h.success_count_le hf hL (sq_pos_of_pos he) (hlow _)
        (fun j hj => htest j (by omega))
      rw [coupled_scale epsilon he] at hh
      have hc : ParameterUpdates.successCount
          (fun j => p.eta1 ≤ ratio f (x j) (s j)) (n + 1) ≤
          ParameterUpdates.successCount (fun j => p.eta1 ≤ ratio f (x j) (s j)) n + 1 := by
        simp only [ParameterUpdates.successCount, Finset.range_add_one, Finset.filter_insert]
        split_ifs
        · exact Finset.card_insert_le _ _
        · omega
      have hc' : (ParameterUpdates.successCount
          (fun j => p.eta1 ≤ ratio f (x j) (s j)) (n + 1) : ℝ) ≤
          (ParameterUpdates.successCount (fun j => p.eta1 ≤ ratio f (x j) (s j)) n : ℝ) + 1 := by
        exact_mod_cast hc
      simp only [derivativeEvaluations, Nat.cast_add, Nat.cast_one]
      change _ ≤ D + 2
      linarith only [hh, hc']

/-- Uniform first-order complexity constants are chosen before the gradient tolerance and
before any legal trace, with a fixed initial point and initial radius. -/
theorem exists_firstOrder_complexity_constants [CompleteSpace E]
    (p : TrustRegion.Parameters) (theta : ℝ) (f : E → ℝ) (x0 : E) (delta0 : ℝ)
    {L low : ℝ} (htheta : 0 < theta)
    (hf : CubicRegularization.HessianLipschitz f L) (hL : 1 ≤ L)
    (hlow : ∀ y, low ≤ f y) :
    ∃ kS kA kB kC : ℝ, 0 < kS ∧ 0 < kA ∧ 0 < kB ∧ 0 < kC ∧
      ∀ tolerance : ℝ, 0 < tolerance → tolerance ≤ 1 →
      ∀ (x s : ℕ → E) (delta : ℕ → ℝ), x 0 = x0 → delta 0 = delta0 →
        (∀ n, (∀ j < n, tolerance < ‖gradient f (x j)‖) →
          TrialTrace p theta (Real.sqrt tolerance) f x s delta n) →
        ∃ K : ℕ, ‖gradient f (x K)‖ ≤ tolerance ∧
          (∀ j < K, tolerance < ‖gradient f (x j)‖) ∧
          (functionEvaluations K : ℝ) ≤
            kA * ((f x0 - low) / tolerance ^ (3 / 2 : ℝ)) +
              kB * |Real.log tolerance| + kC ∧
          (derivativeEvaluations p f x s K : ℝ) ≤
            kS * ((f x0 - low) / tolerance ^ (3 / 2 : ℝ)) + 2 := by
  let c := (1 - p.eta2) * p.gamma1 / L
  let C := 1 + Real.log p.gamma3 / |Real.log p.gamma2|
  have hκ := decreaseCoefficient_pos p hL htheta
  have hZ : 0 < |Real.log p.gamma2| := abs_pos.mpr
    (Real.log_neg (p.gamma1_pos.trans_le p.gamma_le) p.gamma2_lt_one).ne
  have hC : 0 < C := add_pos_of_pos_of_nonneg zero_lt_one
    (div_nonneg (Real.log_pos p.one_lt_gamma3).le hZ.le)
  refine ⟨1 / decreaseCoefficient p L theta,
    1 / decreaseCoefficient p L theta * C, 1 / (2 * |Real.log p.gamma2|),
    |Real.log (c / delta0)| / |Real.log p.gamma2| + 2,
    div_pos zero_lt_one hκ, mul_pos (div_pos zero_lt_one hκ) hC,
    div_pos zero_lt_one (by positivity),
    add_pos_of_nonneg_of_pos (div_nonneg (abs_nonneg _) hZ.le) (by norm_num), ?_⟩
  intro tolerance ht _ht1 x s delta hx hd hprefix
  have he : 0 < Real.sqrt tolerance := Real.sqrt_pos.mpr ht
  obtain ⟨K, hK, hfirst, hfun, hderiv⟩ := exists_firstOrder_with_cost
    (p := p) (epsilon := Real.sqrt tolerance) he htheta hf hL hlow
    (fun n hn => hprefix n (by simpa [Real.sq_sqrt ht.le] using hn))
  have hpow : (Real.sqrt tolerance) ^ 3 = tolerance ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast (Real.sqrt tolerance) 3, Real.sqrt_eq_rpow,
      ← Real.rpow_mul ht.le]
    norm_num
  rw [Real.sq_sqrt ht.le] at hK hfirst
  rw [hpow, hx, hd, Real.log_sqrt ht.le, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hfun
  rw [hpow, hx] at hderiv
  refine ⟨K, hK, hfirst, ?_, ?_⟩
  · convert hfun using 1
    dsimp [C, c]
    ring
  · convert hderiv using 1
    ring

/-- A finite joint-stationarity prefix, including the current-curvature boundary rule. -/
structure JointPrefix [CompleteSpace E] (p : TrustRegion.Parameters)
    (theta epsilon2 : ℝ) (f : E → ℝ) (x s : ℕ → E)
    (delta : ℕ → ℝ) (N : ℕ) : Prop extends
    TrialTrace p theta epsilon2 f x s delta N where
  boundary : ∀ k < N, TrustRegionSecondOrder.curvature f (x k) < -epsilon2 →
    ‖s k‖ = delta k

/-- Objective value with a half-decrease credit at points satisfying the curvature test.
This credit pays for a transition from good current curvature to bad successor curvature. -/
def curvaturePotential [CompleteSpace E] (f : E → ℝ) (epsilon2 d : ℝ) (y : E) : ℝ :=
  f y + if -epsilon2 ≤ TrustRegionSecondOrder.curvature f y then d / 2 else 0

/-- Every accepted trial with a nonstationary successor pays half the mixed decrease in
curvature potential. The boundary rule is used at the current point only. -/
theorem JointPrefix.potential_decrease [CompleteSpace E]
    {epsilon1 epsilon2 L : ℝ} (h : JointPrefix p theta epsilon2 f x s delta N)
    (hf : CubicRegularization.HessianLipschitz f L) (hL : 1 ≤ L) (he : 0 < epsilon1)
    {k : ℕ} (hk : k < N) (hs : p.eta1 ≤ ratio f (x k) (s k))
    (hn : ¬Stationary true f epsilon1 epsilon2 (x (k + 1))) :
    let d := decreaseCoefficient p L theta * min (epsilon2 ^ 3) (epsilon1 ^ 2 / epsilon2)
    d / 2 ≤ curvaturePotential f epsilon2 d (x k) -
      curvaturePotential f epsilon2 d (x (k + 1)) := by
  dsimp only
  let d := decreaseCoefficient p L theta * min (epsilon2 ^ 3) (epsilon1 ^ 2 / epsilon2)
  have hd : 0 < d := mul_pos (decreaseCoefficient_pos p hL h.theta_pos)
    (lt_min (pow_pos h.epsilon_pos _) (div_pos (sq_pos_of_pos he) h.epsilon_pos))
  change d / 2 ≤ curvaturePotential f epsilon2 d (x k) -
    curvaturePotential f epsilon2 d (x (k + 1))
  have hm := h.toTrialTrace.objective_nonincrease hk
  by_cases hc : -epsilon2 ≤ TrustRegionSecondOrder.curvature f (x k)
  · by_cases hc' : -epsilon2 ≤ TrustRegionSecondOrder.curvature f (x (k + 1))
    · have hg : epsilon1 < ‖gradient f (x (k + 1))‖ := by
        by_contra hg
        exact hn ⟨le_of_not_gt hg, fun _ => hc'⟩
      have hh := h.toTrialTrace.accepted_budget hf hL he hk hs hg.le
      change d ≤ _ at hh
      simp only [curvaturePotential, ite_eq_left hc, ite_eq_left hc']
      linarith
    · simp only [curvaturePotential, ite_eq_left hc, ite_eq_right hc']
      linarith
  · have hb := h.boundary k hk (lt_of_not_ge hc)
    have hh := h.toTrialTrace.boundary_decrease hf hL hk hs hb
    have hmin := mul_le_mul_of_nonneg_left
      (min_le_left (epsilon2 ^ 3) (epsilon1 ^ 2 / epsilon2))
      (decreaseCoefficient_pos p hL h.theta_pos).le
    change d ≤ _ at hmin
    by_cases hc' : -epsilon2 ≤ TrustRegionSecondOrder.curvature f (x (k + 1))
    · simp only [curvaturePotential, ite_eq_right hc, ite_eq_left hc']
      linarith
    · simp only [curvaturePotential, ite_eq_right hc, ite_eq_right hc']
      linarith

/-- A prefix failing the joint test through its endpoint has at most twice the objective
budget in successful trials, plus one credit for its initial curvature state. -/
theorem JointPrefix.success_count_le [CompleteSpace E]
    {epsilon1 epsilon2 L low : ℝ} (h : JointPrefix p theta epsilon2 f x s delta N)
    (hf : CubicRegularization.HessianLipschitz f L) (hL : 1 ≤ L) (he : 0 < epsilon1)
    (hlow : low ≤ f (x N))
    (htest : ∀ j ≤ N, ¬Stationary true f epsilon1 epsilon2 (x j)) :
    (ParameterUpdates.successCount (fun k => p.eta1 ≤ ratio f (x k) (s k)) N : ℝ) ≤
      2 * (f (x 0) - low) /
        (decreaseCoefficient p L theta * min (epsilon2 ^ 3) (epsilon1 ^ 2 / epsilon2)) + 1 := by
  classical
  let d := decreaseCoefficient p L theta * min (epsilon2 ^ 3) (epsilon1 ^ 2 / epsilon2)
  have hd : 0 < d := mul_pos (decreaseCoefficient_pos p hL h.theta_pos)
    (lt_min (pow_pos h.epsilon_pos _) (div_pos (sq_pos_of_pos he) h.epsilon_pos))
  have hlo : low ≤ curvaturePotential f epsilon2 d (x N) := by
    unfold curvaturePotential
    split_ifs <;> linarith
  have hinit : curvaturePotential f epsilon2 d (x 0) ≤ f (x 0) + d / 2 := by
    unfold curvaturePotential
    split_ifs <;> linarith
  have hdec : ∀ k < N, p.eta1 ≤ ratio f (x k) (s k) →
      d / 2 ≤ curvaturePotential f epsilon2 d (x k) -
        curvaturePotential f epsilon2 d (x (k + 1)) :=
    fun k hk hs => h.potential_decrease hf hL he hk hs (htest (k + 1) (by omega))
  have hmono : ∀ k < N, curvaturePotential f epsilon2 d (x (k + 1)) ≤
      curvaturePotential f epsilon2 d (x k) := by
    intro k hk
    by_cases hs : p.eta1 ≤ ratio f (x k) (s k)
    · have hh := hdec k hk hs
      linarith
    · rw [h.iterate k hk, ite_eq_right hs]
  have hh := EvaluationComplexity.card_mul_le_gap
    (S := (Finset.range N).filter (fun k => p.eta1 ≤ ratio f (x k) (s k)))
    (Finset.filter_subset _ _) hlo hmono (by
      intro k hk
      obtain ⟨hk, hs⟩ := Finset.mem_filter.mp hk
      exact hdec k (Finset.mem_range.mp hk) hs)
  change (ParameterUpdates.successCount _ N : ℝ) * (d / 2) ≤ _ at hh
  change _ ≤ 2 * (f (x 0) - low) / d + 1
  have hb : (ParameterUpdates.successCount (fun k => p.eta1 ≤ ratio f (x k) (s k)) N : ℝ) - 1 ≤
      2 * (f (x 0) - low) / d := (le_div_iff₀ hd).mpr (by nlinarith only [hh, hinit])
  linarith only [hb]

/-- Total trials in a prefix whose endpoint still fails joint stationarity. -/
theorem JointPrefix.prefix_count_le [CompleteSpace E]
    {L tolerance epsilon2 low : ℝ}
    (h : JointPrefix p theta epsilon2 f x s delta N)
    (hf : CubicRegularization.HessianLipschitz f L) (hL : 1 ≤ L) (ht : 0 < tolerance)
    (hlow : low ≤ f (x N))
    (htest : ∀ j ≤ N, ¬Stationary true f tolerance epsilon2 (x j)) :
    (N : ℝ) ≤ (2 * (f (x 0) - low) /
      (decreaseCoefficient p L theta * min (epsilon2 ^ 3) (tolerance ^ 2 / epsilon2)) + 1) *
        (1 + Real.log p.gamma3 / |Real.log p.gamma2|) +
      (|Real.log (((1 - p.eta2) * p.gamma1 / L) / delta 0)| + |Real.log epsilon2|) /
        |Real.log p.gamma2| := by
  have hZ : 0 < |Real.log p.gamma2| := abs_pos.mpr
    (Real.log_neg (p.gamma1_pos.trans_le p.gamma_le) p.gamma2_lt_one).ne
  have hC : 0 ≤ 1 + Real.log p.gamma3 / |Real.log p.gamma2| :=
    add_nonneg zero_le_one (div_nonneg (Real.log_pos p.one_lt_gamma3).le hZ.le)
  exact (h.toTrialTrace.total_count_le_logarithmic hf hL).trans
    (add_le_add (mul_le_mul_of_nonneg_right
      (h.success_count_le hf hL ht hlow htest) hC) le_rfl)

/-- Local trial and curvature laws until the first joint test imply actual termination and
explicit function and cached-derivative budgets on the mixed tolerance scale. -/
theorem exists_joint_with_cost [CompleteSpace E] {epsilon1 epsilon2 L low : ℝ}
    (he1 : 0 < epsilon1) (he2 : 0 < epsilon2) (htheta : 0 < theta)
    (hf : CubicRegularization.HessianLipschitz f L) (hL : 1 ≤ L)
    (hlow : ∀ y, low ≤ f y)
    (hprefix : ∀ n, (∀ j < n, ¬Stationary true f epsilon1 epsilon2 (x j)) →
      JointPrefix p theta epsilon2 f x s delta n) :
    ∃ K : ℕ, Stationary true f epsilon1 epsilon2 (x K) ∧
      (∀ j < K, ¬Stationary true f epsilon1 epsilon2 (x j)) ∧
      (functionEvaluations K : ℝ) ≤
        (2 * (f (x 0) - low) /
          (decreaseCoefficient p L theta * min (epsilon2 ^ 3) (epsilon1 ^ 2 / epsilon2)) + 1) *
          (1 + Real.log p.gamma3 / |Real.log p.gamma2|) +
        (|Real.log (((1 - p.eta2) * p.gamma1 / L) / delta 0)| +
          |Real.log epsilon2|) / |Real.log p.gamma2| + 2 ∧
      (derivativeEvaluations p f x s K : ℝ) ≤
        2 * (f (x 0) - low) /
          (decreaseCoefficient p L theta * min (epsilon2 ^ 3) (epsilon1 ^ 2 / epsilon2)) + 3 := by
  classical
  let D := 2 * (f (x 0) - low) /
    (decreaseCoefficient p L theta * min (epsilon2 ^ 3) (epsilon1 ^ 2 / epsilon2))
  let C := 1 + Real.log p.gamma3 / |Real.log p.gamma2|
  let B := (D + 1) * C +
    (|Real.log (((1 - p.eta2) * p.gamma1 / L) / delta 0)| +
      |Real.log epsilon2|) / |Real.log p.gamma2|
  have hD : 0 ≤ D := div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr (hlow _)))
    (mul_pos (decreaseCoefficient_pos p hL htheta)
      (lt_min (pow_pos he2 _) (div_pos (sq_pos_of_pos he1) he2))).le
  have hC : 0 ≤ C := add_nonneg zero_le_one
    (div_nonneg (Real.log_pos p.one_lt_gamma3).le (abs_nonneg _))
  have hB : 0 ≤ B := add_nonneg (mul_nonneg (by linarith) hC)
    (div_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _))
  have hbound : ∀ n, (∀ j < n, ¬Stationary true f epsilon1 epsilon2 (x j)) →
      (n : ℝ) ≤ B + 1 := by
    intro n hn
    cases n with
    | zero => simp only [Nat.cast_zero]; linarith only [hB]
    | succ n =>
      have h := hprefix n (fun j hj => hn j (by omega))
      have hh := h.prefix_count_le hf hL he1 (hlow _) (fun j hj => hn j (by omega))
      change (n : ℝ) ≤ B at hh
      push_cast
      linarith only [hh]
  obtain ⟨K, _, hK, hfirst⟩ := EvaluationComplexity.exists_first_of_prefix_bound hbound
  refine ⟨K, hK, hfirst, ?_, ?_⟩
  · have hh := hbound K hfirst
    simp only [functionEvaluations, Nat.cast_add, Nat.cast_one]
    change (K : ℝ) + 1 ≤ B + 2
    linarith only [hh]
  · cases K with
    | zero => simpa [derivativeEvaluations, ParameterUpdates.successCount, D] using
        (by linarith only [hD] : (1 : ℝ) ≤ D + 3)
    | succ n =>
      have h := hprefix n (fun j hj => hfirst j (by omega))
      have hh := h.success_count_le hf hL he1 (hlow _) (fun j hj => hfirst j (by omega))
      have hc : ParameterUpdates.successCount
          (fun j => p.eta1 ≤ ratio f (x j) (s j)) (n + 1) ≤
          ParameterUpdates.successCount (fun j => p.eta1 ≤ ratio f (x j) (s j)) n + 1 := by
        simp only [ParameterUpdates.successCount, Finset.range_add_one, Finset.filter_insert]
        split_ifs
        · exact Finset.card_insert_le _ _
        · omega
      have hc' : (ParameterUpdates.successCount
          (fun j => p.eta1 ≤ ratio f (x j) (s j)) (n + 1) : ℝ) ≤
          (ParameterUpdates.successCount (fun j => p.eta1 ≤ ratio f (x j) (s j)) n : ℝ) + 1 := by
        exact_mod_cast hc
      simp only [derivativeEvaluations, Nat.cast_add, Nat.cast_one]
      change _ ≤ D + 3
      linarith only [hh, hc']

/-- A trace starting at its global objective lower bound cannot accept any strict-decrease
trial. Every iterate is therefore the initial point. -/
theorem TrialTrace.iterate_eq_initial_of_gap_zero
    (h : TrialTrace p theta epsilon f x s delta N) {low : ℝ}
    (hlow : ∀ k ≤ N, low ≤ f (x k)) (hgap : f (x 0) = low) {k : ℕ} (hk : k ≤ N) :
    x k = x 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hi := ih (by omega)
    have hs : ¬p.eta1 ≤ ratio f (x k) (s k) := by
      intro hs
      have hh := h.accepted_decrease (k := k) (by omega) hs
      have hp := mul_pos p.eta1_pos (h.predicted_pos (k := k) (by omega))
      rw [hi] at hp
      rw [hi, hgap] at hh
      have hlo := hlow (k + 1) (by omega)
      linarith only [hh, hp, hlo]
    rw [h.iterate k (by omega), ite_eq_right hs, hi]

/-- Uniform second-order complexity constants, selected before either tolerance or any legal
trace. The derivative budget has the textbook's additive one: its existential constant can
absorb the two transient curvature credits whenever the fixed initial gap is positive. -/
theorem exists_joint_complexity_constants [CompleteSpace E]
    (p : TrustRegion.Parameters) (theta : ℝ) (f : E → ℝ) (x0 : E) (delta0 : ℝ)
    {L low : ℝ} (htheta : 0 < theta)
    (hf : CubicRegularization.HessianLipschitz f L) (hL : 1 ≤ L)
    (hlow : ∀ y, low ≤ f y) :
    ∃ kS kA kC kD : ℝ, 0 < kS ∧ 0 < kA ∧ 0 < kC ∧ 0 < kD ∧
      ∀ epsilon1 epsilon2 : ℝ, 0 < epsilon1 →
        0 < epsilon2 → epsilon2 ≤ 1 →
      ∀ (x s : ℕ → E) (delta : ℕ → ℝ), x 0 = x0 → delta 0 = delta0 →
        (∀ n, (∀ j < n, ¬Stationary true f epsilon1 epsilon2 (x j)) →
          JointPrefix p theta epsilon2 f x s delta n) →
        ∃ K : ℕ, Stationary true f epsilon1 epsilon2 (x K) ∧
          (∀ j < K, ¬Stationary true f epsilon1 epsilon2 (x j)) ∧
          (functionEvaluations K : ℝ) ≤
            kA * ((f x0 - low) / min (epsilon2 ^ 3) (epsilon1 ^ 2 / epsilon2)) +
              kD * |Real.log epsilon2| + kC ∧
          (derivativeEvaluations p f x s K : ℝ) ≤
            kS * ((f x0 - low) / min (epsilon2 ^ 3) (epsilon1 ^ 2 / epsilon2)) + 1 := by
  let c := (1 - p.eta2) * p.gamma1 / L
  let C := 1 + Real.log p.gamma3 / |Real.log p.gamma2|
  let g := f x0 - low
  let κ := decreaseCoefficient p L theta
  have hg : 0 ≤ g := sub_nonneg.mpr (hlow _)
  have hκ : 0 < κ := decreaseCoefficient_pos p hL htheta
  have hZ : 0 < |Real.log p.gamma2| := abs_pos.mpr
    (Real.log_neg (p.gamma1_pos.trans_le p.gamma_le) p.gamma2_lt_one).ne
  have hC : 0 < C := add_pos_of_pos_of_nonneg zero_lt_one
    (div_nonneg (Real.log_pos p.one_lt_gamma3).le hZ.le)
  refine ⟨2 / κ + 2 / g, 2 / κ * C,
    C + |Real.log (c / delta0)| / |Real.log p.gamma2| + 2,
    1 / |Real.log p.gamma2|,
    add_pos_of_pos_of_nonneg (div_pos (by norm_num) hκ) (div_nonneg (by norm_num) hg),
    mul_pos (div_pos (by norm_num) hκ) hC,
    by positivity, div_pos zero_lt_one hZ, ?_⟩
  intro epsilon1 epsilon2 he1 he2 he21 x s delta hx hd hprefix
  obtain ⟨K, hK, hfirst, hfun, hderiv⟩ := exists_joint_with_cost he1 he2 htheta hf hL hlow hprefix
  have hfun' : (functionEvaluations K : ℝ) ≤
      (2 / κ * C) * (g / min (epsilon2 ^ 3) (epsilon1 ^ 2 / epsilon2)) +
        (1 / |Real.log p.gamma2|) * |Real.log epsilon2| +
        (C + |Real.log (c / delta0)| / |Real.log p.gamma2| + 2) := by
    rw [hx, hd] at hfun
    convert hfun using 1
    dsimp [C, c, κ, g]
    ring
  by_cases hgz : g = 0
  · have hi := (hprefix K hfirst).toTrialTrace.iterate_eq_initial_of_gap_zero
      (fun k _ => hlow (x k))
      (by rw [hx]; dsimp [g] at hgz; linarith only [hgz]) (k := K) le_rfl
    have hzero : K = 0 := by
      by_contra hn
      exact hfirst 0 (Nat.pos_of_ne_zero hn) (by simpa only [hi] using hK)
    refine ⟨K, hK, hfirst, hfun', ?_⟩
    change (derivativeEvaluations p f x s K : ℝ) ≤
      (2 / κ + 2 / g) * (g / min (epsilon2 ^ 3) (epsilon1 ^ 2 / epsilon2)) + 1
    simp [hzero, derivativeEvaluations, ParameterUpdates.successCount, hgz]
  · have hgp : 0 < g := lt_of_le_of_ne hg (Ne.symm hgz)
    let m := min (epsilon2 ^ 3) (epsilon1 ^ 2 / epsilon2)
    have hm : 0 < m := lt_min (pow_pos he2 _) (div_pos (sq_pos_of_pos he1) he2)
    have hm1 : m ≤ 1 := (min_le_left _ _).trans (pow_le_one₀ he2.le he21)
    have habsorb : 2 ≤ (2 / g) * (g / m) := by
      have heq : (2 / g) * (g / m) = 2 / m := by field_simp
      rw [heq]
      exact (le_div_iff₀ hm).mpr (by linarith only [hm1])
    rw [hx] at hderiv
    refine ⟨K, hK, hfirst, hfun', ?_⟩
    have heq : 2 * g / (κ * m) = (2 / κ) * (g / m) := by ring
    change _ ≤ 2 * g / (κ * m) + 3 at hderiv
    change _ ≤ (2 / κ + 2 / g) * (g / m) + 1
    rw [heq] at hderiv
    nlinarith only [hderiv, habsorb]

end Optimization.RegularizedTrustRegion
