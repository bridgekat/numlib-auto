import Numlib.Optimization.UniversalRegularizationDecrease
import Numlib.Optimization.EvaluationComplexity

/-!
# Actual stopping and oracle budgets for universal regularization

Finite legal prefixes telescope genuine accepted objective payments. Multiplicative legal
updates bound all trials, and the literal oracle schedule counts rejected and terminal checks.
-/

noncomputable section
namespace Optimization.ParameterUpdates

/-- A finite-prefix version of the multiplicative count bound. The continuation used in
its proof is constant and successful, so no continuation of the algorithm is assumed. -/
theorem total_count_le_of_prefix_upper_bound {u : ℕ → ℝ} {success : ℕ → Prop}
    {a b M : ℝ} {N : ℕ} (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : 1 < b)
    (hpos : ∀ k ≤ N, 0 < u k)
    (hsuccess : ∀ k < N, success k → a * u k ≤ u (k + 1))
    (hfailure : ∀ k < N, ¬success k → b * u k ≤ u (k + 1)) (hM : u N ≤ M) :
    (N : ℝ) ≤ (successCount success N : ℝ) * (1 + |Real.log a| / Real.log b) +
      Real.log (M / u 0) / Real.log b := by
  classical
  let v := fun k => u (min k N)
  let good := fun k => k < N → success k
  have hv : UpdateBounds v good a b := by
    refine ⟨fun k => hpos _ (min_le_right _ _), ?_, ?_⟩
    · intro k hk
      by_cases hkN : k < N
      · dsimp [v]
        rw [min_eq_left (by omega : k ≤ N), min_eq_left (by omega : k + 1 ≤ N)]
        exact hsuccess k hkN (hk hkN)
      · dsimp [v]
        rw [min_eq_right (by omega : N ≤ k), min_eq_right (by omega : N ≤ k + 1)]
        exact mul_le_of_le_one_left (hpos N le_rfl).le ha.2.le
    · intro k hk
      have hkN : k < N := by by_contra hh; exact hk (fun h => (hh h).elim)
      have hbad : ¬success k := fun hh => hk (fun _ => hh)
      dsimp [v]
      rw [min_eq_left (by omega : k ≤ N), min_eq_left (by omega : k + 1 ≤ N)]
      exact hfailure k hkN hbad
  have hc : successCount good N = successCount success N := by
    unfold successCount
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, good]
    tauto
  have hh := total_count_le_of_upper_bound hv ha hb N (by simpa [v] using hM)
  simpa only [hc, v, min_self, Nat.zero_min] using hh

end Optimization.ParameterUpdates
namespace Optimization.UniversalRegularization

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
variable {q p : ℕ} {r H beta : ℝ} {a : Parameters q p r}
  {f : E → ℝ} {x s : ℕ → E} {sigma : ℕ → ℝ} {N : ℕ}

/-- The number of accepted nonterminal trials is bounded by genuine objective decrease. -/
theorem RunPrefix.success_count_le (h : RunPrefix a f x s sigma N)
    (hf : HolderDerivative f p H beta) (hexp : (q : ℝ) < (p : ℝ) + beta)
    (htr : (p : ℝ) + beta ≤ r) {low : ℝ} (hlow : low ≤ f (x N)) :
    (ParameterUpdates.successCount (fun k => Accepted a f (x k) (sigma k) (s k)) N : ℝ) ≤
      (f (x 0) - low) / (decreaseConstant a H ((p : ℝ) + beta) (sigma 0) *
        toleranceRadius a ((p : ℝ) + beta) ^ ((p : ℝ) + beta)) := by
  classical
  have hd : 0 < decreaseConstant a H ((p : ℝ) + beta) (sigma 0) *
      toleranceRadius a ((p : ℝ) + beta) ^ ((p : ℝ) + beta) :=
    mul_pos (decreaseConstant_pos h.initial_positive)
      (Real.rpow_pos_of_pos toleranceRadius_pos _)
  apply (le_div_iff₀ hd).mpr
  exact EvaluationComplexity.card_mul_le_gap (u := fun k => f (x k)) (n := N)
    (Finset.filter_subset _ _) hlow
    (fun k hk => h.objective_nonincrease hk)
    (fun k hk => h.successful_decrease hf hexp htr
      (Finset.mem_range.mp (Finset.mem_filter.mp hk).1) (Finset.mem_filter.mp hk).2)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Actual accepted updates contract by at most `gamma1`, while every rejection expands
by at least `gamma2`, even when rejection is caused by an activated length test. -/
theorem RunPrefix.total_count_le (h : RunPrefix a f x s sigma N) {M : ℝ}
    (hM : sigma N ≤ M) :
    (N : ℝ) ≤
      (ParameterUpdates.successCount (fun k => Accepted a f (x k) (sigma k) (s k)) N : ℝ) *
        (1 + |Real.log a.gamma1| / Real.log a.gamma2) +
      Real.log (M / sigma 0) / Real.log a.gamma2 := by
  apply ParameterUpdates.total_count_le_of_prefix_upper_bound
    ⟨a.gamma1_pos, a.gamma1_lt_one⟩ a.gamma2_gt_one (fun _ hk => h.positive hk) _ _ hM
  · intro k hk ha
    by_cases hv : VerySuccessful a f (x k) (sigma k) (s k)
    · exact ((h.update k hk).1 hv).1
    · exact (mul_le_of_le_one_left (h.positive (by omega)).le a.gamma1_lt_one.le).trans
        ((h.update k hk).2.1 ha hv).1
  · intro k hk ha
    exact ((h.update k hk).2.2 ha).1

/-- The negative logarithm of the common tolerance radius is bounded by the sum of the
activated tolerance logarithms with their exact derivative exponents. -/
theorem neg_log_toleranceRadius_le {t : ℝ} (hexp : (q : ℝ) < t) :
    -Real.log (toleranceRadius a t) ≤ |Real.log (a.epsilon 0)| / (t - 1) +
      (if 2 ≤ q then |Real.log (a.epsilon 1)| / (t - 2) else 0) := by
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast a.order_pos
  have ht : 1 < t := by linarith
  have he := a.epsilon_pos 0 (by have := a.order_pos; simp only [Fin.val_zero]; omega)
  have he1 := a.epsilon_le_one 0 (by have := a.order_pos; simp only [Fin.val_zero]; omega)
  have hlog0 : Real.log (a.epsilon 0) ≤ 0 := Real.log_nonpos he.le he1
  have hroot0 : -Real.log (a.epsilon 0 ^ (t - 1)⁻¹) =
      |Real.log (a.epsilon 0)| / (t - 1) := by
    rw [Real.log_rpow he, abs_of_nonpos hlog0]
    ring
  rw [toleranceRadius]
  split_ifs with hq
  · have hqr2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
    have ht2 : 2 < t := by linarith
    have he' := a.epsilon_pos 1 (by simp only [Fin.val_one]; omega)
    have he1' := a.epsilon_le_one 1 (by simp only [Fin.val_one]; omega)
    have hlog1 : Real.log (a.epsilon 1) ≤ 0 := Real.log_nonpos he'.le he1'
    have hroot1 : -Real.log (a.epsilon 1 ^ (t - 2)⁻¹) =
        |Real.log (a.epsilon 1)| / (t - 2) := by
      rw [Real.log_rpow he', abs_of_nonpos hlog1]
      ring
    rcases le_total (a.epsilon 0 ^ (t - 1)⁻¹) (a.epsilon 1 ^ (t - 2)⁻¹) with hh | hh
    · rw [min_eq_left hh, hroot0]
      exact le_add_of_nonneg_right (by positivity)
    · rw [min_eq_right hh, hroot1]
      exact le_add_of_nonneg_left (by positivity)
  · rw [hroot0, add_zero]

/-- Explicit successful-trial, all-trial and logarithmic constants, fixed independently
of accuracy and trace. The additive constant includes initial and terminal oracle checks. -/
structure ComplexityConstants where
  success : ℝ
  all : ℝ
  firstLog : ℝ
  secondLog : ℝ
  offset : ℝ

/-- The concrete uniform constants in the evaluation bound. -/
def complexityConstants (a : Parameters q p r) (H t initial : ℝ) : ComplexityConstants where
  success := (decreaseConstant a H t initial)⁻¹
  all := (1 + |Real.log a.gamma1| / Real.log a.gamma2) / decreaseConstant a H t initial
  firstLog := (r - t) / (t - 1) / Real.log a.gamma2
  secondLog := if 2 ≤ q then (r - t) / (t - 2) / Real.log a.gamma2 else 0
  offset := 2 + Real.log (decreaseSigma a H t initial / initial) / Real.log a.gamma2

/-- The explicit accuracy factor, with exactly the active complexity powers. -/
def tolerancePower (a : Parameters q p r) (t : ℝ) : ℝ :=
  toleranceRadius a t ^ t

/-- The concrete budget includes the complete accepted-decrease bound and the two
logarithmic tolerance terms, independently charging every activated derivative trial. -/
def evaluationBudget (c : ComplexityConstants) (a : Parameters q p r) (t gap : ℝ) : ℝ :=
  c.all * gap / tolerancePower a t + c.firstLog * |Real.log (a.epsilon 0)| +
    c.secondLog * |Real.log (a.epsilon 1)| + c.offset

/-- Every actual nonterminal prefix has a uniform explicit bound on all processed trials. -/
theorem RunPrefix.explicit_count_le (h : RunPrefix a f x s sigma N)
    (hf : HolderDerivative f p H beta) (hexp : (q : ℝ) < (p : ℝ) + beta)
    (htr : (p : ℝ) + beta ≤ r) {low : ℝ} (hlow : low ≤ f (x N)) :
    (N : ℝ) + 2 ≤ evaluationBudget (complexityConstants a H ((p : ℝ) + beta) (sigma 0))
      a ((p : ℝ) + beta) (f (x 0) - low) := by
  let t := (p : ℝ) + beta
  let z := toleranceRadius a t
  let M := decreaseSigma a H t (sigma 0)
  let C := decreaseConstant a H t (sigma 0)
  let L := Real.log a.gamma2
  have hz : 0 < z := toleranceRadius_pos
  have hM : 0 < M := decreaseSigma_pos h.initial_positive
  have hC : 0 < C := decreaseConstant_pos h.initial_positive
  have hL : 0 < L := Real.log_pos a.gamma2_gt_one
  have hcount := h.total_count_le (h.sigma_upper_radius hf hexp htr le_rfl)
  have hs := h.success_count_le hf hexp htr hlow
  have hfactor : 0 ≤ 1 + |Real.log a.gamma1| / L := by positivity
  have hsuccess := mul_le_mul_of_nonneg_right hs hfactor
  have hlog : Real.log (M * z ^ (t - r) / sigma 0) ≤ Real.log (M / sigma 0) +
      (r - t) * (|Real.log (a.epsilon 0)| / (t - 1) +
        (if 2 ≤ q then |Real.log (a.epsilon 1)| / (t - 2) else 0)) := by
    have hh := mul_le_mul_of_nonneg_left (neg_log_toleranceRadius_le (a := a) hexp)
      (sub_nonneg.mpr htr)
    rw [Real.log_div (mul_pos hM (Real.rpow_pos_of_pos hz _)).ne' h.initial_positive.ne',
      Real.log_mul hM.ne' (Real.rpow_pos_of_pos hz _).ne', Real.log_rpow hz,
      Real.log_div hM.ne' h.initial_positive.ne']
    dsimp [z] at *
    nlinarith only [hh]
  have hlogdiv := div_le_div_of_nonneg_right hlog hL.le
  have hbudget : (f (x 0) - low) / (C * z ^ t) *
      (1 + |Real.log a.gamma1| / L) +
      (Real.log (M / sigma 0) + (r - t) * (|Real.log (a.epsilon 0)| / (t - 1) +
        (if 2 ≤ q then |Real.log (a.epsilon 1)| / (t - 2) else 0))) / L + 2 =
      evaluationBudget (complexityConstants a H t (sigma 0)) a t (f (x 0) - low) := by
    dsimp [evaluationBudget, complexityConstants, tolerancePower, C, M, z, L]
    split_ifs <;> ring
  rw [← hbudget]
  dsimp [L] at hsuccess hlogdiv
  linarith only [hcount, hsuccess, hlogdiv]

/-- The uniform parameter coefficient always contains the initial parameter. -/
theorem le_decreaseSigma {t initial : ℝ} : initial ≤ decreaseSigma a H t initial := by
  unfold decreaseSigma uniformSigma
  split_ifs <;> exact le_max_left _ _

/-- Uniform constants agree for all tolerance choices with the same fixed nonaccuracy
parameters. This includes the logarithmic and initial-cache constants. -/
theorem complexityConstants_eq_of_parameters {b : Parameters q p r} {t initial : ℝ}
    (heta1 : a.eta1 = b.eta1) (heta2 : a.eta2 = b.eta2)
    (hgamma1 : a.gamma1 = b.gamma1) (hgamma2 : a.gamma2 = b.gamma2)
    (hgamma3 : a.gamma3 = b.gamma3) (htheta : a.theta = b.theta)
    (halpha : a.alpha = b.alpha) :
    complexityConstants a H t initial = complexityConstants b H t initial := by
  simp only [complexityConstants, decreaseConstant, decreaseSigma, uniformSigma,
    uniformSuccessThreshold, heta1, heta2, hgamma1, hgamma2, hgamma3, htheta, halpha]

/-- The initial and terminal oracle allowance is available even for an initial stop. -/
theorem two_le_evaluationBudget {t initial gap : ℝ} (hi : 0 < initial)
    (hexp : (q : ℝ) < t) (htr : t ≤ r) (hgap : 0 ≤ gap) :
    2 ≤ evaluationBudget (complexityConstants a H t initial) a t gap := by
  have hM : 0 < decreaseSigma a H t initial := decreaseSigma_pos hi
  have hratio : 1 ≤ decreaseSigma a H t initial / initial :=
    (le_div_iff₀ hi).mpr (by simpa using (le_decreaseSigma (a := a) (H := H) (t := t)))
  have hlog : 0 ≤ Real.log (decreaseSigma a H t initial / initial) := Real.log_nonneg hratio
  have hL : 0 < Real.log a.gamma2 := Real.log_pos a.gamma2_gt_one
  have hC : 0 < decreaseConstant a H t initial := decreaseConstant_pos hi
  have hP : 0 < tolerancePower a t := Real.rpow_pos_of_pos toleranceRadius_pos _
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast a.order_pos
  have ht : 1 < t := by linarith
  dsimp [evaluationBudget, complexityConstants]
  have hterm0 : 0 ≤ (1 + |Real.log a.gamma1| / Real.log a.gamma2) /
      decreaseConstant a H t initial * gap / tolerancePower a t := by positivity
  have hterm1 : 0 ≤ (r - t) / (t - 1) / Real.log a.gamma2 *
      |Real.log (a.epsilon 0)| := by positivity
  have hterm2 : 0 ≤ (if 2 ≤ q then (r - t) / (t - 2) / Real.log a.gamma2 else 0) *
      |Real.log (a.epsilon 1)| := by
    split_ifs with hq
    · have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
      have ht2 : 2 < t := by linarith
      positivity
    · simp only [zero_mul, le_refl]
  have hlast : 0 ≤ Real.log (decreaseSigma a H t initial / initial) / Real.log a.gamma2 :=
    div_nonneg hlog hL.le
  linarith only [hterm0, hterm1, hterm2, hlast]

/-- Legal prefix availability: until a true activated stopping observation is found, the
actual algorithm can compute its next model step and process every nonterminal prefix.
It contains no stopping, objective-decrease, quality or count conclusion. -/
structure Available (a : Parameters q p r) (f : E → ℝ) (x s : ℕ → E)
    (sigma : ℕ → ℝ) : Prop where
  initial_positive : 0 < sigma 0
  prefixes : ∀ N, (∀ i ≤ N, ¬Stationary a f (observation x s i)) → RunPrefix a f x s sigma N
  next : ∀ N, RunPrefix a f x s sigma N → ComputedStep a f (x N) (sigma N) (s N)

/-- Legal prefix availability and a lower-bounded objective force a true first stop;
no termination bound or eventual-quality statement is assumed by availability. -/
theorem Available.exists_first_run (h : Available a f x s sigma)
    (hf : HolderDerivative f p H beta) (hexp : (q : ℝ) < (p : ℝ) + beta)
    (htr : (p : ℝ) + beta ≤ r) {low : ℝ} (hlow : ∀ z, low ≤ f z) :
    ∃ N, IsRun a f x s sigma N ∧
      (N : ℝ) + 1 ≤ evaluationBudget
        (complexityConstants a H ((p : ℝ) + beta) (sigma 0))
        a ((p : ℝ) + beta) (f (x 0) - low) := by
  let B := evaluationBudget (complexityConstants a H ((p : ℝ) + beta) (sigma 0))
    a ((p : ℝ) + beta) (f (x 0) - low)
  have hB : 2 ≤ B := two_le_evaluationBudget h.initial_positive hexp htr (sub_nonneg.mpr (hlow _))
  have hbound : ∀ n, (∀ j < n, ¬Stationary a f (observation x s j)) → (n : ℝ) ≤ B := by
    intro n hn
    cases n with
    | zero => norm_num; linarith
    | succ n =>
      have hp := h.prefixes n (fun i hi => hn i (by omega))
      have hb := hp.explicit_count_le hf hexp htr (hlow _)
      change (n : ℝ) + 2 ≤ B at hb
      push_cast
      linarith
  obtain ⟨N, _, hstat, hfirst⟩ := EvaluationComplexity.exists_first_of_prefix_bound hbound
  refine ⟨N, ?_, ?_⟩
  · refine ⟨h.initial_positive, ?_⟩
    cases N with
    | zero => exact Or.inl ⟨rfl, hstat⟩
    | succ M =>
      have hp := h.prefixes M (fun i hi => hfirst i (by omega))
      exact Or.inr ⟨M, rfl, hp, h.next M hp, hstat⟩
  · cases N with
    | zero => norm_num; linarith
    | succ M =>
      have hp := h.prefixes M (fun i hi => hfirst i (by omega))
      have hb := hp.explicit_count_le hf hexp htr (hlow _)
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hb

/-- Complete actual executions have the explicit active-query bound and the accepted-only
higher-derivative bound. Initial, rejected and terminal trial checks are all included. -/
theorem IsRun.evaluation_bounds (h : IsRun a f x s sigma N)
    (hf : HolderDerivative f p H beta) (hexp : (q : ℝ) < (p : ℝ) + beta)
    (htr : (p : ℝ) + beta ≤ r) {low : ℝ} (hlow : ∀ z, low ≤ f z) :
    (∀ j ≤ q, (evaluations a f x s sigma N j : ℝ) ≤
      evaluationBudget (complexityConstants a H ((p : ℝ) + beta) (sigma 0))
        a ((p : ℝ) + beta) (f (x 0) - low)) ∧
    (∀ j, q < j → j ≤ p → (evaluations a f x s sigma N j : ℝ) ≤
      (complexityConstants a H ((p : ℝ) + beta) (sigma 0)).success *
        (f (x 0) - low) / tolerancePower a ((p : ℝ) + beta) + 1) := by
  have hB := two_le_evaluationBudget (a := a) (H := H) h.1 hexp htr
    (sub_nonneg.mpr (hlow (x 0)))
  have hN : (N : ℝ) + 1 ≤ evaluationBudget
      (complexityConstants a H ((p : ℝ) + beta) (sigma 0))
      a ((p : ℝ) + beta) (f (x 0) - low) := by
    rcases h.2 with ⟨rfl, _⟩ | ⟨M, rfl, hp, _, _⟩
    · norm_num
      linarith
    · have hb := hp.explicit_count_le hf hexp htr (hlow _)
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hb
  refine ⟨?_, ?_⟩
  · intro j hj
    by_cases hj0 : j = 0
    · subst j
      rw [evaluations_value]
      have hm : max 1 N ≤ N + 1 := max_le (by omega) (by omega)
      exact (by exact_mod_cast hm : (max 1 N : ℕ) ≤ (N : ℝ) + 1).trans hN
    · rw [evaluations_active (by omega : 0 < j) hj]
      exact_mod_cast hN
  · intro j hj hjp
    rw [evaluations_high hj hjp]
    rcases h.2 with ⟨rfl, _⟩ | ⟨M, rfl, hp, _, _⟩
    · simp only [ite_eq_left, Nat.cast_zero]
      have hgap : 0 ≤ f (x 0) - low := sub_nonneg.mpr (hlow _)
      have hC := decreaseConstant_pos (a := a) (H := H) (t := (p : ℝ) + beta) h.1
      have hP : 0 < tolerancePower a ((p : ℝ) + beta) :=
        Real.rpow_pos_of_pos toleranceRadius_pos _
      dsimp [complexityConstants]
      positivity
    · simp only [Nat.add_sub_cancel, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
        ]
      have hs := hp.success_count_le hf hexp htr (hlow _)
      dsimp [complexityConstants, tolerancePower]
      push_cast
      convert add_le_add_left hs 1 using 1 <;> ring

/-- Uniform constants are positive where used, apart from logarithmic coefficients that
correctly vanish at the smoothness boundary or for an inactive second order. -/
theorem complexityConstants_signs {t initial : ℝ} (hi : 0 < initial)
    (hexp : (q : ℝ) < t) (htr : t ≤ r) :
    0 < (complexityConstants a H t initial).success ∧
    0 < (complexityConstants a H t initial).all ∧
    0 ≤ (complexityConstants a H t initial).firstLog ∧
    0 ≤ (complexityConstants a H t initial).secondLog ∧
    2 ≤ (complexityConstants a H t initial).offset := by
  have hC : 0 < decreaseConstant a H t initial := decreaseConstant_pos hi
  have hL : 0 < Real.log a.gamma2 := Real.log_pos a.gamma2_gt_one
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast a.order_pos
  have ht : 1 < t := by linarith
  have hrt : 0 ≤ r - t := sub_nonneg.mpr htr
  have hratio : 1 ≤ decreaseSigma a H t initial / initial :=
    (le_div_iff₀ hi).mpr (by simpa using (le_decreaseSigma (a := a) (H := H) (t := t)))
  have hlog := Real.log_nonneg hratio
  refine ⟨inv_pos.mpr hC, ?_, ?_, ?_, ?_⟩
  · exact div_pos (by positivity) hC
  · exact div_nonneg (div_nonneg hrt (by linarith)) hL.le
  · dsimp [complexityConstants]
    split_ifs with hq
    · have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
      exact div_nonneg (div_nonneg hrt (by linarith)) hL.le
    · exact le_rfl
  · dsimp [complexityConstants]
    linarith [div_nonneg hlog hL.le]

/-- Positive versions of the complexity constants. The second logarithmic coefficient
remains zero if curvature is inactive, since its tolerance has no constraints. -/
def positiveComplexityConstants (a : Parameters q p r) (H t initial : ℝ) :
    ComplexityConstants where
  success := (complexityConstants a H t initial).success
  all := (complexityConstants a H t initial).all
  firstLog := (complexityConstants a H t initial).firstLog + 1
  secondLog := if 2 ≤ q then (complexityConstants a H t initial).secondLog + 1 else 0
  offset := (complexityConstants a H t initial).offset + 1

/-- The positive versions only enlarge the explicit evaluation budget. -/
theorem evaluationBudget_le_positive {t initial gap : ℝ} :
    evaluationBudget (complexityConstants a H t initial) a t gap ≤
      evaluationBudget (positiveComplexityConstants a H t initial) a t gap := by
  dsimp [evaluationBudget, positiveComplexityConstants, complexityConstants]
  split_ifs <;> nlinarith only [abs_nonneg (Real.log (a.epsilon 0)),
    abs_nonneg (Real.log (a.epsilon 1))]

/-- The positive constants are positive for both active orders, with a zero coefficient
for the unused curvature tolerance. -/
theorem positiveComplexityConstants_signs {t initial : ℝ} (hi : 0 < initial)
    (hexp : (q : ℝ) < t) (htr : t ≤ r) :
    0 < (positiveComplexityConstants a H t initial).success ∧
    0 < (positiveComplexityConstants a H t initial).all ∧
    0 < (positiveComplexityConstants a H t initial).firstLog ∧
    (2 ≤ q → 0 < (positiveComplexityConstants a H t initial).secondLog) ∧
    0 < (positiveComplexityConstants a H t initial).offset := by
  obtain ⟨hs, ha, hb, hb', hc⟩ := complexityConstants_signs (a := a) (H := H) hi hexp htr
  refine ⟨hs, ha, by dsimp [positiveComplexityConstants]; linarith, ?_, ?_⟩
  · intro hq
    dsimp [positiveComplexityConstants]
    rw [ite_eq_left hq]
    linarith
  · dsimp [positiveComplexityConstants]
    linarith

/-- Fixed algorithm controls, excluding both accuracy tolerances. -/
structure SameControls (a b : Parameters q p r) : Prop where
  eta1 : a.eta1 = b.eta1
  eta2 : a.eta2 = b.eta2
  gamma1 : a.gamma1 = b.gamma1
  gamma2 : a.gamma2 = b.gamma2
  gamma3 : a.gamma3 = b.gamma3
  theta : a.theta = b.theta
  alpha : a.alpha = b.alpha

/-- The positive complexity constants are identical throughout a fixed-control family. -/
theorem SameControls.positiveComplexityConstants_eq {b : Parameters q p r}
    (h : SameControls a b) {t initial : ℝ} :
    positiveComplexityConstants a H t initial = positiveComplexityConstants b H t initial := by
  have hh := complexityConstants_eq_of_parameters (H := H) (t := t) (initial := initial)
    h.eta1 h.eta2 h.gamma1 h.gamma2 h.gamma3 h.theta h.alpha
  simp only [positiveComplexityConstants, hh]

/-- A positive power absorbs an absolute logarithm uniformly on `(0,1]`. -/
theorem rpow_mul_abs_log_le {epsilon d : ℝ} (he : 0 < epsilon) (he1 : epsilon ≤ 1)
    (hd : 0 < d) : epsilon ^ d * |Real.log epsilon| ≤ 1 / d := by
  have hl := Real.log_le_self (Real.rpow_nonneg he.le (-d))
  rw [Real.log_rpow he] at hl
  have hm := mul_le_mul_of_nonneg_right hl (Real.rpow_nonneg he.le d)
  rw [← Real.rpow_add he, neg_add_cancel, Real.rpow_zero] at hm
  rw [abs_of_nonpos (Real.log_nonpos he.le he1), le_div_iff₀ hd]
  nlinarith only [hm]

/-- The common complexity power is positive and at most one. -/
theorem tolerancePower_bounds {t : ℝ} (hexp : (q : ℝ) < t) :
    0 < tolerancePower a t ∧ tolerancePower a t ≤ 1 := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast a.order_pos
  have ht : 1 < t := by linarith
  have he := a.epsilon_pos 0 (by have := a.order_pos; simp only [Fin.val_zero]; omega)
  have he1 := a.epsilon_le_one 0 (by have := a.order_pos; simp only [Fin.val_zero]; omega)
  have hz1 : toleranceRadius a t ≤ 1 := toleranceRadius_le_first.trans
    (Real.rpow_le_one he.le he1 (inv_nonneg.mpr (by linarith)))
  exact ⟨Real.rpow_pos_of_pos toleranceRadius_pos _,
    Real.rpow_le_one toleranceRadius_pos.le hz1 (by linarith)⟩

/-- The explicit logarithmic budget is bounded by a single uniform coefficient times
the reciprocal complexity power. This gives the stated polynomial evaluation order. -/
theorem evaluationBudget_le_power {c : ComplexityConstants} {t gap : ℝ}
    (hexp : (q : ℝ) < t) (hc1 : 0 ≤ c.firstLog) (hc2 : 0 ≤ c.secondLog)
    (hco : 0 ≤ c.offset) (hinactive : ¬2 ≤ q → c.secondLog = 0) :
    evaluationBudget c a t gap ≤
      (c.all * gap + c.firstLog * ((t - 1) / t) +
        (if 2 ≤ q then c.secondLog * ((t - 2) / t) else 0) + c.offset) /
      tolerancePower a t := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast a.order_pos
  have ht : 1 < t := by linarith
  obtain ⟨hP, hP1⟩ := tolerancePower_bounds (a := a) hexp
  have he := a.epsilon_pos 0 (by have := a.order_pos; simp only [Fin.val_zero]; omega)
  have he1 := a.epsilon_le_one 0 (by have := a.order_pos; simp only [Fin.val_zero]; omega)
  have hPfirst : tolerancePower a t ≤ a.epsilon 0 ^ (t / (t - 1)) := by
    rw [tolerancePower, toleranceRadius_power (by linarith : 0 ≤ t)]
    split_ifs
    · exact min_le_left _ _
    · exact le_rfl
  have hfirst : tolerancePower a t * |Real.log (a.epsilon 0)| ≤ (t - 1) / t := by
    have hh := rpow_mul_abs_log_le he he1 (div_pos (by linarith : 0 < t) (by linarith : 0 < t - 1))
    have heq : 1 / (t / (t - 1)) = (t - 1) / t := by field_simp
    rw [heq] at hh
    exact (mul_le_mul_of_nonneg_right hPfirst (abs_nonneg _)).trans hh
  have hsecond : tolerancePower a t * (c.secondLog * |Real.log (a.epsilon 1)|) ≤
      if 2 ≤ q then c.secondLog * ((t - 2) / t) else 0 := by
    by_cases hq : 2 ≤ q
    · rw [ite_eq_left hq]
      have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
      have ht2 : 2 < t := by linarith
      have he' := a.epsilon_pos 1 (by simp only [Fin.val_one]; omega)
      have he1' := a.epsilon_le_one 1 (by simp only [Fin.val_one]; omega)
      have hPsecond : tolerancePower a t ≤ a.epsilon 1 ^ (t / (t - 2)) := by
        rw [tolerancePower, toleranceRadius_power (by linarith : 0 ≤ t), ite_eq_left hq]
        exact min_le_right _ _
      have hh := rpow_mul_abs_log_le he' he1'
        (div_pos (by linarith : 0 < t) (by linarith : 0 < t - 2))
      have heq : 1 / (t / (t - 2)) = (t - 2) / t := by field_simp
      rw [heq] at hh
      have hb := (mul_le_mul_of_nonneg_right hPsecond (abs_nonneg _)).trans hh
      nlinarith [mul_le_mul_of_nonneg_left hb hc2]
    · rw [ite_eq_right hq, hinactive hq]
      ring_nf
      exact le_refl _
  have hfirst' := mul_le_mul_of_nonneg_left hfirst hc1
  have hoff := mul_le_mul_of_nonneg_left hP1 hco
  rw [le_div_iff₀ hP]
  dsimp [evaluationBudget]
  have hcancel : c.all * gap / tolerancePower a t * tolerancePower a t = c.all * gap :=
    div_mul_cancel₀ _ hP.ne'
  nlinarith only [hcancel, hfirst', hsecond, hoff]

end Optimization.UniversalRegularization
