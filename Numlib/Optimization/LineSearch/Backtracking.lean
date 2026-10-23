import Numlib.Optimization.LineSearch.LipschitzGradient
import Numlib.Optimization.EvaluationComplexity.Decrease

/-!
# Backtracking Armijo search along the negative gradient

Halving the initial candidate eventually gives sufficient decrease. Minimality
of the accepted halving index gives a lower bound that also covers initial
candidates already shorter than the sufficient-decrease threshold.
-/

namespace BacktrackingGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The candidate after `j` halvings of the initial step. -/
noncomputable def step (tini : ℝ) (j : ℕ) : ℝ := tini / (2 : ℝ) ^ j

@[simp] theorem step_zero (tini : ℝ) : step tini 0 = tini := by simp [step]

/-- Halving the candidate is the successor update. -/
theorem step_succ (tini : ℝ) (j : ℕ) : step tini (j + 1) = step tini j / 2 := by
  simp [step, pow_succ, div_div]

/-- Every positive threshold is reached after finitely many halvings. -/
theorem exists_step_le (tini : ℝ) {threshold : ℝ} (hthreshold : 0 < threshold) :
    ∃ j, step tini j ≤ threshold := by
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (tini / threshold) (by norm_num : (1 : ℝ) < 2)
  refine ⟨j, (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ j)).mpr ?_⟩
  have hh := (div_lt_iff₀ hthreshold).mp hj
  nlinarith

/-- The sufficient Armijo threshold for a Lipschitz gradient. -/
noncomputable def threshold (L α : ℝ) : ℝ := 2 * (1 - α) / L

/-- An actual Armijo acceptance test at the `j`th candidate. -/
def Accepts (f : E → ℝ) (g : E → E) (α tini : ℝ) (x : E) (j : ℕ) : Prop :=
  LineSearch.Armijo f (fun y => innerSL ℝ (g y)) α x (-g x) (step tini j)

/-- Every candidate at or below the explicit threshold is acceptable. -/
theorem accepts_of_step_le {f : E → ℝ} {g : E → E} {L α tini : ℝ}
    (hf : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLpos : 0 < L)
    (htini : 0 ≤ tini) (x : E) {j : ℕ} (hj : step tini j ≤ threshold L α) :
    Accepts f g α tini x j := by
  apply LineSearch.armijo_neg_gradient_of_lipschitz hf hL (by
    exact div_nonneg htini (pow_nonneg (by norm_num) _))
  have hh := (le_div_iff₀ hLpos).mp hj
  nlinarith

/-- Backtracking accepts some finite candidate at every point. -/
theorem exists_accepts {f : E → ℝ} {g : E → E} {L α tini : ℝ}
    (hf : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLpos : 0 < L)
    (hα : α < 1) (htini : 0 ≤ tini) (x : E) :
    ∃ j, Accepts f g α tini x j := by
  obtain ⟨j, hj⟩ := exists_step_le tini (show 0 < threshold L α from by
    dsimp [threshold]; positivity)
  exact ⟨j, accepts_of_step_le hf hL hLpos htini x hj⟩

/-- Minimality of the accepted index bounds its step from below. The minimum
with the initial step is necessary when that initial candidate is already small. -/
theorem lower_bound_of_rejected_prefix {f : E → ℝ} {g : E → E} {L α tini : ℝ}
    (hf : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLpos : 0 < L)
    (htini : 0 ≤ tini) (x : E) {j : ℕ}
    (hreject : ∀ m < j, ¬Accepts f g α tini x m) :
    min tini ((1 - α) / L) ≤ step tini j := by
  cases j with
  | zero => simp
  | succ j =>
    have hprev : threshold L α < step tini j := by
      by_contra hh
      exact hreject j (by omega) (accepts_of_step_le hf hL hLpos htini x (le_of_not_gt hh))
    rw [step_succ]
    have he : threshold L α / 2 = (1 - α) / L := by dsimp [threshold]; ring
    exact (min_le_right _ _).trans (by linarith)

/-- A finite prefix of backtracking steepest descent before termination. Every
earlier candidate is rejected and the selected candidate passes the actual
Armijo test, expressing the minimal accepted halving index. -/
structure Run (f : E → ℝ) (g : E → E) (x : ℕ → E) (j : ℕ → ℕ)
    (α tini ε : ℝ) (N : ℕ) : Prop where
  derivative : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y
  alpha_pos : 0 < α
  alpha_lt_one : α < 1
  initial_pos : 0 < tini
  accuracy_pos : 0 < ε
  not_terminated : ∀ i < N, ε < ‖g (x i)‖
  accepts : ∀ i < N, Accepts f g α tini (x i) (j i)
  rejects : ∀ i < N, ∀ m < j i, ¬Accepts f g α tini (x i) m
  update : ∀ i < N, x (i + 1) = x i - step tini (j i) • g (x i)

namespace Run

variable {f : E → ℝ} {g : E → E} {x : ℕ → E} {j : ℕ → ℕ}
  {α tini ε L : ℝ} {N : ℕ}

/-- A uniform sufficient threshold index bounds every accepted halving index. -/
theorem index_le (h : Run f g x j α tini ε N)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLpos : 0 < L)
    {M : ℕ} (hM : step tini M ≤ threshold L α) {i : ℕ} (hi : i < N) : j i ≤ M := by
  by_contra hh
  exact h.rejects i hi M (lt_of_not_ge hh)
    (accepts_of_step_le h.derivative hL hLpos h.initial_pos.le (x i) hM)

/-- The successful step has a uniform positive lower bound independent of the
iteration and the requested accuracy. -/
theorem step_lower_bound (h : Run f g x j α tini ε N)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLpos : 0 < L)
    {i : ℕ} (hi : i < N) : min tini ((1 - α) / L) ≤ step tini (j i) :=
  lower_bound_of_rejected_prefix h.derivative hL hLpos h.initial_pos.le (x i) (h.rejects i hi)

/-- Armijo decrease and the uniform step bound give a fixed decrease whenever
the gradient stopping test fails. -/
theorem decrease (h : Run f g x j α tini ε N)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLpos : 0 < L)
    {i : ℕ} (hi : i < N) :
    α * min tini ((1 - α) / L) * ε ^ 2 ≤ f (x i) - f (x (i + 1)) := by
  have ha : f (x (i + 1)) ≤ f (x i) - α * step tini (j i) * ‖g (x i)‖ ^ 2 := by
    simpa [h.update i hi, Accepts, LineSearch.Armijo, smul_neg, sub_eq_add_neg,
      innerSL_apply_apply, real_inner_self_eq_norm_sq] using h.accepts i hi
  have hmin : 0 < min tini ((1 - α) / L) := lt_min h.initial_pos (by
    exact div_pos (by linarith [h.alpha_lt_one]) hLpos)
  have heps := h.accuracy_pos
  have hnorm := h.not_terminated i hi
  have hsq : ε ^ 2 ≤ ‖g (x i)‖ ^ 2 := by nlinarith [norm_nonneg (g (x i))]
  have hproduct : α * min tini ((1 - α) / L) * ε ^ 2 ≤
      α * step tini (j i) * ‖g (x i)‖ ^ 2 := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (h.step_lower_bound hL hLpos hi) h.alpha_pos.le
    · exact hsq
    · positivity
    · exact mul_nonneg h.alpha_pos.le (hmin.le.trans (h.step_lower_bound hL hLpos hi))
  linarith

/-- An initial objective budget bounds every nonterminated prefix. -/
theorem iterations_le (h : Run f g x j α tini ε N)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLpos : 0 < L)
    {flow : ℝ} (hlow : flow ≤ f (x N)) :
    (N : ℝ) ≤ (f (x 0) - flow) / (α * min tini ((1 - α) / L) * ε ^ 2) := by
  have hα := h.alpha_pos
  have hε := h.accuracy_pos
  have hmin : 0 < min tini ((1 - α) / L) := lt_min h.initial_pos (by
    exact div_pos (by linarith [h.alpha_lt_one]) hLpos)
  have hc := EvaluationComplexity.card_successful_le_gap_div
    (S := Set.univ) (f := fun i => f (x i)) (by positivity) hlow
    (fun i hi _ => h.decrease hL hLpos hi) (fun _ _ hu => False.elim (hu (Set.mem_univ _)))
  have hcard : EvaluationComplexity.successfulIterations Set.univ N = Finset.range N := by
    ext i
    simp
  simpa only [hcard, Finset.card_range] using hc

/-- Each backtracking trial evaluates the objective once; add the initial
objective evaluation to the sum of candidate counts. -/
noncomputable def functionEvaluations (j : ℕ → ℕ) (N : ℕ) : ℕ :=
  1 + ∑ i ∈ Finset.range N, (j i + 1)

/-- A uniform sufficient threshold index bounds the total objective calls. -/
theorem functionEvaluations_le (h : Run f g x j α tini ε N)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLpos : 0 < L)
    {M : ℕ} (hM : step tini M ≤ threshold L α) :
    functionEvaluations j N ≤ 1 + (M + 1) * N := by
  apply Nat.add_le_add_left
  calc
    ∑ i ∈ Finset.range N, (j i + 1) ≤ ∑ _i ∈ Finset.range N, (M + 1) :=
      Finset.sum_le_sum (fun i hi => Nat.add_le_add_right
        (h.index_le hL hLpos hM (Finset.mem_range.mp hi)) 1)
    _ = (M + 1) * N := by simp [Nat.mul_comm]

end Run

/-- A consistent backtracking execution reaches the gradient tolerance within
the finite objective budget. Every inner linesearch terminates by `exists_accepts`. -/
theorem exists_termination {f : E → ℝ} {g : E → E} {x : ℕ → E} {j : ℕ → ℕ}
    {α tini ε L flow : ℝ}
    (hprefix : ∀ N, (∀ i < N, ε < ‖g (x i)‖) → Run f g x j α tini ε N)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLpos : 0 < L)
    (hlow : ∀ y, flow ≤ f y) :
    ∃ K, ‖g (x K)‖ ≤ ε ∧ Run f g x j α tini ε K ∧
      (K : ℝ) ≤ (f (x 0) - flow) / (α * min tini ((1 - α) / L) * ε ^ 2) := by
  have hex : ∃ K, ‖g (x K)‖ ≤ ε := by
    by_contra hnone
    push Not at hnone
    obtain ⟨N, hN⟩ := exists_nat_gt
      ((f (x 0) - flow) / (α * min tini ((1 - α) / L) * ε ^ 2))
    have hb := (hprefix N (fun i _ => hnone i)).iterations_le hL hLpos (hlow _)
    exact (not_le_of_gt hN) hb
  have hr := hprefix (Nat.find hex) (fun i hi => lt_of_not_ge (Nat.find_min hex hi))
  exact ⟨Nat.find hex, Nat.find_spec hex, hr, hr.iterations_le hL hLpos (hlow _)⟩

end BacktrackingGradient
