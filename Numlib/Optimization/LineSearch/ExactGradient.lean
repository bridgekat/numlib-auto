import Numlib.Optimization.LineSearch.LipschitzGradient
import Numlib.Optimization.EvaluationComplexity.Decrease

/-!
# Exact linesearch along the negative gradient

Global minimization on the nonnegative ray guarantees at least the decrease of
the explicit candidate step `1/L`. A finite objective budget then bounds the
number of nonterminating iterations. The bound concerns iterations; the work
inside an exact line minimization is not bounded here.
-/

namespace ExactGradientLineSearch

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A nonterminated finite prefix of exact steepest descent. Each selected
step is an actual global minimizer of the objective along its nonnegative ray. -/
structure Run (f : E → ℝ) (g : E → E) (x : ℕ → E) (t : ℕ → ℝ)
    (ε : ℝ) (N : ℕ) : Prop where
  derivative : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y
  accuracy_pos : 0 < ε
  not_terminated : ∀ i < N, ε < ‖g (x i)‖
  step_nonneg : ∀ i < N, 0 ≤ t i
  minimum : ∀ i < N, IsMinOn (fun u : ℝ => f (x i - u • g (x i))) (Set.Ici 0) (t i)
  step : ∀ i < N, x (i + 1) = x i - t i • g (x i)

namespace Run

variable {f : E → ℝ} {g : E → E} {x : ℕ → E} {t : ℕ → ℝ} {ε L : ℝ} {N : ℕ}

/-- The exact minimizer is at least as good as the step `1/L`, so it gives a
decrease of at least the squared gradient divided by `2L`. -/
theorem decrease (h : Run f g x t ε N)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLpos : 0 < L)
    {i : ℕ} (hi : i < N) :
    ‖g (x i)‖ ^ 2 / (2 * L) ≤ f (x i) - f (x (i + 1)) := by
  have ha := LineSearch.armijo_neg_gradient_of_lipschitz (α := 1 / 2)
    h.derivative hL (inv_nonneg.mpr hLpos.le)
    (by rw [mul_inv_cancel₀ hLpos.ne']; norm_num) (x i)
  have ha' : f (x i - L⁻¹ • g (x i)) ≤ f (x i) -
      (1 / 2 : ℝ) * L⁻¹ * ‖g (x i)‖ ^ 2 := by
    simpa [LineSearch.Armijo, smul_neg, sub_eq_add_neg, innerSL_apply_apply,
      real_inner_self_eq_norm_sq] using ha
  have hm := h.minimum i hi (show L⁻¹ ∈ Set.Ici (0 : ℝ) from inv_nonneg.mpr hLpos.le)
  change f (x i - t i • g (x i)) ≤ f (x i - L⁻¹ • g (x i)) at hm
  rw [h.step i hi]
  have he : (1 / 2 : ℝ) * L⁻¹ * ‖g (x i)‖ ^ 2 = ‖g (x i)‖ ^ 2 / (2 * L) := by
    field_simp
  linarith

/-- The finite objective budget bounds the number of nonterminating iterations
by `2L` times the initial objective gap divided by `ε²`. -/
theorem iterations_le (h : Run f g x t ε N)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLpos : 0 < L)
    {flow : ℝ} (hlow : flow ≤ f (x N)) :
    (N : ℝ) ≤ 2 * L * (f (x 0) - flow) / ε ^ 2 := by
  have hε := h.accuracy_pos
  have hd : 0 < ε ^ 2 / (2 * L) := by positivity
  have hc := EvaluationComplexity.card_successful_le_gap_div
    (S := Set.univ) (f := fun i => f (x i)) hd hlow
    (fun i hi _ => ?_) (fun _ _ hu => False.elim (hu (Set.mem_univ _)))
  · have hcard : EvaluationComplexity.successfulIterations Set.univ N = Finset.range N := by
      ext i
      simp
    rw [hcard, Finset.card_range] at hc
    convert hc using 1
    field_simp
  · have hnorm := h.not_terminated i hi
    have hsquare : ε ^ 2 ≤ ‖g (x i)‖ ^ 2 := by nlinarith [norm_nonneg (g (x i))]
    exact (div_le_div_of_nonneg_right hsquare (by positivity)).trans (h.decrease hL hLpos hi)

end Run

/-- A consistent exact-linesearch execution obeying the algorithm at every
prefix before stopping reaches the requested gradient tolerance. -/
theorem exists_termination {f : E → ℝ} {g : E → E} {x : ℕ → E} {t : ℕ → ℝ}
    {ε L flow : ℝ}
    (hprefix : ∀ N, (∀ i < N, ε < ‖g (x i)‖) → Run f g x t ε N)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLpos : 0 < L)
    (hlow : ∀ y, flow ≤ f y) :
    ∃ K, ‖g (x K)‖ ≤ ε ∧ Run f g x t ε K ∧
      (K : ℝ) ≤ 2 * L * (f (x 0) - flow) / ε ^ 2 := by
  have hex : ∃ K, ‖g (x K)‖ ≤ ε := by
    by_contra hnone
    push Not at hnone
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * L * (f (x 0) - flow) / ε ^ 2)
    have hb := (hprefix N (fun i _ => hnone i)).iterations_le hL hLpos (hlow _)
    exact (not_le_of_gt hN) hb
  have hr := hprefix (Nat.find hex) (fun i hi => lt_of_not_ge (Nat.find_min hex hi))
  exact ⟨Nat.find hex, Nat.find_spec hex, hr, hr.iterations_le hL hLpos (hlow _)⟩

end ExactGradientLineSearch
