import Numlib.Optimization.HighOrder.ModelSolve.Halving

/-!
# Actual criticality-radius reductions before model-step acceptance

Each radius reduction is justified by an actual failed Taylor test and an
actual function-decrease test at its current candidate point. The candidate
point may change between reductions. Taylor remainder bounds imply a uniform
radius floor without global-minimum or criticality conclusions in the trace.
-/

namespace ModelSolve
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The primitive tests permitting successive criticality-radius halvings.
The point schedule may include different approximate model minimizers. -/
structure RadiusReductions (f : E → ℝ) (j : ℕ) (α δ₀ : ℝ)
    (x d : ℕ → E) (N : ℕ) : Prop where
  feasible : ∀ t < N, ‖d t‖ ≤ BacktrackingGradient.step δ₀ t
  failed_test : ∀ t < N, α * BacktrackingGradient.step δ₀ t ^ j / j.factorial <
    TaylorModel.decrement f j (x t) (d t)
  insufficient_decrease : ∀ t < N, f (x t) - f (x t + d t) <
    α / 2 * BacktrackingGradient.step δ₀ t ^ j / j.factorial

/-- The actual two tests forbid halving below the Taylor remainder threshold,
so every finite reduction prefix retains a quantitative final radius. -/
theorem RadiusReductions.radius_lower {f : E → ℝ} {j p N : ℕ}
    (hj : 0 < j) (hjp : j ≤ p) (hf : ContDiff ℝ p f)
    {L B α δ₀ : ℝ} (hL : 0 ≤ L) (hB : 0 < B) (hLB : L ≤ B)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    {x d : ℕ → E}
    (hA : ∀ t < N, ∀ a, j < a → a ≤ p → ‖iteratedFDeriv ℝ a f (x t)‖ ≤ B)
    (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ ≤ 1)
    (h : RadiusReductions f j α δ₀ x d N) :
    min (α / (8 * B)) δ₀ ≤ BacktrackingGradient.step δ₀ N := by
  cases N with
  | zero => simp
  | succ k =>
    have hk : k < k + 1 := by omega
    have hprev : α / (4 * B) < BacktrackingGradient.step δ₀ k := by
      apply lt_of_not_ge
      intro ht
      have hdecr := TaylorModel.value_decrement_ge_half_of_taylor_test hj hjp hf hL hB hLB
        hlip (x k) (d k) (BacktrackingGradient.step_pos hδ₀ k)
        ((BacktrackingGradient.step_antitone hδ₀.le (Nat.zero_le k)).trans
          (by simpa using hδ₀1)) (h.feasible k hk) ht (hA k hk) (h.failed_test k hk).le
      exact (not_lt_of_ge hdecr) (h.insufficient_decrease k hk)
    rw [BacktrackingGradient.step_succ]
    apply (min_le_left _ _).trans
    have he : α / (8 * B) = (α / (4 * B)) / 2 := by ring
    rw [he]
    exact div_le_div_of_nonneg_right hprev.le (by norm_num)

/-- A genuine first-passing loop at a global minimum supplies all actual
radius-reduction tests: every rejected Taylor test has strictly insufficient
actual decrease because a global minimum cannot decrease. -/
theorem CriticalHalvingRun.toRadiusReductions {f : E → ℝ} {j N : ℕ} {x : E}
    {α δ₀ : ℝ} (hα : 0 < α) (hδ₀ : 0 < δ₀) {d : ℕ → E}
    (hd : ∀ t, ‖d t‖ ≤ BacktrackingGradient.step δ₀ t)
    (hmin : ∀ z, f x ≤ f z) (h : CriticalHalvingRun f j x α δ₀ d N) :
    RadiusReductions f j α δ₀ (fun _ => x) d N := by
  refine ⟨fun t _ => hd t, ?_, ?_⟩
  · intro t ht
    exact lt_of_not_ge (h.rejected t ht)
  · intro t _
    have hpos : 0 < α / 2 * BacktrackingGradient.step δ₀ t ^ j / j.factorial :=
      div_pos (mul_pos (half_pos hα) (pow_pos (BacktrackingGradient.step_pos hδ₀ t) _))
        (by positivity)
    exact lt_of_le_of_lt (sub_nonpos.mpr (hmin _)) hpos

end ModelSolve
