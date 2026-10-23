import Numlib.Optimization.HighOrder.CriticalityLocalMin
import Numlib.Optimization.LineSearch.Backtracking.Radii
import Numlib.Optimization.HighOrder.TaylorDecrease
import Mathlib.Tactic
/-!
# Finite actual criticality halving at a global model minimizer

Every accepted test and every earlier rejected test is an actual Taylor
condition at a geometric candidate radius. Actual derivative bounds and the
Taylor remainder imply finite termination and an explicit radius floor. The
first two criticality orders accept their initial radius. Maximizing directions
exist by compactness, so the direction schedule itself is also constructed.
-/

namespace ModelSolve
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual normalized Taylor decrement test at a geometric candidate radius. -/
def CriticalityPasses (f : E → ℝ) (j : ℕ) (x : E) (α δ₀ : ℝ)
    (d : ℕ → E) (t : ℕ) : Prop :=
  TaylorModel.decrement f j x (d t) ≤
    α * BacktrackingGradient.step δ₀ t ^ j / j.factorial

/-- A completed finite halving loop records its actual accepted test and all
earlier failed tests. Radius and criticality bounds are derived separately. -/
structure CriticalHalvingRun (f : E → ℝ) (j : ℕ) (x : E) (α δ₀ : ℝ)
    (d : ℕ → E) (N : ℕ) : Prop where
  passes : CriticalityPasses f j x α δ₀ d N
  rejected : ∀ t < N, ¬ CriticalityPasses f j x α δ₀ d t

/-- At an actual global minimum, the sufficient Taylor remainder threshold
forces the computed Taylor test to pass for every feasible direction. -/
theorem criticalityPasses_of_radius_le {f : E → ℝ} {j p : ℕ}
    (hj : 0 < j) (hjp : j ≤ p) (hf : ContDiff ℝ p f)
    {L B α δ₀ : ℝ} (hL : 0 ≤ L) (hB : 0 < B) (hLB : L ≤ B) (hα : 0 < α)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    (x : E) (hmin : ∀ t : E, f x ≤ f t)
    (hA : ∀ a, j < a → a ≤ p → ‖iteratedFDeriv ℝ a f x‖ ≤ B)
    (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ ≤ 1) (d : ℕ → E)
    (hd : ∀ t, ‖d t‖ ≤ BacktrackingGradient.step δ₀ t) {t : ℕ}
    (ht : BacktrackingGradient.step δ₀ t ≤ α / (4 * B)) :
    CriticalityPasses f j x α δ₀ d t := by
  by_contra hfail
  have hfailed : α * BacktrackingGradient.step δ₀ t ^ j / j.factorial ≤
      TaylorModel.decrement f j x (d t) := le_of_not_ge hfail
  have hδ := BacktrackingGradient.step_pos hδ₀ t
  have hδ1 := (BacktrackingGradient.step_antitone hδ₀.le
    (Nat.zero_le t)).trans (by simpa using hδ₀1)
  have hdecr := TaylorModel.value_decrement_ge_half_of_taylor_test hj hjp hf hL hB hLB
    hlip x (d t) hδ hδ1 (hd t) ht hA hfailed
  have hpos : 0 < α / 2 * BacktrackingGradient.step δ₀ t ^ j / j.factorial :=
    div_pos (mul_pos (half_pos hα) (pow_pos hδ j)) (by positivity)
  linarith [hmin (x + d t)]

/-- Every feasible direction schedule gives a genuine finite first-passing
halving loop, with an explicit final radius floor and all prefix bounds. -/
theorem exists_criticalHalvingRun {f : E → ℝ} {j p : ℕ}
    (hj : 0 < j) (hjp : j ≤ p) (hf : ContDiff ℝ p f)
    {L B α δ₀ : ℝ} (hL : 0 ≤ L) (hB : 0 < B) (hLB : L ≤ B) (hα : 0 < α)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    (x : E) (hmin : ∀ t : E, f x ≤ f t)
    (hA : ∀ a, j < a → a ≤ p → ‖iteratedFDeriv ℝ a f x‖ ≤ B)
    (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ ≤ 1) (d : ℕ → E)
    (hd : ∀ t, ‖d t‖ ≤ BacktrackingGradient.step δ₀ t) :
    ∃ N, CriticalHalvingRun f j x α δ₀ d N ∧
      min (α / (8 * B)) δ₀ ≤ BacktrackingGradient.step δ₀ N ∧
      ∀ t ≤ N, BacktrackingGradient.step δ₀ N ≤ BacktrackingGradient.step δ₀ t ∧
        BacktrackingGradient.step δ₀ t ≤ δ₀ := by
  classical
  have hex : ∃ t, CriticalityPasses f j x α δ₀ d t := by
    obtain ⟨t, ht⟩ := BacktrackingGradient.exists_step_le δ₀
      (show 0 < α / (4 * B) by positivity)
    exact ⟨t, criticalityPasses_of_radius_le hj hjp hf hL hB hLB hα hlip x hmin hA
      hδ₀ hδ₀1 d hd ht⟩
  let N := Nat.find hex
  have hrun : CriticalHalvingRun f j x α δ₀ d N :=
    ⟨Nat.find_spec hex, fun t ht => Nat.find_min hex ht⟩
  refine ⟨N, hrun, ?_, ?_⟩
  · cases hN : N with
    | zero => simp
    | succ k =>
      have hprev : α / (4 * B) < BacktrackingGradient.step δ₀ k := by
        apply lt_of_not_ge
        intro hh
        exact hrun.rejected k (by omega)
          (criticalityPasses_of_radius_le hj hjp hf hL hB hLB hα hlip x hmin hA
            hδ₀ hδ₀1 d hd hh)
      rw [BacktrackingGradient.step_succ]
      apply (min_le_left _ _).trans
      have he : α / (8 * B) = (α / (4 * B)) / 2 := by ring
      rw [he]
      exact div_le_div_of_nonneg_right hprev.le (by norm_num)
  · intro t ht
    exact ⟨BacktrackingGradient.step_antitone hδ₀.le ht,
      (BacktrackingGradient.step_antitone hδ₀.le (Nat.zero_le t)).trans (by simp)⟩


variable [ProperSpace E]

/-- The first two derivative orders at a global minimum accept the initial
radius; consequently their actual halving count is zero. -/
theorem CriticalHalvingRun.eq_zero_of_order_le_two {f : E → ℝ} {j p N : ℕ}
    (hj : 0 < j) (hj2 : j ≤ 2) (hjp : j ≤ p) (hf : ContDiff ℝ p f)
    {x : E} (hmin : ∀ t : E, f x ≤ f t) {α δ₀ : ℝ}
    (hα : 0 ≤ α) (hδ₀ : 0 ≤ δ₀) {d : ℕ → E}
    (hd : ‖d 0‖ ≤ δ₀) (h : CriticalHalvingRun f j x α δ₀ d N) : N = 0 := by
  have hlocal : IsLocalMin f x := Filter.Eventually.of_forall hmin
  have hz : TaylorModel.criticality f j x δ₀ = 0 := by
    rcases (show j = 1 ∨ j = 2 by omega) with h1 | h2
    · rw [h1]
      exact TaylorModel.criticality_one_eq_zero_of_isLocalMin hlocal hδ₀
    · rw [h2]
      have hf2 : ContDiff ℝ 2 f := hf.of_le (by exact_mod_cast (by omega : 2 ≤ p))
      exact TaylorModel.criticality_two_eq_zero_of_isLocalMin hf2 hlocal hδ₀
  have hd0 := TaylorModel.decrement_le_criticality f j x hd
  rw [hz] at hd0
  have hpass : CriticalityPasses f j x α δ₀ d 0 := by
    unfold CriticalityPasses
    simp only [BacktrackingGradient.step, pow_zero, div_one]
    exact hd0.trans (div_nonneg (mul_nonneg hα (pow_nonneg hδ₀ j)) (Nat.cast_nonneg _))
  by_contra hN
  exact h.rejected 0 (Nat.pos_of_ne_zero hN) hpass

/-- Compactness constructs actual attaining Taylor-decrement directions and
a finite first-passing loop. Every requested approximation, radius floor and
low-order zero-halving conclusion is proved from the actual model. -/
theorem exists_attaining_criticalHalvingRun {f : E → ℝ} {j p : ℕ}
    (hj : 0 < j) (hjp : j ≤ p) (hf : ContDiff ℝ p f)
    {L B α δ₀ ζ : ℝ} (hL : 0 ≤ L) (hB : 0 < B) (hLB : L ≤ B)
    (hα : 0 < α) (hζ : ζ ≤ 1)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    (x : E) (hmin : ∀ t : E, f x ≤ f t)
    (hA : ∀ a, j < a → a ≤ p → ‖iteratedFDeriv ℝ a f x‖ ≤ B)
    (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ ≤ 1) :
    ∃ (d : ℕ → E) (N : ℕ),
      (∀ t, ‖d t‖ ≤ BacktrackingGradient.step δ₀ t ∧
        ζ * TaylorModel.criticality f j x (BacktrackingGradient.step δ₀ t) ≤
          TaylorModel.decrement f j x (d t)) ∧
      CriticalHalvingRun f j x α δ₀ d N ∧
      min (α / (8 * B)) δ₀ ≤ BacktrackingGradient.step δ₀ N ∧
      (∀ t ≤ N, BacktrackingGradient.step δ₀ N ≤ BacktrackingGradient.step δ₀ t ∧
        BacktrackingGradient.step δ₀ t ≤ δ₀) ∧
      (j ≤ 2 → N = 0) := by
  have hex : ∀ t : ℕ, ∃ d : E, ‖d‖ ≤ BacktrackingGradient.step δ₀ t ∧
      TaylorModel.decrement f j x d =
        TaylorModel.criticality f j x (BacktrackingGradient.step δ₀ t) :=
    fun t => TaylorModel.exists_decrement_eq_criticality f j x
      (BacktrackingGradient.step_pos hδ₀ t).le
  choose d hd heq using hex
  obtain ⟨N, hrun, hfloor, hprefix⟩ := exists_criticalHalvingRun hj hjp hf hL hB hLB hα
    hlip x hmin hA hδ₀ hδ₀1 d hd
  refine ⟨d, N, fun t => ⟨hd t, ?_⟩, hrun, hfloor, hprefix, ?_⟩
  · rw [heq t]
    exact mul_le_of_le_one_left
      (TaylorModel.criticality_nonneg f j x (BacktrackingGradient.step_pos hδ₀ t).le) hζ
  · intro hj2
    exact hrun.eq_zero_of_order_le_two hj hj2 hjp hf hmin hα.le hδ₀.le (by simpa using hd 0)

end ModelSolve
