import Numlib.Optimization.HighOrder.ModelSolve.Reductions
import Numlib.Optimization.Constrained.LocalCriticality

/-!
# Actual feasible Taylor-criticality halving

Every trial direction and intermediate candidate is feasible in the actual
constraint set. True Taylor remainders give a quantitative first-passing radius
floor at constrained global model minima. Convexity gives unit first-order
radii; higher orders use adaptive radii rather than an invalid unit-radius rule.
-/

namespace ModelSolve
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual Taylor halving guards together with feasibility of every
intermediate model point and trial direction. No radius floor is an input. -/
structure FeasibleRadiusReductions (f : E → ℝ) (C : Set E) (j : ℕ) (α δ₀ : ℝ)
    (x d : ℕ → E) (N : ℕ) : Prop extends RadiusReductions f j α δ₀ x d N where
  point_feasible : ∀ t < N, x t ∈ C
  trial_feasible : ∀ t < N, x t + d t ∈ C

/-- A genuine constrained minimum makes every feasible failed Taylor test an
insufficient function-decrease test, giving actual feasible radius reductions. -/
theorem CriticalHalvingRun.toFeasibleRadiusReductions {f : E → ℝ} {C : Set E}
    {j N : ℕ} {x : E} {α δ₀ : ℝ} (hα : 0 < α) (hδ₀ : 0 < δ₀)
    {d : ℕ → E} (hd : ∀ t, ‖d t‖ ≤ BacktrackingGradient.step δ₀ t)
    (hfeas : ∀ t, x + d t ∈ C) (hx : x ∈ C) (hmin : IsMinOn f C x)
    (h : CriticalHalvingRun f j x α δ₀ d N) :
    FeasibleRadiusReductions f C j α δ₀ (fun _ => x) d N := by
  refine ⟨⟨fun t _ => hd t, fun t ht => lt_of_not_ge (h.rejected t ht), ?_⟩,
    fun _ _ => hx, fun t _ => hfeas t⟩
  intro t _
  have hp : 0 < α / 2 * BacktrackingGradient.step δ₀ t ^ j / j.factorial :=
    div_pos (mul_pos (half_pos hα) (pow_pos (BacktrackingGradient.step_pos hδ₀ t) _))
      (by positivity)
  exact lt_of_le_of_lt (sub_nonpos.mpr (hmin (hfeas t))) hp

/-- At an actual constrained global minimum, a sufficiently small geometric
radius forces the true Taylor test for every feasible trial direction. -/
theorem criticalityPasses_of_radius_le_on {f : E → ℝ} {j p : ℕ}
    (hj : 0 < j) (hjp : j ≤ p) (hf : ContDiff ℝ p f)
    {L B α δ₀ : ℝ} (hL : 0 ≤ L) (hB : 0 < B) (hLB : L ≤ B) (hα : 0 < α)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    {C : Set E} (x : E) (hmin : IsMinOn f C x)
    (hA : ∀ a, j < a → a ≤ p → ‖iteratedFDeriv ℝ a f x‖ ≤ B)
    (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ ≤ 1) (d : ℕ → E)
    (hd : ∀ t, ‖d t‖ ≤ BacktrackingGradient.step δ₀ t)
    (hfeas : ∀ t, x + d t ∈ C) {t : ℕ}
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
  have hv : f x ≤ f (x + d t) := hmin (hfeas t)
  linarith

/-- Every actual feasible direction schedule has a finite first-passing Taylor
loop at a constrained global minimum, with exact radius and prefix bounds. -/
theorem exists_constrained_criticalHalvingRun {f : E → ℝ} {j p : ℕ}
    (hj : 0 < j) (hjp : j ≤ p) (hf : ContDiff ℝ p f)
    {L B α δ₀ : ℝ} (hL : 0 ≤ L) (hB : 0 < B) (hLB : L ≤ B) (hα : 0 < α)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    {C : Set E} (x : E) (hx : x ∈ C) (hmin : IsMinOn f C x)
    (hA : ∀ a, j < a → a ≤ p → ‖iteratedFDeriv ℝ a f x‖ ≤ B)
    (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ ≤ 1) (d : ℕ → E)
    (hd : ∀ t, ‖d t‖ ≤ BacktrackingGradient.step δ₀ t)
    (hfeas : ∀ t, x + d t ∈ C) :
    ∃ N, CriticalHalvingRun f j x α δ₀ d N ∧
      min (α / (8 * B)) δ₀ ≤ BacktrackingGradient.step δ₀ N ∧
      ∀ t ≤ N, BacktrackingGradient.step δ₀ N ≤ BacktrackingGradient.step δ₀ t ∧
        BacktrackingGradient.step δ₀ t ≤ δ₀ := by
  classical
  have hex : ∃ t, CriticalityPasses f j x α δ₀ d t := by
    obtain ⟨t, ht⟩ := BacktrackingGradient.exists_step_le δ₀
      (show 0 < α / (4 * B) by positivity)
    exact ⟨t, criticalityPasses_of_radius_le_on hj hjp hf hL hB hLB hα hlip x hmin hA
      hδ₀ hδ₀1 d hd hfeas ht⟩
  let N := Nat.find hex
  have hr : CriticalHalvingRun f j x α δ₀ d N :=
    ⟨Nat.find_spec hex, fun t ht => Nat.find_min hex ht⟩
  have hred := hr.toFeasibleRadiusReductions hα hδ₀ hd hfeas hx hmin
  refine ⟨N, hr, hred.toRadiusReductions.radius_lower hj hjp hf hL hB hLB hlip
    (fun _ _ => hA) hδ₀ hδ₀1, ?_⟩
  intro t ht
  exact ⟨BacktrackingGradient.step_antitone hδ₀.le ht,
    (BacktrackingGradient.step_antitone hδ₀.le (Nat.zero_le t)).trans (by simp)⟩

end ModelSolve

namespace ModelSolve
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Compactness gives actual feasible maximizing directions for a finite
first-passing Taylor loop. On a convex set, order one accepts its initial radius. -/
theorem exists_attaining_constrained_criticalHalvingRun {f : E → ℝ} {j p : ℕ}
    (hj : 0 < j) (hjp : j ≤ p) (hf : ContDiff ℝ p f)
    {L B α δ₀ ζ : ℝ} (hL : 0 ≤ L) (hB : 0 < B) (hLB : L ≤ B)
    (hα : 0 < α) (hζ : ζ ≤ 1)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    {C : Set E} (hC : IsClosed C) (hconv : Convex ℝ C)
    (x : E) (hx : x ∈ C) (hmin : IsMinOn f C x)
    (hA : ∀ a, j < a → a ≤ p → ‖iteratedFDeriv ℝ a f x‖ ≤ B)
    (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ ≤ 1) :
    ∃ (d : ℕ → E) (N : ℕ),
      (∀ t, x + d t ∈ C ∧ ‖d t‖ ≤ BacktrackingGradient.step δ₀ t ∧
        ζ * TaylorModel.constrainedCriticality f j C x (BacktrackingGradient.step δ₀ t) ≤
          TaylorModel.decrement f j x (d t)) ∧
      CriticalHalvingRun f j x α δ₀ d N ∧
      min (α / (8 * B)) δ₀ ≤ BacktrackingGradient.step δ₀ N ∧
      (∀ t ≤ N, BacktrackingGradient.step δ₀ N ≤ BacktrackingGradient.step δ₀ t ∧
        BacktrackingGradient.step δ₀ t ≤ δ₀) ∧
      (j = 1 → N = 0) := by
  classical
  have hex : ∀ t, ∃ d, x + d ∈ C ∧ ‖d‖ ≤ BacktrackingGradient.step δ₀ t ∧
      TaylorModel.decrement f j x d =
        TaylorModel.constrainedCriticality f j C x (BacktrackingGradient.step δ₀ t) :=
    fun t => TaylorModel.exists_decrement_eq_constrainedCriticality f j hC hx
      (BacktrackingGradient.step_pos hδ₀ t).le
  choose d hd hn he using hex
  obtain ⟨N, hr, hfloor, hprefix⟩ := exists_constrained_criticalHalvingRun hj hjp hf hL hB
    hLB hα hlip x hx hmin hA hδ₀ hδ₀1 d hn hd
  refine ⟨d, N, fun t => ⟨hd t, hn t, ?_⟩, hr, hfloor, hprefix, ?_⟩
  · rw [he t]
    exact mul_le_of_le_one_left (TaylorModel.constrainedCriticality_nonneg f j hC hx
      (BacktrackingGradient.step_pos hδ₀ t).le) hζ
  · intro hj1
    have hp : 1 ≤ p := hj.trans_le hjp
    have hdiff : DifferentiableAt ℝ f x :=
      (hf.differentiable (by exact_mod_cast (show p ≠ 0 by omega))).differentiableAt
    have hz := TaylorModel.constrainedCriticality_one_eq_zero_of_isMinOn
      hC hconv hx hmin hdiff hδ₀.le
    have hdec := TaylorModel.decrement_le_constrainedCriticality f j hC (hd 0)
      (by simpa using hn 0)
    rw [hj1, hz] at hdec
    have hpass : CriticalityPasses f j x α δ₀ d 0 := by
      unfold CriticalityPasses
      simp only [BacktrackingGradient.step, pow_zero, div_one]
      rw [hj1]
      exact hdec.trans (by positivity)
    by_contra hN
    exact hr.rejected 0 (Nat.pos_of_ne_zero hN) hpass

end ModelSolve
