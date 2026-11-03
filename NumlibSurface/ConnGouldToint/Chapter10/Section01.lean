import Numlib.Optimization.ModelBased.ReferenceDecrease
import NumlibSurface.ConnGouldToint.Chapter06.Section04
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# A nonmonotone trust-region method

The historical sum can be zero when there are no accepted steps since the reference iteration.
The historical ratio still has a positive denominator because it includes the current predicted
reduction.
-/

open Filter Topology
open scoped BigOperators

namespace ConnGouldToint.Chapter10

/-- The logarithmically rescaled Rosenbrock objective (10.1.1). -/
noncomputable def logRosenbrock (x : ℝ × ℝ) : ℝ :=
  Real.log (1 + 10000 * (x.2 - x.1 ^ 2) ^ 2 + (1 - x.1) ^ 2)

/-- Reference indices for (10.1.2), corrected to allow the same index to be retained.
The reference objective decreases strictly whenever the reference index changes. -/
def IsReferenceSchedule (f : ℕ → ℝ) (r : ℕ → ℕ) : Prop :=
  (∀ k, r k ≤ k) ∧ ∀ k, r (k + 1) ≠ r k → f (r (k + 1)) < f (r k)

/-- An iteration contributes to the cumulative decrease only when accepted. -/
noncomputable def acceptedDecrease (S : Set ℕ) (d : ℕ → ℝ) (k : ℕ) : ℝ :=
  open Classical in if k ∈ S then d k else 0

/-- The acceptance ratio (10.1.3), the maximum of the historical and current ratios. -/
noncomputable def nonmonotoneRatio (S : Set ℕ) (f trial d : ℕ → ℝ) (r k : ℕ) : ℝ :=
  max ((f r - trial k) / ((∑ i ∈ Finset.Ico r k, acceptedDecrease S d i) + d k))
    ((f k - trial k) / d k)

/-- The nonmonotone acceptance rule accounts for every accepted model
decrease along the historical reference intervals. -/
theorem accepted_predicted_sum_le (S : Set ℕ) (f trial d : ℕ → ℝ) (r : ℕ → ℕ)
    {η : ℝ} (hr : ∀ k, r k ≤ k) (hd : ∀ k, 0 < d k)
    (hs : ∀ k ∈ S, η ≤ nonmonotoneRatio S f trial d (r k) k)
    (haccept : ∀ k ∈ S, f (k + 1) = trial k)
    (hreject : ∀ k ∉ S, f (k + 1) = f k) (k : ℕ) :
    η * (∑ i ∈ Finset.range (k + 1), acceptedDecrease S d i) ≤ f 0 - f (k + 1) := by
  classical
  have hpos (a j : ℕ) :
      0 < (∑ i ∈ Finset.Ico a j, acceptedDecrease S d i) + d j := by
    apply add_pos_of_nonneg_of_pos _ (hd j)
    apply Finset.sum_nonneg
    intro i _
    by_cases hi : i ∈ S
    · simpa [acceptedDecrease, hi] using (hd i).le
    · simp [acceptedDecrease, hi]
  have hstep (j : ℕ) : ∃ a ≤ j,
      (∑ i ∈ Finset.Ico a (j + 1), η * acceptedDecrease S d i) ≤ f a - f (j + 1) := by
    by_cases hj : j ∈ S
    · have h := hs j hj
      rw [nonmonotoneRatio, le_max_iff] at h
      rcases h with hh | hc
      · refine ⟨r j, hr j, ?_⟩
        rw [← Finset.mul_sum, Finset.sum_Ico_succ_top (hr j), acceptedDecrease,
          ite_eq_left hj, haccept j hj]
        exact (le_div_iff₀ (hpos (r j) j)).mp hh
      · refine ⟨j, le_rfl, ?_⟩
        simpa [Nat.Ico_succ_singleton, acceptedDecrease, hj, haccept j hj] using
          (le_div_iff₀ (hd j)).mp hc
    · refine ⟨j, le_rfl, ?_⟩
      simp [Nat.Ico_succ_singleton, acceptedDecrease, hj, hreject j hj]
  have h := Optimization.reference_decrease_sum f (fun i ↦ η * acceptedDecrease S d i) hstep (k + 1)
  rwa [← Finset.mul_sum] at h

/-- Lemma 10.1.1. Under the model decrease condition AA.1, the nonmonotone
acceptance rule yields a bound on the sum of decreases over successful iterations.
Here `f` and `trial` are the objective values at the iterates and trial points,
`d` is predicted reduction, and `g` is the gradient norm. -/
theorem lemma_10_1_1 (S : Set ℕ) (f trial d g β Δ : ℕ → ℝ) (r : ℕ → ℕ)
    {η κ : ℝ} (hη : 0 < η) (hr : ∀ k, r k ≤ k) (hd : ∀ k, 0 < d k)
    (haa : ∀ k, κ * (g k * min (g k / β k) (Δ k)) ≤ d k)
    (hs : ∀ k ∈ S, η ≤ nonmonotoneRatio S f trial d (r k) k)
    (haccept : ∀ k ∈ S, f (k + 1) = trial k)
    (hreject : ∀ k ∉ S, f (k + 1) = f k) (k : ℕ) :
    η * κ * (∑ i ∈ Finset.range (k + 1),
      acceptedDecrease S (fun j ↦ g j * min (g j / β j) (Δ j)) i) ≤ f 0 - f (k + 1) := by
  classical
  have hcost (i : ℕ) :
      κ * acceptedDecrease S (fun j ↦ g j * min (g j / β j) (Δ j)) i ≤
        acceptedDecrease S d i := by
    by_cases hi : i ∈ S
    · simpa [acceptedDecrease, hi] using haa i
    · simp [acceptedDecrease, hi]
  rw [mul_assoc, Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ ↦ hcost i)) hη.le).trans
    (accepted_predicted_sum_le S f trial d r hr hd hs haccept hreject k)

open Chapter06 in
/-- Theorem 10.1.2. The nonmonotone ratio dominates the current reduction ratio,
so the small-radius acceptance bound also prevents radius contraction here. -/
theorem theorem_10_1_2 {E : Type*} [NormedAddCommGroup E] {P : BTRParams}
    {f m : E → ℝ} {x s g : E} {β Δ Δ' κ C : ℝ}
    (S : Set ℕ) (values trial d : ℕ → ℝ) (r k : ℕ)
    (hvalues : values k = f x) (htrial : trial k = f (x + s)) (hd : d k = m x - m (x + s))
    (hβ : 0 < β) (hβC : β ≤ C) (hΔ : 0 < Δ) (hg : g ≠ 0)
    (hval : f x = m x) (hdec : HasSufficientModelDecrease m x s g β Δ κ)
    (herr : |f (x + s) - m (x + s)| ≤ C * Δ ^ 2)
    (hsmall : Δ ≤ κ * ‖g‖ * (1 - P.η₂) / C)
    (hupdate : BTRRadiusUpdate P (nonmonotoneRatio S values trial d r k) Δ Δ') :
    P.η₂ ≤ nonmonotoneRatio S values trial d r k ∧ Δ ≤ Δ' := by
  have hcurrent : P.η₂ ≤ btrRatio f m x s :=
    btrRatio_ge_eta₂_of_small_radius hβ hβC hΔ hg hval hdec herr hsmall
  have hdom : btrRatio f m x s ≤ nonmonotoneRatio S values trial d r k := by
    simp only [nonmonotoneRatio, hvalues, htrial, hd, btrRatio, Optimization.reductionRatio]
    exact le_max_right _ _
  exact ⟨hcurrent.trans hdom, hupdate.very_successful (hcurrent.trans hdom)⟩

open Chapter06

/-- An infinite run of Algorithm 10.1.1. The set of accepted indices is part
of the run, and the acceptance condition determines membership from the
earlier accepted decreases and the current trial. The ratios are evaluated
only for steps of positive predicted decrease. -/
structure NonmonotoneRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (P : BTRParams) where
  x : ℕ → E
  s : ℕ → E
  Δ : ℕ → ℝ
  p : ℕ → Seminorm ℝ E
  norm_separates : ∀ k v, p k v = 0 → v = 0
  model : ℕ → E → ℝ
  reference : ℕ → ℕ
  reference_schedule : IsReferenceSchedule (fun k ↦ f (x k)) reference
  successful : Set ℕ
  delta_initial_pos : 0 < Δ 0
  feasible : ∀ k, x k + s k ∈ trustRegion (p k) (x k) (Δ k)
  predicted_pos : ∀ k, 0 < model k (x k) - model k (x k + s k)
  accepted_iff : ∀ k, k ∈ successful ↔ P.η₁ ≤
    nonmonotoneRatio successful (fun j ↦ f (x j)) (fun j ↦ f (x j + s j))
      (fun j ↦ model j (x j) - model j (x j + s j)) (reference k) k
  accepted_update : ∀ k ∈ successful, x (k + 1) = x k + s k
  rejected_update : ∀ k ∉ successful, x (k + 1) = x k
  radius_update : ∀ k,
    BTRRadiusUpdate P
      (nonmonotoneRatio successful (fun j ↦ f (x j)) (fun j ↦ f (x j + s j))
        (fun j ↦ model j (x j) - model j (x j + s j)) (reference k) k)
      (Δ k) (Δ (k + 1))

namespace NonmonotoneRun

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {P : BTRParams}

/-- The reduction of the current model at the trial step. -/
noncomputable def predictedDecrease (run : NonmonotoneRun f P) (k : ℕ) : ℝ :=
  run.model k (run.x k) - run.model k (run.x k + run.s k)

/-- The ratio used by Algorithm 10.1.1 to update the iterate and radius. -/
noncomputable def ratio (run : NonmonotoneRun f P) (k : ℕ) : ℝ :=
  nonmonotoneRatio run.successful (fun j ↦ f (run.x j)) (fun j ↦ f (run.x j + run.s j))
    run.predictedDecrease (run.reference k) k

/-- Every trust-region radius of a nonmonotone run is positive. -/
theorem delta_pos (run : NonmonotoneRun f P) (k : ℕ) : 0 < run.Δ k := by
  induction k with
  | zero => exact run.delta_initial_pos
  | succ k ih => exact (run.radius_update k).pos ih

private theorem radius_lower_bound (run : NonmonotoneRun f P) {N : ℕ} {θ : ℝ}
    (hforce : ∀ k ≥ N, run.Δ k ≤ θ → P.η₂ ≤ run.ratio k)
    (k : ℕ) (hk : N ≤ k) :
    min (run.Δ N) (P.γ₁ * θ) ≤ run.Δ k := by
  induction k, hk using Nat.le_induction with
  | base => exact min_le_left _ _
  | succ k hk ih =>
    have hupdate : BTRRadiusUpdate P (run.ratio k) (run.Δ k) (run.Δ (k + 1)) :=
      run.radius_update k
    by_cases h₂ : P.η₂ ≤ run.ratio k
    · exact ih.trans (hupdate.very_successful h₂)
    have hθ := lt_of_not_ge (fun hle ↦ h₂ (hforce k hk hle))
    have hstep : P.γ₁ * run.Δ k ≤ run.Δ (k + 1) := by
      by_cases h₁ : P.η₁ ≤ run.ratio k
      · exact (mul_le_mul_of_nonneg_right P.gamma₁_le_gamma₂ (run.delta_pos k).le).trans
          (hupdate.successful h₁ (lt_of_not_ge h₂)).1
      · exact (hupdate.unsuccessful (lt_of_not_ge h₁)).1
    exact (min_le_right _ _).trans
      ((mul_le_mul_of_nonneg_left hθ.le P.gamma₁_pos.le).trans hstep)

end NonmonotoneRun

namespace NonmonotoneRun

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ} {P : BTRParams}

private noncomputable def decreaseCost (run : NonmonotoneRun f P) (β : ℕ → ℝ) : ℕ → ℝ :=
  acceptedDecrease run.successful (fun k ↦
    ‖gradient f (run.x k)‖ * min (‖gradient f (run.x k)‖ / β k) (run.Δ k))

private theorem decreaseCost_nonneg (run : NonmonotoneRun f P) (β : ℕ → ℝ)
    (hβ : ∀ k, 0 < β k) (k : ℕ) : 0 ≤ run.decreaseCost β k := by
  classical
  by_cases hk : k ∈ run.successful
  · simpa only [decreaseCost, acceptedDecrease, ite_eq_left hk] using
      mul_nonneg (norm_nonneg (gradient f (run.x k)))
        (le_min (div_nonneg (norm_nonneg _) (hβ k).le) (run.delta_pos k).le)
  · simp [decreaseCost, acceptedDecrease, hk]

private theorem cumulative_decreaseCost_le (run : NonmonotoneRun f P)
    (β : ℕ → ℝ) {κ : ℝ}
    (hdec : ∀ k, HasSufficientModelDecrease (run.model k) (run.x k) (run.s k)
      (gradient f (run.x k)) (β k) (run.Δ k) κ) (k : ℕ) :
    P.η₁ * κ * (∑ i ∈ Finset.range (k + 1), run.decreaseCost β i) ≤
      f (run.x 0) - f (run.x (k + 1)) :=
  lemma_10_1_1 run.successful (fun i ↦ f (run.x i)) (fun i ↦ f (run.x i + run.s i))
    run.predictedDecrease (fun i ↦ ‖gradient f (run.x i)‖) β run.Δ run.reference P.eta₁_pos
    run.reference_schedule.1 run.predicted_pos
    (fun i ↦ by simpa only [predictedDecrease, mul_assoc] using (hdec i).2)
    (fun i hi ↦ (run.accepted_iff i).mp hi)
    (fun i hi ↦ congrArg f (run.accepted_update i hi))
    (fun i hi ↦ congrArg f (run.rejected_update i hi)) k

private theorem summable_decreaseCost (run : NonmonotoneRun f P)
    (β : ℕ → ℝ) {κ : ℝ} (hβ : ∀ k, 0 < β k)
    (hdec : ∀ k, HasSufficientModelDecrease (run.model k) (run.x k) (run.s k)
      (gradient f (run.x k)) (β k) (run.Δ k) κ)
    (hlower : BddBelow (Set.range f)) : Summable (run.decreaseCost β) := by
  obtain ⟨lo, hlo⟩ := hlower
  have hscale : 0 < P.η₁ * κ := mul_pos P.eta₁_pos (hdec 0).1.1
  refine summable_of_sum_range_le (run.decreaseCost_nonneg β hβ)
    (c := (f (run.x 0) - lo) / (P.η₁ * κ)) ?_
  intro n
  cases n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    exact div_nonneg (sub_nonneg.mpr (hlo ⟨run.x 0, rfl⟩)) hscale.le
  | succ n =>
    have h := run.cumulative_decreaseCost_le β hdec n
    apply (le_div_iff₀ hscale).mpr
    rw [mul_comm]
    exact h.trans (sub_le_sub_left (hlo ⟨run.x (n + 1), rfl⟩) _)

private theorem truncated_radius_le_decreaseCost (run : NonmonotoneRun f P)
    (β : ℕ → ℝ) {C ε : ℝ} (hβ : ∀ k, 0 < β k) (hβC : ∀ k, β k ≤ C)
    (hε : 0 < ε) {k : ℕ} (hmem : k ∈ run.successful)
    (hgrad : ε ≤ ‖gradient f (run.x k)‖) :
    ε * min (ε / C) (run.Δ k) ≤ run.decreaseCost β k := by
  classical
  have hC : 0 < C := (hβ k).trans_le (hβC k)
  have hquot : ε / C ≤ ‖gradient f (run.x k)‖ / β k :=
    div_le_div₀ (norm_nonneg _) hgrad (hβ k) (hβC k)
  simpa only [decreaseCost, acceptedDecrease, ite_eq_left hmem] using
    mul_le_mul hgrad (min_le_min hquot le_rfl)
      (le_min (div_nonneg hε.le hC.le) (run.delta_pos k).le) (norm_nonneg _)

private theorem frequently_gradient_norm_lt (run : NonmonotoneRun f P)
    (β : ℕ → ℝ) {κ C : ℝ} (hβ : ∀ k, 0 < β k) (hβC : ∀ k, β k ≤ C)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hdec : ∀ k, HasSufficientModelDecrease (run.model k) (run.x k) (run.s k)
      (gradient f (run.x k)) (β k) (run.Δ k) κ)
    (herr : ∀ k, |f (run.x k + run.s k) - run.model k (run.x k + run.s k)| ≤
      C * (run.Δ k) ^ 2) (hsum : Summable (run.decreaseCost β)) :
    ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop, ‖gradient f (run.x k)‖ < ε := by
  classical
  intro ε hε
  by_contra h
  have hevent : ∀ᶠ k in atTop, ε ≤ ‖gradient f (run.x k)‖ := by
    simpa only [Filter.Frequently, not_not, not_lt] using h
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  have hC : 0 < C := (hβ 0).trans_le (hβC 0)
  have hκ : 0 < κ := (hdec 0).1.1
  have hη : 0 < 1 - P.η₂ := sub_pos.mpr P.eta₂_lt_one
  let θ := κ * ε * (1 - P.η₂) / C
  have hθ : 0 < θ := div_pos (mul_pos (mul_pos hκ hε) hη) hC
  have hforce (k : ℕ) (hk : N ≤ k) (hsmall : run.Δ k ≤ θ) : P.η₂ ≤ run.ratio k :=
    (theorem_10_1_2 run.successful (fun j ↦ f (run.x j)) (fun j ↦ f (run.x j + run.s j))
      run.predictedDecrease (run.reference k) k rfl rfl rfl (hβ k) (hβC k) (run.delta_pos k)
      (norm_pos_iff.mp (hε.trans_le (hN k hk))) (hval k) (hdec k) (herr k)
      (hsmall.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hN k hk) hκ.le) hη.le) hC.le))
      (run.radius_update k)).1
  let r := min (run.Δ N) (P.γ₁ * θ)
  have hr : 0 < r := lt_min (run.delta_pos N) (mul_pos P.gamma₁_pos hθ)
  let a := ε * min (ε / C) r
  have ha : 0 < a := mul_pos hε (lt_min (div_pos hε hC) hr)
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hsum.tendsto_atTop_zero.eventually (gt_mem_nhds ha))
  let M := max N J
  have hfail (k : ℕ) (hk : M ≤ k) : run.ratio k < P.η₁ := by
    apply lt_of_not_ge
    intro haccepted
    have hmem := (run.accepted_iff k).mpr haccepted
    have hgrad := hN k ((le_max_left N J).trans hk)
    have hrk : r ≤ run.Δ k := run.radius_lower_bound hforce k ((le_max_left N J).trans hk)
    have hcost : a ≤ run.decreaseCost β k :=
      (mul_le_mul_of_nonneg_left (min_le_min le_rfl hrk) hε.le).trans
        (run.truncated_radius_le_decreaseCost β hβ hβC hε hmem hgrad)
    exact (hJ k ((le_max_right N J).trans hk)).not_ge hcost
  have hγ : 0 < P.γ₂ := P.gamma₁_pos.trans_le P.gamma₁_le_gamma₂
  have hrad (j : ℕ) : run.Δ (M + j) ≤ P.γ₂ ^ j * run.Δ M := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hupdate : BTRRadiusUpdate P (run.ratio (M + j)) (run.Δ (M + j))
          (run.Δ (M + j + 1)) := run.radius_update (M + j)
      calc
        run.Δ (M + (j + 1)) ≤ P.γ₂ * run.Δ (M + j) :=
          (hupdate.unsuccessful (hfail _ (Nat.le_add_right _ _))).2
        _ ≤ P.γ₂ * (P.γ₂ ^ j * run.Δ M) := mul_le_mul_of_nonneg_left ih hγ.le
        _ = P.γ₂ ^ (j + 1) * run.Δ M := by rw [pow_succ]; ring
  have hlim : Tendsto (fun j : ℕ ↦ P.γ₂ ^ j * run.Δ M) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hγ.le P.gamma₂_lt_one).mul_const (run.Δ M)
  obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds hr)).exists
  have hjN : N ≤ M + j := (le_max_left N J).trans (Nat.le_add_right _ _)
  exact hj.not_ge ((run.radius_lower_bound hforce (M + j) hjN).trans (hrad j))

end NonmonotoneRun

section Convergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ} {P : BTRParams}

/-- The high-gradient radius sum in (10.1.13), with the curvature bound `C`.
Only accepted iterations with gradient norm at least `ε` contribute. -/
theorem high_gradient_radius_sum_le (run : NonmonotoneRun f P)
    (β : ℕ → ℝ) {κ C ε : ℝ} (hβ : ∀ k, 0 < β k) (hβC : ∀ k, β k ≤ C)
    (hdec : ∀ k, HasSufficientModelDecrease (run.model k) (run.x k) (run.s k)
      (gradient f (run.x k)) (β k) (run.Δ k) κ)
    (hε : 0 < ε) (k : ℕ) :
    P.η₁ * κ * ε * (∑ i ∈ Finset.range (k + 1),
      acceptedDecrease {j | j ∈ run.successful ∧ ε ≤ ‖gradient f (run.x j)‖}
        (fun j ↦ min (ε / C) (run.Δ j)) i) ≤ f (run.x 0) - f (run.x (k + 1)) := by
  classical
  let S := {j | j ∈ run.successful ∧ ε ≤ ‖gradient f (run.x j)‖}
  have hcost (i : ℕ) :
      ε * acceptedDecrease S (fun j ↦ min (ε / C) (run.Δ j)) i ≤ run.decreaseCost β i := by
    by_cases hi : i ∈ S
    · change i ∈ run.successful ∧ ε ≤ ‖gradient f (run.x i)‖ at hi
      exact (by
        simp only [acceptedDecrease, ite_eq_left (show i ∈ S from hi)]
        exact run.truncated_radius_le_decreaseCost β hβ hβC hε hi.1 hi.2)
    · simpa only [acceptedDecrease, ite_eq_right hi, mul_zero] using
        run.decreaseCost_nonneg β hβ i
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range (k + 1)) ↦ hcost i)
  rw [← Finset.mul_sum] at hsum
  rw [mul_assoc]
  exact (mul_le_mul_of_nonneg_left hsum (mul_nonneg P.eta₁_pos.le (hdec 0).1.1.le)).trans
    (run.cumulative_decreaseCost_le β hdec k)

/-- The accepted-iteration count estimate (10.1.11) under uniform lower bounds
on the gradient norms and radii. The count includes iteration zero. -/
theorem successful_count_le (run : NonmonotoneRun f P) [DecidablePred (· ∈ run.successful)]
    (β : ℕ → ℝ) {κ C ε δ : ℝ} (hβ : ∀ k, 0 < β k) (hβC : ∀ k, β k ≤ C)
    (hdec : ∀ k, HasSufficientModelDecrease (run.model k) (run.x k) (run.s k)
      (gradient f (run.x k)) (β k) (run.Δ k) κ)
    (hε : 0 < ε) (hgrad : ∀ k, ε ≤ ‖gradient f (run.x k)‖)
    (hrad : ∀ k, δ ≤ run.Δ k) (k : ℕ) :
    P.η₁ * κ * ε * (((Finset.range (k + 1)).filter (· ∈ run.successful)).card *
      min (ε / C) δ) ≤ f (run.x 0) - f (run.x (k + 1)) := by
  have hS : {j | j ∈ run.successful ∧ ε ≤ ‖gradient f (run.x j)‖} = run.successful := by
    ext j
    simp [hgrad j]
  have hsum := high_gradient_radius_sum_le run β hβ hβC hdec hε k
  rw [hS] at hsum
  have hle :
      ((Finset.range (k + 1)).filter (· ∈ run.successful)).card * min (ε / C) δ ≤
        ∑ i ∈ Finset.range (k + 1),
          acceptedDecrease run.successful (fun j ↦ min (ε / C) (run.Δ j)) i := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    simpa only [Finset.sum_filter, acceptedDecrease] using
      (Finset.sum_le_sum (fun i (_ : i ∈ (Finset.range (k + 1)).filter (· ∈ run.successful)) ↦
        min_le_min le_rfl (hrad i)))
  exact (mul_le_mul_of_nonneg_left hle (by positivity [P.eta₁_pos, (hdec 0).1.1])).trans hsum

/-- The radii of accepted high-gradient iterations are summable, as in (10.1.14).
Including the finite initial part does not affect summability. -/
theorem summable_high_gradient_radius (run : NonmonotoneRun f P)
    (β : ℕ → ℝ) {κ C ε : ℝ} (hβ : ∀ k, 0 < β k) (hβC : ∀ k, β k ≤ C)
    (hdec : ∀ k, HasSufficientModelDecrease (run.model k) (run.x k) (run.s k)
      (gradient f (run.x k)) (β k) (run.Δ k) κ)
    (hlower : BddBelow (Set.range f)) (hε : 0 < ε) :
    Summable (acceptedDecrease
      {j | j ∈ run.successful ∧ ε ≤ ‖gradient f (run.x j)‖} run.Δ) := by
  classical
  let S := {j | j ∈ run.successful ∧ ε ≤ ‖gradient f (run.x j)‖}
  have hC : 0 < C := (hβ 0).trans_le (hβC 0)
  have hsum := run.summable_decreaseCost β hβ hdec hlower
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hsum.tendsto_atTop_zero.eventually (gt_mem_nhds (mul_pos hε (div_pos hε hC))))
  change Summable (acceptedDecrease S run.Δ)
  apply (summable_nat_add_iff N).mp
  refine Summable.of_nonneg_of_le (f := fun j ↦ run.decreaseCost β (j + N) / ε) ?_ ?_
    (((summable_nat_add_iff N).mpr hsum).div_const ε)
  · intro j
    by_cases hj : j + N ∈ S
    · simpa only [acceptedDecrease, ite_eq_left hj] using (run.delta_pos (j + N)).le
    · simp only [acceptedDecrease, ite_eq_right hj, le_refl]
  · intro j
    by_cases hj : j + N ∈ S
    · have hmem : j + N ∈ run.successful ∧ ε ≤ ‖gradient f (run.x (j + N))‖ := hj
      have hcost := run.truncated_radius_le_decreaseCost β hβ hβC hε hmem.1 hmem.2
      have hrad : run.Δ (j + N) ≤ ε / C := by
        by_contra! hn
        rw [min_eq_left hn.le] at hcost
        exact (hN _ (Nat.le_add_left N j)).not_ge hcost
      rw [min_eq_right hrad] at hcost
      simpa only [acceptedDecrease, ite_eq_left hj] using
        (le_div_iff₀ hε).mpr ((mul_comm _ _).le.trans hcost)
    · simpa only [acceptedDecrease, ite_eq_right hj] using
        div_nonneg (run.decreaseCost_nonneg β hβ (j + N)) hε.le

/-- Theorem 10.1.3. The gradient norms of the nonmonotone run have zero limit inferior.
The quadratic model error is the consequence of AF.1, AF.3, AN.1, and AM.1–4
from Theorem 6.4.1. The proof excludes a positive gradient lower bound on
every tail, which is the condition needed for the limit inferior. -/
theorem theorem_10_1_3_of_error_bound (run : NonmonotoneRun f P)
    (β : ℕ → ℝ) {κ C : ℝ} (hβ : ∀ k, 0 < β k) (hβC : ∀ k, β k ≤ C)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hdec : ∀ k, HasSufficientModelDecrease (run.model k) (run.x k) (run.s k)
      (gradient f (run.x k)) (β k) (run.Δ k) κ)
    (herr : ∀ k, |f (run.x k + run.s k) - run.model k (run.x k + run.s k)| ≤
      C * (run.Δ k) ^ 2) (hlower : BddBelow (Set.range f)) :
    liminf (fun k ↦ ‖gradient f (run.x k)‖) atTop = 0 := by
  let u (k : ℕ) := ‖gradient f (run.x k)‖
  have hfreq := run.frequently_gradient_norm_lt β hβ hβC hval hdec herr
    (run.summable_decreaseCost β hβ hdec hlower)
  have hb : (atTop : Filter ℕ).IsBoundedUnder (· ≥ ·) u :=
    ⟨0, show ∀ᶠ k in atTop, 0 ≤ u k from Eventually.of_forall fun _ ↦ norm_nonneg _⟩
  have hco : (atTop : Filter ℕ).IsCoboundedUnder (· ≥ ·) u := by
    refine ⟨1, fun b hb' ↦ ?_⟩
    obtain ⟨k, hk, hk'⟩ := ((hfreq 1 zero_lt_one).and_eventually hb').exists
    exact hk'.trans hk.le
  change liminf u atTop = 0
  refine le_antisymm ?_ (le_liminf_of_le hco (Eventually.of_forall fun _ ↦ norm_nonneg _))
  by_contra! hp
  have hlim := liminf_le_of_frequently_le ((hfreq _ (half_pos hp)).mono fun _ h ↦ h.le) hb
  linarith

/-- Theorem 10.1.4. The whole gradient norm sequence of the nonmonotone run tends
to zero. Uniform gradient continuity comes from the bounded Hessian in AF.3.
The argument controls the motion on high-gradient stretches by a tail of the
summable accepted decrease costs, so it permits increases in the objective. -/
theorem theorem_10_1_4_of_error_bound (run : NonmonotoneRun f P)
    (β : ℕ → ℝ) {κ C L K : ℝ} (hβ : ∀ k, 0 < β k) (hβC : ∀ k, β k ≤ C)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hdec : ∀ k, HasSufficientModelDecrease (run.model k) (run.x k) (run.s k)
      (gradient f (run.x k)) (β k) (run.Δ k) κ)
    (herr : ∀ k, |f (run.x k + run.s k) - run.model k (run.x k + run.s k)| ≤
      C * (run.Δ k) ^ 2) (hlower : BddBelow (Set.range f))
    (hf : ContDiff ℝ 2 f) (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ L) (hK : 0 ≤ K)
    (hnorm : ∀ k v, ‖v‖ ≤ K * run.p k v) :
    Tendsto (fun k ↦ ‖gradient f (run.x k)‖) atTop (𝓝 0) := by
  classical
  have hL : 0 ≤ L := (norm_nonneg (fderiv ℝ (fderiv ℝ f) 0)).trans (hH 0)
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hgrad (x y : E) : ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖ := by
    unfold gradient
    rw [← map_sub, LinearIsometryEquiv.norm_map]
    exact Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ ↦ hDf.differentiable (by norm_num) z)
      (fun z _ ↦ hH z) (convex_univ : Convex ℝ (Set.univ : Set E)) (Set.mem_univ y) (Set.mem_univ x)
  let u (k : ℕ) := ‖gradient f (run.x k)‖
  let cost := run.decreaseCost β
  let cumulative (k : ℕ) := ∑ i ∈ Finset.range k, cost i
  let total := ∑' i, cost i
  have hnonneg := run.decreaseCost_nonneg β hβ
  have hsum := run.summable_decreaseCost β hβ hdec hlower
  have hfreq := run.frequently_gradient_norm_lt β hβ hβC hval hdec herr hsum
  have htail : Tendsto (fun k ↦ total - cumulative k) atTop (𝓝 0) := by
    simpa only [total, cumulative, cost, sub_self] using
      (tendsto_const_nhds (x := total)).sub hsum.hasSum.tendsto_sum_nat
  have hC : 0 < C := (hβ 0).trans_le (hβC 0)
  have hLK : 0 ≤ L * K := mul_nonneg hL hK
  rw [Metric.tendsto_atTop]
  intro ε hε
  let e := ε / 2
  have he : 0 < e := half_pos hε
  have hLK₁ : 0 < L * K + 1 := by linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hsum.tendsto_atTop_zero.eventually (gt_mem_nhds (mul_pos he (div_pos he hC))))
  obtain ⟨J, hJ⟩ := eventually_atTop.mp
    (htail.eventually (gt_mem_nhds (div_pos (mul_pos he he) hLK₁)))
  have hstep (i : ℕ) (hi : N ≤ i) (hu : e ≤ u i) :
      e * (u i - u (i + 1)) ≤ (L * K) * cost i := by
    by_cases hs : i ∈ run.successful
    · have hcost : e * min (e / C) (run.Δ i) ≤ cost i :=
        run.truncated_radius_le_decreaseCost β hβ hβC he hs hu
      have hrad : run.Δ i ≤ e / C := by
        by_contra! hn
        rw [min_eq_left hn.le] at hcost
        exact (hN i hi).not_ge hcost
      rw [min_eq_right hrad] at hcost
      have hdist : ‖run.x i - run.x (i + 1)‖ ≤ K * run.Δ i := by
        rw [run.accepted_update i hs, sub_add_cancel_left, norm_neg]
        exact (hnorm i _).trans (mul_le_mul_of_nonneg_left
          (by simpa [trustRegion] using run.feasible i) hK)
      have hgradstep : u i - u (i + 1) ≤ (L * K) * run.Δ i := by
        calc
          _ ≤ ‖gradient f (run.x i) - gradient f (run.x (i + 1))‖ := norm_sub_norm_le _ _
          _ ≤ L * ‖run.x i - run.x (i + 1)‖ := hgrad _ _
          _ ≤ L * (K * run.Δ i) := mul_le_mul_of_nonneg_left hdist hL
          _ = _ := by ring
      calc
        _ ≤ e * ((L * K) * run.Δ i) := mul_le_mul_of_nonneg_left hgradstep he.le
        _ = (L * K) * (e * run.Δ i) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hcost hLK
    · simp only [u, run.rejected_update i hs, sub_self, mul_zero, cost,
        NonmonotoneRun.decreaseCost, acceptedDecrease, ite_eq_right hs, le_refl]
  refine ⟨max N J, fun k hk ↦ ?_⟩
  have hkN := (le_max_left N J).trans hk
  have hkJ := (le_max_right N J).trans hk
  change dist (u k) 0 < ε
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  by_contra! hhigh
  have hex : ∃ j, k ≤ j ∧ u j < e := frequently_atTop.mp (hfreq e he) k
  let j := Nat.find hex
  have hj : k ≤ j ∧ u j < e := Nat.find_spec hex
  have htel (i : ℕ) (hi : k ≤ i) : i ≤ j →
      e * (u k - u i) ≤ (L * K) * (cumulative i - cumulative k) := by
    induction i, hi using Nat.le_induction with
    | base => simp
    | succ i hi ih =>
      intro hij
      have hbelow : i < j := Nat.lt_of_succ_le hij
      have hui : e ≤ u i := le_of_not_gt fun hlt ↦ (Nat.find_min hex hbelow) ⟨hi, hlt⟩
      have hrec : cumulative (i + 1) = cumulative i + cost i := Finset.sum_range_succ _ _
      rw [hrec]
      linarith only [ih hbelow.le, hstep i (hkN.trans hi) hui]
  have hgap : e < u k - u j := by dsimp [e] at hj ⊢; linarith [hj.2]
  have hle : cumulative j ≤ total := Summable.sum_le_tsum _ (fun i _ ↦ hnonneg i) hsum
  have htail_nonneg : 0 ≤ total - cumulative k :=
    sub_nonneg.mpr (Summable.sum_le_tsum _ (fun i _ ↦ hnonneg i) hsum)
  have hbound : (L * K) * (cumulative j - cumulative k) < e * e := calc
    _ ≤ (L * K) * (total - cumulative k) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right hle _) hLK
    _ ≤ (L * K + 1) * (total - cumulative k) := by gcongr; linarith
    _ < _ := by
      have hsmall := (lt_div_iff₀ hLK₁).mp (hJ k hkJ)
      simpa only [mul_comm] using hsmall
  exact hbound.not_ge ((mul_le_mul_of_nonneg_left hgap.le he.le).trans (htel j hj.1 le_rfl))

omit [CompleteSpace E] in
private theorem trial_error_of_uniform_hessian (run : NonmonotoneRun f P)
    {K κf κm : ℝ} (hK : 1 ≤ K) (hκm : 1 ≤ κm)
    (hnorm : ∀ k v, ‖v‖ ≤ K * run.p k v)
    (hf : ContDiff ℝ 2 f) (hF : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ κf)
    (hm : ∀ k, ∀ z ∈ (run.p k).closedBall (run.x k) (run.Δ k), DifferentiableAt ℝ (run.model k) z)
    (hDm : ∀ k, ∀ z ∈ (run.p k).closedBall (run.x k) (run.Δ k),
      DifferentiableAt ℝ (fderiv ℝ (run.model k)) z)
    (hM : ∀ k, ∀ z ∈ (run.p k).closedBall (run.x k) (run.Δ k),
      ‖fderiv ℝ (fderiv ℝ (run.model k)) z‖ ≤ κm - 1)
    (hval : ∀ k, run.model k (run.x k) = f (run.x k))
    (hgrad : ∀ k, fderiv ℝ (run.model k) (run.x k) = fderiv ℝ f (run.x k)) (k : ℕ) :
    |f (run.x k + run.s k) - run.model k (run.x k + run.s k)| ≤
      uniformHessianConstant K κf κm * (run.Δ k) ^ 2 := by
  have hs : run.p k (run.s k) ≤ run.Δ k := by
    simpa [trustRegion] using run.feasible k
  exact (theorem_6_4_1 (run.p k) (run.norm_separates k) (run.delta_pos k).le hκm hs hf hF
    (hm k) (hDm k) (hM k) (hval k) (hgrad k)).2 K (zero_le_one.trans hK) (hnorm k)

private theorem le_uniformHessianConstant {K κf κm : ℝ} (hK : 1 ≤ K) (hκm : 1 ≤ κm) :
    κm ≤ uniformHessianConstant K κf κm := by
  have hK₂ : 1 ≤ K ^ 2 := by nlinarith
  calc
    κm ≤ max κf κm := le_max_right _ _
    _ ≤ K ^ 2 * max κf κm :=
      le_mul_of_one_le_left ((zero_le_one.trans hκm).trans (le_max_right _ _)) hK₂

/-- Theorem 10.1.3 under the uniform Hessian bounds and first-order model agreement.
The curvature parameters of the decrease test are bounded as in (6.3.2) and AM.4. -/
theorem theorem_10_1_3 (run : NonmonotoneRun f P)
    (β : ℕ → ℝ) {κ K κf κm : ℝ} (hK : 1 ≤ K) (hκm : 1 ≤ κm)
    (hβ : ∀ k, 0 < β k) (hβm : ∀ k, β k ≤ κm)
    (hnorm : ∀ k v, ‖v‖ ≤ K * run.p k v)
    (hf : ContDiff ℝ 2 f) (hF : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ κf)
    (hm : ∀ k, ∀ z ∈ (run.p k).closedBall (run.x k) (run.Δ k), DifferentiableAt ℝ (run.model k) z)
    (hDm : ∀ k, ∀ z ∈ (run.p k).closedBall (run.x k) (run.Δ k),
      DifferentiableAt ℝ (fderiv ℝ (run.model k)) z)
    (hM : ∀ k, ∀ z ∈ (run.p k).closedBall (run.x k) (run.Δ k),
      ‖fderiv ℝ (fderiv ℝ (run.model k)) z‖ ≤ κm - 1)
    (hval : ∀ k, run.model k (run.x k) = f (run.x k))
    (hgrad : ∀ k, fderiv ℝ (run.model k) (run.x k) = fderiv ℝ f (run.x k))
    (hdec : ∀ k, HasSufficientModelDecrease (run.model k) (run.x k) (run.s k)
      (gradient f (run.x k)) (β k) (run.Δ k) κ)
    (hlower : BddBelow (Set.range f)) :
    liminf (fun k ↦ ‖gradient f (run.x k)‖) atTop = 0 :=
  theorem_10_1_3_of_error_bound run β hβ
    (fun k ↦ (hβm k).trans (le_uniformHessianConstant hK hκm)) (fun k ↦ (hval k).symm) hdec
    (trial_error_of_uniform_hessian run hK hκm hnorm hf hF hm hDm hM hval hgrad) hlower

/-- Theorem 10.1.4 under the uniform Hessian bounds and first-order model agreement.
The bounded objective Hessian supplies the uniform gradient estimate along the iterates. -/
theorem theorem_10_1_4 (run : NonmonotoneRun f P)
    (β : ℕ → ℝ) {κ K κf κm : ℝ} (hK : 1 ≤ K) (hκm : 1 ≤ κm)
    (hβ : ∀ k, 0 < β k) (hβm : ∀ k, β k ≤ κm)
    (hnorm : ∀ k v, ‖v‖ ≤ K * run.p k v)
    (hf : ContDiff ℝ 2 f) (hF : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ κf)
    (hm : ∀ k, ∀ z ∈ (run.p k).closedBall (run.x k) (run.Δ k), DifferentiableAt ℝ (run.model k) z)
    (hDm : ∀ k, ∀ z ∈ (run.p k).closedBall (run.x k) (run.Δ k),
      DifferentiableAt ℝ (fderiv ℝ (run.model k)) z)
    (hM : ∀ k, ∀ z ∈ (run.p k).closedBall (run.x k) (run.Δ k),
      ‖fderiv ℝ (fderiv ℝ (run.model k)) z‖ ≤ κm - 1)
    (hval : ∀ k, run.model k (run.x k) = f (run.x k))
    (hgrad : ∀ k, fderiv ℝ (run.model k) (run.x k) = fderiv ℝ f (run.x k))
    (hdec : ∀ k, HasSufficientModelDecrease (run.model k) (run.x k) (run.s k)
      (gradient f (run.x k)) (β k) (run.Δ k) κ)
    (hlower : BddBelow (Set.range f)) :
    Tendsto (fun k ↦ ‖gradient f (run.x k)‖) atTop (𝓝 0) :=
  theorem_10_1_4_of_error_bound run β hβ
    (fun k ↦ (hβm k).trans (le_uniformHessianConstant hK hκm)) (fun k ↦ (hval k).symm) hdec
    (trial_error_of_uniform_hessian run hK hκm hnorm hf hF hm hDm hM hval hgrad)
    hlower hf hF (zero_le_one.trans hK) hnorm

end Convergence

end ConnGouldToint.Chapter10
