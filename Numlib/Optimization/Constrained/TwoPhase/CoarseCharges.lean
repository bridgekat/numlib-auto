import Numlib.Optimization.Constrained.TwoPhase.CoarseDecrease
import Numlib.Optimization.Constrained.TwoPhase.Termination

/-!
# Genuine merit and target charges for corrected two-phase calls

True accepted endpoints above a safe fractional tolerance consume merit.
Continuing reflections below that tolerance consume a uniform target drop.
Reset injections are paid separately and all actual merits telescope.
-/

namespace Constrained.TwoPhase
open Set TaylorModel EvaluationComplexity
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A continuing reflected target whose new criticality fails while its old
criticality is small must spend a positive actual target decrease. -/
theorem reflection_target_charge {f : E → ℝ} {c : E → F} {C : Set E} {x : E}
    (hf : ContDiffAt ℝ 1 f x) (hc : ContDiffAt ℝ 1 c x) (hC : IsClosed C) (hx : x ∈ C)
    {β ε₀ ε₁ θ B t : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1) (hε₁ : 0 < ε₁) (hB : 0 < B)
    (hDf : ‖fderiv ℝ f x‖ ≤ B) (hgap : f x < t)
    (hres : θ * ε₀ ≤ ‖residual f c t x‖)
    (hold : firstCriticality (targetMerit f c t) C x ≤ β * (ε₁ * θ * ε₀))
    (hnew : ε₁ * ‖residual f c t x‖ <
      firstCriticality (targetMerit f c (reflectTarget f t x)) C x) :
    (1 - β) * ε₁ * θ * ε₀ / B ≤ t - reflectTarget f t x := by
  have hold' : firstCriticality (targetMerit f c t) C x ≤
      β * (ε₁ * ‖residual f c t x‖) :=
    hold.trans (by nlinarith [mul_le_mul_of_nonneg_left hres (mul_nonneg hβ hε₁.le)])
  have hh := Constrained.reflection_gap_bound_of_criticality_failure hf hc hC hx
    zero_le_one hold' hnew
  have hT : Constrained.targetTaylorBound f 1 x 1 = ‖fderiv ℝ f x‖ := by
    simp [Constrained.targetTaylorBound, norm_iteratedFDeriv_one]
  rw [hT, abs_of_neg (sub_neg.mpr hgap)] at hh
  have hmul := mul_le_mul_of_nonneg_left hDf (show 0 ≤ 2 * -(f x - t) by linarith)
  have hlo := mul_le_mul_of_nonneg_left hres
    (mul_nonneg (sub_nonneg.mpr hβ1.le) hε₁.le)
  apply (div_le_iff₀ hB).mpr
  unfold reflectTarget
  nlinarith only [hh, hmul, hlo]

variable {p : ℕ} {f : E → ℝ} {c : E → F} {C S : Set E}
  {P : ConvexRegularization.Settings p} {ε₀ ε₁ θ L β : ℝ} {D : Data E} {N : ℕ}

/-- Actual accepted endpoints passing the safe fractional inner check. -/
noncomputable def goodSuccesses (P : ConvexRegularization.Settings p) (D : Data E)
    (f : E → ℝ) (c : E → F) (C : Set E) (ε₀ ε₁ θ β : ℝ) (k : ℕ) : Finset ℕ :=
  successfulIterations {i | P.eta1 ≤ (D.inner k).ratio i ∧
    β * (ε₁ * θ * ε₀) ≤ firstCriticality (targetMerit f c (D.target k)) C
      ((D.inner k).point (i + 1))} (D.length k)

omit [ProperSpace E] [InnerProductSpace ℝ F] in
/-- Membership records an actual accepted trial and its true endpoint check. -/
@[simp] theorem mem_goodSuccesses {k i : ℕ} :
    i ∈ goodSuccesses P D f c C ε₀ ε₁ θ β k ↔ i < D.length k ∧
      P.eta1 ≤ (D.inner k).ratio i ∧ β * (ε₁ * θ * ε₀) ≤
        firstCriticality (targetMerit f c (D.target k)) C ((D.inner k).point (i + 1)) := by
  simp only [goodSuccesses, mem_successfulIterations, Set.mem_ofPred_eq]

omit [InnerProductSpace ℝ F] in
/-- Every true good endpoint consumes the fixed fractional merit charge;
all other actual trials have nonincreasing merit. -/
theorem PhaseTwoRun.good_inner_budget
    (h : PhaseTwoRun true f c C P ε₀ ε₁ θ D N) {k : ℕ} (hk : k < N)
    (hclosed : IsClosed C) (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hf : ContDiffOn ℝ p (targetMerit f c (D.target k)) S) (hL : 0 < L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p (targetMerit f c (D.target k)) y -
        iteratedFDeriv ℝ p (targetMerit f c (D.target k)) z‖ ≤ L * ‖y - z‖)
    (hβ : P.theta < β) :
    (goodSuccesses P D f c C ε₀ ε₁ θ β k).card *
        (ConvexRegularization.fractionalDecreaseCoefficient P L β *
          (ε₁ * θ * ε₀) ^ (((p + 1 : ℕ) : ℝ) / p)) ≤
      targetMerit f c (D.target k) (D.point k) -
        targetMerit f c (D.target k) (D.point (k + 1)) := by
  have hh := card_successful_mul_le_gap
    (S := {i | P.eta1 ≤ (D.inner k).ratio i ∧ β * (ε₁ * θ * ε₀) ≤
      firstCriticality (targetMerit f c (D.target k)) C ((D.inner k).point (i + 1))})
    (f := fun i => targetMerit f c (D.target k) ((D.inner k).point i))
    (k := D.length k) (flow := targetMerit f c (D.target k) ((D.inner k).point (D.length k)))
    le_rfl (fun i hi hs => (h.inner_run k hk).fractional_successful_decrease hclosed hS hCS
      hC hf hL hlip hβ hi hs.1 hs.2)
    (fun i hi _ => (h.inner_run k hk).objective_succ_le hi)
  rw [h.inner_start k hk, h.inner_end k hk] at hh
  exact hh

end Constrained.TwoPhase

namespace Constrained.TwoPhase
open Set TaylorModel EvaluationComplexity
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] {p : ℕ} {f : E → ℝ} {c : E → F} {C : Set E}
  {P : ConvexRegularization.Settings p} {ε₀ ε₁ θ : ℝ} {D : Data E} {N : ℕ}

/-- True inner merit decreases telescope across all calls. Reflection costs
nothing, and each actual reset injects at most the initialized squared radius. -/
theorem PhaseTwoRun.total_merit_budget
    (h : PhaseTwoRun true f c C P ε₀ ε₁ θ D N) :
    (∑ k ∈ Finset.range N, (targetMerit f c (D.target k) (D.point k) -
      targetMerit f c (D.target k) (D.point (k + 1)))) ≤
      ε₀ ^ 2 / 2 * ((resetIterations true f c ε₀ θ D N).card + 1) := by
  classical
  let M := fun k => targetMerit f c (D.target k) (D.point k)
  have hbridge : ∀ k < N, M (k + 1) ≤ targetMerit f c (D.target k) (D.point (k + 1)) +
      if ResetGuard true f c ε₀ θ (D.target k) (D.point (k + 1)) then ε₀ ^ 2 / 2 else 0 := by
    intro k hk
    by_cases hr : ResetGuard true f c ε₀ θ (D.target k) (D.point (k + 1))
    · rw [ite_eq_left hr]
      have hm : M (k + 1) = ε₀ ^ 2 / 2 := by
        dsimp only [M]
        rw [targetMerit_eq_residual, h.reset_residual hk hr]
      rw [hm]
      have hn : 0 ≤ targetMerit f c (D.target k) (D.point (k + 1)) := by
        rw [targetMerit_eq_residual]
        positivity
      linarith only [hn]
    · rw [ite_eq_right hr, add_zero]
      dsimp only [M]
      rw [h.target_update k hk, nextTarget, ite_eq_right hr]
      split_ifs with hover
      · rw [targetMerit_eq_residual, targetMerit_eq_residual, residual_reflect]
      · exact le_rfl
  have hsum : (∑ k ∈ Finset.range N,
      if ResetGuard true f c ε₀ θ (D.target k) (D.point (k + 1)) then ε₀ ^ 2 / 2 else 0) =
        (resetIterations true f c ε₀ θ D N).card * (ε₀ ^ 2 / 2) := by
    simp [resetIterations, Finset.sum_ite]
  have hb : (∑ k ∈ Finset.range N, (targetMerit f c (D.target k) (D.point k) -
      targetMerit f c (D.target k) (D.point (k + 1)))) ≤
        M 0 - M N + (resetIterations true f c ε₀ θ D N).card * (ε₀ ^ 2 / 2) := by
    calc
      _ ≤ ∑ k ∈ Finset.range N, ((M k - M (k + 1)) +
          if ResetGuard true f c ε₀ θ (D.target k) (D.point (k + 1))
            then ε₀ ^ 2 / 2 else 0) := by
        apply Finset.sum_le_sum
        intro k hk
        have hh := hbridge k (Finset.mem_range.mp hk)
        change M k - _ ≤ _
        linarith only [hh]
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_range_sub', hsum]
  have hm0 : M 0 ≤ ε₀ ^ 2 / 2 := by
    dsimp only [M]
    rw [targetMerit_eq_residual]
    have hh := pow_le_pow_left₀ (norm_nonneg _) (h.invariants (Nat.zero_le N)).2 2
    linarith only [hh]
  have hmN : 0 ≤ M N := by dsimp [M]; rw [targetMerit_eq_residual]; positivity
  nlinarith only [hb, hm0, hmN]

end Constrained.TwoPhase

namespace Constrained.TwoPhase
open Set TaylorModel EvaluationComplexity
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] {p : ℕ} {f : E → ℝ} {c : E → F} {C : Set E}
  {P : ConvexRegularization.Settings p} {ε₀ ε₁ θ β : ℝ} {D : Data E} {N : ℕ}

/-- Continuing small-old-check reflections, determined by actual returned
points, target branches and criticalities. Their target decrease is proved. -/
noncomputable def badReflections (f : E → ℝ) (c : E → F) (C : Set E)
    (ε₀ ε₁ θ β : ℝ) (D : Data E) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter (fun k => k + 1 < N ∧
    ¬ResetGuard true f c ε₀ θ (D.target k) (D.point (k + 1)) ∧
    f (D.point (k + 1)) < D.target k ∧
    firstCriticality (targetMerit f c (D.target k)) C (D.point (k + 1)) ≤
      β * (ε₁ * θ * ε₀))

omit [ProperSpace E] in
/-- The exact operational characterization of a charged reflection index. -/
@[simp] theorem mem_badReflections {k : ℕ} :
    k ∈ badReflections f c C ε₀ ε₁ θ β D N ↔ k < N ∧ k + 1 < N ∧
      ¬ResetGuard true f c ε₀ θ (D.target k) (D.point (k + 1)) ∧
      f (D.point (k + 1)) < D.target k ∧
      firstCriticality (targetMerit f c (D.target k)) C (D.point (k + 1)) ≤
        β * (ε₁ * θ * ε₀) := by
  classical
  simp only [badReflections, Finset.mem_filter, Finset.mem_range]

omit [ProperSpace E] in
/-- Every call starts strictly above the reset radius; equality at the old
endpoint has already triggered a full closed reset. -/
theorem PhaseTwoRun.start_residual_gt (h : PhaseTwoRun true f c C P ε₀ ε₁ θ D N)
    {k : ℕ} (hk : k ≤ N) : θ * ε₀ < ‖residual f c (D.target k) (D.point k)‖ := by
  cases k with
  | zero =>
    rw [h.initial_target]
    have hc := h.initial_constraint.trans
      (mul_le_of_le_one_left h.primal_pos.le h.theta_lt_one.le)
    rw [residual_reset h.primal_pos.le hc]
    exact mul_lt_of_lt_one_left h.primal_pos h.theta_lt_one
  | succ k => exact CorrectedPhaseTwoRun.residual_gt h (by omega)

omit [ProperSpace E] in
/-- A zero-length call would immediately satisfy the outer stopping test,
so every continuing call performs an actual trial. -/
theorem PhaseTwoRun.continuing_length_pos (h : PhaseTwoRun true f c C P ε₀ ε₁ θ D N)
    {k : ℕ} (hk : k + 1 < N) : 0 < D.length k := by
  by_contra hn
  have hlen : D.length k = 0 := by omega
  have he : D.point (k + 1) = D.point k := by
    rw [← h.inner_end k (by omega), hlen, h.inner_start k (by omega)]
  have hres := h.start_residual_gt (show k ≤ N by omega)
  have hgap := (h.invariants (show k ≤ N by omega)).1
  have hreturn := h.inner_return k (by omega)
  rw [he] at hreturn
  have hr : ¬ResetGuard true f c ε₀ θ (D.target k) (D.point k) := by
    simpa only [ResetGuard, ite_true] using not_le_of_gt hres
  have hg : ¬f (D.point k) < D.target k := by linarith only [hgap]
  have hcrit : MeritTarget f c C ε₁ (D.target k) (D.point k) := by
    rcases hreturn with hh | hh | hh
    · exact (not_le_of_gt hres hh).elim
    · exact (hg hh).elim
    · exact hh
  apply h.continues k hk
  apply Or.inr
  rw [he, nextTarget, ite_eq_right hr, ite_eq_right hg]
  exact hcrit

omit [ProperSpace E] in
/-- The last trial of a positive-length first-return call must be accepted:
a rejected point would already have satisfied the return test one step earlier. -/
theorem PhaseTwoRun.terminal_accepted (h : PhaseTwoRun true f c C P ε₀ ε₁ θ D N)
    {k : ℕ} (hk : k < N) (hlen : 0 < D.length k) :
    P.eta1 ≤ (D.inner k).ratio (D.length k - 1) := by
  by_contra hn
  have hi : D.length k - 1 < D.length k := by omega
  have he : (D.inner k).point (D.length k) = (D.inner k).point (D.length k - 1) := by
    have hh := (h.inner_run k hk).modelTrace.point_update (D.length k - 1) hi
    rw [ite_eq_right hn] at hh
    simpa only [Nat.sub_add_cancel hlen] using hh
  apply h.inner_first k hk (D.length k - 1) hi
  rw [← he, h.inner_end k hk]
  exact h.inner_return k hk

end Constrained.TwoPhase

namespace Constrained.TwoPhase
open Set TaylorModel EvaluationComplexity
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {p : ℕ} {f : E → ℝ} {c : E → F}
  {C S : Set E} {P : ConvexRegularization.Settings p} {ε₀ ε₁ θ β L : ℝ}
  {D : Data E} {N : ℕ}

omit [InnerProductSpace ℝ F] in
/-- Aggregate actual good successful trials consume only initial merit and
actual reset injections, rather than an assumed reflection-block decrease. -/
theorem PhaseTwoRun.good_card_le (h : PhaseTwoRun true f c C P ε₀ ε₁ θ D N)
    (hclosed : IsClosed C) (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hf : ∀ k < N, ContDiffOn ℝ p (targetMerit f c (D.target k)) S) (hL : 0 < L)
    (hlip : ∀ k < N, ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p (targetMerit f c (D.target k)) y -
        iteratedFDeriv ℝ p (targetMerit f c (D.target k)) z‖ ≤ L * ‖y - z‖)
    (hβ : P.theta < β) :
    (∑ k ∈ Finset.range N, ((goodSuccesses P D f c C ε₀ ε₁ θ β k).card : ℝ)) ≤
      ε₀ ^ 2 / 2 * ((resetIterations true f c ε₀ θ D N).card + 1) /
        (ConvexRegularization.fractionalDecreaseCoefficient P L β *
          (ε₁ * θ * ε₀) ^ (((p + 1 : ℕ) : ℝ) / p)) := by
  have hd : 0 < ConvexRegularization.fractionalDecreaseCoefficient P L β *
      (ε₁ * θ * ε₀) ^ (((p + 1 : ℕ) : ℝ) / p) := by
    have := ConvexRegularization.fractionalDecreaseCoefficient_pos P hL hβ
    have := h.dual_pos
    have := h.theta_pos
    have := h.primal_pos
    positivity
  apply (le_div_iff₀ hd).mpr
  rw [Finset.sum_mul]
  apply le_trans _ h.total_merit_budget
  exact Finset.sum_le_sum fun k hk =>
    h.good_inner_budget (Finset.mem_range.mp hk) hclosed hS hCS hC
      (hf k (Finset.mem_range.mp hk)) hL (hlip k (Finset.mem_range.mp hk)) hβ

/-- Every actual small-check continuing reflection pays a uniform positive
target drop. The new-target test is evaluated at exactly the same feasible point. -/
theorem PhaseTwoRun.bad_reflection_drop (h : PhaseTwoRun true f c C P ε₀ ε₁ θ D N)
    (hclosed : IsClosed C) {B : ℝ} (hB : 0 < B) (hβ : 0 ≤ β) (hβ1 : β < 1)
    (hf : ∀ x ∈ C, ContDiffAt ℝ 1 f x) (hc : ∀ x ∈ C, ContDiffAt ℝ 1 c x)
    (hDf : ∀ x ∈ C, ‖c x‖ ≤ 1 → ‖fderiv ℝ f x‖ ≤ B)
    {k : ℕ} (hk : k ∈ badReflections f c C ε₀ ε₁ θ β D N) :
    (1 - β) * ε₁ * θ * ε₀ / B ≤ D.target k - D.target (k + 1) := by
  obtain ⟨hkN, hk1, hr, hover, hold⟩ := mem_badReflections.mp hk
  have hx := h.mem (show k + 1 ≤ N by omega)
  have ht : D.target (k + 1) = reflectTarget f (D.target k) (D.point (k + 1)) := by
    rw [h.target_update k hkN, nextTarget, ite_eq_right hr, ite_eq_left hover]
  have hres : θ * ε₀ ≤ ‖residual f c (D.target k) (D.point (k + 1))‖ := by
    exact (not_le.mp (by simpa only [ResetGuard, ite_true] using hr)).le
  have hnew : ε₁ * ‖residual f c (D.target k) (D.point (k + 1))‖ <
      firstCriticality (targetMerit f c (reflectTarget f (D.target k) (D.point (k + 1)))) C
        (D.point (k + 1)) := by
    apply lt_of_not_ge
    intro hn
    apply h.continues k hk1
    apply Or.inr
    rw [← h.target_update k hkN, ht]
    simpa only [MeritTarget, residual_reflect] using hn
  rw [ht]
  exact reflection_target_charge (hf _ hx) (hc _ hx) hclosed hx hβ hβ1 h.dual_pos hB
    (hDf _ hx ((h.component_bounds (by omega)).1.trans h.primal_le_one)) hover hres hold hnew

/-- The global target range pays for the actual bad reflection events, giving
the additional independent-accuracy term `epsilon0^-1 * epsilon1^-1`. -/
theorem PhaseTwoRun.bad_reflection_card_le (h : PhaseTwoRun true f c C P ε₀ ε₁ θ D N)
    (hclosed : IsClosed C) {B b flow fup : ℝ} (hB : 0 < B) (hβ : 0 ≤ β) (hβ1 : β < 1)
    (hf : ∀ x ∈ C, ContDiffAt ℝ 1 f x) (hc : ∀ x ∈ C, ContDiffAt ℝ 1 c x)
    (hDf : ∀ x ∈ C, ‖c x‖ ≤ 1 → ‖fderiv ℝ f x‖ ≤ B) (hb : ε₀ ≤ b)
    (hfb : ∀ x ∈ C, ‖c x‖ ≤ b → flow ≤ f x ∧ f x ≤ fup) :
    ((badReflections f c C ε₀ ε₁ θ β D N).card : ℝ) ≤
      (fup - flow + 1) / ((1 - β) * ε₁ * θ * ε₀ / B) := by
  let d := (1 - β) * ε₁ * θ * ε₀ / B
  have hd : 0 < d := by
    have := h.dual_pos
    have := h.theta_pos
    have := h.primal_pos
    dsimp [d]
    positivity
  have hs : ∀ k, k ∈ badReflections f c C ε₀ ε₁ θ β D N →
      d ≤ D.target k - D.target (k + 1) :=
    fun k hk => h.bad_reflection_drop hclosed hB hβ hβ1 hf hc hDf hk
  have hsum : ((badReflections f c C ε₀ ε₁ θ β D N).card : ℝ) * d ≤
      D.target 0 - D.target N := by
    calc
      _ = ∑ _k ∈ badReflections f c C ε₀ ε₁ θ β D N, d := by simp
      _ ≤ ∑ k ∈ badReflections f c C ε₀ ε₁ θ β D N,
          (D.target k - D.target (k + 1)) := Finset.sum_le_sum fun k hk => hs k hk
      _ ≤ ∑ k ∈ Finset.range N, (D.target k - D.target (k + 1)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          exact Finset.mem_range.mpr (mem_badReflections.mp hk).1
        · intro k hk _
          exact sub_nonneg.mpr (h.target_succ_le (Finset.mem_range.mp hk))
      _ = _ := Finset.sum_range_sub' D.target N
  have hbound : D.target 0 - D.target N ≤ fup - flow + 1 := by
    have hh0 := (h.target_bounds hb hfb (Nat.zero_le N)).2
    have hhN := (h.target_bounds hb hfb le_rfl).1
    linarith only [hh0, hhN]
  exact (le_div_iff₀ hd).mpr (hsum.trans hbound)

end Constrained.TwoPhase
