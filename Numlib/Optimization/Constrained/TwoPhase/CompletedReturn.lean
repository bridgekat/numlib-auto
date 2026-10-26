import Numlib.Optimization.Constrained.TwoPhase.CompletedRun

/-!
# True stopping certificates for completed-inner target calls

The bounded actual target interval supplies the common merit regularity.
Extracted genuine inner certificates then justify both actual outer stopping
branches. Closed reset and reflection rules exclude a feasible zero-gap return.
-/

namespace Constrained.TwoPhase.CompletedRun
open Set InexactTrustRegion
open HighOrderRegularization (parameterCap)
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  {p q : ℕ} {f : E → ℝ} {c : E → F} {X : Set E}
  {P : ConstrainedRegularization.Settings p q} {β θ ε₀ L : ℝ} {ε : Fin q → ℝ}
  {D : CompletedData E q} {N : ℕ}

/-- Actual completed inner calls yield true old-target certificates and the
fixed quantitative solver radius floor throughout the derived target interval. -/
theorem inner_certificate (h : CompletedRun f c X P β θ ε₀ L ε D N)
    (hX : IsClosed X) (hconv : Convex ℝ X) (hL : 1 ≤ L) {flow fup : ℝ}
    (hfband : ∀ z ∈ X, ‖c z‖ ≤ 1 → flow ≤ f z ∧ f z ≤ fup)
    (hreg : ∀ t ∈ Icc (flow - 1) fup, ContDiff ℝ p (targetMerit f c t) ∧
      ∀ i, 1 ≤ i → i ≤ p → ∀ y z,
        ‖iteratedFDeriv ℝ i (targetMerit f c t) y -
          iteratedFDeriv ℝ i (targetMerit f c t) z‖ ≤ L * ‖y - z‖)
    {k : ℕ} (hk : k < N) :
    let δ := completedRadius (targetMerit f c (D.target k)) X P
      (completedInnerAccuracy β θ ε₀ ε) (D.inner k) (D.length k) L
    ConstrainedRegularization.OptimalityAt (targetMerit f c (D.target k)) X
      (completedInnerAccuracy β θ ε₀ ε) (D.point (k + 1)) δ ∧
      ∀ a, ConstrainedRegularization.radiusCoefficient P L (parameterCap P L) *
        completedInnerAccuracy β θ ε₀ ε a ≤ δ a := by
  obtain ⟨hsm, hlip⟩ := hreg (D.target k) (h.target_bounds hfband hk.le)
  have hi : CompletedRadiusInputs (targetMerit f c (D.target k)) X P
      (completedInnerAccuracy β θ ε₀ ε) (D.inner k) (D.length k) L :=
    ⟨hX, hconv, hsm, hL, hlip, h.inner_run k hk, h.inner_target k hk, h.inner_radius k hk⟩
  have hh := completedRadius_spec hi
  rwa [h.inner_end k hk] at hh

/-- Both actual stopping branches yield legal radii and the true normalized
updated-target certificate. Fallback uses the strictly stronger completed inner test. -/
theorem target_of_stop (h : CompletedRun f c X P β θ ε₀ L ε D N)
    (hX : IsClosed X) (hconv : Convex ℝ X) (hL : 1 ≤ L) {flow fup : ℝ}
    (hfband : ∀ z ∈ X, ‖c z‖ ≤ 1 → flow ≤ f z ∧ f z ≤ fup)
    (hreg : ∀ t ∈ Icc (flow - 1) fup, ContDiff ℝ p (targetMerit f c t) ∧
      ∀ i, 1 ≤ i → i ≤ p → ∀ y z,
        ‖iteratedFDeriv ℝ i (targetMerit f c t) y -
          iteratedFDeriv ℝ i (targetMerit f c t) z‖ ≤ L * ‖y - z‖)
    {k : ℕ} (hk : k < N) (hs : CompletedStopAfter f c X P β θ ε₀ L ε D k) :
    let δ := completedRadius (targetMerit f c (D.target k)) X P
      (completedInnerAccuracy β θ ε₀ ε) (D.inner k) (D.length k) L
    (∀ a, 0 < δ a ∧ δ a ≤ 1) ∧
      CompletedMeritTarget f c X ε (D.target (k + 1)) (D.point (k + 1)) δ := by
  obtain ⟨hopt, _⟩ := h.inner_certificate hX hconv hL hfband hreg hk
  refine ⟨hopt.2.1, ?_⟩
  rw [h.target_update k hk]
  rcases hs with ⟨hr, hgap⟩ | htarget
  · rw [nextTarget, ite_eq_right hr, ite_eq_right (not_lt.mpr hgap)]
    intro a
    have hres : θ * ε₀ ≤ ‖residual f c (D.target k) (D.point (k + 1))‖ := by
      have hh : ¬‖residual f c (D.target k) (D.point (k + 1))‖ ≤ θ * ε₀ := by
        simpa only [ResetGuard, ite_true] using hr
      exact (lt_of_not_ge hh).le
    have hβres : β * (θ * ε₀) ≤ ‖residual f c (D.target k) (D.point (k + 1))‖ :=
      (mul_le_of_le_one_left (mul_pos h.theta_pos h.primal_pos).le h.margin_lt_one.le).trans hres
    apply (hopt.2.2 a).trans
    have hh := mul_le_mul_of_nonneg_right hβres
      (show 0 ≤ ε a *
        completedRadius (targetMerit f c (D.target k)) X P
          (completedInnerAccuracy β θ ε₀ ε) (D.inner k) (D.length k) L a ^ modelOrder a /
            (modelOrder a).factorial by
        have := h.dual_pos a
        have := (hopt.2.1 a).1
        positivity)
    simp only [completedInnerAccuracy]
    convert hh using 1 <;> ring
  · exact htarget

/-- A zero-gap actual return lies strictly outside the reset residual guard;
its constraint norm is therefore strictly greater than the feasibility threshold. -/
theorem zero_gap_constraint_gt (h : CompletedRun f c X P β θ ε₀ L ε D N)
    {k : ℕ} (hk : k < N)
    (hgap : f (D.point (k + 1)) - D.target (k + 1) = 0) :
    θ * ε₀ < ‖c (D.point (k + 1))‖ := by
  have hupdate := h.target_update k hk
  by_cases hr : ResetGuard true f c ε₀ θ (D.target k) (D.point (k + 1))
  · have hcn : ‖c (D.point (k + 1))‖ < ε₀ :=
      (constraint_norm_le_residual f c (D.target k) (D.point (k + 1))).trans_lt
        (hr.le.trans_lt (mul_lt_of_lt_one_left h.primal_pos h.theta_lt_one))
    have hs : 0 < ε₀ ^ 2 - ‖c (D.point (k + 1))‖ ^ 2 := by
      nlinarith [h.primal_pos, norm_nonneg (c (D.point (k + 1)))]
    rw [hupdate, nextTarget, ite_eq_left hr, resetTarget, sub_sub_cancel] at hgap
    exact False.elim ((Real.sqrt_pos.mpr hs).ne' hgap)
  · by_cases hover : f (D.point (k + 1)) < D.target k
    · rw [hupdate, nextTarget, ite_eq_right hr, ite_eq_left hover] at hgap
      exact False.elim ((reflect_gap_pos hover).ne' hgap)
    · rw [nextTarget, ite_eq_right hr, ite_eq_right hover] at hupdate
      have hres : θ * ε₀ < ‖residual f c (D.target k) (D.point (k + 1))‖ := by
        simpa only [ResetGuard, ite_true, not_le] using hr
      have hg : f (D.point (k + 1)) - D.target k = 0 := by rwa [hupdate] at hgap
      simpa only [residual_norm, hg, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero,
        Real.sqrt_sq (norm_nonneg _)] using hres

/-- Actual stopping outputs have feasibility, legal extracted radii, a true
normalized merit certificate and the strict zero-gap infeasibility alternative. -/
theorem return_certificate (h : CompletedRun f c X P β θ ε₀ L ε D N)
    (hX : IsClosed X) (hconv : Convex ℝ X) (hL : 1 ≤ L) {flow fup : ℝ}
    (hfband : ∀ z ∈ X, ‖c z‖ ≤ 1 → flow ≤ f z ∧ f z ≤ fup)
    (hreg : ∀ t ∈ Icc (flow - 1) fup, ContDiff ℝ p (targetMerit f c t) ∧
      ∀ i, 1 ≤ i → i ≤ p → ∀ y z,
        ‖iteratedFDeriv ℝ i (targetMerit f c t) y -
          iteratedFDeriv ℝ i (targetMerit f c t) z‖ ≤ L * ‖y - z‖)
    {k : ℕ} (hk : k < N) (hs : CompletedStopAfter f c X P β θ ε₀ L ε D k) :
    let δ := completedRadius (targetMerit f c (D.target k)) X P
      (completedInnerAccuracy β θ ε₀ ε) (D.inner k) (D.length k) L
    D.point (k + 1) ∈ X ∧ (∀ a, 0 < δ a ∧ δ a ≤ 1) ∧
      0 ≤ f (D.point (k + 1)) - D.target (k + 1) ∧
      ‖residual f c (D.target (k + 1)) (D.point (k + 1))‖ ≤ ε₀ ∧
      CompletedMeritTarget f c X ε (D.target (k + 1)) (D.point (k + 1)) δ ∧
      (f (D.point (k + 1)) - D.target (k + 1) = 0 → θ * ε₀ < ‖c (D.point (k + 1))‖) := by
  obtain ⟨hlegal, htarget⟩ := h.target_of_stop hX hconv hL hfband hreg hk hs
  have hi := h.invariants (show k + 1 ≤ N by omega)
  exact ⟨h.mem (by omega), hlegal, hi.1, hi.2, htarget, h.zero_gap_constraint_gt hk⟩

end Constrained.TwoPhase.CompletedRun
