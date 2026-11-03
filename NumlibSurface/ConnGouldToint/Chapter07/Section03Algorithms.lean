import NumlibSurface.ConnGouldToint.Chapter07.Section03

/-!
# Separate safeguards and the eigenvalue-based method

Algorithms 7.3.2, 7.3.3 and 7.3.6 of [conn2000trust].
-/

namespace ConnGouldToint.Chapter07

open Subproblem Set Filter
open scoped Topology RealInnerProductSpace

section Safeguards

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Algorithm 7.3.2 with midpoint trials in its unspecified bracket choices.
The pair contains the possibly strengthened lower endpoint and the trial.
A zero gradient goes directly to the bracket choice, since the Newton
formula would divide by the norm of a zero solve. -/
noncomputable def algorithm_7_3_2 (g : E) (H : E →L[ℝ] E)
    (pole Δ lo hi x : ℝ) : ℝ × ℝ :=
  if pole < x ∧ ‖g‖ ≠ 0 then
    let candidate := moreSorensenNewtonStep g H Δ x
    if Δ ≤ ‖shiftedStep g H x‖ ∨ pole < candidate then (lo, candidate)
    else let lo' := max lo candidate; (lo', (lo' + hi) / 2)
  else (lo, (lo + hi) / 2)

/-- A Newton candidate at or below the pole can tighten the lower endpoint.
The next trial is strictly inside the resulting interval. -/
theorem algorithm_7_3_2_failed_newton {g : E} {H : E →L[ℝ] E} {pole Δ lo hi x : ℝ}
    (hx : pole < x) (hg : g ≠ 0) (hG : ‖shiftedStep g H x‖ < Δ)
    (hN : moreSorensenNewtonStep g H Δ x ≤ pole) (hlh : lo < hi) (hph : pole < hi) :
    let state := algorithm_7_3_2 g H pole Δ lo hi x
    state.1 = max lo (moreSorensenNewtonStep g H Δ x) ∧ state.2 ∈ Ioo state.1 hi := by
  have hc := max_lt hlh (hN.trans_lt hph)
  have hf : pole < x ∧ ‖g‖ ≠ 0 := ⟨hx, norm_ne_zero_iff.mpr hg⟩
  simp only [algorithm_7_3_2, ite_eq_left hf, not_le.mpr hG, not_lt.mpr hN,
    false_or, ite_false, mem_Ioo, true_and]
  exact ⟨by linarith, by linarith⟩

/-- Algorithm 7.3.3 updates the upper endpoint on the positive-definite
short-step branch and updates the lower endpoint in the other cases. -/
noncomputable def algorithm_7_3_3 (g : E) (H : E →L[ℝ] E)
    (pole Δ lo hi x : ℝ) : ℝ × ℝ :=
  if pole < x ∧ ‖shiftedStep g H x‖ < Δ then (lo, x) else (x, hi)

/-- The bracket update preserves the target when the trial is classified on
the correct side of it, as provided by the secular comparison. -/
theorem algorithm_7_3_3_preserves_bracket {g : E} {H : E →L[ℝ] E}
    {pole Δ lo hi x r : ℝ} (hr : r ∈ Icc lo hi)
    (hG : (pole < x ∧ ‖shiftedStep g H x‖ < Δ) → r ≤ x)
    (hother : ¬(pole < x ∧ ‖shiftedStep g H x‖ < Δ) → x ≤ r) :
    let state := algorithm_7_3_3 g H pole Δ lo hi x
    r ∈ Icc state.1 state.2 := by
  unfold algorithm_7_3_3
  split
  · rename_i h
    exact ⟨hr.1, hG h⟩
  · rename_i h
    exact ⟨hother h, hr.2⟩

end Safeguards

section Eigensolution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {g : E} {H : E →L[ℝ] E} {hH : (H : E →ₗ[ℝ] E).IsSymmetric}

/-- The classification in Algorithm 7.3.3 retains the optimal multiplier
for every nonnegative trial, including a feasible unshifted trial. -/
theorem algorithm_7_3_3_preserves_multiplier {Δ r lo hi x : ℝ}
    (hΔ : 0 < Δ) (hx : 0 ≤ x) {sM : E} (hsM : ‖sM‖ ≤ Δ)
    (hmul : IsTrustRegionMultiplier g H Δ sM r) (hr : r ∈ Icc lo hi) :
    let state := algorithm_7_3_3 g H (-leftmost hH) Δ lo hi x
    r ∈ Icc state.1 state.2 := by
  have hle : -leftmost hH ≤ r := neg_leftmost_le_shiftThreshold.trans
    (shiftThreshold_le_of_isTrustRegionMultiplier (hH := hH) hmul).1
  apply algorithm_7_3_3_preserves_bracket hr
  · rintro ⟨hp, hn⟩
    rcases hx.eq_or_lt with hz | hx'
    · subst x
      have hm : IsTrustRegionMultiplier g H Δ (shiftedStep g H 0) 0 :=
        ⟨le_rfl, (step_spec hp).1, isPositive_add_smul_of_le hp.le, zero_mul _⟩
      exact (hmul.unique hH hΔ hsM hm hn.le).le
    · have ht : shiftThreshold hH < x := max_lt hx' hp
      have hh := (le_secular_iff_of_trustRegion (hH := hH) hΔ hmul hsM ht).not
      exact (lt_of_not_ge (hh.mp (not_le.mpr
        (pow_lt_pow_left₀ hn (norm_nonneg _) two_ne_zero)))).le
  · intro hn
    rcases hx.eq_or_lt with hz | hx'
    · simpa [← hz] using hmul.nonneg
    · by_cases hp : -leftmost hH < x
      · have ht : shiftThreshold hH < x := max_lt hx' hp
        have hn' : Δ ≤ ‖shiftedStep g H x‖ := le_of_not_gt fun h => hn ⟨hp, h⟩
        exact (le_secular_iff_of_trustRegion (hH := hH) hΔ hmul hsM ht).mp
          (pow_le_pow_left₀ hΔ.le hn' 2)
      · exact (le_of_not_gt hp).trans hle

/-- Corrected terminal branch of Algorithm 7.3.6. Test compatibility and
feasibility at the exact threshold. A positive perturbation of the shift
can shorten the raw step, so feasibility there is not an exact hard-case test.
At positive threshold a unit kernel vector supplies the boundary correction. -/
theorem algorithm_7_3_6_exact_threshold {Δ : ℝ}
    (hg : g ∈ (LinearMap.ker ((H + shiftThreshold hH • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ)
    (hs : ‖particular hH g (shiftThreshold hH)‖ ≤ Δ) {u : E}
    (hu : 0 < shiftThreshold hH → ‖u‖ = 1 ∧
      u ∈ LinearMap.ker ((H + shiftThreshold hH • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E)) :
    let μ := shiftThreshold hH
    let p := particular hH g μ
    let s := if μ = 0 then p else p + moreSorensenBoundaryCoefficient Δ p u • u
    s ∈ Metric.closedBall 0 Δ ∧ IsMinOn (quadModel g H) (Metric.closedBall 0 Δ) s := by
  let μ := shiftThreshold hH
  let p := particular hH g μ
  have hμ : 0 ≤ μ := shiftThreshold_nonneg
  have hpole : -leftmost hH ≤ μ := neg_leftmost_le_shiftThreshold
  change (if μ = 0 then p else p + moreSorensenBoundaryCoefficient Δ p u • u) ∈
    Metric.closedBall 0 Δ ∧ IsMinOn (quadModel g H) (Metric.closedBall 0 Δ)
      (if μ = 0 then p else p + moreSorensenBoundaryCoefficient Δ p u • u)
  by_cases hz : μ = 0
  · rw [ite_eq_left hz]
    simpa only [add_zero] using isMinOn_closedBall_of_hardCase (hH := hH)
      hμ hpole hg (w := (0 : E)) (Submodule.zero_mem _) (by simpa only [add_zero] using hs)
      (Or.inl hz)
  · rw [ite_eq_right hz]
    obtain ⟨hun, huk⟩ := hu (lt_of_le_of_ne hμ (Ne.symm hz))
    have hb := norm_add_boundaryCorrection hs hun
    exact isMinOn_closedBall_of_hardCase (hH := hH) hμ hpole hg
      (Submodule.smul_mem _ _ huk) hb.le (Or.inr hb)

/-- Algorithm 7.3.6 reaches its relative-radius stopping test in finitely
many Newton iterations from an easy-case starting trial. -/
theorem algorithm_7_3_6_easy_stop (hg : g ≠ 0) {Δ r x₀ κ : ℝ} (hΔ : 0 < Δ)
    (hr : -leftmost hH < r) (hr₀ : 0 ≤ r) (hroot : secular g H r = Δ ^ 2)
    (hx₀ : -leftmost hH < x₀) (hbelow : phi g H Δ x₀ < 0) (hκ : 0 < κ) :
    let x := fun k : ℕ => (moreSorensenNewtonStep g H Δ)^[k] x₀
    ∃ k, |‖shiftedStep g H (x k)‖ - Δ| ≤ κ * Δ := by
  let x := fun k : ℕ => (moreSorensenNewtonStep g H Δ)^[k] x₀
  have h := (moreSorensen_easy_newton_convergence hg hΔ hr hr₀ hroot hx₀ hbelow).2.1
  have hnorm : ‖shiftedStep g H r‖ = Δ := by
    change ‖shiftedStep g H r‖ ^ 2 = Δ ^ 2 at hroot
    nlinarith [norm_nonneg (shiftedStep g H r)]
  have ht : Tendsto (fun k => ‖shiftedStep g H (x k)‖) atTop (𝓝 Δ) := hnorm ▸ h.norm
  obtain ⟨k, hk⟩ := (ht.eventually (Metric.ball_mem_nhds Δ (mul_pos hκ hΔ))).exists
  exact ⟨k, (by simpa [Metric.mem_ball, Real.dist_eq] using hk : _ < _).le⟩

/-- A feasible step at a strictly perturbed shift does not imply that
the exact threshold system is compatible, however small the perturbation. -/
theorem algorithm_7_3_6_perturbation_counterexample {ε : ℝ} (hε : 0 < ε) :
    let H : ℝ →L[ℝ] ℝ := -(1 : ℝ →L[ℝ] ℝ)
    let g : ℝ := ε / 2
    let s : ℝ := -(1 / 2)
    (H + (1 + ε) • (1 : ℝ →L[ℝ] ℝ)) s = -g ∧ ‖s‖ < 1 ∧
      ¬ ∃ t : ℝ, (H + 1 • (1 : ℝ →L[ℝ] ℝ)) t = -g := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · simp [smul_eq_mul]
    ring
  · norm_num [Real.norm_eq_abs]
  · rintro ⟨t, ht⟩
    simp at ht
    linarith

/-- After the exact threshold test rules out its terminal branch, the
unshifted trial for a positive definite Hessian, or a sufficiently small
positive perturbation of the pole, starts the easy Newton iteration. -/
theorem algorithm_7_3_6_easy_start (hg : g ≠ 0) {Δ r ε κ : ℝ} (hΔ : 0 < Δ)
    {sM : E} (hsM : ‖sM‖ ≤ Δ) (hmul : IsTrustRegionMultiplier g H Δ sM r)
    (heasy : ¬ (g ∈ (LinearMap.ker ((H + shiftThreshold hH • 1 : E →L[ℝ] E) :
      E →ₗ[ℝ] E))ᗮ ∧ ‖particular hH g (shiftThreshold hH)‖ ≤ Δ))
    (hε : 0 < ε) (hnear : ε < r - shiftThreshold hH) (hκ : 0 < κ) :
    let x₀ := if -leftmost hH < 0 then 0 else -leftmost hH + ε
    let x := fun k : ℕ => (moreSorensenNewtonStep g H Δ)^[k] x₀
    (-leftmost hH < x₀ ∧ phi g H Δ x₀ < 0 ∧
      ∃ k, |‖shiftedStep g H (x k)‖ - Δ| ≤ κ * Δ) := by
  let x₀ := if -leftmost hH < 0 then 0 else -leftmost hH + ε
  have hclass := multiplier_classification_of_trustRegion (hH := hH) hΔ hmul hsM
  have hle := (shiftThreshold_le_of_isTrustRegionMultiplier (hH := hH) hmul).1
  have hr : shiftThreshold hH < r := hle.lt_of_ne (fun h => heasy (hclass.1.mp h.symm))
  have hrp := neg_leftmost_le_shiftThreshold.trans_lt hr
  have hnorm : ‖step g H r‖ = Δ := by
    rw [← hclass.2 hr]
    exact hmul.eq_zero_or_norm_eq.resolve_left (shiftThreshold_nonneg.trans_lt hr).ne'
  have hroot : secular g H r = Δ ^ 2 := by rw [secular, hnorm]
  have hφr : phi g H Δ r = 0 := by
    rw [phi_eq_inv_norm_sub_inv]
    change 1 / ‖step g H r‖ - 1 / Δ = 0
    rw [hnorm, sub_self]
  have hx₀ : -leftmost hH < x₀ ∧ x₀ < r := by
    unfold x₀
    split
    · exact ⟨‹-leftmost hH < 0›, shiftThreshold_nonneg.trans_lt hr⟩
    · exact ⟨lt_add_of_pos_right _ hε, by linarith [neg_leftmost_le_shiftThreshold (hH := hH)]⟩
  have hφ : phi g H Δ x₀ < 0 := hφr ▸
    (trSecular_shape (hH := hH) hg Δ (β := -1 / 2) (by norm_num)).2.1 hx₀.1 hrp hx₀.2
  exact ⟨hx₀.1, hφ, algorithm_7_3_6_easy_stop hg hΔ hrp hmul.nonneg hroot hx₀.1 hφ hκ⟩

/-- The corrected eigenvalue-based algorithm. If the exact threshold test
succeeds, return its exact step. Otherwise use the first Newton trial
satisfying the relative radius test. The optional result accommodates
a proposed perturbation for which no such trial is reached. -/
noncomputable def algorithm_7_3_6 (hH : (H : E →ₗ[ℝ] E).IsSymmetric)
    (g : E) (Δ ε κ : ℝ) (u : E) : Option E := by
  classical
  exact
    let μ := shiftThreshold hH
    let p := particular hH g μ
    if g ∈ (LinearMap.ker ((H + μ • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ ∧ ‖p‖ ≤ Δ then
      some (if μ = 0 then p else p + moreSorensenBoundaryCoefficient Δ p u • u)
    else
      let x₀ := if -leftmost hH < 0 then 0 else -leftmost hH + ε
      let s := fun k : ℕ => shiftedStep g H ((moreSorensenNewtonStep g H Δ)^[k] x₀)
      if h : ∃ k, |‖s k‖ - Δ| ≤ κ * Δ then some (s (Nat.find h)) else none

/-- A successful exact threshold test returns a global model minimizer. -/
theorem algorithm_7_3_6_returns_exact {Δ ε κ : ℝ}
    (hg : g ∈ (LinearMap.ker ((H + shiftThreshold hH • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ)
    (hs : ‖particular hH g (shiftThreshold hH)‖ ≤ Δ) {u : E}
    (hu : 0 < shiftThreshold hH → ‖u‖ = 1 ∧
      u ∈ LinearMap.ker ((H + shiftThreshold hH • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E)) :
    ∃ s, algorithm_7_3_6 hH g Δ ε κ u = some s ∧
      s ∈ Metric.closedBall 0 Δ ∧ IsMinOn (quadModel g H) (Metric.closedBall 0 Δ) s := by
  have htest : g ∈ (LinearMap.ker ((H + shiftThreshold hH • 1 : E →L[ℝ] E) :
      E →ₗ[ℝ] E))ᗮ ∧ ‖particular hH g (shiftThreshold hH)‖ ≤ Δ := ⟨hg, hs⟩
  unfold algorithm_7_3_6
  dsimp only
  rw [ite_eq_left htest]
  exact ⟨_, rfl, algorithm_7_3_6_exact_threshold hg hs hu⟩

/-- With a sufficiently small positive perturbation in the easy case,
the corrected algorithm returns a step satisfying the radius test. -/
theorem algorithm_7_3_6_returns_easy (hg : g ≠ 0) {Δ r ε κ : ℝ} (hΔ : 0 < Δ)
    {sM : E} (hsM : ‖sM‖ ≤ Δ) (hmul : IsTrustRegionMultiplier g H Δ sM r)
    (heasy : ¬ (g ∈ (LinearMap.ker ((H + shiftThreshold hH • 1 : E →L[ℝ] E) :
      E →ₗ[ℝ] E))ᗮ ∧ ‖particular hH g (shiftThreshold hH)‖ ≤ Δ))
    (hε : 0 < ε) (hnear : ε < r - shiftThreshold hH) (hκ : 0 < κ) (u : E) :
    ∃ s, algorithm_7_3_6 hH g Δ ε κ u = some s ∧ |‖s‖ - Δ| ≤ κ * Δ := by
  let x₀ := if -leftmost hH < 0 then 0 else -leftmost hH + ε
  let s := fun k : ℕ => shiftedStep g H ((moreSorensenNewtonStep g H Δ)^[k] x₀)
  have h : ∃ k, |‖s k‖ - Δ| ≤ κ * Δ :=
    (algorithm_7_3_6_easy_start hg hΔ hsM hmul heasy hε hnear hκ).2.2
  unfold algorithm_7_3_6
  dsimp only
  rw [ite_eq_right heasy, dite_eq_left h]
  exact ⟨s (Nat.find h), rfl, Nat.find_spec h⟩

end Eigensolution

end ConnGouldToint.Chapter07
