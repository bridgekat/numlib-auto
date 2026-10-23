import Numlib.Optimization.Sharpness.CurvatureInterpolation
import Numlib.Optimization.Regularization.Cubic.SharpnessFinite
import Numlib.Approximation.Hermite.Global

/-!
# Uniform curvature objectives and complete slow algorithm executions

Actual objective families with fixed smoothness and range bounds give complete
initialized trust-region and cubic-regularization lower bounds. The first-order
plateau supplies the other branch of the two-accuracy cubic lower bound.
-/

namespace CurvatureSharpness

/-- A uniformly regular family of actual objectives interpolates the prescribed
curvature jets. Only function values, derivatives and regularity occur in this interface. -/
def UniformObjectives (L B : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ f : ℝ → ℝ,
    Data f ε ε (horizon ε) ∧ (∀ z, |f z| ≤ B) ∧
    (∀ z, |iteratedDeriv 2 f z| ≤ B) ∧
    ∀ z w, ‖iteratedFDeriv ℝ 2 f z - iteratedFDeriv ℝ 2 f w‖ ≤ L * ‖z - w‖

/-- Global Hermite interpolation produces actual curvature objectives with smoothness
and range bounds fixed before the accuracy or the number of interpolation points. -/
theorem exists_uniform_objectives : ∃ L ≥ 1, ∃ B > 0, UniformObjectives L B := by
  obtain ⟨L, hL, B, hB, H⟩ := Hermite.exists_uniform_interpolant 2 2 (by norm_num)
  refine ⟨max 1 L, le_max_left _ _, B, hB, ?_⟩
  intro ε hε hε1
  obtain ⟨hN, hmono, hstep, hjet, hres⟩ := uniform_Hermite_data hε hε1
  obtain ⟨f, hf, hLip, hjets, hbound⟩ := H (horizon ε) hN (grid ε)
    (jet ε ε (horizon ε)) hmono hres
  have hb := hbound ⟨hjet, hstep⟩
  refine ⟨f, Data.of_jets hf hjets, ?_, fun z => hb 2 le_rfl z, ?_⟩
  · intro z
    simpa only [iteratedDeriv_zero] using hb 0 (by omega) z
  · intro z w
    rw [norm_iteratedFDeriv_sub_eq_norm_iteratedDeriv_sub]
    exact (hLip.norm_sub_le z w).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

/-- A uniform family produces actual slow TR2 executions, with fixed regularity,
Hessian and objective-budget constants before every accuracy request. -/
theorem slow_trustRegionRun_of_uniform_objectives {L B : ℝ}
    (hB : 0 < B) (hu : UniformObjectives L B) :
    ∃ H ≥ 1, ∃ G > 0, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ f : ℝ → ℝ,
        ContDiff ℝ 2 f ∧ (∀ z, -B ≤ f z) ∧ f 0 - (-B) ≤ G ∧
        (∀ z, ‖SecondOrderTrustRegion.hessian f z‖ ≤ H) ∧
        (∀ z w, ‖iteratedFDeriv ℝ 2 f z - iteratedFDeriv ℝ 2 f w‖ ≤ L * ‖z - w‖) ∧
        SecondOrderTrustRegion.Run f (grid ε) (fun _ => ε) (fun _ => 0) (fun _ => ε)
          (fun _ => 1) (curvature ε (horizon ε)) (fun _ => ε) (fun _ => 1)
          (1/4) (1/2) (1/4) (1/2) 2 ε ε (horizon ε) ∧
        (∀ i < horizon ε,
          ¬(‖gradient f (grid ε i)‖ ≤ ε ∧ -ε ≤ curvature ε (horizon ε) i)) ∧
        ‖gradient f (grid ε (horizon ε))‖ ≤ ε ∧
        -ε ≤ curvature ε (horizon ε) (horizon ε) ∧
        1 / ε ^ 3 ≤ (horizon ε : ℝ) ∧
        1 / ε ^ 3 ≤ (SecondOrderTrustRegion.functionEvaluations (horizon ε) : ℝ) ∧
        1 / ε ^ 3 ≤ (SecondOrderTrustRegion.gradientEvaluations
          (fun _ => 1) (1/4) (horizon ε) : ℝ) ∧
        1 / ε ^ 3 ≤ (SecondOrderTrustRegion.hessianEvaluations
          (fun _ => 1) (1/4) (horizon ε) : ℝ) := by
  refine ⟨max 1 B, le_max_left _ _, 2 + B, by linarith, ?_⟩
  intro ε hε hε1
  obtain ⟨f, hf, hb, hhb, hlip⟩ := hu ε hε hε1
  have hrun := hf.trustRegion_run (η₁ := 1/4) (η₂ := 1/2) (γ₁ := 1/4)
    (γ₂ := 1/2) (γ₃ := 2) (ε₁ := ε) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hε hε hε
  have hg := (unit_step_uniform_bounds hε hε1).2.2.1 0 (Nat.zero_le _) 0 (by omega)
  change |value ε ε (horizon ε) 0| ≤ 2 at hg
  have hv := hf.values 0 (Nat.zero_le _)
  simp only [grid, Nat.cast_zero, zero_mul] at hv
  have hc := (Data.initialized_counts (N := horizon ε) (η₁ := 1/4) (by norm_num))
  have hcount := (horizon_bounds hε hε1).2.1
  refine ⟨f, hf.regularity, fun z => (abs_le.mp (hb z)).1, ?_, ?_, hlip, hrun,
    ?_, ?_, ?_, hcount, ?_, ?_, ?_⟩
  · rw [←hv] at hg
    linarith [(abs_le.mp hg).2]
  · intro z
    rw [SecondOrderTrustRegion.norm_hessian, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      Real.norm_eq_abs]
    exact (hhb z).trans (le_max_right _ _)
  · intro i hi hs
    have hm := hs.2
    simp only [curvature, ite_eq_left hi] at hm
    linarith
  · rw [hf.gradient_eq_zero le_rfl, norm_zero]
    exact hε.le
  · simp [curvature, hε.le]
  · rw [hc.1]
    push_cast
    linarith
  · rw [hc.2.1]
    push_cast
    linarith
  · rw [hc.2.2.1]
    push_cast
    linarith

set_option maxHeartbeats 800000 in
-- Elaborating both nested witness packages unfolds the actual execution specifications.
/-- Combining the curvature family and the actual smooth plateau yields the maximum
of the first- and second-accuracy lower bounds, with fixed constants and settings. -/
theorem slow_cubicRun_of_uniform_objectives {L B : ℝ}
    (hB : 0 < B) (hu : UniformObjectives L B) :
    ∃ L' ≥ 1, ∃ G > 0,
      ∀ ε₁ : ℝ, 0 < ε₁ → ε₁ ≤ 1 → ∀ ε₂ : ℝ, 0 < ε₂ → ε₂ ≤ 1 →
      ∃ (f : ℝ → ℝ) (x : ℕ → ℝ) (t : ℝ) (ρ μ : ℕ → ℝ) (N : ℕ),
        x 0 = 0 ∧ ContDiff ℝ 2 f ∧ (∀ z, -B ≤ f z) ∧ f 0 - (-B) ≤ G ∧
        (∀ z w, ‖iteratedFDeriv ℝ 2 f z - iteratedFDeriv ℝ 2 f w‖ ≤
          L' * ‖z - w‖) ∧
        CubicRegularization.FiniteRun f x (fun _ => t) (fun _ => 1) μ
          (fun _ => 4) ρ (1/4) (1/2) (1/2) 2 3 4 1 1 ε₁ ε₂ N ∧
        (∀ i < N, ¬(‖fderiv ℝ f (x i)‖ ≤ ε₁ ∧ -ε₂ ≤ μ i)) ∧
        ‖fderiv ℝ f (x N)‖ ≤ ε₁ ∧ -ε₂ ≤ μ N ∧
        max (1 / ε₁ ^ (3/2 : ℝ)) (1 / ε₂ ^ 3) ≤ (N : ℝ) ∧
        max (1 / ε₁ ^ (3/2 : ℝ)) (1 / ε₂ ^ 3) ≤
          (CubicRegularization.functionEvaluations N : ℝ) ∧
        max (1 / ε₁ ^ (3/2 : ℝ)) (1 / ε₂ ^ 3) ≤
          (CubicRegularization.gradientEvaluations ρ (1/4) N : ℝ) ∧
        max (1 / ε₁ ^ (3/2 : ℝ)) (1 / ε₂ ^ 3) ≤
          (CubicRegularization.hessianEvaluations ρ (1/4) N : ℝ) := by
  obtain ⟨L₁, hL₁, hfirst⟩ := CubicRegularization.exists_slow_finiteRun_first_branch
    (η₁ := 1/4) (η₂ := 1/2) (γ₁ := 1/2) (γ₂ := 2) (γ₃ := 3)
    (θ := 1) (θ₂ := 1) (σ := 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨max L L₁, hL₁.trans (le_max_right _ _), 4 + B, by linarith, ?_⟩
  intro ε₁ hε₁ hε₁1 ε₂ hε₂ hε₂1
  by_cases hdom : 1 / ε₂ ^ 3 ≤ 1 / ε₁ ^ (3/2 : ℝ)
  · obtain ⟨f, x, t, ρ, N, hx0, hf, hlow, hlip, hgap, hN, hrun, hvery,
      hterm, hcurv, hnonterm, hcount, hF, hD, hH⟩ :=
      hfirst ε₁ hε₁ hε₁1 ε₂ hε₂ hε₂1
    norm_num at hgap
    refine ⟨f, x, t, ρ, (fun i => iteratedDeriv 2 f (x i)), N,
      hx0, hf, ?_, ?_, ?_, hrun, hnonterm, hterm.le, ?_, ?_, ?_, ?_, ?_⟩
    · intro z
      linarith [hlow z]
    · rw [hx0] at hgap
      linarith
    · intro z w
      exact (hlip z w).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
    · linarith
    · simpa only [max_eq_left hdom] using hcount
    · simpa only [max_eq_left hdom] using hF
    · simpa only [max_eq_left hdom] using hD
    · simpa only [max_eq_left hdom] using hH
  · have hdom' : 1 / ε₁ ^ (3/2 : ℝ) ≤ 1 / ε₂ ^ 3 := le_of_not_ge hdom
    obtain ⟨f, hf, hb, _hhb, hlip⟩ := hu ε₂ hε₂ hε₂1
    have hrun := hf.cubic_finiteRun
      (η₁ := 1/4) (η₂ := 1/2) (γ₁ := 1/2) (γ₂ := 2) (γ₃ := 3)
      (θ₁ := 1) (θ₂ := 1) (σ := 4) (ε₁ := ε₁)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hε₁ hε₁1 hε₂ hε₂1 hε₂ rfl
    have hg := (unit_step_uniform_bounds hε₂ hε₂1).2.2.1 0 (Nat.zero_le _) 0 (by omega)
    change |value ε₂ ε₂ (horizon ε₂) 0| ≤ 2 at hg
    have hv := hf.values 0 (Nat.zero_le _)
    simp only [grid, Nat.cast_zero, zero_mul] at hv
    have hstop := hf.first_stopping_index hε₂ hε₁.le
    have hc := Data.initialized_counts (N := horizon ε₂) (η₁ := 1/4) (by norm_num)
    have hcount := (horizon_bounds hε₂ hε₂1).2.1
    refine ⟨f, grid ε₂, ε₂, (fun _ => 1), curvature ε₂ (horizon ε₂), horizon ε₂,
      by simp [grid], hf.regularity, fun z => (abs_le.mp (hb z)).1, ?_, ?_, hrun,
      hstop.1, hstop.2.1, hstop.2.2, ?_, ?_, ?_, ?_⟩
    · rw [←hv] at hg
      linarith [(abs_le.mp hg).2]
    · intro z w
      exact (hlip z w).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    · simpa only [max_eq_right hdom'] using hcount
    · rw [hc.2.2.2.1, max_eq_right hdom']
      push_cast
      linarith
    · rw [hc.2.2.2.2.1, max_eq_right hdom']
      push_cast
      linarith
    · rw [hc.2.2.2.2.2, max_eq_right hdom']
      push_cast
      linarith

/-- Uniformly regular actual objectives force the inverse-cube TR2 lower bound.
All objective, Hessian and smoothness constants precede every requested accuracy;
the radius is initialized at that accuracy, as in the source construction. -/
theorem exists_slow_trustRegionRun :
    ∃ L ≥ 1, ∃ B > 0,
    ∃ H ≥ 1, ∃ G > 0, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ f : ℝ → ℝ,
        ContDiff ℝ 2 f ∧ (∀ z, -B ≤ f z) ∧ f 0 - (-B) ≤ G ∧
        (∀ z, ‖SecondOrderTrustRegion.hessian f z‖ ≤ H) ∧
        (∀ z w, ‖iteratedFDeriv ℝ 2 f z - iteratedFDeriv ℝ 2 f w‖ ≤ L * ‖z - w‖) ∧
        SecondOrderTrustRegion.Run f (grid ε) (fun _ => ε) (fun _ => 0) (fun _ => ε)
          (fun _ => 1) (curvature ε (horizon ε)) (fun _ => ε) (fun _ => 1)
          (1/4) (1/2) (1/4) (1/2) 2 ε ε (horizon ε) ∧
        (∀ i < horizon ε,
          ¬(‖gradient f (grid ε i)‖ ≤ ε ∧ -ε ≤ curvature ε (horizon ε) i)) ∧
        ‖gradient f (grid ε (horizon ε))‖ ≤ ε ∧
        -ε ≤ curvature ε (horizon ε) (horizon ε) ∧
        1 / ε ^ 3 ≤ (horizon ε : ℝ) ∧
        1 / ε ^ 3 ≤ (SecondOrderTrustRegion.functionEvaluations (horizon ε) : ℝ) ∧
        1 / ε ^ 3 ≤ (SecondOrderTrustRegion.gradientEvaluations
          (fun _ => 1) (1/4) (horizon ε) : ℝ) ∧
        1 / ε ^ 3 ≤ (SecondOrderTrustRegion.hessianEvaluations
          (fun _ => 1) (1/4) (horizon ε) : ℝ) := by
  obtain ⟨L, hL, B, hB, hu⟩ := exists_uniform_objectives
  obtain ⟨H, hH, G, hG, hslow⟩ := slow_trustRegionRun_of_uniform_objectives hB hu
  exact ⟨L, hL, B, hB, H, hH, G, hG, hslow⟩

/-- Uniformly regular actual objectives force the maximum of both accuracy
lower bounds for genuine finite-second-order AR2. The initialization and all algorithm
settings are fixed, while each initialized evaluation counter meets the same lower bound. -/
theorem exists_slow_cubicRun :
    ∃ B > 0,
    ∃ L' ≥ 1, ∃ G > 0,
      ∀ ε₁ : ℝ, 0 < ε₁ → ε₁ ≤ 1 → ∀ ε₂ : ℝ, 0 < ε₂ → ε₂ ≤ 1 →
      ∃ (f : ℝ → ℝ) (x : ℕ → ℝ) (t : ℝ) (ρ μ : ℕ → ℝ) (N : ℕ),
        x 0 = 0 ∧ ContDiff ℝ 2 f ∧ (∀ z, -B ≤ f z) ∧ f 0 - (-B) ≤ G ∧
        (∀ z w, ‖iteratedFDeriv ℝ 2 f z - iteratedFDeriv ℝ 2 f w‖ ≤
          L' * ‖z - w‖) ∧
        CubicRegularization.FiniteRun f x (fun _ => t) (fun _ => 1) μ
          (fun _ => 4) ρ (1/4) (1/2) (1/2) 2 3 4 1 1 ε₁ ε₂ N ∧
        (∀ i < N, ¬(‖fderiv ℝ f (x i)‖ ≤ ε₁ ∧ -ε₂ ≤ μ i)) ∧
        ‖fderiv ℝ f (x N)‖ ≤ ε₁ ∧ -ε₂ ≤ μ N ∧
        max (1 / ε₁ ^ (3/2 : ℝ)) (1 / ε₂ ^ 3) ≤ (N : ℝ) ∧
        max (1 / ε₁ ^ (3/2 : ℝ)) (1 / ε₂ ^ 3) ≤
          (CubicRegularization.functionEvaluations N : ℝ) ∧
        max (1 / ε₁ ^ (3/2 : ℝ)) (1 / ε₂ ^ 3) ≤
          (CubicRegularization.gradientEvaluations ρ (1/4) N : ℝ) ∧
        max (1 / ε₁ ^ (3/2 : ℝ)) (1 / ε₂ ^ 3) ≤
          (CubicRegularization.hessianEvaluations ρ (1/4) N : ℝ) := by
  obtain ⟨L, _hL, B, hB, hu⟩ := exists_uniform_objectives
  obtain ⟨L', hL', G, hG, hslow⟩ := slow_cubicRun_of_uniform_objectives hB hu
  exact ⟨B, hB, L', hL', G, hG, hslow⟩

end CurvatureSharpness
