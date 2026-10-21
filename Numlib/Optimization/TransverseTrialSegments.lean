import Numlib.Optimization.TransverseRefinementBlocks
import Numlib.Optimization.TransverseQualifiedPaths

/-!
# Concrete qualified transverse trial segments

Each phase constructs its own completed failed inspection and actual returned inner call.
The least accurate request index gives all forced refinement edges, followed by one fresh
accepted trial. No assumption on the incoming cache or freshness is imposed on a segment.
-/

noncomputable section
namespace Optimization.TransverseTrialSegments
open TransverseObjective InexactTaylorModels ExplicitRegularization
open TransverseRegularizationContinuation TransverseRefinementBlocks
open TransverseQualifiedContinuation

/-- The actual accepted endpoint keeps every scaled derivative request, sets unit radii
and parameter two, and stores the precise fresh value request at its new point. -/
theorem refinementEndpoint_effects (a : State Plane) (n : ℕ) (s : Plane) :
    (refinementEndpoint a n s).point = a.point + s ∧
    (refinementEndpoint a n s).sigma = 2 ∧
    (refinementEndpoint a n s).radii = (fun _ => 1) ∧
    (refinementEndpoint a n s).request = (fun i => (1 / 2 : ℝ) ^ n * a.request i) ∧
    (refinementEndpoint a n s).fresh = true ∧
    (refinementEndpoint a n s).valueCache = some ((1 / 32 : ℝ) *
      decrement (exactOracle.derivative a.point a.request) 2 s / 2) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Positive prediction makes the actual endpoint's stored fresh value request positive. -/
theorem refinementEndpoint_cache_pos (a : State Plane) (n : ℕ) (s : Plane)
    (hp : 0 < decrement (exactOracle.derivative a.point a.request) 2 s) :
    ∃ request, 0 < request ∧ (refinementEndpoint a n s).valueCache = some request := by
  refine ⟨_, ?_, (refinementEndpoint_effects a n s).2.2.2.2.2⟩
  positivity

/-- The actual accepted endpoint preserves the full continuation invariant whenever the
prescribed endpoint has the continuation geometry and strict gradient cap. -/
theorem invariant_refinementEndpoint (a : State Plane) (ha : Invariant a) (n : ℕ) (s : Plane)
    (hx0 : 0 ≤ (a.point + s) 0) (hx1 : (a.point + s) 0 ≤ 1)
    (hy : 1 ≤ (a.point + s) 1) (hg : ‖fderiv ℝ objective (a.point + s)‖ < 1) :
    Invariant (refinementEndpoint a n s) := by
  refine ⟨hx0, hx1, hy, hg, rfl, rfl, ?_⟩
  intro i
  exact mul_pos (by positivity) (ha.2.2.2.2.2.2 i)

/-- The chosen actual prelude minimum stays on the axis, advances the tail coordinate,
and preserves a strict true-gradient cap. -/
theorem prelude_endpoint_geometry {b : ℝ} (hb : 1 ≤ b) :
    0 ≤ (point 0 b + TransversePrelude.step b) 0 ∧
    (point 0 b + TransversePrelude.step b) 0 ≤ 1 ∧
    1 ≤ (point 0 b + TransversePrelude.step b) 1 ∧
    ‖fderiv ℝ objective (point 0 b + TransversePrelude.step b)‖ < 1 := by
  have he : point 0 b + TransversePrelude.step b =
      point 0 (b + TransversePrelude.step b 1) := by
    rw [TransversePrelude.step_eq_point]
    simp
  have hb' : 1 ≤ b + TransversePrelude.step b 1 := by
    linarith [TransversePrelude.step_one_coord_pos hb]
  rw [he, TransverseInjection.initial_slope_eq]
  exact ⟨by norm_num, by norm_num, hb',
    (TransversePrelude.slope_le_half hb').trans_lt (by norm_num)⟩

private theorem exists_segment {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (a : State Plane) (ha : Invariant a)
    (I : Inspection (parameters ε hε hε1) exactOracle.derivative a)
    (ho : I.order = 1)
    (R : InexactRegularization.InnerResult (parameters ε hε hε1).toImplicitParameters 0
      (exactOracle.derivative a.point a.request) a.sigma I.radii
        (I.direction (by change I.order ≤ 1; omega)))
    (hr : R.radii = fun _ => 1) (hz : R.step ≠ 0) (hs : ‖R.step‖ < 1)
    (hp : 0 < decrement (exactOracle.derivative a.point a.request) 2 R.step)
    (hρ : 1 ≤ HigherOrderRegularization.ratio objective 2 a.point R.step)
    (hmu : (R.execution.state 0).mu = ‖fderiv ℝ objective a.point‖ ^ 2 / 100)
    (hx0 : 0 ≤ (a.point + R.step) 0) (hx1 : (a.point + R.step) 0 ≤ 1)
    (hy : 1 ≤ (a.point + R.step) 1)
    (hg : ‖fderiv ℝ objective (a.point + R.step)‖ < 1) :
    ∃ p : QualifiedPath hε hε1,
      (p.path.node 0).state = a ∧
      (p.path.node p.path.length).state.point = a.point + R.step ∧
      0 < p.path.length ∧ p.path.functionQueries.length = 2 ∧
      (∃ n, (p.path.node p.path.length).state = refinementEndpoint a n R.step) ∧
      ∀ k, k < p.path.length → (p.path.node k).inspection.order = 1 := by
  obtain ⟨n, hacc, hbefore⟩ := exists_least_refinement hε hε1 a
    (ha.2.2.2.2.2.2 1) R.step hz hs
  have hend := invariant_refinementEndpoint a ha n R.step hx0 hx1 hy hg
  obtain ⟨J⟩ := exists_inspection hε hε1 (refinementEndpoint a n R.step) hend
  have hq : I.order ≤ 1 := by omega
  let p := refinementTrialPath hε hε1 a ha.2.2.2.2.1 I hq R hr hz hp hρ n hbefore hacc J
  have hpInv : ∀ k, k ≤ p.length → Invariant (p.node k).state := by
    intro k hk
    by_cases hkn : k ≤ n
    · rw [refinementTrialPath_node_before hε hε1 a ha.2.2.2.2.1 I hq R hr hz hp hρ
        n hbefore hacc J hkn]
      exact invariant_refinedState a ha k
    · have he : k = p.length := by change k ≤ n + 1 at hk; change k = n + 1; omega
      rw [he, refinementTrialPath_node_end]
      exact hend
  let q : QualifiedPath hε hε1 := ⟨p,
    refinementTrialPath_branch hε hε1 a ha.2.2.2.2.1 I hq R hr hz hp hρ
      n hbefore hacc J hmu, hpInv⟩
  refine ⟨q, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (p.node 0).state = a
    rw [refinementTrialPath_node_zero]
  · change (p.node p.length).state.point = a.point + R.step
    rw [refinementTrialPath_node_end]
    rfl
  · change 0 < n + 1
    omega
  · exact refinementTrialPath_functionQueries_length hε hε1 a ha.2.2.2.2.1 I hq R hr hz
      hp hρ n hbefore hacc J
  · refine ⟨n, ?_⟩
    change (p.node p.length).state = refinementEndpoint a n R.step
    rw [refinementTrialPath_node_end]
  · intro k hk
    have hkn : k ≤ n := by change k < n + 1 at hk; omega
    change (p.node k).inspection.order = 1
    rw [refinementTrialPath_node_before hε hε1 a ha.2.2.2.2.1 I hq R hr hz hp hρ
      n hbefore hacc J hkn]
    exact ho

/-- Before the slope crossing, the incoming invariant and actual point determine a
qualified prelude segment. The completed failed search, actual inner return and finite
least request refinement are constructed; the two actual value queries are derived. -/
theorem exists_prelude_segment {ε b : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hb : 1 ≤ b) (hg : 2 * ε / 5 < TransversePrelude.slope b)
    (a : State Plane) (ha : Invariant a) (hpoint : a.point = point 0 b) :
    ∃ p : QualifiedPath hε hε1,
      (p.path.node 0).state = a ∧
      (p.path.node p.path.length).state.point = a.point + TransversePrelude.step b ∧
      0 < p.path.length ∧ p.path.functionQueries.length = 2 ∧
      (∃ n, (p.path.node p.path.length).state =
        refinementEndpoint a n (TransversePrelude.step b)) ∧
      ∀ k, k < p.path.length → (p.path.node k).inspection.order = 1 := by
  have hδ : a.radii 1 ∈ Set.Ioc (0 : ℝ) 1 := by rw [ha.2.2.2.2.2.1]; norm_num
  obtain ⟨I, ho, _hd⟩ := exists_prelude_inspection hε hε1 hb hg a hpoint hδ
  have hq : I.order ≤ 1 := by omega
  obtain ⟨R, hstep, _hlen, hr, hinit⟩ :=
    prelude_innerResult hε hε1 hb a hpoint ha.2.2.2.2.1 I hq
  have hz : R.step ≠ 0 := hstep ▸ prelude_step_ne_zero hb
  have hs : ‖R.step‖ < 1 := hstep ▸ TransversePrelude.norm_step_lt_one hb
  have hp : 0 < decrement (exactOracle.derivative a.point a.request) 2 R.step := by
    apply prediction_pos_of_model_le hz
    rw [hstep, hpoint]
    exact TransversePrelude.step_minimizes b 0
  have hρ : 1 ≤ HigherOrderRegularization.ratio objective 2 a.point R.step := by
    rw [hstep, hpoint]
    exact TransversePrelude.step_ratio_ge_one hb
  have hmu := congrArg HigherOrderApproximateRegularization.InnerState.mu hinit
  obtain ⟨hx0, hx1, hy, hgrad⟩ := prelude_endpoint_geometry hb
  rw [← hpoint, ← hstep] at hx0 hx1 hy hgrad
  simpa only [hstep] using exists_segment hε hε1 a ha I ho R hr hz hs hp hρ hmu
    hx0 hx1 hy hgrad

/-- An admissible injection constructs its actual skew failed search and actual returned
inner execution, performs exactly the forced request refinements and accepts a fresh trial.
Every edge retains its actual return and every node satisfies the full invariant. -/
theorem exists_injection_segment {ε b : ℝ} (h : TransverseInjection.Conditions ε b)
    (hε1 : ε < 1) (a : State Plane) (ha : Invariant a)
    (hpoint : a.point = point 0 b) :
    ∃ p : QualifiedPath h.tolerance_pos hε1,
      (p.path.node 0).state = a ∧
      (p.path.node p.path.length).state.point = a.point + TransverseInjection.step ε ∧
      0 < p.path.length ∧ p.path.functionQueries.length = 2 ∧
      (∃ n, (p.path.node p.path.length).state =
        refinementEndpoint a n (TransverseInjection.step ε)) ∧
      ∀ k, k < p.path.length → (p.path.node k).inspection.order = 1 := by
  have hδ : a.radii 1 ∈ Set.Ioc (0 : ℝ) 1 := by rw [ha.2.2.2.2.2.1]; norm_num
  obtain ⟨I, ho, hd⟩ := exists_injection_inspection h hε1 a hpoint hδ
  obtain ⟨R, hstep, _hlen, hr, hinit⟩ :=
    injection_innerResult h hε1 a hpoint ha.2.2.2.2.1 I ho hd
  have hz : R.step ≠ 0 := by
    rw [hstep]
    intro he
    have hh := congrArg (fun s : Plane => s 1) he
    simp only [TransverseInjection.step_one, PiLp.zero_apply] at hh
    linarith [h.tolerance_pos]
  have hs : ‖R.step‖ < 1 := hstep ▸ TransverseInjection.norm_step_lt_one h
  have hp : 0 < decrement (exactOracle.derivative a.point a.request) 2 R.step := by
    rw [hstep, hpoint, show exactOracle.derivative (point 0 b) a.request =
      (fun i => iteratedFDeriv ℝ i objective (point 0 b)) from rfl,
      decrement_iteratedFDeriv]
    exact TransverseInjection.taylor_prediction_pos h
  have hρ : 1 ≤ HigherOrderRegularization.ratio objective 2 a.point R.step := by
    rw [hstep, hpoint]
    exact TransverseInjection.ratio_ge_one h
  have hmu := congrArg HigherOrderApproximateRegularization.InnerState.mu hinit
  have hx := TransverseInjection.endpoint_geometry h
  have he : a.point + R.step = point (2 * ε / 3) (b + 4 * ε) := by
    rw [hstep, hpoint, TransverseInjection.step, point_add]
    simp
  have hx0 : 0 ≤ (a.point + R.step) 0 := by simpa only [he, point_zero_coord] using hx.1
  have hx1 : (a.point + R.step) 0 ≤ 1 := by simpa only [he, point_zero_coord] using hx.2.1
  have hy : 1 ≤ (a.point + R.step) 1 := by rw [he, point_one_coord]; linarith [h.tail, hx.2.2]
  have hgrad : ‖fderiv ℝ objective (a.point + R.step)‖ < 1 := by
    rw [hstep, hpoint]
    exact (TransverseInjection.endpoint_slope_bounds h).2.trans hε1
  simpa only [hstep] using exists_segment h.tolerance_pos hε1 a ha I ho R hr hz hs hp hρ
    hmu hx0 hx1 hy hgrad

/-- An admissible tail point constructs its complete transverse failed inspection and
actual return, chooses the finite least accurate request index, and accepts a fresh trial.
The resulting exact query log contains two values and its endpoint carries the actual cache. -/
theorem exists_tail_segment {ε b : ℝ} (h : TransverseTailTrial.Conditions ε b)
    (hε1 : ε < 1) (a : State Plane) (ha : Invariant a)
    (hpoint : a.point = point (2 * ε / 3) b) :
    ∃ p : QualifiedPath h.epsilon_pos hε1,
      (p.path.node 0).state = a ∧
      (p.path.node p.path.length).state.point = a.point + TransverseTailTrial.step ε ∧
      0 < p.path.length ∧ p.path.functionQueries.length = 2 ∧
      (∃ n, (p.path.node p.path.length).state =
        refinementEndpoint a n (TransverseTailTrial.step ε)) ∧
      ∀ k, k < p.path.length → (p.path.node k).inspection.order = 1 := by
  have hδ : a.radii 1 ∈ Set.Ioc (0 : ℝ) 1 := by rw [ha.2.2.2.2.2.1]; norm_num
  obtain ⟨I, ho, hd⟩ := exists_tail_inspection h hε1 a hpoint hδ
  obtain ⟨R, hstep, _hlen, hr, hinit⟩ :=
    tail_innerResult h hε1 a hpoint ha.2.2.2.2.1 I ho hd
  have hz : R.step ≠ 0 := hstep ▸ TransverseTailTrial.step_ne_zero h.epsilon_pos
  have hs : ‖R.step‖ < 1 := hstep ▸ TransverseTailTrial.norm_step_lt_one h
  have hp : 0 < decrement (exactOracle.derivative a.point a.request) 2 R.step := by
    rw [hstep, hpoint, show exactOracle.derivative (point (2 * ε / 3) b) a.request =
      (fun i => iteratedFDeriv ℝ i objective (point (2 * ε / 3) b)) from rfl,
      decrement_iteratedFDeriv]
    exact TransverseTailTrial.prediction_pos h
  have hρ : 1 ≤ HigherOrderRegularization.ratio objective 2 a.point R.step := by
    rw [hstep, hpoint]
    exact TransverseTailTrial.ratio_ge_one h
  have hmu := congrArg HigherOrderApproximateRegularization.InnerState.mu hinit
  have he := TransverseTailTrial.endpoint h
  have hge : 0 ≤ 2 * ε / 3 := by linarith [h.epsilon_pos]
  have hle : 2 * ε / 3 ≤ 1 := (le_abs_self _).trans he.2.1
  have hx0 : 0 ≤ (a.point + R.step) 0 := by rw [hstep, hpoint, he.1, point_zero_coord]; exact hge
  have hx1 : (a.point + R.step) 0 ≤ 1 := by rw [hstep, hpoint, he.1, point_zero_coord]; exact hle
  have hy : 1 ≤ (a.point + R.step) 1 := by rw [hstep, hpoint, he.1, point_one_coord]; exact he.2.2.1
  have hgrad : ‖fderiv ℝ objective (a.point + R.step)‖ < 1 := by
    rw [hstep, hpoint]
    exact (TransverseTailTrial.endpoint_norm_fderiv_bounds h).2.trans hε1
  simpa only [hstep] using exists_segment h.epsilon_pos hε1 a ha I ho R hr hz hs hp hρ
    hmu hx0 hx1 hy hgrad

end Optimization.TransverseTrialSegments
