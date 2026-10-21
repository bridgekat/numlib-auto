import Numlib.Optimization.ExplicitRegularizationPaths
import Numlib.Optimization.TransverseQualifiedContinuation
import Numlib.Optimization.PrescribedFirstOrderInspection
import Numlib.Optimization.TransverseRegularizationContinuation
import Numlib.Optimization.TransverseInjection
import Numlib.Optimization.TransverseTailTrial
import Numlib.Optimization.TransversePrelude

/-!
# Actual inspections and finite request-refinement blocks

The exact oracle permits the same completed inspection and returned short step to be
reused after each forced request halving. The least accurate index supplies finitely many
actual refinement transitions, followed by an accepted fresh two-value trial. Cached
values are carried from the incoming state and replaced by the actual endpoint request.
-/

noncomputable section
namespace Optimization.TransverseRefinementBlocks
open TransverseObjective InexactTaylorModels ExplicitRegularization
open TransverseRegularizationContinuation

/-- A prescribed continuous-radius direction family produces a complete failed inspection
at any positive incoming radius at most one, using the actual exact-oracle coefficients. -/
theorem exists_prescribed_inspection {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (a : State Plane) (hδ : a.radii 1 ∈ Set.Ioc (0 : ℝ) 1) (d : ℝ → Plane)
    (hd : ∀ δ, 0 ≤ δ → InexactRegularization.CoefficientWitness
      (fun i => iteratedFDeriv ℝ i objective a.point) 1 δ (1 / 4) (d δ))
    (hf : ∀ δ, 0 < δ → ε * δ / 8 <
      TaylorCriticality.taylorDecrement objective 1 a.point (d δ)) :
    ∃ I : Inspection (parameters ε hε hε1) exactOracle.derivative a,
      I.order = 1 ∧
      (I.search 1 le_rfl (by norm_num [parameters]) I.order_pos).direction =
        fun k => d (InexactRegularization.halvedRadius (a.radii 1) k) := by
  apply InexactRegularization.exists_failed_firstOrderInspection _ rfl _ _ _ _ hδ
  · intro k
    exact hd _ (InexactRegularization.halvedRadius_pos hδ.1 k).le
  · intro k
    have ht := hf _ (InexactRegularization.halvedRadius_pos hδ.1 k)
    change (1 / 4 : ℝ) * ε * _ / 2 <
      decrement (fun i => iteratedFDeriv ℝ i objective a.point) 1 _
    rw [decrement_iteratedFDeriv]
    convert ht using 1
    ring

/-- The actual skew witnesses produce a failed injection inspection, preserving every
search direction and hence its actual selected terminal radius. -/
theorem exists_injection_inspection {ε b : ℝ} (h : TransverseInjection.Conditions ε b)
    (hε1 : ε < 1) (a : State Plane) (hp : a.point = point 0 b)
    (hδ : a.radii 1 ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ I : Inspection (parameters ε h.tolerance_pos hε1) exactOracle.derivative a,
      I.order = 1 ∧
      (I.search 1 le_rfl (by norm_num [parameters]) I.order_pos).direction =
        fun k => TransverseInjection.direction
          (InexactRegularization.halvedRadius (a.radii 1) k) := by
  apply exists_prescribed_inspection h.tolerance_pos hε1 a hδ TransverseInjection.direction
  · intro δ hδ
    simpa only [hp] using TransverseInjection.direction_coefficientWitness h hδ
  · intro δ hδ
    simpa only [hp] using TransverseInjection.direction_computed_failure h hδ

/-- The actual transverse witnesses produce a failed tail inspection at every admissible
incoming radius, with the whole dyadic direction family retained. -/
theorem exists_tail_inspection {ε b : ℝ} (h : TransverseTailTrial.Conditions ε b)
    (hε1 : ε < 1) (a : State Plane) (hp : a.point = point (2 * ε / 3) b)
    (hδ : a.radii 1 ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ I : Inspection (parameters ε h.epsilon_pos hε1) exactOracle.derivative a,
      I.order = 1 ∧
      (I.search 1 le_rfl (by norm_num [parameters]) I.order_pos).direction =
        fun k => point (-InexactRegularization.halvedRadius (a.radii 1) k) 0 := by
  apply exists_prescribed_inspection h.epsilon_pos hε1 a hδ (fun δ => point (-δ) 0)
  · intro δ hδ
    simpa only [hp] using TransverseTailTrial.transverse_coefficientWitness h hδ
  · intro δ hδ
    simpa only [hp] using TransverseTailTrial.transverse_computed_failure h hδ

/-- The full vertical first-order maximizer is a genuine quarter-fraction coefficient
witness on the prelude axis. -/
theorem prelude_coefficientWitness {b δ : ℝ} (hb : 1 ≤ b) (hδ : 0 ≤ δ) :
    InexactRegularization.CoefficientWitness
      (fun i => iteratedFDeriv ℝ i objective (point 0 b)) 1 δ (1 / 4) (point 0 δ) := by
  have hn : ‖point 0 δ‖ = δ := by
    nlinarith [norm_point_sq 0 δ, norm_nonneg (point 0 δ)]
  refine ⟨hn.le, ?_⟩
  have he : decrement (fun i => iteratedFDeriv ℝ i objective (point 0 b)) 1 =
      TaylorCriticality.taylorDecrement objective 1 (point 0 b) :=
    funext (decrement_iteratedFDeriv _ _ _)
  rw [he, TaylorCriticality.gapOn_taylorDecrement_one _ _ hδ,
    TransverseInjection.initial_slope_eq, taylorDecrement_one_local (by norm_num)]
  simp only [point_zero_coord, point_one_coord, mul_zero, neg_zero, zero_sub]
  have hg := TransversePrelude.slope_pos hb
  dsimp only [TransversePrelude.slope] at hg
  nlinarith [mul_nonneg hg.le hδ]

/-- Every prelude radius fails the computed test before the prescribed slope crossing. -/
theorem prelude_computed_failure {ε b δ : ℝ} (hε : 0 < ε)
    (hg : 2 * ε / 5 < TransversePrelude.slope b) (hδ : 0 < δ) :
    ε * δ / 8 < TaylorCriticality.taylorDecrement objective 1 (point 0 b) (point 0 δ) := by
  rw [taylorDecrement_one_local (by norm_num)]
  simp only [point_zero_coord, point_one_coord, mul_zero, neg_zero, zero_sub]
  dsimp only [TransversePrelude.slope] at hg
  nlinarith [mul_lt_mul_of_pos_right hg hδ, mul_pos hε hδ]

/-- Before the accepted-point crossing, full vertical witnesses give a genuine completed
failed inspection at the current point and incoming radius. -/
theorem exists_prelude_inspection {ε b : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hb : 1 ≤ b) (hg : 2 * ε / 5 < TransversePrelude.slope b)
    (a : State Plane) (hp : a.point = point 0 b)
    (hδ : a.radii 1 ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ I : Inspection (parameters ε hε hε1) exactOracle.derivative a,
      I.order = 1 ∧
      (I.search 1 le_rfl (by norm_num [parameters]) I.order_pos).direction =
        fun k => point 0 (InexactRegularization.halvedRadius (a.radii 1) k) := by
  apply exists_prescribed_inspection hε hε1 a hδ (point 0)
  · intro δ hδ
    simpa only [hp] using prelude_coefficientWitness hb hδ
  · intro δ hδ
    simpa only [hp] using prelude_computed_failure hε hg hδ

/-- After a prescribed number of actual accuracy halvings, point, parameter, radii and
cache are unchanged. Every positive-order request is halved and freshness is restored. -/
def refinedState (a : State Plane) (n : ℕ) : State Plane :=
  ⟨⟨a.point, a.sigma, a.radii, fun i => (1 / 2 : ℝ) ^ n * a.request i,
    if n = 0 then a.fresh else true⟩, a.valueCache⟩

/-- Zero request halvings preserve the complete incoming state. -/
@[simp] theorem refinedState_zero (a : State Plane) : refinedState a 0 = a := by
  cases a with
  | mk a cache => cases a; simp [refinedState]

/-- Successive displayed request states are precisely the actual accuracy-refinement
update, including the incoming cache and the fresh-batch flag. -/
theorem refinedState_succ {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (a : State Plane) (n : ℕ) :
    refinedState a (n + 1) = refine (parameters ε hε hε1) (refinedState a n) := by
  simp only [refinedState, refine, InexactRegularization.refine, parameters,
    Nat.succ_ne_zero, ↓reduceIte]
  congr 2
  funext i
  rw [pow_succ]
  ring

/-- Actual request halving preserves the fixed-objective invariant. -/
theorem invariant_refinedState (a : State Plane) (ha : Invariant a) (n : ℕ) :
    Invariant (refinedState a n) := by
  rcases ha with ⟨hx0, hx1, hy, hg, hσ, hr, hh⟩
  exact ⟨hx0, hx1, hy, hg, hσ, hr, fun i => mul_pos (by positivity) (hh i)⟩

/-- For degree two and checked order one, a strictly short step passes exactly when its
first request is below the actual squared-step threshold. -/
theorem stepAccurate_iff {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (a : State Plane) (s : Plane) (hs : ‖s‖ < 1) :
    InexactRegularization.StepAccurate (parameters ε hε hε1).toImplicitParameters 1
      a.request s ↔ a.request 1 ≤ (1 / 32 : ℝ) * ‖s‖ ^ 2 := by
  rw [InexactRegularization.StepAccurate.short_iff hs]
  norm_num [parameters]

/-- A nonzero strictly short returned step has a finite least accurate request index.
Every earlier index fails the literal checked-order-one test. -/
theorem exists_least_refinement {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (a : State Plane) (hreq : 0 < a.request 1) (s : Plane) (hz : s ≠ 0) (hs : ‖s‖ < 1) :
    ∃ N : ℕ,
      InexactRegularization.StepAccurate (parameters ε hε hε1).toImplicitParameters 1
        (refinedState a N).request s ∧
      ∀ k, k < N → ¬InexactRegularization.StepAccurate
        (parameters ε hε hε1).toImplicitParameters 1 (refinedState a k).request s := by
  have ht : 0 < (1 / 32 : ℝ) * ‖s‖ ^ 2 := mul_pos (by norm_num)
    (sq_pos_of_pos (norm_pos_iff.mpr hz))
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos ht hreq)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hex : ∃ n, (refinedState a n).request 1 ≤ (1 / 32 : ℝ) * ‖s‖ ^ 2 := by
    exact ⟨n, ((lt_div_iff₀ hreq).mp hn).le⟩
  refine ⟨Nat.find hex, (stepAccurate_iff hε hε1 _ _ hs).mpr (Nat.find_spec hex), ?_⟩
  intro k hk hkacc
  exact Nat.find_min hex hk ((stepAccurate_iff hε hε1 _ _ hs).mp hkacc)

/-- Every earlier failed accuracy index uses the actual returned inner result and the
literal refine-step constructor. Exact coefficients allow the same result to be reused. -/
theorem refinement_transition {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (a : State Plane) (I : Inspection (parameters ε hε hε1) exactOracle.derivative a)
    (hq : I.order ≤ 1)
    (R : InexactRegularization.InnerResult (parameters ε hε hε1).toImplicitParameters 0
      (exactOracle.derivative a.point a.request) a.sigma I.radii (I.direction hq))
    (k : ℕ) (hfail : ¬InexactRegularization.StepAccurate
      (parameters ε hε hε1).toImplicitParameters 1 (refinedState a k).request R.step) :
    Transition (parameters ε hε hε1) exactOracle (refinedState a k) I
      (refinedState a (k + 1)) false false [] := by
  rw [refinedState_succ hε hε1]
  exact Transition.refineStep hq R hfail

/-- The actual accepted endpoint after the forced request halvings and one fresh trial.
Its cache records precisely the request used at the new endpoint. -/
def acceptedState (a : State Plane) (n : ℕ) (s : Plane) (request : ℝ) : State Plane :=
  ⟨⟨a.point + s, 2, fun _ => 1, (refinedState a n).request, true⟩, some request⟩

/-- An accurate actual return with exact ratio at least one gives the literal accepted
fresh-value transition and records the new endpoint's actual request in its cache. -/
theorem accepted_transition {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (a : State Plane) (hσ : a.sigma = 2)
    (I : Inspection (parameters ε hε hε1) exactOracle.derivative a)
    (hq : I.order ≤ 1)
    (R : InexactRegularization.InnerResult (parameters ε hε hε1).toImplicitParameters 0
      (exactOracle.derivative a.point a.request) a.sigma I.radii (I.direction hq))
    (hr : R.radii = fun _ => 1) (hz : R.step ≠ 0)
    (hp : 0 < decrement (exactOracle.derivative a.point a.request) 2 R.step)
    (hρ : 1 ≤ HigherOrderRegularization.ratio objective 2 a.point R.step)
    (hacc : InexactRegularization.StepAccurate
      (parameters ε hε hε1).toImplicitParameters 1 a.request R.step) :
    let v := freshValueTrial hε hε1 a R.step hp
    Transition (parameters ε hε hε1) exactOracle a I
      (⟨⟨a.point + R.step, 2, fun _ => 1, a.request, true⟩, some v.request⟩ : State Plane)
      true true v.queries := by
  dsimp only
  let v := freshValueTrial hε hε1 a R.step hp
  have hratio : 1 ≤ v.ratio := by
    rw [freshValueTrial_ratio hε hε1 a R.step hz hp]
    exact hρ
  have haccept : (parameters ε hε hε1).eta1 ≤ v.ratio := by
    change (1 / 4 : ℝ) ≤ v.ratio
    linarith
  have ht := Transition.trial (P := parameters ε hε hε1) (O := exactOracle)
    (a := a) (I := I) hq R hacc v 2
      (parameterUpdate_of_eq_two hε hε1 hσ hratio)
  simpa only [trialState, ite_eq_left haccept, hr, decide_eq_true haccept] using ht

/-- Skew-inspection analytic gates construct the actual injection return with its fixed
squared-gradient initialization, both inner transitions and unit returned radii. -/
theorem injection_innerResult {ε b : ℝ} (h : TransverseInjection.Conditions ε b)
    (hε1 : ε < 1) (a : State Plane) (hp : a.point = point 0 b) (hσ : a.sigma = 2)
    (I : Inspection (parameters ε h.tolerance_pos hε1) exactOracle.derivative a)
    (ho : I.order = 1)
    (hd : (I.search 1 le_rfl (by norm_num [parameters]) I.order_pos).direction =
      fun k => TransverseInjection.direction
        (InexactRegularization.halvedRadius (a.radii 1) k)) :
    ∃ R : InexactRegularization.InnerResult
      (parameters ε h.tolerance_pos hε1).toImplicitParameters 0
      (exactOracle.derivative a.point a.request) a.sigma I.radii
        (I.direction (by change I.order ≤ 1; omega)),
      R.step = TransverseInjection.step ε ∧ R.length = 2 ∧ R.radii = (fun _ => 1) ∧
      R.execution.state 0 = ⟨‖fderiv ℝ objective a.point‖ ^ 2 / 100,
        fun _ => 1, 0, .minimize⟩ := by
  have hid := InexactRegularization.Inspection.direction_eq_of_order_one I ho
    (by change I.order ≤ 1; omega) _ hd
  rw [hid]
  generalize I.radii = radii
  generalize InexactRegularization.halvedRadius (a.radii 1) (I.halvings 1) = δ
  rw [show exactOracle.derivative a.point a.request =
    (fun i => iteratedFDeriv ℝ i objective a.point) from rfl, hp, hσ]
  exact TransverseInjection.exists_innerResult h
    (parameters ε h.tolerance_pos hε1).toImplicitParameters rfl rfl rfl rfl 0 radii δ

/-- Transverse-inspection analytic gates construct the actual tail return, including its
fixed squared-gradient initialization and the unit returned-radius policy. -/
theorem tail_innerResult {ε b : ℝ} (h : TransverseTailTrial.Conditions ε b)
    (hε1 : ε < 1) (a : State Plane) (hp : a.point = point (2 * ε / 3) b)
    (hσ : a.sigma = 2)
    (I : Inspection (parameters ε h.epsilon_pos hε1) exactOracle.derivative a)
    (ho : I.order = 1)
    (hd : (I.search 1 le_rfl (by norm_num [parameters]) I.order_pos).direction =
      fun k => point (-InexactRegularization.halvedRadius (a.radii 1) k) 0) :
    ∃ R : InexactRegularization.InnerResult
      (parameters ε h.epsilon_pos hε1).toImplicitParameters 0
      (exactOracle.derivative a.point a.request) a.sigma I.radii
        (I.direction (by change I.order ≤ 1; omega)),
      R.step = TransverseTailTrial.step ε ∧ R.length = 2 ∧ R.radii = (fun _ => 1) ∧
      R.execution.state 0 = ⟨‖fderiv ℝ objective a.point‖ ^ 2 / 100,
        fun _ => 1, 0, .minimize⟩ := by
  have hid := InexactRegularization.Inspection.direction_eq_of_order_one I ho
    (by change I.order ≤ 1; omega) _ hd
  rw [hid]
  generalize I.radii = radii
  generalize InexactRegularization.halvedRadius (a.radii 1) (I.halvings 1) = δ
  rw [show exactOracle.derivative a.point a.request =
    (fun i => iteratedFDeriv ℝ i objective a.point) from rfl, hp, hσ]
  exact TransverseTailTrial.exists_innerResult h
    (parameters ε h.epsilon_pos hε1).toImplicitParameters rfl rfl rfl rfl 0 radii δ

/-- A prelude inspection returns the actual chosen global minimum, with two inner
transitions, unit radii and the fixed squared-gradient initialization policy. -/
theorem prelude_innerResult {ε b : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hb : 1 ≤ b)
    (a : State Plane) (hp : a.point = point 0 b) (hσ : a.sigma = 2)
    (I : Inspection (parameters ε hε hε1) exactOracle.derivative a) (hq : I.order ≤ 1) :
    ∃ R : InexactRegularization.InnerResult (parameters ε hε hε1).toImplicitParameters 0
      (exactOracle.derivative a.point a.request) a.sigma I.radii (I.direction hq),
      R.step = TransversePrelude.step b ∧ R.length = 2 ∧ R.radii = (fun _ => 1) ∧
      R.execution.state 0 = ⟨‖fderiv ℝ objective a.point‖ ^ 2 / 100,
        fun _ => 1, 0, .minimize⟩ := by
  have hm : ∀ t, HigherOrderApproximateRegularization.model objective
      (parameters ε hε hε1).p a.point a.sigma (TransversePrelude.step b) ≤
      HigherOrderApproximateRegularization.model objective
        (parameters ε hε hε1).p a.point a.sigma t := by
    simpa only [parameters, hp, hσ] using TransversePrelude.step_minimizes b
  have hgz : fderiv ℝ objective a.point ≠ 0 := by
    rw [hp]
    exact TransverseCubicModel.fderiv_objective_ne_zero_of_tail 0 hb
  have hg1 : ‖fderiv ℝ objective a.point‖ ≤ 1 := by
    rw [hp, TransverseInjection.initial_slope_eq]
    exact (TransversePrelude.slope_le_half hb).trans (by norm_num)
  let R := InexactRegularization.squaredGradientGlobalMinInnerResult
    (parameters ε hε hε1).toImplicitParameters rfl objective a.point 0 a.sigma I.radii
      (I.direction hq) (TransversePrelude.step b) hm hgz hg1
      (TransversePrelude.norm_step_lt_one hb)
  refine ⟨R, rfl, rfl, ?_, rfl⟩
  exact InexactRegularization.squaredGradientGlobalMinInnerResult_radii _ rfl _ _ _ _ _ _ _
    hm hgz hg1 (TransversePrelude.norm_step_lt_one hb)

/-- The prelude's actual chosen step is nonzero, so its request refinement terminates. -/
theorem prelude_step_ne_zero {b : ℝ} (hb : 1 ≤ b) : TransversePrelude.step b ≠ 0 := by
  intro hz
  have hp := TransversePrelude.step_one_coord_pos hb
  rw [hz] at hp
  norm_num at hp

/-- Every nonzero short actual step whose cubic model does not exceed its zero value has
strictly positive true Taylor prediction at the fixed parameter two. -/
theorem prediction_pos_of_model_le {a s : Plane} (hz : s ≠ 0)
    (hm : HigherOrderRegularization.model objective 2 a 2 s ≤
      HigherOrderRegularization.model objective 2 a 2 0) :
    0 < decrement (fun i => iteratedFDeriv ℝ i objective a) 2 s := by
  have hdec := HigherOrderRegularization.predicted_decrease_of_model_le hm
  have hnorm : 0 < ‖s‖ ^ 3 := pow_pos (norm_pos_iff.mpr hz) 3
  rw [decrement_iteratedFDeriv, TaylorCriticality.taylorDecrement_eq]
  norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul,
    Nat.cast_one, RegularizedTaylorModel.taylorModel_zero] at hdec
  linarith

/-- The actual endpoint after finitely many request halvings and the specified fresh
trial, including its positive half-budget value-cache request. -/
def refinementEndpoint (a : State Plane) (n : ℕ) (s : Plane) : State Plane :=
  acceptedState a n s ((1 / 32 : ℝ) *
    decrement (exactOracle.derivative a.point a.request) 2 s / 2)

section Path
variable {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
  (a : State Plane) (hσ : a.sigma = 2)
  (I : Inspection (parameters ε hε hε1) exactOracle.derivative a)
  (hq : I.order ≤ 1)
  (R : InexactRegularization.InnerResult (parameters ε hε hε1).toImplicitParameters 0
    (exactOracle.derivative a.point a.request) a.sigma I.radii (I.direction hq))
  (hr : R.radii = fun _ => 1) (hz : R.step ≠ 0)
  (hp : 0 < decrement (exactOracle.derivative a.point a.request) 2 R.step)
  (hρ : 1 ≤ HigherOrderRegularization.ratio objective 2 a.point R.step)
  (n : ℕ)
  (hbefore : ∀ k, k < n → ¬InexactRegularization.StepAccurate
    (parameters ε hε hε1).toImplicitParameters 1 (refinedState a k).request R.step)
  (hacc : InexactRegularization.StepAccurate
    (parameters ε hε hε1).toImplicitParameters 1 (refinedState a n).request R.step)
  (J : Inspection (parameters ε hε hε1) exactOracle.derivative
    (refinementEndpoint a n R.step))

/-- A finite actual path contains precisely the forced inaccurate returned-step refinements
and then the accepted fresh-value trial. The endpoint inspection is supplied by the next
segment; the incoming cache is arbitrary. -/
def refinementTrialPath : Path (parameters ε hε hε1) exactOracle where
  length := n + 1
  node := fun k => if k ≤ n then ⟨refinedState a k, I⟩ else
    ⟨refinementEndpoint a n R.step, J⟩
  trial := fun k => decide (k = n)
  accepted := fun k => decide (k = n)
  queries := fun k => if k = n then
    (freshValueTrial hε hε1 (refinedState a n) R.step hp).queries else []
  transition := by
    intro k hk
    have hkn : k ≤ n := by omega
    rw [ite_eq_left hkn]
    by_cases hlt : k < n
    · have hsucc : k + 1 ≤ n := by omega
      have hne : k ≠ n := by omega
      rw [ite_eq_left hsucc, ite_eq_right hne, decide_eq_false hne]
      exact refinement_transition hε hε1 a I hq R k (hbefore k hlt)
    · have he : k = n := by omega
      subst k
      have hsucc : ¬n + 1 ≤ n := by omega
      rw [ite_eq_right hsucc, ite_eq_left rfl, decide_eq_true (Eq.refl n)]
      exact accepted_transition hε hε1 (refinedState a n) hσ I hq R hr hz hp hρ hacc

/-- The block starts at exactly the incoming complete inspected state. -/
@[simp] theorem refinementTrialPath_node_zero :
    (refinementTrialPath hε hε1 a hσ I hq R hr hz hp hρ n hbefore hacc J).node 0 =
      ⟨a, I⟩ := by
  simp only [refinementTrialPath, Nat.zero_le, ite_true]
  congr 1
  exact refinedState_zero a

/-- The complete endpoint node includes the supplied next inspection and the actual
accepted endpoint cache and requests. -/
@[simp] theorem refinementTrialPath_node_end :
    let p := refinementTrialPath hε hε1 a hσ I hq R hr hz hp hρ n hbefore hacc J
    p.node p.length = ⟨refinementEndpoint a n R.step, J⟩ := by
  simp only [refinementTrialPath, show ¬n + 1 ≤ n by omega, ite_false]

/-- Every inspected node before the final acceptance is the same actual failed search,
with only the request vector scaled by the actual number of halvings. -/
theorem refinementTrialPath_node_before {k : ℕ} (hk : k ≤ n) :
    (refinementTrialPath hε hε1 a hσ I hq R hr hz hp hρ n hbefore hacc J).node k =
      ⟨refinedState a k, I⟩ := ite_eq_left hk

/-- The actual value-query log has exactly two requests, both from its sole fresh trial. -/
theorem refinementTrialPath_functionQueries_length :
    (refinementTrialPath hε hε1 a hσ I hq R hr hz hp hρ n hbefore hacc J).functionQueries.length =
      2 := by
  rw [Path.functionQueries_length
    (refinementTrialPath hε hε1 a hσ I hq R hr hz hp hρ n hbefore hacc J)]
  change (∑ k ∈ Finset.range (n + 1),
    (if k = n then
      (freshValueTrial hε hε1 (refinedState a n) R.step hp).queries else []).length) = 2
  rw [Finset.sum_range_succ]
  have hzsum : (∑ k ∈ Finset.range n,
      (if k = n then
        (freshValueTrial hε hε1 (refinedState a n) R.step hp).queries else []).length) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp only [ite_eq_right (Nat.ne_of_lt (Finset.mem_range.mp hk)), List.length_nil]
  rw [hzsum]
  rw [zero_add, ite_eq_left rfl]
  exact ValueTrial.queries_length _

/-- The only trial and acceptance in the actual block occur at its last edge. -/
theorem refinementTrialPath_events (k : ℕ) :
    let p := refinementTrialPath hε hε1 a hσ I hq R hr hz hp hρ n hbefore hacc J
    p.trial k = decide (k = n) ∧ p.accepted k = decide (k = n) := ⟨rfl, rfl⟩

/-- Every actual block edge retains the actual returned inner call, its unit returned
radii and squared-gradient initialization, including the calls discarded by refinement. -/
def refinementTrialPath_branch
    (hmu : (R.execution.state 0).mu = ‖fderiv ℝ objective a.point‖ ^ 2 / 100)
    (k : ℕ)
    (hk : k < (refinementTrialPath hε hε1 a hσ I hq R hr hz hp hρ n hbefore hacc J).length) :
    let p := refinementTrialPath hε hε1 a hσ I hq R hr hz hp hρ n hbefore hacc J
    TransverseQualifiedContinuation.Branch hε hε1 (p.node k).state (p.node k).inspection
      (p.node (k + 1)).state (p.trial k) (p.accepted k) (p.queries k) := by
  have hkn : k ≤ n := by change k < n + 1 at hk; omega
  change TransverseQualifiedContinuation.Branch hε hε1
    ((if k ≤ n then ⟨refinedState a k, I⟩ else ⟨refinementEndpoint a n R.step, J⟩) :
      InspectedState (parameters ε hε hε1) exactOracle).state
    ((if k ≤ n then ⟨refinedState a k, I⟩ else ⟨refinementEndpoint a n R.step, J⟩) :
      InspectedState (parameters ε hε hε1) exactOracle).inspection
    ((if k + 1 ≤ n then ⟨refinedState a (k + 1), I⟩ else
      ⟨refinementEndpoint a n R.step, J⟩) : InspectedState (parameters ε hε hε1) exactOracle).state
    (decide (k = n)) (decide (k = n))
    (if k = n then (freshValueTrial hε hε1 (refinedState a n) R.step hp).queries else [])
  rw [ite_eq_left hkn]
  by_cases hlt : k < n
  · have hsucc : k + 1 ≤ n := by omega
    have hne : k ≠ n := by omega
    rw [ite_eq_left hsucc, ite_eq_right hne, decide_eq_false hne]
    change TransverseQualifiedContinuation.Branch hε hε1 (refinedState a k) I
      (refinedState a (k + 1)) false false []
    rw [refinedState_succ hε hε1]
    exact TransverseQualifiedContinuation.Branch.refineStep hq
      (⟨R, hr, hmu⟩ : TransverseQualifiedContinuation.Returned
        (a := refinedState a k) I hq) (hbefore k hlt)
  · have he : k = n := by omega
    subst k
    have hsucc : ¬n + 1 ≤ n := by omega
    rw [ite_eq_right hsucc, ite_eq_left rfl, decide_eq_true (Eq.refl n)]
    let v := freshValueTrial hε hε1 (refinedState a n) R.step hp
    have hratio : 1 ≤ v.ratio := by
      rw [freshValueTrial_ratio hε hε1 (refinedState a n) R.step hz hp]
      exact hρ
    have haccept : (parameters ε hε hε1).eta1 ≤ v.ratio := by
      change (1 / 4 : ℝ) ≤ v.ratio
      linarith
    let Q : TransverseQualifiedContinuation.Returned (a := refinedState a n) I hq :=
      ⟨R, hr, hmu⟩
    have ht := TransverseQualifiedContinuation.Branch.trial (a := refinedState a n)
      (I := I) hq Q hacc hp (parameterUpdate_of_eq_two hε hε1 hσ hratio)
    have hend : trialState (P := parameters ε hε hε1) (O := exactOracle)
        (refinedState a n) I hq R v 2 = refinementEndpoint a n R.step := by
      calc
        _ = (⟨⟨(refinedState a n).point + R.step, 2, R.radii,
            (refinedState a n).request, true⟩, some v.request⟩ : State Plane) :=
          ite_eq_left haccept
        _ = _ := by rw [hr]; rfl
    change TransverseQualifiedContinuation.Branch hε hε1 (refinedState a n) I
      (refinementEndpoint a n R.step) true true v.queries
    change TransverseQualifiedContinuation.Branch hε hε1 (refinedState a n) I
      (trialState (P := parameters ε hε hε1) (O := exactOracle)
        (refinedState a n) I hq R v 2) true
        (decide ((parameters ε hε hε1).eta1 ≤ v.ratio)) v.queries at ht
    rw [hend, decide_eq_true haccept] at ht
    exact ht

end Path

end Optimization.TransverseRefinementBlocks
