import Numlib.Optimization.CompositeTaylorModels
import Numlib.Optimization.HigherOrderApproximateRegularizationInner
import Mathlib.Topology.Order.IntermediateValue

/-!
# Actual composite regularization executions

The scalar smooth part and vector smooth part are expanded separately. The Lipschitz
composition is always retained exactly, including in inner gap tests. Existence of a stopping
certificate is equivalent to the true generalized gap condition. Literal computed failures
retain their actual directions and do not imply failure of that condition. Evaluation counts
retain the
rejection cache and count the scalar and vector functions separately from the composition.
-/

noncomputable section
open scoped Nat NNReal
open Set Metric
namespace Optimization.CompositeRegularization
open RegularizedTaylorModel CompositeTaylorModels TaylorCriticality
open HigherOrderApproximateRegularization (Parameters ValidRadii ParameterUpdate
  OuterState OuterOutcome IsInitial InnerState InnerInitial InnerPhase)
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The composite objective. -/
def objective (f : E → ℝ) (c : E → F) (h : F → ℝ) (x : E) : ℝ := f x + h (c x)

/-- The smooth scalar part of the actual regularized composite model. -/
def smoothModel (f : E → ℝ) (p : ℕ) (x : E) (σ : ℝ) (s : E) : ℝ :=
  taylorModel f p x s + σ * ‖s‖ ^ (p + 1) / (p + 1)!

/-- The smooth vector part of the actual composite model. -/
abbrev vectorModel (c : E → F) (p : ℕ) (x : E) := taylorModel c p x

/-- The generalized Taylor decrement of the actual regularized model. -/
def modelDecrement (f : E → ℝ) (c : E → F) (h : F → ℝ)
    (p j : ℕ) (x : E) (σ : ℝ) (s d : E) : ℝ :=
  decrement (smoothModel f p x σ) (vectorModel c p x) h j s d

/-- A feasible direction attaining a requested fraction of a generalized gap. -/
structure GapWitness (f : E → ℝ) (c : E → F) (h : F → ℝ)
    (j : ℕ) (x : E) (δ fraction : ℝ) (d : E) : Prop where
  feasible : ‖d‖ ≤ δ
  fraction_le : fraction * gapOn (decrement f c h j x) (closedBall 0 δ) ≤
    decrement f c h j x d

/-- Every fraction between zero and one is attained by a feasible generalized decrement.
This uses continuity of the retained composition, without differentiating it. -/
theorem exists_fraction_gapWitness [ProperSpace E] (f : E → ℝ) (c : E → F)
    {h : F → ℝ} {K : ℝ≥0} (hh : LipschitzWith K h) (j : ℕ) (x : E)
    {δ fraction : ℝ} (hδ : 0 ≤ δ) (hf0 : 0 ≤ fraction) (hf1 : fraction ≤ 1) :
    ∃ d : E, GapWitness f c h j x δ fraction d ∧
      decrement f c h j x d = fraction * gapOn (decrement f c h j x) (closedBall 0 δ) := by
  have hz : (0 : E) ∈ closedBall 0 δ := by simpa using hδ
  have hc := continuous_decrement f c hh j x
  obtain ⟨d, hd, hmax⟩ := exists_eq_gapOn (isCompact_closedBall 0 δ) ⟨0, hz⟩ hc.continuousOn
  have hg : 0 ≤ gapOn (decrement f c h j x) (closedBall 0 δ) :=
    gapOn_nonneg (isCompact_closedBall 0 δ) hc.continuousOn hz (decrement_zero f c h j x)
  have hpath : ContinuousOn (fun t : ℝ => decrement f c h j x (t • d)) (Icc 0 1) :=
    (hc.comp (continuous_id.smul continuous_const)).continuousOn
  have hmem : fraction * gapOn (decrement f c h j x) (closedBall 0 δ) ∈
      Icc ((fun t : ℝ => decrement f c h j x (t • d)) 0)
        ((fun t : ℝ => decrement f c h j x (t • d)) 1) := by
    simp only [zero_smul, one_smul, decrement_zero, hmax]
    exact ⟨mul_nonneg hf0 hg, mul_le_of_le_one_left hg hf1⟩
  obtain ⟨t, ht, hteq⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hpath hmem
  have hnorm : ‖t • d‖ ≤ δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    have hd' : ‖d‖ ≤ δ := by simpa using hd
    exact (mul_le_of_le_one_left (norm_nonneg d) ht.2).trans hd'
  exact ⟨t • d, ⟨hnorm, hteq.ge⟩, hteq⟩

/-- All nonstrict stopping certificates in the source, with their computed directions. -/
structure PassedTest (P : Parameters) (f : E → ℝ) (c : E → F) (h : F → ℝ)
    (x : E) (δ : ℕ → ℝ) where
  direction : ℕ → E
  witness : ∀ j, 1 ≤ j → j ≤ P.q → GapWitness f c h j x (δ j) P.fraction (direction j)
  passes : ∀ j, 1 ≤ j → j ≤ P.q → decrement f c h j x (direction j) ≤
    P.fraction * (P.epsilon j * δ j ^ j / (j ! : ℝ))

/-- A successful certificate implies the corresponding true generalized gap bound. -/
theorem PassedTest.gap_le {P : Parameters} {f : E → ℝ} {c : E → F} {h : F → ℝ}
    {x : E} {δ : ℕ → ℝ} (a : PassedTest P f c h x δ) {j : ℕ}
    (hj : 1 ≤ j) (hjq : j ≤ P.q) :
    gapOn (decrement f c h j x) (closedBall 0 (δ j)) ≤ P.epsilon j * δ j ^ j / (j ! : ℝ) :=
  (mul_le_mul_iff_right₀ P.fraction_pos).mp
    ((a.witness j hj hjq).fraction_le.trans (a.passes j hj hjq))

/-- The existential stopping certificate is precisely the true generalized gap criterion.
Negating existence, rather than a particular unsuccessful witness, yields true gap failure. -/
theorem passedTest_iff [ProperSpace E] {P : Parameters} {f : E → ℝ} {c : E → F}
    {h : F → ℝ} {K : ℝ≥0} (hh : LipschitzWith K h) {x : E} {δ : ℕ → ℝ}
    (hδ : ValidRadii P δ) : Nonempty (PassedTest P f c h x δ) ↔
      ∀ j, 1 ≤ j → j ≤ P.q →
        gapOn (decrement f c h j x) (closedBall 0 (δ j)) ≤
          P.epsilon j * δ j ^ j / (j ! : ℝ) := by
  classical
  constructor
  · rintro ⟨a⟩ j hj hjq
    exact a.gap_le hj hjq
  · intro ha
    have he : ∀ j, ∃ d : E, (1 ≤ j ∧ j ≤ P.q) →
        GapWitness f c h j x (δ j) P.fraction d ∧
        decrement f c h j x d ≤ P.fraction * (P.epsilon j * δ j ^ j / (j ! : ℝ)) := by
      intro j
      by_cases hj : 1 ≤ j ∧ j ≤ P.q
      · obtain ⟨d, hd, heq⟩ := exists_fraction_gapWitness f c hh j x
          (hδ j hj.1 hj.2).1.le P.fraction_pos.le P.fraction_le_one
        exact ⟨d, fun _ => ⟨hd, heq.le.trans
          (mul_le_mul_of_nonneg_left (ha j hj.1 hj.2) P.fraction_pos.le)⟩⟩
      · exact ⟨0, fun h => (hj h).elim⟩
    choose d hd using he
    exact ⟨⟨d, fun j hj hjq => (hd j ⟨hj, hjq⟩).1,
      fun j hj hjq => (hd j ⟨hj, hjq⟩).2⟩⟩

/-- A literal unsuccessful computed test selects the first failed upper threshold.
Such a failure need not mean that the true generalized gap criterion fails. -/
structure FailedTest (P : Parameters) (f : E → ℝ) (c : E → F) (h : F → ℝ)
    (x : E) (δ : ℕ → ℝ) where
  order : ℕ
  order_pos : 1 ≤ order
  order_le : order ≤ P.q
  direction : ℕ → E
  witness : ∀ j, 1 ≤ j → j ≤ order → GapWitness f c h j x (δ j) P.fraction (direction j)
  earlier : ∀ j, 1 ≤ j → j < order → decrement f c h j x (direction j) ≤
    P.fraction * (P.epsilon j * δ j ^ j / (j ! : ℝ))
  fails : P.fraction * (P.epsilon order * δ order ^ order / (order ! : ℝ)) <
    decrement f c h order x (direction order)

/-- A literal outer model step: nonincrease, positive radii, and either a long step or all
computed generalized model-gap certificates. No inner fraction provenance is assumed. -/
structure ModelStep (P : Parameters) (f : E → ℝ) (c : E → F) (h : F → ℝ)
    (x : E) (σ : ℝ) where
  step : E
  radii : ℕ → ℝ
  radii_valid : ValidRadii P radii
  nonincrease : regularizedModel f c h P.p x σ step ≤ regularizedModel f c h P.p x σ 0
  direction : ℕ → E
  quality : 1 ≤ ‖step‖ ∨ ∀ j, 1 ≤ j → j ≤ P.q →
    GapWitness (smoothModel f P.p x σ) (vectorModel c P.p x) h j step
      (radii j) P.fraction (direction j) ∧
    modelDecrement f c h P.p j x σ step (direction j) ≤
      P.fraction * P.theta * P.epsilon j * radii j ^ j / (j ! : ℝ)

/-- Actual acceptance ratio, using the generalized model prediction and composite objective. -/
def ratio (f : E → ℝ) (c : E → F) (h : F → ℝ) (p : ℕ) (x s : E) : ℝ :=
  (objective f c h x - objective f c h (x + s)) / decrement f c h p x s

/-- One literal composite outer pass. The two counts apply separately to each of `f` and `c`;
composition evaluations are not included. Rejections retain every computed derivative. -/
inductive OuterTransition (P : Parameters) (f : E → ℝ) (c : E → F) (h : F → ℝ) :
    OuterState E → OuterOutcome E → ℕ → ℕ → Prop where
  | stop (a : OuterState E) (htest : a.test = true) (hcache : a.cachedOrder ≤ P.q)
      (hpass : PassedTest P f c h a.point a.radii) :
      OuterTransition P f c h a (.stopTest a) 0 (P.q - a.cachedOrder)
  | equal (a : OuterState E)
      (hfail : a.test = true → Nonempty (FailedTest P f c h a.point a.radii))
      (hcache : a.cachedOrder ≤ P.p) (trial : ModelStep P f c h a.point a.sigma)
      (heq : regularizedModel f c h P.p a.point a.sigma trial.step =
        regularizedModel f c h P.p a.point a.sigma 0) :
      OuterTransition P f c h a (.stopEqual {a with radii := trial.radii})
        0 (P.p - a.cachedOrder)
  | trial (a : OuterState E)
      (hfail : a.test = true → Nonempty (FailedTest P f c h a.point a.radii))
      (hcache : a.cachedOrder ≤ P.p) (trial : ModelStep P f c h a.point a.sigma)
      (hstrict : regularizedModel f c h P.p a.point a.sigma trial.step <
        regularizedModel f c h P.p a.point a.sigma 0) (nextSigma : ℝ)
      (hupdate : ParameterUpdate P (ratio f c h P.p a.point trial.step) a.sigma nextSigma) :
      OuterTransition P f c h a (.next
        (if P.eta1 ≤ ratio f c h P.p a.point trial.step then
          ⟨a.point + trial.step, nextSigma, trial.radii, 0, true⟩ else
          ⟨a.point, nextSigma, a.radii, P.p, false⟩)) 1 (P.p - a.cachedOrder)

/-- A genuine finite execution, allowing either stopping location or a continuing final trial.
It imposes no desired optimality or finite termination conclusion. -/
structure OuterExecution (P : Parameters) (f : E → ℝ) (c : E → F) (h : F → ℝ)
    (x : E) (σ : ℝ) (δ : ℕ → ℝ) (N : ℕ) where
  state : ℕ → OuterState E
  functionCalls : ℕ → ℕ
  derivativeCalls : ℕ → ℕ
  last : OuterOutcome E
  initial : IsInitial P x σ δ (state 0)
  valid : ∀ k, k ≤ N → P.sigmaMin ≤ (state k).sigma ∧
    ValidRadii P (state k).radii ∧ (state k).cachedOrder ≤ P.p ∧
    ((state k).test = false → (state k).cachedOrder = P.p)
  transition : ∀ k, k < N → OuterTransition P f c h (state k) (.next (state (k + 1)))
    (functionCalls k) (derivativeCalls k)
  final : OuterTransition P f c h (state N) last (functionCalls N) (derivativeCalls N)

/-- Total scalar function evaluations; the vector map has the same count. -/
def OuterExecution.functionCount {P : Parameters} {f : E → ℝ} {c : E → F} {h : F → ℝ}
    {x : E} {σ : ℝ} {δ : ℕ → ℝ} {N : ℕ} (run : OuterExecution P f c h x σ δ N) : ℕ :=
  1 + ∑ k ∈ Finset.range (N + 1), run.functionCalls k

/-- Individual derivative-order evaluations of `f`; `c` has the same separate count. -/
def OuterExecution.derivativeCount {P : Parameters} {f : E → ℝ} {c : E → F} {h : F → ℝ}
    {x : E} {σ : ℝ} {δ : ℕ → ℝ} {N : ℕ} (run : OuterExecution P f c h x σ δ N) : ℕ :=
  ∑ k ∈ Finset.range (N + 1), run.derivativeCalls k

/-- The actual number of derivative batches, separately for each smooth map.
Orders obtained together at one outer pass form one batch; retained caches cost no new batch. -/
def OuterExecution.derivativeBatchCount {P : Parameters} {f : E → ℝ} {c : E → F} {h : F → ℝ}
    {x : E} {σ : ℝ} {δ : ℕ → ℝ} {N : ℕ} (run : OuterExecution P f c h x σ δ N) : ℕ :=
  ∑ k ∈ Finset.range (N + 1), if 0 < run.derivativeCalls k then 1 else 0

/-- A continuing outer pass evaluates each smooth function once and only missing derivatives. -/
theorem OuterTransition.continuing_costs {P : Parameters} {f : E → ℝ} {c : E → F}
    {h : F → ℝ} {a b : OuterState E} {nf nd : ℕ}
    (ht : OuterTransition P f c h a (.next b) nf nd) :
    nf = 1 ∧ nd = P.p - a.cachedOrder := by
  cases ht
  exact ⟨rfl, rfl⟩

/-- A successful stopping test evaluates only the missing criticality derivatives. -/
theorem OuterTransition.test_costs {P : Parameters} {f : E → ℝ} {c : E → F}
    {h : F → ℝ} {a b : OuterState E} {nf nd : ℕ}
    (ht : OuterTransition P f c h a (.stopTest b) nf nd) :
    nf = 0 ∧ nd = P.q - a.cachedOrder := by
  cases ht
  exact ⟨rfl, rfl⟩

/-- An execution whose accepted points have empty derivative caches uses exactly one new
batch at each pass, including the final stopping test. -/
theorem OuterExecution.derivativeBatchCount_eq_of_cache_zero {P : Parameters}
    {f : E → ℝ} {c : E → F} {h : F → ℝ} {x : E} {σ : ℝ} {δ : ℕ → ℝ} {N : ℕ}
    (run : OuterExecution P f c h x σ δ N)
    (hcache : ∀ k, k ≤ N → (run.state k).cachedOrder = 0)
    (hstop : run.last = .stopTest (run.state N)) : run.derivativeBatchCount = N + 1 := by
  have hpos : ∀ k ∈ Finset.range (N + 1), 0 < run.derivativeCalls k := by
    intro k hk
    have hkN : k ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    by_cases hk' : k < N
    · rw [(run.transition k hk').continuing_costs.2, hcache k hkN, Nat.sub_zero]
      exact lt_of_lt_of_le Nat.zero_lt_one (P.order_pos.trans P.order_le)
    · have he : k = N := by omega
      subst k
      have ht := run.final
      rw [hstop] at ht
      rw [ht.test_costs.2, hcache N le_rfl, Nat.sub_zero]
      exact lt_of_lt_of_le Nat.zero_lt_one P.order_pos
  unfold OuterExecution.derivativeBatchCount
  calc
    _ = ∑ _k ∈ Finset.range (N + 1), 1 :=
      Finset.sum_congr rfl (fun k hk => ite_eq_left (hpos k hk))
    _ = N + 1 := by simp

/-- Detailed composite inner transitions. The favorable flag requires actual convexity;
choosing `false` allows a conservative execution even when convexity is unknown. -/
inductive InnerTransition (P : Parameters) (g : E → ℝ) (v : E → F) (h : F → ℝ)
    (convex : Bool) (convex_correct : convex = true → ConvexOn ℝ univ h)
    (minimizer : E) : InnerState E → InnerState E → Prop where
  | minimize (a : InnerState E) (hphase : a.phase = .minimize) (s : E)
      (hfrac : a.mu * (objective g v h 0 - objective g v h minimizer) ≤
        objective g v h 0 - objective g v h s) :
      InnerTransition P g v h convex convex_correct minimizer a
        ⟨a.mu, a.radii, s, if 1 ≤ ‖s‖ then .returned else .inspect 1⟩
  | pass (a : InnerState E) (j : ℕ) (hphase : a.phase = .inspect j)
      (hj : 1 ≤ j) (hjq : j ≤ P.q) (d : E)
      (hw : GapWitness g v h j a.step (a.radii j) P.fraction d)
      (htest : decrement g v h j a.step d ≤
        P.fraction * P.theta * P.epsilon j * a.radii j ^ j / (j ! : ℝ)) :
      InnerTransition P g v h convex convex_correct minimizer a
        ⟨a.mu, a.radii, a.step, if j = P.q then .returned else .inspect (j + 1)⟩
  | halve (a : InnerState E) (j : ℕ) (hphase : a.phase = .inspect j)
      (hj : 1 ≤ j) (hjq : j ≤ P.q) (hbranch : 2 ≤ j ∨ convex = false) (d : E)
      (hw : GapWitness g v h j a.step (a.radii j) P.fraction d)
      (hfail : P.fraction * P.theta * P.epsilon j * a.radii j ^ j / (j ! : ℝ) <
        decrement g v h j a.step d)
      (hsmall : objective g v h a.step - objective g v h (a.step + d) <
        (1 / 2 : ℝ) * P.fraction * P.theta * P.epsilon j * a.radii j ^ j / (j ! : ℝ)) :
      InnerTransition P g v h convex convex_correct minimizer a
        ⟨a.mu, Function.update a.radii j (a.radii j / 2), a.step, .inspect j⟩
  | improve (a : InnerState E) (j : ℕ) (hphase : a.phase = .inspect j)
      (hj : 1 ≤ j) (hjq : j ≤ P.q) (d : E)
      (hw : GapWitness g v h j a.step (a.radii j) P.fraction d)
      (hfail : P.fraction * P.theta * P.epsilon j * a.radii j ^ j / (j ! : ℝ) <
        decrement g v h j a.step d)
      (hother : (j = 1 ∧ convex = true) ∨
        (1 / 2 : ℝ) * P.fraction * P.theta * P.epsilon j * a.radii j ^ j / (j ! : ℝ) ≤
          objective g v h a.step - objective g v h (a.step + d)) :
      InnerTransition P g v h convex convex_correct minimizer a
        ⟨(1 + a.mu) / 2, a.radii, a.step, .minimize⟩

/-- Finite inner histories retain a genuine attained global minimizer as reference. -/
structure InnerExecution (P : Parameters) (g : E → ℝ) (v : E → F) (h : F → ℝ)
    (convex : Bool) (convex_correct : convex = true → ConvexOn ℝ univ h)
    (minimizer : E) (N : ℕ) where
  state : ℕ → InnerState E
  is_minimizer : ∀ t, objective g v h minimizer ≤ objective g v h t
  initial : InnerInitial (state 0)
  transition : ∀ k, k < N →
    InnerTransition P g v h convex convex_correct minimizer (state k) (state (k + 1))

/-- The accuracy fraction remains positive, at most one, and nondecreasing. -/
theorem InnerTransition.mu_bounds {P : Parameters} {g : E → ℝ} {v : E → F} {h : F → ℝ}
    {convex : Bool} {hconv : convex = true → ConvexOn ℝ univ h} {z : E}
    {a b : InnerState E} (hab : InnerTransition P g v h convex hconv z a b)
    (ha : 0 < a.mu) (ha1 : a.mu ≤ 1) :
    0 < b.mu ∧ b.mu ≤ 1 ∧ a.mu ≤ b.mu := by
  cases hab <;> dsimp <;> exact ⟨by linarith, by linarith, by linarith⟩

/-- Every inspected or returned transition retains its actual positive-fraction certificate. -/
theorem InnerTransition.fraction_of_ne_minimize {P : Parameters} {g : E → ℝ} {v : E → F}
    {h : F → ℝ} {convex : Bool} {hconv : convex = true → ConvexOn ℝ univ h} {z : E}
    {a b : InnerState E} (hab : InnerTransition P g v h convex hconv z a b)
    (ha : a.phase ≠ .minimize → a.mu * (objective g v h 0 - objective g v h z) ≤
      objective g v h 0 - objective g v h a.step) (hb : b.phase ≠ .minimize) :
    b.mu * (objective g v h 0 - objective g v h z) ≤
      objective g v h 0 - objective g v h b.step := by
  cases hab <;> simp_all

/-- Every finite composite inner history retains a positive accuracy fraction at most one. -/
theorem InnerExecution.mu_bounds {P : Parameters} {g : E → ℝ} {v : E → F} {h : F → ℝ}
    {convex : Bool} {hconv : convex = true → ConvexOn ℝ univ h} {z : E} {N : ℕ}
    (run : InnerExecution P g v h convex hconv z N) {k : ℕ} (hk : k ≤ N) :
    0 < (run.state k).mu ∧ (run.state k).mu ≤ 1 := by
  induction k with
  | zero => exact ⟨run.initial.1, run.initial.2.1⟩
  | succ k ih =>
    have hi := ih (by omega)
    exact ((run.transition k (by omega)).mu_bounds hi.1 hi.2).imp_right And.left

/-- Every inspected or returned state has the actual fraction certificate of its last
minimization. A new pending minimization does not prematurely claim such a certificate. -/
theorem InnerExecution.fraction_of_ne_minimize {P : Parameters} {g : E → ℝ} {v : E → F}
    {h : F → ℝ} {convex : Bool} {hconv : convex = true → ConvexOn ℝ univ h} {z : E} {N : ℕ}
    (run : InnerExecution P g v h convex hconv z N) {k : ℕ} (hk : k ≤ N)
    (hphase : (run.state k).phase ≠ .minimize) :
    (run.state k).mu * (objective g v h 0 - objective g v h z) ≤
      objective g v h 0 - objective g v h (run.state k).step := by
  induction k with
  | zero => exact (hphase run.initial.2.2.2).elim
  | succ k ih =>
    exact (run.transition k (by omega)).fraction_of_ne_minimize
      (fun hp => ih (by omega) hp) hphase

/-- A returned equality step from the detailed inner history certifies global model
minimality at zero. Literal outer nonincrease alone has no such consequence. -/
theorem InnerExecution.isMin_zero_of_return_eq {P : Parameters} {g : E → ℝ} {v : E → F}
    {h : F → ℝ} {convex : Bool} {hconv : convex = true → ConvexOn ℝ univ h} {z : E} {N : ℕ}
    (run : InnerExecution P g v h convex hconv z N)
    (hreturn : (run.state N).phase = .returned)
    (heq : objective g v h (run.state N).step = objective g v h 0) :
    ∀ t, objective g v h 0 ≤ objective g v h t :=
  HigherOrderApproximateRegularization.isMin_zero_of_fraction_eq run.is_minimizer
    (run.mu_bounds le_rfl).1 (run.fraction_of_ne_minimize le_rfl
      (by rw [hreturn]; decide)) heq

/-- Certified convexity preserves the first radius through every detailed inner transition. -/
theorem InnerTransition.convex_first_radius {P : Parameters} {g : E → ℝ} {v : E → F}
    {h : F → ℝ} {hconv : true = true → ConvexOn ℝ univ h} {z : E}
    {a b : InnerState E} (hab : InnerTransition P g v h true hconv z a b) :
    b.radii 1 = a.radii 1 := by
  cases hab with
  | minimize => rfl
  | pass => rfl
  | halve j hphase hj hjq hbranch d hw hfail hsmall =>
    have hj1 : j ≠ 1 := by
      rcases hbranch with hj2 | hf
      · omega
      · cases hf
    exact Function.update_of_ne hj1.symm _ _
  | improve => rfl

/-- Every finite history with certified convexity retains the unit first radius. -/
theorem InnerExecution.convex_first_radius {P : Parameters} {g : E → ℝ} {v : E → F}
    {h : F → ℝ} {hconv : true = true → ConvexOn ℝ univ h} {z : E} {N : ℕ}
    (run : InnerExecution P g v h true hconv z N) {k : ℕ} (hk : k ≤ N) :
    (run.state k).radii 1 = 1 := by
  induction k with
  | zero => rw [run.initial.2.2.1]
  | succ k ih =>
    rw [(run.transition k (by omega)).convex_first_radius]
    exact ih (by omega)

end Optimization.CompositeRegularization
