import Numlib.Optimization.InexactRegularizationInspection

/-!
# Regularization with implicit accuracy refinement

Legal finite executions use the supplied tensor oracle, actual radius searches, and the
existing detailed inner regularization procedure. Exact objective values determine acceptance.
Accuracy refinement restores the radii from before inspection and leaves the parameter fixed.
The checked derivative degree is explicit: the literal branch uses `q`, while the
all-order correction uses `p`. Neither variant assumes eventual true optimality or count bounds.
-/

noncomputable section
open scoped Nat
namespace Optimization.InexactRegularization
open InexactTaylorModels TaylorCriticality

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {checked : ℕ}

/-- Regularization constants together with geometric tensor-accuracy refinement. -/
structure Parameters extends HigherOrderApproximateRegularization.Parameters where
  kappaInitial : ℝ
  kappaInitial_nonneg : 0 ≤ kappaInitial
  kappaStep : ℝ
  gammaAccuracy : ℝ
  kappaStep_pos : 0 < kappaStep
  gammaAccuracy_pos : 0 < gammaAccuracy
  gammaAccuracy_lt_one : gammaAccuracy < 1

/-- A complete Step 1 inspection records only orders actually visited, including every
halving and the displacement finally selected at each visited order. `q+1` means all passed. -/
structure Inspection (P : Parameters) (c : ℝ) (A : Coefficients E)
    (σ : ℝ) (δ : ℕ → ℝ) where
  order : ℕ
  order_pos : 1 ≤ order
  order_le : order ≤ P.q + 1
  halvings : ℕ → ℕ
  search : ∀ j, 1 ≤ j → j ≤ P.q → j ≤ order →
    RadiusSearch c A P.p j σ (δ j) P.fraction (P.epsilon j) (halvings j)
  earlier : ∀ j (hj : 1 ≤ j) (hjq : j ≤ P.q) (hjo : j < order),
    decrement A j ((search j hj hjq hjo.le).direction (halvings j)) ≤
      P.fraction * P.epsilon j * halvedRadius (δ j) (halvings j) ^ j / (2 * (j ! : ℝ))
  failed : ∀ hq : order ≤ P.q,
    P.fraction * P.epsilon order * halvedRadius (δ order) (halvings order) ^ order /
        (2 * (order ! : ℝ)) <
      decrement A order ((search order order_pos hq le_rfl).direction (halvings order))
  retained : ∀ hq : order ≤ P.q,
    P.fraction * P.epsilon order * halvedRadius (δ order) (halvings order) ^ order /
        (4 * (order ! : ℝ)) ≤
      c - regularizedPolynomial c A P.p σ
        ((search order order_pos hq le_rfl).direction (halvings order))

/-- Post-inspection radii retain unvisited components unchanged. -/
def Inspection.radii {P : Parameters} {c : ℝ} {A : Coefficients E} {σ : ℝ}
    {δ : ℕ → ℝ} (I : Inspection P c A σ δ) (j : ℕ) : ℝ :=
  if j ≤ I.order then halvedRadius (δ j) (I.halvings j) else δ j

/-- The actual displacement passed from the failed inspection to model minimization. -/
def Inspection.direction {P : Parameters} {c : ℝ} {A : Coefficients E} {σ : ℝ}
    {δ : ℕ → ℝ} (I : Inspection P c A σ δ) (hq : I.order ≤ P.q) : E :=
  (I.search I.order I.order_pos hq le_rfl).direction (I.halvings I.order)

/-- A Step 2 result comes from a returned execution of the actual inner procedure. Its
model value retains the selected Step 1 witness, as required by the outer algorithm. -/
structure InnerResult (P : Parameters) (c : ℝ) (A : Coefficients E) (σ : ℝ)
    (δ : ℕ → ℝ) (d : E) where
  minimizer : E
  length : ℕ
  execution : HigherOrderApproximateRegularization.InnerExecution
    P.toParameters (regularizedPolynomial c A P.p σ) minimizer length
  returned : (execution.state length).phase = .returned
  retained : regularizedPolynomial c A P.p σ (execution.state length).step ≤
    regularizedPolynomial c A P.p σ d

/-- The actual point selected by the inner execution. -/
def InnerResult.step {P : Parameters} {c : ℝ} {A : Coefficients E} {σ : ℝ}
    {δ : ℕ → ℝ} {d : E} (s : InnerResult P c A σ δ d) : E :=
  (s.execution.state s.length).step

/-- On the weak long-step boundary the outer algorithm inherits the inspected radii. -/
def InnerResult.radii {P : Parameters} {c : ℝ} {A : Coefficients E} {σ : ℝ}
    {δ : ℕ → ℝ} {d : E} (s : InnerResult P c A σ δ d) : ℕ → ℝ :=
  if 1 ≤ ‖s.step‖ then δ else (s.execution.state s.length).radii

/-- The accuracy check imposed on steps of norm below one at the specified derivative
orders. The literal algorithm checks through `q`; the all-order variant checks through `p`. -/
def StepAccurate (P : Parameters) (checked : ℕ) (h : ℕ → ℝ) (s : E) : Prop :=
  1 ≤ ‖s‖ ∨ ∀ i ∈ Finset.Icc 1 checked, h i ≤ P.kappaStep * ‖s‖ ^ (P.p - i + 1)

omit [NormedSpace ℝ E] in
/-- A short step passes precisely when every requested checked degree meets its accuracy bound. -/
theorem StepAccurate.short_iff {P : Parameters} {h : ℕ → ℝ} {s : E} (hs : ‖s‖ < 1) :
    StepAccurate P checked h s ↔
      ∀ i ∈ Finset.Icc 1 checked, h i ≤ P.kappaStep * ‖s‖ ^ (P.p - i + 1) := by
  exact or_iff_right (not_le_of_gt hs)

omit [NormedSpace ℝ E] in
/-- Passing a larger set of checked degrees implies passing each smaller checked range. -/
theorem StepAccurate.of_le {P : Parameters} {h : ℕ → ℝ} {s : E}
    {lower upper : ℕ} (ha : StepAccurate P upper h s) (hle : lower ≤ upper) :
    StepAccurate P lower h s := by
  rcases ha with hl | hs
  · exact Or.inl hl
  · exact Or.inr fun i hi => hs i (Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hi).1, (Finset.mem_Icc.mp hi).2.trans hle⟩)

/-- When `q<p`, the literal short-step check can pass positive requests that fail the
all-order check. Thus the two specializations cannot be identified in general. -/
theorem exists_stepAccurate_not_all_orders (P : Parameters) (hqp : P.q < P.p) :
    ∃ h : ℕ → ℝ, (∀ i, 0 < h i) ∧ StepAccurate P P.q h (1 / 2 : ℝ) ∧
      ¬StepAccurate P P.p h (1 / 2 : ℝ) := by
  let h : ℕ → ℝ := fun i =>
    if i ≤ P.q then P.kappaStep * (1 / 2 : ℝ) ^ (P.p - i + 1) else P.kappaStep
  have hs : ‖(1 / 2 : ℝ)‖ < 1 := by norm_num
  refine ⟨h, ?_, ?_, ?_⟩
  · intro i
    dsimp [h]
    split_ifs
    · exact mul_pos P.kappaStep_pos (by positivity)
    · exact P.kappaStep_pos
  · apply (StepAccurate.short_iff hs).mpr
    intro i hi
    simp only [h, ite_eq_left (Finset.mem_Icc.mp hi).2]
    norm_num
  · intro ha
    have hp := (StepAccurate.short_iff hs).mp ha P.p
      (Finset.mem_Icc.mpr ⟨P.order_pos.trans P.order_le, le_rfl⟩)
    have hn : ¬P.p ≤ P.q := by omega
    simp only [h, ite_eq_right hn, Nat.sub_self, zero_add, pow_one] at hp
    norm_num at hp
    linarith [P.kappaStep_pos]

/-- The current point, pre-inspection radii, requests and cache freshness. A false freshness
flag means exactly the same point and requests are reused after rejection. -/
structure State (E : Type*) where
  point : E
  sigma : ℝ
  radii : ℕ → ℝ
  request : ℕ → ℝ
  fresh : Bool

/-- The exact acceptance ratio with the actual supplied polynomial decrement. -/
def ratio (P : Parameters) (f : E → ℝ) (oracle : E → (ℕ → ℝ) → Coefficients E)
    (a : State E) (s : E) : ℝ :=
  (f a.point - f (a.point + s)) / decrement (oracle a.point a.request) P.p s

/-- Accuracy-only refinement restores pre-inspection radii, retains point and parameter,
and requests a fresh tensor batch. -/
def refine (P : Parameters) (a : State E) : State E :=
  ⟨a.point, a.sigma, a.radii, fun i => P.gammaAccuracy * a.request i, true⟩

/-- One actual outer pass. The two refinement constructors identify their precise source
phase. Trial costs and cache reuse are separated from tensor recomputation. -/
inductive Transition (P : Parameters) (checked : ℕ) (f : E → ℝ)
    (oracle : E → (ℕ → ℝ) → Coefficients E) :
    State E → State E → Bool → Bool → Prop where
  | refineInspection (a : State E)
      (I : Inspection P (f a.point) (oracle a.point a.request) a.sigma a.radii)
      (hall : I.order = P.q + 1) :
      Transition P checked f oracle a (refine P a) false false
  | refineStep (a : State E)
      (I : Inspection P (f a.point) (oracle a.point a.request) a.sigma a.radii)
      (hq : I.order ≤ P.q)
      (s : InnerResult P (f a.point) (oracle a.point a.request) a.sigma I.radii
        (I.direction hq)) (hinaccurate : ¬StepAccurate P checked a.request s.step) :
      Transition P checked f oracle a (refine P a) false false
  | trial (a : State E)
      (I : Inspection P (f a.point) (oracle a.point a.request) a.sigma a.radii)
      (hq : I.order ≤ P.q)
      (s : InnerResult P (f a.point) (oracle a.point a.request) a.sigma I.radii
        (I.direction hq)) (haccurate : StepAccurate P checked a.request s.step)
      (nextSigma : ℝ)
      (hupdate : HigherOrderApproximateRegularization.ParameterUpdate P.toParameters
        (ratio P f oracle a s.step) a.sigma nextSigma) :
      Transition P checked f oracle a
        (if P.eta1 ≤ ratio P f oracle a s.step then
          ⟨a.point + s.step, nextSigma, s.radii, a.request, true⟩ else
          ⟨a.point, nextSigma, I.radii, a.request, false⟩)
        true (decide (P.eta1 ≤ ratio P f oracle a s.step))

/-- Legal finite prefixes include initialization and request positivity, but no termination,
true-quality, model-decrease rate or evaluation-complexity premise. -/
structure Execution (P : Parameters) (checked : ℕ) (f : E → ℝ)
    (oracle : E → (ℕ → ℝ) → Coefficients E) (N : ℕ) where
  state : ℕ → State E
  trial : ℕ → Bool
  accepted : ℕ → Bool
  initial_fresh : (state 0).fresh = true
  initial_sigma : P.sigmaMin ≤ (state 0).sigma
  initial_radii : HigherOrderApproximateRegularization.ValidRadii P.toParameters (state 0).radii
  initial_tolerance : ∀ j, 1 ≤ j → j ≤ P.q → P.epsilon j ≤ (state 0).radii j
  initial_request : ∀ i ∈ Finset.Icc 1 P.p, 0 < (state 0).request i
  initial_request_le : ∀ i ∈ Finset.Icc 1 P.p, (state 0).request i ≤ P.kappaInitial
  transition : ∀ k, k < N →
    Transition P checked f oracle (state k) (state (k + 1)) (trial k) (accepted k)

/-- One initial exact function evaluation plus one at each actual trial. -/
def Execution.functionCount {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N : ℕ}
    (r : Execution P checked f oracle N) : ℕ :=
  1 + ((Finset.range N).filter fun k => r.trial k).card

/-- Tensor batches prepared for the inspected iterations; rejected points reuse their cache. -/
def Execution.derivativeBatches {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N : ℕ}
    (r : Execution P checked f oracle N) : ℕ :=
  ((Finset.range N).filter fun k => (r.state k).fresh).card

end Optimization.InexactRegularization
