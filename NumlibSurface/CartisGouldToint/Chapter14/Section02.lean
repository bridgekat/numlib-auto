import Numlib.Optimization.Regularization.Constrained.TerminalRadii
import Numlib.Optimization.Regularization.Constrained.Complexity
import Numlib.Optimization.TrustRegion.HighOrder.CountingCounterexample
import Numlib.Optimization.Constrained.BoxZeroReturn
import Numlib.Optimization.Regularization.HighOrder.VanishingSteps
import Numlib.Optimization.HighOrder.ConstrainedCriticality
import Numlib.Optimization.Sparse.BoxLinear
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Cartis–Gould–Toint, Section 14.2: high-order criticality with simple constraints

Constrained criticality uses actual Taylor decrements over feasible displacements in a
closed ball. No convexity or connectivity of the closed feasible set is required.
Theorem 14.2.1 retains the additive criticality allowance and the local Lipschitz
neighborhood. The unindexed radius in (14.2.6) is the optimality radius `δ_j` from its
hypothesis and from (14.2.7).

In Lemma 14.2.5, (14.2.18) and (14.2.19) must minimize the linear objective `g·d`
(or maximize its negative): the printed maximization contradicts the displayed optimizer,
the proof, and the subsequent TR1-SP algorithm. For one coordinate with `x=0`,
`g=1`, `δ=1` and budget `k=1`, the formula
gives `d=-1`, whereas `d=1` has the larger linear value. The sparse problem below uses
minimization.
-/

namespace CartisGouldToint

/-- The high-order constrained Taylor criticality measure (14.2.2), using the exact
feasible-displacement condition (14.2.3). For a closed feasible set at a feasible point
and nonnegative radius, the supremum is an attained nonnegative maximum. -/
noncomputable def highOrderConstrainedCriticality {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (j : ℕ) (X : Set E) (x : E) (δ : ℝ) : ℝ :=
  TaylorModel.constrainedCriticality f j X x δ

/-- **Theorem 14.2.1 (stability of approximate constrained minimizers).**
Small constrained Taylor criticality gives the printed objective stability bounds with
additive allowance `η` on actual feasible displacements, in both Lipschitz-constant cases.
The highest derivative is Lipschitz only on an open ball of radius larger than `δ`.
The feasible set is closed and nonempty, with no convexity assumption. -/
theorem theorem_14_2_1 {n j : ℕ} (hj : 0 < j)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : IsClosed X) (_hXne : X.Nonempty) (x : EuclideanSpace ℝ (Fin n))
    (hf : ContDiff ℝ j f) {δ ε η L R : ℝ}
    (hδ : 0 < δ) (_hδ1 : δ ≤ 1) (hε : 0 < ε) (_hε1 : ε ≤ 1) (_hη : 0 ≤ η)
    (hL : 0 ≤ L) (hR : δ < R)
    (hlip : ∀ u ∈ Metric.ball x R, ∀ v ∈ Metric.ball x R,
      ‖iteratedFDeriv ℝ j f u - iteratedFDeriv ℝ j f v‖ ≤ L * ‖u - v‖)
    (hcrit : highOrderConstrainedCriticality f j X x δ ≤ ε * δ ^ j / j.factorial + η) :
    (0 < L → ∀ d : EuclideanSpace ℝ (Fin n), x + d ∈ X →
      ‖d‖ ≤ min δ ((j + 1 : ℕ) * ε / L) →
      f x - 2 * ε * δ ^ j / j.factorial - η ≤ f (x + d)) ∧
    (L = 0 → ∀ d : EuclideanSpace ℝ (Fin n), x + d ∈ X → ‖d‖ ≤ δ →
      f x - ε * δ ^ j / j.factorial - η ≤ f (x + d)) := by
  have hball : Metric.closedBall x δ ⊆ Metric.ball x R := fun z hz =>
    (Metric.mem_closedBall.mp hz).trans_lt hR
  have hlip' : ∀ u ∈ Metric.closedBall x δ, ∀ v ∈ Metric.closedBall x δ,
      ‖iteratedFDeriv ℝ j f u - iteratedFDeriv ℝ j f v‖ ≤ L * ‖u - v‖ :=
    fun u hu v hv => hlip u (hball hu) v (hball hv)
  constructor
  · intro hLpos d hfeas hd
    have hdδ := (le_min_iff.mp hd).1
    have hb := TaylorModel.value_ge_of_constrainedCriticality hj hX Metric.isOpen_ball
      hf.contDiffOn x hδ.le hball hL hlip' hcrit hfeas hdδ
    have hsmall : L * ‖d‖ ≤ (j + 1 : ℕ) * ε := by
      have hh := (le_div_iff₀ hLpos).mp (le_min_iff.mp hd).2
      nlinarith
    have herr := TaylorModel.lipschitz_error_le_tolerance j (norm_nonneg d) hε.le hdδ hsmall
    calc f x - 2 * ε * δ ^ j / j.factorial - η =
        f x - ε * δ ^ j / j.factorial - η - ε * δ ^ j / j.factorial := by ring
      _ ≤ f x - ε * δ ^ j / j.factorial - η -
          L * ‖d‖ ^ (j + 1) / (j + 1).factorial := by linarith
      _ ≤ f (x + d) := hb
  · intro hLzero d hfeas hd
    have hb := TaylorModel.value_ge_of_constrainedCriticality hj hX Metric.isOpen_ball
      hf.contDiffOn x hδ.le hball hL hlip' hcrit hfeas hd
    simpa only [hLzero, zero_mul, zero_div, sub_zero] using hb

end CartisGouldToint

namespace CartisGouldToint

/-- A global solution of the corrected sparse linear box problem (14.2.18).
The norm on `Fin n → ℝ` is the infinity norm; the support count is the actual count of
nonzero coordinates of the next iterate `x+d`. The objective is the actual linear form. -/
def sparseStepProblem {n : ℕ} (x g : Fin n → ℝ) (k : ℕ) (δ : ℝ) (d : Fin n → ℝ) : Prop :=
  ‖d‖ ≤ δ ∧ (SparseBox.support (fun i => x i + d i)).card ≤ k ∧
    ∀ s : Fin n → ℝ, ‖s‖ ≤ δ → (SparseBox.support (fun i => x i + s i)).card ≤ k →
      SparseBox.objective g d ≤ SparseBox.objective g s

/-- **Lemma 14.2.5 (optimal sparse solution of the box problem).**
The finite knapsack has an optimum, and every optimal binary support selection produces
an actual sparse box optimizer. The three sums reproduce (14.2.20), while the binary
cardinality sum and gain reproduce (14.2.21). This includes vanishing coefficients and
ties without a uniqueness claim. A nonnegative radius also covers the zero-radius case.

The source's `max g·d` in (14.2.18) must be `min g·d`, consistently with its displayed
step, proof and algorithm. The coefficient vector is arbitrary, so it can in particular
be the gradient specified in the source. -/
theorem lemma_14_2_5 {n : ℕ} (x g : Fin n → ℝ) (k : ℕ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hx : (SparseBox.support x).card ≤ k) :
    (∃ R : Finset (Fin n), SparseBox.IsOptimalSelection x g k δ R) ∧
    (∀ R : Finset (Fin n), SparseBox.IsOptimalSelection x g k δ R →
      sparseStepProblem x g k δ (SparseBox.step x g δ R) ∧
      SparseBox.step x g δ R =
        (∑ i ∈ SparseBox.forced x δ, Pi.single i (-δ * Real.sign (g i))) -
        (∑ i ∈ SparseBox.support x \ SparseBox.forced x δ, Pi.single i (x i)) -
        (∑ i ∈ (SparseBox.forced x δ)ᶜ,
          Pi.single i (SparseBox.binary R i * (δ * Real.sign (g i) - x i))) ∧
      (∀ i, SparseBox.binary R i = 0 ∨ SparseBox.binary R i = 1) ∧
      (∑ i ∈ (SparseBox.forced x δ)ᶜ, SparseBox.binary R i) ≤
        ((k - (SparseBox.forced x δ).card : ℕ) : ℝ) ∧
      SparseBox.selectionGain x g δ R =
        ∑ i ∈ (SparseBox.forced x δ)ᶜ,
          SparseBox.binary R i * (δ * |g i| - x i * g i)) := by
  refine ⟨SparseBox.exists_optimalSelection x g k δ, ?_⟩
  intro R hR
  obtain ⟨hfeas, hmin⟩ := SparseBox.step_isMinOn hδ hx hR
  refine ⟨?_, SparseBox.step_eq_sub_sums x g δ R, SparseBox.binary_values R, ?_,
    SparseBox.selectionGain_eq_binary_sum hR.1⟩
  · have hf := (SparseBox.admissible_iff_norm hδ).mp hfeas
    refine ⟨hf.1, hf.2, ?_⟩
    intro s hs hcard
    exact hmin ((SparseBox.admissible_iff_norm hδ).mpr ⟨hs, hcard⟩)
  · rw [SparseBox.sum_binary hR.1]
    exact_mod_cast hR.1.2

end CartisGouldToint

namespace CartisGouldToint

/-- **Counterexample to the literal Lemma 14.2.2.** A fixed exact ARqp run on
`X = ℝ` has an actual prefix of every finite length and every trial is successful,
but its accepted objective decreases tend to zero. All required first-order
smoothness and initial-level derivative bounds hold. Therefore no positive
uniform decrease coefficient exists, even after fixing this entire run.

The iterates already satisfy true epsilon criticality; their computed relative
checks still select a trial. Restricting the decrease claim to iterations before
a true certificate is an essential correction. -/
theorem lemma_14_2_2_counterexample :
    let f := HighOrderRegularization.ObstructionCounterexample.objective
    let P := HighOrderRegularization.ObstructionCounterexample.settings
    let D := HighOrderRegularization.VanishingSteps.data
    IsClosed (Set.univ : Set ℝ) ∧ Convex ℝ (Set.univ : Set ℝ) ∧
      (Set.univ : Set ℝ).Nonempty ∧ ContDiff ℝ 1 f ∧
      (∀ x y, ‖iteratedFDeriv ℝ 1 f x - iteratedFDeriv ℝ 1 f y‖ ≤ ‖x - y‖) ∧
      (∀ x, f x ≤ f (D.point 0) → ‖iteratedFDeriv ℝ 1 f x‖ ≤ 1) ∧
      (∀ x, 0 ≤ f x) ∧
      (∀ N, HighOrderRegularization.Run f P (fun _ => 9 / 10) D N) ∧
      (∀ k, P.eta1 ≤ D.ratio k) ∧
      (∀ k, highOrderConstrainedCriticality f 1 Set.univ (D.point k) 1 =
        TaylorModel.criticality f 1 (D.point k) 1) ∧
      ¬∃ κ : ℝ, 0 < κ ∧ ∀ k : ℕ, P.eta1 ≤ D.ratio k →
        κ * (9 / 10 : ℝ) ^ 2 ≤ f (D.point k) - f (D.point (k + 1)) := by
  dsimp only
  obtain ⟨hsmooth, hlip, hlow⟩ :=
    HighOrderRegularization.ObstructionCounterexample.objective_regularity
  refine ⟨isClosed_univ, convex_univ, Set.univ_nonempty, hsmooth,
    ?_, fun x hx => HighOrderRegularization.VanishingSteps.level_gradient_bound hx,
    hlow, HighOrderRegularization.VanishingSteps.run,
    HighOrderRegularization.VanishingSteps.successful, ?_,
    HighOrderRegularization.VanishingSteps.no_uniform_decrease⟩
  · intro x y
    simpa only [one_mul] using hlip x y
  · intro k
    exact TaylorModel.constrainedCriticality_univ _ _ _ _

end CartisGouldToint

namespace CartisGouldToint

/-- **Counterexample to literal Theorem 14.2.4.** The feasible set is the simple
scalar box `[-5,5]`, with open convex neighborhood `(-6,6)`. The actual quadratic
objective satisfies the full zeroth- and first-jet assumptions, with fixed
constants eight and thirty-two. In particular, the extra zeroth-order
Lipschitz assumption of this theorem is retained.

An actual initial constrained check fails. The feasible step four has the
initial model value, uses the large-step bypass with unchanged unit radii,
and immediately returns zero. No point produced by this execution satisfies
the requested constrained criticality at any legal positive radius. -/
theorem theorem_14_2_4_counterexample :
    let f := RegularizationZeroReturn.objective
    let X := RegularizationZeroReturn.Box.feasible
    let S := RegularizationZeroReturn.Box.neighborhood
    let P := RegularizationZeroReturn.Box.settings
    IsClosed X ∧ X.Nonempty ∧ Convex ℝ X ∧ IsOpen S ∧ Convex ℝ S ∧ X ⊆ S ∧
      ContDiffOn ℝ 1 f S ∧
      (∀ j : ℕ, j ≤ 1 → ∀ x ∈ X, f x ≤ f 0 →
        ‖iteratedFDeriv ℝ j f x‖ ≤ 32 ∧ ∀ y ∈ S,
          ‖iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j f y‖ ≤ 8 * ‖x - y‖) ∧
      (∀ x ∈ X, 0 ≤ f x) ∧
      HighOrderRegularization.ConstrainedOuterZeroExit f X P (fun _ : Fin 1 => 1 / 2)
        0 4 (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 0) 0 ∧
      ¬∃ (z δ : ℝ), RegularizationZeroReturn.Box.actual_exit.producedPoint z ∧
        0 < δ ∧ δ ≤ 1 ∧ highOrderConstrainedCriticality f 1 X z δ ≤ (1 / 2 : ℝ) * δ := by
  dsimp only
  obtain ⟨hclosed, hne, hconv, hopen, hconvS, hXS⟩ :=
    RegularizationZeroReturn.Box.geometry
  obtain ⟨hsmooth, hjets, hlow⟩ := RegularizationZeroReturn.Box.source_regularity
  exact ⟨hclosed, hne, hconv, hopen, hconvS, hXS, hsmooth, hjets, hlow,
    RegularizationZeroReturn.Box.actual_exit, RegularizationZeroReturn.Box.no_produced_certificate⟩

end CartisGouldToint

namespace CartisGouldToint

/-- **Lemma 14.2.3: obstruction to accuracy-independent additive constants.**
The fixed quartic objective, box, initial point, radius and trust-region
settings satisfy every first-order source regularity condition. For each
requested rejection count, a genuine TR1-SC execution has precisely one
successful trial and still fails true constrained criticality. Hence (14.2.13)
cannot have both constants fixed before the requested accuracy and all legal
model returns. The source's inclusive successful prefix `0,...,m` has `m+1`
trials here. This does not contradict a fixed-accuracy count with an explicit
logarithmic radius term; that valid companion is stated separately. -/
theorem lemma_14_2_3_counterexample :
    let f := HighOrderTrustRegion.CountingCounterexample.objective
    let X := HighOrderTrustRegion.CountingCounterexample.feasible
    let S := HighOrderTrustRegion.CountingCounterexample.neighborhood
    let ε := HighOrderTrustRegion.CountingCounterexample.accuracy
    let P := HighOrderTrustRegion.CountingCounterexample.parameters
    let x := HighOrderTrustRegion.CountingCounterexample.point
    let s := HighOrderTrustRegion.CountingCounterexample.step
    let d := HighOrderTrustRegion.CountingCounterexample.direction
    let j := HighOrderTrustRegion.CountingCounterexample.order
    let Δ := HighOrderTrustRegion.CountingCounterexample.radius
    let ρ := HighOrderTrustRegion.CountingCounterexample.ratio
    IsClosed X ∧ X.Nonempty ∧ Convex ℝ X ∧ IsOpen S ∧ Convex ℝ S ∧ X ⊆ S ∧
    ContDiffOn ℝ 1 f S ∧ (∀ y, 0 ≤ f y) ∧
    (∀ y ∈ X, f y ≤ f 1 → ‖iteratedFDeriv ℝ 1 f y‖ ≤ 27 ∧
      ∀ z ∈ S,
        ‖iteratedFDeriv ℝ 1 f y - iteratedFDeriv ℝ 1 f z‖ ≤ 27 * ‖y - z‖) ∧
    (∀ m, x m 0 = 1 ∧ Δ 0 = 1 ∧
      HighOrderTrustRegion.ConstrainedRun f X (P m) (x m) (s m) d j Δ (ρ m) (m + 1) ∧
      ∀ i, ε m < highOrderConstrainedCriticality f 1 X (x m i) 1) ∧
    ¬∃ A B : ℝ, ∀ m : ℕ, (m : ℝ) ≤ A *
      (EvaluationComplexity.successfulIterations {i | (P m).eta1 ≤ ρ m i} (m + 1)).card + B :=
  HighOrderTrustRegion.CountingCounterexample.verified_counterexample

/-- **Radius-floor companion to Lemma 14.2.3.** Every actual constrained
trust-region run obeys the standard count with its explicit logarithmic
endpoint-radius term. If the positive floor depends on the requested accuracy,
so does this additive term. No uniform-before-accuracy assertion is made. -/
theorem lemma_14_2_3_radius_floor {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {q : ℕ} {f : E → ℝ} {X : Set E}
    {P : HighOrderTrustRegion.Parameters q} {x s : ℕ → E}
    {d : ℕ → Fin q → E} {j : ℕ → Fin q} {Δ ρ : ℕ → ℝ} {N : ℕ}
    (h : HighOrderTrustRegion.ConstrainedRun f X P x s d j Δ ρ N)
    {δmin : ℝ} (hδ : 0 < δmin) (hlow : δmin ≤ Δ N) :
    (N : ℝ) ≤ (EvaluationComplexity.successfulIterations
      {i | P.eta1 ≤ ρ i} N).card *
        (1 + Real.log P.gamma3 / |Real.log P.gamma2|) +
      |Real.log (δmin / Δ 0)| / |Real.log P.gamma2| :=
  h.iterations_le_of_radius_lower hδ hlow

end CartisGouldToint

namespace CartisGouldToint
open InexactTrustRegion

/-- Corrected exact ARqp-SC branch of Lemma 14.2.2. Restrict the decrease claim
to successful steps before the next true certificate; literal nontermination
alone is insufficient. The actual positive-global-gap detailed solver gives
all-order adaptive radii. Replace local anchored regularity by global C^p and
globally Lipschitz derivatives of orders one through p. The fixed coefficient precedes all
accuracies and actual executions. The rate is j(p+1)/p, including q=1's
(p+1)/p rate. Other algorithm variants are not asserted by this companion. -/
theorem lemma_14_2_2_ARqp_before_certificate {n p q : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : IsClosed X) (_hconv : Convex ℝ X) (P : ConstrainedRegularization.Settings p q)
    (hf : ContDiff ℝ p f) {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, 1 ≤ i → i ≤ p → ∀ x y,
      ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ ≤ L * ‖x - y‖) :
    ∃ κ > 0, ∀ (ε : Fin q → ℝ)
      (D : ConstrainedRegularization.ExecutionData (EuclideanSpace ℝ (Fin n)) q)
      (N : ℕ), ConstrainedRegularization.Run f X P ε D N → ∀ k < N,
      P.eta1 ≤ D.ratio k → ¬ConstrainedRegularization.TargetAt f X P ε D (k + 1) →
      κ * ConstrainedRegularization.accuracyFactor P ε ≤
        f (D.point k) - f (D.point (k + 1)) ∧
      κ * minimumAccuracy P.order_pos ε ^ ((q : ℝ) * (p + 1 : ℕ) / p) ≤
        f (D.point k) - f (D.point (k + 1)) := by
  let S := HighOrderRegularization.parameterCap P L
  let κ := ConstrainedRegularization.commonDecreaseCoefficient P L S
  have hκ : 0 < κ := ConstrainedRegularization.commonDecreaseCoefficient_pos P hL
    (HighOrderRegularization.parameterCap_pos P L).le
  refine ⟨κ, hκ, ?_⟩
  intro ε D N h k hk ha hnot
  have hd := h.function_decrease_uniform hX hf hL hlip hk ha hnot
  refine ⟨hd, ?_⟩
  exact (mul_le_mul_of_nonneg_left
    (ConstrainedRegularization.accuracyFactor_lower_minimum P ε h.accuracy_pos
      h.accuracy_le_one) hκ.le).trans hd

end CartisGouldToint

namespace CartisGouldToint
open InexactTrustRegion

/-- Corrected exact ARqp-SC branch of Theorem 14.2.4. Replace the permissive
outer zero-decrease return by the genuine feasible positive-global-gap detailed
solver, with actual finite feasible Taylor halvings. Replace local anchored
regularity by global `C^p` and globally Lipschitz derivatives of orders one
through p; exact evaluation
does not require zeroth-order Lipschitz continuity. The feasible set is closed
and convex. Every actual execution array is constructed, with no prefix or
model-step existence hypothesis.

Positive constants precede all accuracies. The actual all-order constrained
Taylor certificate has legal adaptive radii bounded below by a fixed positive
coefficient times each accuracy, with first-order radius one.
The initialized objective count is K+1 and every enabled derivative order has
its initialized accepted-update count. The rate factor is the true finite
minimum of epsilon_j^(j(p+1)/p), retaining (p+1)/p at q=1. No unit second-order
radius, other algorithm variant or sharpness claim is asserted here. -/
theorem theorem_14_2_4_ARqp_detailed {n p q : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : IsClosed X) (hconv : Convex ℝ X) (P : ConstrainedRegularization.Settings p q)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ X)
    (hf : ContDiff ℝ p f) {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, 1 ≤ i → i ≤ p → ∀ x y,
      ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ ≤ L * ‖x - y‖)
    (hlow : ∀ x ∈ X, flow ≤ f x) :
    ∃ κs > 0, ∃ κa > 0, ∃ κc > 0, ∀ ε : Fin q → ℝ,
      (∀ a, 0 < ε a ∧ ε a ≤ 1) →
      ∃ (D : ConstrainedRegularization.ExecutionData (EuclideanSpace ℝ (Fin n)) q)
        (K : ℕ) (δ : Fin q → ℝ), D.point 0 = x₀ ∧ D.parameter 0 = P.sigmaInitial ∧
        (∀ a, D.radius 0 a = 1) ∧ ConstrainedRegularization.Run f X P ε D K ∧
        ConstrainedRegularization.TargetAt f X P ε D K ∧
        (∀ k < K, ¬ConstrainedRegularization.TargetAt f X P ε D k) ∧
        D.point K ∈ X ∧ (∀ a, 0 < δ a ∧ δ a ≤ 1) ∧
        (∀ a, ConstrainedRegularization.radiusCoefficient P L
          (HighOrderRegularization.parameterCap P L) * ε a ≤ δ a) ∧
        (∀ a, highOrderConstrainedCriticality f (modelOrder a) X (D.point K) (δ a) ≤
          ε a * δ a ^ modelOrder a / (modelOrder a).factorial) ∧
        (∀ a, modelOrder a = 1 → δ a = 1) ∧
        ((K + 1 : ℕ) : ℝ) ≤
          κa * (f x₀ - flow) / ConstrainedRegularization.accuracyFactor P ε + κc ∧
        (((EvaluationComplexity.successfulIterations {i | P.eta1 ≤ D.ratio i} K).card + 1 :
          ℕ) : ℝ) ≤
          κs * (f x₀ - flow) / ConstrainedRegularization.accuracyFactor P ε + 2 ∧
        (∀ j, 1 ≤ j → j ≤ p →
          (ConstrainedRegularization.derivativeEvaluationsForOrder P D K j : ℝ) ≤
            κs * (f x₀ - flow) / ConstrainedRegularization.accuracyFactor P ε + 2) := by
  classical
  obtain ⟨κs, hs, κa, ha, κc, hc, hall⟩ :=
    ConstrainedRegularization.certified_execution_with_radius_floor
      f X hX hconv P x₀ hx₀ hf hL hlip hlow
  refine ⟨κs, hs, κa, ha, κc, hc, ?_⟩
  intro ε hε
  obtain ⟨D, K, δ₀, hx, hσ, hinit, hr, ht, hfirst, hopt, hfloor, hunit, hF, hD⟩ :=
    hall ε hε
  let δ : Fin q → ℝ := fun a => if modelOrder a = 1 then 1 else δ₀ a
  have hδ : ∀ a, 0 < δ a ∧ δ a ≤ 1 := by
    intro a
    by_cases hj : modelOrder a = 1
    · simp only [δ, ite_eq_left hj]
      exact ⟨zero_lt_one, le_rfl⟩
    · simpa only [δ, ite_eq_right hj] using hopt.2.1 a
  have hfloor' : ∀ a, ConstrainedRegularization.radiusCoefficient P L
      (HighOrderRegularization.parameterCap P L) * ε a ≤ δ a := by
    intro a
    by_cases hj : modelOrder a = 1
    · have hc := ConstrainedRegularization.radiusCoefficient_mem P hL
        (HighOrderRegularization.parameterCap_pos P L).le
      have hh := mul_le_mul hc.2 (hε a).2 (hε a).1.le zero_le_one
      simpa only [δ, ite_eq_left hj, one_mul] using hh
    · simpa only [δ, ite_eq_right hj] using hfloor a
  have hb : ∀ a, highOrderConstrainedCriticality f (modelOrder a) X (D.point K) (δ a) ≤
      ε a * δ a ^ modelOrder a / (modelOrder a).factorial := by
    intro a
    by_cases hj : modelOrder a = 1
    · simpa only [δ, ite_eq_left hj, hj, pow_one, Nat.factorial_one, Nat.cast_one,
        mul_one, div_one, highOrderConstrainedCriticality] using hunit a hj
    · simpa only [δ, ite_eq_right hj, highOrderConstrainedCriticality] using hopt.2.2 a
  refine ⟨D, K, δ, hx, hσ, hinit, hr, ht, hfirst, hopt.1, hδ, hfloor', hb,
    fun a hj => ite_eq_left hj, hF, hD, ?_⟩
  intro j hj hjp
  rw [ConstrainedRegularization.derivativeEvaluationsForOrder_eq P D K hj hjp]
  exact hD

end CartisGouldToint
