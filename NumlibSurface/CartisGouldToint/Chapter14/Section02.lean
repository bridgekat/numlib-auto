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
