import Numlib.Optimization.HighOrder.StepLower
import Numlib.Optimization.Regularization.HighOrder.CriticalityObstruction
import Numlib.Optimization.HighOrder.ModelSolve.Sharp
import Numlib.Optimization.HighOrder.ModelSolve.Uniform
import Numlib.Optimization.Regularization.HighOrder.StepTwoTermination
import Numlib.Optimization.TrustRegion.HighOrder.SharpnessGlobal
import Numlib.Optimization.TrustRegion.HighOrder.Complexity
import Numlib.Optimization.TrustRegion.HighOrder.Radius
import Numlib.Optimization.TrustRegion.HighOrder.Trial
import NumlibSurface.CartisGouldToint.Chapter04.Section01
import Numlib.Optimization.HighOrder.ModelDecrease
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Arbitrary-order trust-region evaluation complexity

Actual Taylor trials give the prefix gap, radius, decrease and complete evaluation
bounds for TRq. Uniform Hermite interpolation supplies globally regular objectives
realizing the matching inverse-accuracy lower rate. The sharpness construction
corrects the source's objective drop, ceiling estimate, grid origin and derivative
factorials; initialization retains its accuracy-dependent radius.
-/

namespace CartisGouldToint

/-- The scaled approximate criticality gap of equation (12.2.8). -/
noncomputable def scaledTaylorGap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (j : ℕ) (x d : E) (δ : ℝ) : ℝ :=
  ModelDecrease.scaled (taylorDecrement f j x d) δ j

/-- Lemma 12.2.1: before termination, every scaled criticality gap, and hence its prefix minimum,
is at least `ς ε_min`. The trial step also achieves the rescaled criticality gap. The hypotheses
are precisely the failing Step 1 test and the Step 2 model comparison, for each iteration in
the prefix. No global decrease or criticality estimate is assumed. -/
theorem lemma_12_2_1 {n q k : ℕ} (hq : 1 ≤ q)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (ε : ℕ → ℝ) {ς : ℝ} (hς : 0 ≤ ς)
    (x d s : Fin (k + 1) → EuclideanSpace ℝ (Fin n))
    (j : Fin (k + 1) → ℕ) (δ : Fin (k + 1) → ℝ)
    (hj : ∀ i, j i ∈ Finset.Icc 1 q) (hδ : ∀ i, 0 < δ i)
    (htest : ∀ i, ς * ε (j i) * δ i ^ j i / ((j i).factorial : ℝ) <
      taylorDecrement f (j i) (x i) (d i))
    (hstep : ∀ i, taylorDecrement f (j i) (x i) (d i) ≤
      taylorDecrement f (j i) (x i) (s i)) :
    ς * (Finset.Icc 1 q).inf' (Finset.nonempty_Icc.mpr hq) ε ≤
        Finset.univ.inf' Finset.univ_nonempty
          (fun i => scaledTaylorGap f (j i) (x i) (d i) (δ i)) ∧
      scaledTaylorGap f (j (Fin.last k)) (x (Fin.last k)) (d (Fin.last k))
          (δ (Fin.last k)) * δ (Fin.last k) ^ j (Fin.last k) /
          ((j (Fin.last k)).factorial : ℝ) ≤
        taylorDecrement f (j (Fin.last k)) (x (Fin.last k)) (s (Fin.last k)) := by
  constructor
  · apply (Finset.le_inf'_iff _ _).mpr
    intro i _
    exact (mul_le_mul_of_nonneg_left (Finset.inf'_le ε (hj i)) hς).trans
      (ModelDecrease.le_scaled_of_test (j i) (hδ i) (htest i))
  · unfold scaledTaylorGap
    rw [ModelDecrease.scaled_mul_radius _ (hδ (Fin.last k))]
    exact hstep (Fin.last k)

end CartisGouldToint

namespace CartisGouldToint

/-- The fixed, finite-order parameters in Step 0 of Algorithm 12.2.1. -/
abbrev trqParameters (q : ℕ) := HighOrderTrustRegion.Parameters q

/-- A genuine nonterminal trial of Algorithm 12.2.1, with actual Taylor approximations,
the first failed test, actual objective ratio, and capped three-case radius update. -/
abbrev trqTrial {n q : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : trqParameters q)
    (x : EuclideanSpace ℝ (Fin n)) (Δ : ℝ) (d : Fin q → EuclideanSpace ℝ (Fin n))
    (j : Fin q) (s xnext : EuclideanSpace ℝ (Fin n)) (Δnext ρ : ℝ) : Prop :=
  HighOrderTrustRegion.Trial f P x Δ d j s xnext Δnext ρ

/-- The actual maximum per-order Lipschitz constant `L_f` in equation (12.2.6). -/
noncomputable abbrev trqLipschitzConstant {q : ℕ} (P : trqParameters q)
    (L : Fin q → ℝ) : ℝ :=
  HighOrderTrustRegion.maxLipschitzConstant P L

/-- **Lemma 12.2.2 (condition for success).** The exact small-radius condition
(12.2.11), using the genuine scaled Taylor gap and the actual maximum Lipschitz
constant, makes the objective-to-model ratio at least `η₂` and prevents contraction
of the radius. The trial predicate retains the two distinct radii and the capped
update rule, including the allowed enlargement factor `γ₃ = 1`. -/
theorem lemma_12_2_2 {n q : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : trqParameters q}
    {x s xnext : EuclideanSpace ℝ (Fin n)} {Δ Δnext ρ : ℝ}
    {d : Fin q → EuclideanSpace ℝ (Fin n)} {j : Fin q}
    (h : trqTrial f P x Δ d j s xnext Δnext ρ)
    (hf : ContDiff ℝ q f) (L : Fin q → ℝ) (hL : ∀ a, 1 ≤ L a)
    (hlip : ∀ a y z,
      ‖iteratedFDeriv ℝ (HighOrderTrustRegion.modelOrder a) f y -
        iteratedFDeriv ℝ (HighOrderTrustRegion.modelOrder a) f z‖ ≤ L a * ‖y - z‖)
    (hsmall : Δ ≤ min P.theta ((1 - P.eta2) / trqLipschitzConstant P L *
      scaledTaylorGap f (HighOrderTrustRegion.modelOrder j) x (d j)
        (HighOrderTrustRegion.optimalityRadius P Δ))) :
    P.eta2 ≤ ρ ∧ Δ ≤ Δnext := by
  apply h.very_successful hf (HighOrderTrustRegion.maxLipschitzConstant_pos P L hL)
  · intro y z
    exact (hlip j y z).trans (mul_le_mul_of_nonneg_right
      (HighOrderTrustRegion.le_maxLipschitzConstant P L j) (norm_nonneg _))
  · exact hsmall

end CartisGouldToint

namespace CartisGouldToint

/-- A finite nonterminal prefix of Algorithm 12.2.1, with initialized radius and actual
trials. Its rules contain no radius floor, model-decrease floor, or complexity estimate. -/
abbrev trqRun {n q : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : trqParameters q)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (d : ℕ → Fin q → EuclideanSpace ℝ (Fin n))
    (j : ℕ → Fin q) (Δ ρ : ℕ → ℝ) (N : ℕ) : Prop :=
  HighOrderTrustRegion.Run f P x s d j Δ ρ N

/-- The minimum accuracy `ε_min` of equation (12.2.7). -/
noncomputable abbrev trqMinimumAccuracy {q : ℕ} (P : trqParameters q) : ℝ :=
  HighOrderTrustRegion.minimumAccuracy P

/-- The true finite prefix minimum of the scaled gaps in equation (12.2.8). -/
noncomputable abbrev trqPrefixGap {n q : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (P : trqParameters q) (x : ℕ → EuclideanSpace ℝ (Fin n)) (Δ : ℕ → ℝ)
    (d : ℕ → Fin q → EuclideanSpace ℝ (Fin n)) (j : ℕ → Fin q) (k : ℕ) : ℝ :=
  HighOrderTrustRegion.prefixGap f P x Δ d j k

/-- The exact `κ_Δ` of equation (12.2.14). Its arguments consist only of the fixed
parameters, initial radius, initial point and objective derivatives: no accuracy is an
argument. The printed `2q!` denotes `2 · q!`, as in the source reciprocal-factorial proof. -/
noncomputable abbrev trqRadiusConstant {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (q : ℕ) (hq : 0 < q)
    (x₀ : EuclideanSpace ℝ (Fin n)) (Δ₀ theta eta2 gamma1 L : ℝ) : ℝ :=
  HighOrderTrustRegion.radiusConstant f q hq x₀ Δ₀ theta eta2 gamma1 L

/-- **Lemma 12.2.3 (lower bound on the trust-region radius).** The exact coefficient
(12.2.14) is strictly between zero and one, and the uniform prefix bound (12.2.13)
holds at every nonterminal trial. The initial scaled-gap estimate is derived from the
actual Taylor coefficients; the floor follows from the actual preceding updates.
The enlargement factor may equal one. -/
theorem lemma_12_2_3 {n q : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : trqParameters q}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {d : ℕ → Fin q → EuclideanSpace ℝ (Fin n)}
    {j : ℕ → Fin q} {Δ ρ : ℕ → ℝ} {N k : ℕ}
    (h : trqRun f P x s d j Δ ρ N) (hf : ContDiff ℝ q f)
    (L : Fin q → ℝ) (hL : ∀ a, 1 ≤ L a)
    (hlip : ∀ a y z,
      ‖iteratedFDeriv ℝ (HighOrderTrustRegion.modelOrder a) f y -
        iteratedFDeriv ℝ (HighOrderTrustRegion.modelOrder a) f z‖ ≤ L a * ‖y - z‖)
    (hk : k < N) :
    let κ := trqRadiusConstant f q P.order_pos (x 0) (Δ 0) P.theta P.eta2 P.gamma1
      (trqLipschitzConstant P L)
    κ ∈ Set.Ioo (0 : ℝ) 1 ∧ κ < P.gamma1 ∧
      min (P.gamma1 * P.theta) (κ * trqPrefixGap f P x Δ d j k) ≤ Δ k := by
  have hmax : 1 ≤ trqLipschitzConstant P L :=
    (hL ⟨0,P.order_pos⟩).trans (HighOrderTrustRegion.le_maxLipschitzConstant P L _)
  have hc := h.radiusConstant_pos_lt_gamma1 (by omega) hmax
  refine ⟨⟨hc.1, hc.2.trans (P.gamma1_le_gamma2.trans_lt P.gamma2_lt_one)⟩, hc.2, ?_⟩
  apply h.radius_lower hf hmax _ hk
  intro a y z
  exact (hlip a y z).trans (mul_le_mul_of_nonneg_right
    (HighOrderTrustRegion.le_maxLipschitzConstant P L a) (norm_nonneg _))

/-- **Lemma 12.2.4 (model and function decreases).** The model floor (12.2.18) holds
at every actual nonterminal trial, and every accepted trial attains (12.2.19).
The coefficient is an explicit function of the fixed initial data and parameters;
accuracies occur only as `ε_min^(q+1)`. Both statements use the actual Taylor model
and the actual objective values at the algorithm's successive iterates. -/
theorem lemma_12_2_4 {n q : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : trqParameters q}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {d : ℕ → Fin q → EuclideanSpace ℝ (Fin n)}
    {j : ℕ → Fin q} {Δ ρ : ℕ → ℝ} {N k : ℕ}
    (h : trqRun f P x s d j Δ ρ N) (hf : ContDiff ℝ q f)
    (L : Fin q → ℝ) (hL : ∀ a, 1 ≤ L a)
    (hlip : ∀ a y z,
      ‖iteratedFDeriv ℝ (HighOrderTrustRegion.modelOrder a) f y -
        iteratedFDeriv ℝ (HighOrderTrustRegion.modelOrder a) f z‖ ≤ L a * ‖y - z‖)
    (hk : k < N) :
    let κ := trqRadiusConstant f q P.order_pos (x 0) (Δ 0) P.theta P.eta2 P.gamma1
      (trqLipschitzConstant P L)
    (P.zeta * κ) ^ (q + 1) / q.factorial * trqMinimumAccuracy P ^ (q + 1) ≤
        taylorDecrement f (HighOrderTrustRegion.modelOrder (j k)) (x k) (s k) ∧
      (P.eta1 ≤ ρ k →
        P.eta1 * (P.zeta * κ) ^ (q + 1) / q.factorial * trqMinimumAccuracy P ^ (q + 1) ≤
          f (x k) - f (x (k + 1))) := by
  have hmax : 1 ≤ trqLipschitzConstant P L :=
    (hL ⟨0,P.order_pos⟩).trans (HighOrderTrustRegion.le_maxLipschitzConstant P L _)
  have hcommon : ∀ (a : Fin q) y z,
      ‖iteratedFDeriv ℝ (HighOrderTrustRegion.modelOrder a) f y -
        iteratedFDeriv ℝ (HighOrderTrustRegion.modelOrder a) f z‖ ≤
        trqLipschitzConstant P L * ‖y - z‖ := by
    intro a y z
    exact (hlip a y z).trans (mul_le_mul_of_nonneg_right
      (HighOrderTrustRegion.le_maxLipschitzConstant P L a) (norm_nonneg _))
  exact ⟨h.model_decrease hf hmax hcommon hk,
    fun hs => h.function_decrease hf hmax hcommon hk hs⟩

end CartisGouldToint

namespace CartisGouldToint

/-- The accuracy-independent settings of Algorithm 12.2.1. -/
abbrev trqSettings (q : ℕ) := HighOrderTrustRegion.Settings q

/-- The actual computed Step 1 stopping tests, before converting approximate model
maximization into a conclusion about the true Taylor criticality measures. -/
abbrev trqTestsPass {n q : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : trqParameters q)
    (x : EuclideanSpace ℝ (Fin n)) (Δ : ℝ) (d : Fin q → EuclideanSpace ℝ (Fin n)) : Prop :=
  HighOrderTrustRegion.TestsPass f P x Δ d

/-- Feasibility and the fractional actual Taylor-criticality approximation in Step 1. -/
abbrev trqCheckedOracle {n q : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : trqParameters q)
    (x : EuclideanSpace ℝ (Fin n)) (Δ : ℝ) (d : Fin q → EuclideanSpace ℝ (Fin n)) : Prop :=
  HighOrderTrustRegion.CheckedOracle f P x Δ d

/-- Objective calls: initialization plus one call at every trial. -/
abbrev trqFunctionEvaluations (N : ℕ) : ℕ := HighOrderTrustRegion.functionEvaluations N

/-- Calls of each derivative order: initialization plus accepted new iterates. -/
noncomputable abbrev trqDerivativeEvaluations {q : ℕ} (P : trqParameters q)
    (ρ : ℕ → ℝ) (N : ℕ) : ℕ :=
  HighOrderTrustRegion.derivativeEvaluations P ρ N

/-- The maximum reciprocal accuracy power appearing in the source complexity order. -/
noncomputable abbrev trqMaximumInverseAccuracy {q : ℕ} (P : trqParameters q) (p : ℕ) : ℝ :=
  HighOrderTrustRegion.maximumInverseAccuracy P p

/-- **Theorem 12.2.5 (arbitrary-order complexity of TRq).** Positive constants are
chosen before every admissible accuracy request and execution from the fixed initial
data. The actual algorithm reaches its first passed stopping test, with the objective
and derivative budgets (12.2.21)–(12.2.22), including initialization. Both counters
also have explicit uniform bounds by a constant times the maximum inverse accuracy
power, proving the stated complexity order. The returned radius
is in `(0,1]`, and every derivative order has its required true criticality bound.

For a fixed algorithmic cap `ϑ`, admissibility retains the source condition
`min ε ≤ ϑ`; taking `ϑ = 1` permits every accuracy in `(0,1]^q`. A uniformly positive
coefficient using `max(1,B₀)` covers even a vanishing initial derivative jet. The source's
final criticality display has an index typo: the measure in the `j`-th inequality is
`φ_{f,j}`, as in the stopping criterion, rather than `φ_{f,q}` for every `j`.
The consistent-prefix and checked-oracle premises are precisely the operational trial
and Step 1 approximation rules, with no termination or complexity field. -/
theorem theorem_12_2_5 {n q : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (S : trqSettings q) (x₀ : EuclideanSpace ℝ (Fin n))
    {Δ₀ : ℝ} (hΔ : 0 < Δ₀) (hΔmax : Δ₀ ≤ S.radiusMax)
    (hf : ContDiff ℝ q f) (L : Fin q → ℝ) (hL : ∀ a, 1 ≤ L a)
    (hlip : ∀ (a : Fin q) y z,
      ‖iteratedFDeriv ℝ (HighOrderTrustRegion.modelOrder a) f y -
        iteratedFDeriv ℝ (HighOrderTrustRegion.modelOrder a) f z‖ ≤ L a * ‖y - z‖)
    {flow : ℝ} (hlow : ∀ y, flow ≤ f y) :
    ∃ κS > 0, ∃ κA > 0, ∃ κB > 0, ∃ κC > 0,
      ∀ (ε : Fin q → ℝ) (hε : ∀ a, 0 < ε a) (hε1 : ∀ a, ε a ≤ 1)
        (hεθ : ∃ a, ε a ≤ S.theta),
      let P := S.withAccuracy ε hε hε1 hεθ
      ∀ (x s : ℕ → EuclideanSpace ℝ (Fin n))
        (d : ℕ → Fin q → EuclideanSpace ℝ (Fin n))
        (j : ℕ → Fin q) (Δ ρ : ℕ → ℝ), x 0 = x₀ → Δ 0 = Δ₀ →
      (∀ N, (∀ i < N, ¬trqTestsPass f P (x i) (Δ i) (d i)) → trqRun f P x s d j Δ ρ N) →
      (∀ k, trqTestsPass f P (x k) (Δ k) (d k) → trqCheckedOracle f P (x k) (Δ k) (d k)) →
      ∃ K, trqTestsPass f P (x K) (Δ K) (d K) ∧ trqRun f P x s d j Δ ρ K ∧
        (∀ i < K, ¬trqTestsPass f P (x i) (Δ i) (d i)) ∧
        HighOrderTrustRegion.optimalityRadius P (Δ K) ∈ Set.Ioc (0 : ℝ) 1 ∧
        (∀ a, TaylorModel.criticality f (HighOrderTrustRegion.modelOrder a) (x K)
          (HighOrderTrustRegion.optimalityRadius P (Δ K)) ≤
          ε a * HighOrderTrustRegion.optimalityRadius P (Δ K) ^
            HighOrderTrustRegion.modelOrder a /
            (HighOrderTrustRegion.modelOrder a).factorial) ∧
        (trqFunctionEvaluations K : ℝ) ≤
          κA * (f x₀ - flow) / trqMinimumAccuracy P ^ (q + 1) +
          κB * |Real.log (trqMinimumAccuracy P)| + κC ∧
        (trqDerivativeEvaluations P ρ K : ℝ) ≤
          κS * (f x₀ - flow) / trqMinimumAccuracy P ^ (q + 1) + 1 ∧
        (trqFunctionEvaluations K : ℝ) ≤
          (κA * (f x₀ - flow) + κB + κC) * trqMaximumInverseAccuracy P (q + 1) ∧
        (trqDerivativeEvaluations P ρ K : ℝ) ≤
          (κS * (f x₀ - flow) + 1) * trqMaximumInverseAccuracy P (q + 1) :=
  HighOrderTrustRegion.evaluation_complexity f S x₀ hΔ hΔmax hf L hL hlip hlow

end CartisGouldToint

namespace CartisGouldToint
open HighOrderTrustRegion HighOrderTrustRegion.Sharpness in
/-- **Theorem 12.2.6 (slow convergence of TRq).** Uniform regularity and objective
bounds are chosen before the accuracy. The globally `C^q` objective realizes a legal
run from zero with `ε_j=j!ε`, exactly `ceil(ε^(-(q+1)))` nonterminal trials, and one
additional initialized evaluation of the function and each derivative. Before the
last point, true approximate optimality fails at every positive radius. At the last
point all true tests hold with radius `ε∈(0,1]`.

The construction corrects the source's objective recurrence by making the actual
drop equal the model prediction, starts the objective at four, and uses `x_k=kε`.
The ceiling gives `ε^(q+1)K<2`; it does not give the printed upper bound by one.
Derivative residuals use the descending factorial coefficient and include the
highest-order change `q!ε/K`. Initialization retains the source's radius `Δ₀=ε`.
The same objective works for every legal acceptance/update parameter choice with
unit optimality cap and maximal radius at least one, including `γ₃=1` and every
allowed approximation fraction. -/
theorem theorem_12_2_6 {q : ℕ} (hq : 0 < q)
    (S : Settings q) (hθ : S.theta = 1) (hmax : 1 ≤ S.radiusMax) :
    ∃ L ≥ 1, ∃ B > 0, ∀ (ε : ℝ) (hε : 0 < ε) (hεq : ε ≤ 1 / (q.factorial : ℝ)),
      let P := settingsParameters S hθ ε hε hεq
      ∃ f : ℝ → ℝ, ContDiff ℝ q f ∧
        (∀ j ≤ q, ∀ y, |iteratedDeriv j f y| ≤ B) ∧
        (∀ j ≤ q, ∀ y z,
          ‖iteratedFDeriv ℝ j f y - iteratedFDeriv ℝ j f z‖ ≤ L * ‖y - z‖) ∧
        (∀ y, -B ≤ f y) ∧ f 0 = 4 ∧ f 0 - (-B) = 4 + B ∧
          Run f P (point ε) (fun _ => ε) (fun _ _ => direction q ε P.zeta)
            (fun _ => topIndex hq) (fun _ => ε) (fun _ => 1) (length q ε) ∧
          (∀ k ≤ length q ε, CheckedOracle f P (point ε k) ε
            (fun _ => direction q ε P.zeta)) ∧
          (∀ k < length q ε, ¬TestsPass f P (point ε k) ε
            (fun _ => direction q ε P.zeta)) ∧
          TestsPass f P (point ε (length q ε)) ε (fun _ => direction q ε P.zeta) ∧
          (∀ k < length q ε, ∀ δ > 0,
            ¬∀ a, TaylorModel.criticality f (modelOrder a) (point ε k) δ ≤
              P.accuracy a * δ ^ modelOrder a / (modelOrder a).factorial) ∧
          (ε ∈ Set.Ioc (0 : ℝ) 1) ∧
          (∀ a, TaylorModel.criticality f (modelOrder a) (point ε (length q ε)) ε ≤
            P.accuracy a * ε ^ modelOrder a / (modelOrder a).factorial) ∧
          functionEvaluations (length q ε) = length q ε + 1 ∧
          derivativeEvaluations P (fun _ => 1) (length q ε) = length q ε + 1 ∧
          1 / ε ^ (q + 1) ≤ (length q ε : ℝ) ∧
          1 / ε ^ (q + 1) < (functionEvaluations (length q ε) : ℝ) ∧
          1 / ε ^ (q + 1) < (derivativeEvaluations P (fun _ => 1) (length q ε) : ℝ) :=
  HighOrderTrustRegion.Sharpness.exists_slow_objective_for_settings hq S hθ hmax

end CartisGouldToint

namespace CartisGouldToint

/-- The actual fraction-of-global-model-gap rule (12.2.34) of Step2.
It is equivalent to the usual inequality with the actual attained minimum;
positive regularized finite models genuinely admit such steps. -/
abbrev arqpStepTwoSolve {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (σ μ : ℝ) (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  ModelDecrease.ApproximateGlobalStep (HighOrderRegularization.model f p x σ) μ s

/-- Lemma12.2.10: zero model decrease at an actual approximate-global Step2
return is impossible for orders one and two after a failed Step1 test. For
higher orders the returned objective point is a true approximate minimizer
at some vector of positive optimality radii. Only the finite regularity at
the model center is needed for this conditional result. -/
theorem lemma_12_2_10 {n p q : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x s : EuclideanSpace ℝ (Fin n)}
    (hqp : q ≤ p) (hf : ContDiffAt ℝ p f x) {σ μ : ℝ} (hμ : 0 < μ)
    (hsolve : arqpStepTwoSolve f p x σ μ s)
    (hzero : HighOrderRegularization.model f p x σ 0 =
      HighOrderRegularization.model f p x σ s)
    (ε δ₀ : Fin q → ℝ) (hε : ∀ a, 0 < ε a) (hδ₀ : ∀ a, 0 < δ₀ a)
    (direction : Fin q → EuclideanSpace ℝ (Fin n))
    (hfeasible : ∀ a, ‖direction a‖ ≤ δ₀ a) {ζ : ℝ} (hζ : 0 < ζ)
    (hfailed : ∃ a, ζ * ε a * δ₀ a ^ InexactTrustRegion.modelOrder a /
      (InexactTrustRegion.modelOrder a).factorial ≤
        TaylorModel.decrement f (InexactTrustRegion.modelOrder a) x (direction a)) :
    3 ≤ q ∧ ∃ δ : Fin q → ℝ, (∀ a, 0 < δ a ∧ δ a ≤ 1) ∧
      ∀ a, TaylorModel.criticality f (InexactTrustRegion.modelOrder a) x (δ a) ≤
        ε a * δ a ^ InexactTrustRegion.modelOrder a /
          (InexactTrustRegion.modelOrder a).factorial :=
  HighOrderRegularization.zero_step_termination hqp hf hμ hsolve hzero
    ε δ₀ hε hδ₀ direction hfeasible hζ hfailed

end CartisGouldToint

namespace CartisGouldToint

/-- A uniform quantitative version of the step-existence claim in Lemma12.2.9
with an existential radius coefficient. The coefficient precedes all centers,
penalty parameters below their fixed cap and accuracies. Actual global model
minimization and finite first-passing halving yield every test, including unit
radii for the first two orders. The exact printed coefficient is supplied
separately by Lemma12.2.9. At step norm exactly one the criticality tests are retained. -/
theorem lemma_12_2_9_uniform {n p q : ℕ} (hqp : q ≤ p)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) {L S : ℝ} (hL : 0 ≤ L) (hS : 0 ≤ S)
    (hlip : ∀ i, 1 ≤ i → i < p → ∀ y z,
      ‖iteratedFDeriv ℝ i f y - iteratedFDeriv ℝ i f z‖ ≤ L * ‖y - z‖) :
    ∃ κ > 0, κ ≤ 1 ∧ ∀ x : EuclideanSpace ℝ (Fin n),
      ∀ σ : ℝ, 0 < σ → σ ≤ S → ∀ θ ζ : ℝ,
      0 < θ → θ ≤ 1 → 0 < ζ → ζ ≤ 1 →
      ∀ ε : Fin q → ℝ, (∀ a, 0 < ε a ∧ ε a ≤ 1) →
      ∃ s : EuclideanSpace ℝ (Fin n),
        (∀ t, HighOrderRegularization.model f p x σ s ≤
          HighOrderRegularization.model f p x σ t) ∧
        (∀ μ : ℝ, 0 ≤ μ → μ ≤ 1 → arqpStepTwoSolve f p x σ μ s) ∧
        (1 < ‖s‖ ∨ ∃ (δ : Fin q → ℝ) (d : Fin q → EuclideanSpace ℝ (Fin n)),
          ∀ a, (0 < δ a ∧ δ a ≤ 1) ∧ κ * (ζ * θ * ε a) ≤ δ a ∧
            (InexactTrustRegion.modelOrder a ≤ 2 → δ a = 1) ∧ ‖d a‖ ≤ δ a ∧
            ζ * TaylorModel.criticality (HighOrderRegularization.model f p x σ)
              (InexactTrustRegion.modelOrder a) s (δ a) ≤
              TaylorModel.decrement (HighOrderRegularization.model f p x σ)
                (InexactTrustRegion.modelOrder a) s (d a) ∧
            TaylorModel.decrement (HighOrderRegularization.model f p x σ)
              (InexactTrustRegion.modelOrder a) s (d a) ≤
              ζ * θ * ε a * δ a ^ InexactTrustRegion.modelOrder a /
                (InexactTrustRegion.modelOrder a).factorial ∧
            TaylorModel.criticality (HighOrderRegularization.model f p x σ)
              (InexactTrustRegion.modelOrder a) s (δ a) ≤
              θ * ε a * δ a ^ InexactTrustRegion.modelOrder a /
                (InexactTrustRegion.modelOrder a).factorial) := by
  obtain ⟨κ, hκ, hκ1, hsolve⟩ :=
    ModelSolve.exists_uniform_regularized_critical_step
      (E := EuclideanSpace ℝ (Fin n)) (ι := Fin q) p hS hL
  refine ⟨κ, hκ, hκ1, ?_⟩
  intro x σ hσ hσS θ ζ hθ hθ1 hζ hζ1 ε hε
  have hA : ∀ i, 2 ≤ i → i ≤ p → ‖ftaylorSeries ℝ f x i‖ ≤ L := by
    intro i hi hip
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    change ‖iteratedFDeriv ℝ (j + 1) f x‖ ≤ L
    rw [← norm_fderiv_iteratedFDeriv]
    exact norm_fderiv_le_of_lip' ℝ hL
      (Filter.Eventually.of_forall (fun y => hlip j (by omega) (by omega) y x))
  have horder : ∀ a : Fin q, 0 < InexactTrustRegion.modelOrder a ∧
      InexactTrustRegion.modelOrder a ≤ p := by
    intro a
    unfold InexactTrustRegion.modelOrder
    constructor <;> omega
  exact hsolve σ hσ hσS (ftaylorSeries ℝ f x) hA θ ζ hθ hθ1 hζ hζ1
    InexactTrustRegion.modelOrder horder ε hε

end CartisGouldToint

namespace CartisGouldToint

/-- Lemma12.2.7: the actual regularized Taylor model is `C^p`, its highest
actual derivative is globally sigma-Lipschitz, and all derivatives of orders
2 through p have the printed unit-ball bound `3*L+sigma`. -/
theorem lemma_12_2_7 {n p : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) {L σ : ℝ} (hL : 1 ≤ L) (hσ : 0 ≤ σ)
    (hlip : ∀ i, 1 ≤ i → i < p → ∀ y z,
      ‖iteratedFDeriv ℝ i f y - iteratedFDeriv ℝ i f z‖ ≤ L * ‖y - z‖) :
    ContDiff ℝ p (HighOrderRegularization.model f p x σ) ∧
      (∀ u v, ‖iteratedFDeriv ℝ p (HighOrderRegularization.model f p x σ) u -
        iteratedFDeriv ℝ p (HighOrderRegularization.model f p x σ) v‖ ≤ σ * ‖u - v‖) ∧
      ∀ j, 2 ≤ j → j ≤ p → ∀ s, ‖s‖ ≤ 1 →
        ‖iteratedFDeriv ℝ j (HighOrderRegularization.model f p x σ) s‖ ≤ 3 * L + σ := by
  have hA : ∀ i, 2 ≤ i → i ≤ p → ‖ftaylorSeries ℝ f x i‖ ≤ L := by
    intro i hi hip
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    change ‖iteratedFDeriv ℝ (j + 1) f x‖ ≤ L
    rw [← norm_fderiv_iteratedFDeriv]
    exact norm_fderiv_le_of_lip' ℝ (zero_le_one.trans hL)
      (Filter.Eventually.of_forall (fun y => hlip j (by omega) (by omega) y x))
  refine ⟨ModelDecrease.contDiff_penalized_ofJet (ftaylorSeries ℝ f x) p p le_rfl σ,
    ModelDecrease.norm_sub_iteratedFDeriv_penalized_ofJet_le (ftaylorSeries ℝ f x) p hσ,
    ?_⟩
  intro j hj hjp s hs
  exact ModelDecrease.norm_iteratedFDeriv_penalized_ofJet_le_three_mul_add
    (ftaylorSeries ℝ f x) hjp hσ (zero_le_one.trans hL)
    (fun i hji hip => hA i (hj.trans hji) hip) hs

/-- Lemma12.2.8: every sufficiently small positive Taylor-model decrement
retains at least half its normalized value in the actual regularized model. -/
theorem lemma_12_2_8 {n p j : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x s d : EuclideanSpace ℝ (Fin n)) {L σ α δ : ℝ}
    (hL : 1 ≤ L) (hσ : 0 < σ) (hj : 0 < j) (hjp : j ≤ p)
    (hlip : ∀ i, 1 ≤ i → i < p → ∀ y z,
      ‖iteratedFDeriv ℝ i f y - iteratedFDeriv ℝ i f z‖ ≤ L * ‖y - z‖)
    (hs : ‖s‖ ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hd : ‖d‖ ≤ δ)
    (hsmall : δ ≤ α / (4 * (3 * L + σ)))
    (htest : α * δ ^ j / j.factorial ≤
      TaylorModel.decrement (HighOrderRegularization.model f p x σ) j s d) :
    α / 2 * δ ^ j / j.factorial ≤
      HighOrderRegularization.model f p x σ s -
        HighOrderRegularization.model f p x σ (s + d) := by
  obtain ⟨hf, htop, hbound⟩ := lemma_12_2_7 f x hL hσ.le hlip
  exact TaylorModel.value_decrement_ge_half_of_taylor_test hj hjp hf hσ.le
    (by linarith) (by linarith) htop s d hδ hδ1 hd hsmall
    (fun a hja hap => hbound a (by omega) hap s hs) htest

/-- Lemma12.2.9: a genuine global model minimum and finite criticality halving
supply an admissible step with the exact printed radius floor. All first- and
second-order radii equal one. A step of norm exactly one retains the criticality
checks, as required by the strict large-step alternative in the statement. -/
theorem lemma_12_2_9 {n p q : ℕ} (hqp : q ≤ p)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    {L σ θ ζ : ℝ} (hL : 1 ≤ L) (hσ : 0 < σ)
    (hlip : ∀ i, 1 ≤ i → i < p → ∀ y z,
      ‖iteratedFDeriv ℝ i f y - iteratedFDeriv ℝ i f z‖ ≤ L * ‖y - z‖)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (ε : Fin q → ℝ) (hε : ∀ a, 0 < ε a ∧ ε a ≤ 1) :
    ∃ (s : EuclideanSpace ℝ (Fin n)) (δ : Fin q → ℝ),
      (∀ t, HighOrderRegularization.model f p x σ s ≤
        HighOrderRegularization.model f p x σ t) ∧
      (∀ μ : ℝ, 0 ≤ μ → μ ≤ 1 → arqpStepTwoSolve f p x σ μ s) ∧
      (∀ a, 0 < δ a ∧ δ a ≤ 1) ∧
      (∀ a, InexactTrustRegion.modelOrder a ≤ 2 → δ a = 1) ∧
      (1 < ‖s‖ ∨ ∃ d : Fin q → EuclideanSpace ℝ (Fin n), ∀ a,
        ζ * θ / (8 * (3 * L + σ)) * ε a ≤ δ a ∧ ‖d a‖ ≤ δ a ∧
        ζ * TaylorModel.criticality (HighOrderRegularization.model f p x σ)
          (InexactTrustRegion.modelOrder a) s (δ a) ≤
          TaylorModel.decrement (HighOrderRegularization.model f p x σ)
            (InexactTrustRegion.modelOrder a) s (d a) ∧
        TaylorModel.decrement (HighOrderRegularization.model f p x σ)
          (InexactTrustRegion.modelOrder a) s (d a) ≤
          ζ * θ * ε a * δ a ^ InexactTrustRegion.modelOrder a /
            (InexactTrustRegion.modelOrder a).factorial ∧
        TaylorModel.criticality (HighOrderRegularization.model f p x σ)
          (InexactTrustRegion.modelOrder a) s (δ a) ≤
          θ * ε a * δ a ^ InexactTrustRegion.modelOrder a /
            (InexactTrustRegion.modelOrder a).factorial) := by
  have hA : ∀ i, 2 ≤ i → i ≤ p → ‖ftaylorSeries ℝ f x i‖ ≤ L := by
    intro i hi hip
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    change ‖iteratedFDeriv ℝ (j + 1) f x‖ ≤ L
    rw [← norm_fderiv_iteratedFDeriv]
    exact norm_fderiv_le_of_lip' ℝ (zero_le_one.trans hL)
      (Filter.Eventually.of_forall (fun y => hlip j (by omega) (by omega) y x))
  have horder : ∀ a : Fin q, 0 < InexactTrustRegion.modelOrder a ∧
      InexactTrustRegion.modelOrder a ≤ p := by
    intro a
    unfold InexactTrustRegion.modelOrder
    constructor <;> omega
  exact ModelSolve.exists_regularized_solve_sharp (ftaylorSeries ℝ f x) p hL hσ hA
    hθ hθ1 hζ hζ1 InexactTrustRegion.modelOrder horder ε hε

end CartisGouldToint

namespace CartisGouldToint

/-- Lemma12.2.11: a successful actual ARqp trial followed by failure of true
approximate optimality forces the printed weighted step/radius inequality.
The actual model test is needed only for steps of norm at most one. The
parameter cap is derived from the objective ratio and parameter updates. -/
theorem lemma_12_2_11 {n p q N i : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin L θ : ℝ}
    (h : arpModelTrace f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hqp : q ≤ p) (hf : ContDiff ℝ p f) (hL : 1 ≤ L) (hθ : 0 ≤ θ)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (hi : i < N) (hs : η₁ ≤ ρ i) (ε : Fin q → ℝ)
    (hε : ∀ a, 0 < ε a ∧ ε a ≤ 1) (δ δs : ℕ → Fin q → ℝ)
    (hδ : ∀ a, 0 < δ (i + 1) a ∧ δ (i + 1) a ≤ 1)
    (hupdate : δ (i + 1) = δs i)
    (htest : ‖s i‖ ≤ 1 → ∀ a,
      TaylorModel.criticality (arpModel f p (x i) (σ i))
        (InexactTrustRegion.modelOrder a) (s i) (δs i a) ≤
        θ * ε a * δs i a ^ InexactTrustRegion.modelOrder a /
          (InexactTrustRegion.modelOrder a).factorial)
    (hnot : ¬∀ a, TaylorModel.criticality f (InexactTrustRegion.modelOrder a)
      (x (i + 1)) (δ (i + 1) a) ≤ ε a * δ (i + 1) a ^ InexactTrustRegion.modelOrder a /
        (InexactTrustRegion.modelOrder a).factorial) :
    let σmax := max (σ 0) (γ₃ * L / (1 - η₂))
    ∃ a, (1 - θ) * ε a * δ (i + 1) a ^ InexactTrustRegion.modelOrder a /
        (InexactTrustRegion.modelOrder a).factorial ≤
      (L + σmax) * ∑ ℓ ∈ Finset.range (InexactTrustRegion.modelOrder a),
        δ (i + 1) a ^ (ℓ + 1) * ‖s i‖ ^ (p - (ℓ + 1) + 1) / (ℓ + 1).factorial := by
  have hx : x (i + 1) = x i + s i := by rw [h.point_update i hi, ite_eq_left hs]
  apply HighOrderRegularization.criticality_obstruction hqp f hf hL
    (h.updates.pos hi.le).le (h.parameter_le hf (zero_le_one.trans hL) hlip hi.le)
    hθ hlip (x i) (s i) ε (δ (i + 1)) hε hδ
  · simpa only [hupdate] using htest
  · simpa only [hx] using hnot

end CartisGouldToint

namespace CartisGouldToint

/-- Lemma12.2.12 with a safe common radius coefficient. Taking the minimum
of the actual solver floor and the normalized order-q obstruction coefficient
repairs the scalar comparison when the step is shorter than its radius.
Both source accuracy exponents are retained. The original fixed-coefficient
statement remains a separate open target. -/
theorem lemma_12_2_12_corrected {n p q N i : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin L θ : ℝ}
    (h : arpModelTrace f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hqp : q ≤ p) (hf : ContDiff ℝ p f) (hL : 1 ≤ L)
    (hθ : 0 < θ) (hθ1 : θ < 1) {ζ D : ℝ}
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hD : 1 ≤ D)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (hi : i < N) (hs : η₁ ≤ ρ i) (ε : Fin q → ℝ)
    (hε : ∀ a, 0 < ε a ∧ ε a ≤ 1) (δ δs : ℕ → Fin q → ℝ)
    (hδ : ∀ a, 0 < δ (i + 1) a ∧ δ (i + 1) a ≤ 1)
    (hupdate : δ (i + 1) = δs i)
    (htest : ‖s i‖ ≤ 1 → ∀ a,
      TaylorModel.criticality (arpModel f p (x i) (σ i))
        (InexactTrustRegion.modelOrder a) (s i) (δs i a) ≤
        θ * ε a * δs i a ^ InexactTrustRegion.modelOrder a /
          (InexactTrustRegion.modelOrder a).factorial)
    (hnot : ¬∀ a, TaylorModel.criticality f (InexactTrustRegion.modelOrder a)
      (x (i + 1)) (δ (i + 1) a) ≤ ε a * δ (i + 1) a ^ InexactTrustRegion.modelOrder a /
        (InexactTrustRegion.modelOrder a).factorial)
    (hunit : ∀ a, InexactTrustRegion.modelOrder a ≤ 2 → δ (i + 1) a = 1)
    (hfloor : ‖s i‖ ≤ 1 → ∀ a,
      ζ * θ / (8 * (3 * D + max (σ 0) (γ₃ * L / (1 - η₂)))) * ε a ≤ δ (i + 1) a) :
    let σmax := max (σ 0) (γ₃ * L / (1 - η₂))
    let κ := HighOrderStep.regularizationRadiusCoefficient ζ θ D L σmax q
    0 < κ ∧ κ ≤ 1 ∧ ∃ a,
      (if q ≤ 2 then
        (HighOrderStep.criticalityCoefficient θ (L + σmax)
          (InexactTrustRegion.modelOrder a)) ^
            (1 / ((p - InexactTrustRegion.modelOrder a + 1 : ℕ) : ℝ)) *
          (ε a) ^ (1 / ((p - InexactTrustRegion.modelOrder a + 1 : ℕ) : ℝ))
      else
        (HighOrderStep.criticalityCoefficient θ (L + σmax)
          (InexactTrustRegion.modelOrder a) * κ ^ (InexactTrustRegion.modelOrder a - 1)) ^
            (1 / (p : ℝ)) * (ε a) ^ ((InexactTrustRegion.modelOrder a : ℝ) / p)) ≤
          ‖s i‖ := by
  let S := max (σ 0) (γ₃ * L / (1 - η₂))
  let κ := HighOrderStep.regularizationRadiusCoefficient ζ θ D L S q
  have hcap := h.parameter_le hf (zero_le_one.trans hL) hlip hi.le
  have hS : 0 ≤ S := (h.updates.pos hi.le).le.trans hcap
  have hκ := HighOrderStep.regularizationRadiusCoefficient_mem hζ hζ1 hθ hθ1 hD hL hS q
  obtain ⟨a, ha⟩ := lemma_12_2_11 h hqp hf hL hθ.le hlip hi hs ε hε δ δs
    hδ hupdate htest hnot
  refine ⟨hκ.1, hκ.2, a, ?_⟩
  apply HighOrderStep.lower_of_obstruction (by unfold InexactTrustRegion.modelOrder; omega)
    (by unfold InexactTrustRegion.modelOrder; omega) hqp hθ hθ1
    (by linarith : 1 ≤ L + S) hκ.1.le hκ.2 (min_le_right _ _)
    (hε a).1.le (hε a).2 (hδ a).1 (norm_nonneg _) ?_ ?_ ha
  · intro hq2
    exact hunit a (by unfold InexactTrustRegion.modelOrder; omega)
  · intro hshort
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (hε a).1.le).trans (hfloor hshort a)

end CartisGouldToint
