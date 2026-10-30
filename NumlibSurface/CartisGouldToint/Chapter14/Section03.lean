import Numlib.Analysis.Calculus.AnchoredLipschitz
import Numlib.Analysis.InnerProductSpace.EuclideanProd
import Numlib.Optimization.Complexity.ScaledRestart
import Numlib.Optimization.Constrained.TwoPhase
import Numlib.Optimization.Optimality.CurveConditions
import NumlibSurface.CartisGouldToint.Chapter07.Section02
import NumlibSurface.CartisGouldToint.Chapter14.Section02
import Numlib.Optimization.ModelBased.HighOrder.ARqpCCall
import Numlib.Optimization.Constrained.TargetMeritTaylor
import Numlib.Analysis.Calculus.MultivariateTaylor.Coord
import Numlib.Optimization.Complexity.SlowExample.TRq
import Numlib.Optimization.Constrained.TwoPhase.HighOrder.Examples.Interval
import Numlib.Optimization.Constrained.TwoPhase.HighOrder.Examples.Drift
import Numlib.Optimization.Constrained.TwoPhase.HighOrder.Examples.BoxBadIter
import Numlib.Optimization.Constrained.TwoPhase.HighOrder.Examples.BoxARqp
import Numlib.Optimization.Constrained.TwoPhase.HighOrder.Examples.Rectangle
import Numlib.Optimization.Constrained.TwoPhase.HighOrder.Examples.SlowDecayTwoPhase
import Numlib.Optimization.Constrained.TwoPhase.HighOrder.TRqCalls
import Numlib.Optimization.Constrained.TwoPhase.HighOrder.ARqpCalls
import Numlib.Optimization.Constrained.TwoPhase.HighOrder.OrderBounds

/-!
# Cartis–Gould–Toint §14.3: High-order criticality for nonconvex constraints

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §14.3: the problem
`min_{x ∈ X} f(x)` subject to `c(x) = 0` (14.3.1), with a closed set `X ⊆ ℝⁿ` of simple
constraints and `c : ℝⁿ → ℝᵐ`; curve-based necessary conditions (§14.3.1), the least-norm method
LENq-SC (Algorithm 14.3.1) and the two-phase method TPqp-GC (Algorithm 14.3.2) with their
evaluation complexity (§14.3.2).

## Notation and backbone

The Lagrangian is `ℒ(x, y) = f(x) - ⟪y, c(x)⟫`, `Constrained.innerLagrangian f c y`. The Phase-2
residual `r(x, t) = (c(x), f(x) - t)` and merit `μ(x, t) = ½ ‖r(x, t)‖²` (14.3.30) are
`Constrained.targetResidual`, `Constrained.targetMerit`; `ν = ½ ‖c‖²` and `Φ₂ = ½ ‖r‖²` are
`phi2 c`, `phi2 r`. Phase 2 of TPqp-GC is the backbone high-order target-following run
(`Numlib.Optimization.Constrained.TwoPhase.HighOrder.*`): `TPqpSeq`, `IsTPqpGCPhase2`, `meritCrit`
(14.3.34) are abbreviations of `Constrained.HighOrderTargetSeq`, `Constrained.IsHighOrderTargetRun`
and `Constrained.targetCrit`. The INNER contracts `IsInnerPhaseRun` and `IsInnerPhaseRunStrong` are
the backbone merit-decrease contracts `HighOrderTargetSeq.IsEndCritContract` and
`HighOrderTargetSeq.IsInnerTestContract`, which yield contracts of the generic outer loop
(`Constrained.TargetFollowingSeq.IsInnerContract`) through `IsMeritContract.toContract`; INNER's
certificate on the case-(b) calls is `HighOrderTargetSeq.IsCertified`. The complexity
arguments (counting, the target-drop margin bounding the case-(b) iterations, order bounds) are
backbone theorems on these structures. INNER of trust-region type uses the backbone TRq-call
analysis `Numlib.Optimization.ModelBased.HighOrder.TRqCall`; INNER = ARqp-SC is realized as
ARqpC-SC (`algorithm_14_1_1`) with `c = 0`, `h = 0`, whose calls (`IsARqpSCOutputCost`,
`IsARqpSCCallOut`), costs and contracts are the backbone
`Numlib.Optimization.ModelBased.HighOrder.ARqpCCall` (`Optimization.IsARqpOutputCost`,
`Optimization.IsARqpCallOut`, `Optimization.IsARqpCallOut.contract`) with `c = 0 : ℝⁿ → ℝ⁰`.
Phase-2 runs whose calls are TRq or ARqp calls (`IsTRqSCPhase2Calls`, `IsARqpSCPhase2Calls`,
`IsARqpUnitPhase2Calls`) are the backbone `Constrained.HighOrderTargetSeq.IsTRqCalls`,
`IsARqpCalls`, `IsARqpUnitCalls`, with their contracts and existence results in
`Numlib.Optimization.Constrained.TwoPhase.HighOrder.TRqCalls` and `…ARqpCalls`. The runs used to
refute printed statements are backbone examples
(`Numlib.Optimization.Constrained.TwoPhase.HighOrder.Examples.*`:
`Constrained.TwoPhaseExample.Interval`, `Drift`, `BoxBadIter`, `BoxARqp`, `Rectangle`,
`SlowDecay`); this file instantiates them.

## Book items

* §14.3.1: X.CQ (`AssumptionXCQ`), `theorem_14_3_1` (corrected), `theorem_14_3_2`,
  `example_14_3_1` (corrected).
* §14.3.2.1: LENq-SC (`algorithm_14_3_1`), the INNER cost bound (14.3.20)–(14.3.21)
  (`innerEvalBound`), `theorem_14_3_3`, `theorem_14_3_4` (and `theorem_14_3_4_add`, additive
  per-call constants); runs exist with INNER = ARqp-SC (`exists_algorithm_14_3_1`).
* §14.3.2.2: f.D1pLB.X, c.D1pLB.X (`AssumptionD1pLBX`, `AssumptionCD1pLBX`), TPqp-GC
  (`algorithm_14_3_2`), `lemma_14_3_5`, `lemma_14_3_6_i`, `lemma_14_3_6_ii`, `lemma_14_3_7`
  (and `lemma_14_3_7_add`), `lemma_14_3_8`, `theorem_14_3_9` (corrected, for an abstract INNER
  satisfying the contract of Lemma 14.2.2); runs exist with INNER = ARqp-SC
  (`exists_algorithm_14_3_2`, `exists_isTPqpGCARqpSCRun`), with ARqp on `ℝⁿ` with unit radii
  (`exists_isTPqpGCARqpUnitRun`) and with TRq-SC (`exists_isTPqpGCTRqSCRun`).
* Theorem 14.3.9 for runs whose INNER calls are runs of a given method: ARqp-SC with the
  exponents `j + 1` (`theorem_14_3_9_arqpc`) and `j(p+1)/p` (`theorem_14_3_9_arqp`, `q = p`;
  `theorem_14_3_9_arqp_corrected`, every `q`), ARqp with unit radii on `ℝⁿ`
  (`theorem_14_3_9_arqp_unit`, `theorem_14_3_9_arqp_unit_corrected`), TRq-SC
  (`theorem_14_3_9_trq`, `theorem_14_3_9_trq_one`).

## Deviations from the book

* **Theorem 14.3.1** is false as printed: with arcs that only stay in `X`, `X = ℝ²`,
  `c(x) = x₁² + x₂²`, `f(x) = -x₁`, `x⋆ = 0` violate (14.3.4) for `s₁ = e₁`; the arcs must stay in
  `X ∩ {c = 0}`, and X.CQ is then not needed (`theorem_14_3_1`).
* Example 14.3.1: the multiplier is `y₀ = (-1, 0)` and the origin is a minimizer, not a saddle
  point (`example_14_3_1`).
* Theorem 14.3.2: "neighbourhood of diameter `δ_j`" is the closed ball of radius `δ_j`.
  Theorem 14.3.3: the iteration bound needs a ceiling.
* **Theorem 14.3.4**, Lemma 14.3.7, Theorem 14.3.9: the proofs use `∑_k max_j ≤ max_j ∑_k`; the
  bounds hold with `∑_j` for `max_j` (`theorem_14_3_4`, `lemma_14_3_7`).
* **(14.3.20)–(14.3.21)**: the multiplicative cost contract fails for INNER = ARqp-SC with
  `q = 1`, `p ≥ 2` (`π_1 = (p+1)/p < 2`: a LENq-SC call from a point with small residual costs one
  evaluation against a bound tending to `0`; the same argument applies to any INNER spending at
  least one evaluation per call when every `π_j < 2`;
  `exists_algorithm_14_3_1_cost_contract_counterexample`). It holds for ARqp-SC with the ARqpC-SC
  exponents `j + 1` (`IsARqpSCOutputCost.cost_le_anchored`) and, for LENq-SC calls, with the
  ARqp-SC exponents when `q ≥ 2` (`IsARqpSCOutputCost.cost_le_arqp_anchored`,
  `IsARqpSCOutputCost.cost_le_arqp_lenq`). The additive form with the constants of
  Theorem 14.2.4 holds in all cases and is used (`IsARqpSCOutputCost.cost_le_arqp_add_anchored`,
  `theorem_14_3_4_add`).
* **Lemma 14.3.5**: (14.3.43) and (14.3.46) are false (`lemma_14_3_5_counterexample`); they are
  replaced by terms `(‖∇f‖δ)²/(2(f(x_ε) - t_ε))`, and when `f(x_ε) = t_ε` only the first-order part
  of (14.3.41) follows (`lemma_14_3_5`). Lemma 14.3.6: (14.3.63) bounds `∇^j μ`, not `∇^j ν`.
* **Lemma 14.3.8**: its proof does not bound the "bad" outer iterations (case (b), INNER call
  ending right after its only successful step); the decreases it uses allow Phase-2 sequences that
  never terminate (`lemma_14_3_8_proof_gap_counterexample`). `lemma_14_3_8` counts them
  separately.
* Proof of Lemma 14.3.8, after (B.14.21): the book bounds `‖r(x_{j,s}, t_j)‖^{π_l-1}` below by
  `ε₀^{π_l-1}`, while (B.14.20) only gives `(θε₀)^{π_l-1}`. The constant
  `κ^S = κ_decr⁻¹ (βθ)^{-π_max}` of (14.3.71) is still right: the INNER tolerance
  `β ‖r(x_{j,0}, t_j)‖ ε_l` of (B.14.21) is at least `βθε₀ε_l`, and the residuals are at most `ε₀`
  (`Constrained.IsHighOrderTargetRun.residual_drop`, `lemma_14_3_8`).
* **Theorem 14.3.9** is stated for INNER satisfying Lemma 14.2.2 as stated (decrease unless
  INNER's own test (14.3.19) holds) with radii `ρ` bounded below; Phase 2 then terminates, with an
  extra term `O(ε₀^{-1} + max_j (ε₀ ε_j ρ_j^{j-1})^{-1})`; the Phase-1 cost contract is additive;
  see the fixes listed at `theorem_14_3_9`. As printed, under the per-call reading of its INNER
  hypotheses it is false for a nonspecific INNER (`theorem_14_3_9_false`, `q = 1`,
  `π₁ ∈ [4/3, 3/2]`); under the uniform reading it is vacuous for `π₁ < 2`
  (`theorem_14_3_9_cost_hypothesis_unsatisfiable`).
* Theorem 14.3.9 with INNER = ARqp-SC (exponents `j(p+1)/p`): the extra term is outside the
  printed order for `q < p` (`exists_tpqpOrderF_lt_arqp`); for `q = 1`, `p ≥ 4` and `q = 2`,
  `p ≥ 5` runs that re-initialise `μ` at Step 2.1 of Algorithm 14.1.2 attain it, so the printed
  theorem fails for them (`theorem_14_3_9_arqp_counterexample`,
  `theorem_14_3_9_arqp_printed_false`).
* Theorem 14.3.9 with INNER = TRq-SC holds with `π_j = q + 1` and a factor `1 + |log(ε₀ ε_min)|`
  (`theorem_14_3_9_trq`), which is needed for `q = 1` (`theorem_14_3_9_trq_log_necessary`); the
  printed order fails for every `q ≥ 2` (`theorem_14_3_9_trq_printed_false`,
  `theorem_14_3_9_trq_printed_false_phase2`), and the TRq-SC row `j + 1` of (14.2.12) fails per
  iteration for `q = 2` (`lemma_14_2_2_trq_printed_false_uniform`).
* Algorithm 14.3.2: the INNER calls of Phase 2 are described by their iterates; `μ(·, t_k)` does
  not increase along a call, and a call stops as soon as `‖r‖ < θε₀`. With INNER = ARqp-SC the
  radii returned at a Step-2 termination may be `min(1, ε_j/(4(3 J + σ)))` instead of the book's
  `δ_{s_k}`, which need not certify (14.3.19) (`IsARqpSCCallOut`).
* The book's f.D1qLB.Fb (trust-region case) is not defined; f.D1qLB.X is used.

## Not formalized

The `O(·)` restatements (the bounds are stated with constants chosen before `ε`). Theorem 14.3.9
with INNER = ARqp-SC in the printed order for `q = 1 < p ≤ 3`, `q = 2 < p ≤ 4` and `3 ≤ q < p`, for
runs whose `μ` at Step 2.1 is bounded below, and with unit radii for `q < p`; with INNER = TRq-SC,
whether the logarithmic factor is needed for `q ≥ 2`; TRqIDA-SC and TRqEDA-SC as INNER.
-/

open Set Metric
open scoped Nat RealInnerProductSpace ContDiff Topology
open Constrained (innerLagrangian)

namespace CartisGouldToint.Chapter14

variable {n m : ℕ}

set_option hygiene false in
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

set_option hygiene false in
local notation "ℝᵐ" => EuclideanSpace ℝ (Fin m)

/-! ## §14.3.1 Necessary conditions -/

/-- **Assumption X.CQ** of [cartis2022evaluation], §14.3.1, at `x⋆ ∈ X` for orders `j ≤ q`, as
printed: for each `j ∈ [1 : q]` some nonzero tuple `(s_1, …, s_j)` belongs to the descriptor set
`𝒟^j_X` (an arc `x⋆ + ∑ α^i s_i + o(α^j)` stays in `X`) and satisfies (14.3.3) for `c`. It is not
needed for the (corrected) Theorem 14.3.1. -/
def AssumptionXCQ (X : Set ℝⁿ) (c : ℝⁿ → ℝᵐ) (xs : ℝⁿ) (q : ℕ) : Prop :=
  ∀ j ∈ Finset.Icc 1 q, ∃ s : ℕ → ℝⁿ, (∃ i ∈ Finset.Icc 1 j, s i ≠ 0) ∧
    Optimization.IsFeasibleArc X xs j s ∧
    ∀ i ∈ Finset.Icc 1 j, Optimization.curveCoeff (ftaylorSeries ℝ c xs) s i = 0

/-- **Theorem 14.3.1** of [cartis2022evaluation] (curve-based necessary conditions for a
constrained minimum), **corrected**. Let `f` and `c` be `C^q` on an open set containing `X`, and
let `x⋆` be a local minimizer of (14.3.1): a feasible point (`x⋆ ∈ X`, `c(x⋆) = 0`) minimizing `f`
locally on `X ∩ {c = 0}`. Then `c(x⋆) = 0` and, for every multiplier `y⋆`, every `j ∈ [1 : q]` and
every tuple `s` admitting an arc `x⋆ + ∑_{i ≤ j} α^i s_i + o(α^j)` that stays in `X ∩ {c = 0}`:
the expansion conditions (14.3.3) hold, and if the Lagrangian coefficients of orders `1, …, j-1`
vanish (14.3.5), the coefficient of order `j` is nonnegative (14.3.4). The coefficients are
`Optimization.curveCoeff`, the book's `∑_k 1/k! ∑_{P(j,k)} ∇^k[s_{ℓ₁}, …, s_{ℓ_k}]`.
(As printed, with arcs that are only `X`-feasible, the theorem is false; see the module
documentation.) -/
theorem theorem_14_3_1 {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {q : ℕ} {xs : ℝⁿ}
    (hsmooth : ∃ U, IsOpen U ∧ X ⊆ U ∧ ContDiffOn ℝ q f U ∧ ContDiffOn ℝ q c U)
    (hfeas : xs ∈ X ∩ {x | c x = 0}) (hmin : IsLocalMinOn f (X ∩ {x | c x = 0}) xs) :
    c xs = 0 ∧ ∀ (ys : ℝᵐ), ∀ j ∈ Finset.Icc 1 q, ∀ s : ℕ → ℝⁿ,
      Optimization.IsFeasibleArc (X ∩ {x | c x = 0}) xs j s →
        (∀ i ∈ Finset.Icc 1 j, Optimization.curveCoeff (ftaylorSeries ℝ c xs) s i = 0) ∧
        ((∀ i ∈ Finset.Ico 1 j,
            Optimization.curveCoeff (ftaylorSeries ℝ (innerLagrangian f c ys) xs) s i = 0) →
          0 ≤ Optimization.curveCoeff (ftaylorSeries ℝ (innerLagrangian f c ys) xs) s j) := by
  obtain ⟨U, hU, hXU, hfU, hcU⟩ := hsmooth
  have hxU : xs ∈ U := hXU hfeas.1
  have hf : ContDiffAt ℝ q f xs := hfU.contDiffAt (hU.mem_nhds hxU)
  have hc : ContDiffAt ℝ q c xs := hcU.contDiffAt (hU.mem_nhds hxU)
  refine ⟨hfeas.2, fun ys j hj s harc => ⟨?_, fun hzero => ?_⟩⟩
  · have hjq : (j : WithTop ℕ∞) ≤ q := by exact_mod_cast (Finset.mem_Icc.1 hj).2
    exact Optimization.curveCoeff_eq_zero_of_isFeasibleArc (hc.of_le hjq) harc
  · exact Optimization.curveCoeff_lagrangian_nonneg_of_isLocalMinOn hf hc hfeas.2 hmin ys hj harc
      hzero

/-! ### Theorem 14.3.2 -/

/-- **Theorem 14.3.2** of [cartis2022evaluation] (local sufficiency of the Lagrangian for
approximate minimizers). Let `f` and `c` be `C^j` near `x_ε` with `∇^j f`, `∇^j c` Lipschitz with
constants `L_f, L_c ≥ 0` on the closed ball of radius `δ` around `x_ε`, `V` a set of feasible
displacements, `‖c(x_ε)‖ ≤ ε₀` (14.3.8), and
`φ^δ_{ℒ,V,j}(x_ε, y_ε) ≤ ε ‖(1, y_ε)‖ δ^j/j! + η` (14.3.9), `‖(1, y)‖ = √(1 + ‖y‖²)`. Then for
every `d ∈ V` with `‖d‖ ≤ δ`, `‖c(x_ε + d)‖ ≤ ε₀` and `√2 max(L_f, L_c) ‖d‖ ≤ (j+1) ε` (14.3.11):
(14.3.10) `f(x_ε + d) ≥ f(x_ε) - 2ε₀‖y_ε‖ - 2ε‖(1, y_ε)‖ δ^j/j! - η`; and (14.3.12) the term
`2ε₀‖y_ε‖` can be dropped if `c(x_ε + d) = c(x_ε)`, or if `c(x_ε + d) = 0` and
`⟪y_ε, c(x_ε)⟫ ≤ 0`. -/
theorem theorem_14_3_2 {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {xε : ℝⁿ} {yε : ℝᵐ} {V : Set ℝⁿ} {j : ℕ}
    {δ ε η ε₀ Lf Lc : ℝ} (hf : ∀ z ∈ closedBall xε δ, ContDiffAt ℝ j f z)
    (hc : ∀ z ∈ closedBall xε δ, ContDiffAt ℝ j c z)
    (hLf : IteratedFDerivLipschitzOn f j Lf (closedBall xε δ))
    (hLc : IteratedFDerivLipschitzOn c j Lc (closedBall xε δ)) (hLf0 : 0 ≤ Lf) (hLc0 : 0 ≤ Lc)
    (hcx : ‖c xε‖ ≤ ε₀)
    (hφ : Optimization.taylorMeasure (ftaylorSeries ℝ (innerLagrangian f c yε) xε) j δ V ≤
      ε * √(1 + ‖yε‖ ^ 2) * δ ^ j / j ! + η)
    {d : ℝⁿ} (hdV : d ∈ V) (hd : ‖d‖ ≤ δ)
    (hLd : √2 * max Lf Lc * ‖d‖ ≤ (j + 1) * ε) :
    (‖c (xε + d)‖ ≤ ε₀ →
      f xε - 2 * ε₀ * ‖yε‖ - 2 * ε * √(1 + ‖yε‖ ^ 2) * δ ^ j / (j ! : ℝ) - η ≤ f (xε + d)) ∧
    (c (xε + d) = c xε ∨ (c (xε + d) = 0 ∧ ⟪yε, c xε⟫ ≤ 0) →
      f xε - 2 * ε * √(1 + ‖yε‖ ^ 2) * δ ^ j / (j ! : ℝ) - η ≤ f (xε + d)) := by
  refine ⟨fun hcd => Optimization.le_of_lagrangian_taylorMeasure_le hf hc hLf hLc hLf0 hLc0 hcx
    hφ hdV hd hcd hLd, ?_⟩
  rintro (heq | ⟨h0, hy⟩)
  · exact Optimization.le_of_lagrangian_taylorMeasure_le_of_eq hf hc hLf hLc hLf0 hLc0 hφ hdV hd
      heq hLd
  · exact Optimization.le_of_lagrangian_taylorMeasure_le_of_eq_zero hf hc hLf hLc hLf0 hLc0 hφ hdV
      hd h0 hy hLd

/-! ### Example 14.3.1 -/

section Example1431

/-- The objective `f(x) = x₁ + x₂² + x₂³ - x₃` of Example 14.3.1 (coordinates `x 0, x 1, x 2`). -/
noncomputable def example1431F : EuclideanSpace ℝ (Fin 3) → ℝ :=
  fun x => x 0 + x 1 ^ 2 + x 1 ^ 3 - x 2
/-- The constraints `c(x) = (-x₁ - x₂² + x₁x₂ + x₃, x₁ + x₂² + x₁x₂ + x₃)` of Example 14.3.1. -/
noncomputable def example1431C : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 2) := fun x =>
  !₂[-x 0 - x 1 ^ 2 + x 0 * x 1 + x 2, x 0 + x 1 ^ 2 + x 0 * x 1 + x 2]
/-- The tuple `s₁ = e₂`, `s₂ = -e₁`, `s₃ = e₃` of Example 14.3.1. -/
noncomputable def example1431Arc : ℕ → EuclideanSpace ℝ (Fin 3) := fun ℓ =>
  if ℓ = 1 then !₂[0, 1, 0] else if ℓ = 2 then !₂[-1, 0, 0] else if ℓ = 3 then !₂[0, 0, 1]
  else 0

/-- The polynomial arc of Example 14.3.1 is `α ↦ (-α², α, α³)`. -/
theorem example1431_arc_eq (α : ℝ) :
    (0 : EuclideanSpace ℝ (Fin 3)) + ∑ ℓ ∈ Finset.Icc 1 3, α ^ ℓ • example1431Arc ℓ =
      !₂[-α ^ 2, α, α ^ 3] := by
  rw [show (Finset.Icc 1 3 : Finset ℕ) = {1, 2, 3} by decide]
  ext i; fin_cases i <;> simp [example1431Arc]

/-- The feasible set of Example 14.3.1 is the curve `{(-t², t, t³)}`. -/
theorem example1431C_eq_zero_iff (x : EuclideanSpace ℝ (Fin 3)) :
    example1431C x = 0 ↔ ∃ t : ℝ, x = !₂[-t ^ 2, t, t ^ 3] := by
  constructor
  · intro h
    have h0 : -x 0 - x 1 ^ 2 + x 0 * x 1 + x 2 = 0 := by
      simpa [example1431C] using congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) h
    have h1 : x 0 + x 1 ^ 2 + x 0 * x 1 + x 2 = 0 := by
      simpa [example1431C] using congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) h
    refine ⟨x 1, ?_⟩
    have e0 : x 0 = -x 1 ^ 2 := by linarith
    have e2 : x 2 = x 1 ^ 3 := by rw [e0] at h1; nlinarith
    ext i; fin_cases i <;> simp [e0, e2]
  · rintro ⟨t, rfl⟩
    ext i; fin_cases i <;> simp [example1431C] <;> ring


/-- With `y₀ = (-1, 0)`, the Lagrangian `f - ⟪y₀, c⟫` of Example 14.3.1 is `x₂³ + x₁x₂`. -/
theorem example1431_lagrangian_eq :
    innerLagrangian example1431F example1431C (!₂[-1, 0]) = fun x => x 1 ^ 3 + x 0 * x 1 := by
  funext x
  simp [Constrained.innerLagrangian_apply, example1431F, example1431C,
    EuclideanSpace.inner_eq_star_dotProduct,
    Fin.sum_univ_two, dotProduct]
  ring

/-- Polarization for a symmetric bilinear form on `Fin 2`-tuples. -/
private theorem bilin_polar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ)
    (hA : ∀ u v : E, A ![u, v] = A ![v, u]) (u v : E) :
    A ![u, v] = (A (fun _ => u + v) - A (fun _ => u) - A (fun _ => v)) / 2 := by
  have hl : ∀ a b c : E, A ![a + b, c] = A ![a, c] + A ![b, c] := fun a b c => by
    have := A.map_update_add ![a, c] 0 a b
    have e : ∀ y : E, Function.update ![a, c] 0 y = ![y, c] := fun y => by
      funext i; fin_cases i <;> rfl
    rwa [e, e, e] at this
  have hr : ∀ a b c : E, A ![c, a + b] = A ![c, a] + A ![c, b] := fun a b c => by
    have := A.map_update_add ![c, a] 1 a b
    have e : ∀ y : E, Function.update ![c, a] 1 y = ![c, y] := fun y => by
      funext i; fin_cases i <;> rfl
    rwa [e, e, e] at this
  have hd : ∀ w : E, A (fun _ => w) = A ![w, w] := fun w => by
    congr 1; funext i; fin_cases i <;> rfl
  rw [hd, hd, hd, hl, hr, hr, hA v u]
  ring

/-- The mixed second and the third derivative of the Lagrangian in Example 14.3.1:
`∇²ℒ(0, y₀)[s₁, s₂] = -1` and `(1/6) ∇³ℒ(0, y₀)[s₁]³ = 1`, so (14.3.6) holds with both terms
nonzero. -/
theorem example1431_derivs :
    iteratedFDeriv ℝ 2 (innerLagrangian example1431F example1431C (!₂[-1, 0])) 0
        ![example1431Arc 1, example1431Arc 2] = -1 ∧
      (1 / 6 : ℝ) * iteratedFDeriv ℝ 3
        (innerLagrangian example1431F example1431C (!₂[-1, 0])) 0
        (fun _ => example1431Arc 1) = 1 := by
  rw [example1431_lagrangian_eq]
  set g : EuclideanSpace ℝ (Fin 3) → ℝ := fun x => x 1 ^ 3 + x 0 * x 1
  have hcoord : ∀ i : Fin 3, ContDiff ℝ ⊤ (fun x : EuclideanSpace ℝ (Fin 3) => x i) :=
    fun i => contDiff_piLp_apply (p := 2)
  have hg : ContDiff ℝ ⊤ g := ((hcoord 1).pow 3).add ((hcoord 0).mul (hcoord 1))
  have hdiag : ∀ (d : EuclideanSpace ℝ (Fin 3)), ∀ i ∈ Finset.Icc 1 3,
      iteratedFDeriv ℝ i g 0 (fun _ => d) =
        (Nat.factorial i : ℝ) * (if i = 1 then 0 else if i = 2 then d 0 * d 1 else d 1 ^ 3) := by
    intro d
    refine Optimization.iteratedFDeriv_apply_diag_eq_of_poly (N := 3)
      (hg.contDiffAt.of_le le_top) (Filter.Eventually.of_forall fun t => ?_)
    rw [show (Finset.Icc 1 3 : Finset ℕ) = {1, 2, 3} by decide]
    simp [g]; ring
  constructor
  · have hsymm := (hg.contDiffAt (x := 0)).isSymm_ftaylorSeries (p := 2) le_top
    have hA : ∀ u v : EuclideanSpace ℝ (Fin 3),
        iteratedFDeriv ℝ 2 g 0 ![u, v] = iteratedFDeriv ℝ 2 g 0 ![v, u] := fun u v => by
      have := hsymm 2 le_rfl (Equiv.swap 0 1) ![u, v]
      change iteratedFDeriv ℝ 2 g 0 _ = iteratedFDeriv ℝ 2 g 0 _ at this
      rw [← this]
      congr 1; funext i; fin_cases i <;> rfl
    rw [bilin_polar _ hA, hdiag _ 2 (by decide), hdiag _ 2 (by decide), hdiag _ 2 (by decide)]
    simp [example1431Arc]
  · rw [hdiag _ 3 (by decide)]
    simp [example1431Arc, Nat.factorial]

/-- **Example 14.3.1** of [cartis2022evaluation] (`n = 3`, `m = 2`, `X = ℝ³`), with the
corrections noted below. (i) The arc `x(α) = α s₁ + α² s₂ + α³ s₃ = (-α², α, α³)`
(`s₁ = e₂`, `s₂ = -e₁`, `s₃ = e₃`) is feasible; (ii) the feasible set is exactly
`{(-t², t, t³) | t ∈ ℝ}` and `f` vanishes on it, so the origin is a (non-strict, global)
minimizer — not the "high-order saddle point" claimed by the book; (iii) with `y₀ = (-1, 0)`
(the book's `(1, 0)` corresponds to the opposite sign convention `ℒ = f + ⟨y, c⟩`) the Lagrangian
coefficients of orders `1, 2, 3` along the arc vanish, so (14.3.5) holds for `i = 1, 2` and
(14.3.4) holds with equality for `j = 3`; in the book's notation this is (14.3.6),
`∇²ℒ[s₁, s₂] + (1/6) ∇³ℒ[s₁]³ = -1 + 1 = 0` with both terms nonzero
(`example1431_derivs`). -/
theorem example_14_3_1 :
    Optimization.IsFeasibleArc (univ ∩ {x | example1431C x = 0}) 0 3 example1431Arc ∧
    (∀ x : EuclideanSpace ℝ (Fin 3), example1431C x = 0 ↔ ∃ t : ℝ, x = !₂[-t ^ 2, t, t ^ 3]) ∧
    (∀ x : EuclideanSpace ℝ (Fin 3), example1431C x = 0 → example1431F x = 0) ∧ example1431F 0 = 0 ∧
    IsMinOn example1431F {x | example1431C x = 0} 0 ∧
    ∀ i ∈ Finset.Icc 1 3, Optimization.curveCoeff
      (ftaylorSeries ℝ (innerLagrangian example1431F example1431C (!₂[-1, 0])) 0) example1431Arc i
        = 0 := by
  have hF : ∀ x : EuclideanSpace ℝ (Fin 3), example1431C x = 0 → example1431F x = 0 :=
      fun x hx => by
    obtain ⟨t, rfl⟩ := (example1431C_eq_zero_iff x).1 hx
    simp [example1431F]
  refine ⟨⟨fun α => !₂[-α ^ 2, α, α ^ 3], ?_, Filter.Eventually.of_forall fun α =>
    ⟨mem_univ _, (example1431C_eq_zero_iff _).2 ⟨α, rfl⟩⟩⟩, example1431C_eq_zero_iff, hF,
    by simp [example1431F], fun x hx => ?_, ?_⟩
  · simp only [example1431_arc_eq, sub_self]
    exact Asymptotics.isLittleO_zero _ _
  · simp only [mem_ofPred_eq] at hx ⊢
    rw [hF x hx]; simp [example1431F]
  · rw [example1431_lagrangian_eq]
    have hcoord : ∀ i : Fin 3, ContDiff ℝ ⊤ (fun x : EuclideanSpace ℝ (Fin 3) => x i) :=
      fun i => contDiff_piLp_apply (p := 2)
    have hcd : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin 3) => x 1 ^ 3 + x 0 * x 1) 0 :=
      (((hcoord 1).pow 3).add ((hcoord 0).mul (hcoord 1))).contDiffAt.of_le le_top
    refine Optimization.curveCoeff_eq_of_isLittleO (a := fun _ => 0) hcd ?_
    simp only [example1431_arc_eq]
    simp
    ring_nf
    exact Asymptotics.isLittleO_zero _ _

end Example1431

/-! ## §14.3.2.1 The LENq-SC algorithm -/

/-- The least-squares function `Φ₂(x) = ½ ‖r(x)‖²` of [cartis2022evaluation], (14.3.16) (for
`r = c` this is `ν`): the backbone `Constrained.halfSqNorm`. -/
noncomputable abbrev phi2 (r : ℝⁿ → ℝᵐ) : ℝⁿ → ℝ := Constrained.halfSqNorm r

theorem phi2_apply (r : ℝⁿ → ℝᵐ) (x : ℝⁿ) : phi2 r x = ‖r x‖ ^ 2 / 2 := rfl

/-- The termination test (14.3.23) of LENq-SC ([cartis2022evaluation], Algorithm 14.3.1) at
iteration `k`: `‖r(x_k)‖ ≤ ε₀`, or (for `k ≥ 1`, when radii `δ_k` have been computed)
`φ^{δ_{k,j}}_{Φ₂,X(x_k),j}(x_k) ≤ ε_j ‖r(x_k)‖ δ_{k,j}^j/j!` for all `j ∈ [1 : q]`. The primal
tolerance is `ε 0`. -/
def lenStop (r : ℝⁿ → ℝᵐ) (X : Set ℝⁿ) (q : ℕ) (ε : ℕ → ℝ) (x : ℕ → ℝⁿ) (δ : ℕ → ℕ → ℝ)
    (k : ℕ) : Prop :=
  ‖r (x k)‖ ≤ ε 0 ∨ (1 ≤ k ∧ ∀ j ∈ Finset.Icc 1 q,
    Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 r) (x k)) j (δ k j) {d | x k + d ∈ X} ≤
      ε j * ‖r (x k)‖ * δ k j ^ j / j !)

/-- **Algorithm 14.3.1 (LENq-SC)** of [cartis2022evaluation] as a run predicate on the iterates
`x` and radii `δ` (indexed by the outer iteration `k`; `δ 0` is unused). Given `x₀ ∈ X`,
tolerances `ε_j ∈ (0, 1]` (`j ∈ [0 : q]`) and `β` with `0 < β < 1`, `β ‖r(x₀)‖ < 1`: the run
stops at the first `k` with `lenStop` ((14.3.23); at `k = 0` only `‖r(x₀)‖ ≤ ε₀`), and at every
iteration `k ≥ 1` reached, `x_k ∈ X` and `δ_k ∈ (0, 1]^q` are the output of
`INNER(Φ₂, X, q, x_{k-1}, β ‖r(x_{k-1})‖ ε)`, i.e. satisfy (14.3.22). -/
structure algorithm_14_3_1 (r : ℝⁿ → ℝᵐ) (X : Set ℝⁿ) (q : ℕ) (ε : ℕ → ℝ) (β : ℝ)
    (x : ℕ → ℝⁿ) (δ : ℕ → ℕ → ℝ) : Prop where
  mem_zero : x 0 ∈ X
  /-- The tolerances are positive. -/
  ε_pos : ∀ j ∈ Finset.range (q + 1), 0 < ε j
  /-- The tolerances are at most `1`. -/
  ε_le_one : ∀ j ∈ Finset.range (q + 1), ε j ≤ 1
  /-- `β > 0`. -/
  β_pos : 0 < β
  β_lt_one : β < 1
  β_mul_lt_one : β * ‖r (x 0)‖ < 1
  /-- The INNER output lies in `X`. -/
  mem : ∀ k, 1 ≤ k → (∀ i < k, ¬ lenStop r X q ε x δ i) → x k ∈ X
  /-- The INNER output radii lie in `(0, 1]`. -/
  radius_mem : ∀ k, 1 ≤ k → (∀ i < k, ¬ lenStop r X q ε x δ i) →
    ∀ j ∈ Finset.Icc 1 q, 0 < δ k j ∧ δ k j ≤ 1
  /-- The INNER output condition (14.3.22). -/
  inner : ∀ k, 1 ≤ k → (∀ i < k, ¬ lenStop r X q ε x δ i) → ∀ j ∈ Finset.Icc 1 q,
    Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 r) (x k)) j (δ k j) {d | x k + d ∈ X} ≤
      β * ‖r (x (k - 1))‖ * ε j * δ k j ^ j / j !

namespace algorithm_14_3_1

variable {r : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {q : ℕ} {ε : ℕ → ℝ} {β : ℝ} {x : ℕ → ℝⁿ}
  {δ : ℕ → ℕ → ℝ}

/-- **The residual contracts** ([cartis2022evaluation], proof of Theorem 14.3.3): at every
iteration `k ≥ 1` at which LENq-SC has not terminated (up to and including `k`),
`‖r(x_k)‖ < β ‖r(x_{k-1})‖`. -/
theorem norm_lt (h : algorithm_14_3_1 r X q ε β x δ) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : ∀ i ≤ k, ¬ lenStop r X q ε x δ i) : ‖r (x k)‖ < β * ‖r (x (k - 1))‖ := by
  have hks := hk k le_rfl
  simp only [lenStop, not_or, not_and, not_forall, not_le] at hks
  obtain ⟨j, hj, hlt⟩ := hks.2 hk1
  have hbef : ∀ i < k, ¬ lenStop r X q ε x δ i := fun i hi => hk i hi.le
  have hin := h.inner k hk1 hbef j hj
  have hδ := (h.radius_mem k hk1 hbef j hj).1
  have hεj : 0 < ε j := h.ε_pos j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
  have ha : 0 < ε j * δ k j ^ j / j ! := by positivity
  have : ‖r (x k)‖ * (ε j * δ k j ^ j / j !) < β * ‖r (x (k - 1))‖ * (ε j * δ k j ^ j / j !) := by
    calc ‖r (x k)‖ * (ε j * δ k j ^ j / j !) = ε j * ‖r (x k)‖ * δ k j ^ j / j ! := by ring
      _ < _ := hlt.trans_le hin
      _ = _ := by ring
  exact lt_of_mul_lt_mul_right this ha.le

/-- Iterating the contraction: before termination, `‖r(x_j)‖ ≤ β^{j-i} ‖r(x_i)‖` for `i ≤ j`. -/
theorem norm_le_pow_mul (h : algorithm_14_3_1 r X q ε β x δ) {i j : ℕ} (hij : i ≤ j)
    (hj : ∀ l ≤ j, ¬ lenStop r X q ε x δ l) : ‖r (x j)‖ ≤ β ^ (j - i) * ‖r (x i)‖ := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    have ih := ih fun l hl => hj l (hl.trans j.le_succ)
    have hlt : ‖r (x (j + 1))‖ < β * ‖r (x j)‖ := h.norm_lt (Nat.succ_pos j) hj
    rw [Nat.succ_sub hij, pow_succ]
    have := h.β_pos
    calc ‖r (x (j + 1))‖ ≤ β * ‖r (x j)‖ := hlt.le
      _ ≤ β * (β ^ (j - i) * ‖r (x i)‖) := by gcongr
      _ = _ := by ring

end algorithm_14_3_1

/-- **Theorem 14.3.3** of [cartis2022evaluation] (convergence of LENq-SC), **with the integer
ceiling**. Every LENq-SC run terminates, at an iteration
`k_max ≤ ⌈log(ε₀/‖r(x₀)‖)/log β⌉₊` (the book's `max(0, log(ε₀/‖r(x₀)‖)/log β)` must be rounded
up), at a point satisfying (14.3.18): `‖r(x_{k_max})‖ ≤ ε₀`, or
`φ^{δ_j}_{Φ₂,X(x_{k_max}),j}(x_{k_max}) ≤ ε_j ‖r(x_{k_max})‖ δ_j^j/j!` for all `j ∈ [1 : q]`, for
some `δ ∈ (0, 1]^q`. Moreover `‖r(x_k)‖ < β ‖r(x_{k-1})‖` at every iteration `k ≥ 1` before
termination. -/
theorem theorem_14_3_3 {r : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {q : ℕ} {ε : ℕ → ℝ} {β : ℝ}
    {x : ℕ → ℝⁿ} {δ : ℕ → ℕ → ℝ} (h : algorithm_14_3_1 r X q ε β x δ) :
    (∃ kmax, Optimization.IsFirstHit (lenStop r X q ε x δ) kmax ∧
      kmax ≤ ⌈Real.log (ε 0 / ‖r (x 0)‖) / Real.log β⌉₊ ∧
      (‖r (x kmax)‖ ≤ ε 0 ∨ ∃ δ' : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, 0 < δ' j ∧ δ' j ≤ 1) ∧
        ∀ j ∈ Finset.Icc 1 q, Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 r) (x kmax)) j
          (δ' j) {d | x kmax + d ∈ X} ≤ ε j * ‖r (x kmax)‖ * δ' j ^ j / j !)) ∧
    ∀ k, 1 ≤ k → (∀ i ≤ k, ¬ lenStop r X q ε x δ i) → ‖r (x k)‖ < β * ‖r (x (k - 1))‖ := by
  have hε₀ : 0 < ε 0 := h.ε_pos 0 (by simp)
  obtain ⟨kmax, hhit, hle⟩ := Optimization.le_ceil_log_of_contract (r := fun k => ‖r (x k)‖)
    h.β_pos h.β_lt_one hε₀ (fun k hk => not_le.1 fun h' => hk (Or.inl h'))
    (fun k hk1 hk => h.norm_lt hk1 hk)
  refine ⟨⟨kmax, hhit, hle, ?_⟩, fun k hk1 hk => h.norm_lt hk1 hk⟩
  rcases hhit.1 with h0 | ⟨hk1, hcrit⟩
  · exact Or.inl h0
  · exact Or.inr ⟨δ kmax, h.radius_mem kmax hk1 hhit.2, hcrit⟩

/-- **The INNER cost contract** of [cartis2022evaluation], (14.3.20)–(14.3.21):
`κ (f(x^S) - f_low) max_{j ∈ [1 : q]} ε_j^{-π_j}`, with `gap = f(x^S) - f_low` and the exponents
`π_j > 1` of the chosen INNER method (from (14.2.12)). The maximum is a supremum over the finite
index set (`0` if `q = 0`). -/
noncomputable def innerEvalBound (κ : ℝ) (π : ℕ → ℝ) (q : ℕ) (gap : ℝ) (ε : ℕ → ℝ) : ℝ :=
  κ * gap * ⨆ j : Finset.Icc 1 q, ε j ^ (-π j)

/-- The maximum in the cost contract is at most the sum. -/
theorem innerEvalBound_le_sum {κ gap : ℝ} (hκ : 0 ≤ κ) (hgap : 0 ≤ gap) (π : ℕ → ℝ) (q : ℕ)
    {ε : ℕ → ℝ} (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j) :
    innerEvalBound κ π q gap ε ≤ κ * gap * ∑ j ∈ Finset.Icc 1 q, ε j ^ (-π j) := by
  unfold innerEvalBound
  gcongr
  refine Real.iSup_le (fun j => ?_) (Finset.sum_nonneg fun i hi =>
    (Real.rpow_pos_of_pos (hε i hi) _).le)
  exact Finset.single_le_sum (f := fun i => ε i ^ (-π i))
    (fun i hi => (Real.rpow_pos_of_pos (hε i hi) _).le) j.2

/-- For `q = 1` the cost contract (14.3.20)–(14.3.21) has a single term:
`κ gap ε_1^{-π_1}`. -/
theorem innerEvalBound_one (κ : ℝ) (π : ℕ → ℝ) (gap : ℝ) (ε : ℕ → ℝ) :
    innerEvalBound κ π 1 gap ε = κ * gap * ε 1 ^ (-π 1) := by
  unfold innerEvalBound
  congr 1
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 1 := by simp
  have hbdd : BddAbove (Set.range fun j : Finset.Icc 1 1 => ε j ^ (-π j)) :=
    (Set.finite_range _).bddAbove
  have : Nonempty (Finset.Icc 1 1) := ⟨⟨1, h1⟩⟩
  refine le_antisymm (ciSup_le fun j => ?_) (le_ciSup_of_le hbdd ⟨1, h1⟩ le_rfl)
  obtain ⟨j, hj⟩ := j
  obtain rfl : j = 1 := by simpa using hj
  exact le_rfl

/-- **Theorem 14.3.4** of [cartis2022evaluation] (evaluation complexity of LENq-SC),
**corrected**. Let a LENq-SC run terminate at `k_max`, let `π_j > 1`, and let the cost `n_k` of
the `k`-th INNER call (evaluations of `Φ₂`, or of its derivatives) satisfy the contract
(14.3.20) (resp. (14.3.21)) with constant `κ ≥ 0` and `f_low = 0`:
`n_k ≤ κ Φ₂(x_{k-1}) max_j (β ‖r(x_{k-1})‖ ε_j)^{-π_j}`. Then the total cost is
`∑_{k=1}^{k_max} n_k ≤ ½ κ ‖r(x₀)‖ ∑_{j=1}^q β^{1-2π_j}/(β^{1-π_j} - 1) ε₀^{1-π_j} ε_j^{-π_j}`
((14.3.27)–(14.3.28) with `∑_j` in place of `max_j`: the printed proof exchanges a sum over `k` and
a maximum over `j`). -/
theorem theorem_14_3_4 {r : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {q : ℕ} {ε : ℕ → ℝ} {β : ℝ}
    {x : ℕ → ℝⁿ} {δ : ℕ → ℕ → ℝ} (h : algorithm_14_3_1 r X q ε β x δ) {kmax : ℕ}
    (hend : Optimization.IsFirstHit (lenStop r X q ε x δ) kmax) {π : ℕ → ℝ}
    (hπ : ∀ j ∈ Finset.Icc 1 q, 1 < π j) {κ : ℝ} (hκ : 0 ≤ κ) {cost : ℕ → ℝ}
    (hcost : ∀ k ∈ Finset.Icc 1 kmax,
      cost k ≤ innerEvalBound κ π q (phi2 r (x (k - 1))) (fun j => β * ‖r (x (k - 1))‖ * ε j)) :
    ∑ k ∈ Finset.Icc 1 kmax, cost k ≤
      1 / 2 * κ * ‖r (x 0)‖ * ∑ j ∈ Finset.Icc 1 q,
        β ^ (1 - 2 * π j) / (β ^ (1 - π j) - 1) * ε 0 ^ (1 - π j) * ε j ^ (-π j) := by
  set R : ℕ → ℝ := fun k => ‖r (x k)‖ with hR
  have hβ := h.β_pos
  have hβ1 := h.β_lt_one
  have hε₀ : 0 < ε 0 := h.ε_pos 0 (by simp)
  have hεj : ∀ j ∈ Finset.Icc 1 q, 0 < ε j := fun j hj =>
    h.ε_pos j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
  -- the residuals before termination
  have hnot : ∀ l < kmax, ¬ lenStop r X q ε x δ l := hend.2
  have hRgt : ∀ l < kmax, ε 0 < R l := fun l hl =>
    not_le.1 fun h' => hnot l hl (Or.inl h')
  have hRle0 : ∀ k ∈ Finset.Icc 1 kmax, R (k - 1) ≤ R 0 := fun k hk => by
    have hk := Finset.mem_Icc.1 hk
    have := h.norm_le_pow_mul (Nat.zero_le (k - 1))
      (fun l hl => hnot l (by omega))
    have hp : β ^ (k - 1 - 0) ≤ 1 := pow_le_one₀ hβ.le hβ1.le
    calc R (k - 1) ≤ β ^ (k - 1 - 0) * R 0 := this
      _ ≤ 1 * R 0 := by gcongr
      _ = R 0 := one_mul _
  have hRlow : ∀ k ∈ Finset.Icc 1 kmax, β ^ ((k : ℤ) - kmax) * ε 0 ≤ R (k - 1) := by
    intro k hk
    have hk := Finset.mem_Icc.1 hk
    have hpow := h.norm_le_pow_mul (i := k - 1) (j := kmax - 1) (by omega)
      (fun l hl => hnot l (by omega))
    have hlast := hRgt (kmax - 1) (by omega)
    have hz : β ^ ((k : ℤ) - kmax) = (β ^ (kmax - 1 - (k - 1)))⁻¹ := by
      rw [← zpow_natCast, ← zpow_neg]
      congr 1
      rw [show kmax - 1 - (k - 1) = kmax - k by omega, Nat.cast_sub hk.2]
      ring
    rw [hz, inv_mul_le_iff₀ (pow_pos hβ _)]
    exact (hlast.le.trans hpow)
  -- the per-call bound
  have hcall : ∀ k ∈ Finset.Icc 1 kmax, cost k ≤ 1 / 2 * κ * R 0 *
      ∑ j ∈ Finset.Icc 1 q, β ^ (-π j) * ε j ^ (-π j) * R (k - 1) ^ (1 - π j) := by
    intro k hk
    have hRk : 0 < R (k - 1) := hε₀.trans (hRgt (k - 1) (by have := Finset.mem_Icc.1 hk; omega))
    refine (hcost k hk).trans ((innerEvalBound_le_sum hκ (by rw [phi2_apply]; positivity) π q
      (fun j hj => by have := hεj j hj; positivity)).trans ?_)
    rw [phi2_apply, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hε := hεj j hj
    rw [Real.mul_rpow (by positivity) hε.le, Real.mul_rpow hβ.le hRk.le]
    have hsq : R (k - 1) ^ 2 * R (k - 1) ^ (-π j) ≤ R 0 * R (k - 1) ^ (1 - π j) := by
      have : R (k - 1) ^ 2 * R (k - 1) ^ (-π j) = R (k - 1) * R (k - 1) ^ (1 - π j) := by
        rw [Real.rpow_sub hRk, Real.rpow_one, Real.rpow_neg hRk.le]
        field_simp
      rw [this]
      gcongr
      exact hRle0 k hk
    have h1 : 0 ≤ κ * β ^ (-π j) * ε j ^ (-π j) / 2 := by positivity
    calc κ * (‖r (x (k - 1))‖ ^ 2 / 2) * (β ^ (-π j) * R (k - 1) ^ (-π j) * ε j ^ (-π j))
        = κ * β ^ (-π j) * ε j ^ (-π j) / 2 * (R (k - 1) ^ 2 * R (k - 1) ^ (-π j)) := by
          rw [hR]; ring
      _ ≤ κ * β ^ (-π j) * ε j ^ (-π j) / 2 * (R 0 * R (k - 1) ^ (1 - π j)) := by gcongr
      _ = 1 / 2 * κ * R 0 * (β ^ (-π j) * ε j ^ (-π j) * R (k - 1) ^ (1 - π j)) := by ring
  refine (Finset.sum_le_sum hcall).trans ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hR0 : 0 ≤ R 0 := norm_nonneg _
  gcongr with j hj
  rw [← Finset.mul_sum]
  have hgeom := Optimization.sum_rpow_le_of_geometric_lower (r := R) hβ hβ1 hε₀ (hπ j hj) hRlow
  have hε := hεj j hj
  have hb : 0 ≤ β ^ (-π j) * ε j ^ (-π j) := by positivity
  calc β ^ (-π j) * ε j ^ (-π j) * ∑ k ∈ Finset.Icc 1 kmax, R (k - 1) ^ (1 - π j)
      ≤ β ^ (-π j) * ε j ^ (-π j) * (ε 0 ^ (1 - π j) * β ^ (1 - π j) / (β ^ (1 - π j) - 1)) :=
        mul_le_mul_of_nonneg_left hgeom hb
    _ = β ^ (1 - 2 * π j) / (β ^ (1 - π j) - 1) * ε 0 ^ (1 - π j) * ε j ^ (-π j) := by
        have : β ^ (1 - 2 * π j) = β ^ (-π j) * β ^ (1 - π j) := by
          rw [← Real.rpow_add hβ]; ring_nf
        rw [this]; ring

/-- **Theorem 14.3.4 with an additive per-call constant** ([cartis2022evaluation], footnote 114:
the contract (14.3.20)–(14.3.21) ignores the additive constants of the INNER bounds). If the cost
of the `k`-th INNER call of a LENq-SC run terminating at `k_max` satisfies
`n_k ≤ κ Φ₂(x_{k-1}) max_j (β ‖r(x_{k-1})‖ ε_j)^{-π_j} + a` (`π_j > 1`, `κ ≥ 0`), the total cost
is at most the bound of `theorem_14_3_4` plus `k_max a`. -/
theorem theorem_14_3_4_add {r : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {q : ℕ} {ε : ℕ → ℝ} {β : ℝ}
    {x : ℕ → ℝⁿ} {δ : ℕ → ℕ → ℝ} (h : algorithm_14_3_1 r X q ε β x δ) {kmax : ℕ}
    (hend : Optimization.IsFirstHit (lenStop r X q ε x δ) kmax) {π : ℕ → ℝ}
    (hπ : ∀ j ∈ Finset.Icc 1 q, 1 < π j) {κ a : ℝ} (hκ : 0 ≤ κ) {cost : ℕ → ℝ}
    (hcost : ∀ k ∈ Finset.Icc 1 kmax, cost k ≤
      innerEvalBound κ π q (phi2 r (x (k - 1))) (fun j => β * ‖r (x (k - 1))‖ * ε j) + a) :
    ∑ k ∈ Finset.Icc 1 kmax, cost k ≤
      1 / 2 * κ * ‖r (x 0)‖ * ∑ j ∈ Finset.Icc 1 q,
        β ^ (1 - 2 * π j) / (β ^ (1 - π j) - 1) * ε 0 ^ (1 - π j) * ε j ^ (-π j) +
      kmax * a := by
  have := theorem_14_3_4 h hend hπ hκ (cost := fun k => cost k - a) fun k hk => by
    linarith [hcost k hk]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul,
    Nat.add_sub_cancel] at this
  linarith

/-! ### Smoothness assumptions and Lemma 14.3.6 -/

/-- **Assumption f.D1pLB.X** of [cartis2022evaluation], §14.3.2.2 (and f.D1qLB.X with `q` in
place of `p`): `g` is `p` times continuously differentiable on an open convex set `X₀ ⊇ X`, and
for `j ∈ [1 : p]` its derivative tensors `∇^j g` are Lipschitz continuous (constants `L j`) and
bounded (constants `B j`) on `X₀`. It is stated as the anchored smoothness assumption
`LipschitzDerivsAnchored` on `X₀` with all of `X₀` as anchors (Lipschitz continuity on `X₀`) and
the orders `[1 : p]`, together with `X ⊆ X₀` and the bounds; the book's form is
`AssumptionD1pLBX.of_lipschitzOn`. -/
abbrev AssumptionD1pLBX (g : ℝⁿ → ℝ) (X X₀ : Set ℝⁿ) (p : ℕ) (L B : ℕ → ℝ) : Prop :=
  LipschitzDerivsAnchored g X₀ X₀ 1 p L ∧ X ⊆ X₀ ∧
    ∀ j ∈ Finset.Icc 1 p, ∀ x ∈ X₀, ‖iteratedFDeriv ℝ j g x‖ ≤ B j

namespace AssumptionD1pLBX

variable {g : ℝⁿ → ℝ} {X X₀ : Set ℝⁿ} {p : ℕ} {L B : ℕ → ℝ}

theorem isOpen (hg : AssumptionD1pLBX g X X₀ p L B) : IsOpen X₀ :=
  hg.1.isOpen

theorem convex (hg : AssumptionD1pLBX g X X₀ p L B) : Convex ℝ X₀ :=
  hg.1.convex

theorem subset (hg : AssumptionD1pLBX g X X₀ p L B) : X ⊆ X₀ :=
  hg.2.1

theorem contDiffOn (hg : AssumptionD1pLBX g X X₀ p L B) : ContDiffOn ℝ p g X₀ :=
  fun y hy => (hg.1.contDiffAt y hy).contDiffWithinAt

/-- The derivatives of orders `j ∈ [1 : p]` are `L_j`-Lipschitz on `X₀`. -/
theorem lipschitz (hg : AssumptionD1pLBX g X X₀ p L B) :
    ∀ j ∈ Finset.Icc 1 p, IteratedFDerivLipschitzOn g j (L j) X₀ :=
  fun _ hj => hg.1.lipschitzOn hj

/-- The derivatives of orders `j ∈ [1 : p]` are bounded by `B_j` on `X₀`. -/
theorem norm_le (hg : AssumptionD1pLBX g X X₀ p L B) :
    ∀ j ∈ Finset.Icc 1 p, ∀ x ∈ X₀, ‖iteratedFDeriv ℝ j g x‖ ≤ B j :=
  hg.2.2

/-- f.D1pLB.X in the book's form: `g` is `C^p` on an open convex `X₀ ⊇ X`, with derivatives of
orders `j ∈ [1 : p]` that are `L_j`-Lipschitz and bounded by `B_j` on `X₀`. -/
theorem of_lipschitzOn (hX₀ : IsOpen X₀) (hconv : Convex ℝ X₀) (hX : X ⊆ X₀)
    (hg : ContDiffOn ℝ p g X₀) (hL : ∀ j ∈ Finset.Icc 1 p, IteratedFDerivLipschitzOn g j (L j) X₀)
    (hB : ∀ j ∈ Finset.Icc 1 p, ∀ x ∈ X₀, ‖iteratedFDeriv ℝ j g x‖ ≤ B j) :
    AssumptionD1pLBX g X X₀ p L B :=
  ⟨.of_lipschitzOn hX₀ hconv subset_rfl (fun _ hy => hg.contDiffAt (hX₀.mem_nhds hy)) hL, hX, hB⟩

end AssumptionD1pLBX

/-- **Assumption c.D1pLB.X** of [cartis2022evaluation], §14.3.2.2: the components `c_i` are `p`
times continuously differentiable on an open convex set `X₀ ⊇ X`, with Lipschitz and bounded
derivative tensors of orders `1, …, p` on `X₀` (with constants common to all components, which is
no loss of generality for finitely many components). It is f.D1pLB.X (`AssumptionD1pLBX`) for
every component on a common set `X₀`, whose properties are recorded separately since they are part
of the assumption also when there are no components (`m = 0`). -/
structure AssumptionCD1pLBX (c : ℝⁿ → ℝᵐ) (X X₀ : Set ℝⁿ) (p : ℕ) (L B : ℕ → ℝ) : Prop where
  isOpen : IsOpen X₀
  convex : Convex ℝ X₀
  subset : X ⊆ X₀
  component : ∀ i, AssumptionD1pLBX (fun x => c x i) X X₀ p L B

theorem AssumptionCD1pLBX.contDiffOn {c : ℝⁿ → ℝᵐ} {X X₀ : Set ℝⁿ} {p : ℕ} {L B : ℕ → ℝ}
    (hc : AssumptionCD1pLBX c X X₀ p L B) : ContDiffOn ℝ p c X₀ :=
  contDiffOn_piLp' 2 fun i => (hc.component i).contDiffOn

/-- A `C^∞` function satisfies f.D1pLB.X on any ball containing `X`, with some
constants (Lipschitz and bounded derivative tensors on the compact closure). -/
theorem exists_assumptionD1pLBX_ball {g : ℝⁿ → ℝ} (hg : ContDiff ℝ ∞ g) {X : Set ℝⁿ} {R : ℝ}
    (hX : X ⊆ ball 0 R) (p : ℕ) : ∃ L B : ℕ → ℝ, AssumptionD1pLBX g X (ball 0 R) p L B := by
  have hK : ∀ j : ℕ, ∃ K M : ℝ,
      (∀ x ∈ closedBall (0 : ℝⁿ) R, ∀ y ∈ closedBall (0 : ℝⁿ) R,
        ‖iteratedFDeriv ℝ j g x - iteratedFDeriv ℝ j g y‖ ≤ K * ‖x - y‖) ∧
      ∀ x ∈ closedBall (0 : ℝⁿ) R, ‖iteratedFDeriv ℝ j g x‖ ≤ M := by
    intro j
    have hj : ContDiff ℝ 1 (iteratedFDeriv ℝ j g) :=
      hg.iteratedFDeriv_right (by exact_mod_cast le_top)
    obtain ⟨K, hK⟩ := hj.locallyLipschitz.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
      (isCompact_closedBall (0 : ℝⁿ) R)
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℝⁿ) R).exists_bound_of_continuousOn
      hj.continuous.continuousOn
    exact ⟨K, M, fun x hx y hy => by simpa [dist_eq_norm] using hK.dist_le_mul x hx y hy, hM⟩
  choose L B hL hB using hK
  refine ⟨L, B, .of_lipschitzOn isOpen_ball (convex_ball 0 R) hX
    (hg.of_le (by exact_mod_cast le_top)).contDiffOn (fun j _ x hx y hy => ?_)
    fun j _ x hx => hB j x (ball_subset_closedBall hx)⟩
  simpa [Real.rpow_one] using hL j x (ball_subset_closedBall hx) y (ball_subset_closedBall hy)

/-- The sublevel set `𝓛_ν(x₀) = {x ∈ X | ‖c(x)‖ ≤ ‖c(x₀)‖}` of Lemma 14.3.6(i) of
[cartis2022evaluation]. -/
def nuSublevel (c : ℝⁿ → ℝᵐ) (X : Set ℝⁿ) (x₀ : ℝⁿ) : Set ℝⁿ := {x ∈ X | ‖c x‖ ≤ ‖c x₀‖}

/-- The set `𝓛_μ(t) = {x ∈ X | ‖r(x, t)‖ ≤ 1}` of Lemma 14.3.6(ii) of [cartis2022evaluation]
(`Constrained.targetSublevel`). -/
abbrev muSublevel (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (X : Set ℝⁿ) (t : ℝ) : Set ℝⁿ :=
  Constrained.targetSublevel f c X t

/-- f.D1pLB.X gives the hypotheses of the product rule (`AnchoredJetBounds`) for `g - a` on an
anchor set `A ⊆ X₀` on which `|g - a| ≤ U`. -/
theorem AssumptionD1pLBX.anchoredJetBounds_sub {g : ℝⁿ → ℝ} {X X₀ : Set ℝⁿ} {p : ℕ}
    {L B : ℕ → ℝ} (hg : AssumptionD1pLBX g X X₀ p L B) {A : Set ℝⁿ} (hA : A ⊆ X₀) (a : ℝ)
    {U : ℝ} (hU : ∀ x ∈ A, |g x - a| ≤ U) :
    AnchoredJetBounds (fun y => g y - a) p L B U A X₀ where
  contDiffOn := hg.contDiffOn.sub contDiffOn_const
  lipschitzAnchored i hi x hx y hy := by
    have hip := (Finset.mem_Icc.1 hi).2
    have hi0 : i ≠ 0 := by have := (Finset.mem_Icc.1 hi).1; omega
    have hcd : ∀ z ∈ X₀, ContDiffAt ℝ i g z := fun z hz =>
      (hg.contDiffOn.contDiffAt (hg.isOpen.mem_nhds hz)).of_le (by exact_mod_cast hip)
    rw [AnchoredJetBounds.iteratedFDeriv_sub_const (hcd x (hA hx)) a hi0,
      AnchoredJetBounds.iteratedFDeriv_sub_const (hcd y hy) a hi0]
    exact ((hg.lipschitz i hi).anchored hA) x hx y hy
  norm_le i hi y hy := by
    have hip := (Finset.mem_Icc.1 hi).2
    have hi0 : i ≠ 0 := by have := (Finset.mem_Icc.1 hi).1; omega
    rw [AnchoredJetBounds.iteratedFDeriv_sub_const
      ((hg.contDiffOn.contDiffAt (hg.isOpen.mem_nhds hy)).of_le (by exact_mod_cast hip)) a hi0]
    exact hg.norm_le i hi y hy
  abs_le := hU

/-- **Lemma 14.3.6(i)** of [cartis2022evaluation] (smoothness of `ν`). Under c.D1pLB.X there are
constants `L^A_j, L^B_j, B^A_j, B^B_j ≥ 1`, depending only on `m` and the constants of
c.D1pLB.X, such that for every `x₀`, `ν = ½ ‖c‖²` is `C^p` on `X₀` and for `j ∈ [1 : p]`,
`‖∇^j ν(x) - ∇^j ν(y)‖ ≤ (L^A_j + L^B_j ‖c(x₀)‖) ‖x - y‖` (14.3.60) and
`‖∇^j ν(x)‖ ≤ B^A_j + B^B_j ‖c(x₀)‖` (14.3.61) for all `x ∈ 𝓛_ν(x₀)` and `y ∈ X₀`. -/
theorem lemma_14_3_6_i {c : ℝⁿ → ℝᵐ} {X X₀ : Set ℝⁿ} {p : ℕ} {L B : ℕ → ℝ}
    (hc : AssumptionCD1pLBX c X X₀ p L B) :
    ∃ LA LB BA BB : ℕ → ℝ, (∀ j, 1 ≤ LA j ∧ 1 ≤ LB j ∧ 1 ≤ BA j ∧ 1 ≤ BB j) ∧
      ∀ x₀ : ℝⁿ, ContDiffOn ℝ p (phi2 c) X₀ ∧ ∀ j ∈ Finset.Icc 1 p,
        IteratedFDerivLipschitzAnchored (phi2 c) j (LA j + LB j * ‖c x₀‖) (nuSublevel c X x₀)
          X₀ ∧
        ∀ x ∈ nuSublevel c X x₀, ‖iteratedFDeriv ℝ j (phi2 c) x‖ ≤ BA j + BB j * ‖c x₀‖ := by
  refine ⟨fun j => max 1 (m * (anchoredMulLipConst L L B B j / 2)),
    fun j => max 1 (m * L j), fun j => max 1 (m * (anchoredMulBoundConst B B j / 2)),
    fun j => max 1 (m * B j), fun j => ⟨le_max_left _ _, le_max_left _ _, le_max_left _ _,
      le_max_left _ _⟩, fun x₀ => ?_⟩
  have hA : nuSublevel c X x₀ ⊆ X₀ := fun x hx => hc.subset hx.1
  have hU : 0 ≤ ‖c x₀‖ := norm_nonneg _
  have hjb : ∀ i, AnchoredJetBounds (fun y => c y i) p L B ‖c x₀‖ (nuSublevel c X x₀) X₀ :=
    fun i => by
      simpa using (hc.component i).anchoredJetBounds_sub hA 0 (U := ‖c x₀‖) fun x hx => by
        rw [sub_zero, ← Real.norm_eq_abs]
        exact (PiLp.norm_apply_le (c x) i).trans hx.2
  refine ⟨(hc.contDiffOn.norm_sq ℝ).div_const 2, fun j hj => ⟨?_, fun x hx => ?_⟩⟩
  · refine (AnchoredJetBounds.lipschitzAnchored_half_norm_sq hjb hc.isOpen hc.convex hA hj
      |>.mono_const ?_)
    have h1 := le_max_right 1 (m * (anchoredMulLipConst L L B B j / 2))
    have h2 := mul_le_mul_of_nonneg_right (le_max_right 1 ((m : ℝ) * L j)) hU
    nlinarith
  · refine (AnchoredJetBounds.norm_iteratedFDeriv_half_norm_sq_le hjb hc.isOpen hA hj hx).trans ?_
    have h1 := le_max_right 1 (m * (anchoredMulBoundConst B B j / 2))
    have h2 := mul_le_mul_of_nonneg_right (le_max_right 1 ((m : ℝ) * B j)) hU
    nlinarith

/-- `μ(·, t) = ½ ‖c‖² + ½ (f - t)²`. -/
theorem targetMerit_eq_add (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (t : ℝ) :
    Constrained.targetMerit f c t = (fun y => ‖c y‖ ^ 2 / 2) + fun y => (f y - t) ^ 2 / 2 := by
  funext y
  simp only [Constrained.targetMerit_def, Pi.add_apply]
  ring

/-- **Lemma 14.3.6(ii)** of [cartis2022evaluation] (smoothness of `μ`). Under c.D1pLB.X and
f.D1pLB.X (on the same `X₀`) there are constants `L_{μ,j}, B_{μ,j} ≥ 1`, independent of `t`,
such that for every target `t`, `μ(·, t)` is `C^p` on `X₀` and for `j ∈ [1 : p]`,
`‖∇^j μ(x, t) - ∇^j μ(y, t)‖ ≤ L_{μ,j} ‖x - y‖` (14.3.62) and `‖∇^j μ(x, t)‖ ≤ B_{μ,j}` (14.3.63;
the book writes `∇^j ν` there) for all `x ∈ 𝓛_μ(t) = {x ∈ X | ‖r(x, t)‖ ≤ 1}` and `y ∈ X₀`. -/
theorem lemma_14_3_6_ii {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X X₀ : Set ℝⁿ} {p : ℕ}
    {Lc Bc Lf Bf : ℕ → ℝ} (hc : AssumptionCD1pLBX c X X₀ p Lc Bc)
    (hf : AssumptionD1pLBX f X X₀ p Lf Bf) :
    ∃ Lμ Bμ : ℕ → ℝ, (∀ j, 1 ≤ Lμ j ∧ 1 ≤ Bμ j) ∧
      ∀ t : ℝ, ContDiffOn ℝ p (Constrained.targetMerit f c t) X₀ ∧ ∀ j ∈ Finset.Icc 1 p,
        IteratedFDerivLipschitzAnchored (Constrained.targetMerit f c t) j (Lμ j)
          (muSublevel f c X t) X₀ ∧
        ∀ x ∈ muSublevel f c X t, ‖iteratedFDeriv ℝ j (Constrained.targetMerit f c t) x‖ ≤
          Bμ j := by
  refine ⟨fun j => max 1 (m * (anchoredMulLipConst Lc Lc Bc Bc j / 2 + Lc j) +
      (anchoredMulLipConst Lf Lf Bf Bf j / 2 + Lf j)),
    fun j => max 1 (m * (anchoredMulBoundConst Bc Bc j / 2 + Bc j) +
      (anchoredMulBoundConst Bf Bf j / 2 + Bf j)),
    fun j => ⟨le_max_left _ _, le_max_left _ _⟩, fun t => ?_⟩
  have hA : muSublevel f c X t ⊆ X₀ := fun x hx => hc.subset hx.1
  have hjc : ∀ i, AnchoredJetBounds (fun y => c y i) p Lc Bc 1 (muSublevel f c X t) X₀ :=
    fun i => by
      simpa using (hc.component i).anchoredJetBounds_sub hA 0 (U := 1) fun x hx => by
        rw [sub_zero, ← Real.norm_eq_abs]
        exact (PiLp.norm_apply_le (c x) i).trans
          (Constrained.norm_le_targetResidual.trans hx.2)
  have hjf : AnchoredJetBounds (fun y => f y - t) p Lf Bf 1 (muSublevel f c X t) X₀ :=
    hf.anchoredJetBounds_sub hA t fun x hx =>
      Constrained.abs_sub_le_targetResidual.trans hx.2
  have hcc : ContDiffOn ℝ p (fun y => ‖c y‖ ^ 2 / 2) X₀ :=
    (hc.contDiffOn.norm_sq ℝ).div_const 2
  have hff : ContDiffOn ℝ p (fun y => (f y - t) ^ 2 / 2) X₀ :=
    ((hf.contDiffOn.sub contDiffOn_const).pow 2).div_const 2
  rw [targetMerit_eq_add]
  refine ⟨hcc.add hff, fun j hj => ⟨?_, fun x hx => ?_⟩⟩
  · have hjp : (j : WithTop ℕ∞) ≤ p := by exact_mod_cast (Finset.mem_Icc.1 hj).2
    have h := (AnchoredJetBounds.lipschitzAnchored_half_norm_sq hjc hc.isOpen hc.convex hA
      hj).add (AnchoredJetBounds.lipschitzAnchored_half_sq hjf hc.isOpen hc.convex hA hj)
      (fun y hy => (hcc.contDiffAt (hc.isOpen.mem_nhds hy)).of_le hjp)
      (fun y hy => (hff.contDiffAt (hc.isOpen.mem_nhds hy)).of_le hjp) hA
    refine h.mono_const ?_
    simp only [mul_one]
    exact le_max_right _ _
  · have hjp : (j : WithTop ℕ∞) ≤ p := by exact_mod_cast (Finset.mem_Icc.1 hj).2
    rw [iteratedFDeriv_add_apply ((hcc.contDiffAt (hc.isOpen.mem_nhds (hA hx))).of_le hjp)
      ((hff.contDiffAt (hc.isOpen.mem_nhds (hA hx))).of_le hjp)]
    refine (norm_add_le _ _).trans ?_
    have h1 := AnchoredJetBounds.norm_iteratedFDeriv_half_norm_sq_le hjc hc.isOpen hA hj hx
    have h2 := AnchoredJetBounds.norm_iteratedFDeriv_half_sq_le hjf hc.isOpen hA hj hx
    simp only [mul_one] at h1 h2
    exact (add_le_add h1 h2).trans (le_max_right _ _)


/-! ## §14.3.2.2 The TPqp-GC algorithm -/

/-- The tolerances of Phase 1 of TPqp-GC ([cartis2022evaluation], Algorithm 14.3.2): LENq-SC on
`ν` with primal tolerance `θ ε₀` and dual tolerances `ε_j`, `j ∈ [1 : q]`. -/
noncomputable def phase1Tol (θ : ℝ) (ε : ℕ → ℝ) : ℕ → ℝ := fun j => if j = 0 then θ * ε 0 else ε j

@[simp] theorem phase1Tol_zero (θ : ℝ) (ε : ℕ → ℝ) : phase1Tol θ ε 0 = θ * ε 0 := rfl

theorem phase1Tol_of_ne (θ : ℝ) (ε : ℕ → ℝ) {j : ℕ} (hj : j ≠ 0) : phase1Tol θ ε j = ε j := by
  simp [phase1Tol, hj]

/-- The approximate-criticality test (14.3.34) of TPqp-GC (also the third test of (14.3.32)) at
the point `y` for the target `t` with radii `δ`:
`φ^{δ_j}_{μ,X(y),j}(y, t) ≤ ε_j ‖r(y, t)‖ δ_j^j/j!` for `j ∈ [1 : q]`
(`Constrained.targetCrit`). -/
abbrev meritCrit (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (X : Set ℝⁿ) (q : ℕ) (ε : ℕ → ℝ) (t : ℝ) (y : ℝⁿ)
    (δ : ℕ → ℝ) : Prop :=
  Constrained.targetCrit f c X q ε t y δ

/-- The sequences generated by Phase 2 of TPqp-GC ([cartis2022evaluation], Algorithm 14.3.2),
indexed by the outer iteration `k ≥ 1`: outer iterates `x k`, targets `t k`, optimality radii
`δ k`, and for the `k`-th call of INNER on `μ(·, t_k)` its iterates `xi k i`, its number of
iterations `e k` and its successful iterations `succ k i` (`Constrained.HighOrderTargetSeq`,
whose `IsKa`, `IsKb` ((14.3.36)), `Stop`, `Before`, `IsEnd`, `targetOut`, `InnerTest` ((14.3.19))
and counts apply). -/
abbrev TPqpSeq (n : ℕ) := Constrained.HighOrderTargetSeq (EuclideanSpace ℝ (Fin n))

/-- **Phase 2 of Algorithm 14.3.2** (TPqp-GC) of [cartis2022evaluation], started at the output
`x₁ ∈ X` of Phase 1 with `‖c(x₁)‖ ≤ θε₀`, as a predicate on the sequences `D`
(`Constrained.IsHighOrderTargetRun`). Constants: `θ ∈ (0, 1)`, `β ∈ (0, θ]`, tolerances
`ε_j ∈ (0, 1]`, `j ∈ [0 : q]` (`ε₀ = ε 0`). Step 0: `t₁ = f(x₁) - √(ε₀² - ‖c(x₁)‖²)`. For every
outer iteration `k ≥ 1` reached: Step 1, `x_{k+1} ∈ X` and radii `δ_{k+1} ∈ (0, 1]^q` satisfy
(14.3.32), computed by a call of INNER on `μ(·, t_k)` from `x_k`, whose iterates `x_{k,i}`
(`i ≤ e_k`, `x_{k,0} = x_k`, `x_{k,e_k} = x_{k+1}`) do not increase `μ(·, t_k)` and keep
`‖r(·, t_k)‖ ≥ θε₀` before the last one (the call is stopped as soon as the first test of
(14.3.32) holds); Step 2, the target updates (14.3.33) in case (a) and (14.3.35) in case (b).
Termination is `Constrained.HighOrderTargetSeq.Stop`. It is a run of the target-following outer
loop of the library (`Constrained.IsHighOrderTargetRun.toRun`), whose output satisfies (14.3.48),
(14.3.49) and (14.3.52) (`Constrained.IsHighOrderTargetRun.output_spec`). -/
abbrev IsTPqpGCPhase2 (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (X : Set ℝⁿ) (q : ℕ) (θ β : ℝ)
    (ε : ℕ → ℝ) (x₁ : ℝⁿ) (D : TPqpSeq n) : Prop :=
  Constrained.IsHighOrderTargetRun f c X q θ β ε x₁ D

/-- **Algorithm 14.3.2 (TPqp-GC)** of [cartis2022evaluation] as a run predicate. Phase 1 is a
LENq-SC run (`algorithm_14_3_1`) on `r = c` from `x₀ ∈ X` with constant `β₁` and tolerances
`(θε₀, ε_1, …, ε_q)` (`phase1Tol`), terminating at its first hit `k₁`; its output is
`x₁ = xP k₁` with radii `δP k₁` ((14.3.31)). If `‖c(x₁)‖ > θε₀` the algorithm terminates;
otherwise Phase 2 (`IsTPqpGCPhase2`) runs from `x₁`. (The LENq-SC test stops at
`‖c(x₁)‖ ≤ θε₀`, while (14.3.31) is printed with `<`; the two differ only when
`‖c(x₁)‖ = θε₀`, in which case Phase 2 is entered, consistently with the exit test
`‖c(x₁)‖ > θε₀`.) -/
structure algorithm_14_3_2 (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (X : Set ℝⁿ) (q : ℕ) (θ β₁ β : ℝ)
    (ε : ℕ → ℝ) (x₀ : ℝⁿ) (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq n) : Prop where
  /-- Phase 1 starts at `x₀`. -/
  start : xP 0 = x₀
  /-- Phase 1: LENq-SC on `ν = ½ ‖c‖²`. -/
  phase1 : algorithm_14_3_1 c X q (phase1Tol θ ε) β₁ xP δP
  /-- Phase 1 ends at its first termination index `k₁` (which exists by Theorem 14.3.3 and is
  determined by the Phase-1 sequences). -/
  phase1_end : Optimization.IsFirstHit (lenStop c X q (phase1Tol θ ε) xP δP) k₁
  /-- Phase 2, entered when `‖c(x₁)‖ ≤ θε₀`. -/
  phase2 : ‖c (xP k₁)‖ ≤ θ * ε 0 → IsTPqpGCPhase2 f c X q θ β ε (xP k₁) D


/-! ### Lemma 14.3.5: consequences of termination -/

section Termination

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X X₀ : Set ℝⁿ} {q p : ℕ} {θ β₁ β : ℝ} {ε : ℕ → ℝ}
  {x₀ : ℝⁿ} {xP : ℕ → ℝⁿ} {δP : ℕ → ℕ → ℝ} {k₁ : ℕ} {D : TPqpSeq n}

/-- Termination of Phase 1 with `‖c(x₁)‖ > θε₀` gives (14.3.41) at `x₁` with the radii of the
last LENq-SC iteration. -/
theorem algorithm_14_3_2.phase1_exit (h : algorithm_14_3_2 f c X q θ β₁ β ε x₀ xP δP k₁ D)
    (hc : θ * ε 0 < ‖c (xP k₁)‖) :
    1 ≤ k₁ ∧ (∀ j ∈ Finset.Icc 1 q, 0 < δP k₁ j ∧ δP k₁ j ≤ 1) ∧
      ∀ j ∈ Finset.Icc 1 q, Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 c) (xP k₁)) j
        (δP k₁ j) {d | xP k₁ + d ∈ X} ≤ ε j * ‖c (xP k₁)‖ * δP k₁ j ^ j / j ! := by
  rcases h.phase1_end.1 with h0 | ⟨hk1, hcrit⟩
  · exact absurd h0 (not_le.2 (by simpa using hc))
  · refine ⟨hk1, h.phase1.radius_mem k₁ hk1 h.phase1_end.2, fun j hj => ?_⟩
    have := hcrit j hj
    rwa [phase1Tol_of_ne θ ε (by have := (Finset.mem_Icc.1 hj).1; omega)] at this

/-- `τ⁻¹ ε ‖r‖ δ^j/j! = ε ‖(1, y)‖ δ^j/j!` for `τ = f(x) - t > 0` and `y = -c(x)/τ`. -/
private theorem inv_mul_le_of_le {x : ℝⁿ} {t a ε δ : ℝ} {j : ℕ} (ht : t < f x)
    (hφ : a ≤ ε * Constrained.targetResidual f c t x * δ ^ j / j !) :
    (f x - t)⁻¹ * a ≤
      ε * √(1 + ‖Constrained.targetMultiplier f c t x‖ ^ 2) * δ ^ j / j ! := by
  have hτ : 0 < f x - t := sub_pos.2 ht
  have hdiv := Constrained.targetResidual_div_eq_sqrt (f := f) (c := c) ht
  rw [add_comm (1 : ℝ)]
  calc (f x - t)⁻¹ * a ≤ (f x - t)⁻¹ * (ε * Constrained.targetResidual f c t x * δ ^ j / j !) :=
        mul_le_mul_of_nonneg_left hφ (inv_nonneg.2 hτ.le)
    _ = ε * (Constrained.targetResidual f c t x / (f x - t)) * δ ^ j / j ! := by
        field_simp
    _ = _ := by rw [hdiv]

/-- **Lemma 14.3.5** of [cartis2022evaluation] (consequences of the termination of TPqp-GC),
**corrected**. Assume c.D1pLB.X and f.D1pLB.X on `X₀` with `q ≤ p`. For a TPqp-GC run:

* (Phase-1 exit, (14.3.41)) if `‖c(x₁)‖ > θε₀`, then
  `φ^{δ_j}_{ν,X(x₁),j}(x₁) ≤ ε_j ‖c(x₁)‖ δ_j^j/j!` for `j ∈ [1 : q]`, with the radii
  `δ ∈ (0, 1]^q` of Phase 1;
* (Phase-2 exit) if Phase 2 terminates at `k_ε` with output `x_ε = x_{k_ε+1}`,
  `t_ε = targetOut k_ε` and radii `δ = δ_{k_ε+1}`, then `t_ε ≤ f(x_ε)` (14.3.48) and:
  - if `f(x_ε) = t_ε`: `θε₀ ≤ ‖c(x_ε)‖ ≤ ε₀` and `φ^{δ_1}_{ν,X(x_ε),1}(x_ε) ≤ ε_1 ‖c(x_ε)‖ δ_1`
    (the first-order part of (14.3.41), with `≥ θε₀` instead of the printed `> θε₀`);
  - if `f(x_ε) > t_ε`, with `τ = f(x_ε) - t_ε` and `y_ε = -c(x_ε)/τ` (14.3.53):
    `‖c(x_ε)‖ ≤ ε₀`, `⟪y_ε, c(x_ε)⟫ ≤ 0`,
    (14.3.42) `φ^{δ_1}_{ℒ,X(x_ε),1}(x_ε, y_ε) ≤ ε_1 ‖(1, y_ε)‖ δ_1`; if `q ≥ 2`,
    (14.3.44) `φ^{δ_2}_{ℒ,M(x_ε),2} ≤ ½ ε_2 ‖(1, y_ε)‖ δ_2²` and the corrected (14.3.43)
    `φ^{δ_2}_{ℒ,T(x_ε),2} ≤ ½ ε_2 ‖(1, y_ε)‖ δ_2² + (‖∇f(x_ε)‖ δ_2)²/(2τ)`; if `q ≥ 3`,
    (14.3.47) `φ^{δ_3}_{ℒ,M(x_ε),3} ≤ ⅙ ε_3 ‖(1, y_ε)‖ δ_3³` and the corrected (14.3.46)
    `φ^{δ_3}_{ℒ,T(x_ε),3} ≤ ⅙ ε_3 ‖(1, y_ε)‖ δ_3³ +
      (‖∇f(x_ε)‖ δ_3 + ‖∇²f(x_ε)‖ δ_3²) ‖∇f(x_ε)‖ δ_3/(2τ)`.

Here `T(x) = X(x) ∩ ker ∇c(x)`, `M(x) = T(x) ∩ ker ∇f(x)` (14.3.45) and
`‖(1, y)‖ = √(1 + ‖y‖²)`. Corrections: the printed (14.3.43), (14.3.46) bound the extra terms by
`φ_{ℒ,1} ‖∇f‖ δ`, which is invalid (on `T(x_ε)`, `∇ℒ[d] = ∇f[d]`, not `∇f[d]/τ`; see
`lemma_14_3_5_counterexample`); when `f(x_ε) = t_ε`, Phase 2 only
gives `‖c(x_ε)‖ ≥ θε₀`, and the measures of `ν` and `μ` agree only at first order: for
`j = 2, 3` they agree on `X(x_ε) ∩ ker ∇f(x_ε)`, and on `X(x_ε)` they differ by the terms
`(‖∇f‖δ)²/2` and `‖∇f‖δ ‖∇²f‖δ²/2` (`Constrained.taylorMeasure_halfSqNorm_two_le_of_eq`,
`Constrained.taylorMeasure_halfSqNorm_three_le_of_eq`); so the higher-order part of (14.3.41) holds
only in these corrected forms. Only the smoothness parts of c.D1pLB.X and f.D1pLB.X (`C^q` near
`x_ε`) are
used. -/
theorem lemma_14_3_5 (h : algorithm_14_3_2 f c X q θ β₁ β ε x₀ xP δP k₁ D) {Lc Bc Lf Bf : ℕ → ℝ}
    (hcB : AssumptionCD1pLBX c X X₀ p Lc Bc) (hfB : AssumptionD1pLBX f X X₀ p Lf Bf)
    (hqp : q ≤ p) :
    (θ * ε 0 < ‖c (xP k₁)‖ →
      (∀ j ∈ Finset.Icc 1 q, 0 < δP k₁ j ∧ δP k₁ j ≤ 1) ∧
      ∀ j ∈ Finset.Icc 1 q, Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 c) (xP k₁)) j
        (δP k₁ j) {d | xP k₁ + d ∈ X} ≤ ε j * ‖c (xP k₁)‖ * δP k₁ j ^ j / j !) ∧
    (‖c (xP k₁)‖ ≤ θ * ε 0 → ∀ kε, D.IsEnd f c X q θ ε kε →
      D.targetOut f c θ ε kε ≤ f (D.x (kε + 1)) ∧
      (f (D.x (kε + 1)) = D.targetOut f c θ ε kε →
        θ * ε 0 ≤ ‖c (D.x (kε + 1))‖ ∧ ‖c (D.x (kε + 1))‖ ≤ ε 0 ∧
        (1 ≤ q → Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 c) (D.x (kε + 1))) 1
          (D.δ (kε + 1) 1) {d | D.x (kε + 1) + d ∈ X} ≤
            ε 1 * ‖c (D.x (kε + 1))‖ * D.δ (kε + 1) 1) ∧
        (2 ≤ q →
          Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 c) (D.x (kε + 1))) 2
              (D.δ (kε + 1) 2)
              ({d | D.x (kε + 1) + d ∈ X} ∩ {d | fderiv ℝ f (D.x (kε + 1)) d = 0}) ≤
            ε 2 * ‖c (D.x (kε + 1))‖ * D.δ (kε + 1) 2 ^ 2 / 2 ∧
          Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 c) (D.x (kε + 1))) 2
              (D.δ (kε + 1) 2) {d | D.x (kε + 1) + d ∈ X} ≤
            ε 2 * ‖c (D.x (kε + 1))‖ * D.δ (kε + 1) 2 ^ 2 / 2 +
              (‖fderiv ℝ f (D.x (kε + 1))‖ * D.δ (kε + 1) 2) ^ 2 / 2) ∧
        (3 ≤ q →
          Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 c) (D.x (kε + 1))) 3
              (D.δ (kε + 1) 3)
              ({d | D.x (kε + 1) + d ∈ X} ∩ {d | fderiv ℝ f (D.x (kε + 1)) d = 0}) ≤
            ε 3 * ‖c (D.x (kε + 1))‖ * D.δ (kε + 1) 3 ^ 3 / 6 ∧
          Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 c) (D.x (kε + 1))) 3
              (D.δ (kε + 1) 3) {d | D.x (kε + 1) + d ∈ X} ≤
            ε 3 * ‖c (D.x (kε + 1))‖ * D.δ (kε + 1) 3 ^ 3 / 6 +
              (‖fderiv ℝ f (D.x (kε + 1))‖ * D.δ (kε + 1) 3) ^ 2 / 2 +
              ‖fderiv ℝ f (D.x (kε + 1))‖ * D.δ (kε + 1) 3 *
                (‖iteratedFDeriv ℝ 2 f (D.x (kε + 1))‖ * D.δ (kε + 1) 3 ^ 2) / 2)) ∧
      (D.targetOut f c θ ε kε < f (D.x (kε + 1)) →
        ‖c (D.x (kε + 1))‖ ≤ ε 0 ∧
        ⟪Constrained.targetMultiplier f c (D.targetOut f c θ ε kε) (D.x (kε + 1)),
          c (D.x (kε + 1))⟫ ≤ 0 ∧
        (1 ≤ q → Optimization.taylorMeasure (ftaylorSeries ℝ (innerLagrangian f c
            (Constrained.targetMultiplier f c (D.targetOut f c θ ε kε) (D.x (kε + 1))))
            (D.x (kε + 1))) 1 (D.δ (kε + 1) 1) {d | D.x (kε + 1) + d ∈ X} ≤
          ε 1 * √(1 + ‖Constrained.targetMultiplier f c (D.targetOut f c θ ε kε)
            (D.x (kε + 1))‖ ^ 2) * D.δ (kε + 1) 1) ∧
        (2 ≤ q →
          Optimization.taylorMeasure (ftaylorSeries ℝ (innerLagrangian f c
              (Constrained.targetMultiplier f c (D.targetOut f c θ ε kε) (D.x (kε + 1))))
              (D.x (kε + 1))) 2 (D.δ (kε + 1) 2)
              ({d | D.x (kε + 1) + d ∈ X} ∩ {d | fderiv ℝ c (D.x (kε + 1)) d = 0} ∩
                {d | fderiv ℝ f (D.x (kε + 1)) d = 0}) ≤
            ε 2 * √(1 + ‖Constrained.targetMultiplier f c (D.targetOut f c θ ε kε)
              (D.x (kε + 1))‖ ^ 2) * D.δ (kε + 1) 2 ^ 2 / 2 ∧
          Optimization.taylorMeasure (ftaylorSeries ℝ (innerLagrangian f c
              (Constrained.targetMultiplier f c (D.targetOut f c θ ε kε) (D.x (kε + 1))))
              (D.x (kε + 1))) 2 (D.δ (kε + 1) 2)
              ({d | D.x (kε + 1) + d ∈ X} ∩ {d | fderiv ℝ c (D.x (kε + 1)) d = 0}) ≤
            ε 2 * √(1 + ‖Constrained.targetMultiplier f c (D.targetOut f c θ ε kε)
              (D.x (kε + 1))‖ ^ 2) * D.δ (kε + 1) 2 ^ 2 / 2 +
              (‖fderiv ℝ f (D.x (kε + 1))‖ * D.δ (kε + 1) 2) ^ 2 /
                (2 * (f (D.x (kε + 1)) - D.targetOut f c θ ε kε))) ∧
        (3 ≤ q →
          Optimization.taylorMeasure (ftaylorSeries ℝ (innerLagrangian f c
              (Constrained.targetMultiplier f c (D.targetOut f c θ ε kε) (D.x (kε + 1))))
              (D.x (kε + 1))) 3 (D.δ (kε + 1) 3)
              ({d | D.x (kε + 1) + d ∈ X} ∩ {d | fderiv ℝ c (D.x (kε + 1)) d = 0} ∩
                {d | fderiv ℝ f (D.x (kε + 1)) d = 0}) ≤
            ε 3 * √(1 + ‖Constrained.targetMultiplier f c (D.targetOut f c θ ε kε)
              (D.x (kε + 1))‖ ^ 2) * D.δ (kε + 1) 3 ^ 3 / 6 ∧
          Optimization.taylorMeasure (ftaylorSeries ℝ (innerLagrangian f c
              (Constrained.targetMultiplier f c (D.targetOut f c θ ε kε) (D.x (kε + 1))))
              (D.x (kε + 1))) 3 (D.δ (kε + 1) 3)
              ({d | D.x (kε + 1) + d ∈ X} ∩ {d | fderiv ℝ c (D.x (kε + 1)) d = 0}) ≤
            ε 3 * √(1 + ‖Constrained.targetMultiplier f c (D.targetOut f c θ ε kε)
              (D.x (kε + 1))‖ ^ 2) * D.δ (kε + 1) 3 ^ 3 / 6 +
              (‖fderiv ℝ f (D.x (kε + 1))‖ * D.δ (kε + 1) 3 +
                ‖iteratedFDeriv ℝ 2 f (D.x (kε + 1))‖ * D.δ (kε + 1) 3 ^ 2) *
                (‖fderiv ℝ f (D.x (kε + 1))‖ * D.δ (kε + 1) 3) /
                (2 * (f (D.x (kε + 1)) - D.targetOut f c θ ε kε))))) := by
  refine ⟨fun hc => (h.phase1_exit hc).2, fun hc1 kε hend => ?_⟩
  have h2 := h.phase2 hc1
  set xε := D.x (kε + 1) with hxε
  set tε := D.targetOut f c θ ε kε with htε
  set δε := D.δ (kε + 1) with hδε
  obtain ⟨hθr, hr, hft, hcrit⟩ := h2.output_spec hend
  obtain ⟨hk1, -, hbef⟩ := hend
  have hxX : xε ∈ X := h2.mem_succ kε hk1 hbef
  have hrad := h2.radius_mem kε hk1 hbef
  have hS : (0 : ℝⁿ) ∈ {d | xε + d ∈ X} := by simpa using hxX
  have hfC : ∀ {i : ℕ}, i ≤ q → ContDiffAt ℝ i f xε := fun hi =>
    (hfB.contDiffOn.contDiffAt (hfB.isOpen.mem_nhds (hfB.subset hxX))).of_le
      (by exact_mod_cast hi.trans hqp)
  have hcC : ∀ {i : ℕ}, i ≤ q → ContDiffAt ℝ i c xε := fun hi =>
    (hcB.contDiffOn.contDiffAt (hcB.isOpen.mem_nhds (hcB.subset hxX))).of_le
      (by exact_mod_cast hi.trans hqp)
  refine ⟨hft, fun heq => ?_, fun hlt => ?_⟩
  · -- `f(x_ε) = t_ε`
    have hrc : Constrained.targetResidual f c tε xε = ‖c xε‖ := by
      rw [← heq]; exact Constrained.targetResidual_self
    rw [hrc] at hθr hr
    refine ⟨hθr, hr, fun hq => ?_, fun hq => ?_, fun hq => ?_⟩
    · have hj : (1 : ℕ) ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, hq⟩
      have := hcrit 1 hj
      rw [Constrained.taylorMeasure_one_targetMerit_of_eq ((hfC hq).differentiableAt one_ne_zero)
        ((hcC hq).differentiableAt one_ne_zero) heq, hrc] at this
      simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one] at this
      exact this
    · have hj : (2 : ℕ) ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨by norm_num, hq⟩
      have := hcrit 2 hj
      rw [hrc] at this
      norm_num [Nat.factorial] at this
      exact Constrained.taylorMeasure_halfSqNorm_two_le_of_eq (hfC hq) (hcC hq) heq (hrad 2 hj).1.le
        hS this
    · have hj : (3 : ℕ) ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨by norm_num, hq⟩
      have := hcrit 3 hj
      rw [hrc] at this
      norm_num [Nat.factorial] at this
      exact Constrained.taylorMeasure_halfSqNorm_three_le_of_eq (hfC hq) (hcC hq) heq
        (hrad 3 hj).1.le hS this
  · -- `f(x_ε) > t_ε`
    have hτ : 0 < f xε - tε := sub_pos.2 hlt
    refine ⟨Constrained.norm_le_targetResidual.trans hr,
      Constrained.inner_targetMultiplier_nonpos hlt.le, fun hq => ?_, fun hq => ?_,
      fun hq => ?_⟩
    · have hj : (1 : ℕ) ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, hq⟩
      have hφ := hcrit 1 hj
      rw [Constrained.taylorMeasure_lagrangian_one_eq ((hfC hq).differentiableAt one_ne_zero)
        ((hcC hq).differentiableAt one_ne_zero) hlt]
      simpa using inv_mul_le_of_le hlt hφ
    · have hj : (2 : ℕ) ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨by norm_num, hq⟩
      have hφ := hcrit 2 hj
      have hδ := (hrad 2 hj).1
      have hG : ∀ d ∈ closedBall (0 : ℝⁿ) (δε 2) ∩
          ({d | xε + d ∈ X} ∩ {d | fderiv ℝ c xε d = 0}),
          |fderiv ℝ f xε d| ≤ ‖fderiv ℝ f xε‖ * δε 2 := fun d hd => by
        rw [← Real.norm_eq_abs]
        exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left
          (mem_closedBall_zero_iff.1 hd.1) (norm_nonneg _))
      refine ⟨(Constrained.taylorMeasure_lagrangian_two_le_of_ker (hfC hq) (hcC hq) hlt hδ.le
        hS).trans ?_, (Constrained.taylorMeasure_lagrangian_two_le (hfC hq) (hcC hq) hlt hδ.le
        hS hG).trans ?_⟩
      · simpa using inv_mul_le_of_le hlt hφ
      · rw [mul_add]
        have := inv_mul_le_of_le hlt hφ
        have e : (f xε - tε)⁻¹ * ((‖fderiv ℝ f xε‖ * δε 2) ^ 2 / 2) =
            (‖fderiv ℝ f xε‖ * δε 2) ^ 2 / (2 * (f xε - tε)) := by
          field_simp
        simp only [Nat.factorial_two, Nat.cast_ofNat] at this
        linarith
    · have hj : (3 : ℕ) ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨by norm_num, hq⟩
      have hφ := hcrit 3 hj
      have hδ := (hrad 3 hj).1
      have hG : ∀ d ∈ closedBall (0 : ℝⁿ) (δε 3) ∩
          ({d | xε + d ∈ X} ∩ {d | fderiv ℝ c xε d = 0}),
          |fderiv ℝ f xε d| ≤ ‖fderiv ℝ f xε‖ * δε 3 := fun d hd => by
        rw [← Real.norm_eq_abs]
        exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left
          (mem_closedBall_zero_iff.1 hd.1) (norm_nonneg _))
      have hH : ∀ d ∈ closedBall (0 : ℝⁿ) (δε 3) ∩
          ({d | xε + d ∈ X} ∩ {d | fderiv ℝ c xε d = 0}),
          |iteratedFDeriv ℝ 2 f xε (fun _ => d)| ≤
            ‖iteratedFDeriv ℝ 2 f xε‖ * δε 3 ^ 2 := fun d hd => by
        rw [← Real.norm_eq_abs]
        refine ((iteratedFDeriv ℝ 2 f xε).le_opNorm _).trans ?_
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
          (mem_closedBall_zero_iff.1 hd.1) 2) (norm_nonneg _)
      refine ⟨(Constrained.taylorMeasure_lagrangian_three_le_of_ker (hfC hq) (hcC hq) hlt hδ.le
        hS).trans ?_, (Constrained.taylorMeasure_lagrangian_three_le (hfC hq) (hcC hq) hlt hδ.le
        hS hG hH).trans ?_⟩
      · have := inv_mul_le_of_le hlt hφ
        simpa [Nat.factorial] using this
      · rw [mul_add]
        have := inv_mul_le_of_le hlt hφ
        have e : (f xε - tε)⁻¹ * ((‖fderiv ℝ f xε‖ * δε 3 +
              ‖iteratedFDeriv ℝ 2 f xε‖ * δε 3 ^ 2) * (‖fderiv ℝ f xε‖ * δε 3) / 2) =
            (‖fderiv ℝ f xε‖ * δε 3 + ‖iteratedFDeriv ℝ 2 f xε‖ * δε 3 ^ 2) *
              (‖fderiv ℝ f xε‖ * δε 3) / (2 * (f xε - tε)) := by
          field_simp
        have h6 : ((3 : ℕ)! : ℝ) = 6 := by norm_num [Nat.factorial]
        rw [h6] at this
        linarith

/-- **Lemma 14.3.7** of [cartis2022evaluation] (evaluation complexity of Phase 1 of TPqp-GC, with
the correction of Theorem 14.3.4). Phase 1 terminates at `x₁` with `‖c(x₁)‖ ≤ θε₀` or
`φ^{δ_j}_{ν,X(x₁),j}(x₁) ≤ ε_j ‖c(x₁)‖ δ_j^j/j!` for `j ∈ [1 : q]` and some `δ ∈ (0, 1]^q`
(14.3.64). If the cost of the `k`-th INNER call of Phase 1 (evaluations of `c`, or of its
derivatives) satisfies the contract (14.3.20) (resp. (14.3.21)) for `ν` with constant `κ ≥ 0`
(by Lemma 14.3.6(i) such constants exist depending on the constants of c.D1pLB.X and on
`‖c(x₀)‖`) and exponents `π_j > 1`, then the total cost of Phase 1 is at most
`½ κ ‖c(x₀)‖ ∑_{j=1}^q β₁^{1-2π_j}/(β₁^{1-π_j} - 1) θ^{1-π_j} ε₀^{1-π_j} ε_j^{-π_j}`
((14.3.65)–(14.3.66) with `∑_j` in place of `max_j`). -/
theorem lemma_14_3_7 (h : algorithm_14_3_2 f c X q θ β₁ β ε x₀ xP δP k₁ D) (hθ : 0 < θ)
    {π : ℕ → ℝ} (hπ : ∀ j ∈ Finset.Icc 1 q, 1 < π j) {κ : ℝ} (hκ : 0 ≤ κ) {cost : ℕ → ℝ}
    (hcost : ∀ k ∈ Finset.Icc 1 k₁, cost k ≤ innerEvalBound κ π q (phi2 c (xP (k - 1)))
      (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j)) :
    (‖c (xP k₁)‖ ≤ θ * ε 0 ∨ ∃ δ' : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, 0 < δ' j ∧ δ' j ≤ 1) ∧
      ∀ j ∈ Finset.Icc 1 q, Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 c) (xP k₁)) j
        (δ' j) {d | xP k₁ + d ∈ X} ≤ ε j * ‖c (xP k₁)‖ * δ' j ^ j / j !) ∧
    ∑ k ∈ Finset.Icc 1 k₁, cost k ≤
      1 / 2 * κ * ‖c (x₀)‖ * ∑ j ∈ Finset.Icc 1 q,
        β₁ ^ (1 - 2 * π j) / (β₁ ^ (1 - π j) - 1) * θ ^ (1 - π j) * ε 0 ^ (1 - π j) *
          ε j ^ (-π j) := by
  have hε₀ : 0 < ε 0 := by
    have := h.phase1.ε_pos 0 (by simp)
    rw [phase1Tol_zero] at this
    exact pos_of_mul_pos_right this hθ.le
  refine ⟨?_, ?_⟩
  · rcases h.phase1_end.1 with h0 | ⟨hk1, hcrit⟩
    · exact Or.inl (by simpa using h0)
    · refine Or.inr ⟨δP k₁, h.phase1.radius_mem k₁ hk1 h.phase1_end.2, fun j hj => ?_⟩
      have := hcrit j hj
      rwa [phase1Tol_of_ne θ ε (by have := (Finset.mem_Icc.1 hj).1; omega)] at this
  · have hmain := theorem_14_3_4 h.phase1 h.phase1_end hπ hκ hcost
    rw [h.start] at hmain
    refine hmain.trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [phase1Tol_zero, phase1Tol_of_ne θ ε (by have := (Finset.mem_Icc.1 hj).1; omega),
      Real.mul_rpow hθ.le hε₀.le]
    ring

/-- **Lemma 14.3.7 with an additive per-call constant** (as `theorem_14_3_4_add`): if the cost of
the `k`-th Phase-1 INNER call satisfies the contract (14.3.20) for `ν` up to an additive constant
`a`, the Phase-1 total is at most the bound of `lemma_14_3_7` plus `k₁ a`. -/
theorem lemma_14_3_7_add (h : algorithm_14_3_2 f c X q θ β₁ β ε x₀ xP δP k₁ D) (hθ : 0 < θ)
    {π : ℕ → ℝ} (hπ : ∀ j ∈ Finset.Icc 1 q, 1 < π j) {κ a : ℝ} (hκ : 0 ≤ κ) {cost : ℕ → ℝ}
    (hcost : ∀ k ∈ Finset.Icc 1 k₁, cost k ≤ innerEvalBound κ π q (phi2 c (xP (k - 1)))
      (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j) + a) :
    ∑ k ∈ Finset.Icc 1 k₁, cost k ≤
      1 / 2 * κ * ‖c (x₀)‖ * ∑ j ∈ Finset.Icc 1 q,
        β₁ ^ (1 - 2 * π j) / (β₁ ^ (1 - π j) - 1) * θ ^ (1 - π j) * ε 0 ^ (1 - π j) *
          ε j ^ (-π j) + k₁ * a := by
  have := (lemma_14_3_7 h hθ hπ hκ (cost := fun k => cost k - a) fun k hk => by
    linarith [hcost k hk]).2
  rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul,
    Nat.add_sub_cancel] at this
  linarith

end Termination


/-! ### Lemma 14.3.8 and Theorem 14.3.9: evaluation complexity of TPqp-GC -/

/-- **The INNER contract of the proof of Lemma 14.3.8** ([cartis2022evaluation], Lemmas
14.2.2–14.2.3 applied to `μ(·, t_k)`, with constants independent of `t_k` by Lemma 14.3.6(ii);
`Constrained.HighOrderTargetSeq.IsEndCritContract`): for every outer iteration `k ≥ 1` reached,
(count) `e_k ≤ κ_uns |𝒮_k| + κ_unc` (14.2.13); (stay) unsuccessful inner iterations do not move;
(decrease) every successful inner iteration `i` with `i + 1 < e_k`, or ending a call at a point
failing the third test of (14.3.32), whose new iterate has residual `‖r(x_{k,i+1}, t_k)‖ ≥ θε₀`,
decreases `μ(·, t_k)` by at least `κ_decr min_l (β ‖r(x_k, t_k)‖ ε_l)^{π_l}` ((14.2.11) for INNER
called with tolerances `β ‖r(x_k, t_k)‖ ε_l`; "so long as the third termination test in (14.3.32)
has not been satisfied", (B.14.21)). This exemption is weaker than what INNER runs satisfy
(Lemma 14.2.2 exempts only steps after which INNER's own test (14.3.19) holds,
`IsInnerPhaseRunStrong`), and too weak to bound the bad outer iterations
(`lemma_14_3_8_proof_gap_counterexample`). -/
abbrev IsInnerPhaseRun (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (X : Set ℝⁿ) (q : ℕ) (θ β : ℝ)
    (ε : ℕ → ℝ) (D : TPqpSeq n) (κdecr κuns κunc : ℝ) (π : ℕ → ℝ) : Prop :=
  D.IsEndCritContract f c X q θ β ε κdecr κuns κunc π

/-- **The INNER contract of Phase 2 keyed on INNER's own test** ([cartis2022evaluation],
Lemmas 14.2.2–14.2.3 as stated, for INNER on `μ(·, t_k)`;
`Constrained.HighOrderTargetSeq.IsInnerTestContract`), with radii bounded below by `ρ`: as
`IsInnerPhaseRun`, except that the decrease is required unless the call ends (by any test of
(14.3.32)) at a point passing INNER's test (14.3.19) (`Constrained.HighOrderTargetSeq.InnerTest`),
and a case-(b) call ending at a point passing (14.3.19) returns radii `δ_{k+1,j} ≥ ρ_j`. -/
abbrev IsInnerPhaseRunStrong (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (X : Set ℝⁿ) (q : ℕ) (θ β : ℝ)
    (ε : ℕ → ℝ) (D : TPqpSeq n) (κdecr κuns κunc : ℝ) (π ρ : ℕ → ℝ) : Prop :=
  D.IsInnerTestContract f c X q θ β ε κdecr κuns κunc π ρ

section Complexity

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {q : ℕ} {θ β : ℝ} {ε : ℕ → ℝ} {x₁ : ℝⁿ}
  {D : TPqpSeq n} {κdecr κuns κunc πmax M : ℝ} {π : ℕ → ℝ}

/-- **Lemma 14.3.8** of [cartis2022evaluation] (bounds on the inner iterations of Phase 2),
**corrected**. Let the INNER calls of Phase 2 satisfy the contract `IsInnerPhaseRun` with
`κ_decr > 0`, exponents `0 ≤ π_l ≤ π_max`, and let `M > 0` bound
`ε₀^{2-π_l} ε_l^{-π_l}` for `l ∈ [1 : q]` (the book's `max_l`). For every outer iteration
`K ≥ 1` reached:
(i) the `k`-th call has at most `|good_k| + 1` successful iterations and
`e_k ≤ κ_uns |𝒮_k| + κ_unc` (`κ_unc` is paid per call, each INNER call being a fresh run);
(ii) the number of good inner iterations of `[1, K]` is at most
`G (|𝒦_a ∩ [1, K)| + 1)` with `G = κ^S (1 - θ) M`, `κ^S = κ_decr⁻¹ (βθ)^{-π_max}` (14.3.71)
(the book's per-block bound, summed over the at most `|𝒦_a ∩ [1, K)| + 1` blocks of outer
iterations between consecutive elements of `𝒦_a`);
(iii) `K ≤ |𝒦_a ∩ [1, K)| + |good iterations of [1, K]| + |bad ∩ [1, K)| + 1`.
The printed lemma bounds `|𝓘_k^s|` by `G` per block: this also counts the `i = 0` elements and
the last iterations of the INNER calls, which have no guaranteed decrease, and the number of bad
calls of `𝒦_b` (`Constrained.HighOrderTargetSeq.IsBad`) is not bounded by the printed argument
(as in Lemma 7.2.6). The smoothness and boundedness assumptions of the book only serve to justify
the contract (Lemmas 14.2.2–14.2.3 and 14.3.6). -/
theorem lemma_14_3_8 (h : IsTPqpGCPhase2 f c X q θ β ε x₁ D)
    (hin : IsInnerPhaseRun f c X q θ β ε D κdecr κuns κunc π) (hκ : 0 < κdecr)
    (hπ : ∀ l ∈ Finset.Icc 1 q, 0 ≤ π l ∧ π l ≤ πmax) (hM0 : 0 < M)
    (hM : ∀ l ∈ Finset.Icc 1 q, ε 0 ^ (2 - π l) * ε l ^ (-π l) ≤ M) {K : ℕ} (hK1 : 1 ≤ K)
    (hK : D.Before f c X q θ ε K) :
    (∀ k, 1 ≤ k → k ≤ K → D.succCount k ≤ D.goodCount f c X q θ ε k + 1 ∧
      (D.e k : ℝ) ≤ κuns * D.succCount k + κunc) ∧
    (∑ k ∈ Finset.Icc 1 K, D.goodCount f c X q θ ε k : ℝ) ≤
      Constrained.goodBound κdecr β θ πmax M * (D.kaCount f c θ ε K + 1) ∧
    K ≤ D.kaCount f c θ ε K + ∑ k ∈ Finset.Icc 1 K, D.goodCount f c X q θ ε k +
      D.badCount f c X q θ ε K + 1 := by
  refine ⟨fun k hk1 hkK => ⟨h.toRun.succCount_le (succ := D.succ) hk1 (hK.mono hkK),
    hin.count k hk1 (hK.mono hkK)⟩, ?_, Constrained.TargetFollowingSeq.le_counts hK⟩
  rw [h.goodBound_eq hκ hM0]
  exact_mod_cast (hin.toContract h hκ hπ hM0 hM).sum_goodCount_le h.toRun
    (h.goodDecr_pos hκ hM0) hK1 hK

/-- **Theorem 14.3.9** of [cartis2022evaluation] (complexity of TPqp-GC), **corrected**, for an
abstract INNER satisfying the contracts of both phases. Phase 1: the costs `nF₁ k`, `nD₁ k` of
the `k`-th Phase-1 call satisfy the cost contract (14.3.20)–(14.3.21) for `ν` up to additive
constants `a_F`, `a_D` (constants `κF₁, κD₁ ≥ 0`, exponents `π_j > 1`). Phase 2: the calls
satisfy the INNER contract keyed on INNER's own test (14.3.19) (`IsInnerPhaseRunStrong`:
`κ_decr > 0`, `κ_uns ≥ 0`, `0 ≤ π_l ≤ π_max`, radii of the case-(b) calls passing (14.3.19) at
least `ρ_j ≥ 0`; the calls may be cut by any test of (14.3.32)), with `M > 0` bounding
`ε₀^{2-π_l} ε_l^{-π_l}`. Assume f.B.Fb on `ℱ_{β_F}` with `ε₀ ≤ β_F`, `f` and `c` of class `C^q`
at the points of `X` with `‖∇^i f‖ ≤ B_f` (`i ∈ [1 : q]`) at the points of `X` with `‖c‖ ≤ ε₀`,
and let `τ > 0` satisfy `2 B_f τ ≤ η ε_j ρ_j^{j-1}/j!` (`η = θ(1 - θ)ε₀/(1 + θ)`, `kbMargin`).
Write `N_a = (f_up - f_low + 1)/((1 - θ)ε₀)`, `G = κ^S (1 - θ) M` (Lemma 14.3.8) and
`N_b = N_a + 1 + (f_up - f_low + 1)/τ`. Then:
(Phase 1) the costs of Phase 1 are at most
`½ κ ‖c(x₀)‖ ∑_j β₁^{1-2π_j}/(β₁^{1-π_j} - 1) θ^{1-π_j} ε₀^{1-π_j} ε_j^{-π_j} + k₁ a`
(Lemma 14.3.7, with `k₁ ≤ ⌈log(θε₀/‖c(x₀)‖)/log β₁⌉₊` by Theorem 14.3.3);
(Phase 2) if Phase 2 is entered, every outer iteration `K ≥ 1` reached satisfies
`K ≤ (N_a + 1)(G + 1) + N_b`, and Phase 2 terminates at some `k_ε ≤ (N_a + 1)(G + 1) + N_b`,
using at most `1 + G (N_a + 1) + k_ε` derivative evaluations and
`1 + κ_uns (G (N_a + 1) + k_ε) + κ_unc k_ε` evaluations of `(f, c)`
(`Constrained.IsHighOrderTargetRun.complexity_of_innerTest`).
Fixes relative to the printed theorem:
* the counting gap of Lemma 14.3.8: the bad outer iterations (case (b) without a counted inner
  iteration) are not bounded by the book's argument, and the decreases its proof uses
  (`IsInnerPhaseRun`) do not bound them (`lemma_14_3_8_proof_gap_counterexample`); with the
  contract as Lemma 14.2.2 states it (`IsInnerPhaseRunStrong`) the case-(b) calls ending at a
  point passing (14.3.19) are bounded by the target-drop margin argument, which gives the extra
  term `N_b = O(ε₀^{-1} + max_j (ε₀ ε_j ρ_j^{j-1})^{-1})`, whose order depends on the INNER radii
  (`theorem_14_3_9_arqpc`, `theorem_14_3_9_arqp`, `theorem_14_3_9_trq` for the realizations of
  INNER); the bound with the number of bad iterations as a parameter, under the weaker contract,
  is `Constrained.IsHighOrderTargetRun.complexity`;
* `∑_j` replaces `max_j` in Phase 1 (as in Theorem 14.3.4);
* `f_up - f_low + 1` replaces the printed `f_up - f_low - 1`;
* the derivative count acquires the term `ε₀^{-1}` (one successful iteration per outer iteration
  that moves), and the term `κ^C ε₀^{-1}` of `#F₂` has the factor `1/(1 - θ)`;
* the Phase-1 cost contract is additive: the multiplicative contract (14.3.20)–(14.3.21) fails
  for INNER = ARqp-SC with `q = 1`, `p ≥ 2`, and for any INNER spending at least one evaluation
  per call when every `π_j < 2` (`exists_algorithm_14_3_1_cost_contract_counterexample`); it holds
  for ARqp-SC with the exponents `j + 1` and, with the ARqp-SC exponents, for `q ≥ 2`
  (`IsARqpSCOutputCost.cost_le_anchored`, `IsARqpSCOutputCost.cost_le_arqp_anchored`), while the
  additive one holds for ARqp-SC in all cases (`IsARqpSCOutputCost.cost_le_arqp_add_anchored`);
  `a = 0` is the printed contract;
* `κ_unc` is paid once per call, and the smoothness and boundedness assumptions only serve to
  justify the contracts (Lemmas 14.2.2–14.2.3 and 14.3.6). -/
theorem theorem_14_3_9 {β₁ : ℝ} {x₀ : ℝⁿ} {xP : ℕ → ℝⁿ} {δP : ℕ → ℕ → ℝ} {k₁ : ℕ}
    (h : algorithm_14_3_2 f c X q θ β₁ β ε x₀ xP δP k₁ D) (hθ : 0 < θ)
    (hπ1 : ∀ j ∈ Finset.Icc 1 q, 1 < π j) {κF₁ κD₁ aF aD : ℝ} (hκF₁ : 0 ≤ κF₁)
    (hκD₁ : 0 ≤ κD₁) {nF₁ nD₁ : ℕ → ℝ}
    (hnF₁ : ∀ k ∈ Finset.Icc 1 k₁, nF₁ k ≤ innerEvalBound κF₁ π q (phi2 c (xP (k - 1)))
      (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j) + aF)
    (hnD₁ : ∀ k ∈ Finset.Icc 1 k₁, nD₁ k ≤ innerEvalBound κD₁ π q (phi2 c (xP (k - 1)))
      (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j) + aD)
    {ρ : ℕ → ℝ} (hin : IsInnerPhaseRunStrong f c X q θ β ε D κdecr κuns κunc π ρ)
    (hκ : 0 < κdecr) (hκuns : 0 ≤ κuns) (hπ : ∀ l ∈ Finset.Icc 1 q, 0 ≤ π l ∧ π l ≤ πmax)
    (hM0 : 0 < M) (hM : ∀ l ∈ Finset.Icc 1 q, ε 0 ^ (2 - π l) * ε l ^ (-π l) ≤ M)
    {βF flow fup : ℝ} (hB : Chapter07.AssumptionBFb f c X βF flow fup) (hεβ : ε 0 ≤ βF)
    (hρ : ∀ j ∈ Finset.Icc 1 q, 0 ≤ ρ j) (hf : ∀ y ∈ X, ContDiffAt ℝ q f y)
    (hc : ∀ y ∈ X, ContDiffAt ℝ q c y) {Bf : ℝ}
    (hBf : ∀ y ∈ X, ‖c y‖ ≤ ε 0 → ∀ i ∈ Finset.Icc 1 q, ‖iteratedFDeriv ℝ i f y‖ ≤ Bf)
    {τ : ℝ} (hτ0 : 0 < τ)
    (hτ : ∀ j ∈ Finset.Icc 1 q, 2 * Bf * τ ≤ Constrained.kbMargin θ (ε 0) * ε j * ρ j ^ (j - 1) / j
        !) :
    (∑ k ∈ Finset.Icc 1 k₁, nF₁ k ≤ 1 / 2 * κF₁ * ‖c x₀‖ * ∑ j ∈ Finset.Icc 1 q,
        β₁ ^ (1 - 2 * π j) / (β₁ ^ (1 - π j) - 1) * θ ^ (1 - π j) * ε 0 ^ (1 - π j) *
          ε j ^ (-π j) + k₁ * aF) ∧
    (∑ k ∈ Finset.Icc 1 k₁, nD₁ k ≤ 1 / 2 * κD₁ * ‖c x₀‖ * ∑ j ∈ Finset.Icc 1 q,
        β₁ ^ (1 - 2 * π j) / (β₁ ^ (1 - π j) - 1) * θ ^ (1 - π j) * ε 0 ^ (1 - π j) *
          ε j ^ (-π j) + k₁ * aD) ∧
    (‖c (xP k₁)‖ ≤ θ * ε 0 →
      (∀ K, 1 ≤ K → D.Before f c X q θ ε K →
        (K : ℝ) ≤ ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) *
          (Constrained.goodBound κdecr β θ πmax M + 1) +
            ((fup - flow + 1) / ((1 - θ) * ε 0) + 1 + (fup - flow + 1) / τ)) ∧
      ∃ kε, D.IsEnd f c X q θ ε kε ∧
        (kε : ℝ) ≤ ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) *
          (Constrained.goodBound κdecr β θ πmax M + 1) +
            ((fup - flow + 1) / ((1 - θ) * ε 0) + 1 + (fup - flow + 1) / τ) ∧
        (D.derivEvals kε : ℝ) ≤
          1 + Constrained.goodBound κdecr β θ πmax M * ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) +
              kε ∧
        (D.funEvals kε : ℝ) ≤
          1 + κuns * (Constrained.goodBound κdecr β θ πmax M * ((fup - flow + 1) / ((1 - θ) * ε 0)
              + 1) +
            kε) + κunc * kε) :=
  ⟨lemma_14_3_7_add h hθ hπ1 hκF₁ hnF₁, lemma_14_3_7_add h hθ hπ1 hκD₁ hnD₁, fun hc1 =>
    (h.phase2 hc1).complexity_of_innerTest hin hκ hκuns hπ hM0 hM (hB.of_le hεβ) hρ hf hc hBf
      hτ0 hτ⟩

end Complexity


/-! ## Counterexamples for Lemmas 14.3.5 and 14.3.8

The counterexamples below (and those of `theorem_14_3_9_false` and
`theorem_14_3_9_arqp_counterexample`) are Phase-2 runs of the backbone examples
`Numlib.Optimization.Constrained.TwoPhase.HighOrder.Examples.*`, entered at once from a point `x₀`
with `‖c(x₀)‖ ≤ θε₀`. -/

/-- **Phase 1 stopping at once**: a Phase-2 run from `x₀` (so `x₀ ∈ X` and `‖c(x₀)‖ ≤ θε₀`) is a
run of TPqp-GC from `x₀` whose Phase 1 (LENq-SC on `ν`, any `β₁ ∈ (0, 1)`) stops at `k₁ = 0`. -/
theorem IsTPqpGCPhase2.algorithm_14_3_2_of_stop {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X : Set ℝⁿ}
    {q : ℕ} {θ β : ℝ} {ε : ℕ → ℝ} {x₀ : ℝⁿ} {D : TPqpSeq n}
    (h : IsTPqpGCPhase2 f c X q θ β ε x₀ D) {β₁ : ℝ} (hβ₁ : 0 < β₁) (hβ₁1 : β₁ < 1) :
    algorithm_14_3_2 f c X q θ β₁ β ε x₀ (fun _ => x₀) (fun _ _ => 1) 0 D := by
  have hθε : θ * ε 0 < 1 := by
    have := h.ε_le_one 0 (by simp)
    nlinarith [h.θ_lt_one, h.ε₀_pos]
  have hlen0 : lenStop c X q (phase1Tol θ ε) (fun _ => x₀) (fun _ _ => 1) 0 :=
    Or.inl (by rw [phase1Tol_zero]; exact h.norm_one_le)
  refine ⟨rfl, ⟨h.mem_one, fun j hj => ?_, fun j hj => ?_, hβ₁, hβ₁1, ?_,
    fun k _ h' => absurd hlen0 (h' 0 (by omega)), fun k _ h' => absurd hlen0 (h' 0 (by omega)),
    fun k _ h' => absurd hlen0 (h' 0 (by omega))⟩,
    ⟨hlen0, fun j hj => absurd hj (Nat.not_lt_zero _)⟩, fun _ => h⟩
  · unfold phase1Tol; split_ifs
    · exact mul_pos h.θ_pos h.ε₀_pos
    · exact h.ε_pos j hj
  · unfold phase1Tol; split_ifs
    · exact hθε.le
    · exact h.ε_le_one j hj
  · have := h.norm_one_le
    have := norm_nonneg (c x₀)
    nlinarith

/-! ### Lemma 14.3.5: counterexamples to the printed (14.3.43) and (14.3.46) -/

section Counterexample1435

local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

open Constrained.TwoPhaseExample

/-- c.D1pLB.X for `c ≡ 0` on `X = [-1, 1]` and `X₀ = B(0, 2)`. -/
private theorem interval_assumptionC (p : ℕ) :
    ∃ L B : ℕ → ℝ, AssumptionCD1pLBX Interval.con Interval.interval (ball 0 2) p L B := by
  obtain ⟨L, B, h⟩ := exists_assumptionD1pLBX_ball (g := fun _ : ℝ¹ => (0 : ℝ)) contDiff_const
    Interval.interval_subset_ball p
  refine ⟨L, B, isOpen_ball, convex_ball 0 2, Interval.interval_subset_ball, fun i => ?_⟩
  have e : (fun x => Interval.con x i) = fun _ => (0 : ℝ) := by funext x; simp [Interval.con]
  rw [e]; exact h

/-- **Lemma 14.3.5** of [cartis2022evaluation]: **the printed bounds (14.3.43) and (14.3.46) are
false.** There are TPqp-GC runs (`algorithm_14_3_2`) satisfying every hypothesis of Lemma 14.3.5
(c.D1pLB.X and f.D1pLB.X on `X₀ = B(0, 2)` with `q ≤ p`) whose Phase 2 terminates at `k_ε` with
`f(x_ε) > t_ε` and violates the printed bound:

* (`q = 2`, (14.3.43)) `φ^{δ_2}_{ℒ,T(x_ε),2}(x_ε, y_ε) >
  ½ [ε_2 ‖(1, y_ε)‖ δ_2² + φ^{δ_2}_{ℒ,X(x_ε),1}(x_ε, y_ε) ‖∇f(x_ε)‖ δ_2]`;
* (`q = 3`, (14.3.46)) `φ^{δ_3}_{ℒ,T(x_ε),3}(x_ε, y_ε) > ⅙ [ε_3 ‖(1, y_ε)‖ δ_3³ +
  3 φ^{δ_3}_{ℒ,X(x_ε),1}(x_ε, y_ε) (‖∇f(x_ε)‖ δ_3 + ‖∇²f(x_ε)‖ δ_3²)]`,

with `y_ε = -c(x_ε)/(f(x_ε) - t_ε)` (14.3.53) and `T(x) = X(x) ∩ ker ∇c(x)`. Moreover, the
INNER call of the terminating iteration returns its starting point (`x_{k_ε+1} = x_{k_ε}`), which
INNER may do, as its own termination test `φ^{δ_j}_{μ,X,j}(x_{k_ε+1}, t_{k_ε}) ≤
ε_j β ‖r(x_{k_ε}, t_{k_ε})‖ δ_j^j/j!` already holds there. The other standing assumptions of
§14.3.2 hold as well (not stated): X.CNe (`X = [-1, 1]` is closed and nonempty), f.B.Fb (`f` is
continuous, hence bounded, on the compact `ℱ_{β_F} ⊆ X`), and the INNER contract
`IsInnerPhaseRun` (with `κ_uns = κ_unc = 1` and any `κ_decr`, `π`: INNER makes no iterations;
`Constrained.TwoPhaseExample.Interval.isEndCritContract`).

The data (`n = m = 1`): `X = [-1, 1]`, `c ≡ 0` (so `ℒ = f`, `y_ε = 0`, `T(x_ε) = X(x_ε)`),
`θ = β₁ = β = ½`, `ε₀ = 1/100`, `ε_j = 1` (`j ≥ 1`), `x₀ = 0`; Phase 1 stops at once, Phase 2
starts at `x₁ = 0` with `t₁ = -ε₀` and terminates at `k_ε = 1` in case (c) with
`(x_ε, t_ε) = (0, -ε₀)`, radii `1` and `τ = f(x_ε) - t_ε = ε₀`
(`Constrained.TwoPhaseExample.Interval.isHighOrderTargetRun`).
For `q = 2`, `f(x) = x/4 - (25/8) x²`: `∇²μ(0) = ∇f(0)² + ε₀ ∇²f(0) = 0`, so the tests hold,
and `φ^1_{f,2}(0) ≥ 27/8` while the printed right-hand side is at most `½ (1 + 1/16) = 17/32`.
For `q = 3`, `f(x) = x/12 - (25/72) x² + (625/216) x³`: `∇²μ(0) = ∇³μ(0) = 0`, and
`φ^1_{f,3}(0) ≥ 718/216` while the printed right-hand side is at most `43/216`.
The corrected bounds of `lemma_14_3_5` (with `(‖∇f‖δ)²/(2τ)` and
`(‖∇f‖δ + ‖∇²f‖δ²)‖∇f‖δ/(2τ)`) hold, e.g. `½ + (1/4)²/(2ε₀) = 29/8 ≥ 27/8`. -/
theorem lemma_14_3_5_counterexample :
    (∃ (f : ℝ¹ → ℝ) (c : ℝ¹ → ℝ¹) (X X₀ : Set ℝ¹) (q p : ℕ) (θ β₁ β : ℝ) (ε : ℕ → ℝ)
      (x₀ : ℝ¹) (xP : ℕ → ℝ¹) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq 1)
      (Lc Bc Lf Bf : ℕ → ℝ) (kε : ℕ),
      algorithm_14_3_2 f c X q θ β₁ β ε x₀ xP δP k₁ D ∧
      AssumptionCD1pLBX c X X₀ p Lc Bc ∧ AssumptionD1pLBX f X X₀ p Lf Bf ∧ q ≤ p ∧ q = 2 ∧
      ‖c (xP k₁)‖ ≤ θ * ε 0 ∧ D.IsEnd f c X q θ ε kε ∧
      D.targetOut f c θ ε kε < f (D.x (kε + 1)) ∧ D.x (kε + 1) = D.x kε ∧
      (∀ j ∈ Finset.Icc 1 q, Optimization.taylorMeasure
          (ftaylorSeries ℝ (Constrained.targetMerit f c (D.t kε)) (D.x (kε + 1))) j
          (D.δ (kε + 1) j) {d | D.x (kε + 1) + d ∈ X} ≤
        ε j * β * Constrained.targetResidual f c (D.t kε) (D.x kε) * D.δ (kε + 1) j ^ j / j !) ∧
      (ε 2 * √(1 + ‖Constrained.targetMultiplier f c (D.targetOut f c θ ε kε)
            (D.x (kε + 1))‖ ^ 2) * D.δ (kε + 1) 2 ^ 2 +
          Optimization.taylorMeasure (ftaylorSeries ℝ (innerLagrangian f c
              (Constrained.targetMultiplier f c (D.targetOut f c θ ε kε) (D.x (kε + 1))))
              (D.x (kε + 1))) 1 (D.δ (kε + 1) 2) {d | D.x (kε + 1) + d ∈ X} *
            ‖fderiv ℝ f (D.x (kε + 1))‖ * D.δ (kε + 1) 2) / 2 <
        Optimization.taylorMeasure (ftaylorSeries ℝ (innerLagrangian f c
            (Constrained.targetMultiplier f c (D.targetOut f c θ ε kε) (D.x (kε + 1))))
            (D.x (kε + 1))) 2 (D.δ (kε + 1) 2)
          ({d | D.x (kε + 1) + d ∈ X} ∩ {d | fderiv ℝ c (D.x (kε + 1)) d = 0})) ∧
    (∃ (f : ℝ¹ → ℝ) (c : ℝ¹ → ℝ¹) (X X₀ : Set ℝ¹) (q p : ℕ) (θ β₁ β : ℝ) (ε : ℕ → ℝ)
      (x₀ : ℝ¹) (xP : ℕ → ℝ¹) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq 1)
      (Lc Bc Lf Bf : ℕ → ℝ) (kε : ℕ),
      algorithm_14_3_2 f c X q θ β₁ β ε x₀ xP δP k₁ D ∧
      AssumptionCD1pLBX c X X₀ p Lc Bc ∧ AssumptionD1pLBX f X X₀ p Lf Bf ∧ q ≤ p ∧ q = 3 ∧
      ‖c (xP k₁)‖ ≤ θ * ε 0 ∧ D.IsEnd f c X q θ ε kε ∧
      D.targetOut f c θ ε kε < f (D.x (kε + 1)) ∧ D.x (kε + 1) = D.x kε ∧
      (∀ j ∈ Finset.Icc 1 q, Optimization.taylorMeasure
          (ftaylorSeries ℝ (Constrained.targetMerit f c (D.t kε)) (D.x (kε + 1))) j
          (D.δ (kε + 1) j) {d | D.x (kε + 1) + d ∈ X} ≤
        ε j * β * Constrained.targetResidual f c (D.t kε) (D.x kε) * D.δ (kε + 1) j ^ j / j !) ∧
      (ε 3 * √(1 + ‖Constrained.targetMultiplier f c (D.targetOut f c θ ε kε)
            (D.x (kε + 1))‖ ^ 2) * D.δ (kε + 1) 3 ^ 3 +
          3 * Optimization.taylorMeasure (ftaylorSeries ℝ (innerLagrangian f c
              (Constrained.targetMultiplier f c (D.targetOut f c θ ε kε) (D.x (kε + 1))))
              (D.x (kε + 1))) 1 (D.δ (kε + 1) 3) {d | D.x (kε + 1) + d ∈ X} *
            (‖fderiv ℝ f (D.x (kε + 1))‖ * D.δ (kε + 1) 3 +
              ‖iteratedFDeriv ℝ 2 f (D.x (kε + 1))‖ * D.δ (kε + 1) 3 ^ 2)) / 6 <
        Optimization.taylorMeasure (ftaylorSeries ℝ (innerLagrangian f c
            (Constrained.targetMultiplier f c (D.targetOut f c θ ε kε) (D.x (kε + 1))))
            (D.x (kε + 1))) 3 (D.δ (kε + 1) 3)
          ({d | D.x (kε + 1) + d ∈ X} ∩ {d | fderiv ℝ c (D.x (kε + 1)) d = 0})) := by
  have hε0 := Interval.tol_pos 0
  have hc0 : ‖Interval.con 0‖ ≤ 1 / 2 * Interval.tol 0 := by
    simp [Interval.con]; norm_num [Interval.tol]
  constructor
  · obtain ⟨Lc, Bc, hc⟩ := interval_assumptionC 2
    obtain ⟨Lf, Bf, hf⟩ := exists_assumptionD1pLBX_ball (Interval.contDiff_quad.of_le le_top)
      Interval.interval_subset_ball 2
    refine ⟨Interval.quad, Interval.con, Interval.interval, ball 0 2, 2, 2, 1 / 2, 1 / 2, 1 / 2,
      Interval.tol, 0, fun _ => 0, fun _ _ => 1, 0, Interval.seq (Interval.tol 0), Lc, Bc, Lf, Bf,
      1, IsTPqpGCPhase2.algorithm_14_3_2_of_stop (Interval.isHighOrderTargetRun
        (by simp [Interval.quad]) (fun j _ => Interval.tol_pos j) (fun j _ => Interval.tol_le_one j)
        (Constrained.targetCrit.mono Interval.targetCrit_quad
          (fun j _ => by linarith [Interval.tol_pos j]) fun _ _ => zero_le_one))
        (by norm_num) (by norm_num), hc, hf, le_rfl, rfl, hc0,
      Interval.isEnd_one (by simp [Interval.quad]) hε0, ?_, rfl, Interval.targetCrit_quad, ?_⟩ <;>
      rw [Interval.targetOut_one (by simp [Interval.quad]) hε0]
    · simp [Interval.seq, Interval.quad, Interval.tol]
    · simp only [Interval.seq, Interval.targetMultiplier_con, Interval.innerLagrangian_con,
        norm_zero, Interval.tol_of_ne (show (2 : ℕ) ≠ 0 by norm_num), ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, Real.sqrt_one, one_pow,
        mul_one]
      exact Interval.quad_lt_taylorMeasure_two
  · obtain ⟨Lc, Bc, hc⟩ := interval_assumptionC 3
    obtain ⟨Lf, Bf, hf⟩ := exists_assumptionD1pLBX_ball (Interval.contDiff_cubic.of_le le_top)
      Interval.interval_subset_ball 3
    refine ⟨Interval.cubic, Interval.con, Interval.interval, ball 0 2, 3, 3, 1 / 2, 1 / 2, 1 / 2,
      Interval.tol, 0, fun _ => 0, fun _ _ => 1, 0, Interval.seq (Interval.tol 0), Lc, Bc, Lf, Bf,
      1, IsTPqpGCPhase2.algorithm_14_3_2_of_stop (Interval.isHighOrderTargetRun
        (by simp [Interval.cubic]) (fun j _ => Interval.tol_pos j)
        (fun j _ => Interval.tol_le_one j)
        (Constrained.targetCrit.mono Interval.targetCrit_cubic
          (fun j _ => by linarith [Interval.tol_pos j]) fun _ _ => zero_le_one))
        (by norm_num) (by norm_num), hc, hf, le_rfl, rfl, hc0,
      Interval.isEnd_one (by simp [Interval.cubic]) hε0, ?_, rfl, Interval.targetCrit_cubic,
      ?_⟩ <;> rw [Interval.targetOut_one (by simp [Interval.cubic]) hε0]
    · simp [Interval.seq, Interval.cubic, Interval.tol]
    · simp only [Interval.seq, Interval.targetMultiplier_con, Interval.innerLagrangian_con,
        norm_zero, Interval.tol_of_ne (show (3 : ℕ) ≠ 0 by norm_num), ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, Real.sqrt_one, one_pow,
        mul_one]
      linarith [Interval.cubic_lt_taylorMeasure_three]

end Counterexample1435

/-! ### Lemma 14.3.8: the decreases of its proof do not bound the bad outer iterations -/

section Counterexample1438

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

open Constrained.TwoPhaseExample

/-- **The decreases used in the proof of Lemma 14.3.8** ([cartis2022evaluation]) **do not bound
the bad outer iterations.** There are TPqp-GC sequences (`algorithm_14_3_2`, with Phase 2 in the
sense of `IsTPqpGCPhase2`) satisfying every hypothesis of the library's `theorem_14_3_9` for
Phase 2 — whose INNER hypothesis is the contract `IsInnerPhaseRun` (here for every `κ_decr`, `π`
and every `κ_uns`, `κ_unc` with `κ_uns + κ_unc ≥ 1`) — and f.B.Fb on `ℱ_1` with `ε₀ = 1 ≤ β_F = 1`,
for every `β ∈ (0, θ]` and every Phase-1 constant `β₁ ∈ (0, 1)`, with smooth data (`f`, `c`
affine, `X` closed, `‖∇f‖ ≤ 2`), whose Phase 2 never terminates: every outer iteration is reached
and is bad (`Constrained.HighOrderTargetSeq.IsBad`), so `n_bad(K) = K - 1` is unbounded. The INNER
calls are not runs of
a regularization method: they violate the INNER contract keyed on INNER's own test
(`IsInnerPhaseRunStrong`, for every `κ_decr > 0`, `κ_uns ≥ 0`, `κ_unc`, exponents `π_1 ≥ 0` and
radii `ρ_1 ≥ 0`), since otherwise Phase 2 would terminate by
`Constrained.IsHighOrderTargetRun.complexity_of_innerTest`
(with `B_f = 2`, `τ = η/4`). Indeed INNER's own test (14.3.19) fails at `x_{k+1}` for large `k`
(the gradient of `μ(·, t_k)` tends to `θ` while INNER's tolerance tends to `βθ ≤ θ²`), where
Lemma 14.2.2 would guarantee a decrease bounded below, whereas the decreases here tend to `0`. So
this refutes the argument of Lemma 14.3.8 (and the contract `IsInnerPhaseRun`), not the book's
Theorem 14.3.9.

The data (`n = 2`, `m = 1`, `q = 1`): `X = {|x₁| ≤ 3}`, `f(x) = x₂ - x₁`, `c(x) = 3/5 + x₂`,
`θ = 3/5`, `ε₀ = ε₁ = 1`, `x₀ = x₁ = (-12/5, 0)` (`‖c(x₀)‖ = θε₀`, so Phase 1 stops at once);
Phase 2 has iterates `x_k = (-(24/5) 2^{-k}, 0)`, targets `t_k = (16/5) 2^{-k}` and radii `1`, and
the `k`-th INNER call makes one successful iteration from `x_k` to `x_{k+1}`. Then
`f(x_{k+1}) = t_k - a_k` with `a_k = (4/5) 2^{-k}`, so `k ∈ 𝒦_b` (`‖r(x_{k+1}, t_k)‖² =
θ² + a_k² ≥ θ²ε₀²`) and `t_{k+1} = t_k - 2 a_k` (14.3.35). The call is stopped by the third test of
(14.3.32), which holds at `x_{k+1}` for `t_k` (`‖∇μ(x_{k+1}, t_k)‖² = θ² + 2a_k² - 2θa_k ≤
θ² + a_k²`), so its only successful iteration is exempt from the decrease of `IsInnerPhaseRun`
and is not good; and (14.3.34) fails at `x_{k+1}` for `t_{k+1}` (along `d = -e₂` the decrease is
`θ + a_k > √(θ² + a_k²)`), so Phase 2 does not stop. The decrease of `μ` along the calls and the
target drops `2a_k` are summable: the sequence converges to `((0, 0), 0)` without terminating. -/
theorem lemma_14_3_8_proof_gap_counterexample :
    ∃ (f : ℝ² → ℝ) (c : ℝ² → ℝ¹) (X : Set ℝ²) (θ : ℝ) (ε : ℕ → ℝ) (x₀ : ℝ²) (xP : ℕ → ℝ²)
      (δP : ℕ → ℕ → ℝ) (D : TPqpSeq 2),
      IsClosed X ∧ ContDiff ℝ ⊤ f ∧ ContDiff ℝ ⊤ c ∧
      (∀ y, ∀ i ∈ Finset.Icc 1 1, ‖iteratedFDeriv ℝ i f y‖ ≤ 2) ∧
      Chapter07.AssumptionBFb f c X 1 (-5) 4 ∧ ε 0 = 1 ∧
      (∀ β₁ β : ℝ, 0 < β₁ → β₁ < 1 → 0 < β → β ≤ θ →
        algorithm_14_3_2 f c X 1 θ β₁ β ε x₀ xP δP 0 D ∧ ‖c (xP 0)‖ ≤ θ * ε 0 ∧
        (∀ (κdecr κuns κunc : ℝ) (π : ℕ → ℝ), 1 ≤ κuns + κunc →
          IsInnerPhaseRun f c X 1 θ β ε D κdecr κuns κunc π) ∧
        ∀ (κdecr κuns κunc : ℝ) (π ρ : ℕ → ℝ), 0 < κdecr → 0 ≤ κuns → 0 ≤ π 1 → 0 ≤ ρ 1 →
          ¬ IsInnerPhaseRunStrong f c X 1 θ β ε D κdecr κuns κunc π ρ) ∧
      (∀ K, D.Before f c X 1 θ ε K) ∧ (∀ K, D.badCount f c X 1 θ ε K = K - 1) ∧
      ¬ ∃ kε, D.IsEnd f c X 1 θ ε kε := by
  have hc1 : ‖Drift.con (Drift.iter 1)‖ = 3 / 5 := by
    rw [Drift.norm_con, Drift.iter_apply_one, add_zero, abs_of_pos (by norm_num)]
  refine ⟨Drift.obj, Drift.con, Drift.strip, 3 / 5, fun _ => 1, Drift.iter 1,
    fun _ => Drift.iter 1, fun _ _ => 1, Drift.seq, Drift.isClosed_strip, Drift.contDiff_obj,
    Drift.contDiff_con, Drift.norm_iteratedFDeriv_obj_le,
    Chapter07.assumptionBFb_iff.2 fun x hx hcx => Drift.obj_mem_Icc hx hcx, rfl,
    fun β₁ β hβ₁ hβ₁1 hβ hβθ => ⟨IsTPqpGCPhase2.algorithm_14_3_2_of_stop
      (Drift.isHighOrderTargetRun hβ hβθ) hβ₁ hβ₁1, by rw [hc1]; norm_num,
      fun κdecr κuns κunc π hκ => Drift.isEndCritContract hκ,
      fun κdecr κuns κunc π ρ hκ hκuns hπ hρ =>
        Drift.not_isInnerTestContract hβ hβθ hκ hκuns hπ hρ⟩,
    fun K => Drift.before K, Drift.badCount_eq, fun ⟨kε, hend⟩ => Drift.not_stop kε hend.2.1⟩

end Counterexample1438

/-! ## Theorem 14.3.9 for a nonspecific INNER -/

section TheoremFalse

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

open Constrained.TwoPhaseExample

/-- f.D1pLB.X and c.D1pLB.X hold on `X₀ = B(0, 2)` for every `p` on the square problem
(`Constrained.TwoPhaseExample.Box`). -/
theorem box_assumptionD1pLBX (a : ℝ) (p : ℕ) :
    (∃ L B : ℕ → ℝ, AssumptionD1pLBX (Box.obj a) Box.square (ball 0 2) p L B) ∧
      ∃ L B : ℕ → ℝ, AssumptionCD1pLBX Box.con Box.square (ball 0 2) p L B := by
  refine ⟨exists_assumptionD1pLBX_ball ((Box.contDiff_obj a).of_le le_top)
    Box.square_subset_ball p, ?_⟩
  have hc0 : ContDiff ℝ ∞ (fun x => Box.con x 0) :=
    ((contDiff_piLp_apply (p := 2) (i := (0 : Fin 1))).comp Box.contDiff_con).of_le le_top
  obtain ⟨L, B, h⟩ := exists_assumptionD1pLBX_ball hc0 Box.square_subset_ball p
  exact ⟨L, B, isOpen_ball, convex_ball 0 2, Box.square_subset_ball, fun i => by
    rw [Subsingleton.elim i 0]; exact h⟩

/-- f.B.Fb on `ℱ_1` for `f_a` on `X = [-1, 1]²`, `|a| ≤ 1`: `-2 ≤ f_a ≤ 2`. -/
private theorem box_assumptionBFb {a : ℝ} (ha : |a| ≤ 1) :
    Chapter07.AssumptionBFb (Box.obj a) Box.con Box.square 1 (-2) 2 :=
  Chapter07.assumptionBFb_iff.2 fun _ hx _ => Box.obj_mem_Icc ha hx

/-- **Theorem 14.3.9 of [cartis2022evaluation] fails for a nonspecific INNER under the per-call
reading of its INNER hypotheses** (they are checked on the INNER calls of the run; read uniformly
over all admissible inputs, the cost hypothesis cannot be met here for `π₁ < 2`, see
`theorem_14_3_9_cost_hypothesis_unsatisfiable`, and the theorem is vacuous under that reading).
There is a problem (`n = 2`, `m = 1`, `q = 1`, `X = [-1, 1]²`, `f(x) = x₁ - x₂`,
`c(x) = x₁²/2`) satisfying the book's assumptions of the theorem — X.CNe (`AssumptionXCNe`, `X`
also convex), f.D1pLB.X and c.D1pLB.X on `X₀ = B(0, 2)` for every `p`, `‖∇f‖ ≤ 2`, and f.B.Fb on
`ℱ_1` with `f_low = -2`, `f_up = 2` — such that for every constant `C` and every choice of the
constants `κ^A_{INNER,2}`, `κ^C_{INNER,2}`, `κ^S_{INNER,2}`, `κ^{F,ν}_INNER`, `κ^{D,ν}_INNER` of
the theorem there are tolerances `ε₀, ε₁ ∈ (0, 1]` (at most `(1 + 3(|κ^A| + |κ^C| + |κ^S|))⁻¹`)
and sequences terminating at `k_ε` (`Constrained.HighOrderTargetSeq.IsEnd`) with all optimality
radii `δ_{k,j} = 1`, `#F = #D = k_ε + 1` evaluations and

* `k_ε > C max(ε₀^{-1}, ε₀^{1-π₁} ε₁^{-π₁})` for every `π₁ ≤ 3/2`, so that no constant bounds the
  evaluation counts by the order `max(ε₀^{-1}, ε₀^{1-π₁} ε₁^{-π₁})` of the theorem,

with `μ(·, t_k)` decreasing strictly along each call, which for `θ = 3/4`, every `β ∈ [2/3, θ]`
and every Phase-1 constant `β₁ ∈ (0, 1)` form a TPqp-GC run (`algorithm_14_3_2`, Phase 2 entered
at the feasible `x₀`) whose INNER calls satisfy every hypothesis the book places on its
nonspecific INNER, for all exponents `π₁ ∈ [4/3, 3/2]` (which contains the ARqp-SC exponent
`(p+1)/p` of (14.2.12) for `p ∈ {2, 3}`, `Optimization.arqpPiOf_one_le`,
`Optimization.four_thirds_le_arqpPiOf_one`):

* (14.3.19): each Phase-2 call `INNER(μ(·, t_k), X, 1, x_k, β ‖r(x_k, t_k)‖ ε)` returns
  `x_{k+1} ∈ X` with radius `δ = 1` passing INNER's own test
  (`Constrained.HighOrderTargetSeq.InnerTest`), while that test fails at its starting point
  `x_k`, so that any INNER moves in every call;
* (14.3.20)–(14.3.21): its numbers of evaluations of `μ` (`e_k`) and of its derivatives
  (`succCount k`), even counting one more evaluation at `x^S = x_k`, are at most
  `κ_INNER (μ(x_k, t_k) - f_low) (β ‖r(x_k, t_k)‖ ε₁)^{-π₁}` with `f_low = 0` (the lower bound of
  `μ` the book suggests) and the `ε`-independent constants `κ^F_INNER = κ^D_INNER = κ` for every
  `κ ≥ 8`;
* (14.2.11) and (14.2.13) with constants independent of `t` (`IsInnerPhaseRunStrong`, the form of
  Lemmas 14.2.2–14.2.3 keyed on INNER's own test, for every `κ_decr`, every exponents,
  `κ_uns + κ_unc ≥ 1`, radii `ρ₁ ≤ 1`);
* Phase 1 (LENq-SC) stops at `k₁ = 0` (`‖c(x₀)‖ = 0`) and makes no INNER call, so its INNER
  hypotheses hold vacuously;

and whose numbers of evaluations of `(f, c)` and of their derivatives exceed, for every
`π₁ ≤ 3/2`, the printed bounds `#^F_INNER,1 + #^F_INNER,2` and `#^D_INNER,1 + #^D_INNER,2`, with
(14.3.65)–(14.3.66) for Phase 1 (here `0`, as `‖c(x₀)‖ = 0`) and
`#^F_INNER,2 = (f_up - f_low - 1)(κ^A ε₀^{1-π₁} ε₁^{-π₁} + κ^C ε₀^{-1}) + 1`,
`#^D_INNER,2 = κ^S (f_up - f_low - 1) ε₀^{1-π₁} ε₁^{-π₁} + 1`, `f_up - f_low - 1 = 3`. Every outer
iteration before `k_ε` is a case-(b) iteration whose call ends at a point passing INNER's test.

The run exercises exactly the exemption on which the book's proof of Lemma 14.3.8 rests: its
`k_ε ∼ (ε₀ ε₁)^{-1}` bad case-(b) iterations each cost one evaluation, and the decrease of
Lemma 14.2.2 is not required at a step after which INNER's test holds. The extra term
`O(ε₀^{-1} + (ε₀ ε₁)^{-1})` of `Constrained.IsHighOrderTargetRun.complexity_of_innerTest` (the
corrected statement, which needs no cost hypothesis) is thus attained in order; only the cost
bound needs `π₁ ≥ 4/3`. The INNER calls are not runs of ARqp-SC (see the module doc): they are
not produced by a regularization algorithm of (14.2.12). Runs of ARqp-SC itself, when Step 2.1 of
Algorithm 14.1.2 re-initialises `μ` at every Step 2, exceed the printed order with
`π₁ = (p+1)/p` (per-call reading) for `q = 1` and `p ≥ 4` (`theorem_14_3_9_arqp_counterexample`,
on a different problem; with `μ` bounded below this is open); for `q = p`, and with the exponents
`j + 1`, they attain it (`theorem_14_3_9_arqp`, `theorem_14_3_9_arqpc`).

The construction needs `π₁ ≥ 4/3` for the cost bound: a call costs at least one evaluation while
`(μ(x_k, t_k)) (β ‖r‖ ε₁)^{-π₁} ∼ u^{4 - 3π₁}` (`‖r‖ ∼ u²`, `ε₁ ∼ u`), which tends to `0` for
`π₁ < 4/3`. The upper limit `3/2` comes from the order comparison
(`Constrained.TwoPhaseExample.BoxBadIter.order_le`).

The data (`Constrained.TwoPhaseExample.BoxBadIter.exists_seq`): for `m ≥ 7` large enough,
`u = 1/m`, `ε₀ = u²/2 + u³/2`, `ε₁ = 3u/2`, `N = m³`. Phase 2 starts at `x₁ = (0, -1)` with
`t₁ = 1 - ε₀`; the `k`-th INNER call makes one successful iteration to `x_{k+1} = (u, ·)` with
`f(x_{k+1}) = t_k - E_{k+1}`, `E_j = (u³/2)(1 - j/(4(N + 1))) ∈ [3u³/8, u³/2]`, for `k < N`. At
`x_{k+1}` the gradient `∇μ(x_{k+1}, t_k) = (u³/2 - E_{k+1}, E_{k+1})` has norm at most
`u³/2 ≤ β ‖r(x_k, t_k)‖ ε₁` (INNER's test, using `‖r(x_k, t_k)‖ ≥ u²/2`), while after the
reflection (14.3.35) the decrease along `-e₁` is `u³/2 + E_{k+1} ≥ 7u³/8 > ε₁ ‖r(x_{k+1}, t_{k+1})‖`
((14.3.34) fails). The targets drop by `2E_{k+1} ≈ u³`, so `N ≈ 1/u³` such iterations fit in
`X`; the last call lands on its target, `f(x_{N+1}) = t_N`, where the third test of (14.3.32)
holds (case (c)), and Phase 2 stops at `k_ε = N`. -/
theorem theorem_14_3_9_false :
    ∃ (f : ℝ² → ℝ) (c : ℝ² → ℝ¹) (X : Set ℝ²),
      AssumptionXCNe X ∧ Convex ℝ X ∧ ContDiff ℝ ⊤ f ∧ ContDiff ℝ ⊤ c ∧
      (∀ p : ℕ, (∃ L B : ℕ → ℝ, AssumptionD1pLBX f X (ball 0 2) p L B) ∧
        ∃ L B : ℕ → ℝ, AssumptionCD1pLBX c X (ball 0 2) p L B) ∧
      (∀ y, ∀ i ∈ Finset.Icc 1 1, ‖iteratedFDeriv ℝ i f y‖ ≤ 2) ∧
      Chapter07.AssumptionBFb f c X 1 (-2) 2 ∧
      ∀ C κA κC κS κF₁ κD₁ : ℝ,
      ∃ (ε : ℕ → ℝ) (x₀ : ℝ²) (xP : ℕ → ℝ²) (δP : ℕ → ℕ → ℝ) (D : TPqpSeq 2) (kε : ℕ),
        (∀ j, 0 < ε j ∧ ε j ≤ 1) ∧
        ε 0 ≤ (1 + 3 * (|κA| + |κC| + |κS|))⁻¹ ∧ ε 1 ≤ (1 + 3 * (|κA| + |κC| + |κS|))⁻¹ ∧
        ‖c x₀‖ = 0 ∧ (∀ k j, D.δ k j = 1) ∧ D.IsEnd f c X 1 (3 / 4) ε kε ∧
        D.funEvals kε = kε + 1 ∧ D.derivEvals kε = kε + 1 ∧
        -- the order `max(ε₀^{-1}, ε₀^{1-π₁} ε₁^{-π₁})` of the theorem is exceeded
        (∀ π : ℝ, π ≤ 3 / 2 → C * max (ε 0)⁻¹ (ε 0 ^ (1 - π) * ε 1 ^ (-π)) < kε) ∧
        (∀ k ∈ Finset.Icc 1 kε, D.x (k + 1) ∈ X ∧ D.δ (k + 1) 1 = 1 ∧
          Constrained.targetMerit f c (D.t k) (D.x (k + 1)) <
            Constrained.targetMerit f c (D.t k) (D.x k)) ∧
        ∀ β₁ β : ℝ, 0 < β₁ → β₁ < 1 → 2 / 3 ≤ β → β ≤ 3 / 4 →
          algorithm_14_3_2 f c X 1 (3 / 4) β₁ β ε x₀ xP δP 0 D ∧
          -- (14.3.19) at the output of every Phase-2 call, case (b) before `kε`
          (∀ k ∈ Finset.Icc 1 kε, D.InnerTest f c X 1 β ε k) ∧
          (∀ k ∈ Finset.Ico 1 kε, D.IsKb f c (3 / 4) ε k) ∧
          -- INNER's test fails at the start of every call
          (∀ k ∈ Finset.Icc 1 kε,
            β * Constrained.targetResidual f c (D.t k) (D.x k) * ε 1 <
              Optimization.taylorMeasure
                (ftaylorSeries ℝ (Constrained.targetMerit f c (D.t k)) (D.x k)) 1 1
                {d | D.x k + d ∈ X}) ∧
          -- (14.2.11), (14.2.13) with `t`-independent constants, for all exponents
          (∀ (κdecr κuns κunc : ℝ) (π ρ : ℕ → ℝ), 1 ≤ κuns + κunc → ρ 1 ≤ 1 →
            IsInnerPhaseRunStrong f c X 1 (3 / 4) β ε D κdecr κuns κunc π ρ) ∧
          ∀ π : ℕ → ℝ, π 1 ≤ 3 / 2 →
            -- (14.3.20)–(14.3.21) for every call, `f_low = 0`, when `π₁ ≥ 4/3`
            (4 / 3 ≤ π 1 → ∀ κ : ℝ, 8 ≤ κ → ∀ k ∈ Finset.Icc 1 kε,
              (D.e k : ℝ) + 1 ≤
                innerEvalBound κ π 1 (Constrained.targetMerit f c (D.t k) (D.x k))
                  (fun j => β * Constrained.targetResidual f c (D.t k) (D.x k) * ε j) ∧
              (D.succCount k : ℝ) + 1 ≤
                innerEvalBound κ π 1 (Constrained.targetMerit f c (D.t k) (D.x k))
                  (fun j => β * Constrained.targetResidual f c (D.t k) (D.x k) * ε j)) ∧
            -- the printed bounds fail (`f_low = -2`, `f_up = 2`)
            1 / 2 * κF₁ * ‖c x₀‖ * (β₁ ^ (1 - 2 * π 1) / (β₁ ^ (1 - π 1) - 1)) *
                (3 / 4 : ℝ) ^ (1 - π 1) * (ε 0 ^ (1 - π 1) * ε 1 ^ (-π 1)) +
              ((2 - (-2) - 1) * (κA * (ε 0 ^ (1 - π 1) * ε 1 ^ (-π 1)) + κC * (ε 0)⁻¹) + 1) <
                D.funEvals kε ∧
            1 / 2 * κD₁ * ‖c x₀‖ * (β₁ ^ (1 - 2 * π 1) / (β₁ ^ (1 - π 1) - 1)) *
                (3 / 4 : ℝ) ^ (1 - π 1) * (ε 0 ^ (1 - π 1) * ε 1 ^ (-π 1)) +
              (κS * (2 - (-2) - 1) * (ε 0 ^ (1 - π 1) * ε 1 ^ (-π 1)) + 1) <
                D.derivEvals kε := by
  refine ⟨Box.obj 1, Box.con, Box.square,
    ⟨Box.isClosed_square, ⟨pt 0 (-1), Box.pt_mem_square (by simp) (by simp)⟩⟩, Box.convex_square,
    Box.contDiff_obj 1, Box.contDiff_con, box_assumptionD1pLBX 1,
    Box.norm_iteratedFDeriv_obj_le (by simp),
    box_assumptionBFb (by simp),
    fun C κA κC κS κF₁ κD₁ => ?_⟩
  have hAa := abs_nonneg κA
  have hCa := abs_nonneg κC
  have hSa := abs_nonneg κS
  set K := 1 + 3 * (|κA| + |κC| + |κS|) with hK
  have hK1 : 1 ≤ K := by rw [hK]; linarith
  obtain ⟨ε, D, kε, hε, hCε, hord, hend, hF, hD, hδ, he, hs, hstep, hrun, hβ, hcost⟩ :=
    BoxBadIter.exists_seq (|C| + K)
  obtain ⟨hε0, hε1⟩ := hCε (by linarith [abs_nonneg C])
  have hinv : (|C| + K)⁻¹ ≤ K⁻¹ := inv_anti₀ (by linarith) (by linarith [abs_nonneg C])
  have hc0 : ‖Box.con (pt 0 (-1))‖ = 0 := by rw [Box.norm_con]; simp
  have hmax : ∀ π : ℝ, 0 ≤ max (ε 0)⁻¹ (ε 0 ^ (1 - π) * ε 1 ^ (-π)) := fun π =>
    (inv_pos.2 (hε 0).1).le.trans (le_max_left _ _)
  refine ⟨ε, pt 0 (-1), fun _ => pt 0 (-1), fun _ _ => 1, D, kε, hε, hε0.trans hinv,
    hε1.trans hinv, hc0, hδ, hend, hF, hD, fun π hπ => lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right ((le_abs_self C).trans (by linarith)) (hmax π)) (hord π hπ),
    hstep, fun β₁ β hβ₁ hβ₁1 hβ' hβθ => ?_⟩
  obtain ⟨htest, hkb, hstart, hcon⟩ := hβ β hβ' hβθ
  refine ⟨IsTPqpGCPhase2.algorithm_14_3_2_of_stop (hrun β (by linarith) hβθ) hβ₁ hβ₁1, htest,
    hkb, hstart, hcon, fun π hπ2 => ⟨fun hπ1 κ hκ k hk => ?_, ?_⟩⟩
  · have h2 := hcost β (by linarith) hβθ κ hκ π hπ1 k hk
    rw [innerEvalBound_one, he k, hs k]
    push_cast
    exact ⟨by linarith, by linarith⟩
  set M := ε 0 ^ (1 - π 1) * ε 1 ^ (-π 1) with hM_def
  set E := (ε 0)⁻¹ with hE_def
  have hM0 : 0 ≤ M := by have := (hε 0).1; have := (hε 1).1; positivity
  have hE0 : 0 ≤ E := (inv_pos.2 (hε 0).1).le
  have hMB : M ≤ max E M := le_max_right _ _
  have hEB : E ≤ max E M := le_max_left _ _
  have hA : κA * M ≤ |κA| * max E M :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) hM0).trans
      (mul_le_mul_of_nonneg_left hMB (abs_nonneg _))
  have hC : κC * E ≤ |κC| * max E M :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) hE0).trans
      (mul_le_mul_of_nonneg_left hEB (abs_nonneg _))
  have hS : κS * M ≤ |κS| * max E M :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) hM0).trans
      (mul_le_mul_of_nonneg_left hMB (abs_nonneg _))
  have hB0 : 0 ≤ max E M := hE0.trans hEB
  have hB := hord (π 1) hπ2
  have hCB : 0 ≤ |C| * max E M := mul_nonneg (abs_nonneg C) hB0
  rw [hF, hD, hc0]
  push_cast
  constructor <;> nlinarith

/-- **The literal, uniform reading of the cost hypothesis (14.3.20)–(14.3.21) cannot be met on
the problem of `theorem_14_3_9_false` when `π₁ < 2`** ([cartis2022evaluation], §14.3,
(14.3.20)–(14.3.21) read as a bound, with one `ε`-independent `κ_INNER`, on the cost of every call
`INNER(μ(·, t), X, 1, x^S, β ‖r(x^S, t)‖ ε)` for all admissible tolerances). For every
`π₁ < 2`, `β ∈ (0, 1)` and `κ` there are admissible tolerances (`ε₁ = 1`, `ε₀ ∈ (0, 1]` small)
such that the first Phase-2 call (from `x^S = x₁ = (0, -1) ∈ X`, feasible, with the Step-0 target
`t₁ = f(x₁) - √(ε₀² - ‖c(x₁)‖²)`) starts at a point failing INNER's test (14.3.19) for every
radius `δ ∈ (0, 1]` (the decrease along `-δ e₁` is `ε₀ δ > β ε₀ ε₁ δ`), so any INNER spends at
least one evaluation on it, while its bound `κ μ(x₁, t₁) (β ‖r(x₁, t₁)‖ ε₁)^{-π₁}
= (κ/2) β^{-π₁} ε₀^{2-π₁}` is below `1`. Under that reading no INNER (ARqp-SC included, compare
`exists_algorithm_14_3_1_cost_contract_counterexample`) satisfies the hypotheses of
Theorem 14.3.9 on this problem for `π₁ < 2`, and the printed theorem is vacuous there; under the
per-call reading (the hypotheses checked on the calls of the run) it is false for
`π₁ ∈ [4/3, 3/2]` (`theorem_14_3_9_false`). -/
theorem theorem_14_3_9_cost_hypothesis_unsatisfiable (π : ℕ → ℝ) (hπ : π 1 < 2) {β : ℝ}
    (hβ : 0 < β) (hβ1 : β < 1) (κ : ℝ) :
    ∃ ε : ℕ → ℝ, (∀ j, 0 < ε j ∧ ε j ≤ 1) ∧ pt 0 (-1) ∈ Box.square ∧ ‖Box.con (pt 0 (-1))‖ = 0 ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        β * Constrained.targetResidual (Box.obj 1) Box.con
            (Box.obj 1 (pt 0 (-1)) - √(ε 0 ^ 2 - ‖Box.con (pt 0 (-1))‖ ^ 2)) (pt 0 (-1)) *
            ε 1 * δ ^ 1 / (1 : ℕ)! <
          Optimization.taylorMeasure
            (ftaylorSeries ℝ (Constrained.targetMerit (Box.obj 1) Box.con
              (Box.obj 1 (pt 0 (-1)) - √(ε 0 ^ 2 - ‖Box.con (pt 0 (-1))‖ ^ 2))) (pt 0 (-1))) 1 δ
            {d | pt 0 (-1) + d ∈ Box.square}) ∧
      innerEvalBound κ π 1
          (Constrained.targetMerit (Box.obj 1) Box.con
            (Box.obj 1 (pt 0 (-1)) - √(ε 0 ^ 2 - ‖Box.con (pt 0 (-1))‖ ^ 2)) (pt 0 (-1)))
          (fun j => β * Constrained.targetResidual (Box.obj 1) Box.con
            (Box.obj 1 (pt 0 (-1)) - √(ε 0 ^ 2 - ‖Box.con (pt 0 (-1))‖ ^ 2)) (pt 0 (-1)) * ε j) <
        1 := by
  obtain ⟨ε, hε, hmem, hc0, htest, hcost⟩ :=
    BoxBadIter.exists_tol_start_lt_taylorMeasure π hπ hβ hβ1 κ
  exact ⟨ε, hε, hmem, hc0, htest, by rw [innerEvalBound_one]; exact hcost⟩

end TheoremFalse


/-! ## INNER = ARqp-SC -/

section ARqpSCCalls

/-! ### ARqp-SC calls

INNER = ARqp-SC is the backbone ARqpC run with `c = 0`, `h = 0` (`Optimization.IsARqpCRun`,
`Optimization.IsARqpCRun.isARqpRun_zero`), with the calls and their contracts of
`Numlib.Optimization.ModelBased.HighOrder.ARqpCCall`; here the codomain of `c = 0` is `ℝ⁰`. -/

/-- The zero constraint map `ℝⁿ → ℝ⁰`: ARqpC-SC with `c = 0` and `h = 0` is ARqp-SC on `f`
(`Optimization.IsARqpCRun.isARqpRun_zero`). -/
abbrev zeroCon (n : ℕ) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin 0) := 0

/-- The zero outer function `h = 0` on `ℝ⁰`. -/
abbrev zeroOuter : EuclideanSpace ℝ (Fin 0) → ℝ := 0

/-- The zero constraint map satisfies c.D1pL with constants `0`. -/
theorem assumptionCD1pL_zeroCon (p : ℕ) : AssumptionCD1pL (zeroCon n) p (fun _ => 0) :=
  ⟨fun i => i.elim0, fun _ _ => le_rfl⟩

/-- `(y, δ)` is the output of a call `INNER(F, X, q, x^S, ε)` realized by ARqp-SC: `y` is the
first termination iterate of an ARqpC-SC run (`algorithm_14_1_1`) with `c = 0`, `h = 0` and
initial radii `1` on `F` from `x^S`, and the radii `δ ∈ (0, 1]^q` certify (14.3.19) at `y`
(`Optimization.IsARqpOutput`). -/
abbrev IsARqpSCOutput (F : ℝⁿ → ℝ) (X : Set ℝⁿ) (p q : ℕ) (P : ARqpCParams) (ε : ℕ → ℝ)
    (xS y : ℝⁿ) (δ : ℕ → ℝ) : Prop :=
  Optimization.IsARqpOutput (EuclideanSpace ℝ (Fin 0)) F X p q P.toARqpParams ε xS y δ

/-- `(y, δ)` is the output of an ARqp-SC call `INNER(F, X, q, x^S, ε)` (as in `IsARqpSCOutput`)
whose run uses `nF` evaluations of `F` and `nD` evaluations of its derivatives
(`Optimization.IsARqpOutputCost`). -/
abbrev IsARqpSCOutputCost (F : ℝⁿ → ℝ) (X : Set ℝⁿ) (p q : ℕ) (P : ARqpCParams) (ε : ℕ → ℝ)
    (xS y : ℝⁿ) (δ : ℕ → ℝ) (nF nD : ℕ) : Prop :=
  Optimization.IsARqpOutputCost (EuclideanSpace ℝ (Fin 0)) F X p q P.toARqpParams ε xS y δ nF nD

/-- The constant `κ_F = κ_uns/κ_decr + 2 κ_C` of the cost contract (14.3.20) for function
evaluations of an ARqp-SC call (ARqpC-SC row, `κ_decr = Optimization.arqpCallKappaDecr`,
`κ_C = Optimization.kappaCARqp`). -/
noncomputable def arqpSCKappaF (P : ARqpCParams) (L : ℕ → ℝ) (p q : ℕ) : ℝ :=
  Optimization.arqpKappaUns P.toARqpParams / Optimization.arqpCallKappaDecr P.toARqpParams L p q +
    2 * Optimization.kappaCARqp P.toARqpParams L p

/-- The constant `κ_D = 1/κ_decr + 4` of the cost contract (14.3.21) for derivative evaluations
of an ARqp-SC call. -/
noncomputable def arqpSCKappaD (P : ARqpCParams) (L : ℕ → ℝ) (p q : ℕ) : ℝ :=
  1 / Optimization.arqpCallKappaDecr P.toARqpParams L p q + 4

section InnerCall

variable {F : ℝⁿ → ℝ} {X : Set ℝⁿ} {p q : ℕ} {P : ARqpCParams} {ε : ℕ → ℝ}

/-- One INNER call by ARqp-SC with its evaluation counts, under the anchored bounds of `F`
(`AnchoredCompositeBounds` with `c = 0`, constants `L`, open convex `X₀ ⊇ X`) on a set `S`
containing the sublevel set of `F` at `x^S` (`Optimization.exists_isARqpOutputCost`). -/
theorem exists_isARqpSCOutputCost_anchored {X₀ S : Set ℝⁿ} {L : ℕ → ℝ}
    (hF : AnchoredCompositeBounds F (zeroCon n) X₀ S p L (fun _ => 0)) (hXX₀ : X ⊆ X₀)
    {flow : ℝ} (hb : ∀ y ∈ X, flow ≤ F y) (P : ARqpCParams) (hθς : P.θ < P.ς) (hq : 1 ≤ q)
    (hqp : q ≤ p) (hX : IsClosed X) {xS : ℝⁿ} (hxS : xS ∈ X)
    (hS : ∀ y ∈ X, F y ≤ F xS → y ∈ S) (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1) :
    ∃ (y : ℝⁿ) (δ : ℕ → ℝ) (nF nD : ℕ), IsARqpSCOutputCost F X p q P ε xS y δ nF nD := by
  obtain ⟨y, δ, nF, nD, h, -⟩ := Optimization.exists_isARqpOutputCost (EuclideanSpace ℝ (Fin 0))
    hX hxS hb hF.lipschitzDerivsAnchored_f hF.one_le hF.jet_f hXX₀ hS P.toARqpParams P.σmin_pos
    hθς hq hqp hε
  exact ⟨y, δ, nF, nD, h⟩

/-- `κ gap/min_j ε_j^{π_j} ≤ κ gap max_j ε_j^{-π_j}` (`innerEvalBound`) for `κ, gap ≥ 0`,
`ε ∈ (0, 1]^q` and `π ≥ 0`. -/
theorem div_finMin_le_innerEvalBound {κ gap : ℝ} (hκ : 0 ≤ κ) (hgap : 0 ≤ gap) {π : ℕ → ℝ}
    (hπ : ∀ j ∈ Finset.Icc 1 q, 0 ≤ π j) (hq : 1 ≤ q) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) :
    κ * gap / Optimization.finMin 1 (fun j => ε j ^ π j) q ≤ innerEvalBound κ π q gap ε := by
  obtain ⟨j₀, hj₀, hmin⟩ := Optimization.exists_finMin_eq hq
    (u := fun j => ε j ^ π j) (b := 1) fun j hj =>
      Real.rpow_le_one (hε j hj).1.le (hε j hj).2 (hπ j hj)
  have hbdd : BddAbove (Set.range fun j : Finset.Icc 1 q => ε j ^ (-π j)) :=
    (Set.finite_range _).bddAbove
  have hinv : (Optimization.finMin 1 (fun j => ε j ^ π j) q)⁻¹ ≤
      ⨆ j : Finset.Icc 1 q, ε j ^ (-π j) := by
    rw [hmin, ← Real.rpow_neg (hε j₀ hj₀).1.le]
    exact le_ciSup hbdd ⟨j₀, hj₀⟩
  unfold innerEvalBound
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left hinv (mul_nonneg hκ hgap)

/-- **The cost contract (14.3.20)–(14.3.21) for ARqp-SC under the anchored assumptions**
([cartis2022evaluation], Theorem 14.2.4, ARqpC-SC row with `c = 0`, `h = 0`, `π_j = j + 1`).
Let `F ≥ 0` on `X` satisfy the anchored bounds of the ARqpC analysis with constants `L` on a set
`S` (for an open convex `X₀ ⊇ X`) containing every `y ∈ X` with `F(y) ≤ F(x^S)`, `θ < ς`, and let
the call start at `x^S ∈ X` with `2 F(x^S) ≥ ε_1²`. Then an ARqp-SC call with tolerances `ε` uses
at most `κ_F F(x^S) max_j ε_j^{-(j+1)}` evaluations of `F` and `κ_D F(x^S) max_j ε_j^{-(j+1)}`
evaluations of its derivatives (`innerEvalBound`, `κ_F = arqpSCKappaF P L p q`,
`κ_D = arqpSCKappaD P L p q`), as `IsARqpSCOutputCost.cost_le` under global assumptions. -/
theorem IsARqpSCOutputCost.cost_le_anchored {X₀ S : Set ℝⁿ} {L : ℕ → ℝ}
    (hF : AnchoredCompositeBounds F (zeroCon n) X₀ S p L (fun _ => 0)) (hXX₀ : X ⊆ X₀)
    (hb : ∀ y ∈ X, 0 ≤ F y) (hθς : P.θ < P.ς) {xS y : ℝⁿ} {δ' : ℕ → ℝ} {nF nD : ℕ}
    (h : IsARqpSCOutputCost F X p q P ε xS y δ' nF nD) (hxS : xS ∈ X)
    (hS : ∀ y ∈ X, F y ≤ F xS → y ∈ S) (habs : ε 1 ^ 2 ≤ 2 * F xS) :
    (nF : ℝ) ≤ innerEvalBound (arqpSCKappaF P L p q) (fun l => (l : ℝ) + 1) q (F xS) ε ∧
    (nD : ℝ) ≤ innerEvalBound (arqpSCKappaD P L p q) (fun l => (l : ℝ) + 1) q (F xS) ε := by
  obtain ⟨h1, h2⟩ := h.cost_le (flow := 0) hb hF.lipschitzDerivsAnchored_f hF.one_le hF.jet_f
    hXX₀ hS P.σmin_pos hθς
  have hq := h.one_le_q
  have hε := h.ε_mem
  have hFx : 0 ≤ F xS := hb xS hxS
  set κd := Optimization.arqpCallKappaDecr P.toARqpParams L p q
  set κu := Optimization.arqpKappaUns P.toARqpParams
  set κC := Optimization.kappaCARqp P.toARqpParams L p
  have hκ : 0 < κd := Optimization.arqpCallKappaDecr_pos P.σmin_pos hθς hF.one_le
  have hκu : 0 ≤ κu := Optimization.arqpKappaUns_nonneg
  have hκC : 0 ≤ κC := Optimization.kappaCARqp_nonneg _ _ _
  have hπ : ∀ j ∈ Finset.Icc 1 q, (0 : ℝ) ≤ (fun l : ℕ => (l : ℝ) + 1) j := fun j _ => by
    positivity
  rw [sub_zero, Optimization.finMin_pow_succ_eq_rpow] at h1 h2
  set mε := Optimization.finMin 1 (fun j => ε j ^ ((fun l : ℕ => (l : ℝ) + 1) j)) q
  have hB := div_finMin_le_innerEvalBound (κ := 1) zero_le_one hFx hπ hq hε
  rw [one_mul] at hB
  set S := ⨆ j : Finset.Icc 1 q, ε j ^ (-(fun l : ℕ => (l : ℝ) + 1) j)
  have hBS : F xS / mε ≤ F xS * S := by
    have := hB; unfold innerEvalBound at this; rwa [one_mul] at this
  have h1q : 1 ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, hq⟩
  have hbdd : BddAbove (Set.range fun j : Finset.Icc 1 q =>
      ε j ^ (-(fun l : ℕ => (l : ℝ) + 1) j)) := (Set.finite_range _).bddAbove
  have habs' : 1 ≤ 2 * F xS * S := by
    have hε1 := (hε 1 h1q).1
    have h1 : (ε 1 ^ 2)⁻¹ ≤ S := by
      refine le_trans (le_of_eq ?_) (le_ciSup hbdd ⟨1, h1q⟩)
      rw [Real.rpow_neg hε1.le]
      norm_num
    have : 1 ≤ 2 * F xS * (ε 1 ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      linarith
    exact this.trans (by gcongr)
  have e1 : F xS / (κd * mε) = F xS / mε / κd := by rw [div_div, mul_comm]
  rw [e1] at h1 h2
  have hS0 : 0 ≤ F xS * S := (div_nonneg hFx (Optimization.finMin_pos one_pos fun j hj =>
    Real.rpow_pos_of_pos (hε j hj).1 _).le).trans hBS
  unfold innerEvalBound arqpSCKappaF arqpSCKappaD
  constructor
  · have : κu * (F xS / mε / κd) ≤ κu / κd * (F xS * S) := by
      rw [div_mul_eq_mul_div, mul_div_assoc]
      gcongr
    nlinarith
  · have : F xS / mε / κd ≤ 1 / κd * (F xS * S) := by
      rw [one_div_mul_eq_div]
      gcongr
    nlinarith

/-- **The cost contract (14.3.20)–(14.3.21) for ARqp-SC** ([cartis2022evaluation],
Theorem 14.2.4, ARqpC-SC row with `c = 0`, `h = 0`, `π_j = j + 1`). Let `F ≥ 0` on `X` satisfy
F.D1pL with constants `L`, `θ < ς`, and let the call start at `x^S ∈ X` with
`2 F(x^S) ≥ ε_1²` (so that the additive constant of Theorem 14.2.4 is absorbed). Then an
ARqp-SC call with tolerances `ε` uses at most
`κ_F F(x^S) max_j ε_j^{-(j+1)}` evaluations of `F` and `κ_D F(x^S) max_j ε_j^{-(j+1)}`
evaluations of its derivatives (`innerEvalBound`, `κ_F = arqpSCKappaF`,
`κ_D = arqpSCKappaD`). The exponents `j + 1` are those of the ARqpC-SC row; the ARqp-SC row, in
additive form, is `IsARqpSCOutputCost.cost_le_arqp_add_anchored`. -/
theorem IsARqpSCOutputCost.cost_le {L : ℕ → ℝ} (hF : Chapter12.AssumptionD1pL F p L)
    (hb : ∀ y ∈ X, 0 ≤ F y) (hθς : P.θ < P.ς) {xS y : ℝⁿ} {δ' : ℕ → ℝ} {nF nD : ℕ}
    (h : IsARqpSCOutputCost F X p q P ε xS y δ' nF nD) (hxS : xS ∈ X)
    (habs : ε 1 ^ 2 ≤ 2 * F xS) :
    (nF : ℝ) ≤ innerEvalBound (arqpSCKappaF P L p q) (fun l => (l : ℝ) + 1) q (F xS) ε ∧
    (nD : ℝ) ≤ innerEvalBound (arqpSCKappaD P L p q) (fun l => (l : ℝ) + 1) q (F xS) ε :=
  IsARqpSCOutputCost.cost_le_anchored (AnchoredCompositeBounds.of_global hF
    (assumptionCD1pL_zeroCon p) (h.one_le_q.trans h.q_le_p) univ) (subset_univ X) hb hθς h hxS
    (fun y _ _ => mem_univ y) habs

/-- The decrease constant `η₁ κ_{Δm}` of the ARqp-SC row of Lemma 14.2.2 in radii mode `u`
(`Optimization.arqpKappaDmOf u`). -/
noncomputable def arqpRowKappaDecr (u : Prop) [Decidable u] (P : ARqpCParams) (L : ℕ → ℝ)
    (p q : ℕ) : ℝ :=
  P.η₁ * Optimization.arqpKappaDmOf u P.toARqpParams L p q

/-- **The cost of an ARqp-SC call with the exponents of its row of (14.2.12), additive form,
anchored** ([cartis2022evaluation], Theorem 14.2.4, ARqp-SC row,
`Optimization.IsARqpOutputCost.cost_le_arqp`), under the anchored bounds of `F` on a set `S`
containing every `y ∈ X` with `F(y) ≤ F(x^S)` (an open convex `X₀ ⊇ X`; the book's f.D1pLaB.X), for
`F ≥ 0` on `X` and a radii mode `u` with
`u → q = 1 ∧ X` convex. -/
theorem IsARqpSCOutputCost.cost_le_arqp_add_anchored {X₀ S : Set ℝⁿ} {L : ℕ → ℝ}
    (hF : AnchoredCompositeBounds F (zeroCon n) X₀ S p L (fun _ => 0)) (hXX₀ : X ⊆ X₀)
    (hb : ∀ y ∈ X, 0 ≤ F y) (hθς : P.θ < P.ς) {u : Prop} [Decidable u]
    (hu : u → q = 1 ∧ Convex ℝ X)
    {xS y : ℝⁿ} {δ' : ℕ → ℝ} {nF nD : ℕ}
    (h : IsARqpSCOutputCost F X p q P ε xS y δ' nF nD) (hxS : xS ∈ X)
    (hS : ∀ y ∈ X, F y ≤ F xS → y ∈ S) :
    (nF : ℝ) ≤ innerEvalBound
        (Optimization.arqpKappaUns P.toARqpParams / arqpRowKappaDecr u P L p q)
        (Optimization.arqpPiOf u p) q (F xS) ε + Optimization.kappaCARqp P.toARqpParams L p ∧
    (nD : ℝ) ≤ innerEvalBound (1 / arqpRowKappaDecr u P L p q) (Optimization.arqpPiOf u p) q
        (F xS) ε + 2 := by
  obtain ⟨h1, h2⟩ := h.cost_le_arqp (flow := 0) hb hF.lipschitzDerivsAnchored_f hF.one_le
    hF.jet_f hXX₀ hS P.σmin_pos hθς hu
  have hq := h.one_le_q
  have hε := h.ε_mem
  have hFx : 0 ≤ F xS := hb xS hxS
  have hκ : 0 < arqpRowKappaDecr u P L p q :=
    mul_pos P.η₁_pos (Optimization.arqpKappaDmOf_pos u P.σmin_pos hθς hF.one_le)
  have hπ : ∀ j ∈ Finset.Icc 1 q, 0 ≤ Optimization.arqpPiOf u p j := fun j _ =>
    Optimization.arqpPiOf_nonneg u p j
  rw [sub_zero] at h1 h2
  have eA : Optimization.kappaAARqpOf u P.toARqpParams L p q =
      Optimization.arqpKappaUns P.toARqpParams / arqpRowKappaDecr u P L p q := by
    rw [Optimization.kappaAARqpOf_def, Optimization.kappaSARqpOf_def, arqpRowKappaDecr]
    ring
  have eS : Optimization.kappaSARqpOf u P.toARqpParams L p q = 1 / arqpRowKappaDecr u P L p q :=
    rfl
  rw [eA] at h1
  rw [eS] at h2
  have hB1 := div_finMin_le_innerEvalBound
    (div_nonneg (Optimization.arqpKappaUns_nonneg (P := P.toARqpParams)) hκ.le) hFx hπ hq hε
  have hB2 := div_finMin_le_innerEvalBound (one_div_nonneg.2 hκ.le) hFx hπ hq hε
  exact ⟨by linarith, by linarith⟩

/-- The constant `κ_F = κ_uns/(η₁ κ_{Δm}) + 2 κ_C` of the cost contract (14.3.20) for function
evaluations of an ARqp-SC call, with the ARqp-SC row of Lemma 14.2.2 in radii mode `u`. -/
noncomputable def arqpRowKappaF (u : Prop) [Decidable u] (P : ARqpCParams) (L : ℕ → ℝ)
    (p q : ℕ) : ℝ :=
  Optimization.arqpKappaUns P.toARqpParams / arqpRowKappaDecr u P L p q +
    2 * Optimization.kappaCARqp P.toARqpParams L p

/-- The constant `κ_D = 1/(η₁ κ_{Δm}) + 4` of the cost contract (14.3.21) for derivative
evaluations of an ARqp-SC call, with the ARqp-SC row of Lemma 14.2.2 in radii mode `u`. -/
noncomputable def arqpRowKappaD (u : Prop) [Decidable u] (P : ARqpCParams) (L : ℕ → ℝ)
    (p q : ℕ) : ℝ :=
  1 / arqpRowKappaDecr u P L p q + 4

/-- **The multiplicative cost contract (14.3.20)–(14.3.21) for ARqp-SC with the exponents of its
row of (14.2.12)** ([cartis2022evaluation], Theorem 14.2.4, ARqp-SC row), under the anchored
bounds of `IsARqpSCOutputCost.cost_le_arqp_add_anchored`, for `F ≥ 0` on `X` and a radii mode `u`
of the row available for the run. If the call starts at `x^S ∈ X` with
`1 ≤ 2 F(x^S) ε_j^{-π_j}` for some `j ∈ [1 : q]` (so that the additive constants of the additive
form are absorbed), it uses at most `κ_F F(x^S) max_j ε_j^{-π_j}` evaluations of `F` and
`κ_D F(x^S) max_j ε_j^{-π_j}` evaluations of its derivatives, `π_j = Optimization.arqpPiOf u p j`
(`κ_F = arqpRowKappaF u`, `κ_D = arqpRowKappaD u`). For LENq-SC calls the absorption holds as
soon as some `π_j ≥ 2`, e.g. for every `q ≥ 2` (`IsARqpSCOutputCost.cost_le_arqp_lenq`); it fails
for `q = 1`, `p ≥ 2` (`exists_algorithm_14_3_1_cost_contract_counterexample`). -/
theorem IsARqpSCOutputCost.cost_le_arqp_anchored {X₀ S : Set ℝⁿ} {L : ℕ → ℝ}
    (hF : AnchoredCompositeBounds F (zeroCon n) X₀ S p L (fun _ => 0)) (hXX₀ : X ⊆ X₀)
    (hb : ∀ y ∈ X, 0 ≤ F y) (hθς : P.θ < P.ς) {u : Prop} [Decidable u]
    (hu : u → q = 1 ∧ Convex ℝ X)
    {xS y : ℝⁿ} {δ' : ℕ → ℝ} {nF nD : ℕ}
    (h : IsARqpSCOutputCost F X p q P ε xS y δ' nF nD) (hxS : xS ∈ X)
    (hS : ∀ y ∈ X, F y ≤ F xS → y ∈ S)
    (habs : ∃ j ∈ Finset.Icc 1 q, 1 ≤ 2 * F xS * ε j ^ (-Optimization.arqpPiOf u p j)) :
    (nF : ℝ) ≤ innerEvalBound (arqpRowKappaF u P L p q) (Optimization.arqpPiOf u p) q (F xS) ε ∧
    (nD : ℝ) ≤ innerEvalBound (arqpRowKappaD u P L p q) (Optimization.arqpPiOf u p) q (F xS)
      ε := by
  obtain ⟨h1, h2⟩ := IsARqpSCOutputCost.cost_le_arqp_add_anchored hF hXX₀ hb hθς hu h hxS hS
  set S := ⨆ j : Finset.Icc 1 q, ε j ^ (-Optimization.arqpPiOf u p j)
  have hbdd : BddAbove (Set.range fun j : Finset.Icc 1 q =>
      ε j ^ (-Optimization.arqpPiOf u p j)) := (Set.finite_range _).bddAbove
  have habs' : 1 ≤ 2 * F xS * S := by
    obtain ⟨j, hj, h1⟩ := habs
    have := hb xS hxS
    exact h1.trans (by gcongr; exact le_ciSup hbdd ⟨j, hj⟩)
  have hκC := Optimization.kappaCARqp_nonneg P.toARqpParams L p
  unfold innerEvalBound at h1 h2 ⊢
  unfold arqpRowKappaF arqpRowKappaD
  constructor
  · nlinarith
  · nlinarith

/-- **The multiplicative cost contract (14.3.20)–(14.3.21) holds for the LENq-SC calls of
ARqp-SC when `q ≥ 2`** ([cartis2022evaluation], §14.3.2.1, with the ARqp-SC row `j(p+1)/p` of
(14.2.12)): an ARqp-SC call on `Φ₂ = ½ ‖r‖²` from `x^S ∈ X` with tolerances `β ‖r(x^S)‖ ε_j`,
`β ∈ (0, 1]`, `ε_q ≤ 1`, uses at most `κ_F Φ₂(x^S) max_j (β ‖r(x^S)‖ ε_j)^{-π_j}` evaluations of
`Φ₂` and the same with `κ_D` for its derivatives, since `π_q = q(p+1)/p ≥ 2`. -/
theorem IsARqpSCOutputCost.cost_le_arqp_lenq {r : ℝⁿ → ℝᵐ} {X₀ S : Set ℝⁿ} {L : ℕ → ℝ}
    (hF : AnchoredCompositeBounds (phi2 r) (zeroCon n) X₀ S p L (fun _ => 0)) (hXX₀ : X ⊆ X₀)
    (hθς : P.θ < P.ς) (hq : 2 ≤ q) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hεq : ε q ≤ 1)
    {xS y : ℝⁿ} {δ' : ℕ → ℝ} {nF nD : ℕ}
    (h : IsARqpSCOutputCost (phi2 r) X p q P (fun j => β * ‖r xS‖ * ε j) xS y δ' nF nD)
    (hxS : xS ∈ X) (hS : ∀ y ∈ X, phi2 r y ≤ phi2 r xS → y ∈ S) :
    (nF : ℝ) ≤ innerEvalBound (arqpRowKappaF False P L p q) (Optimization.arqpPiOf False p) q
      (phi2 r xS) (fun j => β * ‖r xS‖ * ε j) ∧
    (nD : ℝ) ≤ innerEvalBound (arqpRowKappaD False P L p q) (Optimization.arqpPiOf False p) q
      (phi2 r xS) (fun j => β * ‖r xS‖ * ε j) := by
  have hqI : q ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨by omega, le_rfl⟩
  obtain ⟨hpos, hle⟩ := h.ε_mem q hqI
  have hp : 1 ≤ p := by
    obtain ⟨⟨_, _, _, _, _, _, _, _, hr, -⟩, -⟩ := h
    exact hr.one_le_q.trans hr.q_le_p
  have hR : 0 < ‖r xS‖ := by
    by_contra h0
    have : ‖r xS‖ = 0 := le_antisymm (not_lt.1 h0) (norm_nonneg _)
    simp [this] at hpos
  have he : 0 < ε q := by
    by_contra h0
    have : β * ‖r xS‖ * ε q ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (not_lt.1 h0)
    linarith
  have hπ : 2 ≤ Optimization.arqpPiOf False p q := by
    rw [Optimization.arqpPiOf_of_neg (not_false)]
    have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  refine h.cost_le_arqp_anchored hF hXX₀ (fun y _ => by rw [phi2_apply]; positivity) hθς
    (u := False) (fun h => h.elim) hxS hS ⟨q, hqI, ?_⟩
  rw [phi2_apply]
  exact Constrained.one_le_mul_sq_div_two_mul_rpow_neg hβ0 he (by nlinarith) hR hle hπ

/-- `(y, δ)` is the output of a call `INNER(F, ℝⁿ, q, x^S, ε)` realized by ARqp on `ℝⁿ` with unit
radii (the ARqp-SC row of (14.2.12) for `X = ℝⁿ`, `q ≤ 2`), using `nF` evaluations of `F` and `nD`
of its derivatives (`Optimization.IsARqpUnitOutputCost`): `y` is the first termination iterate of
an ARqp run (`Chapter12.algorithm_12_2_2`) on `F` from `x^S` with initial radii `1` whose Step-2
radii are `1` before termination, and the radii `δ = 1` certify (14.3.19) at `y`. -/
abbrev IsARqpUnitOutputCost (F : ℝⁿ → ℝ) (p q : ℕ) (P : ARqpCParams) (ε : ℕ → ℝ) (xS y : ℝⁿ)
    (δ : ℕ → ℝ) (nF nD : ℕ) : Prop :=
  Optimization.IsARqpUnitOutputCost F p q P.toARqpParams ε xS y δ nF nD

/-- One INNER call by ARqp on `ℝⁿ` with unit radii, with its evaluation counts, under the
anchored bounds of `F` (`AnchoredCompositeBounds` with `c = 0`, `X₀ = ℝⁿ`) on a set `S`
containing the sublevel set of `F` at `x^S` (`Optimization.exists_isARqpUnitOutputCost`). -/
theorem exists_isARqpUnitOutputCost_anchored {L : ℕ → ℝ} {S : Set ℝⁿ}
    (hF : AnchoredCompositeBounds F (zeroCon n) univ S p L (fun _ => 0))
    {flow : ℝ} (hb : ∀ y, flow ≤ F y) (P : ARqpCParams) (hθς : P.θ < P.ς) (hq : 1 ≤ q)
    (hq2 : q ≤ 2) (hqp : q ≤ p) (xS : ℝⁿ) (hS : ∀ y, F y ≤ F xS → y ∈ S)
    (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1) :
    ∃ (y : ℝⁿ) (nF nD : ℕ), IsARqpUnitOutputCost F p q P ε xS y (fun _ => 1) nF nD :=
  Optimization.exists_isARqpUnitOutputCost hb hF.lipschitzDerivsAnchored_f hF.one_le hF.jet_f
    P.toARqpParams P.σmin_pos hθς hq hq2 hqp xS hS hε

/-- The additive cost contract of an ARqp call on `ℝⁿ` with unit radii, under the anchored
bounds of `exists_isARqpUnitOutputCost_anchored` (`Optimization.IsARqpUnitOutputCost.cost_le`,
with the maximum `innerEvalBound` in place of the minimum). -/
theorem IsARqpUnitOutputCost.cost_le_add_anchored {L : ℕ → ℝ} {S : Set ℝⁿ} {xS y : ℝⁿ}
    {δ' : ℕ → ℝ} {nF nD : ℕ}
    (hF : AnchoredCompositeBounds F (zeroCon n) univ S p L (fun _ => 0)) (hb : ∀ y, 0 ≤ F y)
    (hθς : P.θ < P.ς) (hq : 1 ≤ q) (hqp : q ≤ p) (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1)
    (h : IsARqpUnitOutputCost F p q P ε xS y δ' nF nD) (hS : ∀ y, F y ≤ F xS → y ∈ S) :
    (nF : ℝ) ≤ innerEvalBound (Optimization.kappaAARqpOf True P.toARqpParams L p q)
        (Optimization.arqpPiOf True p) q (F xS) ε + Optimization.kappaCARqp P.toARqpParams L p ∧
    (nD : ℝ) ≤ innerEvalBound (Optimization.kappaSARqpOf True P.toARqpParams L p q)
        (Optimization.arqpPiOf True p) q (F xS) ε + 2 := by
  obtain ⟨h1, h2⟩ := Optimization.IsARqpUnitOutputCost.cost_le (flow := 0) h hb
    hF.lipschitzDerivsAnchored_f hF.one_le hF.jet_f hS P.σmin_pos hθς hq hqp hε
  rw [sub_zero] at h1 h2
  have hπ : ∀ j ∈ Finset.Icc 1 q, 0 ≤ Optimization.arqpPiOf True p j := fun j _ =>
    Optimization.arqpPiOf_nonneg True p j
  have hκs := Optimization.kappaSARqpOf_pos (q := q) True P.σmin_pos hθς hF.one_le
  have hκa : 0 ≤ Optimization.kappaAARqpOf True P.toARqpParams L p q := by
    rw [Optimization.kappaAARqpOf_def]
    exact mul_nonneg hκs.le Optimization.arqpKappaUns_nonneg
  have hB1 := div_finMin_le_innerEvalBound hκa (hb xS) hπ hq hε
  have hB2 := div_finMin_le_innerEvalBound hκs.le (hb xS) hπ hq hε
  exact ⟨by linarith, by linarith⟩

end InnerCall

section LENq

/-- The construction of LENq-SC runs from an INNER oracle: if from every `y ∈ X` with
`‖r(y)‖ ≤ ‖r(x₀)‖`, `0 < ‖r(y)‖` and `β ‖r(y)‖ ≤ 1` some output `o = (x', δ', nF, nD)`
satisfies (14.3.22), does not
increase `‖r‖` and has the property `Good y o`, there is a LENq-SC run whose `k`-th call output
has the property `Good x_{k-1}`. -/
theorem lenq_core_of {r : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {q : ℕ} {ε : ℕ → ℝ}
    (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {x₀ : ℝⁿ} (hx₀ : x₀ ∈ X) (hβr : β * ‖r x₀‖ < 1)
    (Good : ℝⁿ → ℝⁿ × (ℕ → ℝ) × ℕ × ℕ → Prop)
    (hgood : ∀ y : ℝⁿ, y ∈ X → ‖r y‖ ≤ ‖r x₀‖ → 0 < ‖r y‖ → β * ‖r y‖ ≤ 1 →
      ∃ o : ℝⁿ × (ℕ → ℝ) × ℕ × ℕ,
      o.1 ∈ X ∧ ‖r o.1‖ ≤ ‖r y‖ ∧ (∀ j ∈ Finset.Icc 1 q, 0 < o.2.1 j ∧ o.2.1 j ≤ 1) ∧
      (∀ j ∈ Finset.Icc 1 q, Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 r) o.1) j
        (o.2.1 j) {d | o.1 + d ∈ X} ≤ β * ‖r y‖ * ε j * o.2.1 j ^ j / j !) ∧ Good y o) :
    ∃ (x : ℕ → ℝⁿ) (δ : ℕ → ℕ → ℝ) (nF nD : ℕ → ℕ), x 0 = x₀ ∧
      algorithm_14_3_1 r X q ε β x δ ∧
      ∀ k, 1 ≤ k → (∀ i < k, ¬ lenStop r X q ε x δ i) →
        Good (x (k - 1)) (x k, δ k, nF k, nD k) := by
  classical
  -- one INNER call from every admissible point
  have hcall : ∀ y : ℝⁿ, ∃ o : ℝⁿ × (ℕ → ℝ) × ℕ × ℕ, y ∈ X → ‖r y‖ ≤ ‖r x₀‖ → 0 < ‖r y‖ →
      β * ‖r y‖ ≤ 1 → o.1 ∈ X ∧ ‖r o.1‖ ≤ ‖r y‖ ∧
      (∀ j ∈ Finset.Icc 1 q, 0 < o.2.1 j ∧ o.2.1 j ≤ 1) ∧
      (∀ j ∈ Finset.Icc 1 q, Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 r) o.1) j
        (o.2.1 j) {d | o.1 + d ∈ X} ≤ β * ‖r y‖ * ε j * o.2.1 j ^ j / j !) ∧ Good y o := by
    intro y
    by_cases hy : y ∈ X ∧ ‖r y‖ ≤ ‖r x₀‖ ∧ 0 < ‖r y‖ ∧ β * ‖r y‖ ≤ 1
    · obtain ⟨o, ho⟩ := hgood y hy.1 hy.2.1 hy.2.2.1 hy.2.2.2
      exact ⟨o, fun _ _ _ _ => ho⟩
    · exact ⟨(y, 1, 0, 0), fun h1 h2 h3 h4 => absurd ⟨h1, h2, h3, h4⟩ hy⟩
  choose call hcall using hcall
  let seq : ℕ → ℝⁿ × (ℕ → ℝ) × ℕ × ℕ := fun k =>
    Nat.rec (x₀, fun _ => 1, 0, 0) (fun _ o => call o.1) k
  have hseq : ∀ k, seq (k + 1) = call (seq k).1 := fun _ => rfl
  set x : ℕ → ℝⁿ := fun k => (seq k).1 with hxdef
  set δ : ℕ → ℕ → ℝ := fun k => (seq k).2.1 with hδdef
  have hε₀ : 0 < ε 0 := (hε 0 (by simp)).1
  -- the invariant: feasible, residual at most the initial one
  have hinv : ∀ k, (∀ i < k, ¬ lenStop r X q ε x δ i) → x k ∈ X ∧ ‖r (x k)‖ ≤ ‖r x₀‖ := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨hx₀, le_rfl⟩
    | succ k ih =>
      intro hk
      obtain ⟨hxk, hrk⟩ := ih fun i hi => hk i (hi.trans k.lt_succ_self)
      have hpos : 0 < ‖r (x k)‖ :=
        hε₀.trans (not_le.1 fun h' => hk k k.lt_succ_self (Or.inl h'))
      have hβk : β * ‖r (x k)‖ ≤ 1 := by nlinarith
      obtain ⟨h1, h2, -⟩ := hcall (x k) hxk hrk hpos hβk
      exact ⟨h1, h2.trans hrk⟩
  -- the call at iteration `k + 1`
  have hstep : ∀ k, (∀ i < k + 1, ¬ lenStop r X q ε x δ i) →
      x (k + 1) ∈ X ∧ (∀ j ∈ Finset.Icc 1 q, 0 < δ (k + 1) j ∧ δ (k + 1) j ≤ 1) ∧
      (∀ j ∈ Finset.Icc 1 q, Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 r) (x (k + 1))) j
        (δ (k + 1) j) {d | x (k + 1) + d ∈ X} ≤ β * ‖r (x k)‖ * ε j * δ (k + 1) j ^ j / j !) ∧
      Good (x k) (seq (k + 1)) := by
    intro k hk
    obtain ⟨hxk, hrk⟩ := hinv k fun i hi => hk i (hi.trans k.lt_succ_self)
    have hpos : 0 < ‖r (x k)‖ :=
      hε₀.trans (not_le.1 fun h' => hk k k.lt_succ_self (Or.inl h'))
    have hβk : β * ‖r (x k)‖ ≤ 1 := by nlinarith
    obtain ⟨h1, -, h3, h4, h5⟩ := hcall (x k) hxk hrk hpos hβk
    exact ⟨h1, h3, h4, h5⟩
  refine ⟨x, δ, fun k => (seq k).2.2.1, fun k => (seq k).2.2.2, rfl, ⟨hx₀, fun j hj => (hε j hj).1,
    fun j hj => (hε j hj).2, hβ0, hβ1, hβr, ?_, ?_, ?_⟩, ?_⟩
  · intro k hk1 hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hk1
    exact (hstep k hk).1
  · intro k hk1 hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hk1
    exact (hstep k hk).2.1
  · intro k hk1 hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hk1
    exact (hstep k hk).2.2.1
  · intro k hk1 hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hk1
    exact (hstep k hk).2.2.2

/-- **LENq-SC runs with INNER = ARqp-SC under anchored bounds** (the construction of
`exists_algorithm_14_3_1`): if `Φ₂` has the anchored bounds of the ARqpC analysis
(`AnchoredCompositeBounds`, constants `L`) on a set `S` containing every `y ∈ X` with
`‖r(y)‖ ≤ ‖r(x₀)‖`, for an open convex `X₀ ⊇ X`, there is a LENq-SC run from `x₀` whose `k`-th
INNER call is an ARqp-SC call with evaluation counts `nF k`, `nD k`. -/
theorem lenq_core_anchored {r : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} (hX : IsClosed X) {p q : ℕ}
    (hq : 1 ≤ q) (hqp : q ≤ p) {L : ℕ → ℝ} {X₀ S : Set ℝⁿ}
    (hΦ : AnchoredCompositeBounds (phi2 r) (zeroCon n) X₀ S p L (fun _ => 0)) (hXX₀ : X ⊆ X₀)
    (P : ARqpCParams) (hθς : P.θ < P.ς) {ε : ℕ → ℝ}
    (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {x₀ : ℝⁿ} (hx₀ : x₀ ∈ X) (hS : ∀ y ∈ X, ‖r y‖ ≤ ‖r x₀‖ → y ∈ S) (hβr : β * ‖r x₀‖ < 1) :
    ∃ (x : ℕ → ℝⁿ) (δ : ℕ → ℕ → ℝ) (nF nD : ℕ → ℕ), x 0 = x₀ ∧
      algorithm_14_3_1 r X q ε β x δ ∧
      ∀ k, 1 ≤ k → (∀ i < k, ¬ lenStop r X q ε x δ i) →
        IsARqpSCOutputCost (phi2 r) X p q P (fun j => β * ‖r (x (k - 1))‖ * ε j) (x (k - 1))
          (x k) (δ k) (nF k) (nD k) := by
  have hεI : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1 := fun j hj =>
    hε j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
  refine lenq_core_of hε hβ0 hβ1 hx₀ hβr (fun y o => IsARqpSCOutputCost (phi2 r) X p q P
    (fun j => β * ‖r y‖ * ε j) y o.1 o.2.1 o.2.2.1 o.2.2.2) fun y hyX hy0 hry hβy => ?_
  have hε' : ∀ j ∈ Finset.Icc 1 q, 0 < β * ‖r y‖ * ε j ∧ β * ‖r y‖ * ε j ≤ 1 := fun j hj =>
    ⟨by have := (hεI j hj).1; positivity,
      by nlinarith [(hεI j hj).1, (hεI j hj).2, mul_pos hβ0 hry]⟩
  obtain ⟨z, δz, nF, nD, hout⟩ := exists_isARqpSCOutputCost_anchored hΦ hXX₀ (flow := 0)
    (fun _ _ => by rw [phi2_apply]; positivity) P hθς hq hqp hX hyX
    (fun z hz hzy => hS z hz ((Constrained.halfSqNorm_le_halfSqNorm_iff.1 hzy).trans hy0)) hε'
  exact ⟨(z, δz, nF, nD), hout.isARqpOutput.mem,
    Constrained.halfSqNorm_le_halfSqNorm_iff.1 hout.isARqpOutput.le,
    hout.isARqpOutput.radius_mem, hout.isARqpOutput.isEpsDeltaApprox, hout⟩

/-- **Existence of LENq-SC runs** ([cartis2022evaluation], Algorithm 14.3.1 is well defined, with
INNER = ARqp-SC). Let `X` be closed, `1 ≤ q ≤ p`, `Φ₂ = ½ ‖r‖²` satisfy Φ₂.D1pL (on `ℝⁿ`), and
`P` be ARqpC constants with `θ < ς`. Then for every admissible choice of tolerances
`ε_j ∈ (0, 1]` (`j ∈ [0 : q]`), of `β ∈ (0, 1)` with `β ‖r(x₀)‖ < 1` and every starting point
`x₀ ∈ X`, there is a LENq-SC run from `x₀` in which every iterate `x_k` (`k ≥ 1`, before
termination) is the output of an ARqp-SC call `INNER(Φ₂, X, q, x_{k-1}, β ‖r(x_{k-1})‖ ε)`
(run as ARqpC-SC with `c = 0`, `h = 0`; it terminates by Theorem 14.2.4). -/
theorem exists_algorithm_14_3_1 {r : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} (hX : IsClosed X) {p q : ℕ}
    (hq : 1 ≤ q) (hqp : q ≤ p) {L : ℕ → ℝ} (hΦ : Chapter12.AssumptionD1pL (phi2 r) p L)
    (P : ARqpCParams) (hθς : P.θ < P.ς) {ε : ℕ → ℝ}
    (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {x₀ : ℝⁿ} (hx₀ : x₀ ∈ X) (hβr : β * ‖r x₀‖ < 1) :
    ∃ (x : ℕ → ℝⁿ) (δ : ℕ → ℕ → ℝ) (nF nD : ℕ → ℕ), x 0 = x₀ ∧
      algorithm_14_3_1 r X q ε β x δ ∧
      ∀ k, 1 ≤ k → (∀ i < k, ¬ lenStop r X q ε x δ i) →
        IsARqpSCOutputCost (phi2 r) X p q P (fun j => β * ‖r (x (k - 1))‖ * ε j) (x (k - 1))
          (x k) (δ k) (nF k) (nD k) :=
  lenq_core_anchored hX hq hqp (AnchoredCompositeBounds.of_global hΦ (assumptionCD1pL_zeroCon p)
    (hq.trans hqp) univ) (subset_univ X) P hθς hε hβ0 hβ1 hx₀ (fun y _ _ => mem_univ y) hβr

/-- **LENq-SC runs on `ℝⁿ` with INNER = ARqp with unit radii** (`1 ≤ q ≤ min(2, p)`): if
`Φ₂ = ½ ‖r‖²` has the anchored bounds of the ARqp analysis (constants `L`, `X₀ = ℝⁿ`) on a set
`S` containing every `y` with `‖r(y)‖ ≤ ‖r(x₀)‖`, there is a LENq-SC run from `x₀`, terminating
at its first hit `k_max` (Theorem 14.3.3), whose `k`-th INNER call is an ARqp call with unit radii
using `nF k` evaluations of `Φ₂` and `nD k` of its derivatives (`IsARqpUnitOutputCost`). -/
theorem exists_algorithm_14_3_1_unit {r : ℝⁿ → ℝᵐ} {p q : ℕ} (hq : 1 ≤ q)
    (hq2 : q ≤ 2) (hqp : q ≤ p) {L : ℕ → ℝ} {S : Set ℝⁿ}
    (hΦ : AnchoredCompositeBounds (phi2 r) (zeroCon n) univ S p L (fun _ => 0))
    (P : ARqpCParams) (hθς : P.θ < P.ς) {ε : ℕ → ℝ}
    (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (x₀ : ℝⁿ) (hS : ∀ y, ‖r y‖ ≤ ‖r x₀‖ → y ∈ S) (hβr : β * ‖r x₀‖ < 1) :
    ∃ (x : ℕ → ℝⁿ) (δ : ℕ → ℕ → ℝ) (nF nD : ℕ → ℕ) (kmax : ℕ), x 0 = x₀ ∧
      algorithm_14_3_1 r univ q ε β x δ ∧ Optimization.IsFirstHit (lenStop r univ q ε x δ) kmax ∧
      ∀ k, 1 ≤ k → k ≤ kmax →
        IsARqpUnitOutputCost (phi2 r) p q P (fun j => β * ‖r (x (k - 1))‖ * ε j) (x (k - 1))
          (x k) (δ k) (nF k) (nD k) := by
  have hεI : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1 := fun j hj =>
    hε j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
  obtain ⟨x, δ, nF, nD, hx0, hrun, hcalls⟩ := lenq_core_of (X := univ) hε hβ0 hβ1 (mem_univ x₀)
    hβr (fun y o => IsARqpUnitOutputCost (phi2 r) p q P (fun j => β * ‖r y‖ * ε j) y o.1 o.2.1
      o.2.2.1 o.2.2.2) fun y _ hy0 hry hβy => by
    have hε' : ∀ j ∈ Finset.Icc 1 q, 0 < β * ‖r y‖ * ε j ∧ β * ‖r y‖ * ε j ≤ 1 := fun j hj =>
      ⟨by have := (hεI j hj).1; positivity,
        by nlinarith [(hεI j hj).1, (hεI j hj).2, mul_pos hβ0 hry]⟩
    obtain ⟨z, nF, nD, hout⟩ := exists_isARqpUnitOutputCost_anchored hΦ (flow := 0)
      (fun _ => by rw [phi2_apply]; positivity) P hθς hq hq2 hqp y
      (fun z hz => hS z ((Constrained.halfSqNorm_le_halfSqNorm_iff.1 hz).trans hy0)) hε'
    refine ⟨(z, fun _ => 1, nF, nD), mem_univ _, Constrained.halfSqNorm_le_halfSqNorm_iff.1 hout.le,
      fun _ _ => ⟨one_pos, le_rfl⟩, fun j hj => ?_, hout⟩
    have := hout.2.2 j hj
    simpa using this
  obtain ⟨⟨kmax, hhit, -, -⟩, -⟩ := theorem_14_3_3 hrun
  exact ⟨x, δ, nF, nD, kmax, hx0, hrun, hhit,
    fun k hk1 hk => hcalls k hk1 fun i hi => hhit.2 i (hi.trans_le hk)⟩

/-- **The cost contract (14.3.20)–(14.3.21) fails for `q = 1`** ([cartis2022evaluation],
§14.3.2.1, with INNER = ARqp-SC and the exponent `π_1 = (p+1)/p` of its row of (14.2.12), in
either radii mode, `p ≥ 2`). For every constant `κ` (in particular for any choice independent of
`x^S` and `ε`, as the book's `κ_INNER`), every ARqpC constants `P` with `θ < ς` and every
`β ∈ (0, 1)`, there is a LENq-SC run (`algorithm_14_3_1`, on `X = ℝ` with `Φ₂ = ½ ‖r‖²`
satisfying Φ₂.D1pL with constants `1`, tolerances in `(0, 1]` and `β ‖r(x₀)‖ < 1`) which does not
terminate at `k = 0` and whose first INNER call, an ARqp-SC call from `x^S = x₀` with tolerance
`β ‖r(x₀)‖ ε_1` (`IsARqpSCOutputCost`, constructed as in `exists_algorithm_14_3_1`), uses more
evaluations of `Φ₂`, and more of its derivatives, than the printed bound
`κ Φ₂(x^S) (β ‖r(x^S)‖ ε_1)^{-π_1}`. Every call uses at least one evaluation of each kind
(`Optimization.IsARqpOutputCost.one_le`), while the bound is
`(κ/2) β^{-π_1} ‖r(x^S)‖^{2-π_1} ε_1^{-π_1}`, which tends to `0` with `‖r(x^S)‖` since
`π_1 < 2`; the run uses `r ≡ R` constant with `R`
small and `ε₀ = R/2`. (The count of a call includes its initial evaluations at `x^S`, the
per-run convention of Theorems 12.2.14 and 14.2.4; a constant multiple `κ ‖r(x₀)‖` of the bound,
as the book allows for `ν`, still tends to `0`, since `x^S = x₀`.) The additive form
`IsARqpSCOutputCost.cost_le_arqp_add_anchored` (with `theorem_14_3_4_add`) is the
corrected statement. -/
theorem exists_algorithm_14_3_1_cost_contract_counterexample {p : ℕ} (hp : 2 ≤ p)
    (u : Prop) [Decidable u] (P : ARqpCParams) (hθς : P.θ < P.ς) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (κ : ℝ) :
    ∃ (r : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) (ε : ℕ → ℝ)
      (x : ℕ → EuclideanSpace ℝ (Fin 1)) (δ : ℕ → ℕ → ℝ) (nF nD : ℕ → ℕ) (kmax : ℕ),
      Chapter12.AssumptionD1pL (phi2 r) p (fun _ => 1) ∧
      (∀ j ∈ Finset.range 2, 0 < ε j ∧ ε j ≤ 1) ∧ β * ‖r (x 0)‖ < 1 ∧
      algorithm_14_3_1 r univ 1 ε β x δ ∧
      Optimization.IsFirstHit (lenStop r univ 1 ε x δ) kmax ∧ 1 ≤ kmax ∧
      IsARqpSCOutputCost (phi2 r) univ p 1 P (fun j => β * ‖r (x 0)‖ * ε j) (x 0) (x 1) (δ 1)
        (nF 1) (nD 1) ∧
      innerEvalBound κ (Optimization.arqpPiOf u p) 1 (phi2 r (x 0))
          (fun j => β * ‖r (x 0)‖ * ε j) < nF 1 ∧
      innerEvalBound κ (Optimization.arqpPiOf u p) 1 (phi2 r (x 0))
          (fun j => β * ‖r (x 0)‖ * ε j) < nD 1 := by
  have hp1 : 1 ≤ p := by omega
  set π := Optimization.arqpPiOf u p 1 with hπ
  have hπe : π = ((p : ℝ) + 1) / p := Optimization.arqpPiOf_one u hp1
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hπ2 : π < 2 := by rw [hπe, div_lt_iff₀ (by linarith)]; linarith
  have hπ0 : 0 < π := by rw [hπe]; positivity
  obtain ⟨R, hR0, hR1, hRκ⟩ :=
    Constrained.exists_mul_sq_div_two_mul_rpow_neg_lt_one hπ0 hπ2 hβ0 hβ1 κ
  set r : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1) :=
    fun _ => EuclideanSpace.single 0 R
  have hr : ∀ y, ‖r y‖ = R := fun y => by simp [r, abs_of_pos hR0]
  have hΦ : Chapter12.AssumptionD1pL (phi2 r) p (fun _ => 1) := by
    have e : phi2 r = fun _ => R ^ 2 / 2 := funext fun y => by rw [phi2_apply, hr y]
    rw [e]
    refine .of_iteratedFDerivLipschitzOn contDiff_const (fun _ _ => le_rfl) fun j hj =>
      iteratedFDerivLipschitzOn_iff.2 fun a _ b _ => ?_
    have hj0 : j ≠ 0 := by have := (Finset.mem_Icc.1 hj).1; omega
    simp [iteratedFDeriv_const_of_ne hj0]
  set ε : ℕ → ℝ := fun j => if j = 0 then R / 2 else 1
  have hε : ∀ j ∈ Finset.range (1 + 1), 0 < ε j ∧ ε j ≤ 1 := fun j _ => by
    simp only [ε]; split_ifs
    · exact ⟨by positivity, by linarith⟩
    · exact ⟨one_pos, le_rfl⟩
  have hβr : β * ‖r 0‖ < 1 := by rw [hr 0]; nlinarith
  obtain ⟨x, δ, nF, nD, -, hrun, hcalls⟩ := lenq_core_anchored (X := univ) isClosed_univ le_rfl hp1
    (AnchoredCompositeBounds.of_global hΦ (assumptionCD1pL_zeroCon p) hp1 univ) (subset_univ _) P
    hθς hε hβ0 hβ1 (mem_univ 0) (fun y _ _ => mem_univ y) hβr
  obtain ⟨⟨kmax, hhit, -⟩, -⟩ := theorem_14_3_3 hrun
  have hk1 : 1 ≤ kmax := by
    by_contra h0
    have h0 : kmax = 0 := by omega
    rcases h0 ▸ hhit.1 with h | ⟨h, -⟩
    · rw [hr (x 0)] at h
      simp only [ε, ite_eq_left] at h
      linarith
    · omega
  have hcall := hcalls 1 le_rfl fun i hi => hhit.2 i (by omega)
  have hbound : innerEvalBound κ (Optimization.arqpPiOf u p) 1 (phi2 r (x 0))
      (fun j => β * ‖r (x 0)‖ * ε j) < 1 := by
    rw [innerEvalBound_one, phi2_apply, hr (x 0)]
    simp only [ε, one_ne_zero, ite_false, mul_one]
    rw [← hπ]
    exact hRκ
  obtain ⟨h1, h2⟩ := hcall.one_le
  refine ⟨r, ε, x, δ, nF, nD, kmax, hΦ, hε, by rw [hr (x 0)]; nlinarith, hrun, hhit, hk1, hcall,
    hbound.trans_le (by exact_mod_cast h1), hbound.trans_le (by exact_mod_cast h2)⟩

end LENq

section TPqp


/-- The data of one INNER call of Phase 2: iterates, length, successful iterations, radii
(`Constrained.InnerCall`). -/
abbrev CallOut (n : ℕ) := Constrained.InnerCall (EuclideanSpace ℝ (Fin n))

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {p q : ℕ} {P : ARqpCParams} {ε : ℕ → ℝ}
  {θ β : ℝ}

/-- The iterates `x_{k,0}, …, x_{k,e}` and successful iterations of one INNER call of Phase 2 of
TPqp-GC on `X = ℝⁿ`, realized by ARqp with unit radii on `F` with tolerances `ε`
(`Optimization.IsARqpUnitCall`): they are the first `e + 1` iterates of an ARqp run
(`Chapter12.algorithm_12_2_2`, initial radii `1`, Step-2 radii `1` before termination) on `F`
whose first termination index is at least `e`, and the successful iterations are those of the
run. -/
abbrev IsARqpUnitCall (F : ℝⁿ → ℝ) (p q : ℕ) (P : ARqpCParams) (ε : ℕ → ℝ) (xi : ℕ → ℝⁿ)
    (e : ℕ) (succ : ℕ → Prop) : Prop :=
  Optimization.IsARqpUnitCall F p q P.toARqpParams ε xi e succ

open Classical in
/-- The construction of Phase 2 of TPqp-GC from an INNER oracle: if from every `(x, t)` with
`x ∈ X`, `θε₀ ≤ ‖r(x, t)‖ ≤ ε₀` and `t ≤ f(x)` some call `o` (iterates from `x` not increasing
`μ(·, t)`, stopped as soon as `‖r(·, t)‖ < θε₀`, ending at a point of `X` with radii in
`(0, 1]` where the first or the third test of (14.3.32) holds) has the property `Good x t o`,
there is a Phase-2 run whose `k`-th call has the property `Good x_k t_k`
(`Constrained.HighOrderTargetSeq.exists_run_of_oracle`, whose calls may also stop at
`f < t_k`). -/
theorem phase2_core_of (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 < β) (hβθ : β ≤ θ)
    (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) {x₁ : ℝⁿ} (hx₁ : x₁ ∈ X)
    (hc₁ : ‖c x₁‖ ≤ θ * ε 0) (Good : ℝⁿ → ℝ → CallOut n → Prop)
    (hgood : ∀ x t, x ∈ X → θ * ε 0 ≤ Constrained.targetResidual f c t x →
      Constrained.targetResidual f c t x ≤ ε 0 → t ≤ f x → ∃ o : CallOut n,
        o.xi 0 = x ∧ o.xi o.e ∈ X ∧ (∀ j ∈ Finset.Icc 1 q, 0 < o.δ j ∧ o.δ j ≤ 1) ∧
        (Constrained.targetResidual f c t (o.xi o.e) < θ * ε 0 ∨
          meritCrit f c X q ε t (o.xi o.e) o.δ) ∧
        (∀ i < o.e, Constrained.targetMerit f c t (o.xi (i + 1)) ≤
          Constrained.targetMerit f c t (o.xi i)) ∧
        (∀ i < o.e, θ * ε 0 ≤ Constrained.targetResidual f c t (o.xi i)) ∧
        Constrained.targetResidual f c t (o.xi o.e) ≤ Constrained.targetResidual f c t x ∧
        Good x t o) :
    ∃ D : TPqpSeq n, IsTPqpGCPhase2 f c X q θ β ε x₁ D ∧
      ∀ k, 1 ≤ k → D.Before f c X q θ ε k →
        (D.x k ∈ X ∧ θ * ε 0 ≤ Constrained.targetResidual f c (D.t k) (D.x k) ∧
          Constrained.targetResidual f c (D.t k) (D.x k) ≤ ε 0 ∧ D.t k ≤ f (D.x k)) ∧
        Good (D.x k) (D.t k) ⟨D.xi k, D.e k, D.succ k, D.δ (k + 1)⟩ :=
  Constrained.HighOrderTargetSeq.exists_run_of_oracle hθ0 hθ1 hβ0 hβθ hε hx₁ hc₁ Good
    fun x t hx hlo hhi hft => (hgood x t hx hlo hhi hft).imp fun _ ⟨h0, h1, h2, h3, h4⟩ =>
      ⟨h0, h1, h2, h3.imp_right Or.inr, h4⟩

/-- TPqp-GC runs from Phase-2 runs under anchored bounds for `ν` on `𝓛_ν(x₀)`: Phase 1 is a
LENq-SC run with INNER = ARqp-SC on `ν` (`lenq_core_anchored`), and Phase 2 is any run with a
property `Q` provided by `hphase2`. Under global assumptions this is
`exists_algorithm_14_3_2_of_phase2_anchored`. -/
theorem exists_algorithm_14_3_2_of_phase2_anchored (hX : IsClosed X) (hq : 1 ≤ q)
    (hqp : q ≤ p) {X₀ : Set ℝⁿ} {Lν : ℕ → ℝ} {x₀ : ℝⁿ}
    (hν : AnchoredCompositeBounds (phi2 c) (zeroCon n) X₀ (nuSublevel c X x₀) p Lν (fun _ => 0))
    (hXX₀ : X ⊆ X₀) (P : ARqpCParams) (hθς : P.θ < P.ς) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) {β₁ : ℝ} (hβ₁0 : 0 < β₁)
    (hβ₁1 : β₁ < 1) (hx₀ : x₀ ∈ X) (hβ₁c : β₁ * ‖c x₀‖ < 1) {Q : TPqpSeq n → Prop}
    (hphase2 : ∀ x₁ ∈ X, ‖c x₁‖ ≤ θ * ε 0 →
      ∃ D : TPqpSeq n, IsTPqpGCPhase2 f c X q θ β ε x₁ D ∧ Q D) :
    ∃ (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq n) (nF nD : ℕ → ℕ),
      algorithm_14_3_2 f c X q θ β₁ β ε x₀ xP δP k₁ D ∧
      (∀ k, 1 ≤ k → k ≤ k₁ → IsARqpSCOutputCost (phi2 c) X p q P
        (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j) (xP (k - 1)) (xP k) (δP k) (nF k)
          (nD k)) ∧
      (‖c (xP k₁)‖ ≤ θ * ε 0 → Q D) := by
  have hε₁ : ∀ j ∈ Finset.range (q + 1), 0 < phase1Tol θ ε j ∧ phase1Tol θ ε j ≤ 1 := by
    intro j hj
    by_cases h0 : j = 0
    · subst h0
      obtain ⟨h1, h2⟩ := hε 0 hj
      simp only [phase1Tol_zero]
      exact ⟨mul_pos hθ0 h1, by nlinarith⟩
    · rw [phase1Tol_of_ne θ ε h0]
      exact hε j hj
  obtain ⟨xP, δP, nF, nD, hxP0, hrun, hcalls⟩ :=
    lenq_core_anchored hX hq hqp hν hXX₀ P hθς hε₁ hβ₁0 hβ₁1 hx₀ (fun y hy hcy => ⟨hy, hcy⟩)
      hβ₁c
  obtain ⟨⟨k₁, hhit, -, -⟩, -⟩ := theorem_14_3_3 hrun
  have hcalls' : ∀ k, 1 ≤ k → k ≤ k₁ → IsARqpSCOutputCost (phi2 c) X p q P
      (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j) (xP (k - 1)) (xP k) (δP k) (nF k)
        (nD k) :=
    fun k hk1 hk => hcalls k hk1 fun i hi => hhit.2 i (hi.trans_le hk)
  by_cases hc : ‖c (xP k₁)‖ ≤ θ * ε 0
  · have hmem : xP k₁ ∈ X := by
      rcases Nat.eq_zero_or_pos k₁ with h0 | hpos
      · rw [h0]; exact hrun.mem_zero
      · exact hrun.mem k₁ hpos hhit.2
    obtain ⟨D, hD, hQ⟩ := hphase2 _ hmem hc
    exact ⟨xP, δP, k₁, D, nF, nD, ⟨hxP0, hrun, hhit, fun _ => hD⟩, hcalls', fun _ => hQ⟩
  · exact ⟨xP, δP, k₁, ⟨fun _ => x₀, fun _ => 0, fun _ _ => 0, fun _ _ => x₀, fun _ => 0,
      fun _ _ => False⟩, nF, nD, ⟨hxP0, hrun, hhit, fun h => absurd h hc⟩, hcalls',
      fun h => absurd h hc⟩

/-- The Phase-1 INNER calls of a TPqp-GC run with INNER = ARqp-SC satisfy the cost contract
(14.3.20)–(14.3.21) with `π_j = j + 1` under anchored bounds for `ν` on `𝓛_ν(x₀)`
(`IsARqpSCOutputCost.cost_le_anchored`). -/
theorem phase1_cost_le_anchored {β₁ : ℝ} {x₀ : ℝⁿ} {xP : ℕ → ℝⁿ} {δP : ℕ → ℕ → ℝ}
    {k₁ : ℕ} {D : TPqpSeq n} {nF₁ nD₁ : ℕ → ℕ}
    (h : algorithm_14_3_2 f c X q θ β₁ β ε x₀ xP δP k₁ D) (hq : 1 ≤ q) {X₀ : Set ℝⁿ}
    {Lν : ℕ → ℝ}
    (hν : AnchoredCompositeBounds (phi2 c) (zeroCon n) X₀ (nuSublevel c X x₀) p Lν (fun _ => 0))
    (hXX₀ : X ⊆ X₀) (hθς : P.θ < P.ς) (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1)
    (hcalls : ∀ k, 1 ≤ k → k ≤ k₁ → IsARqpSCOutputCost (phi2 c) X p q P
      (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j) (xP (k - 1)) (xP k) (δP k) (nF₁ k)
        (nD₁ k)) :
    ∀ k ∈ Finset.Icc 1 k₁,
      (nF₁ k : ℝ) ≤ innerEvalBound (arqpSCKappaF P Lν p q) (fun l => (l : ℝ) + 1) q
        (phi2 c (xP (k - 1))) (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j) ∧
      (nD₁ k : ℝ) ≤ innerEvalBound (arqpSCKappaD P Lν p q) (fun l => (l : ℝ) + 1) q
        (phi2 c (xP (k - 1))) (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j) := by
  have hεI : ∀ l ∈ Finset.Icc 1 q, 0 < ε l ∧ ε l ≤ 1 := fun l hl =>
    hε l (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hl).2))
  have hβ₁1 := h.phase1.β_lt_one
  have hβ₁0 := h.phase1.β_pos
  intro k hk
  obtain ⟨hk1, hkk⟩ := Finset.mem_Icc.1 hk
  have hmem : xP (k - 1) ∈ X := by
    rcases Nat.eq_zero_or_pos (k - 1) with h0 | hpos
    · rw [h0]; exact h.phase1.mem_zero
    · exact h.phase1.mem (k - 1) hpos fun i hi => h.phase1_end.2 i (by omega)
  have hck : ‖c (xP (k - 1))‖ ≤ ‖c x₀‖ := by
    have := h.phase1.norm_le_pow_mul (Nat.zero_le (k - 1)) fun l hl =>
      h.phase1_end.2 l (by omega)
    rw [h.start] at this
    exact this.trans (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hβ₁0.le hβ₁1.le))
  refine (hcalls k hk1 hkk).cost_le_anchored hν hXX₀ (fun y _ => by rw [phi2_apply]; positivity)
    hθς hmem (fun y hy hyk => ⟨hy, (Constrained.halfSqNorm_le_halfSqNorm_iff.1 hyk).trans hck⟩) ?_
  have h1q : 1 ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, hq⟩
  rw [phase1Tol_of_ne θ ε one_ne_zero, phi2_apply]
  have hb1 : β₁ * ε 1 ≤ 1 := by nlinarith [hεI 1 h1q]
  have hb0 : 0 ≤ β₁ * ε 1 := by have := (hεI 1 h1q).1; positivity
  have : (β₁ * ‖c (xP (k - 1))‖ * ε 1) ^ 2 = (β₁ * ε 1) ^ 2 * ‖c (xP (k - 1))‖ ^ 2 := by ring
  rw [this]
  have : (β₁ * ε 1) ^ 2 ≤ 1 := pow_le_one₀ hb0 hb1
  nlinarith [sq_nonneg ‖c (xP (k - 1))‖]

end TPqp

end ARqpSCCalls


section ARqpSCAnchored

/-! ### Anchored bounds for the objective of INNER -/

/-- The constants `max(L_j, B_{j+1})`: if `∇^j F` is `L_j`-Lipschitz anchored on `S` and
`‖∇^j F‖ ≤ B_j` on `S`, then the anchored bounds of the ARqpC analysis
(`AnchoredCompositeBounds`, which bounds `‖∇^i F‖` by the constant of order `i - 1`) hold with
these constants. -/
noncomputable def anchoredConst (L B : ℕ → ℝ) : ℕ → ℝ := fun j => max (L j) (B (j + 1))

theorem anchoredConst_apply (L B : ℕ → ℝ) (j : ℕ) : anchoredConst L B j = max (L j) (B (j + 1)) :=
  rfl

/-- The zero constraint map `ℝⁿ → ℝ⁰` has vanishing iterated derivatives (all maps into `ℝ⁰`
vanish). -/
theorem iteratedFDeriv_zeroCon (i : ℕ) (x : ℝⁿ) : iteratedFDeriv ℝ i (zeroCon n) x = 0 := by
  ext v j
  exact j.elim0

/-- The anchored bounds of the ARqpC analysis for INNER on `F` (ARqpC-SC with `c = 0`, `h = 0`)
need only the Lipschitz condition of `∇^p F` anchored on `S` (constant `L_p ≥ 1`) and the bounds
`‖∇^i F‖ ≤ L_{i-1}` on `S` for `i ∈ [2 : p]`. -/
theorem anchoredCompositeBounds_zeroCon_of {F : ℝⁿ → ℝ} {X₀ S : Set ℝⁿ} {p : ℕ} {L : ℕ → ℝ}
    (hX₀ : IsOpen X₀) (hconv : Convex ℝ X₀) (hS : S ⊆ X₀) (hF : ContDiffOn ℝ p F X₀)
    (hL1 : 1 ≤ L p) (hlip : IteratedFDerivLipschitzAnchored F p (L p) S X₀)
    (hbd : ∀ i ∈ Finset.Icc 2 p, ∀ x ∈ S, ‖iteratedFDeriv ℝ i F x‖ ≤ L (i - 1)) :
    AnchoredCompositeBounds F (zeroCon n) X₀ S p L (fun _ => 0) where
  isOpen := hX₀
  convex := hconv
  subset := hS
  contDiffOn_f := hF
  contDiffOn_c := contDiffOn_const
  one_le := hL1
  nonneg := le_rfl
  lipschitz_f := hlip
  lipschitz_c x _ y _ := by simp [iteratedFDeriv_zeroCon]
  norm_f := hbd
  norm_c i _ x _ := by simp [iteratedFDeriv_zeroCon]

/-- Anchored Lipschitz and bounded derivatives of `F` of orders `1, …, p` on an anchor set `S`
(the shape of f.D1pLaB.X) give the anchored bounds of the ARqpC analysis for INNER on `F`
(ARqpC-SC with `c = 0`, `h = 0`) with the constants `anchoredConst L B`
(`anchoredCompositeBounds_zeroCon_of`). -/
theorem anchoredCompositeBounds_zeroCon {F : ℝⁿ → ℝ} {X₀ S : Set ℝⁿ} {p : ℕ} {L B : ℕ → ℝ}
    (hX₀ : IsOpen X₀) (hconv : Convex ℝ X₀) (hS : S ⊆ X₀) (hF : ContDiffOn ℝ p F X₀)
    (hp : 1 ≤ p) (hL1 : 1 ≤ L p)
    (hb : ∀ j ∈ Finset.Icc 1 p, IteratedFDerivLipschitzAnchored F j (L j) S X₀ ∧
      ∀ x ∈ S, ‖iteratedFDeriv ℝ j F x‖ ≤ B j) :
    AnchoredCompositeBounds F (zeroCon n) X₀ S p (anchoredConst L B) (fun _ => 0) :=
  anchoredCompositeBounds_zeroCon_of hX₀ hconv hS hF (hL1.trans (le_max_left _ _))
    ((hb p (Finset.mem_Icc.2 ⟨hp, le_rfl⟩)).1.mono_const (le_max_left _ _)) fun i hi x hx => by
      obtain ⟨hi2, hip⟩ := Finset.mem_Icc.1 hi
      refine ((hb i (Finset.mem_Icc.2 ⟨by omega, hip⟩)).2 x hx).trans ?_
      rw [anchoredConst_apply, show i - 1 + 1 = i by omega]
      exact le_max_right _ _

/-! ### LENq-SC under Φ₂.D1pLaB.X -/

section LENq

end LENq

/-! ### Phase 2 of TPqp-GC under the anchored assumptions -/

section TPqp

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {p q : ℕ} {P : ARqpCParams} {ε : ℕ → ℝ}
  {θ β : ℝ}

/-- The constants `max(L^A_j + L^B_j ‖c(x₀)‖, B^A_{j+1} + B^B_{j+1} ‖c(x₀)‖)` (`anchoredConst`) of
the anchored bounds of `ν = ½ ‖c‖²` on `𝓛_ν(x₀)` given by Lemma 14.3.6 (i) (constants `L^A`, `L^B`,
`B^A`, `B^B`, `r = ‖c(x₀)‖`). -/
noncomputable def nuAnchoredConst (LA LB BA BB : ℕ → ℝ) (r : ℝ) : ℕ → ℝ :=
  anchoredConst (fun j => LA j + LB j * r) (fun j => BA j + BB j * r)

/-- **Anchored bounds for `ν` and `μ(·, t)` from the book's assumptions** ([cartis2022evaluation],
Lemma 14.3.6): under c.D1pLB.X and f.D1pLB.X (on an open convex `X₀ ⊇ X`) there are constants
`L^A_j, L^B_j, B^A_j, B^B_j, L_{μ,j}, B_{μ,j} ≥ 1`, depending only on `m` and the constants of these
assumptions, such that for every `x₀` the function `ν = ½ ‖c‖²` satisfies the anchored bounds of the
ARqpC analysis on `𝓛_ν(x₀)` with the constants `nuAnchoredConst L^A L^B B^A B^B ‖c(x₀)‖`, and every
`μ(·, t)` satisfies them on `𝓛_μ(t)` with the constants `anchoredConst L_μ B_μ`. These are the
hypotheses `hν`, `hμ` (with `hXX₀ = hc.subset`) of the TPqp-GC theorems
stated under anchored bounds (`theorem_14_3_9_arqpc`, `theorem_14_3_9_arqp`,
`exists_isTPqpGCARqpSCRun`, and, on `X = X₀ = ℝⁿ`, `theorem_14_3_9_arqp_unit`). -/
theorem exists_anchoredCompositeBounds_nu_mu (hp : 1 ≤ p) {X₀ : Set ℝⁿ} {Lc Bc Lf Bf : ℕ → ℝ}
    (hc : AssumptionCD1pLBX c X X₀ p Lc Bc) (hf : AssumptionD1pLBX f X X₀ p Lf Bf) :
    ∃ LA LB BA BB Lμ Bμ : ℕ → ℝ,
      (∀ j, 1 ≤ LA j ∧ 1 ≤ LB j ∧ 1 ≤ BA j ∧ 1 ≤ BB j ∧ 1 ≤ Lμ j ∧ 1 ≤ Bμ j) ∧
      (∀ x₀ : ℝⁿ, AnchoredCompositeBounds (phi2 c) (zeroCon n) X₀ (nuSublevel c X x₀) p
        (nuAnchoredConst LA LB BA BB ‖c x₀‖) (fun _ => 0)) ∧
      ∀ t, AnchoredCompositeBounds (Constrained.targetMerit f c t) (zeroCon n) X₀
        (muSublevel f c X t) p (anchoredConst Lμ Bμ) (fun _ => 0) := by
  obtain ⟨LA, LB, BA, BB, h1, hν⟩ := lemma_14_3_6_i hc
  obtain ⟨Lμ, Bμ, h2, hμ⟩ := lemma_14_3_6_ii hc hf
  refine ⟨LA, LB, BA, BB, Lμ, Bμ, fun j => ⟨(h1 j).1, (h1 j).2.1, (h1 j).2.2.1, (h1 j).2.2.2,
    (h2 j).1, (h2 j).2⟩, fun x₀ => ?_, fun t => ?_⟩
  · refine anchoredCompositeBounds_zeroCon hc.isOpen hc.convex (fun x hx => hc.subset hx.1)
      (hν x₀).1 hp ?_ (hν x₀).2
    have := (h1 p).1
    have := (h1 p).2.1
    have := norm_nonneg (c x₀)
    nlinarith
  · exact anchoredCompositeBounds_zeroCon hc.isOpen hc.convex (fun x hx => hc.subset hx.1)
      (hμ t).1 hp (h2 p).1 (hμ t).2

/-- f.D1pLB.X gives `C^q` near every point of `X` for `q ≤ p`. -/
theorem AssumptionD1pLBX.contDiffAt_of_le {g : ℝⁿ → ℝ} {X X₀ : Set ℝⁿ} {L B : ℕ → ℝ}
    (hg : AssumptionD1pLBX g X X₀ p L B) (hqp : q ≤ p) {y : ℝⁿ} (hy : y ∈ X) :
    ContDiffAt ℝ q g y :=
  (hg.contDiffOn.contDiffAt (hg.isOpen.mem_nhds (hg.subset hy))).of_le (by exact_mod_cast hqp)

/-- c.D1pLB.X gives `C^q` near every point of `X` for `q ≤ p`. -/
theorem AssumptionCD1pLBX.contDiffAt_of_le {X₀ : Set ℝⁿ} {L B : ℕ → ℝ}
    (hc : AssumptionCD1pLBX c X X₀ p L B) (hqp : q ≤ p) {y : ℝⁿ} (hy : y ∈ X) :
    ContDiffAt ℝ q c y :=
  (hc.contDiffOn.contDiffAt (hc.isOpen.mem_nhds (hc.subset hy))).of_le (by exact_mod_cast hqp)

/-- Under f.D1pLB.X, `‖∇^i g(y)‖ ≤ max(1, max_{j ∈ [1 : q]} B_j)` for `y ∈ X₀`, `i ∈ [1 : q]`,
`q ≤ p`. -/
theorem AssumptionD1pLBX.norm_iteratedFDeriv_le_finMax {g : ℝⁿ → ℝ} {X X₀ : Set ℝⁿ}
    {L B : ℕ → ℝ} (hg : AssumptionD1pLBX g X X₀ p L B) (hqp : q ≤ p) {y : ℝⁿ} (hy : y ∈ X₀) :
    ∀ i ∈ Finset.Icc 1 q, ‖iteratedFDeriv ℝ i g y‖ ≤ Optimization.finMax 1 B q := fun i hi =>
  (hg.norm_le i (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hi).1, (Finset.mem_Icc.1 hi).2.trans hqp⟩) y
    hy).trans (Optimization.le_finMax hi)

end TPqp

end ARqpSCAnchored


section ARqpSCRuns

/-! ### One INNER call of Phase 2 realized by ARqp-SC -/

/-- One INNER call of Phase 2 of TPqp-GC realized by ARqp-SC, with its output radii
(`Optimization.IsARqpCallOut`): the iterates `x_{k,0}, …, x_{k,e}` are the first `e + 1` iterates
of an ARqpC-SC run (`algorithm_14_1_1` with `c = 0`, `h = 0`, initial radii `1`; an ARqp-SC run
whose Step 2 is Algorithm 14.1.2) on `F` whose first termination index `k_ε` is at least `e` (the
call may be cut before INNER terminates, by any test of (14.3.32)), the successful iterations are
those of the run, and the returned radii `δo` are those of the run at the last iterate:
* the current radii `δ_e` (Step 1 of Algorithm 14.1.1; at a Step-1 termination these are the
  returned radii);
* or, whenever Step 2 is computed at `e` (at any cut, not only at a Step-2 termination), the step
  radii `δ_{s_e}` (the radii the book returns at a Step-2 termination, Algorithm 14.1.1, Step 2);
* or, at a Step-2 termination (`e = k_ε`), the radii `min(1, ε_j/(4(3 J + σ_e)))`,
  `J = Optimization.arqpJetBound F p x_e`, which certify (14.3.19) at `x_e` because `0` minimizes
  the model there (the step radii `δ_{s_e}` need not). -/
abbrev IsARqpSCCallOut (F : ℝⁿ → ℝ) (X : Set ℝⁿ) (p q : ℕ) (P : ARqpCParams) (ε : ℕ → ℝ)
    (xi : ℕ → ℝⁿ) (e : ℕ) (succ : ℕ → Prop) (δo : ℕ → ℝ) : Prop :=
  Optimization.IsARqpCallOut (EuclideanSpace ℝ (Fin 0)) F X p q P.toARqpParams ε xi e succ δo

/-! ### Phase 2 with ARqp-SC calls: the INNER contract for every run -/

section Phase2

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {p q : ℕ} {P : ARqpCParams} {θ β : ℝ}
  {ε : ℕ → ℝ} {x₁ : ℝⁿ} {D : TPqpSeq n}

/-- **The INNER calls of Phase 2 of TPqp-GC are ARqp-SC runs** ([cartis2022evaluation],
Algorithm 14.3.2, Step 1: `INNER(μ(·, t_k), X, q, x_k, β ‖r(x_k, t_k)‖ ε)` with INNER = ARqp-SC):
for every outer iteration `k ≥ 1` reached, the iterates, successful iterations and output radii
`δ_{k+1}` of the `k`-th call are those of an ARqp-SC run on `μ(·, t_k)` with tolerances
`β ‖r(x_k, t_k)‖ ε_j` (`IsARqpSCCallOut`), cut at any iteration (by any test of (14.3.32));
`Constrained.HighOrderTargetSeq.IsARqpCalls` with `c = 0 : ℝⁿ → ℝ⁰`. -/
abbrev IsARqpSCPhase2Calls (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (X : Set ℝⁿ) (p q : ℕ) (P : ARqpCParams)
    (θ β : ℝ) (ε : ℕ → ℝ) (D : TPqpSeq n) : Prop :=
  D.IsARqpCalls (EuclideanSpace ℝ (Fin 0)) f c X p q P.toARqpParams θ β ε

/-- **Every Phase-2 run of TPqp-GC whose INNER calls are ARqp-SC runs satisfies the INNER contract
keyed on INNER's own test** (`IsInnerPhaseRunStrong`; [cartis2022evaluation], Lemmas 14.2.2–14.2.3,
ARqpC-SC row of (14.2.12), `π_l = l + 1`), with the `t`-independent constants
`κ_decr = Optimization.arqpCallKappaDecr`, `κ_uns = Optimization.arqpKappaUns`,
`κ_unc = Optimization.arqpCallKappaUnc` and radii `ρ_j = κ_ρ βθ ε₀ ε_j`
(`κ_ρ = Optimization.arqpCallKappaRad`), when every `μ(·, t)` has anchored bounds with constants
`L` on `𝓛_μ(t)` (for an open convex `X₀ ⊇ X`; Lemma 14.3.6 (ii) gives them under c.D1pLB.X and
f.D1pLB.X, `exists_anchoredCompositeBounds_nu_mu`) and `θ < ς`
(`Constrained.IsHighOrderTargetRun.isInnerTestContract_of_isARqpCalls`). This holds for every
run, with calls cut by any test of (14.3.32). -/
theorem IsARqpSCPhase2Calls.isInnerPhaseRunStrong (h : IsTPqpGCPhase2 f c X q θ β ε x₁ D)
    (hcalls : IsARqpSCPhase2Calls f c X p q P θ β ε D) {X₀ : Set ℝⁿ} {L : ℕ → ℝ}
    (hμ : ∀ t, AnchoredCompositeBounds (Constrained.targetMerit f c t) (zeroCon n) X₀
      (muSublevel f c X t) p L (fun _ => 0)) (hXX₀ : X ⊆ X₀) (hθς : P.θ < P.ς) :
    IsInnerPhaseRunStrong f c X q θ β ε D (Optimization.arqpCallKappaDecr P.toARqpParams L p q)
      (Optimization.arqpKappaUns P.toARqpParams)
      (Optimization.arqpCallKappaUnc P.toARqpParams L p) (fun l => (l : ℝ) + 1)
      (fun j => Optimization.arqpCallKappaRad P.toARqpParams L p * β * θ * ε 0 * ε j) :=
  h.isInnerTestContract_of_isARqpCalls hcalls (fun t => (hμ t).lipschitzDerivsAnchored_f)
    (hμ 0).one_le (fun t => (hμ t).jet_f) hXX₀ hθς

/-- **Every Phase-2 run of TPqp-GC whose INNER calls are ARqp-SC runs satisfies the INNER contract
keyed on INNER's own test with the exponents of the ARqp-SC row of (14.2.12)**
([cartis2022evaluation], Lemmas 14.2.2–14.2.3, ARqp-SC row): as
`IsARqpSCPhase2Calls.isInnerPhaseRunStrong`, with `κ_decr = arqpRowKappaDecr u P L p q` and
`π_l = Optimization.arqpPiOf u p l` in a radii mode `u` (the lower-bound mode `u = False`, exponents
`j(p+1)/p`, for every `q` and `X`; the unit-radii mode when `u` forces `q = 1` and `X` convex). -/
theorem IsARqpSCPhase2Calls.isInnerPhaseRunStrong_arqp (h : IsTPqpGCPhase2 f c X q θ β ε x₁ D)
    (hcalls : IsARqpSCPhase2Calls f c X p q P θ β ε D) {X₀ : Set ℝⁿ} {L : ℕ → ℝ}
    (hμ : ∀ t, AnchoredCompositeBounds (Constrained.targetMerit f c t) (zeroCon n) X₀
      (muSublevel f c X t) p L (fun _ => 0)) (hXX₀ : X ⊆ X₀) (hθς : P.θ < P.ς)
    {u : Prop} [Decidable u] (hu : u → q = 1 ∧ Convex ℝ X) :
    IsInnerPhaseRunStrong f c X q θ β ε D (arqpRowKappaDecr u P L p q)
      (Optimization.arqpKappaUns P.toARqpParams)
      (Optimization.arqpCallKappaUnc P.toARqpParams L p) (Optimization.arqpPiOf u p)
      (fun j => Optimization.arqpCallKappaRad P.toARqpParams L p * β * θ * ε 0 * ε j) :=
  h.isInnerTestContract_of_isARqpCalls_arqpPiOf hcalls (fun t => (hμ t).lipschitzDerivsAnchored_f)
    (hμ 0).one_le (fun t => (hμ t).jet_f) hXX₀ hθς hu

end Phase2

/-! ### The orders of Theorem 14.3.9 -/

section Order

/-- **The order of the number of evaluations of `(f, c)` in Theorem 14.3.9** of
[cartis2022evaluation]: `max[ε₀^{-1}, max_{j ∈ [1 : q]} ε₀^{1-π_j} ε_j^{-π_j}]`. -/
noncomputable def tpqpOrderF (π : ℕ → ℝ) (q : ℕ) (ε : ℕ → ℝ) : ℝ :=
  Optimization.finMax (ε 0)⁻¹ (fun j => ε 0 ^ (1 - π j) * ε j ^ (-π j)) q

/-- **The order of the number of derivative evaluations in Theorem 14.3.9** of
[cartis2022evaluation]: `max_{j ∈ [1 : q]} ε₀^{1-π_j} ε_j^{-π_j}` (`0` for `q = 0`). -/
noncomputable def tpqpOrderD (π : ℕ → ℝ) (q : ℕ) (ε : ℕ → ℝ) : ℝ :=
  Optimization.finMax 0 (fun j => ε 0 ^ (1 - π j) * ε j ^ (-π j)) q

variable {π : ℕ → ℝ} {q : ℕ} {ε : ℕ → ℝ}

/-- `ε₀^{-1} ≤ max[ε₀^{-1}, …]`. -/
theorem inv_le_tpqpOrderF : (ε 0)⁻¹ ≤ tpqpOrderF π q ε := Optimization.le_finMax_left

/-- Each term `ε₀^{1-π_j} ε_j^{-π_j}` is at most the function-evaluation order. -/
theorem term_le_tpqpOrderF {j : ℕ} (hj : j ∈ Finset.Icc 1 q) :
    ε 0 ^ (1 - π j) * ε j ^ (-π j) ≤ tpqpOrderF π q ε :=
  Optimization.le_finMax (u := fun j => ε 0 ^ (1 - π j) * ε j ^ (-π j)) hj

/-- Each term `ε₀^{1-π_j} ε_j^{-π_j}` is at most the derivative-evaluation order. -/
theorem term_le_tpqpOrderD {j : ℕ} (hj : j ∈ Finset.Icc 1 q) :
    ε 0 ^ (1 - π j) * ε j ^ (-π j) ≤ tpqpOrderD π q ε :=
  Optimization.le_finMax (u := fun j => ε 0 ^ (1 - π j) * ε j ^ (-π j)) hj

/-- `1 ≤ ε₀^{-1} ≤ max[ε₀^{-1}, …]` for `ε₀ ∈ (0, 1]`. -/
theorem one_le_tpqpOrderF (h0 : 0 < ε 0) (h1 : ε 0 ≤ 1) : 1 ≤ tpqpOrderF π q ε :=
  ((one_le_inv₀ h0).2 h1).trans inv_le_tpqpOrderF

/-- **The two orders agree when some `π_j ≥ 2`**: then `ε₀^{-1} ≤ ε₀^{1-π_j} ε_j^{-π_j}` for
tolerances in `(0, 1]`, so the term `ε₀^{-1}` of the function-evaluation order is absorbed (this
holds for the ARqpC-SC exponents `j + 1`, and for the ARqp-SC exponents when `q = p`). -/
theorem tpqpOrderF_le_tpqpOrderD (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1)
    {j : ℕ} (hj : j ∈ Finset.Icc 1 q) (hπj : 2 ≤ π j) : tpqpOrderF π q ε ≤ tpqpOrderD π q ε := by
  have hε₀ := hε 0 (by simp)
  have hεj := hε j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
  refine Optimization.finMax_le ?_ fun l hl => term_le_tpqpOrderD hl
  refine le_trans ?_ (term_le_tpqpOrderD hj)
  have h1 : (ε 0)⁻¹ ≤ ε 0 ^ (1 - π j) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_ge hε₀.1 hε₀.2 (by linarith)
  have h2 : 1 ≤ ε j ^ (-π j) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hεj.1 hεj.2 (by linarith)
  have h3 : 0 ≤ ε 0 ^ (1 - π j) := Real.rpow_nonneg hε₀.1.le _
  nlinarith


end Order

/-! ### TPqp-GC runs with INNER = ARqp-SC in both phases -/

section Run

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {p q : ℕ} {P : ARqpCParams} {θ β₁ β : ℝ}
  {ε : ℕ → ℝ} {x₀ : ℝⁿ} {xP : ℕ → ℝⁿ} {δP : ℕ → ℕ → ℝ} {k₁ : ℕ} {D : TPqpSeq n}
  {nF₁ nD₁ : ℕ → ℕ}

/-- **A run of TPqp-GC with INNER = ARqp-SC in both phases** ([cartis2022evaluation],
Algorithm 14.3.2 with INNER of regularization type, ARqp-SC run as ARqpC-SC with `c = 0`,
`h = 0`): a run (`algorithm_14_3_2`) whose Phase-1 INNER calls (14.3.23)
`x_k = INNER(ν, X, q, x_{k-1}, β₁ ‖c(x_{k-1})‖ (θε₀, ε_1, …, ε_q))` are ARqp-SC runs on `ν` that
use `nF₁ k` evaluations of `c` and `nD₁ k` of its derivatives (`IsARqpSCOutputCost`), and whose
Phase-2 INNER calls (if Phase 2 is entered) are ARqp-SC runs on `μ(·, t_k)` with their output
radii, cut at any iteration (`IsARqpSCPhase2Calls`). -/
structure IsTPqpGCARqpSCRun (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (X : Set ℝⁿ) (p q : ℕ)
    (P : ARqpCParams) (θ β₁ β : ℝ) (ε : ℕ → ℝ) (x₀ : ℝⁿ) (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ)
    (k₁ : ℕ) (D : TPqpSeq n) (nF₁ nD₁ : ℕ → ℕ) : Prop where
  /-- The TPqp-GC run. -/
  run : algorithm_14_3_2 f c X q θ β₁ β ε x₀ xP δP k₁ D
  /-- The Phase-1 INNER calls are ARqp-SC runs with their evaluation counts. -/
  phase1 : ∀ k, 1 ≤ k → k ≤ k₁ → IsARqpSCOutputCost (phi2 c) X p q P
    (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j) (xP (k - 1)) (xP k) (δP k) (nF₁ k)
      (nD₁ k)
  /-- The Phase-2 INNER calls are ARqp-SC runs with their output radii. -/
  phase2 : ‖c (xP k₁)‖ ≤ θ * ε 0 → IsARqpSCPhase2Calls f c X p q P θ β ε D


end Run

/-! ### Theorem 14.3.9 with INNER = ARqpC-SC (exponents `j + 1`) -/

section Theorem1439

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {p q : ℕ}

/-- **Theorem 14.3.9** of [cartis2022evaluation] (complexity of TPqp-GC) **with the exponents
`π_j = j + 1`, for every run with INNER = ARqpC-SC with `c = 0`, `h = 0`** (ARqp-SC with Step 2
by Algorithm 14.1.2), under the book's assumptions c.D1pLB.X and f.D1pLB.X (on an open convex
`X₀ ⊇ X`) and f.B.Fb on `ℱ_{β_F}`, with `1 ≤ q ≤ p`. This is the printed order of the ARqpC-SC
row of (14.2.12) exactly where that row's entry is `j + 1`: `q ≥ 2`, or `q = 1` with `X`
nonconvex; for `q = 1` with `X` convex the entry is `(p+1)/p` (`h = 0` is convex), which is
proved for `p = 1` (`theorem_14_3_9_arqp`) and false for `p ≥ 4` for runs that re-initialise `μ`
at Step 2.1 of Algorithm 14.1.2 (`theorem_14_3_9_arqp_counterexample`; open when `μ` is bounded
below). For ARqpC constants with `θ < ς`, `θ ∈ (0, 1)`,
`β > 0` (the runs have `β ≤ θ`, the book's `β = θ` included), `β₁` and a starting point `x₀`,
there are constants `κ_F`, `κ_D` such that for all
tolerances `ε ∈ (0, 1]^{q+1}` with `ε₀ ≤ β_F` and every TPqp-GC run whose INNER calls are ARqp-SC
runs (ARqpC-SC with `c = 0`, `h = 0`, `IsTPqpGCARqpSCRun`; Phase-2 calls may be cut by any test of
(14.3.32); such runs exist, `exists_isTPqpGCARqpSCRun`):
* if Phase 1 ends with `‖c(x₁)‖ > θε₀`, it uses at most `κ_F O_F` evaluations of `c` and
  `κ_D O_D` derivative evaluations;
* otherwise Phase 2 terminates at some `k_ε`, and both phases together use at most `κ_F O_F`
  evaluations of `(f, c)` and `κ_D O_D` derivative evaluations,

where `π_j = j + 1` (the ARqpC-SC row of (14.2.12)), `O_F = max[ε₀^{-1}, max_j ε₀^{1-π_j}
ε_j^{-π_j}]` (`tpqpOrderF`) and `O_D = max_j ε₀^{1-π_j} ε_j^{-π_j}` (`tpqpOrderD`), i.e. the
printed orders `O(max[ε₀^{-1}, max_j ε₀^{-j} ε_j^{-(j+1)}])` and `O(max_j ε₀^{-j} ε_j^{-(j+1)})`.
The constants depend only on the data (through Lemma 14.3.6), on `P`, `θ`, `β`, `β₁`, `f_up - f_low`
and `‖c(x₀)‖`. The proof: every such run satisfies the INNER contract keyed on INNER's own test
with `t`-independent constants (`IsARqpSCPhase2Calls.isInnerPhaseRunStrong`) and the Phase-1 cost
contract (`phase1_cost_le_anchored`); the bad-iteration term `(ε₀ ε_j)^{-j}` of
`Constrained.IsHighOrderTargetRun.complexity_of_innerTest` is at most `ε₀^{-j} ε_j^{-(j+1)}`
(`Constrained.inv_mul_pow_le_rpow_succ`),
and since `π_1 = 2` the term `ε₀^{-1}` is absorbed in `O_D` (`tpqpOrderF_le_tpqpOrderD`). -/
theorem theorem_14_3_9_arqpc (hq : 1 ≤ q) (hqp : q ≤ p) {X₀ : Set ℝⁿ} {Lc Bc Lf Bf : ℕ → ℝ}
    (hc : AssumptionCD1pLBX c X X₀ p Lc Bc) (hf : AssumptionD1pLBX f X X₀ p Lf Bf)
    {βF flow fup : ℝ} (hB : Chapter07.AssumptionBFb f c X βF flow fup)
    (P : ARqpCParams) (hθς : P.θ < P.ς) {θ β β₁ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hβ0 : 0 < β) (x₀ : ℝⁿ) :
    ∃ κF κD : ℝ, ∀ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) → ε 0 ≤ βF →
      ∀ (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq n) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCARqpSCRun f c X p q P θ β₁ β ε x₀ xP δP k₁ D nF₁ nD₁ →
        (θ * ε 0 < ‖c (xP k₁)‖ →
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤ κF * tpqpOrderF (fun j => (j : ℝ) + 1) q ε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤ κD * tpqpOrderD (fun j => (j : ℝ) + 1) q ε) ∧
        (‖c (xP k₁)‖ ≤ θ * ε 0 → ∃ kε, D.IsEnd f c X q θ ε kε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) + D.funEvals kε ≤
            κF * tpqpOrderF (fun j => (j : ℝ) + 1) q ε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) + D.derivEvals kε ≤
            κD * tpqpOrderD (fun j => (j : ℝ) + 1) q ε) := by
  obtain ⟨LA, LB, BA, BB, Lμ, Bμ, h1, hνA, hμA⟩ :=
    exists_anchoredCompositeBounds_nu_mu (hq.trans hqp) hc hf
  set Lν := nuAnchoredConst LA LB BA BB ‖c x₀‖ with hLν
  set L := anchoredConst Lμ Bμ with hL
  have hLp : 1 ≤ L p := (hμA 0).one_le
  have hκ : 0 < Optimization.arqpCallKappaDecr P.toARqpParams L p q :=
    Optimization.arqpCallKappaDecr_pos P.σmin_pos hθς hLp
  have hκρ : 0 < Optimization.arqpCallKappaRad P.toARqpParams L p * β * θ := by
    have := (Optimization.arqpCallKappaRad_pos (P := P.toARqpParams) (L := L) (p := p))
    positivity
  obtain ⟨CF, CD, hCF, hCD, hord⟩ :=
    Constrained.IsHighOrderTargetRun.exists_const_order_of_innerTest (f := f) (c := c)
    (X := X) (θ := θ) (β := β) hq (πmax := (q : ℝ) + 1) hκ
    (Optimization.arqpKappaUns_nonneg (P := P.toARqpParams))
    (Optimization.arqpCallKappaUnc_nonneg P.toARqpParams L p) hκρ
    (Optimization.finMax_one_pos (L := Bf))
    (abs_nonneg (fup - flow + 1))
    zero_le_one hθ0 hθ1 hβ0
  -- the Phase-1 constants
  have hνκ : 0 < Optimization.arqpCallKappaDecr P.toARqpParams Lν p q :=
    Optimization.arqpCallKappaDecr_pos P.σmin_pos hθς (hνA x₀).one_le
  have hκF : 0 ≤ arqpSCKappaF P Lν p q := by
    unfold arqpSCKappaF
    have := (Optimization.arqpKappaUns_nonneg (P := P.toARqpParams))
    have := Optimization.kappaCARqp_nonneg P.toARqpParams Lν p
    positivity
  have hκD : 0 ≤ arqpSCKappaD P Lν p q := by
    unfold arqpSCKappaD
    positivity
  set W := ∑ j ∈ Finset.Icc 1 q, |β₁ ^ (1 - 2 * ((j : ℝ) + 1)) / (β₁ ^ (1 - ((j : ℝ) + 1)) - 1) *
    θ ^ (1 - ((j : ℝ) + 1))| with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hP1F : 0 ≤ 1 / 2 * arqpSCKappaF P Lν p q * ‖c x₀‖ * W := by positivity
  have hP1D : 0 ≤ 1 / 2 * arqpSCKappaD P Lν p q * ‖c x₀‖ * W := by positivity
  refine ⟨1 / 2 * arqpSCKappaF P Lν p q * ‖c x₀‖ * W + CF,
    1 / 2 * arqpSCKappaD P Lν p q * ‖c x₀‖ * W + CD,
    fun ε hε hεβ xP δP k₁ D nF₁ nD₁ hR => ?_⟩
  have h := hR.run
  set π : ℕ → ℝ := fun j => (j : ℝ) + 1 with hπ_def
  have hεI : ∀ l ∈ Finset.Icc 1 q, 0 < ε l ∧ ε l ≤ 1 := fun l hl =>
    hε l (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hl).2))
  have hε₀ := hε 0 (by simp)
  have hOT : ∀ j ∈ Finset.Icc 1 q, ε 0 ^ (1 - π j) * ε j ^ (-π j) ≤ tpqpOrderF π q ε :=
    fun j hj => term_le_tpqpOrderF hj
  have hO1 : 1 ≤ tpqpOrderF π q ε := one_le_tpqpOrderF hε₀.1 hε₀.2
  have h1q : 1 ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, hq⟩
  have hFD : tpqpOrderF π q ε ≤ tpqpOrderD π q ε :=
    tpqpOrderF_le_tpqpOrderD hε h1q (by simp only [hπ_def]; norm_num)
  -- Phase 1
  have hπ1 : ∀ l ∈ Finset.Icc 1 q, 1 < π l := fun l hl => by
    have : (1 : ℝ) ≤ l := by exact_mod_cast (Finset.mem_Icc.1 hl).1
    simp only [hπ_def]
    linarith
  have hcost := phase1_cost_le_anchored h hq (hνA x₀) hc.subset hθς hε hR.phase1
  have hF1 := (lemma_14_3_7 h hθ0 hπ1 hκF fun k hk => (hcost k hk).1).2
  have hD1 := (lemma_14_3_7 h hθ0 hπ1 hκD fun k hk => (hcost k hk).2).2
  have hF1' := hF1.trans (Constrained.mul_sum_le_mul_sum_abs_mul hκF (norm_nonneg _)
    (fun j hj => (hε j hj).1) hOT)
  have hD1' := hD1.trans (Constrained.mul_sum_le_mul_sum_abs_mul hκD (norm_nonneg _)
    (fun j hj => (hε j hj).1) hOT)
  rw [← hW] at hF1' hD1'
  have hOnn : 0 ≤ tpqpOrderF π q ε := zero_le_one.trans hO1
  refine ⟨fun _ => ⟨?_, ?_⟩, fun hc1 => ?_⟩
  · calc _ ≤ 1 / 2 * arqpSCKappaF P Lν p q * ‖c x₀‖ * W * tpqpOrderF π q ε := hF1'
      _ ≤ _ := by nlinarith
  · calc _ ≤ 1 / 2 * arqpSCKappaD P Lν p q * ‖c x₀‖ * W * tpqpOrderF π q ε := hD1'
      _ ≤ 1 / 2 * arqpSCKappaD P Lν p q * ‖c x₀‖ * W * tpqpOrderD π q ε :=
          mul_le_mul_of_nonneg_left hFD hP1D
      _ ≤ _ := by nlinarith
  -- Phase 2
  have h2 := h.phase2 hc1
  have hin := ((hR.phase2 hc1).isInnerPhaseRunStrong h2 hμA hc.subset hθς).mono_radius
    (ρ' := fun j => Optimization.arqpCallKappaRad P.toARqpParams L p * β * θ * (ε 0 * ε j))
    fun j _ => le_of_eq (by ring)
  obtain ⟨kε, hend, hF2, hD2⟩ := hord h2 hin (fun j hj => mul_pos hε₀.1 (hεI j hj).1)
    (fun l hl => by
      have : (l : ℝ) ≤ q := by exact_mod_cast (Finset.mem_Icc.1 hl).2
      exact ⟨by positivity, by linarith⟩) (hB.of_le hεβ) (le_abs_self _)
    (fun _ hy => hf.contDiffAt_of_le hqp hy) (fun _ hy => hc.contDiffAt_of_le hqp hy)
    (fun _ hy _ => hf.norm_iteratedFDeriv_le_finMax hqp (hf.subset hy)) inv_le_tpqpOrderF hOT
    (fun j hj => by
      rw [one_mul, mul_pow_sub_one (by have := (Finset.mem_Icc.1 hj).1; omega) _]
      exact (Constrained.inv_mul_pow_le_rpow_succ hε₀.1 (hεI j hj).1 (hεI j hj).2 j).trans
        (hOT j hj))
  refine ⟨kε, hend, ?_, ?_⟩
  · calc _ ≤ 1 / 2 * arqpSCKappaF P Lν p q * ‖c x₀‖ * W * tpqpOrderF π q ε +
          CF * tpqpOrderF π q ε := add_le_add hF1' hF2
      _ = _ := by ring
  · calc _ ≤ 1 / 2 * arqpSCKappaD P Lν p q * ‖c x₀‖ * W * tpqpOrderF π q ε +
          CD * tpqpOrderF π q ε := add_le_add hD1' hD2
      _ ≤ 1 / 2 * arqpSCKappaD P Lν p q * ‖c x₀‖ * W * tpqpOrderD π q ε +
          CD * tpqpOrderD π q ε := by gcongr
      _ = _ := by ring

/-- **Runs of ARqp-SC satisfy the hypotheses of `theorem_14_3_9`**: for every TPqp-GC run whose
INNER calls are ARqp-SC runs (`IsTPqpGCARqpSCRun`), under c.D1pLB.X, f.D1pLB.X and f.B.Fb with
`θ < ς` and `ε₀ ≤ β_F`, the Phase-1 cost contract (with the ARqpC-SC exponents `j + 1`,
`phase1_cost_le_anchored`), the Phase-2 contract keyed on INNER's test
(`IsARqpSCPhase2Calls.isInnerPhaseRunStrong`), the smoothness and derivative bounds and a margin
`τ > 0` all hold, and `theorem_14_3_9` applies: if Phase 2 is entered, it terminates. -/
theorem theorem_14_3_9_arqpc_terminates (hq : 1 ≤ q) (hqp : q ≤ p) {X₀ : Set ℝⁿ}
    {Lc Bc Lf Bf : ℕ → ℝ} (hc : AssumptionCD1pLBX c X X₀ p Lc Bc)
    (hf : AssumptionD1pLBX f X X₀ p Lf Bf) {βF flow fup : ℝ}
    (hB : Chapter07.AssumptionBFb f c X βF flow fup) (P : ARqpCParams) (hθς : P.θ < P.ς)
    {θ β β₁ : ℝ} {ε : ℕ → ℝ} (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1)
    (hεβ : ε 0 ≤ βF) {x₀ : ℝⁿ} {xP : ℕ → ℝⁿ} {δP : ℕ → ℕ → ℝ} {k₁ : ℕ} {D : TPqpSeq n}
    {nF₁ nD₁ : ℕ → ℕ} (hR : IsTPqpGCARqpSCRun f c X p q P θ β₁ β ε x₀ xP δP k₁ D nF₁ nD₁)
    (hc1 : ‖c (xP k₁)‖ ≤ θ * ε 0) :
    ∃ kε, D.IsEnd f c X q θ ε kε := by
  obtain ⟨LA, LB, BA, BB, Lμ, Bμ, -, hνA, hμA⟩ :=
    exists_anchoredCompositeBounds_nu_mu (hq.trans hqp) hc hf
  have h := hR.run
  have h2 := h.phase2 hc1
  set L := anchoredConst Lμ Bμ
  set Lν := nuAnchoredConst LA LB BA BB ‖c x₀‖
  have hθ0 := h2.θ_pos
  have hε₀ := hε 0 (by simp)
  have hε0 : 0 < ε 0 := hε₀.1
  have hβ0 := h2.β_pos
  have hνκ : 0 < Optimization.arqpCallKappaDecr P.toARqpParams Lν p q :=
    Optimization.arqpCallKappaDecr_pos P.σmin_pos hθς (hνA x₀).one_le
  have hεI : ∀ l ∈ Finset.Icc 1 q, 0 < ε l ∧ ε l ≤ 1 := fun l hl =>
    hε l (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hl).2))
  have hκ : 0 < Optimization.arqpCallKappaDecr P.toARqpParams L p q :=
    Optimization.arqpCallKappaDecr_pos P.σmin_pos hθς (hμA 0).one_le
  have hκF : 0 ≤ arqpSCKappaF P Lν p q := by
    unfold arqpSCKappaF
    have := (Optimization.arqpKappaUns_nonneg (P := P.toARqpParams))
    have := Optimization.kappaCARqp_nonneg P.toARqpParams Lν p
    positivity
  have hκD : 0 ≤ arqpSCKappaD P Lν p q := by
    unfold arqpSCKappaD
    positivity
  have hπ1 : ∀ l ∈ Finset.Icc 1 q, 1 < (fun j : ℕ => (j : ℝ) + 1) l := fun l hl => by
    have : (1 : ℝ) ≤ l := by exact_mod_cast (Finset.mem_Icc.1 hl).1
    simp only
    linarith
  have hcost := phase1_cost_le_anchored h hq (hνA x₀) hc.subset hθς hε hR.phase1
  set ρ : ℕ → ℝ := fun j => Optimization.arqpCallKappaRad P.toARqpParams L p * β * θ * ε 0 * ε j
  have hρ : ∀ j ∈ Finset.Icc 1 q, 0 ≤ ρ j := fun j hj => by
    have := (Optimization.arqpCallKappaRad_pos (P := P.toARqpParams) (L := L) (p := p))
    have := h2.β_pos
    have := (hεI j hj).1
    positivity
  set M : ℝ := ∑ l ∈ Finset.Icc 1 q, ε 0 ^ (2 - ((l : ℝ) + 1)) * ε l ^ (-((l : ℝ) + 1)) + 1
  have hterm : ∀ l ∈ Finset.Icc 1 q, 0 ≤ ε 0 ^ (2 - ((l : ℝ) + 1)) * ε l ^ (-((l : ℝ) + 1)) :=
    fun l hl => by have := (hεI l hl).1; positivity
  have hM0 : 0 < M := by
    have := Finset.sum_nonneg hterm
    linarith
  have hM : ∀ l ∈ Finset.Icc 1 q, ε 0 ^ (2 - ((l : ℝ) + 1)) * ε l ^ (-((l : ℝ) + 1)) ≤ M :=
    fun l hl => (Finset.single_le_sum hterm hl).trans (le_add_of_nonneg_right zero_le_one)
  set g : ℕ → ℝ := fun j => Constrained.kbMargin θ (ε 0) * ε j * ρ j ^ (j - 1) / (j ! : ℝ)
  have hg : ∀ j ∈ Finset.Icc 1 q, 0 < g j := fun j hj => by
    have := (Optimization.arqpCallKappaRad_pos (P := P.toARqpParams) (L := L) (p := p))
    have := h2.β_pos
    have := (hεI j hj).1
    have hη : 0 < Constrained.kbMargin θ (ε 0) := by
      rw [Constrained.kbMargin_def]
      have := h2.θ_lt_one
      have : 0 < 1 - θ := by linarith
      positivity
    positivity
  set Bq := Optimization.finMax 1 Bf q
  have hBq : 0 < Bq := Optimization.finMax_one_pos
  have hτ0 : 0 < Optimization.finMin 1 g q / (2 * Bq) :=
    div_pos (Optimization.finMin_pos one_pos hg) (by positivity)
  obtain ⟨-, kε, hend, -⟩ := (theorem_14_3_9 h hθ0 hπ1 hκF hκD (aF := 0) (aD := 0)
    (nF₁ := fun k => (nF₁ k : ℝ)) (nD₁ := fun k => (nD₁ k : ℝ))
    (fun k hk => by rw [add_zero]; exact (hcost k hk).1)
    (fun k hk => by rw [add_zero]; exact (hcost k hk).2)
    ((hR.phase2 hc1).isInnerPhaseRunStrong h2 hμA hc.subset hθς) hκ
    (Optimization.arqpKappaUns_nonneg (P := P.toARqpParams))
    (fun l hl => by
      have : (l : ℝ) ≤ q := by exact_mod_cast (Finset.mem_Icc.1 hl).2
      exact ⟨by positivity, (by linarith : (l : ℝ) + 1 ≤ (q : ℝ) + 1)⟩) hM0 hM hB hεβ hρ
    (fun _ hy => hf.contDiffAt_of_le hqp hy)
    (fun _ hy => hc.contDiffAt_of_le hqp hy)
    (fun _ hy _ => hf.norm_iteratedFDeriv_le_finMax hqp (hf.subset hy)) hτ0
    (fun j hj => by
      rw [mul_div_cancel₀ _ (by positivity : (2 * Bq) ≠ 0)]
      exact Optimization.finMin_le hj)).2.2 hc1
  exact ⟨kε, hend⟩

end Theorem1439

/-! ### Theorem 14.3.9 with INNER = ARqp-SC (exponents `j(p+1)/p`) -/

section Theorem1439ARqp


variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {p q : ℕ}

/-- **The Phase-1 cost of TPqp-GC with INNER = ARqp-SC within an order bound** (the Phase-1 part
of `exists_const_order_arqp`, [cartis2022evaluation], Lemma 14.3.7): under c.D1pLB.X and f.D1pLB.X
there are constants `κ_F, κ_D ≥ 0` such that for all tolerances and every run of
`IsTPqpGCARqpSCRun`, and every `O` with `ε₀^{-1} ≤ O` and `ε₀^{1-π_l} ε_l^{-π_l} ≤ O`
(`π_l = l(p+1)/p`), Phase 1 uses at most `κ_F O` evaluations of `c` and `κ_D O` derivative
evaluations (additive cost contract, `lemma_14_3_7_add`, with `k₁ = O(ε₀^{-1})`,
`Real.natCeil_log_div_log_le`). -/
theorem exists_const_phase1_arqp (hq : 1 ≤ q) (hqp : q ≤ p) {X₀ : Set ℝⁿ}
    {Lc Bc Lf Bf : ℕ → ℝ} (hc : AssumptionCD1pLBX c X X₀ p Lc Bc)
    (hf : AssumptionD1pLBX f X X₀ p Lf Bf) (P : ARqpCParams) (hθς : P.θ < P.ς)
    {θ β β₁ : ℝ} (hθ0 : 0 < θ) (x₀ : ℝⁿ) :
    ∃ κF κD : ℝ, 0 ≤ κF ∧ 0 ≤ κD ∧
      ∀ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) →
      ∀ (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq n) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCARqpSCRun f c X p q P θ β₁ β ε x₀ xP δP k₁ D nF₁ nD₁ → ∀ O : ℝ,
        (ε 0)⁻¹ ≤ O →
        (∀ l ∈ Finset.Icc 1 q, ε 0 ^ (1 - Optimization.arqpPiOf False p l) *
          ε l ^ (-Optimization.arqpPiOf False p l) ≤ O) →
        ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤ κF * O ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤ κD * O := by
  have hp : 1 ≤ p := hq.trans hqp
  obtain ⟨LA, LB, BA, BB, Lμ, Bμ, h1, hνA, hμA⟩ := exists_anchoredCompositeBounds_nu_mu hp hc hf
  set Lν := nuAnchoredConst LA LB BA BB ‖c x₀‖ with hLν
  -- the Phase-1 constants
  have hνκ : 0 < arqpRowKappaDecr False P Lν p q :=
    mul_pos P.η₁_pos (Optimization.arqpKappaDmOf_pos False P.σmin_pos hθς (hνA x₀).one_le)
  set κF₁ := Optimization.arqpKappaUns P.toARqpParams / arqpRowKappaDecr False P Lν p q with hκF₁
  set κD₁ := 1 / arqpRowKappaDecr False P Lν p q with hκD₁
  have hκF : 0 ≤ κF₁ := div_nonneg (Optimization.arqpKappaUns_nonneg (P := P.toARqpParams)) hνκ.le
  have hκD : 0 ≤ κD₁ := div_nonneg zero_le_one hνκ.le
  have hκC := Optimization.kappaCARqp_nonneg P.toARqpParams Lν p
  set W := ∑ j ∈ Finset.Icc 1 q, |β₁ ^ (1 - 2 * Optimization.arqpPiOf False p j) /
    (β₁ ^ (1 - Optimization.arqpPiOf False p j) - 1) * θ ^ (1 - Optimization.arqpPiOf False p j)|
        with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set c₁ := 1 + ‖c x₀‖ / (θ * |Real.log β₁|) with hc₁
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; positivity
  refine ⟨1 / 2 * κF₁ * ‖c x₀‖ * W + Optimization.kappaCARqp P.toARqpParams Lν p * c₁,
    1 / 2 * κD₁ * ‖c x₀‖ * W + 2 * c₁, by positivity, by positivity,
    fun ε hε xP δP k₁ D nF₁ nD₁ hR O hO0 hOT => ?_⟩
  have h := hR.run
  have hε₀ := hε 0 (by simp)
  have hO1 : 1 ≤ O := ((one_le_inv₀ hε₀.1).2 hε₀.2).trans hO0
  have hOnn : 0 ≤ O := zero_le_one.trans hO1
  have hβ₁0 := h.phase1.β_pos
  have hβ₁1 := h.phase1.β_lt_one
  -- Phase 1: the number of iterations and the additive cost contract
  have hk₁ : (k₁ : ℝ) ≤ c₁ * O := by
    obtain ⟨⟨kmax, hhit, hkmax, -⟩, -⟩ := theorem_14_3_3 h.phase1
    rw [hhit.unique h.phase1_end, phase1Tol_zero, h.start] at hkmax
    have h1 : (k₁ : ℝ) ≤ 1 + ‖c x₀‖ / (θ * ε 0 * |Real.log β₁|) :=
      (Nat.cast_le.2 hkmax).trans (Real.natCeil_log_div_log_le (mul_pos hθ0 hε₀.1)
        (norm_nonneg _) hβ₁0 hβ₁1)
    have h2 : ‖c x₀‖ / (θ * ε 0 * |Real.log β₁|) = ‖c x₀‖ / (θ * |Real.log β₁|) * (ε 0)⁻¹ := by
      field_simp
    have h3 : 0 ≤ ‖c x₀‖ / (θ * |Real.log β₁|) := by positivity
    calc (k₁ : ℝ) ≤ 1 + ‖c x₀‖ / (θ * |Real.log β₁|) * (ε 0)⁻¹ := h2 ▸ h1
      _ ≤ O + ‖c x₀‖ / (θ * |Real.log β₁|) * O := by gcongr
      _ = c₁ * O := by rw [hc₁]; ring
  have hcost : ∀ k ∈ Finset.Icc 1 k₁,
      (nF₁ k : ℝ) ≤ innerEvalBound κF₁ (Optimization.arqpPiOf False p) q (phi2 c (xP (k - 1)))
        (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j) +
          Optimization.kappaCARqp P.toARqpParams Lν p ∧
      (nD₁ k : ℝ) ≤ innerEvalBound κD₁ (Optimization.arqpPiOf False p) q (phi2 c (xP (k - 1)))
        (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j) + 2 := by
    intro k hk
    obtain ⟨hk1, hkk⟩ := Finset.mem_Icc.1 hk
    have hmem : xP (k - 1) ∈ X := by
      rcases Nat.eq_zero_or_pos (k - 1) with h0 | hpos
      · rw [h0]; exact h.phase1.mem_zero
      · exact h.phase1.mem (k - 1) hpos fun i hi => h.phase1_end.2 i (by omega)
    have hck : ‖c (xP (k - 1))‖ ≤ ‖c x₀‖ := by
      have := h.phase1.norm_le_pow_mul (Nat.zero_le (k - 1)) fun l hl =>
        h.phase1_end.2 l (by omega)
      rw [h.start] at this
      exact this.trans (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hβ₁0.le hβ₁1.le))
    exact (hR.phase1 k hk1 hkk).cost_le_arqp_add_anchored (hνA x₀) hc.subset
      (fun y _ => by rw [phi2_apply]; positivity) hθς (u := False) (fun h => h.elim) hmem
      (fun y hy hyk => ⟨hy, (Constrained.halfSqNorm_le_halfSqNorm_iff.1 hyk).trans hck⟩)
  have hπ1 : ∀ l ∈ Finset.Icc 1 q, 1 < Optimization.arqpPiOf False p l := fun l hl =>
    (Optimization.arqpPiOf_false_mem hp hl).1
  have hF1 := (lemma_14_3_7_add h hθ0 hπ1 hκF fun k hk => (hcost k hk).1).trans
    (add_le_add (Constrained.mul_sum_le_mul_sum_abs_mul hκF (norm_nonneg _)
      (fun j hj => (hε j hj).1) hOT) le_rfl)
  have hD1 := (lemma_14_3_7_add h hθ0 hπ1 hκD fun k hk => (hcost k hk).2).trans
    (add_le_add (Constrained.mul_sum_le_mul_sum_abs_mul hκD (norm_nonneg _)
      (fun j hj => (hε j hj).1) hOT) le_rfl)
  rw [← hW] at hF1 hD1
  have hF1' : ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤
      (1 / 2 * κF₁ * ‖c x₀‖ * W + Optimization.kappaCARqp P.toARqpParams Lν p * c₁) * O := by
    calc _ ≤ 1 / 2 * κF₁ * ‖c x₀‖ * W * O + k₁ * Optimization.kappaCARqp P.toARqpParams Lν p := hF1
      _ ≤ 1 / 2 * κF₁ * ‖c x₀‖ * W * O + c₁ * O * Optimization.kappaCARqp P.toARqpParams Lν p := by
          gcongr
      _ = _ := by ring
  have hD1' : ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤ (1 / 2 * κD₁ * ‖c x₀‖ * W + 2 * c₁) * O := by
    calc _ ≤ 1 / 2 * κD₁ * ‖c x₀‖ * W * O + k₁ * 2 := hD1
      _ ≤ 1 / 2 * κD₁ * ‖c x₀‖ * W * O + c₁ * O * 2 := by gcongr
      _ = _ := by ring
  exact ⟨hF1', hD1'⟩

/-- **Theorem 14.3.9 with INNER = ARqp-SC and the exponents `π_j = j(p+1)/p`, relative to an
order `O`** (the core of `theorem_14_3_9_arqp` and `theorem_14_3_9_arqp_corrected`). Under the
assumptions of `theorem_14_3_9_arqpc`, there are constants `κ_F, κ_D ≥ 0` such that for all
tolerances and every TPqp-GC run with INNER = ARqp-SC (`IsTPqpGCARqpSCRun`), and for every `O`
with `ε₀^{-1} ≤ O`, `ε₀^{1-π_l} ε_l^{-π_l} ≤ O` and `(ε₀ ε_j)^{-j} ≤ O` for `l, j ∈ [1 : q]`
(`π_l = Optimization.arqpPiOf False p l`, the "otherwise" entries of (14.2.12)), the evaluation
counts of both phases are at most `κ_F O` and `κ_D O`, Phase 2 (if entered) terminating. The
Phase-1 contract is used in its additive form (`IsARqpSCOutputCost.cost_le_arqp_add_anchored`,
`lemma_14_3_7_add`): the extra `κ_C k₁ + 2 k₁` with `k₁ ≤ ⌈log(θε₀/‖c(x₀)‖)/log β₁⌉₊` is
`O(ε₀^{-1})` (`Real.natCeil_log_div_log_le`). -/
theorem exists_const_order_arqp (hq : 1 ≤ q) (hqp : q ≤ p) {X₀ : Set ℝⁿ}
    {Lc Bc Lf Bf : ℕ → ℝ} (hc : AssumptionCD1pLBX c X X₀ p Lc Bc)
    (hf : AssumptionD1pLBX f X X₀ p Lf Bf) {βF flow fup : ℝ}
    (hB : Chapter07.AssumptionBFb f c X βF flow fup) (P : ARqpCParams) (hθς : P.θ < P.ς)
    {θ β β₁ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 < β) (x₀ : ℝⁿ) :
    ∃ κF κD : ℝ, 0 ≤ κF ∧ 0 ≤ κD ∧
      ∀ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) → ε 0 ≤ βF →
      ∀ (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq n) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCARqpSCRun f c X p q P θ β₁ β ε x₀ xP δP k₁ D nF₁ nD₁ → ∀ O : ℝ,
        (ε 0)⁻¹ ≤ O →
        (∀ l ∈ Finset.Icc 1 q, ε 0 ^ (1 - Optimization.arqpPiOf False p l) *
          ε l ^ (-Optimization.arqpPiOf False p l) ≤ O) →
        (∀ j ∈ Finset.Icc 1 q, ((ε 0 * ε j) ^ j)⁻¹ ≤ O) →
        (θ * ε 0 < ‖c (xP k₁)‖ →
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤ κF * O ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤ κD * O) ∧
        (‖c (xP k₁)‖ ≤ θ * ε 0 → ∃ kε, D.IsEnd f c X q θ ε kε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) + D.funEvals kε ≤ κF * O ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) + D.derivEvals kε ≤ κD * O) := by
  have hp : 1 ≤ p := hq.trans hqp
  obtain ⟨LA, LB, BA, BB, Lμ, Bμ, h1, hνA, hμA⟩ := exists_anchoredCompositeBounds_nu_mu hp hc hf
  set L := anchoredConst Lμ Bμ with hL
  have hLp : 1 ≤ L p := (hμA 0).one_le
  have hκ : 0 < arqpRowKappaDecr False P L p q :=
    mul_pos P.η₁_pos (Optimization.arqpKappaDmOf_pos False P.σmin_pos hθς hLp)
  have hκρ : 0 < Optimization.arqpCallKappaRad P.toARqpParams L p * β * θ := by
    have := (Optimization.arqpCallKappaRad_pos (P := P.toARqpParams) (L := L) (p := p))
    positivity
  obtain ⟨CF, CD, hCF, hCD, hord⟩ :=
    Constrained.IsHighOrderTargetRun.exists_const_order_of_innerTest (f := f) (c := c)
    (X := X) (θ := θ) (β := β) hq (πmax := Optimization.arqpPiOf False p q) hκ
    (Optimization.arqpKappaUns_nonneg (P := P.toARqpParams))
    (Optimization.arqpCallKappaUnc_nonneg P.toARqpParams L p) hκρ
    (Optimization.finMax_one_pos (L := Bf))
    (abs_nonneg (fup - flow + 1)) zero_le_one hθ0 hθ1 hβ0
  obtain ⟨κF₁, κD₁, hκF₁, hκD₁, hph1⟩ := exists_const_phase1_arqp hq hqp hc hf P hθς
    (β := β) (β₁ := β₁) hθ0 x₀
  refine ⟨κF₁ + CF, κD₁ + CD, by positivity, by positivity,
    fun ε hε hεβ xP δP k₁ D nF₁ nD₁ hR O hO0 hOT hOB => ?_⟩
  have h := hR.run
  have hε₀ := hε 0 (by simp)
  have hO1 : 1 ≤ O := ((one_le_inv₀ hε₀.1).2 hε₀.2).trans hO0
  have hOnn : 0 ≤ O := zero_le_one.trans hO1
  obtain ⟨hF1', hD1'⟩ := hph1 ε hε xP δP k₁ D nF₁ nD₁ hR O hO0 hOT
  refine ⟨fun _ => ⟨hF1'.trans (by nlinarith), hD1'.trans (by nlinarith)⟩, fun hc1 => ?_⟩
  -- Phase 2
  have h2 := h.phase2 hc1
  have hin := ((hR.phase2 hc1).isInnerPhaseRunStrong_arqp h2 hμA hc.subset hθς (u := False)
    (fun h => h.elim)).mono_radius
    (ρ' := fun j => Optimization.arqpCallKappaRad P.toARqpParams L p * β * θ * (ε 0 * ε j))
    fun j _ => le_of_eq (by ring)
  have hεI : ∀ l ∈ Finset.Icc 1 q, 0 < ε l ∧ ε l ≤ 1 := fun l hl =>
    hε l (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hl).2))
  obtain ⟨kε, hend, hF2, hD2⟩ := hord h2 hin (fun j hj => mul_pos hε₀.1 (hεI j hj).1)
    (fun l hl =>
      ⟨Optimization.arqpPiOf_nonneg False p l, (Optimization.arqpPiOf_false_mem hp hl).2⟩)
      (hB.of_le hεβ)
    (le_abs_self _) (fun _ hy => hf.contDiffAt_of_le hqp hy)
    (fun _ hy => hc.contDiffAt_of_le hqp hy)
    (fun _ hy _ => hf.norm_iteratedFDeriv_le_finMax hqp (hf.subset hy)) hO0 hOT
    (fun j hj => by
      rw [one_mul, mul_pow_sub_one (by have := (Finset.mem_Icc.1 hj).1; omega) _]
      exact hOB j hj)
  refine ⟨kε, hend, ?_, ?_⟩
  · calc _ ≤ κF₁ * O + CF * O :=
          add_le_add hF1' hF2
      _ = _ := by ring
  · calc _ ≤ κD₁ * O + CD * O := add_le_add hD1' hD2
      _ = _ := by ring

/-- **Theorem 14.3.9** of [cartis2022evaluation] **for every run with INNER = ARqp-SC and the
exponents `π_j = j(p+1)/p` of (14.2.12) ("otherwise" entries, the radius bound (12.2.51)), with
the bad-iteration term**: under the assumptions of `theorem_14_3_9_arqpc`, there are constants
`κ_F`, `κ_D` such that for all tolerances `ε ∈ (0, 1]^{q+1}` with `ε₀ ≤ β_F` and every TPqp-GC run
with INNER = ARqp-SC in both phases (`IsTPqpGCARqpSCRun`), the evaluation counts are at most
`κ_F (O_F + ∑_j (ε₀ ε_j)^{-j})` and `κ_D (O_F + ∑_j (ε₀ ε_j)^{-j})` (Phase 2, if entered,
terminating), with `O_F = tpqpOrderF π q ε` the printed order of the function evaluations. The
extra term comes from the case-(b) iterations whose INNER call ends at a point passing INNER's test
(`Constrained.IsHighOrderTargetRun.complexity_of_innerTest`, radii `ρ_j ∼ ε₀ ε_j`): for `q = p` it
is within the printed
order (`theorem_14_3_9_arqp`); for `q < p` it is not dominated by `O_F` (for `j = 1`, `ε_j = 1` for
`j ≥ 2` and `ε_1 = ε₀^s` with `max(0, q(p+1)/p - 2) < s < p - 1`). -/
theorem theorem_14_3_9_arqp_corrected (hq : 1 ≤ q) (hqp : q ≤ p) {X₀ : Set ℝⁿ}
    {Lc Bc Lf Bf : ℕ → ℝ} (hc : AssumptionCD1pLBX c X X₀ p Lc Bc)
    (hf : AssumptionD1pLBX f X X₀ p Lf Bf) {βF flow fup : ℝ}
    (hB : Chapter07.AssumptionBFb f c X βF flow fup) (P : ARqpCParams) (hθς : P.θ < P.ς)
    {θ β β₁ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 < β) (x₀ : ℝⁿ) :
    ∃ κF κD : ℝ, ∀ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) → ε 0 ≤ βF →
      ∀ (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq n) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCARqpSCRun f c X p q P θ β₁ β ε x₀ xP δP k₁ D nF₁ nD₁ →
        let O := tpqpOrderF (Optimization.arqpPiOf False p) q ε +
          ∑ j ∈ Finset.Icc 1 q, ((ε 0 * ε j) ^ j)⁻¹
        (θ * ε 0 < ‖c (xP k₁)‖ →
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤ κF * O ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤ κD * O) ∧
        (‖c (xP k₁)‖ ≤ θ * ε 0 → ∃ kε, D.IsEnd f c X q θ ε kε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) + D.funEvals kε ≤ κF * O ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) + D.derivEvals kε ≤ κD * O) := by
  obtain ⟨κF, κD, -, -, hmain⟩ :=
    exists_const_order_arqp hq hqp hc hf hB P hθς hθ0 hθ1 hβ0 (β₁ := β₁) x₀
  refine ⟨κF, κD, fun ε hε hεβ xP δP k₁ D nF₁ nD₁ hR => ?_⟩
  intro O
  have hB0 : 0 ≤ ∑ j ∈ Finset.Icc 1 q, ((ε 0 * ε j) ^ j)⁻¹ := Finset.sum_nonneg fun j hj => by
    have := (hε 0 (by simp)).1
    have := (hε j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))).1
    positivity
  have hO0 : 0 ≤ tpqpOrderF (Optimization.arqpPiOf False p) q ε :=
    zero_le_one.trans (one_le_tpqpOrderF (hε 0 (by simp)).1 (hε 0 (by simp)).2)
  have hnn : ∀ i ∈ Finset.Icc 1 q, 0 ≤ ((ε 0 * ε i) ^ i)⁻¹ := fun i hi => by
    have := (hε 0 (by simp)).1
    have := (hε i (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hi).2))).1
    positivity
  exact hmain ε hε hεβ xP δP k₁ D nF₁ nD₁ hR O
    (inv_le_tpqpOrderF.trans (le_add_of_nonneg_right hB0))
    (fun l hl => (term_le_tpqpOrderF hl).trans (le_add_of_nonneg_right hB0))
    fun j hj => (Finset.single_le_sum hnn hj).trans (le_add_of_nonneg_left hO0)

/-- **Theorem 14.3.9** of [cartis2022evaluation] **for every run with INNER = ARqp-SC, in the
printed order, when `q = p`** (exponents `π_j = j(p+1)/p` of (14.2.12), `π_p = p + 1`): under the
assumptions of `theorem_14_3_9_arqpc` with `p = q`, there are constants `κ_F`, `κ_D` such that for
all tolerances `ε ∈ (0, 1]^{q+1}` with `ε₀ ≤ β_F` and every TPqp-GC run with INNER = ARqp-SC in both
phases (`IsTPqpGCARqpSCRun`), Phase 1 alone (if it ends with `‖c(x₁)‖ > θε₀`), resp. both phases
(Phase 2 terminating), use at most `κ_F O_F` evaluations of `(f, c)` and `κ_D O_D` derivative
evaluations, `O_F = max[ε₀^{-1}, max_j ε₀^{1-π_j} ε_j^{-π_j}]` (`tpqpOrderF`) and
`O_D = max_j ε₀^{1-π_j} ε_j^{-π_j}` (`tpqpOrderD`), the orders printed in Theorem 14.3.9. The
bad-iteration term `(ε₀ ε_j)^{-j}` is at most `ε₀^{-p} + ε₀^{1-π_j} ε_j^{-π_j}`
(`Constrained.inv_mul_pow_le_add_arqpPiOf`) and `ε₀^{-p} ≤ ε₀^{1-π_p} ε_p^{-π_p}`; for `q < p` see
`theorem_14_3_9_arqp_corrected`. -/
theorem theorem_14_3_9_arqp (hq : 1 ≤ q) {X₀ : Set ℝⁿ} {Lc Bc Lf Bf : ℕ → ℝ}
    (hc : AssumptionCD1pLBX c X X₀ q Lc Bc) (hf : AssumptionD1pLBX f X X₀ q Lf Bf)
    {βF flow fup : ℝ} (hB : Chapter07.AssumptionBFb f c X βF flow fup) (P : ARqpCParams)
    (hθς : P.θ < P.ς) {θ β β₁ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 < β) (x₀ : ℝⁿ) :
    ∃ κF κD : ℝ, ∀ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) → ε 0 ≤ βF →
      ∀ (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq n) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCARqpSCRun f c X q q P θ β₁ β ε x₀ xP δP k₁ D nF₁ nD₁ →
        (θ * ε 0 < ‖c (xP k₁)‖ →
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤
            κF * tpqpOrderF (Optimization.arqpPiOf False q) q ε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤
            κD * tpqpOrderD (Optimization.arqpPiOf False q) q ε) ∧
        (‖c (xP k₁)‖ ≤ θ * ε 0 → ∃ kε, D.IsEnd f c X q θ ε kε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) + D.funEvals kε ≤
            κF * tpqpOrderF (Optimization.arqpPiOf False q) q ε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) + D.derivEvals kε ≤
            κD * tpqpOrderD (Optimization.arqpPiOf False q) q ε) := by
  obtain ⟨κF, κD, hκF, hκD, hmain⟩ :=
    exists_const_order_arqp hq le_rfl hc hf hB P hθς hθ0 hθ1 hβ0 (β₁ := β₁) x₀
  refine ⟨2 * κF, 2 * κD, fun ε hε hεβ xP δP k₁ D nF₁ nD₁ hR => ?_⟩
  set π := Optimization.arqpPiOf False q with hπ
  set OF := tpqpOrderF π q ε with hOF
  have hε₀ := hε 0 (by simp)
  have hq1 : q ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨hq, le_rfl⟩
  have hπq : π q = (q : ℝ) + 1 := Optimization.arqpPiOf_false_self hq
  have hFD : OF ≤ tpqpOrderD π q ε :=
    tpqpOrderF_le_tpqpOrderD hε hq1 (by rw [hπq]; have : (1 : ℝ) ≤ q := by exact_mod_cast hq
                                        linarith)
  have hO0 : 0 ≤ OF := zero_le_one.trans (one_le_tpqpOrderF hε₀.1 hε₀.2)
  -- the bad-iteration term is within twice the printed order
  have hp_le : ((ε 0) ^ q)⁻¹ ≤ OF := by
    refine le_trans ?_ (term_le_tpqpOrderF hq1)
    have hεq := hε q (Finset.mem_range.2 (Nat.lt_succ_self q))
    have e1 : ε 0 ^ (1 - π q) = ((ε 0) ^ q)⁻¹ := by
      rw [hπq, show 1 - ((q : ℝ) + 1) = -(q : ℝ) by ring, Real.rpow_neg hε₀.1.le,
        Real.rpow_natCast]
    rw [e1]
    have : 1 ≤ ε q ^ (-π q) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hεq.1 hεq.2
        (by rw [hπq]; linarith [(Nat.cast_nonneg q : (0 : ℝ) ≤ q)])
    have : 0 ≤ ((ε 0) ^ q)⁻¹ := by have := hε₀.1; positivity
    nlinarith
  have hmain' := hmain ε hε hεβ xP δP k₁ D nF₁ nD₁ hR (2 * OF)
    (inv_le_tpqpOrderF.trans (by linarith))
    (fun l hl => (term_le_tpqpOrderF hl).trans (by linarith)) fun j hj => by
      have hεj := hε j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
      have := Constrained.inv_mul_pow_le_add_arqpPiOf hε₀.1 hεj.1 (j := j) hq
      have := term_le_tpqpOrderF (π := π) (ε := ε) hj
      linarith
  obtain ⟨hP1, hP2⟩ := hmain'
  have hD : ∀ x : ℝ, x ≤ κD * (2 * OF) → x ≤ 2 * κD * tpqpOrderD π q ε := fun x hx => by
    nlinarith
  refine ⟨fun hc1 => ⟨by linarith [(hP1 hc1).1], hD _ (hP1 hc1).2⟩, fun hc1 => ?_⟩
  obtain ⟨kε, hend, hF, hDD⟩ := hP2 hc1
  exact ⟨kε, hend, by linarith, hD _ hDD⟩

end Theorem1439ARqp

/-! ### Existence of TPqp-GC runs with INNER = ARqp-SC -/

section Existence

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {p q : ℕ} {P : ARqpCParams} {ε : ℕ → ℝ}
  {θ β : ℝ}

/-- TPqp-GC runs with INNER = ARqp-SC in both phases from anchored bounds for `ν` on
`𝓛_ν(x₀)` and for every `μ(·, t)` on `𝓛_μ(t)` (with constants that may depend on `t`): Phase 1 by
LENq-SC with ARqp-SC calls (`exists_algorithm_14_3_2_of_phase2_anchored`), Phase 2 with the calls
of `Constrained.exists_arqpCall`. -/
private theorem exists_isTPqpGCARqpSCRun_of_bounds (hX : IsClosed X) (hq : 1 ≤ q) (hqp : q ≤ p)
    {X₀ : Set ℝⁿ} {x₀ : ℝⁿ} {Lν : ℕ → ℝ}
    (hν : AnchoredCompositeBounds (phi2 c) (zeroCon n) X₀ (nuSublevel c X x₀) p Lν (fun _ => 0))
    (hμ : ∀ t, ∃ L, AnchoredCompositeBounds (Constrained.targetMerit f c t) (zeroCon n) X₀
      (muSublevel f c X t) p L (fun _ => 0)) (hXX₀ : X ⊆ X₀) (P : ARqpCParams)
    (hθς : P.θ < P.ς) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 < β) (hβθ : β ≤ θ)
    (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) {β₁ : ℝ} (hβ₁0 : 0 < β₁)
    (hβ₁1 : β₁ < 1) (hx₀ : x₀ ∈ X) (hβ₁c : β₁ * ‖c x₀‖ < 1) :
    ∃ (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq n) (nF₁ nD₁ : ℕ → ℕ),
      IsTPqpGCARqpSCRun f c X p q P θ β₁ β ε x₀ xP δP k₁ D nF₁ nD₁ := by
  choose Lμ hμA using hμ
  obtain ⟨xP, δP, k₁, D, nF, nD, h, hcalls, hQ⟩ := exists_algorithm_14_3_2_of_phase2_anchored hX
    hq hqp hν hXX₀ P hθς hθ0 hθ1 hε hβ₁0 hβ₁1 hx₀ hβ₁c (β := β)
    (Q := IsARqpSCPhase2Calls f c X p q P θ β ε) fun x₁ hx₁ hc₁ => by
      obtain ⟨D, hD, hcallsD⟩ := phase2_core_of hθ0 hθ1 hβ0 hβθ hε hx₁ hc₁
        (fun x t o => IsARqpSCCallOut (Constrained.targetMerit f c t) X p q P
          (fun j => β * Constrained.targetResidual f c t x * ε j) o.xi o.e o.succ o.δ)
        (fun x t hx hlo hhi _ => Constrained.exists_arqpCall (EuclideanSpace ℝ (Fin 0))
          (hμA t).lipschitzDerivsAnchored_f (hμA t).one_le (hμA t).jet_f hXX₀ P.toARqpParams
          P.σmin_pos hθς hq hqp hX hθ0 hβ0 hβθ hε hx hlo hhi)
      exact ⟨D, hD, fun k hk1 hk => (hcallsD k hk1 hk).2⟩
  exact ⟨xP, δP, k₁, D, nF, nD, ⟨h, hcalls, hQ⟩⟩

/-- **Existence of TPqp-GC runs** ([cartis2022evaluation], Algorithm 14.3.2 is well defined, with
INNER = ARqp-SC in both phases, run as ARqpC-SC with `c = 0`, `h = 0`). Let `X` be closed,
`1 ≤ q ≤ p`, `ν = ½ ‖c‖²` satisfy ν.D1pL and every `μ(·, t)` satisfy μ.D1pL (on `ℝⁿ`, with
constants that may depend on `t`), and `P` be ARqpC constants with `θ < ς`. Then for every
`θ ∈ (0, 1)`, `β ∈ (0, θ]`, tolerances `ε ∈ (0, 1]^{q+1}`, `x₀ ∈ X` and `β₁ ∈ (0, 1)` with
`β₁ ‖c(x₀)‖ < 1` there is a TPqp-GC run from `x₀` whose INNER calls in both phases are runs of
ARqp-SC (`IsTPqpGCARqpSCRun`). Under the book's assumptions of §14.3.2.2 this is
`exists_isTPqpGCARqpSCRun`. -/
theorem exists_algorithm_14_3_2 (hX : IsClosed X) (hq : 1 ≤ q) (hqp : q ≤ p) {Lν : ℕ → ℝ}
    (hν : Chapter12.AssumptionD1pL (phi2 c) p Lν)
    (hμ : ∀ t, ∃ L, Chapter12.AssumptionD1pL (Constrained.targetMerit f c t) p L)
    (P : ARqpCParams) (hθς : P.θ < P.ς) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 < β)
    (hβθ : β ≤ θ) (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) {β₁ : ℝ}
    (hβ₁0 : 0 < β₁) (hβ₁1 : β₁ < 1) {x₀ : ℝⁿ} (hx₀ : x₀ ∈ X) (hβ₁c : β₁ * ‖c x₀‖ < 1) :
    ∃ (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq n) (nF₁ nD₁ : ℕ → ℕ),
      IsTPqpGCARqpSCRun f c X p q P θ β₁ β ε x₀ xP δP k₁ D nF₁ nD₁ :=
  exists_isTPqpGCARqpSCRun_of_bounds hX hq hqp
    (AnchoredCompositeBounds.of_global hν (assumptionCD1pL_zeroCon p) (hq.trans hqp) _)
    (fun t => (hμ t).imp fun _ hL =>
      AnchoredCompositeBounds.of_global hL (assumptionCD1pL_zeroCon p) (hq.trans hqp) _)
    (subset_univ X) P hθς hθ0 hθ1 hβ0 hβθ hε hβ₁0 hβ₁1 hx₀ hβ₁c

/-- **TPqp-GC runs with INNER = ARqp-SC in both phases exist under the book's assumptions**
X.CNe (`X` closed), c.D1pLB.X and f.D1pLB.X (on an open convex `X₀ ⊇ X`), for all ARqpC
constants with `θ < ς`, every `θ ∈ (0, 1)`, `β ∈ (0, θ]`, `ε ∈ (0, 1]^{q+1}`, `β₁ ∈ (0, 1)` with
`β₁ ‖c(x₀)‖ < 1` and `x₀ ∈ X` (so the class `IsTPqpGCARqpSCRun` of `theorem_14_3_9_arqpc` and
`theorem_14_3_9_arqp` is not empty); the bounds come from Lemma 14.3.6
(`exists_anchoredCompositeBounds_nu_mu`). -/
theorem exists_isTPqpGCARqpSCRun (hX : IsClosed X) (hq : 1 ≤ q) (hqp : q ≤ p) {X₀ : Set ℝⁿ}
    {Lc Bc Lf Bf : ℕ → ℝ} (hc : AssumptionCD1pLBX c X X₀ p Lc Bc)
    (hf : AssumptionD1pLBX f X X₀ p Lf Bf) (P : ARqpCParams) (hθς : P.θ < P.ς) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hβ0 : 0 < β) (hβθ : β ≤ θ)
    (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) {β₁ : ℝ} (hβ₁0 : 0 < β₁)
    (hβ₁1 : β₁ < 1) {x₀ : ℝⁿ} (hx₀ : x₀ ∈ X) (hβ₁c : β₁ * ‖c x₀‖ < 1) :
    ∃ (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq n) (nF₁ nD₁ : ℕ → ℕ),
      IsTPqpGCARqpSCRun f c X p q P θ β₁ β ε x₀ xP δP k₁ D nF₁ nD₁ := by
  obtain ⟨LA, LB, BA, BB, Lμ, Bμ, -, hνA, hμA⟩ :=
    exists_anchoredCompositeBounds_nu_mu (hq.trans hqp) hc hf
  exact exists_isTPqpGCARqpSCRun_of_bounds hX hq hqp (hνA x₀) (fun t => ⟨_, hμA t⟩) hc.subset P
    hθς hθ0 hθ1 hβ0 hβθ hε hβ₁0 hβ₁1 hx₀ hβ₁c

end Existence

/-! ### Theorem 14.3.9 on `ℝⁿ` with INNER = ARqp with unit radii (`q ≤ 2`) -/

section Unit

variable {F : ℝⁿ → ℝ} {p q : ℕ} {P : ARqpCParams} {ε : ℕ → ℝ} {xi : ℕ → ℝⁿ} {e : ℕ}
  {succ : ℕ → Prop} {δo : ℕ → ℝ}

/-- One INNER call of Phase 2 of TPqp-GC on `X = ℝⁿ` realized by ARqp with unit radii (the
Chapter 12 regime `X = ℝⁿ`, `q ≤ 2`, of the unit-radius exponents; table (14.2.12) keys that
ARqp-SC entry as "`q = 1`, `X` convex"), with its output radii (`Optimization.IsARqpUnitCallOut`):
an `IsARqpUnitCall` (a prefix of an ARqp run of Chapter 12 whose Step 2, Algorithm 12.2.3, keeps
the radii `1` at the orders `j ≤ 2`) returning the radii `1`, those of the run; its contract is
`Optimization.IsARqpUnitCallOut.contract`. -/
abbrev IsARqpUnitCallOut (F : ℝⁿ → ℝ) (p q : ℕ) (P : ARqpCParams) (ε : ℕ → ℝ) (xi : ℕ → ℝⁿ)
    (e : ℕ) (succ : ℕ → Prop) (δo : ℕ → ℝ) : Prop :=
  Optimization.IsARqpUnitCallOut F p q P.toARqpParams ε xi e succ δo

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {θ β : ℝ} {x₁ : ℝⁿ} {D : TPqpSeq n}

/-- **The INNER calls of Phase 2 of TPqp-GC on `X = ℝⁿ` are ARqp runs with unit radii**: for every
outer iteration `k ≥ 1` reached, the `k`-th call is an `IsARqpUnitCallOut` on `μ(·, t_k)` with
tolerances `β ‖r(x_k, t_k)‖ ε_j`, cut at any iteration
(`Constrained.HighOrderTargetSeq.IsARqpUnitCalls`). -/
abbrev IsARqpUnitPhase2Calls (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (p q : ℕ) (P : ARqpCParams) (θ β : ℝ)
    (ε : ℕ → ℝ) (D : TPqpSeq n) : Prop :=
  D.IsARqpUnitCalls f c p q P.toARqpParams θ β ε

/-- **Every Phase-2 run of TPqp-GC on `ℝⁿ` whose INNER calls are ARqp runs with unit radii
satisfies the INNER contract keyed on INNER's own test** (`IsInnerPhaseRunStrong`,
[cartis2022evaluation], Lemmas 12.2.13 and 14.2.3 with unit radii), with the unit-radius exponents
`π_l = (p+1)/(p-l+1)`, the `t`-independent constants `κ_decr = arqpRowKappaDecr True P L p q`,
`κ_uns = Optimization.arqpKappaUns`, `κ_unc = Optimization.arqpCallKappaUnc` and radii `ρ_j = 1`,
when every `μ(·, t)` has anchored bounds with constants `L` on `𝓛_μ(t)` (`X₀ = ℝⁿ`), `θ < ς` and
`1 ≤ q ≤ p` (`Constrained.IsHighOrderTargetRun.isInnerTestContract_of_isARqpUnitCalls`). -/
theorem IsARqpUnitPhase2Calls.isInnerPhaseRunStrong (h : IsTPqpGCPhase2 f c univ q θ β ε x₁ D)
    (hcalls : IsARqpUnitPhase2Calls f c p q P θ β ε D) {L : ℕ → ℝ}
    (hμ : ∀ t, AnchoredCompositeBounds (Constrained.targetMerit f c t) (zeroCon n) univ
      (muSublevel f c univ t) p L (fun _ => 0)) (hθς : P.θ < P.ς) (hq : 1 ≤ q) (hqp : q ≤ p) :
    IsInnerPhaseRunStrong f c univ q θ β ε D (arqpRowKappaDecr True P L p q)
      (Optimization.arqpKappaUns P.toARqpParams) (Optimization.arqpCallKappaUnc P.toARqpParams L p)
      (Optimization.arqpPiOf True p) (fun _ => 1) :=
  h.isInnerTestContract_of_isARqpUnitCalls hcalls (fun t => (hμ t).lipschitzDerivsAnchored_f)
    (hμ 0).one_le hθς hq hqp

end Unit

/-! ### The unit-radius theorem -/

section UnitTheorem

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {p q : ℕ}

/-- **A run of TPqp-GC on `X = ℝⁿ` with INNER = ARqp with unit radii in both phases**
([cartis2022evaluation], Algorithm 14.3.2 with `X = ℝⁿ`, `q ≤ 2`, INNER = ARqp of Chapter 12 with
Step 2 by Algorithm 12.2.3): a run (`algorithm_14_3_2`) whose Phase-1 INNER calls are ARqp runs
with unit radii on `ν` using `nF₁ k` evaluations of `c` and `nD₁ k` of its derivatives
(`IsARqpUnitOutputCost`), and whose Phase-2 INNER calls are ARqp runs with unit radii on
`μ(·, t_k)`, cut at any iteration (`IsARqpUnitPhase2Calls`). -/
structure IsTPqpGCARqpUnitRun (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (p q : ℕ) (P : ARqpCParams)
    (θ β₁ β : ℝ) (ε : ℕ → ℝ) (x₀ : ℝⁿ) (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ)
    (D : TPqpSeq n) (nF₁ nD₁ : ℕ → ℕ) : Prop where
  /-- The TPqp-GC run on `ℝⁿ`. -/
  run : algorithm_14_3_2 f c univ q θ β₁ β ε x₀ xP δP k₁ D
  /-- The Phase-1 INNER calls are ARqp runs with unit radii with their evaluation counts. -/
  phase1 : ∀ k, 1 ≤ k → k ≤ k₁ → IsARqpUnitOutputCost (phi2 c) p q P
    (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j) (xP (k - 1)) (xP k) (δP k) (nF₁ k)
      (nD₁ k)
  /-- The Phase-2 INNER calls are ARqp runs with unit radii. -/
  phase2 : ‖c (xP k₁)‖ ≤ θ * ε 0 → IsARqpUnitPhase2Calls f c p q P θ β ε D

variable {θ β : ℝ} {ε : ℕ → ℝ} {P : ARqpCParams}

/-- **TPqp-GC runs on `ℝⁿ` with INNER = ARqp with unit radii in both phases exist** for
`1 ≤ q ≤ min(2, p)` (so the class `IsTPqpGCARqpUnitRun` of `theorem_14_3_9_arqp_unit` and
`theorem_14_3_9_arqp_unit_corrected` is not empty there), under c.D1pLB.X and f.D1pLB.X on
`X = X₀ = ℝⁿ`, for all ARqpC constants with `θ < ς`, every `θ ∈ (0, 1)`, `β ∈ (0, θ]`,
`ε ∈ (0, 1]^{q+1}`, `β₁ ∈ (0, 1)` with `β₁ ‖c(x₀)‖ < 1`: Phase 1 by LENq-SC with unit-radius ARqp
calls (`exists_algorithm_14_3_1_unit`), Phase 2 with the calls of
`Constrained.exists_arqpUnitCall` (`phase2_core_of`). -/
theorem exists_isTPqpGCARqpUnitRun (hq : 1 ≤ q) (hq2 : q ≤ 2) (hqp : q ≤ p)
    {Lc Bc Lf Bf : ℕ → ℝ} (hc : AssumptionCD1pLBX c univ univ p Lc Bc)
    (hf : AssumptionD1pLBX f univ univ p Lf Bf) (P : ARqpCParams) (hθς : P.θ < P.ς)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 < β) (hβθ : β ≤ θ)
    (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) {β₁ : ℝ} (hβ₁0 : 0 < β₁)
    (hβ₁1 : β₁ < 1) (x₀ : ℝⁿ) (hβ₁c : β₁ * ‖c x₀‖ < 1) :
    ∃ (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq n) (nF₁ nD₁ : ℕ → ℕ),
      IsTPqpGCARqpUnitRun f c p q P θ β₁ β ε x₀ xP δP k₁ D nF₁ nD₁ := by
  obtain ⟨LA, LB, BA, BB, Lμ, Bμ, -, hνA, hμA⟩ :=
    exists_anchoredCompositeBounds_nu_mu (hq.trans hqp) hc hf
  have hε₁ : ∀ j ∈ Finset.range (q + 1), 0 < phase1Tol θ ε j ∧ phase1Tol θ ε j ≤ 1 := by
    intro j hj
    by_cases h0 : j = 0
    · subst h0
      obtain ⟨h1, h2⟩ := hε 0 hj
      simp only [phase1Tol_zero]
      exact ⟨mul_pos hθ0 h1, by nlinarith⟩
    · rw [phase1Tol_of_ne θ ε h0]
      exact hε j hj
  obtain ⟨xP, δP, nF₁, nD₁, k₁, hxP0, hrun, hhit, hcalls⟩ :=
    exists_algorithm_14_3_1_unit hq hq2 hqp (hνA x₀) P hθς hε₁ hβ₁0 hβ₁1 x₀
      (fun y hy => ⟨mem_univ y, hy⟩) hβ₁c
  by_cases hc1 : ‖c (xP k₁)‖ ≤ θ * ε 0
  · obtain ⟨D, hD, hcallsD⟩ := phase2_core_of (X := univ) hθ0 hθ1 hβ0 hβθ hε (mem_univ (xP k₁))
      hc1 (fun x t o => IsARqpUnitCallOut (Constrained.targetMerit f c t) p q P
        (fun j => β * Constrained.targetResidual f c t x * ε j) o.xi o.e o.succ o.δ)
      (fun x t _ hlo hhi _ => Constrained.exists_arqpUnitCall (hμA t).lipschitzDerivsAnchored_f
        (hμA t).one_le (hμA t).jet_f P.toARqpParams P.σmin_pos hθς hq hq2 hqp hθ0 hβ0 hβθ hε hlo
        hhi)
    exact ⟨xP, δP, k₁, D, nF₁, nD₁, ⟨⟨hxP0, hrun, hhit, fun _ => hD⟩, hcalls,
      fun _ k hk1 hk => (hcallsD k hk1 hk).2⟩⟩
  · exact ⟨xP, δP, k₁, ⟨fun _ => x₀, fun _ => 0, fun _ _ => 0, fun _ _ => x₀, fun _ => 0,
      fun _ _ => False⟩, nF₁, nD₁, ⟨⟨hxP0, hrun, hhit, fun h => absurd h hc1⟩, hcalls,
      fun h => absurd h hc1⟩⟩

/-- **Theorem 14.3.9 on `ℝⁿ` with INNER = ARqp with unit radii, relative to an order `O`** (the
core of `theorem_14_3_9_arqp_unit` and `theorem_14_3_9_arqp_unit_corrected`). Under c.D1pLB.X and
f.D1pLB.X on `X = X₀ = ℝⁿ`, f.B.Fb, `1 ≤ q ≤ p` (the class is non-empty for `q ≤ 2`,
`exists_isTPqpGCARqpUnitRun`; for `q > 2` it may be empty, since Algorithm 12.2.3 may halve the
radii of order `j ≥ 3`) and the constants of `theorem_14_3_9_arqpc`, there are constants
`κ_F, κ_D ≥ 0` such that for all tolerances and every TPqp-GC run with INNER = ARqp with unit
radii (`IsTPqpGCARqpUnitRun`), and every `O` with
`ε₀^{-1} ≤ O`, `ε₀^{1-π_l} ε_l^{-π_l} ≤ O` (`π_l = (p+1)/(p-l+1)`) and `(ε₀ ε_j)^{-1} ≤ O`, the
evaluation counts of both phases are at most `κ_F O` and `κ_D O`, Phase 2 (if entered)
terminating. -/
theorem exists_const_order_arqp_unit (hq : 1 ≤ q) (hqp : q ≤ p)
    {Lc Bc Lf Bf : ℕ → ℝ} (hc : AssumptionCD1pLBX c univ univ p Lc Bc)
    (hf : AssumptionD1pLBX f univ univ p Lf Bf) {βF flow fup : ℝ}
    (hB : Chapter07.AssumptionBFb f c univ βF flow fup) (P : ARqpCParams) (hθς : P.θ < P.ς)
    {θ β β₁ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 < β) (x₀ : ℝⁿ) :
    ∃ κF κD : ℝ, 0 ≤ κF ∧ 0 ≤ κD ∧
      ∀ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) → ε 0 ≤ βF →
      ∀ (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq n) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCARqpUnitRun f c p q P θ β₁ β ε x₀ xP δP k₁ D nF₁ nD₁ → ∀ O : ℝ,
        (ε 0)⁻¹ ≤ O →
        (∀ l ∈ Finset.Icc 1 q, ε 0 ^ (1 - Optimization.arqpPiOf True p l) *
          ε l ^ (-Optimization.arqpPiOf True p l) ≤ O) →
        (∀ j ∈ Finset.Icc 1 q, (ε 0 * ε j)⁻¹ ≤ O) →
        (θ * ε 0 < ‖c (xP k₁)‖ →
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤ κF * O ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤ κD * O) ∧
        (‖c (xP k₁)‖ ≤ θ * ε 0 → ∃ kε, D.IsEnd f c univ q θ ε kε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) + D.funEvals kε ≤ κF * O ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) + D.derivEvals kε ≤ κD * O) := by
  have hp : 1 ≤ p := hq.trans hqp
  obtain ⟨LA, LB, BA, BB, Lμ, Bμ, h1, hνA, hμA⟩ := exists_anchoredCompositeBounds_nu_mu hp hc hf
  set Lν := nuAnchoredConst LA LB BA BB ‖c x₀‖ with hLν
  set L := anchoredConst Lμ Bμ with hL
  have hLp : 1 ≤ L p := (hμA 0).one_le
  have hκ : 0 < arqpRowKappaDecr True P L p q :=
    mul_pos P.η₁_pos (Optimization.arqpKappaDmOf_pos True P.σmin_pos hθς hLp)
  obtain ⟨CF, CD, hCF, hCD, hord⟩ :=
    Constrained.IsHighOrderTargetRun.exists_const_order_of_innerTest (f := f) (c := c)
    (X := univ) (θ := θ) (β := β) hq (πmax := Optimization.arqpPiOf True p q) hκ
    (Optimization.arqpKappaUns_nonneg (P := P.toARqpParams))
    (Optimization.arqpCallKappaUnc_nonneg P.toARqpParams L p) one_pos
    (Optimization.finMax_one_pos (L := Bf))
    (abs_nonneg (fup - flow + 1)) zero_le_one hθ0 hθ1 hβ0
  -- the Phase-1 constants
  have hLνp : 1 ≤ Lν p := (hνA x₀).one_le
  set κF₁ := Optimization.kappaAARqpOf True P.toARqpParams Lν p q with hκF₁
  set κD₁ := Optimization.kappaSARqpOf True P.toARqpParams Lν p q with hκD₁
  have hκD : 0 < κD₁ := Optimization.kappaSARqpOf_pos True P.σmin_pos hθς hLνp
  have hκF : 0 ≤ κF₁ := by
    rw [hκF₁]
    rw [Optimization.kappaAARqpOf_def]
    exact mul_nonneg hκD.le Optimization.arqpKappaUns_nonneg
  have hκC := Optimization.kappaCARqp_nonneg P.toARqpParams Lν p
  set W := ∑ j ∈ Finset.Icc 1 q, |β₁ ^ (1 - 2 * Optimization.arqpPiOf True p j) /
    (β₁ ^ (1 - Optimization.arqpPiOf True p j) - 1) * θ ^ (1 - Optimization.arqpPiOf True p j)|
        with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set c₁ := 1 + ‖c x₀‖ / (θ * |Real.log β₁|) with hc₁
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; positivity
  refine ⟨1 / 2 * κF₁ * ‖c x₀‖ * W + Optimization.kappaCARqp P.toARqpParams Lν p * c₁ + CF,
    1 / 2 * κD₁ * ‖c x₀‖ * W + 2 * c₁ + CD, by positivity, by positivity,
    fun ε hε hεβ xP δP k₁ D nF₁ nD₁ hR O hO0 hOT hOB => ?_⟩
  have h := hR.run
  have hε₀ := hε 0 (by simp)
  have hO1 : 1 ≤ O := ((one_le_inv₀ hε₀.1).2 hε₀.2).trans hO0
  have hOnn : 0 ≤ O := zero_le_one.trans hO1
  have hβ₁0 := h.phase1.β_pos
  have hβ₁1 := h.phase1.β_lt_one
  have hεI : ∀ l ∈ Finset.Icc 1 q, 0 < ε l ∧ ε l ≤ 1 := fun l hl =>
    hε l (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hl).2))
  -- Phase 1: the number of iterations and the additive cost contract
  have hk₁ : (k₁ : ℝ) ≤ c₁ * O := by
    obtain ⟨⟨kmax, hhit, hkmax, -⟩, -⟩ := theorem_14_3_3 h.phase1
    rw [hhit.unique h.phase1_end, phase1Tol_zero, h.start] at hkmax
    have h1 : (k₁ : ℝ) ≤ 1 + ‖c x₀‖ / (θ * ε 0 * |Real.log β₁|) :=
      (Nat.cast_le.2 hkmax).trans (Real.natCeil_log_div_log_le (mul_pos hθ0 hε₀.1)
        (norm_nonneg _) hβ₁0 hβ₁1)
    have h2 : ‖c x₀‖ / (θ * ε 0 * |Real.log β₁|) = ‖c x₀‖ / (θ * |Real.log β₁|) * (ε 0)⁻¹ := by
      field_simp
    have h3 : 0 ≤ ‖c x₀‖ / (θ * |Real.log β₁|) := by positivity
    calc (k₁ : ℝ) ≤ 1 + ‖c x₀‖ / (θ * |Real.log β₁|) * (ε 0)⁻¹ := h2 ▸ h1
      _ ≤ O + ‖c x₀‖ / (θ * |Real.log β₁|) * O := by gcongr
      _ = c₁ * O := by rw [hc₁]; ring
  have hcost : ∀ k ∈ Finset.Icc 1 k₁,
      (nF₁ k : ℝ) ≤ innerEvalBound κF₁ (Optimization.arqpPiOf True p) q (phi2 c (xP (k - 1)))
        (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j) +
          Optimization.kappaCARqp P.toARqpParams Lν p ∧
      (nD₁ k : ℝ) ≤ innerEvalBound κD₁ (Optimization.arqpPiOf True p) q (phi2 c (xP (k - 1)))
        (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j) + 2 := by
    intro k hk
    obtain ⟨hk1, hkk⟩ := Finset.mem_Icc.1 hk
    have hck : ‖c (xP (k - 1))‖ ≤ ‖c x₀‖ := by
      have := h.phase1.norm_le_pow_mul (Nat.zero_le (k - 1)) fun l hl =>
        h.phase1_end.2 l (by omega)
      rw [h.start] at this
      exact this.trans (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hβ₁0.le hβ₁1.le))
    have hcpos : θ * ε 0 < ‖c (xP (k - 1))‖ := by
      have hns := h.phase1_end.2 (k - 1) (by omega)
      exact not_le.1 fun h' => hns (Or.inl (by rw [phase1Tol_zero]; exact h'))
    have hβc : β₁ * ‖c x₀‖ < 1 := by have := h.phase1.β_mul_lt_one; rwa [h.start] at this
    have hε' : ∀ j ∈ Finset.Icc 1 q, 0 < β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j ∧
        β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j ≤ 1 := fun j hj => by
      rw [phase1Tol_of_ne θ ε (by have := (Finset.mem_Icc.1 hj).1; omega)]
      have hcp : 0 < ‖c (xP (k - 1))‖ := lt_of_le_of_lt (mul_pos hθ0 hε₀.1).le hcpos
      obtain ⟨hej0, hej1⟩ := hεI j hj
      refine ⟨by positivity, ?_⟩
      have : β₁ * ‖c (xP (k - 1))‖ ≤ 1 := by nlinarith
      calc β₁ * ‖c (xP (k - 1))‖ * ε j ≤ 1 * 1 := by gcongr
        _ = 1 := one_mul 1
    exact (hR.phase1 k hk1 hkk).cost_le_add_anchored (hνA x₀)
      (fun y => by rw [phi2_apply]; positivity) hθς hq hqp hε'
      (fun y hyk => ⟨mem_univ y, (Constrained.halfSqNorm_le_halfSqNorm_iff.1 hyk).trans hck⟩)
  have hπ1 : ∀ l ∈ Finset.Icc 1 q, 1 < Optimization.arqpPiOf True p l := fun l hl =>
    (Optimization.arqpPiOf_true_mem_Icc hqp hl).1
  have hF1 := (lemma_14_3_7_add h hθ0 hπ1 hκF fun k hk => (hcost k hk).1).trans
    (add_le_add (Constrained.mul_sum_le_mul_sum_abs_mul hκF (norm_nonneg _)
      (fun j hj => (hε j hj).1) hOT) le_rfl)
  have hD1 := (lemma_14_3_7_add h hθ0 hπ1 hκD.le fun k hk => (hcost k hk).2).trans
    (add_le_add (Constrained.mul_sum_le_mul_sum_abs_mul hκD.le (norm_nonneg _)
      (fun j hj => (hε j hj).1) hOT) le_rfl)
  rw [← hW] at hF1 hD1
  have hF1' : ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤
      (1 / 2 * κF₁ * ‖c x₀‖ * W + Optimization.kappaCARqp P.toARqpParams Lν p * c₁) * O := by
    calc _ ≤ 1 / 2 * κF₁ * ‖c x₀‖ * W * O + k₁ * Optimization.kappaCARqp P.toARqpParams Lν p := hF1
      _ ≤ 1 / 2 * κF₁ * ‖c x₀‖ * W * O + c₁ * O * Optimization.kappaCARqp P.toARqpParams Lν p := by
          gcongr
      _ = _ := by ring
  have hD1' : ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤ (1 / 2 * κD₁ * ‖c x₀‖ * W + 2 * c₁) * O := by
    calc _ ≤ 1 / 2 * κD₁ * ‖c x₀‖ * W * O + k₁ * 2 := hD1
      _ ≤ 1 / 2 * κD₁ * ‖c x₀‖ * W * O + c₁ * O * 2 := by gcongr
      _ = _ := by ring
  refine ⟨fun _ => ⟨hF1'.trans (by nlinarith), hD1'.trans (by nlinarith)⟩, fun hc1 => ?_⟩
  -- Phase 2
  have h2 := h.phase2 hc1
  have hin := ((hR.phase2 hc1).isInnerPhaseRunStrong h2 hμA hθς hq hqp).mono_radius
    (ρ' := fun _ => 1 * 1) fun j _ => le_of_eq (one_mul 1)
  obtain ⟨kε, hend, hF2, hD2⟩ := hord h2 hin (fun _ _ => one_pos) (fun l hl =>
      ⟨Optimization.arqpPiOf_nonneg True p l, (Optimization.arqpPiOf_true_mem_Icc hqp hl).2⟩)
      (hB.of_le hεβ)
    (le_abs_self _) (fun _ _ => hf.contDiffAt_of_le hqp (mem_univ _))
    (fun _ _ => hc.contDiffAt_of_le hqp (mem_univ _))
    (fun _ hy _ => hf.norm_iteratedFDeriv_le_finMax hqp (hf.subset hy)) hO0 hOT
    (fun j hj => by rw [one_pow, mul_one, one_mul]; exact hOB j hj)
  refine ⟨kε, hend, ?_, ?_⟩
  · calc _ ≤ (1 / 2 * κF₁ * ‖c x₀‖ * W + Optimization.kappaCARqp P.toARqpParams Lν p * c₁) * O +
          CF * O := add_le_add hF1' hF2
      _ = _ := by ring
  · calc _ ≤ (1 / 2 * κD₁ * ‖c x₀‖ * W + 2 * c₁) * O + CD * O := add_le_add hD1' hD2
      _ = _ := by ring

/-- **Theorem 14.3.9** of [cartis2022evaluation] **on `ℝⁿ` for every run with INNER = ARqp with
unit radii (`q ≤ 2`), with the bad-iteration term**: under c.D1pLB.X and f.D1pLB.X on
`X = X₀ = ℝⁿ`, f.B.Fb and `1 ≤ q ≤ p` (the class is non-empty for `q ≤ 2`,
`exists_isTPqpGCARqpUnitRun`, where Algorithm 12.2.3 keeps the radii `1`; for `q > 2` it may be
empty), with the constants of `theorem_14_3_9_arqpc`, there are constants `κ_F`, `κ_D` such
that for all tolerances `ε ∈ (0, 1]^{q+1}` with `ε₀ ≤ β_F` and every run `IsTPqpGCARqpUnitRun`, the
evaluation counts are at most `κ_F (O_F + ∑_j (ε₀ ε_j)^{-1})` and `κ_D (O_F + ∑_j (ε₀ ε_j)^{-1})`
(Phase 2, if entered, terminating), with the unit-radius exponents `π_j = (p+1)/(p-j+1)` of
(14.2.12) in `O_F = tpqpOrderF π q ε`. The extra term (case-(b) iterations ending at a point
passing INNER's test, radii `1`) is within the printed order for `q = p`
(`theorem_14_3_9_arqp_unit`); for `q < p` it is not dominated by `O_F`
(`exists_tpqpOrderF_lt_arqp_unit`). -/
theorem theorem_14_3_9_arqp_unit_corrected (hq : 1 ≤ q) (hqp : q ≤ p)
    {Lc Bc Lf Bf : ℕ → ℝ} (hc : AssumptionCD1pLBX c univ univ p Lc Bc)
    (hf : AssumptionD1pLBX f univ univ p Lf Bf) {βF flow fup : ℝ}
    (hB : Chapter07.AssumptionBFb f c univ βF flow fup) (P : ARqpCParams) (hθς : P.θ < P.ς)
    {θ β β₁ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 < β) (x₀ : ℝⁿ) :
    ∃ κF κD : ℝ, ∀ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) → ε 0 ≤ βF →
      ∀ (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq n) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCARqpUnitRun f c p q P θ β₁ β ε x₀ xP δP k₁ D nF₁ nD₁ →
        let O := tpqpOrderF (Optimization.arqpPiOf True p) q ε +
          ∑ j ∈ Finset.Icc 1 q, (ε 0 * ε j)⁻¹
        (θ * ε 0 < ‖c (xP k₁)‖ →
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤ κF * O ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤ κD * O) ∧
        (‖c (xP k₁)‖ ≤ θ * ε 0 → ∃ kε, D.IsEnd f c univ q θ ε kε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) + D.funEvals kε ≤ κF * O ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) + D.derivEvals kε ≤ κD * O) := by
  obtain ⟨κF, κD, -, -, hmain⟩ :=
    exists_const_order_arqp_unit hq hqp hc hf hB P hθς hθ0 hθ1 hβ0 (β₁ := β₁) x₀
  refine ⟨κF, κD, fun ε hε hεβ xP δP k₁ D nF₁ nD₁ hR => ?_⟩
  intro O
  have hnn : ∀ i ∈ Finset.Icc 1 q, 0 ≤ (ε 0 * ε i)⁻¹ := fun i hi => by
    have := (hε 0 (by simp)).1
    have := (hε i (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hi).2))).1
    positivity
  have hB0 : 0 ≤ ∑ j ∈ Finset.Icc 1 q, (ε 0 * ε j)⁻¹ := Finset.sum_nonneg hnn
  have hO0 : 0 ≤ tpqpOrderF (Optimization.arqpPiOf True p) q ε :=
    zero_le_one.trans (one_le_tpqpOrderF (hε 0 (by simp)).1 (hε 0 (by simp)).2)
  exact hmain ε hε hεβ xP δP k₁ D nF₁ nD₁ hR O
    (inv_le_tpqpOrderF.trans (le_add_of_nonneg_right hB0))
    (fun l hl => (term_le_tpqpOrderF hl).trans (le_add_of_nonneg_right hB0))
    fun j hj => (Finset.single_le_sum hnn hj).trans (le_add_of_nonneg_left hO0)

/-- **Theorem 14.3.9** of [cartis2022evaluation] **on `ℝⁿ` for every run with INNER = ARqp with
unit radii, in the printed order, when `q = p ≤ 2`** (unit-radius exponents
`π_j = (p+1)/(p-j+1)`, which for `p = q ≤ 2` are the exponents `j(p+1)/p`, `π_p = p + 1`): under
the assumptions of `theorem_14_3_9_arqp_unit_corrected` with `p = q`, there are constants `κ_F`,
`κ_D` such that for all tolerances `ε ∈ (0, 1]^{q+1}` with `ε₀ ≤ β_F` and every run
`IsTPqpGCARqpUnitRun`, Phase 1 alone (if it ends with `‖c(x₁)‖ > θε₀`), resp. both phases (Phase 2
terminating), use at most `κ_F O_F` evaluations of `(f, c)` and `κ_D O_D` derivative evaluations,
`O_F = tpqpOrderF π q ε`, `O_D = tpqpOrderD π q ε`. -/
theorem theorem_14_3_9_arqp_unit (hq : 1 ≤ q) (hq2 : q ≤ 2) {Lc Bc Lf Bf : ℕ → ℝ}
    (hc : AssumptionCD1pLBX c univ univ q Lc Bc) (hf : AssumptionD1pLBX f univ univ q Lf Bf)
    {βF flow fup : ℝ} (hB : Chapter07.AssumptionBFb f c univ βF flow fup) (P : ARqpCParams)
    (hθς : P.θ < P.ς) {θ β β₁ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 < β) (x₀ : ℝⁿ) :
    ∃ κF κD : ℝ, ∀ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) → ε 0 ≤ βF →
      ∀ (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq n) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCARqpUnitRun f c q q P θ β₁ β ε x₀ xP δP k₁ D nF₁ nD₁ →
        (θ * ε 0 < ‖c (xP k₁)‖ →
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤
            κF * tpqpOrderF (Optimization.arqpPiOf True q) q ε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤
            κD * tpqpOrderD (Optimization.arqpPiOf True q) q ε) ∧
        (‖c (xP k₁)‖ ≤ θ * ε 0 → ∃ kε, D.IsEnd f c univ q θ ε kε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) + D.funEvals kε ≤
            κF * tpqpOrderF (Optimization.arqpPiOf True q) q ε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) + D.derivEvals kε ≤
            κD * tpqpOrderD (Optimization.arqpPiOf True q) q ε) := by
  obtain ⟨κF, κD, hκF, hκD, hmain⟩ :=
    exists_const_order_arqp_unit hq le_rfl hc hf hB P hθς hθ0 hθ1 hβ0 (β₁ := β₁) x₀
  refine ⟨2 * κF, 2 * κD, fun ε hε hεβ xP δP k₁ D nF₁ nD₁ hR => ?_⟩
  set π := Optimization.arqpPiOf True q with hπ
  set OF := tpqpOrderF π q ε with hOF
  have hε₀ := hε 0 (by simp)
  have hq1 : q ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨hq, le_rfl⟩
  have hπq : π q = (q : ℝ) + 1 := by
    rw [hπ, Optimization.arqpPiOf_of_pos trivial, Nat.sub_self]
    push_cast
    ring
  have hFD : OF ≤ tpqpOrderD π q ε :=
    tpqpOrderF_le_tpqpOrderD hε hq1 (by rw [hπq]; have : (1 : ℝ) ≤ q := by exact_mod_cast hq
                                        linarith)
  have hO0 : 0 ≤ OF := zero_le_one.trans (one_le_tpqpOrderF hε₀.1 hε₀.2)
  have hp_le : ((ε 0) ^ q)⁻¹ ≤ OF := by
    refine le_trans ?_ (term_le_tpqpOrderF hq1)
    have hεq := hε q (Finset.mem_range.2 (Nat.lt_succ_self q))
    have e1 : ε 0 ^ (1 - π q) = ((ε 0) ^ q)⁻¹ := by
      rw [hπq, show 1 - ((q : ℝ) + 1) = -(q : ℝ) by ring, Real.rpow_neg hε₀.1.le,
        Real.rpow_natCast]
    rw [e1]
    have : 1 ≤ ε q ^ (-π q) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hεq.1 hεq.2
        (by rw [hπq]; linarith [(Nat.cast_nonneg q : (0 : ℝ) ≤ q)])
    have : 0 ≤ ((ε 0) ^ q)⁻¹ := by have := hε₀.1; positivity
    nlinarith
  have hmain' := hmain ε hε hεβ xP δP k₁ D nF₁ nD₁ hR (2 * OF)
    (inv_le_tpqpOrderF.trans (by linarith))
    (fun l hl => (term_le_tpqpOrderF hl).trans (by linarith)) fun j hj => by
      have hεj := hε j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
      have hj1 := (Finset.mem_Icc.1 hj).1
      have hx0 : 0 < ε 0 * ε j := mul_pos hε₀.1 hεj.1
      have hx1 : ε 0 * ε j ≤ 1 := by nlinarith
      have h1 : (ε 0 * ε j)⁻¹ ≤ ((ε 0 * ε j) ^ j)⁻¹ := by
        refine inv_anti₀ (by positivity) ?_
        calc (ε 0 * ε j) ^ j ≤ (ε 0 * ε j) ^ 1 := pow_le_pow_of_le_one hx0.le hx1 hj1
          _ = ε 0 * ε j := pow_one _
      have h2 := Constrained.inv_mul_pow_le_add_arqpPiOf hε₀.1 hεj.1 (j := j) hq
      rw [← Optimization.arqpPiOf_true_eq_false hq2 hj] at h2
      have := term_le_tpqpOrderF (π := π) (ε := ε) hj
      linarith
  obtain ⟨hP1, hP2⟩ := hmain'
  have hD : ∀ x : ℝ, x ≤ κD * (2 * OF) → x ≤ 2 * κD * tpqpOrderD π q ε := fun x hx => by
    nlinarith
  refine ⟨fun hc1 => ⟨by linarith [(hP1 hc1).1], hD _ (hP1 hc1).2⟩, fun hc1 => ?_⟩
  obtain ⟨kε, hend, hF, hDD⟩ := hP2 hc1
  exact ⟨kε, hend, by linarith, hD _ hDD⟩

end UnitTheorem

/-! ### For `q < p` the bad-iteration term exceeds the printed order -/

section NotDominated

/-- **The term `(ε₀ ε_1)^{-1}` is not dominated by the printed order** when `1 < π_1 < 2` and
`π_i - 2 < (2 - π_1)/(π_1 - 1)` for every `i ∈ [1 : q]`: for every `C` there are tolerances
`ε ∈ (0, 1]^{q+1}` (`ε₀ = δ`, `ε_1 = δ^a`, `ε_i = 1` for `i ≥ 2`, `δ` small) with
`C max[ε₀^{-1}, max_j ε₀^{1-π_j} ε_j^{-π_j}] < (ε₀ ε_1)^{-1}`. -/
theorem exists_tpqpOrderF_lt {π : ℕ → ℝ} {q : ℕ} (hπ1 : 1 < π 1) (hπ2 : π 1 < 2)
    (hπ : ∀ i ∈ Finset.Icc 1 q, π i - 2 < (2 - π 1) / (π 1 - 1)) (C : ℝ) :
    ∃ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) ∧
      C * tpqpOrderF π q ε < (ε 0 * ε 1)⁻¹ :=
  Constrained.exists_tol_mul_finMax_lt hπ1 hπ2 hπ C

/-- **For `q < p` the bound of `theorem_14_3_9_arqp_corrected` is not within the printed order**
(ARqp-SC exponents `π_j = j(p+1)/p`): for every `C` there are tolerances with
`C O_F < (ε₀ ε_1)^{-1}`, a lower bound for its extra term `∑_j (ε₀ ε_j)^{-j}`
(`exists_tpqpOrderF_lt` with `π_1 = (p+1)/p`, `(2 - π_1)/(π_1 - 1) = p - 1 > q(p+1)/p - 2`). -/
theorem exists_tpqpOrderF_lt_arqp {p q : ℕ} (hq : 1 ≤ q) (hqp : q < p) (C : ℝ) :
    ∃ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) ∧
      C * tpqpOrderF (Optimization.arqpPiOf False p) q ε < (ε 0 * ε 1)⁻¹ :=
  Constrained.exists_tol_mul_finMax_lt_arqpPiOf hq hqp C

/-- **For `q < p`, `q ≤ 2`, the bound of `theorem_14_3_9_arqp_unit_corrected` is not within the
printed order** (unit-radius exponents `π_j = (p+1)/(p-j+1)`): for every `C` there are tolerances
with `C O_F < (ε₀ ε_1)^{-1}` (`exists_tpqpOrderF_lt`; `(2 - π_1)/(π_1 - 1) = p - 1`, and
`π_2 - 2 = (3 - p)/(p - 1) < p - 1` for `p ≥ 3`). -/
theorem exists_tpqpOrderF_lt_arqp_unit {p q : ℕ} (hq : 1 ≤ q) (hq2 : q ≤ 2) (hqp : q < p)
    (C : ℝ) :
    ∃ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) ∧
      C * tpqpOrderF (Optimization.arqpPiOf True p) q ε < (ε 0 * ε 1)⁻¹ :=
  Constrained.exists_tol_mul_finMax_lt_arqpPiOf_true hq hq2 hqp C

end NotDominated

end ARqpSCRuns


/-! ## INNER = ARqp-SC: the printed order fails for `q < p` -/

section ARqpSCSharp

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

open Constrained.TwoPhaseExample

/-- The ARqpC constants of `theorem_14_3_9_arqp_counterexample`: those of
`Constrained.TwoPhaseExample.BoxARqp.params` (`σ_min = 10⁻⁶ > 0`). -/
private noncomputable def boxARqpParams : ARqpCParams :=
  ⟨BoxARqp.params, by rw [BoxARqp.params_σmin]; norm_num⟩

/-- **Theorem 14.3.9 of [cartis2022evaluation] fails for runs of ARqp-SC that re-initialise `μ` at
Step 2.1 of Algorithm 14.1.2, when `q ∈ {1, 2}` and `p ≥ q + 3`** (the exponents `π_j = j(p+1)/p` of
(14.2.12), "otherwise" entry; for `q = 1` the exponent `(p+1)/p` is also that of the "`q = 1`, `X`
convex" ARqp-SC entry and of the convex ARqpC-SC entry). There is one problem (`n = 2`, `m = 1`,
`X = [-1, 1]²`, `f(x) = x₁ - x₂/16`, `c(x) = x₁²/2`) satisfying the assumptions of the theorem —
X.CNe (`AssumptionXCNe`; `X` also convex), c.D1pLB.X and f.D1pLB.X on `X₀ = B(0, 2)`, f.B.Fb on
`ℱ_1` with `f_low = -2`, `f_up = 2` — and ARqpC constants `P` (`BoxARqp.params`, with `θ < ς`) such
that, with `θ = β = 1/2`, `x₀ = (0, 0)` and every Phase-1 constant `β₁ ∈ (0, 1)`, for all `κ_F`,
`κ_D` there are tolerances `ε_j ∈ (0, 1]` (`ε₀ ≤ β_F = 1`, `ε₀, ε₁ ≤ κ_F⁻¹` when `κ_F ≥ 1`,
`ε₂ = 1`) and a TPqp-GC run whose INNER calls in both phases are ARqp-SC runs (`IsTPqpGCARqpSCRun`,
the run class of `theorem_14_3_9_arqp`; Phase 1 makes no call and Phase 2 is entered at `x₀`) such
that at its termination index `k_ε` the numbers of evaluations of `(f, c)` and of their derivatives
exceed `κ_F max[ε₀^{-1}, max_j ε₀^{1-π_j} ε_j^{-π_j}]` and `κ_D max_j ε₀^{1-π_j} ε_j^{-π_j}`, the
orders printed in the theorem, and are at least `(ε₀ ε₁)^{-1}/128`.

The run (`BoxARqp.seq`): for `u = 1/(4N⁵)`, `ε₀ = u²/2 + u³/2`, `ε₁ = 3u/2` and `M = N¹⁵`, Phase 2
makes `M + 1` outer iterations, each a single successful ARqp-SC iteration
(`BoxARqp.isARqpCallOut_run`): the first moves from `(0, 0)` to `(u, ·)`, the next `M - 1` move
along `x₂` with `f(x_{k+1}) = t_k - E_k`, `E_k ≈ u³/2 ≈ 2 ε₀ ε₁/3`, where
`∇μ(·, t_k) = (u³/2 - E_k, E_k/16)` is nearly zero (INNER stops; case (b), the target drops by
`2E_k`; after the reflection the gradient is `≈ (u³, ·)` and (14.3.34) fails), and the last lands at
`(-3u/4, ·)` where (14.3.32) holds with `f > t` (case (c)). Each step satisfies the Step-2
conditions (14.1.12)–(14.1.13), all the printed Algorithm 14.1.1 asks for, and is an output of the
detailed Step 2 (Algorithm 14.1.2) initialized with `μ = Δm(s)/(m(0) - m*)` at Step 2.1
(`μ ∈ (0, 1]` is chosen afresh at every Step 2, not fixed at Step 0, and the book notes after
Algorithm 12.2.3 that global minimization is not required): an approximate critical point of the
model with tiny model decrease, not an approximate global minimizer. The Taylor models are exact
(`μ` is a quartic polynomial, `p ≥ 4`; `BoxARqp.taylorSum_targetMerit`), so every ratio is `1`; the
second-order tests (`q = 2`) hold with room to spare. The number of evaluations is
`M + 2 ∼ (ε₀ ε₁)^{-1}`, the extra term of `theorem_14_3_9_arqp_corrected`, which is thus attained
(for `q ∈ {1, 2}`, `p ≥ q + 3`). -/
theorem theorem_14_3_9_arqp_counterexample {p q : ℕ} (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (hpq : q + 3 ≤ p) :
    ∃ (f : ℝ² → ℝ) (c : ℝ² → ℝ¹) (X : Set ℝ²) (Lc Bc Lf Bf : ℕ → ℝ) (P : ARqpCParams),
      AssumptionXCNe X ∧ Convex ℝ X ∧ AssumptionCD1pLBX c X (ball 0 2) p Lc Bc ∧
      AssumptionD1pLBX f X (ball 0 2) p Lf Bf ∧ Chapter07.AssumptionBFb f c X 1 (-2) 2 ∧
      P.θ < P.ς ∧
      ∀ β₁ κF κD : ℝ, 0 < β₁ → β₁ < 1 →
        ∃ (ε : ℕ → ℝ) (xP : ℕ → ℝ²) (δP : ℕ → ℕ → ℝ) (D : TPqpSeq 2),
          (∀ j, 0 < ε j ∧ ε j ≤ 1) ∧ (1 ≤ κF → ε 0 ≤ κF⁻¹ ∧ ε 1 ≤ κF⁻¹) ∧
          (∀ nF₁ nD₁ : ℕ → ℕ, IsTPqpGCARqpSCRun f c X p q P (1 / 2) β₁ (1 / 2) ε (pt 0 0) xP δP 0
            D nF₁ nD₁) ∧
          ‖c (xP 0)‖ ≤ 1 / 2 * ε 0 ∧ (∃ kε, D.IsEnd f c X q (1 / 2) ε kε) ∧
          ∀ kε, D.IsEnd f c X q (1 / 2) ε kε →
            κF * tpqpOrderF (Optimization.arqpPiOf False p) q ε < D.funEvals kε ∧
            κD * tpqpOrderD (Optimization.arqpPiOf False p) q ε < D.derivEvals kε ∧
            (ε 0 * ε 1)⁻¹ ≤ 128 * D.funEvals kε := by
  obtain ⟨⟨Lf, Bf, hf⟩, Lc, Bc, hc⟩ := box_assumptionD1pLBX (1 / 16) p
  refine ⟨Box.obj (1 / 16), Box.con, Box.square, Lc, Bc, Lf, Bf, boxARqpParams,
    ⟨Box.isClosed_square, ⟨pt 0 0, Box.pt_mem_square (by norm_num) (by norm_num)⟩⟩,
    Box.convex_square, hc, hf, box_assumptionBFb (by norm_num), BoxARqp.params_θ_lt_ς,
    fun β₁ κF κD hβ₁ hβ₁1 => ?_⟩
  set C := max (max κF κD) 1 with hC_def
  have hC1 : 1 ≤ C := le_max_right _ _
  obtain ⟨N, hN3, hNC, hCε⟩ := BoxARqp.exists_params C
  have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hNp : (0 : ℝ) < N := by linarith
  set u : ℝ := 1 / (4 * N ^ 5) with hu_def
  set M : ℕ := N ^ 15 with hM_def
  have hu : 0 < u := by positivity
  have hN5 : (243 : ℝ) ≤ (N : ℝ) ^ 5 := by
    have := pow_le_pow_left₀ (by norm_num) hNR 5; norm_num at this; linarith
  have hu' : u ≤ 1 / 200 := by
    rw [hu_def]; apply one_div_le_one_div_of_le (by norm_num); linarith
  have hMR : ((M : ℕ) : ℝ) = (N : ℝ) ^ 15 := by rw [hM_def]; push_cast; ring
  have hMe : u ^ 3 * M = 1 / 64 := by
    rw [hMR, hu_def]; field_simp; ring
  have hM : u ^ 3 * M ≤ 1 / 64 := hMe.le
  have hM1 : 1 ≤ M := Nat.one_le_pow _ _ (by omega)
  have hu7 : u ≤ 1 / 7 := by linarith
  have hc0 : ‖Box.con (pt 0 0)‖ = 0 := by rw [Box.norm_con]; simp
  have hrun : ∀ nF₁ nD₁ : ℕ → ℕ, IsTPqpGCARqpSCRun (Box.obj (1 / 16)) Box.con Box.square p q
      boxARqpParams (1 / 2) β₁ (1 / 2) (BoxARqp.tol u) (pt 0 0) (fun _ => pt 0 0) (fun _ _ => 1) 0
      (BoxARqp.seq u M) nF₁ nD₁ := fun _ _ =>
    ⟨IsTPqpGCPhase2.algorithm_14_3_2_of_stop
      (BoxARqp.isHighOrderTargetRun hu hu' hM hM1 hq1 hq2) hβ₁ hβ₁1,
      fun k hk1 hk0 => absurd hk1 (by omega),
      fun _ => BoxARqp.isARqpCallOut_calls hu hu' hM hM1 hq1 hq2 (by omega)⟩
  refine ⟨BoxARqp.tol u, fun _ => pt 0 0, fun _ _ => 1, BoxARqp.seq u M,
    fun j => ⟨BoxARqp.tol_pos hu j, BoxARqp.tol_le_one hu hu7 j⟩, fun hκ => ?_,
    hrun,
    by rw [hc0]; exact (mul_pos (by norm_num) (BoxARqp.tol_pos hu 0)).le,
    ⟨M + 1, BoxARqp.isEnd hu hu' hM hq1⟩,
    fun kε hend => ?_⟩
  · have hle : C⁻¹ ≤ κF⁻¹ :=
      inv_anti₀ (by linarith) ((le_max_left _ _).trans (le_max_left _ _))
    obtain ⟨h0, h1'⟩ := hCε hC1
    exact ⟨h0.trans hle, h1'.trans hle⟩
  rw [(BoxARqp.isEnd_iff hu hu' hM hq1).1 hend, BoxARqp.seq,
    Constrained.HighOrderTargetSeq.funEvals_oneStep,
    Constrained.HighOrderTargetSeq.derivEvals_oneStep]
  obtain ⟨hF, hD⟩ := BoxARqp.order_le_pow (p := p) hq1 hq2 hpq (show 1 ≤ N by omega)
  rw [← hu_def] at hF hD
  have hF0 : 0 ≤ tpqpOrderF (Optimization.arqpPiOf False p) q (BoxARqp.tol u) :=
    zero_le_one.trans (one_le_tpqpOrderF (BoxARqp.tol_pos hu 0) (BoxARqp.tol_le_one hu hu7 0))
  have hD0 : 0 ≤ tpqpOrderD (Optimization.arqpPiOf False p) q (BoxARqp.tol u) :=
      Optimization.le_finMax_left
  have hκF : κF * tpqpOrderF (Optimization.arqpPiOf False p) q (BoxARqp.tol u) ≤
      C * (128 * (N : ℝ) ^ 14) :=
    (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) hF0).trans
      (mul_le_mul_of_nonneg_left hF (by linarith))
  have hκD : κD * tpqpOrderD (Optimization.arqpPiOf False p) q (BoxARqp.tol u) ≤
      C * (128 * (N : ℝ) ^ 14) :=
    (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_left _ _)) hD0).trans
      (mul_le_mul_of_nonneg_left hD (by linarith))
  have hε01 : (BoxARqp.tol u 0 * BoxARqp.tol u 1)⁻¹ ≤ 128 * ((M + 1 + 1 : ℕ) : ℝ) := by
    rw [BoxARqp.tol_zero, BoxARqp.tol_one]
    have h3 : 3 * u ^ 3 / 4 ≤ (u ^ 2 / 2 + u ^ 3 / 2) * (3 * u / 2) := by nlinarith [pow_pos hu 4]
    have h3' : 0 < 3 * u ^ 3 / 4 := by positivity
    calc ((u ^ 2 / 2 + u ^ 3 / 2) * (3 * u / 2))⁻¹ ≤ (3 * u ^ 3 / 4)⁻¹ := inv_anti₀ h3' h3
      _ = 4 / 3 * (64 * M) := by
          have : u ^ 3 ≠ 0 := by positivity
          field_simp
          nlinarith [hMe]
      _ ≤ 128 * ((M + 1 + 1 : ℕ) : ℝ) := by push_cast; nlinarith
  push_cast at hε01 ⊢
  rw [hMR] at hε01 ⊢
  refine ⟨by linarith, by linarith, hε01⟩

/-- **The printed Theorem 14.3.9 for INNER = ARqp-SC is false when `q ∈ {1, 2}`, `p ≥ q + 3`**,
for runs whose Step 2.1 of Algorithm 14.1.2 re-initialises `μ ∈ (0, 1]` at every Step 2 (the
reading the book allows; with `μ` bounded below away from `0` the question is open): on the
problem of `theorem_14_3_9_arqp_counterexample`, which satisfies its assumptions, no constants
`κ_F`, `κ_D` bound the evaluation counts of every TPqp-GC run with INNER = ARqp-SC
(`IsTPqpGCARqpSCRun`, `θ = β = β₁ = 1/2`, `x₀ = (0, 0)`) by
`κ_F max[ε₀^{-1}, max_j ε₀^{1-π_j} ε_j^{-π_j}]` and `κ_D max_j ε₀^{1-π_j} ε_j^{-π_j}`,
`π_j = j(p+1)/p` (the conclusion of `theorem_14_3_9_arqp`, proved there for `q = p`, and of the
corrected `theorem_14_3_9_arqp_corrected` without its extra term `∑_j (ε₀ ε_j)^{-j}`). -/
theorem theorem_14_3_9_arqp_printed_false {p q : ℕ} (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (hpq : q + 3 ≤ p) :
    ∃ (f : ℝ² → ℝ) (c : ℝ² → ℝ¹) (X : Set ℝ²) (Lc Bc Lf Bf : ℕ → ℝ) (P : ARqpCParams),
      AssumptionXCNe X ∧ Convex ℝ X ∧ AssumptionCD1pLBX c X (ball 0 2) p Lc Bc ∧
      AssumptionD1pLBX f X (ball 0 2) p Lf Bf ∧ Chapter07.AssumptionBFb f c X 1 (-2) 2 ∧
      P.θ < P.ς ∧
      ¬ ∃ κF κD : ℝ, ∀ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) → ε 0 ≤ 1 →
        ∀ (xP : ℕ → ℝ²) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq 2) (nF₁ nD₁ : ℕ → ℕ),
          IsTPqpGCARqpSCRun f c X p q P (1 / 2) (1 / 2) (1 / 2) ε (pt 0 0) xP δP k₁ D nF₁ nD₁ →
          (1 / 2 * ε 0 < ‖c (xP k₁)‖ →
            ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤
              κF * tpqpOrderF (Optimization.arqpPiOf False p) q ε ∧
            ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤
              κD * tpqpOrderD (Optimization.arqpPiOf False p) q ε) ∧
          (‖c (xP k₁)‖ ≤ 1 / 2 * ε 0 → ∃ kε, D.IsEnd f c X q (1 / 2) ε kε ∧
            ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) + D.funEvals kε ≤
              κF * tpqpOrderF (Optimization.arqpPiOf False p) q ε ∧
            ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) + D.derivEvals kε ≤
              κD * tpqpOrderD (Optimization.arqpPiOf False p) q ε) := by
  obtain ⟨f, c, X, Lc, Bc, Lf, Bf, P, hX, hXc, hc, hf, hB, hθς, hrun⟩ :=
    theorem_14_3_9_arqp_counterexample hq1 hq2 hpq
  refine ⟨f, c, X, Lc, Bc, Lf, Bf, P, hX, hXc, hc, hf, hB, hθς, ?_⟩
  rintro ⟨κF, κD, hκ⟩
  obtain ⟨ε, xP, δP, D, hε, -, hR, hc0, -, hcount⟩ := hrun (1 / 2) κF κD (by norm_num) (by norm_num)
  obtain ⟨kε, hend, hF, -⟩ := (hκ ε (fun j _ => hε j) (hε 0).2 xP δP 0 D (fun _ => 0) (fun _ => 0)
    (hR _ _)).2 hc0
  have := (hcount kε hend).1
  simp only [Finset.Icc_eq_empty_of_lt one_pos, Finset.sum_empty, zero_add] at hF
  linarith

end ARqpSCSharp


/-! ## INNER = TRq-SC -/


section TRqSC

/-! ### Phase 2 with TRq-SC calls

The INNER contract of every run whose Phase-2 calls are TRq-SC runs, the tolerances of the calls,
and the existence of such runs are the backbone results
`Constrained.IsHighOrderTargetRun.isInnerTestContract_of_isTRqCalls`,
`Constrained.IsHighOrderTargetRun.call_tol` and
`Constrained.exists_isHighOrderTargetRun_isTRqCalls`
(`Numlib.Optimization.Constrained.TwoPhase.HighOrder.TRqCalls`). -/

/-- **The INNER calls of Phase 2 of TPqp-GC are TRq-SC runs** ([cartis2022evaluation],
Algorithm 14.3.2, Step 1: `INNER(μ(·, t_k), X, q, x_k, β ‖r(x_k, t_k)‖ ε)` with INNER of
trust-region type): for every outer iteration `k ≥ 1` reached, the iterates, successful iterations
and output radii `δ_{k+1}` of the `k`-th call are those of a TRq-SC run on `μ(·, t_k)` with
threshold `ϑ` and tolerances `β ‖r(x_k, t_k)‖ ε_j` (`Optimization.IsTRqCallOut`), cut at any
iteration (by any test of (14.3.32)); `Constrained.HighOrderTargetSeq.IsTRqCalls`. -/
abbrev IsTRqSCPhase2Calls (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (X : Set ℝⁿ) (q : ℕ)
    (P : Optimization.TRqParams) (ϑ θ β : ℝ) (ε : ℕ → ℝ) (D : TPqpSeq n) : Prop :=
  D.IsTRqCalls f c X q P ϑ θ β ε

/-! ### The Phase-1 INNER calls realized by TRq-SC -/

section Phase1Call

variable {q : ℕ} {ε : ℕ → ℝ}

/-- `κ gap/ε_min^{q+1} ≤ κ gap max_j ε_j^{-(q+1)}` (`innerEvalBound` with the exponents
`π_j = q + 1`), for `κ, gap ≥ 0` and `ε ∈ (0, 1]^q`, `q ≥ 1`. -/
theorem le_innerEvalBound_succ {κ gap : ℝ} (hκ : 0 ≤ κ) (hgap : 0 ≤ gap) (hq : 1 ≤ q)
    (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1) :
    κ * gap / Optimization.finMin 1 ε q ^ (q + 1) ≤
      innerEvalBound κ (fun _ => (q : ℝ) + 1) q gap ε := by
  obtain ⟨l, hl, hmin⟩ := Optimization.exists_finMin_eq hq fun j hj => (hε j hj).2
  unfold innerEvalBound
  rw [hmin, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hκ hgap)
  have e : (ε l ^ (q + 1))⁻¹ = ε l ^ (-((q : ℝ) + 1)) := by
    rw [Real.rpow_neg (hε l hl).1.le, show ((q : ℝ) + 1) = ((q + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  rw [e]
  exact le_ciSup (f := fun j : Finset.Icc 1 q => ε j ^ (-((q : ℝ) + 1)))
    (Set.finite_range _).bddAbove ⟨l, hl⟩

end Phase1Call

/-! ### TPqp-GC runs with a trust-region INNER in both phases -/

section Run

/-- **A run of TPqp-GC with INNER = TRq-SC in both phases** ([cartis2022evaluation],
Algorithm 14.3.2 with INNER of trust-region type): a run (`algorithm_14_3_2`) whose Phase-1 INNER
calls (14.3.23) `x_k = INNER(ν, X, q, x_{k-1}, β₁ ‖c(x_{k-1})‖ (θε₀, ε_1, …, ε_q))` are TRq-SC
runs on `ν` with threshold `ϑ` that use `nF₁ k` evaluations of `c` and `nD₁ k` of its derivatives
(`Optimization.IsTRqOutputCost`), and whose Phase-2 INNER calls (if Phase 2 is entered) are
TRq-SC runs on `μ(·, t_k)` with threshold `ϑ` and their output radii, cut at any iteration
(`IsTRqSCPhase2Calls`). -/
structure IsTPqpGCTRqSCRun (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (X : Set ℝⁿ) (q : ℕ)
    (P : Optimization.TRqParams) (ϑ θ β₁ β : ℝ) (ε : ℕ → ℝ) (x₀ : ℝⁿ) (xP : ℕ → ℝⁿ)
    (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq n) (nF₁ nD₁ : ℕ → ℕ) : Prop where
  /-- The TPqp-GC run. -/
  run : algorithm_14_3_2 f c X q θ β₁ β ε x₀ xP δP k₁ D
  /-- The Phase-1 INNER calls are TRq-SC runs with their evaluation counts. -/
  phase1 : ∀ k, 1 ≤ k → k ≤ k₁ → Optimization.IsTRqOutputCost (phi2 c) X P q
    (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j) ϑ (xP (k - 1)) (xP k) (δP k) (nF₁ k)
      (nD₁ k)
  /-- The Phase-2 INNER calls are TRq-SC runs with their output radii. -/
  phase2 : ‖c (xP k₁)‖ ≤ θ * ε 0 → IsTRqSCPhase2Calls f c X q P ϑ θ β ε D

end Run

/-! ### Theorem 14.3.9 with a trust-region INNER -/

section Theorem1439

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {q : ℕ}

/-- c.D1qLB.X gives, through Lemma 14.3.6 (i), anchored f.D1qL for `ν` on `𝓛_ν(x₀)` with the
constants `L^A_j + L^B_j ‖c(x₀)‖` and the bound `max(1, max_j (B^A_j + B^B_j ‖c(x₀)‖))` on the
derivatives of orders `1, …, q` there. -/
theorem exists_nu_trq {X₀ : Set ℝⁿ} {Lc Bc : ℕ → ℝ} (hc : AssumptionCD1pLBX c X X₀ q Lc Bc) :
    ∃ LA LB BA BB : ℕ → ℝ, ∀ x₀ : ℝⁿ,
      LipschitzDerivsAnchored (phi2 c) X₀ (nuSublevel c X x₀) 1 q
        (fun j => LA j + LB j * ‖c x₀‖) ∧
      ∀ y ∈ nuSublevel c X x₀, Optimization.finMax 0
        (fun i => ‖iteratedFDeriv ℝ i (phi2 c) y‖) q ≤
          Optimization.finMax 1 (fun j => BA j + BB j * ‖c x₀‖) q := by
  obtain ⟨LA, LB, BA, BB, h1, hν⟩ := lemma_14_3_6_i hc
  refine ⟨LA, LB, BA, BB, fun x₀ => ⟨⟨hc.isOpen, hc.convex, fun x hx => hc.subset hx.1,
    fun y hy => (hν x₀).1.contDiffAt (hc.isOpen.mem_nhds hy),
    fun j hj => ((hν x₀).2 j hj).1⟩, fun y hy => ?_⟩⟩
  exact Optimization.finMax_le (zero_le_one.trans Optimization.le_finMax_left) fun i hi =>
    (((hν x₀).2 i hi).2 y hy).trans
      (Optimization.le_finMax (u := fun j => BA j + BB j * ‖c x₀‖) hi)

/-- c.D1qLB.X and f.D1qLB.X give, through Lemma 14.3.6 (ii), anchored f.D1qL for every `μ(·, t)`
on `𝓛_μ(t)` with constants `L_μ` and the bound `max(1, max_j B_{μ,j})` on the derivatives of
orders `1, …, q` there, independent of `t`. -/
theorem exists_mu_trq {X₀ : Set ℝⁿ} {Lc Bc Lf Bf : ℕ → ℝ}
    (hc : AssumptionCD1pLBX c X X₀ q Lc Bc) (hf : AssumptionD1pLBX f X X₀ q Lf Bf) :
    ∃ Lμ Bμ : ℕ → ℝ, ∀ t : ℝ,
      LipschitzDerivsAnchored (Constrained.targetMerit f c t) X₀ (muSublevel f c X t) 1 q Lμ ∧
      ∀ y ∈ muSublevel f c X t, Optimization.finMax 0
        (fun i => ‖iteratedFDeriv ℝ i (Constrained.targetMerit f c t) y‖) q ≤
          Optimization.finMax 1 Bμ q := by
  obtain ⟨Lμ, Bμ, h2, hμ⟩ := lemma_14_3_6_ii hc hf
  refine ⟨Lμ, Bμ, fun t => ⟨⟨hc.isOpen, hc.convex, fun x hx => hc.subset hx.1,
    fun y hy => (hμ t).1.contDiffAt (hc.isOpen.mem_nhds hy),
    fun j hj => ((hμ t).2 j hj).1⟩, fun y hy => ?_⟩⟩
  exact Optimization.finMax_le (zero_le_one.trans Optimization.le_finMax_left) fun i hi =>
    (((hμ t).2 i hi).2 y hy).trans (Optimization.le_finMax (u := Bμ) hi)

/-- The number of Phase-1 iterations of TPqp-GC is at most `1 + ‖c(x₀)‖/(θ |log β₁|) ε₀^{-1}`
(Theorem 14.3.3, `Real.natCeil_log_div_log_le`). -/
theorem phase1_iter_le {θ β₁ β : ℝ} {ε : ℕ → ℝ} {x₀ : ℝⁿ} {xP : ℕ → ℝⁿ} {δP : ℕ → ℕ → ℝ}
    {k₁ : ℕ} {D : TPqpSeq n} (h : algorithm_14_3_2 f c X q θ β₁ β ε x₀ xP δP k₁ D)
    (hθ0 : 0 < θ) : (k₁ : ℝ) ≤ 1 + ‖c x₀‖ / (θ * |Real.log β₁|) * (ε 0)⁻¹ := by
  have hε₀ : 0 < ε 0 := by
    have := h.phase1.ε_pos 0 (by simp)
    rw [phase1Tol_zero] at this
    exact pos_of_mul_pos_right this hθ0.le
  obtain ⟨⟨kmax, hhit, hkmax, -⟩, -⟩ := theorem_14_3_3 h.phase1
  rw [hhit.unique h.phase1_end, phase1Tol_zero, h.start] at hkmax
  have h1 : (k₁ : ℝ) ≤ 1 + ‖c x₀‖ / (θ * ε 0 * |Real.log β₁|) :=
    (Nat.cast_le.2 hkmax).trans
      (Real.natCeil_log_div_log_le (mul_pos hθ0 hε₀) (norm_nonneg _)
        h.phase1.β_pos h.phase1.β_lt_one)
  have h2 : ‖c x₀‖ / (θ * ε 0 * |Real.log β₁|) = ‖c x₀‖ / (θ * |Real.log β₁|) * (ε 0)⁻¹ := by
    field_simp
  rwa [h2] at h1

/-- **The Phase-1 cost contract of TRq-SC calls** ([cartis2022evaluation], (14.3.20)–(14.3.21)
in the additive form of `lemma_14_3_7_add`, with the exponents `π_j = q + 1`): under anchored
f.D1qL for `ν` on `𝓛_ν(x₀)` (constants `L_ν`, derivatives bounded by `M_ν > 0`),
`ϑ ≤ 1` and `β₁ ‖c(x₀)‖ ≤ ϑ`, the `k`-th Phase-1 call of a TPqp-GC run with TRq-SC calls uses at
most `κ^A ν(x_{k-1}) max_j ε'_j^{-(q+1)} + κ^B (|log(β₁θ)| + |log(ε₀ ε_min)|) + κ^C` evaluations
of `c` and `κ^S ν(x_{k-1}) max_j ε'_j^{-(q+1)} + 1` derivative evaluations
(`Optimization.IsTRqOutputCost.cost_le`, `‖c(x_{k-1})‖ > θε₀`). -/
theorem phase1_call_cost_trq {P : Optimization.TRqParams} {ϑ θ β₁ β : ℝ} {ε : ℕ → ℝ}
    {x₀ : ℝⁿ} {xP : ℕ → ℝⁿ} {δP : ℕ → ℕ → ℝ} {k₁ : ℕ} {D : TPqpSeq n} {nF₁ nD₁ : ℕ → ℕ}
    (hR : IsTPqpGCTRqSCRun f c X q P ϑ θ β₁ β ε x₀ xP δP k₁ D nF₁ nD₁) (hq : 1 ≤ q)
    {X₀ : Set ℝⁿ} {Lν : ℕ → ℝ} {Mν : ℝ}
    (hν : LipschitzDerivsAnchored (phi2 c) X₀ (nuSublevel c X x₀) 1 q Lν)
    (hνM : ∀ y ∈ nuSublevel c X x₀,
      Optimization.finMax 0 (fun i => ‖iteratedFDeriv ℝ i (phi2 c) y‖) q ≤ Mν) (hMν0 : 0 < Mν)
    (hXX₀ : X ⊆ X₀) (hϑ1 : ϑ ≤ 1) (hβ₁ϑ : β₁ * ‖c x₀‖ ≤ ϑ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) :
    ∀ k ∈ Finset.Icc 1 k₁,
      (nF₁ k : ℝ) ≤ innerEvalBound (Optimization.trqCallKappaA P Lν ϑ Mν q)
        (fun _ => (q : ℝ) + 1) q
        (phi2 c (xP (k - 1))) (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j) +
          (Optimization.kappaBTRq P * (|Real.log (β₁ * θ)| + Constrained.tolLogTerm q ε) +
            Optimization.trqCallKappaC P Lν ϑ Mν q) ∧
      (nD₁ k : ℝ) ≤ innerEvalBound (Optimization.trqCallKappaS P Lν ϑ Mν q)
        (fun _ => (q : ℝ) + 1) q
        (phi2 c (xP (k - 1))) (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j) + 1 := by
  have h := hR.run
  have hβ₁0 := h.phase1.β_pos
  have hβ₁1 := h.phase1.β_lt_one
  intro k hk
  obtain ⟨hk1, hkk⟩ := Finset.mem_Icc.1 hk
  have hmem : xP (k - 1) ∈ X := by
    rcases Nat.eq_zero_or_pos (k - 1) with h0 | hpos
    · rw [h0]; exact h.phase1.mem_zero
    · exact h.phase1.mem (k - 1) hpos fun i hi => h.phase1_end.2 i (by omega)
  have hck : ‖c (xP (k - 1))‖ ≤ ‖c x₀‖ := by
    have := h.phase1.norm_le_pow_mul (Nat.zero_le (k - 1)) fun l hl =>
      h.phase1_end.2 l (by omega)
    rw [h.start] at this
    exact this.trans (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hβ₁0.le hβ₁1.le))
  have hlo : θ * ε 0 < ‖c (xP (k - 1))‖ := by
    have := h.phase1_end.2 (k - 1) (by omega)
    simp only [lenStop, not_or, not_le, phase1Tol_zero] at this
    exact this.1
  have hε'j : ∀ j ∈ Finset.Icc 1 q,
      β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j = β₁ * ‖c (xP (k - 1))‖ * ε j := fun j hj => by
    rw [phase1Tol_of_ne θ ε (by have := (Finset.mem_Icc.1 hj).1; omega)]
  have hcost := Constrained.IsTRqOutputCost.cost_le_halfSqNorm (hR.phase1 k hk1 hkk) hq hν hνM
    hMν0 hXX₀ hϑ1 hβ₁ϑ hθ0 hθ1 hβ₁0 hβ₁1 hε hmem hck hlo hε'j
  have hε'I : ∀ j ∈ Finset.Icc 1 q, 0 < β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j ∧
      β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j ≤ 1 := fun j hj => by
    have hεj := hε j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
    have hr0 : 0 < ‖c (xP (k - 1))‖ := (mul_pos hθ0 (hε 0 (by simp)).1).trans hlo
    have hrx : β₁ * ‖c (xP (k - 1))‖ ≤ 1 := hβ₁ϑ.trans' (mul_le_mul_of_nonneg_left hck hβ₁0.le)
      |>.trans hϑ1
    rw [hε'j j hj]
    exact ⟨by have := hεj.1; positivity, by nlinarith [hεj.1, hεj.2]⟩
  have hr0 : 0 < ‖c (xP (k - 1))‖ := (mul_pos hθ0 (hε 0 (by simp)).1).trans hlo
  have hϑ0 : 0 < ϑ := lt_of_lt_of_le (mul_pos hβ₁0 (hr0.trans_le hck)) hβ₁ϑ
  have hν0 : 0 ≤ phi2 c (xP (k - 1)) := Constrained.halfSqNorm_nonneg c _
  refine ⟨hcost.1.trans ?_, hcost.2.trans ?_⟩
  · have := le_innerEvalBound_succ
      (Optimization.trqCallKappaA_nonneg (P := P) (L := Lν) (q := q) hϑ0 hMν0) hν0 hq hε'I
    simp only [phi2] at this ⊢
    linarith
  · have := le_innerEvalBound_succ
      (Optimization.trqCallKappaS_nonneg (P := P) (L := Lν) (q := q) hϑ0 hMν0) hν0 hq hε'I
    simp only [phi2] at this ⊢
    linarith

/-- **Theorem 14.3.9** of [cartis2022evaluation] (complexity of TPqp-GC) **for every run with a
trust-region INNER** (TRq-SC, Algorithm 12.2.1 with a feasible set, threshold `ϑ`, in both
phases), under c.D1qLB.X and f.D1qLB.X (on an open convex `X₀ ⊇ X`) and f.B.Fb on `ℱ_{β_F}`,
with `q ≥ 1`. For TRq parameters `P`, `ϑ ≤ 1`, `θ ∈ (0, 1)`, `0 < β ≤ ϑ`, `β₁` and a starting
point `x₀` with `β₁ ‖c(x₀)‖ ≤ ϑ`, there are constants `κ_F, κ_L, κ_D ≥ 0` such that for all
tolerances `ε ∈ (0, 1]^{q+1}` with `ε₀ ≤ β_F` and every TPqp-GC run whose INNER calls are TRq-SC
runs (`IsTPqpGCTRqSCRun`; Phase-2 calls may be cut by any test of (14.3.32); such runs exist,
`exists_isTPqpGCTRqSCRun`):
* if Phase 1 ends with `‖c(x₁)‖ > θε₀`, it uses at most `(κ_F + κ_L Λ) O_F` evaluations of `c`
  and `κ_D O_D` derivative evaluations;
* otherwise Phase 2 terminates at some `k_ε`, and both phases together use at most
  `(κ_F + κ_L Λ) O_F` evaluations of `(f, c)` and `κ_D O_D` derivative evaluations,

where `π_j = q + 1` for every `j` (the exponent of Lemma 12.2.4, the TRq-SC row of Lemma 14.2.2 as
proved in `Chapter14.Section02`), `O_F = max[ε₀^{-1}, max_j ε₀^{-q} ε_j^{-(q+1)}]`
(`tpqpOrderF`), `O_D = max_j ε₀^{-q} ε_j^{-(q+1)}` (`tpqpOrderD`) and
`Λ = |log(ε₀ ε_min)|` (`Constrained.tolLogTerm`).

Deviations from the printed statement: (14.2.12) prints `π_j = j + 1` for TRq-SC; the decrease
proved for TRq (Lemma 12.2.4) is `κ ε_min^{q+1}`, which gives `π_j = q + 1`, the order of the TRq-SC
row of the book's Theorem 14.2.4 (the row `j + 1` is false per iteration for `q = 2` with `κ_decr`
depending only on the algorithm parameters and the f.D1qLaB.X constants,
`lemma_14_2_2_trq_printed_false_uniform`, and for whole runs for every `q ≥ 2`,
`theorem_14_3_9_trq_printed_false`); the two agree for `q = 1`
(`theorem_14_3_9_trq_one`). The function-evaluation bound carries the factor `1 + Λ`,
which is needed for `q = 1` (`theorem_14_3_9_trq_log_necessary`): every INNER call restarts from the
radius `Δ₀`, and its unsuccessful iterations are bounded only by `log(Δ₀/(κ_ρ ε'_min))` (Lemma 2.3.1
with Lemma 12.2.3), `ε'_min ≥ βθ ε₀ ε_min`, which the counting of Lemma 14.3.8 multiplies by the
number of outer iterations; the derivative bound has no such factor. The book's f.D1qLB.Fb is not
defined in the book; f.D1qLB.X (f.D1pLB.X with `q`) is used.
-/
theorem theorem_14_3_9_trq (hq : 1 ≤ q) {X₀ : Set ℝⁿ} {Lc Bc Lf Bf : ℕ → ℝ}
    (hc : AssumptionCD1pLBX c X X₀ q Lc Bc) (hf : AssumptionD1pLBX f X X₀ q Lf Bf)
    {βF flow fup : ℝ} (hB : Chapter07.AssumptionBFb f c X βF flow fup)
    (P : Optimization.TRqParams) {ϑ θ β β₁ : ℝ} (hϑ1 : ϑ ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hβ0 : 0 < β) (hβϑ : β ≤ ϑ) (x₀ : ℝⁿ) (hβ₁ϑ : β₁ * ‖c x₀‖ ≤ ϑ) :
    ∃ κF κL κD : ℝ, 0 ≤ κF ∧ 0 ≤ κL ∧ 0 ≤ κD ∧
      ∀ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) → ε 0 ≤ βF →
      ∀ (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq n) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCTRqSCRun f c X q P ϑ θ β₁ β ε x₀ xP δP k₁ D nF₁ nD₁ →
        (θ * ε 0 < ‖c (xP k₁)‖ →
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤
            (κF + κL * Constrained.tolLogTerm q ε) * tpqpOrderF (fun _ => (q : ℝ) + 1) q ε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤ κD * tpqpOrderD (fun _ => (q : ℝ) + 1) q ε) ∧
        (‖c (xP k₁)‖ ≤ θ * ε 0 → ∃ kε, D.IsEnd f c X q θ ε kε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) + D.funEvals kε ≤
            (κF + κL * Constrained.tolLogTerm q ε) * tpqpOrderF (fun _ => (q : ℝ) + 1) q ε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) + D.derivEvals kε ≤
            κD * tpqpOrderD (fun _ => (q : ℝ) + 1) q ε) := by
  have hϑ0 : 0 < ϑ := hβ0.trans_le hβϑ
  obtain ⟨LA, LB, BA, BB, hν⟩ := exists_nu_trq hc
  obtain ⟨Lμ, Bμ, hμ⟩ := exists_mu_trq hc hf
  have hMν0 : 0 < Optimization.finMax 1 (fun j => BA j + BB j * ‖c x₀‖) q :=
    Optimization.finMax_one_pos
  have hMμ0 : 0 < Optimization.finMax 1 Bμ q := Optimization.finMax_one_pos
  have hg : 0 < |Real.log P.γ₂| := abs_pos.2 (Real.log_neg P.γ₂_pos P.γ₂_lt_one).ne
  -- Phase 2 constants
  have hκ : 0 < Optimization.trqCallKappaDecr P Lμ ϑ (Optimization.finMax 1 Bμ q) q :=
    Optimization.trqCallKappaDecr_pos hϑ0 hMμ0
  have hκρ : 0 < Optimization.trqCallKappaRad P Lμ ϑ (Optimization.finMax 1 Bμ q) q * β * θ := by
    have := Optimization.trqCallKappaRad_pos (P := P) (L := Lμ) (q := q) hϑ0 hMμ0
    positivity
  obtain ⟨CF, CU, CD, hCF, hCU, hCD, hord⟩ :=
    Constrained.IsHighOrderTargetRun.exists_const_order_of_innerTest_unc (f := f) (c := c)
      (X := X) (θ := θ) (β := β) hq (πmax := (q : ℝ) + 1) hκ
      (zero_le_one.trans Optimization.one_le_trqKappaUns) hκρ
      (Optimization.finMax_one_pos (L := Bf))
      (abs_nonneg (fup - flow + 1)) zero_le_one hθ0 hθ1 hβ0
  obtain ⟨U0, hU0⟩ : ∃ x,
      x = Constrained.trqCallKappaUnc0 P Lμ ϑ (Optimization.finMax 1 Bμ q) q β θ := ⟨_, rfl⟩
  have hU00 : 0 ≤ U0 := hU0 ▸ Constrained.trqCallKappaUnc0_nonneg β θ
  -- Phase 1 constants
  obtain ⟨κA, hκA⟩ : ∃ x, x = Optimization.trqCallKappaA P (fun j => LA j + LB j * ‖c x₀‖) ϑ
      (Optimization.finMax 1 (fun j => BA j + BB j * ‖c x₀‖) q) q := ⟨_, rfl⟩
  obtain ⟨κS, hκS⟩ : ∃ x, x = Optimization.trqCallKappaS P (fun j => LA j + LB j * ‖c x₀‖) ϑ
      (Optimization.finMax 1 (fun j => BA j + BB j * ‖c x₀‖) q) q := ⟨_, rfl⟩
  obtain ⟨κC, hκC⟩ : ∃ x, x = Optimization.trqCallKappaC P (fun j => LA j + LB j * ‖c x₀‖) ϑ
      (Optimization.finMax 1 (fun j => BA j + BB j * ‖c x₀‖) q) q := ⟨_, rfl⟩
  obtain ⟨κB, hκB⟩ : ∃ x, x = Optimization.kappaBTRq P := ⟨_, rfl⟩
  have hκA0 : 0 ≤ κA := hκA ▸ Optimization.trqCallKappaA_nonneg hϑ0 hMν0
  have hκS0 : 0 ≤ κS := hκS ▸ Optimization.trqCallKappaS_nonneg hϑ0 hMν0
  have hκC0 : 0 ≤ κC := hκC ▸ zero_le_one.trans Optimization.one_le_trqCallKappaC
  have hκB0 : 0 ≤ κB := by rw [hκB]; exact Optimization.kappaBTRq_nonneg P
  obtain ⟨W, hW⟩ : ∃ x, x = ∑ j ∈ Finset.Icc 1 q, |β₁ ^ (1 - 2 * ((q : ℝ) + 1)) /
      (β₁ ^ (1 - ((q : ℝ) + 1)) - 1) * θ ^ (1 - ((q : ℝ) + 1))| := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := hW ▸ Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨c₁, hc₁⟩ : ∃ x, x = 1 + ‖c x₀‖ / (θ * |Real.log β₁|) := ⟨_, rfl⟩
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; positivity
  obtain ⟨lb, hlb⟩ : ∃ x, x = |Real.log (β₁ * θ)| := ⟨_, rfl⟩
  have hlb0 : 0 ≤ lb := hlb ▸ abs_nonneg _
  obtain ⟨r₀, hr₀⟩ : ∃ x, x = ‖c x₀‖ := ⟨_, rfl⟩
  have hr₀0 : 0 ≤ r₀ := hr₀ ▸ norm_nonneg _
  obtain ⟨g, hg'⟩ : ∃ x, x = |Real.log P.γ₂| := ⟨_, rfl⟩
  rw [← hg'] at hg
  refine ⟨1 / 2 * κA * r₀ * W + c₁ * (κB * lb + κC) + CF + CU * U0,
    c₁ * κB + CU / g, 1 / 2 * κS * r₀ * W + c₁ + CD,
    by positivity, by positivity, by positivity,
    fun ε hε hεβ xP δP k₁ D nF₁ nD₁ hR => ?_⟩
  have h := hR.run
  have hε₀ := hε 0 (by simp)
  have hεI : ∀ l ∈ Finset.Icc 1 q, 0 < ε l ∧ ε l ≤ 1 := fun l hl =>
    hε l (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hl).2))
  have hεm0 : 0 < Optimization.finMin 1 ε q := Optimization.finMin_pos one_pos fun j hj => (hεI j
      hj).1
  have hεm1 : Optimization.finMin 1 ε q ≤ 1 := Optimization.finMin_le_left
  obtain ⟨Λ, hΛ⟩ : ∃ x, x = Constrained.tolLogTerm q ε := ⟨_, rfl⟩
  have hΛ0 : 0 ≤ Λ := hΛ ▸ abs_nonneg _
  obtain ⟨O, hO⟩ : ∃ x, x = tpqpOrderF (fun _ => (q : ℝ) + 1) q ε := ⟨_, rfl⟩
  obtain ⟨OD, hOD⟩ : ∃ x, x = tpqpOrderD (fun _ => (q : ℝ) + 1) q ε := ⟨_, rfl⟩
  rw [← hΛ, ← hO, ← hOD]
  have hOT : ∀ j ∈ Finset.Icc 1 q, ε 0 ^ (1 - ((q : ℝ) + 1)) * ε j ^ (-((q : ℝ) + 1)) ≤ O :=
    fun j hj => by rw [hO]; exact term_le_tpqpOrderF (π := fun _ => (q : ℝ) + 1) hj
  have hO0 : (ε 0)⁻¹ ≤ O := by rw [hO]; exact inv_le_tpqpOrderF
  have hO1 : 1 ≤ O := by rw [hO]; exact one_le_tpqpOrderF hε₀.1 hε₀.2
  have hOnn : 0 ≤ O := zero_le_one.trans hO1
  have h1q : 1 ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, hq⟩
  have hFD : O ≤ OD := by
    rw [hO, hOD]
    refine tpqpOrderF_le_tpqpOrderD hε h1q ?_
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  -- Phase 1: the number of iterations
  have hk₁ : (k₁ : ℝ) ≤ c₁ * O := by
    have h1 := phase1_iter_le h hθ0
    rw [← hr₀] at h1
    have h3 : 0 ≤ r₀ / (θ * |Real.log β₁|) := by positivity
    have h4 : r₀ / (θ * |Real.log β₁|) * (ε 0)⁻¹ ≤ r₀ / (θ * |Real.log β₁|) * O :=
      mul_le_mul_of_nonneg_left hO0 h3
    rw [hc₁, ← hr₀]
    nlinarith
  -- Phase 1: the cost contract
  have hcost := phase1_call_cost_trq hR hq (hν x₀).1 (hν x₀).2 hMν0 hc.subset hϑ1 hβ₁ϑ hθ0 hθ1 hε
  rw [← hκA, ← hκS, ← hκC, ← hκB, ← hlb, ← hΛ] at hcost
  have hπ1 : ∀ l ∈ Finset.Icc 1 q, 1 < (fun _ : ℕ => (q : ℝ) + 1) l := fun l _ => by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    change 1 < (q : ℝ) + 1
    linarith
  have hF1 := (lemma_14_3_7_add h hθ0 hπ1 hκA0 fun k hk => (hcost k hk).1).trans
    (add_le_add (Constrained.mul_sum_le_mul_sum_abs_mul (π := fun _ : ℕ => (q : ℝ) + 1)
      hκA0 (norm_nonneg _) (fun j hj => (hε j hj).1) hOT) le_rfl)
  have hD1 := (lemma_14_3_7_add h hθ0 hπ1 hκS0 fun k hk => (hcost k hk).2).trans
    (add_le_add (Constrained.mul_sum_le_mul_sum_abs_mul (π := fun _ : ℕ => (q : ℝ) + 1)
      hκS0 (norm_nonneg _) (fun j hj => (hε j hj).1) hOT) le_rfl)
  rw [← hW, ← hr₀] at hF1 hD1
  have ha0 : 0 ≤ κB * (lb + Λ) + κC := by positivity
  have hF1' : ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤
      (1 / 2 * κA * r₀ * W + c₁ * (κB * lb + κC) + c₁ * κB * Λ) * O := by
    have := mul_le_mul_of_nonneg_right hk₁ ha0
    linarith only [hF1, this]
  have hD1' : ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤ (1 / 2 * κS * r₀ * W + c₁) * O := by
    linarith only [hD1, hk₁]
  have hP1D : 0 ≤ 1 / 2 * κS * r₀ * W + c₁ := by positivity
  have hextra : 0 ≤ (CF + CU * U0) * O + CU / g * Λ * O := by positivity
  have hD1'' : ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤ (1 / 2 * κS * r₀ * W + c₁) * OD :=
    hD1'.trans (mul_le_mul_of_nonneg_left hFD hP1D)
  refine ⟨fun _ => ⟨by linarith only [hF1', hextra],
    by linarith only [hD1'', mul_nonneg hCD (hOnn.trans hFD)]⟩, fun hc1 => ?_⟩
  -- Phase 2
  have h2 := h.phase2 hc1
  have hin := h2.isInnerTestContract_of_isTRqCalls (hR.phase2 hc1) hq (hμ := fun t => (hμ t).1)
    (fun t => (hμ t).2) hMμ0 hc.subset hβϑ hϑ1
  rw [← hU0, ← hg'] at hin
  obtain ⟨l, hl, hmin⟩ := Optimization.exists_finMin_eq hq fun j hj => (hεI j hj).2
  have hκunc : 0 ≤ U0 + Constrained.tolLogTerm q ε / g := by rw [← hΛ]; positivity
  obtain ⟨kε, hend, hF2, hD2⟩ := hord (ρ' := fun _ => ε 0 * Optimization.finMin 1 ε q) hκunc h2
    hin (fun _ _ => mul_pos hε₀.1 hεm0)
    (fun l _ => ⟨by positivity, le_rfl⟩) (hB.of_le hεβ) (le_abs_self _)
    (fun _ hy => hf.contDiffAt_of_le le_rfl hy) (fun _ hy => hc.contDiffAt_of_le le_rfl hy)
    (fun _ hy _ => hf.norm_iteratedFDeriv_le_finMax le_rfl (hf.subset hy)) hO0 hOT
    (fun j hj => by
      rw [one_mul]
      refine (Constrained.inv_mul_mul_pow_le_rpow_succ hε₀.1 hε₀.2 hεm0 hεm1
        (Optimization.finMin_le hj) (Finset.mem_Icc.1 hj).1 (Finset.mem_Icc.1 hj).2).trans ?_
      have := hOT l hl
      rw [hmin]
      exact this)
  rw [← hΛ] at hF2
  have hD2' : (D.derivEvals kε : ℝ) ≤ CD * OD := hD2.trans (mul_le_mul_of_nonneg_left hFD hCD)
  refine ⟨kε, hend, ?_, by linarith only [hD1'', hD2']⟩
  have e : (CF + CU * (U0 + Λ / g)) * O = (CF + CU * U0) * O + CU / g * Λ * O := by ring
  linarith only [hF1', hF2, e]

/-- `tpqpOrderF` depends only on the exponents `π_j`, `j ∈ [1 : q]`. -/
theorem tpqpOrderF_congr {π π' : ℕ → ℝ} {ε : ℕ → ℝ} (h : ∀ j ∈ Finset.Icc 1 q, π j = π' j) :
    tpqpOrderF π q ε = tpqpOrderF π' q ε := by
  unfold tpqpOrderF
  exact Optimization.finMax_congr fun j hj => by simp only [h j hj]

/-- `tpqpOrderD` depends only on the exponents `π_j`, `j ∈ [1 : q]`. -/
theorem tpqpOrderD_congr {π π' : ℕ → ℝ} {ε : ℕ → ℝ} (h : ∀ j ∈ Finset.Icc 1 q, π j = π' j) :
    tpqpOrderD π q ε = tpqpOrderD π' q ε := by
  unfold tpqpOrderD
  exact Optimization.finMax_congr fun j hj => by simp only [h j hj]

/-- **Theorem 14.3.9** of [cartis2022evaluation] **with a trust-region INNER for `q = 1`, with the
printed exponent `π_1 = 2`** (the TRq-SC entry `j + 1` of (14.2.12)): `theorem_14_3_9_trq` with
`q = 1`, where the exponent `q + 1` of Lemma 12.2.4 is the printed `j + 1`. The derivative
evaluations are `O(max_j ε₀^{-j} ε_j^{-(j+1)}) = O(ε₀^{-1} ε_1^{-2})`, the printed order; the
evaluations of `(f, c)` are `O((1 + |log(ε₀ ε_1)|) max[ε₀^{-1}, ε₀^{-1} ε_1^{-2}])`, the printed
order up to the factor `1 + |log(ε₀ ε_1)|` from the restarts of the trust-region radius. That
factor is needed: the printed bound fails (`theorem_14_3_9_trq_log_necessary`). -/
theorem theorem_14_3_9_trq_one {X₀ : Set ℝⁿ} {Lc Bc Lf Bf : ℕ → ℝ}
    (hc : AssumptionCD1pLBX c X X₀ 1 Lc Bc) (hf : AssumptionD1pLBX f X X₀ 1 Lf Bf)
    {βF flow fup : ℝ} (hB : Chapter07.AssumptionBFb f c X βF flow fup)
    (P : Optimization.TRqParams) {ϑ θ β β₁ : ℝ} (hϑ1 : ϑ ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hβ0 : 0 < β) (hβϑ : β ≤ ϑ) (x₀ : ℝⁿ) (hβ₁ϑ : β₁ * ‖c x₀‖ ≤ ϑ) :
    ∃ κF κL κD : ℝ, 0 ≤ κF ∧ 0 ≤ κL ∧ 0 ≤ κD ∧
      ∀ ε : ℕ → ℝ, (∀ j ∈ Finset.range 2, 0 < ε j ∧ ε j ≤ 1) → ε 0 ≤ βF →
      ∀ (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq n) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCTRqSCRun f c X 1 P ϑ θ β₁ β ε x₀ xP δP k₁ D nF₁ nD₁ →
        (θ * ε 0 < ‖c (xP k₁)‖ →
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤
            (κF + κL * |Real.log (ε 0 * ε 1)|) * tpqpOrderF (fun j => (j : ℝ) + 1) 1 ε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤ κD * tpqpOrderD (fun j => (j : ℝ) + 1) 1 ε) ∧
        (‖c (xP k₁)‖ ≤ θ * ε 0 → ∃ kε, D.IsEnd f c X 1 θ ε kε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) + D.funEvals kε ≤
            (κF + κL * |Real.log (ε 0 * ε 1)|) * tpqpOrderF (fun j => (j : ℝ) + 1) 1 ε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) + D.derivEvals kε ≤
            κD * tpqpOrderD (fun j => (j : ℝ) + 1) 1 ε) := by
  obtain ⟨κF, κL, κD, h0, h1, h2, H⟩ :=
    theorem_14_3_9_trq le_rfl hc hf hB P hϑ1 hθ0 hθ1 hβ0 hβϑ x₀ hβ₁ϑ
  refine ⟨κF, κL, κD, h0, h1, h2, fun ε hε hεβ xP δP k₁ D nF₁ nD₁ hR => ?_⟩
  have hπ : ∀ j ∈ Finset.Icc 1 1,
      (fun _ : ℕ => ((1 : ℕ) : ℝ) + 1) j = (fun j : ℕ => (j : ℝ) + 1) j :=
    fun j hj => by rw [Finset.Icc_self, Finset.mem_singleton] at hj; subst hj; rfl
  have hΛ : Constrained.tolLogTerm 1 ε = |Real.log (ε 0 * ε 1)| := by
    have hε1 := hε 1 (by simp)
    rw [Constrained.tolLogTerm_def]
    congr 3
    exact le_antisymm (Optimization.finMin_le (Finset.mem_Icc.2 ⟨le_rfl, le_rfl⟩))
      (Optimization.le_finMin hε1.2 fun j hj => by
        rw [Finset.Icc_self, Finset.mem_singleton] at hj; subst hj; exact le_rfl)
  rw [← tpqpOrderF_congr hπ, ← tpqpOrderD_congr hπ, ← hΛ]
  exact H ε hε hεβ xP δP k₁ D nF₁ nD₁ hR

end Theorem1439

/-! ### Existence of TPqp-GC runs with a trust-region INNER -/


section Existence

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {q : ℕ} {ϑ θ β : ℝ} {ε : ℕ → ℝ}

/-- **TPqp-GC runs with INNER = TRq-SC in both phases exist** (so the class `IsTPqpGCTRqSCRun` of
`theorem_14_3_9_trq` is not empty) under X.CNe (`X` closed), c.D1qLB.X and f.D1qLB.X (on an open
convex `X₀ ⊇ X`), for all TRq parameters, `θ ∈ (0, 1)`, `β ∈ (0, θ]` with `β ≤ ϑ ≤ 1`,
`ε ∈ (0, 1]^{q+1}`, `β₁ ∈ (0, 1)` with `β₁ ‖c(x₀)‖ < 1` and `β₁ ‖c(x₀)‖ ≤ ϑ`, and `x₀ ∈ X`:
Phase 1 is LENq-SC with TRq-SC calls on `ν`, Phase 2 is a run with TRq-SC calls
(`Constrained.exists_isHighOrderTargetRun_isTRqCalls`). -/
theorem exists_isTPqpGCTRqSCRun (hX : IsClosed X) (hq : 1 ≤ q) {X₀ : Set ℝⁿ}
    {Lc Bc Lf Bf : ℕ → ℝ} (hc : AssumptionCD1pLBX c X X₀ q Lc Bc)
    (hf : AssumptionD1pLBX f X X₀ q Lf Bf) (P : Optimization.TRqParams) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hβ0 : 0 < β) (hβθ : β ≤ θ) (hβϑ : β ≤ ϑ) (hϑ1 : ϑ ≤ 1)
    (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) {β₁ : ℝ} (hβ₁0 : 0 < β₁)
    (hβ₁1 : β₁ < 1) {x₀ : ℝⁿ} (hx₀ : x₀ ∈ X) (hβ₁c : β₁ * ‖c x₀‖ < 1)
    (hβ₁ϑ : β₁ * ‖c x₀‖ ≤ ϑ) :
    ∃ (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq n) (nF₁ nD₁ : ℕ → ℕ),
      IsTPqpGCTRqSCRun f c X q P ϑ θ β₁ β ε x₀ xP δP k₁ D nF₁ nD₁ := by
  obtain ⟨LA, LB, BA, BB, hν⟩ := exists_nu_trq hc
  obtain ⟨Lμ, Bμ, hμ⟩ := exists_mu_trq hc hf
  have hϑ0 : 0 < ϑ := hβ0.trans_le hβϑ
  have hεI : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1 := fun j hj =>
    hε j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
  have h1q : 1 ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, hq⟩
  have hε₁ : ∀ j ∈ Finset.range (q + 1), 0 < phase1Tol θ ε j ∧ phase1Tol θ ε j ≤ 1 := by
    intro j hj
    by_cases h0 : j = 0
    · subst h0
      obtain ⟨h1, h2⟩ := hε 0 hj
      simp only [phase1Tol_zero]
      exact ⟨mul_pos hθ0 h1, by nlinarith⟩
    · rw [phase1Tol_of_ne θ ε h0]
      exact hε j hj
  -- Phase 1: LENq-SC with TRq-SC calls on `ν`
  obtain ⟨xP, δP, nF, nD, hxP0, hrun, hcalls⟩ := lenq_core_of hε₁ hβ₁0 hβ₁1 hx₀ hβ₁c
    (fun y o => Optimization.IsTRqOutputCost (phi2 c) X P q
      (fun j => β₁ * ‖c y‖ * phase1Tol θ ε j) ϑ y o.1 o.2.1 o.2.2.1 o.2.2.2)
    fun y hyX hy0 hry _ => by
      have hε' : ∀ j ∈ Finset.Icc 1 q, β₁ * ‖c y‖ * phase1Tol θ ε j ∈ Ioc 0 1 := fun j hj => by
        rw [phase1Tol_of_ne θ ε (by have := (Finset.mem_Icc.1 hj).1; omega)]
        refine ⟨by have := (hεI j hj).1; positivity, ?_⟩
        calc β₁ * ‖c y‖ * ε j ≤ β₁ * ‖c x₀‖ * 1 :=
              mul_le_mul (mul_le_mul_of_nonneg_left hy0 hβ₁0.le) (hεI j hj).2
                (hεI j hj).1.le (mul_nonneg hβ₁0.le (norm_nonneg _))
          _ ≤ 1 := by rw [mul_one]; exact hβ₁c.le
      have hle1 : β₁ * ‖c y‖ * phase1Tol θ ε 1 ≤ ϑ := by
        rw [phase1Tol_of_ne θ ε one_ne_zero]
        calc β₁ * ‖c y‖ * ε 1 ≤ β₁ * ‖c x₀‖ * 1 :=
              mul_le_mul (mul_le_mul_of_nonneg_left hy0 hβ₁0.le) (hεI 1 h1q).2
                (hεI 1 h1q).1.le (mul_nonneg hβ₁0.le (norm_nonneg _))
          _ ≤ ϑ := by rw [mul_one]; exact hβ₁ϑ
      have hϑ' : Optimization.finMin 1 (fun j => β₁ * ‖c y‖ * phase1Tol θ ε j) q ≤ ϑ :=
        (Optimization.finMin_le h1q).trans hle1
      obtain ⟨x, s, Δ, jk, d, hx0, hr⟩ := Optimization.exists_isTRqRun_feasible hX (phi2 c) P q
        (fun j => β₁ * ‖c y‖ * phase1Tol θ ε j) hϑ0.le hyX
      have hxr0 : x 0 ∈ X := hx0 ▸ hyX
      have hA : ∀ z ∈ X, phi2 c z ≤ phi2 c (x 0) → z ∈ nuSublevel c X x₀ := fun z hz hzy => by
        rw [hx0] at hzy
        exact ⟨hz, (Constrained.halfSqNorm_le_halfSqNorm_iff.1 hzy).trans hy0⟩
      obtain ⟨kε, hhit, hmem, hrad, hcert, -, -⟩ := Optimization.IsTRqRun.complexity
        (flow := 0) (fun z _ => by rw [phi2_apply]; positivity) (hν x₀).1
        hc.subset hA hxr0 hε' hϑ' hϑ1 hr
      have hsub := hr.mem_sublevel hxr0 (fun j hj => (hε' j hj).1.le) hϑ0.le kε hhit.2
      refine ⟨(x kε, fun _ => min (Δ kε) ϑ, Optimization.funEvalCount kε,
        Optimization.derivEvalCount (fun k => P.η₁ ≤ Optimization.trqRatio (phi2 c)
          (fun k => ftaylorSeries ℝ (phi2 c) (x k)) x s jk k) kε),
        hmem, ?_, fun _ _ => hrad, hcert, ⟨x, s, Δ, jk, d, kε, hr, hhit, hx0, rfl,
          fun _ _ => rfl, rfl, rfl⟩⟩
      have := hsub.2
      rw [hx0] at this
      exact Constrained.halfSqNorm_le_halfSqNorm_iff.1 this
  obtain ⟨⟨k₁, hhit, -, -⟩, -⟩ := theorem_14_3_3 hrun
  have hcalls' : ∀ k, 1 ≤ k → k ≤ k₁ → Optimization.IsTRqOutputCost (phi2 c) X P q
      (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j) ϑ (xP (k - 1)) (xP k) (δP k) (nF k)
        (nD k) :=
    fun k hk1 hk => hcalls k hk1 fun i hi => hhit.2 i (hi.trans_le hk)
  by_cases hc1 : ‖c (xP k₁)‖ ≤ θ * ε 0
  · have hmem : xP k₁ ∈ X := by
      rcases Nat.eq_zero_or_pos k₁ with h0 | hpos
      · rw [h0]; exact hrun.mem_zero
      · exact hrun.mem k₁ hpos hhit.2
    -- Phase 2 with TRq-SC calls
    obtain ⟨D, hD, hcallsD⟩ := Constrained.exists_isHighOrderTargetRun_isTRqCalls
      (fun t => (hμ t).1) hc.subset P hq hX hθ0 hθ1 hβ0 hβθ hβϑ hϑ1 hε hmem hc1
    exact ⟨xP, δP, k₁, D, nF, nD, ⟨⟨hxP0, hrun, hhit, fun _ => hD⟩, hcalls', fun _ => hcallsD⟩⟩
  · exact ⟨xP, δP, k₁, ⟨fun _ => x₀, fun _ => 0, fun _ _ => 0, fun _ _ => x₀, fun _ => 0,
      fun _ _ => False⟩, nF, nD, ⟨⟨hxP0, hrun, hhit, fun h => absurd h hc1⟩, hcalls',
      fun h => absurd h hc1⟩⟩

end Existence

end TRqSC


section TRqLog

set_option hygiene false in
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-! The problem of `Constrained.TwoPhaseExample.Rectangle`: `n = 2`, `m = 1`,
`X = [0, 2] × [-1, 1]`, `f(x) = x_1`, `c(x) = x_2`, `x₀ = (2, 0)`; every TPqp-GC run with TRq-SC
calls uses `≳ ε₀^{-1} log(1/ε₀)` evaluations in Phase 2
(`Constrained.TwoPhaseExample.Rectangle.funEvals_ge`). -/

open Constrained.TwoPhaseExample in
/-- Phase 1 stops at once: `c(x₀) = 0`. -/
theorem trqLog_phase1 {q : ℕ} {θ β₁ β : ℝ} {ε : ℕ → ℝ} {xP : ℕ → ℝ²} {δP : ℕ → ℕ → ℝ}
    {k₁ : ℕ} {D : TPqpSeq 2}
    (h : algorithm_14_3_2 Rectangle.obj Rectangle.con Rectangle.rect q θ β₁ β ε Rectangle.start xP
      δP k₁ D)
    (hθ : 0 < θ) : k₁ = 0 ∧ xP k₁ = Rectangle.start := by
  have hε₀ : 0 < ε 0 := by
    have := h.phase1.ε_pos 0 (by simp)
    rw [phase1Tol_zero] at this
    exact pos_of_mul_pos_right this hθ.le
  have hstop : lenStop Rectangle.con Rectangle.rect q (phase1Tol θ ε) xP δP 0 := by
    left
    rw [h.start, phase1Tol_zero]
    simp only [Rectangle.norm_con, Rectangle.start]
    simp only [PiLp.single_apply]
    norm_num
    positivity
  have hk : k₁ = 0 := by
    by_contra hne
    exact h.phase1_end.2 0 (Nat.pos_of_ne_zero hne) hstop
  exact ⟨hk, by rw [hk, h.start]⟩

open Constrained.TwoPhaseExample in
/-- **The problem of `Constrained.TwoPhaseExample.Rectangle` satisfies the hypotheses of
Theorem 14.3.9 with a trust-region INNER** (of the printed statement, and of
`theorem_14_3_9_trq_one`), for every `q`: `X` is closed, c.D1qLB.X
and f.D1qLB.X hold on the ball of radius `3` (with some constants), and f.B.Fb holds for every
`β_F` with `f_low = 0`, `f_up = 2`. -/
theorem trqLog_assumptions (q : ℕ) :
    IsClosed Rectangle.rect ∧ Rectangle.start ∈ Rectangle.rect ∧
    (∃ Lc Bc : ℕ → ℝ, AssumptionCD1pLBX Rectangle.con Rectangle.rect (ball 0 3) q Lc Bc) ∧
    (∃ Lf Bf : ℕ → ℝ, AssumptionD1pLBX Rectangle.obj Rectangle.rect (ball 0 3) q Lf Bf) ∧
    ∀ βF, Chapter07.AssumptionBFb Rectangle.obj Rectangle.con Rectangle.rect βF 0 2 := by
  refine ⟨Rectangle.isClosed_rect, Rectangle.start_mem, ?_, ?_, fun βF x hx => ⟨hx.1.1, hx.1.2.1⟩⟩
  · obtain ⟨L, B, h⟩ :=
      exists_assumptionD1pLBX_ball (Rectangle.contDiff_coord 1) Rectangle.rect_subset_ball q
    refine ⟨L, B, ⟨isOpen_ball, convex_ball 0 3, Rectangle.rect_subset_ball, fun i => ?_⟩⟩
    have : (fun x => Rectangle.con x i) = fun v : ℝ² => v 1 := by
      funext x
      rw [Subsingleton.elim i 0]
      simp [Rectangle.con]
    rw [this]
    exact h
  · exact exists_assumptionD1pLBX_ball (Rectangle.contDiff_coord 0) Rectangle.rect_subset_ball q

open Constrained.TwoPhaseExample in
/-- The printed order of the `(f, c)` evaluations for `q = 1`, `π_1 = 2`, `ε_1 = 1/2` is at most
`4/ε₀`. -/
theorem tpqpOrderF_trqLogTol_le {ε₀ : ℝ} (h0 : 0 < ε₀) :
    tpqpOrderF (fun j => (j : ℝ) + 1) 1 (Rectangle.tol ε₀) ≤ 4 / ε₀ := by
  unfold tpqpOrderF
  refine Optimization.finMax_le ?_ fun j hj => ?_
  · simp only [Rectangle.tol, ↓reduceIte]
    rw [inv_eq_one_div]
    exact div_le_div_of_nonneg_right (by norm_num) h0.le
  · rw [Finset.Icc_self, Finset.mem_singleton] at hj
    subst hj
    simp only [Rectangle.tol, ↓reduceIte, one_ne_zero]
    norm_num
    rw [Real.rpow_neg_one, div_eq_mul_inv, mul_comm]

open Constrained.TwoPhaseExample in
/-- **Every bound of the form `κ_F ε₀^{-1}` on the `(f, c)` evaluations fails for runs
with TRq-SC calls, for every `q ≥ 1`** ([cartis2022evaluation], Theorem 14.3.9 with INNER of
trust-region type). On the example `n = 2`, `m = 1`, `X = [0, 2] × [-1, 1]`, `f(x) = x_1`,
`c(x) = x_2`, `x₀ = (2, 0)` (`trqLog_assumptions`), with the dual tolerances fixed at
`ε_j = 1/2` (`Rectangle.tol`), for all TRq parameters `P`, `0 < β ≤ θ < 1`, `β ≤ ϑ ≤ 1`,
`β₁ ∈ (0, 1)` and `β_F > 0`, there is no `κ_F` such that every run of `IsTPqpGCTRqSCRun`
entering Phase 2 terminates within `κ_F/ε₀` evaluations of `(f, c)` for all `ε₀ ∈ (0, 1]` with
`ε₀ ≤ β_F`: every call of the first `⌊1/(4ε₀)⌋` outer iterations restarts from `Δ₀` and needs
`≳ log(1/ε₀)` unsuccessful first-order iterations (`Rectangle.lt_e_of_trqCalls`,
`Rectangle.funEvals_ge`).

For `q = 1` this is the printed order (`theorem_14_3_9_trq_log_necessary`). For `q ≥ 2` it does
not contradict the printed order, nor the order with the exponents `q + 1`: at these tolerances
both are at least `ε₀^{-2}` (`inv_sq_le_tpqpOrderF_trqLogTol`), while the lower bound this
example gives is only of order `ε₀^{-1} log(1/ε₀)`. -/
theorem theorem_14_3_9_trq_log_necessary_inv {q : ℕ} (hq : 1 ≤ q) (P : Optimization.TRqParams)
    {ϑ θ β β₁ βF : ℝ} (hϑ1 : ϑ ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 < β) (hβθ : β ≤ θ)
    (hβϑ : β ≤ ϑ) (hβ₁0 : 0 < β₁) (hβ₁1 : β₁ < 1) (hβF : 0 < βF) :
    ¬ ∃ κF : ℝ, ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ ≤ 1 → ε₀ ≤ βF →
      ∀ (xP : ℕ → ℝ²) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq 2) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCTRqSCRun Rectangle.obj Rectangle.con Rectangle.rect q P ϑ θ β₁ β (Rectangle.tol ε₀)
          Rectangle.start xP δP k₁ D nF₁ nD₁ →
        ‖Rectangle.con (xP k₁)‖ ≤ θ * ε₀ →
        ∃ kε, D.IsEnd Rectangle.obj Rectangle.con Rectangle.rect q θ (Rectangle.tol ε₀) kε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) + D.funEvals kε ≤ κF / ε₀ := by
  rintro ⟨κF, hκ⟩
  have hϑ0 : 0 < ϑ := hβ0.trans_le hβϑ
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = ⌈8 * |κF|⌉₊ := ⟨_, rfl⟩
  have hL8 : 8 * |κF| ≤ L := hL ▸ Nat.le_ceil _
  obtain ⟨ε₀, hε₀def⟩ : ∃ ε₀ : ℝ,
      ε₀ = min (min (1 / 8) βF) (P.γ₁ ^ L * min P.Δ₀ ϑ * P.ς * β / 4) := ⟨_, rfl⟩
  have hε₀ : 0 < ε₀ := by
    rw [hε₀def]
    have := P.ς_pos
    have := pow_pos P.γ₁_pos L
    have := lt_min P.Δ₀_pos hϑ0
    exact lt_min (lt_min (by norm_num) hβF) (by positivity)
  have hε₀8 : ε₀ ≤ 1 / 8 := hε₀def ▸ (min_le_left _ _).trans (min_le_left _ _)
  have hε₀F : ε₀ ≤ βF := hε₀def ▸ (min_le_left _ _).trans (min_le_right _ _)
  have hε₀L : ε₀ ≤ P.γ₁ ^ L * min P.Δ₀ ϑ * P.ς * β / 4 := hε₀def ▸ min_le_right _ _
  have hLcond : 4 * Rectangle.tol ε₀ 0 / (P.ς * β) ≤ P.γ₁ ^ L * min P.Δ₀ ϑ := by
    simp only [Rectangle.tol, ↓reduceIte]
    have := P.ς_pos
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hε : ∀ j ∈ Finset.range (q + 1), 0 < Rectangle.tol ε₀ j ∧ Rectangle.tol ε₀ j ≤ 1 := by
    intro j _
    by_cases hj : j = 0
    · simp only [Rectangle.tol, hj, ↓reduceIte]; exact ⟨hε₀, by linarith⟩
    · simp only [Rectangle.tol, hj, ↓reduceIte]; norm_num
  obtain ⟨-, -, ⟨Lc, Bc, hc⟩, ⟨Lf, Bf, hf⟩, -⟩ := trqLog_assumptions q
  have hc0 : ‖Rectangle.con Rectangle.start‖ = 0 := by simp [Rectangle.norm_con, Rectangle.start]
  obtain ⟨xP, δP, k₁, D, nF₁, nD₁, hR⟩ := exists_isTPqpGCTRqSCRun Rectangle.isClosed_rect hq hc hf P
    hθ0 hθ1 hβ0 hβθ hβϑ hϑ1 hε hβ₁0 hβ₁1 Rectangle.start_mem (by rw [hc0]; linarith)
    (by rw [hc0]; linarith)
  obtain ⟨hk₁, hx₁⟩ := trqLog_phase1 hR.run hθ0
  have hc1 : ‖Rectangle.con (xP k₁)‖ ≤ θ * ε₀ := by
    rw [hx₁, hc0]; positivity
  obtain ⟨kε, hend, hbound⟩ := hκ ε₀ hε₀ (by linarith) hε₀F xP δP k₁ D nF₁ nD₁ hR hc1
  rw [hk₁] at hbound
  simp only [Finset.Icc_eq_empty (by norm_num : ¬ (1 : ℕ) ≤ 0),
    Finset.sum_empty, zero_add] at hbound
  have hc1' : ‖Rectangle.con (xP k₁)‖ ≤ θ * Rectangle.tol ε₀ 0 := by simpa [Rectangle.tol] using hc1
  have h2 := hR.run.phase2 hc1'
  rw [hx₁] at h2
  have hlow := Rectangle.funEvals_ge hq h2 (hR.phase2 hc1') (by simp [Rectangle.tol])
    (by simp only [Rectangle.tol, ↓reduceIte]; linarith) hϑ0.le hϑ1 hLcond hend
  simp only [Rectangle.tol, ↓reduceIte] at hlow
  -- the lower bound `⌊1/(4ε₀)⌋ (L + 1) ≥ (L + 1)/(8 ε₀)`
  have hN : 1 / (8 * ε₀) ≤ (⌊1 / (4 * ε₀)⌋₊ : ℝ) := by
    have h1 := Nat.lt_floor_add_one (1 / (4 * ε₀))
    have h2 : 1 / (8 * ε₀) + 1 ≤ 1 / (4 * ε₀) := by
      rw [div_add_one (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  have hfin : (L + 1 : ℝ) / (8 * ε₀) ≤ D.funEvals kε := by
    calc (L + 1 : ℝ) / (8 * ε₀) = 1 / (8 * ε₀) * (L + 1) := by ring
      _ ≤ (⌊1 / (4 * ε₀)⌋₊ : ℝ) * (L + 1) := by gcongr
      _ ≤ _ := hlow
  have hcontra : κF / ε₀ < (L + 1 : ℝ) / (8 * ε₀) := by
    rw [div_lt_div_iff₀ hε₀ (by positivity)]
    nlinarith [le_abs_self κF, abs_nonneg κF]
  linarith

open Constrained.TwoPhaseExample in
/-- **Theorem 14.3.9 with a trust-region INNER fails in the printed order without the
logarithmic factor (`q = 1`).** On the example `n = 2`, `m = 1`, `X = [0, 2] × [-1, 1]`,
`f(x) = x_1`, `c(x) = x_2`, `x₀ = (2, 0)` (`Constrained.TwoPhaseExample.Rectangle`, which
satisfies X.CNe, c.D1qLB.X, f.D1qLB.X and f.B.Fb,
`trqLog_assumptions`), for all TRq parameters `P`, `0 < β ≤ θ < 1`, `β ≤ ϑ ≤ 1`,
`β₁ ∈ (0, 1)` and `β_F > 0`, there is no constant `κ_F` such that every TPqp-GC run with TRq-SC
calls (`IsTPqpGCTRqSCRun`; such runs exist, `exists_isTPqpGCTRqSCRun`) entering Phase 2 terminates
within `κ_F max[ε₀^{-1}, ε₀^{-1} ε_1^{-2}]` evaluations of `(f, c)` for all `ε ∈ (0, 1]²` with
`ε₀ ≤ β_F`. With `ε_1 = 1/2`: every call of the first `⌊1/(4ε₀)⌋` outer iterations restarts from
`Δ₀` and needs more than `L` unsuccessful iterations whenever `4ε₀/(ςβ) ≤ γ₁^L min(Δ₀, ϑ)`
(`Rectangle.lt_e_of_trqCalls`), so Phase 2 uses `≳ ε₀^{-1} log(1/ε₀)` evaluations
(`Rectangle.funEvals_ge`, `theorem_14_3_9_trq_log_necessary_inv`). The bound of
`theorem_14_3_9_trq_one`, with the factor `1 + |log(ε₀ ε_1)|`, holds on this example. -/
theorem theorem_14_3_9_trq_log_necessary (P : Optimization.TRqParams) {ϑ θ β β₁ βF : ℝ}
    (hϑ1 : ϑ ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 < β) (hβθ : β ≤ θ) (hβϑ : β ≤ ϑ)
    (hβ₁0 : 0 < β₁) (hβ₁1 : β₁ < 1) (hβF : 0 < βF) :
    ¬ ∃ κF : ℝ, ∀ ε : ℕ → ℝ, (∀ j ∈ Finset.range 2, 0 < ε j ∧ ε j ≤ 1) → ε 0 ≤ βF →
      ∀ (xP : ℕ → ℝ²) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq 2) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCTRqSCRun Rectangle.obj Rectangle.con Rectangle.rect 1 P ϑ θ β₁ β ε Rectangle.start
          xP δP k₁ D nF₁ nD₁ →
        ‖Rectangle.con (xP k₁)‖ ≤ θ * ε 0 →
        ∃ kε, D.IsEnd Rectangle.obj Rectangle.con Rectangle.rect 1 θ ε kε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) + D.funEvals kε ≤
            κF * tpqpOrderF (fun j => (j : ℝ) + 1) 1 ε := by
  rintro ⟨κF, hκ⟩
  refine theorem_14_3_9_trq_log_necessary_inv le_rfl P hϑ1 hθ0 hθ1 hβ0 hβθ hβϑ hβ₁0 hβ₁1 hβF
    ⟨|κF| * 4, fun ε₀ hε₀ hε₀1 hε₀F xP δP k₁ D nF₁ nD₁ hR hc1 => ?_⟩
  have hε : ∀ j ∈ Finset.range 2, 0 < Rectangle.tol ε₀ j ∧ Rectangle.tol ε₀ j ≤ 1 := by
    intro j _
    by_cases hj : j = 0
    · simp only [Rectangle.tol, hj, ↓reduceIte]; exact ⟨hε₀, hε₀1⟩
    · simp only [Rectangle.tol, hj, ↓reduceIte]; norm_num
  have e0 : Rectangle.tol ε₀ 0 = ε₀ := by simp [Rectangle.tol]
  obtain ⟨kε, hend, hbound⟩ := hκ (Rectangle.tol ε₀) hε (by rw [e0]; exact hε₀F) xP δP k₁ D nF₁ nD₁
    hR (by rw [e0]; exact hc1)
  refine ⟨kε, hend, hbound.trans ?_⟩
  have hO := tpqpOrderF_trqLogTol_le hε₀
  have hO0 : 0 ≤ tpqpOrderF (fun j => (j : ℝ) + 1) 1 (Rectangle.tol ε₀) := by
    have h1 := inv_le_tpqpOrderF (π := fun j : ℕ => (j : ℝ) + 1) (q := 1) (ε := Rectangle.tol ε₀)
    rw [e0] at h1
    exact (inv_nonneg.2 hε₀.le).trans h1
  calc κF * tpqpOrderF (fun j => (j : ℝ) + 1) 1 (Rectangle.tol ε₀)
      ≤ |κF| * (4 / ε₀) :=
        (mul_le_mul_of_nonneg_right (le_abs_self κF) hO0).trans
          (mul_le_mul_of_nonneg_left hO (abs_nonneg _))
    _ = |κF| * 4 / ε₀ := by ring

open Constrained.TwoPhaseExample in
/-- **Why the example does not refute the printed order for `q ≥ 2`**: with `ε_j = 1/2`
(`j ≥ 1`) the printed order `max[ε₀^{-1}, max_j ε₀^{-j} ε_j^{-(j+1)}]` of Theorem 14.3.9 with the
TRq-SC exponents `π_j = j + 1` is at least `ε₀^{-2}` (its term `j = 2`), which exceeds the lower
bound of order `ε₀^{-1} log(1/ε₀)` that the example gives. -/
theorem inv_sq_le_tpqpOrderF_trqLogTol {q : ℕ} (hq : 2 ≤ q) {ε₀ : ℝ} (h0 : 0 < ε₀) :
    (ε₀ ^ 2)⁻¹ ≤ tpqpOrderF (fun j => (j : ℝ) + 1) q (Rectangle.tol ε₀) := by
  refine le_trans ?_ (term_le_tpqpOrderF (π := fun j => (j : ℝ) + 1) (ε := Rectangle.tol ε₀)
    (Finset.mem_Icc.2 ⟨by norm_num, hq⟩ : (2 : ℕ) ∈ Finset.Icc 1 q))
  simp only [Rectangle.tol, ↓reduceIte, OfNat.ofNat_ne_zero]
  norm_num
  have : 0 < (ε₀ ^ 2)⁻¹ := by positivity
  linarith

end TRqLog


section TRqPrinted

open Constrained.TwoPhaseExample Constrained.TwoPhaseExample.SlowDecay

set_option hygiene false in
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-! The fixed problems of `theorem_14_3_9_trq_printed_false` and
`theorem_14_3_9_trq_printed_false_phase2` (`f = 0`, `c(v) = (1, v_1^{-1/8}, v_2)` or
`c₂(v) = (v_1^{-1/8}, v_2)` on `X = {v_1 ≥ 1}`) and the long TRq runs on them are
`Numlib.Optimization.Constrained.TwoPhase.HighOrder.Examples.SlowDecay` and
`…SlowDecayTwoPhase`; this section checks the assumptions of Theorem 14.3.9 for them and states
the failure of the printed order. -/

section Assumptions

/-- f.D1pLB.X for `v ↦ g(v_i)` on `ℝⁿ` from derivative bounds of `g` on the `i`-th coordinates of
an open convex `X₀ ⊇ X` (orders `k ≥ 1`), with `B = C`, `L_j = C_{j+1}`. -/
theorem assumptionD1pLBX_comp_coord {n : ℕ} {g : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U) (i : Fin n) {X X₀ : Set (EuclideanSpace ℝ (Fin n))}
    (hX₀ : IsOpen X₀) (hcv : Convex ℝ X₀) (hXX : X ⊆ X₀) (hmem : ∀ v ∈ X₀, v i ∈ U) (p : ℕ)
    {C : ℕ → ℝ} (hC : ∀ k, 1 ≤ k → ∀ v ∈ X₀, |iteratedDeriv k g (v i)| ≤ C k) :
    AssumptionD1pLBX (fun v : EuclideanSpace ℝ (Fin n) => g (v i)) X X₀ p (fun j => C (j + 1))
      C := by
  have hcd : ∀ (m : ℕ), ∀ v ∈ X₀, ContDiffAt ℝ m (fun v : EuclideanSpace ℝ (Fin n) => g (v i))
      v := fun m v hv =>
    ((hg.contDiffAt (hU.mem_nhds (hmem v hv))).of_le (by exact_mod_cast le_top)).comp_coord i
  refine .of_lipschitzOn hX₀ hcv hXX (fun v hv => (hcd p v hv).contDiffWithinAt) (fun j hj => ?_)
    fun j hj v hv => (((hg.contDiffAt (hU.mem_nhds (hmem v hv))).of_le
      (by exact_mod_cast le_top)).norm_iteratedFDeriv_comp_coord_le (k := j) i).trans
      (hC j (Finset.mem_Icc.1 hj).1 v hv)
  exact iteratedFDerivLipschitzOn_of_norm_le hcv (fun y hy => hcd (j + 1) y hy) fun v hv =>
    (((hg.contDiffAt (hU.mem_nhds (hmem v hv))).of_le
      (by exact_mod_cast le_top)).norm_iteratedFDeriv_comp_coord_le (k := j + 1) i).trans
      (hC (j + 1) (by omega) v hv)
/-- f.D1qLB.X for the component `g(v_1) = v_1^{-1/8}`, for every `q`, on `X₀ = {v_1 > 1/2}`. -/
theorem trqSlowG_assumption (q : ℕ) :
    AssumptionD1pLBX (fun v : ℝ² => eighthPow (v 0)) halfPlane openHalfPlane q
      (fun j => derivBound (j + 1)) derivBound :=
  assumptionD1pLBX_comp_coord isOpen_Ioi (fun _ hx =>
    (Real.contDiffAt_rpow_const_of_ne (ne_of_gt (mem_Ioi.1 hx))).contDiffWithinAt) 0
    isOpen_openHalfPlane convex_openHalfPlane halfPlane_subset
    (fun v hv => mem_Ioi.2 (lt_trans (by norm_num) hv)) q
    fun k _ v hv => abs_iteratedDeriv_eighthPow_le k hv

/-- f.D1qLB.X for the coordinate `v_2`, for every `q`, on `X₀ = {v_1 > 1/2}`. -/
theorem trqSlowCoord_assumption (q : ℕ) :
    AssumptionD1pLBX (fun v : ℝ² => v 1) halfPlane openHalfPlane q (fun j => derivBound (j + 1))
      derivBound := by
  refine assumptionD1pLBX_comp_coord (g := fun t : ℝ => t) isOpen_univ contDiffOn_id 1
    isOpen_openHalfPlane convex_openHalfPlane halfPlane_subset (fun _ _ => mem_univ _) q
    fun k hk v _ => ?_
  rw [iteratedDeriv_fun_id, ite_eq_right (by omega)]
  have := one_le_derivBound k
  split_ifs <;> simp <;> linarith

/-- **c.D1qLB.X for the constraint of the example**, for every `q`, on `X₀ = {v_1 > 1/2}`. -/
theorem trqSlowC_assumption (q : ℕ) :
    AssumptionCD1pLBX con halfPlane openHalfPlane q (fun j => derivBound (j + 1)) derivBound := by
  refine ⟨isOpen_openHalfPlane, convex_openHalfPlane, halfPlane_subset, fun i => ?_⟩
  fin_cases i
  · have e : (fun x : ℝ² => con x 0) = fun v : ℝ² => (fun _ : ℝ => (1 : ℝ)) (v 0) := rfl
    simp only [Fin.zero_eta]
    rw [e]
    refine assumptionD1pLBX_comp_coord isOpen_univ contDiffOn_const 0 isOpen_openHalfPlane
      convex_openHalfPlane halfPlane_subset (fun _ _ => mem_univ _) q fun k hk v _ => ?_
    rw [iteratedDeriv_const, ite_eq_right (by omega), abs_zero]
    exact zero_le_one.trans (one_le_derivBound k)
  · exact trqSlowG_assumption q
  · exact trqSlowCoord_assumption q

/-- f.D1qLB.X for the objective `f = 0`. -/
theorem trqSlowF_assumption (q : ℕ) :
    AssumptionD1pLBX (fun _ : ℝ² => (0 : ℝ)) halfPlane openHalfPlane q (fun _ => 0)
      (fun _ => 0) := by
  have e : (fun _ : ℝ² => (0 : ℝ)) = fun v : ℝ² => (fun _ : ℝ => (0 : ℝ)) (v 0) := rfl
  rw [e]
  exact assumptionD1pLBX_comp_coord (C := fun _ => 0) isOpen_univ contDiffOn_const 0
    isOpen_openHalfPlane convex_openHalfPlane halfPlane_subset (fun _ _ => mem_univ _) q
    fun k hk v _ => by
      rw [iteratedDeriv_const, ite_eq_right (by omega), abs_zero]

/-- f.B.Fb for `f = 0` (bounds `0`), for every constraint `c` and on every `ℱ_β`. -/
theorem trqSlowF_assumptionBFb {m : ℕ} (c : ℝ² → EuclideanSpace ℝ (Fin m)) (βF : ℝ) :
    Chapter07.AssumptionBFb (fun _ : ℝ² => (0 : ℝ)) c halfPlane βF 0 0 :=
  fun _ _ => ⟨le_rfl, le_rfl⟩

/-- **c.D1qLB.X for `c₂`**, for every `q`, on `X₀ = {v_1 > 1/2}`. -/
theorem trqSlowC2_assumption (q : ℕ) :
    AssumptionCD1pLBX con₂ halfPlane openHalfPlane q (fun j => derivBound (j + 1)) derivBound := by
  refine ⟨isOpen_openHalfPlane, convex_openHalfPlane, halfPlane_subset, fun i => ?_⟩
  fin_cases i
  · exact trqSlowG_assumption q
  · exact trqSlowCoord_assumption q


end Assumptions

section Runs

open Classical in
/-- **A long TPqp-GC run on a fixed problem that ends in Phase 1** (`f = 0`,
`c(v) = (1, v_1^{-1/8}, v_2)`, `X = {v_1 ≥ 1}`, `x₀ = (2, 0)`, INNER = TRq-SC with
`SlowDecay.params` and `ϑ = 1`, `β₁ = SlowDecay.phaseOneConst`). For `q ≥ 2`, `M ≥ 1`, any
`θ ∈ (0, 1)`, any `β`, and tolerances `ε ∈ (0, 1]^{q+1}` with `ε_1 = 2^{-10M}`, `ε_2 = 2^{-5M}`,
there is a run of `IsTPqpGCTRqSCRun` that terminates in Phase 1 (`‖c(x₁)‖ ≥ 1 > θ ε₀`) after a
single INNER call, the long call of `SlowDecay.exists_isTRqOutputCost`, with at least
`2^{22M} - 2^{18M} - 2^{10M} + 1` derivative evaluations. -/
theorem trqSlow_exists_tpqp_run {q : ℕ} (hq : 2 ≤ q) {M : ℕ} (hM : 1 ≤ M) {θ β : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) {ε : ℕ → ℝ} (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1)
    (h1 : ε 1 = (1 / 2) ^ (10 * M)) (h2 : ε 2 = (1 / 2) ^ (5 * M)) :
    ∃ (xP : ℕ → ℝ²) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq 2) (nF₁ nD₁ : ℕ → ℕ),
      IsTPqpGCTRqSCRun (fun _ => 0) con halfPlane q params 1 θ
        phaseOneConst β ε (pt 2 0) xP δP k₁ D nF₁ nD₁ ∧
      θ * ε 0 < ‖con (xP k₁)‖ ∧
      (((2 ^ (22 * M) - 2 ^ (18 * M) - 2 ^ (10 * M) : ℕ) : ℝ) + 1 ≤
        ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ)) := by
  set x₀ := pt 2 0 with hx₀
  set ε' : ℕ → ℝ := fun j => phaseOneConst * ‖con x₀‖ * phase1Tol θ ε j
    with hε'
  have hε'j : ∀ j, j ≠ 0 → ε' j = ε j / 2 := fun j hj => by
    simp only [hε', phase1Tol_of_ne θ ε hj]
    rw [hx₀, phaseOneConst_mul]; ring
  have hεI : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1 := fun j hj =>
    hε j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
  have hε₀ := hε 0 (by simp)
  obtain ⟨LA, LB, BA, BB, hν⟩ := exists_nu_trq (trqSlowC_assumption q)
  obtain ⟨y, δo, nF, nD, hout, hmem, hrad, hcert, hnDge⟩ :=
    exists_isTRqOutputCost hq hM (ε := ε') (fun j hj => by
      rw [hε'j j (by have := (Finset.mem_Icc.1 hj).1; omega)]
      have := hεI j hj
      exact ⟨by linarith, by linarith⟩) (by rw [hε'j 1 one_ne_zero, h1])
      (by rw [hε'j 2 two_ne_zero, h2]) (hν x₀).1
  obtain ⟨xP, hxP⟩ : ∃ xP : ℕ → ℝ², ∀ k, xP k = if k = 0 then x₀ else y := ⟨_, fun _ => rfl⟩
  have hxP0 : xP 0 = x₀ := by rw [hxP]; simp
  have hxP1 : xP 1 = y := by rw [hxP]; simp
  have hc1 : 1 ≤ ‖con (xP 1)‖ := one_le_norm_con _
  have hc0 : θ * ε 0 < 1 := by nlinarith
  have hstop1 : lenStop con halfPlane q (phase1Tol θ ε) xP (fun _ _ => δo) 1 := by
    refine Or.inr ⟨le_rfl, fun j hj => ?_⟩
    have hcj := hcert j hj
    rw [← hxP1] at hcj
    refine hcj.trans ?_
    rw [hε'j j (by have := (Finset.mem_Icc.1 hj).1; omega),
      phase1Tol_of_ne θ ε (by have := (Finset.mem_Icc.1 hj).1; omega)]
    have hεj := (hεI j hj).1
    have hδ0 : 0 ≤ δo := hrad.1.le
    have : ε j / 2 ≤ ε j * ‖con (xP 1)‖ := by nlinarith
    gcongr
  have hnstop0 : ¬ lenStop con halfPlane q (phase1Tol θ ε) xP (fun _ _ => δo) 0 := by
    rintro (h | ⟨h, -⟩)
    · rw [phase1Tol_zero, hxP0] at h
      have := one_le_norm_con x₀
      linarith
    · omega
  have hhit1 : Optimization.IsFirstHit (lenStop con halfPlane q (phase1Tol θ ε) xP
      (fun _ _ => δo)) 1 := ⟨hstop1, fun j hj => by
        obtain rfl : j = 0 := by omega
        exact hnstop0⟩
  have hbig : ∀ k, 2 ≤ k → ¬ (∀ i < k, ¬ lenStop con halfPlane q (phase1Tol θ ε) xP
      (fun _ _ => δo) i) := fun k hk h => h 1 (by omega) hstop1
  have hk1 : ∀ k, 1 ≤ k → (∀ i < k, ¬ lenStop con halfPlane q (phase1Tol θ ε) xP
      (fun _ _ => δo) i) → k = 1 := fun k h1k h => by
    by_contra hne
    exact hbig k (by omega) h
  have hphase1 : algorithm_14_3_1 con halfPlane q (phase1Tol θ ε) phaseOneConst xP
      (fun _ _ => δo) := by
    refine ⟨by rw [hxP0]; exact pt_mem_halfPlane (by norm_num), fun j hj => ?_,
      fun j hj => ?_, phaseOneConst_pos, phaseOneConst_lt_one,
      by rw [hxP0, phaseOneConst_mul]; norm_num,
      fun k h1k h => ?_, fun k h1k h _ _ => ?_, fun k h1k h j hj => ?_⟩
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [phase1Tol_zero]; exact mul_pos hθ0 hε₀.1
      · rw [phase1Tol_of_ne θ ε hj0.ne']; exact (hε j hj).1
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [phase1Tol_zero]; nlinarith
      · rw [phase1Tol_of_ne θ ε hj0.ne']; exact (hε j hj).2
    · obtain rfl := hk1 k h1k h
      rw [hxP1]; exact hmem
    · exact hrad
    · obtain rfl := hk1 k h1k h
      have hcj := hcert j hj
      rw [← hxP1] at hcj
      simp only [Nat.sub_self, hxP0]
      exact hcj
  refine ⟨xP, fun _ _ => δo, 1, ⟨fun _ => x₀, fun _ => 0, fun _ _ => 0, fun _ _ => x₀,
    fun _ => 0, fun _ _ => False⟩, fun _ => nF, fun _ => nD,
    ⟨⟨hxP0, hphase1, hhit1, fun h => absurd h (by linarith)⟩, fun k h1k hk1' => ?_,
      fun h => absurd h (by linarith)⟩, by linarith, ?_⟩
  · obtain rfl : k = 1 := by omega
    simp only [Nat.sub_self, hxP0, hxP1]
    exact hout
  · rw [Finset.Icc_self, Finset.sum_singleton]
    exact_mod_cast hnDge

open Classical in
/-- **A long TPqp-GC run on a fixed problem that enters Phase 2** (`f = 0`,
`c₂(v) = (v_1^{-1/8}, v_2)`, `X = {v_1 ≥ 1}`, `x₀ = (256, 0)`, `θ = β = 1/2`, any
`β₁ ∈ (0, 1)`, INNER = TRq-SC with `SlowDecay.params` and `ϑ = 1`). For `q ≥ 2`, `M ≥ 2` and
tolerances `ε ∈ (0, 1]^{q+1}` with `ε₀ = 1`, `ε_1 = 2^{-10M}`, `ε_2 = 2^{-5M}`: Phase 1 ends at
once (`‖c₂(x₀)‖ = 1/2 = θ ε₀`), and Phase 2 is the run of `SlowDecay.exists_isHighOrderTargetRun`:
a single INNER call on `μ(·, t_1)`, which differs from `½‖c‖²` (`c = SlowDecay.con`) by a
constant, followed by a termination in case (c); every termination index of Phase 2 has at least
`2^{22M} - 2^{18M} - 2^{10M} + 1` derivative evaluations. -/
theorem trqSlow_exists_tpqp_run_phase2 {q : ℕ} (hq : 2 ≤ q) {M : ℕ} (hM : 2 ≤ M) {β₁ : ℝ}
    (hβ₁0 : 0 < β₁) (hβ₁1 : β₁ < 1) {ε : ℕ → ℝ}
    (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) (h0 : ε 0 = 1)
    (h1 : ε 1 = (1 / 2) ^ (10 * M)) (h2 : ε 2 = (1 / 2) ^ (5 * M)) :
    ∃ (xP : ℕ → ℝ²) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq 2) (nF₁ nD₁ : ℕ → ℕ),
      IsTPqpGCTRqSCRun (fun _ => 0) con₂ halfPlane q params 1
        (1 / 2) β₁ (1 / 2) ε (pt 256 0) xP δP k₁ D nF₁ nD₁ ∧
      ‖con₂ (xP k₁)‖ ≤ 1 / 2 * ε 0 ∧
      ∀ kε, D.IsEnd (fun _ => 0) con₂ halfPlane q (1 / 2) ε kε →
        (((2 ^ (22 * M) - 2 ^ (18 * M) - 2 ^ (10 * M) : ℕ) : ℝ) + 1 ≤ D.derivEvals kε) := by
  set x₀ := pt 256 0 with hx₀
  have hcx₀ : ‖con₂ x₀‖ = 1 / 2 := norm_con₂_x₀
  have hx₀X : x₀ ∈ halfPlane := pt_mem_halfPlane (by norm_num)
  obtain ⟨LA, LB, BA, BB, hν⟩ := exists_nu_trq (trqSlowC_assumption q)
  obtain ⟨D, hphase2, hcalls, hcount⟩ :=
    exists_isHighOrderTargetRun hq hM hε h0 h1 h2 (hν x₀).1
  have hstop0 : lenStop con₂ halfPlane q (phase1Tol (1 / 2) ε) (fun _ => x₀)
      (fun _ _ => 1) 0 := Or.inl (by rw [phase1Tol_zero, hcx₀, h0]; norm_num)
  have hphase1 : algorithm_14_3_1 con₂ halfPlane q (phase1Tol (1 / 2) ε) β₁
      (fun _ => x₀) (fun _ _ => 1) := by
    refine ⟨hx₀X, fun j hj => ?_, fun j hj => ?_, hβ₁0, hβ₁1, by rw [hcx₀]; linarith,
      fun k _ h => absurd hstop0 (h 0 (by omega)), fun k _ h => absurd hstop0 (h 0 (by omega)),
      fun k _ h => absurd hstop0 (h 0 (by omega))⟩
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [phase1Tol_zero, h0]; norm_num
      · rw [phase1Tol_of_ne _ ε hj0.ne']; exact (hε j hj).1
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [phase1Tol_zero, h0]; norm_num
      · rw [phase1Tol_of_ne _ ε hj0.ne']; exact (hε j hj).2
  exact ⟨fun _ => x₀, fun _ _ => 1, 0, D, fun _ => 0, fun _ => 0,
    ⟨⟨rfl, hphase1, ⟨hstop0, fun j hj => absurd hj (Nat.not_lt_zero _)⟩, fun _ => hphase2⟩,
      fun k hk hk0 => absurd hk (by omega), fun _ => hcalls⟩,
    by rw [hcx₀, h0]; norm_num, hcount⟩

end Runs

section Main

/-- `tpqpOrderD ≤ tpqpOrderF`. -/
theorem tpqpOrderD_le_tpqpOrderF {π : ℕ → ℝ} {q : ℕ} {ε : ℕ → ℝ} (h0 : 0 < ε 0) :
    tpqpOrderD π q ε ≤ tpqpOrderF π q ε :=
  Optimization.finMax_le ((inv_nonneg.2 h0.le).trans inv_le_tpqpOrderF) fun _ hj =>
    term_le_tpqpOrderF hj

/-- `κ O_D ≤ κ (1 + |log(ε₀ ε_min)|) O_F` with the printed exponents `π_j = j + 1`, for `κ ≥ 0`
and `ε₀ ∈ (0, 1]`. -/
theorem mul_tpqpOrderD_le_printed {q : ℕ} {ε : ℕ → ℝ} {κ : ℝ} (hκ : 0 ≤ κ) (h0 : 0 < ε 0)
    (h1 : ε 0 ≤ 1) :
    κ * tpqpOrderD (fun j => (j : ℝ) + 1) q ε ≤
      κ * (1 + Constrained.tolLogTerm q ε) * tpqpOrderF (fun j => (j : ℝ) + 1) q ε := by
  have hDF := tpqpOrderD_le_tpqpOrderF (π := fun j => (j : ℝ) + 1) (q := q) h0
  have hO1 := one_le_tpqpOrderF (π := fun j => (j : ℝ) + 1) (q := q) h0 h1
  have hΛ : 0 ≤ Constrained.tolLogTerm q ε := abs_nonneg _
  calc κ * tpqpOrderD (fun j => (j : ℝ) + 1) q ε ≤ κ * tpqpOrderF (fun j => (j : ℝ) + 1) q ε :=
        mul_le_mul_of_nonneg_left hDF hκ
    _ ≤ κ * (1 + Constrained.tolLogTerm q ε) * tpqpOrderF (fun j => (j : ℝ) + 1) q ε := by
      rw [mul_assoc]
      gcongr
      nlinarith

/-- **The count against the printed order**: for `M > 20|κ| + 20`, a count
`N ≥ 2^{22M} - 2^{18M} - 2^{10M} + 1` exceeds `κ (1 + |log(ε₀ ε_min)|) max[ε₀^{-1},
max_j ε₀^{-j} ε_j^{-(j+1)}]` at the tolerances `SlowDecay.tol M` (`q ≥ 2`;
`SlowDecay.not_le_of_count`, `SlowDecay.finMax_tol_le`, `SlowDecay.abs_log_tol_le`). -/
theorem trqSlow_not_le_printed {q : ℕ} (hq : 2 ≤ q) {κ : ℝ} {M : ℕ} (hM : 20 * |κ| + 20 < M)
    {N : ℝ} (hN : ((2 ^ (22 * M) - 2 ^ (18 * M) - 2 ^ (10 * M) : ℕ) : ℝ) + 1 ≤ N) :
    ¬ N ≤ κ * (1 + Constrained.tolLogTerm q (tol M)) *
      tpqpOrderF (fun j => (j : ℝ) + 1) q (tol M) :=
  not_le_of_count hM (abs_nonneg _) (abs_log_tol_le hq M)
    (zero_le_one.trans (one_le_tpqpOrderF (tol_mem M 0).1 (tol_mem M 0).2))
    (finMax_tol_le M) hN

/-- **Theorem 14.3.9 with a trust-region INNER fails in the printed order, `q ≥ 2`**
([cartis2022evaluation], Theorem 14.3.9 with the exponents `π_j = j + 1` of (14.2.12)).
For the fixed problem `f = 0`, `c(v) = (1, v_1^{-1/8}, v_2)`, `X = {v_1 ≥ 1}`,
`x₀ = (2, 0)` (which satisfies c.D1qLB.X, f.D1qLB.X and f.B.Fb, `trqSlowC_assumption`,
`trqSlowF_assumption`, `trqSlowF_assumptionBFb`), the fixed TRq parameters `SlowDecay.params`,
`ϑ = 1`, `β₁ = SlowDecay.phaseOneConst`, and every `θ ∈ (0, 1)` and `β`, there is no constant
`κ` such that every run of `IsTPqpGCTRqSCRun` that terminates in Phase 1 uses at most
`κ (1 + |log(ε₀ ε_min)|) max[ε₀^{-1}, max_j ε₀^{-j} ε_j^{-(j+1)}]` derivative evaluations, for all
tolerances `ε ∈ (0, 1]^{q+1}`. So the printed order fails even with the logarithmic factor and
even for the derivative evaluations alone (which are at most the function evaluations).

With `ε₀ = 1`, `ε_1 = 2^{-10M}`, `ε_2 = 2^{-5M}`, `ε_j = 1` (`j ≥ 3`) the printed order is
`2^{20M}`, while the run of `trqSlow_exists_tpqp_run` has at least `2^{22M}/2` successful
iterations: after the radius has been driven down to `≈ ε_1` (first-order failures across a
direction of unit curvature), the INNER run takes second-order steps of length `≈ ε_1` along the
first axis, where `ν` has slope `≈ v_1^{-5/4}` between `ε_2 ε_1` and `ε_1` and negligible
curvature; each decreases `ν` only by `≈ ε_2 ε_1²` and the first axis is long. -/
theorem theorem_14_3_9_trq_printed_false {q : ℕ} (hq : 2 ≤ q) {θ β : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1) :
    ¬ ∃ κ : ℝ, ∀ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) →
      ∀ (xP : ℕ → ℝ²) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq 2) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCTRqSCRun (fun _ => 0) con halfPlane q params 1 θ phaseOneConst β ε
          (pt 2 0) xP δP k₁ D nF₁ nD₁ →
        θ * ε 0 < ‖con (xP k₁)‖ →
        ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤
          κ * (1 + Constrained.tolLogTerm q ε) * tpqpOrderF (fun j => (j : ℝ) + 1) q ε := by
  rintro ⟨κ, hκ⟩
  obtain ⟨M, hM⟩ := exists_nat_gt (20 * |κ| + 20)
  have hM1 : 1 ≤ M := by
    have : (1 : ℝ) < M := by linarith [abs_nonneg κ]
    exact_mod_cast this.le
  obtain ⟨xP, δP, k₁, D, nF₁, nD₁, hrun, hexit, hcount⟩ := trqSlow_exists_tpqp_run (β := β) hq hM1
    hθ0 hθ1 (ε := tol M) (fun j _ => tol_mem M j) (by simp [tol])
    (by simp [tol])
  have h := hκ (tol M) (fun j _ => tol_mem M j) xP δP k₁ D nF₁ nD₁ hrun hexit
  exact trqSlow_not_le_printed hq hM hcount h

/-- **The printed form of `theorem_14_3_9_trq` is false for every `q ≥ 2`.** The fixed problem of
`theorem_14_3_9_trq_printed_false` satisfies every hypothesis of `theorem_14_3_9_trq` (c.D1qLB.X,
f.D1qLB.X, f.B.Fb with `β_F = 1`, `ϑ = 1`, `θ ∈ (0, 1)`, `0 < β ≤ ϑ`, `β₁ ‖c(x₀)‖ ≤ ϑ`), but its
conclusion with the printed exponents `π_j = j + 1` in place of `q + 1` fails. -/
theorem theorem_14_3_9_trq_printed_false_conclusion {q : ℕ} (hq : 2 ≤ q) {θ β : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    AssumptionCD1pLBX con halfPlane openHalfPlane q (fun j => derivBound (j + 1)) derivBound ∧
    AssumptionD1pLBX (fun _ : ℝ² => (0 : ℝ)) halfPlane openHalfPlane q (fun _ => 0) (fun _ => 0) ∧
    Chapter07.AssumptionBFb (fun _ : ℝ² => (0 : ℝ)) con halfPlane 1 0 0 ∧
    (0 < β ∧ β ≤ 1) ∧ phaseOneConst * ‖con (pt 2 0)‖ ≤ 1 ∧
    ¬ ∃ κF κL κD : ℝ, 0 ≤ κF ∧ 0 ≤ κL ∧ 0 ≤ κD ∧
      ∀ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) → ε 0 ≤ 1 →
      ∀ (xP : ℕ → ℝ²) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq 2) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCTRqSCRun (fun _ => 0) con halfPlane q params 1 θ phaseOneConst β ε
          (pt 2 0) xP δP k₁ D nF₁ nD₁ →
        (θ * ε 0 < ‖con (xP k₁)‖ →
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤
            (κF + κL * Constrained.tolLogTerm q ε) * tpqpOrderF (fun j => (j : ℝ) + 1) q ε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤ κD * tpqpOrderD (fun j => (j : ℝ) + 1) q ε) ∧
        (‖con (xP k₁)‖ ≤ θ * ε 0 → ∃ kε, D.IsEnd (fun _ => 0) con halfPlane q θ ε kε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) + D.funEvals kε ≤
            (κF + κL * Constrained.tolLogTerm q ε) * tpqpOrderF (fun j => (j : ℝ) + 1) q ε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) + D.derivEvals kε ≤
            κD * tpqpOrderD (fun j => (j : ℝ) + 1) q ε) := by
  refine ⟨trqSlowC_assumption q, trqSlowF_assumption q, trqSlowF_assumptionBFb con 1,
    ⟨hβ0, hβ1⟩, by rw [phaseOneConst_mul]; norm_num, ?_⟩
  rintro ⟨κF, κL, κD, -, -, hκD, h⟩
  refine theorem_14_3_9_trq_printed_false hq (β := β) hθ0 hθ1 ⟨κD, fun ε hε xP δP k₁ D nF₁ nD₁ hrun
    hexit => ?_⟩
  have hε0 := hε 0 (by simp)
  exact ((h ε hε hε0.2 xP δP k₁ D nF₁ nD₁ hrun).1 hexit).2.trans
    (mul_tpqpOrderD_le_printed hκD hε0.1 hε0.2)

/-- **Theorem 14.3.9 with a trust-region INNER fails in the printed order in Phase 2, `q ≥ 2`**
([cartis2022evaluation], Theorem 14.3.9, (14.2.12)). For the fixed problem `f = 0`,
`c₂(v) = (v_1^{-1/8}, v_2)`, `X = {v_1 ≥ 1}`, `x₀ = (256, 0)` (c.D1qLB.X, f.D1qLB.X, f.B.Fb:
`trqSlowC2_assumption`, `trqSlowF_assumption`, `trqSlowF_assumptionBFb`), `θ = β = 1/2`, any
`β₁ ∈ (0, 1)`, the TRq parameters `SlowDecay.params` and `ϑ = 1`, there is no `κ` such that every
run of `IsTPqpGCTRqSCRun` that enters Phase 2 reaches a termination index `k_ε` of Phase 2 with at
most `κ (1 + |log(ε₀ ε_min)|) max[ε₀^{-1}, max_j ε₀^{-j} ε_j^{-(j+1)}]` derivative evaluations in
Phase 2. The runs of `trqSlow_exists_tpqp_run_phase2` have a single INNER call on `μ(·, t_1)`,
the TRq-SC run of `SlowDecay.exists_long_run` started at `(256, 0)`. -/
theorem theorem_14_3_9_trq_printed_false_phase2 {q : ℕ} (hq : 2 ≤ q) {β₁ : ℝ} (hβ₁0 : 0 < β₁)
    (hβ₁1 : β₁ < 1) :
    ¬ ∃ κ : ℝ, ∀ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) →
      ∀ (xP : ℕ → ℝ²) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq 2) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCTRqSCRun (fun _ => 0) con₂ halfPlane q params 1 (1 / 2) β₁ (1 / 2) ε
          (pt 256 0) xP δP k₁ D nF₁ nD₁ →
        ‖con₂ (xP k₁)‖ ≤ 1 / 2 * ε 0 →
        ∃ kε, D.IsEnd (fun _ => 0) con₂ halfPlane q (1 / 2) ε kε ∧
          (D.derivEvals kε : ℝ) ≤
            κ * (1 + Constrained.tolLogTerm q ε) * tpqpOrderF (fun j => (j : ℝ) + 1) q ε := by
  rintro ⟨κ, hκ⟩
  obtain ⟨M, hM⟩ := exists_nat_gt (20 * |κ| + 20)
  have hM2 : 2 ≤ M := by
    have : (2 : ℝ) < M := by linarith [abs_nonneg κ]
    exact_mod_cast this.le
  obtain ⟨xP, δP, k₁, D, nF₁, nD₁, hrun, hph2, hcount⟩ := trqSlow_exists_tpqp_run_phase2 hq hM2
    hβ₁0 hβ₁1 (ε := tol M) (fun j _ => tol_mem M j) (by simp [tol])
    (by simp [tol]) (by simp [tol])
  obtain ⟨kε, hend, h⟩ := hκ (tol M) (fun j _ => tol_mem M j) xP δP k₁ D nF₁ nD₁
    hrun hph2
  exact trqSlow_not_le_printed hq hM (hcount kε hend) h

/-- **The printed form of `theorem_14_3_9_trq` is false in Phase 2 for every `q ≥ 2`.** The fixed
problem of `theorem_14_3_9_trq_printed_false_phase2` satisfies every hypothesis of
`theorem_14_3_9_trq` (c.D1qLB.X, f.D1qLB.X, f.B.Fb with `β_F = 1`, `ϑ = 1`, `θ = β = 1/2`,
`β₁ ‖c₂(x₀)‖ = β₁/2 ≤ ϑ`), but its conclusion with the printed exponents `π_j = j + 1` fails,
through its Phase-2 part. -/
theorem theorem_14_3_9_trq_printed_false_conclusion_phase2 {q : ℕ} (hq : 2 ≤ q) {β₁ : ℝ}
    (hβ₁0 : 0 < β₁) (hβ₁1 : β₁ < 1) :
    AssumptionCD1pLBX con₂ halfPlane openHalfPlane q (fun j => derivBound (j + 1)) derivBound ∧
    AssumptionD1pLBX (fun _ : ℝ² => (0 : ℝ)) halfPlane openHalfPlane q (fun _ => 0) (fun _ => 0) ∧
    Chapter07.AssumptionBFb (fun _ : ℝ² => (0 : ℝ)) con₂ halfPlane 1 0 0 ∧
    β₁ * ‖con₂ (pt 256 0)‖ ≤ 1 ∧
    ¬ ∃ κF κL κD : ℝ, 0 ≤ κF ∧ 0 ≤ κL ∧ 0 ≤ κD ∧
      ∀ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) → ε 0 ≤ 1 →
      ∀ (xP : ℕ → ℝ²) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq 2) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCTRqSCRun (fun _ => 0) con₂ halfPlane q params 1 (1 / 2) β₁ (1 / 2) ε
          (pt 256 0) xP δP k₁ D nF₁ nD₁ →
        (1 / 2 * ε 0 < ‖con₂ (xP k₁)‖ →
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤
            (κF + κL * Constrained.tolLogTerm q ε) * tpqpOrderF (fun j => (j : ℝ) + 1) q ε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤ κD * tpqpOrderD (fun j => (j : ℝ) + 1) q ε) ∧
        (‖con₂ (xP k₁)‖ ≤ 1 / 2 * ε 0 →
          ∃ kε, D.IsEnd (fun _ => 0) con₂ halfPlane q (1 / 2) ε kε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) + D.funEvals kε ≤
            (κF + κL * Constrained.tolLogTerm q ε) * tpqpOrderF (fun j => (j : ℝ) + 1) q ε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) + D.derivEvals kε ≤
            κD * tpqpOrderD (fun j => (j : ℝ) + 1) q ε) := by
  refine ⟨trqSlowC2_assumption q, trqSlowF_assumption q, trqSlowF_assumptionBFb con₂ 1,
    by rw [norm_con₂_x₀]; linarith, ?_⟩
  rintro ⟨κF, κL, κD, -, -, hκD, h⟩
  refine theorem_14_3_9_trq_printed_false_phase2 hq hβ₁0 hβ₁1 ⟨κD, fun ε hε xP δP k₁ D nF₁ nD₁
    hrun hph2 => ?_⟩
  have hε0 := hε 0 (by simp)
  obtain ⟨kε, hend, -, h2⟩ := (h ε hε hε0.2 xP δP k₁ D nF₁ nD₁ hrun).2 hph2
  refine ⟨kε, hend, le_trans ?_ (h2.trans (mul_tpqpOrderD_le_printed hκD hε0.1 hε0.2))⟩
  have hs : 0 ≤ ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  linarith

end Main

end TRqPrinted

end CartisGouldToint.Chapter14
