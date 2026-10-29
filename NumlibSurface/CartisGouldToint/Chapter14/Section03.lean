import Numlib.Analysis.Calculus.AnchoredLipschitz
import Numlib.Analysis.InnerProductSpace.EuclideanProd
import Numlib.Optimization.Complexity.ScaledRestart
import Numlib.Optimization.Constrained.TwoPhase
import Numlib.Optimization.Optimality.CurveConditions
import NumlibSurface.CartisGouldToint.Chapter07.Section02
import NumlibSurface.CartisGouldToint.Chapter14.Section02
import Numlib.Optimization.ModelBased.HighOrder.TRqCall
import Numlib.Analysis.Calculus.MultivariateTaylor.Coord
import Numlib.Optimization.Complexity.SlowExample.TRq

/-!
# Cartis–Gould–Toint §14.3: High-order criticality for nonconvex constraints

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §14.3: the problem
`min_{x ∈ X} f(x)` subject to `c(x) = 0` (14.3.1), with a closed set `X ⊆ ℝⁿ` of simple
constraints and `c : ℝⁿ → ℝᵐ`; curve-based necessary conditions (§14.3.1), the least-norm method
LENq-SC (Algorithm 14.3.1) and the two-phase method TPqp-GC (Algorithm 14.3.2) with their
evaluation complexity (§14.3.2).

## Notation and backbone

The Lagrangian is `ℒ(x, y) = f(x) - ⟪y, c(x)⟫`, `Constrained.lagrangianFn f c y`. The Phase-2
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
ARqpC-SC (`algorithm_14_1_1`) with `c = 0`, `h = 0`.

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
open Constrained (lagrangianFn)

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
            Optimization.curveCoeff (ftaylorSeries ℝ (lagrangianFn f c ys) xs) s i = 0) →
          0 ≤ Optimization.curveCoeff (ftaylorSeries ℝ (lagrangianFn f c ys) xs) s j) := by
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
    (hφ : Optimization.taylorMeasure (ftaylorSeries ℝ (lagrangianFn f c yε) xε) j δ V ≤
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
    lagrangianFn example1431F example1431C (!₂[-1, 0]) = fun x => x 1 ^ 3 + x 0 * x 1 := by
  funext x
  simp [lagrangianFn, example1431F, example1431C,
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
    iteratedFDeriv ℝ 2 (lagrangianFn example1431F example1431C (!₂[-1, 0])) 0
        ![example1431Arc 1, example1431Arc 2] = -1 ∧
      (1 / 6 : ℝ) * iteratedFDeriv ℝ 3
        (lagrangianFn example1431F example1431C (!₂[-1, 0])) 0
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
      (ftaylorSeries ℝ (lagrangianFn example1431F example1431C (!₂[-1, 0])) 0) example1431Arc i
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
`r = c` this is `ν`). -/
noncomputable def phi2 (r : ℝⁿ → ℝᵐ) : ℝⁿ → ℝ := fun x => ‖r x‖ ^ 2 / 2

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
    refine (hcost k hk).trans ((innerEvalBound_le_sum hκ (by unfold phi2; positivity) π q
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
bounded (constants `B j`) on `X₀`. -/
structure AssumptionD1pLBX (g : ℝⁿ → ℝ) (X X₀ : Set ℝⁿ) (p : ℕ) (L B : ℕ → ℝ) : Prop where
  isOpen : IsOpen X₀
  convex : Convex ℝ X₀
  subset : X ⊆ X₀
  contDiffOn : ContDiffOn ℝ p g X₀
  lipschitz : ∀ j ∈ Finset.Icc 1 p, IteratedFDerivLipschitzOn g j (L j) X₀
  norm_le : ∀ j ∈ Finset.Icc 1 p, ∀ x ∈ X₀, ‖iteratedFDeriv ℝ j g x‖ ≤ B j

/-- **Assumption c.D1pLB.X** of [cartis2022evaluation], §14.3.2.2: the components `c_i` are `p`
times continuously differentiable on an open convex set `X₀ ⊇ X`, with Lipschitz and bounded
derivative tensors of orders `1, …, p` on `X₀` (with constants common to all components, which is
no loss of generality for finitely many components). -/
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
  refine ⟨L, B, isOpen_ball, convex_ball 0 R, hX, (hg.of_le (by exact_mod_cast le_top)).contDiffOn,
    fun j _ x hx y hy => ?_, fun j _ x hx => hB j x (ball_subset_closedBall hx)⟩
  simpa [Real.rpow_one] using hL j x (ball_subset_closedBall hx) y (ball_subset_closedBall hy)

/-- The sublevel set `𝓛_ν(x₀) = {x ∈ X | ‖c(x)‖ ≤ ‖c(x₀)‖}` of Lemma 14.3.6(i) of
[cartis2022evaluation]. -/
def nuSublevel (c : ℝⁿ → ℝᵐ) (X : Set ℝⁿ) (x₀ : ℝⁿ) : Set ℝⁿ := {x ∈ X | ‖c x‖ ≤ ‖c x₀‖}

/-- The set `𝓛_μ(t) = {x ∈ X | ‖r(x, t)‖ ≤ 1}` of Lemma 14.3.6(ii) of [cartis2022evaluation]. -/
def muSublevel (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (X : Set ℝⁿ) (t : ℝ) : Set ℝⁿ :=
  {x ∈ X | Constrained.targetResidual f c t x ≤ 1}

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

/-- The first-order Taylor decrements of `μ(·, t)` and `ν` agree at a point where `f(x) = t`. -/
theorem taylorMeasure_one_targetMerit_of_eq {x : ℝⁿ} {t : ℝ} (hf : DifferentiableAt ℝ f x)
    (hc : DifferentiableAt ℝ c x) (ht : f x = t) (δ : ℝ) (S : Set ℝⁿ) :
    Optimization.taylorMeasure (ftaylorSeries ℝ (Constrained.targetMerit f c t) x) 1 δ S =
      Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 c) x) 1 δ S := by
  simp only [Optimization.taylorMeasure_eq_sSup]
  congr 2
  funext d
  rw [FormalMultilinearSeries.taylorDecrement_one_apply,
    FormalMultilinearSeries.taylorDecrement_one_apply]
  simp only [ftaylorSeries, iteratedFDeriv_one_apply]
  rw [Constrained.fderiv_targetMerit_of_eq hf hc ht]
  rfl

/-- `ν = ½ ‖c‖²` is the merit function of the zero objective with target `0`. -/
theorem phi2_eq_targetMerit (c : ℝⁿ → ℝᵐ) :
    phi2 c = Constrained.targetMerit (fun _ => (0 : ℝ)) c 0 := by
  funext z
  simp [phi2]

/-- At a point where `f(x) = t`: `ΔT_{μ,2}(d) = ΔT_{ν,2}(d) - ½ (∇f(x)[d])²`. -/
theorem taylorDecrement_two_targetMerit_of_eq {x : ℝⁿ} {t : ℝ} (hf : ContDiffAt ℝ 2 f x)
    (hc : ContDiffAt ℝ 2 c x) (ht : f x = t) (d : ℝⁿ) :
    (ftaylorSeries ℝ (Constrained.targetMerit f c t) x).taylorDecrement 2 d =
      (ftaylorSeries ℝ (phi2 c) x).taylorDecrement 2 d - (fderiv ℝ f x d) ^ 2 / 2 := by
  have hf1 : DifferentiableAt ℝ f x := hf.differentiableAt two_ne_zero
  have hc1 : DifferentiableAt ℝ c x := hc.differentiableAt two_ne_zero
  rw [FormalMultilinearSeries.taylorDecrement_two, FormalMultilinearSeries.taylorDecrement_two]
  simp only [ftaylorSeries, iteratedFDeriv_one_apply]
  rw [Constrained.fderiv_targetMerit_of_eq hf1 hc1 ht,
    Constrained.iteratedFDeriv_two_targetMerit_apply hf hc, phi2_eq_targetMerit,
    Constrained.iteratedFDeriv_two_targetMerit_apply contDiffAt_const hc, ← ht]
  have e : (fun y => ‖c y‖ ^ 2 / 2) = Constrained.targetMerit (fun _ => (0 : ℝ)) c 0 := by
    rw [← phi2_eq_targetMerit]; rfl
  rw [← e]
  simp
  ring

/-- At a point where `f(x) = t`: `ΔT_{μ,3}(d) = ΔT_{ν,3}(d) - ½ (∇f(x)[d])² -
½ ∇f(x)[d] ∇²f(x)[d]²`. -/
theorem taylorDecrement_three_targetMerit_of_eq {x : ℝⁿ} {t : ℝ} (hf : ContDiffAt ℝ 3 f x)
    (hc : ContDiffAt ℝ 3 c x) (ht : f x = t) (d : ℝⁿ) :
    (ftaylorSeries ℝ (Constrained.targetMerit f c t) x).taylorDecrement 3 d =
      (ftaylorSeries ℝ (phi2 c) x).taylorDecrement 3 d - (fderiv ℝ f x d) ^ 2 / 2 -
        fderiv ℝ f x d * iteratedFDeriv ℝ 2 f x (fun _ => d) / 2 := by
  have hf2 : ContDiffAt ℝ 2 f x := hf.of_le (by norm_num)
  have hc2 : ContDiffAt ℝ 2 c x := hc.of_le (by norm_num)
  have h2 := taylorDecrement_two_targetMerit_of_eq hf2 hc2 ht d
  rw [FormalMultilinearSeries.taylorDecrement_three, FormalMultilinearSeries.taylorDecrement_three]
  rw [FormalMultilinearSeries.taylorDecrement_two, FormalMultilinearSeries.taylorDecrement_two]
    at h2
  have h3 : iteratedFDeriv ℝ 3 (Constrained.targetMerit f c t) x (fun _ => d) =
      iteratedFDeriv ℝ 3 (phi2 c) x (fun _ => d) +
        3 * iteratedFDeriv ℝ 2 f x (fun _ => d) * fderiv ℝ f x d := by
    rw [Constrained.iteratedFDeriv_three_targetMerit_apply hf hc, phi2_eq_targetMerit,
      Constrained.iteratedFDeriv_three_targetMerit_apply contDiffAt_const hc, ← ht]
    simp
  simp only [ftaylorSeries] at h2 ⊢
  rw [h3]
  linarith

private theorem abs_fderiv_le {x d : ℝⁿ} {δ : ℝ} (hd : d ∈ closedBall (0 : ℝⁿ) δ) :
    |fderiv ℝ f x d| ≤ ‖fderiv ℝ f x‖ * δ := by
  rw [← Real.norm_eq_abs]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left
    (mem_closedBall_zero_iff.1 hd) (norm_nonneg _))

private theorem abs_iteratedFDeriv_two_le {x d : ℝⁿ} {δ : ℝ} (hd : d ∈ closedBall (0 : ℝⁿ) δ) :
    |iteratedFDeriv ℝ 2 f x (fun _ => d)| ≤ ‖iteratedFDeriv ℝ 2 f x‖ * δ ^ 2 := by
  rw [← Real.norm_eq_abs]
  refine ((iteratedFDeriv ℝ 2 f x).le_opNorm _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
    (mem_closedBall_zero_iff.1 hd) 2) (norm_nonneg _)

/-- Second-order measures of `ν` from those of `μ` at a point where `f(x) = t`: on
`S ∩ ker ∇f(x)` they agree, and on `S` they differ by at most `(‖∇f(x)‖ δ)²/2`. -/
theorem taylorMeasure_phi2_two_le_of_eq {x : ℝⁿ} {t δ B : ℝ} (hf : ContDiffAt ℝ 2 f x)
    (hc : ContDiffAt ℝ 2 c x) (ht : f x = t) (hδ : 0 ≤ δ) {S : Set ℝⁿ} (hS : (0 : ℝⁿ) ∈ S)
    (hμ : Optimization.taylorMeasure (ftaylorSeries ℝ (Constrained.targetMerit f c t) x) 2 δ S ≤
      B) :
    Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 c) x) 2 δ
        (S ∩ {d | fderiv ℝ f x d = 0}) ≤ B ∧
      Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 c) x) 2 δ S ≤
        B + (‖fderiv ℝ f x‖ * δ) ^ 2 / 2 := by
  constructor
  · rw [Optimization.taylorMeasure]
    refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self hδ, hS, by simp⟩
      fun d hd => ?_
    have h := taylorDecrement_two_targetMerit_of_eq hf hc ht d
    have hd0 : fderiv ℝ f x d = 0 := hd.2.2
    have hμd := Optimization.taylorDecrement_le_taylorMeasure
      (ftaylorSeries ℝ (Constrained.targetMerit f c t) x) 2 (S := S) ⟨hd.1, hd.2.1⟩
    rw [hd0] at h
    linarith
  · rw [Optimization.taylorMeasure]
    refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self hδ, hS⟩ fun d hd => ?_
    have h := taylorDecrement_two_targetMerit_of_eq hf hc ht d
    have hμd := Optimization.taylorDecrement_le_taylorMeasure
      (ftaylorSeries ℝ (Constrained.targetMerit f c t) x) 2 (S := S) hd
    have hg : (fderiv ℝ f x d) ^ 2 ≤ (‖fderiv ℝ f x‖ * δ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_fderiv_le hd.1) 2
    linarith

/-- Third-order measures of `ν` from those of `μ` at a point where `f(x) = t`: on
`S ∩ ker ∇f(x)` they agree, and on `S` they differ by at most
`(‖∇f(x)‖ δ)²/2 + ‖∇f(x)‖ δ ‖∇²f(x)‖ δ²/2`. -/
theorem taylorMeasure_phi2_three_le_of_eq {x : ℝⁿ} {t δ B : ℝ} (hf : ContDiffAt ℝ 3 f x)
    (hc : ContDiffAt ℝ 3 c x) (ht : f x = t) (hδ : 0 ≤ δ) {S : Set ℝⁿ} (hS : (0 : ℝⁿ) ∈ S)
    (hμ : Optimization.taylorMeasure (ftaylorSeries ℝ (Constrained.targetMerit f c t) x) 3 δ S ≤
      B) :
    Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 c) x) 3 δ
        (S ∩ {d | fderiv ℝ f x d = 0}) ≤ B ∧
      Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 c) x) 3 δ S ≤
        B + (‖fderiv ℝ f x‖ * δ) ^ 2 / 2 +
          ‖fderiv ℝ f x‖ * δ * (‖iteratedFDeriv ℝ 2 f x‖ * δ ^ 2) / 2 := by
  constructor
  · rw [Optimization.taylorMeasure]
    refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self hδ, hS, by simp⟩
      fun d hd => ?_
    have h := taylorDecrement_three_targetMerit_of_eq hf hc ht d
    have hd0 : fderiv ℝ f x d = 0 := hd.2.2
    have hμd := Optimization.taylorDecrement_le_taylorMeasure
      (ftaylorSeries ℝ (Constrained.targetMerit f c t) x) 3 (S := S) ⟨hd.1, hd.2.1⟩
    rw [hd0] at h
    linarith
  · rw [Optimization.taylorMeasure]
    refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self hδ, hS⟩ fun d hd => ?_
    have h := taylorDecrement_three_targetMerit_of_eq hf hc ht d
    have hμd := Optimization.taylorDecrement_le_taylorMeasure
      (ftaylorSeries ℝ (Constrained.targetMerit f c t) x) 3 (S := S) hd
    have h1 := abs_fderiv_le (f := f) (x := x) hd.1
    have h2 := abs_iteratedFDeriv_two_le (f := f) (x := x) hd.1
    have hg : (fderiv ℝ f x d) ^ 2 ≤ (‖fderiv ℝ f x‖ * δ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have hgh : fderiv ℝ f x d * iteratedFDeriv ℝ 2 f x (fun _ => d) ≤
        ‖fderiv ℝ f x‖ * δ * (‖iteratedFDeriv ℝ 2 f x‖ * δ ^ 2) := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
    linarith

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
`(‖∇f‖δ)²/2` and `‖∇f‖δ ‖∇²f‖δ²/2` (`taylorMeasure_phi2_two_le_of_eq`,
`taylorMeasure_phi2_three_le_of_eq`); so the higher-order part of (14.3.41) holds only in these
corrected forms. Only the smoothness parts of c.D1pLB.X and f.D1pLB.X (`C^q` near `x_ε`) are
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
        (1 ≤ q → Optimization.taylorMeasure (ftaylorSeries ℝ (lagrangianFn f c
            (Constrained.targetMultiplier f c (D.targetOut f c θ ε kε) (D.x (kε + 1))))
            (D.x (kε + 1))) 1 (D.δ (kε + 1) 1) {d | D.x (kε + 1) + d ∈ X} ≤
          ε 1 * √(1 + ‖Constrained.targetMultiplier f c (D.targetOut f c θ ε kε)
            (D.x (kε + 1))‖ ^ 2) * D.δ (kε + 1) 1) ∧
        (2 ≤ q →
          Optimization.taylorMeasure (ftaylorSeries ℝ (lagrangianFn f c
              (Constrained.targetMultiplier f c (D.targetOut f c θ ε kε) (D.x (kε + 1))))
              (D.x (kε + 1))) 2 (D.δ (kε + 1) 2)
              ({d | D.x (kε + 1) + d ∈ X} ∩ {d | fderiv ℝ c (D.x (kε + 1)) d = 0} ∩
                {d | fderiv ℝ f (D.x (kε + 1)) d = 0}) ≤
            ε 2 * √(1 + ‖Constrained.targetMultiplier f c (D.targetOut f c θ ε kε)
              (D.x (kε + 1))‖ ^ 2) * D.δ (kε + 1) 2 ^ 2 / 2 ∧
          Optimization.taylorMeasure (ftaylorSeries ℝ (lagrangianFn f c
              (Constrained.targetMultiplier f c (D.targetOut f c θ ε kε) (D.x (kε + 1))))
              (D.x (kε + 1))) 2 (D.δ (kε + 1) 2)
              ({d | D.x (kε + 1) + d ∈ X} ∩ {d | fderiv ℝ c (D.x (kε + 1)) d = 0}) ≤
            ε 2 * √(1 + ‖Constrained.targetMultiplier f c (D.targetOut f c θ ε kε)
              (D.x (kε + 1))‖ ^ 2) * D.δ (kε + 1) 2 ^ 2 / 2 +
              (‖fderiv ℝ f (D.x (kε + 1))‖ * D.δ (kε + 1) 2) ^ 2 /
                (2 * (f (D.x (kε + 1)) - D.targetOut f c θ ε kε))) ∧
        (3 ≤ q →
          Optimization.taylorMeasure (ftaylorSeries ℝ (lagrangianFn f c
              (Constrained.targetMultiplier f c (D.targetOut f c θ ε kε) (D.x (kε + 1))))
              (D.x (kε + 1))) 3 (D.δ (kε + 1) 3)
              ({d | D.x (kε + 1) + d ∈ X} ∩ {d | fderiv ℝ c (D.x (kε + 1)) d = 0} ∩
                {d | fderiv ℝ f (D.x (kε + 1)) d = 0}) ≤
            ε 3 * √(1 + ‖Constrained.targetMultiplier f c (D.targetOut f c θ ε kε)
              (D.x (kε + 1))‖ ^ 2) * D.δ (kε + 1) 3 ^ 3 / 6 ∧
          Optimization.taylorMeasure (ftaylorSeries ℝ (lagrangianFn f c
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
      rw [taylorMeasure_one_targetMerit_of_eq ((hfC hq).differentiableAt one_ne_zero)
        ((hcC hq).differentiableAt one_ne_zero) heq, hrc] at this
      simpa using this
    · have hj : (2 : ℕ) ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨by norm_num, hq⟩
      have := hcrit 2 hj
      rw [hrc] at this
      norm_num [Nat.factorial] at this
      exact taylorMeasure_phi2_two_le_of_eq (hfC hq) (hcC hq) heq (hrad 2 hj).1.le hS this
    · have hj : (3 : ℕ) ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨by norm_num, hq⟩
      have := hcrit 3 hj
      rw [hrc] at this
      norm_num [Nat.factorial] at this
      exact taylorMeasure_phi2_three_le_of_eq (hfC hq) (hcC hq) heq (hrad 3 hj).1.le hS this
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


/-! ## Counterexamples for Lemmas 14.3.5 and 14.3.8 -/

/-! ### Phase-2 sequences with one-step INNER calls

The counterexamples below (and those of `theorem_14_3_9_false` and
`theorem_14_3_9_arqp_counterexample`) enter Phase 2 at once, from a point `x₀` with
`‖c(x₀)‖ ≤ θε₀`, and every INNER call of Phase 2 makes one successful iteration from `x_k` to
`x_{k+1}`, with radii `1` (`TPqpSeq.oneStep`). -/

section OneStep

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {q : ℕ} {θ β : ℝ} {ε : ℕ → ℝ}

/-- The Phase-2 sequences with iterates `x`, targets `t` and radii `1`, in which the `k`-th
INNER call makes one successful iteration, from `x_k` to `x_{k+1}`. -/
def TPqpSeq.oneStep (x : ℕ → ℝⁿ) (t : ℕ → ℝ) : TPqpSeq n :=
  ⟨x, t, fun _ _ => 1, fun k i => if i = 0 then x k else x (k + 1), fun _ => 1, fun _ _ => True⟩

namespace TPqpSeq

variable (x : ℕ → ℝⁿ) (t : ℕ → ℝ)

@[simp] theorem oneStep_x : (oneStep x t).x = x := rfl

@[simp] theorem oneStep_t : (oneStep x t).t = t := rfl

@[simp] theorem oneStep_δ (k j : ℕ) : (oneStep x t).δ k j = 1 := rfl

@[simp] theorem oneStep_e (k : ℕ) : (oneStep x t).e k = 1 := rfl

@[simp] theorem oneStep_succ (k i : ℕ) : (oneStep x t).succ k i := trivial

@[simp] theorem oneStep_xi_zero (k : ℕ) : (oneStep x t).xi k 0 = x k := rfl

@[simp] theorem oneStep_xi_one (k : ℕ) : (oneStep x t).xi k 1 = x (k + 1) := rfl

/-- Every INNER call makes one successful iteration. -/
@[simp] theorem succCount_oneStep (k : ℕ) : (oneStep x t).succCount k = 1 := by
  classical
  rw [Constrained.HighOrderTargetSeq.succCount_eq_card_filter]
  rw [Finset.card_eq_one]
  exact ⟨0, Finset.eq_singleton_iff_unique_mem.2 ⟨Finset.mem_filter.2 ⟨by simp, trivial⟩,
    fun i hi => by simpa using (Finset.mem_filter.1 hi).1⟩⟩

/-- `#F(k) = k + 1`: one evaluation at `x₁` and one per INNER call. -/
theorem funEvals_oneStep (k : ℕ) : (oneStep x t).funEvals k = k + 1 := by
  simp [Constrained.HighOrderTargetSeq.funEvals_eq_sum, add_comm]

/-- `#D(k) = k + 1`: one evaluation at `x₁` and one per INNER call. -/
theorem derivEvals_oneStep (k : ℕ) : (oneStep x t).derivEvals k = k + 1 := by
  simp [Constrained.HighOrderTargetSeq.derivEvals_eq_sum, add_comm]

end TPqpSeq

/-- **Phase-2 runs with one-step INNER calls**: `TPqpSeq.oneStep x t` is a Phase-2 run of
TPqp-GC from `x₁ = x 1` as soon as the constants are admissible, Step 0 holds, and at every outer
iteration `k ≥ 1` reached the new iterate is feasible and satisfies (14.3.32) with radii `1`, the
step does not increase `μ(·, t_k)`, `‖r(x_k, t_k)‖ ≥ θε₀`, and the target updates (14.3.33),
(14.3.35) hold. -/
theorem isTPqpGCPhase2_oneStep {x : ℕ → ℝⁿ} {t : ℕ → ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hβ : 0 < β) (hβθ : β ≤ θ) (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j)
    (hε1 : ∀ j ∈ Finset.range (q + 1), ε j ≤ 1) (hx1 : x 1 ∈ X) (hc1 : ‖c (x 1)‖ ≤ θ * ε 0)
    (ht1 : t 1 = f (x 1) - √(ε 0 ^ 2 - ‖c (x 1)‖ ^ 2))
    (hmem : ∀ k, 1 ≤ k → (TPqpSeq.oneStep x t).Before f c X q θ ε k → x (k + 1) ∈ X)
    (hout : ∀ k, 1 ≤ k → (TPqpSeq.oneStep x t).Before f c X q θ ε k →
      Constrained.targetResidual f c (t k) (x (k + 1)) < θ * ε 0 ∨ f (x (k + 1)) < t k ∨
        meritCrit f c X q ε (t k) (x (k + 1)) (fun _ => 1))
    (hmono : ∀ k, 1 ≤ k → (TPqpSeq.oneStep x t).Before f c X q θ ε k →
      Constrained.targetMerit f c (t k) (x (k + 1)) ≤ Constrained.targetMerit f c (t k) (x k))
    (hres : ∀ k, 1 ≤ k → (TPqpSeq.oneStep x t).Before f c X q θ ε k →
      θ * ε 0 ≤ Constrained.targetResidual f c (t k) (x k))
    (ha : ∀ k, 1 ≤ k → (TPqpSeq.oneStep x t).Before f c X q θ ε k →
      (TPqpSeq.oneStep x t).IsKa f c θ ε k →
      t (k + 1) = f (x (k + 1)) - √(ε 0 ^ 2 - ‖c (x (k + 1))‖ ^ 2))
    (hb : ∀ k, 1 ≤ k → (TPqpSeq.oneStep x t).Before f c X q θ ε k →
      (TPqpSeq.oneStep x t).IsKb f c θ ε k → t (k + 1) = 2 * f (x (k + 1)) - t k) :
    IsTPqpGCPhase2 f c X q θ β ε (x 1) (TPqpSeq.oneStep x t) :=
  ⟨hθ, hθ1, hβ, hβθ, hε, hε1, hx1, hc1, rfl, ht1, hmem, fun _ _ _ _ _ => ⟨one_pos, le_rfl⟩, hout,
    fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun k hk1 hk i hi => by obtain rfl : i = 0 := by simpa using hi
                            exact hmono k hk1 hk,
    fun k hk1 hk i hi => by obtain rfl : i = 0 := by simpa using hi
                            exact hres k hk1 hk, ha, hb⟩

/-- **The INNER contract for one-step calls cut by the third test of (14.3.32)**: if every call
ends at a point passing the third test of (14.3.32) for the old target, the only successful
iteration of each call is exempt from the decrease of `IsInnerPhaseRun`, which then holds for
every `κ_decr`, `π` and `κ_uns + κ_unc ≥ 1`. -/
theorem isInnerPhaseRun_oneStep {x : ℕ → ℝⁿ} {t : ℕ → ℝ} {κdecr κuns κunc : ℝ} {π : ℕ → ℝ}
    (hκ : 1 ≤ κuns + κunc)
    (hcrit : ∀ k, 1 ≤ k → (TPqpSeq.oneStep x t).Before f c X q θ ε k →
      meritCrit f c X q ε (t k) (x (k + 1)) (fun _ => 1)) :
    IsInnerPhaseRun f c X q θ β ε (TPqpSeq.oneStep x t) κdecr κuns κunc π :=
  ⟨fun _ _ _ => by simp; linarith, fun _ _ _ _ _ hs => absurd trivial hs,
    fun k hk1 hk i hi _ hcont _ => by
      obtain rfl : i = 0 := by simpa using hi
      rcases hcont with h | h
      · simp at h
      · exact absurd (hcrit k hk1 hk) h⟩

/-- **The INNER contract keyed on INNER's test for one-step calls**: if every call ends at a
point passing INNER's own test (14.3.19), the only successful iteration of each call is exempt
from the decrease of `IsInnerPhaseRunStrong`, which then holds for every `κ_decr`, `π`,
`κ_uns + κ_unc ≥ 1` and radii `ρ ≤ 1`. -/
theorem isInnerPhaseRunStrong_oneStep {x : ℕ → ℝⁿ} {t : ℕ → ℝ} {κdecr κuns κunc : ℝ}
    {π ρ : ℕ → ℝ} (hκ : 1 ≤ κuns + κunc) (hρ : ∀ j ∈ Finset.Icc 1 q, ρ j ≤ 1)
    (htest : ∀ k, 1 ≤ k → (TPqpSeq.oneStep x t).Before f c X q θ ε k →
      (TPqpSeq.oneStep x t).InnerTest f c X q β ε k) :
    IsInnerPhaseRunStrong f c X q θ β ε (TPqpSeq.oneStep x t) κdecr κuns κunc π ρ :=
  ⟨⟨fun _ _ _ => by simp; linarith, fun _ _ _ _ _ hs => absurd trivial hs,
    fun k hk1 hk i hi _ hcont _ => by
      obtain rfl : i = 0 := by simpa using hi
      rcases hcont with h | h
      · simp at h
      · exact absurd (htest k hk1 hk) h⟩,
    fun _ _ _ _ _ j hj => hρ j hj⟩

/-- **Phase 1 stopping at once**: a Phase-2 run from `x₀` (so `x₀ ∈ X` and `‖c(x₀)‖ ≤ θε₀`) is a
run of TPqp-GC from `x₀` whose Phase 1 (LENq-SC on `ν`, any `β₁ ∈ (0, 1)`) stops at `k₁ = 0`. -/
theorem IsTPqpGCPhase2.algorithm_14_3_2_of_stop {x₀ : ℝⁿ} {D : TPqpSeq n}
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

end OneStep

/-! ### Data on `ℝ²`

Points, a unit vector of `ℝ¹`, linear objectives and linear decrements on `ℝ²`, shared by the
two-dimensional counterexamples (`lemma_14_3_8_proof_gap_counterexample`,
`theorem_14_3_9_false`, `theorem_14_3_9_arqp_counterexample`). -/

namespace PlaneCex

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

/-- The point `(a, b)` of `ℝ²`. -/
noncomputable def pt (a b : ℝ) : ℝ² := EuclideanSpace.single 0 a + EuclideanSpace.single 1 b

@[simp] theorem pt_zero (a b : ℝ) : pt a b 0 = a := by simp [pt]

@[simp] theorem pt_one (a b : ℝ) : pt a b 1 = b := by simp [pt]

theorem pt_add (a b : ℝ) (d : ℝ²) : pt a b + d = pt (a + d 0) (b + d 1) := by
  ext i; fin_cases i <;> simp

theorem pt_sub (a b a' b' : ℝ) : pt a b - pt a' b' = pt (a - a') (b - b') := by
  ext i; fin_cases i <;> simp

/-- `⟪(a, b), d⟫ = a d₁ + b d₂`. -/
theorem inner_pt (a b : ℝ) (d : ℝ²) : ⟪pt a b, d⟫ = a * d 0 + b * d 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

/-- `‖(a, b)‖ = √(a² + b²)`. -/
theorem norm_pt (a b : ℝ) : ‖pt a b‖ = √(a ^ 2 + b ^ 2) := by
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]

/-- `‖(a, b)‖ ≤ |a| + |b|`. -/
theorem norm_pt_le_add (a b : ℝ) : ‖pt a b‖ ≤ |a| + |b| := by
  rw [norm_pt, Real.sqrt_le_left (by positivity)]
  nlinarith [sq_abs a, sq_abs b, mul_nonneg (abs_nonneg a) (abs_nonneg b)]

/-- `‖(a, b)‖ ≤ 1` for `|a|, |b| ≤ 1/2`. -/
theorem norm_pt_le {a b : ℝ} (ha : |a| ≤ 1 / 2) (hb : |b| ≤ 1 / 2) : ‖pt a b‖ ≤ 1 :=
  (norm_pt_le_add a b).trans (by linarith)

/-- `|d_i| ≤ ‖d‖`. -/
theorem abs_apply_le (d : ℝ²) (i : Fin 2) : |d i| ≤ ‖d‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le d i

/-- The unit vector of `ℝ¹`. -/
noncomputable def unitE : ℝ¹ := EuclideanSpace.single 0 1

theorem norm_smul_unitE (r : ℝ) : ‖r • unitE‖ = |r| := by simp [unitE, norm_smul]

/-- The linear objective `x ↦ a x₁ + b x₂`. -/
def linF (a b : ℝ) (x : ℝ²) : ℝ := a * x 0 + b * x 1

theorem linF_pt (a b u v : ℝ) : linF a b (pt u v) = a * u + b * v := by simp [linF]

theorem hasFDerivAt_linF (a b : ℝ) (y : ℝ²) :
    HasFDerivAt (linF a b) (a • EuclideanSpace.proj (0 : Fin 2) +
      b • EuclideanSpace.proj (1 : Fin 2) : ℝ² →L[ℝ] ℝ) y :=
  ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 y 0).const_smul a).add
    ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 y 1).const_smul b)

theorem contDiff_linF (a b : ℝ) : ContDiff ℝ ⊤ (linF a b) :=
  (contDiff_const.mul (contDiff_piLp_apply (p := 2))).add
    (contDiff_const.mul (contDiff_piLp_apply (p := 2)))

/-- `‖∇(a x₁ + b x₂)‖ ≤ |a| + |b|`. -/
theorem norm_iteratedFDeriv_linF_le (a b : ℝ) (y : ℝ²) :
    ∀ i ∈ Finset.Icc 1 1, ‖iteratedFDeriv ℝ i (linF a b) y‖ ≤ |a| + |b| := by
  intro i hi
  obtain rfl : i = 1 := by simpa using hi
  rw [norm_iteratedFDeriv_one, (hasFDerivAt_linF a b y).fderiv]
  have h : ∀ j : Fin 2, ‖(EuclideanSpace.proj j : ℝ² →L[ℝ] ℝ)‖ ≤ 1 := fun j =>
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
      simpa using PiLp.norm_apply_le x j
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_smul, Real.norm_eq_abs]
  · exact mul_le_of_le_one_right (abs_nonneg a) (h 0)
  · exact mul_le_of_le_one_right (abs_nonneg b) (h 1)

/-- A linear decrement `a d₁ + b d₂` is at most `|a| + |b|` on the unit ball. -/
theorem lin_le (a b : ℝ) {d : ℝ²} (hd : ‖d‖ ≤ 1) : a * d 0 + b * d 1 ≤ |a| + |b| := by
  have h0 := (abs_apply_le d 0).trans hd
  have h1 := (abs_apply_le d 1).trans hd
  have e0 : a * d 0 ≤ |a| := (le_abs_self _).trans (by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg a) h0)
  have e1 : b * d 1 ≤ |b| := (le_abs_self _).trans (by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg b) h1)
  linarith

/-- The measure of a linear decrement `d ↦ a d₁ + b d₂` with radius `1` is at most `|a| + |b|`. -/
theorem measure_lin_le {Δ : ℝ² → ℝ} {a b : ℝ} (hΔ : ∀ d, Δ d = a * d 0 + b * d 1) {S : Set ℝ²}
    (h0 : (0 : ℝ²) ∈ S) : Optimization.decrementMeasure Δ 1 S ≤ |a| + |b| :=
  Optimization.decrementMeasure_le ⟨0, mem_closedBall_self zero_le_one, h0⟩ fun d hd => by
    rw [hΔ]; exact lin_le a b (mem_closedBall_zero_iff.1 hd.1)

/-- The measure of a linear decrement `d ↦ a d₁ + b d₂` with radius `1` is at most
`√(a² + b²)` (Cauchy–Schwarz, `Optimization.decrementMeasure_inner_le`). -/
theorem measure_lin_le_sqrt {Δ : ℝ² → ℝ} {a b : ℝ} (hΔ : ∀ d, Δ d = a * d 0 + b * d 1)
    {S : Set ℝ²} (h0 : (0 : ℝ²) ∈ S) :
    Optimization.decrementMeasure Δ 1 S ≤ √(a ^ 2 + b ^ 2) := by
  have e : Δ = fun d => ⟪pt a b, d⟫ := funext fun d => by rw [hΔ, inner_pt]
  rw [e, ← norm_pt, ← one_mul ‖pt a b‖]
  exact Optimization.decrementMeasure_inner_le ⟨0, mem_closedBall_self zero_le_one, h0⟩

/-- **A witness for a linear decrement with `ς = 1/2`**: a feasible displacement `w` of norm at
most `1` whose decrease is at least `(|a| + |b|)/2` is a `1/2`-approximate optimality
displacement. -/
theorem isApprox_lin {Δ : ℝ² → ℝ} {a b : ℝ} (hΔ : ∀ d, Δ d = a * d 0 + b * d 1) {S : Set ℝ²}
    (h0 : (0 : ℝ²) ∈ S) {w : ℝ²} (hw : ‖w‖ ≤ 1) (hwS : w ∈ S) (hval : (|a| + |b|) / 2 ≤ Δ w) :
    Optimization.IsApproxMeasureStep Δ 1 S (1 / 2) w :=
  ⟨⟨mem_closedBall_zero_iff.2 hw, hwS⟩, by have := measure_lin_le hΔ h0; linarith⟩

end PlaneCex


/-! ### Lemma 14.3.5: counterexamples to the printed (14.3.43) and (14.3.46) -/

section Counterexample1435

local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

namespace Lemma1435Cex

/-- The simple constraint set `X = [-1, 1]` of the counterexample. -/
def cexX : Set ℝ¹ := {x | |x 0| ≤ 1}

/-- The (absent) equality constraint `c ≡ 0` of the counterexample. -/
def cexC : ℝ¹ → ℝ¹ := fun _ => 0

/-- The TPqp-GC sequences of the counterexample: every iterate is `0`, every target `-ε₀`,
every radius `1`, and INNER returns its starting point without iterating. -/
noncomputable def cexRun (ε₀ : ℝ) : TPqpSeq 1 :=
  ⟨fun _ => 0, fun _ => -ε₀, fun _ _ => 1, fun _ _ => 0, fun _ => 0, fun _ _ => False⟩

private theorem cex_targetResidual {g : ℝ¹ → ℝ} (hg0 : g 0 = 0) {ε₀ : ℝ} (hε₀ : 0 ≤ ε₀) :
    Constrained.targetResidual g cexC (-ε₀) 0 = ε₀ := by
  simp [Constrained.targetResidual_def, cexC, hg0, Real.sqrt_sq hε₀]

/-- A TPqp-GC run with `c ≡ 0`, `X = [-1, 1]`, `θ = β₁ = β = ½`, `x₀ = 0` and `f(0) = 0`:
Phase 1 stops at once, Phase 2 starts with `t₁ = -ε₀`, the first INNER call returns `x₂ = x₁ = 0`
(allowed as soon as the approximate-criticality test (14.3.34) holds at `0`), and Phase 2
terminates at `k_ε = 1` in case (c), with output target `t_ε = -ε₀`. -/
theorem cex_run {g : ℝ¹ → ℝ} (hg0 : g 0 = 0) {q : ℕ} {ε : ℕ → ℝ}
    (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j) (hε1 : ∀ j ∈ Finset.range (q + 1), ε j ≤ 1)
    (hcrit : meritCrit g cexC cexX q ε (-ε 0) 0 (fun _ => 1)) :
    algorithm_14_3_2 g cexC cexX q (1 / 2) (1 / 2) (1 / 2) ε 0 (fun _ => 0) (fun _ _ => 1) 0
        (cexRun (ε 0)) ∧
      (cexRun (ε 0)).IsEnd g cexC cexX q (1 / 2) ε 1 ∧
      (cexRun (ε 0)).targetOut g cexC (1 / 2) ε 1 = -ε 0 ∧
      ∀ κdecr π, IsInnerPhaseRun g cexC cexX q (1 / 2) (1 / 2) ε (cexRun (ε 0)) κdecr 1 1 π := by
  classical
  have hε0 : 0 < ε 0 := hε 0 (by simp)
  have hres := cex_targetResidual hg0 hε0.le
  have hna : ∀ k, ¬ (cexRun (ε 0)).IsKa g cexC (1 / 2) ε k := fun k h => by
    simp only [Constrained.HighOrderTargetSeq.isKa_iff, cexRun] at h
    rw [hres] at h
    linarith
  have hnb : ∀ k, ¬ (cexRun (ε 0)).IsKb g cexC (1 / 2) ε k := fun k h => by
    simp only [Constrained.HighOrderTargetSeq.isKb_iff, cexRun, hg0] at h
    linarith [h.2]
  have hstop : ∀ k, (cexRun (ε 0)).Stop g cexC cexX q (1 / 2) ε k :=
    fun k => Or.inl ⟨hna k, hnb k⟩
  have hmem0 : (0 : ℝ¹) ∈ cexX := by simp [cexX]
  have hph2 : IsTPqpGCPhase2 g cexC cexX q (1 / 2) (1 / 2) ε 0 (cexRun (ε 0)) := by
    refine ⟨by norm_num, by norm_num, by norm_num, le_rfl, hε, hε1, hmem0,
      by simp only [cexC, norm_zero]; positivity, rfl, ?_, fun _ _ _ => hmem0,
      fun _ _ _ _ _ => ⟨one_pos, le_rfl⟩, fun _ _ _ => Or.inr (Or.inr hcrit),
      fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ i hi => absurd hi (Nat.not_lt_zero _),
      fun _ _ _ i hi => absurd hi (Nat.not_lt_zero _), fun k _ _ h => absurd h (hna k),
      fun k _ _ h => absurd h (hnb k)⟩
    simp [cexRun, cexC, hg0, Real.sqrt_sq hε0.le]
  refine ⟨hph2.algorithm_14_3_2_of_stop (by norm_num) (by norm_num),
    ⟨le_rfl, hstop 1, fun j h1 hj => absurd hj (by omega)⟩, ?_, fun κdecr π => ?_⟩
  · simp only [Constrained.HighOrderTargetSeq.targetOut, hna 1, hnb 1, or_self, ite_false]
    rfl
  · refine ⟨fun k _ _ => by simp only [cexRun, Nat.cast_zero, one_mul]; positivity,
      fun k _ _ i hi => absurd hi (Nat.not_lt_zero _),
      fun k _ _ i hi => absurd hi (Nat.not_lt_zero _)⟩


private theorem cex_lagrangian (g : ℝ¹ → ℝ) (y : ℝ¹) : lagrangianFn g cexC y = g := by
  funext x; simp [cexC]

private theorem cex_targetMultiplier (g : ℝ¹ → ℝ) (t : ℝ) :
    Constrained.targetMultiplier g cexC t 0 = 0 := by
  simp [Constrained.targetMultiplier_def, cexC]

private theorem cex_fderiv_c : fderiv ℝ cexC 0 = 0 := by
  unfold cexC; simp

private theorem contDiff_coord : ContDiff ℝ ⊤ (fun x : ℝ¹ => x 0) := contDiff_piLp_apply (p := 2)

private theorem cex_mem_closedBall {d : ℝ¹} (hd : d ∈ closedBall (0 : ℝ¹) 1) : |d 0| ≤ 1 := by
  rw [← EuclideanSpace.norm_eq_abs_fin_one]; exact mem_closedBall_zero_iff.1 hd

/-- The first-order measure at `0` on `X = [-1, 1]` with radius `1` is at most `|A|` when
`∇g(0)[d] = A d₀`. -/
private theorem cex_phi1_le {g : ℝ¹ → ℝ} {A : ℝ} (hA : ∀ d, fderiv ℝ g 0 d = A * d 0) :
    Optimization.taylorMeasure (ftaylorSeries ℝ g 0) 1 1 {d | 0 + d ∈ cexX} ≤ |A| := by
  rw [Optimization.taylorMeasure]
  refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self zero_le_one, by simp [cexX]⟩
    fun d hd => ?_
  rw [FormalMultilinearSeries.taylorDecrement_one_apply]
  simp only [ftaylorSeries, iteratedFDeriv_one_apply, hA]
  have := cex_mem_closedBall hd.1
  calc -(A * d 0) ≤ |A * d 0| := neg_le_abs _
    _ = |A| * |d 0| := abs_mul _ _
    _ ≤ |A| * 1 := mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = |A| := mul_one _

private theorem cex_norm_fderiv_le {g : ℝ¹ → ℝ} {A : ℝ} (hA : ∀ d, fderiv ℝ g 0 d = A * d 0) :
    ‖fderiv ℝ g 0‖ ≤ |A| := by
  refine (EuclideanSpace.norm_clm_fin_one_le _).trans ?_
  simp [hA]

/-! #### The `q = 2` instance -/

/-- The objective `f(x) = x/4 - (25/8) x²` of the `q = 2` counterexample. -/
noncomputable def cexF2 : ℝ¹ → ℝ := fun x => x 0 / 4 - 25 / 8 * x 0 ^ 2

/-- The tolerances `ε₀ = 1/100`, `ε_j = 1` (`j ≥ 1`). -/
noncomputable def cexEps : ℕ → ℝ := fun j => if j = 0 then 1 / 100 else 1

private theorem cexEps_zero : cexEps 0 = 1 / 100 := rfl

private theorem cexEps_of_ne {j : ℕ} (hj : j ≠ 0) : cexEps j = 1 := by simp [cexEps, hj]

private theorem cexEps_pos (j : ℕ) : 0 < cexEps j := by unfold cexEps; split_ifs <;> norm_num

private theorem cexEps_le_one (j : ℕ) : cexEps j ≤ 1 := by unfold cexEps; split_ifs <;> norm_num

private theorem contDiff_cexF2 : ContDiff ℝ ⊤ cexF2 :=
  (contDiff_coord.div_const 4).sub (contDiff_const.mul (contDiff_coord.pow 2))

private theorem cexF2_ray (d : ℝ¹) (s : ℝ) :
    cexF2 (0 + s • d) = cexF2 0 + ∑ i ∈ Finset.Icc 1 2,
      s ^ i * (if i = 1 then d 0 / 4 else -(25 / 8) * d 0 ^ 2) := by
  simp [cexF2, Finset.sum_Icc_succ_top]
  ring

private theorem cexF2_fderiv (d : ℝ¹) : fderiv ℝ cexF2 0 d = 1 / 4 * d 0 := by
  have := Optimization.iteratedFDeriv_apply_diag_eq_of_poly (N := 2)
    (contDiff_cexF2.contDiffAt.of_le le_top) (Filter.Eventually.of_forall (cexF2_ray d)) 1
    (by simp)
  rw [iteratedFDeriv_one_apply] at this
  rw [this]; simp; ring

/-- The test (14.3.34) at `x = 0` for the target `-ε₀` (`ε₀ = 1/100`, radii `1`, tolerances
`ε_j/2`), when `μ(·, -ε₀) = (g + 1/100)²/2` is a polynomial of degree `N` along every ray, with
coefficients `a_d(i)`, whose partial Taylor decrements are within the tolerances on `[-1, 1]`. -/
private theorem cex_meritCrit_of_poly {g : ℝ¹ → ℝ} (hg0 : g 0 = 0) (hg : ContDiff ℝ ⊤ g)
    {q N : ℕ} (hqN : q ≤ N) (a : ℝ¹ → ℕ → ℝ)
    (hpoly : ∀ (d : ℝ¹) (s : ℝ), (g (0 + s • d) + 1 / 100) ^ 2 / 2 =
      (g 0 + 1 / 100) ^ 2 / 2 + ∑ i ∈ Finset.Icc 1 N, s ^ i * a d i)
    (hle : ∀ d : ℝ¹, |d 0| ≤ 1 → ∀ j ∈ Finset.Icc 1 q,
      -∑ i ∈ Finset.Icc 1 j, a d i ≤ cexEps j * (1 / 2) * cexEps 0 * 1 ^ j / j !) :
    meritCrit g cexC cexX q (fun j => cexEps j * (1 / 2)) (-cexEps 0) 0 (fun _ => 1) := by
  intro j hj
  have he : Constrained.targetMerit g cexC (-cexEps 0) = fun x => (g x + 1 / 100) ^ 2 / 2 := by
    funext x; simp [Constrained.targetMerit_def, cexC, cexEps_zero]
  have hsm : ContDiffAt ℝ N (Constrained.targetMerit g cexC (-cexEps 0)) 0 := by
    rw [he]
    exact (((hg.add contDiff_const).pow 2).div_const 2).contDiffAt.of_le le_top
  rw [Optimization.taylorMeasure]
  refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self zero_le_one, by simp [cexX]⟩
    fun d hd => ?_
  rw [Optimization.taylorDecrement_eq_of_poly (a := a d) hsm (fun s => by rw [he]; exact hpoly d s)
      ((Finset.mem_Icc.1 hj).2.trans hqN), cex_targetResidual hg0 (cexEps_pos 0).le]
  exact hle d (cex_mem_closedBall hd.1) j hj

private theorem cex2_innerTest :
    meritCrit cexF2 cexC cexX 2 (fun j => cexEps j * (1 / 2)) (-cexEps 0) 0 (fun _ => 1) :=
  cex_meritCrit_of_poly (by simp [cexF2]) contDiff_cexF2 (N := 4) (by norm_num)
    (fun d i => if i = 1 then d 0 / 400 else if i = 2 then 0 else
      if i = 3 then -(25 / 32) * d 0 ^ 3 else 625 / 128 * d 0 ^ 4)
    (fun d s => by simp [cexF2, Finset.sum_Icc_succ_top]; ring) fun d hd j hj => by
      rw [abs_le] at hd
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
      interval_cases j <;> simp [Finset.sum_Icc_succ_top, cexEps] <;> linarith

private theorem cex_neg_e_mem :
    -EuclideanSpace.single (0 : Fin 1) (1 : ℝ) ∈
      closedBall (0 : ℝ¹) 1 ∩ ({d | 0 + d ∈ cexX} ∩ {d | fderiv ℝ cexC 0 d = 0}) := by
  refine ⟨mem_closedBall_zero_iff.2 (by simp), by simp [cexX],
    by simp [cex_fderiv_c]⟩

private theorem cex_phi1_nonneg (g : ℝ¹ → ℝ) :
    0 ≤ Optimization.taylorMeasure (ftaylorSeries ℝ g 0) 1 1 {d | 0 + d ∈ cexX} :=
  Optimization.taylorMeasure_nonneg _ 1 (by simp [cexX]) zero_le_one

private theorem cex2_lhs : 27 / 8 ≤ Optimization.taylorMeasure (ftaylorSeries ℝ cexF2 0) 2 1
    ({d | 0 + d ∈ cexX} ∩ {d | fderiv ℝ cexC 0 d = 0}) := by
  refine le_trans ?_ (Optimization.taylorDecrement_le_taylorMeasure _ 2 cex_neg_e_mem)
  rw [Optimization.taylorDecrement_eq_of_poly (N := 2) (contDiff_cexF2.contDiffAt.of_le le_top)
    (cexF2_ray _) le_rfl]
  simp [Finset.sum_Icc_succ_top]
  norm_num

/-! #### The `q = 3` instance -/

/-- The objective `f(x) = x/12 - (25/72) x² + (625/216) x³` of the `q = 3` counterexample
(`∇f(0) = 1/12`, `∇²f(0) = -25/36`, `∇³f(0) = 625/36`). -/
noncomputable def cexF3 : ℝ¹ → ℝ := fun x => x 0 / 12 - 25 / 72 * x 0 ^ 2 + 625 / 216 * x 0 ^ 3

private theorem contDiff_cexF3 : ContDiff ℝ ⊤ cexF3 :=
  ((contDiff_coord.div_const 12).sub (contDiff_const.mul (contDiff_coord.pow 2))).add
    (contDiff_const.mul (contDiff_coord.pow 3))

private theorem cexF3_ray (d : ℝ¹) (s : ℝ) :
    cexF3 (0 + s • d) = cexF3 0 + ∑ i ∈ Finset.Icc 1 3,
      s ^ i * (if i = 1 then d 0 / 12 else if i = 2 then -(25 / 72) * d 0 ^ 2
        else 625 / 216 * d 0 ^ 3) := by
  simp [cexF3, Finset.sum_Icc_succ_top]
  ring

private theorem cexF3_fderiv (d : ℝ¹) : fderiv ℝ cexF3 0 d = 1 / 12 * d 0 := by
  have := Optimization.iteratedFDeriv_apply_diag_eq_of_poly (N := 3)
    (contDiff_cexF3.contDiffAt.of_le le_top) (Filter.Eventually.of_forall (cexF3_ray d)) 1
    (by simp)
  rw [iteratedFDeriv_one_apply] at this
  rw [this]; simp; ring

private theorem cexF3_norm_hessian_le : ‖iteratedFDeriv ℝ 2 cexF3 0‖ ≤ 25 / 36 := by
  refine (EuclideanSpace.norm_multilinear_fin_one_le _).trans ?_
  rw [Optimization.iteratedFDeriv_apply_diag_eq_of_poly (N := 3)
    (contDiff_cexF3.contDiffAt.of_le le_top) (Filter.Eventually.of_forall (cexF3_ray _)) 2
    (by simp)]
  simp [Nat.factorial]
  norm_num

private theorem cex3_innerTest :
    meritCrit cexF3 cexC cexX 3 (fun j => cexEps j * (1 / 2)) (-cexEps 0) 0 (fun _ => 1) :=
  cex_meritCrit_of_poly (by simp [cexF3]) contDiff_cexF3 (N := 6) (by norm_num)
    (fun d i => if i = 1 then d 0 / 1200 else if i = 2 then 0 else if i = 3 then 0 else
      if i = 4 then 3125 / 10368 * d 0 ^ 4 else if i = 5 then -(15625 / 15552) * d 0 ^ 5 else
      390625 / 93312 * d 0 ^ 6)
    (fun d s => by simp [cexF3, Finset.sum_Icc_succ_top]; ring) fun d hd j hj => by
      rw [abs_le] at hd
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
      interval_cases j <;> simp [Finset.sum_Icc_succ_top, cexEps, Nat.factorial] <;> linarith

private theorem cex3_lhs : 718 / 216 ≤ Optimization.taylorMeasure (ftaylorSeries ℝ cexF3 0) 3 1
    ({d | 0 + d ∈ cexX} ∩ {d | fderiv ℝ cexC 0 d = 0}) := by
  refine le_trans ?_ (Optimization.taylorDecrement_le_taylorMeasure _ 3 cex_neg_e_mem)
  rw [Optimization.taylorDecrement_eq_of_poly (N := 3) (contDiff_cexF3.contDiffAt.of_le le_top)
    (cexF3_ray _) le_rfl]
  simp [Finset.sum_Icc_succ_top]
  norm_num

private theorem cex_subset_ball : cexX ⊆ ball (0 : ℝ¹) 2 := fun x hx => by
  rw [mem_ball_zero_iff, EuclideanSpace.norm_eq_abs_fin_one]
  exact lt_of_le_of_lt hx (by norm_num)

private theorem cex_assumptionC (p : ℕ) :
    ∃ L B : ℕ → ℝ, AssumptionCD1pLBX cexC cexX (ball 0 2) p L B := by
  obtain ⟨L, B, h⟩ := exists_assumptionD1pLBX_ball (g := fun _ : ℝ¹ => (0 : ℝ)) contDiff_const
    cex_subset_ball p
  refine ⟨L, B, isOpen_ball, convex_ball 0 2, cex_subset_ball, fun i => ?_⟩
  have e : (fun x => cexC x i) = fun _ => (0 : ℝ) := by funext x; simp [cexC]
  rw [e]; exact h

end Lemma1435Cex

open Lemma1435Cex in
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
`Lemma1435Cex.cex_run`).

The data (`n = m = 1`): `X = [-1, 1]`, `c ≡ 0` (so `ℒ = f`, `y_ε = 0`, `T(x_ε) = X(x_ε)`),
`θ = β₁ = β = ½`, `ε₀ = 1/100`, `ε_j = 1` (`j ≥ 1`), `x₀ = 0`; Phase 1 stops at once, Phase 2
starts at `x₁ = 0` with `t₁ = -ε₀` and terminates at `k_ε = 1` in case (c) with
`(x_ε, t_ε) = (0, -ε₀)`, radii `1` and `τ = f(x_ε) - t_ε = ε₀` (`Lemma1435Cex.cex_run`).
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
          Optimization.taylorMeasure (ftaylorSeries ℝ (lagrangianFn f c
              (Constrained.targetMultiplier f c (D.targetOut f c θ ε kε) (D.x (kε + 1))))
              (D.x (kε + 1))) 1 (D.δ (kε + 1) 2) {d | D.x (kε + 1) + d ∈ X} *
            ‖fderiv ℝ f (D.x (kε + 1))‖ * D.δ (kε + 1) 2) / 2 <
        Optimization.taylorMeasure (ftaylorSeries ℝ (lagrangianFn f c
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
          3 * Optimization.taylorMeasure (ftaylorSeries ℝ (lagrangianFn f c
              (Constrained.targetMultiplier f c (D.targetOut f c θ ε kε) (D.x (kε + 1))))
              (D.x (kε + 1))) 1 (D.δ (kε + 1) 3) {d | D.x (kε + 1) + d ∈ X} *
            (‖fderiv ℝ f (D.x (kε + 1))‖ * D.δ (kε + 1) 3 +
              ‖iteratedFDeriv ℝ 2 f (D.x (kε + 1))‖ * D.δ (kε + 1) 3 ^ 2)) / 6 <
        Optimization.taylorMeasure (ftaylorSeries ℝ (lagrangianFn f c
            (Constrained.targetMultiplier f c (D.targetOut f c θ ε kε) (D.x (kε + 1))))
            (D.x (kε + 1))) 3 (D.δ (kε + 1) 3)
          ({d | D.x (kε + 1) + d ∈ X} ∩ {d | fderiv ℝ c (D.x (kε + 1)) d = 0})) := by
  constructor
  · obtain ⟨hrun, hend, hout, -⟩ := cex_run (by simp [cexF2]) (fun j _ => cexEps_pos j)
      (fun j _ => cexEps_le_one j)
      (Constrained.targetCrit.mono cex2_innerTest (fun j _ => by linarith [cexEps_pos j])
        fun _ _ => zero_le_one)
    obtain ⟨Lc, Bc, hc⟩ := cex_assumptionC 2
    obtain ⟨Lf, Bf, hf⟩ :=
      exists_assumptionD1pLBX_ball (contDiff_cexF2.of_le le_top) cex_subset_ball 2
    refine ⟨cexF2, cexC, cexX, ball 0 2, 2, 2, 1 / 2, 1 / 2, 1 / 2, cexEps, 0, fun _ => 0,
      fun _ _ => 1, 0, cexRun (cexEps 0), Lc, Bc, Lf, Bf, 1, hrun, hc, hf, le_rfl, rfl,
      by simp [cexC]; norm_num [cexEps], hend, ?_, rfl, cex2_innerTest, ?_⟩
    · rw [hout]; simp [cexRun, cexF2, cexEps]
    · rw [hout]
      simp only [cexRun, cex_targetMultiplier, cex_lagrangian, norm_zero]
      have h1 := cex_phi1_le cexF2_fderiv
      have h2 := cex_norm_fderiv_le cexF2_fderiv
      have h0 := cex_phi1_nonneg cexF2
      have hl := cex2_lhs
      rw [abs_of_pos (by norm_num)] at h1 h2
      have : Optimization.taylorMeasure (ftaylorSeries ℝ cexF2 0) 1 1 {d | 0 + d ∈ cexX} *
          ‖fderiv ℝ cexF2 0‖ ≤ 1 / 4 * (1 / 4) := mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
      rw [cexEps_of_ne (by norm_num)]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, Real.sqrt_one,
        one_pow, mul_one]
      linarith
  · obtain ⟨hrun, hend, hout, -⟩ := cex_run (by simp [cexF3]) (fun j _ => cexEps_pos j)
      (fun j _ => cexEps_le_one j)
      (Constrained.targetCrit.mono cex3_innerTest (fun j _ => by linarith [cexEps_pos j])
        fun _ _ => zero_le_one)
    obtain ⟨Lc, Bc, hc⟩ := cex_assumptionC 3
    obtain ⟨Lf, Bf, hf⟩ :=
      exists_assumptionD1pLBX_ball (contDiff_cexF3.of_le le_top) cex_subset_ball 3
    refine ⟨cexF3, cexC, cexX, ball 0 2, 3, 3, 1 / 2, 1 / 2, 1 / 2, cexEps, 0, fun _ => 0,
      fun _ _ => 1, 0, cexRun (cexEps 0), Lc, Bc, Lf, Bf, 1, hrun, hc, hf, le_rfl, rfl,
      by simp [cexC]; norm_num [cexEps], hend, ?_, rfl, cex3_innerTest, ?_⟩
    · rw [hout]; simp [cexRun, cexF3, cexEps]
    · rw [hout]
      simp only [cexRun, cex_targetMultiplier, cex_lagrangian, norm_zero]
      have h1 := cex_phi1_le cexF3_fderiv
      have h2 := cex_norm_fderiv_le cexF3_fderiv
      have h3 := cexF3_norm_hessian_le
      have h0 := cex_phi1_nonneg cexF3
      have hl := cex3_lhs
      rw [abs_of_pos (by norm_num)] at h1 h2
      have : Optimization.taylorMeasure (ftaylorSeries ℝ cexF3 0) 1 1 {d | 0 + d ∈ cexX} *
          (‖fderiv ℝ cexF3 0‖ + ‖iteratedFDeriv ℝ 2 cexF3 0‖) ≤ 1 / 12 * (1 / 12 + 25 / 36) :=
        mul_le_mul h1 (by linarith) (by positivity) (by norm_num)
      rw [cexEps_of_ne (by norm_num)]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, Real.sqrt_one,
        one_pow, mul_one]
      linarith

end Counterexample1435

/-! ### Lemma 14.3.8: the decreases of its proof do not bound the bad outer iterations -/

section Counterexample1438

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

namespace Lemma1438Cex

open PlaneCex

/-- The simple constraint set `X = {x ∈ ℝ² | |x₁| ≤ 3}` of the counterexample. -/
def cexX : Set ℝ² := {x | |x 0| ≤ 3}

/-- The objective `f(x) = x₂ - x₁`. -/
def cexF : ℝ² → ℝ := linF (-1) 1

/-- The constraint `c(x) = 3/5 + x₂`. -/
noncomputable def cexC : ℝ² → ℝ¹ := fun x => (3 / 5 + x 1) • unitE

/-- The outer iterates `x_k = (-(24/5) 2^{-k}, 0)`. -/
noncomputable def cexPt (k : ℕ) : ℝ² := pt (-(24 / 5) * (1 / 2) ^ k) 0

/-- The Phase-2 sequences of the counterexample: iterates `x_k = cexPt k`, targets
`t_k = (16/5) 2^{-k}`, radii `1`, and the `k`-th INNER call makes one successful iteration from
`x_k` to `x_{k+1}`. -/
noncomputable def cexRun : TPqpSeq 2 := TPqpSeq.oneStep cexPt fun k => 16 / 5 * (1 / 2) ^ k

theorem cexF_apply (y : ℝ²) : cexF y = y 1 - y 0 := by simp [cexF, linF]; ring

theorem cexPt_one (k : ℕ) : cexPt k 1 = 0 := pt_one _ _

theorem cexPt_zero (k : ℕ) : cexPt k 0 = -(24 / 5) * (1 / 2) ^ k := pt_zero _ _

/-- `f(x_k) = (24/5) 2^{-k}`. -/
theorem cexF_pt (k : ℕ) : cexF (cexPt k) = 24 / 5 * (1 / 2) ^ k := by
  rw [cexF_apply, cexPt_one, cexPt_zero]; ring

theorem norm_cexC (y : ℝ²) : ‖cexC y‖ = |3 / 5 + y 1| := norm_smul_unitE _

theorem hasFDerivAt_cexC (y : ℝ²) :
    HasFDerivAt cexC ((EuclideanSpace.proj (1 : Fin 2) : ℝ² →L[ℝ] ℝ).smulRight unitE) y := by
  have := ((hasFDerivAt_const (3 / 5 : ℝ) y).add
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 y 1)).smul_const unitE
  exact this.congr_fderiv (ContinuousLinearMap.ext fun d => by simp)

/-- The first-order Taylor decrement of `μ(·, t)` at a point `y` with `y₂ = 0`:
`-∇μ(y, t)[d] = (f(y) - t) d₁ - (f(y) - t + 3/5) d₂`. -/
theorem cex_decr {y : ℝ²} (hy : y 1 = 0) (t : ℝ) (d : ℝ²) :
    (ftaylorSeries ℝ (Constrained.targetMerit cexF cexC t) y).taylorDecrement 1 d =
      (cexF y - t) * d 0 - (cexF y - t + 3 / 5) * d 1 := by
  rw [Constrained.taylorDecrement_one_targetMerit (f := cexF) (hasFDerivAt_linF _ _ y)
    (hasFDerivAt_cexC y)]
  simp [cexC, unitE, hy, inner_smul_left, inner_smul_right]
  ring

/-- An upper bound on the first-order measure (Cauchy–Schwarz). -/
theorem cex_measure_le {y : ℝ²} (hy : y 1 = 0) (t : ℝ) {S : Set ℝ²} (h0 : (0 : ℝ²) ∈ S) :
    Optimization.taylorMeasure (ftaylorSeries ℝ (Constrained.targetMerit cexF cexC t) y) 1 1 S ≤
      √((cexF y - t) ^ 2 + (cexF y - t + 3 / 5) ^ 2) := by
  have := measure_lin_le_sqrt (a := cexF y - t) (b := -(cexF y - t + 3 / 5))
    (Δ := (ftaylorSeries ℝ (Constrained.targetMerit cexF cexC t) y).taylorDecrement 1)
    (fun d => by rw [cex_decr hy]; ring) h0
  rwa [neg_sq] at this

/-- A lower bound on the first-order measure, along `d = -e₂`. -/
theorem cex_le_measure {y : ℝ²} (hy : y 1 = 0) (t : ℝ) {S : Set ℝ²}
    (hS : EuclideanSpace.single 1 (-1) ∈ S) :
    cexF y - t + 3 / 5 ≤
      Optimization.taylorMeasure (ftaylorSeries ℝ (Constrained.targetMerit cexF cexC t) y) 1 1
        S := by
  have := Optimization.taylorDecrement_le_taylorMeasure
    (ftaylorSeries ℝ (Constrained.targetMerit cexF cexC t) y) 1 (δ := 1)
    (d := EuclideanSpace.single 1 (-1)) ⟨by simp, hS⟩
  rw [cex_decr hy] at this
  simpa using this

/-- `‖r(y, t)‖ = √((3/5)² + (f(y) - t)²)` when `y₂ = 0`. -/
theorem cex_resid {y : ℝ²} (hy : y 1 = 0) (t : ℝ) :
    Constrained.targetResidual cexF cexC t y = √((3 / 5) ^ 2 + (cexF y - t) ^ 2) := by
  rw [Constrained.targetResidual_def, norm_cexC, hy, add_zero, abs_of_pos (by norm_num)]

/-- The test (14.3.34) for `q = 1`, `ε₁ = 1` and radius `1`: `φ^1_{μ,X(y),1}(y, t) ≤ ‖r(y, t)‖`. -/
theorem cex_meritCrit_iff {y : ℝ²} {t : ℝ} :
    meritCrit cexF cexC cexX 1 (fun _ => 1) t y (fun _ => 1) ↔
      Optimization.taylorMeasure (ftaylorSeries ℝ (Constrained.targetMerit cexF cexC t) y) 1 1
        {d | y + d ∈ cexX} ≤ Constrained.targetResidual cexF cexC t y := by
  simp [meritCrit, Constrained.targetCrit]

/-- `|-(24/5) 2^{-(k+1)} + a| ≤ 3` for `|a| ≤ 3/5`. -/
private theorem abs_cexPt_add_le (k : ℕ) {a : ℝ} (ha : |a| ≤ 3 / 5) :
    |-(24 / 5) * (1 / 2) ^ (k + 1) + a| ≤ 3 := by
  have := abs_le.1 ha
  rw [abs_le]; constructor <;> nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k,
    pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) (n := k),
    pow_succ (1 / 2 : ℝ) k]

/-- The new iterate `x_{k+1}` passes the third test of (14.3.32) for the old target `t_k`. -/
theorem cex_meritCrit_old (k : ℕ) :
    meritCrit cexF cexC cexX 1 (fun _ => 1) (16 / 5 * (1 / 2) ^ k) (cexPt (k + 1))
      (fun _ => 1) := by
  rw [cex_meritCrit_iff]
  have h0 : (0 : ℝ²) ∈ {d | cexPt (k + 1) + d ∈ cexX} := by
    simpa [cexX, cexPt_zero] using abs_cexPt_add_le k (a := 0) (by norm_num)
  refine (cex_measure_le (cexPt_one _) _ h0).trans ?_
  rw [cex_resid (cexPt_one _), cexF_pt]
  refine Real.sqrt_le_sqrt ?_
  have hw := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k
  have hw1 := pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) (n := k)
  have e : (1 / 2 : ℝ) ^ (k + 1) = (1 / 2) ^ k / 2 := by rw [pow_succ]; ring
  rw [e]
  nlinarith

/-- The new iterate `x_{k+1}` fails (14.3.34) for the new target `t_{k+1}`. -/
theorem cex_not_meritCrit_new (k : ℕ) :
    ¬ meritCrit cexF cexC cexX 1 (fun _ => 1) (16 / 5 * (1 / 2) ^ (k + 1)) (cexPt (k + 1))
      (fun _ => 1) := by
  rw [cex_meritCrit_iff, not_le]
  have hS : EuclideanSpace.single 1 (-1) ∈ {d | cexPt (k + 1) + d ∈ cexX} := by
    have e : (EuclideanSpace.single (1 : Fin 2) (-1 : ℝ)) 0 = 0 := by simp
    simpa [cexX, cexPt_zero, e] using abs_cexPt_add_le k (a := 0) (by norm_num)
  refine lt_of_lt_of_le ?_ (cex_le_measure (cexPt_one _) _ hS)
  rw [cex_resid (cexPt_one _), cexF_pt]
  have hw := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (k + 1)
  rw [Real.sqrt_lt' (by nlinarith)]
  nlinarith

/-- `‖r(y, t)‖ ≥ 3/5 = θε₀` when `y₂ = 0`. -/
theorem cex_resid_ge {y : ℝ²} (hy : y 1 = 0) (t : ℝ) :
    3 / 5 ≤ Constrained.targetResidual cexF cexC t y := by
  rw [cex_resid hy]
  calc (3 / 5 : ℝ) = √((3 / 5) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (cexF y - t)])

/-- No outer iteration is in `𝒦_a`. -/
theorem cex_not_isKa (k : ℕ) : ¬ cexRun.IsKa cexF cexC (3 / 5) (fun _ => 1) k := by
  rw [Constrained.HighOrderTargetSeq.isKa_iff]
  rw [mul_one, not_lt]
  exact cex_resid_ge (cexPt_one _) _

/-- Every outer iteration is in `𝒦_b`. -/
theorem cex_isKb (k : ℕ) : cexRun.IsKb cexF cexC (3 / 5) (fun _ => 1) k := by
  refine ⟨by rw [mul_one]; exact cex_resid_ge (cexPt_one _) _, ?_⟩
  change cexF (cexPt (k + 1)) < 16 / 5 * (1 / 2) ^ k
  rw [cexF_pt, pow_succ]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k]

/-- Phase 2 never terminates. -/
theorem cex_not_stop (k : ℕ) : ¬ cexRun.Stop cexF cexC cexX 1 (3 / 5) (fun _ => 1) k := by
  rintro (⟨-, hb⟩ | ⟨-, hm⟩)
  · exact hb (cex_isKb k)
  · exact cex_not_meritCrit_new k hm

/-- Every outer iteration is reached. -/
theorem cex_before (K : ℕ) : cexRun.Before cexF cexC cexX 1 (3 / 5) (fun _ => 1) K :=
  fun k _ _ => cex_not_stop k

/-- No INNER call contains a good iteration. -/
theorem cex_goodCount (k : ℕ) : cexRun.goodCount cexF cexC cexX 1 (3 / 5) (fun _ => 1) k = 0 := by
  classical
  rw [Constrained.HighOrderTargetSeq.goodCount,
      Constrained.TargetFollowingSeq.goodCount_eq_zero_iff]
  rintro i - ⟨hi, -, h | h, -⟩
  · exact absurd h (by change ¬ i + 1 < 1; omega)
  · exact h (cex_meritCrit_old k)

/-- The iterates `x_k`, `k ≥ 1`, lie in `X`. -/
theorem cex_mem {k : ℕ} (hk : 1 ≤ k) : cexPt k ∈ cexX := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hk
  simpa [cexX, cexPt_zero] using abs_cexPt_add_le k (a := 0) (by norm_num)

/-- `f` is smooth. -/
theorem cex_contDiffF : ContDiff ℝ ⊤ cexF := contDiff_linF _ _

/-- `c` is smooth. -/
theorem cex_contDiffC : ContDiff ℝ ⊤ cexC := by
  have h1 : ContDiff ℝ ⊤ (fun x : ℝ² => 3 / 5 + x 1) :=
    contDiff_const.add (contDiff_piLp_apply (p := 2))
  exact h1.smul contDiff_const

/-- `‖∇f‖ ≤ 2`. -/
theorem cex_deriv_le (y : ℝ²) : ∀ i ∈ Finset.Icc 1 1, ‖iteratedFDeriv ℝ i cexF y‖ ≤ 2 :=
  fun i hi => (norm_iteratedFDeriv_linF_le (-1) 1 y i hi).trans (by norm_num)

/-- f.B.Fb on `ℱ_1`. -/
theorem cex_assumptionBFb : Chapter07.AssumptionBFb cexF cexC cexX 1 (-5) 4 := by
  intro x hx
  obtain ⟨hxX, hcx⟩ := hx
  rw [norm_cexC] at hcx
  have h0 := abs_le.1 (show |x 0| ≤ 3 from hxX)
  have h1 := abs_le.1 hcx
  rw [cexF_apply]
  constructor <;> linarith

/-- The sequences form a Phase-2 run of TPqp-GC for every `β ∈ (0, 3/5]`. -/
theorem cex_isTPqpGCPhase2 {β : ℝ} (hβ : 0 < β) (hβθ : β ≤ 3 / 5) :
    IsTPqpGCPhase2 cexF cexC cexX 1 (3 / 5) β (fun _ => 1) (cexPt 1) cexRun := by
  have hc1 : ‖cexC (cexPt 1)‖ = 3 / 5 := by
    rw [norm_cexC, cexPt_one, add_zero, abs_of_pos (by norm_num)]
  refine isTPqpGCPhase2_oneStep (by norm_num) (by norm_num) hβ hβθ (fun _ _ => one_pos)
    (fun _ _ => le_rfl) (cex_mem le_rfl) (by rw [hc1]; norm_num) ?_
    (fun k _ _ => cex_mem (by omega)) (fun k _ _ => Or.inr (Or.inl (cex_isKb k).2))
    (fun k _ _ => ?_) (fun k _ _ => by simpa using cex_resid_ge (cexPt_one k) _)
    (fun k _ _ ha => absurd ha (cex_not_isKa k)) (fun k _ _ _ => ?_)
  · change (16 / 5 : ℝ) * (1 / 2) ^ 1 = cexF (cexPt 1) - √(1 ^ 2 - ‖cexC (cexPt 1)‖ ^ 2)
    rw [hc1, cexF_pt, show (1 : ℝ) ^ 2 - (3 / 5) ^ 2 = (4 / 5) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
    norm_num
  · change Constrained.targetMerit cexF cexC (16 / 5 * (1 / 2) ^ k) (cexPt (k + 1)) ≤
      Constrained.targetMerit cexF cexC (16 / 5 * (1 / 2) ^ k) (cexPt k)
    rw [Constrained.targetMerit_def, Constrained.targetMerit_def, norm_cexC, norm_cexC,
      cexPt_one, cexPt_one, cexF_pt, cexF_pt]
    have e : (1 / 2 : ℝ) ^ (k + 1) = (1 / 2) ^ k / 2 := by rw [pow_succ]; ring
    rw [e]
    have hw := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k
    nlinarith
  · change (16 / 5 : ℝ) * (1 / 2) ^ (k + 1) = 2 * cexF (cexPt (k + 1)) - 16 / 5 * (1 / 2) ^ k
    rw [cexF_pt, pow_succ]
    ring

end Lemma1438Cex

open Lemma1438Cex in
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
  classical
  have hX : IsClosed cexX :=
    isClosed_le (continuous_abs.comp (EuclideanSpace.proj (0 : Fin 2)).continuous)
      continuous_const
  have hc1 : ‖cexC (cexPt 1)‖ = 3 / 5 := by
    rw [norm_cexC, cexPt_one, add_zero, abs_of_pos (by norm_num)]
  refine ⟨cexF, cexC, cexX, 3 / 5, fun _ => 1, cexPt 1, fun _ => cexPt 1, fun _ _ => 1, cexRun,
    hX, cex_contDiffF, cex_contDiffC, cex_deriv_le, cex_assumptionBFb, rfl,
    fun β₁ β hβ₁ hβ₁1 hβ hβθ => ⟨(cex_isTPqpGCPhase2 hβ hβθ).algorithm_14_3_2_of_stop hβ₁ hβ₁1,
      by rw [hc1]; norm_num, fun κdecr κuns κunc π hκ =>
        isInnerPhaseRun_oneStep hκ fun k _ _ => cex_meritCrit_old k,
      fun κdecr κuns κunc π ρ hκ hκuns hπ hρ hs => ?_⟩, cex_before, fun K => ?_,
    fun ⟨kε, hend⟩ => cex_not_stop kε hend.2.1⟩
  · have hI : ∀ {j : ℕ}, j ∈ Finset.Icc 1 1 → j = 1 := fun hj => by simpa using hj
    have hη : 0 < Constrained.kbMargin (3 / 5) 1 := by rw [Constrained.kbMargin_def]; norm_num
    obtain ⟨-, kε, hend, -⟩ := (cex_isTPqpGCPhase2 hβ hβθ).complexity_of_innerTest hs hκ hκuns
      (πmax := π 1) (M := 1) (fun l hl => by obtain rfl := hI hl; exact ⟨hπ, le_rfl⟩) one_pos
      (fun l hl => by obtain rfl := hI hl; simp) (cex_assumptionBFb.of_le le_rfl)
      (fun j hj => by obtain rfl := hI hj; exact hρ)
      (fun _ _ => (cex_contDiffF.of_le le_top).contDiffAt)
      (fun _ _ => (cex_contDiffC.of_le le_top).contDiffAt) (fun y _ _ => cex_deriv_le y)
      (div_pos hη (by norm_num : (0 : ℝ) < 4))
      (fun j hj => by obtain rfl := hI hj; simp; linarith)
    exact cex_not_stop kε hend.2.1
  · rw [Constrained.HighOrderTargetSeq.badCount,
      Constrained.TargetFollowingSeq.badCount_eq_card_filter,
      Finset.filter_true_of_mem fun k _ => ⟨cex_isKb k, cex_goodCount k⟩, Nat.card_Ico]

end Counterexample1438


/-! ## Theorem 14.3.9 for a nonspecific INNER -/


section TheoremFalse



local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

namespace Theorem1439Cex

open PlaneCex

/-! #### The data

The problem data are shared with `theorem_14_3_9_arqp_counterexample`, which uses the objective
`f_a(x) = x₁ - a x₂` with `a = 1/16` in place of `a = 1`. -/

/-- The simple constraint set `X = [-1, 1]²`. -/
def boxX : Set ℝ² := {x | |x 0| ≤ 1 ∧ |x 1| ≤ 1}

/-- The objective `f_a(x) = x₁ - a x₂`. -/
def objA (a : ℝ) : ℝ² → ℝ := linF 1 (-a)

/-- The constraint `c(x) = x₁²/2`. -/
noncomputable def conC : ℝ² → ℝ¹ := fun x => (x 0 ^ 2 / 2) • unitE

theorem objA_apply (a : ℝ) (y : ℝ²) : objA a y = y 0 - a * y 1 := by simp [objA, linF]; ring

theorem objA_pt (a u v : ℝ) : objA a (pt u v) = u - a * v := by simp [objA_apply]

/-- `f(a, b) = a - b` for the objective `f = f_1` of this module. -/
theorem objF_pt (a b : ℝ) : objA 1 (pt a b) = a - b := by rw [objA_pt]; ring

/-- `(a, b) ∈ X` for `|a|, |b| ≤ 1`. -/
theorem pt_mem {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) : pt a b ∈ boxX := by
  simp only [boxX, mem_ofPred_eq, pt_zero, pt_one]; exact ⟨ha, hb⟩

/-- `‖c(y)‖ = y₁²/2`. -/
theorem norm_conC (y : ℝ²) : ‖conC y‖ = y 0 ^ 2 / 2 := by
  rw [conC, norm_smul_unitE, abs_of_nonneg (by positivity)]

/-- The derivative of `c`: `d ↦ y₁ d₁ e`. -/
theorem hasFDerivAt_conC (y : ℝ²) :
    HasFDerivAt conC ((y 0 • (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ)).smulRight unitE)
      y := by
  have h1 : HasFDerivAt (fun x : ℝ² => x 0 ^ 2 / 2)
      (y 0 • (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ)) y := by
    have := ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 y 0).pow 2).mul_const (1 / 2 : ℝ)
    convert this using 1
    · funext x; ring
    · ext d; simp; ring
  exact h1.smul_const unitE

/-- The first-order Taylor decrement of `μ(·, t)` at `y`:
`-∇μ(y, t)[d] = -(y₁³/2 + (f_a(y) - t)) d₁ + a (f_a(y) - t) d₂`. -/
theorem decr (a : ℝ) (y : ℝ²) (t : ℝ) (d : ℝ²) :
    (ftaylorSeries ℝ (Constrained.targetMerit (objA a) conC t) y).taylorDecrement 1 d =
      -(y 0 ^ 3 / 2 + (objA a y - t)) * d 0 + a * (objA a y - t) * d 1 := by
  rw [Constrained.taylorDecrement_one_targetMerit (f := objA a) (hasFDerivAt_linF _ _ y)
    (hasFDerivAt_conC y), objA_apply]
  simp [conC, unitE, inner_smul_left, inner_smul_right]
  ring

/-- An upper bound on the first-order measure with radius `1` (Cauchy–Schwarz). -/
theorem measure_le (y : ℝ²) (t : ℝ) {S : Set ℝ²} (h0 : (0 : ℝ²) ∈ S) :
    Optimization.taylorMeasure (ftaylorSeries ℝ (Constrained.targetMerit (objA 1) conC t) y) 1 1 S ≤
      √((y 0 ^ 3 / 2 + (objA 1 y - t)) ^ 2 + (objA 1 y - t) ^ 2) := by
  have := measure_lin_le_sqrt (a := -(y 0 ^ 3 / 2 + (objA 1 y - t))) (b := objA 1 y - t)
    (Δ := (ftaylorSeries ℝ (Constrained.targetMerit (objA 1) conC t) y).taylorDecrement 1)
    (fun d => by rw [decr, one_mul]) h0
  rwa [neg_sq] at this

/-- A lower bound on the first-order measure with radius `1`, along `d = -e₁`. -/
theorem le_measure (y : ℝ²) (t : ℝ) {S : Set ℝ²} (hS : EuclideanSpace.single 0 (-1) ∈ S) :
    y 0 ^ 3 / 2 + (objA 1 y - t) ≤
      Optimization.taylorMeasure (ftaylorSeries ℝ (Constrained.targetMerit (objA 1) conC t) y) 1 1
        S := by
  have := Optimization.taylorDecrement_le_taylorMeasure
    (ftaylorSeries ℝ (Constrained.targetMerit (objA 1) conC t) y) 1 (δ := 1)
    (d := EuclideanSpace.single 0 (-1)) ⟨by simp, hS⟩
  rw [decr] at this
  simpa using this

/-- Bounds on a residual `R = √(A² + F²)` with `A, F ≥ 0`: `A ≤ R ≤ A + F`. -/
theorem resid_bounds {R A F : ℝ} (hR : 0 ≤ R) (hsq : R ^ 2 = A ^ 2 + F ^ 2) (hA : 0 ≤ A)
    (hF : 0 ≤ F) : A ≤ R ∧ R ≤ A + F := by
  constructor <;> nlinarith [sq_nonneg (R - A), sq_nonneg (R - A - F), mul_nonneg hA hF]

/-- `‖r(y, t)‖² = (y₁²/2)² + (f_a(y) - t)²`. -/
theorem resid_sq (a : ℝ) (y : ℝ²) (t : ℝ) :
    Constrained.targetResidual (objA a) conC t y ^ 2 = (y 0 ^ 2 / 2) ^ 2 + (objA a y - t) ^ 2 := by
  rw [Constrained.targetResidual_sq, norm_conC]

/-- `X` is closed. -/
theorem isClosed_boxX : IsClosed boxX :=
  (isClosed_le (continuous_abs.comp (EuclideanSpace.proj (0 : Fin 2)).continuous)
    continuous_const).inter
  (isClosed_le (continuous_abs.comp (EuclideanSpace.proj (1 : Fin 2)).continuous)
    continuous_const)

/-- `X` is convex. -/
theorem convex_boxX : Convex ℝ boxX := by
  have e : boxX = (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ) ⁻¹' Icc (-1) 1 ∩
      (EuclideanSpace.proj (1 : Fin 2) : ℝ² →L[ℝ] ℝ) ⁻¹' Icc (-1) 1 := by
    ext x; simp [boxX, abs_le]
  rw [e]
  exact ((convex_Icc _ _).linear_preimage
      (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).toLinearMap).inter
    ((convex_Icc _ _).linear_preimage
      (EuclideanSpace.proj (1 : Fin 2) : ℝ² →L[ℝ] ℝ).toLinearMap)

/-- `X ⊆ B(0, 2)`. -/
theorem boxX_subset_ball : boxX ⊆ ball 0 2 := by
  intro x hx
  obtain ⟨h0, h1⟩ := hx
  rw [mem_ball_zero_iff, EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_lt' (by norm_num)]
  simp only [Real.norm_eq_abs, sq_abs]
  have := abs_le.1 h0
  have := abs_le.1 h1
  nlinarith

/-- `c` is smooth. -/
theorem contDiff_conC : ContDiff ℝ ⊤ conC := by
  have h : ContDiff ℝ ⊤ (fun x : ℝ² => x 0 ^ 2 / 2) :=
    ((contDiff_piLp_apply (p := 2) (i := (0 : Fin 2))).pow 2).div_const 2
  exact h.smul contDiff_const

/-- `f_a` is smooth. -/
theorem contDiff_objA (a : ℝ) : ContDiff ℝ ⊤ (objA a) := contDiff_linF _ _

/-- `‖∇f_a‖ ≤ 2` for `|a| ≤ 1`. -/
theorem deriv_objA_le {a : ℝ} (ha : |a| ≤ 1) (y : ℝ²) :
    ∀ i ∈ Finset.Icc 1 1, ‖iteratedFDeriv ℝ i (objA a) y‖ ≤ 2 := fun i hi =>
  (norm_iteratedFDeriv_linF_le 1 (-a) y i hi).trans (by rw [abs_one, abs_neg]; linarith)

/-- f.B.Fb on `ℱ_1`: `-2 ≤ f_a ≤ 2` on `X` for `|a| ≤ 1`. -/
theorem assumptionBFb {a : ℝ} (ha : |a| ≤ 1) :
    Chapter07.AssumptionBFb (objA a) conC boxX 1 (-2) 2 := by
  intro x hx
  obtain ⟨⟨h0, h1⟩, -⟩ := hx
  have h2 : |a * x 1| ≤ 1 := by rw [abs_mul]; nlinarith [abs_nonneg a, abs_nonneg (x 1)]
  have := abs_le.1 h0
  have := abs_le.1 h2
  rw [objA_apply]
  constructor <;> linarith

/-- f.D1pLB.X and c.D1pLB.X hold on `X₀ = B(0, 2)` for every `p`. -/
theorem assumptionD1pLBX (a : ℝ) (p : ℕ) :
    (∃ L B : ℕ → ℝ, AssumptionD1pLBX (objA a) boxX (ball 0 2) p L B) ∧
      ∃ L B : ℕ → ℝ, AssumptionCD1pLBX conC boxX (ball 0 2) p L B := by
  refine ⟨exists_assumptionD1pLBX_ball ((contDiff_objA a).of_le le_top) boxX_subset_ball p, ?_⟩
  have hc0 : ContDiff ℝ ∞ (fun x => conC x 0) :=
    ((contDiff_piLp_apply (p := 2) (i := (0 : Fin 1))).comp contDiff_conC).of_le le_top
  obtain ⟨L, B, h⟩ := exists_assumptionD1pLBX_ball hc0 boxX_subset_ball p
  exact ⟨L, B, isOpen_ball, convex_ball 0 2, boxX_subset_ball, fun i => by
    rw [Subsingleton.elim i 0]; exact h⟩

/-! #### The parameters and the run -/

section Run

variable (u : ℝ) (N : ℕ)

/-- The tolerances `ε₀ = u²/2 + u³/2`, `ε_j = 3u/2` (`j ≥ 1`). -/
noncomputable def eps : ℕ → ℝ := fun j => if j = 0 then u ^ 2 / 2 + u ^ 3 / 2 else 3 * u / 2

/-- The overshoot `E_j = (u³/2)(1 - j/(4(N + 1)))` of the `(j-1)`-th INNER call below its
target. -/
noncomputable def ov (j : ℕ) : ℝ := u ^ 3 / 2 * (1 - j / (4 * (N + 1)))

/-- The targets `t_k = 1 - ε₀ - u³ (k - 1) + u³ (k (k + 1) - 2)/(8 (N + 1))`, so that
`t_{k+1} = t_k - 2 E_{k+1}`. -/
noncomputable def tgt (k : ℕ) : ℝ :=
  1 - (u ^ 2 / 2 + u ^ 3 / 2) - u ^ 3 * ((k : ℝ) - 1) +
    u ^ 3 * ((k : ℝ) * (k + 1) - 2) / (8 * (N + 1))

open Classical in
/-- The amount `t_k - f(x_{k+1})` of the `k`-th call: `E_{k+1}` for `k < N`, `0` for `k = N`. -/
noncomputable def gap (k : ℕ) : ℝ := if k < N then ov u N (k + 1) else 0

/-- The outer iterates: `x₁ = (0, -1)`, `x_{k+1} = (u, u - t_k + gap_k)` for `k ≥ 1`. -/
noncomputable def xs : ℕ → ℝ²
  | 0 => pt 0 (-1)
  | k + 1 => if k = 0 then pt 0 (-1) else pt u (u - (tgt u N k - gap u N k))

/-- The Phase-2 sequences: iterates `xs`, targets `tgt`, radii `1`, and the `k`-th INNER call
makes one successful iteration from `x_k` to `x_{k+1}`. -/
noncomputable def run : TPqpSeq 2 := TPqpSeq.oneStep (xs u N) (tgt u N)

end Run

section Facts

variable {u : ℝ} {N : ℕ}

/-- `ε₀ = u²/2 + u³/2`. -/
theorem eps_zero : eps u 0 = u ^ 2 / 2 + u ^ 3 / 2 := by simp [eps]

/-- `ε₁ = 3u/2`. -/
theorem eps_one : eps u 1 = 3 * u / 2 := by simp [eps]

/-- `t₁ = 1 - ε₀`. -/
theorem tgt_one : tgt u N 1 = 1 - (u ^ 2 / 2 + u ^ 3 / 2) := by simp [tgt]; norm_num

/-- The target update of case (b): `t_{k+1} = t_k - 2 E_{k+1}`. -/
theorem tgt_succ (k : ℕ) : tgt u N (k + 1) = tgt u N k - 2 * ov u N (k + 1) := by
  unfold tgt ov
  have : (8 * ((N : ℝ) + 1)) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- `x₁ = (0, -1)`. -/
theorem xs_one : xs u N 1 = pt 0 (-1) := by simp [xs]

/-- `x_{k+1} = (u, u - t_k + gap_k)` for `k ≥ 1`. -/
theorem xs_succ {k : ℕ} (hk : 1 ≤ k) :
    xs u N (k + 1) = pt u (u - (tgt u N k - gap u N k)) := by
  simp [xs, show k ≠ 0 by omega]

/-- The first coordinate of `x_{k+1}`, `k ≥ 1`, is `u`. -/
theorem xs_succ_zero {k : ℕ} (hk : 1 ≤ k) : xs u N (k + 1) 0 = u := by
  rw [xs_succ hk, pt_zero]

/-- `f(x_{k+1}) = t_k - gap_k` for `k ≥ 1`. -/
theorem objF_xs_succ {k : ℕ} (hk : 1 ≤ k) : objA 1 (xs u N (k + 1)) = tgt u N k - gap u N k := by
  rw [xs_succ hk, objF_pt]; ring

/-- `gap_k = E_{k+1}` for `k < N`. -/
theorem gap_of_lt {k : ℕ} (hk : k < N) : gap u N k = ov u N (k + 1) := by simp [gap, hk]

/-- `gap_N = 0`: the last call lands on its target. -/
theorem gap_self : gap u N N = 0 := by simp [gap]

variable (hu : 0 < u)
include hu

/-- `E_j ≤ u³/2`. -/
theorem ov_le (j : ℕ) : ov u N j ≤ u ^ 3 / 2 := by
  unfold ov
  have : 0 ≤ (j : ℝ) / (4 * (N + 1)) := by positivity
  have : 0 < u ^ 3 / 2 := by positivity
  nlinarith

/-- `E_j ≥ 3u³/8` for `j ≤ N + 1`. -/
theorem le_ov {j : ℕ} (hj : j ≤ N + 1) : 3 / 4 * (u ^ 3 / 2) ≤ ov u N j := by
  unfold ov
  have hN : (0 : ℝ) < 4 * (N + 1) := by positivity
  have : (j : ℝ) / (4 * (N + 1)) ≤ 1 / 4 := by
    rw [div_le_iff₀ hN]
    have : (j : ℝ) ≤ N + 1 := by exact_mod_cast hj
    linarith
  have : 0 < u ^ 3 / 2 := by positivity
  nlinarith

/-- `E_{j+1} ≤ E_j`. -/
theorem ov_succ_le (j : ℕ) : ov u N (j + 1) ≤ ov u N j := by
  unfold ov
  have hN : (0 : ℝ) < 4 * (N + 1) := by positivity
  have : (j : ℝ) / (4 * (N + 1)) ≤ ((j + 1 : ℕ) : ℝ) / (4 * (N + 1)) := by
    gcongr; linarith
  have : 0 < u ^ 3 / 2 := by positivity
  nlinarith

/-- `E_{j+1} < E_j`. -/
theorem ov_succ_lt (j : ℕ) : ov u N (j + 1) < ov u N j := by
  unfold ov
  have hN : (0 : ℝ) < 4 * (N + 1) := by positivity
  have : (j : ℝ) / (4 * (N + 1)) < ((j + 1 : ℕ) : ℝ) / (4 * (N + 1)) := by
    gcongr; linarith
  have : 0 < u ^ 3 / 2 := by positivity
  nlinarith

/-- `gap_k < E_k` for `k ≤ N`. -/
theorem gap_lt_ov {k : ℕ} (hk : k ≤ N) : gap u N k < ov u N k := by
  unfold gap
  split_ifs with h
  · exact ov_succ_lt hu k
  · exact (by positivity : (0 : ℝ) < 3 / 4 * (u ^ 3 / 2)).trans_le (le_ov hu (by omega))

/-- `gap_k ≥ 0`. -/
theorem gap_nonneg (k : ℕ) : 0 ≤ gap u N k := by
  unfold gap
  split_ifs with h
  · exact (by positivity : (0 : ℝ) ≤ 3 / 4 * (u ^ 3 / 2)).trans (le_ov hu (by omega))
  · exact le_rfl

/-- `gap_k ≤ u³/2`. -/
theorem gap_le (k : ℕ) : gap u N k ≤ u ^ 3 / 2 := by
  unfold gap
  split_ifs
  · exact ov_le hu _
  · positivity

/-- `1 - ε₀ - u³ N ≤ t_k ≤ 1 - ε₀` for `k ∈ [1, N]`. -/
theorem tgt_mem {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    1 - (u ^ 2 / 2 + u ^ 3 / 2) - u ^ 3 * N ≤ tgt u N k ∧
      tgt u N k ≤ 1 - (u ^ 2 / 2 + u ^ 3 / 2) := by
  unfold tgt
  have hN : (0 : ℝ) < 8 * (N + 1) := by positivity
  have hK1 : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hKN : (k : ℝ) ≤ N := by exact_mod_cast hkN
  have hu3 : 0 < u ^ 3 := by positivity
  have h0 : 0 ≤ u ^ 3 * ((k : ℝ) * (k + 1) - 2) / (8 * (N + 1)) := by
    apply div_nonneg _ hN.le
    apply mul_nonneg hu3.le
    nlinarith
  have h1 : u ^ 3 * ((k : ℝ) * (k + 1) - 2) / (8 * (N + 1)) ≤ u ^ 3 * ((k : ℝ) - 1) := by
    rw [div_le_iff₀ hN]
    have : ((k : ℝ) * (k + 1) - 2) ≤ ((k : ℝ) - 1) * (8 * (N + 1)) := by nlinarith
    nlinarith
  constructor <;> nlinarith

end Facts

section Run2

variable {u : ℝ} {N : ℕ} (hu : 0 < u) (hu7 : u ≤ 1 / 7) (hNu : u ^ 3 * N ≤ 1)
include hu

omit hu in
/-- `f(x_{k+1}) - t_{k+1} = E_{k+1}` for `k ∈ [1, N)`. -/
theorem objF_xs_sub {k : ℕ} (hk1 : 1 ≤ k) (hkN : k < N) :
    objA 1 (xs u N (k + 1)) - tgt u N (k + 1) = ov u N (k + 1) := by
  rw [objF_xs_succ hk1, gap_of_lt hkN, tgt_succ]; ring

omit hu in
/-- `t_k - f(x_{k+1}) = gap_k`. -/
theorem tgt_sub_objF {k : ℕ} (hk1 : 1 ≤ k) :
    objA 1 (xs u N (k + 1)) - tgt u N k = -gap u N k := by
  rw [objF_xs_succ hk1]; ring

include hu7 hNu in
/-- The iterates `x_k`, `k ∈ [1, N + 1]`, lie in `X`. -/
theorem xs_mem {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N + 1) : xs u N k ∈ boxX := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [xs_one]; simp [boxX]
  · rw [xs_succ hj]
    obtain ⟨h1, h2⟩ := tgt_mem hu hj (by omega : j ≤ N)
    have hg0 := gap_nonneg hu (N := N) j
    have hg1 := gap_le hu (N := N) j
    have hu2 : u ^ 2 ≤ u / 7 := by nlinarith
    have hu3 : u ^ 3 ≤ u ^ 2 / 7 := by nlinarith
    simp only [boxX, mem_ofPred_eq, pt_zero, pt_one]
    refine ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by nlinarith, by nlinarith⟩⟩

omit hu in
/-- `‖r(y, t)‖² = (u²/2)² + (f(y) - t)²` at the points with first coordinate `u`. -/
theorem resid_sq_of {y : ℝ²} (hy : y 0 = u) (t : ℝ) :
    Constrained.targetResidual (objA 1) conC t y ^ 2 = (u ^ 2 / 2) ^ 2 + (objA 1 y - t) ^ 2 := by
  rw [resid_sq, hy]

omit hu in
/-- `‖r(x_{k+1}, t_k)‖² = (u²/2)² + gap_k²`. -/
theorem resid_end {k : ℕ} (hk1 : 1 ≤ k) :
    Constrained.targetResidual (objA 1) conC (tgt u N k) (xs u N (k + 1)) ^ 2 =
      (u ^ 2 / 2) ^ 2 + gap u N k ^ 2 := by
  rw [resid_sq_of (xs_succ_zero hk1), tgt_sub_objF hk1]; ring

omit hu in
/-- `‖r(x_{k+1}, t_{k+1})‖² = (u²/2)² + E_{k+1}²` for `k ∈ [1, N)`. -/
theorem resid_new {k : ℕ} (hk1 : 1 ≤ k) (hkN : k < N) :
    Constrained.targetResidual (objA 1) conC (tgt u N (k + 1)) (xs u N (k + 1)) ^ 2 =
      (u ^ 2 / 2) ^ 2 + ov u N (k + 1) ^ 2 := by
  rw [resid_sq_of (xs_succ_zero hk1), objF_xs_sub hk1 hkN]

/-- `‖r(x_k, t_k)‖² ≥ (u²/2)² + E_k²` for `k ∈ [1, N]`. -/
theorem resid_cur_sq {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    (u ^ 2 / 2) ^ 2 + ov u N k ^ 2 ≤
      Constrained.targetResidual (objA 1) conC (tgt u N k) (xs u N k) ^ 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [resid_sq, xs_one, tgt_one, objF_pt]
    simp only [pt_zero]
    have h0 := le_ov hu (N := N) (j := 1) (by omega)
    have h1 := ov_le hu (N := N) 1
    have : 0 < u ^ 2 / 2 := by positivity
    nlinarith
  · rw [resid_new hj (by omega)]

omit hu in
/-- `‖r(x₁, t₁)‖ = ε₀ = u²/2 + u³/2`. -/
theorem resid_one (hu : 0 < u) :
    Constrained.targetResidual (objA 1) conC (tgt u N 1) (xs u N 1) = u ^ 2 / 2 + u ^ 3 / 2 := by
  rw [Constrained.targetResidual_def, xs_one, norm_conC, tgt_one, objF_pt]
  simp only [pt_zero]
  rw [show ((0 : ℝ) ^ 2 / 2) ^ 2 + (0 - -1 - (1 - (u ^ 2 / 2 + u ^ 3 / 2))) ^ 2 =
    (u ^ 2 / 2 + u ^ 3 / 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]

/-- `u²/2 ≤ ‖r(x_k, t_k)‖ ≤ u²/2 + u³/2 = ε₀` for `k ∈ [1, N]`. -/
theorem resid_cur_mem {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    u ^ 2 / 2 ≤ Constrained.targetResidual (objA 1) conC (tgt u N k) (xs u N k) ∧
      Constrained.targetResidual (objA 1) conC (tgt u N k) (xs u N k) ≤
        u ^ 2 / 2 + u ^ 3 / 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [resid_one hu]; constructor <;> nlinarith [pow_pos hu 3]
  · have h := resid_bounds Constrained.targetResidual_nonneg (resid_new hj (by omega))
      (by positivity) ((by positivity : (0 : ℝ) ≤ 3 / 4 * (u ^ 3 / 2)).trans
        (le_ov hu (N := N) (j := j + 1) (by omega)))
    exact ⟨h.1, h.2.trans (by linarith [ov_le hu (N := N) (j + 1)])⟩

/-- `‖r(x_k, t_k)‖ ≥ u²/2` for `k ∈ [1, N]`. -/
theorem resid_cur_ge {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    u ^ 2 / 2 ≤ Constrained.targetResidual (objA 1) conC (tgt u N k) (xs u N k) :=
  (resid_cur_mem hu hk1 hkN).1

/-- `‖r(x_k, t_k)‖ ≤ u²/2 + u³/2 = ε₀` for `k ∈ [1, N]`. -/
theorem resid_cur_le {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    Constrained.targetResidual (objA 1) conC (tgt u N k) (xs u N k) ≤ u ^ 2 / 2 + u ^ 3 / 2 :=
  (resid_cur_mem hu hk1 hkN).2

omit hu in
/-- `‖r(x_{k+1}, t_k)‖ ≥ u²/2`. -/
theorem resid_end_ge {k : ℕ} (hk1 : 1 ≤ k) :
    u ^ 2 / 2 ≤ Constrained.targetResidual (objA 1) conC (tgt u N k) (xs u N (k + 1)) := by
  have h := resid_end (u := u) (N := N) hk1
  have := Constrained.targetResidual_nonneg (f := objA 1) (c := conC) (t := tgt u N k)
    (x := xs u N (k + 1))
  nlinarith [sq_nonneg (gap u N k)]

include hu7 hNu in
/-- **INNER's test (14.3.19) holds at the end of every call** `k ∈ [1, N]`, for `β ≥ 2/3`:
`‖∇μ(x_{k+1}, t_k)‖ ≤ u³/2 ≤ β ‖r(x_k, t_k)‖ ε₁`. -/
theorem innerTest {β : ℝ} (hβ : 2 / 3 ≤ β) {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    (run u N).InnerTest (objA 1) conC boxX 1 β (eps u) k := by
  intro j hj
  obtain rfl : j = 1 := by simpa using hj
  change Optimization.taylorMeasure
      (ftaylorSeries ℝ (Constrained.targetMerit (objA 1) conC (tgt u N k)) (xs u N (k + 1))) 1 1
      {d | xs u N (k + 1) + d ∈ boxX} ≤
    β * Constrained.targetResidual (objA 1) conC (tgt u N k) (xs u N k) * eps u 1 * 1 ^ 1 / (1 : ℕ)!
  have h0 : (0 : ℝ²) ∈ {d | xs u N (k + 1) + d ∈ boxX} := by
    simpa using xs_mem hu hu7 hNu (k := k + 1) (by omega) (by omega)
  refine (measure_le _ _ h0).trans ?_
  rw [xs_succ_zero hk1, tgt_sub_objF hk1, eps_one]
  have hg0 := gap_nonneg hu (N := N) k
  have hg1 := gap_le hu (N := N) k
  have hR := resid_cur_ge hu hk1 hkN
  have hs : √((u ^ 3 / 2 + -gap u N k) ^ 2 + (-gap u N k) ^ 2) ≤ u ^ 3 / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  refine hs.trans ?_
  simp only [one_pow, mul_one, Nat.factorial_one, Nat.cast_one, div_one]
  have : β * (u ^ 2 / 2) * (3 * u / 2) ≤
      β * Constrained.targetResidual (objA 1) conC (tgt u N k) (xs u N k) * (3 * u / 2) := by
    gcongr
  nlinarith

include hu7 hNu in
/-- **(14.3.34) fails at `(x_{k+1}, t_{k+1})`** for `k ∈ [1, N)`: along `d = -e₁` the decrease
is `u³/2 + E_{k+1} ≥ 7u³/8 > ε₁ ‖r(x_{k+1}, t_{k+1})‖`. -/
theorem not_meritCrit_new {k : ℕ} (hk1 : 1 ≤ k) (hkN : k < N) :
    ¬ meritCrit (objA 1) conC boxX 1 (eps u) (tgt u N (k + 1)) (xs u N (k + 1)) (fun _ => 1) := by
  intro h
  have h1 := h 1 (by simp)
  simp only [one_pow, mul_one, Nat.factorial_one, Nat.cast_one, div_one] at h1
  have hmem := xs_mem hu hu7 hNu (k := k + 1) (by omega) (by omega)
  have hS : EuclideanSpace.single 0 (-1) ∈ {d | xs u N (k + 1) + d ∈ boxX} := by
    simp only [boxX, mem_ofPred_eq] at hmem ⊢
    have e0 : (EuclideanSpace.single (0 : Fin 2) (-1 : ℝ)) 0 = -1 := by simp
    have e1 : (EuclideanSpace.single (0 : Fin 2) (-1 : ℝ)) 1 = 0 := by simp
    simp only [PiLp.add_apply, e0, e1, add_zero, xs_succ_zero hk1]
    exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, hmem.2⟩
  have hlow := le_measure (xs u N (k + 1)) (tgt u N (k + 1)) hS
  rw [xs_succ_zero hk1, objF_xs_sub hk1 hkN] at hlow
  rw [eps_one] at h1
  have hov := le_ov hu (N := N) (j := k + 1) (by omega)
  have hR := resid_cur_le hu (N := N) (k := k + 1) (by omega) (by omega)
  have : 3 * u / 2 * Constrained.targetResidual (objA 1) conC (tgt u N (k + 1)) (xs u N (k + 1)) ≤
      3 * u / 2 * (u ^ 2 / 2 + u ^ 3 / 2) := by gcongr
  have hu3 : 0 < u ^ 3 := by positivity
  have hu4 : u ^ 4 ≤ u ^ 3 / 7 := by nlinarith
  have e : 3 * u / 2 * (u ^ 2 / 2 + u ^ 3 / 2) = 3 / 4 * u ^ 3 + 3 / 4 * u ^ 4 := by ring
  linarith

include hu7 hNu in
/-- The third test of (14.3.32) holds at `(x_{N+1}, t_N)`: `‖∇μ(x_{N+1}, t_N)‖ = u³/2 ≤
ε₁ ‖r(x_{N+1}, t_N)‖ = 3u³/4`. -/
theorem meritCrit_end (hN : 1 ≤ N) :
    meritCrit (objA 1) conC boxX 1 (eps u) (tgt u N N) (xs u N (N + 1)) (fun _ => 1) := by
  intro j hj
  obtain rfl : j = 1 := by simpa using hj
  simp only [one_pow, mul_one, Nat.factorial_one, Nat.cast_one, div_one]
  have h0 : (0 : ℝ²) ∈ {d | xs u N (N + 1) + d ∈ boxX} := by
    simpa using xs_mem hu hu7 hNu (k := N + 1) (by omega) le_rfl
  refine (measure_le _ _ h0).trans ?_
  rw [xs_succ_zero hN, tgt_sub_objF hN, gap_self, eps_one]
  have hR := resid_end_ge (u := u) (N := N) hN
  have hs : √((u ^ 3 / 2 + -0) ^ 2 + (-0) ^ 2) ≤ u ^ 3 / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  refine hs.trans ?_
  have : 3 * u / 2 * (u ^ 2 / 2) ≤
      3 * u / 2 * Constrained.targetResidual (objA 1) conC (tgt u N N) (xs u N (N + 1)) := by
    gcongr
  nlinarith

/-- **`μ(·, t_k)` decreases strictly along every call** `k ∈ [1, N]`. -/
theorem merit_lt {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    Constrained.targetMerit (objA 1) conC (tgt u N k) (xs u N (k + 1)) <
      Constrained.targetMerit (objA 1) conC (tgt u N k) (xs u N k) := by
  rw [Constrained.targetMerit_eq, Constrained.targetMerit_eq, resid_end hk1]
  have h1 := resid_cur_sq hu hk1 hkN
  have h2 := gap_nonneg hu (N := N) k
  have h3 := gap_lt_ov hu (N := N) hkN
  nlinarith

include hu7 in
/-- `θ ε₀ ≤ u²/2` for `θ = 3/4`. -/
theorem theta_eps_le : 3 / 4 * eps u 0 ≤ u ^ 2 / 2 := by
  rw [eps_zero]; nlinarith [pow_pos hu 2]

omit hu in
/-- The tolerances are positive. -/
theorem eps_pos (hu : 0 < u) (j : ℕ) : 0 < eps u j := by
  unfold eps; split_ifs <;> positivity

include hu7 in
/-- The tolerances are at most `1`. -/
theorem eps_le_one (j : ℕ) : eps u j ≤ 1 := by
  unfold eps; split_ifs <;> nlinarith [pow_pos hu 2, pow_pos hu 3]

include hu7 in
/-- No outer iteration `k ≥ 1` is in `𝒦_a`. -/
theorem not_isKa {k : ℕ} (hk1 : 1 ≤ k) : ¬ (run u N).IsKa (objA 1) conC (3 / 4) (eps u) k := by
  rw [Constrained.HighOrderTargetSeq.isKa_iff]
  rw [not_lt]
  exact (theta_eps_le hu hu7).trans (resid_end_ge hk1)

include hu7 in
/-- The outer iterations `k ∈ [1, N)` are in `𝒦_b`. -/
theorem isKb {k : ℕ} (hk1 : 1 ≤ k) (hkN : k < N) :
    (run u N).IsKb (objA 1) conC (3 / 4) (eps u) k := by
  refine ⟨(theta_eps_le hu hu7).trans (resid_end_ge hk1), ?_⟩
  change objA 1 (xs u N (k + 1)) < tgt u N k
  rw [objF_xs_succ hk1, gap_of_lt hkN]
  have := le_ov hu (N := N) (j := k + 1) (by omega)
  have : 0 < u ^ 3 := by positivity
  linarith

omit hu in
/-- The outer iteration `N` is not in `𝒦_b`: `f(x_{N+1}) = t_N`. -/
theorem not_isKb_self (hN : 1 ≤ N) : ¬ (run u N).IsKb (objA 1) conC (3 / 4) (eps u) N := by
  intro h
  have h2 := h.2
  change objA 1 (xs u N (N + 1)) < tgt u N N at h2
  rw [objF_xs_succ hN, gap_self] at h2
  linarith

include hu7 in
/-- Phase 2 stops at `N` (case (c)). -/
theorem stop_self (hN : 1 ≤ N) : (run u N).Stop (objA 1) conC boxX 1 (3 / 4) (eps u) N :=
  Or.inl ⟨not_isKa hu hu7 hN, not_isKb_self hN⟩

include hu7 hNu in
/-- Phase 2 does not stop at `k ∈ [1, N)`. -/
theorem not_stop {k : ℕ} (hk1 : 1 ≤ k) (hkN : k < N) :
    ¬ (run u N).Stop (objA 1) conC boxX 1 (3 / 4) (eps u) k := by
  rintro (⟨-, hb⟩ | ⟨-, hm⟩)
  · exact hb (isKb hu hu7 hk1 hkN)
  · exact not_meritCrit_new hu hu7 hNu hk1 hkN hm

include hu7 hNu in
/-- Phase 2 does not stop before `N`. -/
theorem before_self : (run u N).Before (objA 1) conC boxX 1 (3 / 4) (eps u) N :=
  fun _ hj1 hjN => not_stop hu hu7 hNu hj1 hjN

include hu7 in
/-- Every outer iteration reached is at most `N`. -/
theorem le_of_before (hN : 1 ≤ N) {k : ℕ}
    (h : (run u N).Before (objA 1) conC boxX 1 (3 / 4) (eps u) k) : k ≤ N := by
  by_contra hk
  exact h N hN (by omega) (stop_self hu hu7 hN)

include hu7 hNu in
/-- Phase 2 terminates at the outer iteration `N`. -/
theorem isEnd (hN : 1 ≤ N) : (run u N).IsEnd (objA 1) conC boxX 1 (3 / 4) (eps u) N :=
  ⟨hN, stop_self hu hu7 hN, before_self hu hu7 hNu⟩

include hu7 hNu in
/-- **The sequences form a Phase-2 run of TPqp-GC** for `θ = 3/4` and every `β ∈ (0, θ]`. -/
theorem isTPqpGCPhase2 (hN : 1 ≤ N) {β : ℝ} (hβ : 0 < β) (hβθ : β ≤ 3 / 4) :
    IsTPqpGCPhase2 (objA 1) conC boxX 1 (3 / 4) β (eps u) (pt 0 (-1)) (run u N) := by
  have hc1 : ‖conC (pt 0 (-1))‖ = 0 := by rw [norm_conC]; simp
  rw [← xs_one (u := u) (N := N)]
  refine isTPqpGCPhase2_oneStep (by norm_num) (by norm_num) hβ hβθ (fun j _ => eps_pos hu j)
    (fun j _ => eps_le_one hu hu7 j) (by rw [xs_one]; simp [boxX]) ?_ ?_
    (fun k hk1 hk => xs_mem hu hu7 hNu (by omega) (by have := le_of_before hu hu7 hN hk; omega))
    (fun k hk1 hk => ?_) (fun k hk1 hk => merit_lt hu hk1 (le_of_before hu hu7 hN hk) |>.le)
    (fun k hk1 hk => (theta_eps_le hu hu7).trans (resid_cur_ge hu hk1 (le_of_before hu hu7 hN hk)))
    (fun k hk1 _ ha => absurd ha (not_isKa hu hu7 hk1)) fun k hk1 hk hb => ?_
  · rw [xs_one, hc1]; exact (mul_pos (by norm_num) (eps_pos hu 0)).le
  · rw [xs_one, hc1, tgt_one, objF_pt, eps_zero]
    rw [show (u ^ 2 / 2 + u ^ 3 / 2) ^ 2 - (0 : ℝ) ^ 2 = (u ^ 2 / 2 + u ^ 3 / 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
    ring
  · rcases Nat.lt_or_ge k N with hlt | hge
    · exact Or.inr (Or.inl (isKb hu hu7 hk1 hlt).2)
    · obtain rfl : k = N := by have := le_of_before hu hu7 hN hk; omega
      exact Or.inr (Or.inr (meritCrit_end hu hu7 hNu hN))
  · have hlt : k < N :=
      lt_of_le_of_ne (le_of_before hu hu7 hN hk) fun h => not_isKb_self hN (h ▸ hb)
    rw [objF_xs_succ hk1, gap_of_lt hlt, tgt_succ]
    ring

include hu7 hNu in
/-- **The INNER calls satisfy the strong contract** `IsInnerPhaseRunStrong` for every `β ∈ [2/3,
3/4]`, every `κ_decr`, exponents `π`, `κ_uns + κ_unc ≥ 1` and radii `ρ₁ ≤ 1`: each call makes one
successful iteration and ends at a point passing INNER's test, so no decrease is required. -/
theorem isInnerPhaseRunStrong (hN : 1 ≤ N) {β : ℝ} (hβ : 2 / 3 ≤ β) {κdecr κuns κunc : ℝ}
    {π ρ : ℕ → ℝ} (hκ : 1 ≤ κuns + κunc) (hρ : ρ 1 ≤ 1) :
    IsInnerPhaseRunStrong (objA 1) conC boxX 1 (3 / 4) β (eps u) (run u N) κdecr κuns κunc π ρ :=
  isInnerPhaseRunStrong_oneStep hκ (fun j hj => by obtain rfl : j = 1 := by simpa using hj
                                                   exact hρ)
    fun k hk1 hk => innerTest hu hu7 hNu hβ hk1 (le_of_before hu hu7 hN hk)

include hu7 hNu in
/-- **INNER's test fails at the start of every call** `k ∈ [1, N]` for `β ≤ 3/4`: along `-e₁` the
decrease of the linear model of `μ(·, t_k)` at `x_k` exceeds `β ‖r(x_k, t_k)‖ ε₁`. So an INNER
terminating only at points passing its test must move in every call. -/
theorem not_innerTest_start {β : ℝ} (hβ : β ≤ 3 / 4) {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    β * Constrained.targetResidual (objA 1) conC (tgt u N k) (xs u N k) * eps u 1 <
      Optimization.taylorMeasure
        (ftaylorSeries ℝ (Constrained.targetMerit (objA 1) conC (tgt u N k)) (xs u N k)) 1 1
        {d | xs u N k + d ∈ boxX} := by
  have hmem := xs_mem hu hu7 hNu (k := k) hk1 (by omega)
  have hS : EuclideanSpace.single 0 (-1) ∈ {d | xs u N k + d ∈ boxX} := by
    simp only [boxX, mem_ofPred_eq] at hmem ⊢
    have e0 : (EuclideanSpace.single (0 : Fin 2) (-1 : ℝ)) 0 = -1 := by simp
    have e1 : (EuclideanSpace.single (0 : Fin 2) (-1 : ℝ)) 1 = 0 := by simp
    simp only [PiLp.add_apply, e0, e1, add_zero]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [xs_one]; simp
    · rw [xs_succ_zero hj]
      exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, hmem.2⟩
  refine lt_of_lt_of_le ?_ (le_measure (xs u N k) (tgt u N k) hS)
  rw [eps_one]
  have hb : β * Constrained.targetResidual (objA 1) conC (tgt u N k) (xs u N k) * (3 * u / 2) ≤
      3 / 4 * (u ^ 2 / 2 + u ^ 3 / 2) * (3 * u / 2) :=
    mul_le_mul_of_nonneg_right (mul_le_mul hβ (resid_cur_le hu hk1 hkN)
      Constrained.targetResidual_nonneg (by norm_num)) (by positivity)
  refine hb.trans_lt ?_
  have hu3 : 0 < u ^ 3 := by positivity
  have hu4 : u ^ 4 ≤ u ^ 3 / 7 := by nlinarith
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · -- `x₁ = (0, -1)`: the decrease is `ε₀`
    rw [xs_one, objF_pt, tgt_one]
    simp only [pt_zero]
    nlinarith [pow_pos hu 2]
  · -- `x_k = (u, ·)` with `f(x_k) - t_k = E_k ≥ 3u³/8`
    rw [xs_succ_zero hj, objF_xs_sub hj (by omega)]
    nlinarith [le_ov hu (N := N) (j := j + 1) (by omega)]

include hu7 in
/-- **The cost bounds (14.3.20)–(14.3.21) hold for every call** `k ∈ [1, N]`: for `β ∈ (0, 3/4]`,
`κ ≥ 8` and `π₁ ≥ 4/3`, the bound `κ (μ(x_k, t_k) - 0) (β ‖r(x_k, t_k)‖ ε₁)^{-π₁}` of a call of
INNER on `μ(·, t_k)` from `x^S = x_k` with tolerance `β ‖r(x_k, t_k)‖ ε₁` (and `f_low = 0`, the
lower bound of `μ`) is at least `2`. With `R = ‖r(x_k, t_k)‖ ≥ u²/2` and `w = β R ε₁`, one has
`w ≤ 1` and `w⁴ ≤ (2R²)³`, so `w^{π₁} ≤ w^{4/3} ≤ 2R²` and the bound is `≥ κ/4`. -/
theorem two_le_innerEvalBound {β : ℝ} (hβ : 0 < β) (hβθ : β ≤ 3 / 4) {κ : ℝ} (hκ : 8 ≤ κ)
    {π : ℕ → ℝ} (hπ : 4 / 3 ≤ π 1) {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    2 ≤ innerEvalBound κ π 1 (Constrained.targetMerit (objA 1) conC (tgt u N k) (xs u N k))
      (fun j => β * Constrained.targetResidual (objA 1) conC (tgt u N k) (xs u N k) * eps u j) := by
  rw [innerEvalBound_one]
  simp only [Constrained.targetMerit_eq, eps_one]
  set R := Constrained.targetResidual (objA 1) conC (tgt u N k) (xs u N k) with hR_def
  have hRlo := resid_cur_ge hu hk1 hkN
  have hRhi := resid_cur_le hu hk1 hkN
  have hR : 0 < R := lt_of_lt_of_le (by positivity) hRlo
  have hu2 : u ^ 2 ≤ 2 * R := by linarith
  set w := β * R * (3 * u / 2) with hw_def
  have hw0 : 0 < w := by positivity
  have hwle : w ≤ 9 / 8 * R * u := by
    rw [hw_def]
    have : β * R ≤ 3 / 4 * R := by gcongr
    nlinarith
  have hw1 : w ≤ 1 := by
    have : R ≤ 1 := by nlinarith [pow_pos hu 2, pow_pos hu 3]
    nlinarith
  have hw4 : w ^ 4 ≤ (2 * R ^ 2) ^ 3 := by
    calc w ^ 4 ≤ (9 / 8 * R * u) ^ 4 := by gcongr
      _ = (9 / 8) ^ 4 * R ^ 4 * (u ^ 2) ^ 2 := by ring
      _ ≤ (9 / 8) ^ 4 * R ^ 4 * (2 * R) ^ 2 := by gcongr
      _ ≤ (2 * R ^ 2) ^ 3 := by nlinarith [pow_pos hR 6]
  have hw43 : w ^ (4 / 3 : ℝ) ≤ 2 * R ^ 2 := by
    have e : w ^ (4 / 3 : ℝ) = (w ^ (4 : ℕ)) ^ (((3 : ℕ) : ℝ)⁻¹) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hw0.le]; norm_num
    rw [e, ← Real.pow_rpow_inv_natCast (by positivity : (0 : ℝ) ≤ 2 * R ^ 2) (by norm_num : 3 ≠ 0)]
    exact Real.rpow_le_rpow (by positivity) hw4 (by positivity)
  have hwπ : w ^ π 1 ≤ 2 * R ^ 2 := (Real.rpow_le_rpow_of_exponent_ge hw0 hw1 hπ).trans hw43
  have hwπ0 : 0 < w ^ π 1 := Real.rpow_pos_of_pos hw0 _
  rw [Real.rpow_neg hw0.le, ← div_eq_mul_inv, le_div_iff₀ hwπ0]
  nlinarith [sq_nonneg R]

end Run2

/-! #### The order -/

/-- With `u = 1/m`, `m ≥ 7`, and `π ≤ 3/2`, the book's order
`max(ε₀^{-1}, ε₀^{1-π} ε₁^{-π})` is at most `2 m² √m`. -/
theorem order_le {m : ℕ} (hm : 7 ≤ m) {π : ℝ} (hπ : π ≤ 3 / 2) :
    max (eps (1 / m) 0)⁻¹ (eps (1 / m) 0 ^ (1 - π) * eps (1 / m) 1 ^ (-π)) ≤
      2 * (m : ℝ) ^ 2 * √m := by
  have hm1 : (7 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  set u : ℝ := 1 / m with hu_def
  have hu : 0 < u := by positivity
  have hum : u * m = 1 := by rw [hu_def]; field_simp
  rw [eps_zero, eps_one]
  set e0 := u ^ 2 / 2 + u ^ 3 / 2 with he0
  have he0pos : 0 < e0 := by positivity
  have he0inv : e0⁻¹ ≤ 2 * (m : ℝ) ^ 2 := by
    rw [inv_le_comm₀ he0pos (by positivity)]
    have : (2 * (m : ℝ) ^ 2)⁻¹ = u ^ 2 / 2 := by rw [hu_def]; field_simp
    rw [this]
    have : 0 < u ^ 3 := by positivity
    linarith
  have he0le : e0 ≤ 1 := by
    have : u ≤ 1 / 7 := by
      rw [hu_def, div_le_div_iff₀ hm0 (by norm_num)]; linarith
    nlinarith [pow_pos hu 2, pow_pos hu 3]
  have hsq1 : 1 ≤ √(m : ℝ) := by rw [Real.one_le_sqrt]; linarith
  -- `ε₀^{1-π} ≤ 2m`
  have hA : e0 ^ (1 - π) ≤ 2 * m := by
    rcases le_or_gt π 1 with h1 | h1
    · exact (Real.rpow_le_one he0pos.le he0le (by linarith)).trans (by linarith)
    · have hinv1 : 1 ≤ e0⁻¹ := one_le_inv_iff₀.2 ⟨he0pos, he0le⟩
      rw [show 1 - π = -(π - 1) by ring, Real.rpow_neg he0pos.le, ← Real.inv_rpow he0pos.le]
      calc e0⁻¹ ^ (π - 1) ≤ e0⁻¹ ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hinv1 (by linarith)
        _ = √(e0⁻¹) := (Real.sqrt_eq_rpow _).symm
        _ ≤ √((2 * m) ^ 2) := Real.sqrt_le_sqrt (he0inv.trans (by nlinarith))
        _ = 2 * m := Real.sqrt_sq (by positivity)
  -- `ε₁^{-π} ≤ m √m`
  have hB : (3 * u / 2) ^ (-π) ≤ m * √m := by
    have h3 : (3 * u / 2)⁻¹ = 2 * m / 3 := by rw [hu_def]; field_simp
    have h31 : 1 ≤ 2 * (m : ℝ) / 3 := by
      rw [le_div_iff₀ (by norm_num)]; linarith
    rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), h3]
    calc (2 * (m : ℝ) / 3) ^ π ≤ (2 * m / 3) ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h31 hπ
      _ ≤ (m : ℝ) ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      _ = m * √m := by
          rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hm0, Real.rpow_one,
            ← Real.sqrt_eq_rpow]
  refine max_le (he0inv.trans (le_mul_of_one_le_right (by positivity) hsq1)) ?_
  calc e0 ^ (1 - π) * (3 * u / 2) ^ (-π) ≤ (2 * m) * (m * √m) :=
        mul_le_mul hA hB (by positivity) (by positivity)
    _ = 2 * (m : ℝ) ^ 2 * √m := by ring

/-- For `m > 4C²`, `C · 2 m² √m < m³`. -/
theorem lt_cube {m : ℕ} {C : ℝ} (hm : 7 ≤ m) (hC : 4 * C ^ 2 < m) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ 2 * (m : ℝ) ^ 2 * √m) : C * x < ((m ^ 3 : ℕ) : ℝ) := by
  have hm7 : (7 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  push_cast
  rcases le_or_gt C 0 with h | h
  · nlinarith [pow_pos hm0 3, mul_nonpos_of_nonpos_of_nonneg h hx0]
  · have hs : 2 * C < √m := by
      rw [Real.lt_sqrt (by positivity)]; nlinarith
    have hsq : √(m : ℝ) * √m = m := Real.mul_self_sqrt hm0.le
    calc C * x ≤ C * (2 * (m : ℝ) ^ 2 * √m) := by gcongr
      _ = (2 * C) * √m * m ^ 2 := by ring
      _ < √m * √m * m ^ 2 := by
          have : 0 < √(m : ℝ) := Real.sqrt_pos.2 hm0
          gcongr
      _ = (m : ℝ) ^ 3 := by rw [hsq]; ring

/-- **The parameters for a constant `C`**: `u = 1/m`, `N = m³` with `m = ⌈4C²⌉ + 7`, so that
the tolerances vanish as `C` grows and `N > C max(ε₀^{-1}, ε₀^{1-π} ε₁^{-π})` for `π ≤ 3/2`. -/
theorem exists_params (C : ℝ) : ∃ (u : ℝ) (N : ℕ), 0 < u ∧ u ≤ 1 / 7 ∧ u ^ 3 * N ≤ 1 ∧ 1 ≤ N ∧
    (1 ≤ C → eps u 0 ≤ C⁻¹ ∧ eps u 1 ≤ C⁻¹) ∧
    ∀ π : ℝ, π ≤ 3 / 2 → C * max (eps u 0)⁻¹ (eps u 0 ^ (1 - π) * eps u 1 ^ (-π)) < N := by
  set m : ℕ := ⌈4 * C ^ 2⌉₊ + 7 with hm_def
  have hm : 7 ≤ m := by omega
  have hm7 : (7 : ℝ) ≤ m := by exact_mod_cast hm
  have hmR : (0 : ℝ) < m := by linarith
  have hC : 4 * C ^ 2 < m := by
    have := Nat.le_ceil (4 * C ^ 2)
    rw [hm_def]; push_cast; linarith
  set u : ℝ := 1 / m with hu_def
  have hu : 0 < u := by positivity
  have hu7 : u ≤ 1 / 7 := by rw [hu_def, div_le_div_iff₀ hmR (by norm_num)]; linarith
  refine ⟨u, m ^ 3, hu, hu7, ?_, Nat.one_le_pow _ _ (by omega), fun hC1 => ?_, fun π hπ => ?_⟩
  · rw [hu_def]; push_cast; field_simp; exact le_rfl
  · have hmC : 2 * C ≤ m := by nlinarith
    have hε1 : eps u 1 ≤ C⁻¹ := by
      rw [eps_one, hu_def, le_inv_comm₀ (by positivity) (by linarith)]
      rw [show (3 * (1 / (m : ℝ)) / 2)⁻¹ = 2 * m / 3 by field_simp]
      linarith
    refine ⟨le_trans ?_ hε1, hε1⟩
    rw [eps_zero, eps_one]
    nlinarith [pow_pos hu 2, pow_pos hu 3]
  · have hx0 : 0 ≤ max (eps u 0)⁻¹ (eps u 0 ^ (1 - π) * eps u 1 ^ (-π)) :=
      (inv_pos.2 (eps_pos hu 0)).le.trans (le_max_left _ _)
    exact lt_cube hm hC hx0 (order_le hm hπ)

end Theorem1439Cex

open Theorem1439Cex PlaneCex in
/-- **Theorem 14.3.9 of [cartis2022evaluation] fails for a nonspecific INNER under the per-call
reading of its INNER hypotheses** (they are checked on the INNER calls of the run; read uniformly
over all admissible inputs, the cost hypothesis cannot be met here for `π₁ < 2`, see
`theorem_14_3_9_cost_hypothesis_unsatisfiable`, and the theorem is vacuous under that reading).
There is a problem (`n = 2`, `m = 1`, `q = 1`, `X = [-1, 1]²`, `f(x) = x₁ - x₂`,
`c(x) = x₁²/2`) satisfying the book's assumptions of the theorem — X.CNe (`AssumptionXCNe`, `X`
also convex), f.D1pLB.X and c.D1pLB.X on `X₀ = B(0, 2)` for every `p`, `‖∇f‖ ≤ 2`, and f.B.Fb on
`ℱ_1` with `f_low = -2`, `f_up = 2` — such that for every choice of the constants
`κ^A_{INNER,2}`, `κ^C_{INNER,2}`, `κ^S_{INNER,2}`, `κ^{F,ν}_INNER`, `κ^{D,ν}_INNER` of the theorem
there are tolerances `ε₀, ε₁ ∈ (0, 1]` (at most `(1 + 3(|κ^A| + |κ^C| + |κ^S|))⁻¹`) and sequences
terminating at `k_ε` (`Constrained.HighOrderTargetSeq.IsEnd`) with `#F = #D = k_ε + 1` evaluations,
`μ(·, t_k)`
decreasing strictly along each call, which for `θ = 3/4`, every `β ∈ [2/3, θ]` and every Phase-1
constant `β₁ ∈ (0, 1)` form a
TPqp-GC run (`algorithm_14_3_2`, Phase 2 entered at the feasible `x₀`) whose INNER calls satisfy
every hypothesis the book places on its nonspecific INNER, for all exponents `π₁ ∈ [4/3, 3/2]`
(which contains the ARqp-SC exponent `(p+1)/p` of (14.2.12) for `p ∈ {2, 3}`,
`Optimization.arqpPiOf_one_le`,
`Optimization.four_thirds_le_arqpPiOf_one`):

* (14.3.19): each Phase-2 call `INNER(μ(·, t_k), X, 1, x_k, β ‖r(x_k, t_k)‖ ε)` returns
  `x_{k+1} ∈ X` with radius `δ = 1` passing INNER's own test
  (`Constrained.HighOrderTargetSeq.InnerTest`), while that
  test fails at its starting point `x_k`, so that any INNER must move in every call;
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

and whose numbers of evaluations of `(f, c)` and of their derivatives exceed the printed bounds
`#^F_INNER,1 + #^F_INNER,2` and `#^D_INNER,1 + #^D_INNER,2`, with (14.3.65)–(14.3.66) for
Phase 1 (here `0`, as `‖c(x₀)‖ = 0`) and
`#^F_INNER,2 = (f_up - f_low - 1)(κ^A ε₀^{1-π₁} ε₁^{-π₁} + κ^C ε₀^{-1}) + 1`,
`#^D_INNER,2 = κ^S (f_up - f_low - 1) ε₀^{1-π₁} ε₁^{-π₁} + 1`. Every outer iteration before `k_ε`
is a case-(b) iteration whose call ends at a point passing INNER's test.

The run exercises exactly the exemption on which the book's proof of Lemma 14.3.8 rests: its
`k_ε ∼ (ε₀ ε₁)^{-1}` bad case-(b) iterations each cost one evaluation, and the decrease of
Lemma 14.2.2 is not required at a step after which INNER's test holds. The extra term
`O(ε₀^{-1} + (ε₀ ε₁)^{-1})` of `Constrained.IsHighOrderTargetRun.complexity_of_innerTest` (the
corrected statement,
which needs no cost hypothesis) is thus attained in order, and the evaluation counts exceed the
printed bounds for every `π₁ ≤ 3/2` (in particular the ARqp-SC exponent `(p+1)/p` for every
`p ≥ 2`, `Optimization.arqpPiOf_one_le`); only the cost bound needs `π₁ ≥ 4/3`. The INNER calls are
not runs of ARqp-SC (see
the module doc): they are not produced by a regularization algorithm of (14.2.12). Runs of
ARqp-SC itself, when Step 2.1 of Algorithm 14.1.2 re-initialises `μ` at every Step 2, exceed the
printed order with `π₁ = (p+1)/p` (per-call reading) for `q = 1` and `p ≥ 4`
(`theorem_14_3_9_arqp_counterexample`, on a different problem; with `μ` bounded below this is
open); for `q = p`, and with the
exponents `j + 1`, they attain it (`theorem_14_3_9_arqp`, `theorem_14_3_9_arqpc`).

The construction needs `π₁ ≥ 4/3` for the cost bound: a call costs at least one evaluation while
`(μ(x_k, t_k)) (β ‖r‖ ε₁)^{-π₁} ∼ u^{4 - 3π₁}` (`‖r‖ ∼ u²`, `ε₁ ∼ u`), which tends to `0` for
`π₁ < 4/3`. The upper limit `3/2` comes from the order comparison (`order_le`).

The data: for `m ≥ 7`, `u = 1/m`, `ε₀ = u²/2 + u³/2`, `ε₁ = 3u/2`, `N = m³`. Phase 2 starts at
`x₁ = (0, -1)` with `t₁ = 1 - ε₀`; the `k`-th INNER call makes one successful iteration to
`x_{k+1} = (u, ·)` with `f(x_{k+1}) = t_k - E_{k+1}`, `E_j = (u³/2)(1 - j/(4(N + 1))) ∈
[3u³/8, u³/2]`, for `k < N`. At `x_{k+1}` the gradient `∇μ(x_{k+1}, t_k) = (u³/2 - E_{k+1},
E_{k+1})` has norm at most `u³/2 ≤ β ‖r(x_k, t_k)‖ ε₁` (INNER's test, using
`‖r(x_k, t_k)‖ ≥ u²/2`), while after the reflection (14.3.35) the decrease along `-e₁` is
`u³/2 + E_{k+1} ≥ 7u³/8 > ε₁ ‖r(x_{k+1}, t_{k+1})‖` ((14.3.34) fails). The targets drop by
`2E_{k+1} ≈ u³`, so `N ≈ 1/u³` such iterations fit in `X`; the last call lands on its target,
`f(x_{N+1}) = t_N`, where the third test of (14.3.32) holds (case (c)), and Phase 2 stops. -/
theorem theorem_14_3_9_false :
    ∃ (f : ℝ² → ℝ) (c : ℝ² → ℝ¹) (X : Set ℝ²) (flow fup : ℝ),
      AssumptionXCNe X ∧ Convex ℝ X ∧ ContDiff ℝ ⊤ f ∧ ContDiff ℝ ⊤ c ∧
      (∀ p : ℕ, (∃ L B : ℕ → ℝ, AssumptionD1pLBX f X (ball 0 2) p L B) ∧
        ∃ L B : ℕ → ℝ, AssumptionCD1pLBX c X (ball 0 2) p L B) ∧
      (∀ y, ∀ i ∈ Finset.Icc 1 1, ‖iteratedFDeriv ℝ i f y‖ ≤ 2) ∧
      Chapter07.AssumptionBFb f c X 1 flow fup ∧
      ∀ κA κC κS κF₁ κD₁ : ℝ,
      ∃ (ε : ℕ → ℝ) (x₀ : ℝ²) (xP : ℕ → ℝ²) (δP : ℕ → ℕ → ℝ) (D : TPqpSeq 2) (kε : ℕ),
        (∀ j, 0 < ε j ∧ ε j ≤ 1) ∧
        ε 0 ≤ (1 + 3 * (|κA| + |κC| + |κS|))⁻¹ ∧ ε 1 ≤ (1 + 3 * (|κA| + |κC| + |κS|))⁻¹ ∧
        ‖c x₀‖ = 0 ∧ D.IsEnd f c X 1 (3 / 4) ε kε ∧
        D.funEvals kε = kε + 1 ∧ D.derivEvals kε = kε + 1 ∧
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
            -- the printed bounds fail
            1 / 2 * κF₁ * ‖c x₀‖ * (β₁ ^ (1 - 2 * π 1) / (β₁ ^ (1 - π 1) - 1)) *
                (3 / 4 : ℝ) ^ (1 - π 1) * (ε 0 ^ (1 - π 1) * ε 1 ^ (-π 1)) +
              ((fup - flow - 1) * (κA * (ε 0 ^ (1 - π 1) * ε 1 ^ (-π 1)) + κC * (ε 0)⁻¹) + 1) <
                D.funEvals kε ∧
            1 / 2 * κD₁ * ‖c x₀‖ * (β₁ ^ (1 - 2 * π 1) / (β₁ ^ (1 - π 1) - 1)) *
                (3 / 4 : ℝ) ^ (1 - π 1) * (ε 0 ^ (1 - π 1) * ε 1 ^ (-π 1)) +
              (κS * (fup - flow - 1) * (ε 0 ^ (1 - π 1) * ε 1 ^ (-π 1)) + 1) <
                D.derivEvals kε := by
  refine ⟨(objA 1), conC, boxX, -2, 2, ⟨isClosed_boxX, ⟨pt 0 (-1), by simp [boxX]⟩⟩, convex_boxX,
    contDiff_objA 1, contDiff_conC, assumptionD1pLBX 1, deriv_objA_le (by simp),
    assumptionBFb (by simp), fun κA κC κS κF₁ κD₁ => ?_⟩
  have hAa := abs_nonneg κA
  have hCa := abs_nonneg κC
  have hSa := abs_nonneg κS
  obtain ⟨u, N, hu, hu7, hNu, hN, hCε, hord⟩ := exists_params (1 + 3 * (|κA| + |κC| + |κS|))
  obtain ⟨hε0, hε1⟩ := hCε (by linarith)
  have hc0 : ‖conC (pt 0 (-1))‖ = 0 := by rw [norm_conC]; simp
  refine ⟨eps u, pt 0 (-1), fun _ => pt 0 (-1), fun _ _ => 1, run u N, N,
    fun j => ⟨eps_pos hu j, eps_le_one hu hu7 j⟩, hε0, hε1, hc0, isEnd hu hu7 hNu hN,
    TPqpSeq.funEvals_oneStep _ _ _, TPqpSeq.derivEvals_oneStep _ _ _, fun k hk => ?_,
    fun β₁ β hβ₁ hβ₁1 hβ hβθ => ?_⟩
  · obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.1 hk
    exact ⟨xs_mem hu hu7 hNu (k := k + 1) (by omega) (by omega), rfl, merit_lt hu hk1 hkN⟩
  have hβ0 : 0 < β := by linarith
  refine ⟨(isTPqpGCPhase2 hu hu7 hNu hN hβ0 hβθ).algorithm_14_3_2_of_stop hβ₁ hβ₁1,
    fun k hk => innerTest hu hu7 hNu hβ (Finset.mem_Icc.1 hk).1 (Finset.mem_Icc.1 hk).2,
    fun k hk => isKb hu hu7 (Finset.mem_Ico.1 hk).1 (Finset.mem_Ico.1 hk).2,
    fun k hk => not_innerTest_start hu hu7 hNu hβθ (Finset.mem_Icc.1 hk).1
      (Finset.mem_Icc.1 hk).2, fun κdecr κuns κunc π ρ hκ hρ =>
        isInnerPhaseRunStrong hu hu7 hNu hN hβ hκ hρ, fun π hπ2 => ⟨fun hπ1 κ hκ k hk => ?_, ?_⟩⟩
  · obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.1 hk
    have h2 := two_le_innerEvalBound hu hu7 hβ0 hβθ hκ hπ1 hk1 hkN (N := N)
    have hs : ((run u N).succCount k : ℝ) = 1 := by simp [run]
    rw [hs, show ((run u N).e k : ℝ) = 1 by simp [run]]
    exact ⟨by norm_num; exact h2, by norm_num; exact h2⟩
  set M := eps u 0 ^ (1 - π 1) * eps u 1 ^ (-π 1) with hM_def
  set E := (eps u 0)⁻¹ with hE_def
  have hM0 : 0 ≤ M := by have := eps_pos hu 0; have := eps_pos hu 1; positivity
  have hE0 : 0 ≤ E := (inv_pos.2 (eps_pos hu 0)).le
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
  rw [run, TPqpSeq.funEvals_oneStep, TPqpSeq.derivEvals_oneStep, hc0]
  push_cast
  constructor <;> nlinarith

open Theorem1439Cex PlaneCex in
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
    ∃ ε : ℕ → ℝ, (∀ j, 0 < ε j ∧ ε j ≤ 1) ∧ pt 0 (-1) ∈ boxX ∧ ‖conC (pt 0 (-1))‖ = 0 ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        β * Constrained.targetResidual (objA 1) conC
            (objA 1 (pt 0 (-1)) - √(ε 0 ^ 2 - ‖conC (pt 0 (-1))‖ ^ 2)) (pt 0 (-1)) *
            ε 1 * δ ^ 1 / (1 : ℕ)! <
          Optimization.taylorMeasure
            (ftaylorSeries ℝ (Constrained.targetMerit (objA 1) conC
              (objA 1 (pt 0 (-1)) - √(ε 0 ^ 2 - ‖conC (pt 0 (-1))‖ ^ 2))) (pt 0 (-1))) 1 δ
            {d | pt 0 (-1) + d ∈ boxX}) ∧
      innerEvalBound κ π 1
          (Constrained.targetMerit (objA 1) conC
            (objA 1 (pt 0 (-1)) - √(ε 0 ^ 2 - ‖conC (pt 0 (-1))‖ ^ 2)) (pt 0 (-1)))
          (fun j => β * Constrained.targetResidual (objA 1) conC
            (objA 1 (pt 0 (-1)) - √(ε 0 ^ 2 - ‖conC (pt 0 (-1))‖ ^ 2)) (pt 0 (-1)) * ε j) < 1 := by
  have hc0 : ‖conC (pt 0 (-1))‖ = 0 := by rw [norm_conC]; simp
  set a : ℝ := 2 - π 1 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  set K : ℝ := |κ| / 2 * β ^ (-π 1) + 1 with hK_def
  have hK : 0 < K := by rw [hK_def]; positivity
  set e : ℝ := min 1 ((2 * K) ^ (-1 / a)) with he_def
  have he0 : 0 < e := lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _)
  have he1 : e ≤ 1 := min_le_left _ _
  have hea : e ^ a ≤ (2 * K)⁻¹ := by
    calc e ^ a ≤ ((2 * K) ^ (-1 / a)) ^ a :=
          Real.rpow_le_rpow he0.le (min_le_right _ _) ha.le
      _ = (2 * K)⁻¹ := by
          rw [← Real.rpow_mul (by positivity), show -1 / a * a = -1 by field_simp,
            Real.rpow_neg_one]
  refine ⟨fun j => if j = 0 then e else 1, fun j => ?_, by simp [boxX], hc0, ?_⟩
  · dsimp only
    split_ifs
    · exact ⟨he0, he1⟩
    · exact ⟨one_pos, le_rfl⟩
  simp only [↓reduceIte, one_ne_zero, hc0]
  have ht : objA 1 (pt 0 (-1)) - √(e ^ 2 - 0 ^ 2) = objA 1 (pt 0 (-1)) - e := by
    rw [show e ^ 2 - (0 : ℝ) ^ 2 = e ^ 2 by ring, Real.sqrt_sq he0.le]
  rw [ht]
  have hR : Constrained.targetResidual (objA 1) conC (objA 1 (pt 0 (-1)) - e) (pt 0 (-1)) = e := by
    rw [Constrained.targetResidual_def, hc0,
      show (0 : ℝ) ^ 2 + (objA 1 (pt 0 (-1)) - (objA 1 (pt 0 (-1)) - e)) ^ 2 = e ^ 2 by ring,
      Real.sqrt_sq he0.le]
  refine ⟨fun δ hδ hδ1 => ?_, ?_⟩
  · rw [hR]
    have hmem : EuclideanSpace.single (0 : Fin 2) (-δ) ∈
        closedBall (0 : ℝ²) δ ∩ {d | pt 0 (-1) + d ∈ boxX} := by
      refine ⟨by simp [abs_of_pos hδ], ?_⟩
      simp only [boxX, mem_ofPred_eq, PiLp.add_apply, pt_zero, pt_one]
      have e0 : (EuclideanSpace.single (0 : Fin 2) (-δ : ℝ)) 0 = -δ := by simp
      have e1 : (EuclideanSpace.single (0 : Fin 2) (-δ : ℝ)) 1 = 0 := by simp
      rw [e0, e1]
      exact ⟨by rw [abs_le]; constructor <;> linarith, by norm_num⟩
    have h := Optimization.taylorDecrement_le_taylorMeasure
      (ftaylorSeries ℝ (Constrained.targetMerit (objA 1) conC (objA 1 (pt 0 (-1)) - e))
        (pt 0 (-1))) 1
      hmem
    rw [decr] at h
    simp only [pt_zero] at h
    have e0 : (EuclideanSpace.single (0 : Fin 2) (-δ : ℝ)) 0 = -δ := by simp
    have e1 : (EuclideanSpace.single (0 : Fin 2) (-δ : ℝ)) 1 = 0 := by simp
    rw [e0, e1] at h
    refine lt_of_lt_of_le ?_ h
    simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one, mul_one]
    have : β * e * δ < e * δ := by
      have := mul_pos he0 hδ
      nlinarith
    nlinarith
  · rw [innerEvalBound_one, Constrained.targetMerit_eq, hR]
    simp only [one_ne_zero, ↓reduceIte, mul_one]
    rw [Real.mul_rpow hβ.le he0.le]
    have hsplit : e ^ 2 / 2 * (β ^ (-π 1) * e ^ (-π 1)) = β ^ (-π 1) / 2 * e ^ a := by
      rw [ha_def, show 2 - π 1 = (2 : ℝ) + -π 1 by ring, Real.rpow_add he0,
        show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    rw [mul_assoc, hsplit]
    have hb : 0 ≤ β ^ (-π 1) := (Real.rpow_pos_of_pos hβ _).le
    have hea0 : 0 ≤ e ^ a := (Real.rpow_pos_of_pos he0 _).le
    have h1 : κ * (β ^ (-π 1) / 2 * e ^ a) ≤ K * e ^ a := by
      rw [hK_def]
      have := le_abs_self κ
      nlinarith [mul_nonneg hb hea0, abs_nonneg κ]
    have h2 : K * e ^ a ≤ K * (2 * K)⁻¹ := mul_le_mul_of_nonneg_left hea hK.le
    have h3 : K * (2 * K)⁻¹ = 1 / 2 := by field_simp
    linarith



end TheoremFalse


/-! ## INNER = ARqp-SC -/

section ARqpSCCalls

/-! ### Existence of LENq-SC and TPqp-GC runs -/

/-- The zero constraint map `ℝⁿ → ℝ⁰`: ARqpC-SC with `c = 0` and `h = 0` is ARqp-SC on `f`
(`algorithm_14_1_1.zero_algorithm_12_2_2_feasible`). -/
abbrev zeroCon (n : ℕ) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin 0) := 0

/-- The zero outer function `h = 0` on `ℝ⁰`. -/
abbrev zeroOuter : EuclideanSpace ℝ (Fin 0) → ℝ := 0

/-- The zero constraint map satisfies c.D1pL with constants `0`. -/
theorem assumptionCD1pL_zeroCon (p : ℕ) : AssumptionCD1pL (zeroCon n) p (fun _ => 0) where
  contDiff := contDiff_const
  nonneg _ _ := le_rfl
  lipschitz_component i := i.elim0

/-- `h = 0` satisfies h.L with constant `0`. -/
theorem assumptionHLip_zeroOuter : AssumptionHLip zeroOuter 0 := ⟨le_rfl, fun _ _ => by simp⟩

/-- `h = 0` satisfies h.S0. -/
theorem assumptionHS0_zeroOuter : AssumptionHS0 zeroOuter := ⟨fun _ _ => by simp, rfl⟩

/-- The decrease constant `κ_decr = η₁ κ_{Δm}` of an ARqp-SC call on an objective satisfying
f.D1pL with constants `L` (Lemma 14.2.2, ARqpC-SC row with `c = 0`, `h = 0`; the exponents are
`π_j = j + 1`). -/
noncomputable def arqpSCKappaDecr (P : ARqpCParams) (L : ℕ → ℝ) (p q : ℕ) : ℝ :=
  P.η₁ * kappaDm2 P L (fun _ => 0) 0 p q 0

/-- The constant `κ_uns = 1 + |log γ₁|/log γ₂` of Lemma 14.2.3. -/
noncomputable def arqpSCKappaUns (P : ARqpCParams) : ℝ := 1 + |Real.log P.γ₁| / Real.log P.γ₂

/-- The constant `κ_uns + log(σ_max/σ₀)/log γ₂` bounding the number of iterations of an ARqp-SC
call in excess of `κ_uns` times its successful ones (Lemma 14.2.3, ARqpC-SC row with `c = 0`,
`h = 0`, for an objective satisfying f.D1pL with constants `L`; the first `κ_uns` accounts for the
last iteration of a call). -/
noncomputable def arqpSCKappaUnc (P : ARqpCParams) (L : ℕ → ℝ) (p : ℕ) : ℝ :=
  arqpSCKappaUns P + Real.log (arqpcSigmaMax P L (fun _ => 0) 0 p 0 / P.σ₀) / Real.log P.γ₂

/-- `κ_uns ≥ 0`. -/
theorem arqpSCKappaUns_nonneg (P : ARqpCParams) : 0 ≤ arqpSCKappaUns P := by
  unfold arqpSCKappaUns
  have := P.log_γ₂_pos
  positivity

/-- `κ_decr > 0` as soon as `L_p ≥ 1` and `θ < ς`. -/
theorem arqpSCKappaDecr_pos_of {p q : ℕ} {L : ℕ → ℝ} {P : ARqpCParams} (hLp : 1 ≤ L p)
    (hθς : P.θ < P.ς) :
    0 < arqpSCKappaDecr P L p q := by
  have hσ : 0 < arqpcSigmaMax P L (fun _ => 0) 0 p 0 :=
    Optimization.arSigmaMax_pos P.toARParams _
  have hA : 0 < compositeLipschitzWp L (fun _ => 0) 0 p 0 +
      arqpcSigmaMax P L (fun _ => 0) 0 p 0 := by
    rw [compositeLipschitzWp_eq]
    simp only [zero_mul, add_zero]
    linarith
  have hκδ : 0 < kappaDeltaMin P L (fun _ => 0) 0 p 0 := by
    rw [kappaDeltaMin_eq]
    exact Optimization.arqpKappaDelta_pos _ (zero_le_one.trans
      (one_le_compositeLipschitzW_of (m := 0) (Lf := L) (Lc := fun _ => 0) (p := p)
        (le_refl (0 : ℝ)))) hσ
  have hb : 0 < (P.ς - P.θ) / ((q ! : ℝ) * (compositeLipschitzWp L (fun _ => 0) 0 p 0 +
      arqpcSigmaMax P L (fun _ => 0) 0 p 0)) * kappaDeltaMin P L (fun _ => 0) 0 p 0 ^ q / 3 := by
    have : 0 < P.ς - P.θ := by linarith
    positivity
  unfold arqpSCKappaDecr kappaDm2
  have := P.η₁_pos
  have := P.σmin_pos
  have := Real.rpow_pos_of_pos hb (((p : ℝ) + 1) / ((p : ℝ) - q + 1))
  positivity

/-- The sublevel set of the objective `F + 0 ∘ 0` of INNER at `x^S` lies in `S` when every
`y ∈ X` with `F(y) ≤ F(x^S)` does. -/
theorem compositeSublevel_zero_subset {F : ℝⁿ → ℝ} {X S : Set ℝⁿ} {xS : ℝⁿ}
    (h : ∀ y ∈ X, F y ≤ F xS → y ∈ S) :
    compositeSublevel F (zeroCon n) zeroOuter X xS ⊆ S :=
  fun y hy => h y hy.1 (by simpa using hy.2)

/-- The points `y ∈ X` with `F(y) ≤ F(x^S)` lie in the sublevel set of the objective `F + 0 ∘ 0`
of INNER at `x^S`. -/
theorem mem_compositeSublevel_zero {F : ℝⁿ → ℝ} {X : Set ℝⁿ} {xS y : ℝⁿ} (hy : y ∈ X)
    (hFy : F y ≤ F xS) : y ∈ compositeSublevel F (zeroCon n) zeroOuter X xS :=
  ⟨hy, by simpa using hFy⟩

section InnerCall

variable {F : ℝⁿ → ℝ} {X : Set ℝⁿ} {p q : ℕ} {P : ARqpCParams} {ε δ₀ : ℕ → ℝ}
  {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → ℝⁿ}

/-- **ARqpC-SC with `c = 0`, `h = 0` is ARqp-SC**: such a run is a run of
`Chapter12.algorithm_12_2_2_feasible` on `F` (Algorithm 12.2.2 with the feasible set `X`), whose
Step 2 moreover follows Algorithm 14.1.2. -/
theorem algorithm_14_1_1.zero_algorithm_12_2_2_feasible
    (hr : algorithm_14_1_1 F (zeroCon n) zeroOuter X p q P ε δ₀ x s σ δ δs d dm) :
    Chapter12.algorithm_12_2_2_feasible F X P.toARqpParams p q ε δ₀ x s σ δ δs d dm := by
  have h1 : (fun y => F y + zeroOuter (zeroCon n y)) = F := funext fun y => by simp
  have h2 : (fun k => arqpcData F (zeroCon n) zeroOuter p (x k) (σ k)) =
      Optimization.arqpData F p x σ :=
    funext fun k => Optimization.ARqpData.ofComposite_zero_fun _ _ _ _
  have h := hr.run
  rw [h1, h2] at h
  exact h

/-- `F` does not increase along an ARqpC-SC run with `c = 0`, `h = 0`, up to its first
termination index. -/
theorem algorithm_14_1_1.zero_antitone
    (hr : algorithm_14_1_1 F (zeroCon n) zeroOuter X p q P ε δ₀ x s σ δ δs d dm) {kε : ℕ}
    (hhit : Optimization.IsFirstHit (arqpcStop F (zeroCon n) zeroOuter p q P ε x s σ δ d) kε) :
    ∀ i j, i ≤ j → j ≤ kε → F (x j) ≤ F (x i) := by
  intro i j hij hj
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    refine le_trans ?_ (ih (by omega))
    have hk : ∀ l ≤ j, ¬ arqpcStop F (zeroCon n) zeroOuter p q P ε x s σ δ d l :=
      fun l hl => hhit.2 l (by omega)
    by_cases hs : P.η₁ ≤ Optimization.arqpRatio (fun y => F y + zeroOuter (zeroCon n y))
        (fun k => arqpcData F (zeroCon n) zeroOuter p (x k) (σ k)) x s j
    · have hpos := (lemma_14_1_5 hr (fun l hl => hk l hl.le)
        (fun h' => hk j le_rfl (Or.inl h'))).2 (fun h' => hk j le_rfl (Or.inr h'))
      have := (hr.run.toIsARRun.sub_ge_of_succ (w := fun y => F y + zeroOuter (zeroCon n y))
        (pred := fun k => Optimization.compositeTaylorDecrement (ftaylorSeries ℝ F (x k))
          (ftaylorSeries ℝ (zeroCon n) (x k)) zeroOuter p (s k)) hk rfl hpos hs).2
      have := mul_pos P.η₁_pos hpos
      simp only [zeroOuter, Pi.zero_apply, add_zero] at *
      linarith
    · rw [hr.run.toIsARRun.eq_of_not_succ hk (not_le.1 hs)]

/-- The model data of ARqpC with `c = 0`, `h = 0` are those of ARqp. -/
theorem zero_arqpcData_eq (F : ℝⁿ → ℝ) (p : ℕ) (x : ℕ → ℝⁿ) (σ : ℕ → ℝ) :
    (fun k => arqpcData F (zeroCon n) zeroOuter p (x k) (σ k)) = Optimization.arqpData F p x σ :=
  funext fun _ => Optimization.ARqpData.ofComposite_zero_fun _ _ _ _

/-- The termination test of ARqpC with `c = 0`, `h = 0` is that of ARqp. -/
theorem zero_arqpcStop_iff {i : ℕ} :
    arqpcStop F (zeroCon n) zeroOuter p q P ε x s σ δ d i ↔
      Optimization.arqpStop F P.toARqpParams p q ε x s σ δ d i := by
  simp only [arqpcStop, Optimization.arqpStop, zero_arqpcData_eq]

/-- The ratio of ARqpC with `c = 0`, `h = 0` is that of ARqp. -/
theorem zero_arqpRatio_eq {i : ℕ} :
    Optimization.arqpRatio (fun y => F y + zeroOuter (zeroCon n y))
        (fun k => arqpcData F (zeroCon n) zeroOuter p (x k) (σ k)) x s i =
      Optimization.arqpRho F p x s σ i := by
  have h1 : (fun y => F y + zeroOuter (zeroCon n y)) = F := funext fun y => by simp
  simp only [Optimization.arqpRho, h1, zero_arqpcData_eq]

/-- **Decrease of ARqp-SC with the exponents of its row of (14.2.12), anchored**: as
`algorithm_14_1_1.zero_decrease_arqp_anchored`, under the anchored bounds of `F` on the sublevel
set at
`x₀` (an open convex `X₀ ⊇ X`; the book's f.D1pLaB.X), through
`Optimization.IsARqpRun.decrease`. -/
theorem algorithm_14_1_1.zero_decrease_arqp_anchored
    (hr : algorithm_14_1_1 F (zeroCon n) zeroOuter X p q P ε δ₀ x s σ δ δs d dm) {L : ℕ → ℝ}
    {X₀ : Set ℝⁿ} (hF : AnchoredCompositeBounds F (zeroCon n) X₀
      (compositeSublevel F (zeroCon n) zeroOuter X (x 0)) p L (fun _ => 0)) (hX : X ⊆ X₀)
    (hθς : P.θ < P.ς)
    {u : Prop} [Decidable u] (hu : u → q = 1 ∧ Convex ℝ X) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpcStop F (zeroCon n) zeroOuter p q P ε x s σ δ d i)
    (hs : P.η₁ ≤ Optimization.arqpRatio (fun y => F y + zeroOuter (zeroCon n y))
      (fun k => arqpcData F (zeroCon n) zeroOuter p (x k) (σ k)) x s k)
    (h1 : ¬ algorithm_14_1_1.Stop₁ F (zeroCon n) zeroOuter p q P ε x σ δ d (k + 1)) :
    P.η₁ * (Optimization.arqpKappaDmOf u P.toARqpParams L p q *
        Optimization.finMin 1 (fun j => ε j ^ Optimization.arqpPiOf u p j) q) ≤
      F (x k) - F (x (k + 1)) := by
  have hrad1 : δ (k + 1) = δs k := (hr.run.radii k hk).1 hs
  have hnot1 : ¬ algorithm_14_1_1.Stop₁ F (zeroCon n) zeroOuter p q P ε x σ δ d k :=
    fun h' => hk k le_rfl (Or.inl h')
  have hk' : ∀ i < k, ¬ arqpcStop F (zeroCon n) zeroOuter p q P ε x s σ δ d i :=
    fun i hi => hk i hi.le
  refine (Optimization.IsARqpRun.decrease hF.lipschitzDerivsAnchored_f
    hF.one_le hX
      (fun y hy hFy => mem_compositeSublevel_zero hy hFy) hr.one_le_q hr.q_le_p hθς
    (fun j hj => ⟨(hr.ε_mem j hj).1, (hr.ε_mem j hj).2⟩) hr.zero_algorithm_12_2_2_feasible
    (fun i hi => (zero_arqpcStop_iff).not.1 (hk i hi)) (zero_arqpRatio_eq ▸ hs)
    (by simpa only [algorithm_14_1_1.Stop₁, zero_arqpcData_eq] using h1) (u := u)
    ⟨fun hq2 j hj => ?_, fun hq2 => ?_⟩).2
  · have hq1 : q = 1 ∧ Convex ℝ X := hu hq2
    have hj1 : j = 1 := by have := Finset.mem_Icc.1 hj; omega
    subst hj1
    rw [hrad1]
    refine hr.radius_eq_one hk' hnot1 ?_
    simp only [halvingSet, mem_ofPred_eq, not_or, not_not]
    exact ⟨by norm_num, convexOn_const 0 convex_univ, hq1.2⟩
  · have hpol := hr.kappaDeltaMin_mul_le_radius_anchored hF hX assumptionHLip_zeroOuter
      assumptionHS0_zeroOuter hk' hnot1
    refine Or.inr fun j hj => ?_
    rw [hrad1]
    refine le_trans (le_of_eq ?_) (hpol j hj)
    simp [kappaDeltaMin, Optimization.arqpKappaDelta, compositeLipschitzW, compositeLipschitzWp,
      arqpcSigmaMax]

/-- The radius constant `κ_ρ = min(κ_{δ,min}, 1/(4(3 L̄ + σ_max)))` of an ARqp-SC call on an
objective satisfying f.D1pL with constants `L` (`L̄ = max(1, L_1, …, L_p)`, `σ_max` of
Lemma 14.1.6): the radii of its INNER certificate are at least `κ_ρ ε_j`
(`algorithm_14_1_1.zero_exists_cert_anchored`). -/
noncomputable def arqpSCKappaRad (P : ARqpCParams) (L : ℕ → ℝ) (p : ℕ) : ℝ :=
  min (kappaDeltaMin P L (fun _ => 0) 0 p 0)
    (1 / (4 * (3 * Optimization.finMax 1 L p + arqpcSigmaMax P L (fun _ => 0) 0 p 0)))

theorem arqpSCKappaRad_pos (P : ARqpCParams) (L : ℕ → ℝ) (p : ℕ) :
    0 < arqpSCKappaRad P L p := by
  have hσ : 0 < arqpcSigmaMax P L (fun _ => 0) 0 p 0 :=
    Optimization.arSigmaMax_pos P.toARParams (compositeLipschitzWp L (fun _ => 0) 0 p 0)
  have hL1 : 1 ≤ Optimization.finMax 1 L p := Optimization.one_le_finMax
  have hW : 1 ≤ compositeLipschitzW L (fun _ => 0) 0 p 0 := by
    rw [compositeLipschitzW_eq]
    simp only [Nat.cast_zero, Real.sqrt_zero, zero_mul, add_zero]
    exact hL1
  have h3 : 0 < 3 * compositeLipschitzW L (fun _ => 0) 0 p 0 +
      arqpcSigmaMax P L (fun _ => 0) 0 p 0 := by linarith
  have h4 : 0 < 3 * Optimization.finMax 1 L p + arqpcSigmaMax P L (fun _ => 0) 0 p 0 := by linarith
  refine lt_min ?_ (by positivity)
  rw [kappaDeltaMin_eq]
  exact Optimization.arqpKappaDelta_pos _ (by linarith) hσ

/-- The radii of an ARqpC-SC run with `c = 0`, `h = 0` and initial radii `1` stay at least
`κ_{δ,min} ε_j`, under the anchored bounds of `F` on the sublevel set at `x₀`
(`algorithm_14_1_1.kappaDeltaMin_mul_le_radius_anchored`). -/
theorem algorithm_14_1_1.zero_radius_ge_anchored
    (hr : algorithm_14_1_1 F (zeroCon n) zeroOuter X p q P ε (fun _ => 1) x s σ δ δs d dm)
    {L : ℕ → ℝ} {X₀ : Set ℝⁿ} (hF : AnchoredCompositeBounds F (zeroCon n) X₀
      (compositeSublevel F (zeroCon n) zeroOuter X (x 0)) p L (fun _ => 0)) (hX : X ⊆ X₀) :
    ∀ k, (∀ i < k, ¬ arqpcStop F (zeroCon n) zeroOuter p q P ε x s σ δ d i) →
      ∀ j ∈ Finset.Icc 1 q, kappaDeltaMin P L (fun _ => 0) 0 p 0 * ε j ≤ δ k j := by
  have hW : 1 ≤ compositeLipschitzW L (fun _ => 0) 0 p 0 := by
    rw [compositeLipschitzW_eq]
    simp only [Nat.cast_zero, Real.sqrt_zero, zero_mul, add_zero]
    exact Optimization.one_le_finMax
  have hσ := Optimization.arSigmaMax_pos P.toARParams (compositeLipschitzWp L (fun _ => 0) 0 p 0)
  have hκ1 : kappaDeltaMin P L (fun _ => 0) 0 p 0 ≤ 1 := by
    rw [kappaDeltaMin_eq]
    exact (Optimization.arqpKappaDelta_lt_one _ hW hσ.le).le
  have hκ0 : 0 ≤ kappaDeltaMin P L (fun _ => 0) 0 p 0 := by
    rw [kappaDeltaMin_eq]
    exact (Optimization.arqpKappaDelta_pos _ (zero_le_one.trans hW) hσ).le
  intro k
  induction k with
  | zero =>
    intro _ j hj
    rw [hr.run.delta_zero]
    have := hr.ε_mem j hj
    nlinarith
  | succ k ih =>
    intro hk j hj
    have hk' : ∀ i ≤ k, ¬ arqpcStop F (zeroCon n) zeroOuter p q P ε x s σ δ d i :=
      fun i hi => hk i (Nat.lt_succ_of_le hi)
    obtain ⟨hs, hu⟩ := hr.run.radii k hk'
    by_cases hρ : P.η₁ ≤ Optimization.arqpRatio (fun y => F y + zeroOuter (zeroCon n y))
        (fun k => arqpcData F (zeroCon n) zeroOuter p (x k) (σ k)) x s k
    · rw [hs hρ]
      exact hr.kappaDeltaMin_mul_le_radius_anchored hF hX assumptionHLip_zeroOuter
        assumptionHS0_zeroOuter (fun i hi => hk' i hi.le) (fun h' => hk' k le_rfl (Or.inl h'))
        j hj
    · rw [(hu hρ).1]
      exact ih (fun i hi => hk' i hi.le) j hj

/-- **The certificate of an ARqp-SC call with explicit radii, anchored**: as
`algorithm_14_1_1.zero_exists_cert_anchored`, under the anchored bounds of `F` on the sublevel set
at `x₀`
(an open convex `X₀ ⊇ X`; the book's f.D1pLaB.X): the termination iterate lies in the sublevel set,
where the jets of `F` are bounded (`Optimization.isEpsDeltaApprox_of_isMinOn_zero_of_jet`). -/
theorem algorithm_14_1_1.zero_exists_cert_anchored
    (hr : algorithm_14_1_1 F (zeroCon n) zeroOuter X p q P ε (fun _ => 1) x s σ δ δs d dm)
    {L : ℕ → ℝ} {X₀ : Set ℝⁿ} (hF : AnchoredCompositeBounds F (zeroCon n) X₀
      (compositeSublevel F (zeroCon n) zeroOuter X (x 0)) p L (fun _ => 0)) (hX : X ⊆ X₀) {kε : ℕ}
    (hhit : Optimization.IsFirstHit (arqpcStop F (zeroCon n) zeroOuter p q P ε x s σ δ d) kε) :
    ∃ δε : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, 0 < δε j ∧ δε j ≤ 1) ∧
      (∀ j ∈ Finset.Icc 1 q, arqpSCKappaRad P L p * ε j ≤ δε j) ∧
      Optimization.IsEpsDeltaApprox (ftaylorSeries ℝ F (x kε)) {e | x kε + e ∈ X} q ε δε := by
  have h12 := hr.zero_algorithm_12_2_2_feasible
  have hk12 : ∀ i < kε, ¬ Optimization.arqpStop F P.toARqpParams p q ε x s σ δ d i :=
    fun i hi => zero_arqpcStop_iff.not.1 (hhit.2 i hi)
  have hstop : Optimization.arqpStop F P.toARqpParams p q ε x s σ δ d kε :=
    zero_arqpcStop_iff.1 hhit.1
  have hε := hr.ε_mem
  have hσ := sigma_le_arqpcSigmaMax_anchored hr hF hX assumptionHLip_zeroOuter hhit.2 kε le_rfl
  have hσ0 : 0 < σ kε := h12.toIsARRun.sigma_pos hk12 kε le_rfl
  have hL1 : 1 ≤ Optimization.finMax 1 L p := Optimization.one_le_finMax
  have hrad0 : arqpSCKappaRad P L p ≤ kappaDeltaMin P L (fun _ => 0) 0 p 0 := min_le_left _ _
  have hrad1 : arqpSCKappaRad P L p ≤
      1 / (4 * (3 * Optimization.finMax 1 L p + arqpcSigmaMax P L (fun _ => 0) 0 p 0)) :=
    min_le_right _ _
  by_cases h1 : Optimization.arqpStop₁ P.toARqpParams q ε (Optimization.arqpData F p x σ) δ d kε
  · refine ⟨δ kε, fun j hj => h12.delta_mem (fun _ _ => ⟨one_pos, le_rfl⟩) kε hk12 j hj,
      fun j hj => ?_,
      Optimization.MeasureTestPasses.isEpsDeltaApprox P.ς_pos (h12.witness kε hk12) h1⟩
    exact (mul_le_mul_of_nonneg_right hrad0 (hε j hj).1.le).trans
      (hr.zero_radius_ge_anchored hF hX kε hhit.2 j hj)
  · have hstep := h12.step hk12 h1
    have h2 : Optimization.arqpStop₂ (Optimization.arqpData F p x σ) s kε := hstop.resolve_left h1
    have hxA := hr.mem_compositeSublevel hhit.2
    obtain ⟨hδ, hcert⟩ := Optimization.isEpsDeltaApprox_of_isMinOn_zero_of_jet (h12.mem kε hk12)
      (hF.contDiffAt_f (hF.subset hxA)) (fun _ hi => (hF.jet_bounds hxA).1 _ hi)
      hr.q_le_p (fun j hj => ⟨(hε j hj).1, (hε j hj).2⟩) hσ0 (hstep.isMinOn_of_eq h2)
    refine ⟨_, hδ, fun j hj => ?_, hcert⟩
    obtain ⟨hε0, hε1⟩ := hε j hj
    have hK : 0 < 4 * (3 * Optimization.finMax 1 L p + σ kε) := by linarith
    have hK' : 4 * (3 * Optimization.finMax 1 L p + σ kε) ≤
        4 * (3 * Optimization.finMax 1 L p + arqpcSigmaMax P L (fun _ => 0) 0 p 0) := by linarith
    have hK1 : 1 ≤ 4 * (3 * Optimization.finMax 1 L p + σ kε) := by linarith
    have hKm : 0 < 4 * (3 * Optimization.finMax 1 L p + arqpcSigmaMax P L (fun _ => 0) 0 p 0) := by
      linarith
    refine le_min ?_ ?_
    · calc arqpSCKappaRad P L p * ε j
          ≤ 1 / (4 * (3 * Optimization.finMax 1 L p + arqpcSigmaMax P L (fun _ => 0) 0 p 0)) * 1 :=
            mul_le_mul hrad1 hε1 hε0.le (div_pos one_pos hKm).le
        _ ≤ 1 := by
            rw [mul_one, div_le_one hKm]; linarith
    · calc arqpSCKappaRad P L p * ε j
          ≤ 1 / (4 * (3 * Optimization.finMax 1 L p + arqpcSigmaMax P L (fun _ => 0) 0 p 0)) *
              ε j := mul_le_mul_of_nonneg_right hrad1 hε0.le
        _ ≤ ε j / (4 * (3 * Optimization.finMax 1 L p + σ kε)) := by
            rw [one_div_mul_eq_div]
            exact div_le_div_of_nonneg_left hε0.le hK hK'

/-- An ARqp-SC call (ARqpC-SC with `c = 0`, `h = 0`, initial radii `1`) on `F ≥ f_low` from
`x^S ∈ X`, under anchored bounds for `F` on a set `S` containing the sublevel set of `F` at `x^S`,
exists and terminates at a feasible `(ε, δ_ε)`-approximate `q`-th order minimizer, with radii
`δ_{ε,j} ≥ κ_ρ ε_j` (`algorithm_14_1_1.zero_exists_cert_anchored`). -/
private theorem inner_core_anchored {X₀ S : Set ℝⁿ} {L : ℕ → ℝ}
    (hF : AnchoredCompositeBounds F (zeroCon n) X₀ S p L (fun _ => 0)) (hXX₀ : X ⊆ X₀)
    {flow : ℝ} (hb : ∀ y ∈ X, flow ≤ F y) (P : ARqpCParams) (hθς : P.θ < P.ς) (hq : 1 ≤ q)
    (hqp : q ≤ p) (hX : IsClosed X) {xS : ℝⁿ} (hxS : xS ∈ X)
    (hS : ∀ y ∈ X, F y ≤ F xS → y ∈ S) (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1) :
    ∃ (x s : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → ℝⁿ) (kε : ℕ),
      algorithm_14_1_1 F (zeroCon n) zeroOuter X p q P ε (fun _ => 1) x s σ δ δs d dm ∧
      x 0 = xS ∧
      Optimization.IsFirstHit (arqpcStop F (zeroCon n) zeroOuter p q P ε x s σ δ d) kε ∧
      (∀ i ≤ kε, x i ∈ X) ∧
      (∀ i j, i ≤ j → j ≤ kε → F (x j) ≤ F (x i)) ∧
      ∃ δε : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, 0 < δε j ∧ δε j ≤ 1) ∧
        (∀ j ∈ Finset.Icc 1 q, arqpSCKappaRad P L p * ε j ≤ δε j) ∧
        Optimization.IsEpsDeltaApprox (ftaylorSeries ℝ F (x kε)) {e | x kε + e ∈ X} q ε δε := by
  obtain ⟨x, s, σ, δ, δs, d, dm, hx0, hr⟩ := exists_isARqpCRun_of_hLip
    (f := F) (c := zeroCon n) assumptionHLip_zeroOuter assumptionHS0_zeroOuter P hq hqp hε
    (fun _ _ => ⟨one_pos, le_rfl⟩) hX hxS
  have hA := hF.mono (compositeSublevel_zero_subset (hx0 ▸ hS))
  have hmε : ∀ j ∈ Finset.Icc 1 q, ε j ^ (j + 1) ≤ 1 := fun j hj =>
    pow_le_one₀ (hε j hj).1.le (hε j hj).2
  obtain ⟨j₀, hj₀, hmin⟩ := Optimization.exists_finMin_eq hq hmε
  obtain ⟨kε, hhit, -, -, -, -⟩ := theorem_14_2_4_arqpc_anchored hr hθς hA hXX₀
    assumptionHLip_zeroOuter assumptionHS0_zeroOuter (wlow := flow)
    (fun y hy => by simpa using hb y hy)
    (mε := Optimization.finMin 1 (fun j => ε j ^ (j + 1)) q)
    (by rw [hmin]; exact pow_pos (hε j₀ hj₀).1 _) (fun j hj => Optimization.finMin_le hj)
  exact ⟨x, s, σ, δ, δs, d, dm, kε, hr, hx0, hhit, fun i hi => hr.mem fun l hl =>
    hhit.2 l (hl.trans_le hi), hr.zero_antitone hhit, hr.zero_exists_cert_anchored hA hXX₀ hhit⟩

/-- `(y, δ)` is the output of a call `INNER(F, X, q, x^S, ε)` realized by ARqp-SC: `y` is the
first termination iterate of an ARqpC-SC run with `c = 0`, `h = 0` and initial radii `1` on `F`
from `x^S` (an ARqp-SC run, `algorithm_14_1_1.zero_algorithm_12_2_2_feasible`), and the radii
`δ ∈ (0, 1]^q` certify (14.3.19) at `y`. -/
def IsARqpSCOutput (F : ℝⁿ → ℝ) (X : Set ℝⁿ) (p q : ℕ) (P : ARqpCParams) (ε : ℕ → ℝ)
    (xS y : ℝⁿ) (δ : ℕ → ℝ) : Prop :=
  (∃ (x s : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → ℝⁿ) (kε : ℕ),
    algorithm_14_1_1 F (zeroCon n) zeroOuter X p q P ε (fun _ => 1) x s σ δ δs d dm ∧
    Optimization.IsFirstHit (arqpcStop F (zeroCon n) zeroOuter p q P ε x s σ δ d) kε ∧
    x 0 = xS ∧ x kε = y) ∧
  (∀ j ∈ Finset.Icc 1 q, 0 < δ j ∧ δ j ≤ 1) ∧
  Optimization.IsEpsDeltaApprox (ftaylorSeries ℝ F y) {e | y + e ∈ X} q ε δ

namespace IsARqpSCOutput

variable {xS y : ℝⁿ} {δ' : ℕ → ℝ}

/-- The output of an ARqp-SC call is the output of an `algorithm_12_2_2_feasible` run. -/
theorem exists_algorithm_12_2_2_feasible (h : IsARqpSCOutput F X p q P ε xS y δ') :
    ∃ (x s : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → ℝⁿ) (kε : ℕ),
      Chapter12.algorithm_12_2_2_feasible F X P.toARqpParams p q ε (fun _ => 1) x s σ δ δs d dm ∧
      x 0 = xS ∧ x kε = y := by
  obtain ⟨⟨x, s, σ, δ, δs, d, dm, kε, hr, -, h0, hy⟩, -⟩ := h
  exact ⟨x, s, σ, δ, δs, d, dm, kε, hr.zero_algorithm_12_2_2_feasible, h0, hy⟩

/-- The output is feasible. -/
theorem mem (h : IsARqpSCOutput F X p q P ε xS y δ') : y ∈ X := by
  obtain ⟨⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, -, rfl⟩, -⟩ := h
  exact hr.mem hhit.2

/-- INNER does not increase `F`. -/
theorem le (h : IsARqpSCOutput F X p q P ε xS y δ') : F y ≤ F xS := by
  obtain ⟨⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, rfl, rfl⟩, -⟩ := h
  exact hr.zero_antitone hhit 0 kε (Nat.zero_le _) le_rfl

/-- The output radii lie in `(0, 1]`. -/
theorem radius_mem (h : IsARqpSCOutput F X p q P ε xS y δ') :
    ∀ j ∈ Finset.Icc 1 q, 0 < δ' j ∧ δ' j ≤ 1 := h.2.1

/-- The output satisfies (14.3.19). -/
theorem isEpsDeltaApprox (h : IsARqpSCOutput F X p q P ε xS y δ') :
    Optimization.IsEpsDeltaApprox (ftaylorSeries ℝ F y) {e | y + e ∈ X} q ε δ' := h.2.2

end IsARqpSCOutput

/-- The constant `κ_C = (|log γ₁| + log(σ_max/σ₀))/log γ₂ + 2` of Theorem 14.2.4 (ARqpC-SC row
with `c = 0`, `h = 0`) for an objective satisfying f.D1pL with constants `L`. -/
noncomputable def arqpSCKappaC (P : ARqpCParams) (L : ℕ → ℝ) (p : ℕ) : ℝ :=
  (|Real.log P.γ₁| + Real.log (arqpcSigmaMax P L (fun _ => 0) 0 p 0 / P.σ₀)) /
    Real.log P.γ₂ + 2

/-- The constant `κ_F = κ_uns/κ_decr + 2 κ_C` of the cost contract (14.3.20) for function
evaluations of an ARqp-SC call. -/
noncomputable def arqpSCKappaF (P : ARqpCParams) (L : ℕ → ℝ) (p q : ℕ) : ℝ :=
  arqpSCKappaUns P / arqpSCKappaDecr P L p q + 2 * arqpSCKappaC P L p

/-- The constant `κ_D = 1/κ_decr + 4` of the cost contract (14.3.21) for derivative evaluations
of an ARqp-SC call. -/
noncomputable def arqpSCKappaD (P : ARqpCParams) (L : ℕ → ℝ) (p q : ℕ) : ℝ :=
  1 / arqpSCKappaDecr P L p q + 4

/-- `κ_C ≥ 0`. -/
theorem arqpSCKappaC_nonneg (P : ARqpCParams) (L : ℕ → ℝ) (p : ℕ) : 0 ≤ arqpSCKappaC P L p := by
  unfold arqpSCKappaC
  have := P.log_γ₂_pos
  have : 0 ≤ Real.log (arqpcSigmaMax P L (fun _ => 0) 0 p 0 / P.σ₀) :=
    Real.log_nonneg ((one_le_div P.σ₀_pos).2 (Optimization.σ₀_le_arSigmaMax _ _))
  positivity

/-- `(y, δ)` is the output of an ARqp-SC call `INNER(F, X, q, x^S, ε)` (as in `IsARqpSCOutput`)
whose run uses `nF` evaluations of `F` and `nD` evaluations of its derivatives
(`Optimization.funEvalCount` and `Optimization.derivEvalCount` at its first termination
index). -/
def IsARqpSCOutputCost (F : ℝⁿ → ℝ) (X : Set ℝⁿ) (p q : ℕ) (P : ARqpCParams) (ε : ℕ → ℝ)
    (xS y : ℝⁿ) (δ : ℕ → ℝ) (nF nD : ℕ) : Prop :=
  (∃ (x s : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → ℝⁿ) (kε : ℕ),
    algorithm_14_1_1 F (zeroCon n) zeroOuter X p q P ε (fun _ => 1) x s σ δ δs d dm ∧
    Optimization.IsFirstHit (arqpcStop F (zeroCon n) zeroOuter p q P ε x s σ δ d) kε ∧
    x 0 = xS ∧ x kε = y ∧ nF = Optimization.funEvalCount kε ∧
    nD = Optimization.derivEvalCount (fun k => P.η₁ ≤ Optimization.arqpRatio
      (fun y => F y + zeroOuter (zeroCon n y))
      (fun k => arqpcData F (zeroCon n) zeroOuter p (x k) (σ k)) x s k) kε) ∧
  (∀ j ∈ Finset.Icc 1 q, 0 < δ j ∧ δ j ≤ 1) ∧
  Optimization.IsEpsDeltaApprox (ftaylorSeries ℝ F y) {e | y + e ∈ X} q ε δ

/-- An ARqp-SC call with costs is an ARqp-SC call. -/
theorem IsARqpSCOutputCost.isARqpSCOutput {xS y : ℝⁿ} {δ' : ℕ → ℝ} {nF nD : ℕ}
    (h : IsARqpSCOutputCost F X p q P ε xS y δ' nF nD) : IsARqpSCOutput F X p q P ε xS y δ' := by
  obtain ⟨⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, h0, hy, -, -⟩, hδ, happ⟩ := h
  exact ⟨⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, h0, hy⟩, hδ, happ⟩

/-- One INNER call by ARqp-SC with its evaluation counts under anchored bounds for `F` on a set
`S` containing the sublevel set of `F` at `x^S` (`exists_isARqpSCOutputCost_anchored` under the
global
assumption). -/
theorem exists_isARqpSCOutputCost_anchored {X₀ S : Set ℝⁿ} {L : ℕ → ℝ}
    (hF : AnchoredCompositeBounds F (zeroCon n) X₀ S p L (fun _ => 0)) (hXX₀ : X ⊆ X₀)
    {flow : ℝ} (hb : ∀ y ∈ X, flow ≤ F y) (P : ARqpCParams) (hθς : P.θ < P.ς) (hq : 1 ≤ q)
    (hqp : q ≤ p) (hX : IsClosed X) {xS : ℝⁿ} (hxS : xS ∈ X)
    (hS : ∀ y ∈ X, F y ≤ F xS → y ∈ S) (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1) :
    ∃ (y : ℝⁿ) (δ : ℕ → ℝ) (nF nD : ℕ), IsARqpSCOutputCost F X p q P ε xS y δ nF nD := by
  obtain ⟨x, s, σ, δ, δs, d, dm, kε, hr, hx0, hhit, -, -, δε, hδε, -, happ⟩ :=
    inner_core_anchored hF hXX₀ hb P hθς hq hqp hX hxS hS hε
  exact ⟨x kε, δε, _, _, ⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, hx0, rfl, rfl, rfl⟩, hδε, happ⟩

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
  obtain ⟨⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, hx0, -, rfl, rfl⟩, -, -⟩ := h
  have hq := hr.one_le_q
  have hp : 1 ≤ p := hq.trans hr.q_le_p
  have hε := hr.ε_mem
  have hmε : ∀ j ∈ Finset.Icc 1 q, ε j ^ (j + 1) ≤ 1 := fun j hj =>
    pow_le_one₀ (hε j hj).1.le (hε j hj).2
  obtain ⟨j₀, hj₀, hmin⟩ := Optimization.exists_finMin_eq hq hmε
  set mε := Optimization.finMin 1 (fun j => ε j ^ (j + 1)) q
  have hmε0 : 0 < mε := by rw [hmin]; exact pow_pos (hε j₀ hj₀).1 _
  have hA := hF.mono (compositeSublevel_zero_subset (hx0 ▸ hS))
  obtain ⟨kε', hhit', -, -, hF', hD'⟩ := theorem_14_2_4_arqpc_anchored hr hθς hA hXX₀
    assumptionHLip_zeroOuter assumptionHS0_zeroOuter (wlow := 0)
    (fun y hy => by simpa using hb y hy) hmε0 (fun j hj => Optimization.finMin_le hj)
  obtain rfl := hhit'.unique hhit
  have e0 : F (x 0) + zeroOuter (zeroCon n (x 0)) - 0 = F xS := by simp [hx0]
  rw [e0] at hF' hD'
  -- the maximum `S = max_j ε_j^{-(j+1)}`
  set S := ⨆ j : Finset.Icc 1 q, ε j ^ (-(fun l : ℕ => (l : ℝ) + 1) j)
  have hbdd : BddAbove (Set.range fun j : Finset.Icc 1 q =>
      ε j ^ (-(fun l : ℕ => (l : ℝ) + 1) j)) := (Set.finite_range _).bddAbove
  have hS : ∀ j ∈ Finset.Icc 1 q, (ε j ^ (j + 1))⁻¹ ≤ S := fun j hj => by
    refine le_trans (le_of_eq ?_) (le_ciSup hbdd ⟨j, hj⟩)
    rw [Real.rpow_neg (hε j hj).1.le]
    congr 1
    rw [← Real.rpow_natCast]
    push_cast
    rfl
  have h1q : 1 ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, hq⟩
  have hFx : 0 ≤ F xS := hb xS hxS
  have hκ : 0 < arqpSCKappaDecr P L p q := arqpSCKappaDecr_pos_of hF.one_le hθς
  have hκA := arqpSCKappaUns_nonneg P
  have hκC := arqpSCKappaC_nonneg P L p
  have hinv : mε⁻¹ ≤ S := by rw [hmin]; exact hS j₀ hj₀
  have habs' : 1 ≤ 2 * F xS * S := by
    have h1 : (ε 1 ^ 2)⁻¹ ≤ S := hS 1 h1q
    have hε1 := (hε 1 h1q).1
    have : 1 ≤ 2 * F xS * (ε 1 ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      linarith
    exact this.trans (by gcongr)
  have hdiv : F xS / (P.η₁ * (kappaDm2 P L (fun _ => 0) 0 p q 0 * mε)) =
      F xS * mε⁻¹ / arqpSCKappaDecr P L p q := by
    unfold arqpSCKappaDecr
    field_simp
  rw [hdiv] at hF' hD'
  have hFS : F xS * mε⁻¹ ≤ F xS * S := by gcongr
  unfold innerEvalBound
  constructor
  · refine hF'.trans ?_
    unfold arqpSCKappaF
    change _ ≤ (arqpSCKappaUns P / arqpSCKappaDecr P L p q + 2 * arqpSCKappaC P L p) * F xS * S
    have e1 : (1 + |Real.log P.γ₁| / Real.log P.γ₂) = arqpSCKappaUns P := rfl
    have e2 : (|Real.log P.γ₁| + Real.log (arqpcSigmaMax P L (fun _ => 0) 0 p 0 / P.σ₀)) /
        Real.log P.γ₂ + 2 = arqpSCKappaC P L p := rfl
    rw [e1, e2]
    have : arqpSCKappaUns P * (F xS * mε⁻¹ / arqpSCKappaDecr P L p q) ≤
        arqpSCKappaUns P / arqpSCKappaDecr P L p q * (F xS * S) := by
      rw [mul_div_assoc', div_mul_eq_mul_div]
      gcongr
    nlinarith
  · refine hD'.trans ?_
    unfold arqpSCKappaD
    change _ ≤ (1 / arqpSCKappaDecr P L p q + 4) * F xS * S
    have : F xS * mε⁻¹ / arqpSCKappaDecr P L p q ≤ 1 / arqpSCKappaDecr P L p q * (F xS * S) := by
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
additive form,
is `IsARqpSCOutputCost.cost_le_arqp_add_anchored`. -/
theorem IsARqpSCOutputCost.cost_le {L : ℕ → ℝ} (hF : Chapter12.AssumptionD1pL F p L)
    (hb : ∀ y ∈ X, 0 ≤ F y) (hθς : P.θ < P.ς) {xS y : ℝⁿ} {δ' : ℕ → ℝ} {nF nD : ℕ}
    (h : IsARqpSCOutputCost F X p q P ε xS y δ' nF nD) (hxS : xS ∈ X)
    (habs : ε 1 ^ 2 ≤ 2 * F xS) :
    (nF : ℝ) ≤ innerEvalBound (arqpSCKappaF P L p q) (fun l => (l : ℝ) + 1) q (F xS) ε ∧
    (nD : ℝ) ≤ innerEvalBound (arqpSCKappaD P L p q) (fun l => (l : ℝ) + 1) q (F xS) ε := by
  have hp : 1 ≤ p := by
    obtain ⟨⟨_, _, _, _, _, _, _, _, hr, -⟩, -⟩ := h
    exact hr.one_le_q.trans hr.q_le_p
  exact IsARqpSCOutputCost.cost_le_anchored (AnchoredCompositeBounds.of_global hF
    (assumptionCD1pL_zeroCon p) hp univ) (subset_univ X) hb hθς h hxS (fun y _ _ => mem_univ y)
    habs

/-- The decrease constant `η₁ κ_{Δm}` of the ARqp-SC row of Lemma 14.2.2 in radii mode `u`
(`Optimization.arqpKappaDmOf u`). -/
noncomputable def arqpRowKappaDecr (u : Prop) [Decidable u] (P : ARqpCParams) (L : ℕ → ℝ)
    (p q : ℕ) : ℝ :=
  P.η₁ * Optimization.arqpKappaDmOf u P.toARqpParams L p q

/-- **The cost of an ARqp-SC call with the exponents of its row of (14.2.12), additive form,
anchored**: as `IsARqpSCOutputCost.cost_le_arqp_add_anchored`, under the anchored bounds of `F` on
a set
`S` containing every `y ∈ X` with `F(y) ≤ F(x^S)` (an open convex `X₀ ⊇ X`; the book's
f.D1pLaB.X) in place of F.D1pL. -/
theorem IsARqpSCOutputCost.cost_le_arqp_add_anchored {X₀ S : Set ℝⁿ} {L : ℕ → ℝ}
    (hF : AnchoredCompositeBounds F (zeroCon n) X₀ S p L (fun _ => 0)) (hXX₀ : X ⊆ X₀)
    (hb : ∀ y ∈ X, 0 ≤ F y) (hθς : P.θ < P.ς) {u : Prop} [Decidable u]
    (hu : u → q = 1 ∧ Convex ℝ X)
    {xS y : ℝⁿ} {δ' : ℕ → ℝ} {nF nD : ℕ}
    (h : IsARqpSCOutputCost F X p q P ε xS y δ' nF nD) (hxS : xS ∈ X)
    (hS : ∀ y ∈ X, F y ≤ F xS → y ∈ S) :
    (nF : ℝ) ≤ innerEvalBound (arqpSCKappaUns P / arqpRowKappaDecr u P L p q)
        (Optimization.arqpPiOf u p) q (F xS) ε + arqpSCKappaC P L p ∧
    (nD : ℝ) ≤ innerEvalBound (1 / arqpRowKappaDecr u P L p q) (Optimization.arqpPiOf u p) q
        (F xS) ε + 2 := by
  obtain ⟨⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, hx0, -, rfl, rfl⟩, -, -⟩ := h
  have hq := hr.one_le_q
  have hε := hr.ε_mem
  have hLp : 1 ≤ L p := hF.one_le
  have hA := hF.mono (compositeSublevel_zero_subset (hx0 ▸ hS))
  have hκ : 0 < P.η₁ * Optimization.arqpKappaDmOf u P.toARqpParams L p q :=
    mul_pos P.η₁_pos (Optimization.arqpKappaDmOf_pos u P.σmin_pos hθς hLp)
  set mε := Optimization.finMin 1 (fun j => ε j ^ Optimization.arqpPiOf u p j) q
  obtain ⟨j₀, hj₀, hmin⟩ := Optimization.exists_finMin_eq hq
    (u := fun j => ε j ^ Optimization.arqpPiOf u p j) (b := 1) fun j hj =>
      Real.rpow_le_one (hε j hj).1.le (hε j hj).2 (Optimization.arqpPiOf_nonneg u p j)
  have hmε0 : 0 < mε := by
    change 0 < Optimization.finMin 1 (fun j => ε j ^ Optimization.arqpPiOf u p j) q
    rw [hmin]; exact Real.rpow_pos_of_pos (hε j₀ hj₀).1 _
  obtain ⟨kε', hhit', hF', hD'⟩ := hr.run.toIsARRun.exists_isFirstHit_of_decrease
    (σmax := arqpcSigmaMax P L (fun _ => 0) 0 p 0)
    (fun k hk => sigma_le_arqpcSigmaMax_anchored hr hA hXX₀ assumptionHLip_zeroOuter hk k le_rfl)
    (V := fun k => F (x k)) (Vlow := 0) (mul_pos hκ hmε0)
    (fun k hk => by
      have hkε : k < kε := not_le.1 fun hge => hk kε hge hhit.1
      exact hr.zero_antitone hhit k (k + 1) (by omega) (by omega))
    (fun k hk => hb _ (hr.mem hk))
    (fun k hk hs => by
      have := hr.zero_decrease_arqp_anchored hA hXX₀ hθς hu (k := k) (fun i hi => hk i (by omega))
        hs
        (fun h' => hk (k + 1) le_rfl (Or.inl h'))
      rwa [mul_assoc])
  obtain rfl := hhit'.unique hhit
  simp only [hx0, sub_zero] at hF' hD'
  -- the maximum `S = max_j ε_j^{-π_j}`
  set S := ⨆ j : Finset.Icc 1 q, ε j ^ (-Optimization.arqpPiOf u p j)
  have hbdd : BddAbove (Set.range fun j : Finset.Icc 1 q =>
      ε j ^ (-Optimization.arqpPiOf u p j)) := (Set.finite_range _).bddAbove
  have hS : ∀ j ∈ Finset.Icc 1 q, ε j ^ (-Optimization.arqpPiOf u p j) ≤ S := fun j hj =>
    le_ciSup hbdd ⟨j, hj⟩
  have hFx : 0 ≤ F xS := hb xS hxS
  have hκA := arqpSCKappaUns_nonneg P
  have hκC := arqpSCKappaC_nonneg P L p
  have hinv : mε⁻¹ ≤ S := by
    change (Optimization.finMin 1 (fun j => ε j ^ Optimization.arqpPiOf u p j) q)⁻¹ ≤ S
    rw [hmin, ← Real.rpow_neg (hε j₀ hj₀).1.le]
    exact hS j₀ hj₀
  have hdiv : F xS / (P.η₁ * Optimization.arqpKappaDmOf u P.toARqpParams L p q * mε) =
      F xS * mε⁻¹ / (P.η₁ * Optimization.arqpKappaDmOf u P.toARqpParams L p q) := by
    field_simp
  rw [hdiv] at hF' hD'
  have hFS : F xS * mε⁻¹ ≤ F xS * S := by gcongr
  unfold innerEvalBound arqpRowKappaDecr
  constructor
  · refine hF'.trans ?_
    have e1 : (1 + |Real.log P.γ₁| / Real.log P.γ₂) = arqpSCKappaUns P := rfl
    have e2 : (|Real.log P.γ₁| + Real.log (arqpcSigmaMax P L (fun _ => 0) 0 p 0 / P.σ₀)) /
        Real.log P.γ₂ + 2 = arqpSCKappaC P L p := rfl
    rw [e1, e2]
    have : arqpSCKappaUns P *
        (F xS * mε⁻¹ / (P.η₁ * Optimization.arqpKappaDmOf u P.toARqpParams L p q))
        ≤ arqpSCKappaUns P / (P.η₁ * Optimization.arqpKappaDmOf u P.toARqpParams L p q) *
          F xS * S := by
      rw [show arqpSCKappaUns P / (P.η₁ * Optimization.arqpKappaDmOf u P.toARqpParams L p q) *
          F xS * S = arqpSCKappaUns P *
            (F xS * S / (P.η₁ * Optimization.arqpKappaDmOf u P.toARqpParams L p q)) by ring]
      gcongr
    linarith
  · refine hD'.trans ?_
    have : F xS * mε⁻¹ / (P.η₁ * Optimization.arqpKappaDmOf u P.toARqpParams L p q) ≤
        1 / (P.η₁ * Optimization.arqpKappaDmOf u P.toARqpParams L p q) * F xS * S := by
      rw [show 1 / (P.η₁ * Optimization.arqpKappaDmOf u P.toARqpParams L p q) * F xS * S =
          F xS * S / (P.η₁ * Optimization.arqpKappaDmOf u P.toARqpParams L p q) by ring]
      gcongr
    linarith

/-- The tolerances of an ARqp-SC call lie in `(0, 1]`. -/
theorem IsARqpSCOutputCost.ε_mem {xS y : ℝⁿ} {δ' : ℕ → ℝ} {nF nD : ℕ}
    (h : IsARqpSCOutputCost F X p q P ε xS y δ' nF nD) :
    ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1 := by
  obtain ⟨⟨x, s, σ, δ, δs, d, dm, kε, hr, -⟩, -⟩ := h
  exact hr.ε_mem

/-- An ARqp-SC call evaluates `F` and its derivatives at least once. -/
theorem IsARqpSCOutputCost.one_le {xS y : ℝⁿ} {δ' : ℕ → ℝ} {nF nD : ℕ}
    (h : IsARqpSCOutputCost F X p q P ε xS y δ' nF nD) : 1 ≤ nF ∧ 1 ≤ nD := by
  obtain ⟨⟨x, s, σ, δ, δs, d, dm, kε, -, -, -, -, rfl, rfl⟩, -, -⟩ := h
  simp [Optimization.derivEvalCount]

/-- The constant `κ_F = κ_uns/(η₁ κ_{Δm}) + 2 κ_C` of the cost contract (14.3.20) for function
evaluations of an ARqp-SC call, with the ARqp-SC row of Lemma 14.2.2 in radii mode `u`. -/
noncomputable def arqpRowKappaF (u : Prop) [Decidable u] (P : ARqpCParams) (L : ℕ → ℝ)
    (p q : ℕ) : ℝ :=
  arqpSCKappaUns P / arqpRowKappaDecr u P L p q + 2 * arqpSCKappaC P L p

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
  have hκC := arqpSCKappaC_nonneg P L p
  unfold innerEvalBound at h1 h2 ⊢
  unfold arqpRowKappaF arqpRowKappaD
  constructor
  · nlinarith
  · nlinarith

/-- `1 ≤ 2 (R²/2) (β R e)^{-π}` for `π ≥ 2`, `β e ≤ 1` and `β R e ≤ 1`: the absorption condition of
the multiplicative cost contract for a LENq-SC call from a point with `‖r‖ = R`. -/
private theorem one_le_absorb {β e R π : ℝ} (hβ : 0 < β) (he : 0 < e) (hβe : β * e ≤ 1)
    (hR : 0 < R) (ha : β * R * e ≤ 1) (hπ : 2 ≤ π) :
    1 ≤ 2 * (R ^ 2 / 2) * (β * R * e) ^ (-π) := by
  set a := β * R * e with hadef
  have ha0 : 0 < a := by positivity
  have h1 : a ^ (-(2 : ℝ)) ≤ a ^ (-π) := Real.rpow_le_rpow_of_exponent_ge ha0 ha (by linarith)
  have h2 : a ^ (-(2 : ℝ)) = (a ^ 2)⁻¹ := by
    rw [Real.rpow_neg ha0.le]
    norm_cast
  have haR : a ≤ R := by
    have : a = (β * e) * R := by rw [hadef]; ring
    rw [this]
    nlinarith
  have h3 : a ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ ha0.le haR 2
  have h4 : 1 ≤ R ^ 2 * (a ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    linarith
  calc (1 : ℝ) ≤ R ^ 2 * (a ^ 2)⁻¹ := h4
    _ = 2 * (R ^ 2 / 2) * a ^ (-(2 : ℝ)) := by rw [h2]; ring
    _ ≤ 2 * (R ^ 2 / 2) * a ^ (-π) := by gcongr

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
  exact one_le_absorb hβ0 he (by nlinarith) hR hle hπ

/-- **ARqp runs on `ℝⁿ` with unit radii terminate, under anchored bounds**: as
`unit_core_anchored`, with
`F` satisfying the anchored bounds of the ARqp analysis on a set `S` containing the sublevel set
`{y | F(y) ≤ F(x^S)}` (with `X₀ = ℝⁿ`) in place of F.D1pL. -/
theorem unit_core_anchored {L : ℕ → ℝ} {S : Set ℝⁿ}
    (hF : AnchoredCompositeBounds F (zeroCon n) univ S p L (fun _ => 0)) {flow : ℝ}
    (hb : ∀ y, flow ≤ F y) (P : ARqpCParams) (hθς : P.θ < P.ς) (hq : 1 ≤ q) (hq2 : q ≤ 2)
    (hqp : q ≤ p) (xS : ℝⁿ) (hS : ∀ y, F y ≤ F xS → y ∈ S)
    (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1) :
    ∃ (x s : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δr δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → ℝⁿ) (kε : ℕ),
      Chapter12.algorithm_12_2_2 F P.toARqpParams p q ε (fun _ => 1) x s σ δr δs d dm ∧
      (∀ k, (∀ i ≤ k, ¬ Optimization.arqpStop F P.toARqpParams p q ε x s σ δr d i) →
        ∀ j ∈ Finset.Icc 1 q, δs k j = 1) ∧
      Optimization.IsFirstHit (Optimization.arqpStop F P.toARqpParams p q ε x s σ δr d) kε ∧
      x 0 = xS ∧ (∀ i j, i ≤ j → j ≤ kε → F (x j) ≤ F (x i)) ∧
      Optimization.IsEpsDeltaApprox (ftaylorSeries ℝ F (x kε))
        {e | x kε + e ∈ (univ : Set ℝⁿ)} q ε (fun _ => 1) := by
  have hp : 1 ≤ p := hq.trans hqp
  have hε' : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1 := fun j hj => hε j hj
  have hδ₀ : ∀ j ∈ Finset.Icc 1 q, (0 : ℝ) < (fun _ => (1 : ℝ)) j ∧ (fun _ => (1 : ℝ)) j ≤ 1 :=
    fun _ _ => ⟨one_pos, le_rfl⟩
  obtain ⟨x, s, σ, δr, δs, d, dm, h0, h, hrad⟩ := Chapter12.algorithm_12_2_2_exists F
    P.toARqpParams hp hqp (fun j hj => (hε j hj).1) hδ₀ xS
  have hδs : ∀ k, (∀ i ≤ k, ¬ Optimization.arqpStop F P.toARqpParams p q ε x s σ δr d i) →
      ∀ j ∈ Finset.Icc 1 q, δs k j = 1 := fun k hk j hj =>
    hrad k (fun i hi => hk i hi.le) j hj ((Finset.mem_Icc.1 hj).2.trans hq2)
  obtain ⟨kε, hhit, -, -, -, -⟩ := Optimization.IsARqpRun.complexity (X := univ)
    (C := univ) (fun y _ => hb y) hF.lipschitzDerivsAnchored_f hF.one_le
    (fun j hj y hy => (hF.jet_bounds hy).1 j hj) (subset_univ _) (fun y _ hy => hS y (h0 ▸ hy)) hq
        hqp P.σmin_pos hθς
    hε' hδ₀ h (u := True)
    ⟨fun _ => ⟨fun _ _ => rfl, hδs⟩, fun h' => absurd trivial h'⟩
  have h1 : Optimization.arqpStop₁ P.toARqpParams q ε (Optimization.arqpData F p x σ) δr d kε := by
    by_contra h1
    exact Chapter12.lemma_12_2_10_le_two (hF.contDiffAt_f (mem_univ _)) hqp hε' hδ₀ h hhit h1 hq2
  have hone := h.delta_eq_one (fun _ _ => rfl) hδs kε hhit.2
  have hcert := Optimization.MeasureTestPasses.isEpsDeltaApprox P.ς_pos (h.witness kε hhit.2) h1
  refine ⟨x, s, σ, δr, δs, d, dm, kε, h, hδs, hhit, h0, ?_, fun j hj => ?_⟩
  · intro i j hij hj
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih =>
      exact (h.objective_le fun l hl => hhit.2 l (by omega)).trans (ih (by omega))
  · have := hcert j hj
    rwa [hone j hj] at this

/-- `(y, δ)` is the output of a call `INNER(F, ℝⁿ, q, x^S, ε)` realized by ARqp on `ℝⁿ` with unit
radii (the ARqp-SC row of (14.2.12) for `X = ℝⁿ`, `q ≤ 2`), using `nF` evaluations of `F` and `nD`
of its derivatives: `y` is the first termination iterate of an ARqp run
(`Chapter12.algorithm_12_2_2`) on `F` from `x^S` with initial radii `1` whose Step-2 radii are `1`
before termination, and the radii `δ = 1` certify (14.3.19) at `y`. -/
def IsARqpUnitOutputCost (F : ℝⁿ → ℝ) (p q : ℕ) (P : ARqpCParams) (ε : ℕ → ℝ) (xS y : ℝⁿ)
    (δ : ℕ → ℝ) (nF nD : ℕ) : Prop :=
  (∃ (x s : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δr δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → ℝⁿ) (kε : ℕ),
    Chapter12.algorithm_12_2_2 F P.toARqpParams p q ε (fun _ => 1) x s σ δr δs d dm ∧
    (∀ k, (∀ i ≤ k, ¬ Optimization.arqpStop F P.toARqpParams p q ε x s σ δr d i) →
      ∀ j ∈ Finset.Icc 1 q, δs k j = 1) ∧
    Optimization.IsFirstHit (Optimization.arqpStop F P.toARqpParams p q ε x s σ δr d) kε ∧
    x 0 = xS ∧ x kε = y ∧ nF = Optimization.funEvalCount kε ∧
    nD = Optimization.derivEvalCount (fun k => P.η₁ ≤ Optimization.arqpRho F p x s σ k) kε) ∧
  (∀ j ∈ Finset.Icc 1 q, δ j = 1) ∧
  Optimization.IsEpsDeltaApprox (ftaylorSeries ℝ F y) {e | y + e ∈ (univ : Set ℝⁿ)} q ε δ

/-- One INNER call by ARqp on `ℝⁿ` with unit radii, with its evaluation counts, under the
anchored bounds of `unit_core_anchored` (`exists_isARqpUnitOutputCost_anchored` under F.D1pL). -/
theorem exists_isARqpUnitOutputCost_anchored {L : ℕ → ℝ} {S : Set ℝⁿ}
    (hF : AnchoredCompositeBounds F (zeroCon n) univ S p L (fun _ => 0))
    {flow : ℝ} (hb : ∀ y, flow ≤ F y) (P : ARqpCParams) (hθς : P.θ < P.ς) (hq : 1 ≤ q)
    (hq2 : q ≤ 2) (hqp : q ≤ p) (xS : ℝⁿ) (hS : ∀ y, F y ≤ F xS → y ∈ S)
    (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1) :
    ∃ (y : ℝⁿ) (nF nD : ℕ), IsARqpUnitOutputCost F p q P ε xS y (fun _ => 1) nF nD := by
  obtain ⟨x, s, σ, δr, δs, d, dm, kε, h, hδs, hhit, h0, -, hcert⟩ :=
    unit_core_anchored hF hb P hθς hq hq2 hqp xS hS hε
  exact ⟨x kε, _, _, ⟨x, s, σ, δr, δs, d, dm, kε, h, hδs, hhit, h0, rfl, rfl, rfl⟩,
    fun _ _ => rfl, hcert⟩

namespace IsARqpUnitOutputCost

variable {xS y : ℝⁿ} {δ' : ℕ → ℝ} {nF nD : ℕ}

/-- INNER does not increase `F`. -/
theorem le (h : IsARqpUnitOutputCost F p q P ε xS y δ' nF nD) : F y ≤ F xS := by
  obtain ⟨⟨x, s, σ, δr, δs, d, dm, kε, hr, -, hhit, rfl, rfl, -, -⟩, -⟩ := h
  have : ∀ j ≤ kε, F (x j) ≤ F (x 0) := by
    intro j hj
    induction j with
    | zero => exact le_rfl
    | succ j ih =>
      exact (hr.objective_le fun l hl => hhit.2 l (by omega)).trans (ih (by omega))
  exact this kε le_rfl

/-- The additive cost contract of an ARqp call on `ℝⁿ` with unit radii, under the anchored
bounds of `unit_core_anchored` (`IsARqpUnitOutputCost.cost_le_add_anchored` under F.D1pL). -/
theorem cost_le_add_anchored {L : ℕ → ℝ} {S : Set ℝⁿ}
    (hF : AnchoredCompositeBounds F (zeroCon n) univ S p L (fun _ => 0)) (hb : ∀ y, 0 ≤ F y)
    (hθς : P.θ < P.ς) (hq : 1 ≤ q) (hqp : q ≤ p) (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1)
    (h : IsARqpUnitOutputCost F p q P ε xS y δ' nF nD) (hS : ∀ y, F y ≤ F xS → y ∈ S) :
    (nF : ℝ) ≤ innerEvalBound (Optimization.kappaAARqpOf True P.toARqpParams L p q)
        (Optimization.arqpPiOf True p) q (F xS) ε + Optimization.kappaCARqp P.toARqpParams L p ∧
    (nD : ℝ) ≤ innerEvalBound (Optimization.kappaSARqpOf True P.toARqpParams L p q)
        (Optimization.arqpPiOf True p) q (F xS) ε + 2 := by
  obtain ⟨⟨x, s, σ, δr, δs, d, dm, kε, hr, hδs, hhit, hx0, -, rfl, rfl⟩, -, -⟩ := h
  have hp : 1 ≤ p := hq.trans hqp
  have hε' : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1 := fun j hj => hε j hj
  have hδ₀ : ∀ j ∈ Finset.Icc 1 q, (0 : ℝ) < (fun _ => (1 : ℝ)) j ∧ (fun _ => (1 : ℝ)) j ≤ 1 :=
    fun _ _ => ⟨one_pos, le_rfl⟩
  obtain ⟨kε', hhit', -, -, hF', hD'⟩ := Optimization.IsARqpRun.complexity (X := univ)
    (C := univ) (fun y _ => hb y) hF.lipschitzDerivsAnchored_f hF.one_le
    (fun j hj y hy => (hF.jet_bounds hy).1 j hj) (subset_univ _) (fun y _ hy => hS y (hx0 ▸ hy)) hq
        hqp
    P.σmin_pos hθς hε' hδ₀ hr
    (u := True) ⟨fun _ => ⟨fun _ _ => rfl, hδs⟩, fun h' => absurd trivial h'⟩
  obtain rfl := hhit'.unique hhit
  rw [hx0, sub_zero] at hF' hD'
  set mε := Optimization.finMin 1 (fun j => ε j ^ Optimization.arqpPiOf True p j) q
  obtain ⟨j₀, hj₀, hmin⟩ := Optimization.exists_finMin_eq hq
    (u := fun j => ε j ^ Optimization.arqpPiOf True p j) (b := 1) fun j hj =>
      Real.rpow_le_one (hε j hj).1.le (hε j hj).2 (Optimization.arqpPiOf_nonneg True p j)
  have hmε0 : 0 < mε := by
    change 0 < Optimization.finMin 1 (fun j => ε j ^ Optimization.arqpPiOf True p j) q
    rw [hmin]; exact Real.rpow_pos_of_pos (hε j₀ hj₀).1 _
  set S := ⨆ j : Finset.Icc 1 q, ε j ^ (-Optimization.arqpPiOf True p j)
  have hbdd : BddAbove (Set.range fun j : Finset.Icc 1 q =>
      ε j ^ (-Optimization.arqpPiOf True p j)) := (Set.finite_range _).bddAbove
  have hinv : mε⁻¹ ≤ S := by
    change (Optimization.finMin 1 (fun j => ε j ^ Optimization.arqpPiOf True p j) q)⁻¹ ≤ S
    rw [hmin, ← Real.rpow_neg (hε j₀ hj₀).1.le]
    exact le_ciSup hbdd ⟨j₀, hj₀⟩
  have hFx : 0 ≤ F xS := hb xS
  have hLp : 1 ≤ L p := hF.one_le
  have hκs := Optimization.kappaSARqpOf_pos (q := q) True P.σmin_pos hθς hLp
  have hκa : 0 ≤ Optimization.kappaAARqpOf True P.toARqpParams L p q := by
    rw [Optimization.kappaAARqpOf_def]
    have := P.log_γ₂_pos
    positivity
  have hFS : F xS / mε ≤ F xS * S := by
    rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left hinv hFx
  unfold innerEvalBound
  constructor
  · refine hF'.trans ?_
    have : Optimization.kappaAARqpOf True P.toARqpParams L p q * F xS / mε ≤
        Optimization.kappaAARqpOf True P.toARqpParams L p q * F xS * S := by
      rw [mul_div_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_left hFS hκa
    linarith
  · refine hD'.trans ?_
    have : Optimization.kappaSARqpOf True P.toARqpParams L p q * F xS / mε ≤
        Optimization.kappaSARqpOf True P.toARqpParams L p q * F xS * S := by
      rw [mul_div_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_left hFS hκs.le
    linarith

end IsARqpUnitOutputCost

end InnerCall

section LENq

/-- `Φ₂ ≤ Φ₂'` iff `‖r‖ ≤ ‖r'‖`. -/
theorem norm_le_of_phi2_le {r : ℝⁿ → ℝᵐ} {x y : ℝⁿ} (h : phi2 r y ≤ phi2 r x) :
    ‖r y‖ ≤ ‖r x‖ := by
  rw [phi2_apply, phi2_apply, div_le_div_iff_of_pos_right two_pos] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

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
    (fun z hz hzy => hS z hz ((norm_le_of_phi2_le hzy).trans hy0)) hε'
  exact ⟨(z, δz, nF, nD), hout.isARqpSCOutput.mem, norm_le_of_phi2_le hout.isARqpSCOutput.le,
    hout.isARqpSCOutput.radius_mem, hout.isARqpSCOutput.isEpsDeltaApprox, hout⟩

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
      (fun z hz => hS z ((norm_le_of_phi2_le hz).trans hy0)) hε'
    refine ⟨(z, fun _ => 1, nF, nD), mem_univ _, norm_le_of_phi2_le hout.le,
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
(`IsARqpSCOutputCost.one_le`), while the bound is `(κ/2) β^{-π_1} ‖r(x^S)‖^{2-π_1} ε_1^{-π_1}`,
which tends to `0` with `‖r(x^S)‖` since `π_1 < 2`; the run uses `r ≡ R` constant with `R`
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
  set κ' := max κ 0
  set b := β ^ π / (κ' + 1) with hb
  have hκ' : 0 ≤ κ' := le_max_right _ _
  have hb0 : 0 < b := by positivity
  have hb1 : b ≤ 1 := by
    rw [hb, div_le_one (by linarith)]
    have : β ^ π ≤ 1 := Real.rpow_le_one hβ0.le hβ1.le hπ0.le
    linarith
  set R := b ^ (2 - π)⁻¹ with hR
  have hs : 0 < 2 - π := by linarith
  have hR0 : 0 < R := Real.rpow_pos_of_pos hb0 _
  have hR1 : R ≤ 1 := Real.rpow_le_one hb0.le hb1 (inv_nonneg.2 hs.le)
  have hRs : R ^ (2 - π) = b := Real.rpow_inv_rpow hb0.le hs.ne'
  set r : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1) :=
    fun _ => EuclideanSpace.single 0 R
  have hr : ∀ y, ‖r y‖ = R := fun y => by simp [r, abs_of_pos hR0]
  have hΦ : Chapter12.AssumptionD1pL (phi2 r) p (fun _ => 1) := by
    have e : phi2 r = fun _ => R ^ 2 / 2 := funext fun y => by rw [phi2_apply, hr y]
    rw [e]
    refine ⟨contDiff_const, fun _ _ => le_rfl, fun j hj => (iteratedFDerivLipschitzOn_iff).2
      fun a _ b _ => ?_⟩
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
    have e1 : R ^ 2 / 2 * (β * R) ^ (-π) = β ^ (-π) * R ^ (2 - π) / 2 := by
      rw [Real.mul_rpow hβ0.le hR0.le, Real.rpow_sub hR0, Real.rpow_neg hR0.le,
        Real.rpow_two]
      field_simp
    have e2 : β ^ (-π) * b = 1 / (κ' + 1) := by
      rw [hb, Real.rpow_neg hβ0.le]
      have : 0 < β ^ π := Real.rpow_pos_of_pos hβ0 _
      field_simp
    have hpos : 0 ≤ R ^ 2 / 2 * (β * R) ^ (-π) := by positivity
    calc κ * (R ^ 2 / 2) * (β * R) ^ (-π) = κ * (R ^ 2 / 2 * (β * R) ^ (-π)) := by ring
      _ ≤ κ' * (R ^ 2 / 2 * (β * R) ^ (-π)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
      _ = κ' * (β ^ (-π) * b) / 2 := by rw [e1, hRs]; ring
      _ = κ' / (κ' + 1) / 2 := by rw [e2]; ring
      _ < 1 := by
          rw [div_div, div_lt_one (by positivity)]
          linarith
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
TPqp-GC on `X = ℝⁿ`, realized by ARqp with unit radii on `F` with tolerances `ε`: they are the
first `e + 1` iterates of an ARqp run (`Chapter12.algorithm_12_2_2`, initial radii `1`, Step-2
radii `1` before termination) on `F` whose first termination index is at least `e`, and the
successful iterations are those of the run. -/
def IsARqpUnitCall (F : ℝⁿ → ℝ) (p q : ℕ) (P : ARqpCParams) (ε : ℕ → ℝ) (xi : ℕ → ℝⁿ)
    (e : ℕ) (succ : ℕ → Prop) : Prop :=
  ∃ (x s : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δr δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → ℝⁿ) (kε : ℕ),
    Chapter12.algorithm_12_2_2 F P.toARqpParams p q ε (fun _ => 1) x s σ δr δs d dm ∧
    (∀ k, (∀ i ≤ k, ¬ Optimization.arqpStop F P.toARqpParams p q ε x s σ δr d i) →
      ∀ j ∈ Finset.Icc 1 q, δs k j = 1) ∧
    Optimization.IsFirstHit (Optimization.arqpStop F P.toARqpParams p q ε x s σ δr d) kε ∧
    e ≤ kε ∧ (∀ i ≤ e, xi i = x i) ∧
    ∀ i < e, (succ i ↔ P.η₁ ≤ Optimization.arqpRho F p x s σ i)

/-- The constant `κ_unc = κ_uns + log(σ_max/σ₀)/log γ₂` of Lemma 14.2.3 for ARqp runs on an
objective with Lipschitz constants `L` (`σ_max = arSigmaMax P (L p)`), paid per INNER call (with
the extra `κ_uns` for the last iteration of a call). -/
noncomputable def arqpUnitKappaUnc (P : ARqpCParams) (L : ℕ → ℝ) (p : ℕ) : ℝ :=
  arqpSCKappaUns P + Real.log (Optimization.arSigmaMax P.toARParams (L p) / P.σ₀) /
    Real.log P.γ₂

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
    hθς hmem (fun y hy hyk => ⟨hy, (norm_le_of_phi2_le hyk).trans hck⟩) ?_
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

/-- `max(1, max_{j ∈ [1 : q]} B_j) > 0`. -/
theorem finMax_one_pos {B : ℕ → ℝ} : 0 < Optimization.finMax 1 B q :=
  one_pos.trans_le Optimization.le_finMax_left

end TPqp

end ARqpSCAnchored


section ARqpSCRuns

/-! ### One INNER call of Phase 2 realized by ARqp-SC -/

section Call

variable {F : ℝⁿ → ℝ} {X : Set ℝⁿ} {p q : ℕ} {P : ARqpCParams} {ε : ℕ → ℝ}
  {xi : ℕ → ℝⁿ} {e : ℕ} {succ : ℕ → Prop} {δo : ℕ → ℝ}

/-- The jet bound `max(1, max_{i ∈ [2 : p]} ‖∇^i F(y)‖)` at `y` (computable from the derivatives
that Step 1 of ARqp evaluates at `y`). -/
noncomputable def jetBound (F : ℝⁿ → ℝ) (p : ℕ) (y : ℝⁿ) : ℝ :=
  Optimization.finMax 1 (fun i => if i < p then ‖iteratedFDeriv ℝ (i + 1) F y‖ else 0) p

/-- One INNER call of Phase 2 of TPqp-GC realized by ARqp-SC, with its output radii: the iterates
`x_{k,0}, …, x_{k,e}` are the first `e + 1` iterates of an ARqpC-SC run (`algorithm_14_1_1` with
`c = 0`, `h = 0`, initial radii `1`; an ARqp-SC run whose Step 2 is Algorithm 14.1.2) on `F`
whose first termination index `k_ε` is at least `e` (the call may be cut before INNER terminates,
by any test of (14.3.32)), the successful iterations are those of the run, and the returned radii
`δo` are those of the run at the last iterate:
* the current radii `δ_e` (Step 1 of Algorithm 14.1.1; at a Step-1 termination these are the
  returned radii);
* or, whenever Step 2 is computed at `e` (`¬ Stop₁ e`; at any cut, not only at a Step-2
  termination), the step radii `δ_{s_e}` (the radii the book returns at a Step-2 termination,
  Algorithm 14.1.1, Step 2);
* or, at a Step-2 termination (`e = k_ε`, `¬ Stop₁ e`), the radii
  `min(1, ε_j/(4(3 J + σ_e)))`, `J = jetBound F p x_e`, which certify (14.3.19) at `x_e` because
  `0` minimizes the model there (`Optimization.isEpsDeltaApprox_of_isMinOn_zero_of_jet`; the step
  radii `δ_{s_e}` need not). -/
def IsARqpSCCallOut (F : ℝⁿ → ℝ) (X : Set ℝⁿ) (p q : ℕ) (P : ARqpCParams) (ε : ℕ → ℝ)
    (xi : ℕ → ℝⁿ) (e : ℕ) (succ : ℕ → Prop) (δo : ℕ → ℝ) : Prop :=
  ∃ (x s : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → ℝⁿ) (kε : ℕ),
    algorithm_14_1_1 F (zeroCon n) zeroOuter X p q P ε (fun _ => 1) x s σ δ δs d dm ∧
    Optimization.IsFirstHit (arqpcStop F (zeroCon n) zeroOuter p q P ε x s σ δ d) kε ∧
    e ≤ kε ∧ (∀ i ≤ e, xi i = x i) ∧
    (∀ i < e, (succ i ↔ P.η₁ ≤ Optimization.arqpRatio (fun y => F y + zeroOuter (zeroCon n y))
      (fun k => arqpcData F (zeroCon n) zeroOuter p (x k) (σ k)) x s i)) ∧
    ((∀ j ∈ Finset.Icc 1 q, δo j = δ e j) ∨
      (¬ algorithm_14_1_1.Stop₁ F (zeroCon n) zeroOuter p q P ε x σ δ d e ∧
        ∀ j ∈ Finset.Icc 1 q, δo j = δs e j) ∨
      (e = kε ∧ ¬ algorithm_14_1_1.Stop₁ F (zeroCon n) zeroOuter p q P ε x σ δ d e ∧
        ∀ j ∈ Finset.Icc 1 q, δo j = min 1 (ε j / (4 * (3 * jetBound F p (x e) + σ e)))))

/-- **The step before the end of a call is not followed by a Step-1 termination** unless the call
ends at a point passing INNER's test (14.3.19) with the returned radii: if `i < e` and either
`i + 1 < e` or the test fails at `x_{k,e}` with the radii `δo`, then the run has not stopped up to
`i` and the Step-1 test fails at `i + 1` (the hypotheses of Lemma 14.2.2). -/
theorem IsARqpSCCallOut.not_stop₁ (h : IsARqpSCCallOut F X p q P ε xi e succ δo) :
    ∃ (x s : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → ℝⁿ) (kε : ℕ),
      algorithm_14_1_1 F (zeroCon n) zeroOuter X p q P ε (fun _ => 1) x s σ δ δs d dm ∧
      Optimization.IsFirstHit (arqpcStop F (zeroCon n) zeroOuter p q P ε x s σ δ d) kε ∧
      e ≤ kε ∧ (∀ i ≤ e, xi i = x i) ∧
      (∀ i < e, (succ i ↔ P.η₁ ≤ Optimization.arqpRatio (fun y => F y + zeroOuter (zeroCon n y))
        (fun k => arqpcData F (zeroCon n) zeroOuter p (x k) (σ k)) x s i)) ∧
      ((∀ j ∈ Finset.Icc 1 q, δo j = δ e j) ∨
        (¬ algorithm_14_1_1.Stop₁ F (zeroCon n) zeroOuter p q P ε x σ δ d e ∧
          ∀ j ∈ Finset.Icc 1 q, δo j = δs e j) ∨
        (e = kε ∧ ¬ algorithm_14_1_1.Stop₁ F (zeroCon n) zeroOuter p q P ε x σ δ d e ∧
          ∀ j ∈ Finset.Icc 1 q, δo j = min 1 (ε j / (4 * (3 * jetBound F p (x e) + σ e))))) ∧
      ∀ i < e, (i + 1 < e ∨ ¬ Optimization.IsEpsDeltaApprox (ftaylorSeries ℝ F (xi e))
          {d | xi e + d ∈ X} q ε δo) →
        ¬ algorithm_14_1_1.Stop₁ F (zeroCon n) zeroOuter p q P ε x σ δ d (i + 1) := by
  obtain ⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, he, hxi, hsucc, hδo⟩ := h
  refine ⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, he, hxi, hsucc, hδo, fun i hi hcont h1 => ?_⟩
  by_cases hlt : i + 1 < e
  · exact hhit.2 (i + 1) (lt_of_lt_of_le hlt he) (Or.inl h1)
  · have htest := hcont.resolve_left hlt
    have hie : i + 1 = e := by omega
    rw [hie] at h1
    rcases hδo with hδo | ⟨hn, -⟩ | ⟨-, hn, -⟩
    · refine htest fun j hj => ?_
      have h12 := hr.zero_algorithm_12_2_2_feasible
      have hk12 : ∀ l < e, ¬ Optimization.arqpStop F P.toARqpParams p q ε x s σ δ d l :=
        fun l hl => zero_arqpcStop_iff.not.1 (hhit.2 l (by omega))
      have h1' : Optimization.arqpStop₁ P.toARqpParams q ε (Optimization.arqpData F p x σ) δ d e :=
          by
        simpa only [algorithm_14_1_1.Stop₁, zero_arqpcData_eq] using h1
      have happ := Optimization.MeasureTestPasses.isEpsDeltaApprox P.ς_pos (h12.witness e hk12) h1'
      rw [hxi e le_rfl, hδo j hj]
      exact happ j hj
    · exact hn h1
    · exact hn h1

/-- **The objective does not increase along an ARqp-SC call** (ARqpC-SC with `c = 0`, `h = 0`,
`algorithm_14_1_1.zero_antitone`): `F (x_{k,i+1}) ≤ F (x_{k,i})` for `i < e`. -/
theorem IsARqpSCCallOut.antitone (h : IsARqpSCCallOut F X p q P ε xi e succ δo) :
    ∀ i < e, F (xi (i + 1)) ≤ F (xi i) := by
  obtain ⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, he, hxi, -, -⟩ := h
  intro i hi
  rw [hxi i (by omega), hxi (i + 1) (by omega)]
  exact hr.zero_antitone hhit i (i + 1) (by omega) (by omega)

/-- The anchored bounds of `F` on a set `S` containing its sublevel set at the start of the call
give the anchored bounds on the sublevel set of the run's objective at its starting point. -/
private theorem anchored_of_call {X₀ S : Set ℝⁿ} {L : ℕ → ℝ} {x : ℕ → ℝⁿ}
    (hF : AnchoredCompositeBounds F (zeroCon n) X₀ S p L (fun _ => 0)) (hx : xi 0 = x 0)
    (hS : ∀ y ∈ X, F y ≤ F (xi 0) → y ∈ S) :
    AnchoredCompositeBounds F (zeroCon n) X₀
      (compositeSublevel F (zeroCon n) zeroOuter X (x 0)) p L (fun _ => 0) :=
  hF.mono (compositeSublevel_zero_subset (hx ▸ hS))

/-- `jetBound F p y ≤ max(1, max_{i ∈ [1 : p]} L_i)` at a point of the anchor set of anchored
bounds with constants `L` (which bound `‖∇^i F‖` by `L_{i-1}` for `i ∈ [2 : p]`). -/
theorem jetBound_le {X₀ A : Set ℝⁿ} {L : ℕ → ℝ}
    (hF : AnchoredCompositeBounds F (zeroCon n) X₀ A p L (fun _ => 0)) {y : ℝⁿ} (hy : y ∈ A) :
    jetBound F p y ≤ Optimization.finMax 1 L p := by
  refine Optimization.finMax_le Optimization.le_finMax_left fun i hi => ?_
  split_ifs with hip
  · have h2 : i + 1 ∈ Finset.Icc 2 p :=
      Finset.mem_Icc.2 ⟨by have := (Finset.mem_Icc.1 hi).1; omega, by omega⟩
    have := hF.norm_f (i + 1) h2 y hy
    rw [Nat.add_sub_cancel] at this
    exact this.trans (Optimization.le_finMax hi)
  · exact zero_le_one.trans Optimization.le_finMax_left

/-- The radii `min(1, ε_j/(4(3 J + σ_e)))` (`J = jetBound F p x_e`) of a Step-2 termination are at
least `κ_ρ ε_j` (`arqpSCKappaRad`), under anchored bounds on the sublevel set at `x_0`. -/
private theorem jet_radius_ge {X₀ : Set ℝⁿ} {L : ℕ → ℝ} {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ}
    {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → ℝⁿ} {e : ℕ}
    (hr : algorithm_14_1_1 F (zeroCon n) zeroOuter X p q P ε (fun _ => 1) x s σ δ δs d dm)
    (hA : AnchoredCompositeBounds F (zeroCon n) X₀
      (compositeSublevel F (zeroCon n) zeroOuter X (x 0)) p L (fun _ => 0)) (hXX₀ : X ⊆ X₀)
    (hnot : ∀ i < e, ¬ arqpcStop F (zeroCon n) zeroOuter p q P ε x s σ δ d i) :
    ∀ j ∈ Finset.Icc 1 q, arqpSCKappaRad P L p * ε j ≤
      min 1 (ε j / (4 * (3 * jetBound F p (x e) + σ e))) := by
  intro j hj
  obtain ⟨hε0, hε1⟩ := hr.ε_mem j hj
  have hJ := jetBound_le hA (hr.mem_compositeSublevel hnot)
  have hJ1 : 1 ≤ jetBound F p (x e) := Optimization.le_finMax_left
  have hσ := sigma_le_arqpcSigmaMax_anchored hr hA hXX₀ assumptionHLip_zeroOuter hnot e le_rfl
  have hσ0 : 0 < σ e := hr.run.toIsARRun.sigma_pos hnot e le_rfl
  have hL1 : 1 ≤ Optimization.finMax 1 L p := Optimization.one_le_finMax
  have hrad1 : arqpSCKappaRad P L p ≤
      1 / (4 * (3 * Optimization.finMax 1 L p + arqpcSigmaMax P L (fun _ => 0) 0 p 0)) :=
    min_le_right _ _
  have hK : 0 < 4 * (3 * jetBound F p (x e) + σ e) := by linarith
  have hK' : 4 * (3 * jetBound F p (x e) + σ e) ≤
      4 * (3 * Optimization.finMax 1 L p + arqpcSigmaMax P L (fun _ => 0) 0 p 0) := by linarith
  have hKm : 0 < 4 * (3 * Optimization.finMax 1 L p + arqpcSigmaMax P L (fun _ => 0) 0 p 0) := by
    linarith
  refine le_min ?_ ?_
  · calc arqpSCKappaRad P L p * ε j
        ≤ 1 / (4 * (3 * Optimization.finMax 1 L p + arqpcSigmaMax P L (fun _ => 0) 0 p 0)) * 1 :=
          mul_le_mul hrad1 hε1 hε0.le (div_pos one_pos hKm).le
      _ ≤ 1 := by rw [mul_one, div_le_one hKm]; linarith
  · calc arqpSCKappaRad P L p * ε j
        ≤ 1 / (4 * (3 * Optimization.finMax 1 L p + arqpcSigmaMax P L (fun _ => 0) 0 p 0)) *
            ε j := mul_le_mul_of_nonneg_right hrad1 hε0.le
      _ ≤ ε j / (4 * (3 * jetBound F p (x e) + σ e)) := by
          rw [one_div_mul_eq_div]
          exact div_le_div_of_nonneg_left hε0.le hK hK'

open Classical in
/-- **The INNER contract of one ARqp-SC call of Phase 2** ([cartis2022evaluation], Lemmas 14.2.2
and 14.2.3 for ARqp-SC, and the radius policy of Algorithm 14.1.2), for every call
`IsARqpSCCallOut` on an objective `F` with anchored bounds (constants `L`, open convex `X₀ ⊇ X`)
on a set containing the sublevel set of `F` at the start of the call, and `θ < ς`:
(stay) unsuccessful iterations do not move;
(count) `e ≤ κ_uns |𝒮| + κ_unc` (14.2.13), `𝒮` the successful iterations of the call;
(decrease) every successful iteration `i < e` that is not the last one, or that is the last one
of a call ending at a point failing INNER's test (14.3.19) with the returned radii, decreases `F`
by at least `κ_decr ε_l^{l+1}` for some `l` (ARqpC-SC row of (14.2.12)), and by at least
`η₁ κ_{Δm} ε_l^{π_l}` with the exponents of the ARqp-SC row in a radii mode `u` (the lower-bound
mode `u = False` for every `q` and `X`, the unit-radii mode when `u` forces `q = 1` and `X`
convex);
(radii) the returned radii are at least `κ_ρ ε_j` (the radius policy (14.1.28) holds at every
iteration of every run, `algorithm_14_1_1.kappaDeltaMin_mul_le_radius_anchored`). -/
theorem IsARqpSCCallOut.contract {X₀ S : Set ℝⁿ} {L : ℕ → ℝ}
    (hF : AnchoredCompositeBounds F (zeroCon n) X₀ S p L (fun _ => 0)) (hXX₀ : X ⊆ X₀)
    (hθς : P.θ < P.ς) (h : IsARqpSCCallOut F X p q P ε xi e succ δo)
    (hS : ∀ y ∈ X, F y ≤ F (xi 0) → y ∈ S) :
    (∀ i < e, ¬ succ i → xi (i + 1) = xi i) ∧
    (e : ℝ) ≤ arqpSCKappaUns P * ((Finset.range e).filter succ).card + arqpSCKappaUnc P L p ∧
    (∀ i < e, succ i → (i + 1 < e ∨ ¬ Optimization.IsEpsDeltaApprox (ftaylorSeries ℝ F (xi e))
        {d | xi e + d ∈ X} q ε δo) →
      ∃ l ∈ Finset.Icc 1 q, arqpSCKappaDecr P L p q * ε l ^ (l + 1) ≤ F (xi i) - F (xi (i + 1))) ∧
    (∀ (u : Prop) [Decidable u], (u → q = 1 ∧ Convex ℝ X) → ∀ i < e, succ i →
      (i + 1 < e ∨ ¬ Optimization.IsEpsDeltaApprox (ftaylorSeries ℝ F (xi e))
        {d | xi e + d ∈ X} q ε δo) →
      ∃ l ∈ Finset.Icc 1 q, arqpRowKappaDecr u P L p q * ε l ^ Optimization.arqpPiOf u p l ≤
        F (xi i) - F (xi (i + 1))) ∧
    (∀ j ∈ Finset.Icc 1 q, arqpSCKappaRad P L p * ε j ≤ δo j) := by
  obtain ⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, he, hxi, hsucc, hδo, hns⟩ := h.not_stop₁
  have hA := anchored_of_call hF (hxi 0 (Nat.zero_le _)) hS
  have hnot : ∀ i < e, ¬ arqpcStop F (zeroCon n) zeroOuter p q P ε x s σ δ d i :=
    fun i hi => hhit.2 i (by omega)
  have hq := hr.one_le_q
  have hε := hr.ε_mem
  refine ⟨fun i hi hs => ?_, ?_, fun i hi hs hcont => ?_, fun u _ hu i hi hs hcont => ?_,
    fun j hj => ?_⟩
  · -- unsuccessful iterations do not move
    rw [hxi i hi.le, hxi (i + 1) hi]
    exact hr.run.toIsARRun.eq_of_not_succ (fun l hl => hnot l (by omega))
      (not_le.1 ((hsucc i hi).not.1 hs))
  · -- Lemma 14.2.3
    have h3 := lemma_14_2_3_arqpc_anchored hr hA hXX₀ assumptionHLip_zeroOuter (k := e) hnot
    set ρ := fun i => P.η₁ ≤ Optimization.arqpRatio
      (fun y => F y + zeroOuter (zeroCon n y))
      (fun k => arqpcData F (zeroCon n) zeroOuter p (x k) (σ k)) x s i
    have hS' : (Finset.range e).filter succ = (Finset.range e).filter ρ :=
      Finset.filter_congr fun i hi => hsucc i (Finset.mem_range.1 hi)
    have hcard' := Optimization.card_successSet_le_card_filter_add_one ρ e
    have hκ := arqpSCKappaUns_nonneg P
    rw [hS']
    unfold arqpSCKappaUnc
    unfold arqpSCKappaUns at hκ ⊢
    nlinarith
  · -- Lemma 14.2.2, ARqpC-SC row
    have hs' := (hsucc i hi).1 hs
    obtain ⟨l, hl, hdec⟩ := lemma_14_2_2_arqpc_anchored hr hθς hA hXX₀
      assumptionHLip_zeroOuter assumptionHS0_zeroOuter (k := i)
      (fun l hl => hnot l (by omega)) hs' (hns i hi hcont)
    refine ⟨l, hl, ?_⟩
    simp only [zeroOuter, Pi.zero_apply, add_zero] at hdec
    rw [hxi i hi.le, hxi (i + 1) hi]
    unfold arqpSCKappaDecr
    rw [mul_assoc]
    exact hdec
  · -- Lemma 14.2.2, ARqp-SC row in radii mode `u`
    have hs' := (hsucc i hi).1 hs
    have hdec := hr.zero_decrease_arqp_anchored hA hXX₀ hθς hu (k := i)
      (fun l hl => hnot l (by omega)) hs' (hns i hi hcont)
    obtain ⟨l, hl, hmin⟩ := Optimization.exists_finMin_eq hq
      (u := fun j => ε j ^ Optimization.arqpPiOf u p j) (b := 1) fun j hj =>
        Real.rpow_le_one (hε j hj).1.le (hε j hj).2 (Optimization.arqpPiOf_nonneg u p j)
    refine ⟨l, hl, ?_⟩
    rw [hmin] at hdec
    rw [hxi i hi.le, hxi (i + 1) hi]
    unfold arqpRowKappaDecr
    rw [mul_assoc]
    exact hdec
  · -- the radius policy
    have hκ : arqpSCKappaRad P L p ≤ kappaDeltaMin P L (fun _ => 0) 0 p 0 := min_le_left _ _
    have hκε := mul_le_mul_of_nonneg_right hκ (hε j hj).1.le
    rcases hδo with hδo | ⟨hn, hδo⟩ | ⟨-, -, hδo⟩
    · rw [hδo j hj]
      exact hκε.trans (hr.zero_radius_ge_anchored hA hXX₀ e hnot j hj)
    · rw [hδo j hj]
      exact hκε.trans (hr.kappaDeltaMin_mul_le_radius_anchored hA hXX₀ assumptionHLip_zeroOuter
        assumptionHS0_zeroOuter hnot hn j hj)
    · rw [hδo j hj]
      exact jet_radius_ge hr hA hXX₀ hnot j hj

end Call

/-! ### Phase 2 with ARqp-SC calls: the INNER contract for every run -/

section Phase2

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {p q : ℕ} {P : ARqpCParams} {θ β : ℝ}
  {ε : ℕ → ℝ} {x₁ : ℝⁿ} {D : TPqpSeq n}

/-- **The INNER calls of Phase 2 of TPqp-GC are ARqp-SC runs** ([cartis2022evaluation],
Algorithm 14.3.2, Step 1: `INNER(μ(·, t_k), X, q, x_k, β ‖r(x_k, t_k)‖ ε)` with INNER = ARqp-SC):
for every outer iteration `k ≥ 1` reached, the iterates, successful iterations and output radii
`δ_{k+1}` of the `k`-th call are those of an ARqp-SC run on `μ(·, t_k)` with tolerances
`β ‖r(x_k, t_k)‖ ε_j` (`IsARqpSCCallOut`), cut at any iteration (by any test of (14.3.32)). -/
def IsARqpSCPhase2Calls (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (X : Set ℝⁿ) (p q : ℕ) (P : ARqpCParams)
    (θ β : ℝ) (ε : ℕ → ℝ) (D : TPqpSeq n) : Prop :=
  ∀ k, 1 ≤ k → D.Before f c X q θ ε k →
    IsARqpSCCallOut (Constrained.targetMerit f c (D.t k)) X p q P
      (fun j => β * Constrained.targetResidual f c (D.t k) (D.x k) * ε j) (D.xi k) (D.e k)
      (D.succ k) (D.δ (k + 1))

/-- The sublevel set of `μ(·, t_k)` at the start `x_k` of the `k`-th call lies in
`𝓛_μ(t_k) = {x ∈ X | ‖r(x, t_k)‖ ≤ 1}`, since `‖r(x_k, t_k)‖ ≤ ε₀ ≤ 1`. -/
theorem IsTPqpGCPhase2.call_sublevel (h : IsTPqpGCPhase2 f c X q θ β ε x₁ D) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : D.Before f c X q θ ε k) :
    ∀ y ∈ X, Constrained.targetMerit f c (D.t k) y ≤
        Constrained.targetMerit f c (D.t k) (D.xi k 0) → y ∈ muSublevel f c X (D.t k) := by
  intro y hy hyk
  rw [h.inner_zero k hk1 hk] at hyk
  exact ⟨hy, (Constrained.targetMerit_le_targetMerit_iff.1 hyk).trans
    (((h.isTargetSequence hk).residual_le h.θ_lt_one.le h.ε₀_pos.le hk1 le_rfl).trans
      (h.ε_le_one 0 (by simp)))⟩

/-- `ρ_j = κ_ρ βθ ε₀ ε_j ≤ κ_ρ β ‖r(x_k, t_k)‖ ε_j` at a case-(b) iteration. -/
private theorem rad_le_of_isKb (h : IsTPqpGCPhase2 f c X q θ β ε x₁ D) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : D.Before f c X q θ ε k) (hb : D.IsKb f c θ ε k) {κ : ℝ} (hκ : 0 ≤ κ) {j : ℕ}
    (hj : j ∈ Finset.Icc 1 q) :
    κ * β * θ * ε 0 * ε j ≤
      κ * (β * Constrained.targetResidual f c (D.t k) (D.x k) * ε j) := by
  have hrk : θ * ε 0 ≤ Constrained.targetResidual f c (D.t k) (D.x k) :=
    hb.1.trans (h.residual_succ_le hk1 hk)
  have := h.β_pos
  have := h.ε_pos' hj
  calc κ * β * θ * ε 0 * ε j = κ * (β * (θ * ε 0) * ε j) := by ring
    _ ≤ _ := by gcongr

/-- **Every Phase-2 run of TPqp-GC whose INNER calls are ARqp-SC runs satisfies the INNER contract
keyed on INNER's own test** (`IsInnerPhaseRunStrong`; [cartis2022evaluation], Lemmas 14.2.2–14.2.3,
ARqpC-SC row of (14.2.12), `π_l = l + 1`), with the `t`-independent constants
`κ_decr = arqpSCKappaDecr P L p q`, `κ_uns = arqpSCKappaUns P`, `κ_unc = arqpSCKappaUnc P L p` and
radii `ρ_j = κ_ρ βθ ε₀ ε_j` (`κ_ρ = arqpSCKappaRad P L p`), when every `μ(·, t)` has anchored
bounds with constants `L` on `𝓛_μ(t)` (for an open convex `X₀ ⊇ X`; Lemma 14.3.6 (ii) gives them
under c.D1pLB.X and f.D1pLB.X, `exists_anchoredCompositeBounds_nu_mu`) and `θ < ς`. This holds for
every run, with calls cut by any test of (14.3.32). -/
theorem IsARqpSCPhase2Calls.isInnerPhaseRunStrong (h : IsTPqpGCPhase2 f c X q θ β ε x₁ D)
    (hcalls : IsARqpSCPhase2Calls f c X p q P θ β ε D) {X₀ : Set ℝⁿ} {L : ℕ → ℝ}
    (hμ : ∀ t, AnchoredCompositeBounds (Constrained.targetMerit f c t) (zeroCon n) X₀
      (muSublevel f c X t) p L (fun _ => 0)) (hXX₀ : X ⊆ X₀) (hθς : P.θ < P.ς) :
    IsInnerPhaseRunStrong f c X q θ β ε D (arqpSCKappaDecr P L p q) (arqpSCKappaUns P)
      (arqpSCKappaUnc P L p) (fun l => (l : ℝ) + 1)
      (fun j => arqpSCKappaRad P L p * β * θ * ε 0 * ε j) := by
  have hC := fun k (hk1 : 1 ≤ k) (hk : D.Before f c X q θ ε k) =>
    (hcalls k hk1 hk).contract (hμ (D.t k)) hXX₀ hθς (h.call_sublevel hk1 hk)
  refine ⟨⟨fun k hk1 hk => (hC k hk1 hk).2.1, fun k hk1 hk => (hC k hk1 hk).1,
    fun k hk1 hk i hi hs hcont _ => ?_⟩, fun k hk1 hk hb _ j hj => ?_⟩
  · have hcont' : i + 1 < D.e k ∨ ¬ Optimization.IsEpsDeltaApprox
        (ftaylorSeries ℝ (Constrained.targetMerit f c (D.t k)) (D.xi k (D.e k)))
        {d | D.xi k (D.e k) + d ∈ X} q
        (fun j => β * Constrained.targetResidual f c (D.t k) (D.x k) * ε j) (D.δ (k + 1)) := by
      rw [h.inner_end k hk1 hk]
      exact hcont
    obtain ⟨l, hl, hdec⟩ := (hC k hk1 hk).2.2.1 i hi hs hcont'
    refine ⟨l, hl, ?_⟩
    have e : ((l : ℝ) + 1) = ((l + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [e, Real.rpow_natCast]
    exact hdec
  · exact (rad_le_of_isKb h hk1 hk hb (arqpSCKappaRad_pos P L p).le hj).trans
      ((hC k hk1 hk).2.2.2.2 j hj)

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
    IsInnerPhaseRunStrong f c X q θ β ε D (arqpRowKappaDecr u P L p q) (arqpSCKappaUns P)
      (arqpSCKappaUnc P L p) (Optimization.arqpPiOf u p)
      (fun j => arqpSCKappaRad P L p * β * θ * ε 0 * ε j) := by
  have hC := fun k (hk1 : 1 ≤ k) (hk : D.Before f c X q θ ε k) =>
    (hcalls k hk1 hk).contract (hμ (D.t k)) hXX₀ hθς (h.call_sublevel hk1 hk)
  refine ⟨⟨fun k hk1 hk => (hC k hk1 hk).2.1, fun k hk1 hk => (hC k hk1 hk).1,
    fun k hk1 hk i hi hs hcont _ => ?_⟩, fun k hk1 hk hb _ j hj => ?_⟩
  · have hcont' : i + 1 < D.e k ∨ ¬ Optimization.IsEpsDeltaApprox
        (ftaylorSeries ℝ (Constrained.targetMerit f c (D.t k)) (D.xi k (D.e k)))
        {d | D.xi k (D.e k) + d ∈ X} q
        (fun j => β * Constrained.targetResidual f c (D.t k) (D.x k) * ε j) (D.δ (k + 1)) := by
      rw [h.inner_end k hk1 hk]
      exact hcont
    exact (hC k hk1 hk).2.2.2.1 u hu i hi hs hcont'
  · exact (rad_le_of_isKb h hk1 hk hb (arqpSCKappaRad_pos P L p).le hj).trans
      ((hC k hk1 hk).2.2.2.2 j hj)

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

/-- The bad-iteration term of the ARqpC-SC exponents: `(ε₀ ε_j)^{-j} ≤ ε₀^{1-π_j} ε_j^{-π_j}`
for `π_j = j + 1` and `ε₀, ε_j ∈ (0, 1]`. -/
theorem inv_pow_le_term_succ {ε₀ εj : ℝ} (h0 : 0 < ε₀) (hj0 : 0 < εj) (hj1 : εj ≤ 1) (j : ℕ) :
    ((ε₀ * εj) ^ j)⁻¹ ≤ ε₀ ^ (1 - ((j : ℝ) + 1)) * εj ^ (-((j : ℝ) + 1)) := by
  have e1 : ε₀ ^ (1 - ((j : ℝ) + 1)) = (ε₀ ^ j)⁻¹ := by
    rw [show 1 - ((j : ℝ) + 1) = -(j : ℝ) by ring, Real.rpow_neg h0.le, Real.rpow_natCast]
  have e2 : εj ^ (-((j : ℝ) + 1)) = (εj ^ j)⁻¹ * εj⁻¹ := by
    rw [Real.rpow_neg hj0.le, show ((j : ℝ) + 1) = ((j + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, pow_succ, mul_inv]
  rw [e1, e2, mul_pow, mul_inv]
  have : 1 ≤ εj⁻¹ := (one_le_inv₀ hj0).2 hj1
  have : 0 ≤ (ε₀ ^ j)⁻¹ * (εj ^ j)⁻¹ := by positivity
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

/-- `κ_unc ≥ 0`. -/
theorem arqpSCKappaUnc_nonneg (P : ARqpCParams) (L : ℕ → ℝ) (p : ℕ) :
    0 ≤ arqpSCKappaUnc P L p := by
  unfold arqpSCKappaUnc
  have := arqpSCKappaUns_nonneg P
  have := P.log_γ₂_pos
  have : 0 ≤ Real.log (arqpcSigmaMax P L (fun _ => 0) 0 p 0 / P.σ₀) :=
    Real.log_nonneg ((one_le_div P.σ₀_pos).2 (Optimization.σ₀_le_arSigmaMax _ _))
  positivity

/-- The Phase-1 bound of Lemma 14.3.7 is within the order of Theorem 14.3.9:
`½ κ ‖c(x₀)‖ ∑_j β₁^{1-2π_j}/(β₁^{1-π_j} - 1) θ^{1-π_j} ε₀^{1-π_j} ε_j^{-π_j} ≤
½ κ ‖c(x₀)‖ W O` with `W = ∑_j |β₁^{1-2π_j}/(β₁^{1-π_j} - 1) θ^{1-π_j}|`, for `κ ≥ 0` and every
`O ≥ ε₀^{1-π_j} ε_j^{-π_j}`. -/
theorem phase1Bound_le {κ r β₁ θ O : ℝ} {π : ℕ → ℝ} (hκ : 0 ≤ κ) (hr : 0 ≤ r)
    (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j)
    (hO : ∀ j ∈ Finset.Icc 1 q, ε 0 ^ (1 - π j) * ε j ^ (-π j) ≤ O) :
    1 / 2 * κ * r * ∑ j ∈ Finset.Icc 1 q, β₁ ^ (1 - 2 * π j) / (β₁ ^ (1 - π j) - 1) *
        θ ^ (1 - π j) * ε 0 ^ (1 - π j) * ε j ^ (-π j) ≤
      1 / 2 * κ * r * (∑ j ∈ Finset.Icc 1 q,
        |β₁ ^ (1 - 2 * π j) / (β₁ ^ (1 - π j) - 1) * θ ^ (1 - π j)|) * O := by
  rw [mul_assoc (1 / 2 * κ * r), Finset.sum_mul]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_) (by positivity)
  have h0 : 0 ≤ ε 0 ^ (1 - π j) * ε j ^ (-π j) := by
    have := hε 0 (by simp)
    have := hε j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
    positivity
  rw [mul_assoc _ (ε 0 ^ (1 - π j))]
  calc _ ≤ |β₁ ^ (1 - 2 * π j) / (β₁ ^ (1 - π j) - 1) * θ ^ (1 - π j)| *
        (ε 0 ^ (1 - π j) * ε j ^ (-π j)) := mul_le_mul_of_nonneg_right (le_abs_self _) h0
    _ ≤ _ := mul_le_mul_of_nonneg_left (hO j hj) (abs_nonneg _)

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
(`inv_pow_le_term_succ`),
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
  have hκ : 0 < arqpSCKappaDecr P L p q := arqpSCKappaDecr_pos_of hLp hθς
  have hκρ : 0 < arqpSCKappaRad P L p * β * θ := by
    have := arqpSCKappaRad_pos P L p
    positivity
  obtain ⟨CF, CD, hCF, hCD, hord⟩ :=
    Constrained.IsHighOrderTargetRun.exists_const_order_of_innerTest (f := f) (c := c)
    (X := X) (θ := θ) (β := β) hq (πmax := (q : ℝ) + 1) hκ (arqpSCKappaUns_nonneg P)
    (arqpSCKappaUnc_nonneg P L p) hκρ (finMax_one_pos (B := Bf)) (abs_nonneg (fup - flow + 1))
    zero_le_one hθ0 hθ1 hβ0
  -- the Phase-1 constants
  have hνκ : 0 < arqpSCKappaDecr P Lν p q := arqpSCKappaDecr_pos_of (hνA x₀).one_le hθς
  have hκF : 0 ≤ arqpSCKappaF P Lν p q := by
    unfold arqpSCKappaF
    have := arqpSCKappaUns_nonneg P
    have := arqpSCKappaC_nonneg P Lν p
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
  have hF1' := hF1.trans (phase1Bound_le hκF (norm_nonneg _) (fun j hj => (hε j hj).1) hOT)
  have hD1' := hD1.trans (phase1Bound_le hκD (norm_nonneg _) (fun j hj => (hε j hj).1) hOT)
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
    (ρ' := fun j => arqpSCKappaRad P L p * β * θ * (ε 0 * ε j)) fun j _ => le_of_eq (by ring)
  obtain ⟨kε, hend, hF2, hD2⟩ := hord h2 hin (fun j hj => mul_pos hε₀.1 (hεI j hj).1)
    (fun l hl => by
      have : (l : ℝ) ≤ q := by exact_mod_cast (Finset.mem_Icc.1 hl).2
      exact ⟨by positivity, by linarith⟩) (hB.of_le hεβ) (le_abs_self _)
    (fun _ hy => hf.contDiffAt_of_le hqp hy) (fun _ hy => hc.contDiffAt_of_le hqp hy)
    (fun _ hy _ => hf.norm_iteratedFDeriv_le_finMax hqp (hf.subset hy)) inv_le_tpqpOrderF hOT
    (fun j hj => by
      rw [one_mul, mul_pow_sub_one (by have := (Finset.mem_Icc.1 hj).1; omega) _]
      exact (inv_pow_le_term_succ hε₀.1 (hεI j hj).1 (hεI j hj).2 j).trans (hOT j hj))
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
  have hνκ : 0 < arqpSCKappaDecr P Lν p q := arqpSCKappaDecr_pos_of (hνA x₀).one_le hθς
  have hεI : ∀ l ∈ Finset.Icc 1 q, 0 < ε l ∧ ε l ≤ 1 := fun l hl =>
    hε l (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hl).2))
  have hκ : 0 < arqpSCKappaDecr P L p q := arqpSCKappaDecr_pos_of (hμA 0).one_le hθς
  have hκF : 0 ≤ arqpSCKappaF P Lν p q := by
    unfold arqpSCKappaF
    have := arqpSCKappaUns_nonneg P
    have := arqpSCKappaC_nonneg P Lν p
    positivity
  have hκD : 0 ≤ arqpSCKappaD P Lν p q := by
    unfold arqpSCKappaD
    positivity
  have hπ1 : ∀ l ∈ Finset.Icc 1 q, 1 < (fun j : ℕ => (j : ℝ) + 1) l := fun l hl => by
    have : (1 : ℝ) ≤ l := by exact_mod_cast (Finset.mem_Icc.1 hl).1
    simp only
    linarith
  have hcost := phase1_cost_le_anchored h hq (hνA x₀) hc.subset hθς hε hR.phase1
  set ρ : ℕ → ℝ := fun j => arqpSCKappaRad P L p * β * θ * ε 0 * ε j
  have hρ : ∀ j ∈ Finset.Icc 1 q, 0 ≤ ρ j := fun j hj => by
    have := arqpSCKappaRad_pos P L p
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
    have := arqpSCKappaRad_pos P L p
    have := h2.β_pos
    have := (hεI j hj).1
    have hη : 0 < Constrained.kbMargin θ (ε 0) := by
      rw [Constrained.kbMargin_def]
      have := h2.θ_lt_one
      have : 0 < 1 - θ := by linarith
      positivity
    positivity
  set Bq := Optimization.finMax 1 Bf q
  have hBq : 0 < Bq := finMax_one_pos
  have hτ0 : 0 < Optimization.finMin 1 g q / (2 * Bq) :=
    div_pos (Optimization.finMin_pos one_pos hg) (by positivity)
  obtain ⟨-, kε, hend, -⟩ := (theorem_14_3_9 h hθ0 hπ1 hκF hκD (aF := 0) (aD := 0)
    (nF₁ := fun k => (nF₁ k : ℝ)) (nD₁ := fun k => (nD₁ k : ℝ))
    (fun k hk => by rw [add_zero]; exact (hcost k hk).1)
    (fun k hk => by rw [add_zero]; exact (hcost k hk).2)
    ((hR.phase2 hc1).isInnerPhaseRunStrong h2 hμA hc.subset hθς) hκ
    (arqpSCKappaUns_nonneg P)
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

/-- The ARqp-SC exponents of the lower-bound radii mode: `1 < j(p+1)/p ≤ q(p+1)/p` for
`j ∈ [1 : q]`. -/
theorem arqpPiOf_false_mem {p q j : ℕ} (hp : 1 ≤ p) (hj : j ∈ Finset.Icc 1 q) :
    1 < Optimization.arqpPiOf False p j ∧
      Optimization.arqpPiOf False p j ≤ Optimization.arqpPiOf False p q := by
  rw [Optimization.arqpPiOf_of_neg not_false, Optimization.arqpPiOf_of_neg not_false]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.1 hj).1
  have hjq : (j : ℝ) ≤ q := by exact_mod_cast (Finset.mem_Icc.1 hj).2
  refine ⟨by rw [lt_div_iff₀ hp0]; nlinarith, by gcongr⟩

/-- The ARqp-SC exponent of order `p` is `p(p+1)/p = p + 1`. -/
theorem arqpPiOf_false_self {p : ℕ} (hp : 1 ≤ p) :
    Optimization.arqpPiOf False p p = (p : ℝ) + 1 := by
  rw [Optimization.arqpPiOf_of_neg not_false]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 (by omega))

/-- **The bad-iteration term against the ARqp-SC order** (exponents `π_j = j(p+1)/p`): for
`ε₀, ε_j ∈ (0, 1]`, `(ε₀ ε_j)^{-j} ≤ ε₀^{-p} + ε₀^{1-π_j} ε_j^{-π_j}` (weighted AM–GM:
`(ε₀ ε_j)^{-j}` is the geometric mean of `ε₀^{-p}` and `ε₀^{1-π_j} ε_j^{-π_j}` with weights
`1/(p+1)`, `p/(p+1)`). With `q = p`, `ε₀^{-p} ≤ ε₀^{1-π_p} ε_p^{-π_p}` (`π_p = p + 1`), so the
term is within the printed order. -/
theorem inv_pow_le_arqp {ε₀ εj : ℝ} (h0 : 0 < ε₀) (hj0 : 0 < εj) {p j : ℕ} (hp : 1 ≤ p) :
    ((ε₀ * εj) ^ j)⁻¹ ≤ (ε₀ ^ p)⁻¹ +
      ε₀ ^ (1 - Optimization.arqpPiOf False p j) * εj ^ (-Optimization.arqpPiOf False p j) := by
  rw [Optimization.arqpPiOf_of_neg not_false]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  set π : ℝ := (j : ℝ) * (p + 1) / p with hπ
  set w₁ : ℝ := 1 / (p + 1) with hw₁
  set w₂ : ℝ := p / (p + 1) with hw₂
  have hw : w₁ + w₂ = 1 := by rw [hw₁, hw₂]; field_simp; ring
  have hA : 0 ≤ (ε₀ ^ p)⁻¹ := by positivity
  have hB : 0 ≤ ε₀ ^ (1 - π) * εj ^ (-π) := by positivity
  have hgm := Real.geom_mean_le_arith_mean2_weighted (w₁ := w₁) (w₂ := w₂) (by positivity)
    (by positivity) hA hB hw
  have e1 : ((ε₀ ^ p)⁻¹) ^ w₁ = ε₀ ^ (-(p : ℝ) * w₁) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg h0.le, ← Real.rpow_mul h0.le]
  have e2 : (ε₀ ^ (1 - π) * εj ^ (-π)) ^ w₂ = ε₀ ^ ((1 - π) * w₂) * εj ^ (-π * w₂) := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul h0.le,
      ← Real.rpow_mul hj0.le]
  have e3 : ((ε₀ * εj) ^ j)⁻¹ = ε₀ ^ (-(p : ℝ) * w₁ + (1 - π) * w₂) * εj ^ (-π * w₂) := by
    have x1 : -(p : ℝ) * w₁ + (1 - π) * w₂ = -(j : ℝ) := by
      rw [hw₁, hw₂, hπ]; field_simp; ring
    have x2 : -π * w₂ = -(j : ℝ) := by rw [hw₂, hπ]; field_simp
    rw [x1, x2, Real.rpow_neg h0.le, Real.rpow_neg hj0.le, Real.rpow_natCast, Real.rpow_natCast,
      mul_pow, mul_inv]
  rw [e3, Real.rpow_add h0, mul_assoc, ← e2, ← e1]
  have h1 : w₁ ≤ 1 := by rw [hw₁, div_le_one (by positivity)]; linarith
  have h2 : w₂ ≤ 1 := by rw [hw₂, div_le_one (by positivity)]; linarith
  calc _ ≤ w₁ * (ε₀ ^ p)⁻¹ + w₂ * (ε₀ ^ (1 - π) * εj ^ (-π)) := hgm
    _ ≤ _ := add_le_add (mul_le_of_le_one_left hA h1) (mul_le_of_le_one_left hB h2)

/-- The iteration bound of Theorem 14.3.3 is `O(ε₀^{-1})`:
`⌈log(a/r)/log β₁⌉₊ ≤ 1 + r/(a |log β₁|)` for `a > 0`, `r ≥ 0`, `β₁ ∈ (0, 1)`. -/
theorem ceil_log_div_le {a r β₁ : ℝ} (ha : 0 < a) (hr : 0 ≤ r) (hβ₁0 : 0 < β₁) (hβ₁1 : β₁ < 1) :
    (⌈Real.log (a / r) / Real.log β₁⌉₊ : ℝ) ≤ 1 + r / (a * |Real.log β₁|) := by
  have hl : Real.log β₁ < 0 := Real.log_neg hβ₁0 hβ₁1
  have habs : |Real.log β₁| = -Real.log β₁ := abs_of_neg hl
  have hkey : -Real.log (a / r) ≤ r / a := by
    rcases hr.eq_or_lt with rfl | hr0
    · simp
    · rw [← Real.log_inv, inv_div]
      have := Real.log_le_sub_one_of_pos (div_pos hr0 ha)
      linarith
  have hx : Real.log (a / r) / Real.log β₁ ≤ r / (a * |Real.log β₁|) :=
    calc Real.log (a / r) / Real.log β₁ = -Real.log (a / r) / -Real.log β₁ :=
          (neg_div_neg_eq _ _).symm
      _ ≤ r / a / -Real.log β₁ := div_le_div_of_nonneg_right hkey (by linarith)
      _ = r / (a * |Real.log β₁|) := by rw [habs, div_div]
  have hnn : 0 ≤ r / (a * |Real.log β₁|) := by positivity
  by_cases hx0 : 0 ≤ Real.log (a / r) / Real.log β₁
  · have := Nat.ceil_lt_add_one hx0
    linarith
  · rw [Nat.ceil_eq_zero.2 (not_le.1 hx0).le]
    push_cast
    linarith

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {p q : ℕ}

/-- **The Phase-1 cost of TPqp-GC with INNER = ARqp-SC within an order bound** (the Phase-1 part
of `exists_const_order_arqp`, [cartis2022evaluation], Lemma 14.3.7): under c.D1pLB.X and f.D1pLB.X
there are constants `κ_F, κ_D ≥ 0` such that for all tolerances and every run of
`IsTPqpGCARqpSCRun`, and every `O` with `ε₀^{-1} ≤ O` and `ε₀^{1-π_l} ε_l^{-π_l} ≤ O`
(`π_l = l(p+1)/p`), Phase 1 uses at most `κ_F O` evaluations of `c` and `κ_D O` derivative
evaluations (additive cost contract, `lemma_14_3_7_add`, with `k₁ = O(ε₀^{-1})`,
`ceil_log_div_le`). -/
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
  set κF₁ := arqpSCKappaUns P / arqpRowKappaDecr False P Lν p q with hκF₁
  set κD₁ := 1 / arqpRowKappaDecr False P Lν p q with hκD₁
  have hκF : 0 ≤ κF₁ := div_nonneg (arqpSCKappaUns_nonneg P) hνκ.le
  have hκD : 0 ≤ κD₁ := div_nonneg zero_le_one hνκ.le
  have hκC := arqpSCKappaC_nonneg P Lν p
  set W := ∑ j ∈ Finset.Icc 1 q, |β₁ ^ (1 - 2 * Optimization.arqpPiOf False p j) /
    (β₁ ^ (1 - Optimization.arqpPiOf False p j) - 1) * θ ^ (1 - Optimization.arqpPiOf False p j)|
        with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set c₁ := 1 + ‖c x₀‖ / (θ * |Real.log β₁|) with hc₁
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; positivity
  refine ⟨1 / 2 * κF₁ * ‖c x₀‖ * W + arqpSCKappaC P Lν p * c₁,
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
      (Nat.cast_le.2 hkmax).trans (ceil_log_div_le (mul_pos hθ0 hε₀.1) (norm_nonneg _) hβ₁0 hβ₁1)
    have h2 : ‖c x₀‖ / (θ * ε 0 * |Real.log β₁|) = ‖c x₀‖ / (θ * |Real.log β₁|) * (ε 0)⁻¹ := by
      field_simp
    have h3 : 0 ≤ ‖c x₀‖ / (θ * |Real.log β₁|) := by positivity
    calc (k₁ : ℝ) ≤ 1 + ‖c x₀‖ / (θ * |Real.log β₁|) * (ε 0)⁻¹ := h2 ▸ h1
      _ ≤ O + ‖c x₀‖ / (θ * |Real.log β₁|) * O := by gcongr
      _ = c₁ * O := by rw [hc₁]; ring
  have hcost : ∀ k ∈ Finset.Icc 1 k₁,
      (nF₁ k : ℝ) ≤ innerEvalBound κF₁ (Optimization.arqpPiOf False p) q (phi2 c (xP (k - 1)))
        (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j) + arqpSCKappaC P Lν p ∧
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
      (fun y hy hyk => ⟨hy, (norm_le_of_phi2_le hyk).trans hck⟩)
  have hπ1 : ∀ l ∈ Finset.Icc 1 q, 1 < Optimization.arqpPiOf False p l := fun l hl =>
    (arqpPiOf_false_mem hp hl).1
  have hF1 := (lemma_14_3_7_add h hθ0 hπ1 hκF fun k hk => (hcost k hk).1).trans
    (add_le_add (phase1Bound_le hκF (norm_nonneg _) (fun j hj => (hε j hj).1) hOT) le_rfl)
  have hD1 := (lemma_14_3_7_add h hθ0 hπ1 hκD fun k hk => (hcost k hk).2).trans
    (add_le_add (phase1Bound_le hκD (norm_nonneg _) (fun j hj => (hε j hj).1) hOT) le_rfl)
  rw [← hW] at hF1 hD1
  have hF1' : ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤
      (1 / 2 * κF₁ * ‖c x₀‖ * W + arqpSCKappaC P Lν p * c₁) * O := by
    calc _ ≤ 1 / 2 * κF₁ * ‖c x₀‖ * W * O + k₁ * arqpSCKappaC P Lν p := hF1
      _ ≤ 1 / 2 * κF₁ * ‖c x₀‖ * W * O + c₁ * O * arqpSCKappaC P Lν p := by gcongr
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
`O(ε₀^{-1})` (`ceil_log_div_le`). -/
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
  have hκρ : 0 < arqpSCKappaRad P L p * β * θ := by
    have := arqpSCKappaRad_pos P L p
    positivity
  obtain ⟨CF, CD, hCF, hCD, hord⟩ :=
    Constrained.IsHighOrderTargetRun.exists_const_order_of_innerTest (f := f) (c := c)
    (X := X) (θ := θ) (β := β) hq (πmax := Optimization.arqpPiOf False p q) hκ
    (arqpSCKappaUns_nonneg P) (arqpSCKappaUnc_nonneg P L p) hκρ (finMax_one_pos (B := Bf))
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
    (ρ' := fun j => arqpSCKappaRad P L p * β * θ * (ε 0 * ε j)) fun j _ => le_of_eq (by ring)
  have hεI : ∀ l ∈ Finset.Icc 1 q, 0 < ε l ∧ ε l ≤ 1 := fun l hl =>
    hε l (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hl).2))
  obtain ⟨kε, hend, hF2, hD2⟩ := hord h2 hin (fun j hj => mul_pos hε₀.1 (hεI j hj).1)
    (fun l hl =>
      ⟨Optimization.arqpPiOf_nonneg False p l, (arqpPiOf_false_mem hp hl).2⟩) (hB.of_le hεβ)
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
(`inv_pow_le_arqp`) and `ε₀^{-p} ≤ ε₀^{1-π_p} ε_p^{-π_p}`; for `q < p` see
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
  have hπq : π q = (q : ℝ) + 1 := arqpPiOf_false_self hq
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
      have := inv_pow_le_arqp hε₀.1 hεj.1 (j := j) hq
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

open Classical in
/-- **One INNER call of Phase 2 with its output radii exists** from every `(x, t)` with `x ∈ X`
and `θε₀ ≤ ‖r(x, t)‖ ≤ ε₀`: ARqp-SC on `μ(·, t)` with tolerances `β ‖r(x, t)‖ ε` (an ARqpC-SC run
with `c = 0`, `h = 0`, which terminates by Theorem 14.2.4), stopped at its termination or as soon
as `‖r(·, t)‖ < θε₀`, returning the current radii, or the radii `min(1, ε_j/(4(3 J + σ)))` at a
Step-2 termination; its output satisfies (14.3.32) (the first or the third test). -/
theorem exists_callData {t : ℝ} {L : ℕ → ℝ} {X₀ : Set ℝⁿ}
    (hμ : AnchoredCompositeBounds (Constrained.targetMerit f c t) (zeroCon n) X₀
      (muSublevel f c X t) p L (fun _ => 0)) (hXX₀ : X ⊆ X₀) (P : ARqpCParams)
    (hθς : P.θ < P.ς) (hq : 1 ≤ q) (hqp : q ≤ p) (hX : IsClosed X) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hβ0 : 0 < β) (hβθ : β ≤ θ)
    (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) {x : ℝⁿ} (hx : x ∈ X)
    (hlo : θ * ε 0 ≤ Constrained.targetResidual f c t x)
    (hhi : Constrained.targetResidual f c t x ≤ ε 0) :
    ∃ o : CallOut n, o.xi 0 = x ∧ o.xi o.e ∈ X ∧
      (∀ j ∈ Finset.Icc 1 q, 0 < o.δ j ∧ o.δ j ≤ 1) ∧
      (Constrained.targetResidual f c t (o.xi o.e) < θ * ε 0 ∨
        meritCrit f c X q ε t (o.xi o.e) o.δ) ∧
      (∀ i < o.e, Constrained.targetMerit f c t (o.xi (i + 1)) ≤
        Constrained.targetMerit f c t (o.xi i)) ∧
      (∀ i < o.e, θ * ε 0 ≤ Constrained.targetResidual f c t (o.xi i)) ∧
      Constrained.targetResidual f c t (o.xi o.e) ≤ Constrained.targetResidual f c t x ∧
      IsARqpSCCallOut (Constrained.targetMerit f c t) X p q P
        (fun j => β * Constrained.targetResidual f c t x * ε j) o.xi o.e o.succ o.δ := by
  set F := Constrained.targetMerit f c t with hFdef
  set ρ := Constrained.targetResidual f c t x with hρ
  have hεI : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1 := fun j hj =>
    hε j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
  have hε₀ := hε 0 (by simp)
  have hρ0 : 0 < ρ := lt_of_lt_of_le (mul_pos hθ0 hε₀.1) hlo
  have hε' : ∀ j ∈ Finset.Icc 1 q, 0 < β * ρ * ε j ∧ β * ρ * ε j ≤ 1 := by
    intro j hj
    obtain ⟨h1, h2⟩ := hεI j hj
    refine ⟨by positivity, ?_⟩
    have : β * ρ ≤ 1 := by nlinarith
    nlinarith
  have hS : ∀ y ∈ X, F y ≤ F x → y ∈ muSublevel f c X t := fun y hy hyx =>
    ⟨hy, (Constrained.targetMerit_le_targetMerit_iff.1 hyx).trans (hhi.trans hε₀.2)⟩
  obtain ⟨xr, s, σ, δ, δs, d, dm, hx0, hr⟩ := exists_isARqpCRun_of_hLip
    (f := F) (c := zeroCon n) assumptionHLip_zeroOuter assumptionHS0_zeroOuter P hq hqp hε'
    (fun _ _ => ⟨one_pos, le_rfl⟩) hX hx
  have hA : AnchoredCompositeBounds F (zeroCon n) X₀
      (compositeSublevel F (zeroCon n) zeroOuter X (xr 0)) p L (fun _ => 0) :=
    hμ.mono (compositeSublevel_zero_subset (hx0 ▸ hS))
  have hmε : ∀ j ∈ Finset.Icc 1 q, (β * ρ * ε j) ^ (j + 1) ≤ 1 := fun j hj =>
    pow_le_one₀ (hε' j hj).1.le (hε' j hj).2
  obtain ⟨j₀, hj₀, hmin⟩ := Optimization.exists_finMin_eq hq hmε
  obtain ⟨kε, hhit, -, -, -, -⟩ := theorem_14_2_4_arqpc_anchored hr hθς hA hXX₀
    assumptionHLip_zeroOuter assumptionHS0_zeroOuter (wlow := 0)
    (fun y _ => by simpa using (Constrained.targetMerit_nonneg : 0 ≤ F y))
    (mε := Optimization.finMin 1 (fun j => (β * ρ * ε j) ^ (j + 1)) q)
    (by rw [hmin]; exact pow_pos (hε' j₀ hj₀).1 _) (fun j hj => Optimization.finMin_le hj)
  have hmono := hr.zero_antitone hhit
  have hmem : ∀ i ≤ kε, xr i ∈ X := fun i hi => hr.mem fun l hl => hhit.2 l (hl.trans_le hi)
  have hex : ∃ i, i = kε ∨ Constrained.targetResidual f c t (xr i) < θ * ε 0 :=
    ⟨kε, Or.inl rfl⟩
  set e := Nat.find hex with he
  have he_le : e ≤ kε := Nat.find_min' hex (Or.inl rfl)
  have hres : ∀ i ≤ kε, Constrained.targetResidual f c t (xr i) ≤ ρ := fun i hi => by
    have := hmono 0 i (Nat.zero_le _) hi
    rw [hx0] at this
    exact Constrained.targetMerit_le_targetMerit_iff.1 this
  have hnot : ∀ i < e, ¬ arqpcStop F (zeroCon n) zeroOuter p q P (fun j => β * ρ * ε j) xr s σ δ d
      i := fun i hi => hhit.2 i (by omega)
  have h12 := hr.zero_algorithm_12_2_2_feasible
  have hk12 : ∀ l < e, ¬ Optimization.arqpStop F P.toARqpParams p q (fun j => β * ρ * ε j) xr s σ δ
      d
      l := fun l hl => zero_arqpcStop_iff.not.1 (hnot l hl)
  -- the certificate gives the third test of (14.3.32) at a point with residual at least `θε₀`
  have hcrit : ∀ δo : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, 0 < δo j) →
      Optimization.IsEpsDeltaApprox (ftaylorSeries ℝ F (xr e)) {d | xr e + d ∈ X} q
        (fun j => β * ρ * ε j) δo →
      θ * ε 0 ≤ Constrained.targetResidual f c t (xr e) → meritCrit f c X q ε t (xr e) δo := by
    intro δo hδo happ hge j hj
    refine (happ j hj).trans ?_
    have hδ := hδo j hj
    have hεj := (hεI j hj).1
    have : β * ρ ≤ Constrained.targetResidual f c t (xr e) := by nlinarith
    have : β * ρ * ε j ≤ ε j * Constrained.targetResidual f c t (xr e) := by nlinarith
    change β * ρ * ε j * δo j ^ j / (j ! : ℝ) ≤
      ε j * Constrained.targetResidual f c t (xr e) * δo j ^ j / (j ! : ℝ)
    gcongr
  have hsucc : ∀ i < e, ((fun i => P.η₁ ≤ Optimization.arqpRatio
      (fun y => F y + zeroOuter (zeroCon n y))
      (fun k => arqpcData F (zeroCon n) zeroOuter p (xr k) (σ k)) xr s i) i ↔
        P.η₁ ≤ Optimization.arqpRatio (fun y => F y + zeroOuter (zeroCon n y))
          (fun k => arqpcData F (zeroCon n) zeroOuter p (xr k) (σ k)) xr s i) :=
    fun _ _ => Iff.rfl
  have hlow : ∀ i < e, θ * ε 0 ≤ Constrained.targetResidual f c t (xr i) := fun i hi => by
    have := Nat.find_min hex hi
    push Not at this
    exact this.2
  have hmono' : ∀ i < e, F (xr (i + 1)) ≤ F (xr i) := fun i hi =>
    hmono i (i + 1) (by omega) (by omega)
  by_cases hcase : e < kε ∨
      algorithm_14_1_1.Stop₁ F (zeroCon n) zeroOuter p q P (fun j => β * ρ * ε j) xr σ δ d e
  · -- the current radii
    refine ⟨⟨xr, e, fun i => P.η₁ ≤ Optimization.arqpRatio
      (fun y => F y + zeroOuter (zeroCon n y))
      (fun k => arqpcData F (zeroCon n) zeroOuter p (xr k) (σ k)) xr s i, δ e⟩, hx0,
      hmem e he_le, fun j hj => h12.delta_mem (fun _ _ => ⟨one_pos, le_rfl⟩) e hk12 j hj, ?_,
      hmono', hlow, hres e he_le,
      ⟨xr, s, σ, δ, δs, d, dm, kε, hr, hhit, he_le, fun _ _ => rfl, hsucc,
        Or.inl fun _ _ => rfl⟩⟩
    by_cases hlt : Constrained.targetResidual f c t (xr e) < θ * ε 0
    · exact Or.inl hlt
    · refine Or.inr (hcrit (δ e) (fun j hj =>
        (h12.delta_mem (fun _ _ => ⟨one_pos, le_rfl⟩) e hk12 j hj).1) ?_ (not_lt.1 hlt))
      rcases hcase with hlt' | h1
      · rcases Nat.find_spec hex with hek | hlt''
        · exact absurd hek (by omega)
        · exact absurd hlt'' hlt
      · have h1' : Optimization.arqpStop₁ P.toARqpParams q (fun j => β * ρ * ε j)
            (Optimization.arqpData F p xr σ) δ d e := by
          simpa only [algorithm_14_1_1.Stop₁, zero_arqpcData_eq] using h1
        exact Optimization.MeasureTestPasses.isEpsDeltaApprox P.ς_pos (h12.witness e hk12) h1'
  · -- a Step-2 termination: the radii certified by the minimality of the model at `0`
    push Not at hcase
    obtain ⟨hke, h1⟩ := hcase
    have hek : e = kε := le_antisymm he_le hke
    have hstop : Optimization.arqpStop F P.toARqpParams p q (fun j => β * ρ * ε j) xr s σ δ d e :=
      zero_arqpcStop_iff.1 (hek ▸ hhit.1)
    have h1' : ¬ Optimization.arqpStop₁ P.toARqpParams q (fun j => β * ρ * ε j)
        (Optimization.arqpData F p xr σ) δ d e := by
      simpa only [algorithm_14_1_1.Stop₁, zero_arqpcData_eq] using h1
    have hstep := h12.step hk12 h1'
    have h2 : Optimization.arqpStop₂ (Optimization.arqpData F p xr σ) s e := hstop.resolve_left h1'
    have hxA := hr.mem_compositeSublevel hnot
    have hσ0 : 0 < σ e := h12.toIsARRun.sigma_pos hk12 e le_rfl
    obtain ⟨hδ, hcert⟩ := Optimization.isEpsDeltaApprox_of_isMinOn_zero_of_jet (h12.mem e hk12)
      (hA.contDiffAt_f (hA.subset hxA))
      (L := fun i => if i < p then ‖iteratedFDeriv ℝ (i + 1) F (xr e)‖ else 0)
      (fun i hi => by
        have hi' : i - 1 ∈ Finset.Icc 1 p := Finset.mem_Icc.2
          ⟨by have := (Finset.mem_Icc.1 hi).1; omega, by have := (Finset.mem_Icc.1 hi).2; omega⟩
        refine le_trans (le_of_eq ?_) (Optimization.le_finMax hi')
        have hi2 := (Finset.mem_Icc.1 hi).1
        have hip := (Finset.mem_Icc.1 hi).2
        have hlt : i - 1 < p := by omega
        simp only [hlt, ite_true]
        rw [Nat.sub_add_cancel (by omega : 1 ≤ i)])
      hqp (fun j hj => ⟨(hε' j hj).1, (hε' j hj).2⟩) hσ0 (hstep.isMinOn_of_eq h2)
    refine ⟨⟨xr, e, fun i => P.η₁ ≤ Optimization.arqpRatio
      (fun y => F y + zeroOuter (zeroCon n y))
      (fun k => arqpcData F (zeroCon n) zeroOuter p (xr k) (σ k)) xr s i,
      fun j => min 1 (β * ρ * ε j / (4 * (3 * jetBound F p (xr e) + σ e)))⟩, hx0,
      hmem e he_le, fun j hj => hδ j hj, ?_, hmono', hlow, hres e he_le,
      ⟨xr, s, σ, δ, δs, d, dm, kε, hr, hhit, he_le, fun _ _ => rfl, hsucc,
        Or.inr (Or.inr ⟨hek, h1, fun _ _ => rfl⟩)⟩⟩
    by_cases hlt : Constrained.targetResidual f c t (xr e) < θ * ε 0
    · exact Or.inl hlt
    · exact Or.inr (hcrit _ (fun j hj => (hδ j hj).1) hcert (not_lt.1 hlt))

/-- TPqp-GC runs with INNER = ARqp-SC in both phases from anchored bounds for `ν` on
`𝓛_ν(x₀)` and for every `μ(·, t)` on `𝓛_μ(t)` (with constants that may depend on `t`): Phase 1 by
LENq-SC with ARqp-SC calls (`exists_algorithm_14_3_2_of_phase2_anchored`), Phase 2 with the calls
of `exists_callData`. -/
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
        (fun x t hx hlo hhi _ => exists_callData (hμA t) hXX₀ P hθς hq hqp hX hθ0 hθ1 hβ0
          hβθ hε hx hlo hhi)
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
ARqp-SC entry as "`q = 1`, `X` convex"), with its output radii: an `IsARqpUnitCall` (a prefix
of an ARqp run of Chapter 12 whose Step 2, Algorithm 12.2.3, keeps the radii `1` at the orders
`j ≤ 2`) returning the radii `1`, those of the run. -/
def IsARqpUnitCallOut (F : ℝⁿ → ℝ) (p q : ℕ) (P : ARqpCParams) (ε : ℕ → ℝ) (xi : ℕ → ℝⁿ)
    (e : ℕ) (succ : ℕ → Prop) (δo : ℕ → ℝ) : Prop :=
  IsARqpUnitCall F p q P ε xi e succ ∧ ∀ j ∈ Finset.Icc 1 q, δo j = 1

open Classical in
/-- **The INNER contract of one ARqp call with unit radii** ([cartis2022evaluation],
Lemmas 12.2.13 and 14.2.3 with unit radii), for every call `IsARqpUnitCallOut` on an objective `F`
with anchored bounds (constants `L`, `X₀ = ℝⁿ`) on a set containing the sublevel set of `F` at
the start of the call, `θ < ς` and `1 ≤ q ≤ p`: unsuccessful iterations do not move,
`e ≤ κ_uns |𝒮| + κ_unc` (`κ_unc = arqpUnitKappaUnc P L p`), and, for tolerances in `(0, 1]`,
every successful iteration that is not the last one, or the last one of a call ending at a point
failing INNER's test with radii `1`, decreases `F` by at least `η₁ κ_{Δm} ε_l^{π_l}` with the
unit-radius exponents `π_l = (p+1)/(p-l+1)`. -/
theorem IsARqpUnitCallOut.contract {S : Set ℝⁿ} {L : ℕ → ℝ}
    (hF : AnchoredCompositeBounds F (zeroCon n) univ S p L (fun _ => 0)) (hθς : P.θ < P.ς)
    (hq : 1 ≤ q) (hqp : q ≤ p) (h : IsARqpUnitCallOut F p q P ε xi e succ δo)
    (hS : ∀ y, F y ≤ F (xi 0) → y ∈ S) :
    (∀ i < e, ¬ succ i → xi (i + 1) = xi i) ∧
    (e : ℝ) ≤ arqpSCKappaUns P * ((Finset.range e).filter succ).card + arqpUnitKappaUnc P L p ∧
    ((∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) → ∀ i < e, succ i →
      (i + 1 < e ∨ ¬ Optimization.IsEpsDeltaApprox (ftaylorSeries ℝ F (xi e))
        {d | xi e + d ∈ (univ : Set ℝⁿ)} q ε δo) →
      ∃ l ∈ Finset.Icc 1 q, arqpRowKappaDecr True P L p q * ε l ^ Optimization.arqpPiOf True p l ≤
        F (xi i) - F (xi (i + 1))) := by
  obtain ⟨⟨x, s, σ, δr, δs, d, dm, kε, hr, hδs, hhit, he, hxi, hsucc⟩, hδo⟩ := h
  have hAμ : ∀ y ∈ (univ : Set ℝⁿ), F y ≤ F (x 0) → y ∈ S := fun y _ hy =>
    hS y (by rwa [hxi 0 (Nat.zero_le _)])
  have hone := hr.delta_eq_one (fun _ _ => rfl) hδs
  have hnot : ∀ i < e, ¬ Optimization.arqpStop F P.toARqpParams p q ε x s σ δr d i :=
    fun i hi => hhit.2 i (lt_of_lt_of_le hi he)
  refine ⟨fun i hi hs => ?_, ?_, fun hε i hi hs hcont => ?_⟩
  · rw [hxi i hi.le, hxi (i + 1) hi]
    exact hr.toIsARRun.eq_of_not_succ (fun l hl => hnot l (lt_of_le_of_lt hl hi))
      (not_le.1 ((hsucc i hi).not.1 hs))
  · -- Lemma 14.2.3
    have h3 := hr.toIsARRun.le_succ_count (k := e) hnot
      (Optimization.IsARqpRun.sigma_le_of_anchored hF.lipschitzDerivsAnchored_f
        (subset_univ _) hAμ hr e hnot).2
    set ρ := fun i => P.η₁ ≤ Optimization.arqpRho F p x s σ i
    have hS' : (Finset.range e).filter succ = (Finset.range e).filter ρ :=
      Finset.filter_congr fun i hi => hsucc i (Finset.mem_range.1 hi)
    have hcard' := Optimization.card_successSet_le_card_filter_add_one ρ e
    have hκ := arqpSCKappaUns_nonneg P
    rw [hS']
    unfold arqpUnitKappaUnc
    unfold arqpSCKappaUns at hκ ⊢
    nlinarith
  · -- Lemma 12.2.13 with unit radii
    have h1 : ¬ Optimization.arqpStop₁ P.toARqpParams q ε (Optimization.arqpData F p x σ) δr d
        (i + 1) := by
      intro h1
      by_cases hlt : i + 1 < e
      · exact hnot (i + 1) hlt (Or.inl h1)
      · have hie : i + 1 = e := by omega
        rw [hie] at h1
        refine (hcont.resolve_left hlt) fun j hj => ?_
        have happ := Optimization.MeasureTestPasses.isEpsDeltaApprox P.ς_pos (hr.witness e hnot) h1
        rw [hxi e le_rfl, hδo j hj, ← hone e hnot j hj]
        exact happ j hj
    have hdec := (Optimization.IsARqpRun.decrease hF.lipschitzDerivsAnchored_f
      hF.one_le (subset_univ _) hAμ hq hqp hθς hε hr
      (k := i) (fun l hl => hnot l (by omega)) ((hsucc i hi).1 hs) h1 (u := True)
      ⟨fun _ => hone (i + 1) (fun l hl => hnot l (by omega)), fun h' => absurd trivial h'⟩).2
    obtain ⟨l, hl, hmin⟩ := Optimization.exists_finMin_eq hq
      (u := fun j => ε j ^ Optimization.arqpPiOf True p j) (b := 1) fun j hj =>
        Real.rpow_le_one (hε j hj).1.le (hε j hj).2 (Optimization.arqpPiOf_nonneg True p j)
    refine ⟨l, hl, ?_⟩
    rw [hmin] at hdec
    rw [hxi i hi.le, hxi (i + 1) hi]
    unfold arqpRowKappaDecr
    rw [mul_assoc]
    exact hdec

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {θ β : ℝ} {x₁ : ℝⁿ} {D : TPqpSeq n}

/-- **The INNER calls of Phase 2 of TPqp-GC on `X = ℝⁿ` are ARqp runs with unit radii**: for every
outer iteration `k ≥ 1` reached, the `k`-th call is an `IsARqpUnitCallOut` on `μ(·, t_k)` with
tolerances `β ‖r(x_k, t_k)‖ ε_j`, cut at any iteration. -/
def IsARqpUnitPhase2Calls (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (p q : ℕ) (P : ARqpCParams) (θ β : ℝ)
    (ε : ℕ → ℝ) (D : TPqpSeq n) : Prop :=
  ∀ k, 1 ≤ k → D.Before f c univ q θ ε k →
    IsARqpUnitCallOut (Constrained.targetMerit f c (D.t k)) p q P
      (fun j => β * Constrained.targetResidual f c (D.t k) (D.x k) * ε j) (D.xi k) (D.e k)
      (D.succ k) (D.δ (k + 1))

/-- **Every Phase-2 run of TPqp-GC on `ℝⁿ` whose INNER calls are ARqp runs with unit radii
satisfies the INNER contract keyed on INNER's own test** (`IsInnerPhaseRunStrong`,
[cartis2022evaluation], Lemmas 12.2.13 and 14.2.3 with unit radii), with the unit-radius exponents
`π_l = (p+1)/(p-l+1)`, the `t`-independent constants `κ_decr = arqpRowKappaDecr True P L p q`,
`κ_uns = arqpSCKappaUns P`, `κ_unc = arqpUnitKappaUnc P L p` and radii `ρ_j = 1`, when every
`μ(·, t)` has anchored bounds with constants `L` on `𝓛_μ(t)` (`X₀ = ℝⁿ`), `θ < ς` and
`1 ≤ q ≤ p`. -/
theorem IsARqpUnitPhase2Calls.isInnerPhaseRunStrong (h : IsTPqpGCPhase2 f c univ q θ β ε x₁ D)
    (hcalls : IsARqpUnitPhase2Calls f c p q P θ β ε D) {L : ℕ → ℝ}
    (hμ : ∀ t, AnchoredCompositeBounds (Constrained.targetMerit f c t) (zeroCon n) univ
      (muSublevel f c univ t) p L (fun _ => 0)) (hθς : P.θ < P.ς) (hq : 1 ≤ q) (hqp : q ≤ p) :
    IsInnerPhaseRunStrong f c univ q θ β ε D (arqpRowKappaDecr True P L p q) (arqpSCKappaUns P)
      (arqpUnitKappaUnc P L p) (Optimization.arqpPiOf True p) (fun _ => 1) := by
  have hC := fun k (hk1 : 1 ≤ k) (hk : D.Before f c univ q θ ε k) =>
    (hcalls k hk1 hk).contract (hμ (D.t k)) hθς hq hqp
      (fun y hy => h.call_sublevel hk1 hk y (mem_univ y) hy)
  refine ⟨⟨fun k hk1 hk => (hC k hk1 hk).2.1, fun k hk1 hk => (hC k hk1 hk).1,
    fun k hk1 hk i hi hs hcont _ => ?_⟩, fun k hk1 hk _ _ j hj => ((hcalls k hk1 hk).2 j hj).ge⟩
  have hcont' : i + 1 < D.e k ∨ ¬ Optimization.IsEpsDeltaApprox
      (ftaylorSeries ℝ (Constrained.targetMerit f c (D.t k)) (D.xi k (D.e k)))
      {d | D.xi k (D.e k) + d ∈ (univ : Set ℝⁿ)} q
      (fun j => β * Constrained.targetResidual f c (D.t k) (D.x k) * ε j) (D.δ (k + 1)) := by
    rw [h.inner_end k hk1 hk]
    exact hcont
  -- the tolerances of the call lie in `(0, 1]`
  have hrk : θ * ε 0 ≤ Constrained.targetResidual f c (D.t k) (D.x k) := by
    have := h.inner_residual_ge k hk1 hk 0 (by omega)
    rwa [h.inner_zero k hk1 hk] at this
  have hrk1 : Constrained.targetResidual f c (D.t k) (D.x k) ≤ 1 :=
    ((h.isTargetSequence hk).residual_le h.θ_lt_one.le h.ε₀_pos.le hk1 le_rfl).trans
      (h.ε_le_one 0 (by simp))
  have hε' : ∀ j ∈ Finset.Icc 1 q,
      β * Constrained.targetResidual f c (D.t k) (D.x k) * ε j ∈ Ioc 0 1 := fun j hj => by
    have hεj := h.ε_pos' hj
    have hεj1 := h.ε_le_one j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
    have hβ1 : β ≤ 1 := h.β_le_θ.trans h.θ_lt_one.le
    have hr0 : 0 < Constrained.targetResidual f c (D.t k) (D.x k) :=
      lt_of_lt_of_le (mul_pos h.θ_pos h.ε₀_pos) hrk
    refine ⟨by have := h.β_pos; positivity, ?_⟩
    calc β * Constrained.targetResidual f c (D.t k) (D.x k) * ε j ≤ 1 * 1 * 1 := by
          gcongr
      _ = 1 := by ring
  exact (hC k hk1 hk).2.2 hε' i hi hs hcont'

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

open Classical in
/-- **One INNER call of Phase 2 on `ℝⁿ` by ARqp with unit radii exists** (`1 ≤ q ≤ min(2, p)`)
from every `(x, t)` with `θε₀ ≤ ‖r(x, t)‖ ≤ ε₀`: the ARqp run of `unit_core_anchored` on `μ(·, t)`
with tolerances `β ‖r(x, t)‖ ε` (Step 2 by Algorithm 12.2.3, radii `1`), stopped at its termination
or as soon as `‖r(·, t)‖ < θε₀`, returning the radii `1`; its output satisfies (14.3.32). -/
theorem exists_unitCallOut {t : ℝ} {L : ℕ → ℝ}
    (hμ : AnchoredCompositeBounds (Constrained.targetMerit f c t) (zeroCon n) univ
      (muSublevel f c univ t) p L (fun _ => 0)) (P : ARqpCParams) (hθς : P.θ < P.ς)
    (hq : 1 ≤ q) (hq2 : q ≤ 2) (hqp : q ≤ p) (hθ0 : 0 < θ) (hβ0 : 0 < β) (hβθ : β ≤ θ)
    (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) {x : ℝⁿ}
    (hlo : θ * ε 0 ≤ Constrained.targetResidual f c t x)
    (hhi : Constrained.targetResidual f c t x ≤ ε 0) :
    ∃ o : CallOut n, o.xi 0 = x ∧ o.xi o.e ∈ (univ : Set ℝⁿ) ∧
      (∀ j ∈ Finset.Icc 1 q, 0 < o.δ j ∧ o.δ j ≤ 1) ∧
      (Constrained.targetResidual f c t (o.xi o.e) < θ * ε 0 ∨
        meritCrit f c univ q ε t (o.xi o.e) o.δ) ∧
      (∀ i < o.e, Constrained.targetMerit f c t (o.xi (i + 1)) ≤
        Constrained.targetMerit f c t (o.xi i)) ∧
      (∀ i < o.e, θ * ε 0 ≤ Constrained.targetResidual f c t (o.xi i)) ∧
      Constrained.targetResidual f c t (o.xi o.e) ≤ Constrained.targetResidual f c t x ∧
      IsARqpUnitCallOut (Constrained.targetMerit f c t) p q P
        (fun j => β * Constrained.targetResidual f c t x * ε j) o.xi o.e o.succ o.δ := by
  set ρ := Constrained.targetResidual f c t x with hρ
  have hεI : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1 := fun j hj =>
    hε j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
  have hε₀ := hε 0 (by simp)
  have hρ0 : 0 < ρ := lt_of_lt_of_le (mul_pos hθ0 hε₀.1) hlo
  have hε' : ∀ j ∈ Finset.Icc 1 q, 0 < β * ρ * ε j ∧ β * ρ * ε j ≤ 1 := by
    intro j hj
    obtain ⟨h1, h2⟩ := hεI j hj
    refine ⟨by positivity, ?_⟩
    have : β * ρ ≤ 1 := by nlinarith
    nlinarith
  have hS : ∀ y, Constrained.targetMerit f c t y ≤ Constrained.targetMerit f c t x →
      y ∈ muSublevel f c univ t := fun y hyx =>
    ⟨mem_univ y, (Constrained.targetMerit_le_targetMerit_iff.1 hyx).trans (hhi.trans hε₀.2)⟩
  obtain ⟨xr, s, σ, δr, δs, d, dm, kε, hr, hδs, hhit, hx0, hmono, hcert⟩ :=
    unit_core_anchored hμ (flow := 0) (fun _ => Constrained.targetMerit_nonneg) P hθς hq hq2 hqp x
      hS hε'
  have hex : ∃ i, i = kε ∨ Constrained.targetResidual f c t (xr i) < θ * ε 0 := ⟨kε, Or.inl rfl⟩
  set e := Nat.find hex with he
  have he_le : e ≤ kε := Nat.find_min' hex (Or.inl rfl)
  have hres : ∀ i ≤ kε, Constrained.targetResidual f c t (xr i) ≤ ρ := fun i hi => by
    have := hmono 0 i (Nat.zero_le _) hi
    rw [hx0] at this
    exact Constrained.targetMerit_le_targetMerit_iff.1 this
  refine ⟨⟨xr, e, fun i => P.η₁ ≤ Optimization.arqpRho (Constrained.targetMerit f c t) p xr s σ i,
    fun _ => 1⟩, hx0, mem_univ _, fun _ _ => ⟨one_pos, le_rfl⟩, ?_,
    fun i (hi : i < e) => hmono i (i + 1) (by omega) (by omega), fun i (hi : i < e) => ?_,
    hres e he_le, ⟨⟨xr, s, σ, δr, δs, d, dm, kε, hr, hδs, hhit, he_le, fun _ _ => rfl,
      fun _ _ => Iff.rfl⟩, fun _ _ => rfl⟩⟩
  · rcases Nat.find_spec hex with hek | hlt
    · by_cases hlt : Constrained.targetResidual f c t (xr e) < θ * ε 0
      · exact Or.inl hlt
      · refine Or.inr fun j hj => ?_
        have h1 := hcert j hj
        rw [← hek] at h1
        refine h1.trans ?_
        have hεj := (hεI j hj).1
        have : β * ρ ≤ Constrained.targetResidual f c t (xr e) := by nlinarith
        have : β * ρ * ε j ≤ ε j * Constrained.targetResidual f c t (xr e) := by nlinarith
        change β * ρ * ε j * 1 ^ j / (j ! : ℝ) ≤
          ε j * Constrained.targetResidual f c t (xr e) * 1 ^ j / (j ! : ℝ)
        gcongr
    · exact Or.inl hlt
  · have := Nat.find_min hex hi
    push Not at this
    exact this.2

/-- **TPqp-GC runs on `ℝⁿ` with INNER = ARqp with unit radii in both phases exist** for
`1 ≤ q ≤ min(2, p)` (so the class `IsTPqpGCARqpUnitRun` of `theorem_14_3_9_arqp_unit` and
`theorem_14_3_9_arqp_unit_corrected` is not empty there), under c.D1pLB.X and f.D1pLB.X on
`X = X₀ = ℝⁿ`, for all ARqpC constants with `θ < ς`, every `θ ∈ (0, 1)`, `β ∈ (0, θ]`,
`ε ∈ (0, 1]^{q+1}`, `β₁ ∈ (0, 1)` with `β₁ ‖c(x₀)‖ < 1`: Phase 1 by LENq-SC with unit-radius ARqp
calls (`exists_algorithm_14_3_1_unit`), Phase 2 with the calls of
`exists_unitCallOut` (`phase2_core_of`). -/
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
      (fun x t _ hlo hhi _ => exists_unitCallOut (hμA t) P hθς hq hq2 hqp hθ0 hβ0 hβθ hε hlo hhi)
    exact ⟨xP, δP, k₁, D, nF₁, nD₁, ⟨⟨hxP0, hrun, hhit, fun _ => hD⟩, hcalls,
      fun _ k hk1 hk => (hcallsD k hk1 hk).2⟩⟩
  · exact ⟨xP, δP, k₁, ⟨fun _ => x₀, fun _ => 0, fun _ _ => 0, fun _ _ => x₀, fun _ => 0,
      fun _ _ => False⟩, nF₁, nD₁, ⟨⟨hxP0, hrun, hhit, fun h => absurd h hc1⟩, hcalls,
      fun h => absurd h hc1⟩⟩

/-- The unit-radius exponents: `1 < (p+1)/(p-j+1) ≤ (p+1)/(p-q+1)` for `j ∈ [1 : q]`,
`q ≤ p`. -/
theorem arqpPiOf_true_mem_Icc {p q j : ℕ} (hqp : q ≤ p) (hj : j ∈ Finset.Icc 1 q) :
    1 < Optimization.arqpPiOf True p j ∧
      Optimization.arqpPiOf True p j ≤ Optimization.arqpPiOf True p q := by
  rw [Optimization.arqpPiOf_of_pos trivial, Optimization.arqpPiOf_of_pos trivial]
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  have h0 : (0 : ℝ) < ((p - j + 1 : ℕ) : ℝ) := by positivity
  have h0' : (0 : ℝ) < ((p - q + 1 : ℕ) : ℝ) := by positivity
  have h1 : ((p - j + 1 : ℕ) : ℝ) < ((p + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have h2 : ((p - q + 1 : ℕ) : ℝ) ≤ ((p - j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  exact ⟨(one_lt_div h0).2 h1, div_le_div_of_nonneg_left (by positivity) h0' h2⟩

/-- For `q = p ≤ 2` the unit-radius exponents `(p+1)/(p-j+1)` are the "otherwise" exponents
`j(p+1)/p` of (14.2.12). -/
theorem arqpPiOf_true_eq_false {q j : ℕ} (hq2 : q ≤ 2) (hj : j ∈ Finset.Icc 1 q) :
    Optimization.arqpPiOf True q j = Optimization.arqpPiOf False q j := by
  rw [Optimization.arqpPiOf_of_pos trivial, Optimization.arqpPiOf_of_neg not_false]
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  interval_cases q <;> interval_cases j <;> norm_num

/-- `κ_C = (|log γ₁| + log(σ_max/σ₀))/log γ₂ + 2 ≥ 0` (Theorem 12.2.14). -/
theorem kappaCARqp_nonneg (P : ARqpCParams) (L : ℕ → ℝ) (p : ℕ) :
    0 ≤ Optimization.kappaCARqp P.toARqpParams L p := by
  rw [Optimization.kappaCARqp_def]
  have := P.log_γ₂_pos
  have : 0 ≤ Real.log (Optimization.arSigmaMax P.toARParams (L p) / P.σ₀) :=
    Real.log_nonneg ((one_le_div P.σ₀_pos).2 (Optimization.σ₀_le_arSigmaMax _ _))
  positivity

/-- `κ_unc ≥ 0` (Lemma 14.2.3 for ARqp runs). -/
theorem arqpUnitKappaUnc_nonneg (P : ARqpCParams) (L : ℕ → ℝ) (p : ℕ) :
    0 ≤ arqpUnitKappaUnc P L p := by
  unfold arqpUnitKappaUnc
  have := arqpSCKappaUns_nonneg P
  have := P.log_γ₂_pos
  have : 0 ≤ Real.log (Optimization.arSigmaMax P.toARParams (L p) / P.σ₀) :=
    Real.log_nonneg ((one_le_div P.σ₀_pos).2 (Optimization.σ₀_le_arSigmaMax _ _))
  positivity

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
    (arqpSCKappaUns_nonneg P) (arqpUnitKappaUnc_nonneg P L p) one_pos (finMax_one_pos (B := Bf))
    (abs_nonneg (fup - flow + 1)) zero_le_one hθ0 hθ1 hβ0
  -- the Phase-1 constants
  have hLνp : 1 ≤ Lν p := (hνA x₀).one_le
  set κF₁ := Optimization.kappaAARqpOf True P.toARqpParams Lν p q with hκF₁
  set κD₁ := Optimization.kappaSARqpOf True P.toARqpParams Lν p q with hκD₁
  have hκD : 0 < κD₁ := Optimization.kappaSARqpOf_pos True P.σmin_pos hθς hLνp
  have hκF : 0 ≤ κF₁ := by
    rw [hκF₁]
    rw [Optimization.kappaAARqpOf_def]
    have := P.log_γ₂_pos
    have := hκD.le
    positivity
  have hκC := kappaCARqp_nonneg P Lν p
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
      (Nat.cast_le.2 hkmax).trans (ceil_log_div_le (mul_pos hθ0 hε₀.1) (norm_nonneg _) hβ₁0 hβ₁1)
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
      (fun y hyk => ⟨mem_univ y, (norm_le_of_phi2_le hyk).trans hck⟩)
  have hπ1 : ∀ l ∈ Finset.Icc 1 q, 1 < Optimization.arqpPiOf True p l := fun l hl =>
    (arqpPiOf_true_mem_Icc hqp hl).1
  have hF1 := (lemma_14_3_7_add h hθ0 hπ1 hκF fun k hk => (hcost k hk).1).trans
    (add_le_add (phase1Bound_le hκF (norm_nonneg _) (fun j hj => (hε j hj).1) hOT) le_rfl)
  have hD1 := (lemma_14_3_7_add h hθ0 hπ1 hκD.le fun k hk => (hcost k hk).2).trans
    (add_le_add (phase1Bound_le hκD.le (norm_nonneg _) (fun j hj => (hε j hj).1) hOT) le_rfl)
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
      ⟨Optimization.arqpPiOf_nonneg True p l, (arqpPiOf_true_mem_Icc hqp hl).2⟩) (hB.of_le hεβ)
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
      have h2 := inv_pow_le_arqp hε₀.1 hεj.1 (j := j) hq
      rw [← arqpPiOf_true_eq_false hq2 hj] at h2
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
      C * tpqpOrderF π q ε < (ε 0 * ε 1)⁻¹ := by
  obtain ⟨b, hb_def⟩ : ∃ b, b = (2 - π 1) / (π 1 - 1) := ⟨_, rfl⟩
  have hb : 0 < b := hb_def ▸ div_pos (by linarith) (by linarith)
  obtain ⟨mm, hmm⟩ : ∃ mm, mm = Optimization.finMax 0 (fun i => π i - 2) q := ⟨_, rfl⟩
  have hm0 : 0 ≤ mm := hmm ▸ Optimization.le_finMax_left
  have hmb : mm < b := hmm ▸ Optimization.finMax_lt hb (hb_def ▸ hπ)
  obtain ⟨a, ha_def⟩ : ∃ a, a = (mm + b) / 2 := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha_def]; linarith
  have hab : a < b := by rw [ha_def]; linarith
  have hma : ∀ i ∈ Finset.Icc 1 q, π i - 2 < a := fun i hi =>
    lt_of_le_of_lt (hmm ▸ Optimization.le_finMax (u := fun i => π i - 2) hi)
      (by rw [ha_def]; linarith)
  -- the exponents of `δ^{-1}` in the order
  set γ := Optimization.finMax 1 (fun i => if i = 1 then π 1 - 1 + a * π 1 else π i - 1) q with hγ
  have hγ1 : 1 ≤ γ := Optimization.le_finMax_left
  have hγa : γ < 1 + a := by
    refine Optimization.finMax_lt (by linarith) fun i hi => ?_
    split_ifs with h
    · have : a * (π 1 - 1) < 2 - π 1 := by
        rw [hb_def, lt_div_iff₀ (by linarith)] at hab; linarith
      nlinarith
    · linarith [hma i hi]
  set g := 1 + a - γ with hg
  have hg0 : 0 < g := by rw [hg]; linarith
  set δ := min (1 / 2) ((|C| + 1) ^ (-g⁻¹)) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (Real.rpow_pos_of_pos (by positivity) _)
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hδC : |C| + 1 ≤ δ ^ (-g) := by
    have h1 : δ ≤ (|C| + 1) ^ (-g⁻¹) := min_le_right _ _
    have h2 := Real.rpow_le_rpow_of_nonpos hδ0 h1 (by linarith : -g ≤ 0)
    rwa [← Real.rpow_mul (by positivity), show -g⁻¹ * -g = 1 by field_simp, Real.rpow_one] at h2
  set ε : ℕ → ℝ := fun i => if i = 0 then δ else if i = 1 then δ ^ a else 1 with hε
  have hε0 : ε 0 = δ := by simp [hε]
  have hε1 : ε 1 = δ ^ a := by simp [hε]
  have hεi : ∀ i, 2 ≤ i → ε i = 1 := fun i hi => by
    have h0 : i ≠ 0 := by omega
    have h1 : i ≠ 1 := by omega
    simp [hε, h0, h1]
  refine ⟨ε, fun j _ => ?_, ?_⟩
  · simp only [hε]
    split_ifs
    · exact ⟨hδ0, hδ1⟩
    · exact ⟨Real.rpow_pos_of_pos hδ0 _, Real.rpow_le_one hδ0.le hδ1 ha0.le⟩
    · exact ⟨one_pos, le_rfl⟩
  -- every term of the order is at most `δ^{-γ}`
  have hpow : ∀ e : ℝ, e ≤ γ → δ ^ (-e) ≤ δ ^ (-γ) := fun e he =>
    Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
  have hO : tpqpOrderF π q ε ≤ δ ^ (-γ) := by
    refine Optimization.finMax_le ?_ fun i hi => ?_
    · rw [hε0, ← Real.rpow_neg_one]; exact hpow 1 hγ1
    · have hγi : (if i = 1 then π 1 - 1 + a * π 1 else π i - 1) ≤ γ :=
        Optimization.le_finMax (u := fun i => if i = 1 then π 1 - 1 + a * π 1 else π i - 1) hi
      by_cases h1 : i = 1
      · subst h1
        simp only [ite_true] at hγi
        rw [hε0, hε1, ← Real.rpow_mul hδ0.le, ← Real.rpow_add hδ0]
        refine le_of_eq_of_le (by ring_nf) (hpow _ hγi)
      · simp only [h1, ite_false] at hγi
        rw [hε0, hεi i (by have := (Finset.mem_Icc.1 hi).1; omega), Real.one_rpow, mul_one]
        exact le_of_eq_of_le (by ring_nf) (hpow _ hγi)
  have hL : (ε 0 * ε 1)⁻¹ = δ ^ (-γ) * δ ^ (-g) := by
    rw [hε0, hε1, ← Real.rpow_add hδ0, ← Real.rpow_one_add' hδ0.le (by linarith),
      ← Real.rpow_neg hδ0.le]
    congr 1
    rw [hg]; ring
  rw [hL]
  have hγpos : 0 < δ ^ (-γ) := Real.rpow_pos_of_pos hδ0 _
  calc C * tpqpOrderF π q ε ≤ |C| * δ ^ (-γ) := by
        have hO0 : 0 ≤ tpqpOrderF π q ε :=
          (inv_pos.2 (by rw [hε0]; exact hδ0)).le.trans inv_le_tpqpOrderF
        calc C * tpqpOrderF π q ε ≤ |C| * tpqpOrderF π q ε :=
              mul_le_mul_of_nonneg_right (le_abs_self C) hO0
          _ ≤ |C| * δ ^ (-γ) := mul_le_mul_of_nonneg_left hO (abs_nonneg C)
    _ < (|C| + 1) * δ ^ (-γ) := by nlinarith
    _ ≤ δ ^ (-g) * δ ^ (-γ) := mul_le_mul_of_nonneg_right hδC hγpos.le
    _ = δ ^ (-γ) * δ ^ (-g) := mul_comm _ _

/-- **For `q < p` the bound of `theorem_14_3_9_arqp_corrected` is not within the printed order**
(ARqp-SC exponents `π_j = j(p+1)/p`): for every `C` there are tolerances with
`C O_F < (ε₀ ε_1)^{-1}`, a lower bound for its extra term `∑_j (ε₀ ε_j)^{-j}`
(`exists_tpqpOrderF_lt` with `π_1 = (p+1)/p`, `(2 - π_1)/(π_1 - 1) = p - 1 > q(p+1)/p - 2`). -/
theorem exists_tpqpOrderF_lt_arqp {p q : ℕ} (hq : 1 ≤ q) (hqp : q < p) (C : ℝ) :
    ∃ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) ∧
      C * tpqpOrderF (Optimization.arqpPiOf False p) q ε < (ε 0 * ε 1)⁻¹ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (by omega : 2 ≤ p)
  have hqp' : (q : ℝ) + 1 ≤ p := by exact_mod_cast (by omega : q + 1 ≤ p)
  have e1 : Optimization.arqpPiOf False p 1 = 1 + 1 / p := by
    rw [Optimization.arqpPiOf_of_neg not_false]; field_simp; push_cast; ring
  have hp1 : 1 / (p : ℝ) < 1 := by rw [div_lt_one hp0]; linarith
  refine exists_tpqpOrderF_lt (by rw [e1]; have : 0 < 1 / (p : ℝ) := by positivity
                                  linarith) (by rw [e1]; linarith) (fun i hi => ?_) C
  have hb : (2 - Optimization.arqpPiOf False p 1) / (Optimization.arqpPiOf False p 1 - 1) =
      (p : ℝ) - 1 := by rw [e1]; field_simp; ring
  rw [hb, Optimization.arqpPiOf_of_neg not_false]
  have hiq : (i : ℝ) ≤ q := by exact_mod_cast (Finset.mem_Icc.1 hi).2
  rw [sub_lt_iff_lt_add, div_lt_iff₀ hp0]
  nlinarith

/-- **For `q < p`, `q ≤ 2`, the bound of `theorem_14_3_9_arqp_unit_corrected` is not within the
printed order** (unit-radius exponents `π_j = (p+1)/(p-j+1)`): for every `C` there are tolerances
with `C O_F < (ε₀ ε_1)^{-1}` (`exists_tpqpOrderF_lt`; `(2 - π_1)/(π_1 - 1) = p - 1`, and
`π_2 - 2 = (3 - p)/(p - 1) < p - 1` for `p ≥ 3`). -/
theorem exists_tpqpOrderF_lt_arqp_unit {p q : ℕ} (hq : 1 ≤ q) (hq2 : q ≤ 2) (hqp : q < p)
    (C : ℝ) :
    ∃ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) ∧
      C * tpqpOrderF (Optimization.arqpPiOf True p) q ε < (ε 0 * ε 1)⁻¹ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have e1 : Optimization.arqpPiOf True p 1 = 1 + 1 / p := by
    rw [Optimization.arqpPiOf_of_pos trivial, Nat.sub_add_cancel (by omega : 1 ≤ p)]
    field_simp; push_cast; ring
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (by omega : 2 ≤ p)
  have hp1 : 1 / (p : ℝ) < 1 := by rw [div_lt_one hp0]; linarith
  refine exists_tpqpOrderF_lt (by rw [e1]; have : 0 < 1 / (p : ℝ) := by positivity
                                  linarith) (by rw [e1]; linarith) (fun i hi => ?_) C
  have hb : (2 - Optimization.arqpPiOf True p 1) / (Optimization.arqpPiOf True p 1 - 1) =
      (p : ℝ) - 1 := by rw [e1]; field_simp; ring
  rw [hb]
  obtain ⟨hi1, hiq⟩ := Finset.mem_Icc.1 hi
  have hi2 : i ≤ 2 := hiq.trans hq2
  interval_cases i
  · rw [e1]; have : 1 / (p : ℝ) ≤ 1 / 2 := by gcongr
    linarith
  · have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (by omega : 3 ≤ p)
    rw [Optimization.arqpPiOf_of_pos trivial]
    have e2 : ((p - 2 + 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [show p - 2 + 1 = p - 1 by omega, Nat.cast_sub (by omega)]; push_cast; ring
    rw [e2, sub_lt_iff_lt_add, div_lt_iff₀ (by linarith)]
    push_cast
    nlinarith

end NotDominated

end ARqpSCRuns


/-! ## INNER = ARqp-SC: the printed order fails for `q < p` -/


section ARqpSCSharp

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

/-- The objective `f(x) = x₁ - x₂/16` of this module (`Theorem1439Cex.objA`). -/
local notation "objG" => Theorem1439Cex.objA (1 / 16)

namespace Theorem1439ARqpCex

open Theorem1439Cex PlaneCex

/-! ### The data -/

/-- `f(a, b) = a - b/16`. -/
theorem objG_pt (a b : ℝ) : objG (pt a b) = a - b / 16 := by rw [objA_pt]; ring

/-- The first-order Taylor decrement of `μ(·, t)` at `y`:
`-∇μ(y, t)[d] = -(y₁³/2 + (f(y) - t)) d₁ + (f(y) - t)/16 d₂`. -/
theorem decrG (y : ℝ²) (t : ℝ) (d : ℝ²) :
    (ftaylorSeries ℝ (Constrained.targetMerit objG conC t) y).taylorDecrement 1 d =
      -(y 0 ^ 3 / 2 + (objG y - t)) * d 0 + (objG y - t) / 16 * d 1 := by
  rw [decr]; ring

/-- `μ(y, t) = y₁⁴/8 + (f(y) - t)²/2`. -/
theorem merit_eq (y : ℝ²) (t : ℝ) :
    Constrained.targetMerit objG conC t y = y 0 ^ 4 / 8 + (objG y - t) ^ 2 / 2 := by
  rw [Constrained.targetMerit_def, norm_conC]
  ring

/-- `μ(·, t)` is smooth. -/
theorem contDiff_merit (t : ℝ) : ContDiff ℝ ⊤ (Constrained.targetMerit objG conC t) :=
  contDiff_iff_contDiffAt.2 fun _ =>
    Constrained.contDiffAt_targetMerit (contDiff_objA _).contDiffAt contDiff_conC.contDiffAt

/-- The coefficients of `τ ↦ μ(y + τ s, t)`, a quartic polynomial. -/
noncomputable def coef (y s : ℝ²) (t : ℝ) (i : ℕ) : ℝ :=
  if i = 1 then y 0 ^ 3 * s 0 / 2 + (objG y - t) * (s 0 - s 1 / 16)
  else if i = 2 then 3 * y 0 ^ 2 * s 0 ^ 2 / 4 + (s 0 - s 1 / 16) ^ 2 / 2
  else if i = 3 then y 0 * s 0 ^ 3 / 2
  else if i = 4 then s 0 ^ 4 / 8 else 0

/-- `μ(y + τ s, t) = μ(y, t) + ∑_{i=1}^p τ^i a_i` for `p ≥ 4`. -/
theorem merit_line {p : ℕ} (hp : 4 ≤ p) (y s : ℝ²) (t τ : ℝ) :
    Constrained.targetMerit objG conC t (y + τ • s) =
      Constrained.targetMerit objG conC t y + ∑ i ∈ Finset.Icc 1 p, τ ^ i * coef y s t i := by
  have hsub : Finset.Icc 1 4 ⊆ Finset.Icc 1 p := Finset.Icc_subset_Icc le_rfl hp
  rw [← Finset.sum_subset hsub fun i hi hi' => by
    have h1 := Finset.mem_Icc.1 hi
    have h2 : ¬ (1 ≤ i ∧ i ≤ 4) := fun h => hi' (Finset.mem_Icc.2 h)
    have : i ≠ 1 ∧ i ≠ 2 ∧ i ≠ 3 ∧ i ≠ 4 := by omega
    simp [coef, this.1, this.2.1, this.2.2.1, this.2.2.2]]
  rw [show Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) by decide]
  simp only [merit_eq, objA_apply, coef, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  simp [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]
  ring

/-- **The Taylor model of `μ(·, t)` of degree `p ≥ 4` is exact**: `T_p(y, s) = μ(y + s, t)`. -/
theorem taylorSum_merit {p : ℕ} (hp : 4 ≤ p) (y : ℝ²) (t : ℝ) (s : ℝ²) :
    (ftaylorSeries ℝ (Constrained.targetMerit objG conC t) y).taylorSum p s =
      Constrained.targetMerit objG conC t (y + s) := by
  rw [← taylorPolynomial_eq_taylorSum]
  exact Optimization.taylorPolynomial_eq_self_of_poly
    ((contDiff_merit t).contDiffAt.of_le (by exact_mod_cast le_top))
    (merit_line hp y s t)

/-- The coefficient `σ/p! ‖s‖^{p-1}` of the gradient `σ/p! ‖s‖^{p-1} s` of the regularization
term `σ/(p+1)! ‖s‖^{p+1}`. -/
noncomputable def regC (p : ℕ) (σ : ℝ) (s : ℝ²) : ℝ :=
  σ / Optimization.realFactorial ((p : ℝ) + 1 - 1) * ‖s‖ ^ ((p : ℝ) + 1 - 2)

/-- **The first-order decrement of the model** `m(s) = μ(y + s, t) + σ/(p+1)! ‖s‖^{p+1}` (`p ≥ 4`)
at the trial step `s` along `d`: the decrement of `μ(·, t)` at `y + s` minus `c ⟨s, d⟩`,
`c = regC p σ s`. -/
theorem modelDecr {p : ℕ} (hp : 4 ≤ p) (y s d : ℝ²) (t σ : ℝ) :
    (ftaylorSeries ℝ (Optimization.regularizedModel
        (ftaylorSeries ℝ (Constrained.targetMerit objG conC t) y) p σ) s).taylorDecrement 1 d =
      (ftaylorSeries ℝ (Constrained.targetMerit objG conC t) (y + s)).taylorDecrement 1 d -
        regC p σ s * (s 0 * d 0 + s 1 * d 1) := by
  rw [FormalMultilinearSeries.taylorDecrement_one_apply,
    FormalMultilinearSeries.taylorDecrement_one_apply]
  simp only [ftaylorSeries, iteratedFDeriv_one_apply]
  have hr : (1 : ℝ) < (p : ℝ) + 1 := by
    have : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    linarith
  rw [Optimization.regularizedModel_eq_powRegularizedModel,
    Optimization.fderiv_powRegularizedModel hr]
  have hT : (ftaylorSeries ℝ (Constrained.targetMerit objG conC t) y).taylorSum p =
      fun v => Constrained.targetMerit objG conC t (y + v) :=
    funext (taylorSum_merit hp y t)
  rw [hT, fderiv_comp_add_left]
  simp only [add_apply, smul_apply, innerSL_apply_apply,
    smul_eq_mul]
  rw [show (inner ℝ s d : ℝ) = s 0 * d 0 + s 1 * d 1 by
    simp [PiLp.inner_apply, Fin.sum_univ_two]; ring]
  unfold regC
  ring

/-- The Taylor decrements of order `j ≤ 4` of `μ(·, t)` at `y`: `ΔT_j(y, d) = -∑_{i=1}^j a_i`. -/
theorem decr_eq_coef {j : ℕ} (hj : j ≤ 4) (y d : ℝ²) (t : ℝ) :
    (ftaylorSeries ℝ (Constrained.targetMerit objG conC t) y).taylorDecrement j d =
      -∑ i ∈ Finset.Icc 1 j, coef y d t i := by
  rw [FormalMultilinearSeries.taylorDecrement, ← taylorPolynomial_eq_taylorSum,
    taylorPolynomial_zero_right,
    Optimization.taylorPolynomial_eq_of_poly (N := 4) (a := coef y d t)
      ((contDiff_merit t).contDiffAt.of_le (by exact_mod_cast le_top))
      (Filter.Eventually.of_forall fun τ => by simpa [one_mul] using merit_line le_rfl y d t τ) hj]
  ring

/-- **The second-order decrement of `μ(·, t)` is at most the first-order one** (`μ` is convex):
`ΔT_2(y, d) = ΔT_1(y, d) - a_2` with `a_2 = 3 y₁² d₁²/4 + (d₁ - d₂/16)²/2 ≥ 0`. -/
theorem decr_two_le (y d : ℝ²) (t : ℝ) :
    (ftaylorSeries ℝ (Constrained.targetMerit objG conC t) y).taylorDecrement 2 d ≤
      (ftaylorSeries ℝ (Constrained.targetMerit objG conC t) y).taylorDecrement 1 d := by
  rw [decr_eq_coef (by norm_num), decr_eq_coef (by norm_num)]
  rw [show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide]
  simp [coef]
  nlinarith [sq_nonneg (d 0 - d 1 / 16), sq_nonneg (y 0 * d 0)]

/-- `∇²μ(y, t)[d]² ≥ 0`. -/
theorem iteratedFDeriv_two_merit_nonneg (y d : ℝ²) (t : ℝ) :
    0 ≤ iteratedFDeriv ℝ 2 (Constrained.targetMerit objG conC t) y (fun _ => d) := by
  have h := decr_two_le y d t
  rw [FormalMultilinearSeries.taylorDecrement_eq, FormalMultilinearSeries.taylorDecrement_eq,
    show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide] at h
  simp only [Finset.Icc_self, Finset.sum_singleton, ftaylorSeries] at h
  rw [Finset.sum_insert (by decide), Finset.sum_singleton] at h
  norm_num at h
  linarith

/-- **The second-order decrement of the model is at most the first-order one plus
`σ ‖s‖³/2`** (`p ≥ 4`, `σ ≥ 0`, `‖s‖, ‖d‖ ≤ 1`): the Hessian of `μ` is positive semidefinite and
that of the regularization term is at most `σ ‖s‖^{p-1}/(p-1)!` in norm. -/
theorem modelDecr_two_le {p : ℕ} (hp : 4 ≤ p) {σ : ℝ} (hσ : 0 ≤ σ) (y : ℝ²) (t : ℝ) {s d : ℝ²}
    (hs : ‖s‖ ≤ 1) (hd : ‖d‖ ≤ 1) :
    (ftaylorSeries ℝ (Optimization.regularizedModel
        (ftaylorSeries ℝ (Constrained.targetMerit objG conC t) y) p σ) s).taylorDecrement 2 d ≤
      (ftaylorSeries ℝ (Optimization.regularizedModel
        (ftaylorSeries ℝ (Constrained.targetMerit objG conC t) y) p σ) s).taylorDecrement 1 d +
        σ * ‖s‖ ^ 3 / 2 := by
  set m := Optimization.regularizedModel
    (ftaylorSeries ℝ (Constrained.targetMerit objG conC t) y) p σ with hm
  have e : (ftaylorSeries ℝ m s).taylorDecrement 2 d =
      (ftaylorSeries ℝ m s).taylorDecrement 1 d - 1 / 2 * iteratedFDeriv ℝ 2 m s (fun _ => d) := by
    rw [FormalMultilinearSeries.taylorDecrement_eq, FormalMultilinearSeries.taylorDecrement_eq,
      show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide, Finset.sum_insert (by decide),
      Finset.sum_singleton, Finset.Icc_self, Finset.sum_singleton]
    simp only [ftaylorSeries]
    norm_num
    ring
  have hT : (ftaylorSeries ℝ (Constrained.targetMerit objG conC t) y).taylorSum p =
      fun v => Constrained.targetMerit objG conC t (y + v) :=
    funext (taylorSum_merit hp y t)
  have e2 : iteratedFDeriv ℝ 2 m s (fun _ => d) =
      iteratedFDeriv ℝ 2 (Constrained.targetMerit objG conC t) (y + s) (fun _ => d) +
        σ / ((p + 1)! : ℝ) * iteratedFDeriv ℝ 2 (fun y : ℝ² => ‖y‖ ^ (p + 1)) s (fun _ => d) := by
    rw [hm, Optimization.iteratedFDeriv_regularizedModel (Or.inl (by omega)), hT,
      iteratedFDeriv_comp_add_left]
    simp only [add_apply, smul_apply, smul_eq_mul]
  rw [e, e2]
  have h1 := iteratedFDeriv_two_merit_nonneg (y + s) d t
  have h2 := abs_iteratedFDeriv_norm_pow_apply_le (E := ℝ²) (r := p + 1) (ℓ := 2) (by omega)
    (s := s) (Or.inr (by omega)) d
  have hf : ((p + 1)! : ℝ) / ((p + 1 - 2)! : ℝ) ≤ ((p + 1)! : ℝ) := by
    apply div_le_self (by positivity)
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
  have hs3 : ‖s‖ ^ (p + 1 - 2) ≤ ‖s‖ ^ 3 := pow_le_pow_of_le_one (norm_nonneg _) hs (by omega)
  have hd2 : ‖d‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hd
  have hb : |iteratedFDeriv ℝ 2 (fun y : ℝ² => ‖y‖ ^ (p + 1)) s (fun _ => d)| ≤
      ((p + 1)! : ℝ) * ‖s‖ ^ 3 := by
    refine h2.trans ?_
    calc ((p + 1)! : ℝ) / ((p + 1 - 2)! : ℝ) * ‖s‖ ^ (p + 1 - 2) * ‖d‖ ^ 2
        ≤ ((p + 1)! : ℝ) * ‖s‖ ^ 3 * 1 := by gcongr
      _ = _ := mul_one _
  have hc : σ / ((p + 1)! : ℝ) * iteratedFDeriv ℝ 2 (fun y : ℝ² => ‖y‖ ^ (p + 1)) s
      (fun _ => d) ≥ -(σ * ‖s‖ ^ 3) := by
    have hpf : (0 : ℝ) < ((p + 1)! : ℝ) := by positivity
    have := neg_abs_le (iteratedFDeriv ℝ 2 (fun y : ℝ² => ‖y‖ ^ (p + 1)) s (fun _ => d))
    have h3 : σ / ((p + 1)! : ℝ) * (-(((p + 1)! : ℝ) * ‖s‖ ^ 3)) = -(σ * ‖s‖ ^ 3) := by
      field_simp
    rw [ge_iff_le, ← h3]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

/-- **A witness from a maximizer**: a Taylor decrement attains its supremum over the unit ball
intersected with a closed set containing `0`, and a maximizer is a `ς`-approximate optimality
displacement for every `ς ≤ 1`. -/
theorem exists_isApprox_max (D : FormalMultilinearSeries ℝ ℝ² ℝ) (j : ℕ) {S : Set ℝ²}
    (hS : IsClosed S) (h0 : (0 : ℝ²) ∈ S) {ς : ℝ} (hς : ς ≤ 1) :
    ∃ d, Optimization.IsApproxMeasureStep (D.taylorDecrement j) 1 S ς d ∧
      D.taylorDecrement j d = Optimization.decrementMeasure (D.taylorDecrement j) 1 S := by
  obtain ⟨d, hd, hdM⟩ := Optimization.exists_decrementMeasure_eq hS h0 zero_le_one
    (D.continuous_taylorDecrement j).continuousOn
  have hM := Optimization.taylorMeasure_nonneg D j h0 zero_le_one
  exact ⟨d, ⟨hd, by rw [hdM]; exact mul_le_of_le_one_left hM hς⟩, hdM⟩

/-! ### One-step ARqp-SC calls -/

/-- The constants of ARqpC used by the counterexample: `σ₀ = σ_min = 10⁻⁶`, `η₁ = 1/4`,
`η₂ = 3/4`, `γ₁ = 1/2`, `γ₂ = 2 < γ₃ = 3`, `θ = 1/4`, `ς = 1/2` (so `θ < ς`). -/
noncomputable def cexP : ARqpCParams where
  σ₀ := 1 / 10 ^ 6
  σmin := 1 / 10 ^ 6
  η₁ := 1 / 4
  η₂ := 3 / 4
  γ₁ := 1 / 2
  γ₂ := 2
  γ₃ := 3
  σ₀_pos := by norm_num
  σmin_nonneg := by norm_num
  σmin_le_σ₀ := le_rfl
  η₁_pos := by norm_num
  η₁_le_η₂ := by norm_num
  η₂_lt_one := by norm_num
  γ₁_pos := by norm_num
  γ₁_lt_one := by norm_num
  one_lt_γ₂ := by norm_num
  γ₂_le_γ₃ := by norm_num
  θ := 1 / 4
  ς := 1 / 2
  θ_pos := by norm_num
  θ_lt_one := by norm_num
  ς_pos := by norm_num
  ς_le_one := by norm_num
  σmin_pos := by norm_num

/-- The iterates `x, x + s, x + s, …` of a one-step INNER call. -/
noncomputable def stepX {n : ℕ} (x s : EuclideanSpace ℝ (Fin n)) : ℕ → EuclideanSpace ℝ (Fin n) :=
  fun i => if i = 0 then x else x + s

/-- **A one-step ARqp-SC call** (ARqpC-SC with `c = 0`, `h = 0`, `1 ≤ q ≤ p`, all radii `1`) on
an objective `F` bounded below on `X` whose Taylor model of degree `p` at `x` is exact: INNER's
Step-1 test fails at `x` (the witnesses `d₀ j`), the detailed Step 2 returns the step `s` (model
decrease, the model witnesses `dm j` at `s`), the iteration is very successful (ratio `1`), and
the Step-1 test holds at `x + s` (the witnesses `d₁ j`), where the run terminates. Its iterates
are `x, x + s`, one successful iteration, output radius `1`. -/
theorem callOut_one_step {n : ℕ} {F : EuclideanSpace ℝ (Fin n) → ℝ}
    {X : Set (EuclideanSpace ℝ (Fin n))} {p q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) {P : ARqpCParams}
    {ε : ℕ → ℝ} (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1) {x s : EuclideanSpace ℝ (Fin n)}
    {d₀ d₁ dm : ℕ → EuclideanSpace ℝ (Fin n)} (hx : x ∈ X)
    (hxs : x + s ∈ X) (hs1 : ‖s‖ < 1)
    (hTay : ∀ v, (ftaylorSeries ℝ F x).taylorSum p v = F (x + v)) (hlow : BddBelow (F '' X))
    (hmod : Optimization.regularizedModel (ftaylorSeries ℝ F x) p P.σ₀ s < F x)
    (hd₀ : ∀ j ∈ Finset.Icc 1 q, Optimization.IsApproxMeasureStep
      ((ftaylorSeries ℝ F x).taylorDecrement j) 1 {e | x + e ∈ X} P.ς (d₀ j))
    (hfail : ∃ j ∈ Finset.Icc 1 q, P.ς * ε j / j ! < (ftaylorSeries ℝ F x).taylorDecrement j (d₀ j))
    (hdm : ∀ j ∈ Finset.Icc 1 q, Optimization.IsApproxMeasureStep ((ftaylorSeries ℝ
      (Optimization.regularizedModel (ftaylorSeries ℝ F x) p P.σ₀) s).taylorDecrement j) 1
      {e | x + s + e ∈ X} P.ς (dm j) ∧
      (ftaylorSeries ℝ (Optimization.regularizedModel (ftaylorSeries ℝ F x) p P.σ₀)
        s).taylorDecrement j (dm j) ≤ P.ς * P.θ * ε j / j !)
    (hd₁ : ∀ j ∈ Finset.Icc 1 q, Optimization.IsApproxMeasureStep
      ((ftaylorSeries ℝ F (x + s)).taylorDecrement j) 1 {e | x + s + e ∈ X} P.ς (d₁ j))
    (hpass : ∀ j ∈ Finset.Icc 1 q,
      (ftaylorSeries ℝ F (x + s)).taylorDecrement j (d₁ j) ≤ P.ς * ε j / j !) :
    IsARqpSCCallOut F X p q P ε (stepX x s) 1 (fun _ => True) (fun _ => 1) := by
  set xs := stepX x s with hxs_def
  set ss : ℕ → EuclideanSpace ℝ (Fin n) := fun _ => s
  set σs : ℕ → ℝ := fun _ => P.σ₀
  set δ : ℕ → ℕ → ℝ := fun _ _ => 1
  set dd : ℕ → ℕ → EuclideanSpace ℝ (Fin n) := fun i j => if i = 0 then d₀ j else d₁ j
  set dmm : ℕ → ℕ → EuclideanSpace ℝ (Fin n) := fun _ j => dm j
  have hx0 : xs 0 = x := rfl
  have hx1 : xs 1 = x + s := rfl
  have hT0 : (ftaylorSeries ℝ F x).taylorSum p 0 = F x := by rw [hTay, add_zero]
  have hm0 : Optimization.regularizedModel (ftaylorSeries ℝ F x) p P.σ₀ 0 = F x :=
    Optimization.regularizedModel_ftaylorSeries_zero_right p P.σ₀ F x
  have hreg : 0 ≤ P.σ₀ / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) := by
    have := P.σ₀_pos; positivity
  have hFs : F (x + s) < F x := by
    rw [Optimization.regularizedModel_def, hTay] at hmod; linarith
  have hpred : (ftaylorSeries ℝ F x).taylorDecrement p s = F x - F (x + s) := by
    rw [FormalMultilinearSeries.taylorDecrement, hTay, hTay, add_zero]
  have hρ : Optimization.arqpRho F p xs ss σs 0 = 1 := by
    simp only [Optimization.arqpRho, Optimization.arqpRatio, Optimization.arqpData,
      Optimization.ARqpData.ofTaylor_pred, Optimization.reductionRatio, hx0, ss, hpred]
    exact div_self (by linarith)
  -- the Step-1 tests
  have h1stop :
      Optimization.arqpStop₁ P.toARqpParams q ε (Optimization.arqpData F p xs σs) δ dd 1 := by
    intro j hj
    simpa [dd, δ, hx1] using hpass j hj
  have hn1 : ¬ Optimization.arqpStop₁ P.toARqpParams q ε (Optimization.arqpData F p xs σs) δ dd 0
      := by
    intro h
    obtain ⟨j, hj, hlt⟩ := hfail
    have := h j hj
    simp [dd, δ, hx0] at this
    linarith
  have hn2 : ¬ Optimization.arqpStop₂ (Optimization.arqpData F p xs σs) ss 0 := by
    intro h
    simp only [Optimization.arqpStop₂, Optimization.arqpData, Optimization.ARqpData.ofTaylor_model,
      hx0, ss, σs] at h
    rw [h, hm0] at hmod
    exact lt_irrefl _ hmod
  have hNot0 : ¬ Optimization.arqpStop F P.toARqpParams p q ε xs ss σs δ dd 0 := by
    rintro (h | h)
    · exact hn1 h
    · exact hn2 h
  have hStop1 : Optimization.arqpStop F P.toARqpParams p q ε xs ss σs δ dd 1 := Or.inl h1stop
  -- the model is bounded below on the feasible steps
  have hbdd : BddBelow (Optimization.regularizedModel (ftaylorSeries ℝ F x) p P.σ₀ ''
      {v | x + v ∈ X}) := by
    obtain ⟨b, hb⟩ := hlow
    refine ⟨b, forall_mem_image.2 fun v hv => ?_⟩
    rw [Optimization.regularizedModel_def, hTay]
    have := hb (mem_image_of_mem F hv)
    have : 0 ≤ P.σ₀ / ((p + 1)! : ℝ) * ‖v‖ ^ (p + 1) := by have := P.σ₀_pos; positivity
    linarith
  -- the ARqp run
  have hrun : Chapter12.algorithm_12_2_2_feasible F X P.toARqpParams p q ε (fun _ => 1) xs ss σs
      δ δ dd dmm := by
    refine ⟨⟨rfl, fun k hk h1 => ?_, fun k hk => ?_⟩, hx, rfl, fun k hk => ?_, fun k hk => ?_⟩
    · rcases k with _ | _ | k
      · refine ⟨by simpa [hx0, ss] using hxs, ?_, fun h => ?_, fun _ _ => one_pos,
          fun _ _ => le_rfl, Or.inr fun j hj => ?_⟩
        · simp only [Optimization.arqpData, Optimization.ARqpData.ofTaylor_model, hx0, ss, σs, hm0]
          exact hmod.le
        · simp only [Optimization.arqpData, Optimization.ARqpData.ofTaylor_model, hx0, ss, σs,
            hm0] at h
          exact absurd h hmod.ne
        · simp only [Optimization.arqpData, Optimization.ARqpData.ofTaylor_modelDec, hx0, ss, σs,
            dmm, δ]
          exact ⟨(hdm j hj).1, by simpa using (hdm j hj).2⟩
      · exact absurd h1stop h1
      · exact absurd hStop1 (hk 1 (by omega))
    · rcases k with _ | k
      · have := Optimization.arAcceptance_of_one_le P.toARParams (ρ := 1) le_rfl x s
          (σ := P.σ₀) P.σmin_le_σ₀ P.σ₀_pos.le
        change Optimization.ARAcceptance P.toARParams (Optimization.arqpRho F p xs ss σs 0) (xs 0)
          (ss 0) (xs 1) (σs 0) (σs 1)
        rw [hρ, hx0, hx1]
        exact this
      · exact absurd hStop1 (hk 1 (by omega))
    · intro j hj
      rcases k with _ | _ | k
      · exact hd₀ j hj
      · exact hd₁ j hj
      · exact absurd hStop1 (hk 1 (by omega))
    · rcases k with _ | k
      · have hρ' : Optimization.arqpRatio F (Optimization.arqpData F p xs σs) xs ss 0 = 1 := hρ
        refine ⟨fun _ => rfl, fun h => absurd ?_ h⟩
        rw [hρ']
        exact P.η₁_le_η₂.trans P.η₂_lt_one.le
      · exact absurd hStop1 (hk 1 (by omega))
  -- the ARqpC-SC run
  have h1 : (fun y => F y + zeroOuter (zeroCon n y)) = F := funext fun y => by simp
  have h2 := zero_arqpcData_eq F p xs σs
  have hr : algorithm_14_1_1 F (zeroCon n) zeroOuter X p q P ε (fun _ => 1) xs ss σs δ δ dd
      dmm := by
    refine ⟨hq, hqp, hε, fun _ _ => ⟨one_pos, le_rfl⟩, by rw [h1, h2]; exact hrun,
      fun k hk hns => ?_⟩
    rw [h2] at hns
    rcases k with _ | _ | k
    · have em : Optimization.compositeRegularizedModel (ftaylorSeries ℝ F x)
          (ftaylorSeries ℝ (zeroCon n) x) zeroOuter p P.σ₀ =
          Optimization.regularizedModel (ftaylorSeries ℝ F x) p P.σ₀ :=
        Optimization.compositeRegularizedModel_zero_fun _ _ _ _
      have eΔ : (fun j s d => Optimization.compositeModelDecrement (ftaylorSeries ℝ F x)
          (ftaylorSeries ℝ (zeroCon n) x) zeroOuter p P.σ₀ j s d) =
          fun j s d => (ftaylorSeries ℝ (Optimization.regularizedModel (ftaylorSeries ℝ F x) p
            P.σ₀) s).taylorDecrement j d := by
        funext j s d
        exact congrFun (Optimization.compositeModelDecrement_zero_fun _ _ _ _ j s) d
      unfold algorithm_14_1_2 Optimization.IsARqpCDetailedStep
      simp only [hx0, ss, σs, δ]
      rw [em, eΔ]
      exact Optimization.IsDetailedStepOutput.of_short_step hq hxs hbdd (by rw [hm0]; exact hmod)
        hs1 fun j hj => ⟨(hdm j hj).1.1, (hdm j hj).1.2, (hdm j hj).2⟩
    · exact absurd h1stop hns
    · exact absurd (zero_arqpcStop_iff.2 hStop1) (hk 1 (by omega))
  refine ⟨xs, ss, σs, δ, δ, dd, dmm, 1, hr, ⟨zero_arqpcStop_iff.2 hStop1, fun j hj => ?_⟩,
    le_rfl, fun i _ => rfl, fun i hi => ?_, Or.inl fun j _ => rfl⟩
  · obtain rfl : j = 0 := by omega
    exact zero_arqpcStop_iff.not.2 hNot0
  · obtain rfl : i = 0 := by omega
    rw [zero_arqpRatio_eq, hρ]
    exact iff_of_true trivial (P.η₁_le_η₂.trans P.η₂_lt_one.le)


/-! ### One-step calls on the counterexample -/

/-- `0 ≤ regC p σ s ≤ σ ‖s‖³/24` for `σ ≥ 0`, `‖s‖ ≤ 1`, `p ≥ 4`. -/
theorem regC_mem {p : ℕ} (hp : 4 ≤ p) {σ : ℝ} (hσ : 0 ≤ σ) {s : ℝ²} (hs : ‖s‖ ≤ 1) :
    0 ≤ regC p σ s ∧ regC p σ s ≤ σ * ‖s‖ ^ 3 / 24 := by
  have e1 : (p : ℝ) + 1 - 1 = (p : ℝ) := by ring
  have e2 : (p : ℝ) + 1 - 2 = ((p - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  unfold regC
  rw [e1, e2, Optimization.realFactorial_natCast, Real.rpow_natCast]
  have hf : (24 : ℝ) ≤ (p ! : ℝ) := by
    have := Nat.factorial_le hp
    exact_mod_cast this
  have hpow : ‖s‖ ^ (p - 1) ≤ ‖s‖ ^ 3 := pow_le_pow_of_le_one (norm_nonneg _) hs (by omega)
  have hn : 0 ≤ ‖s‖ ^ (p - 1) := by positivity
  refine ⟨by positivity, ?_⟩
  calc σ / (p ! : ℝ) * ‖s‖ ^ (p - 1) ≤ σ / 24 * ‖s‖ ^ 3 := by
        gcongr
    _ = σ * ‖s‖ ^ 3 / 24 := by ring

/-- `σ/(p+1)! ‖s‖^{p+1} ≤ σ ‖s‖⁵/120` for `σ ≥ 0`, `‖s‖ ≤ 1`, `p ≥ 4`. -/
theorem reg_le {p : ℕ} (hp : 4 ≤ p) {σ : ℝ} (hσ : 0 ≤ σ) {s : ℝ²} (hs : ‖s‖ ≤ 1) :
    σ / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) ≤ σ * ‖s‖ ^ 5 / 120 := by
  have hf : (120 : ℝ) ≤ ((p + 1)! : ℝ) := by
    have := Nat.factorial_le (show 5 ≤ p + 1 by omega)
    exact_mod_cast this
  have hpow : ‖s‖ ^ (p + 1) ≤ ‖s‖ ^ 5 := pow_le_pow_of_le_one (norm_nonneg _) hs (by omega)
  calc σ / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) ≤ σ / 120 * ‖s‖ ^ 5 := by
        gcongr
    _ = σ * ‖s‖ ^ 5 / 120 := by ring

/-- **A one-step call of the counterexample.** For the target `t`, the start `x = (xa, xb)` and
the landing point `x' = (ya, yb)` in `[-1/2, 1/2]²` with `F = f(x) - t`, `F' = f(x') - t`,
`L = |ya - xa| + |yb - xb| ≤ 1/2`, an order `q ∈ {1, 2}`, INNER tolerances `T₁ ∈ (0, 1]`
(order `1`) and `T₂ ∈ (0, 1]` (order `2`, used when `q = 2`, with `T₁/4 + σ₀ L³/2 ≤ T₂/16`), and
a sign `g = ±1`: if the linear decrease at `x` exceeds `T₁` (Step 1 fails), `μ` decreases by more
than the regularization bound `σ₀ L⁵/120`, and at `x'` the gradient has the signs of `g` and
`ℓ¹`-norm plus `σ₀ L⁴/24` at most `T₁/4` (model criticality, and Step 1 holds; at order `2` the
decrements are bounded through `decr_two_le` and `modelDecr_two_le`, and the witnesses are
maximizers), then the call from `x` to `x'` is a one-step ARqp-SC call with parameters `cexP`. -/
theorem callOut_cex {p q : ℕ} (hp : 4 ≤ p) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    {t xa xb ya yb T₁ T₂ g : ℝ} {ε : ℕ → ℝ} (hT : ε 1 = T₁) (hT2 : 2 ≤ q → ε 2 = T₂)
    (hT20 : 0 < T₂) (hT21 : T₂ ≤ 1)
    (hT12 : T₁ / 4 + 1 / 10 ^ 6 * (|ya - xa| + |yb - xb|) ^ 3 / 2 ≤ T₂ / 16)
    (hxa : |xa| ≤ 1 / 2) (hxb : |xb| ≤ 1 / 2) (hya : |ya| ≤ 1 / 2) (hyb : |yb| ≤ 1 / 2)
    (hL : |ya - xa| + |yb - xb| ≤ 1 / 2) (hT0 : 0 < T₁) (hT1 : T₁ ≤ 1)
    (hF0 : 0 ≤ xa - xb / 16 - t) (hxa0 : 0 ≤ xa)
    (hfail : T₁ < xa ^ 3 / 2 + (xa - xb / 16 - t) + (xa - xb / 16 - t) / 16)
    (hmod : ya ^ 4 / 8 + (ya - yb / 16 - t) ^ 2 / 2 +
      1 / 10 ^ 6 * (|ya - xa| + |yb - xb|) ^ 5 / 120 < xa ^ 4 / 8 + (xa - xb / 16 - t) ^ 2 / 2)
    (hg : g = 1 ∨ g = -1) (hgA : 0 ≤ g * (ya ^ 3 / 2 + (ya - yb / 16 - t)))
    (hgF : g * (ya - yb / 16 - t) ≤ 0) (hgs0 : 0 ≤ g * (ya - xa)) (hgs1 : 0 ≤ g * (yb - xb))
    (hcrit : g * (ya ^ 3 / 2 + (ya - yb / 16 - t)) - g * (ya - yb / 16 - t) / 16 +
      1 / 10 ^ 6 * (|ya - xa| + |yb - xb|) ^ 4 / 24 ≤ T₁ / 4) :
    IsARqpSCCallOut (Constrained.targetMerit objG conC t) boxX p q cexP ε
      (fun i => if i = 0 then pt xa xb else pt ya yb) 1 (fun _ => True) (fun _ => 1) := by
  have hg1 : |g| = 1 := by rcases hg with rfl | rfl <;> simp
  set s := pt ya yb - pt xa xb with hs_def
  have hs : s = pt (ya - xa) (yb - xb) := pt_sub _ _ _ _
  have hxs : pt xa xb + s = pt ya yb := by rw [hs_def]; abel
  have hsL : ‖s‖ ≤ |ya - xa| + |yb - xb| := by rw [hs]; exact norm_pt_le_add _ _
  have hs1 : ‖s‖ ≤ 1 := by linarith
  have hσ : cexP.σ₀ = 1 / 10 ^ 6 := rfl
  have hς : cexP.ς = 1 / 2 := rfl
  have hθ : cexP.θ = 1 / 4 := rfl
  have hxi : (fun i => if i = 0 then pt xa xb else pt ya yb) = stepX (pt xa xb) s := by
    funext i; rcases i with _ | i
    · rfl
    · simp [stepX, hxs]
  rw [hxi]
  have hmemx : pt xa xb ∈ boxX := pt_mem (hxa.trans (by norm_num)) (hxb.trans (by norm_num))
  have hmemy : pt ya yb ∈ boxX := pt_mem (hya.trans (by norm_num)) (hyb.trans (by norm_num))
  have hS : ∀ {a b : ℝ}, |a| ≤ 1 / 2 → |b| ≤ 1 / 2 → ∀ {c d : ℝ}, |c| ≤ 1 / 2 → |d| ≤ 1 / 2 →
      pt c d ∈ {e | pt a b + e ∈ boxX} := fun {a b} ha hb {c d} hc hd => by
    simp only [mem_ofPred_eq, pt_add, pt_zero, pt_one]
    exact pt_mem ((abs_add_le _ _).trans (by linarith)) ((abs_add_le _ _).trans (by linarith))
  have h0S : ∀ {a b : ℝ}, |a| ≤ 1 / 2 → |b| ≤ 1 / 2 → (0 : ℝ²) ∈ {e | pt a b + e ∈ boxX} :=
    fun {a b} ha hb => by
      simp only [mem_ofPred_eq, add_zero]
      exact pt_mem (ha.trans (by norm_num)) (hb.trans (by norm_num))
  have hhalf : |(1 / 2 : ℝ)| ≤ 1 / 2 := by norm_num
  have hhalf' : |(-1 / 2 : ℝ)| ≤ 1 / 2 := by norm_num
  have hgw : |-g / 2| ≤ 1 / 2 := by rw [abs_div, abs_neg, hg1]; norm_num
  obtain ⟨hc0, hc1⟩ := regC_mem hp (σ := cexP.σ₀) (by rw [hσ]; norm_num) hs1
  have hcL : regC p cexP.σ₀ s * (|ya - xa| + |yb - xb|) ≤
      1 / 10 ^ 6 * (|ya - xa| + |yb - xb|) ^ 4 / 24 := by
    have h3 : ‖s‖ ^ 3 ≤ (|ya - xa| + |yb - xb|) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hsL 3
    have hL0 : 0 ≤ |ya - xa| + |yb - xb| := by positivity
    calc regC p cexP.σ₀ s * (|ya - xa| + |yb - xb|)
        ≤ cexP.σ₀ * ‖s‖ ^ 3 / 24 * (|ya - xa| + |yb - xb|) :=
          mul_le_mul_of_nonneg_right hc1 hL0
      _ ≤ 1 / 10 ^ 6 * (|ya - xa| + |yb - xb|) ^ 3 / 24 * (|ya - xa| + |yb - xb|) := by
          rw [hσ]; gcongr
      _ = _ := by ring
  have hgabs : ∀ z : ℝ, 0 ≤ -g * z → |z| = -g * z := fun z hz => by
    rcases hg with rfl | rfl
    · simp only [neg_mul, one_mul] at hz ⊢; exact abs_of_nonpos (by linarith)
    · simp only [neg_neg, one_mul] at hz ⊢; exact abs_of_nonneg hz
  have hgle : ∀ z : ℝ, g * z ≤ |z| := fun z => by
    rcases hg with rfl | rfl
    · simp only [one_mul]; exact le_abs_self z
    · simp only [neg_one_mul]; exact neg_le_abs z
  have hs0 : s 0 = ya - xa := by rw [hs, pt_zero]
  have hs1' : s 1 = yb - xb := by rw [hs, pt_one]
  have hΔm : ∀ d : ℝ², (ftaylorSeries ℝ (Optimization.regularizedModel (ftaylorSeries ℝ
      (Constrained.targetMerit objG conC t) (pt xa xb)) p cexP.σ₀) s).taylorDecrement 1 d =
      (-(ya ^ 3 / 2 + (ya - yb / 16 - t)) - regC p cexP.σ₀ s * (ya - xa)) * d 0 +
        ((ya - yb / 16 - t) / 16 - regC p cexP.σ₀ s * (yb - xb)) * d 1 := fun d => by
    rw [modelDecr hp, hxs, decrG, objG_pt, hs0, hs1']
    simp only [pt_zero]
    ring
  have hΔ' : ∀ d : ℝ², (ftaylorSeries ℝ (Constrained.targetMerit objG conC t)
      (pt xa xb + s)).taylorDecrement 1 d =
      -(ya ^ 3 / 2 + (ya - yb / 16 - t)) * d 0 + (ya - yb / 16 - t) / 16 * d 1 := fun d => by
    rw [hxs, decrG, objG_pt]; simp only [pt_zero]
  have hgs0' : 0 ≤ regC p cexP.σ₀ s * (g * (ya - xa)) := mul_nonneg hc0 hgs0
  have hgs1' : 0 ≤ regC p cexP.σ₀ s * (g * (yb - xb)) := mul_nonneg hc0 hgs1
  have hab0 : |-(ya ^ 3 / 2 + (ya - yb / 16 - t)) - regC p cexP.σ₀ s * (ya - xa)| =
      -g * (-(ya ^ 3 / 2 + (ya - yb / 16 - t)) - regC p cexP.σ₀ s * (ya - xa)) :=
    hgabs _ (by
      have e : -g * (-(ya ^ 3 / 2 + (ya - yb / 16 - t)) - regC p cexP.σ₀ s * (ya - xa)) =
        g * (ya ^ 3 / 2 + (ya - yb / 16 - t)) + regC p cexP.σ₀ s * (g * (ya - xa)) := by ring
      rw [e]; linarith)
  have hab1 : |(ya - yb / 16 - t) / 16 - regC p cexP.σ₀ s * (yb - xb)| =
      -g * ((ya - yb / 16 - t) / 16 - regC p cexP.σ₀ s * (yb - xb)) :=
    hgabs _ (by
      have e : -g * ((ya - yb / 16 - t) / 16 - regC p cexP.σ₀ s * (yb - xb)) =
        -(g * (ya - yb / 16 - t)) / 16 + regC p cexP.σ₀ s * (g * (yb - xb)) := by ring
      rw [e]; linarith)
  have hab0' : |-(ya ^ 3 / 2 + (ya - yb / 16 - t))| = -g * -(ya ^ 3 / 2 + (ya - yb / 16 - t)) :=
    hgabs _ (by rw [neg_mul_neg]; exact hgA)
  have hab1' : |(ya - yb / 16 - t) / 16| = -g * ((ya - yb / 16 - t) / 16) :=
    hgabs _ (by
      have e : -g * ((ya - yb / 16 - t) / 16) = -(g * (ya - yb / 16 - t)) / 16 := by ring
      rw [e]; linarith)
  have hsg : g * (ya - xa) + g * (yb - xb) ≤ |ya - xa| + |yb - xb| :=
    add_le_add (hgle _) (hgle _)
  have hcs : regC p cexP.σ₀ s * (g * (ya - xa) + g * (yb - xb)) ≤
      regC p cexP.σ₀ s * (|ya - xa| + |yb - xb|) := mul_le_mul_of_nonneg_left hsg hc0
  -- the order-`2` witnesses: maximizers
  have hSc : ∀ z : ℝ², IsClosed {e : ℝ² | z + e ∈ boxX} := fun z =>
    isClosed_boxX.preimage (continuous_const.add continuous_id)
  have hς1 : cexP.ς ≤ 1 := cexP.ς_le_one
  obtain ⟨w₀, hw₀, -⟩ := exists_isApprox_max (ftaylorSeries ℝ
    (Constrained.targetMerit objG conC t) (pt xa xb)) 2 (hSc _) (h0S hxa hxb) hς1
  obtain ⟨wm, hwm, hwm'⟩ := exists_isApprox_max (ftaylorSeries ℝ
    (Optimization.regularizedModel (ftaylorSeries ℝ (Constrained.targetMerit objG conC t)
      (pt xa xb)) p cexP.σ₀) s) 2 (hSc (pt xa xb + s)) (by rw [hxs]; exact h0S hya hyb) hς1
  obtain ⟨w₁, hw₁, hw₁'⟩ := exists_isApprox_max (ftaylorSeries ℝ
    (Constrained.targetMerit objG conC t) (pt xa xb + s)) 2 (hSc (pt xa xb + s))
    (by rw [hxs]; exact h0S hya hyb) hς1
  have hj12 : ∀ j ∈ Finset.Icc 1 q, j = 1 ∨ (j = 2 ∧ 2 ≤ q) := fun j hj => by
    have := Finset.mem_Icc.1 hj; omega
  have hgsum : g * (ya ^ 3 / 2 + (ya - yb / 16 - t)) - g * (ya - yb / 16 - t) / 16 ≤
      T₁ / 4 := by
    have : 0 ≤ 1 / 10 ^ 6 * (|ya - xa| + |yb - xb|) ^ 4 / 24 := by positivity
    linarith
  -- order-2 bounds
  have hm2 : Optimization.decrementMeasure ((ftaylorSeries ℝ (Optimization.regularizedModel
      (ftaylorSeries ℝ (Constrained.targetMerit objG conC t) (pt xa xb)) p cexP.σ₀)
        s).taylorDecrement 2) 1 {e | pt xa xb + s + e ∈ boxX} ≤ T₂ / 16 := by
    refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self zero_le_one,
      by rw [hxs]; exact h0S hya hyb⟩ fun d hd => ?_
    have hd1 : ‖d‖ ≤ 1 := mem_closedBall_zero_iff.1 hd.1
    have h2 := modelDecr_two_le hp (σ := cexP.σ₀) (by rw [hσ]; norm_num) (pt xa xb) t hs1 hd1
    have h1 := lin_le (-(ya ^ 3 / 2 + (ya - yb / 16 - t)) - regC p cexP.σ₀ s * (ya - xa))
      ((ya - yb / 16 - t) / 16 - regC p cexP.σ₀ s * (yb - xb)) hd1
    rw [← hΔm, hab0, hab1] at h1
    have h3 : ‖s‖ ^ 3 ≤ (|ya - xa| + |yb - xb|) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hsL 3
    have e : -g * (-(ya ^ 3 / 2 + (ya - yb / 16 - t)) - regC p cexP.σ₀ s * (ya - xa)) +
        -g * ((ya - yb / 16 - t) / 16 - regC p cexP.σ₀ s * (yb - xb)) =
        g * (ya ^ 3 / 2 + (ya - yb / 16 - t)) - g * (ya - yb / 16 - t) / 16 +
          regC p cexP.σ₀ s * (g * (ya - xa) + g * (yb - xb)) := by ring
    rw [e] at h1
    have h4 : cexP.σ₀ * ‖s‖ ^ 3 / 2 ≤ 1 / 10 ^ 6 * (|ya - xa| + |yb - xb|) ^ 3 / 2 := by
      rw [hσ]; gcongr
    linarith
  have hμ2 : Optimization.decrementMeasure ((ftaylorSeries ℝ (Constrained.targetMerit objG conC t)
      (pt xa xb + s)).taylorDecrement 2) 1 {e | pt xa xb + s + e ∈ boxX} ≤ T₁ / 4 := by
    refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self zero_le_one,
      by rw [hxs]; exact h0S hya hyb⟩ fun d hd => ?_
    have hd1 : ‖d‖ ≤ 1 := mem_closedBall_zero_iff.1 hd.1
    have h2 := decr_two_le (pt xa xb + s) d t
    have h1 := lin_le (-(ya ^ 3 / 2 + (ya - yb / 16 - t))) ((ya - yb / 16 - t) / 16) hd1
    rw [← hΔ', hab0', hab1'] at h1
    have e : -g * -(ya ^ 3 / 2 + (ya - yb / 16 - t)) + -g * ((ya - yb / 16 - t) / 16) =
        g * (ya ^ 3 / 2 + (ya - yb / 16 - t)) - g * (ya - yb / 16 - t) / 16 := by ring
    rw [e] at h1
    linarith
  refine callOut_one_step hq1 (by omega) (P := cexP) (fun j hj => ?_)
    hmemx (by rw [hxs]; exact hmemy) (by linarith) (taylorSum_merit hp _ t)
    ⟨0, forall_mem_image.2 fun _ _ => Constrained.targetMerit_nonneg⟩ ?_
    (d₀ := fun j => if j = 1 then pt (-1 / 2) (1 / 2) else w₀) ?_ ⟨1, by simp; omega, ?_⟩
    (dm := fun j => if j = 1 then pt (-g / 2) (-g / 2) else wm) ?_
    (d₁ := fun j => if j = 1 then pt (-g / 2) (-g / 2) else w₁) ?_ ?_
  · rcases hj12 j hj with rfl | ⟨rfl, h2⟩
    · rw [hT]; exact ⟨hT0, hT1⟩
    · rw [hT2 h2]; exact ⟨hT20, hT21⟩
  · -- the model decreases
    rw [Optimization.regularizedModel_def, taylorSum_merit hp, hxs, merit_eq, merit_eq]
    simp only [pt_zero, objG_pt]
    rw [hσ]
    have := reg_le hp (σ := cexP.σ₀) (by rw [hσ]; norm_num) hs1
    have h5 : ‖s‖ ^ 5 ≤ (|ya - xa| + |yb - xb|) ^ 5 := pow_le_pow_left₀ (norm_nonneg _) hsL 5
    rw [hσ] at this
    linarith
  · -- Step 1 at `x`: the witnesses
    intro j hj
    rcases hj12 j hj with rfl | ⟨rfl, -⟩
    · simp only [↓reduceIte]
      refine isApprox_lin (a := -(xa ^ 3 / 2 + (xa - xb / 16 - t))) (b := (xa - xb / 16 - t) / 16)
        (fun d => by rw [decrG, objG_pt]; simp only [pt_zero]) (h0S hxa hxb)
        (norm_pt_le hhalf' hhalf) (hS hxa hxb hhalf' hhalf) ?_
      rw [decrG, objG_pt]
      simp only [pt_zero, pt_one]
      rw [abs_neg, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      linarith
    · simpa using hw₀
  · -- Step 1 fails at `x`
    simp only [↓reduceIte]
    rw [decrG, objG_pt, hς, hT]
    simp only [pt_zero, pt_one]
    norm_num
    linarith
  · -- the model witnesses at `s`
    intro j hj
    rcases hj12 j hj with rfl | ⟨rfl, hq2'⟩
    · simp only [↓reduceIte]
      refine ⟨?_, ?_⟩
      · rw [hς]
        refine isApprox_lin hΔm (by rw [hxs]; exact h0S hya hyb) (norm_pt_le hgw hgw)
          (by rw [hxs]; exact hS hya hyb hgw hgw) ?_
        rw [hΔm, hab0, hab1]
        simp only [pt_zero, pt_one]
        ring_nf
        exact le_rfl
      · rw [hΔm, hς, hθ, hT]
        simp only [pt_zero, pt_one]
        have e : (-(ya ^ 3 / 2 + (ya - yb / 16 - t)) - regC p cexP.σ₀ s * (ya - xa)) * (-g / 2) +
            ((ya - yb / 16 - t) / 16 - regC p cexP.σ₀ s * (yb - xb)) * (-g / 2) =
            (g * (ya ^ 3 / 2 + (ya - yb / 16 - t)) - g * (ya - yb / 16 - t) / 16 +
              regC p cexP.σ₀ s * (g * (ya - xa) + g * (yb - xb))) / 2 := by ring
        rw [e]
        norm_num
        linarith
    · simp only [show (2 : ℕ) ≠ 1 by norm_num, ↓reduceIte]
      refine ⟨hwm, ?_⟩
      rw [hwm', hς, hθ, hT2 hq2']
      norm_num
      linarith
  · -- Step 1 at `x + s`: the witnesses
    intro j hj
    rcases hj12 j hj with rfl | ⟨rfl, -⟩
    · simp only [↓reduceIte]
      rw [hς]
      refine isApprox_lin hΔ' (by rw [hxs]; exact h0S hya hyb) (norm_pt_le hgw hgw)
        (by rw [hxs]; exact hS hya hyb hgw hgw) ?_
      rw [hΔ', hab0', hab1']
      simp only [pt_zero, pt_one]
      ring_nf
      exact le_rfl
    · simpa using hw₁
  · -- Step 1 holds at `x + s`
    intro j hj
    rcases hj12 j hj with rfl | ⟨rfl, h2⟩
    · simp only [↓reduceIte]
      rw [hΔ', hς, hT]
      simp only [pt_zero, pt_one]
      have e : -(ya ^ 3 / 2 + (ya - yb / 16 - t)) * (-g / 2) + (ya - yb / 16 - t) / 16 * (-g / 2) =
          (g * (ya ^ 3 / 2 + (ya - yb / 16 - t)) - g * (ya - yb / 16 - t) / 16) / 2 := by ring
      rw [e]
      norm_num
      linarith
    · simp only [show (2 : ℕ) ≠ 1 by norm_num, ↓reduceIte]
      rw [hw₁', hς, hT2 h2]
      norm_num
      have : 0 ≤ 1 / 10 ^ 6 * (|ya - xa| + |yb - xb|) ^ 3 / 2 := by positivity
      linarith

/-! ### The run -/

/-- The tolerances `ε₀ = u²/2 + u³/2`, `ε₁ = 3u/2`, `ε_j = 1` for `j ≥ 2`. -/
noncomputable def epsS (u : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then u ^ 2 / 2 + u ^ 3 / 2 else if j = 1 then 3 * u / 2 else 1

theorem epsS_zero {u : ℝ} : epsS u 0 = u ^ 2 / 2 + u ^ 3 / 2 := by simp [epsS]

theorem epsS_one {u : ℝ} : epsS u 1 = 3 * u / 2 := by simp [epsS]

theorem epsS_two {u : ℝ} : epsS u 2 = 1 := by simp [epsS]

theorem epsS_pos {u : ℝ} (hu : 0 < u) (j : ℕ) : 0 < epsS u j := by
  unfold epsS; split_ifs <;> positivity

theorem epsS_le_one {u : ℝ} (hu : 0 < u) (hu7 : u ≤ 1 / 7) (j : ℕ) : epsS u j ≤ 1 := by
  unfold epsS; split_ifs <;> nlinarith [pow_pos hu 2, pow_pos hu 3]


section Run

variable (u : ℝ) (M : ℕ)

/-- The overshoot `E_k = (u³/2)(1 - k/(64(M + 1)))` of the `k`-th call below its target. -/
noncomputable def ovS (k : ℕ) : ℝ := u ^ 3 / 2 * (1 - k / (64 * (M + 1)))

/-- The targets `t_k = -ε₀ - u³ (k - 1) + u³ k (k - 1)/(128 (M + 1))`, so that
`t_{k+1} = t_k - 2 E_k`. -/
noncomputable def tgtS (k : ℕ) : ℝ :=
  -(u ^ 2 / 2 + u ^ 3 / 2) - u ^ 3 * ((k : ℝ) - 1) + u ^ 3 * ((k : ℝ) * (k - 1)) / (128 * (M + 1))

/-- The amount `f(x_{M+2}) - t_{M+1} = (3u/4)³/2` of the last call above its target. -/
noncomputable def finS : ℝ := 27 * u ^ 3 / 128

open Classical in
/-- The first coordinate of the point reached by the `k`-th call: `u` for `k ≤ M`, `-3u/4`
for the last call. -/
noncomputable def landA (k : ℕ) : ℝ := if k ≤ M then u else -3 * u / 4

open Classical in
/-- The value `f(x_{k+1}) - t_k`: `-E_k` for `k ≤ M`, `(3u/4)³/2` for the last call. -/
noncomputable def landF (k : ℕ) : ℝ := if k ≤ M then -ovS u M k else finS u

/-- The outer iterates: `x₁ = (0, 0)` and `x_{k+1} = (a_k, 16 (a_k - t_k - F_k))` for `k ≥ 1`,
so that `f(x_{k+1}) = t_k + F_k`. -/
noncomputable def xsS : ℕ → ℝ²
  | 0 => pt 0 0
  | k + 1 => if k = 0 then pt 0 0 else
      pt (landA u M k) (16 * (landA u M k - tgtS u M k - landF u M k))

/-- The Phase-2 sequences: iterates `xsS`, targets `tgtS`, radii `1`, and the `k`-th INNER call
makes one successful iteration from `x_k` to `x_{k+1}`. -/
noncomputable def runS : TPqpSeq 2 := TPqpSeq.oneStep (xsS u M) (tgtS u M)

end Run

section Facts

variable {u : ℝ} {M : ℕ}

theorem tgtS_one : tgtS u M 1 = -(u ^ 2 / 2 + u ^ 3 / 2) := by simp [tgtS]

/-- `t_{k+1} = t_k - 2 E_k`. -/
theorem tgtS_succ (k : ℕ) : tgtS u M (k + 1) = tgtS u M k - 2 * ovS u M k := by
  unfold tgtS ovS
  have : (64 * ((M : ℝ) + 1)) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem xsS_one : xsS u M 1 = pt 0 0 := by simp [xsS]

theorem xsS_succ {k : ℕ} (hk : 1 ≤ k) :
    xsS u M (k + 1) = pt (landA u M k) (16 * (landA u M k - tgtS u M k - landF u M k)) := by
  simp [xsS, show k ≠ 0 by omega]

theorem objG_xsS_succ {k : ℕ} (hk : 1 ≤ k) :
    objG (xsS u M (k + 1)) = tgtS u M k + landF u M k := by
  rw [xsS_succ hk, objG_pt]; ring

theorem landA_of_le {k : ℕ} (hk : k ≤ M) : landA u M k = u := by simp [landA, hk]

theorem landF_of_le {k : ℕ} (hk : k ≤ M) : landF u M k = -ovS u M k := by simp [landF, hk]

theorem landA_last : landA u M (M + 1) = -3 * u / 4 := by simp [landA]

theorem landF_last : landF u M (M + 1) = finS u := by simp [landF]

/-- The iterates `x_{k+1}`, `1 ≤ k ≤ M`. -/
theorem xsS_mid {k : ℕ} (hk1 : 1 ≤ k) (hkM : k ≤ M) :
    xsS u M (k + 1) = pt u (16 * (u - tgtS u M k + ovS u M k)) := by
  rw [xsS_succ hk1, landA_of_le hkM, landF_of_le hkM]; ring_nf

/-- The last iterate `x_{M+2}`. -/
theorem xsS_last : xsS u M (M + 1 + 1) =
    pt (-3 * u / 4) (16 * (-3 * u / 4 - tgtS u M (M + 1) - finS u)) := by
  rw [xsS_succ (by omega), landA_last, landF_last]

/-- `f(x_k) - t_k = E_{k-1}` at the start of the call `k ∈ [2, M + 1]`. -/
theorem objG_start {k : ℕ} (hk1 : 1 ≤ k) (hkM : k ≤ M) :
    objG (xsS u M (k + 1)) - tgtS u M (k + 1) = ovS u M k := by
  rw [objG_xsS_succ hk1, landF_of_le hkM, tgtS_succ]; ring

variable (hu : 0 < u)
include hu

/-- `E_k ≤ u³/2`. -/
theorem ovS_le (k : ℕ) : ovS u M k ≤ u ^ 3 / 2 := by
  unfold ovS
  have : 0 ≤ (k : ℝ) / (64 * (M + 1)) := by positivity
  have : 0 < u ^ 3 / 2 := by positivity
  nlinarith

/-- `E_k ≥ (63/64) u³/2` for `k ≤ M + 1`. -/
theorem le_ovS {k : ℕ} (hk : k ≤ M + 1) : 63 / 64 * (u ^ 3 / 2) ≤ ovS u M k := by
  unfold ovS
  have hN : (0 : ℝ) < 64 * (M + 1) := by positivity
  have : (k : ℝ) / (64 * (M + 1)) ≤ 1 / 64 := by
    rw [div_le_iff₀ hN]
    have : (k : ℝ) ≤ M + 1 := by exact_mod_cast hk
    linarith
  have : 0 < u ^ 3 / 2 := by positivity
  nlinarith

/-- `E_{k-1} - E_k = u³/(128 (M + 1))`. -/
theorem ovS_sub (k : ℕ) : ovS u M k - ovS u M (k + 1) = u ^ 3 / (128 * (M + 1)) := by
  unfold ovS
  have : (64 * ((M : ℝ) + 1)) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- `-ε₀ - u³ (k - 1) ≤ t_k ≤ -ε₀` for `k ∈ [1, M + 1]`. -/
theorem tgtS_mem {k : ℕ} (hk1 : 1 ≤ k) (hkM : k ≤ M + 1) :
    -(u ^ 2 / 2 + u ^ 3 / 2) - u ^ 3 * ((k : ℝ) - 1) ≤ tgtS u M k ∧
      tgtS u M k ≤ -(u ^ 2 / 2 + u ^ 3 / 2) := by
  unfold tgtS
  have hN : (0 : ℝ) < 128 * (M + 1) := by positivity
  have hK1 : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hKM : (k : ℝ) ≤ M + 1 := by exact_mod_cast hkM
  have hu3 : 0 < u ^ 3 := by positivity
  have h0 : 0 ≤ u ^ 3 * ((k : ℝ) * (k - 1)) / (128 * (M + 1)) := by
    apply div_nonneg _ hN.le
    apply mul_nonneg hu3.le
    nlinarith
  have h1 : u ^ 3 * ((k : ℝ) * (k - 1)) / (128 * (M + 1)) ≤ u ^ 3 * ((k : ℝ) - 1) := by
    rw [div_le_iff₀ hN]
    have : ((k : ℝ) * (k - 1)) ≤ ((k : ℝ) - 1) * (128 * (M + 1)) := by nlinarith
    nlinarith
  constructor <;> linarith

end Facts

/-! ### The INNER calls of the run are ARqp-SC runs -/

/-- `‖r((a, b), t)‖² = (a²/2)² + (a - b/16 - t)²`. -/
theorem resid_sq_pt (a b t : ℝ) :
    Constrained.targetResidual objG conC t (pt a b) ^ 2 =
      (a ^ 2 / 2) ^ 2 + (a - b / 16 - t) ^ 2 := by
  rw [Constrained.targetResidual_sq, norm_conC, objG_pt, pt_zero]

/-- Step 1 fails at the start of the calls `k ≥ 2`. -/
theorem num_fail {u E R : ℝ} (hu : 0 < u) (hu' : u ≤ 1 / 200) (hE0 : 0 ≤ E)
    (hE2 : E ≤ u ^ 3 / 2) (hRhi : R ≤ u ^ 2 / 2 + E) :
    1 / 2 * R * (3 * u / 2) < u ^ 3 / 2 + E + E / 16 := by
  have hu2 : u ^ 2 ≤ u / 200 := by nlinarith
  have : R * u ≤ (u ^ 2 / 2 + u ^ 3 / 2) * u := mul_le_mul_of_nonneg_right (by linarith) hu.le
  nlinarith [pow_pos hu 3]

/-- The arithmetic of the middle calls. -/
theorem num_mid {u E E' R : ℝ} (hu : 0 < u) (hu' : u ≤ 1 / 200)
    (hE1 : 63 / 64 * (u ^ 3 / 2) ≤ E) (hE2 : E ≤ u ^ 3 / 2) (hE1' : 63 / 64 * (u ^ 3 / 2) ≤ E')
    (hE2' : E' ≤ u ^ 3 / 2) (hEE : u ^ 6 / 4 ≤ E - E') (hRlo : u ^ 2 / 2 ≤ R)
    (hRhi : R ≤ u ^ 2 / 2 + E) :
    1 / 2 * R * (3 * u / 2) < u ^ 3 / 2 + E + E / 16 ∧
    u ^ 4 / 8 + (-E') ^ 2 / 2 + 1 / 10 ^ 6 * (16 * (E + E')) ^ 5 / 120 <
      u ^ 4 / 8 + E ^ 2 / 2 ∧
    1 * (u ^ 3 / 2 + -E') - 1 * (-E') / 16 + 1 / 10 ^ 6 * (16 * (E + E')) ^ 4 / 24 ≤
      1 / 2 * R * (3 * u / 2) / 4 := by
  have hu2 : u ^ 2 ≤ u / 200 := by nlinarith
  have hu3p : 0 < u ^ 3 := by positivity
  have hS0 : 0 < E + E' := by linarith
  have hS1 : E + E' ≤ u ^ 3 := by linarith
  have hS4 : (E + E') ^ 4 ≤ (u ^ 3) ^ 4 := pow_le_pow_left₀ hS0.le hS1 4
  have hu6 : (u ^ 3) ^ 4 ≤ u ^ 6 / 1000 := by
    have : u ^ 6 ≤ 1 / 1000 := by
      have : u ^ 6 ≤ (1 / 200) ^ 6 := pow_le_pow_left₀ hu.le hu' 6
      linarith [show ((1 : ℝ) / 200) ^ 6 ≤ 1 / 1000 by norm_num]
    have e : (u ^ 3) ^ 4 = u ^ 6 * u ^ 6 := by ring
    rw [e]; nlinarith [pow_pos hu 6]
  refine ⟨?_, ?_, ?_⟩
  · have : R * u ≤ (u ^ 2 / 2 + u ^ 3 / 2) * u := mul_le_mul_of_nonneg_right (by linarith) hu.le
    nlinarith
  · have e5 : (16 * (E + E')) ^ 5 = 1048576 * (E + E') ^ 4 * (E + E') := by ring
    have h1 : (E + E') ^ 4 * (E + E') ≤ u ^ 6 / 1000 * (E + E') :=
      mul_le_mul_of_nonneg_right (hS4.trans hu6) hS0.le
    have h2 : (u ^ 6 / 4) * (E + E') ≤ (E - E') * (E + E') :=
      mul_le_mul_of_nonneg_right hEE hS0.le
    have h3 : 0 < u ^ 6 * (E + E') := by positivity
    rw [e5]
    nlinarith
  · have e4 : (16 * (E + E')) ^ 4 = 65536 * (E + E') ^ 4 := by ring
    have h6 : u ^ 6 ≤ u ^ 3 / 1000 := by
      have : u ^ 3 ≤ 1 / 1000 := by nlinarith
      nlinarith
    have : u ^ 2 / 2 * u ≤ R * u := mul_le_mul_of_nonneg_right hRlo hu.le
    rw [e4]
    nlinarith

/-- The arithmetic of the last call. -/
theorem num_last {u E R : ℝ} (hu : 0 < u) (hu' : u ≤ 1 / 200)
    (hE1 : 63 / 64 * (u ^ 3 / 2) ≤ E) (hE2 : E ≤ u ^ 3 / 2) (hRlo : u ^ 2 / 2 ≤ R) :
    (-3 * u / 4) ^ 4 / 8 + (27 * u ^ 3 / 128) ^ 2 / 2 +
      1 / 10 ^ 6 * (7 * u / 4 + 16 * (7 * u / 4 - E + 27 * u ^ 3 / 128)) ^ 5 / 120 <
      u ^ 4 / 8 + E ^ 2 / 2 ∧
    -1 * ((-3 * u / 4) ^ 3 / 2 + 27 * u ^ 3 / 128) - -1 * (27 * u ^ 3 / 128) / 16 +
      1 / 10 ^ 6 * (7 * u / 4 + 16 * (7 * u / 4 - E + 27 * u ^ 3 / 128)) ^ 4 / 24 ≤
      1 / 2 * R * (3 * u / 2) / 4 := by
  have hu2 : u ^ 2 ≤ u / 200 := by nlinarith
  have hu3p : 0 < u ^ 3 := by positivity
  have hu3 : u ^ 3 ≤ u / 40000 := by nlinarith
  have hL0 : 0 ≤ 7 * u / 4 + 16 * (7 * u / 4 - E + 27 * u ^ 3 / 128) := by nlinarith
  have hL1 : 7 * u / 4 + 16 * (7 * u / 4 - E + 27 * u ^ 3 / 128) ≤ 30 * u := by nlinarith
  have hL5 := pow_le_pow_left₀ hL0 hL1 5
  have hL4 := pow_le_pow_left₀ hL0 hL1 4
  have e5 : (30 * u) ^ 5 = 24300000 * u ^ 5 := by ring
  have e4 : (30 * u) ^ 4 = 810000 * u ^ 4 := by ring
  have hu5 : u ^ 5 ≤ u ^ 4 / 200 := by nlinarith [pow_pos hu 4]
  have hu4 : u ^ 4 ≤ u ^ 3 / 200 := by nlinarith [pow_pos hu 3]
  have hu6 : u ^ 6 ≤ u ^ 4 / 40000 := by nlinarith [pow_pos hu 4]
  have hE0 : 0 ≤ E := by linarith
  refine ⟨?_, ?_⟩
  · have e1 : (-3 * u / 4) ^ 4 / 8 + (27 * u ^ 3 / 128) ^ 2 / 2 =
        81 / 2048 * u ^ 4 + 729 / 32768 * u ^ 6 := by ring
    rw [e1]
    nlinarith
  · have e1 : -1 * ((-3 * u / 4) ^ 3 / 2 + 27 * u ^ 3 / 128) - -1 * (27 * u ^ 3 / 128) / 16 =
        27 / 2048 * u ^ 3 := by ring
    rw [e1]
    have : u ^ 2 / 2 * u ≤ R * u := mul_le_mul_of_nonneg_right hRlo hu.le
    nlinarith

/-- The order-`2` tolerance `T₂ = ‖r‖/2` dominates (`T₁/4 + σ₀ L³/2 ≤ T₂/16`). -/
theorem num_T2 {u R L : ℝ} (hu : 0 < u) (hu' : u ≤ 1 / 200) (hR : u ^ 2 / 2 ≤ R) (hL0 : 0 ≤ L)
    (hL : L ≤ 30 * u) :
    1 / 2 * R * (3 * u / 2) / 4 + 1 / 10 ^ 6 * L ^ 3 / 2 ≤ 1 / 2 * R * 1 / 16 := by
  have h3 : L ^ 3 ≤ (30 * u) ^ 3 := pow_le_pow_left₀ hL0 hL 3
  have e : (30 * u) ^ 3 = 27000 * u ^ 3 := by ring
  have hR0 : 0 ≤ R := le_trans (by positivity) hR
  have hRu : u * R ≤ R / 200 := by nlinarith
  have hu3 : u ^ 3 ≤ u ^ 2 / 200 := by nlinarith [pow_pos hu 2]
  nlinarith

/-- The tolerances `(1/2) ‖r(x_k, t_k)‖ ε` of the `k`-th call (`β = 1/2`). -/
noncomputable abbrev callTol (u : ℝ) (M k : ℕ) : ℕ → ℝ := fun j =>
  1 / 2 * Constrained.targetResidual objG conC (tgtS u M k) (xsS u M k) * epsS u j

section Calls

variable {u : ℝ} {M : ℕ} (hu : 0 < u) (hu' : u ≤ 1 / 200) (hM : u ^ 3 * M ≤ 1 / 64)
  (hM1 : 1 ≤ M) {q : ℕ} (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
include hu hu' hM hM1 hq1 hq2

omit hM in
/-- **The first call** (from `(0, 0)` with `f - t₁ = ε₀` to `(u, ·)` with `f - t₁ = -E₁`) is a
one-step ARqp-SC call. -/
theorem callOut_first {p : ℕ} (hp : 4 ≤ p) :
    IsARqpSCCallOut (Constrained.targetMerit objG conC (tgtS u M 1)) boxX p q cexP
      (callTol u M 1) (fun i => if i = 0 then xsS u M 1 else xsS u M (1 + 1)) 1
      (fun _ => True) (fun _ => 1) := by
  set e0 := u ^ 2 / 2 + u ^ 3 / 2 with he0
  set E := ovS u M 1 with hE
  have hE1 : 63 / 64 * (u ^ 3 / 2) ≤ E := le_ovS hu (by omega)
  have hE2 : E ≤ u ^ 3 / 2 := ovS_le hu 1
  have ht : tgtS u M 1 = -e0 := tgtS_one
  have hx2 : xsS u M (1 + 1) = pt u (16 * (u + e0 + E)) := by
    rw [xsS_mid le_rfl hM1, ht, ← hE]; congr 1; ring
  have hR : Constrained.targetResidual objG conC (tgtS u M 1) (xsS u M 1) = e0 := by
    have hsq := resid_sq_pt 0 0 (tgtS u M 1)
    rw [← xsS_one (u := u) (M := M), ht] at hsq
    have h0 := Constrained.targetResidual_nonneg (f := objG) (c := conC) (t := tgtS u M 1)
      (x := xsS u M 1)
    rw [ht] at h0 ⊢
    have : 0 < e0 := by positivity
    nlinarith [sq_nonneg (Constrained.targetResidual objG conC (-e0) (xsS u M 1) - e0)]
  have hT : callTol u M 1 1 = 1 / 2 * e0 * (3 * u / 2) := by
    simp only [callTol, hR, epsS_one]
  have hu2 : u ^ 2 ≤ u / 200 := by nlinarith
  have hu3 : u ^ 3 ≤ u ^ 2 / 200 := by nlinarith
  have hu4 : u ^ 4 ≤ u ^ 3 / 200 := by nlinarith
  have hu3p : 0 < u ^ 3 := by positivity
  have hW0 : 0 ≤ 16 * (u + e0 + E) := by
    have : 0 ≤ E := by linarith
    positivity
  have hW1 : 16 * (u + e0 + E) ≤ 17 * u := by nlinarith
  have hL : |u - 0| + |16 * (u + e0 + E) - 0| ≤ 18 * u := by
    rw [sub_zero, sub_zero, abs_of_pos hu, abs_of_nonneg hW0]; linarith
  have hL0 : 0 ≤ |u - 0| + |16 * (u + e0 + E) - 0| := by positivity
  have hL5 : (|u - 0| + |16 * (u + e0 + E) - 0|) ^ 5 ≤ (18 * u) ^ 5 :=
    pow_le_pow_left₀ hL0 hL 5
  have hL4 : (|u - 0| + |16 * (u + e0 + E) - 0|) ^ 4 ≤ (18 * u) ^ 4 :=
    pow_le_pow_left₀ hL0 hL 4
  have hFy : u - 16 * (u + e0 + E) / 16 - tgtS u M 1 = -E := by rw [ht]; ring
  have hFx : (0 : ℝ) - 0 / 16 - tgtS u M 1 = e0 := by rw [ht]; ring
  rw [xsS_one, hx2]
  have hT2 : 2 ≤ q → callTol u M 1 2 = 1 / 2 * e0 * 1 := fun _ => by
    simp only [callTol, hR, epsS_two]
  have he0lo : u ^ 2 / 2 ≤ e0 := by linarith
  refine callOut_cex hp hq1 hq2 (t := tgtS u M 1) (g := 1) hT hT2 (by positivity)
    (by linarith) (num_T2 hu hu' he0lo hL0 (by linarith)) (by norm_num) (by norm_num)
    (by rw [abs_of_pos hu]; linarith) (by rw [abs_of_nonneg hW0]; linarith) (by linarith)
    (by positivity) (by nlinarith) (by rw [hFx]; positivity) le_rfl ?_ ?_ (Or.inl rfl) ?_ ?_
    (by linarith) (by linarith) ?_
  · rw [hFx]; nlinarith
  · rw [hFy, hFx]
    have h5 : (18 * u) ^ 5 = 1889568 * u ^ 5 := by ring
    have hE6 : E ^ 2 ≤ u ^ 6 / 4 := by nlinarith
    have he2 : e0 ^ 2 = u ^ 4 / 4 + u ^ 5 / 2 + u ^ 6 / 4 := by rw [he0]; ring
    have : (0 : ℝ) ^ 4 = 0 := by norm_num
    nlinarith
  · rw [hFy]; linarith
  · rw [hFy]; linarith
  · rw [hFy]
    have h4 : (18 * u) ^ 4 = 104976 * u ^ 4 := by ring
    nlinarith

omit hq1 hq2 in
/-- `u³ (M + 1) ≤ 1/32`, so `E_k - E_{k+1} = u³/(128 (M + 1)) ≥ u⁶/4`. -/
theorem ovS_sub_ge : u ^ 6 / 4 ≤ u ^ 3 / (128 * (M + 1)) := by
  have hN : (0 : ℝ) < 128 * (M + 1) := by positivity
  rw [le_div_iff₀ hN]
  have hu3 : u ^ 3 ≤ 1 / 64 := by nlinarith [pow_pos hu 2]
  have : u ^ 3 * ((M : ℝ) + 1) ≤ 1 / 32 := by nlinarith
  nlinarith [pow_pos hu 3]


/-- **The middle calls** `k = j + 1 ∈ [2, M]` (from `(u, ·)` with `f - t_k = E_j` to `(u, ·)`
with `f - t_k = -E_{j+1}`) are one-step ARqp-SC calls. -/
theorem callOut_mid {p : ℕ} (hp : 4 ≤ p) {j : ℕ} (hj1 : 1 ≤ j) (hjM : j + 1 ≤ M) :
    IsARqpSCCallOut (Constrained.targetMerit objG conC (tgtS u M (j + 1))) boxX p q cexP
      (callTol u M (j + 1)) (fun i => if i = 0 then xsS u M (j + 1) else xsS u M (j + 1 + 1)) 1
      (fun _ => True) (fun _ => 1) := by
  set E := ovS u M j with hE
  set E' := ovS u M (j + 1) with hE'
  set t := tgtS u M j with ht
  have hE1 : 63 / 64 * (u ^ 3 / 2) ≤ E := le_ovS hu (by omega)
  have hE2 : E ≤ u ^ 3 / 2 := ovS_le hu j
  have hE1' : 63 / 64 * (u ^ 3 / 2) ≤ E' := le_ovS hu (by omega)
  have hE2' : E' ≤ u ^ 3 / 2 := ovS_le hu (j + 1)
  have hEE : u ^ 6 / 4 ≤ E - E' := by rw [hE, hE', ovS_sub hu]; exact ovS_sub_ge hu hu' hM hM1
  have ht' : tgtS u M (j + 1) = t - 2 * E := tgtS_succ j
  obtain ⟨htlo, hthi⟩ := tgtS_mem hu (u := u) (M := M) hj1 (by omega)
  rw [← ht] at htlo hthi
  have hjM' : u ^ 3 * ((j : ℝ) - 1) ≤ 1 / 64 := by
    have : ((j : ℝ) - 1) ≤ M := by
      have : (j : ℝ) ≤ M := by exact_mod_cast (show j ≤ M by omega)
      linarith
    nlinarith [pow_pos hu 3]
  set A := 16 * (u - t + E) with hA
  have hx1 : xsS u M (j + 1) = pt u A := by rw [xsS_mid hj1 (by omega)]
  have hx2 : xsS u M (j + 1 + 1) = pt u (A + 16 * (E + E')) := by
    rw [xsS_mid (by omega) hjM, ht', hA, ← hE']; congr 1; ring
  have hFx : u - A / 16 - tgtS u M (j + 1) = E := by rw [ht', hA]; ring
  have hFy : u - (A + 16 * (E + E')) / 16 - tgtS u M (j + 1) = -E' := by rw [ht', hA]; ring
  have hu2 : u ^ 2 ≤ u / 200 := by nlinarith
  have hu2p : 0 ≤ u ^ 2 := by positivity
  have hu3p : 0 < u ^ 3 := by positivity
  have hu3s : u ^ 3 ≤ 1 / 1000 := by nlinarith
  have hR := resid_sq_pt u A (tgtS u M (j + 1))
  rw [hFx] at hR
  obtain ⟨hRlo, hRhi⟩ := resid_bounds Constrained.targetResidual_nonneg hR (by positivity)
    (by linarith)
  set R := Constrained.targetResidual objG conC (tgtS u M (j + 1)) (pt u A) with hRdef
  have hT : callTol u M (j + 1) (1 : ℕ) = 1 / 2 * R * (3 * u / 2) := by
    simp only [callTol, hx1, epsS_one, ← hRdef]
  have hA0 : 0 ≤ A := by rw [hA]; linarith
  have hA1 : A ≤ 3 / 8 := by rw [hA]; linarith
  have hS0 : 0 ≤ E + E' := by linarith
  have hL : |u - u| + |A + 16 * (E + E') - A| = 16 * (E + E') := by
    rw [sub_self, abs_zero, zero_add, add_sub_cancel_left, abs_of_nonneg (by linarith)]
  obtain ⟨n1, n2, n3⟩ := num_mid hu hu' hE1 hE2 hE1' hE2' hEE hRlo hRhi
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hRlo
  have hT0 : 0 < 1 / 2 * R * (3 * u / 2) := by positivity
  have hT1 : 1 / 2 * R * (3 * u / 2) ≤ 1 := by
    have : R * u ≤ 1 * 1 := mul_le_mul (by linarith) (by linarith) hu.le zero_le_one
    linarith
  rw [hx1, hx2]
  have hT2 : 2 ≤ q → callTol u M (j + 1) 2 = 1 / 2 * R * 1 := fun _ => by
    rw [callTol, epsS_two, hx1]
  have hu3u : u ^ 3 ≤ u := pow_le_of_le_one hu.le (by linarith) (by norm_num)
  exact callOut_cex hp hq1 hq2 (t := tgtS u M (j + 1)) (g := 1) hT hT2 (by positivity)
    (by linarith) (num_T2 hu hu' hRlo (by rw [hL]; linarith) (by rw [hL]; linarith))
    (by rw [abs_of_pos hu]; linarith)
    (by rw [abs_of_nonneg hA0]; linarith) (by rw [abs_of_pos hu]; linarith)
    (by rw [abs_of_nonneg (by linarith)]; linarith) (by rw [hL]; linarith)
    hT0 hT1 (by rw [hFx]; linarith) hu.le (by rw [hFx]; exact n1)
    (by rw [hFy, hFx, hL]; exact n2) (Or.inl rfl) (by rw [hFy]; linarith) (by rw [hFy]; linarith)
    (by rw [sub_self]; linarith) (by linarith) (by rw [hFy, hL]; exact n3)

/-- **The last call** `k = M + 1` (from `(u, ·)` with `f - t_k = E_M` to `(-3u/4, ·)` with
`f - t_k = (3u/4)³/2`, a point where `∇μ(·, t_k)` vanishes in its first coordinate) is a
one-step ARqp-SC call. -/
theorem callOut_last {p : ℕ} (hp : 4 ≤ p) :
    IsARqpSCCallOut (Constrained.targetMerit objG conC (tgtS u M (M + 1))) boxX p q cexP
      (callTol u M (M + 1)) (fun i => if i = 0 then xsS u M (M + 1) else xsS u M (M + 1 + 1)) 1
      (fun _ => True) (fun _ => 1) := by
  set E := ovS u M M with hE
  set t := tgtS u M M with ht
  have hE1 : 63 / 64 * (u ^ 3 / 2) ≤ E := le_ovS hu (by omega)
  have hE2 : E ≤ u ^ 3 / 2 := ovS_le hu M
  have ht' : tgtS u M (M + 1) = t - 2 * E := tgtS_succ M
  obtain ⟨htlo, hthi⟩ := tgtS_mem hu (u := u) (M := M) hM1 (by omega)
  rw [← ht] at htlo hthi
  have hjM' : u ^ 3 * ((M : ℝ) - 1) ≤ 1 / 64 := by nlinarith [pow_pos hu 3]
  set A := 16 * (u - t + E) with hA
  have hx1 : xsS u M (M + 1) = pt u A := by rw [xsS_mid hM1 le_rfl]
  have hx2 : xsS u M (M + 1 + 1) =
      pt (-3 * u / 4) (A + 16 * (-(7 * u / 4) + E - 27 * u ^ 3 / 128)) := by
    rw [xsS_last, ht', hA, finS]; congr 1; ring
  have hFx : u - A / 16 - tgtS u M (M + 1) = E := by rw [ht', hA]; ring
  have hFy : -3 * u / 4 - (A + 16 * (-(7 * u / 4) + E - 27 * u ^ 3 / 128)) / 16 -
      tgtS u M (M + 1) = 27 * u ^ 3 / 128 := by rw [ht', hA]; ring
  have hu2 : u ^ 2 ≤ u / 200 := by nlinarith
  have hu2p : 0 ≤ u ^ 2 := by positivity
  have hu3p : 0 < u ^ 3 := by positivity
  have hu3s : u ^ 3 ≤ 1 / 1000 := by nlinarith
  have hu3u : u ^ 3 ≤ u / 40000 := by nlinarith
  have hR := resid_sq_pt u A (tgtS u M (M + 1))
  rw [hFx] at hR
  obtain ⟨hRlo, hRhi⟩ := resid_bounds Constrained.targetResidual_nonneg hR (by positivity)
    (by linarith)
  set R := Constrained.targetResidual objG conC (tgtS u M (M + 1)) (pt u A) with hRdef
  have hT : callTol u M (M + 1) (1 : ℕ) = 1 / 2 * R * (3 * u / 2) := by
    simp only [callTol, hx1, epsS_one, ← hRdef]
  have hA0 : 0 ≤ A := by rw [hA]; linarith
  have hA1 : A ≤ 3 / 8 := by rw [hA]; linarith
  have hL : |-3 * u / 4 - u| + |A + 16 * (-(7 * u / 4) + E - 27 * u ^ 3 / 128) - A| =
      7 * u / 4 + 16 * (7 * u / 4 - E + 27 * u ^ 3 / 128) := by
    rw [add_sub_cancel_left, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    ring
  obtain ⟨n2, n3⟩ := num_last hu hu' hE1 hE2 hRlo
  have n1 := num_fail hu hu' (by linarith) hE2 hRhi
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hRlo
  have hT0 : 0 < 1 / 2 * R * (3 * u / 2) := by positivity
  have hT1 : 1 / 2 * R * (3 * u / 2) ≤ 1 := by
    have : R * u ≤ 1 * 1 := mul_le_mul (by linarith) (by linarith) hu.le zero_le_one
    linarith
  rw [hx1, hx2]
  have hT2 : 2 ≤ q → callTol u M (M + 1) 2 = 1 / 2 * R * 1 := fun _ => by
    rw [callTol, epsS_two, hx1]
  have hLb : 7 * u / 4 + 16 * (7 * u / 4 - E + 27 * u ^ 3 / 128) ≤ 30 * u := by linarith
  exact callOut_cex hp hq1 hq2 (t := tgtS u M (M + 1)) (g := -1) hT hT2 (by positivity)
    (by linarith) (num_T2 hu hu' hRlo (by rw [hL]; linarith) (by rw [hL]; exact hLb))
    (by rw [abs_of_pos hu]; linarith)
    (by rw [abs_of_nonneg hA0]; linarith) (by rw [abs_of_nonpos (by linarith)]; linarith)
    (by rw [abs_le]; constructor <;> linarith) (by rw [hL]; linarith)
    hT0 hT1 (by rw [hFx]; linarith) hu.le (by rw [hFx]; exact n1)
    (by rw [hFy, hFx, hL]; exact n2) (Or.inr rfl) (by rw [hFy]; ring_nf; exact le_rfl)
    (by rw [hFy]; linarith) (by linarith) (by linarith) (by rw [hFy, hL]; exact n3)

/-- **Every INNER call `k ∈ [1, M + 1]` of the run is a one-step ARqp-SC call.** -/
theorem callOut_run {p : ℕ} (hp : 4 ≤ p) {k : ℕ} (hk1 : 1 ≤ k) (hkM : k ≤ M + 1) :
    IsARqpSCCallOut (Constrained.targetMerit objG conC (tgtS u M k)) boxX p q cexP
      (callTol u M k) (fun i => if i = 0 then xsS u M k else xsS u M (k + 1)) 1
      (fun _ => True) (fun _ => 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · exact callOut_first hu hu' hM1 hq1 hq2 hp
  rcases Nat.lt_or_ge j M with hjM | hjM
  · exact callOut_mid hu hu' hM hM1 hq1 hq2 hp hj hjM
  · obtain rfl : j = M := by omega
    exact callOut_last hu hu' hM hM1 hq1 hq2 hp

end Calls

/-! ### The outer run -/

section Outer

variable {u : ℝ} {M : ℕ} (hu : 0 < u) (hu' : u ≤ 1 / 200) (hM : u ^ 3 * M ≤ 1 / 64)
  (hM1 : 1 ≤ M) {q : ℕ} (hq1 : 1 ≤ q) (hq2 : q ≤ 2)

include hu hu' hM in
/-- The iterates `x_k`, `k ∈ [1, M + 2]`, lie in `[-1/2, 1/2]²`, hence in `X`. -/
theorem xsS_mem {k : ℕ} (hk1 : 1 ≤ k) (hkM : k ≤ M + 2) : xsS u M k ∈ boxX := by
  have hu2 : u ^ 2 ≤ u / 200 := by nlinarith
  have hu3p : 0 < u ^ 3 := by positivity
  have hu3s : u ^ 3 ≤ 1 / 1000 := by nlinarith
  have hu2p : 0 ≤ u ^ 2 := by positivity
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [xsS_one]; exact pt_mem (by norm_num) (by norm_num)
  have hE1 : 63 / 64 * (u ^ 3 / 2) ≤ ovS u M j := le_ovS hu (by omega)
  have hE2 : ovS u M j ≤ u ^ 3 / 2 := ovS_le hu j
  obtain ⟨htlo, hthi⟩ := tgtS_mem hu (u := u) (M := M) hj (by omega)
  have hjM' : u ^ 3 * ((j : ℝ) - 1) ≤ 1 / 64 := by
    have : ((j : ℝ) - 1) ≤ M := by
      have : (j : ℝ) ≤ M + 1 := by exact_mod_cast (show j ≤ M + 1 by omega)
      linarith
    nlinarith
  rcases Nat.lt_or_ge j (M + 1) with hjM | hjM
  · rw [xsS_mid hj (by omega)]
    exact pt_mem (by rw [abs_of_pos hu]; linarith)
      (by rw [abs_le]; constructor <;> linarith)
  · obtain rfl : j = M + 1 := by omega
    rw [xsS_last, finS]
    exact pt_mem (by rw [abs_le]; constructor <;> linarith)
      (by rw [abs_le]; constructor <;> linarith)

omit hM hM1 in
include hu hu' in
/-- `θ ε₀ ≤ u²/4 + u³/4 ≤ 9u²/32` for `θ = 1/2`. -/
theorem theta_eps_le' : 1 / 2 * epsS u 0 ≤ 9 * u ^ 2 / 32 := by
  rw [epsS_zero]; nlinarith [pow_pos hu 2]

include hu hu' in
/-- `‖r(x_{k+1}, t_k)‖ ≥ θ ε₀` for every call `k ∈ [1, M + 1]`: no call is in `𝒦_a`. -/
theorem resid_end_ge {k : ℕ} (hk1 : 1 ≤ k) :
    1 / 2 * epsS u 0 ≤ Constrained.targetResidual objG conC (tgtS u M k) (xsS u M (k + 1)) := by
  have hθ := theta_eps_le' hu hu'
  have h := Constrained.norm_le_targetResidual (f := objG) (c := conC) (t := tgtS u M k)
    (x := xsS u M (k + 1))
  have h' : ‖conC (xsS u M (k + 1))‖ = landA u M k ^ 2 / 2 := by
    rw [norm_conC, xsS_succ hk1, pt_zero]
  have hA2 : 9 * u ^ 2 / 32 ≤ landA u M k ^ 2 / 2 := by
    unfold landA; split_ifs
    · nlinarith [pow_pos hu 2]
    · nlinarith [pow_pos hu 2]
  linarith

include hu hu' in
/-- `‖r(x_k, t_k)‖ ≥ θ ε₀` at the start of every call `k ∈ [1, M + 1]`. -/
theorem resid_start_ge {k : ℕ} (hk1 : 1 ≤ k) (hkM : k ≤ M + 1) :
    1 / 2 * epsS u 0 ≤ Constrained.targetResidual objG conC (tgtS u M k) (xsS u M k) := by
  have hθ := theta_eps_le' hu hu'
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have h := Constrained.abs_sub_le_targetResidual (f := objG) (c := conC) (t := tgtS u M (0 + 1))
      (x := xsS u M (0 + 1))
    have e : objG (xsS u M (0 + 1)) - tgtS u M (0 + 1) = epsS u 0 := by
      rw [zero_add, xsS_one, objG_pt, tgtS_one, epsS_zero]; ring
    rw [e, abs_of_pos (epsS_pos hu 0)] at h
    have := epsS_pos hu 0
    linarith
  · have h := Constrained.norm_le_targetResidual (f := objG) (c := conC) (t := tgtS u M (j + 1))
      (x := xsS u M (j + 1))
    have h' : ‖conC (xsS u M (j + 1))‖ = u ^ 2 / 2 := by
      rw [norm_conC, xsS_mid hj (by omega), pt_zero]
    nlinarith [pow_pos hu 2]

include hu hu' in
/-- No outer iteration is in `𝒦_a`. -/
theorem not_isKa {k : ℕ} (hk1 : 1 ≤ k) : ¬ (runS u M).IsKa objG conC (1 / 2) (epsS u) k :=
  not_lt.2 (resid_end_ge hu hu' hk1)

include hu hu' in
/-- The outer iterations `k ∈ [1, M]` are in `𝒦_b`. -/
theorem isKb {k : ℕ} (hk1 : 1 ≤ k) (hkM : k ≤ M) :
    (runS u M).IsKb objG conC (1 / 2) (epsS u) k := by
  refine ⟨resid_end_ge hu hu' hk1, ?_⟩
  change objG (xsS u M (k + 1)) < tgtS u M k
  rw [objG_xsS_succ hk1, landF_of_le hkM]
  have := le_ovS hu (M := M) (k := k) (by omega)
  have : 0 < u ^ 3 := by positivity
  linarith

include hu in
/-- The outer iteration `M + 1` is not in `𝒦_b`: `f(x_{M+2}) > t_{M+1}`. -/
theorem not_isKb_last : ¬ (runS u M).IsKb objG conC (1 / 2) (epsS u) (M + 1) := by
  intro h
  have h2 := h.2
  change objG (xsS u M (M + 1 + 1)) < tgtS u M (M + 1) at h2
  rw [objG_xsS_succ (by omega), landF_last, finS] at h2
  have : 0 < u ^ 3 := by positivity
  linarith

include hu hu' hM hq1 in
/-- **(14.3.34) fails at `(x_{k+1}, t_{k+1})`** for `k ∈ [1, M]`: along `-e₁` the decrease is
`u³/2 + E_k > ε₁ ‖r(x_{k+1}, t_{k+1})‖`. -/
theorem not_meritCrit_new {k : ℕ} (hk1 : 1 ≤ k) (hkM : k ≤ M) :
    ¬ meritCrit objG conC boxX q (epsS u) (tgtS u M (k + 1)) (xsS u M (k + 1)) (fun _ => 1) := by
  intro h
  have h1 := h 1 (Finset.mem_Icc.2 ⟨le_rfl, hq1⟩)
  simp only [one_pow, mul_one, Nat.factorial_one, Nat.cast_one, div_one] at h1
  have hmem := xsS_mem hu hu' hM (k := k + 1) (by omega) (by omega)
  have hx : xsS u M (k + 1) = pt u (16 * (u - tgtS u M k + ovS u M k)) := xsS_mid hk1 hkM
  have hS : pt (-1) 0 ∈ {d | xsS u M (k + 1) + d ∈ boxX} := by
    simp only [mem_ofPred_eq]
    rw [hx] at hmem ⊢
    rw [pt_add]
    simp only [pt_zero, pt_one, add_zero]
    obtain ⟨-, h2⟩ := hmem
    simp only [pt_one] at h2
    exact pt_mem (by rw [abs_le]; constructor <;> linarith) h2
  have hd : pt (-1) 0 ∈ closedBall (0 : ℝ²) 1 := by
    rw [mem_closedBall_zero_iff]
    exact (norm_pt_le_add _ _).trans (by norm_num)
  have hlow := Optimization.taylorDecrement_le_taylorMeasure
    (ftaylorSeries ℝ (Constrained.targetMerit objG conC (tgtS u M (k + 1))) (xsS u M (k + 1))) 1
    (δ := 1) (d := pt (-1) 0) ⟨hd, hS⟩
  have hx0 : xsS u M (k + 1) 0 = u := by rw [hx, pt_zero]
  rw [decrG, objG_start hk1 hkM] at hlow
  simp only [pt_zero, pt_one, hx0] at hlow
  rw [epsS_one] at h1
  have hE1 := le_ovS hu (M := M) (k := k) (by omega)
  have hE2 := ovS_le hu (M := M) k
  have hsq := resid_sq_pt u (16 * (u - tgtS u M k + ovS u M k)) (tgtS u M (k + 1))
  have hF : u - 16 * (u - tgtS u M k + ovS u M k) / 16 - tgtS u M (k + 1) = ovS u M k := by
    rw [tgtS_succ]; ring
  rw [hF] at hsq
  obtain ⟨-, hRhi⟩ := resid_bounds Constrained.targetResidual_nonneg hsq (by positivity)
    (by linarith)
  rw [← hx] at hRhi
  have hu2 : u ^ 2 ≤ u / 200 := by nlinarith
  have : 3 * u / 2 * Constrained.targetResidual objG conC (tgtS u M (k + 1)) (xsS u M (k + 1)) ≤
      3 * u / 2 * (u ^ 2 / 2 + ovS u M k) := by gcongr
  have : u * ovS u M k ≤ u * (u ^ 3 / 2) := mul_le_mul_of_nonneg_left hE2 hu.le
  nlinarith [pow_pos hu 3, pow_pos hu 4]

include hu hu' hM hq2 in
/-- The third test of (14.3.32) holds at `(x_{M+2}, t_{M+1})`: the gradient of
`μ(·, t_{M+1})` there is `(0, -(3u/4)³/32)`. -/
theorem meritCrit_last :
    meritCrit objG conC boxX q (epsS u) (tgtS u M (M + 1)) (xsS u M (M + 1 + 1)) (fun _ => 1) := by
  intro j hj
  have hj12 : j = 1 ∨ j = 2 := by have := Finset.mem_Icc.1 hj; omega
  simp only [one_pow, mul_one]
  have hx := xsS_last (u := u) (M := M)
  set B := 16 * (-3 * u / 4 - tgtS u M (M + 1) - finS u)
  have hF : -3 * u / 4 - B / 16 - tgtS u M (M + 1) = finS u := by ring
  have h0 : (0 : ℝ²) ∈ {d | xsS u M (M + 1 + 1) + d ∈ boxX} := by
    simpa using xsS_mem hu hu' hM (k := M + 1 + 1) (by omega) le_rfl
  have hup := measure_lin_le (Δ := (ftaylorSeries ℝ (Constrained.targetMerit objG conC
    (tgtS u M (M + 1))) (xsS u M (M + 1 + 1))).taylorDecrement 1)
    (a := -((-3 * u / 4) ^ 3 / 2 + finS u)) (b := finS u / 16)
    (fun d => by rw [decrG, hx, objG_pt, pt_zero, hF]) h0
  have h := Constrained.norm_le_targetResidual (f := objG) (c := conC) (t := tgtS u M (M + 1))
    (x := xsS u M (M + 1 + 1))
  have h' : ‖conC (xsS u M (M + 1 + 1))‖ = 9 * u ^ 2 / 32 := by
    rw [norm_conC, hx, pt_zero]; ring
  have e : -((-3 * u / 4) ^ 3 / 2 + finS u) = 0 := by rw [finS]; ring
  rw [e, abs_zero, zero_add, abs_of_pos (by rw [finS]; positivity)] at hup
  have hR : 9 * u ^ 2 / 32 ≤
      Constrained.targetResidual objG conC (tgtS u M (M + 1)) (xsS u M (M + 1 + 1)) := by linarith
  rcases hj12 with rfl | rfl
  · refine (show Optimization.taylorMeasure _ 1 1 _ ≤ _ from hup).trans ?_
    rw [epsS_one, finS]
    have : 3 * u / 2 * (9 * u ^ 2 / 32) ≤ 3 * u / 2 *
        Constrained.targetResidual objG conC (tgtS u M (M + 1)) (xsS u M (M + 1 + 1)) := by
      gcongr
    norm_num
    nlinarith [pow_pos hu 3]
  · have h2 : Optimization.taylorMeasure (ftaylorSeries ℝ (Constrained.targetMerit objG conC
        (tgtS u M (M + 1))) (xsS u M (M + 1 + 1))) 2 1 {d | xsS u M (M + 1 + 1) + d ∈ boxX} ≤
        finS u / 16 := by
      refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self zero_le_one, h0⟩
        fun d hd => (decr_two_le _ d _).trans ?_
      exact (Optimization.le_decrementMeasure
        (Optimization.bddAbove_taylorDecrement _ 1 1 _) hd).trans hup
    refine h2.trans ?_
    rw [epsS_two, finS]
    norm_num
    nlinarith [pow_pos hu 3]

include hu hu' in
/-- Phase 2 stops at `M + 1` (case (c)). -/
theorem stop_last : (runS u M).Stop objG conC boxX q (1 / 2) (epsS u) (M + 1) :=
  Or.inl ⟨not_isKa hu hu' (by omega), not_isKb_last hu⟩

include hu hu' hM hq1 in
/-- Phase 2 does not stop at `k ∈ [1, M]`. -/
theorem not_stop {k : ℕ} (hk1 : 1 ≤ k) (hkM : k ≤ M) :
    ¬ (runS u M).Stop objG conC boxX q (1 / 2) (epsS u) k := by
  rintro (⟨-, hb⟩ | ⟨-, hm⟩)
  · exact hb (isKb hu hu' hk1 hkM)
  · exact not_meritCrit_new hu hu' hM hq1 hk1 hkM hm

include hu hu' hM hq1 in
/-- Phase 2 does not stop before `M + 1`. -/
theorem before_last : (runS u M).Before objG conC boxX q (1 / 2) (epsS u) (M + 1) :=
  fun _ hj1 hjM => not_stop hu hu' hM hq1 hj1 (by omega)

include hu hu' in
/-- Every outer iteration reached is at most `M + 1`. -/
theorem le_of_before {k : ℕ} (h : (runS u M).Before objG conC boxX q (1 / 2) (epsS u) k) :
    k ≤ M + 1 := by
  by_contra hk
  exact h (M + 1) (by omega) (by omega) (stop_last hu hu')

include hu hu' hM hq1 in
/-- Phase 2 terminates at the outer iteration `M + 1`. -/
theorem isEnd : (runS u M).IsEnd objG conC boxX q (1 / 2) (epsS u) (M + 1) :=
  ⟨by omega, stop_last hu hu', before_last hu hu' hM hq1⟩

include hu hu' hM hq1 in
/-- `M + 1` is the only termination index. -/
theorem isEnd_iff {k : ℕ} : (runS u M).IsEnd objG conC boxX q (1 / 2) (epsS u) k ↔ k = M + 1 := by
  refine ⟨fun h => ?_, fun h => h ▸ isEnd hu hu' hM hq1⟩
  have hle := le_of_before hu hu' h.2.2
  rcases Nat.lt_or_ge k (M + 1) with hlt | hge
  · exact absurd h.2.1 (not_stop hu hu' hM hq1 h.1 (by omega))
  · omega

include hu hu' hM hM1 hq1 hq2 in
/-- **The sequences form a Phase-2 run of TPqp-GC** (`θ = β = 1/2`). -/
theorem isTPqpGCPhase2 {p : ℕ} (hp : 4 ≤ p) :
    IsTPqpGCPhase2 objG conC boxX q (1 / 2) (1 / 2) (epsS u) (pt 0 0) (runS u M) := by
  have hu7 : u ≤ 1 / 7 := by linarith
  have hc1 : ‖conC (pt 0 0)‖ = 0 := by rw [norm_conC]; simp
  rw [← xsS_one (u := u) (M := M)]
  refine isTPqpGCPhase2_oneStep (by norm_num) (by norm_num) (by norm_num) le_rfl
    (fun j _ => epsS_pos hu j) (fun j _ => epsS_le_one hu hu7 j)
    (by rw [xsS_one]; exact pt_mem (by norm_num) (by norm_num)) ?_ ?_
    (fun k hk1 hk => xsS_mem hu hu' hM (by omega) (by have := le_of_before hu hu' hk; omega))
    (fun k hk1 hk => ?_) (fun k hk1 hk => IsARqpSCCallOut.antitone
      (callOut_run hu hu' hM hM1 hq1 hq2 hp hk1 (le_of_before hu hu' hk)) 0 one_pos)
    (fun k hk1 hk => resid_start_ge hu hu' hk1 (le_of_before hu hu' hk))
    (fun k hk1 _ ha => absurd ha (not_isKa hu hu' hk1)) fun k hk1 hk hb => ?_
  · rw [xsS_one, hc1]; exact (mul_pos (by norm_num) (epsS_pos hu 0)).le
  · rw [xsS_one, hc1, tgtS_one, objG_pt, epsS_zero]
    rw [show (u ^ 2 / 2 + u ^ 3 / 2) ^ 2 - (0 : ℝ) ^ 2 = (u ^ 2 / 2 + u ^ 3 / 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
    ring
  · rcases Nat.lt_or_ge k (M + 1) with hlt | hge
    · exact Or.inr (Or.inl (isKb hu hu' hk1 (by omega)).2)
    · obtain rfl : k = M + 1 := by have := le_of_before hu hu' hk; omega
      exact Or.inr (Or.inr (meritCrit_last hu hu' hM hq2))
  · have hlt : k ≤ M := by
      by_contra h
      exact not_isKb_last hu ((show k = M + 1 by have := le_of_before hu hu' hk; omega) ▸ hb)
    rw [objG_xsS_succ hk1, landF_of_le hlt, tgtS_succ]
    ring

include hu hu' hM hM1 hq1 hq2 in
/-- **The Phase-2 INNER calls are ARqp-SC runs** (`IsARqpSCPhase2Calls`, `β = 1/2`). -/
theorem isARqpSCPhase2Calls {p : ℕ} (hp : 4 ≤ p) :
    IsARqpSCPhase2Calls objG conC boxX p q cexP (1 / 2) (1 / 2) (epsS u) (runS u M) :=
  fun _ hk1 hk => callOut_run hu hu' hM hM1 hq1 hq2 hp hk1 (le_of_before hu hu' hk)

include hu hu' hM hM1 hq1 hq2 in
/-- **The run is a TPqp-GC run whose INNER calls are ARqp-SC runs** (`IsTPqpGCARqpSCRun`). -/
theorem isTPqpGCARqpSCRun {p : ℕ} (hp : 4 ≤ p) {β₁ : ℝ} (hβ₁ : 0 < β₁) (hβ₁1 : β₁ < 1)
    (nF₁ nD₁ : ℕ → ℕ) :
    IsTPqpGCARqpSCRun objG conC boxX p q cexP (1 / 2) β₁ (1 / 2) (epsS u) (pt 0 0)
      (fun _ => pt 0 0) (fun _ _ => 1) 0 (runS u M) nF₁ nD₁ :=
  ⟨(isTPqpGCPhase2 hu hu' hM hM1 hq1 hq2 hp).algorithm_14_3_2_of_stop hβ₁ hβ₁1,
    fun k hk1 hk0 => absurd hk1 (by omega),
    fun _ => isARqpSCPhase2Calls hu hu' hM hM1 hq1 hq2 hp⟩

end Outer

/-! ### The order -/

/-- `ε^{-c} ≤ B^{a c}` when `ε ≥ B^{-a}` (`ε, B > 0`, `c ≥ 0`). -/
theorem rpow_neg_le {ε B a c : ℝ} (hε : 0 < ε) (hB : 0 < B) (h : (B ^ a)⁻¹ ≤ ε) (hc : 0 ≤ c) :
    ε ^ (-c) ≤ B ^ (a * c) := by
  have hBa : 0 < B ^ a := Real.rpow_pos_of_pos hB a
  have hi : ε⁻¹ ≤ B ^ a := by
    have := inv_anti₀ (inv_pos.2 hBa) h
    rwa [inv_inv] at this
  rw [Real.rpow_neg hε.le, ← Real.inv_rpow hε.le, Real.rpow_mul hB.le]
  exact Real.rpow_le_rpow (inv_pos.2 hε).le hi hc

/-- **One term of the printed order**: if `ε₀ ≥ B^{-5}`, `ε_j ≥ B^{-a}` (`B ≥ 1`) and `π ≥ 1`
with `5(π - 1) + a π ≤ 7`, then `ε₀^{1-π} ε_j^{-π} ≤ B^7`. -/
theorem term_le_pow {ε₀ εj B a π : ℝ} (h0 : 0 < ε₀) (hj : 0 < εj) (hB : 1 ≤ B)
    (h0B : (B ^ (5 : ℝ))⁻¹ ≤ ε₀) (hjB : (B ^ a)⁻¹ ≤ εj) (hπ : 1 ≤ π)
    (hπ7 : 5 * (π - 1) + a * π ≤ 7) : ε₀ ^ (1 - π) * εj ^ (-π) ≤ B ^ (7 : ℝ) := by
  have hB0 : 0 < B := by linarith
  have h1 : ε₀ ^ (1 - π) ≤ B ^ (5 * (π - 1)) := by
    rw [show 1 - π = -(π - 1) by ring]; exact rpow_neg_le h0 hB0 h0B (by linarith)
  have h2 : εj ^ (-π) ≤ B ^ (a * π) := rpow_neg_le hj hB0 hjB (by linarith)
  calc ε₀ ^ (1 - π) * εj ^ (-π) ≤ B ^ (5 * (π - 1)) * B ^ (a * π) :=
        mul_le_mul h1 h2 (Real.rpow_nonneg hj.le _) (Real.rpow_nonneg hB0.le _)
    _ = B ^ (5 * (π - 1) + a * π) := (Real.rpow_add hB0 _ _).symm
    _ ≤ B ^ (7 : ℝ) := Real.rpow_le_rpow_of_exponent_le hB hπ7

/-- **The printed orders along the run's tolerances**: for `u = 1/(4N⁵)` (`N ≥ 1`), `q ∈ {1, 2}`
and `p ≥ q + 3`, both orders of Theorem 14.3.9 with the ARqp-SC exponents `j(p+1)/p` are at
most `128 N¹⁴` (`B = 2N²`, `ε₀ ≥ B^{-5}`, `ε₁ ≥ B^{-3}`, `ε₂ = 1`). -/
theorem order_le_pow {p q N : ℕ} (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hpq : q + 3 ≤ p) (hN : 1 ≤ N) :
    tpqpOrderF (Optimization.arqpPiOf False p) q (epsS (1 / (4 * N ^ 5))) ≤ 128 * (N : ℝ) ^ 14 ∧
      tpqpOrderD (Optimization.arqpPiOf False p) q (epsS (1 / (4 * N ^ 5))) ≤
        128 * (N : ℝ) ^ 14 := by
  set u : ℝ := 1 / (4 * N ^ 5) with hu_def
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  set B : ℝ := 2 * (N : ℝ) ^ 2 with hB_def
  have hB1 : 1 ≤ B := by nlinarith
  have hB0 : 0 < B := by linarith
  have hB7 : B ^ (7 : ℝ) = 128 * (N : ℝ) ^ 14 := by
    rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hB_def]; ring
  have hu : 0 < u := by positivity
  have hε0 : (B ^ (5 : ℝ))⁻¹ ≤ epsS u 0 := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, epsS_zero]
    have : (B ^ 5)⁻¹ = u ^ 2 / 2 := by rw [hB_def, hu_def]; field_simp; ring
    rw [this]; have := pow_pos hu 3; linarith
  have hε1 : (B ^ (3 : ℝ))⁻¹ ≤ epsS u 1 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, epsS_one, hB_def, hu_def]
    rw [inv_le_comm₀ (by positivity) (by positivity)]
    field_simp
    nlinarith [pow_pos hNp 5, pow_pos hNp 6]
  have hπ : ∀ l ∈ Finset.Icc 1 q, 1 ≤ Optimization.arqpPiOf False p l := fun l hl => by
    have := Finset.mem_Icc.1 hl
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast this.1
    simp only [Optimization.arqpPiOf, ite_false]
    rw [le_div_iff₀ hp0]; nlinarith
  have hterm : ∀ l ∈ Finset.Icc 1 q, epsS u 0 ^ (1 - Optimization.arqpPiOf False p l) *
      epsS u l ^ (-Optimization.arqpPiOf False p l) ≤ B ^ (7 : ℝ) := fun l hl => by
    have hl := Finset.mem_Icc.1 hl
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    have hpq' : (q : ℝ) + 3 ≤ p := by exact_mod_cast hpq
    rcases (show l = 1 ∨ l = 2 by omega) with rfl | rfl
    · refine term_le_pow (epsS_pos hu 0) (epsS_pos hu 1) hB1 hε0 hε1
        (hπ 1 (Finset.mem_Icc.2 ⟨le_rfl, hq1⟩)) ?_
      simp only [Optimization.arqpPiOf, ite_false, Nat.cast_one, one_mul]
      have hp4 : (4 : ℝ) ≤ p := by have : (1 : ℝ) ≤ q := by exact_mod_cast hq1
                                   linarith
      have : ((p : ℝ) + 1) / p ≤ 5 / 4 := by rw [div_le_iff₀ hp0]; linarith
      linarith
    · have hq2' : (q : ℝ) = 2 := by exact_mod_cast (show q = 2 by omega)
      have h2 : epsS u 2 = 1 := epsS_two
      rw [h2, Real.one_rpow, mul_one]
      have hπ2 : Optimization.arqpPiOf False p 2 ≤ 12 / 5 := by
        simp only [Optimization.arqpPiOf, ite_false]
        rw [div_le_iff₀ hp0]; push_cast; linarith
      have hπ1 := hπ 2 (Finset.mem_Icc.2 ⟨by norm_num, by omega⟩)
      calc epsS u 0 ^ (1 - Optimization.arqpPiOf False p 2)
          ≤ B ^ (5 * (Optimization.arqpPiOf False p 2 - 1)) := by
            rw [show 1 - Optimization.arqpPiOf False p 2 =
              -(Optimization.arqpPiOf False p 2 - 1) by ring]
            exact rpow_neg_le (epsS_pos hu 0) hB0 hε0 (by linarith)
        _ ≤ B ^ (7 : ℝ) := Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)
  have h0 : (epsS u 0)⁻¹ ≤ B ^ (7 : ℝ) := by
    have := rpow_neg_le (c := 1) (epsS_pos hu 0) hB0 hε0 zero_le_one
    rw [Real.rpow_neg_one, mul_one] at this
    exact this.trans (Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num))
  rw [← hB7]
  exact ⟨Optimization.finMax_le h0 hterm,
    Optimization.finMax_le (Real.rpow_nonneg hB0.le _) hterm⟩

/-- **The parameters for a constant `C`**: `N = ⌈128 |C|⌉ + 3`, so that `C · 128 N¹⁴ < N¹⁵` and
the tolerances `ε₀, ε₁ ≤ C⁻¹` vanish as `C` grows. -/
theorem exists_params (C : ℝ) : ∃ N : ℕ, 3 ≤ N ∧ C * (128 * (N : ℝ) ^ 14) < (N : ℝ) ^ 15 ∧
    (1 ≤ C → epsS (1 / (4 * N ^ 5)) 0 ≤ C⁻¹ ∧ epsS (1 / (4 * N ^ 5)) 1 ≤ C⁻¹) := by
  refine ⟨⌈128 * |C|⌉₊ + 3, by omega, ?_, fun hC => ?_⟩
  · set N : ℕ := ⌈128 * |C|⌉₊ + 3
    have hN : 128 * |C| + 2 < (N : ℝ) := by
      have := Nat.le_ceil (128 * |C|); push_cast [N]; linarith
    have hNp : (0 : ℝ) < N := by linarith [abs_nonneg C]
    have h14 : (0 : ℝ) < (N : ℝ) ^ 14 := by positivity
    calc C * (128 * (N : ℝ) ^ 14) ≤ |C| * (128 * (N : ℝ) ^ 14) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ = 128 * |C| * (N : ℝ) ^ 14 := by ring
      _ < N * (N : ℝ) ^ 14 := mul_lt_mul_of_pos_right (by linarith) h14
      _ = (N : ℝ) ^ 15 := by ring
  · set N : ℕ := ⌈128 * |C|⌉₊ + 3
    have hN : 128 * |C| + 2 < (N : ℝ) := by
      have := Nat.le_ceil (128 * |C|); push_cast [N]; linarith
    have hCN : C ≤ N := by linarith [le_abs_self C, abs_nonneg C]
    have hNp : (1 : ℝ) ≤ N := by linarith
    set u : ℝ := 1 / (4 * N ^ 5)
    have hu : 0 < u := by positivity
    have hN5 : (N : ℝ) ≤ (N : ℝ) ^ 5 := le_self_pow₀ hNp (by norm_num)
    have hu1 : u ≤ 1 := by
      apply div_le_one_of_le₀ (by nlinarith) (by positivity)
    have hNinv : 3 * u / 2 ≤ (N : ℝ)⁻¹ := by
      have : 3 * u / 2 = 3 / (8 * (N : ℝ) ^ 5) := by simp only [u]; field_simp; ring
      rw [this, div_le_iff₀ (by positivity)]
      field_simp
      nlinarith
    have hCi : (N : ℝ)⁻¹ ≤ C⁻¹ := inv_anti₀ (by linarith) hCN
    have hε1 : epsS u 1 ≤ C⁻¹ := by rw [epsS_one]; linarith
    refine ⟨?_, hε1⟩
    rw [epsS_zero]
    nlinarith [pow_pos hu 2, pow_pos hu 3]

end Theorem1439ARqpCex


open Theorem1439Cex Theorem1439ARqpCex PlaneCex in
/-- **Theorem 14.3.9 of [cartis2022evaluation] fails for runs of ARqp-SC that re-initialise `μ`
at Step 2.1 of Algorithm 14.1.2, when `q ∈ {1, 2}` and `p ≥ q + 3`** (the exponents
`π_j = j(p+1)/p` of (14.2.12), "otherwise" entry;
for `q = 1` the exponent `(p+1)/p` is also that of the "`q = 1`, `X` convex" ARqp-SC entry and of
the convex ARqpC-SC entry). There is one problem (`n = 2`, `m = 1`, `X = [-1, 1]²`,
`f(x) = x₁ - x₂/16`, `c(x) = x₁²/2`) satisfying the assumptions of the theorem — X.CNe
(`AssumptionXCNe`; `X` also convex), c.D1pLB.X and f.D1pLB.X on `X₀ = B(0, 2)`, f.B.Fb on `ℱ_1`
with `f_low = -2`, `f_up = 2` — and ARqpC constants `P` (`cexP`, with `θ < ς`) such that, with
`θ = β = 1/2`, `x₀ = (0, 0)` and every Phase-1 constant `β₁ ∈ (0, 1)`, for all `κ_F`, `κ_D` there
are tolerances `ε_j ∈ (0, 1]` (`ε₀ ≤ β_F = 1`, `ε₀, ε₁ ≤ κ_F⁻¹` when `κ_F ≥ 1`, `ε₂ = 1`) and a
TPqp-GC run whose INNER calls in both phases are ARqp-SC runs (`IsTPqpGCARqpSCRun`, the run class
of `theorem_14_3_9_arqp`; Phase 1 makes no call and Phase 2 is entered at `x₀`) such that at its
termination index `k_ε` the numbers of evaluations of `(f, c)` and of their derivatives exceed
`κ_F max[ε₀^{-1}, max_j ε₀^{1-π_j} ε_j^{-π_j}]` and `κ_D max_j ε₀^{1-π_j} ε_j^{-π_j}`, the orders
printed in the theorem, and are at least `(ε₀ ε₁)^{-1}/128`.

The run (`Theorem1439ARqpCex.runS`): for `u = 1/(4N⁵)`, `ε₀ = u²/2 + u³/2`, `ε₁ = 3u/2` and
`M = N¹⁵`, Phase 2 makes `M + 1` outer iterations, each a single successful ARqp-SC iteration
(`callOut_run`): the first moves from `(0, 0)` to `(u, ·)`, the next `M - 1` move along `x₂` with
`f(x_{k+1}) = t_k - E_k`, `E_k ≈ u³/2 ≈ 2 ε₀ ε₁/3`, where `∇μ(·, t_k) = (u³/2 - E_k, E_k/16)` is
nearly zero (INNER stops; case (b), the target drops by `2E_k`; after the reflection the gradient
is `≈ (u³, ·)` and (14.3.34) fails), and the last lands at `(-3u/4, ·)` where (14.3.32) holds with
`f > t` (case (c)). Each step satisfies the Step-2 conditions (14.1.12)–(14.1.13), all the
printed Algorithm 14.1.1 asks for, and is an output of the detailed Step 2 (Algorithm 14.1.2)
initialized with `μ = Δm(s)/(m(0) - m*)` at Step 2.1 (`μ ∈ (0, 1]` is chosen afresh at every
Step 2, not fixed at Step 0, and the book notes after Algorithm 12.2.3 that global
minimization is not required): an approximate critical point of the model with tiny model decrease,
not an
approximate global minimizer. The Taylor models are exact (`μ` is a quartic polynomial, `p ≥ 4`;
`taylorSum_merit`), so every ratio is `1`; the second-order tests (`q = 2`) hold with room to
spare. The number of evaluations is `M + 2 ∼ (ε₀ ε₁)^{-1}`, the extra term of
`theorem_14_3_9_arqp_corrected`, which is thus attained (for `q ∈ {1, 2}`, `p ≥ q + 3`). -/
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
  obtain ⟨⟨Lf, Bf, hf⟩, Lc, Bc, hc⟩ := assumptionD1pLBX (1 / 16) p
  refine ⟨objG, conC, boxX, Lc, Bc, Lf, Bf, cexP, ⟨isClosed_boxX, ⟨pt 0 0, pt_mem (by norm_num)
    (by norm_num)⟩⟩, convex_boxX, hc, hf, assumptionBFb (by norm_num), by norm_num [cexP],
    fun β₁ κF κD hβ₁ hβ₁1 => ?_⟩
  set C := max (max κF κD) 1 with hC_def
  have hC1 : 1 ≤ C := le_max_right _ _
  obtain ⟨N, hN3, hNC, hCε⟩ := Theorem1439ARqpCex.exists_params C
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
  have hc0 : ‖conC (pt 0 0)‖ = 0 := by rw [norm_conC]; simp
  refine ⟨epsS u, fun _ => pt 0 0, fun _ _ => 1, runS u M,
    fun j => ⟨epsS_pos hu j, epsS_le_one hu hu7 j⟩, fun hκ => ?_,
    fun nF₁ nD₁ => isTPqpGCARqpSCRun hu hu' hM hM1 hq1 hq2 (by omega) hβ₁ hβ₁1 nF₁ nD₁,
    by rw [hc0]; exact (mul_pos (by norm_num) (epsS_pos hu 0)).le,
    ⟨M + 1, Theorem1439ARqpCex.isEnd hu hu' hM hq1⟩,
    fun kε hend => ?_⟩
  · have hle : C⁻¹ ≤ κF⁻¹ :=
      inv_anti₀ (by linarith) ((le_max_left _ _).trans (le_max_left _ _))
    obtain ⟨h0, h1'⟩ := hCε hC1
    exact ⟨h0.trans hle, h1'.trans hle⟩
  rw [(isEnd_iff hu hu' hM hq1).1 hend, runS, TPqpSeq.funEvals_oneStep,
    TPqpSeq.derivEvals_oneStep]
  obtain ⟨hF, hD⟩ := order_le_pow (p := p) hq1 hq2 hpq (show 1 ≤ N by omega)
  rw [← hu_def] at hF hD
  have hF0 : 0 ≤ tpqpOrderF (Optimization.arqpPiOf False p) q (epsS u) :=
    zero_le_one.trans (one_le_tpqpOrderF (epsS_pos hu 0) (epsS_le_one hu hu7 0))
  have hD0 : 0 ≤ tpqpOrderD (Optimization.arqpPiOf False p) q (epsS u) :=
      Optimization.le_finMax_left
  have hκF : κF * tpqpOrderF (Optimization.arqpPiOf False p) q (epsS u) ≤
      C * (128 * (N : ℝ) ^ 14) :=
    (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) hF0).trans
      (mul_le_mul_of_nonneg_left hF (by linarith))
  have hκD : κD * tpqpOrderD (Optimization.arqpPiOf False p) q (epsS u) ≤
      C * (128 * (N : ℝ) ^ 14) :=
    (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_left _ _)) hD0).trans
      (mul_le_mul_of_nonneg_left hD (by linarith))
  have hε01 : (epsS u 0 * epsS u 1)⁻¹ ≤ 128 * ((M + 1 + 1 : ℕ) : ℝ) := by
    rw [epsS_zero, epsS_one]
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

open Theorem1439Cex Theorem1439ARqpCex PlaneCex in
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

/-- `a b ≤ 1` for `a ≤ 1` and `b ∈ [0, 1]`. -/
private theorem mul_le_one_aux {a b : ℝ} (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb : b ≤ 1) :
    a * b ≤ 1 :=
  (mul_le_of_le_one_left hb0 ha).trans hb

/-! ### The count constants of a Phase-2 call -/

/-- The constant part `κ_uns + (|log Δ₀| + |log κ_ρ| + |log(βθ)|)/|log γ₂|` of the count of the
iterations of one Phase-2 TRq-SC call (`Optimization.IsTRqCallOut.le_count`); the full count adds
`|log(ε₀ ε_min)|/|log γ₂|` (`trqSCLogTerm`). -/
noncomputable def trqSCKappaUnc0 (P : Optimization.TRqParams) (L : ℕ → ℝ) (ϑ M : ℝ) (q : ℕ)
    (β θ : ℝ) : ℝ :=
  Optimization.trqKappaUns P + (|Real.log P.Δ₀| +
    |Real.log (Optimization.trqCallKappaRad P L ϑ M q)| + |Real.log (β * θ)|) / |Real.log P.γ₂|

/-- The logarithmic term `|log(ε₀ ε_min)|`, `ε_min = min_{j ∈ [1 : q]} ε_j`, of the number of
unsuccessful iterations of the trust-region INNER calls. -/
noncomputable def trqSCLogTerm (q : ℕ) (ε : ℕ → ℝ) : ℝ :=
  |Real.log (ε 0 * Optimization.finMin 1 ε q)|

/-- The constant part of the count constant is nonnegative. -/
theorem trqSCKappaUnc0_nonneg {P : Optimization.TRqParams} {L : ℕ → ℝ} {ϑ M : ℝ} {q : ℕ}
    (β θ : ℝ) : 0 ≤ trqSCKappaUnc0 P L ϑ M q β θ := by
  unfold trqSCKappaUnc0
  have := Optimization.one_le_trqKappaUns (P := P)
  have : 0 ≤ (|Real.log P.Δ₀| + |Real.log (Optimization.trqCallKappaRad P L ϑ M q)| +
    |Real.log (β * θ)|) / |Real.log P.γ₂| := by positivity
  linarith

/-! ### Phase 2 with TRq-SC calls: the INNER contract for every run -/

section Phase2

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {q : ℕ} {P : Optimization.TRqParams}
  {ϑ θ β : ℝ} {ε : ℕ → ℝ} {x₁ : ℝⁿ} {D : TPqpSeq n}

/-- **The INNER calls of Phase 2 of TPqp-GC are TRq-SC runs** ([cartis2022evaluation],
Algorithm 14.3.2, Step 1: `INNER(μ(·, t_k), X, q, x_k, β ‖r(x_k, t_k)‖ ε)` with INNER of
trust-region type): for every outer iteration `k ≥ 1` reached, the iterates, successful iterations
and output radii `δ_{k+1}` of the `k`-th call are those of a TRq-SC run on `μ(·, t_k)` with
threshold `ϑ` and tolerances `β ‖r(x_k, t_k)‖ ε_j` (`Optimization.IsTRqCallOut`), cut at any
iteration (by any test of (14.3.32)). -/
def IsTRqSCPhase2Calls (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (X : Set ℝⁿ) (q : ℕ)
    (P : Optimization.TRqParams) (ϑ θ β : ℝ) (ε : ℕ → ℝ) (D : TPqpSeq n) : Prop :=
  ∀ k, 1 ≤ k → D.Before f c X q θ ε k →
    Optimization.IsTRqCallOut (Constrained.targetMerit f c (D.t k)) X P q
      (fun j => β * Constrained.targetResidual f c (D.t k) (D.x k) * ε j) ϑ (D.xi k) (D.e k)
      (D.succ k) (D.δ (k + 1))

/-- **The residual at the outer iterates is at least `θε₀`**: `‖r(x_k, t_k)‖ ≥ θε₀` for every
outer iteration `k ≥ 1` reached (`‖r(x_1, t_1)‖ = ε₀`, `‖r(x_{k+1}, t_{k+1})‖ = ε₀` after a
case-(a) iteration and `‖r(x_{k+1}, t_{k+1})‖ = ‖r(x_{k+1}, t_k)‖ ≥ θε₀` after a case-(b)
iteration). -/
theorem IsTPqpGCPhase2.le_targetResidual (h : IsTPqpGCPhase2 f c X q θ β ε x₁ D) :
    ∀ k, 1 ≤ k → D.Before f c X q θ ε k →
      θ * ε 0 ≤ Constrained.targetResidual f c (D.t k) (D.x k) := by
  have hθε : θ * ε 0 ≤ ε 0 := mul_le_of_le_one_left h.ε₀_pos.le h.θ_lt_one.le
  intro k hk1
  induction k, hk1 using Nat.le_induction with
  | base =>
    intro _
    rw [h.t_one, h.x_one, Constrained.targetResidual_sub_sqrt h.ε₀_pos.le
      (h.norm_one_le.trans hθε)]
    exact hθε
  | succ k hk1 _ =>
    intro hK
    have T := h.isTargetSequence hK
    have hs : ¬ D.Stop f c X q θ ε k := hK k hk1 (Nat.lt_succ_self k)
    rcases Constrained.TargetFollowingSeq.ka_or_kb_of_not_stop hs with ha | hb
    · rw [T.residual_succ_of_Ka h.θ_lt_one.le h.ε₀_pos.le hk1 (Nat.lt_succ_self k) ha]
      exact hθε
    · have hna : ¬ D.IsKa f c θ ε k := fun ha => absurd hb.1 (not_le.2 ha)
      rw [T.residual_succ_of_not_Ka hk1 (Nat.lt_succ_self k) hna]
      exact hb.1

/-- The tolerances `ε'_j = β ‖r(x_k, t_k)‖ ε_j` of the `k`-th call lie in `(0, 1]`, their minimum
is at most `ϑ` when `β ≤ ϑ`, and at least `βθ ε₀ ε_min`. -/
theorem IsTPqpGCPhase2.call_tol (h : IsTPqpGCPhase2 f c X q θ β ε x₁ D) (hq : 1 ≤ q)
    (hβϑ : β ≤ ϑ) {k : ℕ} (hk1 : 1 ≤ k) (hk : D.Before f c X q θ ε k) :
    (∀ j ∈ Finset.Icc 1 q,
      β * Constrained.targetResidual f c (D.t k) (D.x k) * ε j ∈ Ioc 0 1) ∧
    Optimization.finMin 1 (fun j => β * Constrained.targetResidual f c (D.t k) (D.x k) * ε j) q ≤
      ϑ ∧
    β * θ * (ε 0 * Optimization.finMin 1 ε q) ≤
      Optimization.finMin 1 (fun j => β * Constrained.targetResidual f c (D.t k) (D.x k) * ε j) q
          := by
  set r := Constrained.targetResidual f c (D.t k) (D.x k) with hr
  have hlo := h.le_targetResidual k hk1 hk
  have hhi : r ≤ ε 0 := (h.isTargetSequence hk).residual_le h.θ_lt_one.le h.ε₀_pos.le hk1 le_rfl
  have hε₀ := h.ε₀_pos
  have hε₀1 : ε 0 ≤ 1 := h.ε_le_one 0 (by simp)
  have hβ := h.β_pos
  have hθ := h.θ_pos
  have hβ1 : β ≤ 1 := h.β_le_θ.trans h.θ_lt_one.le
  have hr0 : 0 < r := lt_of_lt_of_le (mul_pos hθ hε₀) hlo
  have hεj : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1 := fun j hj =>
    ⟨h.ε_pos' hj, h.ε_le_one j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))⟩
  have hle : ∀ j ∈ Finset.Icc 1 q, β * r * ε j ≤ β := fun j hj => by
    have h1 : r * ε j ≤ 1 := by nlinarith [hεj j hj]
    nlinarith [hεj j hj]
  refine ⟨fun j hj => ⟨by have := (hεj j hj).1; positivity, (hle j hj).trans hβ1⟩, ?_, ?_⟩
  · exact (Optimization.finMin_le (Finset.mem_Icc.2 ⟨le_rfl, hq⟩)).trans
      ((hle 1 (Finset.mem_Icc.2 ⟨le_rfl, hq⟩)).trans hβϑ)
  · have hεm0 : 0 < Optimization.finMin 1 ε q := Optimization.finMin_pos one_pos fun j hj => (hεj j
      hj).1
    have hεm1 : Optimization.finMin 1 ε q ≤ 1 := Optimization.finMin_le_left
    refine Optimization.le_finMin ?_ fun j hj => ?_
    · exact mul_le_one_aux (mul_le_one_aux hβ1 hθ.le h.θ_lt_one.le) (by positivity)
        (mul_le_one_aux hε₀1 hεm0.le hεm1)
    · have h1 : θ * ε 0 * Optimization.finMin 1 ε q ≤ r * ε j :=
        mul_le_mul hlo (Optimization.finMin_le hj) hεm0.le hr0.le
      nlinarith

/-- **Every Phase-2 run of TPqp-GC whose INNER calls are TRq-SC runs satisfies the INNER contract
keyed on INNER's own test** (`IsInnerPhaseRunStrong`; [cartis2022evaluation], Lemmas 14.2.2–14.2.3,
TRq-SC rows, applied to `μ(·, t_k)`), with the exponents `π_l = q + 1` (the decrease of
Lemma 12.2.4 is `κ_decr ε'_min^{q+1}`, `ε'_l = β ‖r(x_k, t_k)‖ ε_l`), the `t`-independent constants
`κ_decr = Optimization.trqCallKappaDecr P L ϑ M q`, `κ_uns = Optimization.trqKappaUns P`, the
count constant `κ_unc = κ_unc⁰ + |log(ε₀ ε_min)|/|log γ₂|` (`trqSCKappaUnc0`, `trqSCLogTerm`:
every call restarts from the radius `Δ₀` and the radii can shrink to
`κ_ρ ε'_min ≥ κ_ρ βθ ε₀ ε_min`), and radii `ρ_j = κ_ρ βθ ε₀ ε_min`, when every `μ(·, t)`
satisfies anchored f.D1qL with constants `L` on `𝓛_μ(t)` (for an open convex `X₀ ⊇ X`) with
derivatives of orders `1, …, q` bounded by `M > 0` there (Lemma 14.3.6 (ii) gives both under
c.D1qLB.X and f.D1qLB.X), `1 ≤ q` and `β ≤ ϑ ≤ 1`. This holds for every run, with calls cut by
any test of (14.3.32). -/
theorem IsTRqSCPhase2Calls.isInnerPhaseRunStrong (h : IsTPqpGCPhase2 f c X q θ β ε x₁ D)
    (hcalls : IsTRqSCPhase2Calls f c X q P ϑ θ β ε D) (hq : 1 ≤ q) {X₀ : Set ℝⁿ}
    {L : ℕ → ℝ} {M : ℝ}
    (hμ : ∀ t, Chapter12.AssumptionD1pLAnchored (Constrained.targetMerit f c t) X₀
      (muSublevel f c X t) q L)
    (hμM : ∀ t, ∀ y ∈ muSublevel f c X t, Optimization.finMax 0
      (fun i => ‖iteratedFDeriv ℝ i (Constrained.targetMerit f c t) y‖) q ≤ M) (hM0 : 0 < M)
    (hXX₀ : X ⊆ X₀) (hβϑ : β ≤ ϑ) (hϑ1 : ϑ ≤ 1) :
    IsInnerPhaseRunStrong f c X q θ β ε D (Optimization.trqCallKappaDecr P L ϑ M q)
      (Optimization.trqKappaUns P)
      (trqSCKappaUnc0 P L ϑ M q β θ + trqSCLogTerm q ε / |Real.log P.γ₂|)
      (fun _ => (q : ℝ) + 1)
      (fun _ => Optimization.trqCallKappaRad P L ϑ M q * β * θ *
        (ε 0 * Optimization.finMin 1 ε q)) := by
  have hϑ0 : 0 < ϑ := h.β_pos.trans_le hβϑ
  have hκR := Optimization.trqCallKappaRad_pos (P := P) (L := L) (q := q) hϑ0 hM0
  -- the hypotheses of the analysis of the `k`-th call
  have hx : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → D.xi k 0 ∈ X := fun k hk1 hk => by
    rw [h.inner_zero k hk1 hk]; exact h.x_mem k hk1 hk
  have hMk : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → Optimization.finMax 0
      (fun i => ‖iteratedFDeriv ℝ i (Constrained.targetMerit f c (D.t k)) (D.xi k 0)‖) q ≤ M :=
    fun k hk1 hk => hμM _ _ (h.call_sublevel hk1 hk _ (hx k hk1 hk) le_rfl)
  refine ⟨⟨fun k hk1 hk => ?_, fun k hk1 hk => (hcalls k hk1 hk).eq_of_not_succ,
    fun k hk1 hk i hi hs _ _ => ?_⟩, fun k hk1 hk _ _ j hj => ?_⟩
  · -- the count, with the logarithm of the radius bound
    obtain ⟨htol, hϑ', hlow⟩ := h.call_tol hq hβϑ hk1 hk
    have hcount := (hcalls k hk1 hk).le_count (hμ (D.t k)).toLipschitzDerivsAnchored hXX₀
      (h.call_sublevel hk1 hk) (hx k hk1 hk) (hMk k hk1 hk) hM0 htol hϑ' hϑ1
    have hε₀ := h.ε₀_pos
    have hε₀1 : ε 0 ≤ 1 := h.ε_le_one 0 (by simp)
    have hεm0 : 0 < Optimization.finMin 1 ε q :=
      Optimization.finMin_pos one_pos fun j hj => h.ε_pos' hj
    have hεm1 : Optimization.finMin 1 ε q ≤ 1 := Optimization.finMin_le_left
    have hβθ1 : β * θ ≤ 1 := by
      nlinarith [h.β_le_θ, h.θ_lt_one, h.β_pos, h.θ_pos]
    set b := Optimization.finMin 1
      (fun j => β * Constrained.targetResidual f c (D.t k) (D.x k) * ε j) q
    have hb0 : 0 < b := lt_of_lt_of_le (by have := h.β_pos; have := h.θ_pos; positivity) hlow
    -- `|log(κ_ρ b/Δ₀)| ≤ |log Δ₀| + |log κ_ρ| + |log(βθ)| + |log(ε₀ ε_min)|`
    have hlog : |Real.log (Optimization.trqCallKappaRad P L ϑ M q * b / P.Δ₀)| ≤
        |Real.log P.Δ₀| + |Real.log (Optimization.trqCallKappaRad P L ϑ M q)| +
          |Real.log (β * θ)| + trqSCLogTerm q ε := by
      rw [Real.log_div (mul_pos hκR hb0).ne' P.Δ₀_pos.ne', Real.log_mul hκR.ne' hb0.ne']
      have hlb := Real.abs_log_le_of_mul_le (mul_pos h.β_pos h.θ_pos) (mul_pos hε₀ hεm0) hβθ1
        (mul_le_one_aux hε₀1 hεm0.le hεm1) hlow Optimization.finMin_le_left
      unfold trqSCLogTerm
      calc |Real.log (Optimization.trqCallKappaRad P L ϑ M q) + Real.log b - Real.log P.Δ₀| ≤
            |Real.log (Optimization.trqCallKappaRad P L ϑ M q)| + |Real.log b| +
              |Real.log P.Δ₀| := (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ _ := by linarith
    have hg : 0 < |Real.log P.γ₂| := abs_pos.2 (Real.log_neg P.γ₂_pos P.γ₂_lt_one).ne
    classical
    rw [Constrained.HighOrderTargetSeq.succCount_eq_card_filter]
    unfold trqSCKappaUnc0
    have : |Real.log (Optimization.trqCallKappaRad P L ϑ M q * b / P.Δ₀)| / |Real.log P.γ₂| ≤
        (|Real.log P.Δ₀| + |Real.log (Optimization.trqCallKappaRad P L ϑ M q)| +
          |Real.log (β * θ)|) / |Real.log P.γ₂| + trqSCLogTerm q ε / |Real.log P.γ₂| := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right hlog hg.le
    linarith
  · -- the decrease, at an order `l` attaining `ε'_min`
    obtain ⟨htol, hϑ', -⟩ := h.call_tol hq hβϑ hk1 hk
    obtain ⟨l, hl, hmin⟩ := Optimization.exists_finMin_eq hq fun j hj => (htol j hj).2
    refine ⟨l, hl, ?_⟩
    have hdec := (hcalls k hk1 hk).decrease (hμ (D.t k)).toLipschitzDerivsAnchored hXX₀
      (h.call_sublevel hk1 hk) (hx k hk1 hk) (hMk k hk1 hk) hM0 htol hϑ' hϑ1 i hi hs
    rw [hmin] at hdec
    have e : ((q : ℝ) + 1) = ((q + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [e, Real.rpow_natCast]
    exact hdec
  · -- the radii
    obtain ⟨htol, hϑ', hlow⟩ := h.call_tol hq hβϑ hk1 hk
    calc Optimization.trqCallKappaRad P L ϑ M q * β * θ * (ε 0 * Optimization.finMin 1 ε q) =
          Optimization.trqCallKappaRad P L ϑ M q * (β * θ * (ε 0 * Optimization.finMin 1 ε q)) := by
          ring
      _ ≤ Optimization.trqCallKappaRad P L ϑ M q * Optimization.finMin 1
          (fun j => β * Constrained.targetResidual f c (D.t k) (D.x k) * ε j) q :=
        mul_le_mul_of_nonneg_left hlow hκR.le
      _ ≤ D.δ (k + 1) j := (hcalls k hk1 hk).radius_ge (hμ (D.t k)).toLipschitzDerivsAnchored hXX₀
          (h.call_sublevel hk1 hk) (hx k hk1 hk) (hMk k hk1 hk) htol hϑ' hϑ1 j hj

end Phase2

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
      Chapter12.AssumptionD1pLAnchored (phi2 c) X₀ (nuSublevel c X x₀) q
        (fun j => LA j + LB j * ‖c x₀‖) ∧
      ∀ y ∈ nuSublevel c X x₀, Optimization.finMax 0
        (fun i => ‖iteratedFDeriv ℝ i (phi2 c) y‖) q ≤
          Optimization.finMax 1 (fun j => BA j + BB j * ‖c x₀‖) q := by
  obtain ⟨LA, LB, BA, BB, h1, hν⟩ := lemma_14_3_6_i hc
  refine ⟨LA, LB, BA, BB, fun x₀ => ⟨⟨hc.isOpen, hc.convex, fun x hx => hc.subset hx.1,
    fun y hy => (hν x₀).1.contDiffAt (hc.isOpen.mem_nhds hy), fun j _ => ?_,
    fun j hj => ((hν x₀).2 j hj).1⟩, fun y hy => ?_⟩⟩
  · have := (h1 j).1
    have := (h1 j).2.1
    have := norm_nonneg (c x₀)
    nlinarith
  · exact Optimization.finMax_le (zero_le_one.trans Optimization.le_finMax_left) fun i hi =>
      (((hν x₀).2 i hi).2 y hy).trans
        (Optimization.le_finMax (u := fun j => BA j + BB j * ‖c x₀‖) hi)

/-- c.D1qLB.X and f.D1qLB.X give, through Lemma 14.3.6 (ii), anchored f.D1qL for every `μ(·, t)`
on `𝓛_μ(t)` with constants `L_μ` and the bound `max(1, max_j B_{μ,j})` on the derivatives of
orders `1, …, q` there, independent of `t`. -/
theorem exists_mu_trq {X₀ : Set ℝⁿ} {Lc Bc Lf Bf : ℕ → ℝ}
    (hc : AssumptionCD1pLBX c X X₀ q Lc Bc) (hf : AssumptionD1pLBX f X X₀ q Lf Bf) :
    ∃ Lμ Bμ : ℕ → ℝ, ∀ t : ℝ,
      Chapter12.AssumptionD1pLAnchored (Constrained.targetMerit f c t) X₀ (muSublevel f c X t)
        q Lμ ∧
      ∀ y ∈ muSublevel f c X t, Optimization.finMax 0
        (fun i => ‖iteratedFDeriv ℝ i (Constrained.targetMerit f c t) y‖) q ≤
          Optimization.finMax 1 Bμ q := by
  obtain ⟨Lμ, Bμ, h2, hμ⟩ := lemma_14_3_6_ii hc hf
  refine ⟨Lμ, Bμ, fun t => ⟨⟨hc.isOpen, hc.convex, fun x hx => hc.subset hx.1,
    fun y hy => (hμ t).1.contDiffAt (hc.isOpen.mem_nhds hy), fun j _ => (h2 j).1,
    fun j hj => ((hμ t).2 j hj).1⟩, fun y hy => ?_⟩⟩
  exact Optimization.finMax_le (zero_le_one.trans Optimization.le_finMax_left) fun i hi =>
    (((hμ t).2 i hi).2 y hy).trans (Optimization.le_finMax (u := Bμ) hi)

/-- The bad-iteration term with the radii `ρ'_j = ε₀ ε_min` is within the order with the
exponents `q + 1`: `(ε₀ ε_j (ε₀ ε_min)^{j-1})^{-1} ≤ ε₀^{-q} ε_min^{-(q+1)}` for `j ∈ [1 : q]`
and tolerances in `(0, 1]`. -/
theorem inv_bad_le_trq {ε₀ εj εm : ℝ} (h0 : 0 < ε₀) (h01 : ε₀ ≤ 1) (hm0 : 0 < εm) (hm1 : εm ≤ 1)
    (hmj : εm ≤ εj) {j : ℕ} (hj1 : 1 ≤ j) (hjq : j ≤ q) :
    (ε₀ * εj * (ε₀ * εm) ^ (j - 1))⁻¹ ≤ ε₀ ^ (1 - ((q : ℝ) + 1)) * εm ^ (-((q : ℝ) + 1)) := by
  have hp : 0 < ε₀ * εm := mul_pos h0 hm0
  have hp1 : ε₀ * εm ≤ 1 := mul_le_one_aux h01 hm0.le hm1
  have h1 : (ε₀ * εm) ^ j ≤ ε₀ * εj * (ε₀ * εm) ^ (j - 1) := by
    rw [← mul_pow_sub_one (by omega : j ≠ 0) (ε₀ * εm)]
    gcongr
  have h2 : (ε₀ * εm) ^ q ≤ (ε₀ * εm) ^ j := pow_le_pow_of_le_one hp.le hp1 hjq
  calc (ε₀ * εj * (ε₀ * εm) ^ (j - 1))⁻¹ ≤ ((ε₀ * εm) ^ j)⁻¹ := inv_anti₀ (pow_pos hp _) h1
    _ ≤ ((ε₀ * εm) ^ q)⁻¹ := inv_anti₀ (pow_pos hp _) h2
    _ ≤ _ := inv_pow_le_term_succ h0 hm0 hm1 q

/-- The number of Phase-1 iterations of TPqp-GC is at most `1 + ‖c(x₀)‖/(θ |log β₁|) ε₀^{-1}`
(Theorem 14.3.3, `ceil_log_div_le`). -/
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
    (Nat.cast_le.2 hkmax).trans (ceil_log_div_le (mul_pos hθ0 hε₀) (norm_nonneg _)
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
    (hν : Chapter12.AssumptionD1pLAnchored (phi2 c) X₀ (nuSublevel c X x₀) q Lν)
    (hνM : ∀ y ∈ nuSublevel c X x₀,
      Optimization.finMax 0 (fun i => ‖iteratedFDeriv ℝ i (phi2 c) y‖) q ≤ Mν) (hMν0 : 0 < Mν)
    (hXX₀ : X ⊆ X₀) (hϑ1 : ϑ ≤ 1) (hβ₁ϑ : β₁ * ‖c x₀‖ ≤ ϑ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) :
    ∀ k ∈ Finset.Icc 1 k₁,
      (nF₁ k : ℝ) ≤ innerEvalBound (Optimization.trqCallKappaA P Lν ϑ Mν q)
        (fun _ => (q : ℝ) + 1) q
        (phi2 c (xP (k - 1))) (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j) +
          (Optimization.kappaBTRq P * (|Real.log (β₁ * θ)| + trqSCLogTerm q ε) +
            Optimization.trqCallKappaC P Lν ϑ Mν q) ∧
      (nD₁ k : ℝ) ≤ innerEvalBound (Optimization.trqCallKappaS P Lν ϑ Mν q)
        (fun _ => (q : ℝ) + 1) q
        (phi2 c (xP (k - 1))) (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j) + 1 := by
  have h := hR.run
  have hε₀ := hε 0 (by simp)
  have hεI : ∀ l ∈ Finset.Icc 1 q, 0 < ε l ∧ ε l ≤ 1 := fun l hl =>
    hε l (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hl).2))
  have hεm0 : 0 < Optimization.finMin 1 ε q := Optimization.finMin_pos one_pos fun j hj => (hεI j
      hj).1
  have hεm1 : Optimization.finMin 1 ε q ≤ 1 := Optimization.finMin_le_left
  have h1q : 1 ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, hq⟩
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
  have hck0 := hck
  obtain ⟨r, hr⟩ : ∃ x, x = ‖c (xP (k - 1))‖ := ⟨_, rfl⟩
  rw [← hr] at hck hlo ⊢
  have hr0 : 0 < r := (mul_pos hθ0 hε₀.1).trans hlo
  have hϑ0 : 0 < ϑ := lt_of_lt_of_le (mul_pos hβ₁0 (hr0.trans_le hck)) hβ₁ϑ
  obtain ⟨ε', hε'⟩ : ∃ e : ℕ → ℝ, e = fun j => β₁ * r * phase1Tol θ ε j := ⟨_, rfl⟩
  rw [← hε']
  have hε'j : ∀ j ∈ Finset.Icc 1 q, ε' j = β₁ * r * ε j := fun j hj => by
    simp only [hε']
    rw [phase1Tol_of_ne θ ε (by have := (Finset.mem_Icc.1 hj).1; omega)]
  have hle : ∀ j ∈ Finset.Icc 1 q, ε' j ≤ ϑ := fun j hj => by
    rw [hε'j j hj]
    calc β₁ * r * ε j ≤ β₁ * ‖c x₀‖ * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hck hβ₁0.le) (hεI j hj).2 (hεI j hj).1.le
            (mul_nonneg hβ₁0.le (norm_nonneg _))
      _ ≤ ϑ := by rw [mul_one]; exact hβ₁ϑ
  have htol : ∀ j ∈ Finset.Icc 1 q, ε' j ∈ Ioc 0 1 := fun j hj =>
    ⟨by rw [hε'j j hj]; have := (hεI j hj).1; positivity, (hle j hj).trans hϑ1⟩
  have hϑ' : Optimization.finMin 1 ε' q ≤ ϑ := (Optimization.finMin_le h1q).trans (hle 1 h1q)
  have hcall := (hR.phase1 k hk1 hkk)
  rw [← hr, ← hε'] at hcall
  have hcall' := hcall.cost_le (flow := 0) (fun y _ => by rw [phi2_apply]; positivity)
    hν.toLipschitzDerivsAnchored hXX₀ (fun y hy hyk => ⟨hy, (norm_le_of_phi2_le hyk).trans hck0⟩)
    hmem (hνM _ ⟨hmem, hck0⟩) hMν0 htol hϑ' hϑ1
  simp only [sub_zero] at hcall'
  -- the logarithm of `ε'_min`
  have hεm' : β₁ * θ * (ε 0 * Optimization.finMin 1 ε q) ≤ Optimization.finMin 1 ε' q := by
    refine Optimization.le_finMin ?_ fun j hj => ?_
    · exact mul_le_one_aux (mul_le_one_aux hβ₁1.le hθ0.le hθ1.le) (mul_pos hε₀.1 hεm0).le
        (mul_le_one_aux hε₀.2 hεm0.le hεm1)
    · rw [hε'j j hj]
      have : θ * ε 0 * Optimization.finMin 1 ε q ≤ r * ε j :=
        mul_le_mul hlo.le (Optimization.finMin_le hj) hεm0.le hr0.le
      calc β₁ * θ * (ε 0 * Optimization.finMin 1 ε q) =
            β₁ * (θ * ε 0 * Optimization.finMin 1 ε q) := by ring
        _ ≤ β₁ * (r * ε j) := mul_le_mul_of_nonneg_left this hβ₁0.le
        _ = β₁ * r * ε j := by ring
  have hlog : |Real.log (Optimization.finMin 1 ε' q)| ≤
      |Real.log (β₁ * θ)| + trqSCLogTerm q ε :=
    Real.abs_log_le_of_mul_le (mul_pos hβ₁0 hθ0) (mul_pos hε₀.1 hεm0)
      (mul_le_one_aux hβ₁1.le hθ0.le hθ1.le) (mul_le_one_aux hε₀.2 hεm0.le hεm1) hεm'
      Optimization.finMin_le_left
  have hε'I : ∀ j ∈ Finset.Icc 1 q, 0 < ε' j ∧ ε' j ≤ 1 := fun j hj => htol j hj
  have hν0 : 0 ≤ phi2 c (xP (k - 1)) := by rw [phi2_apply]; positivity
  have hB0 : 0 ≤ Optimization.kappaBTRq P := Optimization.kappaBTRq_nonneg P
  refine ⟨hcall'.1.trans ?_, hcall'.2.trans ?_⟩
  · have h1 := le_innerEvalBound_succ
      (Optimization.trqCallKappaA_nonneg (P := P) (L := Lν) (q := q) hϑ0 hMν0) hν0 hq hε'I
    have h2 := mul_le_mul_of_nonneg_left hlog hB0
    linarith
  · have := le_innerEvalBound_succ
      (Optimization.trqCallKappaS_nonneg (P := P) (L := Lν) (q := q) hϑ0 hMν0) hν0 hq hε'I
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
`Λ = |log(ε₀ ε_min)|` (`trqSCLogTerm`).

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
            (κF + κL * trqSCLogTerm q ε) * tpqpOrderF (fun _ => (q : ℝ) + 1) q ε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤ κD * tpqpOrderD (fun _ => (q : ℝ) + 1) q ε) ∧
        (‖c (xP k₁)‖ ≤ θ * ε 0 → ∃ kε, D.IsEnd f c X q θ ε kε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) + D.funEvals kε ≤
            (κF + κL * trqSCLogTerm q ε) * tpqpOrderF (fun _ => (q : ℝ) + 1) q ε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) + D.derivEvals kε ≤
            κD * tpqpOrderD (fun _ => (q : ℝ) + 1) q ε) := by
  have hϑ0 : 0 < ϑ := hβ0.trans_le hβϑ
  obtain ⟨LA, LB, BA, BB, hν⟩ := exists_nu_trq hc
  obtain ⟨Lμ, Bμ, hμ⟩ := exists_mu_trq hc hf
  have hMν0 : 0 < Optimization.finMax 1 (fun j => BA j + BB j * ‖c x₀‖) q := finMax_one_pos
  have hMμ0 : 0 < Optimization.finMax 1 Bμ q := finMax_one_pos
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
      (zero_le_one.trans Optimization.one_le_trqKappaUns) hκρ (finMax_one_pos (B := Bf))
      (abs_nonneg (fup - flow + 1)) zero_le_one hθ0 hθ1 hβ0
  obtain ⟨U0, hU0⟩ : ∃ x, x = trqSCKappaUnc0 P Lμ ϑ (Optimization.finMax 1 Bμ q) q β θ :=
    ⟨_, rfl⟩
  have hU00 : 0 ≤ U0 := hU0 ▸ trqSCKappaUnc0_nonneg β θ
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
  obtain ⟨Λ, hΛ⟩ : ∃ x, x = trqSCLogTerm q ε := ⟨_, rfl⟩
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
    (add_le_add (phase1Bound_le (π := fun _ : ℕ => (q : ℝ) + 1) hκA0 (norm_nonneg _)
      (fun j hj => (hε j hj).1) hOT) le_rfl)
  have hD1 := (lemma_14_3_7_add h hθ0 hπ1 hκS0 fun k hk => (hcost k hk).2).trans
    (add_le_add (phase1Bound_le (π := fun _ : ℕ => (q : ℝ) + 1) hκS0 (norm_nonneg _)
      (fun j hj => (hε j hj).1) hOT) le_rfl)
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
  have hin := (hR.phase2 hc1).isInnerPhaseRunStrong h2 hq (hμ := fun t => (hμ t).1)
    (fun t => (hμ t).2) hMμ0 hc.subset hβϑ hϑ1
  rw [← hU0, ← hg'] at hin
  obtain ⟨l, hl, hmin⟩ := Optimization.exists_finMin_eq hq fun j hj => (hεI j hj).2
  have hκunc : 0 ≤ U0 + trqSCLogTerm q ε / g := by rw [← hΛ]; positivity
  obtain ⟨kε, hend, hF2, hD2⟩ := hord (ρ' := fun _ => ε 0 * Optimization.finMin 1 ε q) hκunc h2
    hin (fun _ _ => mul_pos hε₀.1 hεm0)
    (fun l _ => ⟨by positivity, le_rfl⟩) (hB.of_le hεβ) (le_abs_self _)
    (fun _ hy => hf.contDiffAt_of_le le_rfl hy) (fun _ hy => hc.contDiffAt_of_le le_rfl hy)
    (fun _ hy _ => hf.norm_iteratedFDeriv_le_finMax le_rfl (hf.subset hy)) hO0 hOT
    (fun j hj => by
      rw [one_mul]
      refine (inv_bad_le_trq hε₀.1 hε₀.2 hεm0 hεm1 (Optimization.finMin_le hj)
        (Finset.mem_Icc.1 hj).1 (Finset.mem_Icc.1 hj).2).trans ?_
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
  have hΛ : trqSCLogTerm 1 ε = |Real.log (ε 0 * ε 1)| := by
    have hε1 := hε 1 (by simp)
    unfold trqSCLogTerm
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

open Classical in
/-- **One INNER call of Phase 2 by TRq-SC exists** from every `(x, t)` with `x ∈ X` and
`θε₀ ≤ ‖r(x, t)‖ ≤ ε₀`: TRq-SC on `μ(·, t)` with threshold `ϑ` and tolerances `β ‖r(x, t)‖ ε`
(which terminates, `Optimization.IsTRqRun.complexity`), stopped at its termination or as
soon as `‖r(·, t)‖ < θε₀` (`Optimization.exists_isTRqCallOut_of_stop`), returning the radii
`min(Δ_e, ϑ)`; its output satisfies (14.3.32) (the first or the third test). -/
theorem exists_trqCallData {t : ℝ} {L : ℕ → ℝ} {X₀ : Set ℝⁿ}
    (hμ : Chapter12.AssumptionD1pLAnchored (Constrained.targetMerit f c t) X₀
      (muSublevel f c X t) q L) (hXX₀ : X ⊆ X₀) (P : Optimization.TRqParams) (hq : 1 ≤ q)
    (hX : IsClosed X) (hθ0 : 0 < θ) (hβ0 : 0 < β) (hβθ : β ≤ θ) (hβϑ : β ≤ ϑ) (hϑ1 : ϑ ≤ 1)
    (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) {x : ℝⁿ} (hx : x ∈ X)
    (hlo : θ * ε 0 ≤ Constrained.targetResidual f c t x)
    (hhi : Constrained.targetResidual f c t x ≤ ε 0) :
    ∃ o : CallOut n, o.xi 0 = x ∧ o.xi o.e ∈ X ∧
      (∀ j ∈ Finset.Icc 1 q, 0 < o.δ j ∧ o.δ j ≤ 1) ∧
      (Constrained.targetResidual f c t (o.xi o.e) < θ * ε 0 ∨
        meritCrit f c X q ε t (o.xi o.e) o.δ) ∧
      (∀ i < o.e, Constrained.targetMerit f c t (o.xi (i + 1)) ≤
        Constrained.targetMerit f c t (o.xi i)) ∧
      (∀ i < o.e, θ * ε 0 ≤ Constrained.targetResidual f c t (o.xi i)) ∧
      Constrained.targetResidual f c t (o.xi o.e) ≤ Constrained.targetResidual f c t x ∧
      Optimization.IsTRqCallOut (Constrained.targetMerit f c t) X P q
        (fun j => β * Constrained.targetResidual f c t x * ε j) ϑ o.xi o.e o.succ o.δ := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = Constrained.targetResidual f c t x := ⟨_, rfl⟩
  rw [← hρ] at hlo hhi ⊢
  have hεI : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1 := fun j hj =>
    hε j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
  have hε₀ := hε 0 (by simp)
  have hρ0 : 0 < ρ := lt_of_lt_of_le (mul_pos hθ0 hε₀.1) hlo
  have hβ1 : β ≤ 1 := hβϑ.trans hϑ1
  have hle : ∀ j ∈ Finset.Icc 1 q, β * ρ * ε j ≤ β := fun j hj => by
    have h1 : ρ * ε j ≤ 1 := by nlinarith [hεI j hj]
    nlinarith [hεI j hj]
  have hε' : ∀ j ∈ Finset.Icc 1 q, β * ρ * ε j ∈ Ioc 0 1 := fun j hj =>
    ⟨by have := (hεI j hj).1; positivity, (hle j hj).trans hβ1⟩
  have h1q : 1 ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, hq⟩
  have hϑ' : Optimization.finMin 1 (fun j => β * ρ * ε j) q ≤ ϑ :=
    (Optimization.finMin_le h1q).trans ((hle 1 h1q).trans hβϑ)
  have hS : ∀ y ∈ X, Constrained.targetMerit f c t y ≤ Constrained.targetMerit f c t x →
      y ∈ muSublevel f c X t := fun y hy hyx =>
    ⟨hy, (Constrained.targetMerit_le_targetMerit_iff.1 hyx).trans ((hρ ▸ hhi).trans hε₀.2)⟩
  obtain ⟨xi, e, succ, δ, hcall, hx0, hmem, hδ, hmono, hdec, hlow, hend⟩ :=
    Optimization.exists_isTRqCallOut_of_stop (flow := 0) hX
      (fun y _ => Constrained.targetMerit_nonneg) hμ.toLipschitzDerivsAnchored hXX₀ hx hS hε' hϑ'
      hϑ1 P (fun y => Constrained.targetResidual f c t y < θ * ε 0)
  refine ⟨⟨xi, e, succ, fun _ => δ⟩, hx0, hmem, fun _ _ => hδ, ?_, hmono,
    fun i hi => not_lt.1 (hlow i hi), ?_, hcall⟩
  · by_cases hlt : Constrained.targetResidual f c t (xi e) < θ * ε 0
    · exact Or.inl hlt
    · -- the call has terminated: the certificate gives the third test of (14.3.32)
      refine Or.inr fun j hj => ((hend.resolve_left hlt) j hj).trans ?_
      have hge := not_lt.1 hlt
      have hεj := (hεI j hj).1
      have : β * ρ ≤ Constrained.targetResidual f c t (xi e) := by nlinarith
      have : β * ρ * ε j ≤ ε j * Constrained.targetResidual f c t (xi e) := by nlinarith
      change β * ρ * ε j * δ ^ j / (j ! : ℝ) ≤
        ε j * Constrained.targetResidual f c t (xi e) * δ ^ j / (j ! : ℝ)
      have := hδ.1
      gcongr
  · rw [hρ]
    exact Constrained.targetMerit_le_targetMerit_iff.1 hdec

/-- **TPqp-GC runs with INNER = TRq-SC in both phases exist** (so the class `IsTPqpGCTRqSCRun` of
`theorem_14_3_9_trq` is not empty) under X.CNe (`X` closed), c.D1qLB.X and f.D1qLB.X (on an open
convex `X₀ ⊇ X`), for all TRq parameters, `θ ∈ (0, 1)`, `β ∈ (0, θ]` with `β ≤ ϑ ≤ 1`,
`ε ∈ (0, 1]^{q+1}`, `β₁ ∈ (0, 1)` with `β₁ ‖c(x₀)‖ < 1` and `β₁ ‖c(x₀)‖ ≤ ϑ`, and `x₀ ∈ X`:
Phase 1 is LENq-SC with TRq-SC calls on `ν`, Phase 2 has the calls of `exists_trqCallData`
(`phase2_core_of`). -/
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
        exact ⟨hz, (norm_le_of_phi2_le hzy).trans hy0⟩
      obtain ⟨kε, hhit, hmem, hrad, hcert, -, -⟩ := Optimization.IsTRqRun.complexity
        (flow := 0) (fun z _ => by rw [phi2_apply]; positivity) (hν x₀).1.toLipschitzDerivsAnchored
        hc.subset hA hxr0 hε' hϑ' hϑ1 hr
      have hsub := hr.mem_sublevel hxr0 (fun j hj => (hε' j hj).1.le) hϑ0.le kε hhit.2
      refine ⟨(x kε, fun _ => min (Δ kε) ϑ, Optimization.funEvalCount kε,
        Optimization.derivEvalCount (fun k => P.η₁ ≤ Optimization.trqRatio (phi2 c)
          (fun k => ftaylorSeries ℝ (phi2 c) (x k)) x s jk k) kε),
        hmem, ?_, fun _ _ => hrad, hcert, ⟨x, s, Δ, jk, d, kε, hr, hhit, hx0, rfl,
          fun _ _ => rfl, rfl, rfl⟩⟩
      have := hsub.2
      rw [hx0] at this
      exact norm_le_of_phi2_le this
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
    -- Phase 2 with the calls of `exists_trqCallData`
    obtain ⟨D, hD, hcallsD⟩ := phase2_core_of hθ0 hθ1 hβ0 hβθ hε hmem hc1
      (fun x t o => Optimization.IsTRqCallOut (Constrained.targetMerit f c t) X P q
        (fun j => β * Constrained.targetResidual f c t x * ε j) ϑ o.xi o.e o.succ o.δ)
      (fun x t hx hlo hhi _ => exists_trqCallData (hμ t).1 hc.subset P hq hX hθ0 hβ0 hβθ hβϑ
        hϑ1 hε hx hlo hhi)
    exact ⟨xP, δP, k₁, D, nF, nD, ⟨⟨hxP0, hrun, hhit, fun _ => hD⟩, hcalls',
      fun _ k hk1 hk => (hcallsD k hk1 hk).2⟩⟩
  · exact ⟨xP, δP, k₁, ⟨fun _ => x₀, fun _ => 0, fun _ _ => 0, fun _ _ => x₀, fun _ => 0,
      fun _ _ => False⟩, nF, nD, ⟨⟨hxP0, hrun, hhit, fun h => absurd h hc1⟩, hcalls',
      fun h => absurd h hc1⟩⟩

end Existence

end TRqSC


section TRqLog

set_option hygiene false in
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- The objective `f(x) = x₁` of the example (`x₁ = v 0`). -/
noncomputable def trqLogF : ℝ² → ℝ := fun v => v 0

/-- The constraint `c(x) = x₂` of the example, as a map into `ℝ¹` (`x₂ = v 1`). -/
noncomputable def trqLogC : ℝ² → EuclideanSpace ℝ (Fin 1) := fun v => EuclideanSpace.single 0 (v 1)

/-- The feasible set `X = [0, 2] × [-1, 1]` of the example. -/
def trqLogX : Set ℝ² := {v | 0 ≤ v 0 ∧ v 0 ≤ 2 ∧ -1 ≤ v 1 ∧ v 1 ≤ 1}

/-- The starting point `x₀ = (2, 0)` of the example. -/
noncomputable def trqLogX₀ : ℝ² := EuclideanSpace.single 0 2

/-- `‖c(v)‖ = |v₂|`. -/
theorem norm_trqLogC (v : ℝ²) : ‖trqLogC v‖ = |v 1| := by
  simp [trqLogC]

/-- `μ(v, t) = (v₂² + (v₁ - t)²)/2`. -/
theorem trqLogMerit_eq (t : ℝ) : Constrained.targetMerit trqLogF trqLogC t =
    fun v => ((v 1) ^ 2 + (v 0 - t) ^ 2) / 2 := by
  funext v
  simp [Constrained.targetMerit_def, norm_trqLogC, trqLogF, sq_abs]

/-- `‖r(v, t)‖ = √(v₂² + (v₁ - t)²)`. -/
theorem trqLogResid_eq (t : ℝ) (v : ℝ²) : Constrained.targetResidual trqLogF trqLogC t v =
    √((v 1) ^ 2 + (v 0 - t) ^ 2) := by
  simp [Constrained.targetResidual_def, norm_trqLogC, trqLogF, sq_abs]

/-- The derivative of `μ(·, t)`: `s ↦ v₂ s₂ + (v₁ - t) s₁`. -/
theorem hasFDerivAt_trqLogMerit (t : ℝ) (v : ℝ²) :
    HasFDerivAt (fun w : ℝ² => ((w 1) ^ 2 + (w 0 - t) ^ 2) / 2)
      ((v 1) • (EuclideanSpace.proj 1 : ℝ² →L[ℝ] ℝ) + (v 0 - t) • EuclideanSpace.proj 0) v := by
  have h1 : HasFDerivAt (fun w : ℝ² => w 1) (EuclideanSpace.proj 1 : ℝ² →L[ℝ] ℝ) v :=
    (EuclideanSpace.proj 1 : ℝ² →L[ℝ] ℝ).hasFDerivAt
  have h0 : HasFDerivAt (fun w : ℝ² => w 0) (EuclideanSpace.proj 0 : ℝ² →L[ℝ] ℝ) v :=
    (EuclideanSpace.proj 0 : ℝ² →L[ℝ] ℝ).hasFDerivAt
  have := ((h1.pow 2).add ((h0.sub_const t).pow 2)).mul_const (1 / 2 : ℝ)
  convert this using 1
  · funext w; simp only [Pi.add_apply]; ring
  · ext s; simp; ring

/-- The first-order Taylor decrement of `μ(·, t)` at `v`:
`ΔT₁(s) = -(v₂ s₂ + (v₁ - t) s₁)`. -/
theorem taylorDecrement_trqLogMerit (t : ℝ) (v s : ℝ²) :
    (ftaylorSeries ℝ (Constrained.targetMerit trqLogF trqLogC t) v).taylorDecrement 1 s =
      -(v 1 * s 1 + (v 0 - t) * s 0) := by
  rw [FormalMultilinearSeries.taylorDecrement_one_apply, trqLogMerit_eq]
  change -(iteratedFDeriv ℝ 1 _ v (fun _ => s)) = _
  rw [iteratedFDeriv_one_apply, (hasFDerivAt_trqLogMerit t v).fderiv]
  simp


/-- `μ(·, t)` is quadratic with unit Hessian:
`μ(v + s) = μ(v) + ∇μ(v)·s + ‖s‖²/2`. -/
theorem trqLogMerit_add (t : ℝ) (v s : ℝ²) :
    Constrained.targetMerit trqLogF trqLogC t (v + s) =
      Constrained.targetMerit trqLogF trqLogC t v +
      (v 1 * s 1 + (v 0 - t) * s 0) + ‖s‖ ^ 2 / 2 := by
  rw [trqLogMerit_eq, trqLog_norm_sq]
  simp only [PiLp.add_apply]
  ring

/-- `|∇μ(v)·s| ≤ ‖r(v, t)‖ ‖s‖` (Cauchy–Schwarz). -/
theorem trqLog_abs_lin_le (t : ℝ) (v s : ℝ²) :
    |v 1 * s 1 + (v 0 - t) * s 0| ≤ Constrained.targetResidual trqLogF trqLogC t v * ‖s‖ := by
  rw [trqLogResid_eq, ← Real.sqrt_sq (norm_nonneg s), trqLog_norm_sq,
    ← Real.sqrt_mul (by positivity)]
  apply Real.abs_le_sqrt
  nlinarith [sq_nonneg (v 1 * s 0 - (v 0 - t) * s 1)]

/-- Membership in `X`. -/
theorem trqLogX_mem {v : ℝ²} : v ∈ trqLogX ↔ 0 ≤ v 0 ∧ v 0 ≤ 2 ∧ -1 ≤ v 1 ∧ v 1 ≤ 1 := Iff.rfl

/-- The two coordinate directions give the lower bounds `(v₀ - t) δ` and `|v₁| δ` for the
first-order measure of `μ(·, t)` at `v ∈ X` with `t ≤ v₀` and `δ ≤ min(v₀, 1)`. -/
theorem trqLog_measure_ge {t δ : ℝ} {v : ℝ²} (hv : v ∈ trqLogX) (hδ0 : 0 ≤ δ) (hδv : δ ≤ v 0)
    (hδ1 : δ ≤ 1) :
    (v 0 - t) * δ ≤ Optimization.taylorMeasure
        (ftaylorSeries ℝ (Constrained.targetMerit trqLogF trqLogC t) v) 1 δ {d | v + d ∈ trqLogX} ∧
      |v 1| * δ ≤ Optimization.taylorMeasure
        (ftaylorSeries ℝ (Constrained.targetMerit trqLogF trqLogC t) v) 1 δ
          {d | v + d ∈ trqLogX} := by
  obtain ⟨h0, h2, h3, h4⟩ := hv
  constructor
  · have hd : ((-δ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : ℝ²) ∈
        closedBall (0 : ℝ²) δ ∩ {d | v + d ∈ trqLogX} := by
      refine ⟨mem_closedBall_zero_iff.2 ?_, ?_⟩
      · rw [norm_smul]; simp [abs_of_nonneg hδ0]
      · simp only [Set.mem_ofPred_eq, trqLogX_mem, PiLp.add_apply, PiLp.smul_apply,
          PiLp.single_apply]
        norm_num
        refine ⟨by linarith, by linarith, h3, h4⟩
    have := Optimization.taylorDecrement_le_taylorMeasure
      (ftaylorSeries ℝ (Constrained.targetMerit trqLogF trqLogC t) v) 1 hd
    rw [taylorDecrement_trqLogMerit] at this
    simp only [PiLp.smul_apply, PiLp.single_apply] at this
    norm_num at this
    linarith
  · rcases le_total 0 (v 1) with hs | hs
    · have hd : ((-δ) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) : ℝ²) ∈
          closedBall (0 : ℝ²) δ ∩ {d | v + d ∈ trqLogX} := by
        refine ⟨mem_closedBall_zero_iff.2 ?_, ?_⟩
        · rw [norm_smul]; simp [abs_of_nonneg hδ0]
        · simp only [Set.mem_ofPred_eq, trqLogX_mem, PiLp.add_apply, PiLp.smul_apply,
            PiLp.single_apply]
          norm_num
          refine ⟨h0, h2, by linarith, by linarith⟩
      have := Optimization.taylorDecrement_le_taylorMeasure
        (ftaylorSeries ℝ (Constrained.targetMerit trqLogF trqLogC t) v) 1 hd
      rw [taylorDecrement_trqLogMerit] at this
      simp only [PiLp.smul_apply, PiLp.single_apply] at this
      norm_num at this
      rw [abs_of_nonneg hs]
      linarith
    · have hd : (δ • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) : ℝ²) ∈
          closedBall (0 : ℝ²) δ ∩ {d | v + d ∈ trqLogX} := by
        refine ⟨mem_closedBall_zero_iff.2 ?_, ?_⟩
        · rw [norm_smul]; simp [abs_of_nonneg hδ0]
        · simp only [Set.mem_ofPred_eq, trqLogX_mem, PiLp.add_apply, PiLp.smul_apply,
            PiLp.single_apply]
          norm_num
          refine ⟨h0, h2, by linarith, by linarith⟩
      have := Optimization.taylorDecrement_le_taylorMeasure
        (ftaylorSeries ℝ (Constrained.targetMerit trqLogF trqLogC t) v) 1 hd
      rw [taylorDecrement_trqLogMerit] at this
      simp only [PiLp.smul_apply, PiLp.single_apply] at this
      norm_num at this
      rw [abs_of_nonpos hs]
      linarith

/-- (14.3.34) fails at every `v ∈ X` with `t ≤ v₀`, positive residual and radius
`δ ≤ min(v₀, 1)`, for `ε₁ = 1/2` and every `q ≥ 1` (its first-order part fails). -/
theorem trqLog_not_meritCrit {q : ℕ} (hq : 1 ≤ q) {t : ℝ} {v : ℝ²} {ε δo : ℕ → ℝ}
    (hε1 : ε 1 = 1 / 2) (hv : v ∈ trqLogX)
    (ht : t ≤ v 0) (hρ : 0 < Constrained.targetResidual trqLogF trqLogC t v) (hδ0 : 0 < δo 1)
    (hδv : δo 1 ≤ v 0) (hδ1 : δo 1 ≤ 1) : ¬ meritCrit trqLogF trqLogC trqLogX q ε t v δo := by
  intro hm
  have h := hm 1 (Finset.mem_Icc.2 ⟨le_rfl, hq⟩)
  obtain ⟨ha, hb⟩ := trqLog_measure_ge (t := t) hv hδ0.le hδv hδ1
  rw [hε1] at h
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one] at h
  set ρ := Constrained.targetResidual trqLogF trqLogC t v with hρdef
  have hsq : ρ ^ 2 = (v 1) ^ 2 + (v 0 - t) ^ 2 := by
    rw [hρdef, trqLogResid_eq, Real.sq_sqrt (by positivity)]
  have h1 : v 0 - t ≤ ρ / 2 := by nlinarith
  have h2 : |v 1| ≤ ρ / 2 := by nlinarith
  have h3 : (v 1) ^ 2 ≤ (ρ / 2) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  have h4 : (v 0 - t) ^ 2 ≤ (ρ / 2) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
  nlinarith


/-- At `v ∈ X` with `t ≤ v₁` and `v₁ ≥ 1`, positive residual `ρ`, radius `δ ∈ (0, 1]` and
`β ≤ 1`, the first-order measure of `μ(·, t)` exceeds `β ρ δ/2`: it is at least
`max(v₁ - t, |v₂|) δ ≥ ρ δ/√2` (`trqLog_measure_ge`). -/
theorem trqLog_measure_gt {t δ β : ℝ} {v : ℝ²} (hv : v ∈ trqLogX) (ht : t ≤ v 0) (hx1 : 1 ≤ v 0)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hβ1 : β ≤ 1)
    (hρ : 0 < Constrained.targetResidual trqLogF trqLogC t v) :
    β * Constrained.targetResidual trqLogF trqLogC t v * (1 / 2) * δ <
      Optimization.taylorMeasure (ftaylorSeries ℝ (Constrained.targetMerit trqLogF trqLogC t) v) 1
        δ {d | v + d ∈ trqLogX} := by
  obtain ⟨ha, hb⟩ := trqLog_measure_ge (t := t) hv hδ0.le (hδ1.trans hx1) hδ1
  set M := Optimization.taylorMeasure
    (ftaylorSeries ℝ (Constrained.targetMerit trqLogF trqLogC t) v) 1 δ {d | v + d ∈ trqLogX}
  set ρ := Constrained.targetResidual trqLogF trqLogC t v with hρdef
  have hsq : ρ ^ 2 = (v 1) ^ 2 + (v 0 - t) ^ 2 := by
    rw [hρdef, trqLogResid_eq, Real.sq_sqrt (by positivity)]
  by_contra hc
  push Not at hc
  have hρδ : 0 < ρ * δ := mul_pos hρ hδ0
  have hM : M ≤ ρ * δ / 2 := by nlinarith
  have h1 : (v 0 - t) * δ ≤ ρ * δ / 2 := ha.trans hM
  have h2 : |v 1| * δ ≤ ρ * δ / 2 := hb.trans hM
  have h3 : ((v 0 - t) * δ) ^ 2 ≤ (ρ * δ / 2) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (by linarith) hδ0.le) h1 2
  have h4 : (|v 1| * δ) ^ 2 ≤ (ρ * δ / 2) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) hδ0.le) h2 2
  have h5 : (|v 1| * δ) ^ 2 = (v 1) ^ 2 * δ ^ 2 := by rw [mul_pow, sq_abs]
  have h6 : ((v 0 - t) * δ) ^ 2 = (v 0 - t) ^ 2 * δ ^ 2 := by rw [mul_pow]
  have h7 : (ρ * δ) ^ 2 = ((v 1) ^ 2 + (v 0 - t) ^ 2) * δ ^ 2 := by rw [mul_pow, hsq]
  nlinarith

/-- **A TRq-SC call on `μ(·, t)` stays at its start for `L` iterations** (any `q ≥ 1`): if the
call starts at `x_{k,0} ∈ X` with `t ≤ (x_{k,0})_1` and `(x_{k,0})_1 ≥ 1`, the residual
`ρ₀ = ‖r(x_{k,0}, t)‖ ∈ (0, ε₀]`, the tolerance is `ε'_1 = β ρ₀/2` with `β ≤ 1`, `ϑ ≤ 1` and
`4 ε₀/(ς β) ≤ γ₁^L min(Δ₀, ϑ)`, then every iteration `i < min(e, L)` is unsuccessful: the
first-order test fails at `x_{k,0}` (its measure is at least `ρ₀ δ/√2 > ε'_1 δ`), so the step has
order `1`; the radius is at least `4 ρ₀/(ς β)`, so the step has length `> 2 ρ₀` and increases
`μ(·, t)` (`μ` is quadratic with unit Hessian). Hence a call of length `e ≤ L` ends where it
started. -/
theorem trqLog_call_stuck {q : ℕ} (hq : 1 ≤ q) {P : Optimization.TRqParams} {ϑ β ε₀ t : ℝ}
    {xi : ℕ → ℝ²} {e : ℕ} {succ : ℕ → Prop} {δo ε' : ℕ → ℝ}
    (h : Optimization.IsTRqCallOut (Constrained.targetMerit trqLogF trqLogC t) trqLogX P q ε' ϑ
      xi e succ δo)
    (hε' : ε' 1 = β * Constrained.targetResidual trqLogF trqLogC t (xi 0) * (1 / 2))
    (hρ : 0 < Constrained.targetResidual trqLogF trqLogC t (xi 0))
    (hρε : Constrained.targetResidual trqLogF trqLogC t (xi 0) ≤ ε₀) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hϑ : 0 ≤ ϑ) (hϑ1 : ϑ ≤ 1) (hX : xi 0 ∈ trqLogX) (ht : t ≤ (xi 0) 0) (hx1 : 1 ≤ (xi 0) 0)
    {L : ℕ} (hL : 4 * ε₀ / (P.ς * β) ≤ P.γ₁ ^ L * min P.Δ₀ ϑ) (he : e ≤ L) : xi e = xi 0 := by
  obtain ⟨x, s, Δ, jk, d, kε, hr, hhit, hek, hxi, -, -⟩ := h
  set F := Constrained.targetMerit trqLogF trqLogC t with hF
  set ρ₀ := Constrained.targetResidual trqLogF trqLogC t (xi 0) with hρ₀
  have hγ0 := P.γ₁_pos
  have hγ1 := P.γ₁_le_one
  have hς := P.ς_pos
  have hx0 : x 0 = xi 0 := (hxi 0 (Nat.zero_le _)).symm
  have hϑ0 : 0 < ϑ := by
    rcases hϑ.lt_or_eq with h' | h'
    · exact h'
    · exfalso
      have : min P.Δ₀ ϑ = 0 := by rw [← h']; exact min_eq_right P.Δ₀_pos.le
      rw [this, mul_zero] at hL
      have : 0 < 4 * ε₀ / (P.ς * β) := by
        have : 0 < ε₀ := hρ.trans_le hρε
        positivity
      linarith
  -- an iteration at `x₀` with radius `Δ_i ≥ γ₁^i Δ₀` is unsuccessful
  have key := hr.toIsTRRun.eq_zero_of_unsucc (L := L) fun i hiL hk hxi0 hΔi => by
    have hst := Optimization.IsTRqRun.isTRqStep hr hk
    have hΔpos : 0 < Δ i := lt_of_lt_of_le (mul_pos (pow_pos P.γ₁_pos i) P.Δ₀_pos) hΔi
    have hj : jk i = 1 := by
      have hmem := Finset.mem_Icc.1 hst.order_mem
      by_contra hne
      have h1q : (1 : ℕ) ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, hq⟩
      have hle1 := hst.taylorDecrement_le_of_lt 1 h1q (by omega)
      have hw := (hr.witness i (fun l hl => hk l hl.le) 1 h1q).2
      rw [hxi0, hx0] at hle1 hw
      rw [hε'] at hle1
      simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one] at hle1
      set δ := min (Δ i) ϑ with hδ
      have hgt := trqLog_measure_gt hX ht hx1 (lt_min hΔpos hϑ0)
        ((min_le_right _ _).trans hϑ1) hβ1 hρ
      have hw' : P.ς * Optimization.taylorMeasure (ftaylorSeries ℝ F (xi 0)) 1 δ
          {d | xi 0 + d ∈ trqLogX} ≤ P.ς * (β * ρ₀ * (1 / 2) * δ) :=
        (hw.trans hle1).trans_eq (by ring)
      exact absurd (le_of_mul_le_mul_left hw' P.ς_pos) (not_le.2 hgt)
    have hlt := hst.lt_taylorDecrement
    have hle := hst.taylorDecrement_le
    rw [hj] at hlt hle
    simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one] at hlt
    -- the radius
    have hpow : P.γ₁ ^ L ≤ P.γ₁ ^ i := pow_le_pow_of_le_one hγ0.le hγ1 (by omega)
    have hδ : 4 * ε₀ / (P.ς * β) ≤ min (Δ i) ϑ := by
      refine hL.trans ?_
      rw [mul_min_of_nonneg _ _ (pow_nonneg hγ0.le _)]
      refine min_le_min ((mul_le_mul_of_nonneg_right hpow P.Δ₀_pos.le).trans hΔi) ?_
      exact mul_le_of_le_one_left hϑ (pow_le_one₀ hγ0.le hγ1)
    set Pd := (ftaylorSeries ℝ F (x i)).taylorDecrement 1 (s i) with hPd
    have hρ₀' : Constrained.targetResidual trqLogF trqLogC t (x i) = ρ₀ := by
      rw [hxi0, hx0]
    have hPd_big : 2 * ρ₀ ^ 2 < Pd := by
      have h1 : P.ς * ε' 1 * min (Δ i) ϑ < Pd := hlt.trans_le hle
      rw [hε'] at h1
      have h2 : P.ς * (β * ρ₀ * (1 / 2)) * (4 * ε₀ / (P.ς * β)) = 2 * ρ₀ * ε₀ := by
        field_simp; ring
      have h3 : P.ς * (β * ρ₀ * (1 / 2)) * (4 * ε₀ / (P.ς * β)) ≤
          P.ς * (β * ρ₀ * (1 / 2)) * min (Δ i) ϑ :=
        mul_le_mul_of_nonneg_left hδ (by positivity)
      nlinarith
    have hPd_le : Pd ≤ ρ₀ * ‖s i‖ := by
      have := trqLog_abs_lin_le t (x i) (s i)
      rw [hρ₀'] at this
      rw [hPd, hF, taylorDecrement_trqLogMerit]
      exact (neg_le_abs _).trans this
    have hPd0 : 0 < Pd := lt_of_le_of_lt (by positivity) hPd_big
    have hs : 2 * ρ₀ < ‖s i‖ := by
      by_contra hc
      push Not at hc
      nlinarith [mul_le_mul_of_nonneg_left hc hρ.le]
    change Optimization.trqRatio F (fun k => ftaylorSeries ℝ F (x k)) x s jk i < P.η₁
    rw [Optimization.trqRatio_eq, hj, Optimization.reductionRatio_def, ← hPd]
    have hadd := trqLogMerit_add t (x i) (s i)
    rw [← hF] at hadd
    have hlin : (x i) 1 * (s i) 1 + ((x i) 0 - t) * (s i) 0 = -Pd := by
      rw [hPd, hF, taylorDecrement_trqLogMerit]; ring
    rw [hadd, hlin]
    have hnum : F (x i) - (F (x i) + -Pd + ‖s i‖ ^ 2 / 2) < 0 := by
      have : 2 * Pd < ‖s i‖ ^ 2 := by
        have := mul_le_mul_of_nonneg_left hPd_le (le_of_lt (by positivity : (0:ℝ) < 2))
        nlinarith
      linarith
    exact (div_neg_of_neg_of_pos hnum hPd0).trans P.η₁_pos
  rw [hxi e le_rfl, hxi 0 (Nat.zero_le _),
    (key e he fun l hl => hhit.2 l (lt_of_lt_of_le hl hek)).1]


section Run

variable {θ β : ℝ} {ε : ℕ → ℝ} {x₁ : ℝ²} {D : TPqpSeq 2} {q : ℕ}

/-- `f(x_{k+1}) ≥ t_k - ε₀` along Phase 2. -/
theorem trqLog_f_succ_ge (h2 : IsTPqpGCPhase2 trqLogF trqLogC trqLogX q θ β ε x₁ D) {k : ℕ}
    (hk1 : 1 ≤ k)
    (hk : D.Before trqLogF trqLogC trqLogX q θ ε k) : D.t k - ε 0 ≤ trqLogF (D.x (k + 1)) := by
  have h1 := (Constrained.abs_sub_le_targetResidual (f := trqLogF) (c := trqLogC) (t := D.t k)
    (x := D.x (k + 1)))
  have h2' := h2.residual_succ_le hk1 hk
  have h3 := (h2.isTargetSequence hk).residual_le h2.θ_lt_one.le h2.ε₀_pos.le hk1 le_rfl
  have := neg_abs_le (trqLogF (D.x (k + 1)) - D.t k)
  linarith

/-- **The targets decrease by at most `2 ε₀` per outer iteration**: starting from
`x₁ = (2, 0)`, `t_k ≥ 2 - (2k - 1) ε₀` for every outer iteration `k ≥ 1` reached. -/
theorem trqLog_target_ge (h2 : IsTPqpGCPhase2 trqLogF trqLogC trqLogX q θ β ε trqLogX₀ D) :
    ∀ k, 1 ≤ k → D.Before trqLogF trqLogC trqLogX q θ ε k → 2 - (2 * k - 1) * ε 0 ≤ D.t k := by
  have hε₀ := h2.ε₀_pos
  intro k hk1
  induction k, hk1 using Nat.le_induction with
  | base =>
    intro _
    rw [h2.t_one]
    have hc : ‖trqLogC trqLogX₀‖ = 0 := by simp [norm_trqLogC, trqLogX₀]
    have hf : trqLogF trqLogX₀ = 2 := by simp [trqLogF, trqLogX₀]
    rw [hc, hf, show ε 0 ^ 2 - (0 : ℝ) ^ 2 = ε 0 ^ 2 by ring, Real.sqrt_sq hε₀.le]
    push_cast; linarith
  | succ k hk1 ih =>
    intro hK
    have hk := hK.mono k.le_succ
    have ihk := ih hk
    have hs : ¬ D.Stop trqLogF trqLogC trqLogX q θ ε k := hK k hk1 (Nat.lt_succ_self k)
    have hf := trqLog_f_succ_ge h2 hk1 hk
    push_cast
    rcases Constrained.TargetFollowingSeq.ka_or_kb_of_not_stop hs with ha | hb
    · rw [h2.t_succ_a k hk1 hk ha]
      have : √(ε 0 ^ 2 - ‖trqLogC (D.x (k + 1))‖ ^ 2) ≤ ε 0 := by
        calc √(ε 0 ^ 2 - ‖trqLogC (D.x (k + 1))‖ ^ 2) ≤ √(ε 0 ^ 2) :=
              Real.sqrt_le_sqrt (by nlinarith [norm_nonneg (trqLogC (D.x (k + 1)))])
          _ = ε 0 := Real.sqrt_sq hε₀.le
      linarith
    · rw [h2.t_succ_b k hk1 hk hb]
      linarith

/-- **Phase 2 cannot stop early**: at an outer iteration `k ≥ 1` reached with
`(2k + 1) ε₀ ≤ 1`, the iterate `x_{k+1}` has `f ≥ 1`, so (14.3.34) fails there for every
target that Step 2 can produce, and the Step-1 output condition (14.3.32) excludes case (c). -/
theorem trqLog_not_stop (hq : 1 ≤ q)
    (h2 : IsTPqpGCPhase2 trqLogF trqLogC trqLogX q θ β ε trqLogX₀ D) (hε1 : ε 1 = 1 / 2)
    {k : ℕ} (hk1 : 1 ≤ k) (hk : D.Before trqLogF trqLogC trqLogX q θ ε k)
    (hkε : (2 * k + 1) * ε 0 ≤ 1) : ¬ D.Stop trqLogF trqLogC trqLogX q θ ε k := by
  have hε₀ := h2.ε₀_pos
  have hθ := h2.θ_pos
  have ht := trqLog_target_ge h2 k hk1 hk
  have hf := trqLog_f_succ_ge h2 hk1 hk
  have hy1 : 1 ≤ (D.x (k + 1)) 0 := by
    change 1 ≤ trqLogF (D.x (k + 1)); nlinarith
  have hyX := h2.mem_succ k hk1 hk
  obtain ⟨hδ0, hδ1⟩ := h2.radius_mem k hk1 hk 1 (Finset.mem_Icc.2 ⟨le_rfl, hq⟩)
  have hδy : D.δ (k + 1) 1 ≤ (D.x (k + 1)) 0 := hδ1.trans hy1
  have hθε : 0 < θ * ε 0 := mul_pos hθ hε₀
  rintro (⟨hna, hnb⟩ | ⟨hab, hm⟩)
  · -- case (c)
    have hge : θ * ε 0 ≤ Constrained.targetResidual trqLogF trqLogC (D.t k) (D.x (k + 1)) :=
      not_lt.1 hna
    have hft : D.t k ≤ trqLogF (D.x (k + 1)) := not_lt.1 fun hlt => hnb ⟨hge, hlt⟩
    rcases h2.output k hk1 hk with h | h | h
    · exact hna h
    · exact hnb ⟨hge, h⟩
    · exact trqLog_not_meritCrit hq hε1 hyX hft (hθε.trans_le hge) hδ0 hδy hδ1 h
  · change meritCrit trqLogF trqLogC trqLogX q ε (D.t (k + 1)) (D.x (k + 1)) (D.δ (k + 1)) at hm
    rcases hab with ha | hb
    · rw [h2.t_succ_a k hk1 hk ha] at hm
      have hc : ‖trqLogC (D.x (k + 1))‖ ≤ ε 0 :=
        Constrained.norm_le_targetResidual.trans (ha.le.trans
          (mul_le_of_le_one_left hε₀.le h2.θ_lt_one.le))
      refine trqLog_not_meritCrit hq hε1 hyX ?_ ?_ hδ0 hδy hδ1 hm
      · change _ ≤ trqLogF (D.x (k + 1)); linarith [Real.sqrt_nonneg
          (ε 0 ^ 2 - ‖trqLogC (D.x (k + 1))‖ ^ 2)]
      · rw [Constrained.targetResidual_sub_sqrt hε₀.le hc]; exact hε₀
    · rw [h2.t_succ_b k hk1 hk hb] at hm
      refine trqLog_not_meritCrit hq hε1 hyX ?_ ?_ hδ0 hδy hδ1 hm
      · change _ ≤ trqLogF (D.x (k + 1)); linarith [hb.2]
      · rw [Constrained.targetResidual_two_mul_sub]; exact hθε.trans_le hb.1

end Run


section Count

variable {P : Optimization.TRqParams} {ϑ θ β β₁ : ℝ} {ε : ℕ → ℝ} {xP : ℕ → ℝ²}
  {δP : ℕ → ℕ → ℝ} {k₁ : ℕ} {D : TPqpSeq 2} {q : ℕ} {nF₁ nD₁ : ℕ → ℕ}

/-- Phase 1 stops at once: `c(x₀) = 0`. -/
theorem trqLog_phase1 (h : algorithm_14_3_2 trqLogF trqLogC trqLogX q θ β₁ β ε trqLogX₀ xP δP k₁ D)
    (hθ : 0 < θ) : k₁ = 0 ∧ xP k₁ = trqLogX₀ := by
  have hε₀ : 0 < ε 0 := by
    have := h.phase1.ε_pos 0 (by simp)
    rw [phase1Tol_zero] at this
    exact pos_of_mul_pos_right this hθ.le
  have hstop : lenStop trqLogC trqLogX q (phase1Tol θ ε) xP δP 0 := by
    left
    rw [h.start, phase1Tol_zero]
    simp only [norm_trqLogC, trqLogX₀]
    simp only [PiLp.single_apply]
    norm_num
    positivity
  have hk : k₁ = 0 := by
    by_contra hne
    exact h.phase1_end.2 0 (Nat.pos_of_ne_zero hne) hstop
  exact ⟨hk, by rw [hk, h.start]⟩

/-- **Every call of an early outer iteration is long**: at an outer iteration `k ≥ 1` reached
with `(2k - 1) ε₀ ≤ 1`, a TRq-SC call has more than `L` iterations when
`4 ε₀/(ς β) ≤ γ₁^L min(Δ₀, ϑ)`: otherwise it returns `x_{k+1} = x_k`, where no test of
(14.3.32) holds. -/
theorem trqLog_call_long (hq : 1 ≤ q)
    (h2 : IsTPqpGCPhase2 trqLogF trqLogC trqLogX q θ β ε trqLogX₀ D)
    (hcalls : IsTRqSCPhase2Calls trqLogF trqLogC trqLogX q P ϑ θ β ε D) (hε1 : ε 1 = 1 / 2)
    (hϑ : 0 ≤ ϑ) (hϑ1 : ϑ ≤ 1) {L : ℕ} (hL : 4 * ε 0 / (P.ς * β) ≤ P.γ₁ ^ L * min P.Δ₀ ϑ) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : D.Before trqLogF trqLogC trqLogX q θ ε k) (hkε : (2 * k - 1) * ε 0 ≤ 1) :
    L < D.e k := by
  by_contra hle
  push Not at hle
  have hε₀ := h2.ε₀_pos
  have hθε : 0 < θ * ε 0 := mul_pos h2.θ_pos hε₀
  have hlo := h2.le_targetResidual k hk1 hk
  have hhi := (h2.isTargetSequence hk).residual_le h2.θ_lt_one.le hε₀.le hk1 le_rfl
  have h0 := h2.inner_zero k hk1 hk
  have ht := trqLog_target_ge h2 k hk1 hk
  have hft : D.t k ≤ trqLogF (D.x k) := by
    have := (h2.isTargetSequence hk).sub_target_nonneg hk1 le_rfl; linarith
  have hx1 : 1 ≤ (D.x k) 0 := by change 1 ≤ trqLogF (D.x k); linarith
  have hβ1 : β ≤ 1 := h2.β_le_θ.trans h2.θ_lt_one.le
  have hstuck := trqLog_call_stuck hq (hcalls k hk1 hk) (by rw [h0, hε1])
    (by rw [h0]; linarith) (by rw [h0]; exact hhi) h2.β_pos hβ1 hϑ hϑ1
    (by rw [h0]; exact h2.x_mem k hk1 hk) (by rw [h0]; exact hft) (by rw [h0]; exact hx1) hL hle
  have hx : D.x (k + 1) = D.x k := by rw [← h2.inner_end k hk1 hk, hstuck, h0]
  obtain ⟨hδ0, hδ1⟩ := h2.radius_mem k hk1 hk 1 (Finset.mem_Icc.2 ⟨le_rfl, hq⟩)
  rcases h2.output k hk1 hk with h | h | h
  · rw [hx] at h; linarith
  · rw [hx] at h; linarith
  · rw [hx] at h
    exact trqLog_not_meritCrit hq hε1 (h2.x_mem k hk1 hk) hft (hθε.trans_le hlo) hδ0
      (hδ1.trans hx1) hδ1 h

/-- **The evaluation count of Phase 2 is at least `⌊1/(4ε₀)⌋ (L + 1)`** for every TPqp-GC run
with TRq-SC calls on this example, when `ε₀ ≤ 1/2` and `4 ε₀/(ς β) ≤ γ₁^L min(Δ₀, ϑ)`. -/
theorem trqLog_funEvals_ge (hq : 1 ≤ q)
    (h2 : IsTPqpGCPhase2 trqLogF trqLogC trqLogX q θ β ε trqLogX₀ D)
    (hcalls : IsTRqSCPhase2Calls trqLogF trqLogC trqLogX q P ϑ θ β ε D) (hε1 : ε 1 = 1 / 2)
    (hε₀2 : ε 0 ≤ 1 / 2) (hϑ : 0 ≤ ϑ) (hϑ1 : ϑ ≤ 1) {L : ℕ}
    (hL : 4 * ε 0 / (P.ς * β) ≤ P.γ₁ ^ L * min P.Δ₀ ϑ) {kε : ℕ}
    (hend : D.IsEnd trqLogF trqLogC trqLogX q θ ε kε) :
    (⌊1 / (4 * ε 0)⌋₊ : ℝ) * (L + 1) ≤ D.funEvals kε := by
  have hε₀ := h2.ε₀_pos
  obtain ⟨hkε1, hstop, hbef⟩ := hend
  set N := ⌊1 / (4 * ε 0)⌋₊ with hN
  have hNle : (N : ℝ) ≤ 1 / (4 * ε 0) := Nat.floor_le (by positivity)
  -- `kε` is large
  have hbig : 1 < (2 * kε + 1) * ε 0 := by
    by_contra hc
    push Not at hc
    exact trqLog_not_stop hq h2 hε1 hkε1 hbef hc hstop
  have hNk : N ≤ kε := by
    have : (N : ℝ) ≤ kε := by
      have h1 : 1 / (4 * ε 0) ≤ (kε : ℝ) := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      linarith
    exact_mod_cast this
  have hcount : ∀ k ∈ Finset.Icc 1 N, L + 1 ≤ D.e k := fun k hk => by
    obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.1 hk
    have hkb : D.Before trqLogF trqLogC trqLogX q θ ε k :=
      hbef.mono (hkN.trans hNk)
    have hkε : (2 * k - 1) * ε 0 ≤ 1 := by
      have : (k : ℝ) ≤ N := by exact_mod_cast hkN
      have : (k : ℝ) * ε 0 ≤ 1 / 4 := by
        calc (k : ℝ) * ε 0 ≤ (1 / (4 * ε 0)) * ε 0 := by gcongr; linarith
          _ = 1 / 4 := by field_simp
      nlinarith
    exact trqLog_call_long hq h2 hcalls hε1 hϑ hϑ1 hL hk1 hkb hkε
  have hsum : N * (L + 1) ≤ ∑ j ∈ Finset.Icc 1 kε, D.e j := by
    calc N * (L + 1) = ∑ _j ∈ Finset.Icc 1 N, (L + 1) := by simp
      _ ≤ ∑ j ∈ Finset.Icc 1 N, D.e j := Finset.sum_le_sum hcount
      _ ≤ ∑ j ∈ Finset.Icc 1 kε, D.e j :=
          Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc_right hNk)
  rw [Constrained.HighOrderTargetSeq.funEvals_eq_sum]
  have : ((N * (L + 1) : ℕ) : ℝ) ≤ ((1 + ∑ j ∈ Finset.Icc 1 kε, D.e j : ℕ) : ℝ) := by
    exact_mod_cast hsum.trans (Nat.le_add_left _ _)
  push_cast at this ⊢
  exact this

end Count


section Data


/-- The coordinates are smooth. -/
theorem trqLog_contDiff_coord (i : Fin 2) : ContDiff ℝ ∞ (fun v : ℝ² => v i) :=
  (EuclideanSpace.proj i : ℝ² →L[ℝ] ℝ).contDiff

/-- `X` is closed. -/
theorem isClosed_trqLogX : IsClosed trqLogX := by
  have hc : ∀ a : ℝ, Continuous fun _ : ℝ² => a := fun a => continuous_const
  have h := ((isClosed_le (hc 0) (trqLog_continuous_coord 0)).inter
    (isClosed_le (trqLog_continuous_coord 0) (hc 2))).inter
    ((isClosed_le (hc (-1)) (trqLog_continuous_coord 1)).inter
    (isClosed_le (trqLog_continuous_coord 1) (hc 1)))
  convert h using 1
  ext v
  simp only [trqLogX, Set.mem_ofPred_eq, Set.mem_inter_iff]
  tauto

/-- `x₀ ∈ X`. -/
theorem trqLogX₀_mem : trqLogX₀ ∈ trqLogX := by
  simp only [trqLogX_mem, trqLogX₀, PiLp.single_apply]
  norm_num

/-- `X` lies in the ball of radius `3`. -/
theorem trqLogX_subset_ball : trqLogX ⊆ ball (0 : ℝ²) 3 := by
  intro v hv
  obtain ⟨h0, h2, h3, h4⟩ := hv
  rw [mem_ball_zero_iff]
  have hs := trqLog_norm_sq v
  have : ‖v‖ ^ 2 < 3 ^ 2 := by nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) this

/-- **The example satisfies the hypotheses of Theorem 14.3.9 with a trust-region INNER** (of the
printed statement, and of `theorem_14_3_9_trq_one`), for every `q`: `X` is closed, c.D1qLB.X
and f.D1qLB.X hold on the ball of radius `3` (with some constants), and f.B.Fb holds for every
`β_F` with `f_low = 0`, `f_up = 2`. -/
theorem trqLog_assumptions (q : ℕ) : IsClosed trqLogX ∧ trqLogX₀ ∈ trqLogX ∧
    (∃ Lc Bc : ℕ → ℝ, AssumptionCD1pLBX trqLogC trqLogX (ball 0 3) q Lc Bc) ∧
    (∃ Lf Bf : ℕ → ℝ, AssumptionD1pLBX trqLogF trqLogX (ball 0 3) q Lf Bf) ∧
    ∀ βF, Chapter07.AssumptionBFb trqLogF trqLogC trqLogX βF 0 2 := by
  refine ⟨isClosed_trqLogX, trqLogX₀_mem, ?_, ?_, fun βF x hx => ⟨hx.1.1, hx.1.2.1⟩⟩
  · obtain ⟨L, B, h⟩ := exists_assumptionD1pLBX_ball (trqLog_contDiff_coord 1) trqLogX_subset_ball q
    refine ⟨L, B, ⟨isOpen_ball, convex_ball 0 3, trqLogX_subset_ball, fun i => ?_⟩⟩
    have : (fun x => trqLogC x i) = fun v : ℝ² => v 1 := by
      funext x
      rw [Subsingleton.elim i 0]
      simp [trqLogC]
    rw [this]
    exact h
  · exact exists_assumptionD1pLBX_ball (trqLog_contDiff_coord 0) trqLogX_subset_ball q

end Data


/-- The tolerances `ε₀` and `ε_j = 1/2` (`j ≥ 1`) of the example. -/
noncomputable def trqLogTol (ε₀ : ℝ) : ℕ → ℝ := fun j => if j = 0 then ε₀ else 1 / 2

/-- The printed order of the `(f, c)` evaluations for `q = 1`, `π_1 = 2`, `ε_1 = 1/2` is at most
`4/ε₀`. -/
theorem tpqpOrderF_trqLogTol_le {ε₀ : ℝ} (h0 : 0 < ε₀) :
    tpqpOrderF (fun j => (j : ℝ) + 1) 1 (trqLogTol ε₀) ≤ 4 / ε₀ := by
  unfold tpqpOrderF
  refine Optimization.finMax_le ?_ fun j hj => ?_
  · simp only [trqLogTol, ↓reduceIte]
    rw [inv_eq_one_div]
    exact div_le_div_of_nonneg_right (by norm_num) h0.le
  · rw [Finset.Icc_self, Finset.mem_singleton] at hj
    subst hj
    simp only [trqLogTol, ↓reduceIte, one_ne_zero]
    norm_num
    rw [Real.rpow_neg_one, div_eq_mul_inv, mul_comm]

/-- **Every bound of the form `κ_F ε₀^{-1}` on the `(f, c)` evaluations fails for runs
with TRq-SC calls, for every `q ≥ 1`** ([cartis2022evaluation], Theorem 14.3.9 with INNER of
trust-region type). On the example `n = 2`, `m = 1`, `X = [0, 2] × [-1, 1]`, `f(x) = x_1`,
`c(x) = x_2`, `x₀ = (2, 0)` (`trqLog_assumptions`), with the dual tolerances fixed at
`ε_j = 1/2` (`trqLogTol`), for all TRq parameters `P`, `0 < β ≤ θ < 1`, `β ≤ ϑ ≤ 1`,
`β₁ ∈ (0, 1)` and `β_F > 0`, there is no `κ_F` such that every run of `IsTPqpGCTRqSCRun`
entering Phase 2 terminates within `κ_F/ε₀` evaluations of `(f, c)` for all `ε₀ ∈ (0, 1]` with
`ε₀ ≤ β_F`: every call of the first `⌊1/(4ε₀)⌋` outer iterations restarts from `Δ₀` and needs
`≳ log(1/ε₀)` unsuccessful first-order iterations (`trqLog_call_long`, `trqLog_funEvals_ge`).

For `q = 1` this is the printed order (`theorem_14_3_9_trq_log_necessary`). For `q ≥ 2` it does
not contradict the printed order, nor the order with the exponents `q + 1`: at these tolerances
both are at least `ε₀^{-2}` (`inv_sq_le_tpqpOrderF_trqLogTol`), while the lower bound this
example gives is only of order `ε₀^{-1} log(1/ε₀)`. -/
theorem theorem_14_3_9_trq_log_necessary_inv {q : ℕ} (hq : 1 ≤ q) (P : Optimization.TRqParams)
    {ϑ θ β β₁ βF : ℝ} (hϑ1 : ϑ ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 < β) (hβθ : β ≤ θ)
    (hβϑ : β ≤ ϑ) (hβ₁0 : 0 < β₁) (hβ₁1 : β₁ < 1) (hβF : 0 < βF) :
    ¬ ∃ κF : ℝ, ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ ≤ 1 → ε₀ ≤ βF →
      ∀ (xP : ℕ → ℝ²) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq 2) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCTRqSCRun trqLogF trqLogC trqLogX q P ϑ θ β₁ β (trqLogTol ε₀) trqLogX₀ xP δP k₁ D
          nF₁ nD₁ →
        ‖trqLogC (xP k₁)‖ ≤ θ * ε₀ →
        ∃ kε, D.IsEnd trqLogF trqLogC trqLogX q θ (trqLogTol ε₀) kε ∧
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
  have hLcond : 4 * trqLogTol ε₀ 0 / (P.ς * β) ≤ P.γ₁ ^ L * min P.Δ₀ ϑ := by
    simp only [trqLogTol, ↓reduceIte]
    have := P.ς_pos
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hε : ∀ j ∈ Finset.range (q + 1), 0 < trqLogTol ε₀ j ∧ trqLogTol ε₀ j ≤ 1 := by
    intro j _
    by_cases hj : j = 0
    · simp only [trqLogTol, hj, ↓reduceIte]; exact ⟨hε₀, by linarith⟩
    · simp only [trqLogTol, hj, ↓reduceIte]; norm_num
  obtain ⟨-, -, ⟨Lc, Bc, hc⟩, ⟨Lf, Bf, hf⟩, -⟩ := trqLog_assumptions q
  have hc0 : ‖trqLogC trqLogX₀‖ = 0 := by simp [norm_trqLogC, trqLogX₀]
  obtain ⟨xP, δP, k₁, D, nF₁, nD₁, hR⟩ := exists_isTPqpGCTRqSCRun isClosed_trqLogX hq hc hf P
    hθ0 hθ1 hβ0 hβθ hβϑ hϑ1 hε hβ₁0 hβ₁1 trqLogX₀_mem (by rw [hc0]; linarith)
    (by rw [hc0]; linarith)
  obtain ⟨hk₁, hx₁⟩ := trqLog_phase1 hR.run hθ0
  have hc1 : ‖trqLogC (xP k₁)‖ ≤ θ * ε₀ := by
    rw [hx₁, hc0]; positivity
  obtain ⟨kε, hend, hbound⟩ := hκ ε₀ hε₀ (by linarith) hε₀F xP δP k₁ D nF₁ nD₁ hR hc1
  rw [hk₁] at hbound
  simp only [Finset.Icc_eq_empty (by norm_num : ¬ (1 : ℕ) ≤ 0),
    Finset.sum_empty, zero_add] at hbound
  have hc1' : ‖trqLogC (xP k₁)‖ ≤ θ * trqLogTol ε₀ 0 := by simpa [trqLogTol] using hc1
  have h2 := hR.run.phase2 hc1'
  rw [hx₁] at h2
  have hlow := trqLog_funEvals_ge hq h2 (hR.phase2 hc1') (by simp [trqLogTol])
    (by simp only [trqLogTol, ↓reduceIte]; linarith) hϑ0.le hϑ1 hLcond hend
  simp only [trqLogTol, ↓reduceIte] at hlow
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

/-- **Theorem 14.3.9 with a trust-region INNER fails in the printed order without the
logarithmic factor (`q = 1`).** On the example `n = 2`, `m = 1`, `X = [0, 2] × [-1, 1]`,
`f(x) = x_1`, `c(x) = x_2`, `x₀ = (2, 0)` (which satisfies X.CNe, c.D1qLB.X, f.D1qLB.X and f.B.Fb,
`trqLog_assumptions`), for all TRq parameters `P`, `0 < β ≤ θ < 1`, `β ≤ ϑ ≤ 1`, `β₁ ∈ (0, 1)` and
`β_F > 0`, there is no constant `κ_F` such that every TPqp-GC run with TRq-SC calls
(`IsTPqpGCTRqSCRun`; such runs exist, `exists_isTPqpGCTRqSCRun`) entering Phase 2 terminates
within `κ_F max[ε₀^{-1}, ε₀^{-1} ε_1^{-2}]` evaluations of `(f, c)` for all `ε ∈ (0, 1]²` with
`ε₀ ≤ β_F`. With `ε_1 = 1/2`: every call of the first `⌊1/(4ε₀)⌋` outer iterations restarts from
`Δ₀` and needs more than `L` unsuccessful iterations whenever `4ε₀/(ςβ) ≤ γ₁^L min(Δ₀, ϑ)`
(`trqLog_call_long`), so Phase 2 uses `≳ ε₀^{-1} log(1/ε₀)` evaluations (`trqLog_funEvals_ge`,
`theorem_14_3_9_trq_log_necessary_inv`). The bound of `theorem_14_3_9_trq_one`, with the factor
`1 + |log(ε₀ ε_1)|`, holds on this example. -/
theorem theorem_14_3_9_trq_log_necessary (P : Optimization.TRqParams) {ϑ θ β β₁ βF : ℝ}
    (hϑ1 : ϑ ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 < β) (hβθ : β ≤ θ) (hβϑ : β ≤ ϑ)
    (hβ₁0 : 0 < β₁) (hβ₁1 : β₁ < 1) (hβF : 0 < βF) :
    ¬ ∃ κF : ℝ, ∀ ε : ℕ → ℝ, (∀ j ∈ Finset.range 2, 0 < ε j ∧ ε j ≤ 1) → ε 0 ≤ βF →
      ∀ (xP : ℕ → ℝ²) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq 2) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCTRqSCRun trqLogF trqLogC trqLogX 1 P ϑ θ β₁ β ε trqLogX₀ xP δP k₁ D nF₁ nD₁ →
        ‖trqLogC (xP k₁)‖ ≤ θ * ε 0 →
        ∃ kε, D.IsEnd trqLogF trqLogC trqLogX 1 θ ε kε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) + D.funEvals kε ≤
            κF * tpqpOrderF (fun j => (j : ℝ) + 1) 1 ε := by
  rintro ⟨κF, hκ⟩
  refine theorem_14_3_9_trq_log_necessary_inv le_rfl P hϑ1 hθ0 hθ1 hβ0 hβθ hβϑ hβ₁0 hβ₁1 hβF
    ⟨|κF| * 4, fun ε₀ hε₀ hε₀1 hε₀F xP δP k₁ D nF₁ nD₁ hR hc1 => ?_⟩
  have hε : ∀ j ∈ Finset.range 2, 0 < trqLogTol ε₀ j ∧ trqLogTol ε₀ j ≤ 1 := by
    intro j _
    by_cases hj : j = 0
    · simp only [trqLogTol, hj, ↓reduceIte]; exact ⟨hε₀, hε₀1⟩
    · simp only [trqLogTol, hj, ↓reduceIte]; norm_num
  have e0 : trqLogTol ε₀ 0 = ε₀ := by simp [trqLogTol]
  obtain ⟨kε, hend, hbound⟩ := hκ (trqLogTol ε₀) hε (by rw [e0]; exact hε₀F) xP δP k₁ D nF₁ nD₁
    hR (by rw [e0]; exact hc1)
  refine ⟨kε, hend, hbound.trans ?_⟩
  have hO := tpqpOrderF_trqLogTol_le hε₀
  have hO0 : 0 ≤ tpqpOrderF (fun j => (j : ℝ) + 1) 1 (trqLogTol ε₀) := by
    have h1 := inv_le_tpqpOrderF (π := fun j : ℕ => (j : ℝ) + 1) (q := 1) (ε := trqLogTol ε₀)
    rw [e0] at h1
    exact (inv_nonneg.2 hε₀.le).trans h1
  calc κF * tpqpOrderF (fun j => (j : ℝ) + 1) 1 (trqLogTol ε₀)
      ≤ |κF| * (4 / ε₀) :=
        (mul_le_mul_of_nonneg_right (le_abs_self κF) hO0).trans
          (mul_le_mul_of_nonneg_left hO (abs_nonneg _))
    _ = |κF| * 4 / ε₀ := by ring

/-- **Why the example does not refute the printed order for `q ≥ 2`**: with `ε_j = 1/2`
(`j ≥ 1`) the printed order `max[ε₀^{-1}, max_j ε₀^{-j} ε_j^{-(j+1)}]` of Theorem 14.3.9 with the
TRq-SC exponents `π_j = j + 1` is at least `ε₀^{-2}` (its term `j = 2`), which exceeds the lower
bound of order `ε₀^{-1} log(1/ε₀)` that the example gives. -/
theorem inv_sq_le_tpqpOrderF_trqLogTol {q : ℕ} (hq : 2 ≤ q) {ε₀ : ℝ} (h0 : 0 < ε₀) :
    (ε₀ ^ 2)⁻¹ ≤ tpqpOrderF (fun j => (j : ℝ) + 1) q (trqLogTol ε₀) := by
  refine le_trans ?_ (term_le_tpqpOrderF (π := fun j => (j : ℝ) + 1) (ε := trqLogTol ε₀)
    (Finset.mem_Icc.2 ⟨by norm_num, hq⟩ : (2 : ℕ) ∈ Finset.Icc 1 q))
  simp only [trqLogTol, ↓reduceIte, OfNat.ofNat_ne_zero]
  norm_num
  have : 0 < (ε₀ ^ 2)⁻¹ := by positivity
  linarith

end TRqLog


section TRqPrinted

set_option hygiene false in
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

set_option hygiene false in
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

section OneDim

/-- `p(t) = t^{-1/4}`. -/
noncomputable def trqSlowP : ℝ → ℝ := fun t => t ^ (-(1 / 4 : ℝ))

/-- `p^{(k)}(t) = (-1/4)(-1/4 - 1)⋯(-1/4 - k + 1) t^{-1/4 - k}`. -/
theorem iteratedDeriv_trqSlowP (k : ℕ) (t : ℝ) :
    iteratedDeriv k trqSlowP t =
      (descPochhammer ℝ k).eval (-(1 / 4 : ℝ)) * t ^ (-(1 / 4 : ℝ) - k) := by
  rw [iteratedDeriv_eq_iterate]; exact Real.iter_deriv_rpow_const _ _ _

/-- `p'(t) = -t^{-5/4}/4`. -/
theorem iteratedDeriv_trqSlowP_one (t : ℝ) :
    iteratedDeriv 1 trqSlowP t = -(t ^ (-(5 / 4 : ℝ)) / 4) := by
  rw [iteratedDeriv_trqSlowP]
  norm_num
  ring

/-- `p''(t) = 5 t^{-9/4}/16`. -/
theorem iteratedDeriv_trqSlowP_two (t : ℝ) :
    iteratedDeriv 2 trqSlowP t = 5 * t ^ (-(9 / 4 : ℝ)) / 16 := by
  rw [iteratedDeriv_trqSlowP]
  norm_num [descPochhammer_succ_right]
  ring

/-- `p` is smooth on `(0, ∞)`. -/
theorem contDiffOn_trqSlowP : ContDiffOn ℝ ∞ trqSlowP (Ioi 0) := fun _ hx =>
  (Real.contDiffAt_rpow_const_of_ne (ne_of_gt hx)).contDiffWithinAt

end OneDim

section Problem

/-- The point `(a, b)` of `ℝ²`. -/
noncomputable def slowPt (a b : ℝ) : ℝ² := WithLp.toLp 2 ![a, b]

@[simp] theorem slowPt_apply_zero (a b : ℝ) : slowPt a b 0 = a := rfl

@[simp] theorem slowPt_apply_one (a b : ℝ) : slowPt a b 1 = b := rfl

/-- `(a, b) + (c, d) = (a + c, b + d)`. -/
theorem slowPt_add (a b c d : ℝ) : slowPt a b + slowPt c d = slowPt (a + c) (b + d) := by
  ext i; fin_cases i <;> simp [slowPt]

/-- `‖(a, b)‖² = a² + b²`. -/
theorem norm_slowPt_sq (a b : ℝ) : ‖slowPt a b‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [trqLog_norm_sq]; rfl

/-- `‖(a, b)‖ ≤ |a| + |b|`. -/
theorem norm_slowPt_le (a b : ℝ) : ‖slowPt a b‖ ≤ |a| + |b| := by
  have h := norm_slowPt_sq a b
  have h0 : 0 ≤ |a| + |b| := by positivity
  have h1 : ‖slowPt a b‖ ^ 2 ≤ (|a| + |b|) ^ 2 := by
    rw [h]; nlinarith [sq_abs a, sq_abs b, mul_nonneg (abs_nonneg a) (abs_nonneg b)]
  nlinarith [norm_nonneg (slowPt a b)]

/-- `g(t) = t^{-1/8}`, the second component of the constraint. -/
noncomputable def trqSlowG : ℝ → ℝ := fun t => t ^ (-(1 / 8 : ℝ))

/-- `g(t)² = p(t)` for `t ≥ 0`. -/
theorem trqSlowG_sq {t : ℝ} (ht : 0 ≤ t) : trqSlowG t ^ 2 = trqSlowP t := by
  rw [trqSlowG, trqSlowP, ← Real.rpow_natCast, ← Real.rpow_mul ht]
  norm_num

/-- The constraint `c(v) = (1, v_1^{-1/8}, v_2)` of the example (`v_1 = v 0`, `v_2 = v 1`). -/
noncomputable def trqSlowC : ℝ² → ℝ³ := fun v => WithLp.toLp 2 ![1, trqSlowG (v 0), v 1]

/-- `‖c(v)‖² = 1 + g(v_1)² + v_2²`. -/
theorem norm_trqSlowC_sq (v : ℝ²) : ‖trqSlowC v‖ ^ 2 = 1 + trqSlowG (v 0) ^ 2 + (v 1) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp [trqSlowC, sq_abs]

/-- `‖c(v)‖ ≥ 1`. -/
theorem one_le_norm_trqSlowC (v : ℝ²) : 1 ≤ ‖trqSlowC v‖ := by
  have h := norm_trqSlowC_sq v
  have : 1 ≤ ‖trqSlowC v‖ ^ 2 := by rw [h]; nlinarith [sq_nonneg (trqSlowG (v 0)), sq_nonneg (v 1)]
  nlinarith [norm_nonneg (trqSlowC v)]

/-- The infeasibility measure `ν = ½ ‖c‖²` near the half-plane `v_1 > 0`:
`ν(w) = ½ + p(w_1)/2 + w_2²/2`. -/
noncomputable def trqSlowNu : ℝ² → ℝ := fun w => 1 / 2 + trqSlowP (w 0) / 2 + trqSadSq (w 1)

/-- `ν = ½ ‖c‖²` on `v_1 ≥ 0`. -/
theorem phi2_trqSlowC_eq {v : ℝ²} (hv : 0 ≤ v 0) : phi2 trqSlowC v = trqSlowNu v := by
  rw [phi2_apply, norm_trqSlowC_sq, trqSlowG_sq hv, trqSlowNu, trqSadSq]
  ring

/-- `ν(a, b) = ½ + a^{-1/4}/2 + b²/2` for `a ≥ 0`. -/
theorem phi2_trqSlowC_slowPt {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    phi2 trqSlowC (slowPt a b) = 1 / 2 + a ^ (-(1 / 4 : ℝ)) / 2 + b ^ 2 / 2 := by
  rw [phi2_trqSlowC_eq (by simpa using ha)]
  simp [trqSlowNu, trqSlowP, trqSadSq]

/-- `ν` and `½ ‖c‖²` agree near every point of the open half-plane `v_1 > 0`. -/
theorem phi2_trqSlowC_eventuallyEq {v : ℝ²} (hv : 0 < v 0) : phi2 trqSlowC =ᶠ[𝓝 v] trqSlowNu := by
  have hU : IsOpen {w : ℝ² | 0 < w 0} :=
    isOpen_lt continuous_const ((EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).continuous)
  filter_upwards [hU.mem_nhds hv] with w hw
  exact phi2_trqSlowC_eq (le_of_lt hw)

/-- The Taylor series of `½ ‖c‖²` at a point of the open half-plane `v_1 > 0` is that of `ν`. -/
theorem ftaylorSeries_phi2_trqSlowC {v : ℝ²} (hv : 0 < v 0) :
    ftaylorSeries ℝ (phi2 trqSlowC) v = ftaylorSeries ℝ trqSlowNu v :=
  ((phi2_trqSlowC_eventuallyEq hv).ftaylorSeries ℝ).eq_of_nhds

/-- `ν` is smooth near every point of the open half-plane `v_1 > 0`. -/
theorem contDiffAt_trqSlowNu {v : ℝ²} (hv : 0 < v 0) (n : ℕ) : ContDiffAt ℝ n trqSlowNu v := by
  have h2 : ContDiffAt ℝ n (fun w : ℝ² => trqSlowP (w 0) / 2) v :=
    ((Real.contDiffAt_rpow_const_of_ne hv.ne').comp v
      (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).contDiff.contDiffAt).div_const 2
  have h3 : ContDiffAt ℝ n (fun w : ℝ² => trqSadSq (w 1)) v :=
    (trqSad_contDiff_coordSq 1).contDiffAt.of_le (by exact_mod_cast le_top)
  exact (contDiffAt_const.add h2).add h3

/-- `∇^k ν(v)[s]^k = p^{(k)}(v_1)/2 · s_1^k + (t²/2)^{(k)}(v_2) s_2^k` for `k ≥ 1`, `v_1 > 0`. -/
theorem iteratedFDeriv_trqSlowNu_apply {v : ℝ²} (hv : 0 < v 0) {k : ℕ} (hk : k ≠ 0) (s : ℝ²) :
    iteratedFDeriv ℝ k trqSlowNu v (fun _ => s) =
      iteratedDeriv k trqSlowP (v 0) / 2 * (s 0) ^ k + iteratedDeriv k trqSadSq (v 1) * (s 1) ^ k
        := by
  have e : trqSlowNu =
      ((fun _ => (1 / 2 : ℝ)) + fun w : ℝ² => trqSlowP (w 0) / 2) + fun w => trqSadSq (w 1) := by
    funext w; rfl
  have h1 : ContDiffAt ℝ k (fun _ : ℝ² => (1 / 2 : ℝ)) v := contDiffAt_const
  have h2 : ContDiffAt ℝ k (fun w : ℝ² => trqSlowP (w 0) / 2) v :=
    ((Real.contDiffAt_rpow_const_of_ne hv.ne').comp v
      (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).contDiff.contDiffAt).div_const 2
  have h3 : ContDiffAt ℝ k (fun w : ℝ² => trqSadSq (w 1)) v :=
    (trqSad_contDiff_coordSq 1).contDiffAt.of_le (by exact_mod_cast le_top)
  have h12 : ContDiffAt ℝ k ((fun _ : ℝ² => (1 / 2 : ℝ)) + fun w : ℝ² => trqSlowP (w 0) / 2) v :=
    h1.add h2
  rw [e, iteratedFDeriv_add_apply h12 h3, iteratedFDeriv_add_apply h1 h2,
    iteratedFDeriv_const_of_ne hk]
  simp only [Pi.zero_apply, add_apply, zero_add]
  have hP : ContDiffAt ℝ k (fun t => trqSlowP t / 2) (v 0) :=
    ((contDiffOn_trqSlowP.div_const 2).contDiffAt (isOpen_Ioi.mem_nhds hv)).of_le
      (by exact_mod_cast le_top)
  rw [ContDiffAt.iteratedFDeriv_comp_coord_apply_const 0 hP s,
    iteratedDeriv_div_const, ContDiffAt.iteratedFDeriv_comp_coord_apply_const 1
      (contDiff_trqSadSq.contDiffAt.of_le (by exact_mod_cast le_top)) s]

/-- `|ν'| = t^{-5/4}/8` (the slope along the first axis). -/
noncomputable def trqSlowA (t : ℝ) : ℝ := t ^ (-(5 / 4 : ℝ)) / 8

/-- `ν'' = 5 t^{-9/4}/32` (the curvature along the first axis). -/
noncomputable def trqSlowB (t : ℝ) : ℝ := 5 * t ^ (-(9 / 4 : ℝ)) / 32

/-- `ΔT_1(v, s) = A(v_1) s_1 - v_2 s_2` for `v_1 > 0`. -/
theorem trqSlow_ΔT1 {v : ℝ²} (hv : 0 < v 0) (s : ℝ²) :
    (ftaylorSeries ℝ (phi2 trqSlowC) v).taylorDecrement 1 s = trqSlowA (v 0) * s 0 - v 1 * s 1 := by
  rw [ftaylorSeries_phi2_trqSlowC hv, FormalMultilinearSeries.taylorDecrement_one_apply]
  change -(iteratedFDeriv ℝ 1 trqSlowNu v (fun _ => s)) = _
  rw [iteratedFDeriv_trqSlowNu_apply hv one_ne_zero, iteratedDeriv_trqSlowP_one,
    iteratedDeriv_trqSadSq_one, trqSlowA]
  ring

/-- `ΔT_2(v, s) = A(v_1) s_1 - v_2 s_2 - (B(v_1) s_1² + s_2²)/2` for `v_1 > 0`. -/
theorem trqSlow_ΔT2 {v : ℝ²} (hv : 0 < v 0) (s : ℝ²) :
    (ftaylorSeries ℝ (phi2 trqSlowC) v).taylorDecrement 2 s =
      trqSlowA (v 0) * s 0 - v 1 * s 1 - (trqSlowB (v 0) * (s 0) ^ 2 + (s 1) ^ 2) / 2 := by
  rw [ftaylorSeries_phi2_trqSlowC hv, FormalMultilinearSeries.taylorDecrement_two]
  change -(iteratedFDeriv ℝ 1 trqSlowNu v (fun _ => s)) -
    2⁻¹ * iteratedFDeriv ℝ 2 trqSlowNu v (fun _ => s) = _
  rw [iteratedFDeriv_trqSlowNu_apply hv one_ne_zero, iteratedFDeriv_trqSlowNu_apply hv two_ne_zero,
    iteratedDeriv_trqSlowP_one, iteratedDeriv_trqSlowP_two, iteratedDeriv_trqSadSq_one,
    iteratedDeriv_trqSadSq_two, trqSlowA, trqSlowB]
  ring

end Problem

section Scalar

/-- `A(t) > 0` for `t > 0`. -/
theorem trqSlowA_pos {t : ℝ} (ht : 0 < t) : 0 < trqSlowA t := by
  unfold trqSlowA; positivity

/-- `B(t) ≥ 0` for `t > 0`. -/
theorem trqSlowB_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ trqSlowB t := by
  unfold trqSlowB; positivity

/-- `A` is nonincreasing on `(0, ∞)`. -/
theorem trqSlowA_anti {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) : trqSlowA t ≤ trqSlowA s := by
  unfold trqSlowA
  have := Real.rpow_le_rpow_of_nonpos hs hst (by norm_num : (-(5 / 4 : ℝ)) ≤ 0)
  linarith

/-- `B(t) = (5/4) A(t)/t`. -/
theorem trqSlowB_eq {t : ℝ} (ht : 0 < t) : trqSlowB t = 5 / 4 * trqSlowA t / t := by
  unfold trqSlowB trqSlowA
  have : t ^ (-(9 / 4 : ℝ)) = t ^ (-(5 / 4 : ℝ)) * t ^ (-1 : ℝ) := by
    rw [← Real.rpow_add ht]; norm_num
  rw [this, Real.rpow_neg_one]
  field_simp
  ring

/-- `B(t) δ ≤ A(t)` for `t ≥ 2` and `0 ≤ δ ≤ 1`. -/
theorem trqSlowB_mul_le {t δ : ℝ} (ht : 2 ≤ t) (hδ1 : δ ≤ 1) :
    trqSlowB t * δ ≤ trqSlowA t := by
  have ht0 : 0 < t := by linarith
  rw [trqSlowB_eq ht0, div_mul_eq_mul_div, div_le_iff₀ ht0]
  have := trqSlowA_pos ht0
  nlinarith

/-- `A(t) ≤ 2 A(t + h)` for `t ≥ 2` and `0 ≤ h ≤ 1/2`. -/
theorem trqSlowA_le_two_mul {t h : ℝ} (ht : 2 ≤ t) (hh0 : 0 ≤ h) (hh : h ≤ 1 / 2) :
    trqSlowA t ≤ 2 * trqSlowA (t + h) := by
  have ht0 : 0 < t := by linarith
  have h1 : trqSlowA (5 / 4 * t) ≤ trqSlowA (t + h) := trqSlowA_anti (by linarith) (by linarith)
  have h2 : trqSlowA (5 / 4 * t) = (5 / 4 : ℝ) ^ (-(5 / 4 : ℝ)) * trqSlowA t := by
    unfold trqSlowA
    rw [Real.mul_rpow (by norm_num) ht0.le]
    ring
  have h3 : (16 / 25 : ℝ) ≤ (5 / 4 : ℝ) ^ (-(5 / 4 : ℝ)) := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 5 / 4)
      (by norm_num : (-2 : ℝ) ≤ -(5 / 4 : ℝ))
    have e : (5 / 4 : ℝ) ^ (-2 : ℝ) = 16 / 25 := by
      rw [Real.rpow_neg (by norm_num), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
      norm_num
    linarith
  have := trqSlowA_pos ht0
  nlinarith

/-- `(t^{-1/4})' = -2 A(t)`. -/
theorem hasDerivAt_rpow_quarter {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => x ^ (-(1 / 4 : ℝ))) (-(2 * trqSlowA t)) t := by
  have := Real.hasDerivAt_rpow_const (p := -(1 / 4 : ℝ)) (Or.inl ht.ne')
  convert this using 1
  unfold trqSlowA
  norm_num
  ring

/-- **The decrease along the first axis**: for `t ≥ 2` and `0 ≤ h ≤ 1/2`,
`t^{-1/4}/2 - (t + h)^{-1/4}/2 ≥ A(t) h / 2`. -/
theorem trqSlow_decrease_ge {t h : ℝ} (ht : 2 ≤ t) (hh0 : 0 ≤ h) (hh : h ≤ 1 / 2) :
    trqSlowA t * h / 2 ≤ t ^ (-(1 / 4 : ℝ)) / 2 - (t + h) ^ (-(1 / 4 : ℝ)) / 2 := by
  have ht0 : 0 < t := by linarith
  rcases hh0.eq_or_lt with rfl | hpos
  · simp
  obtain ⟨ξ, hξ, hξd⟩ := exists_hasDerivAt_eq_slope (fun x : ℝ => x ^ (-(1 / 4 : ℝ)))
    (fun x => -(2 * trqSlowA x)) (by linarith : t < t + h)
    (fun x hx =>
      (Real.continuousAt_rpow_const x _ (Or.inl (by linarith [hx.1]))).continuousWithinAt)
    (fun x hx => hasDerivAt_rpow_quarter (by linarith [hx.1]))
  have hξ0 : 0 < ξ := by linarith [hξ.1]
  have hA : trqSlowA (t + h) ≤ trqSlowA ξ := trqSlowA_anti hξ0 hξ.2.le
  have hA2 := trqSlowA_le_two_mul ht hh0 hh
  simp only [add_sub_cancel_left] at hξd
  rw [eq_div_iff hpos.ne'] at hξd
  nlinarith

end Scalar

section Iterations

/-- The trust-region parameters of the example: `Δ₀ = Δ_max = 1`, `η₁ = 1/4`, `η₂ = 3/4`,
`γ₁ = 1/4`, `γ₂ = 1/2`, `γ₃ = 2`, `ς = 1/4`. -/
noncomputable def trqSlowParams : Optimization.TRqParams where
  Δ₀ := 1
  η₁ := 1 / 4
  η₂ := 3 / 4
  γ₁ := 1 / 4
  γ₂ := 1 / 2
  γ₃ := 2
  Δ₀_pos := one_pos
  η₁_pos := by norm_num
  η₁_le_η₂ := by norm_num
  η₂_lt_one := by norm_num
  γ₁_pos := by norm_num
  γ₁_le_γ₂ := by norm_num
  γ₂_lt_one := by norm_num
  one_le_γ₃ := by norm_num
  Δmax := 1
  ς := 1 / 4
  Δ₀_le_Δmax := le_rfl
  ς_pos := by norm_num
  ς_le_one := by norm_num

/-- The feasible set of the example: the closed half-plane `X = {v | v_1 ≥ 1}`. -/
def trqSlowX : Set ℝ² := {v | 1 ≤ v 0}

/-- The open half-plane `X₀ = {v | v_1 > 1/2} ⊇ X` of the assumptions. -/
def trqSlowX₀ : Set ℝ² := {v | 1 / 2 < v 0}

/-- `(a, b) + (c, d) ∈ X` when `a + c ≥ 1`. -/
theorem slowPt_add_mem {a b c d : ℝ} (h : 1 ≤ a + c) : slowPt a b + slowPt c d ∈ trqSlowX := by
  rw [slowPt_add]; exact h

/-- The successful iterations keep the radius. -/
theorem trqSlow_accept_succ {E : Type*} [NormedAddCommGroup E] {ρ Δ : ℝ} {x s x' : E}
    (hΔ : 0 ≤ Δ) (hρ : trqSlowParams.η₁ ≤ ρ) (hx : x' = x + s) :
    Optimization.TRAcceptance trqSlowParams.toTRParams ρ x s x' Δ Δ := by
  refine ⟨by rw [ite_eq_left hρ]; exact hx, ⟨fun _ => ⟨le_rfl, ?_⟩, fun _ _ => ⟨?_, le_rfl⟩,
    fun h => absurd h (not_lt.2 hρ)⟩⟩
  · change Δ ≤ 2 * Δ; linarith
  · change 1 / 2 * Δ ≤ Δ; linarith

/-- The unsuccessful iterations halve the radius. -/
theorem trqSlow_accept_unsucc {E : Type*} [NormedAddCommGroup E] {ρ Δ : ℝ} {x s : E}
    (hΔ : 0 ≤ Δ) (hρ : ρ < trqSlowParams.η₁) :
    Optimization.TRAcceptance trqSlowParams.toTRParams ρ x s x Δ (Δ / 2) := by
  have hρ' : ρ < 1 / 4 := hρ
  refine ⟨(ite_eq_right (not_le.2 hρ)).symm, ⟨fun h => absurd h (not_le.2 (hρ'.trans (by
    norm_num : (1 : ℝ) / 4 < 3 / 4))), fun h => absurd h (not_le.2 hρ), fun _ => ⟨?_, ?_⟩⟩⟩
  · change 1 / 4 * Δ ≤ Δ / 2; linarith
  · change Δ / 2 ≤ 1 / 2 * Δ; linarith

/-- A ratio is at least `η₁ = 1/4` when the decrease of the objective is at least a quarter of the
predicted one. -/
theorem trqSlow_ratio_ge_quarter {E : Type*} [NormedAddCommGroup E] {F : E → ℝ} {x s : E}
    {pred : ℝ} (hp : 0 < pred)
    (h : pred / 4 ≤ F x - F (x + s)) :
    trqSlowParams.η₁ ≤ Optimization.reductionRatio F x s pred := by
  change (1 / 4 : ℝ) ≤ _
  rw [Optimization.reductionRatio_def, le_div_iff₀ hp]; linarith

/-- A ratio is below `η₁ = 1/4` when the decrease of the objective is below a quarter of the
predicted one. -/
theorem trqSlow_ratio_lt_quarter {E : Type*} [NormedAddCommGroup E] {F : E → ℝ} {x s : E}
    {pred : ℝ} (hp : 0 < pred)
    (h : F x - F (x + s) < pred / 4) :
    Optimization.reductionRatio F x s pred < trqSlowParams.η₁ := by
  change _ < (1 / 4 : ℝ)
  rw [Optimization.reductionRatio_def, div_lt_iff₀ hp]; linarith

/-- `ΔT_1(v, d) ≤ (A(a) + |b|) δ` at `v = (a, b)`, `a > 0`, for `‖d‖ ≤ δ`. -/
theorem trqSlow_ΔT1_le {a b δ : ℝ} (ha : 0 < a) {d : ℝ²} (hd : ‖d‖ ≤ δ) :
    (ftaylorSeries ℝ (phi2 trqSlowC) (slowPt a b)).taylorDecrement 1 d ≤
      (trqSlowA a + |b|) * δ := by
  rw [trqSlow_ΔT1 (by simpa using ha)]
  simp only [slowPt_apply_zero, slowPt_apply_one]
  have h0 := (EuclideanSpace.abs_apply_le_norm d 0).trans hd
  have h1 := (EuclideanSpace.abs_apply_le_norm d 1).trans hd
  have hA := (trqSlowA_pos ha).le
  have e0 : trqSlowA a * d 0 ≤ trqSlowA a * δ :=
    (mul_le_mul_of_nonneg_left (le_abs_self _) hA).trans (mul_le_mul_of_nonneg_left h0 hA)
  have e1 : -(b * d 1) ≤ |b| * δ := by
    have := neg_abs_le (b * d 1)
    rw [abs_mul] at this
    nlinarith [abs_nonneg b]
  nlinarith

/-- `ΔT_2(v, d) ≤ ΔT_1(v, d)` at `v = (a, b)`, `a > 0` (the Hessian is positive semidefinite). -/
theorem trqSlow_ΔT2_le_ΔT1 {a b : ℝ} (ha : 0 < a) (d : ℝ²) :
    (ftaylorSeries ℝ (phi2 trqSlowC) (slowPt a b)).taylorDecrement 2 d ≤
      (ftaylorSeries ℝ (phi2 trqSlowC) (slowPt a b)).taylorDecrement 1 d := by
  rw [trqSlow_ΔT1 (by simpa using ha), trqSlow_ΔT2 (by simpa using ha)]
  have := trqSlowB_nonneg (t := (slowPt a b) 0) (by simpa using ha)
  nlinarith [sq_nonneg (d 0), sq_nonneg (d 1)]

/-- `ΔT_2(v, d) ≤ A(a) δ + b²/2` at `v = (a, b)`, `a > 0`, for `‖d‖ ≤ δ`. -/
theorem trqSlow_ΔT2_le {a b δ : ℝ} (ha : 0 < a) {d : ℝ²} (hd : ‖d‖ ≤ δ) :
    (ftaylorSeries ℝ (phi2 trqSlowC) (slowPt a b)).taylorDecrement 2 d ≤
      trqSlowA a * δ + b ^ 2 / 2 := by
  rw [trqSlow_ΔT2 (by simpa using ha)]
  simp only [slowPt_apply_zero, slowPt_apply_one]
  have h0 := (EuclideanSpace.abs_apply_le_norm d 0).trans hd
  have hA := (trqSlowA_pos ha).le
  have hB := trqSlowB_nonneg ha
  have e0 : trqSlowA a * d 0 ≤ trqSlowA a * δ :=
    (mul_le_mul_of_nonneg_left (le_abs_self _) hA).trans (mul_le_mul_of_nonneg_left h0 hA)
  nlinarith [sq_nonneg (d 1 + b), mul_nonneg hB (sq_nonneg (d 0))]

/-- The measure bound behind the Step-1 displacements. -/
theorem trqSlow_isApproxMeasureStep {a b δ B : ℝ} (ha : 1 ≤ a) (hδ : 0 ≤ δ) {j : ℕ} {d : ℝ²}
    (hdδ : ‖d‖ ≤ δ) (hdX : 1 ≤ a + d 0)
    (hB : ∀ e : ℝ², ‖e‖ ≤ δ →
      (ftaylorSeries ℝ (phi2 trqSlowC) (slowPt a b)).taylorDecrement j e ≤ B)
    (hd : B / 4 ≤ (ftaylorSeries ℝ (phi2 trqSlowC) (slowPt a b)).taylorDecrement j d) :
    Optimization.IsApproxMeasureStep
      ((ftaylorSeries ℝ (phi2 trqSlowC) (slowPt a b)).taylorDecrement j) δ
      {e | slowPt a b + e ∈ trqSlowX} trqSlowParams.ς d := by
  have hd' : d = slowPt (d 0) (d 1) := by ext i; fin_cases i <;> rfl
  refine ⟨⟨mem_closedBall_zero_iff.2 hdδ, ?_⟩, ?_⟩
  · change slowPt a b + d ∈ trqSlowX
    rw [hd']; exact slowPt_add_mem hdX
  · have hm : Optimization.decrementMeasure
        ((ftaylorSeries ℝ (phi2 trqSlowC) (slowPt a b)).taylorDecrement j) δ
        {e | slowPt a b + e ∈ trqSlowX} ≤ B :=
      Optimization.decrementMeasure_le ⟨0, mem_closedBall_self hδ, by
        change slowPt a b + 0 ∈ trqSlowX
        rw [add_zero]; exact ha⟩ fun e he => hB e (mem_closedBall_zero_iff.1 he.1)
    change 1 / 4 * _ ≤ _
    linarith

end Iterations

section Steps

/-- `ΔT_1((a, b), (σ, τ)) = A(a) σ - b τ` for `a > 0`. -/
theorem trqSlow_ΔT1_pt {a : ℝ} (ha : 0 < a) (b σ τ : ℝ) :
    (ftaylorSeries ℝ (phi2 trqSlowC) (slowPt a b)).taylorDecrement 1 (slowPt σ τ) =
      trqSlowA a * σ - b * τ := by
  rw [trqSlow_ΔT1 (by simpa using ha)]; simp

/-- `ΔT_2((a, b), (σ, τ)) = A(a) σ - b τ - (B(a) σ² + τ²)/2` for `a > 0`. -/
theorem trqSlow_ΔT2_pt {a : ℝ} (ha : 0 < a) (b σ τ : ℝ) :
    (ftaylorSeries ℝ (phi2 trqSlowC) (slowPt a b)).taylorDecrement 2 (slowPt σ τ) =
      trqSlowA a * σ - b * τ - (trqSlowB a * σ ^ 2 + τ ^ 2) / 2 := by
  rw [trqSlow_ΔT2 (by simpa using ha)]; simp

/-- Unused orders: some approximate optimality displacement exists at every point of `X`. -/
theorem trqSlow_exists_witness : ∃ W : ℝ² → ℝ → ℕ → ℝ², ∀ (y : ℝ²) (δ : ℝ) (j : ℕ),
    y ∈ trqSlowX → 0 ≤ δ → Optimization.IsApproxMeasureStep
      ((ftaylorSeries ℝ (phi2 trqSlowC) y).taylorDecrement j) δ {e | y + e ∈ trqSlowX}
        trqSlowParams.ς (W y δ j) := by
  have hX : IsClosed trqSlowX :=
    isClosed_le continuous_const ((EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).continuous)
  have hW : ∀ (y : ℝ²) (δ : ℝ) (j : ℕ), ∃ w : ℝ², y ∈ trqSlowX → 0 ≤ δ →
      Optimization.IsApproxMeasureStep ((ftaylorSeries ℝ (phi2 trqSlowC) y).taylorDecrement j) δ
        {e | y + e ∈ trqSlowX} trqSlowParams.ς w := by
    intro y δ j
    by_cases h : y ∈ trqSlowX ∧ 0 ≤ δ
    · obtain ⟨w, hw⟩ := Optimization.exists_isApproxMeasureStep_taylorDecrement
        (ftaylorSeries ℝ (phi2 trqSlowC) y) j (hX.preimage (continuous_const.add continuous_id))
        (by change y + 0 ∈ trqSlowX; rw [add_zero]; exact h.1) h.2 trqSlowParams.ς_le_one
      exact ⟨w, fun _ _ => hw⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose W hW using hW
  exact ⟨W, hW⟩

/-- On the axis, `(δ/4, 0)` is an approximate first-order displacement. -/
theorem trqSlow_wit_axis_one {a δ : ℝ} (ha : 2 ≤ a) (hδ : 0 ≤ δ) :
    Optimization.IsApproxMeasureStep
      ((ftaylorSeries ℝ (phi2 trqSlowC) (slowPt a 0)).taylorDecrement 1) δ
      {e | slowPt a 0 + e ∈ trqSlowX} trqSlowParams.ς (slowPt (δ / 4) 0) := by
  have ha0 : 0 < a := by linarith
  refine trqSlow_isApproxMeasureStep (B := trqSlowA a * δ) (by linarith) hδ
    ((norm_slowPt_le _ _).trans (by rw [abs_of_nonneg (by linarith), abs_zero]; linarith))
    (by simp; linarith) (fun e he => (trqSlow_ΔT1_le ha0 he).trans_eq (by simp)) ?_
  rw [trqSlow_ΔT1_pt ha0]; ring_nf; rfl

/-- On the axis, `(δ, 0)` is an approximate second-order displacement for `δ ≤ 1`. -/
theorem trqSlow_wit_axis_two {a δ : ℝ} (ha : 2 ≤ a) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    Optimization.IsApproxMeasureStep
      ((ftaylorSeries ℝ (phi2 trqSlowC) (slowPt a 0)).taylorDecrement 2) δ
      {e | slowPt a 0 + e ∈ trqSlowX} trqSlowParams.ς (slowPt δ 0) := by
  have ha0 : 0 < a := by linarith
  refine trqSlow_isApproxMeasureStep (B := trqSlowA a * δ) (by linarith) hδ
    ((norm_slowPt_le _ _).trans (by rw [abs_of_nonneg hδ, abs_zero, add_zero]))
    (by simp; linarith) (fun e he => ((trqSlow_ΔT2_le_ΔT1 ha0 e).trans
      (trqSlow_ΔT1_le ha0 he)).trans_eq (by simp)) ?_
  rw [trqSlow_ΔT2_pt ha0]
  have := trqSlowB_mul_le ha hδ1
  have := (trqSlowA_pos ha0).le
  nlinarith

/-- At `(a, y)` with `A(a) ≤ y`, `(0, -δ)` is an approximate first-order displacement. -/
theorem trqSlow_wit_shrink_one {a y δ : ℝ} (ha : 2 ≤ a) (hy : 0 ≤ y) (hAy : trqSlowA a ≤ y)
    (hδ : 0 ≤ δ) :
    Optimization.IsApproxMeasureStep
      ((ftaylorSeries ℝ (phi2 trqSlowC) (slowPt a y)).taylorDecrement 1) δ
      {e | slowPt a y + e ∈ trqSlowX} trqSlowParams.ς (slowPt 0 (-δ)) := by
  have ha0 : 0 < a := by linarith
  refine trqSlow_isApproxMeasureStep (B := (trqSlowA a + |y|) * δ) (by linarith) hδ
    ((norm_slowPt_le _ _).trans (by rw [abs_zero, abs_neg, abs_of_nonneg hδ, zero_add]))
    (by simp; linarith) (fun e he => trqSlow_ΔT1_le ha0 he) ?_
  rw [trqSlow_ΔT1_pt ha0, abs_of_nonneg hy]
  nlinarith

/-- At `(a, y)` with `0 ≤ y ≤ δ ≤ 1`, `(δ/2, -min(y, δ/2))` is an approximate second-order
displacement. -/
theorem trqSlow_wit_shrink_two {a y δ : ℝ} (ha : 2 ≤ a) (hy : 0 ≤ y) (hyδ : y ≤ δ) (hδ1 : δ ≤ 1) :
    Optimization.IsApproxMeasureStep
      ((ftaylorSeries ℝ (phi2 trqSlowC) (slowPt a y)).taylorDecrement 2) δ
      {e | slowPt a y + e ∈ trqSlowX} trqSlowParams.ς (slowPt (δ / 2) (-min y (δ / 2))) := by
  have ha0 : 0 < a := by linarith
  have hδ : 0 ≤ δ := hy.trans hyδ
  have hb0 : 0 ≤ min y (δ / 2) := le_min hy (by linarith)
  have hb1 : min y (δ / 2) ≤ y := min_le_left _ _
  have hb2 : min y (δ / 2) ≤ δ / 2 := min_le_right _ _
  have hb3 : y / 2 ≤ min y (δ / 2) := le_min (by linarith) (by linarith)
  have hn : ‖slowPt (δ / 2) (-min y (δ / 2))‖ ≤ δ := by
    refine (norm_slowPt_le _ _).trans ?_
    rw [abs_neg, abs_of_nonneg hb0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ δ / 2)]
    linarith
  refine trqSlow_isApproxMeasureStep (B := trqSlowA a * δ + y ^ 2 / 2) (by linarith) hδ hn
    (by simp; linarith) (fun e he => trqSlow_ΔT2_le ha0 he) ?_
  rw [trqSlow_ΔT2_pt ha0]
  have hB := trqSlowB_mul_le ha hδ1
  have hA := (trqSlowA_pos ha0).le
  have hB0 := trqSlowB_nonneg ha0
  set b := min y (δ / 2)
  have h1 : trqSlowB a * (δ / 2) ^ 2 ≤ trqSlowA a * δ / 4 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 hb1) (sub_nonneg.2 hb3)]

/-- **A first-order step on the axis**: at `(a, 0)` with `ε_1 < A(a)` the first order fails
(Step-1 displacement `(δ/4, 0)`), and every feasible `(h, τ)` in the trust region with
`h ≥ δ/4` is a valid step. -/
theorem trqSlow_step_axis_one {q : ℕ} (hq : 1 ≤ q) {ε : ℕ → ℝ} {a δ Δ h τ : ℝ} (ha : 2 ≤ a)
    (hδ : 0 < δ) (hε : ε 1 < trqSlowA a) (hh : δ / 4 ≤ h) (hs : ‖slowPt h τ‖ ≤ Δ)
    {d : ℕ → ℝ²} (hd1 : d 1 = slowPt (δ / 4) 0) :
    Optimization.IsTRqStep (ftaylorSeries ℝ (phi2 trqSlowC) (slowPt a 0))
      {e | slowPt a 0 + e ∈ trqSlowX} trqSlowParams.ς q ε δ Δ d 1 (slowPt h τ) := by
  have ha0 : 0 < a := by linarith
  have hA := trqSlowA_pos ha0
  refine ⟨Finset.mem_Icc.2 ⟨le_rfl, hq⟩, ?_, fun i hi hi1 => absurd hi1
    (by have := (Finset.mem_Icc.1 hi).1; omega), ⟨mem_closedBall_zero_iff.2 hs,
      slowPt_add_mem (by linarith)⟩, ?_⟩
  · rw [hd1, trqSlow_ΔT1_pt ha0]
    change (1 / 4 : ℝ) * ε 1 * δ ^ 1 / ((1 : ℕ)! : ℝ) < _
    norm_num
    nlinarith
  · rw [hd1, trqSlow_ΔT1_pt ha0, trqSlow_ΔT1_pt ha0]
    nlinarith

/-- **A second-order step on the axis**: at `(a, 0)` with `A(a) ≤ ε_1` and `ε_2 δ < 4 A(a)` the
first order passes, the second order fails, and the step is `(δ, 0)`. -/
theorem trqSlow_step_axis_two {q : ℕ} (hq : 2 ≤ q) {ε : ℕ → ℝ} {a δ Δ : ℝ} (ha : 2 ≤ a)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδΔ : δ ≤ Δ) (hε1 : trqSlowA a ≤ ε 1)
    (hε2 : ε 2 * δ < 4 * trqSlowA a) {d : ℕ → ℝ²} (hd1 : d 1 = slowPt (δ / 4) 0)
    (hd2 : d 2 = slowPt δ 0) :
    Optimization.IsTRqStep (ftaylorSeries ℝ (phi2 trqSlowC) (slowPt a 0))
      {e | slowPt a 0 + e ∈ trqSlowX} trqSlowParams.ς q ε δ Δ d 2 (slowPt δ 0) := by
  have ha0 : 0 < a := by linarith
  have hA := trqSlowA_pos ha0
  have hB := trqSlowB_mul_le ha hδ1
  refine ⟨Finset.mem_Icc.2 ⟨by norm_num, hq⟩, ?_, fun i hi hi2 => ?_, ⟨mem_closedBall_zero_iff.2
    ((norm_slowPt_le _ _).trans (by rw [abs_of_pos hδ, abs_zero, add_zero]; exact hδΔ)),
      slowPt_add_mem (by linarith)⟩, by rw [hd2]⟩
  · rw [hd2, trqSlow_ΔT2_pt ha0]
    change (1 / 4 : ℝ) * ε 2 * δ ^ 2 / ((2 : ℕ)! : ℝ) < _
    norm_num [Nat.factorial]
    nlinarith
  · have hi1 : i = 1 := by have := (Finset.mem_Icc.1 hi).1; omega
    subst hi1
    rw [hd1, trqSlow_ΔT1_pt ha0]
    change _ ≤ (1 / 4 : ℝ) * ε 1 * δ ^ 1 / ((1 : ℕ)! : ℝ)
    norm_num
    nlinarith

/-- **A first-order step off the axis**: at `(a, y)` with `ε_1 < 4y` the first order fails
(Step-1 displacement `(0, -δ)`), and the step is `(0, -δ)`. -/
theorem trqSlow_step_shrink {q : ℕ} (hq : 1 ≤ q) {ε : ℕ → ℝ} {a y δ Δ : ℝ} (ha : 2 ≤ a)
    (hδ : 0 < δ) (hδΔ : δ ≤ Δ) (hε : ε 1 < 4 * y) {d : ℕ → ℝ²} (hd1 : d 1 = slowPt 0 (-δ)) :
    Optimization.IsTRqStep (ftaylorSeries ℝ (phi2 trqSlowC) (slowPt a y))
      {e | slowPt a y + e ∈ trqSlowX} trqSlowParams.ς q ε δ Δ d 1 (slowPt 0 (-δ)) := by
  have ha0 : 0 < a := by linarith
  refine ⟨Finset.mem_Icc.2 ⟨le_rfl, hq⟩, ?_, fun i hi hi1 => absurd hi1
    (by have := (Finset.mem_Icc.1 hi).1; omega), ⟨mem_closedBall_zero_iff.2
      ((norm_slowPt_le _ _).trans (by rw [abs_zero, abs_neg, abs_of_pos hδ, zero_add]; exact hδΔ)),
      slowPt_add_mem (by linarith)⟩, by rw [hd1]⟩
  rw [hd1, trqSlow_ΔT1_pt ha0]
  change (1 / 4 : ℝ) * ε 1 * δ ^ 1 / ((1 : ℕ)! : ℝ) < _
  norm_num
  nlinarith

/-- A step `(h, τ)` from the axis point `(a, 0)` with `0 < h ≤ 1/2`, `τ² ≤ A(a) h/4` and
predicted decrease `pred ∈ (0, A(a) h]` is successful. -/
theorem trqSlow_ratio_axis {a h τ pred : ℝ} (ha : 2 ≤ a) (hh0 : 0 ≤ h) (hh : h ≤ 1 / 2)
    (hp0 : 0 < pred) (hp : pred ≤ trqSlowA a * h) (hτ : τ ^ 2 ≤ trqSlowA a * h / 4) :
    trqSlowParams.η₁ ≤ Optimization.reductionRatio (phi2 trqSlowC) (slowPt a 0) (slowPt h τ) pred
      := by
  refine trqSlow_ratio_ge_quarter hp0 ?_
  rw [slowPt_add, phi2_trqSlowC_slowPt (by linarith), phi2_trqSlowC_slowPt (by linarith)]
  have := trqSlow_decrease_ge ha hh0 hh
  simp only [zero_add]
  nlinarith

/-- The step `(0, -δ)` from `(a, y)` with `2y ≤ δ` is unsuccessful. -/
theorem trqSlow_ratio_shrink_unsucc {a y δ : ℝ} (ha : 0 ≤ a) (hy : 0 < y) (hyδ : 2 * y ≤ δ) :
    Optimization.reductionRatio (phi2 trqSlowC) (slowPt a y) (slowPt 0 (-δ)) (y * δ) <
      trqSlowParams.η₁ := by
  refine trqSlow_ratio_lt_quarter (by nlinarith) ?_
  rw [slowPt_add, phi2_trqSlowC_slowPt ha, phi2_trqSlowC_slowPt (by linarith)]
  simp only [add_zero]
  nlinarith

/-- The step `(0, -y)` from `(a, y)` is successful. -/
theorem trqSlow_ratio_shrink_succ {a y : ℝ} (ha : 0 ≤ a) (hy : 0 < y) :
    trqSlowParams.η₁ ≤
      Optimization.reductionRatio (phi2 trqSlowC) (slowPt a y) (slowPt 0 (-y)) (y * y) := by
  refine trqSlow_ratio_ge_quarter (by nlinarith) ?_
  rw [slowPt_add, phi2_trqSlowC_slowPt ha, phi2_trqSlowC_slowPt (by linarith)]
  simp only [add_zero]
  nlinarith

end Steps

section Phases

/-- The parameters `trqSlowParams` with initial radius `r ∈ (0, 1]`. -/
noncomputable abbrev trqSlowParamsAt (r : ℝ) (h0 : 0 < r) (h1 : r ≤ 1) : Optimization.TRqParams :=
  trqSlowParams.withΔ₀ r h0 h1

/-- `X` is closed. -/
theorem isClosed_trqSlowX : IsClosed trqSlowX :=
  isClosed_le continuous_const ((EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).continuous)

/-- `(a, b) ∈ X` for `a ≥ 1`. -/
theorem slowPt_mem_trqSlowX {a b : ℝ} (ha : 1 ≤ a) : slowPt a b ∈ trqSlowX := ha

open Classical in
/-- **The slow phase.** From `(a, 0)`, `a ≥ 2`, with radius `δ ≤ 1/2`, `A(a) ≤ ε_1` and
`ε_2 δ < 4 A(a + k δ)` for `k < K`, the `K` steps `(δ, 0)` are successful second-order iterations;
any TRq-SC run continues afterwards. -/
theorem trqSlow_slow_phase {q : ℕ} (hq : 2 ≤ q) {ε : ℕ → ℝ} {a δ : ℝ} (ha : 2 ≤ a) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1 / 2) (hε1 : trqSlowA a ≤ ε 1) {K : ℕ}
    (hK : ∀ k < K, ε 2 * δ < 4 * trqSlowA (a + k * δ)) :
    ∃ (x s : ℕ → ℝ²) (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → ℝ²), x 0 = slowPt a 0 ∧
      Chapter12.algorithm_12_2_1_feasible (phi2 trqSlowC) trqSlowX
        (trqSlowParamsAt δ hδ0 (by linarith)) q ε 1 x s Δ jk d ∧
      (∀ k < K, ¬ Chapter12.trqStop (phi2 trqSlowC) (trqSlowParamsAt δ hδ0 (by linarith)) q ε 1 x
        Δ d k) ∧
      K ≤ ((Finset.range K).filter fun k =>
        (trqSlowParamsAt δ hδ0 (by linarith)).η₁ ≤ Chapter12.trqRho (phi2 trqSlowC) x s jk k).card
        := by
  obtain ⟨W, hW⟩ := trqSlow_exists_witness
  have hδ1' : δ ≤ 1 := by linarith
  set P := trqSlowParamsAt δ hδ0 hδ1' with hP
  have hak : ∀ k : ℕ, 2 ≤ a + k * δ := fun k => by
    have : 0 ≤ (k : ℝ) * δ := by positivity
    linarith
  obtain ⟨xp, hxp⟩ : ∃ xp : ℕ → ℝ², ∀ k, xp k = slowPt (a + k * δ) 0 := ⟨_, fun _ => rfl⟩
  obtain ⟨dp, hdp⟩ : ∃ dp : ℕ → ℕ → ℝ², ∀ k, dp k = fun j => if j = 1 then slowPt (δ / 4) 0
      else if j = 2 then slowPt δ 0 else W (xp k) δ j := ⟨_, fun _ => rfl⟩
  have hmin : min δ 1 = δ := min_eq_left hδ1'
  have hstep : ∀ k < K, Optimization.IsTRqStep (ftaylorSeries ℝ (phi2 trqSlowC) (xp k))
      {e | xp k + e ∈ trqSlowX} P.ς q ε (min ((fun _ => δ) k) 1) ((fun _ => δ) k) (dp k)
      ((fun _ => 2) k) ((fun _ => slowPt δ 0) k) := fun k hk => by
    simp only [hmin, hxp]
    have hle : a ≤ a + k * δ := by have : 0 ≤ (k : ℝ) * δ := by positivity
                                   linarith
    exact trqSlow_step_axis_two hq (hak k) hδ0 hδ1' le_rfl
      ((trqSlowA_anti (by linarith) hle).trans hε1) (hK k hk)
      (by rw [hdp]; simp) (by rw [hdp]; simp)
  have hpred : ∀ k, 0 < (ftaylorSeries ℝ (phi2 trqSlowC) (xp k)).taylorDecrement 2 (slowPt δ 0) ∧
      (ftaylorSeries ℝ (phi2 trqSlowC) (xp k)).taylorDecrement 2 (slowPt δ 0) ≤
        trqSlowA (a + k * δ) * δ := fun k => by
    have h0 : 0 < a + k * δ := by linarith [hak k]
    rw [hxp, trqSlow_ΔT2_pt h0]
    have := trqSlowB_mul_le (hak k) hδ1'
    have := trqSlowA_pos h0
    have := trqSlowB_nonneg h0
    constructor <;> nlinarith
  have hacc : ∀ k < K, Optimization.TRAcceptance P.toTRParams
      (Optimization.reductionRatio (phi2 trqSlowC) (xp k) ((fun _ => slowPt δ 0) k)
        ((ftaylorSeries ℝ (phi2 trqSlowC) (xp k)).taylorDecrement ((fun _ => 2) k)
          ((fun _ => slowPt δ 0) k)))
      (xp k) ((fun _ => slowPt δ 0) k) (xp (k + 1)) ((fun _ => δ) k) ((fun _ => δ) (k + 1)) :=
    fun k _ => by
    refine trqSlow_accept_succ hδ0.le ?_ (by rw [hxp, hxp, slowPt_add]; push_cast; ring_nf)
    have := hpred k
    rw [hxp] at this ⊢
    have hA := (trqSlowA_pos (by linarith [hak k] : (0 : ℝ) < a + k * δ)).le
    exact trqSlow_ratio_axis (hak k) hδ0.le hδ1 this.1 this.2 (by
      rw [zero_pow two_ne_zero]; positivity)
  have hwit : ∀ k < K, ∀ j ∈ Finset.Icc 1 q, Optimization.IsApproxMeasureStep
      ((ftaylorSeries ℝ (phi2 trqSlowC) (xp k)).taylorDecrement j) (min ((fun _ => δ) k) 1)
      {e | xp k + e ∈ trqSlowX} P.ς (dp k j) := fun k _ j _ => by
    simp only [hmin]
    rw [hdp]
    by_cases hj1 : j = 1
    · subst hj1; simp only [↓reduceIte]; rw [hxp]; exact trqSlow_wit_axis_one (hak k) hδ0.le
    · by_cases hj2 : j = 2
      · subst hj2; simp only [↓reduceIte]; rw [hxp]
        exact trqSlow_wit_axis_two (hak k) hδ0.le hδ1'
      · simp only [hj1, hj2, ↓reduceIte]
        exact hW _ _ _ (by rw [hxp]; exact slowPt_mem_trqSlowX (by linarith [hak k])) hδ0.le
  obtain ⟨y, sy, Δy, jy, dy, hy0, hy⟩ := Optimization.exists_isTRqRun_feasible
    isClosed_trqSlowX (phi2 trqSlowC) (P.withΔ₀ δ hδ0 hδ1') q ε zero_le_one
    (show xp K ∈ trqSlowX by rw [hxp]; exact slowPt_mem_trqSlowX (by linarith [hak K]))
  obtain ⟨x, s, Δ, jk, d, hx0, hrun, hns, hcount, -, -⟩ := Optimization.exists_isTRqRun_append
    (T := K) (T' := 0) (c := 0) (P := P) (f := phi2 trqSlowC)
    (D := ftaylorSeries ℝ (phi2 trqSlowC)) (S := fun y => {e | y + e ∈ trqSlowX}) (q := q)
    (ε := ε) (ϑ := 1) (xp := xp)
    (sp := fun _ => slowPt δ 0) (Δp := fun _ => δ) (jp := fun _ => 2) (dp := dp) rfl rfl hδ0
    hδ1' hstep hacc hwit (fun _ _ => hδ1') hy0 hy (fun _ h => absurd h (Nat.not_lt_zero _))
    (Nat.zero_le _)
  refine ⟨x, s, Δ, jk, d, by rw [hx0, hxp]; simp, hrun, hns, le_trans ?_ hcount⟩
  rw [add_zero]
  refine le_of_eq ?_
  rw [Finset.filter_true_of_mem fun k hk => ?_, Finset.card_range]
  have := hpred k
  rw [hxp] at this ⊢
  have hA := (trqSlowA_pos (by linarith [hak k] : (0 : ℝ) < a + k * δ)).le
  exact trqSlow_ratio_axis (hak k) hδ0.le hδ1 this.1 this.2 (by
    rw [zero_pow two_ne_zero]; positivity)

open Classical in
/-- **The shrinking phase.** At `(a, y)`, `a ≥ 2`, `y = 2^{-N}`, `A(a) ≤ y`, `ε_1 < 4y`, starting
from the radius `1`: `N` unsuccessful first-order iterations `(0, -Δ)` halve the radius down to
`y`, and a successful one reaches `(a, 0)` keeping the radius `y`; any run from `(a, 0)` with
initial radius `y` continues. -/
theorem trqSlow_shrink_phase {q : ℕ} (hq : 2 ≤ q) {ε : ℕ → ℝ} {a y : ℝ} {N : ℕ} (ha : 2 ≤ a)
    (hyN : y = (1 / 2) ^ N) (hy0 : 0 < y) (hy1 : y ≤ 1) (hAy : trqSlowA a ≤ y)
    (hε : ε 1 < 4 * y) {xt st : ℕ → ℝ²} {Δt : ℕ → ℝ} {jt : ℕ → ℕ} {dt : ℕ → ℕ → ℝ²}
    (hxt0 : xt 0 = slowPt a 0)
    (hrun : Chapter12.algorithm_12_2_1_feasible (phi2 trqSlowC) trqSlowX
      (trqSlowParamsAt y hy0 hy1) q ε 1 xt st Δt jt dt) {T' c : ℕ}
    (hns : ∀ k < T', ¬ Chapter12.trqStop (phi2 trqSlowC) (trqSlowParamsAt y hy0 hy1) q ε 1 xt Δt
      dt k)
    (hc : c ≤ ((Finset.range T').filter fun k =>
      (trqSlowParamsAt y hy0 hy1).η₁ ≤ Chapter12.trqRho (phi2 trqSlowC) xt st jt k).card) :
    ∃ (x s : ℕ → ℝ²) (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → ℝ²), x 0 = slowPt a y ∧
      Chapter12.algorithm_12_2_1_feasible (phi2 trqSlowC) trqSlowX
        (trqSlowParamsAt 1 one_pos le_rfl) q ε 1 x s Δ jk d ∧
      (∀ k < N + 1 + T', ¬ Chapter12.trqStop (phi2 trqSlowC) (trqSlowParamsAt 1 one_pos le_rfl) q
        ε 1 x Δ d k) ∧
      c ≤ ((Finset.range (N + 1 + T')).filter fun k =>
        (trqSlowParamsAt 1 one_pos le_rfl).η₁ ≤ Chapter12.trqRho (phi2 trqSlowC) x s jk k).card
        := by
  obtain ⟨W, hW⟩ := trqSlow_exists_witness
  set P := trqSlowParamsAt 1 one_pos le_rfl with hP
  have ha0 : 0 < a := by linarith
  have hmemy : slowPt a y ∈ trqSlowX := slowPt_mem_trqSlowX (by linarith)
  obtain ⟨xp, hxp⟩ : ∃ xp : ℕ → ℝ², ∀ k, xp k = if k ≤ N then slowPt a y else slowPt a 0 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Δp, hΔp⟩ : ∃ Δp : ℕ → ℝ, ∀ k, Δp k = (1 / 2 : ℝ) ^ (min k N) := ⟨_, fun _ => rfl⟩
  obtain ⟨dp, hdp⟩ : ∃ dp : ℕ → ℕ → ℝ², ∀ k, dp k = fun j => if j = 1 then
      slowPt 0 (-(1 / 2 : ℝ) ^ k) else if j = 2 then
      slowPt ((1 / 2 : ℝ) ^ k / 2) (-min y ((1 / 2 : ℝ) ^ k / 2))
      else W (slowPt a y) ((1 / 2 : ℝ) ^ k) j := ⟨_, fun _ => rfl⟩
  have hxpl : ∀ k < N + 1, xp k = slowPt a y := fun k hk => by
    rw [hxp, ite_eq_left (by omega)]
  have hΔpl : ∀ k < N + 1, Δp k = (1 / 2 : ℝ) ^ k := fun k hk => by
    rw [hΔp, min_eq_left (by omega)]
  have hpow0 : ∀ k : ℕ, 0 < (1 / 2 : ℝ) ^ k := fun k => by positivity
  have hpow1 : ∀ k : ℕ, (1 / 2 : ℝ) ^ k ≤ 1 := fun k => pow_le_one₀ (by norm_num) (by norm_num)
  have hyk : ∀ k < N + 1, y ≤ (1 / 2 : ℝ) ^ k := fun k hk => by
    rw [hyN]; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hstep : ∀ k < N + 1, Optimization.IsTRqStep (ftaylorSeries ℝ (phi2 trqSlowC) (xp k))
      {e | xp k + e ∈ trqSlowX} P.ς q ε (min (Δp k) 1) (Δp k) (dp k) ((fun _ => 1) k)
      ((fun k => slowPt 0 (-(1 / 2 : ℝ) ^ k)) k) := fun k hk => by
    rw [hxpl k hk, hΔpl k hk, min_eq_left (hpow1 k)]
    exact trqSlow_step_shrink (by omega) ha (hpow0 k) le_rfl hε (by rw [hdp]; simp)
  have hacc : ∀ k < N + 1, Optimization.TRAcceptance P.toTRParams
      (Optimization.reductionRatio (phi2 trqSlowC) (xp k) ((fun k => slowPt 0 (-(1 / 2 : ℝ) ^ k)) k)
        ((ftaylorSeries ℝ (phi2 trqSlowC) (xp k)).taylorDecrement ((fun _ => 1) k)
          ((fun k => slowPt 0 (-(1 / 2 : ℝ) ^ k)) k)))
      (xp k) ((fun k => slowPt 0 (-(1 / 2 : ℝ) ^ k)) k) (xp (k + 1)) (Δp k) (Δp (k + 1)) :=
    fun k hk => by
    simp only
    rw [hxpl k hk, trqSlow_ΔT1_pt ha0, hΔpl k hk]
    have hpred : trqSlowA a * 0 - y * -(1 / 2 : ℝ) ^ k = y * (1 / 2 : ℝ) ^ k := by ring
    rw [hpred]
    rcases Nat.lt_or_ge k N with hkN | hkN
    · rw [hxpl (k + 1) (by omega), hΔpl (k + 1) (by omega), pow_succ, ← div_eq_mul_one_div]
      refine trqSlow_accept_unsucc (hpow0 k).le (trqSlow_ratio_shrink_unsucc ha0.le hy0 ?_)
      have := hyk (k + 1) (by omega)
      rw [pow_succ] at this
      linarith
    · have hkN' : k = N := by omega
      subst hkN'
      have e1 : xp (k + 1) = slowPt a 0 := by rw [hxp, ite_eq_right (by omega)]
      have e2 : Δp (k + 1) = (1 / 2 : ℝ) ^ k := by rw [hΔp, min_eq_right (by omega)]
      rw [e1, e2, ← hyN]
      exact trqSlow_accept_succ hy0.le (trqSlow_ratio_shrink_succ ha0.le hy0)
        (by rw [slowPt_add]; simp)
  have hwit : ∀ k < N + 1, ∀ j ∈ Finset.Icc 1 q, Optimization.IsApproxMeasureStep
      ((ftaylorSeries ℝ (phi2 trqSlowC) (xp k)).taylorDecrement j) (min (Δp k) 1)
      {e | xp k + e ∈ trqSlowX} P.ς (dp k j) := fun k hk j _ => by
    rw [hxpl k hk, hΔpl k hk, min_eq_left (hpow1 k), hdp]
    by_cases hj1 : j = 1
    · subst hj1; simp only [↓reduceIte]
      exact trqSlow_wit_shrink_one ha hy0.le hAy (hpow0 k).le
    · by_cases hj2 : j = 2
      · subst hj2; simp only [↓reduceIte]
        exact trqSlow_wit_shrink_two ha hy0.le (hyk k hk) (hpow1 k)
      · simp only [hj1, hj2, ↓reduceIte]
        exact hW _ _ _ hmemy (hpow0 k).le
  have hr : Δp (N + 1) = y := by rw [hΔp, min_eq_right (by omega), hyN]
  obtain ⟨x, s, Δ, jk, d, hx0, hrun', hns', hcount, -, -⟩ :=
    Optimization.exists_isTRqRun_append (T := N + 1) (T' := T') (c := c)
    (P := P) (f := phi2 trqSlowC)
    (D := ftaylorSeries ℝ (phi2 trqSlowC)) (S := fun y => {e | y + e ∈ trqSlowX}) (q := q)
    (ε := ε) (ϑ := 1) (xp := xp)
    (sp := fun k => slowPt 0 (-(1 / 2 : ℝ) ^ k)) (Δp := Δp) (jp := fun _ => 1) (dp := dp)
    (by rw [hΔp]; simp; rfl) hr hy0 hy1 hstep hacc hwit
    (fun k _ => by rw [hΔp]; exact hpow1 _)
    (by rw [hxt0, hxp, ite_eq_right (by omega)]) hrun hns hc
  exact ⟨x, s, Δ, jk, d, by rw [hx0, hxpl 0 (by omega)], hrun', hns', le_trans (le_add_self) hcount⟩

open Classical in
/-- **The travel phase.** From `(a₀, 0)`, `a₀ ≥ 2`, with the radius `1`, `k₀ + 1` successful
first-order steps `(1/2, 0)` (the last one `(1/2, y)`) reach `(a₀ + (k₀ + 1)/2, y)`, provided
`ε_1 < A` at the points `(a₀ + k/2, 0)`, `k ≤ k₀`, `0 ≤ y ≤ 1/2` and `y² ≤ ε_1/8`; any run from
there with the radius `1` continues. -/
theorem trqSlow_travel_phase {q : ℕ} (hq : 1 ≤ q) {ε : ℕ → ℝ} {a₀ y : ℝ} (ha₀ : 2 ≤ a₀) {k₀ : ℕ}
    (hA : ∀ k ≤ k₀, ε 1 < trqSlowA (a₀ + k / 2)) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2)
    (hy2 : y ^ 2 ≤ ε 1 / 8) {xt st : ℕ → ℝ²} {Δt : ℕ → ℝ} {jt : ℕ → ℕ} {dt : ℕ → ℕ → ℝ²}
    (hxt0 : xt 0 = slowPt (a₀ + (k₀ + 1) / 2) y)
    (hrun : Chapter12.algorithm_12_2_1_feasible (phi2 trqSlowC) trqSlowX
      (trqSlowParamsAt 1 one_pos le_rfl) q ε 1 xt st Δt jt dt) {T' c : ℕ}
    (hns : ∀ k < T', ¬ Chapter12.trqStop (phi2 trqSlowC) (trqSlowParamsAt 1 one_pos le_rfl) q ε 1
      xt Δt dt k)
    (hc : c ≤ ((Finset.range T').filter fun k =>
      (trqSlowParamsAt 1 one_pos le_rfl).η₁ ≤ Chapter12.trqRho (phi2 trqSlowC) xt st jt k).card) :
    ∃ (x s : ℕ → ℝ²) (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → ℝ²), x 0 = slowPt a₀ 0 ∧
      Chapter12.algorithm_12_2_1_feasible (phi2 trqSlowC) trqSlowX trqSlowParams q ε 1 x s Δ jk d ∧
      (∀ k < k₀ + 1 + T', ¬ Chapter12.trqStop (phi2 trqSlowC) trqSlowParams q ε 1 x Δ d k) ∧
      c ≤ ((Finset.range (k₀ + 1 + T')).filter fun k =>
        trqSlowParams.η₁ ≤ Chapter12.trqRho (phi2 trqSlowC) x s jk k).card := by
  obtain ⟨W, hW⟩ := trqSlow_exists_witness
  set P := trqSlowParams with hP
  have hak : ∀ k : ℕ, 2 ≤ a₀ + (k : ℝ) / 2 := fun k => by
    have : 0 ≤ (k : ℝ) / 2 := by positivity
    linarith
  obtain ⟨xp, hxp⟩ : ∃ xp : ℕ → ℝ², ∀ k, xp k =
      if k ≤ k₀ then slowPt (a₀ + k / 2) 0 else slowPt (a₀ + (k₀ + 1) / 2) y := ⟨_, fun _ => rfl⟩
  obtain ⟨sp, hsp⟩ : ∃ sp : ℕ → ℝ², ∀ k, sp k =
      if k < k₀ then slowPt (1 / 2) 0 else slowPt (1 / 2) y := ⟨_, fun _ => rfl⟩
  obtain ⟨dp, hdp⟩ : ∃ dp : ℕ → ℕ → ℝ², ∀ k, dp k = fun j => if j = 1 then slowPt (1 / 4) 0
      else if j = 2 then slowPt 1 0 else W (xp k) 1 j := ⟨_, fun _ => rfl⟩
  have hxpl : ∀ k < k₀ + 1, xp k = slowPt (a₀ + k / 2) 0 := fun k hk => by
    rw [hxp, ite_eq_left (by omega)]
  have hspτ : ∀ k < k₀ + 1, ∃ τ, sp k = slowPt (1 / 2) τ ∧ 0 ≤ τ ∧ τ ≤ y := fun k _ => by
    rw [hsp]
    split_ifs
    · exact ⟨0, rfl, le_rfl, hy0⟩
    · exact ⟨y, rfl, hy0, le_rfl⟩
  have hnext : ∀ k < k₀ + 1, xp (k + 1) = xp k + sp k := fun k hk => by
    rw [hxpl k hk, hsp]
    rcases Nat.lt_or_ge k k₀ with hkN | hkN
    · rw [hxpl (k + 1) (by omega), ite_eq_left hkN, slowPt_add]
      push_cast; ring_nf
    · have hkN' : k = k₀ := by omega
      subst hkN'
      rw [hxp, ite_eq_right (by omega), ite_eq_right (by omega), slowPt_add]
      ring_nf
  have hstep : ∀ k < k₀ + 1, Optimization.IsTRqStep (ftaylorSeries ℝ (phi2 trqSlowC) (xp k))
      {e | xp k + e ∈ trqSlowX} P.ς q ε (min ((fun _ => (1 : ℝ)) k) 1) ((fun _ => (1 : ℝ)) k)
      (dp k) ((fun _ => 1) k) (sp k) := fun k hk => by
    obtain ⟨τ, hτ, hτ0, hτy⟩ := hspτ k hk
    simp only [min_self]
    rw [hxpl k hk, hτ]
    refine trqSlow_step_axis_one hq (hak k) one_pos (hA k (by omega)) (by norm_num)
      ((norm_slowPt_le _ _).trans ?_) (by rw [hdp]; simp)
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), abs_of_nonneg hτ0]
    linarith
  have hacc : ∀ k < k₀ + 1, Optimization.TRAcceptance P.toTRParams
      (Optimization.reductionRatio (phi2 trqSlowC) (xp k) (sp k)
        ((ftaylorSeries ℝ (phi2 trqSlowC) (xp k)).taylorDecrement ((fun _ => 1) k) (sp k)))
      (xp k) (sp k) (xp (k + 1)) ((fun _ => (1 : ℝ)) k) ((fun _ => (1 : ℝ)) (k + 1)) :=
    fun k hk => by
    refine trqSlow_accept_succ zero_le_one ?_ (hnext k hk)
    obtain ⟨τ, hτ, hτ0, hτy⟩ := hspτ k hk
    have ha0 : 0 < a₀ + (k : ℝ) / 2 := by linarith [hak k]
    have hA0 := trqSlowA_pos ha0
    have hAk := hA k (by omega)
    simp only
    rw [hxpl k hk, hτ, trqSlow_ΔT1_pt ha0]
    have hτ2 : τ ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hτ0 hτy 2
    exact trqSlow_ratio_axis (hak k) (by norm_num) le_rfl (by nlinarith) (by nlinarith)
      (by nlinarith)
  have hwit : ∀ k < k₀ + 1, ∀ j ∈ Finset.Icc 1 q, Optimization.IsApproxMeasureStep
      ((ftaylorSeries ℝ (phi2 trqSlowC) (xp k)).taylorDecrement j) (min ((fun _ => (1 : ℝ)) k) 1)
      {e | xp k + e ∈ trqSlowX} P.ς (dp k j) := fun k hk j _ => by
    simp only [min_self]
    rw [hdp]
    by_cases hj1 : j = 1
    · subst hj1; simp only [↓reduceIte]; rw [hxpl k hk]
      exact trqSlow_wit_axis_one (hak k) zero_le_one
    · by_cases hj2 : j = 2
      · subst hj2; simp only [↓reduceIte]; rw [hxpl k hk]
        exact trqSlow_wit_axis_two (hak k) zero_le_one le_rfl
      · simp only [hj1, hj2, ↓reduceIte]
        exact hW _ _ _ (by rw [hxpl k hk]; exact slowPt_mem_trqSlowX (by linarith [hak k]))
          zero_le_one
  obtain ⟨x, s, Δ, jk, d, hx0, hrun', hns', hcount, -, -⟩ := Optimization.exists_isTRqRun_append
    (T := k₀ + 1) (T' := T') (c := c) (P := P) (f := phi2 trqSlowC)
    (D := ftaylorSeries ℝ (phi2 trqSlowC)) (S := fun y => {e | y + e ∈ trqSlowX}) (q := q)
    (ε := ε) (ϑ := 1) (xp := xp)
    (sp := sp) (Δp := fun _ => 1) (jp := fun _ => 1) (dp := dp) rfl rfl one_pos le_rfl hstep hacc
    hwit (fun _ _ => le_rfl) (by rw [hxt0, hxp, ite_eq_right (by omega)])
    hrun hns hc
  exact ⟨x, s, Δ, jk, d, by rw [hx0, hxpl 0 (by omega)]; norm_num, hrun', hns',
    le_trans (le_add_self) hcount⟩

end Phases

section LongRun

/-- `A(2^{4n}) = 2^{-5n}/8`. -/
theorem trqSlowA_two_pow (n : ℕ) : trqSlowA ((2 : ℝ) ^ (4 * n)) = (1 / 2) ^ (5 * n) / 8 := by
  unfold trqSlowA
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have e : ((4 * n : ℕ) : ℝ) * (-(5 / 4 : ℝ)) = -((5 * n : ℕ) : ℝ) := by push_cast; ring
  rw [e, Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div_pow, one_div]

/-- `A(x) ≤ 2^{-5n}/8` for `x ≥ 2^{4n}`. -/
theorem trqSlowA_le_of_ge (n : ℕ) {x : ℝ} (hx : (2 : ℝ) ^ (4 * n) ≤ x) :
    trqSlowA x ≤ (1 / 2) ^ (5 * n) / 8 :=
  (trqSlowA_anti (by positivity) hx).trans_eq (trqSlowA_two_pow n)

/-- `A(x) > 2^{-5n}/8` for `0 < x < 2^{4n}`. -/
theorem trqSlowA_gt_of_lt (n : ℕ) {x : ℝ} (hx0 : 0 < x) (hx : x < (2 : ℝ) ^ (4 * n)) :
    (1 / 2) ^ (5 * n) / 8 < trqSlowA x := by
  rw [← trqSlowA_two_pow n]
  unfold trqSlowA
  have := Real.rpow_lt_rpow_of_neg hx0 hx (by norm_num : (-(5 / 4 : ℝ)) < 0)
  linarith

/-- `2^{m+k} 2^{-k} = 2^m`. -/
theorem two_pow_add_mul_half_pow (m k : ℕ) :
    (2 : ℝ) ^ (m + k) * (1 / 2) ^ k = 2 ^ m := by
  rw [pow_add, mul_assoc, ← mul_pow]; norm_num

/-- **A long TRq-SC run on the fixed problem.** For `q ≥ 2`, `M ≥ 1`, tolerances with
`ε_1 = 2^{-10M}/2`, `ε_2 = 2^{-5M}/2`, and a starting point `(a₀, 0)` with `a₀ ≥ 2` and
`ε_1 < A(a₀)`, there is a TRq-SC run of `ν = ½‖c‖²` on `X` from `(a₀, 0)` (parameters
`trqSlowParams`, `ϑ = 1`) that does not terminate during its first `T` iterations, of which at
least `2^{22M} - 2^{18M} - 2^{10M}` are successful: the travel, shrinking and slow phases
(`trqSlow_travel_phase`, `trqSlow_shrink_phase`, `trqSlow_slow_phase`) with `y = 2^{-10M}` and
`K = 2^{22M} - 2^{18M} - 2^{10M}` slow steps. -/
theorem trqSlow_exists_long_run {q : ℕ} (hq : 2 ≤ q) {M : ℕ} (hM : 1 ≤ M) {ε : ℕ → ℝ}
    (h1 : ε 1 = (1 / 2) ^ (10 * M) / 2) (h2 : ε 2 = (1 / 2) ^ (5 * M) / 2) {a₀ : ℝ} (ha₀ : 2 ≤ a₀)
    (hA₀ : ε 1 < trqSlowA a₀) :
    ∃ (x s : ℕ → ℝ²) (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → ℝ²) (T : ℕ), x 0 = slowPt a₀ 0 ∧
      Chapter12.algorithm_12_2_1_feasible (phi2 trqSlowC) trqSlowX trqSlowParams q ε 1 x s Δ jk d ∧
      (∀ k < T, ¬ Chapter12.trqStop (phi2 trqSlowC) trqSlowParams q ε 1 x Δ d k) ∧
      2 ^ (22 * M) - 2 ^ (18 * M) - 2 ^ (10 * M) ≤ ((Finset.range T).filter fun k =>
        trqSlowParams.η₁ ≤ Chapter12.trqRho (phi2 trqSlowC) x s jk k).card := by
  classical
  obtain ⟨y, hydef⟩ : ∃ y : ℝ, y = (1 / 2) ^ (10 * M) := ⟨_, rfl⟩
  have hy0 : 0 < y := by rw [hydef]; positivity
  have hy16 : y ≤ 1 / 16 := by
    rw [hydef]
    calc ((1 : ℝ) / 2) ^ (10 * M) ≤ (1 / 2) ^ 4 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 16 := by norm_num
  have hy1 : y ≤ 1 := by linarith
  have hy10 : y ≤ 1 / 1024 := by
    rw [hydef]
    calc ((1 : ℝ) / 2) ^ (10 * M) ≤ (1 / 2) ^ 10 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 1024 := by norm_num
  have hE : ε 1 = y / 2 := by rw [h1, hydef]
  have hy8 : (1 / 2 : ℝ) ^ (5 * (2 * M)) / 8 = y / 8 := by
    rw [hydef, show 5 * (2 * M) = 10 * M by ring]
  -- the end of the travel phase
  have hex : ∃ k : ℕ, trqSlowA (a₀ + ((k : ℝ) + 1) / 2) ≤ ε 1 := by
    refine ⟨2 * 2 ^ (8 * M), (trqSlowA_le_of_ge (2 * M) ?_).trans ?_⟩
    · rw [show 4 * (2 * M) = 8 * M by ring]
      push_cast
      have : (0 : ℝ) ≤ 2 ^ (8 * M) := by positivity
      linarith
    · rw [hy8, hE]; linarith
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, k₀ = Nat.find hex := ⟨_, rfl⟩
  have hAs : trqSlowA (a₀ + ((k₀ : ℝ) + 1) / 2) ≤ ε 1 := hk₀ ▸ Nat.find_spec hex
  have hAk : ∀ k ≤ k₀, ε 1 < trqSlowA (a₀ + (k : ℝ) / 2) := fun k hk => by
    rcases k with _ | m
    · simpa using hA₀
    · have := Nat.find_min hex (show m < Nat.find hex by omega)
      push Not at this
      push_cast
      exact this
  -- `a_s < 2^{8M} + 1`
  have has : a₀ + ((k₀ : ℝ) + 1) / 2 < 2 ^ (8 * M) + 1 := by
    by_contra hcon
    push Not at hcon
    have h := hAk k₀ le_rfl
    have h' := trqSlowA_le_of_ge (2 * M) (x := a₀ + (k₀ : ℝ) / 2) (by
      rw [show 4 * (2 * M) = 8 * M by ring]; linarith)
    rw [hy8, hE] at *
    linarith
  set as := a₀ + ((k₀ : ℝ) + 1) / 2 with has_def
  have has2 : 2 ≤ as := by
    have : 0 ≤ ((k₀ : ℝ) + 1) / 2 := by positivity
    linarith
  -- the slow phase
  set K := 2 ^ (22 * M) - 2 ^ (18 * M) - 2 ^ (10 * M) with hKdef
  have hKle : 2 ^ (18 * M) + 2 ^ (10 * M) ≤ 2 ^ (22 * M) := by
    have a1 : 2 ^ (18 * M) ≤ 2 ^ (22 * M - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have a2 : 2 ^ (10 * M) ≤ 2 ^ (22 * M - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have a3 : 2 ^ (22 * M) = 2 * 2 ^ (22 * M - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  have hKs1 : 2 ^ (18 * M) ≤ 2 ^ (22 * M) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hKs2 : 2 ^ (10 * M) ≤ 2 ^ (22 * M) - 2 ^ (18 * M) :=
    Nat.le_sub_of_add_le (by rw [add_comm]; exact hKle)
  have hKr : (K : ℝ) * y = 2 ^ (12 * M) - 2 ^ (8 * M) - 1 := by
    rw [hKdef, Nat.cast_sub hKs2, Nat.cast_sub hKs1, hydef]
    push_cast
    rw [sub_mul, sub_mul, show 22 * M = 12 * M + 10 * M by ring,
      show 18 * M = 8 * M + 10 * M by ring, two_pow_add_mul_half_pow,
      two_pow_add_mul_half_pow, ← mul_pow]
    norm_num
  have hK : ∀ k < K, ε 2 * y < 4 * trqSlowA (as + k * y) := fun k hk => by
    have hkK : (k : ℝ) * y ≤ (K : ℝ) * y := by
      have : (k : ℝ) ≤ K := by exact_mod_cast hk.le
      nlinarith
    have hx : as + k * y < (2 : ℝ) ^ (4 * (3 * M)) := by
      rw [show 4 * (3 * M) = 12 * M by ring]
      linarith
    have hpos : 0 < as + k * y := by
      have : 0 ≤ (k : ℝ) * y := by positivity
      linarith
    have := trqSlowA_gt_of_lt (3 * M) hpos hx
    have e : ε 2 * y = (1 / 2) ^ (5 * (3 * M)) / 2 := by
      rw [h2, hydef, show 5 * (3 * M) = 5 * M + 10 * M by ring, pow_add]; ring
    rw [e]
    linarith
  obtain ⟨x3, s3, Δ3, j3, d3, hx3, hrun3, hns3, hc3⟩ :=
    trqSlow_slow_phase hq has2 hy0 (by linarith) (hAs.trans_eq rfl) hK
  -- the shrinking phase
  obtain ⟨x2, s2, Δ2, j2, d2, hx2, hrun2, hns2, hc2⟩ :=
    trqSlow_shrink_phase (N := 10 * M) hq has2 hydef hy0 hy1 (by linarith) (by linarith) hx3
      hrun3 hns3 hc3
  -- the travel phase
  obtain ⟨x1, s1, Δ1, j1, d1, hx1, hrun1, hns1, hc1⟩ :=
    trqSlow_travel_phase (by omega) ha₀ hAk hy0.le (by linarith) (by rw [hE]; nlinarith) hx2 hrun2
      hns2 hc2
  exact ⟨x1, s1, Δ1, j1, d1, _, hx1, hrun1, hns1, hc1⟩

end LongRun

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
  refine ⟨hX₀, hcv, hXX, fun v hv => (hcd p v hv).contDiffWithinAt, fun j hj => ?_,
    fun j hj v hv => (((hg.contDiffAt (hU.mem_nhds (hmem v hv))).of_le
      (by exact_mod_cast le_top)).norm_iteratedFDeriv_comp_coord_le (k := j) i).trans
      (hC j (Finset.mem_Icc.1 hj).1 v hv)⟩
  exact iteratedFDerivLipschitzOn_of_norm_le hcv (fun y hy => hcd (j + 1) y hy) fun v hv =>
    (((hg.contDiffAt (hU.mem_nhds (hmem v hv))).of_le
      (by exact_mod_cast le_top)).norm_iteratedFDeriv_comp_coord_le (k := j + 1) i).trans
      (hC (j + 1) (by omega) v hv)

/-- The bound on the derivatives of `g(t) = t^{-1/8}` on `t > 1/2`. -/
noncomputable def trqSlowCB (k : ℕ) : ℝ :=
  |(descPochhammer ℝ k).eval (-(1 / 8 : ℝ))| * (1 / 2 : ℝ) ^ (-(1 / 8 : ℝ) - k) + 1

/-- The derivative bounds are at least `1`. -/
theorem one_le_trqSlowCB (k : ℕ) : 1 ≤ trqSlowCB k := by
  unfold trqSlowCB
  have : 0 ≤ |(descPochhammer ℝ k).eval (-(1 / 8 : ℝ))| * (1 / 2 : ℝ) ^ (-(1 / 8 : ℝ) - k) := by
    positivity
  linarith

/-- `|g^{(k)}(t)| ≤ C_k` for `t > 1/2`. -/
theorem abs_iteratedDeriv_trqSlowG_le (k : ℕ) {t : ℝ} (ht : 1 / 2 < t) :
    |iteratedDeriv k trqSlowG t| ≤ trqSlowCB k := by
  have e : trqSlowG = fun t : ℝ => t ^ (-(1 / 8 : ℝ)) := rfl
  rw [iteratedDeriv_eq_iterate, e, Real.iter_deriv_rpow_const, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos (by linarith) _)]
  unfold trqSlowCB
  have h := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1 / 2) ht.le
    (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith : -(1 / 8 : ℝ) - k ≤ 0)
  have := abs_nonneg ((descPochhammer ℝ k).eval (-(1 / 8 : ℝ)))
  nlinarith

/-- `X₀` is open. -/
theorem isOpen_trqSlowX₀ : IsOpen trqSlowX₀ :=
  isOpen_lt continuous_const ((EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).continuous)

/-- `X₀` is convex. -/
theorem convex_trqSlowX₀ : Convex ℝ trqSlowX₀ :=
  convex_halfSpace_gt (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).isLinear _

/-- `X ⊆ X₀`. -/
theorem trqSlowX_subset : trqSlowX ⊆ trqSlowX₀ := fun v hv => by
  change 1 ≤ v 0 at hv; change 1 / 2 < v 0; linarith

/-- f.D1qLB.X for the component `g(v_1) = v_1^{-1/8}`, for every `q`, on `X₀ = {v_1 > 1/2}`. -/
theorem trqSlowG_assumption (q : ℕ) :
    AssumptionD1pLBX (fun v : ℝ² => trqSlowG (v 0)) trqSlowX trqSlowX₀ q
      (fun j => trqSlowCB (j + 1)) trqSlowCB :=
  assumptionD1pLBX_comp_coord isOpen_Ioi (fun _ hx =>
    (Real.contDiffAt_rpow_const_of_ne (ne_of_gt (mem_Ioi.1 hx))).contDiffWithinAt) 0
    isOpen_trqSlowX₀ convex_trqSlowX₀ trqSlowX_subset
    (fun v hv => mem_Ioi.2 (lt_trans (by norm_num) hv)) q
    fun k _ v hv => abs_iteratedDeriv_trqSlowG_le k hv

/-- f.D1qLB.X for the coordinate `v_2`, for every `q`, on `X₀ = {v_1 > 1/2}`. -/
theorem trqSlowCoord_assumption (q : ℕ) :
    AssumptionD1pLBX (fun v : ℝ² => v 1) trqSlowX trqSlowX₀ q (fun j => trqSlowCB (j + 1))
      trqSlowCB := by
  refine assumptionD1pLBX_comp_coord (g := fun t : ℝ => t) isOpen_univ contDiffOn_id 1
    isOpen_trqSlowX₀ convex_trqSlowX₀ trqSlowX_subset (fun _ _ => mem_univ _) q
    fun k hk v _ => ?_
  rw [iteratedDeriv_fun_id, ite_eq_right (by omega)]
  have := one_le_trqSlowCB k
  split_ifs <;> simp <;> linarith

/-- **c.D1qLB.X for the constraint of the example**, for every `q`, on `X₀ = {v_1 > 1/2}`. -/
theorem trqSlowC_assumption (q : ℕ) :
    AssumptionCD1pLBX trqSlowC trqSlowX trqSlowX₀ q (fun j => trqSlowCB (j + 1)) trqSlowCB := by
  refine ⟨isOpen_trqSlowX₀, convex_trqSlowX₀, trqSlowX_subset, fun i => ?_⟩
  fin_cases i
  · have e : (fun x : ℝ² => trqSlowC x 0) = fun v : ℝ² => (fun _ : ℝ => (1 : ℝ)) (v 0) := rfl
    simp only [Fin.zero_eta]
    rw [e]
    refine assumptionD1pLBX_comp_coord isOpen_univ contDiffOn_const 0 isOpen_trqSlowX₀
      convex_trqSlowX₀ trqSlowX_subset (fun _ _ => mem_univ _) q fun k hk v _ => ?_
    rw [iteratedDeriv_const, ite_eq_right (by omega), abs_zero]
    exact zero_le_one.trans (one_le_trqSlowCB k)
  · exact trqSlowG_assumption q
  · exact trqSlowCoord_assumption q

/-- f.D1qLB.X for the objective `f = 0`. -/
theorem trqSlowF_assumption (q : ℕ) :
    AssumptionD1pLBX (fun _ : ℝ² => (0 : ℝ)) trqSlowX trqSlowX₀ q (fun _ => 0) (fun _ => 0) := by
  have e : (fun _ : ℝ² => (0 : ℝ)) = fun v : ℝ² => (fun _ : ℝ => (0 : ℝ)) (v 0) := rfl
  rw [e]
  exact assumptionD1pLBX_comp_coord (C := fun _ => 0) isOpen_univ contDiffOn_const 0
    isOpen_trqSlowX₀ convex_trqSlowX₀ trqSlowX_subset (fun _ _ => mem_univ _) q fun k hk v _ => by
      rw [iteratedDeriv_const, ite_eq_right (by omega), abs_zero]

/-- f.B.Fb for `f = 0` (bounds `0`), for every constraint `c` and on every `ℱ_β`. -/
theorem trqSlowF_assumptionBFb {m : ℕ} (c : ℝ² → EuclideanSpace ℝ (Fin m)) (βF : ℝ) :
    Chapter07.AssumptionBFb (fun _ : ℝ² => (0 : ℝ)) c trqSlowX βF 0 0 :=
  fun _ _ => ⟨le_rfl, le_rfl⟩

end Assumptions

section TPqp

/-- `2^{-10M}/2 < A(2)` for `M ≥ 1`. -/
theorem trqSlow_tol_lt_A_two {M : ℕ} (hM : 1 ≤ M) : (1 / 2 : ℝ) ^ (10 * M) / 2 < trqSlowA 2 := by
  have h2 := trqSlowA_gt_of_lt 1 (x := 2) (by norm_num) (by norm_num)
  have : (1 / 2 : ℝ) ^ (10 * M) ≤ (1 / 2) ^ 10 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  norm_num at h2 this ⊢
  linarith

/-- The Phase-1 constant `β₁ = 1/(2‖c(x₀)‖)` of the example (`x₀ = (2, 0)`), so that
`β₁ ‖c(x₀)‖ = 1/2`. -/
noncomputable def trqSlowβ₁ : ℝ := 1 / (2 * ‖trqSlowC (slowPt 2 0)‖)

/-- `β₁ ‖c(x₀)‖ = 1/2`. -/
theorem trqSlowβ₁_mul : trqSlowβ₁ * ‖trqSlowC (slowPt 2 0)‖ = 1 / 2 := by
  have := one_le_norm_trqSlowC (slowPt 2 0)
  unfold trqSlowβ₁
  field_simp

/-- `β₁ > 0`. -/
theorem trqSlowβ₁_pos : 0 < trqSlowβ₁ := by
  have := one_le_norm_trqSlowC (slowPt 2 0)
  unfold trqSlowβ₁; positivity

/-- `β₁ < 1`. -/
theorem trqSlowβ₁_lt_one : trqSlowβ₁ < 1 := by
  have h := one_le_norm_trqSlowC (slowPt 2 0)
  have h2 := trqSlowβ₁_mul
  have h3 := trqSlowβ₁_pos
  nlinarith

open Classical in
/-- **A long TPqp-GC run on the fixed problem** (`f = 0`, `c(v) = (1, v_1^{-1/8}, v_2)`,
`X = {v_1 ≥ 1}`, `x₀ = (2, 0)`, INNER = TRq-SC with `trqSlowParams` and `ϑ = 1`,
`β₁ = trqSlowβ₁`). For `q ≥ 2`, `M ≥ 1`, any `θ ∈ (0, 1)`, any `β`, and tolerances
`ε ∈ (0, 1]^{q+1}` with `ε_1 = 2^{-10M}`, `ε_2 = 2^{-5M}`, there is a run of `IsTPqpGCTRqSCRun`
that terminates in Phase 1 (`‖c(x₁)‖ > θ ε₀`) after a single INNER call with at least
`2^{22M} - 2^{18M} - 2^{10M} + 1` derivative evaluations. -/
theorem trqSlow_exists_tpqp_run {q : ℕ} (hq : 2 ≤ q) {M : ℕ} (hM : 1 ≤ M) {θ β : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) {ε : ℕ → ℝ} (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1)
    (h1 : ε 1 = (1 / 2) ^ (10 * M)) (h2 : ε 2 = (1 / 2) ^ (5 * M)) :
    ∃ (xP : ℕ → ℝ²) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq 2) (nF₁ nD₁ : ℕ → ℕ),
      IsTPqpGCTRqSCRun (fun _ => 0) trqSlowC trqSlowX q trqSlowParams 1 θ trqSlowβ₁ β ε
        (slowPt 2 0) xP δP k₁ D nF₁ nD₁ ∧ θ * ε 0 < ‖trqSlowC (xP k₁)‖ ∧
      (((2 ^ (22 * M) - 2 ^ (18 * M) - 2 ^ (10 * M) : ℕ) : ℝ) + 1 ≤
        ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ)) := by
  set x₀ := slowPt 2 0 with hx₀
  set ε' : ℕ → ℝ := fun j => trqSlowβ₁ * ‖trqSlowC x₀‖ * phase1Tol θ ε j with hε'
  have hε'j : ∀ j, j ≠ 0 → ε' j = ε j / 2 := fun j hj => by
    simp only [hε', phase1Tol_of_ne θ ε hj]
    rw [hx₀, trqSlowβ₁_mul]; ring
  have hεI : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1 := fun j hj =>
    hε j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
  have hε₀ := hε 0 (by simp)
  obtain ⟨x, s, Δ, jk, d, T, hx0, hrun, hns, hcount⟩ := trqSlow_exists_long_run hq hM
    (ε := ε') (by rw [hε'j 1 one_ne_zero, h1]) (by rw [hε'j 2 two_ne_zero, h2]) (a₀ := 2)
    le_rfl (by rw [hε'j 1 one_ne_zero, h1]; exact trqSlow_tol_lt_A_two hM)
  obtain ⟨LA, LB, BA, BB, hν⟩ := exists_nu_trq (trqSlowC_assumption q)
  have hε'I : ∀ j ∈ Finset.Icc 1 q, ε' j ∈ Ioc 0 1 := fun j hj => by
    rw [hε'j j (by have := (Finset.mem_Icc.1 hj).1; omega)]
    have := hεI j hj
    exact ⟨by linarith, by linarith⟩
  have h1q : 1 ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
  have hϑ' : Optimization.finMin 1 ε' q ≤ 1 := (Optimization.finMin_le h1q).trans (hε'I 1 h1q).2
  have hx0X : x 0 ∈ trqSlowX := by rw [hx0]; exact slowPt_mem_trqSlowX (by norm_num)
  have hA : ∀ z ∈ trqSlowX, phi2 trqSlowC z ≤ phi2 trqSlowC (x 0) →
      z ∈ nuSublevel trqSlowC trqSlowX x₀ := fun z hz hzx => by
    rw [hx0] at hzx
    exact ⟨hz, norm_le_of_phi2_le hzx⟩
  obtain ⟨kε, hhit, hmem, hrad, hcert, -, -⟩ := Optimization.IsTRqRun.complexity
    (flow := 0) (fun z _ => by rw [phi2_apply]; positivity) (hν x₀).1.toLipschitzDerivsAnchored
    trqSlowX_subset hA hx0X hε'I hϑ' le_rfl
    hrun
  have hkT : T ≤ kε := by
    by_contra h
    exact hns kε (by omega) hhit.1
  -- the Phase-1 output
  set nD := Optimization.derivEvalCount
    (fun k => trqSlowParams.η₁ ≤ Chapter12.trqRho (phi2 trqSlowC) x s jk k) kε with hnD
  have hnDge : 2 ^ (22 * M) - 2 ^ (18 * M) - 2 ^ (10 * M) + 1 ≤ nD := by
    rw [hnD, Optimization.derivEvalCount]
    refine Nat.add_le_add_right (hcount.trans (Finset.card_le_card ?_)) 1
    exact Finset.filter_subset_filter _ (Finset.range_subset_range.2 hkT)
  obtain ⟨xP, hxP⟩ : ∃ xP : ℕ → ℝ², ∀ k, xP k = if k = 0 then x₀ else x kε := ⟨_, fun _ => rfl⟩
  have hxP0 : xP 0 = x₀ := by rw [hxP]; simp
  have hxP1 : xP 1 = x kε := by rw [hxP]; simp
  set δo : ℝ := min (Δ kε) 1 with hδo
  have hc1 : 1 ≤ ‖trqSlowC (xP 1)‖ := one_le_norm_trqSlowC _
  have hc0 : θ * ε 0 < 1 := by nlinarith
  have hstop1 : lenStop trqSlowC trqSlowX q (phase1Tol θ ε) xP (fun _ _ => δo) 1 := by
    refine Or.inr ⟨le_rfl, fun j hj => ?_⟩
    have hcj := hcert j hj
    rw [← hxP1] at hcj
    refine hcj.trans ?_
    rw [hε'j j (by have := (Finset.mem_Icc.1 hj).1; omega),
      phase1Tol_of_ne θ ε (by have := (Finset.mem_Icc.1 hj).1; omega)]
    have hεj := (hεI j hj).1
    have hδ0 : 0 ≤ δo := hrad.1.le
    have : ε j / 2 ≤ ε j * ‖trqSlowC (xP 1)‖ := by nlinarith
    gcongr
  have hnstop0 : ¬ lenStop trqSlowC trqSlowX q (phase1Tol θ ε) xP (fun _ _ => δo) 0 := by
    rintro (h | ⟨h, -⟩)
    · rw [phase1Tol_zero, hxP0] at h
      have := one_le_norm_trqSlowC x₀
      linarith
    · omega
  have hhit1 : Optimization.IsFirstHit (lenStop trqSlowC trqSlowX q (phase1Tol θ ε) xP
      (fun _ _ => δo)) 1 := ⟨hstop1, fun j hj => by
        obtain rfl : j = 0 := by omega
        exact hnstop0⟩
  have hbig : ∀ k, 2 ≤ k → ¬ (∀ i < k, ¬ lenStop trqSlowC trqSlowX q (phase1Tol θ ε) xP
      (fun _ _ => δo) i) := fun k hk h => h 1 (by omega) hstop1
  have hk1 : ∀ k, 1 ≤ k → (∀ i < k, ¬ lenStop trqSlowC trqSlowX q (phase1Tol θ ε) xP
      (fun _ _ => δo) i) → k = 1 := fun k h1k h => by
    by_contra hne
    exact hbig k (by omega) h
  have hphase1 : algorithm_14_3_1 trqSlowC trqSlowX q (phase1Tol θ ε) trqSlowβ₁ xP
      (fun _ _ => δo) := by
    refine ⟨by rw [hxP0]; exact slowPt_mem_trqSlowX (by norm_num), fun j hj => ?_,
      fun j hj => ?_, trqSlowβ₁_pos, trqSlowβ₁_lt_one, by rw [hxP0, trqSlowβ₁_mul]; norm_num,
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
    fun _ => 0, fun _ _ => False⟩, fun _ => Optimization.funEvalCount kε, fun _ => nD,
    ⟨⟨hxP0, hphase1, hhit1, fun h => absurd h (by linarith)⟩, fun k h1k hk1' => ?_,
      fun h => absurd h (by linarith)⟩, by linarith, ?_⟩
  · obtain rfl : k = 1 := by omega
    simp only [Nat.sub_self, hxP0]
    exact ⟨x, s, Δ, jk, d, kε, hrun, hhit, hx0, hxP1.symm, fun _ _ => rfl, rfl, rfl⟩
  · rw [Finset.Icc_self, Finset.sum_singleton]
    exact_mod_cast hnDge

end TPqp

section Phase2Data

/-- The constraint of the Phase-2 example: `c₂(v) = (v_1^{-1/8}, v_2)` (the constraint `trqSlowC`
without its constant component, so that `‖c₂‖` is small at `x₀ = (256, 0)` and Phase 1 ends at
once). -/
noncomputable def trqSlowC2 : ℝ² → ℝ² := fun v => WithLp.toLp 2 ![trqSlowG (v 0), v 1]

/-- `‖c₂(v)‖² = g(v_1)² + v_2²`. -/
theorem norm_trqSlowC2_sq (v : ℝ²) : ‖trqSlowC2 v‖ ^ 2 = trqSlowG (v 0) ^ 2 + (v 1) ^ 2 := by
  rw [trqLog_norm_sq]; rfl

/-- With `f = 0`, `μ(v, t) = ½‖c(v)‖² - (1 - t²)/2` (`c = trqSlowC`). -/
theorem targetMerit_trqSlowC2 (t : ℝ) (v : ℝ²) :
    Constrained.targetMerit (fun _ => 0) trqSlowC2 t v = phi2 trqSlowC v - (1 - t ^ 2) / 2 := by
  rw [Constrained.targetMerit_def, norm_trqSlowC2_sq, phi2_apply, norm_trqSlowC_sq]; ring

/-- The Taylor decrements of `μ(·, t)` (`f = 0`, `c = c₂`) and of `½‖c‖²` (`c = trqSlowC`) agree on
the open half-plane `v_1 > 0`. -/
theorem taylorDecrement_targetMerit_trqSlowC2 (t : ℝ) {v : ℝ²} (hv : 0 < v 0) (j : ℕ) :
    (ftaylorSeries ℝ (Constrained.targetMerit (fun _ => 0) trqSlowC2 t) v).taylorDecrement j =
      (ftaylorSeries ℝ (phi2 trqSlowC) v).taylorDecrement j := by
  have hU : IsOpen {w : ℝ² | 0 < w 0} :=
    isOpen_lt continuous_const ((EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).continuous)
  have hev : Constrained.targetMerit (fun _ => 0) trqSlowC2 t =ᶠ[𝓝 v]
      fun w => trqSlowNu w - (1 - t ^ 2) / 2 := by
    filter_upwards [hU.mem_nhds hv] with w hw
    rw [targetMerit_trqSlowC2 t w, phi2_trqSlowC_eq (le_of_lt hw)]
  rw [(hev.ftaylorSeries ℝ).eq_of_nhds, ftaylorSeries_phi2_trqSlowC hv]
  funext s
  rw [FormalMultilinearSeries.taylorDecrement_eq, FormalMultilinearSeries.taylorDecrement_eq]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  congr 1
  change iteratedFDeriv ℝ i (fun w => trqSlowNu w - (1 - t ^ 2) / 2) v (fun _ => s) =
    iteratedFDeriv ℝ i trqSlowNu v (fun _ => s)
  rw [iteratedFDeriv_sub_const_apply (by have := (Finset.mem_Icc.1 hi).1; omega)
    (contDiffAt_trqSlowNu hv i)]

/-- **c.D1qLB.X for `c₂`**, for every `q`, on `X₀ = {v_1 > 1/2}`. -/
theorem trqSlowC2_assumption (q : ℕ) :
    AssumptionCD1pLBX trqSlowC2 trqSlowX trqSlowX₀ q (fun j => trqSlowCB (j + 1)) trqSlowCB := by
  refine ⟨isOpen_trqSlowX₀, convex_trqSlowX₀, trqSlowX_subset, fun i => ?_⟩
  fin_cases i
  · exact trqSlowG_assumption q
  · exact trqSlowCoord_assumption q

/-- `g(256) = 1/2`. -/
theorem trqSlowG_256 : trqSlowG 256 = 1 / 2 := by
  rw [trqSlowG, show (256 : ℝ) = 2 ^ ((8 : ℕ) : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- `‖c₂(256, 0)‖ = 1/2`. -/
theorem norm_trqSlowC2_x₀ : ‖trqSlowC2 (slowPt 256 0)‖ = 1 / 2 := by
  have h := norm_trqSlowC2_sq (slowPt 256 0)
  simp only [slowPt_apply_zero, slowPt_apply_one, trqSlowG_256] at h
  nlinarith [norm_nonneg (trqSlowC2 (slowPt 256 0))]

/-- `2^{-10M}/2 < A(256)` for `M ≥ 2`. -/
theorem trqSlow_tol_lt_A_256 {M : ℕ} (hM : 2 ≤ M) :
    (1 / 2 : ℝ) ^ (10 * M) / 2 < trqSlowA 256 := by
  have h := trqSlowA_two_pow 2
  rw [show (2 : ℝ) ^ (4 * 2) = 256 by norm_num] at h
  rw [h]
  have : (1 / 2 : ℝ) ^ (10 * M) ≤ (1 / 2) ^ 20 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  norm_num at this ⊢
  linarith

end Phase2Data

section Phase2Run

open Classical in
/-- **A long TPqp-GC run that enters Phase 2** on the fixed problem `f = 0`,
`c₂(v) = (v_1^{-1/8}, v_2)`, `X = {v_1 ≥ 1}`, `x₀ = (256, 0)`, with `θ = β = 1/2`, any
`β₁ ∈ (0, 1)`, INNER = TRq-SC with `trqSlowParams` and `ϑ = 1`. For `q ≥ 2`, `M ≥ 2` and
tolerances `ε ∈ (0, 1]^{q+1}` with `ε₀ = 1`, `ε_1 = 2^{-10M}`, `ε_2 = 2^{-5M}`: Phase 1 ends at
once (`‖c₂(x₀)‖ = 1/2 = θ ε₀`), and Phase 2 consists of a single INNER call on `μ(·, t_1)`, which
differs from `½‖c‖²` (`c = trqSlowC`) by a constant, followed by a termination in case (c); every
termination index of Phase 2 has at least `2^{22M} - 2^{18M} - 2^{10M} + 1` derivative
evaluations. -/
theorem trqSlow_exists_tpqp_run_phase2 {q : ℕ} (hq : 2 ≤ q) {M : ℕ} (hM : 2 ≤ M) {β₁ : ℝ}
    (hβ₁0 : 0 < β₁) (hβ₁1 : β₁ < 1) {ε : ℕ → ℝ}
    (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) (h0 : ε 0 = 1)
    (h1 : ε 1 = (1 / 2) ^ (10 * M)) (h2 : ε 2 = (1 / 2) ^ (5 * M)) :
    ∃ (xP : ℕ → ℝ²) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq 2) (nF₁ nD₁ : ℕ → ℕ),
      IsTPqpGCTRqSCRun (fun _ => 0) trqSlowC2 trqSlowX q trqSlowParams 1 (1 / 2) β₁ (1 / 2) ε
        (slowPt 256 0) xP δP k₁ D nF₁ nD₁ ∧ ‖trqSlowC2 (xP k₁)‖ ≤ 1 / 2 * ε 0 ∧
      ∀ kε, D.IsEnd (fun _ => 0) trqSlowC2 trqSlowX q (1 / 2) ε kε →
        (((2 ^ (22 * M) - 2 ^ (18 * M) - 2 ^ (10 * M) : ℕ) : ℝ) + 1 ≤ D.derivEvals kε) := by
  set x₀ := slowPt 256 0 with hx₀
  have hcx₀ : ‖trqSlowC2 x₀‖ = 1 / 2 := norm_trqSlowC2_x₀
  have hx₀X : x₀ ∈ trqSlowX := slowPt_mem_trqSlowX (by norm_num)
  obtain ⟨t₁, ht₁⟩ : ∃ t₁ : ℝ, t₁ = (fun _ : ℝ² => (0 : ℝ)) x₀ - √(ε 0 ^ 2 - ‖trqSlowC2 x₀‖ ^ 2) :=
    ⟨_, rfl⟩
  have ht₁sq : t₁ ^ 2 = 3 / 4 := by
    rw [ht₁, h0, hcx₀]
    simp only [zero_sub, neg_sq]
    rw [Real.sq_sqrt (by norm_num)]
    norm_num
  set G := Constrained.targetMerit (fun _ : ℝ² => (0 : ℝ)) trqSlowC2 t₁ with hG
  have hres_ge : ∀ v, 1 / 2 ≤ Constrained.targetResidual (fun _ : ℝ² => (0 : ℝ)) trqSlowC2 t₁ v :=
    fun v => by
    have h := Constrained.targetResidual_sq (f := fun _ : ℝ² => (0 : ℝ)) (c := trqSlowC2) (t := t₁)
      (x := v)
    have hn := Constrained.targetResidual_nonneg (f := fun _ : ℝ² => (0 : ℝ)) (c := trqSlowC2)
      (t := t₁) (x := v)
    nlinarith [sq_nonneg ‖trqSlowC2 v‖]
  have hres0 : Constrained.targetResidual (fun _ : ℝ² => (0 : ℝ)) trqSlowC2 t₁ x₀ = 1 := by
    have h := Constrained.targetResidual_sq (f := fun _ : ℝ² => (0 : ℝ)) (c := trqSlowC2) (t := t₁)
      (x := x₀)
    have hn := Constrained.targetResidual_nonneg (f := fun _ : ℝ² => (0 : ℝ)) (c := trqSlowC2)
      (t := t₁) (x := x₀)
    rw [hcx₀] at h
    nlinarith
  set ε' : ℕ → ℝ := fun j =>
    1 / 2 * Constrained.targetResidual (fun _ : ℝ² => (0 : ℝ)) trqSlowC2 t₁ x₀ * ε j with hε'
  have hε'j : ∀ j, ε' j = ε j / 2 := fun j => by simp only [hε', hres0]; ring
  have hεI : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1 := fun j hj =>
    hε j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
  -- the run of TRq-SC on `½‖c‖²`
  obtain ⟨x, s, Δ, jk, d, T, hx0, hrunF, hns, hcount⟩ := trqSlow_exists_long_run hq
    (by omega : 1 ≤ M) (ε := ε') (by rw [hε'j, h1]) (by rw [hε'j, h2]) (a₀ := 256) (by norm_num)
    (by rw [hε'j, h1]; exact trqSlow_tol_lt_A_256 hM)
  obtain ⟨LA, LB, BA, BB, hν⟩ := exists_nu_trq (trqSlowC_assumption q)
  have hε'I : ∀ j ∈ Finset.Icc 1 q, ε' j ∈ Ioc 0 1 := fun j hj => by
    rw [hε'j]
    have := hεI j hj
    exact ⟨by linarith, by linarith⟩
  have h1q : 1 ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
  have hϑ' : Optimization.finMin 1 ε' q ≤ 1 := (Optimization.finMin_le h1q).trans (hε'I 1 h1q).2
  have hx0X : x 0 ∈ trqSlowX := by rw [hx0]; exact hx₀X
  have hA : ∀ z ∈ trqSlowX, phi2 trqSlowC z ≤ phi2 trqSlowC (x 0) →
      z ∈ nuSublevel trqSlowC trqSlowX x₀ := fun z hz hzx => by
    rw [hx0] at hzx
    exact ⟨hz, norm_le_of_phi2_le hzx⟩
  obtain ⟨kε, hhit, hmem, hrad, hcert, -, -⟩ := Optimization.IsTRqRun.complexity
    (flow := 0) (fun z _ => by rw [phi2_apply]; positivity) (hν x₀).1.toLipschitzDerivsAnchored
    trqSlowX_subset hA hx0X hε'I hϑ' le_rfl
    hrunF
  have hkT : T ≤ kε := by
    by_contra h
    exact hns kε (by omega) hhit.1
  -- the same run on `μ(·, t₁)`
  have hT : ∀ y ∈ trqSlowX, ∀ j, (ftaylorSeries ℝ G y).taylorDecrement j =
      (ftaylorSeries ℝ (phi2 trqSlowC) y).taylorDecrement j := fun y hy j =>
    taylorDecrement_targetMerit_trqSlowC2 t₁ (lt_of_lt_of_le one_pos hy) j
  have hD : ∀ y ∈ trqSlowX, ∀ z ∈ trqSlowX, G y - G z = phi2 trqSlowC y - phi2 trqSlowC z :=
    fun y _ z _ => by rw [hG, targetMerit_trqSlowC2, targetMerit_trqSlowC2]; ring
  obtain ⟨hrunG, hiff, hrho⟩ := hrunF.congr_of_taylorDecrement_eq hT hD hx0X
  have hhitG : Optimization.IsFirstHit
      (Chapter12.trqStop G trqSlowParams q ε' 1 x Δ d) kε :=
    ⟨(hiff kε hhit.2).2 hhit.1, fun i hi hGi =>
      hhit.2 i hi ((hiff i fun j hj => hhit.2 j (hj.trans hi)).1 hGi)⟩
  set δo : ℝ := min (Δ kε) 1 with hδo
  -- the Phase-2 sequences
  obtain ⟨Dx, hDx⟩ : ∃ Dx : ℕ → ℝ², ∀ k, Dx k = if k ≤ 1 then x₀ else x kε := ⟨_, fun _ => rfl⟩
  set D : TPqpSeq 2 := ⟨Dx, fun _ => t₁, fun _ _ => δo, fun _ => x, fun _ => kε,
    fun _ i => trqSlowParams.η₁ ≤ Chapter12.trqRho G x s jk i⟩ with hDdef
  have hDx1 : D.x 1 = x₀ := by simp [hDdef, hDx]
  have hDx2 : D.x 2 = x kε := by simp [hDdef, hDx]
  have hnotKa : ¬ D.IsKa (fun _ => 0) trqSlowC2 (1 / 2) ε 1 := by
    change ¬ (Constrained.targetResidual _ _ t₁ (D.x 2) < 1 / 2 * ε 0)
    rw [h0, mul_one]
    exact not_lt.2 (hres_ge _)
  have hnotKb : ¬ D.IsKb (fun _ => 0) trqSlowC2 (1 / 2) ε 1 := by
    rintro ⟨-, hlt⟩
    change (0 : ℝ) < t₁ at hlt
    have : t₁ ≤ 0 := by rw [ht₁]; simp
    linarith
  have hstop1 : D.Stop (fun _ => 0) trqSlowC2 trqSlowX q (1 / 2) ε 1 := Or.inl ⟨hnotKa, hnotKb⟩
  have hbef : ∀ k, 1 ≤ k → D.Before (fun _ => 0) trqSlowC2 trqSlowX q (1 / 2) ε k → k = 1 :=
    fun k hk hb => by
    by_contra hne
    exact hb 1 le_rfl (by omega) hstop1
  have hcertG : ∀ j ∈ Finset.Icc 1 q, Optimization.taylorMeasure (ftaylorSeries ℝ G (x kε)) j δo
      {e | x kε + e ∈ trqSlowX} ≤ ε j * Constrained.targetResidual (fun _ => 0) trqSlowC2 t₁
        (x kε) * δo ^ j / j ! := fun j hj => by
    have hcj := hcert j hj
    have e : Optimization.taylorMeasure (ftaylorSeries ℝ G (x kε)) j δo {e | x kε + e ∈ trqSlowX}
        = Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 trqSlowC) (x kε)) j δo
          {e | x kε + e ∈ trqSlowX} := by
      simp only [Optimization.taylorMeasure_eq_sSup, hT _ hmem j]
    rw [e]
    refine hcj.trans ?_
    rw [hε'j]
    have hεj := (hεI j hj).1
    have hδ0 : 0 ≤ δo := hrad.1.le
    have := hres_ge (x kε)
    have : ε j / 2 ≤ ε j * Constrained.targetResidual (fun _ => 0) trqSlowC2 t₁ (x kε) := by
      nlinarith
    gcongr
  have hphase2 : IsTPqpGCPhase2 (fun _ => 0) trqSlowC2 trqSlowX q (1 / 2) (1 / 2) ε x₀ D := by
    refine ⟨by norm_num, by norm_num, by norm_num, le_rfl, fun j hj => (hε j hj).1,
      fun j hj => (hε j hj).2, hx₀X, by rw [hcx₀, h0]; norm_num, hDx1, ht₁,
      fun k hk hb => ?_, fun k hk hb => ?_, fun k hk hb => ?_, fun k hk hb => ?_,
      fun k hk hb => ?_, fun k hk hb i hi => ?_, fun k hk hb i hi => ?_,
      fun k hk hb ha => ?_, fun k hk hb hb' => ?_⟩
    · obtain rfl := hbef k hk hb; rw [hDx2]; exact hmem
    · obtain rfl := hbef k hk hb; exact fun _ _ => hrad
    · obtain rfl := hbef k hk hb
      refine Or.inr (Or.inr fun j hj => ?_)
      rw [hDx2]
      exact hcertG j hj
    · obtain rfl := hbef k hk hb; rw [hDx1]; exact hx0
    · obtain rfl := hbef k hk hb; rw [hDx2]
    · obtain rfl := hbef k hk hb
      exact Optimization.IsTRqRun.apply_succ_le hrunG (fun j hj => (hε'I j hj).1.le) zero_le_one
        fun l hl => hhitG.2 l (lt_of_le_of_lt hl hi)
    · obtain rfl := hbef k hk hb
      rw [h0, mul_one]; exact hres_ge _
    · obtain rfl := hbef k hk hb; exact absurd ha hnotKa
    · obtain rfl := hbef k hk hb; exact absurd hb' hnotKb
  have hcalls : IsTRqSCPhase2Calls (fun _ => 0) trqSlowC2 trqSlowX q trqSlowParams 1 (1 / 2)
      (1 / 2) ε D := fun k hk hb => by
    obtain rfl := hbef k hk hb
    rw [hDx1]
    exact ⟨x, s, Δ, jk, d, kε, hrunG, hhitG, le_rfl, fun _ _ => rfl, fun _ _ => Iff.rfl,
      fun _ _ => rfl⟩
  -- Phase 1 ends at once
  have hstop0 : lenStop trqSlowC2 trqSlowX q (phase1Tol (1 / 2) ε) (fun _ => x₀)
      (fun _ _ => 1) 0 := Or.inl (by rw [phase1Tol_zero, hcx₀, h0]; norm_num)
  have hphase1 : algorithm_14_3_1 trqSlowC2 trqSlowX q (phase1Tol (1 / 2) ε) β₁ (fun _ => x₀)
      (fun _ _ => 1) := by
    refine ⟨hx₀X, fun j hj => ?_, fun j hj => ?_, hβ₁0, hβ₁1, by rw [hcx₀]; linarith,
      fun k _ h => absurd hstop0 (h 0 (by omega)), fun k _ h => absurd hstop0 (h 0 (by omega)),
      fun k _ h => absurd hstop0 (h 0 (by omega))⟩
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [phase1Tol_zero, h0]; norm_num
      · rw [phase1Tol_of_ne _ ε hj0.ne']; exact (hε j hj).1
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [phase1Tol_zero, h0]; norm_num
      · rw [phase1Tol_of_ne _ ε hj0.ne']; exact (hε j hj).2
  refine ⟨fun _ => x₀, fun _ _ => 1, 0, D, fun _ => 0, fun _ => 0,
    ⟨⟨rfl, hphase1, ⟨hstop0, fun j hj => absurd hj (Nat.not_lt_zero _)⟩, fun _ => hphase2⟩,
      fun k hk hk0 => absurd hk (by omega), fun _ => hcalls⟩,
    by rw [hcx₀, h0]; norm_num, fun kε' hend => ?_⟩
  -- the derivative evaluations
  obtain rfl : kε' = 1 := hbef kε' hend.1 hend.2.2
  have hsucc : 2 ^ (22 * M) - 2 ^ (18 * M) - 2 ^ (10 * M) ≤ D.succCount 1 := by
    refine hcount.trans (Finset.card_le_card fun i hi => ?_)
    rw [Finset.mem_filter] at hi ⊢
    have hiT := Finset.mem_range.1 hi.1
    refine ⟨Finset.mem_range.2 (by change i < kε; omega), ?_⟩
    change trqSlowParams.η₁ ≤ Optimization.trqRatio G (fun k => ftaylorSeries ℝ G (x k)) x s jk i
    rw [hrho i fun l hl => hhit.2 l (by omega)]
    exact hi.2
  rw [Constrained.HighOrderTargetSeq.derivEvals_eq_sum, Finset.Icc_self, Finset.sum_singleton]
  push_cast
  have : ((2 ^ (22 * M) - 2 ^ (18 * M) - 2 ^ (10 * M) : ℕ) : ℝ) ≤ (D.succCount 1 : ℝ) := by
    exact_mod_cast hsucc
  linarith

end Phase2Run

section Main

/-- The tolerances of the counterexample: `ε_1 = 2^{-10M}`, `ε_2 = 2^{-5M}`, `ε_j = 1` otherwise
(in particular `ε₀ = 1`). -/
noncomputable def trqSlowTol (M : ℕ) : ℕ → ℝ := fun j =>
  if j = 1 then (1 / 2) ^ (10 * M) else if j = 2 then (1 / 2) ^ (5 * M) else 1

/-- The tolerances `trqSlowTol M` lie in `(0, 1]`. -/
theorem trqSlowTol_mem (M : ℕ) (j : ℕ) : 0 < trqSlowTol M j ∧ trqSlowTol M j ≤ 1 := by
  unfold trqSlowTol
  split_ifs
  · exact ⟨by positivity, pow_le_one₀ (by norm_num) (by norm_num)⟩
  · exact ⟨by positivity, pow_le_one₀ (by norm_num) (by norm_num)⟩
  · exact ⟨one_pos, le_rfl⟩

/-- `((1/2)^n)^{-k} = 2^{nk}`. -/
theorem half_pow_rpow_neg (n k : ℕ) : ((1 / 2 : ℝ) ^ n) ^ (-(k : ℝ)) = 2 ^ (n * k) := by
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← pow_mul, one_div, inv_pow, inv_inv]

/-- For the tolerances `trqSlowTol M` (`q ≥ 2`), the printed function-evaluation order of
Theorem 14.3.9 is at most `2^{20M}`. -/
theorem tpqpOrderF_trqSlowTol_le {q : ℕ} (M : ℕ) :
    tpqpOrderF (fun j => (j : ℝ) + 1) q (trqSlowTol M) ≤ 2 ^ (20 * M) := by
  have h0 : trqSlowTol M 0 = 1 := by simp [trqSlowTol]
  have h1M : (1 : ℝ) ≤ 2 ^ (20 * M) := one_le_pow₀ (by norm_num)
  refine Optimization.finMax_le (by rw [h0, inv_one]; exact h1M) fun j hj => ?_
  rw [h0, Real.one_rpow, one_mul]
  have hj1 := (Finset.mem_Icc.1 hj).1
  by_cases hj1' : j = 1
  · subst hj1'
    have e : -((((1 : ℕ) : ℝ)) + 1) = -((2 : ℕ) : ℝ) := by norm_num
    rw [e, show trqSlowTol M 1 = (1 / 2) ^ (10 * M) by simp [trqSlowTol], half_pow_rpow_neg]
    rw [show 10 * M * 2 = 20 * M by ring]
  · by_cases hj2 : j = 2
    · subst hj2
      have e : -((((2 : ℕ) : ℝ)) + 1) = -((3 : ℕ) : ℝ) := by norm_num
      rw [e, show trqSlowTol M 2 = (1 / 2) ^ (5 * M) by simp [trqSlowTol], half_pow_rpow_neg]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    · rw [show trqSlowTol M j = 1 by simp [trqSlowTol, hj1', hj2], Real.one_rpow]
      exact h1M

/-- For the tolerances `trqSlowTol M` (`q ≥ 2`), the logarithmic factor of `theorem_14_3_9_trq`
is `|log(ε₀ ε_min)| = 10 M log 2 ≤ 10 M`. -/
theorem trqSCLogTerm_trqSlowTol_le {q : ℕ} (hq : 2 ≤ q) (M : ℕ) :
    trqSCLogTerm q (trqSlowTol M) ≤ 10 * M := by
  have h0 : trqSlowTol M 0 = 1 := by simp [trqSlowTol]
  have h1q : 1 ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
  have hmin : Optimization.finMin 1 (trqSlowTol M) q = (1 / 2) ^ (10 * M) := by
    refine le_antisymm ((Optimization.finMin_le h1q).trans_eq (by simp [trqSlowTol]))
      (Optimization.le_finMin (pow_le_one₀ (by norm_num) (by norm_num)) fun j hj => ?_)
    unfold trqSlowTol
    split_ifs
    · exact le_rfl
    · exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    · exact pow_le_one₀ (by norm_num) (by norm_num)
  unfold trqSCLogTerm
  rw [h0, one_mul, hmin, Real.log_pow, one_div, Real.log_inv, abs_mul, abs_neg,
    abs_of_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  rw [Nat.abs_cast]
  push_cast
  have : (0 : ℝ) ≤ 10 * M := by positivity
  nlinarith

/-- `|κ| (1 + 10M) 2^{20M} < 2^{22M}/2` for `M > 20|κ| + 20`. -/
theorem trqSlow_final_lt {κ : ℝ} {M : ℕ} (hM : 20 * |κ| + 20 < M) :
    |κ| * (1 + 10 * M) * 2 ^ (20 * M) < (2 : ℝ) ^ (22 * M) / 2 := by
  have h2M : (M : ℝ) + 1 ≤ 2 ^ M := by exact_mod_cast Nat.lt_two_pow_self
  have e : (2 : ℝ) ^ (22 * M) = (2 ^ M) ^ 2 * 2 ^ (20 * M) := by
    rw [← pow_mul, ← pow_add]; ring_nf
  rw [e]
  have hB : (0 : ℝ) < 2 ^ (20 * M) := by positivity
  have hκ := abs_nonneg κ
  have hsq : ((M : ℝ) + 1) ^ 2 ≤ (2 ^ M) ^ 2 := pow_le_pow_left₀ (by positivity) h2M 2
  have key : 2 * (|κ| * (1 + 10 * M)) < ((M : ℝ) + 1) ^ 2 := by nlinarith
  nlinarith

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
      κ * (1 + trqSCLogTerm q ε) * tpqpOrderF (fun j => (j : ℝ) + 1) q ε := by
  have hDF := tpqpOrderD_le_tpqpOrderF (π := fun j => (j : ℝ) + 1) (q := q) h0
  have hO1 := one_le_tpqpOrderF (π := fun j => (j : ℝ) + 1) (q := q) h0 h1
  have hΛ : 0 ≤ trqSCLogTerm q ε := abs_nonneg _
  calc κ * tpqpOrderD (fun j => (j : ℝ) + 1) q ε ≤ κ * tpqpOrderF (fun j => (j : ℝ) + 1) q ε :=
        mul_le_mul_of_nonneg_left hDF hκ
    _ ≤ κ * (1 + trqSCLogTerm q ε) * tpqpOrderF (fun j => (j : ℝ) + 1) q ε := by
      rw [mul_assoc]
      gcongr
      nlinarith

/-- **The count against the printed order**: for `M > 20|κ| + 20`, a count
`N ≥ 2^{22M} - 2^{18M} - 2^{10M} + 1` exceeds `κ (1 + |log(ε₀ ε_min)|) max[ε₀^{-1},
max_j ε₀^{-j} ε_j^{-(j+1)}]` at the tolerances `trqSlowTol M` (`q ≥ 2`). -/
theorem trqSlow_not_le_printed {q : ℕ} (hq : 2 ≤ q) {κ : ℝ} {M : ℕ} (hM : 20 * |κ| + 20 < M)
    {N : ℝ} (hN : ((2 ^ (22 * M) - 2 ^ (18 * M) - 2 ^ (10 * M) : ℕ) : ℝ) + 1 ≤ N) :
    ¬ N ≤ κ * (1 + trqSCLogTerm q (trqSlowTol M)) *
      tpqpOrderF (fun j => (j : ℝ) + 1) q (trqSlowTol M) := by
  have hM1 : 1 ≤ M := by
    have : (1 : ℝ) < M := by linarith [abs_nonneg κ]
    exact_mod_cast this.le
  have hΛ := trqSCLogTerm_trqSlowTol_le hq M
  have hΛ0 : 0 ≤ trqSCLogTerm q (trqSlowTol M) := abs_nonneg _
  have hO := tpqpOrderF_trqSlowTol_le (q := q) M
  have hO0 : 0 ≤ tpqpOrderF (fun j => (j : ℝ) + 1) q (trqSlowTol M) :=
    zero_le_one.trans (one_le_tpqpOrderF (trqSlowTol_mem M 0).1 (trqSlowTol_mem M 0).2)
  have hR : κ * (1 + trqSCLogTerm q (trqSlowTol M)) *
      tpqpOrderF (fun j => (j : ℝ) + 1) q (trqSlowTol M) ≤ |κ| * (1 + 10 * M) * 2 ^ (20 * M) := by
    have hX : 0 ≤ (1 + trqSCLogTerm q (trqSlowTol M)) *
        tpqpOrderF (fun j => (j : ℝ) + 1) q (trqSlowTol M) := by positivity
    rw [mul_assoc, mul_assoc]
    refine (mul_le_mul_of_nonneg_right (le_abs_self κ) hX).trans
      (mul_le_mul_of_nonneg_left ?_ (abs_nonneg κ))
    exact mul_le_mul (by linarith) hO hO0 (by positivity)
  -- the count
  have hKs1 : 2 ^ (18 * M) ≤ 2 ^ (22 * M) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hKle : 2 ^ (18 * M) + 2 ^ (10 * M) ≤ 2 ^ (22 * M) := by
    have a1 : 2 ^ (18 * M) ≤ 2 ^ (22 * M - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have a2 : 2 ^ (10 * M) ≤ 2 ^ (22 * M - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have a3 : 2 ^ (22 * M) = 2 * 2 ^ (22 * M - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  have hKs2 : 2 ^ (10 * M) ≤ 2 ^ (22 * M) - 2 ^ (18 * M) :=
    Nat.le_sub_of_add_le (by rw [add_comm]; exact hKle)
  rw [Nat.cast_sub hKs2, Nat.cast_sub hKs1] at hN
  push_cast at hN
  have h18 : (2 : ℝ) ^ (18 * M) * 4 ≤ 2 ^ (22 * M) := by
    rw [show 22 * M = 18 * M + 2 + (4 * M - 2) by omega, pow_add, pow_add]
    have : (1 : ℝ) ≤ 2 ^ (4 * M - 2) := one_le_pow₀ (by norm_num)
    have : (0 : ℝ) < 2 ^ (18 * M) := by positivity
    nlinarith
  have h10 : (2 : ℝ) ^ (10 * M) ≤ 2 ^ (18 * M) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hfin := trqSlow_final_lt hM
  intro h
  linarith

/-- **Theorem 14.3.9 with a trust-region INNER fails in the printed order, `q ≥ 2`**
([cartis2022evaluation], Theorem 14.3.9 with the exponents `π_j = j + 1` of (14.2.12)).
For the fixed problem `f = 0`, `c(v) = (1, v_1^{-1/8}, v_2)`, `X = {v_1 ≥ 1}`,
`x₀ = (2, 0)` (which satisfies c.D1qLB.X, f.D1qLB.X and f.B.Fb, `trqSlowC_assumption`,
`trqSlowF_assumption`, `trqSlowF_assumptionBFb`), the fixed TRq parameters `trqSlowParams`,
`ϑ = 1`, `β₁ = trqSlowβ₁`, and every `θ ∈ (0, 1)` and `β`, there is no constant `κ` such that
every run of `IsTPqpGCTRqSCRun` that terminates in Phase 1 uses at most
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
        IsTPqpGCTRqSCRun (fun _ => 0) trqSlowC trqSlowX q trqSlowParams 1 θ trqSlowβ₁ β ε
          (slowPt 2 0) xP δP k₁ D nF₁ nD₁ →
        θ * ε 0 < ‖trqSlowC (xP k₁)‖ →
        ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤
          κ * (1 + trqSCLogTerm q ε) * tpqpOrderF (fun j => (j : ℝ) + 1) q ε := by
  rintro ⟨κ, hκ⟩
  obtain ⟨M, hM⟩ := exists_nat_gt (20 * |κ| + 20)
  have hM1 : 1 ≤ M := by
    have : (1 : ℝ) < M := by linarith [abs_nonneg κ]
    exact_mod_cast this.le
  obtain ⟨xP, δP, k₁, D, nF₁, nD₁, hrun, hexit, hcount⟩ := trqSlow_exists_tpqp_run (β := β) hq hM1
    hθ0 hθ1 (ε := trqSlowTol M) (fun j _ => trqSlowTol_mem M j) (by simp [trqSlowTol])
    (by simp [trqSlowTol])
  have h := hκ (trqSlowTol M) (fun j _ => trqSlowTol_mem M j) xP δP k₁ D nF₁ nD₁ hrun hexit
  exact trqSlow_not_le_printed hq hM hcount h

/-- **The printed form of `theorem_14_3_9_trq` is false for every `q ≥ 2`.** The fixed problem of
`theorem_14_3_9_trq_printed_false` satisfies every hypothesis of `theorem_14_3_9_trq` (c.D1qLB.X,
f.D1qLB.X, f.B.Fb with `β_F = 1`, `ϑ = 1`, `θ ∈ (0, 1)`, `0 < β ≤ ϑ`, `β₁ ‖c(x₀)‖ ≤ ϑ`), but its
conclusion with the printed exponents `π_j = j + 1` in place of `q + 1` fails. -/
theorem theorem_14_3_9_trq_printed_false_conclusion {q : ℕ} (hq : 2 ≤ q) {θ β : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    AssumptionCD1pLBX trqSlowC trqSlowX trqSlowX₀ q (fun j => trqSlowCB (j + 1)) trqSlowCB ∧
    AssumptionD1pLBX (fun _ : ℝ² => (0 : ℝ)) trqSlowX trqSlowX₀ q (fun _ => 0) (fun _ => 0) ∧
    Chapter07.AssumptionBFb (fun _ : ℝ² => (0 : ℝ)) trqSlowC trqSlowX 1 0 0 ∧
    (0 < β ∧ β ≤ 1) ∧ trqSlowβ₁ * ‖trqSlowC (slowPt 2 0)‖ ≤ 1 ∧
    ¬ ∃ κF κL κD : ℝ, 0 ≤ κF ∧ 0 ≤ κL ∧ 0 ≤ κD ∧
      ∀ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) → ε 0 ≤ 1 →
      ∀ (xP : ℕ → ℝ²) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq 2) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCTRqSCRun (fun _ => 0) trqSlowC trqSlowX q trqSlowParams 1 θ trqSlowβ₁ β ε
          (slowPt 2 0) xP δP k₁ D nF₁ nD₁ →
        (θ * ε 0 < ‖trqSlowC (xP k₁)‖ →
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤
            (κF + κL * trqSCLogTerm q ε) * tpqpOrderF (fun j => (j : ℝ) + 1) q ε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤ κD * tpqpOrderD (fun j => (j : ℝ) + 1) q ε) ∧
        (‖trqSlowC (xP k₁)‖ ≤ θ * ε 0 → ∃ kε, D.IsEnd (fun _ => 0) trqSlowC trqSlowX q θ ε kε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) + D.funEvals kε ≤
            (κF + κL * trqSCLogTerm q ε) * tpqpOrderF (fun j => (j : ℝ) + 1) q ε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) + D.derivEvals kε ≤
            κD * tpqpOrderD (fun j => (j : ℝ) + 1) q ε) := by
  refine ⟨trqSlowC_assumption q, trqSlowF_assumption q, trqSlowF_assumptionBFb trqSlowC 1,
    ⟨hβ0, hβ1⟩, by rw [trqSlowβ₁_mul]; norm_num, ?_⟩
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
`β₁ ∈ (0, 1)`, the TRq parameters `trqSlowParams` and `ϑ = 1`, there is no `κ` such that every run
of `IsTPqpGCTRqSCRun` that enters Phase 2 reaches a termination index `k_ε` of Phase 2 with at most
`κ (1 + |log(ε₀ ε_min)|) max[ε₀^{-1}, max_j ε₀^{-j} ε_j^{-(j+1)}]` derivative evaluations in
Phase 2. The runs of `trqSlow_exists_tpqp_run_phase2` have a single INNER call on `μ(·, t_1)`,
the TRq-SC run of `trqSlow_exists_long_run` started at `(256, 0)`. -/
theorem theorem_14_3_9_trq_printed_false_phase2 {q : ℕ} (hq : 2 ≤ q) {β₁ : ℝ} (hβ₁0 : 0 < β₁)
    (hβ₁1 : β₁ < 1) :
    ¬ ∃ κ : ℝ, ∀ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) →
      ∀ (xP : ℕ → ℝ²) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq 2) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCTRqSCRun (fun _ => 0) trqSlowC2 trqSlowX q trqSlowParams 1 (1 / 2) β₁ (1 / 2) ε
          (slowPt 256 0) xP δP k₁ D nF₁ nD₁ →
        ‖trqSlowC2 (xP k₁)‖ ≤ 1 / 2 * ε 0 →
        ∃ kε, D.IsEnd (fun _ => 0) trqSlowC2 trqSlowX q (1 / 2) ε kε ∧
          (D.derivEvals kε : ℝ) ≤
            κ * (1 + trqSCLogTerm q ε) * tpqpOrderF (fun j => (j : ℝ) + 1) q ε := by
  rintro ⟨κ, hκ⟩
  obtain ⟨M, hM⟩ := exists_nat_gt (20 * |κ| + 20)
  have hM2 : 2 ≤ M := by
    have : (2 : ℝ) < M := by linarith [abs_nonneg κ]
    exact_mod_cast this.le
  obtain ⟨xP, δP, k₁, D, nF₁, nD₁, hrun, hph2, hcount⟩ := trqSlow_exists_tpqp_run_phase2 hq hM2
    hβ₁0 hβ₁1 (ε := trqSlowTol M) (fun j _ => trqSlowTol_mem M j) (by simp [trqSlowTol])
    (by simp [trqSlowTol]) (by simp [trqSlowTol])
  obtain ⟨kε, hend, h⟩ := hκ (trqSlowTol M) (fun j _ => trqSlowTol_mem M j) xP δP k₁ D nF₁ nD₁
    hrun hph2
  exact trqSlow_not_le_printed hq hM (hcount kε hend) h

/-- **The printed form of `theorem_14_3_9_trq` is false in Phase 2 for every `q ≥ 2`.** The fixed
problem of `theorem_14_3_9_trq_printed_false_phase2` satisfies every hypothesis of
`theorem_14_3_9_trq` (c.D1qLB.X, f.D1qLB.X, f.B.Fb with `β_F = 1`, `ϑ = 1`, `θ = β = 1/2`,
`β₁ ‖c₂(x₀)‖ = β₁/2 ≤ ϑ`), but its conclusion with the printed exponents `π_j = j + 1` fails,
through its Phase-2 part. -/
theorem theorem_14_3_9_trq_printed_false_conclusion_phase2 {q : ℕ} (hq : 2 ≤ q) {β₁ : ℝ}
    (hβ₁0 : 0 < β₁) (hβ₁1 : β₁ < 1) :
    AssumptionCD1pLBX trqSlowC2 trqSlowX trqSlowX₀ q (fun j => trqSlowCB (j + 1)) trqSlowCB ∧
    AssumptionD1pLBX (fun _ : ℝ² => (0 : ℝ)) trqSlowX trqSlowX₀ q (fun _ => 0) (fun _ => 0) ∧
    Chapter07.AssumptionBFb (fun _ : ℝ² => (0 : ℝ)) trqSlowC2 trqSlowX 1 0 0 ∧
    β₁ * ‖trqSlowC2 (slowPt 256 0)‖ ≤ 1 ∧
    ¬ ∃ κF κL κD : ℝ, 0 ≤ κF ∧ 0 ≤ κL ∧ 0 ≤ κD ∧
      ∀ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) → ε 0 ≤ 1 →
      ∀ (xP : ℕ → ℝ²) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq 2) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCTRqSCRun (fun _ => 0) trqSlowC2 trqSlowX q trqSlowParams 1 (1 / 2) β₁ (1 / 2) ε
          (slowPt 256 0) xP δP k₁ D nF₁ nD₁ →
        (1 / 2 * ε 0 < ‖trqSlowC2 (xP k₁)‖ →
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤
            (κF + κL * trqSCLogTerm q ε) * tpqpOrderF (fun j => (j : ℝ) + 1) q ε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤ κD * tpqpOrderD (fun j => (j : ℝ) + 1) q ε) ∧
        (‖trqSlowC2 (xP k₁)‖ ≤ 1 / 2 * ε 0 →
          ∃ kε, D.IsEnd (fun _ => 0) trqSlowC2 trqSlowX q (1 / 2) ε kε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) + D.funEvals kε ≤
            (κF + κL * trqSCLogTerm q ε) * tpqpOrderF (fun j => (j : ℝ) + 1) q ε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) + D.derivEvals kε ≤
            κD * tpqpOrderD (fun j => (j : ℝ) + 1) q ε) := by
  refine ⟨trqSlowC2_assumption q, trqSlowF_assumption q, trqSlowF_assumptionBFb trqSlowC2 1,
    by rw [norm_trqSlowC2_x₀]; linarith, ?_⟩
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
