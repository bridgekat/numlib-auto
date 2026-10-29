import Numlib.Analysis.Calculus.AnchoredLipschitzDerivs
import Numlib.Optimization.Complexity.Existence
import Numlib.Optimization.Complexity.SlowExample.HighOrder
import Numlib.Optimization.ModelBased.HighOrder.ARqpComplexity
import Numlib.Optimization.ModelBased.HighOrder.TRqComplexity
import Numlib.Optimization.ModelBased.HighOrder.ARqpDetailedStep
import Numlib.Optimization.ModelBased.HighOrder.Orders
import NumlibSurface.CartisGouldToint.Chapter02.Section01
import NumlibSurface.CartisGouldToint.Chapter12.Section01

/-!
# Cartis–Gould–Toint §12.2: Finding approximate minimizers of arbitrary order

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §12.2: the trust-region method TRq
(§12.2.1) and the adaptive-regularization method ARqp (§12.2.2) for `(ε, δ)`-approximate
`q`-th order minimizers (12.1.25), their evaluation complexity and its sharpness.

The algorithms are the backbone run predicates with exact Taylor data:
* `algorithm_12_2_1` is `Optimization.IsTRqRun` with `D k = ftaylorSeries ℝ f (x k)` and no
  constraints (built on the generic trust-region run `Optimization.IsTRRun`);
* `algorithm_12_2_2` is `Optimization.IsARqpRun` with the model data
  `Optimization.ARqpData.ofTaylor (ftaylorSeries ℝ f (x k)) p (σ k)` and no constraints (built on
  the generic adaptive-regularization run `Optimization.IsARRun`);
* `algorithm_12_2_3` is the instance `J = {j | 3 ≤ j}` of the backbone transition system
  `Optimization.DetailedStepTrans` (Algorithm 12.2.3, the detailed Step 2).

The definitions are stated on any real inner product space `E`; the complexity theorems on
`ℝⁿ = EuclideanSpace ℝ (Fin n)`, and the sharpness examples, like the book's, on `ℝ`.
Evaluation counts: `Optimization.funEvalCount k = k + 1` (one evaluation of `f` per iteration and
the initial one) and `Optimization.derivEvalCount succ k` (the initial evaluation of the
derivatives and one per successful iteration before `k`).

The analyses are those of the library, stated once on a feasible set `X` under the anchored
smoothness assumption `LipschitzDerivsAnchored` (derivatives Lipschitz anchored at the points of a
set containing the sublevel set `{y ∈ X | f(y) ≤ f(x₀)}`):
`Numlib.Optimization.ModelBased.HighOrder.TRqComplexity` (TRq: Lemmas 12.2.3–12.2.4, Theorem
12.2.5), `Numlib.Optimization.ModelBased.HighOrder.ARqpComplexity` (ARqp: Lemmas 12.2.9–12.2.13,
Theorem 12.2.14, in either radii mode) and
`Numlib.Optimization.ModelBased.HighOrder.ARqpDetailedStep` (Algorithm 12.2.3 terminates and
returns admissible steps). The book's statements below are their
instances with `X = C = A = univ`.

## Main definitions

* `AssumptionD1pL f p L` — f.D1qL, f.D1pL, f.D1rL (bridged to `LipschitzDerivsAnchored` by
  `assumptionD1pL_iff`, `AssumptionD1pL.toLipschitzDerivsAnchored`; the forms on an open convex
  set or anchored at a set used with feasible sets in §14.2 are `LipschitzDerivsAnchored` itself);
* `algorithm_12_2_1` (TRq), with its test `trqStop`; `algorithm_12_2_1_feasible` (TRq-SC);
* `algorithm_12_2_2` (ARqp), with its test `arqpStop`; `algorithm_12_2_2_feasible` (ARqp-SC);
  `algorithm_12_2_3`;
* the book's constants `arqpKappaDm` (`κ_{Δm}`), `arqpPi` (`π_j`), `kappaSARqp`, `kappaAARqp`
  (the radii mode `u = (q ≤ 2)` of the library's `arqpKappaDmOf u`, `arqpPiOf u`, …); the
  extrema `finMax`, `finMin` and the constants `trqKappaDelta`, `kappaSTRq`, …, `arqpKappaDelta`,
  `arqpTau`, `arqpKappaHat`, … are the library's (re-exported);
* `IsARqpGlobalStepRun` — the scenario of Theorem 12.2.15.

## Main results

* TRq: `lemma_12_2_1` – `lemma_12_2_4`, `theorem_12_2_5` (complexity), `theorem_12_2_6`
  (sharpness);
* ARqp: `example_12_2_1`, `example_12_2_2`, `lemma_12_2_7` – `lemma_12_2_13`,
  `theorem_12_2_14_i`, `theorem_12_2_14_ii` (complexity), `theorem_12_2_15`,
  `theorem_12_2_15_counterexample`, `corollary_12_2_16`, `theorem_12_2_17` (sharpness);
* `lemma_12_2_9_algorithm` (Algorithm 12.2.3 terminates and returns admissible steps),
  `algorithm_12_2_2_exists_of_D1pL` (runs with the radii property (12.2.50)),
  `lemma_12_2_10_le_two`, `isEpsDeltaApproxMinimizer_of_isMinOn_zero`.

## Implementation notes

The `export Optimization (…)` command near the top of this file re-exports names that moved to the
library (`finMax`, `finMin` and their lemmas; `trqKappaDelta`, `kappaSTRq`, `kappaATRq`,
`kappaBTRq`, `kappaCTRq`; `arqpData`, `arqpModel`, `arqpStop`, `arqpRho`; `arqpKappaDelta`,
`arqpTau`, `arqpKappaHat`, `arqpPiOf`, `arqpKappaDmOf`, `kappaSARqpOf`, `kappaAARqpOf`,
`kappaCARqp` and their lemmas; `isEpsDeltaApprox_of_isMinOn_zero_of_jet`). These are compatibility
re-exports for the `Chapter12.…` references of Chapter 14, to be removed once those use the library
names.

## Deviations from the book

* **ARqp, Step 1.** The printed test continues when `ΔT_{f,j}(x_k, d_{k,j}) ≥ ς ε_j δ^j/j!`;
  with `≥` the sharpness examples of the book never stop. The test is normalized to `>` (as in
  TRq's (12.2.2)), see `Optimization.IsARqpRun`, which also lists the other normalizations
  (Step-2 termination only at a global model minimizer `0`, as guaranteed by Algorithm 12.2.3;
  the long-step branch `‖s_k‖ ≥ 1`).
* **Theorem 12.2.5.** The conclusion `φ^{δ_ε}_{f,q}` is a typo for `φ^{δ_ε}_{f,j}`.
* **Theorem 12.2.6 (Appendix B).** The printed data decrease `f` by `½ ε^{q+1} c_k` while the
  Taylor decrease is `ε^{q+1} c_k` (so (B.12.8) fails), `x_k = (k-1)ε` is `kε`, and
  `ε^{q+1} k_ε ≤ 1` is false; the corrected data are `Optimization.exists_slowTRq_interpolant`.
* **Lemma 12.2.10.** The printed proof applies (12.2.29) to the step `s_k = 0`, which need not be
  the returned step (Example 12.2.2 allows `s_k = ½`); the statement is proved from the global
  minimality of `0`, with explicit radii.
* **Lemma 12.2.11.** A failed Step-1 test only gives `φ > ς ε_j δ^j/j!`: the printed factor
  `1 - θ` is `ς - θ`, which requires `θ < ς` (the two agree for `ς = 1`). The lemma also needs
  (12.2.29) (not the long-step branch) at iteration `k`.
* **Lemma 12.2.12 (`q > 2`).** "The first case implies the second" needs
  `κ_{δ,min} ≤ τ_q/2`, which fails for `θ` close to `ς`; the constant `κ_{δ,min}` is replaced by
  `κ̂ = min(κ_{δ,min}, τ_q/2)` (`arqpKappaHat`), also in Lemma 12.2.13 and Theorem 12.2.14 (2).
* **Lemma 12.2.13.** It needs f.D1pL (printed: f.D1qL), and holds at successful iterations
  followed by a non-terminating one (printed: every iteration before termination).
* **Theorem 12.2.14.** The hypotheses `θ < ς` (Lemma 12.2.11) and `σ_min > 0` (the book's Step 0;
  `Optimization.ARqpParams` only asks `σ_min ≥ 0`) are explicit. In (1) the radii equal to `1` are
  required of `δ₀` and of every returned step (the book's "the algorithm ensures `δ_{k+1,j} = 1`");
  in (2) the radii property (12.2.50) is a hypothesis on the run, which runs constructed by
  `algorithm_12_2_2_exists_of_D1pL` satisfy.
* **Theorem 12.2.15 for `q ≥ 3`.** Its hypothesis "the choice `δ_{s_k,j} = 1` is possible" fails
  for its own example, e.g. for `p = q = 3` (`theorem_12_2_15_counterexample`); the theorem is
  stated for the
  global-step scenario `IsARqpGlobalStepRun`, which is a genuine ARqp run for `q ≤ 2`
  (`corollary_12_2_16`).
* **Example 12.2.2.** `s²(s - ½)² = ¼ s²(1 - 4s) + s⁴` (printed: `½ s²(1 - 2s) + s⁴`, which has
  the unique minimizer `0`); the measure is `φ^1_{m,3}(0) = ¾` and the radius threshold is `¼`.
* **Theorem 12.2.17.** "`ε` sufficiently small" is `ε ≤ ½`.

## Not formalized

The `O(·)` restatements and Table 12.2.1. (The existence of an admissible step is proved twice:
directly from a global model minimizer in `lemma_12_2_9`, and through the termination of
Algorithm 12.2.3 in `lemma_12_2_9_algorithm`.)
-/

open Set Metric Filter Optimization Topology
open scoped Nat

namespace CartisGouldToint.Chapter12

section Assumption

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Assumptions f.D1qL / f.D1pL / f.D1rL** of [cartis2022evaluation] (§12.2.1.2, §12.2.2.1,
§12.2.2.4; the same condition for the orders `q`, `p`, `r`): `f` is `p` times continuously
differentiable and, for every `j ∈ [1:p]`, its `j`-th derivative is Lipschitz continuous with
constant `L_{f,j} = L j ≥ 1`. -/
structure AssumptionD1pL (f : E → ℝ) (p : ℕ) (L : ℕ → ℝ) : Prop where
  /-- `f` is `C^p`. -/
  contDiff : ContDiff ℝ p f
  /-- The constants are at least `1`. -/
  one_le : ∀ j ∈ Finset.Icc 1 p, 1 ≤ L j
  /-- The `j`-th derivative is `L_{f,j}`-Lipschitz. -/
  lipschitz : ∀ j ∈ Finset.Icc 1 p, IteratedFDerivLipschitzOn f j (L j) univ

variable {f : E → ℝ} {p : ℕ} {L : ℕ → ℝ}

namespace AssumptionD1pL

/-- The assumption of order `p` implies the assumption of every lower order. -/
theorem mono (h : AssumptionD1pL f p L) {q : ℕ} (hq : q ≤ p) : AssumptionD1pL f q L :=
  ⟨h.contDiff.of_le (by exact_mod_cast hq), fun j hj => h.one_le j (Finset.Icc_subset_Icc_right
    hq hj), fun j hj => h.lipschitz j (Finset.Icc_subset_Icc_right hq hj)⟩

/-- Every derivative of order `j ∈ [1:p]` is `L_f`-Lipschitz. -/
theorem lipschitz_finMax (h : AssumptionD1pL f p L) {j : ℕ} (hj : j ∈ Finset.Icc 1 p) :
    IteratedFDerivLipschitzOn f j (finMax 1 L p) univ :=
  IteratedFDerivHolderOn.mono_const (h.lipschitz j hj) (le_finMax hj)

/-- **(12.2.24)** of [cartis2022evaluation] (with Theorem A.8.5): `‖∇^j f(x)‖ ≤ L_{f,j-1}` for
`j ∈ [2:p]`. -/
theorem norm_iteratedFDeriv_le (h : AssumptionD1pL f p L) {j : ℕ} (hj : j ∈ Finset.Icc 2 p)
    (x : E) : ‖iteratedFDeriv ℝ j f x‖ ≤ L (j - 1) := by
  obtain ⟨hj2, hjp⟩ := Finset.mem_Icc.1 hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hi : i ∈ Finset.Icc 1 p := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  rw [Nat.add_sub_cancel]
  exact norm_iteratedFDeriv_succ_le_of_lipschitzOn isOpen_univ
    (zero_le_one.trans (h.one_le i hi)) (h.lipschitz i hi) (mem_univ x)

/-- `‖∇^j f(x)‖ ≤ L_f` for `j ∈ [2:p]`. -/
theorem norm_iteratedFDeriv_le_finMax (h : AssumptionD1pL f p L) {j : ℕ}
    (hj : j ∈ Finset.Icc 2 p) (x : E) : ‖iteratedFDeriv ℝ j f x‖ ≤ finMax 1 L p := by
  refine (h.norm_iteratedFDeriv_le hj x).trans (le_finMax ?_)
  obtain ⟨hj2, hjp⟩ := Finset.mem_Icc.1 hj
  exact Finset.mem_Icc.2 ⟨by omega, by omega⟩

/-- f.D1pL gives the anchored assumption on the whole space, for every anchor set. -/
theorem toLipschitzDerivsAnchored (h : AssumptionD1pL f p L) (A : Set E) :
    LipschitzDerivsAnchored f univ A 1 p L :=
  .of_contDiff h.contDiff h.lipschitz A

/-- f.D1pL at the top order `p` only, the form of the hypotheses of the ARqp analysis. -/
theorem toLipschitzDerivsAnchored_top (h : AssumptionD1pL f p L) (hp : 1 ≤ p) (A : Set E) :
    LipschitzDerivsAnchored f univ A p p L :=
  (h.toLipschitzDerivsAnchored A).mono hp le_rfl

/-- The top-order constant is at least `1`. -/
theorem one_le_top (h : AssumptionD1pL f p L) (hp : 1 ≤ p) : 1 ≤ L p :=
  h.one_le p (Finset.mem_Icc.2 ⟨hp, le_rfl⟩)

end AssumptionD1pL

/-- f.D1pL is the backbone assumption `LipschitzDerivsAnchored` on `C = A = univ` with constants
at least `1`. -/
theorem assumptionD1pL_iff : AssumptionD1pL f p L ↔
    LipschitzDerivsAnchored f univ univ 1 p L ∧ ∀ j ∈ Finset.Icc 1 p, 1 ≤ L j :=
  ⟨fun h => ⟨h.toLipschitzDerivsAnchored univ, h.one_le⟩, fun ⟨h, h1⟩ =>
    ⟨contDiff_iff_contDiffAt.2 fun y => h.contDiffAt y (mem_univ y), h1,
      fun _ hj => h.lipschitzOn hj⟩⟩

end Assumption

/-! ### The TRq algorithm (§12.2.1) -/

section TRq

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Algorithm 12.2.1 (TRq)** of [cartis2022evaluation]: a run of the trust-region method for
`(ε, δ)`-approximate `q`-th order minimizers with constants `P` (`Δ₀`, `Δ_max`, `η₁`, `η₂`, `γ₁`,
`γ₂`, `γ₃`, `ς`), tolerances `ε` and threshold `ϑ`: iterates `x`, steps `s`, radii `Δ`, orders
`j_k = jk k` and Step-1 displacements `d k j`, with optimality radius `δ_k = min(Δ_k, ϑ)`. It is
`Optimization.IsTRqRun` with the exact Taylor data `ftaylorSeries ℝ f (x k)`. (The book's Step 0
asks `ε ∈ (0, 1]^q` and `ϑ ∈ [ε_min, 1]`; these are hypotheses of the results below.) -/
def algorithm_12_2_1 (f : E → ℝ) (P : TRqParams) (q : ℕ) (ε : ℕ → ℝ) (ϑ : ℝ) (x s : ℕ → E)
    (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → E) : Prop :=
  IsTRqRun f (fun k => ftaylorSeries ℝ f (x k)) (fun _ => univ) P q ε ϑ x s Δ jk d

/-- The termination test of TRq (Step 1) at iteration `k`:
`ΔT_{f,j}(x_k, d_{k,j}) ≤ ς ε_j δ_k^j/j!` for all `j ∈ [1:q]`, `δ_k = min(Δ_k, ϑ)`. -/
abbrev trqStop (f : E → ℝ) (P : TRqParams) (q : ℕ) (ε : ℕ → ℝ) (ϑ : ℝ) (x : ℕ → E)
    (Δ : ℕ → ℝ) (d : ℕ → ℕ → E) (k : ℕ) : Prop :=
  trqTest (fun k => ftaylorSeries ℝ f (x k)) P q ε ϑ Δ d k

/-- The ratio (12.2.4) of TRq. -/
noncomputable abbrev trqRho (f : E → ℝ) (x s : ℕ → E) (jk : ℕ → ℕ) (k : ℕ) : ℝ :=
  trqRatio f (fun k => ftaylorSeries ℝ f (x k)) x s jk k

/-- The scaled approximate criticality gap `φ̂_{f,k}` of (12.2.8). -/
noncomputable abbrev trqGapSeq (f : E → ℝ) (ϑ : ℝ) (x : ℕ → E) (Δ : ℕ → ℝ) (jk : ℕ → ℕ)
    (d : ℕ → ℕ → E) (k : ℕ) : ℝ :=
  trqGap (ftaylorSeries ℝ f (x k)) (jk k) (min (Δ k) ϑ) (d k (jk k))

/-- **Algorithm 12.2.1 is well defined**: in finite dimension, for every `f`, `ϑ ≥ 0` and starting
point `x₀`, a TRq run from `x₀` exists. -/
theorem algorithm_12_2_1_exists [FiniteDimensional ℝ E] (f : E → ℝ) (P : TRqParams) (q : ℕ)
    (ε : ℕ → ℝ) {ϑ : ℝ} (hϑ : 0 ≤ ϑ) (x₀ : E) :
    ∃ (x s : ℕ → E) (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → E), x 0 = x₀ ∧
      algorithm_12_2_1 f P q ε ϑ x s Δ jk d :=
  exists_isTRqRun f (fun y => ftaylorSeries ℝ f y) (fun _ => univ) (fun _ => isClosed_univ)
    (fun _ => mem_univ 0) P q ε hϑ x₀

variable {f : E → ℝ} {P : TRqParams} {q : ℕ} {ε : ℕ → ℝ} {ϑ : ℝ} {x s : ℕ → E}
  {Δ : ℕ → ℝ} {jk : ℕ → ℕ} {d : ℕ → ℕ → E} {L : ℕ → ℝ}

/-- **TRq with a feasible set** (TRq-SC, [cartis2022evaluation] §14.2): the run of
Algorithm 12.2.1 whose Step-1 displacements and steps are feasible, `x_k + d ∈ X`
(`Optimization.IsTRqRun` with `S k = {d | x k + d ∈ X}`). With `X = univ` this is
`algorithm_12_2_1` (`algorithm_12_2_1_iff_feasible`). -/
def algorithm_12_2_1_feasible (f : E → ℝ) (X : Set E) (P : TRqParams) (q : ℕ) (ε : ℕ → ℝ)
    (ϑ : ℝ) (x s : ℕ → E) (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → E) : Prop :=
  IsTRqRun f (fun k => ftaylorSeries ℝ f (x k)) (fun k => {e | x k + e ∈ X}) P q ε ϑ x s Δ jk d

theorem algorithm_12_2_1_iff_feasible :
    algorithm_12_2_1 f P q ε ϑ x s Δ jk d ↔
      algorithm_12_2_1_feasible f univ P q ε ϑ x s Δ jk d := by
  have : (fun k => {e | x k + e ∈ (univ : Set E)}) = fun _ => univ := by
    funext k; ext; simp
  rw [algorithm_12_2_1_feasible, this]; rfl

/-- **Lemma 12.2.1** of [cartis2022evaluation]: at every iteration `k` before termination of a TRq
run with `ϑ > 0`, with `ε_min = finMin 1 ε q` (the minimum of the tolerances, (12.2.7)),
`min_{i ∈ [0:k]} φ̂_i ≥ ς ε_min` (12.2.9) and
`ΔT_{f,j_k}(x_k, s_k) ≥ φ̂_k δ_k^{j_k}/j_k!` (12.2.10). -/
theorem lemma_12_2_1 (h : algorithm_12_2_1 f P q ε ϑ x s Δ jk d) (hϑ : 0 < ϑ) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ trqStop f P q ε ϑ x Δ d i) :
    P.ς * finMin 1 ε q ≤ prefixMin (trqGapSeq f ϑ x Δ jk d) k ∧
      trqGapSeq f ϑ x Δ jk d k * min (Δ k) ϑ ^ jk k / (jk k)! ≤
        (ftaylorSeries ℝ f (x k)).taylorDecrement (jk k) (s k) :=
  IsTRqRun.trqGap_ge h hϑ (fun _ hj => finMin_le hj) hk

/-- Model fidelity of TRq under f.D1qL (from (A.19), Corollary A.8.4): before termination,
`|f(x_k + s_k) - T_{f,j_k}(x_k, s_k)| ≤ L_f ‖s_k‖^{j_k+1}/(j_k+1)!`. -/
theorem trq_fidelity (h : algorithm_12_2_1 f P q ε ϑ x s Δ jk d) (hf : AssumptionD1pL f q L) :
    ∀ k, (∀ i ≤ k, ¬ trqStop f P q ε ϑ x Δ d i) →
      |f (x k + s k) - (f (x k) - (ftaylorSeries ℝ f (x k)).taylorDecrement (jk k) (s k))| ≤
        finMax 1 L q / (jk k + 1)! * ‖s k‖ ^ (jk k + 1) :=
  IsTRqRun.abs_sub_le_of_lipschitz h hf.contDiff fun _ hj => hf.lipschitz_finMax hj

/-- **Lemma 12.2.2** of [cartis2022evaluation]: under f.D1qL, if at an iteration `k` before
termination `Δ_k ≤ min(ϑ, (1 - η₂) φ̂_k / L_f)` (12.2.11), then `ρ_k ≥ η₂` (the iteration is very
successful) and `Δ_{k+1} ≥ Δ_k`. -/
theorem lemma_12_2_2 (h : algorithm_12_2_1 f P q ε ϑ x s Δ jk d) (hf : AssumptionD1pL f q L)
    {k : ℕ} (hk : ∀ i ≤ k, ¬ trqStop f P q ε ϑ x Δ d i)
    (hΔ : Δ k ≤ min ϑ ((1 - P.η₂) * trqGapSeq f ϑ x Δ jk d k / finMax 1 L q)) :
    P.η₂ ≤ trqRho f x s jk k ∧ Δ k ≤ Δ (k + 1) := by
  obtain ⟨-, h1, h2⟩ := IsTRqRun.le_reductionRatio h
    (zero_lt_one.trans_le one_le_finMax) hk (trq_fidelity h hf k hk) hΔ
  exact ⟨h1, h2⟩

/-- **Lemma 12.2.4** of [cartis2022evaluation]: under f.D1qL, `ε_j ∈ (0, 1]` and
`ϑ ∈ [ε_min, 1]`, at every iteration `k` before termination
`ΔT_{f,j_k}(x_k, s_k) ≥ (ς κ_Δ)^{q+1} ε_min^{q+1}/q!` (12.2.18), and if `k` is successful,
`f(x_k) - f(x_{k+1}) ≥ η₁ (ς κ_Δ)^{q+1} ε_min^{q+1}/q!` (12.2.19). -/
theorem lemma_12_2_4 (h : algorithm_12_2_1 f P q ε ϑ x s Δ jk d) (hf : AssumptionD1pL f q L)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hϑ : finMin 1 ε q ≤ ϑ) (hϑ1 : ϑ ≤ 1) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ trqStop f P q ε ϑ x Δ d i) :
    (P.ς * trqKappaDelta f P q L ϑ (x 0)) ^ (q + 1) / q ! * finMin 1 ε q ^ (q + 1) ≤
        (ftaylorSeries ℝ f (x k)).taylorDecrement (jk k) (s k) ∧
      (P.η₁ ≤ trqRho f x s jk k →
        P.η₁ * ((P.ς * trqKappaDelta f P q L ϑ (x 0)) ^ (q + 1) / q ! *
          finMin 1 ε q ^ (q + 1)) ≤ f (x k) - f (x (k + 1))) :=
  IsTRqRun.taylorDecrement_ge_of_anchored (X := univ) (algorithm_12_2_1_iff_feasible.1 h)
    (hf.toLipschitzDerivsAnchored univ) subset_rfl (fun _ hy _ => hy) (mem_univ _) hε hϑ hϑ1 hk

/-- **Lemma 12.2.3** of [cartis2022evaluation]: under f.D1qL and `0 < ϑ ≤ 1`, `ε_j ≥ 0`, at every
iteration `k` before termination, `Δ_k ≥ min(γ₁ ϑ, κ_Δ min_{i ∈ [0:k]} φ̂_i)` (12.2.13), and
`κ_Δ ∈ (0, 1)` ((12.2.14)). (The bound also holds for `Δ_{k+1}`.) -/
theorem lemma_12_2_3 (h : algorithm_12_2_1 f P q ε ϑ x s Δ jk d) (hf : AssumptionD1pL f q L)
    (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hε : ∀ j ∈ Finset.Icc 1 q, 0 ≤ ε j) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ trqStop f P q ε ϑ x Δ d i) :
    (0 < trqKappaDelta f P q L ϑ (x 0) ∧ trqKappaDelta f P q L ϑ (x 0) < 1) ∧
      min (P.γ₁ * ϑ) (trqKappaDelta f P q L ϑ (x 0) * prefixMin (trqGapSeq f ϑ x Δ jk d) k) ≤
        Δ k ∧
      min (P.γ₁ * ϑ) (trqKappaDelta f P q L ϑ (x 0) * prefixMin (trqGapSeq f ϑ x Δ jk d) k) ≤
        Δ (k + 1) :=
  IsTRqRun.radius_ge_of_anchored (X := univ) (algorithm_12_2_1_iff_feasible.1 h)
    (hf.toLipschitzDerivsAnchored univ) subset_rfl (fun _ hy _ => hy) (mem_univ _) hϑ hϑ1 hε hk

end TRq

section TRqComplexity

variable {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {flow : ℝ} {P : TRqParams} {q : ℕ}
  {ε : ℕ → ℝ} {ϑ : ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)} {Δ : ℕ → ℝ} {jk : ℕ → ℕ}
  {d : ℕ → ℕ → EuclideanSpace ℝ (Fin n)} {L : ℕ → ℝ}

/-- **Theorem 12.2.5** of [cartis2022evaluation] (complexity of TRq). Assume f.Bb and f.D1qL,
`ε ∈ (0, 1]^q` and `ϑ ∈ [ε_min, 1]`. Every TRq run terminates at some iteration `k_ε`, where
`x_ε = x_{k_ε}` is an `(ε, δ_ε)`-approximate `q`-th order minimizer with the radius
`δ_ε = min(Δ_{k_ε}, ϑ) ∈ (0, 1]` (`φ^{δ_ε}_{f,j}(x_ε) ≤ ε_j δ_ε^j/j!` for all `j ∈ [1:q]`; the
printed `φ_{f,q}` is a typo), after at most
`κ^A (f(x₀) - f_low)/ε_min^{q+1} + κ^B |log ε_min| + κ^C` evaluations of `f` (12.2.21) and at most
`κ^S (f(x₀) - f_low)/ε_min^{q+1} + 1` evaluations of the derivatives (12.2.22), with the book's
constants (`kappaSTRq`, `kappaATRq`, `kappaBTRq`, `kappaCTRq`; `κ_Δ` of (12.2.14) depends on
`x₀`; if all derivatives vanish at `x₀` the run stops at once). -/
theorem theorem_12_2_5 (hb : Chapter02.AssumptionBb f flow) (hf : AssumptionD1pL f q L)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hϑ : finMin 1 ε q ≤ ϑ) (hϑ1 : ϑ ≤ 1)
    (h : algorithm_12_2_1 f P q ε ϑ x s Δ jk d) :
    ∃ kε, IsFirstHit (trqStop f P q ε ϑ x Δ d) kε ∧
      min (Δ kε) ϑ ∈ Ioc 0 1 ∧
      IsEpsDeltaApproxMinimizer f q ε (fun _ => min (Δ kε) ϑ) (x kε) ∧
      (funEvalCount kε : ℝ) ≤
        kappaATRq f P q L ϑ (x 0) * (f (x 0) - flow) / finMin 1 ε q ^ (q + 1) +
          kappaBTRq P * |Real.log (finMin 1 ε q)| + kappaCTRq f P q L ϑ (x 0) ∧
      (derivEvalCount (fun k => P.η₁ ≤ trqRho f x s jk k) kε : ℝ) ≤
        kappaSTRq f P q L ϑ (x 0) * (f (x 0) - flow) / finMin 1 ε q ^ (q + 1) + 1 := by
  obtain ⟨kε, hk, -, hδ, hcert, hF, hD⟩ := IsTRqRun.complexity (X := univ)
    (fun y _ => hb y) (hf.toLipschitzDerivsAnchored univ) subset_rfl (fun _ hy _ => hy)
    (mem_univ _) hε hϑ hϑ1 (algorithm_12_2_1_iff_feasible.1 h)
  have hU : {e : EuclideanSpace ℝ (Fin n) | x kε + e ∈ (univ : Set _)} = univ := by ext; simp
  rw [hU] at hcert
  exact ⟨kε, hk, hδ, ⟨fun j hj => ⟨hε j hj, hδ⟩, hcert⟩, hF, hD⟩

end TRqComplexity

/-! ### Functions of one variable -/

section OneDim

/-- **f.D1rL for functions of one variable**: a `C^r` function with `L`-Lipschitz `r`-th
derivative and derivatives of orders `0, …, r` bounded by `B` satisfies f.D1rL with the
constants `max(1, L, B)`. -/
theorem assumptionD1pL_real {G : ℝ → ℝ} {r : ℕ} {L B : ℝ} (hG : ContDiff ℝ r G)
    (hL : ∀ s t, |iteratedDeriv r G s - iteratedDeriv r G t| ≤ L * |s - t|)
    (hB : ∀ j ≤ r, ∀ t, |iteratedDeriv j G t| ≤ B) :
    AssumptionD1pL G r (fun _ => max 1 (max L B)) := by
  refine ⟨hG, fun _ _ => le_max_left _ _, fun j hj => ?_⟩
  obtain ⟨hj1, hjr⟩ := Finset.mem_Icc.1 hj
  rcases hjr.lt_or_eq with hjr | rfl
  · have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 (Nat.zero_le r) 0)
    refine IteratedFDerivHolderOn.mono_const (iteratedFDerivLipschitzOn_of_norm_le convex_univ
      (fun y _ => (hG.of_le (by exact_mod_cast hjr)).contDiffAt) (L := B) fun y _ => ?_) ?_
    · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
      exact hB (j + 1) hjr y
    · exact (le_max_right _ _).trans (le_max_right _ _)
  · rw [iteratedFDerivLipschitzOn_iff]
    intro s _ t _
    rw [norm_iteratedFDeriv_sub_real, Real.norm_eq_abs]
    refine (hL s t).trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
    exact (le_max_left _ _).trans (le_max_right _ _)

end OneDim

/-! ### Sharpness for TRq (Theorem 12.2.6) -/

section TRqSharp

/-- **Theorem 12.2.6** of [cartis2022evaluation] (slow convergence of TRq; proof in Appendix B,
corrected). For `q ≥ 1` there are `f_low` and `L ≥ 1` depending only on `q` such that, for every
`ε ∈ (0, 1/q!]` (tolerances `ε_j = j! ε ∈ (0, 1]`) and all TRq constants with `Δ₀ = ε`, there is
`f : ℝ → ℝ` satisfying f.Bb (`f ≥ f_low`) and f.D1qL (with all `L_{f,j} = L`) and a TRq run with
`ϑ = 1` from `x₀ = 0` with `x_k = k ε`, `s_k = Δ_k = δ_k = ε` and `ρ_k = 1` before termination,
whose first termination index is `k_ε = ⌈ε^{-(q+1)}⌉`, where `x_{k_ε}` is an `(ε_j, ε)`-approximate
`q`-th order minimizer: TRq may need `ε^{-(q+1)}` iterations and at least `ε^{-(q+1)} + 1`
evaluations of `f` and of its derivatives. (As in the book, the initial radius `Δ₀ = ε` depends on
`ε`, so the example shows that the order `ε^{-(q+1)}` of Theorem 12.2.5 is attained.) -/
theorem theorem_12_2_6 {q : ℕ} (hq : 1 ≤ q) :
    ∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / q ! → ∀ P : TRqParams, P.Δ₀ = ε →
      ∃ f : ℝ → ℝ, (∀ t, flow ≤ f t) ∧ AssumptionD1pL f q (fun _ => L) ∧
        ∃ (x s : ℕ → ℝ) (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → ℝ),
          algorithm_12_2_1 f P q (fun j => j ! * ε) 1 x s Δ jk d ∧
          (∀ k, x k = k * ε ∧ s k = ε ∧ Δ k = ε ∧ min (Δ k) 1 = ε) ∧
          (∀ k < ⌈(ε ^ (q + 1))⁻¹⌉₊, trqRho f x s jk k = 1) ∧
          IsFirstHit (trqStop f P q (fun j => j ! * ε) 1 x Δ d) ⌈(ε ^ (q + 1))⁻¹⌉₊ ∧
          IsEpsDeltaApprox (ftaylorSeries ℝ f (x ⌈(ε ^ (q + 1))⁻¹⌉₊)) univ q
            (fun j => j ! * ε) (fun _ => ε) ∧
          (ε ^ (q + 1))⁻¹ + 1 ≤ (funEvalCount ⌈(ε ^ (q + 1))⁻¹⌉₊ : ℝ) ∧
          (ε ^ (q + 1))⁻¹ + 1 ≤
            (derivEvalCount (fun k => P.η₁ ≤ trqRho f x s jk k) ⌈(ε ^ (q + 1))⁻¹⌉₊ : ℝ) := by
  obtain ⟨L, B, hL, hB, hG⟩ := exists_slowTRq_interpolant hq
  refine ⟨-B, max 1 (max L B), le_max_left _ _, fun ε hε hεq P hP => ?_⟩
  have hqf : (0 : ℝ) < q ! := by exact_mod_cast q.factorial_pos
  have hε1 : ε ≤ 1 := hεq.trans (by
    rw [div_le_one hqf]; exact_mod_cast Nat.one_le_iff_ne_zero.2 q.factorial_ne_zero)
  set x : ℕ → ℝ := fun k => k * ε with hx
  obtain ⟨G, hGc, hGL, hGB, hGd, hGf⟩ := hG ε x hε hε1 fun k _ => by simp only [hx]; push_cast; ring
  set kε : ℕ := ⌈(ε ^ (q + 1))⁻¹⌉₊ with hkε
  have hkε1 : 1 ≤ kε := Nat.one_le_iff_ne_zero.2 (by
    rw [hkε]; exact (Nat.ceil_pos.2 (by positivity)).ne')
  have hkεge : (ε ^ (q + 1))⁻¹ ≤ kε := by rw [hkε]; exact Nat.le_ceil _
  clear_value kε
  have hkεpos : (0 : ℝ) < kε := by exact_mod_cast hkε1
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ, ∀ k, c k = 2 - k / kε := ⟨_, fun _ => rfl⟩
  have hGq : ∀ k ≤ kε, iteratedDeriv q G (x k) = -ε * c k * q ! := fun k hk => by
    rw [hc]; exact (hGd k hk).2
  have hGf' : ∀ k < kε, G (x (k + 1)) = G (x k) - ε ^ (q + 1) * c k := fun k hk => by
    rw [hc]; exact hGf k hk
  have hc1 : ∀ k < kε, 1 < c k := fun k hk => by
    rw [hc]
    have : (k : ℝ) / kε < 1 := (div_lt_one hkεpos).2 (by exact_mod_cast hk)
    linarith
  have hckε : c kε = 1 := by rw [hc, div_self hkεpos.ne']; ring
  have hc0 : ∀ k ≤ kε, 0 ≤ c k := fun k hk => by
    rw [hc]
    have : (k : ℝ) / kε ≤ 1 := (div_le_one hkεpos).2 (by exact_mod_cast hk)
    linarith
  -- Taylor decrements along the iterates
  have hdec_lt : ∀ k ≤ kε, ∀ j ∈ Finset.Icc 1 q, j < q → ∀ e : ℝ,
      (ftaylorSeries ℝ G (x k)).taylorDecrement j e = 0 := fun k hk j hj hjq e =>
    taylorDecrement_real_eq_zero (fun i hi => (hGd k hk).1 i (Finset.mem_Icc.1 hi).1
      (lt_of_le_of_lt (Finset.mem_Icc.1 hi).2 hjq)) e
  have hdec_q : ∀ k ≤ kε, ∀ e : ℝ,
      (ftaylorSeries ℝ G (x k)).taylorDecrement q e = ε * c k * e ^ q := fun k hk e => by
    rw [taylorDecrement_real_spike (m := q) (Finset.mem_Icc.2 ⟨hq, le_rfl⟩)
      (fun i hi hiq => (hGd k hk).1 i (Finset.mem_Icc.1 hi).1
        (lt_of_le_of_ne (Finset.mem_Icc.1 hi).2 hiq)), hGq k hk]
    field_simp
  have hδ : min ε 1 = ε := min_eq_left hε1
  -- the measures
  have hφ_lt : ∀ k ≤ kε, ∀ j ∈ Finset.Icc 1 q, j < q →
      taylorMeasure (ftaylorSeries ℝ G (x k)) j ε univ = 0 := fun k hk j hj hjq => by
    have := taylorMeasure_real_monomial (a := 0) (m := 0) le_rfl hε.le
      (D := ftaylorSeries ℝ G (x k))
      (j := j) fun e => by rw [hdec_lt k hk j hj hjq, zero_mul]
    rwa [zero_mul] at this
  have hφ_q : ∀ k ≤ kε, taylorMeasure (ftaylorSeries ℝ G (x k)) q ε univ = ε * c k * ε ^ q :=
    fun k hk => taylorMeasure_real_monomial (mul_nonneg hε.le (hc0 k hk)) hε.le (hdec_q k hk)
  -- the witnesses: a fraction `ς` of the measure, exactly
  have hw : ∀ k j, ∃ e : ℝ, IsApproxMeasureStep ((ftaylorSeries ℝ G (x k)).taylorDecrement j)
      (min ε 1) univ P.ς e ∧ (ftaylorSeries ℝ G (x k)).taylorDecrement j e =
        P.ς * taylorMeasure (ftaylorSeries ℝ G (x k)) j (min ε 1) univ := fun k j =>
    exists_isApproxMeasureStep_eq isClosed_univ (mem_univ 0) (starConvex_univ 0)
      (le_min hε.le zero_le_one)
      ((ftaylorSeries ℝ G (x k)).continuous_taylorDecrement j).continuousOn
      ((ftaylorSeries ℝ G (x k)).taylorDecrement_zero_right j) ⟨P.ς_pos.le, P.ς_le_one⟩
  choose d hd hdeq using hw
  set εv : ℕ → ℝ := fun j => j ! * ε with hεv
  -- the test
  have htest : ∀ k ≤ kε, (trqStop G P q εv 1 x (fun _ => ε) d k ↔ k = kε) := by
    intro k hk
    rw [trqStop, trqTest_iff, measureTestPasses_iff]
    simp only [hδ]
    constructor
    · intro ht
      by_contra hne
      have hlt : k < kε := lt_of_le_of_ne hk hne
      have := ht q (Finset.mem_Icc.2 ⟨hq, le_rfl⟩)
      rw [hdeq, hδ, hφ_q k hk] at this
      have h1 := hc1 k hlt
      have : P.ς * (ε * c k * ε ^ q) ≤ P.ς * (q ! * ε) * ε ^ q / q ! := this
      have hς := P.ς_pos
      have e : P.ς * (q ! * ε) * ε ^ q / q ! = P.ς * (ε * 1 * ε ^ q) := by field_simp
      rw [e] at this
      have := le_of_mul_le_mul_left this hς
      have := le_of_mul_le_mul_left (by linarith : ε * ε ^ q * c k ≤ ε * ε ^ q * 1)
        (by positivity : (0 : ℝ) < ε * ε ^ q)
      linarith
    · intro hkk j hj
      rw [hdeq, hδ]
      rcases (Finset.mem_Icc.1 hj).2.lt_or_eq with hjq | rfl
      · rw [hφ_lt k hk j hj hjq, mul_zero]
        have := P.ς_pos
        positivity
      · rw [hφ_q k hk, hkk, hckε]
        apply le_of_eq
        simp only [hεv]
        field_simp
  have hfirst : IsFirstHit (trqStop G P q εv 1 x (fun _ => ε) d) kε :=
    ⟨(htest kε le_rfl).2 rfl, fun i hi => fun h => hi.ne ((htest i hi.le).1 h)⟩
  have hbefore : ∀ k, (∀ i ≤ k, ¬ trqStop G P q εv 1 x (fun _ => ε) d i) → k < kε := by
    intro k hk
    by_contra hge
    exact hk kε (not_lt.1 hge) hfirst.1
  -- the ratio
  have hρ : ∀ k < kε, trqRho G x (fun _ => ε) (fun _ => q) k = 1 := by
    intro k hk
    rw [trqRho, trqRatio_eq, reductionRatio_def, hdec_q k hk.le]
    have hxk : x k + ε = x (k + 1) := by simp only [hx]; push_cast; ring
    rw [hxk, hGf' k hk]
    have := hc1 k hk
    have : 0 < ε * c k * ε ^ q := by positivity
    field_simp
    ring
  have hcert : IsEpsDeltaApprox (ftaylorSeries ℝ G (x kε)) univ q (fun j => j ! * ε)
      (fun _ => ε) := by
    have h1 : MeasureTestPasses (fun j => (ftaylorSeries ℝ G (x kε)).taylorDecrement j) q P.ς
        εv (fun _ => min ε 1) (d kε) := hfirst.1
    have h := MeasureTestPasses.isEpsDeltaApprox (S := univ) P.ς_pos (fun j _ => hd kε j) h1
    rwa [show (fun _ : ℕ => min ε 1) = fun _ => ε from funext fun _ => hδ] at h
  have hderiv : (kε : ℝ) + 1 ≤ (derivEvalCount
      (fun k => P.η₁ ≤ trqRho G x (fun _ => ε) (fun _ => q) k) kε : ℝ) := by
    obtain ⟨m, rfl⟩ : ∃ m, kε = m + 1 := ⟨kε - 1, by omega⟩
    rw [derivEvalCount_add_one]
    have hfail : (failureSet (fun k => P.η₁ ≤ trqRho G x (fun _ => ε) (fun _ => q) k) m).card =
        0 := Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem fun j hj => by
      rw [mem_failureSet] at hj
      exact hj.2 (by rw [hρ j (by omega)]; exact P.η₁_le_η₂.trans P.η₂_lt_one.le))
    have := card_successSet_add_card_failureSet
      (succ := fun k => P.η₁ ≤ trqRho G x (fun _ => ε) (fun _ => q) k) (k := m)
    rw [hfail, add_zero] at this
    rw [this]
    push_cast
    linarith
  refine ⟨G, neg_le_of_abs_iteratedDeriv_zero_le fun t => hGB 0 (Nat.zero_le q) t,
    assumptionD1pL_real hGc hGL hGB, x, fun _ => ε, fun _ => ε, fun _ => q, d, ?_,
    fun k => ⟨rfl, rfl, rfl, hδ⟩, hρ, hfirst, hcert,
    by rw [funEvalCount_eq]; push_cast; linarith, by linarith⟩
  refine ⟨⟨hP.symm, fun k hk => ?_, fun k hk => ?_⟩, fun k _ j _ => hd k j,
    fun k _ => hP ▸ P.Δ₀_le_Δmax⟩
  · -- Step 2
    have hkε' := hbefore k hk
    refine ⟨Finset.mem_Icc.2 ⟨hq, le_rfl⟩, ?_, fun i hi hiq => ?_, ⟨?_, mem_univ _⟩, ?_⟩
    · simp only [hδ]
      rw [hdeq, hδ, hφ_q k hkε'.le]
      have h1 := hc1 k hkε'
      have hς := P.ς_pos
      have e : P.ς * (q ! * ε) * ε ^ q / q ! = P.ς * (ε * 1 * ε ^ q) := by field_simp
      rw [e]
      gcongr
    · simp only [hδ]
      rw [hdeq, hδ, hφ_lt k hkε'.le i hi hiq, mul_zero]
      have := P.ς_pos
      positivity
    · simp [Real.norm_eq_abs, abs_of_pos hε]
    · rw [hdeq, hδ, hφ_q k hkε'.le, hdec_q k hkε'.le]
      have := hc0 k hkε'.le
      calc P.ς * (ε * c k * ε ^ q) ≤ 1 * (ε * c k * ε ^ q) :=
            mul_le_mul_of_nonneg_right P.ς_le_one (by positivity)
        _ = ε * c k * ε ^ q := one_mul _
  · -- Steps 3–4
    have hkε' := hbefore k hk
    have hρk := hρ k hkε'
    refine ⟨?_, ⟨fun _ => ⟨le_rfl, ?_⟩, fun _ h => ?_, fun h => ?_⟩⟩
    · change x (k + 1) = if P.η₁ ≤ trqRho G x (fun _ => ε) (fun _ => q) k then x k + ε else x k
      rw [hρk, ite_eq_left (P.η₁_le_η₂.trans P.η₂_lt_one.le)]
      simp only [hx]; push_cast; ring
    · exact le_mul_of_one_le_left hε.le P.one_le_γ₃
    · change trqRho G x (fun _ => ε) (fun _ => q) k < P.η₂ at h
      rw [hρk] at h; linarith [P.η₂_lt_one]
    · change trqRho G x (fun _ => ε) (fun _ => q) k < P.η₁ at h
      rw [hρk] at h; linarith [P.η₁_le_η₂, P.η₂_lt_one]

end TRqSharp

/-! ### The ARqp algorithm (§12.2.2.1) -/

section ARqp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **ARqp with a feasible set** (ARqp-SC, [cartis2022evaluation] §14.2): the run of
Algorithm 12.2.2 whose iterates, steps and displacements are feasible for the closed set `X`
(`Optimization.IsARqpRun f X` with the exact model data). `algorithm_12_2_2` is the case
`X = univ`. -/
def algorithm_12_2_2_feasible (f : E → ℝ) (X : Set E) (P : ARqpParams) (p q : ℕ)
    (ε δ₀ : ℕ → ℝ) (x s : ℕ → E) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → E) : Prop :=
  IsARqpRun f X P q ε δ₀ (arqpData f p x σ) x s σ δ δs d dm

/-- **Algorithm 12.2.2 (ARqp)** of [cartis2022evaluation]: a run of the adaptive-regularization
method for `(ε, δ)`-approximate `q`-th order minimizers with models of degree `p`, constants `P`
(`σ₀`, `σ_min`, `η₁`, `η₂`, `γ₁`, `γ₂`, `γ₃`, `θ`, `ς`), tolerances `ε` and initial radii `δ₀`:
iterates `x`, steps `s`, weights `σ`, Step-1 radii `δ k j` and displacements `d k j`, Step-2 radii
`δs k j` and displacements `dm k j`. It is `Optimization.IsARqpRun` with the exact model data
`arqpData`, without constraints. (The book's Step 0 asks `q ≤ p`, `ε ∈ (0, 1)^q`,
`δ₀ ∈ (0, 1]^q`; these are hypotheses of the results below.) -/
def algorithm_12_2_2 (f : E → ℝ) (P : ARqpParams) (p q : ℕ) (ε δ₀ : ℕ → ℝ) (x s : ℕ → E)
    (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → E) : Prop :=
  algorithm_12_2_2_feasible f univ P p q ε δ₀ x s σ δ δs d dm

/-- **Algorithm 12.2.2 is well defined** ([cartis2022evaluation], Lemmas 12.2.9 and 12.2.10): in
finite dimension, for every `f`, `1 ≤ p`, `q ≤ p`, `ε_j > 0` and `δ₀ ∈ (0, 1]^q`, an ARqp run
from any `x₀` exists, with Step-2 radii `δs_{k,j} = 1` for `j ≤ 2` at every iteration reached. -/
theorem algorithm_12_2_2_exists [FiniteDimensional ℝ E] (f : E → ℝ) (P : ARqpParams) {p q : ℕ}
    (hp : 1 ≤ p) (hq : q ≤ p) {ε δ₀ : ℕ → ℝ} (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j)
    (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1) (x₀ : E) :
    ∃ (x s : ℕ → E) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → E), x 0 = x₀ ∧
      algorithm_12_2_2 f P p q ε δ₀ x s σ δ δs d dm ∧
      ∀ k, (∀ i < k, ¬ arqpStop f P p q ε x s σ δ d i) →
        ∀ j ∈ Finset.Icc 1 q, j ≤ 2 → δs k j = 1 := by
  obtain ⟨x, s, σ, δ, δs, d, dm, h0, h, hrad⟩ := exists_isARqpRun f P hp hq hε hδ₀
    (fun y => ∑ i ∈ Finset.Icc 2 p, ‖iteratedFDeriv ℝ i f y‖) (fun _ => by positivity)
    (fun y i hi => Finset.single_le_sum (f := fun i => ‖iteratedFDeriv ℝ i f y‖)
      (fun _ _ => norm_nonneg _) hi) x₀
  exact ⟨x, s, σ, δ, δs, d, dm, h0, h, fun k hk => (hrad k hk).1⟩

/-- **Example 12.2.1** of [cartis2022evaluation] (with Example 12.1.3). If `f(x_k) = 0`,
`∇f(x_k) = -β e` (`‖e‖ = 1`) and `∇^j f(x_k) = 0` for `j ∈ [2:p]`, the ARqp model (12.2.23) is the
model `m(s) = -β ⟨e, s⟩ + σ ‖s‖^{p+1}/(p+1)!` of Example 12.1.3 (whose unique global minimizer
is `s* = (β p!/σ)^{1/p} e`, `example_12_1_3`). For `p = 5`, `σ = 5!`, `β = 1` (so `s* = e`) and
`θ ε₃ ≤ 1`, every radius `δ ∈ (15/19, 1]` gives `φ^δ_{m,3}(s*) > θ ε₃ δ³/3!` (along `d = -δ s*`,
`ΔT_{m,3}(s*, d) = -5δ²/2 + 10δ³/3`), whereas (12.2.29) at order `3` with radius `δ` implies
`φ^δ_{m,3}(s*) ≤ θ ε₃ δ³/3!`: such radii are not admissible, in particular `δ_{s_k,3} = 1`. -/
theorem example_12_2_1 {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {x e : EuclideanSpace ℝ (Fin n)}
    {β σ : ℝ} {p : ℕ} (hp : 1 ≤ p) (hx : f x = 0)
    (h1 : ∀ s, iteratedFDeriv ℝ 1 f x (fun _ => s) = -β * inner ℝ e s)
    (hj : ∀ j ∈ Finset.Icc 2 p, iteratedFDeriv ℝ j f x = 0) :
    regularizedModel (ftaylorSeries ℝ f x) p σ = example1213Model β σ p e ∧
      (‖e‖ = 1 → ∀ θ ε₃ : ℝ, θ * ε₃ ≤ 1 → ∀ δ ∈ Ioc (15 / 19 : ℝ) 1,
        θ * ε₃ * δ ^ 3 / 3 ! < phiMeasure (example1213Model 1 (5 !) 5 e) 3 δ e) := by
  refine ⟨funext fun s => ?_, fun he θ ε₃ hθε δ hδ => ?_⟩
  · rw [regularizedModel_def, example1213Model, FormalMultilinearSeries.taylorSum_eq_add]
    have hsum : ∑ i ∈ Finset.Icc 1 p, ((i ! : ℝ))⁻¹ • ftaylorSeries ℝ f x i (fun _ => s) =
        -β * inner ℝ e s := by
      rw [Finset.sum_eq_single_of_mem 1 (Finset.mem_Icc.2 ⟨le_rfl, hp⟩)]
      · simp only [Nat.factorial_one, Nat.cast_one, inv_one, one_smul]
        exact h1 s
      · intro i hi hi1
        have : ftaylorSeries ℝ f x i = 0 := hj i (Finset.mem_Icc.2
          ⟨by have := (Finset.mem_Icc.1 hi).1; omega, (Finset.mem_Icc.1 hi).2⟩)
        rw [this]; simp
    have h0 : ftaylorSeries ℝ f x 0 0 = f x := by simp [ftaylorSeries]
    rw [hsum, h0, hx, zero_add]
    ring
  · obtain ⟨hδ0, hδ1⟩ := hδ
    have hδpos : (0 : ℝ) < δ := by linarith
    have hβ : ((5 ! : ℕ) : ℝ) / (5 ! : ℕ) = 1 := div_self (by positivity)
    have hd := example1213_taylorDecrement_unit (σ := (5 ! : ℕ)) (p := 5) he ((-δ) • e)
    rw [hβ] at hd
    have hin : inner ℝ e ((-δ) • e) = -δ := by
      rw [inner_smul_right, real_inner_self_eq_norm_sq, he]; ring
    have hnorm : ‖(-δ) • e‖ ^ 2 = δ ^ 2 := by
      rw [norm_smul, he, Real.norm_eq_abs, abs_neg, abs_of_pos hδpos]; ring
    rw [hin, hnorm] at hd
    have hle := taylorDecrement_le_taylorMeasure
      (ftaylorSeries ℝ (example1213Model 1 (5 !) 5 e) e) 3 (S := univ) (d := (-δ) • e) (δ := δ)
      ⟨mem_closedBall_zero_iff.2 (by
        rw [norm_smul, he, Real.norm_eq_abs, abs_neg, abs_of_pos hδpos, mul_one]), mem_univ _⟩
    rw [hd] at hle
    refine lt_of_lt_of_le ?_ hle
    norm_num [Nat.factorial]
    nlinarith [mul_pos hδpos hδpos,
      mul_le_mul_of_nonneg_right hθε (by positivity : (0 : ℝ) ≤ δ ^ 3)]

/-- The model `m(s) = s²(s - ½)²` of Example 12.2.2. -/
noncomputable def example1222Model (s : ℝ) : ℝ := s ^ 2 * (s - 1 / 2) ^ 2

theorem example1222Model_eq (s : ℝ) : example1222Model s = s ^ 4 - s ^ 3 + s ^ 2 / 4 := by
  rw [example1222Model]; ring

/-- The third-order Taylor decrement of `example1222Model` at `0`: `ΔT_{m,3}(0, d) = d³ - d²/4`. -/
theorem example1222Model_taylorDecrement (d : ℝ) :
    (ftaylorSeries ℝ example1222Model 0).taylorDecrement 3 d = d ^ 3 - d ^ 2 / 4 := by
  have hc : ContDiffAt ℝ 4 example1222Model 0 := by
    unfold example1222Model; fun_prop
  set a : ℕ → ℝ := fun i => if i = 2 then d ^ 2 / 4 else if i = 3 then -d ^ 3 else
    if i = 4 then d ^ 4 else 0 with ha
  have hpoly : ∀ t : ℝ, example1222Model (0 + t • d) =
      example1222Model 0 + ∑ i ∈ Finset.Icc 1 4, t ^ i * a i := by
    intro t
    rw [show Finset.Icc 1 4 = {1, 2, 3, 4} by decide]
    simp [ha, example1222Model_eq, smul_eq_mul]
    ring
  rw [ftaylorSeries_taylorDecrement_eq, taylorPolynomial_eq_of_poly hc
    (Eventually.of_forall hpoly) (by norm_num : 3 ≤ 4)]
  rw [show Finset.Icc 1 3 = {1, 2, 3} by decide]
  simp [ha]
  ring

/-- **Example 12.2.2** of [cartis2022evaluation] (corrected). The function
`m(s) = s²(s - ½)² = ¼ s²(1 - 4s) + s⁴` on `ℝ` is the ARqp model (12.2.23) with `p = 3`,
`σ = 4!` for the data `f(x_k) = 0`, `f'(x_k) = 0`, `f''(x_k) = ½`, `f'''(x_k) = -6`. Its global
minimizers are exactly `0` and `½`. At `0`, `φ^1_{m,3}(0) = ¾ > 0` (so a Step-1 test with radius
`1` at `x_k` does not stop, although the global model minimizer `s_k = 0` makes the algorithm stop
in Step 2), while `φ^δ_{m,3}(0) = 0` exactly when `δ ≤ ¼`. (The printed expansion
`½ s²(1 - 2s) + s⁴`, the value `-½` and the threshold `½` do not match `s²(s - ½)²`.) -/
theorem example_12_2_2 :
    (∀ (f : ℝ → ℝ) (x : ℝ), f x = 0 → iteratedDeriv 1 f x = 0 → iteratedDeriv 2 f x = 1 / 2 →
      iteratedDeriv 3 f x = -6 →
        regularizedModel (ftaylorSeries ℝ f x) 3 (4 !) = example1222Model) ∧
    (∀ s, IsMinOn example1222Model univ s ↔ s = 0 ∨ s = 1 / 2) ∧
    phiMeasure example1222Model 3 1 0 = 3 / 4 ∧
    (∀ δ : ℝ, δ ≤ 1 / 4 → phiMeasure example1222Model 3 δ 0 = 0) ∧
    (∀ δ : ℝ, 1 / 4 < δ → 0 < phiMeasure example1222Model 3 δ 0) := by
  have hnonneg : ∀ t, 0 ≤ example1222Model t := fun t => by unfold example1222Model; positivity
  refine ⟨fun f x h0 h1 h2 h3 => funext fun s => ?_, fun s => ⟨fun hs => ?_, fun hs => ?_⟩, ?_,
    fun δ hδ => ?_, fun δ hδ => ?_⟩
  · rw [regularizedModel_def, FormalMultilinearSeries.taylorSum_eq_add,
      show Finset.Icc 1 3 = {1, 2, 3} by decide]
    have h00 : ftaylorSeries ℝ f x 0 0 = f x := by simp [ftaylorSeries]
    rw [h00, h0, Real.norm_eq_abs, (by decide : Even 4).pow_abs, example1222Model_eq]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
      smul_eq_mul, smul_eq_mul, smul_eq_mul, ftaylorSeries_real_apply, ftaylorSeries_real_apply,
      ftaylorSeries_real_apply, h1, h2, h3]
    norm_num [Nat.factorial]
    ring
  · have h1 : example1222Model s ≤ example1222Model 0 := hs (mem_univ 0)
    have h2 : example1222Model s = 0 :=
      le_antisymm (h1.trans_eq (by simp [example1222Model])) (hnonneg s)
    rw [example1222Model, mul_eq_zero] at h2
    rcases h2 with h | h
    · exact Or.inl (pow_eq_zero_iff (by norm_num) |>.1 h)
    · right; have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h; linarith
  · refine fun t _ => le_trans (le_of_eq ?_) (hnonneg t)
    rcases hs with rfl | rfl <;> simp [example1222Model]
  · refine le_antisymm (decrementMeasure_le ⟨0, by simp, mem_univ _⟩ fun d hd => ?_) ?_
    · have hd1 : |d| ≤ 1 := by simpa [Real.norm_eq_abs] using hd.1
      rw [example1222Model_taylorDecrement]
      obtain ⟨h1, h2⟩ := abs_le.1 hd1
      nlinarith [sq_nonneg (d + 3 / 8)]
    · have := taylorDecrement_le_taylorMeasure (ftaylorSeries ℝ example1222Model 0) 3
        (S := univ) (d := 1) (δ := 1) ⟨by simp, mem_univ _⟩
      rw [example1222Model_taylorDecrement] at this
      linarith
  · rcases lt_or_ge δ 0 with hneg | hδ0
    · rw [phiMeasure_def, taylorMeasure_eq_sSup, closedBall_eq_empty.2 hneg, empty_inter,
        image_empty, Real.sSup_empty]
    refine le_antisymm (decrementMeasure_le ⟨0, mem_closedBall_self hδ0, mem_univ _⟩
      fun d hd => ?_) (phiMeasure_nonneg _ _ hδ0 _)
    have hdδ : |d| ≤ δ := by simpa [Real.norm_eq_abs] using hd.1
    rw [example1222Model_taylorDecrement]
    have : d ≤ 1 / 4 := (le_abs_self d).trans (hdδ.trans hδ)
    nlinarith [sq_nonneg d]
  · have := taylorDecrement_le_taylorMeasure (ftaylorSeries ℝ example1222Model 0) 3
      (S := univ) (d := δ) (δ := δ)
      ⟨mem_closedBall_zero_iff.2 (by rw [Real.norm_eq_abs, abs_of_pos (by linarith)]),
        mem_univ _⟩
    rw [example1222Model_taylorDecrement] at this
    refine lt_of_lt_of_le ?_ this
    nlinarith [mul_pos (by linarith : (0 : ℝ) < δ) (by linarith : (0 : ℝ) < δ)]

/-- **Algorithm 12.2.3** of [cartis2022evaluation] (a detailed Step 2 for ARqp): `(s, δs)` is a
pair returned by the inner procedure for the model `m` (any `m : E → ℝ`; ARqp uses `m_k`), the
order `q`, the constants `ς`, `θ` and the tolerances `ε`: Step 2.2 computes `s_μ` with
`μ (m(0) - m*) ≤ m(0) - m(s_μ)` (12.2.34), Step 2.3 returns long steps `‖s_μ‖ ≥ 1`, Step 2.4
checks the orders `j = 1, …, q` with approximate optimality displacements (12.2.35), halving the
radius `δ_{s,j}` (only for `j ≥ 3`) when (12.2.36) fails but (12.2.37) holds, and otherwise
increasing `μ` to `(1 + μ)/2`. It is the instance `J = {j | 3 ≤ j}`, no constraints, of the
backbone transition system `Optimization.DetailedStepTrans` (shared with Algorithm 14.1.2). -/
def algorithm_12_2_3 (m : E → ℝ) (q : ℕ) (ς θ : ℝ) (ε : ℕ → ℝ) (s : E) (δs : ℕ → ℝ) : Prop :=
  IsDetailedStepOutput m univ (fun _ => univ)
    (fun j s d => (ftaylorSeries ℝ m s).taylorDecrement j d) q ς θ ε {j | 3 ≤ j} s δs

variable {f : E → ℝ} {p q : ℕ} {L : ℕ → ℝ}

/-- **Lemma 12.2.7** of [cartis2022evaluation]: under f.D1pL, for `σ ≥ 0` the model
`m = regularizedModel (ftaylorSeries ℝ f x) p σ` is `C^p`, its `p`-th derivative is
`σ`-Lipschitz, and `‖∇^ℓ m(s)‖ ≤ 3 L_f + σ` for `‖s‖ ≤ 1` and `ℓ ∈ [2:p]` (12.2.38). -/
theorem lemma_12_2_7 (hf : AssumptionD1pL f p L) {σ : ℝ} (hσ : 0 ≤ σ) (x : E) :
    ContDiff ℝ p (regularizedModel (ftaylorSeries ℝ f x) p σ) ∧
      IteratedFDerivLipschitzOn (regularizedModel (ftaylorSeries ℝ f x) p σ) p σ univ ∧
      ∀ s : E, ‖s‖ ≤ 1 → ∀ ℓ ∈ Finset.Icc 2 p,
        ‖iteratedFDeriv ℝ ℓ (regularizedModel (ftaylorSeries ℝ f x) p σ) s‖ ≤
          3 * finMax 1 L p + σ :=
  ⟨contDiff_regularizedModel, iteratedFDerivLipschitzOn_regularizedModel hσ,
    fun _ hs _ hℓ => norm_iteratedFDeriv_regularizedModel_le
      (zero_le_one.trans one_le_finMax)
      (fun _ hi => hf.norm_iteratedFDeriv_le_finMax hi x) hσ hℓ hs⟩

/-- **Lemma 12.2.8** of [cartis2022evaluation]: under f.D1pL, let `σ ≥ 0`, `‖s‖ ≤ 1`, `α ∈ ℝ`,
`δ ∈ (0, min(1, α/(4(3 L_f + σ)))]` (12.2.41), `‖d‖ ≤ δ` and `j ∈ [1:p]`. If
`ΔT_{m,j}(s, d) ≥ α δ^j/j!` (12.2.42), then `m(s) - m(s + d) ≥ ½ α δ^j/j!` (12.2.43). -/
theorem lemma_12_2_8 (hf : AssumptionD1pL f p L) {σ : ℝ} (hσ : 0 ≤ σ) (x : E) {s d : E}
    (hs : ‖s‖ ≤ 1) {α δ : ℝ}
    (hδ : δ ∈ Ioc 0 (min 1 (α / (4 * (3 * finMax 1 L p + σ))))) (hd : ‖d‖ ≤ δ) {j : ℕ}
    (hj : j ∈ Finset.Icc 1 p)
    (hdec : α * δ ^ j / j ! ≤
      (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ f x) p σ) s).taylorDecrement j d) :
    1 / 2 * α * δ ^ j / j ! ≤ regularizedModel (ftaylorSeries ℝ f x) p σ s -
      regularizedModel (ftaylorSeries ℝ f x) p σ (s + d) := by
  have hL1 := one_le_finMax (L := L) (p := p)
  have hL := zero_le_one.trans hL1
  have hK : 0 < 3 * finMax 1 L p + σ := by linarith
  have hδα : 4 * (3 * finMax 1 L p + σ) * δ ≤ α := by
    have := hδ.2.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have := sub_regularizedModel_ge_of_taylorDecrement_ge hL
    (fun i hi => hf.norm_iteratedFDeriv_le_finMax hi x) hσ hj hs hδ.1.le
    (hδ.2.trans (min_le_left _ _)) hδα hd hdec
  calc 1 / 2 * α * δ ^ j / j ! = α / 2 * δ ^ j / j ! := by ring
    _ ≤ _ := this

/-- **Lemma 12.2.9** of [cartis2022evaluation] (existence of a step). Under f.D1pL in finite
dimension, with `1 ≤ p`, `q ≤ p`, `ε ∈ (0, 1]^q` and `σ > 0`, at any iterate `x` there are a step
`s`, radii `δs` and displacements `d^m` satisfying the Step-2 conditions of ARqp ((12.2.27), and
either `‖s‖ ≥ 1` or (12.2.29)), with `δs_j = 1` for `j ∈ [1:min(q, 2)]` (12.2.44) and
`δs_j ≥ κ_δ(σ) ε_j` for `j ∈ [3:q]` (12.2.45). (The step is a global minimizer of the model,
which the book notes is always acceptable; the termination of Algorithm 12.2.3 is not used.) -/
theorem lemma_12_2_9 [FiniteDimensional ℝ E] (hf : AssumptionD1pL f p L) (P : ARqpParams)
    (hp : 1 ≤ p) (hq : q ≤ p) {ε : ℕ → ℝ} (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) {σ : ℝ}
    (hσ : 0 < σ) (x : E) :
    ∃ (s : E) (δs : ℕ → ℝ) (dm : ℕ → E),
      ARqpStep univ P q ε (ARqpData.ofTaylor (ftaylorSeries ℝ f x) p σ) x s δs dm ∧
      (∀ j ∈ Finset.Icc 1 q, j ≤ 2 → δs j = 1) ∧
      ∀ j ∈ Finset.Icc 3 q, arqpKappaDelta P (finMax 1 L p) σ * ε j ≤ δs j := by
  have hL : 1 ≤ finMax 1 L p := one_le_finMax
  obtain ⟨s, δs, dm, hstep, h12, h3⟩ := exists_arqpStep_ofTaylor P hp hq
    (fun j hj => (hε j hj).1) (zero_le_one.trans hL)
    (fun i hi => hf.norm_iteratedFDeriv_le_finMax hi x) hσ x (D := ftaylorSeries ℝ f x)
  refine ⟨s, δs, dm, hstep, h12, fun j hj => ?_⟩
  have hj' : j ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨by have := (Finset.mem_Icc.1 hj).1; omega,
    (Finset.mem_Icc.1 hj).2⟩
  obtain ⟨hε0, hε1⟩ := hε j hj'
  rw [h3 j hj]
  have hK : 0 < 3 * finMax 1 L p + σ := by positivity
  have := P.ς_pos; have := P.θ_pos; have := P.ς_le_one; have := P.θ_lt_one
  refine le_min ?_ ?_
  · calc arqpKappaDelta P (finMax 1 L p) σ * ε j ≤ 1 * 1 :=
          mul_le_mul (arqpKappaDelta_lt_one P hL hσ.le).le hε1 hε0.le zero_le_one
      _ = 1 := one_mul 1
  · rw [arqpKappaDelta]
    calc P.ς * P.θ / (8 * (3 * finMax 1 L p + σ)) * ε j =
        P.ς * P.θ * ε j / (8 * (3 * finMax 1 L p + σ)) := by ring
      _ ≤ P.ς * P.θ * ε j / (4 * (3 * finMax 1 L p + σ)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)

/-- **Runs with the radii property (12.2.50)** ([cartis2022evaluation], Lemmas 12.2.9, 12.2.10):
under f.D1pL in finite dimension, with `1 ≤ q ≤ p`, `ε ∈ (0, 1]^q` and `δ₀ ∈ (0, 1]^q`, from every
`x₀` there is an ARqp run whose Step-2 radii are `1` at the orders `j ≤ 2` (12.2.44) and satisfy
`δs_{k,j} ≥ κ_δ(σ_k) ε_j` for all `j ∈ [1:q]` at every iteration before termination ((12.2.45),
(12.2.50)); in particular the hypotheses of Theorem 12.2.14 can be met. -/
theorem algorithm_12_2_2_exists_of_D1pL [FiniteDimensional ℝ E] (hf : AssumptionD1pL f p L)
    (P : ARqpParams) (hq : 1 ≤ q) (hqp : q ≤ p) {ε δ₀ : ℕ → ℝ}
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1)
    (x₀ : E) :
    ∃ (x s : ℕ → E) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → E), x 0 = x₀ ∧
      algorithm_12_2_2 f P p q ε δ₀ x s σ δ δs d dm ∧
      (∀ k, (∀ i < k, ¬ arqpStop f P p q ε x s σ δ d i) →
        ∀ j ∈ Finset.Icc 1 q, j ≤ 2 → δs k j = 1) ∧
      ∀ k, (∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) →
        ∀ j ∈ Finset.Icc 1 q, arqpKappaDelta P (finMax 1 L p) (σ k) * ε j ≤ δs k j :=
  exists_isARqpRun_of_anchored (A := univ) (fun _ hj y _ => hf.norm_iteratedFDeriv_le_finMax hj y)
    P hq hqp hε hδ₀ x₀ fun y _ => mem_univ y

/-- **Lemma 12.2.9, algorithmic form** ([cartis2022evaluation], proof of Lemma 12.2.9). Under
f.D1pL in finite dimension, with `1 ≤ q ≤ p`, `ε ∈ (0, 1]^q` and `σ > 0`, consider Algorithm
12.2.3 for the model `m = regularizedModel (ftaylorSeries ℝ f x) p σ`, started with
`μ₀ ∈ (0, 1]`. Every execution returns: there is no infinite sequence of transitions, and every
reachable state that is not final has a successor. Every returned pair `(s, δs)` satisfies the
Step-2 conditions of ARqp ((12.2.27)–(12.2.29)), with `δs_j = 1` for `j ≤ 2` (12.2.44) and
`δs_j ≥ κ_δ(σ) ε_j` for `j ∈ [3:q]` (12.2.45). -/
theorem lemma_12_2_9_algorithm [FiniteDimensional ℝ E] (hf : AssumptionD1pL f p L)
    (P : ARqpParams) (hq : 1 ≤ q) (hqp : q ≤ p) {ε : ℕ → ℝ}
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) {σ : ℝ} (hσ : 0 < σ) (x : E) :
    (∀ μ₀ ∈ Ioc (0 : ℝ) 1, ¬ ∃ c : ℕ → DetailedStepState E,
      c 0 = .findStep μ₀ (fun _ => 1) ∧
        ∀ n, ARqpDetailedTrans (ftaylorSeries ℝ f x) p σ q P.ς P.θ ε (c n) (c (n + 1))) ∧
    (∀ μ₀ ∈ Ioc (0 : ℝ) 1, ∀ b : DetailedStepState E,
      Relation.ReflTransGen (ARqpDetailedTrans (ftaylorSeries ℝ f x) p σ q P.ς P.θ ε)
        (.findStep μ₀ fun _ => 1) b → (∀ s δ, b ≠ .done s δ) →
      ∃ b', ARqpDetailedTrans (ftaylorSeries ℝ f x) p σ q P.ς P.θ ε b b') ∧
    ∀ s δs, algorithm_12_2_3 (regularizedModel (ftaylorSeries ℝ f x) p σ) q P.ς P.θ ε s δs →
      (∃ dm, ARqpStep univ P q ε (ARqpData.ofTaylor (ftaylorSeries ℝ f x) p σ) x s δs dm) ∧
      (∀ j ≤ 2, δs j = 1) ∧
      ∀ j ∈ Finset.Icc 3 q, arqpKappaDelta P (finMax 1 L p) σ * ε j ≤ δs j := by
  have hp : 1 ≤ p := hq.trans hqp
  have hL1 : 1 ≤ finMax 1 L p := one_le_finMax
  have hD : ∀ i ∈ Finset.Icc 2 p, ‖ftaylorSeries ℝ f x i‖ ≤ finMax 1 L p :=
    fun i hi => hf.norm_iteratedFDeriv_le_finMax hi x
  have hε0 : ∀ j ∈ Finset.Icc 1 q, 0 < ε j := fun j hj => (hε j hj).1
  refine ⟨fun μ₀ hμ₀ => arqpDetailedStep_terminates hσ (zero_le_one.trans hL1) hD hq hqp
    P.ς_pos P.θ_pos hε0 hμ₀, fun μ₀ hμ₀ b h hb =>
      arqpDetailedStep_exists_trans hσ hp P.ς_le_one hμ₀ h hb, fun s δs h => ?_⟩
  obtain ⟨h1, h2⟩ := h.exists_arqpStep P hp hσ x
  refine ⟨h1, h2, fun j hj => ?_⟩
  have hj' : j ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨by have := (Finset.mem_Icc.1 hj).1; omega,
    (Finset.mem_Icc.1 hj).2⟩
  obtain ⟨μ₀, hμ₀, hrun⟩ := h
  have hlow := arqpDetailedStep_radius_ge hσ (zero_le_one.trans hL1) hD hq hqp P.ς_pos P.θ_pos hε0
    hμ₀ hrun j hj'
  refine le_trans ?_ hlow
  obtain ⟨hεj, hεj1⟩ := hε j hj'
  refine le_min ?_ (le_of_eq ?_)
  · calc arqpKappaDelta P (finMax 1 L p) σ * ε j ≤ 1 * 1 :=
          mul_le_mul (arqpKappaDelta_lt_one P hL1 hσ.le).le hεj1 hεj.le zero_le_one
      _ = 1 := one_mul 1
  · rw [arqpKappaDelta]; ring

variable {P : ARqpParams} {ε δ₀ : ℕ → ℝ} {x s : ℕ → E} {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ}
  {d dm : ℕ → ℕ → E} {X C A : Set E}

/-- **Lemma 12.2.11** of [cartis2022evaluation] (corrected). Under f.D1pL with `1 ≤ q ≤ p`, let
iteration `k` of an ARqp run be successful and before termination, with a short step
`‖s_k‖ < 1` (so that (12.2.29) holds at `k`), and let the Step-1 test fail at `k + 1`. Then for
some `j ∈ [1:q]`
`(ς - θ) ε_j δ_{k+1,j}^j/j! < (L_{f,p} + σ_max) ∑_{ℓ=1}^j δ_{k+1,j}^ℓ/ℓ! ‖s_k‖^{p-ℓ+1}` (12.2.52).
(The printed factor `1 - θ` is valid only for `ς = 1`: the failed Step-1 test only gives
`φ^{δ}_{f,j}(x_{k+1}) > ς ε_j δ^j/j!`.) -/
theorem lemma_12_2_11 (hf : AssumptionD1pL f p L) (hq : 1 ≤ q) (hqp : q ≤ p)
    (h : algorithm_12_2_2 f P p q ε δ₀ x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) (hs : P.η₁ ≤ arqpRho f p x s σ k)
    (hshort : ‖s k‖ < 1) (hk1 : ¬ arqpStop₁ P q ε (arqpData f p x σ) δ d (k + 1)) :
    ∃ j ∈ Finset.Icc 1 q, (P.ς - P.θ) * ε j * δ (k + 1) j ^ j / j ! <
      (L p + arSigmaMax P.toARParams (L p)) *
        ∑ ℓ ∈ Finset.Icc 1 j, δ (k + 1) j ^ ℓ / ℓ ! * ‖s k‖ ^ (p - ℓ + 1) := by
  have hp : 1 ≤ p := hq.trans hqp
  have hT := hf.toLipschitzDerivsAnchored_top hp univ
  have hσ := IsARqpRun.sigma_le_of_anchored hT subset_rfl
    (fun _ hy _ => hy) h k fun i hi => hk i hi.le
  have hstep := h.step (fun i hi => hk i hi.le) fun h1 => hk k le_rfl (Or.inl h1)
  rw [(h.succ_eq hk hs).2]
  exact ARqpStep.exists_radius_ineq hT (hf.one_le_top hp)
    subset_rfl hq hqp (mem_univ _)
    (P.σmin_nonneg.trans hσ.1) hσ.2 hstep hshort
    (h.next_witness hk hs) (h.next_not_measureTestPasses hk hs hk1)

/-- The common core of Lemmas 12.2.12 and 12.2.13 for an ARqp run: at a successful iteration `k`
before termination after which the Step-1 test fails, under the radii hypotheses of
Lemma 12.2.12, some order `j ∈ [1:q]` satisfies `τ_j ε_j/2 ≤ ‖s_k‖^{p-j+1}` if `q ≤ 2` and
`(τ_j/2) κ̂^{j-1} ε_j^j ≤ ‖s_k‖^p` if `q > 2`. -/
theorem arqp_step_core (hf : AssumptionD1pL f p L) (hq : 1 ≤ q) (hqp : q ≤ p)
    (hθς : P.θ < P.ς) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (h : algorithm_12_2_2 f P p q ε δ₀ x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) (hs : P.η₁ ≤ arqpRho f p x s σ k)
    (hk1 : ¬ arqpStop₁ P q ε (arqpData f p x σ) δ d (k + 1))
    (hrad : (q ≤ 2 → ∀ j ∈ Finset.Icc 1 q, δ (k + 1) j = 1) ∧
      (2 < q → 1 ≤ ‖s k‖ ∨ ∀ j ∈ Finset.Icc 1 q,
        arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) * ε j ≤ δ (k + 1) j)) :
    ∃ j ∈ Finset.Icc 1 q,
      (q ≤ 2 → arqpTau P L p j * ε j / 2 ≤ ‖s k‖ ^ (p - j + 1)) ∧
      (2 < q → arqpTau P L p j / 2 * arqpKappaHat P L p q ^ (j - 1) * ε j ^ j ≤ ‖s k‖ ^ p) := by
  have hp : 1 ≤ p := hq.trans hqp
  have hT := hf.toLipschitzDerivsAnchored_top hp univ
  have hσ := IsARqpRun.sigma_le_of_anchored hT subset_rfl
    (fun _ hy _ => hy) h k fun i hi => hk i hi.le
  have hstep := h.step (fun i hi => hk i hi.le) fun h1 => hk k le_rfl (Or.inl h1)
  rw [(h.succ_eq hk hs).2] at hrad
  obtain ⟨j, hj, h1, h2⟩ := ARqpStep.exists_norm_pow_ge hT
    (hf.one_le_top hp) subset_rfl hq
    hqp hθς hε (mem_univ _)
    (P.σmin_nonneg.trans hσ.1) hσ.2 hstep (h.model_lt hk)
    (h.next_witness hk hs) (h.next_not_measureTestPasses hk hs hk1) (u := q ≤ 2)
    ⟨hrad.1, fun h' => hrad.2 (not_le.1 h')⟩
  exact ⟨j, hj, h1, fun h' => h2 (not_le.2 h')⟩

/-- **Lemma 12.2.12** of [cartis2022evaluation] (corrected). Under f.D1pL with `1 ≤ q ≤ p` and
`θ < ς`, let iteration `k` of an ARqp run be successful and before termination, and let the
Step-1 test fail at `k + 1`. Then for some `j ∈ [1:q]`:
* if `q ≤ 2` and `δ_{k+1,j} = 1` for `j ∈ [1:q]`: `‖s_k‖ ≥ (τ_j ε_j/2)^{1/(p-j+1)}`;
* if `q > 2` and `‖s_k‖ ≥ 1` or `δ_{k+1,j} ≥ κ_{δ,min} ε_j` for `j ∈ [1:q]` ((12.2.51)):
  `‖s_k‖ ≥ ((τ_j/2) κ̂^{j-1})^{1/p} ε_j^{j/p}` (12.2.57),

with `τ_j = (ς - θ)/(j!(L_{f,p} + σ_max))` (`arqpTau`) and `κ̂ = min(κ_{δ,min}, τ_q/2)`
(`arqpKappaHat`). The printed constant `κ_{δ,min}` in place of `κ̂` relies on "the first case
implies the second", which needs `κ_{δ,min} ≤ τ_q/2`. (The printed hypothesis `δ_{k+1,j} = 1` for
`j ≤ 2` is not needed when `q > 2`.) -/
theorem lemma_12_2_12 (hf : AssumptionD1pL f p L) (hq : 1 ≤ q) (hqp : q ≤ p)
    (hθς : P.θ < P.ς) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (h : algorithm_12_2_2 f P p q ε δ₀ x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) (hs : P.η₁ ≤ arqpRho f p x s σ k)
    (hk1 : ¬ arqpStop₁ P q ε (arqpData f p x σ) δ d (k + 1)) :
    (q ≤ 2 → (∀ j ∈ Finset.Icc 1 q, δ (k + 1) j = 1) →
      ∃ j ∈ Finset.Icc 1 q,
        (arqpTau P L p j * ε j / 2) ^ (1 / ((p - j + 1 : ℕ) : ℝ)) ≤ ‖s k‖) ∧
    (2 < q → (1 ≤ ‖s k‖ ∨ ∀ j ∈ Finset.Icc 1 q,
        arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) * ε j ≤ δ (k + 1) j) →
      ∃ j ∈ Finset.Icc 1 q,
        (arqpTau P L p j / 2 * arqpKappaHat P L p q ^ (j - 1)) ^ (1 / (p : ℝ)) *
          ε j ^ ((j : ℝ) / p) ≤ ‖s k‖) := by
  have hp : 1 ≤ p := hq.trans hqp
  have hLp : 1 ≤ L p := hf.one_le p (Finset.mem_Icc.2 ⟨hp, le_rfl⟩)
  have hκ := (arqpKappaHat_pos P L hθς hLp q).le
  refine ⟨fun hq2 hrad => ?_, fun hq2 hrad => ?_⟩
  · obtain ⟨j, hj, h1, -⟩ := arqp_step_core hf hq hqp hθς hε h hk hs hk1
      ⟨fun _ => hrad, fun h' => absurd h' (by omega)⟩
    obtain ⟨hε0, -⟩ := hε j hj
    have hτ := arqpTau_pos P L hθς (zero_le_one.trans hLp) j
    exact ⟨j, hj, rpow_one_div_le_of_le_pow (by omega) (by positivity) (norm_nonneg _)
      (h1 hq2)⟩
  · obtain ⟨j, hj, -, h2⟩ := arqp_step_core hf hq hqp hθς hε h hk hs hk1
      ⟨fun h' => absurd h' (by omega), fun _ => hrad⟩
    obtain ⟨hε0, -⟩ := hε j hj
    have hτ := arqpTau_pos P L hθς (zero_le_one.trans hLp) j
    refine ⟨j, hj, ?_⟩
    have hp0 : (p : ℝ) ≠ 0 := by positivity
    calc (arqpTau P L p j / 2 * arqpKappaHat P L p q ^ (j - 1)) ^ (1 / (p : ℝ)) *
          ε j ^ ((j : ℝ) / p)
        = (arqpTau P L p j / 2 * arqpKappaHat P L p q ^ (j - 1) * ε j ^ j) ^
            (1 / (p : ℝ)) := by
          rw [Real.mul_rpow (x := arqpTau P L p j / 2 * arqpKappaHat P L p q ^ (j - 1))
            (y := ε j ^ j) (by positivity) (by positivity), ← Real.rpow_natCast (ε j) j,
            ← Real.rpow_mul hε0.le]
          congr 2
          ring
      _ ≤ ‖s k‖ := rpow_one_div_le_of_le_pow (by omega) (by positivity) (norm_nonneg _) (h2 hq2)

/-- The exponents `π_j` of Lemma 12.2.13 ([cartis2022evaluation]): `(p+1)/(p-j+1)` if
`q ∈ {1, 2}`, `j(p+1)/p` if `q > 2` (the radii mode `u = (q ≤ 2)` of `arqpPiOf`). -/
noncomputable def arqpPi (p q j : ℕ) : ℝ := arqpPiOf (q ≤ 2) p j

/-- The constant `κ_{Δm}` of Lemma 12.2.13 ([cartis2022evaluation]):
`σ_min/(p+1)! (τ_q/2)^{(p+1)/(p-q+1)}` if `q ∈ {1, 2}`, and
`σ_min/(p+1)! ((τ_q/2) κ̂^{q-1})^{q(p+1)/p}` if `q > 2` (with the corrected `κ̂`; the radii mode
`u = (q ≤ 2)` of `arqpKappaDmOf`). -/
noncomputable def arqpKappaDm (P : ARqpParams) (L : ℕ → ℝ) (p q : ℕ) : ℝ :=
  arqpKappaDmOf (q ≤ 2) P L p q

theorem arqpKappaDm_of_le_two {P : ARqpParams} {L : ℕ → ℝ} {p q : ℕ} (hq : q ≤ 2) :
    arqpKappaDm P L p q = P.σmin / ((p + 1)! : ℝ) *
      (arqpTau P L p q / 2) ^ (((p + 1 : ℕ) : ℝ) / ((p - q + 1 : ℕ) : ℝ)) :=
  arqpKappaDmOf_of_pos hq P L p q

theorem arqpKappaDm_of_two_lt {P : ARqpParams} {L : ℕ → ℝ} {p q : ℕ} (hq : 2 < q) :
    arqpKappaDm P L p q = P.σmin / ((p + 1)! : ℝ) *
      (arqpTau P L p q / 2 * arqpKappaHat P L p q ^ (q - 1)) ^ ((q : ℝ) * (p + 1) / p) :=
  arqpKappaDmOf_of_neg (by omega) P L p q

theorem arqpPi_of_le_two {p q j : ℕ} (hq : q ≤ 2) :
    arqpPi p q j = ((p + 1 : ℕ) : ℝ) / ((p - j + 1 : ℕ) : ℝ) :=
  arqpPiOf_of_pos hq p j

theorem arqpPi_of_two_lt {p q j : ℕ} (hq : 2 < q) : arqpPi p q j = (j : ℝ) * (p + 1) / p :=
  arqpPiOf_of_neg (by omega) p j

theorem arqpKappaDm_nonneg {P : ARqpParams} {L : ℕ → ℝ} {p q : ℕ} (hθς : P.θ < P.ς)
    (hL : 1 ≤ L p) : 0 ≤ arqpKappaDm P L p q :=
  arqpKappaDmOf_nonneg _ hθς hL

/-- **Lemma 12.2.13** of [cartis2022evaluation] (corrected). Under f.D1pL with `1 ≤ q ≤ p`,
`θ < ς` and `ε ∈ (0, 1]^q`, let iteration `k` of an ARqp run be successful and before
termination, let the Step-1 test fail at `k + 1`, and assume the radii hypotheses of
Lemma 12.2.12. Then `ΔT_{f,p}(x_k, s_k) ≥ κ_{Δm} min_{j ∈ [1:q]} ε_j^{π_j}` (12.2.61) and
`f(x_k) - f(x_{k+1}) ≥ η₁ κ_{Δm} min_j ε_j^{π_j}` (12.2.62) (`arqpKappaDm`, `arqpPi`; the
minimum is `finMin 1 _ q`). The book assumes only f.D1qL and states the bounds at every iteration
before termination; the proof needs f.D1pL and the next iteration not to terminate. -/
theorem lemma_12_2_13 (hf : AssumptionD1pL f p L) (hq : 1 ≤ q) (hqp : q ≤ p)
    (hθς : P.θ < P.ς) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (h : algorithm_12_2_2 f P p q ε δ₀ x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) (hs : P.η₁ ≤ arqpRho f p x s σ k)
    (hk1 : ¬ arqpStop₁ P q ε (arqpData f p x σ) δ d (k + 1))
    (hrad : (q ≤ 2 → ∀ j ∈ Finset.Icc 1 q, δ (k + 1) j = 1) ∧
      (2 < q → 1 ≤ ‖s k‖ ∨ ∀ j ∈ Finset.Icc 1 q,
        arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) * ε j ≤ δ (k + 1) j)) :
    arqpKappaDm P L p q * finMin 1 (fun j => ε j ^ arqpPi p q j) q ≤
        (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k) ∧
      P.η₁ * (arqpKappaDm P L p q * finMin 1 (fun j => ε j ^ arqpPi p q j) q) ≤
        f (x k) - f (x (k + 1)) :=
  have hT := hf.toLipschitzDerivsAnchored_top (hq.trans hqp) univ
  IsARqpRun.decrease hT (hf.one_le_top (hq.trans hqp)) subset_rfl
    (fun _ hy _ => hy) hq hqp hθς hε h hk hs
    hk1 (u := q ≤ 2)
    ⟨hrad.1, fun h' => hrad.2 (not_le.1 h')⟩

/-- The constant `κ^s_{ARqp} = 1/(η₁ κ_{Δm})` of Theorem 12.2.14 ([cartis2022evaluation]): for
`q ∈ {1, 2}` it is `(p+1)!/(η₁ σ_min) (2 q!(L_{f,p} + σ_max)/(ς - θ))^{(p+1)/(p-q+1)}`
(`κ^{s,1}`), for `q > 2` it is
`(p+1)!/(η₁ σ_min) (2 q!(L_{f,p} + σ_max)/((ς - θ) κ̂^{q-1}))^{q(p+1)/p}` (`κ^{s,2}`, with the
corrected `κ̂`); the radii mode `u = (q ≤ 2)` of `kappaSARqpOf`. -/
noncomputable def kappaSARqp (P : ARqpParams) (L : ℕ → ℝ) (p q : ℕ) : ℝ :=
  kappaSARqpOf (q ≤ 2) P L p q

/-- The constant `κ^a_{ARqp} = κ^s_{ARqp} (1 + |log γ₁|/log γ₂)` of Theorem 12.2.14 (the radii mode
`u = (q ≤ 2)` of `kappaAARqpOf`). -/
noncomputable def kappaAARqp (P : ARqpParams) (L : ℕ → ℝ) (p q : ℕ) : ℝ :=
  kappaAARqpOf (q ≤ 2) P L p q

theorem arqpKappaDm_pos {P : ARqpParams} {L : ℕ → ℝ} {p q : ℕ} (hσmin : 0 < P.σmin)
    (hθς : P.θ < P.ς) (hL : 1 ≤ L p) : 0 < arqpKappaDm P L p q :=
  arqpKappaDmOf_pos _ hσmin hθς hL

theorem kappaSARqp_pos {P : ARqpParams} {L : ℕ → ℝ} {p q : ℕ} (hσmin : 0 < P.σmin)
    (hθς : P.θ < P.ς) (hL : 1 ≤ L p) : 0 < kappaSARqp P L p q :=
  kappaSARqpOf_pos _ hσmin hθς hL

/-- **Certification at a model minimizer `0`** (the content of Lemma 12.2.10,
[cartis2022evaluation]): under f.D1pL with `q ≤ p`, `ε ∈ (0, 1]^q` and `σ > 0`, if `0` globally
minimizes the model `regularizedModel (ftaylorSeries ℝ f y) p σ`, then `y` is an
`(ε, δ)`-approximate `q`-th order minimizer for `δ_j = min(1, ε_j/(4 (3 L_f + σ)))`. -/
theorem isEpsDeltaApproxMinimizer_of_isMinOn_zero {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {y : EuclideanSpace ℝ (Fin n)} {σk : ℝ} (hf : AssumptionD1pL f p L) (hqp : q ≤ p)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hσ : 0 < σk)
    (hmin : IsMinOn (regularizedModel (ftaylorSeries ℝ f y) p σk) univ 0) :
    IsEpsDeltaApproxMinimizer f q ε (fun j => min 1 (ε j / (4 * (3 * finMax 1 L p + σk)))) y := by
  have hU : {e : EuclideanSpace ℝ (Fin n) | y + e ∈ (univ : Set _)} = univ := by ext; simp
  obtain ⟨h1, h2⟩ := isEpsDeltaApprox_of_isMinOn_zero_of_jet (mem_univ y) hf.contDiff.contDiffAt
    (fun _ hi => hf.norm_iteratedFDeriv_le_finMax hi y) hqp hε hσ (hU ▸ hmin)
  rw [hU] at h2
  exact ⟨fun j hj => ⟨hε j hj, h1 j hj⟩, h2⟩

/-- **Lemma 12.2.10, first part** ([cartis2022evaluation]): for `q ≤ 2`, an ARqp run does not
terminate in Step 2. If `k` is the termination index and the Step-1 test fails at `k`, then
`0` minimizes the model, so the model measures of orders `j ≤ 2` vanish at `0`, contradicting the
failed test. Only the smoothness of `f` at `x_k` is used (as under the anchored assumptions). -/
theorem lemma_12_2_10_le_two {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {d dm : ℕ → ℕ → EuclideanSpace ℝ (Fin n)} {k : ℕ}
    (hfk : ContDiffAt ℝ p f (x k)) (hqp : q ≤ p)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1)
    (h : algorithm_12_2_2 f P p q ε δ₀ x s σ δ δs d dm)
    (hk : IsFirstHit (arqpStop f P p q ε x s σ δ d) k)
    (h1 : ¬ arqpStop₁ P q ε (arqpData f p x σ) δ d k) (hq2 : q ≤ 2) : False :=
  h1 (IsARqpRun.arqpStop₁_of_isFirstHit_of_le_two h hfk hqp hε hδ₀ hk hq2)

/-- **Lemma 12.2.10** of [cartis2022evaluation] (termination in Step 2). Under f.D1pL with
`q ≤ p`, `ε ∈ (0, 1]^q` and `δ₀ ∈ (0, 1]^q`, let `k` be the termination index of an ARqp run, with
termination in Step 2 (the Step-1 test fails at `k`). Then `q ≥ 3`, and `x_k` is an
`(ε, δ)`-approximate `q`-th order minimizer for the radii
`δ_j = min(1, ε_j/(4 (3 L_f + σ_k)))`. (The algorithm only stops in Step 2 when `0` globally
minimizes `m_k`; the printed proof applies (12.2.29) to `s_k = 0`, which need not be the returned
step.) -/
theorem lemma_12_2_10 {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {d dm : ℕ → ℕ → EuclideanSpace ℝ (Fin n)}
    (hf : AssumptionD1pL f p L) (hqp : q ≤ p)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1)
    (h : algorithm_12_2_2 f P p q ε δ₀ x s σ δ δs d dm) {k : ℕ}
    (hk : IsFirstHit (arqpStop f P p q ε x s σ δ d) k)
    (h1 : ¬ arqpStop₁ P q ε (arqpData f p x σ) δ d k) :
    (q ≤ 2 → False) ∧
      IsEpsDeltaApproxMinimizer f q ε (fun j => min 1 (ε j / (4 * (3 * finMax 1 L p + σ k))))
        (x k) := by
  have hσ : 0 < σ k := h.toIsARRun.sigma_pos hk.2 k le_rfl
  have hstep := h.step hk.2 h1
  have h2 : arqpStop₂ (arqpData f p x σ) s k := hk.1.resolve_left h1
  have hU : ∀ y : EuclideanSpace ℝ (Fin n),
      {e : EuclideanSpace ℝ (Fin n) | y + e ∈ (univ : Set _)} = univ := fun y => by ext; simp
  have hmin := hstep.isMinOn_of_eq h2
  rw [hU] at hmin
  exact ⟨lemma_12_2_10_le_two hf.contDiff.contDiffAt hqp hε hδ₀ h hk h1,
    isEpsDeltaApproxMinimizer_of_isMinOn_zero hf hqp hε hσ hmin⟩

section ARqpComplexity

variable {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {flow : ℝ}
  {x s : ℕ → EuclideanSpace ℝ (Fin n)} {d dm : ℕ → ℕ → EuclideanSpace ℝ (Fin n)}

/-- **Theorem 12.2.14 (1)** of [cartis2022evaluation] (complexity of ARqp, `q ∈ {1, 2}`). Assume
f.Bb and f.D1pL, `1 ≤ q ≤ 2`, `q ≤ p`, `ε ∈ (0, 1]^q`, `σ_min > 0`, `θ < ς`, and an ARqp run with
`δ₀ = 1` whose steps return radii `δ_{s_k,j} = 1` for `j ∈ [1:q]` (as Lemma 12.2.9 allows). Then
the run terminates at some iteration `k_ε`, in Step 1 (Lemma 12.2.10), with
`φ^1_{f,j}(x_{k_ε}) ≤ ε_j/j!` for `j ∈ [1:q]`, after at most
`κ^{a,1} (f(x₀) - f_low)/min_j ε_j^{(p+1)/(p-j+1)} + κ^c` evaluations of `f` (12.2.63) and
`κ^{s,1} (f(x₀) - f_low)/min_j ε_j^{(p+1)/(p-j+1)} + 2` evaluations of the derivatives (12.2.64)
(`kappaAARqp`, `kappaCARqp`, `kappaSARqp`, with `ς - θ` for the printed `1 - θ`). -/
theorem theorem_12_2_14_i (hb : Chapter02.AssumptionBb f flow) (hf : AssumptionD1pL f p L)
    (hq : 1 ≤ q) (hq2 : q ≤ 2) (hqp : q ≤ p) (hσmin : 0 < P.σmin) (hθς : P.θ < P.ς)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hδ₀ : ∀ j ∈ Finset.Icc 1 q, δ₀ j = 1)
    (h : algorithm_12_2_2 f P p q ε δ₀ x s σ δ δs d dm)
    (hδs : ∀ k, (∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) →
      ∀ j ∈ Finset.Icc 1 q, δs k j = 1) :
    ∃ kε, IsFirstHit (arqpStop f P p q ε x s σ δ d) kε ∧
      arqpStop₁ P q ε (arqpData f p x σ) δ d kε ∧
      (∀ j ∈ Finset.Icc 1 q, phiMeasure f j 1 (x kε) ≤ ε j / j !) ∧
      (funEvalCount kε : ℝ) ≤ kappaAARqp P L p q * (f (x 0) - flow) /
        finMin 1 (fun j => ε j ^ arqpPi p q j) q + kappaCARqp P L p ∧
      (derivEvalCount (fun k => P.η₁ ≤ arqpRho f p x s σ k) kε : ℝ) ≤
        kappaSARqp P L p q * (f (x 0) - flow) / finMin 1 (fun j => ε j ^ arqpPi p q j) q + 2 := by
  have hone := h.delta_eq_one hδ₀ hδs
  have hT := hf.toLipschitzDerivsAnchored_top (hq.trans hqp) univ
  obtain ⟨kε, hk, hF, hD⟩ := IsARqpRun.exists_isFirstHit_of_anchored
    (fun y _ => hb y) hT (hf.one_le_top (hq.trans hqp))
    subset_rfl (fun _ hy _ => hy) hq hqp hσmin hθς hε h (u := q ≤ 2)
    fun k hk _ => ⟨fun _ => hone (k + 1) fun i hi => hk i hi.le,
      fun h' => absurd h' (by omega)⟩
  have hδ₀' : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1 := fun j hj => by
    rw [hδ₀ j hj]; norm_num
  have h1 : arqpStop₁ P q ε (arqpData f p x σ) δ d kε := by
    by_contra h1
    exact (lemma_12_2_10 hf hqp hε hδ₀' h hk h1).1 hq2
  refine ⟨kε, hk, h1, fun j hj => ?_, hF, hD⟩
  have hU : {e : EuclideanSpace ℝ (Fin n) | x kε + e ∈ (univ : Set _)} = univ := by ext; simp
  have hw := h.witness kε hk.2
  rw [hU] at hw
  have := isEpsDeltaApprox_of_measureTestPasses P.ς_pos hw h1 j hj
  rw [hone kε hk.2 j hj, one_pow, mul_one] at this
  exact this

/-- **Theorem 12.2.14 (2)** of [cartis2022evaluation] (complexity of ARqp, `q > 2`, corrected
constant). Assume f.Bb and f.D1pL, `3 ≤ q ≤ p`, `ε ∈ (0, 1]^q`, `δ₀ ∈ (0, 1]^q`, `σ_min > 0`,
`θ < ς`, and an ARqp run satisfying the radii property (12.2.50): before termination, a short
step (`‖s_k‖ < 1`) comes with radii `δ_{s_k,j} ≥ κ_δ(σ_k) ε_j` for `j ∈ [1:q]` (as
Lemma 12.2.9 allows). Then the run terminates at some iteration `k_ε` where `x_{k_ε}` is an
`(ε, δ_ε)`-approximate `q`-th order minimizer for some `δ_ε ∈ (0, 1]^q` (Lemma 12.2.10 for a
termination in Step 2), after at most
`κ^{a,2} (f(x₀) - f_low)/min_j ε_j^{j(p+1)/p} + κ^c` evaluations of `f` (12.2.65) and
`κ^{s,2} (f(x₀) - f_low)/min_j ε_j^{j(p+1)/p} + 2` evaluations of the derivatives (12.2.66)
(`kappaAARqp`, `kappaCARqp`, `kappaSARqp`, with `ς - θ` for `1 - θ` and the corrected
`κ̂ = min(κ_{δ,min}, τ_q/2)` for `κ_{δ,min}`). -/
theorem theorem_12_2_14_ii (hb : Chapter02.AssumptionBb f flow) (hf : AssumptionD1pL f p L)
    (hq : 2 < q) (hqp : q ≤ p) (hσmin : 0 < P.σmin) (hθς : P.θ < P.ς)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1)
    (h : algorithm_12_2_2 f P p q ε δ₀ x s σ δ δs d dm)
    (hrad : ∀ k, (∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) → ‖s k‖ < 1 →
      ∀ j ∈ Finset.Icc 1 q, arqpKappaDelta P (finMax 1 L p) (σ k) * ε j ≤ δs k j) :
    ∃ kε, IsFirstHit (arqpStop f P p q ε x s σ δ d) kε ∧
      (∃ δε : ℕ → ℝ, IsEpsDeltaApproxMinimizer f q ε δε (x kε)) ∧
      (funEvalCount kε : ℝ) ≤ kappaAARqp P L p q * (f (x 0) - flow) /
        finMin 1 (fun j => ε j ^ arqpPi p q j) q + kappaCARqp P L p ∧
      (derivEvalCount (fun k => P.η₁ ≤ arqpRho f p x s σ k) kε : ℝ) ≤
        kappaSARqp P L p q * (f (x 0) - flow) / finMin 1 (fun j => ε j ^ arqpPi p q j) q + 2 := by
  have hq1 : 1 ≤ q := by omega
  have hp : 1 ≤ p := hq1.trans hqp
  have hL1 : 1 ≤ finMax 1 L p := one_le_finMax
  have hT := hf.toLipschitzDerivsAnchored_top hp univ
  obtain ⟨kε, hk, hF, hD⟩ := IsARqpRun.exists_isFirstHit_of_anchored
    (fun y _ => hb y) hT (hf.one_le_top hp)
    subset_rfl (fun _ hy _ => hy) hq1 hqp hσmin hθς hε h (u := q ≤ 2) fun k hk hs => by
    refine ⟨fun h' => absurd h' (by omega), fun _ => ?_⟩
    by_cases hlong : 1 ≤ ‖s k‖
    · exact Or.inl hlong
    refine Or.inr fun j hj => ?_
    have hk' : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i := fun i hi => hk i (by omega)
    rw [(h.succ_eq hk' hs).2]
    have hσ := IsARqpRun.sigma_le_of_anchored hT subset_rfl
      (fun _ hy _ => hy) h k fun i hi => hk' i hi.le
    have hσ0 : 0 ≤ σ k := P.σmin_nonneg.trans hσ.1
    refine le_trans ?_ (hrad k hk' (not_le.1 hlong) j hj)
    exact mul_le_mul_of_nonneg_right (arqpKappaDelta_anti P hL1 hσ0 hσ.2) (hε j hj).1.le
  refine ⟨kε, hk, ?_, hF, hD⟩
  by_cases h1 : arqpStop₁ P q ε (arqpData f p x σ) δ d kε
  · refine ⟨δ kε, fun j hj => ⟨hε j hj, h.delta_mem hδ₀ kε hk.2 j hj⟩, ?_⟩
    have hU : {e : EuclideanSpace ℝ (Fin n) | x kε + e ∈ (univ : Set _)} = univ := by ext; simp
    have hw := h.witness kε hk.2
    rw [hU] at hw
    exact MeasureTestPasses.isEpsDeltaApprox P.ς_pos hw h1
  · exact ⟨_, (lemma_12_2_10 hf hqp hε hδ₀ h hk h1).2⟩

end ARqpComplexity

end ARqp

/-! ### Sharpness for ARqp (§12.2.2.4) -/

section ARqpSharp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The termination test of a global-step ARqp run (radii `1`). -/
abbrev arqpGlobalStop (f : E → ℝ) (P : ARqpParams) (p q : ℕ) (ε : ℕ → ℝ) (x s : ℕ → E)
    (σ : ℕ → ℝ) (d : ℕ → ℕ → E) (k : ℕ) : Prop :=
  IsARRun.Stop (arqpStop₁ P q ε (arqpData f p x σ) (fun _ _ => 1) d)
    (arqpStop₂ (arqpData f p x σ) s) k

/-- **The scenario of Theorem 12.2.15** of [cartis2022evaluation] ("the choice `δ_{s_k,j} = 1`
is possible and made", with steps that globally minimize the model): an ARqp run with all radii
equal to `1` (`δ₀ = 1`, `δ_{s_k} = 1`) whose Step 2 returns a global minimizer `s_k` of the model
`m_k`, without the requirement (12.2.29). For `q ≤ 2` every such run is a genuine ARqp run
(`IsARqpGlobalStepRun.toAlgorithm`); for `q ≥ 3` (12.2.29) may fail with radius `1`
(`theorem_12_2_15_counterexample`). -/
structure IsARqpGlobalStepRun (f : E → ℝ) (P : ARqpParams) (p q : ℕ) (ε : ℕ → ℝ)
    (x s : ℕ → E) (σ : ℕ → ℝ) (d : ℕ → ℕ → E) : Prop where
  /-- Steps 2–4: an adaptive-regularization run whose steps are global model minimizers. -/
  toIsARRun : IsARRun P.toARParams (arqpStop₁ P q ε (arqpData f p x σ) (fun _ _ => 1) d)
    (fun k => IsMinOn (arqpModel f p x σ k) univ (s k)) (arqpStop₂ (arqpData f p x σ) s)
    (arqpRho f p x s σ) x s σ
  /-- Step 1: the witnesses are approximate optimality displacements with radius `1`. -/
  witness : ∀ k, (∀ i < k, ¬ arqpGlobalStop f P p q ε x s σ d i) → ∀ j ∈ Finset.Icc 1 q,
    IsApproxMeasureStep ((ftaylorSeries ℝ f (x k)).taylorDecrement j) 1 univ P.ς (d k j)
  /-- Unsuccessful iterations keep the Step-1 witnesses. -/
  keep : UntilHit (arqpGlobalStop f P p q ε x s σ d) fun k =>
    ¬ P.η₁ ≤ arqpRho f p x s σ k → d (k + 1) = d k

/-- **Global-step runs are ARqp runs for `q ≤ 2`** ([cartis2022evaluation], proof of
Corollary 12.2.16 with Theorem 12.1.4): a global minimizer of the model satisfies (12.2.29) with
radii `1` at the orders `j ≤ 2` (with `d^m_j = 0`). -/
theorem IsARqpGlobalStepRun.toAlgorithm {f : E → ℝ} {P : ARqpParams} {p q : ℕ} {ε : ℕ → ℝ}
    {x s : ℕ → E} {σ : ℕ → ℝ} {d : ℕ → ℕ → E} (h : IsARqpGlobalStepRun f P p q ε x s σ d)
    (hq2 : q ≤ 2) (hqp : q ≤ p) (hε : ∀ j ∈ Finset.Icc 1 q, 0 ≤ ε j) :
    algorithm_12_2_2 f P p q ε (fun _ => 1) x s σ (fun _ _ => 1) (fun _ _ => 1) d
      (fun _ _ => 0) := by
  have hU : ∀ y : E, {e : E | y + e ∈ (univ : Set E)} = univ := fun y => by ext; simp
  refine ⟨h.toIsARRun.mono fun k hmin => ?_, mem_univ _, rfl, fun k hk j hj => ?_,
    fun k hk => ⟨fun _ => rfl, fun hρ => ⟨rfl, h.keep k hk hρ⟩⟩⟩
  · refine ⟨mem_univ _, hmin (mem_univ 0), fun heq => ?_, fun _ _ => one_pos, fun _ _ => le_rfl,
      Or.inr fun j hj => ?_⟩
    · rw [hU]
      intro e _
      change regularizedModel _ p (σ k) 0 ≤ regularizedModel _ p (σ k) e
      change regularizedModel _ p (σ k) (s k) = regularizedModel _ p (σ k) 0 at heq
      rw [← heq]
      exact hmin (mem_univ e)
    · rw [hU]
      have hjp : j ≤ p := (Finset.mem_Icc.1 hj).2.trans hqp
      have hcd : ContDiffAt ℝ j (arqpModel f p x σ k) (s k) :=
        (contDiff_regularizedModel (D := ftaylorSeries ℝ f (x k))).contDiffAt.of_le
          (by exact_mod_cast hjp)
      have hφ := taylorMeasure_eq_zero_of_isLocalMin hcd (hmin.isLocalMin univ_mem)
        (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hj).1, (Finset.mem_Icc.1 hj).2.trans hq2⟩)
        zero_le_one
      refine ⟨⟨⟨by simp, mem_univ _⟩, ?_⟩, ?_⟩
      · change P.ς * taylorMeasure (ftaylorSeries ℝ (arqpModel f p x σ k) (s k)) j 1 univ ≤
          (ftaylorSeries ℝ (arqpModel f p x σ k) (s k)).taylorDecrement j 0
        rw [hφ, mul_zero, FormalMultilinearSeries.taylorDecrement_zero_right]
      · change (ftaylorSeries ℝ (arqpModel f p x σ k) (s k)).taylorDecrement j 0 ≤ _
        rw [FormalMultilinearSeries.taylorDecrement_zero_right]
        have := P.ς_pos; have := P.θ_pos; have := hε j hj
        positivity
  · rw [hU]
    exact h.witness k hk j hj

/-- **Theorem 12.2.15** of [cartis2022evaluation] (slow convergence of ARqp, good case). For
`1 ≤ q ≤ p` there are `f_low` and `L ≥ 1` depending only on `p, q` such that, for every
`ε ∈ (0, 1]` (the book takes `ε ≤ ½`; all `ε_j = ε`) and ARqp constants with
`σ₀ = p!/(q-1)!`, there is `f : ℝ → ℝ` satisfying f.Bb and f.D1pL and a global-step ARqp run
(radii `1`, steps the global model minimizers (12.2.70)) from `x₀ = 0` with `σ_k = σ₀` and
`ρ_k = 1`, whose first termination index is `k_ε = ⌈ε^{-(p+1)/(p-q+1)}⌉`, where
`φ^1_{f,j}(x_{k_ε}) ≤ ε/j!` for `j ∈ [1:q]`, while `φ^1_{f,q}(x_k) > ε/q!` before: ARqp may need
`ε^{-(p+1)/(p-q+1)}` iterations and evaluations. The run is in the relaxed scenario
`IsARqpGlobalStepRun`, whose Step 2 does not require (12.2.29); it is a genuine ARqp run only for
`q ≤ 2` (`corollary_12_2_16`), while for `q ≥ 3` (12.2.29) with radius `1` may fail, e.g. for
`p = q = 3` (`theorem_12_2_15_counterexample`). -/
theorem theorem_12_2_15 {p q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) :
    ∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ P : ARqpParams,
      P.σ₀ = (p ! : ℝ) / (q - 1)! →
      ∃ f : ℝ → ℝ, (∀ t, flow ≤ f t) ∧ AssumptionD1pL f p (fun _ => L) ∧
        ∃ (x s σ : ℕ → ℝ) (d : ℕ → ℕ → ℝ),
          IsARqpGlobalStepRun f P p q (fun _ => ε) x s σ d ∧ x 0 = 0 ∧ (∀ k, σ k = P.σ₀) ∧
          (∀ k < ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊, arqpRho f p x s σ k = 1) ∧
          IsFirstHit (arqpGlobalStop f P p q (fun _ => ε) x s σ d)
            ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ ∧
          (∀ j ∈ Finset.Icc 1 q, phiMeasure f j 1
            (x ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊) ≤ ε / j !) ∧
          ∀ k < ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊,
            ε / q ! < phiMeasure f q 1 (x k) := by
  obtain ⟨L, B, hL, hB, hG⟩ := exists_slowTaylorOrder_interpolant hq hqp one_pos
  refine ⟨-B, max 1 (max L B), le_max_left _ _, fun ε hε hε1 P hP => ?_⟩
  have hq0 : q ≠ 0 := by omega
  set kε : ℕ := ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ with hkε
  have hkε1 : 1 ≤ kε := Nat.one_le_iff_ne_zero.2 (by
    rw [hkε]; exact (Nat.ceil_pos.2 (Real.rpow_pos_of_pos hε _)).ne')
  have hkεpos : (0 : ℝ) < kε := by exact_mod_cast hkε1
  set a : ℕ → ℝ := fun k => ε + ε * ((kε : ℝ) - k) / kε with ha
  set st : ℕ → ℝ := fun k => (1 * a k) ^ (1 / ((p - q + 1 : ℕ) : ℝ)) with hst
  set x : ℕ → ℝ := fun k => ∑ i ∈ Finset.range k, st i with hx
  have hxs : ∀ k, x (k + 1) = x k + st k := fun k => by
    simp only [hx, Finset.sum_range_succ]
  obtain ⟨G, hGc, hGL, hGB, hGd, hGf⟩ := hG ε kε x hε hε1 hkε fun k _ => hxs k
  clear_value kε
  -- the sequence `a_k = ε + ω_k`
  have ha_ge : ∀ k ≤ kε, ε ≤ a k := fun k hk => by
    simp only [ha]
    have : (0 : ℝ) ≤ ε * ((kε : ℝ) - k) / kε := by
      have : (k : ℝ) ≤ kε := by exact_mod_cast hk
      have : 0 ≤ (kε : ℝ) - k := by linarith
      positivity
    linarith
  have ha_gt : ∀ k < kε, ε < a k := fun k hk => by
    simp only [ha]
    have : (0 : ℝ) < ε * ((kε : ℝ) - k) / kε := by
      have : (k : ℝ) < kε := by exact_mod_cast hk
      have : 0 < (kε : ℝ) - k := by linarith
      positivity
    linarith
  have ha_eq : a kε = ε := by simp only [ha]; rw [sub_self, mul_zero, zero_div, add_zero]
  have hst_pos : ∀ k ≤ kε, 0 < st k := fun k hk => by
    simp only [hst]; exact Real.rpow_pos_of_pos (by linarith [ha_ge k hk]) _
  have hqf : (0 : ℝ) < q ! := by exact_mod_cast q.factorial_pos
  have hqm : q ∈ Finset.Icc 1 p := Finset.mem_Icc.2 ⟨hq, hqp⟩
  have hspike : ∀ k ≤ kε, ∀ i ∈ Finset.Icc 1 p, i ≠ q → iteratedDeriv i G (x k) = 0 :=
    fun k hk i hi hiq => (hGd k hk).2 i (Finset.mem_Icc.1 hi).1 (Finset.mem_Icc.1 hi).2 hiq
  have hGq : ∀ k ≤ kε, iteratedDeriv q G (x k) = -a k := fun k hk => (hGd k hk).1
  -- the models and their minimizers
  set σ₀ := P.σ₀
  have hmodel : ∀ k ≤ kε, regularizedModel (ftaylorSeries ℝ G (x k)) p σ₀ =
      fun t => G (x k) + negMonomialRegModel p q ((p ! : ℝ) / (q - 1)!) (a k) t := fun k hk =>
    funext fun t => by
      rw [regularizedModel_real_spike hqm (hspike k hk), hGq k hk, negMonomialRegModel_def, hP]
      ring
  have hminim : ∀ k ≤ kε,
      IsMinOn (regularizedModel (ftaylorSeries ℝ G (x k)) p σ₀) univ (st k) ∧
      regularizedModel (ftaylorSeries ℝ G (x k)) p σ₀ (st k) <
        regularizedModel (ftaylorSeries ℝ G (x k)) p σ₀ 0 := fun k hk => by
    have hak : 0 < a k := by linarith [ha_ge k hk]
    obtain ⟨hmin, hval⟩ := isMinOn_neg_monomial_add_regularization_book hq hqp hak
    rw [hmodel k hk]
    have hstk : st k = (a k) ^ (1 / ((p - q + 1 : ℕ) : ℝ)) := by simp only [hst, one_mul]
    refine ⟨isMinOn_iff.2 fun t _ => ?_, ?_⟩
    · rw [hstk]
      linarith [isMinOn_iff.1 hmin t (mem_univ t)]
    · rw [hstk]
      simp only
      rw [hval]
      have h0 : negMonomialRegModel p q ((p ! : ℝ) / (q - 1)!) (a k) 0 = 0 := by
        simp [negMonomialRegModel_def, hq0]
      rw [h0]
      have : 0 < (((p - q + 1 : ℕ) : ℝ) / ((p + 1) * q !)) * a k ^ ((p + 1 : ℝ) /
          ((p - q + 1 : ℕ) : ℝ)) := by positivity
      linarith
  -- Taylor decrements along the iterates
  have hdec_lt : ∀ k ≤ kε, ∀ j ∈ Finset.Icc 1 q, j < q → ∀ e : ℝ,
      (ftaylorSeries ℝ G (x k)).taylorDecrement j e = 0 := fun k hk j hj hjq e =>
    taylorDecrement_real_eq_zero (fun i hi => hspike k hk i
      (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hi).1, ((Finset.mem_Icc.1 hi).2.trans hjq.le).trans
        hqp⟩) (by have := (Finset.mem_Icc.1 hi).2; omega)) e
  have hdec_q : ∀ k ≤ kε, ∀ e : ℝ,
      (ftaylorSeries ℝ G (x k)).taylorDecrement q e = a k / q ! * e ^ q := fun k hk e => by
    rw [taylorDecrement_real_spike (m := q) (Finset.mem_Icc.2 ⟨hq, le_rfl⟩)
      (fun i hi hiq => hspike k hk i (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hi).1,
        (Finset.mem_Icc.1 hi).2.trans hqp⟩) hiq), hGq k hk]
    ring
  have hdec_p : ∀ k ≤ kε, (ftaylorSeries ℝ G (x k)).taylorDecrement p (st k) =
      a k * st k ^ q / q ! := fun k hk => by
    rw [taylorDecrement_real_spike hqm (hspike k hk), hGq k hk]
    ring
  have hφ_lt : ∀ k ≤ kε, ∀ j ∈ Finset.Icc 1 q, j < q →
      taylorMeasure (ftaylorSeries ℝ G (x k)) j 1 univ = 0 := fun k hk j hj hjq => by
    have := taylorMeasure_real_monomial (a := 0) (m := 0) le_rfl zero_le_one
      (D := ftaylorSeries ℝ G (x k)) (j := j) fun e => by rw [hdec_lt k hk j hj hjq, zero_mul]
    rwa [zero_mul] at this
  have hφ_q : ∀ k ≤ kε, taylorMeasure (ftaylorSeries ℝ G (x k)) q 1 univ = a k / q ! :=
    fun k hk => by
      have := taylorMeasure_real_monomial
        (div_nonneg (by linarith [ha_ge k hk]) hqf.le) zero_le_one (hdec_q k hk)
      rwa [one_pow, mul_one] at this
  -- witnesses
  have hw : ∀ k j, ∃ e : ℝ, IsApproxMeasureStep ((ftaylorSeries ℝ G (x k)).taylorDecrement j)
      1 univ P.ς e ∧ (ftaylorSeries ℝ G (x k)).taylorDecrement j e =
        P.ς * taylorMeasure (ftaylorSeries ℝ G (x k)) j 1 univ := fun k j =>
    exists_isApproxMeasureStep_eq isClosed_univ (mem_univ 0) (starConvex_univ 0) zero_le_one
      ((ftaylorSeries ℝ G (x k)).continuous_taylorDecrement j).continuousOn
      ((ftaylorSeries ℝ G (x k)).taylorDecrement_zero_right j) ⟨P.ς_pos.le, P.ς_le_one⟩
  choose d hd hdeq using hw
  set σs : ℕ → ℝ := fun _ => σ₀ with hσs
  -- the tests
  have hstop₁ : ∀ k ≤ kε, (arqpStop₁ P q (fun _ => ε) (arqpData G p x σs) (fun _ _ => 1) d k ↔
      k = kε) := by
    intro k hk
    simp only [arqpStop₁, measureTestPasses_iff]
    constructor
    · intro ht
      by_contra hne
      have hlt : k < kε := lt_of_le_of_ne hk hne
      have := ht q (Finset.mem_Icc.2 ⟨hq, le_rfl⟩)
      change (ftaylorSeries ℝ G (x k)).taylorDecrement q (d k q) ≤ _ at this
      rw [hdeq, hφ_q k hk, one_pow, mul_one] at this
      have h1 := ha_gt k hlt
      have h2 : P.ς * ε / q ! < P.ς * (a k / q !) := by
        rw [mul_div_assoc]
        exact mul_lt_mul_of_pos_left (div_lt_div_of_pos_right h1 hqf) P.ς_pos
      linarith
    · intro hkk j hj
      change (ftaylorSeries ℝ G (x k)).taylorDecrement j (d k j) ≤ _
      rw [hdeq]
      rcases (Finset.mem_Icc.1 hj).2.lt_or_eq with hjq | rfl
      · rw [hφ_lt k hk j hj hjq, mul_zero]
        have := P.ς_pos
        positivity
      · rw [hφ_q k hk, hkk, ha_eq, one_pow, mul_one]
        exact le_of_eq (mul_div_assoc _ _ _).symm
  -- the ratio
  have hρ : ∀ k < kε, arqpRho G p x st σs k = 1 := by
    intro k hk
    change reductionRatio G (x k) (st k)
      ((ftaylorSeries ℝ G (x k)).taylorDecrement p (st k)) = 1
    have hpos : 0 < a k * st k ^ q / q ! := by
      have := hst_pos k hk.le
      have : 0 < a k := by linarith [ha_ge k hk.le]
      positivity
    rw [reductionRatio_def, hdec_p k hk.le, ← hxs k, hGf k hk, hxs k, add_sub_cancel_left,
      sub_sub_cancel, div_self hpos.ne']
  have hη1 : P.η₁ ≤ 1 := P.η₁_le_η₂.trans P.η₂_lt_one.le
  have hstop₂ : ∀ k ≤ kε, ¬ arqpStop₂ (arqpData G p x σs) st k := fun k hk h2 =>
    (hminim k hk).2.ne h2
  have hfirst : IsFirstHit (arqpGlobalStop G P p q (fun _ => ε) x st σs d) kε :=
    ⟨Or.inl ((hstop₁ kε le_rfl).2 rfl), fun i hi h' => h'.elim
      (fun h1 => hi.ne ((hstop₁ i hi.le).1 h1)) (hstop₂ i hi.le)⟩
  have hbefore : ∀ k, (∀ i ≤ k, ¬ arqpGlobalStop G P p q (fun _ => ε) x st σs d i) → k < kε := by
    intro k hk
    by_contra hge
    exact hk kε (not_lt.1 hge) hfirst.1
  have hbefore' : ∀ k, (∀ i < k, ¬ arqpGlobalStop G P p q (fun _ => ε) x st σs d i) → k ≤ kε := by
    intro k hk
    by_contra hge
    exact hk kε (not_le.1 hge) hfirst.1
  refine ⟨G, neg_le_of_abs_iteratedDeriv_zero_le fun t => hGB 0 (Nat.zero_le p) t,
    assumptionD1pL_real hGc hGL hGB, x, st, σs, d, ⟨⟨rfl, fun k hk _ => (hminim k
      (hbefore' k hk)).1, fun k hk => ?_⟩, fun k _ j _ => hd k j, fun k hk hρ' => ?_⟩,
    by simp [hx], fun _ => rfl, hρ, hfirst, fun j hj => ?_, fun k hk => ?_⟩
  · have hk' := hbefore k hk
    have hρk := hρ k hk'
    refine ⟨?_, ⟨fun _ => ⟨max_le P.σmin_le_σ₀ ?_, le_rfl⟩, fun _ h => ?_, fun h => ?_⟩⟩
    · rw [hρk, ite_eq_left hη1]; exact hxs k
    · exact mul_le_of_le_one_left P.σ₀_pos.le P.γ₁_le_one
    · rw [hρk] at h; linarith [P.η₂_lt_one]
    · rw [hρk] at h; linarith
  · exact absurd (hρ k (hbefore k hk) ▸ hη1) hρ'
  · rcases (Finset.mem_Icc.1 hj).2.lt_or_eq with hjq | rfl
    · rw [phiMeasure_def, hφ_lt kε le_rfl j hj hjq]
      have : (0 : ℝ) < j ! := by positivity
      positivity
    · rw [phiMeasure_def, hφ_q kε le_rfl, ha_eq]
  · rw [phiMeasure_def, hφ_q k hk.le]
    exact div_lt_div_of_pos_right (ha_gt k hk) hqf

/-- **Corollary 12.2.16** of [cartis2022evaluation] (slow convergence of ARqp for `q ∈ {1, 2}`).
For `q ∈ {1, 2}`, `q ≤ p`, the conclusion of Theorem 12.2.15 holds for a genuine ARqp run
(`algorithm_12_2_2` with `δ₀ = 1`, all radii `1` and `d^m = 0`): there are `f_low`, `L ≥ 1`
depending only on `p, q` such that for every `ε ∈ (0, 1]` and `σ₀ = p!/(q-1)!` some `f : ℝ → ℝ`
with f.Bb and f.D1pL and an ARqp run from `x₀ = 0` first terminate at
`k_ε = ⌈ε^{-(p+1)/(p-q+1)}⌉`, with `φ^1_{f,j}(x_{k_ε}) ≤ ε/j!` for `j ∈ [1:q]` and
`φ^1_{f,q}(x_k) > ε/q!` before. So the bound of Theorem 12.2.14 (1) is sharp in order. -/
theorem corollary_12_2_16 {p q : ℕ} (hq : 1 ≤ q) (hq2 : q ≤ 2) (hqp : q ≤ p) :
    ∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ P : ARqpParams,
      P.σ₀ = (p ! : ℝ) / (q - 1)! →
      ∃ f : ℝ → ℝ, (∀ t, flow ≤ f t) ∧ AssumptionD1pL f p (fun _ => L) ∧
        ∃ (x s σ : ℕ → ℝ) (d : ℕ → ℕ → ℝ),
          algorithm_12_2_2 f P p q (fun _ => ε) (fun _ => 1) x s σ (fun _ _ => 1)
            (fun _ _ => 1) d (fun _ _ => 0) ∧ x 0 = 0 ∧
          IsFirstHit (arqpStop f P p q (fun _ => ε) x s σ (fun _ _ => 1) d)
            ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ ∧
          (∀ j ∈ Finset.Icc 1 q, phiMeasure f j 1
            (x ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊) ≤ ε / j !) ∧
          ∀ k < ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊,
            ε / q ! < phiMeasure f q 1 (x k) := by
  obtain ⟨flow, L, hL, H⟩ := theorem_12_2_15 hq hqp
  refine ⟨flow, L, hL, fun ε hε hε1 P hP => ?_⟩
  obtain ⟨f, hb, hf, x, s, σ, d, hrun, hx0, -, -, hfirst, hφ1, hφ2⟩ := H ε hε hε1 P hP
  exact ⟨f, hb, hf, x, s, σ, d, hrun.toAlgorithm hq2 hqp fun _ _ => hε.le, hx0, hfirst, hφ1, hφ2⟩

/-- **Theorem 12.2.15 fails for `q ≥ 3`** ([cartis2022evaluation], Theorem 12.2.15 with
`p = q = 3`). In the example of the proof at `k = 0` (`f'(x₀) = f''(x₀) = 0`,
`f'''(x₀) = -(ε + ω₀) = -2ε`, `σ₀ = 3!/2!`), the model is
`m(s) = f(x₀) - 2ε s³/3! + 3 |s|⁴/4!`, globally minimized at `s₀ = 2ε` (12.2.70), and
`φ^1_{m,3}(s₀) ≥ ΔT_{m,3}(s₀, -1) = 2ε/3 - ε² ≥ ε/6 > θ ε/3!` for `ε < ½`, `θ < 1`. Since
`‖s₀‖ = 2ε < 1`, the long-step branch is not available, and no displacement satisfies (12.2.29) at
order `3` with the radius `δ_{s_0,3} = 1`: the hypothesis "`δ_{s_k,j} = 1` is possible" of the
theorem fails for its own example (as in Example 12.2.1). (At `ε = ½` the step `s₀ = 1` is long
and is accepted by the long-step branch.) -/
theorem theorem_12_2_15_counterexample {ε θ ς : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2) (hθ : θ < 1)
    (hς : 0 < ς) {G : ℝ → ℝ} {y : ℝ} (h1 : iteratedDeriv 1 G y = 0)
    (h2 : iteratedDeriv 2 G y = 0) (h3 : iteratedDeriv 3 G y = -(2 * ε)) :
    IsMinOn (regularizedModel (ftaylorSeries ℝ G y) 3 ((3 ! : ℝ) / 2 !)) univ (2 * ε) ∧
      ‖2 * ε‖ < 1 ∧ θ * ε / 3 ! <
        phiMeasure (regularizedModel (ftaylorSeries ℝ G y) 3 ((3 ! : ℝ) / 2 !)) 3 1 (2 * ε) ∧
      ¬ ∃ dm : ℝ, IsApproxMeasureStep ((ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ G y)
          3 ((3 ! : ℝ) / 2 !)) (2 * ε)).taylorDecrement 3) 1 univ ς dm ∧
        (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ G y) 3 ((3 ! : ℝ) / 2 !))
          (2 * ε)).taylorDecrement 3 dm ≤ ς * θ * ε * 1 ^ 3 / 3 ! := by
  set a := 2 * ε with ha
  have ha0 : 0 < a := by positivity
  set g : ℝ → ℝ := fun t => -a * t ^ 3 / 6 + t ^ 4 / 8 with hg
  have hmodel : regularizedModel (ftaylorSeries ℝ G y) 3 ((3 ! : ℝ) / 2 !) =
      fun t => G y + g t := by
    funext t
    rw [regularizedModel_real_spike (m := 3) (by decide) (fun i hi hi3 => by
      rcases (show i = 1 ∨ i = 2 by have := Finset.mem_Icc.1 hi; omega) with rfl | rfl
      · exact h1
      · exact h2), h3]
    simp only [hg, (by decide : Even 4).pow_abs]
    norm_num [Nat.factorial]
    ring
  have hmodel' : regularizedModel (ftaylorSeries ℝ G y) 3 ((3 ! : ℝ) / 2 !) =
      fun t => G y + negMonomialRegModel 3 3 ((3 ! : ℝ) / (3 - 1)!) a t := by
    rw [hmodel]
    funext t
    simp only [hg, negMonomialRegModel_def, (by decide : Even 4).pow_abs]
    norm_num [Nat.factorial]
    ring
  -- the decrement along `-1`
  have hc : ContDiffAt ℝ 4 g a := by rw [hg]; fun_prop
  have hdec : (ftaylorSeries ℝ g a).taylorDecrement 3 (-1) = a / 3 - a ^ 2 / 4 := by
    set c : ℕ → ℝ := fun i => if i = 2 then a ^ 2 / 4 else if i = 3 then -a / 3 else
      if i = 4 then 1 / 8 else 0 with hcdef
    have hpoly : ∀ t : ℝ, g (a + t • (-1)) = g a + ∑ i ∈ Finset.Icc 1 4, t ^ i * c i := by
      intro t
      rw [show Finset.Icc 1 4 = {1, 2, 3, 4} by decide]
      simp [hcdef, hg, smul_eq_mul]
      ring
    rw [ftaylorSeries_taylorDecrement_eq, taylorPolynomial_eq_of_poly hc
      (Eventually.of_forall hpoly) (by norm_num : 3 ≤ 4),
      show Finset.Icc 1 3 = {1, 2, 3} by decide]
    simp [hcdef]
    ring
  have hφ : θ * ε / 3 ! <
      phiMeasure (regularizedModel (ftaylorSeries ℝ G y) 3 ((3 ! : ℝ) / 2 !)) 3 1 a := by
    rw [phiMeasure_def, hmodel, taylorMeasure_real_const_add]
    refine lt_of_lt_of_le ?_ (taylorDecrement_le_taylorMeasure _ 3 (S := univ) (d := -1)
      (δ := 1) ⟨by simp, mem_univ _⟩)
    rw [hdec, ha]
    norm_num [Nat.factorial]
    nlinarith
  refine ⟨?_, by rw [Real.norm_eq_abs, abs_of_pos ha0]; linarith, hφ, ?_⟩
  · rw [hmodel']
    obtain ⟨hmin, -⟩ := isMinOn_neg_monomial_add_regularization_book (p := 3) (q := 3)
      (by norm_num) le_rfl ha0
    have e : a ^ (1 / ((3 - 3 + 1 : ℕ) : ℝ)) = a := by norm_num
    rw [e] at hmin
    refine isMinOn_iff.2 fun t _ => ?_
    linarith [isMinOn_iff.1 hmin t (mem_univ t)]
  · rintro ⟨dm, hdm, hle⟩
    have h := hdm.2.trans hle
    change ς * phiMeasure _ 3 1 a ≤ _ at h
    have : ς * (θ * ε / 3 !) < ς * phiMeasure (regularizedModel (ftaylorSeries ℝ G y) 3
        ((3 ! : ℝ) / 2 !)) 3 1 a := mul_lt_mul_of_pos_left hφ hς
    have e : ς * θ * ε * 1 ^ 3 / 3 ! = ς * (θ * ε / 3 !) := by ring
    linarith

/-- The regularization weight (12.2.85) of Theorem 12.2.17: `σ = (3/(p-1))^p p!/q!` if `p > 2`,
`σ = p!` otherwise. -/
noncomputable def arqpSigmaSharp (p q : ℕ) : ℝ :=
  if 2 < p then (3 / ((p : ℝ) - 1)) ^ p * p ! / q ! else p !

theorem arqpSigmaSharp_pos (p q : ℕ) : 0 < arqpSigmaSharp p q := by
  unfold arqpSigmaSharp
  split_ifs with hp
  · have : (0 : ℝ) < (p : ℝ) - 1 := by
      have : (2 : ℝ) < p := by exact_mod_cast hp
      linarith
    positivity
  · positivity

/-- The admissible radius of Theorem 12.2.17: with the weight (12.2.85), `p > 2`,
`ε ∈ (0, 1]` and `β ≥ ε^q/q!`, `(p - 1) ε ≤ 3 (β p!/σ)^{1/p}` (so that Example 12.1.3 (iv) gives
`φ^ε_{m,j}(s*) = 0`). -/
theorem arqpSigmaSharp_radius {p q : ℕ} (hp : 2 < p) (hqp : q ≤ p) {ε β : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hβ : ε ^ q / q ! ≤ β) :
    ((p : ℝ) - 1) * ε ≤ 3 * (β * p ! / arqpSigmaSharp p q) ^ (1 / (p : ℝ)) := by
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp
    linarith
  have hp0 : p ≠ 0 := by omega
  have hqf : (0 : ℝ) < q ! := by positivity
  have hpf : (0 : ℝ) < p ! := by positivity
  have hβ0 : 0 < β := lt_of_lt_of_le (by positivity) hβ
  have e : β * p ! / arqpSigmaSharp p q = (β * q !) * (((p : ℝ) - 1) / 3) ^ p := by
    rw [arqpSigmaSharp, ite_eq_left hp, div_pow, div_pow]
    field_simp
  rw [e, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast (((p : ℝ) - 1) / 3),
    ← Real.rpow_mul (by positivity), mul_one_div_cancel (by exact_mod_cast hp0), Real.rpow_one]
  have h1 : ε ≤ (β * q !) ^ (1 / (p : ℝ)) := by
    have h2 : ε ^ q ≤ β * q ! := by rwa [div_le_iff₀ hqf] at hβ
    calc ε = (ε ^ p) ^ (1 / (p : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le, mul_one_div_cancel
            (by exact_mod_cast hp0), Real.rpow_one]
      _ ≤ (ε ^ q) ^ (1 / (p : ℝ)) :=
          Real.rpow_le_rpow (by positivity) (pow_le_pow_of_le_one hε.le hε1 hqp) (by positivity)
      _ ≤ (β * q !) ^ (1 / (p : ℝ)) := Real.rpow_le_rpow (by positivity) h2 (by positivity)
  have : ((p : ℝ) - 1) * ε ≤ ((p : ℝ) - 1) * (β * q !) ^ (1 / (p : ℝ)) :=
    mul_le_mul_of_nonneg_left h1 hp1.le
  linarith

/-- **Theorem 12.2.17** of [cartis2022evaluation] (slow convergence of ARqp, general case). For
`1 ≤ q ≤ p ≤ r` there are `f_low` and `L ≥ 1` depending only on `p, q, r` such that, for every
`ε ∈ (0, ½]` (all `ε_j = ε`; the book's "sufficiently small") and ARqp constants with `σ₀` the
weight (12.2.85), there is `f : ℝ → ℝ` satisfying f.Bb and f.D1rL and a genuine ARqp run from
`x₀ = 0` with `δ₀ = ε`, `σ_k = σ₀`, steps the global model minimizers (12.2.88), radii
`δ_{s_k} = ε` (12.2.89) (so the radii property (12.2.50) of Theorem 12.2.14 (2) holds) and
`ρ_k = 1`, whose first termination index is `k_ε = ⌈ε^{-q(p+1)/p}⌉`, where `x_{k_ε}` is an
`(ε, ε)`-approximate `q`-th order minimizer: ARqp may need `ε^{-q(p+1)/p}` iterations and
evaluations, even on functions with more Lipschitz derivatives than it uses. -/
theorem theorem_12_2_17 {p q r : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) (hpr : p ≤ r) :
    ∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ P : ARqpParams,
      P.σ₀ = arqpSigmaSharp p q →
      ∃ f : ℝ → ℝ, (∀ t, flow ≤ f t) ∧ AssumptionD1pL f r (fun _ => L) ∧
        ∃ (x s σ : ℕ → ℝ) (d : ℕ → ℕ → ℝ),
          algorithm_12_2_2 f P p q (fun _ => ε) (fun _ => ε) x s σ (fun _ _ => ε)
            (fun _ _ => ε) d (fun _ _ => 0) ∧
          x 0 = 0 ∧ (∀ k, σ k = P.σ₀) ∧
          (∀ k, arqpKappaDelta P (finMax 1 (fun _ => L) p) (σ k) * ε ≤ ε) ∧
          (∀ k < ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊, arqpRho f p x s σ k = 1) ∧
          IsFirstHit (arqpStop f P p q (fun _ => ε) x s σ (fun _ _ => ε) d)
            ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ ∧
          IsEpsDeltaApprox (ftaylorSeries ℝ f (x ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊)) univ q
            (fun _ => ε) (fun _ => ε) := by
  have hp : 1 ≤ p := hq.trans hqp
  set σv := arqpSigmaSharp p q with hσv
  have hσv : 0 < σv := arqpSigmaSharp_pos p q
  obtain ⟨L, B, hL, hB, hG⟩ := exists_slowARqpSmooth_interpolant hq hqp hpr hσv
  refine ⟨-B, max 1 (max L B), le_max_left _ _, fun ε hε hε2 P hP => ?_⟩
  have hε1 : ε ≤ 1 := hε2.trans (by norm_num)
  set kε : ℕ := ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ with hkε
  have hkε1 : 1 ≤ kε := Nat.one_le_iff_ne_zero.2 (by
    rw [hkε]; exact (Nat.ceil_pos.2 (Real.rpow_pos_of_pos hε _)).ne')
  have hkεpos : (0 : ℝ) < kε := by exact_mod_cast hkε1
  have hqf : (0 : ℝ) < q ! := by positivity
  set ω : ℕ → ℝ := fun k => ε ^ ((q : ℝ) * r / p) * ((kε : ℝ) - k) / kε with hω
  set β : ℕ → ℝ := fun k => (ε ^ q + ω k) / q ! with hβ
  set st : ℕ → ℝ := fun k => (p ! * β k / σv) ^ (1 / (p : ℝ)) with hst
  set x : ℕ → ℝ := fun k => ∑ i ∈ Finset.range k, st i with hx
  have hxs : ∀ k, x (k + 1) = x k + st k := fun k => by
    simp only [hx, Finset.sum_range_succ]
  obtain ⟨G, hGc, hGL, hGB, hGd, hGf⟩ := hG ε kε x hε hε1 hkε fun k _ => hxs k
  clear_value kε
  -- `ω_k` and `β_k`
  have hω0 : ∀ k ≤ kε, 0 ≤ ω k := fun k hk => by
    have : (k : ℝ) ≤ kε := by exact_mod_cast hk
    have : 0 ≤ (kε : ℝ) - k := by linarith
    exact div_nonneg (mul_nonneg (Real.rpow_nonneg hε.le _) this) hkεpos.le
  have hωpos : ∀ k < kε, 0 < ω k := fun k hk => by
    have : (k : ℝ) < kε := by exact_mod_cast hk
    have : 0 < (kε : ℝ) - k := by linarith
    exact div_pos (mul_pos (Real.rpow_pos_of_pos hε _) this) hkεpos
  have hωkε : ω kε = 0 := by simp only [hω]; rw [sub_self, mul_zero, zero_div]
  have hωle : ∀ k ≤ kε, ω k ≤ ε ^ q := fun k hk => by
    have h1 : ((kε : ℝ) - k) / kε ≤ 1 := by
      rw [div_le_one hkεpos]; have := (Nat.cast_nonneg (α := ℝ) k); linarith
    have h2 : ε ^ ((q : ℝ) * r / p) ≤ ε ^ q := by
      rw [← Real.rpow_natCast ε q]
      refine Real.rpow_le_rpow_of_exponent_ge hε hε1 ?_
      have : (p : ℝ) ≤ r := by exact_mod_cast hpr
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
      rw [le_div_iff₀ hp0]
      have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
      nlinarith
    calc ω k = ε ^ ((q : ℝ) * r / p) * (((kε : ℝ) - k) / kε) := by simp only [hω]; ring
      _ ≤ ε ^ q * 1 := mul_le_mul h2 h1 (div_nonneg (by
          have : (k : ℝ) ≤ kε := by exact_mod_cast hk
          linarith) hkεpos.le) (by positivity)
      _ = ε ^ q := mul_one _
  have hβ_ge : ∀ k ≤ kε, ε ^ q / q ! ≤ β k := fun k hk => by
    simp only [hβ]; gcongr; linarith [hω0 k hk]
  have hβ_pos : ∀ k ≤ kε, 0 < β k := fun k hk => lt_of_lt_of_le (by positivity) (hβ_ge k hk)
  have hst_pos : ∀ k ≤ kε, 0 < st k := fun k hk => by
    have := hβ_pos k hk; simp only [hst]; positivity
  -- the derivatives at the iterates
  have hspike : ∀ k ≤ kε, ∀ j ≤ r, ∀ i ∈ Finset.Icc 1 j, i ≠ 1 →
      iteratedDeriv i G (x k) = 0 := fun k hk j hj i hi hi1 =>
    (hGd k hk).2 i (by have := (Finset.mem_Icc.1 hi).1; omega)
      ((Finset.mem_Icc.1 hi).2.trans hj)
  have hG1 : ∀ k ≤ kε, iteratedDeriv 1 G (x k) = -β k := fun k hk => by
    rw [iteratedDeriv_one]; exact (hGd k hk).1
  have hdec : ∀ k ≤ kε, ∀ j, 1 ≤ j → j ≤ r → ∀ e : ℝ,
      (ftaylorSeries ℝ G (x k)).taylorDecrement j e = β k * e ^ 1 := fun k hk j hj1 hjr e => by
    rw [taylorDecrement_real_spike (m := 1) (Finset.mem_Icc.2 ⟨le_rfl, hj1⟩)
      (hspike k hk j hjr), hG1 k hk]
    simp
  -- the models
  set σ₀ := P.σ₀
  have hmodel : ∀ k ≤ kε, regularizedModel (ftaylorSeries ℝ G (x k)) p σ₀ =
      fun t => G (x k) + (-β k * t + σv * |t| ^ (p + 1) / (p + 1)!) := fun k hk =>
    funext fun t => by
      rw [regularizedModel_real_spike (Finset.mem_Icc.2 ⟨le_rfl, hp⟩)
        (fun i hi hi1 => hspike k hk p hpr i hi hi1), hG1 k hk, hP]
      ring
  have hstk : ∀ k, st k = (β k * p ! / σv) ^ (1 / (p : ℝ)) := fun k => by
    simp only [hst]; ring_nf
  have hminim : ∀ k ≤ kε,
      IsMinOn (regularizedModel (ftaylorSeries ℝ G (x k)) p σ₀) univ (st k) ∧
      regularizedModel (ftaylorSeries ℝ G (x k)) p σ₀ (st k) <
        regularizedModel (ftaylorSeries ℝ G (x k)) p σ₀ 0 := fun k hk => by
    obtain ⟨hmin, hneg⟩ := isMinOn_linearRegModel hp (hβ_pos k hk) hσv
    rw [hmodel k hk, hstk k]
    refine ⟨isMinOn_iff.2 fun t _ => ?_, ?_⟩
    · linarith [isMinOn_iff.1 hmin t (mem_univ t)]
    · simp only [mul_zero, abs_zero, zero_pow (Nat.succ_ne_zero p), zero_div, add_zero]
      linarith
  -- the model measures vanish at the steps with radius `ε`
  have hφm : ∀ k ≤ kε, ∀ j ∈ Finset.Icc 1 q, taylorMeasure (ftaylorSeries ℝ
      (regularizedModel (ftaylorSeries ℝ G (x k)) p σ₀) (st k)) j ε univ = 0 := by
    intro k hk j hj
    rw [hmodel k hk, taylorMeasure_real_const_add, hstk k]
    refine taylorMeasure_linearRegModel_eq_zero ⟨(Finset.mem_Icc.1 hj).1,
      (Finset.mem_Icc.1 hj).2.trans hqp⟩ (hβ_pos k hk) hσv ?_
    by_cases hp2 : 2 < p
    · exact Or.inr (arqpSigmaSharp_radius hp2 hqp hε hε1 (hβ_ge k hk))
    · exact Or.inl (by have := (Finset.mem_Icc.1 hj).2; omega)
  -- Step-1 measures
  have hφ : ∀ k ≤ kε, ∀ j ∈ Finset.Icc 1 q,
      taylorMeasure (ftaylorSeries ℝ G (x k)) j ε univ = β k * ε := fun k hk j hj => by
    have := taylorMeasure_real_monomial (hβ_pos k hk).le hε.le
      (hdec k hk j (Finset.mem_Icc.1 hj).1 (((Finset.mem_Icc.1 hj).2.trans hqp).trans hpr))
    rwa [pow_one] at this
  -- witnesses
  have hw : ∀ k j, ∃ e : ℝ, IsApproxMeasureStep ((ftaylorSeries ℝ G (x k)).taylorDecrement j)
      ε univ P.ς e ∧ (ftaylorSeries ℝ G (x k)).taylorDecrement j e =
        P.ς * taylorMeasure (ftaylorSeries ℝ G (x k)) j ε univ := fun k j =>
    exists_isApproxMeasureStep_eq isClosed_univ (mem_univ 0) (starConvex_univ 0) hε.le
      ((ftaylorSeries ℝ G (x k)).continuous_taylorDecrement j).continuousOn
      ((ftaylorSeries ℝ G (x k)).taylorDecrement_zero_right j) ⟨P.ς_pos.le, P.ς_le_one⟩
  choose d hd hdeq using hw
  set σs : ℕ → ℝ := fun _ => σ₀ with hσs
  have hU : ∀ y : ℝ, {e : ℝ | y + e ∈ (univ : Set ℝ)} = univ := fun y => by ext; simp
  -- the test
  have hstop₁ : ∀ k ≤ kε,
      (arqpStop₁ P q (fun _ => ε) (arqpData G p x σs) (fun _ _ => ε) d k ↔ k = kε) := by
    intro k hk
    simp only [arqpStop₁, measureTestPasses_iff]
    have hς := P.ς_pos
    constructor
    · intro ht
      by_contra hne
      have hlt : k < kε := lt_of_le_of_ne hk hne
      have := ht q (Finset.mem_Icc.2 ⟨hq, le_rfl⟩)
      change (ftaylorSeries ℝ G (x k)).taylorDecrement q (d k q) ≤ _ at this
      rw [hdeq, hφ k hk q (Finset.mem_Icc.2 ⟨hq, le_rfl⟩)] at this
      have h1 : ε ^ q / q ! < β k := by
        simp only [hβ]; gcongr; linarith [hωpos k hlt]
      have h2 : P.ς * ε * ε ^ q / q ! < P.ς * (β k * ε) := by
        have := mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right h1 hε) hς
        calc P.ς * ε * ε ^ q / q ! = P.ς * (ε ^ q / q ! * ε) := by ring
          _ < _ := this
      linarith
    · intro hkk j hj
      change (ftaylorSeries ℝ G (x k)).taylorDecrement j (d k j) ≤ _
      rw [hdeq, hφ k hk j hj]
      have hjq := (Finset.mem_Icc.1 hj).2
      have hj1 := (Finset.mem_Icc.1 hj).1
      have hβj : β k ≤ ε ^ j / j ! := by
        rcases hjq.lt_or_eq with hlt | rfl
        · -- `β_k ≤ 2 ε^q/q! ≤ ε^j/j!`
          have h1 : β k ≤ 2 * ε ^ q / q ! := by
            simp only [hβ]; gcongr; linarith [hωle k hk]
          have h2 : 2 * ε ^ q ≤ ε ^ j := by
            have : ε ^ q = ε ^ j * ε ^ (q - j) := by rw [← pow_add]; congr 1; omega
            rw [this]
            have h3 : ε ^ (q - j) ≤ ε := pow_le_of_le_one hε.le hε1 (by omega)
            have := pow_pos hε j
            nlinarith
          have h3 : (j ! : ℝ) ≤ q ! := by exact_mod_cast Nat.factorial_le hlt.le
          calc β k ≤ 2 * ε ^ q / q ! := h1
            _ ≤ ε ^ j / q ! := by gcongr
            _ ≤ ε ^ j / j ! := by gcongr
        · rw [hkk]; simp only [hβ, hωkε, add_zero]; exact le_rfl
      calc P.ς * (β k * ε) ≤ P.ς * (ε ^ j / j ! * ε) := by gcongr
        _ = P.ς * ε * ε ^ j / j ! := by ring
  -- the ratio
  have hρ : ∀ k < kε, arqpRho G p x st σs k = 1 := by
    intro k hk
    change reductionRatio G (x k) (st k)
      ((ftaylorSeries ℝ G (x k)).taylorDecrement p (st k)) = 1
    have hpos : 0 < β k * st k := mul_pos (hβ_pos k hk.le) (hst_pos k hk.le)
    rw [reductionRatio_def, hdec k hk.le p hp hpr, pow_one, ← hxs k, hGf k hk, hxs k,
      add_sub_cancel_left, sub_sub_cancel, div_self hpos.ne']
  have hη1 : P.η₁ ≤ 1 := P.η₁_le_η₂.trans P.η₂_lt_one.le
  have hstop₂ : ∀ k ≤ kε, ¬ arqpStop₂ (arqpData G p x σs) st k := fun k hk h2 =>
    (hminim k hk).2.ne h2
  have hfirst : IsFirstHit (arqpStop G P p q (fun _ => ε) x st σs (fun _ _ => ε) d) kε :=
    ⟨Or.inl ((hstop₁ kε le_rfl).2 rfl), fun i hi h' => h'.elim
      (fun h1 => hi.ne ((hstop₁ i hi.le).1 h1)) (hstop₂ i hi.le)⟩
  have hbefore : ∀ k, (∀ i ≤ k, ¬ arqpStop G P p q (fun _ => ε) x st σs (fun _ _ => ε) d i) →
      k < kε := by
    intro k hk
    by_contra hge
    exact hk kε (not_lt.1 hge) hfirst.1
  have hbefore' : ∀ k, (∀ i < k, ¬ arqpStop G P p q (fun _ => ε) x st σs (fun _ _ => ε) d i) →
      k ≤ kε := by
    intro k hk
    by_contra hge
    exact hk kε (not_le.1 hge) hfirst.1
  have hLf : 1 ≤ finMax 1 (fun _ => max 1 (max L B)) p := le_finMax_left
  refine ⟨G, neg_le_of_abs_iteratedDeriv_zero_le fun t => hGB 0 (Nat.zero_le r) t,
    assumptionD1pL_real hGc hGL hGB, x, st, σs, d, ⟨⟨rfl, fun k hk _ => ?_, fun k hk => ?_⟩,
      mem_univ _, rfl, fun k hk j hj => ?_, fun k hk => ⟨fun _ => rfl, fun hρ' => ?_⟩⟩,
    by simp [hx], fun _ => rfl, fun k => ?_, hρ, hfirst, ?_⟩
  · -- Step 2
    have hk' := hbefore' k hk
    obtain ⟨hmin, hlt⟩ := hminim k hk'
    refine ⟨mem_univ _, hmin (mem_univ 0), fun heq => ?_, fun _ _ => hε, fun _ _ => hε1,
      Or.inr fun j hj => ?_⟩
    · rw [hU]
      intro e _
      change regularizedModel _ p σ₀ 0 ≤ regularizedModel _ p σ₀ e
      change regularizedModel _ p σ₀ (st k) = regularizedModel _ p σ₀ 0 at heq
      rw [← heq]
      exact hmin (mem_univ e)
    · rw [hU]
      refine ⟨⟨⟨by simp [hε.le], mem_univ _⟩, ?_⟩, ?_⟩
      · change P.ς * taylorMeasure (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ G (x k))
          p σ₀) (st k)) j ε univ ≤ (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ G (x k))
          p σ₀) (st k)).taylorDecrement j 0
        rw [hφm k hk' j hj, mul_zero, FormalMultilinearSeries.taylorDecrement_zero_right]
      · change (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ G (x k)) p σ₀)
          (st k)).taylorDecrement j 0 ≤ _
        rw [FormalMultilinearSeries.taylorDecrement_zero_right]
        have := P.ς_pos; have := P.θ_pos
        positivity
  · -- Steps 3–4
    have hk' := hbefore k hk
    have hρk := hρ k hk'
    refine ⟨?_, ⟨fun _ => ⟨max_le P.σmin_le_σ₀ ?_, le_rfl⟩, fun _ h => ?_, fun h => ?_⟩⟩
    · change x (k + 1) = if P.η₁ ≤ arqpRho G p x st σs k then x k + st k else x k
      rw [hρk, ite_eq_left hη1]; exact hxs k
    · exact mul_le_of_le_one_left P.σ₀_pos.le P.γ₁_le_one
    · change arqpRho G p x st σs k < P.η₂ at h
      rw [hρk] at h; linarith [P.η₂_lt_one]
    · change arqpRho G p x st σs k < P.η₁ at h
      rw [hρk] at h; linarith
  · rw [hU]; exact hd k j
  · exact absurd (hη1.trans_eq (hρ k (hbefore k hk)).symm) hρ'
  · calc arqpKappaDelta P (finMax 1 (fun _ => max 1 (max L B)) p) (σs k) * ε ≤ 1 * ε :=
          mul_le_mul_of_nonneg_right (arqpKappaDelta_lt_one P hLf P.σ₀_pos.le).le hε.le
      _ = ε := one_mul ε
  · exact MeasureTestPasses.isEpsDeltaApprox P.ς_pos (fun j _ => hd kε j)
      (hfirst.1.resolve_right (hstop₂ kε le_rfl))

end ARqpSharp

end CartisGouldToint.Chapter12
