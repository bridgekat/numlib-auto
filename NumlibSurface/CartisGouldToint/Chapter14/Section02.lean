import Numlib.Analysis.Calculus.MultivariateTaylor.Coord
import Numlib.Optimization.Complexity.SlowExample.TRq
import Numlib.Optimization.ModelBased.HighOrder.TRqCall
import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Analysis.Calculus.AnchoredLipschitz
import Numlib.Optimization.Optimality.TaylorStability
import Numlib.Optimization.Subproblem.SparseLinear
import NumlibSurface.CartisGouldToint.Chapter13.Section03
import NumlibSurface.CartisGouldToint.Chapter14.Section01

/-!
# Cartis–Gould–Toint §14.2: Problems with simple constraints

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §14.2: minimization of `f` over a
closed nonempty set `X ⊆ ℝⁿ` (14.2.1) whose "simple" constraints are handled without oracle calls.
The constrained measure (14.2.2) `φ^δ_{f,X(x),j}(x)` is the core
`Optimization.taylorMeasure (ftaylorSeries ℝ f x) j δ {d | x + d ∈ X}`.

"Simple constraints" (the Key Definition after Theorem 14.2.1) is an oracle-cost convention
(solving (14.2.2) and ensuring (14.2.5) costs no evaluation of `f`), not a mathematical property:
in the relational formalization of the algorithms the feasible set enters only through the
measures and the feasibility of the iterates, and the evaluation counts never charge the
subproblems. It therefore has no declaration of its own.

## Main definitions

* `AssumptionXCNe X` — X.CNe;
* `sublevel f X x₀` — the sublevel set `𝓛_f(x₀)` (14.2.8);
* `AssumptionD1qLaBX f X X₀ x₀ j₀ q L B` — f.D1qLaB.X (`j₀ = 1`) and its variant f.D1pLaB.X
  (with `j₀ = 0` it also bounds `|f|` on `𝓛_f(x₀)`);
* `AssumptionD0qLaBX f X X₀ x₀ q L B` — f.D0qLaB.X and f.D0pLaB.X ((14.2.9) for `j ∈ [0:q]`,
  (14.2.10) for `j ∈ [1:q]`);
* `AssumptionBbX f X flow` — f.bB.X.

## Main results

* `theorem_14_2_1` — Theorem 14.2.1 (stability of approximate constrained minimizers);
* `sparseMeasure_eq`, `lemma_14_2_5` — the sparse first-order measure (14.2.17)–(14.2.18) and
  Lemma 14.2.5, on `Fin n → ℝ` with the sup norm (the book's `ℓ∞` ball);
* `lemma_14_2_2_arqpc`, `lemma_14_2_3_arqpc`, `theorem_14_2_4_arqpc`,
  `theorem_14_2_4_arqpc_convex` — the ARqpC-SC rows of Lemmas 14.2.2–14.2.3 and Theorem 14.2.4
  (the §14.1 statements carry a general closed `X`);
* `lemma_14_2_2_trq`, `lemma_14_2_3_trq`, `theorem_14_2_4_trq` — the TRq-SC rows (from
  Chapter 12's TRq with a feasible set; Lemma 14.2.3 through Lemma 12.2.3 with a feasible set);
  `lemma_14_2_2_arqp`, `lemma_14_2_3`, `theorem_14_2_4_arqp` — the ARqp-SC rows (from Chapter 12's
  ARqp with a feasible set), in either radii mode `u` (unit radii, order `(p+1)/(p-j+1)`, or
  (12.2.51) at every order, order `j(p+1)/p`; `Optimization.arqpPiOf u`);
* `lemma_14_2_2_trqida`, `lemma_14_2_3_trqida`, `theorem_14_2_4_trqida` (TRqIDA-SC),
  `lemma_14_2_2_trqeda`, `lemma_14_2_3_trqeda`, `theorem_14_2_4_trqeda` (TRqEDA-SC),
  `lemma_14_2_2_arqpida`, `lemma_14_2_3_arqpida`, `theorem_14_2_4_arqpida` (ARqpIDA-SC),
  `lemma_14_2_2_arqpeda`, `lemma_14_2_3_arqpeda`, `theorem_14_2_4_arqpeda` (ARqpEDA-SC) — the
  dynamic-accuracy rows, from the library's runs with a feasible set
  (`Optimization.IsTRqIDARun`, …, `Optimization.IsARqpEDARun`), the
  regularization rows in either mode of the radii control (`Optimization.ARqpDARadiiControl u`: unit
  radii, order `(p+1)/(p-j+1)`, or (12.2.51) at every order, order `j(p+1)/p`);
  `theorem_14_2_4_arqpida_le_two` — on `X = ℝⁿ` with `q ≤ 2`, every ARqpIDA run satisfies the
  bound of the unit-radii mode whatever its radii mode;
* under the anchored assumptions f.D1qLaB.X (TRq-SC) and f.D1pLaB.X (ARqp-SC), the remark after
  (14.2.10): `lemma_14_2_2_trq_anchored`, `lemma_14_2_3_trq_anchored`,
  `theorem_14_2_4_trq_anchored`,
  `lemma_14_2_2_arqp_anchored`, `lemma_14_2_3_anchored`, `theorem_14_2_4_arqp_anchored` (from the
  anchored Chapter 12 analysis, `AssumptionD1qLaBX.toAnchored`); the ARqpC-SC row under anchored
  bounds is `lemma_14_2_2_arqpc_anchored`, `lemma_14_2_3_arqpc_anchored`,
  `theorem_14_2_4_arqpc_anchored`;
* under the anchored assumptions f.D0qLaB.X (TRqIDA-SC, TRqEDA-SC) and f.D0pLaB.X (ARqpIDA-SC,
  ARqpEDA-SC), the remark of Lemmas 14.2.2–14.2.3 and Theorem 14.2.4:
  `lemma_14_2_2_trqida_anchored`, …, `theorem_14_2_4_arqpeda_anchored` (one `…_anchored` per
  dynamic-accuracy row, from the library's anchored analysis,
  `AssumptionD0qLaBX.lipschitzDerivsAnchored`; the rows under f.D0qL on `C ⊇ X` are the instance
  `A = C`). The anchor is the plain sublevel set `𝓛_f(x₀)`
  for all four methods: the objective does not increase along the runs
  (`Optimization.IsTRqIDARun.objective_le`, …, `Optimization.IsARqpEDARun.objective_le`),
  also for the EDA methods with inexact values, since (13.3.5)/(13.3.13) `κ_s ≤ η₁/4` and
  `h_{k,0} ≤ κ_s \overline{ΔT}_k` give a true decrease of at least `η₁/2 \overline{ΔT}_k > 0` on
  successful iterations;
* bridges: `AssumptionD1qLaBX.of_lipschitzOn`, `AssumptionD1qLaBX.assumptionD1pLOn`,
  `assumptionBbX_iff_assumptionWBb`.

## Deviations from the book

* Theorem 14.2.1: the Lipschitz condition is required on the closed ball of radius `δ_j` around
  `x_ε` (implied by the printed open ball of radius larger than `δ_j`); `X` closed and nonempty,
  `δ_j ≤ 1` and `ε_j ≤ 1` are not needed. The printed `δ^j` in (14.2.6) is `δ_j^j`. The radius
  condition `‖d‖ ≤ (j+1)ε_j/L_{f,j}` is used in the equivalent form `L_{f,j} ‖d‖ ≤ (j+1) ε_j`.
* (14.2.18)–(14.2.19) print `max ℓ(d)`; the measure (14.2.17) and Lemma 14.2.5 need the minimum
  of `ℓ(d) = ⟨∇f(x), d⟩`.

* (14.2.12) prints `π_j = j + 1` for TRq-SC, which is stronger than what Lemmas 12.2.4, 13.1.5
  and 13.3.2 give and inconsistent with the order `O(max_j ε_j^{-(q+1)})` of Theorem 14.2.4; the
  TR rows of Lemma 14.2.2 (`lemma_14_2_2_trq`, `lemma_14_2_2_trqida`, `lemma_14_2_2_trqeda`) use
  `π_j = q + 1` (the decrease is a multiple of `ε_min^{q+1}`). The printed row is false per
  iteration for `q = 2` with `κ_decr` depending only on the algorithm parameters and the
  f.D1qLaB.X constants (`lemma_14_2_2_trq_printed_false`,
  `lemma_14_2_2_trq_printed_false_uniform`).
* Lemma 14.2.3 is stated with explicit constants: `κ_unc` contains `|log ε_min|` terms (the
  radius lower bound of the TR methods is proportional to `ε_min`, and the number of
  accuracy-improving iterations of the IDA/EDA methods is logarithmic in `ε_min`); for the IDA
  methods, which have no termination rule, the count holds up to the first approximately optimal
  iterate. The ARqpIDA-SC row of Lemma 14.2.2 holds at successful iterations followed by an
  iterate that is not approximately optimal, and the ARqpEDA-SC row needs `θ < ς/2` and holds at
  the successful iterations of Lemma 13.3.7 (the corrections of Lemmas 13.1.18 and 13.3.7).
* The ARqp-SC rows are stated by radii mode `u` (exponents `Optimization.arqpPiOf u`), while the
  table keys them by `(q, X)`: the mode `u = False` ((12.2.51) at every order) gives the
  "otherwise" entries `j(p+1)/p` for every `q` and `X`, and the unit-radii entries
  `(p+1)/(p-j+1)` hold under the hypothesis that the radii are `1`.
* The IDA/EDA regularization rows are stated by radii mode (`Chapter13.ARqpDARadiiControl u`), while
  the table keys them by `(q, X)`. On `ℝⁿ` with `q ≤ 2` every ARqpIDA run satisfies the
  unit-radii bound of the table in either mode (`theorem_14_2_4_arqpida_le_two`, a strengthening
  of Theorem 13.1.19 (1), which assumes unit radii): a failure of the criterion is a failure at
  unit radii, and for `q ≤ 2` the bound (13.1.57) on the model transfers to unit radii (`φ^δ_j/δ^j`
  is nonincreasing in `δ` for `j ≤ 2`). Hence the mode-`False` bound of `theorem_14_2_4_arqpida`
  is not sharp on `ℝⁿ` for `q = 2 < p` (for ARqpEDA it is,
  `theorem_14_2_4_sharp_arqpeda_otherwise`).
  The book's sharpness argument (reduction to `X = ℝⁿ`) does not reach the "otherwise" entries
  with `q ≤ 2` (`q = 2` with `X ≠ ℝⁿ`, `q = 1` with `X` nonconvex). The sharpness results are in
  `Chapter14.Section02Sharp`.

## Not formalized here

* Runs satisfying the radius policy of the ARqp-SC rows under the anchored assumptions exist on
  `X = ℝⁿ` (`Optimization.exists_isARqpRun_of_anchored`); for a general closed `X` they are the
  ARqpC-SC runs with `c = 0`, `h = 0` of `Chapter14.Section03` (`exists_isARqpCRun_of_hLip`,
  `algorithm_14_1_1.zero_algorithm_12_2_2_feasible`), whose radii satisfy (12.2.51) by
  `algorithm_14_1_1.kappaDeltaMin_mul_le_radius_anchored`; the `¬ u` radius hypothesis of
  `theorem_14_2_4_arqp_anchored` is not discharged for them in this module.
-/

open Set Metric
open scoped Nat

namespace CartisGouldToint.Chapter14

variable {n : ℕ}

set_option hygiene false in
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ### Assumptions -/

/-- **Assumption X.CNe** of [cartis2022evaluation], §14.2: the constraint set `X` is closed and
nonempty. -/
def AssumptionXCNe (X : Set ℝⁿ) : Prop := IsClosed X ∧ X.Nonempty

theorem assumptionXCNe_iff {X : Set ℝⁿ} : AssumptionXCNe X ↔ IsClosed X ∧ X.Nonempty := Iff.rfl

/-- The sublevel set `𝓛_f(x₀) = {x ∈ X | f(x) ≤ f(x₀)}` of [cartis2022evaluation], (14.2.8). -/
def sublevel (f : ℝⁿ → ℝ) (X : Set ℝⁿ) (x₀ : ℝⁿ) : Set ℝⁿ := {x ∈ X | f x ≤ f x₀}

theorem mem_sublevel {f : ℝⁿ → ℝ} {X : Set ℝⁿ} {x₀ x : ℝⁿ} :
    x ∈ sublevel f X x₀ ↔ x ∈ X ∧ f x ≤ f x₀ := Iff.rfl

theorem sublevel_subset {f : ℝⁿ → ℝ} {X : Set ℝⁿ} {x₀ : ℝⁿ} : sublevel f X x₀ ⊆ X :=
  fun _ hx => hx.1

/-- **Assumption f.D1qLaB.X** of [cartis2022evaluation], §14.2.1, and its variants: `f` is `q`
times continuously differentiable on an open convex set `X₀ ⊇ X`, and for every order
`j ∈ [j₀ : q]` there are constants `L j ≥ 1`, `B j ≥ 1` with
`‖∇^j f(x) - ∇^j f(y)‖ ≤ L_j ‖x - y‖` (14.2.9) and `‖∇^j f(x)‖ ≤ B_j` (14.2.10) for every `x` in
the sublevel set `𝓛_f(x₀)` (14.2.8) and `y ∈ X₀`. With `j₀ = 1` this is f.D1qLaB.X (and
f.D1pLaB.X with `p` in place of `q`). With `j₀ = 0` it is f.D0qLaB.X (`AssumptionD0qLaBX`, where
(14.2.9) runs over `[0:q]`) strengthened by `|f| ≤ B_{f,0}` on `𝓛_f(x₀)`
(`AssumptionD1qLaBX.toD0qLaBX`). -/
structure AssumptionD1qLaBX (f : ℝⁿ → ℝ) (X X₀ : Set ℝⁿ) (x₀ : ℝⁿ) (j₀ q : ℕ)
    (L B : ℕ → ℝ) : Prop where
  isOpen : IsOpen X₀
  convex : Convex ℝ X₀
  subset : X ⊆ X₀
  contDiffOn : ContDiffOn ℝ q f X₀
  one_le_lip : ∀ j ∈ Finset.Icc j₀ q, 1 ≤ L j
  one_le_bound : ∀ j ∈ Finset.Icc j₀ q, 1 ≤ B j
  /-- The anchored Lipschitz condition (14.2.9). -/
  lipschitzAnchored : ∀ j ∈ Finset.Icc j₀ q,
    IteratedFDerivLipschitzAnchored f j (L j) (sublevel f X x₀) X₀
  /-- The derivative bound (14.2.10). -/
  norm_le : ∀ j ∈ Finset.Icc j₀ q, ∀ x ∈ sublevel f X x₀, ‖iteratedFDeriv ℝ j f x‖ ≤ B j

/-- f.D1qLaB.X gives the backbone smoothness hypothesis `LipschitzDerivsAnchored` on `X₀` with
the orders `[j₀ : q]` and the anchor set `𝓛_f(x₀)` (the bound (14.2.10) is not used). -/
theorem AssumptionD1qLaBX.toLipschitzDerivsAnchored {f : ℝⁿ → ℝ} {X X₀ : Set ℝⁿ} {x₀ : ℝⁿ}
    {j₀ q : ℕ} {L B : ℕ → ℝ} (h : AssumptionD1qLaBX f X X₀ x₀ j₀ q L B) :
    LipschitzDerivsAnchored f X₀ (sublevel f X x₀) j₀ q L :=
  ⟨h.isOpen, h.convex, sublevel_subset.trans h.subset,
    fun _ hy => h.contDiffOn.contDiffAt (h.isOpen.mem_nhds hy), h.lipschitzAnchored⟩

/-- f.D1qLaB.X is the backbone assumption `LipschitzDerivsAnchored` (orders `[j₀ : q]`, anchor
set `𝓛_f(x₀)`) with `X ⊆ X₀`, normalized constants `L_j, B_j ≥ 1` and the bound (14.2.10). -/
theorem assumptionD1qLaBX_iff {f : ℝⁿ → ℝ} {X X₀ : Set ℝⁿ} {x₀ : ℝⁿ} {j₀ q : ℕ}
    {L B : ℕ → ℝ} : AssumptionD1qLaBX f X X₀ x₀ j₀ q L B ↔
      LipschitzDerivsAnchored f X₀ (sublevel f X x₀) j₀ q L ∧ X ⊆ X₀ ∧
        (∀ j ∈ Finset.Icc j₀ q, 1 ≤ L j) ∧ (∀ j ∈ Finset.Icc j₀ q, 1 ≤ B j) ∧
        ∀ j ∈ Finset.Icc j₀ q, ∀ x ∈ sublevel f X x₀, ‖iteratedFDeriv ℝ j f x‖ ≤ B j :=
  ⟨fun h => ⟨h.toLipschitzDerivsAnchored, h.subset, h.one_le_lip, h.one_le_bound, h.norm_le⟩,
    fun ⟨h, hX, hL, hB, hn⟩ => ⟨h.isOpen, h.convex, hX,
      fun y hy => (h.contDiffAt y hy).contDiffWithinAt, hL, hB, h.lipschitzAnchored, hn⟩⟩

/-- **Assumption f.bB.X** of [cartis2022evaluation], §14.2.1: `f` is bounded below on `X` by
`flow`. -/
def AssumptionBbX (f : ℝⁿ → ℝ) (X : Set ℝⁿ) (flow : ℝ) : Prop := ∀ x ∈ X, flow ≤ f x

theorem assumptionBbX_iff {f : ℝⁿ → ℝ} {X : Set ℝⁿ} {flow : ℝ} :
    AssumptionBbX f X flow ↔ ∀ x ∈ X, flow ≤ f x := Iff.rfl

theorem AssumptionXCNe.isClosed {X : Set ℝⁿ} (h : AssumptionXCNe X) : IsClosed X := h.1

theorem AssumptionXCNe.nonempty {X : Set ℝⁿ} (h : AssumptionXCNe X) : X.Nonempty := h.2

/-- f.bB.X for the composite objective `w = f + h ∘ c` is w.Bb on `X` (§14.1). -/
theorem assumptionBbX_iff_assumptionWBb {m : ℕ} {f : ℝⁿ → ℝ}
    {c : ℝⁿ → EuclideanSpace ℝ (Fin m)} {h : EuclideanSpace ℝ (Fin m) → ℝ} {X : Set ℝⁿ}
    {wlow : ℝ} : AssumptionBbX (fun x => f x + h (c x)) X wlow ↔ AssumptionWBb f c h X wlow :=
  Iff.rfl

/-- Global Lipschitz continuity and boundedness of the derivatives on `X₀` give the anchored
assumption f.D1qLaB.X (the remark after (14.2.10): (14.2.9) is automatic if the derivatives are
Lipschitz on `X₀`). -/
theorem AssumptionD1qLaBX.of_lipschitzOn {f : ℝⁿ → ℝ} {X X₀ : Set ℝⁿ} {x₀ : ℝⁿ} {j₀ q : ℕ}
    {L B : ℕ → ℝ} (hX₀ : IsOpen X₀) (hconv : Convex ℝ X₀) (hX : X ⊆ X₀)
    (hf : ContDiffOn ℝ q f X₀) (hL1 : ∀ j ∈ Finset.Icc j₀ q, 1 ≤ L j)
    (hB1 : ∀ j ∈ Finset.Icc j₀ q, 1 ≤ B j)
    (hlip : ∀ j ∈ Finset.Icc j₀ q, IteratedFDerivLipschitzOn f j (L j) X₀)
    (hbd : ∀ j ∈ Finset.Icc j₀ q, ∀ x ∈ X₀, ‖iteratedFDeriv ℝ j f x‖ ≤ B j) :
    AssumptionD1qLaBX f X X₀ x₀ j₀ q L B where
  isOpen := hX₀
  convex := hconv
  subset := hX
  contDiffOn := hf
  one_le_lip := hL1
  one_le_bound := hB1
  lipschitzAnchored j hj := (hlip j hj).anchored (sublevel_subset.trans hX)
  norm_le j hj x hx := hbd j hj x (hX hx.1)

/-- The anchored assumption gives f.D1pL on the open convex set `X₀` in the sense of
`Chapter12.AssumptionD1pLOn` when, moreover, the anchor is all of `X₀` (`X₀ ⊆ 𝓛_f(x₀)`). -/
theorem AssumptionD1qLaBX.assumptionD1pLOn {f : ℝⁿ → ℝ} {X X₀ : Set ℝⁿ} {x₀ : ℝⁿ} {q : ℕ}
    {L B : ℕ → ℝ} (h : AssumptionD1qLaBX f X X₀ x₀ 1 q L B) (hsub : X₀ ⊆ sublevel f X x₀) :
    Chapter12.AssumptionD1pLOn f X₀ q L where
  isOpen := h.isOpen
  convex := h.convex
  contDiffAt _ hy := h.contDiffOn.contDiffAt (h.isOpen.mem_nhds hy)
  one_le := h.one_le_lip
  lipschitz j hj := iteratedFDerivLipschitzOn_iff.2 fun x hx y hy =>
    h.lipschitzAnchored j hj x (hsub hx) y hy

/-! ### Theorem 14.2.1 -/

/-- **Theorem 14.2.1** of [cartis2022evaluation] (stability of approximate constrained
minimizers). Let `f` be `C^j` near `x_ε` with `∇^j f` Lipschitz with constant `L ≥ 0` on the
closed ball of radius `δ` around `x_ε`, and let
`φ^δ_{f,X(x_ε),j}(x_ε) ≤ ε δ^j / j! + η`. Then
(14.2.6) `f(x_ε + d) ≥ f(x_ε) - 2 ε δ^j/j! - η` for every `d ∈ X(x_ε)` with `‖d‖ ≤ δ` and
`L ‖d‖ ≤ (j + 1) ε` (the book's `‖d‖ ≤ min(δ, (j+1)ε/L)` when `L > 0`); and
(14.2.7) if `L = 0`, `f(x_ε + d) ≥ f(x_ε) - ε δ^j/j! - η` for every `d ∈ X(x_ε)` with `‖d‖ ≤ δ`. -/
theorem theorem_14_2_1 {f : ℝⁿ → ℝ} {X : Set ℝⁿ} {xε : ℝⁿ} {j : ℕ} {δ ε η L : ℝ}
    (hf : ∀ y ∈ closedBall xε δ, ContDiffAt ℝ j f y)
    (hL : IteratedFDerivLipschitzOn f j L (closedBall xε δ)) (hL0 : 0 ≤ L)
    (hφ : Optimization.taylorMeasure (ftaylorSeries ℝ f xε) j δ {d | xε + d ∈ X} ≤
      ε * δ ^ j / j ! + η) :
    (∀ d, xε + d ∈ X → ‖d‖ ≤ δ → L * ‖d‖ ≤ (j + 1) * ε →
      f xε - 2 * ε * δ ^ j / (j ! : ℝ) - η ≤ f (xε + d)) ∧
    (L = 0 → ∀ d, xε + d ∈ X → ‖d‖ ≤ δ → f xε - ε * δ ^ j / (j ! : ℝ) - η ≤ f (xε + d)) := by
  refine ⟨fun d hd hdδ hLd =>
    Optimization.le_of_taylorMeasure_le_of_mul_le hf hL hL0 hφ hd hdδ hLd, ?_⟩
  rintro rfl d hd hdδ
  exact Optimization.le_of_taylorMeasure_le_of_lipschitz_zero hf hL hφ hd hdδ

/-! ### Sparsity constraints (§14.2.2) -/

section Sparse

open Subproblem

variable {nnz : ℕ} {x : Fin n → ℝ} {δ : ℝ}

/-- **The sparse first-order measure** ([cartis2022evaluation], (14.2.17)–(14.2.18), with the
`ℓ∞` ball of `Fin n → ℝ`): for a sparse `x` (`‖x‖₀ ≤ n_nz`) and `δ ≥ 0`, the linear problem
`min {⟨∇f(x), d⟩ | ‖d‖_∞ ≤ δ, ‖x + d‖₀ ≤ n_nz}` has a solution `d⋆`, and the measure
`φ^δ_{f,X(x),1}(x)` equals `-⟨∇f(x), d⋆⟩` (the book's (14.2.18) prints `max ℓ(d)`; the minimum
is meant). Here `∇f(x)` has the coordinates `g_i = ∇f(x)[e_i]`, and `d⋆` is the step (14.2.20) of
an optimal knapsack selection. -/
theorem sparseMeasure_eq (f : (Fin n → ℝ) → ℝ) (hx : x ∈ sparseSet n nnz) (hδ : 0 ≤ δ) :
    ∃ τ, KnapsackFeasible x δ nnz τ ∧
      sparseLinearStep x (fun i => fderiv ℝ f x (Pi.single i 1)) δ τ ∈
        closedBall 0 δ ∩ {d | x + d ∈ sparseSet n nnz} ∧
      IsMinOn (fun d => ∑ i, fderiv ℝ f x (Pi.single i 1) * d i)
        (closedBall 0 δ ∩ {d | x + d ∈ sparseSet n nnz})
        (sparseLinearStep x (fun i => fderiv ℝ f x (Pi.single i 1)) δ τ) ∧
      Optimization.taylorMeasure (ftaylorSeries ℝ f x) 1 δ {d | x + d ∈ sparseSet n nnz} =
        -∑ i, fderiv ℝ f x (Pi.single i 1) *
          sparseLinearStep x (fun i => fderiv ℝ f x (Pi.single i 1)) δ τ i := by
  obtain ⟨τ, hτ, hopt, hn, hS, hmin⟩ :=
    exists_isMinOn_sparseLinearStep (g := fun i => fderiv ℝ f x (Pi.single i 1)) hx hδ
  refine ⟨τ, hτ, ⟨mem_closedBall_zero_iff.2 hn, hS⟩, hmin, ?_⟩
  rw [taylorMeasure_ftaylorSeries_sparse_eq f hx hδ, sum_mul_sparseLinearStep,
    knapsackValue_eq_knapsackOpt hτ hopt]
  ring

/-- **Lemma 14.2.5** of [cartis2022evaluation] (optimal sparse solution of (14.2.18), as a
minimization): for `‖x‖₀ ≤ n_nz`, a vector `g`, `δ ≥ 0` and a selection `τ` solving the knapsack
problem (14.2.21), the vector `d⋆` of (14.2.20) (`Subproblem.sparseLinearStep x g δ τ`) is
feasible (`‖d⋆‖_∞ ≤ δ`, `‖x + d⋆‖₀ ≤ n_nz`) and minimizes `d ↦ ⟨g, d⟩` over the feasible
displacements. (The hypothesis `‖x‖₀ ≤ n_nz` is not needed: the knapsack constraint keeps
`x + d⋆` sparse.) -/
theorem lemma_14_2_5 {g : Fin n → ℝ} {τ : Fin n → Bool} (hδ : 0 ≤ δ)
    (hτ : KnapsackFeasible x δ nnz τ)
    (hopt : ∀ τ', KnapsackFeasible x δ nnz τ' → knapsackValue x g δ τ' ≤ knapsackValue x g δ τ) :
    ‖sparseLinearStep x g δ τ‖ ≤ δ ∧ x + sparseLinearStep x g δ τ ∈ sparseSet n nnz ∧
      IsMinOn (fun d => ∑ i, g i * d i) (closedBall 0 δ ∩ {d | x + d ∈ sparseSet n nnz})
        (sparseLinearStep x g δ τ) :=
  isMinOn_sparseLinearStep hδ hτ hopt

end Sparse

/-! ### Complexity of the -SC algorithms (§14.2.1)

The rows of Lemmas 14.2.2–14.2.3 and Theorem 14.2.4 for ARqpC-SC, TRq-SC and ARqp-SC are stated
here under smoothness on all of `ℝⁿ` (f.D1pL and c.D1pL of §14.1 for ARqpC-SC) or on an open
convex `C ⊇ X` (`Chapter12.AssumptionD1pLOn`, for TRq-SC and ARqp-SC); the TRq-SC and ARqp-SC rows
under the anchored f.D1qLaB.X / f.D1pLaB.X follow in the section on anchored assumptions; the
ARqpC-SC row is also stated under anchored bounds (`lemma_14_2_2_arqpc_anchored`, …). -/

section ARqpCSC

variable {f : ℝⁿ → ℝ} {m : ℕ} {c : ℝⁿ → EuclideanSpace ℝ (Fin m)}
  {h : EuclideanSpace ℝ (Fin m) → ℝ} {X : Set ℝⁿ} {p q : ℕ} {P : ARqpCParams}
  {ε δ₀ : ℕ → ℝ} {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → ℝⁿ}
  {Lf Lc : ℕ → ℝ} {Lh : ℝ}

/-- **Lemma 14.2.2** of [cartis2022evaluation], ARqpC-SC row: for an ARqpC-SC run
(`algorithm_14_1_1` with a closed feasible set `X`) under the (global) assumptions of §14.1 and
`θ < ς`, every successful iteration `k` not followed by termination decreases `w` by at least
`η₁ κ_{Δm} ε_j^{j+1}` for some `j ∈ [1 : q]` (`π_j = j + 1`; the radius policy (14.1.28) holds for
every run). The convex case `q = 1` is the first part of `lemma_14_1_9`. -/
theorem lemma_14_2_2_arqpc (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hθς : P.θ < P.ς) (hf : Chapter12.AssumptionD1pL f p Lf)
    (hc : AssumptionCD1pL c p Lc) (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpcStop f c h p q P ε x s σ δ d i)
    (hsucc : P.η₁ ≤ Optimization.arqpRatio (fun y => f y + h (c y))
      (fun k => arqpcData f c h p (x k) (σ k)) x s k)
    (h1 : ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d (k + 1)) :
    ∃ j ∈ Finset.Icc 1 q, P.η₁ * (kappaDm2 P Lf Lc Lh p q m * ε j ^ (j + 1)) ≤
      (f (x k) + h (c (x k))) - (f (x (k + 1)) + h (c (x (k + 1)))) := by
  have hpol := hr.radius_policy hf hc hL hS (fun i hi => hk i hi.le)
    (fun h' => hk k le_rfl (Or.inl h'))
  rw [← (hr.run.radii k hk).1 hsucc] at hpol
  obtain ⟨j, hj, -, hdec⟩ := (lemma_14_1_9 hr hθς hf hc hL hk hsucc h1).2 hpol
  exact ⟨j, hj, hdec⟩

/-- **Lemma 14.2.3** of [cartis2022evaluation], ARqpC-SC row (Lemma 2.4.1 with the bound
`σ_max` of Lemma 14.1.6): for every iteration `k` reached (up to and including termination),
`k ≤ κ_uns |𝒮_k| + κ_unc` (14.2.13) with `κ_uns = 1 + |log γ₁|/log γ₂` and
`κ_unc = log(σ_max/σ₀)/log γ₂`. -/
theorem lemma_14_2_3_arqpc (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hf : Chapter12.AssumptionD1pL f p Lf) (hc : AssumptionCD1pL c p Lc)
    (hL : AssumptionHLip h Lh) {k : ℕ} (hk : ∀ i < k, ¬ arqpcStop f c h p q P ε x s σ δ d i) :
    (k : ℝ) ≤ (Optimization.successSet (fun j => P.η₁ ≤ Optimization.arqpRatio
        (fun y => f y + h (c y)) (fun k => arqpcData f c h p (x k) (σ k)) x s j) k).card *
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
      Real.log (arqpcSigmaMax P Lf Lc Lh p m / P.σ₀) / Real.log P.γ₂ :=
  hr.run.toIsARRun.le_succ_count hk (sigma_le_arqpcSigmaMax hr hf hc hL hk k le_rfl)

/-- **Theorem 14.2.4** of [cartis2022evaluation], ARqpC-SC row (`h` nonconvex or `q > 1`):
Theorem 14.1.10, part 2, for ARqpC-SC runs with a closed feasible set `X` (measures over
`{d | x + d ∈ X}`, w.Bb on `X`), with moreover `x_{k_ε} ∈ X`. -/
theorem theorem_14_2_4_arqpc (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hθς : P.θ < P.ς) (hf : Chapter12.AssumptionD1pL f p Lf)
    (hc : AssumptionCD1pL c p Lc) (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h) {wlow : ℝ}
    (hw : AssumptionWBb f c h X wlow) {mε : ℝ} (hmε0 : 0 < mε)
    (hmε : ∀ j ∈ Finset.Icc 1 q, mε ≤ ε j ^ (j + 1)) :
    ∃ kε, Optimization.IsFirstHit (arqpcStop f c h p q P ε x s σ δ d) kε ∧ x kε ∈ X ∧
      (∃ δε : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, 0 < δε j ∧ δε j ≤ 1) ∧
        Optimization.IsEpsDeltaApproxComposite (ftaylorSeries ℝ f (x kε))
          (ftaylorSeries ℝ c (x kε)) h {e | x kε + e ∈ X} q ε δε) ∧
      (Optimization.funEvalCount kε : ℝ) ≤
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
          ((f (x 0) + h (c (x 0)) - wlow) / (P.η₁ * (kappaDm2 P Lf Lc Lh p q m * mε))) +
        ((|Real.log P.γ₁| + Real.log (arqpcSigmaMax P Lf Lc Lh p m / P.σ₀)) /
          Real.log P.γ₂ + 2) ∧
      (Optimization.derivEvalCount (fun k => P.η₁ ≤ Optimization.arqpRatio
          (fun y => f y + h (c y)) (fun k => arqpcData f c h p (x k) (σ k)) x s k) kε : ℝ) ≤
        (f (x 0) + h (c (x 0)) - wlow) / (P.η₁ * (kappaDm2 P Lf Lc Lh p q m * mε)) + 2 := by
  obtain ⟨kε, hhit, h2, h3, h4⟩ := theorem_14_1_10_ii hr hθς hf hc hL hS hw hmε0 hmε
  exact ⟨kε, hhit, hr.mem hhit.2, h2, h3, h4⟩

/-- **Theorem 14.2.4** of [cartis2022evaluation], ARqpC-SC row for `q = 1` with `h` and `X`
convex: Theorem 14.1.10, part 1, for ARqpC-SC runs, with moreover `x_{k_ε} ∈ X`. -/
theorem theorem_14_2_4_arqpc_convex (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hθς : P.θ < P.ς) (hf : Chapter12.AssumptionD1pL f p Lf)
    (hc : AssumptionCD1pL c p Lc) (hL : AssumptionHLip h Lh) {wlow : ℝ}
    (hw : AssumptionWBb f c h X wlow) (hq : q = 1) (hconv : ConvexOn ℝ univ h)
    (hXc : Convex ℝ X) (hδ₀ : δ₀ 1 = 1) :
    ∃ kε, Optimization.IsFirstHit (arqpcStop f c h p q P ε x s σ δ d) kε ∧ x kε ∈ X ∧
      Optimization.compositeTaylorMeasure (ftaylorSeries ℝ f (x kε)) (ftaylorSeries ℝ c (x kε))
        h 1 1 {e | x kε + e ∈ X} ≤ ε 1 ∧
      (Optimization.funEvalCount kε : ℝ) ≤
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
          ((f (x 0) + h (c (x 0)) - wlow) /
            (P.η₁ * (kappaDm1 P Lf Lc Lh p m * ε 1 ^ (((p : ℝ) + 1) / p)))) +
        ((|Real.log P.γ₁| + Real.log (arqpcSigmaMax P Lf Lc Lh p m / P.σ₀)) /
          Real.log P.γ₂ + 2) ∧
      (Optimization.derivEvalCount (fun k => P.η₁ ≤ Optimization.arqpRatio
          (fun y => f y + h (c y)) (fun k => arqpcData f c h p (x k) (σ k)) x s k) kε : ℝ) ≤
        (f (x 0) + h (c (x 0)) - wlow) /
          (P.η₁ * (kappaDm1 P Lf Lc Lh p m * ε 1 ^ (((p : ℝ) + 1) / p))) + 2 := by
  obtain ⟨kε, hhit, h2, h3, h4⟩ :=
    theorem_14_1_10_i hr hθς hf hc hL hw hq hconv hXc hδ₀
  exact ⟨kε, hhit, hr.mem hhit.2, h2, h3, h4⟩

variable {X₀ : Set ℝⁿ}

/-- **Lemma 14.2.2** of [cartis2022evaluation], ARqpC-SC row, under the anchored assumptions
(`AnchoredCompositeBounds` on the sublevel set of `w` at `x₀`, the book's f.D1pLaB.X, with an
open convex `X₀ ⊇ X`) and `θ < ς`: every successful iteration `k` not followed by termination
decreases `w` by at least `η₁ κ_{Δm} ε_j^{j+1}` for some `j ∈ [1 : q]`. -/
theorem lemma_14_2_2_arqpc_anchored (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hθς : P.θ < P.ς)
    (hA : AnchoredCompositeBounds f c X₀ (compositeSublevel f c h X (x 0)) p Lf Lc)
    (hX : X ⊆ X₀) (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpcStop f c h p q P ε x s σ δ d i)
    (hsucc : P.η₁ ≤ Optimization.arqpRatio (fun y => f y + h (c y))
      (fun k => arqpcData f c h p (x k) (σ k)) x s k)
    (h1 : ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d (k + 1)) :
    ∃ j ∈ Finset.Icc 1 q, P.η₁ * (kappaDm2 P Lf Lc Lh p q m * ε j ^ (j + 1)) ≤
      (f (x k) + h (c (x k))) - (f (x (k + 1)) + h (c (x (k + 1)))) := by
  have hpol := hr.kappaDeltaMin_mul_le_radius_anchored hA hX hL hS (fun i hi => hk i hi.le)
    (fun h' => hk k le_rfl (Or.inl h'))
  rw [← (hr.run.radii k hk).1 hsucc] at hpol
  obtain ⟨j, hj, -, hdec⟩ := (lemma_14_1_9_anchored hr hθς hA hX hL hk hsucc h1).2 (Or.inr hpol)
  exact ⟨j, hj, hdec⟩

/-- **Lemma 14.2.3** of [cartis2022evaluation], ARqpC-SC row, under the anchored assumptions:
for every iteration `k` reached, `k ≤ κ_uns |𝒮_k| + κ_unc` (14.2.13). -/
theorem lemma_14_2_3_arqpc_anchored (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hA : AnchoredCompositeBounds f c X₀ (compositeSublevel f c h X (x 0)) p Lf Lc)
    (hX : X ⊆ X₀) (hL : AssumptionHLip h Lh) {k : ℕ}
    (hk : ∀ i < k, ¬ arqpcStop f c h p q P ε x s σ δ d i) :
    (k : ℝ) ≤ (Optimization.successSet (fun j => P.η₁ ≤ Optimization.arqpRatio
        (fun y => f y + h (c y)) (fun k => arqpcData f c h p (x k) (σ k)) x s j) k).card *
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
      Real.log (arqpcSigmaMax P Lf Lc Lh p m / P.σ₀) / Real.log P.γ₂ :=
  hr.run.toIsARRun.le_succ_count hk (sigma_le_arqpcSigmaMax_anchored hr hA hX hL hk k le_rfl)

/-- **Theorem 14.2.4** of [cartis2022evaluation], ARqpC-SC row, under the anchored assumptions
(`theorem_14_1_10_ii_anchored` for ARqpC-SC runs), with moreover `x_{k_ε} ∈ X`. -/
theorem theorem_14_2_4_arqpc_anchored (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hθς : P.θ < P.ς)
    (hA : AnchoredCompositeBounds f c X₀ (compositeSublevel f c h X (x 0)) p Lf Lc)
    (hX : X ⊆ X₀) (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h) {wlow : ℝ}
    (hw : AssumptionWBb f c h X wlow) {mε : ℝ} (hmε0 : 0 < mε)
    (hmε : ∀ j ∈ Finset.Icc 1 q, mε ≤ ε j ^ (j + 1)) :
    ∃ kε, Optimization.IsFirstHit (arqpcStop f c h p q P ε x s σ δ d) kε ∧ x kε ∈ X ∧
      (∃ δε : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, 0 < δε j ∧ δε j ≤ 1) ∧
        Optimization.IsEpsDeltaApproxComposite (ftaylorSeries ℝ f (x kε))
          (ftaylorSeries ℝ c (x kε)) h {e | x kε + e ∈ X} q ε δε) ∧
      (Optimization.funEvalCount kε : ℝ) ≤
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
          ((f (x 0) + h (c (x 0)) - wlow) / (P.η₁ * (kappaDm2 P Lf Lc Lh p q m * mε))) +
        ((|Real.log P.γ₁| + Real.log (arqpcSigmaMax P Lf Lc Lh p m / P.σ₀)) /
          Real.log P.γ₂ + 2) ∧
      (Optimization.derivEvalCount (fun k => P.η₁ ≤ Optimization.arqpRatio
          (fun y => f y + h (c y)) (fun k => arqpcData f c h p (x k) (σ k)) x s k) kε : ℝ) ≤
        (f (x 0) + h (c (x 0)) - wlow) / (P.η₁ * (kappaDm2 P Lf Lc Lh p q m * mε)) + 2 := by
  obtain ⟨kε, hhit, h2, h3, h4⟩ := theorem_14_1_10_ii_anchored hr hθς hA hX hL hS hw hmε0 hmε
  exact ⟨kε, hhit, hr.mem hhit.2, h2, h3, h4⟩

end ARqpCSC

section TRqSC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f : E → ℝ} {X C : Set E}
  {P : Optimization.TRqParams} {q : ℕ} {ε : ℕ → ℝ} {ϑ : ℝ} {x s : ℕ → E} {Δ : ℕ → ℝ}
  {jk : ℕ → ℕ} {d : ℕ → ℕ → E} {L : ℕ → ℝ}

/-- **Lemma 14.2.2** of [cartis2022evaluation], TRq-SC row: for a TRq-SC run
(`Chapter12.algorithm_12_2_1_feasible`, feasible set `X ⊆ C`, `x₀ ∈ X`) under f.D1qL on an open
convex `C`, every iteration `k` before termination has a Taylor decrease at least
`(ς κ_δ)^{q+1}/q! ε_min^{q+1}`, and successful iterations decrease `f` by `η₁` times this
(Lemma 12.2.4 with a feasible set; `π_j = q + 1`). -/
theorem lemma_14_2_2_trq (h : Chapter12.algorithm_12_2_1_feasible f X P q ε ϑ x s Δ jk d)
    (hf : Chapter12.AssumptionD1pLOn f C q L) (hXC : X ⊆ C) (hx0 : x 0 ∈ X)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hϑ : Optimization.finMin 1 ε q ≤ ϑ) (hϑ1 : ϑ ≤ 1)
    {k : ℕ} (hk : ∀ i ≤ k, ¬ Chapter12.trqStop f P q ε ϑ x Δ d i) :
    (P.ς * Optimization.trqKappaDelta f P q L ϑ (x 0)) ^ (q + 1) / q ! *
        Optimization.finMin 1 ε q ^ (q + 1) ≤
        (ftaylorSeries ℝ f (x k)).taylorDecrement (jk k) (s k) ∧
      (P.η₁ ≤ Chapter12.trqRho f x s jk k →
        P.η₁ * ((P.ς * Optimization.trqKappaDelta f P q L ϑ (x 0)) ^ (q + 1) / q ! *
          Optimization.finMin 1 ε q ^ (q + 1)) ≤ f (x k) - f (x (k + 1))) :=
  Optimization.IsTRqRun.taylorDecrement_ge_of_anchored h (hf.toLipschitzDerivsAnchored hXC) hXC
    (fun _ hy _ => hy) hx0 hε hϑ hϑ1 hk

/-- **Theorem 14.2.4** of [cartis2022evaluation], TRq-SC row: every TRq-SC run terminates at some
`k_ε` with `x_{k_ε} ∈ X` and the constrained `(ε, δ)`-certificate over `{d | x_{k_ε} + d ∈ X}`,
within the bounds of Theorem 12.2.5 (`O(max_j ε_j^{-(q+1)})`). -/
theorem theorem_14_2_4_trq {flow : ℝ} (hb : ∀ y ∈ X, flow ≤ f y)
    (hf : Chapter12.AssumptionD1pLOn f C q L) (hXC : X ⊆ C) (hx0 : x 0 ∈ X)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hϑ : Optimization.finMin 1 ε q ≤ ϑ) (hϑ1 : ϑ ≤ 1)
    (h : Chapter12.algorithm_12_2_1_feasible f X P q ε ϑ x s Δ jk d) :
    ∃ kε, Optimization.IsFirstHit (Chapter12.trqStop f P q ε ϑ x Δ d) kε ∧ x kε ∈ X ∧
      min (Δ kε) ϑ ∈ Ioc 0 1 ∧
      Optimization.IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) {e | x kε + e ∈ X} q ε
        (fun _ => min (Δ kε) ϑ) ∧
      (Optimization.funEvalCount kε : ℝ) ≤
        Optimization.kappaATRq f P q L ϑ (x 0) * (f (x 0) - flow) /
            Optimization.finMin 1 ε q ^ (q + 1) +
          Optimization.kappaBTRq P * |Real.log (Optimization.finMin 1 ε q)| +
          Optimization.kappaCTRq f P q L ϑ (x 0) ∧
      (Optimization.derivEvalCount (fun k => P.η₁ ≤ Chapter12.trqRho f x s jk k) kε : ℝ) ≤
        Optimization.kappaSTRq f P q L ϑ (x 0) * (f (x 0) - flow) /
          Optimization.finMin 1 ε q ^ (q + 1) + 1 :=
  Optimization.IsTRqRun.complexity hb (hf.toLipschitzDerivsAnchored hXC) hXC
    (fun _ hy _ => hy) hx0 hε hϑ hϑ1 h

/-- **Lemma 14.2.3** of [cartis2022evaluation], TRq-SC row (Lemma 2.3.1 with the radius lower
bound of Lemma 12.2.3 with a feasible set, `Optimization.IsTRqRun.radius_ge_of_anchored`): for a
TRq-SC run under f.D1qL on an open convex `C ⊇ X`, `x₀ ∈ X`, `ε ∈ (0, 1]^q` and `ϑ ∈ [ε_min, 1]`,
every iteration `k` reached (up to and including termination) satisfies `k ≤ κ_uns |𝒮_k| + κ_unc`
(14.2.13) with `κ_uns = 1 + log γ₃/|log γ₂|` and
`κ_unc = |log(min(γ₁ ϑ, κ_Δ ς ε_min)/Δ₀)|/|log γ₂|` (`κ_Δ` of (12.2.14)). -/
theorem lemma_14_2_3_trq (h : Chapter12.algorithm_12_2_1_feasible f X P q ε ϑ x s Δ jk d)
    (hf : Chapter12.AssumptionD1pLOn f C q L) (hXC : X ⊆ C) (hx0 : x 0 ∈ X)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hϑ : Optimization.finMin 1 ε q ≤ ϑ) (hϑ1 : ϑ ≤ 1)
    {k : ℕ} (hk : ∀ i < k, ¬ Chapter12.trqStop f P q ε ϑ x Δ d i) :
    (k : ℝ) ≤
      (Optimization.successSet (fun j => P.η₁ ≤ Chapter12.trqRho f x s jk j) k).card *
          (1 + Real.log P.γ₃ / |Real.log P.γ₂|) +
        |Real.log (min (P.γ₁ * ϑ) (Optimization.trqKappaDelta f P q L ϑ (x 0) *
          (P.ς * Optimization.finMin 1 ε q)) / P.Δ₀)| / |Real.log P.γ₂| :=
  Optimization.IsTRqRun.le_succ_count_of_anchored h (hf.toLipschitzDerivsAnchored hXC) hXC
    (fun _ hy _ => hy) hx0 hε hϑ hϑ1 hk

end TRqSC

section ARqpSC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f : E → ℝ} {X C : Set E}
  {P : Optimization.ARqpParams} {p q : ℕ} {ε δ₀ : ℕ → ℝ} {x s : ℕ → E} {σ : ℕ → ℝ}
  {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → E} {L : ℕ → ℝ}

/-- **Lemma 14.2.2** of [cartis2022evaluation], ARqp-SC row (Lemma 12.2.13 with a feasible set):
for an ARqp-SC run (`Chapter12.algorithm_12_2_2_feasible`, `X ⊆ C`) under f.D1pL on an open convex
`C` and `θ < ς`, every successful iteration `k` not followed by termination decreases `f` by at
least `η₁ κ_{Δm} min_j ε_j^{π_j}`, provided the radius policy holds in radii mode `u`: unit radii
`δ_{k+1,j} = 1` (`u`, `π_j = (p+1)/(p-j+1)`), or a long step or the lower bound (12.2.51) at every
order (`¬ u`, `π_j = j(p+1)/p`), with `π_j = Optimization.arqpPiOf u p j` and
`κ_{Δm} = Optimization.arqpKappaDmOf u`. The mode `u = False` gives the "otherwise" entry
`j(p+1)/p` of the table for every `q` and `X`; the unit-radii entries need `δ_{k,2} = 1` (the
table's `X = ℝⁿ`, `q = 2`) and `δ_{k,1} = 1` (convex `X`), which here is the hypothesis `u` on the
radii. The book's split is the mode `u = (q ≤ 2)` (`Chapter12.arqpPi`, `Chapter12.arqpKappaDm`). -/
theorem lemma_14_2_2_arqp (hf : Chapter12.AssumptionD1pLOn f C p L) (hXC : X ⊆ C) (hq : 1 ≤ q)
    (hqp : q ≤ p) (hθς : P.θ < P.ς) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (h : Chapter12.algorithm_12_2_2_feasible f X P p q ε δ₀ x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ Optimization.arqpStop f P p q ε x s σ δ d i)
    (hs : P.η₁ ≤ Optimization.arqpRho f p x s σ k)
    (hk1 : ¬ Optimization.arqpStop₁ P q ε (Optimization.arqpData f p x σ) δ d (k + 1))
    {u : Prop} [Decidable u] (hrad : (u → ∀ j ∈ Finset.Icc 1 q, δ (k + 1) j = 1) ∧
      (¬ u → 1 ≤ ‖s k‖ ∨ ∀ j ∈ Finset.Icc 1 q,
        Optimization.arqpKappaDelta P (Optimization.finMax 1 L p)
          (Optimization.arSigmaMax P.toARParams (L p)) * ε j ≤ δ (k + 1) j)) :
    Optimization.arqpKappaDmOf u P L p q *
        Optimization.finMin 1 (fun j => ε j ^ Optimization.arqpPiOf u p j) q ≤
        (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k) ∧
      P.η₁ * (Optimization.arqpKappaDmOf u P L p q *
        Optimization.finMin 1 (fun j => ε j ^ Optimization.arqpPiOf u p j) q) ≤
        f (x k) - f (x (k + 1)) :=
  have hT := hf.anchoredTop hXC (hq.trans hqp)
  Optimization.IsARqpRun.decrease hT.toLipschitzDerivsAnchored hT.one_le hXC
    (fun _ hy _ => hy) hq
    hqp hθς hε h hk hs hk1 hrad

/-- **Lemma 14.2.3** of [cartis2022evaluation], ARqp-SC row (Lemma 2.4.1 with the bound
`σ_max = max(σ₀, γ₃ L_{f,p}/(1 - η₂))` of Lemma 12.2.13's analysis): for every iteration `k`
reached, `k ≤ κ_uns |𝒮_k| + κ_unc` (14.2.13) with `κ_uns = 1 + |log γ₁|/log γ₂` and
`κ_unc = log(σ_max/σ₀)/log γ₂`. The other rows are `lemma_14_2_3_arqpc`, `lemma_14_2_3_trq`,
`lemma_14_2_3_trqida`, `lemma_14_2_3_trqeda`, `lemma_14_2_3_arqpida` and `lemma_14_2_3_arqpeda`. -/
theorem lemma_14_2_3 (hf : Chapter12.AssumptionD1pLOn f C p L) (hXC : X ⊆ C) (hp : 1 ≤ p)
    (h : Chapter12.algorithm_12_2_2_feasible f X P p q ε δ₀ x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i < k, ¬ Optimization.arqpStop f P p q ε x s σ δ d i) :
    (k : ℝ) ≤ (Optimization.successSet (fun j => P.η₁ ≤ Optimization.arqpRho f p x s σ j) k).card *
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
      Real.log (Optimization.arSigmaMax P.toARParams (L p) / P.σ₀) / Real.log P.γ₂ :=
  have hT := hf.anchoredTop hXC hp
  h.toIsARRun.le_succ_count hk
    (Optimization.IsARqpRun.sigma_le_of_anchored hT.toLipschitzDerivsAnchored
    hXC (fun _ hy _ => hy) h k hk).2

/-- **Theorem 14.2.4** of [cartis2022evaluation], ARqp-SC row (Theorem 12.2.14 with a feasible
set): under f.bB.X, f.D1pL on an open convex `C ⊇ X`, `σ_min > 0`, `θ < ς` and the radius policy
in radii mode `u` (`δ = 1` if `u`, (12.2.51) at every order if `¬ u`), every ARqp-SC run
terminates at some `k_ε` with `x_{k_ε} ∈ X` and an `(ε, δ_ε)`-approximate `q`-th order
certificate over `{d | x_{k_ε} + d ∈ X}`, within the bounds of Theorem 12.2.14 (orders
`O(max_j ε_j^{-π_j})`, `π_j = Optimization.arqpPiOf u p j`). The mode `u = False` gives the
"otherwise" order `j(p+1)/p` of the table for every `q` and `X`; the book's split is the mode
`u = (q ≤ 2)` (`Chapter12.arqpPi`). -/
theorem theorem_14_2_4_arqp {flow : ℝ} (hb : ∀ y ∈ X, flow ≤ f y)
    (hf : Chapter12.AssumptionD1pLOn f C p L) (hXC : X ⊆ C) (hq : 1 ≤ q) (hqp : q ≤ p)
    (hσmin : 0 < P.σmin) (hθς : P.θ < P.ς) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1)
    (h : Chapter12.algorithm_12_2_2_feasible f X P p q ε δ₀ x s σ δ δs d dm)
    {u : Prop} [Decidable u]
    (hrad : (u → (∀ j ∈ Finset.Icc 1 q, δ₀ j = 1) ∧
        ∀ k, (∀ i ≤ k, ¬ Optimization.arqpStop f P p q ε x s σ δ d i) →
          ∀ j ∈ Finset.Icc 1 q, δs k j = 1) ∧
      (¬ u → ∀ k, (∀ i ≤ k, ¬ Optimization.arqpStop f P p q ε x s σ δ d i) → ‖s k‖ < 1 →
        ∀ j ∈ Finset.Icc 1 q,
          Optimization.arqpKappaDelta P (Optimization.finMax 1 L p) (σ k) * ε j ≤ δs k j)) :
    ∃ kε, Optimization.IsFirstHit (Optimization.arqpStop f P p q ε x s σ δ d) kε ∧ x kε ∈ X ∧
      (∃ δε : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, δε j ∈ Ioc 0 1) ∧
        Optimization.IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) {e | x kε + e ∈ X} q ε δε) ∧
      (Optimization.funEvalCount kε : ℝ) ≤ Optimization.kappaAARqpOf u P L p q * (f (x 0) - flow) /
        Optimization.finMin 1 (fun j => ε j ^ Optimization.arqpPiOf u p j) q +
          Optimization.kappaCARqp P L p ∧
      (Optimization.derivEvalCount (fun k => P.η₁ ≤ Optimization.arqpRho f p x s σ k) kε : ℝ) ≤
        Optimization.kappaSARqpOf u P L p q * (f (x 0) - flow) /
          Optimization.finMin 1 (fun j => ε j ^ Optimization.arqpPiOf u p j) q + 2 :=
  have hT := hf.anchoredTop hXC (hq.trans hqp)
  Optimization.IsARqpRun.complexity hb hT.toLipschitzDerivsAnchored hT.one_le hT.jet hXC
    (fun _ hy _ => hy)
    hq hqp hσmin hθς hε hδ₀ h hrad

end ARqpSC

/-! ### The TRq-SC and ARqp-SC rows under the anchored assumptions

The remark after (14.2.10) of [cartis2022evaluation]: the rows of Lemmas 14.2.2–14.2.3 and
Theorem 14.2.4 only use the anchored assumption f.D1qLaB.X (TRq-SC) or f.D1pLaB.X (ARqp-SC) with
the starting point `x₀ = x 0`. The iterates lie in the sublevel set `𝓛_f(x₀)` (the objective does
not increase along the runs), the models are built at iterates, and the trial points (in
`X ⊆ X₀`) are related to them by Taylor's theorem anchored at the iterate. The bound (14.2.10) is
not used: the jet bounds at the anchors follow from (14.2.9) at the interior points of `X₀`
(`Chapter12.AssumptionD1pLAnchored.norm_iteratedFDeriv_le`), and the constants are those of the
rows above with the anchored Lipschitz constants `L_{f,j}`. -/

section Anchored

variable {f : ℝⁿ → ℝ} {X X₀ : Set ℝⁿ} {L B : ℕ → ℝ}

/-- f.D1qLaB.X (orders `[1:q]`) with anchor point `x₀` gives the anchored assumption of Chapter 12
on `X₀` with the anchor set `𝓛_f(x₀)` (`Chapter12.AssumptionD1pLAnchored`). -/
theorem AssumptionD1qLaBX.toAnchored {x₀ : ℝⁿ} {q : ℕ} (h : AssumptionD1qLaBX f X X₀ x₀ 1 q L B) :
    Chapter12.AssumptionD1pLAnchored f X₀ (sublevel f X x₀) q L where
  isOpen := h.isOpen
  convex := h.convex
  subset := sublevel_subset.trans h.subset
  contDiffAt _ hy := h.contDiffOn.contDiffAt (h.isOpen.mem_nhds hy)
  one_le := h.one_le_lip
  lipschitzAnchored := h.lipschitzAnchored

/-- **Assumption f.D0qLaB.X** of [cartis2022evaluation], §14.2.1 (and f.D0pLaB.X with `p` in
place of `q`): f.D1qLaB.X (the anchored Lipschitz condition (14.2.9) and the bound (14.2.10) for
`j ∈ [1:q]`), together with (14.2.9) for `j = 0`, `|f(x) - f(y)| ≤ L_{f,0} ‖x - y‖` for
`x ∈ 𝓛_f(x₀)` and `y ∈ X₀`, with `L_{f,0} ≥ 1`. The book extends only the indices of (14.2.9) to
`[0:q]`; `AssumptionD1qLaBX` with `j₀ = 0`, which also bounds `|f|` on `𝓛_f(x₀)`, implies it
(`AssumptionD1qLaBX.toD0qLaBX`). -/
structure AssumptionD0qLaBX (f : ℝⁿ → ℝ) (X X₀ : Set ℝⁿ) (x₀ : ℝⁿ) (q : ℕ) (L B : ℕ → ℝ) : Prop
    extends AssumptionD1qLaBX f X X₀ x₀ 1 q L B where
  /-- `L_{f,0} ≥ 1`. -/
  one_le_lip_zero : 1 ≤ L 0
  /-- (14.2.9) for `j = 0`. -/
  lipschitzAnchored_zero : IteratedFDerivLipschitzAnchored f 0 (L 0) (sublevel f X x₀) X₀

/-- `AssumptionD1qLaBX` with `j₀ = 0` (which also asks `|f| ≤ B_{f,0}` on `𝓛_f(x₀)`) gives
f.D0qLaB.X. -/
theorem AssumptionD1qLaBX.toD0qLaBX {x₀ : ℝⁿ} {q : ℕ} (h : AssumptionD1qLaBX f X X₀ x₀ 0 q L B) :
    AssumptionD0qLaBX f X X₀ x₀ q L B where
  isOpen := h.isOpen
  convex := h.convex
  subset := h.subset
  contDiffOn := h.contDiffOn
  one_le_lip j hj := h.one_le_lip j (Finset.Icc_subset_Icc_left (Nat.zero_le 1) hj)
  one_le_bound j hj := h.one_le_bound j (Finset.Icc_subset_Icc_left (Nat.zero_le 1) hj)
  lipschitzAnchored j hj := h.lipschitzAnchored j (Finset.Icc_subset_Icc_left (Nat.zero_le 1) hj)
  norm_le j hj := h.norm_le j (Finset.Icc_subset_Icc_left (Nat.zero_le 1) hj)
  one_le_lip_zero := h.one_le_lip 0 (Finset.mem_Icc.2 ⟨le_rfl, Nat.zero_le q⟩)
  lipschitzAnchored_zero := h.lipschitzAnchored 0 (Finset.mem_Icc.2 ⟨le_rfl, Nat.zero_le q⟩)

/-- f.D0qLaB.X with anchor point `x₀` gives the smoothness hypothesis `LipschitzDerivsAnchored`
of the library on `X₀` with the orders `[0:q]` and the anchor set `𝓛_f(x₀)`; the bound (14.2.10)
is not used. -/
theorem AssumptionD0qLaBX.lipschitzDerivsAnchored {x₀ : ℝⁿ} {q : ℕ}
    (h : AssumptionD0qLaBX f X X₀ x₀ q L B) :
    LipschitzDerivsAnchored f X₀ (sublevel f X x₀) 0 q L where
  isOpen := h.isOpen
  convex := h.convex
  subset := sublevel_subset.trans h.subset
  contDiffAt _ hy := h.contDiffOn.contDiffAt (h.isOpen.mem_nhds hy)
  lipschitzAnchored j hj := by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact h.lipschitzAnchored_zero
    · exact h.lipschitzAnchored j (Finset.mem_Icc.2 ⟨hj0, (Finset.mem_Icc.1 hj).2⟩)

/-- The constants of f.D0qLaB.X are normalized: `L_{f,j} ≥ 1` for `j ∈ [0:q]`. -/
theorem AssumptionD0qLaBX.normalized {x₀ : ℝⁿ} {q : ℕ} (h : AssumptionD0qLaBX f X X₀ x₀ q L B) :
    ∀ j ≤ q, 1 ≤ L j := fun j hj => by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · exact h.one_le_lip_zero
  · exact h.one_le_lip j (Finset.mem_Icc.2 ⟨hj0, hj⟩)

/-- f.D0qLaB.X is f.D1qLaB.X together with (14.2.9) for `j = 0`, with `L_{f,0} ≥ 1`. -/
theorem assumptionD0qLaBX_iff {x₀ : ℝⁿ} {q : ℕ} : AssumptionD0qLaBX f X X₀ x₀ q L B ↔
    AssumptionD1qLaBX f X X₀ x₀ 1 q L B ∧ 1 ≤ L 0 ∧
      IteratedFDerivLipschitzAnchored f 0 (L 0) (sublevel f X x₀) X₀ :=
  ⟨fun h => ⟨h.toAssumptionD1qLaBX, h.one_le_lip_zero, h.lipschitzAnchored_zero⟩,
    fun ⟨h, h1, h0⟩ => ⟨h, h1, h0⟩⟩

section TRq

variable {P : Optimization.TRqParams} {q : ℕ} {ε : ℕ → ℝ} {ϑ : ℝ} {x s : ℕ → ℝⁿ} {Δ : ℕ → ℝ}
  {jk : ℕ → ℕ} {d : ℕ → ℕ → ℝⁿ}

/-- **Lemma 14.2.2** of [cartis2022evaluation], TRq-SC row under f.D1qLaB.X (with the anchor point
`x₀ = x 0`; the remark after (14.2.10)): the decreases of `lemma_14_2_2_trq`. -/
theorem lemma_14_2_2_trq_anchored (h : Chapter12.algorithm_12_2_1_feasible f X P q ε ϑ x s Δ jk d)
    (hf : AssumptionD1qLaBX f X X₀ (x 0) 1 q L B) (hx0 : x 0 ∈ X)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hϑ : Optimization.finMin 1 ε q ≤ ϑ) (hϑ1 : ϑ ≤ 1)
    {k : ℕ} (hk : ∀ i ≤ k, ¬ Chapter12.trqStop f P q ε ϑ x Δ d i) :
    (P.ς * Optimization.trqKappaDelta f P q L ϑ (x 0)) ^ (q + 1) / q ! *
        Optimization.finMin 1 ε q ^ (q + 1) ≤
        (ftaylorSeries ℝ f (x k)).taylorDecrement (jk k) (s k) ∧
      (P.η₁ ≤ Chapter12.trqRho f x s jk k →
        P.η₁ * ((P.ς * Optimization.trqKappaDelta f P q L ϑ (x 0)) ^ (q + 1) / q ! *
          Optimization.finMin 1 ε q ^ (q + 1)) ≤ f (x k) - f (x (k + 1))) :=
  Optimization.IsTRqRun.taylorDecrement_ge_of_anchored h hf.toLipschitzDerivsAnchored
    hf.subset (fun _ hy hfy => ⟨hy, hfy⟩) hx0 hε hϑ hϑ1 hk

/-- **Lemma 14.2.3** of [cartis2022evaluation], TRq-SC row under f.D1qLaB.X (with the anchor point
`x₀ = x 0`): the bound (14.2.13) of `lemma_14_2_3_trq`. -/
theorem lemma_14_2_3_trq_anchored (h : Chapter12.algorithm_12_2_1_feasible f X P q ε ϑ x s Δ jk d)
    (hf : AssumptionD1qLaBX f X X₀ (x 0) 1 q L B) (hx0 : x 0 ∈ X)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hϑ : Optimization.finMin 1 ε q ≤ ϑ) (hϑ1 : ϑ ≤ 1)
    {k : ℕ} (hk : ∀ i < k, ¬ Chapter12.trqStop f P q ε ϑ x Δ d i) :
    (k : ℝ) ≤
      (Optimization.successSet (fun j => P.η₁ ≤ Chapter12.trqRho f x s jk j) k).card *
          (1 + Real.log P.γ₃ / |Real.log P.γ₂|) +
        |Real.log (min (P.γ₁ * ϑ) (Optimization.trqKappaDelta f P q L ϑ (x 0) *
          (P.ς * Optimization.finMin 1 ε q)) / P.Δ₀)| / |Real.log P.γ₂| :=
  Optimization.IsTRqRun.le_succ_count_of_anchored h hf.toLipschitzDerivsAnchored
    hf.subset (fun _ hy hfy => ⟨hy, hfy⟩) hx0 hε hϑ hϑ1 hk

/-- **Theorem 14.2.4** of [cartis2022evaluation], TRq-SC row under f.bB.X and f.D1qLaB.X (with the
anchor point `x₀ = x 0`; the remark after (14.2.10)): the conclusion of `theorem_14_2_4_trq`. -/
theorem theorem_14_2_4_trq_anchored {flow : ℝ} (hb : AssumptionBbX f X flow)
    (hf : AssumptionD1qLaBX f X X₀ (x 0) 1 q L B) (hx0 : x 0 ∈ X)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hϑ : Optimization.finMin 1 ε q ≤ ϑ) (hϑ1 : ϑ ≤ 1)
    (h : Chapter12.algorithm_12_2_1_feasible f X P q ε ϑ x s Δ jk d) :
    ∃ kε, Optimization.IsFirstHit (Chapter12.trqStop f P q ε ϑ x Δ d) kε ∧ x kε ∈ X ∧
      min (Δ kε) ϑ ∈ Ioc 0 1 ∧
      Optimization.IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) {e | x kε + e ∈ X} q ε
        (fun _ => min (Δ kε) ϑ) ∧
      (Optimization.funEvalCount kε : ℝ) ≤
        Optimization.kappaATRq f P q L ϑ (x 0) * (f (x 0) - flow) /
            Optimization.finMin 1 ε q ^ (q + 1) +
          Optimization.kappaBTRq P * |Real.log (Optimization.finMin 1 ε q)| +
          Optimization.kappaCTRq f P q L ϑ (x 0) ∧
      (Optimization.derivEvalCount (fun k => P.η₁ ≤ Chapter12.trqRho f x s jk k) kε : ℝ) ≤
        Optimization.kappaSTRq f P q L ϑ (x 0) * (f (x 0) - flow) /
          Optimization.finMin 1 ε q ^ (q + 1) + 1 :=
  Optimization.IsTRqRun.complexity hb hf.toLipschitzDerivsAnchored hf.subset
    (fun _ hy hfy => ⟨hy, hfy⟩) hx0 hε hϑ hϑ1 h

end TRq

section ARqp

variable {P : Optimization.ARqpParams} {p q : ℕ} {ε δ₀ : ℕ → ℝ} {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ}
  {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → ℝⁿ}

/-- **Lemma 14.2.2** of [cartis2022evaluation], ARqp-SC row under f.D1pLaB.X (with the anchor
point `x₀ = x 0`; the remark after (14.2.10)): the decreases of `lemma_14_2_2_arqp`, in either
radii mode `u`. -/
theorem lemma_14_2_2_arqp_anchored (hf : AssumptionD1qLaBX f X X₀ (x 0) 1 p L B) (hq : 1 ≤ q)
    (hqp : q ≤ p) (hθς : P.θ < P.ς) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (h : Chapter12.algorithm_12_2_2_feasible f X P p q ε δ₀ x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ Optimization.arqpStop f P p q ε x s σ δ d i)
    (hs : P.η₁ ≤ Optimization.arqpRho f p x s σ k)
    (hk1 : ¬ Optimization.arqpStop₁ P q ε (Optimization.arqpData f p x σ) δ d (k + 1))
    {u : Prop} [Decidable u] (hrad : (u → ∀ j ∈ Finset.Icc 1 q, δ (k + 1) j = 1) ∧
      (¬ u → 1 ≤ ‖s k‖ ∨ ∀ j ∈ Finset.Icc 1 q,
        Optimization.arqpKappaDelta P (Optimization.finMax 1 L p)
          (Optimization.arSigmaMax P.toARParams (L p)) * ε j ≤ δ (k + 1) j)) :
    Optimization.arqpKappaDmOf u P L p q *
        Optimization.finMin 1 (fun j => ε j ^ Optimization.arqpPiOf u p j) q ≤
        (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k) ∧
      P.η₁ * (Optimization.arqpKappaDmOf u P L p q *
        Optimization.finMin 1 (fun j => ε j ^ Optimization.arqpPiOf u p j) q) ≤
        f (x k) - f (x (k + 1)) :=
  have hT := hf.toAnchored.toTop (hq.trans hqp)
  Optimization.IsARqpRun.decrease hT.toLipschitzDerivsAnchored hT.one_le hf.subset
    (fun _ hy hfy => ⟨hy, hfy⟩) hq hqp hθς hε h hk hs hk1 hrad

/-- **Lemma 14.2.3** of [cartis2022evaluation], ARqp-SC row under f.D1pLaB.X (with the anchor
point `x₀ = x 0`): the bound (14.2.13) of `lemma_14_2_3`. -/
theorem lemma_14_2_3_anchored (hf : AssumptionD1qLaBX f X X₀ (x 0) 1 p L B) (hp : 1 ≤ p)
    (h : Chapter12.algorithm_12_2_2_feasible f X P p q ε δ₀ x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i < k, ¬ Optimization.arqpStop f P p q ε x s σ δ d i) :
    (k : ℝ) ≤ (Optimization.successSet (fun j => P.η₁ ≤ Optimization.arqpRho f p x s σ j) k).card *
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
      Real.log (Optimization.arSigmaMax P.toARParams (L p) / P.σ₀) / Real.log P.γ₂ :=
  have hT := hf.toAnchored.toTop hp
  h.toIsARRun.le_succ_count hk
    (Optimization.IsARqpRun.sigma_le_of_anchored hT.toLipschitzDerivsAnchored
    hf.subset (fun _ hy hfy => ⟨hy, hfy⟩) h k hk).2

/-- **Theorem 14.2.4** of [cartis2022evaluation], ARqp-SC row under f.bB.X and f.D1pLaB.X (with
the anchor point `x₀ = x 0`; the remark after (14.2.10)): the conclusion of `theorem_14_2_4_arqp`,
in either radii mode `u`. -/
theorem theorem_14_2_4_arqp_anchored {flow : ℝ} (hb : AssumptionBbX f X flow)
    (hf : AssumptionD1qLaBX f X X₀ (x 0) 1 p L B) (hq : 1 ≤ q) (hqp : q ≤ p)
    (hσmin : 0 < P.σmin) (hθς : P.θ < P.ς) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1)
    (h : Chapter12.algorithm_12_2_2_feasible f X P p q ε δ₀ x s σ δ δs d dm)
    {u : Prop} [Decidable u]
    (hrad : (u → (∀ j ∈ Finset.Icc 1 q, δ₀ j = 1) ∧
        ∀ k, (∀ i ≤ k, ¬ Optimization.arqpStop f P p q ε x s σ δ d i) →
          ∀ j ∈ Finset.Icc 1 q, δs k j = 1) ∧
      (¬ u → ∀ k, (∀ i ≤ k, ¬ Optimization.arqpStop f P p q ε x s σ δ d i) → ‖s k‖ < 1 →
        ∀ j ∈ Finset.Icc 1 q,
          Optimization.arqpKappaDelta P (Optimization.finMax 1 L p) (σ k) * ε j ≤ δs k j)) :
    ∃ kε, Optimization.IsFirstHit (Optimization.arqpStop f P p q ε x s σ δ d) kε ∧ x kε ∈ X ∧
      (∃ δε : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, δε j ∈ Ioc 0 1) ∧
        Optimization.IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) {e | x kε + e ∈ X} q ε δε) ∧
      (Optimization.funEvalCount kε : ℝ) ≤ Optimization.kappaAARqpOf u P L p q * (f (x 0) - flow) /
        Optimization.finMin 1 (fun j => ε j ^ Optimization.arqpPiOf u p j) q +
          Optimization.kappaCARqp P L p ∧
      (Optimization.derivEvalCount (fun k => P.η₁ ≤ Optimization.arqpRho f p x s σ k) kε : ℝ) ≤
        Optimization.kappaSARqpOf u P L p q * (f (x 0) - flow) /
          Optimization.finMin 1 (fun j => ε j ^ Optimization.arqpPiOf u p j) q + 2 :=
  have hT := hf.toAnchored.toTop (hq.trans hqp)
  Optimization.IsARqpRun.complexity hb hT.toLipschitzDerivsAnchored hT.one_le
    hT.jet hf.subset
    (fun _ hy hfy => ⟨hy, hfy⟩) hq hqp hσmin hθς hε hδ₀ h hrad

end ARqp

end Anchored

/-! ### The dynamic-accuracy algorithms with simple constraints

The TRqIDA-SC, TRqEDA-SC, ARqpIDA-SC and ARqpEDA-SC rows of Lemmas 14.2.2–14.2.3 and
Theorem 14.2.4 are instances of the library's analysis of the runs with a feasible set
(`Optimization.IsTRqIDARun`, …, `Optimization.IsARqpEDARun`; `X = univ` gives the algorithms of
Chapter 13) under `LipschitzDerivsAnchored`. Each row `N` is stated twice: `N` under f.D0qL
(f.D0pL) on an open convex `C ⊇ X` (`Chapter13.AssumptionD0qLOn`, anchors `A = C`), and
`N_anchored` under the book's f.D0qLaB.X (f.D0pLaB.X) with the starting point as anchor
(`AssumptionD0qLaBX`, anchors `𝓛_f(x₀)`).
For the IDA algorithms, which have no termination rule, "before termination" reads
"before the first iterate that is approximately optimal on `X`"; for the regularization
algorithms the radius policy is the radii control in either mode
(`Optimization.ARqpDARadiiControl u`): unit radii `δ = 1` (`u`), achievable for `X = ℝⁿ` with
`q ≤ 2` or for `q = 1` with `X` convex, or the (12.2.51)-type bounds at every order (`¬ u`),
available in every case; the radii control of Theorem 13.1.19 (`Optimization.RadiiControl`) is the
mode `u = (q ≤ 2)`. -/

section TRqIDASC

open Chapter13 Optimization

variable {f : ℝⁿ → ℝ} {X C A X₀ : Set ℝⁿ} {κg : ℕ → ℝ} {P : TRqIDAParams} {ε : ℕ → ℝ} {x₀ : ℝⁿ}
  {x : ℕ → ℝⁿ} {Δ : ℕ → ℝ} {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ}
  {dd : ℕ → ℕ → ℝⁿ} {jk : ℕ → ℕ} {s : ℕ → ℝⁿ} {acc : ℕ → Prop} {L B : ℕ → ℝ} {κΔ : ℝ}


/-- **Lemma 14.2.2** of [cartis2022evaluation], TRqIDA-SC row (Lemma 13.1.5 with a feasible set):
for a TRqIDA-SC run (`Optimization.IsTRqIDARun`) under f.D0qL on an open convex
`C ⊇ X` and an admissible `κ_Δ` (`Optimization.IsTRKappaDelta`, `κ_δ = κ_Δ/2`), every successful
iteration `k` (`k ∈ 𝒯`, `ρ_k ≥ η₁`) decreases `f` by at least
`η₁ (ς κ_δ)^{q+1}/(2 q!) ε_min^{q+1}` (`π_j = q + 1`, as for TRq-SC). -/
theorem lemma_14_2_2_trqida (hf : AssumptionD0qLOn f C P.q L) (hXC : X ⊆ C)
    (hrun : IsTRqIDARun f X κg P ε x₀ x Δ h D dd jk s acc)
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ) {k : ℕ} (hk : ¬ acc k)
    (hρ : P.η₁ ≤ trqRatio f D x s jk k) :
    P.η₁ * (P.ς * (κΔ / 2)) ^ (P.q + 1) / (2 * P.q !) * epsMin P.q ε ^ (P.q + 1) ≤
      f (x k) - f (x (k + 1)) :=
  (IsTRqIDARun.decrease_ge hf.toLipschitzDerivsAnchored hf.one_le hXC (fun _ hy _ => hXC hy) hrun
    hκΔ hk).2 hρ

/-- **Lemma 14.2.2** of [cartis2022evaluation], TRqIDA-SC row under f.D0qLaB.X (with the anchor
point `x₀`, the starting point; the remark after (14.2.10)): the conclusion of
`lemma_14_2_2_trqida`. -/
theorem lemma_14_2_2_trqida_anchored (hf : AssumptionD0qLaBX f X X₀ x₀ P.q L B)
    (hrun : IsTRqIDARun f X κg P ε x₀ x Δ h D dd jk s acc)
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ) {k : ℕ} (hk : ¬ acc k)
    (hρ : P.η₁ ≤ trqRatio f D x s jk k) :
    P.η₁ * (P.ς * (κΔ / 2)) ^ (P.q + 1) / (2 * P.q !) * epsMin P.q ε ^ (P.q + 1) ≤
      f (x k) - f (x (k + 1)) :=
  (IsTRqIDARun.decrease_ge hf.lipschitzDerivsAnchored hf.normalized hf.subset
    (fun _ hy hfy => ⟨hy, hfy⟩) hrun hκΔ hk).2 hρ


/-- **Lemma 14.2.3** of [cartis2022evaluation], TRqIDA-SC row (Lemma 13.1.1 with the radius bound
of Lemma 13.1.4, and the count of accuracy-improving iterations of Theorem 13.1.8): for a
TRqIDA-SC run under f.D0qL on an open convex `C ⊇ X` and an admissible `κ_Δ`, every iteration `k`
up to the first iterate that is approximately optimal on `X` satisfies
`k ≤ κ_uns |𝒮_k| + κ_unc` (14.2.13), with `𝒮_k` the successful iterations in `[0, k]`,
`κ_uns = 1 + log γ₃/|log γ₂|` and `κ_unc = |log(ς κ_δ ε_min/Δ₀)|/|log γ₂| + N_𝒜`, where
`N_𝒜 = q(q+1)/|log γ_h| |log ε_min| + |log(κ_acc/κ_h)|/|log γ_h| + 1` bounds the number of
accuracy-improving iterations. -/
theorem lemma_14_2_3_trqida (hf : AssumptionD0qLOn f C P.q L) (hXC : X ⊆ C)
    (hrun : IsTRqIDARun f X κg P ε x₀ x Δ h D dd jk s acc)
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ) {k : ℕ}
    (hk : ∀ j < k, ¬ trqIDATest f X P ε x Δ j) :
    (k : ℝ) ≤ (successSet (fun i => ¬ acc i ∧ P.η₁ ≤ trqRatio f D x s jk i) k).card *
        (1 + Real.log P.γ₃ / |Real.log P.γ₂|) +
      (|Real.log (P.ς * (κΔ / 2) * epsMin P.q ε / P.Δ₀)| / |Real.log P.γ₂| +
        (P.q * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (trKappaAcc P κΔ (lipMax L P.q + ordMax P.q κg * P.κh) (ordMax P.q κg) /
            P.κh)| / |Real.log P.γh| + 1)) :=
  IsTRqIDARun.le_card_succ hf.toLipschitzDerivsAnchored hf.one_le hXC (fun _ hy _ => hXC hy) hrun
      hκΔ hk

/-- **Lemma 14.2.3** of [cartis2022evaluation], TRqIDA-SC row under f.D0qLaB.X (with the anchor
point `x₀`, the starting point; the remark after (14.2.10)): the conclusion of
`lemma_14_2_3_trqida`. -/
theorem lemma_14_2_3_trqida_anchored (hf : AssumptionD0qLaBX f X X₀ x₀ P.q L B)
    (hrun : IsTRqIDARun f X κg P ε x₀ x Δ h D dd jk s acc)
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ) {k : ℕ}
    (hk : ∀ j < k, ¬ trqIDATest f X P ε x Δ j) :
    (k : ℝ) ≤ (successSet (fun i => ¬ acc i ∧ P.η₁ ≤ trqRatio f D x s jk i) k).card *
        (1 + Real.log P.γ₃ / |Real.log P.γ₂|) +
      (|Real.log (P.ς * (κΔ / 2) * epsMin P.q ε / P.Δ₀)| / |Real.log P.γ₂| +
        (P.q * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (trKappaAcc P κΔ (lipMax L P.q + ordMax P.q κg * P.κh) (ordMax P.q κg) /
            P.κh)| / |Real.log P.γh| + 1)) :=
  IsTRqIDARun.le_card_succ hf.lipschitzDerivsAnchored hf.normalized hf.subset
      (fun _ hy hfy => ⟨hy, hfy⟩) hrun hκΔ hk


/-- **Theorem 14.2.4** of [cartis2022evaluation], TRqIDA-SC row (Theorem 13.1.8 with a feasible
set): under f.bB.X, f.D0qL on an open convex `C ⊇ X` and for an admissible `κ_Δ`, every
TRqIDA-SC run has a first iterate `x_{k_ε} ∈ X` that is an `(ε, δ_ε)`-approximate `q`-th order
minimizer on `X` (`Optimization.trqIDATest`, `δ_ε = min(Δ_{k_ε}, ϑ) ∈ (0, 1]`), before which at
most the numbers of function and derivative evaluations of Theorem 13.1.8 are made
(`O(max_j ε_j^{-(q+1)})`). -/
theorem theorem_14_2_4_trqida (hf : AssumptionD0qLOn f C P.q L) (hXC : X ⊆ C) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : IsTRqIDARun f X κg P ε x₀ x Δ h D dd jk s acc)
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ) :
    ∃ kε, IsFirstHit (trqIDATest f X P ε x Δ) kε ∧ x kε ∈ X ∧ 0 < trqDARadius P Δ kε ∧
      trqDARadius P Δ kε ≤ 1 ∧
      (derivEvalCount (fun i => ¬ acc i) kε : ℝ) ≤
        trKappaS P κΔ * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * (f x₀ - flow) /
            epsMin P.q ε ^ (P.q + 1) +
          1 / |Real.log P.γ₂| * |Real.log (epsMin P.q ε)| +
          (|Real.log (P.ς * (κΔ / 2) / P.Δ₀)| / |Real.log P.γ₂| + 1) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ trqRatio f D x s jk i)) kε : ℝ) ≤
        trKappaS P κΔ * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * (f x₀ - flow) /
            epsMin P.q ε ^ (P.q + 1) +
          P.q * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (trKappaAcc P κΔ (lipMax L P.q + ordMax P.q κg * P.κh) (ordMax P.q κg) /
            P.κh)| / |Real.log P.γh| + 2 := by
  obtain ⟨kε, h1, h2, h3, h4, h5⟩ := IsTRqIDARun.complexity hf.toLipschitzDerivsAnchored
      hf.one_le hXC (fun _ hy _ => hXC hy) hb hrun hκΔ
  exact ⟨kε, h1, hrun.mem kε, h2, h3, h4, h5⟩

/-- **Theorem 14.2.4** of [cartis2022evaluation], TRqIDA-SC row under f.D0qLaB.X (with the anchor
point `x₀`, the starting point; the remark after (14.2.10)): the conclusion of
`theorem_14_2_4_trqida`. -/
theorem theorem_14_2_4_trqida_anchored (hf : AssumptionD0qLaBX f X X₀ x₀ P.q L B) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : IsTRqIDARun f X κg P ε x₀ x Δ h D dd jk s acc)
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ) :
    ∃ kε, IsFirstHit (trqIDATest f X P ε x Δ) kε ∧ x kε ∈ X ∧ 0 < trqDARadius P Δ kε ∧
      trqDARadius P Δ kε ≤ 1 ∧
      (derivEvalCount (fun i => ¬ acc i) kε : ℝ) ≤
        trKappaS P κΔ * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * (f x₀ - flow) /
            epsMin P.q ε ^ (P.q + 1) +
          1 / |Real.log P.γ₂| * |Real.log (epsMin P.q ε)| +
          (|Real.log (P.ς * (κΔ / 2) / P.Δ₀)| / |Real.log P.γ₂| + 1) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ trqRatio f D x s jk i)) kε : ℝ) ≤
        trKappaS P κΔ * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * (f x₀ - flow) /
            epsMin P.q ε ^ (P.q + 1) +
          P.q * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (trKappaAcc P κΔ (lipMax L P.q + ordMax P.q κg * P.κh) (ordMax P.q κg) /
            P.κh)| / |Real.log P.γh| + 2 := by
  obtain ⟨kε, h1, h2, h3, h4, h5⟩ := IsTRqIDARun.complexity hf.lipschitzDerivsAnchored
      hf.normalized hf.subset (fun _ hy hfy => ⟨hy, hfy⟩) hb hrun hκΔ
  exact ⟨kε, h1, hrun.mem kε, h2, h3, h4, h5⟩

end TRqIDASC

section TRqEDASC

open Chapter13 Optimization

variable {f : ℝⁿ → ℝ} {X C A X₀ : Set ℝⁿ} {P : TRqIDAParams} {ε : ℕ → ℝ} {x₀ : ℝⁿ} {x : ℕ → ℝⁿ}
  {Δ : ℕ → ℝ} {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ} {dd : ℕ → ℕ → ℝⁿ}
  {jk : ℕ → ℕ} {s : ℕ → ℝⁿ} {acc : ℕ → Prop} {fx fxs h₀ : ℕ → ℝ} {R : ℕ → Prop}
  {L B : ℕ → ℝ} {κΔ : ℝ}


/-- **Lemma 14.2.2** of [cartis2022evaluation], TRqEDA-SC row (Lemma 13.3.2 with a feasible set):
for a TRqEDA-SC run (`Optimization.IsTRqEDARun`) under f.D0qL on an open convex
`C ⊇ X` and an admissible `κ_Δ` (`κ_{∇,max} = 1`, `κ_δ = κ_Δ/2`), every successful iteration `k`
before termination decreases `f` by at least `η₁ (ς κ_δ)^{q+1}/(2 q!) ε_min^{q+1}`. -/
theorem lemma_14_2_2_trqeda (hf : AssumptionD0qLOn f C P.q L) (hXC : X ⊆ C)
    (hrun : IsTRqEDARun f X P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R)
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) 1 κΔ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ edaStopTR P ε D Δ h dd j) (ha : ¬ acc k)
    (hρ : P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement (jk i) (s i)) k) :
    P.η₁ * (P.ς * (κΔ / 2)) ^ (P.q + 1) / (2 * P.q !) * epsMin P.q ε ^ (P.q + 1) ≤
      f (x k) - f (x (k + 1)) :=
  (IsTRqEDARun.decrease_ge hf.toLipschitzDerivsAnchored hf.one_le hXC (fun _ hy _ => hXC hy) hrun
    hκΔ hk ha).2 hρ

/-- **Lemma 14.2.2** of [cartis2022evaluation], TRqEDA-SC row under f.D0qLaB.X (with the anchor
point `x₀`, the starting point; the remark after (14.2.10)): the conclusion of
`lemma_14_2_2_trqeda`. -/
theorem lemma_14_2_2_trqeda_anchored (hf : AssumptionD0qLaBX f X X₀ x₀ P.q L B)
    (hrun : IsTRqEDARun f X P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R)
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) 1 κΔ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ edaStopTR P ε D Δ h dd j) (ha : ¬ acc k)
    (hρ : P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement (jk i) (s i)) k) :
    P.η₁ * (P.ς * (κΔ / 2)) ^ (P.q + 1) / (2 * P.q !) * epsMin P.q ε ^ (P.q + 1) ≤
      f (x k) - f (x (k + 1)) :=
  (IsTRqEDARun.decrease_ge hf.lipschitzDerivsAnchored hf.normalized hf.subset
    (fun _ hy hfy => ⟨hy, hfy⟩) hrun hκΔ hk ha).2 hρ


/-- **Lemma 14.2.3** of [cartis2022evaluation], TRqEDA-SC row (Lemma 13.1.1 with the radius bound
of Lemma 13.1.4 for TRqEDA, and the count of accuracy-improving iterations of Theorem 13.3.4): for
a TRqEDA-SC run under f.D0qL on an open convex `C ⊇ X` and an admissible `κ_Δ`
(`κ_{∇,max} = 1`), every iteration `k` reached (up to and including termination) satisfies
`k ≤ κ_uns |𝒮_k| + κ_unc` (14.2.13) with `κ_uns = 1 + log γ₃/|log γ₂|` and
`κ_unc = |log(ς κ_δ ε_min/Δ₀)|/|log γ₂| + N_𝒜`,
`N_𝒜 = q(q+1)/|log γ_h| |log ε_min| + |log(κ_acc/κ_h)|/|log γ_h| + 1`. -/
theorem lemma_14_2_3_trqeda (hf : AssumptionD0qLOn f C P.q L) (hXC : X ⊆ C)
    (hrun : IsTRqEDARun f X P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R)
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) 1 κΔ) {k : ℕ}
    (hk : ∀ j < k, ¬ edaStopTR P ε D Δ h dd j) :
    (k : ℝ) ≤ (successSet (fun i => ¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement (jk i) (s i)) i) k).card *
        (1 + Real.log P.γ₃ / |Real.log P.γ₂|) +
      (|Real.log (P.ς * (κΔ / 2) * epsMin P.q ε / P.Δ₀)| / |Real.log P.γ₂| +
        (P.q * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (trKappaAcc P κΔ (lipMax L P.q + P.κh) 1 / P.κh)| / |Real.log P.γh| + 1)) :=
  IsTRqEDARun.le_card_succ hf.toLipschitzDerivsAnchored hf.one_le hXC (fun _ hy _ => hXC hy) hrun
      hκΔ hk

/-- **Lemma 14.2.3** of [cartis2022evaluation], TRqEDA-SC row under f.D0qLaB.X (with the anchor
point `x₀`, the starting point; the remark after (14.2.10)): the conclusion of
`lemma_14_2_3_trqeda`. -/
theorem lemma_14_2_3_trqeda_anchored (hf : AssumptionD0qLaBX f X X₀ x₀ P.q L B)
    (hrun : IsTRqEDARun f X P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R)
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) 1 κΔ) {k : ℕ}
    (hk : ∀ j < k, ¬ edaStopTR P ε D Δ h dd j) :
    (k : ℝ) ≤ (successSet (fun i => ¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement (jk i) (s i)) i) k).card *
        (1 + Real.log P.γ₃ / |Real.log P.γ₂|) +
      (|Real.log (P.ς * (κΔ / 2) * epsMin P.q ε / P.Δ₀)| / |Real.log P.γ₂| +
        (P.q * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (trKappaAcc P κΔ (lipMax L P.q + P.κh) 1 / P.κh)| / |Real.log P.γh| + 1)) :=
  IsTRqEDARun.le_card_succ hf.lipschitzDerivsAnchored hf.normalized hf.subset
      (fun _ hy hfy => ⟨hy, hfy⟩) hrun hκΔ hk


/-- **Theorem 14.2.4** of [cartis2022evaluation], TRqEDA-SC row (Theorem 13.3.4 with a feasible
set): under f.bB.X, f.D0qL on an open convex `C ⊇ X` and for an admissible `κ_Δ`
(`κ_{∇,max} = 1`), every TRqEDA-SC run terminates at some `k_ε` with `x_{k_ε} ∈ X` an
`(ε, δ_ε)`-approximate `q`-th order minimizer on `X`, `δ_ε = min(Δ_{k_ε}, ϑ) ∈ (0, 1]`, within
the evaluation bounds of Theorem 13.3.4 (`O(max_j ε_j^{-(q+1)})`). -/
theorem theorem_14_2_4_trqeda (hf : AssumptionD0qLOn f C P.q L) (hXC : X ⊆ C) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : IsTRqEDARun f X P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R)
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) 1 κΔ) :
    ∃ kε, IsFirstHit (edaStopTR P ε D Δ h dd) kε ∧ x kε ∈ X ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) {e | x kε + e ∈ X} P.q ε
        (fun _ => trqDARadius P Δ kε) ∧
      0 < trqDARadius P Δ kε ∧ trqDARadius P Δ kε ≤ 1 ∧
      (edaFunEvalCount acc R kε : ℝ) ≤
        2 * (trKappaS P κΔ * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * (f x₀ - flow) /
            epsMin P.q ε ^ (P.q + 1)) +
          2 * (1 / |Real.log P.γ₂| * |Real.log (epsMin P.q ε)|) +
          2 * (|Real.log (P.ς * (κΔ / 2) / P.Δ₀)| / |Real.log P.γ₂| + 1) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement (jk i) (s i)) i)) kε : ℝ) ≤
        trKappaS P κΔ * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * (f x₀ - flow) /
            epsMin P.q ε ^ (P.q + 1) +
          P.q * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (trKappaAcc P κΔ (lipMax L P.q + P.κh) 1 / P.κh)| /
            |Real.log P.γh| + 2 := by
  obtain ⟨kε, h1, h2, h3, h4, h5, h6⟩ := IsTRqEDARun.complexity hf.toLipschitzDerivsAnchored
      hf.one_le hXC (fun _ hy _ => hXC hy) hb hrun hκΔ
  exact ⟨kε, h1, hrun.mem fun j hj => h1.2 j hj, h2, h3, h4, h5, h6⟩

/-- **Theorem 14.2.4** of [cartis2022evaluation], TRqEDA-SC row under f.D0qLaB.X (with the anchor
point `x₀`, the starting point; the remark after (14.2.10)): the conclusion of
`theorem_14_2_4_trqeda`. -/
theorem theorem_14_2_4_trqeda_anchored (hf : AssumptionD0qLaBX f X X₀ x₀ P.q L B) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : IsTRqEDARun f X P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R)
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) 1 κΔ) :
    ∃ kε, IsFirstHit (edaStopTR P ε D Δ h dd) kε ∧ x kε ∈ X ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) {e | x kε + e ∈ X} P.q ε
        (fun _ => trqDARadius P Δ kε) ∧
      0 < trqDARadius P Δ kε ∧ trqDARadius P Δ kε ≤ 1 ∧
      (edaFunEvalCount acc R kε : ℝ) ≤
        2 * (trKappaS P κΔ * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * (f x₀ - flow) /
            epsMin P.q ε ^ (P.q + 1)) +
          2 * (1 / |Real.log P.γ₂| * |Real.log (epsMin P.q ε)|) +
          2 * (|Real.log (P.ς * (κΔ / 2) / P.Δ₀)| / |Real.log P.γ₂| + 1) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement (jk i) (s i)) i)) kε : ℝ) ≤
        trKappaS P κΔ * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * (f x₀ - flow) /
            epsMin P.q ε ^ (P.q + 1) +
          P.q * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (trKappaAcc P κΔ (lipMax L P.q + P.κh) 1 / P.κh)| /
            |Real.log P.γh| + 2 := by
  obtain ⟨kε, h1, h2, h3, h4, h5, h6⟩ := IsTRqEDARun.complexity hf.lipschitzDerivsAnchored
      hf.normalized hf.subset (fun _ hy hfy => ⟨hy, hfy⟩) hb hrun hκΔ
  exact ⟨kε, h1, hrun.mem fun j hj => h1.2 j hj, h2, h3, h4, h5, h6⟩

end TRqEDASC

section ARqpIDASC

open Chapter13 Optimization

variable {f : ℝⁿ → ℝ} {X C A X₀ : Set ℝⁿ} {κg : ℕ → ℝ} {P : ARqpIDAParams} {ε : ℕ → ℝ} {x₀ : ℝⁿ}
  {x : ℕ → ℝⁿ} {σ : ℕ → ℝ} {δ δ₁ δs : ℕ → ℕ → ℝ} {h : ℕ → ℕ → ℝ}
  {D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ} {dd : ℕ → ℕ → ℝⁿ} {jk : ℕ → ℕ} {s : ℕ → ℝⁿ}
  {acc : ℕ → Prop} {L B : ℕ → ℝ} {u : Prop}


/-- **Lemma 14.2.2** of [cartis2022evaluation], ARqpIDA-SC row (Lemma 13.1.18 with a feasible set):
for an ARqpIDA-SC run (`Optimization.IsARqpIDARun`) under f.D0pL on an open convex `C ⊇ X`
and the radii control at `k`, every successful iteration `k` whose successor `x_{k+1}` is not
approximately optimal on `X` decreases `f` by at least `½ η₁ κ_{Δm} min_j ε_j^{π_j}`, with
`κ_{Δm}` of Lemma 13.1.18 and the radii control in either mode `u`
(`Optimization.ARqpDARadiiControl`): unit radii `δ_{s_k} = 1` (`u`), which Step 2 guarantees for
`X = ℝⁿ` with `q ≤ 2` or for `q = 1` with `X` convex, with `π_j = (p+1)/(p-j+1)`, or the
(12.2.51)-type lower bounds at every order (`¬ u`), available for every `q` and `X`, with
`π_j = j(p+1)/p` (`π_j = Optimization.arPiOf u p j`; the radii control of Theorem 13.1.19,
`Optimization.RadiiControl`, is the mode `u = (q ≤ 2)`). -/
theorem lemma_14_2_2_arqpida (hf : AssumptionD0pLOn f C P.p L) (hXC : X ⊆ C)
    (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) {k : ℕ}
    [Decidable u]
    (hrc : ARqpDARadiiControl u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc k)
    (hk : ¬ acc k)
    (hρ : P.η₁ ≤ arqpIDARatio f P D x s k) (hnot : ¬ arqpIDATest f X P ε x (k + 1)) :
    P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (1 - P.θ)
        (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
          (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
        epsMin P.q (fun j => ε j ^ arPiOf u P.p j) ≤ f (x k) - f (x (k + 1)) :=
  (IsARqpIDARun.decrease_ge hf.toLipschitzDerivsAnchored hf.one_le hXC (fun _ hy _ => hXC hy)
    hrun hrc hk hρ hnot).2

/-- **Lemma 14.2.2** of [cartis2022evaluation], ARqpIDA-SC row under f.D0pLaB.X (with the anchor
point `x₀`, the starting point; the remark after (14.2.10)): the conclusion of
`lemma_14_2_2_arqpida`. -/
theorem lemma_14_2_2_arqpida_anchored (hf : AssumptionD0qLaBX f X X₀ x₀ P.p L B)
    (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) {k : ℕ}
    [Decidable u]
    (hrc : ARqpDARadiiControl u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc k)
    (hk : ¬ acc k)
    (hρ : P.η₁ ≤ arqpIDARatio f P D x s k) (hnot : ¬ arqpIDATest f X P ε x (k + 1)) :
    P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (1 - P.θ)
        (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
          (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
        epsMin P.q (fun j => ε j ^ arPiOf u P.p j) ≤ f (x k) - f (x (k + 1)) :=
  (IsARqpIDARun.decrease_ge hf.lipschitzDerivsAnchored hf.normalized hf.subset
    (fun _ hy hfy => ⟨hy, hfy⟩) hrun hrc hk hρ hnot).2


/-- **Lemma 14.2.3** of [cartis2022evaluation], ARqpIDA-SC row (Lemma 13.1.9 with the bound `σ_max`
of Lemma 13.1.14, and the count of accuracy-improving iterations of Theorem 13.1.19): for an
ARqpIDA-SC run under f.D0pL on an open convex `C ⊇ X` and the radii control, every iteration `k` up
to the first iterate that is approximately optimal on `X` satisfies `k ≤ κ_uns |𝒮_k| + κ_unc`
(14.2.13) with `κ_uns = 1 + |log γ₁|/log γ₂` and `κ_unc = log(σ_max/σ₀)/log γ₂ + N_𝒜`, `N_𝒜 =
p(q+1)/|log γ_h| |log ε_min| + |log(κ_acc/κ_h)|/|log γ_h| + 1`. The radii control
(`Optimization.ARqpDARadiiControl u`) may be in either mode (unit radii, or the (12.2.51)-type lower
bounds at every order). -/
theorem lemma_14_2_3_arqpida (hf : AssumptionD0pLOn f C P.p L) (hXC : X ⊆ C)
    (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i) {k : ℕ}
    (hk : ∀ j < k, ¬ arqpIDATest f X P ε x j) :
    (k : ℝ) ≤ (successSet (fun i => ¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i) k).card *
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
      (Real.log (arqpIDASigmaMax P (L P.p) (ordMax P.p κg) / P.σ₀) / Real.log P.γ₂ +
        (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| /
            |Real.log P.γh| + 1)) :=
  IsARqpIDARun.le_card_succ hf.toLipschitzDerivsAnchored hf.one_le hXC (fun _ hy _ => hXC hy)
      hrun hrc hk

/-- **Lemma 14.2.3** of [cartis2022evaluation], ARqpIDA-SC row under f.D0pLaB.X (with the anchor
point `x₀`, the starting point; the remark after (14.2.10)): the conclusion of
`lemma_14_2_3_arqpida`. -/
theorem lemma_14_2_3_arqpida_anchored (hf : AssumptionD0qLaBX f X X₀ x₀ P.p L B)
    (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i) {k : ℕ}
    (hk : ∀ j < k, ¬ arqpIDATest f X P ε x j) :
    (k : ℝ) ≤ (successSet (fun i => ¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i) k).card *
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
      (Real.log (arqpIDASigmaMax P (L P.p) (ordMax P.p κg) / P.σ₀) / Real.log P.γ₂ +
        (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| /
            |Real.log P.γh| + 1)) :=
  IsARqpIDARun.le_card_succ hf.lipschitzDerivsAnchored hf.normalized hf.subset
      (fun _ hy hfy => ⟨hy, hfy⟩) hrun hrc hk


/-- **Theorem 14.2.4** of [cartis2022evaluation], ARqpIDA-SC row (Theorem 13.1.19 with a feasible
set): under f.bB.X, f.D0pL on an open convex `C ⊇ X` and the radii control at every iteration, every
ARqpIDA-SC run reaches a first iterate `x_{k_ε} ∈ X` that is an `(ε, δ_ε)`-approximate `q`-th order
minimizer on `X` for some radii `δ_ε ∈ (0, 1]^q` (`Optimization.arqpIDATest`), before which at most
`(1 + |log γ₁|/log γ₂) (f(x₀) - f_low)/c + κ^C` function evaluations and `(f(x₀) - f_low)/c + κ^E
|log ε_min| + κ^F + 3` derivative estimates are made, where `c = ½ η₁ κ_{Δm} min_j ε_j^{π_j}` is the
decrease of Lemma 14.2.2, and the constants are those of Theorem 13.1.19, with the radii control
in either mode `u` (`Optimization.ARqpDARadiiControl`): unit radii `δ_{s_k} = 1` (`u`), which
Step 2 guarantees for `X = ℝⁿ` with `q ≤ 2` or for `q = 1` with `X` convex, with
`π_j = (p+1)/(p-j+1)`, or the (12.2.51)-type lower bounds at every order (`¬ u`), available for
every `q` and `X`, with `π_j = j(p+1)/p` (`π_j = Optimization.arPiOf u p j`; the radii control of
Theorem 13.1.19, `Optimization.RadiiControl`, is the mode `u = (q ≤ 2)`). -/
theorem theorem_14_2_4_arqpida (hf : AssumptionD0pLOn f C P.p L) (hXC : X ⊆ C) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    [Decidable u]
    (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i) :
    ∃ kε, IsFirstHit (arqpIDATest f X P ε x) kε ∧ x kε ∈ X ∧
      (derivEvalCount (fun i => ¬ acc i) kε : ℝ) ≤
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) * ((f x₀ - flow) /
          (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (1 - P.θ)
            (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
            epsMin P.q (fun j => ε j ^ arPiOf u P.p j))) +
          (Real.log (arqpIDASigmaMax P (L P.p) (ordMax P.p κg) / P.σ₀) / Real.log P.γ₂ + 2 +
            |Real.log P.γ₁| / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i)) kε : ℝ) ≤
        (f x₀ - flow) /
          (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (1 - P.θ)
            (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
            epsMin P.q (fun j => ε j ^ arPiOf u P.p j)) +
          P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| /
            |Real.log P.γh| + 3 :=
  IsARqpIDARun.complexity_of_radiiControl hf.toLipschitzDerivsAnchored hf.one_le hXC
      (fun _ hy _ => hXC hy) hb hrun hrc

/-- **Theorem 14.2.4** of [cartis2022evaluation], ARqpIDA-SC row under f.D0pLaB.X (with the anchor
point `x₀`, the starting point; the remark after (14.2.10)): the conclusion of
`theorem_14_2_4_arqpida`. -/
theorem theorem_14_2_4_arqpida_anchored (hf : AssumptionD0qLaBX f X X₀ x₀ P.p L B) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    [Decidable u]
    (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i) :
    ∃ kε, IsFirstHit (arqpIDATest f X P ε x) kε ∧ x kε ∈ X ∧
      (derivEvalCount (fun i => ¬ acc i) kε : ℝ) ≤
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) * ((f x₀ - flow) /
          (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (1 - P.θ)
            (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
            epsMin P.q (fun j => ε j ^ arPiOf u P.p j))) +
          (Real.log (arqpIDASigmaMax P (L P.p) (ordMax P.p κg) / P.σ₀) / Real.log P.γ₂ + 2 +
            |Real.log P.γ₁| / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i)) kε : ℝ) ≤
        (f x₀ - flow) /
          (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (1 - P.θ)
            (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
            epsMin P.q (fun j => ε j ^ arPiOf u P.p j)) +
          P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| /
            |Real.log P.γh| + 3 :=
  IsARqpIDARun.complexity_of_radiiControl hf.lipschitzDerivsAnchored hf.normalized hf.subset
      (fun _ hy hfy => ⟨hy, hfy⟩) hb hrun
    hrc

/-- **Theorem 14.2.4** of [cartis2022evaluation], ARqpIDA-SC row on `X = ℝⁿ` with `q ≤ 2`, in
either mode of the radii control (a strengthening of Theorem 13.1.19 (1), which assumes unit
radii): under f.bB and f.D0pL, every
ARqpIDA run on `ℝⁿ` with `q ≤ 2` whose radii satisfy `Optimization.ARqpDARadiiControl u` for
*some* mode `u` (in particular the lower-bound mode `u = False`) satisfies the bounds of the
unit-radii mode, of order `max_j ε_j^{-(p+1)/(p-j+1)}`: a failure of the criterion
`Optimization.arqpIDATest` (approximate optimality for some radii in `(0, 1]^q`) is a failure at
unit radii, and for `q ≤ 2` the bound (13.1.57) on the model transfers to unit radii
(`Optimization.IsARqpIDARun.decrease_ge_unit`). Hence
the mode-`False` bound of `theorem_14_2_4_arqpida`, of order `ε^{-2(p+1)/p}`, is not sharp for
`q = 2 < p` on `ℝⁿ` (it exceeds `ε^{-(p+1)/(p-1)}`). -/
theorem theorem_14_2_4_arqpida_le_two (hf : AssumptionD0pLOn f univ P.p L) {flow : ℝ}
    (hb : ∀ y, flow ≤ f y) (hq2 : P.q ≤ 2)
    (hrun : IsARqpIDARun f univ κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i) :
    ∃ kε, IsFirstHit (arqpIDATest f univ P ε x) kε ∧
      (derivEvalCount (fun i => ¬ acc i) kε : ℝ) ≤
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) * ((f x₀ - flow) /
          (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf True P.q P.p (1 - P.θ)
            (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
            epsMin P.q (fun j => ε j ^ arPiOf True P.p j))) +
          (Real.log (arqpIDASigmaMax P (L P.p) (ordMax P.p κg) / P.σ₀) / Real.log P.γ₂ + 2 +
            |Real.log P.γ₁| / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i)) kε : ℝ) ≤
        (f x₀ - flow) /
          (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf True P.q P.p (1 - P.θ)
            (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
            epsMin P.q (fun j => ε j ^ arPiOf True P.p j)) +
          P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| /
            |Real.log P.γh| + 3 := by
  have hLb := hrun.one_le_Lbar hf.one_le
  have hA := one_le_arConstA (hf.one_le _ le_rfl) hrun.kappaMax_nonneg (P := P) (L := L)
  have hC := arStepConstOf_pos (u := True) (q := P.q) (p := P.p) (sub_pos.2 P.θ_lt_one)
    (zero_lt_one.trans_le hA) (arKappaDelta1_pos (Lb := lipMax L P.p + ordMax P.p κg * P.κh)
      (σ := arqpIDASigmaMax P (L P.p) (ordMax P.p κg)) (P := P) (by linarith))
  have hm : 0 < epsMin P.q (fun j => ε j ^ arPiOf True P.p j) :=
    Optimization.epsMin_pos P.one_le_q fun j hj => Real.rpow_pos_of_pos (hrun.eps_mem j hj).1 _
  have hc : 0 < P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf True P.q P.p (1 - P.θ)
      (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
        (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
      epsMin P.q (fun j => ε j ^ arPiOf True P.p j) := by
    have := P.η₁_pos; have := P.σmin_pos; positivity
  obtain ⟨kε, hk, h1, h2⟩ := IsARqpIDARun.complexity hf.toLipschitzDerivsAnchored hf.one_le
      subset_rfl
    (fun _ hy _ => hy) (fun y _ => hb y) hrun hrc hc fun k hk hρ hnot =>
      IsARqpIDARun.decrease_ge_unit hf.toLipschitzDerivsAnchored hf.one_le hq2 hrun hk hρ hnot
  exact ⟨kε, hk, h1, h2⟩

end ARqpIDASC

section ARqpEDASC

open Chapter13 Optimization

variable {f : ℝⁿ → ℝ} {X C A X₀ : Set ℝⁿ} {P : ARqpIDAParams} {ε : ℕ → ℝ} {x₀ : ℝⁿ} {x : ℕ → ℝⁿ}
  {σ : ℕ → ℝ} {δ δ₁ δs : ℕ → ℕ → ℝ} {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ}
  {dd : ℕ → ℕ → ℝⁿ} {jk : ℕ → ℕ} {s : ℕ → ℝⁿ} {acc : ℕ → Prop} {fx fxs h₀ : ℕ → ℝ}
  {R : ℕ → Prop} {L B : ℕ → ℝ} {u : Prop}


/-- **Lemma 14.2.2** of [cartis2022evaluation], ARqpEDA-SC row (Lemma 13.3.7 with a feasible set):
for an ARqpEDA-SC run (`Optimization.IsARqpEDARun`) under f.D0pL on an open convex `C ⊇
X`, the radii control at `k` and `θ < ς/2`, every successful iteration `k` before termination with
`‖s_k‖ ≥ 1` or such that Step 1 at `k + 1` does not pass with unchanged radii decreases `f` by at
least `½ η₁ κ'_{Δm} min_j ε_j^{π_j}` (`κ'_{Δm}` of Lemma 13.3.7), with the radii control
in either mode `u` (`Optimization.ARqpDARadiiControl`): unit radii `δ_{s_k} = 1` (`u`), which
Step 2 guarantees for `X = ℝⁿ` with `q ≤ 2` or for `q = 1` with `X` convex, with
`π_j = (p+1)/(p-j+1)`, or the (12.2.51)-type lower bounds at every order (`¬ u`), available for
every `q` and `X`, with `π_j = j(p+1)/p` (`π_j = Optimization.arPiOf u p j`; the radii control of
Theorem 13.1.19, `Optimization.RadiiControl`, is the mode `u = (q ≤ 2)`). -/
theorem lemma_14_2_2_arqpeda (hf : AssumptionD0pLOn f C P.p L) (hXC : X ⊆ C)
    (hrun : IsARqpEDARun f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    {k : ℕ} [Decidable u] (hrc : ARqpDARadiiControl u P ε (lipMax L P.p + P.κh) σ δs s acc k)
    (hθ : P.θ < P.ς / 2)
    (hk : ∀ j ≤ k, ¬ edaStopAR P ε D δ₁ h dd j) (ha : ¬ acc k)
    (hρ : P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) k)
    (hgood : 1 ≤ ‖s k‖ ∨ ¬ edaPassUnchanged P ε D δ δ₁ dd (k + 1)) :
    P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (P.ς / 2 - P.θ)
        (arEDAConstA P L) (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1))) /
        2 * epsMin P.q (fun j => ε j ^ arPiOf u P.p j) ≤ f (x k) - f (x (k + 1)) :=
  (IsARqpEDARun.decrease_ge hf.toLipschitzDerivsAnchored hf.one_le hXC (fun _ hy _ => hXC hy)
    hrun hrc hθ hk ha hρ hgood).2

/-- **Lemma 14.2.2** of [cartis2022evaluation], ARqpEDA-SC row under f.D0pLaB.X (with the anchor
point `x₀`, the starting point; the remark after (14.2.10)): the conclusion of
`lemma_14_2_2_arqpeda`. -/
theorem lemma_14_2_2_arqpeda_anchored (hf : AssumptionD0qLaBX f X X₀ x₀ P.p L B)
    (hrun : IsARqpEDARun f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    {k : ℕ} [Decidable u] (hrc : ARqpDARadiiControl u P ε (lipMax L P.p + P.κh) σ δs s acc k)
    (hθ : P.θ < P.ς / 2)
    (hk : ∀ j ≤ k, ¬ edaStopAR P ε D δ₁ h dd j) (ha : ¬ acc k)
    (hρ : P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) k)
    (hgood : 1 ≤ ‖s k‖ ∨ ¬ edaPassUnchanged P ε D δ δ₁ dd (k + 1)) :
    P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (P.ς / 2 - P.θ)
        (arEDAConstA P L) (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1))) /
        2 * epsMin P.q (fun j => ε j ^ arPiOf u P.p j) ≤ f (x k) - f (x (k + 1)) :=
  (IsARqpEDARun.decrease_ge hf.lipschitzDerivsAnchored hf.normalized hf.subset
    (fun _ hy hfy => ⟨hy, hfy⟩) hrun hrc hθ hk ha hρ hgood).2


/-- **Lemma 14.2.3** of [cartis2022evaluation], ARqpEDA-SC row (Lemma 13.1.9 with the bound `σ_max`
of Lemma 13.3.5, and the count of accuracy-improving iterations of Theorem 13.3.8): for an
ARqpEDA-SC run under f.D0pL on an open convex `C ⊇ X` and the radii control, every iteration `k`
reached (up to and including termination) satisfies `k ≤ κ_uns |𝒮_k| + κ_unc` (14.2.13) with `κ_uns
= 1 + |log γ₁|/log γ₂` and `κ_unc = log(σ_max/σ₀)/log γ₂ + N_𝒜`, `N_𝒜 = p(q+1)/|log γ_h| |log ε_min|
+ |log(κ_acc/κ_h)|/|log γ_h| + 1`. The radii control (`Optimization.ARqpDARadiiControl u`) may be in
either mode (unit radii, or the (12.2.51)-type lower bounds at every order). -/
theorem lemma_14_2_3_arqpeda (hf : AssumptionD0pLOn f C P.p L) (hXC : X ⊆ C)
    (hrun : IsARqpEDARun f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + P.κh) σ δs s acc i) {k : ℕ}
    (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) :
    (k : ℝ) ≤ (successSet (fun i => ¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i) k).card *
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
      (Real.log (arqpIDASigmaMax P (L P.p) 1 / P.σ₀) / Real.log P.γ₂ +
        (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
            (arqpIDASigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1) 1 /
            P.κh)| / |Real.log P.γh| + 1)) :=
  IsARqpEDARun.le_card_succ hf.toLipschitzDerivsAnchored hf.one_le hXC (fun _ hy _ => hXC hy)
      hrun hrc hk

/-- **Lemma 14.2.3** of [cartis2022evaluation], ARqpEDA-SC row under f.D0pLaB.X (with the anchor
point `x₀`, the starting point; the remark after (14.2.10)): the conclusion of
`lemma_14_2_3_arqpeda`. -/
theorem lemma_14_2_3_arqpeda_anchored (hf : AssumptionD0qLaBX f X X₀ x₀ P.p L B)
    (hrun : IsARqpEDARun f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + P.κh) σ δs s acc i) {k : ℕ}
    (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) :
    (k : ℝ) ≤ (successSet (fun i => ¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i) k).card *
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
      (Real.log (arqpIDASigmaMax P (L P.p) 1 / P.σ₀) / Real.log P.γ₂ +
        (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
            (arqpIDASigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1) 1 /
            P.κh)| / |Real.log P.γh| + 1)) :=
  IsARqpEDARun.le_card_succ hf.lipschitzDerivsAnchored hf.normalized hf.subset
      (fun _ hy hfy => ⟨hy, hfy⟩) hrun hrc hk


/-- **Theorem 14.2.4** of [cartis2022evaluation], ARqpEDA-SC row (Theorem 13.3.8 with a feasible
set): under f.bB.X, f.D0pL on an open convex `C ⊇ X`, the radii control at every iteration and `θ <
ς/2`, every ARqpEDA-SC run terminates at some `k_ε` with `x_{k_ε} ∈ X` an `(ε,
δ^{(1)}_{k_ε})`-approximate `q`-th order minimizer on `X`, `δ^{(1)}_{k_ε} ∈ (0, 1]^q`, after at most
`2 ((N + M + 1) c_T + log(σ_max/σ₀)/log γ₂)` inexact function evaluations and `N + 2M + 2`
derivative estimates, where `N = (f(x₀) - f_low)/c` with `c = ½ η₁ κ'_{Δm} min_j ε_j^{π_j}` the
decrease of Lemma 14.2.2, `M = p(q+1)/|log γ_h| |log ε_min| + |log(κ_acc/κ_h)|/|log γ_h| + 1` and
`c_T = 1 + |log γ₁|/log γ₂` (as in Theorem 13.3.8), with the radii control in either mode `u`
(`Optimization.ARqpDARadiiControl`): unit radii `δ_{s_k} = 1` (`u`), which Step 2 guarantees for
`X = ℝⁿ` with `q ≤ 2` or for `q = 1` with `X` convex, with `π_j = (p+1)/(p-j+1)`, or the
(12.2.51)-type lower bounds at every order (`¬ u`), available for every `q` and `X`, with
`π_j = j(p+1)/p` (`π_j = Optimization.arPiOf u p j`; the radii control of Theorem 13.1.19,
`Optimization.RadiiControl`, is the mode `u = (q ≤ 2)`). -/
theorem theorem_14_2_4_arqpeda (hf : AssumptionD0pLOn f C P.p L) (hXC : X ⊆ C) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : IsARqpEDARun f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    [Decidable u] (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + P.κh) σ δs s acc i)
    (hθ : P.θ < P.ς / 2) :
    ∃ kε, IsFirstHit (edaStopAR P ε D δ₁ h dd) kε ∧ x kε ∈ X ∧
      (∀ j ∈ Finset.Icc 1 P.q, δ₁ kε j ∈ Set.Ioc 0 1) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) {e | x kε + e ∈ X} P.q ε (δ₁ kε) ∧
      (edaFunEvalCount acc R kε : ℝ) ≤
        2 * (((f x₀ - flow) / (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p
              (P.ς / 2 - P.θ) (arEDAConstA P L)
              (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1))) / 2 *
              epsMin P.q (fun j => ε j ^ arPiOf u P.p j)) +
            (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
              |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
                (arqpIDASigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh)
                  (arqpIDASigmaMax P (L P.p) 1) 1 /
                P.κh)| / |Real.log P.γh| + 1) + 1) *
            (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
          Real.log (arqpIDASigmaMax P (L P.p) 1 / P.σ₀) / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i)) kε : ℝ) ≤
        (f x₀ - flow) / (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p
            (P.ς / 2 - P.θ) (arEDAConstA P L)
            (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1))) / 2 *
            epsMin P.q (fun j => ε j ^ arPiOf u P.p j)) +
          2 * (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
            |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
              (arqpIDASigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1) 1 /
              P.κh)| / |Real.log P.γh| + 1) + 2 :=
  IsARqpEDARun.complexity_of_radiiControl hf.toLipschitzDerivsAnchored hf.one_le hXC
      (fun _ hy _ => hXC hy) hb hrun hrc hθ

/-- **Theorem 14.2.4** of [cartis2022evaluation], ARqpEDA-SC row under f.D0pLaB.X (with the anchor
point `x₀`, the starting point; the remark after (14.2.10)): the conclusion of
`theorem_14_2_4_arqpeda`. -/
theorem theorem_14_2_4_arqpeda_anchored (hf : AssumptionD0qLaBX f X X₀ x₀ P.p L B) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : IsARqpEDARun f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    [Decidable u] (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + P.κh) σ δs s acc i)
    (hθ : P.θ < P.ς / 2) :
    ∃ kε, IsFirstHit (edaStopAR P ε D δ₁ h dd) kε ∧ x kε ∈ X ∧
      (∀ j ∈ Finset.Icc 1 P.q, δ₁ kε j ∈ Set.Ioc 0 1) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) {e | x kε + e ∈ X} P.q ε (δ₁ kε) ∧
      (edaFunEvalCount acc R kε : ℝ) ≤
        2 * (((f x₀ - flow) / (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p
              (P.ς / 2 - P.θ) (arEDAConstA P L)
              (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1))) / 2 *
              epsMin P.q (fun j => ε j ^ arPiOf u P.p j)) +
            (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
              |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
                (arqpIDASigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh)
                  (arqpIDASigmaMax P (L P.p) 1) 1 /
                P.κh)| / |Real.log P.γh| + 1) + 1) *
            (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
          Real.log (arqpIDASigmaMax P (L P.p) 1 / P.σ₀) / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i)) kε : ℝ) ≤
        (f x₀ - flow) / (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p
            (P.ς / 2 - P.θ) (arEDAConstA P L)
            (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1))) / 2 *
            epsMin P.q (fun j => ε j ^ arPiOf u P.p j)) +
          2 * (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
            |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
              (arqpIDASigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1) 1 /
              P.κh)| / |Real.log P.γh| + 1) + 2 :=
  IsARqpEDARun.complexity_of_radiiControl hf.lipschitzDerivsAnchored hf.normalized hf.subset
      (fun _ hy hfy => ⟨hy, hfy⟩) hb hrun
    hrc hθ

end ARqpEDASC

section TRqPrintedFalse

open scoped ContDiff

set_option hygiene false in
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- `‖s‖² = s₁² + s₂²` on `ℝ²`. -/
theorem trqLog_norm_sq (s : ℝ²) : ‖s‖ ^ 2 = (s 0) ^ 2 + (s 1) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp [sq_abs]

/-- The coordinates are continuous. -/
theorem trqLog_continuous_coord (i : Fin 2) : Continuous (fun v : ℝ² => v i) :=
  (EuclideanSpace.proj i : ℝ² →L[ℝ] ℝ).continuous

/-! ### The TRq-SC row `j + 1` of (14.2.12) fails per iteration with uniform constants (`q = 2`) -/

section Decrease

/-- `t ↦ t²/2`. -/
noncomputable def trqSadSq : ℝ → ℝ := fun t => t ^ 2 / 2

/-- `(t²/2)' = t`. -/
theorem iteratedDeriv_trqSadSq_one (t : ℝ) : iteratedDeriv 1 trqSadSq t = t := by
  rw [iteratedDeriv_one]
  unfold trqSadSq
  have := ((hasDerivAt_pow 2 t).div_const 2)
  rw [this.deriv]; ring

/-- `(t²/2)' = t`. -/
theorem deriv_trqSadSq : deriv trqSadSq = fun t => t := by
  funext t
  unfold trqSadSq
  have := ((hasDerivAt_pow 2 t).div_const 2)
  rw [this.deriv]; ring

/-- `(t²/2)'' = 1`. -/
theorem iteratedDeriv_trqSadSq_two (t : ℝ) : iteratedDeriv 2 trqSadSq t = 1 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_trqSadSq, deriv_id'']

/-- `(t²/2)''' = 0`. -/
theorem iteratedDeriv_trqSadSq_three (t : ℝ) : iteratedDeriv 3 trqSadSq t = 0 := by
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, deriv_trqSadSq, deriv_id'']
  simp

/-- `t ↦ t²/2` is smooth. -/
theorem contDiff_trqSadSq : ContDiff ℝ ∞ trqSadSq := by
  unfold trqSadSq; fun_prop

/-- `‖∇ⁿ (w ↦ w_i²/2)(v)‖ ≤ |(t²/2)^{(n)}(v_i)|`. -/
theorem norm_iteratedFDeriv_trqSadSq_comp (i : Fin 2) (n : ℕ) (v : ℝ²) :
    ‖iteratedFDeriv ℝ n (fun w : ℝ² => trqSadSq (w i)) v‖ ≤ |iteratedDeriv n trqSadSq (v i)| :=
  ContDiffAt.norm_iteratedFDeriv_comp_coord_le i
    (contDiff_trqSadSq.contDiffAt.of_le (by exact_mod_cast le_top))


/-- `w ↦ w_i²/2` is smooth. -/
theorem trqSad_contDiff_coordSq (i : Fin 2) : ContDiff ℝ ∞ (fun w : ℝ² => trqSadSq (w i)) :=
  contDiff_trqSadSq.comp (EuclideanSpace.proj i : ℝ² →L[ℝ] ℝ).contDiff

/-- The objective `f_a(x) = x_1²/2 - a x_2²/2` of the example
(`x_1 = v 0`, `x_2 = v 1`). -/
noncomputable def trqSadF (a : ℝ) : ℝ² → ℝ := fun v => trqSadSq (v 0) - a * trqSadSq (v 1)

/-- `f_a` as a difference of coordinate squares. -/
theorem trqSadF_eq (a : ℝ) :
    trqSadF a = (fun w : ℝ² => trqSadSq (w 0)) - a • (fun w : ℝ² => trqSadSq (w 1)) := by
  funext v; simp [trqSadF]

/-- `f_a` is smooth. -/
theorem contDiff_trqSadF (a : ℝ) : ContDiff ℝ ∞ (trqSadF a) := by
  rw [trqSadF_eq]; exact (trqSad_contDiff_coordSq 0).sub ((trqSad_contDiff_coordSq 1).const_smul a)

/-- `f_a` is `C^n` everywhere. -/
theorem contDiffAt_trqSadF (a : ℝ) (n : ℕ) (y : ℝ²) : ContDiffAt ℝ n (trqSadF a) y :=
  ((contDiff_trqSadF a).of_le (by exact_mod_cast le_top : (n : ℕ∞ω) ≤ ∞)).contDiffAt

/-- `‖∇ⁿ f_a(v)‖ ≤ |(t²/2)^{(n)}(v_1)| + a |(t²/2)^{(n)}(v_2)|` for `a ≥ 0`. -/
theorem norm_iteratedFDeriv_trqSadF_le {a : ℝ} (ha : 0 ≤ a) (n : ℕ) (v : ℝ²) :
    ‖iteratedFDeriv ℝ n (trqSadF a) v‖ ≤
      |iteratedDeriv n trqSadSq (v 0)| + a * |iteratedDeriv n trqSadSq (v 1)| := by
  have h0 := ((trqSad_contDiff_coordSq 0).of_le (by exact_mod_cast le_top : (n : ℕ∞ω) ≤
      ∞)).contDiffAt
    (x := v)
  have h1 := ((trqSad_contDiff_coordSq 1).of_le (by exact_mod_cast le_top : (n : ℕ∞ω) ≤
      ∞)).contDiffAt
    (x := v)
  have h1' : ContDiffAt ℝ n (a • fun w : ℝ² => trqSadSq (w 1)) v := h1.const_smul a
  rw [trqSadF_eq, iteratedFDeriv_sub_apply h0 h1', iteratedFDeriv_const_smul_apply h1]
  refine (norm_sub_le _ _).trans (add_le_add (norm_iteratedFDeriv_trqSadSq_comp 0 n v) ?_)
  rw [norm_smul, Real.norm_of_nonneg ha]
  exact mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_trqSadSq_comp 1 n v) ha

/-- `∇² f_a` is constant (`0`-Lipschitz) for `a ≥ 0`. -/
theorem iteratedFDerivLipschitzOn_trqSadF_two {a : ℝ} (ha : 0 ≤ a) (C : Set ℝ²)
    (hC : Convex ℝ C) : IteratedFDerivLipschitzOn (trqSadF a) 2 0 C :=
  iteratedFDerivLipschitzOn_of_norm_le hC
    (fun y _ => contDiffAt_trqSadF a _ y)
    fun x _ => (norm_iteratedFDeriv_trqSadF_le ha 3 x).trans (by
      rw [iteratedDeriv_trqSadSq_three, iteratedDeriv_trqSadSq_three]; simp)

/-- `f_a` is quadratic: `ΔT_2(x, s) = f_a(x) - f_a(x + s)`. -/
theorem taylorDecrement_two_trqSadF {a : ℝ} (ha : 0 ≤ a) (x s : ℝ²) :
    (ftaylorSeries ℝ (trqSadF a) x).taylorDecrement 2 s = trqSadF a x - trqSadF a (x + s) := by
  rw [ftaylorSeries_taylorDecrement_eq]
  have := norm_sub_taylorPolynomial_le_of_lipschitz convex_univ
    (fun y _ => contDiffAt_trqSadF a _ y)
    (iteratedFDerivLipschitzOn_trqSadF_two ha univ convex_univ) (mem_univ x) (mem_univ (x + s))
  simp only [zero_div, zero_mul] at this
  have h := norm_le_zero_iff.1 this
  rw [sub_eq_zero] at h
  rw [h]

/-- The derivative of `f_a`: `s ↦ x_1 s_1 - a x_2 s_2`. -/
theorem hasFDerivAt_trqSadF (a : ℝ) (v : ℝ²) :
    HasFDerivAt (trqSadF a)
      ((v 0) • (EuclideanSpace.proj 0 : ℝ² →L[ℝ] ℝ) - (a * v 1) • EuclideanSpace.proj 1) v := by
  have h1 : HasFDerivAt (fun w : ℝ² => w 1) (EuclideanSpace.proj 1 : ℝ² →L[ℝ] ℝ) v :=
    (EuclideanSpace.proj 1 : ℝ² →L[ℝ] ℝ).hasFDerivAt
  have h0 : HasFDerivAt (fun w : ℝ² => w 0) (EuclideanSpace.proj 0 : ℝ² →L[ℝ] ℝ) v :=
    (EuclideanSpace.proj 0 : ℝ² →L[ℝ] ℝ).hasFDerivAt
  have := ((h0.pow 2).mul_const (1 / 2 : ℝ)).sub (((h1.pow 2).mul_const (1 / 2 : ℝ)).const_mul a)
  convert this using 1
  · funext w; simp only [trqSadF, trqSadSq, Pi.sub_apply]; ring
  · ext s; simp; ring

/-- `ΔT_1(x, s) = -(x_1 s_1 - a x_2 s_2)`. -/
theorem taylorDecrement_one_trqSadF (a : ℝ) (x s : ℝ²) :
    (ftaylorSeries ℝ (trqSadF a) x).taylorDecrement 1 s = -(x 0 * s 0 - a * x 1 * s 1) := by
  rw [FormalMultilinearSeries.taylorDecrement_one_apply]
  change -(iteratedFDeriv ℝ 1 _ x (fun _ => s)) = _
  rw [iteratedFDeriv_one_apply, (hasFDerivAt_trqSadF a x).fderiv]
  simp


/-- The box `[-1, 1]²`. -/
def trqSadX : Set ℝ² := {v | -1 ≤ v 0 ∧ v 0 ≤ 1 ∧ -1 ≤ v 1 ∧ v 1 ≤ 1}

/-- Membership in the box. -/
theorem trqSadX_mem {v : ℝ²} : v ∈ trqSadX ↔ -1 ≤ v 0 ∧ v 0 ≤ 1 ∧ -1 ≤ v 1 ∧ v 1 ≤ 1 := Iff.rfl

/-- The box is closed. -/
theorem isClosed_trqSadX : IsClosed trqSadX := by
  have hc : ∀ a : ℝ, Continuous fun _ : ℝ² => a := fun a => continuous_const
  have h := ((isClosed_le (hc (-1)) (trqLog_continuous_coord 0)).inter
    (isClosed_le (trqLog_continuous_coord 0) (hc 1))).inter
    ((isClosed_le (hc (-1)) (trqLog_continuous_coord 1)).inter
    (isClosed_le (trqLog_continuous_coord 1) (hc 1)))
  convert h using 1
  ext v
  simp only [trqSadX, Set.mem_ofPred_eq, Set.mem_inter_iff]
  tauto

/-- The box lies in the ball of radius `2`. -/
theorem trqSadX_subset_ball : trqSadX ⊆ ball (0 : ℝ²) 2 := by
  intro v hv
  obtain ⟨h0, h2, h3, h4⟩ := hv
  rw [mem_ball_zero_iff]
  have hs := trqLog_norm_sq v
  have : ‖v‖ ^ 2 < 2 ^ 2 := by nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) this

/-- f.D1qLaB.X (`q = 2`) for `f_a` with `a ∈ [0, 1]`, on `X₀` the ball of radius `2`, with the
constants `L_j = B_j = 4` independent of `a` and of the anchor. -/
theorem trqSadF_assumption {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (x₀ : ℝ²) :
    AssumptionD1qLaBX (trqSadF a) trqSadX (ball 0 2) x₀ 1 2 (fun _ => 4) (fun _ => 4) := by
  have hd : ∀ n, ∀ v, ‖iteratedFDeriv ℝ n (trqSadF a) v‖ ≤
      |iteratedDeriv n trqSadSq (v 0)| + a * |iteratedDeriv n trqSadSq (v 1)| :=
    fun n v => norm_iteratedFDeriv_trqSadF_le ha0 n v
  refine AssumptionD1qLaBX.of_lipschitzOn isOpen_ball (convex_ball 0 2) trqSadX_subset_ball
    (fun y _ => (contDiffAt_trqSadF a 2 y).contDiffWithinAt)
    (fun _ _ => by norm_num) (fun _ _ => by norm_num)
    (fun j hj => ?_) (fun j hj x hx => ?_)
  · have hj' : j = 1 ∨ j = 2 := by have := Finset.mem_Icc.1 hj; omega
    refine iteratedFDerivLipschitzOn_of_norm_le (convex_ball 0 2)
      (fun y _ => contDiffAt_trqSadF a _ y) fun x _ => (hd _ x).trans ?_
    rcases hj' with rfl | rfl
    · rw [iteratedDeriv_trqSadSq_two, iteratedDeriv_trqSadSq_two]; norm_num; linarith
    · rw [iteratedDeriv_trqSadSq_three, iteratedDeriv_trqSadSq_three]; norm_num
  · have hj' : j = 1 ∨ j = 2 := by have := Finset.mem_Icc.1 hj; omega
    refine (hd _ x).trans ?_
    rcases hj' with rfl | rfl
    · rw [iteratedDeriv_trqSadSq_one, iteratedDeriv_trqSadSq_one]
      have hx' : ‖x‖ < 2 := mem_ball_zero_iff.1 hx
      have h0 := (EuclideanSpace.abs_apply_le_norm x 0).trans hx'.le
      have h1 := (EuclideanSpace.abs_apply_le_norm x 1).trans hx'.le
      nlinarith [abs_nonneg (x 1)]
    · rw [iteratedDeriv_trqSadSq_two, iteratedDeriv_trqSadSq_two]; norm_num; linarith


/-- The trust-region parameters of the example: `Δ₀ = Δ_max = 1`, `η₁ = 1/4`, `η₂ = 3/4`,
`γ₁ = 1/4`, `γ₂ = 1/2`, `γ₃ = 2`, `ς = 1/2`. -/
noncomputable def trqSadP : Optimization.TRqParams where
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
  ς := 1 / 2
  Δ₀_le_Δmax := le_rfl
  ς_pos := by norm_num
  ς_le_one := by norm_num

/-- The unit vector `e_i` of `ℝ²`. -/
noncomputable def trqSadE (i : Fin 2) : ℝ² := EuclideanSpace.single i 1

@[simp] theorem trqSadE_apply (i j : Fin 2) : trqSadE i j = if j = i then 1 else 0 := by
  simp [trqSadE, PiLp.single_apply]

/-- `‖c e_i‖ = |c|`. -/
theorem norm_smul_trqSadE (c : ℝ) (i : Fin 2) : ‖c • trqSadE i‖ = |c| := by
  rw [norm_smul]; simp [trqSadE]

/-- Unfolding `f_a`. -/
theorem trqSadF_apply (a : ℝ) (v : ℝ²) : trqSadF a v = (v 0) ^ 2 / 2 - a * ((v 1) ^ 2 / 2) := rfl

/-- At `p = b e_0`, `ΔT_1(d) = -b d_0`. -/
theorem trqSad_ΔT1_p (a b : ℝ) (d : ℝ²) :
    (ftaylorSeries ℝ (trqSadF a) (b • trqSadE 0)).taylorDecrement 1 d = -(b * d 0) := by
  rw [taylorDecrement_one_trqSadF]; simp

/-- At `0`, `ΔT_1 = 0`. -/
theorem trqSad_ΔT1_zero (a : ℝ) (d : ℝ²) :
    (ftaylorSeries ℝ (trqSadF a) 0).taylorDecrement 1 d = 0 := by
  rw [taylorDecrement_one_trqSadF]; simp

/-- At `0`, `ΔT_2(d) = -d_0²/2 + a d_1²/2`. -/
theorem trqSad_ΔT2_zero {a : ℝ} (ha : 0 ≤ a) (d : ℝ²) :
    (ftaylorSeries ℝ (trqSadF a) 0).taylorDecrement 2 d = -((d 0) ^ 2 / 2) + a * ((d 1) ^ 2 / 2)
        := by
  rw [taylorDecrement_two_trqSadF ha, zero_add, trqSadF_apply, trqSadF_apply]; simp; ring


section Prefix

variable {a b Δ : ℝ} {ε : ℕ → ℝ}

/-- `b e_1 ∈ X` for `b ∈ [0, 1]` (`e_1 = trqSadE 0`, the first unit vector). -/
theorem trqSad_smul_e0_mem {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) : b • trqSadE 0 ∈ trqSadX := by
  simp only [trqSadX_mem, PiLp.smul_apply, trqSadE_apply]
  norm_num
  exact ⟨by linarith, hb1⟩

/-- `b e_1 - Δ e_1 ∈ X` for `b, Δ ∈ [0, 1]`. -/
theorem trqSadE0_mem {b Δ : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1) :
    (-Δ) • trqSadE 0 ∈ {e | b • trqSadE 0 + e ∈ trqSadX} := by
  simp only [Set.mem_ofPred_eq, trqSadX_mem, PiLp.add_apply, PiLp.smul_apply, trqSadE_apply]
  norm_num
  refine ⟨by linarith, by linarith⟩

/-- The first-order Step 1 at `p = b e_0` with radius `Δ ≤ 1`: the displacement `-Δ e_0`
achieves the first-order measure `b Δ`. -/
theorem trqSad_witness_p (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1) :
    Optimization.IsApproxMeasureStep ((ftaylorSeries ℝ (trqSadF a) (b • trqSadE
        0)).taylorDecrement 1)
      (min Δ 1) {e | b • trqSadE 0 + e ∈ trqSadX} trqSadP.ς ((-Δ) • trqSadE 0) := by
  rw [min_eq_left hΔ1]
  refine ⟨⟨mem_closedBall_zero_iff.2 (by rw [norm_smul_trqSadE, abs_neg, abs_of_nonneg hΔ0]),
    trqSadE0_mem hb0 hb1 hΔ0 hΔ1⟩, ?_⟩
  have hm : Optimization.decrementMeasure
      ((ftaylorSeries ℝ (trqSadF a) (b • trqSadE 0)).taylorDecrement 1) Δ
      {e | b • trqSadE 0 + e ∈ trqSadX} ≤ b * Δ := by
    refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self hΔ0, by
      change b • trqSadE 0 + 0 ∈ trqSadX
      rw [add_zero]; exact trqSad_smul_e0_mem hb0 hb1⟩ fun d hd => ?_
    rw [trqSad_ΔT1_p]
    have h1 := EuclideanSpace.abs_apply_le_norm d 0
    have h2 := mem_closedBall_zero_iff.1 hd.1
    have h3 := mul_le_mul_of_nonneg_left (neg_le_abs (d 0)) hb0
    have h4 := mul_le_mul_of_nonneg_left (h1.trans h2) hb0
    linarith
  rw [trqSad_ΔT1_p]
  simp only [PiLp.smul_apply, trqSadE_apply, ↓reduceIte, smul_eq_mul, mul_one]
  have hς : trqSadP.ς = 1 / 2 := rfl
  rw [hς]
  linarith [mul_nonneg hb0 hΔ0]


/-- The first-order step at `p = b e_0` with radius `Δ ≤ 1` (`ε_1 = b`): order `1` fails, the
step is the Step-1 displacement `-Δ e_0`. -/
theorem trqSad_step_p (hb : 0 < b) (hb1 : b ≤ 1) (hΔ0 : 0 < Δ) (hΔ1 : Δ ≤ 1) (hε1 : ε 1 = b)
    (W : ℕ → ℝ²) :
    Optimization.IsTRqStep (ftaylorSeries ℝ (trqSadF a) (b • trqSadE 0)) {e | b • trqSadE 0 + e ∈
        trqSadX}
      trqSadP.ς 2 ε (min Δ 1) Δ (fun j => if j = 1 then (-Δ) • trqSadE 0 else W j) 1
      ((-Δ) • trqSadE 0) where
  order_mem := by simp
  lt_taylorDecrement := by
    simp only [↓reduceIte, trqSad_ΔT1_p, PiLp.smul_apply, trqSadE_apply, smul_eq_mul, mul_one,
      min_eq_left hΔ1, pow_one, Nat.factorial_one, Nat.cast_one, div_one, hε1]
    have hς : trqSadP.ς = 1 / 2 := rfl
    rw [hς]; nlinarith [mul_pos hb hΔ0]
  taylorDecrement_le_of_lt := fun i hi hlt => absurd hlt (by have := (Finset.mem_Icc.1 hi).1; omega)
  mem := ⟨mem_closedBall_zero_iff.2 (by rw [norm_smul_trqSadE, abs_neg, abs_of_pos hΔ0]),
    trqSadE0_mem hb.le hb1 hΔ0.le hΔ1⟩
  taylorDecrement_le := le_of_eq (by simp)

/-- `f_a(b e_1) = b²/2`. -/
theorem trqSadF_p (a b : ℝ) : trqSadF a (b • trqSadE 0) = b ^ 2 / 2 := by
  rw [trqSadF_apply]; simp

/-- `f_a(b e_1 - Δ e_1) = (b - Δ)²/2`. -/
theorem trqSadF_p_step (a b Δ : ℝ) : trqSadF a (b • trqSadE 0 + (-Δ) • trqSadE 0) = (b - Δ) ^ 2 /
    2 := by
  rw [trqSadF_apply]; simp; ring

/-- An unsuccessful first-order iteration at `p` with radius `Δ ≥ 4b`: the ratio is
`1 - Δ/(2b) ≤ -1`, the iterate stays and the radius is divided by `4`. -/
theorem trqSad_accept_p_unsucc (hb : 0 < b) (h4 : 4 * b ≤ Δ) :
    Optimization.TRAcceptance trqSadP.toTRParams
      (Optimization.reductionRatio (trqSadF a) (b • trqSadE 0) ((-Δ) • trqSadE 0)
        ((ftaylorSeries ℝ (trqSadF a) (b • trqSadE 0)).taylorDecrement 1 ((-Δ) • trqSadE 0)))
      (b • trqSadE 0) ((-Δ) • trqSadE 0) (b • trqSadE 0) Δ (Δ / 4) := by
  have hΔ : 0 < Δ := by linarith
  have hρ : Optimization.reductionRatio (trqSadF a) (b • trqSadE 0) ((-Δ) • trqSadE 0)
      ((ftaylorSeries ℝ (trqSadF a) (b • trqSadE 0)).taylorDecrement 1 ((-Δ) • trqSadE 0)) < 1 /
          4 := by
    rw [Optimization.reductionRatio_def, trqSadF_p, trqSadF_p_step, trqSad_ΔT1_p]
    simp only [PiLp.smul_apply, trqSadE_apply, ↓reduceIte, smul_eq_mul, mul_one]
    rw [div_lt_iff₀ (by nlinarith)]
    nlinarith
  refine ⟨?_, ⟨fun h => absurd h (not_le.2 (hρ.trans (by norm_num : (1 : ℝ) / 4 < 3 / 4))),
    fun h => absurd h (not_le.2 hρ), fun _ => ⟨by change 1 / 4 * Δ ≤ Δ / 4; linarith,
      by change Δ / 4 ≤ 1 / 2 * Δ; linarith⟩⟩⟩
  exact (ite_eq_right (not_le.2 hρ)).symm

/-- The successful first-order iteration at `p` with radius `b`: the ratio is `1/2`, the step
lands at `0` and the radius stays `b`. -/
theorem trqSad_accept_p_succ (hb : 0 < b) :
    Optimization.TRAcceptance trqSadP.toTRParams
      (Optimization.reductionRatio (trqSadF a) (b • trqSadE 0) ((-b) • trqSadE 0)
        ((ftaylorSeries ℝ (trqSadF a) (b • trqSadE 0)).taylorDecrement 1 ((-b) • trqSadE 0)))
      (b • trqSadE 0) ((-b) • trqSadE 0) 0 b b := by
  have hρ : Optimization.reductionRatio (trqSadF a) (b • trqSadE 0) ((-b) • trqSadE 0)
      ((ftaylorSeries ℝ (trqSadF a) (b • trqSadE 0)).taylorDecrement 1 ((-b) • trqSadE 0)) = 1 /
          2 := by
    rw [Optimization.reductionRatio_def, trqSadF_p, trqSadF_p_step, trqSad_ΔT1_p]
    simp only [PiLp.smul_apply, trqSadE_apply, ↓reduceIte, smul_eq_mul, mul_one]
    field_simp; ring
  rw [hρ]
  refine ⟨?_, ⟨fun h => absurd h (by change ¬ (3 / 4 : ℝ) ≤ 1 / 2; norm_num),
    fun _ _ => ⟨by change 1 / 2 * b ≤ b; linarith, le_rfl⟩,
    fun h => absurd h (by change ¬ (1 / 2 : ℝ) < 1 / 4; norm_num)⟩⟩
  rw [ite_eq_left (show trqSadP.η₁ ≤ (1 / 2 : ℝ) by change (1 / 4 : ℝ) ≤ 1 / 2; norm_num),
    ← add_smul, add_neg_cancel, zero_smul]

/-- The second-order Step 1 at `0` with radius `b ≤ 1`: `b e_2` achieves the measure
`a b²/2`. -/
theorem trqSad_witness_zero (ha : 0 ≤ a) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    Optimization.IsApproxMeasureStep ((ftaylorSeries ℝ (trqSadF a) 0).taylorDecrement 2)
      (min b 1) {e | (0 : ℝ²) + e ∈ trqSadX} trqSadP.ς (b • trqSadE 1) := by
  rw [min_eq_left hb1]
  have hmem : b • trqSadE 1 ∈ {e | (0 : ℝ²) + e ∈ trqSadX} := by
    simp only [Set.mem_ofPred_eq, zero_add, trqSadX_mem, PiLp.smul_apply, trqSadE_apply]
    norm_num; exact ⟨by linarith, hb1⟩
  refine ⟨⟨mem_closedBall_zero_iff.2 (by rw [norm_smul_trqSadE, abs_of_nonneg hb0]), hmem⟩, ?_⟩
  have hm : Optimization.decrementMeasure ((ftaylorSeries ℝ (trqSadF a) 0).taylorDecrement 2) b
      {e | (0 : ℝ²) + e ∈ trqSadX} ≤ a * (b ^ 2 / 2) := by
    refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self hb0, by
      change (0 : ℝ²) + 0 ∈ trqSadX
      simp only [add_zero, trqSadX_mem, PiLp.zero_apply]; norm_num⟩ fun d hd => ?_
    rw [trqSad_ΔT2_zero ha]
    have h1 := EuclideanSpace.abs_apply_le_norm d 1
    have h2 := mem_closedBall_zero_iff.1 hd.1
    have h3 : (d 1) ^ 2 ≤ b ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h1.trans h2) 2
    nlinarith [sq_nonneg (d 0)]
  have hval : (ftaylorSeries ℝ (trqSadF a) 0).taylorDecrement 2 (b • trqSadE 1) = a * (b ^ 2 / 2)
      := by
    rw [trqSad_ΔT2_zero ha]; simp
  rw [hval]
  have hς : trqSadP.ς = 1 / 2 := rfl
  rw [hς]
  linarith [mul_nonneg ha (sq_nonneg b)]

/-- The second-order step at `0` with radius `b ≤ 1` (`ε_2 = a`): order `1` passes
(`∇f(0) = 0`), order `2` fails, the step is the Step-1 displacement `b e_2`. -/
theorem trqSad_step_zero (ha : 0 < a) (hb : 0 < b) (hb1 : b ≤ 1) (hε1 : 0 ≤ ε 1) (hε2 : ε 2 = a)
    (W : ℕ → ℝ²) :
    Optimization.IsTRqStep (ftaylorSeries ℝ (trqSadF a) 0) {e | (0 : ℝ²) + e ∈ trqSadX}
      trqSadP.ς 2 ε (min b 1) b (fun j => if j = 2 then b • trqSadE 1 else W j) 2 (b • trqSadE 1)
          where
  order_mem := by simp
  lt_taylorDecrement := by
    simp only [↓reduceIte, trqSad_ΔT2_zero ha.le, PiLp.smul_apply, trqSadE_apply, smul_eq_mul,
      min_eq_left hb1, hε2]
    norm_num
    have hς : trqSadP.ς = 1 / 2 := rfl
    rw [hς]; nlinarith [mul_pos ha (pow_pos hb 2)]
  taylorDecrement_le_of_lt := fun i hi hlt => by
    have hi1 : i = 1 := by have := (Finset.mem_Icc.1 hi).1; omega
    subst hi1
    simp only [trqSad_ΔT1_zero, show ¬ ((1 : ℕ) = 2) by decide, ↓reduceIte]
    have := trqSadP.ς_pos
    have : 0 ≤ min b 1 := le_min hb.le zero_le_one
    positivity
  mem := ⟨mem_closedBall_zero_iff.2 (by rw [norm_smul_trqSadE, abs_of_pos hb]), by
    simp only [Set.mem_ofPred_eq, zero_add, trqSadX_mem, PiLp.smul_apply, trqSadE_apply]
    norm_num; exact ⟨by linarith, hb1⟩⟩
  taylorDecrement_le := le_of_eq (by simp)

/-- The very successful second-order iteration at `0` with radius `b`: the ratio is `1`, the
step lands at `b e_2` and the radius stays `b`. -/
theorem trqSad_ratio_zero (ha : 0 < a) (hb : 0 < b) :
    Optimization.reductionRatio (trqSadF a) 0 (b • trqSadE 1)
      ((ftaylorSeries ℝ (trqSadF a) 0).taylorDecrement 2 (b • trqSadE 1)) = 1 := by
  have h : trqSadF a 0 - trqSadF a (0 + b • trqSadE 1) = a * (b ^ 2 / 2) := by
    rw [zero_add, trqSadF_apply, trqSadF_apply]; simp
  rw [Optimization.reductionRatio_def, taylorDecrement_two_trqSadF ha.le, h, div_self]
  positivity

/-- The very successful second-order iteration at `0` with radius `b`: the step lands at
`b e_2` and the radius stays `b`. -/
theorem trqSad_accept_zero (ha : 0 < a) (hb : 0 < b) :
    Optimization.TRAcceptance trqSadP.toTRParams
      (Optimization.reductionRatio (trqSadF a) 0 (b • trqSadE 1)
        ((ftaylorSeries ℝ (trqSadF a) 0).taylorDecrement 2 (b • trqSadE 1)))
      0 (b • trqSadE 1) (b • trqSadE 1) b b := by
  rw [trqSad_ratio_zero ha hb]
  refine ⟨?_, ⟨fun _ => ⟨le_rfl, by change b ≤ 2 * b; linarith⟩,
    fun _ h => absurd h (by change ¬ (1 : ℝ) < 3 / 4; norm_num),
    fun h => absurd h (by change ¬ (1 : ℝ) < 1 / 4; norm_num)⟩⟩
  rw [ite_eq_left (show trqSadP.η₁ ≤ (1 : ℝ) by change (1 / 4 : ℝ) ≤ 1; norm_num), zero_add]

end Prefix


open Classical in
/-- **(14.2.11) with the printed TRq-SC exponents `π_j = j + 1` is false for `q = 2` with `κ_decr`
depending only on the algorithm parameters, `ϑ` and the f.D1qLaB.X constants**
([cartis2022evaluation], Lemma 14.2.2, (14.2.12); the dependence of the explicit `κ_decr` of Lemma
12.2.4 / (12.2.14)). The objective varies with `κ` within a family with uniform constants; a single
fixed `f` is not treated here. For the TRq parameters `trqSadP`,
the threshold `ϑ = 1`, the box `X = [-1, 1]²` and every `κ > 0` there are `a ∈ (0, 1]` (the
objective `f_a(x) = x_1²/2 - a x_2²/2`, which satisfies f.D1qLaB.X with constants `4` independent of
`a`), tolerances `ε ∈ (0, 1]²` and a TRq-SC run with a successful iteration `k` before termination
that decreases `f_a` by less than `κ min_j ε_j^{j+1}`. With `r = 2^{-N}`, `ε_1 = r²`, `ε_2 = a = r`:
`N` unsuccessful first-order iterations at `(r², 0)` shrink the radius from `1` to `r²`, a
successful step reaches `0`, where the gradient vanishes and the second-order test fails, and the
second-order step `r² e_2` decreases `f_a` by `r⁵/2`, against `κ min(ε_1², ε_2³) = κ r⁴`. The radius
is shared across the orders and is driven down by the first-order failures; the decrease proved in
Lemma 12.2.4 is `κ ε_min^{q+1}` (`Chapter14.lemma_14_2_2_trq`). -/
theorem lemma_14_2_2_trq_printed_false {κ : ℝ} (hκ : 0 < κ) :
    ∃ (a : ℝ) (ε : ℕ → ℝ) (x s : ℕ → ℝ²) (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → ℝ²) (k : ℕ),
      0 < a ∧ a ≤ 1 ∧ (∀ j ∈ Finset.Icc 1 2, ε j ∈ Ioc 0 1) ∧ x 0 ∈ trqSadX ∧
      AssumptionD1qLaBX (trqSadF a) trqSadX (ball 0 2) (x 0) 1 2 (fun _ => 4) (fun _ => 4) ∧
      Chapter12.algorithm_12_2_1_feasible (trqSadF a) trqSadX trqSadP 2 ε 1 x s Δ jk d ∧
      (∀ i ≤ k, ¬ Chapter12.trqStop (trqSadF a) trqSadP 2 ε 1 x Δ d i) ∧
      trqSadP.η₁ ≤ Chapter12.trqRho (trqSadF a) x s jk k ∧
      trqSadF a (x k) - trqSadF a (x (k + 1)) < κ * Optimization.finMin 1 (fun j => ε j ^ (j + 1)) 2
          := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (mul_pos two_pos hκ) (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (1 / 2) ^ N := ⟨_, rfl⟩
  have hr0 : 0 < r := hr ▸ by positivity
  have hr1 : r ≤ 1 := hr ▸ pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = r ^ 2 := ⟨_, rfl⟩
  have hb : 0 < b := hbdef ▸ by positivity
  have hb1 : b ≤ 1 := hbdef ▸ pow_le_one₀ hr0.le hr1
  have hpowN : ((1 : ℝ) / 4) ^ N = b := by
    rw [hbdef, hr, ← pow_mul, mul_comm, pow_mul]; norm_num
  have hq0 : ∀ k : ℕ, 0 < ((1 : ℝ) / 4) ^ k := fun k => by positivity
  have hq1 : ∀ k : ℕ, ((1 : ℝ) / 4) ^ k ≤ 1 := fun k => pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℕ → ℝ, ε = fun j => if j = 1 then b else r := ⟨_, rfl⟩
  have hε1 : ε 1 = b := by simp [hεdef]
  have hε2 : ε 2 = r := by simp [hεdef]
  -- the Step-1 displacements of the orders not used
  have hW : ∀ (y : ℝ²) (δ : ℝ) (j : ℕ), ∃ w : ℝ², y ∈ trqSadX → 0 ≤ δ →
      Optimization.IsApproxMeasureStep ((ftaylorSeries ℝ (trqSadF r) y).taylorDecrement j) δ
        {e | y + e ∈ trqSadX} trqSadP.ς w := by
    intro y δ j
    by_cases h : y ∈ trqSadX ∧ 0 ≤ δ
    · obtain ⟨w, hw⟩ := Optimization.exists_isApproxMeasureStep_taylorDecrement
        (ftaylorSeries ℝ (trqSadF r) y) j
        (isClosed_trqSadX.preimage (continuous_const.add continuous_id))
        (by change y + 0 ∈ trqSadX; rw [add_zero]; exact h.1) h.2 trqSadP.ς_le_one
      exact ⟨w, fun _ _ => hw⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose W hW using hW
  -- the continuation: any TRq-SC run from `b e_2` with initial radius `b`
  have hbmax : b ≤ trqSadP.Δmax := hb1
  have hq₀ : b • trqSadE 1 ∈ trqSadX := by
    simp only [trqSadX_mem, PiLp.smul_apply, trqSadE_apply]; norm_num; exact ⟨by linarith, hb1⟩
  obtain ⟨y, sy, Δy, jy, dy, hy0, hyr⟩ := Optimization.exists_isTRqRun_feasible isClosed_trqSadX
    (trqSadF r) (trqSadP.withΔ₀ b hb hbmax) 2 ε zero_le_one hq₀
  -- the explicit prefix: `N` unsuccessful first-order iterations at `b e_1`, a successful one to
  -- `0`, and the successful second-order iteration from `0` to `b e_2`
  obtain ⟨xp, hxp⟩ : ∃ xp : ℕ → ℝ², ∀ k, xp k =
      if k ≤ N then b • trqSadE 0 else if k = N + 1 then 0 else b • trqSadE 1 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Δp, hΔp⟩ : ∃ Δp : ℕ → ℝ, ∀ k, Δp k = if k ≤ N then ((1 : ℝ) / 4) ^ k else b :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨sp, hsp⟩ : ∃ sp : ℕ → ℝ², ∀ k, sp k =
      if k ≤ N then (-((1 : ℝ) / 4) ^ k) • trqSadE 0 else b • trqSadE 1 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨jp, hjp⟩ : ∃ jp : ℕ → ℕ, ∀ k, jp k = if k ≤ N then 1 else 2 := ⟨_, fun _ => rfl⟩
  obtain ⟨dp, hdp⟩ : ∃ dp : ℕ → ℕ → ℝ², ∀ k, dp k =
      if k ≤ N then (fun j => if j = 1 then (-((1 : ℝ) / 4) ^ k) • trqSadE 0
        else W (b • trqSadE 0) (min (((1 : ℝ) / 4) ^ k) 1) j)
      else (fun j => if j = 2 then b • trqSadE 1 else W 0 (min b 1) j) :=
    ⟨_, fun _ => rfl⟩
  have hxl : ∀ k ≤ N, xp k = b • trqSadE 0 := fun k hk => by rw [hxp, ite_eq_left hk]
  have hΔl : ∀ k ≤ N, Δp k = ((1 : ℝ) / 4) ^ k := fun k hk => by rw [hΔp, ite_eq_left hk]
  have hsl : ∀ k ≤ N, sp k = (-((1 : ℝ) / 4) ^ k) • trqSadE 0 := fun k hk => by
    rw [hsp, ite_eq_left hk]
  have hjl : ∀ k ≤ N, jp k = 1 := fun k hk => by rw [hjp, ite_eq_left hk]
  have hdl : ∀ k ≤ N, dp k = (fun j => if j = 1 then (-((1 : ℝ) / 4) ^ k) • trqSadE 0
      else W (b • trqSadE 0) (min (((1 : ℝ) / 4) ^ k) 1) j) := fun k hk => by
    rw [hdp, ite_eq_left hk]
  have hxN : xp (N + 1) = 0 := by rw [hxp, ite_eq_right (by omega), ite_eq_left rfl]
  have hxN2 : xp (N + 1 + 1) = b • trqSadE 1 := by
    rw [hxp, ite_eq_right (by omega), ite_eq_right (by omega)]
  have hΔN : ∀ k, N < k → Δp k = b := fun k hk => by rw [hΔp, ite_eq_right (by omega)]
  have hsN : sp (N + 1) = b • trqSadE 1 := by rw [hsp, ite_eq_right (by omega)]
  have hjN : jp (N + 1) = 2 := by rw [hjp, ite_eq_right (by omega)]
  have hdN : dp (N + 1) = (fun j => if j = 2 then b • trqSadE 1 else W 0 (min b 1) j) := by
    rw [hdp, ite_eq_right (by omega)]
  have hcases : ∀ k < N + 2, k ≤ N ∨ k = N + 1 := fun k hk => by omega
  have hstep : ∀ k < N + 2, Optimization.IsTRqStep (ftaylorSeries ℝ (trqSadF r) (xp k))
      {e | xp k + e ∈ trqSadX} trqSadP.ς 2 ε (min (Δp k) 1) (Δp k) (dp k) (jp k) (sp k) :=
    fun k hk => by
    rcases hcases k hk with h | rfl
    · rw [hxl k h, hΔl k h, hdl k h, hjl k h, hsl k h]
      exact trqSad_step_p hb hb1 (hq0 k) (hq1 k) hε1 _
    · rw [hxN, hΔN _ (by omega), hdN, hjN, hsN]
      exact trqSad_step_zero hr0 hb hb1 (hε1 ▸ hb.le) hε2 _
  have hacc : ∀ k < N + 2, Optimization.TRAcceptance trqSadP.toTRParams
      (Optimization.reductionRatio (trqSadF r) (xp k) (sp k)
        ((ftaylorSeries ℝ (trqSadF r) (xp k)).taylorDecrement (jp k) (sp k)))
      (xp k) (sp k) (xp (k + 1)) (Δp k) (Δp (k + 1)) := fun k hk => by
    rcases hcases k hk with h | rfl
    · rcases Nat.lt_or_ge k N with hkN | hkN
      · rw [hxl k h, hxl (k + 1) hkN, hsl k h, hΔl k h, hΔl (k + 1) hkN, hjl k h]
        have h4 : 4 * b ≤ ((1 : ℝ) / 4) ^ k := by
          rw [← hpowN]
          have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)
            (show k + 1 ≤ N by omega)
          rw [pow_succ] at this
          linarith
        have e : ((1 : ℝ) / 4) ^ (k + 1) = ((1 : ℝ) / 4) ^ k / 4 := by rw [pow_succ]; ring
        rw [e]
        exact trqSad_accept_p_unsucc hb h4
      · obtain rfl : k = N := le_antisymm h hkN
        rw [hxl k h, hxN, hsl k h, hΔl k h, hΔN _ (by omega), hjl k h, hpowN]
        exact trqSad_accept_p_succ hb
    · rw [hxN, hxN2, hΔN _ (by omega), hΔN _ (by omega), hsN, hjN]
      exact trqSad_accept_zero hr0 hb
  have hwit : ∀ k < N + 2, ∀ j ∈ Finset.Icc 1 2, Optimization.IsApproxMeasureStep
      ((ftaylorSeries ℝ (trqSadF r) (xp k)).taylorDecrement j) (min (Δp k) 1)
      {e | xp k + e ∈ trqSadX} trqSadP.ς (dp k j) := fun k hk j _ => by
    rcases hcases k hk with h | rfl
    · rw [hxl k h, hΔl k h, hdl k h]
      by_cases hj1 : j = 1
      · subst hj1
        simp only [↓reduceIte]
        exact trqSad_witness_p hb.le hb1 (hq0 k).le (hq1 k)
      · simp only [hj1, ↓reduceIte]
        exact hW _ _ _ (trqSad_smul_e0_mem hb.le hb1) (le_min (hq0 k).le zero_le_one)
    · rw [hxN, hΔN _ (by omega), hdN]
      by_cases hj2 : j = 2
      · subst hj2
        simp only [↓reduceIte]
        exact trqSad_witness_zero hr0.le hb.le hb1
      · simp only [hj2, ↓reduceIte]
        exact hW _ _ _ (by simp [trqSadX_mem]) (le_min hb.le zero_le_one)
  have hcap : ∀ k < N + 2, Δp (k + 1) ≤ trqSadP.Δmax := fun k _ => by
    change Δp (k + 1) ≤ 1
    rcases Nat.lt_or_ge k N with hkN | hkN
    · rw [hΔl (k + 1) hkN]; exact hq1 _
    · rw [hΔN _ (by omega)]; exact hb1
  -- the run
  obtain ⟨x, s, Δ, jk, d, hx0, hrun, hns, -, hpre, hpre'⟩ := Optimization.exists_isTRqRun_append
    (T := N + 2) (T' := 0) (c := 0) (f := trqSadF r) (D := ftaylorSeries ℝ (trqSadF r))
    (S := fun y => {e | y + e ∈ trqSadX}) (P := trqSadP) (q := 2) (ε := ε) (ϑ := 1) (xp := xp)
    (sp := sp) (Δp := Δp) (jp := jp) (dp := dp) (by rw [hΔl 0 (Nat.zero_le _), pow_zero]; rfl)
    (hΔN _ (by omega)) hb hbmax hstep hacc hwit hcap (by rw [hy0, ← hxN2]) hyr
    (fun _ h => absurd h (Nat.not_lt_zero _)) (Nat.zero_le _)
  have hxN' : x (N + 1) = 0 := (hpre (N + 1) (by omega)).1.trans hxN
  refine ⟨r, ε, x, s, Δ, jk, d, N + 1, hr0, hr1, fun j hj => ?_, ?_,
    trqSadF_assumption hr0.le hr1 (x 0), hrun, fun i hi => hns i (by omega), ?_, ?_⟩
  · have : j = 1 ∨ j = 2 := by have := Finset.mem_Icc.1 hj; omega
    rcases this with rfl | rfl
    · rw [hε1]; exact ⟨hb, hb1⟩
    · rw [hε2]; exact ⟨hr0, hr1⟩
  · rw [hx0, hxl 0 (Nat.zero_le _)]; exact trqSad_smul_e0_mem hb.le hb1
  · obtain ⟨hsk, hjk, -⟩ := hpre' (N + 1) (by omega)
    change trqSadP.η₁ ≤ Optimization.trqRatio (trqSadF r)
      (fun k => ftaylorSeries ℝ (trqSadF r) (x k)) x s jk (N + 1)
    rw [Optimization.trqRatio_eq, hxN', hsk, hjk, hsN, hjN, trqSad_ratio_zero hr0 hb]
    change (1 / 4 : ℝ) ≤ 1; norm_num
  · -- the decrease `r⁵/2` against `κ min_j ε_j^{j+1} ≥ κ r⁴`
    rw [(hpre (N + 1 + 1) (by omega)).1, hxN2, hxN']
    have hdec : trqSadF r 0 - trqSadF r (b • trqSadE 1) = r * (b ^ 2 / 2) := by
      rw [trqSadF_apply, trqSadF_apply]; simp
    rw [hdec]
    have hmin : b ^ 2 ≤ Optimization.finMin 1 (fun j => ε j ^ (j + 1)) 2 := by
      refine Optimization.le_finMin (pow_le_one₀ hb.le hb1) fun j hj => ?_
      have : j = 1 ∨ j = 2 := by have := Finset.mem_Icc.1 hj; omega
      rcases this with rfl | rfl
      · rw [hε1]
      · rw [hε2, hbdef]
        have : r ^ 4 ≤ r ^ 3 := pow_le_pow_of_le_one hr0.le hr1 (by norm_num)
        calc (r ^ 2) ^ 2 = r ^ 4 := by ring
          _ ≤ r ^ 3 := this
    have hrN : r < 2 * κ := hr ▸ hN
    have hb2 : 0 < b ^ 2 := by positivity
    calc r * (b ^ 2 / 2) < κ * b ^ 2 := by nlinarith
      _ ≤ κ * Optimization.finMin 1 (fun j => ε j ^ (j + 1)) 2 :=
          mul_le_mul_of_nonneg_left hmin hκ.le

/-- **No uniform `κ_decr` for the TRq-SC row `j + 1`** ([cartis2022evaluation], (14.2.11)–(14.2.12),
`q = 2`): there is no `κ > 0` such that, for every `a ∈ (0, 1]`, every TRq-SC run (parameters
`trqSadP`, `ϑ = 1`, `X = [-1, 1]²`) on `f_a` satisfying f.D1qLaB.X with the constants `4`, every
`ε ∈ (0, 1]²` and every successful iteration `k` before termination,
`f_a(x_k) - f_a(x_{k+1}) ≥ κ min_j ε_j^{j+1}` (`lemma_14_2_2_trq_printed_false`). -/
theorem lemma_14_2_2_trq_printed_false_uniform :
    ¬ ∃ κ : ℝ, 0 < κ ∧ ∀ (a : ℝ) (ε : ℕ → ℝ) (x s : ℕ → ℝ²) (Δ : ℕ → ℝ) (jk : ℕ → ℕ)
      (d : ℕ → ℕ → ℝ²) (k : ℕ), 0 < a → a ≤ 1 → (∀ j ∈ Finset.Icc 1 2, ε j ∈ Ioc 0 1) →
      AssumptionD1qLaBX (trqSadF a) trqSadX (ball 0 2) (x 0) 1 2 (fun _ => 4) (fun _ => 4) →
      Chapter12.algorithm_12_2_1_feasible (trqSadF a) trqSadX trqSadP 2 ε 1 x s Δ jk d →
      (∀ i ≤ k, ¬ Chapter12.trqStop (trqSadF a) trqSadP 2 ε 1 x Δ d i) →
      trqSadP.η₁ ≤ Chapter12.trqRho (trqSadF a) x s jk k →
      κ * Optimization.finMin 1 (fun j => ε j ^ (j + 1)) 2 ≤
        trqSadF a (x k) - trqSadF a (x (k + 1)) := by
  rintro ⟨κ, hκ, H⟩
  obtain ⟨a, ε, x, s, Δ, jk, d, k, ha0, ha1, hε, -, hA, hrun, hns, hsucc, hlt⟩ :=
    lemma_14_2_2_trq_printed_false hκ
  exact absurd (H a ε x s Δ jk d k ha0 ha1 hε hA hrun hns hsucc) (not_le.2 hlt)

end Decrease

end TRqPrintedFalse

end CartisGouldToint.Chapter14
