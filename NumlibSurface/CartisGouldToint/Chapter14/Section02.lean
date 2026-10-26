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
* `AssumptionD1qLaBX f X X₀ x₀ j₀ q L B` — f.D1qLaB.X (`j₀ = 1`) and its variants f.D1pLaB.X,
  f.D0qLaB.X, f.D0pLaB.X;
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
  ARqp with a feasible set); `theorem_14_2_4_sharp` — sharpness of the TRq-SC, ARqp-SC (`q ≤ 2`)
  and ARqpC-SC (`q = 1`, convex `h`) orders with `X = ℝ`; `theorem_14_2_4_sharp_arqp` —
  sharpness of the ARqp-SC row for `q ≥ 3` (Theorem 12.2.17 with `X = ℝ`);
* `lemma_14_2_2_trqida`, `lemma_14_2_3_trqida`, `theorem_14_2_4_trqida` (TRqIDA-SC),
  `lemma_14_2_2_trqeda`, `lemma_14_2_3_trqeda`, `theorem_14_2_4_trqeda` (TRqEDA-SC),
  `lemma_14_2_2_arqpida`, `lemma_14_2_3_arqpida`, `theorem_14_2_4_arqpida` (ARqpIDA-SC),
  `lemma_14_2_2_arqpeda`, `lemma_14_2_3_arqpeda`, `theorem_14_2_4_arqpeda` (ARqpEDA-SC) — the
  dynamic-accuracy rows, from the Chapter 13 runs with a feasible set
  (`Chapter13.algorithm_13_1_1_feasible`, …, `Chapter13.algorithm_13_3_2_feasible`);
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
  `π_j = q + 1` (the decrease is a multiple of `ε_min^{q+1}`).
* Lemma 14.2.3 is stated with explicit constants: `κ_unc` contains `|log ε_min|` terms (the
  radius lower bound of the TR methods is proportional to `ε_min`, and the number of
  accuracy-improving iterations of the IDA/EDA methods is logarithmic in `ε_min`); for the IDA
  methods, which have no termination rule, the count holds up to the first approximately optimal
  iterate. The ARqpIDA-SC row of Lemma 14.2.2 holds at successful iterations followed by an
  iterate that is not approximately optimal, and the ARqpEDA-SC row needs `θ < ς/2` and holds at
  the successful iterations of Lemma 13.3.7 (the corrections of Lemmas 13.1.18 and 13.3.7).

## Not formalized here

* The anchored assumptions f.D1qLaB.X (f.D0qLaB.X): the rows formalized here assume f.D1pL (or
  f.D1qL, f.D0qL, f.D0pL) on an open convex superset `C` of `X` (`Chapter12.AssumptionD1pLOn`,
  `Chapter13.AssumptionD0qLOn`; for ARqpC-SC on `ℝⁿ`), which `AssumptionD1qLaBX.assumptionD1pLOn`
  yields when the anchor set is all of `X₀`; the book's remark that only anchored conditions are
  used by the proofs is not formalized.
* For ARqpIDA-SC and ARqpEDA-SC with `q = 2` and `X ≠ ℝⁿ` (or `q = 1` and `X` nonconvex), the
  radius hypothesis `δ = 1` of `Chapter13.RadiiControl` is not guaranteed by Step 2, and the
  book's order `j(p+1)/p` obtained with (12.2.51) at every order is not formalized for these
  methods (for `q > 2`, `RadiiControl` is the (12.2.51)-type control at every order, as for
  ARqp-SC). Sharpness of the IDA/EDA rows is not stated (Chapter 13 has no slow examples).
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
f.D1pLaB.X with `p` in place of `q`); with `j₀ = 0`, f.D0qLaB.X and f.D0pLaB.X. -/
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

/-- f.D0qL on `C` (orders `[0, q]`, `Chapter13.AssumptionD0qLOn`) gives f.D1qL on `C` (orders
`[1, q]`, `Chapter12.AssumptionD1pLOn`). -/
theorem _root_.CartisGouldToint.Chapter13.AssumptionD0qLOn.toAssumptionD1pLOn {f : ℝⁿ → ℝ}
    {C : Set ℝⁿ} {q : ℕ} {L : ℕ → ℝ} (h : Chapter13.AssumptionD0qLOn f C q L) :
    Chapter12.AssumptionD1pLOn f C q L :=
  ⟨h.isOpen, h.convex, h.contDiffAt_q, fun _ hj => h.one_le (Finset.mem_Icc.1 hj).2,
    fun _ hj => h.lipschitz (Finset.mem_Icc.1 hj).2⟩

/-- f.D1qL on `C` together with an `L_{f,0}`-Lipschitz `f` on `C` (`L_{f,0} ≥ 1`) is f.D0qL on
`C`. -/
theorem _root_.CartisGouldToint.Chapter13.AssumptionD0qLOn.of_assumptionD1pLOn {f : ℝⁿ → ℝ}
    {C : Set ℝⁿ} {q : ℕ} {L : ℕ → ℝ} (h : Chapter12.AssumptionD1pLOn f C q L) (h0 : 1 ≤ L 0)
    (hlip : IteratedFDerivLipschitzOn f 0 (L 0) C) : Chapter13.AssumptionD0qLOn f C q L where
  isOpen := h.isOpen
  convex := h.convex
  contDiffAt_q := h.contDiffAt
  one_le {j} hj := by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact h0
    · exact h.one_le j (Finset.mem_Icc.2 ⟨hj0, hj⟩)
  lipschitz {j} hj := by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact hlip
    · exact h.lipschitz j (Finset.mem_Icc.2 ⟨hj0, hj⟩)

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

The rows of Lemmas 14.2.2–14.2.3 and Theorem 14.2.4 for ARqpC-SC and TRq-SC are stated here
under global smoothness assumptions (f.D1pL and c.D1pL of §14.1 on `ℝⁿ` for ARqpC-SC; f.D1qL on
an open convex `C ⊇ X`, `Chapter12.AssumptionD1pLOn`, for TRq-SC) rather than the anchored
f.D1qLaB.X; `AssumptionD1qLaBX.assumptionD1pLOn` gives the latter's Lipschitz part when the
anchor set is the whole of `X₀`. -/

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
    (hc : AssumptionCD1pL c p Lc) (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h) {wlow : ℝ}
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
    theorem_14_1_10_i hr hθς hf hc hL hS hw hq hconv hXc hδ₀
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
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hϑ : Chapter12.finMin 1 ε q ≤ ϑ) (hϑ1 : ϑ ≤ 1)
    {k : ℕ} (hk : ∀ i ≤ k, ¬ Chapter12.trqStop f P q ε ϑ x Δ d i) :
    (P.ς * Chapter12.trqKappaDelta f P q L ϑ (x 0)) ^ (q + 1) / q ! *
        Chapter12.finMin 1 ε q ^ (q + 1) ≤
        (ftaylorSeries ℝ f (x k)).taylorDecrement (jk k) (s k) ∧
      (P.η₁ ≤ Chapter12.trqRho f x s jk k →
        P.η₁ * ((P.ς * Chapter12.trqKappaDelta f P q L ϑ (x 0)) ^ (q + 1) / q ! *
          Chapter12.finMin 1 ε q ^ (q + 1)) ≤ f (x k) - f (x (k + 1))) :=
  Chapter12.lemma_12_2_4_feasible h hf hXC hx0 hε hϑ hϑ1 hk

/-- **Theorem 14.2.4** of [cartis2022evaluation], TRq-SC row: every TRq-SC run terminates at some
`k_ε` with `x_{k_ε} ∈ X` and the constrained `(ε, δ)`-certificate over `{d | x_{k_ε} + d ∈ X}`,
within the bounds of Theorem 12.2.5 (`O(max_j ε_j^{-(q+1)})`). -/
theorem theorem_14_2_4_trq {flow : ℝ} (hb : ∀ y ∈ X, flow ≤ f y)
    (hf : Chapter12.AssumptionD1pLOn f C q L) (hXC : X ⊆ C) (hx0 : x 0 ∈ X)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hϑ : Chapter12.finMin 1 ε q ≤ ϑ) (hϑ1 : ϑ ≤ 1)
    (h : Chapter12.algorithm_12_2_1_feasible f X P q ε ϑ x s Δ jk d) :
    ∃ kε, Optimization.IsFirstHit (Chapter12.trqStop f P q ε ϑ x Δ d) kε ∧ x kε ∈ X ∧
      min (Δ kε) ϑ ∈ Ioc 0 1 ∧
      Optimization.IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) {e | x kε + e ∈ X} q ε
        (fun _ => min (Δ kε) ϑ) ∧
      (Optimization.funEvalCount kε : ℝ) ≤
        Chapter12.kappaATRq f P q L ϑ (x 0) * (f (x 0) - flow) /
            Chapter12.finMin 1 ε q ^ (q + 1) +
          Chapter12.kappaBTRq P * |Real.log (Chapter12.finMin 1 ε q)| +
          Chapter12.kappaCTRq f P q L ϑ (x 0) ∧
      (Optimization.derivEvalCount (fun k => P.η₁ ≤ Chapter12.trqRho f x s jk k) kε : ℝ) ≤
        Chapter12.kappaSTRq f P q L ϑ (x 0) * (f (x 0) - flow) /
          Chapter12.finMin 1 ε q ^ (q + 1) + 1 :=
  Chapter12.theorem_12_2_5_feasible hb hf hXC hx0 hε hϑ hϑ1 h

/-- **Lemma 14.2.3** of [cartis2022evaluation], TRq-SC row (Lemma 2.3.1 with the radius lower
bound of Lemma 12.2.3 with a feasible set, `Chapter12.lemma_12_2_3_feasible`): for a TRq-SC run
under f.D1qL on an open convex `C ⊇ X`, `x₀ ∈ X`, `ε ∈ (0, 1]^q` and `ϑ ∈ [ε_min, 1]`, every
iteration `k` reached (up to and including termination) satisfies `k ≤ κ_uns |𝒮_k| + κ_unc`
(14.2.13) with `κ_uns = 1 + log γ₃/|log γ₂|` and
`κ_unc = |log(min(γ₁ ϑ, κ_Δ ς ε_min)/Δ₀)|/|log γ₂|` (`κ_Δ` of (12.2.14)). -/
theorem lemma_14_2_3_trq (h : Chapter12.algorithm_12_2_1_feasible f X P q ε ϑ x s Δ jk d)
    (hf : Chapter12.AssumptionD1pLOn f C q L) (hXC : X ⊆ C) (hx0 : x 0 ∈ X)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hϑ : Chapter12.finMin 1 ε q ≤ ϑ) (hϑ1 : ϑ ≤ 1)
    {k : ℕ} (hk : ∀ i < k, ¬ Chapter12.trqStop f P q ε ϑ x Δ d i) :
    (k : ℝ) ≤
      (Optimization.successSet (fun j => P.η₁ ≤ Chapter12.trqRho f x s jk j) k).card *
          (1 + Real.log P.γ₃ / |Real.log P.γ₂|) +
        |Real.log (min (P.γ₁ * ϑ) (Chapter12.trqKappaDelta f P q L ϑ (x 0) *
          (P.ς * Chapter12.finMin 1 ε q)) / P.Δ₀)| / |Real.log P.γ₂| := by
  rcases k with _ | k
  · rw [Nat.cast_zero]
    have : 0 ≤ 1 + Real.log P.γ₃ / |Real.log P.γ₂| :=
      add_nonneg zero_le_one (div_nonneg (Real.log_nonneg P.one_le_γ₃) (abs_nonneg _))
    positivity
  have hk' : ∀ i ≤ k, ¬ Chapter12.trqStop f P q ε ϑ x Δ d i := fun i hi =>
    hk i (Nat.lt_succ_of_le hi)
  have hεm : 0 < Chapter12.finMin 1 ε q := Chapter12.finMin_pos one_pos fun j hj => (hε j hj).1
  have hϑ0 : 0 < ϑ := hεm.trans_le hϑ
  obtain ⟨⟨hκ0, -⟩, -, hΔ⟩ := Chapter12.lemma_12_2_3_feasible h hf hXC hx0 hϑ0 hϑ1
    (fun j hj => (hε j hj).1.le) hk'
  have hgap : P.ς * Chapter12.finMin 1 ε q ≤
      Optimization.prefixMin (Chapter12.trqGapSeq f ϑ x Δ jk d) k :=
    (Optimization.IsTRqRun.trqGap_ge h hϑ0 (fun _ hj => Chapter12.finMin_le hj) hk').1
  have hmin : 0 < min (P.γ₁ * ϑ) (Chapter12.trqKappaDelta f P q L ϑ (x 0) *
      (P.ς * Chapter12.finMin 1 ε q)) :=
    lt_min (mul_pos P.γ₁_pos hϑ0) (mul_pos hκ0 (mul_pos P.ς_pos hεm))
  exact h.toIsTRRun.le_succ_count hk hmin
    ((min_le_min le_rfl (mul_le_mul_of_nonneg_left hgap hκ0.le)).trans hΔ)

end TRqSC

section ARqpSC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f : E → ℝ} {X C : Set E}
  {P : Optimization.ARqpParams} {p q : ℕ} {ε δ₀ : ℕ → ℝ} {x s : ℕ → E} {σ : ℕ → ℝ}
  {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → E} {L : ℕ → ℝ}

/-- **Lemma 14.2.2** of [cartis2022evaluation], ARqp-SC row (Lemma 12.2.13 with a feasible set):
for an ARqp-SC run (`Chapter12.algorithm_12_2_2_feasible`, `X ⊆ C`) under f.D1pL on an open convex
`C` and `θ < ς`, every successful iteration `k` not followed by termination decreases `f` by at
least `η₁ κ_{Δm} min_j ε_j^{π_j}`, provided the radius policy holds (`δ_{k+1,j} = 1` if `q ≤ 2`,
(12.2.51) otherwise), with `π_j = Chapter12.arqpPi p q j`. (The book's exponent table needs
`δ_{k,2} = 1` only when `X = ℝⁿ` and `δ_{k,1} = 1` only for convex `X`; here this is the
hypothesis on the radii.) -/
theorem lemma_14_2_2_arqp (hf : Chapter12.AssumptionD1pLOn f C p L) (hXC : X ⊆ C) (hq : 1 ≤ q)
    (hqp : q ≤ p) (hθς : P.θ < P.ς) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (h : Chapter12.algorithm_12_2_2_feasible f X P p q ε δ₀ x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ Chapter12.arqpStop f P p q ε x s σ δ d i)
    (hs : P.η₁ ≤ Chapter12.arqpRho f p x s σ k)
    (hk1 : ¬ Optimization.arqpStop₁ P q ε (Chapter12.arqpData f p x σ) δ d (k + 1))
    (hrad : (q ≤ 2 → ∀ j ∈ Finset.Icc 1 q, δ (k + 1) j = 1) ∧
      (2 < q → 1 ≤ ‖s k‖ ∨ ∀ j ∈ Finset.Icc 1 q,
        Chapter12.arqpKappaDelta P (Chapter12.finMax 1 L p)
          (Optimization.arSigmaMax P.toARParams (L p)) * ε j ≤ δ (k + 1) j)) :
    Chapter12.arqpKappaDm P L p q *
        Chapter12.finMin 1 (fun j => ε j ^ Chapter12.arqpPi p q j) q ≤
        (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k) ∧
      P.η₁ * (Chapter12.arqpKappaDm P L p q *
        Chapter12.finMin 1 (fun j => ε j ^ Chapter12.arqpPi p q j) q) ≤
        f (x k) - f (x (k + 1)) :=
  Chapter12.lemma_12_2_13_feasible hf hXC hq hqp hθς hε h hk hs hk1 hrad

/-- **Lemma 14.2.3** of [cartis2022evaluation], ARqp-SC row (Lemma 2.4.1 with the bound
`σ_max = max(σ₀, γ₃ L_{f,p}/(1 - η₂))` of Lemma 12.2.13's analysis): for every iteration `k`
reached, `k ≤ κ_uns |𝒮_k| + κ_unc` (14.2.13) with `κ_uns = 1 + |log γ₁|/log γ₂` and
`κ_unc = log(σ_max/σ₀)/log γ₂`. The other rows are `lemma_14_2_3_arqpc`, `lemma_14_2_3_trq`,
`lemma_14_2_3_trqida`, `lemma_14_2_3_trqeda`, `lemma_14_2_3_arqpida` and `lemma_14_2_3_arqpeda`. -/
theorem lemma_14_2_3 (hf : Chapter12.AssumptionD1pLOn f C p L) (hXC : X ⊆ C) (hp : 1 ≤ p)
    (h : Chapter12.algorithm_12_2_2_feasible f X P p q ε δ₀ x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i < k, ¬ Chapter12.arqpStop f P p q ε x s σ δ d i) :
    (k : ℝ) ≤ (Optimization.successSet (fun j => P.η₁ ≤ Chapter12.arqpRho f p x s σ j) k).card *
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
      Real.log (Optimization.arSigmaMax P.toARParams (L p) / P.σ₀) / Real.log P.γ₂ :=
  h.toIsARRun.le_succ_count hk (Chapter12.arqp_sigma_le hf hXC hp h k hk).2

/-- **Theorem 14.2.4** of [cartis2022evaluation], ARqp-SC row (Theorem 12.2.14 with a feasible
set): under f.bB.X, f.D1pL on an open convex `C ⊇ X`, `σ_min > 0`, `θ < ς` and the radius policy
(`δ = 1` when `q ≤ 2`, (12.2.51) otherwise), every ARqp-SC run terminates at some `k_ε` with
`x_{k_ε} ∈ X` and an `(ε, δ_ε)`-approximate `q`-th order certificate over
`{d | x_{k_ε} + d ∈ X}`, within the bounds of Theorem 12.2.14 (orders
`O(max_j ε_j^{-π_j})`, `π_j = arqpPi p q j`). -/
theorem theorem_14_2_4_arqp {flow : ℝ} (hb : ∀ y ∈ X, flow ≤ f y)
    (hf : Chapter12.AssumptionD1pLOn f C p L) (hXC : X ⊆ C) (hq : 1 ≤ q) (hqp : q ≤ p)
    (hσmin : 0 < P.σmin) (hθς : P.θ < P.ς) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1)
    (h : Chapter12.algorithm_12_2_2_feasible f X P p q ε δ₀ x s σ δ δs d dm)
    (hrad : (q ≤ 2 → (∀ j ∈ Finset.Icc 1 q, δ₀ j = 1) ∧
        ∀ k, (∀ i ≤ k, ¬ Chapter12.arqpStop f P p q ε x s σ δ d i) →
          ∀ j ∈ Finset.Icc 1 q, δs k j = 1) ∧
      (2 < q → ∀ k, (∀ i ≤ k, ¬ Chapter12.arqpStop f P p q ε x s σ δ d i) → ‖s k‖ < 1 →
        ∀ j ∈ Finset.Icc 1 q,
          Chapter12.arqpKappaDelta P (Chapter12.finMax 1 L p) (σ k) * ε j ≤ δs k j)) :
    ∃ kε, Optimization.IsFirstHit (Chapter12.arqpStop f P p q ε x s σ δ d) kε ∧ x kε ∈ X ∧
      (∃ δε : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, δε j ∈ Ioc 0 1) ∧
        Optimization.IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) {e | x kε + e ∈ X} q ε δε) ∧
      (Optimization.funEvalCount kε : ℝ) ≤ Chapter12.kappaAARqp P L p q * (f (x 0) - flow) /
        Chapter12.finMin 1 (fun j => ε j ^ Chapter12.arqpPi p q j) q +
          Chapter12.kappaCARqp P L p ∧
      (Optimization.derivEvalCount (fun k => P.η₁ ≤ Chapter12.arqpRho f p x s σ k) kε : ℝ) ≤
        Chapter12.kappaSARqp P L p q * (f (x 0) - flow) /
          Chapter12.finMin 1 (fun j => ε j ^ Chapter12.arqpPi p q j) q + 2 :=
  Chapter12.theorem_12_2_14_feasible hb hf hXC hq hqp hσmin hθς hε hδ₀ h hrad

end ARqpSC

/-! ### The dynamic-accuracy algorithms with simple constraints

The TRqIDA-SC, TRqEDA-SC, ARqpIDA-SC and ARqpEDA-SC rows of Lemmas 14.2.2–14.2.3 and
Theorem 14.2.4 are the Chapter 13 results for the runs with a feasible set
(`Chapter13.algorithm_13_1_1_feasible`, …, `X = univ` being the algorithms of Chapter 13), under
f.D0qL (f.D0pL) on an open convex `C ⊇ X` (`Chapter13.AssumptionD0qLOn`) in place of the anchored
f.D0qLaB.X. For the IDA algorithms, which have no termination rule, "before termination" reads
"before the first iterate that is approximately optimal on `X`"; for the regularization
algorithms the radius policy is the radii control of Theorem 13.1.19
(`Chapter13.RadiiControl`: `δ = 1` if `q ≤ 2`, achievable for `X = ℝⁿ` or for `q = 1` with `X`
convex; (12.2.51)-type bounds at every order if `q > 2`, as in the ARqp-SC row). -/

section TRqIDASC

open Chapter13 Optimization

variable {f : ℝⁿ → ℝ} {X C : Set ℝⁿ} {κg : ℕ → ℝ} {P : TRqIDAParams} {ε : ℕ → ℝ} {x₀ : ℝⁿ}
  {x : ℕ → ℝⁿ} {Δ : ℕ → ℝ} {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ}
  {dd : ℕ → ℕ → ℝⁿ} {jk : ℕ → ℕ} {s : ℕ → ℝⁿ} {acc : ℕ → Prop} {L : ℕ → ℝ} {κΔ : ℝ}

/-- **Lemma 14.2.2** of [cartis2022evaluation], TRqIDA-SC row (Lemma 13.1.5 with a feasible set):
for a TRqIDA-SC run (`Chapter13.algorithm_13_1_1_feasible`) under f.D0qL on an open convex
`C ⊇ X` and an admissible `κ_Δ` (`Chapter13.IsTRKappaDelta`, `κ_δ = κ_Δ/2`), every successful
iteration `k` (`k ∈ 𝒯`, `ρ_k ≥ η₁`) decreases `f` by at least
`η₁ (ς κ_δ)^{q+1}/(2 q!) ε_min^{q+1}` (`π_j = q + 1`, as for TRq-SC). -/
theorem lemma_14_2_2_trqida (hf : AssumptionD0qLOn f C P.q L) (hXC : X ⊆ C)
    (hrun : algorithm_13_1_1_feasible f X κg P ε x₀ x Δ h D dd jk s acc)
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ) {k : ℕ} (hk : ¬ acc k)
    (hρ : P.η₁ ≤ trqRatio f D x s jk k) :
    P.η₁ * (P.ς * (κΔ / 2)) ^ (P.q + 1) / (2 * P.q !) * epsMin P.q ε ^ (P.q + 1) ≤
      f (x k) - f (x (k + 1)) :=
  (lemma_13_1_5_feasible hf hXC hrun hκΔ hk).2 hρ

/-- **Lemma 14.2.3** of [cartis2022evaluation], TRqIDA-SC row (Lemma 13.1.1 with the radius bound
of Lemma 13.1.4, and the count of accuracy-improving iterations of Theorem 13.1.8): for a
TRqIDA-SC run under f.D0qL on an open convex `C ⊇ X` and an admissible `κ_Δ`, every iteration `k`
up to the first iterate that is approximately optimal on `X` satisfies
`k ≤ κ_uns |𝒮_k| + κ_unc` (14.2.13), with `𝒮_k` the successful iterations in `[0, k]`,
`κ_uns = 1 + log γ₃/|log γ₂|` and `κ_unc = |log(ς κ_δ ε_min/Δ₀)|/|log γ₂| + N_𝒜`, where
`N_𝒜 = q(q+1)/|log γ_h| |log ε_min| + |log(κ_acc/κ_h)|/|log γ_h| + 1` bounds the number of
accuracy-improving iterations. -/
theorem lemma_14_2_3_trqida (hf : AssumptionD0qLOn f C P.q L) (hXC : X ⊆ C)
    (hrun : algorithm_13_1_1_feasible f X κg P ε x₀ x Δ h D dd jk s acc)
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ) {k : ℕ}
    (hk : ∀ j < k, ¬ trTest_feasible f X P ε x Δ j) :
    (k : ℝ) ≤ (successSet (fun i => ¬ acc i ∧ P.η₁ ≤ trqRatio f D x s jk i) k).card *
        (1 + Real.log P.γ₃ / |Real.log P.γ₂|) +
      (|Real.log (P.ς * (κΔ / 2) * epsMin P.q ε / P.Δ₀)| / |Real.log P.γ₂| +
        (P.q * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (trKappaAcc P κΔ (lipMax L P.q + ordMax P.q κg * P.κh) (ordMax P.q κg) /
            P.κh)| / |Real.log P.γh| + 1)) := by
  have hc : 0 ≤ 1 + Real.log P.γ₃ / |Real.log P.γ₂| :=
    add_nonneg zero_le_one (div_nonneg (Real.log_nonneg P.one_le_γ₃) (abs_nonneg _))
  rcases k with _ | k
  · rw [Nat.cast_zero]; positivity
  have hk' : ∀ j ≤ k, ¬ trTest_feasible f X P ε x Δ j := fun j hj => hk j (Nat.lt_succ_of_le hj)
  have hΔmin : P.ς * (κΔ / 2) * epsMin P.q ε ≤ Δ (k + 1) :=
    (lemma_13_1_4_feasible hf hXC hrun hκΔ.1 hκΔ.2.1 hκΔ.2.2 (k + 1)).2.2.trans
      (min_le_left _ _)
  have hT := lemma_13_1_1 (fun i _ => hrun.step i) hrun.Δ_zero
    (mul_pos (mul_pos P.ς_pos (half_pos hκΔ.1)) hrun.epsMin_pos) hΔmin
  have hA := trqIDA_card_acc_le_feasible hf hXC hrun hκΔ hk'
  have hsum : ((successSet (fun i => ¬ acc i) k).card : ℝ) + (successSet acc k).card = k + 1 := by
    exact_mod_cast card_trial_add_card_acc acc k
  have hmono : ((successSet (fun i => ¬ acc i ∧ P.η₁ ≤ trqRatio f D x s jk i) k).card : ℝ) ≤
      (successSet (fun i => ¬ acc i ∧ P.η₁ ≤ trqRatio f D x s jk i) (k + 1)).card := by
    exact_mod_cast card_successSet_mono k.le_succ
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hmono hc]

/-- **Theorem 14.2.4** of [cartis2022evaluation], TRqIDA-SC row (Theorem 13.1.8 with a feasible
set): under f.bB.X, f.D0qL on an open convex `C ⊇ X` and for an admissible `κ_Δ`, every
TRqIDA-SC run has a first iterate `x_{k_ε} ∈ X` that is an `(ε, δ_ε)`-approximate `q`-th order
minimizer on `X` (`Chapter13.trTest_feasible`, `δ_ε = min(Δ_{k_ε}, ϑ) ∈ (0, 1]`), before which at
most the numbers of function and derivative evaluations of Theorem 13.1.8 are made
(`O(max_j ε_j^{-(q+1)})`). -/
theorem theorem_14_2_4_trqida (hf : AssumptionD0qLOn f C P.q L) (hXC : X ⊆ C) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : algorithm_13_1_1_feasible f X κg P ε x₀ x Δ h D dd jk s acc)
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ) :
    ∃ kε, IsFirstHit (trTest_feasible f X P ε x Δ) kε ∧ x kε ∈ X ∧ 0 < trRadius P Δ kε ∧
      trRadius P Δ kε ≤ 1 ∧
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
  obtain ⟨kε, h1, h2, h3, h4, h5⟩ := theorem_13_1_8_feasible hf hXC hb hrun hκΔ
  exact ⟨kε, h1, hrun.mem kε, h2, h3, h4, h5⟩

end TRqIDASC

section TRqEDASC

open Chapter13 Optimization

variable {f : ℝⁿ → ℝ} {X C : Set ℝⁿ} {P : TRqIDAParams} {ε : ℕ → ℝ} {x₀ : ℝⁿ} {x : ℕ → ℝⁿ}
  {Δ : ℕ → ℝ} {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ} {dd : ℕ → ℕ → ℝⁿ}
  {jk : ℕ → ℕ} {s : ℕ → ℝⁿ} {acc : ℕ → Prop} {fx fxs h₀ : ℕ → ℝ} {R : ℕ → Prop}
  {L : ℕ → ℝ} {κΔ : ℝ}

/-- **Lemma 14.2.2** of [cartis2022evaluation], TRqEDA-SC row (Lemma 13.3.2 with a feasible set):
for a TRqEDA-SC run (`Chapter13.algorithm_13_3_1_feasible`) under f.D0qL on an open convex
`C ⊇ X` and an admissible `κ_Δ` (`κ_{∇,max} = 1`, `κ_δ = κ_Δ/2`), every successful iteration `k`
before termination decreases `f` by at least `η₁ (ς κ_δ)^{q+1}/(2 q!) ε_min^{q+1}`. -/
theorem lemma_14_2_2_trqeda (hf : AssumptionD0qLOn f C P.q L) (hXC : X ⊆ C)
    (hrun : algorithm_13_3_1_feasible f X P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R)
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) 1 κΔ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ edaStopTR P ε D Δ h dd j) (ha : ¬ acc k)
    (hρ : P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement (jk i) (s i)) k) :
    P.η₁ * (P.ς * (κΔ / 2)) ^ (P.q + 1) / (2 * P.q !) * epsMin P.q ε ^ (P.q + 1) ≤
      f (x k) - f (x (k + 1)) :=
  (lemma_13_3_2_feasible hf hXC hrun hκΔ hk ha).2 hρ

/-- **Lemma 14.2.3** of [cartis2022evaluation], TRqEDA-SC row (Lemma 13.1.1 with the radius bound
of Lemma 13.1.4 for TRqEDA, and the count of accuracy-improving iterations of Theorem 13.3.4): for
a TRqEDA-SC run under f.D0qL on an open convex `C ⊇ X` and an admissible `κ_Δ`
(`κ_{∇,max} = 1`), every iteration `k` reached (up to and including termination) satisfies
`k ≤ κ_uns |𝒮_k| + κ_unc` (14.2.13) with `κ_uns = 1 + log γ₃/|log γ₂|` and
`κ_unc = |log(ς κ_δ ε_min/Δ₀)|/|log γ₂| + N_𝒜`,
`N_𝒜 = q(q+1)/|log γ_h| |log ε_min| + |log(κ_acc/κ_h)|/|log γ_h| + 1`. -/
theorem lemma_14_2_3_trqeda (hf : AssumptionD0qLOn f C P.q L) (hXC : X ⊆ C)
    (hrun : algorithm_13_3_1_feasible f X P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R)
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) 1 κΔ) {k : ℕ}
    (hk : ∀ j < k, ¬ edaStopTR P ε D Δ h dd j) :
    (k : ℝ) ≤ (successSet (fun i => ¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement (jk i) (s i)) i) k).card *
        (1 + Real.log P.γ₃ / |Real.log P.γ₂|) +
      (|Real.log (P.ς * (κΔ / 2) * epsMin P.q ε / P.Δ₀)| / |Real.log P.γ₂| +
        (P.q * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (trKappaAcc P κΔ (lipMax L P.q + P.κh) 1 / P.κh)| / |Real.log P.γh| + 1)) := by
  have hc : 0 ≤ 1 + Real.log P.γ₃ / |Real.log P.γ₂| :=
    add_nonneg zero_le_one (div_nonneg (Real.log_nonneg P.one_le_γ₃) (abs_nonneg _))
  rcases k with _ | k
  · rw [Nat.cast_zero]; positivity
  have hk' : ∀ j ≤ k, ¬ edaStopTR P ε D Δ h dd j := fun j hj => hk j (Nat.lt_succ_of_le hj)
  have hΔmin : P.ς * (κΔ / 2) * epsMin P.q ε ≤ Δ (k + 1) :=
    (trEDA_radius_ge_feasible hf hXC hrun hκΔ hk).trans (min_le_left _ _)
  have hT := lemma_13_1_1 (fun i hi => hrun.step fun j hj => hk' j (hj.trans hi)) hrun.Δ_zero
    (mul_pos (mul_pos P.ς_pos (half_pos hκΔ.1)) hrun.epsMin_pos) hΔmin
  have hA := trqEDA_card_acc_le_feasible hf hXC hrun hκΔ hk'
  have hsum : ((successSet (fun i => ¬ acc i) k).card : ℝ) + (successSet acc k).card = k + 1 := by
    exact_mod_cast card_trial_add_card_acc acc k
  have hmono : ((successSet (fun i => ¬ acc i ∧
        P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement (jk i) (s i)) i) k).card : ℝ) ≤
      (successSet (fun i => ¬ acc i ∧
        P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement (jk i) (s i)) i) (k + 1)).card := by
    exact_mod_cast card_successSet_mono k.le_succ
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hmono hc]

/-- **Theorem 14.2.4** of [cartis2022evaluation], TRqEDA-SC row (Theorem 13.3.4 with a feasible
set): under f.bB.X, f.D0qL on an open convex `C ⊇ X` and for an admissible `κ_Δ`
(`κ_{∇,max} = 1`), every TRqEDA-SC run terminates at some `k_ε` with `x_{k_ε} ∈ X` an
`(ε, δ_ε)`-approximate `q`-th order minimizer on `X`, `δ_ε = min(Δ_{k_ε}, ϑ) ∈ (0, 1]`, within
the evaluation bounds of Theorem 13.3.4 (`O(max_j ε_j^{-(q+1)})`). -/
theorem theorem_14_2_4_trqeda (hf : AssumptionD0qLOn f C P.q L) (hXC : X ⊆ C) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : algorithm_13_3_1_feasible f X P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R)
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) 1 κΔ) :
    ∃ kε, IsFirstHit (edaStopTR P ε D Δ h dd) kε ∧ x kε ∈ X ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) {e | x kε + e ∈ X} P.q ε
        (fun _ => trRadius P Δ kε) ∧
      0 < trRadius P Δ kε ∧ trRadius P Δ kε ≤ 1 ∧
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
  obtain ⟨kε, h1, h2, h3, h4, h5, h6⟩ := theorem_13_3_4_feasible hf hXC hb hrun hκΔ
  exact ⟨kε, h1, hrun.mem fun j hj => h1.2 j hj, h2, h3, h4, h5, h6⟩

end TRqEDASC

section ARqpIDASC

open Chapter13 Optimization

variable {f : ℝⁿ → ℝ} {X C : Set ℝⁿ} {κg : ℕ → ℝ} {P : ARqpIDAParams} {ε : ℕ → ℝ} {x₀ : ℝⁿ}
  {x : ℕ → ℝⁿ} {σ : ℕ → ℝ} {δ δ₁ δs : ℕ → ℕ → ℝ} {h : ℕ → ℕ → ℝ}
  {D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ} {dd : ℕ → ℕ → ℝⁿ} {jk : ℕ → ℕ} {s : ℕ → ℝⁿ}
  {acc : ℕ → Prop} {L : ℕ → ℝ}

/-- **Lemma 14.2.2** of [cartis2022evaluation], ARqpIDA-SC row (Lemma 13.1.18 with a feasible set):
for an ARqpIDA-SC run (`Chapter13.algorithm_13_1_2_feasible`) under f.D0pL on an open convex `C ⊇ X`
and the radii control at `k`, every successful iteration `k` whose successor `x_{k+1}` is not
approximately optimal on `X` decreases `f` by at least `½ η₁ κ_{Δm} min_j ε_j^{π_j}`, with `π_j =
(p+1)/(p-j+1)` if `q ≤ 2` and `π_j = j(p+1)/p` if `q > 2` (`Chapter13.arPi`) and `κ_{Δm}` of Lemma
13.1.18. The radii control `Chapter13.RadiiControl` asks `δ_{s_k} = 1` when `q ≤ 2`, which Step 2
guarantees for `X = ℝⁿ` or for `q = 1` with `X` convex (so the book's order `j(p+1)/p` for `q = 2`,
`X ≠ ℝⁿ` is not covered), and the (12.2.51)-type bounds at every order when `q > 2`. -/
theorem lemma_14_2_2_arqpida (hf : AssumptionD0pLOn f C P.p L) (hXC : X ⊆ C)
    (hrun : algorithm_13_1_2_feasible f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) {k : ℕ}
    (hrc : RadiiControl P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc k) (hk : ¬ acc k)
    (hρ : P.η₁ ≤ arqpIDARatio f P D x s k) (hnot : ¬ arTest_feasible f X P ε x (k + 1)) :
    P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConst P.q P.p (1 - P.θ)
        (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
          (arSigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
        epsMin P.q (fun j => ε j ^ arPi P.q P.p j) ≤ f (x k) - f (x (k + 1)) :=
  (lemma_13_1_18_feasible hf hXC hrun hrc hk hρ hnot).2

/-- **Lemma 14.2.3** of [cartis2022evaluation], ARqpIDA-SC row (Lemma 13.1.9 with the bound `σ_max`
of Lemma 13.1.14, and the count of accuracy-improving iterations of Theorem 13.1.19): for an
ARqpIDA-SC run under f.D0pL on an open convex `C ⊇ X` and the radii control, every iteration `k` up
to the first iterate that is approximately optimal on `X` satisfies `k ≤ κ_uns |𝒮_k| + κ_unc`
(14.2.13) with `κ_uns = 1 + |log γ₁|/log γ₂` and `κ_unc = log(σ_max/σ₀)/log γ₂ + N_𝒜`, `N_𝒜 =
p(q+1)/|log γ_h| |log ε_min| + |log(κ_acc/κ_h)|/|log γ_h| + 1`. The radii control
`Chapter13.RadiiControl` asks `δ_{s_k} = 1` when `q ≤ 2`, which Step 2 guarantees for `X = ℝⁿ` or
for `q = 1` with `X` convex (so the book's order `j(p+1)/p` for `q = 2`, `X ≠ ℝⁿ` is not covered),
and the (12.2.51)-type bounds at every order when `q > 2`. -/
theorem lemma_14_2_3_arqpida (hf : AssumptionD0pLOn f C P.p L) (hXC : X ⊆ C)
    (hrun : algorithm_13_1_2_feasible f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    (hrc : ∀ i, RadiiControl P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i) {k : ℕ}
    (hk : ∀ j < k, ¬ arTest_feasible f X P ε x j) :
    (k : ℝ) ≤ (successSet (fun i => ¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i) k).card *
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
      (Real.log (arSigmaMax P (L P.p) (ordMax P.p κg) / P.σ₀) / Real.log P.γ₂ +
        (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arSigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
              (arSigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| /
            |Real.log P.γh| + 1)) := by
  have hc : 0 ≤ 1 + |Real.log P.γ₁| / Real.log P.γ₂ :=
    add_nonneg zero_le_one (div_nonneg (abs_nonneg _) P.log_γ₂_pos.le)
  have hσ : 0 ≤ Real.log (arSigmaMax P (L P.p) (ordMax P.p κg) / P.σ₀) / Real.log P.γ₂ :=
    div_nonneg (Real.log_nonneg ((one_le_div P.σ₀_pos).2 (le_max_left _ _))) P.log_γ₂_pos.le
  rcases k with _ | k
  · rw [Nat.cast_zero]; positivity
  have hk' : ∀ j ≤ k, ¬ arTest_feasible f X P ε x j := fun j hj => hk j (Nat.lt_succ_of_le hj)
  have hT := lemma_13_1_9 (fun i _ => hrun.step i) hrun.σ_zero hrun.δ_zero hrun.h_zero
    (lemma_13_1_14_feasible hf hXC hrun (k + 1))
  have hA := arqpIDA_card_acc_le_feasible hf hXC hrun hrc hk'
  have hsum : ((successSet (fun i => ¬ acc i) k).card : ℝ) + (successSet acc k).card = k + 1 := by
    exact_mod_cast card_trial_add_card_acc acc k
  have hmono : ((successSet (fun i => ¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i) k).card : ℝ) ≤
      (successSet (fun i => ¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i) (k + 1)).card := by
    exact_mod_cast card_successSet_mono k.le_succ
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hmono hc]

/-- **Theorem 14.2.4** of [cartis2022evaluation], ARqpIDA-SC row (Theorem 13.1.19 with a feasible
set): under f.bB.X, f.D0pL on an open convex `C ⊇ X` and the radii control at every iteration, every
ARqpIDA-SC run reaches a first iterate `x_{k_ε} ∈ X` that is an `(ε, δ_ε)`-approximate `q`-th order
minimizer on `X` for some radii `δ_ε ∈ (0, 1]^q` (`Chapter13.arTest_feasible`), before which at most
`(1 + |log γ₁|/log γ₂) (f(x₀) - f_low)/c + κ^C` function evaluations and `(f(x₀) - f_low)/c + κ^E
|log ε_min| + κ^F + 3` derivative estimates are made, where `c = ½ η₁ κ_{Δm} min_j ε_j^{π_j}` is the
decrease of Lemma 14.2.2 (`π_j = (p+1)/(p-j+1)` for `q ≤ 2`, `j(p+1)/p` for `q > 2`), and the
constants are those of Theorem 13.1.19. The radii control `Chapter13.RadiiControl` asks `δ_{s_k} =
1` when `q ≤ 2`, which Step 2 guarantees for `X = ℝⁿ` or for `q = 1` with `X` convex (so the book's
order `j(p+1)/p` for `q = 2`, `X ≠ ℝⁿ` is not covered), and the (12.2.51)-type bounds at every order
when `q > 2`. -/
theorem theorem_14_2_4_arqpida (hf : AssumptionD0pLOn f C P.p L) (hXC : X ⊆ C) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : algorithm_13_1_2_feasible f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    (hrc : ∀ i, RadiiControl P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i) :
    ∃ kε, IsFirstHit (arTest_feasible f X P ε x) kε ∧ x kε ∈ X ∧
      (derivEvalCount (fun i => ¬ acc i) kε : ℝ) ≤
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) * ((f x₀ - flow) /
          (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConst P.q P.p (1 - P.θ)
            (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arSigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
            epsMin P.q (fun j => ε j ^ arPi P.q P.p j))) +
          (Real.log (arSigmaMax P (L P.p) (ordMax P.p κg) / P.σ₀) / Real.log P.γ₂ + 2 +
            |Real.log P.γ₁| / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i)) kε : ℝ) ≤
        (f x₀ - flow) /
          (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConst P.q P.p (1 - P.θ)
            (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arSigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
            epsMin P.q (fun j => ε j ^ arPi P.q P.p j)) +
          P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arSigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
              (arSigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| /
            |Real.log P.γh| + 3 := by
  have hLb := hrun.one_le_Lbar hf
  have hA := one_le_arConstA (hf.one_le le_rfl) hrun.kappaMax_nonneg (P := P) (L := L)
  have hC := arStepConst_pos (q := P.q) (p := P.p) (sub_pos.2 P.θ_lt_one)
    (zero_lt_one.trans_le hA) (arKappaDelta1_pos (Lb := lipMax L P.p + ordMax P.p κg * P.κh)
      (σ := arSigmaMax P (L P.p) (ordMax P.p κg)) (P := P) (by linarith))
  have hm : 0 < epsMin P.q (fun j => ε j ^ arPi P.q P.p j) :=
    Chapter13.epsMin_pos P.one_le_q fun j hj => Real.rpow_pos_of_pos (hrun.eps_mem j hj).1 _
  have hc : 0 < P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConst P.q P.p (1 - P.θ)
      (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
        (arSigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
      epsMin P.q (fun j => ε j ^ arPi P.q P.p j) := by
    have := P.η₁_pos; have := P.σmin_pos; positivity
  obtain ⟨kε, hk, h1, h2⟩ := arqpIDA_complexity_feasible hf hXC hb hrun hrc hc
    fun k hk hρ hnot => (lemma_13_1_18_feasible hf hXC hrun (hrc k) hk hρ hnot).2
  exact ⟨kε, hk, hrun.mem kε, h1, h2⟩

end ARqpIDASC

section ARqpEDASC

open Chapter13 Optimization

variable {f : ℝⁿ → ℝ} {X C : Set ℝⁿ} {P : ARqpIDAParams} {ε : ℕ → ℝ} {x₀ : ℝⁿ} {x : ℕ → ℝⁿ}
  {σ : ℕ → ℝ} {δ δ₁ δs : ℕ → ℕ → ℝ} {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ}
  {dd : ℕ → ℕ → ℝⁿ} {jk : ℕ → ℕ} {s : ℕ → ℝⁿ} {acc : ℕ → Prop} {fx fxs h₀ : ℕ → ℝ}
  {R : ℕ → Prop} {L : ℕ → ℝ}

/-- **Lemma 14.2.2** of [cartis2022evaluation], ARqpEDA-SC row (Lemma 13.3.7 with a feasible set):
for an ARqpEDA-SC run (`Chapter13.algorithm_13_3_2_feasible`) under f.D0pL on an open convex `C ⊇
X`, the radii control at `k` and `θ < ς/2`, every successful iteration `k` before termination with
`‖s_k‖ ≥ 1` or such that Step 1 at `k + 1` does not pass with unchanged radii decreases `f` by at
least `½ η₁ κ'_{Δm} min_j ε_j^{π_j}` (`π_j = Chapter13.arPi q p j`, `κ'_{Δm}` of Lemma 13.3.7). The
radii control `Chapter13.RadiiControl` asks `δ_{s_k} = 1` when `q ≤ 2`, which Step 2 guarantees for
`X = ℝⁿ` or for `q = 1` with `X` convex (so the book's order `j(p+1)/p` for `q = 2`, `X ≠ ℝⁿ` is not
covered), and the (12.2.51)-type bounds at every order when `q > 2`. -/
theorem lemma_14_2_2_arqpeda (hf : AssumptionD0pLOn f C P.p L) (hXC : X ⊆ C)
    (hrun : algorithm_13_3_2_feasible f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    {k : ℕ} (hrc : RadiiControl P ε (lipMax L P.p + P.κh) σ δs s acc k) (hθ : P.θ < P.ς / 2)
    (hk : ∀ j ≤ k, ¬ edaStopAR P ε D δ₁ h dd j) (ha : ¬ acc k)
    (hρ : P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) k)
    (hgood : 1 ≤ ‖s k‖ ∨ ¬ edaPassUnchanged P ε D δ δ₁ dd (k + 1)) :
    P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConst P.q P.p (P.ς / 2 - P.θ)
        (arEDAConstA P L) (arKappaDelta1 P (lipMax L P.p + P.κh) (arSigmaMax P (L P.p) 1))) /
        2 * epsMin P.q (fun j => ε j ^ arPi P.q P.p j) ≤ f (x k) - f (x (k + 1)) :=
  (lemma_13_3_7_feasible hf hXC hrun hrc hθ hk ha hρ hgood).2

/-- **Lemma 14.2.3** of [cartis2022evaluation], ARqpEDA-SC row (Lemma 13.1.9 with the bound `σ_max`
of Lemma 13.3.5, and the count of accuracy-improving iterations of Theorem 13.3.8): for an
ARqpEDA-SC run under f.D0pL on an open convex `C ⊇ X` and the radii control, every iteration `k`
reached (up to and including termination) satisfies `k ≤ κ_uns |𝒮_k| + κ_unc` (14.2.13) with `κ_uns
= 1 + |log γ₁|/log γ₂` and `κ_unc = log(σ_max/σ₀)/log γ₂ + N_𝒜`, `N_𝒜 = p(q+1)/|log γ_h| |log ε_min|
+ |log(κ_acc/κ_h)|/|log γ_h| + 1`. The radii control `Chapter13.RadiiControl` asks `δ_{s_k} = 1`
when `q ≤ 2`, which Step 2 guarantees for `X = ℝⁿ` or for `q = 1` with `X` convex (so the book's
order `j(p+1)/p` for `q = 2`, `X ≠ ℝⁿ` is not covered), and the (12.2.51)-type bounds at every order
when `q > 2`. -/
theorem lemma_14_2_3_arqpeda (hf : AssumptionD0pLOn f C P.p L) (hXC : X ⊆ C)
    (hrun : algorithm_13_3_2_feasible f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hrc : ∀ i, RadiiControl P ε (lipMax L P.p + P.κh) σ δs s acc i) {k : ℕ}
    (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) :
    (k : ℝ) ≤ (successSet (fun i => ¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i) k).card *
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
      (Real.log (arSigmaMax P (L P.p) 1 / P.σ₀) / Real.log P.γ₂ +
        (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
            (arSigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh) (arSigmaMax P (L P.p) 1) 1 /
            P.κh)| / |Real.log P.γh| + 1)) := by
  have hc : 0 ≤ 1 + |Real.log P.γ₁| / Real.log P.γ₂ :=
    add_nonneg zero_le_one (div_nonneg (abs_nonneg _) P.log_γ₂_pos.le)
  have hσ : 0 ≤ Real.log (arSigmaMax P (L P.p) 1 / P.σ₀) / Real.log P.γ₂ :=
    div_nonneg (Real.log_nonneg ((one_le_div P.σ₀_pos).2 (le_max_left _ _))) P.log_γ₂_pos.le
  rcases k with _ | k
  · rw [Nat.cast_zero]; positivity
  have hk' : ∀ j ≤ k, ¬ edaStopAR P ε D δ₁ h dd j := fun j hj => hk j (Nat.lt_succ_of_le hj)
  have hT := lemma_13_1_9 (fun i hi => hrun.step fun j hj => hk' j (hj.trans hi))
    hrun.σ_zero hrun.δ_zero hrun.h_zero (lemma_13_3_5_feasible hf hXC hrun hk)
  have hA := arqpEDA_card_acc_le_feasible hf hXC hrun hrc hk'
  have hsum : ((successSet (fun i => ¬ acc i) k).card : ℝ) + (successSet acc k).card = k + 1 := by
    exact_mod_cast card_trial_add_card_acc acc k
  have hmono : ((successSet (fun i => ¬ acc i ∧
        P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i) k).card : ℝ) ≤
      (successSet (fun i => ¬ acc i ∧
        P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i) (k + 1)).card := by
    exact_mod_cast card_successSet_mono k.le_succ
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hmono hc]

/-- **Theorem 14.2.4** of [cartis2022evaluation], ARqpEDA-SC row (Theorem 13.3.8 with a feasible
set): under f.bB.X, f.D0pL on an open convex `C ⊇ X`, the radii control at every iteration and `θ <
ς/2`, every ARqpEDA-SC run terminates at some `k_ε` with `x_{k_ε} ∈ X` an `(ε,
δ^{(1)}_{k_ε})`-approximate `q`-th order minimizer on `X`, `δ^{(1)}_{k_ε} ∈ (0, 1]^q`, after at most
`2 ((N + M + 1) c_T + log(σ_max/σ₀)/log γ₂)` inexact function evaluations and `N + 2M + 2`
derivative estimates, where `N = (f(x₀) - f_low)/c` with `c = ½ η₁ κ'_{Δm} min_j ε_j^{π_j}` the
decrease of Lemma 14.2.2 (`π_j = Chapter13.arPi q p j`), `M = p(q+1)/|log γ_h| |log ε_min| +
|log(κ_acc/κ_h)|/|log γ_h| + 1` and `c_T = 1 + |log γ₁|/log γ₂` (as in Theorem 13.3.8). The radii
control `Chapter13.RadiiControl` asks `δ_{s_k} = 1` when `q ≤ 2`, which Step 2 guarantees for `X =
ℝⁿ` or for `q = 1` with `X` convex (so the book's order `j(p+1)/p` for `q = 2`, `X ≠ ℝⁿ` is not
covered), and the (12.2.51)-type bounds at every order when `q > 2`. -/
theorem theorem_14_2_4_arqpeda (hf : AssumptionD0pLOn f C P.p L) (hXC : X ⊆ C) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : algorithm_13_3_2_feasible f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hrc : ∀ i, RadiiControl P ε (lipMax L P.p + P.κh) σ δs s acc i) (hθ : P.θ < P.ς / 2) :
    ∃ kε, IsFirstHit (edaStopAR P ε D δ₁ h dd) kε ∧ x kε ∈ X ∧
      (∀ j ∈ Finset.Icc 1 P.q, δ₁ kε j ∈ Set.Ioc 0 1) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) {e | x kε + e ∈ X} P.q ε (δ₁ kε) ∧
      (edaFunEvalCount acc R kε : ℝ) ≤
        2 * (((f x₀ - flow) / (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConst P.q P.p
              (P.ς / 2 - P.θ) (arEDAConstA P L)
              (arKappaDelta1 P (lipMax L P.p + P.κh) (arSigmaMax P (L P.p) 1))) / 2 *
              epsMin P.q (fun j => ε j ^ arPi P.q P.p j)) +
            (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
              |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
                (arSigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh) (arSigmaMax P (L P.p) 1) 1 /
                P.κh)| / |Real.log P.γh| + 1) + 1) *
            (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
          Real.log (arSigmaMax P (L P.p) 1 / P.σ₀) / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i)) kε : ℝ) ≤
        (f x₀ - flow) / (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConst P.q P.p
            (P.ς / 2 - P.θ) (arEDAConstA P L)
            (arKappaDelta1 P (lipMax L P.p + P.κh) (arSigmaMax P (L P.p) 1))) / 2 *
            epsMin P.q (fun j => ε j ^ arPi P.q P.p j)) +
          2 * (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
            |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
              (arSigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh) (arSigmaMax P (L P.p) 1) 1 /
              P.κh)| / |Real.log P.γh| + 1) + 2 := by
  have hLb : 1 ≤ lipMax L P.p + P.κh := by
    have := hf.one_le_lipMax; have := P.κh_nonneg; linarith
  have hA := one_le_arEDAConstA (P := P) (hf.one_le le_rfl)
  have hC := arStepConst_pos (q := P.q) (p := P.p) (sub_pos.2 hθ)
    (zero_lt_one.trans_le hA) (arKappaDelta1_pos (Lb := lipMax L P.p + P.κh)
      (σ := arSigmaMax P (L P.p) 1) (P := P) (by linarith))
  have hm : 0 < epsMin P.q (fun j => ε j ^ arPi P.q P.p j) :=
    Chapter13.epsMin_pos P.one_le_q fun j hj => Real.rpow_pos_of_pos (hrun.eps_mem j hj).1 _
  have hc : 0 < P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConst P.q P.p (P.ς / 2 - P.θ)
      (arEDAConstA P L) (arKappaDelta1 P (lipMax L P.p + P.κh) (arSigmaMax P (L P.p) 1))) / 2 *
      epsMin P.q (fun j => ε j ^ arPi P.q P.p j) := by
    have := P.η₁_pos; have := P.σmin_pos; positivity
  obtain ⟨kε, hk, hmem, happ, h1, h2⟩ := arqpEDA_complexity_feasible hf hXC hb hrun hrc hc
    fun k hk ha hρ hgood => (lemma_13_3_7_feasible hf hXC hrun (hrc k) hθ hk ha hρ hgood).2
  exact ⟨kε, hk, hrun.mem fun j hj => hk.2 j hj, hmem, happ, h1, h2⟩

end ARqpEDASC

/-- **Theorem 14.2.4** of [cartis2022evaluation], sharpness: the orders of the TRq-SC row
(`ε^{-(q+1)}`), of the ARqp-SC row for `q ≤ 2` (`ε^{-(p+1)/(p-q+1)}`) and of the ARqpC-SC row
for `q = 1` and convex `h` (`ε^{-(p+1)/p}`) are attained, by the slow examples of
Theorem 12.2.6, Corollary 12.2.16 and Corollary 14.1.11 run with the (simple) feasible set
`X = ℝ` (`univ`; `X = ℝ¹` and `h = ‖·‖` for ARqpC-SC). The ARqp-SC row for `q ≥ 3` is
`theorem_14_2_4_sharp_arqp`; the IDA/EDA rows are not stated. -/
theorem theorem_14_2_4_sharp {p q : ℕ} (hq : 1 ≤ q) :
    (∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / q ! → ∀ P : Optimization.TRqParams,
      P.Δ₀ = ε → ∃ f : ℝ → ℝ, (∀ t, flow ≤ f t) ∧ Chapter12.AssumptionD1pL f q (fun _ => L) ∧
        ∃ (x s : ℕ → ℝ) (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → ℝ),
          Chapter12.algorithm_12_2_1_feasible f univ P q (fun j => j ! * ε) 1 x s Δ jk d ∧
          Optimization.IsFirstHit (Chapter12.trqStop f P q (fun j => j ! * ε) 1 x Δ d)
            ⌈(ε ^ (q + 1))⁻¹⌉₊ ∧
          (ε ^ (q + 1))⁻¹ + 1 ≤ (Optimization.funEvalCount ⌈(ε ^ (q + 1))⁻¹⌉₊ : ℝ)) ∧
    (q ≤ 2 → q ≤ p → ∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ P : Optimization.ARqpParams, P.σ₀ = (p ! : ℝ) / (q - 1)! →
      ∃ f : ℝ → ℝ, (∀ t, flow ≤ f t) ∧ Chapter12.AssumptionD1pL f p (fun _ => L) ∧
        ∃ (x s σ : ℕ → ℝ) (d : ℕ → ℕ → ℝ),
          Chapter12.algorithm_12_2_2_feasible f univ P p q (fun _ => ε) (fun _ => 1) x s σ
            (fun _ _ => 1) (fun _ _ => 1) d (fun _ _ => 0) ∧
          Optimization.IsFirstHit (Chapter12.arqpStop f P p q (fun _ => ε) x s σ (fun _ _ => 1) d)
            ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊) ∧
    (1 ≤ p → ∀ P : ARqpCParams, ∃ L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ c : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1),
        AssumptionCD1pL c p (fun _ => L) ∧ ‖c 0‖ ≤ L ∧
        AssumptionWBb (fun _ => 0) c (fun v => ‖v‖) univ 0 ∧
        ∃ (x s : ℕ → EuclideanSpace ℝ (Fin 1)) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ)
          (d dm : ℕ → ℕ → EuclideanSpace ℝ (Fin 1)),
          algorithm_14_1_1 (fun _ => 0) c (fun v => ‖v‖) univ p 1 P (fun _ => ε) (fun _ => 1)
            x s σ δ δs d dm ∧
          Optimization.IsFirstHit
            (arqpcStop (fun _ => 0) c (fun v => ‖v‖) p 1 P (fun _ => ε) x s σ δ d)
            ⌈ε ^ (-((p + 1 : ℝ) / p))⌉₊ ∧
          ε ^ (-((p + 1 : ℝ) / p)) + 1 ≤
            (Optimization.funEvalCount ⌈ε ^ (-((p + 1 : ℝ) / p))⌉₊ : ℝ)) := by
  refine ⟨?_, fun hq2 hqp => ?_, fun hp P => ?_⟩
  · obtain ⟨flow, L, hL, H⟩ := Chapter12.theorem_12_2_6 hq
    refine ⟨flow, L, hL, fun ε hε hε1 P hP => ?_⟩
    obtain ⟨f, hb, hf, x, s, Δ, jk, d, hrun, -, -, hhit, -, hF, -⟩ := H ε hε hε1 P hP
    exact ⟨f, hb, hf, x, s, Δ, jk, d, Chapter12.algorithm_12_2_1_iff_feasible.1 hrun, hhit, hF⟩
  · obtain ⟨flow, L, hL, H⟩ := Chapter12.corollary_12_2_16 hq hq2 hqp
    refine ⟨flow, L, hL, fun ε hε hε1 P hP => ?_⟩
    obtain ⟨f, hb, hf, x, s, σ, d, hrun, -, hhit, -⟩ := H ε hε hε1 P hP
    exact ⟨f, hb, hf, x, s, σ, d, hrun, hhit⟩
  · obtain ⟨-, -, -, -, L, hL, H⟩ := corollary_14_1_11 hp P
    refine ⟨L, hL, fun ε hε hε1 => ?_⟩
    obtain ⟨c, hc, hc0, -, hw, x, s, σ, δ, δs, d, dm, hrun, -, hhit, -, hF, -⟩ := H ε hε hε1
    exact ⟨c, hc, hc0, hw, x, s, σ, δ, δs, d, dm, hrun, hhit, hF⟩

/-- **Theorem 14.2.4** of [cartis2022evaluation], sharpness of the ARqp-SC row for `q ≥ 3`
(the "otherwise" order `ε^{-q(p+1)/p}`): the slow example of Theorem 12.2.17 run with the (simple)
feasible set `X = ℝ` (`univ`). For `3 ≤ q ≤ p` there are `f_low` and `L ≥ 1` such that for every
`ε ∈ (0, ½]` and ARqp constants with `σ₀` the weight (12.2.85) there is `f` with f.bB and f.D1pL
and an ARqp-SC run with radii `ε` satisfying the radius hypothesis of `theorem_14_2_4_arqp`
(`δ_{s_k,j} ≥ κ_δ(σ_k) ε_j`) that first terminates at `k_ε = ⌈ε^{-q(p+1)/p}⌉`, after
`k_ε + 1 ≥ ε^{-q(p+1)/p} + 1` evaluations. -/
theorem theorem_14_2_4_sharp_arqp {p q : ℕ} (hq : 2 < q) (hqp : q ≤ p) :
    ∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ P : Optimization.ARqpParams,
      P.σ₀ = Chapter12.arqpSigmaSharp p q →
      ∃ f : ℝ → ℝ, (∀ t, flow ≤ f t) ∧ Chapter12.AssumptionD1pL f p (fun _ => L) ∧
        ∃ (x s σ : ℕ → ℝ) (d : ℕ → ℕ → ℝ),
          Chapter12.algorithm_12_2_2_feasible f univ P p q (fun _ => ε) (fun _ => ε) x s σ
            (fun _ _ => ε) (fun _ _ => ε) d (fun _ _ => 0) ∧
          (∀ k, (∀ i ≤ k, ¬ Chapter12.arqpStop f P p q (fun _ => ε) x s σ (fun _ _ => ε) d i) →
            ‖s k‖ < 1 → ∀ j ∈ Finset.Icc 1 q,
              Chapter12.arqpKappaDelta P (Chapter12.finMax 1 (fun _ => L) p) (σ k) * ε ≤ ε) ∧
          Optimization.IsFirstHit (Chapter12.arqpStop f P p q (fun _ => ε) x s σ (fun _ _ => ε) d)
            ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ ∧
          ε ^ (-((q : ℝ) * (p + 1) / p)) + 1 ≤
            (Optimization.funEvalCount ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ : ℝ) := by
  obtain ⟨flow, L, hL, H⟩ := Chapter12.theorem_12_2_17 (r := p) (by omega) hqp le_rfl
  refine ⟨flow, L, hL, fun ε hε hε2 P hP => ?_⟩
  obtain ⟨f, hb, hf, x, s, σ, d, hrun, -, -, hκ, -, hhit, -⟩ := H ε hε hε2 P hP
  refine ⟨f, hb, hf, x, s, σ, d, hrun, fun k _ _ _ _ => hκ k, hhit, ?_⟩
  simp only [Optimization.funEvalCount, Nat.cast_add, Nat.cast_one]
  linarith [Nat.le_ceil (ε ^ (-((q : ℝ) * (p + 1) / p)))]

end CartisGouldToint.Chapter14
