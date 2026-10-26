import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Analysis.Calculus.AnchoredLipschitz
import Numlib.Optimization.Optimality.TaylorStability
import Numlib.Optimization.Subproblem.SparseLinear
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
* `lemma_14_2_2_trq`, `theorem_14_2_4_trq` — the TRq-SC rows (from Chapter 12's TRq with a
  feasible set); `lemma_14_2_2_arqp`, `lemma_14_2_3`, `theorem_14_2_4_arqp` — the ARqp-SC rows
  (from Chapter 12's ARqp with a feasible set); `theorem_14_2_4_sharp` — sharpness of the TRq-SC
  and ARqp-SC (`q ≤ 2`) orders with `X = ℝ`;
* bridges: `AssumptionD1qLaBX.of_lipschitzOn`, `AssumptionD1qLaBX.assumptionD1pLOn`,
  `assumptionBbX_iff_assumptionWBb`.

## Deviations from the book

* Theorem 14.2.1: the Lipschitz condition is required on the closed ball of radius `δ_j` around
  `x_ε` (implied by the printed open ball of radius larger than `δ_j`); `X` closed and nonempty,
  `δ_j ≤ 1` and `ε_j ≤ 1` are not needed. The printed `δ^j` in (14.2.6) is `δ_j^j`. The radius
  condition `‖d‖ ≤ (j+1)ε_j/L_{f,j}` is used in the equivalent form `L_{f,j} ‖d‖ ≤ (j+1) ε_j`.
* (14.2.18)–(14.2.19) print `max ℓ(d)`; the measure (14.2.17) and Lemma 14.2.5 need the minimum
  of `ℓ(d) = ⟨∇f(x), d⟩`.

## Not formalized here

* The TRqIDA/EDA and ARqpIDA/EDA rows of Lemmas 14.2.2–14.2.3 and Theorem 14.2.4 (the
  Chapter 13 run predicates carry no feasible set), and the TR rows of Lemma 14.2.3 (they need the
  radius lower bound of Lemma 12.2.3 with a feasible set).
* The anchored assumptions f.D1qLaB.X: the rows formalized here assume f.D1pL (or f.D1qL) on an
  open convex superset `C` of `X` (`Chapter12.AssumptionD1pLOn`; for ARqpC-SC on `ℝⁿ`), which
  `AssumptionD1qLaBX.assumptionD1pLOn` yields when the anchor set is all of `X₀`; the book's
  remark that only anchored conditions are used by the proofs is not formalized.
* Sharpness of the ARqpC-SC row (Corollary 14.1.11) and of the ARqp-SC row for `q ≥ 3` (the
  Chapter 12 slow example is a genuine ARqp run only for `q ≤ 2`).
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
`κ_unc = log(σ_max/σ₀)/log γ₂`. The ARqpC-SC row is `lemma_14_2_3_arqpc`; the TR rows (which need
the radius lower bound of Lemma 12.2.3 with a feasible set) are not stated. -/
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

/-- **Theorem 14.2.4** of [cartis2022evaluation], sharpness: the orders of the TRq-SC row
(`ε^{-(q+1)}`) and of the ARqp-SC row for `q ≤ 2` (`ε^{-(p+1)/(p-q+1)}`) are attained, by the
slow examples of Theorem 12.2.6 and Corollary 12.2.16 run with the (simple) feasible set
`X = ℝ` (`univ`). (The ARqpC-SC row would need Corollary 14.1.11, which is not formalized; the
IDA/EDA rows are not stated.) -/
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
            ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊) := by
  refine ⟨?_, fun hq2 hqp => ?_⟩
  · obtain ⟨flow, L, hL, H⟩ := Chapter12.theorem_12_2_6 hq
    refine ⟨flow, L, hL, fun ε hε hε1 P hP => ?_⟩
    obtain ⟨f, hb, hf, x, s, Δ, jk, d, hrun, -, -, hhit, -, hF, -⟩ := H ε hε hε1 P hP
    exact ⟨f, hb, hf, x, s, Δ, jk, d, Chapter12.algorithm_12_2_1_iff_feasible.1 hrun, hhit, hF⟩
  · obtain ⟨flow, L, hL, H⟩ := Chapter12.corollary_12_2_16 hq hq2 hqp
    refine ⟨flow, L, hL, fun ε hε hε1 P hP => ?_⟩
    obtain ⟨f, hb, hf, x, s, σ, d, hrun, -, hhit, -⟩ := H ε hε hε1 P hP
    exact ⟨f, hb, hf, x, s, σ, d, hrun, hhit⟩

end CartisGouldToint.Chapter14
