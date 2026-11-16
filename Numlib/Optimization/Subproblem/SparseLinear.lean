/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.ModelBased.HighOrder.MeasureTest
import Mathlib.Basic.Real.Sign

/-!
# Sparse linear minimization over an $\ell_\infty$ ball

Let $x, g \in \mathbb{R}^n$, $\delta \ge 0$ and $n_{nz} \in \mathbb{N}$, and write $\|y\|_0$ for the
number of nonzero components of $y$. This file solves the problem of minimizing the linear function
$\ell(d) = \sum_i g_i d_i$ over the displacements $d$ with $\|d\|_\infty \le \delta$ and
$\|x + d\|_0 \le n_{nz}$. This is the subproblem of §14.2.2.2 and Lemma 14.2.5 of
[cartis2022evaluation] that makes sparsity constraints simple for first-order trust-region and
regularization methods. Let $\mathcal{A}_\delta(x) = \{i : |x_i| > \delta\}$ be the set of
components that no feasible displacement can make zero. A minimizer moves each component in
$\mathcal{A}_\delta(x)$ to the face $-\delta \operatorname{sign}(g_i)$ of the ball, and for each
other component chooses between this face and the value $x_i + d_i = 0$. The choice is a 0-1
knapsack problem (14.2.21), and the optimal value of the subproblem is
$$\min \ell = -\delta \sum_{i \in \mathcal{A}_\delta(x)} |g_i| - \sum_{i \notin
  \mathcal{A}_\delta(x)} x_i g_i - \kappa,$$
where $\kappa$ is the optimal value of the knapsack problem.

As a consequence, the first-order criticality measure (14.2.17) of the sparsity-constrained problem,
which is $-\min \ell$, has a closed form that needs no evaluation of the objective function beyond
its gradient.

## Main definitions

* `Subproblem.sparseSet`: the sparsity set $\{x : \|x\|_0 \le n_{nz}\}$ of (14.2.14).
* `Subproblem.nzSet`: the support $\mathcal{A}(x) = \{i : x_i \neq 0\}$ of (14.2.15).
* `Subproblem.activeSet`: the set $\mathcal{A}_\delta(x) = \{i : |x_i| > \delta\}$.
* `Subproblem.sparseLinearStep`: the step (14.2.20).
* `Subproblem.knapsackValue`, `Subproblem.KnapsackFeasible`, `Subproblem.knapsackOpt`: the
  objective, the constraint and the optimal value of the knapsack problem (14.2.21).

## Main results

* `Subproblem.isMinOn_sparseLinearStep`: Lemma 14.2.5, as a minimization: for an optimal knapsack
  selection, the step (14.2.20) minimizes $\ell$ over the feasible displacements. Its value is
  `Subproblem.sum_mul_sparseLinearStep`.
* `Subproblem.exists_knapsackFeasible_opt`, `Subproblem.exists_isMinOn_sparseLinearStep`,
  `Subproblem.exists_isMinOn_sparse`: optimal selections and minimizing steps exist when $x$ is
  sparse.
* `Subproblem.isApproxMeasureStep_sparseLinearStep`: the step is an approximate optimality
  displacement in the sense of `Optimization.IsApproxMeasureStep`.
* `Subproblem.taylorMeasure_sparse_eq`: the measure (14.2.17) in closed form.

## Implementation notes

* The space is `Fin n → ℝ` with the sup norm of Mathlib, so that `Metric.closedBall 0 δ` is the
  $\ell_\infty$ ball of the source and `Optimization.taylorMeasure` on this space is the measure
  (14.2.17).
* The subproblem (14.2.18)–(14.2.19) is stated as the minimization of $\ell$, as the measure
  requires: $\varphi = f(x) - \min T_{f,1}(x, \cdot) = -\min \ell$. Its solution (14.2.20) is a
  minimizer.
* Lemma 14.2.5 is stated for any optimal selection $\tau$ of the knapsack problem (14.2.21). Such a
  selection exists because there are finitely many selections.
* A selection is a function `Fin n → Bool`; the value `true` stands for $\tau_i = 1$.
-/

open Set Metric Finset
open scoped BigOperators

namespace Subproblem

variable {n nnz : ℕ}

/-! ### The sparsity set -/

/-- The **support** $\mathcal{A}(x) = \{i : x_i \neq 0\}$ of $x \in \mathbb{R}^n$, as in (14.2.15)
of [cartis2022evaluation]. Its cardinality is $\|x\|_0$. -/
noncomputable def nzSet (x : Fin n → ℝ) : Finset (Fin n) := Finset.univ.filter (fun i => x i ≠ 0)

/-- The **sparsity set** $\{x \in \mathbb{R}^n : \|x\|_0 \le n_{nz}\}$ of the vectors with at most
$n_{nz}$ nonzero components, where $\|x\|_0$ is the cardinality of the support
`Subproblem.nzSet`. This is (14.2.14) of [cartis2022evaluation]. -/
def sparseSet (n nnz : ℕ) : Set (Fin n → ℝ) := {x | (nzSet x).card ≤ nnz}

/-- A vector $x$ lies in the sparsity set if and only if its support has at most $n_{nz}$ elements.
-/
theorem mem_sparseSet {x : Fin n → ℝ} : x ∈ sparseSet n nnz ↔ (nzSet x).card ≤ nnz := Iff.rfl

/-- An index $i$ lies in the support of $x$ if and only if $x_i \neq 0$. -/
theorem mem_nzSet {x : Fin n → ℝ} {i : Fin n} : i ∈ nzSet x ↔ x i ≠ 0 := by simp [nzSet]

/-- The zero vector lies in the sparsity set. -/
theorem zero_mem_sparseSet : (0 : Fin n → ℝ) ∈ sparseSet n nnz := by
  simp [mem_sparseSet, nzSet]

/-- The sparsity set is closed. Near a point, the support can only grow. -/
theorem isClosed_sparseSet : IsClosed (sparseSet n nnz) := by
  rw [← isOpen_compl_iff]
  refine isOpen_iff_mem_nhds.2 fun x hx => ?_
  have hU : IsOpen (⋂ i ∈ nzSet x, {y : Fin n → ℝ | y i ≠ 0}) :=
    isOpen_biInter_finset fun i _ => isOpen_ne_fun (continuous_apply i) continuous_const
  refine Filter.mem_of_superset (hU.mem_nhds (mem_iInter₂.2 fun i hi => mem_nzSet.1 hi))
    fun y hy => ?_
  have hsub : nzSet x ⊆ nzSet y := fun i hi => mem_nzSet.2 (mem_iInter₂.1 hy i hi)
  simp only [mem_compl_iff, mem_sparseSet, not_le] at hx ⊢
  exact hx.trans_le (Finset.card_le_card hsub)

/-- The sparsity set is all of $\mathbb{R}^n$ if and only if $n \le n_{nz}$. -/
theorem sparseSet_eq_univ_iff : sparseSet n nnz = univ ↔ n ≤ nnz := by
  constructor
  · intro h
    have h1 : (fun _ => (1 : ℝ)) ∈ sparseSet n nnz := h ▸ mem_univ _
    simpa [mem_sparseSet, nzSet] using h1
  · intro h
    refine eq_univ_of_forall fun x => ?_
    exact (card_le_univ _).trans (by simpa using h)

/-- The sparsity set is not convex in general: the set $\{x \in \mathbb{R}^2 : \|x\|_0 \le 1\}$
contains $e_1$ and $e_2$ but not their midpoint. -/
theorem not_convex_sparseSet : ¬ Convex ℝ (sparseSet 2 1) := by
  intro h
  have h0 : (Pi.single 0 1 : Fin 2 → ℝ) ∈ sparseSet 2 1 := by
    rw [mem_sparseSet]
    refine (Finset.card_le_card (t := {0}) fun i hi => ?_).trans (by simp)
    rw [mem_nzSet] at hi
    by_contra hne
    exact hi (Pi.single_eq_of_ne (by simpa using hne) _)
  have h1 : (Pi.single 1 1 : Fin 2 → ℝ) ∈ sparseSet 2 1 := by
    rw [mem_sparseSet]
    refine (Finset.card_le_card (t := {1}) fun i hi => ?_).trans (by simp)
    rw [mem_nzSet] at hi
    by_contra hne
    exact hi (Pi.single_eq_of_ne (by simpa using hne) _)
  have hm := h h0 h1 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  rw [mem_sparseSet] at hm
  have : nzSet ((1 / 2 : ℝ) • (Pi.single 0 1 : Fin 2 → ℝ) + (1 / 2 : ℝ) • Pi.single 1 1) =
      Finset.univ := by
    ext i
    fin_cases i <;> simp [mem_nzSet]
  rw [this] at hm
  simp at hm

/-! ### The step (14.2.20) -/

/-- The set $\mathcal{A}_\delta(x) = \{i : |x_i| > \delta\}$ of the large components of $x$. No
displacement $d$ with $\|d\|_\infty \le \delta$ can make such a component of $x + d$ zero. -/
noncomputable def activeSet (x : Fin n → ℝ) (δ : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => δ < |x i|)

/-- An index $i$ lies in $\mathcal{A}_\delta(x)$ if and only if $|x_i| > \delta$. -/
theorem mem_activeSet {x : Fin n → ℝ} {δ : ℝ} {i : Fin n} : i ∈ activeSet x δ ↔ δ < |x i| := by
  simp [activeSet]

/-- The **step of Lemma 14.2.5** of [cartis2022evaluation], (14.2.20). For a selection
$\tau \in \{0, 1\}^n$, its components are
$$d_i = \begin{cases} -\delta \operatorname{sign}(g_i), & i \in \mathcal{A}_\delta(x), \\
  -\delta \operatorname{sign}(g_i), & i \notin \mathcal{A}_\delta(x), \ \tau_i = 1, \\ -x_i, & i
  \notin \mathcal{A}_\delta(x), \ \tau_i = 0. \end{cases}$$
On $\mathcal{A}_\delta(x)$ the step moves to the far face of the ball; on the complement it
either makes the component of $x + d$ zero or moves to the far face.

The source writes the components off $\mathcal{A}_\delta(x)$ as $-x_i - \tau_i (\delta
\operatorname{sign}(g_i) - x_i)$, which simplifies to the two cases above. The selection is a
function `Fin n → Bool`. The sign function is `Real.sign`. -/
noncomputable def sparseLinearStep (x g : Fin n → ℝ) (δ : ℝ) (τ : Fin n → Bool) :
    Fin n → ℝ :=
  fun i => if δ < |x i| then -δ * Real.sign (g i) else if τ i then -δ * Real.sign (g i) else -x i

/-- The objective of the knapsack problem (14.2.21) of [cartis2022evaluation]:
$$\sum_{i \notin \mathcal{A}_\delta(x)} \tau_i \bigl(\delta |g_i| - x_i g_i\bigr).$$
-/
noncomputable def knapsackValue (x g : Fin n → ℝ) (δ : ℝ) (τ : Fin n → Bool) : ℝ :=
  ∑ i ∈ (activeSet x δ)ᶜ, if τ i then δ * |g i| - x i * g i else 0

/-- The constraint of the knapsack problem (14.2.21) of [cartis2022evaluation]: $\sum_{i \notin
\mathcal{A}_\delta(x)} \tau_i \le n_{nz} - |\mathcal{A}_\delta(x)|$. It is written without
truncated subtraction as $|\mathcal{A}_\delta(x)| + \sum_{i \notin \mathcal{A}_\delta(x)} \tau_i
\le n_{nz}$. -/
def KnapsackFeasible (x : Fin n → ℝ) (δ : ℝ) (nnz : ℕ) (τ : Fin n → Bool) : Prop :=
  (activeSet x δ).card + ((activeSet x δ)ᶜ.filter (fun i => τ i = true)).card ≤ nnz

/-- The optimal value of the knapsack problem (14.2.21) of [cartis2022evaluation]: the maximum of
`Subproblem.knapsackValue` over the finitely many feasible selections. If no selection is
feasible, the value is $0$, by the Lean convention for `sSup` on $\mathbb{R}$. -/
noncomputable def knapsackOpt (x g : Fin n → ℝ) (δ : ℝ) (nnz : ℕ) : ℝ :=
  sSup (knapsackValue x g δ '' {τ | KnapsackFeasible x δ nnz τ})

private theorem mul_sign_eq_abs (r : ℝ) : r * Real.sign r = |r| := by
  rcases lt_trichotomy r 0 with h | rfl | h
  · rw [Real.sign_of_neg h, abs_of_neg h]; ring
  · simp
  · rw [Real.sign_of_pos h, abs_of_pos h]; ring

private theorem abs_sign_le_one (r : ℝ) : |Real.sign r| ≤ 1 := by
  rcases lt_trichotomy r 0 with h | rfl | h
  · simp [Real.sign_of_neg h]
  · simp
  · simp [Real.sign_of_pos h]

/-- If $|d| \le \delta$, then $g d \ge -\delta |g|$. -/
private theorem neg_mul_abs_le (g d δ : ℝ) (hd : |d| ≤ δ) : -(δ * |g|) ≤ g * d := by
  have : |g * d| ≤ δ * |g| := by rw [abs_mul, mul_comm]; gcongr
  linarith [neg_abs_le (g * d)]

variable {x g : Fin n → ℝ} {δ : ℝ} {τ : Fin n → Bool}

/-- The value of the linear function at the step $d^\star$ of (14.2.20):
$$\sum_i g_i d^\star_i = -\delta \sum_{i \in \mathcal{A}_\delta(x)} |g_i| - \sum_{i \notin
  \mathcal{A}_\delta(x)} x_i g_i - \sum_{i \notin \mathcal{A}_\delta(x)} \tau_i \bigl(\delta
  |g_i| - x_i g_i\bigr).$$
-/
theorem sum_mul_sparseLinearStep :
    ∑ i, g i * sparseLinearStep x g δ τ i =
      -(δ * ∑ i ∈ activeSet x δ, |g i|) - ∑ i ∈ (activeSet x δ)ᶜ, x i * g i -
        knapsackValue x g δ τ := by
  rw [← sum_add_sum_compl (activeSet x δ), knapsackValue, mul_sum, ← sum_neg_distrib,
    sub_sub, ← sum_add_distrib]
  rw [sub_eq_add_neg, ← sum_neg_distrib]
  congr 1
  · refine sum_congr rfl fun i hi => ?_
    simp only [sparseLinearStep, mem_activeSet.1 hi, ite_true]
    rw [mul_left_comm, mul_sign_eq_abs, neg_mul]
  · refine sum_congr rfl fun i hi => ?_
    have hi' : ¬ δ < |x i| := fun h => (mem_compl.1 hi) (mem_activeSet.2 h)
    simp only [sparseLinearStep, hi', ite_false]
    cases τ i
    · simp; ring
    · simp only [ite_true, mul_left_comm (g i), mul_sign_eq_abs]; ring

/-- For $\delta \ge 0$, the step lies in the $\ell_\infty$ ball of radius $\delta$:
$\|d^\star\|_\infty \le \delta$. -/
theorem norm_sparseLinearStep_le (hδ : 0 ≤ δ) : ‖sparseLinearStep x g δ τ‖ ≤ δ := by
  refine (pi_norm_le_iff_of_nonneg hδ).2 fun i => ?_
  rw [Real.norm_eq_abs]
  have hfar : |-δ * Real.sign (g i)| ≤ δ := by
    rw [abs_mul, abs_neg, abs_of_nonneg hδ]
    exact mul_le_of_le_one_right hδ (abs_sign_le_one _)
  unfold sparseLinearStep
  split_ifs with h1 h2
  · exact hfar
  · exact hfar
  · rw [abs_neg]; exact not_lt.1 h1

/-- The support of $x + d^\star$ is contained in the union of $\mathcal{A}_\delta(x)$ and the set of
selected indices $\{i \notin \mathcal{A}_\delta(x) : \tau_i = 1\}$. -/
theorem nzSet_add_sparseLinearStep_subset :
    nzSet (x + sparseLinearStep x g δ τ) ⊆
      activeSet x δ ∪ (activeSet x δ)ᶜ.filter (fun i => τ i = true) := by
  intro i hi
  rw [mem_nzSet] at hi
  by_cases h1 : δ < |x i|
  · exact mem_union_left _ (mem_activeSet.2 h1)
  · refine mem_union_right _ (mem_filter.2 ⟨mem_compl.2 fun h => h1 (mem_activeSet.1 h), ?_⟩)
    by_contra h2
    simp only [Bool.not_eq_true] at h2
    apply hi
    simp [sparseLinearStep, h1, h2]

/-- For $\delta \ge 0$, $\mathcal{A}_\delta(x) \subseteq \mathcal{A}(x)$. -/
theorem activeSet_subset_nzSet (hδ : 0 ≤ δ) : activeSet x δ ⊆ nzSet x := fun i hi =>
  mem_nzSet.2 fun h0 => by
    have := mem_activeSet.1 hi
    rw [h0, abs_zero] at this
    linarith

/-- **Lemma 14.2.5** of [cartis2022evaluation], as a minimization. Let $x, g \in \mathbb{R}^n$ and
$\delta \ge 0$, and let the selection $\tau$ solve the knapsack problem (14.2.21): $\tau$ is
feasible, and its value is at least the value of every feasible selection. Let $d^\star$ be the
step (14.2.20). Then $\|d^\star\|_\infty \le \delta$, $\|x + d^\star\|_0 \le n_{nz}$, and
$d^\star$ minimizes $\ell(d) = \sum_i g_i d_i$ over
$$\{d \in \mathbb{R}^n : \|d\|_\infty \le \delta, \ \|x + d\|_0 \le n_{nz}\}.$$

The value of $\ell$ at $d^\star$ is given by `Subproblem.sum_mul_sparseLinearStep`. The step is
`Subproblem.sparseLinearStep x g δ τ`, and the ball is `Metric.closedBall 0 δ` for the sup norm. -/
theorem isMinOn_sparseLinearStep (hδ : 0 ≤ δ)
    (hτ : KnapsackFeasible x δ nnz τ)
    (hopt : ∀ τ', KnapsackFeasible x δ nnz τ' → knapsackValue x g δ τ' ≤ knapsackValue x g δ τ) :
    ‖sparseLinearStep x g δ τ‖ ≤ δ ∧ x + sparseLinearStep x g δ τ ∈ sparseSet n nnz ∧
      IsMinOn (fun d => ∑ i, g i * d i) (closedBall 0 δ ∩ {d | x + d ∈ sparseSet n nnz})
        (sparseLinearStep x g δ τ) := by
  refine ⟨norm_sparseLinearStep_le hδ, ?_, ?_⟩
  · rw [mem_sparseSet]
    refine (Finset.card_le_card nzSet_add_sparseLinearStep_subset).trans
      ((Finset.card_union_le _ _).trans ?_)
    unfold KnapsackFeasible at hτ
    omega
  intro d ⟨hdδ, hdS⟩
  simp only [mem_ofPred_eq]
  have hdi : ∀ i, |d i| ≤ δ := fun i => by
    have := (pi_norm_le_iff_of_nonneg hδ).1 (mem_closedBall_zero_iff.1 hdδ) i
    rwa [Real.norm_eq_abs] at this
  -- the selection made by `d`
  set τ' : Fin n → Bool := fun i => decide (x i + d i ≠ 0)
  have hτ' : KnapsackFeasible x δ nnz τ' := by
    have hsub : activeSet x δ ∪ (activeSet x δ)ᶜ.filter (fun i => τ' i = true) ⊆
        nzSet (x + d) := by
      intro i hi
      rcases mem_union.1 hi with hi | hi
      · rw [mem_nzSet, Pi.add_apply]
        intro h0
        have h1 := mem_activeSet.1 hi
        have : x i = -d i := by linarith
        rw [this, abs_neg] at h1
        exact absurd (hdi i) (not_le.2 h1)
      · simpa [τ', mem_nzSet] using (mem_filter.1 hi).2
    have := (Finset.card_le_card hsub).trans (mem_sparseSet.1 hdS)
    rw [card_union_of_disjoint (disjoint_compl_right.mono_right (filter_subset _ _))] at this
    unfold KnapsackFeasible
    omega
  have hlow : -(δ * ∑ i ∈ activeSet x δ, |g i|) - ∑ i ∈ (activeSet x δ)ᶜ, x i * g i -
      knapsackValue x g δ τ' ≤ ∑ i, g i * d i := by
    rw [← sum_add_sum_compl (activeSet x δ), knapsackValue, mul_sum, ← sum_neg_distrib,
      sub_sub, ← sum_add_distrib, sub_eq_add_neg, ← sum_neg_distrib]
    refine add_le_add (sum_le_sum fun i _ => ?_) (sum_le_sum fun i _ => ?_)
    · exact neg_mul_abs_le (g i) (d i) δ (hdi i)
    · by_cases h0 : x i + d i = 0
      · have : d i = -x i := by linarith
        simp [τ', this, mul_comm]
      · simp only [τ', ne_eq, h0, not_false_eq_true, decide_true, ite_true]
        linarith [neg_mul_abs_le (g i) (d i) δ (hdi i)]
  rw [sum_mul_sparseLinearStep]
  linarith [hopt τ' hτ']

/-- If $x$ is sparse and $\delta \ge 0$, the knapsack problem (14.2.21) has an optimal selection.
There are finitely many selections, and the empty selection is feasible because
$|\mathcal{A}_\delta(x)| \le |\mathcal{A}(x)| \le n_{nz}$. -/
theorem exists_knapsackFeasible_opt (hx : x ∈ sparseSet n nnz) (hδ : 0 ≤ δ) :
    ∃ τ, KnapsackFeasible x δ nnz τ ∧
      ∀ τ', KnapsackFeasible x δ nnz τ' → knapsackValue x g δ τ' ≤ knapsackValue x g δ τ := by
  classical
  have hA : (activeSet x δ).card ≤ nnz :=
    (Finset.card_le_card (activeSet_subset_nzSet hδ)).trans hx
  have hne : (Finset.univ.filter (KnapsackFeasible x δ nnz)).Nonempty :=
    ⟨fun _ => false, mem_filter.2 ⟨mem_univ _, by simpa [KnapsackFeasible] using hA⟩⟩
  obtain ⟨τ, hτ, hmax⟩ := Finset.exists_max_image _ (knapsackValue x g δ) hne
  exact ⟨τ, (mem_filter.1 hτ).2, fun τ' hτ' => hmax τ' (mem_filter.2 ⟨mem_univ _, hτ'⟩)⟩

/-- The value of an optimal feasible knapsack selection is the optimal value
`Subproblem.knapsackOpt`. -/
theorem knapsackValue_eq_knapsackOpt (hτ : KnapsackFeasible x δ nnz τ)
    (hopt : ∀ τ', KnapsackFeasible x δ nnz τ' → knapsackValue x g δ τ' ≤ knapsackValue x g δ τ) :
    knapsackValue x g δ τ = knapsackOpt x g δ nnz := by
  have : IsGreatest (knapsackValue x g δ '' {τ | KnapsackFeasible x δ nnz τ})
      (knapsackValue x g δ τ) := ⟨⟨τ, hτ, rfl⟩, Set.forall_mem_image.2 hopt⟩
  exact this.csSup_eq.symm

/-- Lemma 14.2.5 of [cartis2022evaluation] together with the existence of a solution of the knapsack
problem. If $x$ is sparse and $\delta \ge 0$, there is an optimal feasible selection $\tau$, and
for it the step (14.2.20) lies in the ball, keeps $x + d^\star$ sparse, and minimizes $\ell$
over the feasible displacements. -/
theorem exists_isMinOn_sparseLinearStep (hx : x ∈ sparseSet n nnz) (hδ : 0 ≤ δ) :
    ∃ τ, KnapsackFeasible x δ nnz τ ∧
      (∀ τ', KnapsackFeasible x δ nnz τ' → knapsackValue x g δ τ' ≤ knapsackValue x g δ τ) ∧
      ‖sparseLinearStep x g δ τ‖ ≤ δ ∧ x + sparseLinearStep x g δ τ ∈ sparseSet n nnz ∧
      IsMinOn (fun d => ∑ i, g i * d i) (closedBall 0 δ ∩ {d | x + d ∈ sparseSet n nnz})
        (sparseLinearStep x g δ τ) := by
  obtain ⟨τ, hτ, hopt⟩ := exists_knapsackFeasible_opt (g := g) hx hδ
  exact ⟨τ, hτ, hopt, isMinOn_sparseLinearStep hδ hτ hopt⟩

/-- If $x$ is sparse and $\delta \ge 0$, the sparse linear problem (14.2.18), as a minimization, has
a solution: some $d$ with $\|d\|_\infty \le \delta$ and $\|x + d\|_0 \le n_{nz}$ minimizes
$\ell$ over all such displacements. -/
theorem exists_isMinOn_sparse (hx : x ∈ sparseSet n nnz) (hδ : 0 ≤ δ) :
    ∃ d ∈ closedBall 0 δ ∩ {d | x + d ∈ sparseSet n nnz},
      IsMinOn (fun d => ∑ i, g i * d i) (closedBall 0 δ ∩ {d | x + d ∈ sparseSet n nnz}) d := by
  obtain ⟨τ, -, -, hn, hS, hmin⟩ := exists_isMinOn_sparseLinearStep (g := g) hx hδ
  exact ⟨_, ⟨mem_closedBall_zero_iff.2 hn, hS⟩, hmin⟩

/-- The set of feasible displacements $\{d : \|x + d\|_0 \le n_{nz}\}$ is closed. -/
theorem isClosed_shift_sparseSet (x : Fin n → ℝ) :
    IsClosed {d : Fin n → ℝ | x + d ∈ sparseSet n nnz} :=
  isClosed_sparseSet.preimage (continuous_const.add continuous_id)

/-- If $x$ is sparse, the zero displacement is feasible: $\|x + 0\|_0 \le n_{nz}$. -/
theorem zero_mem_shift_sparseSet (hx : x ∈ sparseSet n nnz) :
    (0 : Fin n → ℝ) ∈ {d : Fin n → ℝ | x + d ∈ sparseSet n nnz} := by
  simpa using hx

/-- Let $D$ be a formal multilinear series whose first-order term acts as $D_1[d] = \sum_i g_i d_i$,
let $\delta \ge 0$, and let $\tau$ be an optimal feasible knapsack selection. Then the decrease
of the first-order Taylor sum along the step $d^\star$ equals the measure:
$\Delta T_1(d^\star) = \varphi^\delta_1$, where $\varphi^\delta_1$ is
`Optimization.taylorMeasure` of $D$ of order $1$ over the feasible displacements
$\{d : \|x + d\|_0 \le n_{nz}\}$. -/
theorem taylorDecrement_sparseLinearStep_eq (D : FormalMultilinearSeries ℝ (Fin n → ℝ) ℝ)
    (hg : ∀ d, D 1 (fun _ => d) = ∑ i, g i * d i) (hδ : 0 ≤ δ)
    (hτ : KnapsackFeasible x δ nnz τ)
    (hopt : ∀ τ', KnapsackFeasible x δ nnz τ' → knapsackValue x g δ τ' ≤ knapsackValue x g δ τ) :
    D.taylorDecrement 1 (sparseLinearStep x g δ τ) =
      Optimization.taylorMeasure D 1 δ {d | x + d ∈ sparseSet n nnz} := by
  obtain ⟨hn, hS, hmin⟩ := isMinOn_sparseLinearStep hδ hτ hopt
  have hdec : ∀ d, D.taylorDecrement 1 d = -∑ i, g i * d i := fun d => by
    rw [D.taylorDecrement_one_apply, hg]
  rw [Optimization.taylorMeasure_eq_sSup]
  have hG : IsGreatest (D.taylorDecrement 1 '' (closedBall 0 δ ∩ {d | x + d ∈ sparseSet n nnz}))
      (D.taylorDecrement 1 (sparseLinearStep x g δ τ)) := by
    refine ⟨⟨sparseLinearStep x g δ τ, ⟨mem_closedBall_zero_iff.2 hn, hS⟩, rfl⟩,
      Set.forall_mem_image.2 fun d hd => ?_⟩
    have := hmin hd
    simp only [mem_ofPred_eq] at this
    rw [hdec, hdec]
    linarith
  exact hG.csSup_eq.symm

/-- Let $D$ be a formal multilinear series whose first-order term acts as $D_1[d] = \sum_i g_i d_i$,
let $x$ be sparse, let $\delta \ge 0$, and let $\tau$ be an optimal feasible knapsack selection.
Then for every $\varsigma \le 1$ the step $d^\star$ is an approximate optimality displacement
(`Optimization.IsApproxMeasureStep`) for the first-order Taylor decrease, the radius $\delta$,
the feasible displacements $\{d : \|x + d\|_0 \le n_{nz}\}$ and the fraction $\varsigma$.

This connects the step to Step 1 of the methods TR1-SP and AR1-SP of [cartis2022evaluation]. -/
theorem isApproxMeasureStep_sparseLinearStep (D : FormalMultilinearSeries ℝ (Fin n → ℝ) ℝ)
    (hg : ∀ d, D 1 (fun _ => d) = ∑ i, g i * d i) (hx : x ∈ sparseSet n nnz) (hδ : 0 ≤ δ)
    (hτ : KnapsackFeasible x δ nnz τ)
    (hopt : ∀ τ', KnapsackFeasible x δ nnz τ' → knapsackValue x g δ τ' ≤ knapsackValue x g δ τ)
    {ς : ℝ} (hς : ς ≤ 1) :
    Optimization.IsApproxMeasureStep (D.taylorDecrement 1) δ {d | x + d ∈ sparseSet n nnz} ς
      (sparseLinearStep x g δ τ) := by
  obtain ⟨hn, hS, -⟩ := isMinOn_sparseLinearStep (g := g) hδ hτ hopt
  have heq := taylorDecrement_sparseLinearStep_eq D hg hδ hτ hopt
  have hM := Optimization.taylorMeasure_nonneg D 1 (zero_mem_shift_sparseSet hx) hδ
  refine ⟨⟨mem_closedBall_zero_iff.2 hn, hS⟩, ?_⟩
  change ς * Optimization.taylorMeasure D 1 δ _ ≤ _
  rw [heq]
  exact mul_le_of_le_one_left hM hς

/-- **The sparse measure** of (14.2.17) of [cartis2022evaluation], in closed form. Let $D$ be a
formal multilinear series whose first-order term acts as $D_1[d] = \sum_i g_i d_i$, where $g$ is
the gradient, let $x$ be sparse, and let $\delta \ge 0$. Then the first-order measure over $\{d
: \|d\|_\infty \le \delta, \ \|x + d\|_0 \le n_{nz}\}$ is
$$\varphi^\delta_1 = \delta \sum_{i \in \mathcal{A}_\delta(x)} |g_i| + \sum_{i \notin
  \mathcal{A}_\delta(x)} x_i g_i + \kappa,$$
where $\kappa$ is the optimal value `Subproblem.knapsackOpt` of the knapsack problem (14.2.21).
This is a consequence of Lemma 14.2.5 there.

The formula needs no evaluation of the objective function beyond its gradient. -/
theorem taylorMeasure_sparse_eq (D : FormalMultilinearSeries ℝ (Fin n → ℝ) ℝ)
    (hg : ∀ d, D 1 (fun _ => d) = ∑ i, g i * d i) (hx : x ∈ sparseSet n nnz) (hδ : 0 ≤ δ) :
    Optimization.taylorMeasure D 1 δ {d | x + d ∈ sparseSet n nnz} =
      δ * ∑ i ∈ activeSet x δ, |g i| + ∑ i ∈ (activeSet x δ)ᶜ, x i * g i +
        knapsackOpt x g δ nnz := by
  obtain ⟨τ, hτ, hopt⟩ := exists_knapsackFeasible_opt (g := g) hx hδ
  rw [← taylorDecrement_sparseLinearStep_eq D hg hδ hτ hopt, D.taylorDecrement_one_apply, hg,
    sum_mul_sparseLinearStep, knapsackValue_eq_knapsackOpt hτ hopt]
  ring

/-- The sparse measure for a function $f : \mathbb{R}^n \to \mathbb{R}$. Let $x$ be sparse, let
$\delta \ge 0$, and let $g_i = \nabla f(x)[e_i]$. Then the first-order measure
$\varphi^\delta_{f,X(x),1}(x)$ of (14.2.17) of [cartis2022evaluation], over the feasible
displacements, is
$$\delta \sum_{i \in \mathcal{A}_\delta(x)} |g_i| + \sum_{i \notin \mathcal{A}_\delta(x)} x_i
  g_i + \kappa,$$
where $\kappa$ is the optimal value of the knapsack problem (14.2.21) for this $g$. The measure
uses the Taylor series `ftaylorSeries ℝ f x`, and $g_i$ is `fderiv ℝ f x (Pi.single i 1)`. This
follows from Lemma 14.2.5 there.

No differentiability of $f$ is assumed: if $f$ is not differentiable at $x$, then `fderiv ℝ f x`
is $0$, and the formula holds with $g = 0$. -/
theorem taylorMeasure_ftaylorSeries_sparse_eq (f : (Fin n → ℝ) → ℝ)
    (hx : x ∈ sparseSet n nnz) (hδ : 0 ≤ δ) :
    Optimization.taylorMeasure (ftaylorSeries ℝ f x) 1 δ {d | x + d ∈ sparseSet n nnz} =
      δ * ∑ i ∈ activeSet x δ, |fderiv ℝ f x (Pi.single i 1)| +
        ∑ i ∈ (activeSet x δ)ᶜ, x i * fderiv ℝ f x (Pi.single i 1) +
        knapsackOpt x (fun i => fderiv ℝ f x (Pi.single i 1)) δ nnz := by
  refine taylorMeasure_sparse_eq _ (fun d => ?_) hx hδ
  change iteratedFDeriv ℝ 1 f x (fun _ => d) = _
  have hpi := (fderiv ℝ f x : (Fin n → ℝ) →ₗ[ℝ] ℝ).pi_apply_eq_sum_univ d
  simp only [ContinuousLinearMap.coe_coe] at hpi
  rw [iteratedFDeriv_one_apply, hpi]
  refine sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul, mul_comm]
  congr 2
  ext j
  simp [Pi.single_apply, eq_comm]

end Subproblem
