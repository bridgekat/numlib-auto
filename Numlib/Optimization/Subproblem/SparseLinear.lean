import Numlib.Optimization.ModelBased.HighOrder.MeasureTest
import Mathlib.Basic.Real.Sign

/-!
# Sparse linear minimization over an `ℓ∞` ball

Minimizing a linear function `ℓ(d) = ∑ g_i d_i` over the `ℓ∞` ball of radius `δ` intersected with
the sparsity set `{d | ‖x + d‖₀ ≤ n_nz}` ([cartis2022evaluation], §14.2.2.2, Lemma 14.2.5): the
subproblem that makes sparsity constraints *simple* for first-order trust-region and
regularization methods. The space is `Fin n → ℝ` with Mathlib's sup norm, so
`Metric.closedBall 0 δ` is the book's `ℓ∞` ball and `Optimization.taylorMeasure` on this space is
the measure (14.2.17).

The subproblem (14.2.18)–(14.2.19) is the minimization of `ℓ(d)`, as the measure requires
(`φ = f(x) - min T_{f,1}(x, ·) = -min ℓ`); its solution (14.2.20) is a minimizer. Lemma 14.2.5 is
stated for any optimal selection `τ` of the 0-1 knapsack (14.2.21); such a selection exists since
there are finitely many.

## Main definitions

* `Subproblem.sparseSet n nnz = {x | ‖x‖₀ ≤ nnz}` ((14.2.14)), with the support
  `Subproblem.nzSet x` ((14.2.15)) and the set `Subproblem.activeSet x δ = {i | |x_i| > δ}`;
* `Subproblem.sparseLinearStep x g δ τ`, the step (14.2.20);
* `Subproblem.knapsackValue`, `Subproblem.KnapsackFeasible`, `Subproblem.knapsackOpt`: objective,
  constraint and optimal value of (14.2.21).

## Main results

* `Subproblem.isMinOn_sparseLinearStep`: Lemma 14.2.5 (minimization form) for an optimal knapsack
  selection, with the optimal value `Subproblem.sum_mul_sparseLinearStep`;
* `Subproblem.exists_knapsackFeasible_opt`, `Subproblem.exists_isMinOn_sparseLinearStep`,
  `Subproblem.exists_isMinOn_sparse`: existence of optimal selections and steps;
* `Subproblem.isApproxMeasureStep_sparseLinearStep`: the step is an approximate optimality
  displacement in the sense of `Optimization.IsApproxMeasureStep`;
* `Subproblem.taylorMeasure_sparse_eq`: the measure (14.2.17) in closed form, computable without
  evaluating `f`.
-/

open Set Metric Finset
open scoped BigOperators

namespace Subproblem

variable {n nnz : ℕ}

/-! ### The sparsity set -/

/-- The support `𝒜(x) = {i | x_i ≠ 0}` of `x` ([cartis2022evaluation], (14.2.15)). -/
noncomputable def nzSet (x : Fin n → ℝ) : Finset (Fin n) := Finset.univ.filter (fun i => x i ≠ 0)

/-- The sparsity set `{x | ‖x‖₀ ≤ nnz}` ([cartis2022evaluation], (14.2.14)). -/
def sparseSet (n nnz : ℕ) : Set (Fin n → ℝ) := {x | (nzSet x).card ≤ nnz}

theorem mem_sparseSet {x : Fin n → ℝ} : x ∈ sparseSet n nnz ↔ (nzSet x).card ≤ nnz := Iff.rfl

theorem mem_nzSet {x : Fin n → ℝ} {i : Fin n} : i ∈ nzSet x ↔ x i ≠ 0 := by simp [nzSet]

/-- `0` is sparse. -/
theorem zero_mem_sparseSet : (0 : Fin n → ℝ) ∈ sparseSet n nnz := by
  simp [mem_sparseSet, nzSet]

/-- The sparsity set is closed (the support can only grow near a point). -/
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

/-- The sparsity constraint is void iff `n ≤ nnz`. -/
theorem sparseSet_eq_univ_iff : sparseSet n nnz = univ ↔ n ≤ nnz := by
  constructor
  · intro h
    have h1 : (fun _ => (1 : ℝ)) ∈ sparseSet n nnz := h ▸ mem_univ _
    simpa [mem_sparseSet, nzSet] using h1
  · intro h
    refine eq_univ_of_forall fun x => ?_
    exact (card_le_univ _).trans (by simpa using h)

/-- The sparsity set is not convex in general: `{x ∈ ℝ² | ‖x‖₀ ≤ 1}` contains `e₁`, `e₂` but not
their midpoint. -/
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

/-- The large components `𝒜_δ(x) = {i | |x_i| > δ}`, which no feasible displacement of `ℓ∞`
length `δ` can zero. -/
noncomputable def activeSet (x : Fin n → ℝ) (δ : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => δ < |x i|)

theorem mem_activeSet {x : Fin n → ℝ} {δ : ℝ} {i : Fin n} : i ∈ activeSet x δ ↔ δ < |x i| := by
  simp [activeSet]

/-- The step of Lemma 14.2.5 ([cartis2022evaluation], (14.2.20)): on `𝒜_δ(x)` move to the far face
`-δ sign(g_i)`; on the complement either zero the coordinate (`τ_i = false`, `x_i + d_i = 0`) or
move to the far face (`τ_i = true`). (Equal to (14.2.20) after simplifying
`-x_i - τ_i (δ sign g_i - x_i)`.) -/
noncomputable def sparseLinearStep (x g : Fin n → ℝ) (δ : ℝ) (τ : Fin n → Bool) :
    Fin n → ℝ :=
  fun i => if δ < |x i| then -δ * Real.sign (g i) else if τ i then -δ * Real.sign (g i) else -x i

/-- The objective of the knapsack problem (14.2.21):
`∑_{i ∉ 𝒜_δ(x)} τ_i (δ |g_i| - x_i g_i)`. -/
noncomputable def knapsackValue (x g : Fin n → ℝ) (δ : ℝ) (τ : Fin n → Bool) : ℝ :=
  ∑ i ∈ (activeSet x δ)ᶜ, if τ i then δ * |g i| - x i * g i else 0

/-- The constraint of the knapsack problem (14.2.21), `∑_{i ∉ 𝒜_δ(x)} τ_i ≤ nnz - |𝒜_δ(x)|`,
written without truncated subtraction as `|𝒜_δ(x)| + ∑_{i ∉ 𝒜_δ(x)} τ_i ≤ nnz`. -/
def KnapsackFeasible (x : Fin n → ℝ) (δ : ℝ) (nnz : ℕ) (τ : Fin n → Bool) : Prop :=
  (activeSet x δ).card + ((activeSet x δ)ᶜ.filter (fun i => τ i = true)).card ≤ nnz

/-- The optimal value of the knapsack problem (14.2.21) (the maximum of `knapsackValue` over the
finitely many feasible selections; `0` if there is none). -/
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

/-- `g_i d_i ≥ -δ |g_i|` whenever `|d_i| ≤ δ`. -/
private theorem neg_mul_abs_le (g d δ : ℝ) (hd : |d| ≤ δ) : -(δ * |g|) ≤ g * d := by
  have : |g * d| ≤ δ * |g| := by rw [abs_mul, mul_comm]; gcongr
  linarith [neg_abs_le (g * d)]

variable {x g : Fin n → ℝ} {δ : ℝ} {τ : Fin n → Bool}

/-- The value of the linear function at the step (14.2.20):
`ℓ(d⋆) = -δ ∑_{i ∈ 𝒜_δ} |g_i| - ∑_{i ∉ 𝒜_δ} x_i g_i - ∑_{i ∉ 𝒜_δ} τ_i (δ |g_i| - x_i g_i)`. -/
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

/-- The step lies in the `ℓ∞` ball of radius `δ ≥ 0`. -/
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

/-- The support of `x + d⋆` is contained in `𝒜_δ(x)` together with the selected indices. -/
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

/-- `|𝒜_δ(x)| ≤ |𝒜(x)|` for `δ ≥ 0`. -/
theorem activeSet_subset_nzSet (hδ : 0 ≤ δ) : activeSet x δ ⊆ nzSet x := fun i hi =>
  mem_nzSet.2 fun h0 => by
    have := mem_activeSet.1 hi
    rw [h0, abs_zero] at this
    linarith

/-- **Lemma 14.2.5 of [cartis2022evaluation]** (as a minimization). Let `δ ≥ 0` and let
`τ` solve the knapsack problem (14.2.21): it is feasible and has maximal value
among feasible selections. Then `d⋆ = sparseLinearStep x g δ τ` satisfies `‖d⋆‖∞ ≤ δ`, `x + d⋆` is
sparse, and `d⋆` minimizes `ℓ(d) = ∑ g_i d_i` over `{d | ‖d‖∞ ≤ δ, ‖x + d‖₀ ≤ nnz}`; its value is
`sum_mul_sparseLinearStep`. -/
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

/-- The knapsack problem (14.2.21) has an optimal selection when `x` is sparse (finitely many
selections, `τ = false` is feasible since `|𝒜_δ(x)| ≤ |𝒜(x)| ≤ nnz`). -/
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

/-- An optimal knapsack selection attains `knapsackOpt`. -/
theorem knapsackValue_eq_knapsackOpt (hτ : KnapsackFeasible x δ nnz τ)
    (hopt : ∀ τ', KnapsackFeasible x δ nnz τ' → knapsackValue x g δ τ' ≤ knapsackValue x g δ τ) :
    knapsackValue x g δ τ = knapsackOpt x g δ nnz := by
  have : IsGreatest (knapsackValue x g δ '' {τ | KnapsackFeasible x δ nnz τ})
      (knapsackValue x g δ τ) := ⟨⟨τ, hτ, rfl⟩, Set.forall_mem_image.2 hopt⟩
  exact this.csSup_eq.symm

/-- Lemma 14.2.5 with the existence of the knapsack solution: for sparse `x` and `δ ≥ 0` there is
an optimal selection `τ` whose step `sparseLinearStep x g δ τ` solves the sparse linear problem. -/
theorem exists_isMinOn_sparseLinearStep (hx : x ∈ sparseSet n nnz) (hδ : 0 ≤ δ) :
    ∃ τ, KnapsackFeasible x δ nnz τ ∧
      (∀ τ', KnapsackFeasible x δ nnz τ' → knapsackValue x g δ τ' ≤ knapsackValue x g δ τ) ∧
      ‖sparseLinearStep x g δ τ‖ ≤ δ ∧ x + sparseLinearStep x g δ τ ∈ sparseSet n nnz ∧
      IsMinOn (fun d => ∑ i, g i * d i) (closedBall 0 δ ∩ {d | x + d ∈ sparseSet n nnz})
        (sparseLinearStep x g δ τ) := by
  obtain ⟨τ, hτ, hopt⟩ := exists_knapsackFeasible_opt (g := g) hx hδ
  exact ⟨τ, hτ, hopt, isMinOn_sparseLinearStep hδ hτ hopt⟩

/-- The sparse linear problem (14.2.18) (as a minimization) has a solution for sparse `x` and
`δ ≥ 0`. -/
theorem exists_isMinOn_sparse (hx : x ∈ sparseSet n nnz) (hδ : 0 ≤ δ) :
    ∃ d ∈ closedBall 0 δ ∩ {d | x + d ∈ sparseSet n nnz},
      IsMinOn (fun d => ∑ i, g i * d i) (closedBall 0 δ ∩ {d | x + d ∈ sparseSet n nnz}) d := by
  obtain ⟨τ, -, -, hn, hS, hmin⟩ := exists_isMinOn_sparseLinearStep (g := g) hx hδ
  exact ⟨_, ⟨mem_closedBall_zero_iff.2 hn, hS⟩, hmin⟩

/-- The feasible displacements `{d | x + d ∈ sparseSet n nnz}` form a closed set. -/
theorem isClosed_shift_sparseSet (x : Fin n → ℝ) :
    IsClosed {d : Fin n → ℝ | x + d ∈ sparseSet n nnz} :=
  isClosed_sparseSet.preimage (continuous_const.add continuous_id)

/-- `0` is a feasible displacement at a sparse point. -/
theorem zero_mem_shift_sparseSet (hx : x ∈ sparseSet n nnz) :
    (0 : Fin n → ℝ) ∈ {d : Fin n → ℝ | x + d ∈ sparseSet n nnz} := by
  simpa using hx

/-- At an optimal knapsack selection, the Taylor decrease along `d⋆` is the sparse measure. -/
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

/-- The optimal sparse step is an approximate optimality displacement for every `ς ≤ 1`
(bridge to `Optimization.IsApproxMeasureStep`, Step 1 of TR1-SP / AR1-SP). -/
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

/-- **The sparse measure** ([cartis2022evaluation], (14.2.17), Lemma 14.2.5): if the first-order
data act as `D₁[d] = ∑ g_i d_i` (`g` the gradient), `x` is sparse and `δ ≥ 0`, the measure over
`{d | ‖d‖∞ ≤ δ, ‖x + d‖₀ ≤ nnz}` is `δ ∑_{𝒜_δ} |g_i| + ∑_{𝒜_δ^c} x_i g_i + knapsackOpt`,
computable without further evaluations of `f`. -/
theorem taylorMeasure_sparse_eq (D : FormalMultilinearSeries ℝ (Fin n → ℝ) ℝ)
    (hg : ∀ d, D 1 (fun _ => d) = ∑ i, g i * d i) (hx : x ∈ sparseSet n nnz) (hδ : 0 ≤ δ) :
    Optimization.taylorMeasure D 1 δ {d | x + d ∈ sparseSet n nnz} =
      δ * ∑ i ∈ activeSet x δ, |g i| + ∑ i ∈ (activeSet x δ)ᶜ, x i * g i +
        knapsackOpt x g δ nnz := by
  obtain ⟨τ, hτ, hopt⟩ := exists_knapsackFeasible_opt (g := g) hx hδ
  rw [← taylorDecrement_sparseLinearStep_eq D hg hδ hτ hopt, D.taylorDecrement_one_apply, hg,
    sum_mul_sparseLinearStep, knapsackValue_eq_knapsackOpt hτ hopt]
  ring

/-- The sparse measure for a function on `Fin n → ℝ`: with `g_i = ∇f(x)[e_i]`,
`φ^δ_{f,X(x),1}(x) = δ ∑_{𝒜_δ} |g_i| + ∑_{𝒜_δ^c} x_i g_i + knapsackOpt` ((14.2.17),
Lemma 14.2.5). -/
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
