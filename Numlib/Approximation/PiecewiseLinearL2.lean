/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Numlib.Analysis.Normed.Module.BestApprox
import Numlib.Approximation.Interpolation
import Numlib.IntegralEquations.Basic
import Numlib.IntegralEquations.L2Kernel

/-!
# The $L^2$ projections onto the piecewise linear functions

Let $a = x_0 < x_1 < \dots < x_{n+1} = b$ be a partition of $[a, b]$. The piecewise linear functions
of the partition, as elements of $L^2(a, b)$, form a finite-dimensional subspace. The orthogonal
projection $P_n$ onto it is the **Galerkin projection** of the partition: it gives the best $L^2$
approximation by piecewise linear functions. A Galerkin method for an integral equation of the
second kind discretizes with this projection. It is easier to control than the interpolation
projection of `Numlib.Approximation.Interpolation`, because an orthogonal projection has norm at
most $1$ for every mesh. The presentation follows [han2009theoretical], §12.2.3, equations (12.2.18)
and (12.2.19), for the continuous projection, and §12.3.1 and Example 12.3.2 for the discontinuous
projection and for the operator estimate $\|K(I - P_n)\| = O(h^2)$, which the book states there
without proof.

The module builds two trial spaces. The continuous space `piecewiseLinearLp` is spanned by the
constant function and the clamped ramps of the subintervals. The discontinuous space
`discPiecewiseLinearLp` is spanned by the constant function and the coordinate function, each
restricted to one panel, and it contains the continuous space. The discontinuous space is an
orthogonal direct sum over the panels, so its Galerkin matrix is block diagonal; the continuous
space has about half its dimension. For either projection,
$$\|f - P_n f\|_{L^2} \le \sqrt{b - a}\, \|f - I_n f\|_\infty,$$
where $I_n$ is piecewise linear interpolation, and $P_n \to I$ pointwise on $L^2(a, b)$ when the
mesh tends to $0$. For a kernel operator $K$ on $L^2(a, b)$ and a self-adjoint $Q$, $\|KQ\| \le
\sqrt{b - a}\, \sup_x \|Q k(x, \cdot)\|$. With $Q = I - P_n$ and a kernel that is twice continuously
differentiable in its second variable, this gives $\|K(I - P_n)\| = O(h^2)$, which a
superconvergence argument for an iterated Galerkin method needs.

## Main definitions

* `IntegralOperator.iccIndicatorLp`: the class in $L^2(a, b)$ of a continuous function multiplied by
  the indicator of a measurable set.
* `meshPanel`: the half-open panel $[x_i, x_{i+1})$ of a partition.
* `piecewiseLinearLp`: the continuous trial space, spanned in $L^2(a, b)$ by the constant function
  and the clamped ramps of the subintervals.
* `discPiecewiseLinearLp`: the discontinuous trial space, spanned by the constant function and the
  coordinate function, each restricted to a panel.
* `piecewiseLinearProjCLM`, `discPiecewiseLinearProjCLM`: the orthogonal projections onto the two
  trial spaces.

## Main results

* `norm_sub_starProjection_le_of_iccToLp_mem`: the orthogonal projection $P$ onto a subspace $V$ of
  $L^2(a, b)$ satisfies $\|f - Pf\|_{L^2} \le \sqrt{b - a}\, \|f - g\|_\infty$ for every continuous
  $g$ with $[g] \in V$.
* `isIdempotentElem_piecewiseLinearProjCLM`, `norm_piecewiseLinearProjCLM_le_one`,
  `isIdempotentElem_discPiecewiseLinearProjCLM`, `isSelfAdjoint_discPiecewiseLinearProjCLM`,
  `norm_discPiecewiseLinearProjCLM_le_one`: each Galerkin projection is a projection of norm at most
  $1$, and the discontinuous one is self-adjoint.
* `norm_sub_piecewiseLinearProjCLM_le`, `norm_sub_discPiecewiseLinearProjCLM_le`: $\|f - P_n
  f\|_{L^2} \le \sqrt{b - a}\, \|f - I_n f\|_\infty$ for either projection.
* `tendsto_starProjection_of_piecewiseLinearInterpCLM_mem`, `tendsto_piecewiseLinearProjCLM`,
  `tendsto_discPiecewiseLinearProjCLM`: for partitions whose mesh tends to $0$, the projections
  converge pointwise to the identity on $L^2(a, b)$.
* `norm_l2KernelCLM_comp_le`: $\|KQ\| \le \sqrt{b - a}\, \sup_x \|Q k(x, \cdot)\|$ for a
  self-adjoint $Q$.
* `norm_l2KernelCLM_comp_sub_discPiecewiseLinearProjCLM_le`:
  $\|K(I - P_n)\| \le (b - a)\, h^2 M / 8$ for the discontinuous Galerkin projection, where $M$
  bounds $|\partial_y^2 k|$.

## Proof outline

Both approximation results come from one lemma, `norm_sub_starProjection_le_of_iccToLp_mem`: an
orthogonal projection onto a subspace of $L^2(a, b)$ approximates at least as well as any continuous
function whose class lies in the subspace, and a uniform bound is an $L^2$ bound
(`IntegralOperator.norm_iccToLp_le`). The continuous piecewise linear interpolant lies in both trial
spaces. Pointwise convergence on $L^2(a, b)$ follows from convergence on the dense set of continuous
functions and the bound $\|P_n\| \le 1$. The kernel estimate rests on the identity
$(KQv)(x) = \langle Q k(x, \cdot), v \rangle$ for a self-adjoint $Q$.

## Implementation notes

* $L^2(a, b)$ is `Lp ℝ 2 (IntegralOperator.iccMeasure a b)`, on the subtype `Set.Icc a b`. A
  continuous function enters it through `IntegralOperator.iccToLp`.
* The nodes are a sequence `x : ℕ → Set.Icc a b`, of which $x_0, \dots, x_{n+1}$ are used: the trial
  spaces with parameter $n$ have $n + 1$ panels.
* The panels are half-open, so that the panels of an increasing partition are disjoint and cover
  $[a, b)$. The remaining point $b$ is a null set.
* The dimension $2(n + 1)$ of the discontinuous space is not proved. Only the membership results
  that the approximation theory uses are proved.
-/

open Filter MeasureTheory Topology

open IntegralOperator

variable {a b : ℝ}

namespace IntegralOperator

/-! ### Continuous functions and their indicators inside $L^2(a, b)$ -/

/-- The class in $L^2(a, b)$ of a continuous function $g$ on $[a, b]$ agrees with $g$ almost
everywhere. -/
theorem coeFn_iccToLp (g : C(Set.Icc a b, ℝ)) :
    iccToLp a b g =ᵐ[iccMeasure a b] (g : Set.Icc a b → ℝ) :=
  ContinuousMap.coeFn_toLp (𝕜 := ℝ) (iccMeasure a b) g

/-- A continuous function on the compact interval $[a, b]$ is square-integrable for Lebesgue
measure. -/
theorem memLp_iccToLp (g : C(Set.Icc a b, ℝ)) :
    MemLp (g : Set.Icc a b → ℝ) 2 (iccMeasure a b) :=
  (Lp.memLp (iccToLp a b g)).ae_eq (coeFn_iccToLp g)

/-- A continuous kernel $k$ on the square $[a, b]^2$ is square-integrable for the product of the
Lebesgue measures. This is the hypothesis of `IntegralOperator.l2KernelCLM`. -/
theorem memLp_prod_iccMeasure (k : C(Set.Icc a b × Set.Icc a b, ℝ)) :
    MemLp k 2 ((iccMeasure a b).prod (iccMeasure a b)) :=
  MemLp.of_bound (map_continuous k).aestronglyMeasurable ‖k‖
    (Filter.Eventually.of_forall fun z => k.norm_coe_le_norm z)

/-- For a measurable set $s \subseteq [a, b]$ and a continuous function $g$ on $[a, b]$, the class
in $L^2(a, b)$ of the function $\mathbf{1}_s\, g$, which equals $g$ on $s$ and $0$ elsewhere.

A discontinuous trial space is spanned by such classes: each piece of a piecewise polynomial is
continuous, and only the restriction to a panel makes the whole function discontinuous. -/
noncomputable def iccIndicatorLp (a b : ℝ) {s : Set (Set.Icc a b)} (hs : MeasurableSet s)
    (g : C(Set.Icc a b, ℝ)) : Lp ℝ 2 (iccMeasure a b) :=
  ((memLp_iccToLp g).indicator hs.nullMeasurableSet).toLp _

/-- The class `IntegralOperator.iccIndicatorLp a b hs g` agrees almost everywhere with the function
$\mathbf{1}_s\, g$. -/
theorem coeFn_iccIndicatorLp {s : Set (Set.Icc a b)} (hs : MeasurableSet s)
    (g : C(Set.Icc a b, ℝ)) :
    iccIndicatorLp a b hs g =ᵐ[iccMeasure a b] s.indicator (g : Set.Icc a b → ℝ) :=
  MemLp.coeFn_toLp _

/-- If two continuous functions $g_1$ and $g_2$ agree on the measurable set $s$, then
$\mathbf{1}_s\, g_1$ and $\mathbf{1}_s\, g_2$ have the same class in $L^2(a, b)$. -/
theorem iccIndicatorLp_congr {s : Set (Set.Icc a b)} (hs : MeasurableSet s)
    {g₁ g₂ : C(Set.Icc a b, ℝ)} (h : ∀ t ∈ s, g₁ t = g₂ t) :
    iccIndicatorLp a b hs g₁ = iccIndicatorLp a b hs g₂ := by
  refine Lp.ext ?_
  filter_upwards [coeFn_iccIndicatorLp hs g₁, coeFn_iccIndicatorLp hs g₂] with t h1 h2
  rw [h1, h2]
  by_cases ht : t ∈ s
  · simp [Set.indicator_of_mem ht, h t ht]
  · simp [Set.indicator_of_notMem ht]

/-- The class of $\mathbf{1}_s\, g$ is additive in $g$: $[\mathbf{1}_s (g_1 + g_2)] =
[\mathbf{1}_s\, g_1] + [\mathbf{1}_s\, g_2]$. -/
theorem iccIndicatorLp_add {s : Set (Set.Icc a b)} (hs : MeasurableSet s)
    (g₁ g₂ : C(Set.Icc a b, ℝ)) :
    iccIndicatorLp a b hs (g₁ + g₂) = iccIndicatorLp a b hs g₁ + iccIndicatorLp a b hs g₂ := by
  refine Lp.ext ?_
  filter_upwards [coeFn_iccIndicatorLp hs (g₁ + g₂), coeFn_iccIndicatorLp hs g₁,
    coeFn_iccIndicatorLp hs g₂, Lp.coeFn_add (iccIndicatorLp a b hs g₁) (iccIndicatorLp a b hs g₂)]
    with t h0 h1 h2 h3
  rw [h3, Pi.add_apply, h0, h1, h2]
  by_cases ht : t ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, ht]

/-- The class of $\mathbf{1}_s\, g$ is homogeneous in $g$:
$[\mathbf{1}_s (cg)] = c\, [\mathbf{1}_s\, g]$ for $c \in \mathbb{R}$. -/
theorem iccIndicatorLp_smul {s : Set (Set.Icc a b)} (hs : MeasurableSet s) (c : ℝ)
    (g : C(Set.Icc a b, ℝ)) :
    iccIndicatorLp a b hs (c • g) = c • iccIndicatorLp a b hs g := by
  refine Lp.ext ?_
  filter_upwards [coeFn_iccIndicatorLp hs (c • g), coeFn_iccIndicatorLp hs g,
    Lp.coeFn_smul c (iccIndicatorLp a b hs g)] with t h0 h1 h2
  rw [h2, Pi.smul_apply, h0, h1]
  by_cases ht : t ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, ht]

end IntegralOperator

/-! ### Best approximation in $L^2(a, b)$ by a continuous element of the subspace -/

/-- Let $a \le b$, let $V$ be a subspace of $L^2(a, b)$ with an orthogonal projection $P$, and let
$f$ and $g$ be continuous functions on $[a, b]$ with $[g] \in V$. Then
$$\|f - Pf\|_{L^2} \le \|f - g\|_{L^2} \le \sqrt{b - a}\, \|f - g\|_\infty.$$
So every theorem on uniform approximation gives an $L^2$ bound for the orthogonal projection
onto a subspace that contains the approximant, with one factor $\sqrt{b - a}$. This is the
argument of [han2009theoretical], §12.2.3, equation (12.2.18).

This is the only input from approximation theory that the two Galerkin projections of this
module need. The projection is `Submodule.starProjection`, and $[g]$ is
`IntegralOperator.iccToLp a b g`. -/
theorem norm_sub_starProjection_le_of_iccToLp_mem (hab : a ≤ b)
    (V : Submodule ℝ (Lp ℝ 2 (IntegralOperator.iccMeasure a b))) [V.HasOrthogonalProjection]
    (f : C(Set.Icc a b, ℝ)) {g : C(Set.Icc a b, ℝ)} (hg : iccToLp a b g ∈ V) :
    ‖iccToLp a b f - V.starProjection (iccToLp a b f)‖ ≤ √(b - a) * ‖f - g‖ := by
  refine ((isBestApprox_starProjection V (iccToLp a b f)).2 _ hg).trans ?_
  rw [← map_sub]
  exact norm_iccToLp_le hab _

/-! ### The continuous piecewise linear functions -/

/-- The **continuous piecewise linear functions** of the nodes $x_0, \dots, x_{n+1}$, as a subspace
of $L^2(a, b)$: the span of the classes of the constant function $1$ and of the clamped ramps of
the subintervals $[x_i, x_{i+1}]$, $i = 0, \dots, n$. The clamped ramp of $[u, v]$ is
`piecewiseLinearRamp`: it is $0$ below $u$, rises with slope $1$ on $[u, v]$, and equals $v - u$
above $v$.

The space contains the class of every piecewise linear interpolant
`piecewiseLinearInterpCLM n x f` (`iccToLp_piecewiseLinearInterpCLM_mem`). The definition puts
no condition on the nodes. -/
noncomputable def piecewiseLinearLp (a b : ℝ) (n : ℕ) (x : ℕ → Set.Icc a b) :
    Submodule ℝ (Lp ℝ 2 (IntegralOperator.iccMeasure a b)) :=
  Submodule.span ℝ (iccToLp a b '' insert (1 : C(Set.Icc a b, ℝ))
    ((fun i => piecewiseLinearRamp a b (x i) (x (i + 1))) '' Set.Iic n))

instance (n : ℕ) (x : ℕ → Set.Icc a b) : FiniteDimensional ℝ (piecewiseLinearLp a b n x) :=
  FiniteDimensional.span_of_finite ℝ
    ((((Set.finite_Iic n).image _).insert _).image _)

instance (n : ℕ) (x : ℕ → Set.Icc a b) : (piecewiseLinearLp a b n x).HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- The **Galerkin projection** of the nodes $x_0, \dots, x_{n+1}$: the orthogonal projection of
$L^2(a, b)$ onto the continuous piecewise linear functions `piecewiseLinearLp a b n x`. It is
the projection $P_n$ of [han2009theoretical], §12.2.3. -/
noncomputable def piecewiseLinearProjCLM (a b : ℝ) (n : ℕ) (x : ℕ → Set.Icc a b) :
    Lp ℝ 2 (IntegralOperator.iccMeasure a b) →L[ℝ] Lp ℝ 2 (IntegralOperator.iccMeasure a b) :=
  (piecewiseLinearLp a b n x).starProjection

/-- The Galerkin projection is idempotent: $P_n^2 = P_n$. -/
theorem isIdempotentElem_piecewiseLinearProjCLM (a b : ℝ) (n : ℕ) (x : ℕ → Set.Icc a b) :
    IsIdempotentElem (piecewiseLinearProjCLM a b n x) :=
  Submodule.isIdempotentElem_starProjection _

/-- The Galerkin projection has the operator norm $\|P_n\| \le 1$, because it is an orthogonal
projection. In this it is better than the interpolation projection `piecewiseLinearInterpCLM`:
no Lebesgue constant enters. -/
theorem norm_piecewiseLinearProjCLM_le_one (a b : ℝ) (n : ℕ) (x : ℕ → Set.Icc a b) :
    ‖piecewiseLinearProjCLM a b n x‖ ≤ 1 :=
  Submodule.starProjection_norm_le _

/-- For every continuous function $f$ on $[a, b]$, the class of the piecewise linear interpolant
$I_n f$ (`piecewiseLinearInterpCLM n x f`) lies in the trial space `piecewiseLinearLp a b n x`. -/
theorem iccToLp_piecewiseLinearInterpCLM_mem (n : ℕ) (x : ℕ → Set.Icc a b)
    (f : C(Set.Icc a b, ℝ)) :
    iccToLp a b (piecewiseLinearInterpCLM n x f) ∈ piecewiseLinearLp a b n x := by
  have hgen : ∀ z ∈ insert (1 : C(Set.Icc a b, ℝ))
      ((fun i => piecewiseLinearRamp a b (x i) (x (i + 1))) '' Set.Iic n),
      iccToLp a b z ∈ piecewiseLinearLp a b n x := fun z hz =>
    Submodule.subset_span ⟨z, hz, rfl⟩
  have hone : iccToLp a b (1 : C(Set.Icc a b, ℝ)) ∈ piecewiseLinearLp a b n x :=
    hgen _ (Set.mem_insert _ _)
  have hramp : ∀ i ∈ Finset.range (n + 1),
      iccToLp a b (piecewiseLinearRamp a b (x i) (x (i + 1))) ∈ piecewiseLinearLp a b n x := by
    intro i hi
    exact hgen _ (Set.mem_insert_of_mem _ ⟨i, Set.mem_Iic.2 (Nat.lt_succ_iff.1
      (Finset.mem_range.1 hi)), rfl⟩)
  have hval : piecewiseLinearInterpCLM n x f
      = f (x 0) • (1 : C(Set.Icc a b, ℝ)) + ∑ i ∈ Finset.range (n + 1),
        (((x (i + 1) : ℝ) - (x i : ℝ))⁻¹ * (f (x (i + 1)) - f (x i))) •
          piecewiseLinearRamp a b (x i) (x (i + 1)) := by
    simp [piecewiseLinearInterpCLM, mul_smul]
  rw [hval, map_add, map_smul, map_sum]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ hone) (Submodule.sum_mem _ fun i hi => ?_)
  rw [map_smul]
  exact Submodule.smul_mem _ _ (hramp i hi)

/-- The **approximation property of the Galerkin projection**. Let $a \le b$ and let $f$ be
continuous on $[a, b]$. Then
$$\|f - P_n f\|_{L^2} \le \sqrt{b - a}\, \|f - I_n f\|_\infty,$$
where $I_n f$ is the piecewise linear interpolant of $f$. So every uniform bound on piecewise
linear interpolation gives an $L^2$ bound for the Galerkin projection, with one factor
$\sqrt{b - a}$; see [han2009theoretical], §12.2.3, equation (12.2.18).

The proof is `norm_sub_starProjection_le_of_iccToLp_mem` with $g = I_n f$. -/
theorem norm_sub_piecewiseLinearProjCLM_le (hab : a ≤ b) (n : ℕ) (x : ℕ → Set.Icc a b)
    (f : C(Set.Icc a b, ℝ)) :
    ‖iccToLp a b f - piecewiseLinearProjCLM a b n x (iccToLp a b f)‖
      ≤ √(b - a) * ‖f - piecewiseLinearInterpCLM n x f‖ :=
  norm_sub_starProjection_le_of_iccToLp_mem hab (piecewiseLinearLp a b n x) f
    (iccToLp_piecewiseLinearInterpCLM_mem n x f)

/-! ### The panels of a partition -/

/-- The $i$-th **panel** of the nodes $x$: the half-open interval $[x_i, x_{i+1})$, as a subset of
$[a, b]$. The panels are half-open so that the panels of an increasing partition are pairwise
disjoint and cover $[a, b)$ exactly once. -/
def meshPanel (x : ℕ → Set.Icc a b) (i : ℕ) : Set (Set.Icc a b) :=
  Subtype.val ⁻¹' Set.Ico (x i : ℝ) (x (i + 1) : ℝ)

/-- A point $t$ lies in the $i$-th panel if and only if $x_i \le t < x_{i+1}$. -/
theorem mem_meshPanel {x : ℕ → Set.Icc a b} {i : ℕ} {t : Set.Icc a b} :
    t ∈ meshPanel x i ↔ (x i : ℝ) ≤ (t : ℝ) ∧ (t : ℝ) < (x (i + 1) : ℝ) := Iff.rfl

/-- Each panel is a measurable subset of $[a, b]$, as the preimage of an interval under the
inclusion. -/
theorem measurableSet_meshPanel (x : ℕ → Set.Icc a b) (i : ℕ) :
    MeasurableSet (meshPanel x i) :=
  measurableSet_Ico.preimage measurable_subtype_coe

/-- Let $x_0, \dots, x_{n+1}$ be a partition of $[a, b]$. Every $t \in [a, b]$ with $t \ne b$ lies
in a panel $[x_j, x_{j+1})$ with $j \le n$. The point $b$ lies in no panel; it is a null set, so
nothing is lost in $L^2$. -/
theorem exists_mem_meshPanel {n : ℕ} {x : ℕ → Set.Icc a b}
    (hx : IsIntervalPartition a b (n + 1) fun i => (x i : ℝ)) {t : Set.Icc a b} (ht : (t : ℝ) ≠ b) :
    ∃ j ≤ n, t ∈ meshPanel x j := by
  have hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ) := fun i hi => hx.step i (by omega)
  obtain ⟨j, hj, h1, h2⟩ := exists_mem_subinterval hx.first hx.last t
  rcases lt_or_eq_of_le h2 with h | h
  · exact ⟨j, hj, ⟨h1, h⟩⟩
  · have hjn : j ≠ n := by
      rintro rfl
      exact ht (by rw [h, hx.last])
    exact ⟨j + 1, by omega, ⟨h.ge, h ▸ hstep (j + 1) (by omega)⟩⟩

/-- Let $x_0 < x_1 < \dots < x_{n+1}$. For $i, j \le n$ with $i \ne j$, the panels $[x_i, x_{i+1})$
and $[x_j, x_{j+1})$ are disjoint. -/
theorem notMem_meshPanel_of_mem {n : ℕ} {x : ℕ → Set.Icc a b}
    (hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ)) {i j : ℕ} (hi : i ≤ n) (hj : j ≤ n)
    (hij : i ≠ j) {t : Set.Icc a b} (htj : t ∈ meshPanel x j) : t ∉ meshPanel x i := by
  intro hti
  rcases lt_or_gt_of_ne hij with h | h
  · exact absurd
      (hti.2.trans_le ((piecewiseLinearInterpCLM.le_node_of_le hstep h (by omega)).trans htj.1))
      (lt_irrefl _)
  · exact absurd
      (htj.2.trans_le ((piecewiseLinearInterpCLM.le_node_of_le hstep h (by omega)).trans hti.1))
      (lt_irrefl _)

/-- Let $x_0, \dots, x_{n+1}$ be a partition of $[a, b]$, and let $g$ be continuous on $[a, b]$.
Then
$$\sum_{i=0}^{n} [\mathbf{1}_{[x_i, x_{i+1})}\, g] = [g] \quad \text{in } L^2(a, b),$$
because the panels are disjoint and cover $[a, b)$, and $\{b\}$ is a null set. By this identity,
a trial space built panel by panel contains the global functions built from its pieces. -/
theorem sum_iccIndicatorLp_meshPanel {n : ℕ} {x : ℕ → Set.Icc a b}
    (hx : IsIntervalPartition a b (n + 1) fun i => (x i : ℝ)) (g : C(Set.Icc a b, ℝ)) :
    ∑ i ∈ Finset.range (n + 1), iccIndicatorLp a b (measurableSet_meshPanel x i) g
      = iccToLp a b g := by
  have hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ) := fun i hi => hx.step i (by omega)
  have hab : a ≤ b := (x 0).2.1.trans (x 0).2.2
  refine Lp.ext ?_
  have hall : ∀ᵐ t ∂(iccMeasure a b), ∀ i ∈ Finset.range (n + 1),
      (iccIndicatorLp a b (measurableSet_meshPanel x i) g) t
        = (meshPanel x i).indicator (g : Set.Icc a b → ℝ) t :=
    (Filter.eventually_all_finset _).2 fun i _ => coeFn_iccIndicatorLp _ g
  filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range (n + 1))
      (fun i => iccIndicatorLp a b (measurableSet_meshPanel x i) g), hall, coeFn_iccToLp g,
    ae_ne_iccMeasure (⟨b, ⟨hab, le_rfl⟩⟩ : Set.Icc a b)] with t hsum hind htoLp htb
  rw [hsum, htoLp]
  obtain ⟨j, hj, hmem⟩ := exists_mem_meshPanel hx htb
  rw [Finset.sum_congr rfl hind, Finset.sum_eq_single j
    (fun i hi hij => Set.indicator_of_notMem (notMem_meshPanel_of_mem hstep
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hj hij hmem) _)
    (fun hcon => absurd (Finset.mem_range.2 (by omega)) hcon)]
  exact Set.indicator_of_mem hmem _

/-! ### The discontinuous piecewise linear functions -/

/-- The coordinate function $t \mapsto t$ on $[a, b]$, as a continuous function. Its restrictions to
the panels, together with those of the constant $1$, span the discontinuous piecewise linear
functions. -/
def iccCoord (a b : ℝ) : C(Set.Icc a b, ℝ) := ⟨Subtype.val, continuous_subtype_val⟩

/-- The coordinate function on $[a, b]$ maps $t$ to $t$. -/
@[simp]
theorem iccCoord_apply (a b : ℝ) (t : Set.Icc a b) : iccCoord a b t = (t : ℝ) := rfl

/-- The **discontinuous piecewise linear functions** of the nodes $x_0, \dots, x_{n+1}$, as a
subspace of $L^2(a, b)$: the span of the classes $[\mathbf{1}_{[x_i, x_{i+1})}]$ and
$[\mathbf{1}_{[x_i, x_{i+1})}\, t]$ for $i = 0, \dots, n$. A function of this space is affine on
every panel, and it need not be continuous at the nodes. For a strictly increasing partition the
space is the direct sum of the two-dimensional spaces of the $n + 1$ panels, so it has dimension
$2(n + 1)$; this count is not proved here.

This is the trial space of the discontinuous piecewise linear Galerkin method of
[han2009theoretical], §12.3.1, Example 12.3.2. There a mesh of $n$ subintervals of $[0, 1]$
gives the dimension $2n$, about twice the dimension of the continuous piecewise linear space of
§12.2.3. -/
noncomputable def discPiecewiseLinearLp (a b : ℝ) (n : ℕ) (x : ℕ → Set.Icc a b) :
    Submodule ℝ (Lp ℝ 2 (IntegralOperator.iccMeasure a b)) :=
  Submodule.span ℝ (⋃ i ∈ Set.Iic n,
    ({iccIndicatorLp a b (measurableSet_meshPanel x i) 1,
      iccIndicatorLp a b (measurableSet_meshPanel x i) (iccCoord a b)} :
        Set (Lp ℝ 2 (IntegralOperator.iccMeasure a b))))

instance (n : ℕ) (x : ℕ → Set.Icc a b) :
    FiniteDimensional ℝ (discPiecewiseLinearLp a b n x) :=
  FiniteDimensional.span_of_finite ℝ
    ((Set.finite_Iic n).biUnion fun _ _ => (Set.finite_singleton _).insert _)

instance (n : ℕ) (x : ℕ → Set.Icc a b) :
    (discPiecewiseLinearLp a b n x).HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- Let $i \le n$, and let $g$ be a continuous function on $[a, b]$ with $g(t) = c + dt$ on the
panel $[x_i, x_{i+1})$. Then $[\mathbf{1}_{[x_i, x_{i+1})}\, g]$ lies in the discontinuous trial
space `discPiecewiseLinearLp a b n x`. -/
theorem iccIndicatorLp_mem_discPiecewiseLinearLp {n : ℕ} {x : ℕ → Set.Icc a b} {i : ℕ}
    (hi : i ≤ n) {c d : ℝ} {g : C(Set.Icc a b, ℝ)}
    (hg : ∀ t ∈ meshPanel x i, g t = c + d * (t : ℝ)) :
    iccIndicatorLp a b (measurableSet_meshPanel x i) g ∈ discPiecewiseLinearLp a b n x := by
  have hgen : ∀ z ∈ ({iccIndicatorLp a b (measurableSet_meshPanel x i) 1,
      iccIndicatorLp a b (measurableSet_meshPanel x i) (iccCoord a b)} :
        Set (Lp ℝ 2 (IntegralOperator.iccMeasure a b))),
      z ∈ discPiecewiseLinearLp a b n x := fun z hz =>
    Submodule.subset_span (Set.mem_biUnion (Set.mem_Iic.2 hi) hz)
  have hrw : iccIndicatorLp a b (measurableSet_meshPanel x i) g
      = c • iccIndicatorLp a b (measurableSet_meshPanel x i) 1
        + d • iccIndicatorLp a b (measurableSet_meshPanel x i) (iccCoord a b) := by
    rw [← iccIndicatorLp_smul, ← iccIndicatorLp_smul, ← iccIndicatorLp_add]
    exact iccIndicatorLp_congr _ fun t ht => by simpa using hg t ht
  rw [hrw]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hgen _ (Set.mem_insert _ _)))
    (Submodule.smul_mem _ _ (hgen _ (Set.mem_insert_of_mem _ rfl)))

/-- Let $x_0, \dots, x_{n+1}$ be a partition of $[a, b]$, and let $f$ be continuous on $[a, b]$.
Then the class of the piecewise linear interpolant $I_n f$ lies in the discontinuous trial
space. So the continuous piecewise linear functions lie in the discontinuous ones: on each panel
the interpolant is the affine function through its two node values. -/
theorem iccToLp_piecewiseLinearInterpCLM_mem_disc {n : ℕ} {x : ℕ → Set.Icc a b}
    (hx : IsIntervalPartition a b (n + 1) fun i => (x i : ℝ)) (f : C(Set.Icc a b, ℝ)) :
    iccToLp a b (piecewiseLinearInterpCLM n x f) ∈ discPiecewiseLinearLp a b n x := by
  have hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ) := fun i hi => hx.step i (by omega)
  rw [← sum_iccIndicatorLp_meshPanel hx]
  refine Submodule.sum_mem _ fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hd : (x (i + 1) : ℝ) - (x i : ℝ) ≠ 0 := sub_ne_zero.2 (hstep i hin).ne'
  set D : ℝ := (f (x (i + 1)) - f (x i)) / ((x (i + 1) : ℝ) - (x i : ℝ)) with hD
  refine iccIndicatorLp_mem_discPiecewiseLinearLp hin
    (c := f (x i) - D * (x i : ℝ)) (d := D) fun t ht => ?_
  rw [piecewiseLinearInterpCLM_apply_of_mem hstep f hin ht.1 ht.2.le, hD]
  field_simp
  ring

/-- The **discontinuous Galerkin projection**: the orthogonal projection of $L^2(a, b)$ onto the
discontinuous piecewise linear functions `discPiecewiseLinearLp a b n x`. It is the projection
of the discontinuous piecewise linear Galerkin method of [han2009theoretical], §12.3.1, Example
12.3.2. Because the trial space is the orthogonal direct sum of the panel spaces, the projection
acts panel by panel. -/
noncomputable def discPiecewiseLinearProjCLM (a b : ℝ) (n : ℕ) (x : ℕ → Set.Icc a b) :
    Lp ℝ 2 (IntegralOperator.iccMeasure a b) →L[ℝ] Lp ℝ 2 (IntegralOperator.iccMeasure a b) :=
  (discPiecewiseLinearLp a b n x).starProjection

/-- The discontinuous Galerkin projection is idempotent: $P_n^2 = P_n$. -/
theorem isIdempotentElem_discPiecewiseLinearProjCLM (a b : ℝ) (n : ℕ) (x : ℕ → Set.Icc a b) :
    IsIdempotentElem (discPiecewiseLinearProjCLM a b n x) :=
  Submodule.isIdempotentElem_starProjection _

/-- The discontinuous Galerkin projection is self-adjoint, because it is an orthogonal projection.
In a superconvergence argument this turns $\|K(I - P_n)\|$ into $\|(I - P_n)K^*\|$; see
[han2009theoretical], §12.3.1, equation (12.3.13). -/
theorem isSelfAdjoint_discPiecewiseLinearProjCLM (a b : ℝ) (n : ℕ) (x : ℕ → Set.Icc a b) :
    IsSelfAdjoint (discPiecewiseLinearProjCLM a b n x) :=
  isSelfAdjoint_starProjection _

/-- The discontinuous Galerkin projection has the operator norm $\|P_n\| \le 1$ for every mesh,
because it is an orthogonal projection: no Lebesgue constant enters. -/
theorem norm_discPiecewiseLinearProjCLM_le_one (a b : ℝ) (n : ℕ) (x : ℕ → Set.Icc a b) :
    ‖discPiecewiseLinearProjCLM a b n x‖ ≤ 1 :=
  Submodule.starProjection_norm_le _

/-- The **approximation property of the discontinuous Galerkin projection**. Let $a \le b$, let
$x_0, \dots, x_{n+1}$ be a partition of $[a, b]$, and let $f$ be continuous on $[a, b]$. Then
$$\|f - P_n f\|_{L^2} \le \sqrt{b - a}\, \|f - I_n f\|_\infty,$$
where $P_n$ is the discontinuous Galerkin projection and $I_n f$ is the continuous piecewise
linear interpolant. The constant is the same as in `norm_sub_piecewiseLinearProjCLM_le`, because
the discontinuous trial space contains the interpolant.

With `norm_sub_piecewiseLinearInterpCLM_le`, this gives the order $O(h^2)$ on $C^2[a, b]$ that
[han2009theoretical], §12.3.1, Example 12.3.2, states for the discontinuous piecewise linear
Galerkin method. -/
theorem norm_sub_discPiecewiseLinearProjCLM_le (hab : a ≤ b) {n : ℕ} {x : ℕ → Set.Icc a b}
    (hx : IsIntervalPartition a b (n + 1) fun i => (x i : ℝ)) (f : C(Set.Icc a b, ℝ)) :
    ‖iccToLp a b f - discPiecewiseLinearProjCLM a b n x (iccToLp a b f)‖
      ≤ √(b - a) * ‖f - piecewiseLinearInterpCLM n x f‖ :=
  norm_sub_starProjection_le_of_iccToLp_mem hab (discPiecewiseLinearLp a b n x) f
    (iccToLp_piecewiseLinearInterpCLM_mem_disc hx f)

/-! ### Pointwise convergence -/

/-- Let $a \le b$. For each $m$, let $y^{(m)}_0, \dots, y^{(m)}_{N_m + 1}$ be a partition of
$[a, b]$ with mesh at most $h_m$, where $h_m \to 0$. Let $V_m$ be a subspace of $L^2(a, b)$ with
an orthogonal projection $P_m$, and suppose that $V_m$ contains the class of the piecewise
linear interpolant at the nodes $y^{(m)}$ of every continuous function. Then $P_m u \to u$ for
every $u \in L^2(a, b)$.

The convergence holds on the continuous functions by `norm_sub_starProjection_le_of_iccToLp_mem`
and the convergence of piecewise linear interpolation. The projections have norm at most $1$,
and the continuous functions are dense in $L^2(a, b)$. The result is stated for an arbitrary
family of subspaces because both trial spaces of this module satisfy its hypothesis. It is the
pointwise convergence that a projection method for an equation of the second kind needs; see
[han2009theoretical], §12.2.3, the paragraph after equation (12.2.18).

The partition is given by the conditions $y^{(m)}_i < y^{(m)}_{i+1}$ for $i \le N_m$,
$y^{(m)}_0 = a$ and $y^{(m)}_{N_m + 1} = b$, and the mesh bound is
$y^{(m)}_{i+1} - y^{(m)}_i \le h_m$ for $i \le N_m$. -/
theorem tendsto_starProjection_of_piecewiseLinearInterpCLM_mem (hab : a ≤ b)
    {V : ℕ → Submodule ℝ (Lp ℝ 2 (IntegralOperator.iccMeasure a b))}
    [∀ m, (V m).HasOrthogonalProjection] {N : ℕ → ℕ} {y : ℕ → ℕ → Set.Icc a b} {h : ℕ → ℝ}
    (hmem : ∀ m (f : C(Set.Icc a b, ℝ)),
      iccToLp a b (piecewiseLinearInterpCLM (N m) (y m) f) ∈ V m)
    (hstep : ∀ n, ∀ i ≤ N n, (y n i : ℝ) < (y n (i + 1) : ℝ))
    (hfirst : ∀ n, (y n 0 : ℝ) = a) (hlast : ∀ n, (y n (N n + 1) : ℝ) = b)
    (hmesh : ∀ n, ∀ i ≤ N n, (y n (i + 1) : ℝ) - (y n i : ℝ) ≤ h n)
    (hh : Tendsto h atTop (𝓝 0)) (u : Lp ℝ 2 (IntegralOperator.iccMeasure a b)) :
    Tendsto (fun n => (V n).starProjection u) atTop (𝓝 u) := by
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  -- a continuous function close to `u` in `L²`
  obtain ⟨v, hv⟩ := Metric.denseRange_iff.1
    (ContinuousMap.toLp_denseRange (p := 2) ℝ (IntegralOperator.iccMeasure a b) ℝ (by simp))
    u (ε / 3) (by linarith)
  -- the interpolation error of that function tends to zero
  have hint : Tendsto (fun n => ‖v - piecewiseLinearInterpCLM (N n) (y n) v‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => piecewiseLinearInterpCLM (N n) (y n) v) atTop (𝓝 v) :=
      tendsto_piecewiseLinearInterpCLM hstep hfirst hlast hmesh hh v
    have h2 : Tendsto (fun n => v - piecewiseLinearInterpCLM (N n) (y n) v) atTop (𝓝 (v - v)) :=
      tendsto_const_nhds.sub h1
    rw [sub_self] at h2
    simpa using h2.norm
  obtain ⟨n₀, hn₀⟩ := (Metric.tendsto_atTop.1 hint) (ε / 3 / (√(b - a) + 1)) (by positivity)
  refine ⟨n₀, fun n hn => ?_⟩
  have hmid : √(b - a) * ‖v - piecewiseLinearInterpCLM (N n) (y n) v‖ < ε / 3 := by
    have h1 := hn₀ n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h1
    have hpos : (0 : ℝ) < √(b - a) + 1 := by positivity
    calc √(b - a) * ‖v - piecewiseLinearInterpCLM (N n) (y n) v‖
        ≤ (√(b - a) + 1) * ‖v - piecewiseLinearInterpCLM (N n) (y n) v‖ := by
          nlinarith [norm_nonneg (v - piecewiseLinearInterpCLM (N n) (y n) v)]
      _ < (√(b - a) + 1) * (ε / 3 / (√(b - a) + 1)) := mul_lt_mul_of_pos_left h1 hpos
      _ = ε / 3 := by field_simp
  -- the three-term estimate
  have hproj : ‖(V n).starProjection u
      - (V n).starProjection (iccToLp a b v)‖ ≤ ‖u - iccToLp a b v‖ := by
    rw [← map_sub]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    nlinarith [Submodule.starProjection_norm_le (V n), norm_nonneg (u - iccToLp a b v),
      norm_nonneg ((V n).starProjection)]
  have hd1 : ‖u - iccToLp a b v‖ < ε / 3 := by
    rw [← dist_eq_norm]
    exact hv
  have hd2 := norm_sub_starProjection_le_of_iccToLp_mem hab (V n) v (hmem n v)
  rw [dist_eq_norm]
  have hsplit : (V n).starProjection u - u
      = ((V n).starProjection u
          - (V n).starProjection (iccToLp a b v))
        - (iccToLp a b v - (V n).starProjection (iccToLp a b v))
        - (u - iccToLp a b v) := by abel
  rw [hsplit]
  calc ‖((V n).starProjection u
          - (V n).starProjection (iccToLp a b v))
        - (iccToLp a b v - (V n).starProjection (iccToLp a b v))
        - (u - iccToLp a b v)‖
      ≤ ‖((V n).starProjection u
            - (V n).starProjection (iccToLp a b v))
          - (iccToLp a b v - (V n).starProjection (iccToLp a b v))‖
        + ‖u - iccToLp a b v‖ := norm_sub_le _ _
    _ ≤ (‖(V n).starProjection u
            - (V n).starProjection (iccToLp a b v)‖
          + ‖iccToLp a b v - (V n).starProjection (iccToLp a b v)‖)
        + ‖u - iccToLp a b v‖ := by gcongr; exact norm_sub_le _ _
    _ < ε := by linarith

/-- Let $a \le b$. For each $m$, let $y^{(m)}_0, \dots, y^{(m)}_{N_m + 1}$ be a partition of
$[a, b]$ with mesh at most $h_m$, where $h_m \to 0$. Then the Galerkin projections $P_m$ onto
the continuous piecewise linear functions of these partitions satisfy $P_m u \to u$ for every
$u \in L^2(a, b)$.

This is the pointwise convergence that a projection method for an equation of the second kind
needs; see [han2009theoretical], §12.2.3, the paragraph after equation (12.2.18). It is
`tendsto_starProjection_of_piecewiseLinearInterpCLM_mem` with the continuous trial spaces
`piecewiseLinearLp` as $V_m$. -/
theorem tendsto_piecewiseLinearProjCLM (hab : a ≤ b) {N : ℕ → ℕ} {y : ℕ → ℕ → Set.Icc a b}
    {h : ℕ → ℝ} (hstep : ∀ n, ∀ i ≤ N n, (y n i : ℝ) < (y n (i + 1) : ℝ))
    (hfirst : ∀ n, (y n 0 : ℝ) = a) (hlast : ∀ n, (y n (N n + 1) : ℝ) = b)
    (hmesh : ∀ n, ∀ i ≤ N n, (y n (i + 1) : ℝ) - (y n i : ℝ) ≤ h n)
    (hh : Tendsto h atTop (𝓝 0)) (u : Lp ℝ 2 (IntegralOperator.iccMeasure a b)) :
    Tendsto (fun n => piecewiseLinearProjCLM a b (N n) (y n) u) atTop (𝓝 u) :=
  tendsto_starProjection_of_piecewiseLinearInterpCLM_mem hab
    (fun m f => iccToLp_piecewiseLinearInterpCLM_mem (N m) (y m) f) hstep hfirst hlast hmesh hh u

/-- Let $a \le b$. For each $m$, let $y^{(m)}_0, \dots, y^{(m)}_{N_m + 1}$ be a partition of
$[a, b]$ with mesh at most $h_m$, where $h_m \to 0$. Then the discontinuous Galerkin projections
$P_m$ of these partitions satisfy $P_m u \to u$ for every $u \in L^2(a, b)$; see
[han2009theoretical], §12.3.1.

The proof is the same as for `tendsto_piecewiseLinearProjCLM`, because the discontinuous trial
space contains the continuous piecewise linear interpolants. -/
theorem tendsto_discPiecewiseLinearProjCLM (hab : a ≤ b) {N : ℕ → ℕ} {y : ℕ → ℕ → Set.Icc a b}
    {h : ℕ → ℝ} (hstep : ∀ n, ∀ i ≤ N n, (y n i : ℝ) < (y n (i + 1) : ℝ))
    (hfirst : ∀ n, (y n 0 : ℝ) = a) (hlast : ∀ n, (y n (N n + 1) : ℝ) = b)
    (hmesh : ∀ n, ∀ i ≤ N n, (y n (i + 1) : ℝ) - (y n i : ℝ) ≤ h n)
    (hh : Tendsto h atTop (𝓝 0)) (u : Lp ℝ 2 (IntegralOperator.iccMeasure a b)) :
    Tendsto (fun n => discPiecewiseLinearProjCLM a b (N n) (y n) u) atTop (𝓝 u) :=
  tendsto_starProjection_of_piecewiseLinearInterpCLM_mem hab
    (fun m f => iccToLp_piecewiseLinearInterpCLM_mem_disc
      ⟨fun i hi => hstep m i (by omega), hfirst m, hlast m⟩ f)
    hstep hfirst hlast hmesh hh u

/-! ### Kernel operators against a projection -/

/-- Let $a \le b$, let $k$ be a continuous kernel on $[a, b]^2$ with integral operator $K$ on
$L^2(a, b)$, and let $Q$ be a bounded self-adjoint operator on $L^2(a, b)$. If
$\varepsilon \ge 0$ and $\|Q k(z, \cdot)\|_{L^2} \le \varepsilon$ for every $z \in [a, b]$, then
$$\|KQ\| \le \sqrt{b - a}\, \varepsilon.$$
For $Q = I - P_n$ with a projection $P_n$, this is the estimate that an iterated projection
method needs: $\|K(I - P_n)\|$ is small when $I - P_n$ is uniformly small on the rows of the
kernel; see [han2009theoretical], §12.3.1, the paragraph that contains equation (12.3.17).

The proof uses the identity $(KQv)(x) = \langle k(x, \cdot), Qv \rangle = \langle Q k(x, \cdot),
v \rangle$, which bounds $KQv$ pointwise by $\varepsilon \|v\|$, and a pointwise bound is an
$L^2$ bound with the factor $\sqrt{b - a}$. In Lean, the row $k(z, \cdot)$ is `k.curry z` and
the operator $K$ is `IntegralOperator.l2KernelCLM hk`. -/
theorem norm_l2KernelCLM_comp_le (hab : a ≤ b) {k : C(Set.Icc a b × Set.Icc a b, ℝ)}
    (hk : MemLp k 2 ((iccMeasure a b).prod (iccMeasure a b)))
    {Q : Lp ℝ 2 (IntegralOperator.iccMeasure a b) →L[ℝ] Lp ℝ 2 (IntegralOperator.iccMeasure a b)}
    (hQ : IsSelfAdjoint Q) {ε : ℝ} (hε : 0 ≤ ε)
    (hrow : ∀ z, ‖Q (iccToLp a b (k.curry z))‖ ≤ ε) :
    ‖l2KernelCLM hk ∘L Q‖ ≤ √(b - a) * ε := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have hbd : ∀ᵐ z ∂(iccMeasure a b), ‖(l2KernelCLM hk (Q v)) z‖ ≤ ε * ‖v‖ := by
    filter_upwards [l2KernelCLM_apply_ae hk (Q v)] with z hz
    have hrowae : ∫ y, (iccToLp a b (k.curry z)) y * (Q v) y ∂(iccMeasure a b)
        = ∫ y, k (z, y) * (Q v) y ∂(iccMeasure a b) := by
      refine integral_congr_ae ?_
      filter_upwards [coeFn_iccToLp (k.curry z)] with y hy
      rw [hy]
      rfl
    have hinner : (inner ℝ (Q (iccToLp a b (k.curry z))) v : ℝ)
        = ∫ y, k (z, y) * (Q v) y ∂(iccMeasure a b) := by
      rw [← hrowae, ← L2.inner_eq_integral_mul]
      conv_lhs => rw [← hQ.adjoint_eq]
      rw [ContinuousLinearMap.adjoint_inner_left]
    rw [hz, ← hinner, Real.norm_eq_abs]
    calc |(inner ℝ (Q (iccToLp a b (k.curry z))) v : ℝ)|
        ≤ ‖Q (iccToLp a b (k.curry z))‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ ≤ ε * ‖v‖ := by gcongr; exact hrow z
  refine (Lp.norm_le_of_ae_bound (by positivity : (0 : ℝ) ≤ ε * ‖v‖) hbd).trans_eq ?_
  have hmu : ((measureUnivNNReal (iccMeasure a b) : NNReal) : ℝ) = b - a := by
    rw [show ((measureUnivNNReal (iccMeasure a b) : NNReal) : ℝ)
      = (iccMeasure a b).real Set.univ from rfl]
    exact measureReal_iccMeasure_univ hab
  rw [← mul_assoc]
  norm_num [hmu, Real.sqrt_eq_rpow]

/-- Let $a \le b$, let $x_0, \dots, x_{n+1}$ be a partition of $[a, b]$ with mesh at most $h$, and
let $P_n$ be its discontinuous Galerkin projection. Let $k$ be a continuous kernel on $[a, b]^2$
with integral operator $K$, such that every row is $k(z, t) = G_z(t)$ for a function $G_z$ of
class $C^2$ on $\mathbb{R}$ with $|G_z''(t)| \le M$ for $t \in [a, b]$. Then
$$\|K(I - P_n)\| \le \frac{(b - a)\, h^2 M}{8}.$$

[han2009theoretical], §12.3.1, Example 12.3.2, states without proof that "it is straightforward
to show $\|(I - P_n)K^*\| = O(h^2)$". The two forms agree because $P_n$ is self-adjoint
(`isSelfAdjoint_discPiecewiseLinearProjCLM`) and an operator and its adjoint have the same norm,
which is equation (12.3.13) there.

The rows are handled uniformly by `norm_sub_discPiecewiseLinearProjCLM_le` and
`norm_sub_piecewiseLinearInterpCLM_le`. The two factors $\sqrt{b - a}$, one from
`norm_l2KernelCLM_comp_le` and one from the approximation property, combine into $b - a$. -/
theorem norm_l2KernelCLM_comp_sub_discPiecewiseLinearProjCLM_le (hab : a ≤ b) {n : ℕ}
    {x : ℕ → Set.Icc a b} (hx : IsIntervalPartition a b (n + 1) fun i => (x i : ℝ))
    {k : C(Set.Icc a b × Set.Icc a b, ℝ)}
    (hk : MemLp k 2 ((iccMeasure a b).prod (iccMeasure a b)))
    {G : Set.Icc a b → ℝ → ℝ} (hG : ∀ z, ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (G z))
    (hGk : ∀ z t : Set.Icc a b, k (z, t) = G z (t : ℝ)) {h M : ℝ}
    (hmesh : ∀ i ≤ n, (x (i + 1) : ℝ) - (x i : ℝ) ≤ h)
    (hM : ∀ z : Set.Icc a b, ∀ t ∈ Set.Icc a b, |iteratedDeriv 2 (G z) t| ≤ M) :
    ‖l2KernelCLM hk ∘L (1 - discPiecewiseLinearProjCLM a b n x)‖ ≤ (b - a) * (h ^ 2 / 8 * M) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM (x 0) (x 0) (x 0).2)
  have hsa : IsSelfAdjoint (1 - discPiecewiseLinearProjCLM a b n x) :=
    IsSelfAdjoint.sub (IsSelfAdjoint.one _) (isSelfAdjoint_discPiecewiseLinearProjCLM a b n x)
  have key := norm_l2KernelCLM_comp_le hab hk hsa
    (ε := √(b - a) * (h ^ 2 / 8 * M)) (by positivity) fun z => ?_
  · refine key.trans_eq ?_
    rw [← mul_assoc, Real.mul_self_sqrt (sub_nonneg.2 hab)]
  · have hsub : (1 - discPiecewiseLinearProjCLM a b n x) (iccToLp a b (k.curry z))
        = iccToLp a b (k.curry z)
          - discPiecewiseLinearProjCLM a b n x (iccToLp a b (k.curry z)) := by
      simp
    rw [hsub]
    refine (norm_sub_discPiecewiseLinearProjCLM_le hab hx _).trans ?_
    gcongr
    exact norm_sub_piecewiseLinearInterpCLM_le hx (hG z) (fun t => hGk z t) hmesh
      (hM z)
