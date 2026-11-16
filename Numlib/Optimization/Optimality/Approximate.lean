/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Optimality.Unconstrained
import Numlib.Optimization.Subproblem.MinCurvature
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Basic.Real.Pointwise

/-!
# Approximate optimality and criticality measures

This file defines the notions of approximate optimality and the criticality measures that the
evaluation-complexity results of [cartis2022evaluation] share, from (1.1.5), (2.1.2), (3.2.6),
(12.1.10), (12.1.25) and (13.1.5). A point $x$ is an $\varepsilon$-approximate first-order minimizer
of $f$ if $\|\nabla f(x)\| \le \varepsilon$, and an $(\varepsilon_1, \varepsilon_2)$-approximate
second-order minimizer if moreover $\lambda_{\min}[\nabla^2 f(x)] \ge -\varepsilon_2$. For higher
orders, the measure is the largest decrease of the Taylor polynomial of order $j$ over the
displacements of length at most $\delta$,
$$\phi^\delta_{f,j}(x) = \sup_{\|d\| \le \delta} \big( T_{f,j}(x, 0) - T_{f,j}(x, d) \big),$$
and $x$ is an $(\varepsilon, \delta)$-approximate minimizer of order $q$ if
$\phi^{\delta_j}_{f,j}(x) \le \varepsilon_j \delta_j^j / j!$ for $1 \le j \le q$.

The file proves the basic properties of these measures: bounds, monotonicity, perturbation by
inexact derivatives, and attainment in finite dimension. It also relates the Hessian $\nabla^2 f(x)$
as a bilinear form to the Hessian operator and, on $\mathbb{R}^n$, to the Hessian matrix, so that
$\lambda_{\min}[\nabla^2 f(x)]$ is the least eigenvalue.

## Main definitions

* `Optimization.IsApproxFirstOrder`: $\|\nabla f(x)\| \le \varepsilon$, as in (2.1.2).
* `Optimization.IsApproxSecondOrder`: $\|\nabla f(x)\| \le \varepsilon_1$ and
  $\lambda_{\min}[\nabla^2 f(x)] \ge -\varepsilon_2$, as in (3.2.6).
* `Optimization.criticality₂`: the second-order criticality measure $\omega_2(x) = \max(0,
  -\lambda_{\min}[\nabla^2 f(x)])$ of Section 1.1.2.6. The first-order measure is $\|\nabla f(x)\|$.
* `Optimization.decrementMeasure`: $\sup \{ \Delta(d) : \|d\| \le \delta, d \in S \}$, the largest
  decrease of a model decrement $\Delta$ over the feasible displacements of length at most $\delta$.
* `Optimization.taylorMeasure`: the decrement measure of the Taylor decrement of order $j$ of
  derivative data $D$. For the exact jet of $f$ at $x$ and $S = E$, it is the measure
  $\phi^\delta_{f,j}(x)$ of (12.1.10).
* `Optimization.IsEpsDeltaApprox` and `Optimization.IsEpsApprox`: the condition (12.1.25) for given
  radii $\delta$, and the $(\varepsilon, \delta)$-approximate minimizer of order $q$.
* `Optimization.hessianOperator`: the Hessian $\nabla^2 f(x)$ as an operator, the derivative of the
  gradient.
* `Optimization.hessianMatrix`: on `EuclideanSpace ℝ ι`, the Hessian matrix
  $[\nabla^2 f(x)]_{ij} = \nabla^2 f(x)[e_i, e_j]$.

## Main results

* `Optimization.exists_decrementMeasure_eq`: in finite dimension, the decrement measure of a
  continuous decrement on a closed feasible set is attained.
* `Optimization.taylorMeasure_one_eq`: the first-order measure is $\phi^\delta_1 = \delta \|D_1\|$,
  as in (12.1.12).
* `Optimization.abs_taylorMeasure_sub_le`: the perturbation bound (13.1.6) for inexact derivative
  data.
* `Optimization.pow_div_mul_taylorMeasure_le`: for $j \le 2$, the function
  $\delta \mapsto \phi^\delta_j / \delta^j$ is nonincreasing.
* `Optimization.inner_hessianOperator_apply`: $\langle u, \nabla^2 f(x) v \rangle = \nabla^2 f(x)[u,
  v]$.
* `Optimization.exists_eigenvector_hessianOperator`: a unit eigenvector for
  $\lambda_{\min}[\nabla^2 f(x)] < 0$ with $\langle u, \nabla f(x) \rangle \le 0$, as in (3.2.3).

## Implementation notes

* The first-order and second-order notions use `fderiv` and `minCurvature`, so they make sense on
  every real normed space. On a real Hilbert space, $\|\nabla f(x)\|$ equals the norm of
  `fderiv ℝ f x`, see `Optimization.isApproxFirstOrder_iff_norm_gradient`.
* The source also allows the tolerance $\varepsilon_2 = +\infty$, which switches the second-order
  test off. This value is not a real number, and the statements of the algorithms represent it
  separately.
* The Taylor measure is defined from derivative data `D : FormalMultilinearSeries ℝ E ℝ` and a set
  $S$ of feasible displacements. Thus one definition serves exact derivatives
  (`D = ftaylorSeries ℝ f x`), inexact derivatives (the measure $\bar\phi$ of (13.1.5)) and
  constraints ($S = \{ d : x + d \in C \}$).
* All the measures of the source are instances of `Optimization.decrementMeasure`. Its properties
  (upper and lower bounds, monotonicity, perturbation, attainment) are stated for an arbitrary
  decrement function.
* The decrement measure is the supremum `sSup` of a set of real numbers, which is $0$ if the set is
  empty or not bounded above. The Taylor measure is finite without any compactness, because the
  Taylor decrement is bounded on balls, see `Optimization.bddAbove_taylorDecrement`.
-/

open Filter Set Topology Metric Finset
open scoped Nat RealInnerProductSpace

namespace Optimization

/-! ### The decrement measure -/

section Decrement

variable {E : Type*} [NormedAddCommGroup E]


/-- The **decrement measure** of a decrement function $\Delta : E \to \mathbb{R}$ with radius
$\delta$ and feasible set $S$:
$$\sup \{ \Delta(d) : \|d\| \le \delta, \ d \in S \},$$
the largest decrease $\Delta(d)$ of a model over the feasible displacements of length at most
$\delta$. With the appropriate decrements, it is the measure of (12.1.10), (13.1.5), (14.1.6),
(14.1.14), (14.2.2) and (14.2.4) of [cartis2022evaluation].

The supremum is `sSup`, so the measure is $0$ if the set of feasible displacements is empty or
the decreases are not bounded above. -/
noncomputable def decrementMeasure (Δ : E → ℝ) (δ : ℝ) (S : Set E) : ℝ :=
  sSup (Δ '' (closedBall 0 δ ∩ S))

variable {Δ Δ' : E → ℝ} {δ δ' : ℝ} {S S' : Set E} {d : E}

/-- The decrement measure is the supremum of $\Delta$ over the feasible displacements $d$ with
$\|d\| \le \delta$ and $d \in S$. -/
theorem decrementMeasure_def :
    decrementMeasure Δ δ S = sSup (Δ '' (closedBall 0 δ ∩ S)) := rfl

/-- If the feasible decreases are bounded above, then every feasible decrease is at most the
measure: for $\|d\| \le \delta$ and $d \in S$,
$$\Delta(d) \le \sup \{ \Delta(d') : \|d'\| \le \delta, \ d' \in S \}.$$
-/
theorem le_decrementMeasure (hbdd : BddAbove (Δ '' (closedBall 0 δ ∩ S)))
    (hd : d ∈ closedBall 0 δ ∩ S) : Δ d ≤ decrementMeasure Δ δ S :=
  le_csSup hbdd (mem_image_of_mem Δ hd)

/-- If the feasible decreases are bounded above, $0 \in S$, $\delta \ge 0$ and $\Delta(0) = 0$, then
the decrement measure is nonnegative. -/
theorem decrementMeasure_nonneg (hbdd : BddAbove (Δ '' (closedBall 0 δ ∩ S))) (h0 : (0 : E) ∈ S)
    (hδ : 0 ≤ δ) (hΔ0 : Δ 0 = 0) : 0 ≤ decrementMeasure Δ δ S :=
  hΔ0 ▸ le_decrementMeasure hbdd ⟨mem_closedBall_self hδ, h0⟩

/-- If some displacement is feasible and $\Delta(d) \le B$ for every feasible $d$, then the
decrement measure is at most $B$. -/
theorem decrementMeasure_le {B : ℝ} (hne : (closedBall 0 δ ∩ S).Nonempty)
    (h : ∀ d ∈ closedBall 0 δ ∩ S, Δ d ≤ B) : decrementMeasure Δ δ S ≤ B :=
  csSup_le (hne.image Δ) (forall_mem_image.2 h)

/-- The decrement measure is monotone in the radius: if some displacement of length at most $\delta$
is feasible, the decreases are bounded above on the larger ball, and $\delta \le \delta'$, then
the measure with radius $\delta$ is at most the measure with radius $\delta'$. -/
theorem decrementMeasure_mono_radius (hne : (closedBall 0 δ ∩ S).Nonempty)
    (hbdd : BddAbove (Δ '' (closedBall 0 δ' ∩ S))) (hδ : δ ≤ δ') :
    decrementMeasure Δ δ S ≤ decrementMeasure Δ δ' S :=
  csSup_le_csSup hbdd (hne.image Δ)
    (image_mono (inter_subset_inter_left _ (closedBall_subset_closedBall hδ)))

/-- The decrement measure is monotone in the feasible set: if some displacement of length at most
$\delta$ is in $S$, the decreases are bounded above on the larger set, and $S \subseteq S'$,
then the measure with $S$ is at most the measure with $S'$. -/
theorem decrementMeasure_mono_set (hne : (closedBall 0 δ ∩ S).Nonempty)
    (hbdd : BddAbove (Δ '' (closedBall 0 δ ∩ S'))) (hS : S ⊆ S') :
    decrementMeasure Δ δ S ≤ decrementMeasure Δ δ S' :=
  csSup_le_csSup hbdd (hne.image Δ) (image_mono (inter_subset_inter_right _ hS))

/-- The decrement measure is monotone in the decrement: if some displacement is feasible, $\Delta'$
is bounded above on the feasible displacements, and $\Delta(d) \le \Delta'(d)$ for every
feasible $d$, then the measure of $\Delta$ is at most the measure of $\Delta'$. -/
theorem decrementMeasure_mono_fun (hne : (closedBall 0 δ ∩ S).Nonempty)
    (hbdd : BddAbove (Δ' '' (closedBall 0 δ ∩ S))) (h : ∀ d ∈ closedBall 0 δ ∩ S, Δ d ≤ Δ' d) :
    decrementMeasure Δ δ S ≤ decrementMeasure Δ' δ S :=
  decrementMeasure_le hne fun d hd => (h d hd).trans (le_decrementMeasure hbdd hd)

/-- Perturbation of the decrement. Suppose that some displacement is feasible and that both $\Delta$
and $\Delta'$ are bounded above on the feasible displacements. If
$|\Delta(d) - \Delta'(d)| \le e$ for every feasible $d$, then the two decrement measures differ
by at most $e$. -/
theorem abs_decrementMeasure_sub_le {e : ℝ} (hne : (closedBall 0 δ ∩ S).Nonempty)
    (hbdd : BddAbove (Δ '' (closedBall 0 δ ∩ S))) (hbdd' : BddAbove (Δ' '' (closedBall 0 δ ∩ S)))
    (h : ∀ d ∈ closedBall 0 δ ∩ S, |Δ d - Δ' d| ≤ e) :
    |decrementMeasure Δ δ S - decrementMeasure Δ' δ S| ≤ e := by
  rw [abs_sub_le_iff]
  constructor
  · rw [sub_le_iff_le_add]
    refine decrementMeasure_le hne fun d hd => ?_
    have := le_decrementMeasure hbdd' hd
    linarith [(abs_sub_le_iff.1 (h d hd)).1]
  · rw [sub_le_iff_le_add]
    refine decrementMeasure_le hne fun d hd => ?_
    have := le_decrementMeasure hbdd hd
    linarith [(abs_sub_le_iff.1 (h d hd)).2]

/-- The decrement measure is positively homogeneous in the decrement: for $a \ge 0$, the measure of
$d \mapsto a \Delta(d)$ is $a$ times the measure of $\Delta$. -/
theorem decrementMeasure_const_mul {Δ : E → ℝ} {δ a : ℝ} {S : Set E} (ha : 0 ≤ a) :
    decrementMeasure (fun d => a * Δ d) δ S = a * decrementMeasure Δ δ S := by
  rw [decrementMeasure_def, decrementMeasure_def, ← smul_eq_mul (a := a),
    ← Real.sSup_smul_of_nonneg ha, ← Set.image_smul, Set.image_image]
  rfl

variable [NormedSpace ℝ E]

/-- Let $E$ be a finite-dimensional real normed space, $S \subseteq E$ closed with $0 \in S$, and
$\delta \ge 0$. If $\Delta$ is continuous on the feasible displacements
$\{ d \in S : \|d\| \le \delta \}$, then the decrement measure is attained: there is a feasible
$d$ with $\|d\| \le \delta$ and
$$\Delta(d) = \sup \{ \Delta(d') : \|d'\| \le \delta, \ d' \in S \}.$$
-/
theorem exists_decrementMeasure_eq [FiniteDimensional ℝ E] (hS : IsClosed S) (h0 : (0 : E) ∈ S)
    (hδ : 0 ≤ δ) (hΔ : ContinuousOn Δ (closedBall 0 δ ∩ S)) :
    ∃ d ∈ closedBall 0 δ ∩ S, Δ d = decrementMeasure Δ δ S := by
  have := FiniteDimensional.proper_real E
  have hK : IsCompact (closedBall (0 : E) δ ∩ S) := (isCompact_closedBall 0 δ).inter_right hS
  obtain ⟨d, hd, hmax⟩ := hK.exists_isMaxOn ⟨0, mem_closedBall_self hδ, h0⟩ hΔ
  refine ⟨d, hd, ?_⟩
  exact (IsGreatest.csSup_eq ⟨mem_image_of_mem Δ hd, forall_mem_image.2 hmax⟩).symm

/-- Let $E$ be a finite-dimensional real normed space, $S \subseteq E$ closed and star-shaped about
$0$ with $0 \in S$, and $\delta \ge 0$. Let $\Delta$ be continuous on the feasible displacements
of length at most $\delta$, with $\Delta(0) = 0$. Then for every $\varsigma \in [0, 1]$ there is
a feasible $d$ with $\|d\| \le \delta$ and
$$\Delta(d) = \varsigma \sup \{ \Delta(d') : \|d'\| \le \delta, \ d' \in S \}.$$

The proof applies the intermediate value theorem along the segment from $0$ to a maximizer. -/
theorem exists_decrementMeasure_mul_eq [FiniteDimensional ℝ E] (hS : IsClosed S)
    (h0 : (0 : E) ∈ S) (hstar : StarConvex ℝ 0 S) (hδ : 0 ≤ δ)
    (hΔ : ContinuousOn Δ (closedBall 0 δ ∩ S)) (hΔ0 : Δ 0 = 0) {ς : ℝ} (hς : ς ∈ Icc (0 : ℝ) 1) :
    ∃ d ∈ closedBall 0 δ ∩ S, Δ d = ς * decrementMeasure Δ δ S := by
  obtain ⟨d, hd, hdM⟩ := exists_decrementMeasure_eq hS h0 hδ hΔ
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, t • d ∈ closedBall (0 : E) δ ∩ S := by
    intro t ht
    refine ⟨?_, hstar.smul_mem hd.2 ht.1 ht.2⟩
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans (mem_closedBall_zero_iff.1 hd.1)
  have hg : ContinuousOn (fun t : ℝ => Δ (t • d)) (Icc 0 1) :=
    hΔ.comp (continuous_id.smul continuous_const).continuousOn hseg
  have := FiniteDimensional.proper_real E
  have hK : IsCompact (closedBall (0 : E) δ ∩ S) := (isCompact_closedBall 0 δ).inter_right hS
  have hM : 0 ≤ decrementMeasure Δ δ S :=
    decrementMeasure_nonneg (hK.bddAbove_image hΔ) h0 hδ hΔ0
  have hmem : ς * decrementMeasure Δ δ S ∈ Icc (Δ ((0 : ℝ) • d)) (Δ ((1 : ℝ) • d)) := by
    rw [zero_smul, one_smul, hΔ0, hdM]
    exact ⟨mul_nonneg hς.1 hM, mul_le_of_le_one_left hM hς.2⟩
  obtain ⟨t, ht, hteq⟩ := intermediate_value_Icc zero_le_one hg hmem
  exact ⟨t • d, hseg t ht, hteq⟩

end Decrement

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### First-order and second-order approximate minimizers -/

/-- A point $x$ is an **$\varepsilon$-approximate first-order minimizer** of $f$ if
$$\|\nabla f(x)\| \le \varepsilon,$$
as in (2.1.2) of [cartis2022evaluation].

The norm is the norm of the Fréchet derivative `fderiv ℝ f x`, so the definition makes sense on
every real normed space. -/
def IsApproxFirstOrder (f : E → ℝ) (x : E) (ε : ℝ) : Prop := ‖fderiv ℝ f x‖ ≤ ε

/-- A point $x$ is an $\varepsilon$-approximate first-order minimizer of $f$ if and only if the
derivative of $f$ at $x$ has norm at most $\varepsilon$. -/
theorem isApproxFirstOrder_iff {f : E → ℝ} {x : E} {ε : ℝ} :
    IsApproxFirstOrder f x ε ↔ ‖fderiv ℝ f x‖ ≤ ε := Iff.rfl

/-- A point $x$ is an **$(\varepsilon_1, \varepsilon_2)$-approximate second-order minimizer** of $f$
if
$$\|\nabla f(x)\| \le \varepsilon_1 \quad \text{and} \quad \lambda_{\min}[\nabla^2 f(x)] \ge
  -\varepsilon_2,$$
as in (3.2.6) of [cartis2022evaluation].

Here $\lambda_{\min}[\nabla^2 f(x)] = \inf_{\|d\| = 1} \nabla^2 f(x)[d, d]$ is
`minCurvature (iteratedFDeriv ℝ 2 f x)`. -/
def IsApproxSecondOrder (f : E → ℝ) (x : E) (ε₁ ε₂ : ℝ) : Prop :=
  ‖fderiv ℝ f x‖ ≤ ε₁ ∧ -ε₂ ≤ minCurvature (iteratedFDeriv ℝ 2 f x)

/-- A point $x$ is an $(\varepsilon_1, \varepsilon_2)$-approximate second-order minimizer of $f$ if
and only if $\|\nabla f(x)\| \le \varepsilon_1$ and $\lambda_{\min}[\nabla^2 f(x)] \ge
-\varepsilon_2$. -/
theorem isApproxSecondOrder_iff {f : E → ℝ} {x : E} {ε₁ ε₂ : ℝ} :
    IsApproxSecondOrder f x ε₁ ε₂ ↔
      ‖fderiv ℝ f x‖ ≤ ε₁ ∧ -ε₂ ≤ minCurvature (iteratedFDeriv ℝ 2 f x) := Iff.rfl

/-- An $(\varepsilon_1, \varepsilon_2)$-approximate second-order minimizer is an
$\varepsilon_1$-approximate first-order minimizer. -/
theorem IsApproxSecondOrder.isApproxFirstOrder {f : E → ℝ} {x : E} {ε₁ ε₂ : ℝ}
    (h : IsApproxSecondOrder f x ε₁ ε₂) : IsApproxFirstOrder f x ε₁ := h.1

/-- The **second-order criticality measure**, (1.1.5) and Section 1.1.2.6 of [cartis2022evaluation]:
$$\omega_2(x) = \max\big(0, -\lambda_{\min}[\nabla^2 f(x)]\big).$$
-/
noncomputable def criticality₂ (f : E → ℝ) (x : E) : ℝ :=
  max 0 (-minCurvature (iteratedFDeriv ℝ 2 f x))

/-- The second-order criticality measure is nonnegative. -/
theorem criticality₂_nonneg (f : E → ℝ) (x : E) : 0 ≤ criticality₂ f x := le_max_left _ _

/-- For $\varepsilon \ge 0$, $\omega_2(x) \le \varepsilon$ if and only if
$\lambda_{\min}[\nabla^2 f(x)] \ge -\varepsilon$. -/
theorem criticality₂_le_iff {f : E → ℝ} {x : E} {ε : ℝ} (hε : 0 ≤ ε) :
    criticality₂ f x ≤ ε ↔ -ε ≤ minCurvature (iteratedFDeriv ℝ 2 f x) := by
  rw [criticality₂, max_le_iff, neg_le]
  exact and_iff_right hε

/-- The second-order criticality measure vanishes, $\omega_2(x) = 0$, if and only if
$\lambda_{\min}[\nabla^2 f(x)] \ge 0$. -/
theorem criticality₂_eq_zero_iff {f : E → ℝ} {x : E} :
    criticality₂ f x = 0 ↔ 0 ≤ minCurvature (iteratedFDeriv ℝ 2 f x) := by
  rw [← (criticality₂_nonneg f x).ge_iff_eq', criticality₂_le_iff le_rfl, neg_zero]

/-- For $\varepsilon_2 \ge 0$, a point $x$ is an $(\varepsilon_1, \varepsilon_2)$-approximate
second-order minimizer of $f$ if and only if $\|\nabla f(x)\| \le \varepsilon_1$ and
$\omega_2(x) \le \varepsilon_2$. -/
theorem isApproxSecondOrder_iff_criticality₂_le {f : E → ℝ} {x : E} {ε₁ ε₂ : ℝ} (hε₂ : 0 ≤ ε₂) :
    IsApproxSecondOrder f x ε₁ ε₂ ↔ ‖fderiv ℝ f x‖ ≤ ε₁ ∧ criticality₂ f x ≤ ε₂ := by
  rw [isApproxSecondOrder_iff, criticality₂_le_iff hε₂]

/-- At a local minimizer $x$ of a function $f$ that is twice continuously differentiable at $x$,
both criticality measures vanish: $\|\nabla f(x)\| = 0$ and $\omega_2(x) = 0$, as in (1.1.5) of
[cartis2022evaluation]. -/
theorem IsLocalMin.criticality_eq_zero {f : E → ℝ} {x : E} (hmin : IsLocalMin f x)
    (hf : ContDiffAt ℝ 2 f x) : ‖fderiv ℝ f x‖ = 0 ∧ criticality₂ f x = 0 :=
  ⟨by rw [hmin.fderiv_eq_zero, norm_zero],
    criticality₂_eq_zero_iff.2 (IsLocalMin.minCurvature_iteratedFDeriv_two_nonneg hmin hf)⟩

variable {δ : ℝ} {S : Set E} {d : E}

/-! ### The Taylor-decrement measure -/

/-- For all derivative data $D$, orders $j$, radii $\delta$ and sets $S$, the Taylor decreases
$T_j(0) - T_j(d)$ over the feasible displacements of length at most $\delta$ are bounded above.
Thus the Taylor measure is the supremum of a bounded set. -/
theorem bddAbove_taylorDecrement (D : FormalMultilinearSeries ℝ E ℝ) (j : ℕ) (δ : ℝ) (S : Set E) :
    BddAbove (D.taylorDecrement j '' (closedBall 0 δ ∩ S)) := by
  refine ⟨∑ i ∈ Icc 1 j, ‖D i‖ * δ ^ i / i !, forall_mem_image.2 fun d hd => ?_⟩
  exact (le_abs_self _).trans
    (D.abs_taylorDecrement_le_of_norm_le j (mem_closedBall_zero_iff.1 hd.1))

/-- The **Taylor-decrement measure**, (12.1.10) of [cartis2022evaluation]:
$$\phi^\delta_j = \sup \{ T_j(0) - T_j(d) : \|d\| \le \delta, \ d \in S \},$$
where $T_j$ is the Taylor sum of order $j$ of the derivative data $D$.

For the exact jet `D = ftaylorSeries ℝ f x` and $S = E$, it is
$f(x) - \min_{\|d\| \le \delta} T_{f,j}(x, d)$. With $S = \{ d : x + d \in C \}$, it is the
measure for constraints of Chapters 6 and 14. With inexact data $D$, it is the measure
$\bar\phi$ of (13.1.5). -/
noncomputable def taylorMeasure (D : FormalMultilinearSeries ℝ E ℝ) (j : ℕ) (δ : ℝ)
    (S : Set E) : ℝ :=
  decrementMeasure (D.taylorDecrement j) δ S

/-- The Taylor measure is the supremum of the Taylor decreases $T_j(0) - T_j(d)$ over the feasible
displacements of length at most $\delta$. -/
theorem taylorMeasure_eq_sSup (D : FormalMultilinearSeries ℝ E ℝ) (j : ℕ) (δ : ℝ) (S : Set E) :
    taylorMeasure D j δ S = sSup (D.taylorDecrement j '' (closedBall 0 δ ∩ S)) := rfl

/-- Every feasible Taylor decrease is at most the Taylor measure: if $\|d\| \le \delta$ and
$d \in S$, then $T_j(0) - T_j(d) \le \phi^\delta_j$. -/
theorem taylorDecrement_le_taylorMeasure (D : FormalMultilinearSeries ℝ E ℝ) (j : ℕ)
    (hd : d ∈ closedBall 0 δ ∩ S) : D.taylorDecrement j d ≤ taylorMeasure D j δ S :=
  le_decrementMeasure (bddAbove_taylorDecrement D j δ S) hd

/-- If $0 \in S$ and $\delta \ge 0$, then the Taylor measure is nonnegative: $\phi^\delta_j \ge 0$.
-/
theorem taylorMeasure_nonneg (D : FormalMultilinearSeries ℝ E ℝ) (j : ℕ) (h0 : (0 : E) ∈ S)
    (hδ : 0 ≤ δ) : 0 ≤ taylorMeasure D j δ S :=
  decrementMeasure_nonneg (bddAbove_taylorDecrement D j δ S) h0 hδ
    (D.taylorDecrement_zero_right j)

/-- For a continuous linear functional $\ell$ on a real normed space and $\delta \ge 0$,
$$\sup_{\|s\| \le \delta} \big(-\ell(s)\big) = \delta \|\ell\|.$$
-/
theorem sSup_neg_apply_closedBall (ℓ : E →L[ℝ] ℝ) (hδ : 0 ≤ δ) :
    sSup ((fun s => -ℓ s) '' closedBall 0 δ) = δ * ‖ℓ‖ := by
  rcases hδ.eq_or_lt with rfl | hδ
  · simp
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt
    ((nonempty_closedBall.2 hδ.le).image _) (forall_mem_image.2 fun s hs => ?_) fun b hb => ?_
  · calc -ℓ s ≤ ‖ℓ s‖ := (neg_le_abs _).trans (Real.norm_eq_abs _).ge
      _ ≤ ‖ℓ‖ * ‖s‖ := ℓ.le_opNorm s
      _ ≤ δ * ‖ℓ‖ := by rw [mul_comm]; gcongr; exact mem_closedBall_zero_iff.1 hs
  · obtain ⟨u, hu, hbu⟩ := ℓ.exists_lt_apply_of_lt_opNorm (r := b / δ)
      (by rwa [div_lt_iff₀ hδ, mul_comm])
    rw [div_lt_iff₀ hδ, Real.norm_eq_abs] at hbu
    have hmem : ∀ c : ℝ, |c| ≤ 1 → c • δ • u ∈ closedBall (0 : E) δ := fun c hc => by
      rw [mem_closedBall_zero_iff, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos hδ]
      calc |c| * (δ * ‖u‖) ≤ 1 * (δ * 1) := by gcongr
        _ = δ := by ring
    rcases le_total 0 (ℓ u) with h | h
    · refine ⟨_, ⟨(-1 : ℝ) • δ • u, hmem (-1) (by simp), rfl⟩, ?_⟩
      simp only [map_smul, smul_eq_mul]
      rw [abs_of_nonneg h] at hbu
      linarith
    · refine ⟨_, ⟨(1 : ℝ) • δ • u, hmem 1 (by simp), rfl⟩, ?_⟩
      simp only [map_smul, smul_eq_mul]
      rw [abs_of_nonpos h] at hbu
      linarith

/-- **The first-order measure**, (12.1.12) of [cartis2022evaluation]. Let $D$ be derivative data on
a real normed space $E$ and $\delta \ge 0$. Without constraints ($S = E$),
$$\phi^\delta_1 = \delta \|D_1\|.$$
It is the supremum of the linear functional $-D_1$ over the ball of radius $\delta$. -/
theorem taylorMeasure_one_eq (D : FormalMultilinearSeries ℝ E ℝ) (hδ : 0 ≤ δ) :
    taylorMeasure D 1 δ univ = δ * ‖D 1‖ := by
  set ℓ : E →L[ℝ] ℝ := continuousMultilinearCurryFin1 ℝ E ℝ (D 1)
  have hℓ : ∀ s, ℓ s = D 1 (fun _ => s) := fun s => by
    simp only [ℓ, continuousMultilinearCurryFin1_apply]
    congr 1
  have hnorm : ‖ℓ‖ = ‖D 1‖ := LinearIsometryEquiv.norm_map _ _
  rw [taylorMeasure_eq_sSup, Set.inter_univ, ← hnorm, ← sSup_neg_apply_closedBall ℓ hδ]
  congr 1
  refine image_congr fun s _ => ?_
  rw [D.taylorDecrement_one_apply, hℓ]

/-- **Perturbation of the Taylor measure** by inexact data, (13.1.6) of [cartis2022evaluation]. Let
$D$ and $D'$ be derivative data on a real normed space, $j \in \mathbb{N}$, $0 \in S$ and
$\delta \ge 0$. Then
$$\big|\phi^\delta_j(D) - \phi^\delta_j(D')\big| \le \sum_{i = 1}^{j} \frac{\|D_i - D'_i\| \,
  \delta^i}{i!}.$$
-/
theorem abs_taylorMeasure_sub_le (D D' : FormalMultilinearSeries ℝ E ℝ) (j : ℕ)
    (h0 : (0 : E) ∈ S) (hδ : 0 ≤ δ) :
    |taylorMeasure D j δ S - taylorMeasure D' j δ S| ≤
      ∑ i ∈ Icc 1 j, ‖D i - D' i‖ * δ ^ i / i ! := by
  refine abs_decrementMeasure_sub_le ⟨0, mem_closedBall_self hδ, h0⟩
    (bddAbove_taylorDecrement D j δ S) (bddAbove_taylorDecrement D' j δ S) fun d hd => ?_
  refine (D.abs_taylorDecrement_sub_le D' j d).trans (sum_le_sum fun i _ => ?_)
  gcongr
  exact mem_closedBall_zero_iff.1 hd.1

/-- **Attainment of the Taylor measure.** Let $E$ be a finite-dimensional real normed space, $D$
derivative data on $E$, $j \in \mathbb{N}$, $S \subseteq E$ closed with $0 \in S$, and
$\delta \ge 0$. Then there is $d \in S$ with $\|d\| \le \delta$ and
$$T_j(0) - T_j(d) = \phi^\delta_j.$$
Such a $d$ is an optimality displacement in the terms of [cartis2022evaluation]. -/
theorem exists_taylorMeasure_eq [FiniteDimensional ℝ E] (D : FormalMultilinearSeries ℝ E ℝ)
    (j : ℕ) (hS : IsClosed S) (h0 : (0 : E) ∈ S) (hδ : 0 ≤ δ) :
    ∃ d ∈ closedBall 0 δ ∩ S, D.taylorDecrement j d = taylorMeasure D j δ S :=
  exists_decrementMeasure_eq hS h0 hδ (D.continuous_taylorDecrement j).continuousOn

/-- The condition (12.1.25) of [cartis2022evaluation] for given optimality radii
$\delta = (\delta_j)$: for the data $D$ and the feasible displacements $S$,
$$\phi^{\delta_j}_j \le \frac{\varepsilon_j \, \delta_j^j}{j!} \quad \text{for } 1 \le j \le
  q.$$

Here the radii $\delta$ are fixed. The $(\varepsilon, \delta)$-approximate minimizer of order
$q$ of the source asks for some radii $\delta \in (0, 1]^q$, which is
`Optimization.IsEpsApprox`. For `D = ftaylorSeries ℝ f x` and $S = E$, this is the notion
without constraints; the variants for constraints use $S = \{ d : x + d \in C \}$. The
tolerances and the radii are sequences `ε δ : ℕ → ℝ`, and only the indices $1 \le j \le q$
matter. -/
def IsEpsDeltaApprox (D : FormalMultilinearSeries ℝ E ℝ) (S : Set E) (q : ℕ) (ε δ : ℕ → ℝ) :
    Prop :=
  ∀ j ∈ Finset.Icc 1 q, taylorMeasure D j (δ j) S ≤ ε j * δ j ^ j / j !

/-- The condition (12.1.25) holds for the radii $\delta$ if and only if $\phi^{\delta_j}_j \le
\varepsilon_j \delta_j^j / j!$ for $1 \le j \le q$. -/
theorem isEpsDeltaApprox_iff {D : FormalMultilinearSeries ℝ E ℝ} {q : ℕ} {ε δ : ℕ → ℝ} :
    IsEpsDeltaApprox D S q ε δ ↔
      ∀ j ∈ Finset.Icc 1 q, taylorMeasure D j (δ j) S ≤ ε j * δ j ^ j / j ! :=
  Iff.rfl

/-- The **$(\varepsilon, \delta)$-approximate minimizer of order $q$**, the key definition of
[cartis2022evaluation] with (12.1.25): there are optimality radii $\delta_j \in (0, 1]$ for
$1 \le j \le q$ such that
$$\phi^{\delta_j}_j \le \frac{\varepsilon_j \, \delta_j^j}{j!} \quad \text{for } 1 \le j \le
  q.$$
-/
def IsEpsApprox (D : FormalMultilinearSeries ℝ E ℝ) (S : Set E) (q : ℕ) (ε : ℕ → ℝ) : Prop :=
  ∃ δ : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, δ j ∈ Ioc (0 : ℝ) 1) ∧ IsEpsDeltaApprox D S q ε δ

/-- The data $D$ give an $(\varepsilon, \delta)$-approximate minimizer of order $q$ if and only if
there are radii $\delta_j \in (0, 1]$ for $1 \le j \le q$ for which the condition (12.1.25)
holds. -/
theorem isEpsApprox_iff {D : FormalMultilinearSeries ℝ E ℝ} {q : ℕ} {ε : ℕ → ℝ} :
    IsEpsApprox D S q ε ↔
      ∃ δ : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, δ j ∈ Ioc (0 : ℝ) 1) ∧ IsEpsDeltaApprox D S q ε δ :=
  Iff.rfl

/-! ### Monotonicity of the low-order measures in the radius -/

section Scale

/-- Scaling a step scales the term of order $i$ of derivative data by $c^i$:
$D_i[c d]^i = c^i D_i[d]^i$. -/
theorem formalMultilinearSeries_apply_smul (D : FormalMultilinearSeries ℝ E ℝ) (i : ℕ) (c : ℝ)
    (d : E) : D i (fun _ => c • d) = c ^ i * D i (fun _ => d) := by
  have := (D i).map_smul_univ (fun _ => c) (fun _ => d)
  simpa [Finset.prod_const] using this

/-- **Scaling of decrements of order at most 2.** Let $D$ be derivative data, $j \le 2$,
$t \in [0, 1]$ and $d \in E$. Then there is $d'$ with $\|d'\| \le t \|d\|$ and
$$t^j \big(T_j(0) - T_j(d)\big) \le T_j(0) - T_j(d').$$

The displacement $d'$ is one of $0$, $t d$ and $-t d$. -/
theorem exists_taylorDecrement_scale_ge (D : FormalMultilinearSeries ℝ E ℝ) {j : ℕ}
    (hj : j ≤ 2) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (d : E) :
    ∃ d', ‖d'‖ ≤ t * ‖d‖ ∧ t ^ j * D.taylorDecrement j d ≤ D.taylorDecrement j d' := by
  interval_cases j
  · refine ⟨0, by rw [norm_zero]; positivity, ?_⟩
    simp [FormalMultilinearSeries.taylorDecrement_eq]
  · refine ⟨t • d, by rw [norm_smul, Real.norm_of_nonneg ht0], ?_⟩
    rw [FormalMultilinearSeries.taylorDecrement_one_apply,
      FormalMultilinearSeries.taylorDecrement_one_apply, formalMultilinearSeries_apply_smul]
    ring_nf; rfl
  · set a := -(D 1 fun _ => d)
    set b := -2⁻¹ * D 2 fun _ => d
    have hT : ∀ c : ℝ, D.taylorDecrement 2 (c • d) = c * a + c ^ 2 * b := fun c => by
      rw [FormalMultilinearSeries.taylorDecrement_two, formalMultilinearSeries_apply_smul,
        formalMultilinearSeries_apply_smul]
      simp only [a, b]; ring
    have h1 : D.taylorDecrement 2 d = a + b := by
      have := hT 1; simpa using this
    rcases le_or_gt 0 a with ha | ha
    · refine ⟨t • d, by rw [norm_smul, Real.norm_of_nonneg ht0], ?_⟩
      rw [hT, h1]; nlinarith [mul_nonneg ht0 ha, mul_nonneg (mul_nonneg ht0 ht0) ha]
    · refine ⟨(-t) • d, by rw [norm_smul, norm_neg, Real.norm_of_nonneg ht0], ?_⟩
      rw [hT, h1]; nlinarith [mul_nonneg ht0 (le_of_lt (neg_pos.2 ha)),
        mul_nonneg (mul_nonneg ht0 ht0) (le_of_lt (neg_pos.2 ha))]

/-- **The measures of order at most 2 decrease slowly with the radius**, without constraints. Let
$D$ be derivative data, $j \le 2$ and $0 < \delta' \le \delta$. Then
$$\left(\frac{\delta'}{\delta}\right)^j \phi^\delta_j \le \phi^{\delta'}_j.$$
Equivalently, $\delta \mapsto \phi^\delta_j / \delta^j$ is nonincreasing on $(0, \infty)$. -/
theorem pow_div_mul_taylorMeasure_le (D : FormalMultilinearSeries ℝ E ℝ) {j : ℕ} (hj : j ≤ 2)
    {δ δ' : ℝ} (hδ' : 0 < δ') (hδδ' : δ' ≤ δ) :
    (δ' / δ) ^ j * taylorMeasure D j δ univ ≤ taylorMeasure D j δ' univ := by
  have hδ : 0 < δ := hδ'.trans_le hδδ'
  set t := δ' / δ
  have ht0 : 0 < t := div_pos hδ' hδ
  have ht1 : t ≤ 1 := (div_le_one hδ).2 hδδ'
  have htj : 0 < t ^ j := pow_pos ht0 j
  rw [← le_div_iff₀' htj]
  refine decrementMeasure_le ⟨0, mem_closedBall_self hδ.le, mem_univ _⟩ fun d hd => ?_
  obtain ⟨d', hd'n, hd'⟩ := exists_taylorDecrement_scale_ge D hj ht0.le ht1 d
  have hd'm : d' ∈ closedBall 0 δ' ∩ univ := by
    refine ⟨mem_closedBall_zero_iff.2 (hd'n.trans ?_), mem_univ _⟩
    calc t * ‖d‖ ≤ t * δ := mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hd.1) ht0.le
      _ = δ' := by simp only [t]; field_simp
  rw [le_div_iff₀' htj]
  exact hd'.trans (taylorDecrement_le_taylorMeasure D j hd'm)

end Scale

/-! ### Gradient and Hessian on inner product spaces -/

section Inner

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {f : F → ℝ} {x : F}

/-- On a real Hilbert space, the gradient has the norm of the derivative: $\|\nabla f(x)\|$ equals
the norm of `fderiv ℝ f x`. -/
theorem norm_gradient_eq (f : F → ℝ) (x : F) : ‖gradient f x‖ = ‖fderiv ℝ f x‖ :=
  (InnerProductSpace.toDual ℝ F).symm.norm_map _

/-- On a real Hilbert space, $x$ is an $\varepsilon$-approximate first-order minimizer of $f$ if and
only if $\|\nabla f(x)\| \le \varepsilon$ for the gradient $\nabla f(x)$. -/
theorem isApproxFirstOrder_iff_norm_gradient {ε : ℝ} :
    IsApproxFirstOrder f x ε ↔ ‖gradient f x‖ ≤ ε := by
  rw [isApproxFirstOrder_iff, norm_gradient_eq]

/-- The first-order measure of a function, (12.1.12) of [cartis2022evaluation]: on a real Hilbert
space, for every $f$, $x$ and $\delta \ge 0$,
$$\phi^\delta_{f,1}(x) = \delta \|\nabla f(x)\|.$$

No differentiability is needed: where $f$ is not differentiable, both the gradient and the first
derivative of the jet are $0$ in Lean. -/
theorem taylorMeasure_one_ftaylorSeries (f : F → ℝ) (x : F) {δ : ℝ} (hδ : 0 ≤ δ) :
    taylorMeasure (ftaylorSeries ℝ f x) 1 δ univ = δ * ‖gradient f x‖ := by
  rw [taylorMeasure_one_eq _ hδ, norm_gradient_eq, ← norm_iteratedFDeriv_one]
  rfl

/-- The Riesz map from the dual $F^*$ to $F$, as a real continuous linear map. -/
private noncomputable def rieszL : StrongDual ℝ F →L[ℝ] F :=
  ((InnerProductSpace.toDual ℝ F).symm.toContinuousLinearEquiv :
    StrongDual ℝ F →SL[starRingEnd ℝ] F)

private theorem rieszL_apply (ℓ : StrongDual ℝ F) :
    (rieszL ℓ : F) = (InnerProductSpace.toDual ℝ F).symm ℓ := rfl

/-- The **Hessian operator** $\nabla^2 f(x)$ on a real Hilbert space $F$: the derivative at $x$ of
the gradient $\nabla f$, a bounded linear operator on $F$. -/
noncomputable def hessianOperator (f : F → ℝ) (x : F) : F →L[ℝ] F := fderiv ℝ (gradient f) x

/-- If $f$ is twice continuously differentiable at $x$, then the gradient has at $x$ the derivative
$v \mapsto (\nabla^2 f(x)[v, \cdot])^\sharp$, where $\sharp$ is the Riesz map. -/
private theorem hasFDerivAt_gradient_riesz (hf : ContDiffAt ℝ 2 f x) :
    HasFDerivAt (gradient f) (rieszL.comp (fderiv ℝ (fderiv ℝ f) x)) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  exact rieszL.hasFDerivAt.comp x hd.hasFDerivAt

/-- If $f$ is twice continuously differentiable at $x$, then the gradient is differentiable at $x$,
and its derivative is the Hessian operator $\nabla^2 f(x)$. -/
theorem hasFDerivAt_gradient_hessianOperator (hf : ContDiffAt ℝ 2 f x) :
    HasFDerivAt (gradient f) (hessianOperator f x) x :=
  (hasFDerivAt_gradient_riesz hf).differentiableAt.hasFDerivAt

/-- The Hessian operator represents the Hessian form. Let $F$ be a real Hilbert space and let
$f : F \to \mathbb{R}$ be twice continuously differentiable at $x$. Then for all $u, v \in F$,
$$\langle u, \nabla^2 f(x) v \rangle = \nabla^2 f(x)[u, v],$$
where on the left $\nabla^2 f(x)$ is `Optimization.hessianOperator f x` and on the right it is
the second derivative `iteratedFDeriv ℝ 2 f x`. -/
theorem inner_hessianOperator_apply (hf : ContDiffAt ℝ 2 f x) (u v : F) :
    ⟪u, hessianOperator f x v⟫ = iteratedFDeriv ℝ 2 f x ![u, v] := by
  rw [hessianOperator, (hasFDerivAt_gradient_riesz hf).fderiv,
    ContinuousLinearMap.comp_apply, rieszL_apply, real_inner_comm,
    InnerProductSpace.toDual_symm_apply, iteratedFDeriv_two_apply]
  exact hf.isSymmSndFDerivAt (by simp) v u

/-- If $f$ is twice continuously differentiable at $x$, then the Hessian operator $\nabla^2 f(x)$ is
symmetric. -/
theorem hessianOperator_isSymmetric (hf : ContDiffAt ℝ 2 f x) :
    (hessianOperator f x : F →ₗ[ℝ] F).IsSymmetric := by
  intro u v
  change ⟪hessianOperator f x u, v⟫ = ⟪u, hessianOperator f x v⟫
  rw [real_inner_comm, inner_hessianOperator_apply hf, inner_hessianOperator_apply hf,
    iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
  exact hf.isSymmSndFDerivAt (by simp) _ _

/-- On a finite-dimensional real inner product space, if $f$ is twice continuously differentiable at
$x$, then $\lambda_{\min}[\nabla^2 f(x)]$ is the leftmost eigenvalue of the Hessian operator, as
in Section A.5 of [cartis2022evaluation]. -/
theorem minCurvature_iteratedFDeriv_two_eq_leftmost [FiniteDimensional ℝ F]
    (hf : ContDiffAt ℝ 2 f x) :
    minCurvature (iteratedFDeriv ℝ 2 f x) =
      Subproblem.leftmost (hessianOperator_isSymmetric hf) :=
  minCurvature_eq_leftmost _ fun v w => (inner_hessianOperator_apply hf v w).symm

/-- The Hessian form is symmetric. Let $F$ be a real Hilbert space and let $f : F \to \mathbb{R}$ be
twice continuously differentiable at $x$. Then for all $v, w \in F$,
$$\nabla^2 f(x)[v, w] = \nabla^2 f(x)[w, v].$$
-/
theorem iteratedFDeriv_two_symm (hf : ContDiffAt ℝ 2 f x) (v w : F) :
    iteratedFDeriv ℝ 2 f x ![v, w] = iteratedFDeriv ℝ 2 f x ![w, v] := by
  rw [← inner_hessianOperator_apply hf, ← inner_hessianOperator_apply hf, real_inner_comm]
  exact (hessianOperator_isSymmetric hf w v)

/-- The Hessian operator is bounded by the Hessian form. Let $F$ be a real Hilbert space and let
$f : F \to \mathbb{R}$ be twice continuously differentiable at $x$. Then the operator norm of
the Hessian operator is at most the norm of the bilinear form $\nabla^2 f(x)$:
$$\|\nabla^2 f(x)\|_{\mathrm{op}} \le \|\nabla^2 f(x)\|.$$
-/
theorem norm_hessianOperator_le (hf : ContDiffAt ℝ 2 f x) :
    ‖hessianOperator f x‖ ≤ ‖iteratedFDeriv ℝ 2 f x‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  set w := hessianOperator f x v
  have h : ‖w‖ ^ 2 ≤ ‖iteratedFDeriv ℝ 2 f x‖ * ‖v‖ * ‖w‖ := by
    rw [← real_inner_self_eq_norm_sq]
    change ⟪w, hessianOperator f x v⟫ ≤ _
    rw [inner_hessianOperator_apply hf]
    have := (iteratedFDeriv ℝ 2 f x).le_opNorm ![w, v]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at this
    refine (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ this).trans_eq ?_)
    ring
  rcases (norm_nonneg w).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · nlinarith

/-- **Eigenvectors of the leftmost eigenvalue**, (3.2.3) of [cartis2022evaluation]. Let $F$ be a
finite-dimensional real inner product space and let $f : F \to \mathbb{R}$ be twice continuously
differentiable at $x$, with $\lambda_{\min}[\nabla^2 f(x)] < 0$. Then there is $u \in F$ with
$\|u\| = 1$,
$$\nabla^2 f(x) u = \lambda_{\min}[\nabla^2 f(x)] \, u \quad \text{and} \quad \langle u, \nabla
  f(x) \rangle \le 0.$$
-/
theorem exists_eigenvector_hessianOperator [FiniteDimensional ℝ F] (hf : ContDiffAt ℝ 2 f x)
    (hlam : minCurvature (iteratedFDeriv ℝ 2 f x) < 0) :
    ∃ u, ‖u‖ = 1 ∧ hessianOperator f x u = minCurvature (iteratedFDeriv ℝ 2 f x) • u ∧
      ⟪u, gradient f x⟫ ≤ 0 := by
  rcases subsingleton_or_nontrivial F with hE | hE
  · rw [minCurvature_of_subsingleton] at hlam
    exact absurd hlam (lt_irrefl _)
  obtain ⟨u, hu, -, hev, hgu⟩ := exists_eigenvector_minCurvature (A := iteratedFDeriv ℝ 2 f x)
    (iteratedFDeriv_two_symm hf) (gradient f x)
  refine ⟨u, hu, ext_inner_left ℝ fun w => ?_, hgu⟩
  rw [inner_hessianOperator_apply hf, iteratedFDeriv_two_symm hf, hev, inner_smul_right,
    real_inner_comm]

end Inner

section InnerMonomial

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Cauchy–Schwarz for the decrement measure.** Let $F$ be a real inner product space, $v \in F$,
$\delta \in \mathbb{R}$ and $S \subseteq F$, and suppose that some $d \in S$ has
$\|d\| \le \delta$. Then the measure of the linear decrement $d \mapsto \langle v, d \rangle$ is
at most $\delta \|v\|$:
$$\sup \{ \langle v, d \rangle : \|d\| \le \delta, \ d \in S \} \le \delta \|v\|.$$
-/
theorem decrementMeasure_inner_le {v : F} {δ : ℝ} {S : Set F}
    (hne : (closedBall 0 δ ∩ S).Nonempty) : decrementMeasure (fun d => ⟪v, d⟫) δ S ≤ δ * ‖v‖ :=
  decrementMeasure_le hne fun d hd => (real_inner_le_norm v d).trans (by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (mem_closedBall_zero_iff.1 hd.1) (norm_nonneg v))

/-- Let $F$ be a real inner product space, $e \in F$ a unit vector, $a \ge 0$, $\delta \ge 0$ and
$m \in \mathbb{N}$. Without constraints, the measure of the decrement
$d \mapsto a \langle e, d \rangle^m$ with radius $\delta$ is
$$\sup_{\|d\| \le \delta} a \langle e, d \rangle^m = a \delta^m.$$
It is attained at $d = \delta e$. -/
theorem decrementMeasure_mul_inner_pow {e : F} (he : ‖e‖ = 1) {a δ : ℝ} {m : ℕ}
    (ha : 0 ≤ a) (hδ : 0 ≤ δ) :
    decrementMeasure (fun d => a * ⟪e, d⟫ ^ m) δ univ = a * δ ^ m := by
  have hle : ∀ d ∈ closedBall (0 : F) δ ∩ univ, a * ⟪e, d⟫ ^ m ≤ a * δ ^ m := fun d hd => by
    have h1 : |⟪e, d⟫| ≤ δ := (abs_real_inner_le_norm e d).trans (by
      rw [he, one_mul]; simpa using hd.1)
    refine mul_le_mul_of_nonneg_left ((le_abs_self _).trans ?_) ha
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h1 m
  refine le_antisymm (decrementMeasure_le ⟨0, mem_closedBall_self hδ, mem_univ _⟩ hle) ?_
  have hmem : δ • e ∈ closedBall (0 : F) δ ∩ univ :=
    ⟨by rw [mem_closedBall_zero_iff, norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_nonneg hδ],
      mem_univ _⟩
  have := le_decrementMeasure (Δ := fun d => a * ⟪e, d⟫ ^ m) ⟨a * δ ^ m, forall_mem_image.2 hle⟩
    hmem
  simpa only [inner_smul_right, real_inner_self_eq_norm_sq, he, one_pow, mul_one] using this

end InnerMonomial

section Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {f : EuclideanSpace ℝ ι → ℝ}
  {x : EuclideanSpace ℝ ι}

/-- The **Hessian matrix** of a function $f$ on `EuclideanSpace ℝ ι` at $x$, in the standard basis
$(e_i)$:
$$[\nabla^2 f(x)]_{ij} = \nabla^2 f(x)[e_i, e_j] = \frac{\partial^2 f}{\partial x_i \partial
  x_j}(x).$$
-/
noncomputable def hessianMatrix (f : EuclideanSpace ℝ ι → ℝ) (x : EuclideanSpace ℝ ι) :
    Matrix ι ι ℝ :=
  fun i j => iteratedFDeriv ℝ 2 f x ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]

/-- The entry $(i, j)$ of the Hessian matrix is $\nabla^2 f(x)[e_i, e_j]$. -/
theorem hessianMatrix_apply (i j : ι) :
    hessianMatrix f x i j =
      iteratedFDeriv ℝ 2 f x ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] := rfl

/-- If $f$ is twice continuously differentiable at $x$, then the Hessian matrix represents the
Hessian operator: the linear map of the matrix is `Optimization.hessianOperator f x`. -/
theorem toEuclideanLin_hessianMatrix (hf : ContDiffAt ℝ 2 f x) :
    Matrix.toEuclideanLin (hessianMatrix f x) =
      (hessianOperator f x : EuclideanSpace ℝ ι →ₗ[ℝ] _) := by
  have e : hessianMatrix f x = LinearMap.toMatrix (EuclideanSpace.basisFun ι ℝ).toBasis
      (EuclideanSpace.basisFun ι ℝ).toBasis
      (hessianOperator f x : EuclideanSpace ℝ ι →ₗ[ℝ] _) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    have h := EuclideanSpace.inner_single_left i (1 : ℝ)
      (hessianOperator f x (EuclideanSpace.single j 1))
    simp only [map_one, one_mul] at h
    simp [hessianMatrix, ← h, inner_hessianOperator_apply hf]
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, e, Matrix.toLin_toMatrix]

/-- If $f$ is twice continuously differentiable at $x$, then
$\nabla^2 f(x)[v, w] = \langle v, H w \rangle$ for all $v, w$, where $H$ is the Hessian matrix. -/
theorem iteratedFDeriv_two_eq_inner_hessianMatrix (hf : ContDiffAt ℝ 2 f x)
    (v w : EuclideanSpace ℝ ι) :
    iteratedFDeriv ℝ 2 f x ![v, w] = ⟪v, Matrix.toEuclideanLin (hessianMatrix f x) w⟫ := by
  rw [toEuclideanLin_hessianMatrix hf, ContinuousLinearMap.coe_coe,
    inner_hessianOperator_apply hf]

/-- If $f$ is twice continuously differentiable at $x$, then the Hessian matrix is symmetric. -/
theorem hessianMatrix_isHermitian (hf : ContDiffAt ℝ 2 f x) : (hessianMatrix f x).IsHermitian :=
  Matrix.isSymmetric_toEuclideanLin_iff.mp
    (toEuclideanLin_hessianMatrix hf ▸ hessianOperator_isSymmetric hf)

/-- If $f$ is twice continuously differentiable at $x$, then $\lambda_{\min}[\nabla^2 f(x)]$ is the
least eigenvalue of the Hessian matrix, as in (1.1.5) and Section A.5 of [cartis2022evaluation].
Both sides are $0$ when the index type $\iota$ is empty. -/
theorem minCurvature_iteratedFDeriv_two_eq_iInf_eigenvalues (hf : ContDiffAt ℝ 2 f x) :
    minCurvature (iteratedFDeriv ℝ 2 f x) = ⨅ i, (hessianMatrix_isHermitian hf).eigenvalues i :=
  minCurvature_eq_iInf_isHermitian_eigenvalues _ (iteratedFDeriv_two_eq_inner_hessianMatrix hf)

end Matrix

end Optimization
