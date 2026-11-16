/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Constrained
import Numlib.Optimization.Optimality.Unconstrained

/-!
# Second-order optimality conditions for constrained problems

This file proves second-order necessary and sufficient optimality conditions for $\min f$ subject to
finitely many equality constraints $h_i(x) = 0$ and inequality constraints $g_j(x) \le 0$ on a real
normed space, finite-dimensional where needed. It follows Theorems 1.1.3 and 1.1.4 of
[cartis2022evaluation] and Theorems 12.5 and 12.6 of [nocedal2006numerical]. The conventions are
those of `Numlib.Optimization.Constrained`: the Lagrangian is
$$\mathcal{L}(y) = f(y) + \sum_i \lambda_i h_i(y) + \sum_j \mu_j g_j(y)$$
with multipliers $\mu \ge 0$, and LICQ is `Constrained.IsRegularPointIneq`. The constraints
$c(x) \ge 0$ of [cartis2022evaluation], with the Lagrangian $f - \langle y, c \rangle$, are the
instance $g = -c$, $\mu = y$. The equality-constrained Theorem 1.1.3 is the instance with no
inequality constraints ($\kappa$ empty).

The conditions are stated on the **critical cone**: the directions $d$ that are tangent to the
equality constraints and to the active inequality constraints with positive multiplier, and that
point into the active inequality constraints with zero multiplier. The necessary condition is
$\nabla^2 \mathcal{L}(x)[d]^2 \ge 0$ on the critical cone; the sufficient condition is
$\nabla^2 \mathcal{L}(x)[d]^2 > 0$ for nonzero $d$ in the critical cone.

## Main definitions

* `Constrained.kktLagrangian`: the Lagrangian $y \mapsto f(y) + \sum_i \lambda_i h_i(y) + \sum_j
  \mu_j g_j(y)$ for fixed multipliers.
* `Constrained.criticalCone`: the critical cone $\mathcal{N}_+$ of (1.1.17) of
  [cartis2022evaluation].
* `Constrained.stronglyActiveFeasible`: the feasible points at which every inequality constraint
  with a positive multiplier is active.

## Main results

* `Constrained.secondOrder_necessary_of_isKKTPoint`: at a regular local minimizer, for any
  Karush–Kuhn–Tucker multipliers, $\nabla^2 \mathcal{L}(x)[d]^2 \ge 0$ on the critical cone
  ((1.1.14) and (1.1.17) of [cartis2022evaluation]).
* `Constrained.secondOrder_necessary_ineq`: at a regular local minimizer there are
  Karush–Kuhn–Tucker multipliers with this property.
* `Constrained.secondOrder_necessary_of_isKKTPoint_of_tangent`: the second-order necessary condition
  under the tangent qualification for the strongly active feasible set.
* `Constrained.isStrictLocalMinOn_of_secondOrder_sufficient`: a Karush–Kuhn–Tucker point with
  $\nabla^2 \mathcal{L}(x)[d]^2 > 0$ for nonzero $d$ in the critical cone is a strict local
  minimizer ((1.1.15) and (1.1.18) of [cartis2022evaluation]); no constraint qualification is
  needed.
* `Constrained.IsRegularPoint.isRegularPointIneq`, `Constrained.feasible_of_isEmpty`,
  `Constrained.kktLagrangian_of_isEmpty`: the equality-constrained case (Theorem 1.1.3 of
  [cartis2022evaluation]) is the instance with no inequality constraints.

## Proof outline

The tangent qualification for second-order necessity asks that the critical directions lie in the
positive tangent cone of the strongly active feasible set. On that set the Lagrangian equals the
objective, so a second-order expansion of the stationary Lagrangian along tangent sequences gives
nonnegative curvature. Under LICQ the feasible arcs of `Constrained.exists_contDiff_feasible_arc`
give this qualification. The sufficient conditions require positive curvature on the nonzero
directions of the critical cone.

## Notation

* $\nabla^2 \mathcal{L}(x)[d]^2$: the second derivative of the Lagrangian at $x$ applied to
  $(d, d)$, which is `iteratedFDeriv ℝ 2 (Constrained.kktLagrangian f h g l μ) x (fun _ => d)`.
-/

open Filter Set Topology

namespace Constrained

/-! ### The Lagrangian and the critical cone -/

section Defs

variable {E : Type*} {ι κ : Type*}

/-- The **critical cone** $\mathcal{N}_+$ at $x$ for the multipliers $\mu$: the set of directions
$d$ with
* $h_i'(x) d = 0$ for all $i$;
* $g_j'(x) d = 0$ for every active $j$ with $\mu_j > 0$;
* $g_j'(x) d \le 0$ for every active $j$ with $\mu_j = 0$.

This is (1.1.17) of [cartis2022evaluation], with $g = -c$.

The cone puts no condition for an active $j$ with $\mu_j < 0$; at a Karush–Kuhn–Tucker point
this case does not occur. -/
def criticalCone [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] (h' : ι → E → E →L[ℝ] ℝ)
    (g : κ → E → ℝ) (g' : κ → E → E →L[ℝ] ℝ) (x : E) (μ : κ → ℝ) : Set E :=
  {d | (∀ i, h' i x d = 0) ∧ (∀ j ∈ activeSet g x, 0 < μ j → g' j x d = 0) ∧
    ∀ j ∈ activeSet g x, μ j = 0 → g' j x d ≤ 0}

/-- A direction $d$ is in the critical cone if and only if $h_i'(x) d = 0$ for all $i$,
$g_j'(x) d = 0$ for every active $j$ with $\mu_j > 0$, and $g_j'(x) d \le 0$ for every active
$j$ with $\mu_j = 0$. -/
@[simp]
theorem mem_criticalCone [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    {h' : ι → E → E →L[ℝ] ℝ} {g : κ → E → ℝ} {g' : κ → E → E →L[ℝ] ℝ} {x : E} {μ : κ → ℝ}
    {d : E} :
    d ∈ criticalCone h' g g' x μ ↔ (∀ i, h' i x d = 0) ∧
      (∀ j ∈ activeSet g x, 0 < μ j → g' j x d = 0) ∧
      ∀ j ∈ activeSet g x, μ j = 0 → g' j x d ≤ 0 := Iff.rfl

variable [Fintype ι] [Fintype κ]

/-- The **Lagrangian** of the mixed problem, for fixed multipliers $\lambda \in \mathbb{R}^\iota$
and $\mu \in \mathbb{R}^\kappa$, as a function of $y$:
$$\mathcal{L}(y) = f(y) + \sum_i \lambda_i h_i(y) + \sum_j \mu_j g_j(y).$$
This is (1.1.1) of [cartis2022evaluation], with $g = -c$. -/
def kktLagrangian (f : E → ℝ) (h : ι → E → ℝ) (g : κ → E → ℝ) (l : ι → ℝ) (μ : κ → ℝ) (y : E) :
    ℝ :=
  f y + ∑ i, l i * h i y + ∑ j, μ j * g j y

/-- The Lagrangian at $y$ is $f(y) + \sum_i \lambda_i h_i(y) + \sum_j \mu_j g_j(y)$. -/
theorem kktLagrangian_apply (f : E → ℝ) (h : ι → E → ℝ) (g : κ → E → ℝ) (l : ι → ℝ) (μ : κ → ℝ)
    (y : E) : kktLagrangian f h g l μ y = f y + ∑ i, l i * h i y + ∑ j, μ j * g j y := rfl

/-- Let $\mu_j \ge 0$ for all $j$, and let $y$ be feasible. Then $\mathcal{L}(y) \le f(y)$. -/
theorem kktLagrangian_le {f : E → ℝ} {h : ι → E → ℝ} {g : κ → E → ℝ} {l : ι → ℝ} {μ : κ → ℝ}
    (hμ : ∀ j, 0 ≤ μ j) {y : E} (hy : y ∈ feasible h g) : kktLagrangian f h g l μ y ≤ f y := by
  rw [kktLagrangian_apply]
  have h1 : ∑ i, l i * h i y = 0 := Finset.sum_eq_zero fun i _ => by rw [hy.1 i, mul_zero]
  have h2 : ∑ j, μ j * g j y ≤ 0 :=
    Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (hμ j) (hy.2 j)
  linarith

/-- Let $h_i(y) = 0$ for all $i$ and $\mu_j g_j(y) = 0$ for all $j$. Then $\mathcal{L}(y) = f(y)$.
-/
theorem kktLagrangian_eq {f : E → ℝ} {h : ι → E → ℝ} {g : κ → E → ℝ} {l : ι → ℝ} {μ : κ → ℝ}
    {y : E} (hh : ∀ i, h i y = 0) (hg : ∀ j, μ j * g j y = 0) :
    kktLagrangian f h g l μ y = f y := by
  simp [kktLagrangian_apply, hh, hg]

/-- The Lagrangian of the mixed problem is the equality-constrained Lagrangian
`Constrained.lagrangian` plus the inequality terms: $\mathcal{L}(y) = f(y) + \sum_i \lambda_i
h_i(y) + \sum_j \mu_j g_j(y)$, where the first two terms are `Constrained.lagrangian f h y l`. -/
theorem kktLagrangian_eq_lagrangian_add (f : E → ℝ) (h : ι → E → ℝ) (g : κ → E → ℝ) (l : ι → ℝ)
    (μ : κ → ℝ) (y : E) :
    kktLagrangian f h g l μ y = lagrangian f h y l + ∑ j, μ j * g j y := rfl

/-- If there are no inequality constraints ($\kappa$ is empty), the Lagrangian is the
equality-constrained Lagrangian `Constrained.lagrangian`. -/
theorem kktLagrangian_of_isEmpty [IsEmpty κ] (f : E → ℝ) (h : ι → E → ℝ) (g : κ → E → ℝ)
    (l : ι → ℝ) (μ : κ → ℝ) : kktLagrangian f h g l μ = fun y => lagrangian f h y l := by
  ext y
  simp [kktLagrangian_eq_lagrangian_add]

omit [Fintype ι] [Fintype κ] in
/-- If there are no inequality constraints ($\kappa$ is empty), the feasible set of the mixed
constraints is the feasible set of the equality constraints. -/
theorem feasible_of_isEmpty [IsEmpty κ] (h : ι → E → ℝ) (g : κ → E → ℝ) :
    feasible h g = feasibleEq h := by
  ext y
  simp

end Defs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι κ : Type*} [Fintype ι]
  [Fintype κ]

section Lagrangian

variable {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {h : ι → E → ℝ} {h' : ι → E → E →L[ℝ] ℝ}
  {g : κ → E → ℝ} {g' : κ → E → E →L[ℝ] ℝ} {x : E} {l : ι → ℝ} {μ : κ → ℝ}

/-- Let $f$, $h_i$ and $g_j$ have the derivatives $f'(x)$, $h_i'(x)$ and $g_j'(x)$ at $x$. Then the
Lagrangian has the derivative $f'(x) + \sum_i \lambda_i h_i'(x) + \sum_j \mu_j g_j'(x)$ at $x$. -/
theorem hasFDerivAt_kktLagrangian (hf : HasFDerivAt f (f' x) x)
    (hh : ∀ i, HasFDerivAt (h i) (h' i x) x) (hg : ∀ j, HasFDerivAt (g j) (g' j x) x) :
    HasFDerivAt (kktLagrangian f h g l μ)
      (f' x + ∑ i, l i • h' i x + ∑ j, μ j • g' j x) x := by
  have h1 : HasFDerivAt (fun y => ∑ i, l i * h i y) (∑ i, l i • h' i x) x :=
    HasFDerivAt.fun_sum fun i _ => (hh i).const_mul (l i)
  have h2 : HasFDerivAt (fun y => ∑ j, μ j * g j y) (∑ j, μ j • g' j x) x :=
    HasFDerivAt.fun_sum fun j _ => (hg j).const_mul (μ j)
  exact (hf.add h1).add h2

/-- If $f$ and all $h_i$ and $g_j$ are $C^n$ at $x$, then the Lagrangian is $C^n$ at $x$. -/
theorem contDiffAt_kktLagrangian {n : WithTop ℕ∞} (hf : ContDiffAt ℝ n f x)
    (hh : ∀ i, ContDiffAt ℝ n (h i) x) (hg : ∀ j, ContDiffAt ℝ n (g j) x) :
    ContDiffAt ℝ n (kktLagrangian f h g l μ) x :=
  (hf.add (ContDiffAt.sum fun i _ => contDiffAt_const.mul (hh i))).add
    (ContDiffAt.sum fun j _ => contDiffAt_const.mul (hg j))

/-- At a Karush–Kuhn–Tucker point $x$ with multipliers $(\lambda, \mu)$, the Lagrangian satisfies
$\mathcal{L}(x) = f(x)$. -/
theorem IsKKTPoint.kktLagrangian_eq (hx : IsKKTPoint f' h h' g g' x l μ) :
    kktLagrangian f h g l μ x = f x :=
  Constrained.kktLagrangian_eq hx.feasible_eq hx.complementary

/-- Let $x$ be a Karush–Kuhn–Tucker point with multipliers $(\lambda, \mu)$, and let $f$, $h_i$ and
$g_j$ have the derivatives $f'(x)$, $h_i'(x)$ and $g_j'(x)$ at $x$. Then the Lagrangian has the
derivative $0$ at $x$. -/
theorem IsKKTPoint.hasFDerivAt_kktLagrangian (hx : IsKKTPoint f' h h' g g' x l μ)
    (hf : HasFDerivAt f (f' x) x) (hh : ∀ i, HasFDerivAt (h i) (h' i x) x)
    (hg : ∀ j, HasFDerivAt (g j) (g' j x) x) :
    HasFDerivAt (kktLagrangian f h g l μ) (0 : E →L[ℝ] ℝ) x := by
  have := Constrained.hasFDerivAt_kktLagrangian (l := l) (μ := μ) hf hh hg
  rwa [hx.stationary] at this

end Lagrangian

omit [Fintype ι] [Fintype κ] in
/-- Let there be no inequality constraints ($\kappa$ is empty). Then a regular point of the equality
constraints is a regular point of the mixed constraints, for any $g$ and $g'$. So the
equality-constrained theory is the instance with $\kappa$ empty. -/
theorem IsRegularPoint.isRegularPointIneq [IsEmpty κ] {h : ι → E → ℝ} {h' : ι → E → E →L[ℝ] ℝ}
    {x : E} (hx : IsRegularPoint h h' x) (g : κ → E → ℝ) (g' : κ → E → E →L[ℝ] ℝ) :
    IsRegularPointIneq h h' g g' x := by
  have : IsEmpty (activeSet g x) := ⟨fun j => isEmptyElim j.1⟩
  refine ⟨hx.1, isEmptyElim, hx.2.sum_type (linearIndependent_empty_type) ?_⟩
  convert disjoint_bot_right
  rw [Submodule.span_eq_bot]
  rintro _ ⟨j, -⟩
  exact isEmptyElim j

/-! ### Second-order necessary conditions -/

/-- A real function that is $C^2$ at $x$ with derivative $c'$ at $x$ is strictly differentiable at
$x$ with derivative $c'$. -/
private theorem hasStrictFDerivAt_of_contDiffAt_two {c : E → ℝ} {c' : E →L[ℝ] ℝ} {x : E}
    (hc : ContDiffAt ℝ 2 c x) (hc' : HasFDerivAt c c' x) : HasStrictFDerivAt c c' x := by
  have := hc.hasStrictFDerivAt two_ne_zero
  rwa [hc'.fderiv] at this

/-- The **strongly active feasible set** for the multipliers $\mu$: the feasible points $y$ with
$g_j(y) = 0$ for every $j$ with $\mu_j > 0$. -/
def stronglyActiveFeasible (h : ι → E → ℝ) (g : κ → E → ℝ) (μ : κ → ℝ) : Set E :=
  {y ∈ feasible h g | ∀ j, 0 < μ j → g j y = 0}

/-- **Second-order necessary condition under the tangent qualification.** Let $x$ be a
Karush–Kuhn–Tucker point with multipliers $(\lambda, \mu)$ and a local minimizer of $f$ on the
feasible set. Let $f$ and all $h_i$ and $g_j$ be $C^2$ at $x$, with derivatives $f'(x)$,
$h_i'(x)$ and $g_j'(x)$ at $x$. Suppose that the critical cone is contained in the positive
tangent cone of the strongly active feasible set at $x$. Then
$\nabla^2 \mathcal{L}(x)[d]^2 \ge 0$ for every $d$ in the critical cone.

The inclusion of the critical cone in the tangent cone is the second-order constraint
qualification of Theorem 3.2.5 of [conn2000trust]. The positive tangent cone is the Mathlib
`posTangentConeAt`. On the strongly active feasible set the Lagrangian equals $f$, and the proof
expands the stationary Lagrangian to second order along tangent sequences. -/
theorem secondOrder_necessary_of_isKKTPoint_of_tangent {f : E → ℝ}
    {f' : E → E →L[ℝ] ℝ} {h : ι → E → ℝ} {h' : ι → E → E →L[ℝ] ℝ} {g : κ → E → ℝ}
    {g' : κ → E → E →L[ℝ] ℝ} {x : E} {l : ι → ℝ} {μ : κ → ℝ}
    (hkkt : IsKKTPoint f' h h' g g' x l μ) (hmin : IsLocalMinOn f (feasible h g) x)
    (hf : ContDiffAt ℝ 2 f x) (hh : ∀ i, ContDiffAt ℝ 2 (h i) x) (hg : ∀ j, ContDiffAt ℝ 2 (g j) x)
    (hf' : HasFDerivAt f (f' x) x) (hh' : ∀ i, HasFDerivAt (h i) (h' i x) x)
    (hg' : ∀ j, HasFDerivAt (g j) (g' j x) x)
    (hQ : criticalCone h' g g' x μ ⊆ posTangentConeAt (stronglyActiveFeasible h g μ) x) :
    ∀ d ∈ criticalCone h' g g' x μ,
      0 ≤ iteratedFDeriv ℝ 2 (kktLagrangian f h g l μ) x (fun _ ↦ d) := by
  intro d hd
  by_cases hd0 : d = 0
  · simp [hd0, iteratedFDeriv_two_apply]
  obtain ⟨I, F, hF, a, w, hw, hfeas, hdir⟩ := exists_fun_of_mem_tangentConeAt (hQ hd)
  let : F.NeBot := hF
  let L := kktLagrangian f h g l μ
  have hL : ContDiffAt ℝ 2 L x := contDiffAt_kktLagrangian hf hh hg
  have hL0 : fderiv ℝ L x = 0 := (hkkt.hasFDerivAt_kktLagrangian hf' hh' hg').fderiv
  have ha : ∀ᶠ n in F, 0 < (a n : ℝ) := by
    filter_upwards [hdir.eventually ((isClosed_singleton (x := (0 : E))).isOpen_compl.mem_nhds
      (show d ∈ ({0} : Set E)ᶜ from hd0))] with n hn
    change a n • w n ≠ 0 at hn
    exact lt_of_le_of_ne (a n).coe_nonneg (by
      intro h
      exact hn (by simp [NNReal.smul_def, ← h]))
  have hnear : Tendsto (fun n ↦ x + w n) F (𝓝[feasible h g] x) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa using tendsto_const_nhds.add hw (a := x)
    · exact hfeas.mono fun _ hy ↦ hy.1
  have hge : ∀ᶠ n in F, L x ≤ L (x + w n) := by
    filter_upwards [hfeas, hnear.eventually hmin] with n hy hfy
    rw [show L x = f x from hkkt.kktLagrangian_eq]
    refine hfy.trans (le_of_eq ?_)
    refine (kktLagrangian_eq hy.1.1 fun j ↦ ?_).symm
    rcases (hkkt.nonneg j).eq_or_lt with h0 | hp
    · rw [← h0, zero_mul]
    · rw [hy.2 j hp, mul_zero]
  have hlim := Optimization.tendsto_sub_div_sq_of_contDiffAt hL
    (ha.mono fun _ hn ↦ inv_pos.mpr hn) hw
    (show Tendsto (fun n ↦ ((a n : ℝ)⁻¹)⁻¹ • w n) F (𝓝 d) by
      simpa [NNReal.smul_def] using hdir)
  simp only [hL0, zero_apply, sub_zero] at hlim
  have hnonneg := ge_of_tendsto hlim
    (hge.mono fun _ hn ↦ div_nonneg (sub_nonneg.mpr hn) (sq_nonneg _))
  linarith

/-- **LICQ implies the tangent qualification.** Let $E$ be finite-dimensional, and let $x$ be a
regular point of the mixed constraints at which all $h_i$ and $g_j$ are strictly differentiable.
Let $\mu_j \ge 0$ for all $j$, and let every $j$ with $\mu_j > 0$ be active at $x$. Then the
critical cone is contained in the positive tangent cone of the strongly active feasible set at
$x$.

The directions are velocities of the feasible arcs of
`Constrained.exists_contDiff_feasible_arc`. -/
theorem criticalCone_subset_tangent_stronglyActiveFeasible_of_isRegularPointIneq
    [FiniteDimensional ℝ E] {h : ι → E → ℝ} {h' : ι → E → E →L[ℝ] ℝ}
    {g : κ → E → ℝ} {g' : κ → E → E →L[ℝ] ℝ} {x : E} {μ : κ → ℝ}
    (hx : IsRegularPointIneq h h' g g' x)
    (hh : ∀ i, HasStrictFDerivAt (h i) (h' i x) x)
    (hg : ∀ j, HasStrictFDerivAt (g j) (g' j x) x)
    (hμ : ∀ j, 0 ≤ μ j)
    (hactive : ∀ j, 0 < μ j → j ∈ activeSet g x) :
    criticalCone h' g g' x μ ⊆ posTangentConeAt (stronglyActiveFeasible h g μ) x := by
  intro d hd
  obtain ⟨γ, hγ0, hγ, -, hfeas⟩ := exists_contDiff_feasible_arc hx hh hg hd.1 fun j hj ↦ by
    rcases (hμ j).eq_or_lt with h0 | hp
    · exact hd.2.2 j hj h0.symm
    · exact (hd.2.1 j hj hp).le
  have hγlim : Tendsto (fun t ↦ γ t - x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have ht := (hγ.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))).sub_const x
    rwa [hγ0, sub_self] at ht
  refine mem_tangentConeAt_of_seq (𝓝[>] (0 : ℝ)) (fun t ↦ Real.toNNReal t⁻¹)
    (fun t ↦ γ t - x) hγlim (hfeas.mono fun t ht ↦ ?_) ?_
  · simpa only [add_sub_cancel] using
      (show γ t ∈ stronglyActiveFeasible h g μ from ⟨ht.1, fun j hp ↦ by
        rw [ht.2 j (hactive j hp), hd.2.1 j (hactive j hp) hp, mul_zero]⟩)
  · have hslope := hγ.tendsto_slope_zero_right
    simp only [zero_add, hγ0] at hslope
    refine hslope.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [NNReal.smul_def, Real.coe_toNNReal _ (inv_nonneg.mpr (le_of_lt ht))]

/-- **Second-order necessary condition for given multipliers.** Let $E$ be finite-dimensional. Let
$x$ be a local minimizer of $f$ on the feasible set, a regular point of the mixed constraints,
and a Karush–Kuhn–Tucker point with multipliers $(\lambda, \mu)$. Let $f$ and all $h_i$ and
$g_j$ be $C^2$ at $x$, with derivatives $f'(x)$, $h_i'(x)$ and $g_j'(x)$ at $x$. Then
$\nabla^2 \mathcal{L}(x)[d]^2 \ge 0$ for every $d$ in the critical cone. This is (1.1.14) and
(1.1.17) in Theorems 1.1.3 and 1.1.4 of [cartis2022evaluation], and Theorem 12.5 of
[nocedal2006numerical].

Under LICQ the multipliers are unique (`Constrained.kkt_multipliers_unique`). The proof combines
`Constrained.criticalCone_subset_tangent_stronglyActiveFeasible_of_isRegularPointIneq` with
`Constrained.secondOrder_necessary_of_isKKTPoint_of_tangent`. -/
theorem secondOrder_necessary_of_isKKTPoint [FiniteDimensional ℝ E] {f : E → ℝ}
    {f' : E → E →L[ℝ] ℝ} {h : ι → E → ℝ} {h' : ι → E → E →L[ℝ] ℝ} {g : κ → E → ℝ}
    {g' : κ → E → E →L[ℝ] ℝ} {x : E} {l : ι → ℝ} {μ : κ → ℝ}
    (hkkt : IsKKTPoint f' h h' g g' x l μ) (hx : IsRegularPointIneq h h' g g' x)
    (hmin : IsLocalMinOn f (feasible h g) x) (hf : ContDiffAt ℝ 2 f x)
    (hh : ∀ i, ContDiffAt ℝ 2 (h i) x) (hg : ∀ j, ContDiffAt ℝ 2 (g j) x)
    (hf' : HasFDerivAt f (f' x) x) (hh' : ∀ i, HasFDerivAt (h i) (h' i x) x)
    (hg' : ∀ j, HasFDerivAt (g j) (g' j x) x) :
    ∀ d ∈ criticalCone h' g g' x μ,
      0 ≤ iteratedFDeriv ℝ 2 (kktLagrangian f h g l μ) x (fun _ => d) := by
  apply secondOrder_necessary_of_isKKTPoint_of_tangent hkkt hmin hf hh hg hf' hh' hg'
  exact criticalCone_subset_tangent_stronglyActiveFeasible_of_isRegularPointIneq hx
    (fun i ↦ hasStrictFDerivAt_of_contDiffAt_two (hh i) (hh' i))
    (fun j ↦ hasStrictFDerivAt_of_contDiffAt_two (hg j) (hg' j)) hkkt.nonneg
    (fun j hj ↦ (mem_activeSet).mpr ((mul_eq_zero.mp (hkkt.complementary j)).resolve_left hj.ne'))

/-- **Second-order necessary condition.** Let $E$ be finite-dimensional. Let $x$ be a local
minimizer of $f$ on the feasible set and a regular point of the mixed constraints. Let $f$ and
all $h_i$ and $g_j$ be $C^2$ at $x$, with derivatives $h_i'(x)$ and $g_j'(x)$ at $x$. Then there
are multipliers $(\lambda, \mu)$ such that $x$ is a Karush–Kuhn–Tucker point, with the Fréchet
derivative of $f$ as $f'$, and $\nabla^2 \mathcal{L}(x)[d]^2 \ge 0$ for every $d$ in the
critical cone. This is (1.1.14) and (1.1.17) in Theorems 1.1.3 and 1.1.4 of
[cartis2022evaluation], and Theorem 12.5 of [nocedal2006numerical].

The derivative of $f$ is `fderiv ℝ f`. The conclusion holds for any Karush–Kuhn–Tucker
multipliers by `Constrained.secondOrder_necessary_of_isKKTPoint`. The equality-constrained case
is the instance with no inequality constraints
(`Constrained.IsRegularPoint.isRegularPointIneq`). -/
theorem secondOrder_necessary_ineq [FiniteDimensional ℝ E] {f : E → ℝ} {h : ι → E → ℝ}
    {h' : ι → E → E →L[ℝ] ℝ} {g : κ → E → ℝ} {g' : κ → E → E →L[ℝ] ℝ} {x : E}
    (hx : IsRegularPointIneq h h' g g' x) (hmin : IsLocalMinOn f (feasible h g) x)
    (hf : ContDiffAt ℝ 2 f x) (hh : ∀ i, ContDiffAt ℝ 2 (h i) x)
    (hg : ∀ j, ContDiffAt ℝ 2 (g j) x) (hh' : ∀ i, HasFDerivAt (h i) (h' i x) x)
    (hg' : ∀ j, HasFDerivAt (g j) (g' j x) x) :
    ∃ (l : ι → ℝ) (μ : κ → ℝ), IsKKTPoint (fderiv ℝ f) h h' g g' x l μ ∧
      ∀ d ∈ criticalCone h' g g' x μ,
        0 ≤ iteratedFDeriv ℝ 2 (kktLagrangian f h g l μ) x (fun _ => d) := by
  have hfd : HasFDerivAt f (fderiv ℝ f x) x := (hf.differentiableAt (by norm_num)).hasFDerivAt
  obtain ⟨l, μ, hkkt⟩ := exists_kkt_of_isLocalMinOn hx hmin hfd
    (fun i => hasStrictFDerivAt_of_contDiffAt_two (hh i) (hh' i))
    (fun j => hasStrictFDerivAt_of_contDiffAt_two (hg j) (hg' j))
  exact ⟨l, μ, hkkt, secondOrder_necessary_of_isKKTPoint hkkt hx hmin hf hh hg hfd hh' hg'⟩

/-! ### Second-order sufficient conditions -/

/-- **Second-order sufficient condition.** Let $E$ be finite-dimensional, and let $x$ be a
Karush–Kuhn–Tucker point with multipliers $(\lambda, \mu)$. Let $f$ and all $h_i$ and $g_j$ be
$C^2$ at $x$, with derivatives $f'(x)$, $h_i'(x)$ and $g_j'(x)$ at $x$. Suppose that
$\nabla^2 \mathcal{L}(x)[d]^2 > 0$ for every nonzero $d$ in the critical cone. Then $x$ is a
strict local minimizer of $f$ on the feasible set: $f(x) < f(y)$ for every feasible $y \neq x$
near $x$. No constraint qualification is needed. This is (1.1.15) and (1.1.18) in Theorems 1.1.3
and 1.1.4 of [cartis2022evaluation], for nonzero directions, and Theorem 12.6 of
[nocedal2006numerical].

The strict local minimizer is `Optimization.IsStrictLocalMinOn`. A feasible sequence that
violates the conclusion has unit directions that converge to some $d \neq 0$. First-order
expansions and the sign conditions of the Karush–Kuhn–Tucker point put $d$ in the critical cone.
The second-order expansion of $\mathcal{L}$, which is at most $f$ on the feasible set and equal
to $f$ at $x$, then gives $\nabla^2 \mathcal{L}(x)[d]^2 \le 0$. -/
theorem isStrictLocalMinOn_of_secondOrder_sufficient [FiniteDimensional ℝ E] {f : E → ℝ}
    {f' : E → E →L[ℝ] ℝ} {h : ι → E → ℝ} {h' : ι → E → E →L[ℝ] ℝ} {g : κ → E → ℝ}
    {g' : κ → E → E →L[ℝ] ℝ} {x : E} {l : ι → ℝ} {μ : κ → ℝ}
    (hkkt : IsKKTPoint f' h h' g g' x l μ) (hf : ContDiffAt ℝ 2 f x)
    (hh : ∀ i, ContDiffAt ℝ 2 (h i) x) (hg : ∀ j, ContDiffAt ℝ 2 (g j) x)
    (hf' : HasFDerivAt f (f' x) x) (hh' : ∀ i, HasFDerivAt (h i) (h' i x) x)
    (hg' : ∀ j, HasFDerivAt (g j) (g' j x) x)
    (hpos : ∀ d ∈ criticalCone h' g g' x μ, d ≠ 0 →
      0 < iteratedFDeriv ℝ 2 (kktLagrangian f h g l μ) x (fun _ => d)) :
    Optimization.IsStrictLocalMinOn f (feasible h g) x := by
  by_contra hcon
  obtain ⟨y, z, hy, hylim, hz, hyz⟩ := Optimization.exists_seq_of_not_isStrictLocalMinOn hcon
  have hw : Tendsto (fun n => y n - x) atTop (𝓝 0) := by simpa using hylim.sub_const x
  have hr : ∀ᶠ n in atTop, 0 < ‖y n - x‖ :=
    Eventually.of_forall fun n => norm_pos_iff.2 (sub_ne_zero.2 (hy n).2.1)
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  -- limits of first-order quotients
  have hlimF : ∀ {F : E → ℝ} {F' : E →L[ℝ] ℝ}, HasFDerivAt F F' x →
      Tendsto (fun n => (F (y n) - F x) / ‖y n - x‖) atTop (𝓝 (F' z)) := fun hF => by
    have := Optimization.tendsto_sub_div_of_hasFDerivAt hF hr hw hyz
    simpa only [add_sub_cancel] using this
  have hfz : f' x z ≤ 0 :=
    le_of_tendsto' (hlimF hf') fun n => div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.2 (hy n).2.2) (norm_nonneg _)
  have hhz : ∀ i, h' i x z = 0 := fun i => by
    have := hlimF (hh' i)
    simp only [(hy _).1.1 i, hkkt.feasible_eq i, sub_self, zero_div] at this
    exact (tendsto_nhds_unique this tendsto_const_nhds)
  have hgz : ∀ j ∈ activeSet g x, g' j x z ≤ 0 := fun j hj =>
    le_of_tendsto' (hlimF (hg' j)) fun n => by
      rw [mem_activeSet.1 hj, sub_zero]
      exact div_nonpos_of_nonpos_of_nonneg ((hy n).1.2 j) (norm_nonneg _)
  -- complementarity: `μ_j ∇g_j(x)[z] = 0`
  have hstat := congrArg (fun T : E →L[ℝ] ℝ => T z) hkkt.stationary
  simp only [add_apply, sum_apply, smul_apply, smul_eq_mul, hhz, mul_zero,
    Finset.sum_const_zero, add_zero, zero_apply] at hstat
  have hterm : ∀ j, μ j * g' j x z ≤ 0 := fun j => by
    by_cases hj : j ∈ activeSet g x
    · exact mul_nonpos_of_nonneg_of_nonpos (hkkt.nonneg j) (hgz j hj)
    · rw [hkkt.eq_zero_of_notMem_activeSet hj, zero_mul]
  have hzero : ∀ j, μ j * g' j x z = 0 := by
    have hsum : ∑ j, μ j * g' j x z = 0 := by
      refine le_antisymm (Finset.sum_nonpos fun j _ => hterm j) ?_
      linarith
    exact fun j => (Finset.sum_eq_zero_iff_of_nonpos fun j _ => hterm j).1 hsum j
      (Finset.mem_univ j)
  have hcrit : z ∈ criticalCone h' g g' x μ :=
    ⟨hhz, fun j _ hpos => (mul_eq_zero.1 (hzero j)).resolve_left hpos.ne',
      fun j hj _ => hgz j hj⟩
  -- second order along the sequence
  set L := kktLagrangian f h g l μ
  have hL : ContDiffAt ℝ 2 L x := contDiffAt_kktLagrangian hf hh hg
  have hL0 : fderiv ℝ L x = 0 := (hkkt.hasFDerivAt_kktLagrangian hf' hh' hg').fderiv
  have h2 := Optimization.tendsto_sub_div_sq_of_contDiffAt hL hr hw hyz
  simp only [add_sub_cancel, hL0, zero_apply, sub_zero] at h2
  have hle : iteratedFDeriv ℝ 2 L x (fun _ => z) / 2 ≤ 0 := by
    refine le_of_tendsto' h2 fun n => div_nonpos_of_nonpos_of_nonneg ?_ (sq_nonneg _)
    have h1 : L (y n) ≤ f (y n) := kktLagrangian_le hkkt.nonneg (hy n).1
    have h2 : L x = f x := hkkt.kktLagrangian_eq
    linarith [(hy n).2.2]
  linarith [hpos z hcrit hz0]

end Constrained
