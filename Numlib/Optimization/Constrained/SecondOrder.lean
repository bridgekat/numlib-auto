/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Constrained
import Numlib.Optimization.Optimality.Unconstrained

/-!
# Second-order optimality conditions for constrained problems

Second-order necessary and sufficient optimality conditions for `min f` subject to equality
constraints `h i x = 0` and inequality constraints `g j x ≤ 0` on a finite-dimensional real normed
space ([cartis2022evaluation], Theorems 1.1.3 and 1.1.4; Nocedal–Wright, *Numerical
Optimization*, Theorems 12.5 and 12.6), in the conventions of `Numlib.Optimization.Constrained`:
Lagrangian `ℒ = f + ∑ λ_i h_i + ∑ μ_j g_j`, multipliers `μ ≥ 0`, LICQ = `IsRegularPointIneq`.
Constraints `c(x) ≥ 0` with `ℒ = f - ⟨y, c⟩`, as in [cartis2022evaluation], are the instance
`g = -c`, `μ = y`, and the equality-constrained Theorem 1.1.3 is the instance with no inequality
constraints (`κ = Empty`).

## Main definitions

* `Constrained.kktLagrangian f h g l μ`: the Lagrangian `y ↦ f y + ∑ λ_i h_i y + ∑ μ_j g_j y`;
* `Constrained.criticalCone h' g g' x μ`: the critical cone `𝒩₊` of (1.1.17).

## Main results

* `Constrained.secondOrder_necessary_of_isKKTPoint`: at a regular local minimizer, for any
  Karush–Kuhn–Tucker multipliers, `∇²ℒ(x)[d]² ≥ 0` on the critical cone ((1.1.14), (1.1.17));
  `Constrained.secondOrder_necessary_ineq` is the form with existence of the multipliers;
* `Constrained.secondOrder_necessary_of_isKKTPoint_of_tangent`: second-order necessity under
  the tangent qualification for the feasible set with strongly active constraints held active;
* `Constrained.isStrictLocalMinOn_of_secondOrder_sufficient`: a Karush–Kuhn–Tucker point with
  `∇²ℒ(x)[d]² > 0` for nonzero `d` of the critical cone is a strict local minimizer ((1.1.15),
  (1.1.18)); no constraint qualification is needed;
* `Constrained.IsRegularPoint.isRegularPointIneq`, `Constrained.feasible_of_isEmpty`,
  `Constrained.kktLagrangian_of_isEmpty`: the equality-constrained case (Theorem 1.1.3) is the
  instance with no inequality constraints.

## Implementation notes

The tangent qualification for second-order necessity places the critical directions in the
positive tangent cone of the strongly active feasible set. On that set the Lagrangian equals the
objective, so a second-order expansion of the stationary Lagrangian along tangent sequences yields
nonnegative curvature. The feasible arcs of `Constrained.exists_contDiff_feasible_arc` establish
this qualification under LICQ. The sufficient conditions (1.1.15) and (1.1.18) require positive
curvature on the nonzero directions of the critical cone.
-/

open Filter Set Topology

namespace Constrained

/-! ### The Lagrangian and the critical cone -/

section Defs

variable {E : Type*} {ι κ : Type*}

/-- The critical cone `𝒩₊` of [cartis2022evaluation], (1.1.17) (with `g = -c`): directions
tangent to the equality constraints and to the active inequality constraints with positive
multiplier, and pointing into the active inequality constraints with zero multiplier. -/
def criticalCone [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] (h' : ι → E → E →L[ℝ] ℝ)
    (g : κ → E → ℝ) (g' : κ → E → E →L[ℝ] ℝ) (x : E) (μ : κ → ℝ) : Set E :=
  {d | (∀ i, h' i x d = 0) ∧ (∀ j ∈ activeSet g x, 0 < μ j → g' j x d = 0) ∧
    ∀ j ∈ activeSet g x, μ j = 0 → g' j x d ≤ 0}

/-- Membership in the critical cone. -/
@[simp]
theorem mem_criticalCone [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    {h' : ι → E → E →L[ℝ] ℝ} {g : κ → E → ℝ} {g' : κ → E → E →L[ℝ] ℝ} {x : E} {μ : κ → ℝ}
    {d : E} :
    d ∈ criticalCone h' g g' x μ ↔ (∀ i, h' i x d = 0) ∧
      (∀ j ∈ activeSet g x, 0 < μ j → g' j x d = 0) ∧
      ∀ j ∈ activeSet g x, μ j = 0 → g' j x d ≤ 0 := Iff.rfl

variable [Fintype ι] [Fintype κ]

/-- The Lagrangian `ℒ(y) = f(y) + ∑ λ_i h_i(y) + ∑ μ_j g_j(y)` of the mixed problem as a function
of `y`, for fixed multipliers `(λ, μ)` ([cartis2022evaluation], (1.1.1) with `g = -c`). -/
def kktLagrangian (f : E → ℝ) (h : ι → E → ℝ) (g : κ → E → ℝ) (l : ι → ℝ) (μ : κ → ℝ) (y : E) :
    ℝ :=
  f y + ∑ i, l i * h i y + ∑ j, μ j * g j y

/-- Unfolding lemma for `kktLagrangian`. -/
theorem kktLagrangian_apply (f : E → ℝ) (h : ι → E → ℝ) (g : κ → E → ℝ) (l : ι → ℝ) (μ : κ → ℝ)
    (y : E) : kktLagrangian f h g l μ y = f y + ∑ i, l i * h i y + ∑ j, μ j * g j y := rfl

/-- With nonnegative inequality multipliers, the Lagrangian is below `f` on the feasible set. -/
theorem kktLagrangian_le {f : E → ℝ} {h : ι → E → ℝ} {g : κ → E → ℝ} {l : ι → ℝ} {μ : κ → ℝ}
    (hμ : ∀ j, 0 ≤ μ j) {y : E} (hy : y ∈ feasible h g) : kktLagrangian f h g l μ y ≤ f y := by
  rw [kktLagrangian_apply]
  have h1 : ∑ i, l i * h i y = 0 := Finset.sum_eq_zero fun i _ => by rw [hy.1 i, mul_zero]
  have h2 : ∑ j, μ j * g j y ≤ 0 :=
    Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (hμ j) (hy.2 j)
  linarith

/-- If the equality constraints hold at `y` and every `μ_j g_j(y)` vanishes, the Lagrangian equals
`f` at `y`. -/
theorem kktLagrangian_eq {f : E → ℝ} {h : ι → E → ℝ} {g : κ → E → ℝ} {l : ι → ℝ} {μ : κ → ℝ}
    {y : E} (hh : ∀ i, h i y = 0) (hg : ∀ j, μ j * g j y = 0) :
    kktLagrangian f h g l μ y = f y := by
  simp [kktLagrangian_apply, hh, hg]

/-- The Lagrangian of the mixed problem is the equality-constrained Lagrangian
`Constrained.lagrangian` plus the inequality terms. -/
theorem kktLagrangian_eq_lagrangian_add (f : E → ℝ) (h : ι → E → ℝ) (g : κ → E → ℝ) (l : ι → ℝ)
    (μ : κ → ℝ) (y : E) :
    kktLagrangian f h g l μ y = lagrangian f h y l + ∑ j, μ j * g j y := rfl

/-- Without inequality constraints the Lagrangian is `Constrained.lagrangian`. -/
theorem kktLagrangian_of_isEmpty [IsEmpty κ] (f : E → ℝ) (h : ι → E → ℝ) (g : κ → E → ℝ)
    (l : ι → ℝ) (μ : κ → ℝ) : kktLagrangian f h g l μ = fun y => lagrangian f h y l := by
  ext y
  simp [kktLagrangian_eq_lagrangian_add]

omit [Fintype ι] [Fintype κ] in
/-- Without inequality constraints the feasible set is that of the equality constraints. -/
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

/-- The derivative of the Lagrangian: `∇ℒ = ∇f + ∑ λ_i ∇h_i + ∑ μ_j ∇g_j`. -/
theorem hasFDerivAt_kktLagrangian (hf : HasFDerivAt f (f' x) x)
    (hh : ∀ i, HasFDerivAt (h i) (h' i x) x) (hg : ∀ j, HasFDerivAt (g j) (g' j x) x) :
    HasFDerivAt (kktLagrangian f h g l μ)
      (f' x + ∑ i, l i • h' i x + ∑ j, μ j • g' j x) x := by
  have h1 : HasFDerivAt (fun y => ∑ i, l i * h i y) (∑ i, l i • h' i x) x :=
    HasFDerivAt.fun_sum fun i _ => (hh i).const_mul (l i)
  have h2 : HasFDerivAt (fun y => ∑ j, μ j * g j y) (∑ j, μ j • g' j x) x :=
    HasFDerivAt.fun_sum fun j _ => (hg j).const_mul (μ j)
  exact (hf.add h1).add h2

/-- The Lagrangian of `Cⁿ` data is `Cⁿ`. -/
theorem contDiffAt_kktLagrangian {n : WithTop ℕ∞} (hf : ContDiffAt ℝ n f x)
    (hh : ∀ i, ContDiffAt ℝ n (h i) x) (hg : ∀ j, ContDiffAt ℝ n (g j) x) :
    ContDiffAt ℝ n (kktLagrangian f h g l μ) x :=
  (hf.add (ContDiffAt.sum fun i _ => contDiffAt_const.mul (hh i))).add
    (ContDiffAt.sum fun j _ => contDiffAt_const.mul (hg j))

/-- At a Karush–Kuhn–Tucker point the Lagrangian equals `f`. -/
theorem IsKKTPoint.kktLagrangian_eq (hx : IsKKTPoint f' h h' g g' x l μ) :
    kktLagrangian f h g l μ x = f x :=
  Constrained.kktLagrangian_eq hx.feasible_eq hx.complementary

/-- At a Karush–Kuhn–Tucker point the Lagrangian is stationary. -/
theorem IsKKTPoint.hasFDerivAt_kktLagrangian (hx : IsKKTPoint f' h h' g g' x l μ)
    (hf : HasFDerivAt f (f' x) x) (hh : ∀ i, HasFDerivAt (h i) (h' i x) x)
    (hg : ∀ j, HasFDerivAt (g j) (g' j x) x) :
    HasFDerivAt (kktLagrangian f h g l μ) (0 : E →L[ℝ] ℝ) x := by
  have := Constrained.hasFDerivAt_kktLagrangian (l := l) (μ := μ) hf hh hg
  rwa [hx.stationary] at this

end Lagrangian

omit [Fintype ι] [Fintype κ] in
/-- A regular point of the equality constraints is a regular point of the mixed constraints when
there are no inequality constraints: the equality-constrained theory is the instance
`κ = Empty`. -/
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

/-- Strict differentiability of a constraint `C²` at `x`, with prescribed derivative. -/
private theorem hasStrictFDerivAt_of_contDiffAt_two {c : E → ℝ} {c' : E →L[ℝ] ℝ} {x : E}
    (hc : ContDiffAt ℝ 2 c x) (hc' : HasFDerivAt c c' x) : HasStrictFDerivAt c c' x := by
  have := hc.hasStrictFDerivAt two_ne_zero
  rwa [hc'.fderiv] at this

/-- The feasible points that keep every inequality with a positive multiplier
active. -/
def stronglyActiveFeasible (h : ι → E → ℝ) (g : κ → E → ℝ) (μ : κ → ℝ) : Set E :=
  {y ∈ feasible h g | ∀ j, 0 < μ j → g j y = 0}

/-- Second-order necessity under tangent inclusion for the strongly active
feasible set. This is the second-order constraint qualification in
[conn2000trust], Theorem 3.2.5. -/
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

/-- LICQ implies the tangent inclusion for the strongly active feasible set. -/
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

/-- **Second-order necessary condition for given multipliers** ([cartis2022evaluation],
Theorems 1.1.3 and 1.1.4, (1.1.14) and (1.1.17); Nocedal–Wright Theorem 12.5), under LICQ. In
finite dimension, let `x` be a local minimizer of `f` on the feasible set, a regular point of the
constraints, and a Karush–Kuhn–Tucker point with multipliers `(λ, μ)` (under LICQ these are
unique, `kkt_multipliers_unique`), with `f` and all constraints `C²` at `x` with derivatives
`f' x`, `h' i x`, `g' j x` there. Then `∇²ℒ(x)[d]² ≥ 0` for every `d` in the critical cone. -/
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

/-- **Second-order necessary condition** ([cartis2022evaluation], Theorems 1.1.3 and 1.1.4,
(1.1.14) and (1.1.17); Nocedal–Wright Theorem 12.5), under LICQ. In finite dimension, let `x` be a
local minimizer of `f` on the feasible set, a regular point of the constraints, with `f` and all
constraints `C²` at `x` and the constraint derivatives at `x` given by `h' i x`, `g' j x`. Then
there are multipliers `(λ, μ)` making `x` a Karush–Kuhn–Tucker point such that
`∇²ℒ(x)[d]² ≥ 0` for every `d` in the critical cone (for any such multipliers:
`secondOrder_necessary_of_isKKTPoint`). The equality-constrained case is the instance with no
inequality constraints (`IsRegularPoint.isRegularPointIneq`). -/
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

/-- **Second-order sufficient condition** ([cartis2022evaluation], Theorems 1.1.3 and 1.1.4,
(1.1.15) and (1.1.18), for nonzero directions; Nocedal–Wright Theorem 12.6). In finite dimension,
let `x` be a Karush–Kuhn–Tucker point with multipliers `(λ, μ)`, with `f` and all constraints `C²`
at `x` and derivatives `f' x`, `h' i x`, `g' j x` there, and suppose `∇²ℒ(x)[d]² > 0` for every
nonzero `d` in the critical cone. Then `x` is a strict local minimizer of `f` on the feasible
set. No constraint qualification is needed.

Proof: a violating feasible sequence has
unit directions converging to some `d ≠ 0`; first-order expansions and the sign conditions of the
Karush–Kuhn–Tucker point put `d` in the critical cone, and the second-order expansion of `ℒ`,
which is `≤ f` on the feasible set and `= f` at `x`, gives `∇²ℒ(x)[d]² ≤ 0`. -/
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
