/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Calculus.SpaceTime
import Numlib.Analysis.SpecialFunctions.Sqrt
import Numlib.Analysis.PDE.Transport
import Numlib.Approximation.BrokenInterpolation
import Numlib.Variational.Evolution

/-!
# Error analysis of space–time Galerkin methods for the transport equation

This file proves convergence estimates for the continuous and the discontinuous Galerkin
semi-discretizations in space of the transport equation
$$\partial_t u + a\, \partial_x u + a_0 u = f \quad \text{on } (x_0, x_n) \times (0, T),$$
with broken polynomials of degree at most $r$ on a partition $x_0 < x_1 < \dots < x_n$. These are
the estimates of [quarteroni2000numerical], §13.10.1, which quotes them without proof from
[quarteroni1994numerical], §14.3. The regularity of the exact solution is a hypothesis: for every
$t \in [0, T]$, the function $u(\cdot, t)$ lies in $H^{r+1}(x_0, x_n)$, and for the continuous
method also $\partial_t u(\cdot, t)$ does, with bounds on the $H^{r+1}$ seminorms that are uniform
in $t$. With explicit constants, the error of the continuous method is $O(\|u_0 - u_{0,h}\| + h^r)$,
and the error of the discontinuous method is $O(\|u_0 - u_{0,h}\| + h^{r+1/2})$.

The panels are $I_i = [x_i, x_{i+1}]$ for $0 \le i < n$, and $B_h$ is the space of broken
polynomials: families $v = (v_i)$ of polynomials of degree at most $r$, one for each panel, with no
continuity across the nodes. For a function $g$, the norm $\|g - v\| = (\sum_i \int_{I_i} (g -
v_i)^2)^{1/2}$ is the panelwise $L^2(x_0, x_n)$ norm, and $(g, v) = \sum_i \int_{I_i} g\, v_i$ is
the pairing. The traces of $v$ at a node are $v^+(x_i) = v_i(x_i)$ and $v^-(x_i) = v_{i-1}(x_i)$,
with $v^-(x_0) = 0$, and the jump is $[v]_i = v^+(x_i) - v^-(x_i)$. The transport form is $b(w, v) =
\sum_i \int_{I_i} (a w_i' + a_0 w_i) v_i$, and the upwind form is $b^{DG}(w, v) = b(w, v) + \sum_i
a(x_i) [w]_i v^+(x_i)$. The nodal interpolant is $\Pi_h$, and the $L^2$ projection onto $B_h$ is
$P_h$.

## Main definitions

* `Variational.dgConst`: the explicit constant $C_{DG}$ of the discontinuous Galerkin error
  estimate.

## Main results

* `Variational.IsSemidiscreteGalerkin.sub`: the error equation; the difference of a solution of a
  semi-discrete Galerkin problem and any curve $W$ that is differentiable in time solves the same
  problem with the consistency error of $W$ as source.
* `Variational.hasDerivWithinAt_interp`: the nodal interpolant commutes with $\partial_t$.
* `Variational.hasDerivWithinAt_proj`: the $L^2$ projection commutes with $\partial_t$.
* `SobolevInterval.ae_eq_deriv_one_of_hasDerivAt`: the classical derivative of a continuous
  representative of an $H^{k+1}$ function is its weak derivative almost everywhere.
* `Variational.abs_transport_defect_le`: the consistency error of the transport form is bounded by
  the approximation errors of $u$, $\partial_x u$ and $\partial_t u$.
* `Variational.dg_defect_le`: the consistency error of the upwind form at the $L^2$ projection of
  the exact solution is bounded from above by the $L^2$ projection error, the traces of the
  projection error at the nodes, and jump and outflow terms of the test function with the weight
  $\tfrac{1}{4}$.
* `Variational.sum_mul_sq_sub_proj_le`: a weighted sum of the squared traces of the projection error
  at points of the panels is $O(h^{2r+1})$.
* `Variational.cG_error_le`: the error estimate of the continuous Galerkin method.
* `Variational.dG_error_sq_le`, `Variational.dG_error_le`: the error estimate of the discontinuous
  Galerkin method, in squared form and in the form of the source.

## Proof outline

The error equation `Variational.IsSemidiscreteGalerkin.sub` says that $u_h - W$ solves the
semi-discrete problem with the consistency error $(f, \cdot) - \langle \partial_t W, \cdot\rangle -
b_t(W, \cdot)$ as source and $u_{0,h} - W(0)$ as initial datum. For the continuous method
$W(t) = \Pi_h u(\cdot, t)$, and for the discontinuous method $W(t) = P_h u(\cdot, t)$. Both commute
with $\partial_t$, so the consistency error is an approximation error of $\partial_t u$ in $L^2$ and
of $u$ in $H^1$, of order $h^r$ by the estimates of `Numlib.Approximation.BrokenInterpolation`. The
energy estimate `Variational.IsSemidiscreteGalerkin.norm_sq_add_integral_le` then bounds $u_h - W$,
and the triangle inequality finishes the proof. For the discontinuous method, the dissipation of the
upwind form absorbs the traces of the projection error at the nodes, which are of order $h^{r+1/2}$.
The classical derivative $\partial_x u$ of the solution is identified with the weak derivative of
its $H^{r+1}$ representative by `SobolevInterval.ae_eq_deriv_one_of_hasDerivAt`.

## Implementation notes

* The space $B_h$ is `BrokenPolynomial x r` with its $L^2(x_0, x_n)$ inner product. The norms of the
  errors of non-polynomial functions are written as square roots of sums of panel integrals.
* The regularity of $u(\cdot, t)$ is the existence of some `U : SobolevInterval (r + 1) (x 0) (x
  (Fin.last n))` equal to $u(\cdot, t)$ almost everywhere on $(x_0, x_n)$, with a bound on
  `SobolevInterval.seminorm`.
* The space $V_h$ of the continuous method is any submodule of $B_h$ whose elements are exactly the
  continuous broken polynomials with $v^+(x_0) = 0$.
* [quarteroni2000numerical] states the boundary term of the continuous estimate at the inflow end
  $x_0$, where it vanishes because $u$ and $u_h$ both satisfy the inflow condition.
  `Variational.cG_error_le` has the boundary term at the outflow end $x_n$, where the energy
  identity produces it.
* In the discontinuous estimate, the jump $[u - u_h]_0$ of the source is $\varphi - u_h^+(x_0)$,
  because $u$ is continuous and $u(x_0) = \varphi$.
-/

open Set Filter Topology intervalIntegral Real MeasureTheory Polynomial TopologicalSpace
open scoped RealInnerProductSpace Interval

noncomputable section

namespace Variational

/-! ### The error equation of a semi-discrete Galerkin method -/

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- The **error equation** of a semi-discrete Galerkin problem. Let $K$ be a real inner product
space, let $a(t)$ be bounded bilinear forms and $F(t)$ bounded linear functionals on $K$, and
let $u$ solve the semi-discrete problem $\langle u'(t), v\rangle + a(t)(u(t), v) = F(t)v$ for
all $v \in K$ and $t \in [0, T]$, with $u(0) = u_0$. Let $W : \mathbb{R} \to K$ have the
derivative $W'(t)$ within $[0, T]$ at every $t \in [0, T]$. Then $u - W$ solves the
semi-discrete problem with the source
$$t \mapsto F(t) - \bigl(\langle W'(t), \cdot\rangle + a(t)(W(t), \cdot)\bigr)$$
and the initial datum $u_0 - W(0)$.

The semi-discrete problem is `Variational.IsSemidiscreteGalerkin`. When $W$ is an interpolant or
a projection of the exact solution, this is the equation for the discrete error $u - W$, and its
source is the consistency error of $W$. -/
theorem IsSemidiscreteGalerkin.sub {a : ℝ → SesqForm ℝ K} {F : ℝ → K →L[ℝ] ℝ} {u₀ : K} {T : ℝ}
    {u : ℝ → K} (h : IsSemidiscreteGalerkin a F u₀ T u) {W W' : ℝ → K}
    (hW : ∀ t ∈ Icc 0 T, HasDerivWithinAt W (W' t) (Icc 0 T) t) :
    IsSemidiscreteGalerkin a (fun t => F t - (innerSL ℝ (W' t) + a t (W t))) (u₀ - W 0) T
      (fun t => u t - W t) := by
  obtain ⟨h0, u', hu'⟩ := h
  refine ⟨by simp only [h0], fun t => u' t - W' t,
    fun t ht => ⟨(hu' t ht).1.sub (hW t ht), fun v => ?_⟩⟩
  have := (hu' t ht).2 v
  simp only [inner_sub_left, map_sub, sub_apply, add_apply, innerSL_apply_apply]
  linarith

/-! ### The time derivative of an interpolant -/

variable {n : ℕ} {x : Fin (n + 1) → ℝ} {r : ℕ} [hx : Fact (StrictMono x)]
  {node : Fin n → Fin (r + 1) → ℝ}

/-- Interpolation from nodal values that depend on time is differentiable in time. Let $x$ be a
strictly increasing partition, let the nodes of each panel be distinct, and let each nodal value
$c_{ij}(t)$ have the derivative $c'_{ij}$ within a set $s$ at $t$. Then the broken polynomial
that interpolates the values $c(t)$ has, within $s$ at $t$, the derivative equal to the broken
polynomial that interpolates the values $c'$.

The interpolation map is `BrokenPolynomial.ofValuesₗ`. It is a linear map on a
finite-dimensional space, hence continuous, so the derivative passes through it. -/
theorem hasDerivWithinAt_ofValuesₗ (hinj : ∀ i, Function.Injective (node i))
    {c : ℝ → Fin n → Fin (r + 1) → ℝ} {c' : Fin n → Fin (r + 1) → ℝ} {s : Set ℝ} {t : ℝ}
    (hc : ∀ i j, HasDerivWithinAt (fun t => c t i j) (c' i j) s t) :
    HasDerivWithinAt (fun t => BrokenPolynomial.ofValuesₗ x r node hinj (c t))
      (BrokenPolynomial.ofValuesₗ x r node hinj c') s t := by
  have hc' : HasDerivWithinAt c c' s t :=
    hasDerivWithinAt_pi.2 fun i => hasDerivWithinAt_pi.2 fun j => hc i j
  exact (LinearMap.toContinuousLinearMap
    (BrokenPolynomial.ofValuesₗ x r node hinj)).hasFDerivAt.comp_hasDerivWithinAt t hc'

/-- The **nodal interpolant commutes with the time derivative**. Let $x$ be a strictly increasing
partition with a node system of degree $r$, and let $u$ and $u_t$ be functions of $(y, t)$ such
that, for every $y \in [x_0, x_n]$, the function $t \mapsto u(y, t)$ has the derivative
$u_t(y, t)$ within $[0, T]$ at $t$. Then $t \mapsto \Pi_h u(\cdot, t)$ has the derivative
$\Pi_h u_t(\cdot, t)$ within $[0, T]$ at $t$.

The interpolant $\Pi_h$ is `BrokenPolynomial.interp`, and the proof specializes
`Variational.hasDerivWithinAt_ofValuesₗ`. -/
theorem hasDerivWithinAt_interp (hnode : BrokenPolynomial.IsNodes x r node) {u ut : ℝ → ℝ → ℝ}
    {T t : ℝ}
    (hu : ∀ y ∈ Icc (x 0) (x (Fin.last n)),
      HasDerivWithinAt (fun t => u y t) (ut y t) (Icc 0 T) t) :
    HasDerivWithinAt (fun t => BrokenPolynomial.interp hnode fun y => u y t)
      (BrokenPolynomial.interp hnode fun y => ut y t) (Icc 0 T) t :=
  hasDerivWithinAt_ofValuesₗ hnode.injective fun i j =>
    hu (node i j) (BrokenPolynomial.Icc_panel_subset hx.out.monotone i (hnode.mem i j))

end Variational

/-! ### The classical derivative of an $H^1$ function is its weak derivative -/

open SobolevInterval in
/-- The classical derivative of a representative of an $H^{k+1}$ function is its weak derivative.
Let $a < b$, let $U \in H^{k+1}(a, b)$, and let $f$ be continuous on $[a, b]$ with $U = f$
almost everywhere on $(a, b)$. If $f$ has the derivative $f'(y)$ at every $y \in (a, b)$, then
$f' = U'$ almost everywhere on $(a, b)$, where $U'$ is the first weak derivative
`SobolevInterval.deriv U 1`.

The proof writes $f(y) = c + \int_a^y U'$ on $[a, b]$ by the absolutely continuous
representative, and then applies the Lebesgue differentiation theorem. -/
theorem SobolevInterval.ae_eq_deriv_one_of_hasDerivAt {a b : ℝ} (hab : a < b) {k : ℕ}
    (U : SobolevInterval (k + 1) a b) {f f' : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hU : fn U =ᵐ[volume.restrict (Ioo a b)] f) (hf' : ∀ y ∈ Ioo a b, HasDerivAt f (f' y) y) :
    f' =ᵐ[volume.restrict (Ioo a b)] SobolevInterval.deriv U 1 := by
  have hw : HasWeakDerivOn (fn U) (SobolevInterval.deriv U 1) (Opens.Ioo a b) := by
    have := hasWeakDerivOn_deriv_succ U 0
    rwa [Fin.castSucc_zero, deriv_zero, Fin.succ_zero_eq_one] at this
  have hint : IntegrableOn (SobolevInterval.deriv U 1) (Ioo a b) :=
    SobolevIntervalLp.integrableOn_deriv_Ioo U 1
  obtain ⟨g, hg, hUg, hgint⟩ := hw.exists_continuousOn_ae_eq hab hint
  have hfg : EqOn f g (Icc a b) := eqOn_Icc_of_ae_eq hab hf hg (hU.symm.trans hUg)
  have hii : IntervalIntegrable (SobolevInterval.deriv U 1) volume a b :=
    hint.intervalIntegrable_of_Ioo (left_mem_Icc.2 hab.le) (right_mem_Icc.2 hab.le)
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hii.ae_hasDerivAt_integral] with y hy hyI
  have hyIcc : y ∈ Icc a b := Ioo_subset_Icc_self hyI
  have h1 : HasDerivAt (fun x => g a + ∫ t in a..x, SobolevInterval.deriv U 1 t)
      (SobolevInterval.deriv U 1 y) y :=
    (hy (uIcc_of_le hab.le ▸ hyIcc) a (uIcc_of_le hab.le ▸ left_mem_Icc.2 hab.le)).const_add _
  have hev : f =ᶠ[𝓝 y] fun x => g a + ∫ t in a..x, SobolevInterval.deriv U 1 t := by
    filter_upwards [Icc_mem_nhds hyI.1 hyI.2] with z hz
    rw [hfg hz, ← hgint a (left_mem_Icc.2 hab.le) z hz]
    ring
  exact (hf' y hyI).unique (h1.congr_of_eventuallyEq hev)

namespace Variational

open BrokenPolynomial

variable {n : ℕ} {x : Fin (n + 1) → ℝ} {r : ℕ} [hx : Fact (StrictMono x)] {a : ℝ → ℝ}

section FixedTime

variable {a₀ : ℝ → ℝ}

/-- The **consistency error of the transport form** at a fixed time. Let $x$ be a strictly
increasing partition, let $a$ and $a_0$ be integrable on $[x_0, x_n]$, let $a$ be continuous on
$[x_0, x_n]$, and let $|a| \le A$ and $|a_0| \le A_0$ on $[x_0, x_n]$ for constants
$A, A_0 \ge 0$. Let $u$ and $u_t$ be continuous on $[x_0, x_n]$, with $u_t + a u_x + a_0 u = f$
at every point of $[x_0, x_n]$. Let $g$ be a function such that $g$ and $g^2$ are integrable on
$[x_0, x_n]$ and $u_x = g$ almost everywhere on $(x_0, x_n)$. Let $W, W' \in B_h$ satisfy
$$\|u - W\| \le E_u, \qquad \|u_t - W'\| \le E_{u'}, \qquad \|g - \partial_x W\| \le E_g,$$
where $\partial_x W$ is the panelwise derivative of $W$. Then for every $v \in B_h$
$$\bigl|(f, v) - \langle W', v\rangle - b(W, v)\bigr|
  \le (E_{u'} + A E_g + A_0 E_u) \|v\|.$$

In the error analysis, $W$ and $W'$ are the interpolants of $u$ and $u_t$, and the left side is
the consistency error of the pair $(W, W')$ in the semi-discrete equation. The form $b$ is
`Variational.transportForm`, and the pairing is `BrokenPolynomial.pairing`. -/
theorem abs_transport_defect_le (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : IntervalIntegrable a₀ volume (x 0) (x (Fin.last n)))
    (hac : ContinuousOn a (Icc (x 0) (x (Fin.last n)))) {A A₀ : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ s ∈ Icc (x 0) (x (Fin.last n)), |a s| ≤ A) (hA₀0 : 0 ≤ A₀)
    (hA₀ : ∀ s ∈ Icc (x 0) (x (Fin.last n)), |a₀ s| ≤ A₀) {u ux ut f : ℝ → ℝ}
    (huc : ContinuousOn u (Icc (x 0) (x (Fin.last n))))
    (hutc : ContinuousOn ut (Icc (x 0) (x (Fin.last n))))
    (hpde : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ut y + a y * ux y + a₀ y * u y = f y)
    {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (x 0) (x (Fin.last n)))
    (hg2 : IntervalIntegrable (fun s => g s ^ 2) volume (x 0) (x (Fin.last n)))
    (hux : ux =ᵐ[volume.restrict (Ioo (x 0) (x (Fin.last n)))] g) (W W' : BrokenPolynomial x r)
    {Eu Eu' Eg : ℝ}
    (hEu : √(∑ i, ∫ s in x i.castSucc..x i.succ, (u s - (W i).eval s) ^ 2) ≤ Eu)
    (hEu' : √(∑ i, ∫ s in x i.castSucc..x i.succ, (ut s - (W' i).eval s) ^ 2) ≤ Eu')
    (hEg : √(∑ i, ∫ s in x i.castSucc..x i.succ, (g s - (derivative (W i)).eval s) ^ 2) ≤ Eg)
    (v : BrokenPolynomial x r) :
    |pairing f v - (⟪W', v⟫ + transportForm x r ha ha₀ W v)|
      ≤ (Eu' + A * Eg + A₀ * Eu) * ‖v‖ := by
  have hm : Monotone x := hx.out.monotone
  have hle : ∀ i : Fin n, x i.castSucc ≤ x i.succ := fun i => hm (Fin.castSucc_lt_succ (i := i)).le
  have hab : x 0 ≤ x (Fin.last n) := hm (Fin.zero_le _)
  have hIcc : ∀ i : Fin n, [[x i.castSucc, x i.succ]] ⊆ Icc (x 0) (x (Fin.last n)) := fun i =>
    (BrokenPolynomial.uIcc_panel_subset hm i).trans (uIcc_of_le hab).le
  -- `ux` is square integrable, being `g` almost everywhere
  have hae : ∀ i : Fin n, ux =ᵐ[volume.restrict (Ι (x i.castSucc) (x i.succ))] g := fun i => by
    rw [uIoc_of_le (hle i), Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
    have hb : ∀ᵐ s : ℝ, s ≠ x i.succ := by simp [ae_iff, measure_singleton]
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 hux, hb] with s hs hsb hsI
    exact hs ⟨(hm (Fin.zero_le _)).trans_lt hsI.1, lt_of_le_of_ne (hsI.2.trans (hm (Fin.le_last _)))
      (fun h => hsb (le_antisymm hsI.2 (h ▸ hm (Fin.le_last _)) |>.symm ▸ rfl))⟩
  have hux_i : ∀ i : Fin n, IntervalIntegrable ux volume (x i.castSucc) (x i.succ) := fun i =>
    (intervalIntegrable_panel hm hg i).congr_ae (hae i).symm
  have hvc : ∀ i : Fin n, ContinuousOn (fun s => (v i).eval s) [[x i.castSucc, x i.succ]] :=
    fun i => (v i).continuous.continuousOn
  have hWc : ∀ (w : BrokenPolynomial x r) (i : Fin n),
      ContinuousOn (fun s => (w i).eval s) [[x i.castSucc, x i.succ]] :=
    fun w i => (w i).continuous.continuousOn
  have hW'c : ∀ (w : BrokenPolynomial x r) (i : Fin n),
      ContinuousOn (fun s => (derivative (w i)).eval s) [[x i.castSucc, x i.succ]] :=
    fun w i => (derivative (w i)).continuous.continuousOn
  -- the defect as a sum of three panel sums
  set S₁ := ∑ i, ∫ s in x i.castSucc..x i.succ, (ut s - (W' i).eval s) * (v i).eval s with hS₁
  set S₂ := ∑ i, ∫ s in x i.castSucc..x i.succ,
    a s * (ux s - (derivative (W i)).eval s) * (v i).eval s with hS₂
  set S₃ := ∑ i, ∫ s in x i.castSucc..x i.succ, a₀ s * (u s - (W i).eval s) * (v i).eval s
    with hS₃
  have hD : pairing f v - (⟪W', v⟫ + transportForm x r ha ha₀ W v) = S₁ + S₂ + S₃ := by
    rw [pairing_def, BrokenPolynomial.inner_def, transportForm_apply, hS₁, hS₂, hS₃,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have I1 : IntervalIntegrable (fun s => ut s * (v i).eval s) volume (x i.castSucc) (x i.succ) :=
      (hutc.mono (hIcc i)).intervalIntegrable.mul_continuousOn (hvc i)
    have I2 : IntervalIntegrable (fun s => a s * ux s * (v i).eval s) volume
        (x i.castSucc) (x i.succ) :=
      ((hux_i i).continuousOn_mul (hac.mono (hIcc i))).mul_continuousOn (hvc i)
    have I3 : IntervalIntegrable (fun s => a₀ s * u s * (v i).eval s) volume
        (x i.castSucc) (x i.succ) :=
      ((intervalIntegrable_panel hm ha₀ i).mul_continuousOn (huc.mono (hIcc i))).mul_continuousOn
        (hvc i)
    have I4 : IntervalIntegrable (fun s => (W' i).eval s * (v i).eval s) volume
        (x i.castSucc) (x i.succ) := ((hWc W' i).mul (hvc i)).intervalIntegrable
    have I5 : IntervalIntegrable (fun s => a s * (derivative (W i)).eval s * (v i).eval s) volume
        (x i.castSucc) (x i.succ) :=
      ((intervalIntegrable_panel hm ha i).mul_continuousOn (hW'c W i)).mul_continuousOn (hvc i)
    have I6 : IntervalIntegrable (fun s => a₀ s * (W i).eval s * (v i).eval s) volume
        (x i.castSucc) (x i.succ) :=
      ((intervalIntegrable_panel hm ha₀ i).mul_continuousOn (hWc W i)).mul_continuousOn (hvc i)
    have hf : ∫ s in x i.castSucc..x i.succ, f s * (v i).eval s
        = (∫ s in x i.castSucc..x i.succ, ut s * (v i).eval s)
          + (∫ s in x i.castSucc..x i.succ, a s * ux s * (v i).eval s)
          + ∫ s in x i.castSucc..x i.succ, a₀ s * u s * (v i).eval s := by
      rw [← integral_add I1 I2, ← integral_add (I1.add I2) I3]
      refine integral_congr fun s hs => ?_
      rw [← hpde s (hIcc i hs)]
      ring
    have e1 : ∫ s in x i.castSucc..x i.succ, (ut s - (W' i).eval s) * (v i).eval s
        = (∫ s in x i.castSucc..x i.succ, ut s * (v i).eval s)
          - ∫ s in x i.castSucc..x i.succ, (W' i).eval s * (v i).eval s := by
      rw [← integral_sub I1 I4]
      exact integral_congr fun s _ => by ring
    have e2 : ∫ s in x i.castSucc..x i.succ, a s * (ux s - (derivative (W i)).eval s) * (v i).eval s
        = (∫ s in x i.castSucc..x i.succ, a s * ux s * (v i).eval s)
          - ∫ s in x i.castSucc..x i.succ, a s * (derivative (W i)).eval s * (v i).eval s := by
      rw [← integral_sub I2 I5]
      exact integral_congr fun s _ => by ring
    have e3 : ∫ s in x i.castSucc..x i.succ, a₀ s * (u s - (W i).eval s) * (v i).eval s
        = (∫ s in x i.castSucc..x i.succ, a₀ s * u s * (v i).eval s)
          - ∫ s in x i.castSucc..x i.succ, a₀ s * (W i).eval s * (v i).eval s := by
      rw [← integral_sub I3 I6]
      exact integral_congr fun s _ => by ring
    have e4 : ∫ s in x i.castSucc..x i.succ,
        (a s * (derivative (W i)).eval s + a₀ s * (W i).eval s) * (v i).eval s
        = (∫ s in x i.castSucc..x i.succ, a s * (derivative (W i)).eval s * (v i).eval s)
          + ∫ s in x i.castSucc..x i.succ, a₀ s * (W i).eval s * (v i).eval s := by
      rw [← integral_add I5 I6]
      exact integral_congr fun s _ => by ring
    rw [hf, e1, e2, e3, e4]
    ring
  -- the three bounds
  have hS₁' : |S₁| ≤ Eu' * ‖v‖ := by
    refine (abs_sum_integral_mul_eval_le (η := fun i s => ut s - (W' i).eval s)
      (fun i => ((hutc.mono (hIcc i)).sub (hWc W' i)).intervalIntegrable)
      (fun i => (((hutc.mono (hIcc i)).sub (hWc W' i)).pow 2).intervalIntegrable) v).trans ?_
    exact mul_le_mul_of_nonneg_right hEu' (norm_nonneg _)
  have hS₂' : |S₂| ≤ A * Eg * ‖v‖ := by
    have e : S₂ = ∑ i, ∫ s in x i.castSucc..x i.succ,
        a s * (g s - (derivative (W i)).eval s) * (v i).eval s := by
      rw [hS₂]
      refine Finset.sum_congr rfl fun i _ => integral_congr_ae_restrict ?_
      filter_upwards [hae i] with s hs
      rw [hs]
    rw [e]
    refine (abs_sum_integral_mul_mul_eval_le ha hA0 hA
      (η := fun i s => g s - (derivative (W i)).eval s)
      (fun i => (intervalIntegrable_panel hm hg i).sub (hW'c W i).intervalIntegrable)
      (fun i => intervalIntegrable_sub_sq (intervalIntegrable_panel hm hg i)
        (intervalIntegrable_panel hm hg2 i) (hW'c W i)) v).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEg hA0) (norm_nonneg _)
  have hS₃' : |S₃| ≤ A₀ * Eu * ‖v‖ := by
    refine (abs_sum_integral_mul_mul_eval_le ha₀ hA₀0 hA₀ (η := fun i s => u s - (W i).eval s)
      (fun i => ((huc.mono (hIcc i)).sub (hWc W i)).intervalIntegrable)
      (fun i => (((huc.mono (hIcc i)).sub (hWc W i)).pow 2).intervalIntegrable) v).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEu hA₀0) (norm_nonneg _)
  rw [hD]
  calc |S₁ + S₂ + S₃| ≤ |S₁| + |S₂| + |S₃| := abs_add_three _ _ _
    _ ≤ Eu' * ‖v‖ + A * Eg * ‖v‖ + A₀ * Eu * ‖v‖ := by linarith
    _ = (Eu' + A * Eg + A₀ * Eu) * ‖v‖ := by ring

end FixedTime

section TimeDependent

variable {a₀ : ℝ → ℝ → ℝ}

/-- For $E, B \ge 0$, $E + \sqrt{B} \le \sqrt{2} \sqrt{E^2 + B}$, by
`Real.sqrt_add_sqrt_le_sqrt_two_mul`. -/
private theorem add_sqrt_le_sqrt_two_mul_sqrt {E B : ℝ} (hE : 0 ≤ E) (hB : 0 ≤ B) :
    E + √B ≤ √2 * √(E ^ 2 + B) := by
  have h := Real.sqrt_add_sqrt_le_sqrt_two_mul (sq_nonneg E) hB
  rwa [Real.sqrt_sq hE] at h

/-- For $e, d \ge 0$ and $c \le d^2$, $\sqrt{e^2 + c} \le e + d$. -/
private theorem sqrt_sq_add_le {e c d : ℝ} (he : 0 ≤ e) (hd : 0 ≤ d) (hcd : c ≤ d ^ 2) :
    √(e ^ 2 + c) ≤ e + d := by
  calc √(e ^ 2 + c) ≤ √((e + d) ^ 2) := Real.sqrt_le_sqrt (by nlinarith [mul_nonneg he hd])
    _ = e + d := Real.sqrt_sq (add_nonneg he hd)

/-- For $\mu > 0$ and $t \le T$, $\mu^{-1} (t \Phi^2) \le (T / \mu) \Phi^2$. -/
private theorem inv_mul_le_div_mul {μ t T Φ : ℝ} (hμ : 0 < μ) (ht : t ≤ T) :
    μ⁻¹ * (t * Φ ^ 2) ≤ T / μ * Φ ^ 2 := by
  rw [div_eq_inv_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht (sq_nonneg Φ)) (inv_pos.2 hμ).le

/-- For $s \ge 1$ and $P \ge 0$, $P + s(X + P + Q) \le s(X + 2P + Q)$. -/
private theorem add_mul_le_mul_add {s X P Q : ℝ} (hs : 1 ≤ s) (hP : 0 ≤ P) :
    P + s * (X + P + Q) ≤ s * (X + 2 * P + Q) := by nlinarith

/-- The **error estimate of the continuous Galerkin method** for the transport equation. Let
$x_0 < \dots < x_n$ be a partition with $n \ge 1$, panel lengths at most $h$ and a Lagrange node
system of degree $r$, and let $T > 0$. Let $a$ be integrable on $[x_0, x_n]$ and differentiable
at every point of $[x_0, x_n]$ with $a'$ continuous there, let $a_0(\cdot, t)$ be integrable on
$[x_0, x_n]$ for every $t$, let $a(x_n) \ge 0$, and let there be constants $\mu_0 > 0$, $A$ and
$A_0$ with
$$\mu_0 \le a_0(s, t) - \tfrac{1}{2} a'(s), \qquad |a(s)| \le A,
  \qquad |a_0(s, t)| \le A_0$$
for $s \in [x_0, x_n]$ and $t \in [0, T]$. Let $u$ be a classical solution of
$u_t + a u_x + a_0 u = f$ on the strip $[x_0, x_n] \times [0, T]$ with $u(x_0, t) = 0$: at every
point of the strip, $u(\cdot, t)$ has the derivative $u_x$ within $[x_0, x_n]$ and $u(y, \cdot)$
has the derivative $u_t$ within $[0, T]$, and $u_t(\cdot, t)$ is continuous on $[x_0, x_n]$ for
$t \in [0, T]$. Let $u$ be regular: for every $t \in [0, T]$ there are
$U, U' \in H^{r+1}(x_0, x_n)$, equal almost everywhere to $u(\cdot, t)$ and $u_t(\cdot, t)$,
with $|U|_{H^{r+1}} \le M$ and $|U'|_{H^{r+1}} \le M'$. Let $V_h \subseteq B_h$ be the space of
continuous broken polynomials $v$ with $v^+(x_0) = 0$, let $f_h(t) \in B_h$ satisfy
$\langle f_h(t), v\rangle = (f(\cdot, t), v)$ for $v \in V_h$ and $t \in [0, T]$, and let
$u_h : \mathbb{R} \to V_h$ solve the semi-discrete Galerkin problem $\langle u_h'(t), v\rangle +
b_t(u_h(t), v) = \langle f_h(t), v\rangle$ for $v \in V_h$ and $t \in [0, T]$, with
$u_h(0) = u_{0,h}$. Then for every $t \in [0, T]$
$$\|u(t) - u_h(t)\| +
  \Bigl(\int_0^t a(x_n) \bigl(u(x_n, \tau) - u_h^-(x_n, \tau)\bigr)^2 \, d\tau\Bigr)^{1/2}
  \le \sqrt{2} \Bigl(\|u(0) - u_{0,h}\| +
  h^r \bigl(2hM + \sqrt{T / \mu_0}\, (AM + h(M' + A_0 M))\bigr)\Bigr).$$
This is the estimate for continuous finite elements of degree $r$ in [quarteroni2000numerical],
§13.10.1, which quotes it from [quarteroni1994numerical], §14.3.1, without proof; here the
constants are explicit.

The source states the boundary term at the inflow end $x_0$, where it vanishes because $u$ and
$u_h$ both satisfy the inflow condition; the estimate here has it at the outflow end $x_n$,
where the energy identity produces it. The norms are panelwise $L^2$ norms, and $b_t$ is
`Variational.transportForm` with the coefficient $a_0(\cdot, t)$, restricted to $V_h$. The proof
applies the error equation `Variational.IsSemidiscreteGalerkin.sub` with the nodal interpolant
$W(t) = \Pi_h u(\cdot, t)$, which lies in $V_h$, commutes with $\partial_t$ by
`Variational.hasDerivWithinAt_interp`, and interpolates $u$ at $x_n$. Its consistency error is
bounded by `Variational.abs_transport_defect_le` and the interpolation estimates $h^{r+1} M'$
for $u_t$, $h^r M$ for $u_x$ and $h^{r+1} M$ for $u$, and the energy estimate
`Variational.IsSemidiscreteGalerkin.norm_sq_add_integral_le` bounds $u_h - W$. -/
theorem cG_error_le (hn : 0 < n) {T : ℝ} (hT : 0 < T)
    (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n))))
    {μ₀ : ℝ} (hμ : 0 < μ₀)
    (hμ₀ : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc (x 0) (x (Fin.last n)), μ₀ ≤ a₀ s t - deriv a s / 2)
    (hβ : 0 ≤ a (x (Fin.last n))) {A A₀ : ℝ}
    (hA : ∀ s ∈ Icc (x 0) (x (Fin.last n)), |a s| ≤ A)
    (hA₀ : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc (x 0) (x (Fin.last n)), |a₀ s t| ≤ A₀)
    {u ux ut f : ℝ → ℝ → ℝ}
    (hux : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun y => u y t) (ux y t) (Icc (x 0) (x (Fin.last n))) y)
    (hut : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun t => u y t) (ut y t) (Icc 0 T) t)
    (hutc : ∀ t ∈ Icc 0 T, ContinuousOn (fun y => ut y t) (Icc (x 0) (x (Fin.last n))))
    (hpde : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T,
      ut y t + a y * ux y t + a₀ y t * u y t = f y t)
    (hin : ∀ t ∈ Icc 0 T, u (x 0) t = 0) {M M' : ℝ}
    (hreg : ∀ t ∈ Icc 0 T, ∃ U : SobolevInterval (r + 1) (x 0) (x (Fin.last n)),
      SobolevInterval.fn U =ᵐ[volume.restrict (Ioo (x 0) (x (Fin.last n)))] (fun y => u y t) ∧
        SobolevInterval.seminorm (r + 1) (x 0) (x (Fin.last n)) U ≤ M)
    (hreg' : ∀ t ∈ Icc 0 T, ∃ U : SobolevInterval (r + 1) (x 0) (x (Fin.last n)),
      SobolevInterval.fn U =ᵐ[volume.restrict (Ioo (x 0) (x (Fin.last n)))] (fun y => ut y t) ∧
        SobolevInterval.seminorm (r + 1) (x 0) (x (Fin.last n)) U ≤ M')
    {V : Submodule ℝ (BrokenPolynomial x r)}
    (hV : ∀ v, v ∈ V ↔ v ∈ continuous x r ∧ traceRight v ⟨0, hn⟩ = 0)
    {node : Fin n → Fin (r + 1) → ℝ} (hnode : IsLagrangeNodes x r node) {h : ℝ}
    (hmesh : ∀ i : Fin n, x i.succ - x i.castSucc ≤ h)
    {fh : ℝ → BrokenPolynomial x r}
    (hfh : ∀ t ∈ Icc 0 T, ∀ v ∈ V, ⟪fh t, v⟫ = pairing (fun y => f y t) v)
    {u₀h : V} {uh : ℝ → V}
    (huh : IsSemidiscreteGalerkin (fun t => (transportForm x r ha (ha₀ t)).restrict V)
      (fun t => (innerSL ℝ (fh t)).comp V.subtypeL) u₀h T uh)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    √(∑ i, ∫ s in x i.castSucc..x i.succ, (u s t - ((uh t : BrokenPolynomial x r) i).eval s) ^ 2)
      + √(∫ τ in (0 : ℝ)..t, a (x (Fin.last n))
          * (u (x (Fin.last n)) τ - traceLeft (uh τ : BrokenPolynomial x r) (Fin.last n)) ^ 2)
    ≤ √2 * (√(∑ i, ∫ s in x i.castSucc..x i.succ,
          (u s 0 - ((u₀h : BrokenPolynomial x r) i).eval s) ^ 2)
        + h ^ r * (2 * h * M + √(T / μ₀) * (A * M + h * (M' + A₀ * M)))) := by
  have hm : Monotone x := hx.out.monotone
  have hab : x 0 < x (Fin.last n) := hx.out (Fin.pos_iff_ne_zero.2 (Fin.ne_of_val_ne hn.ne'))
  have hT0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hh : 0 ≤ h :=
    (sub_nonneg.2 (hm (Fin.castSucc_lt_succ (i := ⟨0, hn⟩)).le)).trans (hmesh ⟨0, hn⟩)
  obtain ⟨U₀, hU₀, hU₀M⟩ := hreg 0 hT0
  have hM : 0 ≤ M := (apply_nonneg _ _).trans hU₀M
  obtain ⟨U₀', hU₀', hU₀M'⟩ := hreg' 0 hT0
  have hM' : 0 ≤ M' := (apply_nonneg _ _).trans hU₀M'
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA (x 0) (left_mem_Icc.2 hab.le))
  have hA₀0 : 0 ≤ A₀ := (abs_nonneg _).trans (hA₀ 0 hT0 (x 0) (left_mem_Icc.2 hab.le))
  have hac : ContinuousOn a (Icc (x 0) (x (Fin.last n))) := fun s hs =>
    (hd s hs).continuousAt.continuousWithinAt
  have huc : ∀ t ∈ Icc 0 T, ContinuousOn (fun y => u y t) (Icc (x 0) (x (Fin.last n))) :=
    fun t ht y hy => (hux y hy t ht).continuousWithinAt
  have hsub : [[(0 : ℝ), t]] ⊆ Icc 0 T := by
    rw [uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2
  -- the interpolation errors, as bounds on square roots
  have hsqrt : ∀ (U : SobolevInterval (r + 1) (x 0) (x (Fin.last n))) (K : ℝ) (k : ℕ) (X : ℝ),
      X ≤ h ^ (2 * k) * SobolevInterval.seminorm (r + 1) (x 0) (x (Fin.last n)) U ^ 2 →
      SobolevInterval.seminorm (r + 1) (x 0) (x (Fin.last n)) U ≤ K → √X ≤ h ^ k * K := by
    intro U K k X hX hUK
    calc √X ≤ √(h ^ (2 * k) * SobolevInterval.seminorm (r + 1) (x 0) (x (Fin.last n)) U ^ 2) :=
          Real.sqrt_le_sqrt hX
      _ = h ^ k * SobolevInterval.seminorm (r + 1) (x 0) (x (Fin.last n)) U := by
          rw [Real.sqrt_mul (by positivity), pow_mul', Real.sqrt_sq (by positivity),
            Real.sqrt_sq (apply_nonneg _ _)]
      _ ≤ h ^ k * K := mul_le_mul_of_nonneg_left hUK (by positivity)
  -- the interpolants
  set W : ℝ → BrokenPolynomial x r := fun t => interp hnode.toIsNodes fun y => u y t with hW
  set W' : ℝ → BrokenPolynomial x r := fun t => interp hnode.toIsNodes fun y => ut y t with hW'
  have hWV : ∀ t ∈ Icc 0 T, W t ∈ V := fun t ht => (hV _).2
    ⟨interp_mem_continuous hnode _, by rw [traceRight_interp_zero hnode hn, hin t ht]⟩
  have hut0 : ∀ t ∈ Icc 0 T, ut (x 0) t = 0 := fun t ht => by
    have h1 := hut (x 0) (left_mem_Icc.2 hab.le) t ht
    have h2 : HasDerivWithinAt (fun t => u (x 0) t) 0 (Icc 0 T) t :=
      (hasDerivWithinAt_const t _ (0 : ℝ)).congr (fun s hs => hin s hs) (hin t ht)
    exact (uniqueDiffOn_Icc hT t ht).eq_deriv _ h1 h2
  have hW'V : ∀ t ∈ Icc 0 T, W' t ∈ V := fun t ht => (hV _).2
    ⟨interp_mem_continuous hnode _, by rw [traceRight_interp_zero hnode hn, hut0 t ht]⟩
  -- the interpolants as curves in `V`, clamped to `[0, T]`
  set clamp : ℝ → ℝ := fun t => max 0 (min t T) with hclamp
  have hclampmem : ∀ t, clamp t ∈ Icc 0 T := fun t =>
    ⟨le_max_left _ _, max_le hT.le (min_le_right _ _)⟩
  have hclampeq : ∀ t ∈ Icc 0 T, clamp t = t := fun t ht => by
    simp only [hclamp]; rw [min_eq_left ht.2, max_eq_right ht.1]
  set Wv : ℝ → V := fun t => ⟨W (clamp t), hWV _ (hclampmem t)⟩ with hWv
  set Wv' : ℝ → V := fun t => ⟨W' (clamp t), hW'V _ (hclampmem t)⟩ with hWv'
  have hWvd : ∀ t ∈ Icc 0 T, HasDerivWithinAt Wv (Wv' t) (Icc 0 T) t := fun t ht => by
    have h1 : HasDerivWithinAt W (W' t) (Icc 0 T) t :=
      hasDerivWithinAt_interp hnode.toIsNodes fun y hy => hut y hy t ht
    have h2 : HasDerivWithinAt (fun s => W (clamp s)) (W' t) (Icc 0 T) t :=
      h1.congr (fun s hs => by simp only [hclampeq s hs]) (by simp only [hclampeq t ht])
    have h3 := h2.codRestrict_submodule V (fun s => hWV (clamp s) (hclampmem s)) (hW'V t ht)
    have e : Wv' t = ⟨W' t, hW'V t ht⟩ := Subtype.ext (by simp only [hWv', hclampeq t ht])
    rw [e]
    exact h3
  -- the error equation
  have he := huh.sub hWvd
  -- the consistency error
  set Φ := h ^ (r + 1) * M' + A * (h ^ r * M) + A₀ * (h ^ (r + 1) * M) with hΦ
  have hΦ0 : 0 ≤ Φ := by positivity
  have hG : ∀ s ∈ Icc 0 T, ‖(innerSL ℝ (fh s)).comp V.subtypeL
      - (innerSL ℝ (Wv' s) + ((transportForm x r ha (ha₀ s)).restrict V) (Wv s))‖ ≤ Φ := by
    intro s hs
    refine ContinuousLinearMap.opNorm_le_bound _ hΦ0 fun v => ?_
    obtain ⟨U, hU, hUM⟩ := hreg s hs
    obtain ⟨U', hU', hUM'⟩ := hreg' s hs
    have hg := SobolevInterval.intervalIntegrable_deriv hab.le U 1
    have hg2 := SobolevInterval.intervalIntegrable_deriv_sq hab.le U 1
    have hux_ae : (fun y => ux y s) =ᵐ[volume.restrict (Ioo (x 0) (x (Fin.last n)))]
        SobolevInterval.deriv U 1 :=
      SobolevInterval.ae_eq_deriv_one_of_hasDerivAt hab U (huc s hs) hU fun y hy =>
        (hux y (Ioo_subset_Icc_self hy) s hs).hasDerivAt (Icc_mem_nhds hy.1 hy.2)
    have hEu := hsqrt U M (r + 1) _
      (sum_integral_sq_sub_interp_le_seminorm hx.out hn hnode.toIsNodes hmesh U (huc s hs) hU) hUM
    have hEu' := hsqrt U' M' (r + 1) _
      (sum_integral_sq_sub_interp_le_seminorm hx.out hn hnode.toIsNodes hmesh U' (hutc s hs) hU')
      hUM'
    have hEg := hsqrt U M r _
      (sum_integral_sq_deriv_sub_interp_le_seminorm hx.out hn hnode.toIsNodes hmesh U (huc s hs) hU)
      hUM
    have key := abs_transport_defect_le ha (ha₀ s) hac hA0 hA hA₀0 (hA₀ s hs) (huc s hs)
      (hutc s hs) (fun y hy => hpde y hy s hs) hg hg2 hux_ae (W s) (W' s) hEu hEu' hEg
      (v : BrokenPolynomial x r)
    have e : ((innerSL ℝ (fh s)).comp V.subtypeL
        - (innerSL ℝ (Wv' s) + ((transportForm x r ha (ha₀ s)).restrict V) (Wv s))) v
        = pairing (fun y => f y s) (v : BrokenPolynomial x r)
          - (⟪W' s, (v : BrokenPolynomial x r)⟫ + transportForm x r ha (ha₀ s) (W s) v) := by
      simp only [_root_.sub_apply, _root_.add_apply, ContinuousLinearMap.comp_apply,
        Submodule.subtypeL_apply, innerSL_apply_apply, SesqForm.restrict_apply, Submodule.coe_inner,
        hWv, hWv', hclampeq s hs]
      rw [hfh s hs v v.2]
    rw [e, Real.norm_eq_abs]
    exact key
  -- the energy estimate for the discrete error
  have hQc : ContinuousOn (fun s => a (x (Fin.last n))
      * traceLeft ((uh s - Wv s : V) : BrokenPolynomial x r) (Fin.last n) ^ 2) (Icc 0 T) := by
    have hc : Continuous fun v : V => traceLeft (v : BrokenPolynomial x r) (Fin.last n) :=
      (continuous_traceLeft (Fin.last n)).comp continuous_subtype_val
    exact continuousOn_const.mul ((hc.comp_continuousOn he.continuousOn).pow 2)
  have hcoer : ∀ s ∈ Icc 0 T, ∀ v : V, μ₀ * ‖v‖ ^ 2
      + a (x (Fin.last n)) * traceLeft (v : BrokenPolynomial x r) (Fin.last n) ^ 2 / 2
      ≤ (transportForm x r ha (ha₀ s)).restrict V v v := fun s hs v =>
    le_transportForm_restrict ha (ha₀ s) hd hd' hn (hμ₀ s hs) (fun v hv => (hV v).1 hv) v
  have hstab := he.norm_sq_add_integral_le
    (Q := fun _ v => a (x (Fin.last n)) * traceLeft (v : BrokenPolynomial x r) (Fin.last n) ^ 2)
    hμ hQc hcoer (φ := fun _ => Φ) continuousOn_const (fun s hs => hG s hs) ht
  -- the algebra
  set E := ‖uh t - Wv t‖ with hE
  set e0 := ‖u₀h - Wv 0‖ with he0
  set B := ∫ τ in (0 : ℝ)..t, a (x (Fin.last n))
    * traceLeft ((uh τ - Wv τ : V) : BrokenPolynomial x r) (Fin.last n) ^ 2 with hB
  have hB0 : 0 ≤ B := integral_nonneg ht.1 fun s _ => mul_nonneg hβ (sq_nonneg _)
  have hI : B ≤ ∫ τ in (0 : ℝ)..t, (μ₀ * ‖uh τ - Wv τ‖ ^ 2 + a (x (Fin.last n))
      * traceLeft ((uh τ - Wv τ : V) : BrokenPolynomial x r) (Fin.last n) ^ 2) := by
    refine integral_mono_on ht.1 ((hQc.mono hsub).intervalIntegrable) ?_ fun τ _ => ?_
    · exact ((continuousOn_const.mul (he.continuousOn_norm_sq.mono hsub)).add
        (hQc.mono hsub)).intervalIntegrable
    · exact le_add_of_nonneg_left (mul_nonneg hμ.le (sq_nonneg _))
  have hΦint : ∫ τ in (0 : ℝ)..t, Φ ^ 2 = t * Φ ^ 2 := by
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  rw [hΦint] at hstab
  have hmain : E ^ 2 + B ≤ e0 ^ 2 + μ₀⁻¹ * (t * Φ ^ 2) := (add_le_add_right hI _).trans hstab
  have h1 : E + √B ≤ √2 * √(E ^ 2 + B) := add_sqrt_le_sqrt_two_mul_sqrt (norm_nonneg _) hB0
  have h2 : √(E ^ 2 + B) ≤ e0 + √(T / μ₀) * Φ := by
    refine (Real.sqrt_le_sqrt hmain).trans (sqrt_sq_add_le (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) hΦ0) ?_)
    rw [mul_pow, Real.sq_sqrt (div_nonneg hT.le hμ.le)]
    exact inv_mul_le_div_mul hμ ht.2
  -- the initial error
  have hg0 : IntervalIntegrable (fun s => u s 0) volume (x 0) (x (Fin.last n)) :=
    ((huc 0 hT0).mono (uIcc_of_le hab.le).le).intervalIntegrable
  have hg02 : IntervalIntegrable (fun s => u s 0 ^ 2) volume (x 0) (x (Fin.last n)) :=
    (((huc 0 hT0).mono (uIcc_of_le hab.le).le).pow 2).intervalIntegrable
  have hEu0 := hsqrt U₀ M (r + 1) _
    (sum_integral_sq_sub_interp_le_seminorm hx.out hn hnode.toIsNodes hmesh U₀ (huc 0 hT0) hU₀) hU₀M
  have he0' : e0 ≤ √(∑ i, ∫ s in x i.castSucc..x i.succ,
      (u s 0 - ((u₀h : BrokenPolynomial x r) i).eval s) ^ 2) + h ^ (r + 1) * M := by
    have hW0 : ((u₀h - Wv 0 : V) : BrokenPolynomial x r) = (u₀h : BrokenPolynomial x r) - W 0 := by
      simp only [Submodule.coe_sub, hWv, hclampeq 0 hT0]
    have := norm_sub_le_sqrt_add_sqrt hg0 hg02 (u₀h : BrokenPolynomial x r) (W 0)
    rw [he0, ← Submodule.norm_coe, hW0]
    linarith
  -- the error at time `t`
  have hEt : √(∑ i, ∫ s in x i.castSucc..x i.succ,
      (u s t - ((uh t : BrokenPolynomial x r) i).eval s) ^ 2) ≤ h ^ (r + 1) * M + E := by
    obtain ⟨U, hU, hUM⟩ := hreg t ht
    have hgt : IntervalIntegrable (fun s => u s t) volume (x 0) (x (Fin.last n)) :=
      ((huc t ht).mono (uIcc_of_le hab.le).le).intervalIntegrable
    have hgt2 : IntervalIntegrable (fun s => u s t ^ 2) volume (x 0) (x (Fin.last n)) :=
      (((huc t ht).mono (uIcc_of_le hab.le).le).pow 2).intervalIntegrable
    have hEu := hsqrt U M (r + 1) _
      (sum_integral_sq_sub_interp_le_seminorm hx.out hn hnode.toIsNodes hmesh U (huc t ht) hU) hUM
    have htri := sqrt_sum_integral_sub_sq_le hgt hgt2 (uh t : BrokenPolynomial x r) (W t)
    have hWt : ‖W t - (uh t : BrokenPolynomial x r)‖ = E := by
      rw [hE, norm_sub_rev, ← Submodule.norm_coe, Submodule.coe_sub]
      simp only [hWv, hclampeq t ht]
    linarith
  -- the boundary term
  have hbd : ∫ τ in (0 : ℝ)..t, a (x (Fin.last n))
      * (u (x (Fin.last n)) τ - traceLeft (uh τ : BrokenPolynomial x r) (Fin.last n)) ^ 2 = B := by
    refine integral_congr fun τ hτ => ?_
    have hτ' : τ ∈ Icc 0 T := hsub hτ
    simp only [Submodule.coe_sub, hWv, hclampeq τ hτ']
    rw [traceLeft_sub, traceLeft_interp_last hnode hn]
    ring
  -- assemble
  rw [hbd]
  have hs2 : 1 ≤ √2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hΦeq : Φ = h ^ r * (A * M + h * (M' + A₀ * M)) := by rw [hΦ, pow_succ]; ring
  have hpow : h ^ (r + 1) = h ^ r * h := pow_succ h r
  calc √(∑ i, ∫ s in x i.castSucc..x i.succ,
          (u s t - ((uh t : BrokenPolynomial x r) i).eval s) ^ 2) + √B
      ≤ h ^ (r + 1) * M + E + √B := add_le_add hEt le_rfl
    _ ≤ h ^ (r + 1) * M + √2 * √(E ^ 2 + B) := by linarith
    _ ≤ h ^ (r + 1) * M + √2 * (e0 + √(T / μ₀) * Φ) := by gcongr
    _ ≤ h ^ (r + 1) * M + √2 * (√(∑ i, ∫ s in x i.castSucc..x i.succ,
          (u s 0 - ((u₀h : BrokenPolynomial x r) i).eval s) ^ 2) + h ^ (r + 1) * M
          + √(T / μ₀) * Φ) := by gcongr
    _ ≤ √2 * (√(∑ i, ∫ s in x i.castSucc..x i.succ,
          (u s 0 - ((u₀h : BrokenPolynomial x r) i).eval s) ^ 2)
        + h ^ r * (2 * h * M + √(T / μ₀) * (A * M + h * (M' + A₀ * M)))) := by
        rw [hΦeq, hpow]
        have e : √2 * (√(∑ i, ∫ s in x i.castSucc..x i.succ,
            (u s 0 - ((u₀h : BrokenPolynomial x r) i).eval s) ^ 2)
            + h ^ r * (2 * h * M + √(T / μ₀) * (A * M + h * (M' + A₀ * M))))
            = √2 * (√(∑ i, ∫ s in x i.castSucc..x i.succ,
            (u s 0 - ((u₀h : BrokenPolynomial x r) i).eval s) ^ 2)
            + 2 * (h ^ r * h * M) + √(T / μ₀) * (h ^ r * (A * M + h * (M' + A₀ * M)))) := by
          ring
        rw [e]
        exact add_mul_le_mul_add hs2 (mul_nonneg (mul_nonneg (pow_nonneg hh r) hh) hM)

end TimeDependent

/-! ### The $L^2$ projection of a time-dependent function commutes with $\partial_t$ -/

/-- Let $g$ be continuous on the strip $[x_0, x_n] \times [0, T]$, let $I_i$ be a panel and let $q$
be a polynomial. Then $t \mapsto \int_{x_i}^{x_{i+1}} g(y, t)\, q(y) \, dy$ is continuous on
$[0, T]$.

The proof is by dominated convergence. -/
theorem continuousOn_integral_panel_mul {g : ℝ → ℝ → ℝ} {T : ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Icc (x 0) (x (Fin.last n)) ×ˢ Icc 0 T))
    (i : Fin n) (q : ℝ[X]) :
    ContinuousOn (fun t => ∫ y in x i.castSucc..x i.succ, g y t * q.eval y) (Icc 0 T) := by
  have hm : Monotone x := hx.out.monotone
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hg
  intro t₀ ht₀
  have hle : x i.castSucc ≤ x i.succ := hm (Fin.castSucc_lt_succ (i := i)).le
  have hmemI : ∀ y ∈ Ι (x i.castSucc) (x i.succ), y ∈ Icc (x 0) (x (Fin.last n)) := fun y hy =>
    Icc_panel_subset hm i (by rw [uIoc_of_le hle] at hy; exact Ioc_subset_Icc_self hy)
  refine intervalIntegral.continuousWithinAt_of_dominated_interval
    (bound := fun y => B * |q.eval y|) ?_ ?_ ?_ ?_
  · refine Filter.eventually_of_mem self_mem_nhdsWithin fun t ht => ?_
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    refine ContinuousOn.mul ?_ q.continuous.continuousOn
    intro y hy
    have := hg (y, t) ⟨hmemI y hy, ht⟩
    exact ContinuousWithinAt.comp (f := fun z : ℝ => (z, t)) this
      (continuousWithinAt_id.prodMk continuousWithinAt_const)
      fun z hz => Set.mk_mem_prod (hmemI z hz) ht
  · refine Filter.eventually_of_mem self_mem_nhdsWithin fun t ht => ?_
    refine Filter.Eventually.of_forall fun y hy => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (by simpa using hB (y, t) ⟨hmemI y hy, ht⟩) (abs_nonneg _)
  · exact (q.continuous.abs.intervalIntegrable _ _).const_mul B
  · refine Filter.Eventually.of_forall fun y hy => ?_
    have := hg (y, t₀) ⟨hmemI y hy, ht₀⟩
    exact (ContinuousWithinAt.comp (f := fun z : ℝ => (y, z)) this
      (continuousWithinAt_const.prodMk continuousWithinAt_id)
      fun z hz => Set.mk_mem_prod (hmemI y hy) hz).mul continuousWithinAt_const

/-- Let $g$ be continuous on the strip $[x_0, x_n] \times [0, T]$. For every $v \in B_h$, the
pairing $t \mapsto (g(\cdot, t), v)$ is continuous on $[0, T]$. -/
theorem continuousOn_pairing {g : ℝ → ℝ → ℝ} {T : ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Icc (x 0) (x (Fin.last n)) ×ˢ Icc 0 T))
    (v : BrokenPolynomial x r) :
    ContinuousOn (fun t => pairing (fun y => g y t) v) (Icc 0 T) := by
  simp only [pairing_def]
  exact continuousOn_finsetSum _ fun i _ => continuousOn_integral_panel_mul hg i (v i)

/-- Let $n \ge 1$ and let $g$ be continuous on the strip $[x_0, x_n] \times [0, T]$. Then
$t \mapsto P_h g(\cdot, t)$ is continuous on $[0, T]$.

The projection $P_h$ is `BrokenPolynomial.proj`. It is the sum of the pairings with an
orthonormal basis, so the result follows from `Variational.continuousOn_pairing`. -/
theorem continuousOn_proj (hn : 0 < n) {g : ℝ → ℝ → ℝ} {T : ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Icc (x 0) (x (Fin.last n)) ×ˢ Icc 0 T)) :
    ContinuousOn (fun t => proj x r fun y => g y t) (Icc 0 T) := by
  have hab : x 0 < x (Fin.last n) := hx.out (Fin.pos_iff_ne_zero.2 (Fin.ne_of_val_ne hn.ne'))
  set b := stdOrthonormalBasis ℝ (BrokenPolynomial x r) with hb
  have hexp : ∀ t ∈ Icc 0 T, (proj x r fun y => g y t)
      = ∑ k, pairing (fun y => g y t) (b k) • b k := by
    intro t ht
    have hgt : IntervalIntegrable (fun y => g y t) volume (x 0) (x (Fin.last n)) := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hab.le]
      intro y hy
      have := hg (y, t) ⟨hy, ht⟩
      exact ContinuousWithinAt.comp (f := fun z : ℝ => (z, t)) this
        (continuousWithinAt_id.prodMk continuousWithinAt_const) fun z hz => Set.mk_mem_prod hz ht
    conv_lhs => rw [← b.sum_repr (proj x r fun y => g y t)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [OrthonormalBasis.repr_apply_apply, real_inner_comm, inner_proj hgt]
  refine ContinuousOn.congr ?_ hexp
  exact continuousOn_finsetSum _ fun k _ => (continuousOn_pairing hg (b k)).smul continuousOn_const

/-- The **fundamental theorem of calculus for the pairing**. Let $u(\cdot, t)$ be continuous on
$[x_0, x_n]$ for every $t \in [0, T]$, let $t \mapsto u(y, t)$ have the derivative $u_t(y, t)$
within $[0, T]$ at every point of the strip $[x_0, x_n] \times [0, T]$, and let $u_t$ be
continuous on the strip. Then for $\tau \in [0, T]$ and every $v \in B_h$
$$(u(\cdot, \tau), v) - (u(\cdot, 0), v) = \int_0^\tau (u_t(\cdot, s), v) \, ds.$$

The proof applies the fundamental theorem of calculus in $t$ for each $y$, and then Fubini's
theorem on each panel. -/
theorem pairing_sub_eq_integral {u ut : ℝ → ℝ → ℝ} {T : ℝ}
    (huc : ∀ t ∈ Icc 0 T, ContinuousOn (fun y => u y t) (Icc (x 0) (x (Fin.last n))))
    (hut : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun t => u y t) (ut y t) (Icc 0 T) t)
    (hutc : ContinuousOn (fun p : ℝ × ℝ => ut p.1 p.2) (Icc (x 0) (x (Fin.last n)) ×ˢ Icc 0 T))
    {τ : ℝ} (hτ : τ ∈ Icc 0 T) (v : BrokenPolynomial x r) :
    pairing (fun y => u y τ) v - pairing (fun y => u y 0) v
      = ∫ s in (0 : ℝ)..τ, pairing (fun y => ut y s) v := by
  have hm : Monotone x := hx.out.monotone
  have hT0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hτ.1.trans hτ.2⟩
  -- the fundamental theorem of calculus in time, for each `y`
  have hftc : ∀ y ∈ Icc (x 0) (x (Fin.last n)),
      u y τ - u y 0 = ∫ s in (0 : ℝ)..τ, ut y s := by
    intro y hy
    have hcont : ContinuousOn (fun t => u y t) (Icc 0 τ) := fun t ht =>
      (hut y hy t (Icc_subset_Icc le_rfl hτ.2 ht)).continuousWithinAt.mono
        (Icc_subset_Icc le_rfl hτ.2)
    have hderiv : ∀ s ∈ Ioo 0 τ, HasDerivWithinAt (fun t => u y t) (ut y s) (Ioi s) s := fun s hs =>
      (hut y hy s ⟨hs.1.le, hs.2.le.trans hτ.2⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGT_of_mem ⟨hs.1.le, hs.2.trans_le hτ.2⟩)
    have hint : IntervalIntegrable (fun s => ut y s) volume 0 τ := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hτ.1]
      intro s hs
      have := hutc (y, s) ⟨hy, Icc_subset_Icc le_rfl hτ.2 hs⟩
      exact ContinuousWithinAt.comp (f := fun z : ℝ => (y, z)) this
        (continuousWithinAt_const.prodMk continuousWithinAt_id)
        fun z hz => Set.mk_mem_prod hy (Icc_subset_Icc le_rfl hτ.2 hz)
    exact (integral_eq_sub_of_hasDeriv_right_of_le hτ.1 hcont hderiv hint).symm
  -- Fubini on each panel
  have hswap : ∀ i : Fin n, ∫ y in x i.castSucc..x i.succ,
      (∫ s in (0 : ℝ)..τ, ut y s) * (v i).eval y
      = ∫ s in (0 : ℝ)..τ, ∫ y in x i.castSucc..x i.succ, ut y s * (v i).eval y := by
    intro i
    have hle : x i.castSucc ≤ x i.succ := hm (Fin.castSucc_lt_succ (i := i)).le
    have hIcc : Ι (x i.castSucc) (x i.succ) ⊆ Icc (x 0) (x (Fin.last n)) := fun y hy =>
      Icc_panel_subset hm i (by rw [uIoc_of_le hle] at hy; exact Ioc_subset_Icc_self hy)
    have hcont : ContinuousOn (fun p : ℝ × ℝ => ut p.1 p.2 * (v i).eval p.1)
        (Icc (x 0) (x (Fin.last n)) ×ˢ Icc 0 T) :=
      hutc.mul ((v i).continuous.comp continuous_fst).continuousOn
    have hint : Integrable (Function.uncurry fun y s => ut y s * (v i).eval y)
        ((volume.restrict (Ι (x i.castSucc) (x i.succ))).prod (volume.restrict (Ioc 0 τ))) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      refine (hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set ?_
      exact prod_mono hIcc (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl hτ.2))
    have e1 : ∫ y in x i.castSucc..x i.succ, (∫ s in (0 : ℝ)..τ, ut y s) * (v i).eval y
        = ∫ y in x i.castSucc..x i.succ, ∫ s in Ioc 0 τ, ut y s * (v i).eval y := by
      refine integral_congr fun y _ => ?_
      rw [integral_of_le hτ.1, ← MeasureTheory.integral_mul_const]
    rw [e1, intervalIntegral_integral_swap hint, integral_of_le hτ.1]
  -- the panel integrals of `ut(·, s)` are integrable in `s`
  have hpint : ∀ i ∈ (Finset.univ : Finset (Fin n)), IntervalIntegrable
      (fun s => ∫ y in x i.castSucc..x i.succ, ut y s * (v i).eval y) volume 0 τ := by
    intro i _
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hτ.1]
    exact (continuousOn_integral_panel_mul hutc i (v i)).mono (Icc_subset_Icc le_rfl hτ.2)
  simp only [pairing_def]
  rw [← Finset.sum_sub_distrib, intervalIntegral.integral_finsetSum hpint]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hIcc : [[x i.castSucc, x i.succ]] ⊆ Icc (x 0) (x (Fin.last n)) :=
    (BrokenPolynomial.uIcc_panel_subset hm i).trans (uIcc_of_le (hm (Fin.zero_le _))).le
  rw [← hswap i, ← integral_sub (((huc τ hτ).mono hIcc).intervalIntegrable.mul_continuousOn
    (v i).continuous.continuousOn) (((huc 0 hT0).mono hIcc).intervalIntegrable.mul_continuousOn
    (v i).continuous.continuousOn)]
  refine integral_congr fun y hy => ?_
  rw [← hftc y (hIcc hy)]
  ring

/-- The $L^2$ projection of a time-dependent function is the integral of the projection of its time
derivative. Let $n \ge 1$, let $u(\cdot, t)$ be continuous on $[x_0, x_n]$ for every
$t \in [0, T]$, let $t \mapsto u(y, t)$ have the derivative $u_t(y, t)$ within $[0, T]$ at every
point of the strip $[x_0, x_n] \times [0, T]$, and let $u_t$ be continuous on the strip. Then
for $\tau \in [0, T]$
$$P_h u(\cdot, \tau) = P_h u(\cdot, 0) + \int_0^\tau P_h u_t(\cdot, s) \, ds.$$

The integral is the Bochner integral in $B_h$. The proof tests the identity against every
$v \in B_h$ with `Variational.pairing_sub_eq_integral`. -/
theorem proj_eq_add_integral (hn : 0 < n) {u ut : ℝ → ℝ → ℝ} {T : ℝ}
    (huc : ∀ t ∈ Icc 0 T, ContinuousOn (fun y => u y t) (Icc (x 0) (x (Fin.last n))))
    (hut : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun t => u y t) (ut y t) (Icc 0 T) t)
    (hutc : ContinuousOn (fun p : ℝ × ℝ => ut p.1 p.2) (Icc (x 0) (x (Fin.last n)) ×ˢ Icc 0 T))
    {τ : ℝ} (hτ : τ ∈ Icc 0 T) :
    (proj x r fun y => u y τ)
      = (proj x r fun y => u y 0) + ∫ s in (0 : ℝ)..τ, proj x r fun y => ut y s := by
  have hab : x 0 < x (Fin.last n) := hx.out (Fin.pos_iff_ne_zero.2 (Fin.ne_of_val_ne hn.ne'))
  have hT0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hτ.1.trans hτ.2⟩
  have hPc : ContinuousOn (fun s => proj x r fun y => ut y s) (Icc 0 T) := continuousOn_proj hn hutc
  have hPint : IntervalIntegrable (fun s => proj x r fun y => ut y s) volume 0 τ := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hτ.1]
    exact hPc.mono (Icc_subset_Icc le_rfl hτ.2)
  have hui : ∀ t ∈ Icc 0 T, IntervalIntegrable (fun y => u y t) volume (x 0) (x (Fin.last n)) :=
    fun t ht => ((huc t ht).mono (uIcc_of_le hab.le).le).intervalIntegrable
  have huti : ∀ s ∈ Icc 0 T,
      IntervalIntegrable (fun y => ut y s) volume (x 0) (x (Fin.last n)) := by
    intro s hs
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hab.le]
    intro y hy
    have := hutc (y, s) ⟨hy, hs⟩
    exact ContinuousWithinAt.comp (f := fun z : ℝ => (z, s)) this
      (continuousWithinAt_id.prodMk continuousWithinAt_const) fun z hz => Set.mk_mem_prod hz hs
  rw [← sub_eq_iff_eq_add']
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_sub_left, inner_proj (hui τ hτ), inner_proj (hui 0 hT0),
    pairing_sub_eq_integral huc hut hutc hτ v, real_inner_comm, ← innerSL_apply_apply,
    ← (innerSL ℝ v).intervalIntegral_comp_comm hPint]
  refine integral_congr fun s hs => ?_
  rw [uIcc_of_le hτ.1] at hs
  simp only [innerSL_apply_apply]
  rw [real_inner_comm, inner_proj (huti s (Icc_subset_Icc le_rfl hτ.2 hs))]

/-- The **$L^2$ projection commutes with the time derivative**. Let $n \ge 1$, let $u(\cdot, t)$ be
continuous on $[x_0, x_n]$ for every $t \in [0, T]$, let $t \mapsto u(y, t)$ have the derivative
$u_t(y, t)$ within $[0, T]$ at every point of the strip $[x_0, x_n] \times [0, T]$, and let
$u_t$ be continuous on the strip. Then for $t \in [0, T]$, the function
$t \mapsto P_h u(\cdot, t)$ has the derivative $P_h u_t(\cdot, t)$ within $[0, T]$ at $t$.

The proof applies the fundamental theorem of calculus to the identity of
`Variational.proj_eq_add_integral`, whose integrand is continuous by
`Variational.continuousOn_proj`. -/
theorem hasDerivWithinAt_proj (hn : 0 < n) {u ut : ℝ → ℝ → ℝ} {T : ℝ}
    (huc : ∀ t ∈ Icc 0 T, ContinuousOn (fun y => u y t) (Icc (x 0) (x (Fin.last n))))
    (hut : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun t => u y t) (ut y t) (Icc 0 T) t)
    (hutc : ContinuousOn (fun p : ℝ × ℝ => ut p.1 p.2) (Icc (x 0) (x (Fin.last n)) ×ˢ Icc 0 T))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun t => proj x r fun y => u y t) (proj x r fun y => ut y t) (Icc 0 T) t := by
  have hPc : ContinuousOn (fun s => proj x r fun y => ut y s) (Icc 0 T) := continuousOn_proj hn hutc
  have hPint : IntervalIntegrable (fun s => proj x r fun y => ut y s) volume 0 t := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le ht.1]
    exact hPc.mono (Icc_subset_Icc le_rfl ht.2)
  have : Fact (t ∈ Icc 0 T) := ⟨ht⟩
  have h1 : HasDerivWithinAt
      (fun τ => (proj x r fun y => u y 0) + ∫ s in (0 : ℝ)..τ, proj x r fun y => ut y s)
      (proj x r fun y => ut y t) (Icc 0 T) t :=
    (integral_hasDerivWithinAt_right hPint
      (hPc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hPc t ht)).const_add _
  exact h1.congr (fun τ hτ => proj_eq_add_integral hn huc hut hutc hτ)
    (proj_eq_add_integral hn huc hut hutc ht)

/-! ### The discontinuous Galerkin method -/

section DGFixedTime

variable {a₀ : ℝ → ℝ}

/-! ### The consistency error of the upwind discontinuous Galerkin form -/

/-- If $t^-_0 = 0$, then $\sum_{i < n} c_{i+1} e_{i+1} t^-_{i+1} - \sum_{i < n} c_i e_i t^+_i + c_0
e_0 t^+_0 = c_n e_n t^-_n - \sum_{0 < i < n} c_i e_i (t^+_i - t^-_i)$, which is the reindexing
of the boundary terms of the discontinuous Galerkin consistency error. -/
private theorem boundary_sum_eq (hn : 0 < n) {c e tl : Fin (n + 1) → ℝ} {tr : Fin n → ℝ}
    (htl : tl 0 = 0) :
    ∑ i : Fin n, c i.succ * e i.succ * tl i.succ - ∑ i : Fin n, c i.castSucc * e i.castSucc * tr i
      + c 0 * e 0 * tr ⟨0, hn⟩
      = c (Fin.last n) * e (Fin.last n) * tl (Fin.last n)
        - ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
          c i.castSucc * e i.castSucc * (tr i - tl i.castSucc) := by
  have h1 := Fin.sum_univ_succ fun j : Fin (n + 1) => c j * e j * tl j
  have h2 := Fin.sum_univ_castSucc fun j : Fin (n + 1) => c j * e j * tl j
  rw [htl, mul_zero, zero_add] at h1
  have h3 : ∑ i : Fin n, c i.castSucc * e i.castSucc * (tr i - tl i.castSucc)
      = c 0 * e 0 * (tr ⟨0, hn⟩ - tl 0)
        + ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
          c i.castSucc * e i.castSucc * (tr i - tl i.castSucc) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨0, hn⟩ : Fin n))]
    rfl
  rw [htl, sub_zero] at h3
  have h4 : ∑ i : Fin n, c i.castSucc * e i.castSucc * (tr i - tl i.castSucc)
      = ∑ i : Fin n, c i.castSucc * e i.castSucc * tr i
        - ∑ i : Fin n, c i.castSucc * e i.castSucc * tl i.castSucc := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  linarith

/-- For values $f_i$ at the nodes, $f_n + \sum_{0 < i < n} f_i = \sum_{i < n} f_{i+1}$. -/
private theorem node_sum_eq (hn : 0 < n) (f : Fin (n + 1) → ℝ) :
    f (Fin.last n) + ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), f i.castSucc
      = ∑ i : Fin n, f i.succ := by
  have h1 := Fin.sum_univ_succ f
  have h2 := Fin.sum_univ_castSucc f
  have h3 : ∑ i : Fin n, f i.castSucc
      = f 0 + ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), f i.castSucc := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨0, hn⟩ : Fin n))]
    rfl
  linarith

/-- For $c \ge 0$, $c e t \le c t^2 / 4 + c e^2$. -/
private theorem mul_mul_le_quarter {c e t : ℝ} (hc : 0 ≤ c) :
    c * e * t ≤ c * t ^ 2 / 4 + c * e ^ 2 := by
  nlinarith [mul_nonneg hc (sq_nonneg (t / 2 - e))]

/-- The **consistency error of the upwind discontinuous Galerkin form** at a fixed time. Let
$x_0 < \dots < x_n$ be a partition with $n \ge 1$ and panel lengths in $[h_{\min}, h]$, where
$h_{\min} > 0$. Let $a$ and $a_0$ be integrable on $[x_0, x_n]$, let $a$ be differentiable at
every point of $[x_0, x_n]$ with $a'$ continuous there, and let $a \ge 0$, $|a'| \le A'$ and
$|a_0| \le A_0$ on $[x_0, x_n]$ for constants $A', A_0 \ge 0$. Let $u$ be continuous on
$[x_0, x_n]$ with the derivative $u_x(y)$ at every $y \in (x_0, x_n)$, let $u_t$ be continuous
on $[x_0, x_n]$, and let $u_t + a u_x + a_0 u = f$ on $[x_0, x_n]$ with $u(x_0) = \varphi$. Let
$g$ be integrable on $[x_0, x_n]$ with $u_x = g$ almost everywhere on $(x_0, x_n)$, and let
$\|u - P_h u\| \le E_u$. Then for every $v \in B_h$
$$(f, v) + a(x_0) \varphi v^+(x_0) - \langle P_h u_t, v\rangle - b^{DG}(P_h u, v)
  \le \Bigl(A_0 + A' + A' h \frac{2r(r+1)}{h_{\min}}\Bigr) E_u \|v\| +
  \frac{1}{4} a(x_n) v^-(x_n)^2 + \frac{1}{4} \sum_{0 < i < n} a(x_i) [v]_i^2 +
  \sum_{i < n} a(x_{i+1}) \bigl(u(x_{i+1}) - (P_h u)_i(x_{i+1})\bigr)^2.$$

The bound is one-sided. The form $b^{DG}$ is `Variational.dgUpwindForm`, and $P_h$ is
`BrokenPolynomial.proj`. Integration by parts on each panel moves the derivative from
$u - P_h u$ onto $a v$. The orthogonality of the projection error to $a(x_i) v_i'$ leaves
$(a - a(x_i)) v_i'$, which is bounded through the Lipschitz constant of $a$ and the Markov
inequality for $v$. The boundary terms telescope into the traces of the projection error at the
nodes, and the jump and outflow terms with the weights $\tfrac{1}{4}$ absorb them. -/
theorem dg_defect_le (hn : 0 < n) (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : IntervalIntegrable a₀ volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n))))
    (hapos : ∀ s ∈ Icc (x 0) (x (Fin.last n)), 0 ≤ a s) {A' A₀ : ℝ} (hA'0 : 0 ≤ A')
    (hA' : ∀ s ∈ Icc (x 0) (x (Fin.last n)), |deriv a s| ≤ A') (hA₀0 : 0 ≤ A₀)
    (hA₀ : ∀ s ∈ Icc (x 0) (x (Fin.last n)), |a₀ s| ≤ A₀) {h hmin : ℝ}
    (hmesh : ∀ i : Fin n, x i.succ - x i.castSucc ≤ h) (h0 : 0 < hmin)
    (hminle : ∀ i : Fin n, hmin ≤ x i.succ - x i.castSucc) {u ux ut f : ℝ → ℝ} {φ : ℝ}
    (huc : ContinuousOn u (Icc (x 0) (x (Fin.last n))))
    (hux : ∀ y ∈ Ioo (x 0) (x (Fin.last n)), HasDerivAt u (ux y) y)
    (hutc : ContinuousOn ut (Icc (x 0) (x (Fin.last n))))
    (hpde : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ut y + a y * ux y + a₀ y * u y = f y)
    (hφ : u (x 0) = φ) {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (x 0) (x (Fin.last n)))
    (hux_ae : ux =ᵐ[volume.restrict (Ioo (x 0) (x (Fin.last n)))] g) {Eu : ℝ}
    (hEu : √(∑ i, ∫ s in x i.castSucc..x i.succ, (u s - (proj x r u i).eval s) ^ 2) ≤ Eu)
    (v : BrokenPolynomial x r) :
    (pairing f v + a (x 0) * φ * traceRight v ⟨0, hn⟩)
        - (⟪proj x r ut, v⟫ + dgUpwindForm x r ha ha₀ (proj x r u) v)
      ≤ (A₀ + A' + A' * h * (2 * r * (r + 1) / hmin)) * Eu * ‖v‖
        + a (x (Fin.last n)) * traceLeft v (Fin.last n) ^ 2 / 4
        + (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * jump v i ^ 2 / 4)
        + ∑ i : Fin n, a (x i.succ) * (u (x i.succ) - (proj x r u i).eval (x i.succ)) ^ 2 := by
  have hm : Monotone x := hx.out.monotone
  have hab : x 0 < x (Fin.last n) := hx.out (Fin.pos_iff_ne_zero.2 (Fin.ne_of_val_ne hn.ne'))
  have hlt : ∀ i : Fin n, x i.castSucc < x i.succ := fun i => hx.out (Fin.castSucc_lt_succ (i := i))
  have hle : ∀ i : Fin n, x i.castSucc ≤ x i.succ := fun i => (hlt i).le
  have hIcc : ∀ i : Fin n, [[x i.castSucc, x i.succ]] ⊆ Icc (x 0) (x (Fin.last n)) := fun i =>
    (BrokenPolynomial.uIcc_panel_subset hm i).trans (uIcc_of_le hab.le).le
  have hIoo : ∀ i : Fin n, Ioo (x i.castSucc) (x i.succ) ⊆ Ioo (x 0) (x (Fin.last n)) := fun i =>
    Ioo_subset_Ioo (hm (Fin.zero_le _)) (hm (Fin.le_last _))
  have hac : ContinuousOn a (Icc (x 0) (x (Fin.last n))) := fun s hs =>
    (hd s hs).continuousAt.continuousWithinAt
  have hh : 0 ≤ h := (sub_nonneg.2 (hle ⟨0, hn⟩)).trans (hmesh ⟨0, hn⟩)
  -- `ux` is square integrable on every panel
  have hae : ∀ i : Fin n, ux =ᵐ[volume.restrict (Ι (x i.castSucc) (x i.succ))] g := fun i => by
    rw [uIoc_of_le (hle i), Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
    have hb : ∀ᵐ s : ℝ, s ≠ x i.succ := by simp [ae_iff, measure_singleton]
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 hux_ae, hb] with s hs hsb hsI
    exact hs ⟨(hm (Fin.zero_le _)).trans_lt hsI.1, lt_of_le_of_ne (hsI.2.trans (hm (Fin.le_last _)))
      (fun h => hsb (le_antisymm hsI.2 (h ▸ hm (Fin.le_last _)) |>.symm ▸ rfl))⟩
  have hux_i : ∀ i : Fin n, IntervalIntegrable ux volume (x i.castSucc) (x i.succ) := fun i =>
    (intervalIntegrable_panel hm hg i).congr_ae (hae i).symm
  -- the Lipschitz bound of `a`
  have hLip : ∀ s ∈ Icc (x 0) (x (Fin.last n)), ∀ s' ∈ Icc (x 0) (x (Fin.last n)),
      |a s - a s'| ≤ A' * |s - s'| := fun s hs s' hs' => by
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := a) (f' := deriv a) (C := A') (s := Icc (x 0) (x (Fin.last n)))
      (fun y hy => (hd y hy).hasDerivAt.hasDerivWithinAt)
      (fun y hy => by simpa [Real.norm_eq_abs] using hA' y hy) (convex_Icc _ _) hs' hs
    simpa [Real.norm_eq_abs] using this
  set W := proj x r u with hW
  set W' := proj x r ut with hW'
  set η : Fin n → ℝ → ℝ := fun i s => u s - (W i).eval s with hη
  have hηc : ∀ i, ContinuousOn (η i) [[x i.castSucc, x i.succ]] := fun i =>
    (huc.mono (hIcc i)).sub (W i).continuous.continuousOn
  have hηi : ∀ i, IntervalIntegrable (η i) volume (x i.castSucc) (x i.succ) := fun i =>
    (hηc i).intervalIntegrable
  have hηi2 : ∀ i, IntervalIntegrable (fun s => η i s ^ 2) volume (x i.castSucc) (x i.succ) :=
    fun i => ((hηc i).pow 2).intervalIntegrable
  have hvc : ∀ i : Fin n, ContinuousOn (fun s => (v i).eval s) [[x i.castSucc, x i.succ]] :=
    fun i => (v i).continuous.continuousOn
  -- the pairing of the exact source, and `⟪W', v⟫`
  have hui : IntervalIntegrable u volume (x 0) (x (Fin.last n)) :=
    (huc.mono (uIcc_of_le hab.le).le).intervalIntegrable
  have huti : IntervalIntegrable ut volume (x 0) (x (Fin.last n)) :=
    (hutc.mono (uIcc_of_le hab.le).le).intervalIntegrable
  have hW'v : ⟪W', v⟫ = pairing ut v := inner_proj huti v
  -- integration by parts on each panel
  have hibp : ∀ i : Fin n, ∀ (w : ℝ → ℝ) (w' : ℝ → ℝ),
      ContinuousOn w [[x i.castSucc, x i.succ]] →
      (∀ s ∈ Ioo (x i.castSucc) (x i.succ), HasDerivAt w (w' s) s) →
      IntervalIntegrable w' volume (x i.castSucc) (x i.succ) →
      ∫ s in x i.castSucc..x i.succ, a s * w' s * (v i).eval s
        = a (x i.succ) * (v i).eval (x i.succ) * w (x i.succ)
          - a (x i.castSucc) * (v i).eval (x i.castSucc) * w (x i.castSucc)
          - ∫ s in x i.castSucc..x i.succ,
              (deriv a s * (v i).eval s + a s * (derivative (v i)).eval s) * w s := by
    intro i w w' hw hw' hw'i
    have hU : ContinuousOn (fun s => a s * (v i).eval s) [[x i.castSucc, x i.succ]] :=
      (hac.mono (hIcc i)).mul (hvc i)
    have hUd : ∀ s ∈ Ioo (min (x i.castSucc) (x i.succ)) (max (x i.castSucc) (x i.succ)),
        HasDerivAt (fun s => a s * (v i).eval s)
          (deriv a s * (v i).eval s + a s * (derivative (v i)).eval s) s := by
      intro s hs
      rw [min_eq_left (hle i), max_eq_right (hle i)] at hs
      exact (hd s (hIcc i (Ioo_subset_Icc_self.trans (uIcc_of_le (hle i)).symm.subset hs)))
        |>.hasDerivAt.mul ((v i).hasDerivAt s)
    have hwd : ∀ s ∈ Ioo (min (x i.castSucc) (x i.succ)) (max (x i.castSucc) (x i.succ)),
        HasDerivAt w (w' s) s := by
      intro s hs
      rw [min_eq_left (hle i), max_eq_right (hle i)] at hs
      exact hw' s hs
    have hU' : IntervalIntegrable
        (fun s => deriv a s * (v i).eval s + a s * (derivative (v i)).eval s)
        volume (x i.castSucc) (x i.succ) :=
      ((hd'.mono (hIcc i)).intervalIntegrable.mul_continuousOn (hvc i)).add
        ((intervalIntegrable_panel hm ha i).mul_continuousOn
          (derivative (v i)).continuous.continuousOn)
    have key := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hU hw hUd hwd hU' hw'i
    rw [← key]
    exact integral_congr fun s _ => by ring
  -- the traces of the projection error at the nodes
  set ηm : Fin (n + 1) → ℝ := fun j => u (x j) - traceLeft W j with hηm
  have hηm0 : ηm 0 = φ := by simp only [hηm, traceLeft_zero, sub_zero, hφ]
  have hηms : ∀ i : Fin n, ηm i.succ = η i (x i.succ) := fun i => by
    simp only [hηm, hη, traceLeft_succ]
  -- the per-panel decomposition of the defect
  have hpanel : ∀ i : Fin n,
      (∫ s in x i.castSucc..x i.succ, f s * (v i).eval s)
        - (∫ s in x i.castSucc..x i.succ, ut s * (v i).eval s)
        - (∫ s in x i.castSucc..x i.succ,
            (a s * (derivative (W i)).eval s + a₀ s * (W i).eval s) * (v i).eval s)
        - a (x i.castSucc) * jump W i * traceRight v i
      = ((∫ s in x i.castSucc..x i.succ, a₀ s * η i s * (v i).eval s)
          - ∫ s in x i.castSucc..x i.succ, deriv a s * η i s * (v i).eval s)
        - (∫ s in x i.castSucc..x i.succ, a s * η i s * (derivative (v i)).eval s)
        + (a (x i.succ) * ηm i.succ * traceLeft v i.succ
          - a (x i.castSucc) * ηm i.castSucc * traceRight v i) := by
    intro i
    have I1 : IntervalIntegrable (fun s => ut s * (v i).eval s) volume (x i.castSucc) (x i.succ) :=
      (hutc.mono (hIcc i)).intervalIntegrable.mul_continuousOn (hvc i)
    have I2 : IntervalIntegrable (fun s => a s * ux s * (v i).eval s) volume
        (x i.castSucc) (x i.succ) :=
      ((hux_i i).continuousOn_mul (hac.mono (hIcc i))).mul_continuousOn (hvc i)
    have I3 : IntervalIntegrable (fun s => a₀ s * u s * (v i).eval s) volume
        (x i.castSucc) (x i.succ) :=
      ((intervalIntegrable_panel hm ha₀ i).mul_continuousOn (huc.mono (hIcc i))).mul_continuousOn
        (hvc i)
    have I5 : IntervalIntegrable (fun s => a s * (derivative (W i)).eval s * (v i).eval s) volume
        (x i.castSucc) (x i.succ) :=
      ((intervalIntegrable_panel hm ha i).mul_continuousOn
        (derivative (W i)).continuous.continuousOn).mul_continuousOn (hvc i)
    have I6 : IntervalIntegrable (fun s => a₀ s * (W i).eval s * (v i).eval s) volume
        (x i.castSucc) (x i.succ) :=
      ((intervalIntegrable_panel hm ha₀ i).mul_continuousOn
        (W i).continuous.continuousOn).mul_continuousOn (hvc i)
    have IU : IntervalIntegrable
        (fun s => (deriv a s * (v i).eval s + a s * (derivative (v i)).eval s) * u s) volume
        (x i.castSucc) (x i.succ) :=
      (((hd'.mono (hIcc i)).intervalIntegrable.mul_continuousOn (hvc i)).add
        ((intervalIntegrable_panel hm ha i).mul_continuousOn
          (derivative (v i)).continuous.continuousOn)).mul_continuousOn (huc.mono (hIcc i))
    have IW : IntervalIntegrable
        (fun s => (deriv a s * (v i).eval s + a s * (derivative (v i)).eval s) * (W i).eval s)
        volume (x i.castSucc) (x i.succ) :=
      (((hd'.mono (hIcc i)).intervalIntegrable.mul_continuousOn (hvc i)).add
        ((intervalIntegrable_panel hm ha i).mul_continuousOn
          (derivative (v i)).continuous.continuousOn)).mul_continuousOn
        (W i).continuous.continuousOn
    have hf : ∫ s in x i.castSucc..x i.succ, f s * (v i).eval s
        = (∫ s in x i.castSucc..x i.succ, ut s * (v i).eval s)
          + (∫ s in x i.castSucc..x i.succ, a s * ux s * (v i).eval s)
          + ∫ s in x i.castSucc..x i.succ, a₀ s * u s * (v i).eval s := by
      rw [← integral_add I1 I2, ← integral_add (I1.add I2) I3]
      refine integral_congr fun s hs => ?_
      rw [← hpde s (hIcc i hs)]
      ring
    have hu_ibp := hibp i u ux (huc.mono (hIcc i)) (fun s hs => hux s (hIoo i hs)) (hux_i i)
    have hW_ibp := hibp i (fun s => (W i).eval s) (fun s => (derivative (W i)).eval s)
      (W i).continuous.continuousOn (fun s _ => (W i).hasDerivAt s)
      ((derivative (W i)).continuous.intervalIntegrable _ _)
    have e4 : ∫ s in x i.castSucc..x i.succ,
        (a s * (derivative (W i)).eval s + a₀ s * (W i).eval s) * (v i).eval s
        = (∫ s in x i.castSucc..x i.succ, a s * (derivative (W i)).eval s * (v i).eval s)
          + ∫ s in x i.castSucc..x i.succ, a₀ s * (W i).eval s * (v i).eval s := by
      rw [← integral_add I5 I6]
      exact integral_congr fun s _ => by ring
    have e2 : ∫ s in x i.castSucc..x i.succ, a₀ s * η i s * (v i).eval s
        = (∫ s in x i.castSucc..x i.succ, a₀ s * u s * (v i).eval s)
          - ∫ s in x i.castSucc..x i.succ, a₀ s * (W i).eval s * (v i).eval s := by
      rw [← integral_sub I3 I6]
      exact integral_congr fun s _ => by simp only [hη]; ring
    have e3 : (∫ s in x i.castSucc..x i.succ, deriv a s * η i s * (v i).eval s)
        + ∫ s in x i.castSucc..x i.succ, a s * η i s * (derivative (v i)).eval s
        = (∫ s in x i.castSucc..x i.succ,
            (deriv a s * (v i).eval s + a s * (derivative (v i)).eval s) * u s)
          - ∫ s in x i.castSucc..x i.succ,
            (deriv a s * (v i).eval s + a s * (derivative (v i)).eval s) * (W i).eval s := by
      rw [← integral_sub IU IW, ← integral_add
        ((((hd'.mono (hIcc i)).intervalIntegrable.mul_continuousOn (hηc i)).mul_continuousOn
          (hvc i)))
        (((intervalIntegrable_panel hm ha i).mul_continuousOn (hηc i)).mul_continuousOn
          (derivative (v i)).continuous.continuousOn)]
      exact integral_congr fun s _ => by simp only [hη]; ring
    have etr : traceLeft W i.succ = (W i).eval (x i.succ) := traceLeft_succ W i
    have etr' : traceRight W i = (W i).eval (x i.castSucc) := traceRight_apply W i
    have ejump : jump W i = traceRight W i - traceLeft W i.castSucc := jump_apply W i
    have etl : traceLeft v i.succ = (v i).eval (x i.succ) := traceLeft_succ v i
    have etr'' : traceRight v i = (v i).eval (x i.castSucc) := traceRight_apply v i
    beta_reduce at hW_ibp
    rw [hf, e4, hu_ibp, hW_ibp, e2, ← sub_eq_zero]
    rw [← sub_eq_zero] at e3
    simp only [hηm, hη, etr, etr', ejump, etl, etr''] at e3 ⊢
    linear_combination e3
  -- the defect as the sum of the panel terms
  have hD : (pairing f v + a (x 0) * φ * traceRight v ⟨0, hn⟩)
        - (⟪W', v⟫ + dgUpwindForm x r ha ha₀ W v)
      = ((∑ i, ∫ s in x i.castSucc..x i.succ, a₀ s * η i s * (v i).eval s)
          - ∑ i, ∫ s in x i.castSucc..x i.succ, deriv a s * η i s * (v i).eval s)
        - (∑ i, ∫ s in x i.castSucc..x i.succ, a s * η i s * (derivative (v i)).eval s)
        + (a (x (Fin.last n)) * ηm (Fin.last n) * traceLeft v (Fin.last n)
          - ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
            a (x i.castSucc) * ηm i.castSucc * jump v i) := by
    have hbd := boundary_sum_eq hn (c := fun j => a (x j)) (e := ηm) (tl := traceLeft v)
      (tr := traceRight v) (traceLeft_zero v)
    simp only [hηm0, ← jump_apply] at hbd
    rw [hW'v, dgUpwindForm_apply, transportForm_apply, pairing_def, pairing_def, ← hbd]
    have := Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hpanel i
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at this
    linear_combination this
  rw [hD]
  -- the three volume terms
  have hS₂ : ∑ i, ∫ s in x i.castSucc..x i.succ, a₀ s * η i s * (v i).eval s
      ≤ A₀ * Eu * ‖v‖ := by
    refine (le_abs_self _).trans ((abs_sum_integral_mul_mul_eval_le ha₀ hA₀0 hA₀ hηi hηi2 v).trans
      ?_)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEu hA₀0) (norm_nonneg _)
  have hS₃ : -∑ i, ∫ s in x i.castSucc..x i.succ, deriv a s * η i s * (v i).eval s
      ≤ A' * Eu * ‖v‖ := by
    refine (neg_le_abs _).trans ((abs_sum_integral_mul_mul_eval_le
      ((hd'.mono (uIcc_of_le hab.le).le).intervalIntegrable) hA'0 hA' hηi hηi2 v).trans ?_)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEu hA'0) (norm_nonneg _)
  have hS₄ : -∑ i, ∫ s in x i.castSucc..x i.succ, a s * η i s * (derivative (v i)).eval s
      ≤ A' * h * (2 * r * (r + 1) / hmin) * Eu * ‖v‖ := by
    -- orthogonality: replace `a` by `a - a(xᵢ)`
    have horth : ∀ i : Fin n,
        -∫ s in x i.castSucc..x i.succ, a s * η i s * (derivative (v i)).eval s
        = ∫ s in x i.castSucc..x i.succ,
          (a (x i.castSucc) - a s) * η i s * (derivative (v i)).eval s := by
      intro i
      have hq : (C (a (x i.castSucc)) * derivative (v i)).natDegree ≤ r :=
        (natDegree_C_mul_le _ _).trans ((natDegree_derivative_le _).trans
          (Nat.sub_le_of_le_add ((natDegree_le v i).trans (Nat.le_succ r))))
      have h0 := integral_sub_proj_mul_eq_zero hui i hq
      have hc : IntervalIntegrable (fun s => a s * η i s * (derivative (v i)).eval s) volume
          (x i.castSucc) (x i.succ) :=
        (((hac.mono (hIcc i)).mul (hηc i)).mul (derivative (v i)).continuous.continuousOn)
          |>.intervalIntegrable
      have hc' : IntervalIntegrable
          (fun s => (u s - (proj x r u i).eval s)
            * (C (a (x i.castSucc)) * derivative (v i)).eval s)
          volume (x i.castSucc) (x i.succ) :=
        ((hηc i).mul (C (a (x i.castSucc)) * derivative (v i)).continuous.continuousOn)
          |>.intervalIntegrable
      have e : ∫ s in x i.castSucc..x i.succ,
          (a (x i.castSucc) - a s) * η i s * (derivative (v i)).eval s
          = (∫ s in x i.castSucc..x i.succ,
              (u s - (proj x r u i).eval s) * (C (a (x i.castSucc)) * derivative (v i)).eval s)
            - ∫ s in x i.castSucc..x i.succ, a s * η i s * (derivative (v i)).eval s := by
        rw [← integral_sub hc' hc]
        refine integral_congr fun s _ => ?_
        simp only [hη, eval_mul, eval_C]
        ring
      rw [e, h0, zero_sub]
    have hK : 0 ≤ 2 * r * (r + 1) / hmin := by positivity
    -- the panel bounds
    have hpan : ∀ i : Fin n, ∫ s in x i.castSucc..x i.succ,
        (a (x i.castSucc) - a s) * η i s * (derivative (v i)).eval s
        ≤ (A' * h * √(∫ s in x i.castSucc..x i.succ, η i s ^ 2))
          * (2 * r * (r + 1) / hmin * √(∫ s in x i.castSucc..x i.succ, (v i).eval s ^ 2)) := by
      intro i
      have hcη : ContinuousOn (fun s => (a (x i.castSucc) - a s) * η i s)
          [[x i.castSucc, x i.succ]] :=
        (continuousOn_const.sub (hac.mono (hIcc i))).mul (hηc i)
      have h1 := intervalIntegral.integral_mul_le_sqrt_mul_sqrt (hle i)
        (f := fun s => (a (x i.castSucc) - a s) * η i s) (g := fun s => (derivative (v i)).eval s)
        hcη.intervalIntegrable (hcη.pow 2).intervalIntegrable
        ((derivative (v i)).continuous.intervalIntegrable _ _)
        (((derivative (v i)).continuous.pow 2).intervalIntegrable _ _)
      have h2 : ∫ s in x i.castSucc..x i.succ, ((a (x i.castSucc) - a s) * η i s) ^ 2
          ≤ (A' * h) ^ 2 * ∫ s in x i.castSucc..x i.succ, η i s ^ 2 := by
        rw [← intervalIntegral.integral_const_mul]
        refine integral_mono_on (hle i) (hcη.pow 2).intervalIntegrable ((hηi2 i).const_mul _)
          fun s hs => ?_
        rw [mul_pow]
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        rw [← sq_abs]
        refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
        calc |a (x i.castSucc) - a s| ≤ A' * |x i.castSucc - s| :=
              hLip _ (hIcc i (left_mem_uIcc)) s (hIcc i (uIcc_of_le (hle i) ▸ hs))
          _ ≤ A' * h := by
              refine mul_le_mul_of_nonneg_left ?_ hA'0
              rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hs.1)]
              linarith [hs.2, hmesh i]
      have h3 : ∫ s in x i.castSucc..x i.succ, (derivative (v i)).eval s ^ 2
          ≤ (2 * r * (r + 1) / hmin) ^ 2 * ∫ s in x i.castSucc..x i.succ, (v i).eval s ^ 2 := by
        refine (integral_derivative_sq_le_panel (hlt i) (natDegree_le v i)).trans
          (mul_le_mul_of_nonneg_right ?_ (integral_nonneg (hle i) fun s _ => sq_nonneg _))
        refine pow_le_pow_left₀ (div_nonneg (by positivity) (sub_nonneg.2 (hle i))) ?_ 2
        exact div_le_div_of_nonneg_left (by positivity) h0 (hminle i)
      refine h1.trans (mul_le_mul ?_ ?_ (Real.sqrt_nonneg _)
        (mul_nonneg (mul_nonneg hA'0 hh) (Real.sqrt_nonneg _)))
      · calc √(∫ s in x i.castSucc..x i.succ, ((a (x i.castSucc) - a s) * η i s) ^ 2)
            ≤ √((A' * h) ^ 2 * ∫ s in x i.castSucc..x i.succ, η i s ^ 2) := Real.sqrt_le_sqrt h2
          _ = A' * h * √(∫ s in x i.castSucc..x i.succ, η i s ^ 2) := by
              rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
      · calc √(∫ s in x i.castSucc..x i.succ, (derivative (v i)).eval s ^ 2)
            ≤ √((2 * r * (r + 1) / hmin) ^ 2 * ∫ s in x i.castSucc..x i.succ, (v i).eval s ^ 2) :=
              Real.sqrt_le_sqrt h3
          _ = 2 * r * (r + 1) / hmin * √(∫ s in x i.castSucc..x i.succ, (v i).eval s ^ 2) := by
              rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hK]
    have hnn : ∀ i : Fin n, 0 ≤ ∫ s in x i.castSucc..x i.succ, η i s ^ 2 := fun i =>
      integral_nonneg (hle i) fun _ _ => sq_nonneg _
    have hnn' : ∀ i : Fin n, 0 ≤ ∫ s in x i.castSucc..x i.succ, (v i).eval s ^ 2 := fun i =>
      integral_nonneg (hle i) fun _ _ => sq_nonneg _
    calc -∑ i, ∫ s in x i.castSucc..x i.succ, a s * η i s * (derivative (v i)).eval s
        = ∑ i, ∫ s in x i.castSucc..x i.succ,
            (a (x i.castSucc) - a s) * η i s * (derivative (v i)).eval s := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun i _ => horth i
      _ ≤ ∑ i, (A' * h * √(∫ s in x i.castSucc..x i.succ, η i s ^ 2))
            * (2 * r * (r + 1) / hmin * √(∫ s in x i.castSucc..x i.succ, (v i).eval s ^ 2)) :=
          Finset.sum_le_sum fun i _ => hpan i
      _ = A' * h * (2 * r * (r + 1) / hmin) * ∑ i, √(∫ s in x i.castSucc..x i.succ, η i s ^ 2)
            * √(∫ s in x i.castSucc..x i.succ, (v i).eval s ^ 2) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ A' * h * (2 * r * (r + 1) / hmin)
            * (√(∑ i, √(∫ s in x i.castSucc..x i.succ, η i s ^ 2) ^ 2)
              * √(∑ i, √(∫ s in x i.castSucc..x i.succ, (v i).eval s ^ 2) ^ 2)) :=
          mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) (by positivity)
      _ = A' * h * (2 * r * (r + 1) / hmin)
            * (√(∑ i, ∫ s in x i.castSucc..x i.succ, η i s ^ 2) * ‖v‖) := by
          simp only [Real.sq_sqrt (hnn _), Real.sq_sqrt (hnn' _)]
          rw [← norm_sq_eq, Real.sqrt_sq (norm_nonneg _)]
      _ ≤ A' * h * (2 * r * (r + 1) / hmin) * Eu * ‖v‖ := by
          have := mul_le_mul_of_nonneg_right hEu (norm_nonneg v)
          have hc0 : 0 ≤ A' * h * (2 * r * (r + 1) / hmin) := by positivity
          calc A' * h * (2 * r * (r + 1) / hmin)
                * (√(∑ i, ∫ s in x i.castSucc..x i.succ, η i s ^ 2) * ‖v‖)
              ≤ A' * h * (2 * r * (r + 1) / hmin) * (Eu * ‖v‖) :=
                mul_le_mul_of_nonneg_left this hc0
            _ = A' * h * (2 * r * (r + 1) / hmin) * Eu * ‖v‖ := by ring
  -- the boundary terms
  have hB1 : a (x (Fin.last n)) * ηm (Fin.last n) * traceLeft v (Fin.last n)
      ≤ a (x (Fin.last n)) * traceLeft v (Fin.last n) ^ 2 / 4
        + a (x (Fin.last n)) * ηm (Fin.last n) ^ 2 :=
    mul_mul_le_quarter (hapos _ (right_mem_Icc.2 hab.le))
  have hB2 : -∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
        a (x i.castSucc) * ηm i.castSucc * jump v i
      ≤ ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
        (a (x i.castSucc) * jump v i ^ 2 / 4 + a (x i.castSucc) * ηm i.castSucc ^ 2) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have := mul_mul_le_quarter (c := a (x i.castSucc)) (e := ηm i.castSucc) (t := -jump v i)
      (hapos _ (hIcc i left_mem_uIcc))
    rw [neg_sq] at this
    linarith
  have htr : a (x (Fin.last n)) * ηm (Fin.last n) ^ 2
      + ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * ηm i.castSucc ^ 2
      = ∑ i : Fin n, a (x i.succ) * (u (x i.succ) - (proj x r u i).eval (x i.succ)) ^ 2 := by
    rw [node_sum_eq hn fun j => a (x j) * ηm j ^ 2]
    exact Finset.sum_congr rfl fun i _ => by rw [hηms]
  rw [Finset.sum_add_distrib] at hB2
  have hsum : (A₀ + A' + A' * h * (2 * r * (r + 1) / hmin)) * Eu * ‖v‖
      = A₀ * Eu * ‖v‖ + A' * Eu * ‖v‖ + A' * h * (2 * r * (r + 1) / hmin) * Eu * ‖v‖ := by ring
  rw [hsum]
  linarith

/-- The **traces of the projection error at the nodes**. Let $x_0 < \dots < x_n$ be a partition with
$n \ge 1$, panel lengths in $[h_{\min}, h]$ with $h_{\min} > 0$, and a node system of degree
$r$. Let $|a| \le A$ on $[x_0, x_n]$ with $A \ge 0$, let $U \in H^{r+1}(x_0, x_n)$, and let $u$
be continuous on $[x_0, x_n]$ with $U = u$ almost everywhere on $(x_0, x_n)$. Then for points
$y_i \in I_i$
$$\sum_i a(y_i) \bigl(u(y_i) - (P_h u)_i(y_i)\bigr)^2
  \le 2 A h^{2r+1} |U|_{H^{r+1}}^2 \Bigl(\frac{h}{h_{\min}} +
  \Bigl(1 + 4r(r+1) \frac{h}{h_{\min}}\Bigr)^2\Bigr).$$

The proof applies the trace inequality `BrokenPolynomial.sum_mul_sq_sub_eval_le` to the $L^2$
and $H^1$ errors of the projection. -/
theorem sum_mul_sq_sub_proj_le (hn : 0 < n) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ s ∈ Icc (x 0) (x (Fin.last n)), |a s| ≤ A) {node : Fin n → Fin (r + 1) → ℝ}
    (hnode : IsNodes x r node) {h hmin : ℝ} (hmesh : ∀ i : Fin n, x i.succ - x i.castSucc ≤ h)
    (h0 : 0 < hmin) (hminle : ∀ i : Fin n, hmin ≤ x i.succ - x i.castSucc)
    (U : SobolevInterval (r + 1) (x 0) (x (Fin.last n))) {u : ℝ → ℝ}
    (hu : ContinuousOn u (Icc (x 0) (x (Fin.last n))))
    (hU : SobolevInterval.fn U =ᵐ[volume.restrict (Ioo (x 0) (x (Fin.last n)))] u)
    {y : Fin n → ℝ} (hy : ∀ i, y i ∈ Icc (x i.castSucc) (x i.succ)) :
    ∑ i, a (y i) * (u (y i) - (proj x r u i).eval (y i)) ^ 2
      ≤ 2 * A * h ^ (2 * r + 1) * SobolevInterval.seminorm (r + 1) (x 0) (x (Fin.last n)) U ^ 2
        * (h / hmin + (1 + 4 * r * (r + 1) * (h / hmin)) ^ 2) := by
  have hab : x 0 < x (Fin.last n) := hx.out (Fin.pos_iff_ne_zero.2 (Fin.ne_of_val_ne hn.ne'))
  have hm : Monotone x := hx.out.monotone
  have hh : 0 ≤ h :=
    (sub_nonneg.2 (hx.out (Fin.castSucc_lt_succ (i := ⟨0, hn⟩))).le).trans (hmesh ⟨0, hn⟩)
  set S := SobolevInterval.seminorm (r + 1) (x 0) (x (Fin.last n)) U with hS
  set P := proj x r u with hP
  have hg := SobolevInterval.intervalIntegrable_deriv hab.le U 1
  have hg2 := SobolevInterval.intervalIntegrable_deriv_sq hab.le U 1
  have hfg : ∀ s ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc (x 0) (x (Fin.last n)),
      u t - u s = ∫ q in s..t, SobolevInterval.deriv U 1 q := fun s hs t ht =>
    SobolevInterval.sub_eq_integral_deriv_one hab U hu hU hs ht
  have htr := sum_mul_sq_sub_eval_le hu hg hg2 hfg hmesh h0 hminle P hy (c := fun i => a (y i))
    hA0 fun i => (le_abs_self _).trans (hA (y i) (Icc_panel_subset hm i (hy i)))
  have hE1 : ∑ i, ∫ s in x i.castSucc..x i.succ, (u s - (P i).eval s) ^ 2
      ≤ (h ^ (r + 1) * S) ^ 2 := by
    have h1 := sqrt_sum_integral_sq_sub_proj_le_seminorm hn hnode hmesh U hu hU
    have hnn : 0 ≤ ∑ i, ∫ s in x i.castSucc..x i.succ, (u s - (P i).eval s) ^ 2 :=
      Finset.sum_nonneg fun i _ =>
        integral_nonneg (hm (Fin.castSucc_lt_succ (i := i)).le) fun _ _ => sq_nonneg _
    rw [← Real.sq_sqrt hnn]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  have hE2 : ∑ i, ∫ s in x i.castSucc..x i.succ,
      (SobolevInterval.deriv U 1 s - (derivative (P i)).eval s) ^ 2
      ≤ (h ^ r * (1 + 4 * r * (r + 1) * (h / hmin)) * S) ^ 2 := by
    have h1 := sqrt_sum_integral_sq_deriv_sub_proj_le_seminorm hn hnode hmesh h0 hminle U hu hU
    have hnn : 0 ≤ ∑ i, ∫ s in x i.castSucc..x i.succ,
        (SobolevInterval.deriv U 1 s - (derivative (P i)).eval s) ^ 2 :=
      Finset.sum_nonneg fun i _ =>
        integral_nonneg (hm (Fin.castSucc_lt_succ (i := i)).le) fun _ _ => sq_nonneg _
    rw [← Real.sq_sqrt hnn]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  refine htr.trans ?_
  calc A * (2 / hmin * (∑ i, ∫ s in x i.castSucc..x i.succ, (u s - (P i).eval s) ^ 2)
        + 2 * h * ∑ i, ∫ s in x i.castSucc..x i.succ,
          (SobolevInterval.deriv U 1 s - (derivative (P i)).eval s) ^ 2)
      ≤ A * (2 / hmin * (h ^ (r + 1) * S) ^ 2
        + 2 * h * (h ^ r * (1 + 4 * r * (r + 1) * (h / hmin)) * S) ^ 2) := by
        gcongr
    _ = 2 * A * h ^ (2 * r + 1) * S ^ 2 * (h / hmin + (1 + 4 * r * (r + 1) * (h / hmin)) ^ 2) := by
        rw [show h ^ (2 * r + 1) = (h ^ r) ^ 2 * h by rw [pow_succ, pow_mul'],
          show h ^ (r + 1) = h ^ r * h from pow_succ h r]
        field_simp

end DGFixedTime

section DGTimeDependent

variable {a₀ : ℝ → ℝ → ℝ}

/-- The **constant of the discontinuous Galerkin error estimate**. Let $\rho = h / h_{\min}$ be the
mesh ratio, $K = 2r(r+1)\rho$ the Markov constant, $\Phi_0 = (A_0 + A' + A'K) M$ the consistency
constant and $K_{\mathrm{tr}} = 2AM^2 (\rho + (1 + 4r(r+1)\rho)^2)$ the trace constant. The
constant is
$$C_{DG} = 2hM^2 + T(2hM^2 + 10 K_{\mathrm{tr}}) +
  \Bigl(8 + \frac{2}{\mu_0}\Bigr)
    \Bigl(2hM^2 + T \Bigl(\frac{h \Phi_0^2}{\mu_0} + 2 K_{\mathrm{tr}}\Bigr)\Bigr).$$

The bound of `Variational.dG_error_sq_le` is $(16 + 4/\mu_0) \|u_0 - u_{0,h}\|^2 + C_{DG}
h^{2r+1}$. The definition has no hypotheses; at $\mu_0 = 0$ or $h_{\min} = 0$ the divisions by
zero give $0$. -/
def dgConst (r : ℕ) (A A' A₀ μ₀ T M h hmin : ℝ) : ℝ :=
  2 * h * M ^ 2 + T * (2 * h * M ^ 2 + 10 * (2 * A * M ^ 2
      * (h / hmin + (1 + 4 * r * (r + 1) * (h / hmin)) ^ 2)))
    + (8 + 2 / μ₀) * (2 * h * M ^ 2 + T * (h * ((A₀ + A' + A' * h * (2 * r * (r + 1) / hmin)) * M)
        ^ 2 / μ₀ + 2 * (2 * A * M ^ 2 * (h / hmin + (1 + 4 * r * (r + 1) * (h / hmin)) ^ 2))))


/-- For $c \ge 0$, $c(j + (p - q))^2 \le 2cj^2 + 4cp^2 + 4cq^2$. -/
private theorem mul_sq_add_sub_le {c j p q : ℝ} (hc : 0 ≤ c) :
    c * (j + (p - q)) ^ 2 ≤ 2 * (c * j ^ 2) + 4 * (c * p ^ 2) + 4 * (c * q ^ 2) := by
  nlinarith [mul_nonneg hc (sq_nonneg (j - (p - q))), mul_nonneg hc (sq_nonneg (p + q))]

/-- For $c \ge 0$, $c(j - p)^2 \le 2cj^2 + 2cp^2$. -/
private theorem mul_sq_sub_le {c j p : ℝ} (hc : 0 ≤ c) :
    c * (j - p) ^ 2 ≤ 2 * (c * j ^ 2) + 2 * (c * p ^ 2) := by
  nlinarith [mul_nonneg hc (sq_nonneg (j + p))]

/-- For $\mu_0 > 0$ and $N, B, S, J \ge 0$, $(2/\mu_0) N + 4S + 2J \le (2/\mu_0 + 6)(N + B + S +
J)$, which absorbs the error terms into the energy. -/
private theorem energy_parts_le {N B S J μ₀ : ℝ} (hμ : 0 < μ₀) (hN : 0 ≤ N) (hB : 0 ≤ B)
    (hS : 0 ≤ S) (hJ : 0 ≤ J) : 2 / μ₀ * N + 4 * S + 2 * J ≤ (2 / μ₀ + 6) * (N + B + S + J) := by
  have hμ' : 0 ≤ 2 / μ₀ := by positivity
  nlinarith [mul_nonneg hμ' hB, mul_nonneg hμ' hS, mul_nonneg hμ' hJ]

/-- The final rearrangement in the proof of `Variational.dG_error_sq_le`: if $\mu_0 > 0$, $t \le T$,
$P, Q, G \ge 0$, $e_0 \le 2Y_i + 2P$, $w \le e_0 + tG$, $Y_0 \le 2P + 2(e_0 + tG)$ and
$L \le t(2P + 10Q) + (2/\mu_0 + 6)w$, then $Y_0 + L \le (16 + 4/\mu_0) Y_i + 2P + T(2P + 10Q) +
(8 + 2/\mu_0)(2P + TG)$. -/
private theorem dg_final {Y₀ L Yi P Q G e0 w μ₀ T t : ℝ} (hμ : 0 < μ₀) (htT : t ≤ T)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hG : 0 ≤ G) (he0 : e0 ≤ 2 * Yi + 2 * P)
    (hw : w ≤ e0 + t * G) (hY₀ : Y₀ ≤ 2 * P + 2 * (e0 + t * G))
    (hL : L ≤ t * (2 * P + 10 * Q) + (2 / μ₀ + 6) * w) :
    Y₀ + L ≤ (16 + 4 / μ₀) * Yi
      + (2 * P + T * (2 * P + 10 * Q) + (8 + 2 / μ₀) * (2 * P + T * G)) := by
  have h1 : 0 ≤ 2 / μ₀ + 6 := by positivity
  have h2 : t * G ≤ T * G := mul_le_mul_of_nonneg_right htT hG
  have h3 : t * (2 * P + 10 * Q) ≤ T * (2 * P + 10 * Q) :=
    mul_le_mul_of_nonneg_right htT (by positivity)
  have h4 : (2 / μ₀ + 6) * w ≤ (2 / μ₀ + 6) * (e0 + T * G) :=
    mul_le_mul_of_nonneg_left (hw.trans (by linarith)) h1
  have h5 : (2 / μ₀ + 6) * e0 ≤ (2 / μ₀ + 6) * (2 * Yi + 2 * P) := mul_le_mul_of_nonneg_left he0 h1
  have h7 : (16 + 4 / μ₀) * Yi + (2 * P + T * (2 * P + 10 * Q) + (8 + 2 / μ₀) * (2 * P + T * G))
      = 2 * P + 2 * (2 * Yi + 2 * P) + 2 * (T * G) + T * (2 * P + 10 * Q)
        + ((2 / μ₀ + 6) * (2 * Yi + 2 * P) + (2 / μ₀ + 6) * (T * G)) := by ring
  rw [h7]
  linarith

/-- The **error estimate of the discontinuous Galerkin method** for the transport equation, in
squared form. Let $x_0 < \dots < x_n$ be a partition with $n \ge 1$, panel lengths in
$[h_{\min}, h]$ with $h_{\min} > 0$, and a node system of degree $r$, and let $T > 0$. Let $a$
be integrable on $[x_0, x_n]$ and differentiable at every point of $[x_0, x_n]$ with $a'$
continuous there, let $a_0(\cdot, t)$ be integrable on $[x_0, x_n]$ for every $t$, and let there
be constants $\mu_0 > 0$, $A$, $A'$ and $A_0$ with
$$\mu_0 \le a_0(s, t) - \tfrac{1}{2} a'(s), \quad 0 \le a(s), \quad |a(s)| \le A,
  \quad |a'(s)| \le A', \quad |a_0(s, t)| \le A_0$$
for $s \in [x_0, x_n]$ and $t \in [0, T]$. Let $u$ be a classical solution of
$u_t + a u_x + a_0 u = f$ on the strip $[x_0, x_n] \times [0, T]$ with the inflow value
$u(x_0, t) = \varphi(t)$: $u$ and $u_t$ are continuous on the strip, and at every point of the
strip $u(\cdot, t)$ has the derivative $u_x$ within $[x_0, x_n]$ and $u(y, \cdot)$ has the
derivative $u_t$ within $[0, T]$. Let $u$ be regular: for every $t \in [0, T]$ there is
$U \in H^{r+1}(x_0, x_n)$, equal almost everywhere to $u(\cdot, t)$, with $|U|_{H^{r+1}} \le M$.
Let $f_h(t) \in B_h$ satisfy $\langle f_h(t), v\rangle = (f(\cdot, t), v)$ for all $v \in B_h$
and $t \in [0, T]$, so that $f_h(t)$ is the $L^2$ projection of $f(\cdot, t)$, and let
$u_h : \mathbb{R} \to B_h$ solve the upwind semi-discretization
$$\langle u_h'(t), v\rangle + b^{DG}_t(u_h(t), v)
  = \langle f_h(t), v\rangle + a(x_0) \varphi(t) v^+(x_0) \qquad (v \in B_h,\ t \in [0, T])$$
with $u_h(0) = u_{0,h}$. Then for every $t \in [0, T]$
$$\|u(t) - u_h(t)\|^2 + \int_0^t \Bigl(\|u(\tau) - u_h(\tau)\|^2 +
  \sum_{j=1}^{n-1} a(x_j) [u_h(\tau)]_j^2 +
  a(x_0) \bigl(u_h^+(x_0, \tau) - \varphi(\tau)\bigr)^2\Bigr) d\tau
  \le \Bigl(16 + \frac{4}{\mu_0}\Bigr) \|u(0) - u_{0,h}\|^2 + C_{DG}\, h^{2r+1},$$
where $C_{DG}$ is `Variational.dgConst`. This is the square of the estimate
$O(\|u_0 - u_{0,h}\| + h^{r+1/2})$ for discontinuous finite elements of degree $r$ in
[quarteroni2000numerical], §13.10.1, which quotes it from [quarteroni1994numerical], §14.3.3,
without proof; here the constants are explicit.

The jump $[u - u_h]_0$ of the source is $\varphi - u_h^+(x_0)$ here, because $u$ is continuous
and $u(x_0) = \varphi$. The norms are panelwise $L^2$ norms, and $b^{DG}_t$ is
`Variational.dgUpwindForm` with the coefficient $a_0(\cdot, t)$. The proof applies the error
equation `Variational.IsSemidiscreteGalerkin.sub` with the $L^2$ projection
$W(t) = P_h u(\cdot, t)$, which commutes with $\partial_t$ by
`Variational.hasDerivWithinAt_proj`. The dissipation of the upwind form,
`Variational.le_dgUpwindForm`, absorbs the consistency error of `Variational.dg_defect_le`. The
$L^2$ part of the consistency error is $O(h^{r+1})$, and the traces of the projection error at
the nodes are $O(h^{r+1/2})$ by `Variational.sum_mul_sq_sub_proj_le`; the half power comes from
this trace term. -/
theorem dG_error_sq_le (hn : 0 < n) {T : ℝ} (hT : 0 < T)
    (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n))))
    {μ₀ : ℝ} (hμ : 0 < μ₀)
    (hμ₀ : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc (x 0) (x (Fin.last n)), μ₀ ≤ a₀ s t - deriv a s / 2)
    (hapos : ∀ s ∈ Icc (x 0) (x (Fin.last n)), 0 ≤ a s) {A A' A₀ : ℝ}
    (hA : ∀ s ∈ Icc (x 0) (x (Fin.last n)), |a s| ≤ A)
    (hA' : ∀ s ∈ Icc (x 0) (x (Fin.last n)), |deriv a s| ≤ A')
    (hA₀ : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc (x 0) (x (Fin.last n)), |a₀ s t| ≤ A₀)
    {u ux ut f : ℝ → ℝ → ℝ} {φ : ℝ → ℝ}
    (huc2 : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (Icc (x 0) (x (Fin.last n)) ×ˢ Icc 0 T))
    (hux : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun y => u y t) (ux y t) (Icc (x 0) (x (Fin.last n))) y)
    (hut : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun t => u y t) (ut y t) (Icc 0 T) t)
    (hutc2 : ContinuousOn (fun p : ℝ × ℝ => ut p.1 p.2) (Icc (x 0) (x (Fin.last n)) ×ˢ Icc 0 T))
    (hpde : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T,
      ut y t + a y * ux y t + a₀ y t * u y t = f y t)
    (hin : ∀ t ∈ Icc 0 T, u (x 0) t = φ t) {M : ℝ}
    (hreg : ∀ t ∈ Icc 0 T, ∃ U : SobolevInterval (r + 1) (x 0) (x (Fin.last n)),
      SobolevInterval.fn U =ᵐ[volume.restrict (Ioo (x 0) (x (Fin.last n)))] (fun y => u y t) ∧
        SobolevInterval.seminorm (r + 1) (x 0) (x (Fin.last n)) U ≤ M)
    {node : Fin n → Fin (r + 1) → ℝ} (hnode : IsNodes x r node) {h hmin : ℝ}
    (hmesh : ∀ i : Fin n, x i.succ - x i.castSucc ≤ h) (h0 : 0 < hmin)
    (hminle : ∀ i : Fin n, hmin ≤ x i.succ - x i.castSucc)
    {fh : ℝ → BrokenPolynomial x r}
    (hfh : ∀ t ∈ Icc 0 T, ∀ v, ⟪fh t, v⟫ = pairing (fun y => f y t) v)
    {u₀h : BrokenPolynomial x r} {uh : ℝ → BrokenPolynomial x r}
    (huh : IsSemidiscreteGalerkin (fun t => dgUpwindForm x r ha (ha₀ t))
      (fun t => innerSL ℝ (fh t) + (a (x 0) * φ t) • traceRightL x r ⟨0, hn⟩) u₀h T uh)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    (∑ i, ∫ s in x i.castSucc..x i.succ, (u s t - (uh t i).eval s) ^ 2)
      + ∫ τ in (0 : ℝ)..t, ((∑ i, ∫ s in x i.castSucc..x i.succ, (u s τ - (uh τ i).eval s) ^ 2)
          + (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * jump (uh τ) i ^ 2)
          + a (x 0) * (traceRight (uh τ) ⟨0, hn⟩ - φ τ) ^ 2)
    ≤ (16 + 4 / μ₀) * (∑ i, ∫ s in x i.castSucc..x i.succ, (u s 0 - (u₀h i).eval s) ^ 2)
      + dgConst r A A' A₀ μ₀ T M h hmin * h ^ (2 * r + 1) := by
  have hm : Monotone x := hx.out.monotone
  have hab : x 0 < x (Fin.last n) := hx.out (Fin.pos_iff_ne_zero.2 (Fin.ne_of_val_ne hn.ne'))
  have hT0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hh : 0 ≤ h :=
    (sub_nonneg.2 (hx.out (Fin.castSucc_lt_succ (i := ⟨0, hn⟩))).le).trans (hmesh ⟨0, hn⟩)
  obtain ⟨U₀, hU₀, hU₀M⟩ := hreg 0 hT0
  have hM : 0 ≤ M := (apply_nonneg _ _).trans hU₀M
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA (x 0) (left_mem_Icc.2 hab.le))
  have hA'0 : 0 ≤ A' := (abs_nonneg _).trans (hA' (x 0) (left_mem_Icc.2 hab.le))
  have hA₀0 : 0 ≤ A₀ := (abs_nonneg _).trans (hA₀ 0 hT0 (x 0) (left_mem_Icc.2 hab.le))
  have hsub : [[(0 : ℝ), t]] ⊆ Icc 0 T := by
    rw [uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2
  have huc : ∀ t ∈ Icc 0 T, ContinuousOn (fun y => u y t) (Icc (x 0) (x (Fin.last n))) := by
    intro t ht y hy
    have := huc2 (y, t) ⟨hy, ht⟩
    exact ContinuousWithinAt.comp (f := fun z : ℝ => (z, t)) this
      (continuousWithinAt_id.prodMk continuousWithinAt_const) fun z hz => Set.mk_mem_prod hz ht
  have hutc : ∀ t ∈ Icc 0 T, ContinuousOn (fun y => ut y t) (Icc (x 0) (x (Fin.last n))) := by
    intro t ht y hy
    have := hutc2 (y, t) ⟨hy, ht⟩
    exact ContinuousWithinAt.comp (f := fun z : ℝ => (z, t)) this
      (continuousWithinAt_id.prodMk continuousWithinAt_const) fun z hz => Set.mk_mem_prod hz ht
  -- the constants
  set ρ : ℝ := h / hmin with hρ
  set K : ℝ := 2 * r * (r + 1) / hmin with hK
  set Ktr : ℝ := 2 * A * M ^ 2 * (ρ + (1 + 4 * r * (r + 1) * ρ) ^ 2) with hKtr
  set Φ₀ : ℝ := (A₀ + A' + A' * h * K) * M with hΦ₀
  set Φ : ℝ := (A₀ + A' + A' * h * K) * (h ^ (r + 1) * M) with hΦ
  have hΦeq : Φ = h ^ (r + 1) * Φ₀ := by rw [hΦ, hΦ₀]; ring
  set gconst : ℝ := Φ ^ 2 / μ₀ + 2 * (h ^ (2 * r + 1) * Ktr) with hgconst
  have hgconst0 : 0 ≤ gconst := by positivity
  -- the projections
  set W : ℝ → BrokenPolynomial x r := fun t => proj x r fun y => u y t with hW
  set W' : ℝ → BrokenPolynomial x r := fun t => proj x r fun y => ut y t with hW'
  have hWd : ∀ t ∈ Icc 0 T, HasDerivWithinAt W (W' t) (Icc 0 T) t := fun t ht =>
    hasDerivWithinAt_proj hn huc hut hutc2 ht
  have he := huh.sub hWd
  -- the approximation facts at each time
  have hproj : ∀ s ∈ Icc 0 T,
      √(∑ i, ∫ y in x i.castSucc..x i.succ, (u y s - (W s i).eval y) ^ 2) ≤ h ^ (r + 1) * M ∧
      ∀ y : Fin n → ℝ, (∀ i, y i ∈ Icc (x i.castSucc) (x i.succ)) →
        ∑ i, a (y i) * (u (y i) s - (W s i).eval (y i)) ^ 2 ≤ h ^ (2 * r + 1) * Ktr := by
    intro s hs
    obtain ⟨U, hU, hUM⟩ := hreg s hs
    have hS0 : 0 ≤ SobolevInterval.seminorm (r + 1) (x 0) (x (Fin.last n)) U := apply_nonneg _ _
    refine ⟨(sqrt_sum_integral_sq_sub_proj_le_seminorm hn hnode hmesh U (huc s hs) hU).trans
      (mul_le_mul_of_nonneg_left hUM (by positivity)), fun y hy => ?_⟩
    refine (sum_mul_sq_sub_proj_le hn hA0 hA hnode hmesh h0 hminle U (huc s hs) hU hy).trans ?_
    rw [hKtr, hρ]
    have := pow_le_pow_left₀ hS0 hUM 2
    have hc : 0 ≤ 2 * A * h ^ (2 * r + 1)
        * (h / hmin + (1 + 4 * r * (r + 1) * (h / hmin)) ^ 2) := by
      positivity
    calc 2 * A * h ^ (2 * r + 1) * SobolevInterval.seminorm (r + 1) (x 0) (x (Fin.last n)) U ^ 2
          * (h / hmin + (1 + 4 * r * (r + 1) * (h / hmin)) ^ 2)
        = 2 * A * h ^ (2 * r + 1) * (h / hmin + (1 + 4 * r * (r + 1) * (h / hmin)) ^ 2)
          * SobolevInterval.seminorm (r + 1) (x 0) (x (Fin.last n)) U ^ 2 := by ring
      _ ≤ 2 * A * h ^ (2 * r + 1) * (h / hmin + (1 + 4 * r * (r + 1) * (h / hmin)) ^ 2) * M ^ 2 :=
          mul_le_mul_of_nonneg_left this hc
      _ = h ^ (2 * r + 1)
          * (2 * A * M ^ 2 * (h / hmin + (1 + 4 * r * (r + 1) * (h / hmin)) ^ 2)) := by
          ring
  -- the energy estimate for the discrete error
  set e : ℝ → BrokenPolynomial x r := fun t => uh t - W t with he_def
  set w : ℝ → ℝ := fun s => μ₀ * ‖e s‖ ^ 2
    + a (x (Fin.last n)) * traceLeft (e s) (Fin.last n) ^ 2 / 2
    + (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * jump (e s) i ^ 2 / 2)
    + a (x 0) * jump (e s) ⟨0, hn⟩ ^ 2 with hw_def
  have hec : ContinuousOn e (Icc 0 T) := he.continuousOn
  have hwc : ContinuousOn w (Icc 0 T) := by
    have h1 : ContinuousOn (fun s => μ₀ * ‖e s‖ ^ 2) (Icc 0 T) :=
      continuousOn_const.mul he.continuousOn_norm_sq
    have h2 : ContinuousOn
        (fun s => a (x (Fin.last n)) * traceLeft (e s) (Fin.last n) ^ 2 / 2) (Icc 0 T) :=
      (continuousOn_const.mul
        (((continuous_traceLeft (Fin.last n)).comp_continuousOn hec).pow 2)).div_const 2
    have h3 : ContinuousOn (fun s => ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
        a (x i.castSucc) * jump (e s) i ^ 2 / 2) (Icc 0 T) :=
      continuousOn_finsetSum _ fun i _ =>
        (continuousOn_const.mul (((continuous_jump i).comp_continuousOn hec).pow 2)).div_const 2
    have h4 : ContinuousOn (fun s => a (x 0) * jump (e s) ⟨0, hn⟩ ^ 2) (Icc 0 T) :=
      continuousOn_const.mul (((continuous_jump ⟨0, hn⟩).comp_continuousOn hec).pow 2)
    exact ((h1.add h2).add h3).add h4
  have hbound : ∀ s ∈ Ico 0 T, 2 * (((innerSL ℝ (fh s) + (a (x 0) * φ s) • traceRightL x r ⟨0, hn⟩)
      - (innerSL ℝ (W' s) + dgUpwindForm x r ha (ha₀ s) (W s))) (e s)
      - dgUpwindForm x r ha (ha₀ s) (e s) (e s)) + w s ≤ gconst := by
    intro s hs
    have hs' : s ∈ Icc 0 T := Ico_subset_Icc_self hs
    obtain ⟨U, hU, hUM⟩ := hreg s hs'
    have hux_ae : (fun y => ux y s) =ᵐ[volume.restrict (Ioo (x 0) (x (Fin.last n)))]
        SobolevInterval.deriv U 1 :=
      SobolevInterval.ae_eq_deriv_one_of_hasDerivAt hab U (huc s hs') hU fun y hy =>
        (hux y (Ioo_subset_Icc_self hy) s hs').hasDerivAt (Icc_mem_nhds hy.1 hy.2)
    have hdef := dg_defect_le hn ha (ha₀ s) hd hd' hapos hA'0 hA' hA₀0 (hA₀ s hs') hmesh h0 hminle
      (huc s hs') (fun y hy => (hux y (Ioo_subset_Icc_self hy) s hs').hasDerivAt
        (Icc_mem_nhds hy.1 hy.2)) (hutc s hs') (fun y hy => hpde y hy s hs') (hin s hs')
      (SobolevInterval.intervalIntegrable_deriv hab.le U 1) hux_ae (hproj s hs').1 (e s)
    have htr := (hproj s hs').2 (fun i => x i.succ) fun i => right_mem_Icc.2
      (hm (Fin.castSucc_lt_succ (i := i)).le)
    have hcoer := le_dgUpwindForm ha (ha₀ s) hd hd' (hμ₀ s hs') (e s)
    have hyoung := IsSemidiscreteGalerkin.two_mul_mul_norm_le hμ Φ (e s)
    have hsplit : ∑ i : Fin n, a (x i.castSucc) * jump (e s) i ^ 2 / 2
        = a (x 0) * jump (e s) ⟨0, hn⟩ ^ 2 / 2
          + ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * jump (e s) i ^ 2 / 2 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨0, hn⟩ : Fin n))]
      rfl
    have hsplit' : ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
          a (x i.castSucc) * jump (e s) i ^ 2 / 4
        = (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
          a (x i.castSucc) * jump (e s) i ^ 2 / 2) / 2 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hF : ((innerSL ℝ (fh s) + (a (x 0) * φ s) • traceRightL x r ⟨0, hn⟩)
        - (innerSL ℝ (W' s) + dgUpwindForm x r ha (ha₀ s) (W s))) (e s)
        = (pairing (fun y => f y s) (e s) + a (x 0) * φ s * traceRight (e s) ⟨0, hn⟩)
          - (⟪W' s, e s⟫ + dgUpwindForm x r ha (ha₀ s) (W s) (e s)) := by
      simp only [_root_.sub_apply, _root_.add_apply, innerSL_apply_apply,
        _root_.smul_apply, traceRightL_apply, smul_eq_mul, hfh s hs' (e s)]
    rw [hF]
    simp only [hw_def]
    rw [hsplit] at hcoer
    have hΦ' : (A₀ + A' + A' * h * K) * (h ^ (r + 1) * M) * ‖e s‖ = Φ * ‖e s‖ := by rw [hΦ]
    rw [hΦ', hsplit'] at hdef
    rw [hgconst]
    linarith
  have hstab := he.norm_sq_add_integral_le_integral (w := w) (g := fun _ => gconst) hwc
    continuousOn_const hbound ht
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hstab
  have hle : ∀ i : Fin n, x i.castSucc ≤ x i.succ := fun i => hm (Fin.castSucc_lt_succ (i := i)).le
  have hP1 : (h ^ (r + 1) * M) ^ 2 = h ^ (2 * r + 1) * (h * M ^ 2) := by
    rw [mul_pow, ← pow_mul, show (r + 1) * 2 = 2 * r + 1 + 1 by ring, pow_succ]
    ring
  set P : ℝ := h ^ (2 * r + 1) * (h * M ^ 2) with hP
  set Q : ℝ := h ^ (2 * r + 1) * Ktr with hQ
  have hP0 : 0 ≤ P := by positivity
  have hQ0 : 0 ≤ Q := by positivity
  -- the `L²` error at each time, squared
  have hsqL2 : ∀ τ ∈ Icc 0 T, ∑ i, ∫ s in x i.castSucc..x i.succ, (u s τ - (uh τ i).eval s) ^ 2
      ≤ 2 * P + 2 * ‖e τ‖ ^ 2 := by
    intro τ hτ
    have hui : IntervalIntegrable (fun y => u y τ) volume (x 0) (x (Fin.last n)) :=
      ((huc τ hτ).mono (uIcc_of_le hab.le).le).intervalIntegrable
    have hui2 : IntervalIntegrable (fun y => u y τ ^ 2) volume (x 0) (x (Fin.last n)) :=
      (((huc τ hτ).mono (uIcc_of_le hab.le).le).pow 2).intervalIntegrable
    have htri := sqrt_sum_integral_sub_sq_le hui hui2 (uh τ) (W τ)
    have hX0 : 0 ≤ ∑ i, ∫ s in x i.castSucc..x i.succ, (u s τ - (uh τ i).eval s) ^ 2 :=
      Finset.sum_nonneg fun i _ => integral_nonneg (hle i) fun _ _ => sq_nonneg _
    have hY0 : 0 ≤ ∑ i, ∫ s in x i.castSucc..x i.succ, (u s τ - (W τ i).eval s) ^ 2 :=
      Finset.sum_nonneg fun i _ => integral_nonneg (hle i) fun _ _ => sq_nonneg _
    have hne : ‖W τ - uh τ‖ = ‖e τ‖ := by rw [he_def, norm_sub_rev]
    have hY := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hproj τ hτ).1 2
    rw [Real.sq_sqrt hY0, hP1] at hY
    calc ∑ i, ∫ s in x i.castSucc..x i.succ, (u s τ - (uh τ i).eval s) ^ 2
        = √(∑ i, ∫ s in x i.castSucc..x i.succ, (u s τ - (uh τ i).eval s) ^ 2) ^ 2 :=
          (Real.sq_sqrt hX0).symm
      _ ≤ (√(∑ i, ∫ s in x i.castSucc..x i.succ, (u s τ - (W τ i).eval s) ^ 2)
          + ‖W τ - uh τ‖) ^ 2 :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) htri 2
      _ ≤ 2 * √(∑ i, ∫ s in x i.castSucc..x i.succ, (u s τ - (W τ i).eval s) ^ 2) ^ 2
          + 2 * ‖W τ - uh τ‖ ^ 2 := add_sq_le.trans_eq (mul_add _ _ _)
      _ ≤ 2 * P + 2 * ‖e τ‖ ^ 2 := by
          rw [Real.sq_sqrt hY0, hne]
          linarith only [hY]
  -- the integrand of the left side at each time
  have hL : ∀ τ ∈ Icc 0 T,
      (∑ i, ∫ s in x i.castSucc..x i.succ, (u s τ - (uh τ i).eval s) ^ 2)
        + (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * jump (uh τ) i ^ 2)
        + a (x 0) * (traceRight (uh τ) ⟨0, hn⟩ - φ τ) ^ 2
      ≤ 2 * P + 10 * Q + (2 / μ₀ + 6) * w τ := by
    intro τ hτ
    have hTrp := (hproj τ hτ).2 (fun i => x i.castSucc) fun i => left_mem_Icc.2 (hle i)
    have hTrm := (hproj τ hτ).2 (fun i => x i.succ) fun i => right_mem_Icc.2 (hle i)
    have huhW : uh τ = e τ + W τ := by rw [he_def]; simp
    have hapos' : ∀ i : Fin n, 0 ≤ a (x i.castSucc) := fun i =>
      hapos _ (Icc_panel_subset hm i (left_mem_Icc.2 (hle i)))
    -- the jumps
    have hjump : ∀ i : Fin n, a (x i.castSucc) * jump (uh τ) i ^ 2
        ≤ 2 * (a (x i.castSucc) * jump (e τ) i ^ 2)
          + 4 * (a (x i.castSucc) * (u (x i.castSucc) τ - traceLeft (W τ) i.castSucc) ^ 2)
          + 4 * (a (x i.castSucc) * (u (x i.castSucc) τ - (W τ i).eval (x i.castSucc)) ^ 2) := by
      intro i
      have e1 : jump (uh τ) i = jump (e τ) i + ((u (x i.castSucc) τ - traceLeft (W τ) i.castSucc)
          - (u (x i.castSucc) τ - (W τ i).eval (x i.castSucc))) := by
        rw [huhW, jump_add, jump_apply (W τ), traceRight_apply]
        ring
      rw [e1]
      exact mul_sq_add_sub_le (hapos' i)
    have hsumjump : ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * jump (uh τ) i ^ 2
        ≤ 2 * (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * jump (e τ) i ^ 2)
          + 4 * Q + 4 * Q := by
      have hminus : ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
          a (x i.castSucc) * (u (x i.castSucc) τ - traceLeft (W τ) i.castSucc) ^ 2 ≤ Q := by
        have hnode := node_sum_eq hn fun j => a (x j) * (u (x j) τ - traceLeft (W τ) j) ^ 2
        have hlast : 0 ≤ a (x (Fin.last n))
            * (u (x (Fin.last n)) τ - traceLeft (W τ) (Fin.last n)) ^ 2 :=
          mul_nonneg (hapos _ (right_mem_Icc.2 hab.le)) (sq_nonneg _)
        have hrw : ∑ i : Fin n, a (x i.succ) * (u (x i.succ) τ - traceLeft (W τ) i.succ) ^ 2
            = ∑ i : Fin n, a (x i.succ) * (u (x i.succ) τ - (W τ i).eval (x i.succ)) ^ 2 :=
          Finset.sum_congr rfl fun i _ => by rw [traceLeft_succ]
        linarith only [hnode, hlast, hrw, hTrm]
      have hplus : ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
          a (x i.castSucc) * (u (x i.castSucc) τ - (W τ i).eval (x i.castSucc)) ^ 2 ≤ Q :=
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun i _ _ => mul_nonneg (hapos' i) (sq_nonneg _)).trans hTrp
      calc ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * jump (uh τ) i ^ 2
          ≤ ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), (2 * (a (x i.castSucc) * jump (e τ) i ^ 2)
              + 4 * (a (x i.castSucc) * (u (x i.castSucc) τ - traceLeft (W τ) i.castSucc) ^ 2)
              + 4 * (a (x i.castSucc) * (u (x i.castSucc) τ - (W τ i).eval (x i.castSucc)) ^ 2)) :=
            Finset.sum_le_sum fun i _ => hjump i
        _ = 2 * (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * jump (e τ) i ^ 2)
              + 4 * (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
                a (x i.castSucc) * (u (x i.castSucc) τ - traceLeft (W τ) i.castSucc) ^ 2)
              + 4 * (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
                a (x i.castSucc) * (u (x i.castSucc) τ - (W τ i).eval (x i.castSucc)) ^ 2) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
              Finset.mul_sum]
        _ ≤ 2 * (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * jump (e τ) i ^ 2)
              + 4 * Q + 4 * Q := by gcongr
    -- the inflow term
    have hin' : a (x 0) * (traceRight (uh τ) ⟨0, hn⟩ - φ τ) ^ 2
        ≤ 2 * (a (x 0) * jump (e τ) ⟨0, hn⟩ ^ 2) + 2 * Q := by
      have hc : x (⟨0, hn⟩ : Fin n).castSucc = x 0 := rfl
      have e1 : traceRight (uh τ) ⟨0, hn⟩ - φ τ
          = jump (e τ) ⟨0, hn⟩ - (u (x 0) τ - (W τ ⟨0, hn⟩).eval (x 0)) := by
        rw [huhW, traceRight_add, ← jump_zero (e τ) hn, traceRight_apply, hc, hin τ hτ]
        ring
      have h0' := (Finset.single_le_sum (f := fun i : Fin n =>
          a (x i.castSucc) * (u (x i.castSucc) τ - (W τ i).eval (x i.castSucc)) ^ 2)
          (fun i _ => mul_nonneg (hapos' i) (sq_nonneg _)) (Finset.mem_univ ⟨0, hn⟩)).trans hTrp
      simp only [hc] at h0'
      have ha0 := hapos _ (left_mem_Icc.2 hab.le)
      rw [e1]
      have := mul_sq_sub_le (c := a (x 0)) (j := jump (e τ) ⟨0, hn⟩)
        (p := u (x 0) τ - (W τ ⟨0, hn⟩).eval (x 0)) ha0
      linarith only [this, h0']
    -- the parts of `w`
    have hw1 : 0 ≤ a (x (Fin.last n)) * traceLeft (e τ) (Fin.last n) ^ 2 / 2 := by
      have := hapos _ (right_mem_Icc.2 hab.le); positivity
    have hw2 : 0 ≤ ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
        a (x i.castSucc) * jump (e τ) i ^ 2 / 2 :=
      Finset.sum_nonneg fun i _ => by have := hapos' i; positivity
    have hw3 : 0 ≤ a (x 0) * jump (e τ) ⟨0, hn⟩ ^ 2 := by
      have := hapos _ (left_mem_Icc.2 hab.le); positivity
    have hw4 : 0 ≤ μ₀ * ‖e τ‖ ^ 2 := by positivity
    have hwτ : w τ = μ₀ * ‖e τ‖ ^ 2 + a (x (Fin.last n)) * traceLeft (e τ) (Fin.last n) ^ 2 / 2
        + (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * jump (e τ) i ^ 2 / 2)
        + a (x 0) * jump (e τ) ⟨0, hn⟩ ^ 2 := rfl
    have hsumhalf : ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * jump (e τ) i ^ 2
        = 2 * ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
          a (x i.castSucc) * jump (e τ) i ^ 2 / 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hnorm : 2 * ‖e τ‖ ^ 2 = 2 / μ₀ * (μ₀ * ‖e τ‖ ^ 2) := by field_simp
    have hkey : 2 * ‖e τ‖ ^ 2
        + 2 * (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * jump (e τ) i ^ 2)
        + 2 * (a (x 0) * jump (e τ) ⟨0, hn⟩ ^ 2) ≤ (2 / μ₀ + 6) * w τ := by
      rw [hwτ, hnorm, hsumhalf]
      have := energy_parts_le hμ hw4 hw1 hw2 hw3
      linarith only [this]
    have hsq := hsqL2 τ hτ
    linarith only [hsq, hsumjump, hin', hkey]
  -- integrating the bound on the integrand
  have hwint : IntervalIntegrable w volume 0 t := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le ht.1]
    exact hwc.mono (Icc_subset_Icc le_rfl ht.2)
  have hLnn : ∀ τ ∈ Icc 0 T, 0 ≤ (∑ i, ∫ s in x i.castSucc..x i.succ, (u s τ - (uh τ i).eval s) ^ 2)
      + (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * jump (uh τ) i ^ 2)
      + a (x 0) * (traceRight (uh τ) ⟨0, hn⟩ - φ τ) ^ 2 := by
    intro τ _
    have h1 : 0 ≤ ∑ i, ∫ s in x i.castSucc..x i.succ, (u s τ - (uh τ i).eval s) ^ 2 :=
      Finset.sum_nonneg fun i _ => integral_nonneg (hle i) fun _ _ => sq_nonneg _
    have h2 : 0 ≤ ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * jump (uh τ) i ^ 2 :=
      Finset.sum_nonneg fun i _ =>
        mul_nonneg (hapos _ (Icc_panel_subset hm i (left_mem_Icc.2 (hle i)))) (sq_nonneg _)
    have h3 : 0 ≤ a (x 0) * (traceRight (uh τ) ⟨0, hn⟩ - φ τ) ^ 2 :=
      mul_nonneg (hapos _ (left_mem_Icc.2 hab.le)) (sq_nonneg _)
    linarith only [h1, h2, h3]
  have hLint : ∫ τ in (0 : ℝ)..t,
      ((∑ i, ∫ s in x i.castSucc..x i.succ, (u s τ - (uh τ i).eval s) ^ 2)
        + (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * jump (uh τ) i ^ 2)
        + a (x 0) * (traceRight (uh τ) ⟨0, hn⟩ - φ τ) ^ 2)
      ≤ t * (2 * P + 10 * Q) + (2 / μ₀ + 6) * ∫ τ in (0 : ℝ)..t, w τ := by
    have hR : ∫ τ in (0 : ℝ)..t, (2 * P + 10 * Q + (2 / μ₀ + 6) * w τ)
        = t * (2 * P + 10 * Q) + (2 / μ₀ + 6) * ∫ τ in (0 : ℝ)..t, w τ := by
      rw [integral_add intervalIntegrable_const (hwint.const_mul _),
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul,
        sub_zero]
    rw [← hR, integral_of_le ht.1, integral_of_le ht.1]
    refine integral_mono_of_nonneg ?_ ?_ ?_
    · exact (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun τ hτ =>
        hLnn τ (Icc_subset_Icc le_rfl ht.2 (Ioc_subset_Icc_self hτ)))
    · exact ((continuousOn_const.add (continuousOn_const.mul (hwc.mono
        (Icc_subset_Icc le_rfl ht.2)))).integrableOn_Icc).mono_set Ioc_subset_Icc_self
    · exact (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun τ hτ =>
        hL τ (Icc_subset_Icc le_rfl ht.2 (Ioc_subset_Icc_self hτ)))
  -- the initial error
  have he0 : ‖u₀h - W 0‖ ^ 2
      ≤ 2 * (∑ i, ∫ s in x i.castSucc..x i.succ, (u s 0 - (u₀h i).eval s) ^ 2) + 2 * P := by
    have hui : IntervalIntegrable (fun y => u y 0) volume (x 0) (x (Fin.last n)) :=
      ((huc 0 hT0).mono (uIcc_of_le hab.le).le).intervalIntegrable
    have hui2 : IntervalIntegrable (fun y => u y 0 ^ 2) volume (x 0) (x (Fin.last n)) :=
      (((huc 0 hT0).mono (uIcc_of_le hab.le).le).pow 2).intervalIntegrable
    have htri := norm_sub_le_sqrt_add_sqrt hui hui2 u₀h (W 0)
    have hY0 : 0 ≤ ∑ i, ∫ s in x i.castSucc..x i.succ, (u s 0 - (W 0 i).eval s) ^ 2 :=
      Finset.sum_nonneg fun i _ => integral_nonneg (hle i) fun _ _ => sq_nonneg _
    have hX0 : 0 ≤ ∑ i, ∫ s in x i.castSucc..x i.succ, (u s 0 - (u₀h i).eval s) ^ 2 :=
      Finset.sum_nonneg fun i _ => integral_nonneg (hle i) fun _ _ => sq_nonneg _
    have hY := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hproj 0 hT0).1 2
    rw [Real.sq_sqrt hY0, hP1] at hY
    calc ‖u₀h - W 0‖ ^ 2
        ≤ (√(∑ i, ∫ s in x i.castSucc..x i.succ, (u s 0 - (u₀h i).eval s) ^ 2)
          + √(∑ i, ∫ s in x i.castSucc..x i.succ, (u s 0 - (W 0 i).eval s) ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) htri 2
      _ ≤ 2 * √(∑ i, ∫ s in x i.castSucc..x i.succ, (u s 0 - (u₀h i).eval s) ^ 2) ^ 2
          + 2 * √(∑ i, ∫ s in x i.castSucc..x i.succ, (u s 0 - (W 0 i).eval s) ^ 2) ^ 2 :=
          add_sq_le.trans_eq (mul_add _ _ _)
      _ ≤ 2 * (∑ i, ∫ s in x i.castSucc..x i.succ, (u s 0 - (u₀h i).eval s) ^ 2) + 2 * P := by
          rw [Real.sq_sqrt hX0, Real.sq_sqrt hY0]
          linarith only [hY]
  -- the pieces of the energy estimate
  have hwnn : 0 ≤ ∫ τ in (0 : ℝ)..t, w τ := by
    refine integral_nonneg ht.1 fun τ hτ => ?_
    have h1 := hapos _ (right_mem_Icc.2 hab.le)
    have h2 := hapos _ (left_mem_Icc.2 hab.le)
    have h3 : 0 ≤ ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
        a (x i.castSucc) * jump (e τ) i ^ 2 / 2 :=
      Finset.sum_nonneg fun i _ => by
        have := hapos _ (Icc_panel_subset hm i (left_mem_Icc.2 (hle i))); positivity
    change 0 ≤ μ₀ * ‖e τ‖ ^ 2 + a (x (Fin.last n)) * traceLeft (e τ) (Fin.last n) ^ 2 / 2
      + (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * jump (e τ) i ^ 2 / 2)
      + a (x 0) * jump (e τ) ⟨0, hn⟩ ^ 2
    positivity
  have hwle : ∫ τ in (0 : ℝ)..t, w τ ≤ ‖u₀h - W 0‖ ^ 2 + t * gconst := by
    linarith only [hstab, sq_nonneg ‖e t‖]
  have hY₀ : ∑ i, ∫ s in x i.castSucc..x i.succ, (u s t - (uh t i).eval s) ^ 2
      ≤ 2 * P + 2 * (‖u₀h - W 0‖ ^ 2 + t * gconst) := by
    have := hsqL2 t ht
    linarith only [this, hstab, hwnn]
  -- assembling
  have hfinal := dg_final (μ₀ := μ₀) hμ ht.2 hP0 hQ0 hgconst0 he0 hwle hY₀ hLint
  refine hfinal.trans (le_of_eq ?_)
  have hΦsq : Φ ^ 2 = h ^ (2 * r + 1) * (h * Φ₀ ^ 2) := by
    rw [hΦeq, mul_pow, ← pow_mul, show (r + 1) * 2 = 2 * r + 1 + 1 by ring, pow_succ]
    ring
  rw [hgconst, hΦsq, hQ, hP, hKtr, hΦ₀, hK, hρ, dgConst]
  ring

/-- The **error estimate of the discontinuous Galerkin method** for the transport equation. Under
the hypotheses of `Variational.dG_error_sq_le`, for every $t \in [0, T]$
$$\|u(t) - u_h(t)\| + \Bigl(\int_0^t \Bigl(\|u(\tau) - u_h(\tau)\|^2 +
  \sum_{j=1}^{n-1} a(x_j) [u_h(\tau)]_j^2 +
  a(x_0) \bigl(u_h^+(x_0, \tau) - \varphi(\tau)\bigr)^2\Bigr) d\tau\Bigr)^{1/2}
  \le \sqrt{2} \Bigl(\sqrt{16 + 4/\mu_0}\, \|u(0) - u_{0,h}\| +
    \sqrt{C_{DG}}\, h^r \sqrt{h}\Bigr),$$
where $C_{DG}$ is `Variational.dgConst`. This is the estimate $O(\|u_0 - u_{0,h}\| + h^{r+1/2})$
for discontinuous finite elements of degree $r$ in [quarteroni2000numerical], §13.10.1, which
quotes it from [quarteroni1994numerical], §14.3.3, without proof; here the constants are
explicit.

The power $h^{r+1/2}$ is written $h^r \sqrt{h}$. The estimate follows from the squared form by
$\sqrt{p} + \sqrt{q} \le \sqrt{2} \sqrt{p + q}$ and $\sqrt{p + q} \le \sqrt{p} + \sqrt{q}$. -/
theorem dG_error_le (hn : 0 < n) {T : ℝ} (hT : 0 < T)
    (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n))))
    {μ₀ : ℝ} (hμ : 0 < μ₀)
    (hμ₀ : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc (x 0) (x (Fin.last n)), μ₀ ≤ a₀ s t - deriv a s / 2)
    (hapos : ∀ s ∈ Icc (x 0) (x (Fin.last n)), 0 ≤ a s) {A A' A₀ : ℝ}
    (hA : ∀ s ∈ Icc (x 0) (x (Fin.last n)), |a s| ≤ A)
    (hA' : ∀ s ∈ Icc (x 0) (x (Fin.last n)), |deriv a s| ≤ A')
    (hA₀ : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc (x 0) (x (Fin.last n)), |a₀ s t| ≤ A₀)
    {u ux ut f : ℝ → ℝ → ℝ} {φ : ℝ → ℝ}
    (huc2 : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (Icc (x 0) (x (Fin.last n)) ×ˢ Icc 0 T))
    (hux : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun y => u y t) (ux y t) (Icc (x 0) (x (Fin.last n))) y)
    (hut : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun t => u y t) (ut y t) (Icc 0 T) t)
    (hutc2 : ContinuousOn (fun p : ℝ × ℝ => ut p.1 p.2) (Icc (x 0) (x (Fin.last n)) ×ˢ Icc 0 T))
    (hpde : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T,
      ut y t + a y * ux y t + a₀ y t * u y t = f y t)
    (hin : ∀ t ∈ Icc 0 T, u (x 0) t = φ t) {M : ℝ}
    (hreg : ∀ t ∈ Icc 0 T, ∃ U : SobolevInterval (r + 1) (x 0) (x (Fin.last n)),
      SobolevInterval.fn U =ᵐ[volume.restrict (Ioo (x 0) (x (Fin.last n)))] (fun y => u y t) ∧
        SobolevInterval.seminorm (r + 1) (x 0) (x (Fin.last n)) U ≤ M)
    {node : Fin n → Fin (r + 1) → ℝ} (hnode : IsNodes x r node) {h hmin : ℝ}
    (hmesh : ∀ i : Fin n, x i.succ - x i.castSucc ≤ h) (h0 : 0 < hmin)
    (hminle : ∀ i : Fin n, hmin ≤ x i.succ - x i.castSucc)
    {fh : ℝ → BrokenPolynomial x r}
    (hfh : ∀ t ∈ Icc 0 T, ∀ v, ⟪fh t, v⟫ = pairing (fun y => f y t) v)
    {u₀h : BrokenPolynomial x r} {uh : ℝ → BrokenPolynomial x r}
    (huh : IsSemidiscreteGalerkin (fun t => dgUpwindForm x r ha (ha₀ t))
      (fun t => innerSL ℝ (fh t) + (a (x 0) * φ t) • traceRightL x r ⟨0, hn⟩) u₀h T uh)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    √(∑ i, ∫ s in x i.castSucc..x i.succ, (u s t - (uh t i).eval s) ^ 2)
      + √(∫ τ in (0 : ℝ)..t, ((∑ i, ∫ s in x i.castSucc..x i.succ, (u s τ - (uh τ i).eval s) ^ 2)
          + (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), a (x i.castSucc) * jump (uh τ) i ^ 2)
          + a (x 0) * (traceRight (uh τ) ⟨0, hn⟩ - φ τ) ^ 2))
    ≤ √2 * (√(16 + 4 / μ₀) * √(∑ i, ∫ s in x i.castSucc..x i.succ, (u s 0 - (u₀h i).eval s) ^ 2)
        + √(dgConst r A A' A₀ μ₀ T M h hmin) * (h ^ r * √h)) := by
  have hm : Monotone x := hx.out.monotone
  have hab : x 0 < x (Fin.last n) := hx.out (Fin.pos_iff_ne_zero.2 (Fin.ne_of_val_ne hn.ne'))
  have hle : ∀ i : Fin n, x i.castSucc ≤ x i.succ := fun i => hm (Fin.castSucc_lt_succ (i := i)).le
  have hh : 0 ≤ h := (sub_nonneg.2 (hle ⟨0, hn⟩)).trans (hmesh ⟨0, hn⟩)
  have hT0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  obtain ⟨U₀, hU₀, hU₀M⟩ := hreg 0 hT0
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA (x 0) (left_mem_Icc.2 hab.le))
  have key := dG_error_sq_le hn hT ha ha₀ hd hd' hμ hμ₀ hapos hA hA' hA₀ huc2 hux hut hutc2 hpde
    hin hreg hnode hmesh h0 hminle hfh huh ht
  -- nonnegativity of the pieces
  have hY₀ : 0 ≤ ∑ i, ∫ s in x i.castSucc..x i.succ, (u s t - (uh t i).eval s) ^ 2 :=
    Finset.sum_nonneg fun i _ => intervalIntegral.integral_nonneg (hle i) fun _ _ => sq_nonneg _
  have hI : 0 ≤ ∫ τ in (0 : ℝ)..t,
      ((∑ i, ∫ s in x i.castSucc..x i.succ, (u s τ - (uh τ i).eval s) ^ 2)
        + (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
            a (x i.castSucc) * jump (uh τ) i ^ 2)
        + a (x 0) * (traceRight (uh τ) ⟨0, hn⟩ - φ τ) ^ 2) := by
    refine intervalIntegral.integral_nonneg ht.1 fun τ _ => ?_
    have h1 : 0 ≤ ∑ i, ∫ s in x i.castSucc..x i.succ, (u s τ - (uh τ i).eval s) ^ 2 :=
      Finset.sum_nonneg fun i _ => intervalIntegral.integral_nonneg (hle i) fun _ _ => sq_nonneg _
    have h2 : 0 ≤ ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
        a (x i.castSucc) * jump (uh τ) i ^ 2 :=
      Finset.sum_nonneg fun i _ => mul_nonneg
        (hapos _ (Icc_panel_subset hm i (left_mem_Icc.2 (hle i)))) (sq_nonneg _)
    have h3 : 0 ≤ a (x 0) * (traceRight (uh τ) ⟨0, hn⟩ - φ τ) ^ 2 :=
      mul_nonneg (hapos _ (left_mem_Icc.2 hab.le)) (sq_nonneg _)
    linarith
  have hYi : 0 ≤ ∑ i, ∫ s in x i.castSucc..x i.succ, (u s 0 - (u₀h i).eval s) ^ 2 :=
    Finset.sum_nonneg fun i _ => intervalIntegral.integral_nonneg (hle i) fun _ _ => sq_nonneg _
  have hC₁ : 0 ≤ 16 + 4 / μ₀ := by positivity
  have hC₂ : 0 ≤ dgConst r A A' A₀ μ₀ T M h hmin := by
    unfold dgConst
    positivity
  have hpow : √(h ^ (2 * r + 1)) = h ^ r * √h := by
    rw [show h ^ (2 * r + 1) = (h ^ r) ^ 2 * h by rw [pow_succ, pow_mul'],
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg hh r)]
  calc √(∑ i, ∫ s in x i.castSucc..x i.succ, (u s t - (uh t i).eval s) ^ 2)
        + √(∫ τ in (0 : ℝ)..t,
          ((∑ i, ∫ s in x i.castSucc..x i.succ, (u s τ - (uh τ i).eval s) ^ 2)
          + (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
              a (x i.castSucc) * jump (uh τ) i ^ 2)
          + a (x 0) * (traceRight (uh τ) ⟨0, hn⟩ - φ τ) ^ 2))
      ≤ √2 * √((∑ i, ∫ s in x i.castSucc..x i.succ, (u s t - (uh t i).eval s) ^ 2)
          + ∫ τ in (0 : ℝ)..t,
          ((∑ i, ∫ s in x i.castSucc..x i.succ, (u s τ - (uh τ i).eval s) ^ 2)
          + (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
              a (x i.castSucc) * jump (uh τ) i ^ 2)
          + a (x 0) * (traceRight (uh τ) ⟨0, hn⟩ - φ τ) ^ 2)) :=
        Real.sqrt_add_sqrt_le_sqrt_two_mul hY₀ hI
    _ ≤ √2 * √((16 + 4 / μ₀) * (∑ i, ∫ s in x i.castSucc..x i.succ, (u s 0 - (u₀h i).eval s) ^ 2)
          + dgConst r A A' A₀ μ₀ T M h hmin * h ^ (2 * r + 1)) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt key) (Real.sqrt_nonneg _)
    _ ≤ √2 * (√((16 + 4 / μ₀) * (∑ i, ∫ s in x i.castSucc..x i.succ, (u s 0 - (u₀h i).eval s) ^ 2))
          + √(dgConst r A A' A₀ μ₀ T M h hmin * h ^ (2 * r + 1))) :=
        mul_le_mul_of_nonneg_left (by
          simp only [Real.sqrt_eq_rpow]
          exact Real.rpow_add_le_add_rpow (by positivity) (by positivity) (by norm_num)
            (by norm_num))
          (Real.sqrt_nonneg _)
    _ = √2 * (√(16 + 4 / μ₀) * √(∑ i, ∫ s in x i.castSucc..x i.succ, (u s 0 - (u₀h i).eval s) ^ 2)
          + √(dgConst r A A' A₀ μ₀ T M h hmin) * (h ^ r * √h)) := by
        rw [Real.sqrt_mul hC₁, Real.sqrt_mul hC₂, hpow]

end DGTimeDependent

end Variational

end
