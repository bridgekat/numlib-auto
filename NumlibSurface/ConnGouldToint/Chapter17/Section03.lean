/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Subproblem.Model
import Numlib.Analysis.InnerProductSpace.BoxProjection
import Mathlib.Data.Finset.Sort

/-!
# Conn, Gould and Toint, Section 17.3: The generalized Cauchy point on a box

Section 17.3 of [conn2000trust] computes the generalized Cauchy point for the quadratic model
$m(s) = f + \langle g, s \rangle + \frac{1}{2} \langle s, H s \rangle$ on a box of displacements
$s$. The projected path $t \mapsto P(t d)$ onto the box is piecewise affine, with a breakpoint at
each parameter $t$ where a coordinate reaches its bound. On each affine piece $s + t v$ the model is
a quadratic in $t$, with slope $\langle g, v \rangle + \langle s, H v \rangle$ and curvature
$\langle v, H v \rangle$. Algorithm 17.3.1 scans the pieces in order and stops at the first local
minimizer of the model along the path. This module formalizes the model, the path, the expansion
along a piece, and a corrected Algorithm 17.3.1. The projection is `bestApprox` onto `euclideanBox`
from `Numlib.Analysis.InnerProductSpace.BoxProjection`, and the model is `Subproblem.quadModel` from
`Numlib.Optimization.Subproblem.Model`.

## Main definitions

* Equation (17.3.1), `ConnGouldToint.Chapter17.cauchyQuadratic`: the quadratic model with its
  constant term.
* Equation (17.3.2), `ConnGouldToint.Chapter17.projectedCauchyPath`: the projection of $t d$ onto
  the box.
* Equation (17.3.3), `ConnGouldToint.Chapter17.cauchySegment`: the affine piece $s + t d$.
* Algorithm 17.3.1, `ConnGouldToint.Chapter17.boxedCauchyBreakpoint`: the breakpoint of one
  coordinate, with the bounds clipped by the radius.
* Algorithm 17.3.1, `ConnGouldToint.Chapter17.generalizedCauchyPoint`: the corrected breakpoint
  scan.

## Main results

* Equations (17.3.4)–(17.3.5), `ConnGouldToint.Chapter17.cauchyQuadratic_on_segment`: the expansion
  of the model along an affine piece.
* Algorithm 17.3.1, `ConnGouldToint.Chapter17.cauchyQuadratic_lt_on_negative_stationary_segment`: at
  zero slope and negative curvature, the model decreases strictly along the piece.
* Algorithm 17.3.1,
  `ConnGouldToint.Chapter17.generalizedCauchyPoint_eq_zero_of_no_positive_breakpoint`: with no
  positive breakpoint, the scan returns the zero displacement.
* Algorithm 17.3.1, `ConnGouldToint.Chapter17.generalizedCauchyPoint_zero_radius`: at radius $0$,
  the scan returns the zero displacement.

## Deviations from the source

* **Corrected zero slope and terminal cases.** Algorithm 17.3.1 continues at a zero slope with
  negative curvature and gives explicit terminal and degenerate-box cases. See
  `ConnGouldToint.Chapter17.cauchyQuadratic_lt_on_negative_stationary_segment`,
  `ConnGouldToint.Chapter17.generalizedCauchyPoint`,
  `ConnGouldToint.Chapter17.generalizedCauchyPoint_eq_zero_of_no_positive_breakpoint`,
  `ConnGouldToint.Chapter17.generalizedCauchyPoint_zero_radius`.
* **Algorithm 17.3.1** (correction). A zero slope stops the scan only if the curvature of the
  outgoing piece is nonnegative; at negative curvature the model still decreases. See
  `ConnGouldToint.Chapter17.cauchyQuadratic_lt_on_negative_stationary_segment`.
* **Algorithm 17.3.1** (reading). After the last breakpoint the path is constant, and the scan
  returns that breakpoint without asking for another one. See
  `ConnGouldToint.Chapter17.generalizedCauchyPoint`.
-/

open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter17

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Equation (17.3.1)** of [conn2000trust]. For $f \in \mathbb{R}$, $g \in E$ and a continuous
linear map $H : E \to E$, the **quadratic model** is
$$m(s) = f + \langle g, s \rangle + \tfrac{1}{2} \langle s, H s \rangle.$$
-/
noncomputable def cauchyQuadratic (f : ℝ) (g : E) (H : E →L[ℝ] E) (s : E) : ℝ :=
  f + Subproblem.quadModel g H s

/-- **Equation (17.3.2)** of [conn2000trust]. Let $l, u \in [-\infty, \infty]^\iota$ be bounds on
the displacement, for a finite index type $\iota$, and let $d \in \mathbb{R}^\iota$. The
**projected Cauchy path** is $p(t) = P(t d)$, where $P$ is the Euclidean projection onto the box
$\{s : l_i \le s_i \le u_i \text{ for all } i\}$.

The box is `euclideanBox l u` and the projection is `bestApprox`. The bounds are relative to the
base point, so the path starts at the zero displacement when the box contains it. -/
noncomputable def projectedCauchyPath {ι : Type*} [Fintype ι] (l u : ι → EReal)
    (d : EuclideanSpace ℝ ι) (t : ℝ) : EuclideanSpace ℝ ι :=
  bestApprox (euclideanBox l u) (t • d)

/-- **Equation (17.3.3)** of [conn2000trust]. For $s, d \in E$, the **affine piece** of the path
after a breakpoint is $t \mapsto s + t d$. -/
def cauchySegment (s d : E) (t : ℝ) : E :=
  s + t • d

/-- **Equations (17.3.4)–(17.3.5)** of [conn2000trust]. Let $f \in \mathbb{R}$, $g, s, d \in E$ and
$t \in \mathbb{R}$, and let $H : E \to E$ be a symmetric continuous linear map. Then
$$m(s + t d) = m(s) + t \bigl(\langle g, d \rangle + \langle s, H d \rangle\bigr) + \tfrac{1}{2}
  t^2 \langle d, H d \rangle.$$
-/
theorem cauchyQuadratic_on_segment (f : ℝ) (g s d : E) {H : E →L[ℝ] E}
    (hH : H.toLinearMap.IsSymmetric) (t : ℝ) :
    cauchyQuadratic f g H (cauchySegment s d t) =
      cauchyQuadratic f g H s + t * (⟪g, d⟫ + ⟪s, H d⟫) +
        (1 / 2 : ℝ) * t ^ 2 * ⟪d, H d⟫ := by
  have hcross : ⟪d, H s⟫ = ⟪s, H d⟫ := (hH d s).symm.trans (real_inner_comm _ _)
  simp only [cauchyQuadratic, cauchySegment, Subproblem.quadModel_def, map_add, map_smul,
    inner_add_right, inner_add_left, inner_smul_right, real_inner_smul_left, hcross]
  ring

/-- **Algorithm 17.3.1** of [conn2000trust], breakpoint of one coordinate. Let
$l_i, u_i \in [-\infty, \infty]$ be the bounds of the coordinate relative to the base point,
$\Delta \in \mathbb{R}$ the radius and $d_i \in \mathbb{R}$ the direction. The **breakpoint** is
$$t_i = \begin{cases} \min\{u_i, \Delta\} / d_i & \text{if } d_i > 0, \\ \max\{l_i, -\Delta\} /
  d_i & \text{if } d_i < 0, \\ 0 & \text{if } d_i = 0. \end{cases}$$

The radius clips infinite bounds to finite values. The minimum and the maximum are taken in the
extended reals and converted to real numbers with `EReal.toReal`. -/
noncomputable def boxedCauchyBreakpoint (l u : EReal) (Δ d : ℝ) : ℝ :=
  if 0 < d then (min u (Δ : EReal)).toReal / d
  else if d < 0 then (max l ((-Δ : ℝ) : EReal)).toReal / d
  else 0

/-- **Algorithm 17.3.1** of [conn2000trust], continuation at a zero slope. Let $f \in \mathbb{R}$,
$g, s, d \in E$, and let $H : E \to E$ be a symmetric continuous linear map. If the slope
$\langle g, d \rangle + \langle s, H d \rangle$ is $0$ and the curvature
$\langle d, H d \rangle$ is negative, then $m(s + t d) < m(s)$ for every $t \neq 0$. Therefore
Step 3 must continue in this case.

**Correction.** At zero slope the scan stops only with nonnegative outgoing curvature. Equal
breakpoints are grouped, the scan returns the endpoint of the last segment, and it returns zero when
no positive breakpoint exists, including a zero-radius box containing the origin.
-/
theorem cauchyQuadratic_lt_on_negative_stationary_segment (f : ℝ) (g s d : E)
    {H : E →L[ℝ] E} (hH : H.toLinearMap.IsSymmetric)
    (hSlope : ⟪g, d⟫ + ⟪s, H d⟫ = 0) (hCurv : ⟪d, H d⟫ < 0)
    {t : ℝ} (ht : t ≠ 0) :
    cauchyQuadratic f g H (cauchySegment s d t) < cauchyQuadratic f g H s := by
  rw [cauchyQuadratic_on_segment f g s d hH, hSlope, mul_zero, add_zero]
  exact add_lt_of_neg_right _ (mul_neg_of_pos_of_neg (by positivity) hCurv)

private noncomputable def cauchyFrozenDirection {ι : Type*} [Fintype ι]
    (b : ι → ℝ) (d : EuclideanSpace ℝ ι) (t : ℝ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun i ↦ if b i = t then d i else 0

private noncomputable def cauchyScan {ι : Type*} [Fintype ι]
    (b : ι → ℝ) (g d : EuclideanSpace ℝ ι)
    (H : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :
    List ℝ → ℝ → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι → ℝ →
      EuclideanSpace ℝ ι → ℝ × EuclideanSpace ℝ ι
  | [], t, s, _, _, _ => (t, s)
  | next :: tail, t, s, v, gv, Hv =>
    let slope := gv + ⟪s, Hv⟫
    let curvature := ⟪v, Hv⟫
    let step := -slope / curvature
    if 0 < slope ∨ (slope = 0 ∧ 0 ≤ curvature) then (t, s)
    else if 0 < curvature ∧ step < next - t then
      (t + step, cauchySegment s v step)
    else
      let e := cauchyFrozenDirection b d next
      cauchyScan b g d H tail next (cauchySegment s v (next - t))
        (v - e) (gv - ⟪g, e⟫) (Hv - H e)

/-- **Algorithm 17.3.1** of [conn2000trust], corrected. Let $l, u$ be bounds on the displacement,
let $\Delta$ be the radius, $g, d \in \mathbb{R}^\iota$ and $H$ a continuous linear map. Let
$t_i$ be the breakpoints of the coordinates and $0 < \tau_1 < \dots < \tau_k$ the distinct
positive breakpoints. The scan starts at $t = 0$, $s = 0$ with the direction $v$ obtained from
$d$ by setting the coordinates with $t_i = 0$ to zero. On the piece from $t$ to the next
breakpoint $\tau$, let $\sigma = \langle g, v \rangle + \langle s, H v \rangle$ be the slope and
$\kappa = \langle v, H v \rangle$ the curvature.

* If $\sigma > 0$, or $\sigma = 0$ and $\kappa \ge 0$, the scan returns $(t, s)$.
* Otherwise, if $\kappa > 0$ and $-\sigma / \kappa < \tau - t$, it returns
  $(t - \sigma / \kappa, s - (\sigma / \kappa) v)$.
* Otherwise it replaces $s$ by $s + (\tau - t) v$ and $t$ by $\tau$, and sets to zero the
  coordinates of $v$ with $t_i = \tau$.

When no breakpoint remains, the scan returns $(t, s)$. The first component is the path parameter
and the second the displacement.

**Correction.** A zero slope stops the scan only if the outgoing curvature is nonnegative. At
negative curvature the model decreases strictly along the piece; see
`ConnGouldToint.Chapter17.cauchyQuadratic_lt_on_negative_stationary_segment`.

**Reading.** Equal breakpoints are grouped. After the last breakpoint the path is constant, and
the scan returns its left endpoint without asking for another breakpoint.

The algorithm is meant for a box that contains the zero displacement; the definition itself has
no hypothesis on the bounds. The breakpoints are
`ConnGouldToint.Chapter17.boxedCauchyBreakpoint`.

**Correction.** At zero slope the scan stops only with nonnegative outgoing curvature. Equal
breakpoints are grouped, the scan returns the endpoint of the last segment, and it returns zero when
no positive breakpoint exists, including a zero-radius box containing the origin.
-/
noncomputable def generalizedCauchyPoint {ι : Type*} [Fintype ι]
    (l u : ι → EReal) (Δ : ℝ) (g d : EuclideanSpace ℝ ι)
    (H : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :
    ℝ × EuclideanSpace ℝ ι :=
  let b := fun i ↦ boxedCauchyBreakpoint (l i) (u i) Δ (d i)
  let times := (Finset.univ.image b).filter (fun t ↦ 0 < t)
  let v := d - cauchyFrozenDirection b d 0
  cauchyScan b g d H times.sort 0 0 v ⟪g, v⟫ (H v)

/-- **Algorithm 17.3.1** of [conn2000trust], terminal first interval. If every breakpoint $t_i$ is
at most $0$, then the corrected scan returns $(0, 0)$.

**Correction.** At zero slope the scan stops only with nonnegative outgoing curvature. Equal
breakpoints are grouped, the scan returns the endpoint of the last segment, and it returns zero when
no positive breakpoint exists, including a zero-radius box containing the origin.
-/
theorem generalizedCauchyPoint_eq_zero_of_no_positive_breakpoint {ι : Type*} [Fintype ι]
    (l u : ι → EReal) (Δ : ℝ) (g d : EuclideanSpace ℝ ι)
    (H : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (hb : ∀ i, boxedCauchyBreakpoint (l i) (u i) Δ (d i) ≤ 0) :
    generalizedCauchyPoint l u Δ g d H = (0, 0) := by
  unfold generalizedCauchyPoint
  have hempty : ((Finset.univ.image (fun i ↦ boxedCauchyBreakpoint (l i) (u i) Δ (d i))).filter
      (fun t ↦ 0 < t)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    obtain ⟨h, hpos⟩ := Finset.mem_filter.mp ht
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
    exact (hb i).not_gt hpos
  simp [hempty, cauchyScan]

/-- **Algorithm 17.3.1** of [conn2000trust], degenerate trust box. If $l_i \le 0 \le u_i$ for all
$i$, then the corrected scan with radius $\Delta = 0$ returns $(0, 0)$, even when the direction
$d$ is nonzero.

**Correction.** At zero slope the scan stops only with nonnegative outgoing curvature. Equal
breakpoints are grouped, the scan returns the endpoint of the last segment, and it returns zero when
no positive breakpoint exists, including a zero-radius box containing the origin.
-/
theorem generalizedCauchyPoint_zero_radius {ι : Type*} [Fintype ι]
    (l u : ι → EReal) (g d : EuclideanSpace ℝ ι)
    (H : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (hl : ∀ i, l i ≤ 0) (hu : ∀ i, 0 ≤ u i) :
    generalizedCauchyPoint l u 0 g d H = (0, 0) := by
  apply generalizedCauchyPoint_eq_zero_of_no_positive_breakpoint
  intro i
  simp [boxedCauchyBreakpoint, min_eq_right (hu i), max_eq_right (hl i)]

end ConnGouldToint.Chapter17
