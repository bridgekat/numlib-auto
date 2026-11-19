/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Numlib.Analysis.Calculus.ContDiffOnIcc

/-!
# Quarteroni, Sacco and Saleri, Section 12.1: A Model Problem

This module formalizes Section 12.1 of [quarteroni2000numerical], on the two-point boundary value
problem
$$-u''(x) = f(x), \quad 0 < x < 1, \qquad u(0) = u(1) = 0 \qquad (12.1)\text{–}(12.2).$$
For $u \in C^2([0, 1])$ the problem has the representation $u(x) = \int_0^1 G(x, s) f(s)\, ds$
(12.3) with the Green's function $G(x, s) = s(1 - x)$ for $s \le x$ and $G(x, s) = x(1 - s)$ for
$x \le s$ (12.4). The function $G$ is continuous, symmetric and nonnegative, it vanishes when $x$ or
$s$ is $0$ or $1$, and $\int_0^1 G(x, s)\, ds = x(1 - x)/2$. Hence for every $f \in C^0([0, 1])$ the
problem has a unique solution $u \in C^2([0, 1])$, given by (12.3). The solution is nonnegative when
$f$ is (the monotonicity property), and it satisfies the maximum principle
$\|u\|_\infty \le \|f\|_\infty / 8$ (12.5).

The section is classical calculus on $[0, 1]$. It uses the interval integrals and the fundamental
theorem of calculus of Mathlib, and no backbone module of numerical analysis. The Green's function
appears again in Section 12.2, where $h^{-1}$ times the inverse of the finite difference matrix is
$G$ at the nodes.

## Main definitions

* Equation (12.4), `QuarteroniSaccoSaleri.Chapter12.greenFunction`: the Green's function $G(x, s)$.
* Equations (12.1)–(12.2), `QuarteroniSaccoSaleri.Chapter12.IsSolution`: $u \in C^2([0, 1])$ solves
  the boundary value problem with datum $f$.

## Main results

* Section 12.1, `QuarteroniSaccoSaleri.Chapter12.greenFunction_symm`,
  `QuarteroniSaccoSaleri.Chapter12.greenFunction_nonneg`,
  `QuarteroniSaccoSaleri.Chapter12.greenFunction_zero_left`,
  `QuarteroniSaccoSaleri.Chapter12.greenFunction_one_left`,
  `QuarteroniSaccoSaleri.Chapter12.continuous_greenFunction` and
  `QuarteroniSaccoSaleri.Chapter12.integral_greenFunction`: the properties of $G$ listed after
  (12.4).
* Equation (12.3), `QuarteroniSaccoSaleri.Chapter12.equation_12_3_solution`:
  $x \mapsto \int_0^1 G(x, s) f(s)\, ds$ is a $C^2$ solution for every $f \in C^0([0, 1])$.
* Section 12.1, `QuarteroniSaccoSaleri.Chapter12.IsSolution.eqOn`: two $C^2$ solutions with the same
  datum agree on $[0, 1]$.
* Equation (12.3), `QuarteroniSaccoSaleri.Chapter12.equation_12_3`: every $C^2$ solution is given by
  (12.3).
* Section 12.1, `QuarteroniSaccoSaleri.Chapter12.equation_12_3_existsUnique`: existence and
  uniqueness of the solution.
* Section 12.1, `QuarteroniSaccoSaleri.Chapter12.IsSolution.contDiffOn_of_contDiffOn`:
  $f \in C^m([0, 1])$ implies $u \in C^{m+2}([0, 1])$.
* Section 12.1, `QuarteroniSaccoSaleri.Chapter12.equation_12_3_monotone`: the monotonicity property,
  $f \ge 0$ implies $u \ge 0$.
* Equation (12.5), `QuarteroniSaccoSaleri.Chapter12.equation_12_5_of_forall_le` and
  `QuarteroniSaccoSaleri.Chapter12.equation_12_5`: the maximum principle
  $\|u\|_\infty \le \|f\|_\infty / 8$.

## Proof outline

The source derives (12.3) by integrating (12.1) twice and fixing the two constants by (12.2). The
proof here goes the other way. It differentiates $v(x) = \int_0^1 G(x, s) f(s)\, ds$ twice, after
splitting the integral at the kink $s = x$ of $G$: $v(x) = (1 - x) \int_0^x s f(s)\, ds + x \int_x^1
(1 - s) f(s)\, ds$. Two $C^2$ solutions agree, because their difference has zero second derivative
and vanishes at both ends. Formula (12.3) combines the two facts. The general calculus lemmas that
the argument needs and Mathlib does not state are in `Numlib.Analysis.Calculus.ContDiffOnIcc`.

## Conventions

* $u \in C^2([0, 1])$ is `ContDiffOn ℝ 2 u (Icc 0 1)` for `u : ℝ → ℝ`, and $u''(x)$ at an interior
  point is `iteratedDeriv 2 u x`.
* A datum $f \in C^0([0, 1])$ is a function with `ContinuousOn f (Icc 0 1)`.
* The maximum norm $\|g\|_\infty = \max_{[0, 1]} |g|$ is `sSup ((fun s => |g s|) '' Icc 0 1)`, and a
  bound $\|u\|_\infty \le C$ is written `∀ x ∈ Icc 0 1, |u x| ≤ C`.

## Deviations from the source

* **Equation (12.4) and the Green's function properties** (generalization). The piecewise
  formula extends to all real arguments, with the same two branches. The symmetry and continuity
  declarations apply on the whole plane, and the endpoint values are stated on the corresponding
  half-lines.
* **Equation (12.5)** (generalization). `equation_12_5_of_forall_le` replaces the maximum of
  $|f|$ with any uniform bound $M$ on $[0,1]$ and gives the pointwise estimate $|u(x)|\leq M/8$.
* **Equation (12.5)** (reading). The source writes $f \in C^0(0, 1)$; continuity on the closed
  interval $[0, 1]$ is assumed throughout. See `QuarteroniSaccoSaleri.Chapter12.equation_12_5`.
-/

open Set Filter Topology intervalIntegral

namespace QuarteroniSaccoSaleri.Chapter12

/-! ### The Green's function (12.4) -/

/-- **Equation (12.4)** of [quarteroni2000numerical]. The **Green's function** of the boundary value
problem (12.1)–(12.2) is
$$G(x, s) = \begin{cases} s(1 - x), & 0 \le s \le x, \\ x(1 - s), & x \le s \le 1. \end{cases}$$

The two expressions agree at $s = x$. The definition uses the same two expressions on all of
$\mathbb{R} \times \mathbb{R}$: the first for $s \le x$, the second for $s > x$.

**Generalization.** The two formulas use only the relative order of $x$ and $s$, and continuity
and symmetry extend beyond the unit square. -/
noncomputable def greenFunction (x s : ℝ) : ℝ := if s ≤ x then s * (1 - x) else x * (1 - s)

variable {x s : ℝ}

/-- The first branch of the Green's function (12.4): $G(x, s) = s(1 - x)$ for $s \le x$.

**Generalization.** The two formulas use only the relative order of $x$ and $s$, and continuity
and symmetry extend beyond the unit square. -/
theorem greenFunction_of_le (h : s ≤ x) : greenFunction x s = s * (1 - x) := by
  simp [greenFunction, h]

/-- The second branch of the Green's function (12.4): $G(x, s) = x(1 - s)$ for $x \le s$.

**Generalization.** The two formulas use only the relative order of $x$ and $s$, and continuity
and symmetry extend beyond the unit square. -/
theorem greenFunction_of_ge (h : x ≤ s) : greenFunction x s = x * (1 - s) := by
  unfold greenFunction
  split_ifs with h'
  · rw [le_antisymm h' h]
  · rfl

/-- The Green's function (12.4) in one formula: $G(x, s) = \min(x, s) \, (1 - \max(x, s))$ for all
$x, s \in \mathbb{R}$.

**Generalization.** The two formulas use only the relative order of $x$ and $s$, and continuity
and symmetry extend beyond the unit square. -/
theorem greenFunction_eq_min_mul (x s : ℝ) : greenFunction x s = min x s * (1 - max x s) := by
  rcases le_total s x with h | h
  · rw [greenFunction_of_le h, min_eq_right h, max_eq_left h]
  · rw [greenFunction_of_ge h, min_eq_left h, max_eq_right h]

/-- **Section 12.1** of [quarteroni2000numerical], symmetry of the Green's function. For all
$x, s \in \mathbb{R}$, $G(x, s) = G(s, x)$.

**Generalization.** The two formulas use only the relative order of $x$ and $s$, and continuity
and symmetry extend beyond the unit square. -/
theorem greenFunction_symm (x s : ℝ) : greenFunction x s = greenFunction s x := by
  rw [greenFunction_eq_min_mul, greenFunction_eq_min_mul, min_comm, max_comm]

/-- **Section 12.1** of [quarteroni2000numerical], nonnegativity of the Green's function. For
$x, s \in [0, 1]$, $G(x, s) \ge 0$. -/
theorem greenFunction_nonneg (hx : x ∈ Icc 0 1) (hs : s ∈ Icc 0 1) : 0 ≤ greenFunction x s := by
  rw [greenFunction_eq_min_mul]
  exact mul_nonneg (le_min hx.1 hs.1) (sub_nonneg.2 (max_le hx.2 hs.2))

/-- **Section 12.1** of [quarteroni2000numerical], the Green's function at $x = 0$. For $s \ge 0$,
$G(0, s) = 0$.

**Generalization.** The endpoint identity holds on a half-line of the other argument by the
same piecewise formula. -/
theorem greenFunction_zero_left (hs : 0 ≤ s) : greenFunction 0 s = 0 := by
  rw [greenFunction_of_ge hs, zero_mul]

/-- **Section 12.1** of [quarteroni2000numerical], the Green's function at $x = 1$. For $s \le 1$,
$G(1, s) = 0$.

**Generalization.** The endpoint identity holds on a half-line of the other argument by the
same piecewise formula. -/
theorem greenFunction_one_left (hs : s ≤ 1) : greenFunction 1 s = 0 := by
  rw [greenFunction_of_le hs, sub_self, mul_zero]

/-- The Green's function (12.4) at $s = 0$: for $x \ge 0$, $G(x, 0) = 0$.

**Generalization.** The endpoint identity holds on a half-line of the other argument by the
same piecewise formula. -/
theorem greenFunction_zero_right (hx : 0 ≤ x) : greenFunction x 0 = 0 := by
  rw [greenFunction_symm, greenFunction_zero_left hx]

/-- The Green's function (12.4) at $s = 1$: for $x \le 1$, $G(x, 1) = 0$.

**Generalization.** The endpoint identity holds on a half-line of the other argument by the
same piecewise formula. -/
theorem greenFunction_one_right (hx : x ≤ 1) : greenFunction x 1 = 0 := by
  rw [greenFunction_symm, greenFunction_one_left hx]

/-- **Section 12.1** of [quarteroni2000numerical], continuity of the Green's function. The function
$(x, s) \mapsto G(x, s)$ is continuous on $\mathbb{R} \times \mathbb{R}$, because its two
branches agree on the diagonal $s = x$.

**Generalization.** The two formulas use only the relative order of $x$ and $s$, and continuity
and symmetry extend beyond the unit square. -/
theorem continuous_greenFunction : Continuous fun p : ℝ × ℝ => greenFunction p.1 p.2 := by
  unfold greenFunction
  exact Continuous.if_le (by fun_prop) (by fun_prop) continuous_snd continuous_fst
    fun p hp => by rw [hp]

/-- For fixed $x$, the Green's function $s \mapsto G(x, s)$ of (12.4) is continuous.

**Generalization.** The two formulas use only the relative order of $x$ and $s$, and continuity
and symmetry extend beyond the unit square. -/
theorem continuous_greenFunction_right (x : ℝ) : Continuous (greenFunction x) :=
  continuous_greenFunction.comp (continuous_const.prodMk continuous_id)

/-- For fixed $s$, the Green's function $x \mapsto G(x, s)$ of (12.4) is continuous.

**Generalization.** The two formulas use only the relative order of $x$ and $s$, and continuity
and symmetry extend beyond the unit square. -/
theorem continuous_greenFunction_left (s : ℝ) : Continuous fun x => greenFunction x s :=
  continuous_greenFunction.comp (continuous_id.prodMk continuous_const)

/-- **Section 12.1** of [quarteroni2000numerical], the integral of the Green's function. For
$x \in [0, 1]$,
$$\int_0^1 G(x, s)\, ds = \frac{x(1 - x)}{2}.$$
-/
theorem integral_greenFunction (hx : x ∈ Icc 0 1) :
    ∫ s in (0 : ℝ)..1, greenFunction x s = x * (1 - x) / 2 := by
  have hc : Continuous (greenFunction x) := continuous_greenFunction_right x
  rw [← integral_add_adjacent_intervals (hc.intervalIntegrable 0 x) (hc.intervalIntegrable x 1)]
  have h1 : ∫ s in (0 : ℝ)..x, greenFunction x s = ∫ s in (0 : ℝ)..x, s * (1 - x) :=
    integral_congr fun s hs => by
      rw [uIcc_of_le hx.1] at hs
      exact greenFunction_of_le hs.2
  have h2 : ∫ s in x..1, greenFunction x s = ∫ s in x..1, x * (1 - s) :=
    integral_congr fun s hs => by
      rw [uIcc_of_le hx.2] at hs
      exact greenFunction_of_ge hs.1
  rw [h1, h2, integral_mul_const, integral_id, integral_const_mul,
    integral_sub intervalIntegrable_const (continuous_id'.intervalIntegrable _ _), integral_const,
    integral_id, smul_eq_mul]
  ring

/-! ### The boundary value problem (12.1)–(12.2) -/

/-- **Equations (12.1)–(12.2)** of [quarteroni2000numerical]. A function $u \in C^2([0, 1])$ is a
**solution of the boundary value problem** with datum $f$ if
$$-u''(x) = f(x) \quad \text{for } 0 < x < 1 \quad (12.1), \qquad u(0) = u(1) = 0 \quad
  (12.2).$$
-/
structure IsSolution (f u : ℝ → ℝ) : Prop where
  /-- The solution is $C^2$ on $[0, 1]$. -/
  contDiffOn : ContDiffOn ℝ 2 u (Icc 0 1)
  /-- Equation (12.1): $-u''(x) = f(x)$ for $0 < x < 1$. -/
  equation_12_1 : ∀ x ∈ Ioo 0 1, -iteratedDeriv 2 u x = f x
  /-- The left boundary condition of (12.2): $u(0) = 0$. -/
  equation_12_2_left : u 0 = 0
  /-- The right boundary condition of (12.2): $u(1) = 0$. -/
  equation_12_2_right : u 1 = 0

/-! ### The representation formula (12.3) -/

variable {f u : ℝ → ℝ}

/-- The integral of (12.3), split at the kink $s = x$ of the Green's function. Let
$f \in C^0([0, 1])$ and $x \in [0, 1]$. Then
$$\int_0^1 G(x, s) f(s)\, ds = (1 - x) \int_0^x s f(s)\, ds + x \int_x^1 (1 - s) f(s)\, ds.$$
-/
theorem integral_greenFunction_mul_eq (hf : ContinuousOn f (Icc 0 1)) (hx : x ∈ Icc 0 1) :
    ∫ s in (0 : ℝ)..1, greenFunction x s * f s
      = (1 - x) * (∫ s in (0 : ℝ)..x, s * f s) + x * ∫ s in x..1, (1 - s) * f s := by
  have hcont : ContinuousOn (fun s => greenFunction x s * f s) (Icc 0 1) :=
    (continuous_greenFunction_right x).continuousOn.mul hf
  rw [← integral_add_adjacent_intervals
    ((hcont.mono (Icc_subset_Icc le_rfl hx.2)).intervalIntegrable_of_Icc hx.1)
    ((hcont.mono (Icc_subset_Icc hx.1 le_rfl)).intervalIntegrable_of_Icc hx.2)]
  congr 1
  · rw [← integral_const_mul]
    refine integral_congr fun s hs => ?_
    rw [uIcc_of_le hx.1] at hs
    rw [greenFunction_of_le hs.2]
    ring
  · rw [← integral_const_mul]
    refine integral_congr fun s hs => ?_
    rw [uIcc_of_le hx.2] at hs
    rw [greenFunction_of_ge hs.1]
    ring

/-- **Equation (12.3)** of [quarteroni2000numerical], existence. For every $f \in C^0([0, 1])$, the
function
$$u(x) = \int_0^1 G(x, s) f(s)\, ds$$
is a solution in $C^2([0, 1])$ of the boundary value problem (12.1)–(12.2).

After the split at $s = x$ (`QuarteroniSaccoSaleri.Chapter12.integral_greenFunction_mul_eq`),
the fundamental theorem of calculus gives $u'(x) = \int_x^1 (1 - s) f(s)\, ds - \int_0^x s
f(s)\, ds$ and then $u''(x) = -(1 - x) f(x) - x f(x) = -f(x)$, at every point of $[0, 1]$ as a
derivative within the interval. -/
theorem equation_12_3_solution (hf : ContinuousOn f (Icc 0 1)) :
    IsSolution f fun x => ∫ s in (0 : ℝ)..1, greenFunction x s * f s := by
  -- the two primitives and their derivatives within `[0, 1]`
  have hgA : ContinuousOn (fun s => s * f s) (Icc 0 1) := continuousOn_id.mul hf
  have hgB : ContinuousOn (fun s => (1 - s) * f s) (Icc 0 1) :=
    (continuousOn_const.sub continuousOn_id).mul hf
  have hA : ∀ x ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun x => ∫ s in (0 : ℝ)..x, s * f s) (x * f x) (Icc 0 1) x := by
    intro x hx
    have : Fact (x ∈ Icc (0 : ℝ) 1) := ⟨hx⟩
    exact integral_hasDerivWithinAt_right (s := Icc 0 1) (t := Icc 0 1)
      ((hgA.mono (Icc_subset_Icc le_rfl hx.2)).intervalIntegrable_of_Icc hx.1)
      (hgA.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x) (hgA x hx)
  have hB : ∀ x ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun x => ∫ s in x..1, (1 - s) * f s) (-((1 - x) * f x)) (Icc 0 1) x := by
    intro x hx
    have : Fact (x ∈ Icc (0 : ℝ) 1) := ⟨hx⟩
    exact integral_hasDerivWithinAt_left (s := Icc 0 1) (t := Icc 0 1)
      ((hgB.mono (Icc_subset_Icc hx.1 le_rfl)).intervalIntegrable_of_Icc hx.2)
      (hgB.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x) (hgB x hx)
  -- the first derivative of `u`
  have hu₁ : ∀ x ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun x => ∫ s in (0 : ℝ)..1, greenFunction x s * f s)
        ((∫ s in x..1, (1 - s) * f s) - ∫ s in (0 : ℝ)..x, s * f s) (Icc 0 1) x := by
    intro x hx
    have h := (((hasDerivWithinAt_id x (Icc 0 1)).const_sub 1).mul (hA x hx)).add
      ((hasDerivWithinAt_id x (Icc 0 1)).mul (hB x hx))
    refine (h.congr_deriv ?_).congr (fun y hy => integral_greenFunction_mul_eq hf hy)
      (integral_greenFunction_mul_eq hf hx)
    simp only [id]
    ring
  -- the second derivative of `u`
  have hu₂ : ∀ x ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun x => (∫ s in x..1, (1 - s) * f s) - ∫ s in (0 : ℝ)..x, s * f s)
        (-f x) (Icc 0 1) x := by
    intro x hx
    refine ((hB x hx).sub (hA x hx)).congr_deriv ?_
    ring
  refine ⟨contDiffOn_two_of_hasDerivWithinAt (uniqueDiffOn_Icc zero_lt_one) hu₁ hu₂ hf.neg,
    fun x hx => ?_, ?_, ?_⟩
  · rw [iteratedDeriv_two_eq_of_hasDerivWithinAt hu₁ hu₂ hx, neg_neg]
  · rw [integral_congr (g := fun _ => (0 : ℝ)) fun s hs => ?_, integral_zero]
    rw [uIcc_of_le zero_le_one] at hs
    rw [greenFunction_zero_left hs.1, zero_mul]
  · rw [integral_congr (g := fun _ => (0 : ℝ)) fun s hs => ?_, integral_zero]
    rw [uIcc_of_le zero_le_one] at hs
    rw [greenFunction_one_left hs.2, zero_mul]

/-- **Section 12.1** of [quarteroni2000numerical], uniqueness for (12.1)–(12.2). Let $u$ and $v$ be
solutions of the boundary value problem with the same datum $f$. Then $u = v$ on $[0, 1]$.

The difference $u - v$ has zero second derivative in $(0, 1)$ and vanishes at both ends. -/
theorem IsSolution.eqOn {v : ℝ → ℝ} (hu : IsSolution f u) (hv : IsSolution f v) :
    EqOn u v (Icc 0 1) := by
  have hcu := hu.contDiffOn.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) one_le_two
  have hcv := hv.contDiffOn.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) one_le_two
  have key := eqOn_zero_of_hasDerivAt_zero zero_le_one
    (w := fun y => u y - v y) (w₁ := fun y => derivWithin u (Icc 0 1) y - derivWithin v (Icc 0 1) y)
    (hu.contDiffOn.continuousOn.sub hv.contDiffOn.continuousOn) (hcu.sub hcv)
    (fun y hy => (hasDerivAt_of_contDiffOn_two hu.contDiffOn hy).1.sub
      (hasDerivAt_of_contDiffOn_two hv.contDiffOn hy).1)
    (fun y hy => ((hasDerivAt_of_contDiffOn_two hu.contDiffOn hy).2.sub
      (hasDerivAt_of_contDiffOn_two hv.contDiffOn hy).2).congr_deriv (by
        rw [neg_eq_iff_eq_neg.1 (hu.equation_12_1 y hy), neg_eq_iff_eq_neg.1
          (hv.equation_12_1 y hy), sub_self]))
    (by rw [hu.equation_12_2_left, hv.equation_12_2_left, sub_zero])
    (by rw [hu.equation_12_2_right, hv.equation_12_2_right, sub_zero])
  intro y hy
  exact sub_eq_zero.1 (key hy)

/-- **Equation (12.3)** of [quarteroni2000numerical]. Let $f \in C^0([0, 1])$, and let $u$ be a
solution of the boundary value problem (12.1)–(12.2) with datum $f$. Then for every
$x \in [0, 1]$
$$u(x) = \int_0^1 G(x, s) f(s)\, ds,$$
with the Green's function $G$ of (12.4).

The source integrates (12.1) twice and fixes the constants by (12.2). Here the right-hand side
is a solution (`QuarteroniSaccoSaleri.Chapter12.equation_12_3_solution`), and solutions are
unique (`QuarteroniSaccoSaleri.Chapter12.IsSolution.eqOn`). -/
theorem equation_12_3 (hf : ContinuousOn f (Icc 0 1)) (hu : IsSolution f u) (hx : x ∈ Icc 0 1) :
    u x = ∫ s in (0 : ℝ)..1, greenFunction x s * f s :=
  hu.eqOn (equation_12_3_solution hf) hx

/-- **Section 12.1** of [quarteroni2000numerical], existence and uniqueness. For every
$f \in C^0([0, 1])$ there is a solution $u \in C^2([0, 1])$ of the boundary value problem
(12.1)–(12.2) with datum $f$, it is given by the representation (12.3) on $[0, 1]$, and every
solution agrees with it on $[0, 1]$.

Uniqueness holds on $[0, 1]$, the only place where a solution is constrained. -/
theorem equation_12_3_existsUnique (hf : ContinuousOn f (Icc 0 1)) :
    ∃ u : ℝ → ℝ, IsSolution f u ∧
      (∀ x ∈ Icc 0 1, u x = ∫ s in (0 : ℝ)..1, greenFunction x s * f s) ∧
      ∀ v, IsSolution f v → EqOn v u (Icc 0 1) :=
  ⟨_, equation_12_3_solution hf, fun _ _ => rfl, fun _ hv => hv.eqOn (equation_12_3_solution hf)⟩

/-- **Section 12.1** of [quarteroni2000numerical], regularity. Let $m \in \mathbb{N}$, let $u$ be a
solution of the boundary value problem (12.1)–(12.2) with datum $f$, and let
$f \in C^m([0, 1])$. Then $u \in C^{m+2}([0, 1])$.

The second derivative of $u$ within $[0, 1]$ agrees with $-f$ in the interior by (12.1), hence
on the closed interval by continuity, and $u \in C^{m+2}$ means $u'' \in C^m$. -/
theorem IsSolution.contDiffOn_of_contDiffOn {m : ℕ} (hu : IsSolution f u)
    (hf : ContDiffOn ℝ m f (Icc 0 1)) : ContDiffOn ℝ (m + 2) u (Icc 0 1) := by
  have hs : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have h₂ := hu.contDiffOn
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiffOn_succ_iff_derivWithin hs] at h₂
  obtain ⟨hdiff, -, h₁⟩ := h₂
  rw [contDiffOn_one_iff_derivWithin hs] at h₁
  obtain ⟨hdiff₁, hcont₂⟩ := h₁
  -- the second derivative within `[0, 1]` is `-f` on all of `[0, 1]`
  have heq : EqOn (derivWithin (derivWithin u (Icc 0 1)) (Icc 0 1)) (fun x => -f x) (Icc 0 1) := by
    refine EqOn.of_subset_closure (fun x hx => ?_) hcont₂ hf.continuousOn.neg
      Ioo_subset_Icc_self (by rw [closure_Ioo zero_ne_one])
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2),
      (hasDerivAt_of_contDiffOn_two hu.contDiffOn hx).2.deriv,
      neg_eq_iff_eq_neg.1 (hu.equation_12_1 x hx)]
  rw [show ((m : WithTop ℕ∞) + 2) = (m + 1) + 1 by rw [add_assoc, one_add_one_eq_two],
    contDiffOn_succ_iff_derivWithin hs]
  refine ⟨hdiff, fun h => absurd h (by simp), ?_⟩
  rw [contDiffOn_succ_iff_derivWithin hs]
  exact ⟨hdiff₁, fun h => absurd h (by simp), hf.neg.congr fun x hx => heq hx⟩

/-! ### The monotonicity property and the maximum principle (12.5) -/

/-- **Section 12.1** of [quarteroni2000numerical], the monotonicity property. Let
$f \in C^0([0, 1])$ with $f(s) \ge 0$ for $s \in [0, 1]$, and let $u$ be the solution of the
boundary value problem (12.1)–(12.2) with datum $f$. Then $u(x) \ge 0$ for every $x \in [0, 1]$.

The proof uses (12.3) and $G(x, s) \ge 0$ for $x, s \in [0, 1]$. -/
theorem equation_12_3_monotone (hf : ContinuousOn f (Icc 0 1)) (hf0 : ∀ s ∈ Icc 0 1, 0 ≤ f s)
    (hu : IsSolution f u) : ∀ x ∈ Icc 0 1, 0 ≤ u x := by
  intro x hx
  rw [equation_12_3 hf hu hx]
  exact integral_nonneg zero_le_one fun s hs => mul_nonneg (greenFunction_nonneg hx hs) (hf0 s hs)

/-- **Equation (12.5)** of [quarteroni2000numerical], with an explicit bound. Let
$f \in C^0([0, 1])$ with $|f(s)| \le M$ for $s \in [0, 1]$, and let $u$ be the solution of the
boundary value problem (12.1)–(12.2) with datum $f$. Then $|u(x)| \le M / 8$ for every
$x \in [0, 1]$.

Because $G \ge 0$, $|u(x)| \le \int_0^1 G(x, s) |f(s)|\, ds \le M \int_0^1 G(x, s)\, ds = M
x(1 - x)/2 \le M/8$.

**Reading.** Assumes continuity on the closed interval and uses any bound $M$ for $|f|$,
yielding $|u(x)|\leq M/8$. -/
theorem equation_12_5_of_forall_le (hf : ContinuousOn f (Icc 0 1)) (hu : IsSolution f u) {M : ℝ}
    (hM : ∀ s ∈ Icc 0 1, |f s| ≤ M) : ∀ x ∈ Icc 0 1, |u x| ≤ M / 8 := by
  intro x hx
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  have hcont : ContinuousOn (fun s => greenFunction x s * f s) (Icc 0 1) :=
    (continuous_greenFunction_right x).continuousOn.mul hf
  rw [equation_12_3 hf hu hx]
  calc |∫ s in (0 : ℝ)..1, greenFunction x s * f s|
      ≤ ∫ s in (0 : ℝ)..1, |greenFunction x s * f s| := abs_integral_le_integral_abs zero_le_one
    _ ≤ ∫ s in (0 : ℝ)..1, greenFunction x s * M := by
        refine integral_mono_on zero_le_one (hcont.abs.intervalIntegrable_of_Icc zero_le_one)
          (((continuous_greenFunction_right x).continuousOn.mul
            continuousOn_const).intervalIntegrable_of_Icc zero_le_one) fun s hs => ?_
        rw [abs_mul, abs_of_nonneg (greenFunction_nonneg hx hs)]
        exact mul_le_mul_of_nonneg_left (hM s hs) (greenFunction_nonneg hx hs)
    _ = x * (1 - x) / 2 * M := by rw [integral_mul_const, integral_greenFunction hx]
    _ ≤ M / 8 := by nlinarith [sq_nonneg (2 * x - 1), hM0]

/-- **Equation (12.5)** of [quarteroni2000numerical] (maximum principle). Let $f \in C^0([0, 1])$,
and let $u$ be the solution of the boundary value problem (12.1)–(12.2) with datum $f$. Then
$$\|u\|_\infty \le \frac{1}{8} \|f\|_\infty, \qquad \|g\|_\infty = \max_{0 \le x \le 1}
  |g(x)|.$$
That is, $|u(x)| \le \frac{1}{8} \max_{[0, 1]} |f|$ for every $x \in [0, 1]$.

**Reading.** The source writes $f \in C^0(0, 1)$. The statement assumes continuity on the closed
interval $[0, 1]$, which is what (12.3) uses and what makes $\|f\|_\infty$ finite. -/
theorem equation_12_5 (hf : ContinuousOn f (Icc 0 1)) (hu : IsSolution f u) :
    ∀ x ∈ Icc 0 1, |u x| ≤ (1 / 8) * sSup ((fun s => |f s|) '' Icc 0 1) := by
  have hbdd : BddAbove ((fun s => |f s|) '' Icc 0 1) :=
    (isCompact_Icc.image_of_continuousOn hf.abs).bddAbove
  intro x hx
  rw [one_div_mul_eq_div]
  exact equation_12_5_of_forall_le hf hu (fun s hs => le_csSup hbdd (mem_image_of_mem _ hs)) x hx

end QuarteroniSaccoSaleri.Chapter12
