/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Approximation.BrokenPolynomial
import Numlib.Approximation.SobolevInterpolation
import Numlib.Approximation.MarkovInequality

/-!
# Interpolation and projection in the broken polynomial space

This file gives the approximation tools for the error analysis of Galerkin methods on the broken
polynomial space `BrokenPolynomial x r` of a partition $x_0 < \dots < x_n$
(`Numlib.Approximation.BrokenPolynomial`). This space is the trial space of the continuous and
discontinuous Galerkin methods for the transport equation (§13.10 of [quarteroni2000numerical],
formalized in `Numlib.Variational.Evolution` and `Numlib.Variational.SpaceTimeGalerkin`). Write
$I_i = [x_i, x_{i+1}]$ for the panels, $v_i$ for the polynomial of a broken polynomial $v$ on $I_i$,
and $h$ and $h_{\min}$ for an upper and a lower bound of the panel lengths.

The $L^2(x_0, x_n)$ norm of a function that is defined panel by panel is the panel sum
$\bigl(\sum_i \int_{I_i} \cdots\bigr)^{1/2}$. The file proves the Cauchy–Schwarz and Minkowski
inequalities for such sums. It defines the pairing $\langle g, v \rangle = \sum_i \int_{I_i} g\,
v_i$ of a function with a broken polynomial, the panelwise Lagrange interpolant $\Pi_h f$ at a node
system, and the $L^2$ projection $P g$ onto the broken space. For $U \in H^{r+1}(x_0, x_n)$ it
proves the interpolation estimates $h^{r+1} |U|_{H^{r+1}}$ in $L^2$ and $h^r |U|_{H^{r+1}}$ for the
derivative, the same $L^2$ estimate for the projection, and the derivative estimate $h^r (1 + 4 r
(r + 1) h / h_{\min}) |U|_{H^{r+1}}$ for the projection. A trace inequality summed over the panels
turns these into the $h^{r+1/2}$ bound on the error at the nodes that the error estimate of the
discontinuous Galerkin method needs.

## Main definitions

* `BrokenPolynomial.pairing`, `BrokenPolynomial.pairingL`: the pairing $\langle g, v \rangle$, which
  is the source functional of a Galerkin method with datum $g$, and the pairing as a continuous
  linear functional.
* `BrokenPolynomial.IsNodes`, `BrokenPolynomial.IsLagrangeNodes`: a node system ($r + 1$ distinct
  nodes in each panel), and a node system that contains both endpoints of each panel.
* `BrokenPolynomial.ofValuesₗ`: the broken polynomial that interpolates given nodal values, as a
  linear map in the values.
* `BrokenPolynomial.interp`: the panelwise Lagrange interpolant $\Pi_h f$.
* `BrokenPolynomial.proj`: the $L^2(x_0, x_n)$ projection $P g$ onto the broken space.

## Main results

* `BrokenPolynomial.integral_eq_sum_panels`: an integral over $[x_0, x_n]$ is the sum of the panel
  integrals.
* `BrokenPolynomial.sum_integral_mul_le_sqrt_mul_sqrt`,
  `BrokenPolynomial.sqrt_sum_integral_add_sq_le`: the Cauchy–Schwarz and Minkowski inequalities for
  panel sums.
* `BrokenPolynomial.abs_pairing_le`, `BrokenPolynomial.norm_pairingL_le`: the pairing is bounded by
  the $L^2$ norm of $g$.
* `BrokenPolynomial.sqrt_sum_integral_sub_sq_le`: the triangle inequality between a function and two
  broken polynomials.
* `BrokenPolynomial.interp_mem_continuous`, `BrokenPolynomial.traceRight_interp`,
  `BrokenPolynomial.traceLeft_interp_succ`: at a Lagrange node system, the interpolant is continuous
  and takes the interpolated values at the nodes of the partition.
* `BrokenPolynomial.sum_integral_sq_iteratedDeriv_sub_interp_le`: the interpolation estimate with
  constant $1$, for a $C^r$ function whose $r$-th derivative is the integral of a square integrable
  function.
* `BrokenPolynomial.sum_integral_sq_sub_interp_le_seminorm`,
  `BrokenPolynomial.sum_integral_sq_deriv_sub_interp_le_seminorm`: the interpolation estimates
  $h^{r+1} |U|_{H^{r+1}}$ in $L^2$ and $h^r |U|_{H^{r+1}}$ for the weak derivative, for every
  $r \ge 0$.
* `BrokenPolynomial.integral_derivative_sq_le_panel`,
  `BrokenPolynomial.sum_integral_sq_derivative_le`: the Markov inequality $\|p'\|_{L^2(I)} \le 2 r
  (r + 1) |I|^{-1} \|p\|_{L^2(I)}$ for a polynomial $p$ of degree at most $r$ on a panel $I$, and
  its broken form.
* `BrokenPolynomial.sum_integral_sub_proj_mul_eval_eq_zero`,
  `BrokenPolynomial.integral_sub_proj_mul_eq_zero`: the projection error is orthogonal to the broken
  space, and on each panel to the polynomials of degree at most $r$.
* `BrokenPolynomial.sum_integral_sq_sub_proj_le`: the projection is the best approximation in the
  broken space.
* `BrokenPolynomial.sqrt_sum_integral_sq_sub_proj_le_seminorm`,
  `BrokenPolynomial.sqrt_sum_integral_sq_deriv_sub_proj_le_seminorm`: the $L^2$ error
  $h^{r+1} |U|_{H^{r+1}}$ and the derivative error $h^r (1 + 4 r (r + 1) h / h_{\min})
  |U|_{H^{r+1}}$ of the projection.
* `BrokenPolynomial.sum_mul_sq_sub_eval_le`: the trace inequality `sq_le_of_sub_eq_integral` summed
  over the panels, which gives the bound on the error at the nodes.

## Implementation notes

* The interpolant is linear in the function through `BrokenPolynomial.ofValuesₗ`, a linear map on
  the finite-dimensional space of nodal values. This is what makes the interpolant of a
  time-dependent function differentiable in time, with the interpolant of the time derivative as its
  derivative.
* The interpolation estimates are the panel estimates of
  `Numlib.Approximation.SobolevInterpolation`, summed over the panels of a broken space, which are
  indexed by `Fin n`. The Markov inequality on a panel is the inequality on $[-1, 1]$ of
  `Numlib.Approximation.MarkovInequality`, transported to the panel.
* The projection `BrokenPolynomial.proj` is the Riesz representative of the pairing. For a function
  that is not integrable on $[x_0, x_n]$ it is $0$.
* A function in $H^{r+1}(x_0, x_n)$ is an element `U` of
  `SobolevInterval (r + 1) (x 0) (x (Fin.last n))`, given together with a representative `f` that is
  continuous on $[x_0, x_n]$: `SobolevInterval.fn U` equals `f` almost everywhere on $(x_0, x_n)$.
  The seminorm $|U|_{H^{r+1}}$ is `SobolevInterval.seminorm`, and the weak derivative $U'$ is
  `SobolevInterval.deriv U 1`.
-/

open Polynomial MeasureTheory intervalIntegral Set
open scoped Interval RealInnerProductSpace

noncomputable section

namespace BrokenPolynomial

variable {n : ℕ} {x : Fin (n + 1) → ℝ} {r : ℕ}

/-! ### Panels of a monotone partition -/

/-- For a nondecreasing partition, the closed interval between $x_i$ and $x_{i+1}$ lies in the
closed interval between $x_0$ and $x_n$. -/
theorem uIcc_panel_subset (hx : Monotone x) (i : Fin n) :
    [[x i.castSucc, x i.succ]] ⊆ [[x 0, x (Fin.last n)]] := by
  rw [uIcc_of_le (hx (Fin.castSucc_lt_succ (i := i)).le), uIcc_of_le (hx (Fin.zero_le _))]
  exact Icc_subset_Icc (hx (Fin.zero_le _)) (hx (Fin.le_last _))

/-- For a nondecreasing partition, the closed panel $[x_i, x_{i+1}]$ lies in $[x_0, x_n]$. -/
theorem Icc_panel_subset (hx : Monotone x) (i : Fin n) :
    Icc (x i.castSucc) (x i.succ) ⊆ Icc (x 0) (x (Fin.last n)) :=
  Icc_subset_Icc (hx (Fin.zero_le _)) (hx (Fin.le_last _))

/-- For a nondecreasing partition, a function that is integrable on $[x_0, x_n]$ is integrable on
every panel. -/
theorem intervalIntegrable_panel (hx : Monotone x) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume (x 0) (x (Fin.last n))) (i : Fin n) :
    IntervalIntegrable g volume (x i.castSucc) (x i.succ) :=
  hg.mono_set (uIcc_panel_subset hx i)

/-- For a nondecreasing partition, a function $g$ integrable on $[x_0, x_n]$ and a broken polynomial
$v$, the product $g\, v_i$ is integrable on the panel $I_i$. -/
theorem intervalIntegrable_mul_eval_panel (hx : Monotone x) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume (x 0) (x (Fin.last n))) (v : BrokenPolynomial x r)
    (i : Fin n) :
    IntervalIntegrable (fun s => g s * (v i).eval s) volume (x i.castSucc) (x i.succ) :=
  (intervalIntegrable_panel hx hg i).mul_continuousOn (v i).continuous.continuousOn

/-- For a nondecreasing partition, a function $g$ integrable on $[x_0, x_n]$ and a broken polynomial
$v$, the difference $g - v_i$ is integrable on the panel $I_i$. -/
theorem intervalIntegrable_sub_eval_panel (hx : Monotone x) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume (x 0) (x (Fin.last n))) (v : BrokenPolynomial x r)
    (i : Fin n) :
    IntervalIntegrable (fun s => g s - (v i).eval s) volume (x i.castSucc) (x i.succ) :=
  (intervalIntegrable_panel hx hg i).sub ((v i).continuous.intervalIntegrable _ _)

/-- For a nondecreasing partition, a function $g$ with $g$ and $g^2$ integrable on $[x_0, x_n]$, and
a broken polynomial $v$, the function $(g - v_i)^2$ is integrable on the panel $I_i$. -/
theorem intervalIntegrable_sub_eval_sq_panel (hx : Monotone x) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume (x 0) (x (Fin.last n)))
    (hg2 : IntervalIntegrable (fun s => g s ^ 2) volume (x 0) (x (Fin.last n)))
    (v : BrokenPolynomial x r) (i : Fin n) :
    IntervalIntegrable (fun s => (g s - (v i).eval s) ^ 2) volume (x i.castSucc) (x i.succ) := by
  have : (fun s => (g s - (v i).eval s) ^ 2)
      = fun s => g s ^ 2 - 2 * (g s * (v i).eval s) + (v i).eval s ^ 2 := by
    funext s; ring
  rw [this]
  exact ((intervalIntegrable_panel hx hg2 i).sub
    ((intervalIntegrable_mul_eval_panel hx hg v i).const_mul 2)).add
    (((v i).continuous.pow 2).intervalIntegrable _ _)

/-- **An integral over $[x_0, x_n]$ is the sum of the panel integrals**: for a nondecreasing
partition and a function $g$ integrable on $[x_0, x_n]$,
$$\int_{x_0}^{x_n} g = \sum_{i=0}^{n-1} \int_{x_i}^{x_{i+1}} g.$$
-/
theorem integral_eq_sum_panels (hx : Monotone x) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume (x 0) (x (Fin.last n))) :
    ∫ s in x 0..x (Fin.last n), g s = ∑ i : Fin n, ∫ s in x i.castSucc..x i.succ, g s := by
  set a : ℕ → ℝ := fun j => x ⟨min j n, by omega⟩ with ha
  have ha0 : a 0 = x 0 := by simp [ha]
  have han : a n = x (Fin.last n) := by simp [ha, Fin.last]
  have hcast : ∀ i : Fin n, a i = x i.castSucc := fun i => by
    simp only [ha]
    congr 1
    exact Fin.ext (min_eq_left i.2.le)
  have hsucc : ∀ i : Fin n, a (i + 1) = x i.succ := fun i => by
    simp only [ha]
    congr 1
    exact Fin.ext (min_eq_left i.2)
  have hint : ∀ j < n, IntervalIntegrable g volume (a j) (a (j + 1)) := fun j hj => by
    rw [show a j = x (⟨j, hj⟩ : Fin n).castSucc from hcast ⟨j, hj⟩,
      show a (j + 1) = x (⟨j, hj⟩ : Fin n).succ from hsucc ⟨j, hj⟩]
    exact intervalIntegrable_panel hx hg _
  rw [← ha0, ← han, ← sum_integral_adjacent_intervals hint, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hcast i, hsucc i]

/-! ### Cauchy–Schwarz and Minkowski for panel sums -/

/-- **The Cauchy–Schwarz inequality for panel sums.** Let the partition be nondecreasing, and let
$f_i, g_i : \mathbb{R} \to \mathbb{R}$, $i = 0, \dots, n - 1$, be functions such that $f_i$,
$f_i^2$, $g_i$ and $g_i^2$ are integrable on $I_i$. Then
$$\sum_{i=0}^{n-1} \int_{I_i} f_i\, g_i \le \Bigl(\sum_{i=0}^{n-1} \int_{I_i} f_i^2\Bigr)^{1/2}
  \Bigl(\sum_{i=0}^{n-1} \int_{I_i} g_i^2\Bigr)^{1/2}.$$
The proof applies the Cauchy–Schwarz inequality on each panel, and then the discrete
Cauchy–Schwarz inequality over the panels. -/
theorem sum_integral_mul_le_sqrt_mul_sqrt (hx : Monotone x) {f g : Fin n → ℝ → ℝ}
    (hf : ∀ i, IntervalIntegrable (f i) volume (x i.castSucc) (x i.succ))
    (hf2 : ∀ i, IntervalIntegrable (fun s => f i s ^ 2) volume (x i.castSucc) (x i.succ))
    (hg : ∀ i, IntervalIntegrable (g i) volume (x i.castSucc) (x i.succ))
    (hg2 : ∀ i, IntervalIntegrable (fun s => g i s ^ 2) volume (x i.castSucc) (x i.succ)) :
    ∑ i, ∫ s in x i.castSucc..x i.succ, f i s * g i s
      ≤ √(∑ i, ∫ s in x i.castSucc..x i.succ, f i s ^ 2)
        * √(∑ i, ∫ s in x i.castSucc..x i.succ, g i s ^ 2) := by
  have hle : ∀ i : Fin n, x i.castSucc ≤ x i.succ := fun i => hx (Fin.castSucc_lt_succ (i := i)).le
  have hF : ∀ i, 0 ≤ ∫ s in x i.castSucc..x i.succ, f i s ^ 2 := fun i =>
    integral_nonneg (hle i) fun _ _ => sq_nonneg _
  have hG : ∀ i, 0 ≤ ∫ s in x i.castSucc..x i.succ, g i s ^ 2 := fun i =>
    integral_nonneg (hle i) fun _ _ => sq_nonneg _
  calc ∑ i, ∫ s in x i.castSucc..x i.succ, f i s * g i s
      ≤ ∑ i, √(∫ s in x i.castSucc..x i.succ, f i s ^ 2)
          * √(∫ s in x i.castSucc..x i.succ, g i s ^ 2) :=
        Finset.sum_le_sum fun i _ =>
          intervalIntegral.integral_mul_le_sqrt_mul_sqrt (hle i) (hf i) (hf2 i) (hg i) (hg2 i)
    _ ≤ √(∑ i, √(∫ s in x i.castSucc..x i.succ, f i s ^ 2) ^ 2)
          * √(∑ i, √(∫ s in x i.castSucc..x i.succ, g i s ^ 2) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = √(∑ i, ∫ s in x i.castSucc..x i.succ, f i s ^ 2)
          * √(∑ i, ∫ s in x i.castSucc..x i.succ, g i s ^ 2) := by
        simp only [Real.sq_sqrt (hF _), Real.sq_sqrt (hG _)]

/-- **Minkowski's inequality for panel sums.** Let the partition be nondecreasing, and let
$f_i, g_i : \mathbb{R} \to \mathbb{R}$, $i = 0, \dots, n - 1$, be functions such that $f_i$,
$f_i^2$, $g_i$ and $g_i^2$ are integrable on $I_i$. Then
$$\Bigl(\sum_{i=0}^{n-1} \int_{I_i} (f_i + g_i)^2\Bigr)^{1/2} \le \Bigl(\sum_{i=0}^{n-1}
  \int_{I_i} f_i^2\Bigr)^{1/2} + \Bigl(\sum_{i=0}^{n-1} \int_{I_i} g_i^2\Bigr)^{1/2}.$$
-/
theorem sqrt_sum_integral_add_sq_le (hx : Monotone x) {f g : Fin n → ℝ → ℝ}
    (hf : ∀ i, IntervalIntegrable (f i) volume (x i.castSucc) (x i.succ))
    (hf2 : ∀ i, IntervalIntegrable (fun s => f i s ^ 2) volume (x i.castSucc) (x i.succ))
    (hg : ∀ i, IntervalIntegrable (g i) volume (x i.castSucc) (x i.succ))
    (hg2 : ∀ i, IntervalIntegrable (fun s => g i s ^ 2) volume (x i.castSucc) (x i.succ)) :
    √(∑ i, ∫ s in x i.castSucc..x i.succ, (f i s + g i s) ^ 2)
      ≤ √(∑ i, ∫ s in x i.castSucc..x i.succ, f i s ^ 2)
        + √(∑ i, ∫ s in x i.castSucc..x i.succ, g i s ^ 2) := by
  have hle : ∀ i : Fin n, x i.castSucc ≤ x i.succ := fun i => hx (Fin.castSucc_lt_succ (i := i)).le
  set F := ∑ i, ∫ s in x i.castSucc..x i.succ, f i s ^ 2 with hFdef
  set G := ∑ i, ∫ s in x i.castSucc..x i.succ, g i s ^ 2 with hGdef
  have hF : 0 ≤ F := Finset.sum_nonneg fun i _ => integral_nonneg (hle i) fun _ _ => sq_nonneg _
  have hG : 0 ≤ G := Finset.sum_nonneg fun i _ => integral_nonneg (hle i) fun _ _ => sq_nonneg _
  have hfg : ∀ i, IntervalIntegrable (fun s => f i s * g i s) volume (x i.castSucc) (x i.succ) :=
    fun i => intervalIntegrable_mul_of_sq (hf i) (hf2 i) (hg i) (hg2 i)
  have hsplit : ∑ i, ∫ s in x i.castSucc..x i.succ, (f i s + g i s) ^ 2
      = F + 2 * (∑ i, ∫ s in x i.castSucc..x i.succ, f i s * g i s) + G := by
    rw [hFdef, hGdef, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← intervalIntegral.integral_const_mul, ← integral_add (hf2 i) ((hfg i).const_mul 2),
      ← integral_add ((hf2 i).add ((hfg i).const_mul 2)) (hg2 i)]
    exact integral_congr fun s _ => by ring
  have hcs := sum_integral_mul_le_sqrt_mul_sqrt hx hf hf2 hg hg2
  rw [← hFdef, ← hGdef] at hcs
  calc √(∑ i, ∫ s in x i.castSucc..x i.succ, (f i s + g i s) ^ 2)
      ≤ √((√F + √G) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        rw [hsplit, add_sq, Real.sq_sqrt hF, Real.sq_sqrt hG]
        linarith
    _ = √F + √G := Real.sqrt_sq (by positivity)

/-! ### The pairing with a function -/

/-- **The pairing** of a function $g : \mathbb{R} \to \mathbb{R}$ with a broken polynomial $v$:
$$\langle g, v \rangle = \sum_{i=0}^{n-1} \int_{x_i}^{x_{i+1}} g\, v_i.$$
It is the value at $v$ of the source functional of a Galerkin method with datum $g$. For a
strictly increasing partition, it is the $L^2(x_0, x_n)$ inner product of $g$ with the step
function of $v$. -/
def pairing (g : ℝ → ℝ) (v : BrokenPolynomial x r) : ℝ :=
  ∑ i, ∫ s in x i.castSucc..x i.succ, g s * (v i).eval s

/-- The pairing $\langle g, v \rangle$ is $\sum_{i=0}^{n-1} \int_{x_i}^{x_{i+1}} g\, v_i$. -/
theorem pairing_def (g : ℝ → ℝ) (v : BrokenPolynomial x r) :
    pairing g v = ∑ i, ∫ s in x i.castSucc..x i.succ, g s * (v i).eval s := rfl

/-- For a nondecreasing partition and a function $g$ integrable on $[x_0, x_n]$, the pairing is
additive in the broken polynomial: $\langle g, v + w \rangle = \langle g, v \rangle + \langle g,
w \rangle$. -/
theorem pairing_add (hx : Monotone x) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume (x 0) (x (Fin.last n))) (v w : BrokenPolynomial x r) :
    pairing g (v + w) = pairing g v + pairing g w := by
  simp only [pairing_def, add_apply, eval_add, mul_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact integral_add (intervalIntegrable_mul_eval_panel hx hg v i)
    (intervalIntegrable_mul_eval_panel hx hg w i)

/-- The pairing is homogeneous in the broken polynomial: $\langle g, c v \rangle = c \langle g, v
\rangle$. -/
theorem pairing_smul (g : ℝ → ℝ) (c : ℝ) (v : BrokenPolynomial x r) :
    pairing g (c • v) = c * pairing g v := by
  simp only [pairing_def, smul_apply, eval_smul, smul_eq_mul, Finset.mul_sum,
    ← intervalIntegral.integral_const_mul]
  exact Finset.sum_congr rfl fun i _ => integral_congr fun s _ => by ring

/-- The pairing changes sign with the broken polynomial:
$\langle g, -v \rangle = -\langle g, v \rangle$. -/
theorem pairing_neg (g : ℝ → ℝ) (v : BrokenPolynomial x r) : pairing g (-v) = -pairing g v := by
  simp only [pairing_def, neg_apply, eval_neg, mul_neg, intervalIntegral.integral_neg,
    Finset.sum_neg_distrib]

/-- For a nondecreasing partition and a function $g$ integrable on $[x_0, x_n]$, $\langle g, v - w
\rangle = \langle g, v \rangle - \langle g, w \rangle$. -/
theorem pairing_sub (hx : Monotone x) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume (x 0) (x (Fin.last n))) (v w : BrokenPolynomial x r) :
    pairing g (v - w) = pairing g v - pairing g w := by
  rw [sub_eq_add_neg, pairing_add hx hg, pairing_neg, sub_eq_add_neg]

/-- For a nondecreasing partition and functions $g_1$, $g_2$ integrable on $[x_0, x_n]$, $\langle
g_1 + g_2, v \rangle = \langle g_1, v \rangle + \langle g_2, v \rangle$. -/
theorem pairing_add_left (hx : Monotone x) {g₁ g₂ : ℝ → ℝ}
    (hg₁ : IntervalIntegrable g₁ volume (x 0) (x (Fin.last n)))
    (hg₂ : IntervalIntegrable g₂ volume (x 0) (x (Fin.last n))) (v : BrokenPolynomial x r) :
    pairing (fun s => g₁ s + g₂ s) v = pairing g₁ v + pairing g₂ v := by
  simp only [pairing_def, add_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact integral_add (intervalIntegrable_mul_eval_panel hx hg₁ v i)
    (intervalIntegrable_mul_eval_panel hx hg₂ v i)

/-- For a nondecreasing partition and functions $g_1$, $g_2$ integrable on $[x_0, x_n]$, $\langle
g_1 - g_2, v \rangle = \langle g_1, v \rangle - \langle g_2, v \rangle$. -/
theorem pairing_sub_left (hx : Monotone x) {g₁ g₂ : ℝ → ℝ}
    (hg₁ : IntervalIntegrable g₁ volume (x 0) (x (Fin.last n)))
    (hg₂ : IntervalIntegrable g₂ volume (x 0) (x (Fin.last n))) (v : BrokenPolynomial x r) :
    pairing (fun s => g₁ s - g₂ s) v = pairing g₁ v - pairing g₂ v := by
  simp only [pairing_def, sub_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact integral_sub (intervalIntegrable_mul_eval_panel hx hg₁ v i)
    (intervalIntegrable_mul_eval_panel hx hg₂ v i)

/-- The pairing is homogeneous in the function: $\langle c g, v \rangle = c \langle g, v \rangle$.
-/
theorem pairing_smul_left (g : ℝ → ℝ) (c : ℝ) (v : BrokenPolynomial x r) :
    pairing (fun s => c * g s) v = c * pairing g v := by
  simp only [pairing_def, Finset.mul_sum, ← intervalIntegral.integral_const_mul]
  exact Finset.sum_congr rfl fun i _ => integral_congr fun s _ => by ring

section StrictMono

variable [hx : Fact (StrictMono x)]

/-- **The Cauchy–Schwarz inequality for the pairing**: for a strictly increasing partition and a
function $g$ with $g$ and $g^2$ integrable on $[x_0, x_n]$,
$$\langle g, v \rangle \le \Bigl(\sum_{i=0}^{n-1} \int_{I_i} g^2\Bigr)^{1/2} \|v\|$$
for every broken polynomial $v$. -/
theorem pairing_le_sqrt_mul_norm {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume (x 0) (x (Fin.last n)))
    (hg2 : IntervalIntegrable (fun s => g s ^ 2) volume (x 0) (x (Fin.last n)))
    (v : BrokenPolynomial x r) :
    pairing g v ≤ √(∑ i : Fin n, ∫ s in x i.castSucc..x i.succ, g s ^ 2) * ‖v‖ := by
  have hm : Monotone x := hx.out.monotone
  have h := sum_integral_mul_le_sqrt_mul_sqrt hm (f := fun _ => g) (g := fun i => (v i).eval)
    (fun i => intervalIntegrable_panel hm hg i) (fun i => intervalIntegrable_panel hm hg2 i)
    (fun i => (v i).continuous.intervalIntegrable _ _)
    (fun i => ((v i).continuous.pow 2).intervalIntegrable _ _)
  rw [← norm_sq_eq, Real.sqrt_sq (norm_nonneg _)] at h
  exact h

/-- For a strictly increasing partition and a function $g$ with $g$ and $g^2$ integrable on
$[x_0, x_n]$, every broken polynomial $v$ satisfies $|\langle g, v \rangle| \le \bigl(\sum_i
\int_{I_i} g^2\bigr)^{1/2} \|v\|$. -/
theorem abs_pairing_le {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume (x 0) (x (Fin.last n)))
    (hg2 : IntervalIntegrable (fun s => g s ^ 2) volume (x 0) (x (Fin.last n)))
    (v : BrokenPolynomial x r) :
    |pairing g v| ≤ √(∑ i : Fin n, ∫ s in x i.castSucc..x i.succ, g s ^ 2) * ‖v‖ := by
  rw [abs_le]
  refine ⟨?_, pairing_le_sqrt_mul_norm hg hg2 v⟩
  have h := pairing_le_sqrt_mul_norm hg hg2 (-v)
  rw [pairing_neg, norm_neg] at h
  linarith

variable (x r) in
/-- **The pairing as a continuous linear functional** $v \mapsto \langle g, v \rangle$ on the broken
polynomial space, for a strictly increasing partition and a function $g$ integrable on
$[x_0, x_n]$. -/
def pairingL {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (x 0) (x (Fin.last n))) :
    BrokenPolynomial x r →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := pairing g
      map_add' := pairing_add hx.out.monotone hg
      map_smul' := fun c v => by simp [pairing_smul] }

/-- The functional `BrokenPolynomial.pairingL x r hg` sends $v$ to $\langle g, v \rangle$. -/
@[simp]
theorem pairingL_apply {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (x 0) (x (Fin.last n)))
    (v : BrokenPolynomial x r) : pairingL x r hg v = pairing g v := rfl

/-- For a strictly increasing partition and a function $g$ with $g$ and $g^2$ integrable on
$[x_0, x_n]$, the operator norm of the pairing functional $v \mapsto \langle g, v \rangle$ is at
most the $L^2$ norm $\bigl(\sum_i \int_{I_i} g^2\bigr)^{1/2}$ of $g$. -/
theorem norm_pairingL_le {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (x 0) (x (Fin.last n)))
    (hg2 : IntervalIntegrable (fun s => g s ^ 2) volume (x 0) (x (Fin.last n))) :
    ‖pairingL x r hg‖ ≤ √(∑ i : Fin n, ∫ s in x i.castSucc..x i.succ, g s ^ 2) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun v => by
    rw [pairingL_apply, Real.norm_eq_abs]
    exact abs_pairing_le hg hg2 v

/-- **The triangle inequality between a function and two broken polynomials.** For a strictly
increasing partition, a function $g$ with $g$ and $g^2$ integrable on $[x_0, x_n]$, and broken
polynomials $v$ and $w$,
$$\Bigl(\sum_{i=0}^{n-1} \int_{I_i} (g - v_i)^2\Bigr)^{1/2} \le \Bigl(\sum_{i=0}^{n-1}
  \int_{I_i} (g - w_i)^2\Bigr)^{1/2} + \|w - v\|.$$
-/
theorem sqrt_sum_integral_sub_sq_le {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume (x 0) (x (Fin.last n)))
    (hg2 : IntervalIntegrable (fun s => g s ^ 2) volume (x 0) (x (Fin.last n)))
    (v w : BrokenPolynomial x r) :
    √(∑ i, ∫ s in x i.castSucc..x i.succ, (g s - (v i).eval s) ^ 2)
      ≤ √(∑ i, ∫ s in x i.castSucc..x i.succ, (g s - (w i).eval s) ^ 2) + ‖w - v‖ := by
  have hm : Monotone x := hx.out.monotone
  have h := sqrt_sum_integral_add_sq_le hm (f := fun i s => g s - (w i).eval s)
    (g := fun i s => (w i).eval s - (v i).eval s) (intervalIntegrable_sub_eval_panel hm hg w)
    (intervalIntegrable_sub_eval_sq_panel hm hg hg2 w)
    (fun i => ((w i).continuous.sub (v i).continuous).intervalIntegrable _ _)
    (fun i => (((w i).continuous.sub (v i).continuous).pow 2).intervalIntegrable _ _)
  have e1 : ∑ i, ∫ s in x i.castSucc..x i.succ, ((w i).eval s - (v i).eval s) ^ 2
      = ‖w - v‖ ^ 2 := by
    rw [norm_sq_eq]
    simp only [sub_apply, eval_sub]
  rw [e1, Real.sqrt_sq (norm_nonneg _)] at h
  refine le_trans (le_of_eq ?_) h
  congr 1
  refine Finset.sum_congr rfl fun i _ => integral_congr fun s _ => ?_
  ring

end StrictMono

/-! ### Nodal interpolation -/

/-- **A node system of degree $r$** on the partition: points $\xi_{i,j}$, $i = 0, \dots, n - 1$,
$j = 0, \dots, r$, such that the $r + 1$ nodes $\xi_{i,0}, \dots, \xi_{i,r}$ of each panel lie
in the panel $[x_i, x_{i+1}]$ and are distinct. -/
structure IsNodes (x : Fin (n + 1) → ℝ) (r : ℕ) (node : Fin n → Fin (r + 1) → ℝ) : Prop where
  /-- The nodes $\xi_{i,j}$ of the panel $i$ lie in $[x_i, x_{i+1}]$. -/
  mem : ∀ i j, node i j ∈ Icc (x i.castSucc) (x i.succ)
  /-- The nodes of each panel are distinct. -/
  injective : ∀ i, Function.Injective (node i)

/-- **A Lagrange node system**: a node system of degree $r$ whose first and last nodes in each panel
are the endpoints of the panel, $\xi_{i,0} = x_i$ and $\xi_{i,r} = x_{i+1}$. At such nodes the
interpolant is continuous across the nodes of the partition and takes the interpolated values at
$x_0, \dots, x_n$. -/
structure IsLagrangeNodes (x : Fin (n + 1) → ℝ) (r : ℕ) (node : Fin n → Fin (r + 1) → ℝ) :
    Prop extends IsNodes x r node where
  /-- The first node of each panel is its left endpoint: $\xi_{i,0} = x_i$. -/
  node_zero : ∀ i, node i 0 = x i.castSucc
  /-- The last node of each panel is its right endpoint: $\xi_{i,r} = x_{i+1}$. -/
  node_last : ∀ i, node i (Fin.last r) = x i.succ

/-- The Lagrange interpolating polynomial of any values at $r + 1$ distinct nodes has degree at most
$r$. -/
theorem natDegree_interpolate_le {node : Fin (r + 1) → ℝ} (hnode : Function.Injective node)
    (c : Fin (r + 1) → ℝ) :
    (Lagrange.interpolate Finset.univ node c).natDegree ≤ r := by
  refine natDegree_le_of_degree_le ((Lagrange.degree_interpolate_le _ hnode.injOn).trans ?_)
  simp

variable (x r) in
/-- **Interpolation from nodal values**: for nodes $\xi_{i,j}$ that are distinct in each panel, the
linear map that sends values $c_{i,j}$ to the broken polynomial whose piece on the panel $i$ is
the Lagrange interpolating polynomial of the values $c_{i,0}, \dots, c_{i,r}$ at the nodes
$\xi_{i,0}, \dots, \xi_{i,r}$. -/
def ofValuesₗ (node : Fin n → Fin (r + 1) → ℝ) (hnode : ∀ i, Function.Injective (node i)) :
    (Fin n → Fin (r + 1) → ℝ) →ₗ[ℝ] BrokenPolynomial x r where
  toFun c := mk x (fun i => Lagrange.interpolate Finset.univ (node i) (c i))
    fun i => natDegree_interpolate_le (hnode i) (c i)
  map_add' c d := BrokenPolynomial.ext fun i => by
    simp only [mk_apply, add_apply, Pi.add_apply, map_add]
  map_smul' a c := BrokenPolynomial.ext fun i => by
    simp only [mk_apply, smul_apply, Pi.smul_apply, map_smul, RingHom.id_apply]

/-- The piece on the panel $i$ of the broken polynomial interpolating the values $c$ is the Lagrange
interpolating polynomial of $c_{i,0}, \dots, c_{i,r}$ at the nodes
$\xi_{i,0}, \dots, \xi_{i,r}$. -/
@[simp]
theorem ofValuesₗ_apply (node : Fin n → Fin (r + 1) → ℝ) (hnode : ∀ i, Function.Injective (node i))
    (c : Fin n → Fin (r + 1) → ℝ) (i : Fin n) :
    ofValuesₗ x r node hnode c i = Lagrange.interpolate Finset.univ (node i) (c i) := rfl

variable {node : Fin n → Fin (r + 1) → ℝ}

/-- **The nodal interpolant** $\Pi_h f$ of a function $f : \mathbb{R} \to \mathbb{R}$ at a node
system: the broken polynomial whose piece on each panel is the Lagrange interpolating polynomial
of $f$ at the nodes of that panel. -/
def interp (hnode : IsNodes x r node) (f : ℝ → ℝ) : BrokenPolynomial x r :=
  ofValuesₗ x r node hnode.injective fun i j => f (node i j)

/-- The piece of $\Pi_h f$ on the panel $i$ is the Lagrange interpolating polynomial of the values
$f(\xi_{i,0}), \dots, f(\xi_{i,r})$ at the nodes $\xi_{i,0}, \dots, \xi_{i,r}$. -/
theorem interp_apply (hnode : IsNodes x r node) (f : ℝ → ℝ) (i : Fin n) :
    interp hnode f i = Lagrange.interpolate Finset.univ (node i) fun j => f (node i j) := rfl

/-- The interpolant takes the values of $f$ at the nodes: $(\Pi_h f)_i(\xi_{i,j}) = f(\xi_{i,j})$
for all $i$ and $j$. -/
theorem eval_interp_node (hnode : IsNodes x r node) (f : ℝ → ℝ) (i : Fin n) (j : Fin (r + 1)) :
    (interp hnode f i).eval (node i j) = f (node i j) := by
  rw [interp_apply]
  exact Lagrange.eval_interpolate_at_node _ (hnode.injective i).injOn (Finset.mem_univ j)

/-- The interpolant is additive: $\Pi_h(f + g) = \Pi_h f + \Pi_h g$. -/
theorem interp_add (hnode : IsNodes x r node) (f g : ℝ → ℝ) :
    interp hnode (fun s => f s + g s) = interp hnode f + interp hnode g :=
  (ofValuesₗ x r node hnode.injective).map_add _ _

/-- The interpolant of a difference: $\Pi_h(f - g) = \Pi_h f - \Pi_h g$. -/
theorem interp_sub (hnode : IsNodes x r node) (f g : ℝ → ℝ) :
    interp hnode (fun s => f s - g s) = interp hnode f - interp hnode g :=
  (ofValuesₗ x r node hnode.injective).map_sub _ _

/-- The interpolant is homogeneous: $\Pi_h(c f) = c\, \Pi_h f$. -/
theorem interp_smul (hnode : IsNodes x r node) (c : ℝ) (f : ℝ → ℝ) :
    interp hnode (fun s => c * f s) = c • interp hnode f :=
  (ofValuesₗ x r node hnode.injective).map_smul c _

/-- For a nondecreasing partition, two functions that agree on $[x_0, x_n]$ have the same
interpolant. -/
theorem interp_congr (hx : Monotone x) (hnode : IsNodes x r node) {f g : ℝ → ℝ}
    (hfg : EqOn f g (Icc (x 0) (x (Fin.last n)))) : interp hnode f = interp hnode g := by
  unfold interp
  congr 1
  funext i j
  exact hfg (Icc_panel_subset hx i (hnode.mem i j))

/-- A broken polynomial is its own interpolant, panel by panel: the piece on the panel $i$ of the
interpolant of the function $s \mapsto v_i(s)$ is $v_i$. -/
theorem interp_eval (hnode : IsNodes x r node) (v : BrokenPolynomial x r) (i : Fin n) :
    (interp hnode fun s => (v i).eval s) i = v i := by
  rw [interp_apply]
  have hdeg : (v i).degree < (Finset.univ : Finset (Fin (r + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact (degree_le_of_natDegree_le (natDegree_le v i)).trans_lt
      (by exact_mod_cast Nat.lt_succ_self r)
  exact (Lagrange.eq_interpolate_of_eval_eq _ (hnode.injective i).injOn hdeg fun j _ => rfl).symm

section Lagrange

variable (hnode : IsLagrangeNodes x r node)
include hnode

/-- At a Lagrange node system, the right trace of the interpolant at $x_i$ is $f(x_i)$, for
$i = 0, \dots, n - 1$. -/
theorem traceRight_interp (f : ℝ → ℝ) (i : Fin n) :
    traceRight (interp hnode.toIsNodes f) i = f (x i.castSucc) := by
  rw [traceRight_apply, ← hnode.node_zero i, eval_interp_node]

/-- At a Lagrange node system, the left trace of the interpolant at $x_{i+1}$ is $f(x_{i+1})$, for
$i = 0, \dots, n - 1$. -/
theorem traceLeft_interp_succ (f : ℝ → ℝ) (i : Fin n) :
    traceLeft (interp hnode.toIsNodes f) i.succ = f (x i.succ) := by
  rw [traceLeft_succ, ← hnode.node_last i, eval_interp_node]

/-- At a Lagrange node system, the interpolant of every function lies in the continuous subspace:
its jumps at the interior nodes vanish. -/
theorem interp_mem_continuous (f : ℝ → ℝ) : interp hnode.toIsNodes f ∈ continuous x r := by
  intro i hi
  obtain ⟨j, hj⟩ : ∃ j : Fin n, i.castSucc = j.succ :=
    ⟨⟨i - 1, by omega⟩, Fin.ext (by simp; omega)⟩
  rw [jump_apply, traceRight_interp hnode, hj, traceLeft_interp_succ hnode, ← hj, sub_self]

end Lagrange

/-! ### The interpolation estimates -/

/-- **The interpolation estimate in broken form, with constant $1$.** Let the partition be strictly
increasing with panel lengths at most $h$, and let $\xi$ be a node system of degree $r$. Let
$f : \mathbb{R} \to \mathbb{R}$ be of class $C^r$, and let $g$ be a function such that $g$ and
$g^2$ are integrable on $[x_0, x_n]$ and $f^{(r)}(t) - f^{(r)}(s) = \int_s^t g$ for all
$s, t \in [x_0, x_n]$. Then for every $m \le r$
$$\sum_{i=0}^{n-1} \int_{x_i}^{x_{i+1}} \bigl(f^{(m)} - (\Pi_h f)_i^{(m)}\bigr)^2 \le
  h^{2(r+1-m)} \int_{x_0}^{x_n} g^2.$$

This is the estimate of Theorem 8.3 of [quarteroni2000numerical] for a node system of degree
$r$. The proof sums the panel estimate `integral_sq_iteratedDeriv_sub_le` over the panels. -/
theorem sum_integral_sq_iteratedDeriv_sub_interp_le (hx : StrictMono x) (hnode : IsNodes x r node)
    {h : ℝ} (hmesh : ∀ i : Fin n, x i.succ - x i.castSucc ≤ h) {f g : ℝ → ℝ}
    (hf : ContDiff ℝ r f) (hg : IntervalIntegrable g volume (x 0) (x (Fin.last n)))
    (hg2 : IntervalIntegrable (fun s => g s ^ 2) volume (x 0) (x (Fin.last n)))
    (hfg : ∀ s ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc (x 0) (x (Fin.last n)),
      iteratedDeriv r f t - iteratedDeriv r f s = ∫ q in s..t, g q)
    {m : ℕ} (hm : m ≤ r) :
    ∑ i, ∫ s in x i.castSucc..x i.succ,
        (iteratedDeriv m f s - (derivative^[m] (interp hnode f i)).eval s) ^ 2
      ≤ h ^ (2 * (r + 1 - m)) * ∫ s in x 0..x (Fin.last n), g s ^ 2 := by
  have hm' : Monotone x := hx.monotone
  rw [integral_eq_sum_panels hm' hg2, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  refine integral_sq_iteratedDeriv_sub_le (hx (Fin.castSucc_lt_succ (i := i))) (hmesh i) hf
    (intervalIntegrable_panel hm' hg i) (intervalIntegrable_panel hm' hg2 i)
    (fun s hs t ht => hfg s (Icc_panel_subset hm' i hs) t (Icc_panel_subset hm' i ht))
    (degree_le_of_natDegree_le (natDegree_le _ i)) (hnode.injective i) (hnode.mem i)
    (fun j => eval_interp_node hnode f i j) hm

open SobolevInterval in
/-- **The interpolation estimate over $H^{r+1}(x_0, x_n)$.** Let the partition be strictly
increasing with $n \ge 1$ panels of length at most $h$, and let $\xi$ be a node system of degree
$r$. Let $U \in H^{r+1}(x_0, x_n)$, and let $f$ be a representative of $U$ that is continuous on
$[x_0, x_n]$. Then for every $m \le r$
$$\sum_{i=0}^{n-1} \int_{x_i}^{x_{i+1}} \bigl(f^{(m)} - (\Pi_h f)_i^{(m)}\bigr)^2 \le
  h^{2(r+1-m)} |U|_{H^{r+1}}^2.$$

Here $f^{(m)}$ is the classical derivative `iteratedDeriv m f`. For $m \ge 1$ only its values
inside the open panels matter, and there $f$ is the $C^r$ representative of $U$. -/
theorem sum_integral_sq_iteratedDeriv_sub_interp_le_seminorm (hx : StrictMono x) (hn : 0 < n)
    (hnode : IsNodes x r node) {h : ℝ} (hmesh : ∀ i : Fin n, x i.succ - x i.castSucc ≤ h)
    (U : SobolevInterval (r + 1) (x 0) (x (Fin.last n))) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (x 0) (x (Fin.last n))))
    (hU : fn U =ᵐ[volume.restrict (Ioo (x 0) (x (Fin.last n)))] f) {m : ℕ} (hm : m ≤ r) :
    ∑ i, ∫ s in x i.castSucc..x i.succ,
        (iteratedDeriv m f s - (derivative^[m] (interp hnode f i)).eval s) ^ 2
      ≤ h ^ (2 * (r + 1 - m)) * seminorm (r + 1) (x 0) (x (Fin.last n)) U ^ 2 := by
  have hab : x 0 < x (Fin.last n) := hx (Fin.pos_iff_ne_zero.2 (Fin.ne_of_val_ne hn.ne'))
  have hm' : Monotone x := hx.monotone
  obtain ⟨F, hF, hae, hftc⟩ := exists_contDiff_ae_eq hab U
  have hF0 : fn U =ᵐ[volume.restrict (Ioo (x 0) (x (Fin.last n)))] F := by
    rw [← deriv_zero U]; simpa using hae 0
  have hfF : EqOn f F (Icc (x 0) (x (Fin.last n))) :=
    eqOn_Icc_of_ae_eq hab hf hF.continuous.continuousOn (hU.symm.trans hF0)
  rw [interp_congr hm' hnode hfF, seminorm_sq_eq_integral hab.le]
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ => integral_congr_Ioo
    (hx (Fin.castSucc_lt_succ (i := i))).le fun s hs => ?_))
    (sum_integral_sq_iteratedDeriv_sub_interp_le hx hnode hmesh hF
      (intervalIntegrable_deriv hab.le U _) (intervalIntegrable_deriv_sq hab.le U _) hftc hm)
  have hev : f =ᶠ[nhds s] F := by
    filter_upwards [Icc_mem_nhds ((hm' (Fin.zero_le _)).trans_lt hs.1)
      (hs.2.trans_le (hm' (Fin.le_last _)))] with q hq using hfF hq
  rw [hev.iteratedDeriv_eq m]

open SobolevInterval in
/-- **The interpolation estimate over $H^{r+1}(x_0, x_n)$ in $L^2$.** Let the partition be strictly
increasing with $n \ge 1$ panels of length at most $h$, and let $\xi$ be a node system of degree
$r$. Let $U \in H^{r+1}(x_0, x_n)$, and let $f$ be a representative of $U$ that is continuous on
$[x_0, x_n]$. Then
$$\sum_{i=0}^{n-1} \int_{x_i}^{x_{i+1}} \bigl(f - (\Pi_h f)_i\bigr)^2 \le h^{2(r+1)}
  |U|_{H^{r+1}}^2.$$
-/
theorem sum_integral_sq_sub_interp_le_seminorm (hx : StrictMono x) (hn : 0 < n)
    (hnode : IsNodes x r node) {h : ℝ} (hmesh : ∀ i : Fin n, x i.succ - x i.castSucc ≤ h)
    (U : SobolevInterval (r + 1) (x 0) (x (Fin.last n))) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (x 0) (x (Fin.last n))))
    (hU : fn U =ᵐ[volume.restrict (Ioo (x 0) (x (Fin.last n)))] f) :
    ∑ i, ∫ s in x i.castSucc..x i.succ, (f s - (interp hnode f i).eval s) ^ 2
      ≤ h ^ (2 * (r + 1)) * seminorm (r + 1) (x 0) (x (Fin.last n)) U ^ 2 := by
  have := sum_integral_sq_iteratedDeriv_sub_interp_le_seminorm hx hn hnode hmesh U hf hU
    (Nat.zero_le r)
  simpa only [iteratedDeriv_zero, Function.iterate_zero, id_eq, Nat.sub_zero] using this

open SobolevInterval in
/-- **The interpolation estimate for the weak derivative.** Let the partition be strictly increasing
with $n \ge 1$ panels of length at most $h$, and let $\xi$ be a node system of degree $r$. Let
$U \in H^{r+1}(x_0, x_n)$ with weak derivative $U'$, and let $f$ be a representative of $U$ that
is continuous on $[x_0, x_n]$. Then
$$\sum_{i=0}^{n-1} \int_{x_i}^{x_{i+1}} \bigl(U' - (\Pi_h f)_i'\bigr)^2 \le h^{2r}
  |U|_{H^{r+1}}^2.$$

The weak derivative is `SobolevInterval.deriv U 1`. For $r = 0$ the interpolant is piecewise
constant, and the statement is $\|U'\|^2 \le |U|_{H^1}^2$, which holds with equality. For
$r \ge 1$ the weak derivative is the derivative of the $C^r$ representative, and the statement
is the case $m = 1$ of `BrokenPolynomial.sum_integral_sq_iteratedDeriv_sub_interp_le_seminorm`. -/
theorem sum_integral_sq_deriv_sub_interp_le_seminorm (hx : StrictMono x) (hn : 0 < n)
    (hnode : IsNodes x r node) {h : ℝ} (hmesh : ∀ i : Fin n, x i.succ - x i.castSucc ≤ h)
    (U : SobolevInterval (r + 1) (x 0) (x (Fin.last n))) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (x 0) (x (Fin.last n))))
    (hU : fn U =ᵐ[volume.restrict (Ioo (x 0) (x (Fin.last n)))] f) :
    ∑ i, ∫ s in x i.castSucc..x i.succ,
        (SobolevInterval.deriv U 1 s - (derivative (interp hnode f i)).eval s) ^ 2
      ≤ h ^ (2 * r) * seminorm (r + 1) (x 0) (x (Fin.last n)) U ^ 2 := by
  have hab : x 0 < x (Fin.last n) := hx (Fin.pos_iff_ne_zero.2 (Fin.ne_of_val_ne hn.ne'))
  have hm' : Monotone x := hx.monotone
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · -- the interpolant is piecewise constant
    have hd : ∀ i, derivative (interp hnode f i) = 0 := fun i => by
      rw [eq_C_of_natDegree_le_zero (natDegree_le _ i), derivative_C]
    simp only [hd, eval_zero, sub_zero, Nat.mul_zero, pow_zero, one_mul]
    rw [seminorm_sq_eq_integral hab.le, integral_eq_sum_panels hm'
      (intervalIntegrable_deriv_sq hab.le U _)]
    rfl
  · obtain ⟨F, hF, hae, hftc⟩ := exists_contDiff_ae_eq hab U
    have hF0 : fn U =ᵐ[volume.restrict (Ioo (x 0) (x (Fin.last n)))] F := by
      rw [← deriv_zero U]; simpa using hae 0
    have hfF : EqOn f F (Icc (x 0) (x (Fin.last n))) :=
      eqOn_Icc_of_ae_eq hab hf hF.continuous.continuousOn (hU.symm.trans hF0)
    have h1 : SobolevInterval.deriv U 1 =ᵐ[volume.restrict (Ioo (x 0) (x (Fin.last n)))]
        iteratedDeriv 1 F := by
      have := hae ⟨1, by omega⟩
      simpa using this
    rw [interp_congr hm' hnode hfF]
    have key := sum_integral_sq_iteratedDeriv_sub_interp_le hx hnode hmesh hF
      (intervalIntegrable_deriv hab.le U _) (intervalIntegrable_deriv_sq hab.le U _) hftc hr
    rw [show 2 * (r + 1 - 1) = 2 * r by omega, ← seminorm_sq_eq_integral hab.le] at key
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_)) key
    refine integral_congr_ae_Ioo_of_mem ?_ (Icc_panel_subset hm' i (left_mem_Icc.2
      (hx (Fin.castSucc_lt_succ (i := i))).le)) (Icc_panel_subset hm' i (right_mem_Icc.2
      (hx (Fin.castSucc_lt_succ (i := i))).le))
    filter_upwards [h1] with s hs
    simp only [hs, Function.iterate_one]

/-! ### Traces of differences, and the interpolant at the endpoints -/

/-- For a nondecreasing partition, the pairing $\langle g, v \rangle$ depends only on the values of
$g$ on $[x_0, x_n]$. -/
theorem pairing_congr (hx : Monotone x) {g₁ g₂ : ℝ → ℝ}
    (hg : EqOn g₁ g₂ (Icc (x 0) (x (Fin.last n)))) (v : BrokenPolynomial x r) :
    pairing g₁ v = pairing g₂ v := by
  simp only [pairing_def]
  refine Finset.sum_congr rfl fun i _ => integral_congr fun s hs => ?_
  rw [uIcc_of_le (hx (Fin.castSucc_lt_succ (i := i)).le)] at hs
  rw [hg (Icc_panel_subset hx i hs)]

/-- The left trace of a difference: $(v - w)^-(x_i) = v^-(x_i) - w^-(x_i)$. -/
theorem traceLeft_sub (v w : BrokenPolynomial x r) (i : Fin (n + 1)) :
    traceLeft (v - w) i = traceLeft v i - traceLeft w i := by
  rw [← traceLeftₗ_apply, map_sub, traceLeftₗ_apply, traceLeftₗ_apply]

/-- The right trace of a difference: $(v - w)^+(x_i) = v^+(x_i) - w^+(x_i)$. -/
theorem traceRight_sub (v w : BrokenPolynomial x r) (i : Fin n) :
    traceRight (v - w) i = traceRight v i - traceRight w i :=
  (traceRightₗ x r i).map_sub v w

/-- The jump of a difference: $[v - w]_i = [v]_i - [w]_i$. -/
theorem jump_sub (v w : BrokenPolynomial x r) (i : Fin n) :
    jump (v - w) i = jump v i - jump w i := by
  rw [← jumpₗ_apply, map_sub, jumpₗ_apply, jumpₗ_apply]

/-- At a Lagrange node system on a partition with $n \ge 1$ panels, the left trace of the
interpolant at $x_n$ is $f(x_n)$. -/
theorem traceLeft_interp_last {node : Fin n → Fin (r + 1) → ℝ} (hnode : IsLagrangeNodes x r node)
    (hn : 0 < n) (f : ℝ → ℝ) :
    traceLeft (interp hnode.toIsNodes f) (Fin.last n) = f (x (Fin.last n)) := by
  have h : Fin.last n = (⟨n - 1, by omega⟩ : Fin n).succ := Fin.ext (by simp; omega)
  rw [h, traceLeft_interp_succ hnode]

/-- At a Lagrange node system on a partition with $n \ge 1$ panels, the right trace of the
interpolant at $x_0$ is $f(x_0)$. -/
theorem traceRight_interp_zero {node : Fin n → Fin (r + 1) → ℝ}
    (hnode : IsLagrangeNodes x r node) (hn : 0 < n) (f : ℝ → ℝ) :
    traceRight (interp hnode.toIsNodes f) ⟨0, hn⟩ = f (x 0) :=
  traceRight_interp hnode f ⟨0, hn⟩

section StrictMono

variable [hx : Fact (StrictMono x)]

/-- **The triangle inequality between two broken polynomials through a function.** For a strictly
increasing partition, a function $g$ with $g$ and $g^2$ integrable on $[x_0, x_n]$, and broken
polynomials $v$ and $w$,
$$\|v - w\| \le \Bigl(\sum_{i=0}^{n-1} \int_{I_i} (g - v_i)^2\Bigr)^{1/2} +
  \Bigl(\sum_{i=0}^{n-1} \int_{I_i} (g - w_i)^2\Bigr)^{1/2}.$$
-/
theorem norm_sub_le_sqrt_add_sqrt {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume (x 0) (x (Fin.last n)))
    (hg2 : IntervalIntegrable (fun s => g s ^ 2) volume (x 0) (x (Fin.last n)))
    (v w : BrokenPolynomial x r) :
    ‖v - w‖ ≤ √(∑ i, ∫ s in x i.castSucc..x i.succ, (g s - (v i).eval s) ^ 2)
      + √(∑ i, ∫ s in x i.castSucc..x i.succ, (g s - (w i).eval s) ^ 2) := by
  have hm : Monotone x := hx.out.monotone
  have hη := intervalIntegrable_sub_eval_panel hm hg (r := r)
  have hη2 := intervalIntegrable_sub_eval_sq_panel hm hg hg2 (r := r)
  have hη2' : ∀ i, IntervalIntegrable (fun s => ((v i).eval s - g s) ^ 2)
      volume (x i.castSucc) (x i.succ) := fun i => by
    have : (fun s => ((v i).eval s - g s) ^ 2) = fun s => (g s - (v i).eval s) ^ 2 := by
      funext s; ring
    rw [this]
    exact hη2 v i
  have h := sqrt_sum_integral_add_sq_le hm (f := fun i s => g s - (w i).eval s)
    (g := fun i s => (v i).eval s - g s) (hη w) (hη2 w)
    (fun i => ((v i).continuous.intervalIntegrable _ _).sub (intervalIntegrable_panel hm hg i)) hη2'
  have e1 : ∑ i, ∫ s in x i.castSucc..x i.succ, (g s - (w i).eval s + ((v i).eval s - g s)) ^ 2
      = ‖v - w‖ ^ 2 := by
    rw [norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => integral_congr fun s _ => ?_
    simp only [sub_apply, eval_sub]
    ring
  have e2 : ∑ i, ∫ s in x i.castSucc..x i.succ, ((v i).eval s - g s) ^ 2
      = ∑ i, ∫ s in x i.castSucc..x i.succ, (g s - (v i).eval s) ^ 2 :=
    Finset.sum_congr rfl fun i _ => integral_congr fun s _ => by ring
  rw [e1, e2, Real.sqrt_sq (norm_nonneg _), add_comm] at h
  exact h

/-- The Cauchy–Schwarz inequality for a panel sum against a broken polynomial: for a strictly
increasing partition, functions $\eta_i$ with $\eta_i$ and $\eta_i^2$ integrable on $I_i$, and a
broken polynomial $v$,
$$\Bigl|\sum_{i=0}^{n-1} \int_{I_i} \eta_i\, v_i\Bigr| \le \Bigl(\sum_{i=0}^{n-1} \int_{I_i}
  \eta_i^2\Bigr)^{1/2} \|v\|.$$
-/
theorem abs_sum_integral_mul_eval_le {η : Fin n → ℝ → ℝ}
    (hη : ∀ i, IntervalIntegrable (η i) volume (x i.castSucc) (x i.succ))
    (hη2 : ∀ i, IntervalIntegrable (fun s => η i s ^ 2) volume (x i.castSucc) (x i.succ))
    (v : BrokenPolynomial x r) :
    |∑ i, ∫ s in x i.castSucc..x i.succ, η i s * (v i).eval s|
      ≤ √(∑ i, ∫ s in x i.castSucc..x i.succ, η i s ^ 2) * ‖v‖ := by
  have hm : Monotone x := hx.out.monotone
  have key : ∀ w : BrokenPolynomial x r, ∑ i, ∫ s in x i.castSucc..x i.succ, η i s * (w i).eval s
      ≤ √(∑ i, ∫ s in x i.castSucc..x i.succ, η i s ^ 2) * ‖w‖ := fun w => by
    have h := sum_integral_mul_le_sqrt_mul_sqrt hm (g := fun i => (w i).eval) hη hη2
      (fun i => (w i).continuous.intervalIntegrable _ _)
      (fun i => ((w i).continuous.pow 2).intervalIntegrable _ _)
    rwa [← norm_sq_eq, Real.sqrt_sq (norm_nonneg _)] at h
  rw [abs_le]
  refine ⟨?_, key v⟩
  have h := key (-v)
  simp only [neg_apply, eval_neg, mul_neg, intervalIntegral.integral_neg, Finset.sum_neg_distrib,
    norm_neg] at h
  linarith

/-- The Cauchy–Schwarz inequality for a panel sum with a bounded coefficient: let the partition be
strictly increasing, let $c$ be integrable on $[x_0, x_n]$ with $|c| \le C$ on $[x_0, x_n]$ for
a constant $C \ge 0$, and let $\eta_i$ be functions with $\eta_i$ and $\eta_i^2$ integrable on
$I_i$. Then for every broken polynomial $v$
$$\Bigl|\sum_{i=0}^{n-1} \int_{I_i} c\, \eta_i\, v_i\Bigr| \le C \Bigl(\sum_{i=0}^{n-1}
  \int_{I_i} \eta_i^2\Bigr)^{1/2} \|v\|.$$
-/
theorem abs_sum_integral_mul_mul_eval_le {c : ℝ → ℝ}
    (hc : IntervalIntegrable c volume (x 0) (x (Fin.last n))) {C : ℝ} (hC : 0 ≤ C)
    (hcC : ∀ s ∈ Icc (x 0) (x (Fin.last n)), |c s| ≤ C) {η : Fin n → ℝ → ℝ}
    (hη : ∀ i, IntervalIntegrable (η i) volume (x i.castSucc) (x i.succ))
    (hη2 : ∀ i, IntervalIntegrable (fun s => η i s ^ 2) volume (x i.castSucc) (x i.succ))
    (v : BrokenPolynomial x r) :
    |∑ i, ∫ s in x i.castSucc..x i.succ, c s * η i s * (v i).eval s|
      ≤ C * √(∑ i, ∫ s in x i.castSucc..x i.succ, η i s ^ 2) * ‖v‖ := by
  have hm : Monotone x := hx.out.monotone
  have hle : ∀ i : Fin n, x i.castSucc ≤ x i.succ := fun i => hm (Fin.castSucc_lt_succ (i := i)).le
  have hmemI : ∀ i : Fin n, ∀ s ∈ Ι (x i.castSucc) (x i.succ), s ∈ Icc (x 0) (x (Fin.last n)) :=
    fun i s hs => Icc_panel_subset hm i (by
      rw [uIoc_of_le (hle i)] at hs
      exact Ioc_subset_Icc_self hs)
  have hmeas : ∀ i : Fin n, AEStronglyMeasurable (fun s => c s * η i s)
      (volume.restrict (Ι (x i.castSucc) (x i.succ))) := fun i =>
    (intervalIntegrable_panel hm hc i).def'.aestronglyMeasurable.mul
      (hη i).def'.aestronglyMeasurable
  have hsqle : ∀ s ∈ Icc (x 0) (x (Fin.last n)), c s ^ 2 ≤ C ^ 2 := fun s hs => by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hcC s hs) 2
  have hpt : ∀ i : Fin n, ∀ s ∈ Icc (x 0) (x (Fin.last n)),
      (c s * η i s) ^ 2 ≤ C ^ 2 * η i s ^ 2 := fun i s hs => by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (hsqle s hs) (sq_nonneg _)
  have hcη : ∀ i, IntervalIntegrable (fun s => c s * η i s) volume (x i.castSucc) (x i.succ) := by
    intro i
    refine ((hη i).norm.const_mul C).mono_fun' (hmeas i) ?_
    refine (ae_restrict_iff' measurableSet_uIoc).2 (Filter.Eventually.of_forall fun s hs => ?_)
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hcC s (hmemI i s hs)) (abs_nonneg _)
  have hcη2 : ∀ i, IntervalIntegrable (fun s => (c s * η i s) ^ 2) volume
      (x i.castSucc) (x i.succ) := by
    intro i
    refine ((hη2 i).const_mul (C ^ 2)).mono_fun' ((hmeas i).pow 2) ?_
    refine (ae_restrict_iff' measurableSet_uIoc).2 (Filter.Eventually.of_forall fun s hs => ?_)
    change ‖(c s * η i s) ^ 2‖ ≤ C ^ 2 * η i s ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hpt i s (hmemI i s hs)
  have h := abs_sum_integral_mul_eval_le (η := fun i s => c s * η i s) hcη hcη2 v
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  have hsq : ∑ i, ∫ s in x i.castSucc..x i.succ, (c s * η i s) ^ 2
      ≤ C ^ 2 * ∑ i, ∫ s in x i.castSucc..x i.succ, η i s ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← intervalIntegral.integral_const_mul]
    exact integral_mono_on (hle i) (hcη2 i) ((hη2 i).const_mul _) fun s hs =>
      hpt i s (Icc_panel_subset hm i hs)
  calc √(∑ i, ∫ s in x i.castSucc..x i.succ, (c s * η i s) ^ 2)
      ≤ √(C ^ 2 * ∑ i, ∫ s in x i.castSucc..x i.succ, η i s ^ 2) := Real.sqrt_le_sqrt hsq
    _ = C * √(∑ i, ∫ s in x i.castSucc..x i.succ, η i s ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hC]

end StrictMono

/-! ### The Markov inequality on a panel -/

/-- **The $L^2$ Markov inequality on a panel.** For $u < w$ and a real polynomial $p$ of degree at
most $r$,
$$\int_u^w p'^2 \le \Bigl(\frac{2 r (r + 1)}{w - u}\Bigr)^2 \int_u^w p^2.$$

The proof transports the inequality on $[-1, 1]$ (`Polynomial.integral_derivative_sq_le` of
`Numlib.Approximation.MarkovInequality`) to the panel by the affine map
$\tau \mapsto m + k \tau$, with $m = (u + w)/2$ and $k = (w - u)/2$. -/
theorem integral_derivative_sq_le_panel {u w : ℝ} (huw : u < w) {p : ℝ[X]} (hp : p.natDegree ≤ r) :
    ∫ s in u..w, (derivative p).eval s ^ 2
      ≤ (2 * r * (r + 1) / (w - u)) ^ 2 * ∫ s in u..w, p.eval s ^ 2 := by
  set k : ℝ := (w - u) / 2 with hk
  set m : ℝ := (u + w) / 2 with hm
  have hk0 : 0 < k := by rw [hk]; linarith
  set q : ℝ[X] := p.comp (C k * X + C m) with hq
  have hqdeg : q.natDegree ≤ r := by
    rw [hq, natDegree_comp]
    have : (C k * X + C m).natDegree ≤ 1 := natDegree_linear_le
    calc p.natDegree * (C k * X + C m).natDegree ≤ p.natDegree * 1 :=
          Nat.mul_le_mul_left _ this
      _ ≤ r := by rw [Nat.mul_one]; exact hp
  have hqeval : ∀ τ, q.eval τ = p.eval (k * τ + m) := fun τ => by
    simp [hq, eval_comp]
  have hqder : ∀ τ, (derivative q).eval τ = k * (derivative p).eval (k * τ + m) := fun τ => by
    rw [hq, derivative_comp, derivative_add, derivative_C_mul_X, derivative_C, add_zero]
    simp only [eval_mul, eval_C, eval_comp, eval_add, eval_X]
  have hmk1 : k * (-1) + m = u := by rw [hk, hm]; ring
  have hmk2 : k * 1 + m = w := by rw [hk, hm]; ring
  -- the two substitutions
  have e1 : ∫ τ in (-1 : ℝ)..1, q.eval τ ^ 2 = k⁻¹ * ∫ s in u..w, p.eval s ^ 2 := by
    simp_rw [hqeval]
    rw [integral_comp_mul_add (fun s => p.eval s ^ 2) hk0.ne' m, hmk1, hmk2, smul_eq_mul]
  have e2 : ∫ τ in (-1 : ℝ)..1, (derivative q).eval τ ^ 2
      = k * ∫ s in u..w, (derivative p).eval s ^ 2 := by
    have e21 : ∫ τ in (-1 : ℝ)..1, (derivative q).eval τ ^ 2
        = ∫ τ in (-1 : ℝ)..1, k ^ 2 * (derivative p).eval (k * τ + m) ^ 2 :=
      integral_congr fun τ _ => by rw [hqder, mul_pow]
    have e22 : ∫ τ in (-1 : ℝ)..1, (derivative p).eval (k * τ + m) ^ 2
        = k⁻¹ * ∫ s in u..w, (derivative p).eval s ^ 2 := by
      rw [integral_comp_mul_add (fun s => (derivative p).eval s ^ 2) hk0.ne' m, hmk1, hmk2,
        smul_eq_mul]
    rw [e21, intervalIntegral.integral_const_mul, e22, ← mul_assoc, pow_two, mul_assoc k k,
      mul_inv_cancel₀ hk0.ne', mul_one]
  have hM := Polynomial.integral_derivative_sq_le (N := r) hqdeg
  rw [e1, e2] at hM
  have hwu : w - u = 2 * k := by rw [hk]; ring
  rw [hwu]
  have : (2 * (r : ℝ) * (r + 1) / (2 * k)) ^ 2 = ((r : ℝ) * (r + 1)) ^ 2 * k⁻¹ * k⁻¹ := by
    field_simp
  rw [this]
  calc ∫ s in u..w, (derivative p).eval s ^ 2
      = k⁻¹ * (k * ∫ s in u..w, (derivative p).eval s ^ 2) := by
        rw [← mul_assoc, inv_mul_cancel₀ hk0.ne', one_mul]
    _ ≤ k⁻¹ * (((r : ℝ) * (r + 1)) ^ 2 * (k⁻¹ * ∫ s in u..w, p.eval s ^ 2)) :=
        mul_le_mul_of_nonneg_left hM (inv_pos.2 hk0).le
    _ = ((r : ℝ) * (r + 1)) ^ 2 * k⁻¹ * k⁻¹ * ∫ s in u..w, p.eval s ^ 2 := by ring

/-- **The Markov inequality in the broken norm.** For a strictly increasing partition whose panels
have length at least $h_{\min} > 0$, every broken polynomial $v$ of degree $r$ satisfies
$$\sum_{i=0}^{n-1} \int_{I_i} v_i'^2 \le \Bigl(\frac{2 r (r + 1)}{h_{\min}}\Bigr)^2 \|v\|^2.$$
-/
theorem sum_integral_sq_derivative_le [hx : Fact (StrictMono x)] {hmin : ℝ} (h0 : 0 < hmin)
    (hle : ∀ i : Fin n, hmin ≤ x i.succ - x i.castSucc) (v : BrokenPolynomial x r) :
    ∑ i, ∫ s in x i.castSucc..x i.succ, (derivative (v i)).eval s ^ 2
      ≤ (2 * r * (r + 1) / hmin) ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hlt : x i.castSucc < x i.succ := hx.out (Fin.castSucc_lt_succ (i := i))
  refine (integral_derivative_sq_le_panel hlt (natDegree_le v i)).trans
    (mul_le_mul_of_nonneg_right ?_ (integral_nonneg hlt.le fun s _ => sq_nonneg _))
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  exact div_le_div_of_nonneg_left (by positivity) h0 (hle i)


/-! ### The $L^2$ projection onto the broken space -/

variable (x r) in
/-- The broken polynomial equal to $q$ on the panel $i$ and to $0$ on the other panels, for a real
polynomial $q$ of degree at most $r$. -/
def single (i : Fin n) (q : ℝ[X]) (hq : q.natDegree ≤ r) : BrokenPolynomial x r :=
  mk x (Pi.single i q) fun j => by
    rcases eq_or_ne j i with rfl | h
    · simpa using hq
    · simp [h]

/-- The broken polynomial `BrokenPolynomial.single x r i q hq` has the piece $q$ on the panel $i$.
-/
theorem single_apply_self (i : Fin n) (q : ℝ[X]) (hq : q.natDegree ≤ r) :
    single x r i q hq i = q := by simp [single]

/-- The broken polynomial `BrokenPolynomial.single x r i q hq` has the piece $0$ on every panel
$j \neq i$. -/
theorem single_apply_of_ne {i j : Fin n} (hij : j ≠ i) (q : ℝ[X]) (hq : q.natDegree ≤ r) :
    single x r i q hq j = 0 := by simp [single, hij]

/-- The pairing of $g$ with the broken polynomial equal to $q$ on the panel $i$ and to $0$ elsewhere
is the panel integral $\int_{x_i}^{x_{i+1}} g\, q$. -/
theorem pairing_single (g : ℝ → ℝ) (i : Fin n) (q : ℝ[X]) (hq : q.natDegree ≤ r) :
    pairing g (single x r i q hq) = ∫ s in x i.castSucc..x i.succ, g s * q.eval s := by
  rw [pairing_def, Finset.sum_eq_single i]
  · rw [single_apply_self]
  · intro j _ hji
    simp [single_apply_of_ne hji]
  · intro h
    exact absurd (Finset.mem_univ i) h

section Proj

variable [hx : Fact (StrictMono x)]

instance : CompleteSpace (BrokenPolynomial x r) := FiniteDimensional.complete ℝ _

open scoped Classical in
variable (x r) in
/-- **The $L^2(x_0, x_n)$ projection** $P g$ of a function $g$ onto the broken polynomial space, for
a strictly increasing partition. If $g$ is integrable on $[x_0, x_n]$, then $P g$ is the unique
broken polynomial with
$$\langle P g, v \rangle = \sum_{i=0}^{n-1} \int_{I_i} g\, v_i$$
for every broken polynomial $v$, that is, the Riesz representative of the pairing. If $g$ is not
integrable on $[x_0, x_n]$, then $P g = 0$. -/
def proj (g : ℝ → ℝ) : BrokenPolynomial x r :=
  if hg : IntervalIntegrable g volume (x 0) (x (Fin.last n)) then
    (InnerProductSpace.toDual ℝ (BrokenPolynomial x r)).symm (pairingL x r hg) else 0

/-- The defining property of the projection: for a strictly increasing partition and a function $g$
integrable on $[x_0, x_n]$, the inner product of $P g$ with every broken polynomial $v$ is the
pairing $\langle g, v \rangle$. -/
theorem inner_proj {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (x 0) (x (Fin.last n)))
    (v : BrokenPolynomial x r) : ⟪proj x r g, v⟫ = pairing g v := by
  simp only [proj, hg, ↓reduceDIte, InnerProductSpace.toDual_symm_apply, pairingL_apply]

/-- **Orthogonality of the projection error**: for a strictly increasing partition and a function
$g$ integrable on $[x_0, x_n]$,
$$\sum_{i=0}^{n-1} \int_{I_i} \bigl(g - (P g)_i\bigr)\, v_i = 0$$
for every broken polynomial $v$. -/
theorem sum_integral_sub_proj_mul_eval_eq_zero {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume (x 0) (x (Fin.last n))) (v : BrokenPolynomial x r) :
    ∑ i, ∫ s in x i.castSucc..x i.succ, (g s - (proj x r g i).eval s) * (v i).eval s = 0 := by
  have hm : Monotone x := hx.out.monotone
  have h := inner_proj hg v
  rw [BrokenPolynomial.inner_def, pairing_def] at h
  rw [← sub_eq_zero.2 h.symm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc : Continuous fun s => (proj x r g i).eval s * (v i).eval s := by fun_prop
  rw [← integral_sub (intervalIntegrable_mul_eval_panel hm hg v i) (hc.intervalIntegrable _ _)]
  exact integral_congr fun s _ => by ring

/-- **Panelwise orthogonality of the projection error**: for a strictly increasing partition, a
function $g$ integrable on $[x_0, x_n]$, a panel $i$ and a real polynomial $q$ of degree at most
$r$,
$$\int_{I_i} \bigl(g - (P g)_i\bigr)\, q = 0.$$
-/
theorem integral_sub_proj_mul_eq_zero {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume (x 0) (x (Fin.last n))) (i : Fin n) {q : ℝ[X]}
    (hq : q.natDegree ≤ r) :
    ∫ s in x i.castSucc..x i.succ, (g s - (proj x r g i).eval s) * q.eval s = 0 := by
  have h := sum_integral_sub_proj_mul_eval_eq_zero hg (single x r i q hq)
  rw [Finset.sum_eq_single i] at h
  · rwa [single_apply_self] at h
  · intro j _ hji
    simp [single_apply_of_ne hji]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The expansion of a panel sum of squares: for a strictly increasing partition, functions $\eta_i$
with $\eta_i$ and $\eta_i^2$ integrable on $I_i$, and a broken polynomial $d$,
$$\sum_{i=0}^{n-1} \int_{I_i} (\eta_i + d_i)^2 = \sum_{i=0}^{n-1} \int_{I_i} \eta_i^2 + 2
  \sum_{i=0}^{n-1} \int_{I_i} \eta_i\, d_i + \|d\|^2.$$
-/
theorem sum_integral_add_eval_sq_eq {η : Fin n → ℝ → ℝ}
    (hη : ∀ i, IntervalIntegrable (η i) volume (x i.castSucc) (x i.succ))
    (hη2 : ∀ i, IntervalIntegrable (fun s => η i s ^ 2) volume (x i.castSucc) (x i.succ))
    (d : BrokenPolynomial x r) :
    ∑ i, ∫ s in x i.castSucc..x i.succ, (η i s + (d i).eval s) ^ 2
      = (∑ i, ∫ s in x i.castSucc..x i.succ, η i s ^ 2)
        + 2 * (∑ i, ∫ s in x i.castSucc..x i.succ, η i s * (d i).eval s) + ‖d‖ ^ 2 := by
  rw [norm_sq_eq, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : IntervalIntegrable (fun s => η i s * (d i).eval s) volume (x i.castSucc) (x i.succ) :=
    (hη i).mul_continuousOn (d i).continuous.continuousOn
  have h2 : IntervalIntegrable (fun s => (d i).eval s ^ 2) volume (x i.castSucc) (x i.succ) :=
    (by fun_prop : Continuous fun s => (d i).eval s ^ 2).intervalIntegrable _ _
  rw [← intervalIntegral.integral_const_mul, ← integral_add (hη2 i) (h1.const_mul 2),
    ← integral_add ((hη2 i).add (h1.const_mul 2)) h2]
  exact integral_congr fun s _ => by ring

/-- **The projection is the best approximation**: for a strictly increasing partition and a function
$g$ with $g$ and $g^2$ integrable on $[x_0, x_n]$,
$$\sum_{i=0}^{n-1} \int_{I_i} \bigl(g - (P g)_i\bigr)^2 \le \sum_{i=0}^{n-1} \int_{I_i} (g -
  w_i)^2$$
for every broken polynomial $w$. The proof is Pythagoras' theorem, from the orthogonality of the
error. -/
theorem sum_integral_sq_sub_proj_le {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume (x 0) (x (Fin.last n)))
    (hg2 : IntervalIntegrable (fun s => g s ^ 2) volume (x 0) (x (Fin.last n)))
    (w : BrokenPolynomial x r) :
    ∑ i, ∫ s in x i.castSucc..x i.succ, (g s - (proj x r g i).eval s) ^ 2
      ≤ ∑ i, ∫ s in x i.castSucc..x i.succ, (g s - (w i).eval s) ^ 2 := by
  have hm : Monotone x := hx.out.monotone
  have hη : ∀ i, IntervalIntegrable (fun s => g s - (proj x r g i).eval s) volume
      (x i.castSucc) (x i.succ) := fun i =>
    (intervalIntegrable_panel hm hg i).sub ((proj x r g i).continuous.intervalIntegrable _ _)
  have hη2 : ∀ i, IntervalIntegrable (fun s => (g s - (proj x r g i).eval s) ^ 2) volume
      (x i.castSucc) (x i.succ) := fun i =>
    intervalIntegrable_sub_sq (intervalIntegrable_panel hm hg i) (intervalIntegrable_panel hm hg2 i)
      (proj x r g i).continuous.continuousOn
  have key := sum_integral_add_eval_sq_eq hη hη2 (proj x r g - w)
  rw [sum_integral_sub_proj_mul_eval_eq_zero hg, mul_zero, add_zero] at key
  have e : ∑ i, ∫ s in x i.castSucc..x i.succ, (g s - (w i).eval s) ^ 2
      = ∑ i, ∫ s in x i.castSucc..x i.succ,
          (g s - (proj x r g i).eval s + ((proj x r g - w) i).eval s) ^ 2 :=
    Finset.sum_congr rfl fun i _ => integral_congr fun s _ => by
      simp only [sub_apply, eval_sub]; ring
  rw [e, key]
  exact le_add_of_nonneg_right (sq_nonneg _)

end Proj

/-! ### The continuous representative of a Sobolev function is absolutely continuous -/

open SobolevInterval in
/-- Let $a < b$ and $U \in H^{k+1}(a, b)$ with weak derivative $U'$, and let $f$ be a representative
of $U$ that is continuous on $[a, b]$. Then $f$ is the integral of $U'$:
$$f(t) - f(s) = \int_s^t U'$$
for all $s, t \in [a, b]$.

The weak derivative $U'$ is `SobolevInterval.deriv U 1`. The hypothesis that $f$ represents $U$
is that `SobolevInterval.fn U` equals $f$ almost everywhere on $(a, b)$. -/
theorem _root_.SobolevInterval.sub_eq_integral_deriv_one {a b : ℝ} (hab : a < b) {k : ℕ}
    (U : SobolevInterval (k + 1) a b) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hU : fn U =ᵐ[volume.restrict (Ioo a b)] f) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    f t - f s = ∫ q in s..t, SobolevInterval.deriv U 1 q := by
  have hw : HasWeakDerivOn (fn U) (SobolevInterval.deriv U 1) (TopologicalSpace.Opens.Ioo a b) := by
    have := hasWeakDerivOn_deriv_succ U 0
    rwa [Fin.castSucc_zero, deriv_zero, Fin.succ_zero_eq_one] at this
  obtain ⟨g, hg, hUg, hgint⟩ :=
    hw.exists_continuousOn_ae_eq hab (SobolevIntervalLp.integrableOn_deriv_Ioo U 1)
  have hfg : EqOn f g (Icc a b) := eqOn_Icc_of_ae_eq hab hf hg (hU.symm.trans hUg)
  rw [hfg hs, hfg ht]
  exact hgint s hs t ht

/-! ### The projection error in $L^2$, in $H^1$ and at the nodes -/

section ProjEstimates

variable [hx : Fact (StrictMono x)] {node : Fin n → Fin (r + 1) → ℝ}

open SobolevInterval in
/-- Let the partition be strictly increasing with $n \ge 1$ panels of length at most $h$, let $\xi$
be a node system of degree $r$, let $U \in H^{r+1}(x_0, x_n)$, and let $f$ be a representative
of $U$ that is continuous on $[x_0, x_n]$. Then $\bigl(\sum_i \int_{I_i} (f - (\Pi_h
f)_i)^2\bigr)^{1/2} \le h^{r+1} |U|_{H^{r+1}}$. This is the square-root form of
`BrokenPolynomial.sum_integral_sq_sub_interp_le_seminorm`. -/
theorem sqrt_sum_integral_sq_sub_interp_le_seminorm (hn : 0 < n) (hnode : IsNodes x r node)
    {h : ℝ} (hmesh : ∀ i : Fin n, x i.succ - x i.castSucc ≤ h)
    (U : SobolevInterval (r + 1) (x 0) (x (Fin.last n))) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (x 0) (x (Fin.last n))))
    (hU : fn U =ᵐ[volume.restrict (Ioo (x 0) (x (Fin.last n)))] f) :
    √(∑ i, ∫ s in x i.castSucc..x i.succ, (f s - (interp hnode f i).eval s) ^ 2)
      ≤ h ^ (r + 1) * seminorm (r + 1) (x 0) (x (Fin.last n)) U := by
  have hh : 0 ≤ h :=
    (sub_nonneg.2 (hx.out (Fin.castSucc_lt_succ (i := ⟨0, hn⟩))).le).trans (hmesh ⟨0, hn⟩)
  calc √(∑ i, ∫ s in x i.castSucc..x i.succ, (f s - (interp hnode f i).eval s) ^ 2)
      ≤ √(h ^ (2 * (r + 1)) * seminorm (r + 1) (x 0) (x (Fin.last n)) U ^ 2) :=
        Real.sqrt_le_sqrt (sum_integral_sq_sub_interp_le_seminorm hx.out hn hnode hmesh U hf hU)
    _ = h ^ (r + 1) * seminorm (r + 1) (x 0) (x (Fin.last n)) U := by
        rw [Real.sqrt_mul (by positivity), pow_mul', Real.sqrt_sq (by positivity),
          Real.sqrt_sq (apply_nonneg _ _)]

open SobolevInterval in
/-- Let the partition be strictly increasing with $n \ge 1$ panels of length at most $h$, let $\xi$
be a node system of degree $r$, let $U \in H^{r+1}(x_0, x_n)$ with weak derivative $U'$, and let
$f$ be a representative of $U$ that is continuous on $[x_0, x_n]$. Then $\bigl(\sum_i \int_{I_i}
(U' - (\Pi_h f)_i')^2\bigr)^{1/2} \le h^r |U|_{H^{r+1}}$. This is the square-root form of
`BrokenPolynomial.sum_integral_sq_deriv_sub_interp_le_seminorm`. -/
theorem sqrt_sum_integral_sq_deriv_sub_interp_le_seminorm (hn : 0 < n)
    (hnode : IsNodes x r node) {h : ℝ} (hmesh : ∀ i : Fin n, x i.succ - x i.castSucc ≤ h)
    (U : SobolevInterval (r + 1) (x 0) (x (Fin.last n))) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (x 0) (x (Fin.last n))))
    (hU : fn U =ᵐ[volume.restrict (Ioo (x 0) (x (Fin.last n)))] f) :
    √(∑ i, ∫ s in x i.castSucc..x i.succ,
        (SobolevInterval.deriv U 1 s - (derivative (interp hnode f i)).eval s) ^ 2)
      ≤ h ^ r * seminorm (r + 1) (x 0) (x (Fin.last n)) U := by
  have hh : 0 ≤ h :=
    (sub_nonneg.2 (hx.out (Fin.castSucc_lt_succ (i := ⟨0, hn⟩))).le).trans (hmesh ⟨0, hn⟩)
  calc √(∑ i, ∫ s in x i.castSucc..x i.succ,
        (SobolevInterval.deriv U 1 s - (derivative (interp hnode f i)).eval s) ^ 2)
      ≤ √(h ^ (2 * r) * seminorm (r + 1) (x 0) (x (Fin.last n)) U ^ 2) :=
        Real.sqrt_le_sqrt (sum_integral_sq_deriv_sub_interp_le_seminorm hx.out hn hnode hmesh U hf
          hU)
    _ = h ^ r * seminorm (r + 1) (x 0) (x (Fin.last n)) U := by
        rw [Real.sqrt_mul (by positivity), pow_mul', Real.sqrt_sq (by positivity),
          Real.sqrt_sq (apply_nonneg _ _)]

open SobolevInterval in
/-- **The $L^2$ estimate of the projection error.** Let the partition be strictly increasing with
$n \ge 1$ panels of length at most $h$, and let it carry a node system of degree $r$. Let
$U \in H^{r+1}(x_0, x_n)$, and let $f$ be a representative of $U$ that is continuous on
$[x_0, x_n]$. Then
$$\Bigl(\sum_{i=0}^{n-1} \int_{I_i} \bigl(f - (P f)_i\bigr)^2\Bigr)^{1/2} \le h^{r+1}
  |U|_{H^{r+1}}.$$

The projection is at least as good as the interpolant, by
`BrokenPolynomial.sum_integral_sq_sub_proj_le`. The node system enters only through the
interpolant. -/
theorem sqrt_sum_integral_sq_sub_proj_le_seminorm (hn : 0 < n) (hnode : IsNodes x r node) {h : ℝ}
    (hmesh : ∀ i : Fin n, x i.succ - x i.castSucc ≤ h)
    (U : SobolevInterval (r + 1) (x 0) (x (Fin.last n))) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (x 0) (x (Fin.last n))))
    (hU : fn U =ᵐ[volume.restrict (Ioo (x 0) (x (Fin.last n)))] f) :
    √(∑ i, ∫ s in x i.castSucc..x i.succ, (f s - (proj x r f i).eval s) ^ 2)
      ≤ h ^ (r + 1) * seminorm (r + 1) (x 0) (x (Fin.last n)) U := by
  have hab : x 0 < x (Fin.last n) := hx.out (Fin.pos_iff_ne_zero.2 (Fin.ne_of_val_ne hn.ne'))
  have hfi : IntervalIntegrable f volume (x 0) (x (Fin.last n)) :=
    (hf.mono (uIcc_of_le hab.le).le).intervalIntegrable
  have hfi2 : IntervalIntegrable (fun s => f s ^ 2) volume (x 0) (x (Fin.last n)) :=
    ((hf.mono (uIcc_of_le hab.le).le).pow 2).intervalIntegrable
  exact (Real.sqrt_le_sqrt (sum_integral_sq_sub_proj_le hfi hfi2 _)).trans
    (sqrt_sum_integral_sq_sub_interp_le_seminorm hn hnode hmesh U hf hU)

open SobolevInterval in
/-- **The $H^1$ estimate of the projection error.** Let the partition be strictly increasing with
$n \ge 1$ panels whose lengths satisfy $h_{\min} \le x_{i+1} - x_i \le h$, where $h_{\min} > 0$,
and let it carry a node system of degree $r$. Let $U \in H^{r+1}(x_0, x_n)$ with weak derivative
$U'$, and let $f$ be a representative of $U$ that is continuous on $[x_0, x_n]$. Then
$$\Bigl(\sum_{i=0}^{n-1} \int_{I_i} \bigl(U' - (P f)_i'\bigr)^2\Bigr)^{1/2} \le h^r \Bigl(1 + 4
  r (r + 1) \frac{h}{h_{\min}}\Bigr) |U|_{H^{r+1}}.$$

The proof uses the triangle inequality through the interpolant, whose derivative error is at
most $h^r |U|_{H^{r+1}}$, and the Markov inequality for the difference of the interpolant and
the projection, whose $L^2$ norm is at most twice the $L^2$ error of the interpolant. -/
theorem sqrt_sum_integral_sq_deriv_sub_proj_le_seminorm (hn : 0 < n) (hnode : IsNodes x r node)
    {h hmin : ℝ} (hmesh : ∀ i : Fin n, x i.succ - x i.castSucc ≤ h) (h0 : 0 < hmin)
    (hminle : ∀ i : Fin n, hmin ≤ x i.succ - x i.castSucc)
    (U : SobolevInterval (r + 1) (x 0) (x (Fin.last n))) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (x 0) (x (Fin.last n))))
    (hU : fn U =ᵐ[volume.restrict (Ioo (x 0) (x (Fin.last n)))] f) :
    √(∑ i, ∫ s in x i.castSucc..x i.succ,
        (SobolevInterval.deriv U 1 s - (derivative (proj x r f i)).eval s) ^ 2)
      ≤ h ^ r * (1 + 4 * r * (r + 1) * (h / hmin)) * seminorm (r + 1) (x 0) (x (Fin.last n)) U := by
  have hab : x 0 < x (Fin.last n) := hx.out (Fin.pos_iff_ne_zero.2 (Fin.ne_of_val_ne hn.ne'))
  have hm : Monotone x := hx.out.monotone
  have hfi : IntervalIntegrable f volume (x 0) (x (Fin.last n)) :=
    (hf.mono (uIcc_of_le hab.le).le).intervalIntegrable
  have hfi2 : IntervalIntegrable (fun s => f s ^ 2) volume (x 0) (x (Fin.last n)) :=
    ((hf.mono (uIcc_of_le hab.le).le).pow 2).intervalIntegrable
  have hg := intervalIntegrable_deriv hab.le U 1
  have hg2 := intervalIntegrable_deriv_sq hab.le U 1
  set S := seminorm (r + 1) (x 0) (x (Fin.last n)) U with hS
  have hS0 : 0 ≤ S := apply_nonneg _ _
  set I := interp hnode f with hI
  set P := proj x r f with hP
  -- the interpolation errors
  have hEI : √(∑ i, ∫ s in x i.castSucc..x i.succ, (f s - (I i).eval s) ^ 2) ≤ h ^ (r + 1) * S :=
    sqrt_sum_integral_sq_sub_interp_le_seminorm hn hnode hmesh U hf hU
  have hEI' : √(∑ i, ∫ s in x i.castSucc..x i.succ,
      (SobolevInterval.deriv U 1 s - (derivative (I i)).eval s) ^ 2) ≤ h ^ r * S :=
    sqrt_sum_integral_sq_deriv_sub_interp_le_seminorm hn hnode hmesh U hf hU
  have hEP : √(∑ i, ∫ s in x i.castSucc..x i.succ, (f s - (P i).eval s) ^ 2) ≤ h ^ (r + 1) * S :=
    sqrt_sum_integral_sq_sub_proj_le_seminorm hn hnode hmesh U hf hU
  -- `‖I - P‖ ≤ 2 h^{r+1} S`
  have hIP : ‖I - P‖ ≤ 2 * (h ^ (r + 1) * S) := by
    have := norm_sub_le_sqrt_add_sqrt hfi hfi2 I P
    linarith
  -- Markov for `I - P`
  have hMarkov : √(∑ i, ∫ s in x i.castSucc..x i.succ, (derivative ((I - P) i)).eval s ^ 2)
      ≤ 2 * r * (r + 1) / hmin * ‖I - P‖ := by
    calc √(∑ i, ∫ s in x i.castSucc..x i.succ, (derivative ((I - P) i)).eval s ^ 2)
        ≤ √((2 * r * (r + 1) / hmin) ^ 2 * ‖I - P‖ ^ 2) :=
          Real.sqrt_le_sqrt (sum_integral_sq_derivative_le h0 hminle (I - P))
      _ = 2 * r * (r + 1) / hmin * ‖I - P‖ := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity),
            Real.sqrt_sq (norm_nonneg _)]
  -- the triangle inequality
  have htri := sqrt_sum_integral_add_sq_le hm
    (f := fun i s => SobolevInterval.deriv U 1 s - (derivative (I i)).eval s)
    (g := fun i s => (derivative ((I - P) i)).eval s)
    (fun i => (intervalIntegrable_panel hm hg i).sub
      ((derivative (I i)).continuous.intervalIntegrable _ _))
    (fun i => intervalIntegrable_sub_sq (intervalIntegrable_panel hm hg i)
      (intervalIntegrable_panel hm hg2 i) (derivative (I i)).continuous.continuousOn)
    (fun i => (derivative ((I - P) i)).continuous.intervalIntegrable _ _)
    (fun i => ((derivative ((I - P) i)).continuous.pow 2).intervalIntegrable _ _)
  have e : ∑ i, ∫ s in x i.castSucc..x i.succ,
      (SobolevInterval.deriv U 1 s - (derivative (I i)).eval s
        + (derivative ((I - P) i)).eval s) ^ 2
      = ∑ i, ∫ s in x i.castSucc..x i.succ,
        (SobolevInterval.deriv U 1 s - (derivative (P i)).eval s) ^ 2 :=
    Finset.sum_congr rfl fun i _ => integral_congr fun s _ => by
      simp only [sub_apply, derivative_sub, eval_sub]; ring
  rw [e] at htri
  calc √(∑ i, ∫ s in x i.castSucc..x i.succ,
          (SobolevInterval.deriv U 1 s - (derivative (P i)).eval s) ^ 2)
      ≤ h ^ r * S + 2 * r * (r + 1) / hmin * (2 * (h ^ (r + 1) * S)) := by
        have := mul_le_mul_of_nonneg_left hIP (by positivity : 0 ≤ 2 * r * (r + 1) / hmin)
        linarith
    _ = h ^ r * (1 + 4 * r * (r + 1) * (h / hmin)) * S := by
        rw [pow_succ]; field_simp; ring

/-- **The trace estimate for a panelwise error.** Let the partition be strictly increasing, with
panel lengths $h_{\min} \le x_{i+1} - x_i \le h$, where $h_{\min} > 0$. Let $f$ be continuous on
$[x_0, x_n]$, and let $g$ be a function such that $g$ and $g^2$ are integrable on $[x_0, x_n]$
and $f(t) - f(s) = \int_s^t g$ for all $s, t \in [x_0, x_n]$. Let $P$ be a broken polynomial,
let $y_i \in I_i$ for each $i$, and let $c_i \le C$ for each $i$, where $C \ge 0$. Then
$$\sum_{i=0}^{n-1} c_i \bigl(f(y_i) - P_i(y_i)\bigr)^2 \le C \Bigl(\frac{2}{h_{\min}}
  \sum_{i=0}^{n-1} \int_{I_i} (f - P_i)^2 + 2 h \sum_{i=0}^{n-1} \int_{I_i} (g -
  P_i')^2\Bigr).$$
The proof sums the panel trace inequality `sq_le_of_sub_eq_integral` over the panels. -/
theorem sum_mul_sq_sub_eval_le {f g : ℝ → ℝ} (hf : ContinuousOn f (Icc (x 0) (x (Fin.last n))))
    (hg : IntervalIntegrable g volume (x 0) (x (Fin.last n)))
    (hg2 : IntervalIntegrable (fun s => g s ^ 2) volume (x 0) (x (Fin.last n)))
    (hfg : ∀ s ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc (x 0) (x (Fin.last n)),
      f t - f s = ∫ q in s..t, g q)
    {h hmin : ℝ} (hmesh : ∀ i : Fin n, x i.succ - x i.castSucc ≤ h) (h0 : 0 < hmin)
    (hminle : ∀ i : Fin n, hmin ≤ x i.succ - x i.castSucc) (P : BrokenPolynomial x r)
    {y : Fin n → ℝ} (hy : ∀ i, y i ∈ Icc (x i.castSucc) (x i.succ)) {c : Fin n → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hcC : ∀ i, c i ≤ C) :
    ∑ i, c i * (f (y i) - (P i).eval (y i)) ^ 2
      ≤ C * (2 / hmin * (∑ i, ∫ s in x i.castSucc..x i.succ, (f s - (P i).eval s) ^ 2)
        + 2 * h * ∑ i, ∫ s in x i.castSucc..x i.succ, (g s - (derivative (P i)).eval s) ^ 2) := by
  have hm : Monotone x := hx.out.monotone
  have hlt : ∀ i : Fin n, x i.castSucc < x i.succ := fun i => hx.out (Fin.castSucc_lt_succ (i := i))
  have hpanel : ∀ i : Fin n, c i * (f (y i) - (P i).eval (y i)) ^ 2
      ≤ C * (2 / hmin * (∫ s in x i.castSucc..x i.succ, (f s - (P i).eval s) ^ 2)
        + 2 * h * ∫ s in x i.castSucc..x i.succ, (g s - (derivative (P i)).eval s) ^ 2) := by
    intro i
    have hgi := intervalIntegrable_panel hm hg i
    have hgi2 := intervalIntegrable_panel hm hg2 i
    have hg' : IntervalIntegrable (fun s => g s - (derivative (P i)).eval s) volume
        (x i.castSucc) (x i.succ) := hgi.sub ((derivative (P i)).continuous.intervalIntegrable _ _)
    have hg'2 : IntervalIntegrable (fun s => (g s - (derivative (P i)).eval s) ^ 2) volume
        (x i.castSucc) (x i.succ) :=
      intervalIntegrable_sub_sq hgi hgi2 (derivative (P i)).continuous.continuousOn
    have hvg : ∀ s ∈ Icc (x i.castSucc) (x i.succ), ∀ t ∈ Icc (x i.castSucc) (x i.succ),
        (f t - (P i).eval t) - (f s - (P i).eval s)
          = ∫ q in s..t, (g q - (derivative (P i)).eval q) := by
      intro s hs t ht
      have hs' : s ∈ [[x i.castSucc, x i.succ]] := by rw [uIcc_of_le (hlt i).le]; exact hs
      have ht' : t ∈ [[x i.castSucc, x i.succ]] := by rw [uIcc_of_le (hlt i).le]; exact ht
      rw [integral_sub (hgi.mono_set (uIcc_subset_uIcc hs' ht'))
        (((derivative (P i)).continuous.intervalIntegrable _ _)),
        integral_eq_sub_of_hasDerivAt (fun q _ => (P i).hasDerivAt q)
          ((derivative (P i)).continuous.intervalIntegrable _ _),
        ← hfg s (Icc_panel_subset hm i hs) t (Icc_panel_subset hm i ht)]
      ring
    have htr := sq_le_of_sub_eq_integral (hlt i) (v := fun s => f s - (P i).eval s)
      ((hf.mono (Icc_panel_subset hm i)).sub (P i).continuous.continuousOn) hg' hg'2 hvg (hy i)
    have hF : 0 ≤ ∫ s in x i.castSucc..x i.succ, (f s - (P i).eval s) ^ 2 :=
      integral_nonneg (hlt i).le fun _ _ => sq_nonneg _
    have hG : 0 ≤ ∫ s in x i.castSucc..x i.succ, (g s - (derivative (P i)).eval s) ^ 2 :=
      integral_nonneg (hlt i).le fun _ _ => sq_nonneg _
    have h1 : 2 / (x i.succ - x i.castSucc) ≤ 2 / hmin :=
      div_le_div_of_nonneg_left (by norm_num) h0 (hminle i)
    have h2 : 2 * (x i.succ - x i.castSucc) ≤ 2 * h := by linarith [hmesh i]
    calc c i * (f (y i) - (P i).eval (y i)) ^ 2 ≤ C * (f (y i) - (P i).eval (y i)) ^ 2 :=
          mul_le_mul_of_nonneg_right (hcC i) (sq_nonneg _)
      _ ≤ C * (2 / (x i.succ - x i.castSucc)
            * (∫ s in x i.castSucc..x i.succ, (f s - (P i).eval s) ^ 2)
          + 2 * (x i.succ - x i.castSucc)
            * ∫ s in x i.castSucc..x i.succ, (g s - (derivative (P i)).eval s) ^ 2) :=
          mul_le_mul_of_nonneg_left htr hC
      _ ≤ C * (2 / hmin * (∫ s in x i.castSucc..x i.succ, (f s - (P i).eval s) ^ 2)
          + 2 * h * ∫ s in x i.castSucc..x i.succ, (g s - (derivative (P i)).eval s) ^ 2) := by
          gcongr
  calc ∑ i, c i * (f (y i) - (P i).eval (y i)) ^ 2
      ≤ ∑ i, C * (2 / hmin * (∫ s in x i.castSucc..x i.succ, (f s - (P i).eval s) ^ 2)
          + 2 * h * ∫ s in x i.castSucc..x i.succ, (g s - (derivative (P i)).eval s) ^ 2) :=
        Finset.sum_le_sum fun i _ => hpanel i
    _ = C * (2 / hmin * (∑ i, ∫ s in x i.castSucc..x i.succ, (f s - (P i).eval s) ^ 2)
        + 2 * h * ∑ i, ∫ s in x i.castSucc..x i.succ, (g s - (derivative (P i)).eval s) ^ 2) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]

end ProjEstimates

end BrokenPolynomial

end
