/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Calculus.AnchoredLipschitzDerivs
import Numlib.Analysis.SpecialFunctions.FactorialSum
import Numlib.Data.Set.Basic
import Numlib.Optimization.ModelBased.HighOrder.Orders
import Numlib.Optimization.ModelBased.InexactTaylor

/-!
# Common bounds for the dynamic-accuracy methods

This file collects elementary bounds that the high-order methods with inexact derivatives and
dynamic accuracy of [cartis2022evaluation], Chapter 13, share: the trust-region methods TRqEDA and
TRqIDA and the regularization methods ARqpEDA and ARqpIDA. The smoothness hypothesis is
`LipschitzDerivsAnchored f C A 0 q L` (assumption f.D0qL of the source): $C$ is open and convex, the
set $A$ of anchors lies in $C$, $f$ is $q$ times continuously differentiable near every point of
$C$, and for $0 \le j \le q$ the derivative $\nabla^j f$ satisfies $\|\nabla^j f(y) - \nabla^j
f(x)\| \le L_j \|y - x\|$ for $x \in A$ and $y \in C$. With normalized constants $L_j \ge 1$, the
file gives Taylor's theorem at an anchor, the bound $\|\nabla^i f(x)\| \le L_f$ of (13.1.24) with
$L_f = \max_{0 \le j \le q} L_j$, and its inexact version $\|\overline{\nabla}^i f(x)\| \le L_f +
\kappa_{\nabla,\max} \kappa_h$ of (13.1.63).

## Main results

* `Optimization.one_le_lipMax`: if $L_j \ge 1$ for $j \le q$, then $L_f \ge 1$.
* `LipschitzDerivsAnchored.abs_sub_taylorDecrement_le_of_le`: Taylor's theorem of order $j \le q$ at
  an anchor.
* `LipschitzDerivsAnchored.norm_iteratedFDeriv_le_lipMax`: the bound (13.1.24) on the derivatives at
  an anchor.
* `LipschitzDerivsAnchored.norm_le_of_jetApprox`: the bound (13.1.63) on inexact derivatives at an
  anchor.
* `Optimization.taylorDecrement_le_two_mul`: the decrease of a Taylor polynomial along a step $s$
  with $\|s\| \le 1$ is at most $2 L \|s\|$.
-/

open Set
open scoped Nat

namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Let $L_0, \dots, L_q$ be real numbers with $L_j \ge 1$ for all $j \le q$. Then
$L_f = \max_{0 \le j \le q} L_j$ satisfies $L_f \ge 1$.

Here $L_f$ is `Optimization.lipMax L q`. -/
theorem one_le_lipMax {L : ℕ → ℝ} {q : ℕ} (hL : ∀ j ≤ q, 1 ≤ L j) : 1 ≤ lipMax L q :=
  (hL 0 (Nat.zero_le q)).trans (le_lipMax (Nat.zero_le q))

end Optimization

namespace LipschitzDerivsAnchored

open Optimization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {C A : Set E} {q : ℕ}
  {L : ℕ → ℝ}

/-- Taylor's theorem anchored at $x \in A$, as in (A.19) of [cartis2022evaluation]. Assume
`LipschitzDerivsAnchored f C A 0 q L`, let $j \le q$, let $x \in A$, and let $s \in E$ with
$x + s \in C$. Then
$$|f(x + s) - T_{f,j}(x, s)| \le \frac{L_j}{(j+1)!} \|s\|^{j+1},$$
where $T_{f,j}(x, s) = f(x) - \Delta T_{f,j}(x, s)$ is the Taylor polynomial of order $j$ of $f$
at $x$.

The decrement $\Delta T_{f,j}(x, s)$ is `(ftaylorSeries ℝ f x).taylorDecrement j s`. -/
theorem abs_sub_taylorDecrement_le_of_le (hf : LipschitzDerivsAnchored f C A 0 q L) {j : ℕ}
    (hj : j ≤ q) {x s : E} (hx : x ∈ A) (hxs : x + s ∈ C) :
    |f (x + s) - (f x - (ftaylorSeries ℝ f x).taylorDecrement j s)| ≤
      L j / ((j + 1)! : ℝ) * ‖s‖ ^ (j + 1) :=
  hf.abs_sub_taylorDecrement_le (Finset.mem_Icc.2 ⟨Nat.zero_le j, hj⟩) hx hxs

/-- Assume `LipschitzDerivsAnchored f C A 0 q L`, let $j \le q$ and let $x \in A$. Then $\|\nabla^j
f(y) - \nabla^j f(x)\| \le L_j \|y - x\|$ for every $y \in C$. -/
theorem lipschitzAt_of_le (hf : LipschitzDerivsAnchored f C A 0 q L) {j : ℕ} (hj : j ≤ q) {x : E}
    (hx : x ∈ A) :
    ∀ y ∈ C, ‖iteratedFDeriv ℝ j f y - iteratedFDeriv ℝ j f x‖ ≤ L j * ‖y - x‖ :=
  hf.lipschitzAt (Finset.mem_Icc.2 ⟨Nat.zero_le j, hj⟩) hx

/-- Assume `LipschitzDerivsAnchored f C C 0 q L`, in which every point of $C$ is an anchor, and let
$j \le q$. Then $\nabla^j f$ is Lipschitz on $C$ with constant $L_j$. -/
theorem lipschitzOn_of_le (hf : LipschitzDerivsAnchored f C C 0 q L) {j : ℕ} (hj : j ≤ q) :
    IteratedFDerivLipschitzOn f j (L j) C :=
  hf.lipschitzOn (Finset.mem_Icc.2 ⟨Nat.zero_le j, hj⟩)

/-- The bound (13.1.24) of [cartis2022evaluation] at the anchors. Assume
`LipschitzDerivsAnchored f C A 0 q L` and $L_j \ge 1$ for all $j \le q$. Then for
$1 \le i \le q$ and $x \in A$,
$$\|\nabla^i f(x)\| \le L_f = \max_{0 \le j \le q} L_j.$$

The proof gives $\|\nabla^i f(x)\| \le L_{i-1}$ from the Lipschitz condition on
$\nabla^{i-1} f$, and $L_{i-1} \le L_f$. Here $L_f$ is `Optimization.lipMax L q`. -/
theorem norm_iteratedFDeriv_le_lipMax (hf : LipschitzDerivsAnchored f C A 0 q L)
    (hL : ∀ j ≤ q, 1 ≤ L j) {i : ℕ} (hi : i ∈ Finset.Icc 1 q) {x : E} (hx : x ∈ A) :
    ‖iteratedFDeriv ℝ i f x‖ ≤ lipMax L q := by
  obtain ⟨hi1, hiq⟩ := Finset.mem_Icc.1 hi
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  have hm : m ≤ q := by omega
  exact (hf.norm_iteratedFDeriv_le (Finset.mem_Icc.2 ⟨Nat.zero_le m, hm⟩)
    (zero_le_one.trans (hL m hm)) hx).trans (le_lipMax hm)

/-- The bounds (13.1.24) and (13.1.63) of [cartis2022evaluation] for inexact derivatives at the
anchors. Assume `LipschitzDerivsAnchored f C A 0 q L` and $L_j \ge 1$ for all $j \le q$. Let
$x \in A$, and let $\overline{\nabla}^1 f(x), \dots, \overline{\nabla}^q f(x)$ be inexact
derivatives with
$$\|\overline{\nabla}^i f(x) - \nabla^i f(x)\| \le \kappa_{\nabla,i} h_i \qquad (1 \le i \le
  q),$$
where $\kappa_{\nabla,i} \ge 0$ and $0 \le h_i \le \kappa_h$ for $1 \le i \le q$. Then for
$1 \le i \le q$,
$$\|\overline{\nabla}^i f(x)\| \le L_f + \kappa_{\nabla,\max} \kappa_h,$$
with $L_f = \max_{0 \le j \le q} L_j$ and $\kappa_{\nabla,\max} = \max_{1 \le i \le q}
\kappa_{\nabla,i}$.

The inexact derivatives are the terms `D i` of a formal multilinear series `D`, and the error
bound is `JetApprox (ftaylorSeries ℝ f x) D q (fun i => κg i * hh i)`. The constants are
`Optimization.lipMax L q` and `Optimization.ordMax q κg`. -/
theorem norm_le_of_jetApprox (hf : LipschitzDerivsAnchored f C A 0 q L) (hL : ∀ j ≤ q, 1 ≤ L j)
    {D : FormalMultilinearSeries ℝ E ℝ} {κg hh : ℕ → ℝ} {κh : ℝ} {x : E} (hx : x ∈ A)
    (hD : JetApprox (ftaylorSeries ℝ f x) D q (fun i => κg i * hh i))
    (hκ : ∀ i ∈ Finset.Icc 1 q, 0 ≤ κg i) (hh0 : ∀ i ∈ Finset.Icc 1 q, 0 ≤ hh i)
    (hhκ : ∀ i ∈ Finset.Icc 1 q, hh i ≤ κh) {i : ℕ} (hi : i ∈ Finset.Icc 1 q) :
    ‖D i‖ ≤ lipMax L q + ordMax q κg * κh :=
  norm_le_add_mul_of_jetApprox hD hi (hf.norm_iteratedFDeriv_le_lipMax hL hi hx) (hκ i hi)
    (le_ordMax hi) (hh0 i hi) (hhκ i hi)

end LipschitzDerivsAnchored

namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Let $D$ be a formal multilinear series on $E$, let $j \in \mathbb{N}$, and let $L \ge 0$ with
$\|D_i\| \le L$ for $1 \le i \le j$. If $\|s\| \le 1$, then the decrement of the Taylor
polynomial of order $j$ satisfies
$$\Delta T_j(s) \le 2 L \|s\|.$$

The proof uses the bound $\sum_{i \ge 1} 1/i! < 2$ of (A.34) of [cartis2022evaluation]. -/
theorem taylorDecrement_le_two_mul {D : FormalMultilinearSeries ℝ E ℝ} {j : ℕ} {Lb : ℝ}
    (hLb : 0 ≤ Lb) (hD : ∀ i ∈ Finset.Icc 1 j, ‖D i‖ ≤ Lb) {s : E} (hs : ‖s‖ ≤ 1) :
    D.taylorDecrement j s ≤ 2 * Lb * ‖s‖ := by
  refine (le_abs_self _).trans ((D.abs_taylorDecrement_le j s).trans ?_)
  calc ∑ i ∈ Finset.Icc 1 j, ‖D i‖ * ‖s‖ ^ i / i !
      ≤ ∑ i ∈ Finset.Icc 1 j, Lb * (‖s‖ ^ i / i !) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [mul_div_assoc]
        gcongr
        exact hD i hi
    _ = Lb * ∑ i ∈ Finset.Icc 1 j, ‖s‖ ^ i / i ! := by rw [Finset.mul_sum]
    _ ≤ Lb * (2 * ‖s‖) := by gcongr; exact sum_pow_div_factorial_le_two_mul (norm_nonneg s) hs j
    _ = 2 * Lb * ‖s‖ := by ring

/-- Let $u_0, \dots, u_k$ be real numbers with $u_{i+1} \le u_i$ for $i < k$. Then $u_k \le u_0$. -/
theorem le_zero_of_forall_succ_le {u : ℕ → ℝ} {k : ℕ} (h : ∀ i < k, u (i + 1) ≤ u i) :
    u k ≤ u 0 := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact (h k k.lt_succ_self).trans (ih fun i hi => h i (hi.trans k.lt_succ_self))

end Optimization
