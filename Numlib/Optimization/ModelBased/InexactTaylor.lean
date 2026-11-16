/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Optimality.Approximate
import Numlib.Analysis.Calculus.Gradient
import Numlib.Analysis.Calculus.LipschitzIteratedFDeriv
import Numlib.Analysis.SpecialFunctions.FactorialSum

/-!
# Inexact derivative data and Taylor decrements

Methods with dynamic accuracy ([cartis2022evaluation], §13.1.2 and §13.3) build their models from
inexact derivatives $\overline{\nabla^i_x f}(x)$. Here a jet is a sequence $D = (D_i)_{i \ge 0}$ in
which $D_i$ is a continuous $i$-linear form on $E$; the exact jet of $f$ at $x$ has
$D_i = \nabla^i f(x)$. An inexact jet $\bar D$ is another jet. It **approximates $D$ up to order $p$
with errors $e_i$** if $\|\bar D_i - D_i\| \le e_i$ for $1 \le i \le p$. The error model (13.1.2) of
the source, $\|\bar D_i - D_i\| \le \kappa_{\nabla,i} h_{k,i}$, and the explicit model (13.3.4) with
$\kappa_{\nabla,i} = 1$ both have this form, with $e_i = \kappa_i h_i$.

For a jet $D$, write $T_j(D, s) = \sum_{i=0}^{j} D_i[s]^i/i!$ for its Taylor sum of degree $j$,
$\Delta T_j(D, s) = T_j(D, 0) - T_j(D, s)$ for its Taylor decrement, and $\phi^\delta_j(D) =
\sup\{\Delta T_j(D, d) : \|d\| \le \delta,\ d \in S\}$ for its Taylor-decrement measure over a set
$S$ of displacements. The results bound the differences of these quantities for two jets by the
errors $e_i$. They hold for arbitrary jets $D$ and $\bar D$, so they also serve comparisons of one
model with another. The decrement $\Delta T_j(\bar D, s)$ does not involve $\bar D_0$; function
values enter only through the Taylor sum ((13.1.4), (13.1.7), (13.3.11)).

## Main definitions

* `Optimization.JetApprox`: $\bar D$ approximates $D$ up to order $p$ with errors $e_i$, that is,
  $\|\bar D_i - D_i\| \le e_i$ for $1 \le i \le p$.
* `Optimization.gradientJet`, `Optimization.hessianJet`: a jet with its first-order term replaced by
  an approximate gradient, or its second-order term replaced by an approximate Hessian.

## Main results

* `Optimization.norm_le_of_jetApprox`: $\|\bar D_i\| \le \|D_i\| + e_i$ ((13.1.24), (13.1.63)).
* `Optimization.abs_taylorDecrement_sub_le_of_jetApprox`: $|\Delta T_j(\bar D, s) - \Delta T_j(D,
  s)| \le \sum_{i=1}^j e_i\|s\|^i/i!$, which is (13.1.3);
  `Optimization.abs_taylorDecrement_sub_le_two_mul_of_jetApprox` is its form for $\|s\| \le 1$.
* `Optimization.abs_taylorDecrement_sub_le_of_stepAccuracy`: data accurate relative to the step give
  a decrement error of order $\|s\|^{r+1}$ ((13.1.9) implies (13.1.10), and (13.1.46) implies
  (13.1.47)).
* `Optimization.abs_taylorSum_sub_le_of_jetApprox`: the error of the model values ((13.1.4),
  (13.1.7)–(13.1.8), (13.3.11)).
* `Optimization.taylorMeasure_le_add_of_jetApprox`: $\phi^\delta_j(D) \le \phi^\delta_j(\bar D) +
  \sum_{i=1}^j e_i\delta^i/i!$ ((13.1.6)).
* `Optimization.taylorMeasure_le_of_inexact_certificate`: the certification of approximate
  optimality from inexact data, the common core of Lemmas 13.1.7, 13.1.15, 13.3.3(i) and 13.3.6(i).
* `Optimization.jetApprox_gradientJet`, `Optimization.jetApprox_hessianJet`: an approximate gradient
  or an approximate Hessian gives an approximate jet.

## Implementation notes

* A jet is a `FormalMultilinearSeries ℝ E ℝ`, and the exact jet of $f$ at $x$ is
  `ftaylorSeries ℝ f x`. The norm $\|D_i\|$ is the operator norm of a continuous multilinear map.
* The Taylor sum, the decrement and the measure are `FormalMultilinearSeries.taylorSum`,
  `FormalMultilinearSeries.taylorDecrement` and `Optimization.taylorMeasure`.
* `Optimization.JetApprox` puts no condition on the terms of order $0$.
-/

open Set Metric Finset
open scoped Nat

namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Approximate jets -/

section JetApprox

variable {D D' Dbar : FormalMultilinearSeries ℝ E ℝ} {p p' : ℕ} {err err' : ℕ → ℝ}

/-- Let $D$ and $\bar D$ be jets, $p \in \mathbb{N}$ and $e : \mathbb{N} \to \mathbb{R}$. The jet
$\bar D$ **approximates $D$ up to order $p$ with errors $e$** if
$$\|\bar D_i - D_i\| \le e_i \quad \text{for } 1 \le i \le p.$$
The terms $D_0$ and $\bar D_0$ are not constrained. This is the error model (13.1.2) of
[cartis2022evaluation] with $e_i = \kappa_{\nabla,i} h_{k,i}$, and (13.3.4) with
$e_i = h_{k,i}$. -/
def JetApprox (D Dbar : FormalMultilinearSeries ℝ E ℝ) (p : ℕ) (err : ℕ → ℝ) : Prop :=
  ∀ i ∈ Finset.Icc 1 p, ‖Dbar i - D i‖ ≤ err i

/-- `Optimization.JetApprox D Dbar p err` holds if and only if $\|\bar D_i - D_i\| \le e_i$ for
$1 \le i \le p$. -/
theorem jetApprox_iff :
    JetApprox D Dbar p err ↔ ∀ i ∈ Finset.Icc 1 p, ‖Dbar i - D i‖ ≤ err i := Iff.rfl

/-- Every jet approximates itself up to every order with zero errors. -/
theorem jetApprox_self (D : FormalMultilinearSeries ℝ E ℝ) (p : ℕ) : JetApprox D D p 0 :=
  fun i _ => by simp

/-- If $\bar D$ approximates $D$ up to order $p$ with errors $e$, then $D$ approximates $\bar D$ up
to order $p$ with errors $e$. -/
theorem JetApprox.symm (h : JetApprox D Dbar p err) : JetApprox Dbar D p err :=
  fun i hi => norm_sub_rev (D i) (Dbar i) ▸ h i hi

/-- If $\bar D$ approximates $D$ up to order $p$ with errors $e$, and $e_i \le e'_i$ for
$1 \le i \le p$, then $\bar D$ approximates $D$ up to order $p$ with errors $e'$. -/
theorem JetApprox.mono_err (h : JetApprox D Dbar p err)
    (herr : ∀ i ∈ Finset.Icc 1 p, err i ≤ err' i) : JetApprox D Dbar p err' :=
  fun i hi => (h i hi).trans (herr i hi)

/-- If $\bar D$ approximates $D$ up to order $p$ with errors $e$, then it approximates $D$ up to
every order $p' \le p$ with the same errors. -/
theorem JetApprox.mono (h : JetApprox D Dbar p err) (hp : p' ≤ p) : JetApprox D Dbar p' err :=
  fun i hi => h i (Icc_subset_Icc le_rfl hp hi)

/-- If $\bar D$ approximates $D$ up to order $p$ with errors $e$, then $e_i \ge 0$ for
$1 \le i \le p$. -/
theorem JetApprox.nonneg (h : JetApprox D Dbar p err) {i : ℕ} (hi : i ∈ Finset.Icc 1 p) :
    0 ≤ err i :=
  (norm_nonneg _).trans (h i hi)

/-- **Norms of inexact derivatives.** Let $\bar D$ approximate $D$ up to order $p$ with errors $e$,
and let $1 \le i \le p$. Then
$$\|\bar D_i\| \le \|D_i\| + e_i.$$
This is the bound in (13.1.24) and (13.1.63) of [cartis2022evaluation]. -/
theorem norm_le_of_jetApprox (h : JetApprox D Dbar p err) {i : ℕ} (hi : i ∈ Finset.Icc 1 p) :
    ‖Dbar i‖ ≤ ‖D i‖ + err i := by
  calc ‖Dbar i‖ = ‖D i + (Dbar i - D i)‖ := by rw [add_sub_cancel]
    _ ≤ ‖D i‖ + ‖Dbar i - D i‖ := norm_add_le _ _
    _ ≤ ‖D i‖ + err i := by gcongr; exact h i hi

/-- Let $\bar D$ approximate $D$ up to order $p$ with errors $e_i = \kappa_i h_i$, and let
$1 \le i \le p$. If $\|D_i\| \le L$, $0 \le \kappa_i \le \kappa_{\max}$ and
$0 \le h_i \le \kappa_h$, then $\|\bar D_i\| \le L + \kappa_{\max}\kappa_h$. This is (13.1.24)
and (13.1.63) of [cartis2022evaluation] with the constants of the source. -/
theorem norm_le_add_mul_of_jetApprox {κ hh : ℕ → ℝ} {L κmax κh : ℝ}
    (h : JetApprox D Dbar p (fun i => κ i * hh i)) {i : ℕ} (hi : i ∈ Finset.Icc 1 p)
    (hD : ‖D i‖ ≤ L) (hκ : 0 ≤ κ i) (hκmax : κ i ≤ κmax) (hh0 : 0 ≤ hh i) (hhh : hh i ≤ κh) :
    ‖Dbar i‖ ≤ L + κmax * κh := by
  have := norm_le_of_jetApprox h hi
  have : κ i * hh i ≤ κmax * κh := mul_le_mul hκmax hhh hh0 (hκ.trans hκmax)
  linarith

/-- Let $C \subseteq E$ be open, $x \in C$ and $L \ge 0$, and let the $i$-th derivative $\nabla^i f$
be $L$-Lipschitz on $C$. If $\bar D$ approximates the jet of $f$ at $x$ up to an order
$p \ge i + 1$ with errors $e$, then $\|\bar D_{i+1}\| \le L + e_{i+1}$. This is (13.1.24) of
[cartis2022evaluation] for the jet of a function. -/
theorem norm_le_of_jetApprox_of_lipschitz {f : E → ℝ} {x : E} {C : Set E} {L : ℝ} {i : ℕ}
    (h : JetApprox (ftaylorSeries ℝ f x) Dbar p err) (hi : i + 1 ≤ p) (hC : IsOpen C)
    (hL0 : 0 ≤ L) (hL : IteratedFDerivLipschitzOn f i L C) (hx : x ∈ C) :
    ‖Dbar (i + 1)‖ ≤ L + err (i + 1) := by
  have h1 := norm_le_of_jetApprox h (mem_Icc.2 ⟨Nat.le_add_left 1 i, hi⟩)
  have h2 : ‖ftaylorSeries ℝ f x (i + 1)‖ ≤ L :=
    norm_iteratedFDeriv_succ_le_of_lipschitzOn hC hL0 hL hx
  linarith

end JetApprox

/-! ### Decrements, model values and measures -/

section Bounds

variable {D Dbar : FormalMultilinearSeries ℝ E ℝ} {p j : ℕ} {err : ℕ → ℝ} {s : E}

/-- Let $\bar D$ approximate $D$ up to order $p$ with errors $e$, let $j \le p$ and $s \in E$. Then
$$|\Delta T_j(\bar D, s) - \Delta T_j(D, s)| \le \sum_{i=1}^{j} \frac{e_i\|s\|^i}{i!}.$$
This is (13.1.3) of [cartis2022evaluation]. -/
theorem abs_taylorDecrement_sub_le_of_jetApprox (h : JetApprox D Dbar p err) (hj : j ≤ p)
    (s : E) :
    |Dbar.taylorDecrement j s - D.taylorDecrement j s| ≤
      ∑ i ∈ Finset.Icc 1 j, err i * ‖s‖ ^ i / i ! := by
  refine (Dbar.abs_taylorDecrement_sub_le D j s).trans (sum_le_sum fun i hi => ?_)
  gcongr
  exact h i (Icc_subset_Icc le_rfl hj hi)

/-- Let $\bar D$ approximate $D$ up to order $p$ with errors $e$, let $j \le p$ and $\|s\| \le 1$,
and let $e_{\max} \ge 0$ with $e_i \le e_{\max}$ for $1 \le i \le j$. Then
$$|\Delta T_j(\bar D, s) - \Delta T_j(D, s)| \le 2e_{\max}\|s\|,$$
which is at most $2e_{\max}$. This is (13.1.3) of [cartis2022evaluation] in the form of
(13.1.6); the proof uses the sum bound (A.34). -/
theorem abs_taylorDecrement_sub_le_two_mul_of_jetApprox {e : ℝ} (h : JetApprox D Dbar p err)
    (hj : j ≤ p) (hs : ‖s‖ ≤ 1) (he : ∀ i ∈ Finset.Icc 1 j, err i ≤ e) (he0 : 0 ≤ e) :
    |Dbar.taylorDecrement j s - D.taylorDecrement j s| ≤ 2 * e * ‖s‖ := by
  calc |Dbar.taylorDecrement j s - D.taylorDecrement j s|
      ≤ ∑ i ∈ Finset.Icc 1 j, err i * ‖s‖ ^ i / i ! :=
        abs_taylorDecrement_sub_le_of_jetApprox h hj s
    _ ≤ ∑ i ∈ Finset.Icc 1 j, e * (‖s‖ ^ i / i !) := by
        refine sum_le_sum fun i hi => ?_
        rw [mul_div_assoc]
        gcongr
        exact he i hi
    _ = e * ∑ i ∈ Finset.Icc 1 j, ‖s‖ ^ i / i ! := by rw [mul_sum]
    _ ≤ e * (2 * ‖s‖) := by gcongr; exact sum_pow_div_factorial_le_two_mul (norm_nonneg s) hs j
    _ = 2 * e * ‖s‖ := by ring

/-- **Step-scaled accuracy.** Let $\kappa, \kappa_s \ge 0$, let $\bar D$ approximate $D$ up to order
$r$ with errors $e$, and let $e_i \le \kappa\kappa_s\|s\|^{r-i+1}$ for $1 \le i \le r$. Then for
every $j \le r$,
$$|\Delta T_j(\bar D, s) - \Delta T_j(D, s)| \le 2\kappa_s\kappa\|s\|^{r+1}.$$
This is the implication from (13.1.9) to (13.1.10), and from (13.1.46) to (13.1.47), of
[cartis2022evaluation].

Each term of the sum in (13.1.3) is at most $\kappa\kappa_s\|s\|^{r+1}/i!$, and
$\sum_{i=1}^j 1/i! \le 2$. -/
theorem abs_taylorDecrement_sub_le_of_stepAccuracy {r : ℕ} {κ κs : ℝ} (hκ : 0 ≤ κ)
    (hκs : 0 ≤ κs) (h : JetApprox D Dbar r err)
    (herr : ∀ i ∈ Finset.Icc 1 r, err i ≤ κ * κs * ‖s‖ ^ (r - i + 1)) (hj : j ≤ r) :
    |Dbar.taylorDecrement j s - D.taylorDecrement j s| ≤ 2 * κs * κ * ‖s‖ ^ (r + 1) := by
  calc |Dbar.taylorDecrement j s - D.taylorDecrement j s|
      ≤ ∑ i ∈ Finset.Icc 1 j, err i * ‖s‖ ^ i / i ! :=
        abs_taylorDecrement_sub_le_of_jetApprox h hj s
    _ ≤ ∑ i ∈ Finset.Icc 1 j, κ * κs * ‖s‖ ^ (r + 1) * ((1 : ℝ) ^ i / i !) := by
        refine sum_le_sum fun i hi => ?_
        have hir : i ≤ r := (mem_Icc.1 hi).2.trans hj
        have hpow : ‖s‖ ^ (r - i + 1) * ‖s‖ ^ i = ‖s‖ ^ (r + 1) := by
          rw [← pow_add]; congr 1; omega
        rw [one_pow, mul_one_div, ← hpow, ← mul_assoc]
        gcongr
        exact herr i (Icc_subset_Icc le_rfl hj hi)
    _ = κ * κs * ‖s‖ ^ (r + 1) * ∑ i ∈ Finset.Icc 1 j, (1 : ℝ) ^ i / i ! := by rw [mul_sum]
    _ ≤ κ * κs * ‖s‖ ^ (r + 1) * 2 := by
        gcongr
        simpa using sum_pow_div_factorial_le_two_mul zero_le_one le_rfl j
    _ = 2 * κs * κ * ‖s‖ ^ (r + 1) := by ring

/-- For jets $D$ and $\bar D$, $j \in \mathbb{N}$ and $s \in E$, the difference of the Taylor sums
is the difference of the values at $0$ minus the difference of the decrements:
$$T_j(\bar D, s) - T_j(D, s) = \bigl(T_j(\bar D, 0) - T_j(D, 0)\bigr) - \bigl(\Delta T_j(\bar D,
  s) - \Delta T_j(D, s)\bigr).$$
-/
theorem taylorSum_sub_eq (D Dbar : FormalMultilinearSeries ℝ E ℝ) (j : ℕ) (s : E) :
    Dbar.taylorSum j s - D.taylorSum j s =
      (Dbar.taylorSum j 0 - D.taylorSum j 0) -
        (Dbar.taylorDecrement j s - D.taylorDecrement j s) := by
  simp only [FormalMultilinearSeries.taylorDecrement]
  ring

/-- Let $\bar D$ approximate $D$ up to order $p$ with errors $e$, let $j \le p$ and $s \in E$. Then
$$|T_j(\bar D, s) - T_j(D, s)| \le |T_j(\bar D, 0) - T_j(D, 0)| + \sum_{i=1}^{j}
  \frac{e_i\|s\|^i}{i!}.$$
Here $T_j(D, 0) = D_0$ is the term of order $0$, the function value. This is (13.1.4) of
[cartis2022evaluation]. -/
theorem abs_taylorSum_sub_le_of_jetApprox (h : JetApprox D Dbar p err) (hj : j ≤ p) (s : E) :
    |Dbar.taylorSum j s - D.taylorSum j s| ≤
      |Dbar.taylorSum j 0 - D.taylorSum j 0| + ∑ i ∈ Finset.Icc 1 j, err i * ‖s‖ ^ i / i ! := by
  rw [taylorSum_sub_eq]
  exact (abs_sub _ _).trans (add_le_add le_rfl (abs_taylorDecrement_sub_le_of_jetApprox h hj s))

/-- If the values at $0$ agree, $T_j(\bar D, 0) = T_j(D, 0)$ (exact function values), then for every
$s \in E$ the model error is minus the decrement error:
$$T_j(\bar D, s) - T_j(D, s) = -\bigl(\Delta T_j(\bar D, s) - \Delta T_j(D, s)\bigr).$$
This is (13.1.7)–(13.1.8) of [cartis2022evaluation]. -/
theorem taylorSum_sub_eq_of_value_eq (h0 : Dbar.taylorSum j 0 = D.taylorSum j 0) (s : E) :
    Dbar.taylorSum j s - D.taylorSum j s =
      -(Dbar.taylorDecrement j s - D.taylorDecrement j s) := by
  rw [taylorSum_sub_eq, h0, sub_self, zero_sub]

/-- Let $\kappa, \kappa_s \ge 0$, let $\bar D$ approximate $D$ up to order $r$ with errors
$e_i \le \kappa\kappa_s\|s\|^{r-i+1}$ for $1 \le i \le r$, let $j \le r$, and let the values be
inexact with $|T_j(\bar D, 0) - T_j(D, 0)| \le h_0$. Then
$$|T_j(\bar D, s) - T_j(D, s)| \le h_0 + 2\kappa_s\kappa\|s\|^{r+1}.$$
This is (13.3.11) of [cartis2022evaluation]. -/
theorem abs_taylorSum_sub_le_of_stepAccuracy {r : ℕ} {κ κs h₀ : ℝ} (hκ : 0 ≤ κ) (hκs : 0 ≤ κs)
    (h : JetApprox D Dbar r err)
    (herr : ∀ i ∈ Finset.Icc 1 r, err i ≤ κ * κs * ‖s‖ ^ (r - i + 1)) (hj : j ≤ r)
    (h0 : |Dbar.taylorSum j 0 - D.taylorSum j 0| ≤ h₀) :
    |Dbar.taylorSum j s - D.taylorSum j s| ≤ h₀ + 2 * κs * κ * ‖s‖ ^ (r + 1) := by
  rw [taylorSum_sub_eq]
  exact (abs_sub _ _).trans
    (add_le_add h0 (abs_taylorDecrement_sub_le_of_stepAccuracy hκ hκs h herr hj))

variable {δ : ℝ} {S : Set E}

/-- Let $\bar D$ approximate $D$ up to order $q$ with errors $e$, let $j \le q$, $\delta \ge 0$ and
$0 \in S$. Then
$$\phi^\delta_j(D) \le \phi^\delta_j(\bar D) + \sum_{i=1}^{j} \frac{e_i\delta^i}{i!}.$$
This is (13.1.6) of [cartis2022evaluation].

The measures are `Optimization.taylorMeasure D j δ S`. The approximation relation is symmetric
(`Optimization.JetApprox.symm`), so the bound also holds with $D$ and $\bar D$ exchanged. -/
theorem taylorMeasure_le_add_of_jetApprox {q : ℕ} (h : JetApprox D Dbar q err) (hj : j ≤ q)
    (h0 : (0 : E) ∈ S) (hδ : 0 ≤ δ) :
    taylorMeasure D j δ S ≤
      taylorMeasure Dbar j δ S + ∑ i ∈ Finset.Icc 1 j, err i * δ ^ i / i ! := by
  have habs := abs_taylorMeasure_sub_le D Dbar j h0 hδ
  have hsum : ∑ i ∈ Finset.Icc 1 j, ‖D i - Dbar i‖ * δ ^ i / i ! ≤
      ∑ i ∈ Finset.Icc 1 j, err i * δ ^ i / i ! := by
    refine sum_le_sum fun i hi => ?_
    rw [norm_sub_rev]
    gcongr
    exact h i (Icc_subset_Icc le_rfl hj hi)
  linarith [le_abs_self (taylorMeasure D j δ S - taylorMeasure Dbar j δ S)]

/-- Let $\bar D$ approximate $D$ up to order $q$ with errors $e$, let $j \le q$, $0 \in S$ and
$0 \le \delta \le 1$, and let $e_{\max} \ge 0$ with $e_i \le e_{\max}$ for $1 \le i \le j$. Then
$$\phi^\delta_j(D) \le \phi^\delta_j(\bar D) + 2e_{\max}\delta,$$
which is at most $\phi^\delta_j(\bar D) + 2e_{\max}$. This is (13.1.6) of [cartis2022evaluation]
with a uniform error; the source takes $e_{\max} = \kappa_{\nabla,\max} h_{k,\max}$. -/
theorem taylorMeasure_le_add_two_mul_of_jetApprox {q : ℕ} {e : ℝ} (h : JetApprox D Dbar q err)
    (hj : j ≤ q) (h0 : (0 : E) ∈ S) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (he : ∀ i ∈ Finset.Icc 1 j, err i ≤ e) (he0 : 0 ≤ e) :
    taylorMeasure D j δ S ≤ taylorMeasure Dbar j δ S + 2 * e * δ := by
  refine (taylorMeasure_le_add_of_jetApprox h hj h0 hδ).trans (add_le_add le_rfl ?_)
  calc ∑ i ∈ Finset.Icc 1 j, err i * δ ^ i / i ! ≤ ∑ i ∈ Finset.Icc 1 j, e * (δ ^ i / i !) := by
        refine sum_le_sum fun i hi => ?_
        rw [mul_div_assoc]
        gcongr
        exact he i hi
    _ = e * ∑ i ∈ Finset.Icc 1 j, δ ^ i / i ! := by rw [mul_sum]
    _ ≤ e * (2 * δ) := by gcongr; exact sum_pow_div_factorial_le_two_mul hδ hδ1 j
    _ = 2 * e * δ := by ring

/-- **Certification of approximate optimality from inexact data.** Let $\bar D$ approximate $D$ up
to order $q$ with errors $e$, let $j \le q$, $\delta \ge 0$, $0 \in S$, $\varsigma > 0$,
$\varepsilon \in \mathbb{R}$ and $d \in E$. Suppose that Step 1 found no significant inexact
decrease at order $j$,
$$\varsigma\,\phi^\delta_j(\bar D) \le \Delta T_j(\bar D, d) \le
  \frac{\varsigma\varepsilon\delta^j}{2\,j!},$$
and that the data are accurate enough at the radius $\delta$,
$$\sum_{i=1}^{j} \frac{e_i\delta^i}{i!} \le \frac{\varepsilon\delta^j}{2\,j!}.$$
Then the exact measure satisfies $\phi^\delta_j(D) \le \varepsilon\delta^j/j!$, which is
(12.1.25) at order $j$. This is the common core of the proofs of Lemmas 13.1.7, 13.1.15,
13.3.3(i) and 13.3.6(i) of [cartis2022evaluation].

No bound $\delta \le 1$, $\varsigma \le 1$, $\varepsilon \ge 0$ or $\|d\| \le \delta$ is needed. -/
theorem taylorMeasure_le_of_inexact_certificate {q : ℕ} {ς ε : ℝ} {d : E}
    (h : JetApprox D Dbar q err) (hj : j ≤ q) (h0 : (0 : E) ∈ S) (hδ : 0 ≤ δ) (hς : 0 < ς)
    (hφ : ς * taylorMeasure Dbar j δ S ≤ Dbar.taylorDecrement j d)
    (hd : Dbar.taylorDecrement j d ≤ ς * ε * δ ^ j / j ! / 2)
    (hacc : ∑ i ∈ Finset.Icc 1 j, err i * δ ^ i / i ! ≤ ε * δ ^ j / j ! / 2) :
    taylorMeasure D j δ S ≤ ε * δ ^ j / j ! := by
  have h1 := taylorMeasure_le_add_of_jetApprox h hj h0 hδ
  have h2 : taylorMeasure Dbar j δ S ≤ ε * δ ^ j / j ! / 2 := by
    refine le_of_mul_le_mul_left ?_ hς
    calc ς * taylorMeasure Dbar j δ S ≤ ς * ε * δ ^ j / j ! / 2 := hφ.trans hd
      _ = ς * (ε * δ ^ j / j ! / 2) := by ring
  linarith

/-- **Certification with a uniform error.** Let $\bar D$ approximate $D$ up to order $q$ with errors
$e$, let $1 \le j \le q$, $0 \in S$, $0 \le \delta \le 1$ and $\varsigma > 0$. Let
$e_i \le e_{\max}$ for $1 \le i \le j$, with $e_{\max} \le \varepsilon\delta^j/(4\,j!)$. If
$\varsigma\,\phi^\delta_j(\bar D) \le \Delta T_j(\bar D, d) \le
\varsigma\varepsilon\delta^j/(2\,j!)$, then $\phi^\delta_j(D) \le \varepsilon\delta^j/j!$. This
is the form used in Lemmas 13.1.7 and 13.1.15 of [cartis2022evaluation]. -/
theorem taylorMeasure_le_of_inexact_certificate_uniform {q : ℕ} {ς ε e : ℝ} {d : E}
    (h : JetApprox D Dbar q err) (hj : j ∈ Finset.Icc 1 q) (h0 : (0 : E) ∈ S) (hδ : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hς : 0 < ς)
    (hφ : ς * taylorMeasure Dbar j δ S ≤ Dbar.taylorDecrement j d)
    (hd : Dbar.taylorDecrement j d ≤ ς * ε * δ ^ j / j ! / 2)
    (he : ∀ i ∈ Finset.Icc 1 j, err i ≤ e) (heε : e ≤ ε * δ ^ j / (4 * j !)) :
    taylorMeasure D j δ S ≤ ε * δ ^ j / j ! := by
  obtain ⟨hj1, hjq⟩ := mem_Icc.1 hj
  have he0 : 0 ≤ e := (h.nonneg (mem_Icc.2 ⟨le_rfl, hj1.trans hjq⟩)).trans
    (he 1 (mem_Icc.2 ⟨le_rfl, hj1⟩))
  refine taylorMeasure_le_of_inexact_certificate h hjq h0 hδ hς hφ hd ?_
  calc ∑ i ∈ Finset.Icc 1 j, err i * δ ^ i / i ! ≤ ∑ i ∈ Finset.Icc 1 j, e * (δ ^ i / i !) := by
        refine sum_le_sum fun i hi => ?_
        rw [mul_div_assoc]
        gcongr
        exact he i hi
    _ = e * ∑ i ∈ Finset.Icc 1 j, δ ^ i / i ! := by rw [mul_sum]
    _ ≤ e * (2 * δ) := by gcongr; exact sum_pow_div_factorial_le_two_mul hδ hδ1 j
    _ ≤ e * 2 := by gcongr; linarith
    _ ≤ ε * δ ^ j / (4 * j !) * 2 := by gcongr
    _ = ε * δ ^ j / j ! / 2 := by field_simp; ring

end Bounds

/-! ### Jets with a replaced first- or second-order term -/

section Jets

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

open scoped RealInnerProductSpace

/-- Let $V$ be a real inner product space, $D$ a jet on $V$ and $v \in V$. The jet
`Optimization.gradientJet D v` is $D$ with its first-order term replaced by the linear form
$w \mapsto \langle v, w\rangle$, where $v$ is an approximate gradient. The other terms are those
of $D$. -/
noncomputable def gradientJet (D : FormalMultilinearSeries ℝ V ℝ) (v : V) :
    FormalMultilinearSeries ℝ V ℝ :=
  fun i => match i with
  | 1 => (continuousMultilinearCurryFin1 ℝ V ℝ).symm (innerSL ℝ v)
  | i => D i

/-- The first-order term of `Optimization.gradientJet D v` maps $w$ to $\langle v, w\rangle$. -/
@[simp]
theorem gradientJet_apply_one (D : FormalMultilinearSeries ℝ V ℝ) (v : V) (m : Fin 1 → V) :
    gradientJet D v 1 m = ⟪v, m 0⟫ := by
  simp [gradientJet]

/-- The terms of order $i \neq 1$ of `Optimization.gradientJet D v` are those of $D$. -/
theorem gradientJet_apply_of_ne (D : FormalMultilinearSeries ℝ V ℝ) (v : V) {i : ℕ}
    (hi : i ≠ 1) : gradientJet D v i = D i := by
  match i, hi with
  | 0, _ => rfl
  | _ + 2, _ => rfl

/-- The bilinear form $(u, w) \mapsto \langle u, Aw\rangle$ of a continuous linear operator $A$ on
$V$, as a continuous $2$-linear map. -/
noncomputable def bilinearOfOperator (A : V →L[ℝ] V) : V [×2]→L[ℝ] ℝ :=
  (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => V) ℝ).symm
    ((↑(continuousMultilinearCurryFin1 ℝ V ℝ).symm : (V →L[ℝ] ℝ) →L[ℝ] V [×1]→L[ℝ] ℝ).comp
      ((ContinuousLinearMap.compL ℝ V V ℝ).flip A ∘L innerSL ℝ))

/-- The bilinear form `Optimization.bilinearOfOperator A` maps $(u, w)$ to $\langle u, Aw\rangle$.
-/
@[simp]
theorem bilinearOfOperator_apply (A : V →L[ℝ] V) (m : Fin 2 → V) :
    bilinearOfOperator A m = ⟪m 0, A (m 1)⟫ := by
  simp [bilinearOfOperator]
  rfl

/-- The bilinear form $(u, w) \mapsto \langle u, Aw\rangle$ has norm at most $\|A\|$. -/
theorem norm_bilinearOfOperator_le (A : V →L[ℝ] V) : ‖bilinearOfOperator A‖ ≤ ‖A‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) fun m => ?_
  rw [bilinearOfOperator_apply, Real.norm_eq_abs, Fin.prod_univ_two]
  calc |⟪m 0, A (m 1)⟫| ≤ ‖m 0‖ * ‖A (m 1)‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖m 0‖ * (‖A‖ * ‖m 1‖) := by gcongr; exact A.le_opNorm _
    _ = ‖A‖ * (‖m 0‖ * ‖m 1‖) := by ring

/-- Let $D$ be a jet on $V$ and $A$ a continuous linear operator on $V$. The jet
`Optimization.hessianJet D A` is $D$ with its second-order term replaced by the bilinear form
$(u, w) \mapsto \langle u, Aw\rangle$, where $A$ is an approximate Hessian. The other terms are
those of $D$. -/
noncomputable def hessianJet (D : FormalMultilinearSeries ℝ V ℝ) (A : V →L[ℝ] V) :
    FormalMultilinearSeries ℝ V ℝ :=
  fun i => match i with
  | 2 => bilinearOfOperator A
  | i => D i

/-- The second-order term of `Optimization.hessianJet D A` maps $(u, w)$ to $\langle u, Aw\rangle$.
-/
@[simp]
theorem hessianJet_apply_two (D : FormalMultilinearSeries ℝ V ℝ) (A : V →L[ℝ] V)
    (m : Fin 2 → V) : hessianJet D A 2 m = ⟪m 0, A (m 1)⟫ := by
  simp [hessianJet]

/-- The terms of order $i \neq 2$ of `Optimization.hessianJet D A` are those of $D$. -/
theorem hessianJet_apply_of_ne (D : FormalMultilinearSeries ℝ V ℝ) (A : V →L[ℝ] V) {i : ℕ}
    (hi : i ≠ 2) : hessianJet D A i = D i := by
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | _ + 3, _ => rfl

variable [CompleteSpace V]

/-- Let $V$ be a real Hilbert space, $f : V \to \mathbb{R}$, $x, v \in V$ and $c \in \mathbb{R}$. If
$\|v - \nabla f(x)\| \le c$, then the jet of $f$ at $x$ with its first-order term replaced by
$w \mapsto \langle v, w\rangle$ approximates the jet of $f$ at $x$ up to order $1$ with error
$c$. This is the error model (13.1.2) of [cartis2022evaluation] for an approximate gradient.

The gradient $\nabla f(x)$ is `gradient f x`. No differentiability hypothesis is needed. -/
theorem jetApprox_gradientJet {f : V → ℝ} {x v : V} {c : ℝ} (hv : ‖v - gradient f x‖ ≤ c) :
    JetApprox (ftaylorSeries ℝ f x) (gradientJet (ftaylorSeries ℝ f x) v) 1
      (fun _ => c) := by
  intro i hi
  obtain rfl : i = 1 := by simpa using hi
  have : gradientJet (ftaylorSeries ℝ f x) v 1 - ftaylorSeries ℝ f x 1 =
      (continuousMultilinearCurryFin1 ℝ V ℝ).symm (innerSL ℝ (v - gradient f x)) := by
    change (continuousMultilinearCurryFin1 ℝ V ℝ).symm (innerSL ℝ v) - iteratedFDeriv ℝ 1 f x = _
    ext m
    rw [sub_apply, iteratedFDeriv_one_apply, fderiv_eq_innerSL_gradient]
    simp
  rw [this, LinearIsometryEquiv.norm_map, innerSL_apply_norm]
  exact hv

/-- Let $V$ be a real Hilbert space, let $f : V \to \mathbb{R}$ be of class $C^2$ at $x$, and let
$A$ be a continuous linear operator on $V$ with $\|A - \nabla^2 f(x)\| \le c$. Then the jet of
$f$ at $x$ with its second-order term replaced by $(u, w) \mapsto \langle u, Aw\rangle$
approximates the jet of $f$ at $x$ up to order $2$, with error $0$ at order $1$ and error $c$ at
order $2$.

The Hessian $\nabla^2 f(x)$ is the operator `Optimization.hessianOperator f x`, the derivative
of the gradient. -/
theorem jetApprox_hessianJet {f : V → ℝ} {x : V} (hf : ContDiffAt ℝ 2 f x) {A : V →L[ℝ] V}
    {c : ℝ} (hA : ‖A - hessianOperator f x‖ ≤ c) :
    JetApprox (ftaylorSeries ℝ f x) (hessianJet (ftaylorSeries ℝ f x) A) 2
      (fun i => if i = 2 then c else 0) := by
  intro i hi
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hi
  rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
  · rw [hessianJet_apply_of_ne _ _ (by norm_num), sub_self, norm_zero]
    simp
  · have : hessianJet (ftaylorSeries ℝ f x) A 2 - ftaylorSeries ℝ f x 2 =
        bilinearOfOperator (A - hessianOperator f x) := by
      ext m
      have hm : m = ![m 0, m 1] := by ext j; fin_cases j <;> rfl
      simp only [sub_apply, hessianJet_apply_two,
        bilinearOfOperator_apply, inner_sub_right, ftaylorSeries]
      rw [hm, ← inner_hessianOperator_apply hf]
      rfl
    rw [this]
    simpa using (norm_bilinearOfOperator_le _).trans hA

end Jets

end Optimization
