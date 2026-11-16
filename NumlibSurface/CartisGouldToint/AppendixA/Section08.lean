/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Analysis.Calculus.LipschitzIteratedFDeriv
import Numlib.Analysis.Calculus.Taylor

/-!
# Cartis, Gould and Toint, Section A.8: Taylor's theorem

This module formalizes §A.8 of [cartis2022evaluation]: Taylor's theorem for functions of one
variable, with the integral and the Lagrange form of the remainder, and the bounds on the Taylor
remainder of a function of several variables whose $p$-th derivative is Hölder or Lipschitz
continuous. For $\psi : \mathbb{R} \to \mathbb{R}$ the Taylor approximation of $\psi(t + h)$ is
$\tau_k(t, h) = \psi(t) + \sum_{i=1}^k \psi^{(i)}(t) h^i / i!$. For
$f : \mathbb{R}^n \to \mathbb{R}$ the Taylor polynomial (A.10) is $T_{f,p}(x, s) = \sum_{i=0}^p
\nabla^i f(x)[s]^i / i!$, and the generalized factorial is
$(k + \beta)! = \prod_{\ell=1}^k (\ell + \beta)$. The proofs specialize the backbone modules
`Numlib.Analysis.Calculus.Taylor` and `Numlib.Analysis.Calculus.LipschitzIteratedFDeriv`.

## Main definitions

* Theorem A.8.1, `CartisGouldToint.AppendixA.taylorApprox`: the Taylor approximation $\tau_k(t, h)$,
  with the derivatives taken within a given set.

## Main results

* Theorem A.8.1, `CartisGouldToint.AppendixA.theorem_A_8_1`: Taylor's theorem with the integral
  remainder (A.9).
* Theorem A.8.2, `CartisGouldToint.AppendixA.theorem_A_8_2`: Taylor's theorem with the Lagrange
  remainder.
* Theorem A.8.3, `CartisGouldToint.AppendixA.theorem_A_8_3`: the remainder bounds (A.14) and (A.15)
  when $\nabla^p f$ is Hölder continuous (A.13).
* Equation (A.16), `CartisGouldToint.AppendixA.eq_A_16`: the integral $\int_0^1 \xi^\beta (1 -
  \xi)^{k-1} \, d\xi = (k-1)!/(k+\beta)!$ that the proof of Theorem A.8.3 uses.
* Corollary A.8.4, `CartisGouldToint.AppendixA.corollary_A_8_4`: the remainder bounds (A.19) and
  (A.20) when $\nabla^p f$ is Lipschitz continuous (A.18).
* Theorem A.8.5, `CartisGouldToint.AppendixA.theorem_A_8_5`: on an open convex set, $\nabla^p f$ is
  $L$-Lipschitz if and only if $\|\nabla^{p+1} f\| \le L$ (A.21).

## Conventions

* The derivatives $\psi^{(i)}$ of a function of one variable are taken within the interval on which
  $\psi$ is assumed smooth (`iteratedDerivWithin`), so they are one-sided at the endpoints of the
  interval.
* $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)`.
* $\nabla^j f(x)$ is `iteratedFDeriv ℝ j f x`, and the tensor norm (A.7) is the operator norm of
  multilinear maps.
* $T_{f,p}(x, s)$ is `taylorPolynomial f p x s`.
* $\nabla^j_s T_{f,p}(x, s)$ is `iteratedFDeriv ℝ j (taylorPolynomial f p x) s`.
* $(k + \beta)!$ is `holderFactorial k β`.

## Deviations from the source

* **Theorem A.8.1** (reading). The conditions $k \ge 1$ and $h \ge 0$, which the book leaves
  implicit, are hypotheses. See `CartisGouldToint.AppendixA.theorem_A_8_1`.
* **Theorem A.8.2** (correction). The point $\xi$ lies strictly between $t$ and $t + h$, which needs
  the added hypothesis $h \neq 0$. See `CartisGouldToint.AppendixA.theorem_A_8_2`.
* **Theorem A.8.5** (correction). The added hypothesis $L \ge 0$ is needed: on $\mathbb{R}^0$ with
  $L < 0$ the Lipschitz condition holds and (A.21) fails. See
  `CartisGouldToint.AppendixA.theorem_A_8_5`.

## Not formalized

* **(A.12)**, the Taylor expansion with the Peano remainder. It is not stated in this module. The
  backbone module `Numlib.Analysis.Calculus.MultivariateTaylor.Peano` proves it for $f$ of class
  $C^n$ at $x$, while the book assumes only that $f$ is $n$ times differentiable at $x$.
-/

open Set
open scoped Nat

namespace CartisGouldToint.AppendixA

/-! ### Univariate Taylor theorems -/

/-- **Theorem A.8.1** of [cartis2022evaluation], the Taylor approximation. Let
$\psi : \mathbb{R} \to \mathbb{R}$, $I \subseteq \mathbb{R}$, $k \in \mathbb{N}$ and
$t, h \in \mathbb{R}$. The **Taylor approximation** of degree $k$ of $\psi(t + h)$ about $t$ is
$$\tau_k(t, h) = \psi(t) + \sum_{i=1}^k \frac{1}{i!} \psi^{(i)}(t) h^i,$$
where the derivatives $\psi^{(i)}$ are taken within $I$.

The derivative $\psi^{(i)}(t)$ is `iteratedDerivWithin i ψ I t`. In the theorems of this module,
$I$ is the interval on which $\psi$ is smooth. -/
noncomputable def taylorApprox (ψ : ℝ → ℝ) (I : Set ℝ) (k : ℕ) (t h : ℝ) : ℝ :=
  ψ t + ∑ i ∈ Finset.Icc 1 k, (i ! : ℝ)⁻¹ * iteratedDerivWithin i ψ I t * h ^ i

/-- The Taylor approximation $\tau_k(t, h)$ is the Taylor polynomial `taylorWithinEval ψ k I t` of
Mathlib, evaluated at $t + h$. -/
theorem taylorApprox_eq_taylorWithinEval (ψ : ℝ → ℝ) (I : Set ℝ) (k : ℕ) (t h : ℝ) :
    taylorApprox ψ I k t h = taylorWithinEval ψ k I t (t + h) := by
  rw [taylor_within_apply, Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos k), Nat.succ_eq_add_one,
    Finset.Ico_add_one_right_eq_Icc, zero_add, taylorApprox]
  simp only [add_sub_cancel_left, smul_eq_mul]
  congr 1
  · simp
  · exact Finset.sum_congr rfl fun i _ => by ring

/-- **Theorem A.8.1** of [cartis2022evaluation] (Taylor's theorem for a univariate function). Let
$\psi : \mathbb{R} \to \mathbb{R}$, let $k \ge 1$, $t \in \mathbb{R}$ and $h \ge 0$, and let
$\psi$ be $k$ times continuously differentiable on $[t, t + h]$. Then (A.9) holds:
$$\psi(t + h) - \tau_k(t, h) = \frac{1}{(k-1)!} \int_0^h (h - \xi)^{k-1} \bigl(\psi^{(k)}(t +
  \xi) - \psi^{(k)}(t)\bigr) \, d\xi.$$

**Reading.** The book leaves the conditions $k \ge 1$ and $h \ge 0$ implicit: the remainder
contains $(k-1)!$, and the interval is $[t, t + h]$.

The approximation $\tau_k$ is `CartisGouldToint.AppendixA.taylorApprox` with $I = [t, t + h]$.
All derivatives, also $\psi^{(k)}$ in the integrand, are taken within $[t, t + h]$. -/
theorem theorem_A_8_1 {ψ : ℝ → ℝ} {k : ℕ} {t h : ℝ} (hk : 1 ≤ k) (hh : 0 ≤ h)
    (hψ : ContDiffOn ℝ k ψ (Icc t (t + h))) :
    ψ (t + h) - taylorApprox ψ (Icc t (t + h)) k t h =
      1 / ((k - 1)! : ℝ) * ∫ ξ in (0 : ℝ)..h, (h - ξ) ^ (k - 1) *
        (iteratedDerivWithin k ψ (Icc t (t + h)) (t + ξ) -
          iteratedDerivWithin k ψ (Icc t (t + h)) t) := by
  rw [taylorApprox_eq_taylorWithinEval, one_div]
  exact taylor_integral_remainder_sub hk hh hψ

/-- **Theorem A.8.2** of [cartis2022evaluation] (univariate Taylor's theorem, Lagrange form). Let
$\psi : \mathbb{R} \to \mathbb{R}$, $k \in \mathbb{N}$, $t \in \mathbb{R}$ and $h \neq 0$, and
let $\psi$ be $k + 1$ times continuously differentiable on the closed interval between $t$ and
$t + h$. Then there is $\xi$ strictly between $t$ and $t + h$ with
$$\psi(t + h) - \tau_k(t, h) = \frac{\psi^{(k+1)}(\xi)}{(k+1)!} h^{k+1}.$$

**Correction.** The book does not require $h \neq 0$. For $h = 0$ the open interval between $t$
and $t + h$ is empty, so no such $\xi$ exists, although the identity holds with $\xi = t$.

The statement holds for either sign of $h$. The derivative $\psi^{(k+1)}(\xi)$ is the ordinary
derivative `iteratedDeriv (k + 1) ψ ξ`. In the Lean statement,
`CartisGouldToint.AppendixA.taylorApprox` takes its derivatives within the closed interval
`uIcc t (t + h)`, and the point lies in the open interval `uIoo t (t + h)`. -/
theorem theorem_A_8_2 {ψ : ℝ → ℝ} {k : ℕ} {t h : ℝ} (hh : h ≠ 0)
    (hψ : ContDiffOn ℝ (k + 1) ψ (uIcc t (t + h))) :
    ∃ ξ ∈ uIoo t (t + h), ψ (t + h) - taylorApprox ψ (uIcc t (t + h)) k t h =
      iteratedDeriv (k + 1) ψ ξ * h ^ (k + 1) / ((k + 1)! : ℝ) := by
  obtain ⟨ξ, hξ, e⟩ :=
    exists_taylorWithinEval_add_iteratedDeriv_mul (fun e => hh (by linarith)) hψ
  refine ⟨ξ, hξ, ?_⟩
  rw [taylorApprox_eq_taylorWithinEval, e]
  simp only [add_sub_cancel_left]

/-! ### Multivariate Taylor theorems -/

variable {n : ℕ}

/-- **Equation (A.16)** of [cartis2022evaluation]. For $k \ge 1$ and $\beta \in [0, 1]$,
$$\int_0^1 \xi^\beta (1 - \xi)^{k-1} \, d\xi = \frac{(k-1)!}{(k+\beta)!},$$
where $(k + \beta)! = \prod_{\ell=1}^k (\ell + \beta)$.

The proof of Theorem A.8.3 uses this identity. The factorial $(k + \beta)!$ is
`holderFactorial k β`. The proof does not use the hypothesis $\beta \le 1$. -/
theorem eq_A_16 {k : ℕ} (hk : 1 ≤ k) {β : ℝ} (hβ0 : 0 ≤ β) (_hβ1 : β ≤ 1) :
    ∫ ξ in (0 : ℝ)..1, ξ ^ β * (1 - ξ) ^ (k - 1) = ((k - 1)! : ℝ) / holderFactorial k β :=
  integral_rpow_mul_one_sub_pow hk hβ0

/-- **Theorem A.8.3** of [cartis2022evaluation] (Taylor's theorem for a multivariate Hölder
function). Let $C \subseteq \mathbb{R}^n$ be convex, let $D \supseteq C$ be open, let
$f : \mathbb{R}^n \to \mathbb{R}$ be $p$ times continuously differentiable on $D$, and let
$\beta \in [0, 1]$. Assume that $\nabla^p f$ is Hölder continuous on $C$ with constant $H$ and
exponent $\beta$ (A.13):
$$\|\nabla^p f(x) - \nabla^p f(y)\| \le H \|x - y\|^\beta \quad \text{for all } x, y \in C.$$
Then for all $x$ and $s$ with $x, x + s \in C$, the bound (A.14)
$$|f(x + s) - T_{f,p}(x, s)| \le \frac{H}{(p+\beta)!} \|s\|^{p+\beta}$$
holds, and for every $j \in \{1, \dots, p\}$ the bound (A.15)
$$\|\nabla^j f(x + s) - \nabla^j_s T_{f,p}(x, s)\| \le \frac{H}{(p-j+\beta)!}
  \|s\|^{p-j+\beta}$$
holds.

The proof of (A.15) in the book displays the constant $(p-j+1)!/(p-j+\beta)!$; the constant
$1/(p-j+\beta)!$ of the statement is what is proved here. The proof does not use the hypothesis
$\beta \le 1$, and the backbone form of the result also covers $j = 0$ and every $\beta \ge 0$.
The Taylor polynomial $T_{f,p}(x, s)$ of (A.10) is `taylorPolynomial f p x s`, its derivative
$\nabla^j_s T_{f,p}(x, s)$ is `iteratedFDeriv ℝ j (taylorPolynomial f p x) s`, and
$(k + \beta)!$ is `holderFactorial k β`. -/
theorem theorem_A_8_3 {C D : Set (EuclideanSpace ℝ (Fin n))} (hC : Convex ℝ C) (hD : IsOpen D)
    (hCD : C ⊆ D) {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} (hf : ContDiffOn ℝ p f D)
    {H β : ℝ} (hβ0 : 0 ≤ β) (_hβ1 : β ≤ 1)
    (hH : ∀ x ∈ C, ∀ y ∈ C,
      ‖iteratedFDeriv ℝ p f x - iteratedFDeriv ℝ p f y‖ ≤ H * ‖x - y‖ ^ β)
    {x s : EuclideanSpace ℝ (Fin n)} (hx : x ∈ C) (hxs : x + s ∈ C) :
    |f (x + s) - taylorPolynomial f p x s| ≤ H / holderFactorial p β * ‖s‖ ^ ((p : ℝ) + β) ∧
      ∀ j, 1 ≤ j → j ≤ p → ‖iteratedFDeriv ℝ j f (x + s) -
          iteratedFDeriv ℝ j (taylorPolynomial f p x) s‖ ≤
        H / holderFactorial (p - j) β * ‖s‖ ^ (((p - j : ℕ) : ℝ) + β) := by
  have hf' : ∀ y ∈ C, ContDiffAt ℝ p f y := fun y hy => hf.contDiffAt (hD.mem_nhds (hCD hy))
  have hH' : IteratedFDerivHolderOn f p H β C := iteratedFDerivHolderOn_iff.2 hH
  exact ⟨abs_sub_taylorPolynomial_le_of_holder hC hf' hβ0 hH' hx hxs, fun _ _ hj =>
    norm_iteratedFDeriv_sub_taylorPolynomial_le_of_holder hC hf' hβ0 hH' hx hxs hj⟩

/-- **Corollary A.8.4** of [cartis2022evaluation] (Taylor's theorem for a multivariate Lipschitz
function). Let $C \subseteq \mathbb{R}^n$ be convex, let $D \supseteq C$ be open, and let
$f : \mathbb{R}^n \to \mathbb{R}$ be $p$ times continuously differentiable on $D$. Assume that
$\nabla^p f$ is Lipschitz continuous on $C$ with constant $L$ (A.18):
$$\|\nabla^p f(x) - \nabla^p f(y)\| \le L \|x - y\| \quad \text{for all } x, y \in C.$$
Then for all $x$ and $s$ with $x, x + s \in C$, the bound (A.19)
$$|f(x + s) - T_{f,p}(x, s)| \le \frac{L}{(p+1)!} \|s\|^{p+1}$$
holds, and for every $j \in \{1, \dots, p\}$ the bound (A.20)
$$\|\nabla^j f(x + s) - \nabla^j_s T_{f,p}(x, s)\| \le \frac{L}{(p-j+1)!} \|s\|^{p-j+1}$$
holds.

The Taylor polynomial $T_{f,p}(x, s)$ is `taylorPolynomial f p x s`, and
$\nabla^j_s T_{f,p}(x, s)$ is `iteratedFDeriv ℝ j (taylorPolynomial f p x) s`. -/
theorem corollary_A_8_4 {C D : Set (EuclideanSpace ℝ (Fin n))} (hC : Convex ℝ C)
    (hD : IsOpen D) (hCD : C ⊆ D) {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ}
    (hf : ContDiffOn ℝ p f D) {L : ℝ}
    (hL : ∀ x ∈ C, ∀ y ∈ C, ‖iteratedFDeriv ℝ p f x - iteratedFDeriv ℝ p f y‖ ≤ L * ‖x - y‖)
    {x s : EuclideanSpace ℝ (Fin n)} (hx : x ∈ C) (hxs : x + s ∈ C) :
    |f (x + s) - taylorPolynomial f p x s| ≤ L / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) ∧
      ∀ j, 1 ≤ j → j ≤ p → ‖iteratedFDeriv ℝ j f (x + s) -
          iteratedFDeriv ℝ j (taylorPolynomial f p x) s‖ ≤
        L / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) := by
  have hf' : ∀ y ∈ C, ContDiffAt ℝ p f y := fun y hy => hf.contDiffAt (hD.mem_nhds (hCD hy))
  have hL' : IteratedFDerivLipschitzOn f p L C := iteratedFDerivLipschitzOn_iff.2 hL
  exact ⟨abs_sub_taylorPolynomial_le_of_lipschitz hC hf' hL' hx hxs, fun _ _ hj =>
    norm_iteratedFDeriv_sub_taylorPolynomial_le_of_lipschitz hC hf' hL' hx hxs hj⟩

/-- **Theorem A.8.5** of [cartis2022evaluation] (Lipschitz if and only if bounded derivatives). Let
$C \subseteq \mathbb{R}^n$ be open and convex, let $f : \mathbb{R}^n \to \mathbb{R}$ be $p + 1$
times continuously differentiable on $C$, and let $L \ge 0$. Then $\nabla^p f$ is Lipschitz
continuous on $C$ with constant $L$ (A.18),
$$\|\nabla^p f(x) - \nabla^p f(y)\| \le L \|x - y\| \quad \text{for all } x, y \in C,$$
if and only if (A.21) holds: $\|\nabla^{p+1} f(x)\| \le L$ for all $x \in C$.

**Correction.** The book leaves the sign of $L$ implicit. The hypothesis $L \ge 0$ is needed: on
$\mathbb{R}^0$ with $L < 0$ the Lipschitz condition holds trivially, while (A.21) fails. -/
theorem theorem_A_8_5 {C : Set (EuclideanSpace ℝ (Fin n))} (hCo : IsOpen C) (hC : Convex ℝ C)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} (hf : ContDiffOn ℝ (p + 1) f C) {L : ℝ}
    (hL : 0 ≤ L) :
    (∀ x ∈ C, ∀ y ∈ C, ‖iteratedFDeriv ℝ p f x - iteratedFDeriv ℝ p f y‖ ≤ L * ‖x - y‖) ↔
      ∀ x ∈ C, ‖iteratedFDeriv ℝ (p + 1) f x‖ ≤ L := by
  rw [← iteratedFDerivLipschitzOn_iff]
  exact iteratedFDerivLipschitzOn_iff_norm_le hCo hC hL fun y hy =>
    hf.contDiffAt (hCo.mem_nhds hy)

end CartisGouldToint.AppendixA
