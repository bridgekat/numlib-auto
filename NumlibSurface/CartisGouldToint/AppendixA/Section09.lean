/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Approximation.Hermite
import Numlib.Approximation.HermiteSpline

/-!
# Cartis, Gould and Toint, Section A.9: Polynomial Hermite interpolation

This module formalizes §A.9 of [cartis2022evaluation]: Hermite interpolation of the values and the
first $p$ derivatives of a function, on one interval and on a sequence of nodes, with constants that
depend only on $p$ and on a bound $\kappa_f$ for the data. On an interval $[0, s]$ the data are two
jets $f_0^{(j)}, f_1^{(j)}$ for $j \in \{0, \dots, p\}$, and the interpolant is the polynomial $\pi$
of degree at most $2p + 1$ with $\pi^{(j)}(0) = f_0^{(j)}$ and $\pi^{(j)}(s) = f_1^{(j)}$ (A.24).
The hypotheses compare the right jet with the derivatives of the Taylor polynomial of the left jet,
$$T^{(j)}_{f,p}(0, s) = \sum_{i=j}^p \frac{f_0^{(i)} s^{i-j}}{(i-j)!}.$$
The proofs specialize the backbone modules `Numlib.Approximation.Hermite` and
`Numlib.Approximation.HermiteSpline`.

## Main results

* Theorem A.9.1, `CartisGouldToint.AppendixA.theorem_A_9_1`: under (A.30) the Hermite interpolant on
  $[0, s]$ exists and is unique, its $p$-th derivative is Lipschitz continuous, and under (A.31) its
  derivatives are bounded.
* Theorem A.9.2, `CartisGouldToint.AppendixA.theorem_A_9_2`: under (A.32) there is a $C^p$ function
  on $\mathbb{R}$ that interpolates jets at nodes $x_0 < \dots < x_{k_e}$, whose $p$-th derivative
  is Lipschitz continuous, and whose derivatives are bounded under additional bounds on the data.

## Conventions

* A jet is a sequence `f₀ : ℕ → ℝ`, with `f₀ j` the derivative $f_0^{(j)}$. The $j$-th derivative of
  a polynomial `π` is `derivative^[j] π`, and the derivatives of the Taylor polynomial of a jet are
  written out as sums.

## Implementation notes

* In Theorem A.9.2 the same interpolant satisfies both conclusions: it has the Lipschitz constant
  $L$ in all cases, and the derivative bound $B$ when the additional bounds hold.

## Deviations from the source

* **Generalization and index correction.** Theorem A.9.2 allows order zero, uses the defined steps
  only, and bounds the interpolant on the real line. See `CartisGouldToint.AppendixA.theorem_A_9_2`.
* **Theorem A.9.2** (generalization). The book assumes $p > 0$, which the proof does not use; the
  statement holds for every $p$. See `CartisGouldToint.AppendixA.theorem_A_9_2`.
* **Theorem A.9.2** (reading). The hypothesis $s_k > 0$ "for $k \in [0 : k_e]$" is read for
  $k < k_e$, the only $k$ for which the data define $s_k$. See
  `CartisGouldToint.AppendixA.theorem_A_9_2`.
* **Theorem A.9.2** (typo). The derivative bound "for all $x \in \mathbb{R}^n$" is for all
  $x \in \mathbb{R}$. See `CartisGouldToint.AppendixA.theorem_A_9_2`.
-/

open Polynomial Set
open scoped Polynomial

namespace CartisGouldToint.AppendixA

/-- **Theorem A.9.1** of [cartis2022evaluation] (general Hermite interpolation on an interval). Let
$p \in \mathbb{N}$ and $\kappa_f \ge 0$. There are constants $L, B \ge 0$, which depend only on
$p$ and $\kappa_f$, with the following property. Let $s > 0$, and let $f_0, f_1$ be jets that
satisfy (A.30):
$$\Bigl| f_1^{(j)} - \sum_{i=j}^p \frac{f_0^{(i)} s^{i-j}}{(i-j)!} \Bigr| \le \kappa_f s^{p-j+1}
  \quad \text{for } j \in \{0, \dots, p\}.$$
Then:

* there is exactly one polynomial $\pi$ of degree at most $2p + 1$ with
  $\pi^{(j)}(0) = f_0^{(j)}$ and $\pi^{(j)}(s) = f_1^{(j)}$ for $j \in \{0, \dots, p\}$ (A.24);
* this polynomial satisfies $|\pi^{(p)}(\tau_1) - \pi^{(p)}(\tau_2)| \le L |\tau_1 - \tau_2|$
  for all $\tau_1, \tau_2 \in [0, s]$;
* if moreover (A.31) holds, that is $|f_0^{(j)}| \le \kappa_f$ for $j \in \{0, \dots, p\}$ and
  $s \le \kappa_f$, then $|\pi^{(j)}(\tau)| \le B$ for all $\tau \in [0, s]$ and
  $j \in \{0, \dots, p\}$.

The jets are `f₀ f₁ : ℕ → ℝ`. The second and third conclusions are stated for every polynomial
of degree at most $2p + 1$ that satisfies (A.24). -/
theorem theorem_A_9_1 (p : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) : ∃ L B : ℝ, 0 ≤ L ∧ 0 ≤ B ∧
    ∀ (s : ℝ) (f₀ f₁ : ℕ → ℝ), 0 < s →
      (∀ j ≤ p, |f₁ j - ∑ i ∈ Finset.Icc j p, f₀ i * s ^ (i - j) / (i - j).factorial| ≤
        κ * s ^ (p - j + 1)) →
      (∃! π : ℝ[X], π.natDegree ≤ 2 * p + 1 ∧ (∀ j ≤ p, (derivative^[j] π).eval 0 = f₀ j) ∧
        ∀ j ≤ p, (derivative^[j] π).eval s = f₁ j) ∧
      ∀ π : ℝ[X], π.natDegree ≤ 2 * p + 1 → (∀ j ≤ p, (derivative^[j] π).eval 0 = f₀ j) →
        (∀ j ≤ p, (derivative^[j] π).eval s = f₁ j) →
        (∀ τ₁ ∈ Icc 0 s, ∀ τ₂ ∈ Icc 0 s,
          |(derivative^[p] π).eval τ₁ - (derivative^[p] π).eval τ₂| ≤ L * |τ₁ - τ₂|) ∧
        ((∀ j ≤ p, |f₀ j| ≤ κ) → s ≤ κ →
          ∀ j ≤ p, ∀ τ ∈ Icc 0 s, |(derivative^[j] π).eval τ| ≤ B) := by
  obtain ⟨C, hC, htwo⟩ := Hermite.exists_twoPoint_interpolant p
  obtain ⟨C', hC', htwo'⟩ := Hermite.exists_twoPoint_interpolant_bounded p
  refine ⟨C * κ, (p + 1) * κ * max 1 κ ^ p + C' * κ * max 1 κ ^ (p + 1), mul_nonneg hC hκ,
    by positivity, fun s f₀ f₁ hs hcons => ?_⟩
  obtain ⟨π₀, hdeg₀, h0₀, h1₀, -, hlip₀⟩ := htwo s κ f₀ f₁ hs hcons
  have huniq : ∀ π : ℝ[X], π.natDegree ≤ 2 * p + 1 → (∀ j ≤ p, (derivative^[j] π).eval 0 = f₀ j) →
      (∀ j ≤ p, (derivative^[j] π).eval s = f₁ j) → π = π₀ := fun π hdeg h0 h1 =>
    Hermite.eq_of_twoPoint_jets hs.ne' hdeg hdeg₀ (fun j hj => (h0 j hj).trans (h0₀ j hj).symm)
      (fun j hj => (h1 j hj).trans (h1₀ j hj).symm)
  refine ⟨⟨π₀, ⟨hdeg₀, h0₀, h1₀⟩, fun π ⟨hdeg, h0, h1⟩ => huniq π hdeg h0 h1⟩,
    fun π hdeg h0 h1 => ?_⟩
  obtain rfl := huniq π hdeg h0 h1
  refine ⟨hlip₀, fun hf₀ hsκ j hj τ hτ => ?_⟩
  obtain ⟨π₁, hdeg₁, h0₁, h1₁, hb₁, -⟩ := htwo' s κ f₀ f₁ hs hsκ hf₀ hcons
  obtain rfl := huniq π₁ hdeg₁ h0₁ h1₁
  exact hb₁ j (by omega) τ hτ

/-- **Theorem A.9.2** of [cartis2022evaluation] (general Hermite interpolation). Let
$p \in \mathbb{N}$ and $\kappa_f \ge 0$. There are constants $L, B \ge 0$, which depend only on
$p$ and $\kappa_f$, with the following property. Let $k_e > 0$, let
$x_0 < x_1 < \dots < x_{k_e}$ be real nodes with $s_k = x_{k+1} - x_k$, and let $f_k^{(j)}$ for
$k \in \{0, \dots, k_e\}$ and $j \in \{0, \dots, p\}$ be data that satisfy (A.32):
$$\Bigl| f_{k+1}^{(j)} - \sum_{i=j}^p \frac{f_k^{(i)} s_k^{i-j}}{(i-j)!} \Bigr| \le \kappa_f
  s_k^{p-j+1} \quad \text{for } k < k_e \text{ and } j \in \{0, \dots, p\}.$$
Then there is a $p$ times continuously differentiable function $f : \mathbb{R} \to \mathbb{R}$
with $|f^{(p)}(t_1) - f^{(p)}(t_2)| \le L |t_1 - t_2|$ for all $t_1, t_2 \in \mathbb{R}$ and
$f^{(j)}(x_k) = f_k^{(j)}$ for all $k \le k_e$ and $j \le p$. If moreover
$|f_k^{(j)}| \le \kappa_f$ and $s_k \le \kappa_f$ for all $k < k_e$ and $j \le p$, then
$|f^{(j)}(t)| \le B$ for all $t \in \mathbb{R}$ and $j \le p$.

**Generalization.** The book assumes $p > 0$, which the proof does not use.

**Reading.** The book requires $s_k > 0$ "for $k \in [0 : k_e]$"; this is read for $k < k_e$,
the only $k$ for which the data define $s_k$.

**Typo.** The book states the derivative bound "for all $x \in \mathbb{R}^n$"; the function is
defined on $\mathbb{R}$, and the bound is for all $x \in \mathbb{R}$.

The sum in (A.32) is the $j$-th derivative at $s_k$ of the Taylor polynomial $T_{k,p}(x_k, s) =
\sum_{i=0}^p f_k^{(i)} s^i / i!$ of the jet at $x_k$. The nodes are `x : ℕ → ℝ` and the data are
`F : ℕ → ℕ → ℝ`, with `F k j` $= f_k^{(j)}$.

**Correction.** Order zero is allowed. Step positivity ranges over the actual consecutive pairs of
data, from index zero through one before the final node. The derivative bounds apply on the real
line.
-/
theorem theorem_A_9_2 (p : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) : ∃ L B : ℝ, 0 ≤ L ∧ 0 ≤ B ∧
    ∀ (kₑ : ℕ) (x : ℕ → ℝ) (F : ℕ → ℕ → ℝ), 0 < kₑ → (∀ k < kₑ, x k < x (k + 1)) →
      (∀ k < kₑ, ∀ j ≤ p, |F (k + 1) j - ∑ i ∈ Finset.Icc j p,
        F k i * (x (k + 1) - x k) ^ (i - j) / (i - j).factorial| ≤
          κ * (x (k + 1) - x k) ^ (p - j + 1)) →
      ∃ f : ℝ → ℝ, ContDiff ℝ p f ∧
        (∀ t₁ t₂, |iteratedDeriv p f t₁ - iteratedDeriv p f t₂| ≤ L * |t₁ - t₂|) ∧
        (∀ k ≤ kₑ, ∀ j ≤ p, iteratedDeriv j f (x k) = F k j) ∧
        ((∀ k < kₑ, ∀ j ≤ p, |F k j| ≤ κ) → (∀ k < kₑ, x (k + 1) - x k ≤ κ) →
          ∀ j ≤ p, ∀ t, |iteratedDeriv j f t| ≤ B) := by
  obtain ⟨L₁, hL₁, h₁⟩ := Hermite.exists_contDiff_interpolating_jets p hκ
  obtain ⟨L₂, B, hL₂, hB, h₂⟩ := Hermite.exists_contDiff_interpolating_jets_bounded p hκ
  refine ⟨max L₁ L₂, B, hL₁.trans (le_max_left _ _), hB, fun kₑ x F hk hx hF => ?_⟩
  have hlip : ∀ {L : ℝ} {g : ℝ → ℝ}, L ≤ max L₁ L₂ →
      (∀ t₁ t₂, |iteratedDeriv p g t₁ - iteratedDeriv p g t₂| ≤ L * |t₁ - t₂|) →
      ∀ t₁ t₂, |iteratedDeriv p g t₁ - iteratedDeriv p g t₂| ≤ max L₁ L₂ * |t₁ - t₂| :=
    fun hL hg t₁ t₂ => (hg t₁ t₂).trans (mul_le_mul_of_nonneg_right hL (abs_nonneg _))
  by_cases hbd : (∀ k < kₑ, ∀ j ≤ p, |F k j| ≤ κ) ∧ ∀ k < kₑ, x (k + 1) - x k ≤ κ
  · obtain ⟨g, hg, hgL, hgB, hgF, -⟩ := h₂ kₑ x F hk hx hbd.2 hbd.1 hF
    exact ⟨g, hg, hlip (le_max_right _ _) hgL, hgF, fun _ _ => hgB⟩
  · obtain ⟨g, hg, hgL, hgF⟩ := h₁ kₑ x F hx hF
    exact ⟨g, hg, hlip (le_max_left _ _) hgL, hgF, fun h₁ h₂ => absurd ⟨h₁, h₂⟩ hbd⟩

end CartisGouldToint.AppendixA
