/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Complexity.SlowExample.ZigZag
import NumlibSurface.CartisGouldToint.Chapter02.Section02

/-!
# Cartis, Gould and Toint, Appendix B: Appendix to Chapter 2

This module formalizes the part of Appendix B of [cartis2022evaluation] that belongs to Chapter 2,
Lemmas B.2.1–B.2.6. The lemmas build a function of two variables on which steepest descent with
exact linesearches (SDEX) needs $\varepsilon^{-2}$ iterations; this proves Theorem 2.2.5,
`CartisGouldToint.Chapter02.theorem_2_2_5`. Throughout, $\varepsilon > 0$ and
$k_\varepsilon \varepsilon^2 = 1$, so $k_\varepsilon = \varepsilon^{-2}$ is an integer. The function
is $f_{\mathrm{SDEX}}(x, y) = (f_1(x) + f_2(x, y))/\sqrt{2}$: the term $f_1$ interpolates prescribed
slopes at the nodes $x_k$, and the corridor function $f_2$ keeps the iterates near the middle line
$y_{\mathrm{mid}}(x)$ of a zig-zag corridor. The iterates are $(x_0, y_0) = 0$ and $(x_{k+1},
y_{k+1}) = (x_k, y_k) + (\varepsilon + \omega_k)(1, (-1)^k)$ with $\omega_k = \varepsilon
(k_\varepsilon - k)/k_\varepsilon$. The construction is in the backbone module
`Numlib.Optimization.Complexity.SlowExample.ZigZag`.

## Main definitions

* Lemma B.2.1, `CartisGouldToint.AppendixB.hermiteQuintic`: the quintic Hermite interpolant with the
  coefficients (B.2.1)–(B.2.2).

## Main results

* Lemma B.2.1, `CartisGouldToint.AppendixB.lemma_B_2_1`: the quintic interpolates values, first and
  second derivatives at $0$ and $1$.
* Lemma B.2.1, `CartisGouldToint.AppendixB.lemma_B_2_1_bound`: the interpolant and its first two
  derivatives are bounded on $[0, 1]$ by a constant that depends only on $\kappa_f$.
* Lemma B.2.2, `CartisGouldToint.AppendixB.lemma_B_2_2`: the gradients at the iterates (B.2.25), and
  steepest descent with the step $\sqrt{2}$ needs exactly $k_\varepsilon$ iterations.
* Lemma B.2.3, `CartisGouldToint.AppendixB.lemma_B_2_3`: the corridor function $f_2$ and its first
  two derivatives are bounded independently of $\varepsilon$.
* Lemma B.2.4, `CartisGouldToint.AppendixB.lemma_B_2_4`: $f_{\mathrm{SDEX}}$ satisfies f.Bb with a
  constant independent of $\varepsilon$.
* Lemma B.2.5, `CartisGouldToint.AppendixB.lemma_B_2_5`: $f_{\mathrm{SDEX}}$ satisfies f.gL with a
  constant independent of $\varepsilon$.
* Lemma B.2.6, `CartisGouldToint.AppendixB.lemma_B_2_6`: the linesearches are exact; each iterate is
  the first global minimizer along the steepest-descent ray from the previous one.

## Implementation notes

* The function is `Optimization.zigZagFunction ε k_ε`, the iterates are
  `Optimization.zigZagIterate ε k_ε k`, and the condition on $\varepsilon$ is
  `Optimization.ZigZag.IsAdmissible`. A point $(x, y)$ of $\mathbb{R}^2$ is
  `z : EuclideanSpace ℝ (Fin 2)` with `z 0` $= x$ and `z 1` $= y$.

## Deviations from the source

* **Correction.** Lemma B.2.1 bounds the initial jet in addition to the endpoint residuals. See
  `CartisGouldToint.AppendixB.lemma_B_2_1_bound`.
* **Finite construction and integrality.** Lemma B.2.2 requires an integer stopping count satisfying
  the source identity and proves the first-hit property through that count. See
  `CartisGouldToint.AppendixB.lemma_B_2_2`.
* **Modified corridor construction.** Lemmas B.2.3–B.2.6 use a modified corridor extension that
  yields a global exact line minimizer. See `CartisGouldToint.AppendixB.lemma_B_2_3`,
  `CartisGouldToint.AppendixB.lemma_B_2_4`, `CartisGouldToint.AppendixB.lemma_B_2_5`,
  `CartisGouldToint.AppendixB.lemma_B_2_6`.
* **Lemma B.2.1** (correction). The bound on the interpolant and its derivatives also needs
  $|f_0|, |g_0|, |H_0| \le \kappa_f$. See `CartisGouldToint.AppendixB.lemma_B_2_1_bound`.
* **Corridor function (B.2.19) and Lemma B.2.6** (correction). The book's $f_2$ equals
  $(y - y_{\mathrm{mid}}(x))^2$ in the corridor and is continued by Hermite transitions to the
  constant $8\delta(x)^2$. With this bounded $f_2$, the first minimizer along the ray is only local,
  because $f_1$ keeps decreasing after the ray leaves the corridor. The construction uses
  $f_2(x, y) = \psi(y - y_{\mathrm{mid}}(x))$ with a twice continuously differentiable capped square
  $\psi$ instead. It agrees with the book's $f_2$ on the corridor, where all evaluations of the
  proof take place, and the line minimizer is then global. See `Optimization.ZigZag.f₂` and
  `CartisGouldToint.AppendixB.lemma_B_2_6`.
* **Lemma B.2.3** (generalization). The bound on $f_2$ holds on the bands
  $|y - y_{\mathrm{mid}}(x)| \le 2$, which contain the book's sets, and the bounds on its
  derivatives hold on all of $\mathbb{R}^2$. See `CartisGouldToint.AppendixB.lemma_B_2_3`.
* **Data (B.2.5)–(B.2.6)** (correction). The book prints the data for all $k \ge 0$, but the step
  length $\varepsilon + \omega_k$ vanishes at $k = 2k_\varepsilon$. The construction keeps
  $y_{\mathrm{mid}}$ constant after $x_{k_\varepsilon}$. See `Optimization.zigZagFunction`.
-/

open Set Finset Optimization
open scoped RealInnerProductSpace

namespace CartisGouldToint.AppendixB

/-! ### Lemma B.2.1 -/

/-- The polynomial $\sum_{i=0}^5 c_i t^i$ with coefficient vector $c \in \mathbb{R}^6$. -/
def quintic (c : Fin 6 → ℝ) (t : ℝ) : ℝ := ∑ i : Fin 6, c i * t ^ (i : ℕ)

/-- The coefficients $(c_1, 2c_2, 3c_3, 4c_4, 5c_5, 0)$ of the derivative of the quintic with
coefficients $c$. -/
def derivCoeff (c : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![c 1, 2 * c 2, 3 * c 3, 4 * c 4, 5 * c 5, 0]

/-- The quintic with coefficients $c$ has at $t$ the derivative given by the quintic with the
coefficients `CartisGouldToint.AppendixB.derivCoeff c`. -/
theorem hasDerivAt_quintic (c : Fin 6 → ℝ) (t : ℝ) :
    HasDerivAt (quintic c) (quintic (derivCoeff c) t) t := by
  have h : HasDerivAt (fun t => ∑ i : Fin 6, c i * t ^ (i : ℕ))
      (∑ i : Fin 6, c i * ((i : ℕ) * t ^ ((i : ℕ) - 1))) t :=
    HasDerivAt.fun_sum fun i _ => (hasDerivAt_pow _ t).const_mul (c i)
  refine h.congr_deriv ?_
  simp only [quintic, derivCoeff, Fin.sum_univ_six]
  simp
  ring

/-- The derivative of the quintic with coefficients $c$ is the quintic with the coefficients
`CartisGouldToint.AppendixB.derivCoeff c`. -/
theorem deriv_quintic (c : Fin 6 → ℝ) : deriv (quintic c) = quintic (derivCoeff c) :=
  funext fun t => (hasDerivAt_quintic c t).deriv

/-- The second derivative of the quintic with coefficients $c$ is the quintic with the coefficients
`CartisGouldToint.AppendixB.derivCoeff (CartisGouldToint.AppendixB.derivCoeff c)`. -/
theorem iteratedDeriv_two_quintic (c : Fin 6 → ℝ) :
    iteratedDeriv 2 (quintic c) = quintic (derivCoeff (derivCoeff c)) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_quintic, deriv_quintic]

/-- For $t \in [0, 1]$, $\bigl|\sum_{i=0}^5 c_i t^i\bigr| \le \sum_{i=0}^5 |c_i|$. -/
theorem abs_quintic_le (c : Fin 6 → ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |quintic c t| ≤ ∑ i : Fin 6, |c i| := by
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _)
    (by rw [abs_pow, abs_of_nonneg ht.1]; exact pow_le_one₀ ht.1 ht.2)

/-- The residuals (B.2.2) of the Hermite data: $r_0 = f_1 - f_0 - g_0 - H_0/2$,
$r_1 = g_1 - g_0 - H_0$ and $r_2 = H_1 - H_0$. -/
noncomputable def hermiteResidual (f₀ g₀ H₀ f₁ g₁ H₁ : ℝ) : Fin 3 → ℝ :=
  ![f₁ - f₀ - g₀ - H₀ / 2, g₁ - g₀ - H₀, H₁ - H₀]

/-- The coefficients (B.2.1) of the quintic Hermite interpolant: $c_0 = f_0$, $c_1 = g_0$,
$c_2 = H_0/2$, $c_3 = 10r_0 - 4r_1 + r_2/2$, $c_4 = -15r_0 + 7r_1 - r_2$ and
$c_5 = 6r_0 - 3r_1 + r_2/2$, with the residuals $r_i$ of (B.2.2). -/
noncomputable def hermiteCoeff (f₀ g₀ H₀ f₁ g₁ H₁ : ℝ) : Fin 6 → ℝ :=
  let r := hermiteResidual f₀ g₀ H₀ f₁ g₁ H₁
  ![f₀, g₀, H₀ / 2, 10 * r 0 - 4 * r 1 + r 2 / 2, -15 * r 0 + 7 * r 1 - r 2,
    6 * r 0 - 3 * r 1 + r 2 / 2]

/-- **Lemma B.2.1** of [cartis2022evaluation], the interpolant. For data
$f_0, g_0, H_0, f_1, g_1, H_1 \in \mathbb{R}$, the **quintic Hermite interpolant** is the
polynomial $p(t) = \sum_{i=0}^5 c_i t^i$ with the coefficients (B.2.1) and the residuals
(B.2.2). -/
noncomputable def hermiteQuintic (f₀ g₀ H₀ f₁ g₁ H₁ : ℝ) : ℝ → ℝ :=
  quintic (hermiteCoeff f₀ g₀ H₀ f₁ g₁ H₁)

/-- **Lemma B.2.1** of [cartis2022evaluation], interpolation. Let
$f_0, g_0, H_0, f_1, g_1, H_1 \in \mathbb{R}$, and let $p$ be the quintic Hermite interpolant
with the coefficients (B.2.1)–(B.2.2). Then
$$p(0) = f_0, \quad p'(0) = g_0, \quad p''(0) = H_0, \quad p(1) = f_1, \quad p'(1) = g_1, \quad
  p''(1) = H_1.$$
-/
theorem lemma_B_2_1 (f₀ g₀ H₀ f₁ g₁ H₁ : ℝ) :
    hermiteQuintic f₀ g₀ H₀ f₁ g₁ H₁ 0 = f₀ ∧
      deriv (hermiteQuintic f₀ g₀ H₀ f₁ g₁ H₁) 0 = g₀ ∧
      iteratedDeriv 2 (hermiteQuintic f₀ g₀ H₀ f₁ g₁ H₁) 0 = H₀ ∧
      hermiteQuintic f₀ g₀ H₀ f₁ g₁ H₁ 1 = f₁ ∧
      deriv (hermiteQuintic f₀ g₀ H₀ f₁ g₁ H₁) 1 = g₁ ∧
      iteratedDeriv 2 (hermiteQuintic f₀ g₀ H₀ f₁ g₁ H₁) 1 = H₁ := by
  simp only [hermiteQuintic, deriv_quintic, iteratedDeriv_two_quintic, quintic,
    Fin.sum_univ_six]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [derivCoeff, hermiteCoeff, hermiteResidual] <;> ring

/-- **Lemma B.2.1** of [cartis2022evaluation], bound. Let $\kappa_f \ge 1$. There is $\kappa_h > 0$
with the following property. Let $f_0, g_0, H_0, f_1, g_1, H_1 \in \mathbb{R}$ be data whose
residuals (B.2.2) satisfy $|r_i| \le \kappa_f$ for $i = 0, 1, 2$ (B.2.3), and assume
$|f_0|, |g_0|, |H_0| \le \kappa_f$. Then the quintic Hermite interpolant $p$ satisfies
$|p^{(i)}(t)| \le \kappa_h$ for all $t \in [0, 1]$ and $i \in \{0, 1, 2\}$.

**Correction.** The book assumes only the bounds (B.2.3) on the residuals. These bounds do not
control the constant and linear terms of $p$, so the bounds $|f_0|, |g_0|, |H_0| \le \kappa_f$
on the data at $0$ are added. The book's appeal to Theorem A.9.1 needs them implicitly: they are
the analogue of the hypothesis (A.31) of that theorem.

The proof takes $\kappa_h = 1000 \kappa_f$.

**Correction.** A bound on the endpoint residuals alone cannot bound the interpolating polynomial.
The initial value and both initial derivatives are also bounded by the common constant.
-/
theorem lemma_B_2_1_bound {κf : ℝ} (hκ : 1 ≤ κf) :
    ∃ κh : ℝ, 0 < κh ∧ ∀ f₀ g₀ H₀ f₁ g₁ H₁ : ℝ,
      (∀ i, |hermiteResidual f₀ g₀ H₀ f₁ g₁ H₁ i| ≤ κf) → |f₀| ≤ κf → |g₀| ≤ κf → |H₀| ≤ κf →
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ i ≤ 2,
        |iteratedDeriv i (hermiteQuintic f₀ g₀ H₀ f₁ g₁ H₁) t| ≤ κh := by
  refine ⟨1000 * κf, by positivity, fun f₀ g₀ H₀ f₁ g₁ H₁ hr hf hg hH t ht i hi => ?_⟩
  have hr0 := abs_le.1 (hr 0); have hr1 := abs_le.1 (hr 1); have hr2 := abs_le.1 (hr 2)
  simp only [hermiteResidual, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hr0 hr1 hr2
  set c := hermiteCoeff f₀ g₀ H₀ f₁ g₁ H₁
  have hf' := abs_le.1 hf; have hg' := abs_le.1 hg; have hH' := abs_le.1 hH
  set r₀ := f₁ - f₀ - g₀ - H₀ / 2
  set r₁ := g₁ - g₀ - H₀
  set r₂ := H₁ - H₀
  have b0 : |f₀| ≤ 23 * κf := by linarith
  have b1 : |g₀| ≤ 23 * κf := by linarith
  have b2 : |H₀ / 2| ≤ 23 * κf := abs_le.2 ⟨by linarith, by linarith⟩
  have b3 : |10 * r₀ - 4 * r₁ + r₂ / 2| ≤ 23 * κf := abs_le.2 ⟨by linarith, by linarith⟩
  have b4 : |-15 * r₀ + 7 * r₁ - r₂| ≤ 23 * κf := abs_le.2 ⟨by linarith, by linarith⟩
  have b5 : |6 * r₀ - 3 * r₁ + r₂ / 2| ≤ 23 * κf := abs_le.2 ⟨by linarith, by linarith⟩
  have hc : ∀ j, |c j| ≤ 23 * κf := by
    intro j
    fin_cases j
    · simpa [c, hermiteCoeff] using b0
    · simpa [c, hermiteCoeff] using b1
    · simpa [c, hermiteCoeff] using b2
    · simpa [c, hermiteCoeff, hermiteResidual] using b3
    · simpa [c, hermiteCoeff, hermiteResidual] using b4
    · simpa [c, hermiteCoeff, hermiteResidual] using b5
  interval_cases i
  · rw [iteratedDeriv_zero]
    refine (abs_quintic_le c ht).trans ?_
    simp only [Fin.sum_univ_six]
    linarith [hc 0, hc 1, hc 2, hc 3, hc 4, hc 5]
  · rw [iteratedDeriv_one, hermiteQuintic, deriv_quintic]
    refine (abs_quintic_le _ ht).trans ?_
    simp only [Fin.sum_univ_six]
    simp [derivCoeff, abs_mul]
    linarith [hc 0, hc 1, hc 2, hc 3, hc 4, hc 5]
  · rw [hermiteQuintic, iteratedDeriv_two_quintic]
    refine (abs_quintic_le _ ht).trans ?_
    simp only [Fin.sum_univ_six]
    simp [derivCoeff, abs_mul]
    linarith [hc 0, hc 1, hc 2, hc 3, hc 4, hc 5]

/-! ### Lemmas B.2.2–B.2.6 -/

variable {ε : ℝ} {kε : ℕ}

/-- **Lemma B.2.2** of [cartis2022evaluation]. Let $\varepsilon > 0$ with
$k_\varepsilon \varepsilon^2 = 1$ for an integer $k_\varepsilon$, let $f = f_{\mathrm{SDEX}}$,
and let $\omega_k = \varepsilon (k_\varepsilon - k)/k_\varepsilon$. Then:

* for $k \le k_\varepsilon$ the gradient at the iterate $(x_k, y_k)$ is (B.2.25) $$\nabla f(x_k,
  y_k) = -\frac{\varepsilon + \omega_k}{\sqrt{2}} \bigl(1, (-1)^k\bigr),$$ so that $\|\nabla
  f(x_k, y_k)\| = \varepsilon + \omega_k$;
* let $(z_k)$ be a sequence in $\mathbb{R}^2$ with $z_0 = 0$ and
  $z_{k+1} = z_k - \sqrt{2} \nabla f(z_k)$ whenever $\|\nabla f(z_j)\| > \varepsilon$ for all
  $j \le k$; then $z_k = (x_k, y_k)$ for all $k \le k_\varepsilon$, and $k_\varepsilon$ is the
  first index $k$ with $\|\nabla f(z_k)\| \le \varepsilon$.

The second part says that steepest descent with the step $\sqrt{2}$ from the origin produces the
zig-zag iterates and terminates after exactly $k_\varepsilon$ iterations. The function is
`Optimization.zigZagFunction ε k_ε`, the iterates are `Optimization.zigZagIterate ε k_ε k`,
$\omega_k$ is `Optimization.ZigZag.omega ε k_ε k`, and the first termination index is expressed
by `Optimization.IsFirstHit`.

**Reading.** The exact stopping count is stated for an integer index satisfying the source identity
with the tolerance. The trajectory is guaranteed through that count, using the actual gradient and
first-hit condition.
-/
theorem lemma_B_2_2 (hε : 0 < ε) (hkε : (kε : ℝ) * ε ^ 2 = 1) :
    (∀ k ≤ kε, gradient (zigZagFunction ε kε) (zigZagIterate ε kε k) =
        -((ε + ZigZag.omega ε kε k) / √2) • !₂[1, (-1) ^ k] ∧
      ‖gradient (zigZagFunction ε kε) (zigZagIterate ε kε k)‖ = ε + ZigZag.omega ε kε k) ∧
    ∀ z : ℕ → EuclideanSpace ℝ (Fin 2), z 0 = 0 →
      (∀ k, (∀ j ≤ k, ¬ ‖gradient (zigZagFunction ε kε) (z j)‖ ≤ ε) →
        z (k + 1) = z k - √2 • gradient (zigZagFunction ε kε) (z k)) →
      (∀ k ≤ kε, z k = zigZagIterate ε kε k) ∧
        IsFirstHit (fun k => ‖gradient (zigZagFunction ε kε) (z k)‖ ≤ ε) kε := by
  have hadm : ZigZag.IsAdmissible ε kε := ⟨hε, hkε⟩
  set f := zigZagFunction ε kε
  have hnorm : ∀ k ≤ kε, ‖gradient f (zigZagIterate ε kε k)‖ = ε + ZigZag.omega ε kε k :=
    fun k hk => (zigZag_gradient hadm hk).2.1
  have hgt : ∀ j < kε, ¬ ‖gradient f (zigZagIterate ε kε j)‖ ≤ ε := fun j hj => by
    rw [hnorm j hj.le, not_le]; linarith [hadm.omega_pos hj]
  refine ⟨fun k hk => ⟨(zigZag_gradient hadm hk).1, hnorm k hk⟩, fun z hz0 hz => ?_⟩
  have heq : ∀ k ≤ kε, ∀ j ≤ k, z j = zigZagIterate ε kε j := by
    intro k
    induction k with
    | zero => exact fun _ j hj => by rw [Nat.le_zero.1 hj, hz0, ZigZag.zigZagIterate_zero]
    | succ k ih =>
      intro hk j hj
      have hx := ih (Nat.le_of_succ_le hk)
      rcases Nat.lt_or_eq_of_le hj with hj | rfl
      · exact hx j (Nat.lt_succ_iff.1 hj)
      · have hstop : ∀ j ≤ k, ¬ ‖gradient f (z j)‖ ≤ ε := fun j hj => by
          rw [hx j hj]; exact hgt j (by omega)
        rw [hz k hstop, hx k le_rfl]
        exact ((zigZag_gradient hadm (k := k) (by omega)).2.2).symm
  have hx := heq kε le_rfl
  refine ⟨hx, ⟨?_, fun j hj => ?_⟩⟩
  · simp only
    rw [hx kε le_rfl, hnorm kε le_rfl, ZigZag.omega_self, add_zero]
  · simp only
    rw [hx j hj.le]; exact hgt j hj

/-- **Lemma B.2.3** of [cartis2022evaluation]. There is a constant $C \ge 0$ such that for every
$\varepsilon > 0$ with $k_\varepsilon \varepsilon^2 = 1$ the corridor function
$f_2(x, y) = \psi(y - y_{\mathrm{mid}}(x))$ of the construction is twice continuously
differentiable on $\mathbb{R}^2$, satisfies $|f_2(x, y)| \le C$ whenever
$|y - y_{\mathrm{mid}}(x)| \le 2$, and satisfies $\|\nabla f_2(x, y)\| \le C$ and
$\|\nabla^2 f_2(x, y)\| \le C$ for all $(x, y) \in \mathbb{R}^2$.

**Generalization.** The book bounds $f_2$ on $[y_{\mathrm{low}}(x) - 1, y_{\mathrm{low}}(x)]
\cup [y_{\mathrm{up}}(x), y_{\mathrm{up}}(x) + 1]$; the band $|y - y_{\mathrm{mid}}(x)| \le 2$
contains these sets. The bounds on the first and second derivatives, and hence on all first and
second partial derivatives, hold on all of $\mathbb{R}^2$.

The corridor function is `Optimization.ZigZag.f₂ ε k_ε`, with the capped square $\psi$ in place
of the book's (B.2.19); the two agree on the corridor. The middle line $y_{\mathrm{mid}}$ is
`Optimization.ZigZag.mid ε k_ε`.

**Correction.** The corridor is extended by a different twice continuously differentiable function.
It agrees with the source quadratic on the corridor, extends the stated uniform bounds, and makes
the first line minimizer global. The lower-bound and derivative assertions concern that modified
objective.
-/
theorem lemma_B_2_3 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ) (kε : ℕ), 0 < ε → (kε : ℝ) * ε ^ 2 = 1 →
      ContDiff ℝ 2 (ZigZag.f₂ ε kε) ∧ ∀ z : EuclideanSpace ℝ (Fin 2),
        (|z 1 - ZigZag.mid ε kε (z 0)| ≤ 2 → |ZigZag.f₂ ε kε z| ≤ C) ∧
        ‖fderiv ℝ (ZigZag.f₂ ε kε) z‖ ≤ C ∧ ‖iteratedFDeriv ℝ 2 (ZigZag.f₂ ε kε) z‖ ≤ C := by
  obtain ⟨C, hC, H⟩ := zigZag_hessian_bounds
  refine ⟨C, hC, fun ε kε hε hkε => ?_⟩
  obtain ⟨-, h2, hz⟩ := H ε kε ⟨hε, hkε⟩
  exact ⟨h2, fun z => ⟨(hz z).2.2.2, (hz z).2.2.1, (hz z).2.1⟩⟩

/-- **Lemma B.2.4** of [cartis2022evaluation]. There is $f_{\mathrm{low}} \in \mathbb{R}$ such that
for every $\varepsilon > 0$ with $k_\varepsilon \varepsilon^2 = 1$ the function
$f_{\mathrm{SDEX}}$ satisfies $f_{\mathrm{SDEX}}(z) \ge f_{\mathrm{low}}$ for all
$z \in \mathbb{R}^2$, that is, Assumption f.Bb with a constant independent of $\varepsilon$.

The assumption is `CartisGouldToint.Chapter02.AssumptionBb`.

**Correction.** The corridor is extended by a different twice continuously differentiable function.
It agrees with the source quadratic on the corridor, extends the stated uniform bounds, and makes
the first line minimizer global. The lower-bound and derivative assertions concern that modified
objective.
-/
theorem lemma_B_2_4 :
    ∃ flow : ℝ, ∀ (ε : ℝ) (kε : ℕ), 0 < ε → (kε : ℝ) * ε ^ 2 = 1 →
      Chapter02.AssumptionBb (zigZagFunction ε kε) flow := by
  obtain ⟨M, L, -, -, H⟩ := zigZag_bounds
  exact ⟨-M, fun ε kε hε hkε => (H ε kε ⟨hε, hkε⟩).2.1⟩

/-- **Lemma B.2.5** of [cartis2022evaluation]. There are constants $L$ and $C$ such that for every
$\varepsilon > 0$ with $k_\varepsilon \varepsilon^2 = 1$ the function $f_{\mathrm{SDEX}}$
satisfies Assumption f.gL with constant $L$, is twice continuously differentiable, and satisfies
$\|\nabla^2 f_{\mathrm{SDEX}}(z)\| \le C$ for all $z \in \mathbb{R}^2$.

The assumption is `CartisGouldToint.Chapter02.AssumptionGL`; it includes $L \ge 1$.

**Correction.** The corridor is extended by a different twice continuously differentiable function.
It agrees with the source quadratic on the corridor, extends the stated uniform bounds, and makes
the first line minimizer global. The lower-bound and derivative assertions concern that modified
objective.
-/
theorem lemma_B_2_5 :
    ∃ L C : ℝ, ∀ (ε : ℝ) (kε : ℕ), 0 < ε → (kε : ℝ) * ε ^ 2 = 1 →
      Chapter02.AssumptionGL (zigZagFunction ε kε) L ∧ ContDiff ℝ 2 (zigZagFunction ε kε) ∧
        ∀ z, ‖iteratedFDeriv ℝ 2 (zigZagFunction ε kε) z‖ ≤ C := by
  obtain ⟨M, L, -, hL, H⟩ := zigZag_bounds
  obtain ⟨C, -, H'⟩ := zigZag_hessian_bounds
  refine ⟨L, C, fun ε kε hε hkε => ?_⟩
  obtain ⟨hC, -, hlip⟩ := H ε kε ⟨hε, hkε⟩
  obtain ⟨h2, -, hz⟩ := H' ε kε ⟨hε, hkε⟩
  exact ⟨.of_lipschitz hC hL hlip, h2, fun z => (hz z).1⟩

/-- **Lemma B.2.6** of [cartis2022evaluation] (the linesearches are exact). Let $\varepsilon > 0$
with $k_\varepsilon \varepsilon^2 = 1$, let $f = f_{\mathrm{SDEX}}$, and let
$k < k_\varepsilon$. Then $\tau = \sqrt{2}$ is the first global minimizer of $\tau \mapsto
f\bigl((x_k, y_k) - \tau \nabla f(x_k, y_k)\bigr)$ on $[0, \infty)$, which is the exact
linesearch (2.2.26), and
$$(x_{k+1}, y_{k+1}) = (x_k, y_k) - \sqrt{2} \, \nabla f(x_k, y_k).$$

**Correction.** The book's proof shows only that $(x_{k+1}, y_{k+1})$ is the first local
minimizer along the ray: with the book's bounded corridor function (B.2.19), $f_1$ keeps
decreasing along the ray after the ray leaves the corridor. With the capped square $\psi$ of
`Optimization.ZigZag.f₂` the line minimizer is global, so the exact linesearch itself is
realized.

The exact linesearch is `LineSearch.IsExactLineMin`.

**Correction.** The corridor is extended by a different twice continuously differentiable function.
It agrees with the source quadratic on the corridor, extends the stated uniform bounds, and makes
the first line minimizer global. The lower-bound and derivative assertions concern that modified
objective.
-/
theorem lemma_B_2_6 (hε : 0 < ε) (hkε : (kε : ℝ) * ε ^ 2 = 1) {k : ℕ} (hk : k < kε) :
    LineSearch.IsExactLineMin (zigZagFunction ε kε) (zigZagIterate ε kε k) √2 ∧
      zigZagIterate ε kε (k + 1) = zigZagIterate ε kε k -
        √2 • gradient (zigZagFunction ε kε) (zigZagIterate ε kε k) :=
  ⟨zigZag_isExactLineMin ⟨hε, hkε⟩ hk, (zigZag_gradient ⟨hε, hkε⟩ hk.le).2.2⟩

end CartisGouldToint.AppendixB
