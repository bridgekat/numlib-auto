/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Flat functions

A smooth function is **flat** at a point if all its derivatives vanish there. This file builds flat
functions from Mathlib's `expNegInvGlue`, which is $e^{-1/x}$ for $x > 0$ and $0$ for $x \le 0$.
They give the classical examples which show that the derivatives at a point cannot decide whether
the point is a local minimizer ([cartis2022evaluation], Example 12.1.1 and its variant (12.1.3)).

The first family is $\mathrm{expNegInvGlue} \circ q$ for a smooth function $q$ that vanishes at a
point $x_0$, for example $e^{-1/x_1^2}$ extended by $0$. The second family consists of the flat
oscillating functions
$$\Phi_{P,Q}(t) = \Bigl(P(1/t) \sin(1/t) + Q(1/t) \cos(1/t)\Bigr) e^{-1/t^2}, \qquad \Phi_{P,Q}(0) =
  0,$$
for real polynomials $P$ and $Q$. The derivative of $\Phi_{P,Q}$ is $\Phi_{\tilde P, \tilde Q}$ with
$\tilde P = -X^2 P' + X^2 Q + 2X^3 P$ and $\tilde Q = -X^2 P - X^2 Q' + 2X^3 Q$, again of this form,
so $\Phi_{P,Q}$ is $C^\infty$. In particular $t \mapsto \sin(1/t)\, e^{-1/t^2}$ is $C^\infty$ and
flat at $0$.

## Main definitions

* `oscFlat`: the flat oscillating function $\Phi_{P,Q}$.
* `oscFlatDerivP`, `oscFlatDerivQ`: the polynomials $\tilde P$ and $\tilde Q$ with
  $\Phi_{P,Q}' = \Phi_{\tilde P,\tilde Q}$.

## Main results

* `iteratedFDeriv_expNegInvGlue_zero`: all derivatives of `expNegInvGlue` vanish at $0$.
* `iteratedFDeriv_expNegInvGlue_comp_eq_zero`: if $q$ is $C^\infty$ and $q(x_0) = 0$, all
  derivatives of $\mathrm{expNegInvGlue} \circ q$ vanish at $x_0$.
* `hasDerivAt_oscFlat`: the derivative of $\Phi_{P,Q}$ is $\Phi_{\tilde P,\tilde Q}$ at every point.
* `contDiff_oscFlat`: $\Phi_{P,Q}$ is $C^\infty$.
-/

open Filter Topology Set
open scoped ContDiff

/-- For every natural number $k$, the $k$-th derivative of `expNegInvGlue` at $0$ is zero. The
function vanishes on $(-\infty, 0]$. -/
theorem iteratedFDeriv_expNegInvGlue_zero (k : ℕ) : iteratedFDeriv ℝ k expNegInvGlue 0 = 0 := by
  have hc : Continuous (iteratedFDeriv ℝ k expNegInvGlue) :=
    (expNegInvGlue.contDiff (n := ⊤)).continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hzero : Iio (0 : ℝ) ⊆ {y | iteratedFDeriv ℝ k expNegInvGlue y = 0} := fun y hy => by
    have : expNegInvGlue =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hy] with z hz using expNegInvGlue.zero_of_nonpos hz.le
    rw [Set.mem_ofPred_eq, (this.iteratedFDeriv ℝ k).eq_of_nhds, iteratedFDeriv_fun_zero]
    rfl
  have := (isClosed_eq hc continuous_const).closure_subset_iff.2 hzero
  rw [closure_Iio] at this
  exact this (Set.mem_Iic.2 le_rfl)

/-- **Flatness of `expNegInvGlue` composed with a smooth function that vanishes at a point.** Let
$E$ be a real normed space, let $q : E \to \mathbb{R}$ be $C^\infty$, and let $x_0 \in E$ with
$q(x_0) = 0$. Then for every natural number $k$, the $k$-th Fréchet derivative of
$x \mapsto \mathrm{expNegInvGlue}(q(x))$ at $x_0$ is zero.

An example is $e^{-1/x_1^2}$, extended by $0$ where $x_1 = 0$. -/
theorem iteratedFDeriv_expNegInvGlue_comp_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {q : E → ℝ} (hq : ContDiff ℝ ∞ q) {x₀ : E} (hq0 : q x₀ = 0) (k : ℕ) :
    iteratedFDeriv ℝ k (fun x => expNegInvGlue (q x)) x₀ = 0 := by
  set D : ℝ := 1 + ∑ i ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ i q x₀‖
  have hD1 : 1 ≤ D := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have h := norm_iteratedFDeriv_comp_le (N := ∞) (expNegInvGlue.contDiff (n := ⊤)) hq
    (n := k) (by exact_mod_cast le_top) x₀ (C := 0)
    (fun i _ => by simp [hq0, iteratedFDeriv_expNegInvGlue_zero]) (D := D)
    (fun i hi hik => by
      calc ‖iteratedFDeriv ℝ i q x₀‖ ≤ ∑ j ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ j q x₀‖ :=
            Finset.single_le_sum (f := fun j => ‖iteratedFDeriv ℝ j q x₀‖)
              (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (show i < k + 1 by omega))
        _ ≤ D := le_add_of_nonneg_left zero_le_one
        _ ≤ D ^ i := le_self_pow₀ hD1 (Nat.one_le_iff_ne_zero.1 hi))
  simp only [mul_zero, zero_mul] at h
  exact norm_le_zero_iff.1 h

/-- For $s \ge 0$, $\mathrm{expNegInvGlue}(s) \le s$; that is, $e^{-1/s} \le s$ for $s > 0$. -/
theorem expNegInvGlue_le_self {s : ℝ} (hs : 0 ≤ s) : expNegInvGlue s ≤ s := by
  rcases hs.eq_or_lt with rfl | hs
  · simp
  · rw [expNegInvGlue, ite_eq_right_iff.2 fun h => absurd h (not_le.2 hs)]
    have h1 := Real.add_one_le_exp s⁻¹
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) hs]
    linarith [inv_pos.2 hs]

/-- For real polynomials $P$ and $Q$, the **flat oscillating function** is
$$\Phi_{P,Q}(t) = \Bigl(P(1/t) \sin(1/t) + Q(1/t) \cos(1/t)\Bigr) e^{-1/t^2}$$
for $t \neq 0$, and $\Phi_{P,Q}(0) = 0$. These functions are the building blocks of Lewis'
example (12.1.3) of [cartis2022evaluation].

The factor $e^{-1/t^2}$ is `expNegInvGlue (t ^ 2)`, and $1/t$ is `t⁻¹`. The value $0$ at $t = 0$
comes from $\mathrm{expNegInvGlue}(0) = 0$. -/
noncomputable def oscFlat (P Q : Polynomial ℝ) (t : ℝ) : ℝ :=
  (P.eval t⁻¹ * Real.sin t⁻¹ + Q.eval t⁻¹ * Real.cos t⁻¹) * expNegInvGlue (t ^ 2)

/-- The defining formula of `oscFlat`: $\Phi_{P,Q}(t) = \bigl(P(1/t) \sin(1/t) + Q(1/t)
\cos(1/t)\bigr) \cdot \mathrm{expNegInvGlue}(t^2)$ for every $t \in \mathbb{R}$, with $1/t$ read
as `t⁻¹`. -/
theorem oscFlat_def (P Q : Polynomial ℝ) (t : ℝ) :
    oscFlat P Q t =
      (P.eval t⁻¹ * Real.sin t⁻¹ + Q.eval t⁻¹ * Real.cos t⁻¹) * expNegInvGlue (t ^ 2) :=
  rfl

/-- The polynomial $-X^2 P' + X^2 Q + 2X^3 P$, which multiplies $\sin(1/t)$ in the derivative of
$\Phi_{P,Q}$. -/
noncomputable def oscFlatDerivP (P Q : Polynomial ℝ) : Polynomial ℝ :=
  -(Polynomial.X ^ 2 * Polynomial.derivative P) + Polynomial.X ^ 2 * Q + 2 * Polynomial.X ^ 3 * P

/-- The polynomial $-X^2 P - X^2 Q' + 2X^3 Q$, which multiplies $\cos(1/t)$ in the derivative of
$\Phi_{P,Q}$. -/
noncomputable def oscFlatDerivQ (P Q : Polynomial ℝ) : Polynomial ℝ :=
  -(Polynomial.X ^ 2 * P) - Polynomial.X ^ 2 * Polynomial.derivative Q + 2 * Polynomial.X ^ 3 * Q

/-- For every real polynomial $R$ there is a real polynomial $S$ with $|R(u)| \le S(u^2)$ for all
$u \in \mathbb{R}$. -/
theorem abs_eval_le_eval_sq (R : Polynomial ℝ) :
    ∃ S : Polynomial ℝ, ∀ u : ℝ, |R.eval u| ≤ S.eval (u ^ 2) := by
  refine ⟨∑ i ∈ Finset.range (R.natDegree + 1), Polynomial.C |R.coeff i| * (1 + Polynomial.X ^ i),
    fun u => ?_⟩
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_finsetSum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_pow, Polynomial.eval_X, abs_mul, abs_pow]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rcases le_total |u| 1 with h | h
  · have := pow_le_one₀ (abs_nonneg u) h (n := i)
    have : 0 ≤ (u ^ 2) ^ i := by positivity
    linarith
  · have : |u| ^ i ≤ (u ^ 2) ^ i := by
      rw [← sq_abs u]
      exact pow_le_pow_left₀ (abs_nonneg u) (by nlinarith) i
    linarith

/-- For every real polynomial $R$, $R(1/t)\, e^{-1/t^2} \to 0$ as $t \to 0$. -/
theorem tendsto_eval_inv_mul_expNegInvGlue_sq (R : Polynomial ℝ) :
    Tendsto (fun t : ℝ => R.eval t⁻¹ * expNegInvGlue (t ^ 2)) (𝓝 0) (𝓝 0) := by
  obtain ⟨S, hS⟩ := abs_eval_le_eval_sq R
  have h2 : Tendsto (fun t : ℝ => t ^ 2) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_pow 2).tendsto (0 : ℝ)
  have hlim := (expNegInvGlue.tendsto_polynomial_inv_mul_zero S).comp h2
  refine squeeze_zero_norm (fun t => ?_) hlim
  simp only [Function.comp_apply, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (expNegInvGlue.nonneg _)]
  have := hS t⁻¹
  rw [inv_pow] at this
  exact mul_le_mul_of_nonneg_right this (expNegInvGlue.nonneg _)

/-- For all real polynomials $P$ and $Q$, the flat oscillating function $\Phi_{P,Q}$ is continuous
at $0$. -/
theorem continuousAt_oscFlat_zero (P Q : Polynomial ℝ) : ContinuousAt (oscFlat P Q) 0 := by
  have h0 : oscFlat P Q 0 = 0 := by simp [oscFlat]
  rw [ContinuousAt, h0]
  have hP := tendsto_eval_inv_mul_expNegInvGlue_sq P
  have hQ := tendsto_eval_inv_mul_expNegInvGlue_sq Q
  refine squeeze_zero_norm (fun t => (?_ : ‖oscFlat P Q t‖ ≤
    |P.eval t⁻¹ * expNegInvGlue (t ^ 2)| + |Q.eval t⁻¹ * expNegInvGlue (t ^ 2)|))
    (by simpa using hP.abs.add hQ.abs)
  have hg := expNegInvGlue.nonneg (t ^ 2)
  have h1 := Real.abs_sin_le_one t⁻¹
  have h2 := Real.abs_cos_le_one t⁻¹
  rw [oscFlat, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hg, ← add_mul]
  refine mul_le_mul_of_nonneg_right ((abs_add_le _ _).trans ?_) hg
  rw [abs_mul, abs_mul]
  gcongr
  · exact mul_le_of_le_one_right (abs_nonneg _) h1
  · exact mul_le_of_le_one_right (abs_nonneg _) h2

/-- For real polynomials $P, Q$ and $t \neq 0$, the derivative of $\Phi_{P,Q}$ at $t$ is
$\Phi_{\tilde P, \tilde Q}(t)$, where $\tilde P = -X^2 P' + X^2 Q + 2X^3 P$ and
$\tilde Q = -X^2 P - X^2 Q' + 2X^3 Q$. -/
theorem hasDerivAt_oscFlat_of_ne (P Q : Polynomial ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (oscFlat P Q) (oscFlat (oscFlatDerivP P Q) (oscFlatDerivQ P Q) t) t := by
  have heq : oscFlat P Q =ᶠ[𝓝 t] fun s => (P.eval s⁻¹ * Real.sin s⁻¹ + Q.eval s⁻¹ * Real.cos s⁻¹) *
      Real.exp (-(s⁻¹ ^ 2)) := by
    filter_upwards [isOpen_ne.mem_nhds ht] with s hs
    have hpos : 0 < s ^ 2 := by positivity
    simp only [oscFlat, expNegInvGlue, not_le.2 hpos, ite_false, inv_pow]
  have hu : HasDerivAt (fun s : ℝ => s⁻¹) (-(t ^ 2)⁻¹) t := hasDerivAt_inv ht
  have hP := (P.hasDerivAt t⁻¹).comp t hu
  have hQ := (Q.hasDerivAt t⁻¹).comp t hu
  have hs := (Real.hasDerivAt_sin t⁻¹).comp t hu
  have hc := (Real.hasDerivAt_cos t⁻¹).comp t hu
  have he := (Real.hasDerivAt_exp (-(t⁻¹ ^ 2))).comp t ((hu.pow 2).neg)
  have := (((hP.mul hs).add (hQ.mul hc)).mul he).congr_of_eventuallyEq heq
  convert this using 1
  have hpos : 0 < t ^ 2 := by positivity
  simp only [oscFlat, oscFlatDerivP, oscFlatDerivQ, expNegInvGlue, not_le.2 hpos, ite_false,
    Polynomial.eval_add, Polynomial.eval_neg, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_ofNat, Function.comp_apply,
    inv_pow, Pi.mul_apply, Pi.add_apply, Pi.neg_apply, Pi.pow_apply]
  field_simp
  ring

/-- For real polynomials $P, Q$ and every $t \in \mathbb{R}$, the derivative of $\Phi_{P,Q}$ at $t$
is $\Phi_{\tilde P, \tilde Q}(t)$, where $\tilde P = -X^2 P' + X^2 Q + 2X^3 P$ and
$\tilde Q = -X^2 P - X^2 Q' + 2X^3 Q$. At $t = 0$ both sides vanish. -/
theorem hasDerivAt_oscFlat (P Q : Polynomial ℝ) (t : ℝ) :
    HasDerivAt (oscFlat P Q) (oscFlat (oscFlatDerivP P Q) (oscFlatDerivQ P Q) t) t :=
  hasDerivAt_of_hasDerivAt_of_ne' (fun _ hy => hasDerivAt_oscFlat_of_ne P Q hy)
    (continuousAt_oscFlat_zero P Q) (continuousAt_oscFlat_zero _ _) t

/-- For all real polynomials $P$ and $Q$, the flat oscillating function $\Phi_{P,Q}$ is of class
$C^n$ for every $n \in \mathbb{N} \cup \{\infty\}$.

The derivative of $\Phi_{P,Q}$ is again a flat oscillating function (`hasDerivAt_oscFlat`). By
induction, every iterated derivative is a flat oscillating function, and hence differentiable. -/
theorem contDiff_oscFlat (P Q : Polynomial ℝ) {n : ℕ∞} : ContDiff ℝ n (oscFlat P Q) := by
  have hderiv : ∀ P Q : Polynomial ℝ,
      deriv (oscFlat P Q) = oscFlat (oscFlatDerivP P Q) (oscFlatDerivQ P Q) :=
    fun P Q => funext fun t => (hasDerivAt_oscFlat P Q t).deriv
  have hiter : ∀ m : ℕ, ∃ P' Q' : Polynomial ℝ, iteratedDeriv m (oscFlat P Q) = oscFlat P' Q' := by
    intro m
    induction m with
    | zero => exact ⟨P, Q, iteratedDeriv_zero⟩
    | succ m ih =>
      obtain ⟨P', Q', h⟩ := ih
      exact ⟨_, _, by rw [iteratedDeriv_succ, h, hderiv]⟩
  refine contDiff_of_differentiable_iteratedDeriv fun m _ => ?_
  obtain ⟨P', Q', h⟩ := hiter m
  rw [h]
  exact fun t => (hasDerivAt_oscFlat P' Q' t).differentiableAt


