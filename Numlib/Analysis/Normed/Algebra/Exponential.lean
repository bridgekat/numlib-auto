/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The exponential in a Banach algebra: perturbation and conditioning

Let $\mathbb{A}$ be a complete normed $\mathbb{R}$-algebra; complex matrices are one through
`NormedAlgebra.complexToReal`. This module develops the first-order perturbation theory of
$t \mapsto \exp(ta)$ for Mathlib's exponential `NormedSpace.exp`. The central fact is the
variation-of-constants identity
$$\exp(t(a + e)) - \exp(ta) = \int_0^t \exp((t - s)a)\, e\, \exp(s(a + e))\, ds.$$
Its first-order term in $e$ is the Fréchet derivative $L(a, t)$ of $a \mapsto \exp(ta)$, with $L(a,
t)\, e = \int_0^t \exp((t - s)a)\, e\, \exp(sa)\, ds$. From it comes Van Loan's relative condition
number $\nu(a, t) = \|L(a, t)\| \|a\| / \|\exp(ta)\|$ of the exponential ([golub2013matrix],
§9.3.2), which is the relative condition number of $a \mapsto \exp(ta)$ in the sense of Higham,
*Functions of Matrices*, §3.1. The module also bounds the resolvent in a complex Banach algebra
through the Laplace transform $(z - a)^{-1} = \int_0^\infty e^{-zt} \exp(ta)\, dt$
([golub2013matrix], (9.3.6)).

Section 9.3.2 of [golub2013matrix] states that $\nu(A, t) = t \|A\|_2$ holds if and only if $A$ is
normal. The equality criterion of this module shows that equality holds whenever
$\|\exp(sa)\| = e^{cs}$ for $s \in [0, t]$. Normal matrices satisfy this with $c$ the spectral
abscissa, but so does the non-normal matrix
$[1] \oplus \begin{bmatrix} 0 & 1 \\ 0 & 0 \end{bmatrix}$, so the direction "only if" is false.

## Main definitions

* `NormedSpace.expFrechet`: the Fréchet derivative $L(a, t)$ of $a \mapsto \exp(ta)$, the continuous
  linear map $e \mapsto \int_0^t \exp((t - s)a)\, e\, \exp(sa)\, ds$.
* `NormedSpace.expCondNumber`: Van Loan's condition number
  $\nu(a, t) = \|L(a, t)\| \|a\| / \|\exp(ta)\|$.

## Main results

* `NormedSpace.continuous_exp_real`, `NormedSpace.exp_add_of_commute_real`,
  `NormedSpace.exp_nsmul_real`: the exponential is continuous, $\exp(x + y) = \exp x \exp y$ for
  commuting $x$ and $y$, and $\exp(mx) = (\exp x)^m$.
* `NormedSpace.norm_exp_le_exp_norm`, `NormedSpace.norm_exp_sub_one_le_mul_exp_norm`: if
  $\|1\| = 1$, then $\|\exp x\| \le e^{\|x\|}$ and $\|\exp x - 1\| \le \|x\| e^{\|x\|}$.
* `NormedSpace.exp_eq_sum_range_of_pow_eq_zero`, `NormedSpace.exp_eq_one_add_of_sq_eq_zero`: the
  exponential of a nilpotent element of a topological algebra is a finite sum.
* `NormedSpace.exp_smul_add_sub_exp_smul`: the variation-of-constants identity, with the norm bound
  `NormedSpace.norm_exp_smul_add_sub_exp_smul_le`.
* `NormedSpace.eq_exp_smul_of_hasDerivAt`: $t \mapsto \exp(ta)$ is the unique solution of $X' = aX$,
  $X(0) = 1$.
* `NormedSpace.hasFDerivAt_exp_smul`: $L(a, t)$ is the Fréchet derivative of $b \mapsto \exp(tb)$ at
  $a$.
* `NormedSpace.mul_norm_le_expCondNumber`: $t \|a\| \le \nu(a, t)$ for $t \ge 0$.
* `NormedSpace.expCondNumber_eq_of_norm_exp_smul_eq`: if $\|\exp(sa)\| = e^{cs}$ on $[0, t]$, then
  $\nu(a, t) = t \|a\|$.
* `norm_resolvent_le_of_norm_exp_smul_le`: in a complex Banach algebra, if $\|\exp(ta)\| \le M$ for
  $t \ge 0$ and $\operatorname{Re} z > 0$, then $z \notin \sigma(a)$ and
  $\|(z - a)^{-1}\| \le M / \operatorname{Re} z$.

## Implementation notes

* Mathlib's `NormedSpace.exp_continuous`, `NormedSpace.exp_add_of_commute` and
  `NormedSpace.exp_nsmul` ask for a normed $\mathbb{Q}$-algebra structure. The versions with the
  suffix `_real` ask instead for a complete normed $\mathbb{R}$-algebra, and are proved from the
  analyticity of the exponential over $\mathbb{R}$.
* `NormedSpace.expFrechet` is an interval integral of continuous linear maps, that is, an integral
  in the space of operators on $\mathbb{A}$. `NormedSpace.expFrechet_apply` evaluates it at a
  direction.
* The module extends the Mathlib module `Mathlib.Analysis.Normed.Algebra.Exponential`, whose name it
  mirrors.
-/

open Filter Topology MeasureTheory

namespace NormedSpace

section Nilpotent

variable {𝕂 𝔸 : Type*} [Field 𝕂] [CharZero 𝕂] [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸]
  [IsTopologicalRing 𝔸]

variable (𝕂) in
/-- Let $\mathbb{K}$ be a field of characteristic zero and let $\mathbb{A}$ be a topological ring
that is a $\mathbb{K}$-algebra. The **exponential of a nilpotent element** is a finite sum: if
$x^n = 0$, then
$$\exp x = \sum_{k < n} \frac{x^k}{k!}.$$
-/
theorem exp_eq_sum_range_of_pow_eq_zero {x : 𝔸} {n : ℕ} (hx : x ^ n = 0) :
    exp x = ∑ k ∈ Finset.range n, ((k.factorial : 𝕂)⁻¹) • x ^ k := by
  rw [exp_eq_tsum 𝕂]
  refine tsum_eq_sum fun k hk => ?_
  rw [Finset.mem_range, not_lt] at hk
  rw [show k = n + (k - n) by omega, pow_add, hx, zero_mul, smul_zero]

/-- Let $\mathbb{A}$ be a topological ring that is a $\mathbb{Q}$-algebra. If $x \in \mathbb{A}$
satisfies $x^2 = 0$, then $\exp x = 1 + x$. -/
theorem exp_eq_one_add_of_sq_eq_zero [Algebra ℚ 𝔸] {x : 𝔸} (hx : x ^ 2 = 0) : exp x = 1 + x := by
  rw [exp_eq_sum_range_of_pow_eq_zero ℚ hx]
  simp [Finset.sum_range_succ]

end Nilpotent

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- In a complete normed $\mathbb{R}$-algebra, the exponential $\exp : \mathbb{A} \to \mathbb{A}$ is
continuous. The proof uses the analyticity of the exponential over $\mathbb{R}$; Mathlib's
`NormedSpace.exp_continuous` asks for a normed $\mathbb{Q}$-algebra structure. -/
theorem continuous_exp_real : Continuous (exp : 𝔸 → 𝔸) :=
  continuous_iff_continuousAt.mpr fun x => (exp_analytic (𝕂 := ℝ) x).continuousAt

/-- For a continuous function $c : X \to \mathbb{R}$, the map $s \mapsto \exp(c(s)\, a)$ is
continuous. -/
private theorem continuous_exp_smul {X : Type*} [TopologicalSpace X] {c : X → ℝ}
    (hc : Continuous c) (a : 𝔸) : Continuous fun s => exp (c s • a) :=
  continuous_exp_real.comp (hc.smul continuous_const)

/-- If $x$ and $y$ commute in a complete normed $\mathbb{R}$-algebra, then
$\exp(x + y) = \exp x \exp y$. Mathlib's `NormedSpace.exp_add_of_commute` asks for a normed
$\mathbb{Q}$-algebra structure. -/
theorem exp_add_of_commute_real {x y : 𝔸} (h : Commute x y) :
    exp (x + y) = exp x * exp y :=
  exp_add_of_commute_of_mem_ball (𝕂 := ℝ) h
    ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)

/-- In a complete normed $\mathbb{R}$-algebra, $\exp(mx) = (\exp x)^m$ for every $x$ and every
natural number $m$. Mathlib's `NormedSpace.exp_nsmul` asks for a normed $\mathbb{Q}$-algebra
structure. -/
theorem exp_nsmul_real (m : ℕ) (x : 𝔸) : exp (m • x) = exp x ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [succ_nsmul, exp_add_of_commute_real ((Commute.refl x).smul_left m), ih, pow_succ]

section NormOneClass

variable [NormOneClass 𝔸]

/-- In a complete normed $\mathbb{R}$-algebra with $\|1\| = 1$, every $x$ satisfies
$\|\exp x\| \le e^{\|x\|}$. -/
theorem norm_exp_le_exp_norm (x : 𝔸) : ‖exp x‖ ≤ Real.exp ‖x‖ := by
  have hx := exp_series_hasSum_exp' (𝕂 := ℝ) x
  have hr := exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖
  rw [← Real.exp_eq_exp_ℝ] at hr
  refine hx.norm_le_of_bounded hr fun n => ?_
  rw [norm_smul, Real.norm_of_nonneg (by positivity), smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (norm_pow_le x n) (by positivity)

/-- In a complete normed $\mathbb{R}$-algebra with $\|1\| = 1$, every $x$ satisfies
$\|\exp x - 1\| \le \|x\| e^{\|x\|}$. -/
theorem norm_exp_sub_one_le_mul_exp_norm (x : 𝔸) : ‖exp x - 1‖ ≤ ‖x‖ * Real.exp ‖x‖ := by
  have hx := (hasSum_nat_add_iff' 1).mpr (exp_series_hasSum_exp' (𝕂 := ℝ) x)
  have hr := (hasSum_nat_add_iff' 1).mpr (exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖)
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero,
    Nat.cast_one, inv_one, one_smul] at hx hr
  rw [← Real.exp_eq_exp_ℝ] at hr
  refine (hx.norm_le_of_bounded hr fun n => ?_).trans ?_
  · rw [norm_smul, Real.norm_of_nonneg (by positivity), smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (norm_pow_le x _) (by positivity)
  · have h := Real.add_one_le_exp (-‖x‖)
    have h2 : Real.exp (-‖x‖) * Real.exp ‖x‖ = 1 := by rw [← Real.exp_add, neg_add_cancel,
      Real.exp_zero]
    nlinarith [Real.exp_pos ‖x‖, norm_nonneg x]

end NormOneClass

/-- The derivative of $s \mapsto \exp((t - s)a)$ is $-a \exp((t - s)a)$. -/
private theorem hasDerivAt_exp_sub_smul (a : 𝔸) (t s : ℝ) :
    HasDerivAt (fun s : ℝ => exp ((t - s) • a)) (-(a * exp ((t - s) • a))) s := by
  have h := (hasDerivAt_exp_smul_const' a (t - s)).scomp s ((hasDerivAt_id s).const_sub t)
  simpa [Function.comp_def] using h

omit [CompleteSpace 𝔸] in
private theorem commute_exp_smul (a : 𝔸) (r : ℝ) : Commute a (exp (r • a)) :=
  ((Commute.refl a).smul_right r).exp_right

private theorem continuous_variation (a e b : 𝔸) (t : ℝ) :
    Continuous fun s : ℝ => exp ((t - s) • a) * e * exp (s • b) :=
  ((continuous_exp_smul (continuous_const.sub continuous_id) a).mul continuous_const).mul
    (continuous_exp_smul continuous_id b)

/-- The **variation-of-constants identity**. Let $\mathbb{A}$ be a complete normed
$\mathbb{R}$-algebra, let $a, e \in \mathbb{A}$ and let $t \in \mathbb{R}$. Then
$$\exp(t(a + e)) - \exp(ta) = \int_0^t \exp((t - s)a)\, e\, \exp(s(a + e))\, ds.$$

The integral is an interval integral, so for $t < 0$ it is $-\int_t^0$. The integrand is the
derivative of $s \mapsto \exp((t - s)a) \exp(s(a + e))$; the terms with $a$ cancel because $a$
commutes with $\exp((t - s)a)$. -/
theorem exp_smul_add_sub_exp_smul (a e : 𝔸) (t : ℝ) :
    exp (t • (a + e)) - exp (t • a) =
      ∫ s in (0 : ℝ)..t, exp ((t - s) • a) * e * exp (s • (a + e)) := by
  have hderiv : ∀ s, HasDerivAt (fun s : ℝ => exp ((t - s) • a) * exp (s • (a + e)))
      (exp ((t - s) • a) * e * exp (s • (a + e))) s := by
    intro s
    have h := HasDerivAt.mul (hasDerivAt_exp_sub_smul a t s) (hasDerivAt_exp_smul_const' (a + e) s)
    convert h using 1
    rw [neg_mul, (commute_exp_smul a (t - s)).eq]
    noncomm_ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s)
    ((continuous_variation a e (a + e) t).intervalIntegrable _ _)]
  simp

/-- The norm bound of the variation-of-constants identity. Let $\mathbb{A}$ be a complete normed
$\mathbb{R}$-algebra, let $a, e \in \mathbb{A}$ and let $t \ge 0$. Then
$$\|\exp(t(a + e)) - \exp(ta)\| \le \|e\| \int_0^t \|\exp((t - s)a)\| \, \|\exp(s(a + e))\| \,
  ds.$$
-/
theorem norm_exp_smul_add_sub_exp_smul_le (a e : 𝔸) {t : ℝ} (ht : 0 ≤ t) :
    ‖exp (t • (a + e)) - exp (t • a)‖ ≤
      ‖e‖ * ∫ s in (0 : ℝ)..t, ‖exp ((t - s) • a)‖ * ‖exp (s • (a + e))‖ := by
  rw [exp_smul_add_sub_exp_smul, ← intervalIntegral.integral_const_mul]
  refine (intervalIntegral.norm_integral_le_integral_norm ht).trans
    (intervalIntegral.integral_mono_on ht ?_ ?_ fun s _ => ?_)
  · exact (continuous_variation a e (a + e) t).norm.intervalIntegrable _ _
  · exact (continuous_const.mul ((continuous_exp_smul (continuous_const.sub continuous_id)
      a).norm.mul (continuous_exp_smul continuous_id (a + e)).norm)).intervalIntegrable _ _
  · calc ‖exp ((t - s) • a) * e * exp (s • (a + e))‖
        ≤ ‖exp ((t - s) • a)‖ * ‖e‖ * ‖exp (s • (a + e))‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ = ‖e‖ * (‖exp ((t - s) • a)‖ * ‖exp (s • (a + e))‖) := by ring

/-- **$\exp(ta)$ is the unique solution of $X' = aX$, $X(0) = 1$.** Let $\mathbb{A}$ be a complete
normed $\mathbb{R}$-algebra, let $a \in \mathbb{A}$, and let $X : \mathbb{R} \to \mathbb{A}$
satisfy $X'(t) = a X(t)$ for every $t$ and $X(0) = 1$. Then $X(t) = \exp(ta)$ for every
$t \in \mathbb{R}$. This is the characterization of $e^{tA}$ in [golub2013matrix], §9.3.2.

That $t \mapsto \exp(ta)$ is a solution is Mathlib's `hasDerivAt_exp_smul_const'`. -/
theorem eq_exp_smul_of_hasDerivAt {a : 𝔸} {X : ℝ → 𝔸} (hX : ∀ t, HasDerivAt X (a * X t) t)
    (h0 : X 0 = 1) (t : ℝ) : X t = exp (t • a) := by
  have hψ : ∀ s, HasDerivAt (fun s => exp ((0 - s) • a) * X s) 0 s := by
    intro s
    have := HasDerivAt.mul (hasDerivAt_exp_sub_smul a 0 s) (hX s)
    convert this using 1
    rw [neg_mul, (commute_exp_smul a (0 - s)).eq]
    noncomm_ring
  have hconst : exp ((0 - t) • a) * X t = 1 := by
    have := is_const_of_deriv_eq_zero (fun s => (hψ s).differentiableAt) (fun s => (hψ s).deriv)
      t 0
    simpa [h0] using this
  have hinv : exp (t • a) * exp ((0 - t) • a) = 1 := by
    rw [← exp_add_of_commute_real (((Commute.refl a).smul_left t).smul_right _), ← add_smul]
    simp
  calc X t = exp (t • a) * exp ((0 - t) • a) * X t := by rw [hinv, one_mul]
    _ = exp (t • a) := by rw [mul_assoc, hconst, mul_one]

/-! ### The Fréchet derivative and the condition number -/

/-- For fixed $a$, $t$ and $s$, the continuous linear map $e \mapsto \exp((t - s)a)\, e\, \exp(sa)$,
which is the integrand of the Fréchet derivative. -/
private noncomputable def frechetIntegrand (a : 𝔸) (t s : ℝ) : 𝔸 →L[ℝ] 𝔸 :=
  (ContinuousLinearMap.mul ℝ 𝔸 (exp ((t - s) • a))).comp
    ((ContinuousLinearMap.mul ℝ 𝔸).flip (exp (s • a)))

private theorem continuous_frechetIntegrand (a : 𝔸) (t : ℝ) :
    Continuous (frechetIntegrand a t) :=
  ((ContinuousLinearMap.mul ℝ 𝔸).continuous.comp
    (continuous_exp_smul (continuous_const.sub continuous_id) a)).clm_comp
    ((ContinuousLinearMap.mul ℝ 𝔸).flip.continuous.comp (continuous_exp_smul continuous_id a))

/-- The **Fréchet derivative of the exponential** $a \mapsto \exp(ta)$. For $a$ in a complete normed
$\mathbb{R}$-algebra $\mathbb{A}$ and $t \in \mathbb{R}$, $L(a, t)$ is the continuous linear map
on $\mathbb{A}$ given by
$$L(a, t)\, e = \int_0^t \exp((t - s)a)\, e\, \exp(sa)\, ds.$$
It is the first-order term in $e$ of the variation-of-constants identity ([golub2013matrix],
§9.3.2), and it is (10.15) of Higham, *Functions of Matrices*.

The definition is the interval integral of the operator-valued map $s \mapsto (e \mapsto
\exp((t - s)a)\, e\, \exp(sa))$. `NormedSpace.expFrechet_apply` evaluates it at a direction, and
`NormedSpace.hasFDerivAt_exp_smul` proves that it is the Fréchet derivative. -/
noncomputable def expFrechet (a : 𝔸) (t : ℝ) : 𝔸 →L[ℝ] 𝔸 :=
  ∫ s in (0 : ℝ)..t, frechetIntegrand a t s

/-- The value of the Fréchet derivative $L(a, t)$ at a direction $e$ is
$\int_0^t \exp((t - s)a)\, e\, \exp(sa)\, ds$. -/
theorem expFrechet_apply (a : 𝔸) (t : ℝ) (e : 𝔸) :
    expFrechet a t e = ∫ s in (0 : ℝ)..t, exp ((t - s) • a) * e * exp (s • a) := by
  rw [expFrechet, ContinuousLinearMap.intervalIntegral_apply
    ((continuous_frechetIntegrand a t).intervalIntegrable _ _)]
  simp [frechetIntegrand, mul_assoc]

/-- The Fréchet derivative in the direction $1$ is $L(a, t)\, 1 = t \exp(ta)$. -/
theorem expFrechet_one (a : 𝔸) (t : ℝ) : expFrechet a t 1 = t • exp (t • a) := by
  rw [expFrechet_apply]
  have h : ∀ s : ℝ, exp ((t - s) • a) * exp (s • a) = exp (t • a) := fun s => by
    rw [← exp_add_of_commute_real (((Commute.refl a).smul_left _).smul_right _), ← add_smul,
      sub_add_cancel]
  simp [h]

/-- Let $\mathbb{A}$ be a complete normed $\mathbb{R}$-algebra, let $a, e \in \mathbb{A}$ commute,
and let $t \in \mathbb{R}$. Then the Fréchet derivative of the exponential in the direction $e$
is
$$L(a, t)\, e = t \exp(ta)\, e.$$
-/
theorem expFrechet_apply_of_commute {a e : 𝔸} (h : Commute a e) (t : ℝ) :
    expFrechet a t e = t • (exp (t • a) * e) := by
  rw [expFrechet_apply]
  have hc : ∀ s : ℝ, exp ((t - s) • a) * e * exp (s • a) = exp (t • a) * e := fun s => by
    rw [mul_assoc, ((h.smul_left s).exp_left).eq.symm, ← mul_assoc,
      ← exp_add_of_commute_real (((Commute.refl a).smul_left _).smul_right _), ← add_smul,
      sub_add_cancel]
  simp [hc]

/-- **$L(a, t)$ is the Fréchet derivative of the exponential.** Let $\mathbb{A}$ be a complete
normed $\mathbb{R}$-algebra, let $a \in \mathbb{A}$ and let $t \in \mathbb{R}$. Then the map
$b \mapsto \exp(tb)$ has the Fréchet derivative $L(a, t)$ (`NormedSpace.expFrechet`) at $a$.

The exponential is analytic, hence differentiable. Its derivative in a direction $e$ is computed
from the variation-of-constants identity $\exp(t(a + \varepsilon e)) - \exp(ta) = \varepsilon
\int_0^t \exp((t - s)a)\, e\, \exp(s(a + \varepsilon e))\, ds$, whose integral is continuous in
$\varepsilon$. -/
theorem hasFDerivAt_exp_smul (a : 𝔸) (t : ℝ) :
    HasFDerivAt (fun b : 𝔸 => exp (t • b)) (expFrechet a t) a := by
  have hdiff : DifferentiableAt ℝ (fun b : 𝔸 => exp (t • b)) a :=
    (exp_analytic (𝕂 := ℝ) (t • a)).differentiableAt.comp a
      ((differentiableAt_id).const_smul t)
  convert hdiff.hasFDerivAt using 1
  ext e
  -- the derivative along the line `ε ↦ a + ε • e`
  have hline : HasDerivAt (fun ε : ℝ => exp (t • (a + ε • e)))
      (fderiv ℝ (fun b : 𝔸 => exp (t • b)) a e) 0 := by
    have hg : HasDerivAt (fun ε : ℝ => a + ε • e) e 0 := by
      simpa using HasDerivAt.const_add a (HasDerivAt.smul_const (hasDerivAt_id (0 : ℝ)) e)
    have hf' : HasFDerivAt (fun b : 𝔸 => exp (t • b)) (fderiv ℝ (fun b : 𝔸 => exp (t • b)) a)
        (a + (0 : ℝ) • e) := by
      rw [zero_smul, add_zero]
      exact hdiff.hasFDerivAt
    simpa [Function.comp_def] using hf'.comp_hasDerivAt (0 : ℝ) hg
  -- the same derivative from the variation-of-constants identity
  set I : ℝ → 𝔸 := fun ε => ∫ s in (0 : ℝ)..t, exp ((t - s) • a) * e * exp (s • (a + ε • e))
  have hIcont : Continuous I := by
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun ε s => exp ((t - s) • a) * e * exp (s • (a + ε • e))) ?_ 0 t
    have h1 : Continuous fun p : ℝ × ℝ => p.2 • (a + p.1 • e) := by fun_prop
    exact ((continuous_exp_smul (continuous_const.sub continuous_snd) a).mul
      continuous_const).mul (continuous_exp_real.comp h1)
  have hI : HasDerivAt (fun ε : ℝ => exp (t • (a + ε • e))) (I 0) 0 := by
    rw [hasDerivAt_iff_tendsto_slope]
    refine (hIcont.tendsto 0).mono_left nhdsWithin_le_nhds |>.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : ε ≠ 0 := hε
    rw [slope_def_module, zero_smul, add_zero, sub_zero, exp_smul_add_sub_exp_smul]
    simp only [smul_mul_assoc, mul_smul_comm, intervalIntegral.integral_smul]
    rw [smul_smul, inv_mul_cancel₀ hε', one_smul]
  rw [hline.unique hI, expFrechet_apply]
  simp [I]

/-- **Van Loan's condition number of the exponential** ([golub2013matrix], §9.3.2). For $a$ in a
complete normed $\mathbb{R}$-algebra and $t \in \mathbb{R}$,
$$\nu(a, t) = \frac{\|L(a, t)\| \, \|a\|}{\|\exp(ta)\|},$$
where $L(a, t)$ is the Fréchet derivative `NormedSpace.expFrechet` of $b \mapsto \exp(tb)$ at
$a$, and $\|L(a, t)\|$ is its operator norm.

The source writes $\|L(a, t)\|$ as $\max_{\|E\| \le 1} \|\int_0^t e^{A(t - s)} E e^{As}\, ds\|$,
which is this operator norm. The division is the division of real numbers in Lean, so
$\nu(a, t) = 0$ if $\exp(ta) = 0$; this happens only in the zero algebra, because $\exp(ta)$ is
invertible. -/
noncomputable def expCondNumber (a : 𝔸) (t : ℝ) : ℝ :=
  ‖expFrechet a t‖ * ‖a‖ / ‖exp (t • a)‖

variable [NormOneClass 𝔸]

/-- Let $\mathbb{A}$ be a complete normed $\mathbb{R}$-algebra with $\|1\| = 1$, let
$a \in \mathbb{A}$ and let $t \ge 0$. Then
$$t \|a\| \le \nu(a, t).$$
This is the lower bound of [golub2013matrix], §9.3.2.

The proof evaluates $L(a, t)$ in the direction $1$, where it is $t \exp(ta)$
(`NormedSpace.expFrechet_one`). -/
theorem mul_norm_le_expCondNumber (a : 𝔸) {t : ℝ} (ht : 0 ≤ t) : t * ‖a‖ ≤ expCondNumber a t := by
  have : Nontrivial 𝔸 := NormOneClass.nontrivial
  have hunit : IsUnit (exp (t • a)) := by
    refine ⟨⟨exp (t • a), exp (-(t • a)), ?_, ?_⟩, rfl⟩
    · rw [← exp_add_of_commute_real ((Commute.refl _).neg_right), add_neg_cancel, exp_zero]
    · rw [← exp_add_of_commute_real ((Commute.refl _).neg_left), neg_add_cancel, exp_zero]
  have hpos : 0 < ‖exp (t • a)‖ := norm_pos_iff.mpr hunit.ne_zero
  have hL : t * ‖exp (t • a)‖ ≤ ‖expFrechet a t‖ := by
    have := (expFrechet a t).le_opNorm 1
    rwa [expFrechet_one, norm_one, mul_one, norm_smul, Real.norm_of_nonneg ht] at this
  rw [expCondNumber, le_div_iff₀ hpos]
  calc t * ‖a‖ * ‖exp (t • a)‖ = t * ‖exp (t • a)‖ * ‖a‖ := by ring
    _ ≤ ‖expFrechet a t‖ * ‖a‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg _)

/-- **The equality case of Van Loan's condition number.** Let $\mathbb{A}$ be a complete normed
$\mathbb{R}$-algebra with $\|1\| = 1$, let $a \in \mathbb{A}$, $t \ge 0$ and $c \in \mathbb{R}$.
If $\|\exp(sa)\| = e^{cs}$ for all $s \in [0, t]$, then $\nu(a, t) = t \|a\|$.

Normal matrices satisfy the hypothesis in the spectral norm with $c$ the spectral abscissa
([golub2013matrix], (9.3.4)). The non-normal matrix $[1] \oplus \begin{bmatrix} 0 & 1 \\ 0 & 0
\end{bmatrix}$ satisfies it too, with $c = 1$. So the claim of [golub2013matrix], §9.3.2, that
$\nu(A, t) = t \|A\|_2$ holds if and only if $A$ is normal, is false in the direction "only if". -/
theorem expCondNumber_eq_of_norm_exp_smul_eq (a : 𝔸) {t c : ℝ} (ht : 0 ≤ t)
    (h : ∀ s ∈ Set.Icc 0 t, ‖exp (s • a)‖ = Real.exp (c * s)) :
    expCondNumber a t = t * ‖a‖ := by
  refine le_antisymm ?_ (mul_norm_le_expCondNumber a ht)
  have hpos : 0 < ‖exp (t • a)‖ := by
    rw [h t ⟨ht, le_rfl⟩]
    exact Real.exp_pos _
  have hL : ‖expFrechet a t‖ ≤ t * ‖exp (t • a)‖ := by
    refine (expFrechet a t).opNorm_le_bound (by positivity) fun e => ?_
    rw [expFrechet_apply]
    have hbound : ∀ s ∈ Set.Icc (0 : ℝ) t,
        ‖exp ((t - s) • a) * e * exp (s • a)‖ ≤ ‖exp (t • a)‖ * ‖e‖ := by
      intro s hs
      have h1 := h (t - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
      have h2 := h s hs
      calc ‖exp ((t - s) • a) * e * exp (s • a)‖
          ≤ ‖exp ((t - s) • a)‖ * ‖e‖ * ‖exp (s • a)‖ :=
            (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ = ‖exp (t • a)‖ * ‖e‖ := by
            rw [h1, h2, h t ⟨ht, le_rfl⟩, mul_right_comm, ← Real.exp_add]
            ring_nf
    calc ‖∫ s in (0 : ℝ)..t, exp ((t - s) • a) * e * exp (s • a)‖
        ≤ ‖exp (t • a)‖ * ‖e‖ * |t - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const fun s hs =>
            hbound s ⟨(Set.uIoc_of_le ht ▸ hs).1.le, (Set.uIoc_of_le ht ▸ hs).2⟩
      _ = t * ‖exp (t • a)‖ * ‖e‖ := by rw [sub_zero, abs_of_nonneg ht]; ring
  rw [expCondNumber, div_le_iff₀ hpos]
  calc ‖expFrechet a t‖ * ‖a‖ ≤ t * ‖exp (t • a)‖ * ‖a‖ :=
        mul_le_mul_of_nonneg_right hL (norm_nonneg _)
    _ = t * ‖a‖ * ‖exp (t • a)‖ := by ring

end NormedSpace

open NormedSpace

/-! ### The resolvent as a Laplace transform -/

section Resolvent

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

/-- **The resolvent bound from the Laplace transform.** Let $\mathbb{A}$ be a complete normed
$\mathbb{C}$-algebra, let $a \in \mathbb{A}$, and let $M \in \mathbb{R}$ satisfy
$\|\exp(ta)\| \le M$ for all real $t \ge 0$. If $z \in \mathbb{C}$ has
$\operatorname{Re} z > 0$, then $z$ is not in the spectrum of $a$, and
$$\|(z - a)^{-1}\| \le \frac{M}{\operatorname{Re} z}.$$
This is the bound behind [golub2013matrix], (9.3.6).

The inverse is the Laplace transform $\int_0^\infty e^{-zt} \exp(ta)\, dt$. In the statement it
is `Ring.inverse`, which is the true inverse because $z - a$ is a unit. -/
theorem norm_resolvent_le_of_norm_exp_smul_le {a : 𝔸} {M : ℝ}
    (hM : ∀ t : ℝ, 0 ≤ t → ‖exp (t • a)‖ ≤ M) {z : ℂ} (hz : 0 < z.re) :
    z ∉ spectrum ℂ a ∧ ‖Ring.inverse (algebraMap ℂ 𝔸 z - a)‖ ≤ M / z.re := by
  set w := algebraMap ℂ 𝔸 z - a
  set E : ℝ → 𝔸 := fun t => Complex.exp (-(z * t)) • exp (t • a)
  have hcomm : ∀ t : ℝ, Commute (E t) w := fun t => by
    have h1 : Commute (exp (t • a)) a := ((Commute.refl a).smul_right t).exp_right.symm
    exact ((Algebra.commute_algebraMap_right z _).sub_right h1).smul_left _
  have hcont : Continuous E :=
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal).neg).smul
      (continuous_exp_smul continuous_id a)
  have hnormE : ∀ t : ℝ, 0 ≤ t → ‖E t‖ ≤ M * Real.exp (-z.re * t) := fun t ht => by
    simp only [E, norm_smul, Complex.norm_exp, Complex.neg_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [mul_comm, neg_mul]
    exact mul_le_mul_of_nonneg_right (hM t ht) (Real.exp_pos _).le
  have hgint : IntegrableOn (fun t : ℝ => M * Real.exp (-z.re * t)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos hz) 0).const_mul M
  have hEint : IntegrableOn E (Set.Ioi 0) :=
    hgint.mono' hcont.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht =>
        hnormE t (le_of_lt ht)))
  have hderiv : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivAt (fun t => -E t) (E t * w) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => Complex.exp (-(z * t)))
        (Complex.exp (-(z * t)) * -(z * 1)) t :=
      ((hasDerivAt_id t).ofReal_comp.const_mul z).neg.cexp
    have h2 := h1.smul (hasDerivAt_exp_smul_const' (𝕂 := ℝ) a t)
    have h3 : Commute a (exp (t • a)) := ((Commute.refl a).smul_right t).exp_right
    convert h2.neg using 1
    simp only [E, w, mul_sub, smul_mul_assoc, h3.eq]
    rw [← Algebra.commutes z (exp (t • a)), ← Algebra.smul_def]
    module
  have hlim : Filter.Tendsto (fun t => -E t) Filter.atTop (nhds 0) := by
    rw [← neg_zero]
    refine Filter.Tendsto.neg (squeeze_zero_norm' (a := fun t => M * Real.exp (-z.re * t)) ?_ ?_)
    · exact Filter.eventually_atTop.mpr ⟨0, fun t ht => hnormE t ht⟩
    · have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (Filter.tendsto_id.const_mul_atTop hz)).const_mul M
      simpa [Function.comp_def, neg_mul] using this
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (hEint.mul_const w) hlim
  have hE0 : E 0 = 1 := by simp [E]
  rw [hE0, zero_sub, neg_neg, integral_mul_const_of_integrable hEint] at hFTC
  set R := ∫ t in Set.Ioi (0 : ℝ), E t
  have hRw : w * R = 1 := by
    rw [← hFTC, ← integral_const_mul_of_integrable hEint,
      ← integral_mul_const_of_integrable hEint]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => (hcomm t).eq.symm)
  have hu : IsUnit w := ⟨⟨w, R, hRw, hFTC⟩, rfl⟩
  refine ⟨fun h => (spectrum.mem_iff.mp h) hu, ?_⟩
  rw [show Ring.inverse w = R from by
    rw [Ring.inverse_unit ⟨w, R, hRw, hFTC⟩]
    rfl]
  have hint : ∫ t in Set.Ioi (0 : ℝ), M * Real.exp (-z.re * t) = M / z.re := by
    rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hz)]
    field_simp
    simp
  rw [← hint]
  exact norm_integral_le_of_norm_le hgint
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht =>
      hnormE t (le_of_lt ht)))

end Resolvent
