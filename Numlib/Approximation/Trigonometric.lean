/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.NumberTheory.Harmonic.Bounds
import Numlib.Analysis.Fourier.Dirichlet
import Numlib.Analysis.Fourier.TrigonometricBasis
import Numlib.Analysis.Normed.Module.BestApprox
import Numlib.IntegralEquations.Basic

/-!
# Trigonometric approximation of continuous periodic functions

This file studies the Fourier projection on the space $C_p(2\pi)$ of continuous $2\pi$-periodic real
functions, following §3.7 of [han2009theoretical]. Let $D_n(t) = 1/2 + \sum_{j=1}^n \cos(jt)$ be the
Dirichlet kernel, and let $\mathcal{T}_n$ be the space of trigonometric polynomials of degree at
most $n$. The $n$-th **Fourier projection** is the integral operator
$$\mathcal{F}_n f(x) = \frac{1}{\pi} \int_{-\pi}^{\pi} D_n(y - x) f(y)\, dy.$$
It is the $n$-th partial sum of the Fourier series of $f$, and it is a bounded projection of
$C_p(2\pi)$ onto $\mathcal{T}_n$.

The operator norm of $\mathcal{F}_n$ is the **Lebesgue constant** $L_n = \frac{1}{\pi}
\int_{-\pi}^{\pi} |D_n(t)|\, dt$. The file proves $(4/\pi^2) \log n \le L_n \le 1 + \log(2n + 1)$,
so that $L_n$ is unbounded, and the Lebesgue lemma $\|f - \mathcal{F}_n f\|_\infty \le (1 + L_n)
\operatorname{dist}(f, \mathcal{T}_n)$.

## Main definitions

* `PeriodicCont.dirichletCM`: the Dirichlet kernel $D_n$ as a continuous function on the circle.
* `PeriodicCont.fourierKernel`: the kernel $(x, y) \mapsto D_n(y - x) / \pi$ of the Fourier
  projection.
* `PeriodicCont.fourierProj`: the Fourier projection $\mathcal{F}_n$.
* `PeriodicCont.lebesgueConstant`: the Lebesgue constant $L_n$.

## Main results

* `PeriodicCont.fourierProj_coe`: $\mathcal{F}_n f$ is the $n$-th partial sum of the Fourier series
  of $f$.
* `PeriodicCont.fourierKernel_eq_sum`: $D_n(y - x) / \pi = (2\pi)^{-1} \sum_{|m| \le n} e_m(x)
  e_m(y)$ for the real trigonometric system $(e_m)$.
* `PeriodicCont.range_fourierProj`, `PeriodicCont.isIdempotentElem_fourierProj`: $\mathcal{F}_n$ is
  a projection with range $\mathcal{T}_n$.
* `PeriodicCont.norm_fourierProj`: $\|\mathcal{F}_n\| = L_n$.
* `PeriodicCont.norm_sub_fourierProj_le`: $\|f - \mathcal{F}_n f\|_\infty \le (1 + L_n)
  \operatorname{dist}(f, \mathcal{T}_n)$.
* `PeriodicCont.log_le_lebesgueConstant`: $(4/\pi^2) \log n \le L_n$.
* `PeriodicCont.lebesgueConstant_le`: $L_n \le 1 + \log(2n + 1)$.

## Proof outline

The kernel has two forms. As a function of $y - x$ built from $D_n$, it gives the partial-sum form
of $\mathcal{F}_n$ and its norm: the norm of an integral operator on a compact space is the largest
integral of $|k(x, \cdot)|$, and here this integral does not depend on $x$. As the sum
$(2\pi)^{-1} \sum_{|m| \le n} e_m(x) e_m(y)$, it gives the range and the idempotency from the
orthonormality of the system $(e_m)$. The lower bound on $L_n$ compares the integral of $|D_n|$ over
each arch of $\sin((n + 1/2) t)$ with a term of the harmonic series. The upper bound splits
$[0, \pi]$ at $\pi / (2n + 1)$: below this point $|D_n| \le n + 1/2$, and above it
$|D_n(t)| \le \pi / (2t)$ by Jordan's inequality.

## Notation

* $e_m$, for $m \in \mathbb{Z}$: the real trigonometric system `trigFun (2 * π) m`, with $e_0 = 1$,
  $e_m(x) = \sqrt{2} \cos(mx)$ for $m > 0$, and $e_m(x) = \sqrt{2} \sin(|m| x)$ for $m < 0$.
* $\mathcal{T}_n$: the span `trigPolyLE (2 * π) n` of the $e_m$ with $|m| \le n$.

## Implementation notes

* The space $C_p(2\pi)$ is `C(AddCircle (2 * π), ℝ)` with the supremum norm, and integrals over the
  circle are for its Haar measure `volume`, of total mass $2\pi$.
* The Dirichlet kernel `dirichletKernel` and the partial sums `fourierPartialSum` come from
  `Numlib.Analysis.Fourier.Dirichlet`. This file adds that the partial sum of a continuous periodic
  function is continuous, that the partial-sum map is bounded, and that it is the projection onto
  `trigPolyLE (2 * π) n` of `Numlib.Analysis.Fourier.TrigonometricBasis`.
* The norm identity specializes `IntegralOperator.norm_kernelCLM`, which holds for a kernel operator
  on any compact space, so that it covers the circle as well as an interval.
* The orthonormality of the real trigonometric system is `realFourierCoeff_trigFun`.
* Of the asymptotic formula $L_n = (4/\pi^2) \log n + O(1)$ of Zygmund in (3.7.10) of
  [han2009theoretical], the file proves the lower bound with the sharp constant $4/\pi^2$ and the
  upper bound $1 + \log(2n + 1)$ with a constant that is not sharp. These two bounds are what the
  divergence argument and the convergence rate (3.7.12) use.
* Of the estimate (3.7.11) of [han2009theoretical], the file proves the Lebesgue lemma $\|f -
  \mathcal{F}_n f\|_\infty \le (1 + L_n) \operatorname{dist}(f, \mathcal{T}_n)$, which is the part
  that the projection gives. The rate then follows from Jackson's theorem.
* Jackson's theorem (Theorem 3.7.1 of [han2009theoretical]) bounds the best uniform trigonometric
  approximation of a Hölder continuous function by $M_k / n^{k + \alpha}$. It is in
  `Numlib.Approximation.Jackson`, because it does not use the Fourier projection, only the subspace
  $\mathcal{T}_n$.
-/

open MeasureTheory Metric Set

open scoped Real

namespace PeriodicCont

/-! ### The Dirichlet kernel on the circle -/

/-- A sum of $g(m)$ over the integers $m$ with $|m| \le n$ is $g(0) + \sum_{j=1}^n (g(j) + g(-j))$.
-/
private theorem sum_Icc_neg_eq {M : Type*} [AddCommMonoid M] (g : ℤ → M) (n : ℕ) :
    ∑ m ∈ Finset.Icc (-(n : ℤ)) n, g m = g 0 + ∑ j ∈ Finset.Icc 1 n, (g j + g (-j)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : Finset.Icc (-((n : ℤ) + 1)) ((n : ℤ) + 1)
        = insert ((n : ℤ) + 1) (insert (-((n : ℤ) + 1)) (Finset.Icc (-(n : ℤ)) (n : ℤ))) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have h2 : ((n : ℤ) + 1) ∉ insert (-((n : ℤ) + 1)) (Finset.Icc (-(n : ℤ)) (n : ℤ)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have h3 : (-((n : ℤ) + 1)) ∉ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
      simp only [Finset.mem_Icc]; omega
    push_cast
    rw [h1, Finset.sum_insert h2, Finset.sum_insert h3, ih,
      Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le n))]
    push_cast
    abel

/-- The **Dirichlet kernel on the circle**: the continuous function $\frac{1}{2} + \sum_{j=1}^n
\frac{1}{\sqrt{2}} e_j$ on the circle of circumference $2\pi$, where
$e_j(x) = \sqrt{2} \cos(jx)$. Its value at $t$ is $D_n(t) = \frac{1}{2} + \sum_{j=1}^n \cos(jt)$
(`PeriodicCont.dirichletCM_coe`). -/
noncomputable def dirichletCM (n : ℕ) : C(AddCircle (2 * π), ℝ) :=
  (2 : ℝ)⁻¹ • (1 : C(AddCircle (2 * π), ℝ))
    + ∑ j ∈ Finset.Icc 1 n, ((√2)⁻¹ : ℝ) • trigFun (2 * π) (j : ℤ)

/-- For every real $t$, the function `PeriodicCont.dirichletCM n` at the point $t$ of the circle is
the Dirichlet kernel $D_n(t)$ of `Numlib.Analysis.Fourier.Dirichlet`. -/
@[simp]
theorem dirichletCM_coe (n : ℕ) (t : ℝ) : dirichletCM n ↑t = dirichletKernel n t := by
  have h2 : (√2 : ℝ) ≠ 0 := by positivity
  simp only [dirichletCM, ContinuousMap.add_apply, ContinuousMap.smul_apply,
    ContinuousMap.one_apply, ContinuousMap.coe_sum, Finset.sum_apply, smul_eq_mul,
    dirichletKernel_apply]
  congr 1
  · norm_num
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj0 : (0 : ℤ) < (j : ℤ) := by
    have := (Finset.mem_Icc.1 hj).1; omega
  rw [trigFun_coe_of_pos hj0, ← mul_assoc, inv_mul_cancel₀ h2, one_mul]
  push_cast
  ring_nf

/-! ### The Fourier projection -/

/-- The **kernel of the Fourier projection**: the continuous function
$(x, y) \mapsto D_n(y - x) / \pi$ on the product of two circles of circumference $2\pi$.

This is the kernel of (3.7.6) of [han2009theoretical]. -/
noncomputable def fourierKernel (n : ℕ) : C(AddCircle (2 * π) × AddCircle (2 * π), ℝ) :=
  (π⁻¹ : ℝ) • (dirichletCM n).comp ⟨fun p => p.2 - p.1, by fun_prop⟩

/-- The kernel of the Fourier projection at $(x, y)$ is $\pi^{-1} D_n(y - x)$. -/
@[simp]
theorem fourierKernel_apply (n : ℕ) (x y : AddCircle (2 * π)) :
    fourierKernel n (x, y) = π⁻¹ * dirichletCM n (y - x) :=
  rfl

/-- The **Fourier projection** $\mathcal{F}_n$ on the space of continuous $2\pi$-periodic functions:
the integral operator
$$\mathcal{F}_n f(x) = \frac{1}{\pi} \int f(y)\, D_n(y - x)\, dy,$$
where the integral is over the circle of circumference $2\pi$.

This is the operator of (3.7.6)–(3.7.8) of [han2009theoretical]. It is
`IntegralOperator.kernelCLM` for the kernel `PeriodicCont.fourierKernel n` and the Haar measure
`volume`. It is the partial-sum operator of the Fourier series (`PeriodicCont.fourierProj_coe`)
and the projection onto the trigonometric polynomials of degree at most $n$
(`PeriodicCont.range_fourierProj`, `PeriodicCont.isIdempotentElem_fourierProj`). -/
noncomputable def fourierProj (n : ℕ) :
    C(AddCircle (2 * π), ℝ) →L[ℝ] C(AddCircle (2 * π), ℝ) :=
  IntegralOperator.kernelCLM volume (fourierKernel n)

/-- For a continuous $2\pi$-periodic function $f$ and a point $x$ of the circle,
$\mathcal{F}_n f(x) = \int k_n(x, y) f(y)\, dy$, where $k_n$ is the kernel
`PeriodicCont.fourierKernel n`. -/
theorem fourierProj_apply (n : ℕ) (f : C(AddCircle (2 * π), ℝ)) (x : AddCircle (2 * π)) :
    fourierProj n f x = ∫ y, fourierKernel n (x, y) * f y :=
  rfl

/-- For a function $F$ on the circle of circumference $2\pi$ and a real number $s$, the integral of
$F$ over the circle equals $\int_{-\pi}^{\pi} F(s + r)\, dr$. -/
theorem integral_addCircle_eq (F : AddCircle (2 * π) → ℝ) (s : ℝ) :
    ∫ y : AddCircle (2 * π), F y = ∫ r in -π..π, F ↑(s + r) := by
  have h := AddCircle.intervalIntegral_preimage (2 * π) (s + -π) F
  rw [show s + -π + 2 * π = s + π by ring] at h
  rw [← h, ← intervalIntegral.integral_comp_add_left (fun t : ℝ => F ↑t) s]

/-- **The Fourier projection is the partial-sum operator of the Fourier series.** For a continuous
$2\pi$-periodic function $f$ and a real number $s$,
$$\mathcal{F}_n f(s) = \frac{a_0}{2} + \sum_{j=1}^n \bigl(a_j \cos(js) + b_j \sin(js)\bigr),$$
where $a_j$ and $b_j$ are the Fourier coefficients of $f$ regarded as a periodic function on
$\mathbb{R}$.

This is (3.7.6) of [han2009theoretical]. The right side is `fourierPartialSum` of
`Numlib.Analysis.Fourier.Dirichlet`. -/
theorem fourierProj_coe (n : ℕ) (f : C(AddCircle (2 * π), ℝ)) (s : ℝ) :
    fourierProj n f ↑s = fourierPartialSum (fun t : ℝ => f ↑t) n s := by
  have hcont : Continuous fun t : ℝ => f ↑t :=
    f.continuous.comp (AddCircle.continuous_mk' (2 * π))
  have hper : Function.Periodic (fun t : ℝ => f ↑t) (2 * π) := fun t => by
    simp only []
    rw [AddCircle.coe_add_period]
  rw [fourierPartialSum_eq_integral hper (hcont.intervalIntegrable _ _), fourierProj_apply,
    integral_addCircle_eq (fun y => fourierKernel n (↑s, y) * f y) s,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun r _ => ?_
  have hsub : ((↑(s + r) : AddCircle (2 * π)) - ↑s) = ((r : ℝ) : AddCircle (2 * π)) := by
    have h : ((↑(s + r) : AddCircle (2 * π))) = (↑s : AddCircle (2 * π)) + ↑r := rfl
    rw [h, add_sub_cancel_left]
  simp only [fourierKernel_apply, hsub, dirichletCM_coe]
  field_simp

/-! ### The range: the trigonometric polynomials of degree at most $n$ -/

/-- **The kernel of the Fourier projection is the reproducing kernel of the real trigonometric
system.** For points $x$ and $y$ of the circle,
$$\frac{1}{\pi} D_n(y - x) = \frac{1}{2\pi} \sum_{|m| \le n} e_m(x)\, e_m(y).$$

The range and the idempotency of $\mathcal{F}_n$ follow from this form of the kernel. -/
theorem fourierKernel_eq_sum (n : ℕ) (x y : AddCircle (2 * π)) :
    fourierKernel n (x, y)
      = (2 * π)⁻¹ * ∑ m ∈ Finset.Icc (-(n : ℤ)) n, trigFun (2 * π) m x * trigFun (2 * π) m y := by
  have h2 : (√2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  induction x using QuotientAddGroup.induction_on with
  | _ u =>
    induction y using QuotientAddGroup.induction_on with
    | _ v =>
      have hsub : ((↑v : AddCircle (2 * π)) - ↑u) = ((v - u : ℝ) : AddCircle (2 * π)) := rfl
      rw [fourierKernel_apply, hsub, dirichletCM_coe, dirichletKernel_apply,
        sum_Icc_neg_eq (fun m => trigFun (2 * π) m ↑u * trigFun (2 * π) m ↑v) n, trigFun_zero]
      have hterm : ∀ j ∈ Finset.Icc 1 n,
          trigFun (2 * π) (j : ℤ) ↑u * trigFun (2 * π) (j : ℤ) ↑v
            + trigFun (2 * π) (-(j : ℤ)) ↑u * trigFun (2 * π) (-(j : ℤ)) ↑v
            = 2 * Real.cos (j * (v - u)) := by
        intro j hj
        have hj0 : (0 : ℤ) < (j : ℤ) := by have := (Finset.mem_Icc.1 hj).1; omega
        have hcos : Real.cos ((j : ℝ) * (v - u))
            = Real.cos ((j : ℝ) * v) * Real.cos ((j : ℝ) * u)
              + Real.sin ((j : ℝ) * v) * Real.sin ((j : ℝ) * u) := by
          rw [show (j : ℝ) * (v - u) = (j : ℝ) * v - (j : ℝ) * u by ring, Real.cos_sub]
        rw [trigFun_coe_of_pos hj0, trigFun_coe_of_pos hj0,
          trigFun_coe_of_neg (by omega : (-(j : ℤ)) < 0),
          trigFun_coe_of_neg (by omega : (-(j : ℤ)) < 0), hcos]
        push_cast
        simp only [neg_neg]
        linear_combination (Real.cos ((j : ℝ) * u) * Real.cos ((j : ℝ) * v)
          + Real.sin ((j : ℝ) * u) * Real.sin ((j : ℝ) * v)) * h2
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      simp only [ContinuousMap.one_apply, one_mul, mul_inv]
      ring

/-- The Fourier projection in the real trigonometric system: for a continuous $2\pi$-periodic
function $f$,
$$\mathcal{F}_n f = \sum_{|m| \le n} c_m(f)\, e_m,$$
where $c_m(f)$ is the integral of $e_m f$ for the normalized Haar measure on the circle
(`realFourierCoeff`). This is the series (4.1.1) of [han2009theoretical]. -/
theorem fourierProj_eq_sum (n : ℕ) (f : C(AddCircle (2 * π), ℝ)) :
    fourierProj n f
      = ∑ m ∈ Finset.Icc (-(n : ℤ)) n,
          realFourierCoeff (f : AddCircle (2 * π) → ℝ) m • trigFun (2 * π) m := by
  ext x
  have hcoe : ∀ m : ℤ, realFourierCoeff (f : AddCircle (2 * π) → ℝ) m
      = (2 * π)⁻¹ * ∫ y : AddCircle (2 * π), trigFun (2 * π) m y * f y := by
    intro m
    rw [realFourierCoeff_apply, AddCircle.integral_haarAddCircle, smul_eq_mul]
  have hint : ∀ m : ℤ, Integrable
      (fun y : AddCircle (2 * π) =>
        (2 * π)⁻¹ * trigFun (2 * π) m x * (trigFun (2 * π) m y * f y)) volume := fun m =>
    IntegralOperator.integrable_of_continuousMap volume
      ⟨_, continuous_const.mul ((trigFun (2 * π) m).continuous.mul f.continuous)⟩
  rw [fourierProj_apply, ContinuousMap.coe_sum, Finset.sum_apply]
  have hrw : ∀ y : AddCircle (2 * π), fourierKernel n (x, y) * f y
      = ∑ m ∈ Finset.Icc (-(n : ℤ)) n,
          (2 * π)⁻¹ * trigFun (2 * π) m x * (trigFun (2 * π) m y * f y) := by
    intro y
    rw [fourierKernel_eq_sum, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hrw),
    integral_finsetSum _ fun m _ => hint m]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_const_mul, ContinuousMap.smul_apply, smul_eq_mul, hcoe m]
  ring

/-- For every continuous $2\pi$-periodic function $f$, the function $\mathcal{F}_n f$ is a
trigonometric polynomial of degree at most $n$. -/
theorem fourierProj_mem (n : ℕ) (f : C(AddCircle (2 * π), ℝ)) :
    fourierProj n f ∈ trigPolyLE (2 * π) n :=
  mem_trigPolyLE_iff.2 ⟨fun m => realFourierCoeff (f : AddCircle (2 * π) → ℝ) m,
    fourierProj_eq_sum n f⟩

/-- For an integer $m$ with $|m| \le n$, the Fourier projection fixes $e_m$:
$\mathcal{F}_n e_m = e_m$. -/
theorem fourierProj_trigFun {n : ℕ} {m : ℤ} (hm : m.natAbs ≤ n) :
    fourierProj n (trigFun (2 * π) m) = trigFun (2 * π) m := by
  rw [fourierProj_eq_sum]
  rw [Finset.sum_eq_single m (fun j _ hj => by
      rw [realFourierCoeff_trigFun, ite_eq_right (Ne.symm hj), zero_smul]) fun hm' => ?_]
  · simp
  · exact absurd (Finset.mem_Icc.2 (Set.mem_Icc.1 (mem_Icc_iff_natAbs_le.2 hm))) hm'

/-- **The Fourier projection fixes the trigonometric polynomials of degree at most $n$.** If
$f \in \mathcal{T}_n$, then $\mathcal{F}_n f = f$.

The partial sums `fourierPartialSum` of `Numlib.Analysis.Fourier.Dirichlet` do not record this
fact. It is the step that the idempotency needs. -/
theorem fourierProj_eq_self {n : ℕ} {f : C(AddCircle (2 * π), ℝ)}
    (hf : f ∈ trigPolyLE (2 * π) n) : fourierProj n f = f := by
  obtain ⟨c, rfl⟩ := mem_trigPolyLE_iff.1 hf
  rw [map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [map_smul, fourierProj_trigFun
    (mem_Icc_iff_natAbs_le.1 (Set.mem_Icc.2 (Finset.mem_Icc.1 hm)))]

/-- **The Fourier projection is a projection**: $\mathcal{F}_n \circ \mathcal{F}_n = \mathcal{F}_n$.
-/
theorem isIdempotentElem_fourierProj (n : ℕ) : IsIdempotentElem (fourierProj n) := by
  ext f x
  exact congrFun (congrArg _ (fourierProj_eq_self (fourierProj_mem n f))) x

/-- **The range of the Fourier projection** $\mathcal{F}_n$ is the space $\mathcal{T}_n$ of
trigonometric polynomials of degree at most $n$. -/
theorem range_fourierProj (n : ℕ) :
    LinearMap.range ((fourierProj n : C(AddCircle (2 * π), ℝ) →L[ℝ] C(AddCircle (2 * π), ℝ)) :
        C(AddCircle (2 * π), ℝ) →ₗ[ℝ] C(AddCircle (2 * π), ℝ))
      = trigPolyLE (2 * π) n := by
  refine le_antisymm ?_ fun f hf => ⟨f, fourierProj_eq_self hf⟩
  rintro _ ⟨f, rfl⟩
  exact fourierProj_mem n f

/-! ### The Lebesgue constants -/

/-- The $n$-th **Lebesgue constant**
$$L_n = \frac{1}{\pi} \int_{-\pi}^{\pi} |D_n(\theta)|\, d\theta.$$

This is (3.7.9) of [han2009theoretical]. It is the operator norm of $\mathcal{F}_n$
(`PeriodicCont.norm_fourierProj`). -/
noncomputable def lebesgueConstant (n : ℕ) : ℝ :=
  (1 / π) * ∫ t in -π..π, |dirichletKernel n t|

/-- **The operator norm of the Fourier projection is the Lebesgue constant**:
$\|\mathcal{F}_n\| = L_n$, for the supremum norm on the continuous $2\pi$-periodic functions.

This is (3.7.9) of [han2009theoretical]. The proof specializes
`IntegralOperator.norm_kernelCLM`: the norm of a kernel operator on a compact space is the
supremum over $x$ of $\int |k(x, y)|\, dy$. Here this integral does not depend on $x$, because
the kernel is a function of $y - x$. -/
theorem norm_fourierProj (n : ℕ) : ‖fourierProj n‖ = lebesgueConstant n := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hconst : ∀ x : AddCircle (2 * π),
      (∫ y : AddCircle (2 * π), |fourierKernel n (x, y)|) = lebesgueConstant n := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | _ s =>
      rw [integral_addCircle_eq (fun y => |fourierKernel n (↑s, y)|) s, lebesgueConstant,
        ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun r _ => ?_
      have hsub : ((↑(s + r) : AddCircle (2 * π)) - ↑s) = ((r : ℝ) : AddCircle (2 * π)) := by
        have h : ((↑(s + r) : AddCircle (2 * π))) = (↑s : AddCircle (2 * π)) + ↑r := rfl
        rw [h, add_sub_cancel_left]
      simp only [fourierKernel_apply, hsub, dirichletCM_coe, abs_mul,
        abs_of_pos (inv_pos.2 hπ)]
      rw [one_div]
  rw [fourierProj, IntegralOperator.norm_kernelCLM]
  simp only [hconst]
  exact ciSup_const

/-- **The Lebesgue lemma for the Fourier projection.** For every continuous $2\pi$-periodic function
$f$,
$$\|f - \mathcal{F}_n f\|_\infty \le (1 + L_n) \operatorname{dist}(f, \mathcal{T}_n).$$

This is the estimate of (3.7.11) of [han2009theoretical] that the projection gives. With a bound
on the best approximation $\operatorname{dist}(f, \mathcal{T}_n)$, such as Jackson's theorem in
`Numlib.Approximation.Jackson`, and with the growth of $L_n$, it gives the uniform convergence
rate (3.7.12). The distance is `Metric.infDist` to the subspace `trigPolyLE (2 * π) n`. -/
theorem norm_sub_fourierProj_le (n : ℕ) (f : C(AddCircle (2 * π), ℝ)) :
    ‖f - fourierProj n f‖
      ≤ (1 + lebesgueConstant n) * infDist f (trigPolyLE (2 * π) n : Set _) := by
  have h := norm_sub_apply_le_of_isIdempotentElem (fourierProj n)
    (isIdempotentElem_fourierProj n) f
  rwa [range_fourierProj, norm_fourierProj] at h

/-! ### Zygmund's lower bound for the Lebesgue constants -/

/-- Since $D_n$ is even, the Lebesgue constant is
$$L_n = \frac{2}{\pi} \int_0^{\pi} |D_n(t)|\, dt.$$
-/
theorem lebesgueConstant_eq (n : ℕ) :
    lebesgueConstant n = 2 / π * ∫ t in (0 : ℝ)..π, |dirichletKernel n t| := by
  have hcont : Continuous fun t => |dirichletKernel n t| := (continuous_dirichletKernel n).abs
  have hneg : (∫ t in -π..(0 : ℝ), |dirichletKernel n t|)
      = ∫ t in (0 : ℝ)..π, |dirichletKernel n t| := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := π)
      fun t => |dirichletKernel n t|
    simpa using h.symm
  rw [lebesgueConstant, ← intervalIntegral.integral_add_adjacent_intervals
      (b := (0 : ℝ)) (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _), hneg]
  ring

/-- For every real $a$, $\int_a^{a + \pi} |\sin x|\, dx = 2$. -/
private theorem integral_abs_sin (a : ℝ) : ∫ x in a..a + π, |Real.sin x| = 2 := by
  have hper : Function.Periodic (fun x : ℝ => |Real.sin x|) π := fun x => by
    simp only [Real.sin_add_pi, abs_neg]
  rw [hper.intervalIntegral_add_eq a 0, zero_add]
  have hcongr : ∀ x ∈ Set.uIcc (0 : ℝ) π, |Real.sin x| = Real.sin x := by
    intro x hx
    rw [Set.uIcc_of_le Real.pi_pos.le] at hx
    exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx.1 hx.2)
  rw [intervalIntegral.integral_congr hcongr, integral_sin]
  norm_num

/-- For $0 < t \le \pi$, $|\sin((n + 1/2) t)| / t \le |D_n(t)|$, by the closed form of $D_n$ and
$2 \sin(t/2) \le t$. -/
private theorem abs_sin_div_le {n : ℕ} {t : ℝ} (ht0 : 0 < t) (htπ : t ≤ π) :
    |Real.sin (((n : ℝ) + 1 / 2) * t)| / t ≤ |dirichletKernel n t| := by
  have hs : 0 < Real.sin (t / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hle : 2 * Real.sin (t / 2) ≤ t := by
    have := Real.sin_le (by linarith : (0 : ℝ) ≤ t / 2)
    linarith
  have h2s : (0 : ℝ) < 2 * Real.sin (t / 2) := by linarith
  rw [dirichletKernel_eq_sin_div hs.ne', abs_div, abs_of_pos h2s, div_le_div_iff₀ ht0 h2s]
  exact mul_le_mul_of_nonneg_left hle (abs_nonneg _)

/-- For $1 \le k \le n$, the integral of $|D_n|$ over $[(k - 1)\pi / (n + 1/2), k\pi / (n + 1/2)]$,
the $k$-th arch of $\sin((n + 1/2) t)$, is at least $2 / (k\pi)$. -/
private theorem piece_le (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    2 / ((k : ℝ) * π)
      ≤ ∫ t in (((k : ℝ) - 1) * π / ((n : ℝ) + 1 / 2))..((k : ℝ) * π / ((n : ℝ) + 1 / 2)),
          |dirichletKernel n t| := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hc : (0 : ℝ) < (n : ℝ) + 1 / 2 := by positivity
  have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hkn' : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
  have hA0 : (0 : ℝ) ≤ ((k : ℝ) - 1) * π / ((n : ℝ) + 1 / 2) :=
    div_nonneg (mul_nonneg (by linarith) hπ.le) hc.le
  have hAB : ((k : ℝ) - 1) * π / ((n : ℝ) + 1 / 2) ≤ (k : ℝ) * π / ((n : ℝ) + 1 / 2) := by
    rw [div_le_div_iff₀ hc hc]
    nlinarith
  have hBπ : (k : ℝ) * π / ((n : ℝ) + 1 / 2) ≤ π := by
    rw [div_le_iff₀ hc]
    nlinarith
  have hpt : ∀ t ∈ Set.Icc (((k : ℝ) - 1) * π / ((n : ℝ) + 1 / 2))
      ((k : ℝ) * π / ((n : ℝ) + 1 / 2)),
      ((n : ℝ) + 1 / 2) / ((k : ℝ) * π) * |Real.sin (((n : ℝ) + 1 / 2) * t)|
        ≤ |dirichletKernel n t| := by
    intro t ht
    rcases eq_or_lt_of_le (hA0.trans ht.1) with h0 | h0
    · rw [← h0]
      simp
    · have htπ : t ≤ π := ht.2.trans hBπ
      refine le_trans ?_ (abs_sin_div_le h0 htπ)
      have hct : ((n : ℝ) + 1 / 2) * t ≤ (k : ℝ) * π := by
        have := ht.2
        rw [le_div_iff₀ hc] at this
        linarith
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) h0]
      nlinarith [abs_nonneg (Real.sin (((n : ℝ) + 1 / 2) * t))]
  have hI := intervalIntegral.integral_mono_on (μ := volume) hAB
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _) hpt
  have hcomp : (∫ t in (((k : ℝ) - 1) * π / ((n : ℝ) + 1 / 2))..((k : ℝ) * π / ((n : ℝ) + 1 / 2)),
        |Real.sin (((n : ℝ) + 1 / 2) * t)|)
      = (((n : ℝ) + 1 / 2))⁻¹ * ∫ s in (((k : ℝ) - 1) * π)..(((k : ℝ) - 1) * π + π),
          |Real.sin s| := by
    rw [intervalIntegral.integral_comp_mul_left (fun s => |Real.sin s|) hc.ne', smul_eq_mul]
    congr 2 <;> field_simp
    ring
  rw [intervalIntegral.integral_const_mul, hcomp, integral_abs_sin] at hI
  refine le_trans (le_of_eq ?_) hI
  have hk0 : (k : ℝ) ≠ 0 := by linarith
  field_simp

/-- The integral of $|D_n|$ over $[0, \pi]$ is at least $\sum_{k=1}^n 2 / (k\pi)$. -/
private theorem sum_pieces_le (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, 2 / ((k : ℝ) * π)
      ≤ ∫ t in (0 : ℝ)..π, |dirichletKernel n t| := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hc : (0 : ℝ) < (n : ℝ) + 1 / 2 := by positivity
  have hcont : Continuous fun t : ℝ => |dirichletKernel n t| := (continuous_dirichletKernel n).abs
  have hstep : ∀ m : ℕ, m ≤ n →
      ∑ k ∈ Finset.Icc 1 m, 2 / ((k : ℝ) * π)
        ≤ ∫ t in (0 : ℝ)..((m : ℝ) * π / ((n : ℝ) + 1 / 2)), |dirichletKernel n t| := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      have h2 := piece_le n (m + 1) (by omega) hm
      push_cast at h2
      rw [show (m : ℝ) + 1 - 1 = (m : ℝ) by ring] at h2
      have hadj : (∫ t in (0 : ℝ)..((m : ℝ) * π / ((n : ℝ) + 1 / 2)), |dirichletKernel n t|)
          + (∫ t in ((m : ℝ) * π / ((n : ℝ) + 1 / 2))..(((m : ℝ) + 1) * π / ((n : ℝ) + 1 / 2)),
              |dirichletKernel n t|)
          = ∫ t in (0 : ℝ)..(((m : ℝ) + 1) * π / ((n : ℝ) + 1 / 2)), |dirichletKernel n t| :=
        intervalIntegral.integral_add_adjacent_intervals
          (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
      rw [Finset.sum_Icc_succ_top (by omega)]
      push_cast
      rw [← hadj]
      exact add_le_add h1 h2
  have hfin := hstep n le_rfl
  have hnπ : (n : ℝ) * π / ((n : ℝ) + 1 / 2) ≤ π := by
    rw [div_le_iff₀ hc]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have htail : (0 : ℝ) ≤ ∫ t in ((n : ℝ) * π / ((n : ℝ) + 1 / 2))..π, |dirichletKernel n t| :=
    intervalIntegral.integral_nonneg (μ := volume) hnπ fun _ _ => abs_nonneg _
  have hadj := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (a := (0 : ℝ)) (b := (n : ℝ) * π / ((n : ℝ) + 1 / 2)) (c := π)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
  linarith

/-- For every natural number $n$, $\log n \le \sum_{k=1}^n 1/k$, by `log_add_one_le_harmonic` of
Mathlib. -/
private theorem log_le_sum_inv (n : ℕ) :
    Real.log n ≤ ∑ k ∈ Finset.Icc 1 n, ((k : ℝ))⁻¹ := by
  have key := log_add_one_le_harmonic n
  rw [harmonic_eq_sum_Icc] at key
  push_cast at key
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · refine le_trans (Real.log_le_log (by exact_mod_cast hn) ?_) key
    linarith

/-- **Zygmund's lower bound for the Lebesgue constants.** For every natural number $n$,
$$\frac{4}{\pi^2} \log n \le L_n.$$

This is the lower half of the asymptotic formula $L_n = (4/\pi^2) \log n + O(1)$ in (3.7.10) of
[han2009theoretical]. It is the half that the divergence argument needs: the Lebesgue constants
are unbounded, so the Fourier series of some continuous periodic function does not converge
uniformly.

For $n = 0$ the statement holds because $\log 0 = 0$ in Mathlib. -/
theorem log_le_lebesgueConstant (n : ℕ) :
    4 / π ^ 2 * Real.log n ≤ lebesgueConstant n := by
  have hsum : ∑ k ∈ Finset.Icc 1 n, 2 / ((k : ℝ) * π)
      = 2 / π * ∑ k ∈ Finset.Icc 1 n, ((k : ℝ))⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : (k : ℝ) ≠ 0 := by
      have h := (Finset.mem_Icc.1 hk).1
      have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
      linarith
    field_simp
  have hI : 2 / π * Real.log n ≤ ∫ t in (0 : ℝ)..π, |dirichletKernel n t| := by
    refine le_trans ?_ (sum_pieces_le n)
    rw [hsum]
    exact mul_le_mul_of_nonneg_left (log_le_sum_inv n) (by positivity)
  rw [lebesgueConstant_eq, show 4 / π ^ 2 * Real.log n = 2 / π * (2 / π * Real.log n) by
    field_simp; ring]
  exact mul_le_mul_of_nonneg_left hI (by positivity)

/-! ### An upper bound for the Lebesgue constants -/

/-- For $0 < t \le \pi$, $|D_n(t)| \le \pi / (2t)$, uniformly in $n$: the numerator of the closed
form (3.7.8) is at most one, and Jordan's inequality `Real.mul_le_sin` bounds the denominator
below by $2t / \pi$. -/
private theorem abs_dirichletKernel_le_div (n : ℕ) {t : ℝ} (ht0 : 0 < t) (htp : t ≤ π) :
    |dirichletKernel n t| ≤ π / 2 * t⁻¹ := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hs : t / π ≤ Real.sin (t / 2) := by
    have h := Real.mul_le_sin (x := t / 2) (by positivity) (by linarith)
    calc t / π = 2 / π * (t / 2) := by ring
      _ ≤ Real.sin (t / 2) := h
  have hst : t ≤ π * Real.sin (t / 2) := by
    rw [div_le_iff₀ hπ] at hs
    linarith
  have hs0 : 0 < Real.sin (t / 2) := by nlinarith
  rw [dirichletKernel_eq_sin_div (ne_of_gt hs0), abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.sin (t / 2)),
    div_le_iff₀ (by positivity),
    show π / 2 * t⁻¹ * (2 * Real.sin (t / 2)) = π * Real.sin (t / 2) / t by field_simp,
    le_div_iff₀ ht0]
  have h1 : |Real.sin (((n : ℝ) + 1 / 2) * t)| * t ≤ 1 * t :=
    mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) ht0.le
  linarith

/-- **The Lebesgue constants grow at most like $\log n$.** For every natural number $n$,
$$L_n \le 1 + \log(2n + 1).$$

With `PeriodicCont.log_le_lebesgueConstant`, this shows that $L_n$ grows like $\log n$. Section
3.7 of [han2009theoretical] states the sharp formula $L_n = (4/\pi^2) \log n + O(1)$ in
(3.7.10). The constant here is not the sharp one, but this upper bound is what the uniform
convergence rate (3.7.12) uses.

The proof splits $[0, \pi]$ at $\pi / (2n + 1)$, where the numerator $\sin((n + 1/2) t)$ of the
closed form of $D_n$ first reaches its maximum $1$. Below this point $|D_n| \le n + 1/2$, which
contributes $\pi / 2$. Above it Jordan's inequality gives $|D_n(t)| \le \pi / (2t)$, whose
integral gives the logarithm. -/
theorem lebesgueConstant_le (n : ℕ) : lebesgueConstant n ≤ 1 + Real.log (2 * (n : ℝ) + 1) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hN : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = π / (2 * (n : ℝ) + 1) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [hadef]; positivity
  have hap : a ≤ π := by
    rw [hadef, div_le_iff₀ hN]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hcont : Continuous fun t : ℝ => |dirichletKernel n t| := (continuous_dirichletKernel n).abs
  -- the piece near the origin, where the kernel is bounded by `n + 1/2`
  have h1 : (∫ t in (0 : ℝ)..a, |dirichletKernel n t|) ≤ π / 2 := by
    have hmono := intervalIntegral.integral_mono_on (μ := volume) ha0.le
      (hcont.intervalIntegrable _ _) intervalIntegrable_const
      (fun t _ => abs_dirichletKernel_le n t)
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
    refine hmono.trans (le_of_eq ?_)
    rw [hadef]
    field_simp
  -- the piece away from the origin, where Jordan's inequality applies
  have hint : IntervalIntegrable (fun t : ℝ => π / 2 * t⁻¹) volume a π := by
    refine (ContinuousOn.intervalIntegrable ?_)
    refine continuousOn_const.mul (continuousOn_inv₀.mono ?_)
    intro t ht
    rw [Set.uIcc_of_le hap] at ht
    exact ne_of_gt (lt_of_lt_of_le ha0 ht.1)
  have h2 : (∫ t in a..π, |dirichletKernel n t|) ≤ π / 2 * Real.log (2 * (n : ℝ) + 1) := by
    have hmono := intervalIntegral.integral_mono_on (μ := volume) hap
      (hcont.intervalIntegrable _ _) hint
      (fun t ht => abs_dirichletKernel_le_div n (lt_of_lt_of_le ha0 ht.1) ht.2)
    refine hmono.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos ha0 hπ, hadef]
    congr 1
    field_simp
  -- and the two pieces together
  have hadj := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (a := (0 : ℝ)) (b := a) (c := π)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
  rw [lebesgueConstant_eq]
  have hsum : (∫ t in (0 : ℝ)..π, |dirichletKernel n t|)
      ≤ π / 2 + π / 2 * Real.log (2 * (n : ℝ) + 1) := by
    rw [← hadj]
    linarith
  have hcoef : (0 : ℝ) < 2 / π := by positivity
  calc 2 / π * ∫ t in (0 : ℝ)..π, |dirichletKernel n t|
      ≤ 2 / π * (π / 2 + π / 2 * Real.log (2 * (n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hsum hcoef.le
    _ = 1 + Real.log (2 * (n : ℝ) + 1) := by field_simp

end PeriodicCont
