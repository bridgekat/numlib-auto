/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Numlib.Analysis.Normed.Module.BestApprox
import Numlib.Approximation.Trigonometric
import Numlib.IntegralEquations.Basic

/-!
# Truncated expansions in an orthonormal system, as integral operators

Let $p_0, \dots, p_N$ be continuous real functions on a compact space $X$ that carries a finite
Borel measure $\mu$. The **truncated expansion** $u \mapsto \sum_i (u, p_i)_{L^2(\mu)}\, p_i$ is an
operator on the Banach space $C(X)$, and it is the integral operator whose kernel is the
**reproducing kernel**
$$K(x, t) = \sum_i p_i(x)\, p_i(t)$$
of the system. By the norm formula for a kernel operator, its operator norm is the largest row
integral $\max_x \int |K(x, t)|\, d\mu(t)$. When the system is orthonormal in $L^2(\mu)$, the
operator is the least-squares projection onto the span of the system: it is idempotent, and its
range is that span. The material is [han2009theoretical], §3.7.1, (3.7.13)–(3.7.17), and the
Chebyshev case is Example 3.7.4 of [han2009theoretical].

The identification gives the norm: the size of a least-squares projection in the uniform norm is a
statement about the kernel. For the orthonormal polynomials of a weight, the kernel can be computed
from the Christoffel–Darboux identity. For the orthonormal Chebyshev system on $[-1, 1]$, the kernel
in the angle variables $x = \cos\theta$, $t = \cos\varphi$ is $\frac{1}{\pi}[D_N(\theta - \varphi) +
D_N(\theta + \varphi)]$, with $D_N$ the Dirichlet kernel, and the norm of the projection is exactly
the Lebesgue constant of the Fourier projection.

## Main definitions

* `Approximation.reproducingKernel`: the kernel $K(x, t) = \sum_i p_i(x)\, p_i(t)$ of a finite
  family.
* `Approximation.IsOrthonormal`: the condition $\int p_i p_j \, d\mu = \delta_{ij}$.
* `Approximation.expansionCLM`: the truncated expansion, as a bounded operator on $C(X)$.
* `Approximation.chebyshevMeasureIcc`: the Chebyshev weight $(1 - x^2)^{-1/2}\,dx$ as a measure on
  $[-1, 1]$.
* `Approximation.chebyshevOrthonormal`: the orthonormal Chebyshev system $1/\sqrt{\pi}$,
  $\sqrt{2/\pi}\, T_n$.
* `Approximation.chebyshevProj`: the truncated expansion in the first $N + 1$ members of the
  orthonormal Chebyshev system.

## Main results

* `Approximation.expansionCLM_eq_sum`: the truncated expansion is $\sum_i (u, p_i)\, p_i$.
* `Approximation.norm_expansionCLM`: $\|P\| = \sup_x \int |K(x, t)|\, d\mu(t)$.
* `Approximation.IsOrthonormal.isIdempotentElem_expansionCLM`: for an orthonormal system, the
  truncated expansion is a projection.
* `Approximation.IsOrthonormal.range_expansionCLM`: for an orthonormal system, the range of the
  truncated expansion is the span of the system.
* `Approximation.IsOrthonormal.norm_sub_expansionCLM_le`: the Lebesgue lemma $\|u - Pu\| \le (1 +
  \|P\|) \operatorname{dist}(u, \operatorname{span} p)$.
* `Approximation.chebyshevKernel_cos`: the Chebyshev reproducing kernel in the angle variables.
* `Approximation.norm_chebyshevProj`: the norm of the Chebyshev least-squares projection is the
  Lebesgue constant `PeriodicCont.lebesgueConstant` of the Fourier projection.

## Implementation notes

* [han2009theoretical] states the material for the orthonormal polynomials of a weight on $[-1, 1]$.
  The general results here use only the continuity of the functions of the system; the Chebyshev
  section is the only place that uses polynomials.
* The truncated expansion `Approximation.expansionCLM` is defined for every finite family.
  Orthonormality enters only in the results of the namespace `Approximation.IsOrthonormal`.
-/

open MeasureTheory Set

noncomputable section

namespace Approximation

variable {X ι : Type*} [TopologicalSpace X] [Fintype ι]

/-- The **reproducing kernel** of a finite family $(p_i)$ of continuous functions on $X$ is the
continuous function on $X \times X$
$$K(x, t) = \sum_i p_i(x)\, p_i(t).$$
This is (3.7.16) of [han2009theoretical]. -/
def reproducingKernel (p : ι → C(X, ℝ)) : C(X × X, ℝ) :=
  ⟨fun q => ∑ i, p i q.1 * p i q.2, continuous_finsetSum _ fun i _ =>
    ((p i).continuous.comp continuous_fst).mul ((p i).continuous.comp continuous_snd)⟩

/-- The value of the reproducing kernel: $K(x, t) = \sum_i p_i(x)\, p_i(t)$. -/
@[simp]
theorem reproducingKernel_apply (p : ι → C(X, ℝ)) (x t : X) :
    reproducingKernel p (x, t) = ∑ i, p i x * p i t :=
  rfl

variable [MeasurableSpace X]

/-- A finite family $(p_i)$ of continuous functions on $X$ is **orthonormal in $L^2(\mu)$** if
$$\int p_i\, p_j \, d\mu = \delta_{ij}$$
for all indices $i$ and $j$.

This is the standing hypothesis of [han2009theoretical], §3.7.1, where the family is the family
of orthonormal polynomials of a weight on $[-1, 1]$. -/
structure IsOrthonormal (μ : Measure X) (p : ι → C(X, ℝ)) : Prop where
  /-- Each member has unit norm in $L^2(\mu)$: $\int p_i\, p_i \, d\mu = 1$. -/
  integral_mul_self : ∀ i, (∫ t, p i t * p i t ∂μ) = 1
  /-- Distinct members are orthogonal in $L^2(\mu)$: $\int p_i\, p_j \, d\mu = 0$ for $i \neq j$. -/
  integral_mul_of_ne : ∀ ⦃i j⦄, i ≠ j → (∫ t, p i t * p j t ∂μ) = 0

variable [CompactSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/-- Let $X$ be a compact space with a finite Borel measure $\mu$, and let $(p_i)$ be a finite family
in $C(X)$. The **truncated expansion** in $(p_i)$ is the bounded operator on $C(X)$
$$Pu = \sum_i (u, p_i)_{L^2(\mu)}\, p_i,$$
defined as the integral operator `IntegralOperator.kernelCLM` with the reproducing kernel
`Approximation.reproducingKernel` as kernel. This is (3.7.15) of [han2009theoretical].

For an orthonormal family, $P$ is the least-squares projection onto the span of the family: the
orthogonal projection of $L^2(\mu)$, restricted to the continuous functions. See
`Approximation.IsOrthonormal.isIdempotentElem_expansionCLM` and
`Approximation.IsOrthonormal.range_expansionCLM`. -/
def expansionCLM (p : ι → C(X, ℝ)) : C(X, ℝ) →L[ℝ] C(X, ℝ) :=
  IntegralOperator.kernelCLM μ (reproducingKernel p)

/-- The value of the truncated expansion at a point $x$ is
$$(Pu)(x) = \sum_i \Bigl(\int u(t)\, p_i(t)\, d\mu(t)\Bigr) p_i(x).$$
This is (3.7.13) of [han2009theoretical]. -/
theorem expansionCLM_apply (p : ι → C(X, ℝ)) (u : C(X, ℝ)) (x : X) :
    expansionCLM μ p u x = ∑ i, (∫ t, u t * p i t ∂μ) * p i x := by
  have hint : ∀ i : ι, Integrable (fun t : X => p i x * (u t * p i t)) μ := fun i =>
    IntegralOperator.integrable_of_continuousMap μ
      ⟨_, continuous_const.mul (u.continuous.mul (p i).continuous)⟩
  have hrw : ∀ t : X, reproducingKernel p (x, t) * u t = ∑ i, p i x * (u t * p i t) := fun t => by
    rw [reproducingKernel_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [expansionCLM, IntegralOperator.kernelCLM_apply,
    integral_congr_ae (Filter.Eventually.of_forall hrw),
    integral_finsetSum _ fun i _ => hint i]
  exact Finset.sum_congr rfl fun i _ => by rw [integral_const_mul]; ring

/-- The truncated expansion is the linear combination $Pu = \sum_i \bigl(\int u\, p_i \, d\mu\bigr)
p_i$ of the members of the family. This is (3.7.13) of [han2009theoretical]. -/
theorem expansionCLM_eq_sum (p : ι → C(X, ℝ)) (u : C(X, ℝ)) :
    expansionCLM μ p u = ∑ i, (∫ t, u t * p i t ∂μ) • p i := by
  ext x
  rw [expansionCLM_apply, ContinuousMap.coe_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => rfl

/-- The truncated expansion $Pu$ lies in the span of the family $(p_i)$. -/
theorem expansionCLM_mem_span (p : ι → C(X, ℝ)) (u : C(X, ℝ)) :
    expansionCLM μ p u ∈ Submodule.span ℝ (Set.range p) := by
  rw [expansionCLM_eq_sum]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

/-- **The uniform norm of a truncated expansion is the largest row integral of its reproducing
kernel.** Let $X$ be a nonempty compact space with a finite Borel measure $\mu$, and let $(p_i)$
be a finite family in $C(X)$. Then the truncated expansion $P$ satisfies
$$\|P\| = \sup_{x \in X} \int \Bigl|\sum_i p_i(x)\, p_i(t)\Bigr| \, d\mu(t).$$
This is (3.7.17) of [han2009theoretical].

The proof specializes `IntegralOperator.norm_kernelCLM`, the norm formula for a kernel operator
on a compact space. -/
theorem norm_expansionCLM [Nonempty X] (p : ι → C(X, ℝ)) :
    ‖expansionCLM μ p‖ = ⨆ x, ∫ t, |∑ i, p i x * p i t| ∂μ := by
  rw [expansionCLM, IntegralOperator.norm_kernelCLM]
  simp only [reproducingKernel_apply]

variable {μ}

namespace IsOrthonormal

/-- The truncated expansion in an orthonormal family fixes each member of the family: $P p_j = p_j$.
-/
theorem expansionCLM_apply_eq_self {p : ι → C(X, ℝ)} (h : IsOrthonormal μ p) (j : ι) :
    expansionCLM μ p (p j) = p j := by
  ext x
  rw [expansionCLM_apply,
    Finset.sum_eq_single j (fun i _ hi => by rw [h.integral_mul_of_ne (Ne.symm hi), zero_mul])
      (fun hj => absurd (Finset.mem_univ j) hj),
    h.integral_mul_self j, one_mul]

/-- The truncated expansion in an orthonormal family fixes every function $u$ in the span of the
family: $Pu = u$. -/
theorem expansionCLM_eq_self {p : ι → C(X, ℝ)} (h : IsOrthonormal μ p) {u : C(X, ℝ)}
    (hu : u ∈ Submodule.span ℝ (Set.range p)) : expansionCLM μ p u = u := by
  induction hu using Submodule.span_induction with
  | mem v hv => obtain ⟨j, rfl⟩ := hv; exact h.expansionCLM_apply_eq_self j
  | zero => exact map_zero _
  | add v w _ _ hv hw => rw [map_add, hv, hw]
  | smul c v _ hv => rw [map_smul, hv]

/-- **The truncated expansion in an orthonormal system is a projection.** If $(p_i)$ is orthonormal
in $L^2(\mu)$, then $P \circ P = P$. This is part of (3.7.13) of [han2009theoretical]. -/
theorem isIdempotentElem_expansionCLM {p : ι → C(X, ℝ)} (h : IsOrthonormal μ p) :
    IsIdempotentElem (expansionCLM μ p) := by
  ext u x
  exact congrFun (congrArg _ (h.expansionCLM_eq_self (expansionCLM_mem_span μ p u))) x

/-- **The range of the truncated expansion in an orthonormal system is the span of the system.** If
$(p_i)$ is orthonormal in $L^2(\mu)$, then the range of $P$ is the span of $\{p_i\}$. -/
theorem range_expansionCLM {p : ι → C(X, ℝ)} (h : IsOrthonormal μ p) :
    LinearMap.range ((expansionCLM μ p : C(X, ℝ) →L[ℝ] C(X, ℝ)) : C(X, ℝ) →ₗ[ℝ] C(X, ℝ))
      = Submodule.span ℝ (Set.range p) := by
  refine le_antisymm ?_ fun u hu => ⟨u, h.expansionCLM_eq_self hu⟩
  rintro _ ⟨u, rfl⟩
  exact expansionCLM_mem_span μ p u

/-- **The Lebesgue lemma for a least-squares projection.** If $(p_i)$ is orthonormal in $L^2(\mu)$
and $P$ is the truncated expansion in $(p_i)$, then for every $u \in C(X)$
$$\|u - Pu\| \le (1 + \|P\|)\, \operatorname{dist}(u, \operatorname{span}\{p_i\}),$$
where the norm and the distance are the uniform ones. This is (3.7.14) of [han2009theoretical].

The proof specializes `norm_sub_apply_le_of_isIdempotentElem`. -/
theorem norm_sub_expansionCLM_le {p : ι → C(X, ℝ)} (h : IsOrthonormal μ p) (u : C(X, ℝ)) :
    ‖u - expansionCLM μ p u‖
      ≤ (1 + ‖expansionCLM μ p‖) *
          Metric.infDist u (Submodule.span ℝ (Set.range p) : Set C(X, ℝ)) := by
  have hle := norm_sub_apply_le_of_isIdempotentElem (expansionCLM μ p)
    h.isIdempotentElem_expansionCLM u
  rwa [h.range_expansionCLM] at hle

end IsOrthonormal

/-!
### The Chebyshev least-squares projection

The orthonormal Chebyshev system on $[-1, 1]$ for the weight $(1 - x^2)^{-1/2}$, its reproducing
kernel in the angle variables, and the norm of the truncated expansion in it. This norm is exactly
the Lebesgue constant `PeriodicCont.lebesgueConstant` of the Fourier projection (Example 3.7.4 of
[han2009theoretical]).
-/

section Chebyshev

open Real PeriodicCont

open Polynomial.Chebyshev (T measureT)

/-- Mathlib's Chebyshev measure `Polynomial.Chebyshev.measureT`, Lebesgue measure on $(-1, 1]$ with
the density $(1 - x^2)^{-1/2}$, is a finite measure. Its total mass is $\pi$.

The proof uses only the integrability of the constant function $1$. -/
instance : IsFiniteMeasure measureT := by
  rcases integrable_const_iff.1
      (Polynomial.Chebyshev.integrable_measureT (f := fun _ => (1 : ℝ)) continuousOn_const) with
    h | h
  · exact absurd h one_ne_zero
  · exact h

/-- **The Chebyshev weight as a measure on the compact space $[-1, 1]$**: Lebesgue measure with the
density $(1 - x^2)^{-1/2}$. This is the weight of (3.5.8) and Example 3.7.4 of
[han2009theoretical].

It is the pullback of `Polynomial.Chebyshev.measureT` along the inclusion of $[-1, 1]$ in
$\mathbb{R}$. -/
noncomputable def chebyshevMeasureIcc : Measure (Set.Icc (-1 : ℝ) 1) :=
  Measure.comap Subtype.val measureT

instance : IsFiniteMeasure chebyshevMeasureIcc := by
  refine ⟨?_⟩
  rw [chebyshevMeasureIcc, comap_subtype_coe_apply measurableSet_Icc]
  exact measure_lt_top _ _

/-- For every function $f$ on $\mathbb{R}$, the integral of $f$ over the space $[-1, 1]$ against
`Approximation.chebyshevMeasureIcc` equals the integral of $f$ over the line against
`Polynomial.Chebyshev.measureT`. The endpoints carry no mass. -/
theorem integral_chebyshevMeasureIcc (f : ℝ → ℝ) :
    ∫ t : Set.Icc (-1 : ℝ) 1, f t ∂chebyshevMeasureIcc = ∫ x, f x ∂measureT := by
  have hrestrict : measureT.restrict (Set.Icc (-1 : ℝ) 1) = measureT := by
    rw [measureT, Measure.restrict_restrict measurableSet_Icc]
    congr 1
    exact Set.inter_eq_right.2 (Set.Ioc_subset_Icc_self (a := (-1 : ℝ)) (b := 1))
  rw [chebyshevMeasureIcc, integral_subtype_comap measurableSet_Icc, hrestrict]

/-- The normalizing coefficients of the orthonormal Chebyshev system: $c_0 = \sqrt{1/\pi}$ and
$c_n = \sqrt{2/\pi}$ for $n \ge 1$. They come from the values $\int T_0^2 = \pi$ and
$\int T_n^2 = \pi/2$ of (3.5.9) of [han2009theoretical]. -/
noncomputable def chebyshevCoeff (n : ℕ) : ℝ := if n = 0 then √(1 / π) else √(2 / π)

/-- The normalizing coefficient in degree $0$ satisfies $c_0^2 = 1/\pi$. -/
theorem chebyshevCoeff_mul_self_zero : chebyshevCoeff 0 * chebyshevCoeff 0 = 1 / π := by
  rw [chebyshevCoeff, ite_eq_left rfl, Real.mul_self_sqrt (by positivity)]

/-- The normalizing coefficient in degree $n \neq 0$ satisfies $c_n^2 = 2/\pi$. -/
theorem chebyshevCoeff_mul_self_of_ne {n : ℕ} (hn : n ≠ 0) :
    chebyshevCoeff n * chebyshevCoeff n = 2 / π := by
  rw [chebyshevCoeff, ite_eq_right hn, Real.mul_self_sqrt (by positivity)]

/-- **The orthonormal Chebyshev system** on $[-1, 1]$ for the weight $(1 - x^2)^{-1/2}$: the
continuous functions
$$p_0 = \frac{1}{\sqrt{\pi}}, \qquad p_n = \sqrt{\frac{2}{\pi}}\, T_n \quad (n \ge 1),$$
where $T_n$ is the Chebyshev polynomial of degree $n$. This is (3.5.8) and Example 3.7.4 of
[han2009theoretical]. -/
noncomputable def chebyshevOrthonormal (n : ℕ) : C(Set.Icc (-1 : ℝ) 1, ℝ) :=
  ⟨fun x => chebyshevCoeff n * (T ℝ n).eval (x : ℝ),
    continuous_const.mul ((T ℝ (n : ℤ)).continuous_aeval.comp continuous_subtype_val)⟩

/-- The value of the $n$-th orthonormal Chebyshev function at $x$ is $c_n T_n(x)$, with the
coefficient $c_n$ of `Approximation.chebyshevCoeff`. -/
@[simp]
theorem chebyshevOrthonormal_apply (n : ℕ) (x : Set.Icc (-1 : ℝ) 1) :
    chebyshevOrthonormal n x = chebyshevCoeff n * (T ℝ n).eval (x : ℝ) :=
  rfl

/-- The Chebyshev system is orthonormal for the Chebyshev weight:
$\int_{[-1, 1]} p_m\, p_n \, d\mu = 1$ if $m = n$, and $0$ otherwise. This is (3.5.9) of
[han2009theoretical], normalized. -/
theorem integral_chebyshevOrthonormal_mul (m n : ℕ) :
    (∫ t : Set.Icc (-1 : ℝ) 1,
        chebyshevOrthonormal m t * chebyshevOrthonormal n t ∂chebyshevMeasureIcc)
      = if m = n then 1 else 0 := by
  simp only [chebyshevOrthonormal_apply]
  rw [integral_chebyshevMeasureIcc fun y =>
    (chebyshevCoeff m * (T ℝ m).eval y) * (chebyshevCoeff n * (T ℝ n).eval y)]
  have hmul : ∀ y : ℝ,
      (chebyshevCoeff m * (T ℝ m).eval y) * (chebyshevCoeff n * (T ℝ n).eval y)
        = (chebyshevCoeff m * chebyshevCoeff n) *
            ((T ℝ m).eval y * (T ℝ n).eval y) := fun y => by ring
  simp_rw [hmul]
  rw [integral_const_mul]
  rcases eq_or_ne m n with rfl | hmn
  · rcases eq_or_ne m 0 with rfl | hm
    · rw [ite_eq_left rfl, chebyshevCoeff_mul_self_zero]
      rw [show ((0 : ℕ) : ℤ) = 0 from Nat.cast_zero,
        Polynomial.Chebyshev.integral_eval_T_real_mul_self_measureT_zero]
      field_simp
    · rw [ite_eq_left rfl, chebyshevCoeff_mul_self_of_ne hm,
        Polynomial.Chebyshev.integral_T_real_mul_self_measureT_of_ne_zero hm]
      field_simp
  · rw [Polynomial.Chebyshev.integral_eval_T_real_mul_eval_T_real_measureT_of_ne hmn,
      mul_zero, ite_eq_right hmn]

/-- For every $N$, the first $N + 1$ functions $p_0, \dots, p_N$ of the orthonormal Chebyshev system
form an orthonormal family in $L^2(\mu)$ for the Chebyshev weight $\mu$, in the sense of
`Approximation.IsOrthonormal`. -/
theorem isOrthonormal_chebyshevOrthonormal (N : ℕ) :
    IsOrthonormal chebyshevMeasureIcc fun i : Fin (N + 1) => chebyshevOrthonormal i where
  integral_mul_self i := by rw [integral_chebyshevOrthonormal_mul, ite_eq_left rfl]
  integral_mul_of_ne i j hij := by
    rw [integral_chebyshevOrthonormal_mul, ite_eq_right (fun h => hij (Fin.val_injective h))]

/-- The reproducing kernel of the orthonormal Chebyshev system $p_0, \dots, p_N$, as a function of
two real arguments:
$$K_N(x, t) = \frac{1}{\pi}\, T_0(x)\, T_0(t) + \frac{2}{\pi} \sum_{n=1}^{N} T_n(x)\, T_n(t).$$
This is the kernel of Example 3.7.4 of [han2009theoretical]. -/
noncomputable def chebyshevKernel (N : ℕ) (x t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1),
    (chebyshevCoeff n * chebyshevCoeff n) * ((T ℝ n).eval x * (T ℝ n).eval t)

/-- On $[-1, 1]$, the reproducing kernel of $p_0, \dots, p_N$ is the Chebyshev kernel:
$\sum_{i=0}^{N} p_i(x)\, p_i(t) = K_N(x, t)$. -/
theorem sum_chebyshevOrthonormal_mul (N : ℕ) (x t : Set.Icc (-1 : ℝ) 1) :
    ∑ i : Fin (N + 1), chebyshevOrthonormal i x * chebyshevOrthonormal i t
      = chebyshevKernel N x t := by
  rw [chebyshevKernel, ← Fin.sum_univ_eq_sum_range
    (fun n => (chebyshevCoeff n * chebyshevCoeff n) *
      ((T ℝ n).eval (x : ℝ) * (T ℝ n).eval (t : ℝ)))]
  exact Finset.sum_congr rfl fun i _ => by simp only [chebyshevOrthonormal_apply]; ring

/-- **The Chebyshev reproducing kernel in the angle variables.** For all real $\theta$ and
$\varphi$,
$$K_N(\cos\theta, \cos\varphi) = \frac{1}{\pi} \bigl[D_N(\theta - \varphi) + D_N(\theta +
  \varphi)\bigr],$$
where $D_N(s) = \frac12 + \sum_{j=1}^{N} \cos(js)$ is the Dirichlet kernel `dirichletKernel`.
This is the identity of Example 3.7.4 of [han2009theoretical], in the form that Rivlin gives.

[han2009theoretical] prints the same identity with $D_N(s)$ written out as
$\sin((N + \frac12) s) / (2 \sin(s/2))$. -/
theorem chebyshevKernel_cos (N : ℕ) (θ φ : ℝ) :
    chebyshevKernel N (cos θ) (cos φ)
      = (dirichletKernel N (θ - φ) + dirichletKernel N (θ + φ)) / π := by
  have hπ : (π : ℝ) ≠ 0 := pi_ne_zero
  have hshift : ∀ (M : ℕ) (g : ℕ → ℝ),
      ∑ j ∈ Finset.Icc 1 M, g j = ∑ i ∈ Finset.range M, g (i + 1) := by
    intro M g
    induction M with
    | zero => simp
    | succ K ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
  have hterm : ∀ i : ℕ,
      (chebyshevCoeff (i + 1) * chebyshevCoeff (i + 1)) *
          ((T ℝ ((i + 1 : ℕ) : ℤ)).eval (cos θ) * (T ℝ ((i + 1 : ℕ) : ℤ)).eval (cos φ))
        = (Real.cos ((i + 1 : ℕ) * (θ - φ)) + Real.cos ((i + 1 : ℕ) * (θ + φ))) / π := by
    intro i
    have hT : ∀ s : ℝ, (T ℝ ((i + 1 : ℕ) : ℤ)).eval (cos s) = Real.cos ((i + 1 : ℕ) * s) := by
      intro s
      rw [Polynomial.Chebyshev.T_real_cos]
      push_cast
      ring_nf
    rw [chebyshevCoeff_mul_self_of_ne (Nat.succ_ne_zero i), hT, hT,
      show ((i + 1 : ℕ) : ℝ) * (θ - φ) = (i + 1 : ℕ) * θ - (i + 1 : ℕ) * φ by ring,
      show ((i + 1 : ℕ) : ℝ) * (θ + φ) = (i + 1 : ℕ) * θ + (i + 1 : ℕ) * φ by ring,
      Real.cos_sub, Real.cos_add]
    field_simp
    ring
  have hT0 : (T ℝ ((0 : ℕ) : ℤ)).eval (cos θ) * (T ℝ ((0 : ℕ) : ℤ)).eval (cos φ) = 1 := by
    rw [show ((0 : ℕ) : ℤ) = 0 from Nat.cast_zero, Polynomial.Chebyshev.T_zero]
    simp
  rw [chebyshevKernel, Finset.sum_range_succ' _ N]
  simp only [hterm]
  rw [hT0, chebyshevCoeff_mul_self_zero, mul_one, dirichletKernel_apply, dirichletKernel_apply,
    hshift N, hshift N, ← Finset.sum_div, Finset.sum_add_distrib]
  ring

/-- **The Chebyshev least-squares projection** $P_N$ of Example 3.7.4 of [han2009theoretical]: the
truncated expansion of a continuous function on $[-1, 1]$ in the orthonormal Chebyshev system
$p_0, \dots, p_N$, as a bounded operator on $C[-1, 1]$. -/
noncomputable def chebyshevProj (N : ℕ) :
    C(Set.Icc (-1 : ℝ) 1, ℝ) →L[ℝ] C(Set.Icc (-1 : ℝ) 1, ℝ) :=
  expansionCLM chebyshevMeasureIcc fun i : Fin (N + 1) => chebyshevOrthonormal i

/-- The row integral of the Chebyshev kernel, in the angle variable: for real $\theta$,
$$\int_{[-1, 1]} |K_N(\cos\theta, t)| \, d\mu(t) = \frac{1}{\pi} \int_0^\pi \bigl|D_N(\theta -
  \varphi) + D_N(\theta + \varphi)\bigr| \, d\varphi,$$
where $\mu$ is the Chebyshev weight. -/
theorem integral_abs_chebyshevKernel (N : ℕ) (θ : ℝ) :
    (∫ t : Set.Icc (-1 : ℝ) 1, |chebyshevKernel N (cos θ) t| ∂chebyshevMeasureIcc)
      = 1 / π * ∫ φ in (0 : ℝ)..π,
          |dirichletKernel N (θ - φ) + dirichletKernel N (θ + φ)| := by
  have hπ : (0 : ℝ) < π := pi_pos
  rw [integral_chebyshevMeasureIcc fun y => |chebyshevKernel N (cos θ) y|,
    Polynomial.Chebyshev.integral_measureT_eq_integral_cos,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun φ _ => ?_
  rw [chebyshevKernel_cos, abs_div, abs_of_pos hπ]
  ring

/-- The Lebesgue function of the Chebyshev projection never exceeds the Lebesgue constant $L_N$ of
the Fourier projection: for real $\theta$,
$$\frac{1}{\pi} \int_0^\pi \bigl|D_N(\theta - \varphi) + D_N(\theta + \varphi)\bigr| \, d\varphi
  \le L_N.$$
The integral of $|D_N(\theta - \varphi) + D_N(\theta + \varphi)|$ over half a period is at most
the integral of $|D_N|$ over a full period. -/
theorem integral_abs_chebyshevKernel_le (N : ℕ) (θ : ℝ) :
    (1 / π * ∫ φ in (0 : ℝ)..π, |dirichletKernel N (θ - φ) + dirichletKernel N (θ + φ)|)
      ≤ lebesgueConstant N := by
  have hcont : Continuous fun u : ℝ => |dirichletKernel N u| :=
    (continuous_dirichletKernel N).abs
  have hper : Function.Periodic (fun u : ℝ => |dirichletKernel N u|) (2 * π) := fun u => by
    simp only []
    rw [dirichletKernel_periodic N u]
  have hcont1 : Continuous
      fun φ : ℝ => |dirichletKernel N (θ - φ) + dirichletKernel N (θ + φ)| :=
    (((continuous_dirichletKernel N).comp (continuous_const.sub continuous_id)).add
      ((continuous_dirichletKernel N).comp (continuous_const.add continuous_id))).abs
  have hcontm : Continuous fun φ : ℝ => |dirichletKernel N (θ - φ)| :=
    ((continuous_dirichletKernel N).comp (continuous_const.sub continuous_id)).abs
  have hcontp : Continuous fun φ : ℝ => |dirichletKernel N (θ + φ)| :=
    ((continuous_dirichletKernel N).comp (continuous_const.add continuous_id)).abs
  have hint1 : IntervalIntegrable
      (fun φ : ℝ => |dirichletKernel N (θ - φ) + dirichletKernel N (θ + φ)|) volume 0 π :=
    hcont1.intervalIntegrable _ _
  have hint2 : IntervalIntegrable
      (fun φ : ℝ => |dirichletKernel N (θ - φ)| + |dirichletKernel N (θ + φ)|) volume 0 π :=
    (hcontm.add hcontp).intervalIntegrable _ _
  have hmono : (∫ φ in (0 : ℝ)..π, |dirichletKernel N (θ - φ) + dirichletKernel N (θ + φ)|)
      ≤ ∫ φ in (0 : ℝ)..π, |dirichletKernel N (θ - φ)| + |dirichletKernel N (θ + φ)| :=
    intervalIntegral.integral_mono_on pi_pos.le hint1 hint2 fun φ _ => abs_add_le _ _
  have hsplit : (∫ φ in (0 : ℝ)..π, |dirichletKernel N (θ - φ)| + |dirichletKernel N (θ + φ)|)
      = (∫ φ in (0 : ℝ)..π, |dirichletKernel N (θ - φ)|)
          + ∫ φ in (0 : ℝ)..π, |dirichletKernel N (θ + φ)| :=
    intervalIntegral.integral_add (hcontm.intervalIntegrable _ _)
      (hcontp.intervalIntegrable _ _)
  have hsub : (∫ φ in (0 : ℝ)..π, |dirichletKernel N (θ - φ)|)
      = ∫ u in (θ - π)..θ, |dirichletKernel N u| := by
    rw [intervalIntegral.integral_comp_sub_left (fun u => |dirichletKernel N u|) θ, sub_zero]
  have hadd : (∫ φ in (0 : ℝ)..π, |dirichletKernel N (θ + φ)|)
      = ∫ u in θ..(θ + π), |dirichletKernel N u| := by
    rw [intervalIntegral.integral_comp_add_left (fun u => |dirichletKernel N u|) θ, add_zero]
  have hjoin : (∫ u in (θ - π)..θ, |dirichletKernel N u|)
      + (∫ u in θ..(θ + π), |dirichletKernel N u|)
      = ∫ u in (θ - π)..(θ + π), |dirichletKernel N u| :=
    intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
  have hshift : (∫ u in (θ - π)..(θ + π), |dirichletKernel N u|)
      = ∫ u in (-π)..π, |dirichletKernel N u| := by
    have h := hper.intervalIntegral_add_eq (θ - π) (-π)
    rw [show θ - π + 2 * π = θ + π by ring, show -π + 2 * π = π by ring] at h
    exact h
  rw [lebesgueConstant]
  have hle : (∫ φ in (0 : ℝ)..π, |dirichletKernel N (θ - φ) + dirichletKernel N (θ + φ)|)
      ≤ ∫ u in (-π)..π, |dirichletKernel N u| := by
    rw [← hshift, ← hjoin, ← hsub, ← hadd, ← hsplit]
    exact hmono
  exact mul_le_mul_of_nonneg_left hle (by positivity)

/-- At $\theta = 0$, that is at $x = 1$, the Lebesgue function of the Chebyshev projection equals
the Lebesgue constant:
$$\frac{1}{\pi} \int_0^\pi \bigl|D_N(0 - \varphi) + D_N(0 + \varphi)\bigr| \, d\varphi = L_N.$$
-/
theorem integral_abs_chebyshevKernel_zero (N : ℕ) :
    (1 / π * ∫ φ in (0 : ℝ)..π, |dirichletKernel N (0 - φ) + dirichletKernel N (0 + φ)|)
      = lebesgueConstant N := by
  have hval : ∀ φ : ℝ, |dirichletKernel N (0 - φ) + dirichletKernel N (0 + φ)|
      = 2 * |dirichletKernel N φ| := by
    intro φ
    rw [zero_sub, zero_add, dirichletKernel_neg, ← two_mul, abs_mul]
    norm_num
  rw [intervalIntegral.integral_congr fun φ _ => hval φ, intervalIntegral.integral_const_mul,
    lebesgueConstant_eq]
  ring

/-- **The norm of the Chebyshev least-squares projection.** For every $N$, the operator norm of the
Chebyshev least-squares projection $P_N$ on $C[-1, 1]$ is exactly the $N$-th Lebesgue constant
of the Fourier projection:
$$\|P_N\| = L_N = \frac{1}{\pi} \int_{-\pi}^{\pi} |D_N(s)| \, ds.$$
This is Example 3.7.4 of [han2009theoretical].

The Lebesgue constant is `PeriodicCont.lebesgueConstant`. The change of variables
$x = \cos\theta$, $t = \cos\varphi$ turns the kernel into $\frac{1}{\pi}[D_N(\theta - \varphi) +
D_N(\theta + \varphi)]$ (`Approximation.chebyshevKernel_cos`) and the row integral into
$\frac{1}{\pi} \int_0^\pi |D_N(\theta - \varphi) + D_N(\theta + \varphi)| \, d\varphi$. This
integral is largest at $\theta = 0$, where it is $\frac{2}{\pi} \int_0^\pi |D_N| = L_N$. -/
theorem norm_chebyshevProj (N : ℕ) : ‖chebyshevProj N‖ = lebesgueConstant N := by
  have : Nonempty (Set.Icc (-1 : ℝ) 1) := ⟨⟨1, by norm_num⟩⟩
  have hrow : ∀ x : Set.Icc (-1 : ℝ) 1,
      (∫ t, |∑ i : Fin (N + 1), chebyshevOrthonormal i x * chebyshevOrthonormal i t|
        ∂chebyshevMeasureIcc)
        = 1 / π * ∫ φ in (0 : ℝ)..π,
            |dirichletKernel N (arccos (x : ℝ) - φ) + dirichletKernel N (arccos (x : ℝ) + φ)| := by
    intro x
    have hx : cos (arccos (x : ℝ)) = (x : ℝ) := cos_arccos x.2.1 x.2.2
    simp only [sum_chebyshevOrthonormal_mul]
    rw [← integral_abs_chebyshevKernel N (arccos (x : ℝ))]
    simp only [hx]
  have hle : ∀ x : Set.Icc (-1 : ℝ) 1,
      (∫ t, |∑ i : Fin (N + 1), chebyshevOrthonormal i x * chebyshevOrthonormal i t|
        ∂chebyshevMeasureIcc) ≤ lebesgueConstant N := fun x => by
    rw [hrow x]
    exact integral_abs_chebyshevKernel_le N _
  have heq : (∫ t, |∑ i : Fin (N + 1),
      chebyshevOrthonormal i (⟨1, by norm_num⟩ : Set.Icc (-1 : ℝ) 1) *
        chebyshevOrthonormal i t| ∂chebyshevMeasureIcc) = lebesgueConstant N := by
    rw [hrow ⟨1, by norm_num⟩]
    simp only [arccos_one]
    exact integral_abs_chebyshevKernel_zero N
  rw [chebyshevProj, norm_expansionCLM]
  refine le_antisymm (ciSup_le hle) ?_
  rw [← heq]
  exact le_ciSup ⟨lebesgueConstant N, by rintro _ ⟨x, rfl⟩; exact hle x⟩ _

end Chebyshev

end Approximation
