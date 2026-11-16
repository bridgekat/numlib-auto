/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Approximation.Interpolation
import Numlib.Approximation.Trigonometric

/-!
# The Dirichlet-kernel form of trigonometric interpolation

Let $\mathcal{I}_n$ be trigonometric interpolation at the $2n + 1$ equispaced nodes
$x_j = 2\pi j / (2n + 1)$, $j = 0, \dots, 2n$, of a period: it maps a continuous $2\pi$-periodic
function $f$ to the unique trigonometric polynomial of degree at most $n$ that agrees with $f$ at
the nodes. This file shows that the cardinal functions of $\mathcal{I}_n$ are translates of the
Dirichlet kernel $D_n(t) = 1/2 + \sum_{k=1}^n \cos(kt)$, as in (3.7.19) and Exercise 3.7.5 of
[han2009theoretical]:
$$\mathcal{I}_n f(x) = \frac{2}{2n + 1} \sum_{j=0}^{2n} f(x_j)\, D_n(x - x_j).$$
So $\mathcal{I}_n$ is the discrete analogue of the Fourier projection: the Fourier projection
integrates $f$ against $D_n(y - x) / \pi$, and $\mathcal{I}_n$ averages $f$ against
$2 D_n(x - x_j) / (2n + 1)$ over the nodes.

The operator norm of $\mathcal{I}_n$ on the continuous periodic functions is therefore the largest
value of the Lebesgue function $\Lambda_n(x) = \frac{2}{2n + 1} \sum_j |D_n(x - x_j)|$. The file
proves the bound $\|\mathcal{I}_n\| \le 2 + (2/\pi) \log(2n + 1)$, and the Lebesgue lemma $\|f -
\mathcal{I}_n f\|_\infty \le (1 + \|\mathcal{I}_n\|) \operatorname{dist}(f, \mathcal{T}_n)$, where
$\mathcal{T}_n$ is the space of trigonometric polynomials of degree at most $n$.

## Main definitions

* `PeriodicCont.dirichletShiftCM`: the shifted Dirichlet kernel $D_n(\cdot - a)$ as a continuous
  function on the circle.

## Main results

* `norm_sub_trigInterpCLM_le`: the Lebesgue lemma $\|f - \mathcal{I}_n f\|_\infty \le (1 +
  \|\mathcal{I}_n\|) \operatorname{dist}(f, \mathcal{T}_n)$, for any period $T > 0$.
* `PeriodicCont.dirichletShiftCM_mem_trigPolyLE`: $D_n(\cdot - a)$ is a trigonometric polynomial of
  degree at most $n$.
* `PeriodicCont.dirichletKernel_node_sub`: $D_n(x_k - x_j)$ is $(2n + 1)/2$ for $j = k$ and $0$
  otherwise.
* `PeriodicCont.trigInterpCLM_eq_sum_dirichletShiftCM`, `PeriodicCont.trigInterpCLM_coe_apply`: the
  Lagrange formula $\mathcal{I}_n f = \frac{2}{2n + 1} \sum_j f(x_j)\, D_n(\cdot - x_j)$, on the
  circle and pointwise on $\mathbb{R}$.
* `PeriodicCont.cardinalBasisCM_trigInterpNode`: the cardinal functions of $\mathcal{I}_n$ are
  $2 D_n(\cdot - x_j) / (2n + 1)$.
* `PeriodicCont.isGreatest_norm_trigInterpCLM`: $\|\mathcal{I}_n\|$ is the largest value of the
  Lebesgue function $\Lambda_n$.
* `norm_trigInterpCLM_le`: $\|\mathcal{I}_n\| \le 2 + (2/\pi) \log(2n + 1)$.
* `le_norm_trigInterpCLM_one`: $\|\mathcal{I}_1\| \ge 5/3$.

## Proof outline

The shifted kernel $D_n(\cdot - a)$ is a trigonometric polynomial of degree at most $n$ by the
addition formula for the cosine. At the differences of the nodes, $D_n(x_k - x_j)$ is $(2n + 1)/2$
for $j = k$ and $0$ otherwise, because $(n + 1/2)(x_k - x_j)$ is an integer multiple of $\pi$ and
$(x_k - x_j)/2$ is not. So the functions $2 D_n(\cdot - x_j) / (2n + 1)$ are the cardinal functions,
and the Lagrange formula and the norm formula follow from the general theory of
`Numlib.Approximation.Unisolvent`.

## Notation

* $\mathcal{I}_n$: the interpolation projection `trigInterpCLM (2 * π) n` of
  `Numlib.Approximation.Interpolation`.
* $x_j$: the node `trigInterpNode (2 * π) n j`, the class of $2\pi j / (2n + 1)$ on the circle.

## Implementation notes

* The bound of (3.7.20) of [han2009theoretical] is printed as
  $\|\mathcal{I}_n\| \le 1 + (2/\pi) \log n$. As printed it is false: $\|\mathcal{I}_1\| \ge 5/3$
  (`le_norm_trigInterpCLM_one`). The file proves `norm_trigInterpCLM_le`, which has the sharp
  coefficient $2/\pi$ but the additive constant $2$; the doc comment of `norm_trigInterpCLM_le`
  explains the difference.
* The logarithmic estimate is `SineSum.sum_term_le` of `Numlib.Analysis.SpecialFunctions.SineSum`,
  with $M = 2n + 1$.
-/

open Set

open scoped Real

/-! ### The Lebesgue lemma for the interpolation projection -/

/-- **The Lebesgue lemma for trigonometric interpolation.** Let $T > 0$, and let $\mathcal{I}_n$ be
interpolation at the $2n + 1$ equispaced nodes $jT / (2n + 1)$ of a period by trigonometric
polynomials of degree at most $n$. For every continuous $T$-periodic function $f$,
$$\|f - \mathcal{I}_n f\|_\infty \le (1 + \|\mathcal{I}_n\|) \operatorname{dist}(f,
  \mathcal{T}_n),$$
where $\mathcal{T}_n$ is the space `trigPolyLE T n` of trigonometric polynomials of degree at
most $n$.

This is the abstract Lebesgue lemma `norm_sub_apply_le_of_isIdempotentElem` for the projection
`trigInterpCLM T n`. With a bound on the best approximation error, such as Jackson's theorem, it
gives the uniform convergence rate of trigonometric interpolation. -/
theorem norm_sub_trigInterpCLM_le {T : ℝ} [Fact (0 < T)] (n : ℕ) (f : C(AddCircle T, ℝ)) :
    ‖f - trigInterpCLM T n f‖
      ≤ (1 + ‖trigInterpCLM T n‖) *
        Metric.infDist f (trigPolyLE T n : Set C(AddCircle T, ℝ)) := by
  have h := norm_sub_apply_le_of_isIdempotentElem (trigInterpCLM T n)
    isIdempotentElem_trigInterpCLM f
  rwa [range_trigInterpCLM] at h

namespace PeriodicCont

variable {n : ℕ}

/-! ### The shifted Dirichlet kernel -/

/-- The **shifted Dirichlet kernel**: for a real number $a$, the continuous function
$x \mapsto D_n(x - a)$ on the circle of circumference $2\pi$. Its shifts by the $2n + 1$
equispaced nodes, multiplied by $2 / (2n + 1)$, are the cardinal functions of trigonometric
interpolation (`PeriodicCont.cardinalBasisCM_trigInterpNode`). -/
noncomputable def dirichletShiftCM (n : ℕ) (a : ℝ) : C(AddCircle (2 * π), ℝ) :=
  (dirichletCM n).comp ⟨fun x => x - (a : AddCircle (2 * π)), by fun_prop⟩

/-- For real numbers $a$ and $t$, the shifted Dirichlet kernel `PeriodicCont.dirichletShiftCM n a`
at the point $t$ of the circle is $D_n(t - a)$. -/
@[simp]
theorem dirichletShiftCM_coe (n : ℕ) (a t : ℝ) :
    dirichletShiftCM n a ↑t = dirichletKernel n (t - a) := by
  have hsub : ((↑t : AddCircle (2 * π)) - ↑a) = ((t - a : ℝ) : AddCircle (2 * π)) := rfl
  rw [dirichletShiftCM]
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, hsub, dirichletCM_coe]

/-- **The shifted Dirichlet kernel is a trigonometric polynomial of degree at most $n$.** For every
real number $a$, the function $D_n(\cdot - a)$ lies in $\mathcal{T}_n$, the space
`trigPolyLE (2 * π) n`.

The addition formula $\cos(m(t - a)) = \cos(ma) \cos(mt) + \sin(ma) \sin(mt)$ expands it in the
real trigonometric system. -/
theorem dirichletShiftCM_mem_trigPolyLE (n : ℕ) (a : ℝ) :
    dirichletShiftCM n a ∈ trigPolyLE (2 * π) n := by
  have h2 : (√2 : ℝ) ≠ 0 := by positivity
  set q : C(AddCircle (2 * π), ℝ) :=
    (2 : ℝ)⁻¹ • trigFun (2 * π) 0
      + (∑ m ∈ Finset.Icc 1 n, ((√2)⁻¹ * Real.cos (m * a)) • trigFun (2 * π) (m : ℤ)
        + ∑ m ∈ Finset.Icc 1 n, ((√2)⁻¹ * Real.sin (m * a)) • trigFun (2 * π) (-(m : ℤ)))
    with hq
  have hmem : q ∈ trigPolyLE (2 * π) n := by
    refine Submodule.add_mem _
      (Submodule.smul_mem _ _ (trigFun_mem_trigPolyLE (by simp)))
      (Submodule.add_mem _ (Submodule.sum_mem _ fun m hm => ?_)
        (Submodule.sum_mem _ fun m hm => ?_))
    · exact Submodule.smul_mem _ _ (trigFun_mem_trigPolyLE (by
        simpa using (Finset.mem_Icc.1 hm).2))
    · exact Submodule.smul_mem _ _ (trigFun_mem_trigPolyLE (by
        simpa using (Finset.mem_Icc.1 hm).2))
  have heq : dirichletShiftCM n a = q := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | _ t =>
      have hterm : ∀ m ∈ Finset.Icc 1 n,
          ((√2)⁻¹ * Real.cos (m * a)) * trigFun (2 * π) (m : ℤ) ↑t
            + ((√2)⁻¹ * Real.sin (m * a)) * trigFun (2 * π) (-(m : ℤ)) ↑t
            = Real.cos (m * (t - a)) := by
        intro m hm
        have hm0 : (0 : ℤ) < (m : ℤ) := by
          have := (Finset.mem_Icc.1 hm).1; omega
        rw [trigFun_coe_of_pos hm0, trigFun_coe_of_neg (by omega : (-(m : ℤ)) < 0)]
        push_cast
        rw [neg_neg, mul_sub, Real.cos_sub]
        field_simp
      rw [dirichletShiftCM_coe, dirichletKernel_apply, hq]
      simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.coe_sum,
        Finset.sum_apply, smul_eq_mul, trigFun_zero, ContinuousMap.one_apply, mul_one,
        ← Finset.sum_add_distrib]
      rw [Finset.sum_congr rfl hterm]
      norm_num
  rw [heq]
  exact hmem

/-! ### The kernel at the differences of the equispaced nodes -/

/-- **The Dirichlet kernel at the differences of the equispaced nodes.** For an integer $d$ with
$|d| \le 2n$,
$$D_n\Bigl(\frac{2\pi d}{2n + 1}\Bigr) = \begin{cases} (2n + 1)/2, & d = 0, \\ 0, & d \neq 0.
  \end{cases}$$

For $d \neq 0$ the value vanishes because $(n + 1/2) \cdot 2\pi d / (2n + 1) = \pi d$ is an
integer multiple of $\pi$ and $\pi d / (2n + 1)$ is not. This makes the functions
$2 D_n(\cdot - x_j) / (2n + 1)$ the cardinal functions of trigonometric interpolation. -/
theorem dirichletKernel_node_sub (n : ℕ) (d : ℤ) (hd : d.natAbs ≤ 2 * n) :
    dirichletKernel n (2 * π * d / (2 * n + 1))
      = if d = 0 then (2 * (n : ℝ) + 1) / 2 else 0 := by
  rcases eq_or_ne d 0 with rfl | hd0
  · have h0 : 2 * π * ((0 : ℤ) : ℝ) / (2 * (n : ℝ) + 1) = 0 := by simp
    rw [ite_eq_left rfl, h0, dirichletKernel_apply]
    simp only [mul_zero, Real.cos_zero, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
      nsmul_eq_mul, mul_one]
    ring
  · rw [ite_eq_right hd0]
    have hhalf : 2 * π * (d : ℝ) / (2 * (n : ℝ) + 1) / 2 = π * d / (2 * (n : ℝ) + 1) := by
      field_simp
    have hsin : Real.sin (2 * π * (d : ℝ) / (2 * (n : ℝ) + 1) / 2) ≠ 0 := by
      rw [hhalf]
      intro hzero
      obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.1 hzero
      have hk' : (k : ℝ) * (2 * (n : ℝ) + 1) = (d : ℝ) := by
        refine mul_left_cancel₀ Real.pi_ne_zero ?_
        rw [show π * ((k : ℝ) * (2 * (n : ℝ) + 1)) = ((k : ℝ) * π) * (2 * (n : ℝ) + 1) by ring,
          hk]
        field_simp
      have hkz : k * (2 * (n : ℤ) + 1) = d := by exact_mod_cast hk'
      have hkne : k ≠ 0 := by
        rintro rfl
        simp at hkz
        exact hd0 hkz.symm
      have hnat : d.natAbs = k.natAbs * (2 * n + 1) := by
        have habs : (2 * (n : ℤ) + 1).natAbs = 2 * n + 1 := by omega
        rw [← hkz, Int.natAbs_mul, habs]
      have hk1 : 1 ≤ k.natAbs := Int.natAbs_pos.2 hkne
      have hbig : 2 * n + 1 ≤ d.natAbs := by
        rw [hnat]
        calc 2 * n + 1 = 1 * (2 * n + 1) := by ring
          _ ≤ k.natAbs * (2 * n + 1) := Nat.mul_le_mul_right _ hk1
      omega
    rw [dirichletKernel_eq_sin_div hsin]
    have harg : ((n : ℝ) + 1 / 2) * (2 * π * (d : ℝ) / (2 * (n : ℝ) + 1)) = (d : ℝ) * π := by
      field_simp
    rw [harg, Real.sin_int_mul_pi, zero_div]

/-! ### The Lagrange formula for the interpolation projection -/

/-- For nodes $x_j$ and $x_k$ with $j, k \in \{0, \dots, 2n\}$, the shifted Dirichlet kernel takes
the value
$$D_n(x_k - x_j) = \begin{cases} (2n + 1)/2, & j = k, \\ 0, & j \neq k. \end{cases}$$
So the functions $2 D_n(\cdot - x_j) / (2n + 1)$ are the cardinal functions of the interpolation
problem. -/
theorem dirichletShiftCM_apply_node (n : ℕ) (j k : Fin (2 * n + 1)) :
    dirichletShiftCM n ((j : ℕ) * (2 * π) / (2 * n + 1)) (trigInterpNode (2 * π) n k)
      = if j = k then (2 * (n : ℝ) + 1) / 2 else 0 := by
  have hsub : ((k : ℕ) : ℝ) * (2 * π) / (2 * (n : ℝ) + 1)
      - ((j : ℕ) : ℝ) * (2 * π) / (2 * (n : ℝ) + 1)
      = 2 * π * (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) / (2 * (n : ℝ) + 1) := by
    push_cast
    ring
  rw [trigInterpNode, dirichletShiftCM_coe, hsub, dirichletKernel_node_sub n _ ?_]
  · congr 1
    simp only [eq_iff_iff, sub_eq_zero]
    constructor
    · intro h
      exact Fin.ext (by exact_mod_cast h.symm)
    · rintro rfl
      rfl
  · have hj : (j : ℕ) ≤ 2 * n := by omega
    have hk : (k : ℕ) ≤ 2 * n := by omega
    omega


/-- **The Lagrange formula for trigonometric interpolation.** For every continuous $2\pi$-periodic
function $f$,
$$\mathcal{I}_n f = \frac{2}{2n + 1} \sum_{j=0}^{2n} f(x_j)\, D_n(\cdot - x_j),$$
as an identity of continuous functions on the circle.

This is (3.7.19) of [han2009theoretical]. The function $D_n(\cdot - x_j)$ is
`PeriodicCont.dirichletShiftCM n (j * (2 * π) / (2 * n + 1))`. -/
theorem trigInterpCLM_eq_sum_dirichletShiftCM (n : ℕ) (f : C(AddCircle (2 * π), ℝ)) :
    trigInterpCLM (2 * π) n f
      = (2 / (2 * (n : ℝ) + 1)) •
        ∑ j : Fin (2 * n + 1),
          f (trigInterpNode (2 * π) n j) •
            dirichletShiftCM n ((j : ℕ) * (2 * π) / (2 * n + 1)) := by
  refine (eq_trigInterpCLM ?_ ?_).symm
  · exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (dirichletShiftCM_mem_trigPolyLE n _))
  · intro k
    simp only [ContinuousMap.smul_apply, ContinuousMap.coe_sum, Finset.sum_apply,
      smul_eq_mul, dirichletShiftCM_apply_node]
    rw [Finset.sum_eq_single k (fun j _ hj => by simp [hj])
      (fun h => absurd (Finset.mem_univ k) h), ite_eq_left rfl]
    field_simp

/-- **The Lagrange formula for trigonometric interpolation**, pointwise on $\mathbb{R}$. For every
continuous $2\pi$-periodic function $f$ and every real number $x$,
$$\mathcal{I}_n f(x) = \frac{2}{2n + 1} \sum_{j=0}^{2n} D_n(x - x_j)\, f(x_j), \qquad x_j =
  \frac{2\pi j}{2n + 1}.$$

This is (3.7.19) of [han2009theoretical]. -/
theorem trigInterpCLM_coe_apply (n : ℕ) (f : C(AddCircle (2 * π), ℝ)) (x : ℝ) :
    trigInterpCLM (2 * π) n f ↑x
      = 2 / (2 * (n : ℝ) + 1) *
        ∑ j : Fin (2 * n + 1),
          dirichletKernel n (x - (j : ℕ) * (2 * π) / (2 * n + 1)) *
            f (trigInterpNode (2 * π) n j) := by
  rw [trigInterpCLM_eq_sum_dirichletShiftCM]
  simp only [ContinuousMap.smul_apply, ContinuousMap.coe_sum, Finset.sum_apply, smul_eq_mul,
    dirichletShiftCM_coe]
  exact congrArg _ (Finset.sum_congr rfl fun j _ => mul_comm _ _)

/-! ### The Lebesgue function of trigonometric interpolation -/

/-- **The cardinal functions of trigonometric interpolation.** For $j \in \{0, \dots, 2n\}$, the
$j$-th cardinal function of interpolation by trigonometric polynomials of degree at most $n$ at
the equispaced nodes $x_0, \dots, x_{2n}$ is
$$\varphi_j = \frac{2}{2n + 1} D_n(\cdot - x_j).$$

This is Exercise 3.7.5 of [han2009theoretical]. The cardinal function is
`Approximation.IsUnisolvent.cardinalBasisCM` for the unisolvence `isUnisolvent_trigPolyLE`. The
proof checks that the right side lies in $\mathcal{T}_n$ and takes the value $1$ at $x_j$ and
$0$ at the other nodes; the interpolation problem has only one such solution. -/
theorem cardinalBasisCM_trigInterpNode (n : ℕ) (j : Fin (2 * n + 1)) :
    (isUnisolvent_trigPolyLE (2 * π) (injective_trigInterpNode (2 * π) n)).cardinalBasisCM j
      = (2 / (2 * (n : ℝ) + 1)) • dirichletShiftCM n ((j : ℕ) * (2 * π) / (2 * n + 1)) := by
  set h := isUnisolvent_trigPolyLE (2 * π) (injective_trigInterpNode (2 * π) n) with hh
  have hmem : (2 / (2 * (n : ℝ) + 1)) • dirichletShiftCM n ((j : ℕ) * (2 * π) / (2 * n + 1))
      ∈ trigPolyLE (2 * π) n :=
    Submodule.smul_mem _ _ (dirichletShiftCM_mem_trigPolyLE n _)
  have hval : ∀ k, ((⟨_, hmem⟩ : trigPolyLE (2 * π) n) : C(AddCircle (2 * π), ℝ))
      (trigInterpNode (2 * π) n k)
      = (Pi.single j 1 : Fin (2 * n + 1) → ℝ) k := by
    intro k
    simp only [ContinuousMap.smul_apply, smul_eq_mul, dirichletShiftCM_apply_node, Pi.single_apply]
    by_cases hjk : j = k
    · subst hjk
      simp only [↓reduceIte]
      field_simp
    · simp [hjk, Ne.symm hjk]
  have hfin := h.eq_interpolate (u := ⟨_, hmem⟩) hval
  rw [Approximation.IsUnisolvent.cardinalBasisCM]
  exact (congrArg Subtype.val hfin).symm

/-- **The Lebesgue constant of trigonometric interpolation.** The operator norm of $\mathcal{I}_n$,
for the supremum norm on the continuous $2\pi$-periodic functions, is the largest value of the
Lebesgue function
$$\Lambda_n(t) = \frac{2}{2n + 1} \sum_{j=0}^{2n} |D_n(t - x_j)|, \qquad t \in \mathbb{R},$$
and the largest value is attained.

The bound of Rivlin in (3.7.20) of [han2009theoretical] is a bound on this maximum; see
`norm_trigInterpCLM_le` for the bound proved here. The proof specializes
`Approximation.IsUnisolvent.isGreatest_norm_interpCLM` with the cardinal functions of
`PeriodicCont.cardinalBasisCM_trigInterpNode`. -/
theorem isGreatest_norm_trigInterpCLM (n : ℕ) :
    IsGreatest
      (Set.range fun t : ℝ => 2 / (2 * (n : ℝ) + 1) *
        ∑ j : Fin (2 * n + 1),
          |dirichletKernel n (t - (j : ℕ) * (2 * π) / (2 * n + 1))|)
      ‖trigInterpCLM (2 * π) n‖ := by
  have hN : (0 : ℝ) ≤ 2 / (2 * (n : ℝ) + 1) := by positivity
  have h := (isUnisolvent_trigPolyLE (2 * π)
    (injective_trigInterpNode (2 * π) n)).isGreatest_norm_interpCLM
  have hfun : ∀ x : AddCircle (2 * π),
      ∑ j : Fin (2 * n + 1),
          |(isUnisolvent_trigPolyLE (2 * π)
            (injective_trigInterpNode (2 * π) n)).cardinalBasisCM j x|
        = 2 / (2 * (n : ℝ) + 1) *
          ∑ j : Fin (2 * n + 1), |dirichletShiftCM n ((j : ℕ) * (2 * π) / (2 * n + 1)) x| := by
    intro x
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [cardinalBasisCM_trigInterpNode, ContinuousMap.smul_apply, smul_eq_mul, abs_mul,
      abs_of_nonneg hN]
  simp only [hfun] at h
  have hrange : (Set.range fun x : AddCircle (2 * π) => 2 / (2 * (n : ℝ) + 1) *
        ∑ j : Fin (2 * n + 1), |dirichletShiftCM n ((j : ℕ) * (2 * π) / (2 * n + 1)) x|)
      = Set.range fun t : ℝ => 2 / (2 * (n : ℝ) + 1) *
        ∑ j : Fin (2 * n + 1),
          |dirichletKernel n (t - (j : ℕ) * (2 * π) / (2 * n + 1))| := by
    refine Set.ext fun y => ⟨?_, ?_⟩
    · rintro ⟨x, rfl⟩
      induction x using QuotientAddGroup.induction_on with
      | _ t => exact ⟨t, by simp only [dirichletShiftCM_coe]⟩
    · rintro ⟨t, rfl⟩
      exact ⟨(t : AddCircle (2 * π)), by simp only [dirichletShiftCM_coe]⟩
  rwa [hrange] at h

end PeriodicCont

/-! ### Rivlin's bound for the Lebesgue constant -/

/-- **Rivlin's bound for the Lebesgue constant of trigonometric interpolation**, with the additive
constant $2$: for every natural number $n$,
$$\|\mathcal{I}_n\| \le 2 + \frac{2}{\pi} \log(2n + 1).$$

Section 3.7 of [han2009theoretical] prints the bound $\|\mathcal{I}_n\| \le 1 + (2/\pi) \log n$
for $n \ge 1$ in (3.7.20), quoting Rivlin. As printed this bound is false: at $n = 1$ the
Lebesgue function takes the value $5/3$ at the midpoint of two nodes, and the right side is $1$
(`le_norm_trigInterpCLM_one`). In the bound of Rivlin, $n$ is the number of nodes, here
$2n + 1$, and the sharp statement is $\|\mathcal{I}_n\| \le 1 + (2/\pi) \log(2n + 1)$. Its two
sides differ by about $0.04$ for every $n$. The bound here keeps the sharp coefficient $2/\pi$,
so it gives the growth $O(\log n)$ that the convergence rate (3.7.22) uses, but it has a larger
additive constant: one unit for each of the two nodes nearest the evaluation point.

The estimate is `SineSum.sum_term_le` of `Numlib.Analysis.SpecialFunctions.SineSum`: for
$M \ge 3$, $0 \le \delta < 1$ and an integer $c$, it bounds $\sum_{i < M} |\sin(\pi(c + i +
\delta))| / (M |\sin(\pi(c + i + \delta)/M)|)$ by $2 + (2/\pi) \log M$. Write $M = 2n + 1$ and
the evaluation point as $x = 2\pi(c_0 + \delta)/M$ with $0 \le \delta < 1$. The closed form
$2 \sin(u/2) D_n(u) = \sin(Mu/2)$ turns each term of the Lebesgue function into $(2/M) |D_n(x -
x_j)| = |\sin(\pi(c + \delta))| / (M |\sin(\pi(c + \delta)/M)|)$ with $c = c_0 - j$, and these
$M$ indices $c$ are consecutive. This fails only for $\delta = 0$, when $x$ is a node; there
every term but one vanishes and the Lebesgue function is $1$. For $n = 0$ the bound reads
$\|\mathcal{I}_0\| \le 2$, and the Lebesgue function is $1$. -/
theorem norm_trigInterpCLM_le (n : ℕ) :
    ‖trigInterpCLM (2 * π) n‖ ≤ 2 + 2 / π * Real.log (2 * (n : ℝ) + 1) := by
  have hpi := Real.pi_pos
  obtain ⟨t, ht⟩ := (PeriodicCont.isGreatest_norm_trigInterpCLM n).1
  rw [← ht]
  simp only []
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, mul_zero, zero_add, Real.log_one, mul_zero, add_zero,
      dirichletKernel_zero]
    norm_num
  set M : ℕ := 2 * n + 1 with hMdef
  have hM3 : 3 ≤ M := by omega
  have hMr : ((M : ℕ) : ℝ) = 2 * (n : ℝ) + 1 := by rw [hMdef]; push_cast; ring
  have hM0 : (0 : ℝ) < (M : ℝ) := by rw [hMr]; positivity
  have hMne : (M : ℝ) ≠ 0 := hM0.ne'
  have hlogM : 0 ≤ Real.log (M : ℝ) := by
    refine Real.log_nonneg ?_
    rw [hMr]
    linarith
  rw [← hMr]
  -- write the evaluation point as `2 π (c₀ + δ) / M` with `0 ≤ δ < 1`
  set s : ℝ := (M : ℝ) * t / (2 * π) with hs
  set c0 : ℤ := ⌊s⌋ with hc0
  set δ : ℝ := Int.fract s with hδ
  have hδ0 : 0 ≤ δ := Int.fract_nonneg _
  have hδ1 : δ < 1 := Int.fract_lt_one _
  have hsval : (c0 : ℝ) + δ = s := Int.floor_add_fract s
  have harg : ∀ j : ℕ, t - (j : ℝ) * (2 * π) / (M : ℝ)
      = 2 * π * (((c0 - (j : ℤ) : ℤ) : ℝ) + δ) / (M : ℝ) := by
    intro j
    have hts : t = 2 * π * s / (M : ℝ) := by rw [hs]; field_simp
    push_cast
    rw [hts, ← hsval]
    field_simp
    ring
  -- the closed form of the kernel in the shifted variable
  have hhalf : ∀ z : ℝ, 2 * π * z / (M : ℝ) / 2 = π * z / (M : ℝ) := fun z => by ring
  have hkernel : ∀ z : ℝ, 2 * Real.sin (π * z / (M : ℝ)) * dirichletKernel n (2 * π * z / (M : ℝ))
      = Real.sin (π * z) := by
    intro z
    have h := two_mul_sin_half_mul_dirichletKernel n (2 * π * z / (M : ℝ))
    rw [hhalf] at h
    rw [h]
    congr 1
    rw [hMr]
    field_simp
  have hsinzero : ∀ z : ℝ, Real.sin (π * z / (M : ℝ)) = 0 → ∃ l : ℤ, z = (l : ℝ) * (M : ℝ) := by
    intro z hz
    rw [Real.sin_eq_zero_iff] at hz
    obtain ⟨l, hl⟩ := hz
    refine ⟨l, ?_⟩
    have h1 : π * ((l : ℝ) * (M : ℝ)) = π * z := by
      have h2 : (l : ℝ) * π * (M : ℝ) = π * z / (M : ℝ) * (M : ℝ) := by rw [hl]
      rw [div_mul_cancel₀ _ hMne] at h2
      linarith
    exact (mul_left_cancel₀ hpi.ne' h1).symm
  by_cases hd : δ = 0
  · -- the evaluation point is a node: only the term at that node survives
    have hj0 : ((c0 % (M : ℤ)).toNat) < M := by
      have h1 : 0 ≤ c0 % (M : ℤ) := Int.emod_nonneg _ (by exact_mod_cast (by omega : M ≠ 0))
      have h2 : c0 % (M : ℤ) < (M : ℤ) :=
        Int.emod_lt_of_pos _ (by exact_mod_cast (by omega : 0 < M))
      omega
    have hzero : ∀ j : Fin M, j ≠ ⟨_, hj0⟩ →
        |dirichletKernel n (t - ((j : ℕ) : ℝ) * (2 * π) / (M : ℝ))| = 0 := by
      intro j hj
      rw [harg]
      set c : ℤ := c0 - ((j : ℕ) : ℤ) with hc
      have hnd : ¬ ((M : ℤ) ∣ c) := by
        intro hdvd
        have hmod : ((j : ℕ) : ℤ) % (M : ℤ) = c0 % (M : ℤ) :=
          Int.modEq_iff_dvd.mpr (by rw [← hc]; exact hdvd)
        have hjm : ((j : ℕ) : ℤ) % (M : ℤ) = ((j : ℕ) : ℤ) :=
          Int.emod_eq_of_lt (by positivity) (by exact_mod_cast j.2)
        refine hj (Fin.ext ?_)
        have hv : ((j : ℕ) : ℤ) = c0 % (M : ℤ) := by rw [← hjm, hmod]
        simp only []
        omega
      have hsin : Real.sin (π * ((c : ℝ) + δ) / (M : ℝ)) ≠ 0 := by
        intro h
        obtain ⟨l, hl⟩ := hsinzero _ h
        refine hnd ⟨l, ?_⟩
        have hml : (c : ℝ) = (M : ℝ) * (l : ℝ) := by rw [hd] at hl; linarith [hl]
        exact_mod_cast hml
      have hnum : Real.sin (π * ((c : ℝ) + δ)) = 0 := by
        rw [hd, add_zero, Real.sin_eq_zero_iff]
        exact ⟨c, by ring⟩
      have hval : dirichletKernel n (2 * π * ((c : ℝ) + δ) / (M : ℝ)) = 0 := by
        have h := hkernel ((c : ℝ) + δ)
        rw [hnum] at h
        rcases mul_eq_zero.1 h with h' | h'
        · exact absurd (by rcases mul_eq_zero.1 h' with h'' | h'' <;>
            [norm_num at h''; exact h'']) hsin
        · exact h'
      rw [hval, abs_zero]
    have hone : ∑ j : Fin M, |dirichletKernel n (t - ((j : ℕ) : ℝ) * (2 * π) / (M : ℝ))|
        = |dirichletKernel n (t - (((c0 % (M : ℤ)).toNat : ℕ) : ℝ) * (2 * π) / (M : ℝ))| :=
      Finset.sum_eq_single_of_mem (⟨_, hj0⟩ : Fin M) (Finset.mem_univ _)
        (fun j _ hj => hzero j hj)
    rw [hone]
    have hb := abs_dirichletKernel_le n
      (t - (((c0 % (M : ℤ)).toNat : ℕ) : ℝ) * (2 * π) / (M : ℝ))
    have hMhalf : 2 / (M : ℝ) * ((n : ℝ) + 1 / 2) = 1 := by rw [hMr]; field_simp
    have h2M : (0 : ℝ) < 2 / (M : ℝ) := by positivity
    have h1 := mul_le_mul_of_nonneg_left hb h2M.le
    have h2 : 0 ≤ 2 / π * Real.log (M : ℝ) := mul_nonneg (by positivity) hlogM
    linarith
  · -- a generic point: every term is a `SineSum.term`
    have hterm : ∀ j : ℕ, 2 / (M : ℝ) *
        |dirichletKernel n (t - (j : ℝ) * (2 * π) / (M : ℝ))|
        = SineSum.term M δ (c0 - (j : ℤ)) := by
      intro j
      set c : ℤ := c0 - (j : ℤ) with hc
      have hsin : Real.sin (π * ((c : ℝ) + δ) / (M : ℝ)) ≠ 0 := by
        intro h
        obtain ⟨l, hl⟩ := hsinzero _ h
        have hint : δ = ((l * (M : ℤ) - c : ℤ) : ℝ) := by push_cast; linarith
        rcases lt_trichotomy (l * (M : ℤ) - c) 0 with h1 | h1 | h1
        · have h2 : ((l * (M : ℤ) - c : ℤ) : ℝ) < 0 := by exact_mod_cast h1
          linarith
        · exact hd (by rw [hint, h1]; norm_num)
        · have h2 : (1 : ℝ) ≤ ((l * (M : ℤ) - c : ℤ) : ℝ) := by exact_mod_cast h1
          linarith
      have habs : 2 * |Real.sin (π * ((c : ℝ) + δ) / (M : ℝ))|
          * |dirichletKernel n (2 * π * ((c : ℝ) + δ) / (M : ℝ))|
          = |Real.sin (π * ((c : ℝ) + δ))| := by
        have h := congrArg abs (hkernel ((c : ℝ) + δ))
        rwa [abs_mul, abs_mul, abs_two] at h
      rw [harg, ← hc, SineSum.term, eq_div_iff (by positivity)]
      field_simp
      nlinarith [habs]
    rw [Finset.mul_sum]
    have hsum : ∑ j : Fin M, 2 / (M : ℝ) *
        |dirichletKernel n (t - ((j : ℕ) : ℝ) * (2 * π) / (M : ℝ))|
        = ∑ i ∈ Finset.range M, SineSum.term M δ ((c0 - (M : ℤ) + 1) + i) := by
      rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => 2 / (M : ℝ) *
        |dirichletKernel n (t - (j : ℝ) * (2 * π) / (M : ℝ))|) M]
      rw [Finset.sum_congr rfl (fun j _ => hterm j)]
      rw [← Finset.sum_range_reflect (fun j : ℕ => SineSum.term M δ (c0 - (j : ℤ))) M]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjM : j < M := Finset.mem_range.1 hj
      congr 1
      have h1 : ((M - 1 - j : ℕ) : ℤ) = (M : ℤ) - 1 - j := by
        push_cast [Nat.cast_sub (by omega : j ≤ M - 1), Nat.cast_sub (by omega : 1 ≤ M)]
        ring
      rw [h1]
      ring
    rw [hsum]
    exact SineSum.sum_term_le hM3 hδ0 hδ1 _

/-- **The Lebesgue constant of trigonometric interpolation at three nodes is at least $5/3$**:
$\|\mathcal{I}_1\| \ge 5/3$. The Lebesgue function $\Lambda_1(x) = \frac{2}{3} \sum_j |D_1(x -
x_j)|$ takes the value $5/3$ at $x = \pi/3$, the midpoint of the nodes $0$ and $2\pi/3$.

This shows that the bound $1 + (2/\pi) \log n$ printed in (3.7.20) of [han2009theoretical] is
false: at $n = 1$ its right side is $1$. -/
theorem le_norm_trigInterpCLM_one : 5 / 3 ≤ ‖trigInterpCLM (2 * π) 1‖ := by
  have hD : ∀ t : ℝ, dirichletKernel 1 t = 1 / 2 + Real.cos t := by
    intro t
    rw [dirichletKernel_apply]
    norm_num
  have h := (PeriodicCont.isGreatest_norm_trigInterpCLM 1).2 (Set.mem_range_self (π / 3))
  refine le_trans (le_of_eq ?_) h
  rw [Fin.sum_univ_three]
  simp only [hD, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_zero,
    Nat.cast_one, Nat.cast_ofNat, Nat.cast_one]
  rw [show π / 3 - (0 : ℝ) * (2 * π) / (2 * 1 + 1) = π / 3 by norm_num,
    show π / 3 - (1 : ℝ) * (2 * π) / (2 * 1 + 1) = -(π / 3) by ring,
    show π / 3 - (2 : ℝ) * (2 * π) / (2 * 1 + 1) = -π by ring,
    Real.cos_neg, Real.cos_neg, Real.cos_pi, Real.cos_pi_div_three]
  norm_num

