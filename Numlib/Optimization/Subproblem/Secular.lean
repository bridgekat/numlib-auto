/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Operator.Banach
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Optimization.Subproblem.SecularSum

/-!
# The resolvent step and the secular function

Let $E$ be a finite-dimensional real inner product space, let $H : E \to E$ be a symmetric
continuous linear operator with leftmost (least) eigenvalue $\lambda_1$ and rightmost (greatest)
eigenvalue $\lambda_n$, and let $g \in E$. For a real shift $\lambda$, the **step**
$s(\lambda) = -(H + \lambda I)^{-1} g$ solves $(H + \lambda I) s = -g$, and the **secular function**
is $\pi(\lambda) = \|s(\lambda)\|^2$. These are (8.2.2) and (8.2.4) of [cartis2022evaluation]. This
file studies them on the interval $\lambda > -\lambda_1$, where $H + \lambda I$ is positive
definite. In an orthonormal eigenvector basis $b_i$ of $H$ with eigenvalues $\lambda_i$,
$$s(\lambda) = -\sum_i \frac{\langle b_i, g \rangle}{\lambda + \lambda_i} b_i, \qquad \pi(\lambda) =
  \sum_i \frac{\langle b_i, g \rangle^2}{(\lambda + \lambda_i)^2},$$
so the real-variable properties of $\pi$ follow from `Numlib.Optimization.Subproblem.SecularSum`.

The file also treats the threshold $\lambda \downarrow -\lambda_1$, the minimum-norm solution of
$(H + \lambda I) x = -g$, the derivatives of $s$ and $\pi$ (Theorem 8.2.6 of
[cartis2022evaluation]), the Taylor estimates of $\pi$ (Theorem 8.2.2), and the transformed secular
function $\pi^\beta$ (Lemma 8.2.3, Corollary 8.2.4 and Theorem 8.2.5). The number
$\lambda_s = \max\{0, -\lambda_1\}$ is the threshold of Lemma 8.2.1.

## Main definitions

* `Subproblem.leftmost` and `Subproblem.rightmost`: the least and greatest eigenvalues $\lambda_1$
  and $\lambda_n$ of $H$, both $0$ on the zero space.
* `Subproblem.shiftThreshold`: the number $\lambda_s = \max\{0, -\lambda_1\}$.
* `Subproblem.step` and `Subproblem.secular`: the step $s(\lambda) = -(H + \lambda I)^{-1} g$ and
  the secular function $\pi(\lambda) = \|s(\lambda)\|^2$.
* `Subproblem.particular`: the minimum-norm solution of $(H + \lambda I) x = -g$, when a solution
  exists; it is $-(H + \lambda I)^+ g$ for the pseudoinverse, and $s_s$ of the source at
  $\lambda = -\lambda_1$.
* `Subproblem.stepDeriv`: the $k$-th derivative $s^{(k)}(\lambda) = (-1)^{k+1} k! \, (H + \lambda
  I)^{-(k+1)} g$ of the step.
* `Subproblem.secularCoeff`: the coefficients $\alpha_k = (2k + 1)! / (k!)^2$ of Theorem 8.2.6.

## Main results

* `Subproblem.isPositive_add_smul_iff` and `Subproblem.isSymmetricCoercive_add_smul_iff`: on a
  nonzero space, $H + \lambda I$ is positive semidefinite if and only if $\lambda \ge -\lambda_1$,
  and positive definite if and only if $\lambda > -\lambda_1$.
  `Subproblem.isPositive_add_smul_of_le` and `Subproblem.shiftThreshold_le_of_isPositive` need no
  nontriviality.
* `Subproblem.le_leftmost_iff`, `Subproblem.le_leftmost_iff_forall` and
  `Subproblem.le_leftmost_iff_isCoerciveWith`: $\lambda_1$ is the greatest lower bound of the
  eigenvalues and the best constant $c$ in $c \|v\|^2 \le \langle v, H v \rangle$.
  `Subproblem.inner_le_rightmost_mul_norm_sq` and `Subproblem.rightmost_le_of_forall` give the same
  for $\lambda_n$.
* `Subproblem.norm_add_smul_apply_bounds`: for $\mu \ge -\lambda_1$, $(\mu + \lambda_1) \|s\| \le
  \|(H + \mu I) s\| \le (\mu + \lambda_n) \|s\|$.
* `Subproblem.step_spec`, `Subproblem.step_eq_sum` and `Subproblem.secular_eq_secularSum`: for
  $\lambda > -\lambda_1$, the step is the unique solution of $(H + \lambda I) s = -g$, with the
  spectral expansions (8.2.6) and (8.2.7).
* `Subproblem.secular_shape`: the shape of $\pi$ and of $\pi^\beta$ on $\lambda > -\lambda_1$
  (Corollary 8.2.4).
* `Subproblem.hasDerivAt_secular`, `Subproblem.secular_pos`, `Subproblem.deriv_secular_neg`,
  `Subproblem.hasDerivAt_secular_rpow` and `Subproblem.contDiffOn_secular_rpow`: calculus facts
  about $\pi$ and $\pi^\beta$ on $\lambda > -\lambda_1$ for $g \neq 0$.
* `Subproblem.particular_spec` and `Subproblem.tendsto_step_threshold`: the minimum-norm solution,
  and the limits of $s(\lambda)$ and $\pi(\lambda)$ as $\lambda \downarrow -\lambda_1$. The limit
  $s_s$ is finite if and only if $g \perp \ker(H - \lambda_1 I)$; otherwise $\pi \to +\infty$.
  `Subproblem.tendsto_secular_rpow_threshold` is the same for $\pi^\beta$.
* `Subproblem.iteratedDeriv_step`, `Subproblem.stepDeriv_succ_unique` and
  `Subproblem.iteratedDeriv_secular`: the derivatives of $s$ and $\pi$, computed by the solves
  $(H + \lambda I) s^{(k+1)} = -(k + 1) s^{(k)}$ (Theorem 8.2.6).
* `Subproblem.secular_taylor_bounds`, `Subproblem.secular_rpow_deriv_sign`,
  `Subproblem.secular_rpow_strictConcaveOn` and `Subproblem.secular_rpow_tangent`: Theorem 8.2.2,
  Lemma 8.2.3 and Theorem 8.2.5 for $\pi$. `Subproblem.secular_rpow_zero_left` is the degenerate
  case $g = 0$, where $\pi = 0$.

## Implementation notes

* A scaling norm $\|\cdot\|_M$ of the source is not a parameter. It is the norm of $E$, which can be
  an energy space: there the pencil $(H, M)$ becomes the single symmetric operator $M^{-1} H$ (see
  `Numlib.Optimization.Subproblem.Matrix`).
* "Minimum norm" refers to the norm of $E$. In the scaled setting of the source, where $E$ carries
  the inner product $\langle x, y \rangle_M$, `Subproblem.particular` is the solution of least
  $M$-norm, which is the limit of $s(\lambda)$ as $\lambda \downarrow -\lambda_1$. It is not the
  Euclidean Moore–Penrose solution. The two differ by a kernel vector.
* The step uses `Ring.inverse`, so it is defined for every $\lambda$ and is $0$ when $H + \lambda I$
  is not invertible.
* All computations use the orthonormal eigenvector basis $b_i$ = `hH.eigenvectorBasis rfl i` with
  eigenvalues $\lambda_i$ = `hH.eigenvalues rfl i`. Two vectors are equal when their coordinates are
  equal (`Subproblem.eq_of_inner_eigenvectorBasis`), and $\langle b_i, (H + \lambda I) v \rangle =
  (\lambda + \lambda_i) \langle b_i, v \rangle$.
* Mathlib sorts the eigenvalues in decreasing order. `Subproblem.leftmost` is their infimum, which
  is $0$ on the zero space. For this reason the characterizations of $\lambda_1$ assume that $E$ is
  nontrivial.
* The strict inequalities of Lemma 8.2.3 and Theorem 8.2.5 fail for $\beta = -1/2$ when $g$ is an
  eigenvector of $H$, because then $\pi(\lambda)^{-1/2}$ is affine. The strict inequalities of
  Theorem 8.2.5 also need $\delta \neq 0$. The results here assume these conditions for strictness
  and prove equality in the exceptional case.
* The results are stated on the interval $\lambda > -\lambda_1$, which contains the interval
  $\lambda > \lambda_s$ of the source.
-/

open Set Filter Topology
open Finset (range)
open scoped Nat RealInnerProductSpace

namespace Subproblem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : E →L[ℝ] E}

/-! ### The leftmost eigenvalue -/

section Leftmost

variable (hH : (H : E →ₗ[ℝ] E).IsSymmetric)

/-- The **leftmost eigenvalue** $\lambda_1$ of a symmetric operator $H$ on a finite-dimensional real
inner product space: the least eigenvalue of $H$.

It is the infimum of `hH.eigenvalues rfl`. On the zero space this is an empty infimum, so
$\lambda_1 = 0$. -/
noncomputable def leftmost : ℝ := ⨅ i, hH.eigenvalues rfl i

/-- The **shift threshold** $\lambda_s = \max\{0, -\lambda_1\}$ of a symmetric operator $H$ with
leftmost eigenvalue $\lambda_1$.

This is the number $\lambda_s$ of Lemma 8.2.1 of [cartis2022evaluation]. It is the left end of
the interval of shifts $\lambda \ge 0$ on which $H + \lambda I$ is positive definite. -/
noncomputable def shiftThreshold : ℝ := max 0 (-leftmost hH)

/-- The **rightmost eigenvalue** $\lambda_n$ of a symmetric operator $H$: the greatest eigenvalue of
$H$, and $0$ on the zero space. -/
noncomputable def rightmost : ℝ := ⨆ i, hH.eigenvalues rfl i

/-- The rightmost eigenvalue is the supremum of the eigenvalues, by definition. -/
theorem rightmost_def : rightmost hH = ⨆ i, hH.eigenvalues rfl i := rfl

variable {hH}

/-- Every eigenvalue $\lambda_i$ of $H$ satisfies $\lambda_i \le \lambda_n$. -/
theorem eigenvalues_le_rightmost (i : Fin (Module.finrank ℝ E)) :
    hH.eigenvalues rfl i ≤ rightmost hH :=
  le_ciSup (Set.finite_range _).bddAbove i

/-- Every eigenvalue $\lambda_i$ of $H$ satisfies $\lambda_1 \le \lambda_i$. -/
theorem leftmost_le_eigenvalues (i : Fin (Module.finrank ℝ E)) :
    leftmost hH ≤ hH.eigenvalues rfl i :=
  ciInf_le (Set.finite_range _).bddBelow i

/-- The leftmost eigenvalue is at most the rightmost eigenvalue: $\lambda_1 \le \lambda_n$. -/
theorem leftmost_le_rightmost : leftmost hH ≤ rightmost hH := by
  rcases isEmpty_or_nonempty (Fin (Module.finrank ℝ E)) with h | ⟨⟨i⟩⟩
  · simp [leftmost, rightmost]
  · exact (leftmost_le_eigenvalues i).trans (eigenvalues_le_rightmost i)

/-- On a nonzero space, the leftmost eigenvalue $\lambda_1$ is one of the eigenvalues $\lambda_i$ of
$H$. -/
theorem exists_eigenvalues_eq_leftmost [Nontrivial E] :
    ∃ i, hH.eigenvalues rfl i = leftmost hH := by
  have : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0, Module.finrank_pos⟩⟩
  exact exists_eq_ciInf_of_finite

/-- The shift threshold is nonnegative: $\lambda_s \ge 0$. -/
theorem shiftThreshold_nonneg : 0 ≤ shiftThreshold hH := le_max_left _ _

/-- The shift threshold satisfies $-\lambda_1 \le \lambda_s$. -/
theorem neg_leftmost_le_shiftThreshold : -leftmost hH ≤ shiftThreshold hH := le_max_right _ _

/-- The interval $(\lambda_s, \infty)$ is contained in $(-\lambda_1, \infty)$. -/
theorem Ioi_shiftThreshold_subset : Ioi (shiftThreshold hH) ⊆ Ioi (-leftmost hH) :=
  Ioi_subset_Ioi neg_leftmost_le_shiftThreshold

/-- The operator $H$ maps each vector $b_i$ of its eigenvector basis to $\lambda_i b_i$, with a real
scalar $\lambda_i$. -/
theorem apply_eigenvectorBasis' (i : Fin (Module.finrank ℝ E)) :
    H (hH.eigenvectorBasis rfl i) = hH.eigenvalues rfl i • hH.eigenvectorBasis rfl i := by
  have h := hH.apply_eigenvectorBasis rfl i
  simp only [ContinuousLinearMap.coe_coe, RCLike.ofReal_real_eq_id, id] at h
  exact h

/-- The coordinates of $(H + \lambda I) v$ in the eigenvector basis: $\langle b_i, (H + \lambda I) v
\rangle = (\lambda + \lambda_i) \langle b_i, v \rangle$ for every $\lambda \in \mathbb{R}$ and
$v \in E$. -/
theorem inner_eigenvectorBasis_add_smul (lam : ℝ) (v : E) (i : Fin (Module.finrank ℝ E)) :
    ⟪hH.eigenvectorBasis rfl i, (H + lam • 1) v⟫ =
      (lam + hH.eigenvalues rfl i) * ⟪hH.eigenvectorBasis rfl i, v⟫ := by
  have hsymm : ⟪hH.eigenvectorBasis rfl i, H v⟫ = ⟪H (hH.eigenvectorBasis rfl i), v⟫ :=
    (hH _ _).symm
  simp only [add_apply, smul_apply,
    one_apply_eq_self, inner_add_right, inner_smul_right]
  rw [show ⟪hH.eigenvectorBasis rfl i, H v⟫ = _ from hsymm, apply_eigenvectorBasis',
    real_inner_smul_left]
  ring

/-- The inner product in the coordinates of the eigenvector basis: $\langle x, y \rangle = \sum_i
\langle b_i, x \rangle \langle b_i, y \rangle$. -/
theorem inner_eq_sum_eigenvectorBasis (x y : E) :
    ⟪x, y⟫ = ∑ i, ⟪hH.eigenvectorBasis rfl i, x⟫ * ⟪hH.eigenvectorBasis rfl i, y⟫ := by
  rw [← (hH.eigenvectorBasis rfl).sum_inner_mul_inner x y]
  exact Finset.sum_congr rfl fun i _ => by rw [real_inner_comm x]

/-- Two vectors $x, y \in E$ with $\langle b_i, x \rangle = \langle b_i, y \rangle$ for every $i$
are equal. -/
theorem eq_of_inner_eigenvectorBasis {x y : E}
    (h : ∀ i, ⟪hH.eigenvectorBasis rfl i, x⟫ = ⟪hH.eigenvectorBasis rfl i, y⟫) : x = y := by
  rw [← (hH.eigenvectorBasis rfl).sum_repr' x, ← (hH.eigenvectorBasis rfl).sum_repr' y]
  simp_rw [h]

/-- The coordinates of a combination of the eigenvectors:
$\langle b_i, \sum_j c_j b_j \rangle = c_i$. -/
theorem inner_eigenvectorBasis_sum (c : Fin (Module.finrank ℝ E) → ℝ)
    (i : Fin (Module.finrank ℝ E)) :
    ⟪hH.eigenvectorBasis rfl i, ∑ j, c j • hH.eigenvectorBasis rfl j⟫ = c i :=
  (hH.eigenvectorBasis rfl).orthonormal.inner_right_fintype c i

/-- The Rayleigh lower bound for a shifted operator: for every $\lambda \in \mathbb{R}$ and
$v \in E$, $(\lambda + \lambda_1) \|v\|^2 \le \langle (H + \lambda I) v, v \rangle$. -/
theorem add_leftmost_mul_norm_sq_le (lam : ℝ) (v : E) :
    (lam + leftmost hH) * ‖v‖ ^ 2 ≤ ⟪(H + lam • 1) v, v⟫ := by
  rw [← real_inner_self_eq_norm_sq, real_inner_comm, inner_eq_sum_eigenvectorBasis (hH := hH),
    inner_eq_sum_eigenvectorBasis (hH := hH), Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [inner_eigenvectorBasis_add_smul]
  have := leftmost_le_eigenvalues (hH := hH) i
  nlinarith [mul_self_nonneg ⟪hH.eigenvectorBasis rfl i, v⟫]

/-- The Rayleigh lower bound: $\lambda_1 \|v\|^2 \le \langle v, H v \rangle$ for every $v \in E$. -/
theorem leftmost_mul_norm_sq_le (v : E) : leftmost hH * ‖v‖ ^ 2 ≤ ⟪v, H v⟫ := by
  simpa [real_inner_comm, inner_add_left, real_inner_self_eq_norm_sq] using
    add_leftmost_mul_norm_sq_le (hH := hH) 0 v

/-- On a nonzero space, $c \le \lambda_1$ if and only if $c \le \lambda_i$ for every eigenvalue
$\lambda_i$ of $H$. That is, $\lambda_1$ is the greatest lower bound of the eigenvalues. -/
theorem le_leftmost_iff [Nontrivial E] {c : ℝ} :
    c ≤ leftmost hH ↔ ∀ i, c ≤ hH.eigenvalues rfl i := by
  have : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0, Module.finrank_pos⟩⟩
  exact le_ciInf_iff (Set.finite_range _).bddBelow

/-- On a nonzero space, $c \le \lambda_1$ if and only if $c \|v\|^2 \le \langle v, H v \rangle$ for
every $v \in E$. That is, $\lambda_1$ is the best constant in the Rayleigh bound; this is the
Courant–Fischer principle for the least eigenvalue. -/
theorem le_leftmost_iff_forall [Nontrivial E] {c : ℝ} :
    c ≤ leftmost hH ↔ ∀ v, c * ‖v‖ ^ 2 ≤ ⟪v, H v⟫ := by
  constructor
  · intro hc v
    exact le_trans (mul_le_mul_of_nonneg_right hc (sq_nonneg _)) (leftmost_mul_norm_sq_le v)
  · intro h
    obtain ⟨i, hi⟩ := exists_eigenvalues_eq_leftmost (hH := hH)
    have h' := h (hH.eigenvectorBasis rfl i)
    rw [apply_eigenvectorBasis', real_inner_smul_right, real_inner_self_eq_norm_sq,
      (hH.eigenvectorBasis rfl).norm_eq_one, hi] at h'
    simpa using h'

/-- On a nonzero space, $c \le \lambda_1$ if and only if $H$ is coercive with constant $c$, that is,
$c \|v\|^2 \le \langle H v, v \rangle$ for every $v \in E$ (`LinearMap.IsCoerciveWith`). -/
theorem le_leftmost_iff_isCoerciveWith [Nontrivial E] {c : ℝ} :
    c ≤ leftmost hH ↔ (H : E →ₗ[ℝ] E).IsCoerciveWith c := by
  rw [le_leftmost_iff_forall]
  refine forall_congr' fun v => ?_
  simp [real_inner_comm]

/-- On a nonzero space, the leftmost eigenvalue $\lambda_1$ is an eigenvalue of $H$. -/
theorem hasEigenvalue_leftmost [Nontrivial E] :
    Module.End.HasEigenvalue (H : E →ₗ[ℝ] E) (leftmost hH) := by
  obtain ⟨i, hi⟩ := exists_eigenvalues_eq_leftmost (hH := hH)
  simpa [hi] using hH.hasEigenvalue_eigenvalues rfl i

/-- Let $H$ be a symmetric operator on a nonzero finite-dimensional real inner product space. Then
for every $\lambda \in \mathbb{R}$, $H + \lambda I$ is positive semidefinite if and only if
$$\lambda \ge -\lambda_1.$$

Positive semidefinite is `LinearMap.IsPositive`: symmetric with
$\langle (H + \lambda I) x, x \rangle \ge 0$ for all $x$. On the zero space $\lambda_1 = 0$ and
the equivalence fails for $\lambda < 0$, so the space is assumed nontrivial. -/
theorem isPositive_add_smul_iff [Nontrivial E] (lam : ℝ) :
    ((H + lam • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E).IsPositive ↔ -leftmost hH ≤ lam := by
  rw [ContinuousLinearMap.isPositive_add_smul_one_iff hH]
  constructor
  · intro h
    obtain ⟨i, hi⟩ := exists_eigenvalues_eq_leftmost (hH := hH)
    have h' := h (hH.eigenvectorBasis rfl i)
    rw [inner_eigenvectorBasis_add_smul, real_inner_self_eq_norm_sq,
      (hH.eigenvectorBasis rfl).norm_eq_one, hi] at h'
    linarith
  · intro hlam v
    rw [real_inner_comm]
    exact le_trans (mul_nonneg (by linarith) (sq_nonneg _))
      (add_leftmost_mul_norm_sq_le (hH := hH) lam v)

/-- On the zero space the leftmost eigenvalue is $0$, an empty infimum. -/
theorem leftmost_eq_zero_of_subsingleton [Subsingleton E] : leftmost hH = 0 := by
  have : IsEmpty (Fin (Module.finrank ℝ E)) := by
    rw [Module.finrank_zero_of_subsingleton]; infer_instance
  exact Real.iInf_of_isEmpty _

/-- If $\lambda \ge -\lambda_1$, then $H + \lambda I$ is positive semidefinite. The space may be the
zero space. -/
theorem isPositive_add_smul_of_le {lam : ℝ} (hlam : -leftmost hH ≤ lam) :
    ((H + lam • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E).IsPositive := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · rw [ContinuousLinearMap.isPositive_add_smul_one_iff hH]
    intro v; simp [Subsingleton.elim v 0]
  · exact (isPositive_add_smul_iff (hH := hH) lam).2 hlam

/-- If $\mu \ge 0$ and $H + \mu I$ is positive semidefinite, then $\lambda_s \le \mu$. The space may
be the zero space. -/
theorem shiftThreshold_le_of_isPositive {μ : ℝ} (hμ : 0 ≤ μ)
    (hpos : ((H + μ • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E).IsPositive) : shiftThreshold hH ≤ μ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · rw [shiftThreshold, leftmost_eq_zero_of_subsingleton]; simpa using hμ
  · exact max_le hμ ((isPositive_add_smul_iff (hH := hH) μ).1 hpos)

/-- On a nonzero space, $H + \lambda I$ is positive definite, that is, symmetric and coercive, if
and only if $\lambda > -\lambda_1$. -/
theorem isSymmetricCoercive_add_smul_iff [Nontrivial E] (lam : ℝ) :
    ((H + lam • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E).IsSymmetricCoercive ↔ -leftmost hH < lam := by
  constructor
  · intro hc
    obtain ⟨i, hi⟩ := exists_eigenvalues_eq_leftmost (hH := hH)
    have h := hc.isCoercive.inner_self_pos ((hH.eigenvectorBasis rfl).orthonormal.ne_zero i)
    simp only [RCLike.re_to_real, ContinuousLinearMap.coe_coe] at h
    rw [real_inner_comm, inner_eigenvectorBasis_add_smul, real_inner_self_eq_norm_sq,
      (hH.eigenvectorBasis rfl).norm_eq_one, hi] at h
    linarith
  · intro hlam
    refine ⟨ContinuousLinearMap.isSymmetric_add_smul_one hH lam, ?_⟩
    refine (LinearMap.isCoercive_iff_forall_pos _).2 fun x hx => ?_
    simp only [RCLike.re_to_real, ContinuousLinearMap.coe_coe]
    exact lt_of_lt_of_le (mul_pos (by linarith) (by positivity))
      (add_leftmost_mul_norm_sq_le (hH := hH) lam x)

/-- On a nonzero space, $H - \lambda_1 I$ is singular: its kernel is not $\{0\}$. -/
theorem ker_add_neg_leftmost_ne_bot [Nontrivial E] :
    LinearMap.ker ((H + (-leftmost hH) • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E) ≠ ⊥ := by
  obtain ⟨i, hi⟩ := exists_eigenvalues_eq_leftmost (hH := hH)
  rw [Submodule.ne_bot_iff]
  refine ⟨hH.eigenvectorBasis rfl i, ?_, (hH.eigenvectorBasis rfl).orthonormal.ne_zero i⟩
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, add_apply, apply_eigenvectorBasis', hi]
  simp

/-- For $\lambda > -\lambda_1$, the operator $H + \lambda I$ is invertible. -/
theorem isUnit_add_smul {lam : ℝ} (hlam : -leftmost hH < lam) : IsUnit (H + lam • 1) := by
  have := FiniteDimensional.complete ℝ E
  rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_ker_eq_bot,
    LinearMap.ker_eq_bot']
  intro v hv
  refine eq_of_inner_eigenvectorBasis (hH := hH) fun i => ?_
  have h := inner_eigenvectorBasis_add_smul (hH := hH) lam v i
  rw [ContinuousLinearMap.coe_coe] at hv
  rw [hv, inner_zero_right] at h
  have hpos : 0 < lam + hH.eigenvalues rfl i := by
    have := leftmost_le_eigenvalues (hH := hH) i; linarith
  rw [inner_zero_right]
  exact (mul_eq_zero.1 h.symm).resolve_left hpos.ne'

/-- The Rayleigh upper bound for a shifted operator: for every $\lambda \in \mathbb{R}$ and
$v \in E$, $\langle (H + \lambda I) v, v \rangle \le (\lambda + \lambda_n) \|v\|^2$. -/
theorem inner_add_smul_le_add_rightmost (lam : ℝ) (v : E) :
    ⟪(H + lam • 1) v, v⟫ ≤ (lam + rightmost hH) * ‖v‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, real_inner_comm, inner_eq_sum_eigenvectorBasis (hH := hH),
    inner_eq_sum_eigenvectorBasis (hH := hH), Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [inner_eigenvectorBasis_add_smul]
  have := eigenvalues_le_rightmost (hH := hH) i
  nlinarith [mul_self_nonneg ⟪hH.eigenvectorBasis rfl i, v⟫]

/-- The Rayleigh upper bound: $\langle v, H v \rangle \le \lambda_n \|v\|^2$ for every $v \in E$. -/
theorem inner_le_rightmost_mul_norm_sq (v : E) : ⟪v, H v⟫ ≤ rightmost hH * ‖v‖ ^ 2 := by
  simpa [real_inner_comm, inner_add_left, real_inner_self_eq_norm_sq] using
    inner_add_smul_le_add_rightmost (hH := hH) 0 v

/-- On a nonzero space, the rightmost eigenvalue $\lambda_n$ is one of the eigenvalues $\lambda_i$
of $H$. -/
theorem exists_eigenvalues_eq_rightmost [Nontrivial E] :
    ∃ i, hH.eigenvalues rfl i = rightmost hH := by
  have : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0, Module.finrank_pos⟩⟩
  exact exists_eq_ciSup_of_finite

/-- On a nonzero space, if $\langle v, H v \rangle \le c \|v\|^2$ for every $v \in E$, then
$\lambda_n \le c$. That is, $\lambda_n$ is the least constant in the Rayleigh upper bound. -/
theorem rightmost_le_of_forall [Nontrivial E] {c : ℝ} (h : ∀ v, ⟪v, H v⟫ ≤ c * ‖v‖ ^ 2) :
    rightmost hH ≤ c := by
  obtain ⟨i, hi⟩ := exists_eigenvalues_eq_rightmost (hH := hH)
  have h' := h (hH.eigenvectorBasis rfl i)
  rw [apply_eigenvectorBasis', real_inner_smul_right, real_inner_self_eq_norm_sq,
    (hH.eigenvectorBasis rfl).norm_eq_one, hi] at h'
  simpa using h'

/-- **Norm bound for a positive semidefinite shift.** For $\lambda \ge -\lambda_1$ and every
$v \in E$, $\|(H + \lambda I) v\| \le (\lambda + \lambda_n) \|v\|$. -/
theorem norm_add_smul_apply_le {lam : ℝ} (hlam : -leftmost hH ≤ lam) (v : E) :
    ‖(H + lam • 1) v‖ ≤ (lam + rightmost hH) * ‖v‖ := by
  have hsq : ‖(H + lam • 1) v‖ ^ 2 ≤ ((lam + rightmost hH) * ‖v‖) ^ 2 := by
    rw [mul_pow, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      inner_eq_sum_eigenvectorBasis (hH := hH), inner_eq_sum_eigenvectorBasis (hH := hH) v v,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [inner_eigenvectorBasis_add_smul]
    have h1 := leftmost_le_eigenvalues (hH := hH) i
    have h2 := eigenvalues_le_rightmost (hH := hH) i
    have h3 : 0 ≤ lam + hH.eigenvalues rfl i := by linarith
    have h4 : (lam + hH.eigenvalues rfl i) ^ 2 ≤ (lam + rightmost hH) ^ 2 :=
      pow_le_pow_left₀ h3 (by linarith) 2
    nlinarith [mul_self_nonneg ⟪hH.eigenvectorBasis rfl i, v⟫]
  have h0 : 0 ≤ lam + rightmost hH := by linarith [leftmost_le_rightmost (hH := hH)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- **Rayleigh-quotient bounds for a shifted operator.** Let $H$ be a symmetric operator on a
finite-dimensional real inner product space $E$, with leftmost eigenvalue $\lambda_1$ and
rightmost eigenvalue $\lambda_n$. Let $\mu \ge -\lambda_1$. Then for every $s \in E$
$$(\mu + \lambda_1) \|s\| \le \|(H + \mu I) s\| \le (\mu + \lambda_n) \|s\|.$$

This is the generalized Rayleigh-quotient inequality in the form used in (9.3.1) of
[cartis2022evaluation]. -/
theorem norm_add_smul_apply_bounds {μ : ℝ} (hμ : -leftmost hH ≤ μ) (s : E) :
    (μ + leftmost hH) * ‖s‖ ≤ ‖(H + μ • 1) s‖ ∧ ‖(H + μ • 1) s‖ ≤ (μ + rightmost hH) * ‖s‖ := by
  have hsq' : ∀ x : E, ‖x‖ ^ 2 = ∑ i, ⟪hH.eigenvectorBasis rfl i, x⟫ ^ 2 := fun x => by
    rw [← real_inner_self_eq_norm_sq, inner_eq_sum_eigenvectorBasis (hH := hH)]
    exact Finset.sum_congr rfl fun i _ => (sq _).symm
  have hsq : ‖(H + μ • 1) s‖ ^ 2 =
      ∑ i, (μ + hH.eigenvalues rfl i) ^ 2 * ⟪hH.eigenvectorBasis rfl i, s⟫ ^ 2 := by
    rw [hsq']
    exact Finset.sum_congr rfl fun i _ => by rw [inner_eigenvectorBasis_add_smul, mul_pow]
  have hs := hsq' s
  have h1 : 0 ≤ μ + leftmost hH := by linarith
  have hl : ∀ i, μ + leftmost hH ≤ μ + hH.eigenvalues rfl i := fun i => by
    linarith [leftmost_le_eigenvalues (hH := hH) i]
  have hr : ∀ i, μ + hH.eigenvalues rfl i ≤ μ + rightmost hH := fun i => by
    linarith [eigenvalues_le_rightmost (hH := hH) i]
  have hr0 : 0 ≤ μ + rightmost hH := by linarith [leftmost_le_rightmost (hH := hH)]
  constructor
  · refine (pow_le_pow_iff_left₀ (mul_nonneg h1 (norm_nonneg _)) (norm_nonneg _)
      two_ne_zero).1 ?_
    rw [hsq, mul_pow, hs, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h1 (hl i) 2) (sq_nonneg _)
  · refine (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hr0 (norm_nonneg _))
      two_ne_zero).1 ?_
    rw [hsq, mul_pow, hs, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (h1.trans (hl i)) (hr i) 2) (sq_nonneg _)

end Leftmost

/-! ### The step and the secular function -/

/-- The **step** $s(\lambda) = -(H + \lambda I)^{-1} g$, for $g \in E$, a continuous linear operator
$H$ on $E$ and $\lambda \in \mathbb{R}$.

This is (8.2.2) of [cartis2022evaluation]. The inverse is `Ring.inverse`, so the step is defined
for every $\lambda$, and it is $0$ when $H + \lambda I$ is not invertible. It solves
$(H + \lambda I) s = -g$ whenever $H + \lambda I$ is invertible (`Subproblem.step_spec`). -/
noncomputable def step (g : E) (H : E →L[ℝ] E) (lam : ℝ) : E := -(Ring.inverse (H + lam • 1)) g

/-- The **secular function** $\pi(\lambda) = \|s(\lambda)\|^2$, where $s(\lambda)$ is the step
`Subproblem.step`.

This is (8.2.4) of [cartis2022evaluation]. The transformed secular function
$\pi(\lambda; \beta) = \pi(\lambda)^\beta$ of (8.2.17) is written `secular g H λ ^ β`, with
`Real.rpow`. -/
noncomputable def secular (g : E) (H : E →L[ℝ] E) (lam : ℝ) : ℝ := ‖step g H lam‖ ^ 2

variable {g : E} (hH : (H : E →ₗ[ℝ] E).IsSymmetric)

/-- The **spectral weights** $\gamma_i^2 = \langle b_i, g \rangle^2$ of $g$ in the eigenvector basis
$b_i$ of $H$, in the notation of (8.2.7) of [cartis2022evaluation]. -/
noncomputable def secularWeight (g : E) (i : Fin (Module.finrank ℝ E)) : ℝ :=
  ⟪hH.eigenvectorBasis rfl i, g⟫ ^ 2

variable {hH}

/-- The spectral weights are nonnegative. -/
theorem secularWeight_nonneg : 0 ≤ secularWeight hH g := fun _ => sq_nonneg _

/-- The spectral weights sum to $\|g\|^2$: $\sum_i \gamma_i^2 = \|g\|^2$. -/
theorem sum_secularWeight : ∑ i, secularWeight hH g i = ‖g‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_sum_eigenvectorBasis (hH := hH)]
  simp [secularWeight, sq]

/-- Some spectral weight $\gamma_i^2$ is nonzero if and only if $g \neq 0$. -/
theorem secularWeight_ne_zero_iff : secularWeight hH g ≠ 0 ↔ g ≠ 0 := by
  constructor
  · rintro hw rfl
    exact hw (funext fun i => by simp [secularWeight])
  · intro hg hw
    have := sum_secularWeight (hH := hH) (g := g)
    rw [hw] at this
    simp only [Pi.zero_apply, Finset.sum_const_zero] at this
    exact hg (by simpa using this.symm)

/-- Let $g \neq 0$. Then $H g = c g$ for some $c \in \mathbb{R}$, that is, $g$ is an eigenvector of
$H$, if and only if all nonzero spectral weights of $g$ belong to a single eigenvalue
(`Subproblem.SinglePole`). -/
theorem singlePole_secularWeight_iff (hg : g ≠ 0) :
    SinglePole (hH.eigenvalues rfl) (secularWeight hH g) ↔ ∃ c : ℝ, H g = c • g := by
  have hcoord : ∀ i, ⟪hH.eigenvectorBasis rfl i, H g⟫ =
      hH.eigenvalues rfl i * ⟪hH.eigenvectorBasis rfl i, g⟫ := fun i => by
    have := inner_eigenvectorBasis_add_smul (hH := hH) 0 g i
    simpa using this
  have hw : ∀ i, secularWeight hH g i ≠ 0 ↔ ⟪hH.eigenvectorBasis rfl i, g⟫ ≠ 0 := fun i => by
    simp [secularWeight]
  constructor
  · intro hs
    obtain ⟨i₀, hi₀⟩ : ∃ i, ⟪hH.eigenvectorBasis rfl i, g⟫ ≠ 0 := by
      by_contra h
      push Not at h
      exact hg (eq_of_inner_eigenvectorBasis (hH := hH) fun i => by simp [h i])
    refine ⟨hH.eigenvalues rfl i₀, eq_of_inner_eigenvectorBasis (hH := hH) fun i => ?_⟩
    rw [hcoord, real_inner_smul_right]
    by_cases hi : ⟪hH.eigenvectorBasis rfl i, g⟫ = 0
    · simp [hi]
    · rw [hs i i₀ ((hw i).2 hi) ((hw i₀).2 hi₀)]
  · rintro ⟨c, hc⟩ i j hi hj
    have key : ∀ k, ⟪hH.eigenvectorBasis rfl k, g⟫ ≠ 0 → hH.eigenvalues rfl k = c := by
      intro k hk
      have := hcoord k
      rw [hc, real_inner_smul_right] at this
      exact (mul_right_cancel₀ hk this).symm
    rw [key i ((hw i).1 hi), key j ((hw j).1 hj)]

/-- Every shift $\lambda > -\lambda_1$ lies to the right of every pole $-\lambda_i$, that is, in
`Subproblem.secularDomain` of the eigenvalues. -/
theorem mem_secularDomain_of_lt {lam : ℝ} (hlam : -leftmost hH < lam) :
    lam ∈ secularDomain (hH.eigenvalues rfl) := fun i => by
  have := leftmost_le_eigenvalues (hH := hH) i
  linarith

/-- The interval $(-\lambda_1, \infty)$ is contained in the domain `Subproblem.secularDomain` of the
spectral form of the secular function. -/
theorem Ioi_subset_secularDomain :
    Ioi (-leftmost hH) ⊆ secularDomain (hH.eigenvalues rfl) := fun _ h =>
  mem_secularDomain_of_lt h

/-- For $\lambda > -\lambda_1$, the inverse of $H + \lambda I$ is a right inverse:
$(H + \lambda I) (H + \lambda I)^{-1} x = x$ for every $x \in E$. -/
theorem add_smul_inverse_apply {lam : ℝ} (hlam : -leftmost hH < lam) (x : E) :
    (H + lam • 1) (Ring.inverse (H + lam • 1) x) = x :=
  congrArg (fun T : E →L[ℝ] E => T x) (Ring.mul_inverse_cancel _ (isUnit_add_smul hlam))

/-- For $\lambda > -\lambda_1$, the operator $H + \lambda I$ is injective. -/
theorem injective_add_smul {lam : ℝ} (hlam : -leftmost hH < lam) :
    Function.Injective ⇑(H + lam • 1 : E →L[ℝ] E) :=
  Function.LeftInverse.injective fun x =>
    congrArg (fun T : E →L[ℝ] E => T x) (Ring.inverse_mul_cancel _ (isUnit_add_smul hlam))

/-- **The step solves the shifted system.** Let $H$ be a symmetric operator on a finite-dimensional
real inner product space $E$, let $g \in E$, and let $\lambda > -\lambda_1$. Then
$$(H + \lambda I) s(\lambda) = -g,$$
and every $s \in E$ with $(H + \lambda I) s = -g$ equals $s(\lambda)$.

This is (8.2.2) of [cartis2022evaluation]. -/
theorem step_spec {lam : ℝ} (hlam : -leftmost hH < lam) :
    (H + lam • 1) (step g H lam) = -g ∧
      ∀ s, (H + lam • 1) s = -g → s = step g H lam := by
  have heq : (H + lam • 1) (step g H lam) = -g := by
    rw [step, map_neg, add_smul_inverse_apply hlam]
  refine ⟨heq, fun s hs => ?_⟩
  have hinj := injective_add_smul (hH := hH) hlam
  exact hinj (hs.trans heq.symm)

/-- Let $\lambda > -\lambda_1$. If $(H + \lambda I) y = v$, then the coordinates of $y$ in the
eigenvector basis are $\langle b_i, y \rangle = \langle b_i, v \rangle / (\lambda + \lambda_i)$. -/
theorem inner_eigenvectorBasis_eq_div {lam : ℝ} (hlam : -leftmost hH < lam) {y v : E}
    (hy : (H + lam • 1) y = v) (i : Fin (Module.finrank ℝ E)) :
    ⟪hH.eigenvectorBasis rfl i, y⟫ =
      ⟪hH.eigenvectorBasis rfl i, v⟫ / (lam + hH.eigenvalues rfl i) := by
  have hpos : 0 < lam + hH.eigenvalues rfl i := by
    have := leftmost_le_eigenvalues (hH := hH) i; linarith
  rw [← hy, inner_eigenvectorBasis_add_smul, mul_div_cancel_left₀ _ hpos.ne']

/-- For $\lambda > -\lambda_1$, the coordinates of the step are $\langle b_i, s(\lambda) \rangle =
-\langle b_i, g \rangle / (\lambda + \lambda_i)$. -/
theorem inner_eigenvectorBasis_step {lam : ℝ} (hlam : -leftmost hH < lam)
    (i : Fin (Module.finrank ℝ E)) :
    ⟪hH.eigenvectorBasis rfl i, step g H lam⟫ =
      -⟪hH.eigenvectorBasis rfl i, g⟫ / (lam + hH.eigenvalues rfl i) := by
  rw [inner_eigenvectorBasis_eq_div hlam (step_spec hlam).1, inner_neg_right]

/-- **Spectral expansion of the step.** Let $H$ be a symmetric operator on a finite-dimensional real
inner product space $E$, with orthonormal eigenvector basis $b_i$ and eigenvalues $\lambda_i$.
Let $g \in E$ and $\lambda > -\lambda_1$. Then
$$s(\lambda) = -\sum_i \frac{\langle b_i, g \rangle}{\lambda + \lambda_i} b_i.$$

This is (8.2.6) of [cartis2022evaluation]. The corresponding expansion of $\pi$ is
`Subproblem.secular_eq_secularSum`. -/
theorem step_eq_sum {lam : ℝ} (hlam : -leftmost hH < lam) :
    step g H lam = -∑ i, (⟪hH.eigenvectorBasis rfl i, g⟫ / (lam + hH.eigenvalues rfl i)) •
      hH.eigenvectorBasis rfl i := by
  refine eq_of_inner_eigenvectorBasis (hH := hH) fun i => ?_
  rw [inner_eigenvectorBasis_step hlam, inner_neg_right, inner_eigenvectorBasis_sum, neg_div]

/-- **Spectral expansion of the secular function.** For $\lambda > -\lambda_1$,
$$\pi(\lambda) = \sum_i \frac{\langle b_i, g \rangle^2}{(\lambda + \lambda_i)^2}.$$
This is (8.2.7) of [cartis2022evaluation]. The right side is `Subproblem.secularSum` of the
eigenvalues and the spectral weights. -/
theorem secular_eq_secularSum {lam : ℝ} (hlam : -leftmost hH < lam) :
    secular g H lam = secularSum (hH.eigenvalues rfl) (secularWeight hH g) lam := by
  rw [secular, ← real_inner_self_eq_norm_sq, inner_eq_sum_eigenvectorBasis (hH := hH)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_eigenvectorBasis_step hlam, secularWeight, neg_div, neg_mul_neg, ← sq, div_pow]

/-- The secular function agrees with its spectral form `Subproblem.secularSum` on the interval
$(-\lambda_1, \infty)$. -/
theorem eqOn_secular_secularSum :
    EqOn (secular g H) (secularSum (hH.eigenvalues rfl) (secularWeight hH g))
      (Ioi (-leftmost hH)) := fun _ h => secular_eq_secularSum h

/-- For $\lambda > -\lambda_1$, the secular function agrees with its spectral form
`Subproblem.secularSum` on a neighbourhood of $\lambda$. -/
theorem secular_eventuallyEq {lam : ℝ} (hlam : -leftmost hH < lam) :
    secular g H =ᶠ[𝓝 lam] secularSum (hH.eigenvalues rfl) (secularWeight hH g) :=
  Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hlam) fun _ h => secular_eq_secularSum h

/-- The secular function agrees with its spectral form `Subproblem.secularSum` for all large enough
$\lambda$. -/
theorem secular_eventuallyEq_atTop :
    secular g H =ᶠ[atTop] secularSum (hH.eigenvalues rfl) (secularWeight hH g) :=
  Filter.eventually_of_mem (Ioi_mem_atTop _) fun _ h => secular_eq_secularSum h

/-- **Shape of the secular function.** Let $H$ be a symmetric operator on a finite-dimensional real
inner product space $E$, let $g \in E$ with $g \neq 0$, and let $\beta \in \mathbb{R}$. Then on
the interval $\lambda > -\lambda_1$:
* $\pi$ is positive, continuous, strictly decreasing and strictly convex, and
  $\pi(\lambda) \to 0$ as $\lambda \to \infty$;
* if $\beta > 0$, then $\pi^\beta$ is strictly decreasing and strictly convex, and
  $\pi(\lambda)^\beta \to 0$ as $\lambda \to \infty$;
* if $-1/2 \le \beta < 0$, then $\pi^\beta$ is strictly increasing and concave, and
  $\pi(\lambda)^\beta \to +\infty$ as $\lambda \to \infty$.

This is Section 8.2.1 and Corollary 8.2.4 of [cartis2022evaluation]. The interval
$\lambda > -\lambda_1$ contains the interval $(\lambda_s, \infty)$ of the source. -/
theorem secular_shape (hg : g ≠ 0) (β : ℝ) :
    (∀ lam ∈ Ioi (-leftmost hH), 0 < secular g H lam) ∧
    ContinuousOn (secular g H) (Ioi (-leftmost hH)) ∧
    StrictAntiOn (secular g H) (Ioi (-leftmost hH)) ∧
    StrictConvexOn ℝ (Ioi (-leftmost hH)) (secular g H) ∧
    Tendsto (secular g H) atTop (𝓝 0) ∧
    (0 < β → StrictAntiOn (fun lam => secular g H lam ^ β) (Ioi (-leftmost hH)) ∧
      StrictConvexOn ℝ (Ioi (-leftmost hH)) (fun lam => secular g H lam ^ β) ∧
      Tendsto (fun lam => secular g H lam ^ β) atTop (𝓝 0)) ∧
    (β ∈ Ico (-1 / 2) 0 →
      StrictMonoOn (fun lam => secular g H lam ^ β) (Ioi (-leftmost hH)) ∧
      ConcaveOn ℝ (Ioi (-leftmost hH)) (fun lam => secular g H lam ^ β) ∧
      Tendsto (fun lam => secular g H lam ^ β) atTop atTop) := by
  have hw := secularWeight_nonneg (hH := hH) (g := g)
  have hw0 := (secularWeight_ne_zero_iff (hH := hH)).2 hg
  have hsub := Ioi_subset_secularDomain (hH := hH)
  have heq := eqOn_secular_secularSum (hH := hH) (g := g)
  have heqβ : EqOn (fun lam => secularSum (hH.eigenvalues rfl) (secularWeight hH g) lam ^ β)
      (fun lam => secular g H lam ^ β) (Ioi (-leftmost hH)) := fun x hx => by
    simp only [heq hx]
  have hevβ : (fun lam => secularSum (hH.eigenvalues rfl) (secularWeight hH g) lam ^ β) =ᶠ[atTop]
      (fun lam => secular g H lam ^ β) :=
    (secular_eventuallyEq_atTop (hH := hH) (g := g)).mono fun x hx => by simp only [hx]
  have hconv : Convex ℝ (Ioi (-leftmost hH)) := convex_Ioi _
  obtain ⟨hpos, hneg⟩ := secularSum_rpow_shape hw hw0 β
  refine ⟨fun lam h => heq h ▸ secularSum_pos hw hw0 (hsub h),
    (continuousOn_secularSum.mono hsub).congr fun x hx => heq hx,
    ((secularSum_strictAntiOn hw hw0).mono hsub).congr heq.symm,
    ((secularSum_strictConvexOn hw hw0).subset hsub hconv).congr heq.symm,
    tendsto_secularSum_atTop.congr' (secular_eventuallyEq_atTop (hH := hH) (g := g)).symm,
    fun hβ => ?_, fun hβ => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hpos hβ
    exact ⟨(h1.mono hsub).congr heqβ, (h2.subset hsub hconv).congr heqβ, h3.congr' hevβ⟩
  · obtain ⟨h1, h2, h3⟩ := hneg hβ
    exact ⟨(h1.mono hsub).congr heqβ, (h2.subset hsub hconv).congr heqβ, h3.congr' hevβ⟩

/-! ### The minimum-norm solution and the threshold -/

/-- A vector $v$ lies in $\ker(H + \lambda I)$ if and only if $(\lambda + \lambda_i) \langle b_i, v
\rangle = 0$ for every $i$. -/
theorem mem_ker_add_smul_iff {lam : ℝ} {v : E} :
    v ∈ LinearMap.ker ((H + lam • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E) ↔
      ∀ i, (lam + hH.eigenvalues rfl i) * ⟪hH.eigenvectorBasis rfl i, v⟫ = 0 := by
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  constructor
  · intro h i
    rw [← inner_eigenvectorBasis_add_smul, h, inner_zero_right]
  · intro h
    refine eq_of_inner_eigenvectorBasis (hH := hH) fun i => ?_
    rw [inner_eigenvectorBasis_add_smul, h, inner_zero_right]

/-- An eigenvector $b_i$ with $\lambda + \lambda_i = 0$ lies in the kernel of $H + \lambda I$. -/
theorem eigenvectorBasis_mem_ker {lam : ℝ} {i : Fin (Module.finrank ℝ E)}
    (hi : lam + hH.eigenvalues rfl i = 0) :
    hH.eigenvectorBasis rfl i ∈ LinearMap.ker ((H + lam • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E) := by
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, add_apply, apply_eigenvectorBasis',
    smul_apply, one_apply_eq_self, ← add_smul, add_comm, hi, zero_smul]

variable (hH) in
/-- The **minimum-norm solution** of $(H + \lambda I) x = -g$, for a symmetric operator $H$ with
orthonormal eigenvector basis $b_i$ and eigenvalues $\lambda_i$:
$$-\sum_i \frac{\langle b_i, g \rangle}{\lambda + \lambda_i} b_i,$$
where a term with $\lambda + \lambda_i = 0$ is $0$.

The vanishing terms come from the convention $a / 0 = 0$ of Lean. The vector is
$-(H + \lambda I)^+ g$ for the pseudoinverse $(H + \lambda I)^+$. It solves the system when a
solution exists (`Subproblem.particular_spec`). At $\lambda = -\lambda_1$ it is the vector $s_s$
of Section 8.3 of [cartis2022evaluation], the limit of $s(\lambda)$ as
$\lambda \downarrow -\lambda_1$ when that limit exists (`Subproblem.tendsto_step_threshold`). -/
noncomputable def particular (g : E) (lam : ℝ) : E :=
  -∑ i, (⟪hH.eigenvectorBasis rfl i, g⟫ / (lam + hH.eigenvalues rfl i)) • hH.eigenvectorBasis rfl i

/-- The coordinates of the minimum-norm solution are $\langle b_i, x \rangle = -\langle b_i, g
\rangle / (\lambda + \lambda_i)$, with the value $0$ when $\lambda + \lambda_i = 0$. -/
theorem inner_eigenvectorBasis_particular (lam : ℝ) (i : Fin (Module.finrank ℝ E)) :
    ⟪hH.eigenvectorBasis rfl i, particular hH g lam⟫ =
      -⟪hH.eigenvectorBasis rfl i, g⟫ / (lam + hH.eigenvalues rfl i) := by
  rw [particular, inner_neg_right, inner_eigenvectorBasis_sum, neg_div]

/-- **The minimum-norm solution.** Let $H$ be a symmetric operator on a finite-dimensional real
inner product space $E$, let $g \in E$ and $\lambda \in \mathbb{R}$, and put
$K = \ker(H + \lambda I)$. Let $p$ be `Subproblem.particular` for $g$ and $\lambda$. Then:
* (i) $p \in K^\perp$;
* (ii) if $g \in K^\perp$, that is, the system $(H + \lambda I) x = -g$ is consistent, then $p$
  solves it; the solutions are exactly the vectors $x$ with $x - p \in K$; every solution $x$
  satisfies $\|p\| \le \|x\|$; and $\langle g, v \rangle = 0$ for every $v \in K$;
* (iii) if $\lambda > -\lambda_1$, then $p = s(\lambda)$. -/
theorem particular_spec (lam : ℝ) :
    particular hH g lam ∈ (LinearMap.ker ((H + lam • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ ∧
    (g ∈ (LinearMap.ker ((H + lam • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ →
      (H + lam • 1) (particular hH g lam) = -g ∧
      (∀ x, (H + lam • 1) x = -g ↔
        x - particular hH g lam ∈ LinearMap.ker ((H + lam • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E)) ∧
      (∀ x, (H + lam • 1) x = -g → ‖particular hH g lam‖ ≤ ‖x‖) ∧
      (∀ v ∈ LinearMap.ker ((H + lam • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E), ⟪g, v⟫ = 0)) ∧
    (-leftmost hH < lam → particular hH g lam = step g H lam) := by
  set K := LinearMap.ker ((H + lam • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E)
  have hperp : particular hH g lam ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal']
    intro u hu
    rw [inner_eq_sum_eigenvectorBasis (hH := hH)]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [inner_eigenvectorBasis_particular]
    by_cases hi : lam + hH.eigenvalues rfl i = 0
    · simp [hi]
    · rw [(mul_eq_zero.1 ((mem_ker_add_smul_iff (hH := hH)).1 hu i)).resolve_left hi, mul_zero]
  refine ⟨hperp, fun hg => ?_, fun hlam => ?_⟩
  · have hγ : ∀ i, lam + hH.eigenvalues rfl i = 0 → ⟪hH.eigenvectorBasis rfl i, g⟫ = 0 :=
      fun i hi => Submodule.inner_right_of_mem_orthogonal (eigenvectorBasis_mem_ker hi) hg
    have hsol : (H + lam • 1) (particular hH g lam) = -g := by
      refine eq_of_inner_eigenvectorBasis (hH := hH) fun i => ?_
      rw [inner_eigenvectorBasis_add_smul, inner_eigenvectorBasis_particular, inner_neg_right]
      by_cases hi : lam + hH.eigenvalues rfl i = 0
      · rw [hi, hγ i hi]; simp
      · field_simp
    have hiff : ∀ x, (H + lam • 1) x = -g ↔ x - particular hH g lam ∈ K := fun x => by
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, hsol, sub_eq_zero]
    refine ⟨hsol, hiff, fun x hx => ?_, fun v hv => Submodule.inner_left_of_mem_orthogonal hv hg⟩
    have h0 : ⟪particular hH g lam, x - particular hH g lam⟫ = 0 :=
      Submodule.inner_left_of_mem_orthogonal ((hiff x).1 hx) hperp
    have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_real h0
    rw [add_sub_cancel] at hpy
    by_contra hlt
    push Not at hlt
    have := mul_self_lt_mul_self (norm_nonneg x) hlt
    nlinarith [mul_self_nonneg ‖x - particular hH g lam‖]
  · rw [step_eq_sum hlam, particular]

/-- **Behaviour at the threshold.** Let $H$ be a symmetric operator on a finite-dimensional real
inner product space $E$, let $g \in E$, and put $K = \ker(H - \lambda_1 I)$ and $s_s$ =
`Subproblem.particular` at $-\lambda_1$.
* (i) If $g \in K^\perp$, then $s(\lambda) \to s_s$ and $\pi(\lambda) \to \|s_s\|^2$ as
  $\lambda \downarrow -\lambda_1$.
* (ii) If $g \notin K^\perp$, then $\pi(\lambda) \to +\infty$ as
  $\lambda \downarrow -\lambda_1$.

By (i), $\pi$ extends continuously to $[-\lambda_1, \infty)$ when $g \in K^\perp$. This is how
the value $\pi(\lambda_s)$ of [cartis2022evaluation] is read. The operator $H - \lambda_1 I$ is
written `H + (-leftmost hH) • 1`. -/
theorem tendsto_step_threshold :
    (g ∈ (LinearMap.ker ((H + (-leftmost hH) • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ →
      Tendsto (step g H) (𝓝[>] (-leftmost hH)) (𝓝 (particular hH g (-leftmost hH))) ∧
      Tendsto (secular g H) (𝓝[>] (-leftmost hH)) (𝓝 (‖particular hH g (-leftmost hH)‖ ^ 2))) ∧
    (g ∉ (LinearMap.ker ((H + (-leftmost hH) • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ →
      Tendsto (secular g H) (𝓝[>] (-leftmost hH)) atTop) := by
  set L := leftmost hH
  have hev : step g H =ᶠ[𝓝[>] (-L)] particular hH g :=
    eventually_nhdsWithin_of_forall fun lam h => ((particular_spec (g := g) lam).2.2 h).symm
  refine ⟨fun hg => ?_, fun hg => ?_⟩
  · have hγ : ∀ i, -L + hH.eigenvalues rfl i = 0 → ⟪hH.eigenvectorBasis rfl i, g⟫ = 0 :=
      fun i hi => Submodule.inner_right_of_mem_orthogonal (eigenvectorBasis_mem_ker hi) hg
    have hcont : ContinuousAt (particular hH g) (-L) := by
      have : Tendsto (fun lam => ∑ i, (⟪hH.eigenvectorBasis rfl i, g⟫ /
          (lam + hH.eigenvalues rfl i)) • hH.eigenvectorBasis rfl i) (𝓝 (-L))
          (𝓝 (∑ i, (⟪hH.eigenvectorBasis rfl i, g⟫ /
          (-L + hH.eigenvalues rfl i)) • hH.eigenvectorBasis rfl i)) := by
        refine tendsto_finsetSum _ fun i _ => ?_
        by_cases hi : -L + hH.eigenvalues rfl i = 0
        · simp only [hγ i hi, zero_div, zero_smul]
          exact tendsto_const_nhds
        · exact ((continuousAt_const.div (continuousAt_id.add continuousAt_const) hi).smul
            continuousAt_const).tendsto
      exact this.neg
    have h1 : Tendsto (step g H) (𝓝[>] (-L)) (𝓝 (particular hH g (-L))) :=
      (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm
    exact ⟨h1, (h1.norm.pow 2)⟩
  · -- some eigenvector at `λ₁` carries weight
    obtain ⟨i, hi, hγi⟩ : ∃ i, -L + hH.eigenvalues rfl i = 0 ∧
        ⟪hH.eigenvectorBasis rfl i, g⟫ ≠ 0 := by
      by_contra h
      push Not at h
      refine hg ((Submodule.mem_orthogonal _ _).2 fun v hv => ?_)
      rw [inner_eq_sum_eigenvectorBasis (hH := hH)]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : -L + hH.eigenvalues rfl j = 0
      · rw [h j hj, mul_zero]
      · rw [(mul_eq_zero.1 ((mem_ker_add_smul_iff (hH := hH)).1 hv j)).resolve_left hj,
          zero_mul]
    have hshift : Tendsto (fun lam => lam + L) (𝓝[>] (-L)) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun lam h => ?_⟩
      · exact ((continuous_id.add continuous_const).tendsto' (-L) 0 (neg_add_cancel _)).mono_left
          nhdsWithin_le_nhds
      · simp only [mem_Ioi] at h ⊢; linarith
    have hlim : Tendsto (fun lam => secularWeight hH g i * ((lam + L)⁻¹) ^ 2)
        (𝓝[>] (-L)) atTop :=
      (((tendsto_pow_atTop two_ne_zero).comp (tendsto_inv_nhdsGT_zero.comp hshift))).const_mul_atTop
        (by simp only [secularWeight]; positivity)
    refine tendsto_atTop_mono' _ (eventually_nhdsWithin_of_forall fun lam h => ?_) hlim
    rw [secular_eq_secularSum h, secularSum_apply]
    have hL : lam + hH.eigenvalues rfl i = lam + L := by linarith
    calc secularWeight hH g i * ((lam + L)⁻¹) ^ 2
        = secularWeight hH g i / (lam + hH.eigenvalues rfl i) ^ 2 := by
          rw [hL, div_eq_mul_inv, inv_pow]
      _ ≤ _ := Finset.single_le_sum (f := fun j => secularWeight hH g j /
          (lam + hH.eigenvalues rfl j) ^ 2)
          (fun j _ => div_nonneg (secularWeight_nonneg j) (sq_nonneg _)) (Finset.mem_univ i)

/-! ### Derivatives -/

/-- The **$k$-th derivative of the step**:
$$s^{(k)}(\lambda) = (-1)^{k+1} k! \, (H + \lambda I)^{-(k+1)} g,$$
with the inverse given by `Ring.inverse`.

`Subproblem.iteratedDeriv_step` shows that it is the $k$-th derivative of $s$ for
$\lambda > -\lambda_1$. For $k = 0$ it is the step $s(\lambda)$ (`Subproblem.stepDeriv_zero`). -/
noncomputable def stepDeriv (g : E) (H : E →L[ℝ] E) (k : ℕ) (lam : ℝ) : E :=
  (((-1 : ℝ) ^ (k + 1) * k !) • (Ring.inverse (H + lam • 1) ^ (k + 1))) g

omit [FiniteDimensional ℝ E] in
/-- For $k = 0$, $s^{(0)}(\lambda)$ is the step $s(\lambda)$, for every $\lambda$. -/
theorem stepDeriv_zero (lam : ℝ) : stepDeriv g H 0 lam = step g H lam := by
  simp [stepDeriv, step]

/-- For $\lambda > -\lambda_1$ and every $m \in \mathbb{N}$, the coordinates of
$(H + \lambda I)^{-m} v$ are $\langle b_i, (H + \lambda I)^{-m} v \rangle = \langle b_i, v
\rangle / (\lambda + \lambda_i)^m$. -/
theorem inner_eigenvectorBasis_inverse_pow {lam : ℝ} (hlam : -leftmost hH < lam) (m : ℕ)
    (v : E) (i : Fin (Module.finrank ℝ E)) :
    ⟪hH.eigenvectorBasis rfl i, (Ring.inverse (H + lam • 1) ^ m) v⟫ =
      ⟪hH.eigenvectorBasis rfl i, v⟫ / (lam + hH.eigenvalues rfl i) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ']
    change ⟪_, Ring.inverse (H + lam • 1) ((Ring.inverse (H + lam • 1) ^ m) v)⟫ = _
    rw [inner_eigenvectorBasis_eq_div hlam
      (add_smul_inverse_apply hlam _) i, ih, div_div, pow_succ]

/-- For $\lambda > -\lambda_1$, the coordinates of $s^{(k)}(\lambda)$ are $\langle b_i,
s^{(k)}(\lambda) \rangle = (-1)^{k+1} k! \, \langle b_i, g \rangle / (\lambda +
\lambda_i)^{k+1}$. -/
theorem inner_eigenvectorBasis_stepDeriv {lam : ℝ} (hlam : -leftmost hH < lam) (k : ℕ)
    (i : Fin (Module.finrank ℝ E)) :
    ⟪hH.eigenvectorBasis rfl i, stepDeriv g H k lam⟫ =
      (-1) ^ (k + 1) * k ! * ⟪hH.eigenvectorBasis rfl i, g⟫ /
        (lam + hH.eigenvalues rfl i) ^ (k + 1) := by
  rw [stepDeriv, smul_apply, real_inner_smul_right,
    inner_eigenvectorBasis_inverse_pow hlam, mul_div_assoc]

/-- The spectral expansion of the $k$-th derivative of the step: for $\lambda > -\lambda_1$,
$$s^{(k)}(\lambda) = \sum_i \frac{(-1)^{k+1} k! \, \langle b_i, g \rangle}{(\lambda +
  \lambda_i)^{k+1}} b_i.$$
-/
theorem stepDeriv_eq_sum {lam : ℝ} (hlam : -leftmost hH < lam) (k : ℕ) :
    stepDeriv g H k lam = ∑ i, ((-1) ^ (k + 1) * k ! * ⟪hH.eigenvectorBasis rfl i, g⟫ /
      (lam + hH.eigenvalues rfl i) ^ (k + 1)) • hH.eigenvectorBasis rfl i :=
  eq_of_inner_eigenvectorBasis (hH := hH) fun i => by
    rw [inner_eigenvectorBasis_stepDeriv hlam, inner_eigenvectorBasis_sum]

/-- For $\lambda > -\lambda_1$, the map $\lambda \mapsto s^{(k)}(\lambda)$ has the derivative
$s^{(k+1)}(\lambda)$. -/
theorem hasDerivAt_stepDeriv {lam : ℝ} (hlam : -leftmost hH < lam) (k : ℕ) :
    HasDerivAt (stepDeriv g H k) (stepDeriv g H (k + 1) lam) lam := by
  have hev : stepDeriv g H k =ᶠ[𝓝 lam] fun t => ∑ i, ((-1) ^ (k + 1) * k ! *
      ⟪hH.eigenvectorBasis rfl i, g⟫ / (t + hH.eigenvalues rfl i) ^ (k + 1)) •
        hH.eigenvectorBasis rfl i :=
    Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hlam) fun t ht => stepDeriv_eq_sum ht k
  have hD := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    (hasDerivAt_div_add_pow ((-1) ^ (k + 1) * k ! * ⟪hH.eigenvectorBasis rfl i, g⟫)
      (hH.eigenvalues rfl i) (k + 1) (mem_secularDomain_of_lt hlam i).ne').smul_const
      (hH.eigenvectorBasis rfl i)
  refine (hD.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [stepDeriv_eq_sum hlam (k + 1)]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [Nat.factorial_succ]
  push_cast
  ring

/-- **Derivatives of the step.** Let $H$ be a symmetric operator on a finite-dimensional real inner
product space $E$, let $g \in E$, and let $\lambda > -\lambda_1$. Then for every
$k \in \mathbb{N}$, the $k$-th derivative of the step at $\lambda$ is $s^{(k)}(\lambda)$
(`Subproblem.stepDeriv`), and
$$(H + \lambda I) s^{(k+1)}(\lambda) = -(k + 1) s^{(k)}(\lambda).$$

The solves are (8.2.29) of [cartis2022evaluation]. They compute the derivatives recursively. -/
theorem iteratedDeriv_step {lam : ℝ} (hlam : -leftmost hH < lam) (k : ℕ) :
    iteratedDeriv k (step g H) lam = stepDeriv g H k lam ∧
      (H + lam • 1) (stepDeriv g H (k + 1) lam) = -((k + 1 : ℝ) • stepDeriv g H k lam) := by
  constructor
  · induction k generalizing lam with
    | zero => rw [iteratedDeriv_zero, stepDeriv_zero]
    | succ k ih =>
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv k (step g H) =ᶠ[𝓝 lam] stepDeriv g H k :=
        Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hlam) fun t ht => ih ht
      rw [hev.deriv_eq, (hasDerivAt_stepDeriv hlam k).deriv]
  · refine eq_of_inner_eigenvectorBasis (hH := hH) fun i => ?_
    have ha : lam + hH.eigenvalues rfl i ≠ 0 := (mem_secularDomain_of_lt hlam i).ne'
    rw [inner_eigenvectorBasis_add_smul, inner_eigenvectorBasis_stepDeriv hlam, inner_neg_right,
      real_inner_smul_right, inner_eigenvectorBasis_stepDeriv hlam, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- The coefficients $\alpha_k = \dfrac{(2k + 1)!}{(k!)^2}$ of Theorem 8.2.6 of
[cartis2022evaluation]. -/
noncomputable def secularCoeff (k : ℕ) : ℝ := ((2 * k + 1)! : ℝ) / (k ! : ℝ) ^ 2

/-- The first coefficient is $\alpha_0 = 1$. -/
@[simp]
theorem secularCoeff_zero : secularCoeff 0 = 1 := by simp [secularCoeff]

/-- The recursion $\alpha_{k+1} = \dfrac{2 (2k + 3)}{k + 1} \alpha_k$, which is (8.2.30) of
[cartis2022evaluation]. -/
theorem secularCoeff_succ (k : ℕ) :
    secularCoeff (k + 1) = 2 * (2 * k + 3) / (k + 1) * secularCoeff k := by
  rw [secularCoeff, secularCoeff, show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring,
    Nat.factorial_succ (2 * k + 1 + 1), Nat.factorial_succ (2 * k + 1), Nat.factorial_succ k]
  push_cast
  field_simp
  ring

/-- The derivatives of the secular function in closed form: for $\lambda > -\lambda_1$ and every
$j \in \mathbb{N}$,
$$\pi^{(j)}(\lambda) = (-1)^j (j + 1)! \sum_i \frac{\langle b_i, g \rangle^2}{(\lambda +
  \lambda_i)^{j+2}}.$$
This is (B.8.8) of [cartis2022evaluation]. -/
theorem iteratedDeriv_secular_eq {lam : ℝ} (hlam : -leftmost hH < lam) (j : ℕ) :
    iteratedDeriv j (secular g H) lam = (-1) ^ j * (j + 1)! *
      secularMoment (hH.eigenvalues rfl) (secularWeight hH g) (j + 2) lam := by
  rw [(secular_eventuallyEq hlam).iteratedDeriv_eq j,
    iteratedDeriv_secularSum j fun i => (mem_secularDomain_of_lt hlam i).ne']

/-- **Derivatives of the secular function.** Let $H$ be a symmetric operator on a finite-dimensional
real inner product space $E$, let $g \in E$, and let $\lambda > -\lambda_1$. Then for every
$k \in \mathbb{N}$, with $s^{(j)} = s^{(j)}(\lambda)$ the derivatives of the step and $\alpha_k$
the coefficients `Subproblem.secularCoeff`,
$$\pi^{(2k+1)}(\lambda) = 2 \alpha_k \langle s^{(k)}, s^{(k+1)} \rangle, \qquad
  \pi^{(2k+2)}(\lambda) = \alpha_{k+1} \|s^{(k+1)}\|^2.$$

This is Theorem 8.2.6 of [cartis2022evaluation]. The vectors $s^{(j)}$ are
`Subproblem.stepDeriv`, computed by the solves of `Subproblem.iteratedDeriv_step`. -/
theorem iteratedDeriv_secular {lam : ℝ} (hlam : -leftmost hH < lam) (k : ℕ) :
    iteratedDeriv (2 * k + 1) (secular g H) lam =
        2 * secularCoeff k * ⟪stepDeriv g H k lam, stepDeriv g H (k + 1) lam⟫ ∧
      iteratedDeriv (2 * k + 2) (secular g H) lam =
        secularCoeff (k + 1) * ‖stepDeriv g H (k + 1) lam‖ ^ 2 := by
  have hk : (k ! : ℝ) ≠ 0 := by positivity
  constructor
  · rw [iteratedDeriv_secular_eq hlam, inner_eq_sum_eigenvectorBasis (hH := hH),
      secularMoment_apply, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have ha : lam + hH.eigenvalues rfl i ≠ 0 := (mem_secularDomain_of_lt hlam i).ne'
    rw [inner_eigenvectorBasis_stepDeriv hlam, inner_eigenvectorBasis_stepDeriv hlam,
      secularCoeff, secularWeight, show 2 * k + 1 + 1 = (2 * k + 1) + 1 by ring,
      Nat.factorial_succ (2 * k + 1), Nat.factorial_succ k]
    push_cast
    field_simp
    ring
  · rw [iteratedDeriv_secular_eq hlam, ← real_inner_self_eq_norm_sq,
      inner_eq_sum_eigenvectorBasis (hH := hH), secularMoment_apply, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have ha : lam + hH.eigenvalues rfl i ≠ 0 := (mem_secularDomain_of_lt hlam i).ne'
    rw [inner_eigenvectorBasis_stepDeriv hlam, secularCoeff, secularWeight,
      show 2 * (k + 1) + 1 = 2 * k + 2 + 1 by ring]
    have hk1 : ((k + 1)! : ℝ) ≠ 0 := by positivity
    field_simp
    ring

/-! ### Taylor estimates -/

/-- For $\lambda > -\lambda_1$, the Taylor polynomials of $\pi$ at $\lambda$ equal those of its
spectral form `Subproblem.secularSum`. -/
theorem sum_taylor_secular_eq {lam : ℝ} (hlam : -leftmost hH < lam) (m : ℕ) (δ : ℝ) :
    ∑ j ∈ range m, iteratedDeriv j (secular g H) lam / j ! * δ ^ j =
      ∑ j ∈ range m, iteratedDeriv j
        (secularSum (hH.eigenvalues rfl) (secularWeight hH g)) lam / j ! * δ ^ j :=
  Finset.sum_congr rfl fun j _ => by rw [(secular_eventuallyEq hlam).iteratedDeriv_eq j]

/-- **Lower and upper Taylor estimates of the secular function.** Let $H$ be a symmetric operator on
a finite-dimensional real inner product space $E$, let $g \in E$, let $\lambda_c > -\lambda_1$
and $k \in \mathbb{N}$, and let
$$t_k(\delta) = \sum_{j=0}^{k} \frac{\pi^{(j)}(\lambda_c)}{j!} \delta^j.$$
Then:
* for $\delta > 0$, $\pi(\lambda_c + \delta) \le t_k(\delta)$ if $k$ is even, and
  $t_k(\delta) \le \pi(\lambda_c + \delta)$ if $k$ is odd;
* for $\delta < 0$ with $\lambda_c + \delta > -\lambda_1$, $t_k(\delta) \le t_{k+1}(\delta) \le
  \pi(\lambda_c + \delta)$.

This is Theorem 8.2.2 of [cartis2022evaluation]. The interval $\lambda > -\lambda_1$ contains
the interval $(\lambda_s, \infty)$ of the source. The strict forms for $g \neq 0$ are
`Subproblem.secular_taylor_bounds_strict`. -/
theorem secular_taylor_bounds {lamc : ℝ} (hlam : -leftmost hH < lamc) (k : ℕ) :
    (∀ δ, 0 < δ → (Even k → secular g H (lamc + δ) ≤
        ∑ j ∈ range (k + 1), iteratedDeriv j (secular g H) lamc / j ! * δ ^ j) ∧
      (Odd k → ∑ j ∈ range (k + 1), iteratedDeriv j (secular g H) lamc / j ! * δ ^ j ≤
        secular g H (lamc + δ))) ∧
    (∀ δ, δ < 0 → -leftmost hH < lamc + δ →
      ∑ j ∈ range (k + 1), iteratedDeriv j (secular g H) lamc / j ! * δ ^ j ≤
        ∑ j ∈ range (k + 2), iteratedDeriv j (secular g H) lamc / j ! * δ ^ j ∧
      ∑ j ∈ range (k + 2), iteratedDeriv j (secular g H) lamc / j ! * δ ^ j ≤
        secular g H (lamc + δ)) := by
  obtain ⟨hpos, hneg⟩ := secularSum_taylor_bounds secularWeight_nonneg
    (mem_secularDomain_of_lt hlam) k
  simp only [sum_taylor_secular_eq hlam]
  refine ⟨fun δ hδ => ?_, fun δ hδ hlamδ => ?_⟩
  · rw [secular_eq_secularSum (by linarith : -leftmost hH < lamc + δ)]
    exact hpos δ hδ
  · rw [secular_eq_secularSum hlamδ]
    exact hneg δ hδ (mem_secularDomain_of_lt hlamδ)

/-- The strict Taylor estimates of the secular function. Let $g \neq 0$, $\lambda_c > -\lambda_1$
and $k \in \mathbb{N}$, with $t_k$ as in `Subproblem.secular_taylor_bounds`. For $\delta > 0$,
$\pi(\lambda_c + \delta) < t_k(\delta)$ if $k$ is even and
$t_k(\delta) < \pi(\lambda_c + \delta)$ if $k$ is odd. For $\delta < 0$ with
$\lambda_c + \delta > -\lambda_1$, $t_k(\delta) < t_{k+1}(\delta) < \pi(\lambda_c + \delta)$.
This is the strict part of Theorem 8.2.2 of [cartis2022evaluation]. -/
theorem secular_taylor_bounds_strict (hg : g ≠ 0) {lamc : ℝ} (hlam : -leftmost hH < lamc)
    (k : ℕ) :
    (∀ δ, 0 < δ → (Even k → secular g H (lamc + δ) <
        ∑ j ∈ range (k + 1), iteratedDeriv j (secular g H) lamc / j ! * δ ^ j) ∧
      (Odd k → ∑ j ∈ range (k + 1), iteratedDeriv j (secular g H) lamc / j ! * δ ^ j <
        secular g H (lamc + δ))) ∧
    (∀ δ, δ < 0 → -leftmost hH < lamc + δ →
      ∑ j ∈ range (k + 1), iteratedDeriv j (secular g H) lamc / j ! * δ ^ j <
        ∑ j ∈ range (k + 2), iteratedDeriv j (secular g H) lamc / j ! * δ ^ j ∧
      ∑ j ∈ range (k + 2), iteratedDeriv j (secular g H) lamc / j ! * δ ^ j <
        secular g H (lamc + δ)) := by
  obtain ⟨hpos, hneg⟩ := secularSum_taylor_bounds_strict secularWeight_nonneg
    ((secularWeight_ne_zero_iff (hH := hH)).2 hg) (mem_secularDomain_of_lt hlam) k
  simp only [sum_taylor_secular_eq hlam]
  refine ⟨fun δ hδ => ?_, fun δ hδ hlamδ => ?_⟩
  · rw [secular_eq_secularSum (by linarith : -leftmost hH < lamc + δ)]
    exact hpos δ hδ
  · rw [secular_eq_secularSum hlamδ]
    exact hneg δ hδ (mem_secularDomain_of_lt hlamδ)

/-! ### The transformed secular function -/

/-- For $\lambda > -\lambda_1$ and $\beta \in \mathbb{R}$, the function $t \mapsto \pi(t)^\beta$
agrees near $\lambda$ with the $\beta$-th power of the spectral form `Subproblem.secularSum`. -/
theorem secular_rpow_eventuallyEq {lam : ℝ} (hlam : -leftmost hH < lam) (β : ℝ) :
    (fun t => secular g H t ^ β) =ᶠ[𝓝 lam]
      fun t => secularSum (hH.eigenvalues rfl) (secularWeight hH g) t ^ β :=
  (secular_eventuallyEq (g := g) hlam).mono fun t ht => by simp only [ht]

/-- **Derivatives of the transformed secular function.** Let $g \neq 0$, $\lambda > -\lambda_1$ and
$\beta \in \mathbb{R}$, and let $q(t) = \pi(t)^\beta$. Then:
* if $\beta > 0$, then $q'(\lambda) < 0$ and $q''(\lambda) > 0$;
* if $\beta < 0$, then $q'(\lambda) > 0$;
* if $-1/2 \le \beta < 0$, then $q''(\lambda) \le 0$, and $q''(\lambda) < 0$ unless
  $\beta = -1/2$ and $g$ is an eigenvector of $H$;
* if $\beta = -1/2$ and $H g = c g$ for some $c \in \mathbb{R}$, then $q''(\lambda) = 0$.

This is Lemma 8.2.3 of [cartis2022evaluation], on the interval $\lambda > -\lambda_1$. -/
theorem secular_rpow_deriv_sign (hg : g ≠ 0) {lam : ℝ} (hlam : -leftmost hH < lam) (β : ℝ) :
    (0 < β → deriv (fun t => secular g H t ^ β) lam < 0) ∧
    (β < 0 → 0 < deriv (fun t => secular g H t ^ β) lam) ∧
    (0 < β → 0 < iteratedDeriv 2 (fun t => secular g H t ^ β) lam) ∧
    (β ∈ Ico (-1 / 2) 0 → iteratedDeriv 2 (fun t => secular g H t ^ β) lam ≤ 0) ∧
    (β ∈ Ico (-1 / 2) 0 → (β ≠ -1 / 2 ∨ ¬ ∃ c : ℝ, H g = c • g) →
      iteratedDeriv 2 (fun t => secular g H t ^ β) lam < 0) ∧
    (β = -1 / 2 → (∃ c : ℝ, H g = c • g) →
      iteratedDeriv 2 (fun t => secular g H t ^ β) lam = 0) := by
  have hev := secular_rpow_eventuallyEq (g := g) hlam β
  rw [hev.deriv_eq, hev.iteratedDeriv_eq, ← singlePole_secularWeight_iff hg]
  exact secularSum_rpow_deriv_sign secularWeight_nonneg
    ((secularWeight_ne_zero_iff (hH := hH)).2 hg) β (mem_secularDomain_of_lt hlam)

/-- **First-order Taylor estimates of the transformed secular function.** Let $g \neq 0$, let
$\lambda_c > -\lambda_1$ and $\delta \in \mathbb{R}$ with $\lambda_c + \delta > -\lambda_1$, let
$\beta \in \mathbb{R}$, let $q(t) = \pi(t)^\beta$, and let $t_1(\delta) = q(\lambda_c) +
q'(\lambda_c) \delta$. Then:
* if $\beta > 0$, then $t_1(\delta) \le q(\lambda_c + \delta)$, strictly when $\delta \neq 0$;
* if $-1/2 \le \beta < 0$, then $q(\lambda_c + \delta) \le t_1(\delta)$, strictly when
  $\delta \neq 0$ unless $\beta = -1/2$ and $g$ is an eigenvector of $H$;
* if $\beta = -1/2$ and $H g = c g$ for some $c \in \mathbb{R}$, then $q$ is affine and
  $q(\lambda_c + \delta) = t_1(\delta)$.

This is Theorem 8.2.5 of [cartis2022evaluation], on the interval $\lambda > -\lambda_1$. The
sign statements of Lemma 8.2.3 are `Subproblem.secular_rpow_deriv_sign`. -/
theorem secular_rpow_tangent (hg : g ≠ 0) {lamc δ : ℝ} (hlam : -leftmost hH < lamc)
    (hlamδ : -leftmost hH < lamc + δ) (β : ℝ) :
    (0 < β → secular g H lamc ^ β + deriv (fun t => secular g H t ^ β) lamc * δ ≤
      secular g H (lamc + δ) ^ β) ∧
    (0 < β → δ ≠ 0 → secular g H lamc ^ β + deriv (fun t => secular g H t ^ β) lamc * δ <
      secular g H (lamc + δ) ^ β) ∧
    (β ∈ Ico (-1 / 2) 0 → secular g H (lamc + δ) ^ β ≤
      secular g H lamc ^ β + deriv (fun t => secular g H t ^ β) lamc * δ) ∧
    (β ∈ Ico (-1 / 2) 0 → δ ≠ 0 → (β ≠ -1 / 2 ∨ ¬ ∃ c : ℝ, H g = c • g) →
      secular g H (lamc + δ) ^ β <
        secular g H lamc ^ β + deriv (fun t => secular g H t ^ β) lamc * δ) ∧
    (β = -1 / 2 → (∃ c : ℝ, H g = c • g) → secular g H (lamc + δ) ^ β =
      secular g H lamc ^ β + deriv (fun t => secular g H t ^ β) lamc * δ) := by
  rw [(secular_rpow_eventuallyEq (g := g) hlam β).deriv_eq, secular_eq_secularSum hlam,
    secular_eq_secularSum hlamδ, ← singlePole_secularWeight_iff hg]
  exact secularSum_rpow_tangent secularWeight_nonneg
    ((secularWeight_ne_zero_iff (hH := hH)).2 hg) β (mem_secularDomain_of_lt hlam)
    (mem_secularDomain_of_lt hlamδ)

/-- For $\lambda > -\lambda_1$, the only solution $s$ of
$(H + \lambda I) s = -(k + 1) s^{(k)}(\lambda)$ is $s^{(k+1)}(\lambda)$. So the solves (8.2.29)
of [cartis2022evaluation] determine the derivatives of the step. -/
theorem stepDeriv_succ_unique {lam : ℝ} (hlam : -leftmost hH < lam) (k : ℕ) {s : E}
    (hs : (H + lam • 1) s = -((k + 1 : ℝ) • stepDeriv g H k lam)) :
    s = stepDeriv g H (k + 1) lam :=
  injective_add_smul hlam (hs.trans (iteratedDeriv_step hlam k).2.symm)

omit [FiniteDimensional ℝ E] in
/-- For $g = 0$ the secular function is identically $0$. -/
theorem secular_zero_left (H : E →L[ℝ] E) : secular 0 H = 0 := by
  ext lam
  simp [secular, step]

omit [FiniteDimensional ℝ E] in
/-- The degenerate case $g = 0$ of Lemma 8.2.3 of [cartis2022evaluation]: the function
$t \mapsto \pi(t)^\beta$ is constant, so all its derivatives of order $n + 1 \ge 1$ vanish.
Hence the non-strict sign statements hold trivially. -/
theorem secular_rpow_zero_left (H : E →L[ℝ] E) (β lam : ℝ) (n : ℕ) :
    iteratedDeriv (n + 1) (fun t => secular 0 H t ^ β) lam = 0 := by
  simp only [secular_zero_left, Pi.zero_apply]
  rw [iteratedDeriv_succ']
  simp

/-- Let $g \neq 0$ and $-1/2 \le \beta < 0$, and suppose that $\beta \neq -1/2$ or $g$ is not an
eigenvector of $H$. Then the transformed secular function $\lambda \mapsto \pi(\lambda)^\beta$
is strictly concave on $(-\lambda_1, \infty)$. In the excluded case it is affine. -/
theorem secular_rpow_strictConcaveOn (hg : g ≠ 0) {β : ℝ} (hβ : β ∈ Ico (-1 / 2) 0)
    (hne : β ≠ -1 / 2 ∨ ¬ ∃ c : ℝ, H g = c • g) :
    StrictConcaveOn ℝ (Ioi (-leftmost hH)) (fun t => secular g H t ^ β) := by
  rw [← singlePole_secularWeight_iff hg] at hne
  refine ((secularSum_rpow_strictConcaveOn secularWeight_nonneg
    ((secularWeight_ne_zero_iff (hH := hH)).2 hg) β hβ hne).subset Ioi_subset_secularDomain
    (convex_Ioi _)).congr fun t ht => ?_
  simp only [secular_eq_secularSum ht]

/-- The transformed secular function at the threshold. Let $K = \ker(H - \lambda_1 I)$ and $s_s$ =
`Subproblem.particular` at $-\lambda_1$. As $\lambda \downarrow -\lambda_1$:
* if $g \in K^\perp$, and $s_s \neq 0$ or $\beta \ge 0$, then
  $\pi(\lambda)^\beta \to (\|s_s\|^2)^\beta$;
* if $g \notin K^\perp$, then $\pi(\lambda)^\beta \to +\infty$ for $\beta > 0$ and
  $\pi(\lambda)^\beta \to 0$ for $\beta < 0$. -/
theorem tendsto_secular_rpow_threshold (β : ℝ) :
    (g ∈ (LinearMap.ker ((H + (-leftmost hH) • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ →
      (particular hH g (-leftmost hH) ≠ 0 ∨ 0 ≤ β) →
      Tendsto (fun t => secular g H t ^ β) (𝓝[>] (-leftmost hH))
        (𝓝 ((‖particular hH g (-leftmost hH)‖ ^ 2) ^ β))) ∧
    (g ∉ (LinearMap.ker ((H + (-leftmost hH) • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ →
      (0 < β → Tendsto (fun t => secular g H t ^ β) (𝓝[>] (-leftmost hH)) atTop) ∧
      (β < 0 → Tendsto (fun t => secular g H t ^ β) (𝓝[>] (-leftmost hH)) (𝓝 0))) := by
  refine ⟨fun hg h => ?_, fun hg => ⟨fun hβ => ?_, fun hβ => ?_⟩⟩
  · have h' : ‖particular hH g (-leftmost hH)‖ ^ 2 ≠ 0 ∨ 0 ≤ β :=
      h.imp_left fun hp => pow_ne_zero 2 (norm_ne_zero_iff.2 hp)
    exact (Real.continuousAt_rpow_const _ β h').tendsto.comp
      ((tendsto_step_threshold (hH := hH)).1 hg).2
  · exact (tendsto_rpow_atTop hβ).comp ((tendsto_step_threshold (hH := hH)).2 hg)
  · have := (tendsto_rpow_neg_atTop (neg_pos.2 hβ)).comp
      ((tendsto_step_threshold (hH := hH)).2 hg)
    simpa only [neg_neg, Function.comp_def] using this

/-! ### Calculus facts about the secular function -/

section SecularCalculus

variable {g : E} {hH : (H : E →ₗ[ℝ] E).IsSymmetric}

/-- For $\lambda > -\lambda_1$, the secular function $\pi$ is differentiable at $\lambda$. -/
theorem hasDerivAt_secular {lam : ℝ} (hlam : -leftmost hH < lam) :
    HasDerivAt (secular g H) (deriv (secular g H) lam) lam :=
  ((hasDerivAt_secularSum (μ := hH.eigenvalues rfl) (w := secularWeight hH g)
    fun i => (mem_secularDomain_of_lt hlam i).ne').congr_of_eventuallyEq
      (secular_eventuallyEq hlam)).differentiableAt.hasDerivAt

/-- For $g \neq 0$ and $\lambda > -\lambda_1$, $\pi(\lambda) > 0$. -/
theorem secular_pos (hg : g ≠ 0) {lam : ℝ} (hlam : -leftmost hH < lam) : 0 < secular g H lam :=
  (secular_shape (hH := hH) hg 0).1 lam hlam

/-- For $g \neq 0$ and $\lambda > -\lambda_1$, $\pi'(\lambda) < 0$. This follows from (8.2.4) and
Theorem 8.2.6 of [cartis2022evaluation]. -/
theorem deriv_secular_neg (hg : g ≠ 0) {lam : ℝ} (hlam : -leftmost hH < lam) :
    deriv (secular g H) lam < 0 := by
  rw [(secular_eventuallyEq hlam).deriv_eq,
    deriv_secularSum fun i => (mem_secularDomain_of_lt hlam i).ne']
  have := secularMoment_pos secularWeight_nonneg ((secularWeight_ne_zero_iff (hH := hH)).2 hg)
    (mem_secularDomain_of_lt hlam) 3
  linarith

/-- The derivative of the transformed secular function: for $g \neq 0$, $\lambda > -\lambda_1$ and
$\beta \in \mathbb{R}$,
$$(\pi^\beta)'(\lambda) = \beta \, \pi(\lambda)^{\beta - 1} \pi'(\lambda).$$
This is (8.2.18) of [cartis2022evaluation]. -/
theorem hasDerivAt_secular_rpow (hg : g ≠ 0) {lam : ℝ} (hlam : -leftmost hH < lam) (β : ℝ) :
    HasDerivAt (fun t => secular g H t ^ β)
      (β * secular g H lam ^ (β - 1) * deriv (secular g H) lam) lam := by
  convert (hasDerivAt_secular hlam).rpow_const (p := β) (Or.inl (secular_pos hg hlam).ne') using 1
  ring

/-- The second derivative of the transformed secular function. Let $H$ be a symmetric operator on a
finite-dimensional real inner product space $E$, let $g \in E$ with $g \neq 0$, let
$\lambda > -\lambda_1$ and $\beta \in \mathbb{R}$. Then
$$(\pi^\beta)''(\lambda) = \beta \, \pi(\lambda)^{\beta - 1} \pi''(\lambda) + \beta (\beta - 1)
  \, \pi(\lambda)^{\beta - 2} \pi'(\lambda)^2.$$
-/
theorem iteratedDeriv_two_secular_rpow (hg : g ≠ 0) {lam : ℝ}
    (hlam : -leftmost hH < lam) (β : ℝ) :
    iteratedDeriv 2 (fun t => secular g H t ^ β) lam =
      β * secular g H lam ^ (β - 1) * iteratedDeriv 2 (secular g H) lam +
        β * (β - 1) * secular g H lam ^ (β - 2) * deriv (secular g H) lam ^ 2 := by
  rw [(secular_rpow_eventuallyEq (g := g) hlam β).iteratedDeriv_eq,
    (secular_eventuallyEq (g := g) hlam).iteratedDeriv_eq,
    (secular_eventuallyEq (g := g) hlam).deriv_eq, secular_eq_secularSum hlam]
  exact iteratedDeriv_two_secularSum_rpow secularWeight_nonneg
    ((secularWeight_ne_zero_iff (hH := hH)).2 hg) β (mem_secularDomain_of_lt hlam)

/-- For $g \neq 0$ and $\beta \in \mathbb{R}$, the function $\lambda \mapsto \pi(\lambda)^\beta$ is
$C^n$ on $(-\lambda_1, \infty)$ for every smoothness order $n$, including $n = \infty$ and the
analytic order $\omega$. -/
theorem contDiffOn_secular_rpow (hg : g ≠ 0) (β : ℝ) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (fun t => secular g H t ^ β) (Ioi (-leftmost hH)) :=
  ((contDiffOn_secularSum_rpow secularWeight_nonneg
    ((secularWeight_ne_zero_iff (hH := hH)).2 hg) β).mono Ioi_subset_secularDomain).congr
    fun x hx => by simp only [secular_eq_secularSum hx]

/-- For $-\lambda_1 < x_0 \le x$ and every $m \in \mathbb{N}$, the spectral moments decrease:
$\sum_i \gamma_i^2 / (x + \lambda_i)^m \le \sum_i \gamma_i^2 / (x_0 + \lambda_i)^m$
(`Subproblem.secularMoment`). -/
theorem secularMoment_le_of_le {x₀ x : ℝ} (hx₀ : -leftmost hH < x₀) (hx : x₀ ≤ x) (m : ℕ) :
    secularMoment (hH.eigenvalues rfl) (secularWeight hH g) m x ≤
      secularMoment (hH.eigenvalues rfl) (secularWeight hH g) m x₀ := by
  have h0 := mem_secularDomain_of_lt hx₀
  refine Finset.sum_le_sum fun i _ => div_le_div_of_nonneg_left (secularWeight_nonneg i)
    (pow_pos (h0 i) m) (pow_le_pow_left₀ (h0 i).le (by linarith) m)

end SecularCalculus

omit [FiniteDimensional ℝ E] in
/-- If $\pi(\lambda) > 0$ for some $\lambda$, then $g \neq 0$. -/
theorem ne_zero_of_secular_pos {lam : ℝ} (h : 0 < secular g H lam) : g ≠ 0 := by
  rintro rfl
  simp [secular_zero_left] at h

end Subproblem
