/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Module.Normalize
import Numlib.Nonlinear.Order
import Numlib.Optimization.Subproblem.Secular

/-!
# Inverse iteration with Rayleigh-quotient shifts from the definite side

Let $H$ be a symmetric operator on a finite-dimensional real inner product space $E$, with
eigenvalues $\lambda_1 \le \dots \le \lambda_n$, leftmost eigenspace $E_1 = \ker(H - \lambda_1)$ and
orthogonal projection $P_1$ onto $E_1$. Algorithm 9.3.1 of [cartis2022evaluation], which follows
Gould, Robinson and Thorne, produces shifts $\ell_k > -\lambda_1$, so that each $H + \ell_k$ is
positive definite, and these shifts converge to $-\lambda_1$ with any prescribed Q-order. From a
unit vector $z_k$ it performs $n_k$ steps of shifted inverse iteration
$z \mapsto (H + \ell_k)^{-1} z$, normalizes the result to $z_{k+1}$, computes the Rayleigh quotient
$\rho_{k+1} = \langle z_{k+1}, H z_{k+1} \rangle \ge \lambda_1$, and sets
$$\ell_{k+1} = -\rho_{k+1} + \omega_k (\ell_k + \rho_{k+1})^{\gamma_k}.$$

The file first expresses $P_1$ and the squared norms $\|P_1 z\|^2$ and $\|(1 - P_1) z\|^2$ in an
orthonormal eigenvector basis. It then proves that the Rayleigh quotient of a unit vector has an
error of at most $(\lambda_n - \lambda_1) \|(1 - P_1) z\|^2$, and that $n$ steps of shifted inverse
iteration multiply the squared tangent $\|(1 - P_1) z\|^2 / \|P_1 z\|^2$ by at most $((\ell +
\lambda_1) / (\ell + \lambda_1 + \mu))^{2n}$, where $\mu$ is a lower bound of the gap between
$\lambda_1$ and the other eigenvalues. These two facts give Theorem 9.3.1: from a start close enough
to $-\lambda_1$, the errors $e_k = \ell_k + \lambda_1$ satisfy $\frac{\omega_L}{2} e_k^{\gamma_k}
\le e_{k+1} \le \omega_U 2^{\gamma_k} e_k^{\gamma_k}$.

## Main definitions

* `Subproblem.leftmostSpace`: the leftmost eigenspace $E_1$.
* `Subproblem.leftmostWeight`, `Subproblem.restWeight`: the squared norms $\|P_1 z\|^2$ and
  $\|(1 - P_1) z\|^2$, written in the eigenvector basis.
* `Subproblem.IsInverseIterationRun`: a run of Algorithm 9.3.1.

## Main results

* `Subproblem.starProjection_leftmostSpace`, `Subproblem.norm_starProjection_leftmostSpace_sq`,
  `Subproblem.norm_sub_starProjection_leftmostSpace_sq`: the orthogonal projection onto $E_1$ in the
  eigenvector basis.
* `Subproblem.rayleigh_sub_leftmost_le`: $0 \le \rho(z) - \lambda_1 \le (\lambda_n - \lambda_1)
  \|(1 - P_1) z\|^2$ for a unit vector $z$.
* `Subproblem.restWeight_div_leftmostWeight_inverse_pow_le`: $n$ steps of shifted inverse iteration
  multiply the squared tangent by at most $((\ell + \lambda_1) / (\ell + \lambda_1 + \mu))^{2n}$.
* `Subproblem.IsInverseIterationRun.convergence`,
  `Subproblem.IsInverseIterationRun.convergence_of_eventually_const`: Theorem 9.3.1, the convergence
  of the shifts with Q-order $\bar\gamma$.
* `Subproblem.normalize_iterate`: normalizing after every step of a linear iteration gives the same
  vector as normalizing at the end.

## Implementation notes

* As in `Numlib.Optimization.Subproblem.Secular`, the scaling matrix $M$ of the book is not a
  parameter. The space $E$ carries the energy inner product, in which the pencil $(H, M)$ becomes
  the single symmetric operator $M^{-1} H$.
* The start condition is $P_1 z_0 \neq 0$, for the orthogonal projection in the inner product of
  $E$. For matrix data with a scaling $M$ and the $M$-inner product, this is
  $\langle z_0, M v_i \rangle \neq 0$ for some $M$-orthonormal leftmost eigenvector $v_i$.
* The radius $\varepsilon$ of the start depends on a bound $n_U$ for the numbers $n_k$. Without such
  a bound ($n_U = \infty$), no single $\varepsilon$ serves all runs. For
  $H = \operatorname{diag}(0, \mu)$ with $\mu < 1$ and $z_0 = (1, 1)/\sqrt{2}$, the choices
  $\gamma_0 = 2 n_0 - \gamma_U$ and $n_0$ large give $\ell_1 < -\lambda_1$ from any given
  $\ell_0 \in (-\lambda_1, 1 - \mu - \lambda_1)$, because the error of the Rayleigh quotient, about
  $\mu (e / (e + \mu))^{2 n_0}$, is larger than $\omega e^{\gamma_0}$. The convergence holds when
  the sequences $(n_k)$, $(\omega_k)$, $(\gamma_k)$ are fixed before $\varepsilon$ and $(n_k)$ is
  eventually constant (`Subproblem.IsInverseIterationRun.convergence_of_eventually_const`, where
  $n_U = \infty$ is allowed). `Subproblem.IsInverseIterationRun.convergence` gives an $\varepsilon$
  that is uniform over all runs when $n_U < \infty$.
* For the Q-order $\bar\gamma$, only $\gamma_k = \bar\gamma$ for all large $k$ is needed; the
  numbers $n_k$ may keep varying. The two-sided bounds on the errors hold at every iteration.
* The inverse $(H + \ell)^{-1}$ is `Ring.inverse (H + ℓ • 1)`, the inverse in the ring of continuous
  linear maps. It is the true inverse for $\ell > -\lambda_1$.
-/

open Set Filter Topology
open scoped RealInnerProductSpace

namespace Subproblem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : E →L[ℝ] E}

/-! ### The leftmost eigenspace in the eigenvector basis -/

section Spectral

variable (hH : (H : E →ₗ[ℝ] E).IsSymmetric)

/-- The **leftmost eigenspace** $E_1 = \ker(H - \lambda_1)$ of the symmetric operator $H$, where
$\lambda_1$ is `Subproblem.leftmost`. -/
noncomputable def leftmostSpace : Submodule ℝ E :=
  Module.End.eigenspace (H : E →ₗ[ℝ] E) (leftmost hH)

/-- The squared norm of the component of $z$ in the leftmost eigenspace, in the eigenvector basis
$(b_i)$ with eigenvalues $(\lambda_i)$:
$$\sum_{i : \lambda_i = \lambda_1} \langle b_i, z \rangle^2.$$
It equals $\|P_1 z\|^2$ by `Subproblem.norm_starProjection_leftmostSpace_sq`. -/
noncomputable def leftmostWeight (z : E) : ℝ :=
  ∑ i, if hH.eigenvalues rfl i = leftmost hH then ⟪hH.eigenvectorBasis rfl i, z⟫ ^ 2 else 0

/-- The squared norm of the component of $z$ orthogonal to the leftmost eigenspace, in the
eigenvector basis $(b_i)$ with eigenvalues $(\lambda_i)$:
$$\sum_{i : \lambda_i \neq \lambda_1} \langle b_i, z \rangle^2.$$
It equals $\|(1 - P_1) z\|^2$ by `Subproblem.norm_sub_starProjection_leftmostSpace_sq`. -/
noncomputable def restWeight (z : E) : ℝ :=
  ∑ i, if hH.eigenvalues rfl i = leftmost hH then 0 else ⟪hH.eigenvectorBasis rfl i, z⟫ ^ 2

variable {hH}

/-- The coordinates of $Hv$ in the eigenvector basis: $\langle b_i, H v \rangle = \lambda_i \langle
b_i, v \rangle$. -/
theorem inner_eigenvectorBasis_apply (v : E) (i : Fin (Module.finrank ℝ E)) :
    ⟪hH.eigenvectorBasis rfl i, H v⟫ = hH.eigenvalues rfl i * ⟪hH.eigenvectorBasis rfl i, v⟫ := by
  simpa using inner_eigenvectorBasis_add_smul (hH := hH) 0 v i

/-- A vector $v$ lies in the leftmost eigenspace if and only if $H v = \lambda_1 v$. -/
theorem mem_leftmostSpace_iff {v : E} : v ∈ leftmostSpace hH ↔ H v = leftmost hH • v := by
  rw [leftmostSpace, Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe]

/-- The squared norm in the coordinates of the eigenvector basis:
$\|v\|^2 = \sum_i \langle b_i, v \rangle^2$. -/
theorem norm_sq_eq_sum_eigenvectorBasis (v : E) :
    ‖v‖ ^ 2 = ∑ i, ⟪hH.eigenvectorBasis rfl i, v⟫ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_sum_eigenvectorBasis (hH := hH)]
  simp [sq]

/-- A vector of the leftmost eigenspace has no component along the basis eigenvectors of the other
eigenvalues: if $v \in E_1$ and $\lambda_i \neq \lambda_1$, then $\langle b_i, v \rangle = 0$. -/
theorem inner_eigenvectorBasis_eq_zero_of_mem {v : E} (hv : v ∈ leftmostSpace hH)
    {i : Fin (Module.finrank ℝ E)} (hi : hH.eigenvalues rfl i ≠ leftmost hH) :
    ⟪hH.eigenvectorBasis rfl i, v⟫ = 0 := by
  have h := inner_eigenvectorBasis_apply (hH := hH) v i
  rw [mem_leftmostSpace_iff.1 hv, real_inner_smul_right] at h
  have h' : (hH.eigenvalues rfl i - leftmost hH) * ⟪hH.eigenvectorBasis rfl i, v⟫ = 0 := by
    rw [sub_mul]; linarith
  exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 hi)

/-- The orthogonal projection onto the leftmost eigenspace keeps the leftmost coordinates:
$$P_1 z = \sum_{i : \lambda_i = \lambda_1} \langle b_i, z \rangle \, b_i.$$
-/
theorem starProjection_leftmostSpace (z : E) :
    (leftmostSpace hH).starProjection z = ∑ i, (if hH.eigenvalues rfl i = leftmost hH then
      ⟪hH.eigenvectorBasis rfl i, z⟫ else 0) • hH.eigenvectorBasis rfl i := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [mem_leftmostSpace_iff]
    refine eq_of_inner_eigenvectorBasis (hH := hH) fun j => ?_
    rw [inner_eigenvectorBasis_apply, inner_eigenvectorBasis_sum, real_inner_smul_right,
      inner_eigenvectorBasis_sum]
    split_ifs with h <;> simp [h]
  · intro w hw
    rw [inner_eq_sum_eigenvectorBasis (hH := hH)]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [inner_sub_right, inner_eigenvectorBasis_sum]
    split_ifs with h
    · simp
    · rw [inner_eigenvectorBasis_eq_zero_of_mem hw h, mul_zero]

/-- The coordinates of $P_1 z$: $\langle b_i, P_1 z \rangle$ is $\langle b_i, z \rangle$ if
$\lambda_i = \lambda_1$, and $0$ otherwise. -/
theorem inner_eigenvectorBasis_starProjection (z : E) (i : Fin (Module.finrank ℝ E)) :
    ⟪hH.eigenvectorBasis rfl i, (leftmostSpace hH).starProjection z⟫ =
      if hH.eigenvalues rfl i = leftmost hH then ⟪hH.eigenvectorBasis rfl i, z⟫ else 0 := by
  rw [starProjection_leftmostSpace, inner_eigenvectorBasis_sum]

/-- $\|P_1 z\|^2$ is the leftmost weight `Subproblem.leftmostWeight` of $z$. -/
theorem norm_starProjection_leftmostSpace_sq (z : E) :
    ‖(leftmostSpace hH).starProjection z‖ ^ 2 = leftmostWeight hH z := by
  rw [norm_sq_eq_sum_eigenvectorBasis (hH := hH), leftmostWeight]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_eigenvectorBasis_starProjection]
  split_ifs <;> simp

/-- $\|z - P_1 z\|^2$ is the remaining weight `Subproblem.restWeight` of $z$. -/
theorem norm_sub_starProjection_leftmostSpace_sq (z : E) :
    ‖z - (leftmostSpace hH).starProjection z‖ ^ 2 = restWeight hH z := by
  rw [norm_sq_eq_sum_eigenvectorBasis (hH := hH), restWeight]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sub_right, inner_eigenvectorBasis_starProjection]
  split_ifs <;> simp

/-- The leftmost weight is nonnegative. -/
theorem leftmostWeight_nonneg (z : E) : 0 ≤ leftmostWeight hH z :=
  Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity

/-- The remaining weight is nonnegative. -/
theorem restWeight_nonneg (z : E) : 0 ≤ restWeight hH z :=
  Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity

/-- The leftmost weight and the remaining weight of $z$ add up to $\|z\|^2$. -/
theorem leftmostWeight_add_restWeight (z : E) :
    leftmostWeight hH z + restWeight hH z = ‖z‖ ^ 2 := by
  rw [norm_sq_eq_sum_eigenvectorBasis (hH := hH), leftmostWeight, restWeight,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

/-- The leftmost weight of $cz$ is $c^2$ times the leftmost weight of $z$. -/
theorem leftmostWeight_smul (c : ℝ) (z : E) :
    leftmostWeight hH (c • z) = c ^ 2 * leftmostWeight hH z := by
  rw [leftmostWeight, leftmostWeight, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_right]
  split_ifs <;> ring

/-- The remaining weight of $cz$ is $c^2$ times the remaining weight of $z$. -/
theorem restWeight_smul (c : ℝ) (z : E) :
    restWeight hH (c • z) = c ^ 2 * restWeight hH z := by
  rw [restWeight, restWeight, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_right]
  split_ifs <;> ring

/-- $P_1 z \neq 0$ if and only if the leftmost weight of $z$ is positive. -/
theorem starProjection_leftmostSpace_ne_zero_iff {z : E} :
    (leftmostSpace hH).starProjection z ≠ 0 ↔ 0 < leftmostWeight hH z := by
  rw [← norm_starProjection_leftmostSpace_sq, ← norm_ne_zero_iff]
  exact ⟨fun h => pow_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)) 2,
    fun h h0 => by simp [h0] at h⟩

/-- The Rayleigh quotient in the eigenvector basis:
$$\langle z, H z \rangle - \lambda_1 \|z\|^2 = \sum_i (\lambda_i - \lambda_1) \langle b_i, z
  \rangle^2.$$
-/
theorem inner_apply_sub_leftmost_mul (z : E) :
    ⟪z, H z⟫ - leftmost hH * ‖z‖ ^ 2 =
      ∑ i, (hH.eigenvalues rfl i - leftmost hH) * ⟪hH.eigenvectorBasis rfl i, z⟫ ^ 2 := by
  rw [inner_eq_sum_eigenvectorBasis (hH := hH) z (H z), norm_sq_eq_sum_eigenvectorBasis (hH := hH),
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_eigenvectorBasis_apply]
  ring

/-- For a unit vector $z$, the error of the Rayleigh quotient satisfies $0 \le \langle z, H z
\rangle - \lambda_1 \le (\lambda_n - \lambda_1) \sum_{i : \lambda_i \neq \lambda_1} \langle b_i,
z \rangle^2$. This is the coordinate form of `Subproblem.rayleigh_sub_leftmost_le`. -/
theorem rayleigh_sub_leftmost_le_restWeight {z : E} (hz : ‖z‖ = 1) :
    0 ≤ ⟪z, H z⟫ - leftmost hH ∧
      ⟪z, H z⟫ - leftmost hH ≤ (rightmost hH - leftmost hH) * restWeight hH z := by
  have h := inner_apply_sub_leftmost_mul (hH := hH) z
  rw [hz, one_pow, mul_one] at h
  rw [h, restWeight, Finset.mul_sum]
  constructor
  · exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (sub_nonneg.2 (leftmost_le_eigenvalues i)) (sq_nonneg _)
  · refine Finset.sum_le_sum fun i _ => ?_
    split_ifs with hi
    · simp [hi]
    · exact mul_le_mul_of_nonneg_right
        (by linarith [eigenvalues_le_rightmost (hH := hH) i]) (sq_nonneg _)

/-- **The Rayleigh quotient is accurate to second order.** Let $z$ be a unit vector. Then
$$0 \le \langle z, H z \rangle - \lambda_1 \le (\lambda_n - \lambda_1) \, \|(1 - P_1) z\|^2,$$
and if $P_1 z \neq 0$, then the component off the leftmost eigenspace is at most the tangent:
$\|(1 - P_1) z\| \le \|(1 - P_1) z\| / \|P_1 z\|$.

This standard fact is used in the proof of Theorem 9.3.1 of [cartis2022evaluation]. The numbers
$\lambda_1$ and $\lambda_n$ are `Subproblem.leftmost` and `Subproblem.rightmost`. -/
theorem rayleigh_sub_leftmost_le {z : E} (hz : ‖z‖ = 1) :
    0 ≤ ⟪z, H z⟫ - leftmost hH ∧
      ⟪z, H z⟫ - leftmost hH ≤
        (rightmost hH - leftmost hH) * ‖z - (leftmostSpace hH).starProjection z‖ ^ 2 ∧
      ((leftmostSpace hH).starProjection z ≠ 0 →
        ‖z - (leftmostSpace hH).starProjection z‖ ≤
          ‖z - (leftmostSpace hH).starProjection z‖ /
            ‖(leftmostSpace hH).starProjection z‖) := by
  refine ⟨(rayleigh_sub_leftmost_le_restWeight hz).1, ?_, fun hP => ?_⟩
  · rw [norm_sub_starProjection_leftmostSpace_sq]
    exact (rayleigh_sub_leftmost_le_restWeight hz).2
  · have h1 : ‖(leftmostSpace hH).starProjection z‖ ≤ 1 := by
      have := leftmostWeight_add_restWeight (hH := hH) z
      rw [hz, ← norm_starProjection_leftmostSpace_sq] at this
      nlinarith [restWeight_nonneg (hH := hH) z,
        norm_nonneg ((leftmostSpace hH).starProjection z)]
    exact le_div_self (norm_nonneg _) (norm_pos_iff.2 hP) h1

/-- There is a number $\mu$ with $0 < \mu \le 1$ that bounds the gap between the leftmost eigenvalue
and every other eigenvalue: $\lambda_1 + \mu \le \lambda_i$ whenever $\lambda_i \neq \lambda_1$. -/
theorem exists_spectralGap :
    ∃ μ : ℝ, 0 < μ ∧ μ ≤ 1 ∧
      ∀ i, hH.eigenvalues rfl i ≠ leftmost hH → leftmost hH + μ ≤ hH.eigenvalues rfl i := by
  let f : Fin (Module.finrank ℝ E) → ℝ := fun i =>
    if hH.eigenvalues rfl i = leftmost hH then 1 else hH.eigenvalues rfl i - leftmost hH
  have hf : ∀ i, 0 < f i := fun i => by
    simp only [f]
    split_ifs with h
    · exact one_pos
    · exact sub_pos.2 (lt_of_le_of_ne (leftmost_le_eigenvalues i) (Ne.symm h))
  have key : ∀ μ, μ ≤ 1 → (∀ i, μ ≤ f i) →
      ∀ i, hH.eigenvalues rfl i ≠ leftmost hH → leftmost hH + μ ≤ hH.eigenvalues rfl i :=
    fun μ _ hμ i hi => by
      have := hμ i
      simp only [f, hi, ite_false] at this
      linarith
  rcases isEmpty_or_nonempty (Fin (Module.finrank ℝ E)) with hE | hE
  · exact ⟨1, one_pos, le_rfl, fun i => isEmptyElim i⟩
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_min f
    exact ⟨min 1 (f i₀), lt_min one_pos (hf i₀), min_le_left _ _,
      key _ (min_le_left _ _) fun i => (min_le_right _ _).trans (hi₀ i)⟩

/-- **Shifted inverse iteration reduces the tangent.** Let $\ell > -\lambda_1$, let $\mu > 0$
satisfy $\lambda_1 + \mu \le \lambda_i$ for every eigenvalue $\lambda_i \neq \lambda_1$, let $n$
be a natural number, let $z \in E$, and let $v = (H + \ell)^{-n} z$. Then
$$\|P_1 v\|^2 = \frac{\|P_1 z\|^2}{(\ell + \lambda_1)^{2n}}, \qquad \|(1 - P_1) v\|^2 \le
  \frac{\|(1 - P_1) z\|^2}{(\ell + \lambda_1 + \mu)^{2n}}.$$
Hence the squared tangent $\|(1 - P_1) v\|^2 / \|P_1 v\|^2$ is at most $((\ell + \lambda_1) /
(\ell + \lambda_1 + \mu))^{2n}$ times that of $z$.

The squared norms are written as `Subproblem.leftmostWeight` and `Subproblem.restWeight`. -/
theorem restWeight_div_leftmostWeight_inverse_pow_le {μ ℓ : ℝ} (hμ : 0 < μ)
    (hgap : ∀ i, hH.eigenvalues rfl i ≠ leftmost hH → leftmost hH + μ ≤ hH.eigenvalues rfl i)
    (hℓ : -leftmost hH < ℓ) (n : ℕ) (z : E) :
    leftmostWeight hH ((Ring.inverse (H + ℓ • 1) ^ n) z) =
        leftmostWeight hH z / ((ℓ + leftmost hH) ^ n) ^ 2 ∧
      restWeight hH ((Ring.inverse (H + ℓ • 1) ^ n) z) ≤
        restWeight hH z / ((ℓ + leftmost hH + μ) ^ n) ^ 2 := by
  have he : 0 < ℓ + leftmost hH := by linarith
  constructor
  · rw [leftmostWeight, leftmostWeight, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_eigenvectorBasis_inverse_pow hℓ]
    split_ifs with hi
    · rw [hi, div_pow]
    · simp
  · rw [restWeight, restWeight, Finset.sum_div]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [inner_eigenvectorBasis_inverse_pow hℓ]
    split_ifs with hi
    · simp
    · rw [div_pow]
      have := hgap i hi
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        (pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) n) 2)

/-- One block of Algorithm 9.3.1. Let $\ell > -\lambda_1$, let $\mu > 0$ bound the spectral gap as
in `Subproblem.restWeight_div_leftmostWeight_inverse_pow_le`, let $P_1 z \neq 0$, and let
$v = (H + \ell)^{-n} z$. Then $v / \|v\|$ is a unit vector with $P_1 (v / \|v\|) \neq 0$, and
its squared tangent is at most $((\ell + \lambda_1)^n / (\ell + \lambda_1 + \mu)^n)^2$ times
that of $z$. -/
theorem inverseIteration_block {μ ℓ : ℝ} (hμ : 0 < μ)
    (hgap : ∀ i, hH.eigenvalues rfl i ≠ leftmost hH → leftmost hH + μ ≤ hH.eigenvalues rfl i)
    (hℓ : -leftmost hH < ℓ) (n : ℕ) {z v : E} (hz : 0 < leftmostWeight hH z)
    (hv : v = (Ring.inverse (H + ℓ • 1) ^ n) z) :
    ‖‖v‖⁻¹ • v‖ = 1 ∧ 0 < leftmostWeight hH (‖v‖⁻¹ • v) ∧
      restWeight hH (‖v‖⁻¹ • v) / leftmostWeight hH (‖v‖⁻¹ • v) ≤
        ((ℓ + leftmost hH) ^ n / (ℓ + leftmost hH + μ) ^ n) ^ 2 *
          (restWeight hH z / leftmostWeight hH z) := by
  obtain ⟨hL, hR⟩ := restWeight_div_leftmostWeight_inverse_pow_le hμ hgap hℓ n z
  rw [← hv] at hL hR
  have he : 0 < ℓ + leftmost hH := by linarith
  have hLv : 0 < leftmostWeight hH v := by rw [hL]; positivity
  have hv0 : v ≠ 0 := by rintro rfl; simp [leftmostWeight] at hLv
  have hnv : 0 < ‖v‖ := norm_pos_iff.2 hv0
  have hc : (‖v‖⁻¹) ^ 2 ≠ 0 := by positivity
  refine ⟨by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnv.ne'], ?_, ?_⟩
  · rw [leftmostWeight_smul]; positivity
  · rw [leftmostWeight_smul, restWeight_smul, mul_div_mul_left _ _ hc, hL, div_pow]
    have hA : ((ℓ + leftmost hH) ^ n) ^ 2 ≠ 0 := by positivity
    have hD : ((ℓ + leftmost hH + μ) ^ n) ^ 2 ≠ 0 := by positivity
    have hL0 := hz.ne'
    calc restWeight hH v / (leftmostWeight hH z / ((ℓ + leftmost hH) ^ n) ^ 2)
        ≤ restWeight hH z / ((ℓ + leftmost hH + μ) ^ n) ^ 2 /
            (leftmostWeight hH z / ((ℓ + leftmost hH) ^ n) ^ 2) :=
          div_le_div_of_nonneg_right hR (by positivity)
      _ = _ := by field_simp

end Spectral

/-! ### Algorithm 9.3.1 -/

variable (hH : (H : E →ₗ[ℝ] E).IsSymmetric)

/-- A run of **Algorithm 9.3.1** of [cartis2022evaluation], for the potential hard case, with the
constants $\omega_L$, $\omega_U$, $\gamma_L$, $\gamma_U$ and
$n_U \in \mathbb{N} \cup \{\infty\}$. It consists of shifts $\ell_k$ (the book's $\lambda^G_k$),
vectors $z_k$, numbers $n_k$ of inverse iterations, and parameters $\omega_k$ and $\gamma_k$,
such that $\|z_0\| = 1$, $\ell_0 > -\lambda_1$, and for every $k$:

* $1 \le n_k \le n_U$, $\omega_k \in [\omega_L, \omega_U]$ and
  $\gamma_k \in [\gamma_L, 2 n_k - \gamma_U]$;
* $z_{k+1} = v / \|v\|$ with $v = (H + \ell_k)^{-n_k} z_k$;
* $\ell_{k+1} = -\rho + \omega_k (\ell_k + \rho)^{\gamma_k}$, with the Rayleigh quotient
  $\rho = \langle z_{k+1}, H z_{k+1} \rangle$.

The book normalizes after each inverse step. This gives the same vector, by
`Subproblem.normalize_iterate`. The book's constants satisfy $0 < \omega_L \le \omega_U$,
$0 < \gamma_U \le 1$, $1 < \gamma_L \le 2 - \gamma_U$ and $1 \le n_U \le \infty$; these are
hypotheses of the theorems, not conditions on the run. The inverse is `Ring.inverse`. The
structure does not require $\ell_k > -\lambda_1$ for $k \ge 1$, so $z_{k+1}$ is a unit vector
only when $v \neq 0$; under their hypotheses, the convergence theorems prove
$\ell_k > -\lambda_1$ for all $k$. -/
structure IsInverseIterationRun (ωL ωU γL γU : ℝ) (nU : ℕ∞) (ℓ : ℕ → ℝ) (z : ℕ → E)
    (n : ℕ → ℕ) (ω γ : ℕ → ℝ) : Prop where
  /-- The initial vector is a unit vector: $\|z_0\| = 1$. -/
  norm_zero : ‖z 0‖ = 1
  /-- The initial shift makes $H + \ell_0$ positive definite: $\ell_0 > -\lambda_1$. -/
  shift_zero : -leftmost hH < ℓ 0
  /-- Each block performs at least one inverse iteration: $n_k \ge 1$. -/
  one_le_count : ∀ k, 1 ≤ n k
  /-- The numbers of inverse iterations are bounded by $n_U$: $n_k \le n_U$. -/
  count_le : ∀ k, (n k : ℕ∞) ≤ nU
  /-- The weights lie in $[\omega_L, \omega_U]$. -/
  weight_mem : ∀ k, ω k ∈ Icc ωL ωU
  /-- The exponents satisfy $\gamma_L \le \gamma_k \le 2 n_k - \gamma_U$. -/
  exponent_mem : ∀ k, γ k ∈ Icc γL (2 * n k - γU)
  /-- The next vector is the normalization of $(H + \ell_k)^{-n_k} z_k$. -/
  vector_succ : ∀ k, z (k + 1) = ‖(Ring.inverse (H + ℓ k • 1) ^ n k) (z k)‖⁻¹ •
    (Ring.inverse (H + ℓ k • 1) ^ n k) (z k)
  /-- The next shift is $\ell_{k+1} = -\rho + \omega_k (\ell_k + \rho)^{\gamma_k}$, with the
  Rayleigh quotient $\rho = \langle z_{k+1}, H z_{k+1} \rangle$. -/
  shift_succ : ∀ k, ℓ (k + 1) = -⟪z (k + 1), H (z (k + 1))⟫ +
    ω k * (ℓ k + ⟪z (k + 1), H (z (k + 1))⟫) ^ γ k

variable {hH}

/-- The error recursion of the shift update. Let $0 < \gamma_U$, $1 < \gamma_L$, $K \ge 0$, and let
$\varepsilon$ satisfy
$$\varepsilon \le 1, \quad K \varepsilon \le 1, \quad K \varepsilon^{\gamma_U} \le \omega_L / 2,
  \quad \omega_U 2^{2N} \varepsilon^{\gamma_L - 1} \le 1/2.$$
Let $0 < e \le \varepsilon$ be the error $\ell + \lambda_1$, and let $d$ be the error
$\rho - \lambda_1$ of the Rayleigh quotient, with $0 \le d \le K e^{2n}$, where $1 \le n \le N$.
Let $\omega \in [\omega_L, \omega_U]$ and $\gamma \in [\gamma_L, 2n - \gamma_U]$. Then the new
error $e' = \omega (e + d)^\gamma - d$ satisfies
$$\frac{\omega_L}{2} e^\gamma \le e' \le \omega_U 2^\gamma e^\gamma \quad \text{and} \quad e'
  \le e / 2.$$
-/
theorem shiftUpdate_bounds {ωL ωU γL γU K ε e d ω γ : ℝ} {n N : ℕ} (hγU : 0 < γU)
    (hγL : 1 < γL) (hK : 0 ≤ K) (hε1 : ε ≤ 1) (hKε : K * ε ≤ 1)
    (hKεγ : K * ε ^ γU ≤ ωL / 2) (hωε : ωU * 2 ^ (2 * N : ℝ) * ε ^ (γL - 1) ≤ 1 / 2)
    (he : 0 < e) (heε : e ≤ ε) (hd0 : 0 ≤ d) (hd : d ≤ K * e ^ (2 * n)) (hn : 1 ≤ n)
    (hnN : n ≤ N) (hω : ω ∈ Icc ωL ωU) (hγ : γ ∈ Icc γL (2 * n - γU)) :
    ωL / 2 * e ^ γ ≤ ω * (e + d) ^ γ - d ∧ ω * (e + d) ^ γ - d ≤ ωU * 2 ^ γ * e ^ γ ∧
      ω * (e + d) ^ γ - d ≤ e / 2 := by
  have he1 : e ≤ 1 := heε.trans hε1
  have hγ0 : 0 ≤ γ := by linarith [hγ.1]
  have hωL : 0 ≤ ωL := by
    have : 0 ≤ K * ε ^ γU := mul_nonneg hK (Real.rpow_nonneg (he.le.trans heε) _)
    linarith
  have hω0 : 0 ≤ ω := hωL.trans hω.1
  have heγ : 0 ≤ e ^ γ := Real.rpow_nonneg he.le _
  -- `d ≤ K ε ^ γU e ^ γ ≤ ωL/2 · e ^ γ`
  have hpow : e ^ (2 * n) = e ^ ((2 * n : ℝ) - γ) * e ^ γ := by
    rw [← Real.rpow_add he, sub_add_cancel, ← Real.rpow_natCast]
    norm_num
  have h1 : e ^ ((2 * n : ℝ) - γ) ≤ ε ^ γU :=
    (Real.rpow_le_rpow_of_exponent_ge he he1 (by linarith [hγ.2])).trans
      (Real.rpow_le_rpow he.le heε hγU.le)
  have hdγ : d ≤ ωL / 2 * e ^ γ :=
    calc d ≤ K * e ^ (2 * n) := hd
      _ = K * e ^ ((2 * n : ℝ) - γ) * e ^ γ := by rw [hpow, mul_assoc]
      _ ≤ K * ε ^ γU * e ^ γ := by gcongr
      _ ≤ ωL / 2 * e ^ γ := by gcongr
  have hlow : ωL * e ^ γ ≤ ω * (e + d) ^ γ :=
    mul_le_mul hω.1 (Real.rpow_le_rpow he.le (by linarith) hγ0) heγ hω0
  -- `d ≤ e`
  have hde : d ≤ e := by
    have h2 : e ^ (2 * n) ≤ e ^ 2 := pow_le_pow_of_le_one he.le he1 (by omega)
    calc d ≤ K * e ^ (2 * n) := hd
      _ ≤ K * e ^ 2 := by gcongr
      _ = K * e * e := by ring
      _ ≤ K * ε * e := by gcongr
      _ ≤ 1 * e := by gcongr
      _ = e := one_mul e
  have hup : ω * (e + d) ^ γ ≤ ωU * 2 ^ γ * e ^ γ := by
    rw [mul_assoc, ← Real.mul_rpow (by norm_num) he.le]
    exact mul_le_mul hω.2 (Real.rpow_le_rpow (by linarith) (by linarith) hγ0)
      (Real.rpow_nonneg (by linarith) _) (hω0.trans hω.2)
  refine ⟨by linarith, by linarith, ?_⟩
  -- `ωU 2 ^ γ e ^ γ ≤ e / 2`
  have h2γ : (2 : ℝ) ^ γ ≤ 2 ^ (2 * N : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      have : (n : ℝ) ≤ N := by exact_mod_cast hnN
      linarith [hγ.2])
  have heγ1 : e ^ (γ - 1) ≤ ε ^ (γL - 1) :=
    (Real.rpow_le_rpow_of_exponent_ge he he1 (by linarith [hγ.1])).trans
      (Real.rpow_le_rpow he.le heε (by linarith))
  have hsplit : e ^ γ = e ^ (γ - 1) * e := by
    rw [Real.rpow_sub_one he.ne', div_mul_cancel₀ _ he.ne']
  have hωU : 0 ≤ ωU := hω0.trans hω.2
  have : ωU * 2 ^ γ * e ^ γ ≤ 1 / 2 * e :=
    calc ωU * 2 ^ γ * e ^ γ = ωU * 2 ^ γ * e ^ (γ - 1) * e := by rw [hsplit]; ring
      _ ≤ ωU * 2 ^ (2 * N : ℝ) * ε ^ (γL - 1) * e := by gcongr
      _ ≤ 1 / 2 * e := by gcongr
  linarith

/-- The smallness conditions of `Subproblem.shiftUpdate_bounds` hold for some $\varepsilon$: if
$\omega_L > 0$, $\gamma_U > 0$ and $\gamma_L > 1$, then for every $K$, $\omega_U$ and natural
number $N$ there is $\varepsilon > 0$ with $\varepsilon \le 1$, $K \varepsilon \le 1$,
$K \varepsilon^{\gamma_U} \le \omega_L / 2$ and $\omega_U 2^{2N} \varepsilon^{\gamma_L - 1} \le
1/2$. -/
theorem exists_shiftUpdate_radius {K ωL ωU γL γU : ℝ} (hωL : 0 < ωL) (hγU : 0 < γU)
    (hγL : 1 < γL) (N : ℕ) :
    ∃ ε > 0, ε ≤ 1 ∧ K * ε ≤ 1 ∧ K * ε ^ γU ≤ ωL / 2 ∧
      ωU * 2 ^ (2 * N : ℝ) * ε ^ (γL - 1) ≤ 1 / 2 := by
  have hc : ∀ {p : ℝ}, 0 < p → ∀ c : ℝ, Tendsto (fun ε : ℝ => c * ε ^ p) (𝓝 0) (𝓝 0) :=
    fun hp c => by
      have := ((Real.continuousAt_rpow_const 0 _ (Or.inr hp.le)).tendsto).const_mul c
      simpa [Real.zero_rpow hp.ne'] using this
  have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), ε < 1 := eventually_lt_nhds one_pos
  have h2 : ∀ᶠ ε in 𝓝 (0 : ℝ), K * ε < 1 := by
    have : Tendsto (fun ε : ℝ => K * ε) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_const_mul K).tendsto 0
    exact (tendsto_order.1 this).2 _ one_pos
  have h3 := (tendsto_order.1 (hc hγU K)).2 _ (half_pos hωL)
  have h4 := (tendsto_order.1 (hc (sub_pos.2 hγL) (ωU * 2 ^ (2 * N : ℝ)))).2 _
    (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨ε, hε, ⟨h1, h2⟩, h3, h4⟩ :=
    ((eventually_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0)).and
      (nhdsWithin_le_nhds ((h1.and h2).and (h3.and h4)))).exists
  exact ⟨ε, hε, h1.le, h2.le, h3.le, h4.le⟩

/-- The tangent factor of one block: for $e > 0$, $0 < \mu \le 1$ and natural numbers $n \le N$,
$$\left(\frac{e^n}{(e + \mu)^n}\right)^2 \le \frac{e^{2n}}{\mu^{2N}} \quad \text{and} \quad
  \left(\frac{e^n}{(e + \mu)^n}\right)^2 \le 1.$$
-/
theorem tangentFactor_le {e μ : ℝ} {n N : ℕ} (he : 0 < e) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hnN : n ≤ N) :
    (e ^ n / (e + μ) ^ n) ^ 2 ≤ e ^ (2 * n) / μ ^ (2 * N) ∧ (e ^ n / (e + μ) ^ n) ^ 2 ≤ 1 := by
  have hq : e ^ n / (e + μ) ^ n ≤ 1 :=
    (div_le_one (by positivity)).2 (pow_le_pow_left₀ he.le (by linarith) n)
  refine ⟨?_, pow_le_one₀ (by positivity) hq⟩
  calc (e ^ n / (e + μ) ^ n) ^ 2 ≤ (e ^ n / μ ^ n) ^ 2 := by
        gcongr
        linarith
    _ = e ^ (2 * n) / μ ^ (2 * n) := by rw [div_pow, ← pow_mul, ← pow_mul, mul_comm n 2]
    _ ≤ e ^ (2 * n) / μ ^ (2 * N) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_of_le_one hμ.le hμ1 (by omega))

/-- **Theorem 9.3.1** of [cartis2022evaluation] (fast convergence in the hard case), with a bound on
the numbers of inverse iterations. Let $z_0 \in E$ have $P_1 z_0 \neq 0$, and let the constants
satisfy $\omega_L > 0$, $\gamma_U > 0$, $\gamma_L > 1$ and $n_U < \infty$. Then there is
$\varepsilon > 0$ such that every run of Algorithm 9.3.1 with initial vector $z_0$ and
$\ell_0 < -\lambda_1 + \varepsilon$ has the following properties, where
$e_k = \ell_k + \lambda_1$:

* $\ell_k > -\lambda_1$ for all $k$, so every $H + \ell_k$ is positive definite; the shifts
  decrease, and $\ell_k \to -\lambda_1$;
* $z_k$ approaches $E_1$: $\|(1 - P_1) z_k\| \to 0$;
* $\frac{\omega_L}{2} e_k^{\gamma_k} \le e_{k+1} \le \omega_U 2^{\gamma_k} e_k^{\gamma_k}$ for
  every $k$;
* if $\gamma_k = \bar\gamma$ for all large $k$, the shifts converge with Q-order exactly
  $\bar\gamma$: there are $0 < c \le C$ with $c \, e_k^{\bar\gamma} \le e_{k+1} \le C
  e_k^{\bar\gamma}$ for all large $k$, and $\ell$ converges to $-\lambda_1$ with order
  $\bar\gamma$ in the sense of `ConvergesWithOrder`.

The start condition is read in the inner product of $E$, which is the $M$-inner product of the
book. The radius $\varepsilon$ depends on the bound $n_U$; without such a bound no uniform
$\varepsilon$ exists (see the module documentation), and
`Subproblem.IsInverseIterationRun.convergence_of_eventually_const` gives the version of the
book. -/
theorem IsInverseIterationRun.convergence {ωL ωU γL γU : ℝ} {nU : ℕ∞} (hωL : 0 < ωL)
    (hγU : 0 < γU) (hγL : 1 < γL) (hnU : nU ≠ ⊤) {z₀ : E}
    (hz₀ : (leftmostSpace hH).starProjection z₀ ≠ 0) :
    ∃ ε > 0, ∀ (ℓ : ℕ → ℝ) (z : ℕ → E) (n : ℕ → ℕ) (ω γ : ℕ → ℝ),
      IsInverseIterationRun hH ωL ωU γL γU nU ℓ z n ω γ → z 0 = z₀ →
      ℓ 0 < -leftmost hH + ε →
      (∀ k, -leftmost hH < ℓ k) ∧ Antitone ℓ ∧ Tendsto ℓ atTop (𝓝 (-leftmost hH)) ∧
      Tendsto (fun k => ‖z k - (leftmostSpace hH).starProjection (z k)‖) atTop (𝓝 0) ∧
      (∀ k, ωL / 2 * (ℓ k + leftmost hH) ^ γ k ≤ ℓ (k + 1) + leftmost hH ∧
        ℓ (k + 1) + leftmost hH ≤ ωU * 2 ^ γ k * (ℓ k + leftmost hH) ^ γ k) ∧
      ∀ γbar : ℝ, (∀ᶠ k in atTop, γ k = γbar) →
        (∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ᶠ k in atTop,
          c * (ℓ k + leftmost hH) ^ γbar ≤ ℓ (k + 1) + leftmost hH ∧
            ℓ (k + 1) + leftmost hH ≤ C * (ℓ k + leftmost hH) ^ γbar) ∧
        ConvergesWithOrder ℓ (-leftmost hH) γbar := by
  obtain ⟨N, rfl⟩ := ENat.ne_top_iff_exists.1 hnU
  obtain ⟨μ, hμ, hμ1, hgap⟩ := exists_spectralGap (hH := hH)
  rw [starProjection_leftmostSpace_ne_zero_iff] at hz₀
  set T₀ := restWeight hH z₀ / leftmostWeight hH z₀ with hT₀
  have hT₀0 : 0 ≤ T₀ := div_nonneg (restWeight_nonneg _) hz₀.le
  set Λ := max 0 (rightmost hH - leftmost hH) with hΛ
  set K := Λ * T₀ / μ ^ (2 * N) with hK
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨ε, hε, hε1, hKε, hKεγ, hωε⟩ :=
    exists_shiftUpdate_radius (K := K) (ωU := ωU) hωL hγU hγL N
  refine ⟨ε, hε, fun ℓ z n ω γ hr hz0 hℓ0 => ?_⟩
  -- the error and the invariant
  set e : ℕ → ℝ := fun k => ℓ k + leftmost hH with he_def
  have hnN : ∀ k, n k ≤ N := fun k => by exact_mod_cast hr.count_le k
  let Inv : ℕ → Prop := fun k => ‖z k‖ = 1 ∧ 0 < leftmostWeight hH (z k) ∧
    restWeight hH (z k) / leftmostWeight hH (z k) ≤ T₀ ∧ 0 < e k ∧ e k ≤ ε * (1 / 2) ^ k
  have hstep : ∀ k, Inv k → Inv (k + 1) ∧
      (ωL / 2 * e k ^ γ k ≤ e (k + 1) ∧ e (k + 1) ≤ ωU * 2 ^ γ k * e k ^ γ k) ∧
      e (k + 1) ≤ e k ∧ restWeight hH (z (k + 1)) ≤ T₀ / μ ^ (2 * N) * e k ^ 2 := by
    rintro k ⟨-, hL, hT, he, hek⟩
    have hℓk : -leftmost hH < ℓ k := by simp only [he_def] at he; linarith
    obtain ⟨hz1, hL1, hT1⟩ := inverseIteration_block hμ hgap hℓk (n k) hL rfl
    rw [← hr.vector_succ] at hz1 hL1 hT1
    obtain ⟨hf, hf1⟩ := tangentFactor_le (n := n k) he hμ hμ1 (hnN k)
    have hT1' : restWeight hH (z (k + 1)) / leftmostWeight hH (z (k + 1)) ≤
        e k ^ (2 * n k) / μ ^ (2 * N) * T₀ :=
      hT1.trans (mul_le_mul hf hT (div_nonneg (restWeight_nonneg _) hL.le) (by positivity))
    have hRle : restWeight hH (z (k + 1)) ≤
        restWeight hH (z (k + 1)) / leftmostWeight hH (z (k + 1)) := by
      have := leftmostWeight_add_restWeight (hH := hH) (z (k + 1))
      rw [hz1] at this
      have h0 := restWeight_nonneg (hH := hH) (z (k + 1))
      exact le_div_self h0 hL1 (by linarith)
    -- the Rayleigh-quotient error
    set d := ⟪z (k + 1), H (z (k + 1))⟫ - leftmost hH with hd_def
    obtain ⟨hd0, hd1⟩ := rayleigh_sub_leftmost_le_restWeight (hH := hH) hz1
    have hdK : d ≤ K * e k ^ (2 * n k) :=
      calc d ≤ (rightmost hH - leftmost hH) * restWeight hH (z (k + 1)) := hd1
        _ ≤ Λ * (e k ^ (2 * n k) / μ ^ (2 * N) * T₀) :=
          mul_le_mul (le_max_right _ _) (hRle.trans hT1') (restWeight_nonneg _)
            (le_max_left _ _)
        _ = K * e k ^ (2 * n k) := by rw [hK]; ring
    have hrec : e (k + 1) = ω k * (e k + d) ^ γ k - d := by
      simp only [he_def, hd_def]
      rw [hr.shift_succ]
      ring_nf
    obtain ⟨hlo, hhi, hhalf⟩ := shiftUpdate_bounds hγU hγL hK0 hε1 hKε hKεγ hωε he
      (hek.trans (mul_le_of_le_one_right hε.le (pow_le_one₀ (by norm_num) (by norm_num))))
      hd0 hdK (hr.one_le_count k) (hnN k) (hr.weight_mem k) (hr.exponent_mem k)
    rw [← hrec] at hlo hhi hhalf
    have hpos : 0 < e (k + 1) :=
      lt_of_lt_of_le (mul_pos (half_pos hωL) (Real.rpow_pos_of_pos he _)) hlo
    have hTle : restWeight hH (z (k + 1)) / leftmostWeight hH (z (k + 1)) ≤ T₀ :=
      hT1.trans (by
        calc _ ≤ 1 * T₀ := mul_le_mul hf1 hT (div_nonneg (restWeight_nonneg _) hL.le) one_pos.le
          _ = T₀ := one_mul _)
    have he1 : e k ≤ 1 :=
      hek.trans ((mul_le_of_le_one_right hε.le (pow_le_one₀ (by norm_num) (by norm_num))).trans
        hε1)
    refine ⟨⟨hz1, hL1, hTle, hpos, ?_⟩, ⟨hlo, hhi⟩, by linarith, ?_⟩
    · rw [pow_succ]; linarith
    · calc restWeight hH (z (k + 1)) ≤ e k ^ (2 * n k) / μ ^ (2 * N) * T₀ := hRle.trans hT1'
        _ ≤ e k ^ 2 / μ ^ (2 * N) * T₀ :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
            (pow_le_pow_of_le_one he.le he1 (by linarith [hr.one_le_count k])) (by positivity))
            hT₀0
        _ = T₀ / μ ^ (2 * N) * e k ^ 2 := by ring
  have hinv : ∀ k, Inv k := by
    intro k
    induction k with
    | zero =>
      refine ⟨hr.norm_zero, hz0 ▸ hz₀, by rw [hz0], ?_, ?_⟩
      · simp only [he_def]; linarith [hr.shift_zero]
      · simp only [he_def, pow_zero, mul_one]; linarith
    | succ k ih => exact (hstep k ih).1
  have hpos : ∀ k, 0 < e k := fun k => (hinv k).2.2.2.1
  have hbd := fun k => (hstep k (hinv k)).2.1
  have he0 : Tendsto e atTop (𝓝 0) :=
    squeeze_zero (fun k => (hpos k).le) (fun k => (hinv k).2.2.2.2) (by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul ε)
  have hℓlim : Tendsto ℓ atTop (𝓝 (-leftmost hH)) := by
    simpa [he_def] using he0.sub_const (leftmost hH)
  refine ⟨fun k => by have := hpos k; simp only [he_def] at this; linarith,
    antitone_nat_of_succ_le fun k => ?_, hℓlim, ?_, hbd, fun γbar hγ => ?_⟩
  · have := (hstep k (hinv k)).2.2.1
    simp only [he_def] at this
    linarith
  · have hR : Tendsto (fun k => restWeight hH (z (k + 1))) atTop (𝓝 0) :=
      squeeze_zero (fun k => restWeight_nonneg _) (fun k => (hstep k (hinv k)).2.2.2) (by
        simpa using (he0.pow 2).const_mul (T₀ / μ ^ (2 * N)))
    have hsq : Tendsto (fun k => ‖z k - (leftmostSpace hH).starProjection (z k)‖ ^ 2) atTop
        (𝓝 0) := by
      rw [← tendsto_add_atTop_iff_nat 1]
      simpa only [norm_sub_starProjection_leftmostSpace_sq] using hR
    have := (Real.continuous_sqrt.tendsto 0).comp hsq
    simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at this
    exact this
  · obtain ⟨k₀, hk₀⟩ := hγ.exists
    have hγbar : 1 < γbar := hk₀ ▸ lt_of_lt_of_le hγL (hr.exponent_mem k₀).1
    have hωLU : ωL ≤ ωU := (hr.weight_mem 0).1.trans (hr.weight_mem 0).2
    have h2 : (1 : ℝ) ≤ 2 ^ γbar := Real.one_le_rpow (by norm_num) (by linarith)
    have hC : 0 < ωU * 2 ^ γbar := mul_pos (by linarith) (by linarith)
    have hev : ∀ᶠ k in atTop, ωL / 2 * e k ^ γbar ≤ e (k + 1) ∧
        e (k + 1) ≤ ωU * 2 ^ γbar * e k ^ γbar :=
      hγ.mono fun k hk => by rw [← hk]; exact hbd k
    refine ⟨⟨ωL / 2, ωU * 2 ^ γbar, half_pos hωL, ?_, hev⟩, hℓlim, ωU * 2 ^ γbar, hC,
      hev.mono fun k hk => ?_⟩
    · calc ωL / 2 ≤ ωU * 1 := by linarith
        _ ≤ ωU * 2 ^ γbar := mul_le_mul_of_nonneg_left h2 (by linarith)
    · rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_neg_eq_add, sub_neg_eq_add,
        abs_of_pos (hpos (k + 1)), abs_of_pos (hpos k)]
      exact hk.2


/-- **Theorem 9.3.1** of [cartis2022evaluation], as stated in the book, where $n_U = \infty$ is
allowed. Let $z_0 \in E$ have $P_1 z_0 \neq 0$, and let $\omega_L > 0$, $\gamma_U > 0$ and
$\gamma_L > 1$. Fix the sequences $(n_k)$, $(\omega_k)$ and $(\gamma_k)$, with $n_k = \bar n$
for all large $k$. Then there is $\varepsilon > 0$ such that, for every $n_U$, every run of
Algorithm 9.3.1 with these sequences, initial vector $z_0$ and
$\ell_0 < -\lambda_1 + \varepsilon$ has the properties of
`Subproblem.IsInverseIterationRun.convergence`: $\ell_k > -\lambda_1$, the shifts decrease to
$-\lambda_1$, $\|(1 - P_1) z_k\| \to 0$, the errors $e_k = \ell_k + \lambda_1$ satisfy
$\frac{\omega_L}{2} e_k^{\gamma_k} \le e_{k+1} \le \omega_U 2^{\gamma_k} e_k^{\gamma_k}$, and
the shifts converge with Q-order exactly $\bar\gamma$ when $\gamma_k = \bar\gamma$ for all large
$k$.

The radius $\varepsilon$ depends on the sequences only through a bound for $(n_k)$. -/
theorem IsInverseIterationRun.convergence_of_eventually_const {ωL ωU γL γU : ℝ} (hωL : 0 < ωL)
    (hγU : 0 < γU) (hγL : 1 < γL) {z₀ : E} (hz₀ : (leftmostSpace hH).starProjection z₀ ≠ 0)
    {n : ℕ → ℕ} {ω γ : ℕ → ℝ} {nbar : ℕ} (hn : ∀ᶠ k in atTop, n k = nbar) :
    ∃ ε > 0, ∀ (nU : ℕ∞) (ℓ : ℕ → ℝ) (z : ℕ → E),
      IsInverseIterationRun hH ωL ωU γL γU nU ℓ z n ω γ → z 0 = z₀ →
      ℓ 0 < -leftmost hH + ε →
      (∀ k, -leftmost hH < ℓ k) ∧ Antitone ℓ ∧ Tendsto ℓ atTop (𝓝 (-leftmost hH)) ∧
      Tendsto (fun k => ‖z k - (leftmostSpace hH).starProjection (z k)‖) atTop (𝓝 0) ∧
      (∀ k, ωL / 2 * (ℓ k + leftmost hH) ^ γ k ≤ ℓ (k + 1) + leftmost hH ∧
        ℓ (k + 1) + leftmost hH ≤ ωU * 2 ^ γ k * (ℓ k + leftmost hH) ^ γ k) ∧
      ∀ γbar : ℝ, (∀ᶠ k in atTop, γ k = γbar) →
        (∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ᶠ k in atTop,
          c * (ℓ k + leftmost hH) ^ γbar ≤ ℓ (k + 1) + leftmost hH ∧
            ℓ (k + 1) + leftmost hH ≤ C * (ℓ k + leftmost hH) ^ γbar) ∧
        ConvergesWithOrder ℓ (-leftmost hH) γbar  := by
  obtain ⟨K, hK⟩ := eventually_atTop.1 hn
  have hN : ∀ k, n k ≤ max nbar ((Finset.range K).sup n) := fun k => by
    by_cases hk : k < K
    · exact le_max_of_le_right (Finset.le_sup (Finset.mem_range.2 hk))
    · rw [hK k (not_lt.1 hk)]
      exact le_max_left _ _
  obtain ⟨ε, hε, hconv⟩ := IsInverseIterationRun.convergence (hH := hH) (ωU := ωU)
    (nU := (max nbar ((Finset.range K).sup n) : ℕ)) hωL hγU hγL (ENat.natCast_ne_top _) hz₀
  exact ⟨ε, hε, fun _ ℓ z hr hz0 hℓ0 =>
    hconv ℓ z n ω γ { hr with count_le := fun k => by exact_mod_cast hN k } hz0 hℓ0⟩

/-- **Normalizing after every step of a linear iteration is normalizing at the end.** Let $F$ be a
real normed space, let $R : F \to F$ be a continuous linear map, and let $w_0 = z$ and
$w_{i+1} = \operatorname{normalize}(R w_i)$, where $\operatorname{normalize}(v) = v / \|v\|$ and
$\operatorname{normalize}(0) = 0$. Then $w_{i+1} = \operatorname{normalize}(R^{i+1} z)$ for
every $i$.

This is the inner loop of Algorithm 9.3.1 of [cartis2022evaluation]. -/
theorem normalize_iterate {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (R : F →L[ℝ] F)
    {w : ℕ → F} {z : F} (h0 : w 0 = z) (hs : ∀ i, w (i + 1) = NormedSpace.normalize (R (w i)))
    (i : ℕ) : w (i + 1) = NormedSpace.normalize ((R ^ (i + 1)) z) := by
  induction i with
  | zero => rw [hs, h0, zero_add, pow_one]
  | succ i ih =>
    have hRR : (R * R ^ (i + 1)) z = R ((R ^ (i + 1)) z) := rfl
    have hRn : R (NormedSpace.normalize ((R ^ (i + 1)) z)) =
        ‖(R ^ (i + 1)) z‖⁻¹ • R ((R ^ (i + 1)) z) := by
      rw [NormedSpace.normalize, map_smul]
    rw [hs, ih, pow_succ' R (i + 1), hRR, hRn]
    rcases eq_or_ne ((R ^ (i + 1)) z) 0 with hv | hv
    · simp [hv]
    · exact NormedSpace.normalize_smul_of_pos (inv_pos.2 (norm_pos_iff.2 hv)) _

end Subproblem

