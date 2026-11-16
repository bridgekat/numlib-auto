/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Matrix.PEquiv
import Numlib.Eigen.InverseEigenvalue
import Numlib.Eigen.Normal
import Numlib.LinearAlgebra.Matrix.PlaneRotation
import Numlib.Nonlinear.ScalarNewton

/-!
# Diagonal plus rank-one matrices and the secular equation

Let $d \in \mathbb{R}^n$, $\rho \in \mathbb{R}$ and $z \in \mathbb{K}^n$ with
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $D = \operatorname{diag}(d)$. This file studies
the eigenproblem of the Hermitian matrix $M = D + \rho z z^H$ through the **secular function**
$$f(\lambda) = 1 + \rho \sum_i \frac{|z_i|^2}{d_i - \lambda} = 1 + \rho\, z^H (D - \lambda I)^{-1}
  z,$$
and the merge step of the divide-and-conquer method for symmetric tridiagonal matrices. The
presentation follows §8.4.3–8.4.4 of [golub2013matrix], after Dongarra and Sorensen (1987) and
Barlow (1993). When the $d_i$ are distinct, $\rho \neq 0$ and no $z_i$ vanishes, the real
eigenvalues of $M$ are the zeros of $f$, the eigenvectors are the multiples of
$(D - \lambda I)^{-1} z$, and the eigenvalues strictly interlace the $d_i$.

The file also treats the bordered secular function $1 - \lambda - r^T (B - \lambda I)^{-1} r$ of a
symmetric matrix $\begin{bmatrix} 1 & r^T \\ r & B \end{bmatrix}$, from §4.7.7 of [golub2013matrix]
after Cybenko and Van Loan (1986). Newton's method converges monotonically from the right to its
zero below the spectrum of $B$.

## Main definitions

* `Matrix.secularFunction`: the secular function $f(\lambda) = 1 + \rho \sum_i |z_i|^2 / (d_i -
  \lambda)$ of $D + \rho z z^H$.
* `Matrix.borderedSecularFunction`: the bordered secular function
  $1 - \lambda - r^T (B - \lambda I)^{-1} r$.

## Main results

* `Matrix.isUnit_diagonal_sub_of_hasEigenvector_add_rankOne`: if the $d_i$ are distinct,
  $\rho \neq 0$ and no $z_i$ vanishes, an eigenvector $v$ of $M$ has $z^H v \neq 0$, and its
  eigenvalue is no $d_i$ (Lemma 8.4.2 of [golub2013matrix]).
* `Matrix.hasEigenvalue_iff_secularFunction_eq_zero`: under the same hypotheses, a real $\lambda$ is
  an eigenvalue of $M$ if and only if it is no $d_i$ and $f(\lambda) = 0$ (Theorem 8.4.3(a)).
* `Matrix.hasEigenvector_diagonal_add_rankOne_resolvent`: under the same hypotheses, the
  eigenvectors for $\lambda$ are the nonzero multiples of $(D - \lambda I)^{-1} z$ (Theorem
  8.4.3(c)).
* `Matrix.hasDerivAt_secularFunction`, `Matrix.secularFunction_strictMonoOn` and
  `Matrix.secularFunction_strictAntiOn`: the derivative of $f$, and the strict monotonicity of $f$
  between consecutive poles.
* `Matrix.eigenvalues₀_diagonal_add_rankOne_strictInterlace`: for strictly decreasing $d$, the
  eigenvalues of $M$ strictly interlace the $d_i$ (Theorem 8.4.3(b)).
* `Matrix.exists_orthogonal_deflation`: rotations in the planes of repeated $d_i$ and a permutation
  reduce an arbitrary $(d, z)$ to the generic case (Theorem 8.4.4).
* `Matrix.conj_fromBlocks_add_rankOne_eq`: the merge step of divide and conquer, a block-diagonal
  orthogonal similarity that turns $\operatorname{diag}(T_1, T_2) + \rho v v^T$ into a
  diagonal-plus-rank-one matrix.
* `Matrix.borderedSecularFunction_eq_zero_of_mulVec_eq`: an eigenvalue of the bordered matrix at
  which $B - \lambda I$ is invertible is a zero of the bordered secular function.
* `Matrix.borderedSecularFunction_eq_secularFunction_sub`: in an eigenbasis of $B$, the bordered
  secular function is a secular function with $\rho = -1$, minus $\lambda$.
* `Matrix.tendsto_newton_borderedSecularFunction`: Newton's method for the bordered secular function
  converges monotonically from the right to its zero below the spectrum of $B$ (equations (4.7.9)
  and (4.7.10)).

## Proof outline

The weak inequalities of the interlacing are the rank-one case of the low-rank interlacing in
`Numlib.Eigen.MinMax` (`LinearMap.IsSymmetric.eigenvalues_le_of_isPositive_sub_of_finrank_range_le`,
Theorem 8.1.8 of [golub2013matrix]). Lemma 8.4.2 makes them strict, because no eigenvalue of $M$ is
a $d_i$. The argument of the source through the poles of the secular function and the intermediate
value theorem is not needed.

## Implementation notes

* At a pole $\lambda = d_i$, the Lean value of the secular function reads each term
  $|z_j|^2 / (d_j - \lambda)$ with $d_j = \lambda$ as $0$, because $x / 0 = 0$. Every statement
  about it assumes $\lambda \notin \{d_i\}$.
* Eigenvalues are sorted decreasingly, as everywhere in the backbone
  (`Matrix.IsHermitian.sortedEigenvalues`). Indices start at $0$.
-/

open Finset

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-- The **secular function** of $D + \rho z z^H$ (Theorem 8.4.3(a) of [golub2013matrix]): for
$d \in \mathbb{R}^n$, $\rho \in \mathbb{R}$ and $z \in \mathbb{K}^n$,
$$f(\lambda) = 1 + \rho \sum_i \frac{|z_i|^2}{d_i - \lambda},$$
which the source writes as $1 + \rho z^T (D - \lambda I)^{-1} z$.

At a pole $\lambda = d_i$, each term with $d_j = \lambda$ has the value $0$, by the convention
$x / 0 = 0$. The statements about $f$ assume $\lambda \notin \{d_i\}$. -/
noncomputable def secularFunction (d : n → ℝ) (ρ : ℝ) (z : n → 𝕜) (t : ℝ) : ℝ :=
  1 + ρ * ∑ i, ‖z i‖ ^ 2 / (d i - t)

/-- The secular function in the resolvent form of the source: if $\lambda \in \mathbb{R}$ is no
$d_i$, then
$$f(\lambda) = 1 + \rho \operatorname{Re}\bigl(z^H (D - \lambda I)^{-1} z\bigr).$$
-/
theorem secularFunction_eq_inner_resolvent [DecidableEq n] (d : n → ℝ) (ρ : ℝ) (z : n → 𝕜) {t : ℝ}
    (ht : t ∉ Set.range d) :
    secularFunction d ρ z t =
      1 + ρ * RCLike.re (star z ⬝ᵥ (diagonal fun i => ((d i - t : ℝ) : 𝕜))⁻¹ *ᵥ z) := by
  have hne : ∀ i, d i - t ≠ 0 := fun i h => ht ⟨i, (sub_eq_zero.mp h)⟩
  have hinv : (diagonal fun i => ((d i - t : ℝ) : 𝕜))⁻¹ =
      diagonal fun i => ((d i - t : ℝ) : 𝕜)⁻¹ :=
    inv_eq_right_inv (by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      exact congrArg diagonal (funext fun i => mul_inv_cancel₀ (by exact_mod_cast hne i)))
  rw [secularFunction, hinv, dotProduct, map_sum]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_diagonal, Pi.star_apply, RCLike.star_def, mul_left_comm, RCLike.conj_mul,
    ← RCLike.ofReal_inv, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re,
    div_eq_inv_mul]

/-- **The derivative of the secular function** (§8.4.3 of [golub2013matrix], proof of Theorem
8.4.3). If $\lambda \in \mathbb{R}$ is no $d_i$, then $f$ is differentiable at $\lambda$ with
$$f'(\lambda) = \rho \sum_i \frac{|z_i|^2}{(d_i - \lambda)^2}.$$
-/
theorem hasDerivAt_secularFunction (d : n → ℝ) (ρ : ℝ) (z : n → 𝕜) {t : ℝ}
    (ht : t ∉ Set.range d) :
    HasDerivAt (secularFunction d ρ z) (ρ * ∑ i, ‖z i‖ ^ 2 / (d i - t) ^ 2) t := by
  have hne : ∀ i, d i - t ≠ 0 := fun i h => ht ⟨i, (sub_eq_zero.mp h)⟩
  have hterm : ∀ i, HasDerivAt (fun μ => ‖z i‖ ^ 2 / (d i - μ)) (‖z i‖ ^ 2 / (d i - t) ^ 2) t :=
    fun i => by
      have h := (hasDerivAt_const t (‖z i‖ ^ 2)).div
        ((hasDerivAt_const t (d i)).sub (hasDerivAt_id' t)) (hne i)
      convert h using 1
      simp only [Pi.sub_apply]
      ring
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hterm i
  exact (hsum.const_mul ρ).const_add 1

/-- **The secular function is strictly increasing between consecutive poles.** Let $\rho > 0$, let
$z_i \neq 0$ for some $i$, and let $a, b \in \mathbb{R}$ be such that no $d_i$ lies in the open
interval $(a, b)$. Then $f$ is strictly increasing on $(a, b)$, since $f' = \rho \sum_i |z_i|^2
/ (d_i - \lambda)^2 > 0$ there. -/
theorem secularFunction_strictMonoOn (d : n → ℝ) {ρ : ℝ} (hρ : 0 < ρ) (z : n → 𝕜)
    (hz : ∃ i, z i ≠ 0) {a b : ℝ} (hab : ∀ i, d i ∉ Set.Ioo a b) :
    StrictMonoOn (secularFunction d ρ z) (Set.Ioo a b) := by
  have ht : ∀ t ∈ Set.Ioo a b, t ∉ Set.range d := by
    rintro t ht ⟨i, rfl⟩; exact hab i ht
  refine strictMonoOn_of_deriv_pos (convex_Ioo a b)
    (fun t htab => (hasDerivAt_secularFunction d ρ z (ht t htab)).continuousAt.continuousWithinAt)
    fun t htab => ?_
  rw [interior_Ioo] at htab
  rw [(hasDerivAt_secularFunction d ρ z (ht t htab)).deriv]
  obtain ⟨j, hj⟩ := hz
  have hne : ∀ i, d i - t ≠ 0 := fun i h => ht t htab ⟨i, (sub_eq_zero.mp h)⟩
  refine mul_pos hρ (Finset.sum_pos' (fun i _ => by positivity) ⟨j, Finset.mem_univ _, ?_⟩)
  exact div_pos (pow_pos (norm_pos_iff.mpr hj) 2)
    (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (hne j))))

/-- **The secular function is strictly decreasing between consecutive poles.** Let $\rho < 0$, let
$z_i \neq 0$ for some $i$, and let no $d_i$ lie in the open interval $(a, b)$. Then $f$ is
strictly decreasing on $(a, b)$. This is the twin of `Matrix.secularFunction_strictMonoOn`,
since $f_\rho = 2 - f_{-\rho}$. -/
theorem secularFunction_strictAntiOn (d : n → ℝ) {ρ : ℝ} (hρ : ρ < 0) (z : n → 𝕜)
    (hz : ∃ i, z i ≠ 0) {a b : ℝ} (hab : ∀ i, d i ∉ Set.Ioo a b) :
    StrictAntiOn (secularFunction d ρ z) (Set.Ioo a b) := by
  intro x hx y hy hxy
  have h := secularFunction_strictMonoOn d (neg_pos.2 hρ) z hz hab hx hy hxy
  simp only [secularFunction, neg_mul] at h ⊢
  linarith

variable [DecidableEq n] {d : n → ℝ} {ρ : ℝ} {z : n → 𝕜}

omit [DecidableEq n] in
/-- For $z, v \in \mathbb{K}^n$, the rank-one matrix $z z^H$ satisfies $(z z^H v)_i = z_i\,(z^H v)$
for each index $i$. -/
theorem vecMulVec_star_mulVec_apply (z v : n → 𝕜) (i : n) :
    (vecMulVec z (star z) *ᵥ v) i = z i * (star z ⬝ᵥ v) := by
  simp only [mulVec, dotProduct, vecMulVec_apply, Finset.mul_sum, mul_assoc]

/-- For $v \in \mathbb{K}^n$, the entries of $(D + \rho z z^H) v$ are
$d_i v_i + \rho\,(z^H v)\, z_i$. -/
theorem diagonal_add_rankOne_mulVec_apply (v : n → 𝕜) (i : n) :
    (((diagonal fun i => (d i : 𝕜)) + (ρ : 𝕜) • vecMulVec z (star z)) *ᵥ v) i =
      d i * v i + ρ * (star z ⬝ᵥ v) * z i := by
  rw [add_mulVec, Pi.add_apply, mulVec_diagonal, smul_mulVec, Pi.smul_apply, smul_eq_mul]
  rw [vecMulVec_star_mulVec_apply]
  ring

/-- The eigen-equation of $D + \rho z z^H$ row by row ((8.4.4) of [golub2013matrix]). For
$v \in \mathbb{K}^n$ and $\lambda \in \mathbb{K}$, $(D + \rho z z^H) v = \lambda v$ holds if and
only if
$$(d_i - \lambda)\, v_i = -\rho\, (z^H v)\, z_i \quad \text{for every } i.$$
-/
theorem diagonal_add_rankOne_mulVec_eq_iff {v : n → 𝕜} {t : 𝕜} :
    ((diagonal fun i => (d i : 𝕜)) + (ρ : 𝕜) • vecMulVec z (star z)) *ᵥ v = t • v ↔
      ∀ i, ((d i : 𝕜) - t) * v i = -(ρ * (star z ⬝ᵥ v) * z i) := by
  refine ⟨fun h i => ?_, fun h => funext fun i => ?_⟩
  · have := congrFun h i
    rw [diagonal_add_rankOne_mulVec_apply, Pi.smul_apply, smul_eq_mul] at this
    linear_combination this
  · rw [diagonal_add_rankOne_mulVec_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination h i

/-- **Lemma 8.4.2** of [golub2013matrix]. Let the $d_i$ be distinct, let $\rho \neq 0$, and let
$z_i \neq 0$ for every $i$. If $v \neq 0$ and $(D + \rho z z^H) v = \lambda v$ with
$\lambda \in \mathbb{K}$, then $z^H v \neq 0$ and $\lambda \neq d_i$ for every $i$, so
$D - \lambda I$ is invertible.

If $\lambda = d_i$, row $i$ of (8.4.4) forces $z^H v = 0$. Then $D v = \lambda v$, so $v$ is a
multiple of $e_i$ because the $d_j$ are distinct, and $z^H v = \bar{z}_i v_i \neq 0$, a
contradiction. -/
theorem isUnit_diagonal_sub_of_hasEigenvector_add_rankOne (hd : Function.Injective d)
    (hρ : ρ ≠ 0) (hz : ∀ i, z i ≠ 0) {v : n → 𝕜} (hv : v ≠ 0) {t : 𝕜}
    (h : ((diagonal fun i => (d i : 𝕜)) + (ρ : 𝕜) • vecMulVec z (star z)) *ᵥ v = t • v) :
    star z ⬝ᵥ v ≠ 0 ∧ ∀ i, (d i : 𝕜) ≠ t := by
  rw [diagonal_add_rankOne_mulVec_eq_iff] at h
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra! h0; exact hv (funext h0)
  have hw : star z ⬝ᵥ v ≠ 0 := by
    intro hw
    have hdj : (d j : 𝕜) = t := by
      have := h j
      rw [hw, mul_zero, zero_mul, neg_zero] at this
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hj)
    have hvi : ∀ i, i ≠ j → v i = 0 := fun i hij => by
      have := h i
      rw [hw, mul_zero, zero_mul, neg_zero, ← hdj] at this
      refine (mul_eq_zero.mp this).resolve_left fun hd' => hij (hd ?_)
      exact_mod_cast sub_eq_zero.mp hd'
    refine absurd hw ?_
    rw [dotProduct, Finset.sum_eq_single j (fun i _ hij => by rw [hvi i hij, mul_zero])
      (fun h => absurd (Finset.mem_univ j) h)]
    exact mul_ne_zero (by simpa using hz j) hj
  refine ⟨hw, fun i hi => ?_⟩
  have := h i
  rw [hi, sub_self, zero_mul, eq_comm, neg_eq_zero] at this
  exact mul_ne_zero (mul_ne_zero (by exact_mod_cast hρ) hw) (hz i) this

/-- **Theorem 8.4.3(a)** of [golub2013matrix]. Let the $d_i$ be distinct, let $\rho \neq 0$, and let
$z_i \neq 0$ for every $i$. Then $\lambda \in \mathbb{R}$ is an eigenvalue of $D + \rho z z^H$
if and only if $\lambda \neq d_i$ for every $i$ and $f(\lambda) = 0$.

For the forward direction, apply $z^H (D - \lambda I)^{-1}$ to (8.4.4) and cancel
$z^H v \neq 0$. For the converse, $v = (D - \lambda I)^{-1} z$ is an eigenvector, because the
rows of $(D + \rho z z^H - \lambda I) v$ are $f(\lambda) z_i$. The eigenvalue is one of the
endomorphism `Matrix.toLin'` of $\mathbb{K}^n$. -/
theorem hasEigenvalue_iff_secularFunction_eq_zero (hd : Function.Injective d) (hρ : ρ ≠ 0)
    (hz : ∀ i, z i ≠ 0) (t : ℝ) :
    Module.End.HasEigenvalue
        (toLin' ((diagonal fun i => (d i : 𝕜)) + (ρ : 𝕜) • vecMulVec z (star z))) (t : 𝕜) ↔
      t ∉ Set.range d ∧ secularFunction d ρ z t = 0 := by
  constructor
  · intro hev
    obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
    have hMv : ((diagonal fun i => (d i : 𝕜)) + (ρ : 𝕜) • vecMulVec z (star z)) *ᵥ v =
        (t : 𝕜) • v := by
      have := Module.End.mem_eigenspace_iff.mp hv.1
      rwa [toLin'_apply] at this
    obtain ⟨hw, ht⟩ := isUnit_diagonal_sub_of_hasEigenvector_add_rankOne hd hρ hz hv.2 hMv
    have ht' : t ∉ Set.range d := by
      rintro ⟨i, hi⟩; exact ht i (by rw [hi])
    refine ⟨ht', ?_⟩
    rw [diagonal_add_rankOne_mulVec_eq_iff] at hMv
    have hne : ∀ i, ((d i : 𝕜) - t) ≠ 0 := fun i h => ht i (sub_eq_zero.mp h)
    have hvi : ∀ i, v i = -(ρ * (star z ⬝ᵥ v)) * z i / ((d i : 𝕜) - t) := fun i => by
      rw [eq_div_iff (hne i), mul_comm (v i), hMv i]; ring
    have key : star z ⬝ᵥ v = (star z ⬝ᵥ v) * (-(ρ : 𝕜) *
        ∑ i, ((‖z i‖ ^ 2 / (d i - t) : ℝ) : 𝕜)) := by
      conv_lhs => rw [dotProduct]
      simp_rw [hvi, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.star_apply, RCLike.star_def]
      push_cast
      rw [← RCLike.mul_conj]
      ring
    have h1 : (1 : 𝕜) = -(ρ : 𝕜) * ∑ i, ((‖z i‖ ^ 2 / (d i - t) : ℝ) : 𝕜) := by
      have := mul_left_cancel₀ hw (key.symm.trans (mul_one _).symm)
      exact this.symm
    have h2 : (1 : ℝ) = -ρ * ∑ i, ‖z i‖ ^ 2 / (d i - t) := by exact_mod_cast h1
    rw [secularFunction]
    linarith
  · rintro ⟨ht, hf⟩
    have hne : ∀ i, ((d i : 𝕜) - t) ≠ 0 := fun i h =>
      ht ⟨i, by exact_mod_cast sub_eq_zero.mp h⟩
    set v : n → 𝕜 := fun i => z i / ((d i : 𝕜) - t)
    have hv : v ≠ 0 := by
      intro h0
      obtain ⟨j⟩ : Nonempty n := by
        by_contra hn
        rw [not_nonempty_iff] at hn
        simp [secularFunction] at hf
      exact div_ne_zero (hz j) (hne j) (congrFun h0 j)
    have hzv : star z ⬝ᵥ v = ((∑ i, ‖z i‖ ^ 2 / (d i - t) : ℝ) : 𝕜) := by
      simp only [dotProduct, v, Pi.star_apply, RCLike.star_def]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← RCLike.mul_conj]
      ring
    have hsum : (ρ : 𝕜) * ((∑ i, ‖z i‖ ^ 2 / (d i - t) : ℝ) : 𝕜) = -1 := by
      have : ρ * ∑ i, ‖z i‖ ^ 2 / (d i - t) = -1 := by rw [secularFunction] at hf; linarith
      exact_mod_cast this
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨?_, hv⟩
    rw [Module.End.mem_eigenspace_iff, toLin'_apply, diagonal_add_rankOne_mulVec_eq_iff]
    intro i
    rw [hzv, hsum]
    simp only [v]
    rw [mul_div_cancel₀ _ (hne i)]
    ring

/-- **Theorem 8.4.3(c)** of [golub2013matrix]. Let the $d_i$ be distinct, let $\rho \neq 0$, and let
$z_i \neq 0$ for every $i$. If $v \neq 0$ and $(D + \rho z z^H) v = \lambda v$ with
$\lambda \in \mathbb{K}$, then there is a $c \neq 0$ with
$$v = c\, (D - \lambda I)^{-1} z, \qquad v_i = c\, \frac{z_i}{d_i - \lambda}.$$
This follows from (8.4.4), since $D - \lambda I$ is invertible. -/
theorem hasEigenvector_diagonal_add_rankOne_resolvent (hd : Function.Injective d) (hρ : ρ ≠ 0)
    (hz : ∀ i, z i ≠ 0) {v : n → 𝕜} (hv : v ≠ 0) {t : 𝕜}
    (h : ((diagonal fun i => (d i : 𝕜)) + (ρ : 𝕜) • vecMulVec z (star z)) *ᵥ v = t • v) :
    ∃ c : 𝕜, c ≠ 0 ∧ v = c • fun i => z i / ((d i : 𝕜) - t) := by
  obtain ⟨hw, ht⟩ := isUnit_diagonal_sub_of_hasEigenvector_add_rankOne hd hρ hz hv h
  rw [diagonal_add_rankOne_mulVec_eq_iff] at h
  refine ⟨-(ρ * (star z ⬝ᵥ v)), neg_ne_zero.mpr (mul_ne_zero (by exact_mod_cast hρ) hw),
    funext fun i => ?_⟩
  have hne : ((d i : 𝕜) - t) ≠ 0 := sub_ne_zero.mpr (ht i)
  rw [Pi.smul_apply, smul_eq_mul, mul_div_assoc', eq_div_iff hne, mul_comm (v i), h i]
  ring

/-! ### Strict interlacing -/

section Interlacing

variable {N : ℕ}

/-- Let $d \in \mathbb{R}^N$ be decreasing, $d_0 \ge d_1 \ge \dots$, and let
$D = \operatorname{diag}(d)$, as a Hermitian matrix over $\mathbb{K}$. Then the eigenvalues of
$D$, sorted decreasingly, are $d_0, d_1, \dots, d_{N-1}$.

Both lists are sorted, and they are permutations of each other: both are the roots of
$\prod_i (X - d_i)$ (`Matrix.IsHermitian.roots_charpoly_eq_sortedEigenvalues`). The sorted
eigenvalues are `Matrix.IsHermitian.sortedEigenvalues`. -/
theorem IsHermitian.sortedEigenvalues_diagonal {d : Fin N → ℝ} (hd : Antitone d)
    (hD : (diagonal fun i => (d i : 𝕜)).IsHermitian) : hD.sortedEigenvalues = d := by
  have h1 := hD.roots_charpoly_eq_sortedEigenvalues
  have h2 : (diagonal fun i => (d i : 𝕜)).charpoly.roots =
      Multiset.map (RCLike.ofReal ∘ d) Finset.univ.val := roots_charpoly_diagonal _
  rw [h1, ← Multiset.map_map, ← Multiset.map_map] at h2
  have hm := Multiset.map_injective RCLike.ofReal_injective h2
  rw [Fin.univ_val_map, Fin.univ_val_map] at hm
  exact List.ofFn_injective ((Multiset.coe_eq_coe.mp hm).eq_of_sortedGE
    (List.sortedGE_ofFn_iff.mpr hD.sortedEigenvalues_antitone) (List.sortedGE_ofFn_iff.mpr hd))

/-- Each sorted eigenvalue $\lambda_k$ of a Hermitian matrix $M \in \mathbb{K}^{N \times N}$ has an
eigenvector: there is a $v \neq 0$ with $M v = \lambda_k v$. -/
theorem IsHermitian.exists_mulVec_eq_sortedEigenvalues_smul {M : Matrix (Fin N) (Fin N) 𝕜}
    (hM : M.IsHermitian) (k : Fin N) :
    ∃ v : Fin N → 𝕜, v ≠ 0 ∧ M *ᵥ v = (hM.sortedEigenvalues k : 𝕜) • v := by
  obtain ⟨U, hU, -, hcol⟩ := hM.exists_unitary_conj_eq_diagonal_sortedEigenvalues
  refine ⟨U.col k, fun h0 => ?_, hcol k⟩
  have h1 : ∀ i, U i k = 0 := fun i => congrFun h0 i
  have h2 := congrFun (congrFun (mem_unitaryGroup_iff'.1 hU) k) k
  simp [Matrix.mul_apply, h1] at h2

/-- For $c \in \mathbb{R}$, $z \in \mathbb{K}^n$ and $x$ in the Euclidean space $\mathbb{K}^n$, the
quadratic form of the rank-one matrix $c z z^H$ is
$$\operatorname{Re} \langle c z z^H x, x \rangle = c\, |z^H x|^2.$$
-/
theorem re_inner_toEuclideanLin_smul_vecMulVec (c : ℝ) (z : n → 𝕜) (x : EuclideanSpace 𝕜 n) :
    RCLike.re (inner 𝕜 (toEuclideanLin ((c : 𝕜) • vecMulVec z (star z)) x) x) =
      c * ‖star z ⬝ᵥ WithLp.ofLp x‖ ^ 2 := by
  have hmv : ((c : 𝕜) • vecMulVec z (star z)) *ᵥ WithLp.ofLp x =
      ((c : 𝕜) * (star z ⬝ᵥ WithLp.ofLp x)) • z := by
    ext i
    rw [smul_mulVec, Pi.smul_apply, vecMulVec_star_mulVec_apply, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul]
    ring
  rw [EuclideanSpace.inner_eq_star_dotProduct, ofLp_toEuclideanLin, hmv, star_smul,
    dotProduct_smul, smul_eq_mul, dotProduct_comm (WithLp.ofLp x) (star z),
    star_mul', RCLike.star_def, RCLike.conj_ofReal, mul_assoc, RCLike.conj_mul,
    ← RCLike.ofReal_pow, RCLike.re_ofReal_mul, RCLike.ofReal_re]

/-- For $c \in \mathbb{K}$ and $z \in \mathbb{K}^n$, the rank-one matrix $c z z^H$ has rank at most
$1$: its range lies in the span of $z$. -/
theorem finrank_range_toEuclideanLin_smul_vecMulVec_le (c : 𝕜) (z : n → 𝕜) :
    Module.finrank 𝕜 (LinearMap.range (toEuclideanLin (c • vecMulVec z (star z)))) ≤ 1 := by
  have hle : LinearMap.range (toEuclideanLin (c • vecMulVec z (star z))) ≤
      Submodule.span 𝕜 {WithLp.toLp 2 z} := by
    rintro _ ⟨x, rfl⟩
    refine Submodule.mem_span_singleton.mpr ⟨c * (star z ⬝ᵥ WithLp.ofLp x), ?_⟩
    apply (WithLp.ofLp_injective 2)
    rw [ofLp_toEuclideanLin, WithLp.ofLp_smul]
    ext i
    simp only [smul_mulVec, Pi.smul_apply, vecMulVec_star_mulVec_apply, smul_eq_mul]
    ring
  refine (Submodule.finrank_mono hle).trans ?_
  simpa using finrank_span_le_card ({WithLp.toLp 2 z} : Set (EuclideanSpace 𝕜 n))

/-- **Theorem 8.4.3(b)** of [golub2013matrix], strict interlacing. Let $d \in \mathbb{R}^N$ be
strictly decreasing, let $\rho \neq 0$, let $z \in \mathbb{K}^N$ with $z_i \neq 0$ for every
$i$, and let $\lambda_0 \ge \lambda_1 \ge \dots \ge \lambda_{N-1}$ be the eigenvalues of the
Hermitian matrix $D + \rho z z^H$. With indices from $0$:
* if $\rho > 0$, then $d_i < \lambda_i$ for every $i$, and $\lambda_{i+1} < d_i$ for
  $i + 1 < N$, that is, $\lambda_0 > d_0 > \lambda_1 > \dots > \lambda_{N-1} > d_{N-1}$;
* if $\rho < 0$, then $\lambda_i < d_i$ for every $i$, and $d_{i+1} < \lambda_i$ for
  $i + 1 < N$, that is, $d_0 > \lambda_0 > d_1 > \dots > d_{N-1} > \lambda_{N-1}$.

The weak inequalities are the rank-one interlacing
`LinearMap.IsSymmetric.eigenvalues_le_of_isPositive_sub_of_finrank_range_le`, with the sorted
eigenvalues of $D$ equal to $d$ by `Matrix.IsHermitian.sortedEigenvalues_diagonal`. They are
strict because no eigenvalue of $D + \rho z z^H$ is a $d_i$
(`Matrix.isUnit_diagonal_sub_of_hasEigenvector_add_rankOne`, Lemma 8.4.2). The eigenvalues are
`Matrix.IsHermitian.sortedEigenvalues`, and the source indexes from $1$. -/
theorem eigenvalues₀_diagonal_add_rankOne_strictInterlace {d : Fin N → ℝ} (hd : StrictAnti d)
    {ρ : ℝ} (hρ : ρ ≠ 0) {z : Fin N → 𝕜} (hz : ∀ i, z i ≠ 0)
    (hM : ((diagonal fun i => (d i : 𝕜)) + (ρ : 𝕜) • vecMulVec z (star z)).IsHermitian) :
    (0 < ρ → (∀ i, d i < hM.sortedEigenvalues i) ∧
        ∀ i j : Fin N, (j : ℕ) = i + 1 → hM.sortedEigenvalues j < d i) ∧
      (ρ < 0 → (∀ i, hM.sortedEigenvalues i < d i) ∧
        ∀ i j : Fin N, (j : ℕ) = i + 1 → d j < hM.sortedEigenvalues i) := by
  set D : Matrix (Fin N) (Fin N) 𝕜 := diagonal fun i => (d i : 𝕜)
  set P : Matrix (Fin N) (Fin N) 𝕜 := (ρ : 𝕜) • vecMulVec z (star z)
  have hD : D.IsHermitian := isHermitian_diagonal_iff.mpr fun i => by
    simp [IsSelfAdjoint, RCLike.star_def, RCLike.conj_ofReal]
  have hDsort := hD.sortedEigenvalues_diagonal hd.antitone
  -- no eigenvalue of `D + P` is a `d j`
  have hne : ∀ k j, hM.sortedEigenvalues k ≠ d j := fun k j h => by
    obtain ⟨v, hv, hMv⟩ := hM.exists_mulVec_eq_sortedEigenvalues_smul k
    exact (isUnit_diagonal_sub_of_hasEigenvector_add_rankOne hd.injective hρ hz hv hMv).2 j
      (by rw [h])
  have hTD := isSymmetric_toEuclideanLin_iff.mpr hD
  have hTM := isSymmetric_toEuclideanLin_iff.mpr hM
  have hsub : toEuclideanLin (D + P) - toEuclideanLin D = toEuclideanLin P := by
    rw [map_add, add_sub_cancel_left]
  have hrk : Module.finrank 𝕜 (LinearMap.range (toEuclideanLin P)) ≤ 1 :=
    finrank_range_toEuclideanLin_smul_vecMulVec_le _ z
  have hrk' : Module.finrank 𝕜 (LinearMap.range (-toEuclideanLin P)) ≤ 1 := by
    rw [LinearMap.range_neg]; exact hrk
  have hq := re_inner_toEuclideanLin_smul_vecMulVec ρ z
  -- the eigenvalue indices in `Fin (Fintype.card (Fin N))`
  have hidx : ∀ i j : Fin N, (hij : (j : ℕ) = i + 1) →
      (⟨(Fin.cast (Fintype.card_fin N).symm i : ℕ) + 1, by simp; omega⟩ :
        Fin (Fintype.card (Fin N))) = Fin.cast (Fintype.card_fin N).symm j := fun i j hij => by
    ext; simp [hij]
  have hsD : ∀ k : Fin N, hTD.eigenvalues finrank_euclideanSpace
      (Fin.cast (Fintype.card_fin N).symm k) = d k := fun k => congrFun hDsort k
  refine ⟨fun hρ0 => ⟨fun i => ?_, fun i j hij => ?_⟩, fun hρ0 => ⟨fun i => ?_, fun i j hij => ?_⟩⟩
  · -- `d i ≤ λ i`
    have h := hTD.eigenvalues_le_of_re_inner_le hTM finrank_euclideanSpace (fun x => by
      rw [map_add, LinearMap.add_apply, inner_add_left, map_add, hq x]
      nlinarith [sq_nonneg ‖star z ⬝ᵥ WithLp.ofLp x‖]) (Fin.cast (Fintype.card_fin N).symm i)
    rw [hsD] at h
    exact lt_of_le_of_ne h (hne i i).symm
  · have hpos : (toEuclideanLin (D + P) - toEuclideanLin D).IsPositive :=
      ⟨hTM.sub hTD, fun x => by rw [hsub, hq x]; positivity⟩
    have h := (hTD.eigenvalues_le_of_isPositive_sub_of_finrank_range_le hTM
      finrank_euclideanSpace hpos (r := 1) (by rwa [hsub])
      (Fin.cast (Fintype.card_fin N).symm i) (by simp; omega)).1
    rw [hidx i j hij, hsD] at h
    exact lt_of_le_of_ne h (hne j i)
  · have h := hTM.eigenvalues_le_of_re_inner_le hTD finrank_euclideanSpace (fun x => by
      rw [map_add, LinearMap.add_apply, inner_add_left, map_add, hq x]
      nlinarith [sq_nonneg ‖star z ⬝ᵥ WithLp.ofLp x‖]) (Fin.cast (Fintype.card_fin N).symm i)
    rw [hsD] at h
    exact lt_of_le_of_ne h (hne i i)
  · have hsub' : toEuclideanLin D - toEuclideanLin (D + P) = -toEuclideanLin P := by
      rw [← neg_sub, hsub]
    have hpos : (toEuclideanLin D - toEuclideanLin (D + P)).IsPositive :=
      ⟨hTD.sub hTM, fun x => by
        rw [hsub', LinearMap.neg_apply, inner_neg_left, map_neg, hq x]
        nlinarith [sq_nonneg ‖star z ⬝ᵥ WithLp.ofLp x‖]⟩
    have h := (hTM.eigenvalues_le_of_isPositive_sub_of_finrank_range_le hTD
      finrank_euclideanSpace hpos (r := 1) (by rwa [hsub'])
      (Fin.cast (Fintype.card_fin N).symm i) (by simp; omega)).1
    rw [hidx i j hij, hsD] at h
    exact lt_of_le_of_ne h (hne i j).symm

end Interlacing

/-! ### Deflation to the generic case -/

section Deflation

variable {N : ℕ}

/-- A plane rotation in the plane of two equal diagonal entries $d_j = d_k$ commutes with
$\operatorname{diag}(d)$. -/
private theorem planeRotation_mul_diagonal_comm {d : Fin N → ℝ} {j k : Fin N} (hjk : j ≠ k)
    (hd : d j = d k) (c s : ℝ) :
    planeRotation j k c s * diagonal d = diagonal d * planeRotation j k c s := by
  ext p q
  rw [mul_diagonal, diagonal_mul, planeRotation_apply hjk]
  split_ifs <;> subst_vars <;>
    first | ring1 | (rw [hd]; try ring1)

/-- Rotations in the planes of repeated diagonal entries give an orthogonal $V$ with $V^T D V = D$
such that $V^T z$ has at most one nonzero entry for each value of $d$; this is the first step of
Theorem 8.4.4 of [golub2013matrix], repeated. -/
private theorem exists_orthogonal_distinct_of_ne_zero (d : Fin N → ℝ) :
    ∀ (m : ℕ) (z : Fin N → ℝ), (Finset.univ.filter fun i => z i ≠ 0).card = m →
      ∃ V ∈ orthogonalGroup (Fin N) ℝ, Vᵀ * diagonal d * V = diagonal d ∧
        ∀ i j, i ≠ j → d i = d j → (Vᵀ *ᵥ z) i ≠ 0 → (Vᵀ *ᵥ z) j = 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro z hm
  by_cases hgood : ∀ i j, i ≠ j → d i = d j → z i ≠ 0 → z j = 0
  · exact ⟨1, one_mem _, by simp, by simpa using hgood⟩
  push Not at hgood
  obtain ⟨i, j, hij, hd, hzi, hzj⟩ := hgood
  set G := planeRotation i j (givensPair (z i) (z j)).1 (givensPair (z i) (z j)).2 with hG
  obtain ⟨hz'j, -, hz'q⟩ := transpose_planeRotation_givensPair_mulVec hij z
  set z' := Gᵀ *ᵥ z with hz'
  have hsub : (Finset.univ.filter fun q => z' q ≠ 0) ⊆
      (Finset.univ.filter fun q => z q ≠ 0).erase j := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hq ⊢
    refine ⟨fun h => hq (h ▸ hz'j), ?_⟩
    by_cases hqi : q = i
    · exact hqi ▸ hzi
    · by_cases hqj : q = j
      · exact absurd (hqj ▸ hz'j) hq
      · rwa [hz'q q hqi hqj] at hq
  have hlt : (Finset.univ.filter fun q => z' q ≠ 0).card < m := by
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (by simpa using hzj), hm] at this
    have : 0 < m := hm ▸ Finset.card_pos.mpr ⟨j, by simpa using hzj⟩
    omega
  obtain ⟨V, hV, hVD, hVz⟩ := ih _ hlt z' rfl
  have hGo : G ∈ orthogonalGroup (Fin N) ℝ :=
    planeRotation_mem_orthogonalGroup hij (givensPair_sq_add_sq _ _)
  have hGG : Gᵀ * G = 1 := transpose_planeRotation_mul_self hij (givensPair_sq_add_sq _ _)
  have hGD : Gᵀ * diagonal d * G = diagonal d := by
    rw [Matrix.mul_assoc, ← planeRotation_mul_diagonal_comm hij hd, ← Matrix.mul_assoc, hGG,
      Matrix.one_mul]
  refine ⟨G * V, mul_mem hGo hV, ?_, ?_⟩
  · rw [transpose_mul, show Vᵀ * Gᵀ * diagonal d * (G * V) = Vᵀ * (Gᵀ * diagonal d * G) * V by
      simp only [Matrix.mul_assoc], hGD, hVD]
  · rw [transpose_mul, ← mulVec_mulVec]
    exact hVz

/-- **Theorem 8.4.4** of [golub2013matrix] (deflation to the generic case). Let
$d, z \in \mathbb{R}^N$. Then there are an orthogonal $V_1 \in \mathbb{R}^{N \times N}$, a
vector $\mu \in \mathbb{R}^N$ and a number $r \le N$ such that, with indices from $0$:
* $V_1^T \operatorname{diag}(d) V_1 = \operatorname{diag}(\mu)$;
* $\mu$ is strictly decreasing on the first $r$ indices: $\mu_j < \mu_i$ for $i < j < r$;
* $\mu$ is decreasing on the other indices: $\mu_j \le \mu_i$ for $r \le i \le j$;
* $w = V_1^T z$ satisfies $w_i \neq 0$ if and only if $i < r$.

Rotations in the planes of repeated $d_i$ make all entries of $z$ but one zero for each value of
$d$. A permutation then sorts the nonzero entries to the front by decreasing $\mu$, and the
others behind them by decreasing $\mu$. The source states the ordering as $\mu_1 > \dots > \mu_r
\ge \mu_{r+1} \ge \dots \ge \mu_n$. Across the boundary this is false in general: for
$d = (2, 1)$ and $z = (0, 1)$, the only nonzero entry of $w$ belongs to the eigenvalue $1$, so
$\mu_1 = 1 < \mu_2 = 2$. So only the two separate orderings are stated. -/
theorem exists_orthogonal_deflation (d z : Fin N → ℝ) :
    ∃ V₁ ∈ orthogonalGroup (Fin N) ℝ, ∃ μ : Fin N → ℝ, ∃ r ≤ N,
      V₁ᵀ * diagonal d * V₁ = diagonal μ ∧
      (∀ i j : Fin N, i < j → (j : ℕ) < r → μ j < μ i) ∧
      (∀ i j : Fin N, r ≤ (i : ℕ) → i ≤ j → μ j ≤ μ i) ∧
      ∀ i, (V₁ᵀ *ᵥ z) i ≠ 0 ↔ (i : ℕ) < r := by
  classical
  obtain ⟨V, hV, hVD, hVz⟩ := exists_orthogonal_distinct_of_ne_zero d _ z rfl
  set w := Vᵀ *ᵥ z
  -- sort by (inactive, decreasing `d`)
  set key : Fin N → Lex (ℕ × ℝ) := fun i => toLex ((if w i ≠ 0 then 0 else 1), -d i) with hkey
  set σ : Fin N ≃ Fin N := Tuple.sort key
  have hmono : Monotone (key ∘ σ) := Tuple.monotone_sort key
  set r := (Finset.univ.filter fun i => w i ≠ 0).card
  have hr : r ≤ N := (Finset.card_filter_le _ _).trans (by simp)
  have hcount : (Finset.univ.filter fun i => w (σ i) ≠ 0).card = r := by
    exact Finset.card_bij (fun i _ => σ i) (fun a ha => by simpa using ha)
      (fun _ _ _ _ h => σ.injective h) (fun b hb => ⟨σ.symm b, by simpa using hb, by simp⟩)
  -- the first component of the key is monotone along `σ`
  have hfst : ∀ a b : Fin N, a ≤ b → w (σ b) ≠ 0 → w (σ a) ≠ 0 := by
    intro a b hab hb ha
    have h := hmono hab
    simp only [Function.comp_apply, hkey, ha, hb, ne_eq, not_true_eq_false, not_false_eq_true,
      ↓reduceIte] at h
    rw [Prod.Lex.toLex_le_toLex] at h
    rcases h with h | ⟨h, -⟩ <;> omega
  have hactive : ∀ i : Fin N, w (σ i) ≠ 0 ↔ (i : ℕ) < r := by
    intro i
    constructor
    · intro hi
      by_contra hri
      push Not at hri
      have hsub : Finset.Iic i ⊆ Finset.univ.filter fun a => w (σ a) ≠ 0 := fun a ha => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic] at ha ⊢
        exact hfst a i ha hi
      have h1 := Finset.card_le_card hsub
      rw [hcount, Fin.card_Iic] at h1
      omega
    · intro hri
      by_contra hi
      have hsub : Finset.univ.filter (fun a => w (σ a) ≠ 0) ⊆ Finset.Iio i := fun a ha => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio] at ha ⊢
        by_contra hai
        exact (hfst i a (not_lt.mp hai) ha) hi
      have h1 := Finset.card_le_card hsub
      rw [hcount, Fin.card_Iio] at h1
      omega
  -- the permutation matrix
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin N) (Fin N) ℝ, P = σ.symm.toPEquiv.toMatrix := ⟨_, rfl⟩
  have hPt : Pᵀ = σ.toPEquiv.toMatrix := by
    rw [hP, ← PEquiv.toMatrix_symm, ← Equiv.toPEquiv_symm, Equiv.symm_symm]
  have hconj (M : Matrix (Fin N) (Fin N) ℝ) : Pᵀ * M * P = M.submatrix σ σ := by
    rw [hPt, hP, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm,
      submatrix_submatrix]
    rfl
  have hPP : Pᵀ * P = 1 := by
    rw [← Matrix.mul_one Pᵀ, hconj, submatrix_one_equiv]
  have hPo : P ∈ orthogonalGroup (Fin N) ℝ := (mem_orthogonalGroup_iff' (Fin N) ℝ).2 hPP
  refine ⟨V * P, mul_mem hV hPo, d ∘ σ, r, hr, ?_, fun i j hij hjr => ?_, fun i j hri hij => ?_,
    fun i => ?_⟩
  · rw [transpose_mul, show Pᵀ * Vᵀ * diagonal d * (V * P) = Pᵀ * (Vᵀ * diagonal d * V) * P by
      simp only [Matrix.mul_assoc], hVD, hconj, submatrix_diagonal_equiv]
  · -- two active indices: equal first components, decreasing `d`, and distinct values
    have hj := (hactive j).mpr hjr
    have hi := (hactive i).mpr (lt_trans (Fin.lt_def.mp hij) hjr)
    have h := hmono hij.le
    simp only [Function.comp_apply, hkey, hi, hj, ne_eq, not_false_eq_true, ↓reduceIte] at h
    rw [Prod.Lex.toLex_le_toLex] at h
    have hle : d (σ j) ≤ d (σ i) := by
      rcases h with h | ⟨-, h⟩
      · exact absurd h (lt_irrefl _)
      · linarith
    refine lt_of_le_of_ne hle fun heq => ?_
    exact hj (hVz (σ i) (σ j) (σ.injective.ne hij.ne) heq.symm hi)
  · -- two inactive indices: equal first components and decreasing `d`
    have hi : w (σ i) = 0 := by
      by_contra h
      have := (hactive i).mp h
      omega
    have hj : w (σ j) = 0 := by
      by_contra h
      have := (hactive j).mp h
      have : (i : ℕ) ≤ j := hij
      omega
    have h := hmono hij
    simp only [Function.comp_apply, hkey, hi, hj, ne_eq, not_true_eq_false, ↓reduceIte] at h
    rw [Prod.Lex.toLex_le_toLex] at h
    rcases h with h | ⟨-, h⟩
    · exact absurd h (lt_irrefl _)
    · simp only [Function.comp_apply]
      linarith
  · rw [transpose_mul, ← mulVec_mulVec, hPt, PEquiv.toMatrix_toPEquiv_mulVec, Function.comp_apply]
    exact hactive i

end Deflation

/-! ### The merge step of divide and conquer -/

/-- **The merge step of divide and conquer** (§8.4.4 of [golub2013matrix]). Let
$T_1 \in \mathbb{R}^{m_1 \times m_1}$ and $T_2 \in \mathbb{R}^{m_2 \times m_2}$, and let $Q_1$,
$Q_2$ be orthogonal with $Q_1^T T_1 Q_1 = \operatorname{diag}(d_1)$ and
$Q_2^T T_2 Q_2 = \operatorname{diag}(d_2)$. Let $\rho \in \mathbb{R}$ and
$v \in \mathbb{R}^{m_1 + m_2}$. Then $U = \operatorname{diag}(Q_1, Q_2)$ is orthogonal, and
$$U^T \bigl(\operatorname{diag}(T_1, T_2) + \rho v v^T\bigr) U = \operatorname{diag}(d_1, d_2) +
  \rho z z^T, \qquad z = U^T v.$$

Block matrices are indexed by `m₁ ⊕ m₂`, and $U$ is `Matrix.fromBlocks Q₁ 0 0 Q₂`. -/
theorem conj_fromBlocks_add_rankOne_eq {m₁ m₂ : Type*} [Fintype m₁] [Fintype m₂]
    [DecidableEq m₁] [DecidableEq m₂] {T₁ Q₁ : Matrix m₁ m₁ ℝ} {T₂ Q₂ : Matrix m₂ m₂ ℝ}
    (hQ₁ : Q₁ ∈ orthogonalGroup m₁ ℝ) (hQ₂ : Q₂ ∈ orthogonalGroup m₂ ℝ) {d₁ : m₁ → ℝ}
    {d₂ : m₂ → ℝ} (h₁ : Q₁ᵀ * T₁ * Q₁ = diagonal d₁) (h₂ : Q₂ᵀ * T₂ * Q₂ = diagonal d₂) (ρ : ℝ)
    (v : m₁ ⊕ m₂ → ℝ) :
    fromBlocks Q₁ 0 0 Q₂ ∈ orthogonalGroup (m₁ ⊕ m₂) ℝ ∧
      (fromBlocks Q₁ 0 0 Q₂)ᵀ * (fromBlocks T₁ 0 0 T₂ + ρ • vecMulVec v v) * fromBlocks Q₁ 0 0 Q₂ =
        diagonal (Sum.elim d₁ d₂) +
          ρ • vecMulVec ((fromBlocks Q₁ 0 0 Q₂)ᵀ *ᵥ v) ((fromBlocks Q₁ 0 0 Q₂)ᵀ *ᵥ v) := by
  set U : Matrix (m₁ ⊕ m₂) (m₁ ⊕ m₂) ℝ := fromBlocks Q₁ 0 0 Q₂
  have hUt : Uᵀ = fromBlocks Q₁ᵀ 0 0 Q₂ᵀ := by
    rw [fromBlocks_transpose, transpose_zero, transpose_zero]
  have hQ₁' : Q₁ * Q₁ᵀ = 1 := by
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      mem_unitaryGroup_iff.mp hQ₁
  have hQ₂' : Q₂ * Q₂ᵀ = 1 := by
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      mem_unitaryGroup_iff.mp hQ₂
  refine ⟨mem_unitaryGroup_iff.mpr ?_, ?_⟩
  · rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, hUt, fromBlocks_multiply]
    simp [hQ₁', hQ₂', fromBlocks_one]
  · have hconj : Uᵀ * fromBlocks T₁ 0 0 T₂ * U = diagonal (Sum.elim d₁ d₂) := by
      rw [hUt, fromBlocks_multiply, fromBlocks_multiply, ← fromBlocks_diagonal, ← h₁, ← h₂]
      simp
    have hrank : Uᵀ * vecMulVec v v * U = vecMulVec (Uᵀ *ᵥ v) (Uᵀ *ᵥ v) := by
      rw [mul_vecMulVec, vecMulVec_mul, mulVec_transpose]
    rw [Matrix.mul_add, Matrix.add_mul, hconj, Matrix.mul_smul, Matrix.smul_mul, hrank]

/-! ### The bordered secular function -/

section Bordered

variable {m : ℕ}

/-- The **bordered secular function** of $T = \begin{bmatrix} 1 & r^T \\ r & B \end{bmatrix}$
(§4.7.7 of [golub2013matrix], after Cybenko and Van Loan, 1986): for $r \in \mathbb{R}^m$ and
$B \in \mathbb{R}^{m \times m}$,
$$f(\lambda) = 1 - \lambda - r^T (B - \lambda I)^{-1} r.$$
Its zero below the spectrum of $B$ is the smallest eigenvalue of $T$ under the condition
(4.7.8).

Only the unit corner of $T$ is used, not the Toeplitz structure of the source. If
$B - \lambda I$ is singular, the Lean inverse is $0$ and the value is $1 - \lambda$. The
relation to `Matrix.secularFunction` is `Matrix.borderedSecularFunction_eq_secularFunction_sub`. -/
noncomputable def borderedSecularFunction (r : Fin m → ℝ) (B : Matrix (Fin m) (Fin m) ℝ)
    (t : ℝ) : ℝ :=
  1 - t - r ⬝ᵥ ((B - t • 1)⁻¹ *ᵥ r)

/-- **An eigenvalue of the bordered matrix is a zero of the bordered secular function** (§4.7.7 of
[golub2013matrix]). Let $r \in \mathbb{R}^m$, $B \in \mathbb{R}^{m \times m}$,
$\lambda, \alpha \in \mathbb{R}$ and $y \in \mathbb{R}^m$, with $B - \lambda I$ invertible and
$(\alpha, y) \neq 0$. If
$$\begin{bmatrix} 1 & r^T \\ r & B \end{bmatrix} \begin{bmatrix} \alpha \\ y \end{bmatrix} =
  \lambda \begin{bmatrix} \alpha \\ y \end{bmatrix},$$
then $\alpha \neq 0$, $y = -\alpha (B - \lambda I)^{-1} r$, and $f(\lambda) = 0$.

The formula for $y$ is the second block row, and $f(\lambda) = 0$ is the first block row divided
by $\alpha$. The block matrix is indexed by `Fin 1 ⊕ Fin m`, with the row
`Matrix.replicateRow (Fin 1) r` and the column `Matrix.replicateCol (Fin 1) r`. -/
theorem borderedSecularFunction_eq_zero_of_mulVec_eq {r : Fin m → ℝ}
    {B : Matrix (Fin m) (Fin m) ℝ} {t α : ℝ} {y : Fin m → ℝ} (hB : IsUnit (B - t • 1))
    (hne : Sum.elim (fun _ : Fin 1 => α) y ≠ 0)
    (h : fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) (replicateRow (Fin 1) r)
        (replicateCol (Fin 1) r) B *ᵥ Sum.elim (fun _ => α) y = t • Sum.elim (fun _ => α) y) :
    α ≠ 0 ∧ y = -α • ((B - t • 1)⁻¹ *ᵥ r) ∧ borderedSecularFunction r B t = 0 := by
  have hrow : ∀ i, (fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) (replicateRow (Fin 1) r)
      (replicateCol (Fin 1) r) B *ᵥ Sum.elim (fun _ => α) y) i =
        t * Sum.elim (fun _ => α) y i := fun i => by rw [h]; rfl
  have h1' : α + r ⬝ᵥ y = t * α := by
    have := hrow (Sum.inl 0)
    rw [fromBlocks_mulVec, Sum.elim_inl, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.add_apply,
      one_mulVec, Sum.elim_inl] at this
    rw [← this]
    rfl
  have h2' : (B - t • 1) *ᵥ y = -α • r := by
    ext i
    have := hrow (Sum.inr i)
    rw [fromBlocks_mulVec, Sum.elim_inr, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.add_apply,
      Sum.elim_inr] at this
    have hc : (replicateCol (Fin 1) r *ᵥ fun _ => α) i = r i * α := by
      simp [mulVec, dotProduct, replicateCol_apply]
    rw [hc] at this
    rw [sub_mulVec, Pi.sub_apply, smul_mulVec, one_mulVec, Pi.smul_apply, Pi.smul_apply,
      smul_eq_mul, smul_eq_mul]
    linarith
  have hy : y = -α • ((B - t • 1)⁻¹ *ᵥ r) := by
    have hdet := (isUnit_iff_isUnit_det _).mp hB
    rw [← mulVec_smul, ← h2', mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
  have hα : α ≠ 0 := by
    rintro rfl
    apply hne
    rw [hy, neg_zero, zero_smul]
    ext i; cases i <;> rfl
  refine ⟨hα, hy, ?_⟩
  rw [hy, dotProduct_smul, smul_eq_mul] at h1'
  have : α * borderedSecularFunction r B t = 0 := by
    rw [borderedSecularFunction]; linear_combination h1'
  exact (mul_eq_zero.mp this).resolve_left hα

/-- **Powers of the resolvent in an eigenbasis.** Let $B, Q \in \mathbb{R}^{m \times m}$ with $Q$
orthogonal and $Q^T B Q = \operatorname{diag}(d)$, let $\lambda \in \mathbb{R}$ be no $d_i$, and
let $k \in \mathbb{N}$. Then for every $r \in \mathbb{R}^m$
$$r^T \bigl((B - \lambda I)^{-1}\bigr)^k r = \sum_i \frac{(Q^T r)_i^2}{(d_i - \lambda)^k}.$$
-/
theorem dotProduct_inv_sub_smul_one_pow_mulVec {r : Fin m → ℝ}
    {B Q : Matrix (Fin m) (Fin m) ℝ} (hQ : Q ∈ orthogonalGroup (Fin m) ℝ) {d : Fin m → ℝ}
    (hQB : Qᵀ * B * Q = diagonal d) {t : ℝ} (ht : t ∉ Set.range d) (k : ℕ) :
    r ⬝ᵥ ((B - t • 1)⁻¹ ^ k *ᵥ r) = ∑ i, (Qᵀ *ᵥ r) i ^ 2 / (d i - t) ^ k := by
  have hQB' : star Q * B * Q = diagonal d := by
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have hc : ∀ i, d i ≠ t := fun i h => ht ⟨i, h⟩
  have hQQ : Qᵀ * Q = 1 := by
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      mem_unitaryGroup_iff'.mp hQ
  have hQQ' : Q * Qᵀ = 1 := by
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      mem_unitaryGroup_iff.mp hQ
  set f : Fin m → ℝ := fun i => (d i - t)⁻¹
  have hinv : (B - t • 1)⁻¹ = Q * diagonal f * Qᵀ := by
    rw [sub_smul_one_eq_mul_diagonal_mul_star hQ hQB' t, inv_mul_mul_star_of_mem_unitaryGroup hQ,
      star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
    congr 2
    exact inv_eq_right_inv (by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      exact congrArg diagonal (funext fun i => mul_inv_cancel₀ (sub_ne_zero.mpr (hc i))))
  have hpow : ∀ k : ℕ, (Q * diagonal f * Qᵀ) ^ k = Q * diagonal (fun i => f i ^ k) * Qᵀ := by
    intro k
    induction k with
    | zero => simp [hQQ']
    | succ k ih =>
      calc (Q * diagonal f * Qᵀ) ^ (k + 1)
          = Q * (diagonal (fun i => f i ^ k) * (Qᵀ * Q) * diagonal f) * Qᵀ := by
            rw [pow_succ, ih]; simp only [Matrix.mul_assoc]
        _ = Q * diagonal (fun i => f i ^ (k + 1)) * Qᵀ := by
            rw [hQQ, Matrix.mul_one, diagonal_mul_diagonal]; simp only [← pow_succ]
  rw [hinv, hpow, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose,
    dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_diagonal, inv_pow, div_eq_mul_inv]
  ring

/-- **The bordered secular function in an eigenbasis of the border block.** Let
$B, Q \in \mathbb{R}^{m \times m}$ with $Q$ orthogonal and $Q^T B Q = \operatorname{diag}(d)$,
and let $\lambda \in \mathbb{R}$ be no $d_i$. Then
$$1 - \lambda - r^T (B - \lambda I)^{-1} r = 1 - \lambda - \sum_i \frac{(Q^T r)_i^2}{d_i -
  \lambda},$$
that is, the bordered secular function at $\lambda$ is the secular function
`Matrix.secularFunction d (-1) (Qᵀ *ᵥ r)` at $\lambda$, minus $\lambda$.

This connects the Newton iteration of §4.7.7 of [golub2013matrix] for the smallest eigenvalue of
a bordered matrix with the poles of §8.4.3: one root lies below $\min_i d_i$, and the others
interlace the $d_i$. -/
theorem borderedSecularFunction_eq_secularFunction_sub {r : Fin m → ℝ}
    {B Q : Matrix (Fin m) (Fin m) ℝ} (hQ : Q ∈ orthogonalGroup (Fin m) ℝ) {d : Fin m → ℝ}
    (hQB : Qᵀ * B * Q = diagonal d) {t : ℝ} (ht : t ∉ Set.range d) :
    borderedSecularFunction r B t = secularFunction d (-1) (Qᵀ *ᵥ r) t - t := by
  have key := dotProduct_inv_sub_smul_one_pow_mulVec (r := r) hQ hQB ht 1
  simp only [pow_one] at key
  rw [borderedSecularFunction, secularFunction, key]
  simp only [Real.norm_eq_abs, sq_abs]
  ring

/-- A real symmetric matrix $B$ has an orthogonal $Q$ with
$Q^T B Q = \operatorname{diag}(\lambda_i)$, where the $\lambda_i$ are the eigenvalues
`Matrix.IsHermitian.eigenvalues` of $B$. -/
private theorem IsHermitian.exists_orthogonal_transpose_mul_mul_eq {B : Matrix (Fin m) (Fin m) ℝ}
    (hB : B.IsHermitian) :
    ∃ Q ∈ orthogonalGroup (Fin m) ℝ, Qᵀ * B * Q = diagonal hB.eigenvalues :=
  ⟨hB.eigenvectorUnitary, hB.eigenvectorUnitary.2, hB.transpose_eigenvectorUnitary_mul_mul⟩

/-- **The derivatives of the bordered secular function** (§4.7.7 of [golub2013matrix]). Let
$B \in \mathbb{R}^{m \times m}$ be symmetric, let $r \in \mathbb{R}^m$, and let
$\lambda \in \mathbb{R}$ be no eigenvalue of $B$. Then the bordered secular function $f$
satisfies
$$f'(\lambda) = -1 - \|(B - \lambda I)^{-1} r\|^2, \qquad f''(\lambda) = -2\, r^T (B - \lambda
  I)^{-3} r.$$

Away from the eigenvalues of $B$, $f$ agrees with the rational function $1 - \lambda - \sum_i
(Q^T r)_i^2 / (d_i - \lambda)$ in an eigenbasis of $B$
(`Matrix.borderedSecularFunction_eq_secularFunction_sub`), which is differentiated term by term.
The sums are converted back by `Matrix.dotProduct_inv_sub_smul_one_pow_mulVec`. The second
derivative is the derivative at $\lambda$ of `deriv (Matrix.borderedSecularFunction r B)`. -/
theorem hasDerivAt_borderedSecularFunction {r : Fin m → ℝ} {B : Matrix (Fin m) (Fin m) ℝ}
    (hB : B.IsHermitian) {t : ℝ} (ht : ∀ i, hB.eigenvalues i ≠ t) :
    HasDerivAt (borderedSecularFunction r B)
        (-1 - ((B - t • 1)⁻¹ *ᵥ r) ⬝ᵥ ((B - t • 1)⁻¹ *ᵥ r)) t ∧
      HasDerivAt (deriv (borderedSecularFunction r B))
        (-2 * (r ⬝ᵥ ((B - t • 1)⁻¹ ^ 3 *ᵥ r))) t := by
  obtain ⟨Q, hQ, hQB⟩ := hB.exists_orthogonal_transpose_mul_mul_eq
  set d := hB.eigenvalues
  set w := Qᵀ *ᵥ r
  have hopen : (Set.range d)ᶜ ∈ nhds t :=
    (Set.finite_range d).isClosed.isOpen_compl.mem_nhds fun ⟨i, hi⟩ => ht i hi
  -- the first derivative at every non-pole
  have hd1 : ∀ s ∉ Set.range d, HasDerivAt (borderedSecularFunction r B)
      (-1 - ∑ i, w i ^ 2 / (d i - s) ^ 2) s := fun s hs => by
    have hev : borderedSecularFunction r B =ᶠ[nhds s] fun u => secularFunction d (-1) w u - u := by
      filter_upwards [(Set.finite_range d).isClosed.isOpen_compl.mem_nhds hs] with u hu
      exact borderedSecularFunction_eq_secularFunction_sub hQ hQB hu
    have h := (hasDerivAt_secularFunction d (-1) w hs).sub (hasDerivAt_id' s)
    refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
    simp only [Real.norm_eq_abs, sq_abs]
    ring
  -- the resolvent is symmetric, so `‖(B - λ)⁻¹ r‖² = rᵀ (B - λ)⁻² r`
  have hsymm : ((B - t • 1)⁻¹)ᵀ = (B - t • 1)⁻¹ := by
    rw [transpose_nonsing_inv, transpose_sub, transpose_smul, transpose_one,
      ← conjTranspose_eq_transpose_of_trivial, hB.eq]
  have hvv : ((B - t • 1)⁻¹ *ᵥ r) ⬝ᵥ ((B - t • 1)⁻¹ *ᵥ r) = r ⬝ᵥ ((B - t • 1)⁻¹ ^ 2 *ᵥ r) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hsymm, mulVec_mulVec, dotProduct_comm, sq]
  have htd : t ∉ Set.range d := fun ⟨i, hi⟩ => ht i hi
  refine ⟨?_, ?_⟩
  · rw [hvv, dotProduct_inv_sub_smul_one_pow_mulVec hQ hQB htd 2]
    exact hd1 t htd
  · have hev : deriv (borderedSecularFunction r B) =ᶠ[nhds t]
        fun s => -1 - ∑ i, w i ^ 2 / (d i - s) ^ 2 := by
      filter_upwards [hopen] with s hs
      exact (hd1 s hs).deriv
    have hterm : ∀ i, HasDerivAt (fun s => w i ^ 2 / (d i - s) ^ 2)
        (2 * (w i ^ 2 / (d i - t) ^ 3)) t := fun i => by
      have hne : d i - t ≠ 0 := sub_ne_zero.mpr (ht i)
      have h := (hasDerivAt_const t (w i ^ 2)).div
        (((hasDerivAt_const t (d i)).sub (hasDerivAt_id' t)).pow 2) (pow_ne_zero 2 hne)
      convert h using 1
      simp only [Pi.sub_apply, Pi.pow_apply]
      field_simp
      ring
    have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hterm i
    refine (((hasDerivAt_const t (-1 : ℝ)).sub hsum).congr_of_eventuallyEq hev).congr_deriv ?_
    rw [dotProduct_inv_sub_smul_one_pow_mulVec hQ hQB htd 3, ← Finset.mul_sum]
    ring

/-- **The signs of the derivatives below the spectrum of $B$** (§4.7.7 of [golub2013matrix]). Let
$B \in \mathbb{R}^{m \times m}$ be symmetric, let $r \in \mathbb{R}^m$, and let
$\lambda \in \mathbb{R}$ be less than every eigenvalue of $B$. Then
$$-1 - \|(B - \lambda I)^{-1} r\|^2 \le -1 \quad\text{and}\quad -2\, r^T (B - \lambda I)^{-3} r
  \le 0.$$
By `Matrix.hasDerivAt_borderedSecularFunction`, these are $f'(\lambda)$ and $f''(\lambda)$. So
$f$ is strictly decreasing and concave below the spectrum of $B$, and this makes the Newton
iteration (4.7.10) converge monotonically. -/
theorem neg_one_sub_dotProduct_le_and_neg_two_mul_dotProduct_nonpos {r : Fin m → ℝ}
    {B : Matrix (Fin m) (Fin m) ℝ}
    (hB : B.IsHermitian) {t : ℝ} (ht : ∀ i, t < hB.eigenvalues i) :
    -1 - ((B - t • 1)⁻¹ *ᵥ r) ⬝ᵥ ((B - t • 1)⁻¹ *ᵥ r) ≤ -1 ∧
      -2 * (r ⬝ᵥ ((B - t • 1)⁻¹ ^ 3 *ᵥ r)) ≤ 0 := by
  obtain ⟨Q, hQ, hQB⟩ := hB.exists_orthogonal_transpose_mul_mul_eq
  have htd : t ∉ Set.range hB.eigenvalues := fun ⟨i, hi⟩ => (ht i).ne' hi
  refine ⟨?_, ?_⟩
  · have : 0 ≤ ((B - t • 1)⁻¹ *ᵥ r) ⬝ᵥ ((B - t • 1)⁻¹ *ᵥ r) :=
      Finset.sum_nonneg fun i _ => mul_self_nonneg _
    linarith
  · rw [dotProduct_inv_sub_smul_one_pow_mulVec hQ hQB htd 3]
    have : 0 ≤ ∑ i, (Qᵀ *ᵥ r) i ^ 2 / (hB.eigenvalues i - t) ^ 3 :=
      Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (pow_nonneg (by linarith [ht i]) 3)
    linarith

open Filter Topology Set in
/-- **Newton's method for the smallest eigenvalue of a bordered matrix converges monotonically from
the right** ((4.7.9) and (4.7.10) of [golub2013matrix], after Cybenko and Van Loan, 1986). Let
$B \in \mathbb{R}^{m \times m}$ be symmetric, let $r \in \mathbb{R}^m$, and let $f$ be the
bordered secular function. Let $\alpha, \lambda^{(0)} \in \mathbb{R}$ with $f(\alpha) = 0$,
$\alpha \le \lambda^{(0)}$, and $\lambda^{(0)}$ less than every eigenvalue of $B$. Then the
Newton iterates
$$\lambda^{(k+1)} = \lambda^{(k)} - \frac{f(\lambda^{(k)})}{f'(\lambda^{(k)})}$$
satisfy $\alpha \le \lambda^{(k+1)} \le \lambda^{(k)}$ for every $k$, and
$\lambda^{(k)} \to \alpha$.

Under the condition (4.7.8), $\lambda_{\min}(T) < \lambda_{\min}(B)$ for $T = \begin{bmatrix} 1
& r^T \\ r & B \end{bmatrix}$, and then $\alpha$ is $\lambda_{\min}(T)$
(`Matrix.borderedSecularFunction_eq_zero_of_mulVec_eq`). Below the spectrum of $B$, $f' \le -1$
and $f'' \le 0$ (`Matrix.neg_one_sub_dotProduct_le_and_neg_two_mul_dotProduct_nonpos`), so $f$
is decreasing and concave there, and `Newton.tendsto_iterate_scalarStep_of_antitoneOn_deriv`
applies. The Newton step is `Newton.scalarStep` with $f'$ = `deriv f`. -/
theorem tendsto_newton_borderedSecularFunction {r : Fin m → ℝ} {B : Matrix (Fin m) (Fin m) ℝ}
    (hB : B.IsHermitian) {α x₀ : ℝ} (hα : borderedSecularFunction r B α = 0) (hαx : α ≤ x₀)
    (hx₀ : ∀ i, x₀ < hB.eigenvalues i) :
    (∀ k, α ≤ (Newton.scalarStep (borderedSecularFunction r B)
          (deriv (borderedSecularFunction r B)))^[k + 1] x₀ ∧
        (Newton.scalarStep (borderedSecularFunction r B)
          (deriv (borderedSecularFunction r B)))^[k + 1] x₀ ≤
        (Newton.scalarStep (borderedSecularFunction r B)
          (deriv (borderedSecularFunction r B)))^[k] x₀) ∧
      Tendsto (fun k => (Newton.scalarStep (borderedSecularFunction r B)
        (deriv (borderedSecularFunction r B)))^[k] x₀) atTop (𝓝 α) := by
  have hlt : ∀ x ∈ Icc α x₀, ∀ i, x < hB.eigenvalues i := fun x hx i =>
    hx.2.trans_lt (hx₀ i)
  have hd : ∀ x ∈ Icc α x₀, HasDerivAt (borderedSecularFunction r B)
      (deriv (borderedSecularFunction r B) x) x ∧
        deriv (borderedSecularFunction r B) x ≤ -1 ∧
        HasDerivAt (deriv (borderedSecularFunction r B))
          (-2 * (r ⬝ᵥ ((B - x • 1)⁻¹ ^ 3 *ᵥ r))) x ∧
        -2 * (r ⬝ᵥ ((B - x • 1)⁻¹ ^ 3 *ᵥ r)) ≤ 0 := fun x hx => by
    obtain ⟨h1, h2⟩ := hasDerivAt_borderedSecularFunction (r := r) hB fun i =>
      (hlt x hx i).ne'
    obtain ⟨n1, n2⟩ := neg_one_sub_dotProduct_le_and_neg_two_mul_dotProduct_nonpos (r := r) hB
      (hlt x hx)
    exact ⟨h1.differentiableAt.hasDerivAt, h1.deriv ▸ n1, h2, n2⟩
  have hanti : AntitoneOn (deriv (borderedSecularFunction r B)) (Icc α x₀) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc α x₀)
      (fun x hx => (hd x hx).2.2.1.continuousAt.continuousWithinAt)
      (fun x hx => (hd x (interior_subset hx)).2.2.1.differentiableAt.differentiableWithinAt)
      fun x hx => ?_
    rw [(hd x (interior_subset hx)).2.2.1.deriv]
    exact (hd x (interior_subset hx)).2.2.2
  exact Newton.tendsto_iterate_scalarStep_of_antitoneOn_deriv hαx (fun x hx => (hd x hx).1)
    (fun x hx => (hd x hx).2.1.trans_lt (by norm_num)) hanti hα

end Bordered

end Matrix
