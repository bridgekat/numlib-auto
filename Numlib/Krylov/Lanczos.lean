/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Krylov.Arnoldi

/-!
# The symmetric Lanczos process

Let $A$ be a linear operator on an inner product space $E$ over $\mathbb{K} = \mathbb{R}$ or
$\mathbb{C}$, let $b \in E$, and let $v_0, v_1, \dots$ be the Arnoldi vectors of $(A, b)$ with
coefficients $h_{ij} = \langle v_i, A v_j \rangle$. When $A$ is symmetric, the coefficient array is
Hermitian and upper Hessenberg, hence tridiagonal with a real diagonal ([saad2003iterative], Theorem
6.19; [saad2011numerical], Theorem 6.2). The Arnoldi relation then becomes the three-term recurrence
of the Lanczos process
$$A v_{j+1} = \beta_j v_j + \alpha_{j+1} v_{j+1} + \beta_{j+1} v_{j+2}$$
([saad2003iterative], Algorithm 6.15; [choi2006iterative], §2.1; [meurant2006lanczos], §2.1;
[fong2012cg], §1). Here $\alpha_j = \langle v_j, A v_j \rangle$ and
$\beta_j = h_{j+1,j} = \|w_j\| \ge 0$, where $w_j$ is the unnormalized next Arnoldi vector. This
file defines these coefficients, the $m \times m$ Lanczos matrix $T_m$ and the $(m + 1) \times m$
extended Lanczos matrix $\bar{T}_m$, and proves that $T_m$ and $\bar{T}_m$ are the Arnoldi
Hessenberg matrices $H_m$ and $\bar{H}_m$.

## Main definitions

* `Lanczos.alpha`: the diagonal coefficient $\alpha_j = \operatorname{Re} \langle v_j, A v_j
  \rangle$.
* `Lanczos.beta`: the off-diagonal coefficient $\beta_j = \|w_j\|$.
* `Lanczos.tridiag`: the real symmetric tridiagonal $m \times m$ matrix $T_m$.
* `Lanczos.tridiagExt`: the $(m + 1) \times m$ matrix $\bar{T}_m$.

## Main results

* `Arnoldi.coeff_conj_of_isSymmetric`: for symmetric $A$, $h_{ij} = \overline{h_{ji}}$.
* `Arnoldi.coeff_eq_zero_of_isSymmetric`: for symmetric $A$, $h_{ij} = 0$ when $j > i + 1$.
* `Lanczos.apply_vec_zero`, `Lanczos.apply_vec`: the three-term recurrence.
* `Lanczos.beta_eq_zero_iff`: $\beta_j = 0$ if and only if the grade of $b$ is at most $j + 1$.
* `Lanczos.alpha_mem_Icc`: the coefficients $\alpha_j$ lie between the bounds of the quadratic form
  of $A$.
* `Lanczos.hessenbergSq_eq_map_tridiag`, `Lanczos.hessenberg_eq_map_tridiagExt`: $H_m = T_m$ and
  $\bar{H}_m = \bar{T}_m$ for symmetric $A$.
* `Lanczos.apply_sum`: $A V_{m+1} = V_{m+1} T_{m+1} + \beta_m v_{m+1} e_{m+1}^T$, in coordinates.
* `Lanczos.apply_sum_grade`: at the grade $\ell$, $A V_\ell = V_\ell T_\ell$.

## Implementation notes

* Indices start at $0$. The vector $v_j$ is `Arnoldi.vec A b j`, $h_{ij}$ is
  `Arnoldi.coeff A b i j`, and $w_j$ is `Arnoldi.w A b j`.
* The inner product $\langle x, y \rangle$ is conjugate linear in $x$, as in Mathlib.
* The coefficients and the matrices $T_m$, $\bar{T}_m$ are real. They are defined for every operator
  $A$: $\alpha_j$ is the real part of $h_{jj}$, and $\beta_j$ is a norm. The identity
  $\beta_j = h_{j+1,j}$ holds for every operator, while $\alpha_j = h_{jj}$ needs symmetry. A
  statement over $\mathbb{K}$ uses `Matrix.map` with `algebraMap ℝ 𝕜`.
-/

open Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Arnoldi

variable {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (b : E)
include hA

/-- Let $A$ be a symmetric operator on an inner product space $E$ and let $b \in E$. The Arnoldi
coefficients of $(A, b)$ satisfy $h_{ij} = \overline{h_{ji}}$ for all $i, j$.

Together with the Hessenberg property `Arnoldi.coeff_eq_zero_of_lt`, this makes the coefficient
array tridiagonal. -/
theorem coeff_conj_of_isSymmetric (i j : ℕ) : coeff A b i j = starRingEnd 𝕜 (coeff A b j i) := by
  rw [coeff, coeff, inner_conj_symm, hA]

/-- Let $A$ be a symmetric operator on an inner product space $E$ and let $b \in E$. The Arnoldi
coefficients of $(A, b)$ satisfy $h_{ij} = 0$ when $i + 1 < j$. With the Hessenberg property
this means that the coefficient array is tridiagonal. -/
theorem coeff_eq_zero_of_isSymmetric {i j : ℕ} (h : i + 1 < j) : coeff A b i j = 0 := by
  rw [coeff_conj_of_isSymmetric hA b i j, coeff_eq_zero_of_lt A b h, map_zero]

/-- Let $A$ be a symmetric operator on an inner product space $E$ and let $b \in E$. The diagonal
Arnoldi coefficients $h_{jj}$ of $(A, b)$ are real.

This is the reason that the Lanczos matrix can be defined over $\mathbb{R}$. -/
theorem coeff_diag_re_of_isSymmetric (j : ℕ) :
    coeff A b j j = (RCLike.re (coeff A b j j) : 𝕜) :=
  (RCLike.conj_eq_iff_re.1 (coeff_conj_of_isSymmetric hA b j j).symm).symm

end Arnoldi

namespace Lanczos

variable (A : E →ₗ[𝕜] E) (b : E)

/-- The **diagonal Lanczos coefficient** $\alpha_j = \operatorname{Re} h_{jj} = \operatorname{Re}
\langle v_j, A v_j \rangle$. For symmetric $A$ the number $h_{jj}$ is real, so
$\alpha_j = h_{jj}$ (`Lanczos.coe_alpha`). -/
noncomputable def alpha (j : ℕ) : ℝ := RCLike.re (Arnoldi.coeff A b j j)

/-- The **off-diagonal Lanczos coefficient** $\beta_j = \|w_j\|$, the norm of the unnormalized next
Arnoldi vector $w_j$. It equals $h_{j+1,j}$ (`Lanczos.coe_beta`). -/
noncomputable def beta (j : ℕ) : ℝ := ‖Arnoldi.w A b j‖

/-- The off-diagonal Lanczos coefficients are nonnegative: $\beta_j \ge 0$. -/
theorem beta_nonneg (j : ℕ) : 0 ≤ beta A b j := norm_nonneg _

/-- For every operator $A$ and every $j$, the off-diagonal Lanczos coefficient is the subdiagonal
Arnoldi coefficient: $\beta_j = h_{j+1,j}$.

Symmetry of $A$ is not needed, because $h_{j+1,j} = \|w_j\|$ is real and nonnegative for every
operator. -/
theorem coe_beta (j : ℕ) : (beta A b j : 𝕜) = Arnoldi.coeff A b (j + 1) j :=
  (Arnoldi.coeff_succ_self A b j).symm

/-- The **Lanczos matrix** $T_m$: the real $m \times m$ matrix with $(T_m)_{jj} = \alpha_j$,
$(T_m)_{j,j+1} = (T_m)_{j+1,j} = \beta_j$, and all other entries $0$ ([saad2003iterative],
(6.84)). -/
noncomputable def tridiag (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) = j then alpha A b i
    else if (i : ℕ) + 1 = j then beta A b i
    else if (j : ℕ) + 1 = i then beta A b j
    else 0

/-- The **extended Lanczos matrix** $\bar{T}_m$: the real $(m + 1) \times m$ matrix with
$(\bar{T}_m)_{jj} = \alpha_j$, $(\bar{T}_m)_{j,j+1} = (\bar{T}_m)_{j+1,j} = \beta_j$, and all
other entries $0$. Its first $m$ rows form $T_m$. For $m \ge 1$ its last row is $0$ except for
the entry $\beta_{m-1}$ in the last column. -/
noncomputable def tridiagExt (m : ℕ) : Matrix (Fin (m + 1)) (Fin m) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) = j then alpha A b i
    else if (i : ℕ) + 1 = j then beta A b i
    else if (j : ℕ) + 1 = i then beta A b j
    else 0

/-- The entries of $T_m$: the entry $(i, j)$ is $\alpha_i$ if $i = j$, $\beta_i$ if $j = i + 1$,
$\beta_j$ if $i = j + 1$, and $0$ otherwise.

The matrices $T_m$ and $\bar{T}_m$ have the same entry function, read on different index ranges. -/
theorem tridiag_apply {m : ℕ} (i j : Fin m) :
    tridiag A b m i j =
      if (i : ℕ) = j then alpha A b i
      else if (i : ℕ) + 1 = j then beta A b i
      else if (j : ℕ) + 1 = i then beta A b j
      else 0 := rfl

/-- The entries of $\bar{T}_m$: the entry $(i, j)$ is $\alpha_i$ if $i = j$, $\beta_i$ if
$j = i + 1$, $\beta_j$ if $i = j + 1$, and $0$ otherwise. This is the same entry function as in
`Lanczos.tridiag_apply`. -/
theorem tridiagExt_apply {m : ℕ} (i : Fin (m + 1)) (j : Fin m) :
    tridiagExt A b m i j =
      if (i : ℕ) = j then alpha A b i
      else if (i : ℕ) + 1 = j then beta A b i
      else if (j : ℕ) + 1 = i then beta A b j
      else 0 := rfl

/-- For every operator $A$, the Lanczos matrix $T_m$ is tridiagonal: its entries vanish outside the
diagonal and the two neighbouring diagonals. -/
theorem tridiag_isTridiagonal (m : ℕ) : (tridiag A b m).IsTridiagonal := by
  intro i j hij
  have h : (j : ℕ) + 1 < (i : ℕ) ∨ (i : ℕ) + 1 < (j : ℕ) := by
    rcases hij with ⟨k, hjk, hki⟩ | ⟨k, hik, hkj⟩
    · rw [Fin.lt_def] at hjk hki
      omega
    · rw [Fin.lt_def] at hik hkj
      omega
  simp only [tridiag_apply]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

/-- For every operator $A$, the Lanczos matrix $T_m$ is symmetric: $T_m^T = T_m$, because the same
$\beta_j$ is at the positions $(j, j + 1)$ and $(j + 1, j)$. -/
theorem tridiag_isSymm (m : ℕ) : (tridiag A b m).IsSymm := by
  refine Matrix.IsSymm.ext_iff.2 fun i j => ?_
  simp only [tridiag_apply]
  by_cases h₁ : (i : ℕ) = j
  · rw [ite_eq_left h₁.symm, ite_eq_left h₁, h₁]
  · rw [ite_eq_right h₁, ite_eq_right (Ne.symm h₁)]
    by_cases h₂ : (i : ℕ) + 1 = j
    · rw [ite_eq_right (by omega), ite_eq_left h₂, ite_eq_left h₂]
    · by_cases h₃ : (j : ℕ) + 1 = i
      · rw [ite_eq_left h₃, ite_eq_right h₂, ite_eq_left h₃]
      · rw [ite_eq_right h₃, ite_eq_right h₂, ite_eq_right h₂, ite_eq_right h₃]

section CoeffEq

variable {A b} {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] {A' : E' →ₗ[𝕜] E'}
  {b' : E'}

/-- Let $(A, b)$ and $(A', b')$ be two operators with starting vectors, possibly on different inner
product spaces. If their Arnoldi coefficients are equal, then their diagonal Lanczos
coefficients are equal: $\alpha_j(A', b') = \alpha_j(A, b)$. -/
theorem alpha_eq_of_coeff_eq (h : Arnoldi.coeff A' b' = Arnoldi.coeff A b) (j : ℕ) :
    alpha A' b' j = alpha A b j := by
  rw [alpha, alpha, h]

/-- Let $(A, b)$ and $(A', b')$ be two operators with starting vectors, possibly on different inner
product spaces. If their Arnoldi coefficients are equal, then their off-diagonal Lanczos
coefficients are equal: $\beta_j(A', b') = \beta_j(A, b)$. -/
theorem beta_eq_of_coeff_eq (h : Arnoldi.coeff A' b' = Arnoldi.coeff A b) (j : ℕ) :
    beta A' b' j = beta A b j := by
  have h1 := coe_beta (𝕜 := 𝕜) A' b' j
  rw [h, ← coe_beta] at h1
  exact_mod_cast h1

/-- Let $(A, b)$ and $(A', b')$ be two operators with starting vectors, possibly on different inner
product spaces. If their Arnoldi coefficients are equal, then their Lanczos matrices $T_m$ are
equal for every $m$.

Thus the Lanczos matrix depends only on the Arnoldi coefficients. This is how a Lanczos process
is carried between isometric models of one space. -/
theorem tridiag_eq_of_coeff_eq (h : Arnoldi.coeff A' b' = Arnoldi.coeff A b) (m : ℕ) :
    tridiag A' b' m = tridiag A b m := by
  ext i j
  simp only [tridiag_apply, alpha_eq_of_coeff_eq h, beta_eq_of_coeff_eq h]

end CoeffEq

/-- For every $y \in \mathbb{K}^n$ and $i < n$, the entry $i$ of $\bar{T}_n y$ equals the entry $i$
of $T_n y$: the rows of $\bar{T}_n$ above the last one are the rows of $T_n$. -/
theorem mulVec_tridiagExt_castSucc {n : ℕ} (y : Fin n → 𝕜) (i : Fin n) :
    ((tridiagExt A b n).map (algebraMap ℝ 𝕜)).mulVec y i.castSucc =
      ((tridiag A b n).map (algebraMap ℝ 𝕜)).mulVec y i := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, tridiagExt, tridiag, Matrix.of_apply,
    Fin.val_castSucc]

/-- The last row of $\bar{T}_{m+1}$ is $0$ except for the entry $\beta_m$ in the last column:
$(\bar{T}_{m+1} y)_{m+1} = \beta_m y_m$. -/
private theorem mulVec_tridiagExt_last (m : ℕ) (y : Fin (m + 1) → 𝕜) :
    ((tridiagExt A b (m + 1)).map (algebraMap ℝ 𝕜)).mulVec y (Fin.last (m + 1)) =
      (beta A b m : 𝕜) * y (Fin.last m) := by
  have hrow : ∀ j : Fin (m + 1),
      ((tridiagExt A b (m + 1)).map (algebraMap ℝ 𝕜)) (Fin.last (m + 1)) j =
        if (j : ℕ) = m then (beta A b m : 𝕜) else 0 := by
    intro j
    have hj : (j : ℕ) ≤ m := Nat.lt_succ_iff.1 j.2
    simp only [Matrix.map_apply, tridiagExt, Matrix.of_apply, Fin.val_last,
      RCLike.algebraMap_eq_ofReal]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    by_cases h : (j : ℕ) = m
    · rw [ite_eq_left (by omega), ite_eq_left h, h]
    · rw [ite_eq_right (by omega), ite_eq_right h, RCLike.ofReal_zero]
  simp only [Matrix.mulVec, dotProduct, hrow]
  rw [Finset.sum_eq_single (Fin.last m)]
  · rw [ite_eq_left (Fin.val_last m)]
  · intro j _ hj
    rw [ite_eq_right (fun h => hj (Fin.ext (by simpa using h))), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

variable {A} (hA : A.IsSymmetric)
include hA

/-- Let $A$ be a symmetric operator on an inner product space $E$ and let $b \in E$. The diagonal
Lanczos coefficient is the diagonal Arnoldi coefficient: $\alpha_j = h_{jj}$.

The real part in `Lanczos.alpha` loses nothing, because $h_{jj}$ is real for symmetric $A$. -/
theorem coe_alpha (j : ℕ) : (alpha A b j : 𝕜) = Arnoldi.coeff A b j j :=
  (Arnoldi.coeff_diag_re_of_isSymmetric hA b j).symm

/-- For symmetric $A$, the superdiagonal Arnoldi coefficient is $h_{j,j+1} = \beta_j$. -/
private theorem coeff_succ_eq_beta (j : ℕ) : Arnoldi.coeff A b j (j + 1) = (beta A b j : 𝕜) := by
  rw [Arnoldi.coeff_conj_of_isSymmetric hA b j (j + 1), ← coe_beta A b j, RCLike.conj_ofReal]

/-- For symmetric $A$, the Arnoldi expansion of $A v_{j+1}$ has no terms $h_{i,j+1} v_i$ with
$i < j$. -/
private theorem sum_coeff_eq_zero (j : ℕ) :
    ∑ i ∈ Finset.range j, Arnoldi.coeff A b i (j + 1) • Arnoldi.vec A b i = 0 :=
  Finset.sum_eq_zero fun i hi => by
    rw [Arnoldi.coeff_eq_zero_of_isSymmetric hA b
      (by have := Finset.mem_range.1 hi; omega), zero_smul]

/-- Let $A$ be a symmetric operator on an inner product space $E$ and let $b \in E$. The first step
of the Lanczos recurrence is
$$A v_0 = \alpha_0 v_0 + \beta_0 v_1.$$
-/
theorem apply_vec_zero :
    A (Arnoldi.vec A b 0) = (alpha A b 0 : 𝕜) • Arnoldi.vec A b 0 +
      (beta A b 0 : 𝕜) • Arnoldi.vec A b 1 := by
  rw [coe_alpha b hA 0, coe_beta A b 0,
    Arnoldi.apply_vec_of_le A b (j := 0) (n := 1 + 1) (by omega),
    Finset.sum_range_succ, Finset.sum_range_one]

/-- Let $A$ be a symmetric operator on an inner product space $E$ and let $b \in E$. The Lanczos
vectors satisfy the **three-term recurrence**
$$A v_{j+1} = \beta_j v_j + \alpha_{j+1} v_{j+1} + \beta_{j+1} v_{j+2}$$
for every $j$. This is Algorithm 6.15 of [saad2003iterative], and the display that opens §6.6.2
there.

The identity also holds after a breakdown, where the Arnoldi vectors are $0$. -/
theorem apply_vec (j : ℕ) :
    A (Arnoldi.vec A b (j + 1)) =
      (beta A b j : 𝕜) • Arnoldi.vec A b j + (alpha A b (j + 1) : 𝕜) • Arnoldi.vec A b (j + 1) +
        (beta A b (j + 1) : 𝕜) • Arnoldi.vec A b (j + 2) := by
  rw [show j + 2 = j + 1 + 1 from rfl, coe_alpha b hA (j + 1), coe_beta A b (j + 1),
    ← coeff_succ_eq_beta b hA j,
    Arnoldi.apply_vec_of_le A b (j := j + 1) (n := j + 1 + 1 + 1) (by omega),
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    sum_coeff_eq_zero b hA j, zero_add]

/-- Let $A$ be a symmetric operator on an inner product space $E$ and let $b \in E$. The
unnormalized next Arnoldi vector satisfies
$$w_{j+1} = A v_{j+1} - \alpha_{j+1} v_{j+1} - \beta_j v_j.$$
This is the form in which the Lanczos algorithm computes the recurrence. -/
theorem w_succ_eq (j : ℕ) :
    Arnoldi.w A b (j + 1) = A (Arnoldi.vec A b (j + 1)) -
      (alpha A b (j + 1) : 𝕜) • Arnoldi.vec A b (j + 1) - (beta A b j : 𝕜) • Arnoldi.vec A b j := by
  rw [Arnoldi.w, coe_alpha b hA (j + 1), ← coeff_succ_eq_beta b hA j, Finset.sum_range_succ,
    Finset.sum_range_succ, sum_coeff_eq_zero b hA j, zero_add]
  abel

omit hA in
/-- Let $A$ be any operator on an inner product space $E$ and let $b \in E$ have a
finite-dimensional Krylov space. Then $\beta_j = 0$ if and only if the grade of $b$ with respect
to $A$ is at most $j + 1$.

Thus the Lanczos process breaks down exactly at the grade, and the recurrence runs with nonzero
$\beta_j$ for as long as there is a new direction to find. -/
theorem beta_eq_zero_iff [FiniteDimensional 𝕜 (fullSubspace A b)] (j : ℕ) :
    beta A b j = 0 ↔ grade A b ≤ j + 1 := by
  rw [← Arnoldi.coeff_succ_self_eq_zero_iff A b j, ← coe_beta A b j, RCLike.ofReal_eq_zero]

/-- Let $A$ be a symmetric operator on an inner product space $E$ with $\lambda_{\min} \|x\|^2 \le
\operatorname{Re} \langle Ax, x \rangle \le \lambda_{\max} \|x\|^2$ for all $x \in E$, and let
$b \in E$ have a finite-dimensional Krylov space. If $j$ is less than the grade of $b$, then
$$\lambda_{\min} \le \alpha_j \le \lambda_{\max}.$$

The bounds are `LinearMap.IsSymmetricBoundedBy`. They are bounds of the quadratic form and need
not be eigenvalues of $A$. The number $\alpha_j$ is the Rayleigh quotient of the unit vector
$v_j$. -/
theorem alpha_mem_Icc {lmin lmax : ℝ} (hA' : A.IsSymmetricBoundedBy lmin lmax)
    [FiniteDimensional 𝕜 (fullSubspace A b)] {j : ℕ} (hj : j < grade A b) :
    alpha A b j ∈ Set.Icc lmin lmax := by
  have hn : ‖Arnoldi.vec A b j‖ = 1 := Arnoldi.norm_vec_eq_one_of_lt_grade A b hj
  have hre : alpha A b j = RCLike.re (inner 𝕜 (A (Arnoldi.vec A b j)) (Arnoldi.vec A b j)) := by
    rw [alpha, Arnoldi.coeff, hA]
  rw [Set.mem_Icc, hre]
  refine ⟨?_, ?_⟩
  · have h := hA'.le_re_inner (Arnoldi.vec A b j)
    rwa [hn, one_pow, mul_one] at h
  · have h := hA'.re_inner_le (Arnoldi.vec A b j)
    rwa [hn, one_pow, mul_one] at h

/-- For symmetric $A$, the Arnoldi coefficient $h_{ij}$ is the entry $(i, j)$ of the Lanczos
coefficient array: $\alpha_i$ if $i = j$, $\beta_i$ if $j = i + 1$, $\beta_j$ if $i = j + 1$,
and $0$ otherwise. -/
private theorem coeff_eq_ite (i j : ℕ) :
    Arnoldi.coeff A b i j =
      algebraMap ℝ 𝕜 (if i = j then alpha A b i else if i + 1 = j then beta A b i
        else if j + 1 = i then beta A b j else 0) := by
  simp only [RCLike.algebraMap_eq_ofReal]
  by_cases h₁ : i = j
  · subst h₁
    rw [ite_eq_left rfl]
    exact (coe_alpha b hA i).symm
  · rw [ite_eq_right h₁]
    by_cases h₂ : i + 1 = j
    · subst h₂
      rw [ite_eq_left rfl]
      exact coeff_succ_eq_beta b hA i
    · rw [ite_eq_right h₂]
      by_cases h₃ : j + 1 = i
      · subst h₃
        rw [ite_eq_left rfl]
        exact (coe_beta A b j).symm
      · rw [ite_eq_right h₃, RCLike.ofReal_zero]
        rcases lt_or_gt_of_ne h₁ with h | h
        · exact Arnoldi.coeff_eq_zero_of_isSymmetric hA b (by omega)
        · exact Arnoldi.coeff_eq_zero_of_lt A b (by omega)

/-- Let $A$ be a symmetric operator on an inner product space $E$ and let $b \in E$. For every $m$
the square Arnoldi Hessenberg matrix is the Lanczos matrix: $H_m = T_m$. This is Theorem 6.19 of
[saad2003iterative].

The real matrix $T_m$ is embedded entrywise in the matrices over $\mathbb{K}$. -/
theorem hessenbergSq_eq_map_tridiag (m : ℕ) :
    Arnoldi.hessenbergSq A b m = (tridiag A b m).map (algebraMap ℝ 𝕜) := by
  ext i j
  exact coeff_eq_ite b hA i j

/-- Let $A$ be a symmetric operator on an inner product space $E$ and let $b \in E$. For every $m$
the rectangular Arnoldi Hessenberg matrix is the extended Lanczos matrix:
$\bar{H}_m = \bar{T}_m$. This is the rectangular form of Theorem 6.19 of [saad2003iterative]. -/
theorem hessenberg_eq_map_tridiagExt (m : ℕ) :
    Arnoldi.hessenberg A b m = (tridiagExt A b m).map (algebraMap ℝ 𝕜) := by
  ext i j
  exact coeff_eq_ite b hA i j

/-- Let $A$ be a symmetric operator on an inner product space $E$, let $b \in E$, $m \in \mathbb{N}$
and $y \in \mathbb{K}^{m+1}$. Then
$$A \sum_{j=0}^{m} y_j v_j = \sum_{i=0}^{m} (T_{m+1} y)_i \, v_i + \beta_m y_m v_{m+1}.$$
This is the coordinate form of $A V_{m+1} = V_{m+1} T_{m+1} + \beta_m v_{m+1} e_{m+1}^T$, the
symmetric case of (6.6) of [saad2003iterative], where $H_{m+1} = T_{m+1}$ by Theorem 6.19.

The statement is written for $m + 1$ steps, so that the number of steps is positive and the
vector $v_{m+1}$ outside the span of $V_{m+1}$ carries the rank-one correction. -/
theorem apply_sum (m : ℕ) (y : Fin (m + 1) → 𝕜) :
    A (∑ j, y j • Arnoldi.vec A b j) =
      ∑ i : Fin (m + 1), ((tridiag A b (m + 1)).map (algebraMap ℝ 𝕜)).mulVec y i •
          Arnoldi.vec A b i +
        ((beta A b m : 𝕜) * y (Fin.last m)) • Arnoldi.vec A b (m + 1) := by
  have hsum : ∑ i : Fin (m + 1),
      ((tridiagExt A b (m + 1)).map (algebraMap ℝ 𝕜)).mulVec y i.castSucc •
        Arnoldi.vec A b (i.castSucc : ℕ) =
      ∑ i : Fin (m + 1), ((tridiag A b (m + 1)).map (algebraMap ℝ 𝕜)).mulVec y i •
        Arnoldi.vec A b i :=
    Finset.sum_congr rfl fun i _ => by
      rw [mulVec_tridiagExt_castSucc A b y i, Fin.val_castSucc]
  rw [Arnoldi.apply_sum A b (m + 1) y, hessenberg_eq_map_tridiagExt b hA (m + 1),
    Fin.sum_univ_castSucc, mulVec_tridiagExt_last A b m y, Fin.val_last, hsum]

/-- Let $A$ be a symmetric operator on an inner product space $E$, and let $b \in E$ have a
finite-dimensional Krylov space of dimension $\ell$, the grade of $b$. Then for every
$y \in \mathbb{K}^\ell$
$$A \sum_{j < \ell} y_j v_j = \sum_{i < \ell} (T_\ell y)_i \, v_i,$$
that is, $A V_\ell = V_\ell T_\ell$, and the Krylov space $\mathcal{K}_\ell$ is invariant under
$A$. This is the termination statement (2.4) of [choi2006iterative]. -/
theorem apply_sum_grade [FiniteDimensional 𝕜 (fullSubspace A b)] (y : Fin (grade A b) → 𝕜) :
    A (∑ j, y j • Arnoldi.vec A b j) =
      ∑ i : Fin (grade A b),
        ((tridiag A b (grade A b)).map (algebraMap ℝ 𝕜)).mulVec y i • Arnoldi.vec A b i := by
  have hlast : Arnoldi.vec A b ((Fin.last (grade A b) : Fin (grade A b + 1)) : ℕ) = 0 := by
    rw [Fin.val_last]
    exact (Arnoldi.vec_eq_zero_iff A b _).2 le_rfl
  have hsum : ∑ i : Fin (grade A b),
      ((tridiagExt A b (grade A b)).map (algebraMap ℝ 𝕜)).mulVec y i.castSucc •
        Arnoldi.vec A b (i.castSucc : ℕ) =
      ∑ i : Fin (grade A b), ((tridiag A b (grade A b)).map (algebraMap ℝ 𝕜)).mulVec y i •
        Arnoldi.vec A b i :=
    Finset.sum_congr rfl fun i _ => by
      rw [mulVec_tridiagExt_castSucc A b y i, Fin.val_castSucc]
  rw [Arnoldi.apply_sum A b (grade A b) y, hessenberg_eq_map_tridiagExt b hA (grade A b),
    Fin.sum_univ_castSucc, hlast, smul_zero, add_zero, hsum]

end Lanczos
