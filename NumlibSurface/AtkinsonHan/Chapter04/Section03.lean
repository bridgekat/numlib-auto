/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Fourier.DFT

/-!
# Atkinson and Han, Section 4.3: The discrete Fourier transform

This module formalizes Section 4.3 of [han2009theoretical], the discrete Fourier transform. Let
$n \ge 1$ and $\omega_n = e^{2\pi i/n}$. The book's matrix $F_n$ of (4.3.2) has the entries
$(F_n)_{jk} = \omega_n^{jk}$ for $0 \le j, k \le n - 1$, and the discrete Fourier transform of
$y \in \mathbb{C}^n$ is $\hat y = \overline{F_n}\, y$, that is,
$$\hat y_k = \sum_{j=0}^{n-1} \omega_n^{-kj} y_j, \qquad 0 \le k \le n - 1.$$
The module proves the inversion formula $y_j = n^{-1} \sum_k \omega_n^{jk} \hat y_k$, the summation
formula (4.3.5), the radix-2 splitting on which the fast Fourier transform is built, the discrete
Parseval equality, and the inversion of the two-dimensional transform.

The matrix $F_n$ is the backbone matrix `Matrix.dft` of `Numlib.Analysis.Fourier.DFT`, which is
Mathlib's `ZMod.dft` in matrix form. All results of the section specialize that module.

## Main definitions

* Definition 4.3.1, `AtkinsonHan.Chapter04.definition_4_3_1`: the entries of $F_n$, and the formula
  $\hat y_k = \sum_j \omega_n^{-kj} y_j$ for the transform.

## Main results

* Theorem 4.3.2, `AtkinsonHan.Chapter04.theorem_4_3_2`: $\overline{F_n}^{-1} = n^{-1} F_n$, and the
  inversion formula.
* Equations (4.3.6)–(4.3.9), `AtkinsonHan.Chapter04.equation_4_3_9`: the transform of length $2n$ in
  terms of the two transforms of length $n$ of the even-indexed and the odd-indexed entries.
* Equations (4.3.10)–(4.3.11), `AtkinsonHan.Chapter04.equation_4_3_11`: the two-dimensional
  transform is two one-dimensional transforms in succession, and its inversion formula.
* Exercise 4.3.1, `AtkinsonHan.Chapter04.exercise_4_3_1`: the summation formula (4.3.5), $\sum_k
  \omega_n^{kl} \omega_n^{-kj} = n \delta_{jl}$.
* Exercise 4.3.2, `AtkinsonHan.Chapter04.exercise_4_3_2`: the discrete Parseval equality
  $\sum_k |\hat y_k|^2 = n \sum_j |y_j|^2$.

## Implementation notes

* The book's matrix $\overline{F_n}$ is the conjugate transpose $F_n^H$ (`(Matrix.dft n)ᴴ`). The two
  agree because $F_n$ is symmetric. So $\hat y$ is `(Matrix.dft n)ᴴ *ᵥ y`.
* Indices are elements of `Fin n`, that is, $0, \dots, n - 1$, and $\omega_n^{-kj}$ is written as
  the inverse $(\omega_n^{kj})^{-1}$.

## Deviations from the source

* **Definition 4.3.1 and Exercise 4.3.2** (generalization). Lean also allows order zero in
  these formulas, with vacuous entrywise assertions and empty sums.

## Not formalized

* The fast Fourier transform as an algorithm, and its operation count $O(n \log n)$. This part is an
  algorithm with a cost recursion, not a theorem, and operation counts of algorithms are out of
  scope. The derivation (4.3.8)–(4.3.9) on which the algorithm rests is
  `AtkinsonHan.Chapter04.equation_4_3_9`.
-/

open Complex Matrix

open scoped Real

namespace AtkinsonHan.Chapter04

/-- **Definition 4.3.1** and **equations (4.3.1)–(4.3.2)** of [han2009theoretical]. Let
$n \in \mathbb{N}$, $\omega_n = e^{2\pi i/n}$, and $y \in \mathbb{C}^n$. The matrix $F_n$ has
the entries
$$(F_n)_{jk} = \omega_n^{jk}, \qquad 0 \le j, k \le n - 1,$$
and the discrete Fourier transform $\hat y = \overline{F_n}\, y$ of $y$ has the entries
$$\hat y_k = \sum_{j=0}^{n-1} \omega_n^{-kj} y_j, \qquad 0 \le k \le n - 1.$$

The matrix $F_n$ is `Matrix.dft n`. The book's $\overline{F_n}$ is its conjugate transpose
`(Matrix.dft n)ᴴ`; the two agree because $F_n$ is symmetric. The power $\omega_n^{-kj}$ is
written as $(\omega_n^{kj})^{-1}$.

**Generalization.** The book assumes positive order. The entrywise formulas are vacuous at
order zero, which Lean permits here. -/
theorem definition_4_3_1 {n : ℕ} (y : Fin n → ℂ) :
    (∀ j k : Fin n, dft n j k = Complex.exp (2 * π * I / n) ^ ((j : ℕ) * (k : ℕ))) ∧
      ∀ k : Fin n, ((dft n)ᴴ *ᵥ y) k
        = ∑ j : Fin n, (Complex.exp (2 * π * I / n) ^ ((k : ℕ) * (j : ℕ)))⁻¹ * y j := by
  refine ⟨fun j k => dft_apply j k, fun k => ?_⟩
  rw [conjTranspose_dft_mulVec_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [inv_pow, Nat.mul_comm (k : ℕ) (j : ℕ)]

/-- **Exercise 4.3.1** of [han2009theoretical], the summation formula (4.3.5). Let
$n \in \mathbb{N}$, $\omega_n = e^{2\pi i/n}$ and $0 \le j, l \le n - 1$. Then
$$\sum_{k=0}^{n-1} \omega_n^{kl} \, \omega_n^{-kj} = \begin{cases} n, & j = l, \\ 0, & j \ne l.
  \end{cases}$$

This is the orthogonality of the columns of $F_n$. The inversion formula of Theorem 4.3.2
follows from it. -/
theorem exercise_4_3_1 (n : ℕ) (j l : Fin n) :
    ∑ k : Fin n, Complex.exp (2 * π * I / n) ^ ((k : ℕ) * (l : ℕ))
        * (Complex.exp (2 * π * I / n) ^ ((k : ℕ) * (j : ℕ)))⁻¹
      = if j = l then (n : ℂ) else 0 := by
  have h := congrFun₂ (conjTranspose_dft_mul_dft n) j l
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h
  have hgoal : (if j = l then (n : ℂ) else 0) = (n : ℂ) * (if j = l then 1 else 0) := by
    split_ifs <;> ring
  rw [hgoal, ← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [conjTranspose_dft_apply, dft_apply, inv_pow, Nat.mul_comm (j : ℕ) (k : ℕ)]
  exact mul_comm _ _

/-- **Theorem 4.3.2** and **equations (4.3.3)–(4.3.4)** of [han2009theoretical]. Let $n \ge 1$ and
$\omega_n = e^{2\pi i/n}$. Then the matrix $\overline{F_n}$ of the discrete Fourier transform is
invertible, with
$$\overline{F_n}^{-1} = \frac{1}{n} F_n,$$
and for every $y \in \mathbb{C}^n$ the transform $\hat y = \overline{F_n}\, y$ is inverted by
$$y_j = \frac{1}{n} \sum_{k=0}^{n-1} \omega_n^{jk} \hat y_k, \qquad 0 \le j \le n - 1.$$

The matrix $\overline{F_n}$ is `(Matrix.dft n)ᴴ`, and the inverse is the Mathlib matrix inverse. -/
theorem theorem_4_3_2 {n : ℕ} [NeZero n] :
    ((dft n)ᴴ)⁻¹ = (n : ℂ)⁻¹ • dft n ∧
      ∀ (y : Fin n → ℂ) (j : Fin n), y j = (n : ℂ)⁻¹
        * ∑ k : Fin n, Complex.exp (2 * π * I / n) ^ ((j : ℕ) * (k : ℕ)) * ((dft n)ᴴ *ᵥ y) k := by
  refine ⟨inv_conjTranspose_dft n, fun y j => ?_⟩
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have h := congrFun (dft_mulVec_conjTranspose_dft_mulVec y) j
  rw [Pi.smul_apply, smul_eq_mul, Matrix.mulVec_apply_eq_sum] at h
  have hsum : ∑ k : Fin n, Complex.exp (2 * π * I / n) ^ ((j : ℕ) * (k : ℕ))
      * ((dft n)ᴴ *ᵥ y) k = ∑ k : Fin n, dft n j k * ((dft n)ᴴ *ᵥ y) k :=
    Finset.sum_congr rfl fun k _ => by rw [dft_apply]
  rw [hsum, h, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

/-- **Equations (4.3.6)–(4.3.9)** of [han2009theoretical], the radix-2 splitting on which the fast
Fourier transform is built. Let $n \in \mathbb{N}$ and $y \in \mathbb{C}^{2n}$. Let $E =
\overline{F_n}\,(y_0, y_2, \dots, y_{2n-2})$ and $O = \overline{F_n}\,(y_1, y_3, \dots,
y_{2n-1})$ be the transforms of length $n$ of the even-indexed and the odd-indexed entries of
$y$. Then for $0 \le k \le n - 1$ the transform $\hat y = \overline{F_{2n}}\, y$ satisfies
$$\hat y_k = E_k + \omega_{2n}^{-k} O_k, \qquad \hat y_{k+n} = E_k - \omega_{2n}^{-k} O_k.$$

Thus the transform of length $2n$ costs the two transforms of length $n$ and one multiplication
for each entry. The factor $\omega_{2n}^{-k}$ is written as $(\omega_{2n}^{-1})^k$. -/
theorem equation_4_3_9 {n : ℕ} (y : Fin (2 * n) → ℂ) (k : Fin n) :
    ((dft (2 * n))ᴴ *ᵥ y) ⟨(k : ℕ), by omega⟩
        = ((dft n)ᴴ *ᵥ fun m : Fin n => y ⟨2 * (m : ℕ), by omega⟩) k
          + (Complex.exp (2 * π * I / (2 * n)))⁻¹ ^ (k : ℕ)
            * ((dft n)ᴴ *ᵥ fun m : Fin n => y ⟨2 * (m : ℕ) + 1, by omega⟩) k ∧
      ((dft (2 * n))ᴴ *ᵥ y) ⟨(k : ℕ) + n, by omega⟩
        = ((dft n)ᴴ *ᵥ fun m : Fin n => y ⟨2 * (m : ℕ), by omega⟩) k
          - (Complex.exp (2 * π * I / (2 * n)))⁻¹ ^ (k : ℕ)
            * ((dft n)ᴴ *ᵥ fun m : Fin n => y ⟨2 * (m : ℕ) + 1, by omega⟩) k :=
  ⟨dft_radix_two y k, dft_radix_two_add y k⟩

/-- **Exercise 4.3.2** of [han2009theoretical], the discrete Parseval equality. For
$n \in \mathbb{N}$ and $y \in \mathbb{C}^n$, the transform $\hat y = \overline{F_n}\, y$
satisfies
$$\sum_{k=0}^{n-1} |\hat y_k|^2 = n \sum_{j=0}^{n-1} |y_j|^2.$$

So the transform is $\sqrt n$ times an isometry. This is the orthogonality of the rows of $F_n$,
$F_n \overline{F_n}^T = nI$.

**Generalization.** The equality also holds at order zero, when both sums are empty. -/
theorem exercise_4_3_2 {n : ℕ} (y : Fin n → ℂ) :
    ∑ k : Fin n, ‖((dft n)ᴴ *ᵥ y) k‖ ^ 2 = n * ∑ j : Fin n, ‖y j‖ ^ 2 := by
  have hsq : ∀ v : Fin n → ℂ, ((∑ k : Fin n, ‖v k‖ ^ 2 : ℝ) : ℂ) = star v ⬝ᵥ v := by
    intro v
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    rfl
  have key : star ((dft n)ᴴ *ᵥ y) ⬝ᵥ ((dft n)ᴴ *ᵥ y) = (n : ℂ) * (star y ⬝ᵥ y) := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, Matrix.dotProduct_mulVec,
      Matrix.vecMul_vecMul, dft_mul_conjTranspose_dft, Matrix.vecMul_smul, Matrix.vecMul_one,
      smul_dotProduct, smul_eq_mul]
  refine Complex.ofReal_inj.mp ?_
  rw [hsq, Complex.ofReal_mul, Complex.ofReal_natCast, hsq, key]

/-- **Equations (4.3.10)–(4.3.11)** of [han2009theoretical], the two-dimensional discrete Fourier
transform. Let $n_1, n_2 \ge 1$, and let $y$ and $\hat y$ be $n_1 \times n_2$ arrays of complex
numbers such that
$$\hat y_{k_1 k_2} = \sum_{j_1=0}^{n_1-1} \sum_{j_2=0}^{n_2-1} \omega_{n_1}^{-k_1 j_1}
  \omega_{n_2}^{-k_2 j_2} y_{j_1 j_2}$$
for all $k_1, k_2$. Then:

1. $\hat y$ is obtained by the one-dimensional transform $\overline{F_{n_2}}$ in the second
   index, followed by the one-dimensional transform $\overline{F_{n_1}}$ in the first index;
2. $y$ is recovered by the inversion formula
$$y_{j_1 j_2} = \frac{1}{n_1 n_2} \sum_{k_1=0}^{n_1-1} \sum_{k_2=0}^{n_2-1} \omega_{n_1}^{j_1
  k_1} \omega_{n_2}^{j_2 k_2} \hat y_{k_1 k_2}.$$

The book remarks that the transform in higher dimensions reduces to the one-dimensional
transform. Therefore the iterated form is the main statement here, and the inversion (4.3.11)
follows from it by Theorem 4.3.2 in each index. The same argument works in every dimension. -/
theorem equation_4_3_11 {n₁ n₂ : ℕ} [NeZero n₁] [NeZero n₂] (y : Fin n₁ → Fin n₂ → ℂ)
    (yhat : Fin n₁ → Fin n₂ → ℂ)
    (hy : ∀ k₁ k₂, yhat k₁ k₂ = ∑ j₁ : Fin n₁, ∑ j₂ : Fin n₂,
      (Complex.exp (2 * π * I / n₁) ^ ((k₁ : ℕ) * (j₁ : ℕ)))⁻¹
        * (Complex.exp (2 * π * I / n₂) ^ ((k₂ : ℕ) * (j₂ : ℕ)))⁻¹ * y j₁ j₂) :
    (∀ k₁ k₂, yhat k₁ k₂ = ((dft n₁)ᴴ *ᵥ fun j₁ => ((dft n₂)ᴴ *ᵥ y j₁) k₂) k₁) ∧
      ∀ j₁ j₂, y j₁ j₂ = ((n₁ : ℂ) * n₂)⁻¹ * ∑ k₁ : Fin n₁, ∑ k₂ : Fin n₂,
        Complex.exp (2 * π * I / n₁) ^ ((j₁ : ℕ) * (k₁ : ℕ))
          * Complex.exp (2 * π * I / n₂) ^ ((j₂ : ℕ) * (k₂ : ℕ)) * yhat k₁ k₂ := by
  have hn₁ : (n₁ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n₁)
  have hn₂ : (n₂ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n₂)
  -- the defining double sum is the iterated transform
  have hiter : ∀ k₁ k₂, yhat k₁ k₂ = ((dft n₁)ᴴ *ᵥ fun j₁ => ((dft n₂)ᴴ *ᵥ y j₁) k₂) k₁ := by
    intro k₁ k₂
    rw [hy, conjTranspose_dft_mulVec_apply]
    refine Finset.sum_congr rfl fun j₁ _ => ?_
    rw [conjTranspose_dft_mulVec_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j₂ _ => ?_
    rw [inv_pow, inv_pow, Nat.mul_comm (k₁ : ℕ) (j₁ : ℕ), Nat.mul_comm (k₂ : ℕ) (j₂ : ℕ)]
    ring
  refine ⟨hiter, fun j₁ j₂ => ?_⟩
  -- invert in the first index
  have hcol : ∀ k₂ : Fin n₂, ∑ k₁ : Fin n₁,
      Complex.exp (2 * π * I / n₁) ^ ((j₁ : ℕ) * (k₁ : ℕ)) * yhat k₁ k₂
        = (n₁ : ℂ) * ((dft n₂)ᴴ *ᵥ y j₁) k₂ := by
    intro k₂
    have hfun : (fun k₁ => yhat k₁ k₂)
        = (dft n₁)ᴴ *ᵥ fun j => ((dft n₂)ᴴ *ᵥ y j) k₂ := funext fun k₁ => hiter k₁ k₂
    have h := congrFun (dft_mulVec_conjTranspose_dft_mulVec
      (fun j => ((dft n₂)ᴴ *ᵥ y j) k₂)) j₁
    rw [Pi.smul_apply, smul_eq_mul, Matrix.mulVec_apply_eq_sum] at h
    rw [← h, ← hfun]
    exact Finset.sum_congr rfl fun k₁ _ => by rw [dft_apply]
  -- invert in the second index
  have hrow : ∑ k₂ : Fin n₂,
      Complex.exp (2 * π * I / n₂) ^ ((j₂ : ℕ) * (k₂ : ℕ)) * ((dft n₂)ᴴ *ᵥ y j₁) k₂
        = (n₂ : ℂ) * y j₁ j₂ := by
    have h := congrFun (dft_mulVec_conjTranspose_dft_mulVec (y j₁)) j₂
    rw [Pi.smul_apply, smul_eq_mul, Matrix.mulVec_apply_eq_sum] at h
    rw [← h]
    exact Finset.sum_congr rfl fun k₂ _ => by rw [dft_apply]
  rw [Finset.sum_comm]
  have hswap : ∑ k₂ : Fin n₂, ∑ k₁ : Fin n₁,
      Complex.exp (2 * π * I / n₁) ^ ((j₁ : ℕ) * (k₁ : ℕ))
          * Complex.exp (2 * π * I / n₂) ^ ((j₂ : ℕ) * (k₂ : ℕ)) * yhat k₁ k₂
      = ∑ k₂ : Fin n₂, Complex.exp (2 * π * I / n₂) ^ ((j₂ : ℕ) * (k₂ : ℕ))
          * ((n₁ : ℂ) * ((dft n₂)ᴴ *ᵥ y j₁) k₂) := by
    refine Finset.sum_congr rfl fun k₂ _ => ?_
    rw [← hcol k₂, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k₁ _ => by ring
  have hval : ∑ k₂ : Fin n₂, Complex.exp (2 * π * I / n₂) ^ ((j₂ : ℕ) * (k₂ : ℕ))
      * ((n₁ : ℂ) * ((dft n₂)ᴴ *ᵥ y j₁) k₂) = (n₁ : ℂ) * ((n₂ : ℂ) * y j₁ j₂) := by
    rw [← hrow, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k₂ _ => by ring
  rw [hswap, hval]
  field_simp

end AtkinsonHan.Chapter04
