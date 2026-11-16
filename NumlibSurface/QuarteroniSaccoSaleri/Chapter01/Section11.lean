/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Numlib.Analysis.Matrix.OperatorNorm
import NumlibSurface.QuarteroniSaccoSaleri.Chapter01.Section10

/-!
# Quarteroni, Sacco and Saleri, Section 1.11: Matrix norms

This module formalizes §1.11 of [quarteroni2000numerical]. A matrix norm $\|\cdot\|$ is consistent
with vector norms if $\|Ax\| \le \|A\| \|x\|$ (Definition 1.20), and sub-multiplicative if
$\|AB\| \le \|A\| \|B\|$ (Definition 1.21). Every vector norm induces the matrix norm
$\|A\| = \sup_{x \neq 0} \|Ax\| / \|x\|$ (Theorem 1.1), which is consistent, sub-multiplicative and
has $\|I\| = 1$ (Theorem 1.3). The module treats the Frobenius norm (Example 1.7), the column sum
norm $\|A\|_1$, the row sum norm $\|A\|_\infty$, and the spectral norm
$\|A\|_2 = \sqrt{\rho(A^H A)}$ (Theorem 1.2) with its estimates. In §1.11.1 it relates norms and the
spectral radius: $\rho(A) \le \|A\|$ for every consistent norm (Theorem 1.4), for every
$\varepsilon > 0$ some induced norm has $\|A\| \le \rho(A) + \varepsilon$ (Property 1.13), $\rho(A)$
is the infimum of the induced norms (1.23), and $\|A^m\|^{1/m} \to \rho(A)$ (Property 1.14). In
§1.11.2 it treats sequences and series of matrices: $A^k \to 0$ if and only if $\rho(A) < 1$
(Theorem 1.5), and then $\sum_k A^k = (I - A)^{-1}$, with the bounds (1.26) on $\|(I - A)^{-1}\|$.

The proofs specialize the backbone modules `Numlib.Analysis.Matrix.OperatorNorm` (the induced norm,
the $p$-norms, the spectral norm, the Frobenius norm and the bounds by the spectral radius),
`Numlib.Analysis.Normed.Algebra.SpectralRadius` (the statements in the Banach algebra of complex
matrices), `Numlib.LinearAlgebra.Matrix.Complexify` (the spectral radius of a real matrix) and
`Numlib.Analysis.Normed.Module.NormEquivalence`.

## Main definitions

* Definition 1.19: a matrix norm is a vector norm of Definition 1.17 on the space of matrices; it
  has no declaration here.
* Definition 1.20, `QuarteroniSaccoSaleri.Chapter01.definition_1_20`: a matrix norm consistent with
  vector norms, stated for the backbone predicate `Matrix.IsConsistent`.
* Definition 1.21, `QuarteroniSaccoSaleri.Chapter01.definition_1_21`: sub-multiplicative matrix
  norms; the $p$-norms are sub-multiplicative.

## Main results

* §1.11, `QuarteroniSaccoSaleri.Chapter01.maxEntryNorm_not_submultiplicative`: the norm
  $\|A\|_\Delta = \max_{ij} |a_{ij}|$ is not sub-multiplicative.
* §1.11, `QuarteroniSaccoSaleri.Chapter01.exists_consistent_vectorNorm`: every sub-multiplicative
  matrix norm has a consistent vector norm.
* Example 1.7, `QuarteroniSaccoSaleri.Chapter01.example_1_7`: the Frobenius norm is compatible with
  the Euclidean norm, and $\|I_n\|_F = \sqrt n$.
* Theorem 1.1, `QuarteroniSaccoSaleri.Chapter01.theorem_1_1`: the norm induced by a vector norm is a
  matrix norm.
* §1.11, `QuarteroniSaccoSaleri.Chapter01.lpOpNorm_one_and_top`: the matrix $p$-norms, the column
  sum norm $\|A\|_1$ and the row sum norm $\|A\|_\infty$.
* §1.11, `QuarteroniSaccoSaleri.Chapter01.lpOpNorm_one_eq_linfty_opNorm_transpose`:
  $\|A\|_1 = \|A^T\|_\infty$, and $\|A\|_1 = \|A\|_\infty$ for a Hermitian or real symmetric $A$.
* Theorem 1.2, `QuarteroniSaccoSaleri.Chapter01.theorem_1_2`: $\|A\|_2 = \sqrt{\rho(A^H A)} =
  \sqrt{\rho(A A^H)}$, the largest singular value.
* Theorem 1.2, `QuarteroniSaccoSaleri.Chapter01.theorem_1_2_hermitian`: $\|A\|_2 = \rho(A)$ for a
  Hermitian or real symmetric $A$.
* Theorem 1.2, `QuarteroniSaccoSaleri.Chapter01.theorem_1_2_unitary`: $\|A\|_2 = 1$ for a unitary or
  real orthogonal $A$.
* §1.11, `QuarteroniSaccoSaleri.Chapter01.l2_opNorm_bounds`: the estimates of $\|A\|_2$ by the
  entries, $\|A\|_1$ and $\|A\|_\infty$.
* §1.11, `QuarteroniSaccoSaleri.Chapter01.l2_opNorm_le_lpOpNorm_of_isStarNormal`:
  $\|A\|_2 \le \|A\|_p$ for a normal $A$.
* Exercise 16 of Chapter 1, `QuarteroniSaccoSaleri.Chapter01.exercise_1_16`:
  $\|A\|_F^2 = \sum_i \sigma_i^2$ and $\|A\|_2 \le \|A\|_F \le \sqrt{\operatorname{rank} A}
  \|A\|_2$.
* Theorem 1.3, `QuarteroniSaccoSaleri.Chapter01.theorem_1_3`: an induced norm is consistent and
  sub-multiplicative, with $\|I\| = 1$.
* Theorem 1.4, `QuarteroniSaccoSaleri.Chapter01.theorem_1_4` and
  `QuarteroniSaccoSaleri.Chapter01.theorem_1_4_real`: $\rho(A) \le \|A\|$ for every consistent
  matrix norm, for complex and for real matrices.
* Property 1.13, `QuarteroniSaccoSaleri.Chapter01.property_1_13`: for every $\varepsilon > 0$ there
  is an induced norm with $\|A\| \le \rho(A) + \varepsilon$.
* Equation (1.23), `QuarteroniSaccoSaleri.Chapter01.equation_1_23`: $\rho(A)$ is the infimum of the
  induced norms of $A$.
* §1.11.1, `QuarteroniSaccoSaleri.Chapter01.spectralRadius_not_subadditive`: the spectral radius is
  neither subadditive nor sub-multiplicative.
* Property 1.14, `QuarteroniSaccoSaleri.Chapter01.property_1_14` (Gelfand's formula):
  $\|A^m\|^{1/m} \to \rho(A)$.
* §1.11.2, `QuarteroniSaccoSaleri.Chapter01.tendsto_iff_tendsto_seminorm`: convergence of a sequence
  of matrices does not depend on the norm.
* Theorem 1.5, `QuarteroniSaccoSaleri.Chapter01.theorem_1_5`: $A^k \to 0$ if and only if
  $\rho(A) < 1$.
* Theorem 1.5, `QuarteroniSaccoSaleri.Chapter01.theorem_1_5_series`: $\sum_k A^k$ converges if and
  only if $\rho(A) < 1$, and then its sum is $(I - A)^{-1}$.
* Equation (1.26), `QuarteroniSaccoSaleri.Chapter01.equation_1_26`: if $\|A\| < 1$ for an induced
  norm, then $1/(1 + \|A\|) \le \|(I - A)^{-1}\| \le 1/(1 - \|A\|)$.
* Remark 1.1, `QuarteroniSaccoSaleri.Chapter01.remark_1_1`: if $\rho(A) < 1$, some induced norm has
  $\|A\| < 1$.

## Conventions

* A matrix norm (Definition 1.19) is a definite seminorm on the space of matrices,
  `N : Seminorm ℝ (Matrix (Fin m) (Fin n) ℝ)` with `∀ M, N M = 0 → M = 0`. This is the vector norm
  of Definition 1.17 on that space.
* The norm induced by vector norms `p` on the domain and `q` on the codomain (Theorem 1.1) is the
  backbone's `Matrix.inducedNorm q p`. The matrix $p$-norms are `Matrix.lpOpNorm p`, and
  `Matrix.lpOpNorm_eq_inducedNorm` connects the two.
* The norms $\|\cdot\|_\infty$, $\|\cdot\|_2$, $\|\cdot\|_F$ and
  $\|\cdot\|_\Delta = \max_{ij} |a_{ij}|$ are Mathlib's scoped matrix norm instances
  `Matrix.Norms.Operator`, `Matrix.Norms.L2Operator`, `Matrix.Norms.Frobenius` and
  `Matrix.Norms.Elementwise`, opened for one declaration at a time.
* The spectral radius of a complex matrix is `spectralRadius ℂ A`, and that of a real matrix is
  `Matrix.complexSpectralRadius A`. Both take values in $[0, \infty]$, so a real bound
  $\rho(A) \le \|A\|$ reads `≤ ENNReal.ofReal ‖A‖`.
* The book works in $\mathbb{R}^{m \times n}$ for the definitions and in $\mathbb{C}^{n \times n}$
  for the spectral statements. The declarations follow the book, with the real form beside the
  complex one where the book uses both.
* The book's matrices have positive size (§1.2). This is the hypothesis `[NeZero n]` of the
  statements that need a nonempty index type.

## Implementation notes

* Theorem 1.4 for a real matrix and a real vector norm is a separate statement,
  `QuarteroniSaccoSaleri.Chapter01.theorem_1_4_real`. The eigenvector in the book's proof can be
  complex, so the backbone proves the real case through the induced norm.

## Deviations from the source

* **Example 1.7** (typo). Equation (1.18) prints $\|A\|_F = \operatorname{tr}(A A^H)$ for
  $\sqrt{\operatorname{tr}(A A^H)}$. See `QuarteroniSaccoSaleri.Chapter01.example_1_7`.
* **After Theorem 1.2** (generalization). The book states $\|A\|_2 \le \|A\|_p$ for a normal $A$ and
  $p \ge 2$; it holds for every $p \ge 1$. See
  `QuarteroniSaccoSaleri.Chapter01.l2_opNorm_le_lpOpNorm_of_isStarNormal`.
* **After Property 1.13** (correction). The book calls the spectral radius a sub-multiplicative
  seminorm; it is neither subadditive nor sub-multiplicative. See
  `QuarteroniSaccoSaleri.Chapter01.spectralRadius_not_subadditive`.
* **Equation (1.23)** (reading). The book takes the infimum over all consistent norms; it is stated
  over the induced norms, which gives the same value. See
  `QuarteroniSaccoSaleri.Chapter01.equation_1_23`.
* **Property 1.14** (generalization). The book asks for a consistent matrix norm; the limit holds
  for every matrix norm. See `QuarteroniSaccoSaleri.Chapter01.property_1_14`.
-/

open Filter Finset Matrix Topology WithLp
open scoped ENNReal NNReal

namespace QuarteroniSaccoSaleri.Chapter01

/-! ### Definitions 1.20 and 1.21 -/

/-- **Definition 1.20** of [quarteroni2000numerical], with (1.16). Let $\|\cdot\|$ be a function on
$\mathbb{R}^{m \times n}$, and let $\|\cdot\|_q$ and $\|\cdot\|_p$ be seminorms on
$\mathbb{R}^m$ and $\mathbb{R}^n$. The function $\|\cdot\|$ is **compatible**, or
**consistent**, with these vector norms if and only if
$$\|Ax\|_q \le \|A\| \, \|x\|_p \quad \text{for all } A \in \mathbb{R}^{m \times n}, \ x \in
  \mathbb{R}^n.$$
For square matrices the same vector norm is taken on both sides.

Consistency is the backbone predicate `Matrix.IsConsistent N q p`. -/
theorem definition_1_20 {m n : ℕ} (N : Matrix (Fin m) (Fin n) ℝ → ℝ) (q : Seminorm ℝ (Fin m → ℝ))
    (p : Seminorm ℝ (Fin n → ℝ)) (N' : Matrix (Fin n) (Fin n) ℝ → ℝ) :
    (IsConsistent N q p ↔ ∀ A x, q (A *ᵥ x) ≤ N A * p x) ∧
      (IsConsistent N' p p ↔ ∀ A x, p (A *ᵥ x) ≤ N' A * p x) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- **Definition 1.21** of [quarteroni2000numerical], with (1.17). A matrix norm defined on matrices
of all sizes is **sub-multiplicative** if $\|AB\| \le \|A\| \|B\|$ for all
$A \in \mathbb{R}^{n \times m}$ and $B \in \mathbb{R}^{m \times q}$. The statement shows that
the matrix $r$-norms are sub-multiplicative for every $r \in [1, \infty]$:
$$\|AB\|_r \le \|A\|_r \|B\|_r.$$

This is the remark after Theorem 1.3. The proof is the backbone theorem
`Matrix.lpOpNorm_mul_le`. -/
theorem definition_1_21 {n m q : ℕ} (r : ℝ≥0∞) [Fact (1 ≤ r)] (A : Matrix (Fin n) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin q) ℝ) :
    lpOpNorm r (A * B) ≤ lpOpNorm r A * lpOpNorm r B :=
  lpOpNorm_mul_le r A B

open scoped Matrix.Norms.Elementwise in
/-- **Section 1.11** of [quarteroni2000numerical], the example after Definition 1.21, which the book
attributes to Golub and Van Loan. The function $\|A\|_\Delta = \max_{ij} |a_{ij}|$ is a matrix
norm, but it is not sub-multiplicative: for
$$A = B = \begin{bmatrix} 1 & 1 \\ 1 & 1 \end{bmatrix},$$
$\|AB\|_\Delta = 2 > 1 = \|A\|_\Delta \|B\|_\Delta$.

The norm $\|\cdot\|_\Delta$ is Mathlib's elementwise supremum norm `Matrix.Norms.Elementwise`. -/
theorem maxEntryNorm_not_submultiplicative :
    ‖(!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) * !![1, 1; 1, 1]‖ = 2 ∧
      ‖(!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)‖ * ‖(!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)‖
        = 1 := by
  have hA : ‖(!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)‖ = 1 := by
    refine le_antisymm ((norm_le_iff zero_le_one).2 fun i j => ?_) ?_
    · fin_cases i <;> fin_cases j <;> simp
    · simpa using norm_apply_le_norm (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)
        (i := 0) (j := 0)
  have hmul : (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) * !![1, 1; 1, 1] = !![2, 2; 2, 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  refine ⟨?_, by rw [hA, mul_one]⟩
  rw [hmul]
  refine le_antisymm ((norm_le_iff zero_le_two).2 fun i j => ?_) ?_
  · fin_cases i <;> fin_cases j <;> simp
  · simpa using norm_apply_le_norm (!![2, 2; 2, 2] : Matrix (Fin 2) (Fin 2) ℝ)
      (i := 0) (j := 0)

/-- **Section 1.11** of [quarteroni2000numerical], after Definition 1.21: every sub-multiplicative
matrix norm has a consistent vector norm. Let $\|\cdot\|_\alpha$ be a sub-multiplicative matrix
norm on $\mathbb{C}^{n \times n}$, and let $y \in \mathbb{C}^n$ with $y \neq 0$. Then
$\|x\| = \|x y^H\|_\alpha$ is a vector norm on $\mathbb{C}^n$, and $\|\cdot\|_\alpha$ is
consistent with it.

The seminorm composes `N` with the linear map `fun x => vecMulVec x (star y)`, which is
$x \mapsto x y^H$.
Consistency follows from $A (x y^H) = (Ax) y^H$ and sub-multiplicativity. The proof uses the
backbone theorem `Matrix.exists_isConsistent_of_mul_le`, which does not name the norm. -/
theorem exists_consistent_vectorNorm {n : ℕ} (N : Seminorm ℂ (Matrix (Fin n) (Fin n) ℂ))
    (hN : ∀ B, N B = 0 → B = 0) (hmul : ∀ A B, N (A * B) ≤ N A * N B) {y : Fin n → ℂ}
    (hy : y ≠ 0) :
    ∃ p : Seminorm ℂ (Fin n → ℂ), (∀ x, p x = N (vecMulVec x (star y))) ∧
      IsConsistent N p p ∧ ∀ x, p x = 0 → x = 0 := by
  refine ⟨N.comp ((vecMulVecBilin ℂ ℂ).flip (star y)), fun x => rfl, fun A x => ?_,
    fun x hx => ?_⟩
  · simp only [Seminorm.comp_apply, LinearMap.flip_apply, vecMulVecBilin_apply_apply]
    rw [← mul_vecMulVec]
    exact hmul _ _
  · have h0 : vecMulVec x (star y) = 0 := hN _ hx
    rw [vecMulVec_eq_zero] at h0
    exact h0.resolve_right fun h => hy (star_eq_zero.1 h)

/-! ### Example 1.7: the Frobenius norm -/

open scoped Matrix.Norms.Frobenius in
/-- **Example 1.7** of [quarteroni2000numerical], with (1.18). Let $A \in \mathbb{C}^{n \times n}$
and $x \in \mathbb{C}^n$. The **Frobenius norm**
$$\|A\|_F = \Big(\sum_{i,j} |a_{ij}|^2\Big)^{1/2}$$
satisfies $\|A\|_F^2 = \operatorname{tr}(A A^H)$. It is compatible with the Euclidean vector
norm, $\|Ax\|_2 \le \|A\|_F \|x\|_2$, and $\|I_n\|_F = \sqrt n$.

**Typo.** The display (1.18) prints $\|A\|_F = \operatorname{tr}(A A^H)$, without the square
root. The statement here is $\|A\|_F^2 = \operatorname{tr}(A A^H)$.

The Frobenius norm is Mathlib's scoped `Matrix.Norms.Frobenius`, which is a matrix norm. The
compatibility uses the backbone theorem `Matrix.frobenius_norm_mulVec_le`. -/
theorem example_1_7 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    ‖A‖ = √(∑ i, ∑ j, ‖A i j‖ ^ 2) ∧ ((‖A‖ ^ 2 : ℝ) : ℂ) = trace (A * Aᴴ) ∧
      ‖toLp 2 (A *ᵥ x)‖ ≤ ‖A‖ * ‖toLp 2 x‖ ∧ ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ = √n := by
  refine ⟨?_, ?_, frobenius_norm_mulVec_le A x, by simpa using frobenius_norm_one (n := Fin n)⟩
  · rw [← frobenius_norm_sq_eq_sum_sq, Real.sqrt_sq (norm_nonneg _)]
  · have h := frobenius_norm_sq_eq_trace A
    rw [trace_mul_comm] at h
    exact_mod_cast h

/-! ### Theorem 1.1: the induced norm -/

section Induced

variable {m n : ℕ}

/-- **Theorem 1.1** of [quarteroni2000numerical], with (1.19) and (1.20). Let $n \ge 1$, let
$\|\cdot\|_p$ be a vector norm on $\mathbb{R}^n$ and $\|\cdot\|_q$ a vector norm on
$\mathbb{R}^m$. For $A \in \mathbb{R}^{m \times n}$ let
$$\|A\| = \sup_{x \neq 0} \frac{\|Ax\|_q}{\|x\|_p} = \sup_{\|x\|_p = 1} \|Ax\|_q.$$
The two suprema agree, and the second is attained at some $w$ with $\|w\|_p = 1$. The function
$\|\cdot\|$ is a matrix norm, the **induced** or **natural** matrix norm: for all
$A, B \in \mathbb{R}^{m \times n}$ and $\alpha \in \mathbb{R}$, $\|A\| \ge 0$, $\|A\| = 0$ if
and only if $A = 0$, $\|\alpha A\| = |\alpha| \|A\|$, and $\|A + B\| \le \|A\| + \|B\|$.

The induced norm is the backbone's `Matrix.inducedNorm q p A`, defined as the supremum of
$\|Ax\|_q$ over $\|x\|_p \le 1$. -/
theorem theorem_1_1 [NeZero n] (q : Seminorm ℝ (Fin m → ℝ)) (p : Seminorm ℝ (Fin n → ℝ))
    (hq : ∀ y, q y = 0 → y = 0) (hp : ∀ x, p x = 0 → x = 0) (A B : Matrix (Fin m) (Fin n) ℝ)
    (α : ℝ) :
    inducedNorm q p A = ⨆ x : {x : Fin n → ℝ // x ≠ 0}, q (A *ᵥ x) / p x ∧
      inducedNorm q p A = ⨆ x : {x : Fin n → ℝ // p x = 1}, q (A *ᵥ x) ∧
      (∃ w, p w = 1 ∧ inducedNorm q p A = q (A *ᵥ w)) ∧
      (0 ≤ inducedNorm q p A ∧ (inducedNorm q p A = 0 ↔ A = 0)) ∧
      inducedNorm q p (α • A) = |α| * inducedNorm q p A ∧
      inducedNorm q p (A + B) ≤ inducedNorm q p A + inducedNorm q p B := by
  obtain ⟨w, hw, hAw⟩ := exists_inducedNorm_eq (q := q) hp A
  refine ⟨inducedNorm_eq_iSup_div hp A, ?_, ⟨w, hw, hAw⟩,
    ⟨inducedNorm_nonneg A, inducedNorm_eq_zero_iff hq hp A⟩, ?_,
    map_add_le_add (inducedSeminorm q p hp) A B⟩
  · have hne : Nonempty {x : Fin n → ℝ // p x = 1} := ⟨⟨w, hw⟩⟩
    have hbdd : BddAbove (Set.range fun x : {x : Fin n → ℝ // p x = 1} => q (A *ᵥ x)) :=
      ⟨inducedNorm q p A, by rintro _ ⟨x, rfl⟩; exact le_inducedNorm hp A x.2.le⟩
    refine le_antisymm ?_ (ciSup_le fun x => le_inducedNorm hp A x.2.le)
    rw [hAw]
    exact le_ciSup hbdd ⟨w, hw⟩
  · rw [← inducedSeminorm_apply (q := q) hp, map_smul_eq_mul, Real.norm_eq_abs,
      inducedSeminorm_apply]

/-- **Section 1.11** of [quarteroni2000numerical], the $p$-norms and the $1$- and $\infty$-norms,
after Theorem 1.1. Let $A \in \mathbb{R}^{m \times n}$ and $r \in [1, \infty]$. The matrix
$r$-norm
$$\|A\|_r = \sup_{x \neq 0} \frac{\|Ax\|_r}{\|x\|_r}$$
is the norm induced by the vector $r$-norm. The $1$-norm is the **column sum norm** and the
$\infty$-norm is the **row sum norm**:
$$\|A\|_1 = \max_j \sum_i |a_{ij}|, \qquad \|A\|_\infty = \max_i \sum_j |a_{ij}|.$$

The matrix $r$-norm is `Matrix.lpOpNorm r A`, and the vector $r$-norm is `Matrix.lpSeminorm r`,
the norm of `toLp r x`. The proof uses the backbone theorems `Matrix.lpOpNorm_eq_inducedNorm`
and `Matrix.lpOpNorm_one_eq_sup_sum_norm`, and Mathlib's `Matrix.linfty_opNorm_def`. The maxima
are suprema over finite sets, which are $0$ when the set is empty. -/
theorem lpOpNorm_one_and_top (r : ℝ≥0∞) [Fact (1 ≤ r)] (A : Matrix (Fin m) (Fin n) ℝ) :
    lpOpNorm r A = inducedNorm (lpSeminorm r) (lpSeminorm r) A ∧
      (∀ x : Fin n → ℝ, lpSeminorm r x = ‖toLp r x‖) ∧
      lpOpNorm 1 A = ↑(univ.sup fun j => ∑ i, ‖A i j‖₊) ∧
      lpOpNorm ⊤ A = ↑(univ.sup fun i => ∑ j, ‖A i j‖₊) := by
  refine ⟨lpOpNorm_eq_inducedNorm r A, fun x => rfl, lpOpNorm_one_eq_sup_sum_norm A, ?_⟩
  open scoped Matrix.Norms.Operator in
  rw [lpOpNorm_top, linfty_opNorm_def]

/-- **Section 1.11** of [quarteroni2000numerical], after the column and the row sum norms. For
$A \in \mathbb{R}^{m \times n}$, $\|A\|_1 = \|A^T\|_\infty$. If $B \in \mathbb{C}^{n \times n}$
is Hermitian, then $\|B\|_1 = \|B\|_\infty$; if $C \in \mathbb{R}^{n \times n}$ is symmetric,
then $\|C\|_1 = \|C\|_\infty$.

The proof uses the backbone theorems `Matrix.lpOpNorm_one_eq_linfty_opNorm_transpose` and
`Matrix.IsHermitian.lpOpNorm_one_eq_linfty_opNorm`. -/
theorem lpOpNorm_one_eq_linfty_opNorm_transpose (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin n) (Fin n) ℝ) :
    lpOpNorm 1 A = lpOpNorm ⊤ Aᵀ ∧ (B.IsHermitian → lpOpNorm 1 B = lpOpNorm ⊤ B) ∧
      (C.IsSymm → lpOpNorm 1 C = lpOpNorm ⊤ C) := by
  open scoped Matrix.Norms.Operator in
  refine ⟨by rw [lpOpNorm_top, Matrix.lpOpNorm_one_eq_linfty_opNorm_transpose],
    fun hB => by rw [lpOpNorm_top, hB.lpOpNorm_one_eq_linfty_opNorm],
    fun hC => by rw [lpOpNorm_top, (isHermitian_iff_isSymm.2 hC).lpOpNorm_one_eq_linfty_opNorm]⟩

end Induced

/-! ### Theorem 1.2: the spectral norm -/

section Spectral

open scoped Matrix.Norms.L2Operator

variable {m n : ℕ}

/-- **Theorem 1.2** of [quarteroni2000numerical], with (1.21). Let $n \ge 1$. For
$A \in \mathbb{C}^{m \times n}$,
$$\|A\|_2 = \sqrt{\rho(A^H A)} = \sqrt{\rho(A A^H)}.$$
For $B \in \mathbb{C}^{n \times n}$, $\|B\|_2 = \sigma_1(B) = \max_i \sigma_i(B)$ is the largest
singular value. For $C \in \mathbb{R}^{n \times n}$, $\|C\|_2^2 = \rho(C^T C)$, with the
spectral radius of $C^T C$ regarded as a complex matrix.

The spectral norm $\|\cdot\|_2$ is Mathlib's scoped `Matrix.Norms.L2Operator`. The identities
$\|A\|_2^2 = \rho(A^H A)$ are the backbone theorem
`Matrix.l2_opNorm_sq_eq_spectralRadius_conjTranspose_mul_self` and its companions, stated in
$[0, \infty]$; the square roots are their real form. The singular values are
`Matrix.colSingularValues B`. -/
theorem theorem_1_2 [NeZero n] (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin n) (Fin n) ℝ) :
    ((‖A‖₊ : ℝ≥0∞) ^ 2 = spectralRadius ℂ (Aᴴ * A) ∧
        (‖A‖₊ : ℝ≥0∞) ^ 2 = spectralRadius ℂ (A * Aᴴ)) ∧
      (‖A‖ = √(spectralRadius ℂ (Aᴴ * A)).toReal ∧ ‖A‖ = √(spectralRadius ℂ (A * Aᴴ)).toReal) ∧
      ‖B‖ = ⨆ i, B.colSingularValues i ∧
      (‖C‖₊ : ℝ≥0∞) ^ 2 = complexSpectralRadius (Cᵀ * C) := by
  have h₁ := l2_opNorm_sq_eq_spectralRadius_conjTranspose_mul_self A
  have h₂ := l2_opNorm_sq_eq_spectralRadius_self_mul_conjTranspose A
  have hsq : ∀ ρ : ℝ≥0∞, (‖A‖₊ : ℝ≥0∞) ^ 2 = ρ → ‖A‖ = √ρ.toReal := fun ρ h => by
    rw [← h, ENNReal.toReal_pow, ENNReal.coe_toReal, coe_nnnorm, Real.sqrt_sq (norm_nonneg _)]
  refine ⟨⟨h₁, h₂⟩, ⟨hsq _ h₁, hsq _ h₂⟩, l2_opNorm_eq_iSup_colSingularValues B, ?_⟩
  rw [← conjTranspose_eq_transpose_of_trivial]
  exact l2_opNorm_sq_eq_complexSpectralRadius_conjTranspose_mul_self C

/-- **Theorem 1.2** of [quarteroni2000numerical], with (1.22). If $A \in \mathbb{C}^{n \times n}$ is
Hermitian, then $\|A\|_2 = \rho(A)$. If $B \in \mathbb{R}^{n \times n}$ is symmetric, then
$\|B\|_2 = \rho(B)$, with the spectral radius of $B$ regarded as a complex matrix.

Both identities are stated in $[0, \infty]$ and in $\mathbb{R}$. The proof uses the backbone
theorems `Matrix.IsHermitian.l2_opNorm_eq_spectralRadius` and
`Matrix.IsHermitian.l2_opNNNorm_eq_complexSpectralRadius`. -/
theorem theorem_1_2_hermitian {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsSymm) :
    ((‖A‖₊ : ℝ≥0∞) = spectralRadius ℂ A ∧ ‖A‖ = (spectralRadius ℂ A).toReal) ∧
      ((‖B‖₊ : ℝ≥0∞) = B.complexSpectralRadius ∧ ‖B‖ = B.complexSpectralRadius.toReal) := by
  have h₁ := hA.l2_opNorm_eq_spectralRadius
  have h₂ := (isHermitian_iff_isSymm.2 hB).l2_opNNNorm_eq_complexSpectralRadius
  exact ⟨⟨h₁, by rw [← h₁, ENNReal.coe_toReal, coe_nnnorm]⟩,
    ⟨h₂, by rw [← h₂, ENNReal.coe_toReal, coe_nnnorm]⟩⟩

/-- **Theorem 1.2** of [quarteroni2000numerical], the last clause. Let $n \ge 1$. If
$A \in \mathbb{C}^{n \times n}$ is unitary, then $\|A\|_2 = 1$. If
$Q \in \mathbb{R}^{n \times n}$ is orthogonal, then $\|Q\|_2 = 1$.

The proof uses the backbone theorem `Matrix.l2_opNorm_of_mem_unitaryGroup`. -/
theorem theorem_1_2_unitary [NeZero n] {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A ∈ unitaryGroup (Fin n) ℂ) {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin n) ℝ) : ‖A‖ = 1 ∧ ‖Q‖ = 1 :=
  ⟨l2_opNorm_of_mem_unitaryGroup hA, l2_opNorm_of_mem_unitaryGroup hQ⟩

/-- If $a \le \sqrt n \, b$ and $b \ge 0$, then $a / \sqrt n \le b$, where $1/\sqrt 0 = 0$ in Lean
covers the case $n = 0$. -/
private theorem one_div_sqrt_mul_le {a b : ℝ} (hb : 0 ≤ b) (h : a ≤ √(n : ℝ) * b) :
    1 / √(n : ℝ) * a ≤ b := by
  rcases eq_or_ne (√(n : ℝ)) 0 with h0 | h0
  · rw [h0, div_zero, zero_mul]; exact hb
  · calc 1 / √(n : ℝ) * a ≤ 1 / √(n : ℝ) * (√(n : ℝ) * b) := by gcongr
      _ = b := by field_simp

/-- **Section 1.11** of [quarteroni2000numerical], the estimates of $\|A\|_2$ after Theorem 1.2. Let
$A \in \mathbb{C}^{n \times n}$. Then:

* $|a_{ij}| \le \|A\|_2$ for all $i, j$, and if $|a_{ij}| \le M$ for all $i, j$, with $M \ge 0$,
  then $\|A\|_2 \le n M$; so $\max_{ij} |a_{ij}| \le \|A\|_2 \le n \max_{ij} |a_{ij}|$;
* $n^{-1/2} \|A\|_\infty \le \|A\|_2 \le n^{1/2} \|A\|_\infty$;
* $n^{-1/2} \|A\|_1 \le \|A\|_2 \le n^{1/2} \|A\|_1$;
* $\|A\|_2 \le \sqrt{\|A\|_1 \|A\|_\infty}$.

The norms are `Matrix.lpOpNorm 2`, `Matrix.lpOpNorm 1` and `Matrix.lpOpNorm ⊤`. For $n = 0$ the
factor $n^{-1/2}$ is $0$. The proof uses the backbone theorems `Matrix.norm_entry_le_l2_opNorm`,
`Matrix.l2_opNorm_le_sqrt_card_mul_of_forall_norm_le`,
`Matrix.l2_opNorm_le_sqrt_card_mul_linfty_opNorm`,
`Matrix.l2_opNorm_le_sqrt_card_mul_lpOpNorm_one` and
`Matrix.l2_opNorm_sq_le_lpOpNorm_one_mul_linfty_opNorm`. -/
theorem l2_opNorm_bounds (A : Matrix (Fin n) (Fin n) ℂ) :
    ((∀ i j, ‖A i j‖ ≤ lpOpNorm 2 A) ∧
        ∀ M : ℝ, 0 ≤ M → (∀ i j, ‖A i j‖ ≤ M) → lpOpNorm 2 A ≤ n * M) ∧
      (1 / √(n : ℝ) * lpOpNorm ⊤ A ≤ lpOpNorm 2 A ∧ lpOpNorm 2 A ≤ √(n : ℝ) * lpOpNorm ⊤ A) ∧
      (1 / √(n : ℝ) * lpOpNorm 1 A ≤ lpOpNorm 2 A ∧ lpOpNorm 2 A ≤ √(n : ℝ) * lpOpNorm 1 A) ∧
      lpOpNorm 2 A ≤ √(lpOpNorm 1 A * lpOpNorm ⊤ A) := by
  have hinf := l2_opNorm_le_sqrt_card_mul_linfty_opNorm A
  have hone := l2_opNorm_le_sqrt_card_mul_lpOpNorm_one A
  simp only [Fintype.card_fin] at hinf hone
  refine ⟨⟨fun i j => ?_, fun M hM h => ?_⟩,
    ⟨one_div_sqrt_mul_le (lpOpNorm_nonneg 2 A) hinf.2, hinf.1⟩,
    ⟨one_div_sqrt_mul_le (lpOpNorm_nonneg 2 A) hone.1, hone.2⟩, ?_⟩
  · rw [lpOpNorm_two]
    exact norm_entry_le_l2_opNorm A i j
  · have h' := l2_opNorm_le_sqrt_card_mul_of_forall_norm_le A hM h
    rwa [Fintype.card_fin, Real.sqrt_mul_self (Nat.cast_nonneg n)] at h'
  · rw [Real.le_sqrt (lpOpNorm_nonneg 2 A)
      (mul_nonneg (lpOpNorm_nonneg 1 A) (lpOpNorm_nonneg ⊤ A))]
    exact l2_opNorm_sq_le_lpOpNorm_one_mul_linfty_opNorm A

/-- **Section 1.11** of [quarteroni2000numerical], normal matrices, after the estimates of
$\|A\|_2$. If $A \in \mathbb{C}^{n \times n}$ is normal and $p \in [1, \infty]$, then
$\|A\|_2 \le \|A\|_p$.

**Generalization.** The book states the inequality for $p \ge 2$. It holds for every $p \ge 1$,
because $\|A\|_2 = \rho(A)$ for a normal matrix and $\rho(A) \le \|A\|_p$ by Theorem 1.4.

The proof is the backbone theorem `Matrix.l2_opNorm_le_lpOpNorm_of_isStarNormal`. -/
theorem l2_opNorm_le_lpOpNorm_of_isStarNormal (A : Matrix (Fin n) (Fin n) ℂ) [IsStarNormal A]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] : lpOpNorm 2 A ≤ lpOpNorm p A :=
  Matrix.l2_opNorm_le_lpOpNorm_of_isStarNormal A p

open scoped Matrix.Norms.Frobenius in
/-- **Exercise 16 of Chapter 1** of [quarteroni2000numerical], which §1.11 cites for the table of
Exercise 17. Let $A \in \mathbb{R}^{m \times n}$ with singular values $\sigma_i$. Then the
square of the Frobenius norm is the sum of the squares of the singular values,
$$\|A\|_F^2 = \sum_i \sigma_i(A)^2,$$
and consequently $\|A\|_2 \le \|A\|_F \le \sqrt{\operatorname{rank} A} \, \|A\|_2$.

The singular values are `Matrix.colSingularValues A`, indexed by the columns. The proof uses the
backbone theorems `Matrix.frobenius_norm_sq_eq_sum_sq_colSingularValues`,
`Matrix.l2_opNorm_le_frobenius_norm` and `Matrix.frobenius_norm_le_sqrt_rank_mul_l2_opNorm`. -/
theorem exercise_1_16 (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖A‖ ^ 2 = ∑ i, A.colSingularValues i ^ 2 ∧ lpOpNorm 2 A ≤ ‖A‖ ∧
      ‖A‖ ≤ √(A.rank : ℝ) * lpOpNorm 2 A :=
  ⟨frobenius_norm_sq_eq_sum_sq_colSingularValues A, l2_opNorm_le_frobenius_norm A,
    frobenius_norm_le_sqrt_rank_mul_l2_opNorm A⟩

end Spectral

/-! ### Theorem 1.3 -/

/-- **Theorem 1.3** of [quarteroni2000numerical]. Let $n \ge 1$, let $\|\cdot\|$ be a vector norm on
$\mathbb{R}^n$, and let $|||\cdot|||$ be the matrix norm induced by it. For all
$A, B \in \mathbb{R}^{n \times n}$ and $x \in \mathbb{R}^n$:

* (1) $\|Ax\| \le |||A||| \, \|x\|$, that is, $|||\cdot|||$ is compatible with $\|\cdot\|$;
* (2) $|||I||| = 1$;
* (3) $|||AB||| \le |||A||| \, |||B|||$, that is, $|||\cdot|||$ is sub-multiplicative.

Moreover, as the remark after the theorem says, sub-multiplicativity alone gives only
$N(I) \ge 1$: if a function $N$ on $\mathbb{R}^{n \times n}$ is sub-multiplicative and
$N(I) > 0$, then $N(I) \ge 1$, because $N(I) \le N(I)^2$.

The proof uses the backbone theorems `Matrix.le_inducedNorm_mul`,
`Matrix.isConsistent_inducedNorm`, `Matrix.inducedNorm_one`, `Matrix.inducedNorm_mul_le` and
`Matrix.one_le_of_mul_le`. -/
theorem theorem_1_3 {n : ℕ} [NeZero n] (p : Seminorm ℝ (Fin n → ℝ)) (hp : ∀ x, p x = 0 → x = 0)
    (A B : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) (N : Matrix (Fin n) (Fin n) ℝ → ℝ) :
    (p (A *ᵥ x) ≤ inducedNorm p p A * p x ∧ IsConsistent (inducedNorm p p) p p) ∧
      inducedNorm p p (1 : Matrix (Fin n) (Fin n) ℝ) = 1 ∧
      inducedNorm p p (A * B) ≤ inducedNorm p p A * inducedNorm p p B ∧
      ((∀ A B, N (A * B) ≤ N A * N B) → 0 ≤ N 1 → N 1 ≠ 0 → 1 ≤ N 1) :=
  ⟨⟨le_inducedNorm_mul hp A x, isConsistent_inducedNorm hp⟩, inducedNorm_one hp,
    inducedNorm_mul_le p hp hp A B, fun hmul h0 h1 => one_le_of_mul_le hmul h0 h1⟩

/-! ### §1.11.1 Relation between norms and the spectral radius -/

section SpectralRadius

variable {n : ℕ}

/-- **Theorem 1.4** of [quarteroni2000numerical]. Let $\|\cdot\|$ be a vector norm on
$\mathbb{C}^n$, and let $N$ be a function on $\mathbb{C}^{n \times n}$ consistent with it. Then
$$\rho(A) \le N(A) \quad \text{for every } A \in \mathbb{C}^{n \times n}.$$

The proof is the book's eigenvector argument, the backbone theorem
`Matrix.spectralRadius_le_of_isConsistent`. -/
theorem theorem_1_4 {N : Matrix (Fin n) (Fin n) ℂ → ℝ} {p : Seminorm ℂ (Fin n → ℂ)}
    (hp : ∀ x, p x = 0 → x = 0) (hN : IsConsistent N p p) (A : Matrix (Fin n) (Fin n) ℂ) :
    spectralRadius ℂ A ≤ ENNReal.ofReal (N A) :=
  spectralRadius_le_of_isConsistent hp hN A

/-- **Theorem 1.4** of [quarteroni2000numerical], for a real matrix. Let $\|\cdot\|$ be a vector
norm on $\mathbb{R}^n$, and let $N$ be a function on $\mathbb{R}^{n \times n}$ consistent with
it. For every $A \in \mathbb{R}^{n \times n}$, with $\rho(A)$ the spectral radius of $A$
regarded as a complex matrix,
$$\rho(A) \le N(A), \qquad \rho(A) \le |||A|||, \qquad \rho(A) \le \|A\|_r,$$
where $|||\cdot|||$ is the matrix norm induced by $\|\cdot\|$ and $\|\cdot\|_r$ is the matrix
$r$-norm for any $r \in [1, \infty]$.

The eigenvector in the book's proof can be complex, so it does not apply directly to a real
vector norm. The backbone proof goes through the induced norm, which is an algebra norm:
`Matrix.complexSpectralRadius_le_of_isConsistent`, `Matrix.complexSpectralRadius_le_inducedNorm`
and `Matrix.complexSpectralRadius_le_lpOpNorm`. -/
theorem theorem_1_4_real {N : Matrix (Fin n) (Fin n) ℝ → ℝ} {p : Seminorm ℝ (Fin n → ℝ)}
    (hp : ∀ x, p x = 0 → x = 0) (hN : IsConsistent N p p) (A : Matrix (Fin n) (Fin n) ℝ)
    (r : ℝ≥0∞) [Fact (1 ≤ r)] :
    A.complexSpectralRadius ≤ ENNReal.ofReal (N A) ∧
      A.complexSpectralRadius ≤ ENNReal.ofReal (inducedNorm p p A) ∧
      A.complexSpectralRadius ≤ ENNReal.ofReal (lpOpNorm r A) :=
  ⟨complexSpectralRadius_le_of_isConsistent hp hN A, complexSpectralRadius_le_inducedNorm hp A,
    complexSpectralRadius_le_lpOpNorm r A⟩

/-- **Property 1.13** of [quarteroni2000numerical]. Let $A \in \mathbb{C}^{n \times n}$ and
$\varepsilon > 0$. Then there is a vector norm on $\mathbb{C}^n$, depending on $A$ and
$\varepsilon$, whose induced matrix norm $\|\cdot\|_{A,\varepsilon}$ is consistent with it and
satisfies
$$\|A\|_{A,\varepsilon} \le \rho(A) + \varepsilon.$$
The same holds for $B \in \mathbb{R}^{n \times n}$, with a vector norm on $\mathbb{R}^n$ and the
spectral radius of $B$ regarded as a complex matrix.

The proof uses the backbone theorems `Matrix.exists_inducedNorm_le_spectralRadius_add` and
`Matrix.exists_inducedNorm_le_complexSpectralRadius_add`, built on the norm of
`Numlib.LinearAlgebra.Matrix.EpsilonNorm`. -/
theorem property_1_13 (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin n) ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    (∃ p : Seminorm ℂ (Fin n → ℂ), (∀ x, p x = 0 → x = 0) ∧ IsConsistent (inducedNorm p p) p p ∧
        inducedNorm p p A ≤ (spectralRadius ℂ A).toReal + ε) ∧
      ∃ p : Seminorm ℝ (Fin n → ℝ), (∀ x, p x = 0 → x = 0) ∧ IsConsistent (inducedNorm p p) p p ∧
        inducedNorm p p B ≤ B.complexSpectralRadius.toReal + ε := by
  obtain ⟨p, hp, hle⟩ := exists_inducedNorm_le_spectralRadius_add A hε
  obtain ⟨q, hq, hle'⟩ := exists_inducedNorm_le_complexSpectralRadius_add B hε
  exact ⟨⟨p, hp, isConsistent_inducedNorm hp, hle⟩, ⟨q, hq, isConsistent_inducedNorm hq, hle'⟩⟩

/-- **Equation (1.23)** of [quarteroni2000numerical]. For $A \in \mathbb{R}^{n \times n}$,
$$\rho(A) = \inf \|A\|,$$
where the infimum is taken over the matrix norms induced by the vector norms on $\mathbb{R}^n$,
and $\rho(A)$ is the spectral radius of $A$ regarded as a complex matrix.

**Reading.** The book takes the infimum over all consistent matrix norms. This gives the same
value: every consistent norm is at least $\rho(A)$ by Theorem 1.4, and the induced norms are
consistent.

The proof is the backbone theorem `Matrix.complexSpectralRadius_eq_iInf_inducedNorm`. -/
theorem equation_1_23 (A : Matrix (Fin n) (Fin n) ℝ) :
    A.complexSpectralRadius.toReal =
      ⨅ p : {p : Seminorm ℝ (Fin n → ℝ) // ∀ x, p x = 0 → x = 0}, inducedNorm p.1 p.1 A :=
  complexSpectralRadius_eq_iInf_inducedNorm A

/-- A number $\mu$ is an eigenvalue of $M \in \mathbb{C}^{2 \times 2}$ if and only if
$\mu^2 - \operatorname{tr}(M) \mu + \det M = 0$. -/
private theorem mem_spectrum_fin_two (M : Matrix (Fin 2) (Fin 2) ℂ) (μ : ℂ) :
    μ ∈ spectrum ℂ M ↔ μ ^ 2 - M.trace * μ + M.det = 0 := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot.def, Matrix.charpoly_fin_two]
  simp

/-- **Section 1.11.1** of [quarteroni2000numerical], after Property 1.13: the spectral radius is not
a norm. Let
$$N = \begin{bmatrix} 0 & 1 \\ 0 & 0 \end{bmatrix} \in \mathbb{C}^{2 \times 2}.$$
Then $N \neq 0$ and $\rho(N) = \rho(N^T) = 0$, but
$$\rho(N + N^T) = 1 > 0 = \rho(N) + \rho(N^T), \qquad \rho(N N^T) = 1 > 0 = \rho(N) \rho(N^T).$$
So $\rho$ vanishes at nonzero matrices, and it is neither subadditive nor sub-multiplicative.

**Correction.** The book says that the spectral radius is a sub-multiplicative seminorm, since
it is not true that $\rho(A) = 0$ if and only if $A = 0$. The second part is true, as
$\rho(N) = 0$ shows. The first part is false: the example shows that $\rho$ is neither
subadditive nor sub-multiplicative.

The spectral radius is absolutely homogeneous, by `spectralRadius_smul`. -/
theorem spectralRadius_not_subadditive :
    (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0 ∧
      spectralRadius ℂ (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) = 0 ∧
      spectralRadius ℂ (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)ᵀ = 0 ∧
      spectralRadius ℂ ((!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) + !![0, 1; 0, 0]ᵀ) = 1 ∧
      spectralRadius ℂ ((!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, 1; 0, 0]ᵀ) = 1 := by
  have hT : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)ᵀ = !![0, 0; 1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hsum : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) + !![0, 0; 1, 0] = !![0, 1; 1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hprod : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, 0; 1, 0] = !![1, 0; 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  -- a matrix whose only eigenvalue is `0` has spectral radius `0`
  have hnil : ∀ M : Matrix (Fin 2) (Fin 2) ℂ, M.trace = 0 → M.det = 0 → spectralRadius ℂ M = 0 := by
    intro M htr hdet
    rw [spectralRadius_eq_of_unital]
    refine le_antisymm (iSup₂_le fun μ hμ => ?_) zero_le
    rw [mem_spectrum_fin_two, htr, hdet] at hμ
    have : μ = 0 := pow_eq_zero_iff two_ne_zero |>.1 (by linear_combination hμ)
    simp [this]
  -- a matrix whose eigenvalues have modulus at most `1`, one of them being `1`
  have hone : ∀ M : Matrix (Fin 2) (Fin 2) ℂ, (∀ μ, μ ∈ spectrum ℂ M → ‖μ‖₊ ≤ 1) →
      (1 : ℂ) ∈ spectrum ℂ M → spectralRadius ℂ M = 1 := by
    intro M hle h1
    rw [spectralRadius_eq_of_unital]
    refine le_antisymm (iSup₂_le fun μ hμ => by exact_mod_cast hle μ hμ) ?_
    calc (1 : ℝ≥0∞) = ((‖(1 : ℂ)‖₊ : ℝ≥0) : ℝ≥0∞) := by simp
      _ ≤ _ := le_iSup₂ (f := fun μ (_ : μ ∈ spectrum ℂ M) => ((‖μ‖₊ : ℝ≥0) : ℝ≥0∞)) (1 : ℂ) h1
  have hmod : ∀ μ : ℂ, μ ^ 2 = 1 → ‖μ‖₊ ≤ 1 := fun μ hμ => by
    have h2 : ‖μ‖ ^ 2 = 1 := by rw [← norm_pow, hμ, norm_one]
    have h3 : ‖μ‖ = 1 :=
      (pow_left_inj₀ (norm_nonneg μ) zero_le_one two_ne_zero).mp (by rw [one_pow]; exact h2)
    exact le_of_eq (NNReal.eq (by rw [coe_nnnorm, NNReal.coe_one]; exact h3))
  refine ⟨fun h => by simpa using congrFun (congrFun h 0) 1,
    hnil _ (by simp [trace_fin_two_of]) (by simp [det_fin_two_of]),
    by rw [hT]; exact hnil _ (by simp [trace_fin_two_of]) (by simp [det_fin_two_of]),
    ?_, ?_⟩
  · rw [hT, hsum]
    refine hone _ (fun μ hμ => hmod μ ?_) ((mem_spectrum_fin_two _ _).2 ?_)
    · rw [mem_spectrum_fin_two, trace_fin_two_of, det_fin_two_of] at hμ
      linear_combination hμ
    · simp [trace_fin_two_of, det_fin_two_of]
  · rw [hT, hprod]
    refine hone _ (fun μ hμ => ?_) ((mem_spectrum_fin_two _ _).2 ?_)
    · rw [mem_spectrum_fin_two, trace_fin_two_of, det_fin_two_of] at hμ
      have h : μ * (μ - 1) = 0 := by linear_combination hμ
      rcases mul_eq_zero.1 h with h | h
      · simp [h]
      · rw [sub_eq_zero.1 h]; simp
    · simp [trace_fin_two_of, det_fin_two_of]

open scoped Matrix.Norms.L2Operator in
/-- **Property 1.14** of [quarteroni2000numerical] (Gelfand's formula). Let
$A \in \mathbb{R}^{n \times n}$, and let $N$ be a matrix norm on $\mathbb{R}^{n \times n}$. Then
$$\lim_{m \to \infty} N(A^m)^{1/m} = \rho(A),$$
with the spectral radius of $A$ regarded as a complex matrix. For
$B \in \mathbb{C}^{n \times n}$, $\|B^m\|_2^{1/m} \to \rho(B)$.

**Generalization.** The book asks for a consistent matrix norm. Consistency is not needed: any
two norms on $\mathbb{R}^{n \times n}$ differ by bounded factors, whose $m$-th roots tend to
$1$.

The real case uses the backbone theorem `Matrix.tendsto_pow_rpow_complexSpectralRadius` for the
spectral norm, transported to $N$ by `Seminorm.tendsto_rpow_one_div`. The complex case is
Mathlib's `spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`, in $[0, \infty]$. -/
theorem property_1_14 (N : Seminorm ℝ (Matrix (Fin n) (Fin n) ℝ)) (hN : ∀ M, N M = 0 → M = 0)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (fun m : ℕ => N (A ^ m) ^ (1 / m : ℝ)) atTop (𝓝 A.complexSpectralRadius.toReal) ∧
      Tendsto (fun m : ℕ => (‖B ^ m‖₊ : ℝ≥0∞) ^ (1 / m : ℝ)) atTop (𝓝 (spectralRadius ℂ B)) := by
  have _ : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
  exact ⟨N.tendsto_rpow_one_div hN (tendsto_pow_rpow_complexSpectralRadius A),
    spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius B⟩

end SpectralRadius

/-! ### §1.11.2 Sequences and series of matrices -/

section Sequences

variable {n : ℕ}

open scoped Matrix.Norms.Elementwise in
/-- **Section 1.11.2** of [quarteroni2000numerical], convergence of a sequence of matrices. A
sequence $A^{(k)}$ in $\mathbb{R}^{n \times n}$ converges to $A$ if
$\lim_{k \to \infty} \|A^{(k)} - A\| = 0$, and the choice of the norm does not influence the
result, since all norms on $\mathbb{R}^{n \times n}$ are equivalent. Precisely: for every matrix
norm $N$ on $\mathbb{R}^{n \times n}$, $A^{(k)} \to A$ in the topology of
$\mathbb{R}^{n \times n}$ if and only if $N(A^{(k)} - A) \to 0$. A matrix $A$ is **convergent**
if $A^k \to 0$. -/
theorem tendsto_iff_tendsto_seminorm (N : Seminorm ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hN : ∀ M, N M = 0 → M = 0) (M : ℕ → Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin n) ℝ) :
    Tendsto M atTop (𝓝 B) ↔ Tendsto (fun k => N (M k - B)) atTop (𝓝 0) := by
  rw [Seminorm.tendsto_apply_iff_tendsto_norm N hN fun k => M k - B]
  exact tendsto_iff_norm_sub_tendsto_zero

open scoped Matrix.Norms.L2Operator in
/-- **Theorem 1.5** of [quarteroni2000numerical], with (1.24). Let $n \ge 1$. For
$A \in \mathbb{R}^{n \times n}$,
$$\lim_{k \to \infty} A^k = 0 \iff \rho(A) < 1,$$
with the spectral radius of $A$ regarded as a complex matrix. The same holds for
$B \in \mathbb{C}^{n \times n}$.

The real case is the backbone theorem `Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one`. The
complex case is the backbone theorem `spectralRadius_lt_one_iff_tendsto_pow` in the Banach
algebra $\mathbb{C}^{n \times n}$. -/
theorem theorem_1_5 [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin n) ℂ) :
    (Tendsto (fun k => A ^ k) atTop (𝓝 0) ↔ A.complexSpectralRadius < 1) ∧
      (Tendsto (fun k => B ^ k) atTop (𝓝 0) ↔ spectralRadius ℂ B < 1) := by
  have _ : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
  exact ⟨tendsto_pow_iff_complexSpectralRadius_lt_one A,
    (spectralRadius_lt_one_iff_tendsto_pow B).symm⟩

open scoped Matrix.Norms.L2Operator in
/-- **Theorem 1.5** of [quarteroni2000numerical], with (1.25). Let $n \ge 1$ and
$A \in \mathbb{R}^{n \times n}$. The geometric series $\sum_{k \ge 0} A^k$ converges if and only
if $\rho(A) < 1$, with the spectral radius of $A$ regarded as a complex matrix. In this case
$I - A$ is invertible and
$$\sum_{k=0}^\infty A^k = (I - A)^{-1}.$$
The same holds for $B \in \mathbb{C}^{n \times n}$.

The real case uses the backbone theorems `Matrix.summable_pow_iff_complexSpectralRadius_lt_one`
and `Matrix.hasSum_pow_inv_one_sub_of_complexSpectralRadius_lt_one`. The complex case uses the
backbone theorems `summable_pow_iff_spectralRadius_lt_one` and
`hasSum_pow_inverse_one_sub_of_spectralRadius_lt_one`. -/
theorem theorem_1_5_series [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin n) ℂ) :
    ((Summable fun k => A ^ k) ↔ A.complexSpectralRadius < 1) ∧
      (A.complexSpectralRadius < 1 → IsUnit (1 - A) ∧ HasSum (fun k => A ^ k) (1 - A)⁻¹) ∧
      ((Summable fun k => B ^ k) ↔ spectralRadius ℂ B < 1) ∧
      (spectralRadius ℂ B < 1 → IsUnit (1 - B) ∧ HasSum (fun k => B ^ k) (1 - B)⁻¹) := by
  have _ : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
  refine ⟨summable_pow_iff_complexSpectralRadius_lt_one A,
    fun h => ⟨isUnit_one_sub_of_complexSpectralRadius_lt_one h,
      hasSum_pow_inv_one_sub_of_complexSpectralRadius_lt_one h⟩,
    summable_pow_iff_spectralRadius_lt_one B, fun h => ⟨isUnit_one_sub_of_spectralRadius_lt_one h,
      ?_⟩⟩
  rw [nonsing_inv_eq_ringInverse]
  exact hasSum_pow_inverse_one_sub_of_spectralRadius_lt_one h

/-- **Equation (1.26)** of [quarteroni2000numerical]. Let $n \ge 1$, let $\|\cdot\|$ be a vector
norm on $\mathbb{R}^n$ with induced matrix norm $|||\cdot|||$, and let
$A \in \mathbb{R}^{n \times n}$ with $|||A||| < 1$. Then $I - A$ is invertible and
$$\frac{1}{1 + |||A|||} \le |||(I - A)^{-1}||| \le \frac{1}{1 - |||A|||}.$$

The proof uses the backbone theorems `Matrix.isUnit_one_sub_of_inducedNorm_lt_one`,
`Matrix.one_div_one_add_le_inducedNorm_inv_one_sub` and `Matrix.inducedNorm_inv_one_sub_le`. -/
theorem equation_1_26 [NeZero n] {p : Seminorm ℝ (Fin n → ℝ)} (hp : ∀ x, p x = 0 → x = 0)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : inducedNorm p p A < 1) :
    IsUnit (1 - A) ∧ 1 / (1 + inducedNorm p p A) ≤ inducedNorm p p (1 - A)⁻¹ ∧
      inducedNorm p p (1 - A)⁻¹ ≤ 1 / (1 - inducedNorm p p A) :=
  ⟨isUnit_one_sub_of_inducedNorm_lt_one hp hA, one_div_one_add_le_inducedNorm_inv_one_sub hp hA,
    inducedNorm_inv_one_sub_le hp hA⟩

/-- **Remark 1.1** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ with
$\rho(A) < 1$, where $\rho(A)$ is the spectral radius of $A$ regarded as a complex matrix. By
Theorem 1.5 this is the case when $A$ is convergent. Then there is a vector norm on
$\mathbb{R}^n$ whose induced matrix norm satisfies $|||A||| < 1$. This justifies the assumption
of (1.26).

The proof applies Property 1.13 with $\varepsilon = (1 - \rho(A)) / 2$. -/
theorem remark_1_1 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.complexSpectralRadius < 1) :
    ∃ p : Seminorm ℝ (Fin n → ℝ), (∀ x, p x = 0 → x = 0) ∧ inducedNorm p p A < 1 := by
  have hρ : A.complexSpectralRadius.toReal < 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_strict_mono ENNReal.one_ne_top hA
  obtain ⟨p, hp, hle⟩ := exists_inducedNorm_le_complexSpectralRadius_add A
    (ε := (1 - A.complexSpectralRadius.toReal) / 2) (by linarith)
  exact ⟨p, hp, by linarith⟩

end Sequences

end QuarteroniSaccoSaleri.Chapter01
