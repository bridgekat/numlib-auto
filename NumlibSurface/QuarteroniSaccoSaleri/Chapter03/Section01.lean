/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Conditioning.LinearSystem.Componentwise
import Numlib.FloatingPoint.Stationary
import NumlibSurface.QuarteroniSaccoSaleri.Chapter01.Section11

/-!
# Quarteroni, Sacco and Saleri, Section 3.1: Stability Analysis of Linear Systems

This module formalizes Section 3.1 of [quarteroni2000numerical] on the sensitivity of a linear
system $Ax = b$ with a nonsingular $A \in \mathbb{R}^{n \times n}$ to perturbations of its data.
Section 3.1.1 defines the condition number $K_p(A) = \|A\|_p \|A^{-1}\|_p$ (3.4) and gives its basic
properties, the spectral condition number $K_2(A) = \sigma_1(A) / \sigma_n(A)$, and Kahan's formula
(3.6): the relative distance from $A$ to the singular matrices is $1 / K_p(A)$. Section 3.1.2 bounds
the error $\delta x$ of the perturbed system $(A + \delta A)(x + \delta x) = b + \delta b$, first in
norm (Theorems 3.1–3.3), then componentwise ((3.15)–(3.16) and Example 3.1). Section 3.1.3 analyses
an approximate inverse $C$ through the residual $R = AC - I$ (Property 3.1 and (3.19)). Section
3.1.4 gives a posteriori bounds in terms of the residual $r = b - Ay$ of an approximate solution $y$
((3.20), (3.21) and the LAPACK estimate).

The proofs specialize the backbone modules `Numlib.Analysis.Normed.Ring.CondNumber` (the condition
number $\|a\| \|a^{-1}\|$ in a normed ring), `Numlib.Analysis.Matrix.OperatorNorm` (the induced
$p$-norms and the spectral condition number of orthogonal and positive definite matrices),
`Numlib.LinearAlgebra.Matrix.SVD` (the singular values), `Numlib.Conditioning.LinearSystem` (the
normwise perturbation theory) and `Numlib.Conditioning.LinearSystem.Componentwise` (the
componentwise theory, the Skeel condition number and the bound with a computed residual).

## Main definitions

* Equation (3.4), `QuarteroniSaccoSaleri.Chapter03.condNumber`: the condition number
  $K_p(A) = \|A\|_p \|A^{-1}\|_p$.
* Example 3.1, `QuarteroniSaccoSaleri.Chapter03.example_3_1_matrix`: the matrix $\begin{bmatrix}
  \alpha & 1/\alpha \\ 0 & 1/\alpha \end{bmatrix}$.

## Main results

* Section 3.1.1, `QuarteroniSaccoSaleri.Chapter03.one_le_condNumber`: $K(A) \ge 1$.
* Section 3.1.1, `QuarteroniSaccoSaleri.Chapter03.condNumber_inv`: $K(A^{-1}) = K(A)$.
* Section 3.1.1, `QuarteroniSaccoSaleri.Chapter03.condNumber_smul`: $K(\alpha A) = K(A)$ for
  $\alpha \neq 0$.
* Section 3.1.1, `QuarteroniSaccoSaleri.Chapter03.condNumber_two_of_orthogonal`: $K_2(A) = 1$ for an
  orthogonal $A$.
* Section 3.1.1, `QuarteroniSaccoSaleri.Chapter03.condNumber_two_eq_div_singularValues`:
  $K_2(A) = \sigma_1(A) / \sigma_n(A)$.
* Equation (3.5), `QuarteroniSaccoSaleri.Chapter03.equation_3_5`: $K_2(A) = \lambda_{max} /
  \lambda_{min} = \rho(A) \rho(A^{-1})$ for a symmetric positive definite $A$.
* Remark 3.1, `QuarteroniSaccoSaleri.Chapter03.remark_3_1`: Kahan's formula (3.6) for the distance
  to singularity.
* Equation (3.7), `QuarteroniSaccoSaleri.Chapter03.equation_3_7`: $\|\delta A\| \|A^{-1}\| < 1$
  implies that $A + \delta A$ is nonsingular.
* Theorem 3.1, `QuarteroniSaccoSaleri.Chapter03.theorem_3_1`: the normwise bound (3.9) on
  $\|\delta x\| / \|x\|$.
* Theorem 3.2, `QuarteroniSaccoSaleri.Chapter03.theorem_3_2` and
  `QuarteroniSaccoSaleri.Chapter03.theorem_3_2_lower`: the two inequalities (3.11) for
  $\delta A = 0$.
* Theorem 3.3, `QuarteroniSaccoSaleri.Chapter03.theorem_3_3_sum` and
  `QuarteroniSaccoSaleri.Chapter03.theorem_3_3`: the bounds (3.12) and (3.13) for perturbations of
  relative size $\gamma$.
* Equation (3.15), `QuarteroniSaccoSaleri.Chapter03.equation_3_15`: the componentwise relative error
  bounds in the $\infty$-norm.
* Equation (3.16), `QuarteroniSaccoSaleri.Chapter03.equation_3_16_a` and
  `QuarteroniSaccoSaleri.Chapter03.equation_3_16_b`: the bounds on the components $|\delta x_i|$.
* Example 3.1, `QuarteroniSaccoSaleri.Chapter03.example_3_1`: equation (3.17), a matrix with
  unbounded $\| |A^{-1}| |A| \|_\infty$ and a well-conditioned largest component.
* Property 3.1, `QuarteroniSaccoSaleri.Chapter03.property_3_1_isUnit`,
  `QuarteroniSaccoSaleri.Chapter03.property_3_1_inv` and
  `QuarteroniSaccoSaleri.Chapter03.property_3_1_sub`: if $\|AC - I\| < 1$, then $A$ and $C$ are
  nonsingular, with the bounds (3.18).
* Equation (3.19), `QuarteroniSaccoSaleri.Chapter03.equation_3_19`: the bound on $\delta A$ when $C$
  is the inverse of $A + \delta A$.
* Equation (3.20), `QuarteroniSaccoSaleri.Chapter03.equation_3_20`:
  $\|e\| \le \|r\| \|C\| / (1 - \|R\|)$.
* Equation (3.21), `QuarteroniSaccoSaleri.Chapter03.equation_3_21`:
  $\|e\| / \|x\| \le K(A) \|r\| / \|b\|$.
* Section 3.1.4, `QuarteroniSaccoSaleri.Chapter03.computedResidualErrorBound`: the LAPACK estimate
  with a computed residual.

## Conventions

* The book's $K(A) = \|A\| \|A^{-1}\|$ "for an induced matrix norm" (3.4) is stated for the norm
  $\|\cdot\|_p$ induced by the vector $p$-norm, $1 \le p \le \infty$. The matrix norm $\|A\|_p$ is
  `Matrix.lpOpNorm p A`, and the vector norm $\|x\|_p$ is `‖toLp p x‖`, as in Chapter 1.
* Where the book fixes $p = \infty$ (the componentwise estimates of Section 3.1.2 and the LAPACK
  estimate of Section 3.1.4), the vector norm $\|x\|_\infty$ is the sup norm `‖x‖` of `Fin n → ℝ`.
  The matrix norm $\|A\|_\infty$, the maximum absolute row sum, is Mathlib's scoped
  `Matrix.Norms.Operator` norm, which `Matrix.lpOpNorm_top` identifies with `Matrix.lpOpNorm ⊤`.
* The entrywise absolute value $|A|$ is `Matrix.abs A`, and the entrywise order of Section 3.1.2 is
  `Matrix.EntrywiseLE`, written `C ≤ₑ D`. Both come from `Numlib.LinearAlgebra.Matrix.Order`.
* The perturbed system (3.8) is the hypothesis `(A + δA) *ᵥ (x + δx) = b + δb`, where $\delta x$ is
  the perturbation of the solution $x$ of $Ax = b$.
* The matrices of the book have positive order. This is the hypothesis `[NeZero n]` of the
  statements that need a nontrivial space.

## Implementation notes

* In Mathlib $A^{-1} = 0$ for a singular $A$, so `QuarteroniSaccoSaleri.Chapter03.condNumber p A` is
  $0$ where the book says $\infty$. Every statement assumes $A$ nonsingular, as the book does.
* The condition number is the backbone's `Matrix.condNumberLp p A`
  (`QuarteroniSaccoSaleri.Chapter03.condNumber_eq_condNumberLp`), and it is `NormedRing.condNumber`
  of the operator $x \mapsto Ax$ on `PiLp p (Fin n → ℝ)`
  (`QuarteroniSaccoSaleri.Chapter03.condNumber_eq`). The operator theorems of the backbone reach
  matrices in this way.

## Deviations from the source

* **Equation (3.7)** (correction). The book prints $\|\delta A\|_p \|A\|_p < 1$ and says that it
  follows from the nonsingularity of $A + \delta A$. The statement is:
  $\|\delta A\|_p \|A^{-1}\|_p < 1$ implies that $A + \delta A$ is nonsingular. See
  `QuarteroniSaccoSaleri.Chapter03.equation_3_7`.
* **Theorem 3.1** (correction). The hypothesis (3.7) is the corrected condition
  $\|\delta A\| \|A^{-1}\| < 1$. See `QuarteroniSaccoSaleri.Chapter03.theorem_3_1`.
* **Equation (3.15)** (typo). The second line prints $\|A^{-1} | |A| \|_\infty$ for
  $\| |A^{-1}| |A| \|_\infty$. See `QuarteroniSaccoSaleri.Chapter03.equation_3_15`.
* **Example 3.1** (generalization). The book takes $0 < \alpha < 1$. The identities hold for every
  $\alpha > 0$. See `QuarteroniSaccoSaleri.Chapter03.example_3_1`.
* **Equation (3.19)** (correction). The roles of $A$ and $C$ in the hypothesis are interchanged: the
  residual that has to be small is $R = CA - I$. See
  `QuarteroniSaccoSaleri.Chapter03.equation_3_19`.
-/

open Finset Matrix WithLp
open scoped ENNReal NNReal

namespace QuarteroniSaccoSaleri.Chapter03

variable {n : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-! ### §3.1.1: the condition number of a matrix -/

/-- **Equation (3.4)** of [quarteroni2000numerical]. Let $1 \le p \le \infty$ and
$A \in \mathbb{R}^{n \times n}$. The **condition number** of $A$ in the matrix norm induced by
the vector $p$-norm is
$$K_p(A) = \|A\|_p \, \|A^{-1}\|_p.$$
The cases $p = 1, 2, \infty$ are the important instances.

The matrix norm $\|A\|_p$ is `Matrix.lpOpNorm p A`. In Mathlib $A^{-1} = 0$ for a singular $A$,
so the value is then $0$ rather than the $\infty$ of the book; every statement about it assumes
$A$ nonsingular. The definition is the backbone's `Matrix.condNumberLp p A`. -/
noncomputable def condNumber (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  lpOpNorm p A * lpOpNorm p A⁻¹

/-- The condition number $K_p(A)$ of (3.4) of [quarteroni2000numerical] is the backbone's
`Matrix.condNumberLp p A`. -/
theorem condNumber_eq_condNumberLp (A : Matrix (Fin n) (Fin n) ℝ) :
    condNumber p A = condNumberLp p A := rfl

/-- The condition number $K_p(A)$ of (3.4) of [quarteroni2000numerical] is the condition number
`NormedRing.condNumber` of the operator $x \mapsto Ax$ on $\mathbb{R}^n$ with the $p$-norm,
`Matrix.lpCLM p A` on `PiLp p (Fin n → ℝ)`. The operator theorems of the backbone reach matrices
in this way. -/
theorem condNumber_eq (A : Matrix (Fin n) (Fin n) ℝ) :
    condNumber p A = NormedRing.condNumber (lpCLM p A) :=
  condNumberLp_eq_condNumber p A

variable {p}

/-- **Section 3.1.1** of [quarteroni2000numerical], $K(A) \ge 1$. Let $n \ge 1$ and let
$A \in \mathbb{R}^{n \times n}$ be nonsingular. Then
$$1 = \|A A^{-1}\|_p \le \|A\|_p \|A^{-1}\|_p = K_p(A).$$

The proof is the backbone's `Matrix.one_le_condNumberLp`, through
`NormedRing.one_le_condNumber`. -/
theorem one_le_condNumber [NeZero n] {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) :
    1 ≤ condNumber p A :=
  one_le_condNumberLp p hA

/-- **Section 3.1.1** of [quarteroni2000numerical], $K(A^{-1}) = K(A)$. For every
$A \in \mathbb{R}^{n \times n}$, $K_p(A^{-1}) = K_p(A)$.

For a singular $A$ both sides are $0$. The proof is the backbone's
`NormedRing.condNumber_inverse`. -/
theorem condNumber_inv (A : Matrix (Fin n) (Fin n) ℝ) : condNumber p A⁻¹ = condNumber p A := by
  rw [condNumber_eq, condNumber_eq, ← ringInverse_lpCLM, NormedRing.condNumber_inverse]

/-- **Section 3.1.1** of [quarteroni2000numerical], $K(\alpha A) = K(A)$. For every
$A \in \mathbb{R}^{n \times n}$ and every $\alpha \in \mathbb{R}$ with $\alpha \neq 0$,
$K_p(\alpha A) = K_p(A)$.

The proof is the backbone's `Matrix.condNumberLp_smul`. -/
theorem condNumber_smul {α : ℝ} (hα : α ≠ 0) (A : Matrix (Fin n) (Fin n) ℝ) :
    condNumber p (α • A) = condNumber p A :=
  condNumberLp_smul p hα A

open scoped Matrix.Norms.L2Operator in
/-- The condition number $K_2(A)$ of (3.4) of [quarteroni2000numerical] is `NormedRing.condNumber A`
for Mathlib's scoped `Matrix.Norms.L2Operator` norm on matrices, the form in which the backbone
states the spectral condition number. -/
theorem condNumber_two_eq (A : Matrix (Fin n) (Fin n) ℝ) :
    condNumber 2 A = NormedRing.condNumber A := by
  rw [condNumber, lpOpNorm_two, lpOpNorm_two, NormedRing.condNumber, nonsing_inv_eq_ringInverse]

open scoped Matrix.Norms.L2Operator in
/-- **Section 3.1.1** of [quarteroni2000numerical], orthogonal matrices. Let $n \ge 1$ and let
$A \in \mathbb{R}^{n \times n}$ be orthogonal. Then $K_2(A) = 1$, because $\|A\|_2 =
\sqrt{\rho(A^T A)} = \sqrt{\rho(I)} = 1$ and $A^{-1} = A^T$.

The orthogonal matrices are `Matrix.orthogonalGroup (Fin n) ℝ`. The proof is the backbone's
`Matrix.condNumber_l2_of_mem_unitaryGroup`, since the orthogonal group is the real unitary
group. -/
theorem condNumber_two_of_orthogonal [NeZero n] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A ∈ orthogonalGroup (Fin n) ℝ) : condNumber 2 A = 1 := by
  rw [condNumber_two_eq]
  exact condNumber_l2_of_mem_unitaryGroup hA

open scoped Matrix.Norms.L2Operator in
/-- **Section 3.1.1** of [quarteroni2000numerical], the spectral condition number. Let $n \ge 1$ and
let $A \in \mathbb{R}^{n \times n}$ be nonsingular. Then
$$K_2(A) = \|A\|_2 \|A^{-1}\|_2 = \frac{\sigma_1(A)}{\sigma_n(A)},$$
the ratio of the largest and the smallest singular values of $A$.

The singular values are `Matrix.colSingularValues A`, indexed by the columns of $A$ in no
particular order, so $\sigma_1(A)$ and $\sigma_n(A)$ are their supremum and infimum. The proof
is the backbone's `Matrix.condNumber_l2_eq_div_colSingularValues`. -/
theorem condNumber_two_eq_div_singularValues [NeZero n] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsUnit A) :
    condNumber 2 A = (⨆ i, A.colSingularValues i) / ⨅ i, A.colSingularValues i := by
  rw [condNumber_two_eq]
  exact condNumber_l2_eq_div_colSingularValues A ((isUnit_iff_isUnit_det A).mp hA)

open scoped Matrix.Norms.L2Operator in
/-- **Equation (3.5)** of [quarteroni2000numerical]. Let $n \ge 1$ and let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite. Then
$$K_2(A) = \frac{\lambda_{max}}{\lambda_{min}} = \rho(A) \, \rho(A^{-1}),$$
where $\lambda_{max}$ and $\lambda_{min}$ are the largest and the smallest eigenvalues of $A$,
and $\rho$ is the spectral radius.

The eigenvalues are `Matrix.IsHermitian.eigenvalues` of `hA.1`, and $\rho$ is
`Matrix.complexSpectralRadius`, converted to a real number. The proof is the backbone's
`Matrix.PosDef.condNumber_l2_eq_div_eigenvalues`, with $\|A\|_2 = \rho(A)$ for a symmetric
matrix (`Matrix.l2_opNorm_eq_complexSpectralRadius_of_isHermitian`). -/
theorem equation_3_5 [NeZero n] {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    condNumber 2 A = (⨆ i, hA.1.eigenvalues i) / ⨅ i, hA.1.eigenvalues i ∧
      condNumber 2 A = (complexSpectralRadius A).toReal * (complexSpectralRadius A⁻¹).toReal := by
  refine ⟨by rw [condNumber_two_eq]; exact hA.condNumber_l2_eq_div_eigenvalues, ?_⟩
  rw [condNumber, lpOpNorm_two, lpOpNorm_two,
    l2_opNorm_eq_complexSpectralRadius_of_isHermitian hA.1,
    l2_opNorm_eq_complexSpectralRadius_of_isHermitian hA.1.inv]

/-! ### Remark 3.1: the distance to singularity, and (3.7) -/

/-- Every continuous linear operator on $\mathbb{R}^n$ with the $p$-norm is the operator
$x \mapsto Mx$ of a matrix $M \in \mathbb{R}^{n \times n}$. This is used for Remark 3.1 of
[quarteroni2000numerical].

The proof is the surjectivity of the backbone's linear equivalence `Matrix.lpCLMEquiv`. -/
theorem exists_lpCLM_eq (t : PiLp p (fun _ : Fin n => ℝ) →L[ℝ] PiLp p (fun _ : Fin n => ℝ)) :
    ∃ M : Matrix (Fin n) (Fin n) ℝ, lpCLM p M = t :=
  (lpCLMEquiv p).surjective t

/-- **Remark 3.1** of [quarteroni2000numerical], equation (3.6) (Kahan). Let $n \ge 1$ and let
$A \in \mathbb{R}^{n \times n}$ be nonsingular. The relative distance of $A$ from the set of
singular matrices in the $p$-norm,
$$\operatorname{dist}_p(A) = \min \Bigl\{ \frac{\|\delta A\|_p}{\|A\|_p} : A + \delta A \text{
  is singular} \Bigr\},$$
is attained, and it equals $1 / K_p(A)$.

The statement is `IsLeast` for the set of these ratios. The proof is the backbone's
`ContinuousLinearEquiv.isLeast_dist_singular` for the operator $x \mapsto Ax$ on
`PiLp p (Fin n → ℝ)`. -/
theorem remark_3_1 [NeZero n] {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) :
    IsLeast {r | ∃ δA : Matrix (Fin n) (Fin n) ℝ,
        ¬ IsUnit (A + δA) ∧ lpOpNorm p δA / lpOpNorm p A = r}
      (1 / condNumber p A) := by
  have h := (lpEquiv p hA).isLeast_dist_singular
  rw [← ContinuousLinearEquiv.condNumber_coe, coe_lpEquiv, ← condNumber_eq] at h
  convert h using 1
  ext r
  constructor
  · rintro ⟨δA, hδA, rfl⟩
    refine ⟨lpCLM p δA, ?_, rfl⟩
    rwa [← lpCLM_add, isUnit_lpCLM_iff]
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨δA, rfl⟩ := exists_lpCLM_eq t
    refine ⟨δA, ?_, rfl⟩
    rwa [← lpCLM_add, isUnit_lpCLM_iff] at ht

/-- For $n \ge 1$ and a nonsingular $A \in \mathbb{R}^{n \times n}$, $\|A\|_p > 0$ and
$\|A^{-1}\|_p > 0$, because $1 \le K_p(A)$. -/
private theorem lpOpNorm_pos_of_isUnit [NeZero n] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsUnit A) : 0 < lpOpNorm p A ∧ 0 < lpOpNorm p A⁻¹ := by
  have h1 := one_le_condNumberLp p hA
  rw [condNumberLp] at h1
  refine ⟨(lpOpNorm_nonneg p A).lt_of_ne fun h => ?_,
    (lpOpNorm_nonneg p A⁻¹).lt_of_ne fun h => ?_⟩
  · rw [← h, zero_mul] at h1; norm_num at h1
  · rw [← h, mul_zero] at h1; norm_num at h1

/-- A nonzero vector of $\mathbb{R}^n$ forces $n \neq 0$. -/
private theorem neZero_of_ne_zero {b : Fin n → ℝ} (hb : b ≠ 0) : NeZero n :=
  ⟨fun h => hb (by subst h; exact Subsingleton.elim _ _)⟩

/-- **Equation (3.7)** of [quarteroni2000numerical]. Let $A, \delta A \in \mathbb{R}^{n \times n}$
with $A$ nonsingular. If $\|\delta A\|_p \|A^{-1}\|_p < 1$, then $A + \delta A$ is nonsingular:
the relative perturbation is below the distance $1 / K_p(A)$ to singularity of (3.6).

**Correction.** The book prints the condition $\|\delta A\|_p \|A\|_p < 1$ and says that it
follows from the nonsingularity of $A + \delta A$. Both are wrong. For $A = I$ and
$\delta A = A$, the matrix $A + \delta A = 2I$ is nonsingular but $\|\delta A\|_p \|A\|_p = 1$.
For $A = \varepsilon I$ with $0 < \varepsilon < 1$ and $\delta A = -A$,
$\|\delta A\|_p \|A\|_p = \varepsilon^2 < 1$ but $A + \delta A = 0$ is singular. The proof of
Theorem 3.1 uses (3.7) as "$A^{-1} \delta A$ has norm less than $1$", which is the condition
stated here, and which Kahan's formula (3.6) gives.

The proof is the backbone's `NormedRing.norm_le_of_not_isUnit_add`, the lower half of Kahan's
formula. -/
theorem equation_3_7 {A δA : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A)
    (h : lpOpNorm p δA * lpOpNorm p A⁻¹ < 1) : IsUnit (A + δA) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact isUnit_of_subsingleton _
  have : NeZero n := ⟨hn.ne'⟩
  by_contra hne
  rw [← isUnit_lpCLM_iff p, lpCLM_add] at hne
  have hle := NormedRing.norm_le_of_not_isUnit_add ((isUnit_lpCLM_iff p A).mpr hA) hne
  rw [ringInverse_lpCLM] at hle
  have hpos := (lpOpNorm_pos_of_isUnit (p := p) hA).2
  have h1 : 1 ≤ lpOpNorm p δA * lpOpNorm p A⁻¹ := by
    rw [← div_le_iff₀ hpos, one_div]
    exact hle
  exact absurd h (not_lt.mpr h1)

/-! ### §3.1.2: forward a priori analysis, Theorems 3.1–3.3 -/

section Forward

variable {A δA : Matrix (Fin n) (Fin n) ℝ} {b δb x δx : Fin n → ℝ}

/-- **Theorem 3.1** of [quarteroni2000numerical], equation (3.9). Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular, and let $\delta A \in \mathbb{R}^{n \times n}$
satisfy (3.7), $\|\delta A\| \|A^{-1}\| < 1$, in the norm induced by the vector $p$-norm. Let
$x$ solve $Ax = b$ with $b \neq 0$, and let $\delta x$ and $\delta b$ satisfy the perturbed
system (3.8), $(A + \delta A)(x + \delta x) = b + \delta b$. Then
$$\frac{\|\delta x\|}{\|x\|} \le \frac{K(A)}{1 - K(A) \|\delta A\| / \|A\|} \Bigl(
  \frac{\|\delta b\|}{\|b\|} + \frac{\|\delta A\|}{\|A\|} \Bigr).$$

**Correction.** The hypothesis of the book is (3.7) as printed, $\|\delta A\| \|A\| < 1$. The
statement assumes the corrected condition $\|\delta A\| \|A^{-1}\| < 1$; see
`QuarteroniSaccoSaleri.Chapter03.equation_3_7`.

All norms are $p$-norms. The proof is the backbone's `relative_error_le_condNumber` for the
operator on `PiLp p (Fin n → ℝ)`, whose denominator $1 - \|A^{-1}\| \|\delta A\|$ is the
denominator $1 - K(A) \|\delta A\| / \|A\|$ of the book. -/
theorem theorem_3_1 (hA : IsUnit A) (hδA : lpOpNorm p δA * lpOpNorm p A⁻¹ < 1)
    (hx : A *ᵥ x = b) (hb : b ≠ 0) (hδx : (A + δA) *ᵥ (x + δx) = b + δb) :
    ‖toLp p δx‖ / ‖toLp p x‖ ≤
      condNumber p A / (1 - condNumber p A * (lpOpNorm p δA / lpOpNorm p A)) *
        (‖toLp p δb‖ / ‖toLp p b‖ + lpOpNorm p δA / lpOpNorm p A) := by
  have := neZero_of_ne_zero hb
  have hApos := (lpOpNorm_pos_of_isUnit (p := p) hA).1
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hb (by rw [← hx, mulVec_zero])
  have h := relative_error_le_condNumber (lpEquiv p hA) (lpCLM p δA) (b := toLp p b)
    (Δb := toLp p δb) (x := toLp p x) (y := toLp p (x + δx))
    (by rw [lpEquiv_apply, ofLp_toLp, hx])
    (by rw [coe_lpEquiv, ← lpCLM_add, lpCLM_apply, ofLp_toLp, hδx, toLp_add])
    (by rw [coe_lpEquiv_symm, mul_comm]; exact hδA)
    (by rwa [Ne, toLp_eq_zero]) (by rwa [Ne, toLp_eq_zero])
  rw [coe_lpEquiv, coe_lpEquiv_symm, ← condNumber_eq, ← toLp_sub, add_sub_cancel_left] at h
  have e : condNumber p A * (lpOpNorm p δA / lpOpNorm p A) = lpOpNorm p A⁻¹ * lpOpNorm p δA := by
    rw [condNumber]
    field_simp
  rw [e, add_comm]
  exact h

/-- **Theorem 3.2** of [quarteroni2000numerical], the upper inequality of (3.11). Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular, let $Ax = b$ with $b \neq 0$, and let
$A(x + \delta x) = b + \delta b$. Then
$$\frac{\|\delta x\|}{\|x\|} \le K(A) \, \frac{\|\delta b\|}{\|b\|}.$$

This is the case $\delta A = 0$ of Theorem 3.1. The proof is the backbone's
`ContinuousLinearEquiv.relative_error_le_condNumber_mul_relative_residual`. -/
theorem theorem_3_2 (hA : IsUnit A) (hx : A *ᵥ x = b) (hb : b ≠ 0)
    (hδx : A *ᵥ (x + δx) = b + δb) :
    ‖toLp p δx‖ / ‖toLp p x‖ ≤ condNumber p A * (‖toLp p δb‖ / ‖toLp p b‖) := by
  have h := (lpEquiv p hA).relative_error_le_condNumber_mul_relative_residual (v := toLp p x)
    (v' := toLp p (x + δx)) (w := toLp p b) (w' := toLp p (b + δb))
    (by rw [lpEquiv_apply, ofLp_toLp, hx]) (by rw [lpEquiv_apply, ofLp_toLp, hδx])
    (by rwa [Ne, toLp_eq_zero])
  rwa [← ContinuousLinearEquiv.condNumber_coe, coe_lpEquiv, ← condNumber_eq, ← toLp_sub,
    ← toLp_sub, sub_add_cancel_left, sub_add_cancel_left, toLp_neg, toLp_neg, norm_neg,
    norm_neg] at h

/-- **Theorem 3.2** of [quarteroni2000numerical], the lower inequality of (3.11). Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular, let $Ax = b$ with $b \neq 0$, and let
$A(x + \delta x) = b + \delta b$. Then
$$\frac{1}{K(A)} \, \frac{\|\delta b\|}{\|b\|} \le \frac{\|\delta x\|}{\|x\|}.$$

The proof is the backbone's
`ContinuousLinearEquiv.relative_residual_le_condNumber_mul_relative_error`, divided by
$K(A) \ge 1$. -/
theorem theorem_3_2_lower (hA : IsUnit A) (hx : A *ᵥ x = b) (hb : b ≠ 0)
    (hδx : A *ᵥ (x + δx) = b + δb) :
    1 / condNumber p A * (‖toLp p δb‖ / ‖toLp p b‖) ≤ ‖toLp p δx‖ / ‖toLp p x‖ := by
  have := neZero_of_ne_zero hb
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hb (by rw [← hx, mulVec_zero])
  have h := (lpEquiv p hA).relative_residual_le_condNumber_mul_relative_error (v := toLp p x)
    (v' := toLp p (x + δx)) (w := toLp p b) (w' := toLp p (b + δb))
    (by rw [lpEquiv_apply, ofLp_toLp, hx]) (by rw [lpEquiv_apply, ofLp_toLp, hδx])
    (by rwa [Ne, toLp_eq_zero])
  rw [← ContinuousLinearEquiv.condNumber_coe, coe_lpEquiv, ← condNumber_eq, ← toLp_sub,
    ← toLp_sub, sub_add_cancel_left, sub_add_cancel_left, toLp_neg, toLp_neg, norm_neg,
    norm_neg] at h
  rw [one_div, inv_mul_le_iff₀ (zero_lt_one.trans_le (one_le_condNumber hA))]
  exact h

/-- **Theorem 3.3** of [quarteroni2000numerical], equation (3.13). Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular, let $Ax = b$ with $b \neq 0$, and let
$(A + \delta A)(x + \delta x) = b + \delta b$. Let $\gamma \in \mathbb{R}$ satisfy
$\|\delta A\| \le \gamma \|A\|$, $\|\delta b\| \le \gamma \|b\|$ and $\gamma K(A) < 1$. Then
$$\frac{\|\delta x\|}{\|x\|} \le \frac{2 \gamma}{1 - \gamma K(A)} \, K(A).$$

All norms are $p$-norms. The proof is the backbone's `relative_error_le_of_norm_le_mul`. -/
theorem theorem_3_3 (hA : IsUnit A) (hx : A *ᵥ x = b) (hb : b ≠ 0)
    (hδx : (A + δA) *ᵥ (x + δx) = b + δb) {γ : ℝ} (hδA : lpOpNorm p δA ≤ γ * lpOpNorm p A)
    (hδb : ‖toLp p δb‖ ≤ γ * ‖toLp p b‖) (hγ : γ * condNumber p A < 1) :
    ‖toLp p δx‖ / ‖toLp p x‖ ≤ 2 * γ / (1 - γ * condNumber p A) * condNumber p A := by
  have h := relative_error_le_of_norm_le_mul (lpEquiv p hA) (lpCLM p δA) (b := toLp p b)
    (Δb := toLp p δb) (x := toLp p x) (y := toLp p (x + δx))
    (by rw [lpEquiv_apply, ofLp_toLp, hx])
    (by rw [coe_lpEquiv, ← lpCLM_add, lpCLM_apply, ofLp_toLp, hδx, toLp_add])
    (by rw [coe_lpEquiv]; exact hδA) hδb (by rw [coe_lpEquiv, ← condNumber_eq]; exact hγ)
    (by rwa [Ne, toLp_eq_zero])
  rwa [coe_lpEquiv, ← condNumber_eq, ← toLp_sub, add_sub_cancel_left] at h

/-- **Theorem 3.3** of [quarteroni2000numerical], equation (3.12). Under the hypotheses of
`QuarteroniSaccoSaleri.Chapter03.theorem_3_3`,
$$\frac{\|x + \delta x\|}{\|x\|} \le \frac{1 + \gamma K(A)}{1 - \gamma K(A)}.$$

The proof is the backbone's `norm_add_div_le_of_norm_le_mul`. -/
theorem theorem_3_3_sum (hA : IsUnit A) (hx : A *ᵥ x = b) (hb : b ≠ 0)
    (hδx : (A + δA) *ᵥ (x + δx) = b + δb) {γ : ℝ} (hδA : lpOpNorm p δA ≤ γ * lpOpNorm p A)
    (hδb : ‖toLp p δb‖ ≤ γ * ‖toLp p b‖) (hγ : γ * condNumber p A < 1) :
    ‖toLp p (x + δx)‖ / ‖toLp p x‖ ≤ (1 + γ * condNumber p A) / (1 - γ * condNumber p A) := by
  have h := norm_add_div_le_of_norm_le_mul (lpEquiv p hA) (lpCLM p δA) (b := toLp p b)
    (Δb := toLp p δb) (x := toLp p x) (y := toLp p (x + δx))
    (by rw [lpEquiv_apply, ofLp_toLp, hx])
    (by rw [coe_lpEquiv, ← lpCLM_add, lpCLM_apply, ofLp_toLp, hδx, toLp_add])
    (by rw [coe_lpEquiv]; exact hδA) hδb (by rw [coe_lpEquiv, ← condNumber_eq]; exact hγ)
    (by rwa [Ne, toLp_eq_zero])
  rwa [coe_lpEquiv, ← condNumber_eq] at h

end Forward

/-! ### §3.1.2: the componentwise estimates (3.15)–(3.16) and Example 3.1 -/

section Componentwise

open scoped Matrix.Norms.Operator

variable {A δA : Matrix (Fin n) (Fin n) ℝ} {b δb x δx : Fin n → ℝ}

/-- **Equation (3.15)** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ be
nonsingular, let $Ax = b$ with $b \neq 0$, and let
$(A + \delta A)(x + \delta x) = b + \delta b$. Let $\gamma \ge 0$ satisfy
$|\delta A| \le \gamma |A|$ and $|\delta b| \le \gamma |b|$ entrywise, and
$\gamma \, \| |A^{-1}| |A| \|_\infty < 1$. Then
$$\frac{\|\delta x\|_\infty}{\|x\|_\infty} \le \frac{\gamma \, \| |A^{-1}| |A| |x| + |A^{-1}|
  |b| \|_\infty}{(1 - \gamma \, \| |A^{-1}| |A| \|_\infty) \, \|x\|_\infty}$$
and
$$\frac{\|\delta x\|_\infty}{\|x\|_\infty} \le \frac{2 \gamma}{1 - \gamma \, \| |A^{-1}| |A|
  \|_\infty} \, \| |A^{-1}| |A| \|_\infty.$$

**Typo.** The second line of (3.15) in the book prints $\|A^{-1} | |A| \|_\infty$. The intended
quantity is $\| |A^{-1}| |A| \|_\infty$, the Skeel condition number `Matrix.skeelCond A`.

The proof is the backbone's `Matrix.norm_sub_le_of_abs_le_abs`, which is Theorem 7.4 of
[higham2002accuracy] with $E = |A|$ and $f = |b|$. -/
theorem equation_3_15 (hA : IsUnit A) (hx : A *ᵥ x = b) (hb : b ≠ 0)
    (hδx : (A + δA) *ᵥ (x + δx) = b + δb) {γ : ℝ} (hγ : 0 ≤ γ) (hδA : δA.abs ≤ₑ γ • A.abs)
    (hδb : |δb| ≤ γ • |b|) (hsmall : γ * ‖A⁻¹.abs * A.abs‖ < 1) :
    ‖δx‖ / ‖x‖ ≤ γ * ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|) + A⁻¹.abs *ᵥ |b|‖ /
        ((1 - γ * ‖A⁻¹.abs * A.abs‖) * ‖x‖) ∧
      ‖δx‖ / ‖x‖ ≤ 2 * γ / (1 - γ * ‖A⁻¹.abs * A.abs‖) * ‖A⁻¹.abs * A.abs‖ := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hb (by rw [← hx, mulVec_zero])
  have h := norm_sub_le_of_abs_le_abs hA hx hδx hγ hδA hδb hsmall hx0
  rwa [add_sub_cancel_left] at h

/-- **Equation (3.16)** of [quarteroni2000numerical], the case $\delta b = 0$. Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular, let $Ax = b$ and
$(A + \delta A)(x + \delta x) = b$, and let $\gamma \in \mathbb{R}$ satisfy
$|\delta A| \le \gamma |A|$ entrywise. Then for every $i$,
$$|\delta x_i| \le \gamma \, |r_{(i)}^T| \, |A| \, |x + \delta x|,$$
where $r_{(i)}^T = e_i^T A^{-1}$ is the $i$-th row of $A^{-1}$.

The proof is the backbone's `Matrix.abs_sub_apply_le_of_abs_le_abs`. -/
theorem equation_3_16_a (hA : IsUnit A) (hx : A *ᵥ x = b) (hδx : (A + δA) *ᵥ (x + δx) = b)
    {γ : ℝ} (hδA : δA.abs ≤ₑ γ • A.abs) (i : Fin n) :
    |δx i| ≤ γ * (|A⁻¹ i| ⬝ᵥ (A.abs *ᵥ |x + δx|)) := by
  have h := abs_sub_apply_le_of_abs_le_abs hA hx hδx hδA i
  rwa [Pi.add_apply, add_sub_cancel_left] at h

/-- **Equation (3.16)** of [quarteroni2000numerical], the case $\delta A = 0$. Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular, let $Ax = b$ and
$A(x + \delta x) = b + \delta b$, and let $\gamma \in \mathbb{R}$ satisfy
$|\delta b| \le \gamma |b|$ entrywise. Then for every $i$,
$$\frac{|\delta x_i|}{|x_i|} \le \gamma \, \frac{|r_{(i)}^T| \, |b|}{|r_{(i)}^T b|},$$
where $r_{(i)}^T = e_i^T A^{-1}$ is the $i$-th row of $A^{-1}$.

Here $r_{(i)}^T b = x_i$. If $x_i = 0$, both sides are $0$, because a division by $0$ gives $0$
in Lean. The proof is the backbone's `Matrix.abs_sub_apply_div_le_of_abs_le_abs`. -/
theorem equation_3_16_b (hA : IsUnit A) (hx : A *ᵥ x = b) (hδx : A *ᵥ (x + δx) = b + δb)
    {γ : ℝ} (hδb : |δb| ≤ γ • |b|) (i : Fin n) :
    |δx i| / |x i| ≤ γ * (|A⁻¹ i| ⬝ᵥ |b|) / |A⁻¹ i ⬝ᵥ b| := by
  have h := abs_sub_apply_div_le_of_abs_le_abs hA hx hδx hδb i
  rwa [Pi.add_apply, add_sub_cancel_left] at h

/-- **Example 3.1** of [quarteroni2000numerical], the matrix. For $\alpha \in \mathbb{R}$, this is
$$A = \begin{bmatrix} \alpha & 1/\alpha \\ 0 & 1/\alpha \end{bmatrix}.$$
-/
noncomputable def example_3_1_matrix (α : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![α, α⁻¹; 0, α⁻¹]

/-- For $\alpha > 0$, the inverse of the matrix of Example 3.1 is $\begin{bmatrix} 1/\alpha &
-1/\alpha \\ 0 & \alpha \end{bmatrix}$. -/
private theorem example_3_1_matrix_inv {α : ℝ} (hα : 0 < α) :
    (example_3_1_matrix α)⁻¹ = !![α⁻¹, -α⁻¹; 0, α] := by
  refine inv_eq_right_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [example_3_1_matrix, Matrix.mul_apply, Fin.sum_univ_two, hα.ne']

/-- **Example 3.1** of [quarteroni2000numerical], equation (3.17). Let $\alpha > 0$, let $A$ be the
matrix of Example 3.1, and let $b = (\alpha^2 + 1/\alpha, 1/\alpha)^T$. Then $x = (\alpha, 1)^T$
solves $Ax = b$, and
$$|A^{-1}| \, |A| \, |x| = |A^{-1}| \, |b| = (\alpha + 2/\alpha^2, 1)^T,$$
which is unbounded as $\alpha \to 0$. For the component $x_2$, which has the largest absolute
value when $\alpha < 1$, the amplification factor of (3.16) is
$|r_{(2)}^T| \, |A| \, |x| / |x_2| = 1$.

**Generalization.** The book takes $0 < \alpha < 1$. The identities hold for every $\alpha > 0$.

Indices start at $0$, so the second row $r_{(2)}^T$ of $A^{-1}$ is `(example_3_1_matrix α)⁻¹ 1`. -/
theorem example_3_1 {α : ℝ} (hα : 0 < α) :
    example_3_1_matrix α *ᵥ ![α, 1] = ![α ^ 2 + α⁻¹, α⁻¹] ∧
      (example_3_1_matrix α)⁻¹.abs *ᵥ ((example_3_1_matrix α).abs *ᵥ |![α, 1]|) =
        ![α + 2 / α ^ 2, 1] ∧
      (example_3_1_matrix α)⁻¹.abs *ᵥ |![α ^ 2 + α⁻¹, α⁻¹]| = ![α + 2 / α ^ 2, 1] ∧
      |(example_3_1_matrix α)⁻¹ 1| ⬝ᵥ ((example_3_1_matrix α).abs *ᵥ |![α, 1]|) / |![α, 1] 1|
        = 1 := by
  have hinv := example_3_1_matrix_inv hα
  have hα' : 0 < α⁻¹ := inv_pos.mpr hα
  have habs : |![α, (1 : ℝ)]| = ![α, 1] := by
    ext i; fin_cases i <;> simp [abs_of_pos hα]
  have habsb : |![α ^ 2 + α⁻¹, α⁻¹]| = ![α ^ 2 + α⁻¹, α⁻¹] := by
    ext i; fin_cases i <;> simp [abs_of_pos, hα', add_pos (pow_pos hα 2) hα']
  have hAabs : (example_3_1_matrix α).abs = example_3_1_matrix α := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [example_3_1_matrix, abs_of_pos hα, abs_of_pos hα']
  have hAinvabs : (example_3_1_matrix α)⁻¹.abs = !![α⁻¹, α⁻¹; 0, α] := by
    rw [hinv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [abs_of_pos hα, abs_of_pos hα']
  have hAx : example_3_1_matrix α *ᵥ ![α, 1] = ![α ^ 2 + α⁻¹, α⁻¹] := by
    ext i
    fin_cases i <;> simp [example_3_1_matrix, mulVec, dotProduct, Fin.sum_univ_two, sq]
  have hAb : !![α⁻¹, α⁻¹; 0, α] *ᵥ ![α ^ 2 + α⁻¹, α⁻¹] = ![α + 2 / α ^ 2, 1] := by
    ext i
    fin_cases i
    · simp [mulVec, dotProduct, Fin.sum_univ_two]
      field_simp
      ring
    · simp [mulVec, dotProduct, Fin.sum_univ_two]
      field_simp
  refine ⟨hAx, ?_, ?_, ?_⟩
  · rw [habs, hAabs, hAx, hAinvabs, hAb]
  · rw [hAinvabs, habsb, hAb]
  · rw [habs, hAabs, hAx, hinv]
    simp [dotProduct, Fin.sum_univ_two, abs_of_pos hα]
    field_simp

end Componentwise

/-! ### §3.1.3: backward a priori analysis, Property 3.1 -/

section Backward

variable {A C : Matrix (Fin n) (Fin n) ℝ}

/-- **Property 3.1** of [quarteroni2000numerical], the first clause. Let
$A, C \in \mathbb{R}^{n \times n}$ and $R = AC - I$. If $\|R\|_p < 1$ in the norm induced by the
vector $p$-norm, then $A$ and $C$ are nonsingular.

The proof is the backbone's `isUnit_of_norm_mul_sub_one_lt` in the ring of operators on
`PiLp p (Fin n → ℝ)`, which is Dedekind-finite because the matrix ring is. -/
theorem property_3_1_isUnit (hR : lpOpNorm p (A * C - 1) < 1) : IsUnit A ∧ IsUnit C := by
  have h : ‖lpCLM p A * lpCLM p C - 1‖ < 1 := by
    rw [← lpCLM_mul, ← lpCLM_one, ← lpCLM_sub]
    exact hR
  obtain ⟨hA, hC⟩ := isUnit_of_norm_mul_sub_one_lt h
  exact ⟨(isUnit_lpCLM_iff p A).mp hA, (isUnit_lpCLM_iff p C).mp hC⟩

/-- **Property 3.1** of [quarteroni2000numerical], the first bound of (3.18). Let $n \ge 1$ and
$A, C \in \mathbb{R}^{n \times n}$. If $\|AC - I\|_p < 1$, then
$$\|A^{-1}\|_p \le \frac{\|C\|_p}{1 - \|AC - I\|_p}.$$

The proof is the backbone's `NormedRing.norm_inverse_le_of_norm_mul_sub_one_lt`. -/
theorem property_3_1_inv [NeZero n] (hR : lpOpNorm p (A * C - 1) < 1) :
    lpOpNorm p A⁻¹ ≤ lpOpNorm p C / (1 - lpOpNorm p (A * C - 1)) := by
  have h : ‖lpCLM p A * lpCLM p C - 1‖ < 1 := by
    rw [← lpCLM_mul, ← lpCLM_one, ← lpCLM_sub]
    exact hR
  have hA := (isUnit_lpCLM_iff p A).mpr (property_3_1_isUnit hR).1
  have hle := NormedRing.norm_inverse_le_of_norm_mul_sub_one_lt hA h
  rwa [ringInverse_lpCLM, ← lpCLM_mul, ← lpCLM_one, ← lpCLM_sub] at hle

/-- **Property 3.1** of [quarteroni2000numerical], the second display of (3.18). Let $n \ge 1$ and
$A, C \in \mathbb{R}^{n \times n}$. If $\|AC - I\|_p < 1$, then
$$\frac{\|AC - I\|_p}{\|A\|_p} \le \|C - A^{-1}\|_p \le \frac{\|C\|_p \, \|AC - I\|_p}{1 -
  \|AC - I\|_p}.$$

The proofs are the backbone's `NormedRing.norm_mul_sub_one_div_norm_le_norm_sub_inverse` and
`NormedRing.norm_sub_inverse_le_of_norm_mul_sub_one_lt`. -/
theorem property_3_1_sub [NeZero n] (hR : lpOpNorm p (A * C - 1) < 1) :
    lpOpNorm p (A * C - 1) / lpOpNorm p A ≤ lpOpNorm p (C - A⁻¹) ∧
      lpOpNorm p (C - A⁻¹) ≤
        lpOpNorm p C * lpOpNorm p (A * C - 1) / (1 - lpOpNorm p (A * C - 1)) := by
  have h : ‖lpCLM p A * lpCLM p C - 1‖ < 1 := by
    rw [← lpCLM_mul, ← lpCLM_one, ← lpCLM_sub]
    exact hR
  have hA := (isUnit_lpCLM_iff p A).mpr (property_3_1_isUnit hR).1
  have h1 := NormedRing.norm_mul_sub_one_div_norm_le_norm_sub_inverse (c := lpCLM p C) hA
  have h2 := NormedRing.norm_sub_inverse_le_of_norm_mul_sub_one_lt hA h
  rw [ringInverse_lpCLM, ← lpCLM_sub, ← lpCLM_mul, ← lpCLM_one, ← lpCLM_sub] at h1 h2
  exact ⟨h1, h2⟩

/-- **Equation (3.19)** of [quarteroni2000numerical]. Let $n \ge 1$ and
$A, C \in \mathbb{R}^{n \times n}$, and let $R = CA - I$ satisfy $\|R\|_p < 1$. Interpret $C$ as
the exact inverse of a perturbed matrix $A + \delta A$, so that $C (A + \delta A) = I$ and
$\delta A = C^{-1} - A$. Then
$$\|\delta A\|_p \le \frac{\|R\|_p \, \|A\|_p}{1 - \|R\|_p}.$$

**Correction.** The book's derivation applies Property 3.1 with $R = AC - I$. Because $C$ is the
exact inverse of $A + \delta A$, the derivation needs the roles of $A$ and $C$ interchanged, and
the statement assumes $\|CA - I\|_p < 1$.

The proof is the backbone's `NormedRing.norm_sub_le_of_norm_mul_sub_one_lt`. -/
theorem equation_3_19 [NeZero n] (hR : lpOpNorm p (C * A - 1) < 1) :
    lpOpNorm p (C⁻¹ - A) ≤
      lpOpNorm p (C * A - 1) * lpOpNorm p A / (1 - lpOpNorm p (C * A - 1)) := by
  have h : ‖lpCLM p C * lpCLM p A - 1‖ < 1 := by
    rw [← lpCLM_mul, ← lpCLM_one, ← lpCLM_sub]
    exact hR
  have hC := (isUnit_lpCLM_iff p C).mpr (property_3_1_isUnit hR).1
  have hle := NormedRing.norm_sub_le_of_norm_mul_sub_one_lt hC h
  rwa [ringInverse_lpCLM, ← lpCLM_sub, ← lpCLM_mul, ← lpCLM_one, ← lpCLM_sub] at hle

end Backward

/-! ### §3.1.4: a posteriori analysis -/

section Posteriori

variable {A C : Matrix (Fin n) (Fin n) ℝ} {b x : Fin n → ℝ}

/-- **Equation (3.20)** of [quarteroni2000numerical]. Let $A, C \in \mathbb{R}^{n \times n}$ with
$\|R\|_p = \|AC - I\|_p < 1$, let $x$ solve $Ax = b$, and let $y \in \mathbb{R}^n$ be any
approximate solution, with residual $r = b - Ay$ and error $e = y - x$. Then
$$\|e\|_p \le \frac{\|r\|_p \, \|C\|_p}{1 - \|R\|_p}.$$

The vector $y$ need not be the vector $Cb$ of the backward analysis. The proof is the backbone's
`norm_error_le_of_norm_mul_sub_one_lt`. -/
theorem equation_3_20 (hR : lpOpNorm p (A * C - 1) < 1) (hx : A *ᵥ x = b) (y : Fin n → ℝ) :
    ‖toLp p (y - x)‖ ≤
      ‖toLp p (b - A *ᵥ y)‖ * lpOpNorm p C / (1 - lpOpNorm p (A * C - 1)) := by
  have hA := (property_3_1_isUnit hR).1
  have h : ‖(lpEquiv p hA : _ →L[ℝ] _) * lpCLM p C - 1‖ < 1 := by
    rw [coe_lpEquiv, ← lpCLM_mul, ← lpCLM_one, ← lpCLM_sub]
    exact hR
  have hle := norm_error_le_of_norm_mul_sub_one_lt (lpEquiv p hA) (lpCLM p C) h
    (x := toLp p x) (b := toLp p b) (by rw [lpEquiv_apply, ofLp_toLp, hx]) (toLp p y)
  rwa [coe_lpEquiv, ← lpCLM_mul, ← lpCLM_one, ← lpCLM_sub, lpEquiv_apply, ofLp_toLp,
    ← toLp_sub, ← toLp_sub] at hle

/-- **Equation (3.21)** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ be
nonsingular, let $Ax = b$ with $b \neq 0$, and let $y \in \mathbb{R}^n$ be any approximate
solution, with residual $r = b - Ay$ and error $e = y - x$. Then
$$\frac{\|e\|_p}{\|x\|_p} \le K_p(A) \, \frac{\|r\|_p}{\|b\|_p}.$$
This is (3.11) with $y = x + \delta x$, where $\delta b$ is the residual up to sign.

The proof is the backbone's `relative_error_le_condNumber_mul_relative_residual`. -/
theorem equation_3_21 (hA : IsUnit A) (hx : A *ᵥ x = b) (hb : b ≠ 0) (y : Fin n → ℝ) :
    ‖toLp p (y - x)‖ / ‖toLp p x‖ ≤ condNumber p A * (‖toLp p (b - A *ᵥ y)‖ / ‖toLp p b‖) := by
  have h := relative_error_le_condNumber_mul_relative_residual (lpEquiv p hA) (x := toLp p x)
    (b := toLp p b) (y := toLp p y) (by rw [lpEquiv_apply, ofLp_toLp, hx])
    (by rwa [Ne, toLp_eq_zero])
  rw [coe_lpEquiv, ← condNumber_eq, lpEquiv_apply, ofLp_toLp, ← toLp_sub, ← toLp_sub] at h
  rwa [← neg_sub x y, toLp_neg, norm_neg]

open scoped Matrix.Norms.Operator in
/-- **Section 3.1.4** of [quarteroni2000numerical], the LAPACK estimate. Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular, let $Ax = b$, and let $y \in \mathbb{R}^n$ be an
approximate solution. Let $\hat{r}$ be the residual $b - Ay$ computed in floating-point
arithmetic with unit roundoff $u$, where $(n + 1) u < 1$. Then the error $e = y - x$ satisfies
$$\frac{\|e\|_\infty}{\|y\|_\infty} \le \frac{\bigl\| |A^{-1}| \bigl( |\hat{r}| + \gamma_{n+1}
  (|A| \, |y| + |b|) \bigr) \bigr\|_\infty}{\|y\|_\infty}, \qquad \gamma_{n+1} = \frac{(n + 1)
  u}{1 - (n + 1) u}.$$

The computed residual is an admissible `FloatingPoint.RoundsAffineStep m (-A) b y rhat` of the
relational rounding model `m`, whose unit roundoff is $u$. Then $\hat{r} = r + \delta r$ with
$|\delta r| \le \gamma_{n+1} (|A| \, |y| + |b|)$, by the backbone's
`FloatingPoint.exists_roundsAffineStep_eq_add`, and the bound is
`Matrix.norm_sub_le_of_computedResidual`. The backbone writes the constant $\gamma_{n+1}$ as
`FloatingPoint.gamma`. -/
theorem computedResidualErrorBound {m : FloatingPoint.RoundingModel ℝ}
    (hu : ((n + 1 : ℕ) : ℝ) * m.u < 1) (hA : IsUnit A) (hx : A *ᵥ x = b) {y rhat : Fin n → ℝ}
    (hr : FloatingPoint.RoundsAffineStep m (-A) b y rhat) :
    ‖y - x‖ / ‖y‖ ≤
      ‖A⁻¹.abs *ᵥ (|rhat| + FloatingPoint.gamma m.u (n + 1) • (A.abs *ᵥ |y| + |b|))‖ / ‖y‖ := by
  have hu1 : m.u < 1 := by
    have h0 := m.u_nonneg
    have : m.u ≤ ((n + 1 : ℕ) : ℝ) * m.u := by
      have : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
      nlinarith
    exact this.trans_lt hu
  obtain ⟨ξ, hξ, hξle⟩ := FloatingPoint.exists_roundsAffineStep_eq_add hu1
    (by rwa [Fintype.card_fin]) hr
  have hneg : (-A).abs = A.abs := by
    ext i j
    simp
  rw [Fintype.card_fin, hneg] at hξle
  have hle := norm_sub_le_of_computedResidual hA hx (rhat := rhat) (δr := ξ)
    (by rw [hξ, neg_mulVec, sub_eq_neg_add]) hξle
  exact div_le_div_of_nonneg_right hle (norm_nonneg y)

end Posteriori

end QuarteroniSaccoSaleri.Chapter03
