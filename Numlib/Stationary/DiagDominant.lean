/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Numlib.LinearAlgebra.Matrix.DiagDominant
import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.Stationary.Splitting
import Numlib.Stationary.Sweep

/-!
# Convergence of Jacobi and Gauss–Seidel for diagonally dominant matrices

Let $A = (a_{ij})$ be a square matrix over $\mathbb{R}$ or $\mathbb{C}$, indexed by a finite
linearly ordered set, and write $A = D - E - F$, where $D$ is the diagonal of $A$ and $-E$ and $-F$
are its strictly lower and strictly upper triangular parts. This module proves that the Jacobi
iteration matrix $G_J = D^{-1}(E + F)$ and the Gauss–Seidel iteration matrix
$G_{GS} = (D - E)^{-1} F$ have spectral radius less than $1$ when $A$ is strictly or irreducibly
diagonally dominant ([saad2003iterative], Theorem 4.9 and Corollary 4.8; [kress1998numerical],
Theorems 4.2–4.3, Corollary 4.4 and Theorem 4.7; [han2009theoretical], Example 5.2.2). It also
proves the convergence of SOR for $0 < \omega \le 1$ under strict row dominance
([quarteroni2000numerical], Property 4.3).

Two explicit constants of [kress1998numerical] bound the iteration matrices in the maximum norm
$\|\cdot\|_\infty$. The **Jacobi constant** $q_\infty = \max_i \sum_{j \neq i} |a_{ij}| / |a_{ii}|$
is exactly $\|G_J\|_\infty$. The **Sassenfeld numbers** $p_i$, defined by the recursion $p_i =
(\sum_{j<i} |a_{ij}| p_j + \sum_{j>i} |a_{ij}|) / |a_{ii}|$, bound
$\|G_{GS}\|_\infty \le \max_i p_i$. Under strict row dominance both constants are less than $1$.
Strict dominance in every row is more than convergence needs: a matrix that is irreducible, weakly
dominant in every row and strictly dominant in one row is still nonsingular, and Jacobi and
Gauss–Seidel still converge for it.

## Main definitions

* `Matrix.jacobiContraction`: the Jacobi constant $q_\infty$.
* `Matrix.sassenfeld`: the Sassenfeld numbers $p_i$.

## Main results

* `Matrix.linfty_opNorm_jacobi_iterMatrix`: $\|G_J\|_\infty = q_\infty$.
* `Matrix.IsStrictDiagDominant.jacobiContraction_lt_one`: strict row dominance gives $q_\infty < 1$.
* `Matrix.linfty_opNorm_gaussSeidel_iterMatrix_le`: Sassenfeld's criterion
  $\|G_{GS}\|_\infty \le \max_i p_i$.
* `Matrix.sassenfeld_le_jacobiContraction`: strict row dominance gives $p_i \le q_\infty$.
* `Matrix.jacobi_spectralRadius_lt_one` and `Matrix.gaussSeidel_spectralRadius_lt_one`: strict row
  dominance gives $\rho(G_J) < 1$ and $\rho(G_{GS}) < 1$.
* `Matrix.jacobi_spectralRadius_lt_one_of_col` and
  `Matrix.gaussSeidel_spectralRadius_lt_one_of_col`: the same under strict column dominance.
* `Matrix.sorSplitting_spectralRadius_lt_one_of_le_one`: strict row dominance gives
  $\rho(G_\omega) < 1$ for $0 < \omega \le 1$.
* `Matrix.IsIrreduciblyDiagDominant.jacobi_spectralRadius_lt_one` and
  `Matrix.IsIrreduciblyDiagDominant.gaussSeidel_spectralRadius_lt_one`: irreducible diagonal
  dominance gives $\rho(G_J) < 1$ and $\rho(G_{GS}) < 1$.
* `Matrix.jacobi_complexSpectralRadius_lt_one` and its companions: the same statements for real
  matrices.

## Proof outline

The irreducible and the column-dominant cases use a pencil: the matrix $A$ with its diagonal, or
with its whole lower triangle, scaled by an eigenvalue $\mu$ of the iteration matrix. If
$|\mu| \ge 1$, the pencil inherits the dominance of $A$, so it is nonsingular by
`Matrix.IsPatternIrreducible.isUnit_of_dominant` or by strict column dominance. But it annihilates
the eigenvector, so no such eigenvalue exists. The strictly row-dominant cases compare the moduli in
the row where an eigenvector attains its maximum norm.

## Implementation notes

* The dominance predicates and their nonsingularity theorems are in
  `Numlib.LinearAlgebra.Matrix.DiagDominant`, and the splittings are those of
  `Numlib.Stationary.Splitting`.
* The spectral statements are made for complex matrices. The last section states them for a real
  matrix through `Matrix.complexSpectralRadius`, the spectral radius of the complexification,
  because the classical splittings commute with `Matrix.complexify`
  (`Matrix.complexify_jacobi_iterationOperator`, `Matrix.complexify_gaussSeidel_iterationOperator`).
* The norm $\|\cdot\|_\infty$ of a matrix is the operator norm of the scoped instance
  `Matrix.Norms.Operator`, the maximum absolute row sum.
* The Jacobi constant and the maximum of the Sassenfeld numbers need an index set with at least one
  element.
-/

namespace Matrix

open scoped NNReal ENNReal

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

section Def

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The **Jacobi constant** of a square matrix $A$ of order $n \ge 1$ is
$$q_\infty = \max_i \frac{1}{|a_{ii}|} \sum_{j \neq i} |a_{ij}|$$
([kress1998numerical], Theorem 4.2).

Division by $|a_{ii}| = 0$ gives $0$ in Lean. -/
noncomputable def jacobiContraction [Nonempty n] (A : Matrix n n 𝕜) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => (∑ j ∈ Finset.univ.erase i, ‖A i j‖) / ‖A i i‖

omit [LinearOrder n] in
/-- Let $A$ be a square matrix of order $n \ge 1$ that is strictly diagonally dominant by rows,
$\sum_{j \neq i} |a_{ij}| < |a_{ii}|$ for every $i$. Then the Jacobi constant satisfies
$q_\infty < 1$.

With `Matrix.linfty_opNorm_jacobi_iterMatrix`, which identifies $q_\infty$ with
$\|G_J\|_\infty$, this makes the Jacobi iteration a contraction in the norm $\|\cdot\|_\infty$. -/
theorem IsStrictDiagDominant.jacobiContraction_lt_one [Nonempty n] {A : Matrix n n 𝕜}
    (hA : A.IsStrictDiagDominant) : jacobiContraction A < 1 := by
  rw [jacobiContraction, Finset.sup'_lt_iff]
  exact fun i _ => (div_lt_one (norm_pos_iff.mpr (hA.diag_ne_zero i))).mpr (hA i)

omit [LinearOrder n] in
/-- For every row $i$, the quotient $\sum_{j \neq i} |a_{ij}| / |a_{ii}|$ is at most the Jacobi
constant $q_\infty$. -/
theorem div_le_jacobiContraction [Nonempty n] (A : Matrix n n 𝕜) (i : n) :
    (∑ j ∈ Finset.univ.erase i, ‖A i j‖) / ‖A i i‖ ≤ jacobiContraction A :=
  Finset.le_sup' (fun i => (∑ j ∈ Finset.univ.erase i, ‖A i j‖) / ‖A i i‖) (Finset.mem_univ i)

omit [LinearOrder n] in
/-- The Jacobi constant is nonnegative: $q_\infty \ge 0$. -/
theorem jacobiContraction_nonneg [Nonempty n] (A : Matrix n n 𝕜) : 0 ≤ jacobiContraction A := by
  obtain ⟨i⟩ := ‹Nonempty n›
  refine le_trans ?_ (div_le_jacobiContraction A i)
  positivity

/-- The **Sassenfeld numbers** of a square matrix $A$ are the solution $p$ of the lower triangular
system
$$p_i = \frac{1}{|a_{ii}|} \Bigl(\sum_{j<i} |a_{ij}| p_j + \sum_{j>i} |a_{ij}|\Bigr)$$
([kress1998numerical], Theorem 4.3).

The definition is $p = (|D| - |L|)^{-1} s$, where the lower triangular matrix $|D| - |L|$ has
the entries $|a_{ii}|$ on the diagonal and $-|a_{ij}|$ below it, and
$s_i = \sum_{j>i} |a_{ij}|$. The recursion holds when the diagonal of $A$ is invertible
(`Matrix.sassenfeld_eq`). Otherwise the matrix inverse is Mathlib's value $0$, and $p = 0$. -/
noncomputable def sassenfeld (A : Matrix n n 𝕜) : n → ℝ :=
  (Matrix.of fun i j => if i = j then ‖A i i‖ else if j < i then -‖A i j‖ else 0)⁻¹ *ᵥ
    fun i => ∑ j ∈ Finset.univ.filter (i < ·), ‖A i j‖

/-- The lower triangular matrix $|D| - |L|$, with the entries $|a_{ii}|$ on the diagonal,
$-|a_{ij}|$ below it and $0$ above it. -/
private def sassenfeldMatrix (A : Matrix n n 𝕜) : Matrix n n ℝ :=
  Matrix.of fun i j => if i = j then ‖A i i‖ else if j < i then -‖A i j‖ else 0

omit [Fintype n] in
/-- The entries of the matrix $|D| - |L|$. -/
private theorem sassenfeldMatrix_apply (A : Matrix n n 𝕜) (i j : n) :
    sassenfeldMatrix A i j = if i = j then ‖A i i‖ else if j < i then -‖A i j‖ else 0 := rfl

/-- The Sassenfeld numbers are $(|D| - |L|)^{-1}$ applied to the vector of the upper row sums
$\sum_{j>i} |a_{ij}|$. -/
private theorem sassenfeld_def (A : Matrix n n 𝕜) :
    sassenfeld A =
      (sassenfeldMatrix A)⁻¹ *ᵥ fun i => ∑ j ∈ Finset.univ.filter (i < ·), ‖A i j‖ := rfl

/-- If the diagonal of $A$ is invertible, then so is the lower triangular matrix $|D| - |L|$, whose
diagonal entries are $|a_{ii}|$. -/
private theorem isUnit_sassenfeldMatrix {A : Matrix n n 𝕜} (h : IsUnit (diagPart A)) :
    IsUnit (sassenfeldMatrix A) := by
  have hd := (isUnit_diagPart_iff A).mp h
  have hlt : (sassenfeldMatrix A).IsLowerTriangular := by
    intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
    simp [sassenfeldMatrix_apply, hij'.ne, asymm hij']
  rw [isUnit_iff_isUnit_det, det_of_isLowerTriangular _ hlt, isUnit_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => by
    simpa [sassenfeldMatrix_apply] using norm_ne_zero_iff.mpr (hd i)

/-- If the diagonal of $A$ is invertible, then the Sassenfeld numbers satisfy, for every $i$,
$$p_i = \frac{1}{|a_{ii}|} \Bigl(\sum_{j<i} |a_{ij}| p_j + \sum_{j>i} |a_{ij}|\Bigr).$$
-/
theorem sassenfeld_eq {A : Matrix n n 𝕜} (h : IsUnit (diagPart A)) (i : n) :
    sassenfeld A i = ((∑ j ∈ Finset.univ.filter (· < i), ‖A i j‖ * sassenfeld A j) +
      ∑ j ∈ Finset.univ.filter (i < ·), ‖A i j‖) / ‖A i i‖ := by
  have hd := (isUnit_diagPart_iff A).mp h
  have hsolve : sassenfeldMatrix A *ᵥ sassenfeld A =
      fun i => ∑ j ∈ Finset.univ.filter (i < ·), ‖A i j‖ := by
    rw [sassenfeld_def, mulVec_nonsing_inv_mulVec (isUnit_sassenfeldMatrix h)]
  have hi := congrFun hsolve i
  rw [mulVec, dotProduct] at hi
  have hsplit : ∀ j, sassenfeldMatrix A i j * sassenfeld A j =
      (if i = j then ‖A i i‖ * sassenfeld A j else 0) +
        (if j < i then -(‖A i j‖ * sassenfeld A j) else 0) := by
    intro j
    by_cases hij : i = j
    · subst hij; simp [sassenfeldMatrix_apply]
    · simp only [sassenfeldMatrix_apply, ite_eq_right hij]
      by_cases hji : j < i <;> simp [hji, neg_mul]
  rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib, Finset.sum_ite_eq,
    ← Finset.sum_filter] at hi
  simp only [Finset.mem_univ, ite_true, Finset.sum_neg_distrib] at hi
  rw [eq_div_iff (norm_ne_zero_iff.mpr (hd i))]
  linarith [hi]

/-- Row $i$ of $(D - E) v$ is $a_{ii} v_i + \sum_{j<i} a_{ij} v_j$. -/
private theorem diagPart_add_strictLower_mulVec_apply (A : Matrix n n 𝕜) (v : n → 𝕜) (i : n) :
    ((diagPart A + strictLower A) *ᵥ v) i =
      A i i * v i + ∑ j ∈ Finset.univ.filter (· < i), A i j * v j := by
  simp only [mulVec, dotProduct, Matrix.add_apply, diagPart_apply, strictLower_apply, add_mul,
    ite_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    ← Finset.sum_filter]

omit [Fintype n] [DecidableEq n] [LinearOrder n] in
/-- If $|v_j| \le c$ for every $j$, then $|\sum_{j \in s} a_{ij} v_j| \le (\sum_{j \in s} |a_{ij}|)
\, c$. -/
private theorem norm_sum_mul_le (A : Matrix n n 𝕜) (v : n → 𝕜) (i : n) (s : Finset n) {c : ℝ}
    (hc : ∀ j, ‖v j‖ ≤ c) : ‖∑ j ∈ s, A i j * v j‖ ≤ (∑ j ∈ s, ‖A i j‖) * c :=
  calc ‖∑ j ∈ s, A i j * v j‖ ≤ ∑ j ∈ s, ‖A i j * v j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ s, ‖A i j‖ * c := Finset.sum_le_sum fun j _ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hc j) (norm_nonneg _)
    _ = (∑ j ∈ s, ‖A i j‖) * c := by rw [Finset.sum_mul]

end Def

section Norm

open scoped Matrix.Norms.Operator

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The entries of the Jacobi iteration matrix are $0$ on the diagonal and $-a_{ij} / a_{ii}$ off
the diagonal. -/
private theorem jacobi_iterationOperator_apply (A : Matrix n n 𝕜) (h : IsUnit (diagPart A))
    (i j : n) : (jacobiSplitting A h).iterationOperator i j =
      if i = j then 0 else -((A i i)⁻¹ * A i j) := by
  rw [jacobiSplitting_iterationOperator, inv_diagPart h]
  rcases lt_trichotomy i j with hlt | rfl | hlt
  · simp [diagonal_mul, hlt, hlt.ne, asymm hlt]
  · simp [diagonal_mul]
  · simp [diagonal_mul, hlt, hlt.ne', asymm hlt]

/-- The off-diagonal entries of the Jacobi iteration matrix have absolute value
$|a_{ij}| / |a_{ii}|$. -/
private theorem norm_jacobi_iterationOperator_apply (A : Matrix n n 𝕜) (h : IsUnit (diagPart A))
    {i j : n} (hij : j ≠ i) :
    ‖(jacobiSplitting A h).iterationOperator i j‖ = ‖A i j‖ / ‖A i i‖ := by
  rw [jacobi_iterationOperator_apply, ite_eq_right (Ne.symm hij), norm_neg, norm_mul, norm_inv,
    div_eq_inv_mul]

/-- The absolute row sums of the Jacobi iteration matrix are the quotients
$\sum_{j \neq i} |a_{ij}| / |a_{ii}|$. -/
private theorem sum_norm_jacobi_iterationOperator (A : Matrix n n 𝕜) (h : IsUnit (diagPart A))
    (i : n) : ∑ j, ‖(jacobiSplitting A h).iterationOperator i j‖ =
      (∑ j ∈ Finset.univ.erase i, ‖A i j‖) / ‖A i i‖ := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), jacobi_iterationOperator_apply,
    ite_eq_left rfl, norm_zero, add_zero, Finset.sum_div]
  exact Finset.sum_congr rfl fun j hj =>
    norm_jacobi_iterationOperator_apply A h (Finset.ne_of_mem_erase hj)

/-- Let $A$ be a square matrix of order $n \ge 1$ with invertible diagonal. Then the Jacobi
iteration matrix satisfies
$$\|G_J\|_\infty = q_\infty,$$
where $q_\infty$ is the Jacobi constant `Matrix.jacobiContraction` ([kress1998numerical],
Theorem 4.2).

The norm is the operator norm $\|\cdot\|_\infty$ of the scoped instance `Matrix.Norms.Operator`. -/
theorem linfty_opNorm_jacobi_iterMatrix [Nonempty n] (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) :
    ‖(jacobiSplitting A h).iterationOperator‖ = jacobiContraction A := by
  rw [linfty_opNorm_def, ← Finset.sup'_eq_sup Finset.univ_nonempty,
    Finset.apply_sup'_eq_sup'_comp Finset.univ_nonempty NNReal.toReal NNReal.coe_max,
    jacobiContraction]
  refine Finset.sup'_congr _ rfl fun i _ => ?_
  simpa using sum_norm_jacobi_iterationOperator A h i

/-- $(D - E) \, G_{GS} = F$. -/
private theorem diagPart_add_strictLower_mul_gaussSeidel (A : Matrix n n 𝕜)
    (h : IsUnit (diagPart A)) :
    (diagPart A + strictLower A) * (gaussSeidelSplitting A h).iterationOperator =
      -strictUpper A := by
  rw [(gaussSeidelSplitting A h).iterationOperator_eq, gaussSeidelSplitting_n, ← mul_assoc,
    show (gaussSeidelSplitting A h).m = diagPart A + strictLower A from rfl,
    Ring.mul_inverse_cancel _ (isUnit_diagPart_add_strictLower h), one_mul]

/-- If the diagonal of $A$ is invertible, then the Sassenfeld numbers are nonnegative. -/
theorem sassenfeld_nonneg {A : Matrix n n 𝕜} (h : IsUnit (diagPart A)) (i : n) :
    0 ≤ sassenfeld A i := by
  induction i using WellFoundedLT.induction with
  | _ i ih =>
    rw [sassenfeld_eq h i]
    refine div_nonneg (add_nonneg (Finset.sum_nonneg fun j hj => ?_)
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)) (norm_nonneg _)
    exact mul_nonneg (norm_nonneg _) (ih j (by simpa using (Finset.mem_filter.mp hj).2))

/-- **Sassenfeld's criterion.** Let $A$ be a square matrix of order $n \ge 1$ with invertible
diagonal. Then the Gauss–Seidel iteration matrix satisfies
$$\|G_{GS}\|_\infty \le \max_i p_i,$$
where $p$ are the Sassenfeld numbers `Matrix.sassenfeld` ([kress1998numerical], Theorem 4.3).

For $y = G_{GS} x$, the relation $(D - E) y = F x$ gives $|y_i| \le (\sum_{j<i} |a_{ij}| |y_j| +
\sum_{j>i} |a_{ij}| \|x\|_\infty) / |a_{ii}|$. So $|y_i| \le p_i \|x\|_\infty$, by induction
along the order of the indices. -/
theorem linfty_opNorm_gaussSeidel_iterMatrix_le [Nonempty n] (A : Matrix n n 𝕜)
    (h : IsUnit (diagPart A)) :
    ‖(gaussSeidelSplitting A h).iterationOperator‖ ≤
      Finset.univ.sup' Finset.univ_nonempty (sassenfeld A) := by
  have hd := (isUnit_diagPart_iff A).mp h
  have hMnn : 0 ≤ Finset.univ.sup' Finset.univ_nonempty (sassenfeld A) :=
    le_trans (sassenfeld_nonneg h (Classical.arbitrary n))
      (Finset.le_sup' (sassenfeld A) (Finset.mem_univ _))
  rw [linfty_opNorm_eq_opNorm]
  refine ContinuousLinearMap.opNorm_le_bound _ hMnn fun x => ?_
  have hxnn : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  set y := (gaussSeidelSplitting A h).iterationOperator *ᵥ x with hy
  have heq : (diagPart A + strictLower A) *ᵥ y = -(strictUpper A *ᵥ x) := by
    rw [hy, mulVec_mulVec, diagPart_add_strictLower_mul_gaussSeidel, neg_mulVec]
  have hyi : ∀ i, ‖y i‖ ≤ sassenfeld A i * ‖x‖ := by
    intro i
    induction i using WellFoundedLT.induction with
    | _ i ih =>
      have hi := congrFun heq i
      rw [diagPart_add_strictLower_mulVec_apply, Pi.neg_apply, strictUpper_mulVec_apply] at hi
      have hAy : A i i * y i =
          -(∑ j ∈ Finset.univ.filter (i < ·), A i j * x j) -
            ∑ j ∈ Finset.univ.filter (· < i), A i j * y j := by
        linear_combination hi
      have hb2 : ‖∑ j ∈ Finset.univ.filter (· < i), A i j * y j‖ ≤
          ∑ j ∈ Finset.univ.filter (· < i), ‖A i j‖ * (sassenfeld A j * ‖x‖) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (ih j (by simpa using (Finset.mem_filter.mp hj).2))
          (norm_nonneg _)
      have hnorm : ‖A i i‖ * ‖y i‖ ≤
          (∑ j ∈ Finset.univ.filter (i < ·), ‖A i j‖) * ‖x‖ +
            ∑ j ∈ Finset.univ.filter (· < i), ‖A i j‖ * (sassenfeld A j * ‖x‖) := by
        rw [← norm_mul, hAy]
        refine (norm_sub_le _ _).trans ?_
        rw [norm_neg]
        gcongr
        exact norm_sum_mul_le A x i _ fun j => norm_le_pi_norm x j
      have hdist : (∑ j ∈ Finset.univ.filter (· < i), ‖A i j‖ * sassenfeld A j) * ‖x‖ =
          ∑ j ∈ Finset.univ.filter (· < i), ‖A i j‖ * (sassenfeld A j * ‖x‖) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [sassenfeld_eq h i, div_mul_eq_mul_div, le_div_iff₀ (norm_pos_iff.mpr (hd i)), add_mul,
        hdist]
      nlinarith [hnorm]
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  exact fun i => (hyi i).trans
    (mul_le_mul_of_nonneg_right (Finset.le_sup' (sassenfeld A) (Finset.mem_univ i)) hxnn)

/-- A sum over $j \neq i$ is the sum over $j < i$ plus the sum over $j > i$. -/
private theorem sum_erase_eq_sum_lt_add_sum_gt (f : n → ℝ) (i : n) :
    ∑ j ∈ Finset.univ.erase i, f j =
      (∑ j ∈ Finset.univ.filter (· < i), f j) + ∑ j ∈ Finset.univ.filter (i < ·), f j := by
  rw [← Finset.sum_union (by
    simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun _ hj1 hj2 => absurd hj1 (asymm hj2))]
  refine Finset.sum_congr (Finset.ext fun j => ?_) fun _ _ => rfl
  simp [Finset.mem_erase, lt_or_lt_iff_ne]

/-- Let $A$ be a square matrix of order $n \ge 1$ that is strictly diagonally dominant by rows. Then
$p_i \le q_\infty$ for every $i$ ([kress1998numerical], Corollary 4.4). Since $q_\infty < 1$,
the bound for Gauss–Seidel is at least as good as the bound for Jacobi. -/
theorem sassenfeld_le_jacobiContraction [Nonempty n] {A : Matrix n n 𝕜}
    (hA : A.IsStrictDiagDominant) (i : n) :
    sassenfeld A i ≤ jacobiContraction A := by
  induction i using WellFoundedLT.induction with
  | _ i ih =>
    have hq1 : jacobiContraction A < 1 := hA.jacobiContraction_lt_one
    have hpos : 0 < ‖A i i‖ := norm_pos_iff.mpr (hA.diag_ne_zero i)
    rw [sassenfeld_eq hA.isUnit_diagPart i, div_le_iff₀ hpos]
    have h1 : ∑ j ∈ Finset.univ.filter (· < i), ‖A i j‖ * sassenfeld A j ≤
        ∑ j ∈ Finset.univ.filter (· < i), ‖A i j‖ :=
      Finset.sum_le_sum fun j hj => by
        have hji : j < i := by simpa using (Finset.mem_filter.mp hj).2
        calc ‖A i j‖ * sassenfeld A j ≤ ‖A i j‖ * jacobiContraction A :=
              mul_le_mul_of_nonneg_left (ih j hji) (norm_nonneg _)
          _ ≤ ‖A i j‖ * 1 := mul_le_mul_of_nonneg_left hq1.le (norm_nonneg _)
          _ = ‖A i j‖ := mul_one _
    have h2 : (∑ j ∈ Finset.univ.erase i, ‖A i j‖) ≤ jacobiContraction A * ‖A i i‖ := by
      rw [← div_le_iff₀ hpos]
      exact div_le_jacobiContraction A i
    rw [sum_erase_eq_sum_lt_add_sum_gt] at h2
    linarith

end Norm

section Pencil

variable {𝕜 : Type*} [RCLike 𝕜]

omit [Fintype n] in
/-- The entries of the pencil $\mu D - E - F$ are $\mu a_{ii}$ on the diagonal and $a_{ij}$ off the
diagonal; its singularity detects the eigenvalue $\mu$ of the Jacobi iteration matrix. -/
private theorem jacobiPencil_apply (A : Matrix n n 𝕜) (μ : 𝕜) (i j : n) :
    (μ • diagPart A + strictLower A + strictUpper A) i j =
      if i = j then μ * A i i else A i j := by
  rcases lt_trichotomy i j with hlt | rfl | hlt
  · simp [hlt, hlt.ne, asymm hlt]
  · simp
  · simp [hlt, hlt.ne', asymm hlt]

omit [Fintype n] in
/-- The entries of the pencil $\lambda (D - E) - F$ are $\lambda a_{ij}$ for $j \le i$ and $a_{ij}$
for $j > i$; its singularity detects the eigenvalue $\lambda$ of the Gauss–Seidel iteration
matrix. -/
private theorem gaussSeidelPencil_apply (A : Matrix n n 𝕜) (l : 𝕜) (i j : n) :
    (l • (diagPart A + strictLower A) + strictUpper A) i j =
      if j ≤ i then l * A i j else A i j := by
  rcases lt_trichotomy i j with hlt | rfl | hlt
  · simp [hlt, hlt.ne, asymm hlt, not_le.mpr hlt]
  · simp
  · simp [hlt, hlt.ne', asymm hlt, hlt.le]

/-- $D (\mu I - G_J) = \mu D - E - F$. -/
private theorem diagPart_mul_jacobi_resolvent (A : Matrix n n 𝕜) (h : IsUnit (diagPart A))
    (μ : 𝕜) :
    diagPart A * (μ • (1 : Matrix n n 𝕜) - (jacobiSplitting A h).iterationOperator) =
      μ • diagPart A + strictLower A + strictUpper A := by
  rw [jacobiSplitting_iterationOperator, mul_sub, mul_smul_comm, mul_one, neg_mul, mul_neg,
    ← mul_assoc, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp h), one_mul]
  module

/-- $(D - E)(\lambda I - G_{GS}) = \lambda (D - E) - F$. -/
private theorem diagPart_add_strictLower_mul_gaussSeidel_resolvent (A : Matrix n n 𝕜)
    (h : IsUnit (diagPart A)) (l : 𝕜) :
    (diagPart A + strictLower A) *
        (l • (1 : Matrix n n 𝕜) - (gaussSeidelSplitting A h).iterationOperator) =
      l • (diagPart A + strictLower A) + strictUpper A := by
  rw [mul_sub, mul_smul_comm, mul_one, diagPart_add_strictLower_mul_gaussSeidel, sub_neg_eq_add]

omit [LinearOrder n] in
/-- A vector that an invertible matrix maps to $0$ is $0$; this is Mathlib's
`Matrix.eq_zero_of_mulVec_eq_zero` stated with `IsUnit`. -/
private theorem eq_zero_of_isUnit_of_mulVec_eq_zero {B : Matrix n n 𝕜} (hB : IsUnit B)
    {x : n → 𝕜} (hBx : B *ᵥ x = 0) : x = 0 :=
  eq_zero_of_mulVec_eq_zero (isUnit_iff_ne_zero.mp ((isUnit_iff_isUnit_det B).mp hB)) hBx

omit [LinearOrder n] in
/-- Let $c \ge 0$, let $|b_{ij}| \le c |a_{ij}|$ for $i \neq j$ and $|b_{ii}| = c |a_{ii}|$; if
every row of $A$ is weakly diagonally dominant, then so is every row of $B$. -/
private theorem dominant_of_norm_le {A B : Matrix n n 𝕜} {c : ℝ}
    (hoff : ∀ i j, i ≠ j → ‖B i j‖ ≤ c * ‖A i j‖) (hdiag : ∀ i, ‖B i i‖ = c * ‖A i i‖)
    (hc : 0 ≤ c) (hdom : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ ≤ ‖A i i‖) (i : n) :
    ∑ j ∈ Finset.univ.erase i, ‖B i j‖ ≤ ‖B i i‖ := by
  calc ∑ j ∈ Finset.univ.erase i, ‖B i j‖
      ≤ ∑ j ∈ Finset.univ.erase i, c * ‖A i j‖ :=
        Finset.sum_le_sum fun j hj => hoff i j (Finset.ne_of_mem_erase hj).symm
    _ = c * ∑ j ∈ Finset.univ.erase i, ‖A i j‖ := by rw [Finset.mul_sum]
    _ ≤ c * ‖A i i‖ := by gcongr; exact hdom i
    _ = ‖B i i‖ := (hdiag i).symm

omit [LinearOrder n] in
/-- Let $c > 0$, let $|b_{ij}| \le c |a_{ij}|$ for $i \neq j$ and $|b_{ii}| = c |a_{ii}|$; if row
$i$ of $A$ is strictly diagonally dominant, then so is row $i$ of $B$. -/
private theorem strict_of_norm_le {A B : Matrix n n 𝕜} {c : ℝ}
    (hoff : ∀ i j, i ≠ j → ‖B i j‖ ≤ c * ‖A i j‖) (hdiag : ∀ i, ‖B i i‖ = c * ‖A i i‖)
    (hc : 0 < c) {i : n} (hstrict : ∑ j ∈ Finset.univ.erase i, ‖A i j‖ < ‖A i i‖) :
    ∑ j ∈ Finset.univ.erase i, ‖B i j‖ < ‖B i i‖ := by
  calc ∑ j ∈ Finset.univ.erase i, ‖B i j‖
      ≤ ∑ j ∈ Finset.univ.erase i, c * ‖A i j‖ :=
        Finset.sum_le_sum fun j hj => hoff i j (Finset.ne_of_mem_erase hj).symm
    _ = c * ∑ j ∈ Finset.univ.erase i, ‖A i j‖ := by rw [Finset.mul_sum]
    _ < c * ‖A i i‖ := mul_lt_mul_of_pos_left hstrict hc
    _ = ‖B i i‖ := (hdiag i).symm

omit [LinearOrder n] in
/-- Let $c > 0$, let $|b_{ij}| \le c |a_{ij}|$ for $i \neq j$ and $|b_{ii}| = c |a_{ii}|$; if $A$ is
strictly diagonally dominant by columns, then so is $B$. -/
private theorem isStrictColDiagDominant_of_norm_le {A B : Matrix n n 𝕜} {c : ℝ}
    (hoff : ∀ i j, i ≠ j → ‖B i j‖ ≤ c * ‖A i j‖) (hdiag : ∀ i, ‖B i i‖ = c * ‖A i i‖)
    (hc : 0 < c) (hA : A.IsStrictColDiagDominant) : B.IsStrictColDiagDominant := fun j => by
  calc ∑ i ∈ Finset.univ.erase j, ‖B i j‖
      ≤ ∑ i ∈ Finset.univ.erase j, c * ‖A i j‖ :=
        Finset.sum_le_sum fun i hi => hoff i j (Finset.ne_of_mem_erase hi)
    _ = c * ∑ i ∈ Finset.univ.erase j, ‖A i j‖ := by rw [Finset.mul_sum]
    _ < c * ‖A j j‖ := mul_lt_mul_of_pos_left (hA j) hc
    _ = ‖B j j‖ := (hdiag j).symm

omit [Fintype n] in
/-- If $|\mu| \ge 1$, the off-diagonal entries of $\mu D - E - F$ have absolute value at most
$|\mu|$ times those of $A$. -/
private theorem jacobiPencil_norm_le {A : Matrix n n 𝕜} {μ : 𝕜} (hμ : 1 ≤ ‖μ‖) (i j : n)
    (hij : i ≠ j) : ‖(μ • diagPart A + strictLower A + strictUpper A) i j‖ ≤ ‖μ‖ * ‖A i j‖ := by
  rw [jacobiPencil_apply, ite_eq_right hij]
  nlinarith [norm_nonneg (A i j)]

omit [Fintype n] in
/-- The diagonal entries of $\mu D - E - F$ have absolute value $|\mu| \, |a_{ii}|$. -/
private theorem jacobiPencil_norm_diag (A : Matrix n n 𝕜) (μ : 𝕜) (i : n) :
    ‖(μ • diagPart A + strictLower A + strictUpper A) i i‖ = ‖μ‖ * ‖A i i‖ := by
  rw [jacobiPencil_apply, ite_eq_left rfl, norm_mul]

omit [Fintype n] in
/-- An off-diagonal entry of $\mu D - E - F$ is nonzero where the entry of $A$ is nonzero. -/
private theorem jacobiPencil_ne_zero {A : Matrix n n 𝕜} (μ : 𝕜) {i j : n} (hij : i ≠ j)
    (hAij : A i j ≠ 0) : (μ • diagPart A + strictLower A + strictUpper A) i j ≠ 0 := by
  rwa [jacobiPencil_apply, ite_eq_right hij]

omit [Fintype n] in
/-- If $|\lambda| \ge 1$, the off-diagonal entries of $\lambda (D - E) - F$ have absolute value at
most $|\lambda|$ times those of $A$. -/
private theorem gaussSeidelPencil_norm_le {A : Matrix n n 𝕜} {l : 𝕜} (hl : 1 ≤ ‖l‖) (i j : n)
    (_hij : i ≠ j) :
    ‖(l • (diagPart A + strictLower A) + strictUpper A) i j‖ ≤ ‖l‖ * ‖A i j‖ := by
  rw [gaussSeidelPencil_apply]
  split_ifs with hji
  · exact le_of_eq (norm_mul _ _)
  · nlinarith [norm_nonneg (A i j)]

omit [Fintype n] in
/-- The diagonal entries of $\lambda (D - E) - F$ have absolute value $|\lambda| \, |a_{ii}|$. -/
private theorem gaussSeidelPencil_norm_diag (A : Matrix n n 𝕜) (l : 𝕜) (i : n) :
    ‖(l • (diagPart A + strictLower A) + strictUpper A) i i‖ = ‖l‖ * ‖A i i‖ := by
  rw [gaussSeidelPencil_apply, ite_eq_left le_rfl, norm_mul]

omit [Fintype n] in
/-- For $\lambda \neq 0$, an entry of $\lambda (D - E) - F$ is nonzero where the entry of $A$ is
nonzero. -/
private theorem gaussSeidelPencil_ne_zero {A : Matrix n n 𝕜} {l : 𝕜} (hl : l ≠ 0) (i j : n)
    (hAij : A i j ≠ 0) : (l • (diagPart A + strictLower A) + strictUpper A) i j ≠ 0 := by
  rw [gaussSeidelPencil_apply]
  split_ifs
  · exact mul_ne_zero hl hAij
  · exact hAij

end Pencil

section Spectral

omit [LinearOrder n] in
/-- Every point of the spectrum of a complex square matrix is an eigenvalue of its linear map. -/
private theorem hasEigenvalue_toLin'_of_mem_spectrum {M : Matrix n n ℂ} {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ M) : Module.End.HasEigenvalue (Matrix.toLin' M) μ := by
  rw [Module.End.hasEigenvalue_iff_mem_spectrum,
    show Matrix.toLin' M = Matrix.toLinAlgEquiv' M from rfl, AlgEquiv.spectrum_eq]
  exact hμ

omit [LinearOrder n] in
/-- If $0 \le r < 1$ and every point of the spectrum of a complex square matrix has modulus at most
$r$, then its spectral radius is less than $1$. -/
private theorem spectralRadius_lt_one_of_forall_norm_le {M : Matrix n n ℂ} {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (h : ∀ μ ∈ spectrum ℂ M, ‖μ‖ ≤ r) : spectralRadius ℂ M < 1 := by
  have hrn : (r.toNNReal : ℝ) = r := Real.coe_toNNReal r hr0
  have hle : spectralRadius ℂ M ≤ (r.toNNReal : ENNReal) := by
    rw [spectralRadius_eq_of_unital]
    exact iSup₂_le fun μ hμ => ENNReal.coe_le_coe.mpr (by
      rw [← NNReal.coe_le_coe, coe_nnnorm, hrn]
      exact h μ hμ)
  refine hle.trans_lt ?_
  rw [← ENNReal.coe_one, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, hrn, NNReal.coe_one]
  exact hr1

omit [LinearOrder n] [DecidableEq n] in
/-- Over an empty index set every matrix is invertible, so its spectrum is empty and its spectral
radius is $0$. -/
private theorem spectralRadius_lt_one_of_isEmpty [IsEmpty n] (M : Matrix n n ℂ) :
    spectralRadius ℂ M < 1 := by
  have : Subsingleton (Matrix n n ℂ) := ⟨fun _ _ => by ext i; exact isEmptyElim i⟩
  simp

/-- Let $A$ be a complex square matrix with invertible diagonal that is strictly diagonally dominant
by rows. Then the Jacobi iteration matrix has spectral radius $\rho(G_J) < 1$. This is the
Jacobi part of [saad2003iterative], Theorem 4.9.

The matrix $G_J$ is the iteration operator of `Matrix.jacobiSplitting`. -/
theorem jacobi_spectralRadius_lt_one (A : Matrix n n ℂ) (hA : A.IsStrictDiagDominant)
    (h : IsUnit (diagPart A)) : spectralRadius ℂ (jacobiSplitting A h).iterationOperator < 1 := by
  rcases isEmpty_or_nonempty n with _ | _
  · exact spectralRadius_lt_one_of_isEmpty _
  refine spectralRadius_lt_one_of_forall_norm_le (jacobiContraction_nonneg A)
    hA.jacobiContraction_lt_one fun μ hμ => ?_
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball (hasEigenvalue_toLin'_of_mem_spectrum hμ)
  rw [Metric.mem_closedBall, jacobi_iterationOperator_apply, ite_eq_left rfl,
    dist_zero_right] at hk
  refine hk.trans (le_trans (le_of_eq ?_) (div_le_jacobiContraction A k))
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun j hj =>
    norm_jacobi_iterationOperator_apply A h (Finset.ne_of_mem_erase hj)

/-- Let $A$ be a complex square matrix with invertible diagonal that is strictly diagonally dominant
by rows. Then the Gauss–Seidel iteration matrix has spectral radius $\rho(G_{GS}) < 1$. This is
the Gauss–Seidel part of [saad2003iterative], Theorem 4.9.

The proof is the eigenvector argument of [saad2003iterative]. If $G_{GS} x = \mu x$, then
$F x = \mu (D - E) x$. At a row $i$ where $\|x\|_\infty$ is attained, this gives
$|\mu| (|a_{ii}| - \sigma_1) \le \sigma_2$ with $\sigma_1 = \sum_{j<i} |a_{ij}|$ and
$\sigma_2 = \sum_{j>i} |a_{ij}|$. Then strict dominance gives $|\mu| \le q_\infty < 1$ for the
Jacobi constant $q_\infty$ (`Matrix.jacobiContraction`). -/
theorem gaussSeidel_spectralRadius_lt_one (A : Matrix n n ℂ) (hA : A.IsStrictDiagDominant)
    (h : IsUnit (diagPart A)) :
    spectralRadius ℂ (gaussSeidelSplitting A h).iterationOperator < 1 := by
  rcases isEmpty_or_nonempty n with _ | _
  · exact spectralRadius_lt_one_of_isEmpty _
  refine spectralRadius_lt_one_of_forall_norm_le (jacobiContraction_nonneg A)
    hA.jacobiContraction_lt_one fun μ hμ => ?_
  -- `(D - E) G_GS = F` in Saad's letters, i.e. `(D + L) G = -U` here
  have hML := diagPart_add_strictLower_mul_gaussSeidel A h
  obtain ⟨v, hveig, hvne⟩ := (hasEigenvalue_toLin'_of_mem_spectrum hμ).exists_hasEigenvector
  have hGv : (gaussSeidelSplitting A h).iterationOperator *ᵥ v = μ • v :=
    Module.End.mem_eigenspace_iff.mp hveig
  have hkey : -(strictUpper A) *ᵥ v = μ • ((diagPart A + strictLower A) *ᵥ v) := by
    rw [← hML, ← mulVec_mulVec, hGv, mulVec_smul]
  -- the row where `‖v‖_∞` is attained
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty fun j => ‖v j‖
  have hle : ∀ j, ‖v j‖ ≤ ‖v i‖ := fun j =>
    hi ▸ Finset.le_sup' (fun j => ‖v j‖) (Finset.mem_univ j)
  have hvi : v i ≠ 0 := by
    contrapose hvne
    ext j
    rw [Pi.zero_apply, ← norm_le_zero_iff]
    exact (hle j).trans (norm_le_zero_iff.mpr hvne)
  have hvipos : 0 < ‖v i‖ := norm_pos_iff.mpr hvi
  set s1 := ∑ j ∈ Finset.univ.filter (· < i), ‖A i j‖ with hs1
  set s2 := ∑ j ∈ Finset.univ.filter (i < ·), ‖A i j‖ with hs2
  have hs1nn : 0 ≤ s1 := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hs2nn : 0 ≤ s2 := Finset.sum_nonneg fun _ _ => norm_nonneg _
  -- the scalar identity in row `i`
  have hrow : μ * (A i i * v i) =
      -(∑ j ∈ Finset.univ.filter (i < ·), A i j * v j) -
        μ * ∑ j ∈ Finset.univ.filter (· < i), A i j * v j := by
    have := congrFun hkey i
    rw [neg_mulVec, Pi.neg_apply, strictUpper_mulVec_apply, Pi.smul_apply, smul_eq_mul,
      diagPart_add_strictLower_mulVec_apply] at this
    rw [mul_add] at this
    linear_combination -this
  -- the resulting inequality between the row sums
  have hbound : ‖μ‖ * ‖A i i‖ * ‖v i‖ ≤ s2 * ‖v i‖ + ‖μ‖ * (s1 * ‖v i‖) := by
    have h1 : ‖μ * (A i i * v i)‖ = ‖μ‖ * ‖A i i‖ * ‖v i‖ := by
      rw [norm_mul, norm_mul, mul_assoc]
    rw [← h1, hrow]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_neg, norm_mul]
    gcongr
    · exact norm_sum_mul_le A v i _ hle
    · exact norm_sum_mul_le A v i _ hle
  have hmul : ‖μ‖ * ‖A i i‖ ≤ s2 + ‖μ‖ * s1 := by
    have := hbound
    nlinarith [hvipos]
  -- strict dominance, in the split form
  have hdom : s1 + s2 < ‖A i i‖ := by
    have := hA i
    rwa [sum_erase_eq_sum_lt_add_sum_gt] at this
  have hq : s1 + s2 ≤ jacobiContraction A * ‖A i i‖ := by
    have hpos : 0 < ‖A i i‖ := norm_pos_iff.mpr (hA.diag_ne_zero i)
    rw [← div_le_iff₀ hpos, ← sum_erase_eq_sum_lt_add_sum_gt]
    exact div_le_jacobiContraction A i
  have hq1 : jacobiContraction A < 1 := hA.jacobiContraction_lt_one
  have hpos : 0 < ‖A i i‖ - s1 := by linarith
  refine le_of_mul_le_mul_right ?_ hpos
  nlinarith [norm_nonneg μ, mul_nonneg (by linarith : (0:ℝ) ≤ 1 - jacobiContraction A) hs1nn]

/-- Let $A$ be a complex square matrix with invertible diagonal that is strictly diagonally dominant
by columns, $\sum_{i \neq j} |a_{ij}| < |a_{jj}|$ for every $j$. Then the Jacobi iteration
matrix has spectral radius $\rho(G_J) < 1$ ([kress1998numerical], Problem 4.4).

The Jacobi iteration matrix of $A$ is similar, through $D$, to the transpose of the Jacobi
iteration matrix of $A^T$, and $A^T$ is strictly diagonally dominant by rows. -/
theorem jacobi_spectralRadius_lt_one_of_col (A : Matrix n n ℂ) (hA : A.IsStrictColDiagDominant)
    (h : IsUnit (diagPart A)) : spectralRadius ℂ (jacobiSplitting A h).iterationOperator < 1 := by
  have hAT : Aᵀ.IsStrictDiagDominant := (IsStrictColDiagDominant.transpose_iff A).mpr hA
  have hdiag : diagPart Aᵀ = diagPart A := by ext i j; simp
  have hT : IsUnit (diagPart Aᵀ) := by rw [hdiag]; exact h
  have hinvT : (Ring.inverse (diagPart A))ᵀ = Ring.inverse (diagPart A) := by
    rw [← nonsing_inv_eq_ringInverse, inv_diagPart h, diagonal_transpose]
  have hDinv : diagPart A * Ring.inverse (diagPart A) = 1 := Ring.mul_inverse_cancel _ h
  have key : ((jacobiSplitting A h).iterationOperator)ᵀ =
      diagPart A * (jacobiSplitting Aᵀ hT).iterationOperator * Ring.inverse (diagPart A) := by
    change (1 - Ring.inverse (diagPart A) * A)ᵀ =
      diagPart A * (1 - Ring.inverse (diagPart Aᵀ) * Aᵀ) * Ring.inverse (diagPart A)
    rw [hdiag, transpose_sub, transpose_one, transpose_mul, hinvT, mul_sub, mul_one, ← mul_assoc,
      hDinv, one_mul, sub_mul, hDinv]
  have hspec : spectrum ℂ ((jacobiSplitting A h).iterationOperator)ᵀ =
      spectrum ℂ (jacobiSplitting Aᵀ hT).iterationOperator := by
    rw [key]
    conv_lhs => rw [← h.unit_spec, Ring.inverse_unit]
    exact spectrum.units_conjugate
  calc spectralRadius ℂ (jacobiSplitting A h).iterationOperator
      = spectralRadius ℂ ((jacobiSplitting A h).iterationOperator)ᵀ :=
        (spectralRadius_transpose _).symm
    _ = spectralRadius ℂ (jacobiSplitting Aᵀ hT).iterationOperator := by
        simp only [spectralRadius_eq_of_unital, hspec]
    _ < 1 := jacobi_spectralRadius_lt_one Aᵀ hAT hT

/-- **SOR under strict row dominance.** Let $A$ be a complex square matrix with invertible diagonal
that is strictly diagonally dominant by rows, and let $\omega$ be real with $0 < \omega \le 1$.
Then the SOR iteration matrix has spectral radius $\rho(G_\omega) < 1$
([quarteroni2000numerical], Property 4.3, last sentence).

The proof is the argument of `Matrix.gaussSeidel_spectralRadius_lt_one`. An eigenpair
$G_\omega x = \lambda x$ gives $((1 - \omega) D + \omega F) x = \lambda (D - \omega E) x$. At a
row $i$ where $\|x\|_\infty$ is attained, $|\lambda - (1 - \omega)| \, |a_{ii}| \le \omega
\sigma_2 + |\lambda| \omega \sigma_1$, with $\sigma_1 = \sum_{j<i} |a_{ij}|$ and
$\sigma_2 = \sum_{j>i} |a_{ij}|$. For $|\lambda| \ge 1$, the left side is at least
$\omega |\lambda| \, |a_{ii}|$ and the right side is at most
$\omega |\lambda| (\sigma_1 + \sigma_2)$, which contradicts strict dominance. The matrix
$G_\omega$ is the iteration operator of `Matrix.sorSplitting` at the complex number $\omega$. -/
theorem sorSplitting_spectralRadius_lt_one_of_le_one (A : Matrix n n ℂ)
    (hA : A.IsStrictDiagDominant) (h : IsUnit (diagPart A)) {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1) :
    spectralRadius ℂ
      (sorSplitting A h (Complex.ofReal_ne_zero.mpr hω0.ne')).iterationOperator < 1 := by
  set hω : (ω : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hω0.ne'
  rcases isEmpty_or_nonempty n with _ | _
  · exact spectralRadius_lt_one_of_isEmpty _
  refine spectralRadius_lt_one_of_forall_norm_lt fun μ hμ => ?_
  by_contra hcon
  rw [not_lt] at hcon
  -- `(D + ω L) G_ω = (1 - ω) D - ω U`
  have hML : (diagPart A + (ω : ℂ) • strictLower A) * (sorSplitting A h hω).iterationOperator =
      (1 - (ω : ℂ)) • diagPart A - (ω : ℂ) • strictUpper A := by
    rw [sorSplitting_iterationOperator, mul_nonsing_inv_cancel_left _ _
      ((isUnit_iff_isUnit_det _).mp (isUnit_diagPart_add_smul_strictLower h _))]
  obtain ⟨v, hveig, hvne⟩ := (hasEigenvalue_toLin'_of_mem_spectrum hμ).exists_hasEigenvector
  have hGv : (sorSplitting A h hω).iterationOperator *ᵥ v = μ • v :=
    Module.End.mem_eigenspace_iff.mp hveig
  have hkey : ((1 - (ω : ℂ)) • diagPart A - (ω : ℂ) • strictUpper A) *ᵥ v =
      μ • ((diagPart A + (ω : ℂ) • strictLower A) *ᵥ v) := by
    rw [← hML, ← mulVec_mulVec, hGv, mulVec_smul]
  -- the row where `‖v‖_∞` is attained
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty fun j => ‖v j‖
  have hle : ∀ j, ‖v j‖ ≤ ‖v i‖ := fun j =>
    hi ▸ Finset.le_sup' (fun j => ‖v j‖) (Finset.mem_univ j)
  have hvi : v i ≠ 0 := by
    contrapose hvne
    ext j
    rw [Pi.zero_apply, ← norm_le_zero_iff]
    exact (hle j).trans (norm_le_zero_iff.mpr hvne)
  have hvipos : 0 < ‖v i‖ := norm_pos_iff.mpr hvi
  set s1 := ∑ j ∈ Finset.univ.filter (· < i), ‖A i j‖ with hs1
  set s2 := ∑ j ∈ Finset.univ.filter (i < ·), ‖A i j‖ with hs2
  have hs2nn : 0 ≤ s2 := Finset.sum_nonneg fun _ _ => norm_nonneg _
  -- the scalar identity in row `i`
  have hrow : (μ - (1 - (ω : ℂ))) * (A i i * v i) =
      -((ω : ℂ) * ∑ j ∈ Finset.univ.filter (i < ·), A i j * v j) -
        μ * (ω : ℂ) * ∑ j ∈ Finset.univ.filter (· < i), A i j * v j := by
    have := congrFun hkey i
    simp only [sub_mulVec, add_mulVec, smul_mulVec, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      diagPart_mulVec_apply, strictLower_mulVec_apply, strictUpper_mulVec_apply,
      smul_eq_mul] at this
    linear_combination -this
  -- the resulting inequality between the row sums
  have hbound : ‖μ - (1 - (ω : ℂ))‖ * ‖A i i‖ * ‖v i‖ ≤
      ω * (s2 * ‖v i‖) + ‖μ‖ * ω * (s1 * ‖v i‖) := by
    have h1 : ‖(μ - (1 - (ω : ℂ))) * (A i i * v i)‖ = ‖μ - (1 - (ω : ℂ))‖ * ‖A i i‖ * ‖v i‖ := by
      rw [norm_mul, norm_mul, mul_assoc]
    rw [← h1, hrow]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_neg, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hω0]
    gcongr
    · exact norm_sum_mul_le A v i _ hle
    · exact norm_sum_mul_le A v i _ hle
  have hmul : ‖μ - (1 - (ω : ℂ))‖ * ‖A i i‖ ≤ ω * s2 + ‖μ‖ * ω * s1 := by
    have := hbound
    nlinarith [hvipos]
  -- `|μ - (1 - ω)| ≥ ω |μ|` for `|μ| ≥ 1` and `ω ≤ 1`
  have hlow : ω * ‖μ‖ ≤ ‖μ - (1 - (ω : ℂ))‖ := by
    have h1 : ‖μ‖ - ‖(1 - (ω : ℂ))‖ ≤ ‖μ - (1 - (ω : ℂ))‖ := norm_sub_norm_le _ _
    have h2 : ‖(1 - (ω : ℂ))‖ = 1 - ω := by
      rw [show (1 - (ω : ℂ)) = ((1 - ω : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    nlinarith
  -- strict dominance, in the split form
  have hdom : s1 + s2 < ‖A i i‖ := by
    have := hA i
    rwa [sum_erase_eq_sum_lt_add_sum_gt] at this
  have hμpos : 0 < ‖μ‖ := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hlow (norm_nonneg (A i i)),
    mul_le_mul_of_nonneg_left hcon (mul_nonneg hω0.le hs2nn),
    mul_lt_mul_of_pos_left hdom (mul_pos hω0 hμpos)]

/-- Let $A$ be a complex square matrix with invertible diagonal that is irreducibly diagonally
dominant: its nonzero pattern is irreducible, every row is weakly diagonally dominant, and at
least one row is strictly diagonally dominant. Then the Jacobi iteration matrix has spectral
radius $\rho(G_J) < 1$. This is the irreducible part of [saad2003iterative], Theorem 4.9, for
Jacobi.

The hypothesis is `Matrix.IsIrreduciblyDiagDominant`. An eigenvalue $\mu$ of $G_J$ with
$|\mu| \ge 1$ would make the pencil $\mu D - E - F$, which is $A$ with its diagonal scaled by
$\mu$, irreducibly diagonally dominant. Then the pencil is nonsingular by Corollary 4.8 of
[saad2003iterative], but it maps the eigenvector to $0$. -/
theorem IsIrreduciblyDiagDominant.jacobi_spectralRadius_lt_one {A : Matrix n n ℂ}
    (hA : A.IsIrreduciblyDiagDominant) (h : IsUnit (diagPart A)) :
    spectralRadius ℂ (jacobiSplitting A h).iterationOperator < 1 := by
  refine spectralRadius_lt_one_of_forall_norm_lt fun μ hμ => ?_
  by_contra hge
  rw [not_lt] at hge
  have hpos : (0 : ℝ) < ‖μ‖ := lt_of_lt_of_le zero_lt_one hge
  obtain ⟨x, hx, hxeq⟩ := exists_mulVec_eq_zero_of_mem_spectrum hμ
  obtain ⟨i₀, hi₀⟩ := hA.exists_strict
  have hBx : (μ • diagPart A + strictLower A + strictUpper A) *ᵥ x = 0 := by
    rw [← diagPart_mul_jacobi_resolvent A h μ, ← mulVec_mulVec, hxeq, mulVec_zero]
  have hunit : IsUnit (μ • diagPart A + strictLower A + strictUpper A) :=
    hA.irreducible.isUnit_of_dominant (fun i j hij hAij => jacobiPencil_ne_zero μ hij hAij)
      (dominant_of_norm_le (jacobiPencil_norm_le hge) (jacobiPencil_norm_diag A μ)
        (norm_nonneg μ) hA.dominant)
      ⟨i₀, strict_of_norm_le (jacobiPencil_norm_le hge) (jacobiPencil_norm_diag A μ) hpos hi₀⟩
  exact hx (eq_zero_of_isUnit_of_mulVec_eq_zero hunit hBx)

/-- Let $A$ be a complex square matrix with invertible diagonal that is irreducibly diagonally
dominant. Then the Gauss–Seidel iteration matrix has spectral radius $\rho(G_{GS}) < 1$. This is
the irreducible part of [saad2003iterative], Theorem 4.9, for Gauss–Seidel.

The pencil is now $\lambda (D - E) - F$, which is $A$ with its whole lower triangle scaled by
$\lambda$. For $|\lambda| \ge 1$ it is again irreducibly diagonally dominant, so it is
nonsingular by Corollary 4.8 of [saad2003iterative]. -/
theorem IsIrreduciblyDiagDominant.gaussSeidel_spectralRadius_lt_one {A : Matrix n n ℂ}
    (hA : A.IsIrreduciblyDiagDominant) (h : IsUnit (diagPart A)) :
    spectralRadius ℂ (gaussSeidelSplitting A h).iterationOperator < 1 := by
  refine spectralRadius_lt_one_of_forall_norm_lt fun l hl => ?_
  by_contra hge
  rw [not_lt] at hge
  have hpos : (0 : ℝ) < ‖l‖ := lt_of_lt_of_le zero_lt_one hge
  obtain ⟨x, hx, hxeq⟩ := exists_mulVec_eq_zero_of_mem_spectrum hl
  obtain ⟨i₀, hi₀⟩ := hA.exists_strict
  have hBx : (l • (diagPart A + strictLower A) + strictUpper A) *ᵥ x = 0 := by
    rw [← diagPart_add_strictLower_mul_gaussSeidel_resolvent A h l, ← mulVec_mulVec, hxeq,
      mulVec_zero]
  have hunit : IsUnit (l • (diagPart A + strictLower A) + strictUpper A) :=
    hA.irreducible.isUnit_of_dominant
      (fun i j _ hAij => gaussSeidelPencil_ne_zero (norm_pos_iff.mp hpos) i j hAij)
      (dominant_of_norm_le (gaussSeidelPencil_norm_le hge) (gaussSeidelPencil_norm_diag A l)
        (norm_nonneg l) hA.dominant)
      ⟨i₀, strict_of_norm_le (gaussSeidelPencil_norm_le hge) (gaussSeidelPencil_norm_diag A l)
        hpos hi₀⟩
  exact hx (eq_zero_of_isUnit_of_mulVec_eq_zero hunit hBx)

/-- Let $A$ be a complex square matrix with invertible diagonal that is strictly diagonally dominant
by columns. Then the Gauss–Seidel iteration matrix has spectral radius $\rho(G_{GS}) < 1$
([saad2003iterative], Theorem 4.9 read by columns; [kress1998numerical], Problem 4.4).

For $|\lambda| \ge 1$, the pencil $\lambda (D - E) - F$ is strictly diagonally dominant by
columns, so it is nonsingular. -/
theorem gaussSeidel_spectralRadius_lt_one_of_col (A : Matrix n n ℂ)
    (hA : A.IsStrictColDiagDominant) (h : IsUnit (diagPart A)) :
    spectralRadius ℂ (gaussSeidelSplitting A h).iterationOperator < 1 := by
  refine spectralRadius_lt_one_of_forall_norm_lt fun l hl => ?_
  by_contra hge
  rw [not_lt] at hge
  have hpos : (0 : ℝ) < ‖l‖ := lt_of_lt_of_le zero_lt_one hge
  obtain ⟨x, hx, hxeq⟩ := exists_mulVec_eq_zero_of_mem_spectrum hl
  have hBx : (l • (diagPart A + strictLower A) + strictUpper A) *ᵥ x = 0 := by
    rw [← diagPart_add_strictLower_mul_gaussSeidel_resolvent A h l, ← mulVec_mulVec, hxeq,
      mulVec_zero]
  have hunit : IsUnit (l • (diagPart A + strictLower A) + strictUpper A) :=
    (isStrictColDiagDominant_of_norm_le (gaussSeidelPencil_norm_le hge)
      (gaussSeidelPencil_norm_diag A l) hpos hA).isUnit
  exact hx (eq_zero_of_isUnit_of_mulVec_eq_zero hunit hBx)

end Spectral

section Real

/-!
### The real-matrix forms

For a real matrix the spectral radius is `Matrix.complexSpectralRadius`, the spectral radius of the
complexification. Each complex statement above transports along
`Matrix.complexify_jacobi_iterationOperator` and `Matrix.complexify_gaussSeidel_iterationOperator`,
once the dominance hypothesis is carried to $\mathbb{C}$ by the complexification lemmas of
`Numlib.LinearAlgebra.Matrix.DiagDominant`.
-/

variable {A : Matrix n n ℝ}

/-- Let $A$ be a real square matrix with invertible diagonal that is strictly diagonally dominant by
rows. Then the Jacobi iteration matrix has complex spectral radius $\rho(G_J) < 1$. This is the
Jacobi part of [saad2003iterative], Theorem 4.9, for a real matrix. -/
theorem jacobi_complexSpectralRadius_lt_one (hA : A.IsStrictDiagDominant)
    (h : IsUnit (diagPart A)) :
    complexSpectralRadius (jacobiSplitting A h).iterationOperator < 1 := by
  have h' := isUnit_diagPart_complexify h
  rw [complexSpectralRadius, complexify_jacobi_iterationOperator A h h']
  exact jacobi_spectralRadius_lt_one _ (isStrictDiagDominant_complexify hA) h'

/-- Let $A$ be a real square matrix with invertible diagonal that is strictly diagonally dominant by
rows. Then the Gauss–Seidel iteration matrix has complex spectral radius $\rho(G_{GS}) < 1$.
This is the Gauss–Seidel part of [saad2003iterative], Theorem 4.9, for a real matrix. -/
theorem gaussSeidel_complexSpectralRadius_lt_one (hA : A.IsStrictDiagDominant)
    (h : IsUnit (diagPart A)) :
    complexSpectralRadius (gaussSeidelSplitting A h).iterationOperator < 1 := by
  have h' := isUnit_diagPart_complexify h
  rw [complexSpectralRadius, complexify_gaussSeidel_iterationOperator A h h']
  exact gaussSeidel_spectralRadius_lt_one _ (isStrictDiagDominant_complexify hA) h'

/-- **SOR under strict row dominance, for a real matrix.** Let $A$ be a real square matrix with
invertible diagonal that is strictly diagonally dominant by rows, and let $0 < \omega \le 1$.
Then the SOR iteration matrix has complex spectral radius $\rho(G_\omega) < 1$
([quarteroni2000numerical], Property 4.3, last sentence). -/
theorem sorSplitting_complexSpectralRadius_lt_one_of_le_one (hA : A.IsStrictDiagDominant)
    (h : IsUnit (diagPart A)) {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1) :
    complexSpectralRadius (sorSplitting A h hω0.ne').iterationOperator < 1 := by
  have h' := isUnit_diagPart_complexify h
  rw [complexSpectralRadius, complexify_sor_iterationOperator A h h']
  exact sorSplitting_spectralRadius_lt_one_of_le_one _ (isStrictDiagDominant_complexify hA) h'
    hω0 hω1

/-- Let $A$ be a real square matrix with invertible diagonal that is strictly diagonally dominant by
columns. Then the Jacobi iteration matrix has complex spectral radius $\rho(G_J) < 1$. This is
`Matrix.jacobi_spectralRadius_lt_one_of_col` for a real matrix. -/
theorem jacobi_complexSpectralRadius_lt_one_of_col (hA : A.IsStrictColDiagDominant)
    (h : IsUnit (diagPart A)) :
    complexSpectralRadius (jacobiSplitting A h).iterationOperator < 1 := by
  have h' := isUnit_diagPart_complexify h
  rw [complexSpectralRadius, complexify_jacobi_iterationOperator A h h']
  exact jacobi_spectralRadius_lt_one_of_col _ (isStrictColDiagDominant_complexify hA) h'

/-- Let $A$ be a real square matrix with invertible diagonal that is strictly diagonally dominant by
columns. Then the Gauss–Seidel iteration matrix has complex spectral radius $\rho(G_{GS}) < 1$.
This is `Matrix.gaussSeidel_spectralRadius_lt_one_of_col` for a real matrix. -/
theorem gaussSeidel_complexSpectralRadius_lt_one_of_col (hA : A.IsStrictColDiagDominant)
    (h : IsUnit (diagPart A)) :
    complexSpectralRadius (gaussSeidelSplitting A h).iterationOperator < 1 := by
  have h' := isUnit_diagPart_complexify h
  rw [complexSpectralRadius, complexify_gaussSeidel_iterationOperator A h h']
  exact gaussSeidel_spectralRadius_lt_one_of_col _ (isStrictColDiagDominant_complexify hA) h'

/-- Let $A$ be a real square matrix with invertible diagonal that is irreducibly diagonally
dominant. Then the Jacobi iteration matrix has complex spectral radius $\rho(G_J) < 1$. This is
the irreducible part of [saad2003iterative], Theorem 4.9, for Jacobi and a real matrix. -/
theorem IsIrreduciblyDiagDominant.jacobi_complexSpectralRadius_lt_one
    (hA : A.IsIrreduciblyDiagDominant) (h : IsUnit (diagPart A)) :
    complexSpectralRadius (jacobiSplitting A h).iterationOperator < 1 := by
  have h' := isUnit_diagPart_complexify h
  rw [complexSpectralRadius, complexify_jacobi_iterationOperator A h h']
  exact (isIrreduciblyDiagDominant_complexify hA).jacobi_spectralRadius_lt_one h'

/-- Let $A$ be a real square matrix with invertible diagonal that is irreducibly diagonally
dominant. Then the Gauss–Seidel iteration matrix has complex spectral radius $\rho(G_{GS}) < 1$.
This is the irreducible part of [saad2003iterative], Theorem 4.9, for Gauss–Seidel and a real
matrix. -/
theorem IsIrreduciblyDiagDominant.gaussSeidel_complexSpectralRadius_lt_one
    (hA : A.IsIrreduciblyDiagDominant) (h : IsUnit (diagPart A)) :
    complexSpectralRadius (gaussSeidelSplitting A h).iterationOperator < 1 := by
  have h' := isUnit_diagPart_complexify h
  rw [complexSpectralRadius, complexify_gaussSeidel_iterationOperator A h h']
  exact (isIrreduciblyDiagDominant_complexify hA).gaussSeidel_spectralRadius_lt_one h'

end Real

end Matrix
