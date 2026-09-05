import Numlib.LinearSolve.Stationary.Splitting
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# Diagonal dominance and convergence of Jacobi / Gauss–Seidel

Strict (row / column) diagonal dominance, invertibility, and convergence of the Jacobi and
Gauss–Seidel iterations (Saad[^saad-iterative] Thm 4.6–4.9, Cor 4.8; Kress[^kress] Thm 4.2–4.3,
Cor 4.4 with the explicit `‖·‖_∞` contraction constants; Atkinson–Han[^atkinson-han] Ex 5.2.2).

The two explicit constants are Kress's.  The *Jacobi constant*
`q_∞ = max_i ∑_{j ≠ i} |a_ij| / |a_ii|` is exactly `‖G_J‖_∞`, the `‖·‖_∞` operator norm of the
Jacobi iteration matrix `G_J`.  The *Sassenfeld numbers* `p_i`, defined by the recursion
`p_i = (∑_{j < i} |a_ij| p_j + ∑_{j > i} |a_ij|) / |a_ii|`, bound the corresponding norm
`‖G_GS‖_∞ ≤ max_i p_i` of the Gauss–Seidel iteration matrix `G_GS`.  Under strict row dominance
both constants are `< 1`, so both iterations converge.

Strict dominance in *every* row is more than convergence needs.  A matrix that is only weakly
dominant, but is *irreducible* — its nonzero pattern has a strongly connected adjacency graph,
`Matrix.IsIrreducibleAbs` — and strictly dominant in one row is still nonsingular, and Jacobi and
Gauss-Seidel still converge for it (Saad Thm 4.7, Cor 4.8, Thm 4.9).  The engine is
`Matrix.IsIrreducibleAbs.norm_diag_eq_of_mulVec_eq_zero`: at a row where the modulus of a kernel
vector is maximal, weak dominance is forced to be an equality, and the maximum then propagates
along the graph to every row.  The three convergence statements all apply it to a *pencil* — the
matrix `A` with its diagonal, or its whole lower triangle, scaled by the eigenvalue in question —
which for an eigenvalue of modulus at least one inherits the dominance of `A`, and is therefore
nonsingular; so no such eigenvalue exists.  The same pencil, with strict column dominance in
place of irreducibility, gives Gauss-Seidel under column dominance
(`Matrix.gaussSeidel_spectralRadius_lt_one_of_col`).

## References

[^saad-iterative]: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
  SIAM, 2003.
[^kress]: Rainer Kress, *Numerical Analysis*, Graduate Texts in Mathematics 181, Springer, 1998.
[^atkinson-han]: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
  Analysis Framework*, 3rd edition, Springer, 2009.
-/

namespace Matrix

open scoped NNReal ENNReal

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

section Def

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Row strict diagonal dominance: `∑_{j ≠ i} |a_ij| < |a_ii|` for every row `i`. -/
def IsStrictDiagDominant (A : Matrix n n 𝕜) : Prop :=
  ∀ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ < ‖A i i‖

/-- Column strict diagonal dominance. -/
def IsStrictColDiagDominant (A : Matrix n n 𝕜) : Prop :=
  ∀ j, ∑ i ∈ Finset.univ.erase j, ‖A i j‖ < ‖A j j‖

omit [LinearOrder n] in
/-- Column dominance of `A` is row dominance of `Aᵀ`; true by definition, and the bridge along
which the column-dominance criterion for Jacobi is deduced from the row one. -/
theorem IsStrictColDiagDominant.transpose_iff (A : Matrix n n 𝕜) :
    A.transpose.IsStrictDiagDominant ↔ A.IsStrictColDiagDominant := Iff.rfl

omit [LinearOrder n] in
/-- A strictly row diagonally dominant matrix has no zero on its diagonal: `|a_ii|` strictly
exceeds a sum of norms, hence is positive. -/
theorem IsStrictDiagDominant.diag_ne_zero {A : Matrix n n 𝕜} (hA : A.IsStrictDiagDominant) (i : n) :
    A i i ≠ 0 :=
  norm_pos_iff.mp (lt_of_le_of_lt (Finset.sum_nonneg fun _ _ => norm_nonneg _) (hA i))

omit [LinearOrder n] in
/-- The diagonal part of a strictly row diagonally dominant matrix is invertible, so the Jacobi,
Gauss–Seidel and SOR splittings of such a matrix are all defined; this is the hypothesis every
statement below carries. -/
theorem IsStrictDiagDominant.isUnit_diagPart {A : Matrix n n 𝕜} (hA : A.IsStrictDiagDominant) :
    IsUnit (diagPart A) :=
  (isUnit_diagPart_iff A).mpr hA.diag_ne_zero

omit [LinearOrder n] in
/-- Strictly diagonally dominant matrices are invertible (Saad, *Iterative Methods*, Thm 4.6;
also Kress, *Numerical Analysis*).  Mathlib: `Matrix.det_ne_zero_of_sum_row_lt_diag`. -/
theorem IsStrictDiagDominant.isUnit {A : Matrix n n 𝕜} (hA : A.IsStrictDiagDominant) :
    IsUnit A :=
  (isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr (det_ne_zero_of_sum_row_lt_diag hA))

/-- The Jacobi contraction constant `q_∞ = max_i ∑_{j ≠ i} |a_ij| / |a_ii|`
(Kress, *Numerical Analysis*, Thm 4.2). -/
noncomputable def jacobiContraction [Nonempty n] (A : Matrix n n 𝕜) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => (∑ j ∈ Finset.univ.erase i, ‖A i j‖) / ‖A i i‖

omit [LinearOrder n] in
/-- Strict row dominance says exactly that each row quotient `∑_{j ≠ i} |a_ij| / |a_ii|` is `< 1`,
so their maximum `q_∞` is too.  With `Matrix.linfty_opNorm_jacobi_iterMatrix`, which identifies
`q_∞` with `‖G_J‖_∞`, this makes the Jacobi iteration a contraction in the `‖·‖_∞` norm. -/
theorem IsStrictDiagDominant.jacobiContraction_lt_one [Nonempty n] {A : Matrix n n 𝕜}
    (hA : A.IsStrictDiagDominant) : jacobiContraction A < 1 := by
  rw [jacobiContraction, Finset.sup'_lt_iff]
  exact fun i _ => (div_lt_one (norm_pos_iff.mpr (hA.diag_ne_zero i))).mpr (hA i)

omit [LinearOrder n] in
theorem div_le_jacobiContraction [Nonempty n] (A : Matrix n n 𝕜) (i : n) :
    (∑ j ∈ Finset.univ.erase i, ‖A i j‖) / ‖A i i‖ ≤ jacobiContraction A :=
  Finset.le_sup' (fun i => (∑ j ∈ Finset.univ.erase i, ‖A i j‖) / ‖A i i‖) (Finset.mem_univ i)

omit [LinearOrder n] in
theorem jacobiContraction_nonneg [Nonempty n] (A : Matrix n n 𝕜) : 0 ≤ jacobiContraction A := by
  obtain ⟨i⟩ := ‹Nonempty n›
  refine le_trans ?_ (div_le_jacobiContraction A i)
  positivity

/-- Sassenfeld numbers `p_i = (∑_{j < i} |a_ij| p_j + ∑_{j > i} |a_ij|) / |a_ii|`
(Kress, *Numerical Analysis*, Thm 4.3), obtained as the solution of the lower-triangular system
`(|D| - |L|) p = |U| 𝟙`. -/
noncomputable def sassenfeld (A : Matrix n n 𝕜) : n → ℝ :=
  (Matrix.of fun i j => if i = j then ‖A i i‖ else if j < i then -‖A i j‖ else 0)⁻¹ *ᵥ
    fun i => ∑ j ∈ Finset.univ.filter (i < ·), ‖A i j‖

/-- The lower-triangular matrix `|D| - |L|` defining the Sassenfeld numbers. -/
private def sassenfeldMatrix (A : Matrix n n 𝕜) : Matrix n n ℝ :=
  Matrix.of fun i j => if i = j then ‖A i i‖ else if j < i then -‖A i j‖ else 0

omit [Fintype n] in
private theorem sassenfeldMatrix_apply (A : Matrix n n 𝕜) (i j : n) :
    sassenfeldMatrix A i j = if i = j then ‖A i i‖ else if j < i then -‖A i j‖ else 0 := rfl

private theorem sassenfeld_def (A : Matrix n n 𝕜) :
    sassenfeld A =
      (sassenfeldMatrix A)⁻¹ *ᵥ fun i => ∑ j ∈ Finset.univ.filter (i < ·), ‖A i j‖ := rfl

private theorem isUnit_det_sassenfeldMatrix {A : Matrix n n 𝕜} (h : IsUnit (diagPart A)) :
    IsUnit (sassenfeldMatrix A).det := by
  have hd := (isUnit_diagPart_iff A).mp h
  have hlt : (sassenfeldMatrix A).IsLowerTriangular := by
    intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
    simp [sassenfeldMatrix_apply, hij'.ne, asymm hij']
  rw [det_of_isLowerTriangular _ hlt, isUnit_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => by
    simpa [sassenfeldMatrix_apply] using norm_ne_zero_iff.mpr (hd i)

/-- The defining recursion of the Sassenfeld numbers. -/
theorem sassenfeld_eq {A : Matrix n n 𝕜} (h : IsUnit (diagPart A)) (i : n) :
    sassenfeld A i = ((∑ j ∈ Finset.univ.filter (· < i), ‖A i j‖ * sassenfeld A j) +
      ∑ j ∈ Finset.univ.filter (i < ·), ‖A i j‖) / ‖A i i‖ := by
  have hd := (isUnit_diagPart_iff A).mp h
  have hsolve : sassenfeldMatrix A *ᵥ sassenfeld A =
      fun i => ∑ j ∈ Finset.univ.filter (i < ·), ‖A i j‖ := by
    rw [sassenfeld_def, mulVec_mulVec, mul_nonsing_inv _ (isUnit_det_sassenfeldMatrix h),
      one_mulVec]
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

/-- Row `i` of `(diagPart A + strictLower A) *ᵥ v`, with the diagonal term separated off. -/
private theorem diagPart_add_strictLower_mulVec_apply (A : Matrix n n 𝕜) (v : n → 𝕜) (i : n) :
    ((diagPart A + strictLower A) *ᵥ v) i =
      A i i * v i + ∑ j ∈ Finset.univ.filter (· < i), A i j * v j := by
  simp only [mulVec, dotProduct, add_apply, diagPart_apply, strictLower_apply, add_mul, ite_mul,
    zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    ← Finset.sum_filter]

omit [DecidableEq n] in
/-- Row `i` of `strictUpper A *ᵥ v`. -/
private theorem strictUpper_mulVec_apply (A : Matrix n n 𝕜) (v : n → 𝕜) (i : n) :
    (strictUpper A *ᵥ v) i = ∑ j ∈ Finset.univ.filter (i < ·), A i j * v j := by
  simp only [mulVec, dotProduct, strictUpper_apply, ite_mul, zero_mul, ← Finset.sum_filter]

omit [Fintype n] [DecidableEq n] [LinearOrder n] in
/-- `‖∑_{j ∈ s} a_ij x_j‖ ≤ (∑_{j ∈ s} ‖a_ij‖) ‖x‖_∞`. -/
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

omit [LinearOrder n] in
/-- The inverse of the diagonal part is the diagonal matrix of the inverses. -/
private theorem inv_diagPart {A : Matrix n n 𝕜} (h : IsUnit (diagPart A)) :
    (diagPart A)⁻¹ = diagonal fun i => (A i i)⁻¹ := by
  have hd := (isUnit_diagPart_iff A).mp h
  refine inv_eq_left_inv ?_
  rw [diagPart, diagonal_mul_diagonal, ← diagonal_one]
  exact congrArg _ (funext fun i => inv_mul_cancel₀ (hd i))

/-- Entries of the Jacobi iteration matrix. -/
private theorem jacobi_iterationOperator_apply (A : Matrix n n 𝕜) (h : IsUnit (diagPart A))
    (i j : n) : (jacobiSplitting A h).iterationOperator i j =
      if i = j then 0 else -((A i i)⁻¹ * A i j) := by
  rw [jacobiSplitting_iterationOperator, inv_diagPart h]
  rcases lt_trichotomy i j with hlt | rfl | hlt
  · simp [diagonal_mul, hlt, hlt.ne, asymm hlt]
  · simp [diagonal_mul]
  · simp [diagonal_mul, hlt, hlt.ne', asymm hlt]

private theorem norm_jacobi_iterationOperator_apply (A : Matrix n n 𝕜) (h : IsUnit (diagPart A))
    {i j : n} (hij : j ≠ i) :
    ‖(jacobiSplitting A h).iterationOperator i j‖ = ‖A i j‖ / ‖A i i‖ := by
  rw [jacobi_iterationOperator_apply, ite_eq_right (Ne.symm hij), norm_neg, norm_mul, norm_inv,
    div_eq_inv_mul]

private theorem sum_norm_jacobi_iterationOperator (A : Matrix n n 𝕜) (h : IsUnit (diagPart A))
    (i : n) : ∑ j, ‖(jacobiSplitting A h).iterationOperator i j‖ =
      (∑ j ∈ Finset.univ.erase i, ‖A i j‖) / ‖A i i‖ := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), jacobi_iterationOperator_apply,
    ite_eq_left rfl, norm_zero, add_zero, Finset.sum_div]
  exact Finset.sum_congr rfl fun j hj =>
    norm_jacobi_iterationOperator_apply A h (Finset.ne_of_mem_erase hj)

/-- Kress, *Numerical Analysis*, Thm 4.2: `‖G_J‖_∞ = q_∞` for the Jacobi iteration matrix, with
`q_∞` the Jacobi constant `jacobiContraction`. -/
theorem linfty_opNorm_jacobi_iterMatrix [Nonempty n] (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) :
    ‖(jacobiSplitting A h).iterationOperator‖ = jacobiContraction A := by
  rw [linfty_opNorm_def, ← Finset.sup'_eq_sup Finset.univ_nonempty,
    Finset.apply_sup'_eq_sup'_comp Finset.univ_nonempty NNReal.toReal NNReal.coe_max,
    jacobiContraction]
  refine Finset.sup'_congr _ rfl fun i _ => ?_
  simpa using sum_norm_jacobi_iterationOperator A h i

/-- `(D - E) G_GS = F`, i.e. `(D + L) G = -U` in the `strictLower`/`strictUpper` letters. -/
private theorem diagPart_add_strictLower_mul_gaussSeidel (A : Matrix n n 𝕜)
    (h : IsUnit (diagPart A)) :
    (diagPart A + strictLower A) * (gaussSeidelSplitting A h).iterationOperator =
      -strictUpper A := by
  rw [(gaussSeidelSplitting A h).iterationOperator_eq, gaussSeidelSplitting_n, ← mul_assoc,
    show (gaussSeidelSplitting A h).m = diagPart A + strictLower A from rfl,
    Ring.mul_inverse_cancel _ (isUnit_diagPart_add_strictLower h), one_mul]

/-- The Sassenfeld numbers are nonnegative. -/
theorem sassenfeld_nonneg {A : Matrix n n 𝕜} (h : IsUnit (diagPart A)) (i : n) :
    0 ≤ sassenfeld A i := by
  induction i using WellFoundedLT.induction with
  | _ i ih =>
    rw [sassenfeld_eq h i]
    refine div_nonneg (add_nonneg (Finset.sum_nonneg fun j hj => ?_)
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)) (norm_nonneg _)
    exact mul_nonneg (norm_nonneg _) (ih j (by simpa using (Finset.mem_filter.mp hj).2))

/-- Sassenfeld's criterion (Kress, *Numerical Analysis*, Thm 4.3): `‖G_GS‖_∞ ≤ max_i p_i`, with
`p` the Sassenfeld numbers `sassenfeld`.  For `y = G_GS x` the relation
`(D - E) y = F x` gives `|y_i| ≤ (∑_{j<i} |a_ij| |y_j| + ∑_{j>i} |a_ij| ‖x‖_∞) / |a_ii|`, so
`|y_i| ≤ p_i ‖x‖_∞` by induction along the order of the index type. -/
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

/-- Splitting a row sum over `j ≠ i` into the parts below and above the diagonal. -/
private theorem sum_erase_eq_sum_lt_add_sum_gt (f : n → ℝ) (i : n) :
    ∑ j ∈ Finset.univ.erase i, f j =
      (∑ j ∈ Finset.univ.filter (· < i), f j) + ∑ j ∈ Finset.univ.filter (i < ·), f j := by
  rw [← Finset.sum_union (by
    simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun _ hj1 hj2 => absurd hj1 (asymm hj2))]
  refine Finset.sum_congr (Finset.ext fun j => ?_) fun _ _ => rfl
  simp [Finset.mem_erase, lt_or_lt_iff_ne]

/-- Kress, *Numerical Analysis*, Cor 4.4: under strict row dominance the Sassenfeld numbers are
`≤ q_∞ < 1`, so Gauss–Seidel converges at least as fast as the Jacobi bound. -/
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

section Irreducible

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Saad's irreducibility for a matrix with arbitrary entries: the adjacency graph of the nonzero
pattern is strongly connected.  It is defined as irreducibility of the entrywise absolute value,
so that Mathlib's `Matrix.IsIrreducible` — which asks for nonnegative entries — and its
characterization `Matrix.isIrreducible_iff_exists_pow_pos` by positivity of an entry of some
power apply verbatim. -/
def IsIrreducibleAbs (A : Matrix n n 𝕜) : Prop := IsIrreducible (A.map fun x => ‖x‖)

omit [Fintype n] [DecidableEq n] [LinearOrder n] in
/-- The induction principle that every use of irreducibility goes through: a property of the
indices which holds at one index and propagates along the nonzero entries of `A` holds at every
index, because the adjacency graph of an irreducible matrix has a path from any index to any
other. -/
theorem IsIrreducibleAbs.forall_of_closed {A : Matrix n n 𝕜} (hA : A.IsIrreducibleAbs)
    {P : n → Prop} (hstep : ∀ i j, P i → A i j ≠ 0 → P j) {i : n} (hi : P i) (j : n) : P j := by
  obtain ⟨p, -⟩ := Matrix.IsIrreducible.connected hA i j
  induction p with
  | nil => exact hi
  | cons p e ih =>
    refine hstep _ _ ih ?_
    have hpos := e.down
    rw [Matrix.map_apply] at hpos
    exact norm_pos_iff.mp hpos

omit [LinearOrder n] in
/-- Irreducibility in the sense of the adjacency graph is the algebraic one: between any two
indices some power of the entrywise absolute value has a positive entry. -/
theorem isIrreducibleAbs_iff (A : Matrix n n 𝕜) :
    A.IsIrreducibleAbs ↔ ∀ i j, ∃ k > 0, 0 < ((A.map fun x => ‖x‖) ^ k) i j :=
  isIrreducible_iff_exists_pow_pos fun i j => by
    rw [Matrix.map_apply]
    exact norm_nonneg _

omit [Fintype n] [DecidableEq n] [LinearOrder n] in
/-- Irreducibility is invariant under transposition. -/
@[simp] theorem isIrreducibleAbs_transpose_iff {A : Matrix n n 𝕜} :
    Aᵀ.IsIrreducibleAbs ↔ A.IsIrreducibleAbs := by
  rw [IsIrreducibleAbs, IsIrreducibleAbs, transpose_map, isIrreducible_transpose_iff]

/-- Saad's *irreducibly diagonally dominant* matrices: irreducible, weakly row diagonally
dominant, and strictly dominant in at least one row.  This is the hypothesis under which the
Gershgorin argument still gives nonsingularity and convergence of Jacobi and Gauss–Seidel, with
strict dominance in a single row instead of in all of them. -/
structure IsIrreduciblyDiagDominant (A : Matrix n n 𝕜) : Prop where
  /-- The adjacency graph of the nonzero pattern is strongly connected. -/
  irreducible : A.IsIrreducibleAbs
  /-- Every row is weakly diagonally dominant. -/
  dominant : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ ≤ ‖A i i‖
  /-- At least one row is strictly diagonally dominant. -/
  exists_strict : ∃ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ < ‖A i i‖

/-- The column form of Saad's Definition 4.5: `A` is irreducibly diagonally dominant by columns
when its transpose is by rows. -/
def IsIrreduciblyColDiagDominant (A : Matrix n n 𝕜) : Prop := Aᵀ.IsIrreduciblyDiagDominant

omit [LinearOrder n] in
/-- **Saad's Theorem 4.7**, in the form its applications use.  Let `A` be irreducible and let `B`
have a nonzero entry wherever `A` has one off the diagonal.  If `B` is weakly diagonally dominant
and annihilates a nonzero vector, then every row of `B` is an equality row.

At a row `i` where `|x_i|` is maximal, weak dominance is forced to be an equality, and the
maximum is attained again at every `j` with `b_ij ≠ 0`; the strong connectivity of `A` then
propagates the maximum, hence the equality, to every row. -/
theorem IsIrreducibleAbs.norm_diag_eq_of_mulVec_eq_zero {A B : Matrix n n 𝕜}
    (hA : A.IsIrreducibleAbs) (hAB : ∀ i j, i ≠ j → A i j ≠ 0 → B i j ≠ 0)
    (hdom : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖B i j‖ ≤ ‖B i i‖)
    {x : n → 𝕜} (hx : x ≠ 0) (hBx : B *ᵥ x = 0) (i : n) :
    ‖B i i‖ = ∑ j ∈ Finset.univ.erase i, ‖B i j‖ := by
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hx
  have hne : Nonempty n := ⟨j₀⟩
  set M : ℝ := Finset.univ.sup' Finset.univ_nonempty fun j => ‖x j‖ with hM
  have hle : ∀ j, ‖x j‖ ≤ M := fun j => Finset.le_sup' (fun j => ‖x j‖) (Finset.mem_univ j)
  have hMpos : 0 < M := lt_of_lt_of_le (norm_pos_iff.mpr hj₀) (hle j₀)
  -- the row relation at an index where the maximum modulus is attained
  have hkey : ∀ k, ‖x k‖ = M →
      ‖B k k‖ = (∑ j ∈ Finset.univ.erase k, ‖B k j‖) ∧
        ∀ j ∈ Finset.univ.erase k, B k j ≠ 0 → ‖x j‖ = M := by
    intro k hxk
    have hrow : (∑ j ∈ Finset.univ.erase k, B k j * x j) + B k k * x k = 0 := by
      have hk := congrFun hBx k
      rw [mulVec, dotProduct] at hk
      simpa using (Finset.sum_erase_add Finset.univ (fun j => B k j * x j)
        (Finset.mem_univ k)).trans (by simpa using hk)
    have h1 : ‖B k k‖ * M ≤ ∑ j ∈ Finset.univ.erase k, ‖B k j‖ * ‖x j‖ := by
      have heq : B k k * x k = -∑ j ∈ Finset.univ.erase k, B k j * x j := by
        linear_combination hrow
      calc ‖B k k‖ * M = ‖B k k * x k‖ := by rw [norm_mul, hxk]
        _ = ‖∑ j ∈ Finset.univ.erase k, B k j * x j‖ := by rw [heq, norm_neg]
        _ ≤ ∑ j ∈ Finset.univ.erase k, ‖B k j * x j‖ := norm_sum_le _ _
        _ = ∑ j ∈ Finset.univ.erase k, ‖B k j‖ * ‖x j‖ := by
            exact Finset.sum_congr rfl fun j _ => norm_mul _ _
    have h2 : ∀ j ∈ Finset.univ.erase k, ‖B k j‖ * ‖x j‖ ≤ ‖B k j‖ * M :=
      fun j _ => mul_le_mul_of_nonneg_left (hle j) (norm_nonneg _)
    have h3 : ∑ j ∈ Finset.univ.erase k, ‖B k j‖ * ‖x j‖ ≤
        (∑ j ∈ Finset.univ.erase k, ‖B k j‖) * M := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum h2
    have h4 : ‖B k k‖ = ∑ j ∈ Finset.univ.erase k, ‖B k j‖ := by
      refine le_antisymm ?_ (hdom k)
      exact le_of_mul_le_mul_right (h1.trans h3) hMpos
    refine ⟨h4, fun j hj hBkj => ?_⟩
    have h5 : ∑ j ∈ Finset.univ.erase k, ‖B k j‖ * ‖x j‖ =
        ∑ j ∈ Finset.univ.erase k, ‖B k j‖ * M := by
      refine le_antisymm (Finset.sum_le_sum h2) ?_
      rw [← Finset.sum_mul, ← h4]
      exact h1
    have h6 := (Finset.sum_eq_sum_iff_of_le h2).mp h5 j hj
    exact mul_left_cancel₀ (norm_ne_zero_iff.mpr hBkj) h6
  -- the maximum is attained everywhere, by irreducibility
  obtain ⟨k₀, -, hk₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty fun j => ‖x j‖
  have hall : ∀ j, ‖x j‖ = M := by
    refine hA.forall_of_closed (P := fun j => ‖x j‖ = M) (fun a b ha hab => ?_) (hM.trans hk₀).symm
    rcases eq_or_ne a b with rfl | hab'
    · exact ha
    · exact (hkey a ha).2 b (Finset.mem_erase.mpr ⟨hab'.symm, Finset.mem_univ b⟩)
        (hAB a b hab' hab)
  exact (hkey i (hall i)).1

omit [LinearOrder n] in
/-- **Saad's Corollary 4.8**: an irreducible matrix that is weakly diagonally dominant, with
strict dominance in at least one row, is nonsingular.  A vector in its kernel would make every
row an equality row by `Matrix.IsIrreducibleAbs.norm_diag_eq_of_mulVec_eq_zero`, against the
strict row.  Stated for a matrix `B` dominated off the diagonal by an irreducible `A`, which is
how the convergence proofs below use it. -/
theorem IsIrreducibleAbs.isUnit_of_dominant {A B : Matrix n n 𝕜} (hA : A.IsIrreducibleAbs)
    (hAB : ∀ i j, i ≠ j → A i j ≠ 0 → B i j ≠ 0)
    (hdom : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖B i j‖ ≤ ‖B i i‖)
    (hstrict : ∃ i, ∑ j ∈ Finset.univ.erase i, ‖B i j‖ < ‖B i i‖) : IsUnit B := by
  obtain ⟨i, hi⟩ := hstrict
  rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨x, hx, hBx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  exact hi.ne' (hA.norm_diag_eq_of_mulVec_eq_zero hAB hdom hx hBx i)

omit [LinearOrder n] in
/-- An irreducibly diagonally dominant matrix is nonsingular (Saad, *Iterative Methods*,
Cor 4.8). -/
theorem IsIrreduciblyDiagDominant.isUnit {A : Matrix n n 𝕜} (hA : A.IsIrreduciblyDiagDominant) :
    IsUnit A :=
  hA.irreducible.isUnit_of_dominant (fun _ _ _ hij => hij) hA.dominant hA.exists_strict

omit [LinearOrder n] in
/-- An irreducibly diagonally dominant matrix has no zero on its diagonal: a zero diagonal entry
would force its whole row to vanish, which an irreducible matrix of size at least two forbids,
while for a matrix of size one the strict row is the diagonal entry itself. -/
theorem IsIrreduciblyDiagDominant.diag_ne_zero {A : Matrix n n 𝕜}
    (hA : A.IsIrreduciblyDiagDominant) (i : n) : A i i ≠ 0 := by
  intro h0
  have hzero : ∀ j, A i j = 0 := by
    have hsum := hA.dominant i
    rw [h0, norm_zero] at hsum
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => norm_nonneg (A i j)).mp
      (le_antisymm hsum (Finset.sum_nonneg fun _ _ => norm_nonneg _))
    intro j
    rcases eq_or_ne j i with rfl | hj
    · exact h0
    · exact norm_eq_zero.mp (hall j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩))
  have hsub : ∀ j : n, j = i :=
    hA.irreducible.forall_of_closed (P := fun j => j = i)
      (fun a b ha hab => absurd (hzero b) (ha ▸ hab)) rfl
  obtain ⟨k, hk⟩ := hA.exists_strict
  rw [show Finset.univ.erase k = (∅ : Finset n) from Finset.eq_empty_of_forall_notMem fun j hj =>
    (Finset.ne_of_mem_erase hj) ((hsub j).trans (hsub k).symm), Finset.sum_empty, hsub k, h0,
    norm_zero] at hk
  exact lt_irrefl 0 hk

omit [LinearOrder n] in
/-- The diagonal part of an irreducibly diagonally dominant matrix is invertible, so the Jacobi,
Gauss–Seidel and SOR splittings of such a matrix are defined. -/
theorem IsIrreduciblyDiagDominant.isUnit_diagPart {A : Matrix n n 𝕜}
    (hA : A.IsIrreduciblyDiagDominant) : IsUnit (diagPart A) :=
  (isUnit_diagPart_iff A).mpr hA.diag_ne_zero

omit [LinearOrder n] in
/-- Strictly column diagonally dominant matrices are invertible: the transpose is strictly row
dominant, and a matrix and its transpose have the same determinant. -/
theorem IsStrictColDiagDominant.isUnit {A : Matrix n n 𝕜} (hA : A.IsStrictColDiagDominant) :
    IsUnit A := by
  have h := ((IsStrictColDiagDominant.transpose_iff A).mpr hA).isUnit
  rwa [isUnit_iff_isUnit_det, det_transpose, ← isUnit_iff_isUnit_det] at h

end Irreducible

section Pencil

variable {𝕜 : Type*} [RCLike 𝕜]

omit [Fintype n] in
/-- Entries of the pencil `μ D + E' + F'` whose singularity detects the eigenvalue `μ` of the
Jacobi iteration matrix: the diagonal of `A` is scaled by `μ` and nothing else changes. -/
private theorem jacobiPencil_apply (A : Matrix n n 𝕜) (μ : 𝕜) (i j : n) :
    (μ • diagPart A + strictLower A + strictUpper A) i j =
      if i = j then μ * A i i else A i j := by
  rcases lt_trichotomy i j with hlt | rfl | hlt
  · simp [hlt, hlt.ne, asymm hlt]
  · simp
  · simp [hlt, hlt.ne', asymm hlt]

omit [Fintype n] in
/-- Entries of the pencil `λ (D + L') + F'` whose singularity detects the eigenvalue `λ` of the
Gauss–Seidel iteration matrix: the lower triangle of `A`, diagonal included, is scaled by `λ`. -/
private theorem gaussSeidelPencil_apply (A : Matrix n n 𝕜) (l : 𝕜) (i j : n) :
    (l • (diagPart A + strictLower A) + strictUpper A) i j =
      if j ≤ i then l * A i j else A i j := by
  rcases lt_trichotomy i j with hlt | rfl | hlt
  · simp [hlt, hlt.ne, asymm hlt, not_le.mpr hlt]
  · simp
  · simp [hlt, hlt.ne', asymm hlt, hlt.le]

/-- `D (μ 1 - G_J) = μ D + E' + F'`: multiplying by the diagonal turns the Jacobi resolvent into
a pencil with the entries of `A` off the diagonal. -/
private theorem diagPart_mul_jacobi_resolvent (A : Matrix n n 𝕜) (h : IsUnit (diagPart A))
    (μ : 𝕜) :
    diagPart A * (μ • (1 : Matrix n n 𝕜) - (jacobiSplitting A h).iterationOperator) =
      μ • diagPart A + strictLower A + strictUpper A := by
  rw [jacobiSplitting_iterationOperator, mul_sub, mul_smul_comm, mul_one, neg_mul, mul_neg,
    ← mul_assoc, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp h), one_mul]
  module

/-- `(D + L') (λ 1 - G_GS) = λ (D + L') + F'`. -/
private theorem diagPart_add_strictLower_mul_gaussSeidel_resolvent (A : Matrix n n 𝕜)
    (h : IsUnit (diagPart A)) (l : 𝕜) :
    (diagPart A + strictLower A) *
        (l • (1 : Matrix n n 𝕜) - (gaussSeidelSplitting A h).iterationOperator) =
      l • (diagPart A + strictLower A) + strictUpper A := by
  rw [mul_sub, mul_smul_comm, mul_one, diagPart_add_strictLower_mul_gaussSeidel, sub_neg_eq_add]

omit [LinearOrder n] in
/-- A vector annihilated by a unit is zero. -/
private theorem eq_zero_of_isUnit_of_mulVec_eq_zero {B : Matrix n n 𝕜} (hB : IsUnit B)
    {x : n → 𝕜} (hBx : B *ᵥ x = 0) : x = 0 := by
  by_contra hx
  exact (isUnit_iff_ne_zero.mp ((isUnit_iff_isUnit_det B).mp hB))
    (Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx, hBx⟩)

omit [LinearOrder n] in
/-- A point of the spectrum is an eigenvalue: it comes with a nonzero vector in the kernel of the
resolvent. -/
private theorem exists_mulVec_eq_zero_of_mem_spectrum {M : Matrix n n 𝕜} {μ : 𝕜}
    (hμ : μ ∈ spectrum 𝕜 M) : ∃ x ≠ 0, (μ • (1 : Matrix n n 𝕜) - M) *ᵥ x = 0 := by
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero, not_not] at hμ
  exact Matrix.exists_mulVec_eq_zero_iff.mpr hμ

omit [LinearOrder n] in
/-- Weak row dominance is inherited by a matrix whose entries are dominated by `c` times those of
`A`, with equality on the diagonal. -/
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
/-- Strict row dominance is inherited in the same way, for `c > 0`. -/
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
/-- Strict column dominance is inherited in the same way, for `c > 0`. -/
private theorem col_of_norm_le {A B : Matrix n n 𝕜} {c : ℝ}
    (hoff : ∀ i j, i ≠ j → ‖B i j‖ ≤ c * ‖A i j‖) (hdiag : ∀ i, ‖B i i‖ = c * ‖A i i‖)
    (hc : 0 < c) (hA : A.IsStrictColDiagDominant) : B.IsStrictColDiagDominant := fun j => by
  calc ∑ i ∈ Finset.univ.erase j, ‖B i j‖
      ≤ ∑ i ∈ Finset.univ.erase j, c * ‖A i j‖ :=
        Finset.sum_le_sum fun i hi => hoff i j (Finset.ne_of_mem_erase hi)
    _ = c * ∑ i ∈ Finset.univ.erase j, ‖A i j‖ := by rw [Finset.mul_sum]
    _ < c * ‖A j j‖ := mul_lt_mul_of_pos_left (hA j) hc
    _ = ‖B j j‖ := (hdiag j).symm

omit [Fintype n] in
/-- The Jacobi pencil scales the diagonal only, so its off-diagonal entries are bounded by
`‖μ‖` times those of `A` as soon as `‖μ‖ ≥ 1`. -/
private theorem jacobiPencil_norm_le {A : Matrix n n 𝕜} {μ : 𝕜} (hμ : 1 ≤ ‖μ‖) (i j : n)
    (hij : i ≠ j) : ‖(μ • diagPart A + strictLower A + strictUpper A) i j‖ ≤ ‖μ‖ * ‖A i j‖ := by
  rw [jacobiPencil_apply, ite_eq_right hij]
  nlinarith [norm_nonneg (A i j)]

omit [Fintype n] in
private theorem jacobiPencil_norm_diag (A : Matrix n n 𝕜) (μ : 𝕜) (i : n) :
    ‖(μ • diagPart A + strictLower A + strictUpper A) i i‖ = ‖μ‖ * ‖A i i‖ := by
  rw [jacobiPencil_apply, ite_eq_left rfl, norm_mul]

omit [Fintype n] in
private theorem jacobiPencil_ne_zero {A : Matrix n n 𝕜} (μ : 𝕜) {i j : n} (hij : i ≠ j)
    (hAij : A i j ≠ 0) : (μ • diagPart A + strictLower A + strictUpper A) i j ≠ 0 := by
  rwa [jacobiPencil_apply, ite_eq_right hij]

omit [Fintype n] in
/-- The Gauss–Seidel pencil scales the whole lower triangle, so its off-diagonal entries are
bounded by `‖λ‖` times those of `A` as soon as `‖λ‖ ≥ 1`. -/
private theorem gaussSeidelPencil_norm_le {A : Matrix n n 𝕜} {l : 𝕜} (hl : 1 ≤ ‖l‖) (i j : n)
    (_hij : i ≠ j) :
    ‖(l • (diagPart A + strictLower A) + strictUpper A) i j‖ ≤ ‖l‖ * ‖A i j‖ := by
  rw [gaussSeidelPencil_apply]
  split_ifs with hji
  · exact le_of_eq (norm_mul _ _)
  · nlinarith [norm_nonneg (A i j)]

omit [Fintype n] in
private theorem gaussSeidelPencil_norm_diag (A : Matrix n n 𝕜) (l : 𝕜) (i : n) :
    ‖(l • (diagPart A + strictLower A) + strictUpper A) i i‖ = ‖l‖ * ‖A i i‖ := by
  rw [gaussSeidelPencil_apply, ite_eq_left le_rfl, norm_mul]

omit [Fintype n] in
private theorem gaussSeidelPencil_ne_zero {A : Matrix n n 𝕜} {l : 𝕜} (hl : l ≠ 0) (i j : n)
    (hAij : A i j ≠ 0) : (l • (diagPart A + strictLower A) + strictUpper A) i j ≠ 0 := by
  rw [gaussSeidelPencil_apply]
  split_ifs
  · exact mul_ne_zero hl hAij
  · exact hAij

end Pencil

section Spectral

omit [LinearOrder n] in
/-- Every point of the spectrum of a matrix is an eigenvalue of the associated endomorphism. -/
private theorem hasEigenvalue_toLin'_of_mem_spectrum {M : Matrix n n ℂ} {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ M) : Module.End.HasEigenvalue (Matrix.toLin' M) μ := by
  rw [Module.End.hasEigenvalue_iff_mem_spectrum,
    show Matrix.toLin' M = Matrix.toLinAlgEquiv' M from rfl, AlgEquiv.spectrum_eq]
  exact hμ

omit [LinearOrder n] in
/-- If every point of the spectrum has norm at most `r < 1`, the spectral radius is `< 1`. -/
private theorem spectralRadius_lt_one_of_forall_norm_le {M : Matrix n n ℂ} {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (h : ∀ μ ∈ spectrum ℂ M, ‖μ‖ ≤ r) : spectralRadius ℂ M < 1 := by
  have hrn : (r.toNNReal : ℝ) = r := Real.coe_toNNReal r hr0
  have hle : spectralRadius ℂ M ≤ (r.toNNReal : ENNReal) :=
    iSup₂_le fun μ hμ => ENNReal.coe_le_coe.mpr (by
      rw [← NNReal.coe_le_coe, coe_nnnorm, hrn]
      exact h μ hμ)
  refine hle.trans_lt ?_
  rw [← ENNReal.coe_one, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, hrn, NNReal.coe_one]
  exact hr1

omit [LinearOrder n] in
private theorem spectralRadius_lt_one_of_isEmpty [IsEmpty n] (M : Matrix n n ℂ) :
    spectralRadius ℂ M < 1 := by
  have : Subsingleton (Matrix n n ℂ) := ⟨fun _ _ => by ext i; exact isEmptyElim i⟩
  exact (iSup₂_le fun _ hk => absurd (isUnit_of_subsingleton _) hk).trans_lt zero_lt_one

/-- Saad, *Iterative Methods*, Thm 4.9 (Jacobi): the spectral radius satisfies `ρ(G_J) < 1` for
strictly diagonally dominant `A`. -/
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

/-- Saad, *Iterative Methods*, Thm 4.9 (Gauss–Seidel): the spectral radius satisfies
`ρ(G_GS) < 1` for strictly diagonally dominant `A`.  Saad's
eigenvector argument: in the letters `A = D - E - F` (diagonal, negated strictly lower, negated
strictly upper), if `G_GS x = μ x` then `-F x = μ (D - E) x`, and comparing the row where
`‖x‖_∞` is attained gives `|μ| (|a_ii| - σ₁) ≤ σ₂` with `σ₁ = ∑_{j<i} |a_ij|`,
`σ₂ = ∑_{j>i} |a_ij|`; strict dominance then forces `|μ| ≤ q_∞ < 1` for the Jacobi constant
`q_∞ = jacobiContraction A`. -/
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
    contrapose! hvne
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

/-- Column dominance also suffices for Jacobi (Kress, *Numerical Analysis*, Problem 4.4): the
Jacobi matrix of `A` is
similar (via `D`) to the transpose of the Jacobi matrix of `Aᵀ`, which is row dominant. -/
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
        simp only [spectralRadius, hspec]
    _ < 1 := jacobi_spectralRadius_lt_one Aᵀ hAT hT

omit [LinearOrder n] in
/-- If every point of the spectrum has norm `< 1`, so has the spectral radius: the spectrum of a
matrix over a field is finite, so the supremum is attained. -/
private theorem spectralRadius_lt_one_of_forall_lt {M : Matrix n n ℂ}
    (h : ∀ μ ∈ spectrum ℂ M, ‖μ‖ < 1) : spectralRadius ℂ M < 1 := by
  classical
  have hfin := M.finite_spectrum
  rcases (spectrum ℂ M).eq_empty_or_nonempty with he | hne
  · refine lt_of_le_of_lt (iSup₂_le fun k hk => ?_) zero_lt_one
    exact absurd (he ▸ hk) (Set.notMem_empty k)
  · obtain ⟨μ₁, hμ₁⟩ := hne
    have hmem : μ₁ ∈ hfin.toFinset := hfin.mem_toFinset.mpr hμ₁
    have hne' : hfin.toFinset.Nonempty := ⟨μ₁, hmem⟩
    refine spectralRadius_lt_one_of_forall_norm_le
      (r := hfin.toFinset.sup' hne' fun μ => ‖μ‖)
      (le_trans (norm_nonneg μ₁) (Finset.le_sup' (fun μ => ‖μ‖) hmem)) ?_ ?_
    · rw [Finset.sup'_lt_iff]
      exact fun μ hμ => h μ (hfin.mem_toFinset.mp hμ)
    · exact fun μ hμ => Finset.le_sup' (fun μ => ‖μ‖) (hfin.mem_toFinset.mpr hμ)

omit [LinearOrder n] in
/-- **Saad's Theorem 4.7**: if `A` is irreducible and an eigenvalue of `A` lies on the boundary of
the union of the Gershgorin discs, then it lies on the boundary of *every* disc, that is
`‖μ - a_ii‖ = ∑_{j ≠ i} ‖a_ij‖` for every `i`.  Being on the boundary of the union means being
outside every open disc, which is the weak dominance hypothesis of
`Matrix.IsIrreducibleAbs.norm_diag_eq_of_mulVec_eq_zero` for the resolvent `μ 1 - A`. -/
theorem IsIrreducibleAbs.norm_sub_eq_of_mem_frontier {A : Matrix n n ℂ} (hA : A.IsIrreducibleAbs)
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ A)
    (hfr : μ ∈ frontier (⋃ i, Metric.closedBall (A i i)
      (∑ j ∈ Finset.univ.erase i, ‖A i j‖))) (i : n) :
    ‖μ - A i i‖ = ∑ j ∈ Finset.univ.erase i, ‖A i j‖ := by
  have hBapp : ∀ k j, (μ • (1 : Matrix n n ℂ) - A) k j = if k = j then μ - A k k else -A k j := by
    intro k j
    rcases eq_or_ne k j with rfl | hkj
    · simp
    · simp [Matrix.one_apply_ne hkj, hkj]
  have hBnorm : ∀ k j, k ≠ j → ‖(μ • (1 : Matrix n n ℂ) - A) k j‖ = ‖A k j‖ := fun k j hkj => by
    rw [hBapp, ite_eq_right hkj, norm_neg]
  have hBdiag : ∀ k, ‖(μ • (1 : Matrix n n ℂ) - A) k k‖ = ‖μ - A k k‖ := fun k => by
    rw [hBapp, ite_eq_left rfl]
  have hsum : ∀ k, ∑ j ∈ Finset.univ.erase k, ‖(μ • (1 : Matrix n n ℂ) - A) k j‖ =
      ∑ j ∈ Finset.univ.erase k, ‖A k j‖ :=
    fun k => Finset.sum_congr rfl fun j hj => hBnorm k j (Finset.ne_of_mem_erase hj).symm
  have hnotint : μ ∉ interior (⋃ k, Metric.closedBall (A k k)
      (∑ j ∈ Finset.univ.erase k, ‖A k j‖)) := hfr.2
  have hge : ∀ k, ∑ j ∈ Finset.univ.erase k, ‖(μ • (1 : Matrix n n ℂ) - A) k j‖ ≤
      ‖(μ • (1 : Matrix n n ℂ) - A) k k‖ := by
    intro k
    rw [hsum, hBdiag]
    by_contra hlt
    refine hnotint (interior_maximal (Metric.ball_subset_closedBall.trans
      (Set.subset_iUnion (fun k => Metric.closedBall (A k k)
        (∑ j ∈ Finset.univ.erase k, ‖A k j‖)) k)) Metric.isOpen_ball ?_)
    rw [Metric.mem_ball, dist_eq_norm]
    exact not_le.mp hlt
  obtain ⟨x, hx, hBx⟩ := exists_mulVec_eq_zero_of_mem_spectrum hμ
  have hkey := hA.norm_diag_eq_of_mulVec_eq_zero
    (fun k j hkj hAkj => by rw [hBapp, ite_eq_right hkj]; simpa using hAkj) hge hx hBx i
  rwa [hBdiag, hsum] at hkey

/-- Saad, *Iterative Methods*, Thm 4.9, the irreducible half for Jacobi: an irreducibly
diagonally dominant matrix has `ρ(G_J) < 1`.  An eigenvalue `μ` of `G_J` with `‖μ‖ ≥ 1` would make
the pencil `μ D + E' + F'` — the matrix `A` with its diagonal scaled by `μ` — irreducibly
diagonally dominant, hence nonsingular by Cor 4.8, whereas it annihilates the eigenvector. -/
theorem IsIrreduciblyDiagDominant.jacobi_spectralRadius_lt_one {A : Matrix n n ℂ}
    (hA : A.IsIrreduciblyDiagDominant) (h : IsUnit (diagPart A)) :
    spectralRadius ℂ (jacobiSplitting A h).iterationOperator < 1 := by
  refine spectralRadius_lt_one_of_forall_lt fun μ hμ => ?_
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

/-- Saad, *Iterative Methods*, Thm 4.9, the irreducible half for Gauss–Seidel: an irreducibly
diagonally dominant matrix has `ρ(G_GS) < 1`.  The pencil is now `λ (D + L') + F'`, the matrix `A`
with its whole lower triangle scaled by `λ`; for `‖λ‖ ≥ 1` it is again irreducibly diagonally
dominant, hence nonsingular by Cor 4.8. -/
theorem IsIrreduciblyDiagDominant.gaussSeidel_spectralRadius_lt_one {A : Matrix n n ℂ}
    (hA : A.IsIrreduciblyDiagDominant) (h : IsUnit (diagPart A)) :
    spectralRadius ℂ (gaussSeidelSplitting A h).iterationOperator < 1 := by
  refine spectralRadius_lt_one_of_forall_lt fun l hl => ?_
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

/-- Gauss–Seidel converges under strict *column* diagonal dominance (Saad, *Iterative Methods*,
Thm 4.9 read by columns; Kress, *Numerical Analysis*, Problem 4.4).  The same pencil
`λ (D + L') + F'` is used: for `‖λ‖ ≥ 1` it is strictly column diagonally dominant, hence
nonsingular. -/
theorem gaussSeidel_spectralRadius_lt_one_of_col (A : Matrix n n ℂ)
    (hA : A.IsStrictColDiagDominant) (h : IsUnit (diagPart A)) :
    spectralRadius ℂ (gaussSeidelSplitting A h).iterationOperator < 1 := by
  refine spectralRadius_lt_one_of_forall_lt fun l hl => ?_
  by_contra hge
  rw [not_lt] at hge
  have hpos : (0 : ℝ) < ‖l‖ := lt_of_lt_of_le zero_lt_one hge
  obtain ⟨x, hx, hxeq⟩ := exists_mulVec_eq_zero_of_mem_spectrum hl
  have hBx : (l • (diagPart A + strictLower A) + strictUpper A) *ᵥ x = 0 := by
    rw [← diagPart_add_strictLower_mul_gaussSeidel_resolvent A h l, ← mulVec_mulVec, hxeq,
      mulVec_zero]
  have hunit : IsUnit (l • (diagPart A + strictLower A) + strictUpper A) :=
    (col_of_norm_le (gaussSeidelPencil_norm_le hge) (gaussSeidelPencil_norm_diag A l) hpos
      hA).isUnit
  exact hx (eq_zero_of_isUnit_of_mulVec_eq_zero hunit hBx)

end Spectral

end Matrix
