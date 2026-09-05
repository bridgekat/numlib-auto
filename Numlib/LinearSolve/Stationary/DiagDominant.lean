import Numlib.LinearSolve.Stationary.Splitting
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Diagonal dominance and convergence of Jacobi / Gauss–Seidel

Strict (row / column) diagonal dominance, invertibility, and convergence of the Jacobi and
Gauss–Seidel iterations (Saad Thm 4.6–4.9, Cor 4.8; Kress Thm 4.2–4.3, Cor 4.4 with the explicit
`‖·‖_∞` contraction constants; Atkinson–Han Ex 5.2.2).
-/

namespace Matrix

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
theorem IsStrictColDiagDominant.transpose_iff (A : Matrix n n 𝕜) :
    A.transpose.IsStrictDiagDominant ↔ A.IsStrictColDiagDominant := Iff.rfl

omit [LinearOrder n] in
theorem IsStrictDiagDominant.diag_ne_zero {A : Matrix n n 𝕜} (hA : A.IsStrictDiagDominant) (i : n) :
    A i i ≠ 0 :=
  norm_pos_iff.mp (lt_of_le_of_lt (Finset.sum_nonneg fun _ _ => norm_nonneg _) (hA i))

omit [LinearOrder n] in
theorem IsStrictDiagDominant.isUnit_diagPart {A : Matrix n n 𝕜} (hA : A.IsStrictDiagDominant) :
    IsUnit (diagPart A) :=
  (isUnit_diagPart_iff A).mpr hA.diag_ne_zero

omit [LinearOrder n] in
/-- Saad Thm 4.6 / Kress: strictly diagonally dominant matrices are invertible
(Mathlib: `Matrix.det_ne_zero_of_sum_row_lt_diag`). -/
theorem IsStrictDiagDominant.isUnit {A : Matrix n n 𝕜} (hA : A.IsStrictDiagDominant) :
    IsUnit A :=
  (isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr (det_ne_zero_of_sum_row_lt_diag hA))

/-- The Jacobi contraction constant `q_∞ = max_i ∑_{j ≠ i} |a_ij| / |a_ii|` (Kress Thm 4.2). -/
noncomputable def jacobiContraction [Nonempty n] (A : Matrix n n 𝕜) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => (∑ j ∈ Finset.univ.erase i, ‖A i j‖) / ‖A i i‖

omit [LinearOrder n] in
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

/-- Sassenfeld numbers `p_i = (∑_{j < i} |a_ij| p_j + ∑_{j > i} |a_ij|) / |a_ii|` (Kress Thm 4.3),
obtained as the solution of the lower-triangular system `(|D| - |L|) p = |U| 𝟙`. -/
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

/-- Row `i` of `(D + E) x`, with the diagonal term separated off. -/
private theorem diagPart_add_strictLower_mulVec_apply (A : Matrix n n 𝕜) (v : n → 𝕜) (i : n) :
    ((diagPart A + strictLower A) *ᵥ v) i =
      A i i * v i + ∑ j ∈ Finset.univ.filter (· < i), A i j * v j := by
  simp only [mulVec, dotProduct, add_apply, diagPart_apply, strictLower_apply, add_mul, ite_mul,
    zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    ← Finset.sum_filter]

omit [DecidableEq n] in
/-- Row `i` of `F x`. -/
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

/-- Kress Thm 4.2: `‖G_J‖_∞ = q_∞` for the Jacobi iteration matrix. -/
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

/-- Kress Thm 4.3 (Sassenfeld): `‖G_GS‖_∞ ≤ max_i p_i`.  For `y = G_GS x` the relation
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

/-- Kress Cor 4.4: under strict row dominance the Sassenfeld numbers are `≤ q_∞ < 1`. -/
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

/-- Saad Thm 4.9 (Jacobi): `ρ(G_J) < 1` for strictly diagonally dominant `A`. -/
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

/-- Saad Thm 4.9 (Gauss–Seidel): `ρ(G_GS) < 1` for strictly diagonally dominant `A`.  Saad's
eigenvector argument: if `G_GS x = μ x` then `-F x = μ (D - E) x`, and comparing the row where
`‖x‖_∞` is attained gives `|μ| (|a_ii| - σ₁) ≤ σ₂` with `σ₁ = ∑_{j<i} |a_ij|`,
`σ₂ = ∑_{j>i} |a_ij|`; strict dominance then forces `|μ| ≤ q_∞ < 1`. -/
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

/-- Column dominance also suffices for Jacobi (Kress Problem 4.4): the Jacobi matrix of `A` is
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

end Spectral

end Matrix
