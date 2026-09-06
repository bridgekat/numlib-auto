import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Krylov.Arnoldi

/-!
# The symmetric Lanczos process

For symmetric `A` the Arnoldi coefficients are real and tridiagonal ([saad2003iterative] Thm 6.19 /
[saad2011numerical] Thm 6.2), which gives the three-term recurrence `A v_j = β_j v_{j-1} + α_j v_j +
β_{j+1} v_{j+1}` ([saad2003iterative], Alg 6.15, [choi2006iterative] §2.1, [meurant2006lanczos]
§2.1, [fong2012cg] §1). Indexing is `0`-based: `alpha A b j = ⟪v_j, A v_j⟫` and `beta A b j =
h_{j+1,j} = ‖w_j‖ ≥ 0`, so `A v_{j+1} = beta j • v_j + alpha (j+1) • v_{j+1} + beta (j+1) •
v_{j+2}`.
-/

open Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Arnoldi

variable {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (b : E)
include hA

/-- For symmetric `A` the Arnoldi coefficient array is Hermitian: `h i j = conj (h j i)`. With the
Hessenberg structure of `coeff_eq_zero_of_lt` this is what forces tridiagonality. -/
theorem coeff_conj_of_isSymmetric (i j : ℕ) : coeff A b i j = starRingEnd 𝕜 (coeff A b j i) := by
  rw [coeff, coeff, inner_conj_symm, hA]

/-- Tridiagonal structure: `h i j = 0` for `j > i + 1`. -/
theorem coeff_eq_zero_of_isSymmetric {i j : ℕ} (h : i + 1 < j) : coeff A b i j = 0 := by
  rw [coeff_conj_of_isSymmetric hA b i j, coeff_eq_zero_of_lt A b h, map_zero]

/-- The diagonal Arnoldi coefficients of a symmetric operator are real, which is what lets the
Lanczos matrix be built over `ℝ`. -/
theorem coeff_diag_re_of_isSymmetric (j : ℕ) :
    coeff A b j j = (RCLike.re (coeff A b j j) : 𝕜) :=
  (RCLike.conj_eq_iff_re.1 (coeff_conj_of_isSymmetric hA b j j).symm).symm

end Arnoldi

namespace Lanczos

variable (A : E →ₗ[𝕜] E) (b : E)

/-- Diagonal Lanczos coefficient `α_j = ⟪v_j, A v_j⟫` (real for symmetric `A`). -/
noncomputable def alpha (j : ℕ) : ℝ := RCLike.re (Arnoldi.coeff A b j j)

/-- Off-diagonal Lanczos coefficient `β_j = h_{j+1,j} = ‖w_j‖ ≥ 0`. -/
noncomputable def beta (j : ℕ) : ℝ := ‖Arnoldi.w A b j‖

/-- The off-diagonal Lanczos coefficients are nonnegative, being norms. -/
theorem beta_nonneg (j : ℕ) : 0 ≤ beta A b j := norm_nonneg _

/-- The off-diagonal coefficient is the subdiagonal Arnoldi entry: `β_j = h_{j+1,j}`. Symmetry of
`A` is not needed — that entry is `‖w_j‖`, real and nonnegative for any operator. -/
theorem coe_beta (j : ℕ) : (beta A b j : 𝕜) = Arnoldi.coeff A b (j + 1) j :=
  (Arnoldi.coeff_succ_self A b j).symm

/-- The real symmetric tridiagonal Lanczos matrix `T_m` ([saad2003iterative], (6.84)). -/
noncomputable def tridiag (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) = j then alpha A b i
    else if (i : ℕ) + 1 = j then beta A b i
    else if (j : ℕ) + 1 = i then beta A b j
    else 0

/-- The `(m+1) × m` extended Lanczos matrix `T̄_m`. -/
noncomputable def tridiagExt (m : ℕ) : Matrix (Fin (m + 1)) (Fin m) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) = j then alpha A b i
    else if (i : ℕ) + 1 = j then beta A b i
    else if (j : ℕ) + 1 = i then beta A b j
    else 0

/-- Entrywise description of `T_m`. The two matrices share it: `T_m` and `T̄_m` have the same entry
function, read at different index ranges. -/
theorem tridiag_apply {m : ℕ} (i j : Fin m) :
    tridiag A b m i j =
      if (i : ℕ) = j then alpha A b i
      else if (i : ℕ) + 1 = j then beta A b i
      else if (j : ℕ) + 1 = i then beta A b j
      else 0 := rfl

/-- Entrywise description of `T̄_m`; the same entry function as `Lanczos.tridiag_apply`. -/
theorem tridiagExt_apply {m : ℕ} (i : Fin (m + 1)) (j : Fin m) :
    tridiagExt A b m i j =
      if (i : ℕ) = j then alpha A b i
      else if (i : ℕ) + 1 = j then beta A b i
      else if (j : ℕ) + 1 = i then beta A b j
      else 0 := rfl

/-- `T_m` is tridiagonal: it vanishes outside the diagonal and the two neighbouring diagonals. -/
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

/-- `T_m` is symmetric: the same `β_j` sits above and below the diagonal. -/
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

/-- The rows of `T̄_n` below the last one are the rows of `T_n`. -/
theorem mulVec_tridiagExt_castSucc {n : ℕ} (y : Fin n → 𝕜) (i : Fin n) :
    ((tridiagExt A b n).map (algebraMap ℝ 𝕜)).mulVec y i.castSucc =
      ((tridiag A b n).map (algebraMap ℝ 𝕜)).mulVec y i := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, tridiagExt, tridiag, Matrix.of_apply,
    Fin.val_castSucc]

/-- The last row of `T̄_m` has the single entry `β_m`. -/
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

/-- The diagonal coefficient is the diagonal Arnoldi entry: `α_j = h_{j,j}`. The real part taken in
`alpha` loses nothing, because for symmetric `A` that entry is already real. -/
theorem coe_alpha (j : ℕ) : (alpha A b j : 𝕜) = Arnoldi.coeff A b j j :=
  (Arnoldi.coeff_diag_re_of_isSymmetric hA b j).symm

/-- The subdiagonal entry read off the other side: `h_{j,j+1} = β_j` (real). -/
private theorem coeff_succ_eq_beta (j : ℕ) : Arnoldi.coeff A b j (j + 1) = (beta A b j : 𝕜) := by
  rw [Arnoldi.coeff_conj_of_isSymmetric hA b j (j + 1), ← coe_beta A b j, RCLike.conj_ofReal]

/-- Everything to the left of the subdiagonal drops out of the `(j+1)`-st Arnoldi expansion. -/
private theorem sum_coeff_eq_zero (j : ℕ) :
    ∑ i ∈ Finset.range j, Arnoldi.coeff A b i (j + 1) • Arnoldi.vec A b i = 0 :=
  Finset.sum_eq_zero fun i hi => by
    rw [Arnoldi.coeff_eq_zero_of_isSymmetric hA b
      (by have := Finset.mem_range.1 hi; omega), zero_smul]

/-- Three-term recurrence, first step: `A v_0 = α_0 v_0 + β_0 v_1`. -/
theorem apply_vec_zero :
    A (Arnoldi.vec A b 0) = (alpha A b 0 : 𝕜) • Arnoldi.vec A b 0 +
      (beta A b 0 : 𝕜) • Arnoldi.vec A b 1 := by
  rw [coe_alpha b hA 0, coe_beta A b 0,
    Arnoldi.apply_vec_of_le A b (j := 0) (n := 1 + 1) (by omega),
    Finset.sum_range_succ, Finset.sum_range_one]

/-- Three-term recurrence ([saad2003iterative], Alg 6.15 and the display opening §6.6.2): `A v_{j+1}
= β_j v_j + α_{j+1} v_{j+1} + β_{j+1} v_{j+2}`. -/
theorem apply_vec (j : ℕ) :
    A (Arnoldi.vec A b (j + 1)) =
      (beta A b j : 𝕜) • Arnoldi.vec A b j + (alpha A b (j + 1) : 𝕜) • Arnoldi.vec A b (j + 1) +
        (beta A b (j + 1) : 𝕜) • Arnoldi.vec A b (j + 2) := by
  rw [show j + 2 = j + 1 + 1 from rfl, coe_alpha b hA (j + 1), coe_beta A b (j + 1),
    ← coeff_succ_eq_beta b hA j,
    Arnoldi.apply_vec_of_le A b (j := j + 1) (n := j + 1 + 1 + 1) (by omega),
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    sum_coeff_eq_zero b hA j, zero_add]

/-- The algorithmic form of the recurrence: `w_{j+1} = A v_{j+1} - α_{j+1} v_{j+1} - β_j v_j`. -/
theorem w_succ_eq (j : ℕ) :
    Arnoldi.w A b (j + 1) = A (Arnoldi.vec A b (j + 1)) -
      (alpha A b (j + 1) : 𝕜) • Arnoldi.vec A b (j + 1) - (beta A b j : 𝕜) • Arnoldi.vec A b j := by
  rw [Arnoldi.w, coe_alpha b hA (j + 1), ← coeff_succ_eq_beta b hA j, Finset.sum_range_succ,
    Finset.sum_range_succ, sum_coeff_eq_zero b hA j, zero_add]
  abel

-- `hA` is not needed here: `beta` is `‖w‖` and `Arnoldi.coeff_succ_self_eq_zero_iff` is general.
set_option linter.unusedSectionVars false in
/-- Lanczos breaks down exactly at the grade: `β_j = 0` iff `grade ≤ j + 1`, so the recurrence runs
with nonzero `β` for as long as there is a new direction to find. -/
theorem beta_eq_zero_iff [FiniteDimensional 𝕜 (fullSubspace A b)] (j : ℕ) :
    beta A b j = 0 ↔ grade A b ≤ j + 1 := by
  rw [← Arnoldi.coeff_succ_self_eq_zero_iff A b j, ← coe_beta A b j, RCLike.ofReal_eq_zero]

/-- Rayleigh-quotient bound: `α_j ∈ [λmin, λmax]` when the eigenvalues of `A` are. -/
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

/-- The Arnoldi coefficients of a symmetric operator, entry by entry. -/
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

/-- `H_m = T_m` for symmetric `A` ([saad2003iterative], Thm 6.19). -/
theorem hessenbergSq_eq_map_tridiag (m : ℕ) :
    Arnoldi.hessenbergSq A b m = (tridiag A b m).map (algebraMap ℝ 𝕜) := by
  ext i j
  exact coeff_eq_ite b hA i j

/-- `H̄_m = T̄_m` for symmetric `A`: the rectangular form of [saad2003iterative], Thm 6.19. -/
theorem hessenberg_eq_map_tridiagExt (m : ℕ) :
    Arnoldi.hessenberg A b m = (tridiagExt A b m).map (algebraMap ℝ 𝕜) := by
  ext i j
  exact coeff_eq_ite b hA i j

/-- `A V_m = V_m T_m + β_m v_m e_mᵀ`, the symmetric case of [saad2003iterative], (6.6), where `H_m =
T_m` by Thm 6.19; coordinate form. Written at `m + 1` steps, so that the number of steps is positive
and the vector `v_{m+1}` that falls outside `V_{m+1}` is the one carrying the rank-one correction.
-/
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

/-- Termination ([choi2006iterative], (2.4)): at `ℓ = grade`, `A V_ℓ = V_ℓ T_ℓ` and `𝒦_ℓ` is
invariant. -/
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
