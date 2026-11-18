/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.Jordan
import Numlib.Analysis.Matrix.Function.Basic
import NumlibSurface.BenIsraelGreville.Chapter00.Section02
import NumlibSurface.BenIsraelGreville.Chapter02.Section05
import Mathlib.LinearAlgebra.Eigenspace.Zero

/-!
# The Jordan normal form

Section 0.7 of [benIsrael2003generalized] describes Jordan chains, the
normal form and its uniqueness, and the characteristic and minimal
polynomial factorizations given by the Jordan blocks.

## Deviations from the source

* **Exercise 71** (generalization). The inverse conjugation identity also
  holds for the total matrix inverse used in Lean.
* **Exercise 74** (reading). The two displayed eigenvalues are distinct.
-/

namespace BenIsraelGreville.Chapter00

open Matrix Polynomial

/-- **Equation (116)** of [benIsrael2003generalized], Chapter 0. A Jordan
block has a constant diagonal and a unit superdiagonal. -/
abbrev jordanBlock (k : ℕ) (c : ℂ) : Matrix (Fin k) (Fin k) ℂ := Matrix.jordanBlock k c

section PrincipalVectors

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Equation (119)** of [benIsrael2003generalized], Chapter 0. A principal
vector of grade $j$ is killed by the $j$th power of the shifted matrix and
survives the preceding power. -/
def IsPrincipalVector (A : Matrix n n ℂ) (c : ℂ) (j : ℕ) (x : n → ℂ) : Prop :=
  0 < j ∧ ((A - c • 1) ^ j) *ᵥ x = 0 ∧ ((A - c • 1) ^ (j - 1)) *ᵥ x ≠ 0

/-- **Section 0.7** of [benIsrael2003generalized]. Principal vectors of
grade one are precisely the nonzero eigenvectors. -/
theorem principalVector_grade_one_iff (A : Matrix n n ℂ) (c : ℂ) (x : n → ℂ) :
    IsPrincipalVector A c 1 x ↔ Module.End.HasEigenvector A.mulVecLin c x := by
  rw [hasEigenvector_iff_mulVec_eq, IsPrincipalVector]
  simp [Matrix.sub_mulVec, Matrix.smul_mulVec, sub_eq_zero]

omit [DecidableEq n] in
/-- **Equations (117)–(118)** of [benIsrael2003generalized], Chapter 0.
The first column of a Jordan intertwiner satisfies the eigenvector equation,
and each later column maps to its eigenvalue multiple plus its predecessor. -/
theorem jordanChain_col_eq {k : ℕ} (A : Matrix n n ℂ)
    (X : Matrix n (Fin (k + 1)) ℂ) (c : ℂ) (h : A * X = X * jordanBlock (k + 1) c) :
    A *ᵥ X.col 0 = c • X.col 0 ∧
      ∀ j : Fin k, A *ᵥ X.col j.succ = c • X.col j.succ + X.col j.castSucc := by
  have hCol (j : Fin (k + 1)) : A *ᵥ X.col j = X *ᵥ (jordanBlock (k + 1) c).col j := by
    rw [← col_mul_eq_mulVec_col, h, col_mul_eq_mulVec_col]
  constructor
  · have hJ : (jordanBlock (k + 1) c).col 0 = c • Pi.single (0 : Fin (k + 1)) 1 := by
      funext i
      rw [Matrix.col_apply, jordanBlock, Matrix.jordanBlock_apply, Pi.smul_apply, Pi.single_apply]
      by_cases hi : i = 0
      · simp [hi]
      · simp [hi, smul_eq_mul]
    rw [hCol, hJ, mulVec_smul, Matrix.mulVec_single_one]
  · intro j
    have hJ : (jordanBlock (k + 1) c).col j.succ =
        c • Pi.single j.succ 1 + Pi.single j.castSucc 1 := by
      funext i
      rw [Matrix.col_apply, jordanBlock, Matrix.jordanBlock_apply, Pi.add_apply, Pi.smul_apply,
        Pi.single_apply, Pi.single_apply]
      have he : i.val + 1 = j.succ.val ↔ i = j.castSucc := by
        simp [Fin.ext_iff]
      by_cases hi : i = j.succ
      · subst i
        simp [Fin.ext_iff]
      · simp only [ite_eq_right hi, he, smul_eq_mul, mul_zero, zero_add]
    rw [hCol, hJ, mulVec_add, mulVec_smul, Matrix.mulVec_single_one, Matrix.mulVec_single_one]

/-- **Equations (117)–(119)** of [benIsrael2003generalized], Chapter 0.
The columns of a full-column-rank Jordan intertwiner are principal vectors.
The preceding shifted power sends each column to the first column. -/
theorem principalVector_of_jordanChain {k : ℕ} (A : Matrix n n ℂ)
    (X : Matrix n (Fin k) ℂ) (c : ℂ) (h : A * X = X * jordanBlock k c)
    (hX : Function.Injective X.mulVec) (j : Fin k) :
    let j₀ : Fin k := ⟨0, Nat.zero_lt_of_lt j.isLt⟩
    IsPrincipalVector A c (j.val + 1) (X.col j) ∧
      ((A - c • 1) ^ j.val) *ᵥ X.col j = X.col j₀ := by
  intro j₀
  have hshift : (A - c • 1) * X = X * jordanBlock k 0 := by
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, h,
      show jordanBlock k c = jordanBlock k 0 + c • 1 from Matrix.jordanBlock_eq_add_smul_one,
      Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one,
      add_sub_cancel_right]
  have hpow (p : ℕ) : ((A - c • 1) ^ p) * X = X * (jordanBlock k 0) ^ p := by
    induction p with
    | zero => simp
    | succ p ih =>
        rw [pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc (A - c • 1), hshift,
          Matrix.mul_assoc, ← pow_succ']
  have hcol (p : ℕ) :
      ((A - c • 1) ^ p) *ᵥ X.col j = X *ᵥ ((jordanBlock k 0) ^ p).col j := by
    rw [← Matrix.mulVec_single_one X j, mulVec_mulVec, hpow, ← mulVec_mulVec,
      Matrix.mulVec_single_one]
  have hprev : ((jordanBlock k 0) ^ j.val).col j = Pi.single j₀ 1 := by
    funext i
    rw [Matrix.col_apply, Matrix.jordanBlock_zero_pow_apply, Pi.single_apply]
    have he : i.val + j.val = j.val ↔ i = j₀ := by
      rw [Fin.ext_iff]
      change i.val + j.val = j.val ↔ i.val = 0
      omega
    simp only [he]
  have hlast : ((jordanBlock k 0) ^ (j.val + 1)).col j = 0 := by
    funext i
    rw [Matrix.col_apply, Matrix.jordanBlock_zero_pow_apply, ite_eq_right (by omega)]
    rfl
  have he : ((A - c • 1) ^ j.val) *ᵥ X.col j = X.col j₀ := by
    rw [hcol, hprev, Matrix.mulVec_single_one]
  refine ⟨⟨Nat.succ_pos _, by rw [hcol, hlast, mulVec_zero], ?_⟩, he⟩
  rw [Nat.add_sub_cancel, he, ← Matrix.mulVec_single_one]
  intro hz
  have hv := hX (hz.trans (mulVec_zero X).symm)
  exact (one_ne_zero : (1 : ℂ) ≠ 0) (by simpa using congrFun hv j₀)

end PrincipalVectors

/-- **Theorem 2** of [benIsrael2003generalized], Chapter 0. A complex square
matrix is similar to a block diagonal matrix of positive-sized Jordan blocks. -/
theorem theorem_2 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ (p : ℕ) (e : Fin p → ℕ) (c : Fin p → ℂ) (he : ∑ i, e i = n)
      (X : Matrix (Fin n) (Fin n) ℂ), (∀ i, 0 < e i) ∧ IsUnit X ∧
      X⁻¹ * A * X = (Matrix.jordanForm e c).reindex
        (finSigmaFinEquiv.trans (finCongr he)) (finSigmaFinEquiv.trans (finCongr he)) :=
  A.exists_conj_jordanForm

section JordanForm

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
variable {e : ι → ℕ} {c : ι → ℂ} {A : Matrix n n ℂ}

/-- **Theorem 2** of [benIsrael2003generalized], Chapter 0. The number of
Jordan blocks of a specified eigenvalue and positive size is independent
of the Jordan form chosen. -/
theorem theorem_2_unique {ι' : Type*} [Fintype ι'] [DecidableEq ι']
    {e' : ι' → ℕ} {c' : ι' → ℂ} (he : ∀ i, 0 < e i) (he' : ∀ i, 0 < e' i)
    (s : ((i : ι) × Fin (e i)) ≃ n) (s' : ((i : ι') × Fin (e' i)) ≃ n)
    (h : A.IsSimilar ((Matrix.jordanForm e c).reindex s s))
    (h' : A.IsSimilar ((Matrix.jordanForm e' c').reindex s' s')) (a : ℂ) (k : ℕ) :
    (Finset.univ.filter fun i => c i = a ∧ e i = k).card =
      (Finset.univ.filter fun i => c' i = a ∧ e' i = k).card :=
  Matrix.card_jordanBlocks_eq_of_isSimilar he he' s s' h h' a k

/-- **Equation (125)** of [benIsrael2003generalized], Chapter 0. Each
Jordan block contributes a linear factor to the power of its size. -/
theorem charpoly_eq_jordanFactorization (s : ((i : ι) × Fin (e i)) ≃ n)
    (h : A.IsSimilar ((Matrix.jordanForm e c).reindex s s)) :
    A.charpoly = ∏ i, (X - C (c i)) ^ e i :=
  h.charpoly_eq.trans ((charpoly_reindex s _).trans (charpoly_jordanForm e c))

omit [Fintype ι] in
/-- The scalars on positive-sized Jordan blocks are exactly the eigenvalues. -/
theorem eigenvalue_iff_mem_jordanBlocks [Finite ι] (s : ((i : ι) × Fin (e i)) ≃ n)
    (h : A.IsSimilar ((Matrix.jordanForm e c).reindex s s)) (he : ∀ i, 0 < e i) (a : ℂ) :
    a ∈ spectrum ℂ A ↔ a ∈ Set.range c := by
  classical
  let := Fintype.ofFinite ι
  rw [mem_spectrum_iff_isRoot_charpoly, IsRoot.def, charpoly_eq_jordanFactorization s h,
    eval_prod]
  simp only [eval_pow, eval_sub, eval_X, eval_C, Finset.prod_eq_zero_iff, Finset.mem_univ,
    true_and, pow_eq_zero_iff (he _).ne', sub_eq_zero, Set.mem_range]
  exact exists_congr fun _ => eq_comm

/-- **Section 0.7** of [benIsrael2003generalized]. Algebraic multiplicity
is the multiplicity as a root of the characteristic polynomial. -/
noncomputable def algebraicMultiplicity (A : Matrix n n ℂ) (a : ℂ) : ℕ :=
  A.charpoly.rootMultiplicity a

/-- The algebraic multiplicity of an eigenvalue is the sum of the sizes
of its Jordan blocks. -/
theorem algebraicMultiplicity_eq_sum_jordanSizes (s : ((i : ι) × Fin (e i)) ≃ n)
    (h : A.IsSimilar ((Matrix.jordanForm e c).reindex s s)) (a : ℂ) :
    algebraicMultiplicity A a = ∑ i, if c i = a then e i else 0 := by
  rw [algebraicMultiplicity, h.charpoly_eq, charpoly_reindex, rootMultiplicity_charpoly_jordanForm]
  exact Finset.sum_filter _ _

/-- Each positive-sized Jordan block for an eigenvalue contributes one
dimension to its eigenspace. -/
theorem geometricMultiplicity_eq_card_jordanBlocks (s : ((i : ι) × Fin (e i)) ≃ n)
    (h : A.IsSimilar ((Matrix.jordanForm e c).reindex s s)) (he : ∀ i, 0 < e i) (a : ℂ) :
    geometricMultiplicity A a = (Finset.univ.filter fun i => c i = a).card := by
  rw [geometricMultiplicity, Matrix.eigenspace_mulVecLin_eq_ker, ← pow_one (A - a • 1),
    Matrix.finrank_ker_pow_eq_of_isSimilar_reindex s h, pow_one]
  exact Matrix.finrank_ker_mulVecLin_jordanForm_sub_smul_one he c a

end JordanForm

section Conjugation

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Equation (122)** of [benIsrael2003generalized], Chapter 0. Conjugation
by the Jordan basis matrix commutes with taking natural powers. -/
theorem pow_eq_conj_of_jordanForm {A J X : Matrix n n ℂ} (hX : IsUnit X)
    (h : A = X * J * X⁻¹) (k : ℕ) : A ^ k = X * J ^ k * X⁻¹ := by
  have hL := nonsing_inv_mul X ((isUnit_iff_isUnit_det X).mp hX)
  have hR := mul_nonsing_inv X ((isUnit_iff_isUnit_det X).mp hX)
  induction k with
  | zero => simp [hR]
  | succ k ih =>
      rw [pow_succ, ih, h, pow_succ]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc X⁻¹ X, hL, Matrix.one_mul]

/-- **Equation (123)** of [benIsrael2003generalized], Chapter 0. Polynomial
evaluation in a Jordan basis conjugates by the change of coordinates. -/
theorem aeval_eq_conj_of_jordanForm {A J X : Matrix n n ℂ} (hX : IsUnit X)
    (h : A = X * J * X⁻¹) (p : ℂ[X]) : aeval A p = X * aeval J p * X⁻¹ := by
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Matrix.smul_mul, Matrix.mul_smul]
  rw [pow_eq_conj_of_jordanForm hX h k]

end Conjugation

/-- **Theorem 3** of [benIsrael2003generalized], Chapter 0. The product of the
shifted powers, one for each Jordan block in order, annihilates the matrix. -/
theorem theorem_3 {n p : ℕ} {e : Fin p → ℕ} {c : Fin p → ℂ}
    {A : Matrix (Fin n) (Fin n) ℂ} (s : ((i : Fin p) × Fin (e i)) ≃ Fin n)
    (h : A.IsSimilar ((Matrix.jordanForm e c).reindex s s)) :
    (List.ofFn fun i => (A - c i • 1) ^ e i).prod = 0 := by
  have hp := aeval_self_charpoly A
  rw [charpoly_eq_jordanFactorization s h, ← Fin.prod_ofFn, map_list_prod, List.map_ofFn] at hp
  simpa only [Function.comp_def, map_pow, map_sub, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one] using hp

section Indices

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Section 0.7** of [benIsrael2003generalized]. The index of an
eigenvalue is the first exponent attaining the maximal generalized eigenspace. -/
noncomputable abbrev eigenvalueIndex (A : Matrix n n ℂ) (c : ℂ) : ℕ :=
  Chapter02.primaryIndex A c

private theorem eigenvalueIndex_le_iff_dimKer_eq (A : Matrix n n ℂ) (c : ℂ) (k : ℕ) :
    eigenvalueIndex A c ≤ k ↔
      Module.finrank ℂ (((A - c • 1) ^ (k + 1)).mulVecLin.ker) =
        Module.finrank ℂ (((A - c • 1) ^ k).mulVecLin.ker) := by
  constructor
  · intro h
    rw [← Chapter02.maxGenEigenspace_eq_ker_shift A c (h.trans (Nat.le_succ _)),
      ← Chapter02.maxGenEigenspace_eq_ker_shift A c h]
  · intro h
    let B : Matrix n n ℂ := A - c • 1
    have hKer : (B ^ k).mulVecLin.ker = (B ^ (k + 1)).mulVecLin.ker :=
      Submodule.eq_of_le_of_finrank_eq (B.monotone_ker_mulVecLin_pow (Nat.le_succ k)) h.symm
    have hRank := (B.rank_pow_eq_iff_ker_eq (Nat.le_succ k)).mpr hKer
    apply Chapter02.primaryIndex_le_of_genEigenspace_eq A c
    rw [← Module.End.iSup_genEigenspace_eq A.mulVecLin c, Chapter02.genEigenspace_eq_ker_shift]
    refine le_antisymm (iSup_le fun j => ?_) ?_
    · rw [Chapter02.genEigenspace_eq_ker_shift]
      rcases le_total j k with hj | hj
      · exact B.monotone_ker_mulVecLin_pow hj
      · exact ((B.rank_pow_eq_iff_ker_eq hj).mp (B.rank_pow_eq_of_eq_succ hRank hj)).ge
    · rw [← Chapter02.genEigenspace_eq_ker_shift]
      exact le_iSup (fun j : ℕ => Module.End.genEigenspace A.mulVecLin c j) k

/-- The index of an eigenvalue is the size of its largest Jordan block. -/
theorem eigenvalueIndex_eq_largest_jordanSize {ι : Type*} [Fintype ι] [DecidableEq ι]
    {e : ι → ℕ} {c : ι → ℂ} {A : Matrix n n ℂ} (s : ((i : ι) × Fin (e i)) ≃ n)
    (h : A.IsSimilar ((Matrix.jordanForm e c).reindex s s)) (a : ℂ) :
    eigenvalueIndex A a = (Finset.univ.filter fun i => c i = a).sup e := by
  have hle (k : ℕ) : eigenvalueIndex A a ≤ k ↔ ∀ i, c i = a → e i ≤ k := by
    rw [eigenvalueIndex_le_iff_dimKer_eq, Matrix.finrank_ker_pow_eq_of_isSimilar_reindex s h,
      Matrix.finrank_ker_pow_eq_of_isSimilar_reindex s h,
      Matrix.finrank_ker_mulVecLin_jordanForm_sub_smul_one_pow_succ_eq_iff]
  apply le_antisymm
  · exact (hle _).mpr fun i hi => Finset.le_sup (f := e) (by simp [hi])
  · exact Finset.sup_le fun i hi => (hle _).mp le_rfl i (by simpa using hi)

/-- **Section 0.7** of [benIsrael2003generalized]. The minimal polynomial
has one factor for each distinct eigenvalue, with exponent given by its index. -/
theorem minpoly_eq_prod_of_eigenvalueIndices (A : Matrix n n ℂ) :
    minpoly ℂ A = ∏ a ∈ Chapter02.spectralValues A, (X - C a) ^ eigenvalueIndex A a :=
  Chapter02.minpoly_eq_prod_primary A

/-- **Exercise 82** of [benIsrael2003generalized], Chapter 0. The index of
an eigenvalue is the greatest grade of a principal vector for it. -/
theorem principalVector_max_grade (A : Matrix n n ℂ) (c : ℂ) (hc : c ∈ spectrum ℂ A) :
    IsGreatest {k | ∃ x, IsPrincipalVector A c k x} (eigenvalueIndex A c) := by
  let B : Matrix n n ℂ := A - c • 1
  let k := eigenvalueIndex A c
  have hk : 0 < k := by
    have hc' := (spectrum.mem_iff_isRoot_minpoly (Algebra.IsIntegral.isIntegral A)).mp hc
    change 0 < Chapter02.primaryIndex A c
    rw [Chapter02.primaryIndex_eq_rootMultiplicity]
    exact (rootMultiplicity_pos (minpoly.ne_zero (Algebra.IsIntegral.isIntegral A))).mpr hc'
  constructor
  · have hne : (B ^ k).mulVecLin.ker ≠ (B ^ (k - 1)).mulVecLin.ker := by
      intro he
      have hs : k - 1 + 1 = k := Nat.sub_add_cancel hk
      exact (Nat.not_le.mpr (Nat.sub_lt hk Nat.one_pos))
        ((eigenvalueIndex_le_iff_dimKer_eq A c (k - 1)).mpr (by
          change Module.finrank ℂ (B ^ (k - 1 + 1)).mulVecLin.ker =
            Module.finrank ℂ (B ^ (k - 1)).mulVecLin.ker
          rw [hs, he]))
    obtain ⟨x, hx, hx'⟩ := IsConcreteLE.exists_of_lt
      (lt_of_le_of_ne (B.monotone_ker_mulVecLin_pow (Nat.sub_le k 1)) hne.symm)
    exact ⟨x, hk, LinearMap.mem_ker.mp hx, fun h => hx' (LinearMap.mem_ker.mpr h)⟩
  · intro j ⟨x, hpos, hx, hx'⟩
    by_contra! hj
    have h₁ := Chapter02.maxGenEigenspace_eq_ker_shift A c (k := j) hj.le
    have h₂ := Chapter02.maxGenEigenspace_eq_ker_shift A c (k := j - 1) (by
      change eigenvalueIndex A c ≤ j - 1
      omega)
    have hMem : x ∈ (B ^ j).mulVecLin.ker := LinearMap.mem_ker.mpr hx
    rw [← h₁, h₂] at hMem
    exact hx' (LinearMap.mem_ker.mp hMem)

end Indices

section Exercises

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Exercise 71** of [benIsrael2003generalized], Chapter 0. The matrix
and its Jordan form are invertible together, precisely when zero is outside
their spectrum. -/
theorem isUnit_jordanForm_iff {A J : Matrix n n ℂ} (h : A.IsSimilar J) :
    (IsUnit A ↔ IsUnit J) ∧ (IsUnit A ↔ 0 ∉ spectrum ℂ A) := by
  refine ⟨?_, (spectrum.zero_notMem_iff ℂ).symm⟩
  rw [← spectrum.zero_notMem_iff ℂ, ← spectrum.zero_notMem_iff ℂ, h.spectrum_eq]

/-- **Equation (126)** of [benIsrael2003generalized], Chapter 0. The
inverse conjugates by the Jordan basis matrix. -/
theorem inv_eq_conj_of_jordanForm {A J X : Matrix n n ℂ} (hX : IsUnit X)
    (h : A = X * J * X⁻¹) : A⁻¹ = X * J⁻¹ * X⁻¹ := by
  rw [h, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    Matrix.nonsing_inv_nonsing_inv X ((isUnit_iff_isUnit_det X).mp hX), Matrix.mul_assoc]

/-- **Exercise 71** of [benIsrael2003generalized], Chapter 0. Negative
powers conjugate by the same Jordan basis matrix. -/
theorem inv_pow_eq_conj_of_jordanForm {A J X : Matrix n n ℂ} (hX : IsUnit X)
    (h : A = X * J * X⁻¹) (k : ℕ) : A⁻¹ ^ k = X * J⁻¹ ^ k * X⁻¹ :=
  pow_eq_conj_of_jordanForm hX (inv_eq_conj_of_jordanForm hX h) k

/-- **Exercise 72** of [benIsrael2003generalized], Chapter 0.
The characteristic polynomial has the determinant expression with the sign
chosen to make it monic. -/
theorem eval_charpoly_eq_sign_mul_det (A : Matrix n n ℂ) (c : ℂ) :
    A.charpoly.eval c = (-1) ^ Fintype.card n * (A - c • 1).det := by
  have hs : Matrix.scalar n c = c • (1 : Matrix n n ℂ) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.scalar_apply, Matrix.smul_apply, h]
  rw [Matrix.eval_charpoly, ← det_neg, neg_sub, hs]

/-- **Exercise 73** of [benIsrael2003generalized], Chapter 0. Adjointing
the matrix conjugates its eigenvalues. -/
theorem mem_spectrum_conjTranspose_iff (A : Matrix n n ℂ) (c : ℂ) :
    star c ∈ spectrum ℂ Aᴴ ↔ c ∈ spectrum ℂ A := by
  simp only [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one]
  rw [← show (c • (1 : Matrix n n ℂ) - A)ᴴ = star c • 1 - Aᴴ from by simp,
    isUnit_conjTranspose]

end Exercises

/-- **Exercise 75** of [benIsrael2003generalized], Chapter 0. The
nilpotency index is the first natural exponent with zero power. -/
noncomputable abbrev nilpotencyIndex {n : Type*} [Fintype n] [DecidableEq n]
    (N : Matrix n n ℂ) : ℕ := nilpotencyClass N

/-- **Equation (127)** of [benIsrael2003generalized], Chapter 0. The power
of the shifted Jordan block has ones on the corresponding superdiagonal. -/
theorem jordanBlock_sub_smul_pow_apply {k : ℕ} (c : ℂ) (p : ℕ) (i j : Fin k) :
    ((jordanBlock k c - c • 1) ^ p) i j = if i.val + p = j.val then 1 else 0 := by
  rw [Matrix.jordanBlock_sub_smul_one, sub_self, Matrix.jordanBlock_zero_pow_apply]

/-- **Exercise 75** of [benIsrael2003generalized], Chapter 0. A nilpotent
Jordan block of positive size has nilpotency index equal to its size. -/
theorem nilpotencyIndex_jordanBlock_zero {k : ℕ} (hk : 0 < k) :
    nilpotencyIndex (jordanBlock k 0) = k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  apply nilpotencyClass_eq_succ_iff.mpr
  constructor
  · ext i j
    rw [Matrix.jordanBlock_zero_pow_apply, ite_eq_right (by omega)]
    rfl
  · intro h
    have he := congrArg (fun M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ => M 0 (Fin.last k)) h
    rw [Matrix.jordanBlock_zero_pow_apply] at he
    simp at he

/-- **Equation (129)** of [benIsrael2003generalized], Chapter 0. A
polynomial evaluated on a Jordan block is the truncated Taylor expansion
at the block's eigenvalue, with the nilpotent shift as the variable. -/
theorem aeval_jordanBlock_eq_taylor_sum (p : ℂ[X]) (k : ℕ) (c : ℂ) :
    aeval (jordanBlock k c) p =
      ∑ j ∈ Finset.range k, ((derivative^[j] p).eval c / j.factorial) • (jordanBlock k 0) ^ j := by
  have hp := pfc_polynomial
    (Algebra.IsIntegral.isIntegral (R := ℂ) (jordanBlock k c))
    (Matrix.splits_minpoly_jordanBlock (n := k) (μ := c)) p
  rw [← hp]
  simpa only [Hermite.taylorJet_polynomial, Hermite.coeff_taylor_eq_eval_iterate_derivative_div]
    using Matrix.pfc_jordanBlock (fun z : ℂ => p.eval z) k c

/-- **Equation (129)** of [benIsrael2003generalized], Chapter 0. The
$j$th superdiagonal of a polynomial in a Jordan block is the $j$th Taylor
coefficient. -/
theorem aeval_jordanBlock_apply (p : ℂ[X]) (c : ℂ) {k : ℕ} (i j : Fin k) :
    aeval (jordanBlock k c) p i j =
      if i ≤ j then (derivative^[j.val - i.val] p).eval c / (j.val - i.val).factorial else 0 := by
  rw [← pfc_polynomial (Algebra.IsIntegral.isIntegral (R := ℂ) (jordanBlock k c))
    (Matrix.splits_minpoly_jordanBlock (n := k) (μ := c)) p]
  simpa only [Hermite.taylorJet_polynomial, Hermite.coeff_taylor_eq_eval_iterate_derivative_div]
    using Matrix.pfc_jordanBlock_apply (fun z : ℂ => p.eval z) k c i j

private theorem taylorCoefficient_X_pow (m j : ℕ) (c : ℂ) :
    (derivative^[j] ((X : ℂ[X]) ^ m)).eval c / j.factorial = (m.choose j : ℂ) * c ^ (m - j) := by
  rw [← Hermite.coeff_taylor_eq_eval_iterate_derivative_div, taylor_coeff, X_pow_eq_monomial,
    hasseDeriv_monomial, eval_monomial, mul_one]

/-- **Equations (128b)–(128c)** of [benIsrael2003generalized], Chapter 0. The
powers of a Jordan block have the truncated binomial expansion. -/
theorem jordanBlock_pow_eq_sum (k m : ℕ) (c : ℂ) :
    (jordanBlock k c) ^ m = ∑ j ∈ Finset.range k,
      ((m.choose j : ℂ) * c ^ (m - j)) • (jordanBlock k 0) ^ j := by
  have hp : (jordanBlock k c) ^ m = aeval (jordanBlock k c) ((X : ℂ[X]) ^ m) := by simp
  rw [hp, aeval_jordanBlock_eq_taylor_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [taylorCoefficient_X_pow]

/-- **Equation (128a)** of [benIsrael2003generalized], Chapter 0. The entries
of a block power are obtained by reading its upper superdiagonals. -/
theorem jordanBlock_pow_apply {k : ℕ} (m : ℕ) (c : ℂ) (i j : Fin k) :
    ((jordanBlock k c) ^ m) i j =
      if i ≤ j then ((m.choose (j.val - i.val) : ℂ) * c ^ (m - (j.val - i.val))) else 0 := by
  have hp : (jordanBlock k c) ^ m = aeval (jordanBlock k c) ((X : ℂ[X]) ^ m) := by simp
  rw [hp, aeval_jordanBlock_apply, taylorCoefficient_X_pow]

section PolynomialInverse

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem inv_eq_aeval_of_annihilator {A : Matrix n n ℂ} {p : ℂ[X]}
    (h : aeval A p = 0) (h0 : p.coeff 0 ≠ 0) :
    A⁻¹ = aeval A (C (-(p.coeff 0)⁻¹) * p.divX) := by
  have hSum : A * aeval A p.divX + p.coeff 0 • 1 = 0 := by
    simpa only [map_add, map_mul, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, h]
      using congrArg (aeval A) (X_mul_divX_add p)
  have hMul := eq_neg_of_add_eq_zero_left hSum
  apply Matrix.inv_eq_right_inv
  rw [map_mul, aeval_C, ← Algebra.smul_def, Matrix.mul_smul, hMul, smul_neg,
    smul_smul, neg_mul, inv_mul_cancel₀ h0, neg_one_smul, neg_neg]

/-- **Exercise 79** of [benIsrael2003generalized], Chapter 0. A matrix is
invertible precisely when its characteristic polynomial has nonzero
constant coefficient. In that case, the coefficients give its inverse. -/
theorem inv_eq_charpoly_divX (A : Matrix n n ℂ) :
    (IsUnit A ↔ A.charpoly.coeff 0 ≠ 0) ∧
    (A.charpoly.coeff 0 ≠ 0 →
      A⁻¹ = aeval A (C (-(A.charpoly.coeff 0)⁻¹) * A.charpoly.divX)) := by
  refine ⟨?_, inv_eq_aeval_of_annihilator (aeval_self_charpoly A)⟩
  rw [← spectrum.zero_notMem_iff ℂ, mem_spectrum_iff_isRoot_charpoly, IsRoot.def,
    coeff_zero_eq_eval_zero]

/-- **Equations (130)–(131)** of [benIsrael2003generalized], Chapter 0.
For an invertible matrix, the minimal polynomial is a nonzero scalar
times $1-Xq$, and evaluating $q$ gives the inverse. -/
theorem exists_minpoly_eq_C_mul_one_sub_X_mul (A : Matrix n n ℂ) (hA : IsUnit A) :
    ∃ (c : ℂ) (q : ℂ[X]), c ≠ 0 ∧ minpoly ℂ A = C c * (1 - X * q) ∧
      A⁻¹ = aeval A q := by
  let p := minpoly ℂ A
  have h0 : p.coeff 0 ≠ 0 := by
    intro h
    have hRoot : IsRoot p 0 := by simpa only [IsRoot.def, ← coeff_zero_eq_eval_zero] using h
    exact (spectrum.zero_notMem_iff ℂ).mpr hA
      ((spectrum.mem_iff_isRoot_minpoly (Algebra.IsIntegral.isIntegral A)).mpr hRoot)
  refine ⟨p.coeff 0, C (-(p.coeff 0)⁻¹) * p.divX, h0, ?_,
    inv_eq_aeval_of_annihilator (minpoly.aeval ℂ A) h0⟩
  have hc : C (p.coeff 0) * C (-(p.coeff 0)⁻¹) = (-1 : ℂ[X]) := by
    rw [← C_mul, mul_neg, mul_inv_cancel₀ h0, C_neg, C_1]
  calc
    p = X * p.divX + C (p.coeff 0) := (X_mul_divX_add p).symm
    _ = C (p.coeff 0) * (1 - X * (C (-(p.coeff 0)⁻¹) * p.divX)) := by
      rw [mul_sub, mul_one, ← mul_assoc, mul_comm (C (p.coeff 0)) X,
        mul_assoc X, ← mul_assoc (C (p.coeff 0)), hc]
      ring

/-- **Exercise 81** of [benIsrael2003generalized], Chapter 0. A $2$ by $2$
matrix with eigenvalues $i$ and $-i$ has inverse equal to its negative. -/
theorem inv_eq_neg_of_mem_spectrum_I_neg_I (A : Matrix (Fin 2) (Fin 2) ℂ)
    (h₁ : Complex.I ∈ spectrum ℂ A) (h₂ : -Complex.I ∈ spectrum ℂ A) : A⁻¹ = -A := by
  rw [mem_spectrum_iff_isRoot_charpoly, IsRoot.def, charpoly_fin_two] at h₁ h₂
  simp only [eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C,
    Complex.I_sq, Even.neg_pow (by decide : Even 2)] at h₁ h₂
  have hTraceI : A.trace * Complex.I = 0 := by linear_combination (h₂ - h₁) / 2
  have hTr := (mul_eq_zero.mp hTraceI).resolve_right Complex.I_ne_zero
  have hDet : A.det = 1 := by
    rw [hTr, zero_mul, sub_zero, neg_add_eq_zero] at h₁
    exact h₁.symm
  have hCH := aeval_self_charpoly A
  rw [charpoly_fin_two, hTr, hDet] at hCH
  simp only [map_add, map_sub, map_pow, map_mul, aeval_X, map_zero, Matrix.zero_mul,
    sub_zero, map_one] at hCH
  apply Matrix.inv_eq_right_inv
  rw [Matrix.mul_neg, ← pow_two]
  rw [eq_neg_of_add_eq_zero_left hCH, neg_neg]

end PolynomialInverse

/-- **Exercise 74** of [benIsrael2003generalized], Chapter 0. The six
displayed blocks give the stated characteristic and minimal polynomials.
The first eigenvalue has algebraic multiplicity eight, geometric
multiplicity four, and index three. -/
theorem exercise_74 {a b : ℂ} (hab : a ≠ b) {A : Matrix (Fin 12) (Fin 12) ℂ}
    (s : ((i : Fin 6) × Fin ((![3, 2, 2, 1, 2, 2] : Fin 6 → ℕ) i)) ≃ Fin 12)
    (h : A.IsSimilar ((Matrix.jordanForm ![3, 2, 2, 1, 2, 2] ![a, a, a, a, b, b]).reindex s s)) :
    A.charpoly = (X - C a) ^ 8 * (X - C b) ^ 4 ∧
    minpoly ℂ A = (X - C a) ^ 3 * (X - C b) ^ 2 ∧
    algebraicMultiplicity A a = 8 ∧ geometricMultiplicity A a = 4 ∧ eigenvalueIndex A a = 3 := by
  let e : Fin 6 → ℕ := ![3, 2, 2, 1, 2, 2]
  let c : Fin 6 → ℂ := ![a, a, a, a, b, b]
  have he (i : Fin 6) : 0 < e i := by fin_cases i <;> decide
  have hA : eigenvalueIndex A a = 3 := by
    rw [eigenvalueIndex_eq_largest_jordanSize s h]
    apply le_antisymm
    · apply Finset.sup_le
      intro i _
      fin_cases i <;> decide
    · exact Finset.le_sup (b := 0) (f := e) (by simp)
  have hB : eigenvalueIndex A b = 2 := by
    rw [eigenvalueIndex_eq_largest_jordanSize s h]
    apply le_antisymm
    · apply Finset.sup_le
      intro i hi
      have hi' : c i = b := (Finset.mem_filter.mp hi).2
      fin_cases i <;> simp_all [c, e]
    · exact Finset.le_sup (b := 4) (f := e) (by simp)
  have hs : Chapter02.spectralValues A = {a, b} := by
    ext z
    rw [Chapter02.mem_spectralValues_iff, eigenvalue_iff_mem_jordanBlocks s h he]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact ⟨0, rfl⟩
      · obtain rfl := Finset.mem_singleton.mp hz
        exact ⟨4, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, hA⟩
  · rw [charpoly_eq_jordanFactorization s h]
    simp [Fin.prod_univ_succ]
    ring
  · rw [minpoly_eq_prod_of_eigenvalueIndices, hs, Finset.prod_pair hab, hA, hB]
  · rw [algebraicMultiplicity_eq_sum_jordanSizes s h]
    simp [Fin.sum_univ_succ, hab.symm]
  · rw [geometricMultiplicity_eq_card_jordanBlocks s h he, Finset.card_filter]
    norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, hab.symm, ite_true, ite_false]

section PolynomialDerivativeSpectrum

open Polynomial

/-- The polynomial differentiation endomorphism on polynomials of degree at most $n$. -/
noncomputable def polynomialDerivativeEnd (n : ℕ) : Module.End ℝ (polynomialDegreeSpace n) :=
  (Polynomial.derivative.comp (polynomialDegreeSpace n).subtype).codRestrict
    (polynomialDegreeSpace n) fun p => mem_polynomialDegreeSpace.mpr
      (Polynomial.degree_derivative_le.trans (mem_polynomialDegreeSpace.mp p.property))

private theorem polynomialDerivativeEnd_pow_apply (n k : ℕ) (p : polynomialDegreeSpace n) :
    ((polynomialDerivativeEnd n ^ k) p).val = Polynomial.derivative^[k] p.val := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, Function.iterate_succ_apply', ← ih]
    rfl

private theorem polynomialDerivativeEnd_ker_dimension (n : ℕ) :
    Module.finrank ℝ (polynomialDerivativeEnd n).ker = 1 := by
  let D := polynomialDerivativeEnd n
  let c : polynomialDegreeSpace n := ⟨1, mem_polynomialDegreeSpace.mpr (by simp)⟩
  have hc : c ∈ D.ker := by
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change Polynomial.derivative (1 : ℝ[X]) = 0
    simp
  let u : D.ker := ⟨c, hc⟩
  have hu : u ≠ 0 := by
    intro h
    have he := congrArg (fun p : D.ker => p.val.val) h
    exact one_ne_zero he
  apply (finrank_eq_one_iff_of_ne_zero' u hu).mpr
  intro p
  have hp : Polynomial.derivative p.val.val = 0 :=
    congrArg Subtype.val (LinearMap.mem_ker.mp p.property)
  refine ⟨p.val.val.coeff 0, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change p.val.val.coeff 0 • (1 : ℝ[X]) = p.val.val
  rw [Polynomial.smul_eq_C_mul, mul_one]
  exact (Polynomial.eq_C_of_derivative_eq_zero hp).symm

/-- **Exercise 78** of [benIsrael2003generalized], Chapter 0. The only
polynomial differentiation eigenvalue is zero. Its algebraic multiplicity
is the whole dimension, and its eigenspace consists of the constants. -/
theorem polynomialDerivative_eigenvalue_multiplicities (n : ℕ) :
    let D := polynomialDerivativeEnd n
    spectrum ℝ D = {0} ∧ D.charpoly = X ^ (n + 1) ∧
      D.charpoly.rootMultiplicity 0 = n + 1 ∧
      Module.finrank ℝ (Module.End.eigenspace D 0) = 1 := by
  intro D
  have hNil : IsNilpotent D := by
    refine ⟨n + 1, ?_⟩
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    change ((polynomialDerivativeEnd n ^ (n + 1)) p).val = 0
    rw [polynomialDerivativeEnd_pow_apply]
    apply Polynomial.iterate_derivative_eq_zero_of_degree_lt
    exact (mem_polynomialDegreeSpace.mp p.property).trans_lt (by exact_mod_cast Nat.lt_succ_self n)
  have hChar : D.charpoly = X ^ (n + 1) := by
    rw [hNil.charpoly_eq_X_pow_finrank, (polynomialDegreeSpace_basis n).1]
  refine ⟨?_, hChar, ?_, ?_⟩
  · ext a
    rw [← Module.End.hasEigenvalue_iff_mem_spectrum, Module.End.hasEigenvalue_iff_isRoot_charpoly,
      hChar]
    simp [Polynomial.IsRoot]
  · rw [hChar]
    simpa only [Polynomial.C_0, sub_zero] using Polynomial.rootMultiplicity_X_sub_C_pow (0 : ℝ) (n + 1)
  · rw [Module.End.eigenspace_zero]
    exact polynomialDerivativeEnd_ker_dimension n

end PolynomialDerivativeSpectrum

end BenIsraelGreville.Chapter00
