/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Algebra.Group.Drazin
import Numlib.LinearAlgebra.Eigenspace.Spectral
import NumlibSurface.BenIsraelGreville.Chapter00.Section07
import Numlib.LinearAlgebra.Matrix.GeneralizedInverse

/-!
# Spectral inverse equations

Section 4.1 of [benIsrael2003generalized] adds power equations for square matrices to
the four Penrose equations. The exponents used for these equations in the book are positive.
-/

namespace BenIsraelGreville.Chapter04

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Equation $(1^k)$** of [benIsrael2003generalized], Chapter 4. The first power
equation is $A^k X A = A^k$. -/
def SatisfiesFirstPowerEquation (k : ℕ) (A X : Matrix n n ℂ) : Prop :=
  A ^ k * X * A = A ^ k

/-- **Equation $(5^k)$** of [benIsrael2003generalized], Chapter 4. The fifth power
equation is $A^k X = X A^k$. -/
abbrev SatisfiesFifthPowerEquation (k : ℕ) (A X : Matrix n n ℂ) : Prop :=
  Commute (A ^ k) X

/-- **Equation $(6^k)$** of [benIsrael2003generalized], Chapter 4. The sixth power
equation is $A X^k = X^k A$. -/
abbrev SatisfiesSixthPowerEquation (k : ℕ) (A X : Matrix n n ℂ) : Prop :=
  Commute A (X ^ k)

/-- **Exercise 2** of [benIsrael2003generalized], Chapter 4.
At reciprocal eigenvalues a nonsingular matrix and its inverse have the
same principal vectors of each grade. -/
theorem inverse_reciprocal_principal_grade (A : Matrix n n ℂ) (hA : IsUnit A)
    (μ : ℂ) (p : ℕ) (v : n → ℂ) :
    BenIsraelGreville.Chapter00.IsPrincipalVector A μ p v ↔
      BenIsraelGreville.Chapter00.IsPrincipalVector A⁻¹ μ⁻¹ p v := by
  let T := A⁻¹
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
  have hTA : T * A = 1 := Matrix.nonsing_inv_mul _ hdet
  have hAT : A * T = 1 := Matrix.mul_nonsing_inv _ hdet
  have hT : IsUnit T := by
    change IsUnit A⁻¹
    obtain ⟨u, rfl⟩ := hA
    rw [← Matrix.coe_units_inv]
    exact (u⁻¹).isUnit
  have hPowT (r : ℕ) : Function.Injective (T ^ r).mulVecLin :=
    Matrix.mulVec_injective_iff_isUnit.mpr (hT.pow r)
  by_cases hμ : μ = 0
  · subst μ
    have hPowA (r : ℕ) : Function.Injective (A ^ r).mulVecLin :=
      Matrix.mulVec_injective_iff_isUnit.mpr (hA.pow r)
    simp only [_root_.inv_zero, BenIsraelGreville.Chapter00.IsPrincipalVector, zero_smul, sub_zero]
    constructor
    · intro hv
      have he : (A ^ p).mulVecLin v = (A ^ p).mulVecLin 0 := by
        rw [map_zero]
        exact hv.2.1
      have hv0 := hPowA p he
      exact False.elim (hv.2.2 (by rw [hv0, mulVec_zero]))
    · intro hv
      have he : (T ^ p).mulVecLin v = (T ^ p).mulVecLin 0 := by
        rw [map_zero]
        exact hv.2.1
      have hv0 := hPowT p he
      exact False.elim (hv.2.2 (by rw [hv0, mulVec_zero]))
  have hc : Commute T (A - μ • 1) := by
    have ha : Commute T A := hTA.trans hAT.symm
    have hs : Commute T (μ • (1 : Matrix n n ℂ)) := by
      rw [← Algebra.algebraMap_eq_smul_one]
      exact Algebra.commute_algebraMap_right _ _
    exact ha.sub_right hs
  have hshift : T - μ⁻¹ • 1 = (-μ⁻¹) • (T * (A - μ • 1)) := by
    rw [mul_sub, hTA, mul_smul_comm, mul_one, smul_sub, smul_smul, neg_mul,
      inv_mul_cancel₀ hμ, neg_one_smul, neg_smul]
    abel
  have hz (r : ℕ) : ((T - μ⁻¹ • 1) ^ r) *ᵥ v = 0 ↔ ((A - μ • 1) ^ r) *ᵥ v = 0 := by
    rw [hshift, smul_pow, hc.mul_pow, smul_mulVec, ← mulVec_mulVec,
      smul_eq_zero, or_iff_right (pow_ne_zero _ (neg_ne_zero.mpr (inv_ne_zero hμ)))]
    change (T ^ r).mulVecLin (((A - μ • 1) ^ r) *ᵥ v) = 0 ↔ _
    have hEq : (T ^ r).mulVecLin (((A - μ • 1) ^ r) *ᵥ v) = (T ^ r).mulVecLin 0 ↔
        ((A - μ • 1) ^ r) *ᵥ v = 0 := (hPowT r).eq_iff
    simpa only [map_zero] using hEq
  change (0 < p ∧ ((A - μ • 1) ^ p) *ᵥ v = 0 ∧ ((A - μ • 1) ^ (p - 1)) *ᵥ v ≠ 0) ↔
    (0 < p ∧ ((T - μ⁻¹ • 1) ^ p) *ᵥ v = 0 ∧ ((T - μ⁻¹ • 1) ^ (p - 1)) *ᵥ v ≠ 0)
  simp only [ne_eq, hz]

/-- **Exercise 1** of [benIsrael2003generalized], Chapter 4.
The eigenspaces span the whole space exactly when every principal
vector is an eigenvector. -/
theorem exercise_4_1 (A : Matrix n n ℂ) :
    (⨆ μ : ℂ, Module.End.eigenspace A.mulVecLin μ) = ⊤ ↔
      ∀ μ p v, BenIsraelGreville.Chapter00.IsPrincipalVector A μ p v →
        Module.End.HasEigenvector A.mulVecLin μ v := by
  classical
  let f : Module.End ℂ (n → ℂ) := A.mulVecLin
  have hshift (μ : ℂ) (p : ℕ) :
      (f - μ • 1) ^ p = ((A - μ • 1) ^ p).mulVecLin := by
    simp only [f, ← toLin'_apply', toLin'_pow, map_sub, map_smul, toLin'_one]
    rfl
  have hmem (μ : ℂ) (p : ℕ) (v : n → ℂ) :
      v ∈ f.genEigenspace μ p ↔ ((A - μ • 1) ^ p) *ᵥ v = 0 := by
    rw [Module.End.mem_genEigenspace_nat, hshift, LinearMap.mem_ker]
    rfl
  constructor
  · intro h μ p v hv
    have hmax : v ∈ f.maxGenEigenspace μ :=
      Module.End.genEigenspace_le_maximal _ _ _ ((hmem μ p v).mpr hv.2.1)
    rw [Module.End.maxGenEigenspace_eq_eigenspace_of_iSup_eigenspace_eq_top h] at hmax
    exact ⟨hmax, fun hzero => hv.2.2 (by rw [hzero, mulVec_zero])⟩
  · intro h
    change (⨆ μ : ℂ, f.eigenspace μ) = ⊤
    refine top_unique ?_
    rw [← Module.End.iSup_maxGenEigenspace_eq_top f]
    apply iSup_mono
    intro μ v hv
    by_cases hzero : v = 0
    · rw [hzero]
      exact Submodule.zero_mem _
    have hExists : ∃ p : ℕ, v ∈ f.genEigenspace μ p := by
      obtain ⟨p, hp⟩ := (Module.End.mem_maxGenEigenspace f μ v).mp hv
      rw [hshift] at hp
      exact ⟨p, (hmem μ p v).mpr hp⟩
    let p := Nat.find hExists
    have hp : 0 < p := by
      by_contra! hn
      have hpos : p = 0 := Nat.eq_zero_of_le_zero hn
      have hp' := Nat.find_spec hExists
      change v ∈ f.genEigenspace μ p at hp'
      rw [hpos, Nat.cast_zero, Module.End.genEigenspace_zero, Submodule.mem_bot] at hp'
      exact hzero hp'
    have he : BenIsraelGreville.Chapter00.IsPrincipalVector A μ p v := by
      refine ⟨hp, (hmem μ p v).mp (Nat.find_spec hExists), ?_⟩
      intro hprev
      have hn : p ≤ p - 1 := Nat.find_min' hExists ((hmem μ (p - 1) v).mpr hprev)
      omega
    exact (h μ p v he).1

/-- **Exercise 3** of [benIsrael2003generalized], Chapter 4.
For a nonsingular diagonalizable matrix the reciprocal-grade property
uniquely determines its ordinary inverse. -/
theorem exercise_4_3 (A X : Matrix n n ℂ) (hA : IsUnit A)
    (hspan : (⨆ μ : ℂ, Module.End.eigenspace A.mulVecLin μ) = ⊤)
    (hX : ∀ μ p v, BenIsraelGreville.Chapter00.IsPrincipalVector A μ p v ↔
      BenIsraelGreville.Chapter00.IsPrincipalVector X μ⁻¹ p v) :
    X = A⁻¹ := by
  let H := X.mulVecLin - A⁻¹.mulVecLin
  have hle : (⨆ μ : ℂ, Module.End.eigenspace A.mulVecLin μ) ≤ H.ker := by
    apply iSup_le
    intro μ v hv
    by_cases hzero : v = 0
    · rw [hzero]
      exact Submodule.zero_mem _
    have hA1 := (BenIsraelGreville.Chapter00.principalVector_grade_one_iff A μ v).mpr ⟨hv, hzero⟩
    have hx := (BenIsraelGreville.Chapter00.principalVector_grade_one_iff X μ⁻¹ v).mp
      ((hX μ 1 v).mp hA1)
    have hi := (BenIsraelGreville.Chapter00.principalVector_grade_one_iff A⁻¹ μ⁻¹ v).mp
      ((inverse_reciprocal_principal_grade A hA μ 1 v).mp hA1)
    rw [LinearMap.mem_ker]
    change X.mulVecLin v - A⁻¹.mulVecLin v = 0
    rw [hx.apply_eq_smul, hi.apply_eq_smul, sub_self]
  rw [hspan] at hle
  rw [ext_iff_mulVec]
  intro v
  have hv : v ∈ H.ker := hle (Submodule.mem_top)
  exact sub_eq_zero.mp hv

/-- **Exercise 4** of [benIsrael2003generalized], Chapter 4.
Scaling the off-diagonal entry to any nonzero value preserves the
principal vector grades at the reciprocal eigenvalue. -/
theorem exercise_4_4 (μ c : ℂ) (hc : c ≠ 0) (p : ℕ) (v : Fin 2 → ℂ) :
    BenIsraelGreville.Chapter00.IsPrincipalVector
        (jordanBlock 2 μ) μ p v ↔
      BenIsraelGreville.Chapter00.IsPrincipalVector
        (c • jordanBlock 2 0 + μ⁻¹ • 1) μ⁻¹ p v := by
  have he (r : ℕ) :
      (((c • jordanBlock 2 (0 : ℂ) + μ⁻¹ • 1) - μ⁻¹ • 1) ^ r) *ᵥ v = 0 ↔
        (jordanBlock 2 (0 : ℂ) ^ r) *ᵥ v = 0 := by
    rw [add_sub_cancel_right, smul_pow, smul_mulVec, smul_eq_zero,
      or_iff_right (pow_ne_zero _ hc)]
  unfold BenIsraelGreville.Chapter00.IsPrincipalVector
  rw [jordanBlock_sub_smul_one, sub_self]
  simp only [ne_eq, he]

end BenIsraelGreville.Chapter04
