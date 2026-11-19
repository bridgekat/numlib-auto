/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Numlib.Analysis.Complex.ContourIntegral
import Numlib.LinearAlgebra.Eigenspace.Spectral
import Numlib.LinearAlgebra.Matrix.Drazin
import Numlib.LinearAlgebra.Matrix.GeneralizedInverse

/-!
# Matrix functions and primary decomposition

Section 2.5 of [benIsrael2003generalized] constructs matrix functions using the
projections onto the generalized eigenspaces.

The path version of Theorem 11 uses Lipschitz parametrizations of closed
curves. Continuous rectifiable paths admit such parametrizations by
`Path.exists_lipschitz_reparametrization`. Each path is contained in an open convex set on which the scalar
function is holomorphic. The theorem prescribes the total winding at each eigenvalue.
-/

namespace BenIsraelGreville.Chapter02

open Matrix Module Polynomial

variable {n : Type*} [Fintype n] [DecidableEq n]

private abbrev matrixEnd (A : Matrix n n ℂ) : Module.End ℂ (n → ℂ) := A.mulVecLin

/-- The distinct eigenvalues of a complex square matrix. -/
noncomputable def spectralValues (A : Matrix n n ℂ) : Finset ℂ :=
  A.charpoly.roots.toFinset

/-- The finite set of spectral values contains precisely the points of the spectrum. -/
theorem mem_spectralValues_iff (A : Matrix n n ℂ) (z : ℂ) :
    z ∈ spectralValues A ↔ z ∈ spectrum ℂ A := by
  rw [spectralValues, Multiset.mem_toFinset, Polynomial.mem_roots A.charpoly_monic.ne_zero,
    Matrix.mem_spectrum_iff_isRoot_charpoly]

private theorem mem_spectralValues (A : Matrix n n ℂ) (z : ℂ) :
    z ∈ spectralValues A ↔ (matrixEnd A).HasEigenvalue z := by
  rw [spectralValues, Multiset.mem_toFinset, Polynomial.mem_roots A.charpoly_monic.ne_zero,
    Module.End.hasEigenvalue_iff_isRoot_charpoly]
  exact Iff.of_eq (congrArg (fun p : ℂ[X] => p.IsRoot z) (charpoly_mulVecLin A).symm)

private theorem maxGenEigenspace_eq_bot_of_notMem (A : Matrix n n ℂ) (z : ℂ)
    (hz : z ∉ spectralValues A) : (matrixEnd A).maxGenEigenspace z = ⊥ := by
  classical
  by_contra h
  rw [Module.End.maxGenEigenspace_eq] at h
  exact hz ((mem_spectralValues A z).mpr
    (Module.End.hasEigenvalue_of_hasGenEigenvalue (Module.End.hasGenEigenvalue_iff.mpr h)))

omit [DecidableEq n] in
private theorem matrix_ext_on_maxGenEigenspaces (A : Matrix n n ℂ) {B C : Matrix n n ℂ}
    (h : ∀ z (x : n → ℂ), x ∈ (matrixEnd A).maxGenEigenspace z →
      B.mulVecLin x = C.mulVecLin x) : B = C := by
  classical
  apply toLin'.injective
  apply LinearMap.eqLocus_eq_top.mp
  apply top_unique
  rw [← (matrixEnd A).iSup_maxGenEigenspace_eq_top]
  exact iSup_le fun z x hx => h z x hx

/-- **Equation (45)** of [benIsrael2003generalized], Chapter 2. The principal
idempotent at $z$ projects onto the generalized eigenspace at $z$ along the sum of
the other generalized eigenspaces. -/
noncomputable def principalIdempotent (A : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ :=
  toLin'.symm ((matrixEnd A).spectralProjector (· = z))

private theorem mulVecLin_principalIdempotent (A : Matrix n n ℂ) (z : ℂ) :
    (principalIdempotent A z).mulVecLin = (matrixEnd A).spectralProjector (· = z) := by
  rw [← toLin'_apply', principalIdempotent, LinearEquiv.apply_symm_apply]

private theorem principalIdempotent_apply_of_mem (A : Matrix n n ℂ) (z w : ℂ)
    {x : n → ℂ} (hx : x ∈ (matrixEnd A).maxGenEigenspace w) :
    (principalIdempotent A z).mulVecLin x = if w = z then x else 0 := by
  rw [mulVecLin_principalIdempotent]
  split_ifs with hw
  · exact Module.End.spectralProjector_apply_of_mem
      (Module.End.maxGenEigenspace_le_spectralSubspace (A := matrixEnd A) (p := (· = z)) hw hx)
  · exact (Module.End.spectralProjector_apply_eq_zero_iff (A := matrixEnd A) (p := (· = z))).mpr
      (Module.End.maxGenEigenspace_le_spectralSubspace (A := matrixEnd A) (p := (· ≠ z)) hw hx)

/-- The range of the principal idempotent at $z$ is the maximal generalized eigenspace. -/
theorem range_principalIdempotent (A : Matrix n n ℂ) (z : ℂ) :
    (principalIdempotent A z).mulVecLin.range = Module.End.maxGenEigenspace A.mulVecLin z := by
  rw [mulVecLin_principalIdempotent, Module.End.range_spectralProjector,
    Module.End.spectralSubspace_eq]

/-- The kernel of the principal idempotent at $z$ is the sum of the other maximal
generalized eigenspaces. -/
theorem ker_principalIdempotent (A : Matrix n n ℂ) (z : ℂ) :
    (principalIdempotent A z).mulVecLin.ker =
      ⨆ w : ℂ, ⨆ _ : w ≠ z, Module.End.maxGenEigenspace A.mulVecLin w := by
  rw [mulVecLin_principalIdempotent, Module.End.ker_spectralProjector,
    Module.End.spectralSubspace_def]

private theorem principalIdempotent_eq_zero_of_notMem (A : Matrix n n ℂ) (z : ℂ)
    (hz : z ∉ spectralValues A) : principalIdempotent A z = 0 := by
  apply matrix_ext_on_maxGenEigenspaces A
  intro w x hx
  rw [principalIdempotent_apply_of_mem A z w hx]
  by_cases h : w = z
  · subst w
    have hx0 : x = 0 := by rwa [maxGenEigenspace_eq_bot_of_notMem A z hz, Submodule.mem_bot] at hx
    simp [hx0]
  · simp [h]

private theorem principalIdempotent_mul (A : Matrix n n ℂ) (z w : ℂ) :
    principalIdempotent A z * principalIdempotent A w =
      if z = w then principalIdempotent A z else 0 := by
  rw [ext_iff_mulVec]
  intro x
  have hx : (principalIdempotent A w).mulVecLin x ∈ (matrixEnd A).maxGenEigenspace w :=
    range_principalIdempotent A w ▸ LinearMap.mem_range_self _ x
  change (principalIdempotent A z * principalIdempotent A w).mulVecLin x =
    (if z = w then principalIdempotent A z else 0).mulVecLin x
  rw [mulVecLin_mul, LinearMap.comp_apply, principalIdempotent_apply_of_mem A z w hx]
  by_cases h : z = w
  · subst w
    simp
  · simp [h, Ne.symm h]

private theorem sum_principalIdempotent (A : Matrix n n ℂ) :
    ∑ z ∈ spectralValues A, principalIdempotent A z = 1 := by
  classical
  apply matrix_ext_on_maxGenEigenspaces A
  intro w x hx
  simp only [← toLin'_apply', map_sum, LinearMap.sum_apply, toLin'_one, LinearMap.id_apply]
  by_cases hw : w ∈ spectralValues A
  · rw [Finset.sum_eq_single_of_mem w hw]
    · simpa [toLin'_apply'] using principalIdempotent_apply_of_mem A w w hx
    · intro z _ hz
      simpa [toLin'_apply', Ne.symm hz] using principalIdempotent_apply_of_mem A z w hx
  · have h0 : x = 0 := by rwa [maxGenEigenspace_eq_bot_of_notMem A w hw, Submodule.mem_bot] at hx
    simp [h0]

private theorem commute_principalIdempotent (A : Matrix n n ℂ) (z : ℂ) :
    Commute A (principalIdempotent A z) := by
  change A * principalIdempotent A z = principalIdempotent A z * A
  apply matrix_ext_on_maxGenEigenspaces A
  intro w x hx
  have hAx := Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl (matrixEnd A)) w hx
  rw [mulVecLin_mul, mulVecLin_mul, LinearMap.comp_apply, LinearMap.comp_apply,
    principalIdempotent_apply_of_mem A z w hx, principalIdempotent_apply_of_mem A z w hAx]
  split <;> simp

/-- The index of a spectral value is the least exponent at which the corresponding
generalized eigenspace reaches its maximal value. -/
noncomputable def primaryIndex (A : Matrix n n ℂ) (z : ℂ) : ℕ :=
  (matrixEnd A).maxGenEigenspaceIndex z

/-- The $k$th generalized eigenspace is the kernel of the $k$th shifted power. -/
theorem genEigenspace_eq_ker_shift (A : Matrix n n ℂ) (z : ℂ) (k : ℕ) :
    Module.End.genEigenspace A.mulVecLin z k = ((A - z • 1) ^ k).mulVecLin.ker := by
  change (matrixEnd A).genEigenspace z k = _
  rw [Module.End.genEigenspace_nat, ← toLin'_apply', toLin'_pow, map_sub, map_smul, toLin'_one]
  rfl

/-- From the primary index onward, each shifted power has the maximal
generalized eigenspace as its kernel. -/
theorem maxGenEigenspace_eq_ker_shift (A : Matrix n n ℂ) (z : ℂ)
    {k : ℕ} (hk : primaryIndex A z ≤ k) :
    Module.End.maxGenEigenspace A.mulVecLin z = ((A - z • 1) ^ k).mulVecLin.ker := by
  rw [Module.End.maxGenEigenspace_eq,
    ← Module.End.genEigenspace_eq_genEigenspace_maxUnifEigenspaceIndex_of_le (matrixEnd A) z hk,
    genEigenspace_eq_ker_shift]

omit [DecidableEq n] in
/-- An exponent which gives the maximal generalized eigenspace is at least the
primary index. -/
theorem primaryIndex_le_of_genEigenspace_eq (A : Matrix n n ℂ) (z : ℂ) {k : ℕ}
    (h : Module.End.maxGenEigenspace A.mulVecLin z = Module.End.genEigenspace A.mulVecLin z k) :
    primaryIndex A z ≤ k := by
  change monotonicSequenceLimitIndex
    (((matrixEnd A).genEigenspace z).comp WithTop.coeOrderHom.toOrderHom) ≤ k
  unfold monotonicSequenceLimitIndex
  apply Nat.sInf_le
  intro j hj
  change (matrixEnd A).genEigenspace z k = (matrixEnd A).genEigenspace z j
  exact le_antisymm ((Module.End.genEigenspace _ _).monotone (by exact_mod_cast hj))
    ((Module.End.genEigenspace_le_maximal _ _ j).trans_eq h)

/-- The primary index at a scalar equals its multiplicity in the minimal polynomial. -/
theorem primaryIndex_eq_rootMultiplicity (A : Matrix n n ℂ) (z : ℂ) :
    primaryIndex A z = (minpoly ℂ A).rootMultiplicity z := by
  by_cases hz : z ∈ spectralValues A
  · let S : Matrix n n ℂ := A - z • 1
    let k := S.rankStabilizationIndex
    let l := primaryIndex A z
    have hNZ : ¬ IsUnit S := by
      intro h
      have hS := spectrum.mem_iff.mp ((mem_spectralValues_iff A z).mp hz)
      exact hS (by simpa only [S, neg_sub, Algebra.algebraMap_eq_smul_one] using h.neg)
    have hMin : minpoly ℂ S = (minpoly ℂ A).comp (X + C z) := by
      have hMA := minpoly.monic (Algebra.IsIntegral.isIntegral (R := ℂ) A)
      have hMonic := hMA.comp_X_add_C z
      refine (minpoly.unique ℂ S hMonic ?_ ?_).symm
      · rw [aeval_comp, map_add, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
          show S = A - z • 1 from rfl, sub_add_cancel]
        exact minpoly.aeval ℂ A
      · intro p hp hAnn
        have hComp : aeval A (p.comp (X - C z)) = 0 := by
          rw [aeval_comp, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
          exact hAnn
        have hCompMonic := hp.comp_X_sub_C z
        have hDegree := minpoly.min ℂ A hCompMonic hComp
        rw [degree_eq_natDegree hMA.ne_zero, degree_eq_natDegree hCompMonic.ne_zero,
          natDegree_comp, natDegree_X_sub_C, mul_one] at hDegree
        simpa only [degree_eq_natDegree hMonic.ne_zero, degree_eq_natDegree hp.ne_zero,
          natDegree_comp, natDegree_X_add_C, mul_one] using hDegree
    have hk : k = (minpoly ℂ A).rootMultiplicity z := calc
      k = (minpoly ℂ S).rootMultiplicity 0 :=
        S.rankStabilizationIndex_eq_rootMultiplicity_minpoly hNZ
      _ = _ := by rw [hMin, ← rootMultiplicity_eq_rootMultiplicity]
    have hle : l ≤ k := by
      apply primaryIndex_le_of_genEigenspace_eq
      rw [← Module.End.iSup_genEigenspace_eq (matrixEnd A) z]
      apply le_antisymm ?_ (le_iSup (fun j : ℕ => (matrixEnd A).genEigenspace z j) k)
      refine iSup_le fun j => ?_
      rw [genEigenspace_eq_ker_shift, genEigenspace_eq_ker_shift]
      rcases le_total j k with hj | hj
      · exact S.monotone_ker_mulVecLin_pow hj
      · exact ((S.rank_pow_eq_iff_ker_eq hj).mp
          (S.rank_pow_eq_of_eq_succ S.rankStabilizationIndex_spec.2 hj)).ge
    have hpos : 0 < l := by
      by_contra! h
      have hl : l = 0 := Nat.eq_zero_of_le_zero h
      have h0 := Module.End.maxGenEigenspace_eq (matrixEnd A) z
      change _ = (matrixEnd A).genEigenspace z l at h0
      rw [hl, Nat.cast_zero, Module.End.genEigenspace_zero] at h0
      exact (Module.End.hasEigenvalue_iff.mp ((mem_spectralValues A z).mp hz))
        (le_bot_iff.mp (Module.End.eigenspace_le_maxGenEigenspace.trans_eq h0))
    have hge : k ≤ l := by
      apply (S.rank_pow_eq_succ_iff hpos).mp
      apply (S.rank_pow_eq_iff_ker_eq (Nat.le_succ l)).mpr
      exact (maxGenEigenspace_eq_ker_shift A z (k := l) le_rfl).symm.trans
        (maxGenEigenspace_eq_ker_shift A z (k := l + 1) (Nat.le_succ l))
    exact (le_antisymm hle hge).trans hk
  · have h0 : primaryIndex A z = 0 := by
      apply Nat.eq_zero_of_le_zero
      apply primaryIndex_le_of_genEigenspace_eq
      rw [maxGenEigenspace_eq_bot_of_notMem A z hz, Nat.cast_zero, Module.End.genEigenspace_zero]
    rw [h0]
    exact (rootMultiplicity_eq_zero (fun h =>
      hz ((mem_spectralValues_iff A z).mpr
        ((spectrum.mem_iff_isRoot_minpoly (Algebra.IsIntegral.isIntegral A)).mpr h)))).symm

private theorem commute_shift {A E : Matrix n n ℂ} (h : Commute A E) (z : ℂ) :
    Commute (A - z • 1) E :=
  h.sub_left ((Commute.one_left E).smul_left z)

private theorem principalIdempotent_mul_shift_pow (A : Matrix n n ℂ) (z : ℂ)
    {k : ℕ} (hk : primaryIndex A z ≤ k) :
    principalIdempotent A z * (A - z • 1) ^ k = 0 := by
  rw [← ((commute_shift (commute_principalIdempotent A z) z).pow_left k).eq, ext_iff_mulVec]
  intro x
  have hx : (principalIdempotent A z).mulVecLin x ∈ (matrixEnd A).maxGenEigenspace z :=
    range_principalIdempotent A z ▸ LinearMap.mem_range_self _ x
  rw [maxGenEigenspace_eq_ker_shift A z hk] at hx
  rw [zero_mulVec]
  change (((A - z • 1) ^ k) * principalIdempotent A z).mulVecLin x = 0
  rw [mulVecLin_mul, LinearMap.comp_apply]
  exact LinearMap.mem_ker.mp hx

/-- The principal idempotents of a matrix satisfy the primary decomposition equations.
The family is extended by zero outside the spectrum. -/
structure IsPrimaryDecomposition (A : Matrix n n ℂ) (E : ℂ → Matrix n n ℂ) : Prop where
  supported : ∀ z ∉ spectralValues A, E z = 0
  mul : ∀ z w, E z * E w = if z = w then E z else 0
  sum : ∑ z ∈ spectralValues A, E z = 1
  decomposition : A = (∑ z ∈ spectralValues A, z • E z) +
    ∑ z ∈ spectralValues A, (A - z • 1) * E z
  commute : ∀ z, Commute A (E z)
  annihilate : ∀ z k, primaryIndex A z ≤ k → E z * (A - z • 1) ^ k = 0

/-- Maps into the respective primary subspaces that sum to the identity must be
the principal idempotents. -/
theorem eq_principalIdempotent_of_range_and_sum (A : Matrix n n ℂ) (E : ℂ → Matrix n n ℂ)
    (hSupport : ∀ z ∉ spectralValues A, E z = 0)
    (hSum : ∑ z ∈ spectralValues A, E z = 1)
    (hRange : ∀ z, (E z).mulVecLin.range ≤ Module.End.maxGenEigenspace A.mulVecLin z) :
    E = principalIdempotent A := by
  let P := principalIdempotent A
  have hPE (z w : ℂ) : P z * E w = if z = w then E w else 0 := by
    rw [ext_iff_mulVec]
    intro x
    have hx := hRange w (LinearMap.mem_range_self (E w).mulVecLin x)
    change (P z * E w).mulVecLin x = (if z = w then E w else 0).mulVecLin x
    rw [mulVecLin_mul, LinearMap.comp_apply, principalIdempotent_apply_of_mem A z w hx]
    by_cases h : z = w <;> simp [h, eq_comm]
  funext z
  by_cases hz : z ∈ spectralValues A
  · symm
    calc
      P z = P z * (∑ w ∈ spectralValues A, E w) := by rw [hSum, Matrix.mul_one]
      _ = ∑ w ∈ spectralValues A, P z * E w := Finset.mul_sum _ _ _
      _ = E z := by
        rw [Finset.sum_eq_single_of_mem z hz]
        · simp [hPE]
        · intro w _ hw
          rw [hPE, ite_eq_right (Ne.symm hw)]
  · exact (hSupport z hz).trans (principalIdempotent_eq_zero_of_notMem A z hz).symm

/-- **Theorem 10** of [benIsrael2003generalized], Chapter 2. The primary
decomposition equations determine the family of principal idempotents uniquely. -/
theorem theorem_10 (A : Matrix n n ℂ) :
    IsPrimaryDecomposition A (principalIdempotent A) ∧
      ∀ E, IsPrimaryDecomposition A E → E = principalIdempotent A := by
  let P := principalIdempotent A
  have hsum : ∑ z ∈ spectralValues A, P z = 1 := sum_principalIdempotent A
  refine ⟨⟨principalIdempotent_eq_zero_of_notMem A, principalIdempotent_mul A, hsum, ?_,
    commute_principalIdempotent A, fun z _ hk => principalIdempotent_mul_shift_pow A z hk⟩, ?_⟩
  · calc
      A = A * (∑ z ∈ spectralValues A, P z) := by rw [hsum, Matrix.mul_one]
      _ = ∑ z ∈ spectralValues A, A * P z := Finset.mul_sum _ _ _
      _ = ∑ z ∈ spectralValues A, (z • P z + (A - z • 1) * P z) := by
        apply Finset.sum_congr rfl
        intro z _
        rw [Matrix.sub_mul, smul_mul_assoc, Matrix.one_mul]
        abel
      _ = _ := Finset.sum_add_distrib
  · intro E hE
    apply eq_principalIdempotent_of_range_and_sum A E hE.supported hE.sum
    rintro z _ ⟨x, rfl⟩
    let k := primaryIndex A z
    have h0 : (A - z • 1) ^ k * E z = 0 :=
      ((commute_shift (hE.commute z) z).pow_left k).eq.trans (hE.annihilate z k le_rfl)
    rw [maxGenEigenspace_eq_ker_shift A z (show primaryIndex A z ≤ k from le_rfl),
      LinearMap.mem_ker, ← LinearMap.comp_apply, ← mulVecLin_mul, h0]
    simp

/-- The distinct roots of the minimal polynomial are the spectral values. -/
theorem spectralValues_eq_minpoly_roots (A : Matrix n n ℂ) :
    spectralValues A = (minpoly ℂ A).roots.toFinset := by
  ext z
  rw [mem_spectralValues_iff, Multiset.mem_toFinset,
    spectrum.mem_iff_mem_roots_minpoly (Algebra.IsIntegral.isIntegral A)]

/-- The factors of the minimal polynomial have exponents equal to the primary indices. -/
theorem minpoly_eq_prod_primary (A : Matrix n n ℂ) :
    minpoly ℂ A = ∏ z ∈ spectralValues A, (X - C z) ^ primaryIndex A z := by
  have hm : (minpoly ℂ A).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral A)
  calc
    minpoly ℂ A = Hermite.nodalMultiset (minpoly ℂ A).roots :=
      Hermite.eq_nodalMultiset_roots hm (IsAlgClosed.splits _)
    _ = _ := by
      simp only [Hermite.nodalMultiset_eq_prod_count, spectralValues_eq_minpoly_roots,
        primaryIndex_eq_rootMultiplicity, count_roots]

/-- The projector description of a principal idempotent agrees with its
polynomial construction by Hermite interpolation. -/
theorem principalIdempotent_eq_spectralIdempotent (A : Matrix n n ℂ) (z : ℂ) :
    principalIdempotent A z = spectralIdempotent A z := by
  have hA : IsIntegral ℂ A := Algebra.IsIntegral.isIntegral A
  have hs : (minpoly ℂ A).Splits := IsAlgClosed.splits _
  have hEq : spectralIdempotent A = principalIdempotent A := by
    apply eq_principalIdempotent_of_range_and_sum
    · intro w hw
      apply spectralIdempotent_eq_zero_of_notMem
      rwa [spectralValues_eq_minpoly_roots, Multiset.mem_toFinset] at hw
    · rw [spectralValues_eq_minpoly_roots]
      exact sum_spectralIdempotent hA hs
    · rintro w _ ⟨x, rfl⟩
      have h := pow_mul_spectralIdempotent hA hs w
      have hk : primaryIndex A w ≤ (minpoly ℂ A).rootMultiplicity w :=
        (primaryIndex_eq_rootMultiplicity A w).le
      rw [Algebra.algebraMap_eq_smul_one] at h
      rw [maxGenEigenspace_eq_ker_shift A w hk, LinearMap.mem_ker, ← LinearMap.comp_apply,
        ← mulVecLin_mul, h]
      simp
  exact congrFun hEq.symm z

/-- **Exercise 29** of [benIsrael2003generalized], Chapter 2, polynomial representation.
A principal idempotent is the evaluation of a scalar polynomial at $A$. -/
theorem exercise_29_polynomial (A : Matrix n n ℂ) (z : ℂ) :
    ∃ p : ℂ[X], principalIdempotent A z = aeval A p := by
  rw [principalIdempotent_eq_spectralIdempotent, spectralIdempotent]
  exact ⟨_, rfl⟩

/-- **Exercise 29** of [benIsrael2003generalized], Chapter 2. Clearing the
denominators of the partial fractions of $1/m$ gives polynomials whose values
at $A$ are the principal idempotents. -/
theorem exercise_29 (A : Matrix n n ℂ) (h : ℂ → ℂ[X])
    (hh : (∑ w ∈ spectralValues A,
      h w * ∏ z ∈ (spectralValues A).erase w, (X - C z) ^ primaryIndex A z) = 1)
    (w : ℂ) (hw : w ∈ spectralValues A) :
    principalIdempotent A w = aeval A
      (h w * ∏ z ∈ (spectralValues A).erase w, (X - C z) ^ primaryIndex A z) := by
  let F (z : ℂ) := (X - C z) ^ primaryIndex A z
  let p (z : ℂ) := h z * ∏ t ∈ (spectralValues A).erase z, F t
  let E (z : ℂ) := if z ∈ spectralValues A then aeval A (p z) else 0
  have hSum : ∑ z ∈ spectralValues A, E z = 1 := calc
    _ = ∑ z ∈ spectralValues A, aeval A (p z) := by
      exact Finset.sum_congr rfl fun z hz => by simp [E, hz]
    _ = aeval A (∑ z ∈ spectralValues A, p z) := (map_sum _ _ _).symm
    _ = 1 := by rw [show ∑ z ∈ spectralValues A, p z = 1 from hh, map_one]
  have hE : E = principalIdempotent A := by
    apply eq_principalIdempotent_of_range_and_sum A E (fun z hz => by simp [E, hz]) hSum
    rintro z _ ⟨x, rfl⟩
    by_cases hz : z ∈ spectralValues A
    · have hp : F z * p z = h z * minpoly ℂ A := calc
        F z * p z = h z * (F z * ∏ t ∈ (spectralValues A).erase z, F t) := mul_left_comm ..
        _ = h z * (∏ t ∈ spectralValues A, F t) := by
          rw [Finset.mul_prod_erase _ _ hz]
        _ = _ := congrArg (h z * ·) (minpoly_eq_prod_primary A).symm
      have hKill : (A - z • 1) ^ primaryIndex A z * E z = 0 := calc
        _ = aeval A (F z * p z) := by
          simp only [E, ite_eq_left hz, F, map_mul, map_pow, map_sub, aeval_X, aeval_C,
            Algebra.algebraMap_eq_smul_one]
        _ = 0 := by rw [hp, map_mul, minpoly.aeval, mul_zero]
      rw [maxGenEigenspace_eq_ker_shift A z (k := primaryIndex A z) le_rfl,
        LinearMap.mem_ker, ← LinearMap.comp_apply, ← mulVecLin_mul, hKill]
      simp
    · simp [E, hz]
  simpa [E, p, F, hw] using congrFun hE.symm w

/-- **Corollary 8** of [benIsrael2003generalized], Chapter 2. Polynomial evaluation at
a matrix is the sum of the Taylor expansions truncated on its primary components. -/
theorem corollary_8 (A : Matrix n n ℂ) (p : ℂ[X]) :
    aeval A p = ∑ z ∈ spectralValues A, principalIdempotent A z *
      (∑ j ∈ Finset.range (primaryIndex A z),
        (((derivative^[j]) p).eval z / (j.factorial : ℂ)) • (A - z • 1) ^ j) := by
  calc
    aeval A p = (∑ z ∈ spectralValues A, principalIdempotent A z) * aeval A p := by
      rw [sum_principalIdempotent, Matrix.one_mul]
    _ = ∑ z ∈ spectralValues A, principalIdempotent A z * aeval A p := Finset.sum_mul _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _
      let S : Matrix n n ℂ := A - z • 1
      let q := taylor z p
      let r := max (q.natDegree + 1) (primaryIndex A z)
      have hTaylor : aeval S q = aeval A p := by
        rw [show q = p.comp (X + C z) from taylor_apply _ _, aeval_comp, map_add, aeval_X,
          aeval_C, Algebra.algebraMap_eq_smul_one, show S = A - z • 1 from rfl, sub_add_cancel]
      have hDeg : q.natDegree < r := Nat.lt_of_succ_le (le_max_left _ _)
      simp only [← Hermite.coeff_taylor_eq_eval_iterate_derivative_div]
      rw [← hTaylor, aeval_eq_sum_range' hDeg, Finset.mul_sum, Finset.mul_sum]
      symm
      apply Finset.sum_subset (Finset.range_mono (le_max_right _ _))
      intro j _ hj
      have hj' : primaryIndex A z ≤ j := Nat.le_of_not_gt ((Finset.mem_range.not).mp hj)
      rw [Matrix.mul_smul, principalIdempotent_mul_shift_pow A z hj', smul_zero]

/-- **Definition 1** of [benIsrael2003generalized], Chapter 2. The class $F(A)$ consists
of the complex functions analytic on some open set containing the spectrum of $A$. -/
def analyticFunctions (A : Matrix n n ℂ) : Set (ℂ → ℂ) :=
  {f | ∃ U : Set ℂ, IsOpen U ∧ (spectralValues A : Set ℂ) ⊆ U ∧ AnalyticOnNhd ℂ f U}

/-- **Equation (50)** of [benIsrael2003generalized], Chapter 2. Evaluate an analytic
function at a matrix by its truncated Taylor expansion on each primary component. -/
noncomputable def matrixFunction (A : Matrix n n ℂ) (f : analyticFunctions A) : Matrix n n ℂ :=
  ∑ z ∈ spectralValues A, principalIdempotent A z *
    (∑ j ∈ Finset.range (primaryIndex A z),
      (((deriv^[j]) (f : ℂ → ℂ)) z / (j.factorial : ℂ)) • (A - z • 1) ^ j)

/-- The truncated series evaluation is the primary functional calculus of the matrix. -/
theorem matrixFunction_eq_pfc (A : Matrix n n ℂ) (f : analyticFunctions A) :
    matrixFunction A f = pfc (f : ℂ → ℂ) A := by
  have h : IsIntegral ℂ A := Algebra.IsIntegral.isIntegral A
  rw [matrixFunction, pfc_eq_sum_spectralIdempotent h (IsAlgClosed.splits _),
    ← spectralValues_eq_minpoly_roots A]
  apply Finset.sum_congr rfl
  intro z _
  rw [primaryIndex_eq_rootMultiplicity, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hComm := (commute_shift (commute_principalIdempotent A z) z).pow_left j
  rw [Hermite.taylorJet, iteratedDeriv_eq_iterate, Algebra.algebraMap_eq_smul_one,
    Matrix.mul_smul, ← hComm.eq, principalIdempotent_eq_spectralIdempotent]

/-- **Equations (51a)–(51b)** of [benIsrael2003generalized], Chapter 2. A polynomial
whose derivatives match those of the function through the required orders gives
the same matrix value. -/
theorem matrixFunction_eq_aeval_of_deriv_eq (A : Matrix n n ℂ) (f : analyticFunctions A)
    (p : ℂ[X]) (hp : ∀ z ∈ spectralValues A, ∀ j < primaryIndex A z,
      ((derivative^[j]) p).eval z = ((deriv^[j]) (f : ℂ → ℂ)) z) :
    matrixFunction A f = aeval A p := by
  rw [matrixFunction, corollary_8 A p]
  apply Finset.sum_congr rfl
  intro z hz
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [hp z hz j (Finset.mem_range.mp hj)]

/-- The spectral Hermite interpolation conditions determine exactly one polynomial
of degree less than the degree of the minimal polynomial. -/
theorem existsUnique_spectralInterpolant (A : Matrix n n ℂ) (f : analyticFunctions A) :
    ∃! p : ℂ[X], p.degree < (minpoly ℂ A).degree ∧
      ∀ z ∈ spectralValues A, ∀ j < primaryIndex A z,
        ((derivative^[j]) p).eval z = ((deriv^[j]) (f : ℂ → ℂ)) z := by
  let m := minpoly ℂ A
  have hs : m.Splits := IsAlgClosed.splits _
  have hm : m ≠ 0 := minpoly.ne_zero_of_finite ℂ A
  have hEquiv (p : ℂ[X]) :
      Hermite.IsJetInterpolant m.roots (Hermite.taylorJet (f : ℂ → ℂ)) p ↔
        ∀ z ∈ spectralValues A, ∀ j < primaryIndex A z,
          ((derivative^[j]) p).eval z = ((deriv^[j]) (f : ℂ → ℂ)) z := by
    rw [Hermite.isJetInterpolant_iff_coeff_taylor, spectralValues_eq_minpoly_roots]
    simp only [m, Multiset.mem_toFinset, primaryIndex_eq_rootMultiplicity, count_roots,
      Hermite.coeff_taylor_eq_eval_iterate_derivative_div, Hermite.taylorJet,
      iteratedDeriv_eq_iterate]
    constructor
    · intro h z hz j hj
      have hn : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
      have he := congrArg (fun u : ℂ => u * (j.factorial : ℂ)) (h z hz j hj)
      simpa only [div_mul_cancel₀ _ hn] using he
    · intro h z hz j hj
      rw [h z hz j hj]
  have h := Hermite.existsUnique_isJetInterpolant m.roots (Hermite.taylorJet (f : ℂ → ℂ))
  simpa only [← hs.degree_eq_card_roots hm, hEquiv] using h

/-- **Equation (57)** of [benIsrael2003generalized], Chapter 2. Outside the spectrum,
the resolvent is the sum of the finite Laurent principal parts at the eigenvalues. -/
theorem resolvent_eq_sum_primary (A : Matrix n n ℂ) (z : ℂ) (hz : z ∉ spectralValues A) :
    (z • 1 - A)⁻¹ = ∑ w ∈ spectralValues A, ∑ j ∈ Finset.range (primaryIndex A w),
      ((z - w) ^ (j + 1))⁻¹ • ((A - w • 1) ^ j * principalIdempotent A w) := by
  have hz' : z ∉ (minpoly ℂ A).roots := by
    rwa [spectralValues_eq_minpoly_roots, Multiset.mem_toFinset] at hz
  have h := inverse_sub_eq_sum_spectralIdempotent (Algebra.IsIntegral.isIntegral A)
    (IsAlgClosed.splits (minpoly ℂ A)) hz'
  simpa only [Algebra.algebraMap_eq_smul_one, Matrix.nonsing_inv_eq_ringInverse,
    spectralValues_eq_minpoly_roots, primaryIndex_eq_rootMultiplicity,
    principalIdempotent_eq_spectralIdempotent] using h

open scoped Matrix.Norms.L2Operator Real in
/-- **Theorem 11** of [benIsrael2003generalized], Chapter 2, circular contour.
The Cauchy integral of $f$ times the resolvent around a circle enclosing the
spectrum is $f(A)$ after division by $2\pi i$. -/
theorem theorem_11_circle (A : Matrix n n ℂ) (f : analyticFunctions A) (c : ℂ) (r : ℝ)
    (hf : DifferentiableOn ℂ (f : ℂ → ℂ) (Metric.closedBall c r))
    (hσ : spectrum ℂ A ⊆ Metric.ball c r) :
    matrixFunction A f = (2 * π * Complex.I)⁻¹ •
      ∮ z in C(c, r), (f : ℂ → ℂ) z • (z • 1 - A)⁻¹ := by
  rw [matrixFunction_eq_pfc]
  simpa only [Algebra.algebraMap_eq_smul_one, Matrix.nonsing_inv_eq_ringInverse] using
    pfc_eq_circleIntegral (Algebra.IsIntegral.isIntegral A) hf hσ

open scoped Matrix.Norms.L2Operator Real in
/-- **Theorem 11** of [benIsrael2003generalized], Chapter 2, Equation (53), for
Lipschitz contours in open convex sets of holomorphy. A finite family of paths
avoids the spectrum and has total winding number one at each eigenvalue. -/
theorem theorem_11 (A : Matrix n n ℂ) (f : analyticFunctions A) {ι : Type*} [Fintype ι]
    {p : ι → ℂ} (γ : (i : ι) → Path (p i) (p i)) (hγ : ∀ i, (γ i).IsLipschitz)
    (S : ι → Set ℂ) (hOpen : ∀ i, IsOpen (S i)) (hConvex : ∀ i, Convex ℝ (S i))
    (hRange : ∀ i, Set.range (γ i) ⊆ S i)
    (hf : ∀ i, DifferentiableOn ℂ (f : ℂ → ℂ) (S i))
    (hAvoid : ∀ i w, w ∈ spectralValues A → w ∉ Set.range (γ i))
    (hIndex : ∀ w ∈ spectralValues A, ∑ i, complexPathIndex (γ i) w = 1) :
    matrixFunction A f = ∑ i, (2 * π * Complex.I)⁻¹ •
      complexLineIntegral (γ i) (fun z => (f : ℂ → ℂ) z • (z • 1 - A)⁻¹) := by
  rw [matrixFunction_eq_pfc]
  have hRoots (w : ℂ) (hw : w ∈ (minpoly ℂ A).roots.toFinset) : w ∈ spectralValues A := by
    rwa [spectralValues_eq_minpoly_roots]
  simpa only [Algebra.algebraMap_eq_smul_one, Matrix.nonsing_inv_eq_ringInverse] using
    pfc_eq_sum_complexLineIntegral (Algebra.IsIntegral.isIntegral A) γ hγ S hOpen hConvex hRange
      (fun i w hw => hAvoid i w (hRoots w hw)) hf (fun w hw => hIndex w (hRoots w hw))

open scoped Matrix.Norms.L2Operator Real in
/-- **Theorem 11** of [benIsrael2003generalized], Chapter 2, for one
Lipschitz loop in a disk of holomorphy with winding number one
at every eigenvalue. -/
theorem theorem_11_path (A : Matrix n n ℂ) (f : analyticFunctions A) {p c : ℂ}
    (γ : Path p p) (hγ : γ.IsLipschitz) {r : ℝ} (hDisk : Set.range γ ⊆ Metric.ball c r)
    (hf : DifferentiableOn ℂ (f : ℂ → ℂ) (Metric.ball c r))
    (hAvoid : ∀ w ∈ spectralValues A, w ∉ Set.range γ)
    (hIndex : ∀ w ∈ spectralValues A, complexPathIndex γ w = 1) :
    matrixFunction A f = (2 * π * Complex.I)⁻¹ •
      complexLineIntegral γ (fun z => (f : ℂ → ℂ) z • (z • 1 - A)⁻¹) := by
  simpa using theorem_11 A f
    (ι := Unit) (p := fun _ => p) (fun _ => γ) (fun _ => hγ)
    (fun _ => Metric.ball c r) (fun _ => Metric.isOpen_ball) (fun _ => convex_ball _ _)
    (fun _ => hDisk) (fun _ => hf) (fun _ => hAvoid)
    (fun w hw => by simpa using hIndex w hw)

end BenIsraelGreville.Chapter02
