/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Numlib.LinearAlgebra.Eigenspace.Spectral
import Numlib.LinearAlgebra.Matrix.GeneralizedInverse

/-!
# Matrix functions and primary decomposition

Section 2.5 of [benIsrael2003generalized] constructs matrix functions using the
projections onto the generalized eigenspaces.
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

private theorem maxGenEigenspace_eq_ker_shift (A : Matrix n n ℂ) (z : ℂ)
    {k : ℕ} (hk : primaryIndex A z ≤ k) :
    (matrixEnd A).maxGenEigenspace z = ((A - z • 1) ^ k).mulVecLin.ker := by
  rw [Module.End.maxGenEigenspace_eq,
    ← Module.End.genEigenspace_eq_genEigenspace_maxUnifEigenspaceIndex_of_le (matrixEnd A) z hk,
    Module.End.genEigenspace_nat, ← toLin'_apply', toLin'_pow, map_sub, map_smul, toLin'_one]
  rfl

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

private theorem coeff_taylor_eq_derivative_div_factorial (p : ℂ[X]) (z : ℂ) (j : ℕ) :
    (taylor z p).coeff j = ((derivative^[j]) p).eval z / (j.factorial : ℂ) := by
  have h := congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℂ) (k := j)) p
  have he : (j.factorial : ℂ) * (hasseDeriv j p).eval z = ((derivative^[j]) p).eval z := calc
    _ = (j.factorial • hasseDeriv j p).eval z := by
      change _ = Polynomial.leval z (j.factorial • hasseDeriv j p)
      rw [map_nsmul, nsmul_eq_mul]
      rfl
    _ = _ := congrArg (Polynomial.eval z) h
  rw [taylor_coeff, ← he, mul_comm,
    mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j))]

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
      simp only [← coeff_taylor_eq_derivative_div_factorial]
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

end BenIsraelGreville.Chapter02
