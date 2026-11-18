/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.RankStabilization
import Numlib.LinearAlgebra.Matrix.Drazin
import NumlibSurface.BenIsraelGreville.Chapter04.Section01

/-!
# The matrix index

Section 4.2 of [benIsrael2003generalized] defines the index by the first positive equality
of successive ranks. From the index onward the range and kernel of the powers are constant.

## Deviations from the source

* **Lemma 1(d)** (reading). The exponents under consideration are the positive exponents
  of the spectral inverse equations.
-/

namespace BenIsraelGreville.Chapter04

open Matrix Polynomial
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Equations (5), (7), and (8)** of [benIsrael2003generalized], Chapter 4. For commuting
matrices $A,X$, the spectral inverse equations $A^kXA=A^k$ and $XAX=X$ can be written
$A^{k+1}X=A^k$ and $AX^2=X$. -/
theorem drazin_equations_iff (k : ℕ) (A X : Matrix n n ℂ) (h : Commute A X) :
    SatisfiesFirstPowerEquation k A X ∧ A.IsOuterInverse X ↔
      A ^ (k + 1) * X = A ^ k ∧ A * X ^ 2 = X := by
  rw [SatisfiesFirstPowerEquation, isOuterInverse_iff, pow_succ, pow_two,
    Matrix.mul_assoc (A ^ k) A X, h.eq, ← Matrix.mul_assoc (A ^ k) X A]
  rw [← Matrix.mul_assoc A X X, h.eq]

/-- **Definition 1** of [benIsrael2003generalized], Chapter 4. The matrix index is the
least positive $k$ for which $A^k$ and $A^{k+1}$ have the same rank. -/
noncomputable abbrev matrixIndex (A : Matrix n n ℂ) : ℕ :=
  A.rankStabilizationIndex

private theorem matrixIndex_eq_of_rank_pow_eq (A B : Matrix n n ℂ)
    (h : ∀ k : ℕ, (A ^ k).rank = (B ^ k).rank) :
    matrixIndex A = matrixIndex B := by
  have ha := A.rankStabilizationIndex_spec
  have hb := B.rankStabilizationIndex_spec
  refine le_antisymm ((A.rank_pow_eq_succ_iff hb.1).mp ?_) ((B.rank_pow_eq_succ_iff ha.1).mp ?_)
  · rw [h, h]
    exact hb.2
  · rw [← h, ← h]
    exact ha.2

/-- Transposing a complex square matrix leaves its index unchanged. -/
theorem matrixIndex_transpose (A : Matrix n n ℂ) :
    matrixIndex Aᵀ = matrixIndex A :=
  matrixIndex_eq_of_rank_pow_eq _ _ fun k => by rw [← transpose_pow, rank_transpose]

/-- Taking the conjugate transpose of a complex square matrix leaves its index unchanged. -/
theorem matrixIndex_conjTranspose (A : Matrix n n ℂ) :
    matrixIndex Aᴴ = matrixIndex A :=
  matrixIndex_eq_of_rank_pow_eq _ _ fun k => by rw [← conjTranspose_pow, rank_conjTranspose]

/-- **Lemma 1** of [benIsrael2003generalized], Chapter 4. The powers of $A$, $A^T$, and $A^H$
have ranks, ranges, and kernels constant from the index onward. At a positive exponent below
the index the range and kernel both differ from those at every strictly greater exponent.

**Reading.** Part (d) concerns positive exponents, as in the surrounding spectral equations.
With the positive-index convention, an invertible matrix has index one and already stabilizes
at exponent zero. -/
theorem lemma_4_1 (A : Matrix n n ℂ) (B : Matrix n n ℂ)
    (hB : B = A ∨ B = Aᵀ ∨ B = Aᴴ) :
    (∀ l : ℕ, matrixIndex A ≤ l →
      (B ^ matrixIndex A).rank = (B ^ l).rank ∧
        LinearMap.range (B ^ matrixIndex A).mulVecLin = LinearMap.range (B ^ l).mulVecLin ∧
        LinearMap.ker (B ^ matrixIndex A).mulVecLin = LinearMap.ker (B ^ l).mulVecLin) ∧
    (∀ k l : ℕ, 0 < k → k < matrixIndex A → k < l →
      LinearMap.range (B ^ k).mulVecLin ≠ LinearMap.range (B ^ l).mulVecLin ∧
        LinearMap.ker (B ^ k).mulVecLin ≠ LinearMap.ker (B ^ l).mulVecLin) := by
  have hBA : matrixIndex B = matrixIndex A := by
    rcases hB with rfl | rfl | rfl
    · rfl
    · exact matrixIndex_transpose A
    · exact matrixIndex_conjTranspose A
  rw [← hBA]
  constructor
  · intro l hl
    have h := B.rank_pow_eq_of_eq_succ B.rankStabilizationIndex_spec.2 hl
    exact ⟨h, (B.rank_pow_eq_iff_range_eq hl).mp h, (B.rank_pow_eq_iff_ker_eq hl).mp h⟩
  · intro k l hpos hbelow hkl
    have hne : (B ^ k).rank ≠ (B ^ l).rank := by
      intro eq
      have hstep : (B ^ (k + 1)).rank ≤ (B ^ k).rank := by
        rw [pow_succ]
        exact rank_mul_le_left _ _
      have hlstep : (B ^ l).rank ≤ (B ^ (k + 1)).rank :=
        Submodule.finrank_mono (B.antitone_range_mulVecLin_pow hkl)
      have h : (B ^ k).rank = (B ^ (k + 1)).rank :=
        le_antisymm (by exact eq.le.trans hlstep) hstep
      exact hbelow.not_ge ((B.rank_pow_eq_succ_iff hpos).mp h)
    exact ⟨hne ∘ (B.rank_pow_eq_iff_range_eq hkl.le).mpr,
      hne ∘ (B.rank_pow_eq_iff_ker_eq hkl.le).mpr⟩

/-- **Theorem 1, solvability criterion** of [benIsrael2003generalized], Chapter 4. For
positive $k$, the power equation $A^{k+1}X=A^k$ is solvable precisely when $k$ is at least
the index of $A$. -/
theorem theorem_4_1_solvable (A : Matrix n n ℂ) {k : ℕ} (hk : 0 < k) :
    (∃ X : Matrix n n ℂ, A ^ (k + 1) * X = A ^ k) ↔ matrixIndex A ≤ k := by
  rw [← A.rank_pow_eq_succ_iff hk]
  constructor
  · rintro ⟨X, hX⟩
    refine le_antisymm ?_ ?_
    · calc
        (A ^ k).rank = (A ^ (k + 1) * X).rank := congrArg rank hX.symm
        _ ≤ (A ^ (k + 1)).rank := rank_mul_le_left _ _
    · rw [pow_succ]
      exact rank_mul_le_left _ _
  · intro heq
    let B := A ^ (k + 1)
    refine ⟨B.pinv * A ^ k, ext_iff_mulVec.mpr fun x => ?_⟩
    have hx : (A ^ k).mulVecLin x ∈ LinearMap.range B.mulVecLin := by
      rw [← (A.rank_pow_eq_iff_range_eq (Nat.le_succ k)).mp heq]
      exact LinearMap.mem_range_self _ _
    obtain ⟨y, hy⟩ := hx
    change B.mulVecLin y = (A ^ k).mulVecLin x at hy
    change (B * (B.pinv * A ^ k)).mulVecLin x = (A ^ k).mulVecLin x
    rw [mulVecLin_mul, LinearMap.comp_apply, mulVecLin_mul, LinearMap.comp_apply, ← hy,
      ← LinearMap.comp_apply, ← mulVecLin_mul, ← LinearMap.comp_apply, ← mulVecLin_mul,
      mul_pinv_mul_self]

/-- A generalized zero-eigenvector has grade $k$ when $k$ is the first exponent
at which the vector is annihilated. -/
def IsZeroVectorOfGrade (A : Matrix n n ℂ) (v : n → ℂ) (k : ℕ) : Prop :=
  0 < k ∧ (A ^ k) *ᵥ v = 0 ∧ (A ^ (k - 1)) *ᵥ v ≠ 0

private theorem index_isGreatest_grade {A : Matrix n n ℂ} (hA : ¬ IsUnit A) :
    IsGreatest {k : ℕ | ∃ v, IsZeroVectorOfGrade A v k} (matrixIndex A) := by
  let r := matrixIndex A
  have hpos : 0 < r := A.rankStabilizationIndex_spec.1
  have hpred : r - 1 + 1 = r := by omega
  have hK (j : ℕ) (hj : r ≤ j) :
      LinearMap.ker (A ^ r).mulVecLin = LinearMap.ker (A ^ j).mulVecLin :=
    (A.rank_pow_eq_iff_ker_eq hj).mp
      (A.rank_pow_eq_of_eq_succ A.rankStabilizationIndex_spec.2 hj)
  have hProper : ¬ LinearMap.ker (A ^ r).mulVecLin ≤
      LinearMap.ker (A ^ (r - 1)).mulVecLin := by
    intro hle
    have he := le_antisymm (A.monotone_ker_mulVecLin_pow (Nat.sub_le r 1)) hle
    by_cases h : 0 < r - 1
    · have hr := (A.rank_pow_eq_iff_ker_eq (Nat.sub_le r 1)).mpr he
      have hs : (A ^ (r - 1)).rank = (A ^ (r - 1 + 1)).rank := by rwa [hpred]
      have hh : r ≤ r - 1 := (A.rank_pow_eq_succ_iff h).mp hs
      omega
    · have hr : r = 1 := by omega
      have hid : (1 : Matrix n n ℂ).mulVecLin = LinearMap.id := by
        rw [← toLin'_apply', toLin'_one]
      have hk : LinearMap.ker A.mulVecLin = ⊥ := by
        simpa only [hr, Nat.sub_self, pow_zero, pow_one, hid, LinearMap.ker_id] using he.symm
      exact hA (mulVec_injective_iff_isUnit.mp (LinearMap.ker_eq_bot.mp hk))
  refine ⟨?_, ?_⟩
  · obtain ⟨v, hv, hv'⟩ : ∃ v, v ∈ LinearMap.ker (A ^ r).mulVecLin ∧
        v ∉ LinearMap.ker (A ^ (r - 1)).mulVecLin := by
      by_contra! h
      exact hProper h
    exact ⟨v, hpos, hv, hv'⟩
  · intro j hj
    obtain ⟨v, hj, hv, hn⟩ := hj
    by_contra! h
    have hv' : v ∈ LinearMap.ker (A ^ (j - 1)).mulVecLin := by
      rw [← hK (j - 1) (by omega), hK j h.le]
      exact hv
    exact hn hv'

/-- **Theorem 1** of [benIsrael2003generalized], Chapter 4. The matrix index is the least
positive exponent permitting a solution of $A^{k+1}X=A^k$. When $A$ is singular,
the index is also the multiplicity of zero in the minimal polynomial and the greatest
grade of a generalized zero-eigenvector. -/
theorem theorem_4_1 (A : Matrix n n ℂ) (k : ℕ) :
    (matrixIndex A = k ↔
      IsLeast {j : ℕ | 0 < j ∧ ∃ X : Matrix n n ℂ, A ^ (j + 1) * X = A ^ j} k) ∧
    (¬ IsUnit A →
      (matrixIndex A = k ↔ (minpoly ℂ A).rootMultiplicity 0 = k) ∧
      (matrixIndex A = k ↔ IsGreatest {j : ℕ | ∃ v, IsZeroVectorOfGrade A v j} k)) := by
  have hpos := A.rankStabilizationIndex_spec.1
  have hLeast : IsLeast {j : ℕ | 0 < j ∧ ∃ X : Matrix n n ℂ, A ^ (j + 1) * X = A ^ j}
      (matrixIndex A) :=
    ⟨⟨hpos, (theorem_4_1_solvable A hpos).mpr le_rfl⟩,
      fun _ hj => (theorem_4_1_solvable A hj.1).mp hj.2⟩
  refine ⟨⟨fun h => h ▸ hLeast, fun h => hLeast.unique h⟩, ?_⟩
  intro hA
  have hIndex := A.rankStabilizationIndex_eq_rootMultiplicity_minpoly hA
  have hGrade := index_isGreatest_grade hA
  exact ⟨⟨fun h => hIndex.symm.trans h, fun h => hIndex.trans h⟩,
    ⟨fun h => h ▸ hGrade, fun h => hGrade.unique h⟩⟩

/-- **Equation (13)** of [benIsrael2003generalized], Chapter 4. If $\ell$ is the
multiplicity of zero in the minimal polynomial, the polynomial has the form
$cX^\ell(1-Xq)$ for a nonzero scalar $c$. -/
theorem equation_13 (A : Matrix n n ℂ) :
    ∃ (c : ℂ) (q : ℂ[X]), c ≠ 0 ∧
      minpoly ℂ A = C c * X ^ (minpoly ℂ A).rootMultiplicity 0 * (1 - X * q) :=
  A.exists_minpoly_factorization_at_zero

/-- **Equation (14)** of [benIsrael2003generalized], Chapter 4. The polynomial $q$ in
the factorization of the minimal polynomial satisfies the power equation at $\ell$. -/
theorem equation_14 (A : Matrix n n ℂ) {c : ℂ} {l : ℕ} {q : ℂ[X]} (hc : c ≠ 0)
    (h : minpoly ℂ A = C c * X ^ l * (1 - X * q)) :
    A ^ (l + 1) * aeval A q = A ^ l :=
  A.pow_succ_mul_aeval_eq_of_minpoly_factorization hc h

/-- **Exercise 5** of [benIsrael2003generalized], Chapter 4. The range and kernel of
$A^l$ are complementary precisely when the positive exponent $l$ is at least the index. -/
theorem exercise_4_5 (A : Matrix n n ℂ) {l : ℕ} (hl : 0 < l) :
    IsCompl (LinearMap.range (A ^ l).mulVecLin) (LinearMap.ker (A ^ l).mulVecLin) ↔
      matrixIndex A ≤ l :=
  A.isCompl_range_ker_pow_iff hl

/-- **Exercise 6** of [benIsrael2003generalized], Chapter 4. When two consecutive
powers have the same range, the ranges of all subsequent powers agree. -/
theorem exercise_4_6 (A : Matrix n n ℂ) {k l : ℕ} (hkl : k ≤ l)
    (h : LinearMap.range (A ^ (k + 1)).mulVecLin = LinearMap.range (A ^ k).mulVecLin) :
    LinearMap.range (A ^ (l + 1)).mulVecLin = LinearMap.range (A ^ l).mulVecLin := by
  have hr := (A.rank_pow_eq_iff_range_eq (Nat.le_succ k)).mpr h.symm
  have hl := A.rank_pow_eq_of_eq_succ hr hkl
  have hls := A.rank_pow_eq_of_eq_succ hr (hkl.trans (Nat.le_succ l))
  exact ((A.rank_pow_eq_iff_range_eq (Nat.le_succ l)).mp (hl.symm.trans hls)).symm

/-- **Exercise 7** of [benIsrael2003generalized], Chapter 4. For a square matrix of
positive size, stabilization occurs at a positive exponent at most its size. -/
theorem exercise_4_7 [Nonempty n] (A : Matrix n n ℂ) :
    ∃ k : ℕ, 0 < k ∧ k ≤ Fintype.card n ∧ (A ^ k).rank = (A ^ (k + 1)).rank :=
  ⟨Fintype.card n, Fintype.card_pos, le_rfl, A.rank_pow_eq_succ_of_card_le le_rfl⟩

end BenIsraelGreville.Chapter04
