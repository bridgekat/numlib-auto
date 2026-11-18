/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.Rank

/-!
# Stabilization of the ranks of matrix powers

For a finite square matrix the descending ranges and ascending kernels of its powers
stabilize together. The positive stabilization index is the first positive exponent at
which successive powers have equal rank.
-/

namespace Matrix

open Module

variable {n K : Type*} [Field K] [Fintype n] [DecidableEq n] (A : Matrix n n K)

private theorem mulVecLin_pow_eq (k : ℕ) : (A ^ k).mulVecLin = A.mulVecLin ^ k := by
  simpa only [Matrix.toLin'_apply'] using A.toLin'_pow k

/-- The ranges of the powers of a matrix form a descending sequence. -/
theorem antitone_range_mulVecLin_pow :
    Antitone (fun k : ℕ => LinearMap.range (A ^ k).mulVecLin) := by
  intro k l h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  change LinearMap.range (A ^ (k + d)).mulVecLin ≤ LinearMap.range (A ^ k).mulVecLin
  rw [pow_add, mulVecLin_mul]
  exact LinearMap.range_comp_le_range _ _

/-- The kernels of the powers of a matrix form an ascending sequence. -/
theorem monotone_ker_mulVecLin_pow :
    Monotone (fun k : ℕ => LinearMap.ker (A ^ k).mulVecLin) :=
  monotone_nat_of_le_succ A.ker_mulVecLin_pow_le_succ

/-- Two powers have the same rank exactly when they have the same range. -/
theorem rank_pow_eq_iff_range_eq {k l : ℕ} (hkl : k ≤ l) :
    (A ^ k).rank = (A ^ l).rank ↔
      LinearMap.range (A ^ k).mulVecLin = LinearMap.range (A ^ l).mulVecLin :=
  ⟨fun h => (Submodule.eq_of_le_of_finrank_eq (A.antitone_range_mulVecLin_pow hkl) h.symm).symm,
    fun h => congrArg (fun S : Submodule K (n → K) => finrank K S) h⟩

/-- Two powers have the same rank exactly when they have the same kernel. -/
theorem rank_pow_eq_iff_ker_eq {k l : ℕ} (hkl : k ≤ l) :
    (A ^ k).rank = (A ^ l).rank ↔
      LinearMap.ker (A ^ k).mulVecLin = LinearMap.ker (A ^ l).mulVecLin := by
  have h₁ := rank_add_finrank_ker_mulVecLin (A ^ k)
  have h₂ := rank_add_finrank_ker_mulVecLin (A ^ l)
  refine ⟨fun h => Submodule.eq_of_le_of_finrank_eq (A.monotone_ker_mulVecLin_pow hkl) ?_,
    fun h => ?_⟩
  · omega
  · rw [h] at h₁
    omega

/-- After two successive ranks agree, every later power has that rank. -/
theorem rank_pow_eq_of_eq_succ {k l : ℕ} (hk : (A ^ k).rank = (A ^ (k + 1)).rank)
    (hkl : k ≤ l) : (A ^ k).rank = (A ^ l).rank := by
  have hker := (A.rank_pow_eq_iff_ker_eq (Nat.le_succ k)).mp hk
  have hker' : LinearMap.ker (A.mulVecLin ^ k) = LinearMap.ker (A.mulVecLin ^ k.succ) := by
    simpa only [A.mulVecLin_pow_eq] using hker
  apply (A.rank_pow_eq_iff_ker_eq hkl).mpr
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
  simpa only [A.mulVecLin_pow_eq] using End.ker_pow_constant hker' d

/-- Successive powers of a matrix have equal rank at every exponent at least its size. -/
theorem rank_pow_eq_succ_of_card_le {k : ℕ} (hk : Fintype.card n ≤ k) :
    (A ^ k).rank = (A ^ (k + 1)).rank := by
  rw [← finrank_fintype_fun_eq_card K] at hk
  have h₁ := End.ker_pow_eq_ker_pow_finrank_of_le (f := A.mulVecLin)
    hk
  have h₂ := End.ker_pow_eq_ker_pow_finrank_of_le (f := A.mulVecLin)
    (hk.trans (Nat.le_succ k))
  apply (A.rank_pow_eq_iff_ker_eq (Nat.le_succ k)).mpr
  simpa only [A.mulVecLin_pow_eq] using h₁.trans h₂.symm

/-- The ranks of two successive positive powers of a square matrix eventually agree. -/
theorem exists_pos_rank_pow_eq_succ :
    ∃ k : ℕ, 0 < k ∧ (A ^ k).rank = (A ^ (k + 1)).rank :=
  ⟨Fintype.card n + 1, Nat.succ_pos _, A.rank_pow_eq_succ_of_card_le (Nat.le_succ _)⟩

/-- The least positive exponent $k$ for which $A^k$ and $A^{k+1}$ have the same rank. -/
noncomputable def rankStabilizationIndex : ℕ :=
  Nat.find A.exists_pos_rank_pow_eq_succ

/-- The stabilization index is positive and the ranks at the index and its successor agree. -/
theorem rankStabilizationIndex_spec :
    0 < A.rankStabilizationIndex ∧
      (A ^ A.rankStabilizationIndex).rank = (A ^ (A.rankStabilizationIndex + 1)).rank :=
  Nat.find_spec A.exists_pos_rank_pow_eq_succ

/-- At positive exponents, one-step rank stabilization holds exactly at or above the index. -/
theorem rank_pow_eq_succ_iff {k : ℕ} (hk : 0 < k) :
    (A ^ k).rank = (A ^ (k + 1)).rank ↔ A.rankStabilizationIndex ≤ k := by
  refine ⟨fun h => Nat.find_min' A.exists_pos_rank_pow_eq_succ ⟨hk, h⟩, fun h => ?_⟩
  exact (A.rank_pow_eq_of_eq_succ A.rankStabilizationIndex_spec.2 h).symm.trans
    (A.rank_pow_eq_of_eq_succ A.rankStabilizationIndex_spec.2 (h.trans (Nat.le_succ k)))

/-- The range and kernel of a positive matrix power are complementary exactly when
the exponent is at least the stabilization index. -/
theorem isCompl_range_ker_pow_iff {k : ℕ} (hk : 0 < k) :
    IsCompl (LinearMap.range (A ^ k).mulVecLin) (LinearMap.ker (A ^ k).mulVecLin) ↔
      A.rankStabilizationIndex ≤ k := by
  rw [Submodule.isCompl_iff_disjoint _ _ ?_, Submodule.disjoint_def,
    ← A.rank_pow_eq_succ_iff hk, A.rank_pow_eq_iff_ker_eq (Nat.le_succ k)]
  · constructor
    · intro h
      apply le_antisymm (A.monotone_ker_mulVecLin_pow (Nat.le_succ k))
      intro x hx
      apply h _ ⟨x, rfl⟩
      apply A.monotone_ker_mulVecLin_pow hk
      change (A ^ k).mulVecLin x ∈ LinearMap.ker (A ^ 1).mulVecLin
      rw [pow_one, LinearMap.mem_ker, ← LinearMap.comp_apply, ← mulVecLin_mul, ← pow_succ']
      exact hx
    · intro h y hy hy'
      obtain ⟨x, rfl⟩ := hy
      have hkk : k ≤ k + k := Nat.le_add_right k k
      have hker := (A.rank_pow_eq_iff_ker_eq hkk).mp
        (A.rank_pow_eq_of_eq_succ ((A.rank_pow_eq_iff_ker_eq (Nat.le_succ k)).mpr h) hkk)
      change x ∈ LinearMap.ker (A ^ k).mulVecLin
      rwa [hker, LinearMap.mem_ker, pow_add, mulVecLin_mul, LinearMap.comp_apply]
  · rw [finrank_fintype_fun_eq_card]
    exact (rank_add_finrank_ker_mulVecLin (A ^ k)).ge

end Matrix
