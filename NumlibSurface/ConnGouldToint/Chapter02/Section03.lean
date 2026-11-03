import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.Analysis.InnerProductSpace.Energy

/-! # Vector and matrix norms

Section 2.3 of [conn2000trust] defines dual and energy norms and compares
the induced and Frobenius matrix norms.
-/

open scoped ENNReal Matrix.Norms.Frobenius
open Matrix

namespace ConnGouldToint.Chapter02

section Dual

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **(2.3.1)** The dual norm is the operator norm of a real linear functional.
In coordinates, the functional associated with a vector `x` sends `y` to its dot product
with `x`. -/
noncomputable abbrev dualNorm (φ : E →L[ℝ] ℝ) : ℝ := ‖φ‖

/-- **(2.3.1)** The dual norm equals the supremum over the unit ball and the supremum of
the norm ratio over nonzero vectors. -/
theorem dualNorm_eq_iSup (φ : E →L[ℝ] ℝ) :
    dualNorm φ = (⨆ x : {x : E // ‖x‖ ≤ 1}, |φ x|) ∧
      dualNorm φ = ⨆ x : {x : E // x ≠ 0}, |φ x| / ‖(x : E)‖ := by
  constructor
  · let a (x : {x : E // ‖x‖ ≤ 1}) := |φ x|
    have ha : ∀ x, a x ≤ ‖φ‖ := fun x => by
      change |φ x| ≤ ‖φ‖
      rw [← Real.norm_eq_abs]
      exact (φ.le_opNorm x).trans (mul_le_of_le_one_right (norm_nonneg φ) x.property)
    refine le_antisymm (ContinuousLinearMap.opNorm_le_of_unit_norm
      (Real.iSup_nonneg fun x => abs_nonneg (φ x)) fun x hx => ?_) (Real.iSup_le ha (norm_nonneg _))
    rw [Real.norm_eq_abs]
    exact le_ciSup ⟨‖φ‖, Set.forall_mem_range.2 ha⟩ ⟨x, hx.le⟩
  · let a (x : {x : E // x ≠ 0}) := |φ x| / ‖(x : E)‖
    have ha : ∀ x, a x ≤ ‖φ‖ := fun x =>
      (div_le_iff₀ (norm_pos_iff.2 x.property)).2 (by
        simpa [Real.norm_eq_abs] using φ.le_opNorm x)
    refine le_antisymm (φ.opNorm_le_bound' (Real.iSup_nonneg fun x =>
      div_nonneg (abs_nonneg _) (norm_nonneg _)) fun x hx => ?_)
      (Real.iSup_le ha (norm_nonneg _))
    rw [Real.norm_eq_abs]
    have hx' := norm_ne_zero_iff.1 hx
    exact (div_le_iff₀ (norm_pos_iff.2 hx')).1
      (le_ciSup ⟨‖φ‖, Set.forall_mem_range.2 ha⟩ ⟨x, hx'⟩)

end Dual

variable {m n k : ℕ}

/-- **(2.3.2)** The energy norm induced by the symmetric positive-definite matrix `H`. -/
noncomputable abbrev hNorm (H : Matrix (Fin n) (Fin n) ℝ) (_ : H.PosDef)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  energyNorm H.toEuclideanLin x

/-- **(2.3.2)** The energy norm is the square root of the quadratic form. -/
theorem hNorm_eq_sqrt (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef)
    (x : EuclideanSpace ℝ (Fin n)) :
    hNorm H hH x = √(WithLp.ofLp x ⬝ᵥ (H *ᵥ WithLp.ofLp x)) := by
  simp [hNorm, energyNorm, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.toEuclideanLin_apply]

/-- **(2.3.3)** The dimensional comparison of the induced row-sum, spectral, and
column-sum norms. -/
theorem matrix_norms_2_3_3 (A : Matrix (Fin m) (Fin n) ℝ) :
    lpOpNorm ⊤ A ≤ √(n : ℝ) * lpOpNorm 2 A ∧
    √(n : ℝ) * lpOpNorm 2 A ≤ n * lpOpNorm 1 A ∧
    (n : ℝ) * lpOpNorm 1 A ≤ n * √(m : ℝ) * lpOpNorm 2 A ∧
    (n : ℝ) * √(m : ℝ) * lpOpNorm 2 A ≤ n * m * lpOpNorm ⊤ A := by
  obtain ⟨hi₂, h₂i⟩ := A.l2_opNorm_le_sqrt_card_mul_linfty_opNorm
  obtain ⟨h₁₂, h₂₁⟩ := A.l2_opNorm_le_sqrt_card_mul_lpOpNorm_one
  simp only [Fintype.card_fin] at hi₂ h₂i h₁₂ h₂₁
  refine ⟨h₂i, ?_, ?_, ?_⟩
  · simpa only [← mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg n)] using
      mul_le_mul_of_nonneg_left h₂₁ (Real.sqrt_nonneg n)
  · simpa only [← mul_assoc] using mul_le_mul_of_nonneg_left h₁₂ (Nat.cast_nonneg n)
  · simpa only [← mul_assoc, mul_assoc (n : ℝ) (√(m : ℝ)) (√(m : ℝ)),
      Real.mul_self_sqrt (Nat.cast_nonneg m)] using
      mul_le_mul_of_nonneg_left hi₂ (by positivity : 0 ≤ (n : ℝ) * √(m : ℝ))

/-- **(2.3.4)** The spectral norm bounds the Frobenius norm up to the square root
of the number of columns. -/
theorem frobenius_bounds_2_3_4 (A : Matrix (Fin m) (Fin n) ℝ) :
    lpOpNorm 2 A ≤ ‖A‖ ∧ ‖A‖ ≤ √(n : ℝ) * lpOpNorm 2 A :=
  ⟨A.l2_opNorm_le_frobenius_norm,
    A.frobenius_norm_le_sqrt_rank_mul_l2_opNorm.trans
      (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by exact_mod_cast A.rank_le_width))
        (lpOpNorm_nonneg _ _))⟩

/-- **(2.3.5)** A matrix norm is consistent if it is submultiplicative for
every conformable pair of matrices. -/
def IsConsistentMatrixNorm (N : ∀ {m n : ℕ}, Matrix (Fin m) (Fin n) ℝ → ℝ) : Prop :=
  ∀ {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin k) ℝ),
    N (A * B) ≤ N A * N B

/-- Induced `p`-norms are consistent in the sense of (2.3.5). -/
theorem isConsistentMatrixNorm_lp (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    IsConsistentMatrixNorm (fun A => lpOpNorm p A) :=
  fun A B => lpOpNorm_mul_le p A B

/-- The Frobenius norm is consistent in the sense of (2.3.5). -/
theorem isConsistentMatrixNorm_frobenius :
    IsConsistentMatrixNorm (fun A => ‖A‖) := by
  intro m n k A B
  exact (frobenius_norm_mul_le_lpOpNorm_two_mul A B).trans
    (mul_le_mul_of_nonneg_right A.l2_opNorm_le_frobenius_norm (norm_nonneg B))

/-- **(2.3.6)** For a real symmetric matrix, the row-sum and column-sum
norms coincide and bound the spectral norm. -/
theorem symmetric_norms_2_3_6 {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm) :
    lpOpNorm 2 H ≤ lpOpNorm 1 H ∧ lpOpNorm 1 H = lpOpNorm ⊤ H := by
  have h : H.IsHermitian := by simpa [Matrix.IsHermitian, Matrix.IsSymm] using hH
  have he : lpOpNorm 1 H = lpOpNorm ⊤ H :=
    h.lpOpNorm_one_eq_linfty_opNorm.trans (lpOpNorm_top H).symm
  exact ⟨h.l2_opNorm_le_linfty_opNorm.trans_eq he.symm, he⟩

end ConnGouldToint.Chapter02
