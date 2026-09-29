import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.Analysis.Normed.Ring.Inverse
import Numlib.LinearAlgebra.Matrix.SVD
import NumlibSurface.GolubVanLoan.Chapter02.Section02

/-!
# Golub–Van Loan §2.3: matrix norms

Surface file for [golub2013matrix] §2.3: the definition of a matrix norm, the Frobenius norm
(2.3.1) and the `p`-norms (2.3.2), consistency (2.3.3)–(2.3.4) with the book's counterexample,
subordinate norms (2.3.5)–(2.3.6), the norm comparisons (2.3.7)–(2.3.13), convergence of matrix
sequences (§2.3.2), the 2-norm through `AᵀA` (Theorem 2.3.1, Corollary 2.3.2), the Neumann series
and the perturbation of the inverse (Lemma 2.3.3, Theorem 2.3.4), and orthogonal invariance
(2.3.14)–(2.3.15).

## Conventions

A matrix norm (`IsMatrixNorm`) is the vector-norm predicate `IsVectorNorm` of §2.2 on
`ℝ^{m×n}`, exactly as the book defines it. The matrix `p`-norm `‖A‖_p` is the backbone's
`Matrix.lpOpNorm p A` for `p : ℝ≥0∞` with `[Fact (1 ≤ p)]` (the book's `1 ≤ p ≤ ∞`), rectangular;
the subordinate norm `‖A‖_{α,β}` of (2.3.5) is `Matrix.inducedNorm β α A` for definite seminorms
`α`, `β` (vector norms, by `IsVectorNorm.exists_seminorm`). The Frobenius norm is Mathlib's scoped
`Matrix.Norms.Frobenius` norm and `‖·‖_Δ` the scoped elementwise norm, each opened for the
declarations that use it. The book's 1-based block `A(i₁:i₂, j₁:j₂)` is the 0-based
`A.submatrix` on consecutive indices.

## Sources

Backbone `Numlib/Analysis/Matrix/OperatorNorm` (the comparison constants, the Neumann series),
`Numlib/Analysis/Normed/Ring/Inverse` (Theorem 2.3.4 in a normed ring) and
`Numlib/LinearAlgebra/Matrix/SVD` (the singular values behind the 2-norm). The proofs the book
leaves as exercises (P2.3.1–P2.3.6) are the backbone lemmas cited. Theorem 2.3.1 is proved through
the right singular vector of the largest singular value rather than the book's gradient
computation.

## Readings and errata

The book's proof of Theorem 2.3.4 writes `A + E = (I + F) A` with `F = -E A⁻¹` and claims
`‖F‖_p = r = ‖A⁻¹ E‖_p`, which is false in general; the statement is true through
`A + E = A (I + A⁻¹ E)`, the backbone's route.
-/

open Filter Finset Matrix Topology WithLp
open scoped ENNReal NNReal

namespace GolubVanLoan.Chapter02

variable {m n : ℕ}

/-! ### §2.3.1 Definitions -/

/-- **§2.3.1, matrix norm.** `f : ℝ^{m×n} → ℝ` is a *matrix norm* if it satisfies the three
vector-norm properties on `ℝ^{m×n}`: `f(A) ≥ 0` with `f(A) = 0` iff `A = 0`,
`f(A + B) ≤ f(A) + f(B)`, `f(αA) = |α| f(A)`. -/
def IsMatrixNorm (f : Matrix (Fin m) (Fin n) ℝ → ℝ) : Prop :=
  IsVectorNorm f

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **(2.3.1), the Frobenius norm** `‖A‖_F = √(∑ᵢ ∑ⱼ |aᵢⱼ|²)`, a matrix norm. -/
theorem equation_2_3_1 (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖A‖ = √(∑ i, ∑ j, |A i j| ^ 2) ∧ IsMatrixNorm (fun B : Matrix (Fin m) (Fin n) ℝ => ‖B‖) := by
  refine ⟨?_, isVectorNorm_norm⟩
  simp_rw [← Real.norm_eq_abs]
  rw [← frobenius_norm_sq_eq_sum_sq, Real.sqrt_sq (norm_nonneg _)]

end Frobenius

/-- The matrix `p`-norm is a matrix norm: it is the induced seminorm of the vector `p`-norm, which
is definite. -/
private theorem isMatrixNorm_lpOpNorm (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    IsMatrixNorm (lpOpNorm p : Matrix (Fin m) (Fin n) ℝ → ℝ) :=
  IsVectorNorm.exists_seminorm.2
    ⟨inducedSeminorm (lpSeminorm p) (lpSeminorm p) (lpSeminorm_definite p),
      funext fun A => by simp [lpOpNorm_eq_inducedNorm],
      fun A hA => (inducedNorm_eq_zero_iff (lpSeminorm_definite p) (lpSeminorm_definite p) A).1
        hA⟩

/-- **(2.3.2), the `p`-norms** `‖A‖_p = sup_{x ≠ 0} ‖Ax‖_p / ‖x‖_p`, and for `n ≥ 1` the display
after it: the supremum is a maximum over the unit `p`-sphere, `‖A‖_p = ‖A x‖_p` for some `x` with
`‖x‖_p = 1`; `‖·‖_p` is a matrix norm. -/
theorem equation_2_3_2 (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : Matrix (Fin m) (Fin n) ℝ) :
    lpOpNorm p A = ⨆ x : {x : Fin n → ℝ // x ≠ 0},
        ‖WithLp.toLp p (A *ᵥ (x : Fin n → ℝ))‖ / ‖WithLp.toLp p (x : Fin n → ℝ)‖ ∧
      (0 < n → ∃ x : Fin n → ℝ, ‖WithLp.toLp p x‖ = 1 ∧
        lpOpNorm p A = ‖WithLp.toLp p (A *ᵥ x)‖) ∧
      IsMatrixNorm (lpOpNorm p : Matrix (Fin m) (Fin n) ℝ → ℝ) := by
  refine ⟨?_, fun hn => ?_, isMatrixNorm_lpOpNorm p⟩
  · rw [lpOpNorm_eq_inducedNorm, inducedNorm_eq_iSup_div (lpSeminorm_definite p)]
    rfl
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    rw [lpOpNorm_eq_inducedNorm]
    exact exists_inducedNorm_eq (lpSeminorm_definite p) A

/-- **(2.3.3)**: `‖AB‖_p ≤ ‖A‖_p ‖B‖_p` for `A ∈ ℝ^{m×n}`, `B ∈ ℝ^{n×q}` — an inequality between
three different norms. -/
theorem equation_2_3_3 {q : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin q) ℝ) : lpOpNorm p (A * B) ≤ lpOpNorm p A * lpOpNorm p B :=
  lpOpNorm_mul_le p A B

section Elementwise

open scoped Matrix.Norms.Elementwise

/-- **§2.3.1, after (2.3.4): not every matrix norm is consistent.** `‖A‖_Δ = max |aᵢⱼ|` is a
matrix norm, but for `A = B = [1 1; 1 1]`, `‖AB‖_Δ = 2 > 1 = ‖A‖_Δ ‖B‖_Δ`. -/
theorem maxAbs_not_consistent :
    IsMatrixNorm (fun A : Matrix (Fin 2) (Fin 2) ℝ => ‖A‖) ∧
      ‖(!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) * !![1, 1; 1, 1]‖ = 2 ∧
      ‖(!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)‖ = 1 ∧
      ‖(!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)‖ * ‖(!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)‖
        < ‖(!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) * !![1, 1; 1, 1]‖ := by
  have hA : ‖(!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)‖ = 1 := by
    refine le_antisymm ((norm_le_iff zero_le_one).2 fun i j => ?_) ?_
    · fin_cases i <;> fin_cases j <;> simp
    · simpa using norm_entry_le_entrywise_sup_norm (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)
        (i := 0) (j := 0)
  have hmul : (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) * !![1, 1; 1, 1] = !![2, 2; 2, 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  have hAA : ‖(!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) * !![1, 1; 1, 1]‖ = 2 := by
    rw [hmul]
    refine le_antisymm ((norm_le_iff zero_le_two).2 fun i j => ?_) ?_
    · fin_cases i <;> fin_cases j <;> simp
    · simpa using norm_entry_le_entrywise_sup_norm (!![2, 2; 2, 2] : Matrix (Fin 2) (Fin 2) ℝ)
        (i := 0) (j := 0)
  refine ⟨isVectorNorm_norm, hAA, hA, ?_⟩
  rw [hAA, hA]
  norm_num

end Elementwise

/-- **§2.3.1**: the `p`-norms are consistent with the vector `p`-norms,
`‖Ax‖_p ≤ ‖A‖_p ‖x‖_p`. -/
theorem norm_mulVec_le (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) : ‖WithLp.toLp p (A *ᵥ x)‖ ≤ lpOpNorm p A * ‖WithLp.toLp p x‖ :=
  lpSeminorm_mulVec_le p A x

/-- **(2.3.5), subordinate norms.** For vector norms `‖·‖_α` on `ℝⁿ` and `‖·‖_β` on `ℝᵐ`, the
matrix norm `‖A‖_{α,β} = sup_{x ≠ 0} ‖Ax‖_β / ‖x‖_α` (the backbone's `Matrix.inducedNorm β α A`)
satisfies `‖Ax‖_β ≤ ‖A‖_{α,β} ‖x‖_α`. -/
theorem equation_2_3_5 (α : Seminorm ℝ (Fin n → ℝ)) (β : Seminorm ℝ (Fin m → ℝ))
    (hα : ∀ x, α x = 0 → x = 0) (A : Matrix (Fin m) (Fin n) ℝ) :
    inducedNorm β α A = ⨆ x : {x : Fin n → ℝ // x ≠ 0}, β (A *ᵥ (x : Fin n → ℝ)) / α x ∧
      ∀ x, β (A *ᵥ x) ≤ inducedNorm β α A * α x :=
  ⟨inducedNorm_eq_iSup_div hα A, le_inducedNorm_mul hα A⟩

/-- **(2.3.6)**: the supremum (2.3.5) is attained, `‖A‖_{α,β} = ‖A x_*‖_β` for some `x_*` of unit
`α`-norm (`n ≥ 1`). -/
theorem equation_2_3_6 (α : Seminorm ℝ (Fin n → ℝ)) (β : Seminorm ℝ (Fin m → ℝ))
    (hα : ∀ x, α x = 0 → x = 0) (A : Matrix (Fin m) (Fin n) ℝ) (hn : 0 < n) :
    ∃ x : Fin n → ℝ, α x = 1 ∧ inducedNorm β α A = β (A *ᵥ x) :=
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exists_inducedNorm_eq hα A

/-! ### §2.3.2 Some matrix norm properties -/

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **(2.3.7)**: `‖A‖₂ ≤ ‖A‖_F ≤ √(min{m, n}) ‖A‖₂`. -/
theorem equation_2_3_7 (A : Matrix (Fin m) (Fin n) ℝ) :
    lpOpNorm 2 A ≤ ‖A‖ ∧ ‖A‖ ≤ √((min m n : ℕ) : ℝ) * lpOpNorm 2 A := by
  refine ⟨l2_opNorm_le_frobenius_norm A, (frobenius_norm_le_sqrt_rank_mul_l2_opNorm A).trans ?_⟩
  refine mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) (lpOpNorm_nonneg _ _)
  exact_mod_cast le_min A.rank_le_height A.rank_le_width

end Frobenius

/-- **(2.3.8)**: `max_{i,j} |aᵢⱼ| ≤ ‖A‖₂ ≤ √(mn) max_{i,j} |aᵢⱼ|`. -/
theorem equation_2_3_8 (A : Matrix (Fin m) (Fin n) ℝ) :
    (⨆ i, ⨆ j, |A i j|) ≤ lpOpNorm 2 A ∧
      lpOpNorm 2 A ≤ √((m : ℝ) * n) * ⨆ i, ⨆ j, |A i j| := by
  have hM : 0 ≤ ⨆ i, ⨆ j, |A i j| :=
    Real.iSup_nonneg fun i => Real.iSup_nonneg fun j => abs_nonneg _
  refine ⟨Real.iSup_le (fun i => Real.iSup_le (fun j => ?_) (lpOpNorm_nonneg _ _))
    (lpOpNorm_nonneg _ _), ?_⟩
  · rw [lpOpNorm_two, ← Real.norm_eq_abs]
    exact norm_entry_le_l2_opNorm A i j
  · have h := l2_opNorm_le_sqrt_card_mul_of_forall_norm_le A hM fun i j => by
      rw [Real.norm_eq_abs]
      exact (le_ciSup (Set.finite_range fun j => |A i j|).bddAbove j).trans
        (le_ciSup (Set.finite_range fun i => ⨆ j, |A i j|).bddAbove i)
    simpa using h

/-- A finite supremum in `ℝ≥0`, read in `ℝ`. -/
private theorem coe_univ_sup_eq_iSup {ι : Type*} [Fintype ι] (f : ι → ℝ≥0) :
    ((Finset.univ.sup f : ℝ≥0) : ℝ) = ⨆ i, (f i : ℝ) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [Finset.univ_eq_empty]
  refine le_antisymm ?_ (ciSup_le fun i => NNReal.coe_le_coe.2 (Finset.le_sup (mem_univ i)))
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset ι) Finset.univ_nonempty f
  rw [hi]
  exact le_ciSup (Set.finite_range fun i => (f i : ℝ)).bddAbove i

/-- **(2.3.9)**: `‖A‖₁ = max_j ∑ᵢ |aᵢⱼ|`, the largest column sum. -/
theorem equation_2_3_9 (A : Matrix (Fin m) (Fin n) ℝ) :
    lpOpNorm 1 A = ⨆ j, ∑ i, |A i j| := by
  rw [lpOpNorm_one_eq_sup_sum_norm, coe_univ_sup_eq_iSup]
  simp [Real.norm_eq_abs]

section Operator

open scoped Matrix.Norms.Operator

/-- **(2.3.10)**: `‖A‖_∞ = max_i ∑ⱼ |aᵢⱼ|`, the largest row sum. -/
theorem equation_2_3_10 (A : Matrix (Fin m) (Fin n) ℝ) :
    lpOpNorm ∞ A = ⨆ i, ∑ j, |A i j| := by
  rw [lpOpNorm_top, linfty_opNorm_def, coe_univ_sup_eq_iSup]
  simp [Real.norm_eq_abs]

end Operator

/-- From `a ≤ √c b` to `(1/√c) a ≤ b`, including the degenerate `c = 0`. -/
private theorem one_div_sqrt_mul_le {a b c : ℝ} (hb : 0 ≤ b) (h : a ≤ √c * b) :
    1 / √c * a ≤ b := by
  rcases (Real.sqrt_nonneg c).eq_or_lt with hc | hc
  · rw [← hc, div_zero, zero_mul]
    exact hb
  · rw [one_div, inv_mul_le_iff₀ hc]
    exact h

/-- **(2.3.11)**: `(1/√n) ‖A‖_∞ ≤ ‖A‖₂ ≤ √m ‖A‖_∞`. -/
theorem equation_2_3_11 (A : Matrix (Fin m) (Fin n) ℝ) :
    1 / √(n : ℝ) * lpOpNorm ∞ A ≤ lpOpNorm 2 A ∧ lpOpNorm 2 A ≤ √(m : ℝ) * lpOpNorm ∞ A := by
  obtain ⟨h1, h2⟩ := l2_opNorm_le_sqrt_card_mul_linfty_opNorm A
  simp only [Fintype.card_fin] at h1 h2
  exact ⟨one_div_sqrt_mul_le (lpOpNorm_nonneg _ _) h2, h1⟩

/-- **(2.3.12)**: `(1/√m) ‖A‖₁ ≤ ‖A‖₂ ≤ √n ‖A‖₁`. -/
theorem equation_2_3_12 (A : Matrix (Fin m) (Fin n) ℝ) :
    1 / √(m : ℝ) * lpOpNorm 1 A ≤ lpOpNorm 2 A ∧ lpOpNorm 2 A ≤ √(n : ℝ) * lpOpNorm 1 A := by
  obtain ⟨h1, h2⟩ := l2_opNorm_le_sqrt_card_mul_lpOpNorm_one A
  simp only [Fintype.card_fin] at h1 h2
  exact ⟨one_div_sqrt_mul_le (lpOpNorm_nonneg _ _) h1, h2⟩

/-- **(2.3.13)**: a block `A(i₁:i₂, j₁:j₂)` has `‖A(i₁:i₂, j₁:j₂)‖_p ≤ ‖A‖_p`. The book's 1-based
`1 ≤ i₁ ≤ i₂ ≤ m` is the 0-based `i₁ ≤ i₂ < m` here, the block's rows being `i₁, …, i₂`. -/
theorem equation_2_3_13 (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : Matrix (Fin m) (Fin n) ℝ)
    {i₁ i₂ j₁ j₂ : ℕ} (hi : i₁ ≤ i₂) (hi₂ : i₂ < m) (hj : j₁ ≤ j₂) (hj₂ : j₂ < n) :
    lpOpNorm p (A.submatrix (fun k : Fin (i₂ - i₁ + 1) => (⟨i₁ + k, by omega⟩ : Fin m))
        (fun k : Fin (j₂ - j₁ + 1) => (⟨j₁ + k, by omega⟩ : Fin n))) ≤ lpOpNorm p A :=
  lpOpNorm_submatrix_le p A (fun a b h => Fin.ext (by simpa using congrArg Fin.val h))
    (fun a b h => Fin.ext (by simpa using congrArg Fin.val h))

/-- **§2.3.2, convergence**: a sequence of matrices converges iff `‖A⁽ᵏ⁾ - A‖ → 0` in any matrix
norm; "the choice of norm is immaterial". -/
theorem tendsto_iff_of_isMatrixNorm {f : Matrix (Fin m) (Fin n) ℝ → ℝ} (hf : IsMatrixNorm f)
    (A : ℕ → Matrix (Fin m) (Fin n) ℝ) (A₀ : Matrix (Fin m) (Fin n) ℝ) :
    Tendsto (fun k => f (A k - A₀)) atTop (𝓝 0) ↔ Tendsto A atTop (𝓝 A₀) := by
  let _ : NormedAddCommGroup (Matrix (Fin m) (Fin n) ℝ) := Matrix.normedAddCommGroup
  let _ : NormedSpace ℝ (Matrix (Fin m) (Fin n) ℝ) := Matrix.normedSpace
  exact tendsto_iff_of_isVectorNorm hf A A₀

/-! ### §2.3.3 The matrix 2-norm -/

/-- The 2-norm of a rectangular matrix is its largest singular value, attained at an index. -/
private theorem exists_colSingularValues_eq_lpOpNorm_two (A : Matrix (Fin m) (Fin n) ℝ)
    (hn : 0 < n) :
    ∃ i, A.colSingularValues i = lpOpNorm 2 A ∧ ∀ j, A.colSingularValues j ≤ lpOpNorm 2 A := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max A.colSingularValues
  have hle : lpOpNorm 2 A ≤ A.colSingularValues i₀ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (A.colSingularValues_nonneg i₀) fun x => ?_
    calc ‖lpCLM 2 A x‖ = ‖toEuclideanLin A x‖ := rfl
      _ ≤ (⨆ i, A.colSingularValues i) * ‖x‖ := A.norm_toEuclideanLin_le_iSup_colSingularValues x
      _ ≤ A.colSingularValues i₀ * ‖x‖ :=
          mul_le_mul_of_nonneg_right (ciSup_le hi₀) (norm_nonneg _)
  have hge : A.colSingularValues i₀ ≤ lpOpNorm 2 A := by
    have h := (lpCLM 2 A).le_opNorm (A.rightSingularBasis i₀)
    rw [(A.rightSingularBasis).norm_eq_one, mul_one] at h
    calc A.colSingularValues i₀ = ‖toEuclideanLin A (A.rightSingularBasis i₀)‖ :=
          (A.norm_toEuclideanLin_rightSingularBasis i₀).symm
      _ ≤ lpOpNorm 2 A := h
  exact ⟨i₀, le_antisymm hge hle, fun j => (hi₀ j).trans hge⟩

/-- **Theorem 2.3.1.** For `A ∈ ℝ^{m×n}` (`n ≥ 1`) there is a unit 2-norm `n`-vector `z` with
`AᵀA z = μ² z`, `μ = ‖A‖₂`. -/
theorem theorem_2_3_1 (A : Matrix (Fin m) (Fin n) ℝ) (hn : 0 < n) :
    ∃ z : Fin n → ℝ, ‖WithLp.toLp 2 z‖ = 1 ∧ (Aᵀ * A) *ᵥ z = lpOpNorm 2 A ^ 2 • z := by
  obtain ⟨i, hi, -⟩ := exists_colSingularValues_eq_lpOpNorm_two A hn
  refine ⟨WithLp.ofLp (A.rightSingularBasis i), by
    rw [WithLp.toLp_ofLp, (A.rightSingularBasis).norm_eq_one], ?_⟩
  have h := congrArg WithLp.ofLp (A.toEuclideanLin_conjTranspose_mul_self_rightSingularBasis i)
  simpa [toEuclideanLin_apply, conjTranspose_eq_transpose_of_trivial, hi] using h

/-- The eigenvalues of a Hermitian matrix depend on the matrix only. -/
private theorem eigenvalues₀_congr {M N : Matrix (Fin n) (Fin n) ℝ} (h : M = N)
    (hM : M.IsHermitian) (hN : N.IsHermitian) : hM.eigenvalues₀ = hN.eigenvalues₀ := by
  subst h
  rfl

/-- **§2.3.3, after Theorem 2.3.1**: `‖A‖₂ = √λ_max(AᵀA)` (for `n ≥ 1`), and `‖A‖₂²` is a zero of
`p(λ) = det(AᵀA - λI)`. -/
theorem l2_opNorm_eq_sqrt_eigenvalues₀_zero (A : Matrix (Fin m) (Fin n) ℝ)
    (hAtA : (Aᵀ * A).IsHermitian) (hn : 0 < n) :
    lpOpNorm 2 A = √(hAtA.eigenvalues₀ ⟨0, by simpa using hn⟩) ∧
      (Aᵀ * A - lpOpNorm 2 A ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)).det = 0 := by
  set k₀ : Fin (Fintype.card (Fin n)) := ⟨0, by simpa using hn⟩
  have hG := isHermitian_conjTranspose_mul_self A
  have hcongr : hAtA.eigenvalues₀ = hG.eigenvalues₀ :=
    eigenvalues₀_congr (by rw [conjTranspose_eq_transpose_of_trivial]) hAtA hG
  obtain ⟨i₀, hi₀, hmax⟩ := exists_colSingularValues_eq_lpOpNorm_two A hn
  set e : Fin (Fintype.card (Fin n)) ≃ Fin n := Fintype.equivOfCardEq (Fintype.card_fin _)
  have heig : ∀ j, hG.eigenvalues j = hG.eigenvalues₀ (e.symm j) := fun j => rfl
  have hsq : lpOpNorm 2 A ^ 2 = hAtA.eigenvalues₀ k₀ := by
    rw [hcongr]
    refine le_antisymm ?_ ?_
    · rw [← hi₀, sq_colSingularValues, heig]
      exact hG.eigenvalues₀_antitone (Fin.le_def.2 (Nat.zero_le _))
    · have h := sq_colSingularValues A (e k₀)
      rw [heig, Equiv.symm_apply_apply] at h
      rw [← h]
      exact pow_le_pow_left₀ (A.colSingularValues_nonneg _) (hmax _) 2
  refine ⟨by rw [← hsq, Real.sqrt_sq (lpOpNorm_nonneg _ _)], ?_⟩
  obtain ⟨z, hz1, hz⟩ := theorem_2_3_1 A hn
  refine exists_mulVec_eq_zero_iff.1 ⟨z, fun h0 => by simp [h0] at hz1, ?_⟩
  rw [sub_mulVec, hz, smul_mulVec, one_mulVec, sub_self]

/-- **Corollary 2.3.2**: `‖A‖₂ ≤ √(‖A‖₁ ‖A‖_∞)`. -/
theorem corollary_2_3_2 (A : Matrix (Fin m) (Fin n) ℝ) :
    lpOpNorm 2 A ≤ √(lpOpNorm 1 A * lpOpNorm ∞ A) :=
  (le_abs_self _).trans (Real.abs_le_sqrt (l2_opNorm_sq_le_lpOpNorm_one_mul_linfty_opNorm A))

/-! ### §2.3.4 Perturbations and the inverse -/

/-- **Lemma 2.3.3.** For `1 ≤ p ≤ ∞` and `F ∈ ℝ^{n×n}` with `‖F‖_p < 1`, `I - F` is nonsingular,
`(I - F)⁻¹ = ∑_{k ≥ 0} Fᵏ`, and `‖(I - F)⁻¹‖_p ≤ 1 / (1 - ‖F‖_p)`. -/
theorem lemma_2_3_3 (p : ℝ≥0∞) [Fact (1 ≤ p)] {F : Matrix (Fin n) (Fin n) ℝ}
    (hF : lpOpNorm p F < 1) :
    IsUnit (1 - F) ∧ HasSum (fun k => F ^ k) (1 - F)⁻¹ ∧
      lpOpNorm p (1 - F)⁻¹ ≤ 1 / (1 - lpOpNorm p F) := by
  have hp := lpSeminorm_definite (𝕜 := ℝ) (n := Fin n) p
  simp only [lpOpNorm_eq_inducedNorm] at hF ⊢
  refine ⟨isUnit_one_sub_of_inducedNorm_lt_one hp hF, hasSum_pow_of_inducedNorm_lt_one hp hF, ?_⟩
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · rw [Subsingleton.elim (1 - F)⁻¹ 0, show inducedNorm (lpSeminorm p) (lpSeminorm p)
      (0 : Matrix (Fin n) (Fin n) ℝ) = 0 from (inducedNorm_eq_zero_iff hp hp 0).2 rfl]
    exact div_nonneg zero_le_one (by linarith)
  · exact inducedNorm_inv_one_sub_le hp hF

/-- **§2.3.4, after Lemma 2.3.3**: `‖(I - F)⁻¹ - I‖_p ≤ ‖F‖_p / (1 - ‖F‖_p)`, so `O(ε)`
perturbations of the identity induce `O(ε)` perturbations of the inverse. -/
theorem norm_inv_one_sub_sub_one_le (p : ℝ≥0∞) [Fact (1 ≤ p)] {F : Matrix (Fin n) (Fin n) ℝ}
    (hF : lpOpNorm p F < 1) :
    lpOpNorm p ((1 - F)⁻¹ - 1) ≤ lpOpNorm p F / (1 - lpOpNorm p F) := by
  simp only [lpOpNorm_eq_inducedNorm] at hF ⊢
  exact inducedNorm_inv_one_sub_sub_one_le (lpSeminorm_definite p) hF

/-- The operator of a difference of matrices. -/
private theorem lpCLM_sub (p : ℝ≥0∞) [Fact (1 ≤ p)] (X Y : Matrix (Fin n) (Fin n) ℝ) :
    lpCLM p (X - Y) = lpCLM p X - lpCLM p Y := by
  rw [sub_eq_add_neg, lpCLM_add, sub_eq_add_neg, ← neg_one_smul ℝ Y, lpCLM_smul, neg_one_smul]

/-- **Theorem 2.3.4.** If `A` is nonsingular and `r = ‖A⁻¹E‖_p < 1`, then `A + E` is nonsingular and
`‖(A + E)⁻¹ - A⁻¹‖_p ≤ ‖E‖_p ‖A⁻¹‖_p² / (1 - r)`. -/
theorem theorem_2_3_4 (p : ℝ≥0∞) [Fact (1 ≤ p)] {A E : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A)
    (hr : lpOpNorm p (A⁻¹ * E) < 1) :
    IsUnit (A + E) ∧
      lpOpNorm p ((A + E)⁻¹ - A⁻¹) ≤
        lpOpNorm p E * lpOpNorm p A⁻¹ ^ 2 / (1 - lpOpNorm p (A⁻¹ * E)) := by
  have ha : IsUnit (lpCLM p A) := (isUnit_lpCLM_iff p A).2 hA
  have hinv : Ring.inverse (lpCLM p A) = lpCLM p A⁻¹ := ringInverse_lpCLM p A
  have hr' : ‖Ring.inverse (lpCLM p A) * lpCLM p E‖ < 1 := by
    rw [hinv, ← lpCLM_mul]
    exact hr
  refine ⟨?_, ?_⟩
  · have h := NormedRing.isUnit_add_of_norm_inverse_mul_lt_one ha hr'
    rwa [← lpCLM_add, isUnit_lpCLM_iff] at h
  · have h := (NormedRing.norm_inverse_add_sub_le_of_norm_inverse_mul_lt_one ha hr').2
    rw [← lpCLM_add, ringInverse_lpCLM, hinv, ← lpCLM_mul, ← lpCLM_sub] at h
    exact h

/-! ### §2.3.5 Orthogonal invariance -/

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **(2.3.14)**: `‖QAZ‖_F = ‖A‖_F` for orthogonal `Q`, `Z`. -/
theorem equation_2_3_14 {Q : Matrix (Fin m) (Fin m) ℝ} {Z : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin m) ℝ) (hZ : Z ∈ orthogonalGroup (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) : ‖Q * A * Z‖ = ‖A‖ :=
  frobenius_norm_unitary_mul_mul_unitary hQ A hZ

end Frobenius

/-- **(2.3.15)**: `‖QAZ‖₂ = ‖A‖₂` for orthogonal `Q`, `Z`. -/
theorem equation_2_3_15 {Q : Matrix (Fin m) (Fin m) ℝ} {Z : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin m) ℝ) (hZ : Z ∈ orthogonalGroup (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) : lpOpNorm 2 (Q * A * Z) = lpOpNorm 2 A := by
  rw [lpOpNorm_two, lpOpNorm_two]
  exact l2_opNorm_unitary_mul_mul_unitary hQ A hZ

end GolubVanLoan.Chapter02
