import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.Conditioning.LinearSystem

/-!
# Componentwise perturbation theory for linear systems

The componentwise perturbation theory of `A x = b` for real square matrices:
[quarteroni2000numerical] §3.1.2, (3.14)–(3.16), §3.1.4 and Remark 3.7; [higham2002accuracy]
§7.2, Theorem 7.4; [Ske79]. Everything is in the entrywise order and absolute value of
`Numlib/LinearAlgebra/Matrix/Order`, with the sup norm `‖·‖_∞` of the `Pi` type on vectors and
the maximum absolute row sum, Mathlib's scoped `Matrix.Norms.Operator` instance, on matrices.

* The **Skeel condition numbers** `cond(A, x) = ‖|A⁻¹| |A| |x|‖_∞ / ‖x‖_∞`
  (`Matrix.skeelCondAt`) and `cond(A) = ‖|A⁻¹| |A|‖_∞` (`Matrix.skeelCond`) of Remark 3.7, whose
  printed display is read with the missing absolute values restored; `cond(A) = sup_x cond(A, x)`
  (`Matrix.skeelCond_eq_iSup_skeelCondAt`), and the invariance of `cond(A, x)` under row scaling
  `A ↦ D A` (`Matrix.skeelCondAt_diagonal_mul`), which `κ(A)` lacks.
* **The componentwise perturbation theorem**, [higham2002accuracy] Theorem 7.4
  (`Matrix.norm_sub_le_of_abs_le`): `|ΔA| ≤ γ E`, `|Δb| ≤ γ f`, `γ ‖|A⁻¹| E‖_∞ < 1` give
  `‖δx‖_∞ / ‖x‖_∞ ≤ γ ‖|A⁻¹| (E |x| + f)‖_∞ / ((1 - γ ‖|A⁻¹| E‖_∞) ‖x‖_∞)`; with `E = |A|`,
  `f = |b|` this is (3.15) (`Matrix.norm_sub_le_of_abs_le_abs`), whose second inequality reads
  `‖δx‖_∞ / ‖x‖_∞ ≤ 2 γ cond(A) / (1 - γ cond(A))`.
* **The row-by-row bounds (3.16)** with `r_(i)ᵀ = e_iᵀ A⁻¹` the rows of `A⁻¹`
  (`Matrix.abs_sub_apply_le_of_abs_le_abs`, `Matrix.abs_sub_apply_div_le_of_abs_le_abs`),
  immediate from `δx = -A⁻¹ ΔA (x + δx)` and `δx = A⁻¹ Δb`.
* **The LAPACK a posteriori bound** of §3.1.4 (`Matrix.norm_sub_le_of_computedResidual`):
  `‖e‖_∞ ≤ ‖|A⁻¹| (|r̂| + γ_{n+1} (|A| |y| + |b|))‖_∞` when the computed residual satisfies
  `r̂ = r + δr`, `|δr| ≤ γ_{n+1} (|A| |y| + |b|)`, which is what
  `FloatingPoint.exists_roundsAffineStep_eq_add` of `Numlib/FloatingPoint/Stationary` delivers for
  `r̂ = fl(b - A y)`; the bound is stated for an arbitrary constant `c` in place of `γ_{n+1}`.

This module is separate from `Numlib/Conditioning/LinearSystem` because that one is
operator-level and norm-only; everything here needs entries.
-/

open Finset

open scoped Matrix Matrix.Norms.Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The Skeel condition numbers -/

section Skeel

variable (A : Matrix n n ℝ)

/-- **Skeel's condition number of a system**, [quarteroni2000numerical] Remark 3.7 (read as
`cond(A, x) = ‖|A⁻¹| |A| |x|‖_∞ / ‖x‖_∞`), [higham2002accuracy] (7.11): the amplification of a
componentwise relative perturbation of `A` in the sup norm of the solution `x`. -/
noncomputable def skeelCondAt (x : n → ℝ) : ℝ := ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|)‖ / ‖x‖

/-- **Skeel's condition number of a matrix**, [quarteroni2000numerical] Remark 3.7,
[higham2002accuracy] (7.11): `cond(A) = ‖|A⁻¹| |A|‖_∞`, the supremum of `cond(A, x)` over `x`
(`Matrix.skeelCond_eq_iSup_skeelCondAt`). -/
noncomputable def skeelCond : ℝ := ‖A⁻¹.abs * A.abs‖

variable {A}

/-- `cond(A, x) ≤ cond(A)`. -/
theorem skeelCondAt_le_skeelCond (x : n → ℝ) : skeelCondAt A x ≤ skeelCond A := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [skeelCondAt, skeelCond]
  rw [skeelCondAt, skeelCond, div_le_iff₀ (norm_pos_iff.2 hx), mulVec_mulVec, ← norm_abs_eq x]
  exact linfty_opNorm_mulVec _ _

/-- `cond(A, x)` is nonnegative. -/
theorem skeelCondAt_nonneg (x : n → ℝ) : 0 ≤ skeelCondAt A x :=
  div_nonneg (norm_nonneg _) (norm_nonneg _)

/-- **`cond(A)` is the supremum of the `cond(A, x)`** ([quarteroni2000numerical] Remark 3.7): the
supremum is attained at the vector of ones, where `|A⁻¹| |A| 𝟙` is the vector of row sums. -/
theorem skeelCond_eq_iSup_skeelCondAt [Nonempty n] : skeelCond A = ⨆ x, skeelCondAt A x := by
  have hbdd : BddAbove (Set.range fun x => skeelCondAt A x) :=
    ⟨skeelCond A, by rintro _ ⟨x, rfl⟩; exact skeelCondAt_le_skeelCond x⟩
  refine le_antisymm ?_ (ciSup_le skeelCondAt_le_skeelCond)
  refine le_trans (le_of_eq ?_) (le_ciSup hbdd (1 : n → ℝ))
  have h1 : |(1 : n → ℝ)| = 1 := by ext i; simp
  have h2 : ‖(1 : n → ℝ)‖ = 1 := by
    rw [Pi.one_def, pi_norm_const, norm_one]
  rw [skeelCondAt, h1, mulVec_mulVec, h2, div_one, skeelCond,
    norm_mulVec_one_of_entrywiseNonneg ((entrywiseNonneg_abs _).mul (entrywiseNonneg_abs _))]

/-- The absolute value of a matrix scaled by a diagonal matrix on the left. -/
theorem abs_diagonal_mul (d : n → ℝ) (B : Matrix n n ℝ) :
    (diagonal d * B).abs = diagonal (fun i => |d i|) * B.abs := by
  ext i j
  simp [diagonal_mul, abs_mul]

/-- The absolute value of a matrix scaled by a diagonal matrix on the right. -/
theorem abs_mul_diagonal (B : Matrix n n ℝ) (d : n → ℝ) :
    (B * diagonal d).abs = B.abs * diagonal (fun i => |d i|) := by
  ext i j
  simp [mul_diagonal, abs_mul]

/-- **Row scaling invariance of Skeel's condition number** ([quarteroni2000numerical] Remark
3.7): for a nonsingular diagonal `D = diag d`, `cond(D A, x) = cond(A, x)`, since
`|(D A)⁻¹| |D A| = |A⁻¹| |D⁻¹| |D| |A| = |A⁻¹| |A|`. This is what `κ(A)` lacks, and why `cond(A)`
measures the ill-conditioning of a matrix irrespective of a row scaling. -/
theorem skeelCondAt_diagonal_mul {d : n → ℝ} (hd : ∀ i, d i ≠ 0) (x : n → ℝ) :
    skeelCondAt (diagonal d * A) x = skeelCondAt A x := by
  have hinv : (diagonal d)⁻¹ = diagonal fun i => (d i)⁻¹ :=
    inv_eq_right_inv (by rw [diagonal_mul_diagonal]; simp [mul_inv_cancel₀ (hd _)])
  have hkey : (diagonal d * A)⁻¹.abs * (diagonal d * A).abs = A⁻¹.abs * A.abs := by
    rw [Matrix.mul_inv_rev, hinv, abs_mul_diagonal, abs_diagonal_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal]
    have : (fun i => |(d i)⁻¹| * |d i|) = fun _ => (1 : ℝ) := by
      ext i
      rw [abs_inv, inv_mul_cancel₀ (abs_ne_zero.2 (hd i))]
    rw [this, diagonal_one, Matrix.one_mul]
  rw [skeelCondAt, skeelCondAt, mulVec_mulVec, mulVec_mulVec, hkey]

end Skeel

/-! ### The componentwise perturbation theorem -/

section Perturbation

variable {A ΔA : Matrix n n ℝ} {b Δb x y : n → ℝ}

/-- The error of a perturbed solve, `y - x = A⁻¹ (Δb - ΔA y)`. -/
theorem sub_eq_inv_mulVec_of_mulVec_eq (hA : IsUnit A) (hx : A *ᵥ x = b)
    (hy : (A + ΔA) *ᵥ y = b + Δb) : y - x = A⁻¹ *ᵥ (Δb - ΔA *ᵥ y) := by
  have hAd : IsUnit A.det := (isUnit_iff_isUnit_det A).1 hA
  have h1 : A *ᵥ (y - x) = Δb - ΔA *ᵥ y := by
    rw [add_mulVec] at hy
    rw [mulVec_sub, hx, ← sub_eq_iff_eq_add'.2 hy]
    abel
  rw [← h1, mulVec_mulVec, nonsing_inv_mul A hAd, one_mulVec]

/-- **The componentwise perturbation theorem** ([higham2002accuracy] Theorem 7.4, after
[Ske79]): if `A x = b` and `(A + ΔA) y = b + Δb` with `|ΔA| ≤ γ E`, `|Δb| ≤ γ f` for entrywise
nonnegative `E`, `f`, and `γ ‖|A⁻¹| E‖_∞ < 1`, then
`‖y - x‖_∞ / ‖x‖_∞ ≤ γ ‖|A⁻¹| (E |x| + f)‖_∞ / ((1 - γ ‖|A⁻¹| E‖_∞) ‖x‖_∞)`.
From `y - x = A⁻¹ (Δb - ΔA y)`: `|y - x| ≤ γ |A⁻¹| (f + E |x|) + γ |A⁻¹| E |y - x|`, and the sup
norm is taken. -/
theorem norm_sub_le_of_abs_le (hA : IsUnit A) (hx : A *ᵥ x = b) (hy : (A + ΔA) *ᵥ y = b + Δb)
    {E : Matrix n n ℝ} {f : n → ℝ} {γ : ℝ} (hγ : 0 ≤ γ) (hE : E.EntrywiseNonneg)
    (hΔA : ΔA.abs ≤ₑ γ • E) (hΔb : |Δb| ≤ γ • f) (hsmall : γ * ‖A⁻¹.abs * E‖ < 1) (hx0 : x ≠ 0) :
    ‖y - x‖ / ‖x‖ ≤
      γ * ‖A⁻¹.abs *ᵥ (E *ᵥ |x| + f)‖ / ((1 - γ * ‖A⁻¹.abs * E‖) * ‖x‖) := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hpos : 0 < 1 - γ * ‖A⁻¹.abs * E‖ := by linarith
  have hAinv := entrywiseNonneg_abs A⁻¹
  -- the entrywise bound
  have hsub := sub_eq_inv_mulVec_of_mulVec_eq hA hx hy
  have hΔ : |Δb - ΔA *ᵥ y| ≤ γ • (f + E *ᵥ |y|) := by
    refine Pi.le_def.2 fun i => ?_
    have h2 := abs_mulVec_le ΔA y i
    have h3 : (ΔA.abs *ᵥ |y|) i ≤ (γ • (E *ᵥ |y|)) i := by
      simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => by
        have := hΔA i j
        simp only [Matrix.abs_apply, Matrix.smul_apply, smul_eq_mul] at this
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
    have h4 := hΔb i
    simp only [Pi.abs_apply, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul] at *
    calc |Δb i - (ΔA *ᵥ y) i| ≤ |Δb i| + |(ΔA *ᵥ y) i| := abs_sub _ _
      _ ≤ γ * f i + γ * (E *ᵥ |y|) i := add_le_add h4 (h2.trans h3)
      _ = γ * (f i + (E *ᵥ |y|) i) := by ring
  have hy' : |y| ≤ |x| + |y - x| := fun i => by
    have := abs_sub_abs_le_abs_sub (y i) (x i)
    simp only [Pi.abs_apply, Pi.add_apply, Pi.sub_apply]
    linarith
  have h1 : |y - x| ≤ γ • (A⁻¹.abs *ᵥ (E *ᵥ |x| + f)) + γ • ((A⁻¹.abs * E) *ᵥ |y - x|) := by
    calc |y - x| = |A⁻¹ *ᵥ (Δb - ΔA *ᵥ y)| := by rw [hsub]
      _ ≤ A⁻¹.abs *ᵥ |Δb - ΔA *ᵥ y| := abs_mulVec_le _ _
      _ ≤ A⁻¹.abs *ᵥ (γ • (f + E *ᵥ |y|)) := hAinv.mulVec_mono hΔ
      _ ≤ A⁻¹.abs *ᵥ (γ • (f + E *ᵥ (|x| + |y - x|))) := by
          refine hAinv.mulVec_mono (smul_le_smul_of_nonneg_left ?_ hγ)
          exact add_le_add le_rfl (hE.mulVec_mono hy')
      _ = γ • (A⁻¹.abs *ᵥ (E *ᵥ |x| + f)) + γ • ((A⁻¹.abs * E) *ᵥ |y - x|) := by
          ext i
          simp only [mulVec_add, mulVec_smul, mulVec_mulVec, Pi.add_apply, Pi.smul_apply,
            smul_eq_mul]
          ring
  -- the sup norm
  have h2 : ‖y - x‖ ≤ γ * ‖A⁻¹.abs *ᵥ (E *ᵥ |x| + f)‖ + γ * ‖A⁻¹.abs * E‖ * ‖y - x‖ := by
    refine (norm_le_norm_of_abs_le h1).trans ?_
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hγ, mul_assoc]
    refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hγ)
    rw [← norm_abs_eq (y - x)]
    exact linfty_opNorm_mulVec _ _
  rw [div_le_div_iff₀ hxn (mul_pos hpos hxn)]
  nlinarith [norm_nonneg (y - x)]

/-- The vector `|A⁻¹| |b|` is dominated by `|A⁻¹| |A| |x|` when `A x = b`. -/
theorem abs_inv_mulVec_abs_le (hx : A *ᵥ x = b) :
    A⁻¹.abs *ᵥ |b| ≤ A⁻¹.abs *ᵥ (A.abs *ᵥ |x|) := by
  refine (entrywiseNonneg_abs A⁻¹).mulVec_mono ?_
  rw [← hx]
  exact abs_mulVec_le A x

/-- **[quarteroni2000numerical] (3.15)**, both inequalities: for perturbations `|ΔA| ≤ γ |A|`,
`|Δb| ≤ γ |b|` with `γ cond(A) < 1`,
`‖δx‖_∞ / ‖x‖_∞ ≤ γ ‖|A⁻¹| |A| |x| + |A⁻¹| |b|‖_∞ / ((1 - γ cond(A)) ‖x‖_∞)`
and `‖δx‖_∞ / ‖x‖_∞ ≤ 2 γ cond(A) / (1 - γ cond(A))`, with `cond(A) = ‖|A⁻¹| |A|‖_∞` the Skeel
condition number. -/
theorem norm_sub_le_of_abs_le_abs (hA : IsUnit A) (hx : A *ᵥ x = b) (hy : (A + ΔA) *ᵥ y = b + Δb)
    {γ : ℝ} (hγ : 0 ≤ γ) (hΔA : ΔA.abs ≤ₑ γ • A.abs) (hΔb : |Δb| ≤ γ • |b|)
    (hsmall : γ * skeelCond A < 1) (hx0 : x ≠ 0) :
    ‖y - x‖ / ‖x‖ ≤
        γ * ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|) + A⁻¹.abs *ᵥ |b|‖ / ((1 - γ * skeelCond A) * ‖x‖) ∧
      ‖y - x‖ / ‖x‖ ≤ 2 * γ / (1 - γ * skeelCond A) * skeelCond A := by
  unfold skeelCond at hsmall ⊢
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hpos : 0 < 1 - γ * ‖A⁻¹.abs * A.abs‖ := by linarith
  have h := norm_sub_le_of_abs_le hA hx hy hγ (entrywiseNonneg_abs A) hΔA hΔb hsmall hx0
  rw [mulVec_add] at h
  refine ⟨h, h.trans ?_⟩
  have hb : ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|) + A⁻¹.abs *ᵥ |b|‖ ≤ 2 * (‖A⁻¹.abs * A.abs‖ * ‖x‖) := by
    calc ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|) + A⁻¹.abs *ᵥ |b|‖
        ≤ ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|)‖ + ‖A⁻¹.abs *ᵥ |b|‖ := norm_add_le _ _
      _ ≤ ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|)‖ + ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|)‖ := by
          refine add_le_add le_rfl (norm_le_norm_of_abs_le ?_)
          refine le_trans (le_of_eq ?_) (abs_inv_mulVec_abs_le hx)
          ext i
          rw [Pi.abs_apply]
          exact abs_of_nonneg ((entrywiseNonneg_abs A⁻¹).mulVec_nonneg (abs_nonneg b) i)
      _ = 2 * ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|)‖ := by ring
      _ ≤ 2 * (‖A⁻¹.abs * A.abs‖ * ‖x‖) := by
          rw [mulVec_mulVec, ← norm_abs_eq x]
          exact mul_le_mul_of_nonneg_left (linfty_opNorm_mulVec _ _) two_pos.le
  rw [div_le_iff₀ (mul_pos hpos hxn)]
  calc γ * ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|) + A⁻¹.abs *ᵥ |b|‖
      ≤ γ * (2 * (‖A⁻¹.abs * A.abs‖ * ‖x‖)) := mul_le_mul_of_nonneg_left hb hγ
    _ = 2 * γ / (1 - γ * ‖A⁻¹.abs * A.abs‖) * ‖A⁻¹.abs * A.abs‖ *
          ((1 - γ * ‖A⁻¹.abs * A.abs‖) * ‖x‖) := by
        field_simp

/-- **[quarteroni2000numerical] (3.16), the first bound**: if `A x = b`, `(A + ΔA) y = b` and
`|ΔA| ≤ γ |A|`, then `|y_i - x_i| ≤ γ |r_(i)ᵀ| |A| |y|` with `r_(i)ᵀ = e_iᵀ A⁻¹` the `i`-th row
of `A⁻¹`, since `y - x = -A⁻¹ ΔA y`. -/
theorem abs_sub_apply_le_of_abs_le_abs (hA : IsUnit A) (hx : A *ᵥ x = b) (hy : (A + ΔA) *ᵥ y = b)
    {γ : ℝ} (hΔA : ΔA.abs ≤ₑ γ • A.abs) (i : n) :
    |y i - x i| ≤ γ * (|A⁻¹ i| ⬝ᵥ (A.abs *ᵥ |y|)) := by
  have h := sub_eq_inv_mulVec_of_mulVec_eq (ΔA := ΔA) (Δb := 0) hA hx (by rw [add_zero]; exact hy)
  rw [zero_sub, mulVec_neg] at h
  have hi : y i - x i = -((A⁻¹ *ᵥ (ΔA *ᵥ y)) i) := by
    rw [← Pi.sub_apply, h]
    rfl
  have hΔ : ΔA.abs *ᵥ |y| ≤ γ • (A.abs *ᵥ |y|) := fun j => by
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have := hΔA j k
    simp only [Matrix.abs_apply, Matrix.smul_apply, smul_eq_mul] at this
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  rw [hi, abs_neg]
  calc |(A⁻¹ *ᵥ (ΔA *ᵥ y)) i| ≤ (A⁻¹.abs *ᵥ |ΔA *ᵥ y|) i := abs_mulVec_le _ _ i
    _ ≤ (A⁻¹.abs *ᵥ (ΔA.abs *ᵥ |y|)) i :=
        (entrywiseNonneg_abs A⁻¹).mulVec_mono (abs_mulVec_le ΔA y) i
    _ ≤ (A⁻¹.abs *ᵥ (γ • (A.abs *ᵥ |y|))) i := (entrywiseNonneg_abs A⁻¹).mulVec_mono hΔ i
    _ = γ * (|A⁻¹ i| ⬝ᵥ (A.abs *ᵥ |y|)) := by
        rw [mulVec_smul]
        rfl

/-- **[quarteroni2000numerical] (3.16), the second bound**: if `A x = b`, `A y = b + Δb` and
`|Δb| ≤ γ |b|`, then `|y_i - x_i| / |x_i| ≤ γ |r_(i)ᵀ| |b| / |r_(i)ᵀ b|`, since `x_i = r_(i)ᵀ b`
and `y_i - x_i = r_(i)ᵀ Δb`. -/
theorem abs_sub_apply_div_le_of_abs_le_abs (hA : IsUnit A) (hx : A *ᵥ x = b) (hy : A *ᵥ y = b + Δb)
    {γ : ℝ} (hΔb : |Δb| ≤ γ • |b|) (i : n) :
    |y i - x i| / |x i| ≤ γ * (|A⁻¹ i| ⬝ᵥ |b|) / |A⁻¹ i ⬝ᵥ b| := by
  have hAd : IsUnit A.det := (isUnit_iff_isUnit_det A).1 hA
  have hxi : x i = A⁻¹ i ⬝ᵥ b := by
    have : x = A⁻¹ *ᵥ b := by rw [← hx, mulVec_mulVec, nonsing_inv_mul A hAd, one_mulVec]
    rw [this]
    rfl
  have hyi : y i - x i = A⁻¹ i ⬝ᵥ Δb := by
    have h := sub_eq_inv_mulVec_of_mulVec_eq (ΔA := 0) (Δb := Δb) hA hx
      (by rw [add_zero]; exact hy)
    rw [zero_mulVec, sub_zero] at h
    have : y i - x i = (y - x) i := rfl
    rw [this, h]
    rfl
  rw [hyi, hxi]
  refine div_le_div_of_nonneg_right ?_ (abs_nonneg _)
  simp only [dotProduct, Pi.abs_apply, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have := hΔb j
  simp only [Pi.abs_apply, Pi.smul_apply, smul_eq_mul] at this
  rw [abs_mul, mul_left_comm]
  exact mul_le_mul_of_nonneg_left this (abs_nonneg _)

/-- **The LAPACK a posteriori bound**, [quarteroni2000numerical] §3.1.4: if `A x = b` and the
computed residual of an approximate solution `y` is `r̂ = (b - A y) + δr` with
`|δr| ≤ c (|A| |y| + |b|)`, then `‖y - x‖_∞ ≤ ‖|A⁻¹| (|r̂| + c (|A| |y| + |b|))‖_∞`, from
`y - x = -A⁻¹ r` and `|r| ≤ |r̂| + |δr|`. The book's display follows on dividing by `‖y‖_∞`; the
hypothesis on `r̂` is what `FloatingPoint.exists_roundsAffineStep_eq_add` provides for
`r̂ = fl(b - A y)`, with `c = γ_{n+1}`. -/
theorem norm_sub_le_of_computedResidual (hA : IsUnit A) (hx : A *ᵥ x = b) {rhat δr : n → ℝ}
    {c : ℝ} (hr : rhat = (b - A *ᵥ y) + δr) (hδr : |δr| ≤ c • (A.abs *ᵥ |y| + |b|)) :
    ‖y - x‖ ≤ ‖A⁻¹.abs *ᵥ (|rhat| + c • (A.abs *ᵥ |y| + |b|))‖ := by
  have hAd : IsUnit A.det := (isUnit_iff_isUnit_det A).1 hA
  have hyx : y - x = -(A⁻¹ *ᵥ (b - A *ᵥ y)) := by
    rw [mulVec_sub, mulVec_mulVec, nonsing_inv_mul A hAd, one_mulVec, ← hx, mulVec_mulVec,
      nonsing_inv_mul A hAd, one_mulVec, neg_sub]
  refine norm_le_norm_of_abs_le ?_
  rw [hyx, abs_neg]
  refine (abs_mulVec_le _ _).trans ((entrywiseNonneg_abs A⁻¹).mulVec_mono fun i => ?_)
  have h1 : b i - (A *ᵥ y) i = rhat i - δr i := by
    rw [hr]
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have h2 := hδr i
  simp only [Pi.abs_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h2 ⊢
  rw [h1]
  calc |rhat i - δr i| ≤ |rhat i| + |δr i| := abs_sub _ _
    _ ≤ |rhat i| + c * ((A.abs *ᵥ |y|) i + |b i|) := add_le_add le_rfl h2

end Perturbation

end Matrix
