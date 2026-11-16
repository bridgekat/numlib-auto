/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.Conditioning.LinearSystem

/-!
# Componentwise perturbation theory for linear systems

This module studies the linear system $Ax = b$ for a real square matrix $A$ under componentwise
perturbations: perturbations $\Delta A$ and $\Delta b$ bounded entrywise, $|\Delta A| \le \gamma E$
and $|\Delta b| \le \gamma f$. Here $|A|$ is the matrix of the absolute values of the entries of
$A$, and the inequalities are entrywise. The main quantities are the **Skeel condition numbers**
$$\operatorname{cond}(A, x) = \frac{\| |A^{-1}| \, |A| \, |x| \|_\infty}{\|x\|_\infty}, \qquad
\operatorname{cond}(A) = \| |A^{-1}| \, |A| \|_\infty,$$ which, unlike $\kappa(A)$, do not change
under a row scaling $A \mapsto DA$. The module proves the componentwise perturbation theorem, the
bounds (3.15) and (3.16) of [quarteroni2000numerical], the a posteriori bound of §3.1.4 of the
source, the bound $\operatorname{cond}(A) \le \kappa_\infty(A)$, and the Oettli–Prager theorem with
the componentwise backward error. The sources are [quarteroni2000numerical], §3.1.2, §3.1.4 and
Remark 3.7, [higham2002accuracy], §7.2, and [golub2013matrix], §2.6.5; the theory goes back to
Skeel.

## Main definitions

* `Matrix.skeelCondAt`, `Matrix.skeelCond`: the Skeel condition numbers $\operatorname{cond}(A, x)$
  and $\operatorname{cond}(A)$ of Remark 3.7 of [quarteroni2000numerical].
* `Matrix.componentwiseBackwardError`: the componentwise backward error
  $\max_i |b - Ax|_i / (|E| |x| + |f|)_i$.

## Main results

* `Matrix.skeelCond_eq_iSup_skeelCondAt`: $\operatorname{cond}(A) = \sup_x \operatorname{cond}(A,
  x)$.
* `Matrix.skeelCondAt_diagonal_mul`: $\operatorname{cond}(DA, x) = \operatorname{cond}(A, x)$ for a
  nonsingular diagonal $D$.
* `Matrix.norm_sub_le_of_abs_le`: the componentwise perturbation theorem, Theorem 7.4 of
  [higham2002accuracy].
* `Matrix.norm_sub_le_of_abs_le_abs`: the bound (3.15) of [quarteroni2000numerical], with $\|\delta
  x\|_\infty / \|x\|_\infty \le 2 \gamma \operatorname{cond}(A) / (1 - \gamma
  \operatorname{cond}(A))$.
* `Matrix.abs_sub_apply_le_of_abs_le_abs`, `Matrix.abs_sub_apply_div_le_of_abs_le_abs`: the
  row-by-row bounds (3.16) of [quarteroni2000numerical].
* `Matrix.norm_sub_le_of_computedResidual`: the LAPACK a posteriori bound of §3.1.4 of
  [quarteroni2000numerical].
* `Matrix.skeelCond_le_condNumberLp_top`: $\operatorname{cond}(A) \le \kappa_\infty(A)$, from §2.6.5
  of [golub2013matrix].
* `Matrix.exists_perturbation_iff_abs_residual_le`: the Oettli–Prager theorem, for rectangular
  systems.
* `Matrix.isLeast_componentwiseBackwardError`: the componentwise backward error is the least
  admissible $\omega$.

## Implementation notes

* The entrywise order and absolute value are those of `Numlib.LinearAlgebra.Matrix.Order`:
  `Matrix.abs` is $|A|$, and `≤ₑ` is the entrywise order on matrices. On vectors the order and the
  absolute value are those of the function type.
* Vectors carry the sup norm $\|\cdot\|_\infty$ of the function type, and matrices carry the maximum
  absolute row sum, which is the operator norm induced by $\|\cdot\|_\infty$ (Mathlib's scoped
  `Matrix.Norms.Operator` instance).
* The hypothesis on the computed residual in `Matrix.norm_sub_le_of_computedResidual` is what
  `FloatingPoint.exists_roundsAffineStep_eq_add` of `Numlib.FloatingPoint.Stationary` gives for the
  computed residual $\hat r = \mathrm{fl}(b - Ay)$. The bound is stated for an arbitrary constant
  $c$ in place of $\gamma_{n+1}$.
* This module is separate from `Numlib.Conditioning.LinearSystem` because that module works with
  operators and norms only, and everything here needs matrix entries.
-/

open Finset

open scoped Matrix Matrix.Norms.Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The Skeel condition numbers -/

section Skeel

variable (A : Matrix n n ℝ)

/-- **Skeel's condition number of a system.** For a real square matrix $A$ and a vector $x$,
$$\operatorname{cond}(A, x) = \frac{\| |A^{-1}| \, |A| \, |x| \|_\infty}{\|x\|_\infty},$$ where
$|\cdot|$ is the entrywise absolute value. It measures how much a componentwise relative
perturbation of $A$ is amplified in the sup norm of the solution $x$. It is $0$ for $x = 0$.

This is the number of Remark 3.7 of [quarteroni2000numerical] and (7.11) of
[higham2002accuracy]. The inverse $A^{-1}$ is Mathlib's matrix inverse, which is $0$ for a
singular $A$. The printed display of Remark 3.7 of [quarteroni2000numerical] lacks some of the
absolute values; the definition reads it with these absolute values restored. -/
noncomputable def skeelCondAt (x : n → ℝ) : ℝ := ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|)‖ / ‖x‖

/-- **Skeel's condition number of a matrix.** For a real square matrix $A$,
$$\operatorname{cond}(A) = \| |A^{-1}| \, |A| \|_\infty,$$ where $|\cdot|$ is the entrywise
absolute value and $\|\cdot\|_\infty$ is the maximum absolute row sum. It is the supremum of
$\operatorname{cond}(A, x)$ over $x$ (`Matrix.skeelCond_eq_iSup_skeelCondAt`). This is the
number of Remark 3.7 of [quarteroni2000numerical] and (7.11) of [higham2002accuracy]. -/
noncomputable def skeelCond : ℝ := ‖A⁻¹.abs * A.abs‖

variable {A}

/-- For every vector $x$, $\operatorname{cond}(A, x) \le \operatorname{cond}(A)$. -/
theorem skeelCondAt_le_skeelCond (x : n → ℝ) : skeelCondAt A x ≤ skeelCond A := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [skeelCondAt, skeelCond]
  rw [skeelCondAt, skeelCond, div_le_iff₀ (norm_pos_iff.2 hx), mulVec_mulVec, ← norm_abs_eq x]
  exact linfty_opNorm_mulVec _ _

/-- For every vector $x$, $\operatorname{cond}(A, x) \ge 0$. -/
theorem skeelCondAt_nonneg (x : n → ℝ) : 0 ≤ skeelCondAt A x :=
  div_nonneg (norm_nonneg _) (norm_nonneg _)

/-- **$\operatorname{cond}(A)$ is the supremum of the $\operatorname{cond}(A, x)$** (Remark 3.7 of
[quarteroni2000numerical]). If $A$ has at least one row, then $$\operatorname{cond}(A) = \sup_x
\operatorname{cond}(A, x).$$

The supremum is attained at the vector of ones $\mathbb{1}$, where
$|A^{-1}| \, |A| \, \mathbb{1}$ is the vector of the row sums of $|A^{-1}| \, |A|$. -/
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

/-- For a vector $d$ and a square matrix $B$, $|\operatorname{diag}(d) \, B| =
\operatorname{diag}(|d_i|) \, |B|$. -/
theorem abs_diagonal_mul (d : n → ℝ) (B : Matrix n n ℝ) :
    (diagonal d * B).abs = diagonal (fun i => |d i|) * B.abs := by
  ext i j
  simp [diagonal_mul, abs_mul]

/-- For a square matrix $B$ and a vector $d$, $|B \operatorname{diag}(d)| = |B|
\operatorname{diag}(|d_i|)$. -/
theorem abs_mul_diagonal (B : Matrix n n ℝ) (d : n → ℝ) :
    (B * diagonal d).abs = B.abs * diagonal (fun i => |d i|) := by
  ext i j
  simp [mul_diagonal, abs_mul]

/-- **Row scaling invariance of Skeel's condition number** (Remark 3.7 of
[quarteroni2000numerical]). Let $D = \operatorname{diag}(d)$ with $d_i \neq 0$ for all $i$. Then
for every vector $x$, $$\operatorname{cond}(DA, x) = \operatorname{cond}(A, x).$$

The reason is $|(DA)^{-1}| \, |DA| = |A^{-1}| \, |D^{-1}| \, |D| \, |A| = |A^{-1}| \, |A|$. The
condition number $\kappa(A)$ does not have this invariance; this is why $\operatorname{cond}(A)$
measures the ill-conditioning of a matrix independently of a row scaling. -/
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

/-- Let $A$ be invertible. If $Ax = b$ and $(A + \Delta A) y = b + \Delta b$, then the error of the
perturbed solution is $$y - x = A^{-1} (\Delta b - \Delta A \, y).$$
-/
theorem sub_eq_inv_mulVec_of_mulVec_eq (hA : IsUnit A) (hx : A *ᵥ x = b)
    (hy : (A + ΔA) *ᵥ y = b + Δb) : y - x = A⁻¹ *ᵥ (Δb - ΔA *ᵥ y) := by
  have hAd : IsUnit A.det := (isUnit_iff_isUnit_det A).1 hA
  have h1 : A *ᵥ (y - x) = Δb - ΔA *ᵥ y := by
    rw [add_mulVec] at hy
    rw [mulVec_sub, hx, ← sub_eq_iff_eq_add'.2 hy]
    abel
  rw [← h1, mulVec_mulVec, nonsing_inv_mul A hAd, one_mulVec]

/-- **The componentwise perturbation theorem**, Theorem 7.4 of [higham2002accuracy], after Skeel.
Let $A$ be an invertible real square matrix, let $E$ be an entrywise nonnegative matrix, let $f$
be a vector, and let $\gamma \ge 0$ with $\gamma \| |A^{-1}| E \|_\infty < 1$. If $Ax = b$ with
$x \neq 0$, $(A + \Delta A) y = b + \Delta b$, $|\Delta A| \le \gamma E$ and
$|\Delta b| \le \gamma f$ entrywise, then $$\frac{\|y - x\|_\infty}{\|x\|_\infty} \le
\frac{\gamma \, \| |A^{-1}| (E |x| + f) \|_\infty}{(1 - \gamma \| |A^{-1}| E \|_\infty) \,
\|x\|_\infty}.$$

The proof starts from $y - x = A^{-1} (\Delta b - \Delta A \, y)$, which gives $|y - x| \le
\gamma |A^{-1}| (f + E |x|) + \gamma |A^{-1}| E \, |y - x|$, and then takes the sup norm. -/
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

/-- If $Ax = b$, then $|A^{-1}| \, |b| \le |A^{-1}| \, |A| \, |x|$ entrywise. -/
theorem abs_inv_mulVec_abs_le (hx : A *ᵥ x = b) :
    A⁻¹.abs *ᵥ |b| ≤ A⁻¹.abs *ᵥ (A.abs *ᵥ |x|) := by
  refine (entrywiseNonneg_abs A⁻¹).mulVec_mono ?_
  rw [← hx]
  exact abs_mulVec_le A x

/-- **The bound (3.15)** of [quarteroni2000numerical], both inequalities. Let $A$ be an invertible
real square matrix and $\gamma \ge 0$ with $\gamma \operatorname{cond}(A) < 1$, where
$\operatorname{cond}(A) = \| |A^{-1}| \, |A| \|_\infty$ is Skeel's condition number. If $Ax = b$
with $x \neq 0$, $(A + \Delta A) y = b + \Delta b$, $|\Delta A| \le \gamma |A|$ and
$|\Delta b| \le \gamma |b|$ entrywise, then $$\frac{\|y - x\|_\infty}{\|x\|_\infty} \le
\frac{\gamma \, \| |A^{-1}| \, |A| \, |x| + |A^{-1}| \, |b| \|_\infty}{(1 - \gamma
\operatorname{cond}(A)) \, \|x\|_\infty} \quad \text{and} \quad \frac{\|y -
x\|_\infty}{\|x\|_\infty} \le \frac{2 \gamma \operatorname{cond}(A)}{1 - \gamma
\operatorname{cond}(A)}.$$

This is `Matrix.norm_sub_le_of_abs_le` with $E = |A|$ and $f = |b|$. The source writes
$\delta x$ for $y - x$. -/
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

/-- **The bound (3.16)** of [quarteroni2000numerical], the first inequality. Let $A$ be an
invertible real square matrix, and let $r_{(i)}^T = e_i^T A^{-1}$ be the $i$-th row of $A^{-1}$.
If $Ax = b$, $(A + \Delta A) y = b$ and $|\Delta A| \le \gamma |A|$ entrywise, then for every
$i$, $$|y_i - x_i| \le \gamma \, |r_{(i)}^T| \, |A| \, |y|.$$

The proof uses $y - x = -A^{-1} \Delta A \, y$. -/
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

/-- **The bound (3.16)** of [quarteroni2000numerical], the second inequality. Let $A$ be an
invertible real square matrix, and let $r_{(i)}^T = e_i^T A^{-1}$ be the $i$-th row of $A^{-1}$.
If $Ax = b$, $Ay = b + \Delta b$ and $|\Delta b| \le \gamma |b|$ entrywise, then for every $i$,
$$\frac{|y_i - x_i|}{|x_i|} \le \frac{\gamma \, |r_{(i)}^T| \, |b|}{|r_{(i)}^T b|}.$$ Both sides
are $0$ when their denominator is $0$.

The proof uses $x_i = r_{(i)}^T b$ and $y_i - x_i = r_{(i)}^T \Delta b$. -/
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

/-- **The LAPACK a posteriori bound**, §3.1.4 of [quarteroni2000numerical]. Let $A$ be an invertible
real square matrix with $Ax = b$, let $y$ be an approximate solution, and let $c$ be real.
Suppose that the computed residual is $\hat r = (b - Ay) + \delta r$ with
$|\delta r| \le c \, (|A| \, |y| + |b|)$ entrywise. Then $$\|y - x\|_\infty \le \| |A^{-1}| \,
(|\hat r| + c \, (|A| \, |y| + |b|)) \|_\infty.$$

The display of the source follows on division by $\|y\|_\infty$. The proof uses
$y - x = -A^{-1} r$ with $r = b - Ay$, and $|r| \le |\hat r| + |\delta r|$. The hypothesis on
$\hat r$ is what `FloatingPoint.exists_roundsAffineStep_eq_add` gives for
$\hat r = \mathrm{fl}(b - Ay)$, with $c = \gamma_{n+1}$. -/
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

/-! ### Skeel's condition number against $\kappa_\infty$ -/

/-- **Skeel's condition number never exceeds $\kappa_\infty$** (§2.6.5 of [golub2013matrix]). For
every real square matrix $A$, $$\operatorname{cond}(A) = \| |A^{-1}| \, |A| \|_\infty \le \|
|A^{-1}| \|_\infty \, \| |A| \|_\infty = \|A^{-1}\|_\infty \|A\|_\infty = \kappa_\infty(A).$$

The condition number $\kappa_\infty(A)$ is `Matrix.condNumberLp ⊤ A`. The proof uses
submultiplicativity and the invariance of the $\infty$-norm under entrywise absolute values. -/
theorem skeelCond_le_condNumberLp_top (A : Matrix n n ℝ) : skeelCond A ≤ condNumberLp ⊤ A := by
  rw [skeelCond, condNumberLp, lpOpNorm_top, lpOpNorm_top, mul_comm (‖A‖)]
  refine (linfty_opNorm_mul _ _).trans ?_
  rw [linfty_opNorm_abs, linfty_opNorm_abs]

/-! ### The Oettli–Prager theorem and the componentwise backward error -/

section OettliPrager

variable {m p : Type*} [Fintype p]

/-- For every real $t$, $|\operatorname{sign} t| \le 1$. -/
private theorem abs_sign_le_one (t : ℝ) : |(SignType.sign t : ℝ)| ≤ 1 := by
  rcases lt_trichotomy t 0 with h | h | h
  · simp [sign_neg h]
  · simp [h]
  · simp [sign_pos h]

/-- **The Oettli–Prager theorem**, (2.6.13) of [golub2013matrix] and Theorem 7.3 of
[higham2002accuracy], after Oettli and Prager (1964). Let $A, E$ be real $m \times p$ matrices
with $p$ finite, let $b, f \in \mathbb{R}^m$ and $x \in \mathbb{R}^p$, and let $\omega \ge 0$.
Then there are $\Delta A$ and $\Delta b$ with $$(A + \Delta A) x = b + \Delta b, \qquad |\Delta
A| \le \omega |E|, \qquad |\Delta b| \le \omega |f|$$ if and only if the residual satisfies
$$|b - Ax| \le \omega \, (|E| \, |x| + |f|).$$ All inequalities are entrywise.

The forward direction bounds $b - Ax = \Delta A \, x - \Delta b$. For the converse, let
$r = b - Ax$ and $s = |E| \, |x| + |f|$, and take, row by row, $\Delta A_{ij} = (r_i / s_i)
|E_{ij}| \operatorname{sign}(x_j)$ and $\Delta b_i = -(r_i / s_i) |f_i|$; a row with $s_i = 0$
has $r_i = 0$. -/
theorem exists_perturbation_iff_abs_residual_le (A E : Matrix m p ℝ) (b f : m → ℝ) (x : p → ℝ)
    {ω : ℝ} (hω : 0 ≤ ω) :
    (∃ (ΔA : Matrix m p ℝ) (Δb : m → ℝ), (A + ΔA) *ᵥ x = b + Δb ∧ ΔA.abs ≤ₑ ω • E.abs ∧
      |Δb| ≤ ω • |f|) ↔ |b - A *ᵥ x| ≤ ω • (E.abs *ᵥ |x| + |f|) := by
  constructor
  · rintro ⟨ΔA, Δb, h, hA, hb⟩
    have hr : b - A *ᵥ x = ΔA *ᵥ x - Δb := by
      rw [add_mulVec] at h
      have hb' : b = A *ᵥ x + ΔA *ᵥ x - Δb := by rw [h]; abel
      rw [hb']
      abel
    have hAx : |ΔA *ᵥ x| ≤ ω • (E.abs *ᵥ |x|) := by
      refine (abs_mulVec_le ΔA x).trans ?_
      rw [← smul_mulVec]
      exact hA.mulVec_le_of_nonneg (fun j => abs_nonneg (x j))
    intro i
    rw [hr, smul_add, Pi.add_apply]
    exact (abs_sub _ _).trans (add_le_add (hAx i) (hb i))
  · intro h
    set r := b - A *ᵥ x with hr
    set s := E.abs *ᵥ |x| + |f| with hs
    have hs0 : ∀ i, 0 ≤ s i := fun i =>
      add_nonneg ((entrywiseNonneg_abs E).mulVec_nonneg (fun j => abs_nonneg (x j)) i)
        (abs_nonneg (f i))
    have hri : ∀ i, |r i| ≤ ω * s i := fun i => h i
    set c : m → ℝ := fun i => r i / s i with hc
    have hcs : ∀ i, c i * s i = r i := fun i => by
      rcases eq_or_ne (s i) 0 with h0 | h0
      · have : r i = 0 := abs_nonpos_iff.1 (by simpa [h0] using hri i)
        simp [hc, h0, this]
      · exact div_mul_cancel₀ _ h0
    have hcω : ∀ i, |c i| ≤ ω := fun i => by
      rcases eq_or_ne (s i) 0 with h0 | h0
      · simp [hc, h0, hω]
      · rw [hc, abs_div, abs_of_nonneg (hs0 i), div_le_iff₀ ((hs0 i).lt_of_ne' h0)]
        exact hri i
    refine ⟨Matrix.of fun i j => c i * |E i j| * SignType.sign (x j), fun i => -(c i * |f i|),
      ?_, fun i j => ?_, fun i => ?_⟩
    · ext i
      have hrow : (Matrix.of fun i j => c i * |E i j| * SignType.sign (x j)) *ᵥ x
          = fun i => c i * (E.abs *ᵥ |x|) i := by
        ext i
        simp only [mulVec, dotProduct, of_apply, Finset.mul_sum, abs_apply, Pi.abs_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_assoc, mul_assoc, sign_mul_self]
      have hi := hcs i
      rw [hs, Pi.add_apply, mul_add] at hi
      rw [add_mulVec, Pi.add_apply, hrow, Pi.add_apply]
      simp only [hr, Pi.sub_apply, Pi.abs_apply] at hi
      linarith
    · rw [abs_apply, of_apply, Matrix.smul_apply, abs_apply, smul_eq_mul, abs_mul, abs_mul, abs_abs]
      calc |c i| * |E i j| * |(SignType.sign (x j) : ℝ)| ≤ ω * |E i j| * 1 := by
            gcongr
            · exact hcω i
            · exact abs_sign_le_one _
        _ = ω * |E i j| := mul_one _
    · rw [Pi.abs_apply, Pi.smul_apply, Pi.abs_apply, smul_eq_mul, abs_neg, abs_mul, abs_abs]
      exact mul_le_mul_of_nonneg_right (hcω i) (abs_nonneg _)

/-- The **componentwise backward error** of $x$ for $Ax = b$, with the tolerances $E$ on $A$ and $f$
on $b$: $$\omega_{\min} = \max_i \frac{|b - Ax|_i}{(|E| \, |x| + |f|)_i},$$ where a row with
zero denominator contributes $0$. This is $\omega_{\min}$ of §2.6.5 of [golub2013matrix] and
(7.8) of [higham2002accuracy].

By `Matrix.isLeast_componentwiseBackwardError` it is the least $\omega$ for which $x$ solves
exactly a perturbed system with $|\Delta A| \le \omega |E|$ and $|\Delta b| \le \omega |f|$,
when such an $\omega$ exists. The maximum is the real supremum `⨆ i`, which is meaningful for
finitely many rows. The normwise counterpart is the Rigal–Gaches `backwardError` of
`Numlib.Conditioning.LinearSystem`. -/
noncomputable def componentwiseBackwardError (A E : Matrix m p ℝ) (b f : m → ℝ) (x : p → ℝ) :
    ℝ :=
  ⨆ i, |(b - A *ᵥ x) i| / (E.abs *ᵥ |x| + |f|) i

/-- **The componentwise backward error is attained** (§2.6.5 of [golub2013matrix], Theorem 7.3 of
[higham2002accuracy]). Let $A, E$ be real $m \times p$ matrices with $m$ and $p$ finite, and
$b, f \in \mathbb{R}^m$, $x \in \mathbb{R}^p$. Suppose that every row $i$ with
$(|E| \, |x| + |f|)_i = 0$ has $(b - Ax)_i = 0$. Then $\omega_{\min}$
(`Matrix.componentwiseBackwardError`) is the least $\omega \ge 0$ for which there are $\Delta A$
and $\Delta b$ with $(A + \Delta A) x = b + \Delta b$, $|\Delta A| \le \omega |E|$ and
$|\Delta b| \le \omega |f|$ entrywise.

If the hypothesis fails, no $\omega$ works, and the source writes $\omega_{\min} = \infty$. The
proof applies `Matrix.exists_perturbation_iff_abs_residual_le` row by row. -/
theorem isLeast_componentwiseBackwardError [Finite m] (A E : Matrix m p ℝ) (b f : m → ℝ)
    (x : p → ℝ) (hz : ∀ i, (E.abs *ᵥ |x| + |f|) i = 0 → (b - A *ᵥ x) i = 0) :
    IsLeast {ω : ℝ | 0 ≤ ω ∧ ∃ (ΔA : Matrix m p ℝ) (Δb : m → ℝ),
      (A + ΔA) *ᵥ x = b + Δb ∧ ΔA.abs ≤ₑ ω • E.abs ∧ |Δb| ≤ ω • |f|}
      (componentwiseBackwardError A E b f x) := by
  set s := E.abs *ᵥ |x| + |f| with hs
  have hs0 : ∀ i, 0 ≤ s i := fun i =>
    add_nonneg ((entrywiseNonneg_abs E).mulVec_nonneg (fun j => abs_nonneg (x j)) i)
      (abs_nonneg (f i))
  have hterm : ∀ i, 0 ≤ |(b - A *ᵥ x) i| / s i := fun i => div_nonneg (abs_nonneg _) (hs0 i)
  have h0 : 0 ≤ componentwiseBackwardError A E b f x := Real.iSup_nonneg hterm
  refine ⟨⟨h0, (exists_perturbation_iff_abs_residual_le A E b f x h0).2 fun i => ?_⟩, ?_⟩
  · change |(b - A *ᵥ x) i| ≤ componentwiseBackwardError A E b f x * s i
    rcases eq_or_ne (s i) 0 with hsi | hsi
    · rw [hz i hsi, abs_zero]
      exact mul_nonneg h0 (hs0 i)
    · rw [← div_le_iff₀ ((hs0 i).lt_of_ne' hsi)]
      exact le_ciSup (f := fun i => |(b - A *ᵥ x) i| / s i) (Finite.bddAbove_range _) i
  · rintro ω ⟨hω, h⟩
    have hr := (exists_perturbation_iff_abs_residual_le A E b f x hω).1 h
    refine Real.iSup_le (fun i => ?_) hω
    rcases eq_or_ne (s i) 0 with hsi | hsi
    · change |(b - A *ᵥ x) i| / s i ≤ ω
      rw [hsi, div_zero]
      exact hω
    · change |(b - A *ᵥ x) i| / s i ≤ ω
      rw [div_le_iff₀ ((hs0 i).lt_of_ne' hsi)]
      exact hr i

end OettliPrager

end Matrix
