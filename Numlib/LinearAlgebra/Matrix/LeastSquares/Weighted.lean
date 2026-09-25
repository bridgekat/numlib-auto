/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.LeastSquares`, beside the least-squares solutions
of `Numlib/LinearAlgebra/Matrix/LeastSquares`.
-/
import Numlib.LinearAlgebra.Matrix.LeastSquares

/-!
# Weighted and generalized least squares

Weighted and generalized least-squares problems ([golub2013matrix] §6.1.1–6.1.3), in the operator
picture of `Numlib/LinearAlgebra/Matrix/LeastSquares`: vectors are `EuclideanSpace 𝕜 m`, matrices
act through `Matrix.toEuclideanLin`, the scalars are `[RCLike 𝕜]` except in the statements about a
derivative in a weight, which are over `ℝ`.

## Design

* **No weighted-least-squares predicate.** "`x` minimizes `‖M (A x - b)‖`" is literally
  `Matrix.IsLeastSquaresSolution (M * A) (toEuclideanLin M b) x`; a surface names the book's
  diagonal-weight problem as an abbreviation of it.
* **`Matrix.weightedLeastSquaresOp W A = (Aᴴ W A)⁻¹ Aᴴ W`** is the solution operator of the weighted
  problem for full column rank and Hermitian positive definite `W = Mᴴ M`: the full-rank weighted
  pseudoinverse, not the general-rank weighted pseudoinverse of the literature. "Weighted" here
  always means row (or column) weights.
* The augmented-system lemma carries a general weight factor `M`, so the unweighted augmented system
  ([golub2013matrix] (5.3.20)) is its case `M = 1`.
* **Paige's generalized least-squares problem** `min {‖v‖ : b = A x + B v}` is the predicate
  `Matrix.IsGeneralizedLeastSquaresSolution`, defined for rank-deficient `A` and `B`; for a
  nonsingular `B` it is the weighted problem with weight `B⁻¹`. Paige's method is stated through the
  equations that define its output, so it needs neither `B` nor the factor `S` to be triangular.

## Main definitions

* `Matrix.weightedLeastSquaresOp`: the weighted solution operator `(Aᴴ W A)⁻¹ Aᴴ W`.
* `Matrix.weightedResidual`: the residual of the weighted solution as a function of real weights.
* `Matrix.IsGeneralizedLeastSquaresSolution`: Paige's generalized least-squares problem.

## Main results

* `Matrix.isLeastSquaresSolution_weightedLeastSquaresOp`: the weighted solution is the unique
  solution of the weighted problem ([golub2013matrix] (6.1.1)–(6.1.2)).
* `Matrix.weightedLeastSquaresOp_mulVec_sub_pinv_mulVec`: weighted minus unweighted solution
  ([golub2013matrix] (6.1.3)).
* `Matrix.hasDerivAt_weightedResidual`, `Matrix.antitoneOn_abs_weightedResidual`: the derivative
  of a residual in its own weight, and the monotone decrease of that residual
  ([golub2013matrix] (6.1.4)).
* `Matrix.isLeastSquaresSolution_of_augmented`: the augmented system ([golub2013matrix] (6.1.5)).
* `Matrix.isGeneralizedLeastSquaresSolution_iff`,
  `Matrix.isGeneralizedLeastSquaresSolution_of_paige`: the generalized problem for nonsingular `B`,
  and Paige's method ([golub2013matrix] (6.1.7)–(6.1.10)).
* `Matrix.isLeastSquaresSolution_mul_inv_iff`,
  `Matrix.IsMinNormLeastSquaresSolution.norm_le_of_mul_inv`: column weighting
  ([golub2013matrix] §6.1.3).

## References

* [golub2013matrix] §6.1.1–6.1.3.
-/

open Finset
open scoped ComplexOrder

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-! ### The weighted solution operator -/

section Weighted

/-- The **weighted least-squares solution operator** `(Aᴴ W A)⁻¹ Aᴴ W` ([golub2013matrix] (6.1.2)
with `W = D²`). It solves `min ‖M (A x - b)‖` when `W = Mᴴ M` for an invertible `M` and `A` has full
column rank (`Matrix.isLeastSquaresSolution_weightedLeastSquaresOp`), and it is junk (through Lean's
`⁻¹`) when `Aᴴ W A` is singular. It is not the general-rank weighted pseudoinverse. -/
noncomputable def weightedLeastSquaresOp (W : Matrix m m 𝕜) (A : Matrix m n 𝕜) : Matrix n m 𝕜 :=
  (Aᴴ * W * A)⁻¹ * Aᴴ * W

/-- The weighted solution operator, unfolded. -/
theorem weightedLeastSquaresOp_def (W : Matrix m m 𝕜) (A : Matrix m n 𝕜) :
    weightedLeastSquaresOp W A = (Aᴴ * W * A)⁻¹ * Aᴴ * W := rfl

variable [DecidableEq m]

/-- **The weighted solution solves the weighted problem** ([golub2013matrix] (6.1.1)–(6.1.2)): for
an invertible weight factor `M` and `A` of full column rank, the least-squares solutions of
`M A x = M b` are exactly `x = (Aᴴ Mᴴ M A)⁻¹ Aᴴ Mᴴ M b`. The matrix `M A` has full column rank, and
its pseudoinverse is `((M A)ᴴ (M A))⁻¹ (M A)ᴴ`. -/
theorem isLeastSquaresSolution_weightedLeastSquaresOp {M : Matrix m m 𝕜} (hM : IsUnit M)
    {A : Matrix m n 𝕜} (hA : LinearIndependent 𝕜 Aᵀ) {b : EuclideanSpace 𝕜 m}
    {x : EuclideanSpace 𝕜 n} :
    IsLeastSquaresSolution (M * A) (toEuclideanLin M b) x ↔
      x = toEuclideanLin (weightedLeastSquaresOp (Mᴴ * M) A) b := by
  have hMA : LinearIndependent 𝕜 (M * A)ᵀ := by
    refine mulVec_injective_iff.1 fun y z hyz => ?_
    have h1 : Function.Injective M.mulVec := mulVec_injective_iff_isUnit.2 hM
    have h2 : Function.Injective A.mulVec := mulVec_injective_iff.2 hA
    exact h2 (h1 (by simpa only [mulVec_mulVec] using hyz))
  have hgram : (M * A)ᴴ * (M * A) = Aᴴ * (Mᴴ * M) * A := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [isLeastSquaresSolution_iff_eq_pinv_of_linearIndependent hMA,
    pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose hMA, ← toEuclideanLin_mul_apply, hgram,
    weightedLeastSquaresOp, conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- **Weighted minus unweighted solution** ([golub2013matrix] (6.1.3)): if `Aᴴ W A` is invertible,
`x_W - x = (Aᴴ W A)⁻¹ Aᴴ (W - 1) (b - A x)` with `x = A⁺ b` the unweighted (minimal-norm)
least-squares solution. Subtract the two normal equations: `Aᴴ (b - A x) = 0`, so
`Aᴴ W A (x_W - x) = Aᴴ W (b - A x) - Aᴴ (b - A x)`. No rank hypothesis on `A` beyond the
invertibility of `Aᴴ W A` is needed. -/
theorem weightedLeastSquaresOp_mulVec_sub_pinv_mulVec {W : Matrix m m 𝕜} {A : Matrix m n 𝕜}
    (hW : IsUnit (Aᴴ * W * A)) (b : EuclideanSpace 𝕜 m) :
    toEuclideanLin (weightedLeastSquaresOp W A) b - toEuclideanLin A.pinv b =
      toEuclideanLin ((Aᴴ * W * A)⁻¹ * Aᴴ * (W - 1))
        (b - toEuclideanLin A (toEuclideanLin A.pinv b)) := by
  have hdet : IsUnit (Aᴴ * W * A).det := (isUnit_iff_isUnit_det _).1 hW
  have h1 : (Aᴴ * W * A)⁻¹ * (Aᴴ * W * A) = 1 := nonsing_inv_mul _ hdet
  have h2 : Aᴴ * (A * A.pinv) = Aᴴ := conjTranspose_mul_mul_pinv A
  have key : weightedLeastSquaresOp W A - A.pinv =
      (Aᴴ * W * A)⁻¹ * Aᴴ * (W - 1) * (1 - A * A.pinv) := by
    have e1 : A.pinv = (Aᴴ * W * A)⁻¹ * (Aᴴ * W * A) * A.pinv := by rw [h1, Matrix.one_mul]
    have e2 : (Aᴴ * W * A)⁻¹ * (Aᴴ * (A * A.pinv)) = (Aᴴ * W * A)⁻¹ * Aᴴ := by rw [h2]
    conv_lhs => rw [e1]
    rw [weightedLeastSquaresOp]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc] at e2 ⊢
    rw [e2]
    abel
  rw [← LinearMap.sub_apply, ← map_sub, key, toEuclideanLin_mul_apply]
  congr 1
  rw [toEuclideanLin_sub_apply, toEuclideanLin_one_apply, toEuclideanLin_mul_apply]

/-- **The augmented system of weighted least squares** ([golub2013matrix] (6.1.5), and (5.3.20) at
`M = 1`): for an invertible weight factor `M`, if `r` and `x` satisfy `(Mᴴ M)⁻¹ r + A x = b` and
`Aᴴ r = 0`, then `x` solves the weighted problem `min ‖M (A x - b)‖`. Indeed `r = Mᴴ M (b - A x)`,
so the second equation is the normal equations of the weighted problem. -/
theorem isLeastSquaresSolution_of_augmented {M : Matrix m m 𝕜} (hM : IsUnit M)
    {A : Matrix m n 𝕜} {b r : EuclideanSpace 𝕜 m} {x : EuclideanSpace 𝕜 n}
    (h1 : toEuclideanLin (Mᴴ * M)⁻¹ r + toEuclideanLin A x = b) (h2 : toEuclideanLin Aᴴ r = 0) :
    IsLeastSquaresSolution (M * A) (toEuclideanLin M b) x := by
  have hW : IsUnit (Mᴴ * M) := ((isUnit_conjTranspose M).2 hM).mul hM
  have hr : toEuclideanLin (Mᴴ * M) (b - toEuclideanLin A x) = r := by
    rw [← h1, add_sub_cancel_right, toEuclideanLin_mul_nonsing_inv_apply hW]
  rw [isLeastSquaresSolution_iff_normalEquations]
  have key : toEuclideanLin (M * A)ᴴ (toEuclideanLin M b) - toEuclideanLin ((M * A)ᴴ * (M * A)) x =
      toEuclideanLin Aᴴ (toEuclideanLin (Mᴴ * M) (b - toEuclideanLin A x)) := by
    simp only [conjTranspose_mul, map_sub, ← toEuclideanLin_mul_apply, Matrix.mul_assoc]
  rw [hr, h2, sub_eq_zero] at key
  exact key.symm

end Weighted

/-! ### Real weights: the derivative of a residual in its own weight -/

section RealWeights

variable [DecidableEq m] {A : Matrix m n ℝ}

/-- The **residual of the weighted solution** as a function of the weights ([golub2013matrix]
§6.1.1, `r(δ)`): for real `A`, `b` and weights `w`, `b - A x_w` with
`x_w = (Aᵀ diag(w) A)⁻¹ Aᵀ diag(w) b`. The book's `D(δ)²` with its `k`-th weight perturbed to
`d_k² (1 + δ)` is `diagonal (Function.update (d²) k (d_k² (1 + δ)))`. -/
noncomputable def weightedResidual (A : Matrix m n ℝ) (b : m → ℝ) (w : m → ℝ) : m → ℝ :=
  b - A *ᵥ (weightedLeastSquaresOp (diagonal w) A *ᵥ b)

omit [DecidableEq n] [Fintype n] in
/-- The weighted Gram matrix of positive weights and a matrix of full column rank is positive
definite. -/
theorem posDef_conjTranspose_mul_diagonal_mul [Finite n] (hA : LinearIndependent ℝ Aᵀ)
    {u : m → ℝ} (hu : ∀ i, 0 < u i) : (Aᴴ * diagonal u * A).PosDef := by
  cases nonempty_fintype n
  exact (PosDef.diagonal hu).conjTranspose_mul_mul_same (mulVec_injective_iff.2 hA)

omit [Fintype m] [Fintype n] [DecidableEq n] in
/-- The diagonal matrix of a sum of weights. -/
private theorem diagonal_add_eq (u v : m → ℝ) : diagonal (u + v) = diagonal u + diagonal v :=
  (diagonal_add u v).symm

omit [Fintype m] in
/-- A single changed weight as an additive correction. -/
private theorem update_eq_add_single (w : m → ℝ) (k : m) (t : ℝ) :
    Function.update w k t = w + Pi.single k (t - w k) := by
  ext i
  by_cases hi : i = k
  · subst hi
    simp
  · simp [hi]

omit [Fintype n] [DecidableEq n] in
/-- A weight on one row gives a rank-one weighted Gram matrix: `Aᵀ diag(c e_k) A = c a_k a_kᵀ`. -/
private theorem conjTranspose_mul_diagonal_single_mul (A : Matrix m n ℝ) (k : m) (c : ℝ) :
    Aᴴ * diagonal (Pi.single k c) * A = c • vecMulVec (A k) (A k) := by
  ext i j
  rw [mul_apply, Finset.sum_eq_single k]
  · simp [mul_diagonal, vecMulVec_apply]
    ring
  · intro x _ hx
    simp [mul_diagonal, hx]
  · simp

omit [DecidableEq n] in
/-- Changing one weight changes the weighted Gram matrix by a rank-one term:
`Aᵀ diag(w[k ↦ t]) A y = Aᵀ diag(w) A y + (t - w_k) (a_kᵀ y) a_k`. -/
private theorem gram_update_mulVec (A : Matrix m n ℝ) (w : m → ℝ) (k : m) (t : ℝ) (y : n → ℝ) :
    (Aᴴ * diagonal (Function.update w k t) * A) *ᵥ y
      = (Aᴴ * diagonal w * A) *ᵥ y + ((t - w k) * (A k ⬝ᵥ y)) • A k := by
  rw [update_eq_add_single, diagonal_add_eq,
    Matrix.mul_add, Matrix.add_mul, add_mulVec,
    conjTranspose_mul_diagonal_single_mul, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
    smul_smul]

omit [Fintype n] [DecidableEq n] in
/-- Changing one weight changes the weighted right-hand side by a multiple of the row:
`Aᵀ diag(w[k ↦ t]) b = Aᵀ diag(w) b + (t - w_k) b_k a_k`. -/
private theorem rhs_update_mulVec (A : Matrix m n ℝ) (w : m → ℝ) (k : m) (t : ℝ) (b : m → ℝ) :
    (Aᴴ * diagonal (Function.update w k t)) *ᵥ b
      = (Aᴴ * diagonal w) *ᵥ b + ((t - w k) * b k) • A k := by
  rw [update_eq_add_single, diagonal_add_eq,
    Matrix.mul_add, add_mulVec]
  congr 1
  ext j
  rw [mulVec, dotProduct, Finset.sum_eq_single k]
  · simp [mul_diagonal]
    ring
  · intro x _ hx
    simp [mul_diagonal, hx]
  · simp

/-- The weighted solution, unfolded as the solution of its normal equations. -/
private theorem weightedLeastSquaresOp_diagonal_mulVec (A : Matrix m n ℝ) (u b : m → ℝ) :
    weightedLeastSquaresOp (diagonal u) A *ᵥ b
      = (Aᴴ * diagonal u * A)⁻¹ *ᵥ ((Aᴴ * diagonal u) *ᵥ b) := by
  simp only [weightedLeastSquaresOp, mulVec_mulVec, Matrix.mul_assoc]

/-- **The residual as a function of one weight** (the Sherman–Morrison computation behind
[golub2013matrix] (6.1.4)): if both weighted Gram matrices are invertible,
`r_k(w[k ↦ t]) (1 + (t - w_k) a_kᵀ (Aᵀ diag(w) A)⁻¹ a_k) = r_k(w)`. -/
theorem weightedResidual_update_mul {w : m → ℝ} {k : m} {t : ℝ}
    (hM : IsUnit (Aᴴ * diagonal w * A)) (hMt : IsUnit (Aᴴ * diagonal (Function.update w k t) * A))
    (b : m → ℝ) :
    weightedResidual A b (Function.update w k t) k *
        (1 + (t - w k) * (A k ⬝ᵥ ((Aᴴ * diagonal w * A)⁻¹ *ᵥ A k))) =
      weightedResidual A b w k := by
  have hdM : IsUnit (Aᴴ * diagonal w * A).det := (isUnit_iff_isUnit_det _).1 hM
  have hdMt : IsUnit (Aᴴ * diagonal (Function.update w k t) * A).det :=
    (isUnit_iff_isUnit_det _).1 hMt
  set y := weightedLeastSquaresOp (diagonal (Function.update w k t)) A *ᵥ b with hy_def
  set x := weightedLeastSquaresOp (diagonal w) A *ᵥ b with hx_def
  have hx : x = ((Aᴴ * diagonal w * A)⁻¹ * (Aᴴ * diagonal w)) *ᵥ b := by
    rw [hx_def, weightedLeastSquaresOp_diagonal_mulVec, mulVec_mulVec]
  have hy : (Aᴴ * diagonal (Function.update w k t) * A) *ᵥ y
      = (Aᴴ * diagonal (Function.update w k t)) *ᵥ b := by
    rw [hy_def, weightedLeastSquaresOp_diagonal_mulVec, mulVec_mulVec, mul_nonsing_inv _ hdMt,
      one_mulVec]
  rw [gram_update_mulVec, rhs_update_mulVec] at hy
  have h3 := congrArg (fun v => A k ⬝ᵥ ((Aᴴ * diagonal w * A)⁻¹ *ᵥ v)) hy
  simp only [mulVec_add, mulVec_smul, mulVec_mulVec, nonsing_inv_mul _ hdM, one_mulVec,
    dotProduct_add, dotProduct_smul, smul_eq_mul, ← hx] at h3
  have hAy : (A *ᵥ y) k = A k ⬝ᵥ y := rfl
  have hAx : (A *ᵥ x) k = A k ⬝ᵥ x := rfl
  simp only [weightedResidual, Pi.sub_apply, ← hy_def, ← hx_def, hAy, hAx]
  linear_combination -h3

/-- **The derivative of a residual in its own weight** ([golub2013matrix] (6.1.4)): for real `A`
of full column rank and positive weights `w`, with `W = diag(w)`,
`d/dt r_k(w[k ↦ t]) = -(a_kᵀ (Aᵀ W A)⁻¹ a_k) r_k(w)` at `t = w_k` (`a_kᵀ = A k` the `k`-th row).
The book's `d/dδ` carries the extra factor `d_k²` of the chain rule through `δ ↦ d_k² (1 + δ)`.

Near `w_k`, `r_k(w[k ↦ t]) = r_k(w) / (1 + (t - w_k) a_kᵀ (Aᵀ W A)⁻¹ a_k)`
(`Matrix.weightedResidual_update_mul`), whose derivative at `w_k` is the claim. -/
theorem hasDerivAt_weightedResidual (hA : LinearIndependent ℝ Aᵀ) {w : m → ℝ}
    (hw : ∀ i, 0 < w i) (b : m → ℝ) (k : m) :
    HasDerivAt (fun t => weightedResidual A b (Function.update w k t) k)
      (-(A k ⬝ᵥ ((Aᵀ * diagonal w * A)⁻¹ *ᵥ A k)) * weightedResidual A b w k) (w k) := by
  have hAT : Aᴴ = Aᵀ := conjTranspose_eq_transpose_of_trivial A
  set c := A k ⬝ᵥ ((Aᵀ * diagonal w * A)⁻¹ *ᵥ A k)
  set r := weightedResidual A b w k
  have hM : IsUnit (Aᴴ * diagonal w * A) := (posDef_conjTranspose_mul_diagonal_mul hA hw).isUnit
  have h1 : HasDerivAt (fun t : ℝ => 1 + (t - w k) * c) c (w k) := by
    have := (((hasDerivAt_id' (w k)).sub_const (w k)).mul_const c).const_add 1
    simpa using this
  have hf : HasDerivAt (fun t => r * (1 + (t - w k) * c)⁻¹) (-c * r) (w k) := by
    have h2 := (h1.inv (by simp)).const_mul r
    refine h2.congr_deriv ?_
    simp only [sub_self, zero_mul, add_zero, one_pow, div_one]
    ring
  refine hf.congr_of_eventuallyEq ?_
  have hev1 : ∀ᶠ t in nhds (w k), 0 < t := eventually_gt_nhds (hw k)
  have hev2 : ∀ᶠ t in nhds (w k), 1 + (t - w k) * c ≠ 0 :=
    h1.continuousAt.eventually_ne (by simp)
  filter_upwards [hev1, hev2] with t ht hne
  have hu : ∀ i, 0 < Function.update w k t i := fun i => by
    by_cases hi : i = k
    · rw [hi, Function.update_self]
      exact ht
    · rw [Function.update_of_ne hi]
      exact hw i
  have hMt := (posDef_conjTranspose_mul_diagonal_mul hA hu).isUnit
  have key := weightedResidual_update_mul hM hMt b
  rw [hAT] at key
  rw [eq_mul_inv_iff_mul_eq₀ hne]
  exact key

/-- **Raising a weight never increases its residual** ([golub2013matrix] §6.1.1, "`|r_k(δ)|` is a
monotone decreasing function of `δ`"): for real `A` of full column rank and positive weights,
`t ↦ |r_k(w[k ↦ t])|` is antitone on `t > 0`. The derivative of `r_k²` is
`-2 (a_kᵀ M⁻¹ a_k) r_k² ≤ 0` (`Matrix.hasDerivAt_weightedResidual`, `M⁻¹` positive definite). The
book's strict decrease fails when `a_k = 0` or `r_k = 0` (then `r_k` is constant), and is not
claimed. -/
theorem antitoneOn_abs_weightedResidual (hA : LinearIndependent ℝ Aᵀ) {w : m → ℝ}
    (hw : ∀ i, 0 < w i) (b : m → ℝ) (k : m) :
    AntitoneOn (fun t => |weightedResidual A b (Function.update w k t) k|) (Set.Ioi 0) := by
  have hAT : Aᴴ = Aᵀ := conjTranspose_eq_transpose_of_trivial A
  set f : ℝ → ℝ := fun t => weightedResidual A b (Function.update w k t) k
  have hpos : ∀ t, 0 < t → ∀ i, 0 < Function.update w k t i := fun t ht i => by
    by_cases hi : i = k
    · rw [hi, Function.update_self]
      exact ht
    · rw [Function.update_of_ne hi]
      exact hw i
  have hderiv : ∀ t, 0 < t → HasDerivAt f
      (-(A k ⬝ᵥ ((Aᵀ * diagonal (Function.update w k t) * A)⁻¹ *ᵥ A k)) * f t) t := by
    intro t ht
    have h := hasDerivAt_weightedResidual hA (hpos t ht) b k
    simp only [Function.update_idem, Function.update_self] at h
    exact h
  have hc : ∀ t, 0 < t → 0 ≤ A k ⬝ᵥ ((Aᵀ * diagonal (Function.update w k t) * A)⁻¹ *ᵥ A k) := by
    intro t ht
    have hP := (posDef_conjTranspose_mul_diagonal_mul hA (hpos t ht)).inv.posSemidef
    rw [hAT] at hP
    simpa using hP.dotProduct_mulVec_nonneg (A k)
  have hsq : AntitoneOn (fun t => f t * f t) (Set.Ioi 0) := by
    have hd : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun t => f t * f t)
        (-(A k ⬝ᵥ ((Aᵀ * diagonal (Function.update w k t) * A)⁻¹ *ᵥ A k)) * f t * f t +
          f t * (-(A k ⬝ᵥ ((Aᵀ * diagonal (Function.update w k t) * A)⁻¹ *ᵥ A k)) * f t)) t :=
      fun t ht => (hderiv t ht).mul (hderiv t ht)
    refine antitoneOn_of_deriv_nonpos (convex_Ioi 0)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      fun t ht => ?_
    rw [interior_Ioi] at ht
    rw [(hd t ht).deriv]
    nlinarith [mul_nonneg (hc t ht) (mul_self_nonneg (f t))]
  intro s hs t ht hst
  exact sq_le_sq.1 (by simpa only [sq] using hsq hs ht hst)

end RealWeights

/-! ### Generalized least squares -/

section Generalized

variable {l : Type*} [Fintype l] [DecidableEq l]

/-- **The generalized least-squares problem** ([golub2013matrix] (6.1.8), after Paige): the pair
`(x, v)` solves `min ‖v‖` subject to `b = A x + B v`. It is defined for rank-deficient `A` and `B`,
which is its point; for a nonsingular `B` it is the weighted problem with weight factor `B⁻¹`
(`Matrix.isGeneralizedLeastSquaresSolution_iff`). -/
structure IsGeneralizedLeastSquaresSolution (A : Matrix m n 𝕜) (B : Matrix m l 𝕜)
    (b : EuclideanSpace 𝕜 m) (x : EuclideanSpace 𝕜 n) (v : EuclideanSpace 𝕜 l) : Prop where
  /-- The pair is feasible. -/
  eq_add : b = toEuclideanLin A x + toEuclideanLin B v
  /-- Every feasible pair has a noise vector at least as long. -/
  norm_le : ∀ x' v', b = toEuclideanLin A x' + toEuclideanLin B v' → ‖v‖ ≤ ‖v'‖

variable [DecidableEq m]

/-- **For a nonsingular `B` the generalized problem is the weighted one** ([golub2013matrix] §6.1.2,
(6.1.7) is (6.1.8)): feasibility forces `v = B⁻¹ (b - A x)`, so the objective is
`‖B⁻¹ (A x - b)‖`. -/
theorem isGeneralizedLeastSquaresSolution_iff {A : Matrix m n 𝕜} {B : Matrix m m 𝕜}
    (hB : IsUnit B) {b : EuclideanSpace 𝕜 m} {x : EuclideanSpace 𝕜 n} {v : EuclideanSpace 𝕜 m} :
    IsGeneralizedLeastSquaresSolution A B b x v ↔
      IsLeastSquaresSolution (B⁻¹ * A) (toEuclideanLin B⁻¹ b) x ∧
        v = toEuclideanLin B⁻¹ (b - toEuclideanLin A x) := by
  have hfeas : ∀ x' v', b = toEuclideanLin A x' + toEuclideanLin B v' ↔
      v' = toEuclideanLin B⁻¹ (b - toEuclideanLin A x') := fun x' v' => by
    constructor
    · intro h
      rw [h, add_sub_cancel_left, toEuclideanLin_nonsing_inv_mul_apply hB]
    · intro h
      rw [h, toEuclideanLin_mul_nonsing_inv_apply hB, add_sub_cancel]
  have hnorm : ∀ x', ‖toEuclideanLin B⁻¹ (b - toEuclideanLin A x')‖ =
      ‖toEuclideanLin (B⁻¹ * A) x' - toEuclideanLin B⁻¹ b‖ := fun x' => by
    rw [map_sub, toEuclideanLin_mul_apply, norm_sub_rev]
  constructor
  · rintro ⟨hfe, hmin⟩
    have hv := (hfeas x v).1 hfe
    refine ⟨fun y => ?_, hv⟩
    rw [← hnorm, ← hnorm, ← hv]
    exact hmin y _ ((hfeas y _).2 rfl)
  · rintro ⟨hls, hv⟩
    refine ⟨(hfeas x v).2 hv, fun x' v' h' => ?_⟩
    rw [hv, (hfeas x' v').1 h', hnorm, hnorm]
    exact hls x'

end Generalized

/-! ### Paige's method -/

section Paige

variable {p q : ℕ}

/-- A product split along the first `p` and the last `q` indices of `Fin (p + q)`. -/
private theorem mul_eq_add_submatrix {l l' : Type*} (X : Matrix l (Fin (p + q)) 𝕜)
    (Y : Matrix (Fin (p + q)) l' 𝕜) :
    X * Y = X.submatrix id (Fin.castAdd q) * Y.submatrix (Fin.castAdd q) id
      + X.submatrix id (Fin.natAdd p) * Y.submatrix (Fin.natAdd p) id := by
  ext i j
  simp only [mul_apply, add_apply, submatrix_apply, id, Fin.sum_univ_add]

/-- Two column blocks of a unitary matrix: `(U(:, f))ᴴ U(:, g)` is the corresponding block of the
identity. -/
private theorem conjTranspose_submatrix_mul_submatrix {X : Matrix (Fin (p + q)) (Fin (p + q)) 𝕜}
    (hX : X ∈ unitaryGroup (Fin (p + q)) 𝕜) {r s : Type*} (f : r → Fin (p + q))
    (g : s → Fin (p + q)) :
    (X.submatrix id f)ᴴ * X.submatrix id g =
      (1 : Matrix (Fin (p + q)) (Fin (p + q)) 𝕜).submatrix f g := by
  rw [← mem_unitaryGroup_iff'.1 hX]
  ext i j
  simp only [mul_apply, submatrix_apply, conjTranspose_apply, star_apply, id]

/-- The column blocks of a unitary matrix resolve the identity: `U₁ U₁ᴴ + U₂ U₂ᴴ = 1`. -/
private theorem submatrix_mul_conjTranspose_add {X : Matrix (Fin (p + q)) (Fin (p + q)) 𝕜}
    (hX : X ∈ unitaryGroup (Fin (p + q)) 𝕜) :
    X.submatrix id (Fin.castAdd q) * (X.submatrix id (Fin.castAdd q))ᴴ
      + X.submatrix id (Fin.natAdd p) * (X.submatrix id (Fin.natAdd p))ᴴ = 1 := by
  rw [← mem_unitaryGroup_iff.1 hX, star_eq_conjTranspose, mul_eq_add_submatrix X Xᴴ,
    conjTranspose_submatrix, conjTranspose_submatrix]

/-- The trailing block of the identity against the leading one vanishes. -/
private theorem one_submatrix_natAdd_castAdd :
    (1 : Matrix (Fin (p + q)) (Fin (p + q)) 𝕜).submatrix (Fin.natAdd p) (Fin.castAdd q) = 0 := by
  ext i j
  rw [submatrix_apply, one_apply_ne, zero_apply]
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_natAdd, Fin.val_castAdd] at this
  have := j.isLt
  omega

/-- **Paige's method for the generalized least-squares problem** ([golub2013matrix]
(6.1.9)–(6.1.10)): let `A = Q R` be a full QR factorization of `A ∈ 𝕜^{(p+q) × p}`, with
`Q = [Q₁ Q₂]` split `p | q` and `R₁` the leading `p × p` block of `R`; let `Z = [Z₁ Z₂]` (split
`p | q`) be unitary with
`Q₂ᴴ B Z = [0 S]`, `S` nonsingular. If `S u = Q₂ᴴ b` and `R₁ x = Q₁ᴴ b - Q₁ᴴ B Z₂ u`, then
`(x, Z₂ u)` solves the generalized problem `min ‖v‖` subject to `b = A x + B v`.

The book computes `Z` from an RQ factorization, so that `S` is upper triangular, and assumes `B`
nonsingular and `A` of full column rank to make `S` and `R₁` nonsingular; the statement uses only
what the proof does. Feasibility is checked on the two blocks of `Qᴴ (A x + B v)`; minimality: a
feasible `(x', v')` has `S (Z₂ᴴ v') = Q₂ᴴ b`, so `Z₂ᴴ v' = u` and
`‖v'‖ ≥ ‖Z₂ᴴ v'‖ = ‖u‖ = ‖Z₂ u‖`. -/
theorem isGeneralizedLeastSquaresSolution_of_paige {A : Matrix (Fin (p + q)) (Fin p) 𝕜}
    {Q : Matrix (Fin (p + q)) (Fin (p + q)) 𝕜} {R : Matrix (Fin (p + q)) (Fin p) 𝕜}
    (hQR : IsQR A Q R) {B Z : Matrix (Fin (p + q)) (Fin (p + q)) 𝕜}
    (hZ : Z ∈ unitaryGroup (Fin (p + q)) 𝕜) {S : Matrix (Fin q) (Fin q) 𝕜} (hS : IsUnit S)
    (hZ₁ : (Q.submatrix id (Fin.natAdd p))ᴴ * B * Z.submatrix id (Fin.castAdd q) = 0)
    (hZ₂ : (Q.submatrix id (Fin.natAdd p))ᴴ * B * Z.submatrix id (Fin.natAdd p) = S)
    {b : EuclideanSpace 𝕜 (Fin (p + q))} {u : EuclideanSpace 𝕜 (Fin q)}
    {x : EuclideanSpace 𝕜 (Fin p)}
    (hu : toEuclideanLin S u = toEuclideanLin (Q.submatrix id (Fin.natAdd p))ᴴ b)
    (hx : toEuclideanLin (firstRows R (Nat.le_add_right p q)) x =
      toEuclideanLin (firstColumns Q (Nat.le_add_right p q))ᴴ b -
        toEuclideanLin ((firstColumns Q (Nat.le_add_right p q))ᴴ * B *
          Z.submatrix id (Fin.natAdd p)) u) :
    IsGeneralizedLeastSquaresSolution A B b x
      (toEuclideanLin (Z.submatrix id (Fin.natAdd p)) u) := by
  have hQ := hQR.mem_unitaryGroup
  set Q₁ := firstColumns Q (Nat.le_add_right p q) with hQ₁
  set Q₂ := Q.submatrix id (Fin.natAdd p) with hQ₂
  set Z₁ := Z.submatrix id (Fin.castAdd q) with hZ₁def
  set Z₂ := Z.submatrix id (Fin.natAdd p) with hZ₂def
  set R₁ := firstRows R (Nat.le_add_right p q) with hR₁
  have hQ₁' : Q₁ = Q.submatrix id (Fin.castAdd q) := rfl
  have hA : A = Q₁ * R₁ := (hQR.firstColumns_mul_firstRows (Nat.le_add_right p q)).symm
  have hQ₁Q₁ : Q₁ᴴ * Q₁ = 1 := hQR.conjTranspose_firstColumns_mul_self (Nat.le_add_right p q)
  have hQ₂Q₁ : Q₂ᴴ * Q₁ = 0 := by
    rw [hQ₁', hQ₂, conjTranspose_submatrix_mul_submatrix hQ, one_submatrix_natAdd_castAdd]
  have hQ₁A : Q₁ᴴ * A = R₁ := by rw [hA, ← Matrix.mul_assoc, hQ₁Q₁, Matrix.one_mul]
  have hQ₂A : Q₂ᴴ * A = 0 := by rw [hA, ← Matrix.mul_assoc, hQ₂Q₁, Matrix.zero_mul]
  have hZ₂Z₂ : Z₂ᴴ * Z₂ = 1 := by
    rw [hZ₂def, conjTranspose_submatrix_mul_submatrix hZ]
    exact submatrix_one _ (fun a b hab => by simpa [Fin.ext_iff] using hab)
  -- the resolutions of the identity by the column blocks
  have hsplit : ∀ {X : Matrix (Fin (p + q)) (Fin (p + q)) 𝕜}, X ∈ unitaryGroup (Fin (p + q)) 𝕜 →
      ∀ w, w = toEuclideanLin (X.submatrix id (Fin.castAdd q))
          (toEuclideanLin (X.submatrix id (Fin.castAdd q))ᴴ w)
        + toEuclideanLin (X.submatrix id (Fin.natAdd p))
          (toEuclideanLin (X.submatrix id (Fin.natAdd p))ᴴ w) := by
    intro X hX w
    rw [← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply, ← LinearMap.add_apply, ← map_add,
      submatrix_mul_conjTranspose_add hX, toEuclideanLin_one_apply]
  refine ⟨?_, fun x' v' h' => ?_⟩
  · -- feasibility, block by block
    set y := toEuclideanLin A x + toEuclideanLin B (toEuclideanLin Z₂ u) with hy
    have e1 : toEuclideanLin Q₁ᴴ (toEuclideanLin B (toEuclideanLin Z₂ u)) =
        toEuclideanLin (Q₁ᴴ * B * Z₂) u := by
      rw [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply]
    have e2 : toEuclideanLin Q₂ᴴ (toEuclideanLin B (toEuclideanLin Z₂ u)) =
        toEuclideanLin (Q₂ᴴ * B * Z₂) u := by
      rw [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply]
    have h1 : toEuclideanLin Q₁ᴴ y = toEuclideanLin Q₁ᴴ b := by
      rw [hy, map_add, e1, ← toEuclideanLin_mul_apply Q₁ᴴ A x, hQ₁A, hx, sub_add_cancel]
    have h2 : toEuclideanLin Q₂ᴴ y = toEuclideanLin Q₂ᴴ b := by
      rw [hy, map_add, e2, hZ₂, hu, ← toEuclideanLin_mul_apply Q₂ᴴ A x, hQ₂A,
        toEuclideanLin_zero_apply, zero_add]
    calc b = toEuclideanLin Q₁ (toEuclideanLin Q₁ᴴ b) + toEuclideanLin Q₂ (toEuclideanLin Q₂ᴴ b) :=
          hsplit hQ b
      _ = toEuclideanLin Q₁ (toEuclideanLin Q₁ᴴ y) + toEuclideanLin Q₂ (toEuclideanLin Q₂ᴴ y) := by
          rw [h1, h2]
      _ = y := (hsplit hQ y).symm
  · -- minimality
    have e : toEuclideanLin Q₂ᴴ b = toEuclideanLin (Q₂ᴴ * B) v' := by
      rw [h', map_add, ← toEuclideanLin_mul_apply Q₂ᴴ A x', hQ₂A, toEuclideanLin_zero_apply,
        zero_add, toEuclideanLin_mul_apply]
    have e3 : toEuclideanLin (Q₂ᴴ * B) v' = toEuclideanLin S (toEuclideanLin Z₂ᴴ v') := by
      conv_lhs => rw [hsplit hZ v']
      rw [map_add, ← toEuclideanLin_mul_apply (Q₂ᴴ * B) Z₁,
        ← toEuclideanLin_mul_apply (Q₂ᴴ * B) Z₂, hZ₁, hZ₂, toEuclideanLin_zero_apply, zero_add]
    have hSv : toEuclideanLin S (toEuclideanLin Z₂ᴴ v') = toEuclideanLin S u := by
      rw [hu, e, e3]
    have hZv : toEuclideanLin Z₂ᴴ v' = u := by
      have := congrArg (toEuclideanLin S⁻¹) hSv
      rwa [toEuclideanLin_nonsing_inv_mul_apply hS, toEuclideanLin_nonsing_inv_mul_apply hS]
        at this
    have hnormv : ‖toEuclideanLin Z₂ u‖ = ‖u‖ :=
      (toEuclideanLinearIsometry hZ₂Z₂).norm_map u
    have hle : ‖toEuclideanLin Z₂ᴴ v'‖ ≤ ‖v'‖ := by
      have hZs : Zᴴ ∈ unitaryGroup (Fin (p + q)) 𝕜 := by
        rw [← star_eq_conjTranspose]
        exact Unitary.star_mem hZ
      rw [← norm_toEuclideanLin_apply_of_mem_unitaryGroup hZs v']
      refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_add]
      exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    rw [hnormv, ← hZv]
    exact hle

end Paige

/-! ### Column weighting -/

section ColumnWeighting

/-- **Column weighting** ([golub2013matrix] §6.1.3): for an invertible `G`, `y` is a least-squares
solution of `A G⁻¹ y = b` iff `G⁻¹ y` is one of `A x = b`; the change of variables `x = G⁻¹ y` is a
bijection. -/
theorem isLeastSquaresSolution_mul_inv_iff {A : Matrix m n 𝕜} {G : Matrix n n 𝕜} (hG : IsUnit G)
    {b : EuclideanSpace 𝕜 m} {y : EuclideanSpace 𝕜 n} :
    IsLeastSquaresSolution (A * G⁻¹) b y ↔ IsLeastSquaresSolution A b (toEuclideanLin G⁻¹ y) := by
  simp only [isLeastSquaresSolution_iff, toEuclideanLin_mul_apply]
  constructor
  · intro h x'
    have := h (toEuclideanLin G x')
    rwa [toEuclideanLin_nonsing_inv_mul_apply hG] at this
  · intro h y'
    exact h _

/-- **The column-weighted solution has least `G`-norm** ([golub2013matrix] §6.1.3, "within the set
of minimizers, `x_G` has the smallest `G`-norm", `‖z‖_G = ‖G z‖`): if `y` is the minimal-norm
least-squares solution of `A G⁻¹ y = b` and `x` is any least-squares solution of `A x = b`, then
`‖y‖ ≤ ‖G x‖`, that is `‖x_G‖_G ≤ ‖x‖_G` for `x_G = G⁻¹ y`. -/
theorem IsMinNormLeastSquaresSolution.norm_le_of_mul_inv {A : Matrix m n 𝕜} {G : Matrix n n 𝕜}
    (hG : IsUnit G) {b : EuclideanSpace 𝕜 m} {y x : EuclideanSpace 𝕜 n}
    (hy : IsMinNormLeastSquaresSolution (A * G⁻¹) b y) (hx : IsLeastSquaresSolution A b x) :
    ‖y‖ ≤ ‖toEuclideanLin G x‖ :=
  hy.2 _ ((isLeastSquaresSolution_mul_inv_iff hG).2
    (by rwa [toEuclideanLin_nonsing_inv_mul_apply hG]))

end ColumnWeighting

end Matrix
