import Numlib.Analysis.Matrix.SingularValues
import Numlib.Conditioning.LinearSystem

/-!
# Perturbation theory for least-squares problems

How the least-squares solution `x = A⁺ b` of a system with linearly independent columns, and its
residual `r = b - A x`, move when `A` and `b` are perturbed, and the same for the minimal-norm
solution of a system with linearly independent rows ([golub2013matrix] §5.3.6 Theorem 5.3.1,
§5.3.2 (5.3.4), §5.6.3 Theorem 5.6.1; [higham2002accuracy] Theorem 20.1).

## Main results

* `Matrix.leastSquares_sub_eq`, `Matrix.leastSquares_residual_sub_eq`: the exact perturbation
  identities `x̂ - x = Â⁺ (δb - δA x) + (Âᴴ Â)⁻¹ δAᴴ r` and
  `r̂ - r = (1 - Â Â⁺)(δb - δA x) - Â⁺ᴴ δAᴴ r`, `Â = A + δA`.
* `Matrix.norm_leastSquares_sub_le`, `Matrix.norm_leastSquares_residual_sub_le`: [golub2013matrix]
  Theorem 5.3.1 in rigorous form, with `σ_min(A) - ‖δA‖₂` in place of the book's `σ_min(A)` and no
  `O(ε²)` term.
* `Matrix.norm_normalEquations_sub_le`: the accuracy of the method of normal equations (5.3.4).
* `Matrix.mul_pinv_of_linearIndependent`: for linearly independent rows `A A⁺ = 1`, so the
  minimal-norm solution solves the system (`Matrix.toEuclideanLin_pinv_of_linearIndependent`).
* `Matrix.minNorm_sub_eq`, `Matrix.norm_minNorm_sub_le`: [golub2013matrix] Theorem 5.6.1 in
  rigorous form.
* `Matrix.hasDerivAt_pinv_mulVec_line`, `Matrix.hasDerivAt_minNorm_line`: the derivatives (5.3.15)
  and (5.6.2) that the book's first-order proofs use, over `ℝ`.

## Implementation notes

The book proves Theorems 5.3.1 and 5.6.1 by differentiating `t ↦ x(t)` at `0` and states them up to
`O(ε²)`. Here the exact identities are proved instead, and the bounds follow from the norms of the
pseudoinverse and of the inverse Gram matrix of `Â`
(`Matrix.l2_opNorm_pinv_eq_inv_iInf_colSingularValues`,
`Matrix.l2_opNorm_inv_conjTranspose_mul_self`),
together with Weyl's bound
`σ_min(A + δA) ≥ σ_min(A) - ‖δA‖₂` (`Matrix.iInf_colSingularValues_sub_le`), which also shows that
`A + δA` keeps independent columns. `σ_min` is the column-indexed `⨅ i, A.colSingularValues i`, the
least stretch of `A`. Vectors live in `EuclideanSpace`, matrices act through
`Matrix.toEuclideanLin`, and matrix norms are the scoped `Matrix.Norms.L2Operator` ones.

## References

* [golub2013matrix] G. H. Golub and C. F. Van Loan, *Matrix Computations*, 4th ed., §5.3, §5.6.
* [higham2002accuracy] N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
  Chapter 20.
-/

open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-! ### Stability of full column rank -/

section Stability

omit [DecidableEq m]

/-- **A positive least stretch makes the columns independent**: if `σ_min(A) > 0` then
`A x = 0` forces `x = 0`. -/
theorem linearIndependent_transpose_of_iInf_colSingularValues_pos {A : Matrix m n 𝕜}
    (h : 0 < ⨅ i, A.colSingularValues i) : LinearIndependent 𝕜 Aᵀ := by
  rcases isEmpty_or_nonempty n with hn | hn
  · rw [Real.iInf_of_isEmpty] at h
    exact absurd h (lt_irrefl 0)
  refine mulVec_injective_iff.1 fun v w hvw => ?_
  have h1 := A.iInf_colSingularValues_mul_norm_le (WithLp.toLp 2 (v - w))
  rw [toEuclideanLin_toLp, mulVec_sub, hvw, sub_self, WithLp.toLp_zero, norm_zero] at h1
  have h2 : ‖(WithLp.toLp 2 (v - w) : EuclideanSpace 𝕜 n)‖ = 0 :=
    le_antisymm (nonpos_of_mul_nonpos_right h1 h) (norm_nonneg _)
  have h3 := congrArg WithLp.ofLp (norm_eq_zero.1 h2)
  simpa [sub_eq_zero] using h3

/-- **Linearly independent columns give a positive least stretch**: `σ_min(A) > 0`, the converse
of `Matrix.linearIndependent_transpose_of_iInf_colSingularValues_pos`. -/
theorem iInf_colSingularValues_pos_of_linearIndependent [Nonempty n] {A : Matrix m n 𝕜}
    (hA : LinearIndependent 𝕜 Aᵀ) : 0 < ⨅ i, A.colSingularValues i := by
  obtain ⟨x, hx1, hx⟩ := A.exists_norm_eq_iInf_colSingularValues
  rw [← hx]
  refine norm_pos_iff.2 fun h0 => ?_
  have h1 : A *ᵥ WithLp.ofLp x = A *ᵥ 0 := by
    rw [mulVec_zero]
    exact congrArg WithLp.ofLp h0
  have h2 := mulVec_injective_iff.2 hA h1
  have hx0 : x = 0 := by
    ext i
    simpa using congrFun h2 i
  rw [hx0, norm_zero] at hx1
  exact zero_ne_one hx1

/-- **Weyl stability of the least stretch** ([golub2013matrix] Corollary 2.4.4):
`σ_min(A) - ‖δA‖₂ ≤ σ_min(A + δA)`. -/
theorem sub_l2_opNorm_le_iInf_colSingularValues_add [Nonempty n] (A δA : Matrix m n 𝕜) :
    (⨅ i, A.colSingularValues i) - ‖δA‖ ≤ ⨅ i, (A + δA).colSingularValues i := by
  have h := iInf_colSingularValues_sub_le (A + δA) A
  rw [add_sub_cancel_left] at h
  linarith [neg_abs_le ((⨅ i, (A + δA).colSingularValues i) - ⨅ i, A.colSingularValues i)]

/-- A perturbation smaller than the least stretch cannot happen without columns: `‖δA‖ < σ_min(A)`
forces `n` to be nonempty, since `σ_min` of a matrix without columns is `0`. -/
theorem nonempty_of_l2_opNorm_lt_iInf_colSingularValues {A δA : Matrix m n 𝕜}
    (h : ‖δA‖ < ⨅ i, A.colSingularValues i) : Nonempty n := by
  by_contra hn
  rw [not_nonempty_iff] at hn
  rw [Real.iInf_of_isEmpty] at h
  exact absurd h (not_lt.2 (norm_nonneg _))

/-- **A small perturbation keeps the columns independent**: `‖δA‖₂ < σ_min(A)` implies that
`A + δA` has linearly independent columns ([golub2013matrix] Theorem 2.5.2's use in the proof of
Theorem 5.3.1). -/
theorem linearIndependent_transpose_add_of_l2_opNorm_lt {A δA : Matrix m n 𝕜}
    (h : ‖δA‖ < ⨅ i, A.colSingularValues i) : LinearIndependent 𝕜 (A + δA)ᵀ := by
  have := nonempty_of_l2_opNorm_lt_iInf_colSingularValues h
  exact linearIndependent_transpose_of_iInf_colSingularValues_pos
    ((sub_pos.2 h).trans_le (sub_l2_opNorm_le_iInf_colSingularValues_add A δA))

end Stability

/-! ### The full-rank least-squares problem -/

section FullColumnRank

variable {A δA : Matrix m n 𝕜} {b δb r r' : EuclideanSpace 𝕜 m} {x x' : EuclideanSpace 𝕜 n}

/-- The residual of the least-squares solution is orthogonal to the columns: `Aᴴ r = 0`. -/
private theorem toEuclideanLin_conjTranspose_residual (hx : x = toEuclideanLin A.pinv b) :
    toEuclideanLin Aᴴ (b - toEuclideanLin A x) = 0 := by
  rw [hx, map_sub, ← toEuclideanLin_mul_apply, normalEquations_pinv, sub_self]

/-- A left inverse undoes the matrix. -/
private theorem toEuclideanLin_pinv_apply_toEuclideanLin (hA : LinearIndependent 𝕜 Aᵀ)
    (z : EuclideanSpace 𝕜 n) : toEuclideanLin A.pinv (toEuclideanLin A z) = z := by
  rw [← toEuclideanLin_mul_apply, pinv_mul_self_of_linearIndependent hA, toEuclideanLin_one,
    LinearMap.id_apply]

/-- **The exact perturbation identity of the least-squares solution**: if `A` and `Â = A + δA` have
linearly independent columns, `x = A⁺ b`, `x̂ = Â⁺ (b + δb)` and `r = b - A x`, then
`x̂ - x = Â⁺ (δb - δA x) + (Âᴴ Â)⁻¹ δAᴴ r`. `Â⁺ Â = 1` gives `x̂ - x = Â⁺ (b + δb - Â x)`, which is
`Â⁺ (r + δb - δA x)`, and `Â⁺ r = (Âᴴ Â)⁻¹ Âᴴ r = (Âᴴ Â)⁻¹ δAᴴ r` because `Aᴴ r = 0`. -/
theorem leastSquares_sub_eq (hA' : LinearIndependent 𝕜 (A + δA)ᵀ)
    (hx : x = toEuclideanLin A.pinv b) (hx' : x' = toEuclideanLin (A + δA).pinv (b + δb))
    (hr : r = b - toEuclideanLin A x) :
    x' - x = toEuclideanLin (A + δA).pinv (δb - toEuclideanLin δA x) +
      toEuclideanLin (((A + δA)ᴴ * (A + δA))⁻¹ * δAᴴ) r := by
  have hAr : toEuclideanLin Aᴴ r = 0 := hr ▸ toEuclideanLin_conjTranspose_residual hx
  have hPr : toEuclideanLin (A + δA).pinv r =
      toEuclideanLin (((A + δA)ᴴ * (A + δA))⁻¹ * δAᴴ) r := by
    rw [pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose hA', toEuclideanLin_mul_apply,
      toEuclideanLin_mul_apply, conjTranspose_add, map_add, LinearMap.add_apply, hAr, zero_add]
  have hAx : toEuclideanLin (A + δA) x = toEuclideanLin A x + toEuclideanLin δA x := by
    rw [map_add, LinearMap.add_apply]
  calc x' - x = toEuclideanLin (A + δA).pinv (b + δb) -
        toEuclideanLin (A + δA).pinv (toEuclideanLin (A + δA) x) := by
        rw [hx', toEuclideanLin_pinv_apply_toEuclideanLin hA']
    _ = toEuclideanLin (A + δA).pinv (r + (δb - toEuclideanLin δA x)) := by
        rw [← map_sub, hAx, hr]
        congr 1
        abel
    _ = _ := by rw [map_add, hPr, add_comm]

/-- **The exact perturbation identity of the least-squares residual**: under the hypotheses of
`Matrix.leastSquares_sub_eq`, with `r̂ = (b + δb) - Â x̂`,
`r̂ - r = (1 - Â Â⁺)(δb - δA x) - Â⁺ᴴ δAᴴ r`. Apply `Â` to the identity for `x̂ - x`; `Â (Âᴴ Â)⁻¹`
is `Â⁺ᴴ`. -/
theorem leastSquares_residual_sub_eq (hA' : LinearIndependent 𝕜 (A + δA)ᵀ)
    (hx : x = toEuclideanLin A.pinv b) (hx' : x' = toEuclideanLin (A + δA).pinv (b + δb))
    (hr : r = b - toEuclideanLin A x) (hr' : r' = (b + δb) - toEuclideanLin (A + δA) x') :
    r' - r = toEuclideanLin (1 - (A + δA) * (A + δA).pinv) (δb - toEuclideanLin δA x) -
      toEuclideanLin ((A + δA).pinvᴴ * δAᴴ) r := by
  have hd := leastSquares_sub_eq hA' hx hx' hr
  set u := δb - toEuclideanLin δA x with hu
  have hx'' : x' = x + (toEuclideanLin (A + δA).pinv u +
      toEuclideanLin (((A + δA)ᴴ * (A + δA))⁻¹ * δAᴴ) r) := by
    rw [← hd]
    abel
  have hPH : (A + δA) * ((A + δA)ᴴ * (A + δA))⁻¹ = (A + δA).pinvᴴ := by
    have hH : (((A + δA)ᴴ * (A + δA))⁻¹)ᴴ = ((A + δA)ᴴ * (A + δA))⁻¹ :=
      (isHermitian_conjTranspose_mul_self (A + δA)).inv
    rw [pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose hA', conjTranspose_mul,
      conjTranspose_conjTranspose, hH]
  have hAQ : toEuclideanLin (A + δA)
      (toEuclideanLin (((A + δA)ᴴ * (A + δA))⁻¹ * δAᴴ) r) =
        toEuclideanLin ((A + δA).pinvᴴ * δAᴴ) r := by
    rw [toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply (A + δA), hPH,
      ← toEuclideanLin_mul_apply]
  have hbx : b + δb - toEuclideanLin (A + δA) x - r = u := by
    rw [hr, hu, map_add, LinearMap.add_apply]
    abel
  have hre : ∀ z w, b + δb - (toEuclideanLin (A + δA) x + (z + w)) - r =
      (b + δb - toEuclideanLin (A + δA) x - r) - z - w := fun z w => by abel
  rw [hr', hx'', LinearMap.map_add, LinearMap.map_add, hAQ, hre, hbx,
    show toEuclideanLin (1 - (A + δA) * (A + δA).pinv) =
      toEuclideanLin 1 - toEuclideanLin ((A + δA) * (A + δA).pinv) from map_sub _ _ _,
    LinearMap.sub_apply, toEuclideanLin_one, LinearMap.id_apply,
    toEuclideanLin_mul_apply (A + δA) (A + δA).pinv]

/-- **[golub2013matrix] Theorem 5.3.1 (solution), rigorous form**: if `A` has linearly independent
columns, `σ = σ_min(A)` and `‖δA‖₂ < σ`, then `A + δA` has linearly independent columns and, with
`x = A⁺ b`, `x̂ = (A + δA)⁺ (b + δb)` and `r = b - A x`,
`‖x̂ - x‖ ≤ (‖δb‖ + ‖δA‖₂ ‖x‖) / (σ - ‖δA‖₂) + ‖δA‖₂ ‖r‖ / (σ - ‖δA‖₂)²`. From
`Matrix.leastSquares_sub_eq`, `‖Â⁺‖₂ = 1/σ_min(Â)`, `‖(Âᴴ Â)⁻¹‖₂ = 1/σ_min(Â)²` and
`σ_min(Â) ≥ σ - ‖δA‖₂`. The book's (5.3.11) is the relative form of this bound with `σ` in place of
`σ - ‖δA‖₂`. -/
theorem norm_leastSquares_sub_le (hδA : ‖δA‖ < ⨅ i, A.colSingularValues i)
    (hx : x = toEuclideanLin A.pinv b) (hx' : x' = toEuclideanLin (A + δA).pinv (b + δb))
    (hr : r = b - toEuclideanLin A x) :
    LinearIndependent 𝕜 (A + δA)ᵀ ∧
      ‖x' - x‖ ≤ (‖δb‖ + ‖δA‖ * ‖x‖) / ((⨅ i, A.colSingularValues i) - ‖δA‖) +
        ‖δA‖ * ‖r‖ / ((⨅ i, A.colSingularValues i) - ‖δA‖) ^ 2 := by
  have := nonempty_of_l2_opNorm_lt_iInf_colSingularValues hδA
  set σ := ⨅ i, A.colSingularValues i with hσ
  have hσ' := sub_l2_opNorm_le_iInf_colSingularValues_add A δA
  have hd : 0 < σ - ‖δA‖ := sub_pos.2 hδA
  have hA' := linearIndependent_transpose_add_of_l2_opNorm_lt hδA
  refine ⟨hA', ?_⟩
  rw [leastSquares_sub_eq hA' hx hx' hr]
  have hP : ‖(A + δA).pinv‖ ≤ (σ - ‖δA‖)⁻¹ := by
    rw [l2_opNorm_pinv_eq_inv_iInf_colSingularValues hA']
    exact inv_anti₀ hd hσ'
  have hG : ‖((A + δA)ᴴ * (A + δA))⁻¹‖ ≤ (σ - ‖δA‖)⁻¹ ^ 2 := by
    rw [l2_opNorm_inv_conjTranspose_mul_self hA']
    exact pow_le_pow_left₀ (inv_nonneg.2 (hd.trans_le hσ').le) (inv_anti₀ hd hσ') 2
  have hu : ‖δb - toEuclideanLin δA x‖ ≤ ‖δb‖ + ‖δA‖ * ‖x‖ :=
    (norm_sub_le _ _).trans (add_le_add le_rfl (norm_toEuclideanLin_apply_le _ _))
  have hQ : ‖((A + δA)ᴴ * (A + δA))⁻¹ * δAᴴ‖ ≤ (σ - ‖δA‖)⁻¹ ^ 2 * ‖δA‖ := by
    refine (l2_opNorm_mul _ _).trans ?_
    rw [l2_opNorm_conjTranspose]
    exact mul_le_mul_of_nonneg_right hG (norm_nonneg _)
  calc ‖toEuclideanLin (A + δA).pinv (δb - toEuclideanLin δA x) +
        toEuclideanLin (((A + δA)ᴴ * (A + δA))⁻¹ * δAᴴ) r‖
      ≤ ‖(A + δA).pinv‖ * ‖δb - toEuclideanLin δA x‖ +
          ‖((A + δA)ᴴ * (A + δA))⁻¹ * δAᴴ‖ * ‖r‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_toEuclideanLin_apply_le _ _)
          (norm_toEuclideanLin_apply_le _ _))
    _ ≤ (σ - ‖δA‖)⁻¹ * (‖δb‖ + ‖δA‖ * ‖x‖) + (σ - ‖δA‖)⁻¹ ^ 2 * ‖δA‖ * ‖r‖ :=
        add_le_add (mul_le_mul hP hu (norm_nonneg _) (inv_nonneg.2 hd.le))
          (mul_le_mul_of_nonneg_right hQ (norm_nonneg _))
    _ = _ := by
        rw [div_eq_inv_mul, div_eq_inv_mul, inv_pow]
        ring

/-- **[golub2013matrix] Theorem 5.3.1 (residual), rigorous form**: under the hypotheses of
`Matrix.norm_leastSquares_sub_le`, with `r̂ = (b + δb) - (A + δA) x̂`,
`‖r̂ - r‖ ≤ ‖δb‖ + ‖δA‖₂ ‖x‖ + ‖δA‖₂ ‖r‖ / (σ - ‖δA‖₂)`. From
`Matrix.leastSquares_residual_sub_eq`, `‖1 - Â Â⁺‖₂ ≤ 1` and `‖Â⁺ᴴ‖₂ = ‖Â⁺‖₂`. The book's (5.3.12)
is its relative form. -/
theorem norm_leastSquares_residual_sub_le (hδA : ‖δA‖ < ⨅ i, A.colSingularValues i)
    (hx : x = toEuclideanLin A.pinv b) (hx' : x' = toEuclideanLin (A + δA).pinv (b + δb))
    (hr : r = b - toEuclideanLin A x) (hr' : r' = (b + δb) - toEuclideanLin (A + δA) x') :
    ‖r' - r‖ ≤ ‖δb‖ + ‖δA‖ * ‖x‖ + ‖δA‖ * ‖r‖ / ((⨅ i, A.colSingularValues i) - ‖δA‖) := by
  have := nonempty_of_l2_opNorm_lt_iInf_colSingularValues hδA
  set σ := ⨅ i, A.colSingularValues i with hσ
  have hσ' := sub_l2_opNorm_le_iInf_colSingularValues_add A δA
  have hd : 0 < σ - ‖δA‖ := sub_pos.2 hδA
  have hA' := linearIndependent_transpose_add_of_l2_opNorm_lt hδA
  rw [leastSquares_residual_sub_eq hA' hx hx' hr hr']
  have hP : ‖(A + δA).pinvᴴ‖ ≤ (σ - ‖δA‖)⁻¹ := by
    rw [l2_opNorm_conjTranspose, l2_opNorm_pinv_eq_inv_iInf_colSingularValues hA']
    exact inv_anti₀ hd hσ'
  have hu : ‖δb - toEuclideanLin δA x‖ ≤ ‖δb‖ + ‖δA‖ * ‖x‖ :=
    (norm_sub_le _ _).trans (add_le_add le_rfl (norm_toEuclideanLin_apply_le _ _))
  have hQ : ‖(A + δA).pinvᴴ * δAᴴ‖ ≤ (σ - ‖δA‖)⁻¹ * ‖δA‖ := by
    refine (l2_opNorm_mul _ _).trans ?_
    rw [l2_opNorm_conjTranspose δA]
    exact mul_le_mul_of_nonneg_right hP (norm_nonneg _)
  calc ‖toEuclideanLin (1 - (A + δA) * (A + δA).pinv) (δb - toEuclideanLin δA x) -
        toEuclideanLin ((A + δA).pinvᴴ * δAᴴ) r‖
      ≤ ‖1 - (A + δA) * (A + δA).pinv‖ * ‖δb - toEuclideanLin δA x‖ +
          ‖(A + δA).pinvᴴ * δAᴴ‖ * ‖r‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_toEuclideanLin_apply_le _ _)
          (norm_toEuclideanLin_apply_le _ _))
    _ ≤ 1 * (‖δb‖ + ‖δA‖ * ‖x‖) + (σ - ‖δA‖)⁻¹ * ‖δA‖ * ‖r‖ :=
        add_le_add (mul_le_mul (l2_opNorm_one_sub_mul_pinv_le_one _) hu (norm_nonneg _)
          zero_le_one) (mul_le_mul_of_nonneg_right hQ (norm_nonneg _))
    _ = _ := by
        rw [div_eq_inv_mul]
        ring

open scoped ComplexOrder in
/-- **The accuracy of the method of normal equations** ([golub2013matrix] (5.3.4)): if `A` has
linearly independent columns, `x = A⁺ b`, `(Aᴴ A + E) x̂ = Aᴴ b` with `‖E‖₂ ≤ η ‖Aᴴ A‖₂` and
`η κ₂(A)² < 1`, then `‖x̂ - x‖ / ‖x‖ ≤ η κ₂(A)² / (1 - η κ₂(A)²)`, `κ₂` the rectangular condition
number `Matrix.pinvCondNumberLp 2`. The linear-system bound `relative_error_le_norm_inverse` for
`Aᴴ A`, whose condition number is `κ₂(A)²` (`Matrix.pinvCondNumberLp_two_conjTranspose_mul_self`).
The book's "`≈ u κ₂(A)²`" is this with `η = c u` from the Cholesky backward error. -/
theorem norm_normalEquations_sub_le (hA : LinearIndependent 𝕜 Aᵀ) {E : Matrix n n 𝕜}
    {x y : EuclideanSpace 𝕜 n} (hx : x = toEuclideanLin A.pinv b)
    (hy : toEuclideanLin (Aᴴ * A + E) y = toEuclideanLin Aᴴ b) {η : ℝ}
    (hE : ‖E‖ ≤ η * ‖Aᴴ * A‖) (hη : η * pinvCondNumberLp 2 A ^ 2 < 1) (hx0 : x ≠ 0) :
    ‖y - x‖ / ‖x‖ ≤ η * pinvCondNumberLp 2 A ^ 2 / (1 - η * pinvCondNumberLp 2 A ^ 2) := by
  classical
  have hn : Nonempty n := by
    by_contra hn
    rw [not_nonempty_iff] at hn
    exact hx0 (by ext i; exact isEmptyElim i)
  set G := Aᴴ * A with hG
  have hGu : IsUnit G := (posDef_conjTranspose_mul_self_of_linearIndependent hA).isUnit
  have hu : IsUnit (toEuclideanCLM (n := n) (𝕜 := 𝕜) G) := hGu.map _
  set L := ContinuousLinearEquiv.unitsEquiv 𝕜 (EuclideanSpace 𝕜 n) hu.unit with hL
  have hLc : (L : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n) =
      toEuclideanCLM (n := n) (𝕜 := 𝕜) G := rfl
  have hLs : (L.symm : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n) =
      toEuclideanCLM (n := n) (𝕜 := 𝕜) G⁻¹ := by
    have h1 : (L.symm : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n) = ↑hu.unit⁻¹ := rfl
    rw [h1, ← Ring.inverse_unit, hu.unit_spec, toEuclideanCLM_nonsing_inv hGu]
  have hκ : ‖G⁻¹‖ * ‖G‖ = pinvCondNumberLp 2 A ^ 2 := by
    rw [← pinvCondNumberLp_two_conjTranspose_mul_self hA, pinvCondNumberLp, pinv_eq_inv hGu,
      lpOpNorm_two, lpOpNorm_two, mul_comm]
  have hxb : L x = toEuclideanLin Aᴴ b := by
    rw [← normalEquations_pinv, hx]
    rfl
  have hyb : ((L : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n) +
      toEuclideanCLM (n := n) (𝕜 := 𝕜) E) y =
      toEuclideanLin Aᴴ b + 0 := by
    rw [add_zero, ← hy, map_add, LinearMap.add_apply]
    rfl
  have hsmall : ‖(L.symm : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n)‖ *
      ‖toEuclideanCLM (n := n) (𝕜 := 𝕜) E‖ ≤ η * pinvCondNumberLp 2 A ^ 2 := by
    rw [hLs, l2_opNorm_toEuclideanCLM, l2_opNorm_toEuclideanCLM, ← hκ]
    have := mul_le_mul_of_nonneg_left hE (norm_nonneg G⁻¹)
    linarith
  have h := relative_error_le_norm_inverse L (toEuclideanCLM (n := n) (𝕜 := 𝕜) E) hxb hyb
    (hsmall.trans_lt hη) hx0
  rw [norm_zero, zero_div, zero_add] at h
  refine h.trans ?_
  set t := ‖(L.symm : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n)‖ *
    ‖toEuclideanCLM (n := n) (𝕜 := 𝕜) E‖ with ht
  have ht0 : 0 ≤ t := by positivity
  rw [← mul_div_right_comm, ← ht]
  exact div_le_div₀ (by linarith) hsmall (by linarith) (by linarith)

end FullColumnRank

/-! ### The minimal-norm solution of an underdetermined system -/

section FullRowRank

variable {A δA : Matrix m n 𝕜} {b δb : EuclideanSpace 𝕜 m} {x x' : EuclideanSpace 𝕜 n}

/-- A small perturbation keeps the rows independent: `‖δA‖₂ < σ_min(Aᴴ)` implies that `A + δA` has
linearly independent rows. The column statement for `Aᴴ`, through `star (y ᵥ* M) = Mᴴ *ᵥ star y`. -/
theorem linearIndependent_add_of_l2_opNorm_lt
    (h : ‖δA‖ < ⨅ i, Aᴴ.colSingularValues i) : LinearIndependent 𝕜 (A + δA) := by
  have h' : ‖δAᴴ‖ < ⨅ i, Aᴴ.colSingularValues i := by rwa [l2_opNorm_conjTranspose]
  have hc := linearIndependent_transpose_add_of_l2_opNorm_lt h'
  rw [← conjTranspose_add] at hc
  refine vecMul_injective_iff.1 fun v w hvw => ?_
  have h1 := congrArg star hvw
  rw [star_vecMul, star_vecMul] at h1
  exact star_injective (mulVec_injective_iff.2 hc h1)

open scoped ComplexOrder in
/-- For linearly independent rows the pseudoinverse is a right inverse, `A A⁺ = 1`: the dual of
`Matrix.pinv_mul_self_of_linearIndependent`, through `A⁺ = Aᴴ (A Aᴴ)⁻¹`. -/
theorem mul_pinv_of_linearIndependent (hA : LinearIndependent 𝕜 A) : A * A.pinv = 1 := by
  rw [pinv_eq_conjTranspose_mul_inv_self_mul_conjTranspose hA, ← Matrix.mul_assoc,
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp
      (posDef_self_mul_conjTranspose_of_linearIndependent hA).isUnit)]

/-- The minimal-norm solution solves the system: `A (A⁺ b) = b` for independent rows. -/
theorem toEuclideanLin_pinv_of_linearIndependent (hA : LinearIndependent 𝕜 A) :
    toEuclideanLin A (toEuclideanLin A.pinv b) = b := by
  rw [← toEuclideanLin_mul_apply, mul_pinv_of_linearIndependent hA, toEuclideanLin_one,
    LinearMap.id_apply]

/-- `A⁺ A` is `Aᴴ (Aᴴ)⁺`, so `1 - A⁺ A` is the projection onto the orthogonal complement of the
range of `Aᴴ`. -/
private theorem pinv_mul_self_eq_conjTranspose_mul_pinv (A : Matrix m n 𝕜) :
    A.pinv * A = Aᴴ * Aᴴ.pinv := by
  rw [pinv_conjTranspose, ← conjTranspose_mul, A.isHermitian_pinv_mul.eq]

/-- **The exact perturbation identity of the minimal-norm solution**: if `A` has linearly
independent rows, `x = A⁺ b` and `x̂ = Â⁺ (b + δb)` with `Â = A + δA`, then
`x̂ - x = Â⁺ (δb - δA x) + (1 - Â⁺ Â) δAᴴ (A Aᴴ)⁻¹ b`. With `y = (A Aᴴ)⁻¹ b`, `x = Aᴴ y` solves
`A x = b`, so `Â⁺ (δb - δA x) = x̂ - Â⁺ Â x`; and `(1 - Â⁺ Â) Âᴴ = 0` turns
`Â⁺ Â x - x = -(1 - Â⁺ Â)(Âᴴ - δAᴴ) y` into `(1 - Â⁺ Â) δAᴴ y`. (The sign of the second term is
`+`, as in the derivative (5.6.2).) -/
theorem minNorm_sub_eq (hA : LinearIndependent 𝕜 A) (hx : x = toEuclideanLin A.pinv b)
    (hx' : x' = toEuclideanLin (A + δA).pinv (b + δb)) :
    x' - x = toEuclideanLin (A + δA).pinv (δb - toEuclideanLin δA x) +
      toEuclideanLin ((1 - (A + δA).pinv * (A + δA)) * δAᴴ * (A * Aᴴ)⁻¹) b := by
  set y := toEuclideanLin (A * Aᴴ)⁻¹ b with hy
  have hxy : x = toEuclideanLin Aᴴ y := by
    rw [hx, pinv_eq_conjTranspose_mul_inv_self_mul_conjTranspose hA, toEuclideanLin_mul_apply]
  have hAx : toEuclideanLin A x = b := by
    rw [hx]
    exact toEuclideanLin_pinv_of_linearIndependent hA
  have hPA : toEuclideanLin (1 - (A + δA).pinv * (A + δA)) (toEuclideanLin (A + δA)ᴴ y) = 0 := by
    rw [← toEuclideanLin_mul_apply, Matrix.sub_mul, Matrix.one_mul,
      pinv_mul_self_mul_conjTranspose, sub_self, map_zero, LinearMap.zero_apply]
  have hδ : toEuclideanLin δAᴴ y = toEuclideanLin (A + δA)ᴴ y - x := by
    rw [hxy, conjTranspose_add, map_add, LinearMap.add_apply]
    abel
  have hsecond : toEuclideanLin ((1 - (A + δA).pinv * (A + δA)) * δAᴴ * (A * Aᴴ)⁻¹) b =
      toEuclideanLin (A + δA).pinv (toEuclideanLin (A + δA) x) - x := by
    rw [toEuclideanLin_mul_apply, ← hy, toEuclideanLin_mul_apply, hδ, LinearMap.map_sub, hPA,
      zero_sub, show toEuclideanLin (1 - (A + δA).pinv * (A + δA)) =
        toEuclideanLin 1 - toEuclideanLin ((A + δA).pinv * (A + δA)) from map_sub _ _ _,
      LinearMap.sub_apply, toEuclideanLin_one, LinearMap.id_apply, toEuclideanLin_mul_apply]
    abel
  have hres : b + δb - toEuclideanLin (A + δA) x = δb - toEuclideanLin δA x := by
    rw [map_add, LinearMap.add_apply, hAx]
    abel
  rw [hsecond, hx', ← hres, LinearMap.map_sub]
  abel

omit [DecidableEq n] in
/-- A positive least stretch of `Aᴴ` bounds `y` by `Aᴴ y`. -/
private theorem norm_le_of_iInf_colSingularValues_conjTranspose [Nonempty m]
    (h : 0 < ⨅ i, Aᴴ.colSingularValues i) (y : EuclideanSpace 𝕜 m) :
    ‖y‖ ≤ ‖toEuclideanLin Aᴴ y‖ / ⨅ i, Aᴴ.colSingularValues i := by
  rw [le_div_iff₀ h, mul_comm]
  exact Aᴴ.iInf_colSingularValues_mul_norm_le y

/-- **[golub2013matrix] Theorem 5.6.1, rigorous form**: if `A` has linearly independent rows,
`σ = σ_min(Aᴴ)` (the least singular value `σ_m`), `‖δA‖₂ < σ` and `b ≠ 0`, then `A + δA` has
linearly independent rows and, with `x = A⁺ b`, `x̂ = (A + δA)⁺ (b + δb)`, `ε_A = ‖δA‖₂/‖A‖₂` and
`ε_b = ‖δb‖/‖b‖`,
`‖x̂ - x‖ / ‖x‖ ≤ ‖A‖₂ / (σ - ‖δA‖₂) (ε_A + ε_b) + (κ₂(A) ε_A if m < n, else 0)`, `κ₂` the
rectangular condition number `Matrix.pinvCondNumberLp 2`. From `Matrix.minNorm_sub_eq`,
`‖Â⁺‖₂ ≤ 1/(σ - ‖δA‖₂)`, `‖1 - Â⁺ Â‖₂ ≤ 1` (and `= 0` for a square `A`),
`‖(A Aᴴ)⁻¹ b‖ ≤ ‖x‖/σ` and `‖b‖ ≤ ‖A‖₂ ‖x‖`. Its first-order form is the book's
`κ₂(A)(ε_A min{2, n - m + 1} + ε_b) + O(ε²)`. -/
theorem norm_minNorm_sub_le (hA : LinearIndependent 𝕜 A) (hδA : ‖δA‖ < ⨅ i, Aᴴ.colSingularValues i)
    (hb : b ≠ 0) (hx : x = toEuclideanLin A.pinv b)
    (hx' : x' = toEuclideanLin (A + δA).pinv (b + δb)) :
    LinearIndependent 𝕜 (A + δA) ∧
      ‖x' - x‖ / ‖x‖ ≤ ‖A‖ / ((⨅ i, Aᴴ.colSingularValues i) - ‖δA‖) * (‖δA‖ / ‖A‖ + ‖δb‖ / ‖b‖) +
        if Fintype.card m < Fintype.card n then pinvCondNumberLp 2 A * (‖δA‖ / ‖A‖) else 0 := by
  have hδA' : ‖δAᴴ‖ < ⨅ i, Aᴴ.colSingularValues i := by rwa [l2_opNorm_conjTranspose]
  have := nonempty_of_l2_opNorm_lt_iInf_colSingularValues hδA'
  set σ := ⨅ i, Aᴴ.colSingularValues i with hσ
  have hA'r := linearIndependent_add_of_l2_opNorm_lt hδA
  refine ⟨hA'r, ?_⟩
  have hd : 0 < σ - ‖δA‖ := sub_pos.2 hδA
  have hσ0 : 0 < σ := (norm_nonneg _).trans_lt hδA
  -- `x ≠ 0` and `A ≠ 0`
  have hAx : toEuclideanLin A x = b := by
    rw [hx]
    exact toEuclideanLin_pinv_of_linearIndependent hA
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hAx
    exact hb hAx.symm
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hbA : ‖b‖ ≤ ‖A‖ * ‖x‖ := hAx ▸ norm_toEuclideanLin_apply_le A x
  have hbn : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hAn : 0 < ‖A‖ := by
    by_contra h0
    have : ‖A‖ = 0 := le_antisymm (not_lt.1 h0) (norm_nonneg _)
    rw [this, zero_mul] at hbA
    linarith
  -- the pieces of the identity
  have hσ' : σ - ‖δA‖ ≤ ⨅ i, (A + δA)ᴴ.colSingularValues i := by
    rw [conjTranspose_add, ← l2_opNorm_conjTranspose δA]
    exact sub_l2_opNorm_le_iInf_colSingularValues_add Aᴴ δAᴴ
  have hc' : LinearIndependent 𝕜 (A + δA)ᴴᵀ := by
    rw [conjTranspose_add]
    exact linearIndependent_transpose_add_of_l2_opNorm_lt hδA'
  have hP : ‖(A + δA).pinv‖ ≤ (σ - ‖δA‖)⁻¹ := by
    rw [← l2_opNorm_conjTranspose, ← pinv_conjTranspose,
      l2_opNorm_pinv_eq_inv_iInf_colSingularValues hc']
    exact inv_anti₀ hd hσ'
  set y := toEuclideanLin (A * Aᴴ)⁻¹ b with hy
  have hxy : x = toEuclideanLin Aᴴ y := by
    rw [hx, pinv_eq_conjTranspose_mul_inv_self_mul_conjTranspose hA, toEuclideanLin_mul_apply]
  have hyx : ‖y‖ ≤ ‖x‖ / σ := by
    rw [hxy]
    exact norm_le_of_iInf_colSingularValues_conjTranspose hσ0 y
  -- the projection term
  set c : ℝ := if Fintype.card m < Fintype.card n then 1 else 0 with hc
  have hproj : ‖1 - (A + δA).pinv * (A + δA)‖ ≤ c := by
    rw [pinv_mul_self_eq_conjTranspose_mul_pinv, hc]
    split_ifs with hmn
    · exact l2_opNorm_one_sub_mul_pinv_le_one _
    · -- a square matrix with independent rows: the range of `Âᴴ` is everything
      have hle : Fintype.card m ≤ Fintype.card n := by
        simpa using hA'r.fintype_card_le_finrank
      have heq : Fintype.card m = Fintype.card n := le_antisymm hle (not_lt.1 hmn)
      have hinj : Function.Injective (toEuclideanLin (A + δA)ᴴ) := by
        intro v w hvw
        have := mulVec_injective_iff.2 hc' (show (A + δA)ᴴ *ᵥ WithLp.ofLp v =
          (A + δA)ᴴ *ᵥ WithLp.ofLp w from congrArg WithLp.ofLp hvw)
        exact WithLp.ofLp_injective 2 this
      have htop : LinearMap.range (toEuclideanLin (A + δA)ᴴ) = ⊤ :=
        Submodule.eq_top_of_finrank_eq (by
          rw [LinearMap.finrank_range_of_inj hinj, finrank_euclideanSpace,
            finrank_euclideanSpace, heq])
      have hz : 1 - (A + δA)ᴴ * (A + δA)ᴴ.pinv = 0 := by
        refine toEuclideanLin.injective ?_
        rw [toEuclideanLin_one_sub_mul_pinv, map_zero]
        refine LinearMap.ext fun v => ?_
        have hv : v ∈ LinearMap.range (toEuclideanLin (A + δA)ᴴ) := htop ▸ Submodule.mem_top
        rw [ContinuousLinearMap.coe_coe, LinearMap.zero_apply,
          Submodule.starProjection_orthogonal_val,
          Submodule.starProjection_eq_self_iff.2 hv, sub_self]
      rw [hz, norm_zero]
  have hc0 : 0 ≤ c := by rw [hc]; split_ifs <;> norm_num
  have hκ : pinvCondNumberLp 2 A = ‖A‖ / σ := by
    rw [pinvCondNumberLp, lpOpNorm_two, lpOpNorm_two, ← l2_opNorm_conjTranspose A.pinv,
      ← pinv_conjTranspose, l2_opNorm_pinv_eq_inv_iInf_colSingularValues
        (linearIndependent_transpose_of_iInf_colSingularValues_pos hσ0), div_eq_mul_inv]
  -- the bound on `‖x̂ - x‖`
  have hu : ‖δb - toEuclideanLin δA x‖ ≤ ‖δb‖ + ‖δA‖ * ‖x‖ :=
    (norm_sub_le _ _).trans (add_le_add le_rfl (norm_toEuclideanLin_apply_le _ _))
  have hmain : ‖x' - x‖ ≤ (σ - ‖δA‖)⁻¹ * (‖δb‖ + ‖δA‖ * ‖x‖) + c * ‖δA‖ * (‖x‖ / σ) := by
    rw [minNorm_sub_eq hA hx hx']
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (norm_toEuclideanLin_apply_le _ _).trans (mul_le_mul hP hu (norm_nonneg _)
        (inv_nonneg.2 hd.le))
    · rw [toEuclideanLin_mul_apply, ← hy, toEuclideanLin_mul_apply]
      have h1 : ‖toEuclideanLin δAᴴ y‖ ≤ ‖δA‖ * (‖x‖ / σ) := by
        refine (norm_toEuclideanLin_apply_le _ _).trans ?_
        rw [l2_opNorm_conjTranspose]
        exact mul_le_mul_of_nonneg_left hyx (norm_nonneg _)
      calc _ ≤ ‖1 - (A + δA).pinv * (A + δA)‖ * ‖toEuclideanLin δAᴴ y‖ :=
            norm_toEuclideanLin_apply_le _ _
        _ ≤ c * (‖δA‖ * (‖x‖ / σ)) := mul_le_mul hproj h1 (norm_nonneg _) hc0
        _ = c * ‖δA‖ * (‖x‖ / σ) := by ring
  rw [div_le_iff₀ hxn]
  refine hmain.trans ?_
  have hδb : ‖δb‖ ≤ ‖δb‖ / ‖b‖ * (‖A‖ * ‖x‖) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hbn]
    exact mul_le_mul_of_nonneg_left hbA (norm_nonneg _)
  have e1 : (σ - ‖δA‖)⁻¹ * (‖δb‖ + ‖δA‖ * ‖x‖) ≤
      ‖A‖ / (σ - ‖δA‖) * (‖δA‖ / ‖A‖ + ‖δb‖ / ‖b‖) * ‖x‖ := by
    have hAn' := hAn.ne'
    have hbn' := hbn.ne'
    have hd' := hd.ne'
    rw [show ‖A‖ / (σ - ‖δA‖) * (‖δA‖ / ‖A‖ + ‖δb‖ / ‖b‖) * ‖x‖ =
      (σ - ‖δA‖)⁻¹ * (‖δb‖ / ‖b‖ * (‖A‖ * ‖x‖) + ‖δA‖ * ‖x‖) by field_simp; ring]
    exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hd.le)
  have e2 : c * ‖δA‖ * (‖x‖ / σ) =
      (if Fintype.card m < Fintype.card n then pinvCondNumberLp 2 A * (‖δA‖ / ‖A‖) else 0) *
        ‖x‖ := by
    rw [hc, hκ]
    split_ifs
    · rw [div_mul_div_comm, mul_comm σ ‖A‖, mul_div_mul_left _ _ hAn.ne']
      ring
    · simp
  rw [add_mul, e2]
  linarith

end FullRowRank

/-! ### The derivatives along a line -/

section Derivative

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- A quadratic in a real parameter has derivative its linear coefficient at `0`. -/
private theorem hasDerivAt_quadratic {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c₀ c₁ c₂ : F) : HasDerivAt (fun t : ℝ => c₀ + t • c₁ + t ^ 2 • c₂) c₁ 0 := by
  have h1 := (hasDerivAt_id (0 : ℝ)).smul_const c₁
  have h2 := (hasDerivAt_pow 2 (0 : ℝ)).smul_const c₂
  convert ((hasDerivAt_const (0 : ℝ) c₀).add h1).add h2 using 1
  · rfl
  · simp

omit [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- The Gram matrix along a line is quadratic in the parameter. -/
private theorem conjTranspose_mul_self_line (A E : Matrix m n ℝ) (t : ℝ) :
    (A + t • E)ᴴ * (A + t • E) = Aᴴ * A + t • (Eᴴ * A + Aᴴ * E) + t ^ 2 • (Eᴴ * E) := by
  simp only [conjTranspose_add, conjTranspose_smul, star_trivial, Matrix.add_mul,
    Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]
  module

/-- **The derivative of the least-squares solution along a line** ([golub2013matrix] (5.3.15)):
for a real `A` with linearly independent columns, `E`, `b` and `f`, the map
`t ↦ (A + t E)⁺ (b + t f)` has derivative `(Aᴴ A)⁻¹ Aᴴ (f - E x) + (Aᴴ A)⁻¹ Eᴴ r` at `0`, where
`x = A⁺ b` and `r = b - A x`. Near `0` the columns stay independent
(`Matrix.linearIndependent_transpose_add_of_l2_opNorm_lt`), so the map is
`t ↦ G(t)⁻¹ h(t)` with the quadratics `G(t) = (A + tE)ᴴ(A + tE)` and `h(t) = (A + tE)ᴴ(b + tf)`,
and the derivative of the inverse is `-G⁻¹ G' G⁻¹` (`hasFDerivAt_ringInverse`). (Stated over `ℝ`:
over `ℂ` the conjugate transpose makes the map non-holomorphic in a complex parameter.) -/
theorem hasDerivAt_pinv_mulVec_line {A : Matrix m n ℝ} (hA : LinearIndependent ℝ Aᵀ)
    (E : Matrix m n ℝ) (b f : EuclideanSpace ℝ m) :
    HasDerivAt (fun t : ℝ => toEuclideanLin (A + t • E).pinv (b + t • f))
      (toEuclideanLin ((Aᴴ * A)⁻¹ * Aᴴ) (f - toEuclideanLin E (toEuclideanLin A.pinv b)) +
        toEuclideanLin ((Aᴴ * A)⁻¹ * Eᴴ) (b - toEuclideanLin A (toEuclideanLin A.pinv b)))
      0 := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have : Subsingleton (EuclideanSpace ℝ n) := ⟨fun a b => by ext i; exact isEmptyElim i⟩
    convert hasDerivAt_const (0 : ℝ) (0 : EuclideanSpace ℝ n) using 1
  set x₀ := toEuclideanLin A.pinv b with hx₀
  set G : ℝ → EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n :=
    fun t => toEuclideanCLM (n := n) (𝕜 := ℝ) ((A + t • E)ᴴ * (A + t • E)) with hGdef
  set h : ℝ → EuclideanSpace ℝ n := fun t => toEuclideanLin (A + t • E)ᴴ (b + t • f) with hhdef
  have hGd : HasDerivAt G (toEuclideanCLM (n := n) (𝕜 := ℝ) (Eᴴ * A + Aᴴ * E)) 0 := by
    convert hasDerivAt_quadratic (toEuclideanCLM (n := n) (𝕜 := ℝ) (Aᴴ * A))
      (toEuclideanCLM (n := n) (𝕜 := ℝ) (Eᴴ * A + Aᴴ * E))
      (toEuclideanCLM (n := n) (𝕜 := ℝ) (Eᴴ * E)) using 1
    funext t
    simp only [hGdef]
    rw [conjTranspose_mul_self_line, map_add, map_add, map_smul, map_smul]
  have hhd : HasDerivAt h (toEuclideanLin Eᴴ b + toEuclideanLin Aᴴ f) 0 := by
    convert hasDerivAt_quadratic (toEuclideanLin Aᴴ b)
      (toEuclideanLin Eᴴ b + toEuclideanLin Aᴴ f) (toEuclideanLin Eᴴ f) using 1
    funext t
    simp only [hhdef, conjTranspose_add, conjTranspose_smul, star_trivial, map_add, map_smul,
      LinearMap.add_apply, LinearMap.smul_apply]
    module
  have hGu : IsUnit (Aᴴ * A) := (posDef_conjTranspose_mul_self_of_linearIndependent hA).isUnit
  have hu := hGu.map (toEuclideanCLM (n := n) (𝕜 := ℝ))
  have hG0 : G 0 = hu.unit := by
    rw [hu.unit_spec, hGdef]
    simp
  have hinv' : ((hu.unit⁻¹ : (EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n)ˣ) :
      EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) =
        toEuclideanCLM (n := n) (𝕜 := ℝ) (Aᴴ * A)⁻¹ := by
    rw [toEuclideanCLM_nonsing_inv hGu, ← Ring.inverse_unit, hu.unit_spec]
  have hinvD : HasFDerivAt Ring.inverse (-ContinuousLinearMap.mulLeftRight ℝ
      (EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) ↑hu.unit⁻¹ ↑hu.unit⁻¹) (G 0) := by
    rw [hG0]
    exact hasFDerivAt_ringInverse hu.unit
  have hcomp := hinvD.comp_hasDerivAt (0 : ℝ) hGd
  have hres := hcomp.clm_apply hhd
  -- near `0` the map is `G(t)⁻¹ h(t)`
  have hσ := iInf_colSingularValues_pos_of_linearIndependent hA
  have hev : (fun t : ℝ => toEuclideanLin (A + t • E).pinv (b + t • f)) =ᶠ[nhds 0]
      fun t => (Ring.inverse ∘ G) t (h t) := by
    have hlim : Filter.Tendsto (fun t : ℝ => ‖t • E‖) (nhds 0) (nhds 0) := by
      have := ((continuous_id.smul (continuous_const (y := E))).norm).tendsto (0 : ℝ)
      simpa using this
    filter_upwards [Filter.Tendsto.eventually_lt_const hσ hlim] with t ht
    have hAt := linearIndependent_transpose_add_of_l2_opNorm_lt ht
    have hGt := (posDef_conjTranspose_mul_self_of_linearIndependent hAt).isUnit
    simp only [Function.comp_apply, hGdef]
    rw [← toEuclideanCLM_nonsing_inv hGt,
      pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose hAt, toEuclideanLin_mul_apply]
    rfl
  convert hres.congr_of_eventuallyEq hev using 1
  -- the value of the derivative
  have hh0 : h 0 = toEuclideanLin Aᴴ b := by simp [hhdef]
  have hx₀' : toEuclideanLin (Aᴴ * A)⁻¹ (toEuclideanLin Aᴴ b) = x₀ := by
    rw [hx₀, pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose hA, toEuclideanLin_mul_apply]
  rw [Function.comp_apply, hG0, Ring.inverse_unit, hinv', hh0]
  change _ = -toEuclideanLin (Aᴴ * A)⁻¹ (toEuclideanLin (Eᴴ * A + Aᴴ * E)
      (toEuclideanLin (Aᴴ * A)⁻¹ (toEuclideanLin Aᴴ b))) +
    toEuclideanLin (Aᴴ * A)⁻¹ (toEuclideanLin Eᴴ b + toEuclideanLin Aᴴ f)
  rw [hx₀', toEuclideanLin_mul_apply, toEuclideanLin_mul_apply, ← LinearMap.map_add,
    ← LinearMap.map_neg, ← LinearMap.map_add]
  congr 1
  rw [map_add, LinearMap.add_apply, toEuclideanLin_mul_apply, toEuclideanLin_mul_apply,
    LinearMap.map_sub, LinearMap.map_sub]
  abel

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- The Gram matrix of the rows along a line is quadratic in the parameter. -/
private theorem mul_conjTranspose_self_line (A E : Matrix m n ℝ) (t : ℝ) :
    (A + t • E) * (A + t • E)ᴴ = A * Aᴴ + t • (E * Aᴴ + A * Eᴴ) + t ^ 2 • (E * Eᴴ) := by
  simp only [conjTranspose_add, conjTranspose_smul, star_trivial, Matrix.add_mul,
    Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]
  module

/-- **The derivative of the minimal-norm solution along a line** ([golub2013matrix] (5.6.2)): for a
real `A` with linearly independent rows, `E`, `b` and `f`, the map
`t ↦ (A + tE)ᴴ ((A + tE)(A + tE)ᴴ)⁻¹ (b + t f)` has derivative
`(1 - Aᴴ (A Aᴴ)⁻¹ A) Eᴴ (A Aᴴ)⁻¹ b + Aᴴ (A Aᴴ)⁻¹ (f - E x)` at `0`, where `x = Aᴴ (A Aᴴ)⁻¹ b`. Near
`0` the rows stay independent (`Matrix.linearIndependent_add_of_l2_opNorm_lt`), and the map is
`t ↦ M(t)ᴴ H(t)⁻¹ (b + tf)` with `M(t) = A + tE` and the quadratic `H(t) = M(t) M(t)ᴴ`; the product
rule and the derivative `-H⁻¹ H' H⁻¹` of the inverse give the formula. (Stated over `ℝ`, as
`Matrix.hasDerivAt_pinv_mulVec_line`.) -/
theorem hasDerivAt_minNorm_line {A : Matrix m n ℝ} (hA : LinearIndependent ℝ A)
    (E : Matrix m n ℝ) (b f : EuclideanSpace ℝ m) :
    HasDerivAt (fun t : ℝ =>
        toEuclideanLin ((A + t • E)ᴴ * ((A + t • E) * (A + t • E)ᴴ)⁻¹) (b + t • f))
      (toEuclideanLin ((1 - Aᴴ * (A * Aᴴ)⁻¹ * A) * Eᴴ * (A * Aᴴ)⁻¹) b +
        toEuclideanLin (Aᴴ * (A * Aᴴ)⁻¹)
          (f - toEuclideanLin E (toEuclideanLin (Aᴴ * (A * Aᴴ)⁻¹) b))) 0 := by
  rcases isEmpty_or_nonempty m with hm | hm
  · have : Subsingleton (EuclideanSpace ℝ m) := ⟨fun a b => by ext i; exact isEmptyElim i⟩
    obtain rfl : b = 0 := Subsingleton.elim _ _
    obtain rfl : f = 0 := Subsingleton.elim _ _
    simp only [smul_zero, add_zero, map_zero, sub_zero]
    exact hasDerivAt_const _ _
  set H : ℝ → EuclideanSpace ℝ m →L[ℝ] EuclideanSpace ℝ m :=
    fun t => toEuclideanCLM (n := m) (𝕜 := ℝ) ((A + t • E) * (A + t • E)ᴴ) with hHdef
  set T : ℝ → EuclideanSpace ℝ m →L[ℝ] EuclideanSpace ℝ n :=
    fun t => LinearMap.toContinuousLinearMap (toEuclideanLin (A + t • E)ᴴ) with hTdef
  have hHd : HasDerivAt H (toEuclideanCLM (n := m) (𝕜 := ℝ) (E * Aᴴ + A * Eᴴ)) 0 := by
    convert hasDerivAt_quadratic (toEuclideanCLM (n := m) (𝕜 := ℝ) (A * Aᴴ))
      (toEuclideanCLM (n := m) (𝕜 := ℝ) (E * Aᴴ + A * Eᴴ))
      (toEuclideanCLM (n := m) (𝕜 := ℝ) (E * Eᴴ)) using 1
    funext t
    simp only [hHdef]
    rw [mul_conjTranspose_self_line, map_add, map_add, map_smul, map_smul]
  have hTd : HasDerivAt T (LinearMap.toContinuousLinearMap (toEuclideanLin Eᴴ)) 0 := by
    convert hasDerivAt_quadratic (LinearMap.toContinuousLinearMap (toEuclideanLin Aᴴ))
      (LinearMap.toContinuousLinearMap (toEuclideanLin Eᴴ)) 0 using 1
    funext t
    simp only [hTdef, conjTranspose_add, conjTranspose_smul, star_trivial, map_add, map_smul,
      smul_zero, add_zero]
  have hbd : HasDerivAt (fun t : ℝ => b + t • f) f 0 := by
    convert hasDerivAt_quadratic b f 0 using 1
    funext t
    simp
  have hGu : IsUnit (A * Aᴴ) := (posDef_self_mul_conjTranspose_of_linearIndependent hA).isUnit
  have hu := hGu.map (toEuclideanCLM (n := m) (𝕜 := ℝ))
  have hH0 : H 0 = hu.unit := by
    rw [hu.unit_spec, hHdef]
    simp
  have hinv' : ((hu.unit⁻¹ : (EuclideanSpace ℝ m →L[ℝ] EuclideanSpace ℝ m)ˣ) :
      EuclideanSpace ℝ m →L[ℝ] EuclideanSpace ℝ m) =
        toEuclideanCLM (n := m) (𝕜 := ℝ) (A * Aᴴ)⁻¹ := by
    rw [toEuclideanCLM_nonsing_inv hGu, ← Ring.inverse_unit, hu.unit_spec]
  have hinvD : HasFDerivAt Ring.inverse (-ContinuousLinearMap.mulLeftRight ℝ
      (EuclideanSpace ℝ m →L[ℝ] EuclideanSpace ℝ m) ↑hu.unit⁻¹ ↑hu.unit⁻¹) (H 0) := by
    rw [hH0]
    exact hasFDerivAt_ringInverse hu.unit
  have hw := (hinvD.comp_hasDerivAt (0 : ℝ) hHd).clm_apply hbd
  have hres := hTd.clm_apply hw
  -- near `0` the rows stay independent
  have hAc : LinearIndependent ℝ Aᴴᵀ := by
    rwa [conjTranspose_eq_transpose_of_trivial, transpose_transpose]
  have hσ := iInf_colSingularValues_pos_of_linearIndependent hAc
  have hev : (fun t : ℝ =>
      toEuclideanLin ((A + t • E)ᴴ * ((A + t • E) * (A + t • E)ᴴ)⁻¹) (b + t • f)) =ᶠ[nhds 0]
      fun t => T t ((Ring.inverse ∘ H) t (b + t • f)) := by
    have hlim : Filter.Tendsto (fun t : ℝ => ‖t • E‖) (nhds 0) (nhds 0) := by
      have := ((continuous_id.smul (continuous_const (y := E))).norm).tendsto (0 : ℝ)
      simpa using this
    filter_upwards [Filter.Tendsto.eventually_lt_const hσ hlim] with t ht
    have hAt := linearIndependent_add_of_l2_opNorm_lt ht
    have hHt := (posDef_self_mul_conjTranspose_of_linearIndependent hAt).isUnit
    simp only [Function.comp_apply, hHdef, hTdef]
    rw [← toEuclideanCLM_nonsing_inv hHt, toEuclideanLin_mul_apply]
    rfl
  convert hres.congr_of_eventuallyEq hev using 1
  rw [Function.comp_apply, hH0, Ring.inverse_unit, hinv']
  change _ = toEuclideanLin Eᴴ (toEuclideanLin (A * Aᴴ)⁻¹ (b + (0 : ℝ) • f)) +
    toEuclideanLin (A + (0 : ℝ) • E)ᴴ (-toEuclideanLin (A * Aᴴ)⁻¹
      (toEuclideanLin (E * Aᴴ + A * Eᴴ) (toEuclideanLin (A * Aᴴ)⁻¹ (b + (0 : ℝ) • f))) +
      toEuclideanLin (A * Aᴴ)⁻¹ f)
  simp only [zero_smul, add_zero, toEuclideanLin_mul_apply, map_sub, map_add, map_neg,
    LinearMap.sub_apply, LinearMap.add_apply, toEuclideanLin_one, LinearMap.id_apply]
  abel

end Derivative

end Matrix
