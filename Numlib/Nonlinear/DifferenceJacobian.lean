import Mathlib.Analysis.CStarAlgebra.Matrix
import Numlib.Analysis.Calculus.MeanValue
import Numlib.Analysis.Normed.Lp.PiLp

/-!
# Difference approximations of the Jacobian matrix

The forward-difference Jacobian `J_h` of a map `F : ℝⁿ → ℝⁿ` at `x` with increments `h j` along
the canonical basis vectors ([quarteroni2000numerical] §7.1.2, (7.9)),

  `(J_h)_j = (F (x + h_j e_j) - F x) / h_j`,

and its error against the true derivative `F' x`: column by column,
`‖(J_h - F' x) e_j‖ ≤ (L / 2) |h_j|` when `F'` is `L`-Lipschitz around `x` (the sharp second-order
mean value inequality `Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le` of
`Numlib/Analysis/Calculus/MeanValue`), and in the operator norm,
`‖J_h - F' x‖ ≤ √n (L / 2) max_j |h_j|`.

The module lives on `EuclideanSpace ℝ ι` with the matrix read as an operator through
`Matrix.toEuclideanCLM`, because a difference Jacobian needs coordinates: `Numlib/Nonlinear/Newton`
is a Banach-space file with no basis, and its theorems on Newton-like iterations with approximate
derivatives (`Newton.norm_approxStep_sub_le`,
`Newton.tendsto_of_forall_inverse_sub_step_of_norm_sub_fderiv_le`,
`Newton.norm_succ_sub_le_sq_of_norm_sub_fderiv_le_mul`) take an arbitrary approximation `B k` of
`F' (x k)`, of which `toEuclideanCLM (differenceJacobian F (x k) (h k))` is the instance. The
convergence of the difference-Jacobian Newton method ([quarteroni2000numerical] Property 7.1) is
the combination of the two.

[quarteroni2000numerical] states Property 7.1 in the `‖·‖₁` norm, where the column-wise bound gives
`‖J_h - F' x‖₁ ≤ (L / 2) max_j |h_j|` with no dimensional factor; in the Euclidean norm used here
the factor `√n` appears (`∑ |v_j| ≤ √n ‖v‖₂`), which is irrelevant to the convergence conclusions.
-/

open scoped InnerProductSpace

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The forward-difference Jacobian of `F : ℝⁿ → ℝⁿ` at `x` with increments `h`
([quarteroni2000numerical] (7.9)): column `j` is the difference quotient
`(F (x + h_j e_j) - F x) / h_j` along the `j`-th canonical basis vector. An increment `h j = 0`
gives the junk column `0`. -/
noncomputable def differenceJacobian (F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ ι) (h : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => (F (x + h j • EuclideanSpace.single j 1) i - F x i) / h j

omit [Fintype ι] in
/-- The entries of the difference Jacobian. -/
theorem differenceJacobian_apply (F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ ι) (h : ι → ℝ) (i j : ι) :
    differenceJacobian F x h i j = (F (x + h j • EuclideanSpace.single j 1) i - F x i) / h j :=
  rfl

/-- Column `j` of the difference Jacobian, read as the image of the basis vector `e_j` under the
matrix acting on `EuclideanSpace ℝ ι`: the difference quotient of `F` along `e_j`. -/
theorem toEuclideanCLM_differenceJacobian_single (F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ ι) (h : ι → ℝ) (j : ι) :
    toEuclideanCLM (𝕜 := ℝ) (differenceJacobian F x h) (EuclideanSpace.single j 1)
      = (h j)⁻¹ • (F (x + h j • EuclideanSpace.single j 1) - F x) := by
  ext i
  simp [ofLp_toEuclideanCLM, differenceJacobian, div_eq_inv_mul]

/-- **Column-wise error of the difference Jacobian.** If `F` is differentiable on `ball x r` with
`‖F' y - F' x‖ ≤ L ‖y - x‖` there, and `0 < |h j| < r`, then
`‖(J_h - F' x) e_j‖ ≤ (L / 2) |h j|`: the difference quotient along `e_j` is within `(L / 2) |h j|`
of the directional derivative, by the sharp second-order mean value inequality. -/
theorem norm_differenceJacobian_col_sub_le {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {F' : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι}
    {x : EuclideanSpace ℝ ι} {r L : ℝ} (hF : ∀ y ∈ Metric.ball x r, HasFDerivAt F (F' y) y)
    (hL : ∀ y ∈ Metric.ball x r, ‖F' y - F' x‖ ≤ L * ‖y - x‖) {h : ι → ℝ} {j : ι}
    (hj0 : h j ≠ 0) (hjr : |h j| < r) :
    ‖(toEuclideanCLM (𝕜 := ℝ) (differenceJacobian F x h) - F' x) (EuclideanSpace.single j 1)‖
      ≤ L / 2 * |h j| := by
  set v : EuclideanSpace ℝ ι := h j • EuclideanSpace.single j 1 with hv
  have hvn : ‖v‖ = |h j| := by
    rw [hv, norm_smul, Real.norm_eq_abs, PiLp.norm_single, norm_one, mul_one]
  have hr : 0 < r := lt_of_le_of_lt (abs_nonneg _) hjr
  have hmem : x + v ∈ Metric.ball x r := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, hvn]
    exact hjr
  have htay : ‖F (x + v) - F x - F' x (x + v - x)‖ ≤ L / 2 * ‖x + v - x‖ ^ 2 :=
    Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le (convex_ball x r) hF
      (Metric.mem_ball_self hr) hmem hL
  rw [add_sub_cancel_left, hvn] at htay
  have hkey : (toEuclideanCLM (𝕜 := ℝ) (differenceJacobian F x h) - F' x)
      (EuclideanSpace.single j 1) = (h j)⁻¹ • (F (x + v) - F x - F' x v) := by
    have hFv : F' x v = h j • F' x (EuclideanSpace.single j 1) := by rw [hv, map_smul]
    rw [_root_.sub_apply, toEuclideanCLM_differenceJacobian_single, ← hv, hFv]
    simp only [smul_sub]
    rw [smul_smul, inv_mul_cancel₀ hj0, one_smul]
  rw [hkey, norm_smul, norm_inv, Real.norm_eq_abs]
  have hpos : 0 < |h j| := abs_pos.2 hj0
  calc |h j|⁻¹ * ‖F (x + v) - F x - F' x v‖ ≤ |h j|⁻¹ * (L / 2 * |h j| ^ 2) := by gcongr
    _ = L / 2 * |h j| := by field_simp

/-- **Operator-norm error of the difference Jacobian.** Under the hypotheses of
`Matrix.norm_differenceJacobian_col_sub_le` for every column, with all increments bounded by `η`,
`‖J_h - F' x‖ ≤ √n (L / 2) η` on `EuclideanSpace ℝ ι`, `n = card ι`. The proof expands `v` in the
canonical basis, `‖(J_h - F' x) v‖ ≤ ∑_j |v_j| ‖(J_h - F' x) e_j‖ ≤ (L / 2) η ∑_j |v_j|`, and uses
`∑_j |v_j| ≤ √n ‖v‖` (`PiLp.norm_toLp_one_le_sqrt_card_mul_norm_toLp_two`). In the `‖·‖₁` norm of
[quarteroni2000numerical] Property 7.1 the last step is an equality and the factor `√n` is
absent. -/
theorem opNorm_toEuclideanCLM_differenceJacobian_sub_le
    {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {F' : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι}
    {x : EuclideanSpace ℝ ι} {r L : ℝ} (hF : ∀ y ∈ Metric.ball x r, HasFDerivAt F (F' y) y)
    (hL : ∀ y ∈ Metric.ball x r, ‖F' y - F' x‖ ≤ L * ‖y - x‖) {h : ι → ℝ}
    (hj : ∀ j, h j ≠ 0 ∧ |h j| < r) {η : ℝ} (hη : ∀ j, |h j| ≤ η) :
    ‖toEuclideanCLM (𝕜 := ℝ) (differenceJacobian F x h) - F' x‖
      ≤ √(Fintype.card ι : ℝ) * (L / 2) * η := by
  set D := toEuclideanCLM (𝕜 := ℝ) (differenceJacobian F x h) - F' x with hD
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hD0 : D = 0 := by
      ext v i
      exact isEmptyElim i
    rw [hD0, norm_zero, Fintype.card_eq_zero]
    simp
  obtain ⟨j₀⟩ := hι
  -- `L ≥ 0`, from the Lipschitz bound at one increment
  have hL0 : 0 ≤ L := by
    have hpos : 0 < |h j₀| := abs_pos.2 (hj j₀).1
    have hmem : x + h j₀ • EuclideanSpace.single j₀ 1 ∈ Metric.ball x r := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        PiLp.norm_single, norm_one, mul_one]
      exact (hj j₀).2
    have h1 := hL _ hmem
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, PiLp.norm_single, norm_one,
      mul_one] at h1
    exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans h1) hpos
  have hη0 : 0 ≤ η := (abs_nonneg _).trans (hη j₀)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have hcol : ∀ i, ‖D (EuclideanSpace.single i 1)‖ ≤ L / 2 * η := fun i =>
    (norm_differenceJacobian_col_sub_le hF hL (hj i).1 (hj i).2).trans
      (mul_le_mul_of_nonneg_left (hη i) (by linarith))
  have hv : ∑ i, v i • EuclideanSpace.single i 1 = v := by
    conv_rhs => rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr v]
    simp [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  have hsum : ∑ i, |v i| ≤ √(Fintype.card ι : ℝ) * ‖v‖ := by
    have h1 := PiLp.norm_toLp_one_le_sqrt_card_mul_norm_toLp_two (WithLp.ofLp v)
    rw [PiLp.norm_eq_of_L1] at h1
    simpa [Real.norm_eq_abs] using h1
  calc ‖D v‖ = ‖∑ i, v i • D (EuclideanSpace.single i 1)‖ := by
        conv_lhs => rw [← hv]
        rw [map_sum]
        simp only [map_smul]
    _ ≤ ∑ i, ‖v i • D (EuclideanSpace.single i 1)‖ := norm_sum_le _ _
    _ = ∑ i, |v i| * ‖D (EuclideanSpace.single i 1)‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i, |v i| * (L / 2 * η) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hcol i) (abs_nonneg _)
    _ = L / 2 * η * ∑ i, |v i| := by rw [← Finset.sum_mul, mul_comm]
    _ ≤ L / 2 * η * (√(Fintype.card ι : ℝ) * ‖v‖) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = √(Fintype.card ι : ℝ) * (L / 2) * η * ‖v‖ := by ring

end Matrix
