import NumlibSurface.ConnGouldToint.Chapter09.Section04
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# An incomplete quadratic interpolation counterexample

For an incomplete degree-two block, the bounds on adjacent blocks and
on the last block in Theorem 9.4.4 do not control the model error.
-/

namespace ConnGouldToint.Chapter09

local notation "V" => EuclideanSpace ℝ (Fin 3)

private noncomputable def xyz (x y z : ℝ) : V := WithLp.toLp 2 ![x, y, z]

@[simp] private theorem xyz_zero (x y z : ℝ) : xyz x y z 0 = x := rfl
@[simp] private theorem xyz_one (x y z : ℝ) : xyz x y z 1 = y := rfl
@[simp] private theorem xyz_two (x y z : ℝ) : xyz x y z 2 = z := rfl

private noncomputable def coord (i : Fin 3) : V →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) i

/-- The fixed smooth objective for the counterexample. It equals twice the
product of the sines of the first two coordinates. -/
noncomputable def incompleteQuadraticObjective (x : V) : ℝ :=
  Real.cos ((coord 0 - coord 1) x) - Real.cos ((coord 0 + coord 1) x)

private theorem objective_xyz (x y z : ℝ) :
    incompleteQuadraticObjective (xyz x y z) = Real.cos (x - y) - Real.cos (x + y) := rfl

private theorem fderiv_cos_clm (L : V →L[ℝ] ℝ) (x : V) :
    fderiv ℝ (fun y ↦ Real.cos (L y)) x = (-Real.sin (L x)) • L :=
  L.hasFDerivAt.cos.fderiv

private theorem fderiv_fderiv_cos_clm (L : V →L[ℝ] ℝ) (x : V) :
    fderiv ℝ (fderiv ℝ (fun y ↦ Real.cos (L y))) x =
      (-Real.cos (L x)) • L.smulRight L := by
  rw [show fderiv ℝ (fun y ↦ Real.cos (L y)) = fun y ↦ (-Real.sin (L y)) • L from
    funext (fderiv_cos_clm L)]
  convert (L.hasFDerivAt.sin.neg.smul_const L).fderiv using 1
  ext y z
  simp [ContinuousLinearMap.smulRight_apply, mul_assoc]

private theorem norm_fderiv_cos_clm (L : V →L[ℝ] ℝ) (x : V) :
    ‖fderiv ℝ (fun y ↦ Real.cos (L y)) x‖ ≤ ‖L‖ := by
  rw [fderiv_cos_clm, norm_smul, norm_neg, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one _)

private theorem norm_fderiv_fderiv_cos_clm (L : V →L[ℝ] ℝ) (x : V) :
    ‖fderiv ℝ (fderiv ℝ (fun y ↦ Real.cos (L y))) x‖ ≤ ‖L‖ ^ 2 := by
  rw [fderiv_fderiv_cos_clm]
  apply ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg _)
  intro y
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  simp only [smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul, Real.norm_eq_abs,
    abs_mul, abs_neg]
  have hy : |L y| ≤ ‖L‖ * ‖y‖ := by simpa only [Real.norm_eq_abs] using L.le_opNorm y
  have hz : |L z| ≤ ‖L‖ * ‖z‖ := by simpa only [Real.norm_eq_abs] using L.le_opNorm z
  calc
    _ ≤ |L y| * |L z| :=
      mul_le_of_le_one_left (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Real.abs_cos_le_one _)
    _ ≤ (‖L‖ * ‖y‖) * (‖L‖ * ‖z‖) := mul_le_mul hy hz (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- AF.1, AF.3, and AF.5 hold globally, with constants independent of the
radius and interpolation set. The objective is also bounded below. -/
theorem incompleteQuadraticObjective_bounds :
    ContDiff ℝ 2 incompleteQuadraticObjective ∧
    (∀ x, -2 ≤ incompleteQuadraticObjective x) ∧
    ∃ B > 0, ∀ x : V, ‖fderiv ℝ incompleteQuadraticObjective x‖ ≤ B ∧
      ‖fderiv ℝ (fderiv ℝ incompleteQuadraticObjective) x‖ ≤ B := by
  let Lminus := coord 0 - coord 1
  let Lplus := coord 0 + coord 1
  let gminus (x : V) := Real.cos (Lminus x)
  let gplus (x : V) := Real.cos (Lplus x)
  have hminus : ContDiff ℝ 2 gminus := Lminus.contDiff.cos
  have hplus : ContDiff ℝ 2 gplus := Lplus.contDiff.cos
  have hdiffminus : Differentiable ℝ gminus := hminus.differentiable (by norm_num)
  have hdiffplus : Differentiable ℝ gplus := hplus.differentiable (by norm_num)
  have hddiffminus : Differentiable ℝ (fderiv ℝ gminus) :=
    (hminus.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hddiffplus : Differentiable ℝ (fderiv ℝ gplus) :=
    (hplus.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hf : incompleteQuadraticObjective = fun x ↦ gminus x - gplus x := rfl
  refine ⟨hminus.sub hplus, ?_,
    1 + ‖Lminus‖ + ‖Lplus‖ + ‖Lminus‖ ^ 2 + ‖Lplus‖ ^ 2, by positivity, ?_⟩
  · intro x
    rw [hf]
    dsimp [gminus, gplus]
    linarith [Real.neg_one_le_cos (Lminus x), Real.cos_le_one (Lplus x)]
  · intro x
    have hfirst : fderiv ℝ incompleteQuadraticObjective =
        fun x ↦ fderiv ℝ gminus x - fderiv ℝ gplus x := by
      funext x
      rw [hf, fderiv_fun_sub (hdiffminus x) (hdiffplus x)]
    rw [hfirst, fderiv_fun_sub (hddiffminus x) (hddiffplus x)]
    have h1 := (norm_sub_le (fderiv ℝ gminus x) (fderiv ℝ gplus x)).trans
      (add_le_add (norm_fderiv_cos_clm Lminus x) (norm_fderiv_cos_clm Lplus x))
    have h2 := (norm_sub_le (fderiv ℝ (fderiv ℝ gminus) x) (fderiv ℝ (fderiv ℝ gplus) x)).trans
      (add_le_add (norm_fderiv_fderiv_cos_clm Lminus x) (norm_fderiv_fderiv_cos_clm Lplus x))
    exact ⟨by linarith [sq_nonneg ‖Lminus‖, sq_nonneg ‖Lplus‖],
      by linarith [norm_nonneg Lminus, norm_nonneg Lplus]⟩

/-- The affine blocks are complete and the quadratic block has a single point. -/
abbrev incompleteQuadraticBlockSize : ℕ → ℕ
  | 0 => 1
  | 1 => 3
  | 2 => 1
  | _ => 0

/-- Interpolation points for radius `δ`. The third linear point is only
`δ²` away from the plane through the first three points. -/
noncomputable def incompleteQuadraticPoints (δ : ℝ) :
    (l : ℕ) → Fin (incompleteQuadraticBlockSize l) → V
  | 0, _ => 0
  | 1, i => ![xyz (δ / 2) 0 0, xyz 0 (δ / 2) 0, xyz (δ / 2) (δ / 2) (δ ^ 2)] i
  | 2, _ => xyz (-(δ / 2)) 0 0
  | _ + 3, i => Fin.elim0 i

/-- The Newton polynomials of degrees zero, one and two evaluated at a point. -/
noncomputable def incompleteQuadraticNewton (δ : ℝ) :
    (l : ℕ) → Fin (incompleteQuadraticBlockSize l) → V → ℝ
  | 0, _ => fun _ ↦ 1
  | 1, i => fun x ↦ ![x 0 / (δ / 2) - x 2 / δ ^ 2,
      x 1 / (δ / 2) - x 2 / δ ^ 2, x 2 / δ ^ 2] i
  | 2, _ => fun x ↦ (x 0 / (δ / 2)) * (x 0 / (δ / 2) - 1) / 2
  | _ + 3, i => Fin.elim0 i

private noncomputable def scaledCoordinatePolynomial (i : Fin 3) (a : ℝ) :
    MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.C a⁻¹ * MvPolynomial.X i

private theorem eval_scaledCoordinatePolynomial (i : Fin 3) (a : ℝ) (x : V) :
    MvPolynomial.eval (fun j ↦ x j) (scaledCoordinatePolynomial i a) = x i / a := by
  simp [scaledCoordinatePolynomial, div_eq_inv_mul]

private theorem totalDegree_scaledCoordinatePolynomial (i : Fin 3) (a : ℝ) :
    (scaledCoordinatePolynomial i a).totalDegree ≤ 1 := by
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp

/-- Every Newton function in the example is the evaluation of a polynomial
of degree at most its block index. -/
theorem incompleteQuadraticNewton_isPolynomial (δ : ℝ) (l : ℕ) (hl : l ≤ 2)
    (i : Fin (incompleteQuadraticBlockSize l)) :
    ∃ q : MvPolynomial (Fin 3) ℝ, q.totalDegree ≤ l ∧
      ∀ x : V, MvPolynomial.eval (fun j ↦ x j) q = incompleteQuadraticNewton δ l i x := by
  let X := scaledCoordinatePolynomial 0 (δ / 2)
  let Y := scaledCoordinatePolynomial 1 (δ / 2)
  let Z := scaledCoordinatePolynomial 2 (δ ^ 2)
  have hx : X.totalDegree ≤ 1 := totalDegree_scaledCoordinatePolynomial _ _
  have hy : Y.totalDegree ≤ 1 := totalDegree_scaledCoordinatePolynomial _ _
  have hz : Z.totalDegree ≤ 1 := totalDegree_scaledCoordinatePolynomial _ _
  interval_cases l
  · exact ⟨1, by simp, by simp [incompleteQuadraticNewton]⟩
  · fin_cases i
    · exact ⟨X - Z, (MvPolynomial.totalDegree_sub _ _).trans (max_le hx hz), fun x ↦ by
        simp [X, Z, eval_scaledCoordinatePolynomial, incompleteQuadraticNewton]⟩
    · exact ⟨Y - Z, (MvPolynomial.totalDegree_sub _ _).trans (max_le hy hz), fun x ↦ by
        simp [Y, Z, eval_scaledCoordinatePolynomial, incompleteQuadraticNewton]⟩
    · exact ⟨Z, hz, fun x ↦ by
        simp [Z, eval_scaledCoordinatePolynomial, incompleteQuadraticNewton]⟩
  · refine ⟨X * (X - 1) * MvPolynomial.C (1 / 2), ?_, fun x ↦ ?_⟩
    · have hsub : (X - 1).totalDegree ≤ 1 :=
        (MvPolynomial.totalDegree_sub _ _).trans (max_le hx (by simp))
      have hprod : (X * (X - 1)).totalDegree ≤ 2 :=
        (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hx hsub)
      exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa using hprod)
    · simp [X, eval_scaledCoordinatePolynomial, incompleteQuadraticNewton, div_eq_mul_inv]

/-- The degree-graded Newton conditions (9.4.4) hold for the five points. -/
theorem incompleteQuadraticFundamental {δ : ℝ} (hδ : 0 < δ) :
    IsNewtonFundamentalFamily (incompleteQuadraticPoints δ) (incompleteQuadraticNewton δ) 2 := by
  have hh : δ / 2 ≠ 0 := (half_pos hδ).ne'
  have hd : δ ^ 2 ≠ 0 := pow_ne_zero _ hδ.ne'
  constructor
  · intro l hl i j
    interval_cases l <;> fin_cases i <;> fin_cases j <;>
      norm_num [incompleteQuadraticPoints, incompleteQuadraticNewton,
        Matrix.cons_val_zero', Matrix.cons_val_succ', hh, hd]
  · intro l hl j hj i k
    interval_cases l <;> interval_cases j <;> fin_cases i <;> fin_cases k <;>
      norm_num [incompleteQuadraticPoints, incompleteQuadraticNewton,
        Matrix.cons_val_zero', Matrix.cons_val_succ', hh, hd]

/-- The five points in the order of their Newton blocks. -/
noncomputable def incompleteQuadraticFlatPoints (δ : ℝ) : Fin 5 → V :=
  ![incompleteQuadraticPoints δ 0 0, incompleteQuadraticPoints δ 1 0,
    incompleteQuadraticPoints δ 1 1, incompleteQuadraticPoints δ 1 2,
    incompleteQuadraticPoints δ 2 0]

/-- The five Newton basis functions in the order of their blocks. -/
noncomputable def incompleteQuadraticFlatNewton (δ : ℝ) : Fin 5 → V → ℝ :=
  ![incompleteQuadraticNewton δ 0 0, incompleteQuadraticNewton δ 1 0,
    incompleteQuadraticNewton δ 1 1, incompleteQuadraticNewton δ 1 2,
    incompleteQuadraticNewton δ 2 0]

/-- The evaluation matrix is invertible in the incomplete quadratic space.
It is lower triangular with unit diagonal in the graded Newton basis. -/
theorem incompleteQuadraticPoised {δ : ℝ} (hδ : 0 < δ) :
    IsPoised (incompleteQuadraticFlatPoints δ) (incompleteQuadraticFlatNewton δ) := by
  let A := interpolationMatrix (incompleteQuadraticFlatPoints δ) (incompleteQuadraticFlatNewton δ)
  have hh : δ / 2 ≠ 0 := (half_pos hδ).ne'
  have hd : δ ^ 2 ≠ 0 := pow_ne_zero _ hδ.ne'
  have hlo : A.IsLowerTriangular := by
    intro i j hij
    change i.val < j.val at hij
    fin_cases i <;> fin_cases j <;> norm_num at hij
    all_goals norm_num [A, interpolationMatrix, incompleteQuadraticFlatPoints,
      incompleteQuadraticFlatNewton, incompleteQuadraticPoints, incompleteQuadraticNewton,
      Matrix.cons_val_zero', Matrix.cons_val_succ', hh, hd]
  have hdiag (i : Fin 5) : A i i = 1 := by
    fin_cases i <;> norm_num [A, interpolationMatrix, incompleteQuadraticFlatPoints,
      incompleteQuadraticFlatNewton, incompleteQuadraticPoints, incompleteQuadraticNewton,
      Matrix.cons_val_zero', Matrix.cons_val_succ', hh, hd]
  change A.det ≠ 0
  rw [Matrix.det_of_isLowerTriangular A hlo]
  simp [hdiag]

private theorem xyz_mem_closedBall {δ x y z : ℝ} (hδ : 0 ≤ δ)
    (h : x ^ 2 + y ^ 2 + z ^ 2 ≤ δ ^ 2) : xyz x y z ∈ Metric.closedBall (0 : V) δ := by
  rw [Metric.mem_closedBall, dist_zero_right, ← sq_le_sq₀ (norm_nonneg _) hδ,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simpa only [xyz_zero, xyz_one, xyz_two] using h

private theorem point_mem_closedBall {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    ∀ l ≤ 2, ∀ i, incompleteQuadraticPoints δ l i ∈ Metric.closedBall (0 : V) δ := by
  intro l hl i
  interval_cases l
  · simpa [incompleteQuadraticPoints] using Metric.mem_closedBall_self (x := (0 : V)) hδ.le
  · fin_cases i
    · apply xyz_mem_closedBall hδ.le
      norm_num
      nlinarith only [sq_nonneg δ]
    · apply xyz_mem_closedBall hδ.le
      norm_num
      nlinarith only [sq_nonneg δ]
    · apply xyz_mem_closedBall hδ.le
      have hd : δ ^ 2 ≤ 1 / 4 := by nlinarith [mul_nonneg hδ.le (sub_nonneg.2 hδ')]
      nlinarith only [mul_le_mul_of_nonneg_right hd (sq_nonneg δ), sq_nonneg δ]
  · apply xyz_mem_closedBall hδ.le
    norm_num
    nlinarith only [sq_nonneg δ]

/-- All points lie in the trust region. Adjacent-block and final-block bounds
(9.4.19)–(9.4.20) hold with the same constant three for every radius. -/
theorem incompleteQuadraticPrintedBounds {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    (∀ l ≤ 2, ∀ i, incompleteQuadraticPoints δ l i ∈ Metric.closedBall (0 : V) δ) ∧
    (∀ l < 2, ∀ i j, |incompleteQuadraticNewton δ l i
      (incompleteQuadraticPoints δ (l + 1) j)| ≤ 3) ∧
    ∀ i x, x ∈ Metric.closedBall (0 : V) δ → |incompleteQuadraticNewton δ 2 i x| ≤ 3 := by
  have hh : 0 < δ / 2 := half_pos hδ
  refine ⟨point_mem_closedBall hδ hδ', ?_, ?_⟩
  · intro l hl i j
    interval_cases l <;> fin_cases i <;> fin_cases j <;>
      norm_num [incompleteQuadraticNewton, incompleteQuadraticPoints,
        Matrix.cons_val_zero', Matrix.cons_val_succ', hh.ne']
  · intro i x hx
    have hcoord : |x 0| ≤ δ := by
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      exact (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 0 :
        |x 0| ≤ ‖x‖).trans hx
    let u := x 0 / (δ / 2)
    have hu : |u| ≤ 2 := by
      dsimp [u]
      rw [abs_div, abs_of_pos hh]
      exact (div_le_iff₀ hh).2 (by linarith only [hcoord])
    have hu' : |u - 1| ≤ 3 := (abs_sub u 1).trans (by norm_num; linarith)
    change |u * (u - 1) / 2| ≤ 3
    rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    exact (mul_le_mul hu hu' (abs_nonneg _) (by norm_num)).trans (by norm_num)

private theorem objective_at_test (δ : ℝ) :
    incompleteQuadraticObjective (xyz 0 0 δ) = 0 := by simp [objective_xyz]

private theorem model_at_test {δ : ℝ} (hδ : 0 < δ) :
    newtonInterpolationModel incompleteQuadraticObjective (incompleteQuadraticPoints δ)
      (incompleteQuadraticNewton δ) 2 (xyz 0 0 δ) =
      (1 - Real.cos δ) / δ := by
  have hh : δ / 2 ≠ 0 := (half_pos hδ).ne'
  have hd : δ ^ 2 ≠ 0 := pow_ne_zero _ hδ.ne'
  have hf0 : incompleteQuadraticObjective (0 : V) = 0 := by
    simp [incompleteQuadraticObjective]
  have hf₁ : incompleteQuadraticObjective (xyz (δ / 2) (δ / 2) (δ ^ 2)) =
      1 - Real.cos δ := by
    rw [objective_xyz, sub_self, Real.cos_zero, add_halves]
  norm_num [newtonInterpolationModel, Finset.sum_range_succ, Fin.sum_univ_three,
    newtonInterpolationCoefficient, generalizedFiniteDifference, incompleteQuadraticPoints,
    incompleteQuadraticNewton,
    hf₁, hf0, objective_xyz, Real.cos_neg, hh, hd]
  change (∑ i : Fin 3, incompleteQuadraticObjective
    (![xyz (δ / 2) 0 0, xyz 0 (δ / 2) 0, xyz (δ / 2) (δ / 2) (δ ^ 2)] i) *
    ![-(δ / δ ^ 2), -(δ / δ ^ 2), δ / δ ^ 2] i) = _
  rw [Fin.sum_univ_three]
  norm_num [objective_xyz, Real.cos_neg, hf₁]
  field_simp

private theorem cos_deficit_ge {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    δ ^ 2 / 8 ≤ 1 - Real.cos δ := by
  have hπ := Real.pi_pos
  have habs : |δ| ≤ Real.pi := by rw [abs_of_pos hδ]; linarith [Real.pi_gt_three]
  have hcos := Real.cos_le_one_sub_mul_cos_sq habs
  have hcoef : (1 / 8 : ℝ) ≤ 2 / Real.pi ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hπ)).2
    nlinarith only [Real.pi_lt_four, hπ,
      mul_nonneg (sub_nonneg.2 Real.pi_lt_four.le) (show 0 ≤ Real.pi + 4 by positivity)]
  have h := mul_le_mul_of_nonneg_right hcoef (sq_nonneg δ)
  linarith only [hcos, h]

/-- For every proposed uniform constant in (9.4.21), these data satisfy
the printed geometric bounds for an incomplete quadratic block and violate
the error bound. There are five nodes in dimension three, including a
complete affine block. The objective and geometric constants are fixed. -/
theorem theorem_9_4_4_incompleteQuadratic_counterexample {C : ℝ} (hC : 0 < C) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
      IsNewtonFundamentalFamily (incompleteQuadraticPoints δ) (incompleteQuadraticNewton δ) 2 ∧
      IsPoised (incompleteQuadraticFlatPoints δ) (incompleteQuadraticFlatNewton δ) ∧
      (∀ l ≤ 2, ∀ i, incompleteQuadraticPoints δ l i ∈ Metric.closedBall (0 : V) δ) ∧
      (∀ l < 2, ∀ i j, |incompleteQuadraticNewton δ l i
        (incompleteQuadraticPoints δ (l + 1) j)| ≤ 3) ∧
      (∀ i x, x ∈ Metric.closedBall (0 : V) δ → |incompleteQuadraticNewton δ 2 i x| ≤ 3) ∧
      ∃ x ∈ Metric.closedBall (0 : V) δ,
        C * max (δ ^ 2) (δ ^ 3) <
          |incompleteQuadraticObjective x -
            newtonInterpolationModel incompleteQuadraticObjective (incompleteQuadraticPoints δ)
              (incompleteQuadraticNewton δ) 2 x| := by
  let δ := min (1 / 2) (1 / (16 * (C + 1)))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ' : δ ≤ 1 / 2 := min_le_left _ _
  have hCδ : C * δ < 1 / 8 := by
    have h := (le_div_iff₀ (show 0 < 16 * (C + 1) by positivity)).1
      (show δ ≤ 1 / (16 * (C + 1)) from min_le_right _ _)
    nlinarith only [h, hδ]
  have hge := cos_deficit_ge hδ hδ'
  have herror : δ / 8 ≤ (1 - Real.cos δ) / δ := by
    apply (le_div_iff₀ hδ).2
    nlinarith only [hge]
  have hmax : max (δ ^ 2) (δ ^ 3) = δ ^ 2 := by
    apply max_eq_left
    rw [pow_succ]
    exact mul_le_of_le_one_right (sq_nonneg δ) (by linarith only [hδ'])
  have hp := incompleteQuadraticPoised hδ
  obtain ⟨hball, hadj, htop⟩ := incompleteQuadraticPrintedBounds hδ hδ'
  refine ⟨δ, hδ, hδ', incompleteQuadraticFundamental hδ, hp, hball, hadj, htop,
    xyz 0 0 δ, xyz_mem_closedBall hδ.le (by simp), ?_⟩
  rw [hmax, objective_at_test, model_at_test hδ, zero_sub, abs_neg,
    abs_of_nonneg (le_trans (by positivity : 0 ≤ δ / 8) herror)]
  exact (show C * δ ^ 2 < δ / 8 by
    nlinarith only [mul_lt_mul_of_pos_right hCδ hδ]).trans_le herror

end ConnGouldToint.Chapter09
