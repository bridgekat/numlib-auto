import Numlib.Optimization.CompactAnchoredJets
import Numlib.Optimization.TaylorCriticalityCriteria
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# A coupled cubic objective on a compact box

The polynomial couples a negative quadratic direction to a third coordinate. Its genuine
ambient derivatives give explicit first- and second-order Taylor decrements and an exact
cubic remainder. Compactness supplies fixed anchored jet bounds on a full neighborhood.
-/

noncomputable section
open Set Metric
namespace Optimization.CoupledCubic

/-- Three-dimensional real Euclidean space. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- A vector with three specified coordinates. -/
def point (a b c : ℝ) : Space := WithLp.toLp 2 ![a, b, c]

/-- The first specified coordinate. -/
@[simp] theorem point_zero_coord (a b c : ℝ) : point a b c 0 = a := rfl

/-- The second specified coordinate. -/
@[simp] theorem point_one_coord (a b c : ℝ) : point a b c 1 = b := rfl

/-- The third specified coordinate. -/
@[simp] theorem point_two_coord (a b c : ℝ) : point a b c 2 = c := rfl

/-- Zero coordinates specify the zero vector. -/
@[simp] theorem point_zero : point 0 0 0 = 0 := by ext i; fin_cases i <;> rfl

/-- Specified coordinates commute with vector addition. -/
@[simp] theorem point_add (a b c d e f : ℝ) :
    point a b c + point d e f = point (a + d) (b + e) (c + f) := by
  ext i; fin_cases i <;> rfl

/-- Specified coordinates commute with vector subtraction. -/
@[simp] theorem point_sub (a b c d e f : ℝ) :
    point a b c - point d e f = point (a - d) (b - e) (c - f) := by
  ext i; fin_cases i <;> rfl

/-- Specified coordinates commute with real scalar multiplication. -/
@[simp] theorem point_smul (t a b c : ℝ) :
    t • point a b c = point (t * a) (t * b) (t * c) := by
  ext i; fin_cases i <;> rfl

/-- A vector is determined by its coordinates. -/
@[simp] theorem point_coords (x : Space) : point (x 0) (x 1) (x 2) = x := by
  ext i; fin_cases i <;> rfl

/-- The squared Euclidean norm is the sum of the three squared coordinates. -/
theorem norm_sq_eq (x : Space) : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  ring

/-- The squared norm of a specified vector. -/
theorem norm_point_sq (a b c : ℝ) : ‖point a b c‖ ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 :=
  norm_sq_eq _

/-- Every coordinate is bounded by the ambient norm. -/
theorem abs_coordinate_le_norm (x : Space) (i : Fin 3) : |x i| ≤ ‖x‖ :=
  PiLp.norm_apply_le x i

/-- A norm bound is equivalent to the corresponding sum of squares bound. -/
theorem norm_point_le_iff (a b c : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ‖point a b c‖ ≤ r ↔ a ^ 2 + b ^ 2 + c ^ 2 ≤ r ^ 2 := by
  rw [← norm_point_sq]
  exact (sq_le_sq₀ (norm_nonneg _) hr).symm

/-- A vector supported on the first coordinate has its scalar absolute norm. -/
@[simp] theorem norm_point_x (a : ℝ) : ‖point a 0 0‖ = |a| := by
  have h := norm_point_sq a 0 0
  nlinarith [norm_nonneg (point a 0 0), abs_nonneg a, sq_abs a]

/-- A vector supported on the second coordinate has its scalar absolute norm. -/
@[simp] theorem norm_point_y (b : ℝ) : ‖point 0 b 0‖ = |b| := by
  have h := norm_point_sq 0 b 0
  nlinarith [norm_nonneg (point 0 b 0), abs_nonneg b, sq_abs b]

/-- A vector supported on the third coordinate has its scalar absolute norm. -/
@[simp] theorem norm_point_z (c : ℝ) : ‖point 0 0 c‖ = |c| := by
  have h := norm_point_sq 0 0 c
  nlinarith [norm_nonneg (point 0 0 c), abs_nonneg c, sq_abs c]

/-- The fixed globally defined cubic objective. -/
def objective (x : Space) : ℝ := (x 0) ^ 2 / 2 - x 2 * (x 1) ^ 2 / 2

/-- Evaluation at specified coordinates is the polynomial formula. -/
@[simp] theorem objective_point (a b c : ℝ) :
    objective (point a b c) = a ^ 2 / 2 - c * b ^ 2 / 2 := rfl

/-- The polynomial is smooth to every order on its full ambient space. -/
theorem contDiff_objective (n : WithTop ℕ∞) : ContDiff ℝ n objective := by
  unfold objective
  fun_prop

/-- The actual first derivative in an arbitrary ambient direction. -/
theorem fderiv_objective (x d : Space) : fderiv ℝ objective x d =
    x 0 * d 0 - x 2 * x 1 * d 1 - (x 1) ^ 2 * d 2 / 2 := by
  have h₀ := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).hasFDerivAt (x := x)
  have h₁ := (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).hasFDerivAt (x := x)
  have h₂ := (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).hasFDerivAt (x := x)
  have h := (h₀.pow 2 |>.mul_const (1 / 2 : ℝ)).sub ((h₂.mul (h₁.pow 2)).mul_const (1 / 2 : ℝ))
  have he := congrArg (fun A : Space →L[ℝ] ℝ => A d) h.fderiv
  change fderiv ℝ (fun y : Space => (y 0) ^ 2 * (1 / 2) -
    y 2 * (y 1) ^ 2 * (1 / 2)) x d = _ at he
  have heq : objective = fun y : Space => (y 0) ^ 2 * (1 / 2) -
      y 2 * (y 1) ^ 2 * (1 / 2) := by funext y; simp [objective, div_eq_mul_inv]
  rw [heq]
  simp only [sub_apply, add_apply,
    smul_apply, smul_eq_mul, EuclideanSpace.coe_proj] at he
  convert he using 1
  ring

/-- The actual Hessian applies the symmetric bilinear polynomial coefficients. -/
theorem secondFDeriv_objective (x u v : Space) :
    fderiv ℝ (fderiv ℝ objective) x u v =
      u 0 * v 0 - x 2 * u 1 * v 1 - x 1 * (u 1 * v 2 + u 2 * v 1) := by
  have heq : fderiv ℝ objective = fun y : Space =>
      y 0 • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3) -
        (y 2 * y 1) • EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3) -
        ((y 1) ^ 2 / 2) • EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3) := by
    funext y
    ext d
    simp only [fderiv_objective, sub_apply,
      smul_apply, EuclideanSpace.coe_proj, smul_eq_mul]
    ring
  rw [heq]
  have h₀ := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).hasFDerivAt (x := x)
  have h₁ := (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).hasFDerivAt (x := x)
  have h₂ := (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).hasFDerivAt (x := x)
  have h := (h₀.smul_const (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3))).sub
    ((h₂.mul h₁).smul_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3))) |>.sub
    ((h₁.pow 2 |>.mul_const (1 / 2 : ℝ)).smul_const
      (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)))
  have he := congrArg (fun A : Space →L[ℝ] (Space →L[ℝ] ℝ) => A u v) h.fderiv
  simp only [div_eq_mul_inv]
  simp only [sub_apply, add_apply,
    ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul,
    EuclideanSpace.coe_proj] at he
  simp only [Pi.sub_def, Pi.mul_def, div_eq_mul_inv, one_mul, nsmul_eq_mul] at he ⊢
  convert he using 1
  norm_num
  ring

/-- The full first-order Taylor decrement in every ambient direction. -/
theorem taylorDecrement_one (x d : Space) :
    TaylorCriticality.taylorDecrement objective 1 x d =
      -x 0 * d 0 + x 2 * x 1 * d 1 + (x 1) ^ 2 * d 2 / 2 := by
  rw [TaylorCriticality.taylorDecrement_one, fderiv_objective]
  ring

/-- The full second-order Taylor decrement in every ambient direction. -/
theorem taylorDecrement_two (x d : Space) :
    TaylorCriticality.taylorDecrement objective 2 x d =
      -x 0 * d 0 + x 2 * x 1 * d 1 + (x 1) ^ 2 * d 2 / 2 -
        (d 0) ^ 2 / 2 + x 2 * (d 1) ^ 2 / 2 + x 1 * d 1 * d 2 := by
  rw [TaylorCriticality.taylorDecrement_two, fderiv_objective, secondFDeriv_objective]
  ring

/-- The second Taylor decrement differs from actual reduction by exactly the cubic term. -/
theorem reduction_eq (x d : Space) :
    objective x - objective (x + d) =
      TaylorCriticality.taylorDecrement objective 2 x d + d 2 * (d 1) ^ 2 / 2 := by
  rw [taylorDecrement_two]
  simp only [objective, PiLp.add_apply]
  ring

/-- The fixed feasible box. -/
def box : Set Space := {x | ∀ i, |x i| ≤ 2}

/-- Membership in the feasible box is the coordinate bound. -/
@[simp] theorem mem_box {x : Space} : x ∈ box ↔ ∀ i, |x i| ≤ 2 := Iff.rfl

/-- A specified point is feasible exactly when each coordinate satisfies its bound. -/
@[simp] theorem point_mem_box (a b c : ℝ) :
    point a b c ∈ box ↔ |a| ≤ 2 ∧ |b| ≤ 2 ∧ |c| ≤ 2 := by
  simp [box, Fin.forall_fin_succ]

/-- The feasible box is nonempty. -/
theorem box_nonempty : box.Nonempty := ⟨0, by simp [box]⟩

/-- The feasible box is closed in the ambient Euclidean space. -/
theorem isClosed_box : IsClosed box := by
  have heq : box = ⋂ i : Fin 3, {x : Space | |x i| ≤ 2} := by
    ext x; simp [box]
  rw [heq]
  exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const

/-- Every feasible point lies in the closed ball of radius four. -/
theorem box_subset_closedBall : box ⊆ closedBall 0 4 := by
  intro x hx
  have h₀ := (abs_le.mp (hx 0))
  have h₁ := (abs_le.mp (hx 1))
  have h₂ := (abs_le.mp (hx 2))
  have hs := norm_sq_eq x
  simp only [mem_closedBall, dist_zero_right]
  nlinarith [norm_nonneg x]

/-- The feasible box is compact. -/
theorem isCompact_box : IsCompact box :=
  (isCompact_closedBall (0 : Space) 4).of_isClosed_subset isClosed_box box_subset_closedBall

/-- The feasible box is convex. -/
theorem convex_box : Convex ℝ box := by
  have heq : box = ⋂ i : Fin 3, (fun x : Space => x i) ⁻¹' Icc (-2 : ℝ) 2 := by
    ext x
    simp [box, abs_le]
  rw [heq]
  exact convex_iInter fun i => (convex_Icc (-2 : ℝ) 2).linear_preimage
    (EuclideanSpace.proj (𝕜 := ℝ) i).toLinearMap

/-- The fixed lower bound holds on the whole feasible box. -/
theorem objective_lower_bound {x : Space} (hx : x ∈ box) : -4 ≤ objective x := by
  have h₁ := (abs_le.mp (hx 1))
  have h₂ := (abs_le.mp (hx 2))
  have hy : (x 1) ^ 2 ≤ 4 := by nlinarith
  have hm : x 2 * (x 1) ^ 2 ≤ 8 := by nlinarith [sq_nonneg (x 1)]
  unfold objective
  nlinarith [sq_nonneg (x 0)]

/-- Fixed anchored derivative bounds cover all feasible centers and every comparison point
in the open ball of radius five. The constants precede all algorithmic tolerances. -/
theorem exists_anchoredBoundedJets :
    ∃ L B : ℕ → ℝ, (∀ j, 1 ≤ L j) ∧ (∀ j, 1 ≤ B j) ∧
      ConstrainedTaylorCriticality.HasAnchoredBoundedJets objective 2 box (ball 0 5) false L B := by
  obtain ⟨L, B, hL, hB, h⟩ :=
    ConstrainedTaylorCriticality.exists_anchoredBoundedJets_of_contDiff 2
      (contDiff_objective 3) (by norm_num : (4 : ℝ) < 5)
  exact ⟨L, B, hL, hB, h.mono_centers box_subset_closedBall⟩

end Optimization.CoupledCubic
