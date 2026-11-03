import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Coleman–Li scaling

[conn2000trust], Section 13.12. The gradient and Hessian at the base point are
represented by their Euclidean coordinates. The scaled correction is the positive
gradient diagonal, which is defined even where the scaling matrix is singular.
-/

open Matrix
open scoped BigOperators

namespace ConnGouldToint.Chapter13

variable {ι : Type*}

/-- The vector in (13.12.1), including its extension to the boundary. -/
noncomputable def scalingVector (x g : ι → ℝ) (i : ι) : ℝ :=
  if 0 ≤ g i then x i else -1

/-- The diagonal Coleman–Li scaling in (13.12.2). -/
noncomputable def scalingMatrix [DecidableEq ι] (x g : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal fun i ↦ Real.sqrt |scalingVector x g i|

/-- First-order criticality on the nonnegative orthant, expressed by gradient
nonnegativity and complementarity. Feasibility is supplied separately. -/
def OrthantFirstOrder (x g : ι → ℝ) : Prop :=
  ∀ i, 0 ≤ g i ∧ (0 < x i → g i = 0)

/-- A direction in the nullspace of the active bound constraints. -/
def OrthantFaceDirection (x d : ι → ℝ) : Prop :=
  ∀ i, x i = 0 → d i = 0

section Finite

variable [Fintype ι] [DecidableEq ι]

/-- Weak second-order criticality on the orthant tests the Hessian on the
nullspace of all active bound constraints. -/
def OrthantWeakSecondOrder (x g : ι → ℝ) (H : Matrix ι ι ℝ) : Prop :=
  OrthantFirstOrder x g ∧ ∀ d, OrthantFaceDirection x d → 0 ≤ d ⬝ᵥ (H *ᵥ d)

/-- The scaled gradient. -/
noncomputable def scaledGradient (x g : ι → ℝ) : ι → ℝ :=
  scalingMatrix x g *ᵥ g

/-- The squared-scaled gradient in (13.12.4) admits a continuous
coordinate formula, despite the case distinction in the scaling. -/
theorem scaledResidual_apply (x g : ι → ℝ) (i : ι) :
    ((scalingMatrix x g * scalingMatrix x g) *ᵥ g) i =
      |x i| * max (g i) 0 + min (g i) 0 := by
  rw [scalingMatrix, Matrix.diagonal_mul_diagonal, Matrix.mulVec_diagonal,
    Real.mul_self_sqrt (abs_nonneg _)]
  by_cases h : 0 ≤ g i
  · simp [scalingVector, h]
  · have h' := (lt_of_not_ge h).le
    simp [scalingVector, h, max_eq_right h', min_eq_left h']

/-- The left side of the stationarity system (13.12.4) is continuous in the
point and gradient coordinates. -/
theorem continuous_scaledResidual :
    Continuous (fun xg : (ι → ℝ) × (ι → ℝ) ↦
      (scalingMatrix xg.1 xg.2 * scalingMatrix xg.1 xg.2) *ᵥ xg.2) := by
  apply continuous_pi
  intro i
  simp only [scaledResidual_apply]
  have hx : Continuous (fun xg : (ι → ℝ) × (ι → ℝ) ↦ xg.1 i) :=
    (continuous_apply i).comp continuous_fst
  have hg : Continuous (fun xg : (ι → ℝ) × (ι → ℝ) ↦ xg.2 i) :=
    (continuous_apply i).comp continuous_snd
  exact (hx.abs.mul (hg.max continuous_const)).add (hg.min continuous_const)

/-- A short step along the scaled descent ray retains at least the prescribed
fraction of each coordinate. This gives the feasibility bound used in Theorem 13.12.3. -/
theorem scaledRay_coordinate_lower_bound {x g : ι → ℝ} (hx : ∀ i, 0 ≤ x i)
    {t κ σ : ℝ} (ht : 0 ≤ t) (hσ : σ ≤ 1) (hκ : 0 < κ)
    (hg : ∀ i, g i ≤ κ) (hlen : t ≤ (1 - σ) / κ) (i : ι) :
    σ * x i ≤ x i - t * ((scalingMatrix x g * scalingMatrix x g) *ᵥ g) i := by
  rw [scaledResidual_apply]
  by_cases hgi : 0 ≤ g i
  · rw [abs_of_nonneg (hx i), max_eq_left hgi, min_eq_right hgi, add_zero]
    have hmul : t * g i ≤ 1 - σ :=
      (mul_le_mul_of_nonneg_left (hg i) ht).trans ((le_div_iff₀ hκ).mp hlen)
    have h := mul_le_mul_of_nonneg_left hmul (hx i)
    nlinarith only [h]
  · have hgi' := (lt_of_not_ge hgi).le
    rw [max_eq_right hgi', min_eq_left hgi', mul_zero, zero_add]
    have h := mul_le_mul_of_nonneg_right hσ (hx i)
    linarith [mul_nonpos_of_nonneg_of_nonpos ht hgi']

/-- The positive part of the gradient on the diagonal, written `Ḡ` in the book. -/
noncomputable def scaledCorrection (g : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal fun i ↦ max (g i) 0

/-- The Hessian of the scaled model in (13.12.7). -/
noncomputable def scaledHessian (x g : ι → ℝ) (H : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  scalingMatrix x g * H * scalingMatrix x g + scaledCorrection g

/-- The original quadratic model (13.12.5), in displacement coordinates. -/
noncomputable def affineQuadraticModel (c : ℝ) (g : ι → ℝ) (H : Matrix ι ι ℝ)
    (s : ι → ℝ) : ℝ :=
  c + g ⬝ᵥ s + (1 / 2) * (s ⬝ᵥ (H *ᵥ s))

/-- The scaled Newton system (13.12.6). -/
def IsScaledNewtonStep (x g : ι → ℝ) (H : Matrix ι ι ℝ) (w : ι → ℝ) : Prop :=
  scaledHessian x g H *ᵥ w = -scaledGradient x g

/-- The scaled quadratic model (13.12.7) evaluated in displacement coordinates. -/
noncomputable def scaledModel (c : ℝ) (x g : ι → ℝ) (H : Matrix ι ι ℝ) (w : ι → ℝ) : ℝ :=
  affineQuadraticModel c (scaledGradient x g) (scaledHessian x g H) w

/-- The model correction in original coordinates. The congruence formula
relating it to the scaled correction is used only at strictly interior points. -/
noncomputable def unscaledCorrection (x g : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal fun i ↦ max (g i) 0 / |scalingVector x g i|

/-- The corrected quadratic model in the original displacement coordinates, (13.12.8). -/
noncomputable def unscaledModel (c : ℝ) (x g : ι → ℝ) (H : Matrix ι ι ℝ) (s : ι → ℝ) : ℝ :=
  affineQuadraticModel c g (H + unscaledCorrection x g) s

private theorem vecMul_scalingMatrix (x g w : ι → ℝ) :
    w ᵥ* scalingMatrix x g = scalingMatrix x g *ᵥ w := by
  ext i
  simp [scalingMatrix, Matrix.vecMul_diagonal, Matrix.mulVec_diagonal, mul_comm]

private theorem scaling_pullback_form (x g w : ι → ℝ) (A : Matrix ι ι ℝ) :
    w ⬝ᵥ ((scalingMatrix x g * A * scalingMatrix x g) *ᵥ w) =
      (scalingMatrix x g *ᵥ w) ⬝ᵥ (A *ᵥ (scalingMatrix x g *ᵥ w)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    vecMul_scalingMatrix]

/-- At interior points, the congruence of the unscaled correction is the
positive-gradient diagonal used in the scaled model. -/
theorem scaling_unscaledCorrection {x g : ι → ℝ} (hx : ∀ i, 0 < x i) :
    scalingMatrix x g * unscaledCorrection x g * scalingMatrix x g = scaledCorrection g := by
  unfold scalingMatrix unscaledCorrection scaledCorrection
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  have hv : 0 < |scalingVector x g i| := by
    by_cases h : 0 ≤ g i
    · simpa [scalingVector, h, abs_of_pos (hx i)] using hx i
    · simp [scalingVector, h]
  have hs := Real.sq_sqrt hv.le
  field_simp
  rw [hs, mul_comm]

/-- In the strict interior the scaled and unscaled models agree under the
change of variables `s = S w`. -/
theorem scaledModel_eq_unscaledModel (c : ℝ) {x g : ι → ℝ} (hx : ∀ i, 0 < x i)
    (H : Matrix ι ι ℝ) (w : ι → ℝ) :
    scaledModel c x g H w = unscaledModel c x g H (scalingMatrix x g *ᵥ w) := by
  have hess : scalingMatrix x g * (H + unscaledCorrection x g) * scalingMatrix x g =
      scaledHessian x g H := by
    rw [Matrix.mul_add, Matrix.add_mul, scaling_unscaledCorrection hx, scaledHessian]
  have hlin : (scalingMatrix x g *ᵥ g) ⬝ᵥ w = g ⬝ᵥ (scalingMatrix x g *ᵥ w) := by
    rw [dotProduct_comm (scalingMatrix x g *ᵥ g), Matrix.dotProduct_mulVec, vecMul_scalingMatrix,
      dotProduct_comm]
  unfold scaledModel unscaledModel affineQuadraticModel scaledGradient
  rw [← hess, scaling_pullback_form, hlin]


omit [DecidableEq ι] in
/-- Gradient nonnegativity and complementarity are the variational first-order
condition on the nonnegative orthant. -/
theorem orthantFirstOrder_iff_variational {x g : ι → ℝ} (hx : ∀ i, 0 ≤ x i) :
    OrthantFirstOrder x g ↔ ∀ y : ι → ℝ, (∀ i, 0 ≤ y i) → 0 ≤ g ⬝ᵥ (y - x) := by
  classical
  constructor
  · intro h y hy
    apply Finset.sum_nonneg
    intro i _
    change 0 ≤ g i * (y i - x i)
    rcases (hx i).eq_or_lt with hxi | hxi
    · rw [← hxi, sub_zero]
      exact mul_nonneg (h i).1 (hy i)
    · simp [(h i).2 hxi]
  · intro h i
    have hplus : ∀ j, 0 ≤ (x + Pi.single i (1 : ℝ) : ι → ℝ) j := by
      intro j
      by_cases hj : j = i
      · subst j
        simpa using add_nonneg (hx i) zero_le_one
      · simpa [Pi.single_eq_of_ne hj] using hx j
    have hgi := h _ hplus
    rw [add_sub_cancel_left, dotProduct_single, mul_one] at hgi
    refine ⟨hgi, fun hxi ↦ ?_⟩
    have hminus : ∀ j, 0 ≤ (x + Pi.single i (-x i) : ι → ℝ) j := by
      intro j
      by_cases hj : j = i
      · subst j
        simp
      · simpa [Pi.single_eq_of_ne hj] using hx j
    have hgi' := h _ hminus
    rw [add_sub_cancel_left, dotProduct_single, mul_neg, neg_nonneg] at hgi'
    exact le_antisymm (nonpos_of_mul_nonpos_left hgi' hxi) hgi

private theorem scaledGradient_eq_zero_iff {x g : ι → ℝ} (hx : ∀ i, 0 ≤ x i) :
    scaledGradient x g = 0 ↔ OrthantFirstOrder x g := by
  constructor
  · intro h i
    have he := congrFun h i
    simp only [scaledGradient, scalingMatrix, Matrix.mulVec_diagonal, Pi.zero_apply] at he
    have hg : 0 ≤ g i := by
      by_contra! hgi
      have hz : g i = 0 := by simpa [scalingVector, not_le.mpr hgi] using he
      exact hgi.ne hz
    refine ⟨hg, fun hxi ↦ ?_⟩
    rw [scalingVector, ite_eq_left hg, abs_of_nonneg (hx i)] at he
    exact (mul_eq_zero.mp he).resolve_left (Real.sqrt_pos.2 hxi).ne'
  · intro h
    ext i
    rw [scaledGradient, scalingMatrix, Matrix.mulVec_diagonal, Pi.zero_apply,
      scalingVector, ite_eq_left (h i).1, abs_of_nonneg (hx i)]
    rcases (hx i).eq_or_lt with hxi | hxi
    · simp [← hxi]
    · simp [(h i).2 hxi]

/-- Theorem 13.12.1. Both scaled forms of the gradient vanish precisely at
first-order critical points of the orthant problem. -/
theorem theorem_13_12_1 {x g : ι → ℝ} (hx : ∀ i, 0 ≤ x i) :
    OrthantFirstOrder x g ↔
      (scalingMatrix x g * scalingMatrix x g) *ᵥ g = 0 ∧ scaledGradient x g = 0 := by
  constructor
  · intro h
    have hg := (scaledGradient_eq_zero_iff hx).mpr h
    exact ⟨by rw [← Matrix.mulVec_mulVec, show scalingMatrix x g *ᵥ g = 0 from hg,
      Matrix.mulVec_zero], hg⟩
  · intro h
    exact (scaledGradient_eq_zero_iff hx).mp h.2

private theorem scale_apply_of_firstOrder {x g : ι → ℝ} (hx : ∀ i, 0 ≤ x i)
    (hg : OrthantFirstOrder x g) (w : ι → ℝ) (i : ι) :
    (scalingMatrix x g *ᵥ w) i = Real.sqrt (x i) * w i := by
  simp [scalingMatrix, Matrix.mulVec_diagonal, scalingVector, (hg i).1, abs_of_nonneg (hx i)]

private theorem scaledHessian_isSymm (x g : ι → ℝ) {H : Matrix ι ι ℝ} (hH : H.IsSymm) :
    (scaledHessian x g H).IsSymm := by
  have hA : (scalingMatrix x g * H * scalingMatrix x g).IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    simp only [scalingMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [hH.apply i j]
    ring
  exact hA.add (Matrix.isSymm_diagonal _)

private theorem scaledHessian_form (x g w : ι → ℝ) (H : Matrix ι ι ℝ) :
    w ⬝ᵥ (scaledHessian x g H *ᵥ w) =
      (scalingMatrix x g *ᵥ w) ⬝ᵥ (H *ᵥ (scalingMatrix x g *ᵥ w)) +
        ∑ i, max (g i) 0 * (w i) ^ 2 := by
  rw [scaledHessian, Matrix.add_mulVec, dotProduct_add, scaling_pullback_form]
  congr 1
  unfold dotProduct scaledCorrection
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mulVec_diagonal]
  ring

/-- Theorem 13.12.2. Scaled stationarity and positive semidefiniteness of the
scaled Hessian characterize weak second-order criticality. The positive
gradient correction contributes on active coordinates and vanishes on the
chosen preimage of an active-face direction. -/
theorem theorem_13_12_2 {x g : ι → ℝ} (hx : ∀ i, 0 ≤ x i) {H : Matrix ι ι ℝ}
    (hH : H.IsSymm) :
    (scaledGradient x g = 0 ↔ OrthantFirstOrder x g) ∧
    (scaledGradient x g = 0 ∧ (scaledHessian x g H).PosSemidef ↔
      OrthantWeakSecondOrder x g H) := by
  refine ⟨scaledGradient_eq_zero_iff hx, ?_⟩
  constructor
  · rintro ⟨hg, hp⟩
    have hfirst := (scaledGradient_eq_zero_iff hx).mp hg
    refine ⟨hfirst, fun d hd ↦ ?_⟩
    let w (i : ι) := d i / Real.sqrt (x i)
    have hw : scalingMatrix x g *ᵥ w = d := by
      ext i
      rw [scale_apply_of_firstOrder hx hfirst]
      by_cases hxi : x i = 0
      · simp [hxi, hd i hxi]
      · have hp := Real.sqrt_pos.mpr (lt_of_le_of_ne (hx i) (Ne.symm hxi))
        dsimp [w]
        field_simp [hp.ne']
    have hsum : (∑ i, max (g i) 0 * (w i) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hxi : x i = 0
      · simp [w, hxi]
      · simp [(hfirst i).2 (lt_of_le_of_ne (hx i) (Ne.symm hxi))]
    have hh := hp.dotProduct_mulVec_nonneg w
    have hstar : star w = w := by ext i; simp
    rwa [hstar, scaledHessian_form, hw, hsum, add_zero] at hh
  · rintro ⟨hg, hh⟩
    refine ⟨(scaledGradient_eq_zero_iff hx).mpr hg, Matrix.posSemidef_iff_dotProduct_mulVec.mpr
      ⟨isHermitian_iff_isSymm.mpr (scaledHessian_isSymm x g hH), fun w ↦ ?_⟩⟩
    have hstar : star w = w := by ext i; simp
    rw [hstar, scaledHessian_form]
    apply add_nonneg
    · apply hh
      intro i hi
      rw [scale_apply_of_firstOrder hx hg, hi, Real.sqrt_zero, zero_mul]
    · exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (le_max_right _ _) (sq_nonneg _)

end Finite

end ConnGouldToint.Chapter13
