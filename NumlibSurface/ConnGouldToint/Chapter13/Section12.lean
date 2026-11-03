import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Optimization.LogBarrier
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

open Matrix Metric
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

/-- The Euclidean norm of the scaled gradient. -/
noncomputable def scaledGradientNorm (x g : ι → ℝ) : ℝ :=
  ‖WithLp.toLp 2 (scaledGradient x g)‖

/-- Euclidean distance to the frontier of the nonnegative orthant,
with the vectors written in their coordinates. -/
noncomputable def orthantBoundaryDistance (x : ι → ℝ) : ℝ :=
  sInf ((fun y : ι → ℝ ↦ ‖WithLp.toLp 2 (x - y)‖) ''
    frontier (Optimization.nonnegativeOrthant ι))

omit [DecidableEq ι] in
private theorem orthantBoundaryDistance_le_coordinate {x : ι → ℝ}
    (hx : ∀ i, 0 < x i) (i : ι) : orthantBoundaryDistance x ≤ x i := by
  classical
  let y := Function.update x i 0
  have hy : y ∈ frontier (Optimization.nonnegativeOrthant ι) := by
    refine Optimization.mem_frontier_nonnegativeOrthant.mpr ⟨fun j ↦ ?_, i, by simp [y]⟩
    by_cases h : j = i
    · simp [y, h]
    · simpa [y, Function.update_of_ne h] using (hx j).le
  have hb : BddBelow ((fun z : ι → ℝ ↦ ‖WithLp.toLp 2 (x - z)‖) ''
      frontier (Optimization.nonnegativeOrthant ι)) :=
    ⟨0, by rintro _ ⟨z, _, rfl⟩; exact norm_nonneg _⟩
  have hsq : ‖WithLp.toLp 2 (x - y)‖ ^ 2 = (x i) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Finset.sum_eq_single i]
    · simp [y]
    · intro j _ hj
      simp [y, Function.update_of_ne hj]
    · simp
  have hn := (sq_le_sq₀ (norm_nonneg _) (hx i).le).mp hsq.le
  exact (csInf_le hb ⟨y, hy, rfl⟩).trans hn

/-- The feasible times on the scaled Cauchy ray, as printed in (13.12.11).
At an interior point the scaled norm of the original ray direction is
the Euclidean norm of the scaled gradient. -/
def scaledCauchyTimes (x g : ι → ℝ) (Δ σ : ℝ) : Set ℝ :=
  {t | 0 ≤ t ∧ t * scaledGradientNorm x g ≤ Δ ∧
    σ * orthantBoundaryDistance x ≤
      orthantBoundaryDistance (x - t • ((scalingMatrix x g * scalingMatrix x g) *ᵥ g))}

/-- A minimizing feasible time along the constrained scaled Cauchy ray. -/
def IsScaledCauchyTime (c : ℝ) (x g : ι → ℝ) (H : Matrix ι ι ℝ) (Δ σ tC : ℝ) : Prop :=
  tC ∈ scaledCauchyTimes x g Δ σ ∧
    IsMinOn (fun t : ℝ ↦ unscaledModel c x g H
      ((-t) • ((scalingMatrix x g * scalingMatrix x g) *ᵥ g)))
      (scaledCauchyTimes x g Δ σ) tC

private theorem scaledGradientNorm_sq (x g : ι → ℝ) :
    scaledGradientNorm x g ^ 2 = scaledGradient x g ⬝ᵥ scaledGradient x g := by
  rw [scaledGradientNorm, EuclideanSpace.real_norm_sq_eq]
  unfold dotProduct
  simp only [pow_two]

/-- The model along the scaled Cauchy ray. The curvature is that of the
corrected scaled model, including the positive gradient diagonal. -/
theorem unscaledModel_along_scaledRay (c : ℝ) {x g : ι → ℝ} (hx : ∀ i, 0 < x i)
    (H : Matrix ι ι ℝ) (t : ℝ) :
    unscaledModel c x g H ((-t) • ((scalingMatrix x g * scalingMatrix x g) *ᵥ g)) =
      c - t * scaledGradientNorm x g ^ 2 +
        (1 / 2) * t ^ 2 * (scaledGradient x g ⬝ᵥ (scaledHessian x g H *ᵥ scaledGradient x g)) := by
  have hscale : scalingMatrix x g *ᵥ ((-t) • scaledGradient x g) =
      (-t) • ((scalingMatrix x g * scalingMatrix x g) *ᵥ g) := by
    rw [Matrix.mulVec_smul, scaledGradient, Matrix.mulVec_mulVec]
  rw [← hscale, ← scaledModel_eq_unscaledModel c hx, scaledModel, affineQuadraticModel]
  simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    ← scaledGradientNorm_sq]
  ring

private theorem scaledCauchyTimes_of_cap [Nonempty ι] {x g : ι → ℝ}
    (hx : ∀ i, 0 < x i) {Δ σ t κ : ℝ} (hσ₀ : 0 < σ) (hσ : σ ≤ 1)
    (hκ : 0 < κ) (hg : ∀ i, g i ≤ κ) (ht : 0 ≤ t)
    (hΔ : t * scaledGradientNorm x g ≤ Δ) (hcap : t ≤ (1 - σ) / κ) :
    t ∈ scaledCauchyTimes x g Δ σ := by
  refine ⟨ht, hΔ, ?_⟩
  let C := Optimization.nonnegativeOrthant ι
  let y := x - t • ((scalingMatrix x g * scalingMatrix x g) *ᵥ g)
  change σ * orthantBoundaryDistance x ≤ orthantBoundaryDistance y
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hfront : (frontier C).Nonempty :=
    ⟨0, Optimization.mem_frontier_nonnegativeOrthant.mpr ⟨fun _ ↦ le_rfl, i, rfl⟩⟩
  apply le_csInf (hfront.image (fun z : ι → ℝ ↦ ‖WithLp.toLp 2 (y - z)‖))
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨_, j, hj⟩ := Optimization.mem_frontier_nonnegativeOrthant.mp hz
  have hjlow : σ * x j ≤ y j :=
    scaledRay_coordinate_lower_bound (fun i ↦ (hx i).le) ht hσ hκ hg hcap j
  have hypos := (mul_pos hσ₀ (hx j)).trans_le hjlow
  calc
    σ * orthantBoundaryDistance x ≤ σ * x j :=
      mul_le_mul_of_nonneg_left (orthantBoundaryDistance_le_coordinate hx j) hσ₀.le
    _ ≤ y j := hjlow
    _ = ‖(WithLp.toLp 2 (y - z) : EuclideanSpace ℝ ι) j‖ := by
      simp [hj, Real.norm_eq_abs, abs_of_pos hypos]
    _ ≤ ‖WithLp.toLp 2 (y - z)‖ := PiLp.norm_apply_le _ _

/-- Corrected Theorem 13.12.3. The fraction-to-boundary cap controls the ray
parameter, so it enters the minimum in the step-length bound before multiplying
by the squared scaled gradient norm. The curvature hypothesis is the upper
bound along the ray supplied by (8.1.22). -/
theorem theorem_13_12_3 [Nonempty ι] (c : ℝ) {x g : ι → ℝ} (hx : ∀ i, 0 < x i)
    (H : Matrix ι ι ℝ) {Δ σ κ β tC : ℝ} (hΔ : 0 ≤ Δ) (hσ₀ : 0 < σ) (hσ : σ < 1)
    (hκ : 0 < κ) (hg : ∀ i, g i ≤ κ) (hβ : 0 < β)
    (hcurv : scaledGradient x g ⬝ᵥ (scaledHessian x g H *ᵥ scaledGradient x g) ≤
      β * scaledGradientNorm x g ^ 2)
    (hmin : IsScaledCauchyTime c x g H Δ σ tC) :
    (1 / 2) * scaledGradientNorm x g ^ 2 *
      min (1 / β) (min (Δ / scaledGradientNorm x g) ((1 - σ) / κ)) ≤
      c - unscaledModel c x g H ((-tC) • ((scalingMatrix x g * scalingMatrix x g) *ᵥ g)) := by
  let n := scaledGradientNorm x g
  let t := min (1 / β) (min (Δ / n) ((1 - σ) / κ))
  have hn : 0 ≤ n := norm_nonneg _
  have ht : 0 ≤ t := le_min (div_nonneg zero_le_one hβ.le)
    (le_min (div_nonneg hΔ hn) (div_nonneg (sub_nonneg.mpr hσ.le) hκ.le))
  have htβ : t * β ≤ 1 := (le_div_iff₀ hβ).mp (min_le_left _ _)
  have htΔ : t * n ≤ Δ := by
    rcases hn.eq_or_lt with hn₀ | hn'
    · simpa [← hn₀] using hΔ
    · exact (le_div_iff₀ hn').mp ((min_le_right _ _).trans (min_le_left _ _))
  have hcap : t ≤ (1 - σ) / κ := (min_le_right _ _).trans (min_le_right _ _)
  have hfeas := scaledCauchyTimes_of_cap hx hσ₀ hσ.le hκ hg ht htΔ hcap
  have hcmp := isMinOn_iff.mp hmin.2 t hfeas
  change unscaledModel c x g H ((-tC) • ((scalingMatrix x g * scalingMatrix x g) *ᵥ g)) ≤
    unscaledModel c x g H ((-t) • ((scalingMatrix x g * scalingMatrix x g) *ᵥ g)) at hcmp
  rw [unscaledModel_along_scaledRay c hx H t] at hcmp
  have hq : t ^ 2 * (scaledGradient x g ⬝ᵥ (scaledHessian x g H *ᵥ scaledGradient x g)) ≤
      t * n ^ 2 := calc
    _ ≤ t ^ 2 * (β * n ^ 2) := mul_le_mul_of_nonneg_left hcurv (sq_nonneg t)
    _ = (t * β) * (t * n ^ 2) := by ring
    _ ≤ 1 * (t * n ^ 2) := mul_le_mul_of_nonneg_right htβ (mul_nonneg ht (sq_nonneg _))
    _ = _ := one_mul _
  change (1 / 2) * n ^ 2 * t ≤ _
  change _ ≤ c - t * n ^ 2 +
    (1 / 2) * t ^ 2 * (scaledGradient x g ⬝ᵥ (scaledHessian x g H *ᵥ scaledGradient x g)) at hcmp
  nlinarith only [hcmp, hq]

end Finite

/-! ### Counterexample to the literal Cauchy bound -/

/-- In one dimension, with unit gradient and zero objective-model Hessian,
the corrected unscaled model at a positive base point has curvature `1/x`. -/
noncomputable def scalarColemanLiModel (x s : ℝ) : ℝ :=
  s + (1 / 2) * (1 / x) * s ^ 2

/-- The scalar example is the original-coordinate Coleman–Li model for
a unit gradient and zero objective-model Hessian. -/
theorem scalarColemanLiModel_eq_unscaledModel {x : ℝ} (hx : 0 < x) (s : ℝ) :
    scalarColemanLiModel x s =
      unscaledModel 0 (fun _ : Fin 1 ↦ x) (fun _ ↦ 1) 0 (fun _ ↦ s) := by
  simp [scalarColemanLiModel, unscaledModel, affineQuadraticModel, unscaledCorrection,
    scalingVector, abs_of_pos hx, dotProduct, Matrix.mulVec_diagonal]
  ring

/-- The scaled gradient in the scalar example has Euclidean norm `√x`. -/
theorem scalarColemanLiGradientNorm {x : ℝ} (hx : 0 < x) :
    scaledGradientNorm (fun _ : Fin 1 ↦ x) (fun _ ↦ 1) = Real.sqrt x := by
  have h : scaledGradient (fun _ : Fin 1 ↦ x) (fun _ ↦ 1) = fun _ ↦ Real.sqrt x := by
    funext i
    simp [scaledGradient, scalingMatrix, Matrix.mulVec_diagonal, scalingVector, abs_of_pos hx]
  rw [scaledGradientNorm, h, EuclideanSpace.norm_eq]
  simp

/-- The scaled norm of the scalar ray direction is the square root of the
positive base point. -/
theorem scalarColemanLiRayNorm {x : ℝ} (hx : 0 < x) :
    |x / Real.sqrt x| = Real.sqrt x := by
  have hs := Real.sqrt_pos.mpr hx
  rw [abs_of_nonneg (div_nonneg hx.le hs.le), div_eq_iff hs.ne']
  nlinarith [Real.sq_sqrt hx.le]

/-- The printed curvature bound (8.1.22) is two in this example: the
scaled correction has scalar curvature one. -/
theorem scalarColemanLiCurvature {x : ℝ} (hx : 0 < x) :
    1 + |Real.sqrt x * (1 / x) * Real.sqrt x| = 2 := by
  have h : Real.sqrt x * (1 / x) * Real.sqrt x = 1 := by
    field_simp [hx.ne']
    rw [Real.sq_sqrt hx.le]
  rw [h, abs_one]
  norm_num

/-- The fraction-to-boundary condition from (13.12.11) in one dimension.
The boundary of the nonnegative half-line is the singleton zero. -/
def scalarColemanLiTimes (x : ℝ) : Set ℝ :=
  {t | 0 ≤ t ∧ t * Real.sqrt x ≤ 1 ∧
    (9 / 10) * infDist x (frontier (Set.Ici (0 : ℝ))) ≤
      infDist (x - t * x) (frontier (Set.Ici (0 : ℝ)))}

private theorem scalarColemanLiTimes_iff {x t : ℝ} (hx : 0 < x) :
    t ∈ scalarColemanLiTimes x ↔
      0 ≤ t ∧ t * Real.sqrt x ≤ 1 ∧ (9 / 10 : ℝ) ≤ |1 - t| := by
  change (0 ≤ t ∧ t * Real.sqrt x ≤ 1 ∧
    (9 / 10) * infDist x (frontier (Set.Ici (0 : ℝ))) ≤
      infDist (x - t * x) (frontier (Set.Ici (0 : ℝ)))) ↔ _
  rw [frontier_Ici, infDist_singleton, infDist_singleton, Real.dist_eq, Real.dist_eq,
    sub_zero, sub_zero, abs_of_pos hx, show x - t * x = (1 - t) * x by ring,
    abs_mul, abs_of_pos hx, mul_le_mul_iff_of_pos_right hx]

private theorem orthantBoundaryDistance_fin_one (x : ℝ) :
    orthantBoundaryDistance (fun _ : Fin 1 ↦ x) = |x| := by
  have hfront : frontier (Optimization.nonnegativeOrthant (Fin 1)) = {0} := by
    ext z
    simp only [Optimization.mem_frontier_nonnegativeOrthant, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, i, hi⟩
      funext j
      rw [Subsingleton.elim j i, hi, Pi.zero_apply]
    · rintro rfl
      exact ⟨fun _ ↦ le_rfl, 0, rfl⟩
  rw [orthantBoundaryDistance, hfront, Set.image_singleton, csInf_singleton,
    EuclideanSpace.norm_eq]
  simp [Real.norm_eq_abs, Real.sqrt_sq_eq_abs]

private theorem scaledResidual_fin_one {x : ℝ} (hx : 0 < x) :
    (scalingMatrix (fun _ : Fin 1 ↦ x) (fun _ ↦ 1) *
      scalingMatrix (fun _ : Fin 1 ↦ x) (fun _ ↦ 1)) *ᵥ (fun _ ↦ 1) =
    fun _ ↦ x := by
  funext i
  rw [scaledResidual_apply]
  norm_num [abs_of_pos hx]

/-- The scalar feasible times are exactly the times of (13.12.11) for the
one-coordinate matrix model at radius one and boundary fraction nine tenths. -/
theorem scalarColemanLiTimes_eq_scaledCauchyTimes {x : ℝ} (hx : 0 < x) :
    scalarColemanLiTimes x =
      scaledCauchyTimes (fun _ : Fin 1 ↦ x) (fun _ ↦ 1) 1 (9 / 10) := by
  ext t
  change (0 ≤ t ∧ t * Real.sqrt x ≤ 1 ∧
    (9 / 10) * infDist x (frontier (Set.Ici (0 : ℝ))) ≤
      infDist (x - t * x) (frontier (Set.Ici (0 : ℝ)))) ↔
    (0 ≤ t ∧ t * scaledGradientNorm (fun _ : Fin 1 ↦ x) (fun _ ↦ 1) ≤ 1 ∧
      (9 / 10) * orthantBoundaryDistance (fun _ : Fin 1 ↦ x) ≤
        orthantBoundaryDistance ((fun _ : Fin 1 ↦ x) - t •
          ((scalingMatrix (fun _ : Fin 1 ↦ x) (fun _ ↦ 1) *
            scalingMatrix (fun _ : Fin 1 ↦ x) (fun _ ↦ 1)) *ᵥ (fun _ ↦ 1))))
  rw [scaledResidual_fin_one hx, scalarColemanLiGradientNorm hx]
  have hvec : ((fun _ : Fin 1 ↦ x) - t • (fun _ : Fin 1 ↦ x)) =
      fun _ ↦ x - t * x := by
    funext i
    rfl
  rw [hvec, orthantBoundaryDistance_fin_one, orthantBoundaryDistance_fin_one, frontier_Ici,
    infDist_singleton, infDist_singleton, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero]

private theorem scalarColemanLiModel_onRay {x : ℝ} (hx : 0 < x) (t : ℝ) :
    scalarColemanLiModel x (-t * x) = -(x * (t - t ^ 2 / 2)) := by
  unfold scalarColemanLiModel
  field_simp [hx.ne']
  ring

/-- For any proposed positive criticality cap in the literal Theorem 13.12.3,
there is a strictly interior scalar base point with a constrained scaled
Cauchy minimizer that violates the claimed decrease. The trust-region radius
and upper gradient bound are both one, and the boundary fraction is nine tenths. -/
theorem theorem_13_12_3_counterexample (κmsd : ℝ) (hκ : 0 < κmsd) :
    ∃ x t : ℝ, 0 < x ∧ t ∈ scalarColemanLiTimes x ∧ 0 < x - t * x ∧
      IsMinOn (fun u ↦ scalarColemanLiModel x (-u * x)) (scalarColemanLiTimes x) t ∧
      scalarColemanLiModel x 0 - scalarColemanLiModel x (-t * x) <
        (1 / 2) * min (Real.sqrt x) κmsd * min (min (Real.sqrt x) κmsd / 2) 1 := by
  let a := min 1 κmsd
  have ha : 0 < a := lt_min zero_lt_one hκ
  let x := a ^ 2
  have hx : 0 < x := pow_pos ha _
  have hsqrt : Real.sqrt x = a := Real.sqrt_sq ha.le
  have ha₁ : a ≤ 1 := min_le_left _ _
  have haκ : a ≤ κmsd := min_le_right _ _
  refine ⟨x, 1 / 10, hx, ?_, by linarith, ?_, ?_⟩
  · rw [scalarColemanLiTimes_iff hx, hsqrt]
    norm_num
    linarith
  · apply isMinOn_iff.mpr
    intro u hu
    rw [scalarColemanLiModel_onRay hx, scalarColemanLiModel_onRay hx]
    have hd := ((scalarColemanLiTimes_iff hx).mp hu).2.2
    have hs : (9 / 10 : ℝ) ^ 2 ≤ (1 - u) ^ 2 := by
      rw [← sq_abs (1 - u)]
      exact pow_le_pow_left₀ (by norm_num) hd _
    have hb : u - u ^ 2 / 2 ≤ 19 / 200 := by nlinarith
    have hc := mul_le_mul_of_nonneg_left hb hx.le
    nlinarith only [hc]
  · rw [scalarColemanLiModel_onRay hx, hsqrt, min_eq_left haκ,
      min_eq_left (show a / 2 ≤ 1 by linarith)]
    simp only [scalarColemanLiModel, zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero, zero_sub,
      neg_neg]
    dsimp [x] at hx ⊢
    nlinarith only [hx]

/-- The counterexample in the matrix notation of (13.12.7)–(13.12.11).
Here `xv` is strictly positive, `gv` is the unit gradient, and the uncorrected
objective-model Hessian is zero. The curvature bound is two by
`scalarColemanLiCurvature`. -/
theorem theorem_13_12_3_matrix_counterexample (κmsd : ℝ) (hκ : 0 < κmsd) :
    ∃ x t : ℝ, 0 < x ∧
      let xv : Fin 1 → ℝ := fun _ ↦ x
      let gv : Fin 1 → ℝ := fun _ ↦ 1
      let π := min (scaledGradientNorm xv gv) κmsd
      IsScaledCauchyTime 0 xv gv 0 1 (9 / 10) t ∧
        unscaledModel 0 xv gv 0 0 -
          unscaledModel 0 xv gv 0 ((-t) • ((scalingMatrix xv gv * scalingMatrix xv gv) *ᵥ gv)) <
        (1 / 2) * π * min (π / 2) 1 := by
  obtain ⟨x, t, hx, ht, _, hm, hlt⟩ := theorem_13_12_3_counterexample κmsd hκ
  let xv : Fin 1 → ℝ := fun _ ↦ x
  let gv : Fin 1 → ℝ := fun _ ↦ 1
  have hray (u : ℝ) : unscaledModel 0 xv gv 0
      ((-u) • ((scalingMatrix xv gv * scalingMatrix xv gv) *ᵥ gv)) =
        scalarColemanLiModel x (-u * x) := by
    rw [show (scalingMatrix xv gv * scalingMatrix xv gv) *ᵥ gv = xv from scaledResidual_fin_one hx]
    exact (scalarColemanLiModel_eq_unscaledModel hx (-u * x)).symm
  have htimes : scalarColemanLiTimes x = scaledCauchyTimes xv gv 1 (9 / 10) :=
    scalarColemanLiTimes_eq_scaledCauchyTimes hx
  refine ⟨x, t, hx, ⟨htimes ▸ ht, ?_⟩, ?_⟩
  · apply isMinOn_iff.mpr
    intro u hu
    change unscaledModel 0 xv gv 0
        ((-t) • ((scalingMatrix xv gv * scalingMatrix xv gv) *ᵥ gv)) ≤
      unscaledModel 0 xv gv 0 ((-u) • ((scalingMatrix xv gv * scalingMatrix xv gv) *ᵥ gv))
    rw [hray t, hray u]
    exact isMinOn_iff.mp hm u (htimes.symm ▸ hu)
  · change unscaledModel 0 xv gv 0 0 -
        unscaledModel 0 xv gv 0 ((-t) • ((scalingMatrix xv gv * scalingMatrix xv gv) *ᵥ gv)) <
      (1 / 2) * min (scaledGradientNorm xv gv) κmsd *
        min (min (scaledGradientNorm xv gv) κmsd / 2) 1
    rw [hray, show scaledGradientNorm xv gv = Real.sqrt x from scalarColemanLiGradientNorm hx]
    exact (scalarColemanLiModel_eq_unscaledModel hx 0) ▸ hlt

end ConnGouldToint.Chapter13
