import NumlibSurface.ConnGouldToint.Chapter06.Section06
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Matrix
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

open Matrix Metric Filter
open scoped BigOperators Topology

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

/-- The scaled gradient is continuous in the point and gradient coordinates.
Multiplication by the gradient removes the discontinuity at a sign change. -/
theorem continuous_scaledGradient :
    Continuous (fun xg : (ι → ℝ) × (ι → ℝ) ↦ scaledGradient xg.1 xg.2) := by
  have hform (x g : ι → ℝ) (i : ι) :
      scaledGradient x g i = Real.sqrt |x i| * max (g i) 0 + min (g i) 0 := by
    rw [scaledGradient, scalingMatrix, Matrix.mulVec_diagonal]
    by_cases h : 0 ≤ g i
    · simp [scalingVector, h]
    · have h' := (lt_of_not_ge h).le
      simp [scalingVector, h, max_eq_right h', min_eq_left h']
  apply continuous_pi
  intro i
  simp only [hform]
  have hx : Continuous (fun xg : (ι → ℝ) × (ι → ℝ) ↦ xg.1 i) :=
    (continuous_apply i).comp continuous_fst
  have hg : Continuous (fun xg : (ι → ℝ) × (ι → ℝ) ↦ xg.2 i) :=
    (continuous_apply i).comp continuous_snd
  exact (hx.abs.sqrt.mul (hg.max continuous_const)).add (hg.min continuous_const)

/-- The limit-point implication of Theorem 13.12.4. Once the scaled gradient
norm tends to zero, every limit of converging feasible points and gradients
satisfies the first-order orthant condition. -/
theorem orthantFirstOrder_of_tendsto_scaledGradientNorm {α : Type*} {l : Filter α} [l.NeBot]
    {x g : α → ι → ℝ} {x₀ g₀ : ι → ℝ} (hx : Tendsto x l (𝓝 x₀))
    (hg : Tendsto g l (𝓝 g₀)) (hfeas : ∀ᶠ k in l, ∀ i, 0 ≤ x k i)
    (hzero : Tendsto (fun k ↦ scaledGradientNorm (x k) (g k)) l (𝓝 0)) :
    OrthantFirstOrder x₀ g₀ := by
  have hfeas₀ (i : ι) : 0 ≤ x₀ i :=
    ge_of_tendsto ((continuous_apply i).continuousAt.tendsto.comp hx)
      (hfeas.mono fun _ hk ↦ hk i)
  have hsg := continuous_scaledGradient.continuousAt.tendsto.comp (hx.prodMk_nhds hg)
  have hcoord : Continuous (fun z : ι → ℝ ↦ ‖WithLp.toLp 2 z‖) :=
    continuous_norm.comp (PiLp.continuous_toLp _ _)
  have hlim := hcoord.continuousAt.tendsto.comp hsg
  have hz : scaledGradientNorm x₀ g₀ = 0 := tendsto_nhds_unique hlim hzero
  have hh : scaledGradient x₀ g₀ = 0 := by
    have hz' : WithLp.toLp 2 (scaledGradient x₀ g₀) = 0 := norm_eq_zero.mp hz
    exact congrArg (WithLp.ofLp) hz'
  exact (scaledGradient_eq_zero_iff hfeas₀).mp hh

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

omit [DecidableEq ι] in
private theorem orthantBoundaryDistance_ge_of_coordinate_fraction [Nonempty ι]
    {x y : ι → ℝ} (hx : ∀ i, 0 < x i) {σ : ℝ} (hσ : 0 < σ)
    (hy : ∀ i, σ * x i ≤ y i) :
    σ * orthantBoundaryDistance x ≤ orthantBoundaryDistance y := by
  let C := Optimization.nonnegativeOrthant ι
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hfront : (frontier C).Nonempty :=
    ⟨0, Optimization.mem_frontier_nonnegativeOrthant.mpr ⟨fun _ ↦ le_rfl, i, rfl⟩⟩
  apply le_csInf (hfront.image (fun z : ι → ℝ ↦ ‖WithLp.toLp 2 (y - z)‖))
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨_, j, hj⟩ := Optimization.mem_frontier_nonnegativeOrthant.mp hz
  have hypos := (mul_pos hσ (hx j)).trans_le (hy j)
  calc
    σ * orthantBoundaryDistance x ≤ σ * x j :=
      mul_le_mul_of_nonneg_left (orthantBoundaryDistance_le_coordinate hx j) hσ.le
    _ ≤ y j := hy j
    _ = ‖(WithLp.toLp 2 (y - z) : EuclideanSpace ℝ ι) j‖ := by
      simp [hj, Real.norm_eq_abs, abs_of_pos hypos]
    _ ≤ ‖WithLp.toLp 2 (y - z)‖ := PiLp.norm_apply_le _ _

private theorem scaledCauchyTimes_of_cap [Nonempty ι] {x g : ι → ℝ}
    (hx : ∀ i, 0 < x i) {Δ σ t κ : ℝ} (hσ₀ : 0 < σ) (hσ : σ ≤ 1)
    (hκ : 0 < κ) (hg : ∀ i, g i ≤ κ) (ht : 0 ≤ t)
    (hΔ : t * scaledGradientNorm x g ≤ Δ) (hcap : t ≤ (1 - σ) / κ) :
    t ∈ scaledCauchyTimes x g Δ σ :=
  ⟨ht, hΔ, orthantBoundaryDistance_ge_of_coordinate_fraction hx hσ₀
    (scaledRay_coordinate_lower_bound (fun i ↦ (hx i).le) ht hσ hκ hg hcap)⟩

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

/-- The corrected Cauchy estimate recovers the AA.1b sufficient-decrease
benchmark using the scaled gradient norm. A uniform lower bound `α ≤ 1` on
the feasible time cap gives the coefficient `α / 2`. -/
theorem scaledCauchyTime_sufficientDecrease [Nonempty ι] (c : ℝ)
    {x g : ι → ℝ} (hx : ∀ i, 0 < x i) (H : Matrix ι ι ℝ) {Δ σ κ β tC α : ℝ}
    (hΔ : 0 ≤ Δ) (hσ₀ : 0 < σ) (hσ : σ < 1) (hκ : 0 < κ)
    (hg : ∀ i, g i ≤ κ) (hβ : 1 ≤ β) (hα : 0 < α) (hα₁ : α ≤ 1)
    (hcap : α ≤ (1 - σ) / κ)
    (hcurv : scaledGradient x g ⬝ᵥ (scaledHessian x g H *ᵥ scaledGradient x g) ≤
      β * scaledGradientNorm x g ^ 2)
    (hmin : IsScaledCauchyTime c x g H Δ σ tC) :
    (α / 2) * scaledGradientNorm x g * min (scaledGradientNorm x g / β) Δ ≤
      c - unscaledModel c x g H ((-tC) • ((scalingMatrix x g * scalingMatrix x g) *ᵥ g)) := by
  have hβ₀ : 0 < β := zero_lt_one.trans_le hβ
  have h := theorem_13_12_3 c hx H hΔ hσ₀ hσ hκ hg hβ₀ hcurv hmin
  let n := scaledGradientNorm x g
  let a := min (1 / β) (Δ / n)
  have hn : 0 ≤ n := norm_nonneg _
  have ha : 0 ≤ a := le_min (div_nonneg zero_le_one hβ₀.le) (div_nonneg hΔ hn)
  have ha₁ : a ≤ 1 := (min_le_left _ _).trans ((div_le_one hβ₀).mpr hβ)
  have hαa : α * a ≤ a := mul_le_of_le_one_left ha hα₁
  have hb : α * a ≤ min (1 / β) (min (Δ / n) ((1 - σ) / κ)) :=
    le_min (hαa.trans (min_le_left _ _)) (le_min (hαa.trans (min_le_right _ _))
      ((mul_le_of_le_one_right hα.le ha₁).trans hcap))
  have hl := mul_le_mul_of_nonneg_left hb (mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))
    (sq_nonneg n))
  have he : (α / 2) * n * min (n / β) Δ = (1 / 2) * n ^ 2 * (α * a) := by
    rcases hn.eq_or_lt with hzero | hp
    · simp [← hzero]
    have he' : n * a = min (n / β) Δ := by
      unfold a
      rw [mul_min_of_nonneg _ _ hn]
      congr 1
      · ring
      · rw [mul_comm, div_mul_cancel₀ _ hp.ne']
    rw [← he']
    ring
  rw [he]
  exact hl.trans h

/-- The times allowed by (13.12.23) for a unit scaled eigenvector. -/
def scaledEigenTimes (x g z : ι → ℝ) (Δ σ : ℝ) : Set ℝ :=
  {t | 0 ≤ t ∧ t ≤ Δ ∧ σ * orthantBoundaryDistance x ≤
    orthantBoundaryDistance (x - t • (scalingMatrix x g *ᵥ z))}

/-- A constrained scaled eigenpoint minimizes the model over the times in (13.12.23). -/
def IsScaledEigenTime (c : ℝ) (x g z : ι → ℝ) (H : Matrix ι ι ℝ) (Δ σ tC : ℝ) : Prop :=
  tC ∈ scaledEigenTimes x g z Δ σ ∧
    IsMinOn (fun t : ℝ ↦ unscaledModel c x g H ((-t) • (scalingMatrix x g *ᵥ z)))
      (scaledEigenTimes x g z Δ σ) tC

private theorem scaledEigen_coordinate_bound {x g z : ι → ℝ} {H : Matrix ι ι ℝ}
    {τ A K : ℝ} (hK : 0 ≤ K)
    (heig : scaledHessian x g H *ᵥ z = τ • z)
    (hH : ∀ i, |(H *ᵥ (scalingMatrix x g *ᵥ z)) i| ≤ K)
    (hscale : ∀ i, 0 < (scalingMatrix x g *ᵥ z) i →
      |scalingVector x g i| ≤ A * x i) (i : ι) :
    (-τ) * (scalingMatrix x g *ᵥ z) i ≤ A * K * x i ∨
      (scalingMatrix x g *ᵥ z) i ≤ 0 := by
  let a := Real.sqrt |scalingVector x g i|
  let q := (H *ᵥ (scalingMatrix x g *ᵥ z)) i
  let d := (scalingMatrix x g *ᵥ z) i
  rcases le_or_gt d 0 with hd | hd
  · exact Or.inr hd
  have hentry := congrFun heig i
  simp only [scaledHessian, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Pi.add_apply,
    scalingMatrix, Matrix.mulVec_diagonal, scaledCorrection, Pi.smul_apply, smul_eq_mul] at hentry
  change a * q + max (g i) 0 * z i = τ * z i at hentry
  have hdform : d = a * z i := Matrix.mulVec_diagonal _ _ _
  have ha : a * a = |scalingVector x g i| := Real.mul_self_sqrt (abs_nonneg _)
  have hprod := congrArg (fun r : ℝ ↦ a * r) hentry
  have heq : (max (g i) 0 - τ) * d = -(|scalingVector x g i| * q) := by
    rw [hdform, ← ha]
    nlinarith only [hprod]
  left
  calc
    (-τ) * d ≤ (max (g i) 0 - τ) * d :=
      mul_le_mul_of_nonneg_right (by linarith [le_max_right (g i) 0]) hd.le
    _ = -(|scalingVector x g i| * q) := heq
    _ = |scalingVector x g i| * (-q) := by ring
    _ ≤ |scalingVector x g i| * K :=
      mul_le_mul_of_nonneg_left ((neg_le_abs q).trans (hH i)) (abs_nonneg _)
    _ ≤ (A * x i) * K := mul_le_mul_of_nonneg_right (hscale i hd) hK
    _ = A * K * x i := by ring

private theorem scaledModel_onEigenRay (c : ℝ) {x g z : ι → ℝ} (hx : ∀ i, 0 < x i)
    {H : Matrix ι ι ℝ} {τ : ℝ} (heig : scaledHessian x g H *ᵥ z = τ • z)
    (hz : ‖WithLp.toLp 2 z‖ = 1) (t : ℝ) :
    unscaledModel c x g H ((-t) • (scalingMatrix x g *ᵥ z)) =
      c - t * (scaledGradient x g ⬝ᵥ z) + (1 / 2) * t ^ 2 * τ := by
  have hzz : z ⬝ᵥ z = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 z)
    rw [hz, one_pow] at h
    simpa only [dotProduct, pow_two] using h.symm
  rw [← Matrix.mulVec_smul, ← scaledModel_eq_unscaledModel c hx]
  simp only [scaledModel, affineQuadraticModel, Matrix.mulVec_smul, heig, dotProduct_smul,
    smul_dotProduct, hzz, smul_eq_mul]
  ring

/-- Corrected positive eigenpoint decrease for Theorem 13.12.5. The estimate
replaces the printed Cauchy point and negative lower bound with the
constrained scaled eigenpoint and a positive lower bound. For the ray `-t S z`,
orient the eigenvector by a nonnegative scaled gradient pairing.
The bound on the scaling weights is required on every decreasing coordinate.
It follows from the scaling definition on coordinates with nonnegative gradient. -/
theorem theorem_13_12_5 [Nonempty ι] (c : ℝ) {x g z : ι → ℝ} (hx : ∀ i, 0 < x i)
    {H : Matrix ι ι ℝ} {τ A K Δ σ tC : ℝ} (hτ : τ < 0) (hA : 0 < A) (hK : 0 < K)
    (hΔ : 0 ≤ Δ) (hσ₀ : 0 < σ) (hσ : σ < 1)
    (heig : scaledHessian x g H *ᵥ z = τ • z) (hz : ‖WithLp.toLp 2 z‖ = 1)
    (hdescent : 0 ≤ scaledGradient x g ⬝ᵥ z)
    (hH : ∀ i, |(H *ᵥ (scalingMatrix x g *ᵥ z)) i| ≤ K)
    (hscale : ∀ i, 0 < (scalingMatrix x g *ᵥ z) i →
      |scalingVector x g i| ≤ A * x i)
    (hmin : IsScaledEigenTime c x g z H Δ σ tC) :
    (1 / 2) * (-τ) * (min Δ ((1 - σ) * (-τ) / (A * K))) ^ 2 ≤
      c - unscaledModel c x g H ((-tC) • (scalingMatrix x g *ᵥ z)) := by
  let t := min Δ ((1 - σ) * (-τ) / (A * K))
  have hτ' : 0 < -τ := neg_pos.mpr hτ
  have hAK := mul_pos hA hK
  have ht : 0 ≤ t := le_min hΔ
    (div_nonneg (mul_nonneg (sub_nonneg.mpr hσ.le) hτ'.le) hAK.le)
  have hcap : t * (A * K) ≤ (1 - σ) * (-τ) := (le_div_iff₀ hAK).mp (min_le_right _ _)
  have hcoord (i : ι) : σ * x i ≤ (x - t • (scalingMatrix x g *ᵥ z)) i := by
    change σ * x i ≤ x i - t * (scalingMatrix x g *ᵥ z) i
    rcases scaledEigen_coordinate_bound hK.le heig hH hscale i with hb | hb
    · have h₁ := mul_le_mul_of_nonneg_left hb ht
      have h₂ := mul_le_mul_of_nonneg_right hcap (hx i).le
      have h₃ : (-τ) * (t * (scalingMatrix x g *ᵥ z) i) ≤ (-τ) * ((1 - σ) * x i) := by
        nlinarith only [h₁, h₂]
      have h₄ := le_of_mul_le_mul_left h₃ hτ'
      nlinarith only [h₄]
    · have h₁ := mul_nonpos_of_nonneg_of_nonpos ht hb
      have h₂ := mul_le_mul_of_nonneg_right hσ.le (hx i).le
      linarith only [h₁, h₂]
  have hfeas : t ∈ scaledEigenTimes x g z Δ σ :=
    ⟨ht, min_le_left _ _, orthantBoundaryDistance_ge_of_coordinate_fraction hx hσ₀ hcoord⟩
  have hcmp := isMinOn_iff.mp hmin.2 t hfeas
  change unscaledModel c x g H ((-tC) • (scalingMatrix x g *ᵥ z)) ≤
    unscaledModel c x g H ((-t) • (scalingMatrix x g *ᵥ z)) at hcmp
  rw [scaledModel_onEigenRay c hx heig hz t] at hcmp
  change (1 / 2) * (-τ) * t ^ 2 ≤ _
  linarith [mul_nonneg ht hdescent]

/-- Version 2 of the Coleman–Li acceptance ratio (13.12.24). The numerator
subtracts the same quadratic correction used in the model. -/
noncomputable def colemanLiAcceptanceRatio (f : (ι → ℝ) → ℝ) (x g s : ι → ℝ)
    (H : Matrix ι ι ℝ) : ℝ :=
  (f x - f (x + s) - (1 / 2) * (s ⬝ᵥ (unscaledCorrection x g *ᵥ s))) /
    (unscaledModel (f x) x g H 0 - unscaledModel (f x) x g H s)

/-- Subtracting the correction from the numerator cancels it in the
ratio error. Only the uncorrected objective-model error remains. -/
theorem colemanLiAcceptanceRatio_sub_one (f : (ι → ℝ) → ℝ) (x g s : ι → ℝ)
    (H : Matrix ι ι ℝ)
    (hp : unscaledModel (f x) x g H 0 - unscaledModel (f x) x g H s ≠ 0) :
    colemanLiAcceptanceRatio f x g s H - 1 =
      (affineQuadraticModel (f x) g H s - f (x + s)) /
        (unscaledModel (f x) x g H 0 - unscaledModel (f x) x g H s) := by
  rw [colemanLiAcceptanceRatio, div_sub_one hp]
  congr 1
  simp [unscaledModel, affineQuadraticModel, Matrix.add_mulVec, dotProduct_add]
  ring

section OperatorNorm

open scoped Matrix.Norms.L2Operator

private theorem norm_scalingMatrix_le {x g : ι → ℝ} (hx : ∀ i, 0 ≤ x i)
    {B : ℝ} (hB : 1 ≤ B) (hbound : ∀ i, x i ≤ B) :
    ‖scalingMatrix x g‖ ≤ Real.sqrt B := by
  rw [scalingMatrix, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg B)).mpr
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply Real.sqrt_le_sqrt
  by_cases hg : 0 ≤ g i
  · simpa [scalingVector, hg, abs_of_nonneg (hx i)] using hbound i
  · simpa [scalingVector, hg] using hB

omit [DecidableEq ι] in
/-- AN.1b for the Coleman–Li scaled norm on an interior bounded set.
The vector of quotients represents the displacement after applying `S⁻¹`. -/
theorem norm_le_colemanLiScaledNorm {x g : ι → ℝ} (hx : ∀ i, 0 < x i)
    {B : ℝ} (hB : 1 ≤ B) (hbound : ∀ i, x i ≤ B) (s : ι → ℝ) :
    ‖WithLp.toLp 2 s‖ ≤ Real.sqrt B *
      ‖WithLp.toLp 2 (fun i ↦ s i / Real.sqrt |scalingVector x g i|)‖ := by
  classical
  let w : ι → ℝ := fun i ↦ s i / Real.sqrt |scalingVector x g i|
  have hw : scalingMatrix x g *ᵥ w = s := by
    funext i
    have hv : 0 < |scalingVector x g i| := by
      by_cases hg : 0 ≤ g i
      · simpa [scalingVector, hg, abs_of_pos (hx i)] using hx i
      · simp [scalingVector, hg]
    rw [scalingMatrix, Matrix.mulVec_diagonal]
    dsimp [w]
    rw [mul_comm, div_mul_cancel₀ _ (Real.sqrt_pos.mpr hv).ne']
  have hnorm :=
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (scalingMatrix x g)).le_opNorm (WithLp.toLp 2 w)
  rw [Matrix.toEuclideanCLM_toLp, hw, ← Matrix.cstar_norm_def] at hnorm
  exact hnorm.trans (mul_le_mul_of_nonneg_right
    (norm_scalingMatrix_le (fun i ↦ (hx i).le) hB hbound) (norm_nonneg _))

/-- AM.4b for the Coleman–Li model. The scaled Hessian has norm at most
`B * K + G` when the point, model curvature, and gradient coordinates
are bounded by `B`, `K`, and `G` respectively. -/
theorem norm_scaledHessian_le {x g : ι → ℝ} (hx : ∀ i, 0 ≤ x i)
    {B K G : ℝ} (hB : 1 ≤ B) (hbound : ∀ i, x i ≤ B) (hG : 0 ≤ G)
    (hg : ∀ i, g i ≤ G) {H : Matrix ι ι ℝ} (hH : ‖H‖ ≤ K) :
    ‖scaledHessian x g H‖ ≤ B * K + G := by
  have hS := norm_scalingMatrix_le (g := g) hx hB hbound
  have hcorr : ‖scaledCorrection g‖ ≤ G := by
    rw [scaledCorrection, Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg hG).mpr
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (hg i) hG
  unfold scaledHessian
  calc
    _ ≤ ‖scalingMatrix x g * H * scalingMatrix x g‖ + ‖scaledCorrection g‖ := norm_add_le _ _
    _ ≤ (‖scalingMatrix x g‖ * ‖H‖) * ‖scalingMatrix x g‖ + G :=
      add_le_add ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (norm_mul_le _ _) (norm_nonneg _))) hcorr
    _ ≤ (Real.sqrt B * K) * Real.sqrt B + G := by
      have hK : 0 ≤ K := (norm_nonneg H).trans hH
      gcongr
    _ = _ := by
      rw [show Real.sqrt B * K * Real.sqrt B = (Real.sqrt B) ^ 2 * K by ring,
        Real.sq_sqrt (zero_le_one.trans hB)]

/-- The conditional scaled Hessian agreement in (13.12.25). -/
def ScaledHessianConsistency (x g : ℕ → ι → ℝ) (A H : ℕ → Matrix ι ι ℝ) : Prop :=
  Tendsto (fun k ↦ scaledGradientNorm (x k) (g k)) atTop (𝓝 0) →
    Tendsto (fun k ↦ ‖scalingMatrix (x k) (g k) * (A k - H k) *
      scalingMatrix (x k) (g k)‖) atTop (𝓝 0)

/-- Both scaled Hessians use the same correction, so their difference is
the congruence of the uncorrected Hessian error. -/
theorem scaledHessian_sub_eq (x g : ι → ℝ) (A H : Matrix ι ι ℝ) :
    scaledHessian x g A - scaledHessian x g H =
      scalingMatrix x g * (A - H) * scalingMatrix x g := by
  classical
  simp [scaledHessian, Matrix.mul_sub, Matrix.sub_mul]

end OperatorNorm

section Convergence

open scoped Matrix.Norms.L2Operator

private theorem abs_matrix_quadratic_le (A : Matrix ι ι ℝ) (v : ι → ℝ) :
    |v ⬝ᵥ (A *ᵥ v)| ≤ ‖A‖ * ‖WithLp.toLp 2 v‖ ^ 2 := by
  let V := WithLp.toLp 2 v
  have he : inner ℝ V ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A) V) = v ⬝ᵥ (A *ᵥ v) := by
    rw [Matrix.toEuclideanCLM_toLp, EuclideanSpace.inner_eq_star_dotProduct]
    simp [V, dotProduct_comm]
  rw [← he]
  calc
    _ ≤ ‖V‖ * ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A) V‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖V‖ * (‖A‖ * ‖V‖) := mul_le_mul_of_nonneg_left
      (by rw [Matrix.cstar_norm_def]; exact ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A)).le_opNorm V)
      (norm_nonneg _)
    _ = _ := by ring

private theorem scale_mulVec_div {x g : ι → ℝ} (hx : ∀ i, 0 < x i) (d : ι → ℝ) :
    scalingMatrix x g *ᵥ (fun i => d i / Real.sqrt |scalingVector x g i|) = d := by
  funext i
  have hv : 0 < |scalingVector x g i| := by
    by_cases hg : 0 ≤ g i
    · simpa [scalingVector, hg, abs_of_pos (hx i)] using hx i
    · simp [scalingVector, hg]
  rw [scalingMatrix, Matrix.mulVec_diagonal, mul_comm, div_mul_cancel₀ _ (Real.sqrt_pos.mpr hv).ne']

/-- A quantitative curvature transfer for a fixed trial point. A scaled
model lower bound and the Hessian consistency error control the objective
quadratic form in original coordinates, with the positive-gradient
diagonal separated explicitly. -/
theorem colemanLi_curvature_transfer (x g w : ι → ℝ) (A H : Matrix ι ι ℝ) {e : ℝ}
    (hmodel : -e * ‖WithLp.toLp 2 w‖ ^ 2 ≤ w ⬝ᵥ (scaledHessian x g H *ᵥ w)) :
    -(e + ‖scalingMatrix x g * (A - H) * scalingMatrix x g‖) * ‖WithLp.toLp 2 w‖ ^ 2 -
      (∑ i, max (g i) 0 * (w i) ^ 2) ≤
      (scalingMatrix x g *ᵥ w) ⬝ᵥ (A *ᵥ (scalingMatrix x g *ᵥ w)) := by
  have herr := abs_matrix_quadratic_le (scaledHessian x g A - scaledHessian x g H) w
  rw [Matrix.sub_mulVec, dotProduct_sub, scaledHessian_sub_eq] at herr
  have herr' := (neg_le_neg herr).trans (neg_abs_le _)
  linarith only [hmodel, herr', scaledHessian_form x g w A]

/-- The second-order transfer in Theorem 13.12.6. The scaled model curvature
must have vanishing negative part along the subsequence. The scaled Hessian
error in (13.12.25) then bounds the objective curvature error on bounded
preimages of every active-face direction. -/
theorem theorem_13_12_6 {x g : ℕ → ι → ℝ} {A H : ℕ → Matrix ι ι ℝ}
    {x₀ g₀ : ι → ℝ} {A₀ : Matrix ι ι ℝ}
    (hx : Tendsto x atTop (𝓝 x₀)) (hg : Tendsto g atTop (𝓝 g₀))
    (hA : Tendsto A atTop (𝓝 A₀)) (hpos : ∀ k i, 0 < x k i)
    (hfirst : Tendsto (fun k => scaledGradientNorm (x k) (g k)) atTop (𝓝 0))
    (hcons : ScaledHessianConsistency x g A H)
    {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0)) (he₀ : ∀ k, 0 ≤ e k)
    (hcurv : ∀ k w, -e k * ‖WithLp.toLp 2 w‖ ^ 2 ≤
      w ⬝ᵥ (scaledHessian (x k) (g k) (H k) *ᵥ w)) :
    OrthantWeakSecondOrder x₀ g₀ A₀ := by
  have hfo := orthantFirstOrder_of_tendsto_scaledGradientNorm hx hg
    (Eventually.of_forall fun k i => (hpos k i).le) hfirst
  refine ⟨hfo, fun d hd => ?_⟩
  let w (k : ℕ) (i : ι) := d i / Real.sqrt |scalingVector (x k) (g k) i|
  let D (i : ι) := |d i| / Real.sqrt (min 1 (x₀ i / 2))
  have hbound : ∀ᶠ k in atTop, ∀ i, |w k i| ≤ D i := by
    have hi (i : ι) : ∀ᶠ k in atTop, |w k i| ≤ D i := by
      by_cases hz : x₀ i = 0
      · exact Eventually.of_forall fun k => by simp [w, D, hd i hz]
      have hxi : 0 < x₀ i :=
        lt_of_le_of_ne (ge_of_tendsto ((continuous_apply i).continuousAt.tendsto.comp hx)
          (Eventually.of_forall fun k => (hpos k i).le)) (Ne.symm hz)
      filter_upwards [((continuous_apply i).continuousAt.tendsto.comp hx).eventually
        (lt_mem_nhds (half_lt_self hxi))] with k hk
      have hden : min 1 (x₀ i / 2) ≤ |scalingVector (x k) (g k) i| := by
        by_cases hgi : 0 ≤ g k i
        · simpa [scalingVector, hgi, abs_of_pos (hpos k i)] using
            (min_le_right (1 : ℝ) (x₀ i / 2)).trans hk.le
        · simp [scalingVector, hgi]
      rw [show |w k i| = |d i| / Real.sqrt |scalingVector (x k) (g k) i| by
        dsimp only [w]
        rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]]
      exact div_le_div_of_nonneg_left (abs_nonneg _)
        (Real.sqrt_pos.mpr (lt_min zero_lt_one (half_pos hxi))) (Real.sqrt_le_sqrt hden)
    exact Filter.eventually_all.mpr hi
  let B := ∑ i, (D i) ^ 2
  have hB : ∀ᶠ k in atTop, ‖WithLp.toLp 2 (w k)‖ ^ 2 ≤ B := by
    filter_upwards [hbound] with k hk
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_le_sum fun i _ => by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hk i) 2
  have hterm (i : ι) :
      Tendsto (fun k => max (g k i) 0 * (w k i) ^ 2) atTop (𝓝 0) := by
    by_cases hz : x₀ i = 0
    · simp [w, hd i hz]
    have hxi : 0 < x₀ i :=
      lt_of_le_of_ne (ge_of_tendsto ((continuous_apply i).continuousAt.tendsto.comp hx)
        (Eventually.of_forall fun k => (hpos k i).le)) (Ne.symm hz)
    have hzero := (hfo i).2 hxi
    have hmax : Tendsto (fun k => max (g k i) 0) atTop (𝓝 0) := by
      simpa only [hzero, max_self, Function.comp_apply] using
        ((continuous_apply i).continuousAt.tendsto.comp hg).max (tendsto_const_nhds (x := (0 : ℝ)))
    apply squeeze_zero' (Eventually.of_forall fun k => mul_nonneg (le_max_right _ _) (sq_nonneg _))
      _ (by simpa only [zero_mul] using hmax.mul_const ((D i) ^ 2))
    filter_upwards [hbound] with k hk
    apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hk i) 2
  have hcorr : Tendsto (fun k => ∑ i, max (g k i) 0 * (w k i) ^ 2) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun i _ => hterm i)
  let δ (k : ℕ) := ‖scalingMatrix (x k) (g k) * (A k - H k) * scalingMatrix (x k) (g k)‖
  have hδ : Tendsto δ atTop (𝓝 0) := hcons hfirst
  have hq : ∀ᶠ k in atTop, -(e k + δ k) * B -
      (∑ i, max (g k i) 0 * (w k i) ^ 2) ≤ d ⬝ᵥ (A k *ᵥ d) := by
    filter_upwards [hB] with k hk
    have hlow := mul_le_mul_of_nonpos_left hk
      (neg_nonpos.mpr (add_nonneg (he₀ k) (norm_nonneg _)) : -(e k + δ k) ≤ 0)
    have htransfer := colemanLi_curvature_transfer (x k) (g k) (w k) (A k) (H k) (hcurv k (w k))
    have hscale := scale_mulVec_div (hpos k) (g := g k) d
    change scalingMatrix (x k) (g k) *ᵥ w k = d at hscale
    rw [hscale] at htransfer
    exact (sub_le_sub_right hlow _).trans htransfer
  have hlim : Tendsto (fun k => -(e k + δ k) * B -
      (∑ i, max (g k i) 0 * (w k i) ^ 2)) atTop (𝓝 0) := by
    simpa only [add_zero, neg_zero, zero_mul, sub_zero] using
      (((he.add hδ).neg.mul_const B).sub hcorr)
  have hcont : Continuous (fun M : Matrix ι ι ℝ => d ⬝ᵥ (M *ᵥ d)) := by
    unfold dotProduct Matrix.mulVec
    fun_prop
  exact le_of_tendsto_of_tendsto hlim (hcont.continuousAt.tendsto.comp hA) hq

open ConnGouldToint.Chapter06 in
private theorem scalar_btr_criticality {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : BTRParams} {f : E → ℝ} {sufficient : ℕ → (E → ℝ) → E → E → Prop}
    (run : BTRRun f P sufficient) {a : ℕ → ℝ} {κ β C K : ℝ}
    (ha : ∀ k, 0 ≤ a k) (hκ : 0 < κ) (hκ₁ : κ < 1) (hβ : 0 < β) (hβC : β ≤ C)
    (hK : 0 < K) (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hdec : ∀ k, κ * a k * min (a k / β) (run.Δ k) ≤
      run.model k (run.x k) - run.model k (run.x k + run.s k))
    (herr : ∀ k, |f (run.x k + run.s k) - run.model k (run.x k + run.s k)| ≤ C * (run.Δ k) ^ 2)
    (hstep : ∀ k, ‖run.s k‖ ≤ K * run.Δ k)
    (hcont : ∀ ε > 0, ∃ r > 0, ∀ i j, ‖run.x i - run.x j‖ < r → |a i - a j| < ε)
    (hlower : BddBelow (Set.range f)) :
    Tendsto a atTop (𝓝 0) := by
  let F (k : ℕ) := f (run.x k)
  have hFbound : BddBelow (Set.range F) := hlower.mono (Set.range_comp_subset_range run.x f)
  have hF := tendsto_atTop_ciInf run.objective_antitone hFbound
  have hdiff : Tendsto (fun k => F k - F (k + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self] using hF.sub (hF.comp (tendsto_add_atTop_nat 1))
  have hC : 0 < C := hβ.trans_le hβC
  have hη : 0 < 1 - P.η₂ := sub_pos.mpr P.eta₂_lt_one
  have hfreq (ε : ℝ) (hε : 0 < ε) : ∃ᶠ k in atTop, a k < ε := by
    by_contra! hn
    obtain ⟨N, hN⟩ := eventually_atTop.mp hn
    let θ := κ * ε * (1 - P.η₂) / C
    let r := min (run.Δ N) (P.γ₁ * θ)
    have hr : 0 < r := lt_min (run.delta_pos N)
      (mul_pos P.gamma₁_pos (div_pos (mul_pos (mul_pos hκ hε) hη) hC))
    have hrad (k : ℕ) (hk : N ≤ k) : r ≤ run.Δ k := by
      have h := (run.tail N).delta_lower_bound (θ := θ) (fun j hj => ?_) (k - N)
      · change r ≤ run.Δ (N + (k - N)) at h
        simpa only [Nat.add_sub_of_le hk] using h
      · let i := N + j
        have hi := hN i (Nat.le_add_right N j)
        have hsmall : run.Δ i ≤ κ * a i * (1 - P.η₂) / C := by
          exact hj.trans (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi hκ.le) hη.le) hC.le)
        exact btrRatio_ge_eta₂_of_small_radius_of_decrease hβ hβC (run.delta_pos i)
          (hε.trans_le hi) hκ hκ₁ (hval i) (hdec i) (herr i) hsmall
    let b := P.η₁ * (κ * ε * min (ε / β) r)
    have hb : 0 < b := mul_pos P.eta₁_pos
      (mul_pos (mul_pos hκ hε) (lt_min (div_pos hε hβ) hr))
    obtain ⟨J, hJ⟩ := eventually_atTop.mp (hdiff.eventually (gt_mem_nhds hb))
    let L := max N J
    have hfail (k : ℕ) (hk : L ≤ k) : k ∉ run.successful := by
      intro hks
      have hkN := (le_max_left N J).trans hk
      have hmin := min_le_min (div_le_div_of_nonneg_right (hN k hkN) hβ.le) (hrad k hkN)
      have hlow := (mul_le_mul (mul_le_mul_of_nonneg_left (hN k hkN) hκ.le)
        hmin (le_min (div_nonneg hε.le hβ.le) hr.le) (mul_nonneg hκ.le (ha k))).trans (hdec k)
      exact (hJ k ((le_max_right N J).trans hk)).not_ge
        ((mul_le_mul_of_nonneg_left hlow P.eta₁_pos.le).trans (run.objective_drop_of_successful hks))
    have hγ := P.gamma₁_pos.trans_le P.gamma₁_le_gamma₂
    have hp (j : ℕ) : run.Δ (L + j) ≤ P.γ₂ ^ j * run.Δ L := by
      induction j with
      | zero => simp
      | succ j ih =>
        have hh := ((run.radius_update (L + j)).unsuccessful
          (lt_of_not_ge (hfail (L + j) (Nat.le_add_right _ _)))).2
        rw [Nat.add_succ, pow_succ, mul_comm (P.γ₂ ^ j), mul_assoc]
        exact hh.trans (mul_le_mul_of_nonneg_left ih hγ.le)
    have hlim : Tendsto (fun j : ℕ => P.γ₂ ^ j * run.Δ L) atTop (𝓝 0) := by
      simpa only [zero_mul] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one hγ.le P.gamma₂_lt_one).mul_const (run.Δ L)
    obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds hr)).exists
    exact hj.not_ge ((hrad _ ((le_max_left N J).trans (Nat.le_add_right L j))).trans (hp j))
  apply tendsto_order.mpr
  refine ⟨fun b hb => Eventually.of_forall fun k => hb.trans_le (ha k), ?_⟩
  intro ε hε
  let δ := ε / 2
  have hδ : 0 < δ := half_pos hε
  obtain ⟨r, hr, hnear⟩ := hcont δ hδ
  let c := P.η₁ * (κ * δ)
  have hc : 0 < c := mul_pos P.eta₁_pos (mul_pos hκ hδ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hdiff.eventually (gt_mem_nhds (mul_pos hc (div_pos hδ hβ))))
  have hKc : 0 < K / c := div_pos hK hc
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (hF.eventually (gt_mem_nhds (lt_add_of_pos_right _ (div_pos hr hKc))))
  apply eventually_atTop.mpr
  refine ⟨max N M, fun n hn => ?_⟩
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnM : M ≤ n := (le_max_right _ _).trans hn
  have hex : ∃ j, n ≤ j ∧ a j < δ := by
    obtain ⟨j, hj, hnj⟩ := ((hfreq δ hδ).and_eventually (eventually_ge_atTop n)).exists
    exact ⟨j, hnj, hj⟩
  classical
  let j := Nat.find hex
  obtain ⟨hnj, hj⟩ := Nat.find_spec hex
  have hmove (k : ℕ) (hkn : n ≤ k) (hkj : k < j) :
      ‖run.x k - run.x (k + 1)‖ ≤ (K / c) * (F k - F (k + 1)) := by
    by_cases hs : k ∈ run.successful
    · have hk : δ ≤ a k := le_of_not_gt (fun h => Nat.find_min hex hkj ⟨hkn, h⟩)
      have hmin := min_le_min (div_le_div_of_nonneg_right hk hβ.le) (le_refl (run.Δ k))
      have hm := (mul_le_mul (mul_le_mul_of_nonneg_left hk hκ.le) hmin
        (le_min (div_nonneg hδ.le hβ.le) (run.delta_pos k).le) (mul_nonneg hκ.le (ha k))).trans (hdec k)
      have hdrop : c * min (δ / β) (run.Δ k) ≤ F k - F (k + 1) := by
        simpa only [c, mul_assoc] using
          (mul_le_mul_of_nonneg_left hm P.eta₁_pos.le).trans (run.objective_drop_of_successful hs)
      have hrad : run.Δ k ≤ δ / β := by
        by_contra! hbad
        rw [min_eq_left hbad.le] at hdrop
        exact (hN k (hnN.trans hkn)).not_ge hdrop
      rw [min_eq_right hrad] at hdrop
      rw [run.iterate_update, Optimization.acceptStep_of_le hs, sub_add_cancel_left, norm_neg]
      apply (hstep k).trans
      have hh : run.Δ k ≤ (F k - F (k + 1)) / c := (le_div_iff₀ hc).mpr (by rwa [mul_comm])
      rw [div_mul_eq_mul_div, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hh hK.le
    · simp [run.iterate_eq_of_unsuccessful hs, F]
  have hpath (t : ℕ) (ht : n + t ≤ j) :
      ‖run.x n - run.x (n + t)‖ ≤ (K / c) * (F n - F (n + t)) := by
    induction t with
    | zero => simp
    | succ t ih =>
      have hlt : n + t < j := by omega
      have hm := hmove (n + t) (Nat.le_add_right n t) hlt
      have hprev := ih hlt.le
      have htri : ‖run.x n - run.x (n + (t + 1))‖ ≤
          ‖run.x n - run.x (n + t)‖ + ‖run.x (n + t) - run.x (n + t + 1)‖ := by
        simpa only [sub_add_sub_cancel, Nat.add_assoc] using
          norm_add_le (run.x n - run.x (n + t)) (run.x (n + t) - run.x (n + t + 1))
      rw [← Nat.add_assoc]
      exact htri.trans (by linarith only [hprev, hm])
  have hnj' : n + (j - n) = j := Nat.add_sub_of_le hnj
  have hdist := hpath (j - n) hnj'.le
  rw [hnj'] at hdist
  have hgap : F n - F j < r / (K / c) := by
    have hh : F n < (⨅ k, F k) + r / (K / c) := hM n hnM
    linarith only [hh, ciInf_le hFbound j]
  have hd := hdist.trans_lt (by
    rw [mul_comm]
    exact (lt_div_iff₀ hKc).mp hgap)
  have hh := le_abs_self (a n - a j)
  have hj' : a j < δ := hj
  have hnear' := hnear n j hd
  dsimp [δ] at hj' hnear'
  linarith only [hnear', hh, hj']

open ConnGouldToint.Chapter06 in
/-- Theorem 13.12.4. A bounded interior Coleman–Li run converges in the
scaled gradient norm and has first-order critical limit points. The trial
model decrease is compared with the feasible scaled Cauchy point, with
the corrected time-cap estimate from Theorem 13.12.3. -/
theorem theorem_13_12_4 [Nonempty ι]
    {f : EuclideanSpace ℝ ι → ℝ} {P : BTRParams}
    {sufficient : ℕ → (EuclideanSpace ℝ ι → ℝ) → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι → Prop}
    (run : BTRRun f P sufficient)
    (g : EuclideanSpace ℝ ι → (ι → ℝ)) (H : ℕ → Matrix ι ι ℝ)
    (hf : ContDiff ℝ 2 f) (hg : Continuous g)
    (hgrad : ∀ x v, fderiv ℝ f x v = g x ⬝ᵥ WithLp.ofLp v)
    (hlower : BddBelow (Set.range f))
    {S : Set (EuclideanSpace ℝ ι)} (hS : IsCompact S) (hxS : ∀ k, run.x k ∈ S)
    {B G U L σ α : ℝ} (hB : 1 ≤ B) (hG : 0 < G) (hU : 0 ≤ U) (hL : 0 ≤ L)
    (hσ : 0 < σ) (hσ₁ : σ < 1) (hα : 0 < α) (hα₁ : α ≤ 1)
    (hcap : α ≤ (1 - σ) / G)
    (hx : ∀ k i, 0 < run.x k i) (hbound : ∀ k i, run.x k i ≤ B)
    (hgBound : ∀ k i, g (run.x k) i ≤ G) (hH : ∀ k, ‖H k‖ ≤ U)
    (hfH : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ L)
    (hp : ∀ k (v : EuclideanSpace ℝ ι), run.p k v =
      ‖WithLp.toLp 2 (fun i => v i / Real.sqrt |scalingVector
        (WithLp.ofLp (run.x k)) (g (run.x k)) i|)‖)
    (hm : ∀ k (v : EuclideanSpace ℝ ι), run.model k (run.x k + v) =
      unscaledModel (f (run.x k)) (WithLp.ofLp (run.x k)) (g (run.x k)) (H k) (WithLp.ofLp v))
    (hCauchy : ∀ k, ∃ t, IsScaledCauchyTime (f (run.x k))
      (WithLp.ofLp (run.x k)) (g (run.x k)) (H k) (run.Δ k) σ t ∧
      run.model k (run.x k + run.s k) ≤
        unscaledModel (f (run.x k)) (WithLp.ofLp (run.x k)) (g (run.x k)) (H k)
          ((-t) • ((scalingMatrix (WithLp.ofLp (run.x k)) (g (run.x k)) *
            scalingMatrix (WithLp.ofLp (run.x k)) (g (run.x k))) *ᵥ g (run.x k)))) :
    Tendsto (fun k => scaledGradientNorm (WithLp.ofLp (run.x k)) (g (run.x k))) atTop (𝓝 0) ∧
      ∀ z (j : ℕ → ℕ), Tendsto j atTop atTop → Tendsto (run.x ∘ j) atTop (𝓝 z) →
        OrthantFirstOrder (WithLp.ofLp z) (g z) := by
  let a (x : EuclideanSpace ℝ ι) := scaledGradientNorm (WithLp.ofLp x) (g x)
  let β := 1 + B * U + G
  have hB₀ : 0 ≤ B := zero_le_one.trans hB
  have hβ : 1 ≤ β := by dsimp [β]; linarith [mul_nonneg hB₀ hU]
  have hβ₀ : 0 < β := zero_lt_one.trans_le hβ
  have hmodelH (k : ℕ) :
      ‖scaledHessian (WithLp.ofLp (run.x k)) (g (run.x k)) (H k)‖ ≤ β :=
    (norm_scaledHessian_le (fun i => (hx k i).le) hB (hbound k) hG.le (hgBound k) (hH k)).trans
      (by dsimp [β]; linarith)
  have hval (k : ℕ) : f (run.x k) = run.model k (run.x k) := by
    simpa [unscaledModel, affineQuadraticModel] using (hm k 0).symm
  have hdec (k : ℕ) : (α / 2) * a (run.x k) * min (a (run.x k) / β) (run.Δ k) ≤
      run.model k (run.x k) - run.model k (run.x k + run.s k) := by
    obtain ⟨t, ht, hcmp⟩ := hCauchy k
    have hcurv := (le_abs_self _).trans (abs_matrix_quadratic_le
      (scaledHessian (WithLp.ofLp (run.x k)) (g (run.x k)) (H k))
      (scaledGradient (WithLp.ofLp (run.x k)) (g (run.x k))))
    have hcurv' : scaledGradient (WithLp.ofLp (run.x k)) (g (run.x k)) ⬝ᵥ
        (scaledHessian (WithLp.ofLp (run.x k)) (g (run.x k)) (H k) *ᵥ
          scaledGradient (WithLp.ofLp (run.x k)) (g (run.x k))) ≤ β * a (run.x k) ^ 2 :=
      hcurv.trans (mul_le_mul_of_nonneg_right (hmodelH k) (sq_nonneg _))
    have hh := scaledCauchyTime_sufficientDecrease (f (run.x k)) (hx k) (H k)
      (run.delta_pos k).le hσ hσ₁ hG (hgBound k) hβ hα hα₁ hcap hcurv' ht
    exact hh.trans (by rw [← hval k]; exact sub_le_sub_left hcmp _)
  have hfeas (k : ℕ) : run.p k (run.s k) ≤ run.Δ k := by
    have h := run.feasible k
    change run.p k (run.x k + run.s k - run.x k) ≤ run.Δ k at h
    rwa [add_sub_cancel_left] at h
  have hstep (k : ℕ) : ‖run.s k‖ ≤ Real.sqrt B * run.Δ k := by
    have h := norm_le_colemanLiScaledNorm (g := g (run.x k)) (hx k) hB (hbound k)
      (WithLp.ofLp (run.s k))
    rw [WithLp.toLp_ofLp, ← hp] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hfeas k) (Real.sqrt_nonneg _))
  have herror (k : ℕ) : |f (run.x k + run.s k) - run.model k (run.x k + run.s k)| ≤
      (β + L * B) * (run.Δ k) ^ 2 := by
    let x := run.x k
    let s := run.s k
    let w (i : ι) := s i / Real.sqrt |scalingVector (WithLp.ofLp x) (g x) i|
    let V := scalingMatrix (WithLp.ofLp x) (g x)
    have hw : V *ᵥ w = WithLp.ofLp s := scale_mulVec_div (hx k) _
    have hM : run.model k (x + s) = f x + fderiv ℝ f x s +
        (1 / 2) * (w ⬝ᵥ (scaledHessian (WithLp.ofLp x) (g x) (H k) *ᵥ w)) := by
      rw [hm, ← hw, ← scaledModel_eq_unscaledModel (f x) (hx k), scaledModel,
        affineQuadraticModel, scaledGradient, hgrad, ← hw, dotProduct_comm (V *ᵥ g x),
        Matrix.dotProduct_mulVec, vecMul_scalingMatrix, dotProduct_comm]
    have hDf := (hf.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiable
      (by norm_num)
    have hrem := norm_sub_firstOrder_le_of_hessian_bound
      (convex_univ : Convex ℝ (Set.univ : Set (EuclideanSpace ℝ ι)))
      (Set.mem_univ x) (Set.mem_univ (x + s))
      (fun z _ => hf.differentiable (by norm_num) z) (fun z _ => hDf z)
      (fun z _ => hfH z)
    rw [Real.norm_eq_abs] at hrem
    have hQ := (abs_matrix_quadratic_le (scaledHessian (WithLp.ofLp x) (g x) (H k)) w).trans
      (mul_le_mul_of_nonneg_right (hmodelH k) (sq_nonneg _))
    have hwΔ : ‖WithLp.toLp 2 w‖ ≤ run.Δ k := by
      exact ((hp k s).symm.le).trans (hfeas k)
    have hsΔ := pow_le_pow_left₀ (norm_nonneg _) (hstep k) 2
    rw [mul_pow, Real.sq_sqrt hB₀] at hsΔ
    have hQΔ := hQ.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hwΔ 2) hβ₀.le)
    have hremΔ := hrem.trans (mul_le_mul_of_nonneg_left hsΔ
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hL))
    rw [hM]
    obtain ⟨h₁, h₂⟩ := abs_le.mp hQΔ
    obtain ⟨h₃, h₄⟩ := abs_le.mp hremΔ
    apply abs_le.mpr
    constructor <;> nlinarith only [h₁, h₂, h₃, h₄,
      mul_nonneg (add_nonneg hβ₀.le (mul_nonneg hL hB₀)) (sq_nonneg (run.Δ k))]
  have ha : Continuous a := by
    have ho : Continuous (WithLp.ofLp : EuclideanSpace ℝ ι → (ι → ℝ)) :=
      PiLp.continuous_ofLp _ _
    exact continuous_norm.comp ((PiLp.continuous_toLp _ _).comp
      (continuous_scaledGradient.comp (ho.prodMk hg)))
  have huc := Metric.uniformContinuousOn_iff.mp (hS.uniformContinuousOn_of_continuous ha.continuousOn)
  have hz : Tendsto (a ∘ run.x) atTop (𝓝 0) :=
    scalar_btr_criticality run (fun _ => norm_nonneg _) (half_pos hα)
      (by linarith) hβ₀ (le_add_of_nonneg_right (mul_nonneg hL hB₀))
      (Real.sqrt_pos.mpr (zero_lt_one.trans_le hB)) hval hdec herror hstep
      (fun ε hε => by
        obtain ⟨r, hr, hh⟩ := huc ε hε
        refine ⟨r, hr, fun i j hij => ?_⟩
        simpa only [Real.dist_eq, Function.comp_apply] using hh (run.x i) (hxS i) (run.x j) (hxS j)
          (by simpa only [dist_eq_norm] using hij)) hlower
  refine ⟨hz, fun z j hj hjz => ?_⟩
  exact orthantFirstOrder_of_tendsto_scaledGradientNorm
    ((PiLp.continuous_ofLp _ _).continuousAt.tendsto.comp hjz)
    (hg.continuousAt.tendsto.comp hjz) (Eventually.of_forall fun k i => (hx (j k) i).le)
    (hz.comp hj)

open ConnGouldToint.Chapter06 in
/-- Version 2 of Theorem 13.12.6. The corrected ratio provides objective
decrease and very successful acceptance from the uncorrected model error.
Forced expansion then excludes a negative active-face direction at a
subsequential limit. The first-order limit and the uniform small-radius
uncorrected model agreement are explicit inputs. -/
theorem theorem_13_12_6_version2
    {P : BTRParams} (f : (ι → ℝ) → ℝ) (g : EuclideanSpace ℝ ι → (ι → ℝ))
    (A : EuclideanSpace ℝ ι → Matrix ι ι ℝ) (H : ℕ → Matrix ι ι ℝ)
    (x s : ℕ → EuclideanSpace ℝ ι) (Δ τ : ℕ → ℝ) {z : EuclideanSpace ℝ ι}
    {j : ℕ → ℕ} (hj : StrictMono j) (hz : Tendsto (x ∘ j) atTop (𝓝 z))
    (hg : ContinuousAt g z) (hA : ContinuousAt A z)
    (hpos : ∀ k i, 0 < x k i)
    (hfirst : Tendsto (fun k => scaledGradientNorm (WithLp.ofLp (x k)) (g (x k))) atTop (𝓝 0))
    (hcons : ScaledHessianConsistency (fun k => WithLp.ofLp (x k))
      (g ∘ x) (A ∘ x) H)
    (hcurv : ∀ k w, τ k * ‖WithLp.toLp 2 w‖ ^ 2 ≤
      w ⬝ᵥ (scaledHessian (WithLp.ofLp (x k)) (g (x k)) (H k) *ᵥ w))
    {κ cap K γ₃ γ₄ capExpand : ℝ}
    (hκ : 0 < κ) (hcap : 0 < cap) (hK : 0 < K)
    (hγ₃ : 1 < γ₃) (hγ₄ : γ₃ ≤ γ₄) (hcapExpand : 0 < capExpand)
    (hΔ : ∀ k, 0 < Δ k) (hstep : ∀ k, ‖s k‖ ≤ K * Δ k)
    (hlower : BddBelow (Set.range f)) :
    let y (k : ℕ) := WithLp.ofLp (x k)
    let v (k : ℕ) := WithLp.ofLp (s k)
    let pred (k : ℕ) := f (y k) - unscaledModel (f (y k)) (y k) (g (x k)) (H k) (v k)
    let ρ (k : ℕ) := colemanLiAcceptanceRatio f (y k) (g (x k)) (v k) (H k)
    (∀ k, 0 < pred k) →
    (∀ k, τ k < 0 → κ * |τ k| * min (min (τ k ^ 2) (Δ k ^ 2)) (cap ^ 2) ≤ pred k) →
    (∀ ε > 0, ∃ δ > 0, ∀ᶠ k in atTop, Δ k ≤ δ →
      |affineQuadraticModel (f (y k)) (g (x k)) (H k) (v k) - f (y k + v k)| ≤ ε * Δ k ^ 2) →
    (∀ k, x (k + 1) = if P.η₁ ≤ ρ k then x k + s k else x k) →
    (∀ k, BTRRadiusUpdate P (ρ k) (Δ k) (Δ (k + 1))) →
    (∀ k, P.η₂ ≤ ρ k → Δ k ≤ capExpand →
      γ₃ * Δ k ≤ Δ (k + 1) ∧ Δ (k + 1) ≤ γ₄ * Δ k) →
    OrthantWeakSecondOrder (WithLp.ofLp z) (g z) (A z) := by
  dsimp only
  intro hp hdec herr hupdate hrad hgrow
  let y (k : ℕ) := WithLp.ofLp (x k)
  let v (k : ℕ) := WithLp.ofLp (s k)
  let pred (k : ℕ) := f (y k) - unscaledModel (f (y k)) (y k) (g (x k)) (H k) (v k)
  let ρ (k : ℕ) := colemanLiAcceptanceRatio f (y k) (g (x k)) (v k) (H k)
  let S := {k | P.η₁ ≤ ρ k}
  let F (k : ℕ) := f (y k)
  have hf : ∀ k ∈ S, P.η₁ * pred k ≤ F k - F (k + 1) := by
    intro k hk
    have hcorr : 0 ≤ v k ⬝ᵥ (unscaledCorrection (y k) (g (x k)) *ᵥ v k) := by
      unfold unscaledCorrection dotProduct
      apply Finset.sum_nonneg
      intro i _
      rw [Matrix.mulVec_diagonal]
      rw [show v k i * (max (g (x k) i) 0 / |scalingVector (y k) (g (x k)) i| * v k i) =
        (max (g (x k) i) 0 / |scalingVector (y k) (g (x k)) i|) * (v k i) ^ 2 by ring]
      exact mul_nonneg (div_nonneg (le_max_right _ _) (abs_nonneg _)) (sq_nonneg _)
    have hρ : P.η₁ ≤ ρ k := hk
    have he : ρ k = (F k - f (y k + v k) - (1 / 2) *
        (v k ⬝ᵥ (unscaledCorrection (y k) (g (x k)) *ᵥ v k))) / pred k := by
      simp [ρ, pred, F, colemanLiAcceptanceRatio, unscaledModel, affineQuadraticModel]
    rw [he] at hρ
    have hh := (le_div_iff₀ (hp k)).mp hρ
    have hxs : x (k + 1) = x k + s k := by rw [hupdate, ite_eq_left (show P.η₁ ≤ ρ k from hk)]
    have hy : F (k + 1) = f (y k + v k) := by dsimp [F, y, v]; rw [hxs]; rfl
    rw [hy]
    linarith
  have hstay (k : ℕ) (hk : k ∉ S) : x (k + 1) = x k := by
    rw [hupdate, ite_eq_right (show ¬ P.η₁ ≤ ρ k from hk)]
  have hmono : Antitone F := by
    apply antitone_nat_of_succ_le
    intro k
    by_cases hk : k ∈ S
    · exact sub_nonneg.mp ((mul_pos P.eta₁_pos (hp k)).le.trans (hf k hk))
    · change f (WithLp.ofLp (x (k + 1))) ≤ f (WithLp.ofLp (x k))
      rw [hstay k hk]
  have hFlim := tendsto_atTop_ciInf hmono
    (hlower.mono (show Set.range F ⊆ Set.range f from Set.range_comp_subset_range y f))
  have hdrop : Tendsto (fun k => F k - F (k + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self] using hFlim.sub (hFlim.comp (tendsto_add_atTop_nat 1))
  by_contra hnoncritical
  have hlocal : ∃ a > 0, ∃ r > 0, ∀ᶠ k in atTop, dist (x k) z < r → τ k ≤ -a := by
    by_contra hn
    let e (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
    have hepos (n : ℕ) : 0 < e n := by dsimp [e]; positivity
    have he : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hfq (n : ℕ) : ∃ᶠ k in atTop, dist (x k) z < e n ∧ -e n < τ k := by
      by_contra hbad
      have hev : ∀ᶠ k in atTop, ¬(dist (x k) z < e n ∧ -e n < τ k) := by
        simpa only [Filter.Frequently, not_not] using hbad
      exact hn ⟨e n, hepos n, e n, hepos n, hev.mono fun k hk hd =>
        not_lt.mp (fun ht => hk ⟨hd, ht⟩)⟩
    obtain ⟨i, hi, hib⟩ := extraction_forall_of_frequently hfq
    have hzi : Tendsto (x ∘ i) atTop (𝓝 z) := by
      apply Metric.tendsto_atTop.mpr
      intro ε hε
      obtain ⟨N, hN⟩ := eventually_atTop.mp (he.eventually_lt_const hε)
      exact ⟨N, fun k hk => (hib k).1.trans (hN k hk)⟩
    have hco : ScaledHessianConsistency (y ∘ i) (g ∘ x ∘ i) (A ∘ x ∘ i) (H ∘ i) :=
      fun _ => (hcons hfirst).comp hi.tendsto_atTop
    have hzero := theorem_13_12_6
      ((PiLp.continuous_ofLp _ _).continuousAt.tendsto.comp hzi) (hg.tendsto.comp hzi)
      (hA.tendsto.comp hzi) (fun k => hpos (i k))
      (hfirst.comp hi.tendsto_atTop) hco he (fun k => (hepos k).le) (fun k w =>
        (mul_le_mul_of_nonneg_right (hib k).2.le (sq_nonneg _)).trans (hcurv (i k) w))
    exact hnoncritical hzero
  obtain ⟨a, ha, r, hr, hnear⟩ := hlocal
  let c := min a cap
  have hc : 0 < c := lt_min ha hcap
  have hpred (k : ℕ) (hk : τ k ≤ -a) :
      κ * a * min (c ^ 2) (Δ k ^ 2) ≤ pred k := by
    have hτ := hk.trans_lt (neg_lt_zero.mpr ha)
    have habs : a ≤ |τ k| := by rw [abs_of_neg hτ]; linarith
    have hmin : min (c ^ 2) (Δ k ^ 2) ≤ min (min (τ k ^ 2) (Δ k ^ 2)) (cap ^ 2) := by
      apply le_min
      · apply min_le_min _ le_rfl
        simpa only [sq_abs] using
          pow_le_pow_left₀ hc.le ((min_le_left a cap).trans habs) 2
      · exact (min_le_left _ _).trans (pow_le_pow_left₀ hc.le (min_le_right a cap) 2)
    exact (mul_le_mul (mul_le_mul_of_nonneg_left habs hκ.le) hmin
      (le_min (sq_nonneg _) (sq_nonneg _)) (mul_nonneg hκ.le (abs_nonneg _))).trans (hdec k hτ)
  let margin := (1 - P.η₂) * (κ * a)
  have hm : 0 < margin := mul_pos (sub_pos.mpr P.eta₂_lt_one) (mul_pos hκ ha)
  obtain ⟨δ, hδ, herror⟩ := herr margin hm
  have hvery : ∀ᶠ k in atTop, dist (x k) z < r → Δ k ≤ min δ c → P.η₂ ≤ ρ k := by
    filter_upwards [hnear, herror] with k hn he hdist hsmall
    have hlow := hpred k (hn hdist)
    rw [min_eq_right (pow_le_pow_left₀ (hΔ k).le (hsmall.trans (min_le_right _ _)) 2)] at hlow
    have heq := colemanLiAcceptanceRatio_sub_one f (y k) (g (x k)) (v k) (H k)
      (by simpa [unscaledModel, affineQuadraticModel] using (hp k).ne')
    have hupper := (neg_abs_le _).trans' (neg_le_neg (he (hsmall.trans (min_le_left _ _))))
    have hb := mul_le_mul_of_nonneg_left hlow (sub_nonneg.mpr P.eta₂_lt_one.le)
    have hquot : -(1 - P.η₂) ≤
        (affineQuadraticModel (F k) (g (x k)) (H k) (v k) - f (y k + v k)) / pred k :=
      (le_div_iff₀ (hp k)).mpr (by dsimp [margin] at hupper; nlinarith only [hupper, hb])
    simp only [unscaledModel, affineQuadraticModel, Matrix.mulVec_zero, dotProduct_zero,
      mul_zero, add_zero] at heq
    change ρ k - 1 =
      (affineQuadraticModel (F k) (g (x k)) (H k) (v k) - f (y k + v k)) / pred k at heq
    rw [← heq] at hquot
    linarith
  have hsmall : ∀ ε > 0, ∀ᶠ k in atTop, dist (x k) z < r → k ∈ S → Δ k < ε := by
    intro ε hε
    let b := P.η₁ * (κ * a * min (c ^ 2) (ε ^ 2))
    have hb : 0 < b := mul_pos P.eta₁_pos (mul_pos (mul_pos hκ ha)
      (lt_min (sq_pos_of_pos hc) (sq_pos_of_pos hε)))
    filter_upwards [hnear, hdrop.eventually_lt_const hb] with k hn hd hk hs
    by_contra! hbad
    have hlow := (mul_le_mul_of_nonneg_left (min_le_min le_rfl
      (pow_le_pow_left₀ hε.le hbad 2)) (mul_nonneg hκ.le ha.le)).trans (hpred k (hn hk))
    exact hd.not_ge ((mul_le_mul_of_nonneg_left hlow P.eta₁_pos.le).trans (hf k hs))
  exact (false_of_local_radius_expansion hj hz
    (P.gamma₁_pos.trans_le P.gamma₁_le_gamma₂) P.gamma₂_lt_one hγ₃ hγ₄ hcapExpand hK
    hr (lt_min hδ hc) hΔ hstay
    (fun k hk => ((hrad k).unsuccessful (lt_of_not_ge hk)).2)
    (fun k hk => by
      have he : x (k + 1) = x k + s k := by rw [hupdate, ite_eq_left (show P.η₁ ≤ ρ k from hk)]
      rw [he, dist_eq_norm, add_sub_cancel_left]
      exact hstep k)
    (hvery.mono fun _ hk hr hd => P.eta₁_le_eta₂.trans (hk hr hd))
    (hvery.mono fun k hk hr hd hc => hgrow k (hk hr hd) hc) hsmall).elim

end Convergence

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

section TRAM

variable {m : Type*} [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m]

/-- The slack step from (13.12.28), obtained by eliminating the linear
constraint (13.12.32) when the slack vector is positive. -/
noncomputable def tramSlackStep (A : Matrix m ι ℝ) (c : m → ℝ) (s : ι → ℝ) : m → ℝ :=
  fun i ↦ (A *ᵥ s) i / Real.sqrt (c i)

/-- The model correction (A^T C^{-1}Y A) of (13.12.34). For the modified
model use the vector of absolute multiplier values for `y`. -/
noncomputable def tramCorrection (A : Matrix m ι ℝ) (c y : m → ℝ) : Matrix ι ι ℝ :=
  Aᵀ * Matrix.diagonal (fun i ↦ y i / c i) * A

/-- The model in (13.12.34) in displacement coordinates. Both terms
are evaluated at the free trial displacement `s`. -/
noncomputable def tramModel (mf : (ι → ℝ) → ℝ) (A : Matrix m ι ℝ)
    (c y : m → ℝ) (s : ι → ℝ) : ℝ :=
  mf s + (1 / 2) * (s ⬝ᵥ (tramCorrection A c y *ᵥ s))

/-- The metric (I+A^T C^{-1} A) of (13.12.35). -/
noncomputable def tramMetric (A : Matrix m ι ℝ) (c : m → ℝ) : Matrix ι ι ℝ :=
  1 + Aᵀ * Matrix.diagonal (fun i ↦ (c i)⁻¹) * A

/-- The trust-region norm in (13.12.35), induced by the reduced metric. -/
noncomputable def tramNorm (A : Matrix m ι ℝ) (c : m → ℝ) (s : ι → ℝ) : ℝ :=
  Real.sqrt (s ⬝ᵥ (tramMetric A c *ᵥ s))

omit [DecidableEq ι] in
/-- A positive slack vector gives exactly one slack step for each primal
step in (13.12.32). -/
theorem tramSlackStep_unique (A : Matrix m ι ℝ) {c : m → ℝ} (hc : ∀ i, 0 < c i)
    (s : ι → ℝ) (v : m → ℝ) :
    Matrix.diagonal (fun i ↦ Real.sqrt (c i)) *ᵥ v = A *ᵥ s ↔
      v = tramSlackStep A c s := by
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    rw [Matrix.mulVec_diagonal] at hi
    exact (eq_div_iff (Real.sqrt_pos.2 (hc i)).ne').2 (by simpa [mul_comm] using hi)
  · rintro rfl
    funext i
    rw [Matrix.mulVec_diagonal]
    exact mul_div_cancel₀ _ (Real.sqrt_pos.2 (hc i)).ne'

omit [DecidableEq ι] in
private theorem tramCorrection_quadratic (A : Matrix m ι ℝ) {c : m → ℝ} (hc : ∀ i, 0 < c i)
    (y : m → ℝ) (s : ι → ℝ) :
    s ⬝ᵥ (tramCorrection A c y *ᵥ s) = ∑ i, y i * (tramSlackStep A c s i) ^ 2 := by
  rw [tramCorrection, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_transpose_mulVec, dotProduct_comm, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mulVec_diagonal]
  unfold tramSlackStep
  rw [div_pow, Real.sq_sqrt (hc i).le]
  ring

omit [DecidableEq ι] in
/-- The reduced model is the joint model evaluated at the unique slack step. -/
theorem tramModel_eq_slackModel (mf : (ι → ℝ) → ℝ) (A : Matrix m ι ℝ) {c : m → ℝ}
    (hc : ∀ i, 0 < c i) (y : m → ℝ) (s : ι → ℝ) :
    tramModel mf A c y s = mf s + (1 / 2) * ∑ i, y i * (tramSlackStep A c s i) ^ 2 := by
  rw [tramModel, tramCorrection_quadratic A hc]

private theorem tramNorm_eq_slackNorm (A : Matrix m ι ℝ) {c : m → ℝ} (hc : ∀ i, 0 < c i)
    (s : ι → ℝ) :
    tramNorm A c s = Real.sqrt ((∑ i, s i ^ 2) + ∑ i, (tramSlackStep A c s i) ^ 2) := by
  have hmetric : tramMetric A c = 1 + tramCorrection A c (fun _ ↦ 1) := by
    simp [tramMetric, tramCorrection, one_div]
  rw [tramNorm, hmetric, Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add,
    tramCorrection_quadratic A hc]
  simp only [one_mul]
  congr 2
  simp only [dotProduct, pow_two]

/-- Eliminating the slack step preserves the original joint Euclidean
trust-region bound (13.12.33). The reduced bound (13.12.35) uses the
same radius, without the stray `n` in the printed display. -/
theorem tramNorm_le_iff_exists_slack (A : Matrix m ι ℝ) {c : m → ℝ} (hc : ∀ i, 0 < c i)
    (s : ι → ℝ) (Δ : ℝ) :
    tramNorm A c s ≤ Δ ↔ ∃ v : m → ℝ,
      Matrix.diagonal (fun i ↦ Real.sqrt (c i)) *ᵥ v = A *ᵥ s ∧
      Real.sqrt ((∑ i, s i ^ 2) + ∑ i, v i ^ 2) ≤ Δ := by
  simp only [tramSlackStep_unique A hc, tramNorm_eq_slackNorm A hc]
  exact ⟨fun h ↦ ⟨_, rfl, h⟩, fun ⟨_, rfl, h⟩ ↦ h⟩

/-- Minimizers of the reduced problem lift to minimizers of the joint
trust-region subproblem, and conversely. -/
theorem tramSubproblem_iff (mf : (ι → ℝ) → ℝ) (A : Matrix m ι ℝ) {c : m → ℝ}
    (hc : ∀ i, 0 < c i) (y : m → ℝ) (s : ι → ℝ) (Δ : ℝ) :
    let S := {t | tramNorm A c t ≤ Δ}
    let V := {q : (ι → ℝ) × (m → ℝ) |
      Matrix.diagonal (fun i ↦ Real.sqrt (c i)) *ᵥ q.2 = A *ᵥ q.1 ∧
      Real.sqrt ((∑ i, q.1 i ^ 2) + ∑ i, q.2 i ^ 2) ≤ Δ}
    let M := fun q : (ι → ℝ) × (m → ℝ) ↦ mf q.1 + (1 / 2) * ∑ i, y i * (q.2 i) ^ 2
    (s ∈ S ∧ IsMinOn (tramModel mf A c y) S s) ↔
      ((s, tramSlackStep A c s) ∈ V ∧ IsMinOn M V (s, tramSlackStep A c s)) := by
  dsimp only
  have hfeas (t : ι → ℝ) :
      (t, tramSlackStep A c t) ∈ {q : (ι → ℝ) × (m → ℝ) |
        Matrix.diagonal (fun i ↦ Real.sqrt (c i)) *ᵥ q.2 = A *ᵥ q.1 ∧
        Real.sqrt ((∑ i, q.1 i ^ 2) + ∑ i, q.2 i ^ 2) ≤ Δ} ↔ tramNorm A c t ≤ Δ := by
    simp [tramSlackStep_unique A hc, tramNorm_eq_slackNorm A hc]
  constructor
  · intro ⟨hs, hmin⟩
    refine ⟨(hfeas s).2 hs, isMinOn_iff.mpr ?_⟩
    rintro ⟨t, v⟩ ⟨hv, hΔ⟩
    obtain rfl := (tramSlackStep_unique A hc t v).1 hv
    have ht := (tramNorm_eq_slackNorm A hc t).trans_le hΔ
    simpa only [tramModel_eq_slackModel mf A hc] using (isMinOn_iff.mp hmin t ht)
  · intro ⟨hs, hmin⟩
    refine ⟨(hfeas s).1 hs, isMinOn_iff.mpr ?_⟩
    intro t ht
    simpa only [tramModel_eq_slackModel mf A hc] using
      (isMinOn_iff.mp hmin (t, tramSlackStep A c t) ((hfeas t).2 ht))

end TRAM

end ConnGouldToint.Chapter13
