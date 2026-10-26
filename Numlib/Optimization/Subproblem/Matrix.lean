import Numlib.Eigen.SymmetricPencil
import Numlib.Krylov.Preconditioned
import Numlib.Optimization.Subproblem.Stopping

/-!
# Matrix subproblems in the operator setting

The subproblems of [cartis2022evaluation] Chapters 8–10 are stated for real matrices: a symmetric
`H`, a symmetric positive definite scaling `M`, the norm `‖v‖_M = √⟪v, M v⟫` and its dual
`‖v‖_{M⁻¹}`. The backbone (`Numlib.Optimization.Subproblem.Model` and its successors) works with a
single symmetric operator on an inner product space. This file is the bridge: the space
`ScaledSpace hM` is `EuclideanSpace ℝ ι` with the inner product `⟪x, y⟫_M = ⟪M x, y⟫` (the energy
space of `Krylov.IsPreconditioner`), `toScaled hM` is the identity map into it, and

* `scaledOp H hM` is the operator `M⁻¹ H`, symmetric in `⟪·, ·⟫_M` (`isSymmetric_scaledOp`);
* `scaledGrad hM g` is the vector `M⁻¹ g`.

Every object of the book is the corresponding operator object: the model and the regularized model
(`quadModel_scaled`, `regModel_scaled`), the `M`-norm and the `M⁻¹`-norm (`norm_toScaled`,
`norm_scaledGrad_sq`), the gradient `g + H s + λ M s` (`scaledGrad_gradient`), positive
(semi)definiteness of `H + λ M` (`posSemidef_add_smul_iff_isPositive`,
`posDef_add_smul_iff_scaled`), the step `(H + λ M)⁻¹ (-g)` and the secular function for every `λ`
(`toScaled_step`, `secular_scaled`; more generally solves with `H + λ M`, `toScaled_inv_apply`,
`toScaled_inv_mul_apply`, and invertibility both ways, `isUnit_add_smul_scaledOp`,
`isUnit_of_isUnit_add_smul_scaledOp`), the eigenvalues of the pencil `(H, M)`
(`eigenvalues_scaledOp`, `leftmost_scaledOp`, `rightmost_scaledOp`) and its eigenvectors
(`scaledOp_toScaled_of_eigen`, `eigen_of_scaledOp_eq`, `eigen_of_mem_ker`,
`exists_eigen_of_eigenvalues`, `exists_scaledOp_scaledGrad_eq_iff`),
the norm `‖M⁻¹ H‖₂` (`norm_scaledOp_le`), the kernels of `H + λ M` and consistency of
`(H + λ M) x = -g` (`toScaled_mem_ker_iff`, `scaledGrad_mem_orthogonal_iff`), the
minimum-`M`-norm solution (`toScaled_eq_particular_iff`, `particular_scaled_spec`), the Hessian of
the regularized model (`inner_regModelHessian_scaled`) and the stopping rules (9.3.14)
(`regStoppingRules_scaled_iff`).
-/

open Matrix
open scoped RealInnerProductSpace

namespace Subproblem

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H M : Matrix ι ι ℝ}

/-! ### The scaled space, operator and gradient -/

variable (hM : M.PosDef)

/-- The **`M`-inner product space**: `EuclideanSpace ℝ ι` with `⟪x, y⟫_M = ⟪M x, y⟫`, whose norm is
the book's `‖x‖_M` ([cartis2022evaluation] §8.1). -/
noncomputable abbrev ScaledSpace : Type _ := hM.isPreconditioner_toEuclideanLin.EnergySpace

/-- The identity map from `EuclideanSpace ℝ ι` into the `M`-inner product space. -/
noncomputable abbrev toScaled : EuclideanSpace ℝ ι ≃ₗ[ℝ] ScaledSpace hM :=
  hM.isPreconditioner_toEuclideanLin.toEnergy

variable (H) in
/-- The **scaled operator** `M⁻¹ H` on the `M`-inner product space, symmetric there when `H` is
(`isSymmetric_scaledOp`). Its eigenvalues are those of the pencil `(H, M)`
(`eigenvalues_scaledOp`). -/
noncomputable def scaledOp : ScaledSpace hM →L[ℝ] ScaledSpace hM :=
  LinearMap.toContinuousLinearMap
    (hM.isPreconditioner_toEuclideanLin.energyEnd (toEuclideanLin M⁻¹ ∘ₗ toEuclideanLin H))

/-- The **scaled gradient** `M⁻¹ g`, in the `M`-inner product space. Its norm there is the book's
`‖g‖_{M⁻¹}` (`norm_scaledGrad_sq`). -/
noncomputable def scaledGrad (g : EuclideanSpace ℝ ι) : ScaledSpace hM :=
  toScaled hM (toEuclideanLin M⁻¹ g)

variable {hM}

/-- The scaled operator acts on a transported vector as `M⁻¹ H`. -/
@[simp]
theorem scaledOp_toScaled (x : EuclideanSpace ℝ ι) :
    scaledOp H hM (toScaled hM x) = toScaled hM (toEuclideanLin M⁻¹ (toEuclideanLin H x)) :=
  rfl

/-- The `M`-inner product of transported vectors: `⟪x, y⟫_M = ⟪M x, y⟫`. -/
theorem inner_toScaled (x y : EuclideanSpace ℝ ι) :
    ⟪toScaled hM x, toScaled hM y⟫ = ⟪toEuclideanLin M x, y⟫ :=
  WithEnergy.inner_equiv _ _ x y

/-- `‖x‖_M² = ⟪M x, x⟫`. -/
theorem norm_toScaled_sq (x : EuclideanSpace ℝ ι) :
    ‖toScaled hM x‖ ^ 2 = ⟪toEuclideanLin M x, x⟫ := by
  rw [← real_inner_self_eq_norm_sq, inner_toScaled]

/-- `‖x‖_M = √⟪M x, x⟫`. -/
theorem norm_toScaled (x : EuclideanSpace ℝ ι) : ‖toScaled hM x‖ = √⟪toEuclideanLin M x, x⟫ := by
  rw [← norm_toScaled_sq, Real.sqrt_sq (norm_nonneg _)]

/-- The bilinear form of the scaled operator is that of `H`: `⟪M⁻¹ H x, y⟫_M = ⟪H x, y⟫`. -/
theorem inner_scaledOp_toScaled (x y : EuclideanSpace ℝ ι) :
    ⟪scaledOp H hM (toScaled hM x), toScaled hM y⟫ = ⟪toEuclideanLin H x, y⟫ :=
  hM.isPreconditioner_toEuclideanLin.inner_energyEnd_left _ x y

/-- `⟪M⁻¹ g, y⟫_M = ⟪g, y⟫`. -/
theorem inner_scaledGrad_toScaled (g y : EuclideanSpace ℝ ι) :
    ⟪scaledGrad hM g, toScaled hM y⟫ = ⟪g, y⟫ := by
  rw [real_inner_comm, scaledGrad, hM.isPreconditioner_toEuclideanLin.inner_toEnergy_inv,
    real_inner_comm]

/-- `⟪v, M⁻¹ g⟫_M = ⟪v, g⟫`: the coordinates `γᵢ = vᵢᵀ g` of the book's (8.2.6) are the
`M`-coordinates of the scaled gradient. -/
theorem inner_toScaled_scaledGrad (v g : EuclideanSpace ℝ ι) :
    ⟪toScaled hM v, scaledGrad hM g⟫ = ⟪v, g⟫ := by
  rw [real_inner_comm, inner_scaledGrad_toScaled, real_inner_comm]

/-- `‖M⁻¹ g‖_M² = ⟪g, M⁻¹ g⟫ = ‖g‖_{M⁻¹}²`. -/
theorem norm_scaledGrad_sq (g : EuclideanSpace ℝ ι) :
    ‖scaledGrad hM g‖ ^ 2 = ⟪g, toEuclideanLin M⁻¹ g⟫ :=
  hM.isPreconditioner_toEuclideanLin.norm_toEnergy_inv_sq g

/-- `M⁻¹ H` is symmetric in the `M`-inner product when `H` is symmetric. -/
theorem isSymmetric_scaledOp (hH : H.IsHermitian) :
    (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM).IsSymmetric :=
  (LinearMap.isSymmetric_iff_of_inner_map_eq (toScaled hM) fun x y => inner_scaledOp_toScaled x y).1
    (isSymmetric_toEuclideanLin_iff.2 hH)

/-! ### Models and gradients -/

/-- **The quadratic model in the scaled setting** ([cartis2022evaluation] (8.1.1)):
`⟪g, s⟫ + ½ ⟪s, H s⟫ = quadModel (M⁻¹ g) (M⁻¹ H) s` in the `M`-inner product space. -/
theorem quadModel_scaled (g s : EuclideanSpace ℝ ι) :
    ⟪g, s⟫ + (1 / 2) * ⟪s, toEuclideanLin H s⟫ =
      quadModel (scaledGrad hM g) (scaledOp H hM) (toScaled hM s) := by
  rw [quadModel, inner_scaledGrad_toScaled,
    real_inner_comm (scaledOp H hM (toScaled hM s)) (toScaled hM s), inner_scaledOp_toScaled,
    real_inner_comm (toEuclideanLin H s) s]

/-- **The regularized model in the scaled setting** ([cartis2022evaluation] (8.1.4)):
`⟪g, s⟫ + ½ ⟪s, H s⟫ + σ/r ‖s‖_M^r = regModel (M⁻¹ g) (M⁻¹ H) σ r s`. -/
theorem regModel_scaled (g s : EuclideanSpace ℝ ι) (σ r : ℝ) :
    ⟪g, s⟫ + (1 / 2) * ⟪s, toEuclideanLin H s⟫ + σ / r * √⟪toEuclideanLin M s, s⟫ ^ r =
      regModel (scaledGrad hM g) (scaledOp H hM) σ r (toScaled hM s) := by
  rw [regModel, ← quadModel_scaled, norm_toScaled]

/-- `(M⁻¹ H + λ) x = M⁻¹ (H + λ M) x` on transported vectors. -/
theorem add_smul_scaledOp_toScaled (lam : ℝ) (x : EuclideanSpace ℝ ι) :
    (scaledOp H hM + lam • (1 : ScaledSpace hM →L[ℝ] ScaledSpace hM)) (toScaled hM x) =
      toScaled hM (toEuclideanLin M⁻¹ (toEuclideanLin (H + lam • M) x)) := by
  simp only [_root_.add_apply, _root_.smul_apply, one_apply_eq_self,
    scaledOp_toScaled, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    toEuclideanLin_nonsing_inv_mul_apply hM.isUnit]

/-- **The gradient in the scaled setting** ([cartis2022evaluation] (8.2.34)): the Euclidean
gradient `v = g + H s + λ M s` satisfies `M⁻¹ v = M⁻¹ g + (M⁻¹ H + λ) s`, so its `M⁻¹`-norm
`√⟪v, M⁻¹ v⟫` (`norm_scaledGrad_sq`) is the norm of the operator gradient in the `M`-inner product
space. -/
theorem scaledGrad_gradient (g s : EuclideanSpace ℝ ι) (lam : ℝ) :
    scaledGrad hM (g + toEuclideanLin H s + lam • toEuclideanLin M s) =
      scaledGrad hM g + (scaledOp H hM + lam • (1 : ScaledSpace hM →L[ℝ] ScaledSpace hM))
        (toScaled hM s) := by
  have h : toEuclideanLin (H + lam • M) s = toEuclideanLin H s + lam • toEuclideanLin M s := by
    rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  rw [add_smul_scaledOp_toScaled, scaledGrad, scaledGrad, ← map_add, ← map_add, h, add_assoc]

/-! ### Definiteness, the step and the secular function -/

/-- The bilinear form of `M⁻¹ H + λ` in the `M`-inner product is that of `H + λ M`. -/
theorem inner_add_smul_scaledOp_toScaled (lam : ℝ) (x y : EuclideanSpace ℝ ι) :
    ⟪(scaledOp H hM + lam • (1 : ScaledSpace hM →L[ℝ] ScaledSpace hM)) (toScaled hM x),
      toScaled hM y⟫ = ⟪toEuclideanLin (H + lam • M) x, y⟫ := by
  simp only [_root_.add_apply, _root_.smul_apply, one_apply_eq_self,
    inner_add_left, inner_smul_left, inner_scaledOp_toScaled, inner_toScaled, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, conj_trivial]

/-- `H + λ M` is positive semidefinite iff `M⁻¹ H + λ` is positive in the `M`-inner product. -/
theorem posSemidef_add_smul_iff_isPositive (lam : ℝ) :
    (H + lam • M).PosSemidef ↔
      ((scaledOp H hM + lam • (1 : ScaledSpace hM →L[ℝ] ScaledSpace hM) : _ →L[ℝ] _) :
        ScaledSpace hM →ₗ[ℝ] ScaledSpace hM).IsPositive := by
  rw [← Matrix.isPositive_toEuclideanLin_iff]
  exact LinearMap.isPositive_iff_of_inner_map_eq (toScaled hM) fun x y =>
    inner_add_smul_scaledOp_toScaled lam x y

/-- `H + λ M` is positive definite iff `M⁻¹ H + λ` is symmetric coercive in the `M`-inner
product. -/
theorem posDef_add_smul_iff_isSymmetricCoercive (lam : ℝ) :
    (H + lam • M).PosDef ↔
      ((scaledOp H hM + lam • (1 : ScaledSpace hM →L[ℝ] ScaledSpace hM) : _ →L[ℝ] _) :
        ScaledSpace hM →ₗ[ℝ] ScaledSpace hM).IsSymmetricCoercive := by
  rw [Matrix.posDef_iff_isSymmetricCoercive]
  exact LinearMap.isSymmetricCoercive_iff_of_inner_map_eq (toScaled hM) fun x y =>
    inner_add_smul_scaledOp_toScaled lam x y

/-- The `M`-inner product space is nontrivial when `ι` is nonempty. -/
instance instNontrivialScaledSpace [Nonempty ι] : Nontrivial (ScaledSpace hM) :=
  (toScaled hM).injective.nontrivial

/-- **Definiteness of `H + λ M` and the leftmost eigenvalue** ([cartis2022evaluation] §8.2):
`H + λ M` is positive semidefinite iff `λ ≥ -λ₁` and positive definite iff `λ > -λ₁`, where
`λ₁ = leftmost` of the scaled operator (the least pencil eigenvalue, `leftmost_scaledOp`). -/
theorem posDef_add_smul_iff_scaled [Nonempty ι] (hH : H.IsHermitian) (lam : ℝ) :
    ((H + lam • M).PosSemidef ↔ -leftmost (isSymmetric_scaledOp (hM := hM) hH) ≤ lam) ∧
      ((H + lam • M).PosDef ↔ -leftmost (isSymmetric_scaledOp (hM := hM) hH) < lam) :=
  ⟨(posSemidef_add_smul_iff_isPositive lam).trans (isPositive_add_smul_iff lam),
    (posDef_add_smul_iff_isSymmetricCoercive lam).trans (isSymmetricCoercive_add_smul_iff lam)⟩

/-- If `H + λ M` is invertible then so is `M⁻¹ H + λ`. -/
theorem isUnit_add_smul_scaledOp {lam : ℝ} (hu : IsUnit (H + lam • M)) :
    IsUnit (scaledOp H hM + lam • (1 : ScaledSpace hM →L[ℝ] ScaledSpace hM)) := by
  rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_ker_eq_bot,
    LinearMap.ker_eq_bot']
  intro u hu0
  obtain ⟨x, rfl⟩ := (toScaled hM).surjective u
  rw [ContinuousLinearMap.coe_coe, add_smul_scaledOp_toScaled, LinearEquiv.map_eq_zero_iff] at hu0
  have h1 : toEuclideanLin (H + lam • M) x = 0 := by
    rw [← toEuclideanLin_mul_nonsing_inv_apply hM.isUnit (toEuclideanLin (H + lam • M) x), hu0,
      map_zero]
  rw [← toEuclideanLin_nonsing_inv_mul_apply hu x, h1, map_zero, map_zero]

/-- If `M⁻¹ H + λ` is invertible then so is `H + λ M` (the converse of
`isUnit_add_smul_scaledOp`). -/
theorem isUnit_of_isUnit_add_smul_scaledOp {lam : ℝ}
    (hu : IsUnit (scaledOp H hM + lam • (1 : ScaledSpace hM →L[ℝ] ScaledSpace hM))) :
    IsUnit (H + lam • M) := by
  rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_ker_eq_bot] at hu
  have hinj := LinearMap.ker_eq_bot.1 hu
  rw [← mulVec_injective_iff_isUnit]
  intro x y hxy
  have h : toScaled hM (WithLp.toLp 2 x) = toScaled hM (WithLp.toLp 2 y) := by
    apply hinj
    simp only [ContinuousLinearMap.coe_coe, add_smul_scaledOp_toScaled, toEuclideanLin_toLp, hxy]
  simpa using h

/-- **Solves with `H + λ M` in the scaled setting**: for every `λ`,
`(H + λ M)⁻¹ v` is, transported, `(M⁻¹ H + λ)⁻¹ (M⁻¹ v)` (both sides vanish when `H + λ M` is
singular, by the conventions `A⁻¹ = 0` and `Ring.inverse = 0` for non-units). -/
theorem toScaled_inv_apply (lam : ℝ) (v : EuclideanSpace ℝ ι) :
    toScaled hM (toEuclideanLin (H + lam • M)⁻¹ v) =
      Ring.inverse (scaledOp H hM + lam • (1 : ScaledSpace hM →L[ℝ] ScaledSpace hM))
        (toScaled hM (toEuclideanLin M⁻¹ v)) := by
  set T := scaledOp H hM + lam • (1 : ScaledSpace hM →L[ℝ] ScaledSpace hM) with hTdef
  by_cases hu : IsUnit (H + lam • M)
  · have hinv := congrArg (fun S : ScaledSpace hM →L[ℝ] ScaledSpace hM =>
      S (toScaled hM (toEuclideanLin (H + lam • M)⁻¹ v)))
      (Ring.inverse_mul_cancel _ (isUnit_add_smul_scaledOp (hM := hM) hu))
    change Ring.inverse T (T _) = _ at hinv
    rw [one_apply_eq_self, hTdef, add_smul_scaledOp_toScaled,
      toEuclideanLin_mul_nonsing_inv_apply hu] at hinv
    exact hinv.symm
  · have h1 : (H + lam • M)⁻¹ = 0 :=
      nonsing_inv_apply_not_isUnit _ (by rwa [← isUnit_iff_isUnit_det])
    have h2 : ¬ IsUnit T := fun h => hu (isUnit_of_isUnit_add_smul_scaledOp h)
    rw [h1, Ring.inverse_non_unit _ h2]
    simp

/-- `(H + λ M)⁻¹ M w` is, transported, `(M⁻¹ H + λ)⁻¹ w`, for every `λ`. -/
theorem toScaled_inv_mul_apply (lam : ℝ) (w : EuclideanSpace ℝ ι) :
    toScaled hM (toEuclideanLin (H + lam • M)⁻¹ (toEuclideanLin M w)) =
      Ring.inverse (scaledOp H hM + lam • (1 : ScaledSpace hM →L[ℝ] ScaledSpace hM))
        (toScaled hM w) := by
  rw [toScaled_inv_apply, toEuclideanLin_nonsing_inv_mul_apply hM.isUnit]

/-- **The step in the scaled setting** ([cartis2022evaluation] (8.2.2)): for every `λ`, the vector
`(H + λ M)⁻¹ (-g)` is the operator step of `M⁻¹ g` and `M⁻¹ H` (both vanish when `H + λ M` is
singular). -/
theorem toScaled_step (g : EuclideanSpace ℝ ι) (lam : ℝ) :
    toScaled hM (toEuclideanLin (H + lam • M)⁻¹ (-g)) =
      step (scaledGrad hM g) (scaledOp H hM) lam := by
  rw [toScaled_inv_apply, step, map_neg, map_neg, map_neg, scaledGrad]

/-- **The secular function in the scaled setting** ([cartis2022evaluation] (8.2.4)): for every
`λ`, with `s = (H + λ M)⁻¹ (-g)`, `π(λ) = ‖s‖_M² = ⟪M s, s⟫` is the secular function of `M⁻¹ g`
and `M⁻¹ H`. -/
theorem secular_scaled (g : EuclideanSpace ℝ ι) (lam : ℝ) :
    secular (scaledGrad hM g) (scaledOp H hM) lam =
      ⟪toEuclideanLin M (toEuclideanLin (H + lam • M)⁻¹ (-g)),
        toEuclideanLin (H + lam • M)⁻¹ (-g)⟫ := by
  rw [secular, ← toScaled_step g lam, norm_toScaled_sq]

/-! ### Kernels and the minimum-`M`-norm solution -/

/-- The kernel of `M⁻¹ H + λ` is the transport of the kernel of `H + λ M`. -/
theorem toScaled_mem_ker_iff (lam : ℝ) (x : EuclideanSpace ℝ ι) :
    toScaled hM x ∈ LinearMap.ker ((scaledOp H hM + lam • 1 : ScaledSpace hM →L[ℝ] ScaledSpace hM) :
      ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) ↔ x ∈ LinearMap.ker (toEuclideanLin (H + lam • M)) := by
  rw [LinearMap.mem_ker, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    add_smul_scaledOp_toScaled, LinearEquiv.map_eq_zero_iff]
  constructor
  · intro h
    rw [← toEuclideanLin_mul_nonsing_inv_apply hM.isUnit (toEuclideanLin (H + lam • M) x), h,
      map_zero]
  · intro h; rw [h, map_zero]

/-- Consistency transports: `M⁻¹ g` is `M`-orthogonal to `ker (M⁻¹ H + λ)` iff `g` is orthogonal
to `ker (H + λ M)`. -/
theorem scaledGrad_mem_orthogonal_iff (lam : ℝ) (g : EuclideanSpace ℝ ι) :
    scaledGrad hM g ∈ (LinearMap.ker ((scaledOp H hM + lam • 1 : ScaledSpace hM →L[ℝ]
      ScaledSpace hM) : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM))ᗮ ↔
      g ∈ (LinearMap.ker (toEuclideanLin (H + lam • M)))ᗮ := by
  rw [Submodule.mem_orthogonal', Submodule.mem_orthogonal']
  constructor
  · intro h y hy
    rw [← inner_scaledGrad_toScaled]
    exact h _ ((toScaled_mem_ker_iff lam y).2 hy)
  · intro h u hu
    obtain ⟨y, rfl⟩ := (toScaled hM).surjective u
    rw [inner_scaledGrad_toScaled]
    exact h y ((toScaled_mem_ker_iff lam y).1 hu)

/-- The shifted systems correspond: `(M⁻¹ H + λ) x = -M⁻¹ g` iff `(H + λ M) x = -g`. -/
theorem add_smul_scaledOp_toScaled_eq_neg_iff (lam : ℝ) (g x : EuclideanSpace ℝ ι) :
    (scaledOp H hM + lam • (1 : ScaledSpace hM →L[ℝ] ScaledSpace hM)) (toScaled hM x) =
      -scaledGrad hM g ↔ toEuclideanLin (H + lam • M) x = -g := by
  rw [add_smul_scaledOp_toScaled, scaledGrad, ← map_neg, ← map_neg,
    (toScaled hM).injective.eq_iff]
  constructor
  · intro h
    have := congrArg (toEuclideanLin M) h
    rwa [toEuclideanLin_mul_nonsing_inv_apply hM.isUnit,
      toEuclideanLin_mul_nonsing_inv_apply hM.isUnit] at this
  · intro h; rw [h]

/-- `M`-orthogonality to `ker (H + λ M)` in coordinates. -/
theorem toScaled_mem_orthogonal_ker_iff (lam : ℝ) (y : EuclideanSpace ℝ ι) :
    toScaled hM y ∈ (LinearMap.ker ((scaledOp H hM + lam • 1 : ScaledSpace hM →L[ℝ]
      ScaledSpace hM) : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM))ᗮ ↔
      ∀ v ∈ LinearMap.ker (toEuclideanLin (H + lam • M)), ⟪toEuclideanLin M y, v⟫ = 0 := by
  rw [Submodule.mem_orthogonal']
  constructor
  · intro h v hv
    rw [← inner_toScaled]
    exact h _ ((toScaled_mem_ker_iff lam v).2 hv)
  · intro h u hu
    obtain ⟨v, rfl⟩ := (toScaled hM).surjective u
    rw [inner_toScaled]
    exact h v ((toScaled_mem_ker_iff lam v).1 hu)

/-- **The minimum-`M`-norm solution is `particular`** ([cartis2022evaluation] (8.3.2)). If
`g ⊥ ker (H + λ M)`, a vector `x` is (the transport of) `particular` of the scaled problem iff it
solves `(H + λ M) x = -g` and is `M`-orthogonal to `ker (H + λ M)`. -/
theorem toScaled_eq_particular_iff (hH : H.IsHermitian) {lam : ℝ} {g : EuclideanSpace ℝ ι}
    (hg : g ∈ (LinearMap.ker (toEuclideanLin (H + lam • M)))ᗮ) (x : EuclideanSpace ℝ ι) :
    toScaled hM x = particular (isSymmetric_scaledOp hH) (scaledGrad hM g) lam ↔
      toEuclideanLin (H + lam • M) x = -g ∧
        ∀ v ∈ LinearMap.ker (toEuclideanLin (H + lam • M)), ⟪toEuclideanLin M x, v⟫ = 0 := by
  have hT := isSymmetric_scaledOp (hM := hM) hH
  have hg' := (scaledGrad_mem_orthogonal_iff (H := H) (hM := hM) lam g).2 hg
  obtain ⟨hsol, hiff, -, -⟩ := (particular_spec (hH := hT) (g := scaledGrad hM g) lam).2.1 hg'
  have hperp := (particular_spec (hH := hT) (g := scaledGrad hM g) lam).1
  constructor
  · intro h
    rw [← h] at hsol hperp
    exact ⟨(add_smul_scaledOp_toScaled_eq_neg_iff lam g x).1 hsol,
      (toScaled_mem_orthogonal_ker_iff lam x).1 hperp⟩
  · rintro ⟨h1, h2⟩
    have hk := (hiff _).1 ((add_smul_scaledOp_toScaled_eq_neg_iff lam g x).2 h1)
    have hp := Submodule.sub_mem _ ((toScaled_mem_orthogonal_ker_iff lam x).2 h2) hperp
    exact sub_eq_zero.1 (inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal hk hp))

/-- **`particular` of the scaled problem is the minimum-`M`-norm solution** of
`(H + λ M) x = -g` ([cartis2022evaluation] (8.3.2)), when `g ⊥ ker (H + λ M)`. -/
theorem particular_scaled_spec (hH : H.IsHermitian) {lam : ℝ} {g : EuclideanSpace ℝ ι}
    (hg : g ∈ (LinearMap.ker (toEuclideanLin (H + lam • M)))ᗮ) :
    toEuclideanLin (H + lam • M)
        ((toScaled hM).symm (particular (isSymmetric_scaledOp hH) (scaledGrad hM g) lam)) = -g ∧
      ∀ y, toEuclideanLin (H + lam • M) y = -g →
        ⟪toEuclideanLin M ((toScaled hM).symm
            (particular (isSymmetric_scaledOp hH) (scaledGrad hM g) lam)),
          (toScaled hM).symm (particular (isSymmetric_scaledOp hH) (scaledGrad hM g) lam)⟫ ≤
          ⟪toEuclideanLin M y, y⟫ := by
  have hT := isSymmetric_scaledOp (hM := hM) hH
  have hg' := (scaledGrad_mem_orthogonal_iff (H := H) (hM := hM) lam g).2 hg
  obtain ⟨hsol, -, hmin, -⟩ := (particular_spec (hH := hT) (g := scaledGrad hM g) lam).2.1 hg'
  set p := particular hT (scaledGrad hM g) lam
  have hp : toScaled hM ((toScaled hM).symm p) = p := (toScaled hM).apply_symm_apply p
  refine ⟨(add_smul_scaledOp_toScaled_eq_neg_iff lam g _).1 (by rw [hp]; exact hsol),
    fun y hy => ?_⟩
  rw [← norm_toScaled_sq, ← norm_toScaled_sq, hp]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (hmin _ ((add_smul_scaledOp_toScaled_eq_neg_iff lam g y).2 hy)) 2

/-! ### The Hessian and the stopping rules -/

/-- **The Hessian of the regularized model in the scaled setting** ([cartis2022evaluation]
(8.2.34)): with `n = ‖s‖_M` (`norm_toScaled`),
`⟪v, ∇²m^R(s) w⟫_M = vᵀ (H + σ n^{r-2} M + (r-2) σ n^{r-4} (M s)(M s)ᵀ) w`. -/
theorem inner_regModelHessian_scaled (σ r : ℝ) (s v w : EuclideanSpace ℝ ι) :
    ⟪toScaled hM v, regModelHessian (scaledOp H hM) σ r (toScaled hM s) (toScaled hM w)⟫ =
      ⟪v, toEuclideanLin H w⟫ + σ * ‖toScaled hM s‖ ^ (r - 2) * ⟪v, toEuclideanLin M w⟫ +
        (r - 2) * σ * ‖toScaled hM s‖ ^ (r - 4) *
          (⟪toEuclideanLin M s, v⟫ * ⟪toEuclideanLin M s, w⟫) := by
  have hMs := isSymmetric_toEuclideanLin_iff.2 hM.isHermitian
  have e1 : ⟪toScaled hM v, scaledOp H hM (toScaled hM w)⟫ = ⟪v, toEuclideanLin H w⟫ := by
    rw [real_inner_comm, inner_scaledOp_toScaled, real_inner_comm]
  have e2 : ⟪toScaled hM v, toScaled hM w⟫ = ⟪v, toEuclideanLin M w⟫ := by
    rw [inner_toScaled]; exact hMs v w
  have e3 : ⟪toScaled hM v, toScaled hM s⟫ = ⟪toEuclideanLin M s, v⟫ := by
    rw [real_inner_comm, inner_toScaled]
  have e4 : ⟪toScaled hM s, toScaled hM w⟫ = ⟪toEuclideanLin M s, w⟫ := inner_toScaled s w
  rw [regModelHessian_apply]
  simp only [inner_add_right, inner_smul_right, e1, e2, e3, e4]
  ring

/-- **The stopping rules (9.3.14) in the scaled setting**: for `r ≠ 0` and `n = ‖s‖_M`
(`norm_toScaled`), the operator rules for `M⁻¹ g`, `M⁻¹ H` at `s` say
(9.3.14a) `⟪g, s⟫ + ½ ⟪s, H s⟫ + σ/r n^r ≤ 0`;
(9.3.14b) `‖g + H s + σ n^{r-2} M s‖_{M⁻¹} ≤ ½ θ₁ n²`, the dual norm being `√⟪v, M⁻¹ v⟫`;
(9.3.14c) `-θ₂ n ⟪M w, w⟫ ≤ wᵀ ∇²m^R(s) w` for all `w`, with the Hessian (8.2.34)
(`inner_regModelHessian_scaled`), i.e. `λ_min[∇²m^R(s), M] ≥ -θ₂ n`. -/
theorem regStoppingRules_scaled_iff {σ r θ₁ θ₂ : ℝ} (hr : r ≠ 0) (g s : EuclideanSpace ℝ ι) :
    RegStoppingRules (scaledGrad hM g) (scaledOp H hM) σ r θ₁ θ₂ (toScaled hM s) ↔
      ⟪g, s⟫ + (1 / 2) * ⟪s, toEuclideanLin H s⟫ + σ / r * ‖toScaled hM s‖ ^ r ≤ 0 ∧
      √⟪g + toEuclideanLin H s + (σ * ‖toScaled hM s‖ ^ (r - 2)) • toEuclideanLin M s,
          toEuclideanLin M⁻¹
            (g + toEuclideanLin H s + (σ * ‖toScaled hM s‖ ^ (r - 2)) • toEuclideanLin M s)⟫ ≤
        (1 / 2) * θ₁ * ‖toScaled hM s‖ ^ 2 ∧
      ∀ w, -(θ₂ * ‖toScaled hM s‖) * ⟪toEuclideanLin M w, w⟫ ≤
        ⟪w, toEuclideanLin H w⟫ + σ * ‖toScaled hM s‖ ^ (r - 2) * ⟪w, toEuclideanLin M w⟫ +
          (r - 2) * σ * ‖toScaled hM s‖ ^ (r - 4) *
            (⟪toEuclideanLin M s, w⟫ * ⟪toEuclideanLin M s, w⟫) := by
  set lam := σ * ‖toScaled hM s‖ ^ (r - 2)
  have hdec : regModel (scaledGrad hM g) (scaledOp H hM) σ r (toScaled hM s) =
      ⟪g, s⟫ + (1 / 2) * ⟪s, toEuclideanLin H s⟫ + σ / r * ‖toScaled hM s‖ ^ r := by
    rw [regModel_def, ← quadModel_scaled]
  have hgrad : scaledGrad hM g + scaledOp H hM (toScaled hM s) + lam • toScaled hM s =
      scaledGrad hM (g + toEuclideanLin H s + lam • toEuclideanLin M s) := by
    rw [scaledGrad_gradient, _root_.add_apply, _root_.smul_apply, one_apply_eq_self, add_assoc]
  have hnorm : ∀ u : ScaledSpace hM, ‖u‖ = √(‖u‖ ^ 2) := fun u =>
    (Real.sqrt_sq (norm_nonneg u)).symm
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, fun w => ?_⟩
    · rwa [hdec, regModel_zero _ _ _ hr] at h1
    · rwa [hgrad, hnorm, norm_scaledGrad_sq] at h2
    · have := h3 (toScaled hM w)
      rwa [inner_regModelHessian_scaled, norm_toScaled_sq] at this
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, fun u => ?_⟩
    · rwa [hdec, regModel_zero _ _ _ hr]
    · rwa [hgrad, hnorm, norm_scaledGrad_sq]
    · obtain ⟨w, rfl⟩ := (toScaled hM).surjective u
      rw [inner_regModelHessian_scaled, norm_toScaled_sq]
      exact h3 w

/-! ### Eigenvalues and eigenvectors -/

/-- The `M`-inner product space has dimension `card ι`. -/
theorem finrank_scaledSpace : Module.finrank ℝ (ScaledSpace hM) = Fintype.card ι := by
  rw [← (toScaled hM).finrank_eq, finrank_euclideanSpace]

/-- A generalized eigenvector `H v = μ M v` of the pencil is an eigenvector of `M⁻¹ H`. With
`inner_toScaled`, `M`-orthonormal generalized eigenvectors (`VᵀMV = I`, (8.2.5)) are orthonormal
eigenvectors of the scaled operator, and `inner_toScaled_scaledGrad` gives their coordinates
`γᵢ = vᵢᵀ g`. -/
theorem scaledOp_toScaled_of_eigen {v : EuclideanSpace ℝ ι} {μ : ℝ}
    (hv : toEuclideanLin H v = μ • toEuclideanLin M v) :
    scaledOp H hM (toScaled hM v) = μ • toScaled hM v := by
  rw [scaledOp_toScaled, hv, map_smul, toEuclideanLin_nonsing_inv_mul_apply hM.isUnit, map_smul]

/-- The real quadratic form of `toEuclideanLin A` in coordinates. -/
private theorem inner_toEuclideanLin_toLp (A : Matrix ι ι ℝ) (y : ι → ℝ) :
    ⟪toEuclideanLin A (WithLp.toLp 2 y), WithLp.toLp 2 y⟫ = star y ⬝ᵥ A *ᵥ y := by
  rw [toEuclideanLin_toLp, EuclideanSpace.inner_toLp_toLp_real, star_trivial, dotProduct_comm]

/-- **The eigenvalues of the scaled operator are the pencil eigenvalues** (sorted decreasingly,
as both families are): `eigenvalues` of `M⁻¹ H` in the `M`-inner product is
`Matrix.pencilEigenvalues hH hM`. Both are characterized by the Courant–Fischer max–min principle,
for the Rayleigh quotient `⟪H x, x⟫ / ⟪M x, x⟫`. -/
theorem eigenvalues_scaledOp (hH : H.IsHermitian) :
    (isSymmetric_scaledOp (hM := hM) hH).eigenvalues finrank_scaledSpace =
      pencilEigenvalues hH hM := by
  funext i
  set Φ : (ι → ℝ) ≃ₗ[ℝ] ScaledSpace hM := (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm.trans (toScaled hM)
  have hΦ : ∀ y, (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM).rayleighQuotient (Φ y) =
      RCLike.re (star y ⬝ᵥ H *ᵥ y) / RCLike.re (star y ⬝ᵥ M *ᵥ y) := fun y => by
    simp only [LinearMap.rayleighQuotient, RCLike.re_to_real, ContinuousLinearMap.coe_coe]
    rw [norm_sq_eq_re_inner (𝕜 := ℝ), RCLike.re_to_real]
    change ⟪scaledOp H hM (toScaled hM (WithLp.toLp 2 y)), toScaled hM (WithLp.toLp 2 y)⟫ /
      ⟪toScaled hM (WithLp.toLp 2 y), toScaled hM (WithLp.toLp 2 y)⟫ = _
    rw [inner_scaledOp_toScaled, inner_toScaled, inner_toEuclideanLin_toLp,
      inner_toEuclideanLin_toLp]
  have h1 := (isSymmetric_scaledOp (hM := hM) hH).isGreatest_eigenvalues finrank_scaledSpace i
  rw [Matrix.setOf_exists_submodule_eq Φ hΦ _ (· ≤ ·)] at h1
  exact h1.unique (isGreatest_pencilEigenvalues hH hM i)

/-- **The leftmost eigenvalue of the scaled operator is the least pencil eigenvalue** `λ₁` of
`(H, M)` ([cartis2022evaluation] (8.2.5)), so `shiftThreshold` of the scaled operator is the book's
`λₛ = max(0, -λ₁)`. -/
theorem leftmost_scaledOp (hH : H.IsHermitian) :
    leftmost (isSymmetric_scaledOp (hM := hM) hH) = ⨅ i, pencilEigenvalues hH hM i := by
  rw [← eigenvalues_scaledOp hH, leftmost]
  simp_rw [LinearMap.IsSymmetric.eigenvalues_eq_cast _ finrank_scaledSpace]
  exact ((finCongr finrank_scaledSpace.symm).iInf_comp
    (g := fun j => (isSymmetric_scaledOp (hM := hM) hH).eigenvalues rfl j)).symm

/-- **The norm of the scaled operator** is at most the Euclidean operator norm `‖M⁻¹ H‖₂`
(`Matrix.l2_opNorm_eq_norm_toEuclideanLin`): the operator norm of a symmetric operator is its
largest absolute eigenvalue, and each eigenvalue `μ` of `M⁻¹ H` satisfies `|μ| ≤ ‖M⁻¹ H‖₂`. -/
theorem norm_scaledOp_le (hH : H.IsHermitian) :
    ‖scaledOp H hM‖ ≤ ‖LinearMap.toContinuousLinearMap (toEuclideanLin (M⁻¹ * H))‖ := by
  set C := ‖LinearMap.toContinuousLinearMap (toEuclideanLin (M⁻¹ * H))‖
  have hT := isSymmetric_scaledOp (hM := hM) hH
  set b := hT.eigenvectorBasis rfl
  set μ := hT.eigenvalues rfl
  -- every eigenvalue is bounded by `C`
  have hμ : ∀ i, |μ i| ≤ C := fun i => by
    obtain ⟨x, hx⟩ := (toScaled hM).surjective (b i)
    have hx0 : x ≠ 0 := by
      rintro rfl; exact (b.orthonormal.ne_zero i) (by rw [← hx, map_zero])
    have heig : scaledOp H hM (b i) = μ i • b i := apply_eigenvectorBasis' (hH := hT) i
    rw [← hx, scaledOp_toScaled, ← map_smul] at heig
    have hMH : toEuclideanLin (M⁻¹ * H) x = μ i • x := by
      rw [toEuclideanLin_mul_apply]; exact (toScaled hM).injective heig
    have hle := (LinearMap.toContinuousLinearMap (toEuclideanLin (M⁻¹ * H))).le_opNorm x
    rw [LinearMap.coe_toContinuousLinearMap', hMH, norm_smul, Real.norm_eq_abs] at hle
    exact le_of_mul_le_mul_right hle (norm_pos_iff.2 hx0)
  have hC : 0 ≤ C := norm_nonneg _
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun u => ?_
  have hcoord : ∀ i, ⟪b i, scaledOp H hM u⟫ = μ i * ⟪b i, u⟫ := fun i => by
    rw [← ContinuousLinearMap.coe_coe, ← hT, ContinuousLinearMap.coe_coe,
      apply_eigenvectorBasis' (hH := hT) i, real_inner_smul_left]
  have hsq : ‖scaledOp H hM u‖ ^ 2 ≤ (C * ‖u‖) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_eq_sum_eigenvectorBasis (hH := hT), mul_pow,
      ← real_inner_self_eq_norm_sq u, inner_eq_sum_eigenvectorBasis (hH := hT), Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [hcoord]
    have : (μ i) ^ 2 ≤ C ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hμ i) 2
    nlinarith [sq_nonneg ⟪b i, u⟫]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-! ### Generalized eigenvectors and the scaled gradient -/

/-- The scaled gradient vanishes only for `g = 0`. -/
theorem scaledGrad_ne_zero {g : EuclideanSpace ℝ ι} (hg : g ≠ 0) : scaledGrad hM g ≠ 0 := by
  intro h
  apply hg
  have h2 : toEuclideanLin M⁻¹ g = 0 := by
    rw [scaledGrad, LinearEquiv.map_eq_zero_iff] at h; exact h
  rw [← toEuclideanLin_mul_nonsing_inv_apply hM.isUnit g, h2, map_zero]

@[simp]
theorem scaledGrad_zero : scaledGrad hM (0 : EuclideanSpace ℝ ι) = 0 := by
  simp [scaledGrad]

/-- A vector with `M⁻¹ H u = c u` is a generalized eigenvector of the pencil: `H u = c M u` (the
converse of `scaledOp_toScaled_of_eigen`). -/
theorem eigen_of_scaledOp_eq {u : EuclideanSpace ℝ ι} {c : ℝ}
    (h : scaledOp H hM (toScaled hM u) = c • toScaled hM u) :
    toEuclideanLin H u = c • toEuclideanLin M u := by
  rw [scaledOp_toScaled, ← map_smul, (toScaled hM).injective.eq_iff] at h
  have := congrArg (toEuclideanLin M) h
  rwa [toEuclideanLin_mul_nonsing_inv_apply hM.isUnit, map_smul] at this

/-- A vector of `ker (M⁻¹ H + μ)` is, transported back, a generalized eigenvector of `(H, M)` for
the eigenvalue `-μ`. -/
theorem eigen_of_mem_ker {μ : ℝ} {w : ScaledSpace hM}
    (hw : w ∈ LinearMap.ker ((scaledOp H hM + μ • 1 : ScaledSpace hM →L[ℝ] ScaledSpace hM) :
      ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)) :
    toEuclideanLin H ((toScaled hM).symm w) = (-μ) • toEuclideanLin M ((toScaled hM).symm w) := by
  rw [← (toScaled hM).apply_symm_apply w, toScaled_mem_ker_iff, LinearMap.mem_ker, map_add,
    map_smul, LinearMap.add_apply, LinearMap.smul_apply] at hw
  rw [neg_smul, eq_neg_iff_add_eq_zero]
  exact hw

/-- `M⁻¹ g` is an eigenvector of `M⁻¹ H` iff `g = M v` for a generalized eigenvector `v` of the
pencil `(H, M)`. -/
theorem exists_scaledOp_scaledGrad_eq_iff {g : EuclideanSpace ℝ ι} :
    (∃ c : ℝ, scaledOp H hM (scaledGrad hM g) = c • scaledGrad hM g) ↔
      ∃ (v : EuclideanSpace ℝ ι) (c : ℝ), toEuclideanLin M v = g ∧
        toEuclideanLin H v = c • toEuclideanLin M v := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨toEuclideanLin M⁻¹ g, c, toEuclideanLin_mul_nonsing_inv_apply hM.isUnit g, ?_⟩
    exact eigen_of_scaledOp_eq hc
  · rintro ⟨v, c, rfl, hv⟩
    refine ⟨c, ?_⟩
    rw [scaledGrad, toEuclideanLin_nonsing_inv_mul_apply hM.isUnit]
    exact scaledOp_toScaled_of_eigen hv

/-- Every eigenvalue of the scaled operator is a generalized eigenvalue of `(H, M)`, with a nonzero
eigenvector. -/
theorem exists_eigen_of_eigenvalues (hH : H.IsHermitian)
    (i : Fin (Module.finrank ℝ (ScaledSpace hM))) :
    ∃ u : EuclideanSpace ℝ ι, u ≠ 0 ∧ toEuclideanLin H u =
      (isSymmetric_scaledOp (hM := hM) hH).eigenvalues rfl i • toEuclideanLin M u := by
  set hT := isSymmetric_scaledOp (hM := hM) hH
  refine ⟨(toScaled hM).symm (hT.eigenvectorBasis rfl i), ?_, eigen_of_scaledOp_eq (hM := hM) ?_⟩
  · simpa using (hT.eigenvectorBasis rfl).orthonormal.ne_zero i
  · rw [LinearEquiv.apply_symm_apply]; exact apply_eigenvectorBasis' (hH := hT) i

/-- **The rightmost eigenvalue of the scaled operator is the largest pencil eigenvalue** `λₙ` of
`(H, M)`. -/
theorem rightmost_scaledOp (hH : H.IsHermitian) :
    rightmost (isSymmetric_scaledOp (hM := hM) hH) = ⨆ i, pencilEigenvalues hH hM i := by
  rw [← eigenvalues_scaledOp hH, rightmost]
  simp_rw [LinearMap.IsSymmetric.eigenvalues_eq_cast _ finrank_scaledSpace]
  exact ((finCongr finrank_scaledSpace.symm).iSup_comp
    (g := fun j => (isSymmetric_scaledOp (hM := hM) hH).eigenvalues rfl j)).symm

end Subproblem
