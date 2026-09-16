/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Operator.Bilinear`, beside `ContinuousLinearMap.le_opNorm₂`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.RCLike.Basic

/-!
# Operator-norm estimates for curried multilinear maps

Elementary bounds for continuous multilinear maps presented in curried form, `X →L[ℝ] X →L[ℝ] X`
and `X →L[ℝ] X →L[ℝ] X →L[ℝ] X`, which is the shape the iterated Fréchet derivative takes when it
is carried around as a chain of `ContinuousLinearMap`s rather than as a
`ContinuousMultilinearMap`.

## Main statements

* `ContinuousLinearMap.le_opNorm₃` — the three-argument companion of Mathlib's
  `ContinuousLinearMap.le_opNorm₂`.
* `norm_bilinear_diag_sub_le`, `norm_trilinear_diag_sub_le` — the diagonal `w ↦ B w w` of a
  bilinear map and `w ↦ C w w w` of a trilinear map are Lipschitz on bounded sets, with the
  first-order cross terms kept explicitly. These are what bound the remainder of a Taylor
  expansion whose perturbation is itself only known to first order.
* `ContinuousLinearMap.norm_comp_le_of_norm_le_one` — post-composition with a norm-nonincreasing
  map does not increase the operator norm. Applied at each level of a curried tower, it carries a
  bound on the derivatives of a map to the derivatives of its composition with a projection.
-/

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **The operator bound for a trilinear map** in curried form:
`‖C x y z‖ ≤ ‖C‖ ‖x‖ ‖y‖ ‖z‖`, the three-argument companion of
`ContinuousLinearMap.le_opNorm₂`. -/
theorem ContinuousLinearMap.le_opNorm₃ (C : X →L[ℝ] X →L[ℝ] X →L[ℝ] X) (x y z : X) :
    ‖C x y z‖ ≤ ‖C‖ * ‖x‖ * ‖y‖ * ‖z‖ := by
  calc ‖C x y z‖ ≤ ‖C x y‖ * ‖z‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖C‖ * ‖x‖ * ‖y‖ * ‖z‖ := by
        gcongr
        exact ContinuousLinearMap.le_opNorm₂ _ _ _

/-- **The diagonal of a bilinear map under a perturbation**: with `e` a first approximation of the
perturbation `d`, `B (g + d) (g + d)` differs from `B g g + B e g + B g e` by
`B (d - e) g + B g (d - e) + B d d`, hence by at most `‖B‖ (2 ‖g‖ ‖d - e‖ + ‖d‖²)`. This is what
bounds the `h³` error of a Runge–Kutta stage ([quarteroni2000numerical] §11.8). -/
theorem norm_bilinear_diag_sub_le (B : X →L[ℝ] X →L[ℝ] X) (g d e : X) :
    ‖B (g + d) (g + d) - B g g - B e g - B g e‖
      ≤ ‖B‖ * ‖d - e‖ * ‖g‖ + ‖B‖ * ‖g‖ * ‖d - e‖ + ‖B‖ * ‖d‖ * ‖d‖ := by
  have key : B (g + d) (g + d) - B g g - B e g - B g e
      = B (d - e) g + B g (d - e) + B d d := by
    simp only [map_add, map_sub, _root_.add_apply, _root_.sub_apply]
    abel
  rw [key]
  refine norm_add₃_le.trans ?_
  gcongr <;> exact ContinuousLinearMap.le_opNorm₂ _ _ _

/-- **The diagonal of a trilinear map is Lipschitz on bounded sets**:
`C x x x - C y y y = C (x - y) x x + C y (x - y) x + C y y (x - y)`, so the difference is at most
`‖C‖ (‖x‖² + ‖x‖‖y‖ + ‖y‖²) ‖x - y‖` ([quarteroni2000numerical] §11.8). -/
theorem norm_trilinear_diag_sub_le (C : X →L[ℝ] X →L[ℝ] X →L[ℝ] X) (x y : X) :
    ‖C x x x - C y y y‖
      ≤ ‖C‖ * ‖x - y‖ * ‖x‖ * ‖x‖ + ‖C‖ * ‖y‖ * ‖x - y‖ * ‖x‖
        + ‖C‖ * ‖y‖ * ‖y‖ * ‖x - y‖ := by
  have key : C x x x - C y y y = C (x - y) x x + C y (x - y) x + C y y (x - y) := by
    simp only [map_sub, _root_.sub_apply]
    abel
  rw [key]
  refine norm_add₃_le.trans ?_
  gcongr <;> exact ContinuousLinearMap.le_opNorm₃ _ _ _ _

/-- **Post-composition with a norm-nonincreasing map does not increase the operator norm**:
`‖J ∘L L‖ ≤ ‖L‖` when `‖J‖ ≤ 1`. Applied at each level of multilinearity, this is what carries a
bound on the derivatives of `f` to the derivatives of the autonomized field `(1, f)`. -/
theorem ContinuousLinearMap.norm_comp_le_of_norm_le_one {𝕜 : Type*} [RCLike 𝕜]
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G] (J : F →L[𝕜] G) (hJ : ‖J‖ ≤ 1)
    (L : E →L[𝕜] F) : ‖J.comp L‖ ≤ ‖L‖ := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  calc ‖J‖ * ‖L‖ ≤ 1 * ‖L‖ := by
        refine mul_le_mul_of_nonneg_right hJ (ContinuousLinearMap.opNorm_nonneg L)
    _ = ‖L‖ := one_mul _

