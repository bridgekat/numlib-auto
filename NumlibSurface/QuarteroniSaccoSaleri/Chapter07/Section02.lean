import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Numlib.Optimization.ConjugateGradient
import Numlib.Optimization.LineSearch
import Numlib.Optimization.QuasiNewton
import Numlib.Projection.ConjugateDirection
import NumlibSurface.QuarteroniSaccoSaleri.Chapter07.Section01

/-!
# Quarteroni–Sacco–Saleri §7.2: unconstrained optimization

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §7.2, the minimization of `f : ℝⁿ → ℝ`: the optimality conditions of
Property 7.4 with the Hessian matrix and critical points, Example 7.5, descent methods
(7.25)–(7.28) and Theorem 7.3, the line search conditions (7.31)–(7.34) and Property 7.5, the
quadratic case (7.35)–(7.39) with Lemma 7.1 (Kantorovich) and Property 7.6 (conjugate
directions), the conjugate gradient method for minimization and Remark 7.2, Newton's method for
minimization (7.40)–(7.41), the global convergence Properties 7.7–7.8, and the secant updates
(7.42)–(7.46) of §7.2.7. The backbone is `Numlib/Optimization/{Descent, LineSearch,
ConjugateGradient, QuasiNewton}`, `Numlib/Projection/{OneDimensional, ConjugateDirection}`,
`Numlib/Krylov/CG` and `Numlib/Analysis/InnerProductSpace/Energy`.

## Conventions

Gradients are Mathlib's `gradient f x` on `EuclideanSpace ℝ (Fin n)`, which the backbone's
derivative data `f' = fderiv ℝ f` reach through `fderiv_eq_innerSL_gradient`
(`fderiv ℝ f x = innerSL ℝ (gradient f x)`, so `fderiv ℝ f x d = ⟪∇f(x), d⟫`). The Hessian
matrix `H(x)` is `hessianMatrix f x`, the matrix of the second partial derivatives
`∂²f/∂xᵢ∂xⱼ`, with bridges to the second Fréchet derivative and to the derivative of the gradient
map (`hasFDerivAt_gradient`) for `C²` functions. A descent method (7.25)–(7.26) is the
backbone's relational `Descent.IsDescentSequence (fderiv ℝ f) x d α`. The quadratic (7.35) is
`energyFunctional (toEuclideanLin A) b`, and its line-search and conjugate-direction iterations
are `Projection.step1` and `ConjugateDirection.iterate` of the backbone.

## Readings and errata

* Property 7.4 (c) reads "if `x* ∈ B(x*; R)` and `H(x*)` is positive definite then `x*` is a
  local minimizer"; the hypothesis `∇f(x*) = 0` is missing (`f x = x + x²` at `0`), and the
  conclusion is a strict local minimum (`property_7_4_sufficient`).
* (7.31) is printed with an outer `0 ≥ v_M(x^{(k+1)})`; the Armijo condition is the inner
  inequality, and the outer sign is what it implies (`equation_7_31`).
* Property 7.5's restriction `σ ∈ (0, 1/2)` is nowhere needed (the backbone proves it for
  `0 < σ < β < 1`); it is carried for fidelity. Likewise Property 7.7 holds for `0 < σ` and
  `β < 1`.
* (7.38) is stated over `ℝ`, where `|dᵀr|² = (dᵀr)²`; the backbone's identity is over `RCLike`.
* Property 7.8 as printed ("a convergent sequence … any limit is a critical point … then
  `∇f(x_k) → 0`") is the continuity of `∇f`; the intended statement is the compactness one
  (bounded sequence, every cluster point critical), which is `property_7_8`; the literal reading
  is `property_7_8_of_tendsto`.
* The symmetrization iteration (7.45) converges to (7.46) from a *symmetric* `B_k` only, and the
  bounded deterioration of `B_SPB` needs `B_k` symmetric; both are implicit in the text.
-/

open Filter Matrix Metric Set Topology WithLp
open scoped InnerProductSpace

namespace QuarteroniSaccoSaleri.Chapter07

variable {n : ℕ}

/-! ### Gradients, the Hessian matrix, and Property 7.4 -/

section Hessian

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- TODO(backbone): natural home `Mathlib/Analysis/Calculus/Gradient/Basic`, beside
-- `toDual_gradient`; it is the form in which the backbone's derivative data
-- `f' x = innerSL ℝ (g x)` (`Numlib/Optimization/Descent`) is met by Mathlib's gradient.
/-- The Fréchet derivative is the inner product with the gradient, as a continuous linear map:
`fderiv ℝ f x = innerSL ℝ (∇f(x))`, so that `fderiv ℝ f x d = ⟪∇f(x), d⟫`. No differentiability
is needed, both sides being junk-valued together. -/
theorem fderiv_eq_innerSL_gradient (f : H → ℝ) (x : H) :
    fderiv ℝ f x = innerSL ℝ (gradient f x) := by
  ext d
  rw [innerSL_apply_apply, inner_gradient_left]

/-- The gradient map is `(toDual ℝ H).symm ∘ fderiv ℝ f`. -/
theorem gradient_eq_toDual_symm_fderiv (f : H → ℝ) :
    gradient f = fun x => (InnerProductSpace.toDual ℝ H).symm (fderiv ℝ f x) :=
  rfl

end Hessian

/-- **The Hessian matrix** `H(x)` of `f : ℝⁿ → ℝ` at `x`, with entries
`h_{ij}(x) = ∂²f/∂xᵢ∂xⱼ (x)`: the derivative in the direction `eᵢ` of the partial derivative
`y ↦ ∂f/∂xⱼ (y) = fderiv ℝ f y (eⱼ)`. For a `C²` function it is the matrix of the second Fréchet
derivative (`hessianMatrix_apply`), it is symmetric (`hessianMatrix_isSymm`), and it is the
derivative of the gradient map (`hasFDerivAt_gradient`). -/
noncomputable def hessianMatrix (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)

section HessianMatrix

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}

/-- The entries of the Hessian matrix are the values of the second Fréchet derivative on the
standard basis, `h_{ij}(x) = f''(x)(eᵢ)(eⱼ)`, whenever `fderiv ℝ f` is differentiable at `x`. -/
theorem hessianMatrix_apply (hf : DifferentiableAt ℝ (fderiv ℝ f) x) (i j : Fin n) :
    hessianMatrix f x i j
      = fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  rw [hessianMatrix, Matrix.of_apply, fderiv_clm_apply hf (differentiableAt_const _)]
  simp

/-- The coordinates of `H(x) v`: `(H(x) v)ᵢ = f''(x)(eᵢ)(v)`. -/
theorem toEuclideanLin_hessianMatrix_apply (hf : DifferentiableAt ℝ (fderiv ℝ f) x)
    (v : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    toEuclideanLin (hessianMatrix f x) v i
      = fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1) v := by
  have hv : ∑ i, v i • EuclideanSpace.single i 1 = v := by
    conv_rhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v]
    simp [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  have h1 : fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1) v
      = fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1)
        (∑ j, v j • EuclideanSpace.single j 1) := by rw [hv]
  rw [h1, map_sum, toEuclideanLin_apply]
  simp only [Matrix.mulVec, dotProduct, map_smul, smul_eq_mul, hessianMatrix_apply hf]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- The quadratic form of the Hessian matrix is the second derivative along a direction:
`vᵀ H(x) v = f''(x)(v)(v)`. -/
theorem inner_toEuclideanLin_hessianMatrix (hf : DifferentiableAt ℝ (fderiv ℝ f) x)
    (v : EuclideanSpace ℝ (Fin n)) :
    ⟪toEuclideanLin (hessianMatrix f x) v, v⟫_ℝ = fderiv ℝ (fderiv ℝ f) x v v := by
  set f'' := fderiv ℝ (fderiv ℝ f) x with hf''
  have hv : ∑ i, v i • EuclideanSpace.single i 1 = v := by
    conv_rhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v]
    simp [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  have hcoord : ∀ i, toEuclideanLin (hessianMatrix f x) v i
      = f'' (EuclideanSpace.single i 1) v := toEuclideanLin_hessianMatrix_apply hf v
  have hvv : f'' v v = f'' (∑ i, v i • EuclideanSpace.single i 1) v := by rw [hv]
  calc ⟪toEuclideanLin (hessianMatrix f x) v, v⟫_ℝ
      = ∑ i, toEuclideanLin (hessianMatrix f x) v i * v i := by
        rw [real_inner_comm, EuclideanSpace.inner_eq_star_dotProduct]
        simp [dotProduct]
    _ = ∑ i, v i * f'' (EuclideanSpace.single i 1) v := by
        simp only [hcoord, mul_comm]
    _ = f'' v v := by
        rw [hvv, map_sum, _root_.sum_apply]
        simp only [map_smul, _root_.smul_apply, smul_eq_mul]

/-- The Hessian matrix of a `C²` function is symmetric (Schwarz's theorem,
`ContDiffAt.isSymmSndFDerivAt`). -/
theorem hessianMatrix_isSymm (hf : ContDiffAt ℝ 2 f x) : (hessianMatrix f x).IsSymm := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero
  have hsymm := hf.isSymmSndFDerivAt (by simp)
  refine IsSymm.ext fun i j => ?_
  rw [hessianMatrix_apply hd, hessianMatrix_apply hd, hsymm]

/-- The Hessian matrix of a `C²` function is the derivative of its gradient map:
`HasFDerivAt (∇f) (H(x)) x`, with `H(x)` acting on `ℝⁿ` through `toEuclideanCLM`. -/
theorem hasFDerivAt_gradient (hf : ContDiffAt ℝ 2 f x) :
    HasFDerivAt (gradient f) (toEuclideanCLM (𝕜 := ℝ) (hessianMatrix f x)) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero
  have hsymm := hf.isSymmSndFDerivAt (by simp)
  rw [gradient_eq_toDual_symm_fderiv]
  have h := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.hasFDerivAt.comp x
    hd.hasFDerivAt
  refine h.congr_fderiv ?_
  ext v i
  have hR : toEuclideanCLM (𝕜 := ℝ) (hessianMatrix f x) v i
      = fderiv ℝ (fderiv ℝ f) x v (EuclideanSpace.single i 1) := by
    rw [← hsymm]
    exact toEuclideanLin_hessianMatrix_apply hd v i
  have hL : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
      (fderiv ℝ (fderiv ℝ f) x v) i = fderiv ℝ (fderiv ℝ f) x v (EuclideanSpace.single i 1) := by
    rw [← InnerProductSpace.toDual_symm_apply, EuclideanSpace.inner_single_right]
    simp
  rw [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearEquiv.coe_coe]
  exact hL.trans hR.symm

end HessianMatrix

section Property74

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {xstar : EuclideanSpace ℝ (Fin n)}

/-- **Property 7.4 (a).** If `x*` is a local minimizer of `f` and `f` is differentiable at `x*`
(the book: `f ∈ C¹(B(x*; R))`), then `∇f(x*) = 0`. Mathlib's `IsLocalMin.hasFDerivAt_eq_zero`. -/
theorem property_7_4_gradient (hmin : IsLocalMin f xstar) (hf : DifferentiableAt ℝ f xstar) :
    gradient f xstar = 0 := by
  have h := hmin.hasFDerivAt_eq_zero (hasGradientAt_iff_hasFDerivAt.1 hf.hasGradientAt)
  rw [map_eq_zero_iff _ (InnerProductSpace.toDual ℝ _).injective] at h
  exact h

/-- **Property 7.4 (b).** If `x*` is a local minimizer of `f` and `f` is `C²` at `x*` (the book:
`f ∈ C²(B(x*; R))`), then the Hessian matrix `H(x*)` is positive semidefinite.
`Descent.nonneg_apply_apply_of_isLocalMin` gives `0 ≤ f''(x*)(v)(v) = vᵀ H(x*) v` for every `v`, and
Schwarz's theorem the symmetry. -/
theorem property_7_4_hessian (hmin : IsLocalMin f xstar) (hf : ContDiffAt ℝ 2 f xstar) :
    (hessianMatrix f xstar).PosSemidef := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) xstar :=
    (hf.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero
  have hev : ∀ᶠ y in 𝓝 xstar, HasFDerivAt f (fderiv ℝ f y) y := by
    filter_upwards [hf.eventually (by simp)] with y hy
    exact (hy.differentiableAt (by simp)).hasFDerivAt
  refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨isHermitian_iff_isSymm.2
    (hessianMatrix_isSymm hf), fun v => ?_⟩
  have h := Descent.nonneg_apply_apply_of_isLocalMin hmin hev hd.hasFDerivAt (toLp 2 v)
  rw [← inner_toEuclideanLin_hessianMatrix hd, toEuclideanLin_toLp,
    EuclideanSpace.inner_toLp_toLp, star_trivial] at h
  rw [star_trivial]
  exact h

/-- **Property 7.4 (c), corrected.** If `f` is `C²` at `x*`, `∇f(x*) = 0` and the Hessian matrix
`H(x*)` is positive definite, then `x*` is a strict local minimizer of `f`:
`f(x*) < f(y)` for all `y ≠ x*` in a ball around `x*`. The book omits `∇f(x*) = 0`, without
which the statement is false (`f x = x + x²` at `0`). `Descent.isLocalMin_of_coercive_second`
with the coercivity of the Hessian form from `Matrix.posDef_iff_isSymmetricCoercive`. -/
theorem property_7_4_sufficient (hf : ContDiffAt ℝ 2 f xstar) (hcrit : gradient f xstar = 0)
    (hH : (hessianMatrix f xstar).PosDef) :
    ∃ δ > 0, ∀ y ∈ ball xstar δ, y ≠ xstar → f xstar < f y := by
  -- the differentiability data on a ball, from `C²` at `x*`
  have h2 : ∀ᶠ y in 𝓝 xstar, ContDiffAt ℝ 2 f y := hf.eventually (by simp)
  have h1 : ∀ᶠ y in 𝓝 xstar, ContDiffAt ℝ 1 (fderiv ℝ f) y :=
    (hf.fderiv_right (m := 1) le_rfl).eventually (by simp)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 (h2.and h1)
  have hcont : ContinuousAt (fderiv ℝ (fderiv ℝ f)) xstar :=
    ((hf.fderiv_right (m := 1) le_rfl).fderiv_right (m := 0) le_rfl).continuousAt
  -- coercivity of the Hessian form
  obtain ⟨c, hc, hcoer⟩ := ((Matrix.posDef_iff_isSymmetricCoercive _).1 hH).isCoercive
  have hd : DifferentiableAt ℝ (fderiv ℝ f) xstar :=
    (hf.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero
  refine Descent.isLocalMin_of_coercive_second (f' := fderiv ℝ f) (f'' := fderiv ℝ (fderiv ℝ f))
    hr hc (fun y hy => ((hball hy).1.differentiableAt (by simp)).hasFDerivAt)
    (fun y hy => ((hball hy).2.differentiableAt one_ne_zero).hasFDerivAt) hcont ?_ fun v => ?_
  · rw [fderiv_eq_innerSL_gradient, hcrit, map_zero]
  · have := hcoer v
    rwa [inner_toEuclideanLin_hessianMatrix hd, RCLike.re_to_real] at this

/-- **Critical points** (§7.2): `x*` is a critical point of `f` when `∇f(x*) = 0`. By Property
7.4 (a) this is necessary for a local minimum; it is sufficient when `f` is convex
(`isMinOn_of_convexOn_of_isCriticalPoint`). -/
def IsCriticalPoint (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  gradient f x = 0

/-- **The remark after Property 7.4**: for `f` convex on `ℝⁿ` (7.21) and differentiable, a
critical point is a global minimizer. Property 7.9 (2) with `Ω = ℝⁿ`,
`isMinOn_iff_forall_lineDeriv_nonneg`. -/
theorem isMinOn_of_convexOn_of_isCriticalPoint (hconv : ConvexOn ℝ univ f)
    (hf : ∀ y, DifferentiableAt ℝ f y) {x : EuclideanSpace ℝ (Fin n)} (hx : IsCriticalPoint f x) :
    IsMinOn f univ x := by
  refine (isMinOn_iff_forall_lineDeriv_nonneg (f' := fderiv ℝ f) hconv
    (fun u _ h => (hf u).hasFDerivAt.hasLineDerivAt h) (mem_univ x)).2 fun v _ => ?_
  rw [fderiv_eq_innerSL_gradient, hx, map_zero]
  rfl

end Property74

/-! ### Example 7.5: the Rosenbrock function -/

/-- The Rosenbrock function (7.24), `f(x) = 100 (x₂ - x₁²)² + (1 - x₁)²`. -/
noncomputable def rosenbrock (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  100 * (x 1 - x 0 ^ 2) ^ 2 + (1 - x 0) ^ 2

/-- **Example 7.5, the one statement in it** (the rest is a numerical comparison): the Rosenbrock
function has the global minimizer `(1, 1)`, where it vanishes, and no other. -/
theorem example_7_5 :
    IsMinOn rosenbrock univ !₂[1, 1] ∧ rosenbrock !₂[1, 1] = 0 ∧
      ∀ y, IsMinOn rosenbrock univ y → y = !₂[1, 1] := by
  have h0 : rosenbrock !₂[1, 1] = 0 := by simp [rosenbrock]
  have hnn : ∀ y, 0 ≤ rosenbrock y := fun y => by unfold rosenbrock; positivity
  refine ⟨isMinOn_iff.2 fun y _ => by rw [h0]; exact hnn y, h0, fun y hy => ?_⟩
  have hy0 : rosenbrock y = 0 :=
    le_antisymm (by simpa [h0] using isMinOn_iff.1 hy _ (mem_univ !₂[1, 1])) (hnn y)
  have h1 : y 0 = 1 := by
    unfold rosenbrock at hy0
    nlinarith [sq_nonneg (y 1 - y 0 ^ 2), sq_nonneg (1 - y 0)]
  have h2 : y 1 = 1 := by
    unfold rosenbrock at hy0
    rw [h1] at hy0
    nlinarith [sq_nonneg (y 1 - 1)]
  ext i
  fin_cases i <;> simp [h1, h2]

/-! ### Descent methods, Theorem 7.3, and the line search conditions -/

section Descent

variable {f : EuclideanSpace ℝ (Fin n) → ℝ}

/-- **(7.27)–(7.28).** If `d` is a descent direction at `x` in the sense of (7.26),
`dᵀ ∇f(x) < 0`, and `f` is differentiable at `x`, then `f(x + α d) < f(x)` for every small enough
positive step `α`. `Descent.exists_forall_lt_of_isDescentDirection`. -/
theorem equation_7_27 {x d : EuclideanSpace ℝ (Fin n)} (hf : DifferentiableAt ℝ f x)
    (hd : ⟪gradient f x, d⟫_ℝ < 0) : ∃ ε > 0, ∀ α ∈ Ioo (0 : ℝ) ε, f (x + α • d) < f x :=
  Descent.exists_forall_lt_of_isDescentDirection (f' := fderiv ℝ f) hf.hasFDerivAt
    (by rw [Descent.IsDescentDirection, fderiv_eq_innerSL_gradient, innerSL_apply_apply]; exact hd)

/-- **The directions of §7.2.2.** The steepest-descent direction `d = -∇f(x)` is a descent
direction when `∇f(x) ≠ 0`, with `dᵀ ∇f(x) = -‖∇f(x)‖₂²`; and the Newton and inexact-Newton
directions `d = -B⁻¹ ∇f(x)` are descent directions for every symmetric positive definite `B`
(the Hessian `H(x)`, or an approximation `B_k` of it). `Descent.isDescentDirection_neg_gradient`,
`Descent.isDescentDirection_neg_inverse_of_isCoercive`. -/
theorem steepestDescent_isDescentDirection {x : EuclideanSpace ℝ (Fin n)}
    (hx : gradient f x ≠ 0) :
    Descent.IsDescentDirection (fderiv ℝ f) x (-gradient f x) ∧
      ⟪gradient f x, -gradient f x⟫_ℝ = -‖gradient f x‖ ^ 2 ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosDef →
        Descent.IsDescentDirection (fderiv ℝ f) x
          (-(toEuclideanCLM (𝕜 := ℝ) B⁻¹ (gradient f x))) := by
  have hg : fderiv ℝ f x = innerSL ℝ (gradient f x) := fderiv_eq_innerSL_gradient f x
  refine ⟨Descent.isDescentDirection_neg_gradient hg hx, ?_, fun B hB => ?_⟩
  · rw [inner_neg_right, real_inner_self_eq_norm_sq]
  · have hu : IsUnit B := hB.isUnit
    let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
      ContinuousLinearEquiv.equivOfInverse (toEuclideanCLM (𝕜 := ℝ) B)
        (toEuclideanCLM (𝕜 := ℝ) B⁻¹)
        (fun v => by
          change toEuclideanLin B⁻¹ (toEuclideanLin B v) = v
          exact toEuclideanLin_nonsing_inv_mul_apply hu v)
        (fun v => by
          change toEuclideanLin B (toEuclideanLin B⁻¹ v) = v
          exact toEuclideanLin_mul_nonsing_inv_apply hu v)
    have hcoer : ((e : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsCoercive := by
      have := ((Matrix.posDef_iff_isSymmetricCoercive B).1 hB).isCoercive
      exact this
    exact Descent.isDescentDirection_neg_inverse_of_isCoercive hg hx e hcoer

/-- **Theorem 7.3.** In the descent method (7.25), if at step `k` the parameter `α_k` is a (local)
solution of the one-dimensional problem (7.29), `minimize φ(α) = f(x^{(k)} + α d^{(k)})`, and `f`
is differentiable at `x^{(k+1)}`, then `∇f(x^{(k+1)})ᵀ d^{(k)} = 0`.
`Descent.fderiv_apply_eq_zero_of_isLocalMin_line`. -/
theorem theorem_7_3 {x d : ℕ → EuclideanSpace ℝ (Fin n)} {α : ℕ → ℝ}
    (hseq : Descent.IsDescentSequence (fderiv ℝ f) x d α) (k : ℕ)
    (hf : DifferentiableAt ℝ f (x (k + 1)))
    (hα : IsLocalMin (fun t : ℝ => f (x k + t • d k)) (α k)) :
    ⟪gradient f (x (k + 1)), d k⟫_ℝ = 0 := by
  rw [← innerSL_apply_apply, ← fderiv_eq_innerSL_gradient, hseq.step k]
  rw [hseq.step k] at hf
  exact Descent.fderiv_apply_eq_zero_of_isLocalMin_line hf.hasFDerivAt hα

variable {x d : EuclideanSpace ℝ (Fin n)} {σ β α : ℝ}

/-- **(7.31), the Armijo condition in the book's form.** For `α > 0`, the backbone's
`LineSearch.Armijo f (fderiv ℝ f) σ x d α` says that the average descent rate
`v_M(x^{(k+1)}) = (f(x) - f(x + α d)) / α` is at least the fraction `σ` of the initial rate
`-∇f(x)ᵀ d`. The outer `0 ≥ v_M` printed in (7.31) is a consequence (for a descent direction),
not part of the condition. -/
theorem equation_7_31 (hα : 0 < α) :
    LineSearch.Armijo f (fderiv ℝ f) σ x d α ↔
      -σ * ⟪gradient f x, d⟫_ℝ ≤ (f x - f (x + α • d)) / α := by
  rw [LineSearch.Armijo, fderiv_eq_innerSL_gradient, innerSL_apply_apply, le_div_iff₀ hα]
  constructor <;> intro h <;> linarith

/-- **(7.32)–(7.33), the curvature conditions.** The strong Wolfe condition (7.32) is
`|∇f(x + α d)ᵀ d| ≤ β |∇f(x)ᵀ d|`, the weak one (7.33) is `∇f(x + α d)ᵀ d ≥ β ∇f(x)ᵀ d`, and the
strong condition implies the weak one along a descent direction. `LineSearch.StrongWolfeCurvature`,
`LineSearch.WolfeCurvature`. -/
theorem equation_7_32 :
    (LineSearch.StrongWolfeCurvature (fderiv ℝ f) β x d α ↔
        |⟪gradient f (x + α • d), d⟫_ℝ| ≤ β * |⟪gradient f x, d⟫_ℝ|) ∧
      (LineSearch.WolfeCurvature (fderiv ℝ f) β x d α ↔
        β * ⟪gradient f x, d⟫_ℝ ≤ ⟪gradient f (x + α • d), d⟫_ℝ) ∧
      (⟪gradient f x, d⟫_ℝ < 0 → LineSearch.StrongWolfeCurvature (fderiv ℝ f) β x d α →
        LineSearch.WolfeCurvature (fderiv ℝ f) β x d α) := by
  refine ⟨?_, ?_, fun hd h => h.wolfeCurvature ?_⟩
  · rw [LineSearch.StrongWolfeCurvature, fderiv_eq_innerSL_gradient, fderiv_eq_innerSL_gradient,
      innerSL_apply_apply, innerSL_apply_apply]
  · rw [LineSearch.WolfeCurvature, fderiv_eq_innerSL_gradient, fderiv_eq_innerSL_gradient,
      innerSL_apply_apply, innerSL_apply_apply]
  · rw [Descent.IsDescentDirection, fderiv_eq_innerSL_gradient, innerSL_apply_apply]
    exact hd

/-- **(7.34), the Goldstein conditions, and the Armijo rule.** For a descent direction and
`α > 0`, `LineSearch.Goldstein f (fderiv ℝ f) σ x d α` is
`σ ≤ (f(x + α d) - f(x)) / (α ∇f(x)ᵀ d) ≤ 1 - σ`; and the Armijo rule `α_k = β^{m_k} ᾱ`, with
`m_k` the first nonnegative integer such that (7.31) holds, is well defined: for `f`
differentiable at `x`, `σ < 1`, `β ∈ (0, 1)` and `ᾱ > 0`, some `m` satisfies (7.31)
(`LineSearch.eventually_armijo_of_isDescentDirection`). -/
theorem equation_7_34 (hd : ⟪gradient f x, d⟫_ℝ < 0) (hα : 0 < α) :
    (LineSearch.Goldstein f (fderiv ℝ f) σ x d α ↔
      σ ≤ (f (x + α • d) - f x) / (α * ⟪gradient f x, d⟫_ℝ) ∧
        (f (x + α • d) - f x) / (α * ⟪gradient f x, d⟫_ℝ) ≤ 1 - σ) ∧
      (DifferentiableAt ℝ f x → σ < 1 → 0 < β → β < 1 → ∀ a : ℝ, 0 < a →
        ∃ m : ℕ, LineSearch.Armijo f (fderiv ℝ f) σ x d (β ^ m * a)) := by
  have hneg : α * ⟪gradient f x, d⟫_ℝ < 0 := mul_neg_of_pos_of_neg hα hd
  refine ⟨?_, fun hf hσ hβ0 hβ1 a ha => ?_⟩
  · rw [LineSearch.Goldstein, fderiv_eq_innerSL_gradient, innerSL_apply_apply,
      le_div_iff_of_neg hneg, div_le_iff_of_neg hneg]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  · have hdesc : Descent.IsDescentDirection (fderiv ℝ f) x d := by
      rw [Descent.IsDescentDirection, fderiv_eq_innerSL_gradient, innerSL_apply_apply]
      exact hd
    have ht : Tendsto (fun m : ℕ => β ^ m * a) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun m => ?_⟩
      · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const a
      · exact mul_pos (pow_pos hβ0 m) ha
    exact (ht.eventually (LineSearch.eventually_armijo_of_isDescentDirection hf.hasFDerivAt
      hdesc hσ)).exists

-- The book restricts `σ ∈ (0, 1/2)`; the backbone proves the statement for every `0 < σ < β < 1`
-- (`LineSearch.exists_Icc_armijo_wolfe`), so `hσ2` is carried for fidelity only.
set_option linter.unusedVariables false in
/-- **Property 7.5.** Let `f ∈ C¹(ℝⁿ)` be bounded below, `f(x) ≥ M` for all `x`. Then at every
step of a descent method (a descent direction `d` at `x`), for `σ ∈ (0, 1/2)` and `β ∈ (σ, 1)`,
there is an interval `I = [c, C]` with `0 < c < C` such that every `α ∈ I` satisfies (7.31) and
(7.32) — hence also (7.31) and (7.33). `LineSearch.exists_Icc_armijo_wolfe`. -/
theorem property_7_5 (hf : ContDiff ℝ 1 f) {M : ℝ} (hM : ∀ y, M ≤ f y)
    (hd : ⟪gradient f x, d⟫_ℝ < 0) (hσ : 0 < σ) (hσ2 : σ < 1 / 2) (hσβ : σ < β) (hβ : β < 1) :
    ∃ c C : ℝ, 0 < c ∧ c < C ∧ ∀ α ∈ Icc c C,
      LineSearch.Armijo f (fderiv ℝ f) σ x d α ∧
        LineSearch.StrongWolfeCurvature (fderiv ℝ f) β x d α ∧
        LineSearch.WolfeCurvature (fderiv ℝ f) β x d α := by
  have hdesc : Descent.IsDescentDirection (fderiv ℝ f) x d := by
    rw [Descent.IsDescentDirection, fderiv_eq_innerSL_gradient, innerSL_apply_apply]
    exact hd
  obtain ⟨c, C, hc, hcC, h⟩ := LineSearch.exists_Icc_armijo_wolfe
    (fun y => (hf.differentiable one_ne_zero y).hasFDerivAt) (hf.continuous_fderiv one_ne_zero)
    (fun t => hM (x + t • d)) hdesc hσ hσβ hβ
  exact ⟨c, C, hc, hcC, fun α hα => ⟨(h α hα).1, (h α hα).2.2, (h α hα).2.1⟩⟩

end Descent

/-! ### The quadratic case: (7.35)–(7.39), Lemma 7.1 and Property 7.6 -/

section Quadratic

variable {A : Matrix (Fin n) (Fin n) ℝ} {b : EuclideanSpace ℝ (Fin n)}

/-- The symmetric bounded operator of a real symmetric matrix, as `hasGradientAt_energyFunctional`
wants it. -/
private theorem isSymmetric_toEuclideanCLM (hA : A.IsSymm) :
    ((toEuclideanCLM (𝕜 := ℝ) A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric := by
  rw [coe_toEuclideanCLM_eq_toEuclideanLin]
  exact hA.isSymmetric_toEuclideanLin

/-- **(7.35) and the display after it.** For a symmetric `A` and `b ∈ ℝⁿ`, the quadratic
`f(x) = ½ xᵀ A x - bᵀ x` is the backbone's `energyFunctional (toEuclideanLin A) b`; its gradient
is `∇f(x) = A x - b = -r`, the negative residual, and its Hessian matrix is `H(x) = A` at every
`x`. `hasGradientAt_energyFunctional`. -/
theorem equation_7_35 (hA : A.IsSymm) (x : EuclideanSpace ℝ (Fin n)) :
    energyFunctional (toEuclideanLin A) b x
        = (ofLp x ⬝ᵥ (A *ᵥ ofLp x)) / 2 - ofLp b ⬝ᵥ ofLp x ∧
      gradient (energyFunctional (toEuclideanLin A) b) x = toEuclideanLin A x - b ∧
      hessianMatrix (energyFunctional (toEuclideanLin A) b) x = A := by
  have hA' := isSymmetric_toEuclideanCLM hA
  have hgrad : ∀ y, HasFDerivAt (energyFunctional (toEuclideanLin A) b)
      (innerSL ℝ (toEuclideanCLM (𝕜 := ℝ) A y - b)) y := fun y => by
    have := hasFDerivAt_energyFunctional (A := toEuclideanCLM (𝕜 := ℝ) A) hA' b y
    rwa [coe_toEuclideanCLM_eq_toEuclideanLin] at this
  refine ⟨?_, ?_, ?_⟩
  · simp only [energyFunctional, RCLike.re_to_real, EuclideanSpace.inner_eq_star_dotProduct,
      star_trivial, ofLp_toEuclideanLin]
    rw [dotProduct_comm (ofLp x) (ofLp b)]
  · have := hasGradientAt_energyFunctional (A := toEuclideanCLM (𝕜 := ℝ) A) hA' b x
    rw [coe_toEuclideanCLM_eq_toEuclideanLin] at this
    exact this.gradient
  · have hfd : fderiv ℝ (energyFunctional (toEuclideanLin A) b)
        = fun y => innerSL ℝ (toEuclideanCLM (𝕜 := ℝ) A y - b) := funext fun y => (hgrad y).fderiv
    ext i j
    rw [hessianMatrix, Matrix.of_apply]
    have hfun : (fun y => fderiv ℝ (energyFunctional (toEuclideanLin A) b) y
          (EuclideanSpace.single j 1))
        = fun y => ⟪EuclideanSpace.single j 1, toEuclideanCLM (𝕜 := ℝ) A y⟫_ℝ
          - ⟪EuclideanSpace.single j 1, b⟫_ℝ := by
      funext y
      rw [hfd, innerSL_apply_apply, inner_sub_left, real_inner_comm, real_inner_comm b]
    have hder : HasFDerivAt (fun y => ⟪EuclideanSpace.single j 1, toEuclideanCLM (𝕜 := ℝ) A y⟫_ℝ
          - ⟪EuclideanSpace.single j 1, b⟫_ℝ)
        ((innerSL ℝ (EuclideanSpace.single j 1)).comp (toEuclideanCLM (𝕜 := ℝ) A)) x :=
      ((innerSL ℝ (EuclideanSpace.single j 1)).comp
        (toEuclideanCLM (𝕜 := ℝ) A)).hasFDerivAt.sub_const _
    rw [hfun, hder.fderiv, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      EuclideanSpace.inner_single_left, ofLp_toEuclideanCLM]
    simp [hA.apply i j]

/-- **(7.36).** For the quadratic (7.35) with `A` symmetric positive definite and a direction
`d ≠ 0`, the exact line search `minimize α ↦ f(x + α d)` has the unique solution
`α = dᵀ r / dᵀ A d`, `r = b - A x`; the resulting point `x + α d` is the backbone's
`Projection.step1 (toEuclideanLin A) b d d x`. Minimality is `Projection.step1_isGalerkin` with
`IsGalerkin.quadratic_le`; uniqueness comes from the exact expansion
`f(x + t d) = f(x + α d) + ½ (t - α)² dᵀ A d` (`LinearMap.IsSymmetric.energyFunctional_add`). -/
theorem equation_7_36 (hA : A.PosDef) (x : EuclideanSpace ℝ (Fin n))
    {d : EuclideanSpace ℝ (Fin n)} (hd : d ≠ 0) :
    Projection.step1 (toEuclideanLin A) b d d x
        = x + (⟪d, b - toEuclideanLin A x⟫_ℝ / ⟪d, toEuclideanLin A d⟫_ℝ) • d ∧
      IsMinOn (fun t : ℝ => energyFunctional (toEuclideanLin A) b (x + t • d)) univ
        (⟪d, b - toEuclideanLin A x⟫_ℝ / ⟪d, toEuclideanLin A d⟫_ℝ) ∧
      ∀ t : ℝ, IsMinOn (fun t : ℝ => energyFunctional (toEuclideanLin A) b (x + t • d)) univ t →
        t = ⟪d, b - toEuclideanLin A x⟫_ℝ / ⟪d, toEuclideanLin A d⟫_ℝ := by
  have hAsc := (Matrix.posDef_iff_isSymmetricCoercive A).1 hA
  set α : ℝ := ⟪d, b - toEuclideanLin A x⟫_ℝ / ⟪d, toEuclideanLin A d⟫_ℝ with hα
  set φ : ℝ → ℝ := fun t => energyFunctional (toEuclideanLin A) b (x + t • d) with hφ
  have hstep : Projection.step1 (toEuclideanLin A) b d d x = x + α • d := rfl
  -- the exact expansion along the line
  have hq : 0 < ⟪toEuclideanLin A d, d⟫_ℝ := by
    simpa using hAsc.isCoercive.inner_self_pos hd
  have hqs : ⟪d, toEuclideanLin A d⟫_ℝ = ⟪toEuclideanLin A d, d⟫_ℝ := real_inner_comm _ _
  have hexp : ∀ t, φ t = φ α + ⟪toEuclideanLin A d, d⟫_ℝ / 2 * (t - α) ^ 2 := by
    intro t
    have h1 := hAsc.isSymmetric.energyFunctional_add b x (t • d)
    have h2 := hAsc.isSymmetric.energyFunctional_add b x (α • d)
    simp only [hφ, RCLike.re_to_real, inner_smul_right, inner_smul_left, map_smul,
      RCLike.conj_to_real] at h1 h2 ⊢
    rw [h1, h2]
    have hα' : α * ⟪toEuclideanLin A d, d⟫_ℝ = ⟪d, b - toEuclideanLin A x⟫_ℝ := by
      rw [hα, hqs, div_mul_cancel₀ _ hq.ne']
    have hr : ⟪toEuclideanLin A x - b, d⟫_ℝ = -⟪d, b - toEuclideanLin A x⟫_ℝ := by
      rw [real_inner_comm, ← inner_neg_right, neg_sub]
    rw [hr]
    linear_combination (t - α) * hα'
  refine ⟨hstep, isMinOn_iff.2 fun t _ => ?_, fun t ht => ?_⟩
  · have hgal := Projection.step1_isGalerkin (b := b) hAsc.isCoercive d x
    have := IsGalerkin.quadratic_le hAsc hgal (y := x + t • d)
      (by
        rw [add_sub_cancel_left]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self d))
    rw [hstep] at this
    exact this
  · have h1 := isMinOn_iff.1 ht α (mem_univ α)
    have h2 := hexp t
    have h3 : (t - α) ^ 2 = 0 := by
      have hnn : 0 ≤ ⟪toEuclideanLin A d, d⟫_ℝ / 2 * (t - α) ^ 2 := by positivity
      have : ⟪toEuclideanLin A d, d⟫_ℝ / 2 * (t - α) ^ 2 ≤ 0 := by
        change φ t ≤ φ α at h1
        linarith
      have hz : ⟪toEuclideanLin A d, d⟫_ℝ / 2 * (t - α) ^ 2 = 0 := le_antisymm this hnn
      rcases mul_eq_zero.1 hz with h | h
      · exact absurd h (by positivity)
      · exact h
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h3)

/-- **(7.37)–(7.38).** With the step (7.36) along `d`, the energy-norm error satisfies
`‖x^{(k+1)} - x*‖_A² = ρ_k ‖x^{(k)} - x*‖_A²` with `ρ_k = 1 - σ_k`,
`σ_k = (dᵀ r)² / ((dᵀ A d)(rᵀ A⁻¹ r))`, where `rᵀ A⁻¹ r = ‖x^{(k)} - x*‖_A²`; and for `d ≠ 0`,
`x ≠ x*`, `ρ_k < 1` unless `d ⟂ r`, in which case `ρ_k = 1`. Stated over `ℝ`, where the
backbone's `|dᵀr|²` is `(dᵀr)²`; `Projection.energyNorm_step1_sq_eq_mul`. -/
theorem equation_7_38 (hA : A.PosDef) {xstar : EuclideanSpace ℝ (Fin n)}
    (hstar : toEuclideanLin A xstar = b) (x d : EuclideanSpace ℝ (Fin n)) :
    energyNorm (toEuclideanLin A) (xstar - Projection.step1 (toEuclideanLin A) b d d x) ^ 2
        = (1 - ⟪d, b - toEuclideanLin A x⟫_ℝ ^ 2 / (⟪d, toEuclideanLin A d⟫_ℝ *
            ⟪b - toEuclideanLin A x, toEuclideanLin A⁻¹ (b - toEuclideanLin A x)⟫_ℝ))
          * energyNorm (toEuclideanLin A) (xstar - x) ^ 2 ∧
      ⟪b - toEuclideanLin A x, toEuclideanLin A⁻¹ (b - toEuclideanLin A x)⟫_ℝ
        = energyNorm (toEuclideanLin A) (xstar - x) ^ 2 ∧
      (d ≠ 0 → x ≠ xstar →
        (⟪d, b - toEuclideanLin A x⟫_ℝ ≠ 0 →
          1 - ⟪d, b - toEuclideanLin A x⟫_ℝ ^ 2 / (⟪d, toEuclideanLin A d⟫_ℝ *
            ⟪b - toEuclideanLin A x, toEuclideanLin A⁻¹ (b - toEuclideanLin A x)⟫_ℝ) < 1) ∧
        (⟪d, b - toEuclideanLin A x⟫_ℝ = 0 →
          1 - ⟪d, b - toEuclideanLin A x⟫_ℝ ^ 2 / (⟪d, toEuclideanLin A d⟫_ℝ *
            ⟪b - toEuclideanLin A x, toEuclideanLin A⁻¹ (b - toEuclideanLin A x)⟫_ℝ) = 1)) := by
  have hAsc := (Matrix.posDef_iff_isSymmetricCoercive A).1 hA
  have hu : IsUnit A := hA.isUnit
  have hr : b - toEuclideanLin A x = toEuclideanLin A (xstar - x) := by rw [map_sub, hstar]
  have hres : ⟪b - toEuclideanLin A x, toEuclideanLin A⁻¹ (b - toEuclideanLin A x)⟫_ℝ
      = energyNorm (toEuclideanLin A) (xstar - x) ^ 2 := by
    rw [hr, toEuclideanLin_nonsing_inv_mul_apply hu, hAsc.energyNorm_sq, RCLike.re_to_real]
  refine ⟨?_, hres, fun hd hx => ?_⟩
  · rw [Projection.energyNorm_step1_sq_eq_mul hAsc hstar d x, hres, mul_comm, Real.norm_eq_abs,
      sq_abs, RCLike.re_to_real, real_inner_comm d (toEuclideanLin A d)]
  · have hq : 0 < ⟪d, toEuclideanLin A d⟫_ℝ := by
      rw [real_inner_comm]; simpa using hAsc.isCoercive.inner_self_pos hd
    have he : 0 < energyNorm (toEuclideanLin A) (xstar - x) ^ 2 :=
      pow_pos (hAsc.energyNorm_pos (sub_ne_zero.2 (Ne.symm hx))) 2
    rw [hres]
    refine ⟨fun hdr => ?_, fun hdr => by rw [hdr]; simp⟩
    have : 0 < ⟪d, b - toEuclideanLin A x⟫_ℝ ^ 2 / (⟪d, toEuclideanLin A d⟫_ℝ *
        energyNorm (toEuclideanLin A) (xstar - x) ^ 2) :=
      div_pos (by positivity) (mul_pos hq he)
    linarith

/-- **(7.39).** For the steepest descent method, `d^{(k)} = r^{(k)}`, with the exact step (7.36)
(the backbone's `Projection.steepestDescentStep`),
`‖x^{(k+1)} - x*‖_A ≤ (λmax - λmin)/(λmax + λmin) ‖x^{(k)} - x*‖_A`, with `λmax`, `λmin` the
extreme eigenvalues of the symmetric positive definite `A`.
`Projection.energyNorm_steepestDescentStep_le` with
`Matrix.IsHermitian.isSymmetricBoundedBy_toEuclideanLin`. -/
theorem equation_7_39 (hA : A.PosDef) {lmin lmax : ℝ}
    (hmin : IsLeast (Set.range hA.1.eigenvalues) lmin)
    (hmax : IsGreatest (Set.range hA.1.eigenvalues) lmax) {xstar : EuclideanSpace ℝ (Fin n)}
    (hstar : toEuclideanLin A xstar = b) (x : EuclideanSpace ℝ (Fin n)) :
    Projection.steepestDescentStep (toEuclideanLin A) b x
        = Projection.step1 (toEuclideanLin A) b (b - toEuclideanLin A x)
          (b - toEuclideanLin A x) x ∧
      energyNorm (toEuclideanLin A) (xstar - Projection.steepestDescentStep (toEuclideanLin A) b x)
        ≤ (lmax - lmin) / (lmax + lmin) * energyNorm (toEuclideanLin A) (xstar - x) := by
  obtain ⟨i, hi⟩ := hmin.1
  have hl : 0 < lmin := hi ▸ hA.eigenvalues_pos i
  have hAb : (toEuclideanLin A).IsSymmetricBoundedBy lmin lmax :=
    hA.1.isSymmetricBoundedBy_toEuclideanLin fun j =>
      ⟨hmin.2 (Set.mem_range_self j), hmax.2 (Set.mem_range_self j)⟩
  exact ⟨rfl, Projection.energyNorm_steepestDescentStep_le hl hAb hstar x⟩

/-- **Lemma 7.1 (Kantorovich inequality).** For `A` symmetric positive definite with extreme
eigenvalues `λmax` and `λmin`, and every `y ≠ 0`,
`(yᵀ y)² / ((yᵀ A y)(yᵀ A⁻¹ y)) ≥ 4 λmax λmin / (λmax + λmin)²`. The reciprocal form of the
backbone's `Projection.kantorovich_inequality`. -/
theorem lemma_7_1 (hA : A.PosDef) {lmin lmax : ℝ}
    (hmin : IsLeast (Set.range hA.1.eigenvalues) lmin)
    (hmax : IsGreatest (Set.range hA.1.eigenvalues) lmax) {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ≠ 0) :
    4 * lmax * lmin / (lmax + lmin) ^ 2
      ≤ ⟪y, y⟫_ℝ ^ 2 / (⟪y, toEuclideanLin A y⟫_ℝ * ⟪y, toEuclideanLin A⁻¹ y⟫_ℝ) := by
  obtain ⟨i, hi⟩ := hmin.1
  have hl : 0 < lmin := hi ▸ hA.eigenvalues_pos i
  have hlmax : lmin ≤ lmax := hmax.2 (hi ▸ Set.mem_range_self i)
  have hlmax0 : 0 < lmax := lt_of_lt_of_le hl hlmax
  have hAb : (toEuclideanLin A).IsSymmetricBoundedBy lmin lmax :=
    hA.1.isSymmetricBoundedBy_toEuclideanLin fun j =>
      ⟨hmin.2 (Set.mem_range_self j), hmax.2 (Set.mem_range_self j)⟩
  have hu : IsUnit A := hA.isUnit
  have hk := Projection.kantorovich_inequality hl hAb y (y := toEuclideanLin A⁻¹ y)
    (toEuclideanLin_mul_nonsing_inv_apply hu y)
  simp only [RCLike.re_to_real] at hk
  have hp1 : 0 < ⟪toEuclideanLin A y, y⟫_ℝ := by
    simpa using ((Matrix.posDef_iff_isSymmetricCoercive A).1 hA).isCoercive.inner_self_pos hy
  have hp2 : 0 < ⟪toEuclideanLin A⁻¹ y, y⟫_ℝ := by
    simpa using ((Matrix.posDef_iff_isSymmetricCoercive A⁻¹).1 hA.inv).isCoercive.inner_self_pos hy
  have hpos : 0 < 4 * lmax * lmin := by positivity
  rw [real_inner_comm (toEuclideanLin A y) y, real_inner_comm (toEuclideanLin A⁻¹ y) y,
    real_inner_self_eq_norm_sq, div_le_div_iff₀ (by positivity) (mul_pos hp1 hp2)]
  have hk' : 4 * lmax * lmin * (⟪toEuclideanLin A y, y⟫_ℝ * ⟪toEuclideanLin A⁻¹ y, y⟫_ℝ)
      ≤ (lmax + lmin) ^ 2 * ‖y‖ ^ 4 := by
    have := mul_le_mul_of_nonneg_left hk hpos.le
    have heq : 4 * lmax * lmin * ((lmax + lmin) ^ 2 / (4 * lmax * lmin) * ‖y‖ ^ 4)
        = (lmax + lmin) ^ 2 * ‖y‖ ^ 4 := by field_simp
    linarith
  nlinarith [hk']

/-- **Property 7.6, last clause.** For pairwise `A`-conjugate directions `d^{(0)}, d^{(1)}, …`
(`d^{(k)ᵀ} A d^{(m)} = 0` for `k ≠ m`) and the steps (7.36), the residual is orthogonal to all the
directions used so far: `r^{(k+1)ᵀ} d^{(m)} = 0` for every `m ≤ k`.
`ConjugateDirection.inner_residual_direction_eq_zero`. -/
theorem property_7_6_orthogonal (hA : A.PosDef) (x₀ : EuclideanSpace ℝ (Fin n))
    {d : ℕ → EuclideanSpace ℝ (Fin n)}
    (hd : ConjugateDirection.IsConjugateFamily (toEuclideanLin A) d) {k m : ℕ} (hm : m ≤ k) :
    ⟪b - toEuclideanLin A (ConjugateDirection.iterate (toEuclideanLin A) b d x₀ (k + 1)),
      d m⟫_ℝ = 0 :=
  ConjugateDirection.inner_residual_direction_eq_zero b x₀
    ((Matrix.posDef_iff_isSymmetricCoercive A).1 hA).isCoercive hd k m hm

/-- **Property 7.6, second clause.** With conjugate directions and the steps (7.36), `x^{(k+1)}`
minimizes the quadratic (7.35) over the affine subspace `x^{(0)} + span {d^{(0)}, …, d^{(k)}}`
(the book's "subspace generated by `x^{(0)}, d^{(0)}, …, d^{(k)}`").
`ConjugateDirection.isGalerkin_iterate` with `IsGalerkin.quadratic_le`. -/
theorem property_7_6_isMinOn (hA : A.PosDef) (x₀ : EuclideanSpace ℝ (Fin n))
    {d : ℕ → EuclideanSpace ℝ (Fin n)}
    (hd : ConjugateDirection.IsConjugateFamily (toEuclideanLin A) d) (k : ℕ) :
    IsMinOn (energyFunctional (toEuclideanLin A) b)
      {y | y - x₀ ∈ Submodule.span ℝ (Set.range fun i : Fin (k + 1) => d i)}
      (ConjugateDirection.iterate (toEuclideanLin A) b d x₀ (k + 1)) := by
  have hAsc := (Matrix.posDef_iff_isSymmetricCoercive A).1 hA
  exact isMinOn_iff.2 fun y hy =>
    IsGalerkin.quadratic_le hAsc (ConjugateDirection.isGalerkin_iterate b x₀ hAsc.isCoercive hd
      (k + 1)) hy

/-- **Property 7.6, first clause.** A conjugate direction method with nonzero directions
`d^{(0)}, …, d^{(n-1)}` and the steps (7.36) reaches the minimizer `x*` of the quadratic (7.35),
the solution of `A x* = b`, after at most `n` steps: `x^{(k)} = x*` for every `k ≥ n`.
`ConjugateDirection.iterate_eq_of_finrank_le`. -/
theorem property_7_6_termination (hA : A.PosDef) (x₀ : EuclideanSpace ℝ (Fin n))
    {d : ℕ → EuclideanSpace ℝ (Fin n)}
    (hd : ConjugateDirection.IsConjugateFamily (toEuclideanLin A) d) (h0 : ∀ i < n, d i ≠ 0)
    {xstar : EuclideanSpace ℝ (Fin n)} (hstar : toEuclideanLin A xstar = b) {k : ℕ}
    (hk : n ≤ k) : ConjugateDirection.iterate (toEuclideanLin A) b d x₀ k = xstar :=
  ConjugateDirection.iterate_eq_of_finrank_le b x₀
    ((Matrix.posDef_iff_isSymmetricCoercive A).1 hA).isCoercive hd
    (by rwa [finrank_euclideanSpace_fin]) hstar (by rwa [finrank_euclideanSpace_fin])

/-- **The conjugate gradient method for function minimization** (§7.2.4): with
`d^{(0)} = r^{(0)}`, `d^{(k+1)} = r^{(k+1)} + β_k d^{(k)}`,
`β_k = -r^{(k+1)ᵀ} A d^{(k)} / d^{(k)ᵀ} A d^{(k)} = r^{(k+1)ᵀ} r^{(k+1)} / r^{(k)ᵀ} r^{(k)}` and
`x^{(k+1)} = x^{(k)} + α_k d^{(k)}` with the step (7.36), the iteration is the backbone's
`CG.iterate (toEuclideanLin A) b x₀`: the points are the conjugate-direction iterates along the
CG directions (`CG.iterate_x_eq_conjugateDirection_iterate`), and the two expressions of `β_k`
agree (`CG.beta_iterate`, `CG.inner_residual_eq_zero`). Its error estimate
`‖x^{(k)} - x*‖_A ≤ 2 ((√K₂(A) - 1)/(√K₂(A) + 1))^k ‖x^{(0)} - x*‖_A` is chapter 4's restatement
of `Krylov.IsGalerkinIterate.energyNorm_error_le`. -/
theorem conjugateGradient_eq_CG (hA : A.PosDef) (x₀ : EuclideanSpace ℝ (Fin n)) :
    (∀ k, (CG.iterate (toEuclideanLin A) b x₀ k).x
        = ConjugateDirection.iterate (toEuclideanLin A) b
          (fun k => (CG.iterate (toEuclideanLin A) b x₀ k).p) x₀ k) ∧
      (∀ k, (CG.iterate (toEuclideanLin A) b x₀ k).r
        = b - toEuclideanLin A (CG.iterate (toEuclideanLin A) b x₀ k).x) ∧
      (CG.iterate (toEuclideanLin A) b x₀ 0).p = b - toEuclideanLin A x₀ ∧
      (∀ k, (CG.iterate (toEuclideanLin A) b x₀ (k + 1)).p
        = (CG.iterate (toEuclideanLin A) b x₀ (k + 1)).r
          + CG.beta (toEuclideanLin A) (CG.iterate (toEuclideanLin A) b x₀ k) •
            (CG.iterate (toEuclideanLin A) b x₀ k).p) ∧
      (∀ k, CG.beta (toEuclideanLin A) (CG.iterate (toEuclideanLin A) b x₀ k)
        = ⟪(CG.iterate (toEuclideanLin A) b x₀ (k + 1)).r,
            (CG.iterate (toEuclideanLin A) b x₀ (k + 1)).r⟫_ℝ /
          ⟪(CG.iterate (toEuclideanLin A) b x₀ k).r, (CG.iterate (toEuclideanLin A) b x₀ k).r⟫_ℝ) ∧
      ∀ k, CG.beta (toEuclideanLin A) (CG.iterate (toEuclideanLin A) b x₀ k)
        = -⟪(CG.iterate (toEuclideanLin A) b x₀ (k + 1)).r,
            toEuclideanLin A (CG.iterate (toEuclideanLin A) b x₀ k).p⟫_ℝ /
          ⟪(CG.iterate (toEuclideanLin A) b x₀ k).p,
            toEuclideanLin A (CG.iterate (toEuclideanLin A) b x₀ k).p⟫_ℝ := by
  have hAsc := (Matrix.posDef_iff_isSymmetricCoercive A).1 hA
  set A' := toEuclideanLin A with hA'
  refine ⟨CG.iterate_x_eq_conjugateDirection_iterate b x₀ hAsc, CG.residual_eq A' b x₀, rfl,
    CG.iterate_succ_p A' b x₀, CG.beta_iterate A' b x₀, fun k => ?_⟩
  rw [CG.beta_iterate]
  set s := CG.iterate A' b x₀ k with hs
  set s' := CG.iterate A' b x₀ (k + 1) with hs'
  rcases eq_or_ne s.r 0 with h0 | h0
  · -- a vanishing residual makes every quantity vanish
    have hr' : s'.r = 0 := by
      rw [hs', CG.iterate_succ_r, ← hs, h0, CG.alpha, h0, inner_zero_left, zero_div, zero_smul,
        sub_zero]
    rw [hr', h0]
    simp
  · have hq : 0 < ⟪A' s.p, s.p⟫_ℝ := by
      simpa using CG.re_inner_apply_direction_pos b x₀ hAsc h0
    have hα : CG.alpha A' s = ⟪s.r, s.r⟫_ℝ / ⟪A' s.p, s.p⟫_ℝ := rfl
    have hrr : 0 < ⟪s.r, s.r⟫_ℝ := real_inner_self_pos.2 h0
    have hα0 : CG.alpha A' s ≠ 0 := by rw [hα]; positivity
    -- `α A p = r - r'`
    have hAp : CG.alpha A' s • A' s.p = s.r - s'.r := by
      rw [hs', CG.iterate_succ_r, ← hs]; abel
    have horth : ⟪s'.r, s.r⟫_ℝ = 0 := CG.inner_residual_eq_zero b x₀ hAsc (Nat.succ_ne_self k)
    have h1 : CG.alpha A' s * ⟪s'.r, A' s.p⟫_ℝ = -⟪s'.r, s'.r⟫_ℝ := by
      rw [← inner_smul_right, hAp, inner_sub_right, horth, zero_sub]
    have h2 : ⟪s.p, A' s.p⟫_ℝ = ⟪A' s.p, s.p⟫_ℝ := real_inner_comm _ _
    rw [h2, div_eq_div_iff hrr.ne' hq.ne']
    rw [hα, div_mul_eq_mul_div, div_eq_iff hq.ne'] at h1
    linear_combination h1

/-- **Remark 7.2 (the nonquadratic case).** The Fletcher–Reeves and Polak–Ribière coefficients,
`β_k = ‖∇f(x^{(k)})‖₂² / ‖∇f(x^{(k-1)})‖₂²` and
`β_k = ∇f(x^{(k)})ᵀ(∇f(x^{(k)}) - ∇f(x^{(k-1)})) / ‖∇f(x^{(k-1)})‖₂²`
(`NonlinearCG.betaFletcherReeves`, `NonlinearCG.betaPolakRibiere`), with the initial direction
`d^{(0)} = -∇f(x^{(0)})` (the book's `β₁ = 0`) and the recurrence
`d^{(k+1)} = -∇f(x^{(k+1)}) + β_{k+1} d^{(k)}`, define the nonlinear conjugate gradient methods
`NonlinearCG.iterate (∇f) β α x₀` for any step rule `α`. On the quadratic (7.35) with exact line
searches (`NonlinearCG.exactStep`) both reproduce the conjugate gradient iterates, which is the
sense in which they extend the method to non-quadratic `f`
(`NonlinearCG.iterate_fletcherReeves_eq_CG_iterate`,
`NonlinearCG.iterate_polakRibiere_eq_CG_iterate`). -/
theorem remark_7_2 (gOld gNew : EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (x₀ : EuclideanSpace ℝ (Fin n))
    (hA : A.PosDef) :
    NonlinearCG.betaFletcherReeves gOld gNew = ‖gNew‖ ^ 2 / ‖gOld‖ ^ 2 ∧
      NonlinearCG.betaPolakRibiere gOld gNew = ⟪gNew, gNew - gOld⟫_ℝ / ‖gOld‖ ^ 2 ∧
      (NonlinearCG.init g x₀).d = -g x₀ ∧
      (∀ (β : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
        (α : NonlinearCG.State (EuclideanSpace ℝ (Fin n)) → ℝ) (k : ℕ),
        (NonlinearCG.iterate g β α x₀ (k + 1)).d
          = -g (NonlinearCG.iterate g β α x₀ (k + 1)).x
            + β (g (NonlinearCG.iterate g β α x₀ k).x) (g (NonlinearCG.iterate g β α x₀ (k + 1)).x)
              • (NonlinearCG.iterate g β α x₀ k).d) ∧
      (∀ k, NonlinearCG.iterate (gradient (energyFunctional (toEuclideanLin A) b))
          NonlinearCG.betaFletcherReeves (NonlinearCG.exactStep (toEuclideanLin A)) x₀ k
        = ⟨(CG.iterate (toEuclideanLin A) b x₀ k).x, -(CG.iterate (toEuclideanLin A) b x₀ k).r,
            (CG.iterate (toEuclideanLin A) b x₀ k).p⟩) ∧
      ∀ k, NonlinearCG.iterate (gradient (energyFunctional (toEuclideanLin A) b))
          NonlinearCG.betaPolakRibiere (NonlinearCG.exactStep (toEuclideanLin A)) x₀ k
        = ⟨(CG.iterate (toEuclideanLin A) b x₀ k).x, -(CG.iterate (toEuclideanLin A) b x₀ k).r,
            (CG.iterate (toEuclideanLin A) b x₀ k).p⟩ := by
  have hAsc := (Matrix.posDef_iff_isSymmetricCoercive A).1 hA
  have hg : gradient (energyFunctional (toEuclideanLin A) b) = fun x => toEuclideanLin A x - b :=
    funext fun x => (equation_7_35 (isHermitian_iff_isSymm.1 hA.1) x).2.1
  refine ⟨rfl, rfl, rfl, fun β α k => ?_, fun k => ?_, fun k => ?_⟩
  · rw [NonlinearCG.iterate_succ, NonlinearCG.step_d, NonlinearCG.step_g, NonlinearCG.step_x,
      NonlinearCG.iterate_g]
  · rw [hg]
    exact NonlinearCG.iterate_fletcherReeves_eq_CG_iterate hAsc b x₀ k
  · rw [hg]
    exact NonlinearCG.iterate_polakRibiere_eq_CG_iterate hAsc b x₀ k

end Quadratic

/-! ### Newton's method for minimization, (7.40)–(7.41) -/

section NewtonMin

variable {f : EuclideanSpace ℝ (Fin n) → ℝ}

/-- **(7.40) and the remark after (7.41).** Newton's method for minimization,
`d^{(k)} = -H_k⁻¹ ∇f(x^{(k)})`, `x^{(k+1)} = x^{(k)} + d^{(k)}`, is Newton's method (7.4) applied to
`∇f` with the Hessian matrix as Jacobian: the backbone's
`Newton.iterate (gradient f) (fun x => toEuclideanCLM (hessianMatrix f x)) x₀`. "A result analogous
to Theorem 7.1 holds": if `∇f(x*) = 0`, `f` is `C²` on `B(x*; R)`, `H(x*)` is invertible with
`‖H(x*)⁻¹‖ ≤ C` and `H` is `L`-Lipschitz on the ball (as operators on `ℝⁿ`), then from every start
close enough to `x*` the iterates are well defined and converge quadratically to `x*`. It is
`theorem_7_1` for `F = ∇f`, whose derivative is `H` (`hasFDerivAt_gradient`). -/
theorem equation_7_40 {xstar : EuclideanSpace ℝ (Fin n)} (hcrit : gradient f xstar = 0)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (he : (e : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      = toEuclideanCLM (𝕜 := ℝ) (hessianMatrix f xstar))
    {R C L : ℝ} (hR : 0 < R) (hC : 0 < C) (hL : 0 < L)
    (hCe : ‖(e.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))‖ ≤ C)
    (hf : ∀ x ∈ ball xstar R, ContDiffAt ℝ 2 f x)
    (hLip : ∀ x ∈ ball xstar R, ∀ y ∈ ball xstar R,
      ‖toEuclideanCLM (𝕜 := ℝ) (hessianMatrix f x) - toEuclideanCLM (𝕜 := ℝ) (hessianMatrix f y)‖
        ≤ L * ‖x - y‖) :
    (∀ (x₀ : EuclideanSpace ℝ (Fin n)) (k : ℕ),
      Newton.iterate (gradient f) (fun x => toEuclideanCLM (𝕜 := ℝ) (hessianMatrix f x)) x₀ (k + 1)
        = Newton.iterate (gradient f) (fun x => toEuclideanCLM (𝕜 := ℝ) (hessianMatrix f x)) x₀ k
          - (toEuclideanCLM (𝕜 := ℝ) (hessianMatrix f
              (Newton.iterate (gradient f) (fun x => toEuclideanCLM (𝕜 := ℝ) (hessianMatrix f x))
                x₀ k))).inverse
            (gradient f (Newton.iterate (gradient f)
              (fun x => toEuclideanCLM (𝕜 := ℝ) (hessianMatrix f x)) x₀ k))) ∧
    ∃ r > 0, ∀ x₀ ∈ ball xstar r,
      (∀ k, ∃ e' : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
        (e' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
          = toEuclideanCLM (𝕜 := ℝ) (hessianMatrix f (Newton.iterate (gradient f)
              (fun x => toEuclideanCLM (𝕜 := ℝ) (hessianMatrix f x)) x₀ k))) ∧
      Tendsto (Newton.iterate (gradient f)
        (fun x => toEuclideanCLM (𝕜 := ℝ) (hessianMatrix f x)) x₀) atTop (𝓝 xstar) ∧
      ∀ k, ‖Newton.iterate (gradient f) (fun x => toEuclideanCLM (𝕜 := ℝ) (hessianMatrix f x)) x₀
            (k + 1) - xstar‖
        ≤ C * L * ‖Newton.iterate (gradient f)
            (fun x => toEuclideanCLM (𝕜 := ℝ) (hessianMatrix f x)) x₀ k - xstar‖ ^ 2 :=
  ⟨fun x₀ k => by rw [Newton.iterate_succ]; rfl,
    theorem_7_1 hcrit e he hR hC hL hCe (fun x hx => hasFDerivAt_gradient (hf x hx)) hLip⟩

/-- **The remark after (7.41).** For the quadratic (7.35) with `A` symmetric positive definite,
Newton's method (7.40) converges in one step: `x^{(1)} = A⁻¹ b` from any `x^{(0)}`, because
`H = A` and `∇f(x^{(0)}) = A x^{(0)} - b` (`equation_7_35`). -/
theorem equation_7_41 {A : Matrix (Fin n) (Fin n) ℝ} {b : EuclideanSpace ℝ (Fin n)} (hA : A.PosDef)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    Newton.iterate (gradient (energyFunctional (toEuclideanLin A) b))
        (fun x => toEuclideanCLM (𝕜 := ℝ) (hessianMatrix (energyFunctional (toEuclideanLin A) b) x))
        x₀ 1
      = toEuclideanLin A⁻¹ b := by
  have hu : IsUnit A := hA.isUnit
  have hS : A.IsSymm := isHermitian_iff_isSymm.1 hA.1
  rw [Newton.iterate, Function.iterate_one, Newton.step, (equation_7_35 hS x₀).2.2,
    (equation_7_35 hS x₀).2.1, ← ContinuousLinearMap.ringInverse_eq_inverse,
    ← toEuclideanCLM_nonsing_inv hu]
  change x₀ - toEuclideanLin A⁻¹ (toEuclideanLin A x₀ - b) = toEuclideanLin A⁻¹ b
  rw [map_sub, toEuclideanLin_nonsing_inv_mul_apply hu]
  abel

end NewtonMin

/-! ### Global convergence: Properties 7.7 and 7.8 -/

section Global

variable {f : EuclideanSpace ℝ (Fin n) → ℝ}

-- The `C¹` hypothesis `hf` and `σ < β` are the book's; the backbone's Zoutendijk theorem
-- (`LineSearch.tendsto_atBot_or_tendsto_zero`) needs only the Lipschitz gradient, `0 < σ` and
-- `β < 1`.
set_option linter.unusedVariables false in
/-- **Property 7.7 (convergence).** Let `f ∈ C¹(ℝⁿ)` with `‖∇f(x) - ∇f(y)‖₂ ≤ L ‖x - y‖₂`, and let
`x^{(k)}` be generated by a gradient-like method — the descent method (7.25)–(7.26), with
`d^{(k)ᵀ} ∇f(x^{(k)}) < 0` where `∇f(x^{(k)}) ≠ 0` and `d^{(k)} = 0` where `∇f(x^{(k)}) = 0` — whose
steps satisfy (7.31) and (7.33) with `0 < σ < β < 1`. Then one of the following occurs:
(1) `∇f(x^{(k)}) = 0` for some `k`; (2) `f(x^{(k)}) → -∞`;
(3) `∇f(x^{(k)})ᵀ d^{(k)} / ‖d^{(k)}‖₂ → 0`.
Case (1) is the termination case; otherwise the method is a `Descent.IsDescentSequence` and
Zoutendijk's theorem applies. The book cites Wolfe for the proof. -/
theorem property_7_7 (hf : ContDiff ℝ 1 f) {L : ℝ}
    (hL : ∀ y z, ‖gradient f y - gradient f z‖ ≤ L * ‖y - z‖)
    {x d : ℕ → EuclideanSpace ℝ (Fin n)} {α : ℕ → ℝ} (hstep : ∀ k, x (k + 1) = x k + α k • d k)
    (hα : ∀ k, 0 < α k)
    (hd : ∀ k, (gradient f (x k) ≠ 0 → ⟪gradient f (x k), d k⟫_ℝ < 0) ∧
      (gradient f (x k) = 0 → d k = 0))
    {σ β : ℝ} (harmijo : ∀ k, LineSearch.Armijo f (fderiv ℝ f) σ (x k) (d k) (α k))
    (hwolfe : ∀ k, LineSearch.WolfeCurvature (fderiv ℝ f) β (x k) (d k) (α k))
    (hσ : 0 < σ) (hσβ : σ < β) (hβ : β < 1) :
    (∃ k, gradient f (x k) = 0) ∨ Tendsto (fun k => f (x k)) atTop atBot ∨
      Tendsto (fun k => ⟪gradient f (x k), d k⟫_ℝ / ‖d k‖) atTop (𝓝 0) := by
  by_cases hz : ∃ k, gradient f (x k) = 0
  · exact Or.inl hz
  simp only [not_exists] at hz
  right
  have hseq : Descent.IsDescentSequence (fderiv ℝ f) x d α :=
    ⟨hstep, hα, fun k => by
      rw [Descent.IsDescentDirection, fderiv_eq_innerSL_gradient, innerSL_apply_apply]
      exact (hd k).1 (hz k)⟩
  have hL' : ∀ y z, ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ L * ‖y - z‖ := fun y z => by
    rw [fderiv_eq_innerSL_gradient, fderiv_eq_innerSL_gradient, ← map_sub, innerSL_apply_norm]
    exact hL y z
  have h := LineSearch.tendsto_atBot_or_tendsto_zero hL' hseq harmijo hwolfe hσ hβ
  simpa only [fderiv_eq_innerSL_gradient, innerSL_apply_apply] using h

/-- **Property 7.8, as intended.** Let `f ∈ C¹(ℝⁿ)` and let `x^{(k)}` be a bounded sequence
generated by a gradient-like method, in the book's sense that any limit (cluster point) of the
sequence is a critical point of `f`. Then `∇f(x^{(k)}) → 0`.
`Descent.tendsto_fderiv_zero_of_forall_clusterPt`. -/
theorem property_7_8 (hf : ContDiff ℝ 1 f) {x : ℕ → EuclideanSpace ℝ (Fin n)}
    (hb : Bornology.IsBounded (Set.range x))
    (hcl : ∀ y, MapClusterPt y atTop x → IsCriticalPoint f y) :
    Tendsto (fun k => gradient f (x k)) atTop (𝓝 0) := by
  have h := Descent.tendsto_fderiv_zero_of_forall_clusterPt (f' := fderiv ℝ f)
    (hf.continuous_fderiv one_ne_zero) hb fun y hy => by
      rw [fderiv_eq_innerSL_gradient, hcl y hy, map_zero]
  have hc := ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.tendsto
    0).comp h
  rw [map_zero] at hc
  exact hc

/-- **Property 7.8, read literally**: for `f ∈ C¹(ℝⁿ)`, if `x^{(k)}` converges to a critical point
`y` of `f`, then `∇f(x^{(k)}) → 0` — the continuity of `∇f`. -/
theorem property_7_8_of_tendsto (hf : ContDiff ℝ 1 f) {x : ℕ → EuclideanSpace ℝ (Fin n)}
    {y : EuclideanSpace ℝ (Fin n)} (hx : Tendsto x atTop (𝓝 y)) (hy : IsCriticalPoint f y) :
    Tendsto (fun k => gradient f (x k)) atTop (𝓝 0) := by
  have hcont : Continuous (gradient f) := by
    rw [gradient_eq_toDual_symm_fderiv]
    exact (InnerProductSpace.toDual ℝ _).symm.continuous.comp (hf.continuous_fderiv one_ne_zero)
  have := (hcont.tendsto y).comp hx
  rwa [hy] at this

end Global

/-! ### Secant-like methods, §7.2.7 -/

section Secant

/-- **(7.42).** The rank-one secant update
`B_{k+1} = B_k + ((y^{(k)} - B_k s^{(k)}) cᵀ) / (cᵀ s^{(k)})` (`Matrix.rankOneSecantUpdate`)
satisfies the secant equation `B_{k+1} s^{(k)} = y^{(k)}` whenever `cᵀ s^{(k)} ≠ 0`, and the
choice `c = s^{(k)}` is Broyden's update of §7.1.4.
`Matrix.rankOneSecantUpdate_mulVec`, `Matrix.broydenUpdate_eq_rankOneSecantUpdate`. -/
theorem equation_7_42 (B : Matrix (Fin n) (Fin n) ℝ) {s c : Fin n → ℝ} (hcs : c ⬝ᵥ s ≠ 0)
    (y : Fin n → ℝ) :
    rankOneSecantUpdate B s y c *ᵥ s = y ∧ broydenUpdate B s y = rankOneSecantUpdate B s y s :=
  ⟨rankOneSecantUpdate_mulVec B hcs y, broydenUpdate_eq_rankOneSecantUpdate B s y⟩

/-- **(7.43).** The symmetric rank-one update, (7.42) with `c = y^{(k)} - B_k s^{(k)}`, is
`Matrix.sr1Update B_k s^{(k)} y^{(k)}`; it is symmetric when `B_k` is and satisfies
`B_{k+1} s^{(k)} = y^{(k)}` when `(y^{(k)} - B_k s^{(k)})ᵀ s^{(k)} ≠ 0`. -/
theorem equation_7_43 {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsSymm) {s y : Fin n → ℝ}
    (h : (y - B *ᵥ s) ⬝ᵥ s ≠ 0) :
    sr1Update B s y = rankOneSecantUpdate B s y (y - B *ᵥ s) ∧ (sr1Update B s y).IsSymm ∧
      sr1Update B s y *ᵥ s = y :=
  ⟨rfl, sr1Update_isSymm hB s y, sr1Update_mulVec B h⟩

/-- **(7.44).** With `C_k = B_k⁻¹` for a symmetric nonsingular `B_k`, and
`(s^{(k)} - C_k y^{(k)})ᵀ y^{(k)} ≠ 0`, the inverse of the symmetric rank-one update is
`C_{k+1} = C_k + (w wᵀ) / (wᵀ y^{(k)})` with `w = s^{(k)} - C_k y^{(k)}` (the display (7.44)),
by the Sherman–Morrison formula (3.57). `Matrix.sr1Update_inv`. -/
theorem equation_7_44 {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsSymm) (hu : IsUnit B)
    {s y : Fin n → ℝ} (hσ : (y - B *ᵥ s) ⬝ᵥ s ≠ 0) (hw : (s - B⁻¹ *ᵥ y) ⬝ᵥ y ≠ 0) :
    (sr1Update B s y)⁻¹
      = B⁻¹ + (1 / ((s - B⁻¹ *ᵥ y) ⬝ᵥ y)) • vecMulVec (s - B⁻¹ *ᵥ y) (s - B⁻¹ *ᵥ y) :=
  sr1Update_inv hB hu hσ hw

/-- **(7.45)–(7.46).** The symmetrization iteration
`B^{(2j+1)} = B^{(2j)} + ((y - B^{(2j)} s) cᵀ)/(cᵀ s)`,
`B^{(2j+2)} = (B^{(2j+1)} + B^{(2j+1)ᵀ})/2` from a symmetric `B^{(0)} = B_k`
(`Matrix.symmetrizationStep`) converges, as `j → ∞`, to the matrix (7.46)
`Matrix.generalSymmetricUpdate B_k s y c`; with `c = s` the limit is the symmetric
Powell–Broyden matrix `B_SPB = Matrix.psbUpdate B_k s y`, which is symmetric and satisfies the
secant equation. The book says "it can be shown"; `Matrix.tendsto_symmetrizationStep_iterate`. -/
theorem equation_7_46 {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsSymm) {s c : Fin n → ℝ}
    (hcs : c ⬝ᵥ s ≠ 0) (hs : s ≠ 0) (y : Fin n → ℝ) :
    Tendsto (fun j => (symmetrizationStep s y c)^[j] B) atTop
        (𝓝 (generalSymmetricUpdate B s y c)) ∧
      psbUpdate B s y = generalSymmetricUpdate B s y s ∧ (psbUpdate B s y).IsSymm ∧
      psbUpdate B s y *ᵥ s = y :=
  ⟨tendsto_symmetrizationStep_iterate hcs hB, rfl, psbUpdate_isSymm hB s y,
    psbUpdate_mulVec B hs y⟩

open scoped Matrix.Norms.Frobenius

/-- **The characterization after (7.46).** `B_SPB = Matrix.psbUpdate B_k s^{(k)} y^{(k)}` is the
unique solution of the problem: find a symmetric `B̄` with `B̄ s^{(k)} = y^{(k)}` minimizing
`‖B̄ - B_k‖_F`, for symmetric `B_k` and `s^{(k)} ≠ 0`. `Matrix.frobenius_norm_psbUpdate_sub_le`
and its strict form `Matrix.frobenius_norm_psbUpdate_sub_lt`. -/
theorem psbLeastChange {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsSymm) {s : Fin n → ℝ} (hs : s ≠ 0)
    (y : Fin n → ℝ) :
    (psbUpdate B s y).IsSymm ∧ psbUpdate B s y *ᵥ s = y ∧
      (∀ B' : Matrix (Fin n) (Fin n) ℝ, B'.IsSymm → B' *ᵥ s = y →
        ‖psbUpdate B s y - B‖ ≤ ‖B' - B‖) ∧
      ∀ B' : Matrix (Fin n) (Fin n) ℝ, B'.IsSymm → B' *ᵥ s = y →
        ‖B' - B‖ ≤ ‖psbUpdate B s y - B‖ → B' = psbUpdate B s y :=
  ⟨psbUpdate_isSymm hB s y, psbUpdate_mulVec B hs y,
    fun B' hB' hB's => frobenius_norm_psbUpdate_sub_le hB hs hB' hB's, fun B' hB' hB's hle => by
      by_contra hne
      exact absurd hle (not_le.2 (frobenius_norm_psbUpdate_sub_lt hB hs hB' hB's hne))⟩

/-- **The last display of §7.2.7 (bounded deterioration).** If `f` is `C²` on an open convex `D`
containing `x^{(k)}` and `x^{(k+1)} = x^{(k)} + s^{(k)}`, its Hessian `H` is Lipschitz continuous
on `D` with constant `L` in the Frobenius norm, `y^{(k)} = ∇f(x^{(k+1)}) - ∇f(x^{(k)})`, and `B_k`
is symmetric, then `‖B_SPB - H(x^{(k+1)})‖_F ≤ ‖B_k - H(x^{(k)})‖_F + 3 L ‖s^{(k)}‖`.
`Matrix.frobenius_norm_psbUpdate_sub_le_add` with `H = hessianMatrix f`, whose derivative
relation to `∇f` is `hasFDerivAt_gradient`. -/
theorem psbBoundedDeterioration {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : Convex ℝ D) (hf : ∀ w ∈ D, ContDiffAt ℝ 2 f w)
    {L : ℝ} (hL : ∀ w ∈ D, ∀ z ∈ D, ‖hessianMatrix f w - hessianMatrix f z‖ ≤ L * ‖w - z‖)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ D) {s : Fin n → ℝ} (hs : s ≠ 0)
    (hxs : x + toLp 2 s ∈ D) {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsSymm) :
    ‖psbUpdate B s (ofLp (gradient f (x + toLp 2 s) - gradient f x))
        - hessianMatrix f (x + toLp 2 s)‖
      ≤ ‖B - hessianMatrix f x‖ + 3 * L * ‖toLp 2 s‖ :=
  frobenius_norm_psbUpdate_sub_le_add hD (fun w hw => hasFDerivAt_gradient (hf w hw))
    (fun w hw => hessianMatrix_isSymm (hf w hw)) hL hx hs hxs hB

end Secant

end QuarteroniSaccoSaleri.Chapter07
