import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.MeasureTheory.Function.Holder
import Numlib.Analysis.Calculus.ContDiffOnClosure
import Numlib.Analysis.Sobolev.Compactness
import Numlib.Analysis.Sobolev.Poincare
import Numlib.Analysis.Sobolev.Zero
import Numlib.Analysis.Normed.Operator.Riesz
import Numlib.Variational.EllipticInterval
import Numlib.Variational.Inequality.Basic

/-!
# The variational formulation of second-order elliptic boundary value problems

Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, §9.5: the weak
theory of the Dirichlet and Neumann problems for `-Δu + u = f` and for the general second-order
operator `-∑ ∂_j (a_ij ∂_i u) + ∑ a_i ∂_i u + a_0 u` on an open set `Ω ⊆ ℝ^N`, in the Hilbert
spaces `H^1(Ω) = SobolevEuclidean N 1 2 Ω` and `H^1_0(Ω) = SobolevEuclideanZero N 1 2 Ω` of
`Numlib/Analysis/Sobolev/MultiIndex.lean`.

## The forms

A bilinear form is a `SesqForm ℝ (H^1(Ω))` assembled, as `EllipticInterval.form` is on `H^1(a, b)`,
from `L²(Ω)`-pairings `(u, v) ↦ ⟪T (∂^α u), ∂^β v⟫` of weak derivatives through a bounded operator
`T` on `L²(Ω)` — the identity, or multiplication by an `L^∞(Ω)` coefficient (`Elliptic.mulL`):

* `Elliptic.dirichletForm Ω`, the Dirichlet form `∫_Ω ∇u · ∇v`;
* `Elliptic.laplaceForm Ω`, the form `∫_Ω ∇u · ∇v + ∫_Ω u v` of `-Δ + 1`, which **is the inner
  product of `H^1(Ω)`** (`Elliptic.laplaceForm_eq_innerSL`), so that the existence theorems for
  it are the Riesz representation theorem and need no boundedness of `Ω`;
* `Elliptic.generalForm Ω A a₁ a₀`, the form (41) of the general operator with `L^∞` coefficients,
  with the ellipticity condition `Elliptic.IsUniformlyElliptic`, Gårding's inequality
  (`Elliptic.generalForm_garding`, with an explicit shift) and its coercivity on `H^1_0(Ω)` of a
  bounded `Ω` when `a₁ = 0` and `a₀ ≥ 0` (Poincaré's inequality).

A weak problem is `IsGalerkinSolution a (load Ω f) K u` of `Numlib/Variational/Galerkin.lean`
with `K = H^1_0(Ω)` (Dirichlet) or `K = ⊤` (Neumann); nothing distinguishes the continuous problem
from a Galerkin discretization.

## Main results

* `Elliptic.existsUnique_isGalerkinSolution_laplace` and
  `Elliptic.isMinOn_energy_iff_isGalerkinSolution_laplace`: **Theorem 9.21** (Dirichlet's
  principle);
* `Elliptic.isGalerkinSolution_laplace_of_classical` and
  `Elliptic.laplacian_ae_eq_of_isGalerkinSolution`: Steps A and D of Example 1, a classical
  solution is a weak solution and a `C²` weak solution satisfies the equation — the interior
  half of Step A, without the boundary condition, is
  `Elliptic.exists_sobolev_forall_laplaceForm_eq_load_of_classical` (what Example 2 uses);
* `Elliptic.existsUnique_isWeakSolution_inhomogeneous`: **Proposition 9.22** (inhomogeneous
  Dirichlet data, on the affine set `Elliptic.admissibleSet`);
* `Elliptic.existsUnique_isGalerkinSolution_general_of_nonneg`: Example 3;
* `Elliptic.existsUnique_isGalerkinSolution_neumann`: **Proposition 9.24** (Neumann);
* `Elliptic.solutionOperator`, the solution operator `T : L²(Ω) → L²(Ω)` of a form coercive on
  `H^1_0(Ω)`, compact when `Ω` has finite measure (`Elliptic.solutionOperator_isCompactOperator`,
  by the Rellich–Kondrachov theorem on `W_0^{1,p}(Ω)` of Remark 20,
  `Numlib/Analysis/Sobolev/Compactness.lean`), and the Fredholm alternative of **Theorem 9.23**
  first for a compact `T` (`Elliptic.finiteDimensional_homogeneousKernel_of_isCompactOperator`,
  `Elliptic.exists_orthogonality_iff_exists_solution_of_isCompactOperator`), then for the general
  form (41) on an open set of finite measure (`Elliptic.finiteDimensional_ker_general`,
  `Elliptic.exists_orthogonality_iff_exists_solution`), with **Remark 23**
  (`Elliptic.existsUnique_of_ker_eq_bot`).

## Conventions

Coefficients live in `Lp ℝ ⊤ (volume.restrict Ω)`, so the book's `C^1(Ω̄)` coefficients enter as
`L^∞` classes on a bounded `Ω` and the ellipticity condition is stated almost everywhere. The
Laplacian of a classical solution is Mathlib's `Δ` (`InnerProductSpace.instLaplacian`, computed in
coordinates by `laplacian_eq_iteratedFDeriv_orthonormalBasis`). The book's `u ∈ C²(Ω̄)` of a
classical solution is `ContDiffOnClosure ℝ 2 u Ω` (`Numlib/Analysis/Calculus/ContDiffOnClosure`:
`C²` on `Ω` with derivatives of order `≤ 2` extending continuously to `Ω̄`, footnote 16 of
[brezis2011functional] §9.3), together with `ContinuousOn u (closure Ω)` where boundary values
are read; Mathlib's stronger `ContDiffOn ℝ 2 u (closure Ω)` implies both.

## References

[brezis2011functional], §9.5: Examples 1–4, Theorem 9.21, Proposition 9.22, Theorem 9.23,
Remark 23, Proposition 9.24.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology InnerProductSpace

noncomputable section

namespace Elliptic

variable {N : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin N)))

/-! ### Multiplication by an `L^∞` coefficient, and the pairings -/

/-- Multiplication by an `L^∞(Ω)` coefficient, as a continuous linear map on `L²(Ω)`: Mathlib's
Hölder product at the exponents `(2, ∞, 2)`. The same construction as `EllipticInterval.mulL`,
on an open subset of `ℝ^N`. -/
def mulL (a : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →L[ℝ]
      Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  ((ContinuousLinearMap.mul ℝ ℝ).holderL (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
    2 ⊤ 2).flip a

/-- `Elliptic.mulL a f` is the pointwise product `a f` almost everywhere. -/
theorem coeFn_mulL (a : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    mulL Ω a f =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fun x ↦ a x * f x := by
  refine ((ContinuousLinearMap.mul ℝ ℝ).coeFn_holder f a).trans (Eventually.of_forall fun x ↦ ?_)
  simp [mul_comm]

/-- `‖a f‖_{L²} ≤ ‖a‖_∞ ‖f‖_{L²}`. -/
theorem norm_mulL_apply_le (a : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ‖mulL Ω a f‖ ≤ ‖a‖ * ‖f‖ := by
  refine ((ContinuousLinearMap.mul ℝ ℝ).norm_holder_apply_apply_le f a).trans ?_
  calc ‖ContinuousLinearMap.mul ℝ ℝ‖ * ‖f‖ * ‖a‖ ≤ 1 * ‖f‖ * ‖a‖ := by
        gcongr; exact ContinuousLinearMap.opNorm_mul_le ℝ ℝ
    _ = ‖a‖ * ‖f‖ := by ring

/-- `‖mulL a‖ ≤ ‖a‖_∞`. -/
theorem norm_mulL_le (a : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ‖mulL Ω a‖ ≤ ‖a‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (norm_mulL_apply_le Ω a)

/-- `⟪a f, g⟫_{L²} = ∫_Ω a f g`. -/
theorem inner_mulL_eq_integral (a : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (f g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ⟪mulL Ω a f, g⟫_ℝ = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), a x * f x * g x := by
  rw [L2.inner_def]
  refine integral_congr_ae ((coeFn_mulL Ω a f).mono fun x hx ↦ ?_)
  simp only [hx, RCLike.inner_apply, conj_trivial]
  ring

/-- The product of an `L^∞` coefficient and two `L²` functions is integrable on `Ω`. -/
theorem integrable_mul_mul (a : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (f g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    Integrable (fun x ↦ a x * f x * g x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
  refine (L2.integrable_inner (𝕜 := ℝ) (mulL Ω a f) g).congr
    ((coeFn_mulL Ω a f).mono fun x hx ↦ ?_)
  simp only [hx, RCLike.inner_apply, conj_trivial]
  ring

/-- The pairing `(u, v) ↦ ⟪T (∂^α u), ∂^β v⟫_{L²(Ω)}` of two weak derivatives of elements of
`H^1(Ω)` through a bounded operator `T` on `L²(Ω)`, as a bounded bilinear form on `H^1(Ω)`
(`SobolevMultiIndex.weakDerivL` is the weak derivative as a continuous linear map). Every form of
this file is a finite sum of pairings. -/
def pairing (T : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →L[ℝ]
      Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (α β : MultiIndexLE (Fin N) 1) : SesqForm ℝ (SobolevEuclidean N 1 2 Ω) :=
  (((innerSL ℝ).comp (T.comp (SobolevMultiIndex.weakDerivL ℝ
    (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume α))).flip.comp
      (SobolevMultiIndex.weakDerivL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
        volume β)).flip

/-- `Elliptic.pairing` is the inner product it was built from. -/
theorem pairing_apply (T : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →L[ℝ]
      Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (α β : MultiIndexLE (Fin N) 1) (u v : SobolevEuclidean N 1 2 Ω) :
    pairing Ω T α β u v
      = ⟪T (SobolevMultiIndex.weakDeriv u α), SobolevMultiIndex.weakDeriv v β⟫_ℝ :=
  rfl

/-- `|pairing T α β u v| ≤ ‖T‖ ‖∂^α u‖₂ ‖∂^β v‖₂`. -/
theorem abs_pairing_le (T : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →L[ℝ]
      Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (α β : MultiIndexLE (Fin N) 1) (u v : SobolevEuclidean N 1 2 Ω) :
    |pairing Ω T α β u v|
      ≤ ‖T‖ * ‖SobolevMultiIndex.weakDeriv u α‖ * ‖SobolevMultiIndex.weakDeriv v β‖ := by
  rw [pairing_apply]
  exact (abs_real_inner_le_norm _ _).trans (by gcongr; exact T.le_opNorm _)

/-- `|pairing T α β u v| ≤ ‖T‖ ‖u‖ ‖v‖` in the `H^1` norm. -/
theorem abs_pairing_le' (T : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →L[ℝ]
      Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (α β : MultiIndexLE (Fin N) 1) (u v : SobolevEuclidean N 1 2 Ω) :
    |pairing Ω T α β u v| ≤ ‖T‖ * ‖u‖ * ‖v‖ :=
  (abs_pairing_le Ω T α β u v).trans (by
    gcongr
    · exact SobolevMultiIndex.norm_weakDeriv_le u α
    · exact SobolevMultiIndex.norm_weakDeriv_le v β)

/-- A pairing through the identity is symmetric in `(u, α)` and `(v, β)`. -/
theorem pairing_id_comm (α β : MultiIndexLE (Fin N) 1) (u v : SobolevEuclidean N 1 2 Ω) :
    pairing Ω (ContinuousLinearMap.id ℝ _) α β u v
      = pairing Ω (ContinuousLinearMap.id ℝ _) β α v u := by
  simp only [pairing_apply, ContinuousLinearMap.id_apply]
  exact real_inner_comm _ _

/-! ### The Dirichlet form and the form of `-Δ + 1` -/

/-- **The Dirichlet form** `a₀(u, v) = ∫_Ω ∇u · ∇v = ∑ᵢ ∫_Ω ∂ᵢu ∂ᵢv` on `H^1(Ω)`
([brezis2011functional] Corollary 9.19, the scalar product of `H^1_0(Ω)`; Theorem 9.31). -/
def dirichletForm : SesqForm ℝ (SobolevEuclidean N 1 2 Ω) :=
  ∑ i : Fin N,
    pairing Ω (ContinuousLinearMap.id ℝ _) (MultiIndexLE.single i) (MultiIndexLE.single i)

/-- The Dirichlet form as a sum of `L²` inner products of the partial derivatives. -/
theorem dirichletForm_apply_inner (u v : SobolevEuclidean N 1 2 Ω) :
    dirichletForm Ω u v = ∑ i : Fin N, ⟪SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i),
      SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i)⟫_ℝ := by
  simp only [dirichletForm, sum_apply, pairing_apply,
    ContinuousLinearMap.id_apply]

/-- **The Dirichlet form is the integral `∫_Ω ∇u · ∇v`**:
`dirichletForm Ω u v = ∫ x in Ω, ∑ i, ∂ᵢu x * ∂ᵢv x`. -/
theorem dirichletForm_apply (u v : SobolevEuclidean N 1 2 Ω) :
    dirichletForm Ω u v = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      ∑ i : Fin N, SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
        * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x := by
  rw [dirichletForm_apply_inner, integral_finsetSum Finset.univ fun i _ ↦ ?_]
  · exact Finset.sum_congr rfl fun i _ ↦ L2.inner_eq_integral_mul _ _
  · exact (L2.integrable_inner (𝕜 := ℝ) (SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i))
      (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i))).congr
      (Eventually.of_forall fun x ↦ by simp [RCLike.inner_apply, mul_comm])

/-- The Dirichlet form is symmetric. -/
theorem dirichletForm_isHermitian : (dirichletForm Ω).IsHermitian := fun u v ↦ by
  rw [dirichletForm_apply_inner, dirichletForm_apply_inner, conj_trivial]
  exact Finset.sum_congr rfl fun i _ ↦ real_inner_comm _ _

/-- The diagonal of the Dirichlet form is `∫_Ω |∇v|² = ∑ᵢ ‖∂ᵢv‖₂²`. -/
theorem dirichletForm_self_eq (v : SobolevEuclidean N 1 2 Ω) :
    dirichletForm Ω v v
      = ∑ i : Fin N, ‖SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i)‖ ^ 2 := by
  rw [dirichletForm_apply_inner]
  exact Finset.sum_congr rfl fun i _ ↦ real_inner_self_eq_norm_sq _

/-- The gradient norm is `√(∑ᵢ ‖∂ᵢv‖₂²)` at `p = 2`. -/
theorem gradNorm_eq_sqrt (v : SobolevEuclidean N 1 2 Ω) :
    SobolevMultiIndex.gradNorm v
      = √(∑ i : Fin N, ‖SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i)‖ ^ 2) := by
  rw [SobolevMultiIndex.gradNorm_eq_sum (p := 2) (by norm_num), Real.sqrt_eq_rpow]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]

/-- The squared `H^1` norm is `‖v‖₂² + ∑ᵢ ‖∂ᵢv‖₂²`. -/
theorem norm_sq_eq (v : SobolevEuclidean N 1 2 Ω) :
    ‖v‖ ^ 2 = ‖SobolevMultiIndex.weakDeriv v 0‖ ^ 2
      + ∑ i : Fin N, ‖SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i)‖ ^ 2 := by
  rw [SobolevMultiIndex.norm_eq_sum (p := 2) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (Finset.sum_nonneg fun α _ ↦ sq_nonneg _),
    MultiIndexLE.sum_univ_one]

/-- The diagonal of the Dirichlet form is the square of the gradient norm `‖∇v‖_{L²(Ω)}` of
`Numlib/Analysis/Sobolev/MultiIndex.lean`. -/
theorem dirichletForm_self_eq_gradNorm_sq (v : SobolevEuclidean N 1 2 Ω) :
    dirichletForm Ω v v = SobolevMultiIndex.gradNorm v ^ 2 := by
  rw [dirichletForm_self_eq, gradNorm_eq_sqrt,
    Real.sq_sqrt (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)]

/-- The Dirichlet form is positive: `0 ≤ ∫_Ω |∇v|²`. -/
theorem dirichletForm_self_nonneg (v : SobolevEuclidean N 1 2 Ω) : 0 ≤ dirichletForm Ω v v := by
  rw [dirichletForm_self_eq]
  exact Finset.sum_nonneg fun i _ ↦ sq_nonneg _

/-- `dirichletForm Ω v v ≤ ‖v‖²` in the `H^1` norm: the `H^1` norm squared is `‖v‖₂² + ∫ |∇v|²`. -/
theorem dirichletForm_self_le (v : SobolevEuclidean N 1 2 Ω) : dirichletForm Ω v v ≤ ‖v‖ ^ 2 := by
  rw [dirichletForm_self_eq, norm_sq_eq]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- **The Dirichlet form is bounded by the gradient norms**: `|∫_Ω ∇u · ∇v| ≤ ‖∇u‖₂ ‖∇v‖₂`, by
Cauchy–Schwarz in `L²(Ω)` and in `ℓ²(Fin N)`. -/
theorem abs_dirichletForm_le (u v : SobolevEuclidean N 1 2 Ω) :
    |dirichletForm Ω u v| ≤ SobolevMultiIndex.gradNorm u * SobolevMultiIndex.gradNorm v := by
  rw [dirichletForm_apply_inner, gradNorm_eq_sqrt, gradNorm_eq_sqrt]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ ↦ abs_real_inner_le_norm _ _).trans ?_
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-- **The Dirichlet form is bounded with constant `1`**: `|∫_Ω ∇u · ∇v| ≤ ‖u‖ ‖v‖` in the `H^1`
norm, the gradient norm being bounded by the norm of `H^1(Ω)`. -/
theorem dirichletForm_isBoundedWith : (dirichletForm Ω).IsBoundedWith 1 := fun u v ↦ by
  rw [Real.norm_eq_abs, one_mul]
  refine (abs_dirichletForm_le Ω u v).trans ?_
  gcongr
  · exact SobolevMultiIndex.gradNorm_nonneg _
  · exact SobolevMultiIndex.gradNorm_le_norm u
  · exact SobolevMultiIndex.gradNorm_le_norm v

/-- **The form of `-Δ + 1`**: `a(u, v) = ∫_Ω ∇u · ∇v + ∫_Ω u v` on `H^1(Ω)`, the bilinear form of
[brezis2011functional] Theorem 9.21, Proposition 9.22, Proposition 9.24, Theorem 9.25,
Theorem 9.27 and Corollary 9.28. -/
def laplaceForm : SesqForm ℝ (SobolevEuclidean N 1 2 Ω) :=
  dirichletForm Ω + pairing Ω (ContinuousLinearMap.id ℝ _) 0 0

/-- The form of `-Δ + 1` as inner products: `∑ᵢ ⟪∂ᵢu, ∂ᵢv⟫ + ⟪u, v⟫`. -/
theorem laplaceForm_apply_inner (u v : SobolevEuclidean N 1 2 Ω) :
    laplaceForm Ω u v = (∑ i : Fin N, ⟪SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i),
      SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i)⟫_ℝ)
      + ⟪SobolevMultiIndex.weakDeriv u 0, SobolevMultiIndex.weakDeriv v 0⟫_ℝ := by
  rw [laplaceForm, add_apply, add_apply,
    dirichletForm_apply_inner, pairing_apply, ContinuousLinearMap.id_apply]

/-- The form of `-Δ + 1` is the Dirichlet form plus the `L²` inner product of the functions:
`laplaceForm Ω U V = dirichletForm Ω U V + ⟪U, V⟫_{L²}`. -/
theorem laplaceForm_apply_eq_dirichletForm_add (U V : SobolevEuclidean N 1 2 Ω) :
    laplaceForm Ω U V = dirichletForm Ω U V
      + ⟪SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume U,
        SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume V⟫_ℝ := by
  rw [laplaceForm, add_apply, add_apply, pairing_apply, ContinuousLinearMap.id_apply]
  rfl

/-- `laplaceForm_apply_eq_dirichletForm_add` with the `L²` functions written as the zeroth weak
derivatives (the two spellings are definitionally equal). -/
theorem laplaceForm_apply_eq_dirichletForm_add_weakDeriv (u v : SobolevEuclidean N 1 2 Ω) :
    laplaceForm Ω u v = dirichletForm Ω u v
      + ⟪SobolevMultiIndex.weakDeriv u 0, SobolevMultiIndex.weakDeriv v 0⟫_ℝ := by
  rw [laplaceForm_apply_inner, dirichletForm_apply_inner]

/-- **The form of `-Δ + 1` is the integral (32)**:
`laplaceForm Ω u v = ∫_Ω (∇u · ∇v + u v)`. -/
theorem laplaceForm_apply (u v : SobolevEuclidean N 1 2 Ω) :
    laplaceForm Ω u v = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      ((∑ i : Fin N, SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
        * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x)
        + SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x) := by
  rw [laplaceForm, add_apply, add_apply,
    dirichletForm_apply, pairing_apply, ContinuousLinearMap.id_apply, L2.inner_eq_integral_mul,
    ← integral_add]
  · rfl
  · exact integrable_finsetSum _ fun i _ ↦
      (L2.integrable_inner (𝕜 := ℝ) (SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i))
        (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i))).congr
        (Eventually.of_forall fun x ↦ by simp [RCLike.inner_apply, mul_comm])
  · exact (L2.integrable_inner (𝕜 := ℝ) (SobolevMultiIndex.weakDeriv u 0)
      (SobolevMultiIndex.weakDeriv v 0)).congr
      (Eventually.of_forall fun x ↦ by simp [RCLike.inner_apply, mul_comm])

/-- **The form of `-Δ + 1` is the inner product of `H^1(Ω)`**: `laplaceForm Ω = innerSL ℝ`. The
inner product of the `ℓ²` product of `L²(Ω)` spaces is the sum of the inner products of the
components, indexed by the multi-indices `0` and `e_i` (`MultiIndexLE.sum_univ_one`). This is why
Theorem 9.21 and Proposition 9.24 cost nothing: Lax–Milgram for the inner product is the Riesz
representation theorem, and no boundedness of `Ω` is needed. -/
theorem laplaceForm_eq_innerSL : laplaceForm Ω = innerSL ℝ := by
  ext u v
  rw [laplaceForm_apply_inner, innerSL_apply_apply, Submodule.coe_inner, PiLp.inner_apply,
    MultiIndexLE.sum_univ_one, add_comm]
  rfl

/-- `laplaceForm Ω u v = ⟪u, v⟫_{H^1(Ω)}`. -/
theorem laplaceForm_apply_eq_inner (u v : SobolevEuclidean N 1 2 Ω) :
    laplaceForm Ω u v = ⟪u, v⟫_ℝ := by
  rw [laplaceForm_eq_innerSL]
  rfl

/-- The form of `-Δ + 1` is coercive with constant `1`: `a(v, v) = ‖v‖²`. -/
theorem laplaceForm_isCoerciveWith_one : (laplaceForm Ω).IsCoerciveWith 1 := by
  rw [laplaceForm_eq_innerSL]
  exact SesqForm.innerSL_isCoerciveWith

/-- The form of `-Δ + 1` is symmetric. -/
theorem laplaceForm_isHermitian : (laplaceForm Ω).IsHermitian := by
  rw [laplaceForm_eq_innerSL]
  exact SesqForm.innerSL_isHermitian

/-- The form of `-Δ + 1` is bounded with constant `1`. -/
theorem laplaceForm_isBoundedWith_one : (laplaceForm Ω).IsBoundedWith 1 := fun u v ↦ by
  rw [laplaceForm_apply_eq_inner, one_mul]
  exact norm_inner_le_norm u v

/-! ### The load functional -/

/-- **The load functional** `v ↦ ∫_Ω f v = ⟪f, v⟫_{L²(Ω)}` for `f ∈ L²(Ω)`, as a continuous linear
functional on `H^1(Ω)`; the twin of `EllipticInterval.load`. -/
def load (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    SobolevEuclidean N 1 2 Ω →L[ℝ] ℝ :=
  (innerSL ℝ f).comp
    (SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume)

/-- The load functional is the `L²` inner product with `f`. -/
theorem load_apply_inner (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (v : SobolevEuclidean N 1 2 Ω) : load Ω f v = ⟪f, SobolevMultiIndex.weakDeriv v 0⟫_ℝ :=
  rfl

/-- The load functional is the integral `∫_Ω f v`. -/
theorem load_apply (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (v : SobolevEuclidean N 1 2 Ω) :
    load Ω f v = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), f x * SobolevMultiIndex.fn v x := by
  rw [load_apply_inner, L2.inner_eq_integral_mul]
  rfl

/-- `|∫_Ω f v| ≤ ‖f‖₂ ‖v‖₂`. -/
theorem abs_load_le (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (v : SobolevEuclidean N 1 2 Ω) :
    |load Ω f v| ≤ ‖f‖ * ‖SobolevMultiIndex.weakDeriv v 0‖ := by
  rw [load_apply_inner]
  exact abs_real_inner_le_norm _ _

/-- The load functional has norm at most `‖f‖₂`. -/
theorem norm_load_le (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ‖load Ω f‖ ≤ ‖f‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v ↦ ?_
  rw [Real.norm_eq_abs]
  exact (abs_load_le Ω f v).trans (by gcongr; exact SobolevMultiIndex.norm_weakDeriv_le v 0)

/-- **The load restricted to a subspace `K` of `H^1(Ω)`, as a continuous linear map of `f`**:
`loadL Ω K f v = ∫_Ω f v` for `v ∈ K`. It is what makes the solution operator of the weak
Dirichlet problem a continuous linear map of `f`. -/
def loadL (K : Submodule ℝ (SobolevEuclidean N 1 2 Ω)) :
    Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →L[ℝ] (K →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.compL ℝ K
      (Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) ℝ).flip
    ((SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume).comp
      K.subtypeL)).comp (innerSL ℝ)

/-- `loadL Ω K f v = ⟪f, v⟫_{L²(Ω)}`. -/
theorem loadL_apply (K : Submodule ℝ (SobolevEuclidean N 1 2 Ω))
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) (v : K) :
    loadL Ω K f v = ⟪f, SobolevMultiIndex.weakDeriv (v : SobolevEuclidean N 1 2 Ω) 0⟫_ℝ :=
  rfl

/-- `loadL Ω K f` is the restriction of `load Ω f` to `K`. -/
theorem loadL_eq (K : Submodule ℝ (SobolevEuclidean N 1 2 Ω))
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    loadL Ω K f = (load Ω f).comp K.subtypeL :=
  rfl


/-! ### Theorem 9.21 (Dirichlet's principle) and Proposition 9.24 (the Neumann problem) -/

/-- **Theorem 9.21 (Dirichlet, Riemann, Poincaré, Hilbert): existence and uniqueness of the weak
solution of the Dirichlet problem** `-Δu + u = f` in `Ω`, `u = 0` on `∂Ω`, for every open
`Ω ⊆ ℝ^N` and every `f ∈ L²(Ω)`: exactly one `u ∈ H^1_0(Ω)` satisfies
`∫_Ω ∇u · ∇v + ∫_Ω u v = ∫_Ω f v` for all `v ∈ H^1_0(Ω)` (the weak formulation (32)). Lax–Milgram
on `H^1_0(Ω)` for the form of `-Δ + 1`, which is the inner product of `H^1(Ω)`; no boundedness of
`Ω` is needed, which is what Example 5 (a), (b) use ([brezis2011functional] Theorem 9.21). -/
theorem existsUnique_isGalerkinSolution_laplace
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ∃! u, IsGalerkinSolution (laplaceForm Ω) (load Ω f) (SobolevEuclideanZero N 1 2 Ω) u :=
  IsGalerkinSolution.existsUnique one_pos (laplaceForm_isCoerciveWith_one Ω)

/-- **The stability estimate `‖u‖_{H^1(Ω)} ≤ ‖f‖_{L²(Ω)}`** for a weak solution of the Dirichlet
problem for `-Δ + 1` in any subspace `K` (in particular `H^1_0(Ω)`), which the proof of
[brezis2011functional] Theorem 9.25 quotes as "`‖u‖_{H^1} ≤ ‖f‖_{L²}` by (48)". -/
theorem norm_le_of_isGalerkinSolution_laplace
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    {K : Submodule ℝ (SobolevEuclidean N 1 2 Ω)} {u : SobolevEuclidean N 1 2 Ω}
    (hu : IsGalerkinSolution (laplaceForm Ω) (load Ω f) K u) : ‖u‖ ≤ ‖f‖ := by
  have hcoer : ((laplaceForm Ω).restrict K).IsCoerciveWith 1 := fun v ↦
    laplaceForm_isCoerciveWith_one Ω (v : SobolevEuclidean N 1 2 Ω)
  have h := ((laplaceForm Ω).restrict K).norm_le_of_forall_apply_eq ((load Ω f).comp K.subtypeL)
    one_pos hcoer (u := ⟨u, hu.1⟩) fun v ↦ hu.2 v v.2
  rw [div_one] at h
  calc ‖u‖ = ‖(⟨u, hu.1⟩ : K)‖ := rfl
    _ ≤ ‖(load Ω f).comp K.subtypeL‖ := h
    _ ≤ ‖load Ω f‖ * ‖K.subtypeL‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖f‖ * 1 :=
        mul_le_mul (norm_load_le Ω f) (Submodule.norm_subtypeL_le K) (norm_nonneg _)
          (norm_nonneg _)
    _ = ‖f‖ := mul_one _

/-- **The energy of the Dirichlet problem** for `-Δ + 1`:
`E(v) = ½ ∫_Ω (|∇v|² + v²) - ∫_Ω f v`, the functional of [brezis2011functional] Theorem 9.21. -/
theorem energy_laplace_apply (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (v : SobolevEuclidean N 1 2 Ω) :
    (laplaceForm Ω).energy (load Ω f) v
      = (1 / 2 : ℝ) * (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          ((∑ i : Fin N, SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x
            * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x)
            + SobolevMultiIndex.fn v x * SobolevMultiIndex.fn v x))
        - ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), f x * SobolevMultiIndex.fn v x := by
  rw [SesqForm.energy, laplaceForm_apply, load_apply]
  simp only [RCLike.re_to_real]

/-- **Theorem 9.21, Dirichlet's principle**: `u ∈ H^1_0(Ω)` is the weak solution of the Dirichlet
problem for `-Δ + 1` if and only if it minimizes the energy
`E(v) = ½ ∫_Ω (|∇v|² + v²) - ∫_Ω f v` over `H^1_0(Ω)` (`Elliptic.energy_laplace_apply`). The
form is symmetric and coercive, so this is `SesqForm.isMinOn_energy_iff`
([brezis2011functional] Theorem 9.21, second half). -/
theorem isMinOn_energy_iff_isGalerkinSolution_laplace
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    {u : SobolevEuclidean N 1 2 Ω} (hu : u ∈ SobolevEuclideanZero N 1 2 Ω) :
    IsMinOn ((laplaceForm Ω).energy (load Ω f)) (SobolevEuclideanZero N 1 2 Ω) u
      ↔ IsGalerkinSolution (laplaceForm Ω) (load Ω f) (SobolevEuclideanZero N 1 2 Ω) u := by
  rw [SesqForm.isMinOn_energy_iff (load Ω f) (laplaceForm_isHermitian Ω) one_pos
    (laplaceForm_isCoerciveWith_one Ω) _ hu]
  exact ⟨fun h ↦ ⟨hu, h⟩, fun h ↦ h.2⟩

/-- `H^1(Ω)`, as the top submodule of itself, is complete: the trial space of the Neumann
problem. -/
theorem completeSpace_top : CompleteSpace (⊤ : Submodule ℝ (SobolevEuclidean N 1 2 Ω)) :=
  (isClosed_univ (X := SobolevEuclidean N 1 2 Ω)).completeSpace_coe

/-- **Proposition 9.24 (the homogeneous Neumann problem): existence and uniqueness of the weak
solution** of `-Δu + u = f` in `Ω`, `∂u/∂n = 0` on `∂Ω`, for every open `Ω ⊆ ℝ^N` and
`f ∈ L²(Ω)`: exactly one `u ∈ H^1(Ω)` satisfies `∫_Ω ∇u · ∇v + ∫_Ω u v = ∫_Ω f v` for all
`v ∈ H^1(Ω)` (the weak formulation (45)). Lax–Milgram on `H^1(Ω)`; since the form is the inner
product this is the Riesz representation of the load. The book's hypothesis "`Ω` bounded of
class `C^1`" is needed only for the passage between the classical and the weak formulations
(Green's formula), not for this proposition ([brezis2011functional] Proposition 9.24; Example 5
(a) and (c) are the cases `Ω = ℝ^N` and `Ω = ℝ^N_+`). -/
theorem existsUnique_isGalerkinSolution_neumann
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ∃! u, IsGalerkinSolution (laplaceForm Ω) (load Ω f) ⊤ u :=
  haveI := completeSpace_top Ω
  IsGalerkinSolution.existsUnique one_pos (laplaceForm_isCoerciveWith_one Ω)

/-- **Proposition 9.24, Dirichlet's principle for the Neumann problem**: `u ∈ H^1(Ω)` is the weak
solution of the Neumann problem for `-Δ + 1` if and only if it minimizes the energy
`E(v) = ½ ∫_Ω (|∇v|² + v²) - ∫_Ω f v` over `H^1(Ω)`. -/
theorem isMinOn_energy_iff_isGalerkinSolution_neumann
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (u : SobolevEuclidean N 1 2 Ω) :
    IsMinOn ((laplaceForm Ω).energy (load Ω f)) univ u
      ↔ IsGalerkinSolution (laplaceForm Ω) (load Ω f) ⊤ u := by
  have h := SesqForm.isMinOn_energy_iff (load Ω f) (laplaceForm_isHermitian Ω) one_pos
    (laplaceForm_isCoerciveWith_one Ω) ⊤ (Submodule.mem_top (x := u))
  rw [Submodule.top_coe] at h
  rw [h]
  exact ⟨fun h ↦ ⟨Submodule.mem_top, h⟩, fun h ↦ h.2⟩

/-! ### Proposition 9.22: inhomogeneous Dirichlet data -/

/-- **The admissible set of the inhomogeneous Dirichlet problem**,
`K = {v ∈ H^1(Ω) : v − g̃ ∈ H^1_0(Ω)}` of [brezis2011functional] §9.5, Example 2: the functions of
`H^1(Ω)` with the boundary values of `g̃`. -/
def admissibleSet (g : SobolevEuclidean N 1 2 Ω) : Set (SobolevEuclidean N 1 2 Ω) :=
  {v | v - g ∈ SobolevEuclideanZero N 1 2 Ω}

/-- Membership of the admissible set, unfolded. -/
theorem mem_admissibleSet_iff {g v : SobolevEuclidean N 1 2 Ω} :
    v ∈ admissibleSet Ω g ↔ v - g ∈ SobolevEuclideanZero N 1 2 Ω :=
  Iff.rfl

/-- `g̃ ∈ K`. -/
theorem self_mem_admissibleSet (g : SobolevEuclidean N 1 2 Ω) : g ∈ admissibleSet Ω g := by
  rw [mem_admissibleSet_iff, sub_self]
  exact Submodule.zero_mem _

/-- `K` is nonempty. -/
theorem admissibleSet_nonempty (g : SobolevEuclidean N 1 2 Ω) : (admissibleSet Ω g).Nonempty :=
  ⟨g, self_mem_admissibleSet Ω g⟩

/-- `K` is closed: the preimage of the closed subspace `H^1_0(Ω)` under `v ↦ v − g̃`. -/
theorem isClosed_admissibleSet (g : SobolevEuclidean N 1 2 Ω) : IsClosed (admissibleSet Ω g) :=
  SobolevMultiIndexZero.isClosed.preimage (continuous_id.sub continuous_const)

/-- `K` is convex: a translate of a subspace. -/
theorem convex_admissibleSet (g : SobolevEuclidean N 1 2 Ω) : Convex ℝ (admissibleSet Ω g) := by
  intro u hu v hv a b ha hb hab
  rw [mem_admissibleSet_iff] at hu hv ⊢
  have : a • u + b • v - g = a • (u - g) + b • (v - g) := by
    rw [smul_sub, smul_sub, ← add_sub_add_comm, ← add_smul, hab, one_smul]
  rw [this]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hu) (Submodule.smul_mem _ _ hv)

/-- **`K` depends only on the boundary values of `g̃`**: two extensions `g̃`, `g̃'` whose
difference lies in `H^1_0(Ω)` define the same admissible set ("`K` is independent of the choice of
`g̃`", [brezis2011functional] §9.5, Example 2; that `g̃ − g̃' ∈ H^1_0(Ω)` when both are continuous
on `closure Ω` and agree on `∂Ω` is Theorem 9.17). -/
theorem admissibleSet_eq_of_sub_mem {g g' : SobolevEuclidean N 1 2 Ω}
    (h : g - g' ∈ SobolevEuclideanZero N 1 2 Ω) : admissibleSet Ω g = admissibleSet Ω g' := by
  ext v
  rw [mem_admissibleSet_iff, mem_admissibleSet_iff]
  constructor
  · intro hv
    have := Submodule.add_mem _ hv h
    rwa [sub_add_sub_cancel] at this
  · intro hv
    have := Submodule.sub_mem _ hv h
    rwa [sub_sub_sub_cancel_right] at this

/-- **The weak formulation (34) of the inhomogeneous Dirichlet problem is the variational
inequality (35)**, [brezis2011functional] §9.5, proof of Proposition 9.22: for `u ∈ K`,
`a(u, v) = ⟨f, v⟩` for all `v ∈ H^1_0(Ω)` if and only if `⟨f, v − u⟩ ≤ a(u, v − u)` for all
`v ∈ K`. One direction is the equality; conversely `v = u ± w` with `w ∈ H^1_0(Ω)` gives (34).
Stated for any bilinear form `a` and functional `ℓ`. -/
theorem isWeakSolution_inhomogeneous_iff_forall_le (a : SesqForm ℝ (SobolevEuclidean N 1 2 Ω))
    (ℓ : SobolevEuclidean N 1 2 Ω →L[ℝ] ℝ) {g u : SobolevEuclidean N 1 2 Ω}
    (hu : u ∈ admissibleSet Ω g) :
    (∀ v ∈ SobolevEuclideanZero N 1 2 Ω, a u v = ℓ v)
      ↔ ∀ v ∈ admissibleSet Ω g, ℓ (v - u) ≤ a u (v - u) := by
  rw [mem_admissibleSet_iff] at hu
  constructor
  · intro h v hv
    rw [mem_admissibleSet_iff] at hv
    have hvu : v - u ∈ SobolevEuclideanZero N 1 2 Ω := by
      have := Submodule.sub_mem _ hv hu
      rwa [sub_sub_sub_cancel_right] at this
    exact (h _ hvu).ge
  · intro h w hw
    have h1 := h (u + w) (by
      rw [mem_admissibleSet_iff, add_sub_right_comm]
      exact Submodule.add_mem _ hu hw)
    have h2 := h (u - w) (by
      rw [mem_admissibleSet_iff, sub_right_comm]
      exact Submodule.sub_mem _ hu hw)
    rw [add_sub_cancel_left] at h1
    rw [sub_sub_cancel_left, map_neg, map_neg, neg_le_neg_iff] at h2
    exact le_antisymm h2 h1

/-- **Proposition 9.22 (inhomogeneous Dirichlet condition): existence and uniqueness.** For
`Ω ⊆ ℝ^N` open, `g̃ ∈ H^1(Ω)` and `f ∈ L²(Ω)` there is exactly one `u ∈ K = g̃ + H^1_0(Ω)` with
`∫_Ω ∇u · ∇v + ∫_Ω u v = ∫_Ω f v` for all `v ∈ H^1_0(Ω)` (the weak formulation (34)). The book
argues through the variational inequality (35) and Stampacchia's theorem; the short proof is
`u = g̃ + w` with `w ∈ H^1_0(Ω)` the Galerkin solution for the load `⟨f, ·⟩ − a(g̃, ·)`, and
uniqueness is the coercivity of the form on the difference of two solutions, which lies in
`H^1_0(Ω)` ([brezis2011functional] Proposition 9.22). -/
theorem existsUnique_isWeakSolution_inhomogeneous (g : SobolevEuclidean N 1 2 Ω)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ∃! u, u ∈ admissibleSet Ω g ∧
      ∀ v ∈ SobolevEuclideanZero N 1 2 Ω, laplaceForm Ω u v = load Ω f v := by
  obtain ⟨w, ⟨hwK, hw⟩, -⟩ := IsGalerkinSolution.existsUnique (a := laplaceForm Ω)
    (ℓ := load Ω f - laplaceForm Ω g) (K := SobolevEuclideanZero N 1 2 Ω) one_pos
    (laplaceForm_isCoerciveWith_one Ω)
  refine ⟨g + w, ⟨?_, fun v hv ↦ ?_⟩, ?_⟩
  · rw [mem_admissibleSet_iff, add_sub_cancel_left]
    exact hwK
  · have e2 : laplaceForm Ω (g + w) = laplaceForm Ω g + laplaceForm Ω w := map_add _ _ _
    rw [e2, add_apply, hw v hv, sub_apply]
    ring
  · rintro u ⟨huK, hu⟩
    rw [mem_admissibleSet_iff] at huK
    have hdiff : u - (g + w) ∈ SobolevEuclideanZero N 1 2 Ω := by
      have := Submodule.sub_mem _ huK hwK
      rwa [sub_sub] at this
    have e1 : laplaceForm Ω (u - (g + w)) = laplaceForm Ω u - laplaceForm Ω (g + w) :=
      map_sub _ _ _
    have e2 : laplaceForm Ω (g + w) = laplaceForm Ω g + laplaceForm Ω w := map_add _ _ _
    have h0 : laplaceForm Ω (u - (g + w)) (u - (g + w)) = 0 := by
      rw [e1, sub_apply, hu _ hdiff, e2, add_apply, hw _ hdiff, sub_apply]
      ring
    rw [laplaceForm_apply_eq_inner, real_inner_self_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero,
      sub_eq_zero] at h0
    exact h0

/-- **Proposition 9.22, the minimization**: `u ∈ K` is the weak solution of the inhomogeneous
Dirichlet problem if and only if it minimizes `E(v) = ½ ∫_Ω (|∇v|² + v²) − ∫_Ω f v` over `K`
(`SesqForm.isMinOn_energy_iff_forall_le` on the convex set `K` and the equivalence (34) ⇔ (35)). -/
theorem isMinOn_energy_iff_isWeakSolution_inhomogeneous
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    {g u : SobolevEuclidean N 1 2 Ω} (hu : u ∈ admissibleSet Ω g) :
    IsMinOn ((laplaceForm Ω).energy (load Ω f)) (admissibleSet Ω g) u
      ↔ ∀ v ∈ SobolevEuclideanZero N 1 2 Ω, laplaceForm Ω u v = load Ω f v := by
  rw [SesqForm.isMinOn_energy_iff_forall_le (laplaceForm_isHermitian Ω) (load Ω f) one_pos
    (laplaceForm_isCoerciveWith_one Ω) (convex_admissibleSet Ω g) hu,
    isWeakSolution_inhomogeneous_iff_forall_le Ω (laplaceForm Ω) (load Ω f) hu]


/-! ### The general second-order form (41) with `L^∞` coefficients -/

/-- **The ellipticity condition (36)** of [brezis2011functional] §9.5, Example 3, for `L^∞`
coefficients `A i j`: `0 < α`, and for almost every `x ∈ Ω`, `α ‖ξ‖² ≤ ∑ᵢⱼ A i j x ξᵢ ξⱼ` for every
`ξ ∈ ℝ^N`. Stated almost everywhere because the coefficients are classes; for coefficients
continuous on `Ω` the pointwise condition implies it. -/
def IsUniformlyElliptic
    (A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (α : ℝ) : Prop :=
  0 < α ∧ ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
    ∀ ξ : EuclideanSpace ℝ (Fin N), α * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, A i j x * ξ i * ξ j

/-- **The general second-order form (41)** of [brezis2011functional] §9.5:
`a(u, v) = ∑ᵢⱼ ∫_Ω a_ij ∂ᵢu ∂ⱼv + ∑ᵢ ∫_Ω a_i ∂ᵢu v + ∫_Ω a₀ u v` on `H^1(Ω)`, for `L^∞(Ω)`
coefficients `A i j = a_ij`, `a₁ i = a_i`, `a₀`. The form (38) of the symmetric problem (37) is
the case `a₁ = 0`. -/
def generalForm
    (A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (a₁ : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    SesqForm ℝ (SobolevEuclidean N 1 2 Ω) :=
  (∑ i : Fin N, ∑ j : Fin N,
      pairing Ω (mulL Ω (A i j)) (MultiIndexLE.single i) (MultiIndexLE.single j))
    + (∑ i : Fin N, pairing Ω (mulL Ω (a₁ i)) (MultiIndexLE.single i) 0)
    + pairing Ω (mulL Ω a₀) 0 0

section GeneralForm

variable (A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
  (a₁ : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
  (a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))

/-- The general form as a sum of `L²` inner products. -/
theorem generalForm_apply_inner (u v : SobolevEuclidean N 1 2 Ω) :
    generalForm Ω A a₁ a₀ u v
      = (∑ i : Fin N, ∑ j : Fin N, ⟪mulL Ω (A i j) (SobolevMultiIndex.weakDeriv u
          (MultiIndexLE.single i)), SobolevMultiIndex.weakDeriv v (MultiIndexLE.single j)⟫_ℝ)
        + (∑ i : Fin N, ⟪mulL Ω (a₁ i) (SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i)),
          SobolevMultiIndex.weakDeriv v 0⟫_ℝ)
        + ⟪mulL Ω a₀ (SobolevMultiIndex.weakDeriv u 0), SobolevMultiIndex.weakDeriv v 0⟫_ℝ := by
  simp only [generalForm, add_apply, sum_apply, pairing_apply]

/-- **The general form is the integral (41)**:
`a(u, v) = ∫_Ω (∑ᵢⱼ a_ij ∂ᵢu ∂ⱼv + ∑ᵢ a_i ∂ᵢu v + a₀ u v)`. -/
theorem generalForm_apply (u v : SobolevEuclidean N 1 2 Ω) :
    generalForm Ω A a₁ a₀ u v = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      ((∑ i : Fin N, ∑ j : Fin N, A i j x * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
          * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single j) x)
        + (∑ i : Fin N, a₁ i x * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
          * SobolevMultiIndex.fn v x)
        + a₀ x * SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x) := by
  have h1 : ∀ i j, Integrable (fun x ↦ A i j x
      * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
      * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single j) x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := fun i j ↦ integrable_mul_mul Ω _ _ _
  have h2 : ∀ i, Integrable (fun x ↦ a₁ i x
      * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
      * SobolevMultiIndex.weakDeriv v 0 x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := fun i ↦ integrable_mul_mul Ω _ _ _
  have h3 : Integrable (fun x ↦ a₀ x * SobolevMultiIndex.weakDeriv u 0 x
      * SobolevMultiIndex.weakDeriv v 0 x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := integrable_mul_mul Ω _ _ _
  have e1 : ∀ i, ∑ j, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), A i j x
      * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
      * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single j) x
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), ∑ j, A i j x
        * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
        * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single j) x := fun i ↦
    (integral_finsetSum _ fun j _ ↦ h1 i j).symm
  have e2 : ∑ i, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), ∑ j, A i j x
      * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
      * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single j) x
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), ∑ i, ∑ j, A i j x
        * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
        * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single j) x :=
    (integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ h1 i j).symm
  have e3 : ∑ i, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), a₁ i x
      * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
      * SobolevMultiIndex.weakDeriv v 0 x
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), ∑ i, a₁ i x
        * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
        * SobolevMultiIndex.weakDeriv v 0 x :=
    (integral_finsetSum _ fun i _ ↦ h2 i).symm
  have e4 : (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), ∑ i, ∑ j, A i j x
      * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
      * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single j) x)
      + (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), ∑ i, a₁ i x
        * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
        * SobolevMultiIndex.weakDeriv v 0 x)
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), ((∑ i, ∑ j, A i j x
        * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
        * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single j) x)
        + ∑ i, a₁ i x * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
          * SobolevMultiIndex.weakDeriv v 0 x) :=
    (integral_add (integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ h1 i j)
      (integrable_finsetSum _ fun i _ ↦ h2 i)).symm
  have e5 : (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), ((∑ i, ∑ j, A i j x
      * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
      * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single j) x)
      + ∑ i, a₁ i x * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
        * SobolevMultiIndex.weakDeriv v 0 x))
      + (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), a₀ x * SobolevMultiIndex.weakDeriv u 0 x
        * SobolevMultiIndex.weakDeriv v 0 x)
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), (((∑ i, ∑ j, A i j x
        * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
        * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single j) x)
        + ∑ i, a₁ i x * SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
          * SobolevMultiIndex.weakDeriv v 0 x)
        + a₀ x * SobolevMultiIndex.weakDeriv u 0 x * SobolevMultiIndex.weakDeriv v 0 x) :=
    (integral_add ((integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ h1 i j).add
      (integrable_finsetSum _ fun i _ ↦ h2 i)) h3).symm
  rw [generalForm_apply_inner]
  simp only [inner_mulL_eq_integral]
  simp only [e1]
  rw [e2, e3, e4, e5]
  rfl

/-- **The general form is bounded**, with constant `∑ᵢⱼ ‖a_ij‖_∞ + ∑ᵢ ‖a_i‖_∞ + ‖a₀‖_∞`. -/
theorem generalForm_isBoundedWith :
    (generalForm Ω A a₁ a₀).IsBoundedWith ((∑ i, ∑ j, ‖A i j‖) + ∑ i, ‖a₁ i‖ + ‖a₀‖) := by
  intro u v
  rw [Real.norm_eq_abs, generalForm_apply_inner]
  have key : ∀ (a : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
      (α β : MultiIndexLE (Fin N) 1),
      |⟪mulL Ω a (SobolevMultiIndex.weakDeriv u α), SobolevMultiIndex.weakDeriv v β⟫_ℝ|
        ≤ ‖a‖ * ‖u‖ * ‖v‖ := fun a α β ↦ by
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖mulL Ω a (SobolevMultiIndex.weakDeriv u α)‖ * ‖SobolevMultiIndex.weakDeriv v β‖
        ≤ ‖a‖ * ‖SobolevMultiIndex.weakDeriv u α‖ * ‖SobolevMultiIndex.weakDeriv v β‖ := by
          gcongr; exact norm_mulL_apply_le Ω a _
      _ ≤ ‖a‖ * ‖u‖ * ‖v‖ := by
          gcongr
          · exact SobolevMultiIndex.norm_weakDeriv_le u α
          · exact SobolevMultiIndex.norm_weakDeriv_le v β
  calc |(∑ i, ∑ j, ⟪mulL Ω (A i j) (SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i)),
          SobolevMultiIndex.weakDeriv v (MultiIndexLE.single j)⟫_ℝ)
        + (∑ i, ⟪mulL Ω (a₁ i) (SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i)),
          SobolevMultiIndex.weakDeriv v 0⟫_ℝ)
        + ⟪mulL Ω a₀ (SobolevMultiIndex.weakDeriv u 0), SobolevMultiIndex.weakDeriv v 0⟫_ℝ|
      ≤ (∑ i, ∑ j, ‖A i j‖ * ‖u‖ * ‖v‖) + (∑ i, ‖a₁ i‖ * ‖u‖ * ‖v‖) + ‖a₀‖ * ‖u‖ * ‖v‖ := by
        refine (abs_add_three _ _ _).trans (add_le_add (add_le_add ?_ ?_) (key _ _ _))
        · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ key _ _ _)
        · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ key _ _ _)
    _ = ((∑ i, ∑ j, ‖A i j‖) + ∑ i, ‖a₁ i‖ + ‖a₀‖) * ‖u‖ * ‖v‖ := by
        rw [add_mul, add_mul, add_mul, add_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul,
          Finset.sum_mul]
        congr 2
        exact Finset.sum_congr rfl fun i _ ↦ by rw [Finset.sum_mul, Finset.sum_mul]

/-- Multiplication by the zero coefficient is the zero operator. -/
@[simp]
theorem mulL_zero : mulL Ω 0 = 0 := map_zero _

/-- A pairing through the zero operator is the zero form. -/
@[simp]
theorem pairing_zero (α β : MultiIndexLE (Fin N) 1) : pairing Ω 0 α β = 0 :=
  ContinuousLinearMap.ext fun u ↦ ContinuousLinearMap.ext fun v ↦ by
    rw [pairing_apply]
    simp

/-- The symmetric-problem form (38) is symmetric when the matrix `a_ij` is. -/
theorem generalForm_isHermitian_of_symm (hA : ∀ i j, A i j = A j i) :
    (generalForm Ω A 0 a₀).IsHermitian := fun u v ↦ by
  rw [conj_trivial, generalForm_apply_inner, generalForm_apply_inner]
  simp only [Pi.zero_apply, mulL_zero, zero_apply, inner_zero_left,
    Finset.sum_const_zero, add_zero, inner_mulL_eq_integral]
  rw [Finset.sum_comm]
  congr 1
  · refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hA i j]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
  · exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)

end GeneralForm



/-! ### Lax–Milgram on a subspace -/

/-- **Existence and uniqueness of the Galerkin solution when the form is coercive on the trial
space only**: the variant of `IsGalerkinSolution.existsUnique` whose coercivity hypothesis is on
the restriction `a.restrict K` of the form to the complete subspace `K` rather than on the whole
space, which is the situation of a form coercive on `H^1_0(Ω)` by Poincaré's inequality but not
on `H^1(Ω)`. Belongs beside `IsGalerkinSolution.existsUnique` in
`Numlib/Variational/Galerkin.lean`. -/
theorem _root_.IsGalerkinSolution.existsUnique_of_restrict {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {a : SesqForm ℝ V} {ℓ : V →L[ℝ] ℝ} {K : Submodule ℝ V} {c : ℝ}
    (hc : 0 < c) (ha : (a.restrict K).IsCoerciveWith c) [CompleteSpace K] :
    ∃! u, IsGalerkinSolution a ℓ K u := by
  obtain ⟨w, hw, hwu⟩ := SesqForm.laxMilgram (a.restrict K) (ℓ.comp K.subtypeL) hc ha
  refine ⟨(w : V), ⟨w.2, fun v hv ↦ hw ⟨v, hv⟩⟩, ?_⟩
  rintro y ⟨hyK, hy⟩
  exact congrArg Subtype.val (hwu ⟨y, hyK⟩ fun z ↦ hy (z : V) z.2)

/-- **Dirichlet's principle on a subspace when the form is coercive on that subspace only**: for
a form `a` whose restriction to the complete subspace `K` is Hermitian and coercive, `u ∈ K`
minimizes the energy `a.energy ℓ` over `K` if and only if `a u v = ℓ v` for all `v ∈ K`. The
variant of `SesqForm.isMinOn_energy_iff` with hypotheses on `a.restrict K`; belongs beside it in
`Numlib/Variational/LaxMilgram.lean`. -/
theorem _root_.SesqForm.isMinOn_energy_iff_of_restrict {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {a : SesqForm ℝ V} (ℓ : V →L[ℝ] ℝ) {K : Submodule ℝ V}
    (ha : (a.restrict K).IsHermitian) {c : ℝ} (hc : 0 < c)
    (hcoer : (a.restrict K).IsCoerciveWith c) {u : V} (hu : u ∈ K) :
    IsMinOn (a.energy ℓ) K u ↔ ∀ v ∈ K, a u v = ℓ v := by
  have key := SesqForm.isMinOn_energy_iff (K := ⊤) (ℓ.comp K.subtypeL) ha hc hcoer (u := ⟨u, hu⟩)
    Submodule.mem_top
  rw [Submodule.top_coe, isMinOn_iff] at key
  rw [isMinOn_iff]
  have he : ∀ w : K, (a.restrict K).energy (ℓ.comp K.subtypeL) w = a.energy ℓ (w : V) :=
    fun w ↦ rfl
  simp only [he] at key
  constructor
  · intro hmin v hv
    exact key.1 (fun w _ ↦ hmin w w.2) ⟨v, hv⟩ Submodule.mem_top
  · intro h w hw
    exact key.2 (fun v _ ↦ h v v.2) ⟨w, hw⟩ (mem_univ _)

/-! ### Ellipticity, Gårding's inequality and coercivity on `H^1_0(Ω)` -/

section Ellipticity

variable {A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {a₁ : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))} {α : ℝ}

/-- **The principal part of the form is bounded below by `α ∫_Ω |∇v|²`** under the ellipticity
condition (36): `∑ᵢⱼ ∫_Ω a_ij ∂ᵢv ∂ⱼv ≥ α ∑ᵢ ‖∂ᵢv‖₂²`, the pointwise inequality applied to
`ξ = ∇v(x)` under the integral. -/
theorem sum_inner_mulL_ge (hA : IsUniformlyElliptic Ω A α) (v : SobolevEuclidean N 1 2 Ω) :
    α * ∑ i : Fin N, ‖SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i)‖ ^ 2
      ≤ ∑ i : Fin N, ∑ j : Fin N, ⟪mulL Ω (A i j) (SobolevMultiIndex.weakDeriv v
        (MultiIndexLE.single i)), SobolevMultiIndex.weakDeriv v (MultiIndexLE.single j)⟫_ℝ := by
  have hint : ∀ i j, Integrable (fun x ↦ A i j x
      * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x
      * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single j) x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := fun i j ↦ integrable_mul_mul Ω _ _ _
  have hsq : ∀ i, Integrable (fun x ↦ SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x
      * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := fun i ↦
    (L2.integrable_inner (𝕜 := ℝ) (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i))
      (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i))).congr
      (Eventually.of_forall fun x ↦ by simp [sq])
  simp only [inner_mulL_eq_integral]
  have e : ∑ i : Fin N, ‖SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i)‖ ^ 2
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        ∑ i : Fin N, SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x
          * SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x := by
    rw [integral_finsetSum _ fun i _ ↦ hsq i]
    exact Finset.sum_congr rfl fun i _ ↦ by
      rw [← real_inner_self_eq_norm_sq, L2.inner_eq_integral_mul]
  rw [e, ← integral_const_mul]
  simp only [← integral_finsetSum _ fun j _ ↦ hint _ j]
  rw [← integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j]
  refine integral_mono_ae ((integrable_finsetSum _ fun i _ ↦ hsq i).const_mul α)
    (integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j) ?_
  filter_upwards [hA.2] with x hx
  have h := hx (WithLp.toLp 2 fun i ↦ SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) x)
  rw [EuclideanSpace.real_norm_sq_eq] at h
  simpa [sq] using h

/-- **The lower bound of the general form on the diagonal** under the ellipticity condition (36):
`a(v, v) ≥ α ∑ᵢ ‖∂ᵢv‖₂² − (∑ᵢ ‖a_i‖_∞ ‖∂ᵢv‖₂) ‖v‖₂ − ‖a₀‖_∞ ‖v‖₂²`. -/
theorem generalForm_self_ge (hA : IsUniformlyElliptic Ω A α) (v : SobolevEuclidean N 1 2 Ω) :
    α * (∑ i : Fin N, ‖SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i)‖ ^ 2)
      - (∑ i : Fin N, ‖a₁ i‖ * ‖SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i)‖)
        * ‖SobolevMultiIndex.weakDeriv v 0‖
      - ‖a₀‖ * ‖SobolevMultiIndex.weakDeriv v 0‖ ^ 2
      ≤ generalForm Ω A a₁ a₀ v v := by
  rw [generalForm_apply_inner]
  have h1 := sum_inner_mulL_ge Ω hA v
  have h2 : -((∑ i : Fin N, ‖a₁ i‖ * ‖SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i)‖)
      * ‖SobolevMultiIndex.weakDeriv v 0‖)
      ≤ ∑ i : Fin N, ⟪mulL Ω (a₁ i) (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i)),
        SobolevMultiIndex.weakDeriv v 0⟫_ℝ := by
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    refine le_trans ?_ (neg_abs_le (⟪mulL Ω (a₁ i)
      (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i)), SobolevMultiIndex.weakDeriv v 0⟫_ℝ))
    refine neg_le_neg ((abs_real_inner_le_norm _ _).trans ?_)
    exact mul_le_mul_of_nonneg_right (norm_mulL_apply_le Ω _ _)
      (norm_nonneg (SobolevMultiIndex.weakDeriv v 0))
  have h3 : -(‖a₀‖ * ‖SobolevMultiIndex.weakDeriv v 0‖ ^ 2)
      ≤ ⟪mulL Ω a₀ (SobolevMultiIndex.weakDeriv v 0), SobolevMultiIndex.weakDeriv v 0⟫_ℝ := by
    refine le_trans ?_ (neg_abs_le (⟪mulL Ω a₀ (SobolevMultiIndex.weakDeriv v 0),
      SobolevMultiIndex.weakDeriv v 0⟫_ℝ))
    refine neg_le_neg ((abs_real_inner_le_norm _ _).trans ?_)
    rw [sq, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (norm_mulL_apply_le Ω _ _) (norm_nonneg _)
  linarith

/-- **Gårding's inequality** for the form (41) with `L^∞` coefficients: under the ellipticity
condition (36) with constant `α`, the form `a(u, v) + λ ∫_Ω u v` is coercive on `H^1(Ω)` with
constant `α / 2` for the explicit shift `λ = (∑ᵢ ‖a_i‖_∞)² / (2α) + ‖a₀‖_∞ + α / 2`:
`(α/2) ‖v‖²_{H^1} ≤ a(v, v) + λ ‖v‖₂²`. From `Elliptic.generalForm_self_ge` and
`c √D ‖v‖₂ ≤ (α/2) D + (c²/(2α)) ‖v‖₂²` with `D = ∑ᵢ ‖∂ᵢv‖₂²`. This is the "fix `λ > 0` large enough
that `a(u, v) + λ ∫ uv` is coercive" of the proof of [brezis2011functional] Theorem 9.23, made
explicit; no Poincaré inequality and no boundedness of `Ω` enters. -/
theorem generalForm_garding (hA : IsUniformlyElliptic Ω A α) :
    (generalForm Ω A a₁ a₀ + ((∑ i, ‖a₁ i‖) ^ 2 / (2 * α) + ‖a₀‖ + α / 2)
      • pairing Ω (ContinuousLinearMap.id ℝ _) 0 0).IsCoerciveWith (α / 2) := by
  intro v
  have hα : 0 < α := hA.1
  simp only [RCLike.re_to_real, add_apply, smul_apply, pairing_apply, ContinuousLinearMap.id_apply,
    real_inner_self_eq_norm_sq, smul_eq_mul]
  rw [norm_sq_eq]
  obtain ⟨D, hD⟩ : ∃ D : ℝ,
      D = ∑ i : Fin N, ‖SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i)‖ ^ 2 := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := hD ▸ Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ∑ i, ‖a₁ i‖ := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := hc ▸ Finset.sum_nonneg fun i _ ↦ norm_nonneg (a₁ i)
  have hS : ∑ i : Fin N, ‖a₁ i‖ * ‖SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i)‖
      ≤ c * √D := by
    rw [hc, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [Real.le_sqrt (norm_nonneg _) hD0, hD]
    exact Finset.single_le_sum (f := fun i ↦
      ‖SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i)‖ ^ 2) (fun i _ ↦ sq_nonneg _)
      (Finset.mem_univ i)
  have hge := generalForm_self_ge Ω (a₁ := a₁) (a₀ := a₀) hA v
  rw [← hD] at hge ⊢
  rw [← hc]
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = ‖SobolevMultiIndex.weakDeriv v 0‖ := ⟨_, rfl⟩
  rw [← hw] at hge ⊢
  have hw0 : 0 ≤ w := hw ▸ norm_nonneg _
  have hsq : √D ^ 2 = D := Real.sq_sqrt hD0
  have key : c * √D * w ≤ α / 2 * D + c ^ 2 / (2 * α) * w ^ 2 := by
    have h2α : 0 < 2 * α := by positivity
    have e : c ^ 2 / (2 * α) * w ^ 2 = (c * w) ^ 2 / (2 * α) := by ring
    rw [e, ← sub_le_iff_le_add', le_div_iff₀ h2α]
    have hsq2 : α ^ 2 * √D ^ 2 = α ^ 2 * D := by rw [hsq]
    nlinarith [sq_nonneg (α * √D - c * w), hsq2]
  have hSw : (∑ i : Fin N, ‖a₁ i‖ * ‖SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i)‖) * w
      ≤ c * √D * w := mul_le_mul_of_nonneg_right hS hw0
  nlinarith

end Ellipticity

/-! ### Example 3: the symmetric problem on a bounded domain -/

section Example3

variable {d : ℕ} {Ω' : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
  {A : Fin (d + 1) → Fin (d + 1) →
    Lp ℝ ⊤ (volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
  {a₀ : Lp ℝ ⊤ (volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin (d + 1)))))} {α : ℝ}

/-- **Coercivity of the symmetric-problem form (38) on `H^1_0(Ω)`** for a bounded `Ω ⊆ B(0, R)`,
under the ellipticity condition (36) and `a₀ ≥ 0` ([brezis2011functional] §9.5, Example 3): the
restriction of `generalForm Ω A 0 a₀` to `H^1_0(Ω)` is coercive with constant
`α / (1 + (2R)²)`. For `v ∈ H^1_0(Ω)`, `a(v, v) ≥ α ∑ᵢ ‖∂ᵢv‖₂² + ∫_Ω a₀ v² ≥ α ∑ᵢ ‖∂ᵢv‖₂²`, and
Poincaré's inequality (Corollary 9.19, `SobolevEuclideanZero.norm_le_gradNorm`) gives
`‖v‖²_{H^1} ≤ (1 + (2R)²) ∑ᵢ ‖∂ᵢv‖₂²`. The book's coefficients `a_ij ∈ C^1(Ω̄)`, `a₀ ∈ C(Ω̄)`
enter as `L^∞` classes. -/
theorem generalForm_isCoerciveWith_of_nonneg {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω' : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R) (hA : IsUniformlyElliptic Ω' A α)
    (ha₀ : 0 ≤ a₀) :
    ((generalForm Ω' A 0 a₀).restrict (SobolevEuclideanZero (d + 1) 1 2 Ω')).IsCoerciveWith
      (α / (1 + (2 * R) ^ 2)) := by
  intro v
  have hα : 0 < α := hA.1
  rw [RCLike.re_to_real, SesqForm.restrict_apply, generalForm_apply_inner, ← Submodule.norm_coe]
  simp only [Pi.zero_apply, mulL_zero, zero_apply, inner_zero_left, Finset.sum_const_zero, add_zero]
  have h1 := sum_inner_mulL_ge Ω' hA (v : SobolevEuclidean (d + 1) 1 2 Ω')
  have h2 : 0 ≤ ⟪mulL Ω' a₀ (SobolevMultiIndex.weakDeriv (v : SobolevEuclidean (d + 1) 1 2 Ω') 0),
      SobolevMultiIndex.weakDeriv (v : SobolevEuclidean (d + 1) 1 2 Ω') 0⟫_ℝ := by
    rw [inner_mulL_eq_integral]
    refine integral_nonneg_of_ae ?_
    filter_upwards [(Lp.coeFn_nonneg a₀).2 ha₀] with x hx
    rw [mul_assoc, ← sq]
    exact mul_nonneg hx (sq_nonneg _)
  have hP := SobolevEuclideanZero.norm_le_gradNorm (p := 2) (by norm_num) hR hΩ v
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, ← Real.sqrt_eq_rpow] at hP
  have hP2 : ‖(v : SobolevEuclidean (d + 1) 1 2 Ω')‖ ^ 2
      ≤ (1 + (2 * R) ^ 2) * ∑ i, ‖SobolevMultiIndex.weakDeriv (v : SobolevEuclidean (d + 1) 1 2 Ω')
        (MultiIndexLE.single i)‖ ^ 2 := by
    calc ‖(v : SobolevEuclidean (d + 1) 1 2 Ω')‖ ^ 2
        ≤ (√(1 + (2 * R) ^ 2)
          * SobolevMultiIndex.gradNorm (v : SobolevEuclidean (d + 1) 1 2 Ω')) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hP 2
      _ = (1 + (2 * R) ^ 2) * ∑ i, ‖SobolevMultiIndex.weakDeriv
          (v : SobolevEuclidean (d + 1) 1 2 Ω') (MultiIndexLE.single i)‖ ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by positivity), gradNorm_eq_sqrt,
            Real.sq_sqrt (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)]
  have hpos : 0 < 1 + (2 * R) ^ 2 := by positivity
  calc α / (1 + (2 * R) ^ 2) * ‖(v : SobolevEuclidean (d + 1) 1 2 Ω')‖ ^ 2
      ≤ α / (1 + (2 * R) ^ 2) * ((1 + (2 * R) ^ 2) * ∑ i, ‖SobolevMultiIndex.weakDeriv
          (v : SobolevEuclidean (d + 1) 1 2 Ω') (MultiIndexLE.single i)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hP2 (by positivity)
    _ = α * ∑ i, ‖SobolevMultiIndex.weakDeriv (v : SobolevEuclidean (d + 1) 1 2 Ω')
          (MultiIndexLE.single i)‖ ^ 2 := by
        field_simp
    _ ≤ _ := by linarith

/-- **Example 3 of [brezis2011functional] §9.5: existence and uniqueness for the symmetric
problem (37)** on a bounded `Ω ⊆ B(0, R)`, under the ellipticity condition (36) and `a₀ ≥ 0`:
every `f ∈ L²(Ω)` has exactly one weak solution `u ∈ H^1_0(Ω)`, i.e. one `u` with
`∑ᵢⱼ ∫_Ω a_ij ∂ᵢu ∂ⱼv + ∫_Ω a₀ u v = ∫_Ω f v` for all `v ∈ H^1_0(Ω)` — Lax–Milgram with the
coercivity of `Elliptic.generalForm_isCoerciveWith_of_nonneg`. No symmetry of `a_ij` is needed
for existence, as the book notes. -/
theorem existsUnique_isGalerkinSolution_general_of_nonneg {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω' : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R) (hA : IsUniformlyElliptic Ω' A α)
    (ha₀ : 0 ≤ a₀) (f : Lp ℝ 2 (volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    ∃! u, IsGalerkinSolution (generalForm Ω' A 0 a₀) (load Ω' f)
      (SobolevEuclideanZero (d + 1) 1 2 Ω') u := by
  have hc : 0 < α / (1 + (2 * R) ^ 2) := div_pos hA.1 (by positivity)
  have hcoer := generalForm_isCoerciveWith_of_nonneg hR hΩ hA ha₀
  exact IsGalerkinSolution.existsUnique_of_restrict (ℓ := load Ω' f) hc hcoer

/-- **Example 3, the minimization**: when the matrix `a_ij` is symmetric, the weak solution of the
symmetric problem (37) is the minimizer of `½ ∫_Ω (∑ᵢⱼ a_ij ∂ᵢv ∂ⱼv + a₀ v²) − ∫_Ω f v` over
`H^1_0(Ω)` (`SesqForm.isMinOn_energy_iff` for the Hermitian form, coercive on `H^1_0(Ω)`). -/
theorem isMinOn_energy_iff_isGalerkinSolution_general_of_symm {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω' : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R) (hA : IsUniformlyElliptic Ω' A α)
    (hsymm : ∀ i j, A i j = A j i) (ha₀ : 0 ≤ a₀)
    {f : Lp ℝ 2 (volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    {u : SobolevEuclidean (d + 1) 1 2 Ω'} (hu : u ∈ SobolevEuclideanZero (d + 1) 1 2 Ω') :
    IsMinOn ((generalForm Ω' A 0 a₀).energy (load Ω' f)) (SobolevEuclideanZero (d + 1) 1 2 Ω') u
      ↔ IsGalerkinSolution (generalForm Ω' A 0 a₀) (load Ω' f)
        (SobolevEuclideanZero (d + 1) 1 2 Ω') u := by
  have hcoer := generalForm_isCoerciveWith_of_nonneg hR hΩ hA ha₀
  have hherm := (generalForm_isHermitian_of_symm Ω' A a₀ hsymm).restrict
    (SobolevEuclideanZero (d + 1) 1 2 Ω')
  rw [SesqForm.isMinOn_energy_iff_of_restrict (load Ω' f) hherm (div_pos hA.1 (by positivity))
    hcoer hu]
  exact ⟨fun h ↦ ⟨hu, h⟩, fun h ↦ h.2⟩

end Example3


/-! ### The solution operator on `L²(Ω)` -/

section SolutionOperator

/-- A form coercive in the sense of `SesqForm.IsCoercive` is coercive in Mathlib's sense
(`IsCoercive`): the bridge to Mathlib's Lax–Milgram equivalence
`IsCoercive.continuousLinearEquivOfBilin`. -/
theorem _root_.SesqForm.IsCoercive.isCoercive {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {a : SesqForm ℝ V} (ha : a.IsCoercive) :
    IsCoercive (a : V →L[ℝ] V →L[ℝ] ℝ) :=
  let ⟨c, hc, h⟩ := ha
  ⟨c, hc, fun u ↦ by rw [mul_assoc, ← sq]; exact h u⟩

/-- The Riesz representation `(K →L[ℝ] ℝ) ≃L[ℝ] K` of a real Hilbert space `K`, as a real
continuous linear equivalence: Mathlib's `InnerProductSpace.toDual` is conjugate-linear, and over
`ℝ` the ascription makes it a `≃L[ℝ]`. -/
def rieszEquiv (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K] :
    (K →L[ℝ] ℝ) ≃L[ℝ] K :=
  (InnerProductSpace.toDual ℝ K).symm.toContinuousLinearEquiv

/-- `⟪rieszEquiv K ℓ, v⟫ = ℓ v`. -/
theorem inner_rieszEquiv_apply {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [CompleteSpace K] (ℓ : K →L[ℝ] ℝ) (v : K) : ⟪rieszEquiv K ℓ, v⟫_ℝ = ℓ v :=
  InnerProductSpace.toDual_symm_apply

variable (a : SesqForm ℝ (SobolevEuclidean N 1 2 Ω))
  (ha : (a.restrict (SobolevEuclideanZero N 1 2 Ω)).IsCoercive)

/-- **The solution map `f ↦ u ∈ H^1_0(Ω)`** of the weak Dirichlet problem `a(u, v) = ⟨f, v⟩` for
all `v ∈ H^1_0(Ω)`, for a form `a` coercive on `H^1_0(Ω)`, as a continuous linear map
`L²(Ω) → H^1_0(Ω)`: the Riesz representative of the load, pulled back through Mathlib's
Lax–Milgram equivalence `IsCoercive.continuousLinearEquivOfBilin` of the restricted form. -/
def solutionMap : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →L[ℝ]
    SobolevEuclideanZero N 1 2 Ω :=
  (((IsCoercive.continuousLinearEquivOfBilin ha.isCoercive).symm :
      SobolevEuclideanZero N 1 2 Ω →L[ℝ] SobolevEuclideanZero N 1 2 Ω) ∘L
    (rieszEquiv (SobolevEuclideanZero N 1 2 Ω) :
      (SobolevEuclideanZero N 1 2 Ω →L[ℝ] ℝ) →L[ℝ] SobolevEuclideanZero N 1 2 Ω)) ∘L
    loadL Ω (SobolevEuclideanZero N 1 2 Ω)

/-- **The solution operator `T : L²(Ω) → L²(Ω)`** of the weak Dirichlet problem for a form `a`
coercive on `H^1_0(Ω)`: `T f` is the function of the unique `u ∈ H^1_0(Ω)` with `a(u, v) = ⟨f, v⟩`
for all `v ∈ H^1_0(Ω)` (`Elliptic.solutionMap`), read in `L²(Ω)`. This is the operator `T` of the
proofs of [brezis2011functional] Theorem 9.23 and Theorem 9.31. -/
def solutionOperator : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →L[ℝ]
    Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume ∘L
    solutionMap Ω a ha

/-- `T f` is the function of the solution `u ∈ H^1_0(Ω)`. -/
theorem solutionOperator_apply
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    solutionOperator Ω a ha f = SobolevMultiIndexZero.fnL ℝ _ 1 2 Ω volume (solutionMap Ω a ha f) :=
  rfl

/-- **The solution map solves the weak problem**: `a(u, v) = ⟨f, v⟩_{L²}` for every
`v ∈ H^1_0(Ω)`, `u = solutionMap Ω a ha f`. -/
theorem restrict_apply_solutionMap
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (v : SobolevEuclideanZero N 1 2 Ω) :
    a.restrict (SobolevEuclideanZero N 1 2 Ω) (solutionMap Ω a ha f) v
      = loadL Ω (SobolevEuclideanZero N 1 2 Ω) f v := by
  have h := IsCoercive.continuousLinearEquivOfBilin_apply ha.isCoercive (solutionMap Ω a ha f) v
  rw [← h]
  simp only [solutionMap, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]
  exact inner_rieszEquiv_apply _ _

/-- **The solution map gives the Galerkin solution** in `H^1_0(Ω)`:
`IsGalerkinSolution a (load Ω f) (H^1_0(Ω)) (solutionMap Ω a ha f)`. -/
theorem isGalerkinSolution_solutionMap
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    IsGalerkinSolution a (load Ω f) (SobolevEuclideanZero N 1 2 Ω) (solutionMap Ω a ha f) :=
  ⟨(solutionMap Ω a ha f).2, fun v hv ↦ restrict_apply_solutionMap Ω a ha f ⟨v, hv⟩⟩

/-- **Uniqueness**: every Galerkin solution in `H^1_0(Ω)` is the value of the solution map. -/
theorem eq_solutionMap_of_isGalerkinSolution
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    {u : SobolevEuclidean N 1 2 Ω}
    (hu : IsGalerkinSolution a (load Ω f) (SobolevEuclideanZero N 1 2 Ω) u) :
    u = solutionMap Ω a ha f := by
  obtain ⟨c, hc, hcoer⟩ := id ha
  obtain ⟨w, -, hw⟩ := IsGalerkinSolution.existsUnique_of_restrict (ℓ := load Ω f) hc hcoer
  rw [hw u hu, hw _ (isGalerkinSolution_solutionMap Ω a ha f)]

/-- **Uniqueness, on the solution operator**: the function of any Galerkin solution `u ∈ H^1_0(Ω)`
of `a(u, v) = ⟨f, v⟩` is `T f`. -/
theorem solutionOperator_eq_of_isGalerkinSolution
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    {u : SobolevEuclidean N 1 2 Ω}
    (hu : IsGalerkinSolution a (load Ω f) (SobolevEuclideanZero N 1 2 Ω) u) :
    SobolevMultiIndex.fnL ℝ _ 1 2 Ω volume u = solutionOperator Ω a ha f := by
  rw [solutionOperator_apply, SobolevMultiIndexZero.fnL_eq,
    ← eq_solutionMap_of_isGalerkinSolution Ω a ha hu]

/-- **The solution operator, specified**: `T f` is the function of some `u ∈ H^1_0(Ω)` with
`a(u, v) = ⟨f, v⟩` for all `v ∈ H^1_0(Ω)`. -/
theorem solutionOperator_spec (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ∃ u ∈ SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndex.fnL ℝ _ 1 2 Ω volume u = solutionOperator Ω a ha f ∧
        ∀ v ∈ SobolevEuclideanZero N 1 2 Ω, a u v = load Ω f v :=
  ⟨solutionMap Ω a ha f, (solutionMap Ω a ha f).2, rfl,
    (isGalerkinSolution_solutionMap Ω a ha f).2⟩

/-- **The stability bound of the solution map**, `‖u‖_{H^1(Ω)} ≤ ‖f‖₂ / c` for a coercivity
constant `c` of the form on `H^1_0(Ω)`. -/
theorem norm_solutionMap_le {c : ℝ} (hc : 0 < c)
    (hcoer : (a.restrict (SobolevEuclideanZero N 1 2 Ω)).IsCoerciveWith c)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ‖solutionMap Ω a ha f‖ ≤ ‖f‖ / c := by
  have h := (a.restrict (SobolevEuclideanZero N 1 2 Ω)).norm_le_of_forall_apply_eq
    (loadL Ω (SobolevEuclideanZero N 1 2 Ω) f) hc hcoer (restrict_apply_solutionMap Ω a ha f)
  refine h.trans (div_le_div_of_nonneg_right ?_ hc.le)
  rw [loadL_eq]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  calc ‖load Ω f‖ * ‖(SobolevEuclideanZero N 1 2 Ω).subtypeL‖ ≤ ‖f‖ * 1 :=
        mul_le_mul (norm_load_le Ω f) (Submodule.norm_subtypeL_le _) (norm_nonneg _)
          (norm_nonneg _)
    _ = ‖f‖ := mul_one _

/-- **The stability bound of the solution operator**, `‖T f‖₂ ≤ ‖f‖₂ / c`. -/
theorem norm_solutionOperator_apply_le {c : ℝ} (hc : 0 < c)
    (hcoer : (a.restrict (SobolevEuclideanZero N 1 2 Ω)).IsCoerciveWith c)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ‖solutionOperator Ω a ha f‖ ≤ ‖f‖ / c :=
  (SobolevMultiIndexZero.norm_fnL_apply_le _).trans (norm_solutionMap_le Ω a ha hc hcoer f)

end SolutionOperator


/-! ### Classical and weak solutions: Steps A and D of Example 1 -/

section Classical

open Laplacian

variable {u : EuclideanSpace ℝ (Fin N) → ℝ}

/-- **The Laplacian of a `C²` function on an open set, in coordinates**: at `x ∈ Ω`,
`Δ u x = ∑ᵢ ∂ᵢ(∂ᵢu)(x)`, with `∂ᵢu = fderiv u · e_i`
(`laplacian_eq_iteratedFDeriv_orthonormalBasis` and `fderiv_clm_apply`). -/
theorem laplacian_eq_sum_fderiv_fderiv (hu : ContDiffOn ℝ 2 u Ω)
    {x : EuclideanSpace ℝ (Fin N)} (hx : x ∈ Ω) :
    Δ u x = ∑ i : Fin N, fderiv ℝ (fun y ↦ fderiv ℝ u y (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single i 1) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    ((hu.fderiv_of_isOpen Ω.isOpen (m := 1) le_rfl).differentiableOn one_ne_zero).differentiableAt
      (Ω.isOpen.mem_nhds hx)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u
    (EuclideanSpace.basisFun (Fin N) ℝ)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [iteratedFDeriv_two_apply, fderiv_clm_apply hd (differentiableAt_const _)]
  simp

/-- The Laplacian of a `C²` function is continuous on the open set. -/
theorem continuousOn_laplacian (hu : ContDiffOn ℝ 2 u Ω) : ContinuousOn (Δ u) Ω := by
  refine ContinuousOn.congr (continuousOn_finsetSum Finset.univ fun i _ ↦ ?_)
    fun x hx ↦ laplacian_eq_sum_fderiv_fderiv Ω hu hx
  have hg : ContDiffOn ℝ 1 (fun y ↦ fderiv ℝ u y (EuclideanSpace.single i 1)) Ω :=
    (hu.fderiv_of_isOpen Ω.isOpen le_rfl).clm_apply contDiffOn_const
  exact (hg.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl).clm_apply continuousOn_const

/-- The partial derivatives of an element `U` of `H^1(Ω)` whose function is a `C^1` function `u`
on `Ω` are the classical ones, almost everywhere on `Ω`. -/
theorem weakDeriv_single_ae_eq_fderiv_of_contDiffOn (hu : ContDiffOn ℝ 1 u Ω)
    {U : SobolevEuclidean N 1 2 Ω}
    (hU : SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u)
    (i : Fin N) :
    (SobolevMultiIndex.weakDeriv U (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        fun x ↦ fderiv ℝ u x (EuclideanSpace.single i 1) := by
  have h1 := ((SobolevMultiIndex.hasWeakIteratedLineDerivOn U (MultiIndexLE.single i)).of_perm
    (multiIndexTuple_single_perm ((EuclideanSpace.basisFun (Fin N) ℝ).toBasis : Fin N → _)
      i)).congr_ae hU (Filter.EventuallyEq.refl _ _)
  rw [EuclideanSpace.basisFun_toBasis_apply] at h1
  exact (ae_restrict_iff' Ω.isOpen.measurableSet).2
    (h1.ae_eq (hu.hasWeakIteratedLineDerivOn_single Ω i))

/-- **The form of `-Δ + 1` against a test function, for a `C²` function**: if `U ∈ H^1(Ω)` has the
`C²` function `u` on `Ω` as its function and `V` has the test function `φ` as its function, then
`laplaceForm Ω U V = ∫_Ω (-Δu + u) φ`. Integration by parts of `∂ᵢu` (a `C^1` function on `Ω`)
against `φ`, summed over `i` (`Elliptic.laplacian_eq_sum_fderiv_fderiv`). -/
theorem laplaceForm_eq_integral_of_contDiffOn (hu : ContDiffOn ℝ 2 u Ω)
    {U : SobolevEuclidean N 1 2 Ω}
    (hU : SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u)
    {V : SobolevEuclidean N 1 2 Ω} {φ : 𝓓(Ω, ℝ)}
    (hV : SobolevMultiIndex.fn V =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] φ) :
    laplaceForm Ω U V = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), (-Δ u x + u x) * φ x := by
  have hΩo := Ω.isOpen
  have hΩm := hΩo.measurableSet
  have hu1 : ContDiffOn ℝ 1 u Ω := hu.of_le (by norm_num)
  have hUd := weakDeriv_single_ae_eq_fderiv_of_contDiffOn Ω hu1 hU
  have hVd := fun i ↦ SobolevMultiIndexZero.weakDeriv_single_ae_eq_testFunction hV i
  -- `∂ᵢu` is `C^1` on `Ω`, so its weak derivative along `e_i` is `∂ᵢ∂ᵢu`
  have hg : ∀ i : Fin N, ContDiffOn ℝ 1 (fun y ↦ fderiv ℝ u y (EuclideanSpace.single i 1)) Ω :=
    fun i ↦ (hu.fderiv_of_isOpen hΩo le_rfl).clm_apply contDiffOn_const
  have hibp : ∀ i : Fin N, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      fderiv ℝ u x (EuclideanSpace.single i 1) * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = -∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), φ x
        * fderiv ℝ (fun y ↦ fderiv ℝ u y (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1) := by
    intro i
    have h := ((hg i).hasWeakIteratedLineDerivOn_single Ω i).integral_smul_eq φ
    simp only [iteratedFDeriv_one_apply, Matrix.cons_val_zero, smul_eq_mul, pow_one,
      neg_one_mul] at h
    rw [← h]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
  -- integrability of the pieces
  have hI1 : ∀ i : Fin N, Integrable (fun x ↦ φ x
      * fderiv ℝ (fun y ↦ fderiv ℝ u y (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1))
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := fun i ↦ by
    have := ((hg i).hasWeakIteratedLineDerivOn_single Ω i).integrable_smul_weakDeriv φ
    simp only [smul_eq_mul] at this
    exact this.integrableOn
  have hI0 : Integrable (fun x ↦ u x * φ x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
    have := (hu1.continuousOn.locallyIntegrableOn (μ := volume) hΩm)
      |>.integrable_smul_left_of_tsupport_subset φ.contDiff.continuous φ.hasCompactSupport
        φ.tsupport_subset
    simp only [smul_eq_mul] at this
    exact this.integrableOn.congr_fun (fun x _ ↦ mul_comm _ _) hΩm
  -- the left-hand side as integrals of classical derivatives
  have e1 : ∀ i : Fin N, ⟪SobolevMultiIndex.weakDeriv U (MultiIndexLE.single i),
      SobolevMultiIndex.weakDeriv V (MultiIndexLE.single i)⟫_ℝ
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        fderiv ℝ u x (EuclideanSpace.single i 1) * fderiv ℝ φ x (EuclideanSpace.single i 1) :=
    fun i ↦ by
      rw [L2.inner_eq_integral_mul]
      refine integral_congr_ae ((hUd i).mul ?_)
      rw [← EuclideanSpace.basisFun_toBasis_apply i]
      exact hVd i
  have e0 : ⟪SobolevMultiIndex.weakDeriv U 0, SobolevMultiIndex.weakDeriv V 0⟫_ℝ
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), u x * φ x := by
    rw [L2.inner_eq_integral_mul]
    exact integral_congr_ae (hU.mul hV)
  -- the right-hand side, split
  have e2 : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), (-Δ u x + u x) * φ x
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        (-(∑ i : Fin N, φ x * fderiv ℝ (fun y ↦ fderiv ℝ u y (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1)) + u x * φ x) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem hΩm] with x hx
    rw [laplacian_eq_sum_fderiv_fderiv Ω hu hx, ← Finset.mul_sum]
    ring
  have e3 : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        (-(∑ i : Fin N, φ x * fderiv ℝ (fun y ↦ fderiv ℝ u y (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1)) + u x * φ x)
      = (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          -(∑ i : Fin N, φ x * fderiv ℝ (fun y ↦ fderiv ℝ u y (EuclideanSpace.single i 1)) x
            (EuclideanSpace.single i 1)))
        + ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), u x * φ x :=
    integral_add (integrable_finsetSum _ fun i _ ↦ hI1 i).neg hI0
  have e4 : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        -(∑ i : Fin N, φ x * fderiv ℝ (fun y ↦ fderiv ℝ u y (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1))
      = ∑ i : Fin N, -∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          φ x * fderiv ℝ (fun y ↦ fderiv ℝ u y (EuclideanSpace.single i 1)) x
            (EuclideanSpace.single i 1) := by
    rw [integral_neg, integral_finsetSum _ fun i _ ↦ hI1 i, Finset.sum_neg_distrib]
  rw [laplaceForm_apply_inner, e2, e3, e4, e0]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by rw [e1, hibp]

/-- **The interior half of Step A of Example 1**: let `Ω ⊆ ℝ^N` be open and bounded,
`u ∈ C²(Ω̄)` (`ContDiffOnClosure ℝ 2 u Ω`: `C²` on `Ω` with derivatives of order `≤ 2` extending
continuously to `Ω̄`), and `f ∈ L²(Ω)` with `-Δu + u = f` on `Ω`. Then `u` is the function of
some `U ∈ H^1(Ω)` with `a(U, v) = ∫_Ω f v` for every `v ∈ H^1_0(Ω)`, where `a` is the form of
`-Δ + 1`. No boundary condition enters: this is what the inhomogeneous Dirichlet problem
([brezis2011functional] §9.5, Example 2, "as above, any classical solution is a weak solution")
uses, the homogeneous problem adding `U ∈ H^1_0(Ω)` by Theorem 9.17
(`Elliptic.isGalerkinSolution_laplace_of_classical`).

Proof ([brezis2011functional] §9.5, Example 1, Step A): `u ∈ W^{1,2}(Ω)` with its classical
gradient as weak gradient (`ContDiffOnClosure.memSobolevMultiIndex_of_isBounded`), hence the
function of some `U ∈ H^1(Ω)`; for a test function `v`, `a(U, v) = ∫_Ω (-Δu + u) v = ∫_Ω f v`
(`Elliptic.laplaceForm_eq_integral_of_contDiffOn`), and the identity extends to `H^1_0(Ω)` by
density, both sides being continuous in `v`
(`SobolevMultiIndexZero.eqOn_of_eqOn_testFunctions`). -/
theorem exists_sobolev_forall_laplaceForm_eq_load_of_classical
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (hu : ContDiffOnClosure ℝ 2 u Ω) {f : EuclideanSpace ℝ (Fin N) → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (heq : ∀ x ∈ Ω, -Δ u x + u x = f x) :
    ∃ U : SobolevEuclidean N 1 2 Ω,
      SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u ∧
        ∀ v ∈ SobolevEuclideanZero N 1 2 Ω, laplaceForm Ω U v = load Ω (hf.toLp f) v := by
  have hΩm := Ω.isOpen.measurableSet
  have hu1 : ContDiffOnClosure ℝ 1 u Ω := hu.of_le (by norm_num)
  obtain ⟨U, hU⟩ := (hu1.memSobolevMultiIndex_of_isBounded Ω hΩ 2).exists_sobolevMultiIndex
  refine ⟨U, hU, SobolevMultiIndexZero.eqOn_of_eqOn_testFunctions (laplaceForm Ω U).continuous
    (load Ω (hf.toLp f)).continuous ?_⟩
  rintro V ⟨φ, hV⟩
  rw [laplaceForm_eq_integral_of_contDiffOn Ω hu.contDiffOn hU hV, load_apply]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem hΩm, hf.coeFn_toLp, hV] with x hx hfx hVx
  rw [heq x hx, hfx, hVx]

/-- **Step A of Example 1: a classical solution is a weak solution.** Let `Ω ⊆ ℝ^N` be open and
bounded, `u ∈ C²(Ω̄)` — `ContDiffOnClosure ℝ 2 u Ω` (footnote 16 of [brezis2011functional]
§9.3: `C²` on `Ω` with derivatives of order `≤ 2` extending continuously to `Ω̄`) and `u` itself
continuous on `closure Ω`, so that its boundary values are meaningful — with `u = 0` on `∂Ω`,
and `f ∈ L²(Ω)` with `-Δu + u = f` on `Ω`. Then `u` is the function of some `U ∈ H^1_0(Ω)`, and
`U` is the weak solution: `IsGalerkinSolution (laplaceForm Ω) (load Ω f) (H^1_0(Ω)) U`.
Mathlib's `ContDiffOn ℝ 2 u (closure Ω)` gives both hypotheses on `u`
(`ContDiffOn.contDiffOnClosure`, `ContDiffOn.continuousOn`).

Proof ([brezis2011functional] §9.5, Example 1, Step A): `u` is the function of some `U ∈ H^1(Ω)`
satisfying the weak identity on `H^1_0(Ω)`
(`Elliptic.exists_sobolev_forall_laplaceForm_eq_load_of_classical`); `u` is continuous on
`closure Ω` and vanishes on `∂Ω`, so `U ∈ H^1_0(Ω)` by Theorem 9.17 (i) ⇒ (ii), which holds for
every open `Ω` (Remark 19). -/
theorem isGalerkinSolution_laplace_of_classical
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (hu : ContDiffOnClosure ℝ 2 u Ω)
    (huc : ContinuousOn u (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (h0 : EqOn u 0 (frontier Ω)) {f : EuclideanSpace ℝ (Fin N) → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (heq : ∀ x ∈ Ω, -Δ u x + u x = f x) :
    ∃ U ∈ SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u ∧
        IsGalerkinSolution (laplaceForm Ω) (load Ω (hf.toLp f)) (SobolevEuclideanZero N 1 2 Ω)
          U := by
  obtain ⟨U, hU, hUw⟩ := exists_sobolev_forall_laplaceForm_eq_load_of_classical Ω hΩ hu hf heq
  have hU0 : U ∈ SobolevEuclideanZero N 1 2 Ω :=
    SobolevEuclideanZero.mem_of_continuousOn_closure_of_eqOn_frontier (by norm_num) U hU huc h0
  exact ⟨U, hU0, hU, hU0, hUw⟩

/-- **Step D of Example 1: a `C²` weak solution satisfies the equation almost everywhere.** If
`U ∈ H^1(Ω)` satisfies `a(U, v) = ⟨f, v⟩` for every test function `v` and its function is a `C²`
function `u` on `Ω`, then `-Δu + u = f` almost everywhere on `Ω`: the weak identity reads
`∫_Ω (-Δu + u - f) v = 0` for every test function `v`
(`Elliptic.laplaceForm_eq_integral_of_contDiffOn`), and Corollary 4.24 is Mathlib's
`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` ([brezis2011functional] §9.5, Example 1,
Step D). -/
theorem laplacian_ae_eq_of_forall_testFunction {U : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hUw : ∀ V ∈ SobolevMultiIndex.testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
      1 2 Ω volume, laplaceForm Ω U V = load Ω f V)
    (hu : ContDiffOn ℝ 2 u Ω)
    (hU : SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u) :
    (fun x ↦ -Δ u x + u x) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] f := by
  have hΩo := Ω.isOpen
  have hΩm := hΩo.measurableSet
  have hloc : LocallyIntegrableOn (fun x ↦ -Δ u x + u x - f x) Ω volume := by
    refine (((continuousOn_laplacian Ω hu).neg.add
      (hu.of_le (by norm_num) : ContDiffOn ℝ 1 u Ω).continuousOn).locallyIntegrableOn hΩm).sub
      ((Lp.memLp f).locallyIntegrableOn (by norm_num))
  have key := hΩo.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume) hloc
    fun g hg hgc hgs ↦ by
    set φ : 𝓓(Ω, ℝ) := ⟨g, hg, hgc, hgs⟩ with hφ
    obtain ⟨V, hVT, hV⟩ := φ.exists_mem_sobolevMultiIndex_testFunctions
      (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis) (k := 1) (p := 2) (μ := volume)
    have h1 := hUw V hVT
    rw [laplaceForm_eq_integral_of_contDiffOn Ω hu hU hV, load_apply] at h1
    have hI1 : Integrable (fun x ↦ (-Δ u x + u x) * g x)
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
      have := (((continuousOn_laplacian Ω hu).neg.add
        (hu.of_le (by norm_num) : ContDiffOn ℝ 1 u Ω).continuousOn).locallyIntegrableOn
          (μ := volume) hΩm)
        |>.integrable_smul_left_of_tsupport_subset hg.continuous hgc hgs
      simp only [smul_eq_mul] at this
      exact this.integrableOn.congr_fun (fun x _ ↦ mul_comm _ _) hΩm
    have hI2 : Integrable (fun x ↦ f x * g x)
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
      have := ((Lp.memLp f).locallyIntegrableOn (by norm_num) (Ω := Ω))
        |>.integrable_smul_left_of_tsupport_subset hg.continuous hgc hgs
      simp only [smul_eq_mul] at this
      exact this.integrableOn.congr_fun (fun x _ ↦ mul_comm _ _) hΩm
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hgs h), zero_smul]]
    have e : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), g x • (-Δ u x + u x - f x)
        = (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), (-Δ u x + u x) * g x)
          - ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), f x * g x := by
      rw [← integral_sub hI1 hI2]
      exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [smul_eq_mul]; ring)
    have h1' : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), (-Δ u x + u x) * g x
        = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), f x * g x := by
      have h2 : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), (-Δ u x + u x) * φ x
          = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), f x * φ x := by
        rw [h1]
        exact integral_congr_ae (hV.mono fun x hx ↦ by dsimp only; rw [hx])
      exact h2
    rw [e, h1', sub_self]
  filter_upwards [(ae_restrict_iff' hΩm).2 key] with x hx
  exact sub_eq_zero.1 hx

/-- **Step D, for a Galerkin solution**: if `U` is the weak solution of the Dirichlet problem for
`-Δ + 1` with datum `f` and its function is a `C²` function `u` on `Ω`, then `-Δu + u = f`
almost everywhere on `Ω`. -/
theorem laplacian_ae_eq_of_isGalerkinSolution {U : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hUw : IsGalerkinSolution (laplaceForm Ω) (load Ω f) (SobolevEuclideanZero N 1 2 Ω) U)
    (hu : ContDiffOn ℝ 2 u Ω)
    (hU : SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u) :
    (fun x ↦ -Δ u x + u x) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] f :=
  laplacian_ae_eq_of_forall_testFunction Ω
    (fun V hV ↦ hUw.2 V (SobolevMultiIndexZero.testFunctions_le hV)) hu hU

/-- **Step D, everywhere for a continuous datum**: if moreover `f` agrees almost everywhere on
`Ω` with a function `g` continuous on `Ω`, then `-Δu + u = g` at every point of `Ω`: two
functions continuous on the open set `Ω` that agree almost everywhere agree everywhere
(`Measure.eqOn_open_of_ae_eq`). The book's "`-Δu + u = f` everywhere on `Ω`, since
`u ∈ C²(Ω)`" presumes such a continuous representative of `f`. -/
theorem laplacian_eq_of_isGalerkinSolution_of_continuousOn {U : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hUw : IsGalerkinSolution (laplaceForm Ω) (load Ω f) (SobolevEuclideanZero N 1 2 Ω) U)
    (hu : ContDiffOn ℝ 2 u Ω)
    (hU : SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u)
    {g : EuclideanSpace ℝ (Fin N) → ℝ} (hg : ContinuousOn g Ω)
    (hfg : (f : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] g) :
    ∀ x ∈ Ω, -Δ u x + u x = g x :=
  Measure.eqOn_open_of_ae_eq ((laplacian_ae_eq_of_isGalerkinSolution Ω hUw hu hU).trans hfg)
    Ω.isOpen ((continuousOn_laplacian Ω hu).neg.add
      (hu.of_le (by norm_num) : ContDiffOn ℝ 1 u Ω).continuousOn) hg

/-! ### Step A of Example 3: a classical solution of the general equation is a weak solution -/

/-- **The general form against a test function, for a `C²` function and `C¹` coefficients**: if
`U ∈ H^1(Ω)` has the `C²` function `u` on `Ω` as its function, the `L^∞` coefficients `A i j`,
`a₁ i`, `a₀` agree almost everywhere on `Ω` with functions `a i j` (of class `C¹` on `Ω`), `b i`
and `c`, and `V` has the test function `φ` as its function, then
`generalForm Ω A a₁ a₀ U V = ∫_Ω (-∑ᵢⱼ ∂ⱼ(a_ij ∂ᵢu) + ∑ᵢ b_i ∂ᵢu + c u) φ`, where
`∂ⱼ(a_ij ∂ᵢu)(x) = D(a_ij ∂ᵢu)(x) e_j`. Integration by parts of the `C^1` function `a_ij ∂ᵢu`
against `φ` along `e_j` (`ContDiffOn.hasWeakIteratedLineDerivOn_single`) for each pair `(i, j)`;
the first- and zeroth-order terms are read off almost everywhere. -/
theorem generalForm_eq_integral_of_contDiffOn (hu : ContDiffOn ℝ 2 u Ω)
    {a : Fin N → Fin N → EuclideanSpace ℝ (Fin N) → ℝ} (ha : ∀ i j, ContDiffOn ℝ 1 (a i j) Ω)
    {A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hA : ∀ i j, (A i j : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] a i j)
    {b : Fin N → EuclideanSpace ℝ (Fin N) → ℝ}
    {a₁ : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (ha₁ : ∀ i, (a₁ i : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] b i)
    {c : EuclideanSpace ℝ (Fin N) → ℝ}
    {a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (ha₀ : (a₀ : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] c)
    {U : SobolevEuclidean N 1 2 Ω}
    (hU : SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u)
    {V : SobolevEuclidean N 1 2 Ω} {φ : 𝓓(Ω, ℝ)}
    (hV : SobolevMultiIndex.fn V =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] φ) :
    generalForm Ω A a₁ a₀ U V = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      (-(∑ i : Fin N, ∑ j : Fin N, fderiv ℝ (fun y ↦ a i j y * fderiv ℝ u y
          (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1))
        + (∑ i : Fin N, b i x * fderiv ℝ u x (EuclideanSpace.single i 1)) + c x * u x) * φ x := by
  have hΩo := Ω.isOpen
  have hΩm := hΩo.measurableSet
  have hu1 : ContDiffOn ℝ 1 u Ω := hu.of_le (by norm_num)
  have hUd := weakDeriv_single_ae_eq_fderiv_of_contDiffOn Ω hu1 hU
  have hVd : ∀ j : Fin N,
      (SobolevMultiIndex.weakDeriv V (MultiIndexLE.single j) : EuclideanSpace ℝ (Fin N) → ℝ)
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
          fun x ↦ fderiv ℝ φ x (EuclideanSpace.single j 1) := fun j ↦ by
    have h := SobolevMultiIndexZero.weakDeriv_single_ae_eq_testFunction hV j
    rwa [EuclideanSpace.basisFun_toBasis_apply] at h
  -- `a_ij ∂ᵢu` is `C^1` on `Ω`, so its weak derivative along `e_j` is `∂ⱼ(a_ij ∂ᵢu)`
  have hg : ∀ i j : Fin N,
      ContDiffOn ℝ 1 (fun y ↦ a i j y * fderiv ℝ u y (EuclideanSpace.single i 1)) Ω :=
    fun i j ↦ (ha i j).mul ((hu.fderiv_of_isOpen hΩo le_rfl).clm_apply contDiffOn_const)
  have hibp : ∀ i j : Fin N, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      a i j x * fderiv ℝ u x (EuclideanSpace.single i 1) * fderiv ℝ φ x (EuclideanSpace.single j 1)
      = -∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), φ x
        * fderiv ℝ (fun y ↦ a i j y * fderiv ℝ u y (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single j 1) := by
    intro i j
    have h := ((hg i j).hasWeakIteratedLineDerivOn_single Ω j).integral_smul_eq φ
    simp only [iteratedFDeriv_one_apply, Matrix.cons_val_zero, smul_eq_mul, pow_one,
      neg_one_mul] at h
    rw [← h]
    congr 1
    funext x
    ring
  -- integrability of the pieces
  have hI2 : ∀ i j : Fin N, Integrable (fun x ↦ φ x
      * fderiv ℝ (fun y ↦ a i j y * fderiv ℝ u y (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single j 1))
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := fun i j ↦ by
    have := ((hg i j).hasWeakIteratedLineDerivOn_single Ω j).integrable_smul_weakDeriv φ
    simp only [smul_eq_mul] at this
    exact this.integrableOn
  have hI1 : ∀ i : Fin N, Integrable (fun x ↦ b i x * fderiv ℝ u x (EuclideanSpace.single i 1)
      * φ x) (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := fun i ↦
    (integrable_mul_mul Ω (a₁ i) (SobolevMultiIndex.weakDeriv U (MultiIndexLE.single i))
      (SobolevMultiIndex.weakDeriv V 0)).congr (((ha₁ i).mul (hUd i)).mul hV)
  have hI0 : Integrable (fun x ↦ c x * u x * φ x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    (integrable_mul_mul Ω a₀ (SobolevMultiIndex.weakDeriv U 0)
      (SobolevMultiIndex.weakDeriv V 0)).congr ((ha₀.mul hU).mul hV)
  -- the left-hand side as integrals of classical quantities
  have e2 : ∀ i j : Fin N, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), A i j x
      * SobolevMultiIndex.weakDeriv U (MultiIndexLE.single i) x
      * SobolevMultiIndex.weakDeriv V (MultiIndexLE.single j) x
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), a i j x
        * fderiv ℝ u x (EuclideanSpace.single i 1) * fderiv ℝ φ x (EuclideanSpace.single j 1) :=
    fun i j ↦ integral_congr_ae (((hA i j).mul (hUd i)).mul (hVd j))
  have e1 : ∀ i : Fin N, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), a₁ i x
      * SobolevMultiIndex.weakDeriv U (MultiIndexLE.single i) x
      * SobolevMultiIndex.weakDeriv V 0 x
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        b i x * fderiv ℝ u x (EuclideanSpace.single i 1) * φ x :=
    fun i ↦ integral_congr_ae (((ha₁ i).mul (hUd i)).mul hV)
  have e0 : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), a₀ x
      * SobolevMultiIndex.weakDeriv U 0 x * SobolevMultiIndex.weakDeriv V 0 x
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), c x * u x * φ x :=
    integral_congr_ae ((ha₀.mul hU).mul hV)
  -- the right-hand side, split
  have e3 : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      (-(∑ i : Fin N, ∑ j : Fin N, fderiv ℝ (fun y ↦ a i j y * fderiv ℝ u y
          (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1))
        + (∑ i : Fin N, b i x * fderiv ℝ u x (EuclideanSpace.single i 1)) + c x * u x) * φ x
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        (-(∑ i : Fin N, ∑ j : Fin N, φ x * fderiv ℝ (fun y ↦ a i j y * fderiv ℝ u y
            (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1))
          + (∑ i : Fin N, b i x * fderiv ℝ u x (EuclideanSpace.single i 1) * φ x)
          + c x * u x * φ x) := by
    congr 1
    funext x
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have e4 : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        (-(∑ i : Fin N, ∑ j : Fin N, φ x * fderiv ℝ (fun y ↦ a i j y * fderiv ℝ u y
            (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1))
          + (∑ i : Fin N, b i x * fderiv ℝ u x (EuclideanSpace.single i 1) * φ x)
          + c x * u x * φ x)
      = (∑ i : Fin N, ∑ j : Fin N, -∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          φ x * fderiv ℝ (fun y ↦ a i j y * fderiv ℝ u y (EuclideanSpace.single i 1)) x
            (EuclideanSpace.single j 1))
        + (∑ i : Fin N, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          b i x * fderiv ℝ u x (EuclideanSpace.single i 1) * φ x)
        + ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), c x * u x * φ x := by
    have hs2 : Integrable (fun x ↦ ∑ i : Fin N, ∑ j : Fin N, φ x
        * fderiv ℝ (fun y ↦ a i j y * fderiv ℝ u y (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single j 1)) (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
      integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hI2 i j
    have hs1 : Integrable (fun x ↦ ∑ i : Fin N,
        b i x * fderiv ℝ u x (EuclideanSpace.single i 1) * φ x)
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
      integrable_finsetSum _ fun i _ ↦ hI1 i
    have h2n : Integrable (fun x ↦ -(∑ i : Fin N, ∑ j : Fin N, φ x
        * fderiv ℝ (fun y ↦ a i j y * fderiv ℝ u y (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single j 1))) (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
      hs2.neg
    have h12 : Integrable (fun x ↦ -(∑ i : Fin N, ∑ j : Fin N, φ x
        * fderiv ℝ (fun y ↦ a i j y * fderiv ℝ u y (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single j 1))
        + ∑ i : Fin N, b i x * fderiv ℝ u x (EuclideanSpace.single i 1) * φ x)
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := h2n.add hs1
    rw [integral_add h12 hI0, integral_add h2n hs1, integral_neg,
      integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hI2 i j,
      integral_finsetSum _ fun i _ ↦ hI1 i]
    simp only [Finset.sum_neg_distrib]
    congr 3
    exact Finset.sum_congr rfl fun i _ ↦ integral_finsetSum _ fun j _ ↦ hI2 i j
  rw [generalForm_apply_inner]
  simp only [inner_mulL_eq_integral]
  rw [e3, e4, e0]
  congr 2
  · exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by rw [e2, hibp]
  · exact Finset.sum_congr rfl fun i _ ↦ e1 i

/-- **The interior half of Step A of Example 3**: let `Ω ⊆ ℝ^N` be open and bounded,
`u ∈ C²(Ω̄)` (`ContDiffOnClosure ℝ 2 u Ω`), `a_ij ∈ C¹(Ω)`, and let the `L^∞` coefficients `A i j`,
`a₁ i`, `a₀` agree almost everywhere on `Ω` with `a_ij`, `b_i`, `c`. If `f ∈ L²(Ω)` and
`-∑ᵢⱼ ∂ⱼ(a_ij ∂ᵢu) + ∑ᵢ b_i ∂ᵢu + c u = f` on `Ω`, then `u` is the function of some
`U ∈ H^1(Ω)` with `a(U, v) = ∫_Ω f v` for every `v ∈ H^1_0(Ω)`, `a` being the form (41)
`generalForm Ω A a₁ a₀`. No boundary condition enters; the homogeneous Dirichlet problem adds
`U ∈ H^1_0(Ω)` by Theorem 9.17 (`Elliptic.isGalerkinSolution_general_of_classical`).

Proof ([brezis2011functional] §9.5, Example 3, "as above, any classical solution is a weak
solution"): `u ∈ W^{1,2}(Ω)` (`ContDiffOnClosure.memSobolevMultiIndex_of_isBounded`), hence the
function of some `U ∈ H^1(Ω)`; for a test function `v`, `a(U, v) = ∫_Ω f v` is the integration by
parts `Elliptic.generalForm_eq_integral_of_contDiffOn`, and the identity extends to `H^1_0(Ω)`
by density (`SobolevMultiIndexZero.eqOn_of_eqOn_testFunctions`). -/
theorem exists_sobolev_forall_generalForm_eq_load_of_classical
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (hu : ContDiffOnClosure ℝ 2 u Ω)
    {a : Fin N → Fin N → EuclideanSpace ℝ (Fin N) → ℝ} (ha : ∀ i j, ContDiffOn ℝ 1 (a i j) Ω)
    {A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hA : ∀ i j, (A i j : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] a i j)
    {b : Fin N → EuclideanSpace ℝ (Fin N) → ℝ}
    {a₁ : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (ha₁ : ∀ i, (a₁ i : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] b i)
    {c : EuclideanSpace ℝ (Fin N) → ℝ}
    {a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (ha₀ : (a₀ : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] c)
    {f : EuclideanSpace ℝ (Fin N) → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (heq : ∀ x ∈ Ω, -(∑ i : Fin N, ∑ j : Fin N, fderiv ℝ (fun y ↦ a i j y * fderiv ℝ u y
        (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1))
      + (∑ i : Fin N, b i x * fderiv ℝ u x (EuclideanSpace.single i 1)) + c x * u x = f x) :
    ∃ U : SobolevEuclidean N 1 2 Ω,
      SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u ∧
        ∀ v ∈ SobolevEuclideanZero N 1 2 Ω,
          generalForm Ω A a₁ a₀ U v = load Ω (hf.toLp f) v := by
  have hΩm := Ω.isOpen.measurableSet
  have hu1 : ContDiffOnClosure ℝ 1 u Ω := hu.of_le (by norm_num)
  obtain ⟨U, hU⟩ := (hu1.memSobolevMultiIndex_of_isBounded Ω hΩ 2).exists_sobolevMultiIndex
  refine ⟨U, hU, SobolevMultiIndexZero.eqOn_of_eqOn_testFunctions
    (generalForm Ω A a₁ a₀ U).continuous (load Ω (hf.toLp f)).continuous ?_⟩
  rintro V ⟨φ, hV⟩
  rw [generalForm_eq_integral_of_contDiffOn Ω hu.contDiffOn ha hA ha₁ ha₀ hU hV, load_apply]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem hΩm, hf.coeFn_toLp, hV] with x hx hfx hVx
  rw [heq x hx, hfx, hVx]

/-- **Step A of Example 3: a classical solution of the general second-order equation is a weak
solution.** Let `Ω ⊆ ℝ^N` be open and bounded, `u ∈ C²(Ω̄)` (`ContDiffOnClosure ℝ 2 u Ω`,
continuous on `closure Ω`) with `u = 0` on `∂Ω`, let `a_ij ∈ C¹(Ω)`, and let the `L^∞`
coefficients `A i j`, `a₁ i`, `a₀` agree almost everywhere on `Ω` with `a_ij`, `b_i`, `c`. If
`f ∈ L²(Ω)` and `-∑ᵢⱼ ∂ⱼ(a_ij ∂ᵢu) + ∑ᵢ b_i ∂ᵢu + c u = f` on `Ω`, then `u` is the function of
some `U ∈ H^1_0(Ω)`, and `U` is the weak solution:
`IsGalerkinSolution (generalForm Ω A a₁ a₀) (load Ω f) (H^1_0(Ω)) U`. The book's (37) is the case
`a₁ = 0`, `b = 0`, with `a_ij ∈ C¹(Ω̄)` and `a₀ ∈ C(Ω̄)` supplying the `L^∞` classes
([brezis2011functional] §9.5, Example 3, "as above, any classical solution is a weak solution").

Proof: the interior identity is `Elliptic.exists_sobolev_forall_generalForm_eq_load_of_classical`,
and `U ∈ H^1_0(Ω)` by Theorem 9.17 (i) ⇒ (ii), which needs no regularity of `Ω`. -/
theorem isGalerkinSolution_general_of_classical
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (hu : ContDiffOnClosure ℝ 2 u Ω)
    (huc : ContinuousOn u (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (h0 : EqOn u 0 (frontier Ω))
    {a : Fin N → Fin N → EuclideanSpace ℝ (Fin N) → ℝ} (ha : ∀ i j, ContDiffOn ℝ 1 (a i j) Ω)
    {A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hA : ∀ i j, (A i j : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] a i j)
    {b : Fin N → EuclideanSpace ℝ (Fin N) → ℝ}
    {a₁ : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (ha₁ : ∀ i, (a₁ i : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] b i)
    {c : EuclideanSpace ℝ (Fin N) → ℝ}
    {a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (ha₀ : (a₀ : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] c)
    {f : EuclideanSpace ℝ (Fin N) → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (heq : ∀ x ∈ Ω, -(∑ i : Fin N, ∑ j : Fin N, fderiv ℝ (fun y ↦ a i j y * fderiv ℝ u y
        (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1))
      + (∑ i : Fin N, b i x * fderiv ℝ u x (EuclideanSpace.single i 1)) + c x * u x = f x) :
    ∃ U ∈ SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u ∧
        IsGalerkinSolution (generalForm Ω A a₁ a₀) (load Ω (hf.toLp f))
          (SobolevEuclideanZero N 1 2 Ω) U := by
  obtain ⟨U, hU, hUw⟩ :=
    exists_sobolev_forall_generalForm_eq_load_of_classical Ω hΩ hu ha hA ha₁ ha₀ hf heq
  have hU0 : U ∈ SobolevEuclideanZero N 1 2 Ω :=
    SobolevEuclideanZero.mem_of_continuousOn_closure_of_eqOn_frontier (by norm_num) U hU huc h0
  exact ⟨U, hU0, hU, hU0, hUw⟩

end Classical



/-! ### The Fredholm alternative for a second-kind equation, abstractly -/

section Abstract

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

omit [CompleteSpace X] in
/-- `(1 • 1 - μ • T) v = v - μ T v`. -/
theorem one_smul_one_sub_smul_apply (T : X →L[ℝ] X) (μ : ℝ) (v : X) :
    ((1 : ℝ) • (1 : X →L[ℝ] X) - μ • T) v = v - μ • T v := by
  simp

/-- **The Fredholm alternative for a solvability predicate**: if `P f` holds exactly when
`f ∈ range (μ • 1 - K)`, for a compact `K` on a real Hilbert space and `μ ≠ 0`, then there is a
finite-dimensional subspace `F`, of the dimension of `ker (μ • 1 - K)`, such that `P f` holds iff
`f ⊥ F`: `F = ker (μ • 1 - K†)`, by `IsCompactOperator.range_smul_sub_eq_orthogonal_ker_adjoint`
and `IsCompactOperator.finrank_ker_eq_finrank_ker_adjoint` ([brezis2011functional]
Theorem 6.6 (b), (d), in Hilbert space). -/
theorem exists_finiteDimensional_forall_iff_inner_eq_zero {K : X →L[ℝ] X}
    (hK : IsCompactOperator K) {μ : ℝ} (hμ : μ ≠ 0) {P : X → Prop}
    (hP : ∀ f, P f ↔ f ∈ (μ • (1 : X →L[ℝ] X) - K).range) :
    ∃ F : Submodule ℝ X, FiniteDimensional ℝ F ∧
      finrank ℝ F = finrank ℝ (μ • (1 : X →L[ℝ] X) - K).ker ∧
        ∀ f, P f ↔ ∀ v ∈ F, ⟪f, v⟫_ℝ = 0 := by
  refine ⟨((starRingEnd ℝ) μ • (1 : X →L[ℝ] X) - ContinuousLinearMap.adjoint K).ker, ?_, ?_,
    fun f ↦ ?_⟩
  · have h1 := hK.adjoint.finiteDimensional_ker_pow
      (by simpa using hμ : (starRingEnd ℝ) μ ≠ 0) 1
    rwa [pow_one] at h1
  · exact (hK.finrank_ker_eq_finrank_ker_adjoint hμ).symm
  · rw [hP, hK.range_smul_sub_eq_orthogonal_ker_adjoint hμ, Submodule.mem_orthogonal]
    exact forall₂_congr fun v _ ↦ by rw [real_inner_comm]

/-- **The Fredholm alternative, existence from uniqueness**: a compact perturbation `μ • 1 - K`
of a nonzero multiple of the identity with trivial kernel is surjective
(`IsCompactOperator.injective_iff_surjective_smul_one_sub`). -/
theorem surjective_smul_one_sub_of_ker_eq_bot {K : X →L[ℝ] X} (hK : IsCompactOperator K) {μ : ℝ}
    (hμ : μ ≠ 0) (h : (μ • (1 : X →L[ℝ] X) - K).ker = ⊥) :
    Function.Surjective (μ • (1 : X →L[ℝ] X) - K) :=
  (hK.injective_iff_surjective_smul_one_sub hμ).1 (LinearMap.ker_eq_bot.1 h)

end Abstract

/-! ### Theorem 9.23: the Fredholm alternative for (40), modulo compactness of `T` -/

section Fredholm

variable (a : SesqForm ℝ (SobolevEuclidean N 1 2 Ω))

/-- **The space of weak solutions of the homogeneous problem (40)**,
`{u ∈ H^1_0(Ω) | ∀ v ∈ H^1_0(Ω), a(u, v) = 0}`, as a subspace of `H^1(Ω)`
([brezis2011functional] Theorem 9.23, "the space `N` of solutions of (40) with `f = 0`"). -/
def homogeneousKernel : Submodule ℝ (SobolevEuclidean N 1 2 Ω) where
  carrier := {u | u ∈ SobolevEuclideanZero N 1 2 Ω ∧
    ∀ v ∈ SobolevEuclideanZero N 1 2 Ω, a u v = 0}
  zero_mem' := ⟨zero_mem _, fun v _ ↦ by simp⟩
  add_mem' {u w} hu hw := ⟨add_mem hu.1 hw.1, fun v hv ↦ by
    have e : a (u + w) = a u + a w := map_add _ _ _
    rw [e, add_apply, hu.2 v hv, hw.2 v hv, add_zero]⟩
  smul_mem' c u hu := ⟨Submodule.smul_mem _ c hu.1, fun v hv ↦ by
    have e : a (c • u) = c • a u := by rw [map_smulₛₗ, conj_trivial]
    rw [e, smul_apply, hu.2 v hv, smul_zero]⟩

/-- Membership of `Elliptic.homogeneousKernel`, unfolded. -/
theorem mem_homogeneousKernel_iff {u : SobolevEuclidean N 1 2 Ω} :
    u ∈ homogeneousKernel Ω a ↔ u ∈ SobolevEuclideanZero N 1 2 Ω ∧
      ∀ v ∈ SobolevEuclideanZero N 1 2 Ω, a u v = 0 :=
  Iff.rfl

/-- The homogeneous solutions lie in `H^1_0(Ω)`. -/
theorem homogeneousKernel_le : homogeneousKernel Ω a ≤ SobolevEuclideanZero N 1 2 Ω :=
  fun _ hu ↦ hu.1

/-- The homogeneous solutions are the Galerkin solutions with datum `0`. -/
theorem mem_homogeneousKernel_iff_isGalerkinSolution {u : SobolevEuclidean N 1 2 Ω} :
    u ∈ homogeneousKernel Ω a ↔
      IsGalerkinSolution a (load Ω 0) (SobolevEuclideanZero N 1 2 Ω) u := by
  simp only [mem_homogeneousKernel_iff, IsGalerkinSolution, load_apply_inner, inner_zero_left]

/-- The shifted form `a_μ = a + μ ⟪·, ·⟫_{L²}`, applied. -/
theorem add_smul_pairing_apply (μ : ℝ) (u v : SobolevEuclidean N 1 2 Ω) :
    (a + μ • pairing Ω (ContinuousLinearMap.id ℝ _) 0 0) u v
      = a u v + μ * ⟪SobolevMultiIndex.weakDeriv u 0, SobolevMultiIndex.weakDeriv v 0⟫_ℝ := by
  simp only [add_apply, smul_apply, pairing_apply, ContinuousLinearMap.id_apply, smul_eq_mul]

/-- The load of `f + μ g`. -/
theorem load_add_smul (f g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (μ : ℝ) (v : SobolevEuclidean N 1 2 Ω) :
    load Ω (f + μ • g) v = load Ω f v + μ * load Ω g v := by
  simp only [load_apply_inner, inner_add_left, real_inner_smul_left]

variable {μ : ℝ}
  (ha : ((a + μ • pairing Ω (ContinuousLinearMap.id ℝ _) 0 0).restrict
    (SobolevEuclideanZero N 1 2 Ω)).IsCoercive)

/-- **(40) is a fixed-point equation for the shifted solution map**: `u ∈ H^1_0(Ω)` is a weak
solution of `a(u, v) = ⟨f, v⟩` for all `v ∈ H^1_0(Ω)` iff `u = T_μ (f + μ u)`, where `T_μ` is the
solution map of the coercive shifted form `a_μ = a + μ ⟪·, ·⟫_{L²}`: the sentence
"`u` is a solution of (40) iff `u = T(f + λu)`" of the proof of [brezis2011functional]
Theorem 9.23. -/
theorem isGalerkinSolution_iff_eq_solutionMap
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (u : SobolevEuclidean N 1 2 Ω) :
    IsGalerkinSolution a (load Ω f) (SobolevEuclideanZero N 1 2 Ω) u ↔
      u = solutionMap Ω _ ha
        (f + μ • SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
          volume u) := by
  have key : IsGalerkinSolution a (load Ω f) (SobolevEuclideanZero N 1 2 Ω) u ↔
      IsGalerkinSolution (a + μ • pairing Ω (ContinuousLinearMap.id ℝ _) 0 0)
        (load Ω (f + μ • SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
          volume u)) (SobolevEuclideanZero N 1 2 Ω) u := by
    refine and_congr_right fun _ ↦ forall₂_congr fun v hv ↦ ?_
    rw [add_smul_pairing_apply, load_add_smul, load_apply_inner, load_apply_inner,
      SobolevMultiIndex.fnL_eq_weakDeriv_zero, add_left_inj]
  rw [key]
  constructor
  · exact eq_solutionMap_of_isGalerkinSolution Ω _ ha
  · intro h
    have := isGalerkinSolution_solutionMap Ω _ ha
      (f + μ • SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume u)
    rwa [← h] at this

/-- **The homogeneous solutions are the fixed points of `μ T_μ` in `L²(Ω)`**: `u ∈ H^1(Ω)` lies in
`homogeneousKernel Ω a` iff `u = T_μ (μ u)`. -/
theorem mem_homogeneousKernel_iff_eq_solutionMap (u : SobolevEuclidean N 1 2 Ω) :
    u ∈ homogeneousKernel Ω a ↔
      u = solutionMap Ω _ ha
        (μ • SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
          volume u) := by
  rw [mem_homogeneousKernel_iff_isGalerkinSolution, isGalerkinSolution_iff_eq_solutionMap Ω a ha,
    zero_add]

/-- **The homogeneous solutions, read in `L²(Ω)`**: the linear map
`homogeneousKernel Ω a → L²(Ω)`, `u ↦ u`. -/
def homogeneousKernelToLp :
    homogeneousKernel Ω a →ₗ[ℝ] Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  (SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume :
    SobolevEuclidean N 1 2 Ω →ₗ[ℝ] _) ∘ₗ (homogeneousKernel Ω a).subtype

/-- `homogeneousKernelToLp Ω a u` is the function of `u`. -/
theorem homogeneousKernelToLp_apply (u : homogeneousKernel Ω a) :
    homogeneousKernelToLp Ω a u
      = SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume u :=
  rfl

/-- The map `homogeneousKernel Ω a → L²(Ω)` is injective: an element of `H^1(Ω)` is determined by
its function (`SobolevMultiIndex.fnL_injective`). -/
theorem homogeneousKernelToLp_injective : Function.Injective (homogeneousKernelToLp Ω a) :=
  fun _ _ h ↦ Subtype.ext (SobolevMultiIndex.fnL_injective h)

/-- **The homogeneous solutions, in `L²(Ω)`, are the kernel of `1 - μ T_μ`**: the range of
`homogeneousKernelToLp Ω a` is `ker (1 • 1 - μ • solutionOperator Ω a_μ _)`. So the space of
solutions of the homogeneous problem (40) is isomorphic to `N(I - λT)` of the proof of
[brezis2011functional] Theorem 9.23. -/
theorem range_homogeneousKernelToLp :
    LinearMap.range (homogeneousKernelToLp Ω a)
      = ((1 : ℝ) • (1 : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →L[ℝ]
          Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
        - μ • solutionOperator Ω _ ha).ker := by
  ext w
  rw [LinearMap.mem_range, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    one_smul_one_sub_smul_apply, sub_eq_zero]
  constructor
  · rintro ⟨u, rfl⟩
    have hu := (mem_homogeneousKernel_iff_eq_solutionMap Ω a ha u).1 u.2
    rw [homogeneousKernelToLp_apply, ← map_smul (solutionOperator Ω _ ha), solutionOperator_apply,
      SobolevMultiIndexZero.fnL_eq, ← hu]
  · intro hw
    have hT : SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
        (solutionMap Ω _ ha (μ • w)) = w := by
      rw [← SobolevMultiIndexZero.fnL_eq, ← solutionOperator_apply,
        map_smul (solutionOperator Ω _ ha), ← hw]
    refine ⟨⟨solutionMap Ω _ ha (μ • w), ?_⟩, hT⟩
    rw [mem_homogeneousKernel_iff_eq_solutionMap Ω a ha, hT]

/-- **The first half of Theorem 9.23, modulo compactness of `T_μ`**: if the solution operator
`T_μ : L²(Ω) → L²(Ω)` of the coercive shifted form is compact, then the space of solutions of the
homogeneous problem (40) is finite-dimensional. It is isomorphic to `ker (1 - μ T_μ)`
(`Elliptic.range_homogeneousKernelToLp`), which is finite-dimensional by the Riesz theory
(`IsCompactOperator.finiteDimensional_ker_pow`). The compactness hypothesis is
`Elliptic.solutionOperator_isCompactOperator`, for `Ω` bounded ([brezis2011functional]
Theorem 9.23, proof, and Theorem 6.6 (a)). -/
theorem finiteDimensional_homogeneousKernel_of_isCompactOperator
    (hT : IsCompactOperator (solutionOperator Ω _ ha)) :
    FiniteDimensional ℝ (homogeneousKernel Ω a) := by
  have hK : IsCompactOperator (μ • solutionOperator Ω _ ha) := hT.smul μ
  have h1 := hK.finiteDimensional_ker_pow one_ne_zero 1
  rw [pow_one] at h1
  have h2 : FiniteDimensional ℝ (LinearMap.range (homogeneousKernelToLp Ω a)) := by
    rw [range_homogeneousKernelToLp Ω a ha]
    exact h1
  exact (LinearEquiv.ofInjective _ (homogeneousKernelToLp_injective Ω a)).symm.finiteDimensional

/-- The dimension of the space of homogeneous solutions is that of `ker (1 - μ T_μ)`. -/
theorem finrank_homogeneousKernel :
    finrank ℝ (homogeneousKernel Ω a)
      = finrank ℝ (((1 : ℝ) • (1 : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
          →L[ℝ] Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
        - μ • solutionOperator Ω _ ha).ker) := by
  rw [← range_homogeneousKernelToLp Ω a ha]
  exact (LinearEquiv.ofInjective _ (homogeneousKernelToLp_injective Ω a)).finrank_eq

/-- **(40) is solvable iff `f ∈ range (1 - μ T_μ)`**: the weak problem `a(u, v) = ⟨f, v⟩` for all
`v ∈ H^1_0(Ω)` has a solution `u ∈ H^1_0(Ω)` iff `v - μ T_μ v = f` has a solution `v ∈ L²(Ω)`
(then `u = T_μ v`; conversely `v = f + μ u`): the reduction of the proof of
[brezis2011functional] Theorem 9.23. -/
theorem exists_isGalerkinSolution_iff_mem_range
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    (∃ u, IsGalerkinSolution a (load Ω f) (SobolevEuclideanZero N 1 2 Ω) u) ↔
      f ∈ ((1 : ℝ) • (1 : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →L[ℝ]
          Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
        - μ • solutionOperator Ω _ ha).range := by
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨u, hu⟩
    rw [isGalerkinSolution_iff_eq_solutionMap Ω a ha] at hu
    refine ⟨f + μ • SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
      volume u, ?_⟩
    rw [ContinuousLinearMap.coe_coe, one_smul_one_sub_smul_apply, solutionOperator_apply,
      SobolevMultiIndexZero.fnL_eq, ← hu, add_sub_cancel_right]
  · rintro ⟨v, hv⟩
    rw [ContinuousLinearMap.coe_coe, one_smul_one_sub_smul_apply, solutionOperator_apply,
      SobolevMultiIndexZero.fnL_eq, sub_eq_iff_eq_add] at hv
    refine ⟨solutionMap Ω _ ha v, ?_⟩
    rw [isGalerkinSolution_iff_eq_solutionMap Ω a ha, ← hv]

/-- **The second half of Theorem 9.23, modulo compactness of `T_μ`** (the Fredholm alternative
for (40)): if the solution operator `T_μ` of the coercive shifted form is compact, there is a
finite-dimensional subspace `F ⊆ L²(Ω)` of the same dimension as the space of homogeneous
solutions such that, for every `f ∈ L²(Ω)`, the problem (40) has a solution iff `f ⊥ F`:
`F = ker (1 - μ T_μ†)`, by the solvability criterion
`IsCompactOperator.range_smul_sub_eq_orthogonal_ker_adjoint` and the index formula
`IsCompactOperator.finrank_ker_eq_finrank_ker_adjoint` on the Hilbert space `L²(Ω)`
([brezis2011functional] Theorem 9.23, proof, and Theorem 6.6 (b), (d)). -/
theorem exists_orthogonality_iff_exists_solution_of_isCompactOperator
    (hT : IsCompactOperator (solutionOperator Ω _ ha)) :
    ∃ F : Submodule ℝ (Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))),
      FiniteDimensional ℝ F ∧ finrank ℝ F = finrank ℝ (homogeneousKernel Ω a) ∧
        ∀ f, (∃ u, IsGalerkinSolution a (load Ω f) (SobolevEuclideanZero N 1 2 Ω) u) ↔
          ∀ v ∈ F, ⟪f, v⟫_ℝ = 0 := by
  obtain ⟨F, h1, h2, h3⟩ := exists_finiteDimensional_forall_iff_inner_eq_zero (hT.smul μ)
    one_ne_zero (exists_isGalerkinSolution_iff_mem_range Ω a ha)
  exact ⟨F, h1, h2.trans (finrank_homogeneousKernel Ω a ha).symm, h3⟩

/-- **Remark 23, first clause, modulo compactness of `T_μ`**: if the solution operator `T_μ` of
the coercive shifted form is compact and the homogeneous problem (40) has only the zero solution,
then (40) has exactly one weak solution for every `f ∈ L²(Ω)`. Existence is the Fredholm
alternative `IsCompactOperator.injective_iff_surjective_smul_one_sub` for `1 - μ T_μ`, whose
kernel is the image of the homogeneous solutions; uniqueness is that the difference of two
solutions is a homogeneous solution ([brezis2011functional] Chapter 9, Remark 23, and
Theorem 6.6 (c)). -/
theorem existsUnique_of_homogeneousKernel_eq_bot_of_isCompactOperator
    (hT : IsCompactOperator (solutionOperator Ω _ ha)) (h : homogeneousKernel Ω a = ⊥)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ∃! u, IsGalerkinSolution a (load Ω f) (SobolevEuclideanZero N 1 2 Ω) u := by
  have hker : ((1 : ℝ) • (1 : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
      →L[ℝ] Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
        - μ • solutionOperator Ω _ ha).ker = ⊥ := by
    rw [← range_homogeneousKernelToLp Ω a ha, LinearMap.range_eq_bot]
    ext u
    have hu : (u : SobolevEuclidean N 1 2 Ω) ∈ (⊥ : Submodule ℝ (SobolevEuclidean N 1 2 Ω)) :=
      h ▸ u.2
    rw [Submodule.mem_bot] at hu
    rw [homogeneousKernelToLp_apply, hu, map_zero, LinearMap.zero_apply]
  have hsurj := surjective_smul_one_sub_of_ker_eq_bot (hT.smul μ) one_ne_zero hker
  obtain ⟨u, hu⟩ := (exists_isGalerkinSolution_iff_mem_range Ω a ha f).2
    (LinearMap.mem_range.2 (hsurj f))
  refine ⟨u, hu, fun w hw ↦ ?_⟩
  have hmem : w - u ∈ homogeneousKernel Ω a := by
    refine ⟨sub_mem hw.1 hu.1, fun v hv ↦ ?_⟩
    have e : a (w - u) = a w - a u := map_sub _ _ _
    rw [e, sub_apply, hw.2 v hv, hu.2 v hv, sub_self]
  rw [h, Submodule.mem_bot, sub_eq_zero] at hmem
  exact hmem

end Fredholm

/-! ### Compactness of the solution operator, reduced to the embedding `H^1_0(Ω) ↪ L²(Ω)` -/

/-- **The solution operator is compact as soon as the inclusion `H^1_0(Ω) → L²(Ω)` is**: `T`
factors as `fnL ∘ solutionMap`, and a compact operator composed with a bounded one is compact
(`IsCompactOperator.comp_clm`). With the Rellich–Kondrachov theorem in the `W_0^{1,p}` form of
[brezis2011functional] Remark 20 (compactness of `H^1_0(Ω) ↪ L²(Ω)` for `Ω` bounded), this is
`Elliptic.solutionOperator_isCompactOperator`. -/
theorem solutionOperator_isCompactOperator_of_isCompactOperator_fnL
    (a : SesqForm ℝ (SobolevEuclidean N 1 2 Ω))
    (ha : (a.restrict (SobolevEuclideanZero N 1 2 Ω)).IsCoercive)
    (h : IsCompactOperator
      (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume)) :
    IsCompactOperator (solutionOperator Ω a ha) := by
  rw [solutionOperator, ContinuousLinearMap.coe_comp]
  exact h.comp_clm _


/-! ### Theorem 9.23 and Remark 23: the Fredholm alternative for the general Dirichlet problem -/

section Fredholm23

variable {A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {a₁ : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))} {α : ℝ}

/-- **Gårding's inequality on `H^1_0(Ω)`**: under the ellipticity condition (36), the shifted form
`a(u, v) + λ ∫_Ω u v` with the shift `λ` of `Elliptic.generalForm_garding` is coercive on
`H^1_0(Ω)`, so that its solution operator `Elliptic.solutionOperator` exists — the `T` of the
proof of [brezis2011functional] Theorem 9.23. -/
theorem generalForm_garding_restrict_isCoercive (hA : IsUniformlyElliptic Ω A α) :
    ((generalForm Ω A a₁ a₀ + ((∑ i, ‖a₁ i‖) ^ 2 / (2 * α) + ‖a₀‖ + α / 2)
      • pairing Ω (ContinuousLinearMap.id ℝ _) 0 0).restrict
        (SobolevEuclideanZero N 1 2 Ω)).IsCoercive :=
  SesqForm.IsCoercive.restrict ⟨α / 2, half_pos hA.1, generalForm_garding Ω hA⟩ _

/-- **The solution operator is compact** for an open set `Ω` of finite measure (in particular a
bounded one), for every form `a` coercive on `H^1_0(Ω)`: `T = fnL ∘ solutionMap` factors through
the inclusion `H^1_0(Ω) → L²(Ω)`, which is compact by the Rellich–Kondrachov theorem in the
`W_0^{1,p}` form of [brezis2011functional] Remark 20
(`SobolevEuclideanZero.isCompactOperator_fnL`, no regularity of `Ω`), and a compact operator
composed with a bounded one is compact. This is the sentence "`T : L² → L²` is a compact linear
operator (since `Ω` is bounded, the injection `H^1_0 ⊂ L²` is compact; see Theorem 9.16 and
Remark 20)" of the proof of Theorem 9.23, and the compactness of `T` in the proof of
Theorem 9.31. -/
theorem solutionOperator_isCompactOperator
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤)
    (a : SesqForm ℝ (SobolevEuclidean N 1 2 Ω))
    (ha : (a.restrict (SobolevEuclideanZero N 1 2 Ω)).IsCoercive) :
    IsCompactOperator (solutionOperator Ω a ha) :=
  solutionOperator_isCompactOperator_of_isCompactOperator_fnL Ω a ha
    (SobolevEuclideanZero.isCompactOperator_fnL ENNReal.ofNat_ne_top hΩ)

/-- **[brezis2011functional] Theorem 9.23, first half.** Let `Ω` be an open set of finite
measure (the book: bounded), `A`, `a₁`, `a₀` be `L^∞(Ω)` coefficients with the ellipticity
condition (36), `IsUniformlyElliptic Ω A α`, and `a = generalForm Ω A a₁ a₀` the form (41). The
space `N = {u ∈ H^1_0(Ω) | ∀ v ∈ H^1_0(Ω), a(u, v) = 0}` of weak solutions of the homogeneous
problem (40) (`Elliptic.homogeneousKernel`) is finite-dimensional. Proof: with `λ` from Gårding's
inequality (`Elliptic.generalForm_garding`), `T = solutionOperator` of the coercive shifted form
is compact (`Elliptic.solutionOperator_isCompactOperator`), and `u ∈ N` iff `u = λ T u` in
`L²(Ω)`, so `N ≅ ker (1 − λ T)` is finite-dimensional by the Riesz theory
(`Elliptic.finiteDimensional_homogeneousKernel_of_isCompactOperator`). -/
theorem finiteDimensional_ker_general (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤)
    (hA : IsUniformlyElliptic Ω A α) :
    FiniteDimensional ℝ (homogeneousKernel Ω (generalForm Ω A a₁ a₀)) :=
  finiteDimensional_homogeneousKernel_of_isCompactOperator Ω _
    (generalForm_garding_restrict_isCoercive Ω hA) (solutionOperator_isCompactOperator Ω hΩ _ _)

/-- **[brezis2011functional] Theorem 9.23, second half (the Fredholm alternative for (40)).**
Under the hypotheses of `Elliptic.finiteDimensional_ker_general` there is a finite-dimensional
subspace `F ⊆ L²(Ω)` with `dim F = dim N` (`N` the space of homogeneous solutions) such that,
for every `f ∈ L²(Ω)`, the weak problem `a(u, v) = ∫_Ω f v` for all `v ∈ H^1_0(Ω)` has a solution
`u ∈ H^1_0(Ω)` iff `f ⊥ F`: `F = ker (1 − λ T†)`, by the Hilbert-space Fredholm alternative
(`IsCompactOperator.range_smul_sub_eq_orthogonal_ker_adjoint`,
`IsCompactOperator.finrank_ker_eq_finrank_ker_adjoint`) for the compact solution operator `T`
of the shifted form; the book routes through its Theorem 6.6. -/
theorem exists_orthogonality_iff_exists_solution
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) (hA : IsUniformlyElliptic Ω A α) :
    ∃ F : Submodule ℝ (Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))),
      FiniteDimensional ℝ F ∧
        finrank ℝ F = finrank ℝ (homogeneousKernel Ω (generalForm Ω A a₁ a₀)) ∧
        ∀ f, (∃ u, IsGalerkinSolution (generalForm Ω A a₁ a₀) (load Ω f)
          (SobolevEuclideanZero N 1 2 Ω) u) ↔ ∀ v ∈ F, ⟪f, v⟫_ℝ = 0 :=
  exists_orthogonality_iff_exists_solution_of_isCompactOperator Ω _
    (generalForm_garding_restrict_isCoercive Ω hA) (solutionOperator_isCompactOperator Ω hΩ _ _)

/-- **[brezis2011functional] Chapter 9, Remark 23, first clause**: under the hypotheses of
Theorem 9.23, if the homogeneous problem (40) has only the zero solution
(`homogeneousKernel Ω a = ⊥`), then for every `f ∈ L²(Ω)` the weak problem (40) has exactly one
solution `u ∈ H^1_0(Ω)`. Existence is the Fredholm alternative
(`IsCompactOperator.injective_iff_surjective_smul_one_sub` for `1 − λ T`), uniqueness that the
difference of two solutions is a homogeneous solution. The remark's second clause — that
`a₀ ≥ 0` alone forces the trivial kernel — is the general case of Proposition 9.29, cited from
Gilbarg–Trudinger, and is not proved here. -/
theorem existsUnique_of_ker_eq_bot (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤)
    (hA : IsUniformlyElliptic Ω A α) (h : homogeneousKernel Ω (generalForm Ω A a₁ a₀) = ⊥)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ∃! u, IsGalerkinSolution (generalForm Ω A a₁ a₀) (load Ω f) (SobolevEuclideanZero N 1 2 Ω) u :=
  existsUnique_of_homogeneousKernel_eq_bot_of_isCompactOperator Ω _
    (generalForm_garding_restrict_isCoercive Ω hA) (solutionOperator_isCompactOperator Ω hΩ _ _)
    h f

end Fredholm23

end Elliptic
