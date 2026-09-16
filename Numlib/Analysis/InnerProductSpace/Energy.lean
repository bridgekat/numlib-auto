/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Numlib.Analysis.InnerProductSpace.Coercive

/-!
# Energy inner product and energy norm

For a symmetric coercive `A`, `⟪x, y⟫_A := ⟪A x, y⟫` is an inner product and
`‖x‖_A := √(re ⟪A x, x⟫)` the associated norm, classically called the energy inner product and
the energy (or `A`-) norm. `WithEnergy A hA` is a type synonym of `E` carrying this inner
product, so that Mathlib's orthogonal projection theory applies to `A`-orthogonal projections.

## Main definitions

* `energyInner A x y` and `energyNorm A x`, the energy inner product and the energy norm on `E`
  itself, defined for every `A` and useful without any hypothesis on it;
* `WithEnergy A hA`, the type synonym of `E` carrying the energy inner product of a symmetric
  coercive `A`, together with `WithEnergy.equiv`, the identity `E ≃ₗ[𝕜] WithEnergy A hA` along
  which Mathlib's inner product theory is imported;
* `energyFunctional A b`, the quadratic `x ↦ ½ re ⟪A x, x⟫ - re ⟪b, x⟫` (the *energy* of the
  system `A x = b`, [quarteroni2000numerical] §4.3.3 and (7.35)), whose gradient at `x` is
  `A x - b` for a real symmetric bounded `A` (`hasGradientAt_energyFunctional`) and whose
  excess over its minimum is half the squared energy norm of the error
  (`LinearMap.IsSymmetricCoercive.energyFunctional_sub_eq`).

## Notation

Scoped in `Energy`:

* `⟪x, y⟫_[A]` for `energyInner A x y`;
* `‖x‖_[A]` for `energyNorm A x`.

## Implementation notes

The plain algebraic instances on `WithEnergy A hA` are `local`: only the instances derived from
`WithEnergy.core` are global, following Mathlib's `Matrix.toInnerProductSpace` pattern, which
avoids an `AddCommMonoid` diamond between the two routes.
-/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The energy inner product `⟪x, y⟫_A = ⟪A x, y⟫`. -/
noncomputable def energyInner (A : E →ₗ[𝕜] E) (x y : E) : 𝕜 := inner 𝕜 (A x) y

/-- The energy norm `‖x‖_A = √(re ⟪A x, x⟫)`. -/
noncomputable def energyNorm (A : E →ₗ[𝕜] E) (x : E) : ℝ :=
  Real.sqrt (RCLike.re (inner 𝕜 (A x) x))

scoped[Energy] notation "⟪" x ", " y "⟫_[" A "]" => energyInner A x y
scoped[Energy] notation "‖" x "‖_[" A "]" => energyNorm A x

/-- The energy norm is nonnegative for every `A`, symmetric coercive or not, being a square
root. Keep it at hand: `positivity` does not see through `energyNorm`. -/
theorem energyNorm_nonneg (A : E →ₗ[𝕜] E) (x : E) : 0 ≤ energyNorm A x := Real.sqrt_nonneg _

/-- The energy functional `φ(x) = ½ re ⟪A x, x⟫ - re ⟪b, x⟫` of the system `A x = b`
([quarteroni2000numerical] §4.3.3, (7.35); [fong2012cg] (2.1)). For symmetric coercive `A` its
unique minimizer is the solution of `A x = b`, and Galerkin iterates minimize it over affine
subspaces (`IsGalerkin.quadratic_le` in `Numlib/Projection/Optimality`). It is defined for every
`A`; the hypotheses enter only in the statements about it. -/
noncomputable def energyFunctional (A : E →ₗ[𝕜] E) (b x : E) : ℝ :=
  RCLike.re (inner 𝕜 (A x) x) / 2 - RCLike.re (inner 𝕜 b x)

namespace LinearMap

variable {A : E →ₗ[𝕜] E}

/-- The energy form of a symmetric coercive `A` as a `PreInnerProductSpace.Core` on `E` itself.
It is only used to get Cauchy–Schwarz before the type synonym `WithEnergy` is available. -/
@[instance_reducible]
private noncomputable def energyPreCore (hA : A.IsSymmetricCoercive) :
    PreInnerProductSpace.Core 𝕜 E where
  inner x y := inner 𝕜 (A x) y
  conj_inner_symm x y := by
    show starRingEnd 𝕜 (inner 𝕜 (A y) x) = inner 𝕜 (A x) y
    rw [inner_conj_symm, hA.isSymmetric x y]
  re_inner_nonneg x := hA.isPositive.re_inner_nonneg_left x
  add_left x y z := by show inner 𝕜 (A (x + y)) z = _; simp [inner_add_left]
  smul_left x y r := by show inner 𝕜 (A (r • x)) y = _; simp [inner_smul_left]

/-- Squaring undoes the square root: `‖x‖_A² = re ⟪A x, x⟫`. This is the form to rewrite with,
since the quadratic form is what every estimate actually manipulates. -/
theorem IsSymmetricCoercive.energyNorm_sq (hA : A.IsSymmetricCoercive) (x : E) :
    energyNorm A x ^ 2 = RCLike.re (inner 𝕜 (A x) x) :=
  Real.sq_sqrt (hA.isPositive.re_inner_nonneg_left x)

/-- The energy norm is definite: it vanishes only at `0`. This is where coercivity is used —
positivity alone would leave a seminorm. -/
theorem IsSymmetricCoercive.energyNorm_eq_zero_iff (hA : A.IsSymmetricCoercive) {x : E} :
    energyNorm A x = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h, energyNorm]⟩
  by_contra hx
  have hpos := hA.isCoercive.inner_self_pos hx
  rw [← hA.energyNorm_sq, h] at hpos
  simp at hpos

/-- The energy norm is strictly positive away from the origin. -/
theorem IsSymmetricCoercive.energyNorm_pos (hA : A.IsSymmetricCoercive) {x : E} (hx : x ≠ 0) :
    0 < energyNorm A x :=
  (energyNorm_nonneg A x).lt_of_ne fun h => hx (hA.energyNorm_eq_zero_iff.1 h.symm)

/-- Lower norm equivalence `√c ‖x‖ ≤ ‖x‖_A`. -/
theorem IsCoerciveWith.norm_le_energyNorm {c : ℝ} (hc : 0 ≤ c) (hA : A.IsCoerciveWith c) (x : E) :
    Real.sqrt c * ‖x‖ ≤ energyNorm A x := by
  have h1 : Real.sqrt c * ‖x‖ = Real.sqrt (c * ‖x‖ ^ 2) := by
    rw [Real.sqrt_mul hc, Real.sqrt_sq (norm_nonneg x)]
  rw [h1, energyNorm]
  exact Real.sqrt_le_sqrt (hA x)

/-- Upper norm equivalence `‖x‖_A ≤ √‖A‖ ‖x‖` for bounded `A`. -/
theorem IsSymmetricCoercive.energyNorm_le_norm {A : E →L[𝕜] E}
    (hA : (A : E →ₗ[𝕜] E).IsSymmetricCoercive) (x : E) :
    energyNorm (A : E →ₗ[𝕜] E) x ≤ Real.sqrt ‖A‖ * ‖x‖ := by
  have hsq : energyNorm (A : E →ₗ[𝕜] E) x ^ 2 ≤ (Real.sqrt ‖A‖ * ‖x‖) ^ 2 := by
    rw [hA.energyNorm_sq, mul_pow, Real.sq_sqrt (norm_nonneg A)]
    calc RCLike.re (inner 𝕜 (A x) x) ≤ ‖inner 𝕜 (A x) x‖ := RCLike.re_le_norm _
      _ ≤ ‖A x‖ * ‖x‖ := norm_inner_le_norm _ _
      _ ≤ ‖A‖ * ‖x‖ * ‖x‖ := by gcongr; exact A.le_opNorm x
      _ = ‖A‖ * ‖x‖ ^ 2 := by ring
  have h1 := energyNorm_nonneg (A : E →ₗ[𝕜] E) x
  have h2 : (0 : ℝ) ≤ Real.sqrt ‖A‖ * ‖x‖ := by positivity
  nlinarith

/-- The energy norm of the error against the residual: `‖x* - x‖_A² = re ⟪x* - x, r⟫`, where
`x*` solves `A x* = b` and `r = b - A x` is the residual at `x`. -/
theorem IsSymmetricCoercive.energyNorm_error_sq_eq (hA : A.IsSymmetricCoercive) {b xstar x : E}
    (hstar : A xstar = b) :
    energyNorm A (xstar - x) ^ 2 = RCLike.re (inner 𝕜 (xstar - x) (b - A x)) := by
  rw [hA.energyNorm_sq, map_sub, hstar, ← inner_conj_symm (b - A x) (xstar - x), RCLike.conj_re]

/-- Second-order expansion of the energy functional at `x` in the direction `v`, exact because the
functional is quadratic: `φ(x + v) = φ x + re ⟪A x - b, v⟫ + ½ re ⟪A v, v⟫`. The linear term is the
gradient `A x - b = -r` paired with `v`, the quadratic term is half the energy quadratic form.
Only symmetry of `A` is used. -/
theorem IsSymmetric.energyFunctional_add (hA : A.IsSymmetric) (b x v : E) :
    energyFunctional A b (x + v)
      = energyFunctional A b x + RCLike.re (inner 𝕜 (A x - b) v)
        + RCLike.re (inner 𝕜 (A v) v) / 2 := by
  have h : RCLike.re (inner 𝕜 (A v) x) = RCLike.re (inner 𝕜 (A x) v) := by
    rw [hA v x, ← inner_conj_symm]
    exact RCLike.conj_re _
  simp only [energyFunctional, map_add, inner_add_left, inner_add_right, inner_sub_left, map_sub]
  rw [h]
  ring

/-- The energy functional exceeds its value at the solution `x*` of `A x* = b` by half the squared
energy norm of the error: `φ y - φ x* = ½ ‖y - x*‖_A²` ([quarteroni2000numerical] (4.35)). Hence
`x*` is the strict global minimizer of `φ`, and minimizing `φ` over a set is minimizing the
energy-norm error over it. -/
theorem IsSymmetricCoercive.energyFunctional_sub_eq (hA : A.IsSymmetricCoercive) {b xstar : E}
    (hstar : A xstar = b) (y : E) :
    energyFunctional A b y - energyFunctional A b xstar = energyNorm A (y - xstar) ^ 2 / 2 := by
  have h := hA.isSymmetric.energyFunctional_add b xstar (y - xstar)
  rw [add_sub_cancel, hstar, sub_self, inner_zero_left, map_zero, add_zero] at h
  rw [h, hA.energyNorm_sq]
  ring

/-- Cauchy–Schwarz for the energy inner product. -/
theorem IsSymmetricCoercive.abs_energyInner_le (hA : A.IsSymmetricCoercive) (x y : E) :
    ‖energyInner A x y‖ ≤ energyNorm A x * energyNorm A y := by
  have hcs := @InnerProductSpace.Core.inner_mul_inner_self_le 𝕜 E _ _ _ (energyPreCore hA) x y
  have hsym : ‖inner 𝕜 (A y) x‖ = ‖inner 𝕜 (A x) y‖ := by
    rw [hA.isSymmetric y x, ← inner_conj_symm (A x) y, RCLike.norm_conj]
  refine nonneg_le_nonneg_of_sq_le_sq
    (mul_nonneg (energyNorm_nonneg A x) (energyNorm_nonneg A y)) ?_
  calc ‖energyInner A x y‖ * ‖energyInner A x y‖
      = ‖inner 𝕜 (A x) y‖ * ‖inner 𝕜 (A y) x‖ := by rw [hsym]; rfl
    _ ≤ RCLike.re (inner 𝕜 (A x) x) * RCLike.re (inner 𝕜 (A y) y) := hcs
    _ = energyNorm A x * energyNorm A y * (energyNorm A x * energyNorm A y) := by
        rw [← hA.energyNorm_sq x, ← hA.energyNorm_sq y]; ring

end LinearMap

/-- Type synonym of `E` carrying the energy inner product of `A`. -/
def WithEnergy (A : E →ₗ[𝕜] E) (_hA : A.IsSymmetricCoercive) : Type _ := E

namespace WithEnergy

variable (A : E →ₗ[𝕜] E) (hA : A.IsSymmetricCoercive)

/-- The identity `E → WithEnergy A hA` (before any instance exists). -/
def toEnergy : E → WithEnergy A hA := id

/-- The identity `WithEnergy A hA → E`. -/
def ofEnergy : WithEnergy A hA → E := id

section Build

-- These are *local*: they only serve to state the core.  See the implementation note above.
local instance addCommGroup : AddCommGroup (WithEnergy A hA) := inferInstanceAs (AddCommGroup E)
local instance module : Module 𝕜 (WithEnergy A hA) := inferInstanceAs (Module 𝕜 E)

/-- The energy inner product as an `InnerProductSpace.Core`. -/
@[instance_reducible]
noncomputable def core : InnerProductSpace.Core 𝕜 (WithEnergy A hA) where
  inner x y := inner 𝕜 (A (ofEnergy A hA x)) (ofEnergy A hA y)
  conj_inner_symm := by
    intro x y
    show starRingEnd 𝕜 (inner 𝕜 (A (ofEnergy A hA y)) (ofEnergy A hA x)) = _
    rw [inner_conj_symm, hA.isSymmetric (ofEnergy A hA x) (ofEnergy A hA y)]
  re_inner_nonneg := by
    intro x
    exact hA.isPositive.re_inner_nonneg_left (ofEnergy A hA x)
  add_left := by
    intro x y z
    change inner 𝕜 (A (ofEnergy A hA x + ofEnergy A hA y)) (ofEnergy A hA z) = _
    simp [inner_add_left]
  smul_left := by
    intro x y r
    change inner 𝕜 (A (r • ofEnergy A hA x)) (ofEnergy A hA y) = _
    simp [inner_smul_left]
  definite := by
    intro x hx
    change ofEnergy A hA x = (0 : E)
    by_contra hx0
    have := hA.isCoercive.inner_self_pos hx0
    rw [show inner 𝕜 (A (ofEnergy A hA x)) (ofEnergy A hA x) = 0 from hx] at this
    simp at this

noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (WithEnergy A hA) :=
  (core A hA).toNormedAddCommGroup

noncomputable instance instInnerProductSpace : InnerProductSpace 𝕜 (WithEnergy A hA) :=
  InnerProductSpace.ofCore (core A hA).toCore

end Build

/-- The identity as a linear equivalence `E ≃ₗ WithEnergy A hA` (defined after the global
instances so that it refers to them). -/
def equiv : E ≃ₗ[𝕜] WithEnergy A hA where
  toFun := toEnergy A hA
  invFun := ofEnergy A hA
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The inner product of the energy space is the energy inner product of `E`: this is what makes
`equiv` the bridge along which Mathlib's inner product theory is imported. -/
@[simp]
theorem inner_equiv (x y : E) : inner 𝕜 (equiv A hA x) (equiv A hA y) = energyInner A x y := rfl

/-- The norm of the energy space is the energy norm of `E`, so distances measured there are
`A`-energy distances. -/
@[simp]
theorem norm_equiv (x : E) : ‖equiv A hA x‖ = energyNorm A x := rfl

/-- Orthogonality in the energy space is `A`-conjugacy. -/
theorem inner_equiv_eq_zero_iff (x y : E) :
    inner 𝕜 (equiv A hA x) (equiv A hA y) = 0 ↔ inner 𝕜 (A x) y = 0 := Iff.rfl

/-- A submodule of `E` transported to the energy space. -/
noncomputable def submoduleMap (K : Submodule 𝕜 E) : Submodule 𝕜 (WithEnergy A hA) :=
  K.map (equiv A hA).toLinearMap

instance (K : Submodule 𝕜 E) [FiniteDimensional 𝕜 K] :
    FiniteDimensional 𝕜 (submoduleMap A hA K) := by
  unfold submoduleMap; infer_instance

/-- Transporting a submodule does not change what belongs to it. -/
theorem equiv_mem_submoduleMap_iff {K : Submodule 𝕜 E} {x : E} :
    equiv A hA x ∈ submoduleMap A hA K ↔ x ∈ K := by
  rw [submoduleMap, Submodule.mem_map]
  refine ⟨?_, fun hx => ⟨x, hx, rfl⟩⟩
  rintro ⟨y, hy, hxy⟩
  rwa [(equiv A hA).injective hxy] at hy

section FiniteDimensional

variable [FiniteDimensional 𝕜 E]

/-- The energy space of a finite-dimensional space is finite-dimensional. -/
instance instFiniteDimensional : FiniteDimensional 𝕜 (WithEnergy A hA) :=
  (equiv A hA).finiteDimensional

/-- The energy space of a finite-dimensional space is complete. -/
instance instCompleteSpace : CompleteSpace (WithEnergy A hA) :=
  FiniteDimensional.complete 𝕜 _

end FiniteDimensional

/-- For bounded `A` the energy norm is equivalent to the original norm, so `equiv` is a
continuous linear equivalence. -/
theorem continuous_equiv {A : E →L[𝕜] E} (hA : (A : E →ₗ[𝕜] E).IsSymmetricCoercive) :
    Continuous (equiv (A : E →ₗ[𝕜] E) hA) ∧ Continuous (equiv (A : E →ₗ[𝕜] E) hA).symm := by
  obtain ⟨c, hc, hco⟩ := hA.isCoercive
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  refine ⟨AddMonoidHomClass.continuous_of_bound (equiv (A : E →ₗ[𝕜] E) hA)
      (Real.sqrt ‖A‖) fun x => ?_,
    AddMonoidHomClass.continuous_of_bound (equiv (A : E →ₗ[𝕜] E) hA).symm
      (Real.sqrt c)⁻¹ fun x => ?_⟩
  · exact hA.energyNorm_le_norm x
  · change ‖ofEnergy (A : E →ₗ[𝕜] E) hA x‖ ≤ (Real.sqrt c)⁻¹ * ‖x‖
    have h := hco.norm_le_energyNorm hc.le (ofEnergy (A : E →ₗ[𝕜] E) hA x)
    have hx : energyNorm (A : E →ₗ[𝕜] E) (ofEnergy (A : E →ₗ[𝕜] E) hA x) = ‖x‖ := rfl
    rw [hx] at h
    rw [inv_mul_eq_div, le_div_iff₀ hsc, mul_comm]
    exact h

end WithEnergy

/-! ### The gradient of the energy functional

Over `ℝ` the energy functional of a symmetric bounded `A` is differentiable everywhere with
gradient `∇φ(x) = A x - b`, the negative of the residual ([quarteroni2000numerical] (4.34),
§7.2.4): this is what makes the projection methods of `Numlib/Projection` and the conjugate
gradient method descent methods for `φ`, and the linear system `A x = b` the stationarity
condition `∇φ = 0`. -/

section Gradient

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The Fréchet derivative of the energy functional of a real symmetric bounded `A` at `x` is the
functional `v ↦ ⟪A x - b, v⟫`. No completeness is needed for this form. -/
theorem hasFDerivAt_energyFunctional {A : F →L[ℝ] F} (hA : (A : F →ₗ[ℝ] F).IsSymmetric)
    (b x : F) :
    HasFDerivAt (energyFunctional (A : F →ₗ[ℝ] F) b) (innerSL ℝ (A x - b)) x := by
  have hfun : energyFunctional (A : F →ₗ[ℝ] F) b
      = fun y => 2⁻¹ * inner ℝ (A y) y - inner ℝ b y := by
    funext y; simp [energyFunctional, div_eq_inv_mul]
  have h1 : HasFDerivAt (fun y => inner ℝ (A y) y) (2 • innerSL ℝ (A x)) x := by
    refine ((A.hasFDerivAt (x := x)).inner ℝ (hasFDerivAt_id x)).congr_fderiv ?_
    ext v
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.prod_apply,
      fderivInnerCLM_apply, ContinuousLinearMap.coe_id', id_eq, smul_apply,
      innerSL_apply_apply, nsmul_eq_mul]
    have hs : inner ℝ (A v) x = inner ℝ v (A x) := by simpa using hA v x
    rw [hs, real_inner_comm (A x) v]
    ring
  have h2 : HasFDerivAt (fun y => inner ℝ b y) (innerSL ℝ b) x := (innerSL ℝ b).hasFDerivAt
  rw [hfun]
  refine ((HasFDerivAt.const_mul h1 (2⁻¹ : ℝ)).sub h2).congr_fderiv ?_
  ext v
  simp only [FunLike.coe_sub, Pi.sub_apply, smul_apply, innerSL_apply_apply,
    nsmul_eq_mul, smul_eq_mul, inner_sub_left]
  ring

/-- The gradient of the energy functional of a real symmetric bounded `A` is `∇φ(x) = A x - b`,
the negative residual ([quarteroni2000numerical] (4.34)); in particular the derivative of the
gradient map is `A` itself, the Hessian of `φ`. Completeness is what Mathlib's `HasGradientAt`
(defined through the Riesz isomorphism) requires; the derivative form
`hasFDerivAt_energyFunctional` needs none. -/
theorem hasGradientAt_energyFunctional [CompleteSpace F] {A : F →L[ℝ] F}
    (hA : (A : F →ₗ[ℝ] F).IsSymmetric) (b x : F) :
    HasGradientAt (energyFunctional (A : F →ₗ[ℝ] F) b) (A x - b) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h : (InnerProductSpace.toDual ℝ F (A x - b) : F →L[ℝ] ℝ) = innerSL ℝ (A x - b) := by
    ext v
    simp [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]
  rw [h]
  exact hasFDerivAt_energyFunctional hA b x

/-- `hasGradientAt_energyFunctional` for a linear map on a finite-dimensional space, where every
linear map is bounded and the space is complete. -/
theorem hasGradientAt_energyFunctional_of_finiteDimensional [FiniteDimensional ℝ F]
    {A : F →ₗ[ℝ] F} (hA : A.IsSymmetric) (b x : F) :
    HasGradientAt (energyFunctional A b) (A x - b) x := by
  have h := hasGradientAt_energyFunctional (A := LinearMap.toContinuousLinearMap A)
    (by simpa using hA) b x
  simpa using h

end Gradient
