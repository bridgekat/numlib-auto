/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
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
  which Mathlib's inner product theory is imported.

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
