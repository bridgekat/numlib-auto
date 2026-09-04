/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.InnerProductSpace.Coercive
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Energy inner product and energy norm

For a symmetric coercive `A`, `⟪x, y⟫_A := ⟪A x, y⟫` is an inner product and
`‖x‖_A := √(re ⟪A x, x⟫)` the associated norm (Saad §5.2, Atkinson–Han §5.6/§9.4, Fong–Saunders,
Meurant–Strakoš §3). `WithEnergy A hA` is a type synonym of `E` carrying this inner product, so
that Mathlib's orthogonal projection theory applies to `A`-orthogonal projections.
-/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The energy inner product `⟪x, y⟫_A = ⟪A x, y⟫`. -/
noncomputable def energyInner (A : E →ₗ[𝕜] E) (x y : E) : 𝕜 := inner 𝕜 (A x) y

/-- The energy norm `‖x‖_A = √(re ⟪A x, x⟫)`. -/
noncomputable def energyNorm (A : E →ₗ[𝕜] E) (x : E) : ℝ :=
  Real.sqrt (RCLike.re (inner 𝕜 (A x) x))

scoped[Energy] notation "⟪" x ", " y "⟫_[" A "]" => energyInner A x y
scoped[Energy] notation "‖" x "‖_[" A "]" => energyNorm A x

namespace LinearMap

variable {A : E →ₗ[𝕜] E}

theorem IsSymmetricCoercive.energyNorm_sq (hA : A.IsSymmetricCoercive) (x : E) :
    energyNorm A x ^ 2 = RCLike.re (inner 𝕜 (A x) x) := by
  sorry

theorem IsSymmetricCoercive.energyNorm_eq_zero_iff (hA : A.IsSymmetricCoercive) {x : E} :
    energyNorm A x = 0 ↔ x = 0 := by
  sorry

theorem IsSymmetricCoercive.energyNorm_pos (hA : A.IsSymmetricCoercive) {x : E} (hx : x ≠ 0) :
    0 < energyNorm A x := by
  sorry

/-- Lower norm equivalence `√c ‖x‖ ≤ ‖x‖_A`. -/
theorem IsCoerciveWith.norm_le_energyNorm {c : ℝ} (hc : 0 ≤ c) (hA : A.IsCoerciveWith c) (x : E) :
    Real.sqrt c * ‖x‖ ≤ energyNorm A x := by
  sorry

/-- Upper norm equivalence `‖x‖_A ≤ √‖A‖ ‖x‖` for bounded `A`. -/
theorem IsSymmetricCoercive.energyNorm_le_norm {A : E →L[𝕜] E}
    (hA : (A : E →ₗ[𝕜] E).IsSymmetricCoercive) (x : E) :
    energyNorm (A : E →ₗ[𝕜] E) x ≤ Real.sqrt ‖A‖ * ‖x‖ := by
  sorry

/-- `‖x* - x‖_A² = re ⟪x* - x, r⟫` with `r = b - A x` (Saad Thm 5.9 proof, Meurant §3.3). -/
theorem IsSymmetricCoercive.energyNorm_error_sq_eq (hA : A.IsSymmetricCoercive) {b xstar x : E}
    (hstar : A xstar = b) :
    energyNorm A (xstar - x) ^ 2 = RCLike.re (inner 𝕜 (xstar - x) (b - A x)) := by
  sorry

/-- Cauchy–Schwarz for the energy inner product. -/
theorem IsSymmetricCoercive.abs_energyInner_le (hA : A.IsSymmetricCoercive) (x y : E) :
    ‖energyInner A x y‖ ≤ energyNorm A x * energyNorm A y := by
  sorry

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

-- The plain algebraic instances are *local*: they only serve to state the core, and only the
-- core-derived normed instances are global (Mathlib's `Matrix.toInnerProductSpace` pattern),
-- which avoids an `AddCommMonoid` diamond between the two.
local instance addCommGroup : AddCommGroup (WithEnergy A hA) := inferInstanceAs (AddCommGroup E)
local instance module : Module 𝕜 (WithEnergy A hA) := inferInstanceAs (Module 𝕜 E)

/-- The energy inner product as an `InnerProductSpace.Core`. -/
@[instance_reducible]
noncomputable def core : InnerProductSpace.Core 𝕜 (WithEnergy A hA) where
  inner x y := inner 𝕜 (A (ofEnergy A hA x)) (ofEnergy A hA y)
  conj_inner_symm := by sorry
  re_inner_nonneg := by sorry
  add_left := by sorry
  smul_left := by sorry
  definite := by sorry

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

@[simp]
theorem inner_equiv (x y : E) : inner 𝕜 (equiv A hA x) (equiv A hA y) = energyInner A x y := rfl

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

theorem equiv_mem_submoduleMap_iff {K : Submodule 𝕜 E} {x : E} :
    equiv A hA x ∈ submoduleMap A hA K ↔ x ∈ K := by
  sorry

/-- For bounded `A` the energy norm is equivalent to the original norm, so `equiv` is a
continuous linear equivalence. -/
theorem continuous_equiv {A : E →L[𝕜] E} (hA : (A : E →ₗ[𝕜] E).IsSymmetricCoercive) :
    Continuous (equiv (A : E →ₗ[𝕜] E) hA) ∧ Continuous (equiv (A : E →ₗ[𝕜] E) hA).symm := by
  sorry

end WithEnergy
