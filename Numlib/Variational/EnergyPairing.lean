import Numlib.Analysis.Convex.Duality.InnerPairing
import Numlib.Variational.Forms

/-!
# The energy pairing of a symmetric coercive operator

`IsInnerPairing B` (`Duality/InnerPairing`) is the convex library's symmetric positive definite
pairing of a space with itself; `LinearMap.IsSymmetricCoercive A` (`InnerProductSpace/Coercive`)
and the energy inner product `energyInner A x y = ⟪A x, y⟫` (`InnerProductSpace/Energy`) are the
older library's. This module is the dictionary between the two: for a real symmetric coercive `A`
the bilinear map `energyPairing A : E →ₗ[ℝ] E →ₗ[ℝ] ℝ`, `x ↦ y ↦ ⟪A x, y⟫`, is an inner pairing,
its `pairingNorm` is the energy norm `energyNorm A`, and when `A` is bounded its quadratic form is
continuous, so it is an `IsContinuousInnerPairing` — which is all that Moreau's theorem and the
proximal calculus of `Numlib/Analysis/Convex/Extremum/Moreau` ask of a pairing. A real Hermitian
coercive bounded form `a : SesqForm ℝ V` on a Hilbert space is the energy pairing of its operator
`toOperator a`, so it inherits the same instance in one step.

It is a bridge module, and it sits on the variational side because that is the more specific of the
two subjects. `Numlib/Analysis/Convex` is a general library whose natural home upstream is
`Mathlib.Analysis.Convex`; a module of it that imported `Numlib/Variational/Forms` would tie that
library to a numerical-analysis layer, which is why this one is here and not there.
`Numlib/Variational/Inequality/NormalCone` is the other bridge between these two vocabularies and
sits here for the same reason.

## Main definitions

* `energyPairing A` — `x ↦ y ↦ ⟪A x, y⟫` as an element of `E →ₗ[ℝ] E →ₗ[ℝ] ℝ`, the bilinear
  form of `energyInner A`.

## Main results

* `LinearMap.IsSymmetricCoercive.isInnerPairing_energyPairing` — the energy pairing of a symmetric
  coercive operator is an inner pairing: symmetry is `LinearMap.IsSymmetric`, positivity and
  definiteness are coercivity.
* `pairingNorm_energyPairing` — the norm the pairing induces is the energy norm.
* `LinearMap.IsSymmetricCoercive.isContinuousInnerPairing_energyPairing` — for a bounded `A` the
  quadratic form `x ↦ ⟪A x, x⟫` is continuous.
* `SesqForm.energyPairing_toOperator_apply`, `SesqForm.IsHermitian.isInnerPairing_energyPairing` —
  a real Hermitian coercive form is the energy pairing of `SesqForm.toOperator`, and so an inner
  pairing.

## Implementation notes

The results are theorems and not instances, because `IsSymmetricCoercive` is a hypothesis on `A`
and not a class; a consumer writes `haveI := hA.isInnerPairing_energyPairing` before applying the
`IsInnerPairing` API. Cauchy–Schwarz for the energy inner product is *not* re-derived from
`pairing_sq_le_mul` here: `LinearMap.IsSymmetricCoercive.abs_energyInner_le` is stated over any
`RCLike` field, where the pairing below does not exist, and the real-valued private lemmas of
`Variational/Inequality/Basic` (`convexOn_energy` and its neighbours) hold for positive
*semidefinite* forms, which an inner pairing is not.
-/

open scoped RealInnerProductSpace

open ConvexAnalysis

section Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **energy pairing** of a real operator: `energyPairing A x y = ⟪A x, y⟫`, the bilinear
form of `energyInner A`. -/
noncomputable def energyPairing (A : E →ₗ[ℝ] E) : E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ⟪A x, y⟫)
    (fun x x' y => by rw [map_add, inner_add_left])
    (fun c x y => by rw [map_smul, real_inner_smul_left, smul_eq_mul])
    (fun x y y' => inner_add_right _ _ _)
    (fun c x y => by rw [real_inner_smul_right, smul_eq_mul])

/-- The defining equation of the energy pairing. -/
@[simp] theorem energyPairing_apply (A : E →ₗ[ℝ] E) (x y : E) :
    energyPairing A x y = ⟪A x, y⟫ := rfl

/-- The energy pairing is the energy inner product `energyInner A` of `InnerProductSpace/Energy`,
read as a bilinear map. -/
theorem energyPairing_apply_eq_energyInner (A : E →ₗ[ℝ] E) (x y : E) :
    energyPairing A x y = energyInner A x y := rfl

/-- The energy pairing of a symmetric coercive operator is an inner pairing. -/
theorem LinearMap.IsSymmetricCoercive.isInnerPairing_energyPairing {A : E →ₗ[ℝ] E}
    (hA : A.IsSymmetricCoercive) : IsInnerPairing (energyPairing A) where
  pairing_comm x y := by
    simp only [energyPairing_apply]
    rw [hA.isSymmetric x y, real_inner_comm]
  self_nonneg x := by
    simpa only [energyPairing_apply, RCLike.re_to_real] using hA.isPositive.re_inner_nonneg_left x
  eq_zero_of_self_eq_zero x h := by
    by_contra hx
    have := hA.isCoercive.inner_self_pos hx
    simp only [energyPairing_apply, RCLike.re_to_real] at h this
    exact this.ne' h

/-- The norm induced by the energy pairing is the energy norm. -/
theorem pairingNorm_energyPairing (A : E →ₗ[ℝ] E) (x : E) :
    pairingNorm (energyPairing A) x = energyNorm A x := by
  simp only [pairingNorm, energyPairing_apply, energyNorm, RCLike.re_to_real]

/-- For a bounded symmetric coercive operator the quadratic form `x ↦ ⟪A x, x⟫` is continuous, so
the energy pairing is a continuous inner pairing. -/
theorem LinearMap.IsSymmetricCoercive.isContinuousInnerPairing_energyPairing {A : E →L[ℝ] E}
    (hA : (A : E →ₗ[ℝ] E).IsSymmetricCoercive) :
    IsContinuousInnerPairing (energyPairing (A : E →ₗ[ℝ] E)) :=
  { hA.isInnerPairing_energyPairing with
    continuous_self := by
      simp only [energyPairing_apply, ContinuousLinearMap.coe_coe]
      exact A.continuous.inner continuous_id }

end Operator

section Form

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

namespace SesqForm

/-- A real bounded form is the energy pairing of its operator: `⟪toOperator a u, v⟫ = a u v`. -/
theorem energyPairing_toOperator_apply (a : SesqForm ℝ V) (u v : V) :
    energyPairing (toOperator a : V →ₗ[ℝ] V) u v = a u v := by
  rw [energyPairing_apply, ContinuousLinearMap.coe_coe, inner_toOperator]

/-- A real Hermitian coercive bounded form is an inner pairing, read through its operator. -/
theorem IsHermitian.isInnerPairing_energyPairing {a : SesqForm ℝ V} (ha : a.IsHermitian)
    (hc : a.IsCoercive) : IsInnerPairing (energyPairing (toOperator a : V →ₗ[ℝ] V)) :=
  have hA : (toOperator a : V →ₗ[ℝ] V).IsSymmetricCoercive :=
    ⟨(isHermitian_iff_toOperator_isSymmetric a).1 ha,
      let ⟨c, hc₀, hcc⟩ := hc
      ⟨c, hc₀, (isCoerciveWith_iff_toOperator a c).1 hcc⟩⟩
  hA.isInnerPairing_energyPairing

end SesqForm

end Form
