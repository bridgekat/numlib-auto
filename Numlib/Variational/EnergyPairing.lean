/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Duality.InnerPairing
import Numlib.Variational.Forms

/-!
# The energy pairing of a symmetric coercive operator

Let $E$ be a real inner product space and $A : E \to E$ a linear operator. The **energy pairing** of
$A$ is the bilinear map $(x, y) \mapsto \langle A x, y \rangle$ on $E$. This module shows that for a
symmetric coercive $A$ the energy pairing is an inner pairing in the sense of
`ConvexAnalysis.IsInnerPairing`: it is symmetric and positive definite. The norm that it induces is
the energy norm $\|x\|_A = \sqrt{\langle A x, x \rangle}$. When $A$ is bounded, the quadratic form
$x \mapsto \langle A x, x \rangle$ is continuous, so the energy pairing is a
`ConvexAnalysis.IsContinuousInnerPairing`. This is the hypothesis on a pairing that Moreau's theorem
and the proximal calculus of `Numlib.Analysis.Convex.Extremum.Moreau` use.

A real Hermitian coercive bounded form $a$ on a Hilbert space $V$ is the energy pairing of its
operator $A$, defined by $\langle A u, v \rangle = a(u, v)$. So the same results apply to $a$ at
once. The module connects two vocabularies: the inner pairings of
`Numlib.Analysis.Convex.Duality.InnerPairing`, and the symmetric coercive operators of
`Numlib.Analysis.InnerProductSpace.Coercive` with the energy inner product of
`Numlib.Analysis.InnerProductSpace.Energy`.

## Main definitions

* `energyPairing`: the bilinear map $(x, y) \mapsto \langle A x, y \rangle$, the bilinear form of
  `energyInner A`.

## Main results

* `LinearMap.IsSymmetricCoercive.isInnerPairing_energyPairing`: the energy pairing of a symmetric
  coercive operator is symmetric and positive definite.
* `pairingNorm_energyPairing`: the norm that the energy pairing induces is the energy norm.
* `LinearMap.IsSymmetricCoercive.isContinuousInnerPairing_energyPairing`: for a bounded symmetric
  coercive $A$, the quadratic form $x \mapsto \langle A x, x \rangle$ is continuous.
* `SesqForm.energyPairing_toOperator_apply`, `SesqForm.IsHermitian.isInnerPairing_energyPairing`: a
  real bounded form is the energy pairing of `SesqForm.toOperator`, and it is an inner pairing when
  it is Hermitian and coercive.

## Implementation notes

* The results are theorems and not instances, because `LinearMap.IsSymmetricCoercive` is a
  hypothesis on $A$ and not a class. To use the API of `ConvexAnalysis.IsInnerPairing`, first write
  `haveI := hA.isInnerPairing_energyPairing`.
* The Cauchy–Schwarz inequality for the energy inner product is not derived here from
  `ConvexAnalysis.pairing_sq_le_mul`. The lemma `LinearMap.IsSymmetricCoercive.abs_energyInner_le`
  holds over any `RCLike` field, where the energy pairing of this module does not exist. The
  convexity lemmas for the energy in `Numlib.Variational.Inequality.Basic` hold for positive
  semidefinite forms, and such a form is in general not an inner pairing.
* The module is a bridge between the convex analysis library and the variational library. It is in
  the variational library because that subject is the more specific one: a module of
  `Numlib.Analysis.Convex` that imports `Numlib.Variational.Forms` would make the general convex
  analysis library depend on numerical analysis. `Numlib.Variational.Inequality.NormalCone` is the
  other bridge between the two vocabularies, and it is in the variational library for the same
  reason.
-/

open scoped RealInnerProductSpace

open ConvexAnalysis

section Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **energy pairing** of a linear operator $A : E \to E$ on a real inner product space $E$ is
the bilinear map
$$(x, y) \mapsto \langle A x, y \rangle.$$
It is the bilinear form of the energy inner product `energyInner A`. -/
noncomputable def energyPairing (A : E →ₗ[ℝ] E) : E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ⟪A x, y⟫)
    (fun x x' y => by rw [map_add, inner_add_left])
    (fun c x y => by rw [map_smul, real_inner_smul_left, smul_eq_mul])
    (fun x y y' => inner_add_right _ _ _)
    (fun c x y => by rw [real_inner_smul_right, smul_eq_mul])

/-- The energy pairing of $A$ at $(x, y)$ is $\langle A x, y \rangle$. -/
@[simp] theorem energyPairing_apply (A : E →ₗ[ℝ] E) (x y : E) :
    energyPairing A x y = ⟪A x, y⟫ := rfl

/-- The energy pairing of $A$ at $(x, y)$ is the energy inner product `energyInner A x y`. -/
theorem energyPairing_apply_eq_energyInner (A : E →ₗ[ℝ] E) (x y : E) :
    energyPairing A x y = energyInner A x y := rfl

/-- Let $A : E \to E$ be a symmetric coercive linear operator on a real inner product space $E$.
Then the energy pairing $(x, y) \mapsto \langle A x, y \rangle$ is an inner pairing: it is
symmetric, $\langle A x, x \rangle \ge 0$ for every $x$, and $\langle A x, x \rangle = 0$ only
for $x = 0$.

Symmetry is the symmetry of $A$. Positivity and definiteness follow from coercivity. -/
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

/-- For every linear operator $A : E \to E$, the norm $\sqrt{\langle A x, x \rangle}$ induced by the
energy pairing is the energy norm $\|x\|_A$ of `energyNorm`. -/
theorem pairingNorm_energyPairing (A : E →ₗ[ℝ] E) (x : E) :
    pairingNorm (energyPairing A) x = energyNorm A x := by
  simp only [pairingNorm, energyPairing_apply, energyNorm, RCLike.re_to_real]

/-- Let $A : E \to E$ be a bounded linear operator on a real inner product space $E$, and let $A$ be
symmetric and coercive. Then the energy pairing of $A$ is a continuous inner pairing: it is an
inner pairing, and the quadratic form $x \mapsto \langle A x, x \rangle$ is continuous. -/
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

/-- Let $a$ be a real bounded bilinear form on a real Hilbert space $V$, and let $A$ be its operator
`SesqForm.toOperator a`. Then the energy pairing of $A$ is $a$:
$$\langle A u, v \rangle = a(u, v) \quad \text{for all } u, v \in V.$$
-/
theorem energyPairing_toOperator_apply (a : SesqForm ℝ V) (u v : V) :
    energyPairing (toOperator a : V →ₗ[ℝ] V) u v = a u v := by
  rw [energyPairing_apply, ContinuousLinearMap.coe_coe, inner_toOperator]

/-- Let $a$ be a real bounded bilinear form on a real Hilbert space $V$. If $a$ is Hermitian (that
is, symmetric) and coercive, then the energy pairing of its operator `SesqForm.toOperator a` is
an inner pairing. -/
theorem IsHermitian.isInnerPairing_energyPairing {a : SesqForm ℝ V} (ha : a.IsHermitian)
    (hc : a.IsCoercive) : IsInnerPairing (energyPairing (toOperator a : V →ₗ[ℝ] V)) :=
  have hA : (toOperator a : V →ₗ[ℝ] V).IsSymmetricCoercive :=
    ⟨(isHermitian_iff_toOperator_isSymmetric a).1 ha,
      let ⟨c, hc₀, hcc⟩ := hc
      ⟨c, hc₀, (isCoerciveWith_iff_toOperator a c).1 hcc⟩⟩
  hA.isInnerPairing_energyPairing

end SesqForm

end Form
