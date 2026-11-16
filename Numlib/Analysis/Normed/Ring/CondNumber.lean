/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Ring.Units`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.Units

/-!
# The condition number in a normed ring

The **condition number** of an element $a$ of a normed ring is
$$\kappa(a) = \|a\| \, \|a^{-1}\|,$$
with the value $0$ when $a$ is not a unit. It specializes to bounded operators $E \to E$ and to
matrices under any of Mathlib's scoped matrix norms. This is the standard condition number of
numerical linear algebra: it bounds the amplification of a relative perturbation of the data in the
solution of $ax = b$. The file proves $\kappa(a) \ge 0$, $\kappa(a) \ge 1$ for a unit when
$\|1\| = 1$, $\kappa(a^{-1}) = \kappa(a)$, $\kappa(ca) = \kappa(a)$ for a nonzero scalar $c$, and
$\kappa(ab) \le \kappa(a) \kappa(b)$ for units.

For an isomorphism $e \colon E \to F$ of normed spaces, the two-space form is
$\kappa(e) = \|e\| \, \|e^{-1}\|$, which needs no special value. For $F = E$ it agrees with the
condition number in the ring of bounded operators on $E$.

## Main definitions

* `NormedRing.condNumber`: $\kappa(a) = \|a\| \, \|a^{-1}\|$, and $0$ for a non-unit.
* `ContinuousLinearEquiv.condNumber`: $\kappa(e) = \|e\| \, \|e^{-1}\|$ for an isomorphism
  $e \colon E \to F$.

## Main results

* `NormedRing.one_le_condNumber`: $1 \le \kappa(a)$ for a unit $a$ when $\|1\| = 1$.
* `NormedRing.condNumber_inverse`: $\kappa(a^{-1}) = \kappa(a)$.
* `NormedRing.condNumber_smul`: $\kappa(ca) = \kappa(a)$ for $c \ne 0$.
* `ContinuousLinearEquiv.condNumber_eq`: for an isomorphism $e \colon E \to E$, the ring condition
  number is $\|e\| \, \|e^{-1}\|$.
* `ContinuousLinearEquiv.one_le_condNumber`: $1 \le \kappa(e)$ when $E$ is nontrivial.

## Notation

* `κ a`: the condition number `NormedRing.condNumber a`, scoped in `NormedRing`.

## Implementation notes

* The inverse is `Ring.inverse`, which is $0$ at a non-unit. So a singular element has condition
  number $0$, not $\infty$. Test for invertibility with `IsUnit a`, not with the sign of
  $\kappa(a)$.
* `ContinuousLinearEquiv.condNumber_coe` identifies the two-space form with `NormedRing.condNumber`
  when $F = E$.
-/

namespace NormedRing

variable {R : Type*} [NormedRing R]

/-- The **condition number** of an element $a$ of a normed ring $R$ is
$$\kappa(a) = \|a\| \, \|a^{-1}\|,$$
where $a^{-1}$ is `Ring.inverse a`. If $a$ is not a unit, then $a^{-1} = 0$ and $\kappa(a) = 0$. -/
noncomputable def condNumber (a : R) : ℝ := ‖a‖ * ‖Ring.inverse a‖

/-- The notation $\kappa(a)$ for the condition number `NormedRing.condNumber a`. -/
scoped notation "κ" => NormedRing.condNumber

/-- Let $\mathbb{K}$ be a field and $A$ a $\mathbb{K}$-algebra. For $c \in \mathbb{K}$ with
$c \ne 0$ and $a \in A$, `Ring.inverse` satisfies $(ca)^{-1} = c^{-1} a^{-1}$. This includes the
case where $a$ is not a unit, where both sides are $0$. -/
theorem _root_.Ring.inverse_smul {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A] {c : 𝕜}
    (hc : c ≠ 0) (a : A) : Ring.inverse (c • a) = c⁻¹ • Ring.inverse a := by
  by_cases ha : IsUnit a
  · exact Ring.inverse_unit (⟨c • a, c⁻¹ • Ring.inverse a,
      by rw [smul_mul_smul_comm, Ring.mul_inverse_cancel a ha, mul_inv_cancel₀ hc, one_smul],
      by rw [smul_mul_smul_comm, Ring.inverse_mul_cancel a ha, inv_mul_cancel₀ hc, one_smul]⟩ : Aˣ)
  · rw [Ring.inverse_non_unit (c • a) ((isUnit_smul_iff (Units.mk0 c hc) a).not.mpr ha),
      Ring.inverse_non_unit _ ha, smul_zero]

/-- If $a$ is not a unit, then $\kappa(a) = 0$.

This is the value of `Ring.inverse` at a non-unit, not $\infty$. Test for invertibility with
`IsUnit a`, not with the sign of $\kappa(a)$. -/
theorem condNumber_of_not_isUnit {a : R} (ha : ¬ IsUnit a) : condNumber a = 0 := by
  rw [condNumber, Ring.inverse_non_unit _ ha, norm_zero, mul_zero]

/-- The condition number is nonnegative: $0 \le \kappa(a)$ for every $a$, including non-units. -/
theorem condNumber_nonneg (a : R) : 0 ≤ condNumber a :=
  mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- Let $R$ be a normed ring with $\|1\| = 1$, and let $a \in R$ be a unit. Then
$$1 \le \kappa(a).$$

The proof applies submultiplicativity of the norm to $a a^{-1} = 1$. The bound fails for a
non-unit, where $\kappa(a) = 0$. -/
theorem one_le_condNumber [NormOneClass R] {a : R} (ha : IsUnit a) : 1 ≤ condNumber a :=
  calc (1 : ℝ) = ‖a * Ring.inverse a‖ := by rw [Ring.mul_inverse_cancel a ha, norm_one]
    _ ≤ condNumber a := norm_mul_le _ _

/-- For every $a$ in a normed ring, $\kappa(a^{-1}) = \kappa(a)$, where $a^{-1}$ is
`Ring.inverse a`.

Solving $ax = b$ and applying $a^{-1}$ are equally sensitive problems. For a non-unit both sides
are $0$. -/
theorem condNumber_inverse (a : R) : condNumber (Ring.inverse a) = condNumber a := by
  by_cases ha : IsUnit a
  · rw [condNumber, condNumber, Ring.inverse_inverse ha, mul_comm]
  · rw [condNumber, condNumber, Ring.inverse_non_unit _ ha, norm_zero, zero_mul, mul_zero]

/-- The condition number is **scale invariant**. Let $R$ be a normed algebra over a normed field
$\mathbb{K}$, let $c \in \mathbb{K}$ with $c \ne 0$, and let $a \in R$. Then
$$\kappa(ca) = \kappa(a).$$

Rescaling the equation $ax = b$ does not make it easier or harder to solve. This is why
$\kappa(a)$, and not $\|a^{-1}\|$, measures the sensitivity of the solution to a relative
perturbation of the data. -/
theorem condNumber_smul {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra 𝕜 R] {c : 𝕜} (hc : c ≠ 0)
    (a : R) : condNumber (c • a) = condNumber a := by
  have hc' : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  rw [condNumber, condNumber, Ring.inverse_smul hc, norm_smul, norm_smul, norm_inv]
  field_simp

/-- For units $a$ and $b$ of a normed ring, $\kappa(ab) \le \kappa(a) \kappa(b)$. -/
theorem condNumber_mul_le {a b : R} (ha : IsUnit a) (hb : IsUnit b) :
    condNumber (a * b) ≤ condNumber a * condNumber b := by
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨v, rfl⟩ := hb
  rw [condNumber, condNumber, condNumber, ← Units.val_mul, Ring.inverse_unit, Ring.inverse_unit,
    Ring.inverse_unit, mul_inv_rev, Units.val_mul, Units.val_mul]
  calc ‖(u : R) * v‖ * ‖(↑v⁻¹ : R) * ↑u⁻¹‖
      ≤ ‖(u : R)‖ * ‖(v : R)‖ * (‖(↑v⁻¹ : R)‖ * ‖(↑u⁻¹ : R)‖) := by
        gcongr <;> exact norm_mul_le _ _
    _ = ‖(u : R)‖ * ‖(↑u⁻¹ : R)‖ * (‖(v : R)‖ * ‖(↑v⁻¹ : R)‖) := by ring

end NormedRing

namespace ContinuousLinearEquiv

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- For a continuous linear equivalence $e \colon E \to E$, `Ring.inverse` of $e$ in the ring of
bounded operators is the inverse map $e^{-1}$. -/
theorem ring_inverse_coe (e : E ≃L[𝕜] E) :
    Ring.inverse (e : E →L[𝕜] E) = (e.symm : E →L[𝕜] E) :=
  Ring.inverse_unit (⟨(e : E →L[𝕜] E), (e.symm : E →L[𝕜] E), by ext x; simp, by ext x; simp⟩ :
    (E →L[𝕜] E)ˣ)

/-- Let $e \colon E \to E$ be a continuous linear equivalence of a normed space $E$ over a
nontrivially normed field. Then its condition number in the ring of bounded operators is
$$\kappa(e) = \|e\| \, \|e^{-1}\|,$$
with the inverse map $e^{-1}$.

The value $0$ of `Ring.inverse` at a non-unit never arises here. -/
theorem condNumber_eq (e : E ≃L[𝕜] E) :
    NormedRing.condNumber (e : E →L[𝕜] E) = ‖(e : E →L[𝕜] E)‖ * ‖(e.symm : E →L[𝕜] E)‖ := by
  rw [NormedRing.condNumber, ring_inverse_coe]

section TwoSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The **condition number of an isomorphism** $e \colon E \to F$ of normed spaces over a
nontrivially normed field is
$$\kappa(e) = \|e\| \, \|e^{-1}\|.$$

This is the two-space form. Unlike `NormedRing.condNumber`, which lives in one normed ring and
needs a special value for the non-invertible elements, an equivalence is invertible by
construction. For $F = E$ the two agree, by `ContinuousLinearEquiv.condNumber_coe`. It measures
the same sensitivity: for $v, \hat v \in E$ with $v \ne 0$,
$$\frac{\|v - \hat v\|}{\|v\|} \le \kappa(e) \, \frac{\|ev - e\hat v\|}{\|ev\|},$$
so the relative error of the solution of $ev = w$ is at most $\kappa(e)$ times the relative
error of the data. -/
noncomputable def condNumber (e : E ≃L[𝕜] F) : ℝ :=
  ‖(e : E →L[𝕜] F)‖ * ‖(e.symm : F →L[𝕜] E)‖

/-- For a continuous linear equivalence $e \colon E \to E$, `NormedRing.condNumber` of $e$ in the
ring of bounded operators equals the two-space condition number
`ContinuousLinearEquiv.condNumber e`. -/
theorem condNumber_coe (e : E ≃L[𝕜] E) :
    NormedRing.condNumber (e : E →L[𝕜] E) = condNumber e :=
  condNumber_eq e

/-- For an isomorphism $e \colon E \to F$, $\kappa(e^{-1}) = \kappa(e)$. -/
@[simp] theorem condNumber_symm (e : E ≃L[𝕜] F) : condNumber e.symm = condNumber e := by
  rw [condNumber, condNumber, e.symm_symm, mul_comm]

/-- The condition number of an isomorphism is nonnegative: $0 \le \kappa(e)$. -/
theorem condNumber_nonneg (e : E ≃L[𝕜] F) : 0 ≤ condNumber e :=
  mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- Let $E$ be a nontrivial normed space and $e \colon E \to F$ an isomorphism. Then
$$1 \le \kappa(e).$$

The composite $e^{-1} \circ e$ is the identity, of norm $1$. The identity of a trivial space has
norm $0$, so the hypothesis that $E$ is nontrivial is needed. -/
theorem one_le_condNumber [Nontrivial E] (e : E ≃L[𝕜] F) : 1 ≤ condNumber e :=
  e.one_le_norm_mul_norm_symm

end TwoSpace

end ContinuousLinearEquiv
