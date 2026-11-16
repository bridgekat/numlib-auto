/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.Adjoint`, beside `IsSelfAdjoint.isSymmetric`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The ascent of a self-adjoint operator is one

Let $A$ be a self-adjoint bounded operator on a Hilbert space $H$ over $\mathbb{K} = \mathbb{R}$ or
$\mathbb{C}$. If $A^2 v = 0$, then $\|Av\|^2 = \langle A^2 v, v \rangle = 0$. Hence
$\ker A^2 = \ker A$, and by induction $\ker A^k = \ker A$ for every $k \ge 1$: the ascent of $A$ is
one. Applied to $A = T - \lambda I$ for a self-adjoint $T$ and a real $\lambda$, this says that the
algebraic and the geometric multiplicities of an eigenvalue of a self-adjoint operator coincide:
$\ker (T - \lambda I)^k = \ker (T - \lambda I)$. The same holds for $\lambda I - T$. This is item 3
of the Comments on Chapter 6 (last sentence) and Problem 36 of [brezis2011functional], and the index
clause of Theorem 2.8.15 of [han2009theoretical].

## Main results

* `ContinuousLinearMap.ker_pow_eq_ker_of_ker_sq_eq`: if $\ker A^2 = \ker A$, then
  $\ker A^k = \ker A$ for every $k \ge 1$.
* `IsSelfAdjoint.ker_sq_eq_ker` and `IsSelfAdjoint.ker_pow_eq_ker`: for self-adjoint $A$,
  $\ker A^k = \ker A$ for every $k \ge 1$.
* `IsSelfAdjoint.ker_sq_sub_smul_eq_ker` and `IsSelfAdjoint.ker_pow_sub_smul_eq_ker`: for
  self-adjoint $T$ and real $\lambda$, $\ker (T - \lambda I)^k = \ker (T - \lambda I)$ for every
  $k \ge 1$.
* `IsSelfAdjoint.ker_sq_smul_sub_eq_ker` and `IsSelfAdjoint.ker_pow_smul_sub_eq_ker`: the same for
  $\lambda I - T$.

## Implementation notes

* A real scalar $\lambda \in \mathbb{K}$ is expressed by the hypothesis `starRingEnd 𝕜 l = l`, that
  is, $\bar{\lambda} = \lambda$.
* The induction step is the general statement `ContinuousLinearMap.ker_pow_eq_ker_of_ker_sq_eq`,
  which holds for a continuous linear operator on any topological module over a semiring.
-/

open ContinuousLinearMap
open scoped InnerProductSpace

section General

variable {R M : Type*} [Semiring R] [TopologicalSpace M] [AddCommMonoid M] [Module R M]

/-- **An operator whose kernel stabilizes at the second power has the ascent one.** Let $M$ be a
topological module over a semiring $R$, and let $A$ be a continuous linear operator on $M$ with
$\ker A^2 = \ker A$. Then
$$\ker A^k = \ker A \qquad \text{for every } k \ge 1.$$

If $A^{k + 1} x = 0$, then $Ax \in \ker A^k = \ker A$, so $x \in \ker A^2 = \ker A$. -/
theorem ContinuousLinearMap.ker_pow_eq_ker_of_ker_sq_eq (A : M →L[R] M)
    (h : LinearMap.ker ((A ^ 2 : M →L[R] M) : M →ₗ[R] M) = LinearMap.ker (A : M →ₗ[R] M))
    {k : ℕ} (hk : 1 ≤ k) :
    LinearMap.ker ((A ^ k : M →L[R] M) : M →ₗ[R] M) = LinearMap.ker (A : M →ₗ[R] M) := by
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
    · rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, pow_succ, mul_apply_eq_comp] at hx
      have hAx : A x ∈ LinearMap.ker ((A ^ n : M →L[R] M) : M →ₗ[R] M) := by
        rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
        exact hx
      rw [ih hn] at hAx
      have hx2 : x ∈ LinearMap.ker ((A ^ 2 : M →L[R] M) : M →ₗ[R] M) := by
        rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, pow_two, mul_apply_eq_comp]
        exact hAx
      rwa [h] at hx2
    · rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx ⊢
      rw [pow_succ, mul_apply_eq_comp, hx, map_zero]

end General

namespace IsSelfAdjoint

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- **The ascent of a self-adjoint operator is one**: let $H$ be a Hilbert space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $A$ be a self-adjoint bounded operator on
$H$. Then $\ker A^2 = \ker A$.

If $A^2 v = 0$, then $\|Av\|^2 = \langle Av, Av \rangle = \langle A^2 v, v \rangle = 0$. -/
theorem ker_sq_eq_ker {A : H →L[𝕜] H} (hA : IsSelfAdjoint A) :
    LinearMap.ker ((A ^ 2 : H →L[𝕜] H) : H →ₗ[𝕜] H) = LinearMap.ker (A : H →ₗ[𝕜] H) := by
  refine le_antisymm (fun v hv ↦ ?_) (fun v hv ↦ ?_)
  · rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, pow_two, mul_apply_eq_comp] at hv
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    have hinner : ⟪A v, A v⟫_𝕜 = 0 := by
      rw [← ContinuousLinearMap.adjoint_inner_left, hA.adjoint_eq, hv, inner_zero_left]
    exact inner_self_eq_zero.1 hinner
  · rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hv ⊢
    rw [pow_two, mul_apply_eq_comp, hv, map_zero]

/-- Let $A$ be a self-adjoint bounded operator on a Hilbert space $H$, and let $k \ge 1$. Then
$\ker A^k = \ker A$. -/
theorem ker_pow_eq_ker {A : H →L[𝕜] H} (hA : IsSelfAdjoint A) {k : ℕ} (hk : 1 ≤ k) :
    LinearMap.ker ((A ^ k : H →L[𝕜] H) : H →ₗ[𝕜] H) = LinearMap.ker (A : H →ₗ[𝕜] H) :=
  A.ker_pow_eq_ker_of_ker_sq_eq hA.ker_sq_eq_ker hk

/-- Let $T$ be a self-adjoint bounded operator on a Hilbert space $H$, and let
$\lambda \in \mathbb{K}$ be real, that is, $\bar{\lambda} = \lambda$. Then $T - \lambda I$ is
self-adjoint. -/
theorem sub_smul_one {T : H →L[𝕜] H} (hT : IsSelfAdjoint T) {l : 𝕜} (hl : starRingEnd 𝕜 l = l) :
    IsSelfAdjoint (T - l • (1 : H →L[𝕜] H)) :=
  have hl' : IsSelfAdjoint l := hl
  hT.sub (hl'.smul (IsSelfAdjoint.one (H →L[𝕜] H)))

/-- Let $T$ be a self-adjoint bounded operator on a Hilbert space $H$, and let
$\lambda \in \mathbb{K}$ be real, that is, $\bar{\lambda} = \lambda$. Then $\lambda I - T$ is
self-adjoint. -/
theorem smul_one_sub {T : H →L[𝕜] H} (hT : IsSelfAdjoint T) {l : 𝕜} (hl : starRingEnd 𝕜 l = l) :
    IsSelfAdjoint (l • (1 : H →L[𝕜] H) - T) :=
  have hl' : IsSelfAdjoint l := hl
  (hl'.smul (IsSelfAdjoint.one (H →L[𝕜] H))).sub hT

/-- **The algebraic and the geometric multiplicities of an eigenvalue of a self-adjoint operator
coincide**: let $T$ be a self-adjoint bounded operator on a Hilbert space $H$, and let
$\lambda \in \mathbb{K}$ be real. Then
$$\ker (T - \lambda I)^2 = \ker (T - \lambda I).$$
See item 3 of the Comments on Chapter 6 of [brezis2011functional], and Theorem 2.8.15 of
[han2009theoretical]. -/
theorem ker_sq_sub_smul_eq_ker {T : H →L[𝕜] H} (hT : IsSelfAdjoint T) {l : 𝕜}
    (hl : starRingEnd 𝕜 l = l) :
    LinearMap.ker (((T - l • (1 : H →L[𝕜] H)) ^ 2 : H →L[𝕜] H) : H →ₗ[𝕜] H)
      = LinearMap.ker ((T - l • (1 : H →L[𝕜] H) : H →L[𝕜] H) : H →ₗ[𝕜] H) :=
  (hT.sub_smul_one hl).ker_sq_eq_ker

/-- Let $T$ be a self-adjoint bounded operator on a Hilbert space $H$, let $\lambda \in \mathbb{K}$
be real, and let $k \ge 1$. Then $\ker (T - \lambda I)^k = \ker (T - \lambda I)$. -/
theorem ker_pow_sub_smul_eq_ker {T : H →L[𝕜] H} (hT : IsSelfAdjoint T) {l : 𝕜}
    (hl : starRingEnd 𝕜 l = l) {k : ℕ} (hk : 1 ≤ k) :
    LinearMap.ker (((T - l • (1 : H →L[𝕜] H)) ^ k : H →L[𝕜] H) : H →ₗ[𝕜] H)
      = LinearMap.ker ((T - l • (1 : H →L[𝕜] H) : H →L[𝕜] H) : H →ₗ[𝕜] H) :=
  (hT.sub_smul_one hl).ker_pow_eq_ker hk

/-- Let $T$ be a self-adjoint bounded operator on a Hilbert space $H$, and let
$\lambda \in \mathbb{K}$ be real. Then $\ker (\lambda I - T)^2 = \ker (\lambda I - T)$. -/
theorem ker_sq_smul_sub_eq_ker {T : H →L[𝕜] H} (hT : IsSelfAdjoint T) {l : 𝕜}
    (hl : starRingEnd 𝕜 l = l) :
    LinearMap.ker (((l • (1 : H →L[𝕜] H) - T) ^ 2 : H →L[𝕜] H) : H →ₗ[𝕜] H)
      = LinearMap.ker ((l • (1 : H →L[𝕜] H) - T : H →L[𝕜] H) : H →ₗ[𝕜] H) :=
  (hT.smul_one_sub hl).ker_sq_eq_ker

/-- Let $T$ be a self-adjoint bounded operator on a Hilbert space $H$, let $\lambda \in \mathbb{K}$
be real, and let $k \ge 1$. Then $\ker (\lambda I - T)^k = \ker (\lambda I - T)$. -/
theorem ker_pow_smul_sub_eq_ker {T : H →L[𝕜] H} (hT : IsSelfAdjoint T) {l : 𝕜}
    (hl : starRingEnd 𝕜 l = l) {k : ℕ} (hk : 1 ≤ k) :
    LinearMap.ker (((l • (1 : H →L[𝕜] H) - T) ^ k : H →L[𝕜] H) : H →ₗ[𝕜] H)
      = LinearMap.ker ((l • (1 : H →L[𝕜] H) - T : H →L[𝕜] H) : H →ₗ[𝕜] H) :=
  (hT.smul_one_sub hl).ker_pow_eq_ker hk

end IsSelfAdjoint
