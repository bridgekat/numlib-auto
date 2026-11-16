/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Numlib.Analysis.Normed.Operator.CollectivelyCompact
import Numlib.Analysis.Normed.Ring.Inverse
import Numlib.Variational.ProjectionMethod

/-!
# Equations of the second kind

Let $X$ be a normed space over a nontrivially normed field $\mathbb{K}$, let $\mu \in \mathbb{K}$,
and let $K$ be a bounded linear operator on $X$. This module studies the equation of the second kind
$$(\mu - K) u = f$$
and its approximations: the conditions under which a projection method, a Nyström method or a
two-grid iteration for this equation is stable and convergent. The results are pure operator theory,
without kernels, quadrature or function spaces. The applications are integral equations, and for
this reason the module is next to `Numlib.IntegralEquations.Basic`. The presentation follows Chapter
12 of [han2009theoretical].

A projection method replaces the equation by $(\mu - PK) u_n = Pf$ with $u_n$ in the range of an
idempotent operator $P$. Its error is between two multiples of the approximation error $\|u - Pu\|$.
The iterated projection solution $\hat u_n = (f + K u_n) / \mu$ of Sloan solves
$(\mu - KP) \hat u_n = f$. Anselone's perturbation theorem transfers the invertibility of $\mu - T$
to $\mu - S$ for a compact $S$ under a condition on $(T - S) S$. The two-grid iteration solves a
fine equation $(\mu - K_n) u = f$ with only the coarse inverse $(\mu - K_m)^{-1}$.

## Main definitions

* `SecondKind.iterated`: the iterated projection solution $\hat u_n = \mu^{-1}(f + K u_n)$.
* `SecondKind.residual`: the residual $f - (\mu - K) u$.
* `SecondKind.twoGridStep`: one step of the two-grid residual correction.
* `SecondKind.twoGridOperator`: the operator $\mu^{-1} (\mu - K_m)^{-1} (K_n - K_m) K_n$ that
  multiplies the error of one two-grid step.

## Main results

* `SecondKind.sub_projection_eq`: the error equation $(\mu - PK)(u - u_n) = \mu (u - Pu)$ of a
  projection method.
* `SecondKind.exists_equiv_of_projection`: if $\|(\mu - K)^{-1}\| \, \|K - PK\| < 1$, then
  $\mu - PK$ is invertible, with a bound on its inverse.
* `SecondKind.norm_smul_sub_le_of_projection` and `SecondKind.norm_sub_le_of_projection`: the
  two-sided estimate $|\mu| \, \|u - Pu\| \le \|\mu - PK\| \, \|u - u_n\|$ and $\|u - u_n\| \le
  |\mu| \, \|(\mu - PK)^{-1}\| \, \|u - Pu\|$.
* `SecondKind.exists_equiv_smul_sub_comp_comm`: Jacobson's identity $(\mu - BA)^{-1} = \mu^{-1}(1 +
  B (\mu - AB)^{-1} A)$.
* `SecondKind.iterated_error_eq`: the error equation $(\mu - KP)(u - \hat u_n) = K(u - Pu)$ of the
  iterated projection solution.
* `SecondKind.exists_equiv_of_isCompactOperator`: Anselone's perturbation theorem.
* `SecondKind.norm_sub_le`: the error bound $\|u - z\| \le \|(\mu - S)^{-1}\| \, \|Tu - Su\|$.
* `SecondKind.twoGrid_error_eq`: one two-grid step multiplies the error by the two-grid operator.
* `SecondKind.tendsto_twoGridIterate`: if the two-grid operator has norm less than $1$, then the
  two-grid iteration converges.
* `SecondKind.eventually_norm_twoGridOperator_lt_one`: for a collectively compact family, the
  two-grid operator has norm less than $1$ when both indices are large.

## Proof outline

All error estimates for projection methods follow from the algebraic error equation
$(\mu - PK)(u - u_n) = \mu (u - Pu)$. The stability of a projection method is the Neumann series for
$\mu - PK = (\mu - K) + (K - PK)$. For a compact $K$ and projections $P_n$ that converge pointwise
to the identity, $\|K - P_n K\| \to 0$ by `tendsto_opNorm_comp_of_isCompactOperator`, so the
hypothesis holds for large $n$. Jacobson's identity with $A = P$ and $B = K$ relates the projection
equations to the equations of the iterated projection solution. The error equation of the iterated
projection solution has the factor $1 - P$ inside $K$, and this is the source of the
superconvergence of Sloan.

In Anselone's perturbation theorem, the Neumann series shows only that $\mu - S$ is injective. The
compactness of $S$ is used only through the Fredholm alternative, which makes an injective $\mu - S$
invertible. The hypothesis is on $(T - S) S$ and not on $T - S$. For a quadrature approximation
$S_n$ of an integral operator $T$, the norm $\|T - S_n\|$ does not tend to zero, but
$\|(T - S_n) S_n\|$ does (`IsCollectivelyCompact.tendsto_opNorm_sub_comp`). The two-grid operator
contains the same kind of product $(K_n - K_m) K_n$.

## Implementation notes

* An invertible operator is given as a `ContinuousLinearEquiv` `e : X ≃L[𝕜] X` together with an
  equation for its coercion, such as `(e : X →L[𝕜] X) = μ • 1 - K`. Then $\|(\mu - K)^{-1}\|$ is the
  norm of `e.symm`, and every bound is about a true inverse, never about the value of `Ring.inverse`
  at a noninvertible element.
* The projection method is `IsProjectionMethodSolution`: $u_n$ is in the range of $P$ and
  $P(\mu - K) u_n = Pf$ ([kress1998numerical]). The qualitative stability result is
  `exists_isProjectionMethodSolution_of_isCompactOperator`. This module adds the quantitative
  two-sided estimate.
-/

open Filter Topology

namespace SecondKind

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-! ### Projection methods -/

/-- Let $\mu \in \mathbb{K}$, let $K$ and $P$ be bounded operators on $X$ with $P^2 = P$, and let
$f, u, u_n \in X$. If $(\mu - K) u = f$ and $u_n$ is a projection method solution, that is,
$u_n$ is in the range of $P$ and $P (\mu - K) u_n = P f$, then
$$(\mu - PK)(u - u_n) = \mu (u - Pu).$$
This is (12.1.27) of [han2009theoretical].

The proof uses only linearity. It needs no bound on $K$, no invertibility and no compactness.
Both bounds `SecondKind.norm_smul_sub_le_of_projection` and
`SecondKind.norm_sub_le_of_projection` follow from this equation. -/
theorem sub_projection_eq {μ : 𝕜} {K P : X →L[𝕜] X} (hP : IsIdempotentElem P) {f u un : X}
    (hu : (μ • 1 - K : X →L[𝕜] X) u = f)
    (hun : IsProjectionMethodSolution ((μ • 1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X) f P un) :
    (μ • 1 - P ∘L K : X →L[𝕜] X) (u - un) = μ • (u - P u) := by
  have hPun : P un = un := IsProjectionMethodSolution.apply_eq_self hP hun
  have h2 : μ • un - P (K un) = μ • P u - P (K u) := by
    have h := hun.2
    simp only [ContinuousLinearMap.coe_coe, sub_apply, smul_apply, one_apply_eq_self, map_sub,
      map_smul, hPun] at h
    rw [h, ← hu]
    simp only [sub_apply, smul_apply, one_apply_eq_self, map_sub, map_smul]
  have hlhs : (μ • 1 - P ∘L K : X →L[𝕜] X) (u - un)
      = (μ • u - μ • P u) - ((μ • un - P (K un)) - (μ • P u - P (K u))) := by
    simp only [sub_apply, smul_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply, map_sub]
    abel
  rw [hlhs, h2, sub_self, sub_zero, ← smul_sub]

/-- Let $X$ be a Banach space, let $\mu \in \mathbb{K}$, and let $K$ and $P$ be bounded operators on
$X$. Suppose that $\mu - K$ is invertible and
$$\|(\mu - K)^{-1}\| \, \|K - PK\| < 1.$$
Then $\mu - PK$ is invertible, and
$$\|(\mu - PK)^{-1}\| \le \frac{\|(\mu - K)^{-1}\|}{1 - \|(\mu - K)^{-1}\| \, \|K - PK\|}.$$
This is Theorem 12.1.2 of [han2009theoretical].

The inverse of $\mu - K$ is `e.symm`, where `e` is a `ContinuousLinearEquiv` with coercion
$\mu - K$. The proof is the Neumann series for $\mu - PK = (\mu - K) + (K - PK)$. For a compact
$K$ and projections $P_n$ that converge pointwise to the identity, the hypothesis holds for all
large $n$ by `tendsto_opNorm_comp_of_isCompactOperator`. -/
theorem exists_equiv_of_projection [CompleteSpace X] {μ : 𝕜} {K P : X →L[𝕜] X} (e : X ≃L[𝕜] X)
    (he : (e : X →L[𝕜] X) = μ • 1 - K)
    (h : ‖(e.symm : X →L[𝕜] X)‖ * ‖K - P ∘L K‖ < 1) :
    ∃ e' : X ≃L[𝕜] X, (e' : X →L[𝕜] X) = μ • 1 - P ∘L K ∧
      ‖(e'.symm : X →L[𝕜] X)‖ ≤
        ‖(e.symm : X →L[𝕜] X)‖ / (1 - ‖(e.symm : X →L[𝕜] X)‖ * ‖K - P ∘L K‖) := by
  obtain ⟨e', he'coe, he'norm, -⟩ :=
    ContinuousLinearEquiv.exists_symm_norm_le_of_add e (K - P ∘L K) h
  exact ⟨e', by rw [he'coe, he]; abel, he'norm⟩

/-- Let $\mu \in \mathbb{K}$, let $K$ and $P$ be bounded operators on $X$ with $P^2 = P$, let
$(\mu - K) u = f$, and let $u_n$ be a projection method solution: $u_n$ is in the range of $P$
and $P(\mu - K) u_n = Pf$. Then
$$|\mu| \, \|u - Pu\| \le \|\mu - PK\| \, \|u - u_n\|.$$
This is the lower half of the two-sided estimate (12.1.24) of [han2009theoretical]: the method
cannot converge faster than the range of $P$ approximates the solution. -/
theorem norm_smul_sub_le_of_projection {μ : 𝕜} {K P : X →L[𝕜] X} (hP : IsIdempotentElem P)
    {f u un : X} (hu : (μ • 1 - K : X →L[𝕜] X) u = f)
    (hun : IsProjectionMethodSolution ((μ • 1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X) f P un) :
    ‖μ‖ * ‖u - P u‖ ≤ ‖(μ • 1 - P ∘L K : X →L[𝕜] X)‖ * ‖u - un‖ := by
  have hkey := sub_projection_eq hP hu hun
  calc ‖μ‖ * ‖u - P u‖ = ‖μ • (u - P u)‖ := (norm_smul μ (u - P u)).symm
    _ = ‖(μ • 1 - P ∘L K : X →L[𝕜] X) (u - un)‖ := by rw [hkey]
    _ ≤ ‖(μ • 1 - P ∘L K : X →L[𝕜] X)‖ * ‖u - un‖ := ContinuousLinearMap.le_opNorm _ _

/-- Let $\mu \in \mathbb{K}$, let $K$ and $P$ be bounded operators on $X$ with $P^2 = P$, and
suppose that $\mu - PK$ is invertible. Let $(\mu - K) u = f$, and let $u_n$ be a projection
method solution: $u_n$ is in the range of $P$ and $P(\mu - K) u_n = Pf$. Then
$$\|u - u_n\| \le |\mu| \, \|(\mu - PK)^{-1}\| \, \|u - Pu\|.$$
This is the upper half of the two-sided estimate of Theorem 12.1.2 and (12.1.24) of
[han2009theoretical].

The inverse of $\mu - PK$ is `e'.symm`. With `SecondKind.norm_smul_sub_le_of_projection` and the
uniform bound on $\|(\mu - P_n K)^{-1}\|$ from `SecondKind.exists_equiv_of_projection`, this
shows that $\|u - u_n\|$ and $\|u - P_n u\|$ tend to zero at the same rate. This is the
convergence analysis of collocation and Galerkin methods for equations of the second kind. -/
theorem norm_sub_le_of_projection {μ : 𝕜} {K P : X →L[𝕜] X} (hP : IsIdempotentElem P)
    {e' : X ≃L[𝕜] X} (he' : (e' : X →L[𝕜] X) = μ • 1 - P ∘L K) {f u un : X}
    (hu : (μ • 1 - K : X →L[𝕜] X) u = f)
    (hun : IsProjectionMethodSolution ((μ • 1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X) f P un) :
    ‖u - un‖ ≤ ‖μ‖ * ‖(e'.symm : X →L[𝕜] X)‖ * ‖u - P u‖ := by
  have hkey := sub_projection_eq hP hu hun
  have h1 : u - un = e'.symm (μ • (u - P u)) := by
    rw [← hkey, ← he', ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  rw [h1]
  calc ‖e'.symm (μ • (u - P u))‖ ≤ ‖(e'.symm : X →L[𝕜] X)‖ * ‖μ • (u - P u)‖ :=
        ContinuousLinearMap.le_opNorm (e'.symm : X →L[𝕜] X) (μ • (u - P u))
    _ = ‖μ‖ * ‖(e'.symm : X →L[𝕜] X)‖ * ‖u - P u‖ := by rw [norm_smul]; ring

/-! ### Jacobson's identity -/

/-- **Jacobson's identity.** Let $A$ and $B$ be bounded operators on $X$ and let $\mu \neq 0$. If
$\mu - AB$ is invertible, then $\mu - BA$ is invertible, and
$$(\mu - BA)^{-1} = \mu^{-1} \left( 1 + B (\mu - AB)^{-1} A \right).$$
This is Lemma 12.3.1 of [han2009theoretical].

The inverse of $\mu - AB$ is `e.symm`, and the result gives a `ContinuousLinearEquiv` `e'` with
coercion $\mu - BA$. With $A = P$ and $B = K$, the identity relates the projection equation
$(\mu - PK) u_n = Pf$ to the equation $(\mu - KP) \hat u_n = f$ of the iterated projection
solution. Each of the two inverses is bounded in terms of the other. -/
theorem exists_equiv_smul_sub_comp_comm {μ : 𝕜} (hμ : μ ≠ 0) {A B : X →L[𝕜] X} (e : X ≃L[𝕜] X)
    (he : (e : X →L[𝕜] X) = μ • 1 - A ∘L B) :
    ∃ e' : X ≃L[𝕜] X, (e' : X →L[𝕜] X) = μ • 1 - B ∘L A ∧
      (e'.symm : X →L[𝕜] X) = μ⁻¹ • (1 + B ∘L ((e.symm : X →L[𝕜] X) ∘L A)) := by
  simp only [← ContinuousLinearMap.mul_def] at he ⊢
  obtain ⟨R, hR⟩ : ∃ R : X →L[𝕜] X, (e.symm : X →L[𝕜] X) = R := ⟨_, rfl⟩
  rw [hR]
  have hRr : ((μ • 1 : X →L[𝕜] X) - A * B) * R = 1 := by
    rw [← hR, ← he]; ext x; simp
  have hRl : R * ((μ • 1 : X →L[𝕜] X) - A * B) = 1 := by
    rw [← hR, ← he]; ext x; simp
  -- `μ - B A` intertwines with `μ - A B` through `A` and through `B`
  have hBl : ((μ • 1 : X →L[𝕜] X) - B * A) * B = B * ((μ • 1 : X →L[𝕜] X) - A * B) := by
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, mul_assoc]
  have hAr : A * ((μ • 1 : X →L[𝕜] X) - B * A) = ((μ • 1 : X →L[𝕜] X) - A * B) * A := by
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, mul_assoc]
  have hcancelR : ((μ • 1 : X →L[𝕜] X) - A * B) * (R * A) = A := by
    rw [← mul_assoc, hRr, one_mul]
  have hcancelL : R * (((μ • 1 : X →L[𝕜] X) - A * B) * A) = A := by
    rw [← mul_assoc, hRl, one_mul]
  have hGF : ((μ • 1 : X →L[𝕜] X) - B * A) * (μ⁻¹ • (1 + B * (R * A))) = 1 := by
    have hstep : ((μ • 1 : X →L[𝕜] X) - B * A) * (1 + B * (R * A)) = μ • 1 := by
      calc ((μ • 1 : X →L[𝕜] X) - B * A) * (1 + B * (R * A))
          = ((μ • 1 : X →L[𝕜] X) - B * A)
            + (((μ • 1 : X →L[𝕜] X) - B * A) * B) * (R * A) := by
            rw [mul_add, mul_one, ← mul_assoc]
        _ = ((μ • 1 : X →L[𝕜] X) - B * A)
            + B * (((μ • 1 : X →L[𝕜] X) - A * B) * (R * A)) := by rw [hBl, mul_assoc]
        _ = μ • 1 := by rw [hcancelR]; abel
    rw [mul_smul_comm, hstep, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  have hFG : (μ⁻¹ • (1 + B * (R * A))) * ((μ • 1 : X →L[𝕜] X) - B * A) = 1 := by
    have hstep : (1 + B * (R * A)) * ((μ • 1 : X →L[𝕜] X) - B * A) = μ • 1 := by
      calc (1 + B * (R * A)) * ((μ • 1 : X →L[𝕜] X) - B * A)
          = ((μ • 1 : X →L[𝕜] X) - B * A)
            + B * ((R * A) * ((μ • 1 : X →L[𝕜] X) - B * A)) := by
            rw [add_mul, one_mul, mul_assoc]
        _ = ((μ • 1 : X →L[𝕜] X) - B * A)
            + B * (R * (((μ • 1 : X →L[𝕜] X) - A * B) * A)) := by rw [mul_assoc, hAr]
        _ = μ • 1 := by rw [hcancelL]; abel
    rw [smul_mul_assoc, hstep, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  exact ⟨ContinuousLinearEquiv.ofUnit ⟨_, _, hGF, hFG⟩, rfl, by ext x; rfl⟩

/-- **Jacobson's identity**, qualitative form. Let $A$ and $B$ be bounded operators on $X$ and let
$\mu \neq 0$. Then $\mu - AB$ is invertible if and only if $\mu - BA$ is invertible. This is
Lemma 12.3.1 of [han2009theoretical]. -/
theorem isUnit_smul_sub_comp_comm {μ : 𝕜} (hμ : μ ≠ 0) (A B : X →L[𝕜] X) :
    IsUnit (μ • 1 - A ∘L B : X →L[𝕜] X) ↔ IsUnit (μ • 1 - B ∘L A : X →L[𝕜] X) := by
  have key : ∀ C D : X →L[𝕜] X, IsUnit (μ • 1 - C ∘L D : X →L[𝕜] X) →
      IsUnit (μ • 1 - D ∘L C : X →L[𝕜] X) := by
    intro C D hCD
    obtain ⟨u, hu⟩ := hCD
    obtain ⟨e', he', -⟩ :=
      exists_equiv_smul_sub_comp_comm hμ (ContinuousLinearEquiv.ofUnit u) hu
    exact ⟨ContinuousLinearEquiv.toUnit e', he'⟩
  exact ⟨key A B, key B A⟩

/-! ### The iterated projection solution -/

/-- Let $\mu \in \mathbb{K}$, let $K$ be a bounded operator on $X$, and let $f, u_n \in X$. The
**iterated projection solution** of Sloan is
$$\hat u_n = \mu^{-1} (f + K u_n).$$
This is (12.3.1) of [han2009theoretical]. When $u_n$ is the projection method solution of
$(\mu - K) u = f$, the vector $\hat u_n$ is one fixed-point step from $u_n$, and it is a better
approximation for every size of $\|K\|$.

For $\mu = 0$ the definition gives $0$, because $0^{-1} = 0$ in Lean. -/
def iterated (μ : 𝕜) (K : X →L[𝕜] X) (f un : X) : X := μ⁻¹ • (f + K un)

/-- Let $\mu \neq 0$, let $K$ and $P$ be bounded operators on $X$ with $P^2 = P$, and let $u_n$ be a
projection method solution of $(\mu - K) u = f$: $u_n$ is in the range of $P$ and
$P(\mu - K) u_n = Pf$. Then the iterated projection solution satisfies
$$P \hat u_n = u_n.$$
This is (12.3.2) of [han2009theoretical]. -/
theorem apply_iterated {μ : 𝕜} (hμ : μ ≠ 0) {K P : X →L[𝕜] X} (hP : IsIdempotentElem P) {f un : X}
    (hun : IsProjectionMethodSolution ((μ • 1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X) f P un) :
    P (iterated μ K f un) = un := by
  have hPun : P un = un := IsProjectionMethodSolution.apply_eq_self hP hun
  have h := hun.2
  simp only [ContinuousLinearMap.coe_coe, sub_apply, smul_apply, one_apply_eq_self, map_sub,
    map_smul, hPun] at h
  simp only [iterated, map_smul, map_add, ← h]
  rw [sub_add_cancel, smul_smul, inv_mul_cancel₀ hμ, one_smul]

/-- Let $\mu \neq 0$, let $K$ and $P$ be bounded operators on $X$ with $P^2 = P$, and let $u_n$ be a
projection method solution of $(\mu - K) u = f$: $u_n$ is in the range of $P$ and
$P(\mu - K) u_n = Pf$. Then the iterated projection solution satisfies
$$(\mu - KP) \hat u_n = f.$$
This is (12.3.3) of [han2009theoretical]. By Jacobson's identity, this equation is solvable when
the projection equation is. -/
theorem smul_sub_comp_iterated {μ : 𝕜} (hμ : μ ≠ 0) {K P : X →L[𝕜] X} (hP : IsIdempotentElem P)
    {f un : X} (hun : IsProjectionMethodSolution ((μ • 1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X) f P un) :
    (μ • 1 - K ∘L P : X →L[𝕜] X) (iterated μ K f un) = f := by
  have hPit : P (iterated μ K f un) = un := apply_iterated hμ hP hun
  simp only [sub_apply, smul_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply, hPit]
  simp only [iterated, smul_smul, mul_inv_cancel₀ hμ, one_smul]
  abel

/-- Let $\mu \neq 0$, let $K$ and $P$ be bounded operators on $X$ with $P^2 = P$, let
$(\mu - K) u = f$, and let $u_n$ be a projection method solution: $u_n$ is in the range of $P$
and $P(\mu - K) u_n = Pf$. Then the iterated projection solution satisfies
$$(\mu - KP)(u - \hat u_n) = K (u - Pu).$$
This is (12.3.11) of [han2009theoretical].

The right side has the factor $1 - P$ inside $K$. This is the source of the superconvergence of
Sloan: the error is bounded by a multiple of $\|K(1 - P)\| \, \|u - Pu\|$, which is better by
one factor than the bound for $\|u - u_n\|$. -/
theorem iterated_error_eq {μ : 𝕜} (hμ : μ ≠ 0) {K P : X →L[𝕜] X} (hP : IsIdempotentElem P)
    {f u un : X} (hu : (μ • 1 - K : X →L[𝕜] X) u = f)
    (hun : IsProjectionMethodSolution ((μ • 1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X) f P un) :
    (μ • 1 - K ∘L P : X →L[𝕜] X) (u - iterated μ K f un) = K (u - P u) := by
  have h1 : (μ • 1 - K ∘L P : X →L[𝕜] X) (iterated μ K f un) = f :=
    smul_sub_comp_iterated hμ hP hun
  rw [map_sub, h1, ← hu]
  simp only [sub_apply, smul_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply, map_sub]
  abel

/-! ### Anselone's perturbation theorem -/

/-- **Anselone's perturbation theorem.** Let $X$ be a Banach space, let $S$ and $T$ be bounded
operators on $X$ with $S$ compact, and let $\mu \neq 0$. Suppose that $\mu - T$ is invertible
and
$$\|(\mu - T)^{-1}\| \, \|(T - S) S\| < |\mu|.$$
Then $\mu - S$ is invertible, and
$$\|(\mu - S)^{-1}\| \le \frac{1 + \|(\mu - T)^{-1}\| \, \|S\|}{|\mu| - \|(\mu - T)^{-1}\| \,
  \|(T - S) S\|}.$$
This is Theorem 12.4.3 of [han2009theoretical]; see also [anselone1971collectively].

The inverse of $\mu - T$ is `e.symm`. The hypothesis is on $(T - S) S$ and not on $T - S$. For
this reason the theorem applies to a quadrature approximation $S$ of an integral operator $T$,
where $\|T - S\|$ does not tend to zero. For a collectively compact family $S_n$ that converges
pointwise to $T$, $\|(T - S_n) S_n\| \to 0$ by `IsCollectivelyCompact.tendsto_opNorm_sub_comp`.

The candidate inverse is $\mu^{-1}(1 + (\mu - T)^{-1} S)$. It satisfies $\mu^{-1}(1 + (\mu -
T)^{-1} S)(\mu - S) = 1 + \mu^{-1}(\mu - T)^{-1}(T - S) S$, and the right side is invertible by
the Neumann series. So $\mu - S$ is injective. The compactness of $S$ is used only here: the
Fredholm alternative makes the injective operator $\mu - S$ invertible. -/
theorem exists_equiv_of_isCompactOperator [CompleteSpace X] {μ : 𝕜} (hμ : μ ≠ 0)
    {S T : X →L[𝕜] X} (hS : IsCompactOperator S) {e : X ≃L[𝕜] X}
    (he : (e : X →L[𝕜] X) = μ • 1 - T)
    (h : ‖(e.symm : X →L[𝕜] X)‖ * ‖(T - S) ∘L S‖ < ‖μ‖) :
    ∃ e' : X ≃L[𝕜] X, (e' : X →L[𝕜] X) = μ • 1 - S ∧
      ‖(e'.symm : X →L[𝕜] X)‖ ≤ (1 + ‖(e.symm : X →L[𝕜] X)‖ * ‖S‖) /
        (‖μ‖ - ‖(e.symm : X →L[𝕜] X)‖ * ‖(T - S) ∘L S‖) := by
  have hcs : ((T - S) ∘L S : X →L[𝕜] X) = (T - S) * S := rfl
  rw [hcs] at h ⊢
  obtain ⟨R, hR⟩ : ∃ R : X →L[𝕜] X, (e.symm : X →L[𝕜] X) = R := ⟨_, rfl⟩
  rw [hR] at h ⊢
  have hμpos : (0 : ℝ) < ‖μ‖ := norm_pos_iff.2 hμ
  have hμ0 : ‖μ‖ ≠ 0 := hμpos.ne'
  have hRA : R * ((μ • 1 : X →L[𝕜] X) - T) = 1 := by
    rw [← hR, ← he]; ext x; simp
  -- the small correction term, and the geometric series applied to it
  obtain ⟨t, htdef⟩ : ∃ t : X →L[𝕜] X, t = μ⁻¹ • (R * ((T - S) * S)) := ⟨_, rfl⟩
  have htnorm : ‖μ‖ * ‖t‖ ≤ ‖R‖ * ‖(T - S) * S‖ := by
    rw [htdef, norm_smul, norm_inv, ← mul_assoc, mul_inv_cancel₀ hμ0, one_mul]
    exact norm_mul_le _ _
  have htlt : ‖t‖ < 1 := by
    have h1 : ‖μ‖ * ‖t‖ < ‖μ‖ * 1 := by rw [mul_one]; linarith
    exact lt_of_mul_lt_mul_left h1 hμpos.le
  obtain ⟨w, hw⟩ : IsUnit ((1 : X →L[𝕜] X) + t) := by
    have hu := isUnit_one_sub_of_norm_lt_one (x := -t) (by rwa [norm_neg])
    rwa [sub_neg_eq_add] at hu
  have hwinv : (↑w⁻¹ : X →L[𝕜] X) * ((1 : X →L[𝕜] X) + t) = 1 := by
    rw [← hw]; exact w.inv_mul
  have hwnorm : ‖(↑w⁻¹ : X →L[𝕜] X)‖ ≤ 1 + ‖(↑w⁻¹ : X →L[𝕜] X)‖ * ‖t‖ := by
    have hid : (↑w⁻¹ : X →L[𝕜] X) = 1 - (↑w⁻¹ : X →L[𝕜] X) * t := by
      rw [← hwinv, mul_add, mul_one]; abel
    calc ‖(↑w⁻¹ : X →L[𝕜] X)‖ = ‖(1 : X →L[𝕜] X) - (↑w⁻¹ : X →L[𝕜] X) * t‖ := by rw [← hid]
      _ ≤ ‖(1 : X →L[𝕜] X)‖ + ‖(↑w⁻¹ : X →L[𝕜] X) * t‖ := norm_sub_le _ _
      _ ≤ 1 + ‖(↑w⁻¹ : X →L[𝕜] X)‖ * ‖t‖ :=
          add_le_add ContinuousLinearMap.norm_id_le (norm_mul_le _ _)
  -- the factorisation `(1 + R S) (μ - S) = μ + R (T - S) S`, which rests on `S (μ - S) = (μ - S) S`
  have hcomm : S * ((μ • 1 : X →L[𝕜] X) - S) = ((μ • 1 : X →L[𝕜] X) - S) * S := by
    rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  have hTS : (T - S : X →L[𝕜] X) = ((μ • 1 : X →L[𝕜] X) - S) - ((μ • 1 : X →L[𝕜] X) - T) := by
    abel
  have h1 : R * (T - S : X →L[𝕜] X) = R * ((μ • 1 : X →L[𝕜] X) - S) - 1 := by
    rw [hTS, mul_sub, hRA]
  have h2 : (R * ((μ • 1 : X →L[𝕜] X) - S) - 1) * S
      = R * (((μ • 1 : X →L[𝕜] X) - S) * S) - S := by
    rw [sub_mul, one_mul, mul_assoc]
  have hprod : ((1 : X →L[𝕜] X) + R * S) * ((μ • 1 : X →L[𝕜] X) - S)
      = μ • 1 + R * ((T - S) * S) := by
    calc ((1 : X →L[𝕜] X) + R * S) * ((μ • 1 : X →L[𝕜] X) - S)
        = ((μ • 1 : X →L[𝕜] X) - S) + R * (S * ((μ • 1 : X →L[𝕜] X) - S)) := by
          rw [add_mul, one_mul, mul_assoc]
      _ = ((μ • 1 : X →L[𝕜] X) - S) + R * (((μ • 1 : X →L[𝕜] X) - S) * S) := by rw [hcomm]
      _ = ((μ • 1 : X →L[𝕜] X) - S) + (R * ((μ • 1 : X →L[𝕜] X) - S) - 1) * S + S := by
          rw [h2]; abel
      _ = μ • 1 + R * ((T - S) * S) := by rw [← h1, mul_assoc]; abel
  have hprod' : μ⁻¹ • (((1 : X →L[𝕜] X) + R * S) * ((μ • 1 : X →L[𝕜] X) - S)) = 1 + t := by
    rw [hprod, htdef, smul_add, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  -- hence `μ - S` has a left inverse, so it is injective
  obtain ⟨V, hVdef⟩ : ∃ V : X →L[𝕜] X, V = μ⁻¹ • ((↑w⁻¹ : X →L[𝕜] X) * (1 + R * S)) := ⟨_, rfl⟩
  have hV : V * ((μ • 1 : X →L[𝕜] X) - S) = 1 := by
    rw [hVdef, smul_mul_assoc, mul_assoc, ← mul_smul_comm, hprod', hwinv]
  have hVx : ∀ x : X, V ((μ • 1 - S : X →L[𝕜] X) x) = x := by
    intro x
    have hx := congrArg (fun Z : X →L[𝕜] X => Z x) hV
    simpa using hx
  have hinj : Function.Injective (μ • 1 - S : X →L[𝕜] X) := by
    intro x y hxy
    rw [← hVx x, ← hVx y, hxy]
  -- and the Fredholm alternative for the compact `S` promotes injectivity to invertibility
  have hres : μ ∈ resolventSet 𝕜 S := by
    refine (IsCompactOperator.hasEigenvalue_or_mem_resolventSet hS hμ).resolve_left ?_
    intro hev
    obtain ⟨x, hx, hx0⟩ := hev.exists_hasEigenvector
    refine hx0 (hinj ?_)
    have hSx : S x = μ • x := Module.End.mem_eigenspace_iff.1 hx
    simp [hSx]
  have hunitS : IsUnit ((μ • 1 : X →L[𝕜] X) - S) := by
    have h' : IsUnit (algebraMap 𝕜 (X →L[𝕜] X) μ - S) := hres
    rwa [Algebra.algebraMap_eq_smul_one] at h'
  obtain ⟨uS, huS⟩ := hunitS
  have hVinv : V = (↑uS⁻¹ : X →L[𝕜] X) := by
    calc V = V * ((uS : X →L[𝕜] X) * (↑uS⁻¹ : X →L[𝕜] X)) := by rw [uS.mul_inv, mul_one]
      _ = (V * ((μ • 1 : X →L[𝕜] X) - S)) * (↑uS⁻¹ : X →L[𝕜] X) := by rw [huS, mul_assoc]
      _ = (↑uS⁻¹ : X →L[𝕜] X) := by rw [hV, one_mul]
  refine ⟨ContinuousLinearEquiv.ofUnit uS, huS, ?_⟩
  have hsymm : ((ContinuousLinearEquiv.ofUnit uS).symm : X →L[𝕜] X) = V := by
    rw [hVinv]; ext x; rfl
  rw [hsymm]
  -- the bound on the inverse
  have hnq : 0 < ‖μ‖ - ‖R‖ * ‖(T - S) * S‖ := by linarith
  have hone : ‖(1 : X →L[𝕜] X) + R * S‖ ≤ 1 + ‖R‖ * ‖S‖ :=
    (norm_add_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le (norm_mul_le _ _))
  have hVle : ‖V‖ ≤ ‖μ‖⁻¹ * ‖(↑w⁻¹ : X →L[𝕜] X)‖ * (1 + ‖R‖ * ‖S‖) := by
    calc ‖V‖ = ‖μ‖⁻¹ * ‖(↑w⁻¹ : X →L[𝕜] X) * ((1 : X →L[𝕜] X) + R * S)‖ := by
          rw [hVdef, norm_smul, norm_inv]
      _ ≤ ‖μ‖⁻¹ * (‖(↑w⁻¹ : X →L[𝕜] X)‖ * ‖(1 : X →L[𝕜] X) + R * S‖) :=
          mul_le_mul_of_nonneg_left (norm_mul_le _ _) (by positivity)
      _ ≤ ‖μ‖⁻¹ * (‖(↑w⁻¹ : X →L[𝕜] X)‖ * (1 + ‖R‖ * ‖S‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hone (norm_nonneg _))
            (by positivity)
      _ = ‖μ‖⁻¹ * ‖(↑w⁻¹ : X →L[𝕜] X)‖ * (1 + ‖R‖ * ‖S‖) := by ring
  have hwq : ‖(↑w⁻¹ : X →L[𝕜] X)‖ * (‖μ‖ - ‖R‖ * ‖(T - S) * S‖) ≤ ‖μ‖ := by
    nlinarith [mul_le_mul_of_nonneg_left htnorm (norm_nonneg (↑w⁻¹ : X →L[𝕜] X)),
      mul_le_mul_of_nonneg_left hwnorm hμpos.le, norm_nonneg (↑w⁻¹ : X →L[𝕜] X)]
  rw [le_div_iff₀ hnq]
  calc ‖V‖ * (‖μ‖ - ‖R‖ * ‖(T - S) * S‖)
      ≤ (‖μ‖⁻¹ * ‖(↑w⁻¹ : X →L[𝕜] X)‖ * (1 + ‖R‖ * ‖S‖)) *
          (‖μ‖ - ‖R‖ * ‖(T - S) * S‖) := mul_le_mul_of_nonneg_right hVle hnq.le
    _ = (‖μ‖⁻¹ * (1 + ‖R‖ * ‖S‖)) *
          (‖(↑w⁻¹ : X →L[𝕜] X)‖ * (‖μ‖ - ‖R‖ * ‖(T - S) * S‖)) := by ring
    _ ≤ (‖μ‖⁻¹ * (1 + ‖R‖ * ‖S‖)) * ‖μ‖ := mul_le_mul_of_nonneg_left hwq (by positivity)
    _ = 1 + ‖R‖ * ‖S‖ := by field_simp

/-- Let $\mu \in \mathbb{K}$, let $S$ and $T$ be bounded operators on $X$, and suppose that
$\mu - S$ is invertible. If $(\mu - T) u = f$ and $(\mu - S) z = f$, then
$$\|u - z\| \le \|(\mu - S)^{-1}\| \, \|Tu - Su\|.$$
This is (12.4.24) of [han2009theoretical].

The inverse of $\mu - S$ is `e.symm`. The right side is the consistency error at the exact
solution, not an operator norm. With the uniform bound of
`SecondKind.exists_equiv_of_isCompactOperator`, this gives the convergence analysis of the
Nyström method. -/
theorem norm_sub_le {μ : 𝕜} {S T : X →L[𝕜] X} {e : X ≃L[𝕜] X}
    (he : (e : X →L[𝕜] X) = μ • 1 - S) {f u z : X} (hu : (μ • 1 - T : X →L[𝕜] X) u = f)
    (hz : (μ • 1 - S : X →L[𝕜] X) z = f) :
    ‖u - z‖ ≤ ‖(e.symm : X →L[𝕜] X)‖ * ‖T u - S u‖ := by
  have h : (μ • 1 - T : X →L[𝕜] X) u = e z := by
    rw [hu, ← hz, ← he, ContinuousLinearEquiv.coe_coe]
  have hbound := ContinuousLinearEquiv.norm_sub_le_of_apply_eq (μ • 1 - T : X →L[𝕜] X) e h
  have heq : ((μ • 1 - T : X →L[𝕜] X) - (e : X →L[𝕜] X)) u = S u - T u := by
    rw [he]
    simp only [sub_apply, smul_apply, one_apply_eq_self]
    abel
  rwa [heq, norm_sub_rev (S u) (T u)] at hbound

/-! ### The two-grid iteration -/

/-- The **residual** $f - (\mu - K) u$ of the equation $(\mu - K) u = f$ at $u \in X$. -/
def residual (μ : 𝕜) (K : X →L[𝕜] X) (f u : X) : X := f - (μ • 1 - K : X →L[𝕜] X) u

/-- Let $\mu \in \mathbb{K}$, let $K_n$ be a bounded operator on $X$, and let `e` be an invertible
operator on $X$, which stands for the coarse operator $\mu - K_m$. The **two-grid step** for the
fine equation $(\mu - K_n) u = f$ maps $u$ to
$$u + \mu^{-1} \left( r + (\mu - K_m)^{-1} K_n r \right), \qquad r = f - (\mu - K_n) u.$$
This is (12.6.20)–(12.6.22) of [han2009theoretical].

The coarse inverse $(\mu - K_m)^{-1}$ is `e.symm`. It acts as the approximate inverse of a
residual correction method, and it is the only inverse that the iteration uses. The operator
$K_m$ does not appear as an argument: it enters only through `e`. -/
def twoGridStep (μ : 𝕜) (e : X ≃L[𝕜] X) (Kn : X →L[𝕜] X) (f u : X) : X :=
  u + μ⁻¹ • (residual μ Kn f u + e.symm (Kn (residual μ Kn f u)))

/-- Let $\mu \in \mathbb{K}$, let $K_m$ and $K_n$ be bounded operators on $X$, and let `e` be an
invertible operator, which stands for $\mu - K_m$. The **two-grid operator** is
$$\mu^{-1} (\mu - K_m)^{-1} (K_n - K_m) K_n,$$
with $(\mu - K_m)^{-1}$ the inverse `e.symm`. This is (12.6.28) of [han2009theoretical]. One
step of `SecondKind.twoGridStep` multiplies the error by this operator
(`SecondKind.twoGrid_error_eq`). -/
def twoGridOperator (μ : 𝕜) (e : X ≃L[𝕜] X) (Km Kn : X →L[𝕜] X) : X →L[𝕜] X :=
  μ⁻¹ • ((e.symm : X →L[𝕜] X) ∘L ((Kn - Km) ∘L Kn))

/-- Let $\mu \neq 0$, let $K_m$ and $K_n$ be bounded operators on $X$, and suppose that $\mu - K_m$
is invertible. If $u^*$ solves the fine equation $(\mu - K_n) u^* = f$, then for every $u \in X$
the two-grid step $u'$ from $u$ satisfies
$$u^* - u' = \mu^{-1} (\mu - K_m)^{-1} (K_n - K_m) K_n \, (u^* - u).$$
This is (12.6.27)–(12.6.28) of [han2009theoretical].

The factor $K_n - K_m$ appears composed with $K_n$. Collective compactness makes such a product
small. -/
theorem twoGrid_error_eq {μ : 𝕜} (hμ : μ ≠ 0) {e : X ≃L[𝕜] X} {Km Kn : X →L[𝕜] X}
    (he : (e : X →L[𝕜] X) = μ • 1 - Km) {f ustar : X}
    (hstar : (μ • 1 - Kn : X →L[𝕜] X) ustar = f) (u : X) :
    ustar - twoGridStep μ e Kn f u = twoGridOperator μ e Km Kn (ustar - u) := by
  have hKmeq : Km = μ • 1 - (e : X →L[𝕜] X) := by rw [he]; abel
  have hKm : ∀ y : X, e.symm (Km y) = μ • e.symm y - y := by
    intro y
    rw [hKmeq]
    simp only [sub_apply, smul_apply, one_apply_eq_self, ContinuousLinearEquiv.coe_coe, map_sub,
      map_smul, ContinuousLinearEquiv.symm_apply_apply]
  have hr : residual μ Kn f u = (μ • 1 - Kn : X →L[𝕜] X) (ustar - u) := by
    rw [residual, ← hstar, map_sub]
  have hkey : residual μ Kn f u + e.symm (Kn (residual μ Kn f u))
      = μ • (ustar - u) - e.symm ((Kn - Km) (Kn (ustar - u))) := by
    rw [hr]
    simp only [sub_apply, smul_apply, one_apply_eq_self, map_sub, map_smul, hKm]
    module
  simp only [twoGridStep, twoGridOperator, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe]
  rw [hkey, smul_sub, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  abel

/-- Let $\mu \neq 0$, let $K_m$ and $K_n$ be bounded operators on $X$, and suppose that $\mu - K_m$
is invertible. Let $(\mu - K_n) u^* = f$, let $u_0 \in X$, and let $u_k$ be the $k$-th iterate
of the two-grid step from $u_0$. Then, with $M$ the two-grid operator,
$$\|u^* - u_k\| \le \|M\|^k \, \|u^* - u_0\|.$$
-/
theorem norm_sub_twoGridStep_iterate_le {μ : 𝕜} (hμ : μ ≠ 0) {e : X ≃L[𝕜] X} {Km Kn : X →L[𝕜] X}
    (he : (e : X →L[𝕜] X) = μ • 1 - Km) {f ustar : X}
    (hstar : (μ • 1 - Kn : X →L[𝕜] X) ustar = f) (u₀ : X) (k : ℕ) :
    ‖ustar - (twoGridStep μ e Kn f)^[k] u₀‖ ≤
      ‖twoGridOperator μ e Km Kn‖ ^ k * ‖ustar - u₀‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', twoGrid_error_eq hμ he hstar]
    calc ‖twoGridOperator μ e Km Kn (ustar - (twoGridStep μ e Kn f)^[k] u₀)‖
        ≤ ‖twoGridOperator μ e Km Kn‖ * ‖ustar - (twoGridStep μ e Kn f)^[k] u₀‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖twoGridOperator μ e Km Kn‖ * (‖twoGridOperator μ e Km Kn‖ ^ k * ‖ustar - u₀‖) :=
          mul_le_mul_of_nonneg_left ih (norm_nonneg _)
      _ = ‖twoGridOperator μ e Km Kn‖ ^ (k + 1) * ‖ustar - u₀‖ := by ring

/-- Let $\mu \neq 0$, let $K_m$ and $K_n$ be bounded operators on $X$, and suppose that $\mu - K_m$
is invertible. If the two-grid operator $M = \mu^{-1} (\mu - K_m)^{-1} (K_n - K_m) K_n$
satisfies $\|M\| < 1$ and $(\mu - K_n) u^* = f$, then for every starting point $u_0 \in X$ the
iterates of the two-grid step converge to $u^*$. This is Theorem 12.6.1 of [han2009theoretical].

The convergence is geometric, by `SecondKind.norm_sub_twoGridStep_iterate_le`. For a
collectively compact family that converges pointwise, the hypothesis $\|M\| < 1$ holds when both
indices are large (`SecondKind.eventually_norm_twoGridOperator_lt_one`). -/
theorem tendsto_twoGridIterate {μ : 𝕜} (hμ : μ ≠ 0) {e : X ≃L[𝕜] X} {Km Kn : X →L[𝕜] X}
    (he : (e : X →L[𝕜] X) = μ • 1 - Km) (hM : ‖twoGridOperator μ e Km Kn‖ < 1) {f ustar : X}
    (hstar : (μ • 1 - Kn : X →L[𝕜] X) ustar = f) (u₀ : X) :
    Tendsto (fun k => (twoGridStep μ e Kn f)^[k] u₀) atTop (𝓝 ustar) := by
  have hlim : Tendsto (fun k => ‖twoGridOperator μ e Km Kn‖ ^ k * ‖ustar - u₀‖) atTop (𝓝 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hM).mul_const ‖ustar - u₀‖
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm (fun k => ?_) hlim
  rw [norm_sub_rev]
  exact norm_sub_twoGridStep_iterate_le hμ he hstar u₀ k

/-! ### A uniform estimate for collectively compact families -/

/-- Let $X$ be a Banach space, let $(K_n)$ be a collectively compact sequence of bounded operators
on $X$ that converges pointwise to $L$, and let $\varepsilon > 0$. Then for all sufficiently
large $m$,
$$\|(L - K_m) K_n\| < \varepsilon \quad \text{for every } n.$$

The bound is uniform in $n$, not only on the diagonal $n = m$. This is
`IsCollectivelyCompact.tendsto_opNorm_sub_comp` with the two indices separated, and the proof is
the same: the convergence $K_m \to L$ is uniform on a compact set that contains the image of a
neighborhood of the origin under every $K_n$. The result is a companion of that lemma in
`Numlib.Analysis.Normed.Operator.CollectivelyCompact`. -/
theorem eventually_forall_opNorm_sub_comp_lt [CompleteSpace X] {K : ℕ → X →L[𝕜] X}
    {L : X →L[𝕜] X} (hK : IsCollectivelyCompact K)
    (hL : ∀ x, Tendsto (fun n => K n x) atTop (𝓝 (L x))) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m in atTop, ∀ n, ‖(L - K m) ∘L K n‖ < ε := by
  obtain ⟨U, hU, hcpt⟩ := hK
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
  have hunif : TendstoUniformlyOn (fun n => (K n : X → X)) L atTop
      (closure (⋃ i, K i '' U)) := tendstoUniformlyOn_of_tendsto_of_isCompact hL hcpt
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hunif (ε * r / (2 * ‖c‖)) (by positivity))
  filter_upwards [eventually_ge_atTop N] with m hm n
  have hbound : ∀ x : X, ‖x‖ < r → ‖((L - K m) ∘L K n) x‖ ≤ ε * r / (2 * ‖c‖) := by
    intro x hx
    have hmem : K n x ∈ closure (⋃ i, K i '' U) :=
      subset_closure (Set.mem_iUnion.2 ⟨n, ⟨x, hrU (mem_ball_zero_iff.2 hx), rfl⟩⟩)
    have hd := hN m hm (K n x) hmem
    rw [dist_eq_norm] at hd
    simpa using hd.le
  refine lt_of_le_of_lt
    (ContinuousLinearMap.opNorm_le_of_forall_norm_lt hc hr (by positivity) hbound) ?_
  have heq : ‖c‖ / r * (ε * r / (2 * ‖c‖)) = ε / 2 := by field_simp
  rw [heq]
  linarith

/-- Let $X$ be a Banach space, let $\mu \neq 0$, and let $(K_p)$ be a collectively compact sequence
of bounded operators on $X$ that converges pointwise to $L$, with $\mu - L$ invertible. Then for
every sufficiently large $m$, the coarse operator $\mu - K_m$ is invertible, and for every
$n \ge m$ the two-grid operator $\mu^{-1} (\mu - K_m)^{-1} (K_n - K_m) K_n$ has norm less than
$1$. This is Theorem 12.6.1 of [han2009theoretical]. With `SecondKind.tendsto_twoGridIterate`,
it gives the convergence of the two-grid method.

The uniform bound on the coarse inverses comes from
`SecondKind.exists_equiv_of_isCompactOperator` and `IsCollectivelyCompact.exists_opNorm_le`. The
product $(K_n - K_m) K_n$ is the sum of $(K_n - L) K_n$, which is small for large $n$ by
`IsCollectivelyCompact.tendsto_opNorm_sub_comp`, and $(L - K_m) K_n$, which is small for large
$m$ uniformly in $n$ by `SecondKind.eventually_forall_opNorm_sub_comp_lt`. For this reason both
indices must be large, and the conclusion is for $n \ge m$. -/
theorem eventually_norm_twoGridOperator_lt_one [CompleteSpace X] {μ : 𝕜} (hμ : μ ≠ 0)
    {K : ℕ → X →L[𝕜] X} {L : X →L[𝕜] X} (hK : IsCollectivelyCompact K)
    (hL : ∀ x, Tendsto (fun n => K n x) atTop (𝓝 (L x))) {e : X ≃L[𝕜] X}
    (he : (e : X →L[𝕜] X) = μ • 1 - L) :
    ∀ᶠ m in atTop, ∃ em : X ≃L[𝕜] X, (em : X →L[𝕜] X) = μ • 1 - K m ∧
      ∀ n ≥ m, ‖twoGridOperator μ em (K m) (K n)‖ < 1 := by
  have hμpos : (0 : ℝ) < ‖μ‖ := norm_pos_iff.2 hμ
  obtain ⟨C, hC⟩ := IsCollectivelyCompact.exists_opNorm_le hK
  have hC0 : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hC 0)
  obtain ⟨A, hA⟩ : ∃ A : ℝ, ‖(e.symm : X →L[𝕜] X)‖ = A := ⟨_, rfl⟩
  have hA0 : (0 : ℝ) ≤ A := hA ▸ norm_nonneg _
  have hnum0 : (0 : ℝ) ≤ 1 + A * C := by linarith [mul_nonneg hA0 hC0]
  have hhalf : (0 : ℝ) < ‖μ‖ / 2 := by linarith
  obtain ⟨B, hB⟩ : ∃ B : ℝ, (1 + A * C) / (‖μ‖ / 2) = B := ⟨_, rfl⟩
  have hB0 : (0 : ℝ) ≤ B := hB ▸ div_nonneg hnum0 hhalf.le
  have hk0 : (0 : ℝ) ≤ 2 * ‖μ‖⁻¹ * B := mul_nonneg (by positivity) hB0
  obtain ⟨ε, hεpos, hε⟩ : ∃ ε : ℝ, 0 < ε ∧ 2 * ‖μ‖⁻¹ * B * ε < 1 := by
    refine ⟨1 / (2 * ‖μ‖⁻¹ * B + 1), div_pos one_pos (by linarith), ?_⟩
    rw [mul_one_div, div_lt_one (by linarith)]
    linarith
  have hq : Tendsto (fun n => ‖(L - K n) ∘L K n‖) atTop (𝓝 0) :=
    IsCollectivelyCompact.tendsto_opNorm_sub_comp hK hL
  obtain ⟨Nc, hNc⟩ := eventually_atTop.1 (hq.eventually (eventually_lt_nhds hεpos))
  have hansel : ∀ᶠ m in atTop, A * ‖(L - K m) ∘L K m‖ < ‖μ‖ / 2 := by
    have h0 : Tendsto (fun n => A * ‖(L - K n) ∘L K n‖) atTop (𝓝 0) := by
      simpa using hq.const_mul A
    exact h0.eventually (eventually_lt_nhds hhalf)
  filter_upwards [hansel, eventually_forall_opNorm_sub_comp_lt hK hL hεpos,
    eventually_ge_atTop Nc] with m hma hmb hmc
  obtain ⟨em, hem, hemnorm⟩ :=
    exists_equiv_of_isCompactOperator hμ (IsCollectivelyCompact.isCompactOperator hK m) he
      (by rw [hA]; linarith)
  have hemB : ‖(em.symm : X →L[𝕜] X)‖ ≤ B := by
    refine hemnorm.trans ?_
    rw [hA, ← hB]
    exact div_le_div₀ hnum0 (by linarith [mul_le_mul_of_nonneg_left (hC m) hA0]) hhalf
      (by linarith)
  refine ⟨em, hem, fun n hn => ?_⟩
  have hsplit : ‖((K n - K m) ∘L K n : X →L[𝕜] X)‖ ≤ 2 * ε := by
    have hid : ((K n - K m) ∘L K n : X →L[𝕜] X) = (K n - L) ∘L K n + (L - K m) ∘L K n := by
      ext x
      simp only [add_apply, ContinuousLinearMap.comp_apply, sub_apply]
      abel
    have hneg : ((K n - L) ∘L K n : X →L[𝕜] X) = -((L - K n) ∘L K n) := by
      ext x
      simp only [neg_apply, ContinuousLinearMap.comp_apply, sub_apply]
      abel
    have h1 : ‖((K n - L) ∘L K n : X →L[𝕜] X)‖ ≤ ε := by
      rw [hneg, norm_neg]
      exact (hNc n (le_trans hmc hn)).le
    have h2 : ‖((L - K m) ∘L K n : X →L[𝕜] X)‖ ≤ ε := (hmb n).le
    rw [hid]
    exact (norm_add_le _ _).trans (by linarith)
  calc ‖twoGridOperator μ em (K m) (K n)‖
      = ‖μ‖⁻¹ * ‖(em.symm : X →L[𝕜] X) ∘L ((K n - K m) ∘L K n)‖ := by
        rw [twoGridOperator, norm_smul, norm_inv]
    _ ≤ ‖μ‖⁻¹ * (‖(em.symm : X →L[𝕜] X)‖ * ‖((K n - K m) ∘L K n : X →L[𝕜] X)‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (by positivity)
    _ ≤ ‖μ‖⁻¹ * (B * (2 * ε)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hemB hsplit (norm_nonneg _) hB0) (by positivity)
    _ = 2 * ‖μ‖⁻¹ * B * ε := by ring
    _ < 1 := hε

end SecondKind
