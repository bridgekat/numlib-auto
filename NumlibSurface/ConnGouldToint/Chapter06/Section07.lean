/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.SingularValues
import NumlibSurface.ConnGouldToint.Chapter06.Section01

/-!
# Conn, Gould and Toint, Section 6.7: Variable scaling

This module formalizes the scaling of variables in Section 6.7 of [conn2000trust]. Let $E$ be a real
inner product space and $S : E \to E$ an invertible linear map. In the scaled variables $w$, the
objective is $w \mapsto f(x + S w)$ (6.7.2). A Euclidean ball in the scaled variables corresponds to
the trust region $\{s : \|S^{-1} s\| \le \Delta\}$ in the original variables (6.7.8), whose norm
$\|s\|_S = \|S^{-1} s\|$ satisfies $\|s\|_S^2 = \langle s, S^{-T} S^{-1} s \rangle$ (6.7.9). If the
singular values of the scaling maps $S_k$ lie in $[1/\kappa, \kappa]$, the scaled norms satisfy the
uniform norm comparison of assumption AN.1 (Theorem 6.7.1).

## Main definitions

* Equation (6.7.2), `ConnGouldToint.Chapter06.scaledObjective`: the objective $w \mapsto f(x + S w)$
  in the scaled variables.
* Equation (6.7.9), `ConnGouldToint.Chapter06.scaledTrustNorm`: the scaled trust-region norm
  $\|s\|_S = \|S^{-1} s\|$.

## Main results

* Equations (6.7.8)–(6.7.9), `ConnGouldToint.Chapter06.scaledTrustRegion_eq_image`: the scaled trust
  region is the image of the Euclidean ball under $S$.
* Equation (6.7.9), `ConnGouldToint.Chapter06.scaledTrustNorm_sq`: the two formulas for $\|s\|_S^2$.
* Theorem 6.7.1, `ConnGouldToint.Chapter06.theorem_6_7_1`: uniform bounds on the singular values of
  the scaling maps give the norm comparisons of AN.1.

## Deviations from the source

* **Equations (6.7.8)–(6.7.9) and Theorem 6.7.1** (generalization). The coordinates are related by a
  linear equivalence of real inner product spaces. The singular-value bounds in the finite
  dimensional result become bounds on the norms of images of vectors under that equivalence.
-/

namespace ConnGouldToint.Chapter06

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Equation (6.7.2)** of [conn2000trust]. For $f : E \to \mathbb{R}$, a point $x \in E$ and an
invertible linear map $S : E \to E$, the **scaled objective** is the function
$$w \mapsto f(x + S w).$$

**Reading.** Linear equivalence between abstract real inner product spaces replaces scaling matrix.
-/
def scaledObjective (f : E → ℝ) (x : E) (S : E ≃ₗ[ℝ] E) (w : E) : ℝ :=
  f (x + S w)

/-- **Equation (6.7.9)** of [conn2000trust]. For an invertible linear map $S : E \to E$, the
**scaled trust-region norm** is $\|s\|_S = \|S^{-1} s\|$.

It is a seminorm on $E$, written as the Euclidean norm composed with $S^{-1}$.

**Reading.** Pulls the norm back through an equivalence of real inner product spaces.
-/
noncomputable def scaledTrustNorm (S : E ≃ₗ[ℝ] E) : Seminorm ℝ E :=
  (normSeminorm ℝ E).comp S.symm.toLinearMap

/-- **Equations (6.7.8)–(6.7.9)** of [conn2000trust]. For an invertible linear map $S : E \to E$ and
$\Delta \in \mathbb{R}$, the scaled trust region is the image of the closed Euclidean ball under
$S$:
$$\{s \in E : \|S^{-1} s\| \le \Delta\} = S\bigl(\{w \in E : \|w\| \le \Delta\}\bigr).$$

**Reading.** Ball-image identity for abstract real inner product spaces.
-/
theorem scaledTrustRegion_eq_image (S : E ≃ₗ[ℝ] E) (Δ : ℝ) :
    {s | scaledTrustNorm S s ≤ Δ} = S '' Metric.closedBall (0 : E) Δ := by
  ext s
  change ‖S.symm s‖ ≤ Δ ↔ _
  constructor
  · intro h
    exact ⟨S.symm s, by simpa [Metric.mem_closedBall, dist_zero_right] using h,
      S.apply_symm_apply s⟩
  · rintro ⟨w, hw, rfl⟩
    simpa only [LinearEquiv.symm_apply_apply, Metric.mem_closedBall, dist_zero_right] using hw

/-- **Equation (6.7.9)** of [conn2000trust]. Let $E$ be a real Hilbert space and $S : E \to E$ a
continuous linear map with continuous inverse. For every $s \in E$,
$$\|s\|_S^2 = \langle S^{-1} s, S^{-1} s \rangle = \langle s, (S^{-1})^* S^{-1} s \rangle,$$
where $(S^{-1})^*$ is the adjoint of $S^{-1}$.

**Reading.** Inner product and adjoint formula for an abstract equivalence.
-/
theorem scaledTrustNorm_sq [CompleteSpace E] (S : E ≃L[ℝ] E) (s : E) :
    scaledTrustNorm S.toLinearEquiv s ^ 2 = ⟪S.symm s, S.symm s⟫ ∧
      ⟪S.symm s, S.symm s⟫ =
        ⟪s, S.symm.toContinuousLinearMap.adjoint (S.symm s)⟫ := by
  refine ⟨(real_inner_self_eq_norm_sq (S.symm s)).symm, ?_⟩
  exact (S.symm.toContinuousLinearMap.adjoint_inner_right s (S.symm s)).symm

/-- **Theorem 6.7.1** of [conn2000trust]. Let $E$ be a finite-dimensional real inner product space
of dimension $n \ge 1$, let $S_k : E \to E$ be invertible linear maps, and let $\kappa \ge 1$.
Suppose that, for all $k$, the smallest singular value of $S_k$ is at least $1 / \kappa$ and the
largest is at most $\kappa$. Then for all $k$ and $v \in E$,
$$\frac{\|v\|}{\kappa} \le \|S_k^{-1} v\| \le \kappa \|v\|.$$

These are the two uniform norm comparisons of assumption AN.1 for the norms $\|\cdot\|_{S_k}$.
The singular values are `LinearMap.singularValues` in decreasing order, so the largest has index
$0$ and the smallest has index $n - 1$.

**Reading.** Operator bounds on equivalent finite-dimensional spaces serve as singular-value
endpoint bounds.
-/
theorem theorem_6_7_1 [FiniteDimensional ℝ E] [Nontrivial E]
    (S : ℕ → E ≃ₗ[ℝ] E) {κ : ℝ} (hκ : 1 ≤ κ)
    (hmin : ∀ k, 1 / κ ≤ (S k).toLinearMap.singularValues (Module.finrank ℝ E - 1))
    (hmax : ∀ k, (S k).toLinearMap.singularValues 0 ≤ κ) :
    ∀ k v, ‖v‖ / κ ≤ scaledTrustNorm (S k) v ∧ scaledTrustNorm (S k) v ≤ κ * ‖v‖ := by
  intro k v
  have hκ' : 0 < κ := zero_lt_one.trans_le hκ
  let T := (S k).toLinearMap
  let u := (S k).symm v
  have hTu : T u = v := (S k).apply_symm_apply v
  change ‖v‖ / κ ≤ ‖u‖ ∧ ‖u‖ ≤ κ * ‖v‖
  constructor
  · apply (div_le_iff₀ hκ').mpr
    calc
      ‖v‖ = ‖T u‖ := by rw [hTu]
      _ ≤ T.singularValues 0 * ‖u‖ := T.norm_apply_le_singularValues_zero_mul u
      _ ≤ κ * ‖u‖ := mul_le_mul_of_nonneg_right (hmax k) (norm_nonneg u)
      _ = ‖u‖ * κ := mul_comm _ _
  · let n := Module.finrank ℝ E
    have hn : 0 < n := Module.finrank_pos
    obtain ⟨V, hV, hlow⟩ := (T.isGreatest_singularValues (k := n - 1) (by omega)).1
    have htop : V = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hV]; omega)
    have h := (mul_le_mul_of_nonneg_right (hmin k) (show 0 ≤ ‖u‖ from norm_nonneg u)).trans
      (hlow u (htop ▸ Submodule.mem_top))
    rw [hTu, one_div, ← div_eq_inv_mul] at h
    exact (div_le_iff₀ hκ').mp h |>.trans_eq (mul_comm _ _)

end ConnGouldToint.Chapter06
