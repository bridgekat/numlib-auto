/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Linear-plus-quadratic equations in a Banach space

This file proves Stewart's lemma on the equation $Lx + \varphi(x) = g$ in a Banach space $F$. Here
$L$ is an invertible bounded operator and $\varphi$ is a quadratic perturbation: $\varphi(0) = 0$
and $\|\varphi(x) - \varphi(y)\| \le \eta (\|x\| + \|y\|) \|x - y\|$, so that $\varphi$ is Lipschitz
on each ball with a constant proportional to the radius. If $\|L^{-1}\| \le 1/\delta$ and
$4 \|g\| \eta < \delta^2$, the equation has a solution of norm at most $2 \|g\| / \delta$. In finite
dimension it suffices that $L$ is bounded below, $\delta \|x\| \le \|Lx\|$.

The lemma is the fixed-point step of the perturbation theory of invariant and singular subspaces. In
Theorem 7.2.4 of [golub2013matrix], and in its analogue for singular subspaces, Theorem 8.6.5, the
unknown is the matrix $P$ that describes the perturbed subspace as a graph, $L$ is a Sylvester
operator whose inverse is bounded by $1 / \operatorname{sep}$, and $\varphi(P) = P E_{12} P$ is
quadratic. The statement and the proof follow G. W. Stewart, *Error and perturbation bounds for
subspaces associated with certain eigenvalue problems*, SIAM Rev. 15 (1973), Theorem 3.1.

## Main results

* `ContinuousLinearEquiv.exists_apply_add_eq_of_quadratic`: if $\|L^{-1}\| \le 1/\delta$,
  $\|g\| \le \gamma$ and $4 \gamma \eta < \delta^2$, then $Lx + \varphi(x) = g$ has a solution with
  $\|x\| \le 2\gamma/\delta$.
* `LinearMap.exists_apply_add_eq_of_quadratic_of_le_norm`: the same conclusion on a
  finite-dimensional space when $\delta \|x\| \le \|Lx\|$ for all $x$.

## Proof outline

The map $x \mapsto L^{-1}(g - \varphi(x))$ sends the closed ball of radius $2\gamma/\delta$ into
itself and is a contraction there with constant $4 \gamma \eta / \delta^2 < 1$. The ball is
complete, so the Banach fixed-point theorem (`ContractingWith.exists_fixedPoint'`) gives a fixed
point, which solves the equation.

## Implementation notes

* The results use nothing specific to numerical analysis. Their natural place in Mathlib is
  `Mathlib.Analysis.Normed.Operator` or `Mathlib.Topology.MetricSpace.Contracting`.
-/

open Metric Set

namespace ContinuousLinearEquiv

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace F]

/-- **Stewart's lemma on quadratic equations.** Let $F$ be a Banach space over a nontrivially normed
field, let $L : F \to F$ be an invertible bounded linear operator, and let $\delta > 0$ with
$\|L^{-1}\| \le 1/\delta$. Let $g \in F$ with $\|g\| \le \gamma$. Let $\varphi : F \to F$
satisfy $\varphi(0) = 0$ and $$\|\varphi(x) - \varphi(y)\| \le \eta (\|x\| + \|y\|) \|x - y\|
\qquad \text{for all } x, y \in F.$$ If $4 \gamma \eta < \delta^2$, then there is $x \in F$ with
$$Lx + \varphi(x) = g \qquad \text{and} \qquad \|x\| \le 2\gamma / \delta.$$

This is the lemma behind Theorem 7.2.4 of [golub2013matrix], and it is Theorem 3.1 of G. W.
Stewart (SIAM Rev. 15, 1973). The proof applies the Banach fixed-point theorem to
$x \mapsto L^{-1}(g - \varphi(x))$ on the closed ball of radius $2\gamma/\delta$. -/
theorem exists_apply_add_eq_of_quadratic (L : F ≃L[𝕜] F) {δ γ η : ℝ} (hδ : 0 < δ)
    (hL : ‖(L.symm : F →L[𝕜] F)‖ ≤ 1 / δ) {g : F} (hg : ‖g‖ ≤ γ) {φ : F → F} (hφ0 : φ 0 = 0)
    (hφ : ∀ x y, ‖φ x - φ y‖ ≤ η * (‖x‖ + ‖y‖) * ‖x - y‖) (h : 4 * γ * η < δ ^ 2) :
    ∃ x, L x + φ x = g ∧ ‖x‖ ≤ 2 * γ / δ := by
  -- Work with `η₊ = max η 0`, for which the Lipschitz hypothesis still holds.
  set η' := max η 0 with hη'
  have hφ' : ∀ x y, ‖φ x - φ y‖ ≤ η' * (‖x‖ + ‖y‖) * ‖x - y‖ := fun x y =>
    (hφ x y).trans (by gcongr; exact le_max_left _ _)
  have hγ : 0 ≤ γ := (norm_nonneg g).trans hg
  have h' : 4 * γ * η' < δ ^ 2 := by
    rcases le_total η 0 with hη | hη
    · rw [hη', max_eq_right hη, mul_zero]; positivity
    · rwa [hη', max_eq_left hη]
  set ρ := 2 * γ / δ with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  -- The contraction constant `κ = 4 γ η₊ / δ² < 1`.
  set κ := 4 * γ * η' / δ ^ 2 with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hκ1 : κ < 1 := by rw [hκ, div_lt_one (by positivity)]; exact h'
  have hηρ : η' * ρ ^ 2 ≤ γ := by
    have : η' * ρ ^ 2 = γ * κ := by rw [hρ, hκ]; field_simp; ring
    rw [this]; exact mul_le_of_le_one_right hγ hκ1.le
  set T : F → F := fun x => L.symm (g - φ x) with hT
  have hLs : ∀ v, ‖L.symm v‖ ≤ ‖v‖ / δ := fun v => by
    calc ‖L.symm v‖ = ‖(L.symm : F →L[𝕜] F) v‖ := rfl
      _ ≤ ‖(L.symm : F →L[𝕜] F)‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 / δ * ‖v‖ := by gcongr
      _ = ‖v‖ / δ := by ring
  have hmaps : MapsTo T (closedBall 0 ρ) (closedBall 0 ρ) := by
    intro x hx
    rw [mem_closedBall_zero_iff] at hx ⊢
    have hφx : ‖φ x‖ ≤ η' * ρ ^ 2 := by
      have := hφ' x 0
      rw [hφ0, sub_zero, norm_zero, add_zero, sub_zero] at this
      calc ‖φ x‖ ≤ η' * ‖x‖ * ‖x‖ := this
        _ ≤ η' * ρ * ρ := by gcongr
        _ = η' * ρ ^ 2 := by ring
    calc ‖T x‖ ≤ ‖g - φ x‖ / δ := hLs _
      _ ≤ (γ + γ) / δ := by
          gcongr
          exact (norm_sub_le _ _).trans (add_le_add hg (hφx.trans hηρ))
      _ = ρ := by rw [hρ]; ring
  have hcontr : ∀ x ∈ closedBall (0 : F) ρ, ∀ y ∈ closedBall (0 : F) ρ,
      dist (T x) (T y) ≤ κ * dist x y := by
    intro x hx y hy
    rw [mem_closedBall_zero_iff] at hx hy
    rw [dist_eq_norm, dist_eq_norm]
    have hsub : T x - T y = L.symm (φ y - φ x) := by
      simp only [hT, ← map_sub]; congr 1; abel
    rw [hsub]
    calc ‖L.symm (φ y - φ x)‖ ≤ ‖φ y - φ x‖ / δ := hLs _
      _ ≤ η' * (‖y‖ + ‖x‖) * ‖y - x‖ / δ := by gcongr; exact hφ' y x
      _ ≤ η' * (ρ + ρ) * ‖x - y‖ / δ := by rw [norm_sub_rev]; gcongr
      _ = κ * ‖x - y‖ := by rw [hκ, hρ]; field_simp; ring
  have hC : ContractingWith ⟨κ, hκ0⟩ (hmaps.restrict T _ _) := by
    refine ⟨show (⟨κ, hκ0⟩ : NNReal) < 1 from hκ1, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    exact hcontr x.1 x.2 y.1 y.2
  obtain ⟨x, hx, hfix, -⟩ := hC.exists_fixedPoint' isClosed_closedBall.isComplete hmaps
    (x := 0) (mem_closedBall_self hρ0) (edist_ne_top _ _)
  refine ⟨x, ?_, mem_closedBall_zero_iff.1 hx⟩
  have hx' : L.symm (g - φ x) = x := hfix
  calc L x + φ x = L (L.symm (g - φ x)) + φ x := by rw [hx']
    _ = g := by rw [L.apply_symm_apply]; abel

end ContinuousLinearEquiv

namespace LinearMap

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- **Stewart's lemma for an operator bounded below.** Let $F$ be a finite-dimensional normed space
over a complete nontrivially normed field, and let $L : F \to F$ be linear with
$\delta \|x\| \le \|Lx\|$ for all $x$, where $\delta > 0$. Let $\|g\| \le \gamma$, and let
$\varphi : F \to F$ satisfy $\varphi(0) = 0$ and $\|\varphi(x) - \varphi(y)\| \le \eta (\|x\| +
\|y\|) \|x - y\|$ for all $x, y$. If $4 \gamma \eta < \delta^2$, then there is $x$ with
$Lx + \varphi(x) = g$ and $\|x\| \le 2\gamma/\delta$.

The lower bound makes $L$ invertible with $\|L^{-1}\| \le 1/\delta$, and then
`ContinuousLinearEquiv.exists_apply_add_eq_of_quadratic` applies. The statement is for a general
normed space $F$ so that the operator norm is formed on $F$, and not on a type with a scoped
norm such as the Frobenius norm on matrices. -/
theorem exists_apply_add_eq_of_quadratic_of_le_norm (L : F →ₗ[𝕜] F) {δ γ η : ℝ} (hδ : 0 < δ)
    (hL : ∀ x, δ * ‖x‖ ≤ ‖L x‖) {g : F} (hg : ‖g‖ ≤ γ) {φ : F → F} (hφ0 : φ 0 = 0)
    (hφ : ∀ x y, ‖φ x - φ y‖ ≤ η * (‖x‖ + ‖y‖) * ‖x - y‖) (h : 4 * γ * η < δ ^ 2) :
    ∃ x, L x + φ x = g ∧ ‖x‖ ≤ 2 * γ / δ := by
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 := hL x
    rw [hx, norm_zero] at h1
    exact norm_eq_zero.1 (le_antisymm (nonpos_of_mul_nonpos_right h1 hδ) (norm_nonneg _))
  have : CompleteSpace F := FiniteDimensional.complete 𝕜 F
  set L₁ := LinearEquiv.ofBijective L ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
  set L' := L₁.toContinuousLinearEquiv
  have hLs : ‖(L'.symm : F →L[𝕜] F)‖ ≤ 1 / δ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
    have hy : L (L'.symm y) = y := L₁.apply_symm_apply y
    have h1 := hL (L'.symm y)
    rw [hy] at h1
    change ‖L'.symm y‖ ≤ 1 / δ * ‖y‖
    rw [one_div_mul_eq_div, le_div_iff₀ hδ, mul_comm]
    exact h1
  exact ContinuousLinearEquiv.exists_apply_add_eq_of_quadratic L' hδ hLs hg hφ0 hφ h

end LinearMap
