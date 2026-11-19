/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Variational.Galerkin
import NumlibSurface.AtkinsonHan.Chapter09.Section01

/-!
# Atkinson and Han, Section 9.3: The generalized Galerkin method

This module formalizes Section 9.3 of [han2009theoretical]. In the generalized Galerkin method the
discrete space $V_N$ need not be a subspace of $V$, and the form $a$ and the functional $\ell$ are
replaced by approximations $a_N$ and $\ell_N$. The problem (9.3.1) asks for $u_N \in V_N$ with
$a_N(u_N, v_N) = \ell_N(v_N)$ for all $v_N \in V_N$. Strang's first lemma (Theorem 9.3.1) bounds the
error by an approximation term and a consistency term: $$\|u - u_N\|_N \le \Big(1 +
\frac{M}{\alpha_0}\Big) \inf_{w_N \in V_N} \|u - w_N\|_N + \frac{1}{\alpha_0} \sup_{0 \ne v_N \in
V_N} \frac{|a_N(u, v_N) - \ell_N(v_N)|}{\|v_N\|_N}.$$ Exercise 9.3.1 recovers an inequality of Céa
type in the conforming case. The proofs specialize `IsGeneralizedGalerkinSolution` of
`Numlib.Variational.Galerkin`.

## Main definitions

* Equation (9.3.1), `AtkinsonHan.GeneralizedGalerkinProblem`: $u_N \in V_N$ and
  $a_N(u_N, v_N) = \ell_N(v_N)$ for all $v_N \in V_N$.
* Equation (9.3.2), `AtkinsonHan.Chapter09.consistencyError`: the consistency term $\sup_{0 \ne v_N
  \in V_N} |a_N(u, v_N) - \ell_N(v_N)| / \|v_N\|$.

## Main results

* Theorem 9.3.1, `AtkinsonHan.Chapter09.theorem_9_3_1_existsUnique`: the problem (9.3.1) has a
  unique solution.
* Theorem 9.3.1, `AtkinsonHan.Chapter09.theorem_9_3_1`: the error bound (9.3.2) on an abstract
  normed space $W$.
* Theorem 9.3.1, `AtkinsonHan.Chapter09.theorem_9_3_1'`: the error bound (9.3.2) with the data of
  the source.
* Exercise 9.3.1, `AtkinsonHan.Chapter09.exercise_9_3_1`: in the conforming case,
  $\|u - u_N\| \le (1 + M / c_0) \|u - v\|$ for $v \in V_N$.

## Implementation notes

* The source carries out the analysis on $V + V_N$ with a norm $\|\cdot\|_N$ that depends on the
  discretization. The theorem is for one $N$ at a time, so this space is an abstract real normed
  space $W$, as in the backbone. The forms $a_N$ and $\ell_N$ are linear maps on $W$, with
  boundedness and coercivity assumed only on $V_N$.
* The source states Theorem 9.3.1 with $V$ a Hilbert space, the solution $u \in V$ of (9.1.1) and an
  injection of $V$ into $W$. The proof uses none of these data.
  `AtkinsonHan.Chapter09.theorem_9_3_1` is the estimate for an arbitrary $u \in W$, and
  `AtkinsonHan.Chapter09.theorem_9_3_1'` keeps the unused hypotheses of the source.
* The supremum in the consistency term is `iSup` on $\mathbb{R}$, which is $0$ on an empty or
  unbounded set.

## Deviations from the source

* **Theorem 9.3.1** (scope). The abstract estimate allows any comparison point in
  the ambient normed space. The version with an injected exact solution keeps the
  source's continuous problem. Both statements use boundedness of the consistency
  quotient only where needed.
-/

open Filter Topology
open scoped InnerProductSpace

namespace AtkinsonHan

/-- **Equation (9.3.1)** of [han2009theoretical]. Let $W$ be a real normed space, which plays the
role of $V + V_N$ with the norm $\|\cdot\|_N$. Let $a_N$ be a bilinear form on $W$, $\ell_N$ a
linear functional on $W$, and $V_N \subseteq W$ a subspace. An element $u_N \in W$ **solves the
generalized Galerkin problem** if $u_N \in V_N$ and $$a_N(u_N, v_N) = \ell_N(v_N) \quad
\text{for all } v_N \in V_N.$$

It is `IsGeneralizedGalerkinSolution` of the backbone. -/
abbrev GeneralizedGalerkinProblem {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (aN : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (ℓN : W →ₗ[ℝ] ℝ) (VN : Submodule ℝ W) (uN : W) : Prop :=
  IsGeneralizedGalerkinSolution aN ℓN VN uN

namespace Chapter09

section Strang

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
variable {aN : W →ₗ[ℝ] W →ₗ[ℝ] ℝ} {ℓN : W →ₗ[ℝ] ℝ} {VN : Submodule ℝ W} {M α₀ c₀ : ℝ}

/-- The consistency term of (9.3.2). For $u \in W$, it is $$\sup_{0 \ne v_N \in V_N} \frac{|a_N(u,
v_N) - \ell_N(v_N)|}{\|v_N\|}.$$

The supremum is `iSup` on $\mathbb{R}$: it is $0$ when $V_N = \{0\}$ or when the quotients are
unbounded above. -/
noncomputable def consistencyError (aN : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (ℓN : W →ₗ[ℝ] ℝ)
    (VN : Submodule ℝ W) (u : W) : ℝ :=
  ⨆ v : {v : VN // v ≠ 0},
    |aN u ((v : VN) : W) - ℓN ((v : VN) : W)| / ‖((v : VN) : W)‖

/-- The consistency term is nonnegative. -/
theorem consistencyError_nonneg (aN : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (ℓN : W →ₗ[ℝ] ℝ)
    (VN : Submodule ℝ W) (u : W) : 0 ≤ consistencyError aN ℓN VN u :=
  Real.iSup_nonneg fun _ => by positivity

private theorem bddAbove_consistency (hM : ∀ w, ∀ v ∈ VN, |aN w v| ≤ M * ‖w‖ * ‖v‖)
    (hℓ : ∀ v ∈ VN, |ℓN v| ≤ c₀ * ‖v‖) (u : W) :
    BddAbove (Set.range fun v : {v : VN // v ≠ 0} =>
      |aN u ((v : VN) : W) - ℓN ((v : VN) : W)| / ‖((v : VN) : W)‖) := by
  refine ⟨M * ‖u‖ + c₀, Set.forall_mem_range.2 fun v => ?_⟩
  have hv : ((v : VN) : W) ≠ 0 := fun h => v.2 (Subtype.ext h)
  have hvpos : (0 : ℝ) < ‖((v : VN) : W)‖ := norm_pos_iff.mpr hv
  rw [div_le_iff₀ hvpos]
  have h1 := hM u ((v : VN) : W) (v : VN).2
  have h2 := hℓ ((v : VN) : W) (v : VN).2
  calc |aN u ((v : VN) : W) - ℓN ((v : VN) : W)|
      ≤ |aN u ((v : VN) : W)| + |ℓN ((v : VN) : W)| := abs_sub _ _
    _ ≤ M * ‖u‖ * ‖((v : VN) : W)‖ + c₀ * ‖((v : VN) : W)‖ := by gcongr
    _ = (M * ‖u‖ + c₀) * ‖((v : VN) : W)‖ := by ring

/-- Let $|a_N(w, v)| \le M \|w\| \|v\|$ for $w \in W$ and $v \in V_N$, and let
$|\ell_N(v)| \le c_0 \|v\|$ for $v \in V_N$. Then for every $u \in W$ and $w \in V_N$, $$|a_N(u,
w) - \ell_N(w)| \le E(u) \, \|w\|,$$ where $E(u)$ is the consistency term
`AtkinsonHan.Chapter09.consistencyError`. -/
theorem le_consistencyError (hM : ∀ w, ∀ v ∈ VN, |aN w v| ≤ M * ‖w‖ * ‖v‖)
    (hℓ : ∀ v ∈ VN, |ℓN v| ≤ c₀ * ‖v‖) (u : W) {w : W} (hw : w ∈ VN) :
    ‖aN u w - ℓN w‖ ≤ consistencyError aN ℓN VN u * ‖w‖ := by
  rcases eq_or_ne w 0 with rfl | hw0
  · simp
  · rw [Real.norm_eq_abs, ← div_le_iff₀ (norm_pos_iff.mpr hw0)]
    exact le_ciSup (bddAbove_consistency hM hℓ u)
      (⟨⟨w, hw⟩, fun h => hw0 (congrArg Subtype.val h)⟩ : {v : VN // v ≠ 0})

/-- **Theorem 9.3.1** of [han2009theoretical] (Strang's first lemma), existence and uniqueness. Let
$V_N \subseteq W$ be finite-dimensional, and let $a_N(v, v) \ge \alpha_0 \|v\|^2$ for all
$v \in V_N$, with $\alpha_0 > 0$. Then the problem (9.3.1) has exactly one solution $u_N$.

The proof uses neither the boundedness of $a_N$ nor the bound on $\ell_N$.

**Reading.** Only finite dimension and coercivity are needed to solve the discrete equation.
-/
theorem theorem_9_3_1_existsUnique (aN : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (ℓN : W →ₗ[ℝ] ℝ)
    (VN : Submodule ℝ W) [FiniteDimensional ℝ VN] (hα₀ : 0 < α₀)
    (hcoer : ∀ v ∈ VN, α₀ * ‖v‖ ^ 2 ≤ aN v v) : ∃! uN, GeneralizedGalerkinProblem aN ℓN VN uN :=
  existsUnique_isGeneralizedGalerkinSolution aN ℓN VN hα₀ hcoer

/-- **Theorem 9.3.1** of [han2009theoretical] (Strang's first lemma), the error bound (9.3.2). Let
$W$ be a real normed space, let $V_N \subseteq W$ be finite-dimensional, let $M \ge 0$ and
$\alpha_0 > 0$, and let $a_N$ and $\ell_N$ satisfy, for all $w \in W$ and $v \in V_N$, $$|a_N(w,
v)| \le M \|w\| \|v\|, \qquad a_N(v, v) \ge \alpha_0 \|v\|^2, \qquad |\ell_N(v)| \le c_0
\|v\|.$$ Let $u_N$ solve the problem (9.3.1). Then for every $u \in W$, $$\|u - u_N\| \le
\Big(1 + \frac{M}{\alpha_0}\Big) \inf_{w_N \in V_N} \|u - w_N\| + \frac{1}{\alpha_0} \sup_{0 \ne
v_N \in V_N} \frac{|a_N(u, v_N) - \ell_N(v_N)|}{\|v_N\|}.$$

The first term is an approximation term of Céa type, and the second is the consistency term
`AtkinsonHan.Chapter09.consistencyError`. The unique solvability of (9.3.1) is
`AtkinsonHan.Chapter09.theorem_9_3_1_existsUnique`.

**Reading.** Same two error terms for any ambient comparison point.
-/
theorem theorem_9_3_1 (aN : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (ℓN : W →ₗ[ℝ] ℝ) (VN : Submodule ℝ W)
    [FiniteDimensional ℝ VN] (hM0 : 0 ≤ M) (hα₀ : 0 < α₀)
    (hM : ∀ w, ∀ v ∈ VN, |aN w v| ≤ M * ‖w‖ * ‖v‖)
    (hcoer : ∀ v ∈ VN, α₀ * ‖v‖ ^ 2 ≤ aN v v) (hℓ : ∀ v ∈ VN, |ℓN v| ≤ c₀ * ‖v‖) (u : W)
    {uN : W} (huN : GeneralizedGalerkinProblem aN ℓN VN uN) :
    ‖u - uN‖ ≤ (1 + M / α₀) * (⨅ w : VN, ‖u - (w : W)‖)
      + 1 / α₀ * consistencyError aN ℓN VN u := by
  have hC : 0 < 1 + M / α₀ := by
    have : 0 ≤ M / α₀ := div_nonneg hM0 hα₀.le
    linarith
  set δ := consistencyError aN ℓN VN u with hδdef
  have hδ0 : 0 ≤ δ := consistencyError_nonneg aN ℓN VN u
  have hpt : ∀ w : VN, ‖u - uN‖ - δ / α₀ ≤ (1 + M / α₀) * ‖u - (w : W)‖ := by
    intro w
    have := strang_first (𝕜 := ℝ) hα₀ hM0 hM hcoer huN u hδ0
      (fun z hz => le_consistencyError hM hℓ u hz) w.2
    linarith
  have hkey : ∀ w : VN, (‖u - uN‖ - δ / α₀) / (1 + M / α₀) ≤ ‖u - (w : W)‖ := by
    intro w
    rw [div_le_iff₀ hC, mul_comm]
    exact hpt w
  have hle := le_ciInf hkey
  rw [div_le_iff₀ hC] at hle
  have hδα : 1 / α₀ * δ = δ / α₀ := by ring
  rw [hδα]
  linarith [hle]

set_option linter.unusedVariables false in
/-- **Theorem 9.3.1** of [han2009theoretical] (Strang's first lemma), with the data of the source.
Let $V$ be a real Hilbert space, let $a$ be a bilinear form on $V$, let $\ell \in V'$, and let
$u \in V$ satisfy $a(u, v) = \ell(v)$ for all $v \in V$. Let $\iota : V \to W$ be an injective
linear map into a real normed space $W$, which plays the role of $V + V_N$ with the norm
$\|\cdot\|_N$. Under the hypotheses of `AtkinsonHan.Chapter09.theorem_9_3_1` on $V_N$, $a_N$ and
$\ell_N$, the error bound (9.3.2) holds for $\iota u$: $$\|\iota u - u_N\| \le \Big(1 +
\frac{M}{\alpha_0}\Big) \inf_{w_N \in V_N} \|\iota u - w_N\| + \frac{1}{\alpha_0} \sup_{0 \ne
v_N \in V_N} \frac{|a_N(\iota u, v_N) - \ell_N(v_N)|}{\|v_N\|}.$$

The proof does not use $V$, $a$, $\ell$, the equation for $u$, or the injectivity of $\iota$:
the estimate is a statement about $W$ alone. These hypotheses are kept as the source states
them. -/
theorem theorem_9_3_1' {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (a : BilinForm V) (ℓ : StrongDual ℝ V) {u : V} (hu : ∀ v, a u v = ℓ v)
    (ι : V →ₗ[ℝ] W) (hι : Function.Injective ι) (aN : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (ℓN : W →ₗ[ℝ] ℝ)
    (VN : Submodule ℝ W) [FiniteDimensional ℝ VN] (hM0 : 0 ≤ M) (hα₀ : 0 < α₀)
    (hM : ∀ w, ∀ v ∈ VN, |aN w v| ≤ M * ‖w‖ * ‖v‖)
    (hcoer : ∀ v ∈ VN, α₀ * ‖v‖ ^ 2 ≤ aN v v) (hℓ : ∀ v ∈ VN, |ℓN v| ≤ c₀ * ‖v‖) {uN : W}
    (huN : GeneralizedGalerkinProblem aN ℓN VN uN) :
    ‖ι u - uN‖ ≤ (1 + M / α₀) * (⨅ w : VN, ‖ι u - (w : W)‖)
      + 1 / α₀ * consistencyError aN ℓN VN (ι u) :=
  theorem_9_3_1 aN ℓN VN hM0 hα₀ hM hcoer hℓ (ι u) huN

end Strang

/-- **Exercise 9.3.1** of [han2009theoretical]. Let $V$ be a real inner product space, let $a$ be a
bilinear form on $V$ that is bounded with constant $M \ge 0$ and $V$-elliptic with constant
$c_0 > 0$, and let $\ell \in V'$. Let $u \in V$ satisfy $a(u, v) = \ell(v)$ for all $v \in V$,
and let $u_N$ solve the Galerkin problem (9.1.4) on a subspace $V_N \subseteq V$. Then $$\|u -
u_N\| \le \Big(1 + \frac{M}{c_0}\Big) \|u - v\| \quad \text{for every } v \in V_N.$$

This is the conforming case $V_N \subseteq V$, $a_N = a$, $\ell_N = \ell$ of Theorem 9.3.1. The
consistency term of (9.3.2) is $0$, and the estimate has the form of (9.1.11). -/
theorem exercise_9_3_1 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (a : BilinForm V)
    (ℓ : StrongDual ℝ V) (VN : Submodule ℝ V) {M c₀ : ℝ} (hM0 : 0 ≤ M) (hc₀ : 0 < c₀)
    (hM : a.IsBoundedWith M) (ha : a.IsEllipticWith c₀) {u uN : V} (hu : ∀ v, a u v = ℓ v)
    (huN : GalerkinProblem a ℓ VN uN) {v : V} (hv : v ∈ VN) :
    ‖u - uN‖ ≤ (1 + M / c₀) * ‖u - v‖ := by
  have hres : ∀ w ∈ VN, ‖a u w - (ℓ : V →ₗ[ℝ] ℝ) w‖ ≤ (0 : ℝ) * ‖w‖ := by
    intro w _
    simp [hu w]
  have h := strang_first (𝕜 := ℝ) (aN := a) (ℓN := (ℓ : V →ₗ[ℝ] ℝ)) (K := VN) hc₀ hM0
    (fun w v _ => hM w v) (fun v _ => ha v) huN u le_rfl hres hv
  simpa using h

end Chapter09

end AtkinsonHan
