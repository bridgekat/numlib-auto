/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Optimality.Clarke
import Numlib.Optimization.ModelBased.ProjectedPath
import Numlib.Analysis.Calculus.Taylor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Conn, Gould and Toint, Section 3.1: Basic real analysis

This module formalizes the mean-value and Taylor theorems of Section 3.1 of [conn2000trust]. Let $f$
be continuously differentiable on an open set $S$ that contains the segment $[x, x + s]$. Then
$f(x + s) - f(x)$ is the derivative at an intermediate point applied to $s$ (Theorem 3.1.1), or the
integral of the derivative along the segment (Theorem 3.1.3). Lipschitz bounds on the derivative or
on the Hessian give the remainder estimates
$$|f(x + s) - f(x) - \langle g(x), s \rangle| \le \tfrac{1}{2} \gamma \|s\|^2, \qquad |f(x + s) -
  m^Q(x + s)| \le \tfrac{1}{6} \gamma \|s\|^3$$
of Theorems 3.1.4 and 3.1.5, where $m^Q$ is the second-order Taylor model. The module also proves
the support identity (3.1.4) for the Clarke directional derivative and Moreau's decomposition
(3.1.7) of a vector into its tangent and normal components.

The proofs use the backbone modules `Numlib.Analysis.Calculus.Taylor`,
`Numlib.Optimization.Optimality.Clarke` and `Numlib.Optimization.ModelBased.ProjectedPath`.

## Main results

* Theorem 3.1.1, `ConnGouldToint.Chapter03.theorem_3_1_1`: the mean-value theorem along a segment.
* Theorem 3.1.2, `ConnGouldToint.Chapter03.theorem_3_1_2`: Taylor's theorem with the second-order
  Lagrange remainder.
* Theorem 3.1.3, `ConnGouldToint.Chapter03.theorem_3_1_3`: the integral mean-value theorem for a
  vector-valued function.
* Theorem 3.1.4, `ConnGouldToint.Chapter03.theorem_3_1_4`: a Lipschitz derivative gives a quadratic
  remainder for the first-order Taylor model.
* Theorem 3.1.5, `ConnGouldToint.Chapter03.theorem_3_1_5`: a Lipschitz Hessian gives a cubic
  remainder for the second-order Taylor model.
* Theorem 3.1.6, `ConnGouldToint.Chapter03.theorem_3_1_6`: a Lipschitz Jacobian gives a quadratic
  remainder for a vector-valued function.
* Equation (3.1.4), `ConnGouldToint.Chapter03.clarkeDerivative_isGreatest`: the Clarke directional
  derivative is the maximum of $\langle g, d \rangle$ over the Clarke subgradients $g$.
* Equation (3.1.7), `ConnGouldToint.Chapter03.moreau_normal_tangent`: Moreau's decomposition of a
  vector into orthogonal tangent and normal components.

## Conventions

* The gradient pairing $\langle g(x), s \rangle$ and the Jacobian action $J(x) s$ are both
  `fderiv ℝ f x s`, the derivative applied to the step. The Hessian form $\langle s, H(x) s \rangle$
  is `fderiv ℝ (fderiv ℝ f) x s s`.
* The norm of the derivative is the operator norm of `E →L[ℝ] F`. For a real-valued $f$ this is the
  dual norm of the norm on steps.

## Implementation notes

* The theorems hold in any real normed space $E$; the integral form needs a complete codomain. The
  segment is the condition $x + ts \in S$ for all $t \in [0, 1]$.
* The Lipschitz conditions of Theorems 3.1.4–3.1.6 compare the derivative at each point $z \in S$
  with the derivative at the expansion point $x$ only.

## Deviations from the source

* **Generalization.** The segment Taylor formulas and bounds apply to real normed spaces using
  Fréchet derivatives. See `ConnGouldToint.Chapter03.theorem_3_1_1`,
  `ConnGouldToint.Chapter03.theorem_3_1_2`, `ConnGouldToint.Chapter03.theorem_3_1_4`,
  `ConnGouldToint.Chapter03.theorem_3_1_5`, `ConnGouldToint.Chapter03.theorem_3_1_6`.
* **Generalization.** Theorem 3.1.3 extends the integral mean-value formula to complete normed
  codomains. See `ConnGouldToint.Chapter03.theorem_3_1_3`.
* **Scope.** Equation (3.1.7) gives the decomposition in the project's general direction-cone
  formulation. See `ConnGouldToint.Chapter03.moreau_normal_tangent`.
-/

open Set Filter Topology

namespace ConnGouldToint.Chapter03

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Theorem 3.1.1** of [conn2000trust]. Let $E$ be a real normed space, let $S \subseteq E$ be
open, and let $f : E \to \mathbb{R}$ be continuously differentiable on $S$. Let $x, s \in E$
with $x + ts \in S$ for all $t \in [0, 1]$. Then there is $t \in [0, 1]$ with
$$f(x + s) = f(x) + \langle g(x + ts), s \rangle.$$

**Generalization.** The segment Taylor formulas and remainder estimates use Fréchet derivatives on
real normed spaces. Each Lipschitz estimate compares the derivative at the base to its value
throughout the displayed set.
-/
theorem theorem_3_1_1 {S : Set E} (hS : IsOpen S) {f : E → ℝ} (hf : ContDiffOn ℝ 1 f S)
    {x s : E} (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • s ∈ S) :
    ∃ t ∈ Icc (0 : ℝ) 1, f (x + s) = f x + fderiv ℝ f (x + t • s) s := by
  have hd : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun u : ℝ => f (x + u • s)) (fderiv ℝ f (x + t • s) s) t :=
    fun t ht => DifferentiableAt.hasDerivAt_comp_add_smul
      ((hf.contDiffAt (hS.mem_nhds (hseg t ht))).differentiableAt (by norm_num))
  obtain ⟨t, ht, he⟩ := exists_deriv_eq_slope
    (fun u : ℝ => f (x + u • s)) (by norm_num : (0 : ℝ) < 1)
    (fun u hu => (hd u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hd u (Ioo_subset_Icc_self hu)).differentiableAt.differentiableWithinAt)
  refine ⟨t, Ioo_subset_Icc_self ht, ?_⟩
  rw [(hd t (Ioo_subset_Icc_self ht)).deriv] at he
  simp only [one_smul, zero_smul, add_zero, sub_zero, div_one] at he
  linarith

/-- **Theorem 3.1.2** of [conn2000trust]. Let $E$ be a real normed space, let $S \subseteq E$ be
open, and let $f : E \to \mathbb{R}$ be twice continuously differentiable on $S$. Let
$x, s \in E$ with $x + ts \in S$ for all $t \in [0, 1]$. Then there is $t \in [0, 1]$ with
$$f(x + s) = f(x) + \langle g(x), s \rangle + \tfrac{1}{2} \langle s, H(x + ts) s \rangle.$$

**Generalization.** The segment Taylor formulas and remainder estimates use Fréchet derivatives on
real normed spaces. Each Lipschitz estimate compares the derivative at the base to its value
throughout the displayed set.
-/
theorem theorem_3_1_2 {S : Set E} (hS : IsOpen S) {f : E → ℝ} (hf : ContDiffOn ℝ 2 f S)
    {x s : E} (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • s ∈ S) :
    ∃ t ∈ Icc (0 : ℝ) 1, f (x + s) = f x + fderiv ℝ f x s +
      (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) (x + t • s) s s := by
  let g : ℝ → ℝ := fun t => f (x + t • s)
  let U : Set ℝ := (fun t : ℝ => x + t • s) ⁻¹' S
  have hU : IsOpen U := hS.preimage (by fun_prop)
  have hsub : Icc (0 : ℝ) 1 ⊆ U := hseg
  have hg : ContDiffOn ℝ 2 g U := hf.comp (by fun_prop) (fun _ h => h)
  have hd : ∀ t ∈ U, deriv g t = fderiv ℝ f (x + t • s) s :=
    fun t ht => (DifferentiableAt.hasDerivAt_comp_add_smul
      ((hf.contDiffAt (hS.mem_nhds ht)).differentiableAt (by norm_num))).deriv
  have hdd : ∀ t ∈ U, iteratedDeriv 2 g t = fderiv ℝ (fderiv ℝ f) (x + t • s) s s := by
    intro t ht
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    have he : deriv g =ᶠ[nhds t] fun u : ℝ => fderiv ℝ f (x + u • s) s :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨U, hU.mem_nhds ht, hd⟩
    rw [he.deriv_eq]
    have hF : ContDiffOn ℝ 1 (fderiv ℝ f) S := hf.fderiv_of_isOpen hS (by norm_num)
    have h := (DifferentiableAt.hasDerivAt_comp_add_smul
      ((hF.contDiffAt (hS.mem_nhds ht)).differentiableAt (by norm_num))).clm_apply
        (hasDerivAt_const t s)
    simpa using h.deriv
  have hne : (0 : ℝ) ≠ 1 := zero_ne_one
  have hsub' : uIcc (0 : ℝ) 1 ⊆ U := by simpa [uIcc_of_le zero_le_one] using hsub
  obtain ⟨t, ht, he⟩ := exists_taylorWithinEval_add_iteratedDeriv_mul
    (f := g) (n := 1) hne (by exact hg.mono hsub')
  have ht' : t ∈ Icc (0 : ℝ) 1 := by
    exact Ioo_subset_Icc_self (by simpa only [uIoo_of_le zero_le_one] using ht)
  rw [taylorWithinEval_eq_sum_of_contDiffAt hne
    ((hg.contDiffAt (hU.mem_nhds (hsub (left_mem_Icc.2 zero_le_one)))).of_le (by norm_num)),
    hdd t (hsub ht')] at he
  refine ⟨t, ht', ?_⟩
  have hd0 := hd 0 (hsub (left_mem_Icc.2 zero_le_one))
  norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one] at he
  rw [hd0] at he
  simp only [g, zero_smul, one_smul, add_zero] at he
  linarith

/-- **Theorem 3.1.3** of [conn2000trust] (integral mean-value theorem). Let $E$ be a real normed
space and $F$ a real Banach space, let $S \subseteq E$ be open, and let $f : E \to F$ be
continuously differentiable on $S$. Let $x, s \in E$ with $x + ts \in S$ for all $t \in [0, 1]$.
Then
$$f(x + s) = f(x) + \int_0^1 J(x + ts) s \, dt.$$

The completeness of $F$ is needed for the Bochner integral `intervalIntegral`.

**Generalization.** The integral mean-value formula takes values in a complete real normed space,
using the Bochner integral of the derivative applied along the segment.
-/
theorem theorem_3_1_3 [CompleteSpace F] {S : Set E} (hS : IsOpen S) {f : E → F}
    (hf : ContDiffOn ℝ 1 f S) {x s : E}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • s ∈ S) :
    f (x + s) = f x + ∫ t in (0 : ℝ)..1, fderiv ℝ f (x + t • s) s := by
  have hd : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun u : ℝ => f (x + u • s)) (fderiv ℝ f (x + t • s) s) t :=
    fun t ht => DifferentiableAt.hasDerivAt_comp_add_smul
      ((hf.contDiffAt (hS.mem_nhds (hseg t ht))).differentiableAt (by norm_num))
  have hc : ContinuousOn (fderiv ℝ f) S :=
    hf.continuousOn_fderiv_of_isOpen hS (by norm_num)
  have hi : IntervalIntegrable (fun t : ℝ => fderiv ℝ f (x + t • s) s) MeasureTheory.volume 0 1 :=
    ContinuousOn.intervalIntegrable (by
      rw [uIcc_of_le zero_le_one]
      exact (hc.comp (by fun_prop) hseg).clm_apply continuousOn_const)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u : ℝ => f (x + u • s)) (by rwa [uIcc_of_le zero_le_one]) hi
  rw [he]
  simp [add_comm (f x)]

/-- **Theorem 3.1.4** of [conn2000trust]. Let $E$ be a real normed space, let $S \subseteq E$ be
open, and let $f : E \to \mathbb{R}$ be continuously differentiable on $S$. Let $x, s \in E$
with $x + ts \in S$ for all $t \in [0, 1]$, and let $\gamma \in \mathbb{R}$ satisfy
$\|g(z) - g(x)\| \le \gamma \|z - x\|$ for all $z \in S$. Then
$$|f(x + s) - f(x) - \langle g(x), s \rangle| \le \tfrac{1}{2} \gamma \|s\|^2.$$

The norm of $g(z) - g(x)$ is the dual norm of the norm on $E$, that is, the operator norm of
`fderiv ℝ f z - fderiv ℝ f x`.

**Generalization.** The segment Taylor formulas and remainder estimates use Fréchet derivatives on
real normed spaces. Each Lipschitz estimate compares the derivative at the base to its value
throughout the displayed set.
-/
theorem theorem_3_1_4 {S : Set E} (hS : IsOpen S) {f : E → ℝ}
    (hf : ContDiffOn ℝ 1 f S) {x s : E} {γ : ℝ}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • s ∈ S)
    (hlip : ∀ z ∈ S, ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ γ * ‖z - x‖) :
    |f (x + s) - (f x + fderiv ℝ f x s)| ≤ (1 / 2 : ℝ) * γ * ‖s‖ ^ 2 := by
  simpa only [Real.norm_eq_abs] using norm_sub_firstOrder_le_of_lipschitzAt_segment hS hf hseg hlip

/-- **Theorem 3.1.5** of [conn2000trust]. Let $E$ be a real normed space, let $S \subseteq E$ be
open, and let $f : E \to \mathbb{R}$ be twice continuously differentiable on $S$. Let
$x, s \in E$ with $x + ts \in S$ for all $t \in [0, 1]$, and let $\gamma \in \mathbb{R}$ satisfy
$\|H(z) - H(x)\| \le \gamma \|z - x\|$ for all $z \in S$. Then
$$\left| f(x + s) - f(x) - \langle g(x), s \rangle - \tfrac{1}{2} \langle s, H(x) s \rangle
  \right| \le \tfrac{1}{6} \gamma \|s\|^3.$$

The norm of $H(z) - H(x)$ is the operator norm of the second derivative `fderiv ℝ (fderiv ℝ f)`.

**Generalization.** The segment Taylor formulas and remainder estimates use Fréchet derivatives on
real normed spaces. Each Lipschitz estimate compares the derivative at the base to its value
throughout the displayed set.
-/
theorem theorem_3_1_5 {S : Set E} (hS : IsOpen S) {f : E → ℝ}
    (hf : ContDiffOn ℝ 2 f S) {x s : E} {γ : ℝ}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • s ∈ S)
    (hlip : ∀ z ∈ S, ‖fderiv ℝ (fderiv ℝ f) z - fderiv ℝ (fderiv ℝ f) x‖ ≤ γ * ‖z - x‖) :
    |f (x + s) - (f x + fderiv ℝ f x s + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) x s s)| ≤
      (1 / 6 : ℝ) * γ * ‖s‖ ^ 3 :=
  abs_sub_secondOrder_le_of_lipschitzAt_segment hS hf hseg hlip

/-- **Theorem 3.1.6** of [conn2000trust]. Let $E$ and $F$ be real normed spaces, let $S \subseteq E$
be open, and let $f : E \to F$ be continuously differentiable on $S$ with Jacobian $J$. Let
$x, s \in E$ with $x + ts \in S$ for all $t \in [0, 1]$, and let $\gamma \in \mathbb{R}$ satisfy
$\|J(z) - J(x)\| \le \gamma \|z - x\|$ for all $z \in S$. Then
$$\|f(x + s) - f(x) - J(x) s\| \le \tfrac{1}{2} \gamma \|s\|^2.$$

**Generalization.** The segment Taylor formulas and remainder estimates use Fréchet derivatives on
real normed spaces. Each Lipschitz estimate compares the derivative at the base to its value
throughout the displayed set.
-/
theorem theorem_3_1_6 {S : Set E} (hS : IsOpen S) {f : E → F}
    (hf : ContDiffOn ℝ 1 f S) {x s : E} {γ : ℝ}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • s ∈ S)
    (hlip : ∀ z ∈ S, ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ γ * ‖z - x‖) :
    ‖f (x + s) - (f x + fderiv ℝ f x s)‖ ≤ (1 / 2 : ℝ) * γ * ‖s‖ ^ 2 :=
  norm_sub_firstOrder_le_of_lipschitzAt_segment hS hf hseg hlip

open Optimization ConvexAnalysis in
/-- **Equation (3.1.4)** of [conn2000trust]. Let $V$ be a finite-dimensional real inner product
space, and let $f : V \to \mathbb{R}$ be Lipschitz continuous on a neighbourhood of $x \in V$.
Then for every direction $d \in V$ the Clarke directional derivative is attained as a maximum
over the Clarke subdifferential:
$$f^\circ(x; d) = \max_{g \in \partial f(x)} \langle g, d \rangle.$$

The Clarke derivative is `Optimization.clarkeDerivative`, the upper limit of the difference
quotients. The subdifferential `Optimization.clarkeSubgradient` is the set of $g$ with
$\langle g, d \rangle \le f^\circ(x; d)$ for all $d$. Local Lipschitz continuity makes the upper
limit finite and gives the support identity, and compactness of the subdifferential in finite
dimension gives attainment. -/
theorem clarkeDerivative_isGreatest {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {f : V → ℝ} {x : V}
    {U : Set V} {L : NNReal} (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U) (d : V) :
    IsGreatest ((fun g : V ↦ inner ℝ g d) '' Optimization.clarkeSubgradient f x)
      (Optimization.clarkeDerivative f x d) := by
  have hs := hasClarkeSupport_of_lipschitzOnWith hU hL
  have hc := isCompact_clarkeSubgradient hU hL
  have hcont : Continuous (fun g : V ↦ inner ℝ g d) :=
    continuous_id.inner continuous_const
  obtain ⟨g, hg, hm⟩ := hc.exists_isMaxOn hs.nonempty hcont.continuousOn
  have hu (z : V) (hz : z ∈ clarkeSubgradient f x) :
      inner ℝ z d ≤ clarkeDerivative f x d := hz d
  have hmax : clarkeDerivative f x d ≤ inner ℝ g d := by
    apply EReal.coe_le_coe_iff.mp
    rw [← hs d]
    apply supportFn_le_coe_iff.mpr
    intro z hz
    simpa only [innerₗ_apply_apply] using isMaxOn_iff.mp hm z hz
  refine ⟨⟨g, hg, le_antisymm (hu g hg) hmax⟩, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hu z hz

section Moreau

open scoped RealInnerProductSpace
open ConvexAnalysis Optimization

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- **Equation (3.1.7)** of [conn2000trust] (Moreau decomposition). Let $V$ be a real Hilbert space,
let $C \subseteq V$, and let $x, v \in V$. Let $N$ be the normal cone of $C$ at $x$, the set of
$d$ with $\langle d, y - x \rangle \le 0$ for all $y \in C$, and let $T$ be its polar cone, the
tangent cone. Then
$$v = P_T(v) + P_N(v) \quad \text{and} \quad \langle P_T(v), P_N(v) \rangle = 0.$$

The cones are `Optimization.normalDirections C x` and `Optimization.tangentDirections C x`, and
the projections are `bestApprox`. The set $C$ need not be convex, because $N$ is a closed convex
cone for every $C$.

**Reading.** The theorem gives the orthogonal decomposition using the project's normal and tangent
direction cones for a general set. Closed convex feasible sets recover the source cones.
-/
theorem moreau_normal_tangent (C : Set V) (x v : V) :
    let n := bestApprox (normalDirections C x) v
    let t := bestApprox (tangentDirections C x) v
    v = t + n ∧ ⟪t, n⟫ = 0 := by
  let N := normalDirections C x
  let T := tangentDirections C x
  let n := bestApprox N v
  let d := v - n
  have hN : N = polarCone (innerₗ V) ((fun y ↦ y - x) '' C) := by
    ext u
    change u ∈ normalDirections C x ↔ _
    rw [mem_normalDirections, mem_polarCone]
    simp only [Set.forall_mem_image, innerₗ_apply_apply, real_inner_comm]
  have hn₀ : (0 : V) ∈ N := hN ▸ zero_mem_polarCone _ _
  have hn := (bestApprox_eq_iff ⟨0, hn₀⟩ (hN ▸ isClosed_polarCone)
    (hN ▸ convex_polarCone _ _)).1 (rfl : bestApprox N v = n)
  have hadd {u w : V} (hu : u ∈ N) (hw : w ∈ N) : u + w ∈ N := by
    apply mem_normalDirections.mpr
    intro y hy
    rw [inner_add_left]
    exact add_nonpos (mem_normalDirections.mp hu y hy) (mem_normalDirections.mp hw y hy)
  have hd₀ := hn.2 0 hn₀
  have hd₂ := hn.2 (n + n) (hadd hn.1 hn.1)
  have horth : ⟪d, n⟫ = 0 := by
    change ⟪d, 0 - n⟫ ≤ 0 at hd₀
    change ⟪d, n + n - n⟫ ≤ 0 at hd₂
    simp only [zero_sub, inner_neg_right, add_sub_cancel_right] at hd₀ hd₂
    linarith
  have hd : d ∈ T := by
    apply mem_polarCone.mpr
    intro u hu
    have h := hn.2 (n + u) (hadd hn.1 hu)
    change ⟪d, n + u - n⟫ ≤ 0 at h
    simpa only [add_sub_cancel_left, innerₗ_apply_apply, real_inner_comm] using h
  have ht : bestApprox T v = d := by
    apply (bestApprox_eq_iff (polarCone_nonempty _ _) isClosed_polarCone
      (convex_polarCone _ _)).mpr
    refine ⟨hd, fun u hu ↦ ?_⟩
    have hp := (mem_polarCone.mp hu) n hn.1
    have he : v - d = n := by simp [d]
    have horth' : ⟪n, d⟫ = 0 := (real_inner_comm _ _).trans horth
    rw [he, inner_sub_right, horth', sub_zero]
    exact hp
  change v = bestApprox T v + n ∧ ⟪bestApprox T v, n⟫ = 0
  exact ⟨by rw [ht]; simp [d], ht.symm ▸ horth⟩

end Moreau

end ConnGouldToint.Chapter03
