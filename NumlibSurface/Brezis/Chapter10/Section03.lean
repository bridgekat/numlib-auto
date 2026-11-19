/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.PDE.Wave
import NumlibSurface.Brezis.Chapter10.Section02

/-!
# Brezis, Section 10.3: The wave equation

This module formalizes Section 10.3 of [brezis2011functional]. Let $\Omega \subset \mathbb{R}^N$ be
open with boundary $\Gamma$, $Q = \Omega \times (0, \infty)$ and
$\Sigma = \Gamma \times (0, \infty)$. The wave equation is the problem
$$\partial_{tt} u - \Delta u = 0 \text{ in } Q \ (27), \quad u = 0 \text{ on } \Sigma \ (28), \quad
  u(\cdot, 0) = u_0 \ (29), \quad \partial_t u(\cdot, 0) = v_0 \ (30).$$
The source solves it as the first-order system $dU/dt + AU = 0$ for $U = (u, \partial_t u)$ in the
phase space $H = H^1_0(\Omega) \times L^2(\Omega)$ with the scalar product displayed after (35).
The operator (35) is $A(u, v) = (-v, -\Delta u)$. Theorem 10.7 gives existence and uniqueness of a
solution in the class (31) and the energy identity (32), which Remark 6 reads as a conservation law.
Remark 7 uses the Dirichlet scalar product on a bounded $\Omega$, for which $A$ and $-A$ are maximal
monotone and the solutions form a group of isometries. Remark 8 treats d'Alembert's formula on
$\mathbb{R}$ and the propagation of singularities along the characteristics, Remark 9 the Fourier
method, and Theorem 10.8 with Remark 10 the regularity of the solution and the compatibility
conditions.

The proofs specialize the backbone module `Numlib.Analysis.PDE.Wave`.

## Main definitions

* Equation (35), `Brezis.Chapter10.waveOperator`: $A(u, v) = (-v, -\Delta u)$ on $D(A) =
  (H^2(\Omega) \cap H^1_0(\Omega)) \times H^1_0(\Omega)$.
* Problem (27)–(30) in the class (31), `Brezis.Chapter10.IsWaveSolution`: $u \in C([0, \infty); H^2
  \cap H^1_0) \cap C^1([0, \infty); H^1_0) \cap C^2([0, \infty); L^2)$ solves the wave equation with
  $u(0) = u_0$ and $\partial_t u(0) = v_0$.

## Main results

* Equation (35), `Brezis.Chapter10.waveOperator_mem_domain_iff`: $D(A) = (H^2(\Omega) \cap
  H^1_0(\Omega)) \times H^1_0(\Omega)$.
* Equation (35), `Brezis.Chapter10.waveOperator_apply`: $A(u, v) = (-v, -\Delta u)$.
* Proof of Theorem 10.7, claim (i), `Brezis.Chapter10.waveOperator_add_id_inner_self_nonneg`:
  $A + I$ is monotone on every open set.
* Proof of Theorem 10.7, `Brezis.Chapter10.waveOperator_eq`: on a $C^2$ domain with bounded
  boundary, $A$ is the backbone wave operator.
* Proof of Theorem 10.7, `Brezis.Chapter10.waveOperator_add_id_isMaximalMonotone`: $A + I$ is
  maximal monotone in $H$.
* Theorem 10.7, `Brezis.Chapter10.theorem_10_7`: the problem (27)–(30) has a unique solution in the
  class (31).
* Theorem 10.7, `Brezis.Chapter10.theorem_10_7_energy`: the energy identity (32), $|\partial_t
  u(t)|^2 + |\nabla u(t)|^2 = |v_0|^2 + |\nabla u_0|^2$.
* Remark 6, `Brezis.Chapter10.remark_10_6`: the energy is constant in time.
* Remark 7, `Brezis.Chapter10.remark_10_7`: for the Dirichlet scalar product on a bounded $\Omega$,
  $(AU, U) = 0$, and $A$ and $-A$ are maximal monotone.
* Remark 7, `Brezis.Chapter10.remark_10_7_group`: the problem can be solved on all of $\mathbb{R}$,
  and (32) holds for all $t \in \mathbb{R}$.
* Remark 8, `Brezis.Chapter10.remark_10_8`: on $\Omega = \mathbb{R}$, d'Alembert's formula (40)
  gives the solution.
* Remark 8, `Brezis.Chapter10.remark_10_8_characteristics`: for $v_0 = 0$, the solution is
  $C^\infty$ off the characteristics through a singular point of $u_0$.
* Remark 9, `Brezis.Chapter10.remark_10_9`: the coefficients of the Fourier series (41)
  in the Dirichlet eigenbasis satisfy the stated oscillator equation.
* Proof of Theorem 10.8, `Brezis.Chapter10.theorem_10_8_domain`: the description of $D(A^k)$, and
  $D(A^k) \subseteq H^{k+1}(\Omega) \times H^k(\Omega)$.
* Proof of Theorem 10.8, `Brezis.Chapter10.theorem_10_8_domain_norm`: the injection $D(A^k)
  \subseteq H^{k+1}(\Omega) \times H^k(\Omega)$ is continuous.
* Theorem 10.8, `Brezis.Chapter10.theorem_10_8`: under the compatibility conditions, $u \in
  C^\infty(\overline{\Omega} \times [0, \infty))$.
* Remark 10, `Brezis.Chapter10.remark_10_10`: the compatibility conditions are necessary for a
  solution that is smooth up to $t = 0$.

## Conventions

* As in Section 10.1, a solution is the curve `u : ℝ → L²(Ω)` of the unknown $u(x, t)$ of the
  source, not the phase-space curve $U = (u, \partial_t u)$. The classes of (31) are the Bochner
  classes of `Numlib.Analysis.PDE.Bochner`.
* The data are $u_0, v_0 \in H^1_0(\Omega)$, elements of `Brezis.Chapter09.hZeroSpace N Ω`. The
  condition $u_0 \in H^2(\Omega) \cap H^1_0(\Omega)$ is that the function of $u_0$ lies in the
  domain $D(A)$ of the operator $A = -\Delta$ of Section 10.1
  (`Brezis.Chapter10.heatOperator_mem_domain_iff`).
* The quantity $|\nabla u(t)|^2_{L^2} = \sum_i \int_\Omega |\partial_i u(x, t)|^2$ of footnote 10 is
  written, as in Section 10.1, for an $H^1_0$-lift of $u(t)$.
* Remark 8 is stated on $\Omega = \mathbb{R}$, the open set `⊤ : Opens ℝ¹` with $\mathbb{R}^1$ =
  `EuclideanSpace ℝ (Fin 1)`.

## Implementation notes

* The phase space is the backbone space `Wave.phaseSpace Ω`, which is `WithLp 2 (H¹₀(Ω) × L²(Ω))`
  with the scalar product displayed after (35).
* The operator (35) of the source is `Brezis.Chapter10.waveOperator Ω`: the backbone operator
  `Wave.operator Ω`, whose domain is $D(-\Delta) \times H^1_0(\Omega)$ for the weak Dirichlet
  Laplacian, restricted to the pairs whose first component lies in $H^2(\Omega)$. On a $C^2$ domain
  with bounded boundary the two operators coincide (`Brezis.Chapter10.waveOperator_eq`, by Theorem
  9.25).
* In Remark 8 the data $u_0 \in H^2(\mathbb{R})$ and $v_0 \in H^1(\mathbb{R})$ are read in
  $H^1_0(\mathbb{R}) = H^1(\mathbb{R})$ through `Wave.toZeroTopL`, and the formula (40) through
  `Wave.lineEmbed : ℝ → ℝ¹` and the first coordinate (`Wave.coeFn_dAlembertL2_dAlembert`).
* The compatibility conditions of Theorem 10.8 are read through the domains $D_m$ of the Dirichlet
  Laplacian, `Wave.MemLaplacianDomain`: $D_0 = L^2(\Omega)$, $D_1 = H^1_0(\Omega)$ and $D_{m+2} =
  \{w \in D(-\Delta) : -\Delta w \in D_m\}$.

## Deviations from the source

* **Standing hypothesis of Chapter 10** (generalization). The energy identity (32), Remark 6, Remark
  7 and Remark 9 hold on every open set, or on every bounded one, and are stated so. Theorem 10.7
  carries the hypothesis that $\Omega$ is of class $C^\infty$ with $\Gamma$ bounded. See
  `Brezis.Chapter10.theorem_10_7_energy` and `Brezis.Chapter10.remark_10_9`.
* **Remark 7, group of isometries** (generalization). The two-sided solvability and
  $|U(t)|_H = |U_0|_H$ for all $t \in \mathbb{R}$ are obtained by time reversal, which needs neither
  the boundedness of $\Omega$ nor the Dirichlet scalar product. The statement gives
  trajectories for data in the operator domain and their energy conservation. See
  `Brezis.Chapter10.remark_10_7_group`.
* **Remark 8** (reading). The $L^2$ d'Alembert solution uses $H^2$ displacement and $H^1$
  velocity. The zero-velocity result asserts smoothness away from the characteristic lines.
  See `Brezis.Chapter10.remark_10_8` and `Brezis.Chapter10.remark_10_8_characteristics`.
* **Theorem 10.8** (reading). The compatibility conditions $\Delta^j u_0 = \Delta^j v_0 = 0$ on
  $\Gamma$ are read, as in the display of the proof, as $u_0, v_0 \in D_k$ for every $k$. The
  hypothesis $u_0, v_0 \in H^k(\Omega)$ for every $k$ is then a consequence and is not assumed. See
  `Brezis.Chapter10.theorem_10_8`.
* **Remark 10** (reading). As for Remark 4 of Section 10.1, the statement is for $u$ of class
  $C^\infty$ on $\mathbb{R}^N \times \mathbb{R}$. See `Brezis.Chapter10.remark_10_10`.

## Not formalized

* **Remark 7(ii), $A^* = -A$.** The backbone does not formalize the adjoint for the Dirichlet scalar
  product.
-/

open Filter MeasureTheory Metric Set Topology TopologicalSpace Laplacian
open scoped ContDiff Distributions ENNReal NNReal InnerProductSpace

namespace Brezis.Chapter10

open Brezis.Chapter07 Brezis.Chapter09 SobolevMultiIndex

section General

variable {N : ℕ}

/-- The space $\mathbb{R}^N$ of the source. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-- The standard basis of $\mathbb{R}^N$. -/
local notation "𝔟" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin N) ℝ)

variable {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-! ### The operator (35) on the phase space $H^1_0(\Omega) \times L^2(\Omega)$ -/

variable (Ω) in
/-- **Equation (35)** in Chapter 10 of [brezis2011functional], the operator $A$. Let
$\Omega \subset \mathbb{R}^N$ be open, and let $H = H^1_0(\Omega) \times L^2(\Omega)$ with the
scalar product displayed after (35). The operator $A : D(A) \subset H \to H$ is defined by
$$A(u, v) = (-v, -\Delta u), \qquad D(A) = (H^2(\Omega) \cap H^1_0(\Omega)) \times
  H^1_0(\Omega).$$
As the source says, "the boundary condition (28) has been incorporated in the space $H$".

The definition restricts the backbone operator `Wave.operator Ω`, whose domain is
$D(-\Delta) \times H^1_0(\Omega)$ for the weak Dirichlet Laplacian, to the pairs $(u, v)$ whose
first component is the function of an element of $H^2(\Omega)$, with `LinearPMap.domRestrict`.

**Generalization.** The restriction defining this operator is available on arbitrary open sets. -/
noncomputable def waveOperator : Wave.phaseSpace Ω →ₗ.[ℝ] Wave.phaseSpace Ω :=
  (Wave.operator Ω).domRestrict ((LinearMap.range (fnL ℝ 𝔟 2 2 Ω volume).toLinearMap).comap
    ((SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume).comp (Wave.phaseSpace.fstL Ω)).toLinearMap)

/-- The domain $D(A)$ of the operator (35) is contained in the domain of the backbone wave operator
`Wave.operator Ω`. -/
theorem waveOperator_domain_le : (waveOperator Ω).domain ≤ (Wave.operator Ω).domain :=
  inf_le_right

/-- **Equation (35)** in Chapter 10 of [brezis2011functional], $D(A) = (H^2(\Omega) \cap
H^1_0(\Omega)) \times H^1_0(\Omega)$. Let $\Omega \subset \mathbb{R}^N$ be open and $U = (u, v)
\in H^1_0(\Omega) \times L^2(\Omega)$. Then $U \in D(A)$ if and only if the function of $u$ is
the function of an element of $H^2(\Omega)$ and $v$ is the function of an element of
$H^1_0(\Omega)$.

**Generalization.** The stated domain identity holds on every open set. -/
theorem waveOperator_mem_domain_iff {U : Wave.phaseSpace Ω} :
    U ∈ (waveOperator Ω).domain ↔
      (∃ w : sobolevSpaceHigher N 2 2 Ω,
        fnL ℝ 𝔟 2 2 Ω volume w = SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume U.fst) ∧
      ∃ z : hZeroSpace N Ω, SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume z = U.snd := by
  -- both memberships unfold to the stated conjunctions (`Submodule.mem_inf`, `mem_comap`,
  -- `LinearMap.mem_range` and `Wave.mem_operatorDomain_iff` are all `Iff.rfl`)
  exact ⟨fun h ↦ ⟨h.1, h.2.2⟩,
    fun h ↦ ⟨h.1, mem_dirichletLaplacianDomain_of_exists_sobolev_two h.1 ⟨U.fst, U.fst.2, rfl⟩,
      h.2⟩⟩

/-- For $U \in D(A)$, the value $AU$ of the operator (35) is the value of the backbone wave operator
`Wave.operator Ω` at $U$. -/
theorem waveOperator_apply_eq (U : (waveOperator Ω).domain) :
    waveOperator Ω U = Wave.operator Ω ⟨U, waveOperator_domain_le U.2⟩ :=
  rfl

/-- **Equation (35)** in Chapter 10 of [brezis2011functional], $A(u, v) = (-v, -\Delta u)$. Let
$\Omega \subset \mathbb{R}^N$ be open, let $U = (u, v) \in D(A)$, and let $w \in H^2(\Omega)$
have the same function as $u$. Then the first component of $AU$ has the function $-v$ in
$L^2(\Omega)$, and the second component is
$$-\Delta u = -\sum_i \frac{\partial^2 w}{\partial x_i^2},$$
where $\partial^2 w / \partial x_i^2$ is the weak derivative of $w$ at the multi-index $2 e_i$.

**Generalization.** The component formula holds on every open set. -/
theorem waveOperator_apply (U : (waveOperator Ω).domain) (w : sobolevSpaceHigher N 2 2 Ω)
    (hw : fnL ℝ 𝔟 2 2 Ω volume w
      = SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume (U : Wave.phaseSpace Ω).fst) :
    SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume (waveOperator Ω U).fst
        = -(U : Wave.phaseSpace Ω).snd ∧
      (waveOperator Ω U).snd
        = -∑ i, weakDeriv w (MultiIndexLE.addSingle i (MultiIndexLE.single i)) := by
  refine ⟨(congrArg (fun V ↦ SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume V.fst)
    (waveOperator_apply_eq U)).trans (Wave.fnL_operator_apply_fst _), ?_⟩
  -- the ascription fixes `Ω` before the anonymous constructor is elaborated (a minute otherwise)
  exact (congrArg Wave.phaseSpace.snd (waveOperator_apply_eq U)).trans
    ((Wave.operator_apply_snd
      (⟨U, waveOperator_domain_le U.2⟩ : (Wave.operator Ω).domain)).trans
      ((dirichletLaplacian_apply_eq_neg_sobolevLaplacianL w _ hw).trans
        (congrArg Neg.neg (sobolevLaplacianL_apply w))))

/-- **Proof of Theorem 10.7** in [brezis2011functional], claim (i): $A + I$ is monotone. Let
$\Omega \subset \mathbb{R}^N$ be open. For every $U = (u, v) \in D(A)$,
$$(AU, U)_H + |U|^2_H = -\int_\Omega uv + \int_\Omega u^2 + \int_\Omega v^2 + \int_\Omega
  |\nabla u|^2 \ge 0.$$

The statement holds on every open set. The proof specializes
`Wave.operator_add_id_inner_self_nonneg`.

**Generalization.** Monotonicity of $A+I$ holds on every open set. -/
theorem waveOperator_add_id_inner_self_nonneg (U : (waveOperator Ω).domain) :
    0 ≤ ⟪waveOperator Ω U, (U : Wave.phaseSpace Ω)⟫_ℝ + ‖(U : Wave.phaseSpace Ω)‖ ^ 2 := by
  have h := Wave.operator_add_id_inner_self_nonneg
    (⟨U, waveOperator_domain_le U.2⟩ : (Wave.operator Ω).domain)
  exact h

/-! ### The problem (27)–(30) in the class (31) -/

variable (Ω) in
/-- **Theorem 10.7** of [brezis2011functional], the problem (27), (28), (29), (30) in the class
(31). Let $\Omega \subset \mathbb{R}^N$ be open and $u_0, v_0 \in H^1_0(\Omega)$. A curve
$u : \mathbb{R} \to L^2(\Omega)$ is a **solution of the wave equation** with data $u_0$, $v_0$
if

* $u(t) \in D(A) = H^2(\Omega) \cap H^1_0(\Omega)$ for $t \ge 0$, which is the boundary
  condition (28), and $u \in C([0, \infty); H^2(\Omega))$,
* $u \in C^1([0, \infty); H^1_0(\Omega))$ and $u \in C^2([0, \infty); L^2(\Omega))$,
* $\partial_{tt} u(t) = \Delta u(t) = -A u(t)$ in $L^2(\Omega)$ for $t \ge 0$, which is the wave
  equation (27), and
* $u(0) = u_0$ and $\partial_t u(0) = v_0$, which are the initial conditions (29) and (30).

The curve $u$ is the function $u(x, t)$ of the source, read as $t \mapsto u(\cdot, t)$. Here
$A$ is the operator `Brezis.Chapter10.heatOperator` of Section 10.1.

**Reading.** The initial derivatives are one-sided, and the differential equation is also
imposed at time zero by continuity. The predicate is available on every open set. -/
structure IsWaveSolution (u₀ v₀ : hZeroSpace N Ω) (u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) :
    Prop where
  /-- $u \in C([0, \infty); H^2(\Omega))$. -/
  contDiffOnThrough_two : Bochner.ContDiffOnThrough (fnL ℝ 𝔟 2 2 Ω volume) 0 u (Ici 0)
  /-- $u(t) \in H^2(\Omega) \cap H^1_0(\Omega)$ for $t \ge 0$: the boundary condition (28). -/
  mem_domain : ∀ t, 0 ≤ t → u t ∈ (heatOperator Ω).domain
  /-- $u \in C^1([0, \infty); H^1_0(\Omega))$. -/
  contDiffOnThrough_one :
    Bochner.ContDiffOnThrough (SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume) 1 u (Ici 0)
  /-- $u \in C^2([0, \infty); L^2(\Omega))$. -/
  contDiffOn : ContDiffOn ℝ 2 u (Ici 0)
  /-- The wave equation (27): $\partial_{tt} u(t) = \Delta u(t) = -A u(t)$ for $t \ge 0$, with
  one-sided derivatives at $t = 0$. -/
  eqn : ∀ t (ht : 0 ≤ t),
    iteratedDerivWithin 2 u (Ici 0) t = -(heatOperator Ω ⟨u t, mem_domain t ht⟩)
  /-- The initial condition (29): $u(0) = u_0$. -/
  apply_zero : u 0 = SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume u₀
  /-- The initial condition (30): $\partial_t u(0) = v_0$, with the right derivative at $t = 0$. -/
  derivWithin_zero : derivWithin u (Ici 0) 0 = SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume v₀

variable {u₀ v₀ : hZeroSpace N Ω}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-- A solution of the wave equation in the class (31) of Theorem 10.7 is a solution in the backbone
class `Wave.IsSolution`. This holds on every open set $\Omega$, because
$D(A) \subseteq D(-\Delta)$, and the clause $u \in C([0, \infty); D(-\Delta))$ follows from
$u \in C^2([0, \infty); L^2(\Omega))$ and the equation $-\Delta u = -\partial_{tt} u$. -/
theorem IsWaveSolution.isSolution (h : IsWaveSolution Ω u₀ v₀ u) :
    Wave.IsSolution Ω u₀ (SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume v₀) u where
  contDiffOn := h.contDiffOn
  contDiffOnThrough := h.contDiffOnThrough_one
  mem_domain t ht := heatOperator_domain_le (h.mem_domain t ht)
  contDiffOnPowDomain := by
    rw [LinearPMap.contDiffOnPowDomain_iff dirichletLaplacian_isClosed]
    refine ⟨![u, fun t ↦ -iteratedDerivWithin 2 u (Ici 0) t], fun t _ ↦ rfl, ?_, ?_⟩
    · rw [Fin.forall_fin_two]
      exact ⟨h.contDiffOn.of_le (by simp), contDiffOn_zero.2
        (h.contDiffOn.continuousOn_iteratedDerivWithin le_rfl (uniqueDiffOn_Ici 0)).neg⟩
    · intro t ht i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      refine ⟨heatOperator_domain_le (h.mem_domain t ht), ?_⟩
      change dirichletLaplacian Ω ⟨u t, heatOperator_domain_le (h.mem_domain t ht)⟩
        = -iteratedDerivWithin 2 u (Ici 0) t
      rw [h.eqn t ht, neg_neg]
      exact (heatOperator_apply_eq ⟨u t, h.mem_domain t ht⟩).symm
  eqn t ht := (h.eqn t ht).trans (congrArg Neg.neg (heatOperator_apply_eq ⟨u t, h.mem_domain t ht⟩))
  apply_zero := h.apply_zero
  derivWithin_zero := h.derivWithin_zero

/-- Let $u$ be a solution of the wave equation in the class (31) of Theorem 10.7, let $t \ge 0$, and
let $w \in H^1_0(\Omega)$ have the function $u(t)$. Then $(-\Delta u(t), u(t))_{L^2} = \sum_i
\int_\Omega |\partial w / \partial x_i|^2$, where $-\Delta$ is the Dirichlet Laplacian
`dirichletLaplacian Ω`. Thus the gradient norm of $u(t)$ does not depend on the choice of the
$H^1_0$-lift. -/
theorem IsWaveSolution.inner_apply_self_eq (h : IsWaveSolution Ω u₀ v₀ u) {t : ℝ} (ht : 0 ≤ t)
    {w : hSpace N Ω} (hw : w ∈ hZeroSpace N Ω) (hwt : fnL ℝ 𝔟 1 2 Ω volume w = u t) :
    ⟪dirichletLaplacian Ω ⟨u t, h.isSolution.mem_domain t ht⟩, u t⟫_ℝ
      = ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv w i x ^ 2 :=
  (dirichletLaplacian_inner_self_eq_dirichletForm _ hw hwt).trans
    (sum_integral_partialDeriv_sq w).symm

/-! ### Theorem 10.7, the energy identity (32), and Remark 6 -/

/-- **Theorem 10.7** of [brezis2011functional], the energy identity (32). Let
$\Omega \subset \mathbb{R}^N$ be open, let $u_0, v_0 \in H^1_0(\Omega)$, and let $u$ be a
solution of (27), (28), (29), (30) in the class (31). Let $t \ge 0$ and let
$w \in H^1_0(\Omega)$ have the function $u(t)$. Then
$$|\partial_t u(t)|^2_{L^2} + |\nabla u(t)|^2_{L^2} = |v_0|^2_{L^2} + |\nabla u_0|^2_{L^2},$$
where $|\nabla u(t)|^2_{L^2} = \sum_i \int_\Omega |\partial w / \partial x_i|^2$ as in
footnote 10.

The statement holds on every open set, and $\partial_t u(t)$ is the right derivative at $t = 0$.
The argument of the source: "multiply (27) by $\partial_t u$ and integrate on $\Omega$", with
$\int_\Omega \partial_{tt} u \, \partial_t u = \frac12 \partial_t \int_\Omega |\partial_t u|^2$
and $\int_\Omega (-\Delta u) \partial_t u = \frac12 \partial_t \int_\Omega |\nabla u|^2$. The
proof specializes `Wave.IsSolution.energy_dirichletForm`.

**Generalization.** The same energy identity holds on every open set. -/
theorem theorem_10_7_energy (hu : IsWaveSolution Ω u₀ v₀ u) {t : ℝ} (ht : 0 ≤ t)
    {w : hSpace N Ω} (hw : w ∈ hZeroSpace N Ω) (hwt : fnL ℝ 𝔟 1 2 Ω volume w = u t) :
    ‖derivWithin u (Ici 0) t‖ ^ 2 + ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv w i x ^ 2
      = ‖SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume v₀‖ ^ 2
        + ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv (u₀ : hSpace N Ω) i x ^ 2 := by
  have e := hu.isSolution.energy ht
  have e1 := hu.inner_apply_self_eq ht hw hwt
  have e2 : ⟪dirichletLaplacian Ω ⟨SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume u₀,
        hu.isSolution.memOperatorDomain_mk.1⟩, SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume u₀⟫_ℝ
      = ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv (u₀ : hSpace N Ω) i x ^ 2 :=
    (dirichletLaplacian_inner_self_eq_dirichletForm _ u₀.2 rfl).trans
      (sum_integral_partialDeriv_sq _).symm
  exact (congrArg (‖derivWithin u (Ici 0) t‖ ^ 2 + ·) e1).symm.trans
    (e.trans (congrArg (‖SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume v₀‖ ^ 2 + ·) e2))

/-- **Remark 6** in Chapter 10 of [brezis2011functional]. Equation (32) is a conservation law: the
energy $E(t) = |\partial_t u(t)|^2_{L^2} + |\nabla u(t)|^2_{L^2}$ of the system is constant in
time. Precisely, let $\Omega \subset \mathbb{R}^N$ be open, let $u$ be a solution of (27), (28),
(29), (30) in the class (31), and let $E : \mathbb{R} \to \mathbb{R}$ be a function with $E(t) =
|\partial_t u(t)|^2_{L^2} + \sum_i \int_\Omega |\partial_i u(x, t)|^2$ for $t \ge 0$, computed
on an $H^1_0$-lift of $u(t)$. Then $E(t) = E(0)$ for every $t \ge 0$.

**Generalization.** Conservation holds on every open set. -/
theorem remark_10_6 (hu : IsWaveSolution Ω u₀ v₀ u) {E : ℝ → ℝ}
    (hE : ∀ t, 0 ≤ t → ∃ w : hSpace N Ω, w ∈ hZeroSpace N Ω ∧ fnL ℝ 𝔟 1 2 Ω volume w = u t ∧
      E t = ‖derivWithin u (Ici 0) t‖ ^ 2 + ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv w i x ^ 2) :
    ∀ t, 0 ≤ t → E t = E 0 := by
  intro t ht
  obtain ⟨w, hw, hwt, hEt⟩ := hE t ht
  obtain ⟨w₀, hw₀, hw₀t, hE0⟩ := hE 0 le_rfl
  rw [hEt, hE0, theorem_10_7_energy hu ht hw hwt, theorem_10_7_energy hu le_rfl hw₀ hw₀t]

/-! ### Remark 8: d'Alembert's formula, the characteristics -/

/-- **Remark 8** in Chapter 10 of [brezis2011functional], the propagation of singularities. On
$\Omega = \mathbb{R}$ with $v_0 = 0$, the solution is
$$u(x, t) = \frac12 \big(u_0(x + t) + u_0(x - t)\big),$$
and it is not more regular than $u_0$. Precisely, let $u_0 : \mathbb{R} \to \mathbb{R}$ and
$x_0 \in \mathbb{R}$, and let $u_0$ be of class $C^\infty$ on $\mathbb{R} \setminus \{x_0\}$.
Then the function $u$ above is of class $C^\infty$ on $\mathbb{R} \times \mathbb{R}$ except on
the characteristics $x + t = x_0$ and $x - t = x_0$ through $(x_0, 0)$: singularities propagate
along the characteristics.

The function $u$ is the backbone function `Wave.dAlembert u₀ 0`, and the first part of the
statement is the formula for it. The proof specializes
`Wave.dAlembert_contDiffOn_off_characteristics`.

**Reading.** This proves smoothness off the two characteristics. It makes no assertion of
 singularity at every point of either line. -/
theorem remark_10_8_characteristics {u₀ : ℝ → ℝ} {x₀ : ℝ} (hu₀ : ContDiffOn ℝ ∞ u₀ {x₀}ᶜ) :
    (∀ t x, Wave.dAlembert u₀ 0 t x = (1 / 2) * (u₀ (x + t) + u₀ (x - t))) ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ ↦ Wave.dAlembert u₀ 0 p.2 p.1)
        {p : ℝ × ℝ | p.1 + p.2 ≠ x₀ ∧ p.1 - p.2 ≠ x₀} :=
  ⟨fun t x ↦ Wave.dAlembert_zero_apply u₀ t x, Wave.dAlembert_contDiffOn_off_characteristics hu₀⟩

end General

section Regular

variable {d : ℕ}

/-- The space $\mathbb{R}^N$ of the source, with $N = d + 1$. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

/-- The standard basis of $\mathbb{R}^N$. -/
local notation "𝔟" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin (d + 1)) ℝ)

variable {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-! ### The operator on a regular domain, and Theorem 10.7 -/

/-- **Proof of Theorem 10.7** in [brezis2011functional], $A$ is the backbone wave operator. Let
$\Omega \subset \mathbb{R}^N$ be open of class $C^2$, with $N = d + 1$ and bounded boundary
$\Gamma$. Then the operator (35) equals the backbone operator `Wave.operator Ω`: its domain
$D(-\Delta) \times H^1_0(\Omega)$ is $(H^2(\Omega) \cap H^1_0(\Omega)) \times H^1_0(\Omega)$ by
Theorem 9.25 (`Brezis.Chapter10.heatOperator_eq_dirichletLaplacian`). -/
theorem waveOperator_eq (hΩ : IsOfClassC 2 (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) :
    waveOperator Ω = Wave.operator Ω := by
  have hdom := (dirichletLaplacianDomain_eq_of_isContDiffChartDomain hΩ hΓ).1
  refine LinearPMap.eq_of_le_of_domain_eq LinearPMap.domRestrict_le
    (le_antisymm inf_le_right (le_inf (fun U hU ↦ ?_) le_rfl))
  -- `U ∈ D(−Δ) × H¹₀` has an `H²` first component by Theorem 9.25
  exact ((hdom _).1 (Wave.memOperatorDomain_of_mem hU).1).1

/-- **Proof of Theorem 10.7** in [brezis2011functional]: $A + I$ is maximal monotone in $H$. Let
$\Omega \subset \mathbb{R}^N$ be open of class $C^2$, with $N = d + 1$ and bounded boundary
$\Gamma$. Then $A + I$ is maximal monotone in $H = H^1_0(\Omega) \times L^2(\Omega)$:

* (i) $(AU, U)_H + |U|^2_H \ge 0$ (`Brezis.Chapter10.waveOperator_add_id_inner_self_nonneg`),
  and
* (ii) $A + 2I$ is onto: given $F = (f, g)$, solve $-\Delta u + 4u = 2f + g$ by Theorem 9.25 and
  set $v = 2u - f$.

Maximal monotonicity is `Brezis.Chapter07.IsMaximalMonotone`. On the weak domain, (ii) uses the
Riesz representation on $H^1_0(\Omega)$. The proof specializes
`Wave.operator_add_id_isMaximalMonotone` through `Brezis.Chapter10.waveOperator_eq`.

**Generalization.** For maximal monotonicity of the source operator plus identity, a
 $C^2$ boundary suffices. -/
theorem waveOperator_add_id_isMaximalMonotone (hΩ : IsOfClassC 2 (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) :
    Brezis.Chapter07.IsMaximalMonotone
      ((LinearMap.id : Wave.phaseSpace Ω →ₗ[ℝ] Wave.phaseSpace Ω) +ᵥ waveOperator Ω) := by
  rw [waveOperator_eq hΩ hΓ, isMaximalMonotone_iff]
  exact Wave.operator_add_id_isMaximalMonotone

variable {u₀ v₀ : hZeroSpace (d + 1) Ω}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}

/-- Let $\Omega \subset \mathbb{R}^N$ be open of class $C^2$, with $N = d + 1$ and bounded boundary
$\Gamma$, and let $u_0, v_0 \in H^1_0(\Omega)$. Then a curve $u$ is a solution of the wave
equation in the class (31) of Theorem 10.7 if and only if it is a solution in the backbone class
`Wave.IsSolution` with the data $u_0$ and the function of $v_0$.

The forward direction holds on every open set (`Brezis.Chapter10.IsWaveSolution.isSolution`).
Conversely, a solution in the backbone class has $u(t) \in H^2(\Omega) \cap H^1_0(\Omega)$ and
lifts continuously to $H^2(\Omega)$ by the graph-norm estimate of Theorem 9.25. -/
theorem isWaveSolution_iff (hΩ : IsOfClassC 2 (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) :
    IsWaveSolution Ω u₀ v₀ u
      ↔ Wave.IsSolution Ω u₀ (SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume v₀) u := by
  refine ⟨fun h ↦ h.isSolution, fun h ↦ ?_⟩
  have hdom := (dirichletLaplacianDomain_eq_of_isContDiffChartDomain hΩ hΓ).1
  have hmem : ∀ t, 0 ≤ t → u t ∈ (heatOperator Ω).domain := fun t ht ↦
    heatOperator_mem_domain_iff.2 ((hdom _).1 (h.mem_domain t ht))
  have hΩ' : IsContDiffChartDomain (2 * 1) (Ω : Set 𝔼) := hΩ.of_le (by norm_num)
  exact
    { contDiffOnThrough_two := Bochner.ContDiffOnThrough.of_contDiffOnPowDomain
        h.contDiffOnPowDomain (dirichletLaplacian.powDomainToSobolevL hΩ' hΓ) _
        (fnL_powDomainToSobolevL hΩ' hΓ)
      mem_domain := hmem
      contDiffOnThrough_one := h.contDiffOnThrough
      contDiffOn := h.contDiffOn
      eqn := fun t ht ↦ (h.eqn t ht).trans
        (congrArg Neg.neg (heatOperator_apply_eq ⟨u t, hmem t ht⟩).symm)
      apply_zero := h.apply_zero
      derivWithin_zero := h.derivWithin_zero }

/-- **Theorem 10.7** of [brezis2011functional] (existence and uniqueness). Let
$\Omega \subset \mathbb{R}^N$ be open of class $C^\infty$, with $N = d + 1$ and bounded boundary
$\Gamma$. Let $u_0 \in H^2(\Omega) \cap H^1_0(\Omega)$ and $v_0 \in H^1_0(\Omega)$. Then there
exists a solution $u$ of (27), (28), (29), (30) in the class (31),
$$u \in C([0, \infty); H^2(\Omega) \cap H^1_0(\Omega)) \cap C^1([0, \infty); H^1_0(\Omega)) \cap
  C^2([0, \infty); L^2(\Omega)),$$
and every other such solution agrees with $u$ on $[0, \infty)$.

Uniqueness holds on $[0, \infty)$ because the class does not constrain negative times. The proof
of the source: $A + I$ is maximal monotone in $H = H^1_0(\Omega) \times L^2(\Omega)$
(`Brezis.Chapter10.waveOperator_add_id_isMaximalMonotone`). Theorem 7.4 with the shift $e^{-t}$
gives $U \in C^1([0, \infty); H) \cap C([0, \infty); D(A))$ solving (38) with
$U(0) = (u_0, v_0) \in D(A)$, and (31) is read off from (39). The source cites "Remark 7.7" for
the shift; the remark meant is Remark 6 of Chapter 7, `Brezis.Chapter07.remark_7_6`. The class
$u \in C([0, \infty); H^2 \cap H^1_0)$ of (31) is a consequence of $U \in C^1([0, \infty); H)$
and the equation, not a separate output of Theorem 7.4. The proof specializes
`Wave.existsUnique_isSolution`, on every open set for the weak class, through
`Brezis.Chapter10.isWaveSolution_iff`. The energy identity (32) is
`Brezis.Chapter10.theorem_10_7_energy`.

**Reading.** Here uniqueness is equality of $L^2$-valued curves on nonnegative times.
 The energy identity is stated separately. -/
theorem theorem_10_7 (hΩ : IsOfClassC ⊤ (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) (u₀ v₀ : hZeroSpace (d + 1) Ω)
    (hu₀ : SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume u₀ ∈ (heatOperator Ω).domain) :
    ∃ u, IsWaveSolution Ω u₀ v₀ u ∧ ∀ v, IsWaveSolution Ω u₀ v₀ v → EqOn v u (Ici 0) := by
  have hΩ2 : IsOfClassC 2 (Ω : Set 𝔼) := hΩ.of_le le_top
  obtain ⟨u, hu, huniq⟩ :=
    Wave.existsUnique_isSolution (heatOperator_domain_le hu₀) (v₀ := _) ⟨v₀, rfl⟩
  exact ⟨u, (isWaveSolution_iff hΩ2 hΓ).2 hu, fun v hv ↦ huniq v hv.isSolution⟩

/-! ### Remark 7: the Dirichlet scalar product, the group of isometries -/

/-- **Remark 7** in Chapter 10 of [brezis2011functional], for bounded $\Omega$. Let
$\Omega \subset \mathbb{R}^N$ be a bounded open set of class $C^2$, with $N = d + 1$ and bounded
boundary $\Gamma$. Equip $H^1_0(\Omega)$ with the scalar product
$\int_\Omega \nabla u_1 \cdot \nabla u_2$ (Corollary 9.19) and
$H = H^1_0(\Omega) \times L^2(\Omega)$ with the scalar product
$$(U_1, U_2) = \int_\Omega \nabla u_1 \cdot \nabla u_2 + \int_\Omega v_1 v_2.$$
Let $A(u, v) = (-v, -\Delta u)$ on this space. Then

* the scalar product of the space is the one displayed,
* $D(A) = (H^2(\Omega) \cap H^1_0(\Omega)) \times H^1_0(\Omega)$,
* $(AU, U) = -\int_\Omega \nabla v \cdot \nabla u + \int_\Omega (-\Delta u) v = 0$ for all
  $U = (u, v) \in D(A)$, and
* (i) $A$ and $-A$ are maximal monotone.

The space is `Wave.dirichletPhaseSpace Ω hb` and the operator is `Wave.operator' Ω hb`. Maximal
monotonicity is `Brezis.Chapter07.IsMaximalMonotone`. The clause (ii) $A^* = -A$ is not
formalized, because the backbone does not formalize the adjoint for this scalar product.

**Generalization.** For these claims a bounded domain of class $C^2$ suffices. -/
theorem remark_10_7 (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hΩ : IsOfClassC 2 (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) :
    (∀ U V : Wave.dirichletPhaseSpace Ω hb, ⟪U, V⟫_ℝ
      = (∫ x in (Ω : Set 𝔼), ∑ i, partialDeriv (U.fst : hSpace (d + 1) Ω) i x
          * partialDeriv (V.fst : hSpace (d + 1) Ω) i x)
        + ∫ x in (Ω : Set 𝔼), U.snd x * V.snd x) ∧
    (∀ U : Wave.dirichletPhaseSpace Ω hb, U ∈ (Wave.operator' Ω hb).domain ↔
      (∃ w : sobolevSpaceHigher (d + 1) 2 2 Ω,
        fnL ℝ 𝔟 2 2 Ω volume w = SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume U.fst) ∧
      ∃ z : hZeroSpace (d + 1) Ω, SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume z = U.snd) ∧
    (∀ U : (Wave.operator' Ω hb).domain,
      ⟪Wave.operator' Ω hb U, (U : Wave.dirichletPhaseSpace Ω hb)⟫_ℝ = 0) ∧
    Brezis.Chapter07.IsMaximalMonotone (Wave.operator' Ω hb) ∧
    Brezis.Chapter07.IsMaximalMonotone (-Wave.operator' Ω hb) := by
  have hdom := (dirichletLaplacianDomain_eq_of_isContDiffChartDomain hΩ hΓ).1
  refine ⟨fun U V ↦ ?_, fun U ↦ ?_, Wave.operator'_inner_self_eq_zero,
    (isMaximalMonotone_iff _).2 Wave.operator'_isMaximalMonotone,
    (isMaximalMonotone_iff _).2 Wave.neg_operator'_isMaximalMonotone⟩
  · rw [Wave.dirichletPhaseSpace.inner_def, Elliptic.dirichletForm_apply,
      MeasureTheory.L2.inner_eq_integral_mul]
    rfl
  · exact (Wave.mem_operator'_domain_iff.trans Wave.memOperatorDomain'_iff).trans
      ⟨fun h ↦ ⟨((hdom _).1 h.1).1, h.2⟩, fun h ↦
        ⟨mem_dirichletLaplacianDomain_of_exists_sobolev_two h.1 ⟨U.fst, U.fst.2, rfl⟩, h.2⟩⟩

/-- **Remark 7** in Chapter 10 of [brezis2011functional], the group of isometries. The problem
$dU/dt + AU = 0$ can also be solved on $(-\infty, 0]$: "just change $t$ into $-t$", and footnote
12 notes that time is reversible for the wave equation. Let $\Omega \subset \mathbb{R}^N$ be
open of class $C^\infty$, with $N = d + 1$ and bounded boundary $\Gamma$, let
$u_0 \in H^2(\Omega) \cap H^1_0(\Omega)$ and $v_0 \in H^1_0(\Omega)$. Then

* there is a unique curve $u : \mathbb{R} \to L^2(\Omega)$ that solves (27)–(30) with the data
  $(u_0, v_0)$ on $[0, \infty)$ and whose reflection $t \mapsto u(-t)$ solves (27)–(30) with the
  data $(u_0, -v_0)$ on $[0, \infty)$, and
* for such a curve $u$, the relation (32) holds for all $t \in \mathbb{R}$: $|U(t)|_H = |U_0|_H$
  in the energy norm, that is, $|\partial_t u(t)|^2 + |\nabla u(t)|^2 = |v_0|^2 + |\nabla
  u_0|^2$, where $|\nabla u(t)|^2$ is computed on any $H^1_0$-lift of $u(t)$.

**Generalization.** The source states the remark for bounded $\Omega$ with the Dirichlet scalar
product. Time reversal needs neither the boundedness of $\Omega$ nor the Dirichlet scalar
product, so the statement assumes neither.

For $t \le 0$ the time derivative $\partial_t u(t)$ is that of the reflected solution at $-t$.
The proof specializes `Wave.existsUnique_isSolution_backward` and `Wave.IsSolution.energy_neg`.

**Reading.** The statement gives two-sided solvability and energy conservation for data in
 the operator domain. The source also describes the isometries as a group on the phase space. -/
theorem remark_10_7_group (hΩ : IsOfClassC ⊤ (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) (u₀ v₀ : hZeroSpace (d + 1) Ω)
    (hu₀ : SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume u₀ ∈ (heatOperator Ω).domain) :
    (∃! u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)),
      IsWaveSolution Ω u₀ v₀ u ∧ IsWaveSolution Ω u₀ (-v₀) fun t ↦ u (-t)) ∧
    ∀ u, IsWaveSolution Ω u₀ v₀ u → IsWaveSolution Ω u₀ (-v₀) (fun t ↦ u (-t)) →
      ∀ t (w : hSpace (d + 1) Ω), w ∈ hZeroSpace (d + 1) Ω → fnL ℝ 𝔟 1 2 Ω volume w = u t →
        (0 ≤ t → ‖derivWithin u (Ici 0) t‖ ^ 2
            + ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv w i x ^ 2
          = ‖SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume v₀‖ ^ 2
            + ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv (u₀ : hSpace (d + 1) Ω) i x ^ 2) ∧
        (t ≤ 0 → ‖derivWithin (fun s ↦ u (-s)) (Ici 0) (-t)‖ ^ 2
            + ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv w i x ^ 2
          = ‖SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume v₀‖ ^ 2
            + ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv (u₀ : hSpace (d + 1) Ω) i x ^ 2) := by
  have hΩ2 : IsOfClassC 2 (Ω : Set 𝔼) := hΩ.of_le le_top
  have hneg : SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume (-v₀)
      = -SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume v₀ := _root_.map_neg _ _
  -- the reflected class, with the datum `−v₀` read in `L²(Ω)`
  have hrefl : ∀ u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)),
      IsWaveSolution Ω u₀ (-v₀) (fun t ↦ u (-t)) →
      Wave.IsSolution Ω u₀ (-(SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume v₀)) (fun t ↦ u (-t)) :=
    fun u hu' ↦ Eq.mp (congrArg (fun z ↦ Wave.IsSolution Ω u₀ z (fun t ↦ u (-t))) hneg)
      hu'.isSolution
  have hrefl' : ∀ u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)),
      Wave.IsSolution Ω u₀ (-(SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume v₀))
      (fun t ↦ u (-t)) → IsWaveSolution Ω u₀ (-v₀) (fun t ↦ u (-t)) :=
    fun u h ↦ (isWaveSolution_iff hΩ2 hΓ).2
      (Eq.mp (congrArg (fun z ↦ Wave.IsSolution Ω u₀ z (fun t ↦ u (-t))) hneg.symm) h)
  refine ⟨?_, fun u hu hu' t w hw hwt ↦ ⟨fun ht ↦ theorem_10_7_energy hu ht hw hwt, fun ht ↦ ?_⟩⟩
  · obtain ⟨U, ⟨hU1, hU2⟩, huniq⟩ := Wave.existsUnique_isSolution_backward
      (heatOperator_domain_le hu₀) (v₀ := _) ⟨v₀, rfl⟩
    exact ⟨U, ⟨(isWaveSolution_iff hΩ2 hΓ).2 hU1, hrefl' U hU2⟩,
      fun v ⟨hv1, hv2⟩ ↦ huniq v ⟨hv1.isSolution, hrefl v hv2⟩⟩
  · have h' := hrefl u hu'
    have e := h'.energy_neg ht
    have hmem : u t ∈ (dirichletLaplacian Ω).domain :=
      neg_neg t ▸ h'.mem_domain (-t) (neg_nonneg.2 ht)
    have e1 : ⟪dirichletLaplacian Ω ⟨u t, hmem⟩, u t⟫_ℝ
        = ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv w i x ^ 2 :=
      (dirichletLaplacian_inner_self_eq_dirichletForm _ hw hwt).trans
        (sum_integral_partialDeriv_sq w).symm
    have e2 : ⟪dirichletLaplacian Ω ⟨SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume u₀,
          h'.memOperatorDomain_mk.1⟩, SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume u₀⟫_ℝ
        = ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv (u₀ : hSpace (d + 1) Ω) i x ^ 2 :=
      (dirichletLaplacian_inner_self_eq_dirichletForm _ u₀.2 rfl).trans
        (sum_integral_partialDeriv_sq _).symm
    exact (congrArg (‖derivWithin (fun s ↦ u (-s)) (Ici 0) (-t)‖ ^ 2 + ·) e1).symm.trans
      (e.trans (congrArg (‖SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume v₀‖ ^ 2 + ·) e2))

/-! ### Remark 9: the Fourier method -/

/-- **Remark 9** in Chapter 10 of [brezis2011functional] (the Fourier method for the wave equation).
Let $\Omega \subset \mathbb{R}^N$ be a bounded nonempty open set, with $N = d + 1$. Let $(e_n)$
and $(\lambda_n)$ be the Dirichlet eigenbasis of $-\Delta$ and its eigenvalues from Theorem
9.31, with $\lambda_n > 0$, let $u_0, v_0 \in H^1_0(\Omega)$, and let $u$ be a solution of (27),
(28), (29), (30) in the class (31). Write $a_n(t) = (u(t), e_n)_{L^2}$, so that
$u(t) = \sum_n a_n(t) e_n$. Then

* $a_n'' + \lambda_n a_n = 0$ on $[0, \infty)$: $a_n' = (\partial_t u, e_n)$ and
  $(a_n')' = -\lambda_n a_n$, with one-sided derivatives at $t = 0$,
* the coefficients are given by the oscillator formula,
$$a_n(t) = a_n(0) \cos(\sqrt{\lambda_n}\, t) + \frac{a_n'(0)}{\sqrt{\lambda_n}}
  \sin(\sqrt{\lambda_n}\, t), \qquad a_n(0) = \int_\Omega u_0 e_n, \quad a_n'(0) = \int_\Omega
  v_0 e_n,$$
for $t \ge 0$, and
* $u(t) = \sum_n a_n(t) e_n$ in $L^2(\Omega)$ for every $t \ge 0$.

The eigenbasis is `Elliptic.dirichletEigenbasis` and the eigenvalues are
`Elliptic.dirichletEigenvalue`. No regularity of $\Omega$ is needed. The proof specializes
`Wave.IsSolution.hasDerivWithinAt_inner_eigenbasis`,
`Wave.IsSolution.hasDerivWithinAt_inner_derivWithin_eigenbasis`,
`Wave.IsSolution.inner_eigenfunction` and `Wave.IsSolution.hasSum_eigenfunction`.

**Generalization.** No boundary regularity is needed on the bounded nonempty domain. The
 series is shown to converge in $L^2$ at each nonnegative time. -/
theorem remark_10_9 (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hne : (Ω : Set 𝔼).Nonempty)
    (hu : IsWaveSolution Ω u₀ v₀ u) :
    (∀ n, ∀ t, 0 ≤ t →
      HasDerivWithinAt (fun t ↦ ⟪u t, Elliptic.dirichletEigenbasis Ω hb hne n⟫_ℝ)
        ⟪derivWithin u (Ici 0) t, Elliptic.dirichletEigenbasis Ω hb hne n⟫_ℝ (Ici 0) t ∧
      HasDerivWithinAt
        (fun t ↦ ⟪derivWithin u (Ici 0) t, Elliptic.dirichletEigenbasis Ω hb hne n⟫_ℝ)
        (-(Elliptic.dirichletEigenvalue Ω hb n
          * ⟪u t, Elliptic.dirichletEigenbasis Ω hb hne n⟫_ℝ)) (Ici 0) t) ∧
    (∀ n, ∀ t, 0 ≤ t → ⟪u t, Elliptic.dirichletEigenbasis Ω hb hne n⟫_ℝ
      = (∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn (u₀ : hSpace (d + 1) Ω) x
          * Elliptic.dirichletEigenbasis Ω hb hne n x)
          * Real.cos (√(Elliptic.dirichletEigenvalue Ω hb n) * t)
        + (∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn (v₀ : hSpace (d + 1) Ω) x
          * Elliptic.dirichletEigenbasis Ω hb hne n x) / √(Elliptic.dirichletEigenvalue Ω hb n)
          * Real.sin (√(Elliptic.dirichletEigenvalue Ω hb n) * t)) ∧
    ∀ t, 0 ≤ t → HasSum (fun n ↦ ⟪u t, Elliptic.dirichletEigenbasis Ω hb hne n⟫_ℝ
      • Elliptic.dirichletEigenbasis Ω hb hne n) (u t) := by
  have h := hu.isSolution
  refine ⟨fun n t ht ↦ ⟨h.hasDerivWithinAt_inner_eigenbasis hb hne n ht,
    (h.hasDerivWithinAt_inner_derivWithin_eigenbasis hb hne n ht).congr_deriv (neg_mul _ _)⟩,
    fun n t ht ↦ ?_, fun t ht ↦ ?_⟩
  · have h1 : ⟪SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume u₀,
          Elliptic.dirichletEigenbasis Ω hb hne n⟫_ℝ
        = ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn (u₀ : hSpace (d + 1) Ω) x
          * Elliptic.dirichletEigenbasis Ω hb hne n x :=
      MeasureTheory.L2.inner_eq_integral_mul _ _
    have h2 : ⟪SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume v₀,
          Elliptic.dirichletEigenbasis Ω hb hne n⟫_ℝ
        = ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn (v₀ : hSpace (d + 1) Ω) x
          * Elliptic.dirichletEigenbasis Ω hb hne n x :=
      MeasureTheory.L2.inner_eq_integral_mul _ _
    exact (h.inner_eigenfunction hb hne n ht).trans (congrArg₂ (· + ·)
      (congrArg (· * Real.cos (√(Elliptic.dirichletEigenvalue Ω hb n) * t)) h1)
      (congrArg (fun z ↦ z / √(Elliptic.dirichletEigenvalue Ω hb n)
        * Real.sin (√(Elliptic.dirichletEigenvalue Ω hb n) * t)) h2))
  · have := (Elliptic.dirichletEigenbasis Ω hb hne).hasSum_repr (u t)
    refine this.congr_fun fun n ↦ ?_
    rw [HilbertBasis.repr_apply_apply, real_inner_comm]

/-! ### Theorem 10.8: regularity -/

/-- **Proof of Theorem 10.8** in [brezis2011functional], the domains $D(A^k)$. Let
$\Omega \subset \mathbb{R}^N$ be open of class $C^\infty$, with $N = d + 1$ and bounded boundary
$\Gamma$, and let $k \in \mathbb{N}$. The source states, "easy to see, by induction on $k$",
that
$$D(A^k) = \Big\{(u, v) : u \in H^{k+1}(\Omega),\ \Delta^j u = 0 \text{ on } \Gamma \text{ for }
  0 \le j \le [k/2];\ v \in H^k(\Omega),\ \Delta^j v = 0 \text{ on } \Gamma \text{ for } 0 \le j
  \le [(k+1)/2] - 1\Big\}.$$
The statement reads this with the domains $D_m$ of the Dirichlet Laplacian, and has two parts:

* $(u, v) \in D(A^k)$ if and only if $u \in D_{k+1}$ and $v \in D_k$, and
* if $(u, v) \in D(A^k)$, then $u$ is the function of an element of $H^{k+1}(\Omega)$ and $v$ is
  the function of an element of $H^k(\Omega)$, so $D(A^k) \subseteq H^{k+1}(\Omega) \times
  H^k(\Omega)$.

The domains are `Wave.MemLaplacianDomain`: $D_0 = L^2(\Omega)$, $D_1 = H^1_0(\Omega)$ and
$D_{m+2} = \{w \in D(-\Delta) : -\Delta w \in D_m\}$. This is the condition
"$w \in H^m(\Omega)$, $\Delta^j w = 0$ on $\Gamma$ for $2j < m$" of the source, with "$= 0$ on
$\Gamma$" read as membership of $H^1_0(\Omega)$ and each iterate in
$D(-\Delta) = H^2 \cap H^1_0$. The domain $D(A^k)$ is `Brezis.Chapter07.domainPow`. The first
part is `Wave.mem_operator_powGraph_iff`, on every open set; the second is
`Wave.MemLaplacianDomain.exists_sobolev`, Theorem 9.25 at every order. The operator $A$ of the
source is `Wave.operator Ω` on a $C^2$ domain (`Brezis.Chapter10.waveOperator_eq`). The
continuity of the injection is `Brezis.Chapter10.theorem_10_8_domain_norm`.

**Reading.** The boundary vanishing of successive Laplacians is represented by the recursive
 weak domains $D_m$. -/
theorem theorem_10_8_domain (hΩ : IsOfClassC ⊤ (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) (k : ℕ) :
    (∀ U : Wave.phaseSpace Ω, U ∈ domainPow (waveOperator Ω) k ↔
      Wave.MemLaplacianDomain Ω (k + 1) (SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume U.fst) ∧
        Wave.MemLaplacianDomain Ω k U.snd) ∧
    ∀ U : Wave.phaseSpace Ω, U ∈ domainPow (waveOperator Ω) k →
      (∃ w : sobolevSpaceHigher (d + 1) (k + 1) 2 Ω,
        fnL ℝ 𝔟 (k + 1) 2 Ω volume w = SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume U.fst) ∧
      ∃ z : sobolevSpaceHigher (d + 1) k 2 Ω, fnL ℝ 𝔟 k 2 Ω volume z = U.snd := by
  have hΩk : IsContDiffChartDomain (k + 1) (Ω : Set 𝔼) := hΩ.of_le (by simp)
  have hΩk' : IsContDiffChartDomain k (Ω : Set 𝔼) := hΩ.of_le (by simp)
  have e := waveOperator_eq (hΩ.of_le le_top) hΓ
  -- membership in `D(A^k)` is transported along `A = Wave.operator Ω` by `congrArg` (a `rw` of
  -- `e` in a goal mentioning `MemLaplacianDomain Ω (k + 1)` exhausts the budget)
  have hmem : ∀ U : Wave.phaseSpace Ω, U ∈ domainPow (waveOperator Ω) k ↔
      Wave.MemLaplacianDomain Ω (k + 1) (SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume U.fst) ∧
        Wave.MemLaplacianDomain Ω k U.snd := fun U ↦
    (Iff.of_eq (congrArg (fun A ↦ U ∈ domainPow A k) e)).trans
      (mem_domainPow_iff.trans (Wave.mem_operator_powGraph_iff k U))
  exact ⟨hmem, fun U hU ↦ ⟨((hmem U).1 hU).1.exists_sobolev (k + 1) hΩk hΓ,
    ((hmem U).1 hU).2.exists_sobolev k hΩk' hΓ⟩⟩

/-- **Proof of Theorem 10.8** in [brezis2011functional], "$D(A^k) \subset H^{k+1}(\Omega) \times
H^k(\Omega)$ with continuous injection". Let $\Omega \subset \mathbb{R}^N$ be open of class
$C^\infty$, with $N = d + 1$ and bounded boundary $\Gamma$, and let $k \in \mathbb{N}$. There is
$C \ge 0$ such that for every $x \in D(A^k)$ with components $(u, v)$, and for all
$w \in H^{k+1}(\Omega)$ and $z \in H^k(\Omega)$ with the same functions as $u$ and $v$,
$$\|w\|_{H^{k+1}} \le C \|x\|_{D(A^k)}, \qquad \|z\|_{H^k} \le C \|x\|_{D(A^k)}.$$

The norm of $D(A^k)$ is the graph norm $(\sum_{j \le k} |A^j U|^2)^{1/2}$ of the Hilbert space
`LinearPMap.PowDomain` of Chapter 7, and $(u, v)$ is the component $A^0 x$. The lifts exist by
`Brezis.Chapter10.theorem_10_8_domain`. The proof uses the backbone bounded linear map
`Wave.operator.powDomainToSobolevL`, from the closed graph theorem; the lifts are its two
components because `SobolevMultiIndex.fnL` is injective. -/
theorem theorem_10_8_domain_norm (hΩ : IsOfClassC ⊤ (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : (waveOperator Ω).PowDomain k)
      (w : sobolevSpaceHigher (d + 1) (k + 1) 2 Ω) (z : sobolevSpaceHigher (d + 1) k 2 Ω),
      fnL ℝ 𝔟 (k + 1) 2 Ω volume w = SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume
          (LinearPMap.PowDomain.applyL (waveOperator Ω) k 0 x).fst →
        fnL ℝ 𝔟 k 2 Ω volume z = (LinearPMap.PowDomain.applyL (waveOperator Ω) k 0 x).snd →
        ‖w‖ ≤ C * ‖x‖ ∧ ‖z‖ ≤ C * ‖x‖ := by
  have hΩk : IsContDiffChartDomain (k + 1) (Ω : Set 𝔼) := hΩ.of_le (by simp)
  -- the statement is transported from the backbone's operator along `A = Wave.operator Ω` with
  -- an explicit motive (`rw`, `simp only` and `generalize` all fail on the dependent binder
  -- `x : D(A^k)`: the first two exhaust the budget, the third cannot rewrite it)
  refine Eq.mpr (congrArg (fun A : Wave.phaseSpace Ω →ₗ.[ℝ] Wave.phaseSpace Ω ↦
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : A.PowDomain k)
      (w : sobolevSpaceHigher (d + 1) (k + 1) 2 Ω) (z : sobolevSpaceHigher (d + 1) k 2 Ω),
      fnL ℝ 𝔟 (k + 1) 2 Ω volume w = SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume
          (LinearPMap.PowDomain.applyL A k 0 x).fst →
        fnL ℝ 𝔟 k 2 Ω volume z = (LinearPMap.PowDomain.applyL A k 0 x).snd →
        ‖w‖ ≤ C * ‖x‖ ∧ ‖z‖ ≤ C * ‖x‖) (waveOperator_eq (hΩ.of_le le_top) hΓ)) ?_
  refine ⟨‖Wave.operator.powDomainToSobolevL k hΩk hΓ‖, norm_nonneg _, fun x w z hw hz ↦ ?_⟩
  -- the lifts are the components of `powDomainToSobolevL x` (`fnL` is injective; its
  -- injectivity is stated with the type spelled out, instance search on the implicit form being
  -- a minute)
  have hJ : Function.Injective (fnL ℝ 𝔟 (k + 1) 2 Ω volume) := fnL_injective
  have hJ' : Function.Injective (fnL ℝ 𝔟 k 2 Ω volume) := fnL_injective
  have e1 : w = (Wave.operator.powDomainToSobolevL k hΩk hΓ x).1 :=
    hJ (hw.trans (Wave.fnL_powDomainToSobolevL_fst k hΩk hΓ x).symm)
  have e2 : z = (Wave.operator.powDomainToSobolevL k hΩk hΓ x).2 :=
    hJ' (hz.trans (Wave.fnL_powDomainToSobolevL_snd k hΩk hΓ x).symm)
  rw [e1, e2]
  exact ⟨(norm_fst_le _).trans ((Wave.operator.powDomainToSobolevL k hΩk hΓ).le_opNorm x),
    (norm_snd_le _).trans ((Wave.operator.powDomainToSobolevL k hΩk hΓ).le_opNorm x)⟩

/-- **Theorem 10.8** of [brezis2011functional] (regularity). Let $\Omega \subset \mathbb{R}^N$ be
open of class $C^\infty$, with $N = d + 1$ and bounded boundary $\Gamma$, and let
$u_0, v_0 \in H^1_0(\Omega)$ satisfy the compatibility conditions
$$\Delta^j u_0 = 0 \text{ and } \Delta^j v_0 = 0 \text{ on } \Gamma \qquad \text{for every
  integer } j \ge 0,$$
read as $u_0 \in D_k$ and $v_0 \in D_k$ for every $k$. Let $u$ be the solution of (27), (28),
(29), (30) in the class (31). Then $u \in C^\infty(\overline{\Omega} \times [0, \infty))$: there
is a function $U : \mathbb{R}^N \times \mathbb{R} \to \mathbb{R}$ such that $U(\cdot, t) = u(t)$
almost everywhere on $\Omega$ for every $t \ge 0$, and $U$ is of class $C^\infty$ on
$\Omega \times (0, \infty)$ with every derivative extending continuously to the closure
$\overline{\Omega} \times [0, \infty)$.

**Reading.** The source also assumes $u_0, v_0 \in H^k(\Omega)$ for every $k$. The compatibility
conditions are read, as in the display of the proof (`Brezis.Chapter10.theorem_10_8_domain`),
through the domains $D_k$ of `Wave.MemLaplacianDomain`: the iterates
$u_0, -\Delta u_0, (-\Delta)^2 u_0, \dots$ lie in $D(-\Delta) = H^2 \cap H^1_0$, with
$(-\Delta)^j u_0 \in H^1_0(\Omega)$ for every $j$, and likewise for $v_0$. On a $C^\infty$
domain this implies $u_0, v_0 \in H^k(\Omega)$ for every $k$
(`Wave.MemLaplacianDomain.exists_sobolev`), so that hypothesis is not assumed separately.

The smoothness class is `ContDiffOnClosure`, as in `Brezis.Chapter10.theorem_10_2_c`. The proof
of the source: $U_0 = (u_0, v_0) \in D(A^k)$ for every $k$
(`Brezis.Chapter10.theorem_10_8_domain`), Theorem 7.5 gives
$U \in C^{k - j}([0, \infty); D(A^j))$ for $0 \le j \le k$, so $u \in C^{k - j}([0, \infty);
H^{j + 1}(\Omega))$ (`Brezis.Chapter10.theorem_10_8_domain_norm`), and Corollary 9.15 concludes.
The proof specializes `Wave.IsSolution.contDiffOnThrough_of_powDomain` and
`Wave.IsSolution.contDiffOnClosure_spaceTime`, through
`Bochner.contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough_Ici`.

**Reading.** Smoothness is stated on the open cylinder with continuous extensions of the
 derivatives to the closure. The representative is matched in $L^2$ even at time zero. -/
theorem theorem_10_8 (hΩ : IsOfClassC ⊤ (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼)))
    (hu₀ : ∀ k, Wave.MemLaplacianDomain Ω k (SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume u₀))
    (hv₀ : ∀ k, Wave.MemLaplacianDomain Ω k (SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume v₀))
    (hu : IsWaveSolution Ω u₀ v₀ u) :
    ∃ U : 𝔼 × ℝ → ℝ, (∀ t, 0 ≤ t → (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set 𝔼)] u t) ∧
      ContDiffOnClosure ℝ ∞ U ((Ω : Set 𝔼) ×ˢ Ioi 0) := by
  -- `(u₀, v₀) ∈ D(A^k)` for every `k`: the display of the proof, `D(A^k) = D_{k+1} × D_k`
  have hU₀ : ∀ k, ∃ x : (Wave.operator Ω).PowDomain k,
      LinearPMap.PowDomain.applyL (Wave.operator Ω) k 0 x
        = Wave.phaseSpace.mk Ω u₀ (SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume v₀) := fun k ↦
    (Wave.mem_operator_powGraph_iff k _).2 ⟨hu₀ (k + 1), hv₀ k⟩
  obtain ⟨U, hU, hc⟩ := hu.isSolution.contDiffOnClosure_spaceTime hU₀ hΩ hΓ
  exact ⟨U, fun t ht ↦ hU t ht, hc⟩

end Regular

section DAlembert

/-- The line $\mathbb{R}$ as $\mathbb{R}^1$. -/
local notation "𝔼₁" => EuclideanSpace ℝ (Fin 1)

/-! ### Remark 8: d'Alembert's formula is the solution on $\Omega = \mathbb{R}$ -/

/-- **Remark 8** in Chapter 10 of [brezis2011functional], d'Alembert's formula (40). Let
$\Omega = \mathbb{R}$, so $N = 1$, and let $u_0 \in H^2(\mathbb{R})$ and
$v_0 \in H^1(\mathbb{R})$, the data of Theorem 10.7 with $H^1_0(\mathbb{R}) = H^1(\mathbb{R})$
(Remark 17 of Chapter 9). Let $u$ be the curve in $L^2(\mathbb{R})$ of
$$u(x, t) = \frac12 \big(u_0(x + t) + u_0(x - t)\big) + \frac12 \int_{x - t}^{x + t} v_0(s) \,
  ds.$$
Then

* $u$ is a solution of (27)–(30) in the class (31) with the data $u_0$, $v_0$,
* every solution of (27)–(30) in the class (31) with these data agrees with $u$ on
  $[0, \infty)$, and
* for every $t$, $u(t)$ agrees almost everywhere with the function given by the formula above.

For $v_0 = 0$ the integral term vanishes. The curve $u$ is `Wave.dAlembertL2 u₀ v₀`, whose value is
`Wave.dAlembert` read on the line through the coordinate $x \mapsto x_0$ and
`Wave.lineEmbed : ℝ → ℝ¹`. The data are read in $H^1_0$ of the line through `Wave.toZeroTopL`.
The proof specializes `Wave.isSolution_dAlembert` and `Wave.IsSolution.eqOn_dAlembertL2`.

**Reading.** The d'Alembert formula is stated for $H^2$ initial displacement and $H^1$
 velocity, with equality almost everywhere on each time slice. -/
theorem remark_10_8 (u₀ : sobolevSpaceHigher 1 2 2 ⊤) (v₀ : hSpace 1 ⊤) :
    IsWaveSolution ⊤ (Wave.toZeroTopL (by simp) (Wave.dAlembertU₀ u₀))
        (Wave.toZeroTopL (by simp) v₀) (Wave.dAlembertL2 u₀ v₀) ∧
      (∀ v, IsWaveSolution ⊤ (Wave.toZeroTopL (by simp) (Wave.dAlembertU₀ u₀))
        (Wave.toZeroTopL (by simp) v₀) v → EqOn v (Wave.dAlembertL2 u₀ v₀) (Ici 0)) ∧
      ∀ t, Wave.dAlembertL2 u₀ v₀ t =ᵐ[volume.restrict ((⊤ : Opens 𝔼₁) : Set 𝔼₁)]
        fun x ↦ Wave.dAlembert (fun r ↦ fn u₀ (Wave.lineEmbed r))
          (fun r ↦ fn v₀ (Wave.lineEmbed r)) t (x 0) := by
  have hΩ : IsOfClassC 2 ((⊤ : Opens 𝔼₁) : Set 𝔼₁) :=
    ⟨isOpen_univ, fun _ h ↦ by simp [frontier_univ] at h⟩
  have hΓ : Bornology.IsBounded (frontier ((⊤ : Opens 𝔼₁) : Set 𝔼₁)) := by
    rw [Opens.coe_top, frontier_univ]
    exact Bornology.isBounded_empty
  have h := Wave.isSolution_dAlembert u₀ v₀
  refine ⟨(isWaveSolution_iff hΩ hΓ).2 h, fun v hv ↦ hv.isSolution.unique h, fun t ↦ ?_⟩
  exact Wave.coeFn_dAlembertL2_dAlembert u₀ v₀ t

end DAlembert

section Necessity

variable {N : ℕ}

/-- The space $\mathbb{R}^N$ of the source. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

variable {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-! ### Remark 10: the compatibility conditions are necessary -/

/-- **Remark 10** in Chapter 10 of [brezis2011functional]. The compatibility conditions of Theorem
10.8 are necessary and sufficient for a solution $u \in C^\infty(\overline{\Omega} \times [0,
\infty))$ of (27), (28), (29), (30); sufficiency is `Brezis.Chapter10.theorem_10_8`. This
declaration states necessity. Let $\Omega \subset \mathbb{R}^N$ be open with boundary $\Gamma$,
and let $u : \mathbb{R}^N \times \mathbb{R} \to \mathbb{R}$ be of class $C^\infty$ with
$$\partial_{tt} u = \Delta u \text{ in } Q = \Omega \times (0, \infty), \qquad u = 0 \text{ on }
  \Sigma = \Gamma \times (0, \infty).$$
Let $u_0 = u(\cdot, 0)$ and $v_0 = \partial_t u(\cdot, 0)$. Then $\Delta^j u_0 = 0$ and
$\Delta^j v_0 = 0$ on $\Gamma$ for every $j \in \mathbb{N}$.

**Reading.** The source considers $u \in C^\infty(\overline{\Omega} \times [0, \infty))$. As for
Remark 4 (`Brezis.Chapter10.remark_10_4`), the statement assumes that $u$ is of class $C^\infty$
on $\mathbb{R}^N \times \mathbb{R}$, so that the boundary values of $\Delta^j u(\cdot, 0)$ and
$\Delta^j \partial_t u(\cdot, 0)$ are meaningful as written.

The source says "the proof is the same as in Remark 4": all time derivatives of $u$ vanish on
$\Gamma \times [0, \infty)$ by continuity, $\partial_t^{2j} u = \Delta^j u$ and
$\partial_t^{2j+1} u = \Delta^j \partial_t u$ in $\overline{Q}$ by induction and continuity, and
the two are compared on $\Gamma \times \{0\}$. The proof specializes
`Wave.IsClassicalSolution.iteratedLaplacian_eq_zero_frontier`, on the cylinder
$\Omega \times (0, 1)$.

**Reading.** This states the necessity of compatibility for a globally smooth solution.
 Sufficiency under the Sobolev hypotheses is `Brezis.Chapter10.theorem_10_8`. -/
theorem remark_10_10 {u : 𝔼 × ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    (heq : ∀ x ∈ Ω, ∀ t, 0 < t →
      deriv (deriv fun s ↦ u (x, s)) t = Δ (fun y ↦ u (y, t)) x)
    (hΓ : ∀ x ∈ frontier (Ω : Set 𝔼), ∀ t, 0 < t → u (x, t) = 0) (j : ℕ) :
    ∀ x ∈ frontier (Ω : Set 𝔼), (Δ^[j] fun y ↦ u (y, 0)) x = 0 ∧
      (Δ^[j] fun y ↦ deriv (fun s ↦ u (y, s)) 0) x = 0 :=
  Wave.IsClassicalSolution.iteratedLaplacian_eq_zero_frontier Ω.isOpen one_pos
    ⟨fun p hp ↦ heq p.1 hp.1 p.2 hp.2.1⟩ hu (fun x hx t ht ↦ hΓ x hx t ht.1) j

end Necessity

end Brezis.Chapter10
