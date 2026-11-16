/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.PDE.Bochner.SpaceTime
import Numlib.Analysis.PDE.Heat
import Numlib.Analysis.PDE.Heat.Classical
import NumlibSurface.Brezis.Chapter07.Section04
import NumlibSurface.Brezis.Chapter09.Section08

/-!
# Brezis, Section 10.1: The heat equation: existence, uniqueness, and regularity

This module formalizes Section 10.1 of [brezis2011functional]. Let $\Omega \subset \mathbb{R}^N$ be
open with boundary $\Gamma$, let $Q = \Omega \times (0, \infty)$ and
$\Sigma = \Gamma \times (0, \infty)$. The heat equation is the problem
$$\partial_t u - \Delta u = 0 \text{ in } Q \quad (1), \qquad u = 0 \text{ on } \Sigma \quad (2),
  \qquad u(\cdot, 0) = u_0 \text{ in } \Omega \quad (3).$$
The source solves it with the Hille–Yosida theory of Chapter 7 in $H = L^2(\Omega)$, for the
operator $A u = -\Delta u$ with domain $D(A) = H^2(\Omega) \cap H^1_0(\Omega)$. Theorem 10.1 gives
existence and uniqueness of a solution in the class (4), the smoothing property (5) and the energy
identity (6). The display (7) describes the domains $D(A^\ell)$. Theorem 10.2 gives regularity up to
$t = 0$ for data in $H^1_0(\Omega)$, in $H^2(\Omega) \cap H^1_0(\Omega)$, and for data that satisfy
the compatibility conditions (8). Remark 1 treats the backward problem, Remark 3 the Fourier method,
and Remark 4 the necessity of the compatibility conditions.

The proofs specialize the backbone modules `Numlib.Analysis.PDE.DirichletLaplacian` (the operator
$A$), `Numlib.Analysis.PDE.Heat` (Section 10.1 in Bochner form),
`Numlib.Analysis.PDE.Bochner.SpaceTime` (the passage from curves to functions of $(x, t)$ behind
(5)) and `Numlib.Analysis.PDE.Heat.Classical` (Remark 4).

## Main definitions

* Proof of Theorem 10.1, the operator $A$, `Brezis.Chapter10.heatOperator`: $A u = -\Delta u$ on
  $D(A) = H^2(\Omega) \cap H^1_0(\Omega)$.
* Problem (1), (2), (3) in the class (4), `Brezis.Chapter10.IsHeatSolution`: $u \in C([0, \infty);
  L^2) \cap C((0, \infty); H^2 \cap H^1_0) \cap C^1((0, \infty); L^2)$ solves the heat equation with
  $u(0) = u_0$.
* Remark 1, the backward problem (9'), (10), (11), `Brezis.Chapter10.IsBackwardHeatSolution`: the
  same class on $(-\infty, T]$ for $\partial_t u = -\Delta u$ with $u(T) = u_T$.

## Main results

* Proof of Theorem 10.1, `Brezis.Chapter10.heatOperator_mem_domain_iff`:
  $D(A) = H^2(\Omega) \cap H^1_0(\Omega)$.
* Proof of Theorem 10.1, `Brezis.Chapter10.heatOperator_apply`:
  $A u = -\sum_i \partial^2 u / \partial x_i^2$.
* Proof of Theorem 10.1, claim (i), `Brezis.Chapter10.heatOperator_isMonotone`: $A$ is monotone on
  every open set.
* Proof of Theorem 10.1, claim (iii), `Brezis.Chapter10.heatOperator_isSymmetric`: $A$ is symmetric
  on every open set.
* Proof of Theorem 10.1, `Brezis.Chapter10.heatOperator_eq_dirichletLaplacian`: on a $C^2$ domain
  with bounded boundary, $A$ is the Dirichlet Laplacian with its weak domain.
* Proof of Theorem 10.1, claims (i)–(ii), `Brezis.Chapter10.heatOperator_isMaximalMonotone`: $A$ is
  maximal monotone.
* Proof of Theorem 10.1, claim (iii), `Brezis.Chapter10.heatOperator_isSelfAdjoint`: $A$ is
  self-adjoint.
* Footnote 3, `Brezis.Chapter10.sum_integral_partialDeriv_sq`: $|\nabla v|^2_{L^2} = \sum_i
  \int_\Omega |\partial v / \partial x_i|^2$ is the Dirichlet form.
* Theorem 10.1, `Brezis.Chapter10.theorem_10_1`: the problem (1), (2), (3) has a unique solution in
  the class (4).
* Theorem 10.1, `Brezis.Chapter10.theorem_10_1_smooth`: the smoothing (5), $u \in
  C^\infty(\overline{\Omega} \times [\varepsilon, \infty))$ for every $\varepsilon > 0$.
* Theorem 10.1, `Brezis.Chapter10.theorem_10_1_energy`: the energy identity (6).
* Theorem 10.1, `Brezis.Chapter10.theorem_10_1_memLp_gradient`: $\int_0^\infty |\nabla u(t)|^2 \, dt
  \le \frac12 |u_0|^2$ on every open set.
* Theorem 10.1, `Brezis.Chapter10.theorem_10_1_memLp`: $u \in L^2(0, \infty; H^1_0(\Omega))$ for
  bounded $\Omega$.
* Equation (7), `Brezis.Chapter10.equation_10_7`: $D(A^\ell) = \{u \in H^{2\ell}(\Omega) : u =
  \Delta u = \dots = \Delta^{\ell - 1} u = 0 \text{ on } \Gamma\}$ with continuous injection into
  $H^{2\ell}(\Omega)$.
* Theorem 10.2(a), `Brezis.Chapter10.theorem_10_2_a`: for $u_0 \in H^1_0(\Omega)$,
  $u \in C([0, \infty); H^1_0(\Omega))$, $\partial_t u \in L^2(0, \infty; L^2(\Omega))$ and the
  identity (11).
* Theorem 10.2(a), `Brezis.Chapter10.theorem_10_2_a_memLp`: $u \in L^2(0, \infty; H^2(\Omega))$ for
  bounded $\Omega$.
* Theorem 10.2(b), `Brezis.Chapter10.theorem_10_2_b`: for $u_0 \in H^2(\Omega) \cap H^1_0(\Omega)$,
  $u \in C([0, \infty); H^2(\Omega))$ and an energy identity for $\Delta u$.
* Theorem 10.2(b), `Brezis.Chapter10.theorem_10_2_b_memLp`: $u \in L^2(0, \infty; H^3(\Omega))$ and
  $\partial_t u \in L^2(0, \infty; H^1_0(\Omega))$ for bounded $\Omega$.
* Theorem 10.2(c), `Brezis.Chapter10.theorem_10_2_c`: under the compatibility conditions (8), $u \in
  C^\infty(\overline{\Omega} \times [0, \infty))$.
* Remark 1, `Brezis.Chapter10.remark_10_1`: the backward problem (9'), (10), (11) is well posed.
* Remark 1, `Brezis.Chapter10.remark_10_1_necessary`: the condition (12) is necessary for the
  backward problem (9), (10), (11).
* Remark 3, `Brezis.Chapter10.remark_10_3`: the Fourier method, the solution is the series (14) in
  the Dirichlet eigenbasis.
* Remark 4, `Brezis.Chapter10.remark_10_4`: the compatibility conditions (8) are necessary for a
  solution that is smooth up to $t = 0$.

## Conventions

* The source reads $u(x, t)$ as a function of $t$ with values in a space of functions of $x$: "when
  we write $u(t)$, we mean the element $x \mapsto u(x, t)$ of $H$". A solution is therefore a curve
  in $L^2(\Omega)$, of type `ℝ → Lp ℝ 2 (volume.restrict Ω)`.
* The classes $C^k(I; V)$ for $V = H^2(\Omega)$ or $H^1_0(\Omega)$ are
  `Bochner.ContDiffOnThrough J k u I`: a $C^k$ lift of $u$ through the inclusion
  $J : V \to L^2(\Omega)$. The class $L^2(I; V)$ is `Bochner.MemLpThrough J 2 u I`. The class
  $C^\infty(\overline{\Omega} \times [\varepsilon, \infty))$ is
  `ContDiffOnClosure ℝ ∞ U (Ω ×ˢ Ioi ε)` for a function $U$ of $(x, t)$ that represents the curve,
  in the sense of footnote 16 of Chapter 9 for $C^k$ up to the boundary.
* The spaces $H^k(\Omega)$, $H^1(\Omega)$ and $H^1_0(\Omega)$ of Sections 9.1 and 9.4 are
  `Brezis.Chapter09.sobolevSpaceHigher N k 2 Ω`, `Brezis.Chapter09.hSpace N Ω` and
  `Brezis.Chapter09.hZeroSpace N Ω`. A function in $L^2(\Omega)$ "lies in $H^k(\Omega)$" when it is
  the function `SobolevMultiIndex.fnL w` of some $w$ in $H^k(\Omega)$. In the same way,
  "$u_0 \in H^1_0(\Omega)$" means that $u_0$ is the function of some $v_0$ in $H^1_0(\Omega)$.
* The quantity $|\nabla u(t)|^2_{L^2} = \sum_i \int_\Omega |\partial_i u(x, t)|^2$ of footnote 3 is
  written for an $H^1_0$-lift of $u(t)$ with the weak partial derivatives
  `Brezis.Chapter09.partialDeriv` of Section 9.1.
* The boundary conditions "$\Delta^j u = 0$ on $\Gamma$" of (7) and (8) are read without a trace, as
  membership of $H^1_0(\Omega)$ (the reading of Theorem 9.17), through `IsDirichletLaplacianChain`.
* The standing hypothesis of the chapter, "$\Omega$ of class $C^\infty$ with $\Gamma$ bounded", is
  `Brezis.Chapter09.IsOfClassC ⊤ Ω` together with `Bornology.IsBounded (frontier Ω)`, with
  $N = d + 1$, because the chart definition of Section 9.2 needs a boundary variable.

## Implementation notes

* The operator $A$ of the source is `Brezis.Chapter10.heatOperator Ω`: the backbone Dirichlet
  Laplacian `dirichletLaplacian Ω`, whose domain is the weak domain $\{u \in H^1_0(\Omega) : \Delta
  u \in L^2(\Omega)\}$, restricted to the functions of elements of $H^2(\Omega)$. On a domain of
  class $C^2$ with bounded boundary the two operators coincide
  (`Brezis.Chapter10.heatOperator_eq_dirichletLaplacian`, by Theorem 9.25). This identification is
  how every backbone statement about `dirichletLaplacian` is read for the operator $A$ of the
  source.
* The class (4) implies the backbone class `Heat.IsSolution` on every open set, and the two classes
  agree on a $C^2$ domain with bounded boundary (`Brezis.Chapter10.isHeatSolution_iff`).

## Deviations from the source

* **Standing hypothesis of Chapter 10** (generalization). The source assumes $\Omega$ of class
  $C^\infty$ with $\Gamma$ bounded throughout. The library assumes it only where a proof uses it, in
  the form needed: results whose proofs hold on every open set (the monotonicity and symmetry of
  $A$, the energy identities (6) and (11), Theorem 10.2(a) and Remark 3) carry no regularity
  hypothesis, and several results assume only class $C^2$ or $C^3$. The source itself notes that
  "this assumption may be considerably weakened if we are interested only in weak solutions". See
  `Brezis.Chapter10.theorem_10_1_energy` and `Brezis.Chapter10.theorem_10_2_b`.
* **Theorem 10.1, $u \in L^2(0, \infty; H^1_0(\Omega))$** (correction). The clause is false on
  unbounded $\Omega$ ($\Omega = \mathbb{R}$ with a Gaussian datum). The library proves
  $\int_0^\infty |\nabla u(t)|^2 \, dt \le \frac12 |u_0|^2$ on every open set and the membership for
  bounded $\Omega$. See `Brezis.Chapter10.theorem_10_1_memLp_gradient` and
  `Brezis.Chapter10.theorem_10_1_memLp`.
* **Theorem 10.2(a), $u \in L^2(0, \infty; H^2(\Omega))$** (correction). The clause is false on
  unbounded $\Omega$. The library proves it for bounded $\Omega$. See
  `Brezis.Chapter10.theorem_10_2_a_memLp`.
* **Theorem 10.2(b), $u \in L^2(0, \infty; H^3(\Omega))$ and
  $\partial_t u \in L^2(0, \infty; H^1_0(\Omega))$** (correction). The clauses are false on
  unbounded $\Omega$. The library proves them for bounded $\Omega$. See
  `Brezis.Chapter10.theorem_10_2_b_memLp`.
* **Remark 4** (reading). The boundary values of $\Delta^j u(\cdot, 0)$ must have a meaning. The
  library states the remark for $u$ of class $C^\infty$ on $\mathbb{R}^N \times \mathbb{R}$. See
  `Brezis.Chapter10.remark_10_4`.

## Not formalized

* **Remark 1, nonexistence under (12).** The claim of the source that the backward problem (9),
  (10), (11) need not have a solution even when (12) holds is a counterexample claim.
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

/-! ### The operator $A$ of the proof of Theorem 10.1 -/

variable (Ω) in
/-- **Proof of Theorem 10.1** in [brezis2011functional], the operator $A$. Let
$\Omega \subset \mathbb{R}^N$ be open. The operator
$A : D(A) \subset L^2(\Omega) \to L^2(\Omega)$ is defined by
$D(A) = H^2(\Omega) \cap H^1_0(\Omega)$ and $A u = -\Delta u$, "the boundary condition (2) being
incorporated in the definition of the domain".

The definition restricts the backbone Dirichlet Laplacian `dirichletLaplacian Ω`, whose domain
is the weak domain $\{u \in H^1_0(\Omega) : \Delta u \in L^2(\Omega)\}$, to the submodule of
$L^2(\Omega)$ functions of elements of $H^2(\Omega)$, with `LinearPMap.domRestrict`. The weak
domain contains $H^2(\Omega) \cap H^1_0(\Omega)$ on every open set
(`mem_dirichletLaplacianDomain_of_sobolev_two`). Therefore the domain is
$H^2(\Omega) \cap H^1_0(\Omega)$ (`Brezis.Chapter10.heatOperator_mem_domain_iff`) and
$A u = -\sum_i \partial_{ii} u$ (`Brezis.Chapter10.heatOperator_apply`). -/
noncomputable def heatOperator :
    Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)) →ₗ.[ℝ] Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)) :=
  (dirichletLaplacian Ω).domRestrict (LinearMap.range (fnL ℝ 𝔟 2 2 Ω volume).toLinearMap)

/-- The domain $D(A)$ of the operator $A$ of Theorem 10.1 is contained in the weak domain of the
Dirichlet Laplacian `dirichletLaplacian Ω`. -/
theorem heatOperator_domain_le : (heatOperator Ω).domain ≤ (dirichletLaplacian Ω).domain :=
  inf_le_right

/-- **Proof of Theorem 10.1** in [brezis2011functional], $D(A) = H^2(\Omega) \cap H^1_0(\Omega)$.
Let $\Omega \subset \mathbb{R}^N$ be open and $f \in L^2(\Omega)$. Then $f \in D(A)$ if and only
if $f$ is the function of an element of $H^2(\Omega)$ and the function of an element of
$H^1_0(\Omega)$. -/
theorem heatOperator_mem_domain_iff {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))} :
    f ∈ (heatOperator Ω).domain ↔
      (∃ w : sobolevSpaceHigher N 2 2 Ω, fnL ℝ 𝔟 2 2 Ω volume w = f) ∧
        ∃ v : hSpace N Ω, v ∈ hZeroSpace N Ω ∧ fnL ℝ 𝔟 1 2 Ω volume v = f := by
  change f ∈ LinearMap.range (fnL ℝ 𝔟 2 2 Ω volume).toLinearMap ⊓ dirichletLaplacianDomain Ω ↔ _
  rw [Submodule.mem_inf, LinearMap.mem_range]
  exact ⟨fun ⟨hw, hf⟩ ↦ ⟨hw, dirichletLaplacian_exists_lift ⟨f, hf⟩⟩,
    fun ⟨hw, hv⟩ ↦ ⟨hw, mem_dirichletLaplacianDomain_of_exists_sobolev_two hw hv⟩⟩

/-- For $f \in D(A)$, the value $A f$ of the operator $A$ of Theorem 10.1 is the value of the
Dirichlet Laplacian `dirichletLaplacian Ω` at $f$. -/
theorem heatOperator_apply_eq (f : (heatOperator Ω).domain) :
    heatOperator Ω f = dirichletLaplacian Ω ⟨f, heatOperator_domain_le f.2⟩ :=
  LinearPMap.domRestrict_apply rfl

/-- **Proof of Theorem 10.1** in [brezis2011functional], $A u = -\Delta u$. Let
$\Omega \subset \mathbb{R}^N$ be open, let $f \in D(A)$, and let $w \in H^2(\Omega)$ have the
function $f$. Then
$$A f = -\sum_{i} \frac{\partial^2 w}{\partial x_i^2},$$
where $\partial^2 w / \partial x_i^2$ is the weak derivative of $w$ at the multi-index $2 e_i$. -/
theorem heatOperator_apply (f : (heatOperator Ω).domain) (w : sobolevSpaceHigher N 2 2 Ω)
    (hw : fnL ℝ 𝔟 2 2 Ω volume w = f) :
    heatOperator Ω f = -∑ i, weakDeriv w (MultiIndexLE.addSingle i (MultiIndexLE.single i)) := by
  rw [heatOperator_apply_eq, ← sobolevLaplacianL_apply]
  exact dirichletLaplacian_apply_eq_neg_sobolevLaplacianL w _ hw

/-- **Proof of Theorem 10.1** in [brezis2011functional], claim (i): $A$ is monotone. Let
$\Omega \subset \mathbb{R}^N$ be open. Then $(A u, u)_{L^2} = \int_\Omega |\nabla u|^2 \ge 0$
for every $u \in D(A)$.

The statement holds on every open set. Monotonicity is `Brezis.Chapter07.IsMonotone`. -/
theorem heatOperator_isMonotone : Brezis.Chapter07.IsMonotone (heatOperator Ω) := fun f ↦ by
  rw [heatOperator_apply_eq]
  exact dirichletLaplacian_inner_self_nonneg _

/-- **Proof of Theorem 10.1** in [brezis2011functional], claim (iii): $A$ is symmetric. Let
$\Omega \subset \mathbb{R}^N$ be open. Then
$$(A u, v)_{L^2} = \int_\Omega \nabla u \cdot \nabla v = (u, A v)_{L^2} \qquad \text{for all }
  u, v \in D(A).$$

The statement holds on every open set. Symmetry is `Brezis.Chapter07.IsSymmetricOperator`. -/
theorem heatOperator_isSymmetric : IsSymmetricOperator (heatOperator Ω) := fun f g ↦ by
  rw [heatOperator_apply_eq, heatOperator_apply_eq]
  exact dirichletLaplacian_isFormalAdjoint
    (⟨f, heatOperator_domain_le f.2⟩ : (dirichletLaplacian Ω).domain)
    ⟨g, heatOperator_domain_le g.2⟩

/-! ### The problem (1), (2), (3) in the class (4) -/

variable (Ω) in
/-- **Theorem 10.1** of [brezis2011functional], the problem (1), (2), (3) in the class (4). Let
$\Omega \subset \mathbb{R}^N$ be open and $u_0 \in L^2(\Omega)$. A curve
$u : \mathbb{R} \to L^2(\Omega)$ is a **solution of the heat equation** with initial datum $u_0$
if

* $u \in C([0, \infty); L^2(\Omega))$,
* $u(t) \in D(A) = H^2(\Omega) \cap H^1_0(\Omega)$ for $t > 0$, which is the boundary condition
  (2), and $u \in C((0, \infty); H^2(\Omega))$,
* $u \in C^1((0, \infty); L^2(\Omega))$,
* $\partial_t u(t) = \Delta u(t) = -A u(t)$ in $L^2(\Omega)$ for $t > 0$, which is the heat
  equation (1), and
* $u(0) = u_0$, which is the initial condition (3).

The curve $u$ is the function $u(x, t)$ of the source, read as $t \mapsto u(\cdot, t)$. Its
values at negative times are not constrained. -/
structure IsHeatSolution (u₀ : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)))
    (u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) : Prop where
  /-- $u \in C([0, \infty); L^2(\Omega))$. -/
  continuousOn : ContinuousOn u (Ici 0)
  /-- $u(t) \in H^2(\Omega) \cap H^1_0(\Omega)$ for $t > 0$: the boundary condition (2). -/
  mem_domain : ∀ t, 0 < t → u t ∈ (heatOperator Ω).domain
  /-- $u \in C((0, \infty); H^2(\Omega))$. -/
  contDiffOnThrough : Bochner.ContDiffOnThrough (fnL ℝ 𝔟 2 2 Ω volume) 0 u (Ioi 0)
  /-- $u \in C^1((0, \infty); L^2(\Omega))$. -/
  contDiffOn : ContDiffOn ℝ 1 u (Ioi 0)
  /-- The heat equation (1): $\partial_t u(t) = \Delta u(t) = -A u(t)$ for $t > 0$. -/
  hasDerivAt : ∀ t (ht : 0 < t), HasDerivAt u (-(heatOperator Ω ⟨u t, mem_domain t ht⟩)) t
  /-- The initial condition (3): $u(0) = u_0$. -/
  apply_zero : u 0 = u₀

variable {u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-- A solution of the heat equation in the class (4) of Theorem 10.1 is a solution in the backbone
class `Heat.IsSolution`, the class of Theorem 7.7 for the Dirichlet Laplacian with its weak
domain. This holds on every open set $\Omega$, because $D(A) \subseteq \{u \in H^1_0(\Omega) :
\Delta u \in L^2(\Omega)\}$ and $A$ agrees with the Dirichlet Laplacian on $D(A)$. -/
theorem IsHeatSolution.isSolution (h : IsHeatSolution Ω u₀ u) : Heat.IsSolution Ω u₀ u where
  toIsSolutionOn :=
    { apply_zero := h.apply_zero
      mem_domain := fun t ht ↦ heatOperator_domain_le (h.mem_domain t ht)
      hasDerivWithinAt := fun t ht ↦
        ((h.hasDerivAt t ht).congr_deriv (congrArg Neg.neg (heatOperator_apply_eq _)))
          |>.hasDerivWithinAt }
  continuousOn := h.continuousOn
  contDiffOn := h.contDiffOn

/-- **Footnote 3** in Chapter 10 of [brezis2011functional]. Let $\Omega \subset \mathbb{R}^N$ be
open and $v \in H^1(\Omega)$. Then
$$|\nabla v|^2_{L^2(\Omega)} = \sum_i \int_\Omega \left|\frac{\partial v}{\partial
  x_i}\right|^2$$
is the Dirichlet form $\int_\Omega |\nabla v|^2$ of the backbone,
`Elliptic.dirichletForm Ω v v`. -/
theorem sum_integral_partialDeriv_sq (v : hSpace N Ω) :
    ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv v i x ^ 2 = Elliptic.dirichletForm Ω v v := by
  rw [Elliptic.dirichletForm_apply_inner]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [MeasureTheory.L2.inner_eq_integral_mul]
  exact integral_congr_ae (Eventually.of_forall fun x ↦ sq _)

/-- Let $u$ be a solution of the heat equation in the class (4) of Theorem 10.1, let $t > 0$, and
let $v \in H^1_0(\Omega)$ have the function $u(t)$. Then $(A u(t), u(t))_{L^2} = \sum_i
\int_\Omega |\partial v / \partial x_i|^2$, where $A$ is the Dirichlet Laplacian
`dirichletLaplacian Ω`. Thus the gradient norm of $u(t)$ does not depend on the choice of the
$H^1_0$-lift. -/
theorem IsHeatSolution.inner_apply_self_eq (h : IsHeatSolution Ω u₀ u) {t : ℝ} (ht : 0 < t)
    {v : hSpace N Ω} (hv : v ∈ hZeroSpace N Ω) (hvt : fnL ℝ 𝔟 1 2 Ω volume v = u t) :
    ⟪dirichletLaplacian Ω ⟨u t, h.isSolution.mem_domain ht⟩, u t⟫_ℝ
      = ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv v i x ^ 2 := by
  rw [sum_integral_partialDeriv_sq]
  exact dirichletLaplacian_inner_self_eq_dirichletForm _ hv hvt

/-! ### Theorem 10.1, the energy identity (6) -/

/-- **Theorem 10.1** of [brezis2011functional], the energy identity (6). Let
$\Omega \subset \mathbb{R}^N$ be open, let $u_0 \in L^2(\Omega)$, and let $u$ be a solution of
(1), (2), (3) in the class (4). Let $g : \mathbb{R} \to \mathbb{R}$ be a function with $g(t) =
|\nabla u(t)|^2_{L^2(\Omega)} = \sum_i \int_\Omega |\partial_i u(x, t)|^2 \, dx$ for $t > 0$,
computed on an $H^1_0$-lift of $u(t)$ as in footnote 3. Then for every $T > 0$ the function $g$
is integrable on $(0, T]$ and
$$\frac12 |u(T)|^2_{L^2} + \int_0^T |\nabla u(t)|^2_{L^2} \, dt = \frac12 |u_0|^2_{L^2}.$$

The statement holds on every open set. The argument of the source, with
$\varphi(t) = \frac12 |u(t)|^2$, $\varphi' = (u, \Delta u) = -|\nabla u|^2$ on $(0, \infty)$ and
$\varepsilon \to 0$, is the backbone theorem `Heat.IsSolution.energy`. -/
theorem theorem_10_1_energy (hu : IsHeatSolution Ω u₀ u) {g : ℝ → ℝ}
    (hg : ∀ t, 0 < t → ∃ v : hSpace N Ω, v ∈ hZeroSpace N Ω ∧ fnL ℝ 𝔟 1 2 Ω volume v = u t ∧
      g t = ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv v i x ^ 2)
    {T : ℝ} (hT : 0 < T) :
    IntegrableOn g (Ioc 0 T) ∧
      1 / 2 * ‖u T‖ ^ 2 + ∫ t in (0 : ℝ)..T, g t = 1 / 2 * ‖u₀‖ ^ 2 :=
  hu.isSolution.energy (fun t ht ↦ by
    obtain ⟨v, hv, hvt, hgt⟩ := hg t ht
    rw [hgt, hu.inner_apply_self_eq ht hv hvt]) hT

/-- **Theorem 10.1** of [brezis2011functional], the gradient part of
"$u \in L^2(0, \infty; H^1_0(\Omega))$". Let $\Omega \subset \mathbb{R}^N$ be open, let
$u_0 \in L^2(\Omega)$, let $u$ be a solution of (1), (2), (3) in the class (4), and let
$g(t) = |\nabla u(t)|^2_{L^2(\Omega)}$ for $t > 0$, as in
`Brezis.Chapter10.theorem_10_1_energy`. Then $g$ is integrable on $(0, \infty)$ and
$$\int_0^\infty |\nabla u(t)|^2_{L^2} \, dt \le \frac12 |u_0|^2_{L^2}.$$

**Correction.** The source states $u \in L^2(0, \infty; H^1_0(\Omega))$ for every $\Omega$. This
is false on unbounded domains, where $\int_0^\infty |u(t)|^2_{L^2} \, dt$ need not be finite,
for example for $\Omega = \mathbb{R}$ with a Gaussian datum. What the proof of the source
establishes on every open set is this gradient bound. The membership itself holds for bounded
$\Omega$ (`Brezis.Chapter10.theorem_10_1_memLp`).

The bound follows from (6) for every $T$, since $|u(T)|^2 \ge 0$. -/
theorem theorem_10_1_memLp_gradient (hu : IsHeatSolution Ω u₀ u) {g : ℝ → ℝ}
    (hg : ∀ t, 0 < t → ∃ v : hSpace N Ω, v ∈ hZeroSpace N Ω ∧ fnL ℝ 𝔟 1 2 Ω volume v = u t ∧
      g t = ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv v i x ^ 2) :
    IntegrableOn g (Ioi 0) ∧ ∫ t in Ioi 0, g t ≤ 1 / 2 * ‖u₀‖ ^ 2 :=
  hu.isSolution.integral_inner_apply_le fun t ht ↦ by
    obtain ⟨v, hv, hvt, hgt⟩ := hg t ht
    rw [hgt, hu.inner_apply_self_eq ht hv hvt]

/-! ### Theorem 10.2(a) -/

/-- **Theorem 10.2(a)** of [brezis2011functional], the clauses that hold on every open set. Let
$\Omega \subset \mathbb{R}^N$ be open, let $u_0 \in H^1_0(\Omega)$, that is, $u_0$ is the
function of some $v_0 \in H^1_0(\Omega)$, and let $u$ be the solution of (1), (2), (3) in the
class (4). Then

* $u \in C([0, \infty); H^1_0(\Omega))$,
* $\partial_t u \in L^2(0, \infty; L^2(\Omega))$, and
* the identity (11) holds: for every $T > 0$ and every $v \in H^1_0(\Omega)$ with function
  $u(T)$,
$$\int_0^T |\partial_t u(t)|^2_{L^2} \, dt + \frac12 |\nabla v|^2_{L^2} = \frac12 |\nabla
  v_0|^2_{L^2},$$
where $|\nabla v|^2_{L^2} = \sum_i \int_\Omega |\partial v / \partial x_i|^2$ as in footnote 3.

The proof of the source uses the operator $A_1$ in $H_1 = H^1_0(\Omega)$ with the scalar product
$\int_\Omega \nabla u \cdot \nabla v + \int_\Omega uv$ (the backbone operator
`dirichletLaplacianH10`, maximal monotone and symmetric on every open set), Theorem 7.7 for
$A_1$, uniqueness, and $\varphi(t) = \frac12 |\nabla u(t)|^2$ with
$\varphi' = -|\partial_t u|^2$. This is the backbone theorems
`Heat.IsSolution.contDiffOnThrough_sobolevZero_of_mem`, `Heat.IsSolution.memLp_deriv` and
`Heat.IsSolution.energy_sobolevZero`. The clause $u \in L^2(0, \infty; H^2(\Omega))$ is
`Brezis.Chapter10.theorem_10_2_a_memLp`, for bounded $\Omega$. -/
theorem theorem_10_2_a {v₀ : hZeroSpace N Ω}
    (hu : IsHeatSolution Ω (SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume v₀) u) :
    Bochner.ContDiffOnThrough (SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume) 0 u (Ici 0) ∧
      MemLp (deriv u) 2 (volume.restrict (Ioi 0)) ∧
      ∀ T, 0 < T → ∀ v : hSpace N Ω, v ∈ hZeroSpace N Ω → fnL ℝ 𝔟 1 2 Ω volume v = u T →
        (∫ t in (0 : ℝ)..T, ‖deriv u t‖ ^ 2)
            + 1 / 2 * ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv v i x ^ 2
          = 1 / 2 * ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv (v₀ : hSpace N Ω) i x ^ 2 := by
  refine ⟨hu.isSolution.contDiffOnThrough_sobolevZero_of_mem rfl,
    (hu.isSolution.memLp_deriv rfl).1, fun T hT v hv hvT ↦ ?_⟩
  have e := (hu.isSolution.energy_sobolevZero rfl hT).2
  rw [hu.inner_apply_self_eq hT hv hvT, ← sum_integral_partialDeriv_sq] at e
  exact e

/-! ### Remark 1: the backward problem (9'), (10), (11) -/

variable (Ω) in
/-- **Remark 1** in Chapter 10 of [brezis2011functional], the backward problem (9'), (10), (11). Let
$\Omega \subset \mathbb{R}^N$ be open, $T \in \mathbb{R}$ and $u_T \in L^2(\Omega)$. The
backward problem is $-\partial_t u - \Delta u = 0$ in $\Omega \times (-\infty, T)$, $u = 0$ on
$\Gamma \times (-\infty, T)$, $u(T) = u_T$. A curve $u : \mathbb{R} \to L^2(\Omega)$ is a
**solution of the backward problem** if

* $u \in C((-\infty, T]; L^2(\Omega))$,
* $u(t) \in H^2(\Omega) \cap H^1_0(\Omega)$ for $t < T$ and
  $u \in C((-\infty, T); H^2(\Omega))$,
* $u \in C^1((-\infty, T); L^2(\Omega))$,
* $\partial_t u(t) = -\Delta u(t) = A u(t)$ for $t < T$, and
* $u(T) = u_T$.

This is the class of Theorem 10.1 transported by $t \mapsto T - t$. -/
structure IsBackwardHeatSolution (T : ℝ) (uT : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)))
    (u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) : Prop where
  /-- $u \in C((-\infty, T]; L^2(\Omega))$. -/
  continuousOn : ContinuousOn u (Iic T)
  /-- $u(t) \in H^2(\Omega) \cap H^1_0(\Omega)$ for $t < T$: the boundary condition (10). -/
  mem_domain : ∀ t, t < T → u t ∈ (heatOperator Ω).domain
  /-- $u \in C((-\infty, T); H^2(\Omega))$. -/
  contDiffOnThrough : Bochner.ContDiffOnThrough (fnL ℝ 𝔟 2 2 Ω volume) 0 u (Iio T)
  /-- $u \in C^1((-\infty, T); L^2(\Omega))$. -/
  contDiffOn : ContDiffOn ℝ 1 u (Iio T)
  /-- The equation (9'): $\partial_t u(t) = -\Delta u(t) = A u(t)$ for $t < T$. -/
  hasDerivAt : ∀ t (ht : t < T), HasDerivAt u (heatOperator Ω ⟨u t, mem_domain t ht⟩) t
  /-- The final condition (11): $u(T) = u_T$. -/
  apply_eq : u T = uT

/-- A solution of the backward problem of Remark 1 in Chapter 10 is a solution in the backbone class
`Heat.IsBackwardSolution`. This holds on every open set $\Omega$. -/
theorem IsBackwardHeatSolution.isBackwardSolution {T : ℝ}
    {uT : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))} (h : IsBackwardHeatSolution Ω T uT u) :
    Heat.IsBackwardSolution Ω T uT u where
  apply_eq := h.apply_eq
  mem_domain := fun t ht ↦ heatOperator_domain_le (h.mem_domain t ht)
  hasDerivAt := fun t ht ↦ (h.hasDerivAt t ht).congr_deriv (heatOperator_apply_eq _)
  continuousOn := h.continuousOn
  contDiffOn := h.contDiffOn

/-! ### Remark 4: the compatibility conditions are necessary -/

/-- **Remark 4** in Chapter 10 of [brezis2011functional]. The compatibility conditions (8) are
necessary for a solution of (1), (2), (3) that is smooth up to $t = 0$. Let
$\Omega \subset \mathbb{R}^N$ be open with boundary $\Gamma$, and let $u : \mathbb{R}^N \times
\mathbb{R} \to \mathbb{R}$ be of class $C^\infty$ with
$$\partial_t u = \Delta u \text{ in } Q = \Omega \times (0, \infty), \qquad u = 0 \text{ on }
  \Sigma = \Gamma \times (0, \infty).$$
Then $\Delta^j u(\cdot, 0) = 0$ on $\Gamma$ for every $j \in \mathbb{N}$.

**Reading.** The source considers $u \in C^\infty(\overline{\Omega} \times [0, \infty))$. The
statement assumes that $u$ is of class $C^\infty$ on $\mathbb{R}^N \times \mathbb{R}$, so that
the boundary values of $\Delta^j u(\cdot, 0)$ are meaningful as written.

The Laplacian $\Delta$ acts on the variable $x$ and is Mathlib's, and $\partial_t u$ is the
derivative of $s \mapsto u(x, s)$. The argument: $\partial_t^j u = 0$ on
$\Gamma \times [0, \infty)$ by continuity (15), $\partial_t^j u = \Delta^j u$ in $\overline{Q}$
by induction and continuity (16), and the two are compared on $\Gamma \times \{0\}$. The proof
specializes `Heat.IsClassicalSolution.iteratedLaplacian_eq_zero_frontier`, with diffusivity $1$,
on the cylinder $\Omega \times (0, 1)$. -/
theorem remark_10_4 {u : 𝔼 × ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    (heq : ∀ x ∈ Ω, ∀ t, 0 < t → deriv (fun s ↦ u (x, s)) t = Δ (fun y ↦ u (y, t)) x)
    (hΓ : ∀ x ∈ frontier (Ω : Set 𝔼), ∀ t, 0 < t → u (x, t) = 0) (j : ℕ) :
    ∀ x ∈ frontier (Ω : Set 𝔼), (Δ^[j] fun y ↦ u (y, 0)) x = 0 := by
  have hcl : Heat.IsClassicalSolution 1 (Ω : Set 𝔼) 1 u :=
    { continuousOn := hu.continuous.continuousOn
      differentiableAt_snd := fun x _ t _ ↦
        ((hu.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)).differentiableAt
      contDiffAt_fst := fun x _ t _ ↦
        ((hu.comp (contDiff_id.prodMk contDiff_const)).of_le (by simp)).contDiffAt
      deriv_eq_laplacian := fun x hx t ht ↦ by rw [one_mul]; exact heq x hx t ht.1 }
  exact Heat.IsClassicalSolution.iteratedLaplacian_eq_zero_frontier Ω.isOpen one_ne_zero
    one_pos hcl hu (fun x hx t ht ↦ hΓ x hx t ht.1) j

end General

section Regular

variable {d : ℕ}

/-- The space $\mathbb{R}^N$ of the source, with $N = d + 1$. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

/-- The standard basis of $\mathbb{R}^N$. -/
local notation "𝔟" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin (d + 1)) ℝ)

variable {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-! ### The operator $A$ on a regular domain: claims (i)–(iii) of the proof of Theorem 10.1 -/

/-- **Proof of Theorem 10.1** in [brezis2011functional], claim (ii): $A$ is the Dirichlet Laplacian.
Let $\Omega \subset \mathbb{R}^N$ be open of class $C^2$, with $N = d + 1$ and bounded boundary
$\Gamma$. Then the operator $A$ equals the Dirichlet Laplacian `dirichletLaplacian Ω`: the weak
domain $\{u \in H^1_0(\Omega) : \Delta u \in L^2(\Omega)\}$ is $H^2(\Omega) \cap H^1_0(\Omega)$.

The proof applies Theorem 9.25 to $u - \Delta u \in L^2(\Omega)$, as in step (ii) of the proof
of the source; it specializes `dirichletLaplacianDomain_eq_of_isContDiffChartDomain`. Under the
standing $C^\infty$ hypothesis of the chapter, this identification lets every backbone statement
about `dirichletLaplacian` be read for the operator $A$ of the source. -/
theorem heatOperator_eq_dirichletLaplacian (hΩ : IsOfClassC 2 (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) :
    heatOperator Ω = dirichletLaplacian Ω := by
  refine LinearPMap.eq_of_le_of_domain_eq LinearPMap.domRestrict_le ?_
  ext f
  rw [heatOperator_mem_domain_iff]
  exact ((dirichletLaplacianDomain_eq_of_isContDiffChartDomain hΩ hΓ).1 f).symm

/-- **Proof of Theorem 10.1** in [brezis2011functional], claims (i)–(ii): $A$ is maximal monotone.
Let $\Omega \subset \mathbb{R}^N$ be open of class $C^2$, with $N = d + 1$ and bounded boundary
$\Gamma$. Then $A$ is maximal monotone: $(A u, u) = \int_\Omega |\nabla u|^2 \ge 0$, and
$R(I + A) = L^2(\Omega)$, since for every $f \in L^2(\Omega)$ the equation $u - \Delta u = f$
has a solution $u \in H^2(\Omega) \cap H^1_0(\Omega)$ (Theorem 9.25).

Maximal monotonicity is `Brezis.Chapter07.IsMaximalMonotone`. The proof specializes
`dirichletLaplacian_isMaximalMonotone` through
`Brezis.Chapter10.heatOperator_eq_dirichletLaplacian`. -/
theorem heatOperator_isMaximalMonotone (hΩ : IsOfClassC 2 (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) :
    Brezis.Chapter07.IsMaximalMonotone (heatOperator Ω) := by
  rw [heatOperator_eq_dirichletLaplacian hΩ hΓ, isMaximalMonotone_iff]
  exact dirichletLaplacian_isMaximalMonotone

/-- **Proof of Theorem 10.1** in [brezis2011functional], claim (iii): $A$ is self-adjoint. Let
$\Omega \subset \mathbb{R}^N$ be open of class $C^2$, with $N = d + 1$ and bounded boundary
$\Gamma$. Then $A$ is self-adjoint.

Self-adjointness is `Brezis.Chapter07.IsSelfAdjointOperator`. The operator $A$ is symmetric
(`Brezis.Chapter10.heatOperator_isSymmetric`) and maximal monotone, hence self-adjoint by
Proposition 7.6. -/
theorem heatOperator_isSelfAdjoint (hΩ : IsOfClassC 2 (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) :
    IsSelfAdjointOperator (heatOperator Ω) :=
  proposition_7_6 (heatOperator_isMaximalMonotone hΩ hΓ) heatOperator_isSymmetric

variable {u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}

/-- Let $\Omega \subset \mathbb{R}^N$ be open of class $C^2$, with $N = d + 1$ and bounded boundary
$\Gamma$. Then a curve $u$ is a solution of the heat equation in the class (4) of Theorem 10.1
if and only if it is a solution in the backbone class `Heat.IsSolution`.

The forward direction holds on every open set (`Brezis.Chapter10.IsHeatSolution.isSolution`).
Conversely, a solution in the backbone class has
$u(t) \in D(A) = H^2(\Omega) \cap H^1_0(\Omega)$ for $t > 0$ by
`Brezis.Chapter10.heatOperator_eq_dirichletLaplacian`, and lifts continuously to $H^2(\Omega)$
on $(0, \infty)$ by the graph-norm estimate of Theorem 9.25
(`Heat.IsSolution.contDiffOnThrough_two`). -/
theorem isHeatSolution_iff (hΩ : IsOfClassC 2 (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) :
    IsHeatSolution Ω u₀ u ↔ Heat.IsSolution Ω u₀ u := by
  refine ⟨fun h ↦ h.isSolution, fun h ↦ ?_⟩
  have hdom := (dirichletLaplacianDomain_eq_of_isContDiffChartDomain hΩ hΓ).1
  have hmem : ∀ t, 0 < t → u t ∈ (heatOperator Ω).domain := fun t ht ↦
    heatOperator_mem_domain_iff.2 ((hdom _).1 (h.mem_domain ht))
  exact
    { continuousOn := h.continuousOn
      mem_domain := hmem
      contDiffOnThrough := (h.contDiffOnThrough_two hΩ hΓ).1
      contDiffOn := h.contDiffOn
      hasDerivAt := fun t ht ↦
        (h.hasDerivAt ht).congr_deriv
          (congrArg Neg.neg (heatOperator_apply_eq ⟨u t, hmem t ht⟩).symm)
      apply_zero := h.apply_zero }

/-! ### Theorem 10.1 -/

/-- **Theorem 10.1** of [brezis2011functional], existence and uniqueness. Let
$\Omega \subset \mathbb{R}^N$ be open of class $C^\infty$, with $N = d + 1$ and bounded boundary
$\Gamma$, and let $u_0 \in L^2(\Omega)$. Then there exists a function $u$ that satisfies (1),
(2), (3) in the class (4),
$$u \in C([0, \infty); L^2(\Omega)) \cap C((0, \infty); H^2(\Omega) \cap H^1_0(\Omega)), \qquad
  u \in C^1((0, \infty); L^2(\Omega)),$$
and every other such function agrees with $u$ on $[0, \infty)$.

Uniqueness holds on $[0, \infty)$ because the class does not constrain negative times. The proof
of the source: $A$ is a self-adjoint maximal monotone operator in $H = L^2(\Omega)$
(`Brezis.Chapter10.heatOperator_isSelfAdjoint`), and Theorem 7.7 applies. The backbone theorem
`Heat.existsUnique_isSolution` proves the result on every open set for the weak class, which the
$C^2$ hypothesis identifies with the class of the source
(`Brezis.Chapter10.isHeatSolution_iff`). The solution is the semigroup $t \mapsto S_A(t) u_0$
(`Heat.solution`). The smoothing (5) is `Brezis.Chapter10.theorem_10_1_smooth`, the energy
identity (6) is `Brezis.Chapter10.theorem_10_1_energy`, and
$u \in L^2(0, \infty; H^1_0(\Omega))$ is `Brezis.Chapter10.theorem_10_1_memLp`. -/
theorem theorem_10_1 (hΩ : IsOfClassC ⊤ (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) (u₀ : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) :
    ∃ u, IsHeatSolution Ω u₀ u ∧ ∀ v, IsHeatSolution Ω u₀ v → EqOn v u (Ici 0) := by
  have hΩ2 : IsOfClassC 2 (Ω : Set 𝔼) := hΩ.of_le le_top
  obtain ⟨u, hu, huniq⟩ := Heat.existsUnique_isSolution (Ω := Ω) u₀
  exact ⟨u, (isHeatSolution_iff hΩ2 hΓ).2 hu, fun v hv ↦ huniq v hv.isSolution⟩

/-- **Theorem 10.1** of [brezis2011functional], "$u \in L^2(0, \infty; H^1_0(\Omega))$", for bounded
$\Omega$. Let $\Omega \subset \mathbb{R}^N$ be a bounded open set, with $N = d + 1$, let
$u_0 \in L^2(\Omega)$, and let $u$ be a solution of (1), (2), (3) in the class (4). Then $u$
lifts on $(0, \infty)$ to a curve in $L^2((0, \infty); H^1_0(\Omega))$ through the inclusion
$H^1_0(\Omega) \to L^2(\Omega)$.

**Correction.** The source states the clause for every $\Omega$ of class $C^\infty$ with
$\Gamma$ bounded. On an unbounded domain it is false. The statement assumes that $\Omega$ is
bounded, and then needs no regularity of $\Omega$.

The proof combines the gradient bound $\int_0^\infty |\nabla u(t)|^2 \, dt \le \frac12 |u_0|^2$
(`Brezis.Chapter10.theorem_10_1_memLp_gradient`) with Poincaré's inequality (Corollary 9.19),
$|u(t)|_{H^1} \le C |\nabla u(t)|_{L^2}$. It specializes
`Heat.IsSolution.memLpThrough_sobolevZero_of_isBounded`. -/
theorem theorem_10_1_memLp (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hu : IsHeatSolution Ω u₀ u) :
    Bochner.MemLpThrough (SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume) 2 u (Ioi 0) :=
  hu.isSolution.memLpThrough_sobolevZero_of_isBounded hb

/-- **Equation (7)** in Chapter 10 of [brezis2011functional], in the proof of Theorem 10.1. Let
$\Omega \subset \mathbb{R}^N$ be open of class $C^\infty$, with $N = d + 1$ and bounded boundary
$\Gamma$, and let $\ell \in \mathbb{N}$. Then
$$D(A^\ell) = \{u \in H^{2\ell}(\Omega) : u = \Delta u = \dots = \Delta^{\ell - 1} u = 0 \text{
  on } \Gamma\},$$
with continuous injection $D(A^\ell) \subseteq H^{2\ell}(\Omega)$. Precisely:

* $f \in L^2(\Omega)$ lies in $D(A^\ell)$ if and only if $f$ is the function of an element of
  $H^{2\ell}(\Omega)$ and the iterates $f, -\Delta f, \dots, (-\Delta)^{\ell - 1} f$ all lie in
  $H^1_0(\Omega)$;
* there is $C \ge 0$ with $\|w\|_{H^{2\ell}} \le C \|x\|_{D(A^\ell)}$ for every
  $x \in D(A^\ell)$ and every $w \in H^{2\ell}(\Omega)$ whose function is $x$.

The domain $D(A^\ell)$ is `Brezis.Chapter07.domainPow` of Chapter 7, and the norm of $D(A^\ell)$
is the graph norm $(\sum_{j \le \ell} |A^j u|^2)^{1/2}$ of the Hilbert space
`LinearPMap.PowDomain`. The condition on the iterates is `IsDirichletLaplacianChain`: "$= 0$ on
$\Gamma$" is read as membership of $H^1_0(\Omega)$, the trace-free reading of Theorem 9.17, and
each iterate lies in $H^2(\Omega)$ with the next iterate as its weak Laplacian. The proof
iterates Theorem 9.25 (`Brezis.Chapter09.theorem_9_25_higher`) and specializes
`dirichletLaplacian_mem_powDomain_iff` and `dirichletLaplacian_norm_sobolev_le_of_powDomain`.
The inclusion $\supseteq$ needs no regularity. -/
theorem equation_10_7 (hΩ : IsOfClassC ⊤ (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) (ℓ : ℕ) :
    (∀ f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)), f ∈ domainPow (heatOperator Ω) ℓ ↔
      (∃ w : sobolevSpaceHigher (d + 1) (2 * ℓ) 2 Ω, fnL ℝ 𝔟 (2 * ℓ) 2 Ω volume w = f) ∧
        IsDirichletLaplacianChain Ω ℓ f) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : (heatOperator Ω).PowDomain ℓ)
      (w : sobolevSpaceHigher (d + 1) (2 * ℓ) 2 Ω),
      fnL ℝ 𝔟 (2 * ℓ) 2 Ω volume w = LinearPMap.PowDomain.applyL (heatOperator Ω) ℓ 0 x →
        ‖w‖ ≤ C * ‖x‖ := by
  have hΩ' : IsContDiffChartDomain (2 * ℓ) (Ω : Set 𝔼) := hΩ.of_le (by simp)
  rw [heatOperator_eq_dirichletLaplacian (hΩ.of_le le_top) hΓ]
  exact ⟨fun f ↦ by rw [mem_domainPow_iff]; exact dirichletLaplacian_mem_powDomain_iff hΩ' hΓ f,
    dirichletLaplacian_norm_sobolev_le_of_powDomain hΩ' hΓ⟩

/-- **Theorem 10.1** of [brezis2011functional], the smoothing (5). Let $\Omega \subset \mathbb{R}^N$
be open of class $C^\infty$, with $N = d + 1$ and bounded boundary $\Gamma$, let
$u_0 \in L^2(\Omega)$, and let $u$ be a solution of (1), (2), (3) in the class (4). Then $u \in
C^\infty(\overline{\Omega} \times [\varepsilon, \infty))$ for every $\varepsilon > 0$: there is
a function $U : \mathbb{R}^N \times \mathbb{R} \to \mathbb{R}$ such that $U(\cdot, t) = u(t)$
almost everywhere on $\Omega$ for every $t > 0$, and for every $\varepsilon > 0$ the function
$U$ is of class $C^\infty$ on $\Omega \times (\varepsilon, \infty)$ with every derivative
extending continuously to $\overline{\Omega} \times [\varepsilon, \infty)$.

The smoothness class is `ContDiffOnClosure`, in the sense of footnote 16 of Chapter 9. The
argument of the source: $u \in C^k((0, \infty); D(A^\ell))$ for all $k, \ell$ (Theorem 7.7), and
$D(A^\ell) \subseteq H^{2\ell}(\Omega)$ with continuous injection by (7)
(`Brezis.Chapter10.equation_10_7`). Hence $u \in C^k((0, \infty); H^{2\ell}(\Omega))$ for all
$k, \ell$, and Corollary 9.15 gives $H^{2\ell}(\Omega) \subseteq C^k(\overline{\Omega})$ for
$k + N/2 < 2\ell$. The proof specializes `Heat.IsSolution.contDiffOnThrough_sobolev` and
`Bochner.contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough_Ioi`. The conclusion cannot be
strengthened to $C^\infty(\overline{\Omega} \times [0, \infty))$ (Theorem 10.2(c) and Remark 4). -/
theorem theorem_10_1_smooth (hΩ : IsOfClassC ⊤ (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) (hu : IsHeatSolution Ω u₀ u) :
    ∃ U : 𝔼 × ℝ → ℝ, (∀ t, 0 < t → (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set 𝔼)] u t) ∧
      ∀ ε > 0, ContDiffOnClosure ℝ ∞ U ((Ω : Set 𝔼) ×ˢ Ioi ε) := by
  have hext : IsSobolevExtensionDomainAll (d + 1) Ω :=
    IsSobolevExtensionDomainAll.of_isContDiffChartDomain (hΩ.of_le (by simp)) hΓ
  have hm : ∀ m : ℕ, Bochner.ContDiffOnThrough (fnL ℝ 𝔟 m 2 Ω volume) ∞ u (Ioi 0) := fun m ↦
    (hu.isSolution.contDiffOnThrough_sobolev (ℓ := m) (hΩ.of_le (by simp)) hΓ).sobolev_of_le
      (by omega)
  obtain ⟨U, hU, hc⟩ := Bochner.contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough_Ioi hext hm
  exact ⟨U, fun t ht ↦ hU t ht, hc⟩

/-! ### Theorem 10.2(a)–(c) on a regular domain -/

/-- **Theorem 10.2(a)** of [brezis2011functional], "$u \in L^2(0, \infty; H^2(\Omega))$", for
bounded $\Omega$. Let $\Omega \subset \mathbb{R}^N$ be a bounded open set of class $C^2$, with
$N = d + 1$ and bounded boundary $\Gamma$. Let $u_0 \in H^1_0(\Omega)$, that is, $u_0$ is the
function of some $v_0 \in H^1_0(\Omega)$, and let $u$ be the solution of (1), (2), (3) in the
class (4). Then $u$ lifts on $(0, \infty)$ to a curve in $L^2((0, \infty); H^2(\Omega))$.

**Correction.** The source states the clause for every $\Omega$ of class $C^\infty$ with
$\Gamma$ bounded. On an unbounded domain only $\int_0^\infty |\Delta u(t)|^2 \, dt =
\int_0^\infty |\partial_t u(t)|^2 \, dt < \infty$ holds. The statement assumes that $\Omega$ is
bounded.

The $H^2$-lift $w$ satisfies $|w(t)|_{H^2} \le C (|u(t)| + |\partial_t u(t)|)$ by the graph-norm
estimate of Theorem 9.25, and both terms are square integrable by Poincaré's inequality and
(11). The proof specializes `Heat.IsSolution.memLpThrough_two_of_isBounded`. -/
theorem theorem_10_2_a_memLp (hb : Bornology.IsBounded (Ω : Set 𝔼))
    (hΩ : IsOfClassC 2 (Ω : Set 𝔼)) (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼)))
    {v₀ : hZeroSpace (d + 1) Ω}
    (hu : IsHeatSolution Ω (SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume v₀) u) :
    Bochner.MemLpThrough (fnL ℝ 𝔟 2 2 Ω volume) 2 u (Ioi 0) :=
  hu.isSolution.memLpThrough_two_of_isBounded hb hΩ hΓ rfl

/-- **Theorem 10.2(b)** of [brezis2011functional]. Let $\Omega \subset \mathbb{R}^N$ be open of
class $C^2$, with $N = d + 1$ and bounded boundary $\Gamma$. Let
$u_0 \in H^2(\Omega) \cap H^1_0(\Omega) = D(A)$, and let $u$ be the solution of (1), (2), (3) in
the class (4). Then $u \in C([0, \infty); H^2(\Omega))$, and the identity of the proof of the
source holds: let $g : \mathbb{R} \to \mathbb{R}$ be a function with $g(t) = |\nabla \partial_t
u(t)|^2_{L^2} = |\nabla \Delta u(t)|^2_{L^2}$ for $t > 0$, computed on an $H^1_0$-lift of
$\partial_t u(t)$ as in footnote 3. Then for every $T > 0$ the function $g$ is integrable on
$(0, T]$ and
$$\frac12 |\Delta u(T)|^2_{L^2} + \int_0^T |\nabla \Delta u(t)|^2_{L^2} \, dt = \frac12 |\Delta
  u_0|^2_{L^2}.$$

In the statement $\Delta u(T)$ is $-A u(T)$, and $\partial_t u$ is `deriv u`. The proof of the
source applies Theorem 7.7 to the operator $A_2$ in $H_2 = H^2(\Omega) \cap H^1_0(\Omega)$. The
proof here applies Theorem 7.4 for $u_0 \in D(A)$
(`Heat.IsSolution.contDiffOnThrough_two_Ici_of_mem_domain`) and uses
$\varphi(t) = \frac12 |\Delta u(t)|^2$ with $\varphi' = -|\nabla \Delta u|^2$
(`Heat.IsSolution.energy_domain`, on every open set). The clauses
$u \in L^2(0, \infty; H^3(\Omega))$ and $\partial_t u \in L^2(0, \infty; H^1_0(\Omega))$ are
`Brezis.Chapter10.theorem_10_2_b_memLp`. -/
theorem theorem_10_2_b (hΩ : IsOfClassC 2 (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) (hu₀ : u₀ ∈ (heatOperator Ω).domain)
    (hu : IsHeatSolution Ω u₀ u) :
    Bochner.ContDiffOnThrough (fnL ℝ 𝔟 2 2 Ω volume) 0 u (Ici 0) ∧
      ∀ g : ℝ → ℝ, (∀ t, 0 < t → ∃ z : hSpace (d + 1) Ω, z ∈ hZeroSpace (d + 1) Ω ∧
          fnL ℝ 𝔟 1 2 Ω volume z = deriv u t ∧
          g t = ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv z i x ^ 2) →
        ∀ T (hT : 0 < T), IntegrableOn g (Ioc 0 T) ∧
          1 / 2 * ‖heatOperator Ω ⟨u T, hu.mem_domain T hT⟩‖ ^ 2 + ∫ t in (0 : ℝ)..T, g t
            = 1 / 2 * ‖heatOperator Ω ⟨u₀, hu₀⟩‖ ^ 2 := by
  have h := hu.isSolution
  refine ⟨h.contDiffOnThrough_two_Ici_of_mem_domain (heatOperator_domain_le hu₀) hΩ hΓ,
    fun g hg T hT ↦ ?_⟩
  have hg' : ∀ t (ht : 0 < t),
      g t = ⟪dirichletLaplacian Ω ⟨deriv u t, h.deriv_mem_domain ht⟩, deriv u t⟫_ℝ := by
    intro t ht
    obtain ⟨z, hz, hzt, hgt⟩ := hg t ht
    rw [hgt, sum_integral_partialDeriv_sq]
    exact (dirichletLaplacian_inner_self_eq_dirichletForm _ hz hzt).symm
  obtain ⟨hint, e⟩ := h.energy_domain (heatOperator_domain_le hu₀) hg' hT
  refine ⟨hint, ?_⟩
  rw [heatOperator_apply_eq, heatOperator_apply_eq, ← e, h.deriv_eq hT, norm_neg]

/-- **Theorem 10.2(b)** of [brezis2011functional], "$u \in L^2(0, \infty; H^3(\Omega))$ and
$\partial_t u \in L^2(0, \infty; H^1_0(\Omega))$", for bounded $\Omega$. Let
$\Omega \subset \mathbb{R}^N$ be a bounded open set of class $C^3$, with $N = d + 1$ and bounded
boundary $\Gamma$. Let $u_0 \in H^2(\Omega) \cap H^1_0(\Omega)$, and let $u$ be the solution of
(1), (2), (3) in the class (4). Then $u$ lifts on $(0, \infty)$ to a curve in
$L^2((0, \infty); H^3(\Omega))$, and $\partial_t u$ lifts on $(0, \infty)$ to a curve in
$L^2((0, \infty); H^1_0(\Omega))$.

**Correction.** The source states the clauses for every $\Omega$ of class $C^\infty$ with
$\Gamma$ bounded. On an unbounded domain the memberships fail. The statement assumes that
$\Omega$ is bounded.

The source asks "(why?)". The answer is the $H^3$ estimate of Theorem 9.25 for
$-\Delta u = -\partial_t u \in H^1_0(\Omega)$, together with Poincaré's inequality. The proof
specializes `Heat.IsSolution.memLpThrough_three_of_isBounded` and
`Heat.IsSolution.memLpThrough_sobolevZero_deriv_of_isBounded`. -/
theorem theorem_10_2_b_memLp (hb : Bornology.IsBounded (Ω : Set 𝔼))
    (hΩ : IsOfClassC 3 (Ω : Set 𝔼)) (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼)))
    (hu₀ : u₀ ∈ (heatOperator Ω).domain) (hu : IsHeatSolution Ω u₀ u) :
    Bochner.MemLpThrough (fnL ℝ 𝔟 3 2 Ω volume) 2 u (Ioi 0) ∧
      Bochner.MemLpThrough (SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume) 2 (deriv u) (Ioi 0) :=
  ⟨hu.isSolution.memLpThrough_three_of_isBounded hb hΩ hΓ (heatOperator_domain_le hu₀),
    hu.isSolution.memLpThrough_sobolevZero_deriv_of_isBounded hb (heatOperator_domain_le hu₀)⟩

/-- If $u_0 \in D(A^k)$ for every $k$, then a solution $u$ of the heat equation satisfies
$u \in C^\infty([0, \infty); H^m(\Omega))$ for every $m$; this is the input of Theorem 10.2(c),
from Theorem 7.5 and (7). -/
private theorem forall_contDiffOnThrough_Ici_of_forall_powDomain (hΩ : IsOfClassC ⊤ (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) (h : Heat.IsSolution Ω u₀ u)
    (hk : ∀ k : ℕ, ∃ x : (dirichletLaplacian Ω).PowDomain k,
      LinearPMap.PowDomain.applyL (dirichletLaplacian Ω) k 0 x = u₀) (m : ℕ) :
    Bochner.ContDiffOnThrough (fnL ℝ 𝔟 m 2 Ω volume) ∞ u (Ici 0) := by
  have hΩ' : IsContDiffChartDomain (2 * m) (Ω : Set 𝔼) := hΩ.of_le (by simp)
  have h2m : ∀ n : ℕ, Bochner.ContDiffOnThrough (fnL ℝ 𝔟 (2 * m) 2 Ω volume) n u (Ici 0) := by
    intro n
    obtain ⟨x, hx⟩ := hk (m + n)
    exact (h.contDiffOnThrough_sobolev_Ici_of_powDomain x hx (ℓ := m) (by omega) hΩ' hΓ).of_le
      (by exact_mod_cast (by omega : n ≤ m + n - m))
  -- the injectivity of the inclusion, with its type spelled out (instance search on the
  -- implicit form of `fnL_injective` takes a minute)
  have hJ : Function.Injective (fnL ℝ 𝔟 (2 * m) 2 Ω volume) := SobolevMultiIndex.fnL_injective
  exact (Bochner.ContDiffOnThrough.infty_of_forall_nat hJ h2m).sobolev_of_le (by omega)

/-- **Theorem 10.2(c)** of [brezis2011functional]. Let $\Omega \subset \mathbb{R}^N$ be open of
class $C^\infty$, with $N = d + 1$ and bounded boundary $\Gamma$. Let $u_0 \in H^k(\Omega)$ for
every $k$, and let $u_0$ satisfy the compatibility conditions (8),
$$u_0 = \Delta u_0 = \dots = \Delta^j u_0 = \dots = 0 \text{ on } \Gamma,$$
read as in (7): for every $\ell$ the iterates $u_0, -\Delta u_0, \dots, (-\Delta)^{\ell - 1}
u_0$ lie in $H^1_0(\Omega)$. Let $u$ be the solution of (1), (2), (3) in the class (4). Then $u
\in C^\infty(\overline{\Omega} \times [0, \infty))$: there is a function $U : \mathbb{R}^N
\times \mathbb{R} \to \mathbb{R}$ such that $U(\cdot, t) = u(t)$ almost everywhere on $\Omega$
for every $t \ge 0$, and $U$ is of class $C^\infty$ on $\Omega \times (0, \infty)$ with every
derivative extending continuously to the closure $\overline{\Omega} \times [0, \infty)$.

The compatibility conditions are `IsDirichletLaplacianChain Ω ℓ u₀` for every $\ell$, and the
smoothness class is `ContDiffOnClosure`. The proof of the source: "assumption (8) says precisely
that $u_0 \in D(A^k)$ for every $k$" (by (7), `Brezis.Chapter10.equation_10_7`), Theorem 7.5
gives $u \in C^{k - j}([0, \infty); D(A^j))$ for all $j \le k$, and (7) with Corollary 9.15
concludes as in Theorem 10.1. The proof specializes
`Heat.IsSolution.contDiffOnThrough_sobolev_Ici_of_powDomain` and
`Bochner.contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough_Ici`. -/
theorem theorem_10_2_c (hΩ : IsOfClassC ⊤ (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼)))
    (hu₀ : ∀ k : ℕ, ∃ w : sobolevSpaceHigher (d + 1) k 2 Ω, fnL ℝ 𝔟 k 2 Ω volume w = u₀)
    (hcomp : ∀ ℓ : ℕ, IsDirichletLaplacianChain Ω ℓ u₀) (hu : IsHeatSolution Ω u₀ u) :
    ∃ U : 𝔼 × ℝ → ℝ, (∀ t, 0 ≤ t → (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set 𝔼)] u t) ∧
      ContDiffOnClosure ℝ ∞ U ((Ω : Set 𝔼) ×ˢ Ioi 0) := by
  have hk : ∀ k : ℕ, ∃ x : (dirichletLaplacian Ω).PowDomain k,
      LinearPMap.PowDomain.applyL (dirichletLaplacian Ω) k 0 x = u₀ := fun k ↦
    (dirichletLaplacian_mem_powDomain_iff (hΩ.of_le (by simp)) hΓ u₀).2 ⟨hu₀ (2 * k), hcomp k⟩
  have hext : IsSobolevExtensionDomainAll (d + 1) Ω :=
    IsSobolevExtensionDomainAll.of_isContDiffChartDomain (hΩ.of_le (by simp)) hΓ
  obtain ⟨U, hU, hc⟩ := Bochner.contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough_Ici hext
    (forall_contDiffOnThrough_Ici_of_forall_powDomain hΩ hΓ hu.isSolution hk)
  exact ⟨U, fun t ht ↦ hU t ht, hc⟩

/-! ### Remark 1 -/

/-- Let $\Omega \subset \mathbb{R}^N$ be open of class $C^2$, with $N = d + 1$ and bounded boundary
$\Gamma$. Then a curve $u$ is a solution of the backward problem of Remark 1 in Chapter 10 if
and only if it is a solution in the backbone class `Heat.IsBackwardSolution`. -/
theorem isBackwardHeatSolution_iff (hΩ : IsOfClassC 2 (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) {T : ℝ}
    {uT : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))} :
    IsBackwardHeatSolution Ω T uT u ↔ Heat.IsBackwardSolution Ω T uT u := by
  refine ⟨fun h ↦ h.isBackwardSolution, fun h ↦ ?_⟩
  have hdom := (dirichletLaplacianDomain_eq_of_isContDiffChartDomain hΩ hΓ).1
  have hmem : ∀ t, t < T → u t ∈ (heatOperator Ω).domain := fun t ht ↦
    heatOperator_mem_domain_iff.2 ((hdom _).1 (h.mem_domain t ht))
  -- the `H²`-lift, transported from the forward solution `s ↦ u (T − s)`
  obtain ⟨v, hv, hvu⟩ := ((Heat.isBackwardSolution_iff.1 h).contDiffOnThrough_two hΩ hΓ).1
  exact
    { continuousOn := h.continuousOn
      mem_domain := hmem
      contDiffOnThrough := ⟨fun t ↦ v (T - t),
        hv.comp (contDiffOn_const.sub contDiffOn_id) fun t (ht : t < T) ↦
          show T - t ∈ Ioi (0 : ℝ) from sub_pos.2 ht,
        fun t (ht : t < T) ↦ by
          have := hvu (T - t) (sub_pos.2 ht)
          simp only [sub_sub_cancel] at this
          exact this⟩
      contDiffOn := h.contDiffOn
      hasDerivAt := fun t ht ↦
        (h.hasDerivAt t ht).congr_deriv (heatOperator_apply_eq ⟨u t, hmem t ht⟩).symm
      apply_eq := h.apply_eq }

/-- **Remark 1** in Chapter 10 of [brezis2011functional], the well-posed backward problem. Let
$\Omega \subset \mathbb{R}^N$ be open of class $C^\infty$, with $N = d + 1$ and bounded boundary
$\Gamma$, let $T \in \mathbb{R}$ and $u_T \in L^2(\Omega)$. Then the problem (9'), (10), (11),
$$-\partial_t u - \Delta u = 0 \text{ in } \Omega \times (-\infty, T), \qquad u = 0 \text{ on }
  \Gamma \times (-\infty, T), \qquad u(T) = u_T,$$
has a solution in the class of Theorem 10.1, and every other solution agrees with it on
$(-\infty, T]$.

The source says: "change $t$ into $T - t$ and apply Theorem 10.1". The proof specializes
`Heat.existsUnique_isSolution_backward`, and the solution is $t \mapsto S_A(T - t) u_T$. -/
theorem remark_10_1 (hΩ : IsOfClassC ⊤ (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) (T : ℝ)
    (uT : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) :
    ∃ u, IsBackwardHeatSolution Ω T uT u ∧
      ∀ v, IsBackwardHeatSolution Ω T uT v → EqOn v u (Iic T) := by
  have hΩ2 : IsOfClassC 2 (Ω : Set 𝔼) := hΩ.of_le le_top
  obtain ⟨u, hu, huniq⟩ := Heat.existsUnique_isSolution_backward (Ω := Ω) T uT
  exact ⟨u, (isBackwardHeatSolution_iff hΩ2 hΓ).2 hu, fun v hv ↦ huniq v hv.isBackwardSolution⟩

/-- **Remark 1** in Chapter 10 of [brezis2011functional], the necessary condition (12) for the
backward problem (9), (10), (11). Let $\Omega \subset \mathbb{R}^N$ be open of class $C^\infty$,
with $N = d + 1$ and bounded boundary $\Gamma$, and let $T > 0$. The backward problem is
$\partial_t u - \Delta u = 0$ in $\Omega \times (0, T)$, $u = 0$ on $\Gamma \times (0, T)$,
$u(T) = u_T$. Let $u$ be a solution of (1), (2), (3) in the class (4), with some initial datum
$u_0$, such that $u(T) = u_T$. Then

* $u_T \in D(A^\ell)$ for every $\ell$,
* hence, by (7), for every $\ell$ the function $u_T$ lies in $H^{2\ell}(\Omega)$ and
  $\Delta^j u_T = 0$ on $\Gamma$ for all $j < \ell$, and
* $u_T \in C^\infty(\overline{\Omega})$: $u_T$ agrees almost everywhere on $\Omega$ with a
  function $\tilde u$ that is continuous on $\overline{\Omega}$ and of class
  $C^\infty(\overline{\Omega})$.

A solution of the backward problem in the class of Theorem 10.1 is a solution of (1), (2), (3)
on $[0, \infty)$ with datum $u(0)$; by uniqueness this is the only way that a solution on
$[0, T]$ in that class arises. So $u_T = u(T)$ is as smooth as Theorem 10.1 makes the solution
at any positive time (`Heat.IsSolution.exists_powDomain`). The condition "$\Delta^j u_T = 0$ on
$\Gamma$" is read as in (7), with `IsDirichletLaplacianChain`, and $C^\infty(\overline{\Omega})$
is `ContDiffOnClosure`. The further claim of the source, that even under (12) a solution need
not exist, is not formalized. -/
theorem remark_10_1_necessary (hΩ : IsOfClassC ⊤ (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) {T : ℝ} (hT : 0 < T)
    {uT : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))} (hu : IsHeatSolution Ω u₀ u) (huT : u T = uT) :
    (∀ ℓ, uT ∈ domainPow (heatOperator Ω) ℓ) ∧
      (∀ ℓ, (∃ w : sobolevSpaceHigher (d + 1) (2 * ℓ) 2 Ω, fnL ℝ 𝔟 (2 * ℓ) 2 Ω volume w = uT) ∧
        IsDirichletLaplacianChain Ω ℓ uT) ∧
      ∃ ũ : 𝔼 → ℝ, ContDiffOnClosure ℝ ∞ ũ Ω ∧ ContinuousOn ũ (closure (Ω : Set 𝔼)) ∧
        (uT : 𝔼 → ℝ) =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ := by
  have hpow : ∀ ℓ, ∃ x : (dirichletLaplacian Ω).PowDomain ℓ,
      LinearPMap.PowDomain.applyL (dirichletLaplacian Ω) ℓ 0 x = uT := fun ℓ ↦
    huT ▸ hu.isSolution.exists_powDomain hT ℓ
  have h7 : ∀ ℓ, (∃ w : sobolevSpaceHigher (d + 1) (2 * ℓ) 2 Ω,
      fnL ℝ 𝔟 (2 * ℓ) 2 Ω volume w = uT) ∧ IsDirichletLaplacianChain Ω ℓ uT := fun ℓ ↦
    (dirichletLaplacian_mem_powDomain_iff (hΩ.of_le (by simp)) hΓ uT).1 (hpow ℓ)
  refine ⟨fun ℓ ↦ ?_, h7, ?_⟩
  · rw [heatOperator_eq_dirichletLaplacian (hΩ.of_le le_top) hΓ, mem_domainPow_iff]
    exact hpow ℓ
  · refine Elliptic.exists_contDiffOnClosure_infty_of_forall_memSobolevMultiIndex
      (hΩ.of_le (by simp)) hΓ fun m ↦ ?_
    obtain ⟨w, hw⟩ := (h7 m).1
    have hw' : fn w =ᵐ[volume.restrict (Ω : Set 𝔼)] uT :=
      Filter.EventuallyEq.of_eq (congrArg (fun z : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)) ↦
        (z : 𝔼 → ℝ)) hw)
    exact ((SobolevMultiIndex.memSobolevMultiIndex w).congr_ae hw').mono_order (by omega)

/-! ### Remark 3: the Fourier method -/

/-- **Remark 3** in Chapter 10 of [brezis2011functional] (the Fourier method). Let
$\Omega \subset \mathbb{R}^N$ be a bounded nonempty open set, with $N = d + 1$. Let $(e_n)$ and
$(\lambda_n)$ be the Dirichlet eigenbasis of $-\Delta$ and its eigenvalues from Theorem 9.31,
let $u_0 \in L^2(\Omega)$, and let $u$ be a solution of (1), (2), (3) in the class (4). Write
$a_n(t) = (u(t), e_n)_{L^2}$, so that $u(t) = \sum_n a_n(t) e_n$. Then

* the coefficients satisfy (13), $a_n' + \lambda_n a_n = 0$ on $(0, \infty)$,
* $a_n(t) = a_n(0) e^{-\lambda_n t}$ for $t \ge 0$, with $a_n(0) = \int_\Omega u_0 e_n$, and
* the solution is given by the series (14), which converges in $L^2(\Omega)$ for every
  $t \ge 0$:
$$u(t) = \sum_n \Big(\int_\Omega u_0 e_n\Big) e^{-\lambda_n t} e_n.$$

The eigenbasis is `Elliptic.dirichletEigenbasis` and the eigenvalues are
`Elliptic.dirichletEigenvalue` (see `Brezis.Chapter09.theorem_9_31_weak`). No regularity of
$\Omega$ is needed. The question of convergence, for which the source refers to the literature,
is settled by uniqueness. The proof specializes
`Heat.IsSolution.hasDerivAt_inner_eigenfunction`, `Heat.IsSolution.inner_eigenfunction` and
`Heat.IsSolution.hasSum_eigenfunction`. -/
theorem remark_10_3 (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hne : (Ω : Set 𝔼).Nonempty)
    (hu : IsHeatSolution Ω u₀ u) :
    (∀ n, ∀ t, 0 < t → HasDerivAt (fun t ↦ ⟪u t, Elliptic.dirichletEigenbasis Ω hb hne n⟫_ℝ)
      (-(Elliptic.dirichletEigenvalue Ω hb n
        * ⟪u t, Elliptic.dirichletEigenbasis Ω hb hne n⟫_ℝ)) t) ∧
    (∀ n, ∀ t, 0 ≤ t → ⟪u t, Elliptic.dirichletEigenbasis Ω hb hne n⟫_ℝ
      = (∫ x in (Ω : Set 𝔼), u₀ x * Elliptic.dirichletEigenbasis Ω hb hne n x)
        * Real.exp (-(Elliptic.dirichletEigenvalue Ω hb n * t))) ∧
    ∀ t, 0 ≤ t → HasSum (fun n ↦
      ((∫ x in (Ω : Set 𝔼), u₀ x * Elliptic.dirichletEigenbasis Ω hb hne n x)
        * Real.exp (-(Elliptic.dirichletEigenvalue Ω hb n * t)))
        • Elliptic.dirichletEigenbasis Ω hb hne n) (u t) := by
  have h := hu.isSolution
  refine ⟨fun n t ht ↦ (h.hasDerivAt_inner_eigenfunction hb hne n ht).congr_deriv (neg_mul _ _),
    fun n t ht ↦ ?_, fun t ht ↦ (h.hasSum_eigenfunction hb hne ht).congr_fun fun n ↦ ?_⟩
  · rw [h.inner_eigenfunction hb hne n ht, MeasureTheory.L2.inner_eq_integral_mul, neg_mul,
      mul_comm]
  · rw [MeasureTheory.L2.inner_eq_integral_mul, neg_mul, mul_comm]

end Regular

end Brezis.Chapter10
