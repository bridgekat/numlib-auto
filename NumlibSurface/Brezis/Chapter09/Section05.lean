/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.PDE.Elliptic.MaximumPrinciple
import Numlib.Analysis.Sobolev.Boundary.ContDiffDomain
import Numlib.MeasureTheory.Function.ContinuousOnClosure
import NumlibSurface.Brezis.Chapter09.Section04

/-!
# Brezis, Section 9.5: Variational formulation of some boundary value problems

This module formalizes Section 9.5 of [brezis2011functional]. Let $\Omega \subset \mathbb{R}^N$ be
an open set with boundary $\Gamma = \partial\Omega$. The section solves five boundary value problems
by the variational method: a classical solution is a weak solution (Step A), the weak problem has a
unique solution by the Lax–Milgram theorem or by Stampacchia's theorem, and a weak solution that is
regular enough is a classical solution (Step D). The problems are the homogeneous Dirichlet problem
(31) for $-\Delta u + u = f$ (Example 1, Theorem 9.21), the inhomogeneous Dirichlet condition
$u = g$ on $\Gamma$ (Example 2, Proposition 9.22), the Dirichlet problem for a general second-order
elliptic operator (Example 3, Theorem 9.23, Remark 23), the homogeneous Neumann problem (Example 4,
Proposition 9.24) and problems on unbounded domains (Example 5). For example, a weak solution of
(31) is a function $u \in H_0^1(\Omega)$ with
$$\int_\Omega \nabla u \cdot \nabla v + \int_\Omega u v = \int_\Omega f v \quad \text{for all } v
  \in H_0^1(\Omega).$$

The proofs specialize the backbone module `Numlib.Analysis.PDE.Elliptic.Dirichlet`, which defines
the bilinear forms `Elliptic.laplaceForm` and `Elliptic.generalForm` and the load functional
`Elliptic.load`. The second clause of Remark 23 uses the maximum principle of
`Numlib.Analysis.PDE.Elliptic.MaximumPrinciple`. Steps A and D of Example 4 use the boundary theory
of `Numlib.Analysis.Sobolev.Boundary.ContDiffDomain` on a bounded $C^1$ domain: the surface measure
`IsContDiffDomain.boundaryMeasure`, the outward normal `IsContDiffDomain.outwardNormal`, Green's
formula `BoundaryData.integral_laplacian_mul_add_eq` and the density theorem
`IsContDiffDomain.hasSmoothDensity`.

## Main definitions

* Example 1, classical solution, `Brezis.Chapter09.IsClassicalSolutionDirichlet`:
  $u \in C^2(\overline\Omega)$ satisfies $-\Delta u + u = f$ in $\Omega$ and $u = 0$ on $\Gamma$
  (31).
* Example 1, weak solution, `Brezis.Chapter09.IsWeakSolutionDirichlet`: $u \in H_0^1(\Omega)$
  satisfies (32).
* Example 2, the set $K$, `Brezis.Chapter09.admissibleSetInhomogeneous`: $K = \{v \in H^1(\Omega) :
  v - \tilde g \in H_0^1(\Omega)\}$.
* Example 2, classical solution, `Brezis.Chapter09.IsClassicalSolutionInhomogeneous`:
  $u \in C^2(\overline\Omega)$ satisfies $-\Delta u + u = f$ in $\Omega$ and $u = g$ on $\Gamma$
  (33).
* Example 2, weak solution, `Brezis.Chapter09.IsWeakSolutionInhomogeneous`: $u \in K$ satisfies
  (34).
* Example 3, the ellipticity condition (36), `Brezis.Chapter09.ellipticityCondition`: $\sum_{i,j}
  a_{ij}(x) \xi_i \xi_j \ge \alpha |\xi|^2$ for all $x \in \Omega$ and $\xi \in \mathbb{R}^N$, with
  $\alpha > 0$.
* Example 3, classical solution, `Brezis.Chapter09.IsClassicalSolutionElliptic`:
  $u \in C^2(\overline\Omega)$ satisfies $-\sum_{i,j} \partial_j(a_{ij} \partial_i u) + a_0 u = f$
  in $\Omega$ and $u = 0$ on $\Gamma$ (37).
* Example 3, weak solution of (37), `Brezis.Chapter09.IsWeakSolutionElliptic`: $u \in H_0^1(\Omega)$
  satisfies (38).
* Example 3, weak solution of the general problem (39),
  `Brezis.Chapter09.IsWeakSolutionGeneralElliptic`: $u \in H_0^1(\Omega)$ satisfies (40), with
  coefficients in $L^\infty(\Omega)$.
* Example 4, classical solution, `Brezis.Chapter09.IsClassicalSolutionNeumann`:
  $u \in C^2(\overline\Omega)$ satisfies $-\Delta u + u = f$ in $\Omega$ and
  $\partial u / \partial n = 0$ on $\Gamma$ (44).
* Example 4, weak solution, `Brezis.Chapter09.IsWeakSolutionNeumann`: $u \in H^1(\Omega)$ satisfies
  (45).

## Main results

* Example 1, Step A, `Brezis.Chapter09.example_9_1_stepA`: on a bounded $\Omega$, a classical
  solution of (31) is a weak solution.
* Theorem 9.21, `Brezis.Chapter09.theorem_9_21` (Dirichlet, Riemann, Poincaré, Hilbert): for every
  $f \in L^2(\Omega)$, (31) has a unique weak solution $u \in H_0^1(\Omega)$.
* Theorem 9.21, Dirichlet's principle, `Brezis.Chapter09.theorem_9_21_isMinOn`: the weak solution is
  the minimizer of $\frac12 \int_\Omega (|\nabla v|^2 + v^2) - \int_\Omega f v$ over
  $H_0^1(\Omega)$.
* Example 1, Step D, `Brezis.Chapter09.example_9_1_stepD` and
  `Brezis.Chapter09.example_9_1_stepD_of_continuous`: on a $C^1$ domain, a weak solution in
  $C^2(\overline\Omega)$ vanishes on $\Gamma$ and satisfies the equation almost everywhere, and
  everywhere when $f$ is continuous.
* Example 2, the set $K$, `Brezis.Chapter09.example_9_2`: $K$ is nonempty, closed and convex, and
  depends only on the boundary values of $\tilde g$.
* Example 2, Step A, `Brezis.Chapter09.example_9_2_stepA`: on a bounded $\Omega$, a classical
  solution of (33) is a weak solution.
* Proposition 9.22, `Brezis.Chapter09.proposition_9_22`: for every $f \in L^2(\Omega)$, (33) has a
  unique weak solution $u \in K$.
* Proposition 9.22, (34) ⇔ (35), `Brezis.Chapter09.proposition_9_22_iff`: the weak problem is
  equivalent to the variational inequality (35) on $K$.
* Proposition 9.22, the minimization, `Brezis.Chapter09.proposition_9_22_isMinOn`: the weak solution
  is the minimizer of the energy over $K$.
* Example 3, Step A, `Brezis.Chapter09.example_9_3_stepA`: on a bounded $\Omega$, a classical
  solution of (37) is a weak solution.
* Example 3, existence and uniqueness, `Brezis.Chapter09.example_9_3`: for elliptic continuous
  $a_{ij}$ and continuous $a_0 \ge 0$ on a bounded $\Omega$, (37) has a unique weak solution.
* Example 3, the symmetric case, `Brezis.Chapter09.example_9_3_isMinOn`: for symmetric $(a_{ij})$,
  the weak solution is the minimizer of the energy over $H_0^1(\Omega)$.
* Theorem 9.23, `Brezis.Chapter09.theorem_9_23` (Fredholm alternative): on a bounded $\Omega$, the
  solutions of (40) with $f = 0$ form a space of finite dimension $d$, and (40) is solvable if and
  only if $f$ satisfies $d$ orthogonality conditions.
* Remark 23, first clause, `Brezis.Chapter09.remark_9_23`: uniqueness for (40) implies existence and
  uniqueness for every $f$.
* Remark 23, second clause, `Brezis.Chapter09.remark_9_23_zero_drift`: if $a_i = 0$ and $a_0 \ge 0$,
  (40) has a unique solution for every $f$.
* Proposition 9.24, `Brezis.Chapter09.proposition_9_24`: for every $f \in L^2(\Omega)$, (44) has a
  unique weak solution $u \in H^1(\Omega)$.
* Proposition 9.24, the minimization, `Brezis.Chapter09.proposition_9_24_isMinOn`: the weak solution
  is the minimizer of the energy over $H^1(\Omega)$.
* Example 4, Step A, `Brezis.Chapter09.example_9_4_stepA`: on a bounded $C^1$ domain, a classical
  solution of (44) is a weak solution.
* Example 4, Step D, `Brezis.Chapter09.example_9_4_stepD_interior` and
  `Brezis.Chapter09.example_9_4_stepD`: a weak solution in $C^2(\overline\Omega)$ satisfies the
  equation in $\Omega$, and on a bounded $C^1$ domain it satisfies $\partial u / \partial n = 0$ on
  $\Gamma$.
* Example 5(a), `Brezis.Chapter09.example_9_5_a`: on $\mathbb{R}^N$, $-\Delta u + u = f$ has a
  unique weak solution in $H^1(\mathbb{R}^N)$.
* Example 5(b), `Brezis.Chapter09.example_9_5_b`: on the half space $\mathbb{R}^N_+$, the Dirichlet
  problem has a unique weak solution in $H_0^1(\mathbb{R}^N_+)$.
* Example 5(c), `Brezis.Chapter09.example_9_5_c`: on the half space $\mathbb{R}^N_+$, the Neumann
  problem has a unique weak solution in $H^1(\mathbb{R}^N_+)$.

## Conventions

* $H^1(\Omega)$ is `Brezis.Chapter09.hSpace N Ω` and $H_0^1(\Omega)$ is
  `Brezis.Chapter09.hZeroSpace N Ω` (Sections 9.1 and 9.4). The integrals of the source are written
  with the weak partial derivatives `Brezis.Chapter09.partialDeriv` and the functions
  `SobolevMultiIndex.fn`. Each weak problem is stated with the display of the source: (32), (34),
  (38), (40) or (45).
* The class $C^2(\overline\Omega)$ of footnote 16 of Section 9.3 is `ContDiffOnClosure ℝ 2 u Ω`
  together with `ContinuousOn u (closure Ω)`: $u$ is $C^2$ on $\Omega$, its derivatives of order at
  most $2$ extend continuously to $\overline\Omega$, and $u$ is its own continuous extension, so
  that its boundary values are meaningful. Mathlib's `ContDiffOn ℝ 2 u (closure Ω)` is a stronger
  hypothesis.
* The Laplacian is Mathlib's `Δ` (`InnerProductSpace.instLaplacian`). The data $f$ of the weak
  problems are elements of $L^2(\Omega)$, and the classical equations hold at every point of
  $\Omega$. The boundary $\Gamma$ is `frontier Ω`.
* The coefficients $a_{ij}, a_i, a_0$ of (39) and (40) are elements of $L^\infty(\Omega)$, as in the
  source, and the ellipticity condition (36) for them holds almost everywhere
  (`Elliptic.IsUniformlyElliptic`). For the continuous coefficients of Example 3, the pointwise
  condition (36) is `Brezis.Chapter09.ellipticityCondition`.
* "$\Omega$ is bounded" is `Bornology.IsBounded Ω`.

## Implementation notes

* Each weak problem is equivalent to a Galerkin problem `IsGalerkinSolution` of the backbone, for a
  bilinear form and the load functional $v \mapsto \int_\Omega f v$: see
  `Brezis.Chapter09.isWeakSolutionDirichlet_iff`,
  `Brezis.Chapter09.isWeakSolutionInhomogeneous_iff`, `Brezis.Chapter09.isWeakSolutionElliptic_iff`,
  `Brezis.Chapter09.isWeakSolutionGeneralElliptic_iff` and
  `Brezis.Chapter09.isWeakSolutionNeumann_iff`.
* `Brezis.Chapter09.isClassicalSolutionDirichlet_of_contDiffOn` and
  `Brezis.Chapter09.example_9_1_stepA_of_contDiffOn` accept a solution that is $C^2$ on
  $\overline\Omega$ in Mathlib's sense.
* The classical Neumann problem takes the unit normal field $n$ as a parameter. In Steps A and D of
  Example 4 it is the outward normal `IsContDiffDomain.outwardNormal` of a bounded domain of class
  $C^1$ in the graph form `IsContDiffDomain 1 Ω`.
* Results that need a $C^1$ domain, the half space or Poincaré's inequality are stated on
  $\mathbb{R}^N$ with $N = d + 1$.

## Deviations from the source

* **Theorem 9.21** (generalization). The source assumes that $\Omega$ is bounded. The existence,
  uniqueness and Dirichlet's principle hold for every open set. See `Brezis.Chapter09.theorem_9_21`
  and `Brezis.Chapter09.theorem_9_21_isMinOn`.
* **Example 1, Step D** (reading). The source concludes that $-\Delta u + u = f$ holds everywhere in
  $\Omega$. For $f \in L^2(\Omega)$ this presumes a continuous representative of $f$, which is a
  hypothesis. See `Brezis.Chapter09.example_9_1_stepD_of_continuous`.
* **Example 2, the set $K$** (generalization). The source takes $\tilde g \in H^1(\Omega) \cap
  C(\overline\Omega)$ with $\tilde g = g$ on $\Gamma$. The definition takes any
  $\tilde g \in H^1(\Omega)$. See `Brezis.Chapter09.admissibleSetInhomogeneous`.
* **Example 3, existence and the symmetric case** (generalization). The source assumes
  $a_{ij} \in C^1(\overline\Omega)$. The statements assume only $a_{ij} \in C(\overline\Omega)$. See
  `Brezis.Chapter09.example_9_3` and `Brezis.Chapter09.example_9_3_isMinOn`.
* **Remark 23, second clause** (reading). The source leaves the hypothesis $N \ge 1$ implicit. See
  `Brezis.Chapter09.remark_9_23_zero_drift`.
* **Proposition 9.24** (generalization). The source assumes that $\Omega$ is bounded and of class
  $C^1$. The statement holds for every open set. See `Brezis.Chapter09.proposition_9_24` and
  `Brezis.Chapter09.proposition_9_24_isMinOn`.

## Not formalized

* **Remark 23, second clause, with a first-order term.** For arbitrary $a_i$ the clause rests on
  Proposition 9.29 in the general case (Gilbarg–Trudinger), which the source does not prove.
-/

open Filter MeasureTheory Metric Set Topology TopologicalSpace Laplacian
open scoped ContDiff Distributions ENNReal InnerProductSpace NNReal

namespace Brezis.Chapter09

section Example1

variable {N : ℕ}

/-- The space $\mathbb{R}^N$ of the source, `EuclideanSpace ℝ (Fin N)`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

variable {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-! ### Example 1: the homogeneous Dirichlet problem for the Laplacian -/

/-- **Section 9.5** of [brezis2011functional], Example 1, definition of a classical solution. Let
$\Omega \subset \mathbb{R}^N$ be open and let $f, u : \mathbb{R}^N \to \mathbb{R}$. The function
$u$ is a **classical solution** of problem (31),
$$-\Delta u + u = f \text{ in } \Omega, \qquad u = 0 \text{ on } \Gamma,$$
if $u \in C^2(\overline\Omega)$, $-\Delta u(x) + u(x) = f(x)$ for every $x \in \Omega$, and
$u(x) = 0$ for every $x \in \Gamma = \partial\Omega$.

Here $u \in C^2(\overline\Omega)$ has the meaning of footnote 16 of Section 9.3:
`ContDiffOnClosure ℝ 2 u Ω` ($u$ is $C^2$ on $\Omega$ and its derivatives of order at most $2$
extend continuously to $\overline\Omega$), and $u$ is continuous on $\overline\Omega$. The
boundary $\Gamma$ is `frontier Ω`, and the Laplacian is the one of Mathlib,
`InnerProductSpace.instLaplacian`. -/
def IsClassicalSolutionDirichlet (Ω : Opens (EuclideanSpace ℝ (Fin N)))
    (f u : EuclideanSpace ℝ (Fin N) → ℝ) : Prop :=
  ContDiffOnClosure ℝ 2 u Ω ∧ ContinuousOn u (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) ∧
    (∀ x ∈ Ω, -Δ u x + u x = f x) ∧ EqOn u 0 (frontier (Ω : Set (EuclideanSpace ℝ (Fin N))))

/-- Let $\Omega \subset \mathbb{R}^N$ be open and let $f, u : \mathbb{R}^N \to \mathbb{R}$. If $u$
is $C^2$ on $\overline\Omega$ in Mathlib's sense (`ContDiffOn ℝ 2 u (closure Ω)`),
$-\Delta u + u = f$ in $\Omega$ and $u = 0$ on $\Gamma$, then $u$ is a classical solution of
(31) in the sense of `Brezis.Chapter09.IsClassicalSolutionDirichlet`.

The hypothesis gives `ContDiffOnClosure ℝ 2 u Ω` by `ContDiffOn.contDiffOnClosure`, and it gives
the continuity of $u$ on $\overline\Omega$. -/
theorem isClassicalSolutionDirichlet_of_contDiffOn {f u : 𝔼 → ℝ}
    (hu : ContDiffOn ℝ 2 u (closure (Ω : Set 𝔼))) (heq : ∀ x ∈ Ω, -Δ u x + u x = f x)
    (h0 : EqOn u 0 (frontier (Ω : Set 𝔼))) : IsClassicalSolutionDirichlet Ω f u :=
  ⟨hu.contDiffOnClosure Ω.isOpen, hu.continuousOn, heq, h0⟩

/-- **Section 9.5** of [brezis2011functional], Example 1, definition of a weak solution. Let
$\Omega \subset \mathbb{R}^N$ be open and let $f \in L^2(\Omega)$. An element
$u \in H^1(\Omega)$ is a **weak solution** of (31) if $u \in H_0^1(\Omega)$ and
$$\int_\Omega \nabla u \cdot \nabla v + \int_\Omega u v = \int_\Omega f v \quad \text{for all }
  v \in H_0^1(\Omega), \qquad (32)$$
where $\nabla u \cdot \nabla v = \sum_i \frac{\partial u}{\partial x_i} \frac{\partial
v}{\partial x_i}$.

The space $H^1(\Omega)$ is `Brezis.Chapter09.hSpace N Ω` and $H_0^1(\Omega)$ is
`Brezis.Chapter09.hZeroSpace N Ω`. The weak derivative $\partial u / \partial x_i$ is
`Brezis.Chapter09.partialDeriv u i`, and the function of $u$ is `SobolevMultiIndex.fn u`. -/
def IsWeakSolutionDirichlet (Ω : Opens (EuclideanSpace ℝ (Fin N)))
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) (u : hSpace N Ω) : Prop :=
  u ∈ hZeroSpace N Ω ∧ ∀ v ∈ hZeroSpace N Ω,
    (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), ∑ i, partialDeriv u i x * partialDeriv v i x)
      + ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), f x * SobolevMultiIndex.fn v x

/-- Let $\Omega \subset \mathbb{R}^N$ be open and let $u, v \in H^1(\Omega)$. The bilinear form of
$-\Delta + 1$, `Elliptic.laplaceForm Ω`, is the left-hand side of (32), written as two
integrals:
$$a(u, v) = \int_\Omega \nabla u \cdot \nabla v + \int_\Omega u v.$$

The backbone's `Elliptic.laplaceForm_apply` writes it as one integral. -/
theorem laplaceForm_apply_two (u v : hSpace N Ω) :
    Elliptic.laplaceForm Ω u v
      = (∫ x in (Ω : Set 𝔼), ∑ i, partialDeriv u i x * partialDeriv v i x)
        + ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x := by
  rw [Elliptic.laplaceForm, add_apply, add_apply, Elliptic.dirichletForm_apply,
    Elliptic.pairing_apply, ContinuousLinearMap.id_apply, MeasureTheory.L2.inner_eq_integral_mul]
  rfl

/-- Let $\Omega \subset \mathbb{R}^N$ be open, let $f \in L^2(\Omega)$ and let $u \in H^1(\Omega)$.
Then $u$ is a weak solution of (31) in the sense of (32) if and only if $u$ solves the Galerkin
problem on $H_0^1(\Omega)$ for the bilinear form `Elliptic.laplaceForm Ω` and the load
functional `Elliptic.load Ω f`, which is $v \mapsto \int_\Omega f v$. That is,
$u \in H_0^1(\Omega)$ and $a(u, v) = \int_\Omega f v$ for all $v \in H_0^1(\Omega)$.

The Galerkin problem is `IsGalerkinSolution`. -/
theorem isWeakSolutionDirichlet_iff (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) (u : hSpace N Ω) :
    IsWeakSolutionDirichlet Ω f u ↔
      IsGalerkinSolution (Elliptic.laplaceForm Ω) (Elliptic.load Ω f) (hZeroSpace N Ω) u := by
  simp only [IsWeakSolutionDirichlet, IsGalerkinSolution, laplaceForm_apply_two,
    Elliptic.load_apply]

/-- **Example 1** of [brezis2011functional], Step A: every classical solution is a weak solution.
Let $\Omega \subset \mathbb{R}^N$ be a bounded open set, let $f : \mathbb{R}^N \to \mathbb{R}$
be square integrable on $\Omega$, and let $u$ be a classical solution of (31). Then there is
$U \in H^1(\Omega)$ whose function equals $u$ almost everywhere on $\Omega$, and $U$ is a weak
solution of (31) with the datum $f \in L^2(\Omega)$.

The datum is the class `hf.toLp f` of $f$ in $L^2(\Omega)$. The proof is the backbone's
`Elliptic.isGalerkinSolution_laplace_of_classical`. Since $u$ and $\nabla u$ are bounded,
$u \in H^1(\Omega) \cap C(\overline\Omega)$, and $u = 0$ on $\Gamma$ gives $u \in H_0^1(\Omega)$
by Theorem 9.17, (i) ⇒ (ii), which needs no regularity of $\Omega$ (Remark 19). For
$v \in C_c^1(\Omega)$ the identity (32) is an integration by parts, and it extends to all
$v \in H_0^1(\Omega)$ by density. -/
theorem example_9_1_stepA (hb : Bornology.IsBounded (Ω : Set 𝔼)) {f u : 𝔼 → ℝ}
    (hu : IsClassicalSolutionDirichlet Ω f u) (hf : MemLp f 2 (volume.restrict (Ω : Set 𝔼))) :
    ∃ U : hSpace N Ω, SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set 𝔼)] u ∧
      IsWeakSolutionDirichlet Ω (hf.toLp f) U := by
  obtain ⟨U, -, hUu, hUw⟩ := Elliptic.isGalerkinSolution_laplace_of_classical Ω hb hu.1 hu.2.1
    hu.2.2.2 hf hu.2.2.1
  exact ⟨U, hUu, (isWeakSolutionDirichlet_iff _ _).2 hUw⟩

/-- **Example 1** of [brezis2011functional], Step A, for a solution of class $C^2$ on
$\overline\Omega$ in Mathlib's sense. Let $\Omega \subset \mathbb{R}^N$ be a bounded open set,
let $f : \mathbb{R}^N \to \mathbb{R}$ be square integrable on $\Omega$, and let $u$ satisfy
`ContDiffOn ℝ 2 u (closure Ω)`, $-\Delta u + u = f$ in $\Omega$ and $u = 0$ on $\Gamma$. Then
there is $U \in H^1(\Omega)$ whose function equals $u$ almost everywhere on $\Omega$, and $U$ is
a weak solution of (31).

The proof combines `Brezis.Chapter09.example_9_1_stepA` with
`Brezis.Chapter09.isClassicalSolutionDirichlet_of_contDiffOn`. -/
theorem example_9_1_stepA_of_contDiffOn (hb : Bornology.IsBounded (Ω : Set 𝔼)) {u : 𝔼 → ℝ}
    (hu : ContDiffOn ℝ 2 u (closure (Ω : Set 𝔼))) {f : 𝔼 → ℝ}
    (heq : ∀ x ∈ Ω, -Δ u x + u x = f x) (h0 : EqOn u 0 (frontier (Ω : Set 𝔼)))
    (hf : MemLp f 2 (volume.restrict (Ω : Set 𝔼))) :
    ∃ U : hSpace N Ω, SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set 𝔼)] u ∧
      IsWeakSolutionDirichlet Ω (hf.toLp f) U :=
  example_9_1_stepA hb (isClassicalSolutionDirichlet_of_contDiffOn hu heq h0) hf

/-- **Theorem 9.21** of [brezis2011functional] (Dirichlet, Riemann, Poincaré, Hilbert). Let
$\Omega \subset \mathbb{R}^N$ be open. For every $f \in L^2(\Omega)$ there is a unique weak
solution $u \in H_0^1(\Omega)$ of (31).

**Generalization.** The source assumes that $\Omega$ is bounded. The proof does not use this,
and the statement holds for every open set.

The proof is the backbone's `Elliptic.existsUnique_isGalerkinSolution_laplace`: the Lax–Milgram
theorem (Corollary 5.8) in the Hilbert space $H_0^1(\Omega)$ with the bilinear form $a(u, v) =
\int_\Omega (\nabla u \cdot \nabla v + u v)$, which is the scalar product of $H^1(\Omega)$, and
the linear functional $v \mapsto \int_\Omega f v$. -/
theorem theorem_9_21 (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) :
    ∃! u : hSpace N Ω, IsWeakSolutionDirichlet Ω f u := by
  simp only [isWeakSolutionDirichlet_iff]
  exact Elliptic.existsUnique_isGalerkinSolution_laplace Ω f

/-- **Theorem 9.21** of [brezis2011functional], Dirichlet's principle. Let
$\Omega \subset \mathbb{R}^N$ be open, let $f \in L^2(\Omega)$ and let $u \in H_0^1(\Omega)$.
Then $u$ minimizes
$$\varphi(v) = \frac12 \int_\Omega \bigl(|\nabla v|^2 + v^2\bigr) - \int_\Omega f v$$
over $v \in H_0^1(\Omega)$ if and only if $u$ is the weak solution of (31).

**Generalization.** As in `Brezis.Chapter09.theorem_9_21`, $\Omega$ need not be bounded.

The source states that the weak solution is obtained by $\min_{v \in H_0^1(\Omega)} \varphi(v)$.
The proof is the backbone's `Elliptic.isMinOn_energy_iff_isGalerkinSolution_laplace`, which uses
that the form is symmetric and coercive. -/
theorem theorem_9_21_isMinOn (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) {u : hSpace N Ω}
    (hu : u ∈ hZeroSpace N Ω) :
    IsMinOn (fun v : hSpace N Ω ↦ (1 / 2 : ℝ) * (∫ x in (Ω : Set 𝔼),
        (∑ i, partialDeriv v i x ^ 2 + SobolevMultiIndex.fn v x ^ 2))
      - ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn v x) (hZeroSpace N Ω) u
      ↔ IsWeakSolutionDirichlet Ω f u := by
  have e : (fun v : hSpace N Ω ↦ (1 / 2 : ℝ) * (∫ x in (Ω : Set 𝔼),
        (∑ i, partialDeriv v i x ^ 2 + SobolevMultiIndex.fn v x ^ 2))
      - ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn v x)
      = (Elliptic.laplaceForm Ω).energy (Elliptic.load Ω f) := by
    funext v
    rw [Elliptic.energy_laplace_apply]
    simp only [sq]
    rfl
  rw [e, isWeakSolutionDirichlet_iff]
  exact Elliptic.isMinOn_energy_iff_isGalerkinSolution_laplace Ω hu

end Example1

section Example1StepD

variable {d : ℕ}

/-- The space $\mathbb{R}^N$ of the source with $N = d + 1$, `EuclideanSpace ℝ (Fin (d + 1))`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

variable {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **Example 1** of [brezis2011functional], Step D: recovery of a classical solution. Let
$N \ge 1$, let $\Omega \subset \mathbb{R}^N$ be an open set of class $C^1$, let
$f \in L^2(\Omega)$, and let $U \in H^1(\Omega)$ be the weak solution of (31). Suppose that the
function of $U$ equals almost everywhere on $\Omega$ a function $u \in C^2(\overline\Omega)$.
Then $u = 0$ on $\Gamma$, and $-\Delta u + u = f$ almost everywhere on $\Omega$.

The boundary condition follows from Theorem 9.17, and the equation from Corollary 4.24 through
the backbone's `Elliptic.laplacian_ae_eq_of_isGalerkinSolution`. With a continuous datum the
equation holds everywhere, see `Brezis.Chapter09.example_9_1_stepD_of_continuous`. The statement
does not assume that $\Omega$ is bounded. "Of class $C^1$" is `Brezis.Chapter09.IsClassC1`, and
$\mathbb{R}^N$ is written with $N = d + 1$. -/
theorem example_9_1_stepD (hΩ : IsClassC1 (Ω : Set 𝔼)) {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))}
    {U : hSpace (d + 1) Ω} (hU : IsWeakSolutionDirichlet Ω f U) {u : 𝔼 → ℝ}
    (hUu : SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set 𝔼)] u)
    (hu : ContDiffOnClosure ℝ 2 u Ω) (huc : ContinuousOn u (closure (Ω : Set 𝔼))) :
    EqOn u 0 (frontier (Ω : Set 𝔼)) ∧
      (fun x ↦ -Δ u x + u x) =ᵐ[volume.restrict (Ω : Set 𝔼)] f :=
  ⟨theorem_9_17_mpr hΩ (by simp) hU.1 hUu huc,
    Elliptic.laplacian_ae_eq_of_isGalerkinSolution Ω ((isWeakSolutionDirichlet_iff f U).1 hU)
      hu.contDiffOn hUu⟩

/-- **Example 1** of [brezis2011functional], Step D, with a continuous datum. Let $N \ge 1$, let
$\Omega \subset \mathbb{R}^N$ be an open set of class $C^1$, let $f \in L^2(\Omega)$, let
$U \in H^1(\Omega)$ be the weak solution of (31), and let $u \in C^2(\overline\Omega)$ equal the
function of $U$ almost everywhere on $\Omega$. If $f$ equals almost everywhere on $\Omega$ a
function $g$ that is continuous on $\Omega$, then $u$ is a classical solution of (31) with the
datum $g$.

**Reading.** The source concludes that the equation holds "in fact everywhere, since
$u \in C^2(\Omega)$". Because $f$ is only an element of $L^2(\Omega)$, this presumes that $f$
has a continuous representative $g$. Here this is a hypothesis. -/
theorem example_9_1_stepD_of_continuous (hΩ : IsClassC1 (Ω : Set 𝔼))
    {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))} {U : hSpace (d + 1) Ω}
    (hU : IsWeakSolutionDirichlet Ω f U) {u : 𝔼 → ℝ}
    (hUu : SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set 𝔼)] u)
    (hu : ContDiffOnClosure ℝ 2 u Ω) (huc : ContinuousOn u (closure (Ω : Set 𝔼)))
    {g : 𝔼 → ℝ} (hg : ContinuousOn g Ω) (hfg : (f : 𝔼 → ℝ) =ᵐ[volume.restrict (Ω : Set 𝔼)] g) :
    IsClassicalSolutionDirichlet Ω g u :=
  ⟨hu, huc, Elliptic.laplacian_eq_of_isGalerkinSolution_of_continuousOn Ω
    ((isWeakSolutionDirichlet_iff f U).1 hU) hu.contDiffOn hUu hg hfg,
    theorem_9_17_mpr hΩ (by simp) hU.1 hUu huc⟩

end Example1StepD

/-! ### Example 2: the inhomogeneous Dirichlet condition -/

section Example2

variable {N : ℕ}

/-- The space $\mathbb{R}^N$ of the source, `EuclideanSpace ℝ (Fin N)`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

variable {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **Section 9.5** of [brezis2011functional], Example 2, the set $K$. Let
$\Omega \subset \mathbb{R}^N$ be open and let $\tilde g \in H^1(\Omega)$. The set $K$ is
$$K = \{v \in H^1(\Omega) : v - \tilde g \in H_0^1(\Omega)\}.$$

**Generalization.** The source takes $\tilde g \in H^1(\Omega) \cap C(\overline\Omega)$ with
$\tilde g = g$ on $\Gamma$. The definition accepts any $\tilde g \in H^1(\Omega)$.

The set is the backbone's `Elliptic.admissibleSet Ω g`. -/
noncomputable abbrev admissibleSetInhomogeneous (Ω : Opens (EuclideanSpace ℝ (Fin N)))
    (g : hSpace N Ω) : Set (hSpace N Ω) :=
  Elliptic.admissibleSet Ω g

/-- Let $\tilde g, v \in H^1(\Omega)$. Then $v$ belongs to the set $K$ of Example 2 if and only if
$v - \tilde g \in H_0^1(\Omega)$. -/
theorem mem_admissibleSetInhomogeneous_iff {g v : hSpace N Ω} :
    v ∈ admissibleSetInhomogeneous Ω g ↔ v - g ∈ hZeroSpace N Ω :=
  Iff.rfl

/-- **Example 2** of [brezis2011functional], the set $K$. Let $\Omega \subset \mathbb{R}^N$ be open
and let $\tilde g \in H^1(\Omega)$. Then $K$ is a nonempty, closed and convex subset of
$H^1(\Omega)$. Moreover, $K$ depends only on the boundary values of $\tilde g$: let
$\tilde g_2 \in H^1(\Omega)$, and let $k_1, k_2$ be functions continuous on $\overline\Omega$
that equal $\tilde g$ and $\tilde g_2$ almost everywhere on $\Omega$, with $k_1 = k_2$ on
$\Gamma$. Then $\tilde g$ and $\tilde g_2$ define the same set $K$.

The source says: "it follows from Theorem 9.17 that $K$ is independent of the choice of
$\tilde g$ and depends only on $g$". Indeed, $k_1 - k_2 \in H^1(\Omega) \cap C(\overline\Omega)$
vanishes on $\Gamma$, so it lies in $H_0^1(\Omega)$ by Theorem 9.17, (i) ⇒ (ii), which needs no
regularity of $\Omega$. -/
theorem example_9_2 (g : hSpace N Ω) :
    (admissibleSetInhomogeneous Ω g).Nonempty ∧ IsClosed (admissibleSetInhomogeneous Ω g) ∧
    Convex ℝ (admissibleSetInhomogeneous Ω g) ∧
    ∀ (g₂ : hSpace N Ω) {k₁ k₂ : 𝔼 → ℝ},
      SobolevMultiIndex.fn g =ᵐ[volume.restrict (Ω : Set 𝔼)] k₁ →
      SobolevMultiIndex.fn g₂ =ᵐ[volume.restrict (Ω : Set 𝔼)] k₂ →
      ContinuousOn k₁ (closure (Ω : Set 𝔼)) → ContinuousOn k₂ (closure (Ω : Set 𝔼)) →
      EqOn k₁ k₂ (frontier (Ω : Set 𝔼)) →
      admissibleSetInhomogeneous Ω g = admissibleSetInhomogeneous Ω g₂ := by
  refine ⟨Elliptic.admissibleSet_nonempty Ω g, Elliptic.isClosed_admissibleSet Ω g,
    Elliptic.convex_admissibleSet Ω g, fun g₂ k₁ k₂ h₁ h₂ hc₁ hc₂ hΓ ↦ ?_⟩
  refine Elliptic.admissibleSet_eq_of_sub_mem Ω (theorem_9_17_mp (by simp) (g - g₂)
    ((SobolevMultiIndex.fn_sub g g₂).trans (h₁.sub h₂)) (hc₁.sub hc₂) fun x hx ↦ ?_)
  simp only [Pi.sub_apply, Pi.zero_apply, hΓ hx, sub_self]

/-- **Section 9.5** of [brezis2011functional], Example 2, definition of a classical solution. Let
$\Omega \subset \mathbb{R}^N$ be open and let $f, g, u : \mathbb{R}^N \to \mathbb{R}$. The
function $u$ is a **classical solution** of problem (33),
$$-\Delta u + u = f \text{ in } \Omega, \qquad u = g \text{ on } \Gamma,$$
if $u \in C^2(\overline\Omega)$, $-\Delta u(x) + u(x) = f(x)$ for every $x \in \Omega$, and
$u(x) = g(x)$ for every $x \in \Gamma$.

The class $C^2(\overline\Omega)$ is read as in `Brezis.Chapter09.IsClassicalSolutionDirichlet`. -/
def IsClassicalSolutionInhomogeneous (Ω : Opens (EuclideanSpace ℝ (Fin N)))
    (f g u : EuclideanSpace ℝ (Fin N) → ℝ) : Prop :=
  ContDiffOnClosure ℝ 2 u Ω ∧ ContinuousOn u (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) ∧
    (∀ x ∈ Ω, -Δ u x + u x = f x) ∧ EqOn u g (frontier (Ω : Set (EuclideanSpace ℝ (Fin N))))

/-- **Section 9.5** of [brezis2011functional], Example 2, definition of a weak solution. Let
$\Omega \subset \mathbb{R}^N$ be open, let $f \in L^2(\Omega)$ and let
$\tilde g \in H^1(\Omega)$. An element $u \in H^1(\Omega)$ is a **weak solution** of (33) if
$u \in K$ and
$$\int_\Omega (\nabla u \cdot \nabla v + u v) = \int_\Omega f v \quad \text{for all } v \in
  H_0^1(\Omega). \qquad (34)$$

The set $K$ is `Brezis.Chapter09.admissibleSetInhomogeneous Ω g`. -/
def IsWeakSolutionInhomogeneous (Ω : Opens (EuclideanSpace ℝ (Fin N)))
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) (g u : hSpace N Ω) :
    Prop :=
  u ∈ admissibleSetInhomogeneous Ω g ∧ ∀ v ∈ hZeroSpace N Ω,
    ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), ((∑ i, partialDeriv u i x * partialDeriv v i x)
        + SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x)
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), f x * SobolevMultiIndex.fn v x

/-- Let $\Omega \subset \mathbb{R}^N$ be open, let $f \in L^2(\Omega)$ and let
$\tilde g, u \in H^1(\Omega)$. Then $u$ is a weak solution of (33) in the sense of (34) if and
only if $u \in K$ and $a(u, v) = \int_\Omega f v$ for all $v \in H_0^1(\Omega)$, where $a$ is
the backbone's form `Elliptic.laplaceForm Ω` and the right-hand side is `Elliptic.load Ω f`. -/
theorem isWeakSolutionInhomogeneous_iff (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)))
    (g u : hSpace N Ω) :
    IsWeakSolutionInhomogeneous Ω f g u ↔ u ∈ Elliptic.admissibleSet Ω g ∧
      ∀ v ∈ hZeroSpace N Ω, Elliptic.laplaceForm Ω u v = Elliptic.load Ω f v := by
  simp only [IsWeakSolutionInhomogeneous, Elliptic.laplaceForm_apply, Elliptic.load_apply]
  rfl

/-- **Example 2** of [brezis2011functional], Step A: "as above, any classical solution is a weak
solution". Let $\Omega \subset \mathbb{R}^N$ be a bounded open set, let
$f : \mathbb{R}^N \to \mathbb{R}$ be square integrable on $\Omega$, and let
$g : \mathbb{R}^N \to \mathbb{R}$. Let $\tilde g \in H^1(\Omega)$ equal almost everywhere on
$\Omega$ a function $k$ that is continuous on $\overline\Omega$ with $k = g$ on $\Gamma$, and
let $u$ be a classical solution of (33). Then there is $U \in H^1(\Omega)$ whose function equals
$u$ almost everywhere on $\Omega$, and $U$ is a weak solution of (33) for $\tilde g$.

The function $u - \tilde g \in H^1(\Omega) \cap C(\overline\Omega)$ vanishes on $\Gamma$, so it
lies in $H_0^1(\Omega)$ by Theorem 9.17, (i) ⇒ (ii) (`Brezis.Chapter09.theorem_9_17_mp`), which
needs no regularity of $\Omega$. The identity (34) is Step A of Example 1 without its boundary
condition, the backbone's `Elliptic.exists_sobolev_forall_laplaceForm_eq_load_of_classical`. -/
theorem example_9_2_stepA (hb : Bornology.IsBounded (Ω : Set 𝔼)) {G : hSpace N Ω} {k g : 𝔼 → ℝ}
    (hG : SobolevMultiIndex.fn G =ᵐ[volume.restrict (Ω : Set 𝔼)] k)
    (hk : ContinuousOn k (closure (Ω : Set 𝔼))) (hkg : EqOn k g (frontier (Ω : Set 𝔼)))
    {f u : 𝔼 → ℝ} (hu : IsClassicalSolutionInhomogeneous Ω f g u)
    (hf : MemLp f 2 (volume.restrict (Ω : Set 𝔼))) :
    ∃ U : hSpace N Ω, SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set 𝔼)] u ∧
      IsWeakSolutionInhomogeneous Ω (hf.toLp f) G U := by
  obtain ⟨U, hUu, hUw⟩ :=
    Elliptic.exists_sobolev_forall_laplaceForm_eq_load_of_classical Ω hb hu.1 hf hu.2.2.1
  refine ⟨U, hUu, (isWeakSolutionInhomogeneous_iff _ _ _).2 ⟨?_, hUw⟩⟩
  refine mem_admissibleSetInhomogeneous_iff.2 (theorem_9_17_mp (by simp) (U - G)
    ((SobolevMultiIndex.fn_sub U G).trans (hUu.sub hG)) (hu.2.1.sub hk) fun x hx ↦ ?_)
  simp only [Pi.sub_apply, Pi.zero_apply, hu.2.2.2 hx, hkg hx, sub_self]

/-- **Proposition 9.22** of [brezis2011functional]. Let $\Omega \subset \mathbb{R}^N$ be open and
let $\tilde g \in H^1(\Omega)$. For every $f \in L^2(\Omega)$ there is a unique weak solution
$u \in K$ of (33).

The proof is the backbone's `Elliptic.existsUnique_isWeakSolution_inhomogeneous`. The proof in
the source goes through the variational inequality (35)
(`Brezis.Chapter09.proposition_9_22_iff`) and Stampacchia's theorem (Theorem 5.6) on the
nonempty closed convex set $K$ (`Brezis.Chapter09.example_9_2`). -/
theorem proposition_9_22 (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) (g : hSpace N Ω) :
    ∃! u : hSpace N Ω, IsWeakSolutionInhomogeneous Ω f g u := by
  simp only [isWeakSolutionInhomogeneous_iff]
  exact Elliptic.existsUnique_isWeakSolution_inhomogeneous Ω g f

/-- **Proposition 9.22** of [brezis2011functional], the equivalence (34) ⇔ (35) of the proof. Let
$\Omega \subset \mathbb{R}^N$ be open, let $f \in L^2(\Omega)$, let $\tilde g \in H^1(\Omega)$
and let $u \in K$. Then $u$ is a weak solution of (33) if and only if
$$\int_\Omega \nabla u \cdot \nabla (v - u) + \int_\Omega u (v - u) \ge \int_\Omega f (v - u)
  \quad \text{for all } v \in K. \qquad (35)$$

If $u$ is a weak solution, (35) holds with equality. Conversely, $v = u \pm w$ with
$w \in H_0^1(\Omega)$ gives (34). The proof is the backbone's
`Elliptic.isWeakSolution_inhomogeneous_iff_forall_le`. -/
theorem proposition_9_22_iff (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) {g u : hSpace N Ω}
    (hu : u ∈ admissibleSetInhomogeneous Ω g) :
    IsWeakSolutionInhomogeneous Ω f g u ↔ ∀ v ∈ admissibleSetInhomogeneous Ω g,
      ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn (v - u) x
        ≤ (∫ x in (Ω : Set 𝔼), ∑ i, partialDeriv u i x * partialDeriv (v - u) i x)
          + ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn u x * SobolevMultiIndex.fn (v - u) x := by
  rw [isWeakSolutionInhomogeneous_iff, and_iff_right hu,
    Elliptic.isWeakSolution_inhomogeneous_iff_forall_le Ω (Elliptic.laplaceForm Ω)
      (Elliptic.load Ω f) hu]
  simp only [laplaceForm_apply_two, Elliptic.load_apply]

/-- **Proposition 9.22** of [brezis2011functional], the minimization. Let
$\Omega \subset \mathbb{R}^N$ be open, let $f \in L^2(\Omega)$, let $\tilde g \in H^1(\Omega)$
and let $u \in K$. Then $u$ minimizes
$$\frac12 \int_\Omega \bigl(|\nabla v|^2 + v^2\bigr) - \int_\Omega f v$$
over $v \in K$ if and only if $u$ is the weak solution of (33).

The source states ("furthermore") that the weak solution is obtained by this minimum. The proof
is the backbone's `Elliptic.isMinOn_energy_iff_isWeakSolution_inhomogeneous`. -/
theorem proposition_9_22_isMinOn (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) {g u : hSpace N Ω}
    (hu : u ∈ admissibleSetInhomogeneous Ω g) :
    IsMinOn (fun v : hSpace N Ω ↦ (1 / 2 : ℝ) * (∫ x in (Ω : Set 𝔼),
        (∑ i, partialDeriv v i x ^ 2 + SobolevMultiIndex.fn v x ^ 2))
      - ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn v x) (admissibleSetInhomogeneous Ω g) u
      ↔ IsWeakSolutionInhomogeneous Ω f g u := by
  have e : (fun v : hSpace N Ω ↦ (1 / 2 : ℝ) * (∫ x in (Ω : Set 𝔼),
        (∑ i, partialDeriv v i x ^ 2 + SobolevMultiIndex.fn v x ^ 2))
      - ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn v x)
      = (Elliptic.laplaceForm Ω).energy (Elliptic.load Ω f) := by
    funext v
    rw [Elliptic.energy_laplace_apply]
    simp only [sq]
    rfl
  rw [e, isWeakSolutionInhomogeneous_iff, and_iff_right hu]
  exact Elliptic.isMinOn_energy_iff_isWeakSolution_inhomogeneous Ω hu

end Example2

/-! ### Example 3: general elliptic equations of second order -/

section Example3

variable {N : ℕ}

/-- The space $\mathbb{R}^N$ of the source, `EuclideanSpace ℝ (Fin N)`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

variable {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **Section 9.5** of [brezis2011functional], Example 3, the ellipticity condition (36). Let
$\Omega \subset \mathbb{R}^N$ be open, let $a_{ij} : \mathbb{R}^N \to \mathbb{R}$ for
$1 \le i, j \le N$, and let $\alpha \in \mathbb{R}$. The coefficients satisfy the **ellipticity
condition** with the constant $\alpha$ if $\alpha > 0$ and
$$\sum_{i,j} a_{ij}(x) \xi_i \xi_j \ge \alpha |\xi|^2 \quad \text{for all } x \in \Omega \text{
  and all } \xi \in \mathbb{R}^N.$$

The condition holds at every point of $\Omega$. The backbone's condition
`Elliptic.IsUniformlyElliptic` is the same condition almost everywhere, for coefficients in
$L^\infty(\Omega)$; `Brezis.Chapter09.isUniformlyElliptic_of_ellipticityCondition` relates the
two. -/
def ellipticityCondition (Ω : Opens (EuclideanSpace ℝ (Fin N)))
    (a : Fin N → Fin N → EuclideanSpace ℝ (Fin N) → ℝ) (α : ℝ) : Prop :=
  0 < α ∧ ∀ x ∈ Ω, ∀ ξ : EuclideanSpace ℝ (Fin N), α * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, a i j x * ξ i * ξ j

/-- Let $\Omega \subset \mathbb{R}^N$ be open, let $a_{ij} : \mathbb{R}^N \to \mathbb{R}$ satisfy
the ellipticity condition (36) on $\Omega$ with the constant $\alpha$, and let
$A_{ij} \in L^\infty(\Omega)$ equal $a_{ij}$ almost everywhere on $\Omega$. Then the $A_{ij}$
satisfy the backbone's almost-everywhere ellipticity condition
`Elliptic.IsUniformlyElliptic Ω A α`.

The proof is `Elliptic.isUniformlyElliptic_of_forall_mem`. -/
theorem isUniformlyElliptic_of_ellipticityCondition {a : Fin N → Fin N → 𝔼 → ℝ} {α : ℝ}
    (h : ellipticityCondition Ω a α) {A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼))}
    (hA : ∀ i j, (A i j : 𝔼 → ℝ) =ᵐ[volume.restrict (Ω : Set 𝔼)] a i j) :
    Elliptic.IsUniformlyElliptic Ω A α :=
  Elliptic.isUniformlyElliptic_of_forall_mem Ω A h.1 h.2 hA

/-- Let $\Omega \subset \mathbb{R}^N$ be a bounded open set and let
$a : \mathbb{R}^N \to \mathbb{R}$ be continuous on $\overline\Omega$. Then
$a \in L^\infty(\Omega)$.

The proof is `ContinuousOn.memLp_top_restrict_of_isBounded`. -/
theorem memLp_top_of_continuousOn_closure (hb : Bornology.IsBounded (Ω : Set 𝔼)) {a : 𝔼 → ℝ}
    (ha : ContinuousOn a (closure (Ω : Set 𝔼))) : MemLp a ⊤ (volume.restrict (Ω : Set 𝔼)) :=
  ha.memLp_top_restrict_of_isBounded hb Ω.isOpen.measurableSet

/-- **Section 9.5** of [brezis2011functional], Example 3, definition of a classical solution. Let
$\Omega \subset \mathbb{R}^N$ be open and let $a_{ij}, a_0, f, u : \mathbb{R}^N \to \mathbb{R}$
for $1 \le i, j \le N$. The function $u$ is a **classical solution** of problem (37),
$$-\sum_{i,j} \frac{\partial}{\partial x_j}\Bigl(a_{ij} \frac{\partial u}{\partial x_i}\Bigr) +
  a_0 u = f \text{ in } \Omega, \qquad u = 0 \text{ on } \Gamma,$$
if $u \in C^2(\overline\Omega)$, the equation holds at every point of $\Omega$, and $u = 0$ at
every point of $\Gamma$.

The source takes $a_{ij} \in C^1(\overline\Omega)$ and $a_0 \in C(\overline\Omega)$; the
definition puts no condition on the coefficients, and Step A assumes them. The derivative
$\partial_j(a_{ij} \partial_i u)(x)$ is the Fréchet derivative of
$y \mapsto a_{ij}(y) \, Du(y) e_i$ at $x$ applied to $e_j$, where $e_i$ is
`EuclideanSpace.single i 1`. The class $C^2(\overline\Omega)$ is read as in
`Brezis.Chapter09.IsClassicalSolutionDirichlet`. -/
def IsClassicalSolutionElliptic (Ω : Opens (EuclideanSpace ℝ (Fin N)))
    (a : Fin N → Fin N → EuclideanSpace ℝ (Fin N) → ℝ) (a₀ f u : EuclideanSpace ℝ (Fin N) → ℝ) :
    Prop :=
  ContDiffOnClosure ℝ 2 u Ω ∧ ContinuousOn u (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) ∧
    (∀ x ∈ Ω, -(∑ i, ∑ j, fderiv ℝ (fun y ↦ a i j y * fderiv ℝ u y (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single j 1)) + a₀ x * u x = f x) ∧
    EqOn u 0 (frontier (Ω : Set (EuclideanSpace ℝ (Fin N))))

/-- **Section 9.5** of [brezis2011functional], Example 3, definition of a weak solution of (37). Let
$\Omega \subset \mathbb{R}^N$ be open, let $a_{ij}, a_0 : \mathbb{R}^N \to \mathbb{R}$ and let
$f \in L^2(\Omega)$. An element $u \in H^1(\Omega)$ is a **weak solution** of (37) if
$u \in H_0^1(\Omega)$ and
$$\int_\Omega \sum_{i,j} a_{ij} \frac{\partial u}{\partial x_i} \frac{\partial v}{\partial
  x_j} + \int_\Omega a_0 u v = \int_\Omega f v \quad \text{for all } v \in H_0^1(\Omega). \qquad
  (38)$$

The coefficients are functions on $\mathbb{R}^N$, not classes in $L^\infty(\Omega)$.
`Brezis.Chapter09.isWeakSolutionElliptic_iff` relates (38) to the backbone's Galerkin problem. -/
def IsWeakSolutionElliptic (Ω : Opens (EuclideanSpace ℝ (Fin N)))
    (a : Fin N → Fin N → EuclideanSpace ℝ (Fin N) → ℝ) (a₀ : EuclideanSpace ℝ (Fin N) → ℝ)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) (u : hSpace N Ω) : Prop :=
  u ∈ hZeroSpace N Ω ∧ ∀ v ∈ hZeroSpace N Ω,
    (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        ∑ i, ∑ j, a i j x * partialDeriv u i x * partialDeriv v j x)
      + ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          a₀ x * SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), f x * SobolevMultiIndex.fn v x

/-- **Section 9.5** of [brezis2011functional], Example 3, definition of a weak solution of (39). Let
$\Omega \subset \mathbb{R}^N$ be open, let $a_{ij}, a_i, a_0 \in L^\infty(\Omega)$ for
$1 \le i, j \le N$, and let $f \in L^2(\Omega)$. An element $u \in H^1(\Omega)$ is a **weak
solution** of the general problem (39) if $u \in H_0^1(\Omega)$ and
$$\int_\Omega \sum_{i,j} a_{ij} \frac{\partial u}{\partial x_i} \frac{\partial v}{\partial
  x_j} + \int_\Omega \sum_i a_i \frac{\partial u}{\partial x_i} v + \int_\Omega a_0 u v =
  \int_\Omega f v \quad \text{for all } v \in H_0^1(\Omega). \qquad (40)$$

The coefficients $a_{ij}$ are `A i j` and the $a_i$ are `a₁ i`. The bilinear form (41) of the
left-hand side is `Elliptic.generalForm Ω A a₁ a₀`; in general it is not symmetric (footnote
23). -/
def IsWeakSolutionGeneralElliptic (Ω : Opens (EuclideanSpace ℝ (Fin N)))
    (A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (a₁ : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) (u : hSpace N Ω) : Prop :=
  u ∈ hZeroSpace N Ω ∧ ∀ v ∈ hZeroSpace N Ω,
    (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        ∑ i, ∑ j, A i j x * partialDeriv u i x * partialDeriv v j x)
      + (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          ∑ i, a₁ i x * partialDeriv u i x * SobolevMultiIndex.fn v x)
      + ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          a₀ x * SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), f x * SobolevMultiIndex.fn v x

/-- Let $\Omega \subset \mathbb{R}^N$ be open, let $a_{ij}, a_i, a_0 \in L^\infty(\Omega)$, and let
$u, v \in H^1(\Omega)$. The bilinear form (41), `Elliptic.generalForm Ω A a₁ a₀`, is the
left-hand side of (40), written as three integrals:
$$a(u, v) = \int_\Omega \sum_{i,j} a_{ij} \frac{\partial u}{\partial x_i} \frac{\partial
  v}{\partial x_j} + \int_\Omega \sum_i a_i \frac{\partial u}{\partial x_i} v + \int_\Omega a_0
  u v.$$

This restates the backbone's `Elliptic.generalForm_apply_three` with
`Brezis.Chapter09.partialDeriv`. -/
theorem generalForm_apply_three (A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼)))
    (a₁ : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼))) (a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼)))
    (u v : hSpace N Ω) :
    Elliptic.generalForm Ω A a₁ a₀ u v
      = (∫ x in (Ω : Set 𝔼), ∑ i, ∑ j, A i j x * partialDeriv u i x * partialDeriv v j x)
        + (∫ x in (Ω : Set 𝔼), ∑ i, a₁ i x * partialDeriv u i x * SobolevMultiIndex.fn v x)
        + ∫ x in (Ω : Set 𝔼), a₀ x * SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x :=
  Elliptic.generalForm_apply_three Ω A a₁ a₀ u v

/-- Let $\Omega \subset \mathbb{R}^N$ be open, let $a_{ij}, a_i, a_0 \in L^\infty(\Omega)$, let
$f \in L^2(\Omega)$ and let $u \in H^1(\Omega)$. Then $u$ is a weak solution of (39) in the
sense of (40) if and only if $u$ solves the Galerkin problem on $H_0^1(\Omega)$ for the form
`Elliptic.generalForm Ω A a₁ a₀` and the load functional `Elliptic.load Ω f`. -/
theorem isWeakSolutionGeneralElliptic_iff
    (A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼)))
    (a₁ : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼))) (a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼)))
    (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) (u : hSpace N Ω) :
    IsWeakSolutionGeneralElliptic Ω A a₁ a₀ f u ↔
      IsGalerkinSolution (Elliptic.generalForm Ω A a₁ a₀) (Elliptic.load Ω f)
        (hZeroSpace N Ω) u := by
  simp only [IsWeakSolutionGeneralElliptic, IsGalerkinSolution, generalForm_apply_three,
    Elliptic.load_apply]

/-- Let $\Omega \subset \mathbb{R}^N$ be open, let $a_{ij}, a_0 : \mathbb{R}^N \to \mathbb{R}$, and
let $A_{ij}, A_0 \in L^\infty(\Omega)$ equal $a_{ij}$ and $a_0$ almost everywhere on $\Omega$.
Let $f \in L^2(\Omega)$ and $u \in H^1(\Omega)$. Then $u$ is a weak solution of (37) in the
sense of (38) if and only if $u$ solves the Galerkin problem on $H_0^1(\Omega)$ for the form
`Elliptic.generalForm Ω A 0 A₀`, which has no first-order term, and the load functional
`Elliptic.load Ω f`. -/
theorem isWeakSolutionElliptic_iff {a : Fin N → Fin N → 𝔼 → ℝ} {a₀ : 𝔼 → ℝ}
    {A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼))}
    (hA : ∀ i j, (A i j : 𝔼 → ℝ) =ᵐ[volume.restrict (Ω : Set 𝔼)] a i j)
    {A₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼))}
    (hA₀ : (A₀ : 𝔼 → ℝ) =ᵐ[volume.restrict (Ω : Set 𝔼)] a₀)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) (u : hSpace N Ω) :
    IsWeakSolutionElliptic Ω a a₀ f u ↔
      IsGalerkinSolution (Elliptic.generalForm Ω A 0 A₀) (Elliptic.load Ω f)
        (hZeroSpace N Ω) u := by
  have hall : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), ∀ i j, (A i j : 𝔼 → ℝ) x = a i j x :=
    eventually_all.2 fun i ↦ eventually_all.2 fun j ↦ hA i j
  have hzero : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), ∀ i,
      ((0 : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼))) i : 𝔼 → ℝ) x = 0 := by
    filter_upwards [Lp.coeFn_zero ℝ ⊤ (volume.restrict (Ω : Set 𝔼))] with x hx i
    simpa only [Pi.zero_apply] using hx
  have key : ∀ v : hSpace N Ω, Elliptic.generalForm Ω A 0 A₀ u v
      = (∫ x in (Ω : Set 𝔼), ∑ i, ∑ j, a i j x * partialDeriv u i x * partialDeriv v j x)
        + ∫ x in (Ω : Set 𝔼), a₀ x * SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x := by
    intro v
    rw [generalForm_apply_three]
    have e1 : ∫ x in (Ω : Set 𝔼), ∑ i, ∑ j, A i j x * partialDeriv u i x * partialDeriv v j x
        = ∫ x in (Ω : Set 𝔼), ∑ i, ∑ j, a i j x * partialDeriv u i x * partialDeriv v j x :=
      integral_congr_ae (hall.mono fun x hx ↦ by simp only [hx])
    have e2 : ∫ x in (Ω : Set 𝔼),
        ∑ i, ((0 : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼))) i : 𝔼 → ℝ) x
          * partialDeriv u i x * SobolevMultiIndex.fn v x = ∫ x in (Ω : Set 𝔼), (0 : ℝ) :=
      integral_congr_ae (hzero.mono fun x hx ↦ by simp only [hx, zero_mul,
        Finset.sum_const_zero])
    have e3 : ∫ x in (Ω : Set 𝔼), A₀ x * SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x
        = ∫ x in (Ω : Set 𝔼), a₀ x * SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x :=
      integral_congr_ae (hA₀.mono fun x hx ↦ by simp only [hx])
    rw [e1, e2, integral_zero, e3, add_zero]
  simp only [IsWeakSolutionElliptic, IsGalerkinSolution, key, Elliptic.load_apply]

/-- **Example 3** of [brezis2011functional], Step A: "as above, any classical solution is a weak
solution". Let $\Omega \subset \mathbb{R}^N$ be a bounded open set, let
$a_{ij} \in C^1(\overline\Omega)$ and $a_0 \in C(\overline\Omega)$, let
$f : \mathbb{R}^N \to \mathbb{R}$ be square integrable on $\Omega$, and let $u$ be a classical
solution of (37). Then there is $U \in H^1(\Omega)$ whose function equals $u$ almost everywhere
on $\Omega$, and $U$ is a weak solution of (37) in the sense of (38).

Here $a_{ij} \in C^1(\overline\Omega)$ is `ContDiffOnClosure ℝ 1 (a i j) Ω` (footnote 16 of
Section 9.3), and $a_0 \in C(\overline\Omega)$ is the continuity of $a_0$ on $\overline\Omega$.
The proof is the backbone's `Elliptic.isGalerkinSolution_general_of_classical` for the classes
of the coefficients in $L^\infty(\Omega)$, with no first-order term. The function
$u \in H^1(\Omega) \cap C(\overline\Omega)$ vanishes on $\Gamma$, so it lies in $H_0^1(\Omega)$
by Theorem 9.17. For $v \in C_c^1(\Omega)$ the identity (38) is the integration by parts
$\int_\Omega \partial_j(a_{ij} \partial_i u) v = -\int_\Omega a_{ij} \partial_i u \, \partial_j
v$ of the $C^1$ functions $a_{ij} \partial_i u$, and it extends to $H_0^1(\Omega)$ by density. -/
theorem example_9_3_stepA (hb : Bornology.IsBounded (Ω : Set 𝔼)) {a : Fin N → Fin N → 𝔼 → ℝ}
    (ha : ∀ i j, ContDiffOnClosure ℝ 1 (a i j) Ω) {a₀ : 𝔼 → ℝ}
    (ha₀ : ContinuousOn a₀ (closure (Ω : Set 𝔼))) {f u : 𝔼 → ℝ}
    (hu : IsClassicalSolutionElliptic Ω a a₀ f u) (hf : MemLp f 2 (volume.restrict (Ω : Set 𝔼))) :
    ∃ U : hSpace N Ω, SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set 𝔼)] u ∧
      IsWeakSolutionElliptic Ω a a₀ (hf.toLp f) U := by
  have hA := fun i j ↦ (ha i j).memLp_of_isBounded Ω hb ⊤
  have hA₀ := memLp_top_of_continuousOn_closure hb ha₀
  have hzero : ∀ i, ((0 : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼))) i : 𝔼 → ℝ)
      =ᵐ[volume.restrict (Ω : Set 𝔼)] (fun _ ↦ (0 : ℝ)) := fun i ↦ by
    filter_upwards [Lp.coeFn_zero ℝ ⊤ (volume.restrict (Ω : Set 𝔼))] with x hx
    simpa only [Pi.zero_apply] using hx
  have heq : ∀ x ∈ Ω, -(∑ i, ∑ j, fderiv ℝ (fun y ↦ a i j y * fderiv ℝ u y
        (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1))
      + (∑ i, (fun _ : 𝔼 ↦ (0 : ℝ)) x * fderiv ℝ u x (EuclideanSpace.single i 1))
      + a₀ x * u x = f x := fun x hx ↦ by
    simpa only [zero_mul, Finset.sum_const_zero, add_zero] using hu.2.2.1 x hx
  obtain ⟨U, -, hUu, hUw⟩ := Elliptic.isGalerkinSolution_general_of_classical Ω hb hu.1 hu.2.1
    hu.2.2.2 (fun i j ↦ (ha i j).contDiffOn) (fun i j ↦ (hA i j).coeFn_toLp) hzero
    hA₀.coeFn_toLp hf heq
  exact ⟨U, hUu, (isWeakSolutionElliptic_iff (fun i j ↦ (hA i j).coeFn_toLp) hA₀.coeFn_toLp
    _ _).2 hUw⟩

end Example3

section Example3Bounded

variable {d : ℕ}

/-- The space $\mathbb{R}^N$ of the source with $N = d + 1$, `EuclideanSpace ℝ (Fin (d + 1))`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

variable {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **Example 3** of [brezis2011functional], existence and uniqueness. Let $N \ge 1$, let
$\Omega \subset \mathbb{R}^N$ be a bounded open set, let $a_{ij} \in C(\overline\Omega)$ satisfy
the ellipticity condition (36), and let $a_0 \in C(\overline\Omega)$ with $a_0 \ge 0$ in
$\Omega$. Then for every $f \in L^2(\Omega)$ there is a unique weak solution
$u \in H_0^1(\Omega)$ of (37).

**Generalization.** The source assumes $a_{ij} \in C^1(\overline\Omega)$, which only the
classical formulation needs. The statement assumes only $a_{ij} \in C(\overline\Omega)$.

The proof is the Lax–Milgram theorem in $H_0^1(\Omega)$ for the continuous bilinear form of
(38). Its coercivity comes from the ellipticity condition, from $a_0 \ge 0$ and from Poincaré's
inequality (Corollary 9.19). This is the backbone's
`Elliptic.existsUnique_isGalerkinSolution_general_of_nonneg` for the classes of the coefficients
in $L^\infty(\Omega)$. The space $\mathbb{R}^N$ is written with $N = d + 1$. -/
theorem example_9_3 (hb : Bornology.IsBounded (Ω : Set 𝔼)) {a : Fin (d + 1) → Fin (d + 1) → 𝔼 → ℝ}
    (ha : ∀ i j, ContinuousOn (a i j) (closure (Ω : Set 𝔼))) {α : ℝ}
    (hell : ellipticityCondition Ω a α) {a₀ : 𝔼 → ℝ} (ha₀ : ContinuousOn a₀ (closure (Ω : Set 𝔼)))
    (ha₀0 : ∀ x ∈ Ω, 0 ≤ a₀ x) (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) :
    ∃! u : hSpace (d + 1) Ω, IsWeakSolutionElliptic Ω a a₀ f u := by
  obtain ⟨R, hR⟩ := hb.subset_ball 0
  have hA := fun i j ↦ memLp_top_of_continuousOn_closure hb (ha i j)
  have hA₀ := memLp_top_of_continuousOn_closure hb ha₀
  have hnn : 0 ≤ hA₀.toLp a₀ := by
    refine (Lp.coeFn_nonneg _).1 ?_
    filter_upwards [hA₀.coeFn_toLp, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
    rw [hx]
    exact ha₀0 x hxΩ
  simp only [isWeakSolutionElliptic_iff (A := fun i j ↦ (hA i j).toLp (a i j))
    (fun i j ↦ (hA i j).coeFn_toLp) hA₀.coeFn_toLp]
  exact Elliptic.existsUnique_isGalerkinSolution_general_of_nonneg (le_max_right R 0)
    (hR.trans (ball_subset_ball (le_max_left R 0)))
    (isUniformlyElliptic_of_ellipticityCondition hell fun i j ↦ (hA i j).coeFn_toLp) hnn f

/-- **Example 3** of [brezis2011functional], the symmetric case. Let $N \ge 1$, let
$\Omega \subset \mathbb{R}^N$ be a bounded open set, let $a_{ij} \in C(\overline\Omega)$ satisfy
the ellipticity condition (36) with $a_{ij} = a_{ji}$, and let $a_0 \in C(\overline\Omega)$ with
$a_0 \ge 0$ in $\Omega$. Let $f \in L^2(\Omega)$ and $u \in H_0^1(\Omega)$. Then $u$ minimizes
$$\frac12 \int_\Omega \Bigl(\sum_{i,j} a_{ij} \frac{\partial v}{\partial x_i} \frac{\partial
  v}{\partial x_j} + a_0 v^2\Bigr) - \int_\Omega f v$$
over $v \in H_0^1(\Omega)$ if and only if $u$ is the weak solution of (37).

**Generalization.** As in `Brezis.Chapter09.example_9_3`, the coefficients $a_{ij}$ are only
assumed to be continuous on $\overline\Omega$, not of class $C^1(\overline\Omega)$.

The source says that the form (38) is then symmetric and that the weak solution is obtained by
this minimum. The proof is the backbone's
`Elliptic.isMinOn_energy_iff_isGalerkinSolution_general_of_symm`. -/
theorem example_9_3_isMinOn (hb : Bornology.IsBounded (Ω : Set 𝔼))
    {a : Fin (d + 1) → Fin (d + 1) → 𝔼 → ℝ} (ha : ∀ i j, ContinuousOn (a i j) (closure (Ω : Set 𝔼)))
    (hsymm : ∀ i j, a i j = a j i) {α : ℝ} (hell : ellipticityCondition Ω a α) {a₀ : 𝔼 → ℝ}
    (ha₀ : ContinuousOn a₀ (closure (Ω : Set 𝔼))) (ha₀0 : ∀ x ∈ Ω, 0 ≤ a₀ x)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) {u : hSpace (d + 1) Ω}
    (hu : u ∈ hZeroSpace (d + 1) Ω) :
    IsMinOn (fun v : hSpace (d + 1) Ω ↦ (1 / 2 : ℝ) * (∫ x in (Ω : Set 𝔼),
        ((∑ i, ∑ j, a i j x * partialDeriv v i x * partialDeriv v j x)
          + a₀ x * SobolevMultiIndex.fn v x ^ 2))
      - ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn v x) (hZeroSpace (d + 1) Ω) u
      ↔ IsWeakSolutionElliptic Ω a a₀ f u := by
  obtain ⟨R, hR⟩ := hb.subset_ball 0
  have hA := fun i j ↦ memLp_top_of_continuousOn_closure hb (ha i j)
  have hA₀ := memLp_top_of_continuousOn_closure hb ha₀
  have hnn : 0 ≤ hA₀.toLp a₀ := by
    refine (Lp.coeFn_nonneg _).1 ?_
    filter_upwards [hA₀.coeFn_toLp, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
    rw [hx]
    exact ha₀0 x hxΩ
  have hAsymm : ∀ i j, (hA i j).toLp (a i j) = (hA j i).toLp (a j i) := fun i j ↦ by
    simp only [hsymm i j]
  have hall : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), ∀ i j,
      ((hA i j).toLp (a i j) : 𝔼 → ℝ) x = a i j x :=
    eventually_all.2 fun i ↦ eventually_all.2 fun j ↦ (hA i j).coeFn_toLp
  have e : (fun v : hSpace (d + 1) Ω ↦ (1 / 2 : ℝ) * (∫ x in (Ω : Set 𝔼),
        ((∑ i, ∑ j, a i j x * partialDeriv v i x * partialDeriv v j x)
          + a₀ x * SobolevMultiIndex.fn v x ^ 2))
      - ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn v x)
      = (Elliptic.generalForm Ω (fun i j ↦ (hA i j).toLp (a i j)) 0 (hA₀.toLp a₀)).energy
        (Elliptic.load Ω f) := by
    funext v
    rw [SesqForm.energy, Elliptic.generalForm_apply, Elliptic.load_apply]
    simp only [RCLike.re_to_real]
    congr 2
    refine integral_congr_ae ?_
    have hzero : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), ∀ i,
        ((0 : Fin (d + 1) → Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼))) i : 𝔼 → ℝ) x = 0 := by
      filter_upwards [Lp.coeFn_zero ℝ ⊤ (volume.restrict (Ω : Set 𝔼))] with x hx i
      simpa only [Pi.zero_apply] using hx
    filter_upwards [hall, hzero, hA₀.coeFn_toLp] with x hx hx0 hx₀
    simp only [hx, hx0, hx₀, zero_mul, Finset.sum_const_zero, add_zero, sq, mul_assoc]
    rfl
  rw [e, isWeakSolutionElliptic_iff (A := fun i j ↦ (hA i j).toLp (a i j))
    (fun i j ↦ (hA i j).coeFn_toLp) hA₀.coeFn_toLp]
  exact Elliptic.isMinOn_energy_iff_isGalerkinSolution_general_of_symm (le_max_right R 0)
    (hR.trans (ball_subset_ball (le_max_left R 0)))
    (isUniformlyElliptic_of_ellipticityCondition hell fun i j ↦ (hA i j).coeFn_toLp) hAsymm hnn hu

end Example3Bounded

/-! ### Theorem 9.23: the Fredholm alternative -/

section Fredholm

variable {N : ℕ}

/-- The space $\mathbb{R}^N$ of the source, `EuclideanSpace ℝ (Fin N)`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

variable {Ω : Opens (EuclideanSpace ℝ (Fin N))}
  {A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {a₁ : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))} {α : ℝ}

/-- Let $\Omega \subset \mathbb{R}^N$ be open, let $a_{ij}, a_i, a_0 \in L^\infty(\Omega)$ and let
$u \in H^1(\Omega)$. Then $u$ is a weak solution of (40) with $f = 0$ if and only if $u$ belongs
to the backbone's subspace `Elliptic.homogeneousKernel Ω (Elliptic.generalForm Ω A a₁ a₀)` of
$H^1(\Omega)$. -/
theorem mem_homogeneousKernel_iff_isWeakSolutionGeneralElliptic (u : hSpace N Ω) :
    u ∈ Elliptic.homogeneousKernel Ω (Elliptic.generalForm Ω A a₁ a₀) ↔
      IsWeakSolutionGeneralElliptic Ω A a₁ a₀ 0 u := by
  rw [Elliptic.mem_homogeneousKernel_iff_isGalerkinSolution, isWeakSolutionGeneralElliptic_iff]

/-- **Theorem 9.23** of [brezis2011functional] (Fredholm alternative). Let
$\Omega \subset \mathbb{R}^N$ be a bounded open set, let
$a_{ij}, a_i, a_0 \in L^\infty(\Omega)$, and let $(a_{ij})$ satisfy the ellipticity condition
(36) almost everywhere with a constant $\alpha$. Then the solutions $u \in H_0^1(\Omega)$ of
(40) with $f = 0$ form a finite-dimensional vector space, say of dimension $d$. Moreover, there
is a subspace $F \subset L^2(\Omega)$ of dimension $d$ such that for every $f \in L^2(\Omega)$,
$$\text{(40) has a solution} \iff \int_\Omega f v = 0 \text{ for all } v \in F.$$

Footnote 24 calls these $d$ orthogonality conditions. The space of solutions with $f = 0$ is
`Elliptic.homogeneousKernel`
(`Brezis.Chapter09.mem_homogeneousKernel_iff_isWeakSolutionGeneralElliptic`). The proof is the
backbone's `Elliptic.finiteDimensional_ker_general` and
`Elliptic.exists_orthogonality_iff_exists_solution`, as in the source. Gårding's inequality
gives $\lambda$ such that $a(u, v) + \lambda \int_\Omega u v$ is coercive on $H_0^1(\Omega)$.
The solution operator $T : L^2(\Omega) \to L^2(\Omega)$ is compact, because the injection
$H_0^1(\Omega) \subset L^2(\Omega)$ is compact for a bounded $\Omega$ (Theorem 9.16 and Remark
20). Then (40) takes the form $v - \lambda T v = f$ with $v = f + \lambda u$, and the Fredholm
alternative (Theorem 6.6) applies. The proof uses only $|\Omega| < \infty$. -/
theorem theorem_9_23 (hb : Bornology.IsBounded (Ω : Set 𝔼))
    (hA : Elliptic.IsUniformlyElliptic Ω A α) :
    FiniteDimensional ℝ (Elliptic.homogeneousKernel Ω (Elliptic.generalForm Ω A a₁ a₀)) ∧
    ∃ F : Submodule ℝ (Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))), FiniteDimensional ℝ F ∧
      Module.finrank ℝ F
        = Module.finrank ℝ (Elliptic.homogeneousKernel Ω (Elliptic.generalForm Ω A a₁ a₀)) ∧
      ∀ f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)),
        (∃ u, IsWeakSolutionGeneralElliptic Ω A a₁ a₀ f u) ↔
          ∀ v ∈ F, ∫ x in (Ω : Set 𝔼), f x * v x = 0 := by
  refine ⟨Elliptic.finiteDimensional_ker_general Ω hb.measure_lt_top.ne hA, ?_⟩
  obtain ⟨F, hF, hd, h⟩ := Elliptic.exists_orthogonality_iff_exists_solution Ω (a₁ := a₁)
    (a₀ := a₀) hb.measure_lt_top.ne hA
  refine ⟨F, hF, hd, fun f ↦ ?_⟩
  simp only [isWeakSolutionGeneralElliptic_iff, h f, MeasureTheory.L2.inner_eq_integral_mul]

/-- **Remark 23** of [brezis2011functional], first clause. Let $\Omega \subset \mathbb{R}^N$ be a
bounded open set, let $a_{ij}, a_i, a_0 \in L^\infty(\Omega)$, and let $(a_{ij})$ satisfy the
ellipticity condition (36) almost everywhere. Suppose that $u = 0$ is the only solution of (40)
with $f = 0$. Then for every $f \in L^2(\Omega)$ there is a unique solution
$u \in H_0^1(\Omega)$ of (40).

By footnote 25, existence follows from uniqueness by the Fredholm alternative. The proof is the
backbone's `Elliptic.existsUnique_of_ker_eq_bot`. -/
theorem remark_9_23 (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hA : Elliptic.IsUniformlyElliptic Ω A α)
    (h : ∀ u : hSpace N Ω, IsWeakSolutionGeneralElliptic Ω A a₁ a₀ 0 u → u = 0)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) :
    ∃! u : hSpace N Ω, IsWeakSolutionGeneralElliptic Ω A a₁ a₀ f u := by
  simp only [isWeakSolutionGeneralElliptic_iff]
  refine Elliptic.existsUnique_of_ker_eq_bot Ω hb.measure_lt_top.ne hA ?_ f
  rw [Submodule.eq_bot_iff]
  intro u hu
  exact h u ((mem_homogeneousKernel_iff_isWeakSolutionGeneralElliptic u).1 hu)

/-- **Remark 23** of [brezis2011functional], second clause, in the case $a_i = 0$. Let $N \ge 1$,
let $\Omega \subset \mathbb{R}^N$ be a bounded open set, let $a_{ij}, a_0 \in L^\infty(\Omega)$,
let $(a_{ij})$ satisfy the ellipticity condition (36) almost everywhere, and let $a_0 \ge 0$
almost everywhere in $\Omega$. Then for every $f \in L^2(\Omega)$ there is a unique weak
solution $u \in H_0^1(\Omega)$ of (40) with $a_i = 0$.

**Reading.** The source leaves the hypothesis $N \ge 1$ implicit. The constancy argument of
footnote 39 uses $|\mathbb{R}^N| = \infty$, which fails for $N = 0$.

The source proves this case in Section 9.7. The homogeneous problem has only the solution $0$: a
weak solution $u \in H_0^1(\Omega)$ with $f = 0$ satisfies $u \ge 0$ and $-u \ge 0$ almost
everywhere, by the maximum principle for $u \in H_0^1(\Omega)$ (footnote 38; the backbone's
`Elliptic.nonneg_of_mem_zero_general_zero_drift` and
`Elliptic.nonpos_of_mem_zero_general_zero_drift`). Then `Brezis.Chapter09.remark_9_23` applies.
The case of arbitrary $a_i$ rests on Proposition 9.29 in the general case (Gilbarg–Trudinger),
which the source does not prove; it is not formalized. -/
theorem remark_9_23_zero_drift (hN : N ≠ 0) (hb : Bornology.IsBounded (Ω : Set 𝔼))
    (hA : Elliptic.IsUniformlyElliptic Ω A α)
    (ha₀ : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), 0 ≤ a₀ x)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) :
    ∃! u : hSpace N Ω, IsWeakSolutionGeneralElliptic Ω A 0 a₀ f u := by
  refine remark_9_23 hb hA (fun u hu ↦ ?_) f
  rw [isWeakSolutionGeneralElliptic_iff] at hu
  have hf0 : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)),
      ((0 : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) : 𝔼 → ℝ) x = 0 :=
    Lp.coeFn_zero (E := ℝ) (p := 2) (μ := volume.restrict (Ω : Set 𝔼))
  have h1 := Elliptic.nonneg_of_mem_zero_general_zero_drift hN hA ha₀ hu.1 hu.2
    (hf0.mono fun x hx ↦ hx.symm.le)
  have h2 := Elliptic.nonpos_of_mem_zero_general_zero_drift hN hA ha₀ hu.1 hu.2
    (hf0.mono fun x hx ↦ hx.le)
  refine SobolevMultiIndex.ext_of_fn_ae_eq ?_
  have hz : SobolevMultiIndex.fn (0 : hSpace N Ω) =ᵐ[volume.restrict (Ω : Set 𝔼)] 0 :=
    SobolevMultiIndex.fn_zero
  refine Filter.EventuallyEq.trans ?_ hz.symm
  filter_upwards [h1, h2] with x hx1 hx2
  exact le_antisymm hx2 hx1

end Fredholm

/-! ### Example 4: the homogeneous Neumann problem -/

section Example4

variable {N : ℕ}

/-- The space $\mathbb{R}^N$ of the source, `EuclideanSpace ℝ (Fin N)`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

variable {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **Section 9.5** of [brezis2011functional], Example 4, definition of a classical solution. Let
$\Omega \subset \mathbb{R}^N$ be open, let $n : \mathbb{R}^N \to \mathbb{R}^N$ be a vector field
(the outward unit normal on $\Gamma$), and let $f, u : \mathbb{R}^N \to \mathbb{R}$. The
function $u$ is a **classical solution** of problem (44),
$$-\Delta u + u = f \text{ in } \Omega, \qquad \frac{\partial u}{\partial n} = 0 \text{ on }
  \Gamma,$$
if $u \in C^2(\overline\Omega)$, $-\Delta u(x) + u(x) = f(x)$ for every $x \in \Omega$, and
there is a map $g$ from $\mathbb{R}^N$ to the linear forms on $\mathbb{R}^N$ that is continuous
on $\overline\Omega$, equals $Du$ on $\Omega$, and satisfies $g(x)(n(x)) = 0$ for every
$x \in \Gamma$.

The normal derivative $\partial u / \partial n = \nabla u \cdot n$ is read through the
continuous extension $g$ of $Du$ to $\overline\Omega$ that $u \in C^2(\overline\Omega)$
provides; this extension is unique, because $\Omega$ is dense in $\overline\Omega$. The class
$C^2(\overline\Omega)$ is read as in `Brezis.Chapter09.IsClassicalSolutionDirichlet`. The normal
field $n$ is a parameter: the definition does not derive it from a $C^1$ structure of $\Omega$. -/
def IsClassicalSolutionNeumann (Ω : Opens (EuclideanSpace ℝ (Fin N)))
    (n : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (f u : EuclideanSpace ℝ (Fin N) → ℝ) : Prop :=
  ContDiffOnClosure ℝ 2 u Ω ∧ ContinuousOn u (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) ∧
    (∀ x ∈ Ω, -Δ u x + u x = f x) ∧
    ∃ g : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ,
      ContinuousOn g (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) ∧
      EqOn g (fderiv ℝ u) Ω ∧ ∀ x ∈ frontier (Ω : Set (EuclideanSpace ℝ (Fin N))), g x (n x) = 0

/-- **Section 9.5** of [brezis2011functional], Example 4, definition of a weak solution. Let
$\Omega \subset \mathbb{R}^N$ be open and let $f \in L^2(\Omega)$. An element
$u \in H^1(\Omega)$ is a **weak solution** of (44) if
$$\int_\Omega \nabla u \cdot \nabla v + \int_\Omega u v = \int_\Omega f v \quad \text{for all }
  v \in H^1(\Omega). \qquad (45)$$
-/
def IsWeakSolutionNeumann (Ω : Opens (EuclideanSpace ℝ (Fin N)))
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) (u : hSpace N Ω) : Prop :=
  ∀ v : hSpace N Ω,
    (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), ∑ i, partialDeriv u i x * partialDeriv v i x)
      + ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), f x * SobolevMultiIndex.fn v x

/-- Let $\Omega \subset \mathbb{R}^N$ be open, let $f \in L^2(\Omega)$ and let $u \in H^1(\Omega)$.
Then $u$ is a weak solution of (44) in the sense of (45) if and only if $u$ solves the Galerkin
problem on the whole space $H^1(\Omega)$ for the form `Elliptic.laplaceForm Ω` and the load
functional `Elliptic.load Ω f`. -/
theorem isWeakSolutionNeumann_iff (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) (u : hSpace N Ω) :
    IsWeakSolutionNeumann Ω f u ↔
      IsGalerkinSolution (Elliptic.laplaceForm Ω) (Elliptic.load Ω f) ⊤ u := by
  simp only [IsWeakSolutionNeumann, IsGalerkinSolution, Submodule.mem_top, true_and, true_implies,
    laplaceForm_apply_two, Elliptic.load_apply]

/-- **Proposition 9.24** of [brezis2011functional]. Let $\Omega \subset \mathbb{R}^N$ be open. For
every $f \in L^2(\Omega)$ there is a unique weak solution $u \in H^1(\Omega)$ of the Neumann
problem (44).

**Generalization.** The source assumes that $\Omega$ is bounded and of class $C^1$. The proof
does not use this, and the statement holds for every open set.

The proof is the Lax–Milgram theorem in $H^1(\Omega)$, the backbone's
`Elliptic.existsUnique_isGalerkinSolution_neumann`. -/
theorem proposition_9_24 (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) :
    ∃! u : hSpace N Ω, IsWeakSolutionNeumann Ω f u := by
  simp only [isWeakSolutionNeumann_iff]
  exact Elliptic.existsUnique_isGalerkinSolution_neumann Ω f

/-- **Proposition 9.24** of [brezis2011functional], the minimization. Let
$\Omega \subset \mathbb{R}^N$ be open, let $f \in L^2(\Omega)$ and let $u \in H^1(\Omega)$. Then
$u$ minimizes
$$\frac12 \int_\Omega \bigl(|\nabla v|^2 + v^2\bigr) - \int_\Omega f v$$
over $v \in H^1(\Omega)$ if and only if $u$ is the weak solution of (44).

**Generalization.** As in `Brezis.Chapter09.proposition_9_24`, $\Omega$ is any open set.

The source states ("furthermore") that the weak solution is obtained by this minimum. The proof
is the backbone's `Elliptic.isMinOn_energy_iff_isGalerkinSolution_neumann`. -/
theorem proposition_9_24_isMinOn (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) (u : hSpace N Ω) :
    IsMinOn (fun v : hSpace N Ω ↦ (1 / 2 : ℝ) * (∫ x in (Ω : Set 𝔼),
        (∑ i, partialDeriv v i x ^ 2 + SobolevMultiIndex.fn v x ^ 2))
      - ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn v x) univ u
      ↔ IsWeakSolutionNeumann Ω f u := by
  have e : (fun v : hSpace N Ω ↦ (1 / 2 : ℝ) * (∫ x in (Ω : Set 𝔼),
        (∑ i, partialDeriv v i x ^ 2 + SobolevMultiIndex.fn v x ^ 2))
      - ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn v x)
      = (Elliptic.laplaceForm Ω).energy (Elliptic.load Ω f) := by
    funext v
    rw [Elliptic.energy_laplace_apply]
    simp only [sq]
    rfl
  rw [e, isWeakSolutionNeumann_iff]
  exact Elliptic.isMinOn_energy_iff_isGalerkinSolution_neumann Ω u

/-- **Example 4** of [brezis2011functional], Step D, the equation in $\Omega$. Let
$\Omega \subset \mathbb{R}^N$ be open, let $f \in L^2(\Omega)$, and let $U \in H^1(\Omega)$ be a
weak solution of (44) whose function equals almost everywhere on $\Omega$ a function $u$ of
class $C^2$ on $\Omega$. Then $-\Delta u + u = f$ almost everywhere on $\Omega$. If moreover $f$
equals almost everywhere on $\Omega$ a function $g$ continuous on $\Omega$, then
$-\Delta u + u = g$ at every point of $\Omega$.

The proof applies the weak identity (46) to $v \in C_c^1(\Omega)$ and uses Corollary 4.24,
through the backbone's `Elliptic.laplacian_ae_eq_of_forall_testFunction`: a weak solution of the
Neumann problem satisfies in particular the weak identity for all test functions. -/
theorem example_9_4_stepD_interior {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))} {U : hSpace N Ω}
    (hU : IsWeakSolutionNeumann Ω f U) {u : 𝔼 → ℝ}
    (hUu : SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set 𝔼)] u) (hu : ContDiffOn ℝ 2 u Ω) :
    (fun x ↦ -Δ u x + u x) =ᵐ[volume.restrict (Ω : Set 𝔼)] f ∧
      ∀ g : 𝔼 → ℝ, ContinuousOn g Ω → (f : 𝔼 → ℝ) =ᵐ[volume.restrict (Ω : Set 𝔼)] g →
        ∀ x ∈ Ω, -Δ u x + u x = g x := by
  have hUw := (isWeakSolutionNeumann_iff f U).1 hU
  have hae := Elliptic.laplacian_ae_eq_of_forall_testFunction Ω
    (fun V _ ↦ hUw.2 V Submodule.mem_top) hu hUu
  refine ⟨hae, fun g hg hfg ↦ ?_⟩
  exact Measure.eqOn_open_of_ae_eq (hae.trans hfg) Ω.isOpen
    ((Elliptic.continuousOn_laplacian Ω hu).neg.add
      (hu.of_le (by norm_num) : ContDiffOn ℝ 1 u Ω).continuousOn) hg

/-! ### Example 5: unbounded domains -/

/-- **Example 5** of [brezis2011functional], case (a), $\Omega = \mathbb{R}^N$. For every
$f \in L^2(\mathbb{R}^N)$, the equation $-\Delta u + u = f$ in $\mathbb{R}^N$ has a unique weak
solution: there is a unique $u \in H^1(\mathbb{R}^N)$ with
$$\int \nabla u \cdot \nabla v + \int u v = \int f v \quad \text{for all } v \in
  H^1(\mathbb{R}^N).$$

This is `Brezis.Chapter09.proposition_9_24` on $\Omega = \mathbb{R}^N$, which needs no
boundedness. Equivalently it is Theorem 9.21, since $H_0^1(\mathbb{R}^N) = H^1(\mathbb{R}^N)$
(Remark 17). The whole space is the open set `⊤`. -/
theorem example_9_5_a (f : Lp ℝ 2 (volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼))) :
    ∃! u : hSpace N ⊤, IsWeakSolutionNeumann ⊤ f u :=
  proposition_9_24 f

end Example4

/-! ### Example 4 on a bounded $C^1$ domain: Steps A and D through the boundary theory -/

section Example4Boundary

variable {d : ℕ}

/-- The space $\mathbb{R}^N$ of the source with $N = d + 1$, `EuclideanSpace ℝ (Fin (d + 1))`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

variable {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **Example 4** of [brezis2011functional], Step A: every classical solution of the Neumann problem
is a weak solution. Let $N \ge 1$, let $\Omega \subset \mathbb{R}^N$ be a bounded open set of
class $C^1$ with the outward unit normal $n$, let $f : \mathbb{R}^N \to \mathbb{R}$ be square
integrable on $\Omega$, and let $u$ be a classical solution of (44) for $n$. Then there is
$U \in H^1(\Omega)$ whose function equals $u$ almost everywhere on $\Omega$, and $U$ is a weak
solution of (44).

"Of class $C^1$" is the graph form `IsContDiffDomain 1 Ω` of the backbone, which follows from
`Brezis.Chapter09.IsClassC1` by `Brezis.Chapter09.isContDiffDomain_of_isClassC1`, and $n$ is
`hΩ.outwardNormal hb` (`IsContDiffDomain.outwardNormal`). The proof is the one of the source.
First, $u \in H^1(\Omega)$ by `ContDiffOnClosure.memSobolevMultiIndex_of_isBounded`. Green's
formula
$$\int_\Omega (\Delta u) v = \int_\Gamma \frac{\partial u}{\partial n} v \, d\sigma -
  \int_\Omega \nabla u \cdot \nabla v$$
for $u \in C^2(\overline\Omega)$ and $v \in C^1(\overline\Omega)$ is
`BoundaryData.integral_laplacian_mul_add_eq` for the boundary data `hΩ.boundaryData hb`; it
comes from the divergence theorem `IsContDiffDomain.integral_div_eq` for $F = v \nabla u$. Its
boundary term vanishes by the boundary condition, so (45) holds for the restrictions to $\Omega$
of all $v \in C_c^\infty(\mathbb{R}^N)$. These restrictions are dense in $H^1(\Omega)$
(Corollary 9.8, `IsContDiffDomain.hasSmoothDensity`), and both sides of (45) are continuous in
$v$. -/
theorem example_9_4_stepA (hΩ : IsContDiffDomain 1 (Ω : Set 𝔼))
    (hb : Bornology.IsBounded (Ω : Set 𝔼)) {f u : 𝔼 → ℝ}
    (hu : IsClassicalSolutionNeumann Ω (hΩ.outwardNormal hb) f u)
    (hf : MemLp f 2 (volume.restrict (Ω : Set 𝔼))) :
    ∃ U : hSpace (d + 1) Ω, SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set 𝔼)] u ∧
      IsWeakSolutionNeumann Ω (hf.toLp f) U := by
  obtain ⟨hu2, -, heq, g, hg, hge, hg0⟩ := hu
  have hΩo := Ω.isOpen
  have hΩm := hΩo.measurableSet
  have hu1 : ContDiffOnClosure ℝ 1 u Ω := hu2.of_le (by norm_num)
  obtain ⟨U, hU⟩ := (hu1.memSobolevMultiIndex_of_isBounded Ω hb 2).exists_sobolevMultiIndex
  refine ⟨U, hU, (isWeakSolutionNeumann_iff _ _).2 ⟨Submodule.mem_top, fun V _ ↦ ?_⟩⟩
  -- the identity on the smooth restrictions
  have key : ∀ V ∈ SobolevEuclidean.smoothRestrictions (d + 1) 2 Ω,
      Elliptic.laplaceForm Ω U V = Elliptic.load Ω (hf.toLp f) V := by
    rintro V ⟨v, hv, -, hV⟩
    have hv1 : ContDiff ℝ 1 v := hv.of_le (by simp)
    -- Green's formula for the classical `u` against `v`
    have hgreen := (hΩ.boundaryData hb).integral_laplacian_mul_add_eq hu2 hg hge
      hv.continuous.continuousOn (hv1.contDiffOn.contDiffOnClosure hΩo)
    -- the boundary term vanishes
    have hbd : ∫ x, g x ((hΩ.boundaryData hb).ν x) * v x ∂(hΩ.boundaryData hb).σ = 0 := by
      rw [← integral_zero 𝔼 ℝ (μ := (hΩ.boundaryData hb).σ)]
      refine integral_congr_ae ?_
      filter_upwards [(hΩ.boundaryData hb).ae_mem_frontier] with x hx
      rw [IsContDiffDomain.boundaryData_ν, hg0 x hx, zero_mul]
    rw [hbd] at hgreen
    -- the weak derivatives are the classical ones
    have hdU := fun i ↦ Elliptic.weakDeriv_single_ae_eq_fderiv_of_contDiffOn Ω hu1.contDiffOn hU i
    have hdV := fun i ↦ Elliptic.weakDeriv_single_ae_eq_fderiv_of_contDiffOn Ω
      hv1.contDiffOn hV i
    rw [Elliptic.laplaceForm_apply, Elliptic.load_apply]
    -- integrability of the pieces
    have hI₁ : IntegrableOn (fun x ↦ ⟪_root_.gradient u x, _root_.gradient v x⟫_ℝ)
        (Ω : Set 𝔼) := by
      have hc : ContinuousOn (fun x ↦ ⟪(InnerProductSpace.toDualReal 𝔼).symm (g x),
          _root_.gradient v x⟫_ℝ) (closure (Ω : Set 𝔼)) :=
        ((InnerProductSpace.toDualReal 𝔼).symm.continuous.comp_continuousOn hg).inner
          (EuclideanSpace.continuous_gradient hv1).continuousOn
      refine ((hΩ.boundaryData hb).integrableOn_of_continuousOn hc).congr_fun
        (fun x hx ↦ ?_) hΩm
      simp only [gradient_eq_toDualReal_symm, hge hx]
    have hI₂ : Integrable (fun x ↦ u x * v x) (volume.restrict (Ω : Set 𝔼)) :=
      ((Lp.memLp (SobolevMultiIndex.weakDeriv U 0)).integrable_mul
        (Lp.memLp (SobolevMultiIndex.weakDeriv V 0))).congr (hU.mul hV)
    have hI₃ : Integrable (fun x ↦ Δ u x * v x) (volume.restrict (Ω : Set 𝔼)) := by
      refine (((Lp.memLp (SobolevMultiIndex.weakDeriv U 0)).sub hf).integrable_mul
        (Lp.memLp (SobolevMultiIndex.weakDeriv V 0))).congr ?_
      filter_upwards [ae_restrict_mem hΩm, hU, hV] with x hx hUx hVx
      change (SobolevMultiIndex.fn U x - f x) * SobolevMultiIndex.fn V x = _
      rw [hUx, hVx]
      linear_combination (v x) * heq x hx
    -- the left side is `∫ ⟪∇u, ∇v⟫ + ∫ u v`
    have hL : ∫ x in (Ω : Set 𝔼),
        ((∑ i, (SobolevMultiIndex.weakDeriv U (MultiIndexLE.single i) : 𝔼 → ℝ) x
          * (SobolevMultiIndex.weakDeriv V (MultiIndexLE.single i) : 𝔼 → ℝ) x)
          + SobolevMultiIndex.fn U x * SobolevMultiIndex.fn V x)
        = (∫ x in (Ω : Set 𝔼), ⟪_root_.gradient u x, _root_.gradient v x⟫_ℝ)
          + ∫ x in (Ω : Set 𝔼), u x * v x := by
      rw [← integral_add hI₁ hI₂]
      refine integral_congr_ae ?_
      filter_upwards [ae_all_iff.2 hdU, ae_all_iff.2 hdV, hU, hV] with x hxU hxV hUx hVx
      simp only [hxU, hxV, hUx, hVx, EuclideanSpace.inner_gradient_eq_sum]
    -- the right side is `∫ f v = ∫ (−Δu) v + ∫ u v`
    have hR : ∫ x in (Ω : Set 𝔼), (hf.toLp f) x * SobolevMultiIndex.fn V x
        = ∫ x in (Ω : Set 𝔼), f x * v x :=
      integral_congr_ae (hf.coeFn_toLp.mul hV)
    have hF : ∫ x in (Ω : Set 𝔼), f x * v x
        = (∫ x in (Ω : Set 𝔼), -(Δ u x * v x)) + ∫ x in (Ω : Set 𝔼), u x * v x := by
      have hI₃' : Integrable (fun x ↦ -(Δ u x * v x)) (volume.restrict (Ω : Set 𝔼)) := hI₃.neg
      rw [← integral_add hI₃' hI₂]
      refine setIntegral_congr_fun hΩm fun x hx ↦ ?_
      rw [← heq x hx]
      ring
    rw [hL, hR, hF, integral_neg]
    linarith
  -- extend by density
  have h := Continuous.ext_on
    (hΩ.hasSmoothDensity (p := 2) ENNReal.ofNat_ne_top).dense_smoothRestrictions
    (Elliptic.laplaceForm Ω U).continuous (Elliptic.load Ω (hf.toLp f)).continuous key
  exact congrFun h V

/-- **Example 4** of [brezis2011functional], Step D, the boundary condition: a weak solution in
$C^2(\overline\Omega)$ has a vanishing normal derivative on $\Gamma$. Let $N \ge 1$, let
$\Omega \subset \mathbb{R}^N$ be a bounded open set of class $C^1$ with the outward unit normal
$n$, let $f \in L^2(\Omega)$, and let $U \in H^1(\Omega)$ be a weak solution of (44). Suppose
that the function of $U$ equals almost everywhere on $\Omega$ a function
$u \in C^2(\overline\Omega)$, and let $g$ be a map that is continuous on $\overline\Omega$ and
equals $Du$ on $\Omega$. Then $\partial u / \partial n = g(n) = 0$ at every point of $\Gamma$.
If moreover $f$ equals almost everywhere on $\Omega$ a function $f'$ continuous on $\Omega$,
then $u$ is a classical solution of (44) with the datum $f'$.

The map $g$ gives the boundary values of $\nabla u$; `ContDiffOnClosure` only asserts that such
an extension exists. The argument is (47) of the source with $v \in C_c^\infty(\mathbb{R}^N)$.
Green's formula `BoundaryData.integral_laplacian_mul_add_eq` and the equation in $\Omega$
(`Brezis.Chapter09.example_9_4_stepD_interior`) leave $\int_\Gamma (\partial u / \partial n) v
\, d\sigma = 0$ for every such $v$. The function $\partial u / \partial n$ is continuous on
$\Gamma$ (`IsContDiffDomain.continuousOn_outwardNormal`), and every open set that meets $\Gamma$
has positive surface measure (`IsContDiffDomain.boundaryMeasure_pos_of_isOpen`), so
$\partial u / \partial n$ vanishes on $\Gamma$
(`BoundaryData.eqOn_zero_frontier_of_forall_integral_mul_eq_zero`). -/
theorem example_9_4_stepD (hΩ : IsContDiffDomain 1 (Ω : Set 𝔼))
    (hb : Bornology.IsBounded (Ω : Set 𝔼)) {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))}
    {U : hSpace (d + 1) Ω} (hU : IsWeakSolutionNeumann Ω f U) {u : 𝔼 → ℝ}
    (hUu : SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set 𝔼)] u)
    (hu : ContDiffOnClosure ℝ 2 u Ω) (huc : ContinuousOn u (closure (Ω : Set 𝔼)))
    {g : 𝔼 → 𝔼 →L[ℝ] ℝ} (hg : ContinuousOn g (closure (Ω : Set 𝔼)))
    (hge : EqOn g (fderiv ℝ u) Ω) :
    (∀ x ∈ frontier (Ω : Set 𝔼), g x (hΩ.outwardNormal hb x) = 0) ∧
      ∀ f' : 𝔼 → ℝ, ContinuousOn f' Ω → (f : 𝔼 → ℝ) =ᵐ[volume.restrict (Ω : Set 𝔼)] f' →
        IsClassicalSolutionNeumann Ω (hΩ.outwardNormal hb) f' u := by
  have hΩo := Ω.isOpen
  have hΩm := hΩo.measurableSet
  have hu1 : ContDiffOnClosure ℝ 1 u Ω := hu.of_le (by norm_num)
  obtain ⟨hint, hint'⟩ := example_9_4_stepD_interior hU hUu hu.contDiffOn
  -- `∂u/∂n` is continuous on `Γ`
  have hc : ContinuousOn (fun x ↦ g x (hΩ.outwardNormal hb x)) (frontier (Ω : Set 𝔼)) :=
    (hg.mono frontier_subset_closure).clm_apply (hΩ.continuousOn_outwardNormal hb)
  have hbd : ∀ x ∈ frontier (Ω : Set 𝔼), g x (hΩ.outwardNormal hb x) = 0 := by
    refine (hΩ.boundaryData hb).eqOn_zero_frontier_of_forall_integral_mul_eq_zero
      (fun U hU hne ↦ hΩ.boundaryMeasure_pos_of_isOpen hb hU hne) hc fun ψ hψ hψc ↦ ?_
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
    obtain ⟨W, hW⟩ := hψ1.exists_sobolevMultiIndex_of_hasCompactSupport'
      (b := (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis) (p := 2) (Ω := Ω) (μ := volume)
      hψc
    -- Green's formula for the classical `u` against `ψ`
    have hgreen := (hΩ.boundaryData hb).integral_laplacian_mul_add_eq hu hg hge
      hψ.continuous.continuousOn (hψ1.contDiffOn.contDiffOnClosure hΩo)
    -- the weak equation at `W`
    have hweak := hU W
    have hdU := fun i ↦ Elliptic.weakDeriv_single_ae_eq_fderiv_of_contDiffOn Ω hu1.contDiffOn
      hUu i
    have hdW := fun i ↦ Elliptic.weakDeriv_single_ae_eq_fderiv_of_contDiffOn Ω hψ1.contDiffOn
      hW i
    have hI₁ : IntegrableOn (fun x ↦ ⟪_root_.gradient u x, _root_.gradient ψ x⟫_ℝ)
        (Ω : Set 𝔼) := by
      have hc : ContinuousOn (fun x ↦ ⟪(InnerProductSpace.toDualReal 𝔼).symm (g x),
          _root_.gradient ψ x⟫_ℝ) (closure (Ω : Set 𝔼)) :=
        ((InnerProductSpace.toDualReal 𝔼).symm.continuous.comp_continuousOn hg).inner
          (EuclideanSpace.continuous_gradient hψ1).continuousOn
      refine ((hΩ.boundaryData hb).integrableOn_of_continuousOn hc).congr_fun
        (fun x hx ↦ ?_) hΩm
      simp only [gradient_eq_toDualReal_symm, hge hx]
    have hI₂ : Integrable (fun x ↦ u x * ψ x) (volume.restrict (Ω : Set 𝔼)) :=
      ((Lp.memLp (SobolevMultiIndex.weakDeriv U 0)).integrable_mul
        (Lp.memLp (SobolevMultiIndex.weakDeriv W 0))).congr (hUu.mul hW)
    have hI₃ : Integrable (fun x ↦ Δ u x * ψ x) (volume.restrict (Ω : Set 𝔼)) := by
      refine (((Lp.memLp (SobolevMultiIndex.weakDeriv U 0)).sub (Lp.memLp f)).integrable_mul
        (Lp.memLp (SobolevMultiIndex.weakDeriv W 0))).congr ?_
      filter_upwards [hint, hUu, hW] with x hx hUx hWx
      change (SobolevMultiIndex.fn U x - f x) * SobolevMultiIndex.fn W x = _
      rw [hUx, hWx]
      change -Δ u x + u x = f x at hx
      linear_combination (ψ x) * hx
    have hL : (∫ x in (Ω : Set 𝔼), ∑ i, partialDeriv U i x * partialDeriv W i x)
        = ∫ x in (Ω : Set 𝔼), ⟪_root_.gradient u x, _root_.gradient ψ x⟫_ℝ := by
      refine integral_congr_ae ?_
      filter_upwards [ae_all_iff.2 hdU, ae_all_iff.2 hdW] with x hxU hxW
      simp only [partialDeriv, hxU, hxW, EuclideanSpace.inner_gradient_eq_sum]
    have hM : ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn U x * SobolevMultiIndex.fn W x
        = ∫ x in (Ω : Set 𝔼), u x * ψ x := integral_congr_ae (hUu.mul hW)
    have hR : ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn W x
        = (∫ x in (Ω : Set 𝔼), -(Δ u x * ψ x)) + ∫ x in (Ω : Set 𝔼), u x * ψ x := by
      have hI₃' : Integrable (fun x ↦ -(Δ u x * ψ x)) (volume.restrict (Ω : Set 𝔼)) := hI₃.neg
      rw [← integral_add hI₃' hI₂]
      refine integral_congr_ae ?_
      filter_upwards [hint, hW] with x hx hWx
      change -Δ u x + u x = f x at hx
      rw [hWx, ← hx]
      ring
    rw [hL, hM, hR, integral_neg] at hweak
    have hbd : ∫ x, g x ((hΩ.boundaryData hb).ν x) * ψ x ∂(hΩ.boundaryData hb).σ = 0 := by
      linarith
    exact hbd
  exact ⟨hbd, fun f' hf' hff' ↦ ⟨hu, huc, hint' f' hf' hff', g, hg, hge, hbd⟩⟩

end Example4Boundary

section Example5

variable {d : ℕ}

/-- The space $\mathbb{R}^N$ of the source with $N = d + 1$, `EuclideanSpace ℝ (Fin (d + 1))`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

/-- **Example 5** of [brezis2011functional], case (b), $\Omega = \mathbb{R}^N_+$ with the Dirichlet
condition $u(x', 0) = 0$. Let $N \ge 1$. For every $f \in L^2(\mathbb{R}^N_+)$, the problem
$-\Delta u + u = f$ in $\mathbb{R}^N_+$, $u(x', 0) = 0$, has a unique weak solution: there is a
unique $u \in H_0^1(\mathbb{R}^N_+)$ with
$$\int_{\mathbb{R}^N_+} \nabla u \cdot \nabla v + \int_{\mathbb{R}^N_+} u v =
  \int_{\mathbb{R}^N_+} f v \quad \text{for all } v \in H_0^1(\mathbb{R}^N_+).$$

This is `Brezis.Chapter09.theorem_9_21` on the half space, which needs no boundedness. The half
space $\mathbb{R}^N_+ = \{x \in \mathbb{R}^N : x_N > 0\}$ is
`EuclideanSpace.upperHalfSpaceOpens d`, with $N = d + 1$. -/
theorem example_9_5_b
    (f : Lp ℝ 2 (volume.restrict ((EuclideanSpace.upperHalfSpaceOpens d : Opens 𝔼) : Set 𝔼))) :
    ∃! u : hSpace (d + 1) (EuclideanSpace.upperHalfSpaceOpens d),
      IsWeakSolutionDirichlet (EuclideanSpace.upperHalfSpaceOpens d) f u :=
  theorem_9_21 f

/-- **Example 5** of [brezis2011functional], case (c), $\Omega = \mathbb{R}^N_+$ with the Neumann
condition $\frac{\partial u}{\partial x_N}(x', 0) = 0$. Let $N \ge 1$. For every
$f \in L^2(\mathbb{R}^N_+)$, this problem has a unique weak solution: there is a unique
$u \in H^1(\mathbb{R}^N_+)$ with
$$\int_{\mathbb{R}^N_+} \nabla u \cdot \nabla v + \int_{\mathbb{R}^N_+} u v =
  \int_{\mathbb{R}^N_+} f v \quad \text{for all } v \in H^1(\mathbb{R}^N_+).$$

This is `Brezis.Chapter09.proposition_9_24` on the half space $\mathbb{R}^N_+$,
`EuclideanSpace.upperHalfSpaceOpens d`, with $N = d + 1$. -/
theorem example_9_5_c
    (f : Lp ℝ 2 (volume.restrict ((EuclideanSpace.upperHalfSpaceOpens d : Opens 𝔼) : Set 𝔼))) :
    ∃! u : hSpace (d + 1) (EuclideanSpace.upperHalfSpaceOpens d),
      IsWeakSolutionNeumann (EuclideanSpace.upperHalfSpaceOpens d) f u :=
  proposition_9_24 f

end Example5

end Brezis.Chapter09
