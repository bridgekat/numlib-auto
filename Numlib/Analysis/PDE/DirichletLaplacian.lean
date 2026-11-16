/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Distributions.TestFunctionOps
import Numlib.Analysis.ODE.HilleYosida
import Numlib.Analysis.PDE.Bochner
import Numlib.Analysis.PDE.Elliptic.Regularity

/-!
# The Dirichlet Laplacian on $L^2(\Omega)$

Let $\Omega \subseteq \mathbb{R}^N$ be an open set. This file defines the operator $A = -\Delta$ on
$L^2(\Omega)$ with the Dirichlet boundary condition, the operator on which the heat equation and the
wave equation of §10.1 of [brezis2011functional] rest. Write $a_0(u, v) = \int_\Omega \nabla u \cdot
\nabla v$ for $u, v \in H^1(\Omega)$ and $\langle f, g \rangle = \int_\Omega f g$ for the inner
product of $L^2(\Omega)$. An **$H^k$-lift** of $f \in L^2(\Omega)$ is an element of $H^k(\Omega)$
whose $L^2$ class is $f$, and an **$H^1_0$-lift** is an $H^1$-lift that lies in $H^1_0(\Omega)$; a
lift is unique when it exists. The domain of $A$ is the weak one,
$$D(A) = \{u \in H^1_0(\Omega) : \Delta u \in L^2(\Omega)\} = \{u \in H^1_0(\Omega) : \exists\, g
  \in L^2(\Omega),\ a_0(u, \varphi) = \langle g, \varphi \rangle \text{ for all } \varphi \in
  H^1_0(\Omega)\},$$
with $Au = g$. On every open set, $A$ is monotone, symmetric, and satisfies
$R(I + A) = L^2(\Omega)$, which are the claims (i)–(iii) in the proof of Theorem 10.1 of
[brezis2011functional]. Hence $A$ is maximal monotone and self-adjoint, and the Hille–Yosida theory
of chapter 7 applies to it. Maximality is the Dirichlet principle (Theorem 9.21), and no regularity
theory enters.

The regularity theorem 9.25 (`Elliptic.regularity_dirichlet`) identifies the domains on regular open
sets. On a $C^2$ domain with bounded boundary, $D(A) = H^2(\Omega) \cap H^1_0(\Omega)$, and
$\|u\|_{H^2} \le C (\|u\|_{L^2} + \|Au\|_{L^2})$; the inclusion
$H^2(\Omega) \cap H^1_0(\Omega) \subseteq D(A)$ holds on every open set. On a $C^{2\ell}$ domain
with bounded boundary, the higher-order clause of Theorem 9.25
(`Elliptic.regularity_dirichlet_higher_mem`), iterated, gives the continuous injection
$D(A^\ell) \hookrightarrow H^{2\ell}(\Omega)$ and the identification (7) of the book, $D(A^\ell) =
\{u \in H^{2\ell}(\Omega) : u = \Delta u = \dots = \Delta^{\ell - 1} u = 0 \text{ on } \Gamma\}$.
The file also studies the same operator in the Hilbert space $H^1_0(\Omega)$, the operator $A_1$ of
the proof of Theorem 10.2 (a): $A_1$ is maximal monotone and self-adjoint on every open set, and
$D(A_1) \hookrightarrow H^3(\Omega)$ on a $C^3$ domain with bounded boundary.

## Main definitions

* `dirichletLaplacianDomain`: the weak domain $D(A)$, a subspace of $L^2(\Omega)$.
* `dirichletLaplacian`: the Dirichlet Laplacian $A = -\Delta$ with domain $D(A)$, an unbounded
  operator on $L^2(\Omega)$.
* `sobolevLaplacianL`: the weak Laplacian $\Delta w = \sum_i \partial_i^2 w$ as a bounded linear map
  $H^2(\Omega) \to L^2(\Omega)$.
* `dirichletLaplacian.powDomainToSobolevL`: the continuous injection
  $D(A^\ell) \hookrightarrow H^{2\ell}(\Omega)$ on a $C^{2\ell}$ domain with bounded boundary.
* `IsDirichletLaplacianChain`: the boundary conditions
  $u = \Delta u = \dots = \Delta^{\ell - 1} u = 0$ on $\Gamma$ of (7), read without traces.
* `dirichletLaplacianH10`: the operator $A_1$, the Dirichlet Laplacian in the Hilbert space
  $H^1_0(\Omega)$.
* `dirichletLaplacianH10.powDomainOneToSobolevThreeL`: the continuous injection
  $D(A_1) \hookrightarrow H^3(\Omega)$ on a $C^3$ domain with bounded boundary.

## Main results

* `dirichletLaplacian_isMaximalMonotone`: $A$ is maximal monotone on every open set.
* `dirichletLaplacian_isSelfAdjoint`: $A$ is self-adjoint on every open set.
* `mem_dirichletLaplacianDomain_of_sobolev_two`: on every open set,
  $H^2(\Omega) \cap H^1_0(\Omega) \subseteq D(A)$, and $Au = -\Delta u$ there.
* `testFunction_exists_powDomain`: every test function $\varphi$ lies in $D(A^\ell)$ for every
  $\ell$, with $A^j \varphi = (-\Delta)^j \varphi$.
* `dirichletLaplacianDomain_eq_of_isContDiffChartDomain`: on a $C^2$ domain with bounded boundary,
  $D(A) = H^2(\Omega) \cap H^1_0(\Omega)$, with the bound
  $\|u\|_{H^2} \le C (\|u\|_{L^2} + \|Au\|_{L^2})$.
* `dirichletLaplacian_mem_powDomain_iff`: the identification (7) of $D(A^\ell)$ on a $C^{2\ell}$
  domain with bounded boundary.
* `Bochner.ContDiffOnThrough.of_contDiffOnPowDomain`: a curve of class $C^n$ with values in $D(A^j)$
  is of class $C^n$ with values in every space through which the inclusion $D(A^j) \to H$ factors.
* `dirichletLaplacianH10_isMaximalMonotone`: $A_1$ is maximal monotone in $H^1_0(\Omega)$ on every
  open set.
* `dirichletLaplacianH10_isSelfAdjoint`: $A_1$ is self-adjoint in $H^1_0(\Omega)$ on every open set.

## Proof outline

Monotonicity and symmetry come from the identity $\langle Au, v \rangle = a_0(u, v)$ for
$u \in D(A)$ and $v \in H^1_0(\Omega)$. For $R(I + A) = L^2(\Omega)$, Theorem 9.21 gives, for each
$f \in L^2(\Omega)$, a $v \in H^1_0(\Omega)$ with $a_0(v, \varphi) + \langle v, \varphi \rangle =
\langle f, \varphi \rangle$ for all $\varphi \in H^1_0(\Omega)$; then $v \in D(A)$ with
$Av = f - v$. For $u \in D(A)$, the $H^1_0$-lift of $u$ is the weak solution of
$-\Delta v + v = u + Au$, so Theorem 9.25 applies to it. The results on $D(A^\ell)$ iterate this
step with the higher-order clause of Theorem 9.25. Each continuous injection is bounded by the
closed graph theorem.

## Implementation notes

* The open set $\Omega$ is `Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin N))`.
* The space $L^2(\Omega)$ is `MeasureTheory.Lp ℝ 2 (volume.restrict Ω)`.
* The Sobolev space $H^k(\Omega)$ is `SobolevEuclidean N k 2 Ω`.
* The space $H^1_0(\Omega)$ is `SobolevEuclideanZero N 1 2 Ω`.
* The $L^2$ class of $v \in H^k(\Omega)$ is `SobolevMultiIndex.fnL ℝ _ k 2 Ω volume v`.
* For an element $v$ of the type `SobolevEuclideanZero N 1 2 Ω`, the $L^2$ class is
  `SobolevMultiIndexZero.fnL ℝ _ 1 2 Ω volume v`.
* "$f \in L^2(\Omega)$ lies in $H^1_0(\Omega)$" means that $f$ has an $H^1_0$-lift. Every boundary
  condition $u = 0$ on $\Gamma$ of chapter 10 is read in this way.
* $a_0(u, v)$ is `Elliptic.dirichletForm Ω u v`, and the functional
  $\varphi \mapsto \int_\Omega g \varphi$ is `Elliptic.load Ω g`.
* The operator is a Mathlib `LinearPMap`, `L²(Ω) →ₗ.[ℝ] L²(Ω)`. Its domain is defined weakly, not as
  $H^2(\Omega) \cap H^1_0(\Omega)$. This is why the results of chapter 7 apply on every open set,
  and why regularity enters only in the identification of the domain.
* "$\Omega$ is of class $C^k$" is `IsContDiffChartDomain k Ω` (local charts), and "$\Gamma$ is
  bounded" is `Bornology.IsBounded (frontier Ω)`. The results that use these hypotheses are stated
  in dimension $N = d + 1 \ge 1$, the setting of `IsContDiffChartDomain`.
* $D(A^\ell)$ is the Hilbert space `LinearPMap.PowDomain A ℓ` of chapter 7: the tuples
  $(u, Au, \dots, A^\ell u)$ with the norm $(\sum_{j \le \ell} \|A^j u\|^2)^{1/2}$. The coordinate
  $A^j x$ is `LinearPMap.PowDomain.applyL A ℓ j x`, and "$u \in D(A^\ell)$" is
  `∃ x : A.PowDomain ℓ, applyL A ℓ 0 x = u`. The space $D(A)$ with the graph norm is
  `A.PowDomain 1`.
* The passage from the classes $C^k(s; D(A^\ell))$ of chapter 7 to the classes
  $C^k(s; H^{2\ell}(\Omega))$ of curves in Sobolev spaces is
  `Bochner.ContDiffOnThrough.of_contDiffOnPowDomain`.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology InnerProductSpace

noncomputable section

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex Elliptic

/-! ### Continuous linear functionals that agree on the test functions agree on $H^1_0(\Omega)$ -/

/-- Let $L_1, L_2$ be continuous linear functionals on $H^1(\Omega)$ such that
$L_1 \varphi = L_2 \varphi$ for every element $\varphi$ of $H^1(\Omega)$ whose function agrees
almost everywhere on $\Omega$ with a test function. Then $L_1 \varphi = L_2 \varphi$ for every
$\varphi \in H^1_0(\Omega)$.

The elements of $H^1(\Omega)$ given by test functions form `SobolevMultiIndex.testFunctions`.
The proof uses that $H^1_0(\Omega)$ is the closure of the test functions, and that the set where
two continuous maps agree is closed. -/
theorem SobolevEuclideanZero.ext_on_testFunctions {L₁ L₂ : SobolevEuclidean N 1 2 Ω →L[ℝ] ℝ}
    (h : ∀ φ ∈ testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume,
      L₁ φ = L₂ φ)
    {φ : SobolevEuclidean N 1 2 Ω} (hφ : φ ∈ SobolevEuclideanZero N 1 2 Ω) : L₁ φ = L₂ φ := by
  have := Elliptic.apply_eq_zero_of_forall_testFunctions (L := L₁ - L₂)
    (fun ψ hψ ↦ by rw [sub_apply, h ψ hψ, sub_self]) hφ
  rwa [sub_apply, sub_eq_zero] at this

/-! ### The domain $\{u \in H^1_0(\Omega) : \Delta u \in L^2(\Omega)\}$ -/

variable (Ω) in
/-- The **domain of the Dirichlet Laplacian**: the subspace $D(A)$ of $L^2(\Omega)$ of the functions
$f$ that have an $H^1_0$-lift $v$ with a weak Laplacian in $L^2(\Omega)$, that is, for which
there is $g \in L^2(\Omega)$ with
$$\int_\Omega \nabla v \cdot \nabla \varphi = \int_\Omega g \varphi
  \qquad \text{for all } \varphi \in H^1_0(\Omega).$$
The function $g$ is $Af$, the book's $-\Delta f$.

The set is a subspace because the lifts and the functions $g$ add and scale. The lift $v$ is an
element of `SobolevEuclidean N 1 2 Ω` that lies in `SobolevEuclideanZero N 1 2 Ω`, and the two
sides of the identity are `Elliptic.dirichletForm Ω v φ` and `Elliptic.load Ω g φ`. -/
def dirichletLaplacianDomain :
    Submodule ℝ (Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) where
  carrier := {f | ∃ v : SobolevEuclidean N 1 2 Ω, v ∈ SobolevEuclideanZero N 1 2 Ω ∧
    fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v = f ∧
    ∃ g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, dirichletForm Ω v φ = load Ω g φ}
  zero_mem' := ⟨0, Submodule.zero_mem _, map_zero _, 0, fun φ _ ↦ by
    rw [map_zero, zero_apply, load_apply_inner, inner_zero_left]⟩
  add_mem' := by
    rintro f₁ f₂ ⟨v₁, hv₁, hf₁, g₁, hg₁⟩ ⟨v₂, hv₂, hf₂, g₂, hg₂⟩
    refine ⟨v₁ + v₂, add_mem hv₁ hv₂, by rw [map_add, hf₁, hf₂], g₁ + g₂, fun φ hφ ↦ ?_⟩
    rw [dirichletForm_add_left, load_add, hg₁ φ hφ, hg₂ φ hφ]
  smul_mem' := by
    rintro c f ⟨v, hv, hf, g, hg⟩
    refine ⟨c • v, Submodule.smul_mem _ c hv, by rw [map_smul, hf], c • g, fun φ hφ ↦ ?_⟩
    rw [dirichletForm_smul_left, load_smul, hg φ hφ]

/-- A function $f \in L^2(\Omega)$ lies in $D(A)$ if and only if it has an $H^1_0$-lift $v$ for
which there is $g \in L^2(\Omega)$ with $\int_\Omega \nabla v \cdot \nabla \varphi = \int_\Omega
g \varphi$ for all $\varphi \in H^1_0(\Omega)$. This is the definition of
`dirichletLaplacianDomain`, unfolded. -/
theorem mem_dirichletLaplacianDomain_iff
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))} :
    f ∈ dirichletLaplacianDomain Ω ↔ ∃ v : SobolevEuclidean N 1 2 Ω,
      v ∈ SobolevEuclideanZero N 1 2 Ω ∧
      fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v = f ∧
      ∃ g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
        ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, dirichletForm Ω v φ = load Ω g φ :=
  Iff.rfl

/-- **Uniqueness of the weak Laplacian.** Let $g_1, g_2 \in L^2(\Omega)$. If $\int_\Omega g_1
\varphi = \int_\Omega g_2 \varphi$ for every $\varphi \in H^1_0(\Omega)$, then $g_1 = g_2$.

The proof uses that the test functions are dense in $L^2(\Omega)$, through
`SobolevEuclideanZero.toDualL2_injective`. -/
theorem eq_of_forall_load_eq
    {g₁ g₂ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (h : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, load Ω g₁ φ = load Ω g₂ φ) : g₁ = g₂ := by
  refine SobolevEuclideanZero.toDualL2_injective (ContinuousLinearMap.ext fun v ↦ ?_)
  exact h v v.2

/-- Two elements of $H^1(\Omega)$ with the same $L^2$ class are equal: the inclusion
$H^1(\Omega) \to L^2(\Omega)$ is injective. In particular, an $H^1_0$-lift is unique when it
exists. -/
theorem eq_of_fnL_eq {v₁ v₂ : SobolevEuclidean N 1 2 Ω}
    (h : fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v₁
      = fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v₂) : v₁ = v₂ :=
  SobolevMultiIndex.fnL_injective h

/-! ### The operator -/

variable (Ω) in
/-- The value of the Dirichlet Laplacian at $f \in L^2(\Omega)$. For $f \in D(A)$, it is a function
$g \in L^2(\Omega)$ as in the definition of `dirichletLaplacianDomain`, chosen; for
$f \notin D(A)$, it is $0$.

By `eq_dirichletLaplacianApply`, the function $g$ is unique, so the choice has no effect. -/
def dirichletLaplacianApply (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  open Classical in
  if hf : f ∈ dirichletLaplacianDomain Ω then Classical.choose (Classical.choose_spec hf).2.2
  else 0

/-- Let $f \in D(A)$ and let $g$ be `dirichletLaplacianApply Ω f`. Then $f$ has an $H^1_0$-lift $v$
with
$$\int_\Omega \nabla v \cdot \nabla \varphi = \int_\Omega g \varphi
  \qquad \text{for all } \varphi \in H^1_0(\Omega).$$
-/
theorem dirichletLaplacianApply_spec
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hf : f ∈ dirichletLaplacianDomain Ω) :
    ∃ v : SobolevEuclidean N 1 2 Ω, v ∈ SobolevEuclideanZero N 1 2 Ω ∧
      fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v = f ∧
      ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω,
        dirichletForm Ω v φ = load Ω (dirichletLaplacianApply Ω f) φ := by
  refine ⟨Classical.choose hf, (Classical.choose_spec hf).1, (Classical.choose_spec hf).2.1, ?_⟩
  unfold dirichletLaplacianApply
  rw [dite_eq_left hf]
  exact Classical.choose_spec (Classical.choose_spec hf).2.2

/-- **Every weak Laplacian is the value of the operator.** Let $f \in L^2(\Omega)$, let $v$ be an
$H^1_0$-lift of $f$, and let $g \in L^2(\Omega)$ satisfy $\int_\Omega \nabla v \cdot \nabla
\varphi = \int_\Omega g \varphi$ for all $\varphi \in H^1_0(\Omega)$. Then $g$ is
`dirichletLaplacianApply Ω f`. -/
theorem eq_dirichletLaplacianApply
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    {v : SobolevEuclidean N 1 2 Ω} (hv : v ∈ SobolevEuclideanZero N 1 2 Ω)
    (hvf : fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v = f)
    {g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hg : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, dirichletForm Ω v φ = load Ω g φ) :
    g = dirichletLaplacianApply Ω f := by
  have hf : f ∈ dirichletLaplacianDomain Ω := ⟨v, hv, hvf, g, hg⟩
  obtain ⟨v', hv', hv'f, hg'⟩ := dirichletLaplacianApply_spec hf
  obtain rfl : v' = v := eq_of_fnL_eq (hv'f.trans hvf.symm)
  exact eq_of_forall_load_eq fun φ hφ ↦ (hg φ hφ).symm.trans (hg' φ hφ)

/-- For $f_1, f_2 \in D(A)$, the value of `dirichletLaplacianApply Ω` at $f_1 + f_2$ is the sum of
its values at $f_1$ and at $f_2$. -/
theorem dirichletLaplacianApply_add
    {f₁ f₂ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (h₁ : f₁ ∈ dirichletLaplacianDomain Ω) (h₂ : f₂ ∈ dirichletLaplacianDomain Ω) :
    dirichletLaplacianApply Ω (f₁ + f₂)
      = dirichletLaplacianApply Ω f₁ + dirichletLaplacianApply Ω f₂ := by
  obtain ⟨v₁, hv₁, hf₁, hg₁⟩ := dirichletLaplacianApply_spec h₁
  obtain ⟨v₂, hv₂, hf₂, hg₂⟩ := dirichletLaplacianApply_spec h₂
  refine (eq_dirichletLaplacianApply (v := v₁ + v₂) (add_mem hv₁ hv₂)
    (by rw [map_add, hf₁, hf₂]) fun φ hφ ↦ ?_).symm
  rw [dirichletForm_add_left, load_add, hg₁ φ hφ, hg₂ φ hφ]

/-- For $f \in D(A)$ and $c \in \mathbb{R}$, the value of `dirichletLaplacianApply Ω` at $c f$ is
$c$ times its value at $f$. -/
theorem dirichletLaplacianApply_smul (c : ℝ)
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (h : f ∈ dirichletLaplacianDomain Ω) :
    dirichletLaplacianApply Ω (c • f) = c • dirichletLaplacianApply Ω f := by
  obtain ⟨v, hv, hf, hg⟩ := dirichletLaplacianApply_spec h
  refine (eq_dirichletLaplacianApply (v := c • v) (Submodule.smul_mem _ c hv)
    (by rw [map_smul, hf]) fun φ hφ ↦ ?_).symm
  rw [dirichletForm_smul_left, load_smul, hg φ hφ]

/-- The value of `dirichletLaplacianApply Ω` at $0$ is $0$. -/
theorem dirichletLaplacianApply_zero : dirichletLaplacianApply Ω 0 = 0 :=
  (eq_dirichletLaplacianApply (v := 0) (Submodule.zero_mem _)
    (map_zero (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume)) fun φ _ ↦ by
      rw [map_zero, zero_apply, load_apply_inner, inner_zero_left]).symm

variable (Ω) in
/-- The **Dirichlet Laplacian** $A = -\Delta$ on $L^2(\Omega)$, as an unbounded operator. Its domain
is $D(A) = \{u \in H^1_0(\Omega) : \Delta u \in L^2(\Omega)\}$ (`dirichletLaplacianDomain`), and
for $u \in D(A)$, $Au$ is the weak Laplacian: the unique $Au \in L^2(\Omega)$ with
$$\int_\Omega \nabla u \cdot \nabla \varphi = \int_\Omega (Au) \varphi
  \qquad \text{for all } \varphi \in H^1_0(\Omega),$$
where $\nabla u$ is the gradient of the $H^1_0$-lift of $u$. This is the operator of the proof
of Theorem 10.1 of [brezis2011functional].

The operator is a Mathlib `LinearPMap` whose values are `dirichletLaplacianApply`. On a $C^2$
domain with bounded boundary, the domain is $H^2(\Omega) \cap H^1_0(\Omega)$
(`dirichletLaplacianDomain_eq_of_isContDiffChartDomain`). On an arbitrary open set, the operator
is the Friedrichs extension, and the three claims (i)–(iii) of the book hold for it without any
regularity of $\Omega$. -/
def dirichletLaplacian : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →ₗ.[ℝ]
    Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) where
  domain := dirichletLaplacianDomain Ω
  toFun :=
    { toFun := fun f ↦ dirichletLaplacianApply Ω f
      map_add' := fun f₁ f₂ ↦ dirichletLaplacianApply_add f₁.2 f₂.2
      map_smul' := fun c f ↦ dirichletLaplacianApply_smul c f.2 }

/-- The domain of `dirichletLaplacian Ω` is `dirichletLaplacianDomain Ω`. -/
@[simp]
theorem dirichletLaplacian_domain : (dirichletLaplacian Ω).domain = dirichletLaplacianDomain Ω :=
  rfl

/-- At $f$ in its domain, `dirichletLaplacian Ω` takes the value `dirichletLaplacianApply Ω f`. -/
theorem dirichletLaplacian_apply (f : (dirichletLaplacian Ω).domain) :
    dirichletLaplacian Ω f = dirichletLaplacianApply Ω f :=
  rfl

/-- **$Af$ is the only weak Laplacian of $f$.** Let $f \in D(A)$, let $v$ be an $H^1_0$-lift of $f$,
and let $g \in L^2(\Omega)$ satisfy $\int_\Omega \nabla v \cdot \nabla \varphi = \int_\Omega g
\varphi$ for all $\varphi \in H^1_0(\Omega)$. Then $Af = g$. -/
theorem dirichletLaplacian_apply_unique (f : (dirichletLaplacian Ω).domain)
    {v : SobolevEuclidean N 1 2 Ω} (hv : v ∈ SobolevEuclideanZero N 1 2 Ω)
    (hvf : fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v = f)
    {g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hg : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, dirichletForm Ω v φ = load Ω g φ) :
    dirichletLaplacian Ω f = g :=
  (eq_dirichletLaplacianApply hv hvf hg).symm

/-- **The defining identity of $A$.** Let $f \in D(A)$ and let $v$ be an $H^1_0$-lift of $f$. Then
for every $\varphi \in H^1_0(\Omega)$,
$$\langle Af, \varphi \rangle = \int_\Omega \nabla v \cdot \nabla \varphi.$$

On the left, $\varphi$ stands for its $L^2$ class `SobolevMultiIndex.fnL ℝ _ 1 2 Ω volume φ`;
the right side is `Elliptic.dirichletForm Ω v φ`. -/
theorem dirichletLaplacian_inner_eq_dirichletForm (f : (dirichletLaplacian Ω).domain)
    {v : SobolevEuclidean N 1 2 Ω} (hv : v ∈ SobolevEuclideanZero N 1 2 Ω)
    (hvf : fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v = f)
    {φ : SobolevEuclidean N 1 2 Ω} (hφ : φ ∈ SobolevEuclideanZero N 1 2 Ω) :
    ⟪dirichletLaplacian Ω f, fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume φ⟫_ℝ
      = dirichletForm Ω v φ := by
  obtain ⟨v', hv', hv'f, hg'⟩ := dirichletLaplacianApply_spec f.2
  obtain rfl : v' = v := eq_of_fnL_eq (hv'f.trans hvf.symm)
  rw [dirichletLaplacian_apply]
  exact (hg' φ hφ).symm

/-- Every $f \in D(A)$ has an $H^1_0$-lift: there is $v \in H^1(\Omega)$ with $v \in H^1_0(\Omega)$
whose $L^2$ class is $f$. -/
theorem dirichletLaplacian_exists_lift (f : (dirichletLaplacian Ω).domain) :
    ∃ v : SobolevEuclidean N 1 2 Ω, v ∈ SobolevEuclideanZero N 1 2 Ω ∧
      fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v = f := by
  obtain ⟨v, hv, hvf, -⟩ := dirichletLaplacianApply_spec f.2
  exact ⟨v, hv, hvf⟩

/-- Let $f \in D(A)$ and let $v$ be an $H^1_0$-lift of $f$. Then
$$\langle Af, f \rangle = \int_\Omega |\nabla v|^2.$$
This is the identity $(Au, u) = \int |\nabla u|^2$ in the proof of Theorem 10.1 of
[brezis2011functional]. -/
theorem dirichletLaplacian_inner_self_eq_dirichletForm (f : (dirichletLaplacian Ω).domain)
    {v : SobolevEuclidean N 1 2 Ω} (hv : v ∈ SobolevEuclideanZero N 1 2 Ω)
    (hvf : fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v = f) :
    ⟪dirichletLaplacian Ω f, (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))⟫_ℝ
      = dirichletForm Ω v v := by
  rw [← hvf]
  exact dirichletLaplacian_inner_eq_dirichletForm f hv hvf hv

/-- **$A$ is monotone.** For every $f \in D(A)$, $\langle Af, f \rangle \ge 0$. This is claim (i) in
the proof of Theorem 10.1 of [brezis2011functional]. -/
theorem dirichletLaplacian_inner_self_nonneg (f : (dirichletLaplacian Ω).domain) :
    0 ≤ ⟪dirichletLaplacian Ω f,
      (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))⟫_ℝ := by
  obtain ⟨v, hv, hvf⟩ := dirichletLaplacian_exists_lift f
  rw [dirichletLaplacian_inner_self_eq_dirichletForm f hv hvf]
  exact dirichletForm_self_nonneg Ω v

/-- **The Dirichlet Laplacian is monotone** in the sense of chapter 7 of [brezis2011functional]:
$\langle Au, u \rangle \ge 0$ for every $u \in D(A)$.

Monotonicity is `LinearPMap.IsMonotone`. -/
theorem dirichletLaplacian_isMonotone : (dirichletLaplacian Ω).IsMonotone := fun f ↦ by
  simpa using dirichletLaplacian_inner_self_nonneg f

/-- **$A$ is symmetric.** For all $f, g \in D(A)$, $\langle Af, g \rangle = \langle f, Ag \rangle$.
This is claim (iii) in the proof of Theorem 10.1 of [brezis2011functional].

Both sides equal $\int_\Omega \nabla v \cdot \nabla w$ for the $H^1_0$-lifts $v$ of $f$ and $w$
of $g$. Symmetry is Mathlib's `LinearPMap.IsFormalAdjoint` of $A$ with itself. -/
theorem dirichletLaplacian_isFormalAdjoint :
    (dirichletLaplacian Ω).IsFormalAdjoint (dirichletLaplacian Ω) := fun f g ↦ by
  obtain ⟨v, hv, hvf⟩ := dirichletLaplacian_exists_lift f
  obtain ⟨w, hw, hwg⟩ := dirichletLaplacian_exists_lift g
  rw [← hwg, dirichletLaplacian_inner_eq_dirichletForm f hv hvf hw, real_inner_comm, ← hvf,
    dirichletLaplacian_inner_eq_dirichletForm g hw hwg hv]
  exact (dirichletForm_isHermitian Ω w v).symm.trans (by simp)

/-! ### Maximality: $R(\lambda I + A) = L^2(\Omega)$ -/

/-- **$R(I + A) = L^2(\Omega)$.** For every $f \in L^2(\Omega)$ there is $u \in D(A)$ with
$u + Au = f$. This is claim (ii) in the proof of Theorem 10.1 of [brezis2011functional].

The Dirichlet principle (Theorem 9.21 of [brezis2011functional],
`Elliptic.existsUnique_isGalerkinSolution_laplace`) gives $v \in H^1_0(\Omega)$ with
$\int_\Omega \nabla v \cdot \nabla \varphi + \int_\Omega v \varphi = \int_\Omega f \varphi$ for
all $\varphi \in H^1_0(\Omega)$. Then the $L^2$ class $u$ of $v$ lies in $D(A)$, with
$Au = f - u$. No regularity of $\Omega$ is needed, because the domain is the weak one. -/
theorem dirichletLaplacian_exists_add_apply_eq
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ∃ u : (dirichletLaplacian Ω).domain,
      (u : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) + dirichletLaplacian Ω u
        = f := by
  obtain ⟨v, hv⟩ := (existsUnique_isGalerkinSolution_laplace Ω f).exists
  have heq := dirichletForm_eq_load_sub_of_isGalerkinSolution_laplace hv
  have hmem : fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v
      ∈ dirichletLaplacianDomain Ω := ⟨v, hv.1, rfl, f - weakDeriv v 0, heq⟩
  refine ⟨⟨_, hmem⟩, ?_⟩
  rw [dirichletLaplacian_apply_unique ⟨_, hmem⟩ hv.1 rfl heq]
  change fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v + (f - weakDeriv v 0) = f
  rw [fnL_eq_weakDeriv_zero]
  abel

/-- **The Dirichlet Laplacian is maximal monotone** on every open set $\Omega$: it is monotone, and
$R(I + A) = L^2(\Omega)$. These are claims (i) and (ii) in the proof of Theorem 10.1 of
[brezis2011functional].

Maximal monotonicity is `LinearPMap.IsMaximalMonotone`. -/
theorem dirichletLaplacian_isMaximalMonotone : (dirichletLaplacian Ω).IsMaximalMonotone :=
  ⟨dirichletLaplacian_isMonotone, dirichletLaplacian_exists_add_apply_eq⟩

/-- Let $\lambda > 0$. For every $f \in L^2(\Omega)$ there is $u \in D(A)$ with
$\lambda u + Au = f$, so $R(\lambda I + A) = L^2(\Omega)$.

This is part (c) of Proposition 7.1 of [brezis2011functional], applied to the maximal monotone
operator $A$. -/
theorem dirichletLaplacian_exists_smul_add_apply_eq {c : ℝ} (hc : 0 < c)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ∃ u : (dirichletLaplacian Ω).domain,
      c • (u : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
        + dirichletLaplacian Ω u = f := by
  obtain ⟨u, hu⟩ := dirichletLaplacian_isMaximalMonotone.exists_add_smul_eq (inv_pos.2 hc)
    (c⁻¹ • f)
  refine ⟨u, ?_⟩
  have := congrArg (fun z ↦ c • z) hu
  simp only [smul_add, smul_smul, mul_inv_cancel₀ hc.ne', one_smul] at this
  simpa [mul_inv_cancel₀ hc.ne'] using this

/-- Let $\lambda > 0$. The range of $\lambda I + A$ is $L^2(\Omega)$.

This is the book's form $R(\lambda I + A) = L^2(\Omega)$ of
`dirichletLaplacian_exists_smul_add_apply_eq`. Here Mathlib's `+ᵥ` adds the linear map
$\lambda I$ to the partial map $A$. -/
theorem dirichletLaplacian_range_smul_id_vadd_eq_top {c : ℝ} (hc : 0 < c) :
    LinearMap.range ((c • (LinearMap.id :
      Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →ₗ[ℝ]
        Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))) +ᵥ
        dirichletLaplacian Ω).toFun = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro f
  obtain ⟨u, hu⟩ := dirichletLaplacian_exists_smul_add_apply_eq hc f
  exact ⟨u, hu⟩

/-- The Dirichlet Laplacian is a closed operator: its graph is closed in
$L^2(\Omega) \times L^2(\Omega)$. This follows from Proposition 7.1 of [brezis2011functional],
because $A$ is maximal monotone. -/
theorem dirichletLaplacian_isClosed : (dirichletLaplacian Ω).IsClosed :=
  dirichletLaplacian_isMaximalMonotone.isClosed

/-- The domain $D(A)$ of the Dirichlet Laplacian is dense in $L^2(\Omega)$. This follows from
Proposition 7.1 of [brezis2011functional], because $A$ is maximal monotone. -/
theorem dirichletLaplacian_dense_domain :
    Dense ((dirichletLaplacian Ω).domain :
      Set (Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))) :=
  dirichletLaplacian_isMaximalMonotone.dense_domain

/-- **The Dirichlet Laplacian is self-adjoint** on every open set: $A^* = A$. This is claim (iii) in
the proof of Theorem 10.1 of [brezis2011functional].

Self-adjointness is Mathlib's `IsSelfAdjoint` for `LinearPMap.adjoint`. The proof applies
Proposition 7.6 of [brezis2011functional] to the symmetric maximal monotone operator $A$.
Self-adjointness is the hypothesis of Theorem 7.7 that makes every $u_0 \in L^2(\Omega)$ an
admissible initial datum for the heat equation. -/
theorem dirichletLaplacian_isSelfAdjoint : IsSelfAdjoint (dirichletLaplacian Ω) :=
  dirichletLaplacian_isMaximalMonotone.isSelfAdjoint_of_isFormalAdjoint
    dirichletLaplacian_isFormalAdjoint

/-! ### The $H^1_0$-lift of $D(A)$ as a bounded operator -/

section SobolevZeroLift

open LinearPMap LinearPMap.PowDomain

/-- Every $f \in D(A)$ has an $H^1_0$-lift that is an element of the type $H^1_0(\Omega)$: there is
$v \in H^1_0(\Omega)$ whose $L^2$ class is $f$.

Here $v$ is an element of the type `SobolevEuclideanZero N 1 2 Ω`; in
`dirichletLaplacian_exists_lift` it is an element of $H^1(\Omega)$ with a membership proof. -/
theorem dirichletLaplacian_exists_sobolevZero_lift (f : (dirichletLaplacian Ω).domain) :
    ∃ v : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v
        = f := by
  obtain ⟨v, hv, hvf⟩ := dirichletLaplacian_exists_lift f
  exact ⟨⟨v, hv⟩, hvf⟩

variable (Ω) in
/-- **The $H^1_0$-lift as a bounded linear map** $D(A) \to H^1_0(\Omega)$, on the Hilbert space
$D(A)$ with the graph norm: it takes $u \in D(A)$ to the element of $H^1_0(\Omega)$ whose $L^2$
class is $u$.

The domain is `LinearPMap.PowDomain A 1`, and the map takes $x$ to the lift of its coordinate
$A^0 x$; `fnL_sobolevZeroLiftL` is its defining property. The map is bounded by the closed graph
theorem (`exists_continuousLinearMap_comp_eq_of_injective`). It turns curves with values in
$D(A)$ into curves with values in $H^1_0(\Omega)$. -/
def dirichletLaplacian.sobolevZeroLiftL :
    (dirichletLaplacian Ω).PowDomain 1 →L[ℝ] SobolevEuclideanZero N 1 2 Ω :=
  haveI : CompleteSpace ((dirichletLaplacian Ω).PowDomain 1) :=
    dirichletLaplacian_isClosed.completeSpace_powDomain 1
  Classical.choose (exists_continuousLinearMap_comp_eq_of_injective
    (J := SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume)
    SobolevMultiIndexZero.fnL_injective (S := applyL (dirichletLaplacian Ω) 1 0)
    fun x ↦ dirichletLaplacian_exists_sobolevZero_lift ⟨_, applyL_mem_domain x 0⟩)

/-- For $x \in D(A)$ with the graph norm, the $L^2$ class of
`dirichletLaplacian.sobolevZeroLiftL Ω x` is the coordinate $A^0 x$, that is, the function $x$
itself. -/
theorem fnL_sobolevZeroLiftL (x : (dirichletLaplacian Ω).PowDomain 1) :
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
      (dirichletLaplacian.sobolevZeroLiftL Ω x) = applyL (dirichletLaplacian Ω) 1 0 x :=
  haveI : CompleteSpace ((dirichletLaplacian Ω).PowDomain 1) :=
    dirichletLaplacian_isClosed.completeSpace_powDomain 1
  Classical.choose_spec (exists_continuousLinearMap_comp_eq_of_injective
    (J := SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume)
    SobolevMultiIndexZero.fnL_injective (S := applyL (dirichletLaplacian Ω) 1 0)
    fun x ↦ dirichletLaplacian_exists_sobolevZero_lift ⟨_, applyL_mem_domain x 0⟩) x

/-- Let $f \in D(A)$ and let $v \in H^1_0(\Omega)$ be its $H^1_0$-lift. Then
$$\|v\|_{H^1}^2 = \|f\|_{L^2}^2 + \langle Af, f \rangle.$$

The proof combines $\|v\|_{H^1}^2 = \|v\|_{L^2}^2 + \int_\Omega |\nabla v|^2$
(`Elliptic.laplaceForm_eq_innerSL`) with $\langle Af, f \rangle = \int_\Omega |\nabla v|^2$. -/
theorem dirichletLaplacian_norm_sq_lift_eq (f : (dirichletLaplacian Ω).domain)
    {v : SobolevEuclideanZero N 1 2 Ω}
    (hv : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v
      = f) :
    ‖v‖ ^ 2 = ‖(f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))‖ ^ 2
      + ⟪dirichletLaplacian Ω f,
        (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))⟫_ℝ := by
  have h1 : ‖v‖ ^ 2 = ‖(v : SobolevEuclidean N 1 2 Ω)‖ ^ 2 := by rw [Submodule.norm_coe]
  have h2 := Elliptic.norm_sq_eq Ω (v : SobolevEuclidean N 1 2 Ω)
  have h3 := dirichletForm_self_eq Ω (v : SobolevEuclidean N 1 2 Ω)
  have h4 := dirichletLaplacian_inner_self_eq_dirichletForm f v.2 hv
  have h5 : weakDeriv (v : SobolevEuclidean N 1 2 Ω) 0 = f := hv
  have h5' : ‖weakDeriv (v : SobolevEuclidean N 1 2 Ω) 0‖ ^ 2
      = ‖(f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))‖ ^ 2 := by rw [h5]
  linarith

end SobolevZeroLift

/-! ### The $H^1_0$-preimage of an $L^2$ function -/

section ToSobolevZero


variable (Ω) in
/-- The **$H^1_0$-preimage** of $v \in L^2(\Omega)$: the element $w \in H^1_0(\Omega)$ whose $L^2$
class is $v$, if there is one, and $0$ otherwise.

When $w$ exists, it is unique (`SobolevMultiIndexZero.fnL_injective`). -/
def toSobolevZero (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    SobolevEuclideanZero N 1 2 Ω :=
  open Classical in
  if h : ∃ w : SobolevEuclideanZero N 1 2 Ω,
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w = v
  then h.choose else 0

/-- If $v \in L^2(\Omega)$ is the $L^2$ class of some element of $H^1_0(\Omega)$, then the $L^2$
class of `toSobolevZero Ω v` is $v$. -/
theorem fnL_toSobolevZero {v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hv : ∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w = v) :
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
      (toSobolevZero Ω v) = v := by
  unfold toSobolevZero
  rw [dite_eq_left hv]
  exact hv.choose_spec

/-- For $w \in H^1_0(\Omega)$, the $H^1_0$-preimage of the $L^2$ class of $w$ is $w$. -/
theorem toSobolevZero_fnL (w : SobolevEuclideanZero N 1 2 Ω) :
    toSobolevZero Ω (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
      volume w) = w :=
  SobolevMultiIndexZero.fnL_injective (fnL_toSobolevZero ⟨w, rfl⟩)

/-- The $H^1_0$-preimage is unique: if the $L^2$ class of $w \in H^1_0(\Omega)$ is $v$, then
`toSobolevZero Ω v` is $w$. -/
theorem toSobolevZero_eq {v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    {w : SobolevEuclideanZero N 1 2 Ω}
    (hw : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w
      = v) : toSobolevZero Ω v = w := by
  rw [← hw, toSobolevZero_fnL]

/-- If $v_1, v_2 \in L^2(\Omega)$ are $L^2$ classes of elements of $H^1_0(\Omega)$, then the
$H^1_0$-preimage of $v_1 + v_2$ is the sum of the $H^1_0$-preimages of $v_1$ and $v_2$. -/
theorem toSobolevZero_add {v₁ v₂ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (h₁ : ∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w = v₁)
    (h₂ : ∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w
        = v₂) :
    toSobolevZero Ω (v₁ + v₂) = toSobolevZero Ω v₁ + toSobolevZero Ω v₂ :=
  toSobolevZero_eq (by rw [_root_.map_add, fnL_toSobolevZero h₁, fnL_toSobolevZero h₂])

/-- If $v \in L^2(\Omega)$ is the $L^2$ class of an element of $H^1_0(\Omega)$ and
$c \in \mathbb{R}$, then the $H^1_0$-preimage of $c v$ is $c$ times the $H^1_0$-preimage of $v$. -/
theorem toSobolevZero_smul (c : ℝ)
    {v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (h : ∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w = v) :
    toSobolevZero Ω (c • v) = c • toSobolevZero Ω v :=
  toSobolevZero_eq (by rw [_root_.map_smul, fnL_toSobolevZero h])

end ToSobolevZero

/-! ### $H^2(\Omega) \cap H^1_0(\Omega) \subseteq D(A)$ on every open set -/

variable (Ω) in
/-- **The weak Laplacian on $H^2(\Omega)$**: the bounded linear map $H^2(\Omega) \to L^2(\Omega)$,
$$w \mapsto \Delta w = \sum_{i=1}^N \partial_i^2 w,$$
where $\partial_i^2 w$ is the weak derivative of $w$ at the multi-index $2 e_i$.

The multi-index $2 e_i$ is `MultiIndexLE.addSingle i (MultiIndexLE.single i)`. The map is the
Laplacian, not its negative. -/
def sobolevLaplacianL : SobolevEuclidean N 2 2 Ω →L[ℝ]
    Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  ∑ i : Fin N, weakDerivL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 2 Ω volume
    (MultiIndexLE.addSingle i (MultiIndexLE.single i))

/-- For $w \in H^2(\Omega)$, `sobolevLaplacianL Ω w` is $\sum_i \partial_i^2 w$, the sum of the weak
derivatives of $w$ at the multi-indices $2 e_i$. -/
theorem sobolevLaplacianL_apply (w : SobolevEuclidean N 2 2 Ω) :
    sobolevLaplacianL Ω w
      = ∑ i : Fin N, weakDeriv w (MultiIndexLE.addSingle i (MultiIndexLE.single i)) := by
  simp only [sobolevLaplacianL, sum_apply, weakDerivL_apply]

/-- **The Dirichlet form through $H^1$ derivatives.** Let $v \in H^1(\Omega)$, and let
$Q_1, \dots, Q_N \in H^1(\Omega)$ satisfy $\partial_i v = Q_i$ almost everywhere on $\Omega$ for
each $i$. Then for every $\Phi \in H^1_0(\Omega)$,
$$\int_\Omega \nabla v \cdot \nabla \Phi = \int_\Omega \Bigl(-\sum_i \partial_i Q_i\Bigr)
  \Phi.$$

For a test function $\Phi$, the identity $\int_\Omega \partial_i v \, \partial_i \Phi =
-\int_\Omega \partial_i Q_i \, \Phi$ is the weak-derivative identity of $Q_i$. The identity
extends from the test functions to $H^1_0(\Omega)$ by
`Elliptic.dirichletForm_eq_load_of_forall_testFunctions`. -/
theorem Elliptic.dirichletForm_eq_load_neg_sum_weakDeriv {v : SobolevEuclidean N 1 2 Ω}
    (Q : Fin N → SobolevEuclidean N 1 2 Ω)
    (hQ : ∀ i, ⇑(weakDeriv v (MultiIndexLE.single i))
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn (Q i)) :
    ∀ Φ ∈ SobolevEuclideanZero N 1 2 Ω,
      dirichletForm Ω v Φ = load Ω (-∑ i, weakDeriv (Q i) (MultiIndexLE.single i)) Φ := by
  -- the datum, as a function
  have hg : ⇑(-∑ i, weakDeriv (Q i) (MultiIndexLE.single i))
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      fun x ↦ -∑ i, weakDeriv (Q i) (MultiIndexLE.single i) x := by
    filter_upwards [Lp.coeFn_neg (∑ i, weakDeriv (Q i) (MultiIndexLE.single i)),
      Lp.coeFn_finsetSum Finset.univ fun i ↦ weakDeriv (Q i) (MultiIndexLE.single i)] with x hx1 hx2
    rw [hx1, Pi.neg_apply, hx2, Finset.sum_apply]
  -- the equation against test functions
  have heq : ∀ Φ ∈ testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume,
      dirichletForm Ω v Φ = load Ω (-∑ i, weakDeriv (Q i) (MultiIndexLE.single i)) Φ := by
    intro Φ hΦ
    obtain ⟨ψ, hψ⟩ := hΦ
    rw [dirichletForm_apply_eq_of_ae_eq hQ hψ, load_apply_eq_of_ae_eq hg hψ]
    have hterm : ∀ i, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        fn (Q i) x * fderiv ℝ ψ x (EuclideanSpace.single i 1)
        = -∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          weakDeriv (Q i) (MultiIndexLE.single i) x * ψ x := by
      intro i
      have key := (weakDeriv_hasWeakIteratedLineDerivOn_single (Q i) i)
        |>.integral_fderiv_mul_eq_of_eqOn ψ (fun _ _ ↦ rfl)
      calc ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
            fn (Q i) x * fderiv ℝ ψ x (EuclideanSpace.single i 1)
          = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
              fderiv ℝ ψ x (EuclideanSpace.single i 1) * fn (Q i) x :=
            integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
        _ = -∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
              ψ x * weakDeriv (Q i) (MultiIndexLE.single i) x := key
        _ = -∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
              weakDeriv (Q i) (MultiIndexLE.single i) x * ψ x := by
            congr 1
            exact integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
    simp only [hterm, Finset.sum_neg_distrib]
    have hI : ∀ i, Integrable
        (fun x ↦ weakDeriv (Q i) (MultiIndexLE.single i) x * ψ x)
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := fun i ↦ by
      have := ((weakDeriv_hasWeakIteratedLineDerivOn_single (Q i) i)
        |>.integrable_smul_weakDeriv ψ).integrableOn (s := (Ω : Set (EuclideanSpace ℝ (Fin N))))
      exact this.congr (Eventually.of_forall fun x ↦ by simp only [smul_eq_mul]; ring)
    rw [← integral_finsetSum _ fun i _ ↦ hI i, ← integral_neg]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by
      simp only [Finset.sum_mul, neg_mul])
  exact fun Φ hΦ ↦ dirichletForm_eq_load_of_forall_testFunctions heq hΦ

/-- **The weak Laplacian of an $H^2$ function is its distributional Laplacian.** Let
$w \in H^2(\Omega)$ and $v \in H^1(\Omega)$ have the same function almost everywhere on
$\Omega$. Then for every $\Phi \in H^1_0(\Omega)$,
$$\int_\Omega \nabla v \cdot \nabla \Phi = \int_\Omega (-\Delta w) \Phi,$$
where $\Delta w$ is `sobolevLaplacianL Ω w`.

For a test function $\Phi$, the identity $\int_\Omega \partial_i v \, \partial_i \Phi =
-\int_\Omega \partial_i^2 w \, \Phi$ is the weak-derivative identity of $w$; the first
derivatives of $v$ and $w$ agree because weak derivatives are unique. The identity extends from
the test functions to $H^1_0(\Omega)$ by
`Elliptic.dirichletForm_eq_load_of_forall_testFunctions`. This is the identity in
`mem_dirichletLaplacianDomain_of_sobolev_two` without the hypothesis $v \in H^1_0(\Omega)$. The
obstacle problem needs this form, because the obstacle $\psi$ is in general not in
$H^1_0(\Omega)$. -/
theorem Elliptic.dirichletForm_eq_load_neg_sobolevLaplacianL (w : SobolevEuclidean N 2 2 Ω)
    {v : SobolevEuclidean N 1 2 Ω}
    (hvw : fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn w) :
    ∀ Φ ∈ SobolevEuclideanZero N 1 2 Ω,
      dirichletForm Ω v Φ = load Ω (-sobolevLaplacianL Ω w) Φ := by
  -- the first derivatives of `v` are the functions of the `∂ᵢ w ∈ H¹(Ω)`
  have hd : ∀ i, ⇑(weakDeriv v (MultiIndexLE.single i))
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      fn (partialDeriv ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 Ω volume i w) := by
    intro i
    have h2 := hasWeakIteratedLineDerivOn_fn_partialDeriv i w
    rw [EuclideanSpace.basisFun_toBasis_apply] at h2
    exact SobolevEuclidean.weakDeriv_single_ae_eq v hvw h2
  have hL : -sobolevLaplacianL Ω w = -∑ i, weakDeriv
      (partialDeriv ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 Ω volume i w)
      (MultiIndexLE.single i) := by
    rw [sobolevLaplacianL_apply]
    simp only [weakDeriv_partialDeriv]
  rw [hL]
  exact Elliptic.dirichletForm_eq_load_neg_sum_weakDeriv _ hd

/-- For every $w \in H^2(\Omega)$, $\|\Delta w\|_{L^2} \le N \|w\|_{H^2}$, where
$\Delta w = \sum_i \partial_i^2 w$ is `sobolevLaplacianL Ω w`. -/
theorem Elliptic.norm_sobolevLaplacianL_le (w : SobolevEuclidean N 2 2 Ω) :
    ‖sobolevLaplacianL Ω w‖ ≤ N * ‖w‖ := by
  rw [sobolevLaplacianL_apply]
  calc ‖∑ i, weakDeriv w (MultiIndexLE.addSingle i (MultiIndexLE.single i))‖
      ≤ ∑ i, ‖weakDeriv w (MultiIndexLE.addSingle i (MultiIndexLE.single i))‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, ‖w‖ := Finset.sum_le_sum fun i _ ↦ norm_weakDeriv_le w _
    _ = N * ‖w‖ := by simp

/-- **$H^2(\Omega) \cap H^1_0(\Omega) \subseteq D(A)$ on every open set, with $Af = -\Delta f$.**
Let $w \in H^2(\Omega)$ and let $v \in H^1(\Omega)$ lie in $H^1_0(\Omega)$, and suppose that $v$
and $w$ have the same function almost everywhere on $\Omega$. Then the $L^2$ class $f$ of $v$
lies in $D(A)$, and
$$Af = -\Delta w = -\sum_i \partial_i^2 w.$$

The value $Af$ is stated as `dirichletLaplacianApply Ω f`, and $\Delta w$ is
`sobolevLaplacianL Ω w`. The proof is `Elliptic.dirichletForm_eq_load_neg_sobolevLaplacianL`.
This inclusion makes the book's uniqueness class
$C((0, \infty); H^2(\Omega) \cap H^1_0(\Omega))$ for the heat equation a subclass of the weak
one. -/
theorem mem_dirichletLaplacianDomain_of_sobolev_two (w : SobolevEuclidean N 2 2 Ω)
    {v : SobolevEuclidean N 1 2 Ω} (hv : v ∈ SobolevEuclideanZero N 1 2 Ω)
    (hvw : fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn w) :
    fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v ∈ dirichletLaplacianDomain Ω
      ∧ dirichletLaplacianApply Ω (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v)
        = -sobolevLaplacianL Ω w := by
  have heq' := Elliptic.dirichletForm_eq_load_neg_sobolevLaplacianL w hvw
  exact ⟨⟨v, hv, rfl, _, heq'⟩, (eq_dirichletLaplacianApply hv rfl heq').symm⟩

/-- **$H^2(\Omega) \cap H^1_0(\Omega) \subseteq D(A)$ on every open set.** Let $w \in H^2(\Omega)$
and let $v \in H^1(\Omega)$ lie in $H^1_0(\Omega)$, with the same function as $w$ almost
everywhere on $\Omega$. Then the $L^2$ class of $v$ lies in $D(A)$. -/
theorem fnL_mem_dirichletLaplacianDomain_of_sobolev_two (w : SobolevEuclidean N 2 2 Ω)
    {v : SobolevEuclidean N 1 2 Ω} (hv : v ∈ SobolevEuclideanZero N 1 2 Ω)
    (hvw : fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn w) :
    fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v ∈ dirichletLaplacianDomain Ω :=
  (mem_dirichletLaplacianDomain_of_sobolev_two w hv hvw).1

/-- **$Af = -\Delta w$ on $H^2(\Omega) \cap H^1_0(\Omega)$.** Let $w \in H^2(\Omega)$, let
$v \in H^1(\Omega)$ lie in $H^1_0(\Omega)$ with the same function as $w$ almost everywhere on
$\Omega$, and let $f \in D(A)$ be the $L^2$ class of $v$. Then $Af = -\Delta w$, where
$\Delta w$ is `sobolevLaplacianL Ω w`. -/
theorem dirichletLaplacian_apply_of_sobolev_two (w : SobolevEuclidean N 2 2 Ω)
    {v : SobolevEuclidean N 1 2 Ω} (hv : v ∈ SobolevEuclideanZero N 1 2 Ω)
    (hvw : fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn w)
    (f : (dirichletLaplacian Ω).domain)
    (hf : fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v = f) :
    dirichletLaplacian Ω f = -sobolevLaplacianL Ω w := by
  rw [dirichletLaplacian_apply, ← hf]
  exact (mem_dirichletLaplacianDomain_of_sobolev_two w hv hvw).2

/-! ### Test functions lie in every $D(A^\ell)$ -/

/-- Let $\varphi$ be a test function on $\Omega$ and let $u \in H^2(\Omega)$ have the function
$\varphi$ almost everywhere on $\Omega$. Then for each $i$, the weak derivative of $u$ at the
multi-index $2 e_i$ equals the classical second derivative $\partial_i \partial_i \varphi$
almost everywhere on $\Omega$. -/
theorem weakDeriv_addSingle_ae_eq_of_testFunction (φ : 𝓓(Ω, ℝ)) {u : SobolevEuclidean N 2 2 Ω}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] φ) (i : Fin N) :
    ⇑(weakDeriv u (MultiIndexLE.addSingle i (MultiIndexLE.single i)))
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      fun x ↦ fderiv ℝ (fun z ↦ fderiv ℝ φ z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1) := by
  have hΩm : MeasurableSet (Ω : Set (EuclideanSpace ℝ (Fin N))) := Ω.isOpen.measurableSet
  have hφ1 : HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1]
      (φ : EuclideanSpace ℝ (Fin N) → ℝ) (fun x ↦ fderiv ℝ φ x (EuclideanSpace.single i 1))
      Ω volume :=
    (φ.contDiff.contDiffOn.of_le (by simp)).hasWeakIteratedLineDerivOn_single Ω i
  have hdφ : ContDiff ℝ ∞ fun x ↦ fderiv ℝ φ x (EuclideanSpace.single i 1) :=
    (φ.contDiff.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  have hφ2 : HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1]
      (fun x ↦ fderiv ℝ φ x (EuclideanSpace.single i 1))
      (fun x ↦ fderiv ℝ (fun z ↦ fderiv ℝ φ z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1)) Ω volume :=
    (hdφ.contDiffOn.of_le (by simp)).hasWeakIteratedLineDerivOn_single Ω i
  -- the first derivative of `u` along `eᵢ` is `∂ᵢ φ`
  have h1 := (hasWeakIteratedLineDerivOn_single u i).congr_ae hu (EventuallyEq.refl _ _)
  rw [EuclideanSpace.basisFun_toBasis_apply] at h1
  have e1 : ⇑(weakDeriv u (MultiIndexLE.singleLE i))
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      fun x ↦ fderiv ℝ φ x (EuclideanSpace.single i 1) :=
    (ae_restrict_iff' hΩm).2 (h1.ae_eq hφ1)
  -- the second derivative
  have h2 := ((hasWeakIteratedLineDerivOn_addSingle u i (MultiIndexLE.single i)).of_perm
    (multiIndexTuple_single_perm ((EuclideanSpace.basisFun (Fin N) ℝ).toBasis :
      Fin N → EuclideanSpace ℝ (Fin N)) i)).congr_ae e1 (EventuallyEq.refl _ _)
  rw [EuclideanSpace.basisFun_toBasis_apply] at h2
  exact (ae_restrict_iff' hΩm).2 (h2.ae_eq hφ2)

/-- **Every test function lies in $D(A)$, with $A\varphi = -\Delta\varphi$.** For every test
function $\varphi$ on $\Omega$, the $L^2$ class of $\varphi$ lies in $D(A)$, and $A\varphi$ is
the $L^2$ class of the test function $-\Delta\varphi = -\sum_i \partial_i \partial_i \varphi$.
This gives the data in $C_c^\infty(\Omega)$ of Theorem 10.2 (c) and Corollary 10.5 of
[brezis2011functional].

The value $A\varphi$ is stated as `dirichletLaplacianApply Ω φ.toL2`, and $-\Delta\varphi$ is
`TestFunction.negLaplacian φ`. The proof applies `mem_dirichletLaplacianDomain_of_sobolev_two`
to the $H^2$ and $H^1_0$ elements of $\varphi$, whose weak second derivatives are the classical
ones (`weakDeriv_addSingle_ae_eq_of_testFunction`). -/
theorem testFunction_mem_dirichletLaplacianDomain (φ : 𝓓(Ω, ℝ)) :
    φ.toL2 ∈ dirichletLaplacianDomain Ω ∧
      dirichletLaplacianApply Ω φ.toL2 = φ.negLaplacian.toL2 := by
  obtain ⟨u₂, -, hu₂φ⟩ := φ.exists_mem_sobolevMultiIndex_testFunctions
    (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis) (k := 2) (p := 2) (μ := volume)
  obtain ⟨u₁, hu₁, hu₁φ⟩ := φ.exists_mem_sobolevMultiIndex_testFunctions
    (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis) (k := 1) (p := 2) (μ := volume)
  have hv : u₁ ∈ SobolevEuclideanZero N 1 2 Ω := SobolevMultiIndexZero.testFunctions_le hu₁
  obtain ⟨hmem, happ⟩ := mem_dirichletLaplacianDomain_of_sobolev_two u₂ hv
    (hu₁φ.trans hu₂φ.symm)
  have e1 : fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume u₁ = φ.toL2 :=
    Lp.ext (hu₁φ.trans φ.coeFn_toL2.symm)
  have e2 : -sobolevLaplacianL Ω u₂ = φ.negLaplacian.toL2 := by
    refine Lp.ext ?_
    rw [sobolevLaplacianL_apply]
    have hsum := Lp.coeFn_finsetSum Finset.univ
      fun i ↦ weakDeriv u₂ (MultiIndexLE.addSingle i (MultiIndexLE.single i))
    filter_upwards [Lp.coeFn_neg
      (∑ i, weakDeriv u₂ (MultiIndexLE.addSingle i (MultiIndexLE.single i))),
      hsum, φ.negLaplacian.coeFn_toL2,
      ae_all_iff.2 fun i ↦ weakDeriv_addSingle_ae_eq_of_testFunction φ hu₂φ i]
      with x hx1 hx2 hx3 hx4
    rw [hx1, Pi.neg_apply, hx2, Finset.sum_apply, hx3, TestFunction.negLaplacian_coe]
    simp only [hx4]
  rw [e1] at hmem happ
  exact ⟨hmem, happ.trans e2⟩

/-- For a test function $\varphi$ and $j \in \mathbb{N}$, the $L^2$ class of $(-\Delta)^j \varphi$
lies in $D(A)$, and $A$ maps it to the $L^2$ class of $(-\Delta)^{j+1} \varphi$. Here
$(-\Delta)^j \varphi$ is the $j$-th iterate of `TestFunction.negLaplacian`. -/
theorem testFunction_iterate_negLaplacian_chain (φ : 𝓓(Ω, ℝ)) (j : ℕ) :
    ∃ h : (TestFunction.negLaplacian^[j] φ).toL2 ∈ (dirichletLaplacian Ω).domain,
      dirichletLaplacian Ω ⟨(TestFunction.negLaplacian^[j] φ).toL2, h⟩
        = (TestFunction.negLaplacian^[j + 1] φ).toL2 := by
  refine ⟨(testFunction_mem_dirichletLaplacianDomain _).1, ?_⟩
  rw [dirichletLaplacian_apply, (testFunction_mem_dirichletLaplacianDomain _).2,
    Function.iterate_succ_apply']

/-- **Every test function lies in every $D(A^\ell)$.** Let $\varphi$ be a test function on $\Omega$
and let $\ell \in \mathbb{N}$. There is $x \in D(A^\ell)$ whose coordinates are
$$A^j x = (-\Delta)^j \varphi \qquad \text{for } j = 0, \dots, \ell,$$
where $(-\Delta)^j \varphi$ stands for its $L^2$ class.

The element $x$ is the tuple $(\varphi, -\Delta\varphi, \dots, (-\Delta)^\ell \varphi)$, built
with `LinearPMap.PowDomain.mk`; consecutive entries are related by $A$ by
`testFunction_mem_dirichletLaplacianDomain`. Here $(-\Delta)^j \varphi$ is the $j$-th iterate of
`TestFunction.negLaplacian`. -/
theorem testFunction_exists_powDomain (φ : 𝓓(Ω, ℝ)) (ℓ : ℕ) :
    ∃ x : (dirichletLaplacian Ω).PowDomain ℓ, ∀ j : Fin (ℓ + 1),
      LinearPMap.PowDomain.applyL (dirichletLaplacian Ω) ℓ j x
        = (TestFunction.negLaplacian^[j] φ).toL2 := by
  have hchain : ∀ i : Fin ℓ, ∃ h : (fun j : Fin (ℓ + 1) ↦ (TestFunction.negLaplacian^[j] φ).toL2)
      i.castSucc ∈ (dirichletLaplacian Ω).domain,
      dirichletLaplacian Ω ⟨(fun j : Fin (ℓ + 1) ↦ (TestFunction.negLaplacian^[j] φ).toL2)
        i.castSucc, h⟩ = (fun j : Fin (ℓ + 1) ↦ (TestFunction.negLaplacian^[j] φ).toL2) i.succ := by
    intro i
    obtain ⟨h, hh⟩ := testFunction_iterate_negLaplacian_chain φ i
    exact LinearPMap.PowDomain.exists_apply_eq_of_eq h hh (by simp) (by simp)
  exact ⟨LinearPMap.PowDomain.mk (dirichletLaplacian Ω) _ hchain, fun j ↦
    LinearPMap.PowDomain.applyL_mk _ _ j⟩

/-! ### $D(A) = H^2(\Omega) \cap H^1_0(\Omega)$ on a $C^2$ domain with bounded boundary -/

/-- **The $H^1_0$-lift of $f \in D(A)$ is the weak solution of $-\Delta v + v = f + Af$.** Let
$f \in D(A)$ and let $v$ be an $H^1_0$-lift of $f$. Then $v \in H^1_0(\Omega)$ and
$$\int_\Omega \nabla v \cdot \nabla \varphi + \int_\Omega v \varphi = \int_\Omega (f + Af)
  \varphi \qquad \text{for all } \varphi \in H^1_0(\Omega).$$
This is equation (48) in the proof of Theorem 10.1 of [brezis2011functional].

The conclusion is `IsGalerkinSolution` for the form `Elliptic.laplaceForm Ω` of $-\Delta + 1$,
the load of $f + Af$, and the subspace $H^1_0(\Omega)$. -/
theorem dirichletLaplacian_isGalerkinSolution_laplace (f : (dirichletLaplacian Ω).domain)
    {v : SobolevEuclidean N 1 2 Ω} (hv : v ∈ SobolevEuclideanZero N 1 2 Ω)
    (hvf : fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v = f) :
    IsGalerkinSolution (laplaceForm Ω) (load Ω ((f : Lp ℝ 2 (volume.restrict
      (Ω : Set (EuclideanSpace ℝ (Fin N))))) + dirichletLaplacian Ω f))
      (SobolevEuclideanZero N 1 2 Ω) v := by
  refine ⟨hv, fun φ hφ ↦ ?_⟩
  have h1 := laplaceForm_apply_eq_dirichletForm_add_weakDeriv Ω v φ
  have h2 := dirichletLaplacian_inner_eq_dirichletForm f hv hvf hφ
  rw [fnL_eq_weakDeriv_zero] at h2
  have h3 : load Ω ((f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
      + dirichletLaplacian Ω f) φ
      = ⟪(f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))),
          weakDeriv φ 0⟫_ℝ + ⟪dirichletLaplacian Ω f, weakDeriv φ 0⟫_ℝ := by
    rw [load_add, load_apply_inner, load_apply_inner]
  have h4 : weakDeriv v 0 = f := (fnL_eq_weakDeriv_zero v).symm.trans hvf
  rw [h4] at h1
  rw [h1, h3, h2, add_comm]

/-- **$D(A) \subseteq H^2(\Omega)$ from a regularity estimate, with the graph-norm bound.** Let
$C \ge 0$, and suppose that for every $g \in L^2(\Omega)$, every weak solution
$u \in H^1_0(\Omega)$ of $-\Delta u + u = g$ has its function in $H^2(\Omega)$, and every
$U \in H^2(\Omega)$ with the function of $u$ satisfies $\|U\|_{H^2} \le C \|g\|_{L^2}$. Then
every $f \in D(A)$ has an $H^2$-lift, and every $H^2$-lift $w$ of $f$ satisfies
$$\|w\|_{H^2} \le C \bigl(\|f\|_{L^2} + \|Af\|_{L^2}\bigr).$$

The hypothesis is the conclusion of Theorem 9.25 of [brezis2011functional]
(`Elliptic.regularity_dirichlet`); here $\Omega$ is an arbitrary open set. A weak solution is
`IsGalerkinSolution` for `Elliptic.laplaceForm Ω` on $H^1_0(\Omega)$. The proof applies the
hypothesis to the $H^1_0$-lift of $f$, which solves $-\Delta v + v = f + Af$
(`dirichletLaplacian_isGalerkinSolution_laplace`). -/
theorem dirichletLaplacian_exists_sobolev_two_of_forall {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ (g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
      (u : SobolevEuclidean N 1 2 Ω),
      IsGalerkinSolution (laplaceForm Ω) (load Ω g) (SobolevEuclideanZero N 1 2 Ω) u →
      MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (fn u) 2 2 Ω volume ∧
      ∀ U : SobolevEuclidean N 2 2 Ω,
        fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn u → ‖U‖ ≤ C * ‖g‖)
    (f : (dirichletLaplacian Ω).domain) :
    (∃ w : SobolevEuclidean N 2 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 2 Ω volume w = f) ∧
    ∀ w : SobolevEuclidean N 2 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 2 Ω volume w = f →
      ‖w‖ ≤ C * (‖(f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))‖
        + ‖dirichletLaplacian Ω f‖) := by
  obtain ⟨v, hv, hvf⟩ := dirichletLaplacian_exists_lift f
  obtain ⟨hmem, hbound⟩ := hC _ v (dirichletLaplacian_isGalerkinSolution_laplace f hv hvf)
  refine ⟨?_, fun w hwf ↦ ?_⟩
  · obtain ⟨w, hw⟩ := hmem.exists_sobolevMultiIndex
    refine ⟨w, Lp.ext (hw.trans ?_)⟩
    rw [← hvf]
    rfl
  · have hwv : fn w =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn v :=
      Filter.EventuallyEq.of_eq (congrArg (fun z : Lp ℝ 2 (volume.restrict
        (Ω : Set (EuclideanSpace ℝ (Fin N)))) ↦ (z : EuclideanSpace ℝ (Fin N) → ℝ))
        (hwf.trans hvf.symm))
    exact (hbound w hwv).trans (mul_le_mul_of_nonneg_left (norm_add_le _ _) hC0)

/-- **$D(A) \subseteq H^2(\Omega)$ on a $C^2$ domain with bounded boundary, with the graph-norm
bound.** Let $N \ge 1$ and let $\Omega \subseteq \mathbb{R}^N$ be an open set of class $C^2$
with bounded boundary. There is $C \ge 0$ such that every $f \in D(A)$ has an $H^2$-lift, and
every $H^2$-lift $w$ of $f$ satisfies
$$\|w\|_{H^2} \le C \bigl(\|f\|_{L^2} + \|Af\|_{L^2}\bigr).$$

The proof applies Theorem 9.25 of [brezis2011functional] (`Elliptic.regularity_dirichlet`)
through `dirichletLaplacian_exists_sobolev_two_of_forall`. -/
theorem dirichletLaplacian_exists_sobolev_two_of_isContDiffChartDomain {d : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffChartDomain 2 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : (dirichletLaplacian Ω).domain,
      (∃ w : SobolevEuclidean (d + 1) 2 2 Ω,
        fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 2 2 Ω volume w = f) ∧
      ∀ w : SobolevEuclidean (d + 1) 2 2 Ω,
        fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 2 2 Ω volume w = f →
        ‖w‖ ≤ C * (‖(f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))‖
          + ‖dirichletLaplacian Ω f‖) := by
  obtain ⟨C, hC0, hC⟩ := regularity_dirichlet hΩ hΓ
  exact ⟨C, hC0, fun f ↦ dirichletLaplacian_exists_sobolev_two_of_forall hC0 hC f⟩

/-- **$H^2(\Omega) \cap H^1_0(\Omega) \subseteq D(A)$ on every open set**, for a function given by
its two lifts: if $f \in L^2(\Omega)$ has an $H^2$-lift and an $H^1_0$-lift, then $f \in D(A)$. -/
theorem mem_dirichletLaplacianDomain_of_exists_sobolev_two
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hw : ∃ w : SobolevEuclidean N 2 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 2 Ω volume w = f)
    (hv : ∃ v : SobolevEuclidean N 1 2 Ω, v ∈ SobolevEuclideanZero N 1 2 Ω ∧
      fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v = f) :
    f ∈ dirichletLaplacianDomain Ω := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨v, hv, hvf⟩ := hv
  rw [← hvf]
  refine fnL_mem_dirichletLaplacianDomain_of_sobolev_two w hv ?_
  exact Filter.EventuallyEq.of_eq (congrArg (fun z : Lp ℝ 2 (volume.restrict
    (Ω : Set (EuclideanSpace ℝ (Fin N)))) ↦ (z : EuclideanSpace ℝ (Fin N) → ℝ))
    (hvf.trans hw.symm))

/-- **$D(A) = H^2(\Omega) \cap H^1_0(\Omega)$ on a $C^2$ domain with bounded boundary, with the
graph-norm bound.** Let $N \ge 1$ and let $\Omega \subseteq \mathbb{R}^N$ be an open set of
class $C^2$ with bounded boundary. Then: (a) a function $f \in L^2(\Omega)$ lies in $D(A)$ if
and only if it has an $H^2$-lift and an $H^1_0$-lift; (b) there is $C \ge 0$ such that for every
$f \in D(A)$ and every $H^2$-lift $w$ of $f$,
$$\|w\|_{H^2} \le C \bigl(\|f\|_{L^2} + \|Af\|_{L^2}\bigr).$$
Part (b) says that the inclusion $D(A) \hookrightarrow H^2(\Omega)$ is continuous for the graph
norm $\|f\| + \|Af\|$. This is Theorem 9.25 of [brezis2011functional] read on the operator, as
in the proof of Theorem 10.1.

The direction "if" of (a) is `mem_dirichletLaplacianDomain_of_sobolev_two` and holds on every
open set. The direction "only if" applies the regularity theorem `Elliptic.regularity_dirichlet`
to the $H^1_0$-lift $v$ of $f$, which is the weak solution of $-\Delta v + v = f + Af$. -/
theorem dirichletLaplacianDomain_eq_of_isContDiffChartDomain {d : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffChartDomain 2 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    (∀ f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      f ∈ dirichletLaplacianDomain Ω ↔
        (∃ w : SobolevEuclidean (d + 1) 2 2 Ω,
          fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 2 2 Ω volume w = f) ∧
        ∃ v : SobolevEuclidean (d + 1) 1 2 Ω, v ∈ SobolevEuclideanZero (d + 1) 1 2 Ω ∧
          fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume v = f) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : (dirichletLaplacian Ω).domain) (w : SobolevEuclidean (d + 1) 2 2 Ω),
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 2 2 Ω volume w = f →
      ‖w‖ ≤ C * (‖(f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))‖
        + ‖dirichletLaplacian Ω f‖) := by
  obtain ⟨C, hC0, hC⟩ := dirichletLaplacian_exists_sobolev_two_of_isContDiffChartDomain hΩ hΓ
  exact ⟨fun f ↦ ⟨fun hf ↦ ⟨(hC ⟨f, hf⟩).1, dirichletLaplacian_exists_lift ⟨f, hf⟩⟩,
    fun h ↦ mem_dirichletLaplacianDomain_of_exists_sobolev_two h.1 h.2⟩, C, hC0,
    fun f w hwf ↦ (hC f).2 w hwf⟩

/-! ### From the lifts of chapter 7 to curves in Sobolev spaces -/

/-- **A curve of class $C^n$ in $D(A^j)$ is a curve of class $C^n$ in $V$.** Let $H$ be a real inner
product space, $V$ a real normed space, $A$ an unbounded operator on $H$,
$s \subseteq \mathbb{R}$, and $u : \mathbb{R} \to H$. Suppose that $u$ has on $s$ a lift of
class $C^n$ with values in $D(A^j)$ (`LinearPMap.ContDiffOnPowDomain`). Let $J : D(A^j) \to V$
and $K : V \to H$ be bounded linear maps such that $K \circ J$ is the inclusion $D(A^j) \to H$,
that is, $K(Jx) = A^0 x$. Then $u$ is of class $C^n$ on $s$ with values in $V$, read through $K$
(`Bochner.ContDiffOnThrough K n u s`).

The lift in $V$ is $J \circ v$ for the lift $v$ in $D(A^j)$. With
`dirichletLaplacian.powDomainToSobolevL` as $J$ and `SobolevMultiIndex.fnL` as $K$, this turns
the clauses $C^k([0, \infty); D(A^\ell))$ of the heat equation into
$C^k([0, \infty); H^{2\ell}(\Omega))$. -/
theorem Bochner.ContDiffOnThrough.of_contDiffOnPowDomain {H V : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [NormedAddCommGroup V] [NormedSpace ℝ V] {A : H →ₗ.[ℝ] H}
    {n : WithTop ℕ∞} {j : ℕ} {u : ℝ → H} {s : Set ℝ} (h : A.ContDiffOnPowDomain n j u s)
    (J : A.PowDomain j →L[ℝ] V) (K : V →L[ℝ] H)
    (hKJ : ∀ x, K (J x) = LinearPMap.PowDomain.applyL A j 0 x) :
    Bochner.ContDiffOnThrough K n u s := by
  obtain ⟨v, hv0, hv⟩ := h
  exact ⟨fun t ↦ J (v t), J.contDiff.comp_contDiffOn hv, fun t ht ↦ by rw [hKJ, hv0 t ht]⟩

/-! ### The Dirichlet Laplacian $A_1$ in $H^1_0(\Omega)$ -/

variable (Ω) in
/-- The condition for $v \in H^1_0(\Omega)$ to lie in the domain $D(A_1)$ of the Dirichlet Laplacian
in $H^1_0(\Omega)$: the $L^2$ class of $v$ lies in $D(A)$, and $A v$ lies in $H^1_0(\Omega)$,
that is, $Av$ is the $L^2$ class of some element of $H^1_0(\Omega)$. -/
def MemDirichletLaplacianH10Domain (v : SobolevEuclideanZero N 1 2 Ω) : Prop :=
  SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v
      ∈ dirichletLaplacianDomain Ω ∧ ∃ w : SobolevEuclideanZero N 1 2 Ω,
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w
      = dirichletLaplacianApply Ω
        (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v)

/-- The element $0$ of $H^1_0(\Omega)$ satisfies the condition `MemDirichletLaplacianH10Domain` of
$D(A_1)$. -/
theorem memDirichletLaplacianH10Domain_zero : MemDirichletLaplacianH10Domain Ω 0 := by
  refine ⟨by rw [map_zero]; exact Submodule.zero_mem _, 0, ?_⟩
  rw [map_zero, dirichletLaplacianApply_zero]

/-- The condition `MemDirichletLaplacianH10Domain` of $D(A_1)$ is closed under addition. -/
theorem MemDirichletLaplacianH10Domain.add {v₁ v₂ : SobolevEuclideanZero N 1 2 Ω}
    (h₁ : MemDirichletLaplacianH10Domain Ω v₁) (h₂ : MemDirichletLaplacianH10Domain Ω v₂) :
    MemDirichletLaplacianH10Domain Ω (v₁ + v₂) := by
  obtain ⟨h₁, w₁, hw₁⟩ := h₁
  obtain ⟨h₂, w₂, hw₂⟩ := h₂
  have e₁ := map_add (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2
    Ω volume) v₁ v₂
  have e₂ := map_add (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2
    Ω volume) w₁ w₂
  refine ⟨e₁ ▸ add_mem h₁ h₂, w₁ + w₂, ?_⟩
  exact (e₂.trans (congrArg₂ (· + ·) hw₁ hw₂)).trans
    ((dirichletLaplacianApply_add h₁ h₂).symm.trans (congrArg _ e₁.symm))

/-- The condition `MemDirichletLaplacianH10Domain` of $D(A_1)$ is closed under multiplication by a
real scalar. -/
theorem MemDirichletLaplacianH10Domain.smul (c : ℝ) {v : SobolevEuclideanZero N 1 2 Ω}
    (h : MemDirichletLaplacianH10Domain Ω v) : MemDirichletLaplacianH10Domain Ω (c • v) := by
  obtain ⟨h, w, hw⟩ := h
  have e₁ := map_smul (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2
    Ω volume) c v
  have e₂ := map_smul (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2
    Ω volume) c w
  refine ⟨e₁ ▸ Submodule.smul_mem _ c h, c • w, ?_⟩
  exact (e₂.trans (congrArg (c • ·) hw)).trans
    ((dirichletLaplacianApply_smul c h).symm.trans (congrArg _ e₁.symm))

variable (Ω) in
/-- The **domain $D(A_1)$ of the Dirichlet Laplacian in $H^1_0(\Omega)$**: the subspace of the
$v \in H^1_0(\Omega)$ whose $L^2$ class lies in $D(A)$ and for which $Av$ lies in
$H^1_0(\Omega)$.

Once the regularity theorem identifies the domains, this is the book's $\{u \in H^3(\Omega) \cap
H^1_0(\Omega) : \Delta u \in H^1_0(\Omega)\}$. -/
def dirichletLaplacianH10Domain : Submodule ℝ (SobolevEuclideanZero N 1 2 Ω) where
  carrier := {v | MemDirichletLaplacianH10Domain Ω v}
  zero_mem' := memDirichletLaplacianH10Domain_zero
  add_mem' := fun h₁ h₂ ↦ h₁.add h₂
  smul_mem' := fun c _ h ↦ h.smul c

/-- An element $v \in H^1_0(\Omega)$ lies in $D(A_1)$ if and only if its $L^2$ class lies in $D(A)$
and $Av$ is the $L^2$ class of some element of $H^1_0(\Omega)$. This is the definition of
`dirichletLaplacianH10Domain`, unfolded. -/
theorem mem_dirichletLaplacianH10Domain_iff {v : SobolevEuclideanZero N 1 2 Ω} :
    v ∈ dirichletLaplacianH10Domain Ω ↔
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v
        ∈ dirichletLaplacianDomain Ω ∧ ∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w
        = dirichletLaplacianApply Ω
          (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
            v) :=
  Iff.rfl

variable (Ω) in
/-- The value of $A_1$ at $v \in H^1_0(\Omega)$: for $v \in D(A_1)$, an element of $H^1_0(\Omega)$
whose $L^2$ class is $Av$, chosen; for $v \notin D(A_1)$, the value $0$.

The chosen element is unique, because the inclusion $H^1_0(\Omega) \to L^2(\Omega)$ is
injective. -/
def dirichletLaplacianH10Apply (v : SobolevEuclideanZero N 1 2 Ω) : SobolevEuclideanZero N 1 2 Ω :=
  open Classical in
  if hv : v ∈ dirichletLaplacianH10Domain Ω then Classical.choose hv.2 else 0

/-- For $v \in D(A_1)$, the $L^2$ class of `dirichletLaplacianH10Apply Ω v` is $Av$, the value of
`dirichletLaplacianApply Ω` at the $L^2$ class of $v$. -/
theorem fnL_dirichletLaplacianH10Apply {v : SobolevEuclideanZero N 1 2 Ω}
    (hv : v ∈ dirichletLaplacianH10Domain Ω) :
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
      (dirichletLaplacianH10Apply Ω v)
      = dirichletLaplacianApply Ω
        (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
          v) := by
  unfold dirichletLaplacianH10Apply
  rw [dite_eq_left hv]
  exact Classical.choose_spec hv.2

/-- For $v_1, v_2 \in D(A_1)$, the value of `dirichletLaplacianH10Apply Ω` at $v_1 + v_2$ is the sum
of its values at $v_1$ and at $v_2$. -/
theorem dirichletLaplacianH10Apply_add {v₁ v₂ : SobolevEuclideanZero N 1 2 Ω}
    (h₁ : v₁ ∈ dirichletLaplacianH10Domain Ω) (h₂ : v₂ ∈ dirichletLaplacianH10Domain Ω) :
    dirichletLaplacianH10Apply Ω (v₁ + v₂)
      = dirichletLaplacianH10Apply Ω v₁ + dirichletLaplacianH10Apply Ω v₂ := by
  have e₁ := map_add (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2
    Ω volume) v₁ v₂
  have e₂ := map_add (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2
    Ω volume) (dirichletLaplacianH10Apply Ω v₁) (dirichletLaplacianH10Apply Ω v₂)
  have h₁₂ : v₁ + v₂ ∈ dirichletLaplacianH10Domain Ω := add_mem h₁ h₂
  refine SobolevMultiIndexZero.fnL_injective ?_
  refine (fnL_dirichletLaplacianH10Apply h₁₂).trans ?_
  refine ((congrArg _ e₁).trans (dirichletLaplacianApply_add h₁.1 h₂.1)).trans ?_
  refine (congrArg₂ (· + ·) (fnL_dirichletLaplacianH10Apply h₁).symm
    (fnL_dirichletLaplacianH10Apply h₂).symm).trans e₂.symm

/-- For $v \in D(A_1)$ and $c \in \mathbb{R}$, the value of `dirichletLaplacianH10Apply Ω` at $c v$
is $c$ times its value at $v$. -/
theorem dirichletLaplacianH10Apply_smul (c : ℝ) {v : SobolevEuclideanZero N 1 2 Ω}
    (h : v ∈ dirichletLaplacianH10Domain Ω) :
    dirichletLaplacianH10Apply Ω (c • v) = c • dirichletLaplacianH10Apply Ω v := by
  have e₁ := map_smul (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2
    Ω volume) c v
  have e₂ := map_smul (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2
    Ω volume) c (dirichletLaplacianH10Apply Ω v)
  have hc : c • v ∈ dirichletLaplacianH10Domain Ω := Submodule.smul_mem _ c h
  refine SobolevMultiIndexZero.fnL_injective ?_
  refine (fnL_dirichletLaplacianH10Apply hc).trans ?_
  refine ((congrArg _ e₁).trans (dirichletLaplacianApply_smul c h.1)).trans ?_
  exact (congrArg (c • ·) (fnL_dirichletLaplacianH10Apply h).symm).trans e₂.symm

variable (Ω) in
/-- The **Dirichlet Laplacian $A_1$ in $H^1_0(\Omega)$**, as an unbounded operator on the Hilbert
space $H^1_0(\Omega)$ with the inner product $(u, v)_{H^1} = \int_\Omega \nabla u \cdot \nabla
v + \int_\Omega u v$. Its domain is
$$D(A_1) = \{v \in H^1_0(\Omega) : v \in D(A),\ Av \in H^1_0(\Omega)\},$$
and $A_1 v$ is the element of $H^1_0(\Omega)$ whose $L^2$ class is $Av$. This is the operator
$A_1$ of the proof of Theorem 10.2 (a) of [brezis2011functional].

The operator is a Mathlib `LinearPMap` whose values are `dirichletLaplacianH10Apply`. The
identity "the $L^2$ class of $A_1 v$ is $Av$" is `fnL_dirichletLaplacianH10_apply`. -/
def dirichletLaplacianH10 : SobolevEuclideanZero N 1 2 Ω →ₗ.[ℝ] SobolevEuclideanZero N 1 2 Ω where
  domain := dirichletLaplacianH10Domain Ω
  toFun :=
    { toFun := fun v ↦ dirichletLaplacianH10Apply Ω v
      map_add' := fun v₁ v₂ ↦ dirichletLaplacianH10Apply_add v₁.2 v₂.2
      map_smul' := fun c v ↦ dirichletLaplacianH10Apply_smul c v.2 }

/-- The domain of `dirichletLaplacianH10 Ω` is `dirichletLaplacianH10Domain Ω`. -/
@[simp]
theorem dirichletLaplacianH10_domain :
    (dirichletLaplacianH10 Ω).domain = dirichletLaplacianH10Domain Ω :=
  rfl

/-- **$A_1$ is $A$ read in $H^1_0(\Omega)$.** For $v \in D(A_1)$, the $L^2$ class of $A_1 v$ is
$Av$, the value of $A$ at the $L^2$ class of $v$. -/
theorem fnL_dirichletLaplacianH10_apply (v : (dirichletLaplacianH10 Ω).domain) :
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
      (dirichletLaplacianH10 Ω v)
      = dirichletLaplacian Ω
        ⟨SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v,
          v.2.1⟩ :=
  fnL_dirichletLaplacianH10Apply v.2

/-- For $u, v \in D(A_1)$,
$$\int_\Omega \nabla (A_1 u) \cdot \nabla v = \langle Au, Av \rangle,$$
where $Au$ and $Av$ are the values of $A$ at the $L^2$ classes of $u$ and $v$. The left side
equals $\langle Av, A_1 u \rangle$ by the defining identity of $A$, and $A_1 u = Au$ in
$L^2(\Omega)$. -/
theorem dirichletForm_dirichletLaplacianH10_apply (u v : (dirichletLaplacianH10 Ω).domain) :
    dirichletForm Ω (dirichletLaplacianH10 Ω u : SobolevEuclidean N 1 2 Ω)
        (v : SobolevEuclidean N 1 2 Ω)
      = ⟪dirichletLaplacian Ω
          ⟨SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume u,
            u.2.1⟩,
        dirichletLaplacian Ω
          ⟨SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v,
            v.2.1⟩⟫_ℝ := by
  have h1 : dirichletForm Ω (dirichletLaplacianH10 Ω u : SobolevEuclidean N 1 2 Ω)
      (v : SobolevEuclidean N 1 2 Ω)
      = dirichletForm Ω (v : SobolevEuclidean N 1 2 Ω)
        (dirichletLaplacianH10 Ω u : SobolevEuclidean N 1 2 Ω) := by
    rw [dirichletForm_isHermitian Ω _ _, conj_trivial]
  have h2 := dirichletLaplacian_inner_eq_dirichletForm ⟨_, v.2.1⟩
    (v : SobolevEuclideanZero N 1 2 Ω).2 rfl (dirichletLaplacianH10 Ω u).2
  have h3 := congrArg (fun z ↦ ⟪dirichletLaplacian Ω ⟨_, v.2.1⟩, z⟫_ℝ)
    (fnL_dirichletLaplacianH10_apply u)
  exact (h1.trans h2.symm).trans (h3.trans (real_inner_comm _ _))

/-- For $u, v \in D(A_1)$, $\langle A_1 u, v \rangle = \int_\Omega \nabla u \cdot \nabla v$, where
the inner product on the left is that of $L^2(\Omega)$, taken between the $L^2$ classes. -/
theorem inner_fnL_dirichletLaplacianH10_apply (u v : (dirichletLaplacianH10 Ω).domain) :
    ⟪SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
        (dirichletLaplacianH10 Ω u),
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
        (v : SobolevEuclideanZero N 1 2 Ω)⟫_ℝ
      = dirichletForm Ω (u : SobolevEuclidean N 1 2 Ω) (v : SobolevEuclidean N 1 2 Ω) := by
  have h1 := dirichletLaplacian_inner_eq_dirichletForm ⟨_, u.2.1⟩
    (u : SobolevEuclideanZero N 1 2 Ω).2 rfl (v : SobolevEuclideanZero N 1 2 Ω).2
  have h2 := congrArg (fun z ↦ ⟪z, SobolevMultiIndexZero.fnL ℝ
    (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (v : SobolevEuclideanZero N 1 2 Ω)⟫_ℝ)
    (fnL_dirichletLaplacianH10_apply u)
  exact h2.trans h1

/-- For $u, v \in D(A_1)$,
$$(A_1 u, v)_{H^1} = \langle Au, Av \rangle + \int_\Omega \nabla u \cdot \nabla v,$$
where $Au$ and $Av$ are the values of $A$ at the $L^2$ classes of $u$ and $v$. This is the
identity behind claim (iii) in the proof of Theorem 10.2 (a) of [brezis2011functional]. -/
theorem dirichletLaplacianH10_inner_eq (u v : (dirichletLaplacianH10 Ω).domain) :
    ⟪dirichletLaplacianH10 Ω u, (v : SobolevEuclideanZero N 1 2 Ω)⟫_ℝ
      = ⟪dirichletLaplacian Ω
          ⟨SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume u,
            u.2.1⟩,
        dirichletLaplacian Ω
          ⟨SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v,
            v.2.1⟩⟫_ℝ
        + dirichletForm Ω (u : SobolevEuclidean N 1 2 Ω) (v : SobolevEuclidean N 1 2 Ω) := by
  have h1 : ⟪dirichletLaplacianH10 Ω u, (v : SobolevEuclideanZero N 1 2 Ω)⟫_ℝ
      = laplaceForm Ω (dirichletLaplacianH10 Ω u : SobolevEuclidean N 1 2 Ω)
        (v : SobolevEuclidean N 1 2 Ω) := by
    rw [laplaceForm_apply_eq_inner, Submodule.coe_inner]
  have h2 := laplaceForm_apply_eq_dirichletForm_add_weakDeriv Ω
    (dirichletLaplacianH10 Ω u : SobolevEuclidean N 1 2 Ω) (v : SobolevEuclidean N 1 2 Ω)
  have h3 := dirichletForm_dirichletLaplacianH10_apply u v
  have h4 : ⟪weakDeriv (dirichletLaplacianH10 Ω u : SobolevEuclidean N 1 2 Ω) 0,
      weakDeriv (v : SobolevEuclidean N 1 2 Ω) 0⟫_ℝ
      = dirichletForm Ω (u : SobolevEuclidean N 1 2 Ω) (v : SobolevEuclidean N 1 2 Ω) :=
    inner_fnL_dirichletLaplacianH10_apply u v
  exact h1.trans (h2.trans (congrArg₂ (· + ·) h3 h4))

/-- **$A_1$ is monotone** in $H^1_0(\Omega)$: for every $v \in D(A_1)$,
$$(A_1 v, v)_{H^1} = \|Av\|_{L^2}^2 + \int_\Omega |\nabla v|^2 \ge 0.$$
This is claim (i) in the proof of Theorem 10.2 (a) of [brezis2011functional].

Monotonicity is `LinearPMap.IsMonotone`. -/
theorem dirichletLaplacianH10_isMonotone : (dirichletLaplacianH10 Ω).IsMonotone := fun v ↦ by
  rw [RCLike.re_to_real, dirichletLaplacianH10_inner_eq v v]
  exact add_nonneg real_inner_self_nonneg (dirichletForm_self_nonneg Ω _)

/-- **$A_1$ is symmetric** in $H^1_0(\Omega)$: $(A_1 u, v)_{H^1} = (u, A_1 v)_{H^1}$ for all
$u, v \in D(A_1)$. This is claim (iii) in the proof of Theorem 10.2 (a) of
[brezis2011functional].

The proof uses that $(A_1 u, v)_{H^1} = \langle Au, Av \rangle + \int_\Omega \nabla u \cdot
\nabla v$ is symmetric in $u$ and $v$. Symmetry is Mathlib's `LinearPMap.IsFormalAdjoint` of
$A_1$ with itself. -/
theorem dirichletLaplacianH10_isFormalAdjoint :
    (dirichletLaplacianH10 Ω).IsFormalAdjoint (dirichletLaplacianH10 Ω) := fun u v ↦ by
  have h1 := dirichletLaplacianH10_inner_eq u v
  have h2 := dirichletLaplacianH10_inner_eq v u
  have h3 : ⟪(u : SobolevEuclideanZero N 1 2 Ω), dirichletLaplacianH10 Ω v⟫_ℝ
      = ⟪dirichletLaplacianH10 Ω v, (u : SobolevEuclideanZero N 1 2 Ω)⟫_ℝ := real_inner_comm _ _
  have h4 := real_inner_comm (dirichletLaplacian Ω ⟨_, v.2.1⟩) (dirichletLaplacian Ω ⟨_, u.2.1⟩)
  have h5 : dirichletForm Ω (v : SobolevEuclidean N 1 2 Ω) (u : SobolevEuclidean N 1 2 Ω)
      = dirichletForm Ω (u : SobolevEuclidean N 1 2 Ω) (v : SobolevEuclidean N 1 2 Ω) := by
    have := dirichletForm_isHermitian Ω (v : SobolevEuclidean N 1 2 Ω)
      (u : SobolevEuclidean N 1 2 Ω)
    rwa [conj_trivial] at this
  exact h1.trans ((congrArg₂ (· + ·) h4 h5.symm).trans (h2.symm.trans h3.symm))

/-- Let $f \in H^1_0(\Omega)$, let $u \in D(A)$ satisfy $u + Au = f$ in $L^2(\Omega)$, and let
$v \in H^1_0(\Omega)$ have the $L^2$ class $u$. Then $v \in D(A_1)$ and $A_1 v = f - v$. -/
theorem mem_dirichletLaplacianH10Domain_of_add_apply_eq {f : SobolevEuclideanZero N 1 2 Ω}
    {u : (dirichletLaplacian Ω).domain}
    (hu : (u : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
        + dirichletLaplacian Ω u
      = SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume f)
    {v : SobolevEuclideanZero N 1 2 Ω}
    (hvu : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v
      = u) :
    v ∈ dirichletLaplacianH10Domain Ω ∧ ∀ hv : v ∈ dirichletLaplacianH10Domain Ω,
      dirichletLaplacianH10 Ω ⟨v, hv⟩ = f - v := by
  have hmem : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v
      ∈ dirichletLaplacianDomain Ω := hvu ▸ u.2
  have e1 := map_sub (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2
    Ω volume) f v
  have e2 : dirichletLaplacian Ω u
      = SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume f
        - (u : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :=
    eq_sub_of_add_eq' hu
  have e3 : dirichletLaplacianApply Ω (SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v) = dirichletLaplacian Ω u :=
    congrArg (dirichletLaplacianApply Ω) hvu
  have hA : dirichletLaplacianApply Ω (SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v)
      = SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
        (f - v) :=
    (e3.trans e2).trans ((congrArg (SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume f - ·) hvu.symm).trans e1.symm)
  refine ⟨mem_dirichletLaplacianH10Domain_iff.2 ⟨hmem, f - v, hA.symm⟩, fun hv ↦ ?_⟩
  refine SobolevMultiIndexZero.fnL_injective ?_
  exact (fnL_dirichletLaplacianH10Apply hv).trans hA

/-- **$R(I + A_1) = H^1_0(\Omega)$.** For every $f \in H^1_0(\Omega)$ there is $v \in D(A_1)$ with
$v + A_1 v = f$. This is claim (ii) in the proof of Theorem 10.2 (a) of [brezis2011functional].

The solution $u \in D(A)$ of $u + Au = f$ has $Au = f - u \in H^1_0(\Omega)$, so its
$H^1_0$-lift lies in $D(A_1)$ and solves $v + A_1 v = f$
(`mem_dirichletLaplacianH10Domain_of_add_apply_eq`). -/
theorem dirichletLaplacianH10_exists_add_apply_eq (f : SobolevEuclideanZero N 1 2 Ω) :
    ∃ v : (dirichletLaplacianH10 Ω).domain,
      (v : SobolevEuclideanZero N 1 2 Ω) + dirichletLaplacianH10 Ω v = f := by
  obtain ⟨u, hu⟩ := dirichletLaplacian_exists_add_apply_eq
    (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume f)
  obtain ⟨v, hv, hvu⟩ := dirichletLaplacian_exists_lift u
  obtain ⟨hmem, hA₁⟩ := mem_dirichletLaplacianH10Domain_of_add_apply_eq hu (v := ⟨v, hv⟩) hvu
  refine ⟨⟨⟨v, hv⟩, hmem⟩, ?_⟩
  rw [hA₁ hmem]
  abel

/-- **$A_1$ is maximal monotone** in $H^1_0(\Omega)$, on every open set $\Omega$: it is monotone,
and $R(I + A_1) = H^1_0(\Omega)$. These are claims (i) and (ii) in the proof of Theorem 10.2 (a)
of [brezis2011functional]. -/
theorem dirichletLaplacianH10_isMaximalMonotone : (dirichletLaplacianH10 Ω).IsMaximalMonotone :=
  ⟨dirichletLaplacianH10_isMonotone, dirichletLaplacianH10_exists_add_apply_eq⟩

/-- **$A_1$ is self-adjoint** in $H^1_0(\Omega)$, on every open set $\Omega$.

The proof applies Proposition 7.6 of [brezis2011functional] to the symmetric maximal monotone
operator $A_1$. Self-adjointness gives $u \in C([0, \infty); H^1_0(\Omega))$ for an initial
datum $u_0 \in H^1_0(\Omega)$ in Theorem 10.2 (a). -/
theorem dirichletLaplacianH10_isSelfAdjoint : IsSelfAdjoint (dirichletLaplacianH10 Ω) :=
  dirichletLaplacianH10_isMaximalMonotone.isSelfAdjoint_of_isFormalAdjoint
    dirichletLaplacianH10_isFormalAdjoint

/-! ### $D(A^\ell) \hookrightarrow H^{2\ell}(\Omega)$ on a $C^{2\ell}$ domain -/

/-- **The elliptic step at every order.** Let $m, k \in \mathbb{N}$ with $k = m + 2$, let $N \ge 1$,
and let $\Omega \subseteq \mathbb{R}^N$ be an open set of class $C^k$ with bounded boundary. If
$f \in D(A)$ and $Af$ has an $H^m$-lift, then $f$ has an $H^k$-lift.

The $H^1_0$-lift $v$ of $f$ is a weak solution of $-\Delta v = Af$, so
`Elliptic.regularity_dirichlet_higher_mem` applies to it. The order $k$ is a separate variable,
so that the statement needs no arithmetic on the order. The even case is
`dirichletLaplacian_exists_sobolev_of_apply`. -/
theorem dirichletLaplacian_exists_sobolev_add_two_of_apply {d : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} (m k : ℕ) (hk : k = m + 2)
    (hΩ : IsContDiffChartDomain k (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {f : (dirichletLaplacian Ω).domain} (w' : SobolevEuclidean (d + 1) m 2 Ω)
    (hw' : fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis m 2 Ω volume w'
      = dirichletLaplacian Ω f) :
    ∃ w : SobolevEuclidean (d + 1) k 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis k 2 Ω volume w = f := by
  subst hk
  obtain ⟨v, hv, hvf⟩ := dirichletLaplacian_exists_lift f
  have hg : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (⇑(dirichletLaplacian Ω f)) m 2 Ω volume := by
    refine (memSobolevMultiIndex w').congr_ae ?_
    rw [← hw']
    rfl
  have heq : ∀ Φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω,
      dirichletForm Ω v Φ = load Ω (dirichletLaplacian Ω f) Φ := fun Φ hΦ ↦
    (dirichletLaplacian_inner_eq_dirichletForm f hv hvf hΦ).symm
  obtain ⟨w, hw⟩ :=
    (regularity_dirichlet_higher_mem m hΩ hΓ hv hg heq).exists_sobolevMultiIndex
  refine ⟨w, Lp.ext (hw.trans ?_)⟩
  rw [← hvf]
  rfl

/-- **The inductive step of $D(A^\ell) \subseteq H^{2\ell}(\Omega)$.** Let $\ell, k \in \mathbb{N}$
with $k = 2\ell + 2$, let $N \ge 1$, and let $\Omega \subseteq \mathbb{R}^N$ be an open set of
class $C^k$ with bounded boundary. If $f \in D(A)$ and $Af$ has an $H^{2\ell}$-lift, then $f$
has an $H^k$-lift. This is the even case of
`dirichletLaplacian_exists_sobolev_add_two_of_apply`. -/
theorem dirichletLaplacian_exists_sobolev_of_apply {d : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} (ℓ k : ℕ) (hk : k = 2 * ℓ + 2)
    (hΩ : IsContDiffChartDomain k (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {f : (dirichletLaplacian Ω).domain} (w' : SobolevEuclidean (d + 1) (2 * ℓ) 2 Ω)
    (hw' : fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (2 * ℓ) 2 Ω volume w'
      = dirichletLaplacian Ω f) :
    ∃ w : SobolevEuclidean (d + 1) k 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis k 2 Ω volume w = f :=
  dirichletLaplacian_exists_sobolev_add_two_of_apply (2 * ℓ) k hk hΩ hΓ w' hw'

/-- **$D(A^\ell) \subseteq H^{2\ell}(\Omega)$, in the form of the induction on $\ell$.** Let
$\ell, k \in \mathbb{N}$ with $k = 2\ell$, let $N \ge 1$, and let
$\Omega \subseteq \mathbb{R}^N$ be an open set of class $C^k$ with bounded boundary. Then for
every $x \in D(A^\ell)$, the coordinate $A^0 x$ has an $H^k$-lift.

The order $k$ is a separate variable, so that no arithmetic on the order is needed. In the
inductive step, $x \in D(A^{\ell+1})$ has $Ax \in D(A^\ell) \subseteq H^{2\ell}(\Omega)$, hence
$x \in H^{2\ell+2}(\Omega)$ by `dirichletLaplacian_exists_sobolev_of_apply`. The form with
$k = 2\ell$ substituted is `dirichletLaplacian_exists_sobolev_of_powDomain`. -/
theorem dirichletLaplacian_exists_sobolev_of_powDomain' {d : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} (ℓ : ℕ) :
    ∀ k : ℕ, k = 2 * ℓ → IsContDiffChartDomain k (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) →
    Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) →
    ∀ x : (dirichletLaplacian Ω).PowDomain ℓ, ∃ w : SobolevEuclidean (d + 1) k 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis k 2 Ω volume w
        = LinearPMap.PowDomain.applyL (dirichletLaplacian Ω) ℓ 0 x := by
  induction ℓ with
  | zero =>
    intro k hk _ _ x
    subst hk
    obtain ⟨w, hw⟩ := (memSobolevMultiIndex_zero_iff.2
      (Lp.memLp (LinearPMap.PowDomain.applyL (dirichletLaplacian Ω) 0 0
        x))).exists_sobolevMultiIndex (b := (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis)
    exact ⟨w, Lp.ext hw⟩
  | succ ℓ ih =>
    intro k hk hΩ hΓ x
    have hΩ' : IsContDiffChartDomain (2 * ℓ) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) :=
      hΩ.of_le (by exact_mod_cast (by omega : 2 * ℓ ≤ k))
    obtain ⟨w', hw'⟩ :=
      ih (2 * ℓ) rfl hΩ' hΓ (LinearPMap.PowDomain.shiftL (dirichletLaplacian Ω) ℓ x)
    exact dirichletLaplacian_exists_sobolev_of_apply ℓ k (by omega) hΩ hΓ w'
      (hw'.trans (LinearPMap.PowDomain.applyL_zero_shiftL x))

/-- **$D(A^\ell) \subseteq H^{2\ell}(\Omega)$ on a $C^{2\ell}$ domain with bounded boundary.** Let
$\ell \in \mathbb{N}$, let $N \ge 1$, and let $\Omega \subseteq \mathbb{R}^N$ be an open set of
class $C^{2\ell}$ with bounded boundary. Then for every $x \in D(A^\ell)$, the coordinate
$A^0 x$ has an $H^{2\ell}$-lift. This is the membership half of the identification (7) in §10.1
of [brezis2011functional]. -/
theorem dirichletLaplacian_exists_sobolev_of_powDomain {d : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} (ℓ : ℕ)
    (hΩ : IsContDiffChartDomain (2 * ℓ) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (x : (dirichletLaplacian Ω).PowDomain ℓ) :
    ∃ w : SobolevEuclidean (d + 1) (2 * ℓ) 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (2 * ℓ) 2 Ω volume w
        = LinearPMap.PowDomain.applyL (dirichletLaplacian Ω) ℓ 0 x :=
  dirichletLaplacian_exists_sobolev_of_powDomain' ℓ (2 * ℓ) rfl hΩ hΓ x

open LinearPMap.PowDomain in
/-- **The odd orders: $H^{2\ell+1}(\Omega)$ regularity**, in the form of an induction on $\ell$. Let
$\ell, k \in \mathbb{N}$ with $k = 2\ell + 1$, let $N \ge 1$, and let
$\Omega \subseteq \mathbb{R}^N$ be an open set of class $C^k$ with bounded boundary. Let
$x \in D(A^\ell)$, and suppose that its last coordinate $A^\ell x$ lies in $H^1_0(\Omega)$. Then
the coordinate $A^0 x$ has an $H^k$-lift.

The order $k$ is a separate variable, so that no arithmetic on the order is needed. For
$\ell = 0$ the hypothesis gives the conclusion. In the inductive step, the induction hypothesis
gives $Ax \in H^{2\ell+1}(\Omega)$, and `dirichletLaplacian_exists_sobolev_add_two_of_apply`
gives $x \in H^{2\ell+3}(\Omega)$. This is the odd-order companion of
`dirichletLaplacian_exists_sobolev_of_powDomain`. -/
theorem dirichletLaplacian_exists_sobolev_of_powDomain_of_last {d : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} (ℓ : ℕ) :
    ∀ k : ℕ, k = 2 * ℓ + 1 →
    IsContDiffChartDomain k (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) →
    Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) →
    ∀ x : (dirichletLaplacian Ω).PowDomain ℓ,
    (∃ w : SobolevEuclideanZero (d + 1) 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume w
        = applyL (dirichletLaplacian Ω) ℓ (Fin.last ℓ) x) →
    ∃ w : SobolevEuclidean (d + 1) k 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis k 2 Ω volume w
        = applyL (dirichletLaplacian Ω) ℓ 0 x := by
  induction ℓ with
  | zero =>
    intro k hk _ _ x hx
    subst hk
    obtain ⟨w, hw⟩ := hx
    exact ⟨(w : SobolevEuclidean (d + 1) 1 2 Ω), hw.trans (congrArg
      (fun i ↦ applyL (dirichletLaplacian Ω) 0 i x) (by simp : Fin.last 0 = 0))⟩
  | succ ℓ ih =>
    intro k hk hΩ hΓ x hx
    have hΩ' : IsContDiffChartDomain (2 * ℓ + 1) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) :=
      hΩ.of_le (by exact_mod_cast (by omega : 2 * ℓ + 1 ≤ k))
    have hlast : ∃ w : SobolevEuclideanZero (d + 1) 1 2 Ω,
        SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
          w = applyL (dirichletLaplacian Ω) ℓ (Fin.last ℓ) (shiftL (dirichletLaplacian Ω) ℓ x) := by
      obtain ⟨w, hw⟩ := hx
      exact ⟨w, hw.trans ((congrArg (fun i ↦ applyL (dirichletLaplacian Ω) (ℓ + 1) i x)
        (Fin.succ_last ℓ).symm).trans (applyL_shiftL (Fin.last ℓ) x).symm)⟩
    obtain ⟨w', hw'⟩ := ih (2 * ℓ + 1) rfl hΩ' hΓ (shiftL (dirichletLaplacian Ω) ℓ x) hlast
    have := dirichletLaplacian_exists_sobolev_add_two_of_apply (2 * ℓ + 1) k (by omega) hΩ hΓ
      (f := ⟨applyL (dirichletLaplacian Ω) (ℓ + 1) 0 x, applyL_mem_domain x 0⟩) w'
      (hw'.trans (applyL_zero_shiftL x))
    exact this

/-- **The continuous injection $D(A^\ell) \hookrightarrow H^{2\ell}(\Omega)$.** Let
$\ell \in \mathbb{N}$, let $N \ge 1$, and let $\Omega \subseteq \mathbb{R}^N$ be an open set of
class $C^{2\ell}$ with bounded boundary. This is the bounded linear map
$D(A^\ell) \to H^{2\ell}(\Omega)$ that takes $x$ to the $H^{2\ell}$-lift of its coordinate
$A^0 x$. It is the statement "$D(A^\ell) \subset H^{2\ell}(\Omega)$ with continuous injection"
that accompanies the identification (7) in §10.1 of [brezis2011functional].

The lift exists by `dirichletLaplacian_exists_sobolev_of_powDomain`, and the map is bounded by
the closed graph theorem
(`SobolevEuclidean.exists_continuousLinearMap_of_forall_exists_fnL_eq`). Its defining property
is `fnL_powDomainToSobolevL`. The map turns lifts in the class `LinearPMap.ContDiffOnPowDomain`
of chapter 7 into lifts in the class `Bochner.ContDiffOnThrough`
(`Bochner.ContDiffOnThrough.of_contDiffOnPowDomain`). -/
def dirichletLaplacian.powDomainToSobolevL {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    {ℓ : ℕ} (hΩ : IsContDiffChartDomain (2 * ℓ) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    (dirichletLaplacian Ω).PowDomain ℓ →L[ℝ] SobolevEuclidean (d + 1) (2 * ℓ) 2 Ω :=
  haveI : CompleteSpace ((dirichletLaplacian Ω).PowDomain ℓ) :=
    dirichletLaplacian_isClosed.completeSpace_powDomain ℓ
  Classical.choose (SobolevEuclidean.exists_continuousLinearMap_of_forall_exists_fnL_eq
    (S := LinearPMap.PowDomain.applyL (dirichletLaplacian Ω) ℓ 0)
    (dirichletLaplacian_exists_sobolev_of_powDomain ℓ hΩ hΓ))

/-- Let $N \ge 1$, and let $\Omega \subseteq \mathbb{R}^N$ be an open set of class $C^{2\ell}$ with
bounded boundary. For every $x \in D(A^\ell)$, the $L^2$ class of the image of $x$ under the
injection $D(A^\ell) \hookrightarrow H^{2\ell}(\Omega)$
(`dirichletLaplacian.powDomainToSobolevL`) is the coordinate $A^0 x$. -/
theorem fnL_powDomainToSobolevL {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} {ℓ : ℕ}
    (hΩ : IsContDiffChartDomain (2 * ℓ) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (x : (dirichletLaplacian Ω).PowDomain ℓ) :
    fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (2 * ℓ) 2 Ω volume
        (dirichletLaplacian.powDomainToSobolevL hΩ hΓ x)
      = LinearPMap.PowDomain.applyL (dirichletLaplacian Ω) ℓ 0 x :=
  haveI : CompleteSpace ((dirichletLaplacian Ω).PowDomain ℓ) :=
    dirichletLaplacian_isClosed.completeSpace_powDomain ℓ
  Classical.choose_spec (SobolevEuclidean.exists_continuousLinearMap_of_forall_exists_fnL_eq
    (S := LinearPMap.PowDomain.applyL (dirichletLaplacian Ω) ℓ 0)
    (dirichletLaplacian_exists_sobolev_of_powDomain ℓ hΩ hΓ)) x

/-- **The bound of the injection $D(A^\ell) \hookrightarrow H^{2\ell}(\Omega)$.** Let $N \ge 1$, and
let $\Omega \subseteq \mathbb{R}^N$ be an open set of class $C^{2\ell}$ with bounded boundary.
There is $C \ge 0$ such that for every $x \in D(A^\ell)$ and every $H^{2\ell}$-lift $w$ of
$A^0 x$,
$$\|w\|_{H^{2\ell}} \le C \|x\|_{D(A^\ell)},$$
where $\|x\|_{D(A^\ell)} = (\sum_{j \le \ell} \|A^j x\|_{L^2}^2)^{1/2}$. -/
theorem dirichletLaplacian_norm_sobolev_le_of_powDomain {d : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} {ℓ : ℕ}
    (hΩ : IsContDiffChartDomain (2 * ℓ) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : (dirichletLaplacian Ω).PowDomain ℓ)
      (w : SobolevEuclidean (d + 1) (2 * ℓ) 2 Ω),
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (2 * ℓ) 2 Ω volume w
        = LinearPMap.PowDomain.applyL (dirichletLaplacian Ω) ℓ 0 x → ‖w‖ ≤ C * ‖x‖ := by
  refine ⟨‖dirichletLaplacian.powDomainToSobolevL hΩ hΓ‖, norm_nonneg _, fun x w hw ↦ ?_⟩
  have : w = dirichletLaplacian.powDomainToSobolevL hΩ hΓ x :=
    SobolevMultiIndex.fnL_injective (hw.trans (fnL_powDomainToSobolevL hΩ hΓ x).symm)
  rw [this]
  exact ContinuousLinearMap.le_opNorm _ x

/-!
### The identification (7) of $D(A^\ell)$

On a $C^{2\ell}$ domain with bounded boundary, $D(A^\ell) = \{u \in H^{2\ell}(\Omega) : u = \Delta
u = \dots = \Delta^{\ell - 1} u = 0 \text{ on } \Gamma\}$.
-/

variable (Ω) in
/-- **The boundary conditions of the identification (7)**,
$u = \Delta u = \dots = \Delta^{\ell - 1} u = 0$ on $\Gamma$, read without traces. A function
$f \in L^2(\Omega)$ satisfies `IsDirichletLaplacianChain Ω ℓ f` if there is a chain
$g_0 = f, g_1, \dots, g_\ell$ in $L^2(\Omega)$ such that for each $j < \ell$:

* $g_j$ has an $H^1_0$-lift (the condition "$\Delta^j u = 0$ on $\Gamma$");
* $g_j$ has an $H^2$-lift $w_j$ with $g_{j+1} = -\Delta w_j$.

Then $g_j = (-\Delta)^j f$. The reading of "$\Delta^j u = 0$ on $\Gamma$" as membership in
$H^1_0(\Omega)$ is the trace-free reading of Theorem 9.17 of [brezis2011functional]. The weak
Laplacian of $w \in H^2(\Omega)$ is `sobolevLaplacianL Ω w`. -/
def IsDirichletLaplacianChain (ℓ : ℕ)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) : Prop :=
  ∃ g : Fin (ℓ + 1) → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), g 0 = f ∧
    ∀ j : Fin ℓ, (∃ v : SobolevEuclidean N 1 2 Ω, v ∈ SobolevEuclideanZero N 1 2 Ω ∧
        fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v = g j.castSucc) ∧
      ∃ w : SobolevEuclidean N 2 2 Ω,
        fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 2 Ω volume w = g j.castSucc ∧
        g j.succ = -sobolevLaplacianL Ω w

/-- Consecutive terms of a chain are related by $A$. Let $g_0, \dots, g_\ell \in L^2(\Omega)$ and
$j < \ell$. If $g_j$ has an $H^1_0$-lift and an $H^2$-lift $w$ with $g_{j+1} = -\Delta w$, then
$g_j \in D(A)$ and $A g_j = g_{j+1}$. -/
theorem IsDirichletLaplacianChain.exists_apply_eq {ℓ : ℕ}
    {g : Fin (ℓ + 1) → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    {j : Fin ℓ}
    (hv : ∃ v : SobolevEuclidean N 1 2 Ω, v ∈ SobolevEuclideanZero N 1 2 Ω ∧
      fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v = g j.castSucc)
    (hw : ∃ w : SobolevEuclidean N 2 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 2 Ω volume w = g j.castSucc ∧
      g j.succ = -sobolevLaplacianL Ω w) :
    ∃ h : g j.castSucc ∈ (dirichletLaplacian Ω).domain,
      dirichletLaplacian Ω ⟨g j.castSucc, h⟩ = g j.succ := by
  obtain ⟨v, hv, hvg⟩ := hv
  obtain ⟨w, hwg, hg⟩ := hw
  have hvw : fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn w :=
    Filter.EventuallyEq.of_eq (congrArg (fun z : Lp ℝ 2 (volume.restrict
      (Ω : Set (EuclideanSpace ℝ (Fin N)))) ↦ (z : EuclideanSpace ℝ (Fin N) → ℝ))
      (hvg.trans hwg.symm))
  obtain ⟨hmem, happ⟩ := mem_dirichletLaplacianDomain_of_sobolev_two w hv hvw
  rw [hvg] at hmem happ
  exact ⟨hmem, (dirichletLaplacian_apply _).trans (happ.trans hg.symm)⟩

/-- **A chain lies in $D(A^\ell)$, on every open set.** If $f \in L^2(\Omega)$ satisfies
`IsDirichletLaplacianChain Ω ℓ f`, then there is $x \in D(A^\ell)$ with $A^0 x = f$. This is the
inclusion $\supseteq$ of the identification (7) in §10.1 of [brezis2011functional], which needs
no regularity of $\Omega$.

The element $x$ is the tuple $(f, -\Delta f, \dots)$ of the chain, built with
`LinearPMap.PowDomain.mk`; consecutive entries are related by $A$ by
`mem_dirichletLaplacianDomain_of_sobolev_two`. -/
theorem IsDirichletLaplacianChain.exists_powDomain {ℓ : ℕ}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (h : IsDirichletLaplacianChain Ω ℓ f) :
    ∃ x : (dirichletLaplacian Ω).PowDomain ℓ,
      LinearPMap.PowDomain.applyL (dirichletLaplacian Ω) ℓ 0 x = f := by
  obtain ⟨g, hg0, hg⟩ := h
  refine ⟨LinearPMap.PowDomain.mk (dirichletLaplacian Ω) g fun j ↦ ?_, hg0⟩
  exact IsDirichletLaplacianChain.exists_apply_eq (hg j).1 (hg j).2

/-- **$Af = -\Delta w$ for every $H^2$-lift $w$ of $f \in D(A)$.** Let $w \in H^2(\Omega)$ and
$f \in D(A)$, and let the $L^2$ class of $w$ be $f$. Then $Af = -\Delta w$, where $\Delta w$ is
`sobolevLaplacianL Ω w`. This holds on every open set. -/
theorem dirichletLaplacian_apply_eq_neg_sobolevLaplacianL (w : SobolevEuclidean N 2 2 Ω)
    (f : (dirichletLaplacian Ω).domain)
    (hwf : fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 2 Ω volume w = f) :
    dirichletLaplacian Ω f = -sobolevLaplacianL Ω w := by
  obtain ⟨v, hv, hvf⟩ := dirichletLaplacian_exists_lift f
  have hvw : fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn w :=
    Filter.EventuallyEq.of_eq (congrArg (fun z : Lp ℝ 2 (volume.restrict
      (Ω : Set (EuclideanSpace ℝ (Fin N)))) ↦ (z : EuclideanSpace ℝ (Fin N) → ℝ))
      (hvf.trans hwf.symm))
  exact dirichletLaplacian_apply_of_sobolev_two w hv hvw f hvf

/-- **Every $f \in D(A)$ has an $H^2$-lift** on a $C^2$ domain with bounded boundary: let $N \ge 1$,
and let $\Omega \subseteq \mathbb{R}^N$ be an open set of class $C^2$ with bounded boundary.
Then every $f \in D(A)$ is the $L^2$ class of some $w \in H^2(\Omega)$. -/
theorem dirichletLaplacian_exists_sobolev_two_lift {d : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffChartDomain 2 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (f : (dirichletLaplacian Ω).domain) :
    ∃ w : SobolevEuclidean (d + 1) 2 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 2 2 Ω volume w = f := by
  obtain ⟨C, -, hC⟩ := dirichletLaplacian_exists_sobolev_two_of_isContDiffChartDomain hΩ hΓ
  exact (hC f).1

/-- Let $N \ge 1$, and let $\Omega \subseteq \mathbb{R}^N$ be an open set of class $C^2$ with
bounded boundary. Every $f \in D(A)$ has an $H^1_0$-lift and an $H^2$-lift $w$, and
$Af = -\Delta w$, where $\Delta w$ is `sobolevLaplacianL Ω w`. -/
theorem dirichletLaplacian_exists_lifts_of_isContDiffChartDomain {d : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffChartDomain 2 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (f : (dirichletLaplacian Ω).domain) :
    (∃ v : SobolevEuclidean (d + 1) 1 2 Ω, v ∈ SobolevEuclideanZero (d + 1) 1 2 Ω ∧
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume v = f) ∧
    ∃ w : SobolevEuclidean (d + 1) 2 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 2 2 Ω volume w = f ∧
      dirichletLaplacian Ω f = -sobolevLaplacianL Ω w := by
  obtain ⟨w, hw⟩ := dirichletLaplacian_exists_sobolev_two_lift hΩ hΓ f
  exact ⟨dirichletLaplacian_exists_lift f, w, hw,
    dirichletLaplacian_apply_eq_neg_sobolevLaplacianL w f hw⟩

/-- **The iterates of an element of $D(A^\ell)$ form a chain.** Let $N \ge 1$, and let
$\Omega \subseteq \mathbb{R}^N$ be an open set of class $C^2$ with bounded boundary. For every
$x \in D(A^\ell)$, the coordinate $A^0 x$ satisfies `IsDirichletLaplacianChain Ω ℓ`.

The chain is $g_j = A^j x$. For $j < \ell$, $g_j$ lies in
$D(A) = H^2(\Omega) \cap H^1_0(\Omega)$, and $A g_j = -\Delta w_j$ for its $H^2$-lift $w_j$
(`dirichletLaplacian_exists_lifts_of_isContDiffChartDomain`). -/
theorem isDirichletLaplacianChain_of_powDomain {d : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffChartDomain 2 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) {ℓ : ℕ}
    (x : (dirichletLaplacian Ω).PowDomain ℓ) :
    IsDirichletLaplacianChain Ω ℓ (LinearPMap.PowDomain.applyL (dirichletLaplacian Ω) ℓ 0 x) := by
  refine ⟨fun j ↦ LinearPMap.PowDomain.applyL (dirichletLaplacian Ω) ℓ j x, rfl, fun j ↦ ?_⟩
  obtain ⟨hv, w, hw, hA⟩ := dirichletLaplacian_exists_lifts_of_isContDiffChartDomain hΩ hΓ
    ⟨_, LinearPMap.PowDomain.applyL_mem_domain x j⟩
  refine ⟨hv, w, hw, ?_⟩
  exact (LinearPMap.PowDomain.apply_applyL x j).symm.trans hA

/-- **The identification (7)** in §10.1 of [brezis2011functional], in the proof of Theorem 10.1. Let
$\ell \in \mathbb{N}$, let $N \ge 1$, and let $\Omega \subseteq \mathbb{R}^N$ be an open set of
class $C^{2\ell}$ with bounded boundary. Then
$$D(A^\ell) = \{u \in H^{2\ell}(\Omega) : u = \Delta u = \dots = \Delta^{\ell - 1} u = 0 \text{
  on } \Gamma\}:$$
a function $f \in L^2(\Omega)$ is the coordinate $A^0 x$ of some $x \in D(A^\ell)$ if and only
if $f$ has an $H^{2\ell}$-lift and satisfies `IsDirichletLaplacianChain Ω ℓ f`.

The boundary conditions are read as `IsDirichletLaplacianChain`: each iterate $(-\Delta)^j u$,
$j < \ell$, lies in $H^1_0(\Omega)$ and in $H^2(\Omega)$, and the next iterate is its weak
Laplacian with the sign changed. The inclusion $\subseteq$ is the iterated regularity theorem
`dirichletLaplacian_exists_sobolev_of_powDomain` together with
`isDirichletLaplacianChain_of_powDomain`. The inclusion $\supseteq$ is
`IsDirichletLaplacianChain.exists_powDomain` and holds on every open set. For $\ell = 0$ both
sides hold for every $f$. -/
theorem dirichletLaplacian_mem_powDomain_iff {d : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} {ℓ : ℕ}
    (hΩ : IsContDiffChartDomain (2 * ℓ) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    (∃ x : (dirichletLaplacian Ω).PowDomain ℓ,
        LinearPMap.PowDomain.applyL (dirichletLaplacian Ω) ℓ 0 x = f) ↔
      (∃ w : SobolevEuclidean (d + 1) (2 * ℓ) 2 Ω,
        fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (2 * ℓ) 2 Ω volume w = f) ∧
      IsDirichletLaplacianChain Ω ℓ f := by
  refine ⟨fun ⟨x, hx⟩ ↦ ⟨hx ▸ dirichletLaplacian_exists_sobolev_of_powDomain ℓ hΩ hΓ x, ?_⟩,
    fun h ↦ h.2.exists_powDomain⟩
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · exact ⟨fun _ ↦ f, rfl, fun j ↦ j.elim0⟩
  · have hΩ2 : IsContDiffChartDomain 2 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) :=
      hΩ.of_le (by exact_mod_cast (by omega : 2 ≤ 2 * ℓ))
    exact hx ▸ isDirichletLaplacianChain_of_powDomain hΩ2 hΓ x

/-! ### The bounded injection $D(A_1) \hookrightarrow H^3(\Omega)$ on a $C^3$ domain -/

section SobolevThree

open LinearPMap LinearPMap.PowDomain

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **The weak equation of an element of $D(A_1)$.** Let $N \ge 1$ and let
$\Omega \subseteq \mathbb{R}^N$ be open. For $y \in D(A_1)$ and $\varphi \in H^1_0(\Omega)$,
$$\int_\Omega \nabla y \cdot \nabla \varphi = \int_\Omega (A_1 y) \varphi.$$
-/
theorem dirichletForm_eq_load_fnL_dirichletLaplacianH10_apply (y : (dirichletLaplacianH10 Ω).domain)
    {φ : SobolevEuclidean (d + 1) 1 2 Ω} (hφ : φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω) :
    dirichletForm Ω ((y : SobolevEuclideanZero (d + 1) 1 2 Ω) : SobolevEuclidean (d + 1) 1 2 Ω) φ
      = load Ω (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
        volume (dirichletLaplacianH10 Ω y)) φ := by
  have h1 := fnL_dirichletLaplacianH10_apply y
  have h2 := dirichletLaplacian_inner_eq_dirichletForm ⟨_, y.2.1⟩
    (y : SobolevEuclideanZero (d + 1) 1 2 Ω).2 rfl hφ
  have h3 := congrArg (fun z ↦ ⟪z, fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
    volume φ⟫_ℝ) h1
  exact h2.symm.trans h3.symm

/-- **$H^3$ regularity of a weak solution with an $H^1$ datum.** Let $N \ge 1$, and let
$\Omega \subseteq \mathbb{R}^N$ be an open set of class $C^3$ with bounded boundary. Let
$v \in H^1_0(\Omega)$ and $g \in L^2(\Omega)$ with $g \in H^1(\Omega)$, and suppose that
$\int_\Omega \nabla v \cdot \nabla \varphi = \int_\Omega g \varphi$ for all
$\varphi \in H^1_0(\Omega)$. Then $v$ has an $H^3$-lift: there is $U \in H^3(\Omega)$ with the
same $L^2$ class as $v$.

This is Theorem 9.25 of [brezis2011functional] at order $m = 1$
(`Elliptic.regularity_dirichlet_higher_mem`), with the conclusion given as an element of
$H^3(\Omega)$. The weak equation is `Elliptic.IsWeakSolution` for `Elliptic.dirichletForm Ω`. -/
theorem Elliptic.exists_sobolev_three_of_forall_dirichletForm_eq_load
    (hΩ : IsContDiffChartDomain 3 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {v : SobolevEuclidean (d + 1) 1 2 Ω} (hv : v ∈ SobolevEuclideanZero (d + 1) 1 2 Ω)
    {g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    (hg : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (⇑g) 1 2 Ω volume)
    (heq : Elliptic.IsWeakSolution (dirichletForm Ω) (SobolevEuclideanZero (d + 1) 1 2 Ω) v g) :
    ∃ U : SobolevEuclidean (d + 1) 3 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 3 2 Ω volume U
        = fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume v := by
  have hΩ' : IsContDiffChartDomain ((1 : ℕ) + 2) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) :=
    hΩ.of_le (by norm_num)
  have hmem := regularity_dirichlet_higher_mem 1 hΩ' hΓ hv hg heq
  have key : ∀ k : ℕ, k = 1 + 2 →
      MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (fn v) k 2 Ω
        volume := by
    intro k hk
    subst hk
    exact hmem
  obtain ⟨U, hU⟩ := (key 3 rfl).exists_sobolevMultiIndex
  exact ⟨U, Lp.ext hU⟩

/-- **An element of $D(A_1)$ lies in $H^3(\Omega)$.** Let $N \ge 1$, and let
$\Omega \subseteq \mathbb{R}^N$ be an open set of class $C^3$ with bounded boundary. Every
$y \in D(A_1)$ has an $H^3$-lift: there is $U \in H^3(\Omega)$ with the same $L^2$ class as $y$.

Here $y \in H^1_0(\Omega)$ with $Ay \in H^1_0(\Omega)$. Then $y$ is a weak solution of
$-\Delta y = A_1 y$ with a datum in $H^1(\Omega)$, so Theorem 9.25 of [brezis2011functional]
gives $y \in H^3(\Omega)$. -/
theorem dirichletLaplacianH10_exists_sobolev_three
    (hΩ : IsContDiffChartDomain 3 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (y : (dirichletLaplacianH10 Ω).domain) :
    ∃ U : SobolevEuclidean (d + 1) 3 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 3 2 Ω volume U
        = SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
          volume (y : SobolevEuclideanZero (d + 1) 1 2 Ω) := by
  have hg : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (⇑(SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
        (dirichletLaplacianH10 Ω y))) 1 2 Ω volume :=
    (memSobolevMultiIndex ((dirichletLaplacianH10 Ω y : SobolevEuclideanZero (d + 1) 1 2 Ω) :
      SobolevEuclidean (d + 1) 1 2 Ω)).congr_ae
      (Filter.EventuallyEq.of_eq (SobolevMultiIndexZero.fnL_apply _).symm)
  exact exists_sobolev_three_of_forall_dirichletForm_eq_load hΩ hΓ
    (y : SobolevEuclideanZero (d + 1) 1 2 Ω).2 hg
    fun φ hφ ↦ dirichletForm_eq_load_fnL_dirichletLaplacianH10_apply y hφ

/-- Let $N \ge 1$, and let $\Omega \subseteq \mathbb{R}^N$ be an open set of class $C^3$ with
bounded boundary. For every $x$ in $D(A_1)$ with the graph norm, the $L^2$ class of the
coordinate $A_1^0 x \in H^1_0(\Omega)$ is the $L^2$ class of some $U \in H^3(\Omega)$.

This is `dirichletLaplacianH10_exists_sobolev_three` for the coordinate $A_1^0 x$, in the
composed form that the closed graph theorem uses. The space $D(A_1)$ with the graph norm is
`LinearPMap.PowDomain (dirichletLaplacianH10 Ω) 1`. -/
theorem dirichletLaplacianH10_exists_sobolev_three_comp
    (hΩ : IsContDiffChartDomain 3 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (x : (dirichletLaplacianH10 Ω).PowDomain 1) :
    ∃ U : SobolevEuclidean (d + 1) 3 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 3 2 Ω volume U
        = ((SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
          volume).comp (applyL (dirichletLaplacianH10 Ω) 1 0)) x := by
  have hmem := applyL_mem_domain x 0
  have h := dirichletLaplacianH10_exists_sobolev_three hΩ hΓ
    ⟨applyL (dirichletLaplacianH10 Ω) 1 0 x, hmem⟩
  rw [ContinuousLinearMap.comp_apply]
  exact h

set_option maxHeartbeats 1000000 in
-- The instance chain of `D(A₁)` (a submodule of `PiLp 2 (Fin 2 → H¹₀(Ω))`, itself a submodule
-- of a subtype of a `PiLp` of `L²` spaces) makes the defeq checks of the closed graph lemma's
-- instance arguments exceed the default budget; the term itself is a single application.
variable (Ω) in
/-- **The bounded injection $D(A_1) \hookrightarrow H^3(\Omega)$.** Let $N \ge 1$, and let
$\Omega \subseteq \mathbb{R}^N$ be an open set of class $C^3$ with bounded boundary. This is the
bounded linear map from the Hilbert space $D(A_1)$ with the graph norm to $H^3(\Omega)$ that
takes $x$ to the $H^3$-lift of its coordinate $A_1^0 x$.

The domain is `LinearPMap.PowDomain (dirichletLaplacianH10 Ω) 1`. The map is bounded by the
closed graph theorem (`exists_continuousLinearMap_comp_eq_of_injective`), and
`fnL_powDomainOneToSobolevThreeL` is its defining property. -/
def dirichletLaplacianH10.powDomainOneToSobolevThreeL
    (hΩ : IsContDiffChartDomain 3 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    (dirichletLaplacianH10 Ω).PowDomain 1 →L[ℝ] SobolevEuclidean (d + 1) 3 2 Ω :=
  haveI : CompleteSpace ((dirichletLaplacianH10 Ω).PowDomain 1) :=
    dirichletLaplacianH10_isMaximalMonotone.isClosed.completeSpace_powDomain 1
  Classical.choose (exists_continuousLinearMap_comp_eq_of_injective
    (J := fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 3 2 Ω volume)
    SobolevMultiIndex.fnL_injective
    (S := (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume).comp (applyL (dirichletLaplacianH10 Ω) 1 0))
    (dirichletLaplacianH10_exists_sobolev_three_comp hΩ hΓ))

set_option maxHeartbeats 1000000 in
-- Same instance chain as in the definition above.
/-- Let $N \ge 1$, and let $\Omega \subseteq \mathbb{R}^N$ be an open set of class $C^3$ with
bounded boundary. For every $x$ in $D(A_1)$ with the graph norm, the $L^2$ class of the image of
$x$ under the injection $D(A_1) \hookrightarrow H^3(\Omega)$ is the $L^2$ class of the
coordinate $A_1^0 x \in H^1_0(\Omega)$. -/
theorem fnL_powDomainOneToSobolevThreeL
    (hΩ : IsContDiffChartDomain 3 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (x : (dirichletLaplacianH10 Ω).PowDomain 1) :
    fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 3 2 Ω volume
      (dirichletLaplacianH10.powDomainOneToSobolevThreeL Ω hΩ hΓ x)
      = SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
        (applyL (dirichletLaplacianH10 Ω) 1 0 x) :=
  haveI : CompleteSpace ((dirichletLaplacianH10 Ω).PowDomain 1) :=
    dirichletLaplacianH10_isMaximalMonotone.isClosed.completeSpace_powDomain 1
  (Classical.choose_spec (exists_continuousLinearMap_comp_eq_of_injective
    (J := fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 3 2 Ω volume)
    SobolevMultiIndex.fnL_injective
    (S := (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume).comp (applyL (dirichletLaplacianH10 Ω) 1 0))
    (dirichletLaplacianH10_exists_sobolev_three_comp hΩ hΓ)) x).trans
    (ContinuousLinearMap.comp_apply _ _ _)

end SobolevThree

end
