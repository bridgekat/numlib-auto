/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.PDE.Elliptic.Regularity
import NumlibSurface.Brezis.Chapter09.Section05

/-!
# Brezis, Section 9.6: Regularity of weak solutions

This module formalizes Section 9.6 of [brezis2011functional]. Let $\Omega \subset \mathbb{R}^N$ be
open with boundary $\Gamma$, let $f \in L^2(\Omega)$, and let $u \in H_0^1(\Omega)$ be the weak
solution of the Dirichlet problem
$$\int_\Omega \nabla u \cdot \nabla \varphi + \int_\Omega u \varphi = \int_\Omega f \varphi \quad
  \text{for all } \varphi \in H_0^1(\Omega). \qquad (48)$$
Theorem 9.25 says that $u$ gains two derivatives. If $\Omega$ is of class $C^2$ with $\Gamma$
bounded, or $\Omega = \mathbb{R}^N_+$, then $u \in H^2(\Omega)$ and $\|u\|_{H^2} \le C \|f\|_{L^2}$.
If moreover $\Omega$ is of class $C^{m+2}$ and $f \in H^m(\Omega)$, then $u \in H^{m+2}(\Omega)$ and
$\|u\|_{H^{m+2}} \le C \|f\|_{H^m}$; in particular $u \in C^2(\overline\Omega)$ for $m > N/2$, and
$u \in C^\infty(\overline\Omega)$ when $\Omega$ is of class $C^\infty$ and
$f \in C^\infty(\overline\Omega)$. Theorem 9.26 states the same conclusions for the Neumann problem
(49). Lemmas 9.6–9.8 are steps of the proof of Theorem 9.25, and Remark 25 gives interior regularity
and hypoellipticity. An open set of class $C^m$ is `Brezis.Chapter09.IsOfClassC` of Section 9.2.

The proofs specialize the backbone module `Numlib.Analysis.PDE.Elliptic.Regularity`, which follows
the proof of the source case by case with the method of translations: case A,
$\Omega = \mathbb{R}^N$; case B, $\Omega = \mathbb{R}^N_+$; case C₁, the interior estimates; case
C₂, the estimates near the boundary through the charts. The boundary condition of Theorem 9.26 uses
the traces on a bounded $C^1$ domain of `Numlib.Analysis.Sobolev.Boundary.ContDiffDomain`.

## Main results

* Theorem 9.25, `Brezis.Chapter09.theorem_9_25` (regularity for the Dirichlet problem): for $\Omega$
  of class $C^2$ with $\Gamma$ bounded, $u \in H^2(\Omega)$ and $\|u\|_{H^2} \le C \|f\|_{L^2}$.
* Theorem 9.25, the half space, `Brezis.Chapter09.theorem_9_25_upperHalfSpace`: the same for
  $\Omega = \mathbb{R}^N_+$.
* Theorem 9.25, the $H^{m+2}$ clause, `Brezis.Chapter09.theorem_9_25_higher`: for $\Omega$ of class
  $C^{m+2}$ and $f \in H^m(\Omega)$, $u \in H^{m+2}(\Omega)$ and
  $\|u\|_{H^{m+2}} \le C \|f\|_{H^m}$.
* Theorem 9.25, the $C^2(\overline\Omega)$ clause, `Brezis.Chapter09.theorem_9_25_contDiffOn`: if
  moreover $m > N/2$, then $u \in C^2(\overline\Omega)$.
* Theorem 9.25, the $C^\infty(\overline\Omega)$ clause, `Brezis.Chapter09.theorem_9_25_smooth` and
  `Brezis.Chapter09.theorem_9_25_smooth_of_forall_mem`: for $\Omega$ of class $C^\infty$,
  $u \in C^\infty(\overline\Omega)$ if $\Omega$ is bounded and $f \in C^\infty(\overline\Omega)$, or
  if $\Gamma$ is bounded and $f \in H^m(\Omega)$ for every $m$.
* Theorem 9.26, the half space, `Brezis.Chapter09.theorem_9_26_upperHalfSpace` (regularity for the
  Neumann problem): on $\mathbb{R}^N_+$, $u \in H^2$ and $\|u\|_{H^2} \le C \|f\|_{L^2}$.
* Theorem 9.26, the half space at higher order,
  `Brezis.Chapter09.theorem_9_26_upperHalfSpace_higher`: on $\mathbb{R}^N_+$, $f \in H^m$ gives
  $u \in H^{m+2}$.
* Theorem 9.26, the boundary condition, `Brezis.Chapter09.theorem_9_26_normalDeriv`: on a bounded
  $C^1$ domain, an $H^2$ weak solution of the Neumann problem has $\partial u / \partial n = 0$ on
  $\Gamma$ in the sense of traces.
* Lemma 9.6, `Brezis.Chapter09.lemma_9_6`: on $\mathbb{R}^N_+$,
  $\|D_h v\|_{L^2} \le \|\nabla v\|_{L^2}$ for $v \in H^1$ and $h$ parallel to $\Gamma$.
* Lemma 9.7, `Brezis.Chapter09.lemma_9_7`: on $\mathbb{R}^N_+$, the tangential derivatives of an
  $H^2$ weak solution are weak solutions with the differentiated datum.
* Lemma 9.8, `Brezis.Chapter09.lemma_9_8`: a weak solution of $-\Delta v = g$ on $\Omega \cap U$,
  transported by a $C^2$ chart, is a weak solution on $Q_+$ of an elliptic equation with $C^1$
  coefficients.
* Remark 25, interior regularity, `Brezis.Chapter09.remark_9_25` and
  `Brezis.Chapter09.remark_9_25_smooth`: on any open set, $f \in H^m(\Omega)$ gives
  $u \in H^{m+2}_{\mathrm{loc}}(\Omega)$, and $f \in C^\infty(\Omega)$ gives
  $u \in C^\infty(\Omega)$.
* Remark 25, hypoellipticity, `Brezis.Chapter09.remark_9_25_local`: the regularity of $u$ on an open
  $\omega \subseteq \Omega$ depends only on the regularity of $f$ on $\omega$.

## Conventions

* $H^m(\Omega)$ is `Brezis.Chapter09.sobolevSpaceHigher N m 2 Ω`, and $H^1(\Omega)$ and
  $H_0^1(\Omega)$ are `Brezis.Chapter09.hSpace N Ω` and `Brezis.Chapter09.hZeroSpace N Ω` (Sections
  9.1 and 9.4). For $u \in H^1(\Omega)$, "$u \in H^m(\Omega)$" means that some element of
  $H^m(\Omega)$ has the same function as $u$, and $\|u\|_{H^m}$ is the Hilbert norm of that element
  (`Brezis.Chapter09.hSpaceHigher`). The weak equation (48) is
  `Brezis.Chapter09.IsWeakSolutionDirichlet` and (49) is `Brezis.Chapter09.IsWeakSolutionNeumann` of
  Section 9.5.
* The class $C^k(\overline\Omega)$ of footnote 16 of Section 9.3 is `ContDiffOnClosure ℝ k · Ω`
  together with the continuity of the function itself on $\overline\Omega$, as in Section 9.5. The
  conclusions of Theorem 9.25 are stated in this sense.
* "$\Omega$ is of class $C^m$" is `Brezis.Chapter09.IsOfClassC m Ω`, the chart condition
  `IsContDiffChartDomain`.
  "$\Gamma$ is bounded" is `Bornology.IsBounded (frontier Ω)`. The half space $\mathbb{R}^N_+$ is
  `EuclideanSpace.upperHalfSpaceOpens d` with $N = d + 1$, and "$h$ is
  parallel to $\Gamma$" is $h_N = 0$.
* Lemma 9.8 takes the chart $H : Q \to U$ as a `ContDiffChart 2 Ω`, and the open sets
  $\Omega \cap U$ and $Q_+$ as `Opens` variables with the given carriers. Its coefficients
  $a_{k\ell}$ are the backbone's `Elliptic.chartCoeff H J`, and its datum $\tilde g$ is
  `Elliptic.chartDatum H g`.

## Implementation notes

* Remark 25 is stated with the global hypotheses $u \in H^1(\Omega)$ and $f \in H^m(\Omega)$ of the
  source. The backbone's `Elliptic.regularity_interior_higher` needs only the local ones.
* The $C^\infty(\overline\Omega)$ clause of Theorem 9.25 has two forms. For a bounded $\Omega$,
  $f \in C^\infty(\overline\Omega)$ gives $f \in H^m(\Omega)$ for every $m$
  (`Brezis.Chapter09.theorem_9_25_smooth`). For $\Gamma$ bounded only, the hypothesis is
  $f \in H^m(\Omega)$ for every $m$ (`Brezis.Chapter09.theorem_9_25_smooth_of_forall_mem`).
* `Brezis.Chapter09.IsOfClassC.isContDiffChartDomain_add_two` converts the order $m + 2$ of
  `Brezis.Chapter09.IsOfClassC` to the chart condition of the backbone.

## Deviations from the source

* **Theorem 9.25, the $C^\infty(\overline\Omega)$ clause with $\Gamma$ bounded** (reading). On an
  unbounded $\Omega$, $f \in C^\infty(\overline\Omega)$ does not give $f \in H^m(\Omega)$, which the
  proof of the source uses. The hypothesis is $f \in H^m(\Omega)$ for every $m$. See
  `Brezis.Chapter09.theorem_9_25_smooth_of_forall_mem`.
* **Remark 25, hypoellipticity** (generalization). The source takes $\omega \subset\subset \Omega$.
  The statement holds for every open $\omega \subseteq \Omega$. See
  `Brezis.Chapter09.remark_9_25_local`.

* **Lemmas 9.6–9.8** (generalization, reading and typo). The difference quotient includes zero
  displacement, the differentiated equation assumes $f \in H^1$, and the transformed
  coefficients are $C^1$ on $Q$. The source omits a minus sign in the proof of Lemma 9.7.
  See `Brezis.Chapter09.lemma_9_6`, `Brezis.Chapter09.lemma_9_7` and
  `Brezis.Chapter09.lemma_9_8`.
* **Theorem 9.26** (reading). The higher-order half-space statement gives Sobolev
  membership, while the normal derivative statement assumes $H^2$ and gives the trace identity.
  See `Brezis.Chapter09.theorem_9_26_upperHalfSpace_higher` and
  `Brezis.Chapter09.theorem_9_26_normalDeriv`.

## Not formalized

* **Theorem 9.25, higher-order estimates on the half space.** The backbone proves these as
  `Elliptic.regularity_upperHalfSpace_higher`.

* **Theorem 9.26 on a general domain.** The conclusions of Theorem 9.25 for the Neumann problem (49)
  on $\Omega$ of class $C^2$ with $\Gamma$ bounded. The source says only that "the proof of Theorem
  9.26 is entirely analogous", and the analogy fails in case C₂: a Neumann solution cut off by a
  partition function $\theta_i$ does not solve a homogeneous Neumann problem on $\Omega \cap U_i$,
  but the inhomogeneous condition $\partial(\theta_i u)/\partial n = (\partial \theta_i / \partial
  n) u$ on $\Gamma \cap U_i$. For example, on $\Omega = (0, \infty)$ with
  $\theta \in C_c^\infty(-1, 1)$, $\theta(0) = 1$ and $\theta'(0) = a \neq 0$, a Neumann solution
  has $u'(0) = 0$, so $(\theta u)'(0) = a u(0) \neq 0$ in general. A correct proof cuts off the test
  function instead, by the method of translations with $\psi = D_{-h}(\zeta^2 D_h w)$ (a Caccioppoli
  estimate), which the backbone does not have; the module doc comment of
  `Numlib.Analysis.PDE.Elliptic.Regularity` gives the details.
* **Theorem 9.26 on the half space, the norm bound of the $H^{m+2}$ clause.** The closed-graph
  argument of `Brezis.Chapter09.theorem_9_25_higher` needs a solution map for the Neumann problem,
  and the backbone's `Elliptic.solutionMap` is built only for the test space $H_0^1(\Omega)$.
* **Remark 24, the Dirichlet half.** The conclusions of Theorem 9.25 for the Dirichlet problem (50)
  of a general second-order elliptic operator: if $a_{ij} \in C^1(\overline\Omega)$ are elliptic,
  $a_i \in C(\overline\Omega)$ and $a_0 \in L^\infty(\Omega)$, with bounded derivatives of the
  coefficients when $\Omega$ is unbounded (footnote 26), and $f \in L^2(\Omega)$, then
  $u \in H^2(\Omega)$; and for $m \ge 1$, $f \in H^m(\Omega)$, $a_{ij} \in C^{m+1}(\overline\Omega)$
  and $a_i \in C^m(\overline\Omega)$ give $u \in H^{m+2}(\Omega)$. The source gives no proof. A
  proof exists along case C₂ of Theorem 9.25, which is already the estimate for variable
  coefficients, with the lower-order terms moved to the right-hand side; the module doc comment of
  `Numlib.Analysis.PDE.Elliptic.Regularity` describes it.
* **Remark 24, the Neumann half.** The same conclusions for the Neumann problem of the general
  operator, together with the conormal boundary condition $\sum_{i,j} a_{ij} \nu_j \gamma(\partial_i
  u) = 0$ $\sigma$-almost everywhere on $\Gamma$. This needs the $H^2$ regularity of the Neumann
  problem for an operator with variable coefficients, and so the Caccioppoli estimate that is
  missing above. The boundary condition alone, with $H^2$ as a hypothesis as in
  `Brezis.Chapter09.theorem_9_26_normalDeriv`, needs an $H^2$ Green formula for the conormal
  derivative: the analogue of `BoundaryData.TraceFamily.green_laplacian` for `Elliptic.generalForm`,
  from `BoundaryData.TraceFamily.green` applied to the products
  $a_{ij} \partial_i u \in H^1(\Omega)$, which needs $a_{ij} \in C^1(\overline\Omega)$ and the
  product rule in $H^1$. Neither is in the backbone.
* **Remark 25, footnotes 33 and 34.** Footnote 33 (nothing can be said about $u$ up to the boundary)
  and footnote 34 (a pointer to the strong maximum principle) are comments without a precise
  statement.
-/

open Filter MeasureTheory Metric Set Topology TopologicalSpace Laplacian
open scoped ContDiff Distributions ENNReal NNReal

namespace Brezis.Chapter09

section Interior

variable {N : ℕ}

/-- The space $\mathbb{R}^N$ of the source, `EuclideanSpace ℝ (Fin N)`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-- The standard basis of $\mathbb{R}^N$, which indexes the weak derivatives of the backbone's
multi-index Sobolev spaces. -/
local notation "𝔟" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin N) ℝ)

variable {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-! ### Remark 25: interior regularity -/

/-- **Remark 25** of [brezis2011functional], interior regularity. Let $\Omega \subset \mathbb{R}^N$
be an arbitrary open set, let $m \ge 0$, let $f \in H^m(\Omega)$, and let $u \in H^1(\Omega)$
satisfy
$$\int_\Omega \nabla u \cdot \nabla \varphi = \int_\Omega f \varphi \quad \text{for all }
  \varphi \in C_c^\infty(\Omega).$$
Then $u \in H^{m+2}_{\mathrm{loc}}(\Omega)$, and $\theta u \in H^{m+2}(\Omega)$ for every
$\theta \in C_c^\infty(\Omega)$.

The source defines $u \in H^{m+2}_{\mathrm{loc}}(\Omega)$ by the second property. The first
conclusion is the backbone's `MemSobolevMultiIndexLoc`, membership in $H^{m+2}(\omega)$ for
every $\omega \subset\subset \Omega$. The test functions $C_c^\infty(\Omega)$ are `𝓓(Ω, ℝ)`. The
proof "proceeds as in case C₁ and argues by induction on $m$"
(`Elliptic.regularity_interior_higher`, which assumes only $u \in H^1_{\mathrm{loc}}(\Omega)$
and $f \in H^m_{\mathrm{loc}}(\Omega)$). The second property is
`MemSobolevMultiIndexLoc.smul_testFunction`, restricted from $\mathbb{R}^N$ to $\Omega$. -/
theorem remark_9_25 (m : ℕ) (u : hSpace N Ω) (f : sobolevSpaceHigher N m 2 Ω)
    (heq : ∀ φ : 𝓓(Ω, ℝ), ∫ x in (Ω : Set 𝔼),
      ∑ i, partialDeriv u i x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn f x * φ x) :
    MemSobolevMultiIndexLoc 𝔟 (SobolevMultiIndex.fn u) (m + 2) 2 Ω volume ∧
    ∀ θ : 𝓓(Ω, ℝ), ∃ v : sobolevSpaceHigher N (m + 2) 2 Ω,
      SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)]
        fun x ↦ θ x * SobolevMultiIndex.fn u x := by
  have hloc := Elliptic.regularity_interior_higher m
    (SobolevMultiIndex.memSobolevMultiIndex u).memSobolevMultiIndexLoc
    (fun i ↦ Elliptic.weakDeriv_hasWeakIteratedLineDerivOn_single u i)
    (SobolevMultiIndex.memSobolevMultiIndex f).memSobolevMultiIndexLoc heq
  refine ⟨hloc, fun θ ↦ ?_⟩
  have h1 := (hloc.smul_testFunction one_le_two θ).mono_set (le_top : Ω ≤ ⊤)
  refine (h1.congr_ae ?_).exists_sobolevMultiIndex
  refine ae_restrict_of_forall_mem Ω.isOpen.measurableSet fun x hx ↦ ?_
  rw [Set.indicator_of_mem hx, smul_eq_mul]

/-- **Remark 25** of [brezis2011functional], "in particular, $f \in C^\infty(\Omega) \Rightarrow u
\in C^\infty(\Omega)$". Let $\Omega \subset \mathbb{R}^N$ be open, let
$f : \mathbb{R}^N \to \mathbb{R}$ be of class $C^\infty$ on $\Omega$, and let
$u \in H^1(\Omega)$ satisfy
$$\int_\Omega \nabla u \cdot \nabla \varphi = \int_\Omega f \varphi \quad \text{for all }
  \varphi \in C_c^\infty(\Omega).$$
Then $u$ equals almost everywhere on $\Omega$ a function of class $C^\infty$ on $\Omega$.

A $C^\infty$ function lies in $H^m_{\mathrm{loc}}(\Omega)$ for every $m$
(`ContDiffOn.memSobolevMultiIndexLoc`). So $u \in H^{m+2}_{\mathrm{loc}}(\Omega)$ for every $m$
by `Elliptic.regularity_interior_higher`, and `MemSobolevMultiIndexLoc.exists_contDiffOn` gives
the smooth representative. -/
theorem remark_9_25_smooth (u : hSpace N Ω) {f : 𝔼 → ℝ} (hf : ContDiffOn ℝ ∞ f Ω)
    (heq : ∀ φ : 𝓓(Ω, ℝ), ∫ x in (Ω : Set 𝔼),
      ∑ i, partialDeriv u i x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = ∫ x in (Ω : Set 𝔼), f x * φ x) :
    ∃ ũ : 𝔼 → ℝ, ContDiffOn ℝ ∞ ũ Ω ∧
      SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ :=
  MemSobolevMultiIndexLoc.exists_contDiffOn fun m ↦
    (Elliptic.regularity_interior_higher m
      (SobolevMultiIndex.memSobolevMultiIndex u).memSobolevMultiIndexLoc
      (fun i ↦ Elliptic.weakDeriv_hasWeakIteratedLineDerivOn_single u i)
      (hf.memSobolevMultiIndexLoc (by simp)) heq).mono_order (Nat.le_add_right m 2)

/-- **Remark 25** of [brezis2011functional], hypoellipticity. Let $\Omega \subset \mathbb{R}^N$ be
open, let $f \in L^2(\Omega)$, let $u \in H_0^1(\Omega)$ be the weak solution of (48), and let
$\omega \subseteq \Omega$ be open. Then the regularity of $u$ on $\omega$ depends only on the
regularity of $f$ on $\omega$:
* for every $m \ge 0$, if $f \in H^m(\omega)$, then $u \in H^{m+2}_{\mathrm{loc}}(\omega)$;
* if $f$ equals almost everywhere on $\omega$ a function of class $C^\infty$ on $\omega$, then
  so does $u$.

In particular $f \in C^\infty(\omega) \Rightarrow u \in C^\infty(\omega)$, even if $f$ is very
irregular outside $\omega$.

**Generalization.** The source takes $\omega \subset\subset \Omega$. The statement holds for
every open $\omega \subseteq \Omega$.

The proof applies interior regularity on $\omega$ to the datum $f - u$, whose regularity on
$\omega$ is that of $f$ one step behind, and iterates
(`Elliptic.memSobolevMultiIndexLoc_of_forall_testFunction_add_mul`). The open set $\omega$ is
`Ω'`. The sentence before the remark, that $u|_\omega$ depends on the values of $f$ in all of
$\Omega$, refers through footnote 34 to the strong maximum principle and is not formalized. -/
theorem remark_9_25_local {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))} {u : hSpace N Ω}
    (hu : IsWeakSolutionDirichlet Ω f u) {Ω' : Opens 𝔼} (hω : Ω' ≤ Ω) :
    (∀ m : ℕ, MemSobolevMultiIndex 𝔟 (⇑f) m 2 Ω' volume →
      MemSobolevMultiIndexLoc 𝔟 (SobolevMultiIndex.fn u) (m + 2) 2 Ω' volume) ∧
    ∀ f₀ : 𝔼 → ℝ, ContDiffOn ℝ ∞ f₀ Ω' → (f : 𝔼 → ℝ) =ᵐ[volume.restrict (Ω' : Set 𝔼)] f₀ →
      ∃ ũ : 𝔼 → ℝ, ContDiffOn ℝ ∞ ũ Ω' ∧
        SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω' : Set 𝔼)] ũ := by
  have hu' := (isWeakSolutionDirichlet_iff f u).1 hu
  have hg := Elliptic.dirichletForm_eq_load_sub_of_isGalerkinSolution_laplace hu'
  have hpred := Elliptic.forall_testFunction_of_forall_testFunctions
    (fun Φ hΦ ↦ hg Φ (SobolevMultiIndexZero.testFunctions_le hΦ))
  have hsub : ⇑(f - SobolevMultiIndex.weakDeriv u 0) =ᵐ[volume.restrict (Ω : Set 𝔼)]
      fun x ↦ f x + (-1) * SobolevMultiIndex.fn u x := by
    filter_upwards [Lp.coeFn_sub f (SobolevMultiIndex.weakDeriv u 0)] with x hx
    rw [hx, Pi.sub_apply]
    change f x - SobolevMultiIndex.weakDeriv u 0 x = f x + -1 * SobolevMultiIndex.weakDeriv u 0 x
    ring
  have hpred' : ∀ φ : 𝓓(Ω, ℝ), ∫ x in (Ω : Set 𝔼),
      ∑ i, partialDeriv u i x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = ∫ x in (Ω : Set 𝔼), (f x + (-1) * SobolevMultiIndex.fn u x) * φ x := fun φ ↦ by
    have hint : ∀ i, Integrable
        (fun x ↦ partialDeriv u i x * fderiv ℝ φ x (EuclideanSpace.single i 1))
        (volume.restrict (Ω : Set 𝔼)) := fun i ↦
      (Lp.memLp _).integrable_mul_two
        ((TestFunction.memLp (φ.fderivApply (EuclideanSpace.single i 1)) 2 volume).restrict _)
    rw [integral_finsetSum _ fun i _ ↦ hint i]
    refine (hpred φ).trans (integral_congr_ae ?_)
    filter_upwards [hsub] with x hx
    rw [hx]
  have hpredω := Elliptic.forall_testFunction_of_le hω hpred'
  have huω : MemSobolevMultiIndexLoc 𝔟 (SobolevMultiIndex.fn u) 1 2 Ω' volume :=
    ((SobolevMultiIndex.memSobolevMultiIndex u).mono_set hω).memSobolevMultiIndexLoc
  have hwω : ∀ i, HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1] (SobolevMultiIndex.fn u)
      (partialDeriv u i) Ω' volume := fun i ↦
    (Elliptic.weakDeriv_hasWeakIteratedLineDerivOn_single u i).mono hω
  refine ⟨fun m hf ↦ Elliptic.memSobolevMultiIndexLoc_of_forall_testFunction_add_mul m huω hwω
    hf.memSobolevMultiIndexLoc hpredω, fun f₀ hf₀ hff ↦ ?_⟩
  refine MemSobolevMultiIndexLoc.exists_contDiffOn fun m ↦ ?_
  have hfm : MemSobolevMultiIndexLoc 𝔟 (⇑f) m 2 Ω' volume :=
    (hf₀.memSobolevMultiIndexLoc (by simp)).congr_ae hff.symm
  exact (Elliptic.memSobolevMultiIndexLoc_of_forall_testFunction_add_mul m huω hwω hfm
    hpredω).mono_order (Nat.le_add_right m 2)

end Interior

section Regularity

variable {d : ℕ}

/-- The space $\mathbb{R}^N$ of the source with $N = d + 1$, `EuclideanSpace ℝ (Fin (d + 1))`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

/-- The standard basis of $\mathbb{R}^N$, which indexes the weak derivatives of the backbone's
multi-index Sobolev spaces. -/
local notation "𝔟" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin (d + 1)) ℝ)

/-- The half space $\mathbb{R}^N_+ = \{x \in \mathbb{R}^N : x_N > 0\}$, as an open set. -/
local notation "ℝ₊" => EuclideanSpace.upperHalfSpaceOpens d

variable {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- Let $m \ge 0$ and let $\Omega \subset \mathbb{R}^N$ be an open set of class $C^{m+2}$. Then
$\Omega$ satisfies the backbone's chart condition `IsContDiffChartDomain` at the order $m + 2$.

The order is a natural number cast to `ℕ∞` in `Brezis.Chapter09.IsOfClassC` and to `WithTop ℕ∞`
in `IsContDiffChartDomain`; the lemma converts between the two casts. -/
theorem IsOfClassC.isContDiffChartDomain_add_two {m : ℕ} (hΩ : IsOfClassC (m + 2) (Ω : Set 𝔼)) :
    IsContDiffChartDomain (m + 2) (Ω : Set 𝔼) := by
  have : (((m + 2 : ℕ∞)) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 2 := by push_cast; rfl
  rw [IsOfClassC, this] at hΩ
  exact hΩ

/-! ### Theorem 9.25 -/

/-- **Theorem 9.25** of [brezis2011functional] (regularity for the Dirichlet problem), the $H^2$
clause. Let $N \ge 1$ and let $\Omega \subset \mathbb{R}^N$ be an open set of class $C^2$ with
$\Gamma$ bounded. There is a constant $C \ge 0$, depending only on $\Omega$, with the following
property. Let $f \in L^2(\Omega)$ and let $u \in H_0^1(\Omega)$ satisfy (48). Then
$u \in H^2(\Omega)$ and
$$\|u\|_{H^2} \le C \|f\|_{L^2}.$$

Precisely, the function of $u$ is the function of some $U \in H^2(\Omega)$, and every such $U$
has $\|U\|_{H^2} \le C \|f\|_{L^2}$. The alternative "or else $\Omega = \mathbb{R}^N_+$" is
`Brezis.Chapter09.theorem_9_25_upperHalfSpace`. The proof is the backbone's
`Elliptic.regularity_dirichlet`: the method of translations in the cases A, B, C₁ and C₂, with
the constant from the closed graph theorem. -/
theorem theorem_9_25 (hΩ : IsOfClassC 2 (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) (u : hSpace (d + 1) Ω),
      IsWeakSolutionDirichlet Ω f u →
        (∃ U : sobolevSpaceHigher (d + 1) 2 2 Ω,
          SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set 𝔼)] SobolevMultiIndex.fn u) ∧
        ∀ U : sobolevSpaceHigher (d + 1) 2 2 Ω,
          SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set 𝔼)] SobolevMultiIndex.fn u →
            ‖U‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC0, hC⟩ := Elliptic.regularity_dirichlet hΩ hΓ
  refine ⟨C, hC0, fun f u hu ↦ ?_⟩
  obtain ⟨hmem, hbound⟩ := hC f u ((isWeakSolutionDirichlet_iff f u).1 hu)
  exact ⟨hmem.exists_sobolevMultiIndex, hbound⟩

/-- **Theorem 9.25** of [brezis2011functional], the alternative "or else $\Omega = \mathbb{R}^N_+$",
$H^2$ clause. Let $N \ge 1$. There is a constant $C \ge 0$ such that for every
$f \in L^2(\mathbb{R}^N_+)$, the weak solution $u \in H_0^1(\mathbb{R}^N_+)$ of (48) satisfies
$u \in H^2(\mathbb{R}^N_+)$ and $\|u\|_{H^2} \le C \|f\|_{L^2}$.

The conclusion is read as in `Brezis.Chapter09.theorem_9_25`. The proof is case B of the source
(`Elliptic.regularity_upperHalfSpace`) for the equation $\int \nabla u \cdot \nabla \varphi =
\int (f - u) \varphi$, with the constant $3 C_N$ that comes from $\|u\|_{H^1} \le \|f\|_{L^2}$
and $\|f - u\|_{L^2} \le 2 \|f\|_{L^2}$. -/
theorem theorem_9_25_upperHalfSpace :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Lp ℝ 2 (volume.restrict ((ℝ₊ : Opens 𝔼) : Set 𝔼)))
      (u : hSpace (d + 1) ℝ₊), IsWeakSolutionDirichlet ℝ₊ f u →
        (∃ U : sobolevSpaceHigher (d + 1) 2 2 ℝ₊, SobolevMultiIndex.fn U
          =ᵐ[volume.restrict ((ℝ₊ : Opens 𝔼) : Set 𝔼)] SobolevMultiIndex.fn u) ∧
        ∀ U : sobolevSpaceHigher (d + 1) 2 2 ℝ₊, SobolevMultiIndex.fn U
          =ᵐ[volume.restrict ((ℝ₊ : Opens 𝔼) : Set 𝔼)] SobolevMultiIndex.fn u →
            ‖U‖ ≤ C * ‖f‖ := by
  have hC0 : (0 : ℝ) ≤ Elliptic.regularityConst d 1 1 0 := by
    unfold Elliptic.regularityConst
    positivity
  refine ⟨3 * Elliptic.regularityConst d 1 1 0, by linarith, fun f u hu ↦ ?_⟩
  have hu' := (isWeakSolutionDirichlet_iff f u).1 hu
  have hg := Elliptic.dirichletForm_eq_load_sub_of_isGalerkinSolution_laplace hu'
  obtain ⟨U, hU, hUn⟩ := Elliptic.regularity_upperHalfSpace ⟨hu'.1, hg⟩
  have hun : ‖u‖ ≤ ‖f‖ := Elliptic.norm_le_of_isGalerkinSolution_laplace _ hu'
  have hg' : ‖f - SobolevMultiIndex.weakDeriv u 0‖ ≤ 2 * ‖f‖ := by
    calc ‖f - SobolevMultiIndex.weakDeriv u 0‖ ≤ ‖f‖ + ‖SobolevMultiIndex.weakDeriv u 0‖ :=
          norm_sub_le _ _
      _ ≤ ‖f‖ + ‖u‖ := by gcongr; exact SobolevMultiIndex.norm_weakDeriv_le u 0
      _ ≤ 2 * ‖f‖ := by linarith
  refine ⟨⟨U, hU⟩, fun U' hU' ↦ ?_⟩
  rw [SobolevMultiIndex.ext_of_fn_ae_eq (hU'.trans hU.symm)]
  calc ‖U‖ ≤ Elliptic.regularityConst d 1 1 0 * (‖u‖ + ‖f - SobolevMultiIndex.weakDeriv u 0‖) :=
        hUn
    _ ≤ Elliptic.regularityConst d 1 1 0 * (‖f‖ + 2 * ‖f‖) := by gcongr
    _ = 3 * Elliptic.regularityConst d 1 1 0 * ‖f‖ := by ring

/-- **Theorem 9.25** of [brezis2011functional], the $H^{m+2}$ clause. Let $N \ge 1$, let $m \ge 0$,
and let $\Omega \subset \mathbb{R}^N$ be an open set of class $C^{m+2}$ with $\Gamma$ bounded.
There is a constant $C \ge 0$, depending only on $\Omega$ and $m$, with the following property.
Let $f \in H^m(\Omega)$ and let $u \in H_0^1(\Omega)$ satisfy (48). Then $u \in H^{m+2}(\Omega)$
and
$$\|u\|_{H^{m+2}} \le C \|f\|_{H^m}.$$

Precisely, the function of $u$ is the function of some $U \in H^{m+2}(\Omega)$, and every such
$U$ has $\|U\|_{H^{m+2}} \le C \|f\|_{H^m}$. The datum of (48) is the function of $f$ as an
element of $L^2(\Omega)$, `SobolevMultiIndex.fnL ℝ 𝔟 m 2 Ω volume f`. The proof is the
backbone's `Elliptic.regularity_dirichlet_higher`: induction on $m$ in the cases A, B and C,
which differentiates the equation (Lemma 9.7 and (58)) instead of using the Leibniz rule of
order $m$ as the source does, with the constant from the closed graph theorem.

**Reading.** This clause uses the bounded-frontier hypothesis. The half-space higher-order
 result is available in the backbone as `Elliptic.regularity_upperHalfSpace_higher`. -/
theorem theorem_9_25_higher (m : ℕ) (hΩ : IsOfClassC (m + 2) (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : sobolevSpaceHigher (d + 1) m 2 Ω) (u : hSpace (d + 1) Ω),
      IsWeakSolutionDirichlet Ω (SobolevMultiIndex.fnL ℝ 𝔟 m 2 Ω volume f) u →
        (∃ U : sobolevSpaceHigher (d + 1) (m + 2) 2 Ω,
          SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set 𝔼)] SobolevMultiIndex.fn u) ∧
        ∀ U : sobolevSpaceHigher (d + 1) (m + 2) 2 Ω,
          SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set 𝔼)] SobolevMultiIndex.fn u →
            ‖U‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC0, hC⟩ :=
    Elliptic.regularity_dirichlet_higher m hΩ.isContDiffChartDomain_add_two hΓ
  refine ⟨C, hC0, fun f u hu ↦ ?_⟩
  obtain ⟨hmem, hbound⟩ := hC f u ((isWeakSolutionDirichlet_iff _ u).1 hu)
  exact ⟨hmem.exists_sobolevMultiIndex, hbound⟩

/-- **Theorem 9.25** of [brezis2011functional], "in particular, if $f \in H^m(\Omega)$ with
$m > N/2$, then $u \in C^2(\overline\Omega)$". Let $N \ge 1$, let $m \ge 0$ with $m > N/2$, and
let $\Omega \subset \mathbb{R}^N$ be an open set of class $C^{m+2}$ with $\Gamma$ bounded. Let
$f \in H^m(\Omega)$ and let $u \in H_0^1(\Omega)$ satisfy (48). Then $u$ equals almost
everywhere on $\Omega$ a function $\tilde u \in C^2(\overline\Omega)$.

Here $\tilde u \in C^2(\overline\Omega)$ has the meaning of footnote 16 of Section 9.3:
`ContDiffOnClosure ℝ 2 ũ Ω`, and $\tilde u$ is continuous on $\overline\Omega$. The proof
combines the $H^{m+2}$ clause with Corollary 9.15 (`Elliptic.regularity_dirichlet_contDiffOn`,
whose representative is continuous on $\mathbb{R}^N$, with derivatives of order at most $2$ that
extend continuously from $\Omega$ to $\mathbb{R}^N$). The condition $m > N/2$ is the condition
$2 + N/2 < m + 2$ of Corollary 9.15.

**Reading.** This closure-regularity clause is stated under the bounded-frontier hypothesis. -/
theorem theorem_9_25_contDiffOn (m : ℕ) (hΩ : IsOfClassC (m + 2) (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) (hm : ((d + 1 : ℕ) : ℝ) / 2 < m)
    (f : sobolevSpaceHigher (d + 1) m 2 Ω) {u : hSpace (d + 1) Ω}
    (hu : IsWeakSolutionDirichlet Ω (SobolevMultiIndex.fnL ℝ 𝔟 m 2 Ω volume f) u) :
    ∃ ũ : 𝔼 → ℝ, ContDiffOnClosure ℝ 2 ũ Ω ∧ ContinuousOn ũ (closure (Ω : Set 𝔼)) ∧
      SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ := by
  obtain ⟨ũ, hc, h2, hae, hG⟩ := Elliptic.regularity_dirichlet_contDiffOn m
    hΩ.isContDiffChartDomain_add_two hΓ hm (SobolevMultiIndex.memSobolevMultiIndex f)
    ((isWeakSolutionDirichlet_iff _ u).1 hu)
  refine ⟨ũ, ⟨h2, fun j hj ↦ ?_⟩, hc.continuousOn, hae⟩
  obtain ⟨G, hGc, hGe⟩ := hG j (by exact_mod_cast hj)
  exact ⟨G, hGc.continuousOn, hGe.symm⟩

/-- **Theorem 9.25** of [brezis2011functional], "finally, if $\Omega$ is of class $C^\infty$ and
$f \in C^\infty(\overline\Omega)$, then $u \in C^\infty(\overline\Omega)$", for a bounded
$\Omega$. Let $N \ge 1$ and let $\Omega \subset \mathbb{R}^N$ be a bounded open set of class
$C^\infty$. Let $f \in L^2(\Omega)$ equal almost everywhere on $\Omega$ a function
$f_0 \in C^\infty(\overline\Omega)$, and let $u \in H_0^1(\Omega)$ satisfy (48). Then $u$ equals
almost everywhere on $\Omega$ a function $\tilde u \in C^\infty(\overline\Omega)$ that is
continuous on $\overline\Omega$.

"Of class $C^\infty$" is `Brezis.Chapter09.IsOfClassC ⊤ Ω`, a $C^\infty$ chart at every boundary
point, and $f_0 \in C^\infty(\overline\Omega)$ is `ContDiffOnClosure ℝ ∞ f₀ Ω`. On a bounded
$\Omega$, $f \in C^\infty(\overline\Omega)$ gives $f \in H^m(\Omega)$ for every $m$
(`ContDiffOnClosure.memSobolevMultiIndex_of_isBounded_of_le`). The backbone's
`Elliptic.regularity_dirichlet_smooth` is the $C^2(\overline\Omega)$ clause at every order, with
one representative for all orders. For an unbounded $\Omega$ with bounded $\Gamma$, see
`Brezis.Chapter09.theorem_9_25_smooth_of_forall_mem`.

**Reading.** The domain is bounded here. This makes the smooth datum belong to every $H^m$.
 For the bounded-frontier version this membership is assumed in
 `Brezis.Chapter09.theorem_9_25_smooth_of_forall_mem`. -/
theorem theorem_9_25_smooth (hΩ : IsOfClassC ⊤ (Ω : Set 𝔼)) (hb : Bornology.IsBounded (Ω : Set 𝔼))
    {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))} {f₀ : 𝔼 → ℝ} (hf : ContDiffOnClosure ℝ ∞ f₀ Ω)
    (hff : (f : 𝔼 → ℝ) =ᵐ[volume.restrict (Ω : Set 𝔼)] f₀) {u : hSpace (d + 1) Ω}
    (hu : IsWeakSolutionDirichlet Ω f u) :
    ∃ ũ : 𝔼 → ℝ, ContDiffOnClosure ℝ ∞ ũ Ω ∧ ContinuousOn ũ (closure (Ω : Set 𝔼)) ∧
      SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ := by
  have hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼)) :=
    hb.isCompact_closure.isBounded.subset frontier_subset_closure
  have hfm : ∀ m : ℕ, MemSobolevMultiIndex 𝔟 (⇑f) m 2 Ω volume := fun m ↦
    (hf.memSobolevMultiIndex_of_isBounded_of_le Ω hb 2 (by simp)).congr_ae hff.symm
  obtain ⟨ũ, hc, h2, hae, hG⟩ := Elliptic.regularity_dirichlet_smooth hΩ hΓ hfm
    ((isWeakSolutionDirichlet_iff _ u).1 hu)
  refine ⟨ũ, ⟨h2, fun j _ ↦ ?_⟩, hc.continuousOn, hae⟩
  obtain ⟨G, hGc, hGe⟩ := hG j
  exact ⟨G, hGc.continuousOn, hGe.symm⟩

/-- **Theorem 9.25** of [brezis2011functional], the $C^\infty(\overline\Omega)$ clause for $\Omega$
of class $C^\infty$ with $\Gamma$ bounded. Let $N \ge 1$ and let $\Omega \subset \mathbb{R}^N$
be an open set of class $C^\infty$ with $\Gamma$ bounded. Let $f \in L^2(\Omega)$ with
$f \in H^m(\Omega)$ for every $m \ge 0$, and let $u \in H_0^1(\Omega)$ satisfy (48). Then $u$
equals almost everywhere on $\Omega$ a function of class $C^\infty(\overline\Omega)$ that is
continuous on $\overline\Omega$.

**Reading.** The source assumes $f \in C^\infty(\overline\Omega)$. On an unbounded $\Omega$ this
does not give $f \in H^m(\Omega)$, which is what the proof of the source uses. The statement
assumes $f \in H^m(\Omega)$ for every $m$. On a bounded $\Omega$ the hypothesis of the source
suffices: see `Brezis.Chapter09.theorem_9_25_smooth`.

The proof is the backbone's `Elliptic.regularity_dirichlet_smooth`. -/
theorem theorem_9_25_smooth_of_forall_mem (hΩ : IsOfClassC ⊤ (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))}
    (hf : ∀ m : ℕ, ∃ F : sobolevSpaceHigher (d + 1) m 2 Ω,
      SobolevMultiIndex.fn F =ᵐ[volume.restrict (Ω : Set 𝔼)] f)
    {u : hSpace (d + 1) Ω} (hu : IsWeakSolutionDirichlet Ω f u) :
    ∃ ũ : 𝔼 → ℝ, ContDiffOnClosure ℝ ∞ ũ Ω ∧ ContinuousOn ũ (closure (Ω : Set 𝔼)) ∧
      SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ := by
  have hfm : ∀ m : ℕ, MemSobolevMultiIndex 𝔟 (⇑f) m 2 Ω volume := fun m ↦
    (exists_fn_ae_eq_iff (m := m) (p := 2) (f : 𝔼 → ℝ)).1 (hf m)
  obtain ⟨ũ, hc, h2, hae, hG⟩ := Elliptic.regularity_dirichlet_smooth hΩ hΓ hfm
    ((isWeakSolutionDirichlet_iff _ u).1 hu)
  refine ⟨ũ, ⟨h2, fun j _ ↦ ?_⟩, hc.continuousOn, hae⟩
  obtain ⟨G, hGc, hGe⟩ := hG j
  exact ⟨G, hGc.continuousOn, hGe.symm⟩

/-! ### The lemmas of the proof: Lemmas 9.6, 9.7 (case B) and 9.8 (case C₂) -/

/-- **Lemma 9.6** of [brezis2011functional]. Let $N \ge 1$ and $\Omega = \mathbb{R}^N_+$. For every
$v \in H^1(\Omega)$ and every $h \in \mathbb{R}^N$ parallel to $\Gamma$ (that is, $h_N = 0$),
$$\|D_h v\|_{L^2(\Omega)} \le \|\nabla v\|_{L^2(\Omega)},$$
where $D_h v(x) = (v(x + h) - v(x)) / |h|$.

The difference quotient is `Elliptic.diffQuot h v`; for $h = 0$ it is $0$. The norm
$\|\nabla v\|_{L^2}$ is the $L^2$ norm of the gradient vector `Brezis.Chapter09.gradient v`
(Section 9.1), and the indices are $0$-based, so $h_N$ is `h (Fin.last d)`. The proof in the
source starts with $v \in C_c^1(\mathbb{R}^N)$ as in Proposition 9.3 and argues by density. The
backbone's `Elliptic.eLpNorm_diffQuot_le_of_tangential` is Proposition 9.3, (i) ⇒ (iii), on the
half space, which is invariant under these translations. Its bound is the $\ell^2$ norm of the
gradient, which for $p = 2$ equals the Euclidean one
(`Brezis.Chapter09.gradNorm_eq_toReal_eLpNorm_gradient_two`).

**Generalization.** The totalized quotient also gives the inequality for $h=0$, with value zero
 on the left. -/
theorem lemma_9_6 {h : 𝔼} (hh : h (Fin.last d) = 0) (v : hSpace (d + 1) ℝ₊) :
    eLpNorm (Elliptic.diffQuot h (SobolevMultiIndex.fn v)) 2
        (volume.restrict ((ℝ₊ : Opens 𝔼) : Set 𝔼))
      ≤ eLpNorm (gradient v) 2 (volume.restrict ((ℝ₊ : Opens 𝔼) : Set 𝔼)) := by
  refine (Elliptic.eLpNorm_diffQuot_le_of_tangential hh v).trans ?_
  rw [gradNorm_eq_toReal_eLpNorm_gradient_two,
    ENNReal.ofReal_toReal (memLp_gradient v).eLpNorm_ne_top]

/-- **Lemma 9.7** of [brezis2011functional]. Let $N \ge 1$ and $\Omega = \mathbb{R}^N_+$. Let
$f \in H^1(\Omega)$, and let $u \in H^2(\Omega) \cap H_0^1(\Omega)$ satisfy (48). Then for every
tangential direction $j$, $1 \le j \le N - 1$, the derivative $Du = \partial u / \partial x_j$
belongs to $H_0^1(\Omega)$, and
$$\int_\Omega \nabla(Du) \cdot \nabla \varphi + \int_\Omega (Du) \varphi = \int_\Omega (Df)
  \varphi \quad \text{for all } \varphi \in H_0^1(\Omega). \qquad (58)$$

Precisely, there is $w \in H^1(\Omega)$ that is the weak derivative of $u$ in the direction
$e_j$, and $w$ is a weak solution of (48) with the datum $\partial f / \partial x_j$
(`Brezis.Chapter09.IsWeakSolutionDirichlet`, whose first clause is $w \in H_0^1(\Omega)$). The
indices are $0$-based, so the tangential directions are `j ≠ Fin.last d`. The membership is the
"delicate point" of the proof in the source, the backbone's
`Elliptic.tangentialDeriv_mem_zero_of_isGalerkinSolution` (weak compactness of the tangential
difference quotients in $H_0^1(\Omega)$). The identity (58) "is derived from (48) by choosing
$D\varphi$ instead of $\varphi$ (with $\varphi \in C_c^\infty(\Omega)$) and then arguing by
density" (`Elliptic.forall_testFunction_deriv` and
`Elliptic.apply_eq_zero_of_forall_testFunctions`).

**Reading.** The lemma makes $f \in H^1$ explicit, as required to use $Df$ as an $L^2$ datum
in the induction.

**Typo.** The finite-difference integration by parts in the source's proof omits a minus
sign before $\int u D_{-h}\varphi$. -/
theorem lemma_9_7 {f u : hSpace (d + 1) ℝ₊}
    (hu2 : ∃ U : sobolevSpaceHigher (d + 1) 2 2 ℝ₊,
      SobolevMultiIndex.fn U =ᵐ[volume.restrict ((ℝ₊ : Opens 𝔼) : Set 𝔼)] SobolevMultiIndex.fn u)
    (hu : IsWeakSolutionDirichlet ℝ₊ (SobolevMultiIndex.fnL ℝ 𝔟 1 2 ℝ₊ volume f) u)
    {j : Fin (d + 1)} (hj : j ≠ Fin.last d) :
    ∃ w : hSpace (d + 1) ℝ₊,
      HasWeakIteratedLineDerivOn ![EuclideanSpace.single j 1] (SobolevMultiIndex.fn u)
        (SobolevMultiIndex.fn w) ℝ₊ volume ∧
      IsWeakSolutionDirichlet ℝ₊ (partialDeriv f j) w := by
  have hΩm : MeasurableSet ((ℝ₊ : Opens 𝔼) : Set 𝔼) := (ℝ₊ : Opens 𝔼).isOpen.measurableSet
  obtain ⟨U, hU⟩ := hu2
  have hu' := (isWeakSolutionDirichlet_iff _ u).1 hu
  have hg := Elliptic.dirichletForm_eq_load_sub_of_isGalerkinSolution_laplace hu'
  obtain ⟨w, hw0, hwd⟩ := Elliptic.tangentialDeriv_mem_zero_of_isGalerkinSolution ⟨hu'.1, hg⟩ hj
  have hwfn : SobolevMultiIndex.fn w =ᵐ[volume.restrict ((ℝ₊ : Opens 𝔼) : Set 𝔼)]
      SobolevMultiIndex.weakDeriv u (MultiIndexLE.single j) :=
    (ae_restrict_iff' hΩm).2
      (hwd.ae_eq (Elliptic.weakDeriv_hasWeakIteratedLineDerivOn_single u j))
  -- the first derivatives of `u` as `H¹` elements
  have hV : ∀ k, ∃ V : hSpace (d + 1) ℝ₊, SobolevMultiIndex.fn V
      =ᵐ[volume.restrict ((ℝ₊ : Opens 𝔼) : Set 𝔼)] SobolevMultiIndex.weakDeriv u
        (MultiIndexLE.single k) := fun k ↦
    Elliptic.exists_sobolevEuclidean_one_fn_ae_eq_weakDeriv hU k
  choose V hV using hV
  -- the predicate form of the equation, with the datum `f - u`
  have hpred := Elliptic.forall_testFunction_of_forall_testFunctions
    (fun Φ hΦ ↦ hg Φ (SobolevMultiIndexZero.testFunctions_le hΦ))
  have hsub : ⇑(SobolevMultiIndex.fnL ℝ 𝔟 1 2 ℝ₊ volume f - SobolevMultiIndex.weakDeriv u 0)
      =ᵐ[volume.restrict ((ℝ₊ : Opens 𝔼) : Set 𝔼)]
        fun x ↦ SobolevMultiIndex.fn f x - SobolevMultiIndex.fn u x :=
    Lp.coeFn_sub _ _
  have hpred' : ∀ φ : 𝓓(ℝ₊, ℝ), ∑ i, ∫ x in ((ℝ₊ : Opens 𝔼) : Set 𝔼),
      SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
        * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = ∫ x in ((ℝ₊ : Opens 𝔼) : Set 𝔼),
        (SobolevMultiIndex.fn f x - SobolevMultiIndex.fn u x) * φ x := fun φ ↦ by
    rw [hpred φ]
    refine integral_congr_ae ?_
    filter_upwards [hsub] with x hx
    rw [hx]
  -- the derivatives of the datum along `e_k`
  have hgj : ∀ k, HasWeakIteratedLineDerivOn ![EuclideanSpace.single k 1]
      (fun x ↦ SobolevMultiIndex.fn f x - SobolevMultiIndex.fn u x)
      (fun x ↦ partialDeriv f k x - SobolevMultiIndex.weakDeriv u (MultiIndexLE.single k) x)
      ℝ₊ volume := fun k ↦
    (Elliptic.weakDeriv_hasWeakIteratedLineDerivOn_single f k).sub
      (Elliptic.weakDeriv_hasWeakIteratedLineDerivOn_single u k)
  -- the differentiated equation against the test functions
  have hderiv := Elliptic.forall_testFunction_deriv
    (w := fun i ↦ ⇑(SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i)))
    (v := fun i k ↦ ⇑(SobolevMultiIndex.weakDeriv (V k) (MultiIndexLE.single i)))
    (fun i ↦ Elliptic.weakDeriv_hasWeakIteratedLineDerivOn_single u i)
    (fun i k ↦ (Elliptic.weakDeriv_hasWeakIteratedLineDerivOn_single (V k) i).congr_ae (hV k)
      (EventuallyEq.refl _ _))
    hgj hpred' j
  -- `∂_i (V j) = ∂_i w` almost everywhere
  have hvw : ∀ i, ⇑(SobolevMultiIndex.weakDeriv (V j) (MultiIndexLE.single i))
      =ᵐ[volume.restrict ((ℝ₊ : Opens 𝔼) : Set 𝔼)]
        SobolevMultiIndex.weakDeriv w (MultiIndexLE.single i) := fun i ↦ by
    have h1 := (Elliptic.weakDeriv_hasWeakIteratedLineDerivOn_single (V j) i).congr_ae (hV j)
      (EventuallyEq.refl _ _)
    have h2 := (Elliptic.weakDeriv_hasWeakIteratedLineDerivOn_single w i).congr_ae hwfn
      (EventuallyEq.refl _ _)
    exact (ae_restrict_iff' hΩm).2 (h1.ae_eq h2)
  -- the typed equation for `w` on the test-function elements
  have hweq : ∀ Φ ∈ SobolevMultiIndex.testFunctions ℝ 𝔟 1 2 ℝ₊ volume,
      Elliptic.laplaceForm ℝ₊ w Φ = Elliptic.load ℝ₊ (partialDeriv f j) Φ := by
    intro Φ hΦ
    obtain ⟨ψ, hψ⟩ := hΦ
    rw [Elliptic.laplaceForm_apply_eq_dirichletForm_add_weakDeriv,
      Elliptic.dirichletForm_apply_eq_of_ae_eq (fun i ↦ EventuallyEq.refl _ _) hψ,
      Elliptic.load_apply_eq_of_ae_eq (EventuallyEq.refl _ _) hψ, L2.inner_eq_integral_mul]
    have e1 : ∑ i, ∫ x in ((ℝ₊ : Opens 𝔼) : Set 𝔼),
        SobolevMultiIndex.weakDeriv w (MultiIndexLE.single i) x
          * fderiv ℝ ψ x (EuclideanSpace.single i 1)
        = ∫ x in ((ℝ₊ : Opens 𝔼) : Set 𝔼),
          (partialDeriv f j x - SobolevMultiIndex.weakDeriv u (MultiIndexLE.single j) x) * ψ x := by
      rw [← hderiv ψ]
      refine Finset.sum_congr rfl fun i _ ↦ integral_congr_ae ?_
      filter_upwards [hvw i] with x hx
      rw [hx]
    have e2 : ∫ x in ((ℝ₊ : Opens 𝔼) : Set 𝔼),
        SobolevMultiIndex.weakDeriv w 0 x * SobolevMultiIndex.weakDeriv Φ 0 x
        = ∫ x in ((ℝ₊ : Opens 𝔼) : Set 𝔼),
          SobolevMultiIndex.weakDeriv u (MultiIndexLE.single j) x * ψ x := by
      refine integral_congr_ae ?_
      filter_upwards [hwfn, hψ] with x hx hx'
      change SobolevMultiIndex.fn w x * SobolevMultiIndex.fn Φ x = _
      rw [hx, hx']
    have hψ2 : MemLp ψ 2 (volume.restrict ((ℝ₊ : Opens 𝔼) : Set 𝔼)) :=
      (TestFunction.memLp ψ 2 volume).restrict _
    have hi1 : Integrable (fun x ↦ (partialDeriv f j x
        - SobolevMultiIndex.weakDeriv u (MultiIndexLE.single j) x) * ψ x)
        (volume.restrict ((ℝ₊ : Opens 𝔼) : Set 𝔼)) :=
      ((Lp.memLp (partialDeriv f j)).sub (Lp.memLp _)).integrable_mul_two hψ2
    have hi2 : Integrable (fun x ↦ SobolevMultiIndex.weakDeriv u (MultiIndexLE.single j) x * ψ x)
        (volume.restrict ((ℝ₊ : Opens 𝔼) : Set 𝔼)) :=
      (Lp.memLp _).integrable_mul_two hψ2
    rw [e1, e2, ← integral_add hi1 hi2]
    congr 1
    funext x
    ring
  refine ⟨w, hwd, (isWeakSolutionDirichlet_iff _ w).2 ⟨hw0, fun Φ hΦ ↦ ?_⟩⟩
  have := Elliptic.apply_eq_zero_of_forall_testFunctions
    (L := Elliptic.laplaceForm ℝ₊ w - Elliptic.load ℝ₊ (partialDeriv f j))
    (fun Ψ hΨ ↦ by rw [sub_apply, hweq Ψ hΨ, sub_self]) hΦ
  rwa [sub_apply, sub_eq_zero] at this

/-- **Lemma 9.8** of [brezis2011functional]. Let $N \ge 1$, let $\Omega \subset \mathbb{R}^N$ be
open, and let $H : Q \to U$ be a $C^2$ chart of $\Omega$ with inverse $J = H^{-1}$, as in case
C₂ of the proof of Theorem 9.25. Let $g \in L^2(\Omega \cap U)$ and let
$v \in H_0^1(\Omega \cap U)$ satisfy
$$\int_{\Omega \cap U} \nabla v \cdot \nabla \varphi = \int_{\Omega \cap U} g \varphi \quad
  \text{for all } \varphi \in H_0^1(\Omega \cap U). \qquad (59)$$
Then the function $w(y) = v(H(y))$ belongs to $H_0^1(Q_+)$ and satisfies
$$\sum_{k, \ell} \int_{Q_+} a_{k\ell} \frac{\partial w}{\partial y_k} \frac{\partial
  \psi}{\partial y_\ell} = \int_{Q_+} \tilde g \psi \quad \text{for all } \psi \in H_0^1(Q_+),
  \qquad (60)$$
where $\tilde g = (g \circ H) |\det \operatorname{Jac} H| \in L^2(Q_+)$, and the functions
$a_{k\ell} = \sum_j \frac{\partial J_k}{\partial x_j} \frac{\partial J_\ell}{\partial x_j} |\det
\operatorname{Jac} H|$ are of class $C^1$ on $Q \supseteq Q_+$ and satisfy the ellipticity
condition (36) on $Q_+$ for some constant.

The chart is `c : ContDiffChart 2 Ω`, with $H$ = `c.toFun` and $J$ = `c.invFun`. The open sets
$\Omega \cap U$ and $Q_+$ are the `Opens` variables `Ω₁` and `Qp`, with the carriers
$U \cap \Omega$ and `unitChartCubePos d`; $Q$ is `unitChartCube d`. The datum $\tilde g$ is
`Elliptic.chartDatum H g`, and the coefficients $a_{k\ell}$ are
`Elliptic.chartCoeff H J k ℓ`. The proof is the backbone's `Elliptic.transfer_chart_ae_eq` (the
change of variables of Proposition 9.6 and Mathlib's
`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`), with
`Elliptic.contDiffOn_chartCoeff` and `Elliptic.chartCoeff_elliptic` for the coefficients.

**Generalization.** The transformed coefficients are proved $C^1$ on $Q$. The source's
 statement asks for $C^1$ regularity on $Q_+$. -/
theorem lemma_9_8 (c : ContDiffChart 2 (Ω : Set 𝔼)) {Ω₁ Qp : Opens 𝔼}
    (hΩ₁ : (Ω₁ : Set 𝔼) = c.U ∩ Ω) (hQp : (Qp : Set 𝔼) = unitChartCubePos d)
    {v : hSpace (d + 1) Ω₁} (hv : v ∈ hZeroSpace (d + 1) Ω₁)
    {g : Lp ℝ 2 (volume.restrict (Ω₁ : Set 𝔼))}
    (heq : ∀ φ ∈ hZeroSpace (d + 1) Ω₁,
      ∫ x in (Ω₁ : Set 𝔼), ∑ i, partialDeriv v i x * partialDeriv φ i x
        = ∫ x in (Ω₁ : Set 𝔼), g x * SobolevMultiIndex.fn φ x) :
    ∃ w : hSpace (d + 1) Qp, w ∈ hZeroSpace (d + 1) Qp ∧
      (SobolevMultiIndex.fn w =ᵐ[volume.restrict (Qp : Set 𝔼)]
        fun y ↦ SobolevMultiIndex.fn v (c.toFun y)) ∧
      MemLp (Elliptic.chartDatum c.toFun g) 2 (volume.restrict (Qp : Set 𝔼)) ∧
      (∀ k l, ContDiffOn ℝ 1 (Elliptic.chartCoeff c.toFun c.invFun k l) (unitChartCube d)) ∧
      (∃ α, ellipticityCondition Qp (Elliptic.chartCoeff c.toFun c.invFun) α) ∧
      ∀ ψ ∈ hZeroSpace (d + 1) Qp,
        ∑ k, ∑ l, ∫ y in (Qp : Set 𝔼), Elliptic.chartCoeff c.toFun c.invFun k l y
          * partialDeriv w k y * partialDeriv ψ l y
          = ∫ y in (Qp : Set 𝔼), Elliptic.chartDatum c.toFun g y * SobolevMultiIndex.fn ψ y := by
  -- the chart as a diffeomorphism `Q₊ → Ω ∩ U`, and as a diffeomorphism `Q → U`
  obtain ⟨M, h⟩ := c.isDiffeoOnWithBoundedJacobian_pos (by norm_num) Ω.isOpen
  have h' : IsDiffeoOnWithBoundedJacobian c.toFun c.invFun (Qp : Set 𝔼) (Ω₁ : Set 𝔼) M := by
    rw [hQp, hΩ₁]; exact h
  obtain ⟨M', hfull⟩ := c.isDiffeoOnWithBoundedJacobian (by norm_num)
  -- the typed equation (59)
  have heq' : ∀ Ψ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω₁,
      Elliptic.dirichletForm Ω₁ v Ψ = Elliptic.load Ω₁ g Ψ := fun Ψ hΨ ↦ by
    rw [Elliptic.dirichletForm_apply, Elliptic.load_apply]
    exact heq Ψ hΨ
  obtain ⟨w, A, G', hw0, hwfn, hAa, hG', hweq⟩ := Elliptic.transfer_chart_ae_eq h' hv heq'
  refine ⟨w, hw0, hwfn, Elliptic.memLp_chartDatum h' g, fun k l ↦ ?_, ?_, fun ψ hψ ↦ ?_⟩
  · exact Elliptic.contDiffOn_chartCoeff isOpen_unitChartCube c.isOpen_U
      (c.contDiffOn.mono subset_closure) (c.contDiffOn_invFun.mono subset_closure)
      c.bijOn.mapsTo (fun y hy ↦ hfull.det_fderiv_ne_zero hy) k l
  · obtain ⟨α, hα, hell⟩ := Elliptic.chartCoeff_elliptic h'
    exact ⟨α, hα, hell⟩
  · have e := hweq ψ hψ
    rw [Elliptic.generalForm_zero_zero_apply, Elliptic.load_apply] at e
    have e2 : ∫ y in (Qp : Set 𝔼), G' y * SobolevMultiIndex.fn ψ y
        = ∫ y in (Qp : Set 𝔼), Elliptic.chartDatum c.toFun g y * SobolevMultiIndex.fn ψ y :=
      integral_congr_ae (hG'.mono fun y hy ↦ by dsimp only; rw [hy])
    rw [e2] at e
    rw [← e]
    refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
    rw [Elliptic.inner_mulL_eq_integral]
    refine integral_congr_ae ((hAa k l).mono fun y hy ↦ ?_)
    dsimp only
    rw [hy]
    rfl

/-! ### Theorem 9.26: the half space, and the Neumann boundary condition -/

/-- **Theorem 9.26** of [brezis2011functional] (regularity for the Neumann problem), the alternative
"or else $\Omega = \mathbb{R}^N_+$", $H^2$ clause. Let $N \ge 1$. There is a constant $C \ge 0$
with the following property. Let $f \in L^2(\mathbb{R}^N_+)$ and let $u \in H^1(\mathbb{R}^N_+)$
satisfy
$$\int \nabla u \cdot \nabla \varphi + \int u \varphi = \int f \varphi \quad \text{for all }
  \varphi \in H^1(\mathbb{R}^N_+). \qquad (49)$$
Then $u \in H^2(\mathbb{R}^N_+)$ and $\|u\|_{H^2} \le C \|f\|_{L^2}$.

The conclusion is read as in `Brezis.Chapter09.theorem_9_25`. The proof is case B of the proof
of Theorem 9.25. The method of translations needs of the test space only that it contains the
test functions and is invariant under the tangential translations. Both hold for
$H^1(\mathbb{R}^N_+)$, so the delicate point of the source (Lemma 9.7) does not arise:
`Elliptic.regularity_neumann_upperHalfSpace` is case B of the Dirichlet problem with the test
space `⊤`, and the constant is the same $3 C_N$ as in
`Brezis.Chapter09.theorem_9_25_upperHalfSpace`. On a general $C^2$ domain with $\Gamma$ bounded,
the theorem is not formalized. -/
theorem theorem_9_26_upperHalfSpace :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Lp ℝ 2 (volume.restrict ((ℝ₊ : Opens 𝔼) : Set 𝔼)))
      (u : hSpace (d + 1) ℝ₊), IsWeakSolutionNeumann ℝ₊ f u →
        (∃ U : sobolevSpaceHigher (d + 1) 2 2 ℝ₊, SobolevMultiIndex.fn U
          =ᵐ[volume.restrict ((ℝ₊ : Opens 𝔼) : Set 𝔼)] SobolevMultiIndex.fn u) ∧
        ∀ U : sobolevSpaceHigher (d + 1) 2 2 ℝ₊, SobolevMultiIndex.fn U
          =ᵐ[volume.restrict ((ℝ₊ : Opens 𝔼) : Set 𝔼)] SobolevMultiIndex.fn u →
            ‖U‖ ≤ C * ‖f‖ := by
  have hC0 : (0 : ℝ) ≤ Elliptic.regularityConst d 1 1 0 := by
    unfold Elliptic.regularityConst
    positivity
  refine ⟨3 * Elliptic.regularityConst d 1 1 0, by linarith, fun f u hu ↦ ?_⟩
  have hu' := (isWeakSolutionNeumann_iff f u).1 hu
  have hg := Elliptic.dirichletForm_eq_load_sub_of_isGalerkinSolution_laplace hu'
  obtain ⟨U, hU, hUn⟩ := Elliptic.regularity_neumann_upperHalfSpace ⟨hu'.1, hg⟩
  have hun : ‖u‖ ≤ ‖f‖ := Elliptic.norm_le_of_isGalerkinSolution_laplace _ hu'
  have hg' : ‖f - SobolevMultiIndex.weakDeriv u 0‖ ≤ 2 * ‖f‖ := by
    calc ‖f - SobolevMultiIndex.weakDeriv u 0‖ ≤ ‖f‖ + ‖SobolevMultiIndex.weakDeriv u 0‖ :=
          norm_sub_le _ _
      _ ≤ ‖f‖ + ‖u‖ := by gcongr; exact SobolevMultiIndex.norm_weakDeriv_le u 0
      _ ≤ 2 * ‖f‖ := by linarith
  refine ⟨⟨U, hU⟩, fun U' hU' ↦ ?_⟩
  rw [SobolevMultiIndex.ext_of_fn_ae_eq (hU'.trans hU.symm)]
  calc ‖U‖ ≤ Elliptic.regularityConst d 1 1 0 * (‖u‖ + ‖f - SobolevMultiIndex.weakDeriv u 0‖) :=
        hUn
    _ ≤ Elliptic.regularityConst d 1 1 0 * (‖f‖ + 2 * ‖f‖) := by gcongr
    _ = 3 * Elliptic.regularityConst d 1 1 0 * ‖f‖ := by ring

/-- **Theorem 9.26** of [brezis2011functional], the alternative "or else $\Omega = \mathbb{R}^N_+$",
$H^{m+2}$ clause. Let $N \ge 1$ and $m \ge 0$, let $f \in H^m(\mathbb{R}^N_+)$, and let
$u \in H^1(\mathbb{R}^N_+)$ satisfy (49). Then $u \in H^{m+2}(\mathbb{R}^N_+)$: the function of
$u$ is the function of some element of $H^{m+2}(\mathbb{R}^N_+)$.

The source also states the bound $\|u\|_{H^{m+2}} \le C \|f\|_{H^m}$, which is not formalized:
the closed-graph argument of `Brezis.Chapter09.theorem_9_25_higher` needs a solution map for the
Neumann problem, and the backbone's `Elliptic.solutionMap` is built only for the test space
$H_0^1(\Omega)$. The proof is case B at every order
(`Elliptic.regularity_neumann_upperHalfSpace_higher_mem_laplace`). The tangential derivatives of
a Neumann solution are Neumann solutions with the differentiated data; this Neumann analogue of
Lemma 9.7 is proved by a tangential integration by parts against the test functions of
$\mathbb{R}^N$, not by the weak compactness of the source. The second normal derivative is then
read off the equation.

**Reading.** This statement includes the Sobolev membership on the half space. The source
 also asserts a norm bound. -/
theorem theorem_9_26_upperHalfSpace_higher (m : ℕ) (f : sobolevSpaceHigher (d + 1) m 2 ℝ₊)
    {u : hSpace (d + 1) ℝ₊}
    (hu : IsWeakSolutionNeumann ℝ₊ (SobolevMultiIndex.fnL ℝ 𝔟 m 2 ℝ₊ volume f) u) :
    ∃ U : sobolevSpaceHigher (d + 1) (m + 2) 2 ℝ₊, SobolevMultiIndex.fn U
      =ᵐ[volume.restrict ((ℝ₊ : Opens 𝔼) : Set 𝔼)] SobolevMultiIndex.fn u := by
  refine (Elliptic.regularity_neumann_upperHalfSpace_higher_mem_laplace m ?_
    ((isWeakSolutionNeumann_iff _ u).1 hu)).exists_sobolevMultiIndex
  rw [SobolevMultiIndex.fnL_apply]
  exact SobolevMultiIndex.memSobolevMultiIndex f

/-- **Theorem 9.26** of [brezis2011functional], the boundary condition. Let $N \ge 1$, let
$\Omega \subset \mathbb{R}^N$ be a bounded open set of class $C^1$ with the outward unit normal
$n$ and the surface measure $\sigma$, and let $f \in L^2(\Omega)$. Let $U \in H^2(\Omega)$ be
such that $U$, as an element of $H^1(\Omega)$, is a weak solution of the Neumann problem (49).
Then the normal derivative of $U$ in the sense of traces vanishes:
$$\frac{\partial U}{\partial n} = \sum_i n_i \, \gamma\Bigl(\frac{\partial U}{\partial
  x_i}\Bigr) = 0 \quad \sigma\text{-almost everywhere on } \Gamma.$$

The $C^2$ hypothesis of Theorem 9.26 is needed only for the $H^2$ regularity, which is a
hypothesis here. This is the sense in which the Neumann condition $\partial u / \partial n = 0$
on $\Gamma$ of (44) holds for the $H^2$ solution of Theorem 9.26. Together with the $H^2$
regularity, which is `Brezis.Chapter09.theorem_9_26_upperHalfSpace` on the half space and is not
formalized on a general $C^2$ domain, it gives the full Theorem 9.26.

In Lean, "of class $C^1$" is `IsContDiffDomain 1 Ω`. The trace $\gamma$ is
`IsContDiffDomain.traceL`. The measure `hΩ.boundaryMeasure hb` is the surface measure $\sigma$,
and the field `hΩ.outwardNormal hb` is the normal $n$. The normal derivative is
`BoundaryData.TraceFamily.normalTrace`, the $\partial u / \partial n$ of the Comments on Chapter
9, 7(iii). The element $U$ of $H^2(\Omega)$, read in $H^1(\Omega)$, is
`SobolevMultiIndex.toLowerOrderL ℝ 𝔟 2 Ω volume _ U₂`. The proof is the backbone's
`BoundaryData.TraceFamily.normalTrace_eq_zero_of_forall_laplaceForm_eq` through
`Brezis.Chapter09.isWeakSolutionNeumann_iff`.

**Reading.** This statement assumes $H^2$ membership and gives the homogeneous normal
 condition as an almost-everywhere trace identity. -/
theorem theorem_9_26_normalDeriv (hΩ : IsContDiffDomain 1 (Ω : Set 𝔼))
    (hb : Bornology.IsBounded (Ω : Set 𝔼)) {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))}
    (U₂ : SobolevEuclidean (d + 1) 2 2 Ω)
    (hU : IsWeakSolutionNeumann Ω f
      (SobolevMultiIndex.toLowerOrderL ℝ 𝔟 2 Ω volume (by norm_num) U₂)) :
    (hΩ.traceFamily hb).normalTrace U₂ =ᵐ[hΩ.boundaryMeasure hb] 0 :=
  (hΩ.traceFamily hb).normalTrace_eq_zero_of_forall_laplaceForm_eq U₂ f fun φ ↦
    ((isWeakSolutionNeumann_iff f _).1 hU).2 φ Submodule.mem_top

end Regularity

end Brezis.Chapter09
