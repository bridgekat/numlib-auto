/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.Brezis.Chapter09.Section05

/-!
# Brezis, Section 9.7: The maximum principle

This module formalizes Section 9.7 of [brezis2011functional]. Let $\Omega$ be a general open subset
of $\mathbb{R}^N$ with boundary $\Gamma$. Theorem 9.27 is the maximum principle for the Dirichlet
problem: if $f \in L^2(\Omega)$ and $u \in H^1(\Omega) \cap C(\overline\Omega)$ satisfy
$$\int_\Omega \nabla u \cdot \nabla \varphi + \int_\Omega u \varphi = \int_\Omega f \varphi \quad
  \text{for all } \varphi \in H_0^1(\Omega), \qquad (70)$$
then
$$\min\Bigl\{\inf_\Gamma u, \inf_\Omega f\Bigr\} \le u \le \max\Bigl\{\sup_\Gamma u, \sup_\Omega
  f\Bigr\} \quad \text{in } \Omega. \qquad (71)$$
The proof is Stampacchia's truncation method. Corollary 9.28 draws consequences for the sign and the
$L^\infty$ norm of $u$. Remark 27 gives the classical proof for classical solutions, which also
applies to general second-order elliptic operators. Proposition 9.29 extends the maximum principle
to the weak solutions of general second-order elliptic equations with $a_0 \ge 0$, and Proposition
9.30 is the maximum principle for the Neumann problem.

The proofs specialize the backbone module `Numlib.Analysis.PDE.Elliptic.MaximumPrinciple`.

## Main results

* Theorem 9.27, `Brezis.Chapter09.theorem_9_27` (maximum principle for the Dirichlet problem): the
  bounds (71).
* Theorem 9.27, footnote 35, `Brezis.Chapter09.theorem_9_27_of_mem_zero`: for $u \in H_0^1(\Omega)$,
  the bounds hold almost everywhere without the continuity of $u$.
* Corollary 9.28, (72), `Brezis.Chapter09.corollary_9_28`: $u \ge 0$ on $\Gamma$ and $f \ge 0$ in
  $\Omega$ give $u \ge 0$ in $\Omega$.
* Corollary 9.28, (73), `Brezis.Chapter09.corollary_9_28_bound`: $\|u\|_{L^\infty(\Omega)} \le
  \max\{\|u\|_{L^\infty(\Gamma)}, \|f\|_{L^\infty(\Omega)}\}$.
* Corollary 9.28, the case $f = 0$, `Brezis.Chapter09.corollary_9_28_zero_load`:
  $\|u\|_{L^\infty(\Omega)} \le \|u\|_{L^\infty(\Gamma)}$.
* Corollary 9.28, the case $u = 0$ on $\Gamma$, `Brezis.Chapter09.corollary_9_28_zero_boundary`:
  $\|u\|_{L^\infty(\Omega)} \le \|f\|_{L^\infty(\Omega)}$.
* Remark 27, the Laplacian, `Brezis.Chapter09.remark_9_27`: the classical maximum principle for
  $-\Delta u + u = f$ on a bounded $\Omega$.
* Remark 27, the general operator, `Brezis.Chapter09.remark_9_27_general`: the classical maximum
  principle for the general elliptic equation (77).
* Proposition 9.29, (79), without first-order term, `Brezis.Chapter09.proposition_9_29_zero_drift`:
  $u \ge 0$ on $\Gamma$ and $f \ge 0$ in $\Omega$ give $u \ge 0$ in $\Omega$.
* Proposition 9.29, (79), footnote 38, `Brezis.Chapter09.proposition_9_29_zero_drift_of_mem_zero`:
  the same almost everywhere for $u \in H_0^1(\Omega)$.
* Proposition 9.29, (80), without first-order term,
  `Brezis.Chapter09.proposition_9_29_inf_zero_drift`: for $a_0 = 0$ and a bounded $\Omega$,
  $f \ge 0$ gives $u \ge \inf_\Gamma u$.
* Proposition 9.29, (81), without first-order term,
  `Brezis.Chapter09.proposition_9_29_sup_inf_zero_drift`: for $a_0 = 0$, $f = 0$ and a bounded
  $\Omega$, $\inf_\Gamma u \le u \le \sup_\Gamma u$.
* Proposition 9.29, (79), (80) and (81) with a first-order term,
  `Brezis.Chapter09.proposition_9_29`, `Brezis.Chapter09.proposition_9_29_inf` and
  `Brezis.Chapter09.proposition_9_29_sup_inf`: the same statements for arbitrary
  $a_i \in L^\infty(\Omega)$, for $N \ge 3$.
* Proposition 9.30, `Brezis.Chapter09.proposition_9_30` (maximum principle for the Neumann problem):
  $\inf_\Omega f \le u \le \sup_\Omega f$ almost everywhere in $\Omega$.

## Conventions

* The source writes $\sup_\Gamma u$ and $\sup_\Omega f$, where the supremum over $\Omega$ is the
  essential supremum. The statements use explicit bounds $K$: "$u \le K$ on $\Gamma$ and $f \le K$
  almost everywhere on $\Omega$ give $u \le K$ in $\Omega$". With $K$ equal to the supremum, this is
  the statement of the source when the supremum is finite; when it is infinite, the statement of the
  source says nothing. The displays (71), (74), (80) and (81) are read in this way.
* "$u \in H^1(\Omega) \cap C(\overline\Omega)$" is an element `u : Brezis.Chapter09.hSpace N Ω` with
  a representative $\tilde u$ that is continuous on $\overline\Omega$. The conclusions "$u \le K$ in
  $\Omega$" hold for $\tilde u$ at every point of $\Omega$.
* Footnotes 35, 37 and 38 say that "the assumption $u \in C(\overline\Omega)$ can be removed if
  $u \in H_0^1(\Omega)$". The variants `Brezis.Chapter09.theorem_9_27_of_mem_zero` (footnote 35) and
  `Brezis.Chapter09.proposition_9_29_zero_drift_of_mem_zero` (footnote 38) state this; their
  conclusions hold almost everywhere.
* The weak equations (70), (78) and that of Proposition 9.30 are written with the integrals of the
  source. `Brezis.Chapter09.forall_laplaceForm_eq_load_iff`,
  `Brezis.Chapter09.forall_generalForm_zero_drift_eq_load_iff` and
  `Brezis.Chapter09.forall_generalForm_eq_load_iff` relate them to the bilinear forms of the
  backbone.

## Implementation notes

* The source proves Proposition 9.29 only for $a_i \equiv 0$. This case is stated for every
  $N \ge 1$, as the hypothesis `N ≠ 0`. The statements with an arbitrary first-order term follow the
  proof of Gilbarg–Trudinger in the backbone and assume $N \ge 3$, which the Sobolev inequality of
  Remark 20 on $W_0^{1,2}(\Omega)$ requires.

## Deviations from the source

* **Theorem 9.27 and Corollary 9.28** (reading). The statements use finite pointwise bounds
  on the boundary and finite essential bounds on the datum in the domain. See
  `Brezis.Chapter09.theorem_9_27` and `Brezis.Chapter09.corollary_9_28_bound`.
* **Remark 27** (reading). The classical results state the upper inequality. The general
  operator has an explicitly symmetric principal matrix. See
  `Brezis.Chapter09.remark_9_27` and `Brezis.Chapter09.remark_9_27_general`.
* **Proposition 9.29 without first-order term** (reading). The source leaves the hypothesis
  $N \ge 1$ implicit; the constancy argument of footnote 39 needs it. See
  `Brezis.Chapter09.proposition_9_29_zero_drift` and the three variants that follow it.
* **Proposition 9.29 with first-order term** (reading). The library treats $N \ge 3$. See
  `Brezis.Chapter09.proposition_9_29`.
* **Proposition 9.29, (81)** (typo). The source omits $u$ between the boundary bounds. See
  `Brezis.Chapter09.proposition_9_29_sup_inf` and
  `Brezis.Chapter09.proposition_9_29_sup_inf_zero_drift`.
* **Proposition 9.30** (reading). The two-sided bound requires finite essential upper and
  lower bounds at the same time, while the source's inequalities use possibly infinite
  extrema. See `Brezis.Chapter09.proposition_9_30`.

## Not formalized

* **Proposition 9.29, (79), (80) and (81) with a first-order term, for $N \le 2$.** The proof uses
  the Sobolev inequality $\|v\|_{L^{2^*}(\Omega)} \le C(2, N) \|\nabla v\|_{L^2(\Omega)}$ on
  $W_0^{1,2}(\Omega)$ of Remark 20 (`Brezis.Chapter09.remark_9_20_sobolev`), which needs $N > 2$.
  The proof needs it only in the form $\|v\|_{L^2(\Omega)} \le C_N \|\nabla v\|_{L^2(\Omega)} |\{v
  \neq 0\}|^{1/N}$, which is true in every dimension but is not in the library for $N \le 2$. The
  module doc comment of `Numlib.Analysis.PDE.Elliptic.MaximumPrinciple` records what the cases
  $N = 2$ and $N = 1$ need. The source gives no proof of the general case, and Gilbarg–Trudinger
  state their Theorem 8.1 for a bounded domain.
* **Remark 27, the last sentence.** The maximum principle for weak solutions of (77), which the
  source quotes from Gilbarg–Trudinger.
-/

open Filter MeasureTheory Metric Set Topology TopologicalSpace Laplacian
open scoped ContDiff Distributions ENNReal NNReal

namespace Brezis.Chapter09

section MaximumPrinciple

variable {N : ℕ}

/-- The space $\mathbb{R}^N$ of the source, `EuclideanSpace ℝ (Fin N)`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

variable {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-! ### The weak equations in the backbone's terms -/

/-- Let $\Omega \subset \mathbb{R}^N$ be open, let $u \in H^1(\Omega)$ and $f \in L^2(\Omega)$, and
let $V$ be a subspace of $H^1(\Omega)$. Then
$$\int_\Omega \nabla u \cdot \nabla \varphi + \int_\Omega u \varphi = \int_\Omega f \varphi
  \quad \text{for all } \varphi \in V$$
if and only if $a(u, \varphi) = \int_\Omega f \varphi$ for all $\varphi \in V$, where $a$ is the
backbone's form `Elliptic.laplaceForm Ω` and the right-hand side is `Elliptic.load Ω f`.

For $V = H_0^1(\Omega)$ this is the weak equation (70), and for $V = H^1(\Omega)$ it is the weak
equation of Proposition 9.30.

**Generalization.** The test space can be any submodule. The source uses $H_0^1$ and $H^1$. -/
theorem forall_laplaceForm_eq_load_iff (u : hSpace N Ω) (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)))
    (V : Submodule ℝ (hSpace N Ω)) :
    (∀ φ ∈ V, (∫ x in (Ω : Set 𝔼), ∑ i, partialDeriv u i x * partialDeriv φ i x)
        + ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn u x * SobolevMultiIndex.fn φ x
        = ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn φ x) ↔
      ∀ φ ∈ V, Elliptic.laplaceForm Ω u φ = Elliptic.load Ω f φ := by
  simp only [laplaceForm_apply_two, Elliptic.load_apply]

/-- Let $\Omega \subset \mathbb{R}^N$ be open, let $a_{ij}, a_0 \in L^\infty(\Omega)$, and let
$u, v \in H^1(\Omega)$. The bilinear form (41) without first-order term,
`Elliptic.generalForm Ω A 0 a₀`, is the left-hand side of (78) with $a_i = 0$:
$$a(u, v) = \int_\Omega \sum_{i,j} a_{ij} \frac{\partial u}{\partial x_i} \frac{\partial
  v}{\partial x_j} + \int_\Omega a_0 u v.$$

This restates the backbone's `Elliptic.generalForm_zero_drift_apply` with
`Brezis.Chapter09.partialDeriv`. -/
theorem generalForm_zero_drift_apply (A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼)))
    (a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼))) (u v : hSpace N Ω) :
    Elliptic.generalForm Ω A 0 a₀ u v
      = (∫ x in (Ω : Set 𝔼), ∑ i, ∑ j, A i j x * partialDeriv u i x * partialDeriv v j x)
        + ∫ x in (Ω : Set 𝔼), a₀ x * SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x :=
  Elliptic.generalForm_zero_drift_apply Ω A a₀ u v

/-- Let $\Omega \subset \mathbb{R}^N$ be open, let $a_{ij}, a_0 \in L^\infty(\Omega)$, let
$u \in H^1(\Omega)$ and let $f \in L^2(\Omega)$. Then
$$\int_\Omega \sum_{i,j} a_{ij} \frac{\partial u}{\partial x_i} \frac{\partial \varphi}{\partial
  x_j} + \int_\Omega a_0 u \varphi = \int_\Omega f \varphi \quad \text{for all } \varphi \in
  H_0^1(\Omega),$$
which is (78) with $a_i = 0$, if and only if $a(u, \varphi) = \int_\Omega f \varphi$ for all
$\varphi \in H_0^1(\Omega)$, where $a$ is `Elliptic.generalForm Ω A 0 a₀` and the right-hand
side is `Elliptic.load Ω f`. -/
theorem forall_generalForm_zero_drift_eq_load_iff
    (A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼)))
    (a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼))) (u : hSpace N Ω)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) :
    (∀ φ ∈ hZeroSpace N Ω,
        (∫ x in (Ω : Set 𝔼), ∑ i, ∑ j, A i j x * partialDeriv u i x * partialDeriv φ j x)
          + ∫ x in (Ω : Set 𝔼), a₀ x * SobolevMultiIndex.fn u x * SobolevMultiIndex.fn φ x
          = ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn φ x) ↔
      ∀ φ ∈ hZeroSpace N Ω, Elliptic.generalForm Ω A 0 a₀ u φ = Elliptic.load Ω f φ := by
  simp only [generalForm_zero_drift_apply, Elliptic.load_apply]

/-! ### Theorem 9.27 -/

/-- **Theorem 9.27** of [brezis2011functional] (maximum principle for the Dirichlet problem). Let
$\Omega \subset \mathbb{R}^N$ be a general open set, and let $f \in L^2(\Omega)$ and
$u \in H^1(\Omega) \cap C(\overline\Omega)$ satisfy (70). Then for every $x \in \Omega$,
$$\min\Bigl\{\inf_\Gamma u, \inf_\Omega f\Bigr\} \le u(x) \le \max\Bigl\{\sup_\Gamma u,
  \sup_\Omega f\Bigr\}. \qquad (71)$$
Precisely, let $\tilde u$ be the representative of $u$ that is continuous on $\overline\Omega$.
If $\tilde u \le K_1$ on $\Gamma$ and $f \le K_2$ almost everywhere on $\Omega$, then
$\tilde u(x) \le \max\{K_1, K_2\}$ for every $x \in \Omega$. If $K_1 \le \tilde u$ on $\Gamma$
and $K_2 \le f$ almost everywhere on $\Omega$, then $\min\{K_1, K_2\} \le \tilde u(x)$ for every
$x \in \Omega$.

The proof is the backbone's `Elliptic.le_max_of_isWeakSolution` and
`Elliptic.ge_of_ge_frontier`. It uses Stampacchia's truncation $G(u - K')$
(`exists_stampacchiaTruncation`), which lies in $H^1(\Omega)$ by Proposition 9.5 and in
$H_0^1(\Omega)$ by Theorem 9.17, and it covers both cases $|\Omega| < \infty$ and
$|\Omega| = \infty$ of the proof of the source. The proof of the source says "proceed as in the
proof of Theorem 8.18"; the one-dimensional maximum principle is Theorem 8.19
(`Brezis.Chapter08.theorem_8_19`).

**Reading.** The boundary inequalities are pointwise. The domain forcing bounds are
 essential. The statement quantifies over finite bounds for each side independently. -/
theorem theorem_9_27 {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))} {u : hSpace N Ω}
    (hu : ∀ φ ∈ hZeroSpace N Ω,
      (∫ x in (Ω : Set 𝔼), ∑ i, partialDeriv u i x * partialDeriv φ i x)
        + ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn u x * SobolevMultiIndex.fn φ x
        = ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn φ x)
    {ũ : 𝔼 → ℝ} (hũ : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set 𝔼))) :
    (∀ K₁ K₂ : ℝ, (∀ x ∈ frontier (Ω : Set 𝔼), ũ x ≤ K₁) →
      (∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), f x ≤ K₂) → ∀ x ∈ Ω, ũ x ≤ max K₁ K₂) ∧
    (∀ K₁ K₂ : ℝ, (∀ x ∈ frontier (Ω : Set 𝔼), K₁ ≤ ũ x) →
      (∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), K₂ ≤ f x) → ∀ x ∈ Ω, min K₁ K₂ ≤ ũ x) := by
  have heq := (forall_laplaceForm_eq_load_iff u f _).1 hu
  refine ⟨fun K₁ K₂ hΓ hf ↦ Elliptic.le_max_of_isWeakSolution heq hũ hc hΓ hf,
    fun K₁ K₂ hΓ hf ↦ ?_⟩
  exact Elliptic.ge_of_ge_frontier heq hũ hc (K := min K₁ K₂)
    (fun x hx ↦ (min_le_left _ _).trans (hΓ x hx))
    (hf.mono fun x hx ↦ (min_le_right _ _).trans hx)

/-- **Theorem 9.27** of [brezis2011functional], footnote 35: for $u \in H_0^1(\Omega)$ the
assumption $u \in C(\overline\Omega)$ can be removed. Let $\Omega \subset \mathbb{R}^N$ be open,
and let $f \in L^2(\Omega)$ and $u \in H_0^1(\Omega)$ satisfy (70). If $K \ge 0$ and $f \le K$
almost everywhere on $\Omega$, then $u \le K$ almost everywhere on $\Omega$. If $K \le 0$ and
$K \le f$ almost everywhere on $\Omega$, then $K \le u$ almost everywhere on $\Omega$.

The boundary value $0$ of $u$ takes the place of $\sup_\Gamma u$ and of $\inf_\Gamma u$. The
proof is the backbone's `Elliptic.le_of_mem_zero` and `Elliptic.ge_of_mem_zero`, where the
truncations $G(u - K')$ lie in $H_0^1(\Omega)$ by the chain rule on $W_0^{1,p}$.

**Reading.** The replacement for continuity is membership in $H_0^1$. Each bound is stated
 for a real constant compatible with the zero boundary value. -/
theorem theorem_9_27_of_mem_zero {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))} {u : hSpace N Ω}
    (hu0 : u ∈ hZeroSpace N Ω)
    (hu : ∀ φ ∈ hZeroSpace N Ω,
      (∫ x in (Ω : Set 𝔼), ∑ i, partialDeriv u i x * partialDeriv φ i x)
        + ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn u x * SobolevMultiIndex.fn φ x
        = ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn φ x) :
    (∀ K : ℝ, 0 ≤ K → (∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), f x ≤ K) →
      ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), SobolevMultiIndex.fn u x ≤ K) ∧
    (∀ K : ℝ, K ≤ 0 → (∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), K ≤ f x) →
      ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), K ≤ SobolevMultiIndex.fn u x) := by
  have heq := (forall_laplaceForm_eq_load_iff u f _).1 hu
  exact ⟨fun K hK hf ↦ Elliptic.le_of_mem_zero hu0 heq hK hf,
    fun K hK hf ↦ Elliptic.ge_of_mem_zero hu0 heq hK hf⟩

/-! ### Corollary 9.28 -/

/-- **Corollary 9.28** of [brezis2011functional], (72). Let $\Omega \subset \mathbb{R}^N$ be open,
and let $f \in L^2(\Omega)$ and $u \in H^1(\Omega) \cap C(\overline\Omega)$ satisfy (70). Then
$$[u \ge 0 \text{ on } \Gamma \text{ and } f \ge 0 \text{ in } \Omega] \Rightarrow [u \ge 0
  \text{ in } \Omega].$$

The condition $f \ge 0$ holds almost everywhere, and the conditions on $u$ hold at every point
for the representative $\tilde u$ of $u$ that is continuous on $\overline\Omega$. The proof is
the backbone's `Elliptic.nonneg_of_nonneg_frontier`, the lower bound of Theorem 9.27 with
$K = 0$. -/
theorem corollary_9_28 {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))} {u : hSpace N Ω}
    (hu : ∀ φ ∈ hZeroSpace N Ω,
      (∫ x in (Ω : Set 𝔼), ∑ i, partialDeriv u i x * partialDeriv φ i x)
        + ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn u x * SobolevMultiIndex.fn φ x
        = ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn φ x)
    {ũ : 𝔼 → ℝ} (hũ : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set 𝔼))) (hΓ : ∀ x ∈ frontier (Ω : Set 𝔼), 0 ≤ ũ x)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), 0 ≤ f x) : ∀ x ∈ Ω, 0 ≤ ũ x :=
  Elliptic.nonneg_of_nonneg_frontier ((forall_laplaceForm_eq_load_iff u f _).1 hu) hũ hc hΓ hf

/-- **Corollary 9.28** of [brezis2011functional], (73). Let $\Omega \subset \mathbb{R}^N$ be open,
and let $f \in L^2(\Omega)$ and $u \in H^1(\Omega) \cap C(\overline\Omega)$ satisfy (70). Then
$$\|u\|_{L^\infty(\Omega)} \le \max\bigl\{\|u\|_{L^\infty(\Gamma)},
  \|f\|_{L^\infty(\Omega)}\bigr\}.$$
Precisely, let $\tilde u$ be the representative of $u$ that is continuous on $\overline\Omega$.
If $|\tilde u| \le K_1$ on $\Gamma$ and $|f| \le K_2$ almost everywhere on $\Omega$, then
$|\tilde u| \le \max\{K_1, K_2\}$ on $\Omega$.

The proof is the backbone's `Elliptic.abs_le_max_of_isWeakSolution`, from the two bounds of
Theorem 9.27.

**Reading.** The norm estimate uses arbitrary finite pointwise bounds on the boundary and
 finite essential bounds on the forcing. -/
theorem corollary_9_28_bound {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))} {u : hSpace N Ω}
    (hu : ∀ φ ∈ hZeroSpace N Ω,
      (∫ x in (Ω : Set 𝔼), ∑ i, partialDeriv u i x * partialDeriv φ i x)
        + ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn u x * SobolevMultiIndex.fn φ x
        = ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn φ x)
    {ũ : 𝔼 → ℝ} (hũ : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set 𝔼))) {K₁ K₂ : ℝ}
    (hΓ : ∀ x ∈ frontier (Ω : Set 𝔼), |ũ x| ≤ K₁)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), |f x| ≤ K₂) : ∀ x ∈ Ω, |ũ x| ≤ max K₁ K₂ :=
  Elliptic.abs_le_max_of_isWeakSolution ((forall_laplaceForm_eq_load_iff u f _).1 hu) hũ hc hΓ hf

/-- **Corollary 9.28** of [brezis2011functional], "in particular, if $f = 0$ in $\Omega$ then
$\|u\|_{L^\infty(\Omega)} \le \|u\|_{L^\infty(\Gamma)}$". Let $\Omega \subset \mathbb{R}^N$ be
open, and let $u \in H^1(\Omega) \cap C(\overline\Omega)$ satisfy (70) with $f = 0$. Let
$\tilde u$ be the representative of $u$ that is continuous on $\overline\Omega$. If $K \ge 0$
and $|\tilde u| \le K$ on $\Gamma$, then $|\tilde u| \le K$ on $\Omega$.

The proof is the backbone's `Elliptic.abs_le_of_load_eq_zero`.

**Reading.** The norm on the boundary is represented by a finite nonnegative pointwise bound. -/
theorem corollary_9_28_zero_load {u : hSpace N Ω}
    (hu : ∀ φ ∈ hZeroSpace N Ω,
      (∫ x in (Ω : Set 𝔼), ∑ i, partialDeriv u i x * partialDeriv φ i x)
        + ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn u x * SobolevMultiIndex.fn φ x
        = ∫ x in (Ω : Set 𝔼), (0 : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) x
          * SobolevMultiIndex.fn φ x)
    {ũ : 𝔼 → ℝ} (hũ : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set 𝔼))) {K : ℝ} (hK : 0 ≤ K)
    (hΓ : ∀ x ∈ frontier (Ω : Set 𝔼), |ũ x| ≤ K) : ∀ x ∈ Ω, |ũ x| ≤ K :=
  Elliptic.abs_le_of_load_eq_zero ((forall_laplaceForm_eq_load_iff u 0 _).1 hu) hũ hc hK hΓ

/-- **Corollary 9.28** of [brezis2011functional], "in particular, if $u = 0$ on $\Gamma$ then
$\|u\|_{L^\infty(\Omega)} \le \|f\|_{L^\infty(\Omega)}$". Let $\Omega \subset \mathbb{R}^N$ be
open, and let $f \in L^2(\Omega)$ and $u \in H^1(\Omega) \cap C(\overline\Omega)$ satisfy (70).
Let $\tilde u$ be the representative of $u$ that is continuous on $\overline\Omega$, with
$\tilde u = 0$ on $\Gamma$. If $K \ge 0$ and $|f| \le K$ almost everywhere on $\Omega$, then
$|\tilde u| \le K$ on $\Omega$.

The proof is the backbone's `Elliptic.abs_le_of_eqOn_zero_frontier`.

**Reading.** The forcing norm is represented by a finite nonnegative essential bound. -/
theorem corollary_9_28_zero_boundary {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))} {u : hSpace N Ω}
    (hu : ∀ φ ∈ hZeroSpace N Ω,
      (∫ x in (Ω : Set 𝔼), ∑ i, partialDeriv u i x * partialDeriv φ i x)
        + ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn u x * SobolevMultiIndex.fn φ x
        = ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn φ x)
    {ũ : 𝔼 → ℝ} (hũ : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set 𝔼))) (hΓ : EqOn ũ 0 (frontier (Ω : Set 𝔼))) {K : ℝ}
    (hK : 0 ≤ K) (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), |f x| ≤ K) : ∀ x ∈ Ω, |ũ x| ≤ K :=
  Elliptic.abs_le_of_eqOn_zero_frontier ((forall_laplaceForm_eq_load_iff u f _).1 hu) hũ hc hΓ hK
    hf

/-! ### Remark 27: the classical proof -/

/-- **Remark 27** of [brezis2011functional], the classical proof of Theorem 9.27 for the Laplacian.
Let $\Omega \subset \mathbb{R}^N$ be a bounded open set, let $f : \mathbb{R}^N \to \mathbb{R}$,
and let $u \in C(\overline\Omega) \cap C^2(\Omega)$ be a classical solution of
$$-\Delta u + u = f \quad \text{in } \Omega. \qquad (76)$$
Let $K \in \mathbb{R}$ with $f \le K$ in $\Omega$ and $u \le K$ on $\Gamma$. Then $u \le K$ in
$\Omega$.

The argument of the remark: let $x_0 \in \overline\Omega$ be a point where $u$ attains its
maximum on $\overline\Omega$. If $x_0 \in \Gamma$, then $u(x_0) \le K$. If $x_0 \in \Omega$,
then $\nabla u(x_0) = 0$ and $\frac{\partial^2 u}{\partial x_i^2}(x_0) \le 0$, so
$\Delta u(x_0) \le 0$ and $u(x_0) = f(x_0) + \Delta u(x_0) \le f(x_0) \le K$. The proof is the
backbone's `Elliptic.le_of_classical_laplacian` (with `IsLocalMax.laplacian_nonpos`). The class
$C^2(\Omega)$ is `ContDiffOn ℝ 2 u Ω`.

**Reading.** This classical argument states the upper inequality. The lower inequality
 follows by applying it to $-u$. -/
theorem remark_9_27 (hb : Bornology.IsBounded (Ω : Set 𝔼)) {u f : 𝔼 → ℝ}
    (hc : ContinuousOn u (closure (Ω : Set 𝔼))) (hu : ContDiffOn ℝ 2 u Ω)
    (heq : ∀ x ∈ Ω, -Δ u x + u x = f x) {K : ℝ} (hΓ : ∀ x ∈ frontier (Ω : Set 𝔼), u x ≤ K)
    (hf : ∀ x ∈ Ω, f x ≤ K) : ∀ x ∈ Ω, u x ≤ K :=
  Elliptic.le_of_classical_laplacian hb hc hu heq hΓ hf

/-- **Remark 27** of [brezis2011functional], the general operator: "this method has the advantage
that it applies to general second-order elliptic equations". Let $\Omega \subset \mathbb{R}^N$
be a bounded open set. Let $a_{ij} \in C^1(\Omega)$ for $1 \le i, j \le N$, with
$a_{ij} = a_{ji}$ and the ellipticity condition (36), and let
$a_i, f : \mathbb{R}^N \to \mathbb{R}$ be arbitrary. Let
$u \in C(\overline\Omega) \cap C^2(\Omega)$ satisfy
$$-\sum_{i,j} \frac{\partial}{\partial x_j}\Bigl(a_{ij} \frac{\partial u}{\partial x_i}\Bigr) +
  \sum_i a_i \frac{\partial u}{\partial x_i} + u = f \quad \text{in } \Omega. \qquad (77)$$
Let $K \in \mathbb{R}$ with $f \le K$ in $\Omega$ and $u \le K$ on $\Gamma$. Then $u \le K$ in
$\Omega$.

No continuity of the $a_i$ is needed, because the first-order term vanishes at a critical point.
At an interior maximum $x_0$, $\nabla u(x_0) = 0$ and $\sum_{i,j} a_{ij}(x_0) \partial_i
\partial_j u(x_0) \le 0$, so $u(x_0) = f(x_0) + \sum_{i,j} a_{ij}(x_0) \partial_i \partial_j
u(x_0) \le f(x_0) \le K$. The source proves the inequality by "a change of coordinates", which
reduces to the case of a diagonal matrix $(a_{ij}(x_0))$. The backbone's
`Elliptic.le_of_classical` uses the square root of $(a_{ij}(x_0))$ instead. The coefficients
$a_i$ are `b i`. The last sentence of the remark, the same for weak solutions of (77)
(Gilbarg–Trudinger), is not formalized.

**Reading.** This classical argument assumes the principal matrix is symmetric and gives
 the upper inequality. The source uses diagonalization at the extremum without writing a
 symmetry hypothesis in (77). -/
theorem remark_9_27_general (hb : Bornology.IsBounded (Ω : Set 𝔼)) {u f : 𝔼 → ℝ}
    (hc : ContinuousOn u (closure (Ω : Set 𝔼))) (hu : ContDiffOn ℝ 2 u Ω)
    {a : Fin N → Fin N → 𝔼 → ℝ} (ha : ∀ i j, ContDiffOn ℝ 1 (a i j) Ω)
    (hsymm : ∀ i j, a i j = a j i) {α : ℝ} (hell : ellipticityCondition Ω a α)
    {b : Fin N → 𝔼 → ℝ}
    (heq : ∀ x ∈ Ω, -(∑ i, ∑ j, fderiv ℝ (fun y ↦ a i j y * fderiv ℝ u y
        (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1))
      + (∑ i, b i x * fderiv ℝ u x (EuclideanSpace.single i 1)) + u x = f x)
    {K : ℝ} (hΓ : ∀ x ∈ frontier (Ω : Set 𝔼), u x ≤ K) (hf : ∀ x ∈ Ω, f x ≤ K) :
    ∀ x ∈ Ω, u x ≤ K :=
  Elliptic.le_of_classical hb hc hu (fun i j ↦ (ha i j).differentiableOn one_ne_zero) hsymm
    (fun x hx ξ ↦ (mul_nonneg hell.1.le (sq_nonneg _)).trans (hell.2 x hx ξ)) heq hΓ hf

/-! ### Proposition 9.29, the drift-free case -/

variable {A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))} {α : ℝ}

/-- **Proposition 9.29** of [brezis2011functional], (79), in the case $a_i \equiv 0$ that the source
proves. Let $N \ge 1$ and let $\Omega \subset \mathbb{R}^N$ be open. Let
$a_{ij} \in L^\infty(\Omega)$ satisfy the ellipticity condition (36) almost everywhere, and let
$a_0 \in L^\infty(\Omega)$ with $a_0 \ge 0$ almost everywhere in $\Omega$. Let
$f \in L^2(\Omega)$, and let $u \in H^1(\Omega) \cap C(\overline\Omega)$ satisfy
$$\int_\Omega \sum_{i,j} a_{ij} \frac{\partial u}{\partial x_i} \frac{\partial \varphi}{\partial
  x_j} + \int_\Omega a_0 u \varphi = \int_\Omega f \varphi \quad \text{for all } \varphi \in
  H_0^1(\Omega),$$
which is (78) with $a_i = 0$. Then
$$[u \ge 0 \text{ on } \Gamma \text{ and } f \ge 0 \text{ in } \Omega] \Rightarrow [u \ge 0
  \text{ in } \Omega].$$

**Reading.** The source leaves the hypothesis $N \ge 1$ implicit. The constancy argument of
footnote 39 needs it.

The ellipticity condition is `Elliptic.IsUniformlyElliptic`, and the conditions on $u$ hold at
every point for the representative $\tilde u$ of $u$ that is continuous on $\overline\Omega$.
The proof is the backbone's `Elliptic.nonneg_of_nonneg_frontier_general_zero_drift`. As in the
proof of (79') in the source, it tests (78) with $\varphi = G(u)$, uses the ellipticity to get
$\int |\nabla u|^2 G'(u) \le 0$, and concludes with the auxiliary function
$H(t) = \int_0^t \sqrt{G'}$ and footnote 39
(`SobolevMultiIndexZero.eq_zero_of_gradient_eq_zero`: a function in $W_0^{1,p}$ with zero
gradient vanishes, by Proposition 9.18 and Remark 7). -/
theorem proposition_9_29_zero_drift (hN : N ≠ 0) (hA : Elliptic.IsUniformlyElliptic Ω A α)
    (ha₀ : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), 0 ≤ a₀ x)
    {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))} {u : hSpace N Ω}
    (hu : ∀ φ ∈ hZeroSpace N Ω,
      (∫ x in (Ω : Set 𝔼), ∑ i, ∑ j, A i j x * partialDeriv u i x * partialDeriv φ j x)
        + ∫ x in (Ω : Set 𝔼), a₀ x * SobolevMultiIndex.fn u x * SobolevMultiIndex.fn φ x
        = ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn φ x)
    {ũ : 𝔼 → ℝ} (hũ : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set 𝔼))) (hΓ : ∀ x ∈ frontier (Ω : Set 𝔼), 0 ≤ ũ x)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), 0 ≤ f x) : ∀ x ∈ Ω, 0 ≤ ũ x :=
  Elliptic.nonneg_of_nonneg_frontier_general_zero_drift hN hA ha₀
    ((forall_generalForm_zero_drift_eq_load_iff A a₀ u f).1 hu) hũ hc hΓ hf

/-- **Proposition 9.29** of [brezis2011functional], (79), footnote 38: for $u \in H_0^1(\Omega)$ the
assumption $u \in C(\overline\Omega)$ can be removed, in the case $a_i \equiv 0$. Let $N \ge 1$,
let $\Omega \subset \mathbb{R}^N$ be open, let $a_{ij} \in L^\infty(\Omega)$ satisfy the
ellipticity condition (36) almost everywhere, and let $a_0 \in L^\infty(\Omega)$ with
$a_0 \ge 0$ almost everywhere. Let $f \in L^2(\Omega)$ and let $u \in H_0^1(\Omega)$ satisfy
(78) with $a_i = 0$. If $f \ge 0$ almost everywhere in $\Omega$, then $u \ge 0$ almost
everywhere in $\Omega$.

**Reading.** As in `Brezis.Chapter09.proposition_9_29_zero_drift`, the hypothesis $N \ge 1$ is
stated.

The proof is the backbone's `Elliptic.nonneg_of_mem_zero_general_zero_drift`. -/
theorem proposition_9_29_zero_drift_of_mem_zero (hN : N ≠ 0)
    (hA : Elliptic.IsUniformlyElliptic Ω A α)
    (ha₀ : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), 0 ≤ a₀ x)
    {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))} {u : hSpace N Ω} (hu0 : u ∈ hZeroSpace N Ω)
    (hu : ∀ φ ∈ hZeroSpace N Ω,
      (∫ x in (Ω : Set 𝔼), ∑ i, ∑ j, A i j x * partialDeriv u i x * partialDeriv φ j x)
        + ∫ x in (Ω : Set 𝔼), a₀ x * SobolevMultiIndex.fn u x * SobolevMultiIndex.fn φ x
        = ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn φ x)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), 0 ≤ f x) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), 0 ≤ SobolevMultiIndex.fn u x :=
  Elliptic.nonneg_of_mem_zero_general_zero_drift hN hA ha₀ hu0
    ((forall_generalForm_zero_drift_eq_load_iff A a₀ u f).1 hu) hf

/-- **Proposition 9.29** of [brezis2011functional], (80), in the case $a_i \equiv 0$. Let $N \ge 1$,
let $\Omega \subset \mathbb{R}^N$ be a bounded open set, and let $a_{ij} \in L^\infty(\Omega)$
satisfy the ellipticity condition (36) almost everywhere. Let $f \in L^2(\Omega)$ and let
$u \in H^1(\Omega) \cap C(\overline\Omega)$ satisfy (78) with $a_i = 0$ and $a_0 = 0$. Then
$$[f \ge 0 \text{ in } \Omega] \Rightarrow \Bigl[u \ge \inf_\Gamma u \text{ in } \Omega\Bigr].$$
Precisely, let $\tilde u$ be the representative of $u$ that is continuous on $\overline\Omega$.
If $K \le \tilde u$ on $\Gamma$ and $f \ge 0$ almost everywhere, then $K \le \tilde u$ on
$\Omega$.

**Reading.** As in `Brezis.Chapter09.proposition_9_29_zero_drift`, the hypothesis $N \ge 1$ is
stated.

The proof is the backbone's `Elliptic.ge_of_ge_frontier_general_zero_drift`: it applies (79) to
$u - K$, which satisfies (78) because $a_0 = 0$ and the constant $K$ lies in $H^1(\Omega)$ for a
bounded $\Omega$.

**Reading.** The conclusion uses an arbitrary finite pointwise lower bound on the boundary. -/
theorem proposition_9_29_inf_zero_drift (hN : N ≠ 0) (hA : Elliptic.IsUniformlyElliptic Ω A α)
    (hb : Bornology.IsBounded (Ω : Set 𝔼)) {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))}
    {u : hSpace N Ω}
    (hu : ∀ φ ∈ hZeroSpace N Ω,
      (∫ x in (Ω : Set 𝔼), ∑ i, ∑ j, A i j x * partialDeriv u i x * partialDeriv φ j x)
        + ∫ x in (Ω : Set 𝔼), (0 : Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼))) x
          * SobolevMultiIndex.fn u x * SobolevMultiIndex.fn φ x
        = ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn φ x)
    {ũ : 𝔼 → ℝ} (hũ : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set 𝔼))) {K : ℝ} (hΓ : ∀ x ∈ frontier (Ω : Set 𝔼), K ≤ ũ x)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), 0 ≤ f x) : ∀ x ∈ Ω, K ≤ ũ x :=
  Elliptic.ge_of_ge_frontier_general_zero_drift hN hA hb.measure_lt_top.ne
    ((forall_generalForm_zero_drift_eq_load_iff A 0 u f).1 hu) hũ hc hΓ hf

/-- **Proposition 9.29** of [brezis2011functional], (81), in the case $a_i \equiv 0$. Let $N \ge 1$,
let $\Omega \subset \mathbb{R}^N$ be a bounded open set, and let $a_{ij} \in L^\infty(\Omega)$
satisfy the ellipticity condition (36) almost everywhere. Let
$u \in H^1(\Omega) \cap C(\overline\Omega)$ satisfy (78) with $a_i = 0$, $a_0 = 0$ and $f = 0$.
Then
$$\inf_\Gamma u \le u \le \sup_\Gamma u \quad \text{in } \Omega.$$
Precisely, let $\tilde u$ be the representative of $u$ that is continuous on $\overline\Omega$.
If $K_1 \le \tilde u \le K_2$ on $\Gamma$, then $K_1 \le \tilde u \le K_2$ on $\Omega$.

**Reading.** As in `Brezis.Chapter09.proposition_9_29_zero_drift`, the hypothesis $N \ge 1$ is
stated.

This is (80) for $u$ and for $-u$. The proof is the backbone's
`Elliptic.mem_Icc_of_frontier_general_zero_drift`.

**Typo.** In (81) the source omits $u$ between the boundary infimum and supremum. -/
theorem proposition_9_29_sup_inf_zero_drift (hN : N ≠ 0) (hA : Elliptic.IsUniformlyElliptic Ω A α)
    (hb : Bornology.IsBounded (Ω : Set 𝔼)) {u : hSpace N Ω}
    (hu : ∀ φ ∈ hZeroSpace N Ω,
      (∫ x in (Ω : Set 𝔼), ∑ i, ∑ j, A i j x * partialDeriv u i x * partialDeriv φ j x)
        + ∫ x in (Ω : Set 𝔼), (0 : Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼))) x
          * SobolevMultiIndex.fn u x * SobolevMultiIndex.fn φ x
        = ∫ x in (Ω : Set 𝔼), (0 : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) x
          * SobolevMultiIndex.fn φ x)
    {ũ : 𝔼 → ℝ} (hũ : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set 𝔼))) {K₁ K₂ : ℝ}
    (hΓ : ∀ x ∈ frontier (Ω : Set 𝔼), K₁ ≤ ũ x ∧ ũ x ≤ K₂) :
    ∀ x ∈ Ω, K₁ ≤ ũ x ∧ ũ x ≤ K₂ :=
  Elliptic.mem_Icc_of_frontier_general_zero_drift hN hA hb.measure_lt_top.ne
    ((forall_generalForm_zero_drift_eq_load_iff A 0 u 0).1 hu) hũ hc hΓ

/-! ### Proposition 9.29 with a first-order term, for $N \ge 3$ -/

variable {a₁ : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-- Let $\Omega \subset \mathbb{R}^N$ be open, let $a_{ij}, a_i, a_0 \in L^\infty(\Omega)$, let
$u \in H^1(\Omega)$ and let $f \in L^2(\Omega)$. Then $u$ satisfies the weak equation (78),
$$\int_\Omega \sum_{i,j} a_{ij} \frac{\partial u}{\partial x_i} \frac{\partial \varphi}{\partial
  x_j} + \int_\Omega \sum_i a_i \frac{\partial u}{\partial x_i} \varphi + \int_\Omega a_0 u
  \varphi = \int_\Omega f \varphi \quad \text{for all } \varphi \in H_0^1(\Omega),$$
if and only if $a(u, \varphi) = \int_\Omega f \varphi$ for all $\varphi \in H_0^1(\Omega)$,
where $a$ is `Elliptic.generalForm Ω A a₁ a₀` and the right-hand side is `Elliptic.load Ω f`.

The proof uses the backbone's `Elliptic.generalForm_apply_three`. -/
theorem forall_generalForm_eq_load_iff
    (A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼)))
    (a₁ : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼)))
    (a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼))) (u : hSpace N Ω)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) :
    (∀ φ ∈ hZeroSpace N Ω,
        (∫ x in (Ω : Set 𝔼), ∑ i, ∑ j, A i j x * partialDeriv u i x * partialDeriv φ j x)
          + (∫ x in (Ω : Set 𝔼), ∑ i, a₁ i x * partialDeriv u i x * SobolevMultiIndex.fn φ x)
          + ∫ x in (Ω : Set 𝔼), a₀ x * SobolevMultiIndex.fn u x * SobolevMultiIndex.fn φ x
          = ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn φ x) ↔
      ∀ φ ∈ hZeroSpace N Ω, Elliptic.generalForm Ω A a₁ a₀ u φ = Elliptic.load Ω f φ := by
  simp only [generalForm_apply_three, Elliptic.load_apply]

/-- **Proposition 9.29** of [brezis2011functional], (79), with a first-order term. Let $N \ge 3$ and
let $\Omega \subset \mathbb{R}^N$ be open. Let $a_{ij} \in L^\infty(\Omega)$ satisfy the
ellipticity condition (36) almost everywhere, and let $a_i, a_0 \in L^\infty(\Omega)$ with
$a_0 \ge 0$ almost everywhere in $\Omega$. Let $f \in L^2(\Omega)$ and let
$u \in H^1(\Omega) \cap C(\overline\Omega)$ satisfy (78). Then
$$[u \ge 0 \text{ on } \Gamma \text{ and } f \ge 0 \text{ in } \Omega] \Rightarrow [u \ge 0
  \text{ in } \Omega].$$

The source states the proposition for every $N$; the case $N \le 2$ with a first-order term is
not formalized. The source proves only the case $a_i \equiv 0$
(`Brezis.Chapter09.proposition_9_29_zero_drift`) and refers to Gilbarg–Trudinger, Theorem 8.1,
for the general case. The backbone's `Elliptic.nonneg_of_nonneg_frontier_general` follows that
proof: it tests (78) with the truncation $(u - l)^+$ and uses the Sobolev inequality of Remark
20 on $W_0^{1,2}(\Omega)$, hence the hypothesis $N \ge 3$. The coefficients $a_i$ are `a₁ i`.

**Reading.** This statement treats the first-order term in dimension $N \ge 3$. -/
theorem proposition_9_29 (hN : 3 ≤ N) (hA : Elliptic.IsUniformlyElliptic Ω A α)
    (ha₀ : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), 0 ≤ a₀ x)
    {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))} {u : hSpace N Ω}
    (hu : ∀ φ ∈ hZeroSpace N Ω,
      (∫ x in (Ω : Set 𝔼), ∑ i, ∑ j, A i j x * partialDeriv u i x * partialDeriv φ j x)
        + (∫ x in (Ω : Set 𝔼), ∑ i, a₁ i x * partialDeriv u i x * SobolevMultiIndex.fn φ x)
        + ∫ x in (Ω : Set 𝔼), a₀ x * SobolevMultiIndex.fn u x * SobolevMultiIndex.fn φ x
        = ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn φ x)
    {ũ : 𝔼 → ℝ} (hũ : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set 𝔼))) (hΓ : ∀ x ∈ frontier (Ω : Set 𝔼), 0 ≤ ũ x)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), 0 ≤ f x) : ∀ x ∈ Ω, 0 ≤ ũ x :=
  Elliptic.nonneg_of_nonneg_frontier_general hN hA ha₀
    ((forall_generalForm_eq_load_iff A a₁ a₀ u f).1 hu) hũ hc hΓ hf

/-- **Proposition 9.29** of [brezis2011functional], (80), with a first-order term. Let $N \ge 3$,
let $\Omega \subset \mathbb{R}^N$ be a bounded open set, let $a_{ij} \in L^\infty(\Omega)$
satisfy the ellipticity condition (36) almost everywhere, and let $a_i \in L^\infty(\Omega)$.
Let $f \in L^2(\Omega)$ and let $u \in H^1(\Omega) \cap C(\overline\Omega)$ satisfy (78) with
$a_0 = 0$. Then
$$[f \ge 0 \text{ in } \Omega] \Rightarrow \Bigl[u \ge \inf_\Gamma u \text{ in } \Omega\Bigr].$$
Precisely, let $\tilde u$ be the representative of $u$ that is continuous on $\overline\Omega$.
If $K \le \tilde u$ on $\Gamma$ and $f \ge 0$ almost everywhere, then $K \le \tilde u$ on
$\Omega$.

As in `Brezis.Chapter09.proposition_9_29`, the case $N \le 2$ is not formalized. The proof is
the backbone's `Elliptic.ge_iInf_frontier_of_nonneg`: it applies (79) to $u - K$, which
satisfies (78) because $a_0 = 0$ and the constant $K$ lies in $H^1(\Omega)$ for a bounded
$\Omega$.

**Reading.** This statement uses a pointwise lower bound on the boundary and assumes
 $N \ge 3$ when the first-order term is present. -/
theorem proposition_9_29_inf (hN : 3 ≤ N) (hA : Elliptic.IsUniformlyElliptic Ω A α)
    (hb : Bornology.IsBounded (Ω : Set 𝔼)) {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))}
    {u : hSpace N Ω}
    (hu : ∀ φ ∈ hZeroSpace N Ω,
      (∫ x in (Ω : Set 𝔼), ∑ i, ∑ j, A i j x * partialDeriv u i x * partialDeriv φ j x)
        + (∫ x in (Ω : Set 𝔼), ∑ i, a₁ i x * partialDeriv u i x * SobolevMultiIndex.fn φ x)
        + ∫ x in (Ω : Set 𝔼), (0 : Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼))) x
          * SobolevMultiIndex.fn u x * SobolevMultiIndex.fn φ x
        = ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn φ x)
    {ũ : 𝔼 → ℝ} (hũ : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set 𝔼))) {K : ℝ} (hΓ : ∀ x ∈ frontier (Ω : Set 𝔼), K ≤ ũ x)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), 0 ≤ f x) : ∀ x ∈ Ω, K ≤ ũ x :=
  Elliptic.ge_iInf_frontier_of_nonneg hN hA hb.measure_lt_top.ne
    ((forall_generalForm_eq_load_iff A a₁ 0 u f).1 hu) hũ hc hΓ hf

/-- **Proposition 9.29** of [brezis2011functional], (81), with a first-order term. Let $N \ge 3$,
let $\Omega \subset \mathbb{R}^N$ be a bounded open set, let $a_{ij} \in L^\infty(\Omega)$
satisfy the ellipticity condition (36) almost everywhere, and let $a_i \in L^\infty(\Omega)$.
Let $u \in H^1(\Omega) \cap C(\overline\Omega)$ satisfy (78) with $a_0 = 0$ and $f = 0$. Then
$$\inf_\Gamma u \le u \le \sup_\Gamma u \quad \text{in } \Omega.$$
Precisely, let $\tilde u$ be the representative of $u$ that is continuous on $\overline\Omega$.
If $K_1 \le \tilde u \le K_2$ on $\Gamma$, then $K_1 \le \tilde u \le K_2$ on $\Omega$.

As in `Brezis.Chapter09.proposition_9_29`, the case $N \le 2$ is not formalized. This is (80)
for $u$ and for $-u$. The proof is the backbone's `Elliptic.mem_Icc_of_frontier_general`.

**Typo.** In (81) the source omits $u$ between the two boundary bounds.

**Reading.** The first-order term is treated in dimension $N \ge 3$. -/
theorem proposition_9_29_sup_inf (hN : 3 ≤ N) (hA : Elliptic.IsUniformlyElliptic Ω A α)
    (hb : Bornology.IsBounded (Ω : Set 𝔼)) {u : hSpace N Ω}
    (hu : ∀ φ ∈ hZeroSpace N Ω,
      (∫ x in (Ω : Set 𝔼), ∑ i, ∑ j, A i j x * partialDeriv u i x * partialDeriv φ j x)
        + (∫ x in (Ω : Set 𝔼), ∑ i, a₁ i x * partialDeriv u i x * SobolevMultiIndex.fn φ x)
        + ∫ x in (Ω : Set 𝔼), (0 : Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼))) x
          * SobolevMultiIndex.fn u x * SobolevMultiIndex.fn φ x
        = ∫ x in (Ω : Set 𝔼), (0 : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) x
          * SobolevMultiIndex.fn φ x)
    {ũ : 𝔼 → ℝ} (hũ : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set 𝔼))) {K₁ K₂ : ℝ}
    (hΓ : ∀ x ∈ frontier (Ω : Set 𝔼), K₁ ≤ ũ x ∧ ũ x ≤ K₂) :
    ∀ x ∈ Ω, K₁ ≤ ũ x ∧ ũ x ≤ K₂ :=
  Elliptic.mem_Icc_of_frontier_general hN hA hb.measure_lt_top.ne
    ((forall_generalForm_eq_load_iff A a₁ 0 u 0).1 hu) hũ hc hΓ

/-! ### Proposition 9.30 -/

/-- **Proposition 9.30** of [brezis2011functional] (maximum principle for the Neumann problem). Let
$\Omega \subset \mathbb{R}^N$ be open, and let $f \in L^2(\Omega)$ and $u \in H^1(\Omega)$
satisfy
$$\int_\Omega \nabla u \cdot \nabla \varphi + \int_\Omega u \varphi = \int_\Omega f \varphi
  \quad \text{for all } \varphi \in H^1(\Omega).$$
Then
$$\inf_\Omega f \le u \le \sup_\Omega f \quad \text{almost everywhere in } \Omega.$$
Precisely, if $K_1 \le f \le K_2$ almost everywhere on $\Omega$, then $K_1 \le u \le K_2$ almost
everywhere on $\Omega$.

The proof is the backbone's `Elliptic.le_of_neumann` and `Elliptic.ge_of_neumann`: the
truncation method with the test space $H^1(\Omega)$, "analogous to the proof of Theorem 9.27".

**Reading.** The source gives separate inequalities against the possibly infinite essential
 extrema. The statement uses a pair of finite essential bounds and therefore applies to
 essentially bounded data. -/
theorem proposition_9_30 {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))} {u : hSpace N Ω}
    (hu : ∀ φ : hSpace N Ω,
      (∫ x in (Ω : Set 𝔼), ∑ i, partialDeriv u i x * partialDeriv φ i x)
        + ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn u x * SobolevMultiIndex.fn φ x
        = ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn φ x)
    {K₁ K₂ : ℝ} (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), K₁ ≤ f x ∧ f x ≤ K₂) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)),
      K₁ ≤ SobolevMultiIndex.fn u x ∧ SobolevMultiIndex.fn u x ≤ K₂ := by
  have heq := (forall_laplaceForm_eq_load_iff u f ⊤).1 fun φ _ ↦ hu φ
  have h1 := Elliptic.ge_of_neumann (fun φ ↦ heq φ Submodule.mem_top) (hf.mono fun x hx ↦ hx.1)
  have h2 := Elliptic.le_of_neumann (fun φ ↦ heq φ Submodule.mem_top) (hf.mono fun x hx ↦ hx.2)
  filter_upwards [h1, h2] with x hx1 hx2
  exact ⟨hx1, hx2⟩

end MaximumPrinciple

end Brezis.Chapter09
