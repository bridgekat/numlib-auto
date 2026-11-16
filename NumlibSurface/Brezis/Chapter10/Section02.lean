/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.PDE.Heat.MaximumPrinciple
import NumlibSurface.Brezis.Chapter10.Section01

/-!
# Brezis, Section 10.2: The maximum principle

This module formalizes Section 10.2 of [brezis2011functional], the maximum principle for the heat
equation $\partial_t u - \Delta u = 0$ of Section 10.1. Theorem 10.3 states that the solution $u$
with initial datum $u_0 \in L^2(\Omega)$ satisfies $\min\{0, \inf_\Omega u_0\} \le u \le \max\{0,
\sup_\Omega u_0\}$ in $Q = \Omega \times (0, \infty)$. The proof uses Stampacchia's truncation
method in time. Corollary 10.4 gives positivity and the $L^\infty$ contraction $\|u\|_{L^\infty(Q)}
\le \|u_0\|_{L^\infty(\Omega)}$, and Corollary 10.5 gives continuity on $\overline{Q}$ for
continuous data that vanish on $\Gamma$. Theorem 10.6 is the classical maximum principle: a function
$u(x, t)$ of class $C^1$ in $t$ and $C^2$ in $x$ with $\partial_t u - \Delta u \le 0$ on a bounded
cylinder attains its maximum on the parabolic boundary $P = (\overline{\Omega} \times \{0\}) \cup
(\Gamma \times [0, T])$.

The proofs specialize the backbone modules `Numlib.Analysis.PDE.Heat.MaximumPrinciple` (Theorem 10.3
and Corollary 10.4, on every open set) and `Numlib.Analysis.PDE.Heat.Classical` (Theorem 10.6).

## Main definitions

* Theorem 10.6, the parabolic boundary, `Brezis.Chapter10.parabolicBoundary`: $P =
  (\overline{\Omega} \times \{0\}) \cup (\Gamma \times [0, T])$.
* Theorem 10.6, the hypotheses (20), (21), (22), `Brezis.Chapter10.IsHeatSubsolution`:
  $u \in C(\overline{\Omega} \times [0, T])$, of class $C^1$ in $t$ and $C^2$ in $x$ in
  $\Omega \times (0, T)$, with $\partial_t u - \Delta u \le 0$ there.

## Main results

* Theorem 10.3, `Brezis.Chapter10.theorem_10_3`: a bound $-K \le u_0 \le K$ with $K \ge 0$ almost
  everywhere passes to $u(t)$ for every $t \ge 0$.
* Theorem 10.3, `Brezis.Chapter10.theorem_10_3_essSup`: $\min\{0, \operatorname{ess\,inf} u_0\} \le
  u(t) \le \max\{0, \operatorname{ess\,sup} u_0\}$ almost everywhere, for an essentially bounded
  datum.
* Theorem 10.3, `Brezis.Chapter10.theorem_10_3_pointwise`: the same bounds at every point
  $(x, t) \in Q$ for a smooth representative of $u$.
* Corollary 10.4(i), `Brezis.Chapter10.corollary_10_4_i`: if $u_0 \ge 0$, then $u \ge 0$.
* Corollary 10.4(ii), `Brezis.Chapter10.corollary_10_4_ii`: if $u_0 \in L^\infty(\Omega)$, then
  $\|u(t)\|_{L^\infty(\Omega)} \le \|u_0\|_{L^\infty(\Omega)}$ for every $t \ge 0$.
* Corollary 10.5, `Brezis.Chapter10.corollary_10_5`: for
  $u_0 \in C(\overline{\Omega}) \cap L^2(\Omega)$ with $u_0 = 0$ on $\Gamma$ and $u_0 \to 0$ at
  infinity, $u \in C(\overline{Q})$.
* Corollary 10.5, `Brezis.Chapter10.corollary_10_5_of_isBounded`: the same for bounded $\Omega$,
  without the condition at infinity.
* Theorem 10.6, `Brezis.Chapter10.theorem_10_6`: on a bounded nonempty $\Omega$, the maximum of $u$
  over $\overline{\Omega} \times [0, T]$ is attained on $P$.
* Theorem 10.6, `Brezis.Chapter10.theorem_10_6_le`: a bound $u \le M$ on $P$ holds on
  $\overline{\Omega} \times [0, T]$.

## Conventions

* Theorem 10.3 and Corollary 10.4 are stated for a solution $u$ of (1), (2), (3) in the class (4) of
  Section 10.1 (`Brezis.Chapter10.IsHeatSolution`). Their proofs hold on every open set, without the
  standing regularity hypothesis of the chapter.
* Theorem 10.6 is classical: $u$ is a function `𝔼 × ℝ → ℝ` of $(x, t)$, and the Laplacian in $x$ is
  Mathlib's $\Delta$ (`InnerProductSpace.laplacian`).

## Implementation notes

* In Corollary 10.5 the datum $u_0 \in C(\overline{\Omega}) \cap L^2(\Omega)$ with $u_0 = 0$ on
  $\Gamma$ is an $L^2$ datum that agrees almost everywhere with a function $f$ continuous on
  $\overline{\Omega}$ and zero on $\Gamma$. By footnote 6 it tends to $0$ at infinity along
  $\Omega$, `Tendsto f (cocompact ⊓ 𝓟 Ω) (𝓝 0)`, a condition that is void for bounded $\Omega$. The
  conclusion $u \in C(\overline{Q})$ is a function $U$ continuous on
  $\overline{\Omega} \times [0, \infty)$ with $U(\cdot, t) = u(t)$ almost everywhere for every
  $t \ge 0$ and $U(\cdot, 0) = f$ on $\overline{\Omega}$.
* The backbone theorem `Heat.IsSolution.continuousOn_spaceTime` for Corollary 10.5 needs only a
  domain of class $C^{2\ell}$ with $N/2 < 2\ell$. The surface keeps the $C^\infty$ hypothesis of the
  chapter.

## Deviations from the source

* **Theorem 10.3** (reading). The source states the bounds "for all $(x, t) \in Q$" for an
  $L^2$-valued solution, with $\sup_\Omega u_0$ and $\inf_\Omega u_0$. The library reads them almost
  everywhere in $x$ for each $t \ge 0$, for every essential bound $K \ge 0$, and everywhere for a
  continuous representative. See `Brezis.Chapter10.theorem_10_3`,
  `Brezis.Chapter10.theorem_10_3_essSup` and `Brezis.Chapter10.theorem_10_3_pointwise`.
* **Corollary 10.4(ii)** (reading). The source states $\|u\|_{L^\infty(Q)} \le
  \|u_0\|_{L^\infty(\Omega)}$. The library states $\|u(t)\|_{L^\infty(\Omega)} \le
  \|u_0\|_{L^\infty(\Omega)}$ for every $t \ge 0$, because no jointly measurable representative of
  the curve is built. See `Brezis.Chapter10.corollary_10_4_ii`.
* **Theorem 10.6** (reading). The source leaves $\Omega \neq \emptyset$ implicit; for
  $\Omega = \emptyset$ there is no maximum. The library assumes it for the attained maximum and
  states the bound form without it. See `Brezis.Chapter10.theorem_10_6` and
  `Brezis.Chapter10.theorem_10_6_le`.
-/

open Filter MeasureTheory Metric Set Topology TopologicalSpace Laplacian
open scoped ContDiff Distributions ENNReal NNReal InnerProductSpace

namespace Brezis.Chapter10

open Brezis.Chapter07 Brezis.Chapter09 SobolevMultiIndex

section General

variable {N : ℕ}

/-- The space $\mathbb{R}^N$ of the source. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

variable {Ω : Opens (EuclideanSpace ℝ (Fin N))}
  {u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-! ### Theorem 10.3 -/

/-- **Theorem 10.3** of [brezis2011functional] (the maximum principle). Let
$\Omega \subset \mathbb{R}^N$ be open, let $u_0 \in L^2(\Omega)$, and let $u$ be the solution of
(1), (2), (3) in the class (4). Let $K \ge 0$. Then

* if $u_0 \le K$ almost everywhere on $\Omega$, then $u(t) \le K$ almost everywhere on $\Omega$
  for every $t \ge 0$, and
* if $-K \le u_0$ almost everywhere on $\Omega$, then $-K \le u(t)$ almost everywhere on
  $\Omega$ for every $t \ge 0$.

**Reading.** The source states $\min\{0, \inf_\Omega u_0\} \le u(x, t) \le \max\{0, \sup_\Omega
u_0\}$ for all $(x, t) \in Q$. For an $L^2$-valued solution the statement is read almost
everywhere in $x$ for each $t \ge 0$, and the bounds of the source are read as essential bounds.
The bound $\max\{0, \sup_\Omega u_0\}$ is the least admissible $K$, and the statement is empty
when $\sup_\Omega u_0 = +\infty$. The form with `essSup` and `essInf` is
`Brezis.Chapter10.theorem_10_3_essSup`, and the pointwise form is
`Brezis.Chapter10.theorem_10_3_pointwise`.

The proof is Stampacchia's truncation method in time. With $K = \max\{0, \sup u_0\}$,
$H(s) = \int_0^s G$ and $\varphi(t) = \int_\Omega H(u(x, t) - K) \, dx$, one has
$\varphi \in C([0, \infty))$, $\varphi(0) = 0$, $\varphi \ge 0$, $\varphi \in C^1((0, \infty))$
and
$$\varphi' = \int_\Omega G(u - K) \partial_t u = \int_\Omega G(u - K) \Delta u = -\int_\Omega
  G'(u - K) |\nabla u|^2 \le 0,$$
since $G(u(t) - K) \in H^1_0(\Omega)$. So $\varphi \equiv 0$. The proof specializes
`Heat.IsSolution.le_of_le` and `Heat.IsSolution.ge_of_ge`, on every open set. -/
theorem theorem_10_3 (hu : IsHeatSolution Ω u₀ u) {K : ℝ} (hK : 0 ≤ K) :
    ((∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), u₀ x ≤ K) →
      ∀ t, 0 ≤ t → ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), u t x ≤ K) ∧
    ((∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), -K ≤ u₀ x) →
      ∀ t, 0 ≤ t → ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), -K ≤ u t x) :=
  ⟨fun hu₀ _ ht ↦ hu.isSolution.le_of_le hK hu₀ ht, fun hu₀ _ ht ↦ hu.isSolution.ge_of_ge hK hu₀ ht⟩

/-- **Theorem 10.3** of [brezis2011functional], with the bounds of the source. Let
$\Omega \subset \mathbb{R}^N$ be open, let $u_0 \in L^2(\Omega)$ be essentially bounded above
and below on $\Omega$, and let $u$ be the solution of (1), (2), (3) in the class (4). Then for
every $t \ge 0$,
$$\min\{0, \operatorname{ess\,inf}_\Omega u_0\} \le u(t) \le \max\{0,
  \operatorname{ess\,sup}_\Omega u_0\} \qquad \text{almost everywhere on } \Omega.$$

**Reading.** The source writes $\inf_\Omega u_0$ and $\sup_\Omega u_0$ for an $L^2$ datum. They
are read as the essential infimum and supremum. -/
theorem theorem_10_3_essSup (hu : IsHeatSolution Ω u₀ u)
    (hb : IsBoundedUnder (· ≤ ·) (ae (volume.restrict (Ω : Set 𝔼))) u₀)
    (hb' : IsBoundedUnder (· ≥ ·) (ae (volume.restrict (Ω : Set 𝔼))) u₀) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)),
      min 0 (essInf u₀ (volume.restrict (Ω : Set 𝔼))) ≤ u t x ∧
        u t x ≤ max 0 (essSup u₀ (volume.restrict (Ω : Set 𝔼))) := by
  have h1 := (theorem_10_3 hu (le_max_left 0 (essSup u₀ _))).1
    ((ae_le_essSup hb).mono fun x hx ↦ hx.trans (le_max_right _ _)) t ht
  have h2 := (theorem_10_3 hu (K := -min 0 (essInf u₀ (volume.restrict (Ω : Set 𝔼))))
    (by simp)).2
    ((ae_essInf_le hb').mono fun x hx ↦ by rw [neg_neg]; exact (min_le_right _ _).trans hx) t ht
  filter_upwards [h1, h2] with x hx1 hx2
  exact ⟨by simpa using hx2, hx1⟩

/-- **Theorem 10.3** of [brezis2011functional], "for all $(x, t) \in Q$". Let
$\Omega \subset \mathbb{R}^N$ be open, let $u_0 \in L^2(\Omega)$, and let $u$ be the solution of
(1), (2), (3) in the class (4). Let $U : \mathbb{R}^N \times \mathbb{R} \to \mathbb{R}$ satisfy
$U(\cdot, t) = u(t)$ almost everywhere on $\Omega$ for every $t > 0$ and $U \in
C^\infty(\overline{\Omega} \times [\varepsilon, \infty))$ for every $\varepsilon > 0$, and let
$K \ge 0$. Then

* if $u_0 \le K$ almost everywhere on $\Omega$, then $U(x, t) \le K$ for all $x \in \Omega$ and
  $t > 0$, and
* if $-K \le u_0$ almost everywhere on $\Omega$, then $-K \le U(x, t)$ for all $x \in \Omega$
  and $t > 0$.

The representative $U$ of the smoothing (5) of Theorem 10.1
(`Brezis.Chapter10.theorem_10_1_smooth`) satisfies the hypotheses; the class
$C^\infty(\overline{\Omega} \times [\varepsilon, \infty))$ is `ContDiffOnClosure`. An
almost-everywhere bound on an open set for a continuous function holds everywhere:
$\max(U(\cdot, t), K)$ is continuous on $\Omega$ and almost everywhere equal to the constant $K$
(`MeasureTheory.Measure.eqOn_open_of_ae_eq`). -/
theorem theorem_10_3_pointwise (hu : IsHeatSolution Ω u₀ u) {U : 𝔼 × ℝ → ℝ}
    (hU : ∀ t, 0 < t → (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set 𝔼)] u t)
    (hUs : ∀ ε > 0, ContDiffOnClosure ℝ ∞ U ((Ω : Set 𝔼) ×ˢ Ioi ε)) {K : ℝ} (hK : 0 ≤ K) :
    ((∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), u₀ x ≤ K) →
      ∀ t, 0 < t → ∀ x ∈ Ω, U (x, t) ≤ K) ∧
    ((∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), -K ≤ u₀ x) →
      ∀ t, 0 < t → ∀ x ∈ Ω, -K ≤ U (x, t)) := by
  -- the slices `U(·, t)`, `t > 0`, are continuous on `Ω`
  have hc : ∀ t, 0 < t → ContinuousOn (fun x ↦ U (x, t)) Ω := fun t ht ↦
    ((hUs (t / 2) (by positivity)).contDiffOn.continuousOn.comp
      (continuousOn_id.prodMk continuousOn_const) fun x hx ↦
        (⟨hx, by simp only [mem_Ioi]; linarith⟩ : (x, t) ∈ (Ω : Set 𝔼) ×ˢ Ioi (t / 2)))
  refine ⟨fun hu₀ t ht x hx ↦ ?_, fun hu₀ t ht x hx ↦ ?_⟩
  · have hae : (fun x ↦ max (U (x, t)) K) =ᵐ[volume.restrict (Ω : Set 𝔼)] fun _ ↦ K := by
      filter_upwards [(theorem_10_3 hu hK).1 hu₀ t ht.le, hU t ht] with x hx hx'
      simp only [hx', max_eq_right hx]
    have := Measure.eqOn_open_of_ae_eq hae Ω.isOpen (ContinuousOn.sup (hc t ht) continuousOn_const)
      continuousOn_const hx
    simpa only [max_eq_right_iff] using this
  · have hae : (fun x ↦ min (U (x, t)) (-K)) =ᵐ[volume.restrict (Ω : Set 𝔼)] fun _ ↦ -K := by
      filter_upwards [(theorem_10_3 hu hK).2 hu₀ t ht.le, hU t ht] with x hx hx'
      simp only [hx', min_eq_right hx]
    have := Measure.eqOn_open_of_ae_eq hae Ω.isOpen (ContinuousOn.inf (hc t ht) continuousOn_const)
      continuousOn_const hx
    simpa only [min_eq_right_iff] using this

/-! ### Corollary 10.4 -/

/-- **Corollary 10.4(i)** of [brezis2011functional]. Let $\Omega \subset \mathbb{R}^N$ be open, let
$u_0 \in L^2(\Omega)$, and let $u$ be the solution of (1), (2), (3) in the class (4). If
$u_0 \ge 0$ almost everywhere on $\Omega$, then $u \ge 0$ in $Q$: $u(t) \ge 0$ almost everywhere
on $\Omega$ for every $t \ge 0$.

The proof is Theorem 10.3 with $K = 0$ for the lower bound. It specializes
`Heat.IsSolution.nonneg`. -/
theorem corollary_10_4_i (hu : IsHeatSolution Ω u₀ u)
    (hu₀ : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), 0 ≤ u₀ x) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), 0 ≤ u t x :=
  hu.isSolution.nonneg hu₀ ht

/-- **Corollary 10.4(ii)** of [brezis2011functional]. Let $\Omega \subset \mathbb{R}^N$ be open, let
$u_0 \in L^2(\Omega)$, and let $u$ be the solution of (1), (2), (3) in the class (4). If
$u_0 \in L^\infty(\Omega)$, then for every $t \ge 0$, $u(t) \in L^\infty(\Omega)$ and
$$\|u(t)\|_{L^\infty(\Omega)} \le \|u_0\|_{L^\infty(\Omega)}.$$

**Reading.** The source states $u \in L^\infty(Q)$ and $\|u\|_{L^\infty(Q)} \le
\|u_0\|_{L^\infty(\Omega)}$. No jointly measurable representative of the curve $u$ is built, so
the bound on $Q$ is read as this bound for every $t \ge 0$.

The proof uses both bounds of Theorem 10.3 with $K = \|u_0\|_{L^\infty}$. It specializes
`Heat.IsSolution.eLpNorm_top_le`. -/
theorem corollary_10_4_ii (hu : IsHeatSolution Ω u₀ u)
    (hu₀ : MemLp u₀ ∞ (volume.restrict (Ω : Set 𝔼))) {t : ℝ} (ht : 0 ≤ t) :
    MemLp (u t) ∞ (volume.restrict (Ω : Set 𝔼)) ∧
      eLpNorm (u t) ∞ (volume.restrict (Ω : Set 𝔼)) ≤ eLpNorm u₀ ∞ (volume.restrict (Ω : Set 𝔼)) :=
  ⟨(hu.isSolution.eLpNorm_top_le ht).trans_lt hu₀, hu.isSolution.eLpNorm_top_le ht⟩

end General

/-! ### Corollary 10.5: continuity on $\overline{Q}$ for continuous data vanishing on $\Gamma$ -/

section Regular

variable {d : ℕ}

/-- The space $\mathbb{R}^N$ of the source, with $N = d + 1$. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

variable {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
  {u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}

/-- **Corollary 10.5** of [brezis2011functional]. Let $\Omega \subset \mathbb{R}^N$ be open of class
$C^\infty$, with $N = d + 1$ and bounded boundary $\Gamma$. Let
$u_0 \in C(\overline{\Omega}) \cap L^2(\Omega)$ with $u_0 = 0$ on $\Gamma$ and, by footnote 6,
$u_0(x) \to 0$ as $|x| \to \infty$ if $\Omega$ is unbounded. Precisely, the $L^2$ datum $u_0$
agrees almost everywhere on $\Omega$ with a function $f$ that is continuous on
$\overline{\Omega}$, zero on $\Gamma$, and tends to $0$ at infinity along $\Omega$. Let $u$ be
the solution of (1), (2), (3) in the class (4). Then $u \in C(\overline{Q})$: there is a
function $U : \mathbb{R}^N \times \mathbb{R} \to \mathbb{R}$, continuous on
$\overline{\Omega} \times [0, \infty)$, with $U(\cdot, t) = u(t)$ almost everywhere on $\Omega$
for every $t \ge 0$ and $U(\cdot, 0) = f$ on $\overline{\Omega}$.

The condition at infinity is `Tendsto f (cocompact 𝔼 ⊓ 𝓟 Ω) (𝓝 0)`; it is void for bounded
$\Omega$ (`Brezis.Chapter10.corollary_10_5_of_isBounded`). The proof of the source takes
$u_{0n} \in C_c^\infty(\Omega)$ with $u_{0n} \to u_0$ in $L^\infty(\Omega)$ (the "easily
established" approximation, `Heat.exists_testFunction_tendsto_of_continuousOn`). Then
$u_n \in C^\infty(\overline{Q})$ by Theorem 10.2(c), and $\|u_n - u_m\|_{L^\infty(Q)} \le
\|u_{0n} - u_{0m}\|_{L^\infty(\Omega)}$ by (19), so $(u_n)$ converges uniformly on
$\overline{Q}$. The source identifies the limit with $u$ by
$|u_n(t) - u(t)|_{L^2} \le |u_{0n} - u_0|_{L^2}$ (Theorem 7.7); the backbone uses (19) once
more, which gives $u_n(t) \to u(t)$ almost everywhere. The proof specializes
`Heat.IsSolution.continuousOn_spaceTime`. -/
theorem corollary_10_5 (hΩ : IsOfClassC ⊤ (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) {f : 𝔼 → ℝ}
    (hf : ContinuousOn f (closure (Ω : Set 𝔼))) (hf0 : ∀ x ∈ frontier (Ω : Set 𝔼), f x = 0)
    (hft : Tendsto f (cocompact 𝔼 ⊓ 𝓟 (Ω : Set 𝔼)) (𝓝 0))
    (hu₀ : u₀ =ᵐ[volume.restrict (Ω : Set 𝔼)] f) (hu : IsHeatSolution Ω u₀ u) :
    ∃ U : 𝔼 × ℝ → ℝ, ContinuousOn U (closure (Ω : Set 𝔼) ×ˢ Ici 0) ∧
      (∀ t, 0 ≤ t → (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set 𝔼)] u t) ∧
      EqOn (fun x ↦ U (x, 0)) f (closure (Ω : Set 𝔼)) :=
  hu.isSolution.continuousOn_spaceTime hΩ hΓ hf hf0 hft hu₀

/-- **Corollary 10.5** of [brezis2011functional], for bounded $\Omega$. Let
$\Omega \subset \mathbb{R}^N$ be a bounded open set of class $C^\infty$, with $N = d + 1$. Let
$u_0 \in L^2(\Omega)$ agree almost everywhere on $\Omega$ with a function $f$ that is continuous
on $\overline{\Omega}$ and zero on $\Gamma$, and let $u$ be the solution of (1), (2), (3) in the
class (4). Then there is a function $U : \mathbb{R}^N \times \mathbb{R} \to \mathbb{R}$,
continuous on $\overline{\Omega} \times [0, \infty)$, with $U(\cdot, t) = u(t)$ almost
everywhere on $\Omega$ for every $t \ge 0$ and $U(\cdot, 0) = f$ on $\overline{\Omega}$.

The condition at infinity of footnote 6 is void, because `cocompact ⊓ 𝓟 Ω` is the trivial filter
when $\overline{\Omega}$ is compact. The proof specializes
`Heat.IsSolution.continuousOn_spaceTime_of_isBounded`. -/
theorem corollary_10_5_of_isBounded (hb : Bornology.IsBounded (Ω : Set 𝔼))
    (hΩ : IsOfClassC ⊤ (Ω : Set 𝔼)) {f : 𝔼 → ℝ} (hf : ContinuousOn f (closure (Ω : Set 𝔼)))
    (hf0 : ∀ x ∈ frontier (Ω : Set 𝔼), f x = 0) (hu₀ : u₀ =ᵐ[volume.restrict (Ω : Set 𝔼)] f)
    (hu : IsHeatSolution Ω u₀ u) :
    ∃ U : 𝔼 × ℝ → ℝ, ContinuousOn U (closure (Ω : Set 𝔼) ×ˢ Ici 0) ∧
      (∀ t, 0 ≤ t → (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set 𝔼)] u t) ∧
      EqOn (fun x ↦ U (x, 0)) f (closure (Ω : Set 𝔼)) :=
  hu.isSolution.continuousOn_spaceTime_of_isBounded hb hΩ hf hf0 hu₀

end Regular

/-! ### Theorem 10.6: the classical maximum principle -/

section Classical

variable {N : ℕ}

/-- The space $\mathbb{R}^N$ of the source. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

variable (Ω : Opens (EuclideanSpace ℝ (Fin N))) (T : ℝ)

/-- **Theorem 10.6** of [brezis2011functional], the parabolic boundary. Let
$\Omega \subset \mathbb{R}^N$ be open with boundary $\Gamma$, and let $T \in \mathbb{R}$. The
**parabolic boundary** of the cylinder $\Omega \times (0, T)$ is
$$P = (\overline{\Omega} \times \{0\}) \cup (\Gamma \times [0, T]),$$
the bottom and the lateral surface, without the top.

The definition agrees with the backbone definition `Heat.parabolicBoundary`
(`Brezis.Chapter10.parabolicBoundary_eq`). -/
def parabolicBoundary : Set (𝔼 × ℝ) :=
  closure (Ω : Set 𝔼) ×ˢ {0} ∪ frontier (Ω : Set 𝔼) ×ˢ Icc 0 T

/-- The parabolic boundary `Brezis.Chapter10.parabolicBoundary Ω T` of Theorem 10.6 equals the
backbone set `Heat.parabolicBoundary Ω T`. -/
theorem parabolicBoundary_eq : parabolicBoundary Ω T = Heat.parabolicBoundary (Ω : Set 𝔼) T :=
  rfl

/-- **Theorem 10.6** of [brezis2011functional], the hypotheses (20), (21), (22). Let
$\Omega \subset \mathbb{R}^N$ be open and $T \in \mathbb{R}$. A function $u : \mathbb{R}^N
\times \mathbb{R} \to \mathbb{R}$ is a **subsolution of the heat equation** on
$\Omega \times (0, T)$ if

* (20) $u \in C(\overline{\Omega} \times [0, T])$,
* (21) $u$ is of class $C^1$ in $t$ and of class $C^2$ in $x$ at every point of
  $\Omega \times (0, T)$, and
* (22) $\partial_t u - \Delta u \le 0$ in $\Omega \times (0, T)$.

The Laplacian $\Delta$ is Mathlib's, in the space variable. As footnote 7 says, no boundary
condition and no initial datum are prescribed. -/
structure IsHeatSubsolution (u : 𝔼 × ℝ → ℝ) : Prop where
  /-- (20): $u \in C(\overline{\Omega} \times [0, T])$. -/
  continuousOn : ContinuousOn u (closure (Ω : Set 𝔼) ×ˢ Icc 0 T)
  /-- (21): $u$ is of class $C^1$ in $t$ in $\Omega \times (0, T)$. -/
  contDiffAt_snd : ∀ x ∈ Ω, ∀ t ∈ Ioo 0 T, ContDiffAt ℝ 1 (fun s ↦ u (x, s)) t
  /-- (21): $u$ is of class $C^2$ in $x$ in $\Omega \times (0, T)$. -/
  contDiffAt_fst : ∀ x ∈ Ω, ∀ t ∈ Ioo 0 T, ContDiffAt ℝ 2 (fun y ↦ u (y, t)) x
  /-- (22): $\partial_t u - \Delta u \le 0$ in $\Omega \times (0, T)$. -/
  deriv_sub_laplacian_nonpos : ∀ x ∈ Ω, ∀ t ∈ Ioo 0 T,
    deriv (fun s ↦ u (x, s)) t - Δ (fun y ↦ u (y, t)) x ≤ 0

variable {Ω T} {u : EuclideanSpace ℝ (Fin N) × ℝ → ℝ}

/-- A function that satisfies (20), (21), (22) of Theorem 10.6 is a classical subsolution of
$\partial_t u - \Delta u \le 0$ in the sense of the backbone, `Heat.IsClassicalSubsolution` with
diffusivity $1$, which asks only differentiability in $t$. -/
theorem IsHeatSubsolution.isClassicalSubsolution (hu : IsHeatSubsolution Ω T u) :
    Heat.IsClassicalSubsolution 1 (Ω : Set 𝔼) T u :=
  ⟨hu.continuousOn, fun x hx t ht ↦ (hu.contDiffAt_snd x hx t ht).differentiableAt one_ne_zero,
    hu.contDiffAt_fst, fun x hx t ht ↦ by
      rw [one_mul]
      exact hu.deriv_sub_laplacian_nonpos x hx t ht⟩

/-- **Theorem 10.6** of [brezis2011functional]. Let $\Omega \subset \mathbb{R}^N$ be a bounded
nonempty open set, let $T > 0$, and let $u$ satisfy (20), (21), (22). Then
$$\max_{\overline{\Omega} \times [0, T]} u = \max_P u:$$
the maximum of $u$ over the closed cylinder $\overline{\Omega} \times [0, T]$ is attained at a
point of the parabolic boundary $P = (\overline{\Omega} \times \{0\}) \cup (\Gamma \times [0,
T])$.

**Reading.** The source leaves $\Omega \neq \emptyset$ implicit. For $\Omega = \emptyset$ there
is no maximum, so the statement assumes it. The bound form `Brezis.Chapter10.theorem_10_6_le`
needs no such hypothesis.

The proof of the source takes $v = u + \varepsilon |x|^2$ with $\partial_t v - \Delta v \le
-2\varepsilon N < 0$. A maximum of $v$ at $(x_0, t_0) \notin P$ would have
$\Delta v(x_0, t_0) \le 0$ and $\partial_t v(x_0, t_0) \ge 0$ (footnote 8: $t_0 = T$ gives only
the one-sided sign), a contradiction, and then $\varepsilon \to 0$. The proof here specializes
`Heat.IsClassicalSubsolution.exists_isMaxOn_parabolicBoundary`, which uses the perturbation
$u - \varepsilon t$ and needs no computation of $\Delta |x|^2$. Its one ingredient outside
Mathlib is the second-derivative test at an interior maximum. -/
theorem theorem_10_6 (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hne : (Ω : Set 𝔼).Nonempty)
    (hT : 0 < T) (hu : IsHeatSubsolution Ω T u) :
    ∃ p ∈ parabolicBoundary Ω T, IsMaxOn u (closure (Ω : Set 𝔼) ×ˢ Icc 0 T) p :=
  hu.isClassicalSubsolution.exists_isMaxOn_parabolicBoundary Ω.isOpen hb hne one_pos hT

/-- **Theorem 10.6** of [brezis2011functional], the bound form. Let $\Omega \subset \mathbb{R}^N$ be
a bounded open set, let $T > 0$, let $u$ satisfy (20), (21), (22), and let $M \in \mathbb{R}$
with $u \le M$ on the parabolic boundary $P$. Then $u \le M$ on the closed cylinder
$\overline{\Omega} \times [0, T]$.

This is the inequality $\max_{\overline{\Omega} \times [0, T]} u \le \max_P u$, which needs no
hypothesis $\Omega \neq \emptyset$. The proof specializes
`Heat.IsClassicalSubsolution.le_of_le_on_parabolicBoundary`. -/
theorem theorem_10_6_le (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hT : 0 < T)
    (hu : IsHeatSubsolution Ω T u) {M : ℝ} (hM : ∀ p ∈ parabolicBoundary Ω T, u p ≤ M) :
    ∀ q ∈ closure (Ω : Set 𝔼) ×ˢ Icc 0 T, u q ≤ M :=
  hu.isClassicalSubsolution.le_of_le_on_parabolicBoundary Ω.isOpen hb one_pos hT hM

end Classical

end Brezis.Chapter10
