/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Sobolev.Interval
import Numlib.Analysis.Sobolev.Interval.Dual
import NumlibSurface.Brezis.Chapter08.Section02

/-!
# Brezis, Section 8.3: The space $W_0^{1,p}(I)$ and its dual $W^{-1,p'}(I)$

This module formalizes Section 8.3 of [brezis2011functional], with its paragraph on the dual space
$W^{-1,p'}(I)$. Let $I$ be an open interval and $1 \le p < \infty$. The space $W_0^{1,p}(I)$ is the
closure of $C_c^1(I)$ in $W^{1,p}(I)$, with the norm of $W^{1,p}(I)$, and $H_0^1(I) = W_0^{1,2}(I)$.
It is a separable Banach space, reflexive for $p > 1$, and $H_0^1(I)$ is a separable Hilbert space.
Theorem 8.12 characterizes it by the boundary condition: $u \in W_0^{1,p}(I)$ if and only if $u = 0$
on $\partial I$. Proposition 8.13 is Poincaré's inequality
$\|u\|_{W^{1,p}(I)} \le C \|u'\|_{L^p(I)}$ on a bounded interval. The dual space of $W_0^{1,p}(I)$
is $W^{-1,p'}(I)$, and the dual space of $H_0^1(I)$ is $H^{-1}(I)$. Proposition 8.14 represents
every $F \in W^{-1,p'}(I)$ as $\langle F, u \rangle = \int_I f_0 u + \int_I f_1 u'$ with
$f_0, f_1 \in L^{p'}(I)$.

The proofs specialize the backbone modules `Numlib.Analysis.Sobolev.Interval.Zero` and
`Numlib.Analysis.Sobolev.Interval.Dual`, and the results of Section 8.2 in
`NumlibSurface.Brezis.Chapter08.Section02`.

## Main definitions

* Section 8.3, definition of $W_0^{1,p}(I)$, `Brezis.Chapter08.sobolevSpaceZero`: the closure of the
  test functions in $W^{1,p}(I)$.
* Section 8.3, notation, `Brezis.Chapter08.H10`: the space $H_0^1(I) = W_0^{1,2}(I)$.
* Section 8.3, notation, `Brezis.Chapter08.sobolevSpaceDual` and `Brezis.Chapter08.Hneg1`: the dual
  spaces $W^{-1,p'}(I)$ of $W_0^{1,p}(I)$ and $H^{-1}(I)$ of $H_0^1(I)$.

## Main results

* Section 8.3, `Brezis.Chapter08.sobolevSpaceZero_banach`,
  `Brezis.Chapter08.sobolevSpaceZero_separable`, `Brezis.Chapter08.sobolevSpaceZero_reflexive` and
  `Brezis.Chapter08.sobolevSpaceZero_hilbert`: $W_0^{1,p}(I)$ is a separable Banach space, reflexive
  for $p > 1$, and $H_0^1(I)$ is a separable Hilbert space.
* Remark 13, `Brezis.Chapter08.remark_8_13`: $W_0^{1,p}(\mathbb{R}) = W^{1,p}(\mathbb{R})$.
* Remark 14, `Brezis.Chapter08.remark_8_14`: $C_c^\infty(I)$ is dense in $W_0^{1,p}(I)$, and
  $W^{1,p}(I) \cap C_c(I) \subseteq W_0^{1,p}(I)$.
* Theorem 8.12, `Brezis.Chapter08.theorem_8_12`: $u \in W_0^{1,p}(I)$ if and only if $u = 0$ on
  $\partial I$.
* Remark 16, `Brezis.Chapter08.remark_8_16`: $u \in W_0^{1,p}(I)$ if and only if its extension by
  $0$ lies in $W^{1,p}(\mathbb{R})$, and for $p > 1$ if and only if $|\int_I u \varphi'| \le C
  \|\varphi\|_{L^{p'}(I)}$ for all $\varphi \in C_c^\infty(\mathbb{R})$.
* Proposition 8.13, `Brezis.Chapter08.proposition_8_13`, `Brezis.Chapter08.proposition_8_13_const`
  and `Brezis.Chapter08.proposition_8_13_equiv` (Poincaré's inequality):
  $\|u\|_{W^{1,p}} \le C \|u'\|_{L^p}$ on $W_0^{1,p}(I)$ for a bounded interval $I$.
* Remark 17, `Brezis.Chapter08.remark_8_17`: on a bounded interval, $\int u' v'$ is a scalar product
  on $H_0^1(I)$ with a norm equivalent to the norm of $H^1$.
* Remark 18, `Brezis.Chapter08.remark_8_18`, `Brezis.Chapter08.remark_8_18_of_bounded` and
  `Brezis.Chapter08.remark_8_18_ne`: $u \in W_0^{m,p}(I)$ if and only if
  $u = Du = \dots = D^{m-1} u = 0$ on $\partial I$, and
  $W_0^{2,p}(I) \ne W^{2,p}(I) \cap W_0^{1,p}(I)$.
* Section 8.3, the dual space, `Brezis.Chapter08.inclusions_H10_L2_Hneg1`,
  `Brezis.Chapter08.inclusions_W1p_L2_of_bounded` and
  `Brezis.Chapter08.inclusions_W1p_L2_of_unbounded`: the inclusions
  $H_0^1 \subseteq L^2 \subseteq H^{-1}$ and $W_0^{1,p} \subseteq L^2 \subseteq W^{-1,p'}$.
* Proposition 8.14, `Brezis.Chapter08.proposition_8_14` and
  `Brezis.Chapter08.proposition_8_14_bounded`: every $F \in W^{-1,p'}(I)$ is
  $u \mapsto \int_I f_0 u + \int_I f_1 u'$ for some $f_0, f_1 \in L^{p'}(I)$, with $f_0 = 0$ when
  $I$ is bounded.
* Remark 19, `Brezis.Chapter08.remark_8_19`: the functions $f_0$ and $f_1$ are not unique.
* Remark 21, `Brezis.Chapter08.remark_8_21`: the same representation holds for continuous linear
  functionals on $W^{1,p}(I)$.

## Conventions

* The conventions of Section 8.2 (`NumlibSurface.Brezis.Chapter08.Section02`) apply. In particular
  `SobolevIntervalLp.rep u` is the continuous representative of $u$ of Theorem 8.2, and the
  conjugate exponent $p'$ is `q` with `[p.HolderConjugate q]`.
* Where the source excludes $p = \infty$, the statements have the hypothesis `hp : p ≠ ∞`.
* The space $W_0^{1,p}(I)$ is a `Submodule ℝ (SobolevIntervalLp 1 p I)`. So it carries the norm of
  $W^{1,p}(I)$ and, for $p = 2$, the scalar product of $H^1(I)$.
* The condition "$u = 0$ on $\partial I$" is `∀ x ∈ frontier (I : Set ℝ), u.rep x = 0`.

## Implementation notes

* The space $W_0^{1,p}(I)$ is the closure of the test functions $C_c^\infty(I)$, where the source
  closes $C_c^1(I)$. By Remark 1 both closures are the same space.
* The subspace $W_0^{1,p}(I)$ is also defined for $p = \infty$, which the source excludes. Results
  that do not need $p < \infty$ hold in this case too.

## Deviations from the source

* **Definitions of $W_0^{1,p}(I)$ and its dual** (generalization). The definitions include
  $p = \infty$ and apply to arbitrary open sets. See `Brezis.Chapter08.sobolevSpaceZero` and
  `Brezis.Chapter08.sobolevSpaceDual`.
* **Basic Banach and Hilbert properties and Remark 14(i)** (generalization). The results apply
  on arbitrary open sets. Completeness and smooth density include $p=\infty$.
* **Proposition 8.13 and Remark 17** (generalization). Poincaré's inequality includes $p=\infty$,
  and the estimates give explicit constants. See `Brezis.Chapter08.proposition_8_13_const` and
  `Brezis.Chapter08.remark_8_17`.
* **Remark 18** (generalization). The source states the characterization of $W_0^{m,p}(I)$ for
  $m \ge 2$. It is stated for every $m \ge 1$, and the case $m = 1$ is Theorem 8.12. See
  `Brezis.Chapter08.remark_8_18` and `Brezis.Chapter08.remark_8_18_of_bounded`.
* **Proposition 8.14** (reading). The source prints $\|F\| = \max(\|f_0\|_{L^{p'}},
  \|f_1\|_{L^{p'}})$ for the norm $\|u\|_{L^p} + \|u'\|_{L^p}$ on $W^{1,p}$. The statement uses the
  norm of the type, whose dual norm is the $\ell^{p'}$ norm of the pair $(f_0, f_1)$. See
  `Brezis.Chapter08.proposition_8_14`.
* **Proposition 8.14, bounded interval** (reading). The source's proof switches to the
  equivalent derivative norm. The library states existence of the one-term representation.
  See `Brezis.Chapter08.proposition_8_14_bounded`.
* **Remarks 19 and 21** (generalization). The representation statements allow arbitrary open
  sets. The nonuniqueness identity includes $p=\infty$. See `Brezis.Chapter08.remark_8_19` and
  `Brezis.Chapter08.remark_8_21`.

## Not formalized

* **Remark 15**, a discussion.
* **Remark 20.** The identification of $F \in W^{-1,p'}(I)$ with the distribution $f_0 - f_1'$.
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal InnerProductSpace Topology

noncomputable section

namespace Brezis.Chapter08

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {I : Opens ℝ}

/-! ### The definition -/

/-- **Section 8.3** of [brezis2011functional], definition of $W_0^{1,p}(I)$. Let
$I \subseteq \mathbb{R}$ be open and $1 \le p \le \infty$. The space $W_0^{1,p}(I)$ is the
closure of the test functions $C_c^\infty(I)$ in $W^{1,p}(I)$. It is a closed subspace of
$W^{1,p}(I)$, with the norm of $W^{1,p}(I)$.

**Generalization.** The source assumes $p < \infty$ and an interval. The closure defining the
subspace also applies to arbitrary open sets and at $p = \infty$.

The source takes the closure of $C_c^1(I)$. Mollification gives the same closure by Remark 14(i).
The subspace is `SobolevIntervalLpZero 1 p I`. -/
abbrev sobolevSpaceZero (p : ℝ≥0∞) [Fact (1 ≤ p)] (I : Opens ℝ) :
    Submodule ℝ (SobolevIntervalLp 1 p I) :=
  SobolevIntervalLpZero 1 p I

/-- **Section 8.3** of [brezis2011functional], notation. The space $H_0^1(I)$ is $W_0^{1,2}(I)$,
with the scalar product of $H^1(I)$.

**Generalization.** The notation applies on arbitrary open sets. -/
abbrev H10 (I : Opens ℝ) : Submodule ℝ (SobolevIntervalLp 1 2 I) := sobolevSpaceZero 2 I

/-- Let $I \subseteq \mathbb{R}$ be open, $1 \le p \le \infty$ and $u \in W^{1,p}(I)$. Then
$u \in W_0^{1,p}(I)$ if and only if $u$ lies in the closure, in $W^{1,p}(I)$, of the set of
elements whose function equals a test function in $C_c^\infty(I)$ almost everywhere on $I$. This
unfolds the definition of Section 8.3 of [brezis2011functional].

**Generalization.** The smooth closure characterization applies on arbitrary open sets and
includes $p=\infty$. -/
theorem mem_sobolevSpaceZero_iff_mem_closure (u : SobolevIntervalLp 1 p I) :
    u ∈ sobolevSpaceZero p I ↔
      u ∈ closure {v : SobolevIntervalLp 1 p I | ∃ φ : 𝓓(I, ℝ), v.fn =ᵐ[volume.restrict I] φ} := by
  change u ∈ SobolevIntervalLpZero 1 p I ↔ _
  rw [SobolevIntervalLpZero, SobolevMultiIndexZero, ← SetLike.mem_coe,
    Submodule.topologicalClosure_coe]
  rfl

/-! ### The space $W_0^{1,p}$ is a Banach space, reflexive and separable -/

/-- **Section 8.3** of [brezis2011functional], $W_0^{1,p}$ is a Banach space. Let
$I \subseteq \mathbb{R}$ be open and $1 \le p \le \infty$. Then $W_0^{1,p}(I)$ is complete, as a
closed subspace of $W^{1,p}(I)$.

Completeness is the instance `SobolevMultiIndexZero.instCompleteSpace`.

**Generalization.** Completeness holds on arbitrary open sets and at $p=\infty$. -/
theorem sobolevSpaceZero_banach : CompleteSpace (sobolevSpaceZero p I) := inferInstance

/-- **Section 8.3** of [brezis2011functional], $W_0^{1,p}$ is separable. Let
$I \subseteq \mathbb{R}$ be open and $1 \le p < \infty$. Then $W_0^{1,p}(I)$ is separable, as a
subspace of the separable space $W^{1,p}(I)$ (Proposition 8.1).

The source refers to its Proposition 3.25.

**Generalization.** Separability holds on arbitrary open sets for finite $p$. -/
theorem sobolevSpaceZero_separable (hp : p ≠ ∞) :
    TopologicalSpace.SeparableSpace (sobolevSpaceZero p I) :=
  have : Fact (p ≠ ∞) := ⟨hp⟩
  have : SecondCountableTopology (SobolevIntervalLp 1 p I) :=
    SobolevMultiIndex.instSecondCountableTopology
  TopologicalSpace.SecondCountableTopology.to_separableSpace

/-- **Section 8.3** of [brezis2011functional], $W_0^{1,p}$ is reflexive for $p > 1$. Let
$I \subseteq \mathbb{R}$ be open and $1 < p < \infty$. Then $W_0^{1,p}(I)$ is reflexive, as a
closed subspace of the reflexive space $W^{1,p}(I)$ (Proposition 8.1).

The source refers to its Proposition 3.20. The proof uses
`SobolevMultiIndexZero.instIsReflexive` and Theorem 4.10 (`Brezis.Chapter04.theorem_4_10`).

**Generalization.** Reflexivity holds on arbitrary open sets for $1<p<\infty$. -/
theorem sobolevSpaceZero_reflexive (hp1 : 1 < p) (hp : p ≠ ∞) :
    NormedSpace.IsReflexive ℝ (sobolevSpaceZero p I) :=
  have : NormedSpace.IsReflexive ℝ (Lp ℝ p (volume.restrict (I : Set ℝ))) :=
    Brezis.Chapter04.theorem_4_10 hp1 hp
  inferInstance

/-- **Section 8.3** of [brezis2011functional], $H_0^1$ is a separable Hilbert space. Let
$I \subseteq \mathbb{R}$ be open. The scalar product of $H_0^1(I)$ is the scalar product of
$H^1(I)$, $(u, v)_{H_0^1} = (u, v)_{H^1}$, and $H_0^1(I)$ is complete and separable.

**Generalization.** The separable Hilbert structure applies on arbitrary open sets. -/
theorem sobolevSpaceZero_hilbert :
    (∀ u v : H10 I, ⟪u, v⟫_ℝ = ⟪(u : SobolevIntervalLp 1 2 I), (v : SobolevIntervalLp 1 2 I)⟫_ℝ) ∧
      CompleteSpace (H10 I) ∧ TopologicalSpace.SeparableSpace (H10 I) :=
  ⟨fun u v ↦ Submodule.coe_inner _ u v, inferInstance,
    sobolevSpaceZero_separable ENNReal.ofNat_ne_top⟩

/-! ### Remarks 13 and 14 -/

/-- **Remark 13** in Chapter 8 of [brezis2011functional]. Let $1 \le p < \infty$. Then
$W_0^{1,p}(\mathbb{R}) = W^{1,p}(\mathbb{R})$.

The source deduces this from the density of $C_c^1(\mathbb{R})$ in $W^{1,p}(\mathbb{R})$,
Theorem 8.7. The line $\mathbb{R}$ is `⊤ : Opens ℝ`, and the whole space $W^{1,p}(\mathbb{R})$
is the subspace `⊤`. The proof specializes `sobolevIntervalLpZero_top`. -/
theorem remark_8_13 (hp : p ≠ ∞) : sobolevSpaceZero p ⊤ = ⊤ := sobolevIntervalLpZero_top hp

/-- **Remark 14(i)** in Chapter 8 of [brezis2011functional]. Let $I \subseteq \mathbb{R}$ be open
and $1 \le p \le \infty$. The elements of $W_0^{1,p}(I)$ whose function equals a test function
in $C_c^\infty(I)$ almost everywhere form a dense subset of $W_0^{1,p}(I)$.

This holds by the definition of $W_0^{1,p}(I)$, since a set is dense in its closure.

**Generalization.** Smooth density holds on arbitrary open sets and includes $p=\infty$. -/
theorem remark_8_14_i :
    Dense {v : sobolevSpaceZero p I |
      ∃ φ : 𝓓(I, ℝ), (v : SobolevIntervalLp 1 p I).fn =ᵐ[volume.restrict I] φ} := by
  change ∀ x, x ∈ closure _
  intro x
  rw [closure_subtype]
  have hx : (x : SobolevIntervalLp 1 p I) ∈ closure
      (SobolevMultiIndex.testFunctions ℝ (Module.Basis.singleton Unit ℝ) 1 p I volume :
        Set (SobolevIntervalLp 1 p I)) := by
    have hx2 : (x : SobolevIntervalLp 1 p I) ∈ SobolevIntervalLpZero 1 p I := x.2
    rwa [← SetLike.mem_coe, SobolevIntervalLpZero, SobolevMultiIndexZero,
      Submodule.topologicalClosure_coe] at hx2
  refine closure_mono ?_ hx
  rintro v ⟨φ, hφ⟩
  exact ⟨⟨v, SobolevIntervalLpZero.mem_of_fn_ae_eq φ hφ⟩, ⟨φ, hφ⟩, rfl⟩

/-- **Remark 14(ii)** in Chapter 8 of [brezis2011functional]. Let $I$ be an open interval,
$1 \le p < \infty$ and $u \in W^{1,p}(I)$. Suppose that there is a compact set $K \subseteq I$
such that $\tilde u(x) = 0$ for all $x \in \bar I \setminus K$. Then $u \in W_0^{1,p}(I)$. So
$W^{1,p}(I) \cap C_c(I) \subseteq W_0^{1,p}(I)$.

Here $\tilde u$ is `SobolevIntervalLp.rep u`. The proof specializes
`SobolevIntervalLpZero.mem_of_hasCompactSupport`, through Theorem 8.12 instead of the
mollification of the source. -/
theorem remark_8_14_ii (hI : (I : Set ℝ).OrdConnected) (hp : p ≠ ∞) (u : SobolevIntervalLp 1 p I)
    (h : ∃ K : Set ℝ, IsCompact K ∧ K ⊆ I ∧ ∀ x ∈ closure (I : Set ℝ), x ∉ K → u.rep x = 0) :
    u ∈ sobolevSpaceZero p I :=
  SobolevIntervalLpZero.mem_of_hasCompactSupport hI hp u h

/-- **Remark 14** in Chapter 8 of [brezis2011functional]. Let $I$ be an open interval and
$1 \le p < \infty$. (i) The elements of $W_0^{1,p}(I)$ whose function equals a test function in
$C_c^\infty(I)$ almost everywhere are dense in $W_0^{1,p}(I)$. (ii) If $u \in W^{1,p}(I)$ and
$\tilde u$ vanishes on $\bar I$ outside a compact subset of $I$, then $u \in W_0^{1,p}(I)$; that
is, $W^{1,p}(I) \cap C_c(I) \subseteq W_0^{1,p}(I)$. -/
theorem remark_8_14 (hI : (I : Set ℝ).OrdConnected) (hp : p ≠ ∞) :
    Dense {v : sobolevSpaceZero p I |
      ∃ φ : 𝓓(I, ℝ), (v : SobolevIntervalLp 1 p I).fn =ᵐ[volume.restrict I] φ} ∧
    ∀ u : SobolevIntervalLp 1 p I,
      (∃ K : Set ℝ, IsCompact K ∧ K ⊆ I ∧ ∀ x ∈ closure (I : Set ℝ), x ∉ K → u.rep x = 0) →
      u ∈ sobolevSpaceZero p I :=
  ⟨remark_8_14_i, fun u h ↦ remark_8_14_ii hI hp u h⟩

/-! ### Theorem 8.12 and Remark 16 -/

/-- **Theorem 8.12** of [brezis2011functional]. Let $I$ be an open interval, $1 \le p < \infty$ and
$u \in W^{1,p}(I)$. Then $u \in W_0^{1,p}(I)$ if and only if $u = 0$ on $\partial I$.

Here "$u = 0$ on $\partial I$" means that the continuous representative
`SobolevIntervalLp.rep u` vanishes on the frontier of $I$. For $I = \mathbb{R}$ the frontier is
empty. The proof specializes `mem_sobolevIntervalLpZero_iff`. Its converse uses a cut-off
function and the bounded case instead of the truncation $G(nu)/n$ of the source. For $p = 2$ on
$(a, b)$ the backbone also has `mem_sobolevIntervalZero_iff` in
`Numlib.Analysis.Sobolev.Interval`. -/
theorem theorem_8_12 (hI : (I : Set ℝ).OrdConnected) (hp : p ≠ ∞) (u : SobolevIntervalLp 1 p I) :
    u ∈ sobolevSpaceZero p I ↔ ∀ x ∈ frontier (I : Set ℝ), u.rep x = 0 :=
  mem_sobolevIntervalLpZero_iff hI hp u

/-- If $f = g$ almost everywhere on a measurable set $s$, then the extensions of $f$ and $g$ by $0$
outside $s$ are equal almost everywhere on $\mathbb{R}$. -/
private theorem indicator_ae_eq_of_ae_eq_restrict {f g : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (h : f =ᵐ[volume.restrict s] g) : s.indicator f =ᵐ[volume] s.indicator g := by
  filter_upwards [(ae_restrict_iff' hs).1 h] with x hx
  by_cases hxs : x ∈ s
  · rw [indicator_of_mem hxs, indicator_of_mem hxs, hx hxs]
  · rw [indicator_of_notMem hxs, indicator_of_notMem hxs]

/-- **Remark 16(i)** in Chapter 8 of [brezis2011functional]. Let $I$ be an open interval,
$1 \le p < \infty$ and $u \in L^p(I)$, and let $\bar u$ be the extension of $u$ by $0$ outside
$I$. Then $u \in W_0^{1,p}(I)$ if and only if $\bar u \in W^{1,p}(\mathbb{R})$.

Here $u \in W_0^{1,p}(I)$ means that some element of $W_0^{1,p}(I)$ has the function $u$ almost
everywhere on $I$. The proof specializes `mem_sobolevIntervalLpZero_iff_indicator_mem`, and it
uses the restriction `SobolevIntervalLp.restrict` of $\bar u$ to $I$ for the converse. -/
theorem remark_8_16_i (hI : (I : Set ℝ).OrdConnected) (hp : p ≠ ∞) {u : ℝ → ℝ}
    (_hu : MemLp u p (volume.restrict I)) :
    (∃ v ∈ sobolevSpaceZero p I, (v : SobolevIntervalLp 1 p I).fn =ᵐ[volume.restrict I] u) ↔
      MemSobolevSpace p ⊤ ((I : Set ℝ).indicator u) := by
  rw [memSobolevSpace_iff_memSobolevIntervalLp]
  constructor
  · rintro ⟨v, hv, hvu⟩
    refine ((mem_sobolevIntervalLpZero_iff_indicator_mem hI hp v).1 hv).congr_ae ?_
    exact SobolevIntervalLp.eventuallyEq_restrict_top_iff.2
      (indicator_ae_eq_of_ae_eq_restrict I.isOpen.measurableSet hvu)
  · intro h
    obtain ⟨w, hw⟩ := h.exists_sobolevIntervalLp
    have hw' : w.fn =ᵐ[volume] (I : Set ℝ).indicator u :=
      SobolevIntervalLp.eventuallyEq_restrict_top_iff.1 hw
    have hw'' : w.fn =ᵐ[volume.restrict I] (I : Set ℝ).indicator u := ae_restrict_of_ae hw'
    have hvu : (SobolevIntervalLp.restrict (J := I) (I := ⊤) (subset_univ _) w).fn
        =ᵐ[volume.restrict I] u :=
      (SobolevIntervalLp.fn_restrict_ae_eq _ w).trans
        (hw''.trans (indicator_ae_eq_restrict I.isOpen.measurableSet.nullMeasurableSet))
    refine ⟨_, (mem_sobolevIntervalLpZero_iff_indicator_mem hI hp _).2 (h.congr_ae ?_), hvu⟩
    exact SobolevIntervalLp.eventuallyEq_restrict_top_iff.2
      (indicator_ae_eq_of_ae_eq_restrict I.isOpen.measurableSet hvu).symm

/-- **Remark 16(ii)** in Chapter 8 of [brezis2011functional]. Let $I$ be an open interval,
$1 < p < \infty$ with conjugate exponent $p'$, and $u \in L^p(I)$. Then $u \in W_0^{1,p}(I)$ if
and only if there is a constant $C$ with
$$\left| \int_I u \varphi' \right| \le C \|\varphi\|_{L^{p'}(I)} \quad \text{for all } \varphi
  \in C_c^\infty(\mathbb{R}).$$

The test functions are test functions on the whole line, not on $I$. The source tests against
$C_c^1(\mathbb{R})$. Here $u \in W_0^{1,p}(I)$ means that some element of $W_0^{1,p}(I)$ has the
function $u$ almost everywhere on $I$. The proof specializes
`mem_sobolevIntervalLpZero_iff_forall_abs_integral_le`. -/
theorem remark_8_16_ii {q : ℝ≥0∞} [p.HolderConjugate q] (hp1 : 1 < p) (hp : p ≠ ∞)
    (hI : (I : Set ℝ).OrdConnected) {u : ℝ → ℝ} (hu : MemLp u p (volume.restrict I)) :
    (∃ v ∈ sobolevSpaceZero p I, (v : SobolevIntervalLp 1 p I).fn =ᵐ[volume.restrict I] u) ↔
      ∃ C : ℝ, ∀ φ : 𝓓((⊤ : Opens ℝ), ℝ),
        |∫ x in (I : Set ℝ), u x * deriv φ x| ≤ C * (eLpNorm φ q (volume.restrict I)).toReal :=
  mem_sobolevIntervalLpZero_iff_forall_abs_integral_le hp
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt q p).2 hp1).ne hI hu

/-- **Remark 16** in Chapter 8 of [brezis2011functional]. Let $I$ be an open interval,
$1 \le p < \infty$ with conjugate exponent $p'$, and $u \in L^p(I)$. (i) $u \in W_0^{1,p}(I)$ if
and only if the extension of $u$ by $0$ outside $I$ lies in $W^{1,p}(\mathbb{R})$. (ii) If
$p > 1$, then $u \in W_0^{1,p}(I)$ if and only if there is a constant $C$ with $|\int_I u
\varphi'| \le C \|\varphi\|_{L^{p'}(I)}$ for all $\varphi \in C_c^\infty(\mathbb{R})$. -/
theorem remark_8_16 {q : ℝ≥0∞} [p.HolderConjugate q] (hI : (I : Set ℝ).OrdConnected) (hp : p ≠ ∞)
    {u : ℝ → ℝ} (hu : MemLp u p (volume.restrict I)) :
    ((∃ v ∈ sobolevSpaceZero p I, (v : SobolevIntervalLp 1 p I).fn =ᵐ[volume.restrict I] u) ↔
      MemSobolevSpace p ⊤ ((I : Set ℝ).indicator u)) ∧
    (1 < p →
      ((∃ v ∈ sobolevSpaceZero p I, (v : SobolevIntervalLp 1 p I).fn =ᵐ[volume.restrict I] u) ↔
        ∃ C : ℝ, ∀ φ : 𝓓((⊤ : Opens ℝ), ℝ),
          |∫ x in (I : Set ℝ), u x * deriv φ x|
            ≤ C * (eLpNorm φ q (volume.restrict I)).toReal)) :=
  ⟨remark_8_16_i hI hp hu, fun hp1 ↦ remark_8_16_ii hp1 hp hI hu⟩

/-! ### Proposition 8.13, Poincaré's inequality -/

/-- **Proposition 8.13** of [brezis2011functional] (Poincaré's inequality), with an explicit
constant. Let $a < b$, $1 \le p \le \infty$ and $u \in W_0^{1,p}((a, b))$. Then
$$\|u\|_{W^{1,p}} \le \left( \frac{b - a}{p^{1/p}} + 1 \right) \|u'\|_{L^p}$$
in the norm of the source. For $p = \infty$ the factor is $(b - a) + 1$.

The proof of the source gives the factor $1 + (b - a)$. For $p = 2$ the $L^2$ part of the factor
is $(b - a)/\sqrt{2}$, as in `SobolevIntervalZero.norm_deriv_zero_le`. The proof specializes
`SobolevIntervalLpZero.norm_deriv_zero_le`.

**Generalization.** The explicit factor improves the bound from the source's proof at
$1<p<\infty$. The estimate also applies at $p=\infty$. -/
theorem proposition_8_13_const {a b : ℝ} (hab : a < b) {u : SobolevIntervalLp 1 p (Opens.Ioo a b)}
    (hu : u ∈ sobolevSpaceZero p (Opens.Ioo a b)) :
    sobolevNorm u ≤ ((b - a) / p.toReal ^ p.toReal⁻¹ + 1) * ‖u.deriv 1‖ := by
  have := SobolevIntervalLpZero.norm_deriv_zero_le hab hu
  unfold sobolevNorm
  linarith

/-- **Proposition 8.13** of [brezis2011functional] (Poincaré's inequality). Let $I = (a, b)$ be a
bounded interval and $1 \le p \le \infty$. There is a constant $C$ such that
$$\|u\|_{W^{1,p}(I)} \le C \|u'\|_{L^p(I)} \quad \text{for all } u \in W_0^{1,p}(I).$$

The source says that $C$ depends on $|I| < \infty$. A value of $C$ is in
`Brezis.Chapter08.proposition_8_13_const`. The norm on the left is the norm of the source,
`Brezis.Chapter08.sobolevNorm`. The statement includes $p = \infty$, for the closure of the test
functions in $W^{1,\infty}(I)$.

**Generalization.** The inequality applies at $p=\infty$. -/
theorem proposition_8_13 {a b : ℝ} (hab : a < b) :
    ∃ C : ℝ, ∀ u ∈ sobolevSpaceZero p (Opens.Ioo a b), sobolevNorm u ≤ C * ‖u.deriv 1‖ :=
  ⟨_, fun _ hu ↦ proposition_8_13_const hab hu⟩

/-- **Proposition 8.13** of [brezis2011functional], the equivalent norm. Let $a < b$ and
$1 \le p \le \infty$. There is a constant $C$ such that for all $u \in W_0^{1,p}((a, b))$,
$$\|u'\|_{L^p} \le \|u\| \le C \|u'\|_{L^p},$$
and $\|u'\|_{L^p} = 0$ if and only if $u = 0$. So $\|u'\|_{L^p}$ is a norm on
$W_0^{1,p}((a, b))$, equivalent to the norm of $W^{1,p}$.

Here $\|u\|$ is the norm of the type.

**Generalization.** The derivative norm equivalence applies at $p=\infty$. -/
theorem proposition_8_13_equiv {a b : ℝ} (hab : a < b) :
    ∃ C : ℝ, ∀ u ∈ sobolevSpaceZero p (Opens.Ioo a b),
      ‖u.deriv 1‖ ≤ ‖u‖ ∧ ‖u‖ ≤ C * ‖u.deriv 1‖ ∧ (‖u.deriv 1‖ = 0 ↔ u = 0) :=
  ⟨_, fun u hu ↦ ⟨SobolevIntervalLp.norm_deriv_le u 1,
    SobolevIntervalLpZero.norm_le_mul_norm_deriv hab hu,
    SobolevIntervalLpZero.norm_deriv_one_eq_zero_iff hab hu⟩⟩

/-- **Remark 17** in Chapter 8 of [brezis2011functional]. Let $I = (a, b)$ be a bounded interval.
For $u, v \in H^1(I)$, the $L^2$ scalar product of the derivatives is
$(u', v')_{L^2} = \int_a^b u' v'$. It is definite on $H_0^1(I)$: if $u \in H_0^1(I)$ and
$(u', u')_{L^2} = 0$, then $u = 0$. So it is a scalar product on $H_0^1(I)$, and its norm
$\|u'\|_{L^2}$ is equivalent to the norm of $H^1$:
$$\|u'\|_{L^2} \le \|u\|_{H^1} \le \sqrt{1 + (b - a)^2/2} \, \|u'\|_{L^2} \quad \text{for all }
  u \in H_0^1(I).$$

The proof specializes `SobolevIntervalZero.norm_le_seminorm` and
`SobolevIntervalZero.seminorm_eq_zero_iff`.

**Generalization.** The integral identity applies to $H^1(I)$, and the norm equivalence on
$H_0^1(I)$ includes the displayed upper bound. -/
theorem remark_8_17 {a b : ℝ} (hab : a < b) :
    (∀ u v : SobolevIntervalLp 1 2 (Opens.Ioo a b),
      ⟪u.deriv 1, v.deriv 1⟫_ℝ = ∫ x in Ioo a b, u.deriv 1 x * v.deriv 1 x) ∧
    (∀ u ∈ sobolevSpaceZero 2 (Opens.Ioo a b), ⟪u.deriv 1, u.deriv 1⟫_ℝ = 0 → u = 0) ∧
    ∀ u ∈ sobolevSpaceZero 2 (Opens.Ioo a b),
      ‖u.deriv 1‖ ≤ ‖u‖ ∧ ‖u‖ ≤ √(1 + (b - a) ^ 2 / 2) * ‖u.deriv 1‖ := by
  refine ⟨fun u v ↦ ?_, fun u hu h ↦ ?_, fun u hu ↦ ⟨SobolevIntervalLp.norm_deriv_le u 1, ?_⟩⟩
  · rw [L2.inner_def]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp [RCLike.inner_apply, mul_comm]
  · rw [real_inner_self_eq_norm_sq, sq_eq_zero_iff] at h
    exact (SobolevIntervalZero.seminorm_eq_zero_iff hab hu).1 h
  · exact SobolevIntervalZero.norm_le_seminorm hab hu

/-! ### Remark 18: the spaces $W_0^{m,p}$ -/

/-- **Remark 18** in Chapter 8 of [brezis2011functional], on a bounded interval. Let $a < b$,
$1 \le p < \infty$, $m \ge 1$ and $u \in W^{m,p}((a, b))$. Let $W_0^{m,p}((a, b))$ be the
closure of the test functions $C_c^\infty((a, b))$ in $W^{m,p}((a, b))$. Then
$u \in W_0^{m,p}((a, b))$ if and only if
$$u = Du = \dots = D^{m-1} u = 0 \quad \text{at } a \text{ and at } b,$$
where each $D^j u$ is read through its continuous representative.

**Generalization.** The source states this for $m \ge 2$. The statement here holds for every
$m \ge 1$, and the case $m = 1$ is Theorem 8.12.

The source defines $W_0^{m,p}(I)$ as the closure of $C_c^m(I)$. The space is
`SobolevIntervalLpZero (m + 1) p (Opens.Ioo a b)`, with the order written `m + 1`. The function
$D^j u$ with its derivative $D^{j+1} u$ is the element `SobolevIntervalLp.derivOne u j` of
$W^{1,p}((a, b))$, and its continuous representative is taken with `SobolevIntervalLp.rep`. The
proof specializes `mem_sobolevIntervalLpZero_higher_iff_of_bounded`, by induction from Theorem
8.12 instead of Exercise 8.9 as in the source. -/
theorem remark_8_18_of_bounded {a b : ℝ} (hab : a < b) (hp : p ≠ ∞) {m : ℕ}
    (u : SobolevIntervalLp (m + 1) p (Opens.Ioo a b)) :
    u ∈ SobolevIntervalLpZero (m + 1) p (Opens.Ioo a b) ↔
      ∀ j : Fin (m + 1), ∀ x ∈ frontier (Ioo a b), (SobolevIntervalLp.derivOne u j).rep x = 0 :=
  mem_sobolevIntervalLpZero_higher_iff_of_bounded hab hp u

/-- **Remark 18** in Chapter 8 of [brezis2011functional]. Let $I$ be an open interval,
$1 \le p < \infty$, $m \ge 1$ and $u \in W^{m,p}(I)$. Let $W_0^{m,p}(I)$ be the closure of the
test functions $C_c^\infty(I)$ in $W^{m,p}(I)$. Then $u \in W_0^{m,p}(I)$ if and only if
$$u = Du = \dots = D^{m-1} u = 0 \quad \text{on } \partial I,$$
where each $D^j u$ is read through its continuous representative.

**Generalization.** The source states this for $m \ge 2$. The statement here holds for every
$m \ge 1$, and the case $m = 1$ is Theorem 8.12.

The source defines $W_0^{m,p}(I)$ as the closure of $C_c^m(I)$. The order is written `m + 1`,
and $D^j u$ is read through `SobolevIntervalLp.derivOne u j` as in
`Brezis.Chapter08.remark_8_18_of_bounded`. The proof specializes
`mem_sobolevIntervalLpZero_higher_iff`, which reduces the unbounded case to the bounded one by
the cut-offs $\zeta_n u$ at every order instead of Exercise 8.9 as in the source. -/
theorem remark_8_18 (hI : (I : Set ℝ).OrdConnected) (hp : p ≠ ∞) {m : ℕ}
    (u : SobolevIntervalLp (m + 1) p I) :
    u ∈ SobolevIntervalLpZero (m + 1) p I ↔
      ∀ j : Fin (m + 1), ∀ x ∈ frontier (I : Set ℝ), (SobolevIntervalLp.derivOne u j).rep x = 0 :=
  mem_sobolevIntervalLpZero_higher_iff hI hp u

/-- **Remark 18** in Chapter 8 of [brezis2011functional],
$W_0^{2,p}(I) \ne W^{2,p}(I) \cap W_0^{1,p}(I)$. Let $1 \le p < \infty$ and $I = (0, 1)$. There
is an element $u \in W^{2,p}(I)$ with function $x(1 - x)$ almost everywhere that lies in
$W_0^{1,p}(I)$, as an element of $W^{1,p}(I)$, but not in $W_0^{2,p}(I)$: its derivative at $0$
is $1$.

The element of $W^{1,p}(I)$ is `SobolevIntervalLp.derivOne u 0`, the pair $(u, u')$.

**Reading.** The polynomial on $(0,1)$ gives an explicit witness for the distinction of
the two spaces in the source. -/
theorem remark_8_18_ne (hp : p ≠ ∞) :
    ∃ u : SobolevIntervalLp 2 p (Opens.Ioo 0 1),
      (u.fn =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] fun x ↦ x * (1 - x)) ∧
      SobolevIntervalLp.derivOne u 0 ∈ sobolevSpaceZero p (Opens.Ioo 0 1) ∧
      u ∉ SobolevIntervalLpZero 2 p (Opens.Ioo 0 1) := by
  have hI := SobolevIntervalLp.ordConnected_coe_Ioo (0 : ℝ) 1
  have hcl := SobolevIntervalLp.closure_coe_Ioo (zero_lt_one' ℝ)
  have hfr : frontier ((Opens.Ioo (0 : ℝ) 1 : Opens ℝ) : Set ℝ) = {0, 1} := by
    rw [Opens.coe_Ioo, frontier_Ioo zero_lt_one]
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun x ↦ x * (1 - x) := ⟨_, rfl⟩
  have hgs : ContDiff ℝ (⊤ : ℕ∞) g := by rw [hg]; fun_prop
  have hderiv : ∀ x, deriv g x = 1 * (1 - x) + x * (0 - 1) := fun x ↦ by
    rw [hg]
    exact ((hasDerivAt_id x).mul ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x))).deriv
  have hmemj : ∀ j : ℕ,
      MemLp (iteratedDeriv j g) p (volume.restrict ((Opens.Ioo (0 : ℝ) 1 : Opens ℝ) : Set ℝ)) :=
    fun j ↦ ((hgs.continuous_iteratedDeriv j
      (by simp)).continuousOn.memLp_top_restrict_Ioo).mono_exponent le_top
  obtain ⟨v, hv⟩ : ∃ v : Fin 3 → Lp ℝ p (volume.restrict ((Opens.Ioo (0 : ℝ) 1 : Opens ℝ) : Set ℝ)),
      ∀ j, v j = (hmemj j).toLp _ := ⟨_, fun _ ↦ rfl⟩
  have hv0 : ⇑(v 0) =ᵐ[volume.restrict ((Opens.Ioo (0 : ℝ) 1 : Opens ℝ) : Set ℝ)] g := by
    rw [hv]
    exact (hmemj 0).coeFn_toLp.trans (Eventually.of_forall fun x ↦ by rw [iteratedDeriv_zero])
  have hvj : ∀ j : Fin 3, ⇑(v j) =ᵐ[volume.restrict ((Opens.Ioo (0 : ℝ) 1 : Opens ℝ) : Set ℝ)]
      iteratedDeriv j g := fun j ↦ by rw [hv]; exact (hmemj j).coeFn_toLp
  obtain ⟨u, hu⟩ : ∃ u : SobolevIntervalLp 2 p (Opens.Ioo 0 1), u = SobolevIntervalLp.mk v
      (fun j ↦ (hasWeakIteratedDerivOn_of_contDiffOn (I := Opens.Ioo 0 1) (k := j)
        hgs.contDiffOn (by simp)).congr_ae hv0.symm (hvj j).symm) := ⟨_, rfl⟩
  have hfn : u.fn =ᵐ[volume.restrict ((Opens.Ioo (0 : ℝ) 1 : Opens ℝ) : Set ℝ)] g := by
    rw [hu]; exact hv0
  have hrep0 : ∀ x ∈ Icc (0 : ℝ) 1, (SobolevIntervalLp.derivOne u 0).rep x = g x := fun x hx ↦
    SobolevIntervalLp.rep_eq_of_continuousOn hI _ hgs.continuous.continuousOn hfn (hcl ▸ hx)
  have hrep1 : ∀ x ∈ Icc (0 : ℝ) 1, (SobolevIntervalLp.derivOne u 1).rep x = deriv g x := by
    intro x hx
    refine SobolevIntervalLp.rep_eq_of_continuousOn hI _
      (hgs.continuous_deriv (by simp)).continuousOn ?_ (hcl ▸ hx)
    have h1 : ⇑(v 1) =ᵐ[volume.restrict ((Opens.Ioo (0 : ℝ) 1 : Opens ℝ) : Set ℝ)]
        iteratedDeriv 1 g := hvj 1
    rw [iteratedDeriv_one] at h1
    rw [hu]
    exact h1
  refine ⟨u, ?_, ?_, fun hu0 ↦ ?_⟩
  · rw [← hg]; exact hfn
  · refine (theorem_8_12 hI hp _).2 fun x hx ↦ ?_
    rw [hfr] at hx
    rcases hx with rfl | rfl
    · rw [hrep0 0 (left_mem_Icc.2 zero_le_one), hg]; ring
    · rw [hrep0 1 (right_mem_Icc.2 zero_le_one), hg]; ring
  · have := (remark_8_18_of_bounded (zero_lt_one' ℝ) hp u).1 hu0 1 0
      (by rw [frontier_Ioo zero_lt_one]; simp)
    rw [hrep1 0 (left_mem_Icc.2 zero_le_one), hderiv] at this
    norm_num at this

/-! ### The dual space $W^{-1,p'}(I)$ -/

/-- **Section 8.3** of [brezis2011functional], notation for the dual space of $W_0^{1,p}(I)$. Let
$I \subseteq \mathbb{R}$ be open and $1 \le p \le \infty$. The dual space of $W_0^{1,p}(I)$, the
space of continuous linear functionals on $W_0^{1,p}(I)$, is denoted by $W^{-1,p'}(I)$.

**Generalization.** The source assumes $p < \infty$. The strong dual also exists at
$p = \infty$, since `Brezis.Chapter08.sobolevSpaceZero` includes that exponent.

The type is the backbone's `SobolevIntervalLpDual p I`, the strong dual of
`SobolevIntervalLpZero 1 p I`.

**Generalization.** The dual is defined on arbitrary open sets and includes $p=\infty$. -/
abbrev sobolevSpaceDual (p : ℝ≥0∞) [Fact (1 ≤ p)] (I : Opens ℝ) : Type := SobolevIntervalLpDual p I

/-- **Section 8.3** of [brezis2011functional], notation. The dual space of $H_0^1(I)$ is denoted by
$H^{-1}(I)$.

**Generalization.** The notation applies on arbitrary open sets. -/
abbrev Hneg1 (I : Opens ℝ) : Type := sobolevSpaceDual 2 I

/-- **Section 8.3** of [brezis2011functional], the inclusions
$H_0^1 \subseteq L^2 \subseteq H^{-1}$. Let $I$ be an open interval. The inclusion
$H_0^1(I) \to L^2(I)$ of the functions and the map $L^2(I) \to H^{-1}(I)$,
$f \mapsto (u \mapsto \int_I f u)$, are continuous, injective, and have dense range.

The source identifies $L^2$ with its dual, but not $H_0^1$ (Remark 3 of Chapter 5). The two maps
are the continuous linear maps `SobolevIntervalLpZero.toL2` and `SobolevIntervalLpDual.ofL2`. -/
theorem inclusions_H10_L2_Hneg1 (hI : (I : Set ℝ).OrdConnected) :
    Function.Injective (SobolevIntervalLpZero.toL2 2 I hI le_rfl) ∧
      DenseRange (SobolevIntervalLpZero.toL2 2 I hI le_rfl) ∧
      Function.Injective (SobolevIntervalLpDual.ofL2 2 I hI le_rfl) ∧
      DenseRange (SobolevIntervalLpDual.ofL2 2 I hI le_rfl) :=
  have : Fact ((1 : ℝ≥0∞) < 2) := ⟨ENNReal.one_lt_two⟩
  ⟨SobolevIntervalLpZero.toL2_injective hI le_rfl, SobolevIntervalLpZero.denseRange_toL2 hI le_rfl,
    SobolevIntervalLpDual.ofL2_injective hI le_rfl, SobolevIntervalLpDual.denseRange_ofL2 hI le_rfl⟩

/-- **Section 8.3** of [brezis2011functional], the inclusions
$W_0^{1,p} \subseteq L^2 \subseteq W^{-1,p'}$ on a bounded interval. Let $a < b$ and
$1 \le p < \infty$. The inclusion $W_0^{1,p}((a, b)) \to L^2((a, b))$ and the map
$L^2((a, b)) \to W^{-1,p'}((a, b))$, $f \mapsto (u \mapsto \int_a^b f u)$, are continuous and
injective. For $1 < p < \infty$ both maps have dense range.

The maps are `SobolevIntervalLpZero.toL2OfBounded` and `SobolevIntervalLpDual.ofL2OfBounded`.
The finite-exponent assumption is used to obtain density in the dual. -/
theorem inclusions_W1p_L2_of_bounded {a b : ℝ} (hab : a < b) (_hp : p ≠ ∞) :
    Function.Injective (SobolevIntervalLpZero.toL2OfBounded p hab) ∧
      Function.Injective (SobolevIntervalLpDual.ofL2OfBounded p hab) ∧
      (1 < p → DenseRange (SobolevIntervalLpZero.toL2OfBounded p hab) ∧
        DenseRange (SobolevIntervalLpDual.ofL2OfBounded p hab)) :=
  ⟨SobolevIntervalLpZero.toL2OfBounded_injective hab,
    SobolevIntervalLpDual.ofL2OfBounded_injective hab, fun hp1 ↦
      have : Fact (1 < p) := ⟨hp1⟩
      have : Fact (p ≠ ∞) := ⟨_hp⟩
      ⟨SobolevIntervalLpZero.denseRange_toL2OfBounded hab,
        SobolevIntervalLpDual.denseRange_ofL2OfBounded hab⟩⟩

/-- **Section 8.3** of [brezis2011functional], the inclusions
$W_0^{1,p} \subseteq L^2 \subseteq W^{-1,p'}$ on an unbounded interval. Let $I$ be an unbounded
open interval and $1 \le p \le 2$. The inclusion $W_0^{1,p}(I) \to L^2(I)$ and the map
$L^2(I) \to W^{-1,p'}(I)$, $f \mapsto (u \mapsto \int_I f u)$, are continuous and injective.

On an unbounded interval the inclusion into $L^2$ needs $p \le 2$, by Remark 12. The maps are
`SobolevIntervalLpZero.toL2` and `SobolevIntervalLpDual.ofL2`. The proof does not use that $I$
is unbounded. -/
theorem inclusions_W1p_L2_of_unbounded (hI : (I : Set ℝ).OrdConnected)
    (_hunb : ¬ Bornology.IsBounded (I : Set ℝ)) (hp : p ≤ 2) :
    Function.Injective (SobolevIntervalLpZero.toL2 p I hI hp) ∧
      Function.Injective (SobolevIntervalLpDual.ofL2 p I hI hp) :=
  ⟨SobolevIntervalLpZero.toL2_injective hI hp, SobolevIntervalLpDual.ofL2_injective hI hp⟩

/-- **Proposition 8.14** of [brezis2011functional]. Let $I \subseteq \mathbb{R}$ be open,
$1 \le p < \infty$ with conjugate exponent $p'$, and $F \in W^{-1,p'}(I)$. Then there are
$f_0, f_1 \in L^{p'}(I)$ such that
$$\langle F, u \rangle = \int_I f_0 u + \int_I f_1 u' \quad \text{for all } u \in
  W_0^{1,p}(I),$$
and $\|F\|_{W^{-1,p'}} = \|(f_0, f_1)\|$, the norm of the pair in the $\ell^{p'}$ product of two
copies of $L^{p'}(I)$.

**Reading.** The source prints $\|F\| = \max(\|f_0\|_{L^{p'}}, \|f_1\|_{L^{p'}})$. That identity
is for the norm $\|u\|_{L^p} + \|u'\|_{L^p}$ on $W^{1,p}(I)$. The type carries the equivalent
norm $(\|u\|_{L^p}^p + \|u'\|_{L^p}^p)^{1/p}$, whose dual norm is the $\ell^{p'}$ norm of the
pair, $(\|f_0\|_{L^{p'}}^{p'} + \|f_1\|_{L^{p'}}^{p'})^{1/p'}$. The two norms on $W^{1,p}(I)$
agree for $p = 1$.

The pair is an element `f` of `PiLp q`, with $f_0$ = `f 0` and $f_1$ = `f 1`. The proof
specializes `SobolevIntervalLpDual.exists_repr`, by the Hahn–Banach and the Riesz representation
theorems as in the source.

**Generalization.** The representation applies on arbitrary open sets. -/
theorem proposition_8_14 {q : ℝ≥0∞} [p.HolderConjugate q] (hp : p ≠ ∞)
    (F : sobolevSpaceDual p I) :
    ∃ f : PiLp q (fun _ : Fin 2 ↦ Lp ℝ q (volume.restrict (I : Set ℝ))),
      (∀ u : sobolevSpaceZero p I,
        F u = (∫ x in (I : Set ℝ), f 0 x * (u : SobolevIntervalLp 1 p I).fn x)
          + ∫ x in (I : Set ℝ), f 1 x * (u : SobolevIntervalLp 1 p I).deriv 1 x) ∧
      ‖F‖ = ‖f‖ :=
  SobolevIntervalLpDual.exists_repr hp F

/-- **Proposition 8.14** of [brezis2011functional], the bounded case. Let $a < b$,
$1 \le p < \infty$ with conjugate exponent $p'$, and $F \in W^{-1,p'}((a, b))$. Then there is
$f_1 \in L^{p'}((a, b))$ with
$$\langle F, u \rangle = \int_a^b f_1 u' \quad \text{for all } u \in W_0^{1,p}((a, b)).$$
So when $I$ is bounded one can take $f_0 = 0$.

Poincaré's inequality makes $u \mapsto u'$ an isomorphism onto its range. The proof specializes
`SobolevIntervalLpDual.exists_repr_of_bounded`.

**Reading.** The printed proof changes to the equivalent derivative-only norm. The library
concludes existence of the derivative-only representation with the original dual norm in use. -/
theorem proposition_8_14_bounded {q : ℝ≥0∞} [p.HolderConjugate q] (hp : p ≠ ∞) {a b : ℝ}
    (hab : a < b) (F : sobolevSpaceDual p (Opens.Ioo a b)) :
    ∃ f₁ : Lp ℝ q (volume.restrict (Ioo a b)), ∀ u : sobolevSpaceZero p (Opens.Ioo a b),
      F u = ∫ x in Ioo a b, f₁ x * (u : SobolevIntervalLp 1 p (Opens.Ioo a b)).deriv 1 x :=
  SobolevIntervalLpDual.exists_repr_of_bounded hp hab F

/-- **Remark 19** in Chapter 8 of [brezis2011functional]. Let $I \subseteq \mathbb{R}$ be open,
$1 \le p \le \infty$ with conjugate exponent $p'$, $f_0, f_1 \in L^{p'}(I)$,
$g \in C_c^\infty(I)$ and $u \in W_0^{1,p}(I)$. Then
$$\int_I (f_0 + g') u + \int_I (f_1 + g) u' = \int_I f_0 u + \int_I f_1 u'.$$
So the pairs $(f_0 + g', f_1 + g)$ and $(f_0, f_1)$ represent the same functional, and the
functions $f_0$ and $f_1$ of Proposition 8.14 are not uniquely determined by $F$.

The identity holds since $\int_I g' u = -\int_I g u'$ for $u \in W_0^{1,p}(I)$. The proof
specializes `SobolevIntervalLpDual.repr_not_unique`.

**Generalization.** The identity applies on arbitrary open sets and includes $p=\infty$. -/
theorem remark_8_19 {q : ℝ≥0∞} [p.HolderConjugate q] {f₀ f₁ : ℝ → ℝ}
    (hf₀ : MemLp f₀ q (volume.restrict I)) (hf₁ : MemLp f₁ q (volume.restrict I)) (g : 𝓓(I, ℝ))
    (u : sobolevSpaceZero p I) :
    (∫ x in (I : Set ℝ), (f₀ x + deriv g x) * (u : SobolevIntervalLp 1 p I).fn x)
        + ∫ x in (I : Set ℝ), (f₁ x + g x) * (u : SobolevIntervalLp 1 p I).deriv 1 x
      = (∫ x in (I : Set ℝ), f₀ x * (u : SobolevIntervalLp 1 p I).fn x)
        + ∫ x in (I : Set ℝ), f₁ x * (u : SobolevIntervalLp 1 p I).deriv 1 x :=
  SobolevIntervalLpDual.repr_not_unique hf₀ hf₁ g (u : SobolevIntervalLp 1 p I)

/-- **Remark 21** in Chapter 8 of [brezis2011functional]. Let $I \subseteq \mathbb{R}$ be open,
$1 \le p < \infty$ with conjugate exponent $p'$, and let $F$ be a continuous linear functional
on $W^{1,p}(I)$. Then there are $f_0, f_1 \in L^{p'}(I)$ with
$$\langle F, u \rangle = \int_I f_0 u + \int_I f_1 u' \quad \text{for all } u \in W^{1,p}(I).$$
So the first assertion of Proposition 8.14 also holds for functionals on $W^{1,p}(I)$.

The proof specializes `SobolevIntervalLp.exists_repr_strongDual`.

**Generalization.** The representation applies on arbitrary open sets. -/
theorem remark_8_21 {q : ℝ≥0∞} [p.HolderConjugate q] (hp : p ≠ ∞)
    (F : StrongDual ℝ (SobolevIntervalLp 1 p I)) :
    ∃ f : PiLp q (fun _ : Fin 2 ↦ Lp ℝ q (volume.restrict (I : Set ℝ))),
      ∀ u : SobolevIntervalLp 1 p I,
        F u = (∫ x in (I : Set ℝ), f 0 x * u.fn x) + ∫ x in (I : Set ℝ), f 1 x * u.deriv 1 x :=
  let ⟨f, hf, _⟩ := SobolevIntervalLp.exists_repr_strongDual hp F
  ⟨f, hf⟩

end Brezis.Chapter08
