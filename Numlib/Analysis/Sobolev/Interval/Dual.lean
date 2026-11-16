/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/Interval/Basic.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Normed.Lp.PiLpDual
import Numlib.Analysis.Sobolev.Interval.Zero

/-!
# The dual space $W^{-1,p'}(I)$ of $W_0^{1,p}(I)$

Let $I \subseteq \mathbb{R}$ be open, let $1 \le p \le \infty$ and let $p'$ be the conjugate
exponent. This module studies the dual space $W^{-1,p'}(I)$ of $W_0^{1,p}(I)$, following §8.3 of
[brezis2011functional], "The dual space of $W_0^{1,p}(I)$". It gives the inclusions
$$W_0^{1,p}(I) \subseteq L^2(I) \subseteq W^{-1,p'}(I),$$
which are continuous and injective, and have dense range under conditions on $p$; at $p = 2$ these
are the inclusions $H_0^1 \subseteq L^2 \subseteq H^{-1}$. It proves the representation of
Proposition 8.14 and Remark 21 of [brezis2011functional]: for $1 \le p < \infty$, every
$F \in W^{-1,p'}(I)$ has the form
$$\langle F, u \rangle = \int_I f_0 u + \int_I f_1 u', \qquad f_0, f_1 \in L^{p'}(I),$$
and the norm of $F$ is the norm of the pair $(f_0, f_1)$. By Remark 19 of [brezis2011functional],
the pair $(f_0, f_1)$ is not unique.

## Main definitions

* `SobolevIntervalLpDual`: the space $W^{-1,p'}(I)$, the strong dual of $W_0^{1,p}(I)$; $H^{-1}(I)$
  at $p = 2$.
* `SobolevIntervalLpZero.toL2`: the inclusion $W_0^{1,p}(I) \subseteq L^2(I)$ for an interval $I$
  and $p \le 2$.
* `SobolevIntervalLpZero.toL2OfBounded`: the inclusion $W_0^{1,p}(a, b) \subseteq L^2(a, b)$ for
  every $p$.
* `SobolevIntervalLpDual.ofL2` and `SobolevIntervalLpDual.ofL2OfBounded`: the inclusion
  $L^2(I) \subseteq W^{-1,p'}(I)$, $f \mapsto (u \mapsto \int_I f u)$, the transpose of the previous
  inclusions through the self-duality of $L^2$.

## Main results

* `SobolevIntervalLpZero.toL2_injective`, `SobolevIntervalLpZero.toL2OfBounded_injective`,
  `SobolevIntervalLpZero.denseRange_toL2` and `SobolevIntervalLpZero.denseRange_toL2OfBounded`: the
  inclusion $W_0^{1,p}(I) \subseteq L^2(I)$ is injective and has dense range.
* `SobolevIntervalLpDual.ofL2_injective` and `SobolevIntervalLpDual.ofL2OfBounded_injective`: the
  inclusion $L^2(I) \subseteq W^{-1,p'}(I)$ is injective.
* `SobolevIntervalLpDual.denseRange_ofL2` and `SobolevIntervalLpDual.denseRange_ofL2OfBounded`: for
  $1 < p < \infty$ the inclusion $L^2(I) \subseteq W^{-1,p'}(I)$ has dense range, by the reflexivity
  of $W_0^{1,p}(I)$.
* `SobolevIntervalLp.exists_repr_strongDual`: for $1 \le p < \infty$, every continuous linear
  functional on $W^{1,p}(I)$ is $u \mapsto \int_I f_0 u + \int_I f_1 u'$ with
  $f_0, f_1 \in L^{p'}(I)$, and its norm is the $\ell^{p'}$ norm of $(\|f_0\|, \|f_1\|)$ (Remark 21
  of [brezis2011functional]).
* `SobolevIntervalLpDual.exists_repr`: the same representation for $F \in W^{-1,p'}(I)$ (Proposition
  8.14 of [brezis2011functional]).
* `SobolevIntervalLpDual.exists_repr_of_bounded`: on a bounded interval one can take $f_0 = 0$.
* `SobolevIntervalLpDual.repr_not_unique`: the pairs $(f_0, f_1)$ and $(f_0 + g', f_1 + g)$, $g$ a
  test function, define the same functional (Remark 19 of [brezis2011functional]).

## Implementation notes

* The norm identity of Proposition 8.14 is stated for the norm of the type. The space $W^{1,p}(I)$
  sits isometrically in the $\ell^p$ product of two copies of $L^p(I)$, so the dual norm of the
  representing pair is its $\ell^{p'}$ norm $(\|f_0\|_{p'}^{p'} + \|f_1\|_{p'}^{p'})^{1/p'}$. At
  $p = 1$ this is $\max\{\|f_0\|_\infty, \|f_1\|_\infty\}$; there the norm of the type is the sum
  norm of [brezis2011functional], and the identity is the identity of the source. The general step
  is the duality of a finite $\ell^p$ product, `PiLp.norm_strongDual_eq` in
  `Numlib.Analysis.Normed.Lp.PiLpDual`.
* The inclusion $W_0^{1,p}(I) \subseteq L^2(I)$ is `SobolevIntervalLp.toLp` (Remark 12 of
  [brezis2011functional]) restricted to $W_0^{1,p}(I)$ when $p \le 2$, and
  `SobolevIntervalLp.toLpOfBounded` restricted to $W_0^{1,p}(a, b)$ on a bounded interval. The
  properties of $L^2 \subseteq W^{-1,p'}$ are proved once for any continuous linear map
  $T : W_0^{1,p}(I) \to L^2(I)$ whose values are the functions (`SobolevIntervalLpDual.ofL2Of`), and
  then specialized.
* The conjugate exponent $p'$ is written `q`, with the hypothesis `ENNReal.HolderConjugate p q`.
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology

noncomputable section

/-! ### The space $W^{-1,p'}(I)$ -/

/-- **The dual space $W^{-1,p'}(I)$ of $W_0^{1,p}(I)$.** For $1 \le p \le \infty$ and an open set
$I \subseteq \mathbb{R}$, $W^{-1,p'}(I)$ is the space of continuous linear functionals on
$W_0^{1,p}(I)$, with the dual norm. At $p = 2$ it is $H^{-1}(I)$. This is the notation of §8.3
of [brezis2011functional].

It is the strong dual `StrongDual ℝ (SobolevIntervalLpZero 1 p I)`, and it is a Banach space
because it is a dual space. -/
abbrev SobolevIntervalLpDual (p : ℝ≥0∞) [Fact (1 ≤ p)] (I : Opens ℝ) : Type :=
  StrongDual ℝ (SobolevIntervalLpZero 1 p I)

/-! ### The inclusion $W_0^{1,p}(I) \subseteq L^2(I)$ -/

namespace SobolevIntervalLpZero

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {I : Opens ℝ}

open SobolevIntervalLp

variable (p I) in
/-- **The inclusion $W_0^{1,p}(I) \subseteq L^2(I)$ for $p \le 2$.** Let $I \subseteq \mathbb{R}$ be
an open interval and $1 \le p \le 2$. This is the continuous linear map
$W_0^{1,p}(I) \to L^2(I)$ that sends $u$ to its function. It is one of the inclusions
$W_0^{1,p} \subseteq L^2 \subseteq W^{-1,p'}$ of §8.3 of [brezis2011functional], for an interval
that may be unbounded.

It is the inclusion $W^{1,p}(I) \subseteq L^2(I)$ of Remark 12 of [brezis2011functional],
`SobolevIntervalLp.toLp`, restricted to $W_0^{1,p}(I)$. -/
def toL2 (hI : (I : Set ℝ).OrdConnected) (hp : p ≤ 2) :
    SobolevIntervalLpZero 1 p I →L[ℝ] Lp ℝ 2 (volume.restrict (I : Set ℝ)) :=
  (SobolevIntervalLp.toLp p hI hp).comp (SobolevIntervalLpZero 1 p I).subtypeL

/-- Let $I \subseteq \mathbb{R}$ be an open interval, $1 \le p \le 2$ and $u \in W_0^{1,p}(I)$. The
image of $u$ under `SobolevIntervalLpZero.toL2` agrees almost everywhere on $I$ with the
function of $u$. -/
theorem coeFn_toL2 (hI : (I : Set ℝ).OrdConnected) (hp : p ≤ 2) (u : SobolevIntervalLpZero 1 p I) :
    ⇑(toL2 p I hI hp u) =ᵐ[volume.restrict I] fn (u : SobolevIntervalLp 1 p I) := by
  rw [toL2, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  exact coeFn_toLp hI hp u

variable {a b : ℝ}

variable (p) in
/-- **The inclusion $W_0^{1,p}(a, b) \subseteq L^2(a, b)$ on a bounded interval.** Let $a < b$ and
$1 \le p \le \infty$. This is the continuous linear map $W_0^{1,p}(a, b) \to L^2(a, b)$ that
sends $u$ to its function. It is one of the inclusions
$W_0^{1,p} \subseteq L^2 \subseteq W^{-1,p'}$ of §8.3 of [brezis2011functional], for a bounded
interval.

It is `SobolevIntervalLp.toLpOfBounded` restricted to $W_0^{1,p}(a, b)$. -/
def toL2OfBounded (hab : a < b) :
    SobolevIntervalLpZero 1 p (Opens.Ioo a b) →L[ℝ] Lp ℝ 2 (volume.restrict (Ioo a b)) :=
  (SobolevIntervalLp.toLpOfBounded p hab 2).comp
    (SobolevIntervalLpZero 1 p (Opens.Ioo a b)).subtypeL

/-- Let $a < b$, $1 \le p \le \infty$ and $u \in W_0^{1,p}(a, b)$. The image of $u$ under
`SobolevIntervalLpZero.toL2OfBounded` agrees almost everywhere on $(a, b)$ with the function of
$u$. -/
theorem coeFn_toL2OfBounded (hab : a < b) (u : SobolevIntervalLpZero 1 p (Opens.Ioo a b)) :
    ⇑(toL2OfBounded p hab u) =ᵐ[volume.restrict (Ioo a b)]
      fn (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) := by
  rw [toL2OfBounded, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  exact coeFn_toLpOfBounded hab 2 (u : SobolevIntervalLp 1 p (Opens.Ioo a b))

/-- Let $I \subseteq \mathbb{R}$ be open and $1 \le p \le \infty$. Let $T : W_0^{1,p}(I) \to L^2(I)$
be a continuous linear map such that $Tu$ agrees almost everywhere on $I$ with the function of
$u$, for every $u$. Then $T$ is injective.

Two elements of $W^{1,p}(I)$ with the same function are equal
(`SobolevMultiIndex.ext_of_fn_ae_eq`). -/
theorem injective_of_coeFn_ae_eq (T : SobolevIntervalLpZero 1 p I →L[ℝ]
      Lp ℝ 2 (volume.restrict (I : Set ℝ)))
    (hT : ∀ u, ⇑(T u) =ᵐ[volume.restrict I] fn (u : SobolevIntervalLp 1 p I)) :
    Function.Injective T := by
  intro u v huv
  refine Subtype.ext (SobolevMultiIndex.ext_of_fn_ae_eq ?_)
  refine (hT u).symm.trans ?_
  rw [huv]
  exact hT v

/-- Let $I \subseteq \mathbb{R}$ be an open interval and $1 \le p \le 2$. The inclusion
$W_0^{1,p}(I) \subseteq L^2(I)$ is injective. -/
theorem toL2_injective (hI : (I : Set ℝ).OrdConnected) (hp : p ≤ 2) :
    Function.Injective (toL2 p I hI hp) :=
  injective_of_coeFn_ae_eq _ (coeFn_toL2 hI hp)

/-- Let $a < b$ and $1 \le p \le \infty$. The inclusion $W_0^{1,p}(a, b) \subseteq L^2(a, b)$ is
injective. -/
theorem toL2OfBounded_injective (hab : a < b) : Function.Injective (toL2OfBounded p hab) :=
  injective_of_coeFn_ae_eq _ (coeFn_toL2OfBounded hab)

/-- Let $I \subseteq \mathbb{R}$ be open and $1 \le p \le \infty$. Let $T : W_0^{1,p}(I) \to L^2(I)$
be a continuous linear map such that $Tu$ agrees almost everywhere on $I$ with the function of
$u$, for every $u$. Then $T$ has dense range.

The range of $T$ contains the test functions, which are dense in $L^2(I)$
(`MeasureTheory.Lp.dense_contDiff_tsupport_subset`). -/
theorem denseRange_of_coeFn_ae_eq (T : SobolevIntervalLpZero 1 p I →L[ℝ]
      Lp ℝ 2 (volume.restrict (I : Set ℝ)))
    (hT : ∀ u, ⇑(T u) =ᵐ[volume.restrict I] fn (u : SobolevIntervalLp 1 p I)) :
    DenseRange T := by
  refine (Lp.dense_contDiff_tsupport_subset (F := ℝ) (μ := volume) (p := 2) I.isOpen
    ENNReal.ofNat_ne_top).mono ?_
  rintro f ⟨g, hfg, hgc, hgs, hgI⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : 𝓓(I, ℝ), (φ : ℝ → ℝ) = g := ⟨⟨g, hgs, hgc, hgI⟩, rfl⟩
  refine ⟨⟨TestFunction.toSobolevIntervalLp p φ, TestFunction.toSobolevIntervalLp_mem (p := p) φ⟩,
    ?_⟩
  refine Lp.ext ((hT _).trans ?_)
  refine (TestFunction.fn_toSobolevIntervalLp_ae_eq (p := p) φ).trans ?_
  rw [hφ]
  exact hfg.symm

/-- Let $I \subseteq \mathbb{R}$ be an open interval and $1 \le p \le 2$. The inclusion
$W_0^{1,p}(I) \subseteq L^2(I)$ has dense range. -/
theorem denseRange_toL2 (hI : (I : Set ℝ).OrdConnected) (hp : p ≤ 2) :
    DenseRange (toL2 p I hI hp) :=
  denseRange_of_coeFn_ae_eq _ (coeFn_toL2 hI hp)

/-- Let $a < b$ and $1 \le p \le \infty$. The inclusion $W_0^{1,p}(a, b) \subseteq L^2(a, b)$ has
dense range. -/
theorem denseRange_toL2OfBounded (hab : a < b) : DenseRange (toL2OfBounded p hab) :=
  denseRange_of_coeFn_ae_eq _ (coeFn_toL2OfBounded hab)

end SobolevIntervalLpZero

/-! ### The inclusion $L^2(I) \subseteq W^{-1,p'}(I)$ -/

namespace SobolevIntervalLpDual

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {I : Opens ℝ}

open SobolevIntervalLp

/-- **The inclusion $L^2(I) \subseteq W^{-1,p'}(I)$ along a map $T$.** Let $I \subseteq \mathbb{R}$
be open, $1 \le p \le \infty$, and let $T : W_0^{1,p}(I) \to L^2(I)$ be a continuous linear map.
This is the continuous linear map $L^2(I) \to W^{-1,p'}(I)$ given by
$$f \mapsto \Big(u \mapsto \int_I f \cdot Tu\Big).$$

It is the transpose of $T$ composed with the self-duality of $L^2(I)$, the $L^p$–$L^q$ pairing
`MeasureTheory.Lp.toDualCLM` at $p = q = 2$. -/
def ofL2Of (T : SobolevIntervalLpZero 1 p I →L[ℝ] Lp ℝ 2 (volume.restrict (I : Set ℝ))) :
    Lp ℝ 2 (volume.restrict (I : Set ℝ)) →L[ℝ] SobolevIntervalLpDual p I :=
  ((ContinuousLinearMap.compL ℝ (SobolevIntervalLpZero 1 p I)
    (Lp ℝ 2 (volume.restrict (I : Set ℝ))) ℝ).flip T).comp
    (Lp.toDualCLM ℝ 2 2 (volume.restrict (I : Set ℝ)))

/-- Let $T : W_0^{1,p}(I) \to L^2(I)$ be a continuous linear map, $f \in L^2(I)$ and
$u \in W_0^{1,p}(I)$. Then the functional `SobolevIntervalLpDual.ofL2Of T f` takes at $u$ the
value $\int_I f \cdot Tu$. -/
theorem ofL2Of_apply (T : SobolevIntervalLpZero 1 p I →L[ℝ] Lp ℝ 2 (volume.restrict (I : Set ℝ)))
    (f : Lp ℝ 2 (volume.restrict (I : Set ℝ))) (u : SobolevIntervalLpZero 1 p I) :
    ofL2Of T f u = ∫ x in (I : Set ℝ), f x * T u x := by
  simp only [ofL2Of, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, Lp.toDualCLM_apply]

/-- Let $T : W_0^{1,p}(I) \to L^2(I)$ be a continuous linear map such that $Tu$ agrees almost
everywhere on $I$ with the function of $u$, for every $u$. Then for $f \in L^2(I)$ and
$u \in W_0^{1,p}(I)$, the functional `SobolevIntervalLpDual.ofL2Of T f` takes at $u$ the value
$\int_I f u$. -/
theorem ofL2Of_apply_eq_integral_mul_fn
    (T : SobolevIntervalLpZero 1 p I →L[ℝ] Lp ℝ 2 (volume.restrict (I : Set ℝ)))
    (hT : ∀ u, ⇑(T u) =ᵐ[volume.restrict I] fn (u : SobolevIntervalLp 1 p I))
    (f : Lp ℝ 2 (volume.restrict (I : Set ℝ))) (u : SobolevIntervalLpZero 1 p I) :
    ofL2Of T f u = ∫ x in (I : Set ℝ), f x * fn (u : SobolevIntervalLp 1 p I) x := by
  rw [ofL2Of_apply]
  exact integral_congr_ae ((hT u).mono fun x hx ↦ by simp only [hx])

/-- Let $I \subseteq \mathbb{R}$ be open, $1 \le p \le \infty$, and let
$T : W_0^{1,p}(I) \to L^2(I)$ be a continuous linear map such that $Tu$ agrees almost everywhere
on $I$ with the function of $u$, for every $u$. Then the map $L^2(I) \to W^{-1,p'}(I)$,
$f \mapsto (u \mapsto \int_I f u)$, is injective.

A function of $L^2(I)$ whose integral against every test function vanishes is zero. -/
theorem ofL2Of_injective
    (T : SobolevIntervalLpZero 1 p I →L[ℝ] Lp ℝ 2 (volume.restrict (I : Set ℝ)))
    (hT : ∀ u, ⇑(T u) =ᵐ[volume.restrict I] fn (u : SobolevIntervalLp 1 p I)) :
    Function.Injective (ofL2Of T) := by
  refine (injective_iff_map_eq_zero _).2 fun f hf ↦ ?_
  have hloc : LocallyIntegrableOn (⇑f) I (volume.restrict (I : Set ℝ)) :=
    ((Lp.memLp f).locallyIntegrable one_le_two).locallyIntegrableOn _
  have key := I.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun g hgs hgc hgI ↦ ?_
  · refine Lp.ext ?_
    filter_upwards [key, ae_restrict_mem I.isOpen.measurableSet, Lp.coeFn_zero ℝ 2
      (volume.restrict (I : Set ℝ))] with x hx hxI hx0
    rw [hx hxI, hx0]
    rfl
  · obtain ⟨φ, hφ⟩ : ∃ φ : 𝓓(I, ℝ), (φ : ℝ → ℝ) = g := ⟨⟨g, hgs, hgc, hgI⟩, rfl⟩
    have h1 := DFunLike.congr_fun hf
      ⟨TestFunction.toSobolevIntervalLp p φ, TestFunction.toSobolevIntervalLp_mem (p := p) φ⟩
    rw [ofL2Of_apply_eq_integral_mul_fn T hT, zero_apply] at h1
    rw [← h1, ← hφ]
    refine integral_congr_ae
      ((TestFunction.fn_toSobolevIntervalLp_ae_eq (p := p) φ).mono fun x hx ↦ ?_)
    simp only [smul_eq_mul, mul_comm, hx]

/-- Let $I \subseteq \mathbb{R}$ be open, $1 < p < \infty$, and let $T : W_0^{1,p}(I) \to L^2(I)$ be
a continuous linear map such that $Tu$ agrees almost everywhere on $I$ with the function of $u$,
for every $u$. Then the map $L^2(I) \to W^{-1,p'}(I)$, $f \mapsto (u \mapsto \int_I f u)$, has
dense range.

By the reflexivity of $W_0^{1,p}(I)$ (`SobolevMultiIndexZero.instIsReflexive`), a functional on
$W^{-1,p'}(I)$ that vanishes on the range is the evaluation at some $v \in W_0^{1,p}(I)$. Then
$\int_I f v = 0$ for all $f \in L^2(I)$, in particular for $f = Tv$, so $Tv = 0$ and $v = 0$. A
closed proper subspace would be separated from a point by a nonzero functional
(`Submodule.exists_dual_eq_zero_of_notMem`). -/
theorem denseRange_ofL2Of [Fact (1 < p)] [Fact (p ≠ ⊤)]
    (T : SobolevIntervalLpZero 1 p I →L[ℝ] Lp ℝ 2 (volume.restrict (I : Set ℝ)))
    (hT : ∀ u, ⇑(T u) =ᵐ[volume.restrict I] fn (u : SobolevIntervalLp 1 p I)) :
    DenseRange (ofL2Of T) := by
  have hTinj := SobolevIntervalLpZero.injective_of_coeFn_ae_eq T hT
  obtain ⟨M, hM⟩ : ∃ M : Submodule ℝ (SobolevIntervalLpDual p I),
      M = (LinearMap.range (ofL2Of T : Lp ℝ 2 (volume.restrict (I : Set ℝ)) →ₗ[ℝ]
        SobolevIntervalLpDual p I)).topologicalClosure := ⟨_, rfl⟩
  have hMtop : M = ⊤ := by
    by_contra hne
    obtain ⟨z, -, hz⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.2 hne)
    obtain ⟨Λ, -, hΛ0, hΛz⟩ :=
      M.exists_dual_eq_zero_of_notMem (hM ▸ Submodule.isClosed_topologicalClosure _) hz
    obtain ⟨v, rfl⟩ := NormedSpace.surjective_inclusionInDoubleDual (𝕜 := ℝ) Λ
    have hv : ∀ f : Lp ℝ 2 (volume.restrict (I : Set ℝ)), ofL2Of T f v = 0 := fun f ↦ by
      have := hΛ0 (ofL2Of T f) (hM ▸ Submodule.le_topologicalClosure _ ⟨f, rfl⟩)
      rwa [NormedSpace.dual_def] at this
    have hTv : T v = 0 := by
      have h := hv (T v)
      rw [ofL2Of_apply] at h
      have h2 : ∫ x in (I : Set ℝ), (T v) x * (T v) x = ‖T v‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, L2.inner_def]
        exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp [pow_two])
      rw [h2] at h
      exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h)
    have hv0 : v = 0 := hTinj (hTv.trans (map_zero T).symm)
    apply hΛz
    rw [hv0, map_zero]
    rfl
  have hrange : Set.range (ofL2Of T) = ((LinearMap.range (ofL2Of T :
      Lp ℝ 2 (volume.restrict (I : Set ℝ)) →ₗ[ℝ] SobolevIntervalLpDual p I)) : Set _) := by
    rw [LinearMap.coe_range, ContinuousLinearMap.coe_coe]
  rw [DenseRange, hrange, Submodule.dense_iff_topologicalClosure_eq_top, ← hM, hMtop]

variable (p I) in
/-- **The inclusion $L^2(I) \subseteq W^{-1,p'}(I)$ for $p \le 2$.** Let $I \subseteq \mathbb{R}$ be
an open interval and $1 \le p \le 2$. This is the continuous linear map
$L^2(I) \to W^{-1,p'}(I)$, $f \mapsto (u \mapsto \int_I f u)$. It is one of the inclusions
$W_0^{1,p} \subseteq L^2 \subseteq W^{-1,p'}$ of §8.3 of [brezis2011functional].

It is the transpose of `SobolevIntervalLpZero.toL2` through the self-duality of $L^2(I)$. -/
def ofL2 (hI : (I : Set ℝ).OrdConnected) (hp : p ≤ 2) :
    Lp ℝ 2 (volume.restrict (I : Set ℝ)) →L[ℝ] SobolevIntervalLpDual p I :=
  ofL2Of (SobolevIntervalLpZero.toL2 p I hI hp)

/-- Let $I \subseteq \mathbb{R}$ be an open interval, $1 \le p \le 2$, $f \in L^2(I)$ and
$u \in W_0^{1,p}(I)$. Then the functional `SobolevIntervalLpDual.ofL2 p I hI hp f` takes at $u$
the value $\int_I f u$. -/
theorem ofL2_apply (hI : (I : Set ℝ).OrdConnected) (hp : p ≤ 2)
    (f : Lp ℝ 2 (volume.restrict (I : Set ℝ))) (u : SobolevIntervalLpZero 1 p I) :
    ofL2 p I hI hp f u = ∫ x in (I : Set ℝ), f x * fn (u : SobolevIntervalLp 1 p I) x :=
  ofL2Of_apply_eq_integral_mul_fn _ (SobolevIntervalLpZero.coeFn_toL2 hI hp) f u

/-- Let $I \subseteq \mathbb{R}$ be an open interval and $1 \le p \le 2$. The inclusion
$L^2(I) \subseteq W^{-1,p'}(I)$ is injective. -/
theorem ofL2_injective (hI : (I : Set ℝ).OrdConnected) (hp : p ≤ 2) :
    Function.Injective (ofL2 p I hI hp) :=
  ofL2Of_injective _ (SobolevIntervalLpZero.coeFn_toL2 hI hp)

/-- Let $I \subseteq \mathbb{R}$ be an open interval and $1 < p \le 2$. The inclusion
$L^2(I) \subseteq W^{-1,p'}(I)$ has dense range. -/
theorem denseRange_ofL2 [Fact (1 < p)] (hI : (I : Set ℝ).OrdConnected) (hp : p ≤ 2) :
    DenseRange (ofL2 p I hI hp) :=
  have : Fact (p ≠ ⊤) := ⟨ne_top_of_le_ne_top ENNReal.ofNat_ne_top hp⟩
  denseRange_ofL2Of _ (SobolevIntervalLpZero.coeFn_toL2 hI hp)

variable {a b : ℝ}

variable (p) in
/-- **The inclusion $L^2(a, b) \subseteq W^{-1,p'}(a, b)$ on a bounded interval.** Let $a < b$ and
$1 \le p \le \infty$. This is the continuous linear map $L^2(a, b) \to W^{-1,p'}(a, b)$,
$f \mapsto (u \mapsto \int_a^b f u)$, the transpose of `SobolevIntervalLpZero.toL2OfBounded`. -/
def ofL2OfBounded (hab : a < b) :
    Lp ℝ 2 (volume.restrict (Ioo a b)) →L[ℝ] SobolevIntervalLpDual p (Opens.Ioo a b) :=
  ofL2Of (SobolevIntervalLpZero.toL2OfBounded p hab)

/-- Let $a < b$, $1 \le p \le \infty$, $f \in L^2(a, b)$ and $u \in W_0^{1,p}(a, b)$. Then the
functional `SobolevIntervalLpDual.ofL2OfBounded p hab f` takes at $u$ the value $\int_a^b f u$. -/
theorem ofL2OfBounded_apply (hab : a < b) (f : Lp ℝ 2 (volume.restrict (Ioo a b)))
    (u : SobolevIntervalLpZero 1 p (Opens.Ioo a b)) :
    ofL2OfBounded p hab f u
      = ∫ x in Ioo a b, f x * fn (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) x :=
  ofL2Of_apply_eq_integral_mul_fn _ (SobolevIntervalLpZero.coeFn_toL2OfBounded hab) f u

/-- Let $a < b$ and $1 \le p \le \infty$. The inclusion $L^2(a, b) \subseteq W^{-1,p'}(a, b)$ is
injective. -/
theorem ofL2OfBounded_injective (hab : a < b) :
    Function.Injective (ofL2OfBounded p hab) :=
  ofL2Of_injective _ (SobolevIntervalLpZero.coeFn_toL2OfBounded hab)

/-- Let $a < b$ and $1 < p < \infty$. The inclusion $L^2(a, b) \subseteq W^{-1,p'}(a, b)$ has dense
range. This is the statement "dense injections when $1 < p < \infty$" of §8.3 of
[brezis2011functional]. -/
theorem denseRange_ofL2OfBounded [Fact (1 < p)] [Fact (p ≠ ⊤)] (hab : a < b) :
    DenseRange (ofL2OfBounded p hab) :=
  denseRange_ofL2Of _ (SobolevIntervalLpZero.coeFn_toL2OfBounded hab)

end SobolevIntervalLpDual

/-! ### Proposition 8.14 and Remark 21: the representation of functionals -/

section Repr

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] {I : Opens ℝ}

namespace SobolevIntervalLp

/-- Let $I \subseteq \mathbb{R}$ be open, let $1 \le p < \infty$ and let $q$ be the conjugate
exponent. Let $F$ be a continuous linear functional on $W^{1,p}(I)$. Then there are
$f_0, f_1 \in L^q(I)$ such that
$$F(u) = \int_I f_0 u + \int_I f_1 u' \quad \text{for every } u \in W^{1,p}(I),$$
and $\|F\| = \|(f_0, f_1)\|$, the norm in the $\ell^q$ product of two copies of $L^q(I)$. This
is Remark 21 of [brezis2011functional], Chapter 8, with the norm identity of Proposition 8.14
there.

The space $W^{1,p}(I)$ is a closed subspace of the $\ell^p$ product of two copies of $L^p(I)$.
The functional $F$ extends to the product with the same norm (the Hahn–Banach theorem,
`exists_extension_norm_eq`). The restrictions of the extension to the two factors are
represented by $f_0$ and $f_1$ by the Riesz representation theorem
(`MeasureTheory.Lp.exists_forall_eq_integral`). The norm of a functional on an $\ell^p$ product
is the $\ell^q$ norm of the norms of its restrictions (`PiLp.norm_strongDual_eq`). The pair is
an element `f` of `PiLp q (fun _ : Fin 2 ↦ Lp ℝ q _)`, with $f_0$ = `f 0` and $f_1$ = `f 1`. -/
theorem exists_repr_strongDual [ENNReal.HolderConjugate p q] (hp : p ≠ ⊤)
    (F : StrongDual ℝ (SobolevIntervalLp 1 p I)) :
    ∃ f : PiLp q (fun _ : Fin 2 ↦ Lp ℝ q (volume.restrict (I : Set ℝ))),
      (∀ u, F u = (∫ x in (I : Set ℝ), f 0 x * fn u x)
        + ∫ x in (I : Set ℝ), f 1 x * deriv u 1 x) ∧ ‖F‖ = ‖f‖ := by
  classical
  have hq1 : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  obtain ⟨Φ, hΦ, hΦn⟩ := exists_extension_norm_eq
    (SobolevMultiIndex ℝ (Module.Basis.singleton Unit ℝ) 1 p I volume) F
  -- the restrictions of the extension to the two factors, and their representatives
  obtain ⟨ψ, hψ⟩ : ∃ ψ : MultiIndexLE Unit 1 → StrongDual ℝ (Lp ℝ p (volume.restrict (I : Set ℝ))),
      ∀ α, ψ α = Φ.comp (PiLp.singleL p α) := ⟨_, fun _ ↦ rfl⟩
  choose g hg using fun α ↦ Lp.exists_forall_eq_integral (q := q) hp (ψ α)
  have hnorm : ∀ α, ‖ψ α‖ = ‖g α‖ := fun α ↦ by
    have : ψ α = Lp.toDualCLM ℝ p q (volume.restrict (I : Set ℝ)) (g α) :=
      ContinuousLinearMap.ext fun h ↦ by rw [hg, Lp.toDualCLM_apply]
    rw [this, Lp.norm_toDualCLM_apply]
  refine ⟨WithLp.toLp q fun j ↦ g (derivIndex 1 j), fun u ↦ ?_, ?_⟩
  · rw [← hΦ u, PiLp.strongDual_apply_eq_sum]
    simp only [← hψ, hg]
    rw [← (derivIndexEquiv 1).sum_comp, Fin.sum_univ_two]
    rfl
  · rw [← hΦn, PiLp.norm_strongDual_eq (q := q) hp,
      PiLp.norm_eq_norm_toLp_norm (WithLp.toLp q fun j ↦ g (derivIndex 1 j))]
    simp only [← hψ, hnorm]
    exact ((LinearIsometryEquiv.piLpCongrLeft q ℝ ℝ (derivIndexEquiv 1).symm).norm_map
      (WithLp.toLp q fun α ↦ ‖g α‖)).symm

end SobolevIntervalLp

namespace SobolevIntervalLpDual

open SobolevIntervalLp

/-- Let $I \subseteq \mathbb{R}$ be open, let $1 \le p < \infty$ and let $q$ be the conjugate
exponent. For $F \in W^{-1,q}(I)$ there are $f_0, f_1 \in L^q(I)$ such that
$$\langle F, u \rangle = \int_I f_0 u + \int_I f_1 u' \quad \text{for every } u \in
  W_0^{1,p}(I),$$
and $\|F\| = \|(f_0, f_1)\|$, the norm in the $\ell^q$ product of two copies of $L^q(I)$. This
is Proposition 8.14 of [brezis2011functional].

At $p = 1$ the norm of the type is the sum norm of [brezis2011functional], and the norm of the
pair is $\max\{\|f_0\|, \|f_1\|\}$ as in the source. The functional $F$ extends from the closed
subspace $W_0^{1,p}(I)$ to $W^{1,p}(I)$ with the same norm (`exists_extension_norm_eq`), and
Remark 21 (`SobolevIntervalLp.exists_repr_strongDual`) represents the extension. -/
theorem exists_repr [ENNReal.HolderConjugate p q] (hp : p ≠ ⊤) (F : SobolevIntervalLpDual p I) :
    ∃ f : PiLp q (fun _ : Fin 2 ↦ Lp ℝ q (volume.restrict (I : Set ℝ))),
      (∀ u : SobolevIntervalLpZero 1 p I,
        F u = (∫ x in (I : Set ℝ), f 0 x * fn (u : SobolevIntervalLp 1 p I) x)
          + ∫ x in (I : Set ℝ), f 1 x * deriv (u : SobolevIntervalLp 1 p I) 1 x) ∧ ‖F‖ = ‖f‖ := by
  obtain ⟨G, hG, hGn⟩ := exists_extension_norm_eq (SobolevIntervalLpZero 1 p I) F
  obtain ⟨f, hf, hfn⟩ := exists_repr_strongDual (q := q) hp G
  exact ⟨f, fun u ↦ by rw [← hG u, hf], hGn.symm.trans hfn⟩

variable {a b : ℝ}

/-- Let $a < b$, let $1 \le p < \infty$ and let $q$ be the conjugate exponent. For
$F \in W^{-1,q}(a, b)$ there is $f_1 \in L^q(a, b)$ such that
$$\langle F, u \rangle = \int_a^b f_1 u' \quad \text{for every } u \in W_0^{1,p}(a, b).$$
This is the statement "when $I$ is bounded we can take $f_0 = 0$" after Proposition 8.14 of
[brezis2011functional].

By the Poincaré inequality (Proposition 8.13 of [brezis2011functional],
`SobolevIntervalLpZero.norm_le_mul_norm_deriv`), the map $u \mapsto u'$ is injective on
$W_0^{1,p}(a, b)$ with $\|u\| \le C \|u'\|_{L^p}$. So $F \circ (u \mapsto u')^{-1}$ is a bounded
functional on the range of $u \mapsto u'$ in $L^p(a, b)$. It extends to $L^p(a, b)$ and is
represented by $f_1$. -/
theorem exists_repr_of_bounded [ENNReal.HolderConjugate p q] (hp : p ≠ ⊤) (hab : a < b)
    (F : SobolevIntervalLpDual p (Opens.Ioo a b)) :
    ∃ f₁ : Lp ℝ q (volume.restrict (Ioo a b)), ∀ u : SobolevIntervalLpZero 1 p (Opens.Ioo a b),
      F u = ∫ x in Ioo a b, f₁ x * deriv (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) 1 x := by
  have hq1 : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SobolevIntervalLpZero 1 p (Opens.Ioo a b),
      ‖(u : SobolevIntervalLp 1 p (Opens.Ioo a b))‖
        ≤ C * ‖deriv (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) 1‖ :=
    ⟨(b - a) / p.toReal ^ p.toReal⁻¹ + 1, by
      have := poincareConst_nonneg (p := p) hab.le
      linarith, fun u ↦ SobolevIntervalLpZero.norm_le_mul_norm_deriv hab u.2⟩
  -- the derivative `u ↦ u'` on `W_0^{1,p}(a, b)`, injective by Poincaré's inequality
  obtain ⟨D, hD⟩ : ∃ D : SobolevIntervalLpZero 1 p (Opens.Ioo a b) →ₗ[ℝ]
      Lp ℝ p (volume.restrict ((Opens.Ioo a b : Opens ℝ) : Set ℝ)),
      ∀ u, D u = deriv (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) 1 :=
    ⟨(derivL 1 p (Opens.Ioo a b) 1 : SobolevIntervalLp 1 p (Opens.Ioo a b) →ₗ[ℝ]
      Lp ℝ p (volume.restrict ((Opens.Ioo a b : Opens ℝ) : Set ℝ))).comp
        (SobolevIntervalLpZero 1 p (Opens.Ioo a b)).subtype,
      fun u ↦ derivL_apply 1 (u : SobolevIntervalLp 1 p (Opens.Ioo a b))⟩
  have hDinj : Function.Injective D := by
    intro u v huv
    have h1 : ‖(u - v : SobolevIntervalLpZero 1 p (Opens.Ioo a b))‖ = 0 := by
      refine le_antisymm ((hC (u - v)).trans_eq ?_) (norm_nonneg _)
      rw [Submodule.coe_sub, deriv_sub, ← hD u, ← hD v, huv, sub_self, norm_zero, mul_zero]
    exact sub_eq_zero.1 (norm_eq_zero.1 h1)
  -- the functional `F ∘ D⁻¹` on the range of `D`, bounded by `C ‖F‖`
  obtain ⟨e, he⟩ : ∃ e : SobolevIntervalLpZero 1 p (Opens.Ioo a b) ≃ₗ[ℝ] LinearMap.range D,
      e = LinearEquiv.ofInjective D hDinj := ⟨_, rfl⟩
  have he_apply : ∀ u, (e u : Lp ℝ p (volume.restrict ((Opens.Ioo a b : Opens ℝ) : Set ℝ)))
      = D u := fun u ↦ by
    rw [he]; rfl
  obtain ⟨G, hG⟩ : ∃ G : LinearMap.range D →ₗ[ℝ] ℝ, G = (F : _ →ₗ[ℝ] ℝ).comp e.symm.toLinearMap :=
    ⟨_, rfl⟩
  have hGle : ∀ r : LinearMap.range D, ‖G r‖ ≤ C * ‖F‖ * ‖r‖ := by
    intro r
    rw [hG, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, ContinuousLinearMap.coe_coe]
    refine (F.le_opNorm _).trans ?_
    have h1 := hC (e.symm r)
    rw [← hD, ← he_apply, LinearEquiv.apply_symm_apply] at h1
    change ‖F‖ * ‖((e.symm r : SobolevIntervalLpZero 1 p (Opens.Ioo a b)) :
      SobolevIntervalLp 1 p (Opens.Ioo a b))‖ ≤ C * ‖F‖ * ‖r‖
    calc ‖F‖ * ‖((e.symm r : SobolevIntervalLpZero 1 p (Opens.Ioo a b)) :
          SobolevIntervalLp 1 p (Opens.Ioo a b))‖ ≤ ‖F‖ * (C * ‖r‖) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = C * ‖F‖ * ‖r‖ := by ring
  obtain ⟨Ĝ, hĜ, -⟩ := exists_extension_norm_eq (LinearMap.range D)
    (G.mkContinuous (C * ‖F‖) hGle)
  obtain ⟨f₁, hf₁⟩ := Lp.exists_forall_eq_integral (q := q) hp Ĝ
  refine ⟨f₁, fun u ↦ ?_⟩
  have h1 := hĜ (e u)
  rw [hf₁, LinearMap.mkContinuous_apply, hG, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply, he_apply, hD] at h1
  exact h1.symm

end SobolevIntervalLpDual

/-! ### Remark 19: the representation is not unique -/

namespace SobolevIntervalLpDual

open SobolevIntervalLp

omit [Fact (1 ≤ p)] in
/-- Let $I \subseteq \mathbb{R}$ be open, let $q$ be the conjugate exponent of $p$, let
$f_0, f_1 \in L^q(I)$, let $g$ be a test function on $I$ and let $u \in W^{1,p}(I)$. Then
$$\int_I (f_0 + g') u + \int_I (f_1 + g) u' = \int_I f_0 u + \int_I f_1 u'.$$
Hence the pair $(f_0, f_1)$ that represents a functional on $W^{1,p}(I)$ or on $W_0^{1,p}(I)$ is
not unique. This is Remark 19 of [brezis2011functional], Chapter 8.

The identity is $\int_I g' u = -\int_I g u'$, the definition of the weak derivative. -/
theorem repr_not_unique [ENNReal.HolderConjugate p q] {f₀ f₁ : ℝ → ℝ}
    (hf₀ : MemLp f₀ q (volume.restrict I)) (hf₁ : MemLp f₁ q (volume.restrict I)) (g : 𝓓(I, ℝ))
    (u : SobolevIntervalLp 1 p I) :
    (∫ x in (I : Set ℝ), (f₀ x + deriv g x) * fn u x)
        + ∫ x in (I : Set ℝ), (f₁ x + g x) * deriv u 1 x
      = (∫ x in (I : Set ℝ), f₀ x * fn u x) + ∫ x in (I : Set ℝ), f₁ x * deriv u 1 x := by
  have h := (hasWeakDerivOn_fn u).integral_deriv_mul g
  have hu0 : MemLp (fn u) p (volume.restrict I) := memLp_deriv u 0
  have hu1 : MemLp (deriv u 1) p (volume.restrict I) := memLp_deriv u 1
  have hi0 : Integrable (fun x ↦ f₀ x * fn u x) (volume.restrict I) := hf₀.integrable_mul hu0
  have hi1 : Integrable (fun x ↦ f₁ x * deriv u 1 x) (volume.restrict I) := hf₁.integrable_mul hu1
  have hg0 : Integrable (fun x ↦ deriv g x * fn u x) (volume.restrict I) := by
    have := ((hasWeakDerivOn_fn u).integrable_smul (g.fderivApply 1)).restrict (s := I)
    simpa only [TestFunction.derivApply_coe, smul_eq_mul] using this
  have hg1 : Integrable (fun x ↦ g x * deriv u 1 x) (volume.restrict I) := by
    have := ((hasWeakDerivOn_fn u).integrable_smul_weakDeriv g).restrict (s := I)
    simpa only [smul_eq_mul] using this
  have e1 : ∫ x in (I : Set ℝ), (f₀ x + deriv g x) * fn u x
      = (∫ x in (I : Set ℝ), f₀ x * fn u x) + ∫ x in (I : Set ℝ), deriv g x * fn u x := by
    rw [← integral_add hi0 hg0]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
  have e2 : ∫ x in (I : Set ℝ), (f₁ x + g x) * deriv u 1 x
      = (∫ x in (I : Set ℝ), f₁ x * deriv u 1 x) + ∫ x in (I : Set ℝ), g x * deriv u 1 x := by
    rw [← integral_add hi1 hg1]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
  rw [e1, e2, h]
  ring

end SobolevIntervalLpDual

end Repr

end
