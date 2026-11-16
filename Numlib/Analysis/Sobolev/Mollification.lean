/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Mollification`, beside
`Mathlib.Analysis.Distribution.WeakDeriv`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Convolution.Lp
import Numlib.Analysis.Sobolev.WeakDeriv

/-!
# Mollification on an open set

Let $E$ be a finite-dimensional real normed space, let $\Omega \subseteq E$ be open, and let
$\varphi$ be a smooth bump supported in the closed ball $\bar B(0, \varepsilon)$. The convolution
$(\varphi \star f)(x) = \int \varphi(t) f(x - t) \, d\mu(t)$ depends on $f$ only on
$\bar B(x, \varepsilon)$. So the mollification of a function $f$ given on $\Omega$ makes sense at
the points $x$ with $\bar B(x, \varepsilon) \subseteq \Omega$, that is, on the $\varepsilon$-erosion
of $\Omega$. This file develops this bookkeeping and proves that **the weak derivative commutes with
mollification**: if $w$ is the weak derivative of $f$ along a tuple $y$ of directions on $\Omega$,
then $\partial^y (\varphi \star f)(x) = (\varphi \star w)(x)$ at every point $x$ with
$\bar B(x, \varepsilon) \subseteq \Omega$.

From the commutation follow the local approximation of a weakly differentiable function by smooth
functions in $L^p$, the product rule for two weakly differentiable factors, and the chain rule with
a $C^1$ function. The classical statements are in Evans, *Partial Differential Equations*, 2nd
edition, §C.5 and §5.3.1, and in [brezis2011functional], §4.4 and §9.1. The product rule and the
chain rule are Propositions 7.1.11 and 7.1.12 of [han2009theoretical].

## Main definitions

* `TestFunction.compConstSub`: the reflected translate $z \mapsto \varphi(x - z)$ of a bump, as a
  test function on $\Omega$. It turns a convolution into an instance of the defining identity of the
  weak derivative.

## Main results

* `exists_isCompact_forall_closedBall_subset` and `IsCompact.exists_pos_forall_closedBall_subset`:
  two forms of the fact that a compact subset of an open set has a positive distance from the
  complement.
* `ContDiff.iteratedFDeriv_comp_const_sub`: the $n$-th derivative of $z \mapsto f(a - z)$ at $x$ is
  $(-1)^n$ times the $n$-th derivative of $f$ at $a - x$, with the directions in the same order.
* `HasWeakIteratedLineDerivOn.convolution_iteratedFDeriv`: $((\partial^y \varphi) \star f)(x) =
  (\varphi \star w)(x)$, an integration by parts under the integral sign.
* `HasWeakIteratedLineDerivOn.iteratedFDeriv_convolution` and
  `HasWeakIteratedFDerivOn.iteratedFDeriv_convolution`: the weak derivative commutes with
  mollification, for one tuple of directions and for all tuples at once.
* `HasWeakIteratedLineDerivOn.exists_seq_contDiff_tendsto_eLpNorm`: local approximation in
  $W^{k,p}$; smooth functions $g_j$ with $g_j \to f$ and $\partial^y g_j \to w$ in $L^p(V)$, for $V$
  relatively compact in $\Omega$.
* `HasWeakIteratedLineDerivOn.mul`: the product rule
  $\partial(uv) = (\partial u) v + u (\partial v)$ for $u, \partial u \in L^p_{\mathrm{loc}}$ and
  $v, \partial v \in L^q_{\mathrm{loc}}$, with conjugate exponents.
* `HasWeakIteratedLineDerivOn.contDiff_comp`: the chain rule $\partial(f \circ v) = (f' \circ v) \,
  \partial v$ for a $C^1$ function $f$ with bounded derivative.
* `TopologicalSpace.Opens.exists_exhaustion` and `IsCompact.exists_contDiff_eqOn_one`: an exhaustion
  of an open set by relatively compact open sets, and the smooth Urysohn lemma. Neither is used in
  this file. Density theorems built on this file need them, and Mathlib does not have them for an
  open subset of a vector space.

## Implementation notes

* The derivative of the reflected translate looks dangerous but is not. The function
  $z \mapsto \varphi(a - z)$ is written as $(w \mapsto \varphi(a + w)) \circ (-\mathrm{id})$, and
  `ContinuousLinearMap.iteratedFDeriv_comp_right` composes the derivative with the linear map
  $-\mathrm{id}$ in every slot. Each slot gives the same factor $-1$, so multilinearity gives
  $(-1)^n$, and the directions stay in their original order. No reversal of the tuple appears,
  unlike in the bookkeeping of `iteratedFDeriv_succ_apply_left` and
  `iteratedFDeriv_succ_apply_right` that the module `Numlib.Analysis.Sobolev.WeakDeriv` warns about.
* `HasWeakIteratedLineDerivOn` asks for local integrability on $\Omega$ only, so $\varphi \star f$
  need not be defined, nor smooth, away from the erosion of $\Omega$. Both places where this matters
  use a truncation: $f$ is replaced by $1_K f$ for a compact $K \subseteq \Omega$ that contains
  $\bar B(x', \varepsilon)$ for every $x'$ near the point in question. The truncation is integrable
  on $E$, so its mollification is smooth on $E$, and it agrees with $f$ wherever the convolution
  sees it. `Filter.EventuallyEq.iteratedFDeriv` then transfers the derivative, because an iterated
  derivative at a point depends only on the germ of the function there.
* The product rule and the chain rule take the limit in two different ways. The product rule pairs
  an $L^p$ convergence with a fixed $L^q$ factor, so Hölder's inequality is sufficient
  (`MeasureTheory.tendsto_integral_mul_of_tendsto_eLpNorm`). In the chain rule, the factor
  $f' \circ v_\varepsilon$ moves with $\varepsilon$ and converges only pointwise. So one term needs
  a subsequence that converges almost everywhere
  (`MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae`) and the dominated convergence theorem. A
  subsequence is sufficient, because the statement to prove is an identity between two fixed
  quantities.
-/

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Convolution Distributions ENNReal Manifold Topology

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E} {n : ℕ}

/-!
### Compact sets inside an open set

All results below need a positive distance between a compact set and the complement of an open set
that contains it. It is used in two forms: a compact $K \subseteq \Omega$ that contains
$\bar B(x', \varepsilon)$ for every $x'$ near a given point, or a radius $\varepsilon > 0$ that
works uniformly on a neighbourhood of a given compact set.
-/

section Neighbourhoods

variable [FiniteDimensional ℝ E]

/-- Let $E$ be finite-dimensional, let $U \subseteq E$ be open, and let
$\bar B(x, \varepsilon) \subseteq U$. Then there are a compact set $K \subseteq U$ and a number
$\delta > 0$ such that $\bar B(x, \varepsilon)$ lies in the interior of $K$ and
$\bar B(x', \varepsilon) \subseteq K$ for every $x' \in B(x, \delta)$.

This lets a function that is only locally integrable on $U$ be replaced by an integrable
truncation, without a change of its convolution near $x$. -/
theorem exists_isCompact_forall_closedBall_subset {U : Set E} (hU : IsOpen U)
    {ε : ℝ} {x : E} (hx : closedBall x ε ⊆ U) :
    ∃ (K : Set E) (δ : ℝ), IsCompact K ∧ K ⊆ U ∧ 0 < δ ∧ closedBall x ε ⊆ interior K ∧
      ∀ x' ∈ ball x δ, closedBall x' ε ⊆ K := by
  obtain ⟨r, hr, hrU⟩ := (isCompact_closedBall x ε).exists_thickening_subset_open hU hx
  refine ⟨cthickening (r / 2) (closedBall x ε), r / 2, (isCompact_closedBall x ε).cthickening,
    (cthickening_subset_thickening' hr (by linarith) _).trans hrU, by linarith, ?_, ?_⟩
  · exact (self_subset_thickening (by linarith) _).trans
      (thickening_subset_interior_cthickening _ _)
  · intro x' hx' p hp
    refine mem_cthickening_of_dist_le p (p - (x' - x)) _ _ ?_ ?_
    · simp only [mem_closedBall, dist_eq_norm] at hp ⊢
      simpa [sub_sub, sub_add_eq_sub_sub] using hp
    · rw [mem_ball, dist_eq_norm] at hx'
      rw [dist_eq_norm, show p - (p - (x' - x)) = x' - x by abel]
      exact hx'.le

/-- Let $E$ be finite-dimensional, and let $K$ be a compact subset of an open set $U \subseteq E$.
Then there are an open set $V \supseteq K$ and a radius $\varepsilon > 0$ such that the closure
of $V$ is compact and contained in $U$, and $\bar B(x, \varepsilon) \subseteq U$ for every
$x \in V$.

On such a $V$ the mollification at scale $\varepsilon$ is available. -/
theorem IsCompact.exists_pos_forall_closedBall_subset {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (V : Set E) (ε : ℝ), IsOpen V ∧ K ⊆ V ∧ 0 < ε ∧ IsCompact (closure V) ∧ closure V ⊆ U ∧
      ∀ x ∈ V, closedBall x ε ⊆ U := by
  obtain ⟨r, hr, hrU⟩ := hK.exists_thickening_subset_open hU hKU
  refine ⟨thickening (r / 3) K, r / 3, isOpen_thickening, self_subset_thickening (by linarith) K,
    by linarith, ?_, ?_, ?_⟩
  · exact hK.cthickening.of_isClosed_subset isClosed_closure
      (closure_minimal (thickening_subset_cthickening _ _) isClosed_cthickening)
  · refine (closure_minimal (thickening_subset_cthickening _ _) isClosed_cthickening).trans ?_
    exact (cthickening_subset_thickening' hr (by linarith) _).trans hrU
  · intro x hx p hp
    refine hrU ?_
    rw [mem_thickening_iff] at hx ⊢
    obtain ⟨z, hz, hxz⟩ := hx
    refine ⟨z, hz, ?_⟩
    have h := dist_triangle p x z
    rw [mem_closedBall] at hp
    linarith

end Neighbourhoods

/-!
### Exhaustions and smooth cut-offs

Two facts about an open subset of a finite-dimensional real normed space that Mathlib has only for
the whole space (`CompactExhaustion`) or only on a manifold (`SmoothPartitionOfUnity`). They are not
used in this file. A density theorem built on the mollification below needs them.
-/

section Exhaustion

variable [FiniteDimensional ℝ E]

/-- **An open set is exhausted by relatively compact open subsets.** Let $E$ be finite-dimensional
and $\Omega \subseteq E$ open. Then there are open sets $U_0, U_1, \dots$ such that each closure
$\overline{U_n}$ is compact and contained in $U_{n+1}$, and $\bigcup_n U_n = \Omega$.

Mathlib's `CompactExhaustion` gives this for the whole space. In the proof, instance search
finds neither `SigmaCompactSpace ↥Ω` nor `WeaklyLocallyCompactSpace ↥Ω`, so
`IsOpen.locallyCompactSpace` is supplied by hand. -/
theorem TopologicalSpace.Opens.exists_exhaustion (Ω : Opens E) :
    ∃ U : ℕ → Opens E, (∀ n, IsCompact (closure (U n : Set E))) ∧
      (∀ n, closure (U n : Set E) ⊆ U (n + 1)) ∧ (⋃ n, (U n : Set E)) = Ω := by
  have := Ω.isOpen.locallyCompactSpace
  set K : CompactExhaustion (Ω : Set E) := default with hK
  set V : ℕ → Set E := fun n ↦ Subtype.val '' interior (K (n + 1)) with hV
  have hopen : ∀ n, IsOpen (V n) := fun n ↦ Ω.isOpen.isOpenMap_subtype_val _ isOpen_interior
  have hcpt : ∀ n, IsCompact (Subtype.val '' (K (n + 1) : Set (Ω : Set E))) := fun n ↦
    (K.isCompact (n + 1)).image continuous_subtype_val
  have hsub : ∀ n, closure (V n) ⊆ Subtype.val '' (K (n + 1) : Set (Ω : Set E)) := fun n ↦
    closure_minimal (image_mono interior_subset) (hcpt n).isClosed
  refine ⟨fun n ↦ ⟨V n, hopen n⟩, fun n ↦ ?_, fun n ↦ ?_, ?_⟩
  · exact (hcpt n).of_isClosed_subset isClosed_closure (hsub n)
  · exact (hsub n).trans (image_mono (K.subset_interior (by omega)))
  · apply subset_antisymm
    · exact iUnion_subset fun n ↦ (image_subset_range _ _).trans (by simp)
    · rintro x hx
      obtain ⟨n, hn⟩ := K.exists_mem ⟨x, hx⟩
      exact mem_iUnion.2 ⟨n, ⟨x, hx⟩, K.subset_interior_succ n hn, rfl⟩

/-- **The smooth Urysohn lemma.** Let $E$ be finite-dimensional, and let $K$ be a compact subset of
an open set $V \subseteq E$. Then there is a smooth function $f : E \to \mathbb{R}$ with $f = 1$
on $K$, $\operatorname{tsupport} f \subseteq V$, and $0 \le f \le 1$.

Mathlib proves this on a manifold, as `exists_contMDiffMap_zero_one_nhds_of_isClosed`; this is
the case of the model space $E$ with the model `𝓘(ℝ, E)`. -/
theorem IsCompact.exists_contDiff_eqOn_one {K V : Set E} (hK : IsCompact K) (hV : IsOpen V)
    (hKV : K ⊆ V) :
    ∃ f : E → ℝ, ContDiff ℝ ∞ f ∧ EqOn f 1 K ∧ tsupport f ⊆ V ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨f, hf0, hf1, hf01⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed (I := 𝓘(ℝ, E)) (n := (⊤ : ℕ∞))
      hV.isClosed_compl hK.isClosed (disjoint_compl_left_iff_subset.2 hKV)
  refine ⟨f, contMDiff_iff_contDiff.mp f.contMDiff, fun x hx ↦ hf1.self_of_nhdsSet x hx, ?_, hf01⟩
  obtain ⟨W, hWopen, hWsub, hWf⟩ := mem_nhdsSet_iff_exists.1 hf0
  have : tsupport (f : E → ℝ) ⊆ Wᶜ :=
    closure_minimal (fun x hx hxW ↦ hx (hWf hxW)) hWopen.isClosed_compl
  exact this.trans (compl_subset_comm.2 hWsub)

/-- Let $E$ be finite-dimensional, and let $K$ be a compact subset of an open set $V \subseteq E$.
Then there is a smooth function $\theta : E \to \mathbb{R}$ with $\theta = 1$ on $K$, with
compact support, and with $\operatorname{tsupport} \theta \subseteq V$.

The proof applies `IsCompact.exists_contDiff_eqOn_one` to the interior of a compact
neighbourhood of $K$ inside $V$. -/
theorem IsCompact.exists_contDiff_eqOn_one_hasCompactSupport {K V : Set E} (hK : IsCompact K)
    (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ θ : E → ℝ, ContDiff ℝ ∞ θ ∧ EqOn θ 1 K ∧ HasCompactSupport θ ∧ tsupport θ ⊆ V := by
  obtain ⟨L, hLc, hKL, hLV⟩ := exists_compact_between hK hV hKV
  obtain ⟨θ, hθ, hθ1, hθL, -⟩ := hK.exists_contDiff_eqOn_one isOpen_interior hKL
  exact ⟨θ, hθ, hθ1, hLc.of_isClosed_subset (isClosed_tsupport θ) (hθL.trans interior_subset),
    hθL.trans (interior_subset.trans hLV)⟩

end Exhaustion

/-! ### The iterated derivative of a reflected translate -/

section Reflection

/-- **The iterated derivative of a reflected translate.** Let $f : E \to F$ be of class $C^N$ and
$n \le N$. For $a, x \in E$ and directions $y_1, \dots, y_n$,
$$D^n \bigl(z \mapsto f(a - z)\bigr)(x)[y_1, \dots, y_n] = (-1)^n D^n f(a - x)[y_1, \dots,
  y_n].$$
The directions appear in the same order on both sides. -/
theorem ContDiff.iteratedFDeriv_comp_const_sub {N : ℕ∞ω} {f : E → F} (hf : ContDiff ℝ N f)
    (hn : (n : ℕ∞ω) ≤ N) (a x : E) (y : Fin n → E) :
    iteratedFDeriv ℝ n (fun z ↦ f (a - z)) x y
      = (-1 : ℝ) ^ n • iteratedFDeriv ℝ n f (a - x) y := by
  have hg : ContDiff ℝ N (fun w ↦ f (a + w)) := hf.comp (contDiff_const.add contDiff_id)
  have h1 : (fun z : E ↦ f (a - z))
      = (fun w ↦ f (a + w)) ∘ ⇑(-ContinuousLinearMap.id ℝ E) := by
    funext z; simp [sub_eq_add_neg]
  rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_right (-ContinuousLinearMap.id ℝ E) hg x hn]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, neg_apply,
    ContinuousLinearMap.id_apply]
  rw [show (fun i ↦ -(y i)) = fun i ↦ (-1 : ℝ) • y i by funext i; simp,
    ContinuousMultilinearMap.map_smul_univ]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 2
  rw [iteratedFDeriv_comp_add_left]
  congr 1
  rw [sub_eq_add_neg]

end Reflection

/-! ### The reflected translate of a bump, as a test function -/

namespace TestFunction

variable [FiniteDimensional ℝ E]

/-- The reflected translate $z \mapsto \varphi(x - z)$ of a smooth function $\varphi$ with
$\operatorname{tsupport} \varphi \subseteq \bar B(0, \varepsilon)$, as a test function on
$\Omega$, for a point $x$ with $\bar B(x, \varepsilon) \subseteq \Omega$. The hypothesis on $x$
puts the support inside $\Omega$.

This connects the convolution $(\varphi \star f)(x) = \int \varphi(t) f(x - t) \, dt$ with the
defining identity of the weak derivative on $\Omega$, which quantifies over test functions on
$\Omega$. -/
def compConstSub (Ω : Opens E) {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) {ε : ℝ}
    (hsupp : tsupport φ ⊆ closedBall 0 ε) {x : E} (hx : closedBall x ε ⊆ (Ω : Set E)) :
    𝓓(Ω, ℝ) where
  toFun z := φ (x - z)
  contDiff' := hφ.comp (contDiff_const.sub contDiff_id)
  hasCompactSupport' := by
    refine IsCompact.of_isClosed_subset (isCompact_closedBall x ε) isClosed_closure ?_
    refine closure_minimal (fun z hz ↦ ?_) isClosed_closedBall
    have : x - z ∈ tsupport φ := subset_tsupport _ hz
    simpa [mem_closedBall, dist_eq_norm, norm_sub_rev] using hsupp this
  tsupport_subset' := by
    refine subset_trans (closure_minimal (fun z hz ↦ ?_) isClosed_closedBall) hx
    have : x - z ∈ tsupport φ := subset_tsupport _ hz
    simpa [mem_closedBall, dist_eq_norm, norm_sub_rev] using hsupp this

/-- The test function `TestFunction.compConstSub` is the function $z \mapsto \varphi(x - z)$. -/
@[simp]
theorem compConstSub_coe (Ω : Opens E) {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) {ε : ℝ}
    (hsupp : tsupport φ ⊆ closedBall 0 ε) {x : E} (hx : closedBall x ε ⊆ (Ω : Set E)) :
    (compConstSub Ω hφ hsupp hx : E → ℝ) = fun z ↦ φ (x - z) :=
  rfl

end TestFunction

/-! ### The weak derivative commutes with mollification -/

section Commutation

open ContinuousLinearMap

variable [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure] {y : Fin n → E} {f w : E → F}

/-- **Integration by parts under the integral sign.** Let $E$ be finite-dimensional with an additive
Haar measure $\mu$, and let $w$ be the weak derivative of $f$ along the tuple
$y = (y_1, \dots, y_n)$ on $\Omega$. Let $\varphi$ be smooth with $\operatorname{tsupport}
\varphi \subseteq \bar B(0, \varepsilon)$, and let $\bar B(x, \varepsilon) \subseteq \Omega$.
Then
$$\bigl((\partial^y \varphi) \star f\bigr)(x) = (\varphi \star w)(x),$$
where $\partial^y \varphi(z) = D^n \varphi(z)[y_1, \dots, y_n]$ and the convolutions are with
respect to $\mu$.

This carries the content of the commutation of the weak derivative with mollification.
`HasWeakIteratedLineDerivOn.iteratedFDeriv_convolution` adds only the identification of the left
side with a derivative of $\varphi \star f$. -/
theorem HasWeakIteratedLineDerivOn.convolution_iteratedFDeriv
    (h : HasWeakIteratedLineDerivOn y f w Ω μ) {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) {ε : ℝ}
    (hsupp : tsupport φ ⊆ closedBall 0 ε) {x : E} (hx : closedBall x ε ⊆ (Ω : Set E)) :
    ((fun z ↦ iteratedFDeriv ℝ n φ z y) ⋆[lsmul ℝ ℝ, μ] f) x = (φ ⋆[lsmul ℝ ℝ, μ] w) x := by
  set ψ : 𝓓(Ω, ℝ) := TestFunction.compConstSub Ω hφ hsupp hx with hψ
  have hrefl : ∀ s, iteratedFDeriv ℝ n (ψ : E → ℝ) s y
      = (-1 : ℝ) ^ n • iteratedFDeriv ℝ n φ (x - s) y := fun s ↦ by
    simpa [hψ] using hφ.iteratedFDeriv_comp_const_sub (n := n) (by simp) x s y
  have hL : ((fun z ↦ iteratedFDeriv ℝ n φ z y) ⋆[lsmul ℝ ℝ, μ] f) x
      = ∫ s, iteratedFDeriv ℝ n φ (x - s) y • f s ∂μ := by
    rw [convolution_def]
    simp only [lsmul_apply]
    rw [← integral_sub_left_eq_self (fun t ↦ iteratedFDeriv ℝ n φ (x - t) y • f t) μ x]
    exact integral_congr_ae (Eventually.of_forall fun t ↦ by simp only [sub_sub_cancel])
  have hR : (φ ⋆[lsmul ℝ ℝ, μ] w) x = ∫ s, φ (x - s) • w s ∂μ := by
    rw [convolution_def]
    simp only [lsmul_apply]
    rw [← integral_sub_left_eq_self (fun t ↦ φ (x - t) • w t) μ x]
    exact integral_congr_ae (Eventually.of_forall fun t ↦ by simp only [sub_sub_cancel])
  have key := h.integral_smul_eq' ψ
  have e1 : ∫ s, iteratedFDeriv ℝ n (ψ : E → ℝ) s y • f s ∂μ
      = (-1 : ℝ) ^ n • ∫ s, iteratedFDeriv ℝ n φ (x - s) y • f s ∂μ := by
    rw [← integral_smul]
    exact integral_congr_ae (Eventually.of_forall fun s ↦ by simp only [hrefl s, smul_assoc])
  have e2 : ∫ s, ψ s • w s ∂μ = ∫ s, φ (x - s) • w s ∂μ := rfl
  rw [e1, e2] at key
  rw [hL, hR]
  exact smul_right_injective F (pow_ne_zero n (by norm_num : (-1 : ℝ) ≠ 0)) key

/-- **The weak derivative commutes with mollification**, for one tuple of directions. Let $E$ be
finite-dimensional with an additive Haar measure $\mu$, and let $w$ be the weak derivative of
$f$ along the tuple $y = (y_1, \dots, y_n)$ on $\Omega$. Let $\varphi$ be smooth with
$\operatorname{tsupport} \varphi \subseteq \bar B(0, \varepsilon)$, and let
$\bar B(x, \varepsilon) \subseteq \Omega$. Then the mollification $\varphi \star f$ has the
classical derivative
$$D^n (\varphi \star f)(x)[y_1, \dots, y_n] = (\varphi \star w)(x).$$

The function $f$ is only locally integrable on $\Omega$, so $\varphi \star f$ need not be
smooth, nor defined, elsewhere. The derivative on the left is still the classical one, because
near $x$ the function $\varphi \star f$ agrees with the mollification of a compactly supported
truncation of $f$, which is smooth on $E$. -/
theorem HasWeakIteratedLineDerivOn.iteratedFDeriv_convolution
    (h : HasWeakIteratedLineDerivOn y f w Ω μ) {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) {ε : ℝ}
    (hsupp : tsupport φ ⊆ closedBall 0 ε) {x : E} (hx : closedBall x ε ⊆ (Ω : Set E)) :
    iteratedFDeriv ℝ n (φ ⋆[lsmul ℝ ℝ, μ] f) x y = (φ ⋆[lsmul ℝ ℝ, μ] w) x := by
  have hcφ : HasCompactSupport φ :=
    IsCompact.of_isClosed_subset (isCompact_closedBall 0 ε) isClosed_closure hsupp
  obtain ⟨K, δ, hK, hKΩ, hδ, hxK, hball⟩ :=
    exists_isCompact_forall_closedBall_subset Ω.isOpen hx
  set f' : E → F := K.indicator f with hf'
  have hf'loc : LocallyIntegrable f' μ :=
    ((h.locallyIntegrableOn.integrableOn_compact_subset hKΩ hK).integrable_indicator
      hK.isClosed.measurableSet).locallyIntegrable
  have heq : (φ ⋆[lsmul ℝ ℝ, μ] f) =ᶠ[𝓝 x] (φ ⋆[lsmul ℝ ℝ, μ] f') := by
    filter_upwards [ball_mem_nhds x hδ] with x' hx'
    refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
    rcases eq_or_ne (φ t) 0 with h0 | h0
    · simp [h0]
    · have ht : t ∈ closedBall (0 : E) ε := hsupp (subset_tsupport _ h0)
      have hmem : x' - t ∈ K := hball x' hx' (by
        simpa [mem_closedBall, dist_eq_norm] using (by simpa using ht : ‖t‖ ≤ ε))
      simp [hf', Set.indicator_of_mem hmem]
  have h' : HasWeakIteratedLineDerivOn y f' w ⟨interior K, isOpen_interior⟩ μ :=
    (h.mono (interior_subset.trans hKΩ)).congr_ae
      (Filter.eventually_of_mem (self_mem_ae_restrict isOpen_interior.measurableSet)
        fun z hz ↦ (Set.indicator_of_mem (interior_subset hz) f).symm)
      (Filter.EventuallyEq.refl _ _)
  rw [(Filter.EventuallyEq.iteratedFDeriv ℝ heq n).self_of_nhds,
    hf'loc.iteratedFDeriv_convolution_left_apply n hcφ hφ x y,
    h'.convolution_iteratedFDeriv hφ hsupp hxK]

/-- **The weak derivative commutes with mollification**, for all tuples of directions at once. Let
$E$ be finite-dimensional with an additive Haar measure $\mu$, and let $w$ be the $n$-th weak
derivative of $f$ on $\Omega$, with values in the continuous $n$-linear maps. Let $\varphi$ be
smooth with $\operatorname{tsupport} \varphi \subseteq \bar B(0, \varepsilon)$, and let
$\bar B(x, \varepsilon) \subseteq \Omega$. Then
$$D^n (\varphi \star f)(x) = (\varphi \star w)(x)$$
as continuous $n$-linear maps. -/
theorem HasWeakIteratedFDerivOn.iteratedFDeriv_convolution {w : E → E [×n]→L[ℝ] F}
    (h : HasWeakIteratedFDerivOn n f w Ω μ) {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) {ε : ℝ}
    (hsupp : tsupport φ ⊆ closedBall 0 ε) {x : E} (hx : closedBall x ε ⊆ (Ω : Set E)) :
    iteratedFDeriv ℝ n (φ ⋆[lsmul ℝ ℝ, μ] f) x = (φ ⋆[lsmul ℝ ℝ, μ] w) x := by
  have hex : ConvolutionExistsAt φ w x (lsmul ℝ ℝ) μ :=
    h.locallyIntegrableOn_weakDeriv.convolutionExistsAt hφ.continuous hsupp hx
  refine ContinuousMultilinearMap.ext fun z ↦ ?_
  rw [(h.lineDeriv z).iteratedFDeriv_convolution hφ hsupp hx, convolution_def, convolution_def,
    ContinuousMultilinearMap.integral_apply hex]
  rfl

end Commutation

/-!
### Hölder's inequality, locally

The local form of Hölder's inequality that the product rule needs. Its companions for $L^p$ limits,
`MeasureTheory.tendsto_integral_mul_of_tendsto_eLpNorm`,
`MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm` and
`MeasureTheory.enorm_integral_smul_le_of_bound`, are in `Numlib.Analysis.Convolution.Lp`. The $L^p$
analogues of local integrability on a compact subset are in `Numlib.Analysis.Sobolev.WeakDeriv`,
beside `MeasureTheory.LocallyMemLpOn`.
-/

namespace MeasureTheory

variable {X G : Type*} [TopologicalSpace X] [MeasurableSpace X] [NormedAddCommGroup G]
  {f : X → G} {s t : Set X} {μ : Measure X} {p : ℝ≥0∞}

/-- **Hölder's inequality, locally.** Let $p$ and $q$ be Hölder conjugate exponents. If
$u \in L^p_{\mathrm{loc}}(s)$ and $v \in L^q_{\mathrm{loc}}(s)$, then the product $uv$ is
locally integrable on $s$. -/
theorem LocallyMemLpOn.locallyIntegrableOn_mul {q : ℝ≥0∞} [ENNReal.HolderConjugate p q]
    {u v : X → ℝ} (hu : LocallyMemLpOn u p s μ) (hv : LocallyMemLpOn v q s μ) :
    LocallyIntegrableOn (fun x ↦ u x * v x) s μ := by
  intro x hx
  obtain ⟨a, ha, hua⟩ := hu x hx
  obtain ⟨b, hb, hvb⟩ := hv x hx
  refine ⟨a ∩ b, Filter.inter_mem ha hb, ?_⟩
  have hu' : MemLp u p (μ.restrict (a ∩ b)) :=
    hua.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl)
  have hv' : MemLp v q (μ.restrict (a ∩ b)) :=
    hvb.mono_measure (Measure.restrict_mono Set.inter_subset_right le_rfl)
  have huv : MemLp (fun x ↦ u x * v x) 1 (μ.restrict (a ∩ b)) := hu'.fun_mul hv'
  exact memLp_one_iff_integrable.1 huv

end MeasureTheory

/-! ### Local approximation in $W^{k,p}$ -/

section Approximation

open ContinuousLinearMap

variable [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F]
  {μ : Measure E} [μ.IsAddHaarMeasure] {y : Fin n → E} {f w : E → F} {p : ℝ≥0∞}

omit [CompleteSpace F] in
/-- **Mollification by a normalized bump does not increase an $L^\infty$ bound.** Let $\mu$ be an
additive Haar measure on a finite-dimensional space $E$, and let $\varphi$ be a smooth bump
centred at $0$. If $\|h\| \le M$ almost everywhere, then $\|(\varphi_\mu \star h)(x)\| \le M$ at
every point $x$. Here $\varphi_\mu$ is $\varphi$ normalized to integral one with respect to
$\mu$, a nonnegative kernel. -/
theorem ContDiffBump.norm_convolution_normed_le_of_ae_norm_le (φ : ContDiffBump (0 : E))
    {h : E → F} {M : ℝ} (hM : ∀ᵐ z ∂μ, ‖h z‖ ≤ M) (x : E) :
    ‖(φ.normed μ ⋆[lsmul ℝ ℝ, μ] h) x‖ ≤ M := by
  rw [convolution_def]
  have hbound : ∀ᵐ t ∂μ, ‖lsmul ℝ ℝ (φ.normed μ t) (h (x - t))‖ ≤ φ.normed μ t * M := by
    filter_upwards [(measurePreserving_sub_left_of_isAddRightInvariant μ x)
      |>.quasiMeasurePreserving.tendsto_ae.eventually hM] with t ht
    rw [lsmul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed t)]
    exact mul_le_mul_of_nonneg_left ht (φ.nonneg_normed t)
  refine (norm_integral_le_of_norm_le (φ.integrable_normed.mul_const M) hbound).trans (le_of_eq ?_)
  rw [integral_mul_const, φ.integral_normed, one_mul]

/-- **Local approximation in $W^{k,p}$ by smooth functions, with an $L^\infty$ bound.** Let $E$ be
finite-dimensional with an additive Haar measure $\mu$, let $F$ be complete, and let
$1 \le p < \infty$. Let $w$ be the weak derivative of $f$ along the tuple
$y = (y_1, \dots, y_n)$ on $\Omega$, with $f, w \in L^p_{\mathrm{loc}}(\Omega)$. Let $V$ be an
open set whose closure is compact and contained in $\Omega$. Then there are smooth functions
$g_0, g_1, \dots$ on $E$ such that

* $g_j \in L^p(V)$ and $\partial^y g_j \in L^p(V)$ for every $j$;
* $g_j \to f$ and $\partial^y g_j \to w$ in $L^p(V)$;
* for every $M \ge 0$ with $\|f\| \le M$ almost everywhere on $\Omega$, $\|g_j(x)\| \le M$ for
  all $j$ and all $x \in E$.

Here $\partial^y g(x) = D^n g(x)[y_1, \dots, y_n]$.

The $g_j$ are the mollifications of a compactly supported truncation of $f$. The convergence is
`ContDiffBump.tendsto_eLpNorm_convolution_sub`, the identification of $\partial^y g_j$ with the
mollification of $w$ on $V$ is `HasWeakIteratedLineDerivOn.iteratedFDeriv_convolution`, and the
bound is `ContDiffBump.norm_convolution_normed_le_of_ae_norm_le`. Without the bound, this is
`HasWeakIteratedLineDerivOn.exists_seq_contDiff_tendsto_eLpNorm`. -/
theorem HasWeakIteratedLineDerivOn.exists_seq_contDiff_tendsto_eLpNorm_and_norm_le
    (h : HasWeakIteratedLineDerivOn y f w Ω μ) (hf : LocallyMemLpOn f p Ω μ)
    (hw : LocallyMemLpOn w p Ω μ) (hp : 1 ≤ p) (hp' : p ≠ ⊤) {V : Set E} (hVo : IsOpen V)
    (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ (Ω : Set E)) :
    ∃ g : ℕ → E → F, (∀ j, ContDiff ℝ ∞ (g j)) ∧ (∀ j, MemLp (g j) p (μ.restrict V)) ∧
      (∀ j, MemLp (fun x ↦ iteratedFDeriv ℝ n (g j) x y) p (μ.restrict V)) ∧
      Tendsto (fun j ↦ eLpNorm (fun x ↦ g j x - f x) p (μ.restrict V)) atTop (𝓝 0) ∧
      Tendsto (fun j ↦ eLpNorm (fun x ↦ iteratedFDeriv ℝ n (g j) x y - w x) p (μ.restrict V))
        atTop (𝓝 0) ∧
      ∀ M, 0 ≤ M → (∀ᵐ x ∂μ.restrict (Ω : Set E), ‖f x‖ ≤ M) → ∀ j x, ‖g j x‖ ≤ M := by
  obtain ⟨W, -, hWo, hVW, -, hWc, hWΩ, -⟩ := hVc.exists_pos_forall_closedBall_subset Ω.isOpen hVΩ
  obtain ⟨V', ε, hV'o, hVV', hε, -, -, hV'ball⟩ := hVc.exists_pos_forall_closedBall_subset hWo hVW
  set C : Set E := closure W with hCdef
  have hCmeas : MeasurableSet C := hWc.isClosed.measurableSet
  have hWC : W ⊆ interior C := interior_maximal subset_closure hWo
  have hVC : V ⊆ C := (subset_closure.trans hVW).trans subset_closure
  set f' : E → F := C.indicator f with hf'def
  set w' : E → F := C.indicator w with hw'def
  have hf'Lp : MemLp f' p μ :=
    (memLp_indicator_iff_restrict hCmeas.nullMeasurableSet).2
      (hf.memLp_restrict_of_compact_subset hp' hWΩ hWc)
  have hw'Lp : MemLp w' p μ :=
    (memLp_indicator_iff_restrict hCmeas.nullMeasurableSet).2
      (hw.memLp_restrict_of_compact_subset hp' hWΩ hWc)
  have hf'loc : LocallyIntegrable f' μ := hf'Lp.locallyIntegrable hp
  have hint : HasWeakIteratedLineDerivOn y f' w' ⟨interior C, isOpen_interior⟩ μ :=
    (h.mono (interior_subset.trans hWΩ)).congr_ae
      (Filter.eventually_of_mem (self_mem_ae_restrict isOpen_interior.measurableSet)
        fun z hz ↦ (Set.indicator_of_mem (interior_subset hz) f).symm)
      (Filter.eventually_of_mem (self_mem_ae_restrict isOpen_interior.measurableSet)
        fun z hz ↦ (Set.indicator_of_mem (interior_subset hz) w).symm)
  set φ : ℕ → ContDiffBump (0 : E) := fun j ↦
    ⟨ε / (2 * (j + 2)), ε / (j + 2), by positivity, by
      apply div_lt_div_of_pos_left hε (by positivity)
      nlinarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]⟩ with hφdef
  have hrOut : ∀ j, (φ j).rOut = ε / (j + 2) := fun j ↦ rfl
  have hrOutle : ∀ j, (φ j).rOut ≤ ε := fun j ↦ by
    rw [hrOut]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
  have htend : Tendsto (fun j ↦ (φ j).rOut) atTop (𝓝 0) := by
    simp only [hrOut]
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  set g : ℕ → E → F := fun j ↦ (φ j).normed μ ⋆[lsmul ℝ ℝ, μ] f' with hgdef
  have hball : ∀ j, ∀ x ∈ V, closedBall x (φ j).rOut ⊆ interior C := fun j x hx ↦
    ((closedBall_subset_closedBall (hrOutle j)).trans
      (hV'ball x (hVV' (subset_closure hx)))).trans hWC
  have hderivEq : ∀ j, ∀ x ∈ V, iteratedFDeriv ℝ n (g j) x y
      = ((φ j).normed μ ⋆[lsmul ℝ ℝ, μ] w') x := fun j x hx ↦
    hint.iteratedFDeriv_convolution (φ j).contDiff_normed
      (le_of_eq ((φ j).tsupport_normed_eq (μ := μ))) (hball j x hx)
  have hconvLp : ∀ (j : ℕ) (c : E → F), MemLp c p μ →
      MemLp ((φ j).normed μ ⋆[lsmul ℝ ℝ, μ] c) p μ := fun j _ hc ↦
    MemLp.convolution hp (memLp_one_iff_integrable.2 (φ j).integrable_normed) hc
  refine ⟨g, fun j ↦ (φ j).hasCompactSupport_normed.contDiff_convolution_left _
    (φ j).contDiff_normed hf'loc, fun j ↦ (hconvLp j f' hf'Lp).restrict V, fun j ↦ ?_, ?_, ?_,
    fun M hM0 hM j x ↦ (φ j).norm_convolution_normed_le_of_ae_norm_le ?_ x⟩
  · refine ((hconvLp j w' hw'Lp).restrict V).ae_eq ?_
    filter_upwards [self_mem_ae_restrict hVo.measurableSet] with x hx
    exact (hderivEq j x hx).symm
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (ContDiffBump.tendsto_eLpNorm_convolution_sub htend hp hp' hf'Lp)
      (fun _ ↦ zero_le) (fun j ↦ ?_)
    refine le_trans (le_of_eq (eLpNorm_congr_ae ?_))
      (eLpNorm_mono_measure _ Measure.restrict_le_self)
    filter_upwards [self_mem_ae_restrict hVo.measurableSet] with x hx
    simp [hgdef, hf'def, Set.indicator_of_mem (hVC hx)]
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (ContDiffBump.tendsto_eLpNorm_convolution_sub htend hp hp' hw'Lp)
      (fun _ ↦ zero_le) (fun j ↦ ?_)
    refine le_trans (le_of_eq (eLpNorm_congr_ae ?_))
      (eLpNorm_mono_measure _ Measure.restrict_le_self)
    filter_upwards [self_mem_ae_restrict hVo.measurableSet] with x hx
    rw [hderivEq j x hx]
    simp [hw'def, Set.indicator_of_mem (hVC hx)]
  · filter_upwards [(ae_restrict_iff' Ω.isOpen.measurableSet).1 hM] with z hz
    by_cases hzC : z ∈ C
    · rw [hf'def, Set.indicator_of_mem hzC]
      exact hz (hWΩ hzC)
    · rw [hf'def, Set.indicator_of_notMem hzC, norm_zero]
      exact hM0

/-- **Local approximation in $W^{k,p}$ by smooth functions.** Let $E$ be finite-dimensional with an
additive Haar measure $\mu$, let $F$ be complete, and let $1 \le p < \infty$. Let $w$ be the
weak derivative of $f$ along the tuple $y = (y_1, \dots, y_n)$ on $\Omega$, with
$f, w \in L^p_{\mathrm{loc}}(\Omega)$. Let $V$ be an open set whose closure is compact and
contained in $\Omega$. Then there are smooth functions $g_0, g_1, \dots$ on $E$ with
$g_j \in L^p(V)$ and $\partial^y g_j \in L^p(V)$, such that $g_j \to f$ and
$\partial^y g_j \to w$ in $L^p(V)$. Here $\partial^y g(x) = D^n g(x)[y_1, \dots, y_n]$.

The $g_j$ are the mollifications of a compactly supported truncation of $f$. The convergence is
`ContDiffBump.tendsto_eLpNorm_convolution_sub`, and the identification of $\partial^y g_j$ with
the mollification of $w$ on $V$ is `HasWeakIteratedLineDerivOn.iteratedFDeriv_convolution`.
`HasWeakIteratedLineDerivOn.exists_seq_contDiff_tendsto_eLpNorm_and_norm_le` also bounds the
$g_j$. This is the local half of the Meyers–Serrin theorem $H = W$; it does not patch the local
approximations together over an exhaustion of $\Omega$. -/
theorem HasWeakIteratedLineDerivOn.exists_seq_contDiff_tendsto_eLpNorm
    (h : HasWeakIteratedLineDerivOn y f w Ω μ) (hf : LocallyMemLpOn f p Ω μ)
    (hw : LocallyMemLpOn w p Ω μ) (hp : 1 ≤ p) (hp' : p ≠ ⊤) {V : Set E} (hVo : IsOpen V)
    (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ (Ω : Set E)) :
    ∃ g : ℕ → E → F, (∀ j, ContDiff ℝ ∞ (g j)) ∧ (∀ j, MemLp (g j) p (μ.restrict V)) ∧
      (∀ j, MemLp (fun x ↦ iteratedFDeriv ℝ n (g j) x y) p (μ.restrict V)) ∧
      Tendsto (fun j ↦ eLpNorm (fun x ↦ g j x - f x) p (μ.restrict V)) atTop (𝓝 0) ∧
      Tendsto (fun j ↦ eLpNorm (fun x ↦ iteratedFDeriv ℝ n (g j) x y - w x) p (μ.restrict V))
        atTop (𝓝 0) := by
  obtain ⟨g, hgs, hgp, hgdp, hgt, hgdt, -⟩ :=
    h.exists_seq_contDiff_tendsto_eLpNorm_and_norm_le hf hw hp hp' hVo hVc hVΩ
  exact ⟨g, hgs, hgp, hgdp, hgt, hgdt⟩

end Approximation

/-! ### The product rule for two weakly differentiable factors -/

section ProductRule

open ContinuousLinearMap

variable [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure] {p q : ℝ≥0∞}

/-- **The product rule for weak derivatives.** Let $E$ be finite-dimensional with an additive Haar
measure $\mu$, and let $y$ be a tuple of one direction. Let $1 \le p < \infty$, and let
$q < \infty$ be the Hölder conjugate exponent of $p$ (so in fact $1 < p < \infty$). Let $w_u$ be
the weak derivative of $u$ along $y$ on $\Omega$, and $w_v$ that of $v$, with
$u, w_u \in L^p_{\mathrm{loc}}(\Omega)$ and $v, w_v \in L^q_{\mathrm{loc}}(\Omega)$. Then $uv$
has the weak derivative $w_u v + u w_v$ along $y$ on $\Omega$.

This is Proposition 7.1.11 of [han2009theoretical], which the source states without proof. The
proof mollifies $u$, applies the case of a smooth factor
(`HasWeakIteratedLineDerivOn.mul_contDiff`) on a relatively compact open neighbourhood of the
support of the test function, and passes to the limit with Hölder's inequality. The tuple $y$
has length one, as in the source, because the case of a smooth factor requires it; the length is
a variable `m` with the hypothesis `m = 1`. -/
theorem HasWeakIteratedLineDerivOn.mul {m : ℕ} {y : Fin m → E} {u wu v wv : E → ℝ}
    (hu : HasWeakIteratedLineDerivOn y u wu Ω μ) (hm : m = 1)
    (hv : HasWeakIteratedLineDerivOn y v wv Ω μ)
    (hp : 1 ≤ p) (hp' : p ≠ ⊤) (hq' : q ≠ ⊤) [ENNReal.HolderConjugate p q]
    (hup : LocallyMemLpOn u p Ω μ) (hwup : LocallyMemLpOn wu p Ω μ)
    (hvq : LocallyMemLpOn v q Ω μ) (hwvq : LocallyMemLpOn wv q Ω μ) :
    HasWeakIteratedLineDerivOn y (fun x ↦ u x * v x) (fun x ↦ wu x * v x + u x * wv x) Ω μ := by
  subst hm
  refine ⟨hup.locallyIntegrableOn_mul hvq,
    (hwup.locallyIntegrableOn_mul hvq).add (hup.locallyIntegrableOn_mul hwvq), ?_⟩
  intro φ
  -- a relatively compact open neighbourhood `V` of the support of `φ`
  obtain ⟨V, ε, hVo, hKV, hε, hVc, hVΩ, -⟩ :=
    φ.hasCompactSupport.exists_pos_forall_closedBall_subset Ω.isOpen φ.tsupport_subset
  set Ω' : Opens E := ⟨V, hVo⟩ with hΩ'def
  have hΩ'Ω : Ω' ≤ Ω := subset_closure.trans hVΩ
  set ψ : 𝓓(Ω', ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hKV⟩ with hψdef
  have hcoe : (Ω' : Set E) = V := by rw [hΩ'def]; rfl
  have hψcoe : (ψ : E → ℝ) = (φ : E → ℝ) := by rw [hψdef]; rfl
  -- the `L^p` and `L^q` memberships on `V`
  have hres : ∀ (r : ℝ≥0∞) (c : E → ℝ), r ≠ ⊤ → LocallyMemLpOn c r Ω μ →
      MemLp c r (μ.restrict V) := fun r c hr hc ↦
    (hc.memLp_restrict_of_compact_subset hr hVΩ hVc).mono_measure
      (Measure.restrict_mono subset_closure le_rfl)
  have huν : MemLp u p (μ.restrict V) := hres p u hp' hup
  have hwuν : MemLp wu p (μ.restrict V) := hres p wu hp' hwup
  have hvν : MemLp v q (μ.restrict V) := hres q v hq' hvq
  have hwvν : MemLp wv q (μ.restrict V) := hres q wv hq' hwvq
  -- the bounded factors coming from the test function
  obtain ⟨Cφ, hCφ⟩ := φ.hasCompactSupport.exists_bound_of_continuous φ.contDiff.continuous
  obtain ⟨Cd, hCd⟩ := (φ.iteratedFDerivApply 1 y).hasCompactSupport.exists_bound_of_continuous
    (φ.iteratedFDerivApply 1 y).contDiff.continuous
  have hφtop : MemLp (φ : E → ℝ) ⊤ (μ.restrict V) :=
    memLp_top_of_bound φ.contDiff.continuous.aestronglyMeasurable Cφ (.of_forall hCφ)
  have hdtop : MemLp (fun x ↦ iteratedFDeriv ℝ 1 (φ : E → ℝ) x y) ⊤ (μ.restrict V) :=
    memLp_top_of_bound (φ.iteratedFDerivApply 1 y).contDiff.continuous.aestronglyMeasurable Cd
      (.of_forall hCd)
  have hb1 : MemLp (fun x ↦ iteratedFDeriv ℝ 1 (φ : E → ℝ) x y * v x) q (μ.restrict V) :=
    hdtop.fun_mul hvν
  have hb2 : MemLp (fun x ↦ (φ : E → ℝ) x * wv x) q (μ.restrict V) := hφtop.fun_mul hwvν
  have hb3 : MemLp (fun x ↦ (φ : E → ℝ) x * v x) q (μ.restrict V) := hφtop.fun_mul hvν
  -- the mollifications of `u`
  obtain ⟨g, hgsm, hgLp, hgdLp, hgt, hgdt⟩ :=
    hu.exists_seq_contDiff_tendsto_eLpNorm hup hwup hp hp' hVo hVc hVΩ
  -- the identity for each mollification, from the smooth-factor product rule
  have key : ∀ j, (∫ x in V, (iteratedFDeriv ℝ 1 (φ : E → ℝ) x y * v x) * g j x ∂μ)
      = -((∫ x in V, ((φ : E → ℝ) x * wv x) * g j x ∂μ)
        + ∫ x in V, ((φ : E → ℝ) x * v x) * iteratedFDeriv ℝ 1 (g j) x y ∂μ) := by
    intro j
    have hj := ((hv.mono hΩ'Ω).mul_contDiff rfl (hgsm j)).integral_smul_eq ψ
    rw [hcoe, hψcoe] at hj
    have i2 : Integrable (fun x ↦ ((φ : E → ℝ) x * wv x) * g j x) (μ.restrict V) :=
      memLp_one_iff_integrable.1 (hb2.fun_mul (hgLp j))
    have i3 : Integrable
        (fun x ↦ ((φ : E → ℝ) x * v x) * iteratedFDeriv ℝ 1 (g j) x y) (μ.restrict V) :=
      memLp_one_iff_integrable.1 (hb3.fun_mul (hgdLp j))
    have e1 : (∫ x in V, iteratedFDeriv ℝ 1 (φ : E → ℝ) x y • (v x * g j x) ∂μ)
        = ∫ x in V, (iteratedFDeriv ℝ 1 (φ : E → ℝ) x y * v x) * g j x ∂μ :=
      integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [smul_eq_mul]; ring)
    have e2 : (∫ x in V, (φ : E → ℝ) x •
          (wv x * g j x + v x * iteratedFDeriv ℝ 1 (g j) x y) ∂μ)
        = (∫ x in V, ((φ : E → ℝ) x * wv x) * g j x ∂μ)
          + ∫ x in V, ((φ : E → ℝ) x * v x) * iteratedFDeriv ℝ 1 (g j) x y ∂μ := by
      rw [← integral_add i2 i3]
      exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [smul_eq_mul]; ring)
    rw [e1, e2] at hj
    simpa using hj
  -- passing to the limit
  have hfinal : (∫ x in V, (iteratedFDeriv ℝ 1 (φ : E → ℝ) x y * v x) * u x ∂μ)
      = -((∫ x in V, ((φ : E → ℝ) x * wv x) * u x ∂μ)
        + ∫ x in V, ((φ : E → ℝ) x * v x) * wu x ∂μ) := by
    refine tendsto_nhds_unique
      (tendsto_integral_mul_of_tendsto_eLpNorm hgLp huν hb1 hgt) ?_
    simp only [key]
    exact ((tendsto_integral_mul_of_tendsto_eLpNorm hgLp huν hb2 hgt).add
      (tendsto_integral_mul_of_tendsto_eLpNorm hgdLp hwuν hb3 hgdt)).neg
  -- transporting the identity from `V` to `Ω`
  have hzeroD : ∀ x ∉ V, iteratedFDeriv ℝ 1 (φ : E → ℝ) x y = 0 := fun x hx ↦
    hψcoe ▸ (ψ.iteratedFDerivApply 1 y).eq_zero_of_notMem (by rwa [← hcoe] at hx)
  have hzeroP : ∀ x ∉ V, (φ : E → ℝ) x = 0 := fun x hx ↦
    hψcoe ▸ ψ.eq_zero_of_notMem (by rwa [← hcoe] at hx)
  have hzeroD' : ∀ x ∉ (Ω : Set E), iteratedFDeriv ℝ 1 (φ : E → ℝ) x y = 0 := fun x hx ↦
    (φ.iteratedFDerivApply 1 y).eq_zero_of_notMem hx
  have hzeroP' : ∀ x ∉ (Ω : Set E), (φ : E → ℝ) x = 0 := fun x hx ↦ φ.eq_zero_of_notMem hx
  have hL : (∫ x in (Ω : Set E), iteratedFDeriv ℝ 1 (φ : E → ℝ) x y • (u x * v x) ∂μ)
      = ∫ x in V, (iteratedFDeriv ℝ 1 (φ : E → ℝ) x y * v x) * u x ∂μ := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx ↦ by rw [hzeroD' x hx, zero_smul]),
      ← setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := V) (fun x hx ↦ by rw [hzeroD x hx, zero_smul])]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [smul_eq_mul]; ring)
  have i4 : Integrable (fun x ↦ ((φ : E → ℝ) x * wv x) * u x) (μ.restrict V) :=
    memLp_one_iff_integrable.1 (hb2.fun_mul huν)
  have i5 : Integrable (fun x ↦ ((φ : E → ℝ) x * v x) * wu x) (μ.restrict V) :=
    memLp_one_iff_integrable.1 (hb3.fun_mul hwuν)
  have hR : (∫ x in (Ω : Set E), (φ : E → ℝ) x • (wu x * v x + u x * wv x) ∂μ)
      = (∫ x in V, ((φ : E → ℝ) x * wv x) * u x ∂μ)
        + ∫ x in V, ((φ : E → ℝ) x * v x) * wu x ∂μ := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx ↦ by rw [hzeroP' x hx, zero_smul]),
      ← setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := V) (fun x hx ↦ by rw [hzeroP x hx, zero_smul]), ← integral_add i4 i5]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [smul_eq_mul]; ring)
  rw [hL, hR, hfinal]
  simp

end ProductRule

/-! ### The chain rule with a $C^1$ function -/

section ChainRule

variable [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure] {p : ℝ≥0∞}

/-- A $C^1$ function $f : \mathbb{R} \to \mathbb{R}$ with $|f'| \le M$ is $M$-Lipschitz:
$|f(a) - f(b)| \le M |a - b|$ for all $a, b$. -/
theorem abs_sub_le_mul_of_abs_deriv_le {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {M : ℝ}
    (hM : ∀ t, |deriv f t| ≤ M) (a b : ℝ) : |f a - f b| ≤ M * |a - b| := by
  have := (convex_univ (𝕜 := ℝ) (E := ℝ)).norm_image_sub_le_of_norm_deriv_le (f := f) (C := M)
    (fun x _ ↦ (hf.differentiable one_ne_zero).differentiableAt)
    (fun x _ ↦ by simpa [Real.norm_eq_abs] using hM x) (mem_univ b) (mem_univ a)
  simpa [Real.norm_eq_abs] using this

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- **The classical chain rule** for the first derivative along one direction. Let
$f : \mathbb{R} \to \mathbb{R}$ be $C^1$ and $g : E \to \mathbb{R}$ smooth. Then for $x \in E$
and a direction $y$,
$$D(f \circ g)(x)[y] = f'(g(x)) \, Dg(x)[y].$$
The derivatives are the first iterated derivatives, along a tuple of one direction. -/
theorem iteratedFDeriv_one_comp {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {g : E → ℝ}
    (hg : ContDiff ℝ ∞ g) (y : Fin 1 → E) (x : E) :
    iteratedFDeriv ℝ 1 (fun z ↦ f (g z)) x y = deriv f (g x) * iteratedFDeriv ℝ 1 g x y := by
  rw [iteratedFDeriv_one_apply, iteratedFDeriv_one_apply]
  have hgd : HasFDerivAt g (fderiv ℝ g x) x :=
    ((hg.differentiable (by simp)).differentiableAt).hasFDerivAt
  have hfd : HasDerivAt f (deriv f (g x)) (g x) :=
    ((hf.differentiable one_ne_zero).differentiableAt).hasDerivAt
  have hcomp : HasFDerivAt (fun z ↦ f (g z)) (deriv f (g x) • fderiv ℝ g x) x := by
    simpa [Function.comp_def] using hfd.comp_hasFDerivAt x hgd
  rw [hcomp.fderiv]
  simp

/-- **The chain rule for weak derivatives.** Let $E$ be finite-dimensional with an additive Haar
measure $\mu$, let $y$ be a tuple of one direction, and let $1 \le p < \infty$. Let $w$ be the
weak derivative of $v$ along $y$ on $\Omega$, with $v, w \in L^p_{\mathrm{loc}}(\Omega)$. Let
$f : \mathbb{R} \to \mathbb{R}$ be $C^1$ with $|f'| \le M$. Then $f \circ v$ has the weak
derivative $(f' \circ v) \, w$ along $y$ on $\Omega$.

This is Proposition 7.1.12 of [han2009theoretical], which the source states without proof, for
$v \in W^{1,p}$ on a bounded open set; the local hypotheses here are weaker. The length of $y$
is a variable `m` with the hypothesis `m = 1`.

Unlike the product rule, there is no simple special case: $f \circ v$ cannot be integrated by
parts against a test function before $v$ is approximated by smooth functions. The proof
mollifies $v$ on a relatively compact open neighbourhood of the support of the test function,
uses the classical chain rule there, and passes to the limit. The terms with a bounded factor
converge in $L^1$. The term $(f' \circ v_\varepsilon - f' \circ v) \, \partial v$ converges by
dominated convergence, along a subsequence that converges almost everywhere. -/
theorem HasWeakIteratedLineDerivOn.contDiff_comp {m : ℕ} {y : Fin m → E} {v w : E → ℝ}
    (h : HasWeakIteratedLineDerivOn y v w Ω μ) (hm : m = 1)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {M : ℝ} (hM : ∀ t, |deriv f t| ≤ M)
    (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    (hv : LocallyMemLpOn v p Ω μ) (hw : LocallyMemLpOn w p Ω μ) :
    HasWeakIteratedLineDerivOn y (fun x ↦ f (v x)) (fun x ↦ deriv f (v x) * w x) Ω μ := by
  subst hm
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hfc : Continuous f := hf.continuous
  have hdfc : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hlin : ∀ t, |f t| ≤ |f 0| + M * |t| := fun t ↦ by
    have h1 := abs_sub_le_mul_of_abs_deriv_le hf hM t 0
    rw [sub_zero] at h1
    have h2 : |f t| ≤ |f t - f 0| + |f 0| := by
      calc |f t| = ‖f t - f 0 + f 0‖ := by rw [Real.norm_eq_abs]; congr 1; ring
        _ ≤ ‖f t - f 0‖ + ‖f 0‖ := norm_add_le _ _
        _ = |f t - f 0| + |f 0| := by rw [Real.norm_eq_abs, Real.norm_eq_abs]
    linarith
  -- local integrability of the two functions in the statement
  have hlocf : LocallyIntegrableOn (fun x ↦ f (v x)) Ω μ := by
    intro x hx
    obtain ⟨s, hs, hvs⟩ := h.locallyIntegrableOn x hx
    refine ⟨s ∩ ball x 1, Filter.inter_mem hs (nhdsWithin_le_nhds (ball_mem_nhds x one_pos)), ?_⟩
    have hvs' : IntegrableOn v (s ∩ ball x 1) μ := hvs.mono_set Set.inter_subset_left
    have : IsFiniteMeasure (μ.restrict (s ∩ ball x 1)) := by
      constructor
      rw [Measure.restrict_apply_univ]
      exact (measure_mono Set.inter_subset_right).trans_lt measure_ball_lt_top
    have hdom : Integrable (fun z ↦ |f 0| + M * |v z|) (μ.restrict (s ∩ ball x 1)) :=
      (integrable_const (|f 0|)).add (hvs'.abs.const_mul M)
    refine Integrable.mono hdom (hfc.comp_aestronglyMeasurable hvs'.aestronglyMeasurable)
      (Eventually.of_forall fun z ↦ ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (abs_nonneg _) (mul_nonneg hM0 (abs_nonneg _)))]
    exact hlin (v z)
  have hlocd : LocallyIntegrableOn (fun x ↦ deriv f (v x) * w x) Ω μ := by
    intro x hx
    obtain ⟨s, hs, hvs⟩ := h.locallyIntegrableOn x hx
    obtain ⟨t, ht, hws⟩ := h.locallyIntegrableOn_weakDeriv x hx
    refine ⟨s ∩ t, Filter.inter_mem hs ht, ?_⟩
    have hvs' : IntegrableOn v (s ∩ t) μ := hvs.mono_set Set.inter_subset_left
    have hws' : IntegrableOn w (s ∩ t) μ := hws.mono_set Set.inter_subset_right
    refine Integrable.mono (hws'.abs.const_mul M) ?_ (Eventually.of_forall fun z ↦ ?_)
    · exact (hdfc.comp_aestronglyMeasurable hvs'.aestronglyMeasurable).mul
        hws'.aestronglyMeasurable
    · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (mul_nonneg hM0 (abs_nonneg (w z)))]
      exact mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _)
  refine ⟨hlocf, hlocd, ?_⟩
  intro φ
  -- a relatively compact open neighbourhood `V` of the support of `φ`
  obtain ⟨V, ε, hVo, hKV, hε, hVc, hVΩ, -⟩ :=
    φ.hasCompactSupport.exists_pos_forall_closedBall_subset Ω.isOpen φ.tsupport_subset
  set Ω' : Opens E := ⟨V, hVo⟩ with hΩ'def
  set ψ : 𝓓(Ω', ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hKV⟩ with hψdef
  have hcoe : (Ω' : Set E) = V := by rw [hΩ'def]; rfl
  have hψcoe : (ψ : E → ℝ) = (φ : E → ℝ) := by rw [hψdef]; rfl
  have hνfin : IsFiniteMeasure (μ.restrict V) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (measure_mono subset_closure) hVc.measure_lt_top
  have hvν : MemLp v p (μ.restrict V) :=
    (hv.memLp_restrict_of_compact_subset hp' hVΩ hVc).mono_measure
      (Measure.restrict_mono subset_closure le_rfl)
  have hwν : MemLp w p (μ.restrict V) :=
    (hw.memLp_restrict_of_compact_subset hp' hVΩ hVc).mono_measure
      (Measure.restrict_mono subset_closure le_rfl)
  -- the mollifications of `v`, along a subsequence converging almost everywhere
  obtain ⟨g₀, hg₀sm, hg₀Lp, hg₀dLp, hg₀t, hg₀dt⟩ :=
    h.exists_seq_contDiff_tendsto_eLpNorm hv hw hp hp' hVo hVc hVΩ
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (p := p) (μ := μ.restrict V)
      (lt_of_lt_of_le zero_lt_one hp).ne' hg₀t).exists_seq_tendsto_ae
  set g : ℕ → E → ℝ := fun k ↦ g₀ (ns k) with hgdef
  have hgsm : ∀ k, ContDiff ℝ ∞ (g k) := fun k ↦ hg₀sm (ns k)
  have hgLp : ∀ k, MemLp (g k) p (μ.restrict V) := fun k ↦ hg₀Lp (ns k)
  have hgdLp : ∀ k, MemLp (fun x ↦ iteratedFDeriv ℝ 1 (g k) x y) p (μ.restrict V) := fun k ↦
    hg₀dLp (ns k)
  have hgt : Tendsto (fun k ↦ eLpNorm (fun x ↦ g k x - v x) p (μ.restrict V)) atTop (𝓝 0) :=
    hg₀t.comp hns.tendsto_atTop
  have hgdt : Tendsto
      (fun k ↦ eLpNorm (fun x ↦ iteratedFDeriv ℝ 1 (g k) x y - w x) p (μ.restrict V))
      atTop (𝓝 0) := hg₀dt.comp hns.tendsto_atTop
  -- everything relevant is integrable on `V`, the measure being finite
  have hvL1 : MemLp v 1 (μ.restrict V) := hvν.mono_exponent hp
  have hwL1 : MemLp w 1 (μ.restrict V) := hwν.mono_exponent hp
  have hgL1 : ∀ k, MemLp (g k) 1 (μ.restrict V) := fun k ↦ (hgLp k).mono_exponent hp
  have hgdL1 : ∀ k, MemLp (fun x ↦ iteratedFDeriv ℝ 1 (g k) x y) 1 (μ.restrict V) := fun k ↦
    (hgdLp k).mono_exponent hp
  have hgt1 : Tendsto (fun k ↦ eLpNorm (fun x ↦ g k x - v x) 1 (μ.restrict V)) atTop (𝓝 0) :=
    tendsto_eLpNorm_one_of_tendsto_eLpNorm hp
      (fun k ↦ ((hgLp k).sub hvν).aestronglyMeasurable) hgt
  have hgdt1 : Tendsto
      (fun k ↦ eLpNorm (fun x ↦ iteratedFDeriv ℝ 1 (g k) x y - w x) 1 (μ.restrict V))
      atTop (𝓝 0) :=
    tendsto_eLpNorm_one_of_tendsto_eLpNorm hp
      (fun k ↦ ((hgdLp k).sub hwν).aestronglyMeasurable) hgdt
  -- `f` composed with an `L^1` function is `L^1`
  have hcompL1 : ∀ c : E → ℝ, MemLp c 1 (μ.restrict V) →
      MemLp (fun x ↦ f (c x)) 1 (μ.restrict V) := by
    intro c hc
    have hdom : MemLp (fun x ↦ |f 0| + M * |c x|) 1 (μ.restrict V) :=
      (memLp_const (|f 0|)).add (hc.abs.const_mul M)
    refine MemLp.of_le hdom (hfc.comp_aestronglyMeasurable hc.aestronglyMeasurable)
      (Eventually.of_forall fun z ↦ ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (abs_nonneg _) (mul_nonneg hM0 (abs_nonneg _)))]
    exact hlin (c z)
  -- the bounded factors coming from the test function
  obtain ⟨Cφ, hCφ⟩ := φ.hasCompactSupport.exists_bound_of_continuous φ.contDiff.continuous
  obtain ⟨Cd, hCd⟩ := (φ.iteratedFDerivApply 1 y).hasCompactSupport.exists_bound_of_continuous
    (φ.iteratedFDerivApply 1 y).contDiff.continuous
  have hCφ' : ∀ z, |(φ : E → ℝ) z| ≤ Cφ := fun z ↦ by simpa [Real.norm_eq_abs] using hCφ z
  have hCφ0 : 0 ≤ Cφ := le_trans (abs_nonneg _) (hCφ' 0)
  have hdtop : MemLp (fun x ↦ iteratedFDeriv ℝ 1 (φ : E → ℝ) x y) ⊤ (μ.restrict V) :=
    memLp_top_of_bound (φ.iteratedFDerivApply 1 y).contDiff.continuous.aestronglyMeasurable Cd
      (.of_forall hCd)
  -- a bounded factor times an `L^1` function is `L^1`
  have hbdmul : ∀ (b d : E → ℝ) (C : ℝ), 0 ≤ C → (∀ z, |b z| ≤ C) →
      AEStronglyMeasurable b (μ.restrict V) → MemLp d 1 (μ.restrict V) →
      MemLp (fun x ↦ b x * d x) 1 (μ.restrict V) := by
    intro b d C hC0 hCb hbm hd
    have hdom : MemLp (fun x ↦ C * |d x|) 1 (μ.restrict V) := hd.abs.const_mul C
    refine MemLp.of_le hdom (hbm.mul hd.aestronglyMeasurable) (Eventually.of_forall fun z ↦ ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg hC0 (abs_nonneg _))]
    exact mul_le_mul_of_nonneg_right (hCb z) (abs_nonneg _)
  have hφdm : ∀ c : E → ℝ, AEStronglyMeasurable c (μ.restrict V) →
      AEStronglyMeasurable (fun x ↦ (φ : E → ℝ) x * deriv f (c x)) (μ.restrict V) := fun c hc ↦
    φ.contDiff.continuous.aestronglyMeasurable.mul (hdfc.comp_aestronglyMeasurable hc)
  have hφdb : ∀ c : E → ℝ, ∀ z, |(φ : E → ℝ) z * deriv f (c z)| ≤ Cφ * M := fun c z ↦ by
    rw [abs_mul]
    exact mul_le_mul (hCφ' z) (hM _) (abs_nonneg _) hCφ0
  have hIinf : MemLp (fun x ↦ ((φ : E → ℝ) x * deriv f (v x)) * w x) 1 (μ.restrict V) :=
    hbdmul _ _ (Cφ * M) (mul_nonneg hCφ0 hM0) (hφdb v) (hφdm v hvL1.aestronglyMeasurable) hwL1
  have hIk : ∀ k, MemLp (fun x ↦ ((φ : E → ℝ) x * deriv f (g k x)) *
      iteratedFDeriv ℝ 1 (g k) x y) 1 (μ.restrict V) := fun k ↦
    hbdmul _ _ (Cφ * M) (mul_nonneg hCφ0 hM0) (hφdb (g k))
      (hφdm (g k) (hgL1 k).aestronglyMeasurable) (hgdL1 k)
  -- the identity for each mollification, from the classical chain rule
  have key : ∀ k, (∫ x in V, iteratedFDeriv ℝ 1 (φ : E → ℝ) x y * f (g k x) ∂μ)
      = -∫ x in V, ((φ : E → ℝ) x * deriv f (g k x)) * iteratedFDeriv ℝ 1 (g k) x y ∂μ := by
    intro k
    have hcd : ContDiff ℝ 1 (fun z ↦ f (g k z)) := hf.comp ((hgsm k).of_le (by simp))
    have h1 := (hcd.contDiffOn (s := (Ω' : Set E))).hasWeakIteratedFDerivOn (μ := μ) (m := 1)
      le_rfl
    have h2 := h1.lineDeriv y
    rw [funext (fun x ↦ iteratedFDeriv_one_comp hf (hgsm k) y x)] at h2
    have hj := h2.integral_smul_eq ψ
    rw [hcoe, hψcoe] at hj
    simpa [smul_eq_mul, mul_assoc] using hj
  -- limit of the left-hand sides
  have hfgt : Tendsto (fun k ↦ eLpNorm (fun x ↦ f (g k x) - f (v x)) 1 (μ.restrict V))
      atTop (𝓝 0) := by
    have hbd : ∀ k, eLpNorm (fun x ↦ f (g k x) - f (v x)) 1 (μ.restrict V)
        ≤ ‖M‖ₑ * eLpNorm (fun x ↦ g k x - v x) 1 (μ.restrict V) := by
      intro k
      rw [← eLpNorm_const_smul M (fun x ↦ g k x - v x) 1 (μ.restrict V)]
      refine eLpNorm_mono ((hfc.comp_aestronglyMeasurable
        (hgsm k).continuous.aestronglyMeasurable).sub
        (hfc.comp_aestronglyMeasurable hvν.aestronglyMeasurable)) fun x ↦ ?_
      rw [Real.norm_eq_abs, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg hM0]
      exact abs_sub_le_mul_of_abs_deriv_le hf hM _ _
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le) hbd
    simpa using ENNReal.Tendsto.const_mul hgt1 (Or.inr (by simp))
  have hLHS : Tendsto (fun k ↦ ∫ x in V, iteratedFDeriv ℝ 1 (φ : E → ℝ) x y * f (g k x) ∂μ)
      atTop (𝓝 (∫ x in V, iteratedFDeriv ℝ 1 (φ : E → ℝ) x y * f (v x) ∂μ)) :=
    tendsto_integral_mul_of_tendsto_eLpNorm (fun k ↦ hcompL1 _ (hgL1 k)) (hcompL1 _ hvL1) hdtop
      hfgt
  -- limit of the right-hand sides, in two steps
  have hT1 : Tendsto (fun k ↦ ∫ x in V,
      ((φ : E → ℝ) x * deriv f (g k x)) * (iteratedFDeriv ℝ 1 (g k) x y - w x) ∂μ)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hbd : ∀ k, ‖∫ x in V,
        ((φ : E → ℝ) x * deriv f (g k x)) * (iteratedFDeriv ℝ 1 (g k) x y - w x) ∂μ‖
        ≤ (ENNReal.ofReal (Cφ * M) *
          eLpNorm (fun x ↦ iteratedFDeriv ℝ 1 (g k) x y - w x) 1 (μ.restrict V)).toReal := by
      intro k
      have hfin : ENNReal.ofReal (Cφ * M) *
          eLpNorm (fun x ↦ iteratedFDeriv ℝ 1 (g k) x y - w x) 1 (μ.restrict V) ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top ((hgdL1 k).sub hwL1).eLpNorm_lt_top.ne
      calc ‖∫ x in V, ((φ : E → ℝ) x * deriv f (g k x)) *
              (iteratedFDeriv ℝ 1 (g k) x y - w x) ∂μ‖
          = ‖∫ x in V, ((φ : E → ℝ) x * deriv f (g k x)) *
              (iteratedFDeriv ℝ 1 (g k) x y - w x) ∂μ‖ₑ.toReal := by
            rw [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)]
        _ ≤ _ := ENNReal.toReal_mono hfin (enorm_integral_smul_le_of_bound (hφdb (g k)))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun _ ↦ norm_nonneg _) hbd
    rw [show (0 : ℝ) = (0 : ℝ≥0∞).toReal by simp]
    refine (ENNReal.tendsto_toReal (by simp)).comp ?_
    simpa using ENNReal.Tendsto.const_mul hgdt1 (Or.inr ENNReal.ofReal_ne_top)
  have hT2 : Tendsto (fun k ↦ ∫ x in V,
      ((φ : E → ℝ) x * (deriv f (g k x) - deriv f (v x))) * w x ∂μ) atTop (𝓝 0) := by
    have hzero : (0 : ℝ) = ∫ _x in V, (0 : ℝ) ∂μ := by simp
    rw [hzero]
    refine tendsto_integral_of_dominated_convergence (fun x ↦ (Cφ * (2 * M)) * |w x|)
      (fun k ↦ ?_) (memLp_one_iff_integrable.1 (hwL1.abs.const_mul (Cφ * (2 * M))))
      (fun k ↦ Eventually.of_forall fun z ↦ ?_) ?_
    · exact (φ.contDiff.continuous.aestronglyMeasurable.mul
        ((hdfc.comp_aestronglyMeasurable (hgL1 k).aestronglyMeasurable).sub
          (hdfc.comp_aestronglyMeasurable hvL1.aestronglyMeasurable))).mul
        hwL1.aestronglyMeasurable
    · have h2 : |deriv f (g k z) - deriv f (v z)| ≤ 2 * M := by
        have := abs_sub (deriv f (g k z)) (deriv f (v z))
        linarith [hM (g k z), hM (v z), abs_sub_abs_le_abs_sub (deriv f (g k z)) (deriv f (v z))]
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (hCφ' z) h2 (abs_nonneg _) hCφ0) (abs_nonneg _)
    · filter_upwards [hae] with z hz
      have hd : Tendsto (fun k ↦ deriv f (g k z)) atTop (𝓝 (deriv f (v z))) :=
        (hdfc.tendsto (v z)).comp hz
      have : Tendsto (fun k ↦ ((φ : E → ℝ) z * (deriv f (g k z) - deriv f (v z))) * w z) atTop
          (𝓝 (((φ : E → ℝ) z * (deriv f (v z) - deriv f (v z))) * w z)) :=
        ((tendsto_const_nhds.mul (hd.sub tendsto_const_nhds)).mul tendsto_const_nhds)
      simpa using this
  have hRHS : Tendsto (fun k ↦ ∫ x in V,
      ((φ : E → ℝ) x * deriv f (g k x)) * iteratedFDeriv ℝ 1 (g k) x y ∂μ)
      atTop (𝓝 (∫ x in V, ((φ : E → ℝ) x * deriv f (v x)) * w x ∂μ)) := by
    have hsplit : ∀ k, (∫ x in V, ((φ : E → ℝ) x * deriv f (g k x)) *
          iteratedFDeriv ℝ 1 (g k) x y ∂μ)
        = (∫ x in V, ((φ : E → ℝ) x * deriv f (g k x)) *
            (iteratedFDeriv ℝ 1 (g k) x y - w x) ∂μ)
          + (∫ x in V, ((φ : E → ℝ) x * (deriv f (g k x) - deriv f (v x))) * w x ∂μ)
          + ∫ x in V, ((φ : E → ℝ) x * deriv f (v x)) * w x ∂μ := by
      intro k
      have i1 : Integrable (fun x ↦ ((φ : E → ℝ) x * deriv f (g k x)) *
          (iteratedFDeriv ℝ 1 (g k) x y - w x)) (μ.restrict V) :=
        memLp_one_iff_integrable.1 (hbdmul _ _ (Cφ * M) (mul_nonneg hCφ0 hM0) (hφdb (g k))
          (hφdm (g k) (hgL1 k).aestronglyMeasurable) ((hgdL1 k).sub hwL1))
      have i2 : Integrable (fun x ↦ ((φ : E → ℝ) x * (deriv f (g k x) - deriv f (v x))) * w x)
          (μ.restrict V) := by
        refine memLp_one_iff_integrable.1 (hbdmul _ _ (Cφ * (2 * M))
          (by positivity) (fun z ↦ ?_) ?_ hwL1)
        · rw [abs_mul]
          refine mul_le_mul (hCφ' z) ?_ (abs_nonneg _) hCφ0
          have h3 : |deriv f (g k z) - deriv f (v z)| ≤ |deriv f (g k z)| + |deriv f (v z)| := by
            simpa [Real.norm_eq_abs] using norm_sub_le (deriv f (g k z)) (deriv f (v z))
          linarith [hM (g k z), hM (v z)]
        · exact φ.contDiff.continuous.aestronglyMeasurable.mul
            ((hdfc.comp_aestronglyMeasurable (hgL1 k).aestronglyMeasurable).sub
              (hdfc.comp_aestronglyMeasurable hvL1.aestronglyMeasurable))
      have i12 : Integrable (fun x ↦ ((φ : E → ℝ) x * deriv f (g k x)) *
          (iteratedFDeriv ℝ 1 (g k) x y - w x)
          + ((φ : E → ℝ) x * (deriv f (g k x) - deriv f (v x))) * w x) (μ.restrict V) := i1.add i2
      rw [← integral_add i1 i2, ← integral_add i12 (memLp_one_iff_integrable.1 hIinf)]
      exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
    simp only [hsplit]
    simpa using (hT1.add hT2).add
      (tendsto_const_nhds (x := ∫ x in V, ((φ : E → ℝ) x * deriv f (v x)) * w x ∂μ))
  -- the identity in the limit, transported from `V` to `Ω`
  have hfinal : (∫ x in V, iteratedFDeriv ℝ 1 (φ : E → ℝ) x y * f (v x) ∂μ)
      = -∫ x in V, ((φ : E → ℝ) x * deriv f (v x)) * w x ∂μ := by
    refine tendsto_nhds_unique hLHS ?_
    simp only [key]
    exact hRHS.neg
  have hzeroD : ∀ x ∉ V, iteratedFDeriv ℝ 1 (φ : E → ℝ) x y = 0 := fun x hx ↦
    hψcoe ▸ (ψ.iteratedFDerivApply 1 y).eq_zero_of_notMem (by rwa [← hcoe] at hx)
  have hzeroP : ∀ x ∉ V, (φ : E → ℝ) x = 0 := fun x hx ↦
    hψcoe ▸ ψ.eq_zero_of_notMem (by rwa [← hcoe] at hx)
  have hzeroD' : ∀ x ∉ (Ω : Set E), iteratedFDeriv ℝ 1 (φ : E → ℝ) x y = 0 := fun x hx ↦
    (φ.iteratedFDerivApply 1 y).eq_zero_of_notMem hx
  have hzeroP' : ∀ x ∉ (Ω : Set E), (φ : E → ℝ) x = 0 := fun x hx ↦ φ.eq_zero_of_notMem hx
  have hL : (∫ x in (Ω : Set E), iteratedFDeriv ℝ 1 (φ : E → ℝ) x y • f (v x) ∂μ)
      = ∫ x in V, iteratedFDeriv ℝ 1 (φ : E → ℝ) x y * f (v x) ∂μ := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx ↦ by rw [hzeroD' x hx, zero_smul]),
      ← setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := V) (fun x hx ↦ by rw [hzeroD x hx, zero_smul])]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [smul_eq_mul])
  have hR : (∫ x in (Ω : Set E), (φ : E → ℝ) x • (deriv f (v x) * w x) ∂μ)
      = ∫ x in V, ((φ : E → ℝ) x * deriv f (v x)) * w x ∂μ := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx ↦ by rw [hzeroP' x hx, zero_smul]),
      ← setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := V) (fun x hx ↦ by rw [hzeroP x hx, zero_smul])]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [smul_eq_mul, mul_assoc])
  rw [hL, hR, hfinal]
  simp

end ChainRule
