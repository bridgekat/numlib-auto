/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.WeakDeriv`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.TestFunction
import Numlib.Analysis.Calculus.ContDiffConstOffCompact
import Numlib.Analysis.Calculus.IteratedFDeriv

/-!
# Weak derivatives on an open set

Let $\Omega$ be an open subset of a real normed space $E$, and let $f : E \to F$. A function $w$
with values in the continuous $n$-linear maps $E^n \to F$ is an **$n$-th weak derivative** of $f$ on
$\Omega$ if $f$ and $w$ are locally integrable on $\Omega$ and the integration by parts formula
$$\int_\Omega D^n \varphi(x)(y) \, f(x) \, dx = (-1)^n \int_\Omega \varphi(x) \, w(x)(y) \, dx$$
holds for every test function $\varphi \in C_0^\infty(\Omega)$ and every tuple
$y = (y_1, \dots, y_n)$ of directions in $E$. This is Definition 7.1.3 of [han2009theoretical], read
for all multi-indices of length $n$ at once: a tuple of $n$ directions plays the role of a
multi-index $\alpha$ with $|\alpha| = n$. The module proves that a weak derivative is unique almost
everywhere, that a classical derivative is a weak derivative, that weak differentiation is linear,
and the Leibniz rule for a smooth factor.

## Main definitions

* `MeasureTheory.LocallyMemLpOn`: the space $L^p_{\mathrm{loc}}(s)$ of functions that are
  $p$-integrable near every point of $s$, Definition 7.1.1 of [han2009theoretical].
* `HasWeakIteratedFDerivOn`: the weak derivative of order $n$, Definition 7.1.3 of
  [han2009theoretical].
* `HasWeakFDerivOn`: the first-order weak derivative, with values in $E \to_L F$.
* `HasWeakIteratedLineDerivOn`: the weak derivative along one fixed tuple $y$ of directions, with
  values in $F$. This is Definition 7.1.3 of [han2009theoretical] for a single multi-index.

## Main results

* `HasWeakIteratedFDerivOn.ae_eq` and `HasWeakIteratedLineDerivOn.ae_eq`: a weak derivative is
  unique almost everywhere on $\Omega$, Lemma 7.1.4 of [han2009theoretical].
* `ContDiffOn.hasWeakIteratedFDerivOn`: the classical derivative of order $n$ of a $C^N$ function on
  $\Omega$ is its weak derivative for every $n \le N$, Lemma 7.1.5 of [han2009theoretical].
* `HasWeakIteratedFDerivOn.add`, `HasWeakIteratedFDerivOn.const_smul`,
  `HasWeakIteratedFDerivOn.neg`, `HasWeakIteratedFDerivOn.sub`, `HasWeakIteratedFDerivOn.zero`: weak
  differentiation is linear, Proposition 7.1.10 of [han2009theoretical].
* `HasWeakIteratedLineDerivOn.mul_contDiff`: the Leibniz rule at first order when one factor is
  smooth, a special case of Proposition 7.1.11 of [han2009theoretical].
* `HasWeakIteratedLineDerivOn.cons` and `HasWeakIteratedLineDerivOn.of_cons`: a weak derivative
  along $(z, y_1, \dots, y_n)$ is the weak derivative in the direction $z$ of the weak derivative
  along $(y_1, \dots, y_n)$.
* `HasWeakIteratedFDerivOn.mono` and `HasWeakIteratedLineDerivOn.mono`: a weak derivative on
  $\Omega$ is a weak derivative on every smaller open set.
* `HasWeakIteratedLineDerivOn.comp_continuousLinearMap`: a continuous linear map passes through the
  weak derivative.
* `HasWeakIteratedLineDerivOn.ofReal_iff`: a real function has a real weak derivative if and only if
  its complexification has the complexified weak derivative.
* `MeasureTheory.LocallyMemLpOn.memLp_restrict_of_compact_subset`: for $p < \infty$, a function in
  $L^p_{\mathrm{loc}}(s)$ is in $L^p$ of every compact subset of $s$.

## Proof outline

Uniqueness applies the generalized variational lemma
`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` of Mathlib, which is Lemma 7.1.2 of
[han2009theoretical], to the difference of two weak derivatives. The Leibniz rule for a smooth
factor needs no mollification: the product of a test function with a smooth function is again a test
function (`TestFunction.mulContDiff`), so the identity is a direct integration by parts.

## Implementation notes

* The Mathlib module `Mathlib.Analysis.Distribution.Sobolev` is about the Bessel potential spaces
  $H^{s,p}$ of tempered distributions on the whole space. It has no weak derivative on an open set.
* Mathlib PR 32305 and its continuation `grunweg/SobolevSlobodeckij` (Michael Rothgang, Filippo
  Nuccio and Floris van Doorn) develop weak derivatives, $W^{k,p}(\Omega)$ and the
  Sobolev–Slobodeckij spaces in far greater depth. That development uses an older Lean toolchain and
  cannot be imported here. The names and the argument order of this module follow it where possible,
  with `Ω : TopologicalSpace.Opens E` and a trailing measure argument, and `MemSobolev f k p Ω μ` in
  `Numlib.Analysis.Sobolev.Domain`, so that a later migration to it is a renaming and not a rewrite.
* There are two differences from that development. There the weak derivative is a distribution, an
  element of $\mathcal{D}'(\Omega, E \to_L F)$, obtained from a weak Taylor series through
  `FormalMultilinearSeries`. Here it is a predicate that relates two functions, which is lighter and
  is all that the integration by parts formula needs. Also, the order here is an explicit $n$ and
  the derivative has values in `ContinuousMultilinearMap`, so that one object describes all
  derivatives of order $n$ without an iteration of the construction.
* `HasWeakIteratedLineDerivOn` returns to the classical indexing by multi-indices: it fixes the
  tuple of directions and so has values in $F$. `Numlib.Analysis.Sobolev.MultiIndex` needs it,
  because the norm of Definition 7.2.2 of [han2009theoretical] sums over the multi-indices $\alpha$
  separately and not over the orders $|\alpha|$, and that norm is the one that an inner product
  induces when $p = 2$. The tuple-by-tuple form is one component of the tensor form, by
  `HasWeakIteratedFDerivOn.lineDeriv`.
* The definition differentiates the test function $n$ times. The lemma
  `ContDiff.fderiv_iteratedFDeriv_apply` of `Numlib.Analysis.Calculus.IteratedFDeriv` states that,
  for a smooth function, an extra directional derivative can be taken either inside or outside the
  $n$ iterated ones. This lemma makes the two sides of the integration by parts formula carry the
  same tuple $y$. Without it the formula would relate $D^n \varphi(y)$ to
  $D^n f(y \circ \mathrm{rev})$, because $n$ integrations by parts move the derivatives onto $f$ in
  the opposite order. The same module proves the symmetry `ContDiff.iteratedFDeriv_congr_perm` of
  the iterated derivative of a $C^\infty$ function, on which the multi-index reading of
  `Numlib.Analysis.Sobolev.MultiIndex` rests.
-/

open Filter MeasureTheory Set TopologicalSpace

open scoped ContDiff Distributions ENNReal Topology

/-! ### Locally $p$-integrable functions -/

namespace MeasureTheory

variable {X G : Type*} [TopologicalSpace X] [MeasurableSpace X] [NormedAddCommGroup G]
  {f : X → G} {s t : Set X} {μ : Measure X} {p : ℝ≥0∞}

/-- A function $f$ is **locally $p$-integrable on $s$**, written $f \in L^p_{\mathrm{loc}}(s)$, if
every point $x \in s$ has a neighbourhood $u$ relative to $s$ such that $f \in L^p(u)$.

This is Definition 7.1.1 of [han2009theoretical]. For $p = 1$ it is
`MeasureTheory.LocallyIntegrableOn`, by `MeasureTheory.locallyMemLpOn_one_iff`. -/
def LocallyMemLpOn (f : X → G) (p : ℝ≥0∞) (s : Set X) (μ : Measure X := by volume_tac) : Prop :=
  ∀ x ∈ s, ∃ u ∈ 𝓝[s] x, MemLp f p (μ.restrict u)

/-- A function is locally $1$-integrable on $s$ if and only if it is locally integrable on $s$. -/
theorem locallyMemLpOn_one_iff : LocallyMemLpOn f 1 s μ ↔ LocallyIntegrableOn f s μ := by
  simp only [LocallyMemLpOn, LocallyIntegrableOn, IntegrableAtFilter, IntegrableOn,
    memLp_one_iff_integrable]

alias ⟨LocallyMemLpOn.locallyIntegrableOn, LocallyIntegrableOn.locallyMemLpOn⟩ :=
  locallyMemLpOn_one_iff

section LocalLp

omit [TopologicalSpace X] in
/-- Let $f, g$ be real functions, with $g \in L^q(\nu)$ and $f$ almost everywhere strongly
measurable. If $|f(x)| \le c |g(x)|$ for almost every $x$, then $f \in L^q(\nu)$. -/
theorem MemLp.of_ae_norm_le_mul {ν : Measure X} {f g : X → ℝ} {q : ℝ≥0∞} (hg : MemLp g q ν)
    (hf : AEStronglyMeasurable f ν) {c : ℝ}
    (h : ∀ᵐ x ∂ν, |f x| ≤ c * |g x|) : MemLp f q ν :=
  (hg.const_mul c).of_le hf (h.mono fun x hx ↦ by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    exact hx.trans (mul_le_mul_of_nonneg_right (le_abs_self c) (abs_nonneg _)))

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
  {μ : Measure E} [IsLocallyFiniteMeasure μ] {Ω : Opens E} {p : ℝ≥0∞}

omit [BorelSpace E] [ProperSpace E] [IsLocallyFiniteMeasure μ] in
/-- A real function in $L^p(\Omega)$ is locally $p$-integrable on $\Omega$. -/
theorem MemLp.locallyMemLpOn {f : E → ℝ}
    (hf : MemLp f p (μ.restrict (Ω : Set E))) : LocallyMemLpOn f p Ω μ :=
  fun _ _ ↦ ⟨Ω, self_mem_nhdsWithin, hf⟩

open Metric in
/-- Let $E$ be a proper space with a Borel measure $\mu$ that is locally finite, and let
$\Omega \subseteq E$ be open. A real function that is continuous on $\Omega$ is locally
$p$-integrable on $\Omega$ for every exponent $p$. -/
theorem _root_.ContinuousOn.locallyMemLpOn {f : E → ℝ} (hf : ContinuousOn f Ω) (p : ℝ≥0∞) :
    LocallyMemLpOn f p Ω μ := by
  intro x hx
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen x hx
  have hball : closedBall x (ε / 2) ⊆ Ω := (closedBall_subset_ball (half_lt_self hε)).trans hεΩ
  refine ⟨closedBall x (ε / 2), mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x (half_pos hε)),
    ?_⟩
  obtain ⟨C, hC⟩ := (isCompact_closedBall x (ε / 2)).exists_bound_of_continuousOn
    (hf.mono hball)
  have : IsFiniteMeasure (μ.restrict (closedBall x (ε / 2))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (isCompact_closedBall x (ε / 2)).measure_lt_top⟩
  exact MemLp.of_bound ((hf.mono hball).aestronglyMeasurable measurableSet_closedBall) C
    ((ae_restrict_mem measurableSet_closedBall).mono fun z hz ↦ hC z hz)

end LocalLp

omit [TopologicalSpace X] in
/-- Let $p < \infty$. If $f \in L^p(s)$ and $f \in L^p(t)$, then $f \in L^p(s \cup t)$.

The statement is also true for $p = \infty$. The proof excludes $p = \infty$ only because it
compares the $p$-th powers of the $L^p$ norms. -/
theorem MemLp.union_of_ne_top (hp : p ≠ ⊤) (hs : MemLp f p (μ.restrict s))
    (ht : MemLp f p (μ.restrict t)) : MemLp f p (μ.restrict (s ∪ t)) := by
  have hmeas : AEStronglyMeasurable f (μ.restrict (s ∪ t)) :=
    aestronglyMeasurable_union_iff.2 ⟨hs.aestronglyMeasurable, ht.aestronglyMeasurable⟩
  rcases eq_or_ne p 0 with rfl | hp0
  · exact memLp_zero_iff_aestronglyMeasurable.2 hmeas
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hrw : ∀ ν : Measure X, AEStronglyMeasurable f ν →
      eLpNorm f p ν ^ p.toReal = ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂ν := fun ν hν ↦ by
    rw [eLpNorm_eq_eLpNorm' hp0 hp hν, lintegral_rpow_enorm_eq_rpow_eLpNorm' hr]
  have key : eLpNorm f p (μ.restrict (s ∪ t)) ^ p.toReal
      ≤ eLpNorm f p (μ.restrict s) ^ p.toReal + eLpNorm f p (μ.restrict t) ^ p.toReal := by
    rw [hrw _ hmeas, hrw _ hs.aestronglyMeasurable, hrw _ ht.aestronglyMeasurable]
    exact lintegral_union_le _ _ _
  have hfin : eLpNorm f p (μ.restrict (s ∪ t)) ^ p.toReal ≠ ⊤ :=
    (key.trans_lt (ENNReal.add_lt_top.2
      ⟨ENNReal.rpow_lt_top_of_nonneg hr.le hs.eLpNorm_lt_top.ne,
        ENNReal.rpow_lt_top_of_nonneg hr.le ht.eLpNorm_lt_top.ne⟩)).ne
  rw [memLp_iff, lt_top_iff_ne_top]
  intro hcon
  rw [hcon, ENNReal.top_rpow_of_pos hr] at hfin
  exact hfin rfl

/-- If $f$ is locally $p$-integrable on $s$ and $t \subseteq s$, then $f$ is locally $p$-integrable
on $t$. -/
theorem LocallyMemLpOn.mono_set (hf : LocallyMemLpOn f p s μ) (hts : t ⊆ s) :
    LocallyMemLpOn f p t μ := fun x hx ↦
  let ⟨u, hu, h⟩ := hf x (hts hx); ⟨u, nhdsWithin_mono x hts hu, h⟩

/-- Let $p < \infty$ and let $s$ be compact. If $f$ is locally $p$-integrable on $s$, then
$f \in L^p(s)$.

This is the $L^p$ analogue of `MeasureTheory.LocallyIntegrableOn.integrableOn_compact_subset`,
and the proof is the same, by `IsCompact.induction_on`. -/
theorem LocallyMemLpOn.memLp_restrict_of_isCompact (hf : LocallyMemLpOn f p s μ) (hp : p ≠ ⊤)
    (hs : IsCompact s) : MemLp f p (μ.restrict s) :=
  IsCompact.induction_on hs (by simp)
    (fun _ _ hst ht ↦ ht.mono_measure (Measure.restrict_mono hst le_rfl))
    (fun _ _ h₁ h₂ ↦ MemLp.union_of_ne_top hp h₁ h₂) hf

/-- **A function in $L^p_{\mathrm{loc}}(s)$ is in $L^p$ of every compact subset of $s$.** Let
$p < \infty$, let $f$ be locally $p$-integrable on $s$, and let $t \subseteq s$ be compact. Then
$f \in L^p(t)$. -/
theorem LocallyMemLpOn.memLp_restrict_of_compact_subset (hf : LocallyMemLpOn f p s μ)
    (hp : p ≠ ⊤)
    (hts : t ⊆ s) (ht : IsCompact t) : MemLp f p (μ.restrict t) :=
  (hf.mono_set hts).memLp_restrict_of_isCompact hp ht

/-- Let $X$ be a Hausdorff space in which open sets are measurable. If $f$ is locally integrable on
$s$ and $g$ is a continuous real function with compact support and
$\operatorname{tsupport} g \subseteq s$, then $g f$ is integrable on $X$.

This is the version on a set of
`MeasureTheory.LocallyIntegrable.integrable_smul_left_of_hasCompactSupport` of Mathlib. -/
theorem LocallyIntegrableOn.integrable_smul_left_of_tsupport_subset [OpensMeasurableSpace X]
    [T2Space X] [NormedSpace ℝ G] (hf : LocallyIntegrableOn f s μ) {g : X → ℝ}
    (hg : Continuous g) (h'g : HasCompactSupport g) (hgs : tsupport g ⊆ s) :
    Integrable (fun x ↦ g x • f x) μ := by
  have hK : IsCompact (tsupport g) := h'g
  have h1 : (fun x ↦ g x • f x) = (tsupport g).indicator fun x ↦ g x • f x :=
    (indicator_eq_self.2 (Function.support_subset_iff'.2 fun x hx ↦ by
      simp [image_eq_zero_of_notMem_tsupport hx])).symm
  rw [h1, Set.indicator_smul]
  exact Integrable.smul_of_top_right
    ((integrable_indicator_iff hK.measurableSet).2 (hf.integrableOn_compact_subset hgs hK))
    (hg.memLp_top_of_hasCompactSupport h'g μ)

/-- If a real function $f$ is locally integrable on $s$ and $g$ is continuous, then $f g$ is locally
integrable on $s$. Near each point, the continuous factor is bounded. -/
theorem LocallyIntegrableOn.mul_continuous [OpensMeasurableSpace X] {f g : X → ℝ}
    (hf : LocallyIntegrableOn f s μ)
    (hg : Continuous g) : LocallyIntegrableOn (fun x ↦ f x * g x) s μ := by
  intro x hx
  obtain ⟨u, hu, hfu⟩ := hf x hx
  have hSopen : IsOpen {y | ‖g y‖ < ‖g x‖ + 1} := isOpen_lt hg.norm continuous_const
  have hxS : x ∈ {y | ‖g y‖ < ‖g x‖ + 1} := by simp
  refine ⟨u ∩ {y | ‖g y‖ < ‖g x‖ + 1},
    Filter.inter_mem hu (mem_nhdsWithin_of_mem_nhds (hSopen.mem_nhds hxS)), ?_⟩
  refine Integrable.mul_bdd (c := ‖g x‖ + 1) (hfu.mono_set inter_subset_left)
    hg.aestronglyMeasurable.restrict ?_
  exact ((ae_restrict_mem hSopen.measurableSet).mono fun y hy ↦ hy.le).filter_mono
    (ae_mono (Measure.restrict_mono inter_subset_right le_rfl))

/-- If $f$ is locally integrable on $s$ and $L$ is a continuous linear map, then $x \mapsto L(f(x))$
is locally integrable on $s$. -/
theorem LocallyIntegrableOn.comp_continuousLinearMap {G' : Type*} [NormedAddCommGroup G']
    [NormedSpace ℝ G] [NormedSpace ℝ G'] (hf : LocallyIntegrableOn f s μ) (L : G →L[ℝ] G') :
    LocallyIntegrableOn (fun x ↦ L (f x)) s μ := fun x hx ↦
  let ⟨u, hu, hfu⟩ := hf x hx
  ⟨u, hu, L.integrable_comp hfu⟩

end MeasureTheory

/-! ### Test functions -/

namespace TestFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E}

/-- A test function on $\Omega$ vanishes at every point outside $\Omega$. -/
theorem eq_zero_of_notMem (φ : 𝓓(Ω, F)) {x : E} (hx : x ∉ (Ω : Set E)) : φ x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h ↦ hx (φ.tsupport_subset h)

/-- For a test function $\varphi$ on $\Omega$ and a tuple $y \in E^n$, the function
$x \mapsto D^n \varphi(x)(y)$, the $n$-th derivative of $\varphi$ evaluated at $y$, is a test
function on $\Omega$. -/
noncomputable def iteratedFDerivApply (φ : 𝓓(Ω, F)) (n : ℕ) (y : Fin n → E) : 𝓓(Ω, F) where
  toFun x := iteratedFDeriv ℝ n φ x y
  contDiff' := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n ↦ E) F y).contDiff.comp
    (φ.contDiff.iteratedFDeriv_right (m := ∞) (i := n) (by simp))
  hasCompactSupport' := (φ.hasCompactSupport.iteratedFDeriv n).of_isClosed_subset
    isClosed_closure (tsupport_comp_subset (g := fun L : E [×n]→L[ℝ] F ↦ L y) rfl _)
  tsupport_subset' := (tsupport_comp_subset (g := fun L : E [×n]→L[ℝ] F ↦ L y) rfl _).trans
    ((tsupport_iteratedFDeriv_subset n).trans φ.tsupport_subset)

/-- The function of `TestFunction.iteratedFDerivApply φ n y` is $x \mapsto D^n \varphi(x)(y)$. -/
@[simp]
theorem iteratedFDerivApply_coe (φ : 𝓓(Ω, F)) (n : ℕ) (y : Fin n → E) :
    (φ.iteratedFDerivApply n y : E → F) = fun x ↦ iteratedFDeriv ℝ n φ x y :=
  rfl

/-- The value of `TestFunction.iteratedFDerivApply φ n y` at $x$ is $D^n \varphi(x)(y)$. -/
theorem iteratedFDerivApply_apply (φ : 𝓓(Ω, F)) (n : ℕ) (y : Fin n → E) (x : E) :
    φ.iteratedFDerivApply n y x = iteratedFDeriv ℝ n φ x y :=
  rfl

/-- For a test function $\varphi$ on $\Omega$ and a direction $v$, the directional derivative
$x \mapsto D\varphi(x) v$ is a test function on $\Omega$. -/
noncomputable def fderivApply (φ : 𝓓(Ω, F)) (v : E) : 𝓓(Ω, F) where
  toFun x := fderiv ℝ φ x v
  contDiff' := (φ.contDiff.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  hasCompactSupport' := φ.hasCompactSupport.fderiv_apply ℝ v
  tsupport_subset' := (tsupport_fderiv_apply_subset ℝ v).trans φ.tsupport_subset

/-- The function of `TestFunction.fderivApply φ v` is $x \mapsto D\varphi(x) v$. -/
@[simp]
theorem fderivApply_coe (φ : 𝓓(Ω, F)) (v : E) :
    (φ.fderivApply v : E → F) = fun x ↦ fderiv ℝ φ x v :=
  rfl

/-- The value of `TestFunction.fderivApply φ v` at $x$ is $D\varphi(x) v$. -/
theorem fderivApply_apply (φ : 𝓓(Ω, F)) (v x : E) : φ.fderivApply v x = fderiv ℝ φ x v :=
  rfl

/-- The product $\varphi g$ of a real test function $\varphi$ on $\Omega$ with a smooth real
function $g$ is a test function on $\Omega$. It is smooth, and its support lies in the support
of $\varphi$. -/
noncomputable def mulContDiff (φ : 𝓓(Ω, ℝ)) {g : E → ℝ} (hg : ContDiff ℝ ∞ g) : 𝓓(Ω, ℝ) where
  toFun x := φ x * g x
  contDiff' := φ.contDiff.mul hg
  hasCompactSupport' := φ.hasCompactSupport.mul_right
  tsupport_subset' := tsupport_mul_subset_left.trans φ.tsupport_subset

/-- The function of `TestFunction.mulContDiff φ hg` is $x \mapsto \varphi(x) g(x)$. -/
@[simp]
theorem mulContDiff_coe (φ : 𝓓(Ω, ℝ)) {g : E → ℝ} (hg : ContDiff ℝ ∞ g) :
    (φ.mulContDiff hg : E → ℝ) = fun x ↦ φ x * g x :=
  rfl

/-- Let $\varphi$ be a real test function on $\Omega$, and let $c$ be a real function of class $C^1$
on $\Omega$. Then $x \mapsto \varphi(x) c(x)$ is of class $C^1$ on all of $E$.

The product is $C^1$ on $\Omega$, and it vanishes on the open complement of the support of
$\varphi$. -/
theorem contDiff_mul_of_contDiffOn (φ : 𝓓(Ω, ℝ)) {c : E → ℝ}
    (hc : ContDiffOn ℝ 1 c Ω) : ContDiff ℝ 1 fun x ↦ φ x * c x :=
  (φ.contDiff.of_le (by simp)).mul_contDiffOn_of_tsupport_subset Ω.isOpen hc φ.tsupport_subset

end TestFunction

/-- Let $\mu$ be a locally finite Borel measure, let $g$ be a real function continuous on $\Omega$,
and let $\varphi$ be a real test function on $\Omega$. Then $g \varphi$ is integrable on
$\Omega$. -/
theorem integrable_mul_testFunction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E] {Ω : Opens E} {μ : Measure E}
    [IsLocallyFiniteMeasure μ] {g : E → ℝ} (hg : ContinuousOn g Ω) (φ : 𝓓(Ω, ℝ)) :
    Integrable (fun x ↦ g x * φ x) (μ.restrict (Ω : Set E)) := by
  have := (hg.locallyIntegrableOn (μ := μ) Ω.isOpen.measurableSet)
    |>.integrable_smul_left_of_tsupport_subset φ.contDiff.continuous φ.hasCompactSupport
      φ.tsupport_subset
  simp only [smul_eq_mul] at this
  exact this.integrableOn.congr_fun (fun x _ ↦ mul_comm _ _) Ω.isOpen.measurableSet

/-! ### The weak derivative -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {μ : Measure E} {n : ℕ} {f : E → F} {w : E → E [×n]→L[ℝ] F}

/-- **The weak derivative of order $n$.** A function $w$ with values in the continuous $n$-linear
maps $E^n \to F$ is an $n$-th **weak derivative** of $f : E \to F$ on the open set $\Omega$ if
$f$ and $w$ are locally integrable on $\Omega$ and
$$\int_\Omega D^n \varphi(x)(y) \, f(x) \, d\mu(x) = (-1)^n \int_\Omega \varphi(x) \, w(x)(y) \,
  d\mu(x)$$
for every real test function $\varphi$ on $\Omega$ and every tuple $y \in E^n$.

A tuple of directions plays the role of a multi-index of length $n$, so this is Definition 7.1.3
of [han2009theoretical] for all multi-indices of length $n$ at once. -/
structure HasWeakIteratedFDerivOn (n : ℕ) (f : E → F) (w : E → E [×n]→L[ℝ] F) (Ω : Opens E)
    (μ : Measure E) : Prop where
  /-- The function $f$ is locally integrable on $\Omega$. -/
  locallyIntegrableOn : LocallyIntegrableOn f Ω μ
  /-- The weak derivative $w$ is locally integrable on $\Omega$. -/
  locallyIntegrableOn_weakDeriv : LocallyIntegrableOn w Ω μ
  /-- The integration by parts formula: for every test function $\varphi$ and every tuple
  $y \in E^n$, $\int_\Omega D^n \varphi(x)(y) f(x) \, d\mu = (-1)^n \int_\Omega \varphi(x)
  w(x)(y) \, d\mu$. -/
  integral_smul_eq (φ : 𝓓(Ω, ℝ)) (y : Fin n → E) :
    ∫ x in (Ω : Set E), iteratedFDeriv ℝ n φ x y • f x ∂μ
      = (-1 : ℝ) ^ n • ∫ x in (Ω : Set E), φ x • w x y ∂μ

/-- **The first-order weak derivative.** A function $w : E \to (E \to_L F)$ is a first-order weak
derivative of $f$ on the open set $\Omega$ if it is a weak derivative of order $1$, with $w(x)$
read as a $1$-linear map. -/
def HasWeakFDerivOn (f : E → F) (w : E → E →L[ℝ] F) (Ω : Opens E) (μ : Measure E) : Prop :=
  HasWeakIteratedFDerivOn 1 f (fun x ↦ (continuousMultilinearCurryFin1 ℝ E F).symm (w x)) Ω μ

namespace HasWeakIteratedFDerivOn

section Integrals

variable [OpensMeasurableSpace E]

/-- Let $w$ be an $n$-th weak derivative of $f$ on $\Omega$. For every test function $\varphi$ on
$\Omega$, the product $\varphi f$ is integrable on $E$. -/
theorem integrable_smul (h : HasWeakIteratedFDerivOn n f w Ω μ) (φ : 𝓓(Ω, ℝ)) :
    Integrable (fun x ↦ φ x • f x) μ :=
  LocallyIntegrableOn.integrable_smul_left_of_tsupport_subset h.locallyIntegrableOn
    φ.contDiff.continuous φ.hasCompactSupport φ.tsupport_subset

/-- Let $w$ be an $n$-th weak derivative of $f$ on $\Omega$. For every test function $\varphi$ on
$\Omega$, the product $\varphi w$ is integrable on $E$. -/
theorem integrable_smul_weakDeriv (h : HasWeakIteratedFDerivOn n f w Ω μ) (φ : 𝓓(Ω, ℝ)) :
    Integrable (fun x ↦ φ x • w x) μ :=
  LocallyIntegrableOn.integrable_smul_left_of_tsupport_subset h.locallyIntegrableOn_weakDeriv
    φ.contDiff.continuous φ.hasCompactSupport φ.tsupport_subset

/-- Let $w$ be an $n$-th weak derivative of $f$ on $\Omega$. For every test function $\varphi$ on
$\Omega$ and every tuple $y \in E^n$, the function $x \mapsto \varphi(x) w(x)(y)$ is integrable
on $E$. -/
theorem integrable_smul_weakDeriv_apply (h : HasWeakIteratedFDerivOn n f w Ω μ) (φ : 𝓓(Ω, ℝ))
    (y : Fin n → E) : Integrable (fun x ↦ φ x • w x y) μ :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n ↦ E) F y).integrable_comp
    (h.integrable_smul_weakDeriv φ)

omit [OpensMeasurableSpace E] in
omit [OpensMeasurableSpace E] in
/-- The integration by parts formula of an $n$-th weak derivative, with the integrals over all of
$E$: $\int_E D^n \varphi(x)(y) f(x) \, d\mu = (-1)^n \int_E \varphi(x) w(x)(y) \, d\mu$. This
holds because the test function vanishes outside $\Omega$. -/
theorem integral_smul_eq' (h : HasWeakIteratedFDerivOn n f w Ω μ) (φ : 𝓓(Ω, ℝ))
    (y : Fin n → E) :
    ∫ x, iteratedFDeriv ℝ n φ x y • f x ∂μ = (-1 : ℝ) ^ n • ∫ x, φ x • w x y ∂μ := by
  have e1 : ∫ x in (Ω : Set E), iteratedFDeriv ℝ n φ x y • f x ∂μ
      = ∫ x, iteratedFDeriv ℝ n φ x y • f x ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [show iteratedFDeriv ℝ n (φ : E → ℝ) x y = 0 from
        (φ.iteratedFDerivApply n y).eq_zero_of_notMem hx, zero_smul]
  have e2 : ∫ x in (Ω : Set E), φ x • w x y ∂μ = ∫ x, φ x • w x y ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [φ.eq_zero_of_notMem hx, zero_smul]
  rw [← e1, ← e2]
  exact h.integral_smul_eq φ y

omit [OpensMeasurableSpace E] in
/-- If $w$ is an $n$-th weak derivative of $f$ on $\Omega$, and $f'$ and $w'$ agree with $f$ and $w$
almost everywhere on $\Omega$, then $w'$ is an $n$-th weak derivative of $f'$ on $\Omega$. -/
theorem congr_ae {f' : E → F} {w' : E → E [×n]→L[ℝ] F} (h : HasWeakIteratedFDerivOn n f w Ω μ)
    (hf : f =ᵐ[μ.restrict (Ω : Set E)] f') (hw : w =ᵐ[μ.restrict (Ω : Set E)] w') :
    HasWeakIteratedFDerivOn n f' w' Ω μ where
  locallyIntegrableOn := h.locallyIntegrableOn.congr hf
  locallyIntegrableOn_weakDeriv := h.locallyIntegrableOn_weakDeriv.congr hw
  integral_smul_eq φ y := by
    have e1 : ∫ x in (Ω : Set E), iteratedFDeriv ℝ n φ x y • f' x ∂μ
        = ∫ x in (Ω : Set E), iteratedFDeriv ℝ n φ x y • f x ∂μ :=
      integral_congr_ae (by filter_upwards [hf] with x hx; rw [hx])
    have e2 : ∫ x in (Ω : Set E), φ x • w' x y ∂μ = ∫ x in (Ω : Set E), φ x • w x y ∂μ :=
      integral_congr_ae (by filter_upwards [hw] with x hx; rw [hx])
    rw [e1, e2]
    exact h.integral_smul_eq φ y

omit [OpensMeasurableSpace E] in
/-- If $w$ is an $n$-th weak derivative of $f$ on $\Omega$ and $\Omega' \subseteq \Omega$ is open,
then $w$ is an $n$-th weak derivative of $f$ on $\Omega'$. -/
theorem mono {Ω' : Opens E} (h : HasWeakIteratedFDerivOn n f w Ω μ) (hΩ : Ω' ≤ Ω) :
    HasWeakIteratedFDerivOn n f w Ω' μ where
  locallyIntegrableOn := h.locallyIntegrableOn.mono_set hΩ
  locallyIntegrableOn_weakDeriv := h.locallyIntegrableOn_weakDeriv.mono_set hΩ
  integral_smul_eq φ y := by
    have e1 : ∫ x in (Ω' : Set E), iteratedFDeriv ℝ n φ x y • f x ∂μ
        = ∫ x, iteratedFDeriv ℝ n φ x y • f x ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
        rw [show iteratedFDeriv ℝ n (φ : E → ℝ) x y = 0 from
          (φ.iteratedFDerivApply n y).eq_zero_of_notMem hx, zero_smul]
    have e2 : ∫ x in (Ω' : Set E), φ x • w x y ∂μ = ∫ x, φ x • w x y ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
        rw [φ.eq_zero_of_notMem hx, zero_smul]
    rw [e1, e2]
    exact h.integral_smul_eq' ⟨φ, φ.contDiff, φ.hasCompactSupport,
      φ.tsupport_subset.trans hΩ⟩ y

end Integrals

variable [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F]

/-- **Uniqueness of the weak derivative**, Lemma 7.1.4 of [han2009theoretical]. Let $E$ be
finite-dimensional with its Borel $\sigma$-algebra and let $F$ be complete. If $w_1$ and $w_2$
are $n$-th weak derivatives of $f$ on $\Omega$, then $w_1(x) = w_2(x)$ for almost every
$x \in \Omega$.

The proof applies the generalized variational lemma
`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` of Mathlib, which is Lemma 7.1.2 of
[han2009theoretical], to $w_1 - w_2$. -/
theorem ae_eq {w₁ w₂ : E → E [×n]→L[ℝ] F} (h₁ : HasWeakIteratedFDerivOn n f w₁ Ω μ)
    (h₂ : HasWeakIteratedFDerivOn n f w₂ Ω μ) : ∀ᵐ x ∂μ, x ∈ (Ω : Set E) → w₁ x = w₂ x := by
  have key : ∀ᵐ x ∂μ, x ∈ (Ω : Set E) → w₁ x - w₂ x = 0 := by
    refine Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (LocallyIntegrableOn.sub h₁.locallyIntegrableOn_weakDeriv
        h₂.locallyIntegrableOn_weakDeriv) fun g hg h'g hgs ↦ ?_
    set φ : 𝓓(Ω, ℝ) := ⟨g, hg, h'g, hgs⟩ with hφ
    have e1 : Integrable (fun x ↦ g x • w₁ x) μ := h₁.integrable_smul_weakDeriv φ
    have e2 : Integrable (fun x ↦ g x • w₂ x) μ := h₂.integrable_smul_weakDeriv φ
    have key : ∫ x, g x • w₁ x ∂μ = ∫ x, g x • w₂ x ∂μ := by
      refine ContinuousMultilinearMap.ext fun y ↦ ?_
      rw [ContinuousMultilinearMap.integral_apply e1, ContinuousMultilinearMap.integral_apply e2]
      refine smul_right_injective F (pow_ne_zero n (by norm_num : (-1 : ℝ) ≠ 0)) ?_
      exact (h₁.integral_smul_eq' φ y).symm.trans (h₂.integral_smul_eq' φ y)
    have hsub : (fun x ↦ g x • (w₁ x - w₂ x)) = fun x ↦ g x • w₁ x - g x • w₂ x :=
      funext fun x ↦ smul_sub _ _ _
    rw [hsub, integral_sub e1 e2, key, sub_self]
  filter_upwards [key] with x hx hxΩ using sub_eq_zero.mp (hx hxΩ)

end HasWeakIteratedFDerivOn

/-! ### Linearity -/

namespace HasWeakIteratedFDerivOn

variable [OpensMeasurableSpace E]

omit [OpensMeasurableSpace E] in
/-- The zero function has the weak derivative $0$ of every order. -/
protected theorem zero : HasWeakIteratedFDerivOn n (0 : E → F) 0 Ω μ where
  locallyIntegrableOn := locallyIntegrable_zero.locallyIntegrableOn _
  locallyIntegrableOn_weakDeriv := locallyIntegrable_zero.locallyIntegrableOn _
  integral_smul_eq φ y := by simp

/-- **Additivity of weak differentiation**, half of Proposition 7.1.10 of [han2009theoretical]. If
$w_1$ and $w_2$ are $n$-th weak derivatives of $f_1$ and $f_2$ on $\Omega$, then $w_1 + w_2$ is
an $n$-th weak derivative of $f_1 + f_2$. -/
protected theorem add {f₁ f₂ : E → F} {w₁ w₂ : E → E [×n]→L[ℝ] F}
    (h₁ : HasWeakIteratedFDerivOn n f₁ w₁ Ω μ) (h₂ : HasWeakIteratedFDerivOn n f₂ w₂ Ω μ) :
    HasWeakIteratedFDerivOn n (f₁ + f₂) (w₁ + w₂) Ω μ where
  locallyIntegrableOn := LocallyIntegrableOn.add h₁.locallyIntegrableOn h₂.locallyIntegrableOn
  locallyIntegrableOn_weakDeriv :=
    LocallyIntegrableOn.add h₁.locallyIntegrableOn_weakDeriv h₂.locallyIntegrableOn_weakDeriv
  integral_smul_eq φ y := by
    have i₁ := (h₁.integrable_smul (φ.iteratedFDerivApply n y)).integrableOn (s := (Ω : Set E))
    have i₂ := (h₂.integrable_smul (φ.iteratedFDerivApply n y)).integrableOn (s := (Ω : Set E))
    simp only [TestFunction.iteratedFDerivApply_apply] at i₁ i₂
    have j₁ := (h₁.integrable_smul_weakDeriv_apply φ y).integrableOn (s := (Ω : Set E))
    have j₂ := (h₂.integrable_smul_weakDeriv_apply φ y).integrableOn (s := (Ω : Set E))
    simp only [Pi.add_apply, add_apply, smul_add]
    rw [integral_add i₁ i₂, integral_add j₁ j₂, h₁.integral_smul_eq, h₂.integral_smul_eq, smul_add]

omit [OpensMeasurableSpace E] in
/-- **Homogeneity of weak differentiation**, half of Proposition 7.1.10 of [han2009theoretical]. If
$w$ is an $n$-th weak derivative of $f$ on $\Omega$ and $c \in \mathbb{R}$, then $c w$ is an
$n$-th weak derivative of $c f$. -/
protected theorem const_smul (h : HasWeakIteratedFDerivOn n f w Ω μ) (c : ℝ) :
    HasWeakIteratedFDerivOn n (c • f) (c • w) Ω μ where
  locallyIntegrableOn := h.locallyIntegrableOn.smul c
  locallyIntegrableOn_weakDeriv := h.locallyIntegrableOn_weakDeriv.smul c
  integral_smul_eq φ y := by
    simp only [Pi.smul_apply, smul_apply, smul_comm _ c, integral_smul, h.integral_smul_eq]

omit [OpensMeasurableSpace E] in
/-- If $w$ is an $n$-th weak derivative of $f$ on $\Omega$, then $-w$ is an $n$-th weak derivative
of $-f$. -/
protected theorem neg (h : HasWeakIteratedFDerivOn n f w Ω μ) :
    HasWeakIteratedFDerivOn n (-f) (-w) Ω μ where
  locallyIntegrableOn := h.locallyIntegrableOn.neg
  locallyIntegrableOn_weakDeriv := h.locallyIntegrableOn_weakDeriv.neg
  integral_smul_eq φ y := by
    simp only [Pi.neg_apply, neg_apply, smul_neg, integral_neg, h.integral_smul_eq, smul_neg]

/-- If $w_1$ and $w_2$ are $n$-th weak derivatives of $f_1$ and $f_2$ on $\Omega$, then $w_1 - w_2$
is an $n$-th weak derivative of $f_1 - f_2$. -/
protected theorem sub {f₁ f₂ : E → F} {w₁ w₂ : E → E [×n]→L[ℝ] F}
    (h₁ : HasWeakIteratedFDerivOn n f₁ w₁ Ω μ) (h₂ : HasWeakIteratedFDerivOn n f₂ w₂ Ω μ) :
    HasWeakIteratedFDerivOn n (f₁ - f₂) (w₁ - w₂) Ω μ := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg

/-- **Linearity of weak differentiation**, Proposition 7.1.10 of [han2009theoretical]. If $w_1$ and
$w_2$ are $n$-th weak derivatives of $f_1$ and $f_2$ on $\Omega$, and $c_1, c_2 \in \mathbb{R}$,
then $c_1 w_1 + c_2 w_2$ is an $n$-th weak derivative of $c_1 f_1 + c_2 f_2$. -/
theorem const_smul_add_const_smul {f₁ f₂ : E → F} {w₁ w₂ : E → E [×n]→L[ℝ] F}
    (h₁ : HasWeakIteratedFDerivOn n f₁ w₁ Ω μ) (h₂ : HasWeakIteratedFDerivOn n f₂ w₂ Ω μ)
    (c₁ c₂ : ℝ) :
    HasWeakIteratedFDerivOn n (c₁ • f₁ + c₂ • f₂) (c₁ • w₁ + c₂ • w₂) Ω μ :=
  (h₁.const_smul c₁).add (h₂.const_smul c₂)

end HasWeakIteratedFDerivOn

/-! ### Weak derivatives along a fixed tuple of directions -/

section Line

variable {y : Fin n → E} {w : E → F}

/-- **The weak derivative along a tuple of directions.** Let $y \in E^n$. A function $w : E \to F$
is a **weak derivative of $f$ along $y$** on the open set $\Omega$ if $f$ and $w$ are locally
integrable on $\Omega$ and
$$\int_\Omega D^n \varphi(x)(y) \, f(x) \, d\mu(x) = (-1)^n \int_\Omega \varphi(x) \, w(x) \,
  d\mu(x)$$
for every real test function $\varphi$ on $\Omega$.

`HasWeakIteratedFDerivOn` takes all tuples of length $n$ at once and has values in the
continuous $n$-linear maps. This predicate takes one tuple and has values in $F$: it is
Definition 7.1.3 of [han2009theoretical] for the single multi-index that the tuple names. -/
structure HasWeakIteratedLineDerivOn {n : ℕ} (y : Fin n → E) (f : E → F) (w : E → F)
    (Ω : Opens E) (μ : Measure E) : Prop where
  /-- The function $f$ is locally integrable on $\Omega$. -/
  locallyIntegrableOn : LocallyIntegrableOn f Ω μ
  /-- The weak derivative $w$ is locally integrable on $\Omega$. -/
  locallyIntegrableOn_weakDeriv : LocallyIntegrableOn w Ω μ
  /-- The integration by parts formula: for every test function $\varphi$, $\int_\Omega D^n
  \varphi(x)(y) f(x) \, d\mu = (-1)^n \int_\Omega \varphi(x) w(x) \, d\mu$. -/
  integral_smul_eq (φ : 𝓓(Ω, ℝ)) :
    ∫ x in (Ω : Set E), iteratedFDeriv ℝ n φ x y • f x ∂μ
      = (-1 : ℝ) ^ n • ∫ x in (Ω : Set E), φ x • w x ∂μ

/-- If $w$ is an $n$-th weak derivative of $f$ on $\Omega$ and $y \in E^n$, then $x \mapsto w(x)(y)$
is a weak derivative of $f$ along $y$ on $\Omega$. -/
theorem HasWeakIteratedFDerivOn.lineDeriv {w : E → E [×n]→L[ℝ] F}
    (h : HasWeakIteratedFDerivOn n f w Ω μ) (y : Fin n → E) :
    HasWeakIteratedLineDerivOn y f (fun x ↦ w x y) Ω μ where
  locallyIntegrableOn := h.locallyIntegrableOn
  locallyIntegrableOn_weakDeriv := h.locallyIntegrableOn_weakDeriv.comp_continuousLinearMap
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n ↦ E) F y)
  integral_smul_eq φ := h.integral_smul_eq φ y

namespace HasWeakIteratedLineDerivOn

variable [OpensMeasurableSpace E]

omit [OpensMeasurableSpace E] in
/-- Let $y$ be a tuple of length $n = 0$. If $f$ is locally integrable on $\Omega$, then $f$ is a
weak derivative of itself along $y$ on $\Omega$.

The hypothesis is $n = 0$ and not a fixed empty tuple, so that the lemma applies to a tuple
whose length is only propositionally zero. -/
theorem of_length_eq_zero (hn : n = 0) (y : Fin n → E) (hf : LocallyIntegrableOn f Ω μ) :
    HasWeakIteratedLineDerivOn y f f Ω μ := by
  subst hn
  exact ⟨hf, hf, fun φ ↦ by simp⟩

omit [OpensMeasurableSpace E] in
/-- The integration by parts formula of a weak derivative along $y$, with the integrals over all of
$E$: $\int_E D^n \varphi(x)(y) f(x) \, d\mu = (-1)^n \int_E \varphi(x) w(x) \, d\mu$. This holds
because the test function vanishes outside $\Omega$. -/
theorem integral_smul_eq' (h : HasWeakIteratedLineDerivOn y f w Ω μ) (φ : 𝓓(Ω, ℝ)) :
    ∫ x, iteratedFDeriv ℝ n φ x y • f x ∂μ = (-1 : ℝ) ^ n • ∫ x, φ x • w x ∂μ := by
  have e1 : ∫ x in (Ω : Set E), iteratedFDeriv ℝ n φ x y • f x ∂μ
      = ∫ x, iteratedFDeriv ℝ n φ x y • f x ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [show iteratedFDeriv ℝ n (φ : E → ℝ) x y = 0 from
        (φ.iteratedFDerivApply n y).eq_zero_of_notMem hx, zero_smul]
  have e2 : ∫ x in (Ω : Set E), φ x • w x ∂μ = ∫ x, φ x • w x ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [φ.eq_zero_of_notMem hx, zero_smul]
  rw [← e1, ← e2]
  exact h.integral_smul_eq φ

omit [OpensMeasurableSpace E] in
/-- If $w$ is a weak derivative of $f$ along $y$ on $\Omega$, and $f'$ and $w'$ agree with $f$ and
$w$ almost everywhere on $\Omega$, then $w'$ is a weak derivative of $f'$ along $y$ on $\Omega$. -/
theorem congr_ae {f' w' : E → F} (h : HasWeakIteratedLineDerivOn y f w Ω μ)
    (hf : f =ᵐ[μ.restrict (Ω : Set E)] f') (hw : w =ᵐ[μ.restrict (Ω : Set E)] w') :
    HasWeakIteratedLineDerivOn y f' w' Ω μ where
  locallyIntegrableOn := h.locallyIntegrableOn.congr hf
  locallyIntegrableOn_weakDeriv := h.locallyIntegrableOn_weakDeriv.congr hw
  integral_smul_eq φ := by
    have e1 : ∫ x in (Ω : Set E), iteratedFDeriv ℝ n φ x y • f' x ∂μ
        = ∫ x in (Ω : Set E), iteratedFDeriv ℝ n φ x y • f x ∂μ :=
      integral_congr_ae (by filter_upwards [hf] with x hx; rw [hx])
    have e2 : ∫ x in (Ω : Set E), φ x • w' x ∂μ = ∫ x in (Ω : Set E), φ x • w x ∂μ :=
      integral_congr_ae (by filter_upwards [hw] with x hx; rw [hx])
    rw [e1, e2]
    exact h.integral_smul_eq φ

omit [OpensMeasurableSpace E] in
/-- If $w$ is a weak derivative of $f$ along $y$ on $\Omega$ and $\Omega' \subseteq \Omega$ is open,
then $w$ is a weak derivative of $f$ along $y$ on $\Omega'$. -/
theorem mono {Ω' : Opens E} (h : HasWeakIteratedLineDerivOn y f w Ω μ) (hΩ : Ω' ≤ Ω) :
    HasWeakIteratedLineDerivOn y f w Ω' μ where
  locallyIntegrableOn := h.locallyIntegrableOn.mono_set hΩ
  locallyIntegrableOn_weakDeriv := h.locallyIntegrableOn_weakDeriv.mono_set hΩ
  integral_smul_eq φ := by
    have e1 : ∫ x in (Ω' : Set E), iteratedFDeriv ℝ n φ x y • f x ∂μ
        = ∫ x, iteratedFDeriv ℝ n φ x y • f x ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
        rw [show iteratedFDeriv ℝ n (φ : E → ℝ) x y = 0 from
          (φ.iteratedFDerivApply n y).eq_zero_of_notMem hx, zero_smul]
    have e2 : ∫ x in (Ω' : Set E), φ x • w x ∂μ = ∫ x, φ x • w x ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
        rw [φ.eq_zero_of_notMem hx, zero_smul]
    rw [e1, e2]
    exact h.integral_smul_eq' ⟨φ, φ.contDiff, φ.hasCompactSupport,
      φ.tsupport_subset.trans hΩ⟩

omit [OpensMeasurableSpace E] in
/-- The zero function has the weak derivative $0$ along every tuple of directions. -/
protected theorem zero : HasWeakIteratedLineDerivOn y (0 : E → F) 0 Ω μ where
  locallyIntegrableOn := locallyIntegrable_zero.locallyIntegrableOn _
  locallyIntegrableOn_weakDeriv := locallyIntegrable_zero.locallyIntegrableOn _
  integral_smul_eq φ := by simp

/-- If $w$ is a weak derivative of $f$ along $y$ on $\Omega$, then $\varphi f$ is integrable on $E$
for every test function $\varphi$ on $\Omega$. -/
theorem integrable_smul (h : HasWeakIteratedLineDerivOn y f w Ω μ) (φ : 𝓓(Ω, ℝ)) :
    Integrable (fun x ↦ φ x • f x) μ :=
  LocallyIntegrableOn.integrable_smul_left_of_tsupport_subset h.locallyIntegrableOn
    φ.contDiff.continuous φ.hasCompactSupport φ.tsupport_subset

/-- If $w$ is a weak derivative of $f$ along $y$ on $\Omega$, then $\varphi w$ is integrable on $E$
for every test function $\varphi$ on $\Omega$. -/
theorem integrable_smul_weakDeriv (h : HasWeakIteratedLineDerivOn y f w Ω μ) (φ : 𝓓(Ω, ℝ)) :
    Integrable (fun x ↦ φ x • w x) μ :=
  LocallyIntegrableOn.integrable_smul_left_of_tsupport_subset h.locallyIntegrableOn_weakDeriv
    φ.contDiff.continuous φ.hasCompactSupport φ.tsupport_subset

/-- If $w_1$ and $w_2$ are weak derivatives of $f_1$ and $f_2$ along $y$ on $\Omega$, then
$w_1 + w_2$ is a weak derivative of $f_1 + f_2$ along $y$. -/
protected theorem add {f₁ f₂ w₁ w₂ : E → F} (h₁ : HasWeakIteratedLineDerivOn y f₁ w₁ Ω μ)
    (h₂ : HasWeakIteratedLineDerivOn y f₂ w₂ Ω μ) :
    HasWeakIteratedLineDerivOn y (f₁ + f₂) (w₁ + w₂) Ω μ where
  locallyIntegrableOn := LocallyIntegrableOn.add h₁.locallyIntegrableOn h₂.locallyIntegrableOn
  locallyIntegrableOn_weakDeriv :=
    LocallyIntegrableOn.add h₁.locallyIntegrableOn_weakDeriv h₂.locallyIntegrableOn_weakDeriv
  integral_smul_eq φ := by
    have i₁ := (h₁.integrable_smul (φ.iteratedFDerivApply n y)).integrableOn (s := (Ω : Set E))
    have i₂ := (h₂.integrable_smul (φ.iteratedFDerivApply n y)).integrableOn (s := (Ω : Set E))
    simp only [TestFunction.iteratedFDerivApply_apply] at i₁ i₂
    have j₁ := (h₁.integrable_smul_weakDeriv φ).integrableOn (s := (Ω : Set E))
    have j₂ := (h₂.integrable_smul_weakDeriv φ).integrableOn (s := (Ω : Set E))
    simp only [Pi.add_apply, smul_add]
    rw [integral_add i₁ i₂, integral_add j₁ j₂, h₁.integral_smul_eq, h₂.integral_smul_eq, smul_add]

/-- Let $s$ be a finite index set. If $w_i$ is a weak derivative of $f_i$ along $y$ on $\Omega$ for
every $i \in s$, then $\sum_{i \in s} w_i$ is a weak derivative of $\sum_{i \in s} f_i$ along
$y$. -/
protected theorem finset_sum {ι : Type*} {s : Finset ι}
    {f w : ι → E → F} (h : ∀ i ∈ s, HasWeakIteratedLineDerivOn y (f i) (w i) Ω μ) :
    HasWeakIteratedLineDerivOn y (fun x ↦ ∑ i ∈ s, f i x) (fun x ↦ ∑ i ∈ s, w i x) Ω μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact HasWeakIteratedLineDerivOn.zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

omit [OpensMeasurableSpace E] in
/-- If $w$ is a weak derivative of $f$ along $y$ on $\Omega$ and $c \in \mathbb{R}$, then $c w$ is a
weak derivative of $c f$ along $y$. -/
protected theorem const_smul (h : HasWeakIteratedLineDerivOn y f w Ω μ) (c : ℝ) :
    HasWeakIteratedLineDerivOn y (c • f) (c • w) Ω μ where
  locallyIntegrableOn := h.locallyIntegrableOn.smul c
  locallyIntegrableOn_weakDeriv := h.locallyIntegrableOn_weakDeriv.smul c
  integral_smul_eq φ := by
    simp only [Pi.smul_apply, smul_comm _ c, integral_smul, h.integral_smul_eq]

omit [OpensMeasurableSpace E] in
/-- If $w$ is a weak derivative of $f$ along $y$ on $\Omega$, then $-w$ is a weak derivative of $-f$
along $y$. -/
protected theorem neg (h : HasWeakIteratedLineDerivOn y f w Ω μ) :
    HasWeakIteratedLineDerivOn y (-f) (-w) Ω μ where
  locallyIntegrableOn := h.locallyIntegrableOn.neg
  locallyIntegrableOn_weakDeriv := h.locallyIntegrableOn_weakDeriv.neg
  integral_smul_eq φ := by
    simp only [Pi.neg_apply, smul_neg, integral_neg, h.integral_smul_eq, smul_neg]

/-- If $w_1$ and $w_2$ are weak derivatives of $f_1$ and $f_2$ along $y$ on $\Omega$, then
$w_1 - w_2$ is a weak derivative of $f_1 - f_2$ along $y$. -/
protected theorem sub {f₁ f₂ w₁ w₂ : E → F} (h₁ : HasWeakIteratedLineDerivOn y f₁ w₁ Ω μ)
    (h₂ : HasWeakIteratedLineDerivOn y f₂ w₂ Ω μ) :
    HasWeakIteratedLineDerivOn y (f₁ - f₂) (w₁ - w₂) Ω μ := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
/-- For a real test function $\varphi$ on $\Omega$, a direction $z$ and a tuple $y \in E^n$, the
derivative of order $n + 1$ along the tuple $(z, y_1, \dots, y_n)$ is the derivative of order
$n$ of $\partial_z \varphi$ along $y$:
$$D^{n+1} \varphi(x)(z, y_1, \dots, y_n) = D^n (\partial_z \varphi)(x)(y_1, \dots, y_n).$$

The proof is `ContDiff.iteratedFDeriv_cons`. The function $\partial_z \varphi$ is the test
function `TestFunction.fderivApply φ z`. -/
theorem _root_.TestFunction.iteratedFDeriv_cons (φ : 𝓓(Ω, ℝ)) (z : E) (y : Fin n → E) (x : E) :
    iteratedFDeriv ℝ (n + 1) (φ : E → ℝ) x (Fin.cons z y)
      = iteratedFDeriv ℝ n (φ.fderivApply z : E → ℝ) x y :=
  φ.contDiff.iteratedFDeriv_cons z y x

omit [OpensMeasurableSpace E] in
/-- **The composition rule for weak derivatives along tuples.** Let $y \in E^n$ and $z \in E$. If
$w$ is a weak derivative of $f$ along $y$ on $\Omega$, and $u$ is a weak derivative of $w$ along
the one-element tuple $(z)$, then $u$ is a weak derivative of $f$ along the tuple
$(z, y_1, \dots, y_n)$ of length $n + 1$.

With its converse `HasWeakIteratedLineDerivOn.of_cons`, this lemma connects a weak derivative of
order $n$ with $n$ iterated weak derivatives of order one. An induction on the order can so
build weak derivatives one direction at a time, as in the Leibniz rule for a smooth factor. The
proof applies the defining identity twice, to the test functions $\partial_z \varphi$ and
$\varphi$, and the signs $(-1)^n$ and $(-1)^1$ multiply to $(-1)^{n+1}$. -/
theorem cons {z : E} {u : E → F} (h : HasWeakIteratedLineDerivOn y f w Ω μ)
    (h' : HasWeakIteratedLineDerivOn ![z] w u Ω μ) :
    HasWeakIteratedLineDerivOn (Fin.cons z y) f u Ω μ where
  locallyIntegrableOn := h.locallyIntegrableOn
  locallyIntegrableOn_weakDeriv := h'.locallyIntegrableOn_weakDeriv
  integral_smul_eq φ := by
    have e1 : ∫ x in (Ω : Set E), iteratedFDeriv ℝ (n + 1) (φ : E → ℝ) x (Fin.cons z y) • f x ∂μ
        = ∫ x in (Ω : Set E), iteratedFDeriv ℝ n (φ.fderivApply z : E → ℝ) x y • f x ∂μ := by
      simp_rw [TestFunction.iteratedFDeriv_cons φ z y]
    have e2 : ∫ x in (Ω : Set E), (φ.fderivApply z) x • w x ∂μ
        = ∫ x in (Ω : Set E), iteratedFDeriv ℝ 1 (φ : E → ℝ) x ![z] • w x ∂μ := by
      simp [iteratedFDeriv_one_apply]
    rw [e1, h.integral_smul_eq, e2, h'.integral_smul_eq, smul_smul]
    congr 1
    ring

omit [OpensMeasurableSpace E] in
/-- **The converse of the composition rule.** Let $y \in E^n$ and $z \in E$. If $w$ is a weak
derivative of $f$ along $y$ on $\Omega$, and $u$ is a weak derivative of $f$ along the tuple
$(z, y_1, \dots, y_n)$, then $u$ is a weak derivative of $w$ along the one-element tuple $(z)$.

So the weak derivatives of a Sobolev function form a chain: the derivative of order $n + 1$
along $(z, y_1, \dots, y_n)$ is the first-order derivative in the direction $z$ of the
derivative of order $n$ along $y$. -/
theorem of_cons {z : E} {u : E → F} (h : HasWeakIteratedLineDerivOn y f w Ω μ)
    (h' : HasWeakIteratedLineDerivOn (Fin.cons z y) f u Ω μ) :
    HasWeakIteratedLineDerivOn ![z] w u Ω μ where
  locallyIntegrableOn := h.locallyIntegrableOn_weakDeriv
  locallyIntegrableOn_weakDeriv := h'.locallyIntegrableOn_weakDeriv
  integral_smul_eq φ := by
    have k1 := h.integral_smul_eq (φ.fderivApply z)
    have k2 := h'.integral_smul_eq φ
    simp_rw [TestFunction.iteratedFDeriv_cons φ z y] at k2
    have e2 : ∫ x in (Ω : Set E), (φ.fderivApply z) x • w x ∂μ
        = ∫ x in (Ω : Set E), iteratedFDeriv ℝ 1 (φ : E → ℝ) x ![z] • w x ∂μ := by
      simp [iteratedFDeriv_one_apply]
    have key : ((-1 : ℝ) ^ n) •
          ∫ x in (Ω : Set E), iteratedFDeriv ℝ 1 (φ : E → ℝ) x ![z] • w x ∂μ
        = ((-1 : ℝ) ^ n) • ((-1 : ℝ) ^ 1 • ∫ x in (Ω : Set E), φ x • u x ∂μ) := by
      rw [← e2, ← k1, k2, smul_smul]
      congr 1
      ring
    exact smul_right_injective F (pow_ne_zero n (by norm_num : (-1 : ℝ) ≠ 0)) key

/-- **The Leibniz rule for a smooth factor.** Let $y$ be a tuple of length $m = 1$, let $f$ be a
real function with the weak derivative $w$ along $y$ on $\Omega$, and let $g$ be a smooth real
function. Then $f g$ has the weak derivative
$$x \mapsto w(x) g(x) + f(x) \, D^m g(x)(y)$$
along $y$ on $\Omega$.

Proposition 7.1.11 of [han2009theoretical] allows both factors to be merely locally integrable
with locally integrable weak derivatives. That case needs mollification in $L^p$ and is not
proved here. -/
theorem mul_contDiff {m : ℕ} {f' w' : E → ℝ} {y' : Fin m → E} {Ω : Opens E} {μ : Measure E}
    (h : HasWeakIteratedLineDerivOn y' f' w' Ω μ) (hm : m = 1) {g : E → ℝ}
    (hg : ContDiff ℝ ∞ g) :
    HasWeakIteratedLineDerivOn y' (fun x ↦ f' x * g x)
      (fun x ↦ w' x * g x + f' x * iteratedFDeriv ℝ m g x y') Ω μ := by
  subst hm
  simp only [iteratedFDeriv_one_apply]
  have hgd : ContDiff ℝ ∞ fun x ↦ fderiv ℝ g x (y' 0) :=
    (hg.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  refine ⟨h.locallyIntegrableOn.mul_continuous hg.continuous,
    (h.locallyIntegrableOn_weakDeriv.mul_continuous hg.continuous).add
      (h.locallyIntegrableOn.mul_continuous hgd.continuous), fun φ ↦ ?_⟩
  set ψ : 𝓓(Ω, ℝ) := φ.mulContDiff hg with hψ
  set χ : 𝓓(Ω, ℝ) := φ.mulContDiff hgd with hχ
  set θ : 𝓓(Ω, ℝ) := (φ.fderivApply (y' 0)).mulContDiff hg with hθ
  have hexp : ∀ x, iteratedFDeriv ℝ 1 (ψ : E → ℝ) x y' = χ x + θ x := by
    intro x
    rw [iteratedFDeriv_one_apply]
    change fderiv ℝ (fun z ↦ φ z * g z) x (y' 0) = φ x * fderiv ℝ g x (y' 0)
      + fderiv ℝ (φ : E → ℝ) x (y' 0) * g x
    rw [fderiv_fun_mul (φ.contDiff.differentiable (by simp) x) (hg.differentiable (by simp) x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have Iχ := (h.integrable_smul χ).integrableOn (s := (Ω : Set E))
  have Iθ := (h.integrable_smul θ).integrableOn (s := (Ω : Set E))
  have Iψ := (h.integrable_smul_weakDeriv ψ).integrableOn (s := (Ω : Set E))
  have e1 : ∫ x in (Ω : Set E), iteratedFDeriv ℝ 1 (ψ : E → ℝ) x y' • f' x ∂μ
      = (∫ x in (Ω : Set E), χ x • f' x ∂μ) + ∫ x in (Ω : Set E), θ x • f' x ∂μ := by
    rw [← integral_add Iχ Iθ]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by
      simp only [hexp x, add_smul])
  have e2 : ∫ x in (Ω : Set E), φ x • (w' x * g x + f' x * fderiv ℝ g x (y' 0)) ∂μ
      = (∫ x in (Ω : Set E), ψ x • w' x ∂μ) + ∫ x in (Ω : Set E), χ x • f' x ∂μ := by
    rw [← integral_add Iψ Iχ]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by
      simp only [hψ, hχ, TestFunction.mulContDiff_coe, smul_eq_mul]; ring)
  have e3 : ∫ x in (Ω : Set E), iteratedFDeriv ℝ 1 (φ : E → ℝ) x y' • (f' x * g x) ∂μ
      = ∫ x in (Ω : Set E), θ x • f' x ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by
      simp only [hθ, TestFunction.mulContDiff_coe, TestFunction.fderivApply_coe,
        iteratedFDeriv_one_apply, smul_eq_mul]
      ring)
  have key := h.integral_smul_eq ψ
  rw [e1] at key
  rw [e3, e2]
  simp only [pow_one, neg_one_smul] at key ⊢
  linarith [key]

variable [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F]

/-- **Uniqueness of the weak derivative along a tuple**, the tuple-by-tuple form of Lemma 7.1.4 of
[han2009theoretical]. Let $E$ be finite-dimensional with its Borel $\sigma$-algebra and let $F$
be complete. If $w_1$ and $w_2$ are weak derivatives of $f$ along $y$ on $\Omega$, then
$w_1(x) = w_2(x)$ for almost every $x \in \Omega$. -/
theorem ae_eq {w₁ w₂ : E → F} (h₁ : HasWeakIteratedLineDerivOn y f w₁ Ω μ)
    (h₂ : HasWeakIteratedLineDerivOn y f w₂ Ω μ) : ∀ᵐ x ∂μ, x ∈ (Ω : Set E) → w₁ x = w₂ x := by
  have key : ∀ᵐ x ∂μ, x ∈ (Ω : Set E) → w₁ x - w₂ x = 0 := by
    refine Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (LocallyIntegrableOn.sub h₁.locallyIntegrableOn_weakDeriv
        h₂.locallyIntegrableOn_weakDeriv) fun g hg h'g hgs ↦ ?_
    set φ : 𝓓(Ω, ℝ) := ⟨g, hg, h'g, hgs⟩ with hφ
    have e1 : Integrable (fun x ↦ g x • w₁ x) μ := h₁.integrable_smul_weakDeriv φ
    have e2 : Integrable (fun x ↦ g x • w₂ x) μ := h₂.integrable_smul_weakDeriv φ
    have key : ∫ x, g x • w₁ x ∂μ = ∫ x, g x • w₂ x ∂μ :=
      smul_right_injective F (pow_ne_zero n (by norm_num : (-1 : ℝ) ≠ 0))
        ((h₁.integral_smul_eq' φ).symm.trans (h₂.integral_smul_eq' φ))
    have hsub : (fun x ↦ g x • (w₁ x - w₂ x)) = fun x ↦ g x • w₁ x - g x • w₂ x :=
      funext fun x ↦ smul_sub _ _ _
    rw [hsub, integral_sub e1 e2, key, sub_self]
  filter_upwards [key] with x hx hxΩ using sub_eq_zero.mp (hx hxΩ)

/-- Let $E$ be finite-dimensional with its Borel $\sigma$-algebra, let $F$ be complete, and let $y$
have length $n = 0$. If $w$ is a weak derivative of $f$ along $y$ on $\Omega$, then
$w(x) = f(x)$ for almost every $x \in \Omega$. -/
theorem ae_eq_of_length_eq_zero (hn : n = 0) (h : HasWeakIteratedLineDerivOn y f w Ω μ) :
    ∀ᵐ x ∂μ, x ∈ (Ω : Set E) → w x = f x :=
  h.ae_eq (of_length_eq_zero hn y h.locallyIntegrableOn)

end HasWeakIteratedLineDerivOn

end Line

/-! ### Weak derivatives under a continuous linear map -/

/-- **A continuous linear map passes through the weak derivative.** Let $F$ be complete and let
$L : F \to G$ be a continuous linear map. If $w$ is a weak derivative of $f$ along $y$ on
$\Omega$, then $L \circ w$ is a weak derivative of $L \circ f$ along $y$.

Both sides of the integration by parts formula integrate integrable functions, so $L$ commutes
with the integrals, and $L$ is $\mathbb{R}$-linear, so it commutes with the scalars
$D^n \varphi(x)(y)$ and $(-1)^n$. The completeness of $F$ makes `MeasureTheory.integral` on $F$
the Bochner integral and not the default value $0$; without it the hypothesis carries no
information. The space $G$ need not be complete, because there the default value makes the
conclusion trivial. -/
theorem HasWeakIteratedLineDerivOn.comp_continuousLinearMap {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {n : ℕ} {y : Fin n → E} {f w : E → F} {Ω : Opens E} {μ : Measure E}
    (h : HasWeakIteratedLineDerivOn y f w Ω μ) (L : F →L[ℝ] G) :
    HasWeakIteratedLineDerivOn y (fun x ↦ L (f x)) (fun x ↦ L (w x)) Ω μ where
  locallyIntegrableOn := h.locallyIntegrableOn.comp_continuousLinearMap L
  locallyIntegrableOn_weakDeriv := h.locallyIntegrableOn_weakDeriv.comp_continuousLinearMap L
  integral_smul_eq φ := by
    by_cases hG : CompleteSpace G
    · have i₁ : Integrable (fun x ↦ iteratedFDeriv ℝ n (φ : E → ℝ) x y • f x)
          (μ.restrict (Ω : Set E)) := by
        have h' := (h.integrable_smul (φ.iteratedFDerivApply n y)).integrableOn (s := (Ω : Set E))
        simp only [TestFunction.iteratedFDerivApply_apply] at h'
        exact h'
      have i₂ : Integrable (fun x ↦ (φ : E → ℝ) x • w x) (μ.restrict (Ω : Set E)) :=
        (h.integrable_smul_weakDeriv φ).integrableOn
      calc ∫ x in (Ω : Set E), iteratedFDeriv ℝ n (φ : E → ℝ) x y • L (f x) ∂μ
          = ∫ x in (Ω : Set E), L (iteratedFDeriv ℝ n (φ : E → ℝ) x y • f x) ∂μ := by
            simp only [map_smul]
        _ = L (∫ x in (Ω : Set E), iteratedFDeriv ℝ n (φ : E → ℝ) x y • f x ∂μ) :=
            L.integral_comp_comm i₁
        _ = L ((-1 : ℝ) ^ n • ∫ x in (Ω : Set E), (φ : E → ℝ) x • w x ∂μ) := by
            rw [h.integral_smul_eq φ]
        _ = (-1 : ℝ) ^ n • ∫ x in (Ω : Set E), (φ : E → ℝ) x • L (w x) ∂μ := by
            rw [map_smul, ← L.integral_comp_comm i₂]
            simp only [map_smul]
    · simp only [integral_of_not_completeSpace hG, smul_zero]

/-! ### The real and the complex form of one weak derivative -/

/-- **Real and complex weak derivatives.** Let $f, w$ be real functions and $y \in E^n$. Then $w$ is
a weak derivative of $f$ along $y$ on $\Omega$ if and only if $x \mapsto w(x) \in \mathbb{C}$ is
a weak derivative of $x \mapsto f(x) \in \mathbb{C}$ along $y$ on $\Omega$.

The embedding $\mathbb{R} \to \mathbb{C}$ and the real part are continuous $\mathbb{R}$-linear
maps, so `HasWeakIteratedLineDerivOn.comp_continuousLinearMap` gives both directions. -/
theorem HasWeakIteratedLineDerivOn.ofReal_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E] {n : ℕ} {y : Fin n → E} {f w : E → ℝ}
    {Ω : Opens E} {μ : Measure E} :
    HasWeakIteratedLineDerivOn y f w Ω μ ↔
      HasWeakIteratedLineDerivOn y (fun x ↦ (f x : ℂ)) (fun x ↦ (w x : ℂ)) Ω μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa using h.comp_continuousLinearMap Complex.ofRealCLM
  · simpa using h.comp_continuousLinearMap Complex.reCLM

/-! ### Classical derivatives are weak derivatives -/

section Classical

variable [FiniteDimensional ℝ E] [BorelSpace E] {N : ℕ∞ω} {m : ℕ}

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- If $f$ is of class $C^N$ on the open set $\Omega$ and $m \le N$, then the derivative $D^m f$ is
continuous on $\Omega$. -/
theorem ContDiffOn.continuousOn_iteratedFDeriv (hf : ContDiffOn ℝ N f Ω)
    (hm : (m : ℕ∞ω) ≤ N) : ContinuousOn (iteratedFDeriv ℝ m f) (Ω : Set E) := fun x hx ↦
  ((hf.contDiffAt (Ω.isOpen.mem_nhds hx)).iteratedFDeriv_right (m := 0)
    (by simpa using hm)).continuousAt.continuousWithinAt

/-- Let $E$ be finite-dimensional with its Borel $\sigma$-algebra and $\mu$ locally finite. If $f$
is of class $C^N$ on the open set $\Omega$, $m \le N$ and $y \in E^m$, then
$x \mapsto D^m f(x)(y)$ is locally integrable on $\Omega$. -/
theorem ContDiffOn.locallyIntegrableOn_iteratedFDeriv_apply [IsLocallyFiniteMeasure μ]
    (hf : ContDiffOn ℝ N f Ω) (hm : (m : ℕ∞ω) ≤ N) (y : Fin m → E) :
    LocallyIntegrableOn (fun x ↦ iteratedFDeriv ℝ m f x y) (Ω : Set E) μ :=
  ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin m ↦ E) F y).continuous.comp_continuousOn
    (hf.continuousOn_iteratedFDeriv hm)).locallyIntegrableOn Ω.isOpen.measurableSet

variable [μ.IsAddHaarMeasure]

/-- **Iterated integration by parts on an open set**, formula (7.1.1) of [han2009theoretical]. Let
$E$ be finite-dimensional with an additive Haar measure $\mu$, and let $f$ be of class $C^N$ on
the open set $\Omega$. Then for every $n \le N$, every real test function $\varphi$ on $\Omega$
and every tuple $y \in E^n$,
$$\int_\Omega D^n \varphi(x)(y) \, f(x) \, d\mu = (-1)^n \int_\Omega \varphi(x) \, D^n f(x)(y)
  \, d\mu.$$
-/
theorem ContDiffOn.integral_iteratedFDeriv_smul (hf : ContDiffOn ℝ N f Ω) :
    ∀ (n : ℕ), (n : ℕ∞ω) ≤ N → ∀ (φ : 𝓓(Ω, ℝ)) (y : Fin n → E),
      ∫ x in (Ω : Set E), iteratedFDeriv ℝ n φ x y • f x ∂μ
        = (-1 : ℝ) ^ n • ∫ x in (Ω : Set E), φ x • iteratedFDeriv ℝ n f x y ∂μ := by
  intro n
  induction n with
  | zero => intro _ φ y; simp
  | succ n ih =>
    intro hn φ y
    have hnN : (n : ℕ∞ω) ≤ N := le_trans (by exact_mod_cast n.le_succ) hn
    have hn1 : (1 : ℕ∞ω) + (n : ℕ∞ω) ≤ N := by
      refine le_trans (le_of_eq ?_) hn
      push_cast
      exact add_comm _ _
    have hdiff : ∀ x ∈ (Ω : Set E), DifferentiableAt ℝ (iteratedFDeriv ℝ n f) x := fun x hx ↦
      ((hf.contDiffAt (Ω.isOpen.mem_nhds hx)).iteratedFDeriv_right (m := 1)
        hn1).differentiableAt one_ne_zero
    have hGdiff : ∀ x ∈ (Ω : Set E),
        DifferentiableAt ℝ (fun z ↦ iteratedFDeriv ℝ n f z (Fin.tail y)) x := fun x hx ↦
      ((hdiff x hx).hasFDerivAt.continuousMultilinear_apply_const _).differentiableAt
    have hGderiv : ∀ x ∈ (Ω : Set E),
        fderiv ℝ (fun z ↦ iteratedFDeriv ℝ n f z (Fin.tail y)) x (y 0)
          = iteratedFDeriv ℝ (n + 1) f x y :=
      fun x hx ↦ (iteratedFDeriv_succ_apply_left_of_differentiableAt (hdiff x hx) y).symm
    have hGloc : LocallyIntegrableOn (fun x ↦ iteratedFDeriv ℝ n f x (Fin.tail y))
        (Ω : Set E) μ := hf.locallyIntegrableOn_iteratedFDeriv_apply hnN _
    have hG'loc : LocallyIntegrableOn
        (fun x ↦ fderiv ℝ (fun z ↦ iteratedFDeriv ℝ n f z (Fin.tail y)) x (y 0)) (Ω : Set E) μ :=
      LocallyIntegrableOn.congr ((ae_restrict_iff' Ω.isOpen.measurableSet).2
        (Filter.Eventually.of_forall fun x hx ↦ (hGderiv x hx).symm))
        (hf.locallyIntegrableOn_iteratedFDeriv_apply hn y)
    have ibp : ∫ x, φ x • fderiv ℝ (fun z ↦ iteratedFDeriv ℝ n f z (Fin.tail y)) x (y 0) ∂μ
        = -∫ x, fderiv ℝ (φ : E → ℝ) x (y 0) • iteratedFDeriv ℝ n f x (Fin.tail y) ∂μ :=
      integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
        (LocallyIntegrableOn.integrable_smul_left_of_tsupport_subset hGloc
          (φ.fderivApply (y 0)).contDiff.continuous (φ.fderivApply (y 0)).hasCompactSupport
          (φ.fderivApply (y 0)).tsupport_subset)
        (LocallyIntegrableOn.integrable_smul_left_of_tsupport_subset hG'loc φ.contDiff.continuous
          φ.hasCompactSupport φ.tsupport_subset)
        (LocallyIntegrableOn.integrable_smul_left_of_tsupport_subset hGloc φ.contDiff.continuous
          φ.hasCompactSupport φ.tsupport_subset)
        (fun x _ ↦ φ.contDiff.differentiable (by simp) x)
        (fun x hx ↦ hGdiff x (φ.tsupport_subset hx))
    have r1 : ∫ x in (Ω : Set E),
          φ x • fderiv ℝ (fun z ↦ iteratedFDeriv ℝ n f z (Fin.tail y)) x (y 0) ∂μ
        = ∫ x, φ x • fderiv ℝ (fun z ↦ iteratedFDeriv ℝ n f z (Fin.tail y)) x (y 0) ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
        rw [φ.eq_zero_of_notMem hx, zero_smul]
    have r2 : ∫ x in (Ω : Set E),
          fderiv ℝ (φ : E → ℝ) x (y 0) • iteratedFDeriv ℝ n f x (Fin.tail y) ∂μ
        = ∫ x, fderiv ℝ (φ : E → ℝ) x (y 0) • iteratedFDeriv ℝ n f x (Fin.tail y) ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
        rw [show fderiv ℝ (φ : E → ℝ) x (y 0) = 0 from
          (φ.fderivApply (y 0)).eq_zero_of_notMem hx, zero_smul]
    have main : ∫ x in (Ω : Set E),
          fderiv ℝ (φ : E → ℝ) x (y 0) • iteratedFDeriv ℝ n f x (Fin.tail y) ∂μ
        = -∫ x in (Ω : Set E), φ x • iteratedFDeriv ℝ (n + 1) f x y ∂μ := by
      rw [r2, ← neg_neg (∫ x, fderiv ℝ (φ : E → ℝ) x (y 0) •
        iteratedFDeriv ℝ n f x (Fin.tail y) ∂μ), ← ibp, ← r1]
      congr 1
      exact setIntegral_congr_fun Ω.isOpen.measurableSet fun x hx ↦ by rw [hGderiv x hx]
    have e2 := ih hnN (φ.fderivApply (y 0)) (Fin.tail y)
    simp only [TestFunction.fderivApply_coe] at e2
    calc ∫ x in (Ω : Set E), iteratedFDeriv ℝ (n + 1) (φ : E → ℝ) x y • f x ∂μ
        = ∫ x in (Ω : Set E),
            iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ (φ : E → ℝ) z (y 0)) x (Fin.tail y) • f x ∂μ :=
          setIntegral_congr_fun Ω.isOpen.measurableSet fun x _ ↦ by
            rw [ContDiff.iteratedFDeriv_succ_apply_left' φ.contDiff n y x]
      _ = (-1 : ℝ) ^ n • ∫ x in (Ω : Set E),
            fderiv ℝ (φ : E → ℝ) x (y 0) • iteratedFDeriv ℝ n f x (Fin.tail y) ∂μ := e2
      _ = (-1 : ℝ) ^ n • -∫ x in (Ω : Set E), φ x • iteratedFDeriv ℝ (n + 1) f x y ∂μ := by
          rw [main]
      _ = (-1 : ℝ) ^ (n + 1) • ∫ x in (Ω : Set E), φ x • iteratedFDeriv ℝ (n + 1) f x y ∂μ := by
          rw [pow_succ, mul_smul, neg_one_smul]

/-- **A classical derivative is a weak derivative**, Lemma 7.1.5 of [han2009theoretical]. Let $E$ be
finite-dimensional with an additive Haar measure $\mu$, let $f$ be of class $C^N$ on the open
set $\Omega$, and let $m \le N$. Then the classical derivative $D^m f$ is an $m$-th weak
derivative of $f$ on $\Omega$.

So the weak derivative extends the classical one, and both can be written $\partial^n$. -/
theorem ContDiffOn.hasWeakIteratedFDerivOn (hf : ContDiffOn ℝ N f Ω) (hm : (m : ℕ∞ω) ≤ N) :
    HasWeakIteratedFDerivOn m f (iteratedFDeriv ℝ m f) Ω μ where
  locallyIntegrableOn := hf.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  locallyIntegrableOn_weakDeriv :=
    (hf.continuousOn_iteratedFDeriv hm).locallyIntegrableOn Ω.isOpen.measurableSet
  integral_smul_eq φ y := hf.integral_iteratedFDeriv_smul m hm φ y

end Classical

/-! ### First-order weak derivatives -/

section FirstOrder

variable {w : E → E →L[ℝ] F}

/-- A function $w : E \to (E \to_L F)$ is a first-order weak derivative of $f$ on $\Omega$ if and
only if $f$ and $w$ are locally integrable on $\Omega$ and, for every real test function
$\varphi$ on $\Omega$ and every direction $v$,
$$\int_\Omega D\varphi(x) v \, f(x) \, d\mu = -\int_\Omega \varphi(x) \, w(x) v \, d\mu.$$
-/
theorem hasWeakFDerivOn_iff :
    HasWeakFDerivOn f w Ω μ ↔ LocallyIntegrableOn f Ω μ ∧ LocallyIntegrableOn w Ω μ ∧
      ∀ (φ : 𝓓(Ω, ℝ)) (v : E), ∫ x in (Ω : Set E), fderiv ℝ φ x v • f x ∂μ
        = -∫ x in (Ω : Set E), φ x • w x v ∂μ := by
  constructor
  · refine fun h ↦ ⟨h.locallyIntegrableOn, ?_, fun φ v ↦ ?_⟩
    · refine MeasureTheory.LocallyIntegrableOn.congr
        (Filter.Eventually.of_forall fun x ↦ ?_)
        (MeasureTheory.LocallyIntegrableOn.comp_continuousLinearMap
          h.locallyIntegrableOn_weakDeriv
          (continuousMultilinearCurryFin1 ℝ E F).toContinuousLinearEquiv.toContinuousLinearMap)
      simp
    · simpa [iteratedFDeriv_one_apply] using h.integral_smul_eq φ fun _ ↦ v
  · refine fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, ?_, fun φ y ↦ ?_⟩
    · exact MeasureTheory.LocallyIntegrableOn.comp_continuousLinearMap h₂
        (continuousMultilinearCurryFin1 ℝ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap
    · simpa [iteratedFDeriv_one_apply] using h₃ φ (y 0)

/-- If $w$ is a first-order weak derivative of $f$ on $\Omega$, then for every test function
$\varphi$ on $\Omega$ and every direction $v$, $\int_\Omega D\varphi(x) v \, f(x) \, d\mu =
-\int_\Omega \varphi(x) \, w(x) v \, d\mu$. -/
theorem HasWeakFDerivOn.integral_smul_eq (h : HasWeakFDerivOn f w Ω μ) (φ : 𝓓(Ω, ℝ)) (v : E) :
    ∫ x in (Ω : Set E), fderiv ℝ φ x v • f x ∂μ = -∫ x in (Ω : Set E), φ x • w x v ∂μ :=
  (hasWeakFDerivOn_iff.1 h).2.2 φ v

/-- A function with a first-order weak derivative on $\Omega$ is locally integrable on $\Omega$. -/
theorem HasWeakFDerivOn.locallyIntegrableOn (h : HasWeakFDerivOn f w Ω μ) :
    LocallyIntegrableOn f Ω μ :=
  (hasWeakFDerivOn_iff.1 h).1

/-- A first-order weak derivative on $\Omega$ is locally integrable on $\Omega$. -/
theorem HasWeakFDerivOn.locallyIntegrableOn_weakDeriv (h : HasWeakFDerivOn f w Ω μ) :
    LocallyIntegrableOn w Ω μ :=
  (hasWeakFDerivOn_iff.1 h).2.1

end FirstOrder
