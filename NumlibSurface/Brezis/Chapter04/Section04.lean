/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Numlib.Analysis.Convolution.Lp
import Numlib.Analysis.Normed.Lp.SmoothApprox
import Numlib.MeasureTheory.Function.EssSupport
import NumlibSurface.Brezis.Chapter04.Section03

/-!
# Brezis, Section 4.4: Convolution and regularization

This module formalizes Section 4.4 of [brezis2011functional] for real-valued functions on
$\mathbb{R}^N$ with Lebesgue measure. The convolution of $f$ and $g$ is
$$(f \star g)(x) = \int_{\mathbb{R}^N} f(x - y) g(y) \, dy.$$
The module proves Young's inequality $\|f \star g\|_p \le \|f\|_1 \|g\|_p$ (Theorem 4.15) and its
general form (Theorem 4.33, from the Comments on Chapter 4), the adjoint identity (Proposition
4.16), the definition of the support of a measurable function and the support of a convolution
(Propositions 4.17 and 4.18), and the regularity of $f \star g$ for $f \in C_c^k$ and
$g \in L^1_{loc}$ (Propositions 4.19 and 4.20). With a sequence of mollifiers $(\rho_n)$,
$\rho_n \star f \to f$ uniformly on compact sets for continuous $f$ (Proposition 4.21) and in $L^p$
for $f \in L^p$, $1 \le p < \infty$ (Theorem 4.22). As consequences, $C_c^\infty(\Omega)$ is dense
in $L^p(\Omega)$ (Corollary 4.23), and a function $u \in L^1_{loc}(\Omega)$ with $\int uf = 0$ for
all $f \in C_c^\infty(\Omega)$ vanishes a.e. (Corollary 4.24).

Mathlib's `Mathlib.Analysis.Convolution` supplies the pointwise theory (Propositions 4.19 and 4.20,
Corollary 4.24). The backbone module `Numlib.Analysis.Convolution.Lp` supplies the $L^p$ theory
(Theorems 4.15, 4.22 and 4.33, Proposition 4.16), `Numlib.MeasureTheory.Function.EssSupport` the
support of a measurable function (Propositions 4.17 and 4.18, Remarks 9 and 10), and
`Numlib.Analysis.Normed.Lp.SmoothApprox` Corollary 4.23.

## Main definitions

* Section 4.4, definition of $L^p_{loc}(\Omega)$, `Brezis.Chapter04.MemLpLoc`:
  $f \chi_K \in L^p(\Omega)$ for every compact $K \subseteq \Omega$.
* Section 4.4, definition of a sequence of mollifiers, `Brezis.Chapter04.IsMollifierSeq`: smooth
  nonnegative functions with integral $1$ and support in $\overline{B(0, 1/n)}$.

## Main results

* Theorem 4.15 (Young), `Brezis.Chapter04.theorem_4_15`: for $f \in L^1$ and $g \in L^p$,
  $f \star g$ is defined a.e., lies in $L^p$, and $\|f \star g\|_p \le \|f\|_1 \|g\|_p$.
* Proposition 4.16, `Brezis.Chapter04.proposition_4_16`:
  $\int (f \star g) h = \int g (\check f \star h)$.
* Proposition 4.17, `Brezis.Chapter04.proposition_4_17`: the support of a function, the complement
  of the largest open set on which it vanishes a.e.
* Remark 9, `Brezis.Chapter04.remark_4_9`: the support depends only on the a.e. class, and is the
  usual support for a continuous function.
* Proposition 4.18, `Brezis.Chapter04.proposition_4_18`: $\operatorname{supp}(f \star g) \subseteq
  \overline{\operatorname{supp} f + \operatorname{supp} g}$.
* Remark 10, `Brezis.Chapter04.remark_4_10`: if $f$ and $g$ have compact support, so does
  $f \star g$.
* Section 4.4, `Brezis.Chapter04.memLpLoc_one_iff_locallyIntegrableOn` and
  `Brezis.Chapter04.MemLpLoc.memLpLoc_one`: $L^1_{loc}$ is local integrability, and
  $L^p_{loc} \subseteq L^1_{loc}$.
* Proposition 4.19, `Brezis.Chapter04.proposition_4_19`: for $f \in C_c$ and $g \in L^1_{loc}$,
  $f \star g$ is defined everywhere and continuous.
* Proposition 4.20, `Brezis.Chapter04.proposition_4_20`: for $f \in C_c^k$ and $g \in L^1_{loc}$,
  $f \star g \in C^k$ and the derivatives fall on $f$.
* Section 4.4, `Brezis.Chapter04.isMollifierSeq_contDiffBump` and
  `Brezis.Chapter04.IsMollifierSeq.tendsto_support`: sequences of mollifiers exist, and their
  supports shrink to $0$.
* Proposition 4.21, `Brezis.Chapter04.proposition_4_21`: for continuous $f$, $\rho_n \star f \to f$
  uniformly on compact sets.
* Theorem 4.22, `Brezis.Chapter04.theorem_4_22`: for $f \in L^p$, $1 \le p < \infty$,
  $\rho_n \star f \to f$ in $L^p$.
* Corollary 4.23, `Brezis.Chapter04.corollary_4_23`: $C_c^\infty(\Omega)$ is dense in $L^p(\Omega)$
  for open $\Omega$ and $1 \le p < \infty$.
* Corollary 4.24, `Brezis.Chapter04.corollary_4_24`: if $u \in L^1_{loc}(\Omega)$ and $\int uf = 0$
  for all $f \in C_c^\infty(\Omega)$, then $u = 0$ a.e. on $\Omega$.
* Theorem 4.33 (Young, general form), `Brezis.Chapter04.theorem_4_33`:
  $\|f \star g\|_r \le \|f\|_p \|g\|_q$ for $1/r = 1/p + 1/q - 1$.

## Conventions

* The space $\mathbb{R}^N$ is `EuclideanSpace ℝ (Fin N)`, with the local notation `𝔼`, with Lebesgue
  measure `volume`.
* The convolution $f \star g$ is Mathlib's `f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g`, defined by
  $(f \star g)(x) = \int f(t) g(x - t) \, dt$. The substitution $y = x - t$ turns it into the
  formula of the source (`MeasureTheory.convolution_eq_swap`).
* The support $\operatorname{supp} f$ of a measurable function is the backbone's
  `MeasureTheory.essSupport volume f`.
* A function of $C_c^\infty(\Omega)$ is a function $f$ on $\mathbb{R}^N$ with `ContDiff ℝ ∞ f`,
  `HasCompactSupport f` and `tsupport f ⊆ Ω`.

## Deviations from the source

* **Proposition 4.18 and Remark 10** (generalization). The source assumes $f \in L^1$ and
  $g \in L^p$. The formal statements assume no integrability. See
  `Brezis.Chapter04.proposition_4_18` and `Brezis.Chapter04.remark_4_10`.

## Not formalized

* **Remark 10, second sentence.** The claim that $f \star g$ need not have compact support when only
  one of $f$, $g$ has compact support has no example in the source.
* **Proposition 4.20, higher derivatives for $f \in C_c^k$.** The formula
  $D^\alpha(f \star g) = (D^\alpha f) \star g$ is stated for $|\alpha| = 1$ when $f \in C_c^k$, and
  for all $\alpha$ only when $f \in C_c^\infty$, because the backbone's
  `MeasureTheory.LocallyIntegrable.iteratedFDeriv_convolution_left_apply` covers smooth $f$ only.
-/

open Filter MeasureTheory Metric Topology
open scoped ContDiff Convolution Pointwise

namespace Brezis.Chapter04

variable {N : ℕ}

/-- The space $\mathbb{R}^N$ of the source, `EuclideanSpace ℝ (Fin N)`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-! ### Young's inequality and the adjoint identity -/

/-- The bilinear maps `ContinuousLinearMap.lsmul ℝ ℝ` and `ContinuousLinearMap.mul ℝ ℝ` are equal:
both send $(a, b)$ to $ab$. So the two ways to write a real convolution agree. -/
theorem lsmul_eq_mul_real : ContinuousLinearMap.lsmul ℝ ℝ = ContinuousLinearMap.mul ℝ ℝ :=
  ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b => by simp

/-- The operator norm of the multiplication $\mathbb{R} \times \mathbb{R} \to \mathbb{R}$, as a
bilinear map `ContinuousLinearMap.mul ℝ ℝ`, is at most $1$, as an element of $[0, +\infty]$. -/
theorem enorm_mul_real_le_one : ‖ContinuousLinearMap.mul ℝ ℝ‖ₑ ≤ 1 := by
  rw [← ofReal_norm, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (ContinuousLinearMap.opNorm_mul_le ℝ ℝ)

/-- **Theorem 4.15** of [brezis2011functional] (Young). Let $f \in L^1(\mathbb{R}^N)$ and
$g \in L^p(\mathbb{R}^N)$ with $1 \le p \le \infty$. Then for a.e. $x \in \mathbb{R}^N$ the
function $y \mapsto f(x - y) g(y)$ is integrable on $\mathbb{R}^N$, so that
$(f \star g)(x) = \int f(x - y) g(y) \, dy$ is defined. Moreover
$f \star g \in L^p(\mathbb{R}^N)$ and
$$\|f \star g\|_p \le \|f\|_1 \|g\|_p.$$

The norms are `eLpNorm`, with values in $[0, +\infty]$. -/
theorem theorem_4_15 {p : ENNReal} [Fact (1 ≤ p)] {f g : 𝔼 → ℝ} (hf : MemLp f 1 volume)
    (hg : MemLp g p volume) :
    (∀ᵐ x ∂(volume : Measure 𝔼), Integrable (fun y => f (x - y) * g y) volume) ∧
    MemLp (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) p volume ∧
    eLpNorm (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) p volume ≤
      eLpNorm f 1 volume * eLpNorm g p volume := by
  refine ⟨?_, hf.convolution (L := ContinuousLinearMap.mul ℝ ℝ) Fact.out hg, ?_⟩
  · filter_upwards [hf.ae_convolutionExistsAt (L := ContinuousLinearMap.mul ℝ ℝ) Fact.out hg]
      with x hx
    exact convolutionExistsAt_flip.2 hx
  · refine (eLpNorm_convolution_le (L := ContinuousLinearMap.mul ℝ ℝ) Fact.out
      hf.aestronglyMeasurable hg.aestronglyMeasurable).trans ?_
    rw [mul_assoc]
    exact mul_le_of_le_one_left bot_le enorm_mul_real_le_one

/-- **Proposition 4.16** of [brezis2011functional]. Let $1 \le p \le \infty$ with conjugate exponent
$p'$, and let $f \in L^1(\mathbb{R}^N)$, $g \in L^p(\mathbb{R}^N)$ and
$h \in L^{p'}(\mathbb{R}^N)$. Then
$$\int_{\mathbb{R}^N} (f \star g) h = \int_{\mathbb{R}^N} g (\check f \star h), \qquad \check
  f(x) = f(-x).$$

The conjugate exponent $p'$ is `q`.
The reflected function $\check f$ is `f ∘ Neg.neg`. -/
theorem proposition_4_16 {p q : ENNReal} [p.HolderConjugate q] {f g h : 𝔼 → ℝ}
    (hf : MemLp f 1 volume) (hg : MemLp g p volume) (hh : MemLp h q volume) :
    ∫ x, (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) x * h x =
      ∫ y, g y * ((f ∘ Neg.neg) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] h) y :=
  integral_convolution_mul hf hg hh

/-! ### Support and convolution -/

/-- **Proposition 4.17** of [brezis2011functional], with the definition of the support. Let
$f : \mathbb{R}^N \to \mathbb{R}$, and let $\omega$ be the union of all open sets $U$ such that
$f = 0$ a.e. on $U$. Then $f = 0$ a.e. on $\omega$. The **support** $\operatorname{supp} f$ is
by definition $\mathbb{R}^N \setminus \omega$.

The support is the backbone's `MeasureTheory.essSupport volume f`. The first clause says that
its complement is $\omega$, and the second that $f = 0$ a.e. outside it. No measurability of $f$
is needed. -/
theorem proposition_4_17 (f : 𝔼 → ℝ) :
    (essSupport (volume : Measure 𝔼) f)ᶜ =
      ⋃₀ {U : Set 𝔼 | IsOpen U ∧ ∀ᵐ x ∂(volume : Measure 𝔼), x ∈ U → f x = 0} ∧
    ∀ᵐ x ∂(volume : Measure 𝔼), x ∉ essSupport volume f → f x = 0 := by
  refine ⟨?_, ae_eq_zero_of_notMem_essSupport⟩
  rw [essSupport, Measure.compl_support_eq_sUnion]
  congr 1
  ext U
  simp only [Set.mem_ofPred_eq]
  refine and_congr_right fun hU => ?_
  rw [Measure.restrict_apply hU.measurableSet, measure_eq_zero_iff_ae_notMem]
  refine eventually_congr (Eventually.of_forall fun x => ?_)
  simp only [Set.mem_inter_iff, Function.mem_support, not_and, not_not]

/-- **Remark 9** in Chapter 4 of [brezis2011functional].

1. If $f_1 = f_2$ a.e. on $\mathbb{R}^N$, then $\operatorname{supp} f_1 = \operatorname{supp}
   f_2$. So $\operatorname{supp} f$ is defined for an element $f$ of $L^p$.
2. If $f$ is continuous, then $\operatorname{supp} f$ is the usual support, the closure of
   $\{x : f(x) \neq 0\}$.

The usual support is Mathlib's `tsupport f`. -/
theorem remark_4_9 :
    (∀ f₁ f₂ : 𝔼 → ℝ, f₁ =ᵐ[(volume : Measure 𝔼)] f₂ →
      essSupport (volume : Measure 𝔼) f₁ = essSupport volume f₂) ∧
    ∀ f : 𝔼 → ℝ, Continuous f → essSupport (volume : Measure 𝔼) f = tsupport f :=
  ⟨fun _ _ h => essSupport_congr_ae h, fun _ hf => essSupport_eq_tsupport hf⟩

/-- **Proposition 4.18** of [brezis2011functional]. For all functions
$f, g : \mathbb{R}^N \to \mathbb{R}$,
$$\operatorname{supp}(f \star g) \subseteq \overline{\operatorname{supp} f + \operatorname{supp}
  g}.$$

**Generalization.** The source assumes $f \in L^1(\mathbb{R}^N)$ and $g \in L^p(\mathbb{R}^N)$.
The backbone's `MeasureTheory.essSupport_convolution_subset` needs no integrability. -/
theorem proposition_4_18 (f g : 𝔼 → ℝ) :
    essSupport (volume : Measure 𝔼) (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) ⊆
      closure (essSupport volume f + essSupport volume g) :=
  essSupport_convolution_subset _

/-- **Remark 10** in Chapter 4 of [brezis2011functional]. Let $f, g : \mathbb{R}^N \to \mathbb{R}$
have compact support. Then $f \star g$ has compact support.

**Generalization.** The source works with $f \in L^1$ and $g \in L^p$, as in Proposition 4.18.
No integrability is assumed here.

The second sentence of the remark, that this can fail if only one of the functions has compact
support, has no example in the source and is not formalized. -/
theorem remark_4_10 {f g : 𝔼 → ℝ} (hf : IsCompact (essSupport (volume : Measure 𝔼) f))
    (hg : IsCompact (essSupport (volume : Measure 𝔼) g)) :
    IsCompact (essSupport (volume : Measure 𝔼) (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g)) :=
  (hf.add hg).closure.of_isClosed_subset isClosed_essSupport (proposition_4_18 f g)

/-! ### The spaces $L^p_{loc}$ -/

/-- **Section 4.4** of [brezis2011functional], definition of $L^p_{loc}(\Omega)$. Let
$\Omega \subseteq \mathbb{R}^N$ and $1 \le p \le \infty$. A function $f$ belongs to
$L^p_{loc}(\Omega)$ if $f \chi_K \in L^p(\Omega)$ for every compact set $K \subseteq \Omega$.

The source takes $\Omega$ open and $f : \Omega \to \mathbb{R}$. Here $f$ is defined on
$\mathbb{R}^N$; only its values on $\Omega$ matter. The function $f \chi_K$ is `K.indicator f`,
and $L^p(\Omega)$ is $L^p$ of `volume.restrict Ω`. The exponent is not restricted in the
definition. -/
def MemLpLoc (f : 𝔼 → ℝ) (p : ENNReal) (Ω : Set 𝔼) : Prop :=
  ∀ K ⊆ Ω, IsCompact K → MemLp (K.indicator f) p (volume.restrict Ω)

/-- **Section 4.4** of [brezis2011functional]. Let $\Omega \subseteq \mathbb{R}^N$ be open. A
function belongs to $L^1_{loc}(\Omega)$ if and only if it is locally integrable on $\Omega$ in
the sense of Mathlib's `MeasureTheory.LocallyIntegrableOn`. -/
theorem memLpLoc_one_iff_locallyIntegrableOn {f : 𝔼 → ℝ} {Ω : Set 𝔼} (hΩ : IsOpen Ω) :
    MemLpLoc f 1 Ω ↔ LocallyIntegrableOn f Ω volume := by
  rw [locallyIntegrableOn_iff hΩ.isLocallyClosed]
  refine forall_congr' fun K => forall_congr' fun hKΩ => forall_congr' fun hK => ?_
  rw [memLp_one_iff_integrable, integrable_indicator_iff hK.measurableSet, IntegrableOn,
    Measure.restrict_restrict hK.measurableSet, Set.inter_eq_left.2 hKΩ]
  rfl

/-- **Section 4.4** of [brezis2011functional]. Let $\Omega \subseteq \mathbb{R}^N$ and
$1 \le p \le \infty$. If $f \in L^p_{loc}(\Omega)$, then $f \in L^1_{loc}(\Omega)$.

On a compact set $K$ the measure is finite, so $L^p(K) \subseteq L^1(K)$. -/
theorem MemLpLoc.memLpLoc_one {f : 𝔼 → ℝ} {p : ENNReal} [Fact (1 ≤ p)] {Ω : Set 𝔼}
    (hf : MemLpLoc f p Ω) : MemLpLoc f 1 Ω := by
  intro K hKΩ hK
  have h : MemLp f p ((volume.restrict Ω).restrict K) := by
    rw [memLp_iff, ← eLpNorm_indicator_eq_eLpNorm_restrict hK.measurableSet.nullMeasurableSet]
    exact hf K hKΩ hK
  have : IsFiniteMeasure ((volume.restrict Ω).restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (Measure.le_iff'.1 Measure.restrict_le_self K).trans_lt hK.measure_lt_top⟩
  rw [memLp_iff, eLpNorm_indicator_eq_eLpNorm_restrict hK.measurableSet.nullMeasurableSet]
  exact (h.mono_exponent Fact.out).eLpNorm_lt_top

/-- **Proposition 4.19** of [brezis2011functional]. Let $f \in C_c(\mathbb{R}^N)$ and
$g \in L^1_{loc}(\mathbb{R}^N)$. Then $(f \star g)(x)$ is defined for every
$x \in \mathbb{R}^N$, and $f \star g$ is continuous.

"Defined for every $x$" is Mathlib's `ConvolutionExists`. -/
theorem proposition_4_19 {f g : 𝔼 → ℝ} (hf : Continuous f) (hfs : HasCompactSupport f)
    (hg : MemLpLoc g 1 Set.univ) :
    ConvolutionExists f g (ContinuousLinearMap.mul ℝ ℝ) volume ∧
      Continuous (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) := by
  have hg' : LocallyIntegrable g volume :=
    locallyIntegrableOn_univ.1 ((memLpLoc_one_iff_locallyIntegrableOn isOpen_univ).1 hg)
  exact ⟨hfs.convolutionExists_left _ hf hg', hfs.continuous_convolution_left _ hf hg'⟩

/-- **Proposition 4.20** of [brezis2011functional]. Let $1 \le k \le \infty$, let
$f \in C_c^k(\mathbb{R}^N)$ and let $g \in L^1_{loc}(\mathbb{R}^N)$. Then:

1. $f \star g \in C^k(\mathbb{R}^N)$;
2. for all $x, v \in \mathbb{R}^N$, the derivative of $f \star g$ at $x$ in the direction $v$ is
   $((\nabla f \cdot v) \star g)(x)$, that is, $\nabla(f \star g) = (\nabla f) \star g$;
3. if $f \in C_c^\infty(\mathbb{R}^N)$, then for every $n$ and all directions $y_1, \dots, y_n$,
   the $n$-th derivative of $f \star g$ in the directions $y_1, \dots, y_n$ is the convolution
   of the $n$-th derivative of $f$ in these directions with $g$. In particular
   $D^\alpha(f \star g) = (D^\alpha f) \star g$ for every multi-index $\alpha$.

The source states the formula $D^\alpha(f \star g) = (D^\alpha f) \star g$ for $|\alpha| \le k$
and $f \in C_c^k$. Here the formula for $|\alpha| \ge 2$ is stated only for smooth $f$, because
the backbone's `MeasureTheory.LocallyIntegrable.iteratedFDeriv_convolution_left_apply` covers
smooth $f$ only. The derivatives are Mathlib's `fderiv` and `iteratedFDeriv`; $D^\alpha$ along
the coordinate directions is a special case. -/
theorem proposition_4_20 {k : ℕ∞} (hk : 1 ≤ k) {f g : 𝔼 → ℝ} (hf : ContDiff ℝ k f)
    (hfs : HasCompactSupport f) (hg : MemLpLoc g 1 Set.univ) :
    ContDiff ℝ k (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) ∧
    (∀ x v : 𝔼, fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) x v =
      ((fun t => fderiv ℝ f t v) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) x) ∧
    (ContDiff ℝ ∞ f → ∀ (n : ℕ) (x : 𝔼) (y : Fin n → 𝔼),
      iteratedFDeriv ℝ n (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) x y =
        ((fun z => iteratedFDeriv ℝ n f z y) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) x) := by
  have hg' : LocallyIntegrable g volume :=
    locallyIntegrableOn_univ.1 ((memLpLoc_one_iff_locallyIntegrableOn isOpen_univ).1 hg)
  refine ⟨hfs.contDiff_convolution_left _ hf hg', fun x v =>
    hg'.fderiv_convolution_left_apply hfs (hf.of_le (by exact_mod_cast hk)) x v,
    fun hf' n x y => hg'.iteratedFDeriv_convolution_left_apply n hfs hf' x y⟩

/-! ### Mollifiers -/

/-- **Section 4.4** of [brezis2011functional], definition of a sequence of mollifiers. A sequence
$(\rho_n)_{n \ge 1}$ of functions on $\mathbb{R}^N$ is a **sequence of mollifiers** if for every
$n \ge 1$,
$$\rho_n \in C_c^\infty(\mathbb{R}^N), \quad \operatorname{supp} \rho_n \subseteq \overline{B(0,
  1/n)}, \quad \int \rho_n = 1, \quad \rho_n \ge 0 \text{ on } \mathbb{R}^N.$$

The sequence is indexed by `ℕ`, and the term with index $0$ is not constrained. The support here
is the usual support `tsupport`. -/
def IsMollifierSeq (ρ : ℕ → 𝔼 → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ContDiff ℝ ∞ (ρ n) ∧ HasCompactSupport (ρ n) ∧
    tsupport (ρ n) ⊆ closedBall 0 (1 / n) ∧ ∫ x, ρ n x = 1 ∧ ∀ x, 0 ≤ ρ n x

/-- **Section 4.4** of [brezis2011functional], existence of mollifiers. Let $(\varphi_n)$ be a
sequence of smooth bump functions centred at $0$ (Mathlib's `ContDiffBump`) whose outer radius
is at most $1/n$ for $n \ge 1$. Then their normalizations $\varphi_n / \int \varphi_n$ form a
sequence of mollifiers.

The source writes "it is easy to generate a sequence of mollifiers" and uses
$\rho(x) = e^{1/(|x|^2 - 1)}$ for $|x| < 1$. Mathlib builds its bump functions in inner product
spaces from a function of this kind. -/
theorem isMollifierSeq_contDiffBump (φ : ℕ → ContDiffBump (0 : 𝔼))
    (hφ : ∀ n : ℕ, 1 ≤ n → (φ n).rOut ≤ 1 / n) :
    IsMollifierSeq fun n => (φ n).normed volume := fun n hn =>
  ⟨(φ n).contDiff_normed, (φ n).hasCompactSupport_normed,
    by rw [(φ n).tsupport_normed_eq]; exact closedBall_subset_closedBall (hφ n hn),
    (φ n).integral_normed, (φ n).nonneg_normed⟩

/-- The supports of a sequence of mollifiers shrink to $0$: for every neighbourhood $U$ of $0$ in
$\mathbb{R}^N$, the support of $\rho_n$ lies in $U$ for all large $n$.

This is the form of the hypothesis in Mathlib's `convolution_tendsto_right` and in the
backbone's `MeasureTheory.tendsto_eLpNorm_convolution_sub`. It is stated as `Tendsto (fun n =>
Function.support (ρ n)) atTop (𝓝 0).smallSets`. -/
theorem IsMollifierSeq.tendsto_support {ρ : ℕ → 𝔼 → ℝ} (hρ : IsMollifierSeq ρ) :
    Tendsto (fun n => Function.support (ρ n)) atTop (𝓝 (0 : 𝔼)).smallSets := by
  rw [tendsto_smallSets_iff]
  intro t ht
  obtain ⟨ε, hε, hεt⟩ := Metric.mem_nhds_iff.1 ht
  obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt hε
  refine eventually_atTop.2 ⟨max (n₀ + 1) 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_of_max_le_right hn
  have hnn₀ : (1 : ℝ) / n < ε := by
    refine lt_of_le_of_lt ?_ hn₀
    have : (n₀ + 1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_left hn
    exact one_div_le_one_div_of_le (by positivity) this
  refine (subset_tsupport _).trans ((hρ n hn1).2.2.1.trans ?_)
  exact (closedBall_subset_ball hnn₀).trans hεt

/-- **Proposition 4.21** of [brezis2011functional]. Let $(\rho_n)$ be a sequence of mollifiers and
let $f \in C(\mathbb{R}^N)$. Then $\rho_n \star f \to f$ uniformly on compact sets of
$\mathbb{R}^N$.

Uniform convergence on compact sets is Mathlib's `TendstoLocallyUniformly`, which is equivalent
on $\mathbb{R}^N$. The proof applies Mathlib's `convolution_tendsto_right` at every point. -/
theorem proposition_4_21 {ρ : ℕ → 𝔼 → ℝ} (hρ : IsMollifierSeq ρ) {f : 𝔼 → ℝ}
    (hf : Continuous f) :
    TendstoLocallyUniformly (fun n => ρ n ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] f) f atTop := by
  rw [← lsmul_eq_mul_real, tendstoLocallyUniformly_iff_forall_tendsto]
  intro x
  have h1 : Tendsto (fun y : ℕ × 𝔼 => f y.2) (atTop ×ˢ 𝓝 x) (𝓝 (f x)) :=
    hf.continuousAt.tendsto.comp tendsto_snd
  have h2 : Tendsto (fun y : ℕ × 𝔼 => (ρ y.1 ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) y.2)
      (atTop ×ˢ 𝓝 x) (𝓝 (f x)) := by
    refine convolution_tendsto_right (g := fun _ => f) (φ := fun y : ℕ × 𝔼 => ρ y.1)
      (k := fun y => y.2) ?_ ?_ ?_ ?_ ?_ tendsto_snd
    · exact ((eventually_ge_atTop 1).mono fun n hn => (hρ n hn).2.2.2.2).prod_inl (𝓝 x)
    · exact ((eventually_ge_atTop 1).mono fun n hn => (hρ n hn).2.2.2.1).prod_inl (𝓝 x)
    · exact hρ.tendsto_support.comp tendsto_fst
    · exact Eventually.of_forall fun _ => hf.aestronglyMeasurable
    · exact hf.continuousAt.tendsto.comp tendsto_snd
  exact (h1.prodMk_nhds h2).mono_right (nhds_le_uniformity _)

/-- **Theorem 4.22** of [brezis2011functional]. Let $(\rho_n)$ be a sequence of mollifiers, let
$1 \le p < \infty$ and let $f \in L^p(\mathbb{R}^N)$. Then $\rho_n \star f \to f$ in
$L^p(\mathbb{R}^N)$, that is, $\|\rho_n \star f - f\|_p \to 0$.

The proof is the backbone's `MeasureTheory.tendsto_eLpNorm_convolution_sub`, which uses the
continuity of translation in $L^p$, not the density argument of the source. -/
theorem theorem_4_22 {ρ : ℕ → 𝔼 → ℝ} (hρ : IsMollifierSeq ρ) {p : ENNReal} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) {f : 𝔼 → ℝ} (hf : MemLp f p volume) :
    Tendsto (fun n => eLpNorm (ρ n ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] f - f) p volume) atTop
      (𝓝 0) := by
  rw [← lsmul_eq_mul_real]
  refine tendsto_eLpNorm_convolution_sub ?_ ?_ ?_ hρ.tendsto_support Fact.out hp hf
  · exact (eventually_ge_atTop 1).mono fun n hn => (hρ n hn).2.2.2.2
  · exact (eventually_ge_atTop 1).mono fun n hn =>
      (hρ n hn).1.continuous.integrable_of_hasCompactSupport (hρ n hn).2.1
  · exact (eventually_ge_atTop 1).mono fun n hn => (hρ n hn).2.2.2.1

/-- **Corollary 4.23** of [brezis2011functional]. Let $\Omega \subseteq \mathbb{R}^N$ be open and
$1 \le p < \infty$. Then $C_c^\infty(\Omega)$ is dense in $L^p(\Omega)$: the classes of smooth
functions with compact support in $\Omega$ form a dense subset of $L^p(\Omega)$.

The space $L^p(\Omega)$ is `Lp ℝ p (volume.restrict Ω)`. -/
theorem corollary_4_23 {Ω : Set 𝔼} (hΩ : IsOpen Ω) {p : ENNReal} [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    Dense {g : Lp ℝ p (volume.restrict Ω) | ∃ φ : 𝔼 → ℝ, ⇑g =ᵐ[volume.restrict Ω] φ ∧
      HasCompactSupport φ ∧ ContDiff ℝ ∞ φ ∧ tsupport φ ⊆ Ω} :=
  Lp.dense_contDiff_tsupport_subset hΩ hp

/-- **Corollary 4.24** of [brezis2011functional]. Let $\Omega \subseteq \mathbb{R}^N$ be open and
let $u \in L^1_{loc}(\Omega)$ be such that
$$\int u f = 0 \quad \text{for all } f \in C_c^\infty(\Omega).$$
Then $u = 0$ a.e. on $\Omega$.

The proof is Mathlib's `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`. -/
theorem corollary_4_24 {Ω : Set 𝔼} (hΩ : IsOpen Ω) {u : 𝔼 → ℝ} (hu : MemLpLoc u 1 Ω)
    (h : ∀ f : 𝔼 → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ Ω →
      ∫ x, u x * f x = 0) :
    ∀ᵐ x ∂(volume : Measure 𝔼), x ∈ Ω → u x = 0 :=
  hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((memLpLoc_one_iff_locallyIntegrableOn hΩ).1 hu) fun f hf hfs hfΩ => by
      simpa only [smul_eq_mul, mul_comm] using h f hf hfs hfΩ

/-- **Theorem 4.33** of [brezis2011functional] (Young's inequality, general form). Let
$f \in L^p(\mathbb{R}^N)$ and $g \in L^q(\mathbb{R}^N)$ with $1 \le p, q \le \infty$, and let
$r$ satisfy
$$\frac1r = \frac1p + \frac1q - 1 \ge 0.$$
Then $f \star g \in L^r(\mathbb{R}^N)$ and $\|f \star g\|_r \le \|f\|_p \|g\|_q$.

The source states this theorem in the Comments on Chapter 4. The condition on $r$ is written
$1/p + 1/q = 1 + 1/r$ in $[0, +\infty]$, which also requires $1/p + 1/q \ge 1$. -/
theorem theorem_4_33 {p q r : ENNReal} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpqr : 1 / p + 1 / q = 1 + 1 / r) {f g : 𝔼 → ℝ} (hf : MemLp f p volume)
    (hg : MemLp g q volume) :
    MemLp (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) r volume ∧
    eLpNorm (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) r volume ≤
      eLpNorm f p volume * eLpNorm g q volume := by
  have h : eLpNorm (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) r volume ≤
      eLpNorm f p volume * eLpNorm g q volume := by
    refine (eLpNorm_convolution_le_of_inv_add_inv (L := ContinuousLinearMap.mul ℝ ℝ) Fact.out
      Fact.out hpqr hf.aestronglyMeasurable hg.aestronglyMeasurable).trans ?_
    rw [mul_assoc]
    exact mul_le_of_le_one_left bot_le enorm_mul_real_le_one
  exact ⟨memLp_iff.2 (h.trans_lt (ENNReal.mul_lt_top hf.eLpNorm_lt_top hg.eLpNorm_lt_top)), h⟩

end Brezis.Chapter04
