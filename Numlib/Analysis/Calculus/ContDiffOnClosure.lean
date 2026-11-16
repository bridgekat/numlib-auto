/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Calculus.ContDiff.Defs`, beside `ContDiffOn`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Numlib.Analysis.Calculus.AddTorsor.AffineMap

/-!
# Functions of class $C^n$ up to the boundary

Let $X$ and $F$ be normed spaces over a nontrivially normed field $\mathbb{K}$, and let
$s \subseteq X$. A function $f : X \to F$ is of **class $C^n(\bar s)$** if $f$ is $C^n$ on $s$ and
each derivative $D^m f$ of order $m \le n$ has a continuous extension from $s$ to the closure
$\bar s$. This is the class $C^n(\bar\Omega)$ of the literature on partial differential equations,
as in [brezis2011functional], Chapter 9, footnote 16, where $s$ is open.

The class is weaker than Mathlib's `ContDiffOn 𝕜 n f (closure s)`, which asks at every boundary
point for a Taylor expansion within the closure. The two agree on regular domains, but the Mathlib
notion is the wrong hypothesis to write when a text says $u \in C^k(\bar\Omega)$. The implication
from the Mathlib notion holds for every open $s$, with no unique differentiability of the closure:
the continuous extension of $D^m f$ is built from the local Taylor data by limits along $s$. The
extension of each derivative is unique on $\bar s$, since $s$ is dense in $\bar s$
(`Set.EqOn.of_subset_closure`).

The class has two uses. With $s = \Omega$ a spatial domain, it states the conclusions
$u \in C^k(\bar\Omega)$ of the Sobolev embeddings and of elliptic regularity. With
$s = \Omega \times I$ for a time interval $I$, it states space–time classes such as
$C^\infty(\bar\Omega \times [\varepsilon, \infty))$ for evolution equations.

## Main definitions

* `ContDiffOnClosure`: the class $C^n(\bar s)$.

## Main results

* `ContDiffOnClosure.of_le`, `ContDiffOnClosure.mono`: the class is monotone in the order and in the
  set.
* `ContDiffOnClosure.continuousOn_closure`: a function of class $C^n(\bar s)$ extends continuously
  to $\bar s$.
* `ContDiffOn.contDiffOnClosure`: for open $s$, a function that is $C^n$ on $\bar s$ in Mathlib's
  sense is of class $C^n(\bar s)$.
* `contDiffOnClosure_one_iff`: $f \in C^1(\bar s)$ if and only if $f$ is $C^1$ on $s$ and both $f$
  and $Df$ extend continuously to $\bar s$. This is the working form of the class at order one, and
  the stability results below are proved through it.
* `ContDiffOnClosure.smul`, `ContDiffOnClosure.mul`, `ContDiffOnClosure.const`,
  `ContDiffOnClosure.smul_const`, `ContDiffOnClosure.continuousLinearMap_comp`,
  `ContDiffOnClosure.clm_comp_comp_affine`, `ContDiffOnClosure.comp_affineIsometryEquiv`: on an open
  set $s$, the class $C^1(\bar s)$ is stable under products, constants, continuous linear maps and
  affine changes of variables.
* `ContDiffOnClosure.congr_set_of_tsupport_subset`: the class $C^1(\bar s)$ is local on the support
  of the function.
* `ContDiffOnClosure.exists_norm_fderiv_le`,
  `ContDiffOnClosure.exists_norm_fderiv_le_of_hasCompactSupport`: the derivative of a function of
  class $C^1(\bar s)$ is bounded on $s$ if $s$ is bounded or if the function has compact support.
* `ContDiffOnClosure.exists_continuousOn_fderiv_fderiv`: the second derivative of a function of
  class $C^2(\bar s)$ extends continuously to $\bar s$.

## Implementation notes

* The field $\mathbb{K}$ is `𝕜`. The order $n$ is a term of `WithTop ℕ∞`. The derivative of order
  $m$ is `iteratedFDeriv 𝕜 m f`, a continuous $m$-linear map, and its extension is a function
  `X → X [×m]→L[𝕜] F` that is continuous on `closure s` and equal to `iteratedFDeriv 𝕜 m f` on `s`.
* The definition does not require $s$ to be open, but most results assume it.
-/

open Filter Set Topology

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {X F : Type*} [NormedAddCommGroup X]
  [NormedSpace 𝕜 X] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Let $X$ and $F$ be normed spaces over $\mathbb{K}$, let
$n \in \mathbb{N} \cup \{\infty, \omega\}$, and let $s \subseteq X$. A function $f : X \to F$ is
of **class $C^n(\bar s)$** if $f$ is $C^n$ on $s$ and, for every natural number $m \le n$, there
is a function $g$ that is continuous on the closure $\bar s$ and equal to $D^m f$ on $s$.

This is the class of [brezis2011functional], Chapter 9, footnote 16, which is meant for an open
set $s$. The derivative $D^m f$ is `iteratedFDeriv 𝕜 m f`, and "$C^n$ on $s$" is
`ContDiffOn 𝕜 n f s`. -/
def ContDiffOnClosure (n : WithTop ℕ∞) (f : X → F) (s : Set X) : Prop :=
  ContDiffOn 𝕜 n f s ∧ ∀ m : ℕ, (m : WithTop ℕ∞) ≤ n →
    ∃ g : X → X [×m]→L[𝕜] F, ContinuousOn g (closure s) ∧ EqOn g (iteratedFDeriv 𝕜 m f) s

variable {𝕜} {n : WithTop ℕ∞} {f : X → F} {s : Set X}

namespace ContDiffOnClosure

/-- A function of class $C^n(\bar s)$ is $C^n$ on $s$. -/
theorem contDiffOn (h : ContDiffOnClosure 𝕜 n f s) : ContDiffOn 𝕜 n f s := h.1

/-- Let $f$ be of class $C^n(\bar s)$, and let $m \le n$ be a natural number. Then there is a
function $g$ that is continuous on $\bar s$ and equal to $D^m f$ on $s$. -/
theorem exists_continuousOn_closure_iteratedFDeriv (h : ContDiffOnClosure 𝕜 n f s) {m : ℕ}
    (hm : (m : WithTop ℕ∞) ≤ n) :
    ∃ g : X → X [×m]→L[𝕜] F, ContinuousOn g (closure s) ∧ EqOn g (iteratedFDeriv 𝕜 m f) s :=
  h.2 m hm

/-- Let $m \le n$. A function of class $C^n(\bar s)$ is of class $C^m(\bar s)$. -/
theorem of_le {m : WithTop ℕ∞} (h : ContDiffOnClosure 𝕜 n f s) (hmn : m ≤ n) :
    ContDiffOnClosure 𝕜 m f s :=
  ⟨h.1.of_le hmn, fun k hk ↦ h.2 k (hk.trans hmn)⟩

/-- Let $s' \subseteq s$. A function of class $C^n(\bar s)$ is of class $C^n(\bar s')$: the
extensions restrict, since $\bar s' \subseteq \bar s$.

This is how $C^\infty(\bar\Omega \times (0, \infty))$ gives $C^\infty(\bar\Omega \times
[\varepsilon, \infty))$ for every $\varepsilon > 0$. -/
theorem mono {s' : Set X} (h : ContDiffOnClosure 𝕜 n f s) (hs : s' ⊆ s) :
    ContDiffOnClosure 𝕜 n f s' :=
  ⟨h.1.mono hs, fun m hm ↦
    let ⟨g, hgc, hge⟩ := h.2 m hm
    ⟨g, hgc.mono (closure_mono hs), hge.mono hs⟩⟩

/-- A function $f$ of class $C^n(\bar s)$ extends continuously to $\bar s$: there is a function $g$
that is continuous on $\bar s$ and equal to $f$ on $s$. -/
theorem continuousOn_closure (h : ContDiffOnClosure 𝕜 n f s) :
    ∃ g : X → F, ContinuousOn g (closure s) ∧ EqOn g f s := by
  obtain ⟨g₀, hgc, hge⟩ := h.2 0 (by simp)
  refine ⟨fun x ↦ continuousMultilinearCurryFin0 𝕜 X F (g₀ x),
    (continuousMultilinearCurryFin0 𝕜 X F).continuous.comp_continuousOn hgc, fun x hx ↦ ?_⟩
  change continuousMultilinearCurryFin0 𝕜 X F (g₀ x) = f x
  rw [hge hx, iteratedFDeriv_zero_eq_comp, Function.comp_apply]
  exact (continuousMultilinearCurryFin0 𝕜 X F).apply_symm_apply (f x)

end ContDiffOnClosure

/-- Let $s \subseteq X$ be open, and let $f$ be $C^n$ on the closure $\bar s$ in the sense of
`ContDiffOn`. Then $f$ is of class $C^n(\bar s)$. No unique differentiability of $\bar s$ is
assumed.

The extension of $D^m f$ is $y \mapsto \lim_{z \to y,\, z \in s} D^m f(z)$. Near each point of
$\bar s$, the Taylor data of `ContDiffWithinAt` give a continuous function that agrees with
$D^m f$ on $s$, so the limit exists and is continuous. -/
theorem ContDiffOn.contDiffOnClosure (hs : IsOpen s) (h : ContDiffOn 𝕜 n f (closure s)) :
    ContDiffOnClosure 𝕜 n f s := by
  refine ⟨h.mono subset_closure, fun m hm ↦ ?_⟩
  -- local continuous extensions of `D^m f`, from the Taylor data
  have key : ∀ x ∈ closure s, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ g : X → X [×m]→L[𝕜] F,
      ContinuousOn g (closure s ∩ V) ∧ EqOn g (iteratedFDeriv 𝕜 m f) (s ∩ V) := by
    intro x hx
    obtain ⟨u, hu, p, hp⟩ := contDiffWithinAt_nat.1 ((h x hx).of_le hm)
    rw [insert_eq_of_mem hx] at hu
    obtain ⟨V, hVo, hxV, hVu⟩ := mem_nhdsWithin.1 hu
    refine ⟨V, hVo, hxV, fun y ↦ p y m, (hp.cont m le_rfl).mono fun y hy ↦ hVu ⟨hy.2, hy.1⟩,
      fun y hy ↦ ?_⟩
    have hsub : s ∩ V ⊆ u := fun z hz ↦ hVu ⟨hz.2, subset_closure hz.1⟩
    change p y m = iteratedFDeriv 𝕜 m f y
    rw [(hp.mono hsub).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl (hs.inter hVo).uniqueDiffOn
      hy, iteratedFDerivWithin_of_isOpen m (hs.inter hVo) hy]
  choose! V hVo hxV g hgc hge using key
  -- the global extension, as a limit along `s`
  set G : X → X [×m]→L[𝕜] F := fun y ↦ limUnder (𝓝[s] y) (iteratedFDeriv 𝕜 m f) with hGdef
  have hG : ∀ x ∈ closure s, EqOn G (g x) (closure s ∩ V x) := by
    intro x hx y hy
    have hne : (𝓝[s] y).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hy.1
    have h1 : Tendsto (g x) (𝓝[closure s ∩ V x] y) (𝓝 (g x y)) :=
      (hgc x hx).continuousWithinAt hy
    have h2 : 𝓝[s] y ≤ 𝓝[closure s ∩ V x] y :=
      nhdsWithin_le_of_mem (mem_nhdsWithin.2
        ⟨V x, hVo x hx, hy.2, fun z hz ↦ ⟨subset_closure hz.2, hz.1⟩⟩)
    have h3 : g x =ᶠ[𝓝[s] y] iteratedFDeriv 𝕜 m f := by
      filter_upwards [inter_mem_nhdsWithin s ((hVo x hx).mem_nhds hy.2)] with z hz
      exact hge x hx hz
    exact ((h1.mono_left h2).congr' h3).limUnder_eq
  refine ⟨G, fun y hy ↦ ?_, fun y hy ↦ ?_⟩
  · have hmem : V y ∈ 𝓝[closure s] y :=
      mem_nhdsWithin_of_mem_nhds ((hVo y hy).mem_nhds (hxV y hy))
    refine (continuousWithinAt_inter' hmem).1 ?_
    exact ((hgc y hy).continuousWithinAt ⟨hy, hxV y hy⟩).congr (fun z hz ↦ hG y hy hz)
      (hG y hy ⟨hy, hxV y hy⟩)
  · have hy' : y ∈ closure s := subset_closure hy
    rw [hG y hy' ⟨hy', hxV y hy'⟩, hge y hy' ⟨hy, hxV y hy'⟩]

/-! ### The class $C^1(\bar s)$ through the derivative -/

section One

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- For $f : X \to F$ and $x \in X$, the first derivative tensor $D^1 f(x)$ is the derivative
$Df(x)$, read through the identification of $1$-linear maps with linear maps.

The identification is `continuousMultilinearCurryFin1`. The real case is
`iteratedFDeriv_one_eq_symm_fderiv` of `Numlib.Analysis.Sobolev.Friedrichs`. -/
theorem iteratedFDeriv_one_eq_symm_fderiv' (f : X → F) (x : X) :
    iteratedFDeriv 𝕜 1 f x = (continuousMultilinearCurryFin1 𝕜 X F).symm (fderiv 𝕜 f x) :=
  ContinuousMultilinearMap.ext fun m ↦ by simp

/-- A function $f$ is of class $C^1(\bar s)$ if and only if $f$ is $C^1$ on $s$, there is a function
that is continuous on $\bar s$ and equal to $f$ on $s$, and there is a function that is
continuous on $\bar s$ and equal to the derivative $Df$ on $s$.

The derivative is `fderiv 𝕜 f`. -/
theorem contDiffOnClosure_one_iff :
    ContDiffOnClosure 𝕜 1 f s ↔ ContDiffOn 𝕜 1 f s ∧
      (∃ g : X → F, ContinuousOn g (closure s) ∧ EqOn g f s) ∧
      ∃ g' : X → X →L[𝕜] F, ContinuousOn g' (closure s) ∧ EqOn g' (fderiv 𝕜 f) s := by
  constructor
  · intro h
    refine ⟨h.1, h.continuousOn_closure, ?_⟩
    obtain ⟨g, hgc, hge⟩ := h.2 1 le_rfl
    refine ⟨fun x ↦ continuousMultilinearCurryFin1 𝕜 X F (g x),
      (continuousMultilinearCurryFin1 𝕜 X F).continuous.comp_continuousOn hgc, fun x hx ↦ ?_⟩
    change continuousMultilinearCurryFin1 𝕜 X F (g x) = fderiv 𝕜 f x
    rw [hge hx, iteratedFDeriv_one_eq_symm_fderiv', LinearIsometryEquiv.apply_symm_apply]
  · rintro ⟨h, ⟨g, hgc, hge⟩, ⟨g', hgc', hge'⟩⟩
    refine ⟨h, fun m hm ↦ ?_⟩
    have hm' : m ≤ 1 := by exact_mod_cast hm
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hm' with rfl | rfl
    · refine ⟨fun x ↦ (continuousMultilinearCurryFin0 𝕜 X F).symm (g x),
        (continuousMultilinearCurryFin0 𝕜 X F).symm.continuous.comp_continuousOn hgc,
        fun x hx ↦ ?_⟩
      change (continuousMultilinearCurryFin0 𝕜 X F).symm (g x) = iteratedFDeriv 𝕜 0 f x
      rw [hge hx, iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    · refine ⟨fun x ↦ (continuousMultilinearCurryFin1 𝕜 X F).symm (g' x),
        (continuousMultilinearCurryFin1 𝕜 X F).symm.continuous.comp_continuousOn hgc',
        fun x hx ↦ ?_⟩
      change (continuousMultilinearCurryFin1 𝕜 X F).symm (g' x) = iteratedFDeriv 𝕜 1 f x
      rw [hge' hx, iteratedFDeriv_one_eq_symm_fderiv']

/-- Let $f$ be of class $C^2(\bar s)$. Then the second derivative $D(Df)$ has a continuous extension
from $s$ to $\bar s$.

The second derivative is `fderiv 𝕜 (fderiv 𝕜 f)`, with values in `X →L[𝕜] X →L[𝕜] F`. -/
theorem ContDiffOnClosure.exists_continuousOn_fderiv_fderiv (h : ContDiffOnClosure 𝕜 2 f s) :
    ∃ G : X → X →L[𝕜] X →L[𝕜] F, ContinuousOn G (closure s) ∧
      EqOn G (fderiv 𝕜 (fderiv 𝕜 f)) s := by
  obtain ⟨g₂, hc, he⟩ := h.2 2 le_rfl
  let C : (X [×1]→L[𝕜] F) →L[𝕜] (X →L[𝕜] F) :=
    (continuousMultilinearCurryFin1 𝕜 X F : (X [×1]→L[𝕜] F) →L[𝕜] (X →L[𝕜] F))
  let L : (X [×2]→L[𝕜] F) →L[𝕜] (X →L[𝕜] X [×1]→L[𝕜] F) :=
    (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin 2 ↦ X) F :
      (X [×2]→L[𝕜] F) →L[𝕜] (X →L[𝕜] X [×1]→L[𝕜] F))
  refine ⟨fun x ↦ ContinuousLinearMap.compL 𝕜 X (X [×1]→L[𝕜] F) (X →L[𝕜] F) C (L (g₂ x)), ?_,
    fun x hx ↦ ?_⟩
  · exact ((ContinuousLinearMap.compL 𝕜 X (X [×1]→L[𝕜] F) (X →L[𝕜] F) C).continuous.comp
      L.continuous).comp_continuousOn hc
  · ext w v
    simp only [ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply, he hx]
    change continuousMultilinearCurryFin1 𝕜 X F
      (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin 2 ↦ X) F (iteratedFDeriv 𝕜 2 f x) w) v
      = _
    rw [continuousMultilinearCurryFin1_apply, continuousMultilinearCurryLeftEquiv_apply,
      iteratedFDeriv_two_apply]
    simp

namespace ContDiffOnClosure

/-- Let $s$ be open, let $u : X \to \mathbb{K}$ and $v : X \to F$ be of class $C^1(\bar s)$. Then
$x \mapsto u(x) v(x)$ is of class $C^1(\bar s)$.

On $s$, $D(uv) = u\, Dv + (Du)\, v$, and the continuous extensions of $u$, $v$, $Du$ and $Dv$ to
$\bar s$ combine to an extension of $D(uv)$. -/
theorem smul (hs : IsOpen s) {u : X → 𝕜} {v : X → F} (hu : ContDiffOnClosure 𝕜 1 u s)
    (hv : ContDiffOnClosure 𝕜 1 v s) : ContDiffOnClosure 𝕜 1 (fun x ↦ u x • v x) s := by
  rw [contDiffOnClosure_one_iff] at hu hv ⊢
  obtain ⟨hu, ⟨u₁, hu₁c, hu₁e⟩, ⟨u₁', hu₁c', hu₁e'⟩⟩ := hu
  obtain ⟨hv, ⟨v₁, hv₁c, hv₁e⟩, ⟨v₁', hv₁c', hv₁e'⟩⟩ := hv
  refine ⟨hu.smul hv, ⟨fun x ↦ u₁ x • v₁ x, hu₁c.smul hv₁c, fun x hx ↦ by
    simp only [hu₁e hx, hv₁e hx]⟩,
    ⟨fun x ↦ u₁ x • v₁' x + (u₁' x).smulRight (v₁ x), ?_, fun x hx ↦ ?_⟩⟩
  · refine (hu₁c.smul hv₁c').add ?_
    exact (ContinuousLinearMap.smulRightL 𝕜 X F).continuous₂.comp_continuousOn
      (hu₁c'.prodMk hv₁c)
  · have hux : DifferentiableAt 𝕜 u x :=
      (hu.differentiableOn one_ne_zero).differentiableAt (hs.mem_nhds hx)
    have hvx : DifferentiableAt 𝕜 v x :=
      (hv.differentiableOn one_ne_zero).differentiableAt (hs.mem_nhds hx)
    simp only [hu₁e hx, hv₁e hx, hu₁e' hx, hv₁e' hx]
    exact (fderiv_fun_smul hux hvx).symm

/-- Let $s$ be open, and let $u, v : X \to \mathbb{K}$ be of class $C^1(\bar s)$. Then $uv$ is of
class $C^1(\bar s)$. -/
theorem mul (hs : IsOpen s) {u v : X → 𝕜} (hu : ContDiffOnClosure 𝕜 1 u s)
    (hv : ContDiffOnClosure 𝕜 1 v s) : ContDiffOnClosure 𝕜 1 (fun x ↦ u x * v x) s :=
  hu.smul hs hv

/-- For every $c \in F$, the constant function $c$ is of class $C^1(\bar s)$, for every set $s$. -/
theorem const (c : F) : ContDiffOnClosure 𝕜 1 (fun _ : X ↦ c) s := by
  rw [contDiffOnClosure_one_iff]
  exact ⟨contDiffOn_const, ⟨fun _ ↦ c, continuousOn_const, fun _ _ ↦ rfl⟩,
    ⟨fun _ ↦ 0, continuousOn_const, fun x _ ↦ (fderiv_const_apply c).symm⟩⟩

/-- Let $s$ be open, let $u : X \to \mathbb{K}$ be of class $C^1(\bar s)$, and let $c \in F$. Then
$x \mapsto u(x) c$ is of class $C^1(\bar s)$. -/
theorem smul_const (hs : IsOpen s) {u : X → 𝕜} (hu : ContDiffOnClosure 𝕜 1 u s) (c : F) :
    ContDiffOnClosure 𝕜 1 (fun x ↦ u x • c) s :=
  hu.smul hs (const c)

/-- Let $X$ be a proper space, let $s$ be bounded, and let $f$ be of class $C^1(\bar s)$. Then the
derivative of $f$ is bounded on $s$: there is $C$ with $\|Df(x)\| \le C$ for all $x \in s$.

The continuous extension of $Df$ is bounded on the compact set $\bar s$. -/
theorem exists_norm_fderiv_le [ProperSpace X] (hf : ContDiffOnClosure 𝕜 1 f s)
    (hs : Bornology.IsBounded s) : ∃ C, ∀ x ∈ s, ‖fderiv 𝕜 f x‖ ≤ C := by
  obtain ⟨-, -, g', hg'c, hg'e⟩ := contDiffOnClosure_one_iff.1 hf
  obtain ⟨C, hC⟩ := hs.isCompact_closure.exists_bound_of_continuousOn hg'c
  exact ⟨C, fun x hx ↦ by rw [← hg'e hx]; exact hC x (subset_closure hx)⟩

/-- Let $f$ be of class $C^1(\bar s)$ with compact support. Then the derivative of $f$ is bounded on
$s$: there is $M$ with $\|Df(x)\| \le M$ for all $x \in s$.

The continuous extension of $Df$ is bounded on the compact set
$\bar s \cap \operatorname{tsupport} f$, and $Df = 0$ off the closed support
$\operatorname{tsupport} f$. Compare `ContDiffOn.exists_norm_fderiv_le_of_isCompact` of
`Numlib.Analysis.Sobolev.Chart`, which bounds the derivative on the interior of a compact set,
and `ContDiffOnClosure.exists_norm_fderiv_le`, which assumes instead that $s$ is bounded. -/
theorem exists_norm_fderiv_le_of_hasCompactSupport (hf : ContDiffOnClosure 𝕜 1 f s)
    (hfc : HasCompactSupport f) : ∃ M, ∀ x ∈ s, ‖fderiv 𝕜 f x‖ ≤ M := by
  obtain ⟨-, -, G, hGc, hGe⟩ := contDiffOnClosure_one_iff.1 hf
  obtain ⟨C, hC⟩ := (hfc.inter_left isClosed_closure).exists_bound_of_continuousOn
    (hGc.mono inter_subset_left)
  refine ⟨max C 0, fun x hx ↦ ?_⟩
  by_cases hxs : x ∈ tsupport f
  · rw [← hGe hx]
    exact (hC x ⟨subset_closure hx, hxs⟩).trans (le_max_left _ _)
  · rw [fderiv_of_notMem_tsupport 𝕜 hxs, norm_zero]
    exact le_max_right _ _

/-- Let $s$ be open, let $f : X \to F$ be of class $C^1(\bar s)$, and let $L : F \to G$ be a
continuous linear map. Then $x \mapsto L(f(x))$ is of class $C^1(\bar s)$: the extensions of $f$
and $Df$ compose with $L$. -/
theorem continuousLinearMap_comp (hs : IsOpen s) (hf : ContDiffOnClosure 𝕜 1 f s) (L : F →L[𝕜] G) :
    ContDiffOnClosure 𝕜 1 (fun x ↦ L (f x)) s := by
  rw [contDiffOnClosure_one_iff] at hf ⊢
  obtain ⟨hf, ⟨g₀, hg₀c, hg₀e⟩, ⟨g₁, hg₁c, hg₁e⟩⟩ := hf
  refine ⟨hf.continuousLinearMap_comp L, ⟨fun x ↦ L (g₀ x), L.continuous.comp_continuousOn hg₀c,
    fun x hx ↦ by simp only [hg₀e hx]⟩, ⟨fun x ↦ L.comp (g₁ x), continuousOn_const.clm_comp hg₁c,
    fun x hx ↦ ?_⟩⟩
  have hx' : DifferentiableAt 𝕜 f x :=
    (hf.differentiableOn one_ne_zero).differentiableAt (hs.mem_nhds hx)
  simp only [hg₁e hx]
  exact (L.hasFDerivAt.comp x hx'.hasFDerivAt).fderiv.symm

end ContDiffOnClosure

/-- Let $Y$ be a topological space, let $s, K \subseteq Y$ with $K$ closed, and let $\varphi$ be
continuous on $\bar s$ with $\varphi(y) = 0$ for every $y \in s \setminus K$. Then
$\varphi(y) = 0$ for every $y \in \bar s \setminus K$, because $\bar s \setminus K$ lies in the
closure of $s \setminus K$. -/
theorem ContinuousOn.eq_zero_of_notMem_of_forall {Y : Type*} [TopologicalSpace Y] {φ : Y → G}
    {s K : Set Y} (hφ : ContinuousOn φ (closure s)) (hK : IsClosed K)
    (h : ∀ y ∈ s, y ∉ K → φ y = 0) {y : Y} (hy : y ∈ closure s) (hyK : y ∉ K) : φ y = 0 := by
  have hsub : closure s ∩ Kᶜ ⊆ closure (s ∩ Kᶜ) := fun z hz ↦ by
    have := hK.isOpen_compl.inter_closure ⟨hz.2, hz.1⟩
    rwa [inter_comm] at this
  exact Set.EqOn.of_subset_closure (s := s ∩ Kᶜ) (t := closure s ∩ Kᶜ) (f := φ) (g := 0)
    (fun z hz ↦ h z hz.1 hz.2) (hφ.mono inter_subset_left) continuousOn_const
    (inter_subset_inter_left _ subset_closure) hsub ⟨hy, hyK⟩

/-- Let $Y$ be a topological space, let $V \subseteq Y$ be open, let $s, s' \subseteq Y$ with
$s \cap V = s' \cap V$, and let $f : Y \to F$ have its closed support
$\operatorname{tsupport} f$ in $V$. Let $\varphi$ be continuous on $\bar s$ with $\varphi = 0$
on $s \setminus \operatorname{tsupport} f$. Then the function equal to $\varphi$ on
$\operatorname{tsupport} f$ and to $0$ elsewhere is continuous on $\bar s'$.

Near a point of $V$, $\bar s' \cap V \subseteq \bar s$, and $\varphi$ serves. Away from $V$ the
function vanishes on a neighbourhood. This gives the continuity clauses of
`ContDiffOnClosure.congr_set_of_tsupport_subset`. -/
theorem ContinuousOn.indicator_tsupport_of_inter_eq {Y : Type*} [TopologicalSpace Y]
    {f : Y → F} {s s' V : Set Y} (hV : IsOpen V) (hsV : s ∩ V = s' ∩ V) (hsupp : tsupport f ⊆ V)
    {φ : Y → G} (hφ : ContinuousOn φ (closure s)) (hφ0 : ∀ x ∈ s, x ∉ tsupport f → φ x = 0) :
    ContinuousOn ((tsupport f).indicator φ) (closure s') := by
  -- `closure s' ∩ V ⊆ closure s`, and `closure s` is a neighbourhood within `closure s'` there
  have hcl : closure s' ∩ V ⊆ closure s := fun x hx ↦ by
    have h1 : x ∈ closure (s' ∩ V) := by
      have := hV.inter_closure ⟨hx.2, hx.1⟩
      rwa [inter_comm] at this
    rw [← hsV] at h1
    exact closure_mono inter_subset_left h1
  have hnhds : ∀ x ∈ closure s', x ∈ V → closure s ∈ 𝓝[closure s'] x := fun x hx hxV ↦
    mem_nhdsWithin.2 ⟨V, hV, hxV, fun z hz ↦ hcl ⟨hz.2, hz.1⟩⟩
  intro x hx
  have heq : ∀ z ∈ closure s, (tsupport f).indicator φ z = φ z := fun z hz ↦ by
    by_cases hzK : z ∈ tsupport f
    · exact indicator_of_mem hzK _
    · rw [indicator_of_notMem hzK,
        hφ.eq_zero_of_notMem_of_forall (isClosed_tsupport f) hφ0 hz hzK]
  by_cases hxV : x ∈ V
  · have h1 : ContinuousWithinAt φ (closure s') x :=
      (hφ x (hcl ⟨hx, hxV⟩)).mono_of_mem_nhdsWithin (hnhds x hx hxV)
    refine h1.congr_of_eventuallyEq ?_ (heq x (hcl ⟨hx, hxV⟩))
    filter_upwards [hnhds x hx hxV] with z hz using heq z hz
  · have hxs : x ∉ tsupport f := fun h ↦ hxV (hsupp h)
    have hev : (tsupport f).indicator φ =ᶠ[𝓝 x] fun _ ↦ 0 := by
      filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hxs] with z hz
      exact indicator_of_notMem hz _
    exact (continuousAt_const.congr hev.symm).continuousWithinAt

/-- The class $C^1(\bar s)$ is **local on the support**. Let $s$ and $V$ be open, let $s'$ be a set
with $s \cap V = s' \cap V$, and let $f$ have its closed support $\operatorname{tsupport} f$ in
$V$. If $f$ is continuous on $\bar s$ and of class $C^1(\bar s)$, then $f$ is continuous on
$\bar s'$ and of class $C^1(\bar s')$.

Near a point of $V$, $\bar s' \cap V \subseteq \overline{s \cap V}$, and the data of $f$ on
$\bar s$ serve. Away from $V$ the function vanishes on a neighbourhood. The extension of $Df$ to
$\bar s'$ is the given extension times the indicator of $\operatorname{tsupport} f$; it vanishes
on $\bar s \setminus \operatorname{tsupport} f$ by `ContinuousOn.eq_zero_of_notMem_of_forall`
and `ContinuousOn.indicator_tsupport_of_inter_eq`. This result moves a field supported in a
chart ball from $\Omega$ to the global rotated epigraph. -/
theorem ContDiffOnClosure.congr_set_of_tsupport_subset {s' V : Set X} (hs : IsOpen s)
    (hV : IsOpen V) (hsV : s ∩ V = s' ∩ V) (hsupp : tsupport f ⊆ V)
    (hf₀ : ContinuousOn f (closure s)) (hf₁ : ContDiffOnClosure 𝕜 1 f s) :
    ContinuousOn f (closure s') ∧ ContDiffOnClosure 𝕜 1 f s' := by
  have hmem : ∀ x ∈ s', x ∈ V → x ∈ s := fun x hx hxV ↦ by
    have : x ∈ s' ∩ V := ⟨hx, hxV⟩
    rw [← hsV] at this
    exact this.1
  have hcontf : ContinuousOn f (closure s') := by
    have := hf₀.indicator_tsupport_of_inter_eq hV hsV hsupp
      fun x _ hx ↦ image_eq_zero_of_notMem_tsupport (f := f) hx
    rwa [Set.indicator_eq_self.2 (subset_tsupport f)] at this
  refine ⟨hcontf, ?_⟩
  rw [contDiffOnClosure_one_iff] at hf₁ ⊢
  obtain ⟨hf, -, ⟨g₁, hg₁c, hg₁e⟩⟩ := hf₁
  refine ⟨fun x hx ↦ ?_, ⟨f, hcontf, fun _ _ ↦ rfl⟩, ⟨(tsupport f).indicator g₁,
    hg₁c.indicator_tsupport_of_inter_eq hV hsV hsupp fun x hx hxK ↦ ?_, fun x hx ↦ ?_⟩⟩
  · by_cases hxV : x ∈ V
    · exact (hf.contDiffAt (hs.mem_nhds (hmem x hx hxV))).contDiffWithinAt
    · have hxs : x ∉ tsupport f := fun h ↦ hxV (hsupp h)
      exact (contDiffAt_const.congr_of_eventuallyEq
        (notMem_tsupport_iff_eventuallyEq.1 hxs)).contDiffWithinAt
  · rw [hg₁e hx]
    exact fderiv_of_notMem_tsupport 𝕜 hxK
  · by_cases hxK : x ∈ tsupport f
    · rw [indicator_of_mem hxK, hg₁e (hmem x hx (hsupp hxK))]
    · rw [indicator_of_notMem hxK, fderiv_of_notMem_tsupport 𝕜 hxK]

/-- Let $s \subseteq X$ be open, let $f : X \to F$ be of class $C^1(\bar s)$, let $L : F \to G$ be a
continuous linear map, let $M : Y \to X$ be a continuous linear equivalence, and let $b \in X$.
Then $y \mapsto L(f(My + b))$ is of class $C^1$ up to the boundary on the preimage of $s$ under
$y \mapsto My + b$. -/
theorem ContDiffOnClosure.clm_comp_comp_affine {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace 𝕜 Y] (hs : IsOpen s) (hf : ContDiffOnClosure 𝕜 1 f s) (L : F →L[𝕜] G)
    (M : Y ≃L[𝕜] X) (b : X) :
    ContDiffOnClosure 𝕜 1 (fun y ↦ L (f (M y + b))) ((fun y ↦ M y + b) ⁻¹' s) := by
  obtain ⟨hcd, ⟨g, hgc, hge⟩, ⟨g', hg'c, hg'e⟩⟩ := contDiffOnClosure_one_iff.1 hf
  have hΦ : Continuous fun y ↦ M y + b := M.continuous.add continuous_const
  have hΦh : (fun y ↦ M y + b) = M.toHomeomorph.trans (Homeomorph.addRight b) := by
    funext y; rfl
  have hcl : closure ((fun y ↦ M y + b) ⁻¹' s) = (fun y ↦ M y + b) ⁻¹' closure s := by
    rw [hΦh, Homeomorph.preimage_closure]
  refine contDiffOnClosure_one_iff.2 ⟨?_, ⟨fun y ↦ L (g (M y + b)), ?_, fun y hy ↦ ?_⟩,
    ⟨fun y ↦ (L.comp (g' (M y + b))).comp (M : Y →L[𝕜] X), ?_, fun y hy ↦ ?_⟩⟩
  · exact L.contDiff.comp_contDiffOn
      (hcd.comp (M.contDiff.add contDiff_const).contDiffOn (mapsTo_preimage _ _))
  · rw [hcl]
    exact L.continuous.comp_continuousOn (hgc.comp hΦ.continuousOn (mapsTo_preimage _ _))
  · simp only [hge hy]
  · rw [hcl]
    exact (continuousOn_const.clm_comp (hg'c.comp hΦ.continuousOn
      (mapsTo_preimage _ _))).clm_comp continuousOn_const
  · have hd : DifferentiableAt 𝕜 f (M y + b) :=
      (hcd.differentiableOn one_ne_zero).differentiableAt (hs.mem_nhds hy)
    simp only [hg'e hy]
    exact (L.hasFDerivAt.comp y (hd.hasFDerivAt.comp y (M.hasFDerivAt.add_const b))).fderiv.symm

end One

section Real

variable {E E' F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [NormedAddCommGroup F'] [NormedSpace ℝ F']

/-- Let $E$ be a proper real normed space, let $s \subseteq E$ be bounded, and let $f : E \to F'$ be
of class $C^1(\bar s)$. Then there is $M$ with $\|Df(x)\| \le M$ for all $x \in s$. This is the
real case of `ContDiffOnClosure.exists_norm_fderiv_le`. -/
theorem ContDiffOnClosure.exists_norm_fderiv_le_of_isBounded [ProperSpace E] {f : E → F'}
    {s : Set E} (hf : ContDiffOnClosure ℝ 1 f s) (hs : Bornology.IsBounded s) :
    ∃ M, ∀ x ∈ s, ‖fderiv ℝ f x‖ ≤ M :=
  hf.exists_norm_fderiv_le hs

/-- Let $s \subseteq E$ be open, let $f : E \to F'$ be of class $C^1(\bar s)$, and let
$T : E' \to E$ be an affine isometry equivalence of real normed spaces. Then $f \circ T$ is of
class $C^1$ up to the boundary on $T^{-1}(s)$.

The extensions compose with $T$, and the derivative with the linear part of $T$
(`AffineIsometryEquiv.hasFDerivAt`). -/
theorem ContDiffOnClosure.comp_affineIsometryEquiv {f : E → F'} {s : Set E} (hs : IsOpen s)
    (hf : ContDiffOnClosure ℝ 1 f s) (T : E' ≃ᵃⁱ[ℝ] E) :
    ContDiffOnClosure ℝ 1 (fun z ↦ f (T z)) (T ⁻¹' s) := by
  rw [contDiffOnClosure_one_iff] at hf ⊢
  obtain ⟨hf, ⟨g₀, hg₀c, hg₀e⟩, ⟨g₁, hg₁c, hg₁e⟩⟩ := hf
  have hcl : closure (T ⁻¹' s) = T ⁻¹' closure s := by
    have := T.toHomeomorph.preimage_closure s
    rwa [AffineIsometryEquiv.coe_toHomeomorph, eq_comm] at this
  have hTc : ContinuousOn T (closure (T ⁻¹' s)) := T.continuous.continuousOn
  have hmaps : MapsTo T (closure (T ⁻¹' s)) (closure s) := fun z hz ↦ by rwa [hcl] at hz
  have hT : ContDiff ℝ 1 T := T.toAffineIsometry.toContinuousAffineMap.contDiff
  refine ⟨hf.comp hT.contDiffOn (mapsTo_preimage T s), ⟨fun z ↦ g₀ (T z), hg₀c.comp hTc hmaps,
    fun z hz ↦ hg₀e hz⟩, ⟨fun z ↦ (g₁ (T z)).comp
      (T.linearIsometryEquiv.toContinuousLinearEquiv : E' →L[ℝ] E),
    (hg₁c.comp hTc hmaps).clm_comp continuousOn_const, fun z hz ↦ ?_⟩⟩
  have hd : DifferentiableAt ℝ f (T z) :=
    (hf.differentiableOn one_ne_zero).differentiableAt (hs.mem_nhds hz)
  simp only [hg₁e hz]
  exact (hd.hasFDerivAt.comp z (T.hasFDerivAt z)).fderiv.symm

end Real
