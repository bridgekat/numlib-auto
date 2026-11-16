/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Calculus.ContDiff.Basic` for the class and the induction,
`Mathlib.Analysis.Calculus.FDeriv.Partial` for the differentiability from partial derivatives.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Numlib.Analysis.Calculus.ContDiffOnClosure

/-!
# Smoothness on a space-time product from partial derivatives, up to the boundary

Let $E$ and $F$ be real normed spaces, let $\Omega \subseteq E$ be open, and let
$s \subseteq \mathbb{R}$. A function $f(x, t)$ of a space variable $x \in \Omega$ and a time
variable $t \in s$ is of class $C^k$ on $\Omega \times s$ as soon as its partial derivatives
$\partial_t^j D_x^i f$ with $i + j \le k$ exist and are jointly continuous. Mathlib proves the
differentiability of a function of two variables from partial derivatives that are continuous at a
point of an open set (`hasStrictFDerivAt_uncurry_coprod`). This module extends that statement in
three ways: to a set $\Omega \times s$ that need not be open in the time direction (for example
$s = [0, \infty)$), to every order, and with derivatives that extend continuously to a larger set.
The last class is the class $C^k(\bar\Omega \times s)$ in which the evolution equations of
[brezis2011functional], chapter 10, state their regularity, as in Theorem 10.1 (5); the class
$C^k(\bar\Omega)$ is defined in chapter 9, footnote 16.

The class `ContDiffOnExtendsTo 𝕜 n f s t` says that $f$ is $C^n$ on $s$ and that, for every
$m \le n$, the $m$-th derivative of $f$ within $s$ agrees on $s$ with a function that is continuous
on $t$. For an open $s$ and $t = \bar s$ it is the class $C^n(\bar s)$ of `ContDiffOnClosure` in
`Numlib.Analysis.Calculus.ContDiffOnClosure`. The extra generality is what the induction on the
order needs. On $\Omega \times [0, \infty)$ the derivatives at $t = 0$ are one-sided, so they are
taken within a set that is not open. The extension target can also be a set smaller than the
closure, such as $\bar\Omega \times (0, \infty)$.

## Main definitions

* `ContDiffOnExtendsTo`: $f$ is $C^n$ on $s$, and its derivatives of order $m \le n$ within $s$
  extend continuously to $t$.
* `prodFDerivL`: the derivative on $E \times \mathbb{R}$ assembled from the two partial derivatives,
  $(A, b) \mapsto ((y, \tau) \mapsto Ay + \tau b)$.

## Main results

* `hasFDerivWithinAt_prod_of_partials`: a function on $E \times \mathbb{R}$ with a partial Fréchet
  derivative $f_x$ in $x$ that is jointly continuous on $\Omega \times s$, and a partial derivative
  $f_t$ in $t$ within $s$, is differentiable within $\Omega \times s$ with derivative
  $(y, \tau) \mapsto f_x(p) y + \tau f_t(p)$.
* `ContDiffOnExtendsTo.prod_succ`: the induction step. If $f$ extends continuously to $t$ and its
  two partial derivatives are of class `ContDiffOnExtendsTo ℝ n` on $\Omega \times s$ with
  extensions to $t$, then $f$ is of this class at order $n + 1$.
* `contDiffOnExtendsTo_prod_of_partials`: a family $g_{ij}$ of candidate partial derivatives
  $\partial_t^j D_x^i f$, $i + j \le k$, each continuous on $t \supseteq \Omega \times s$, makes
  $g_{00}$ of class $C^k$ on $\Omega \times s$ with extensions to $t$.

## Proof outline

Differentiability comes from the mean value inequality on a segment in $\Omega$: only the partial
derivative in $x$ needs to be continuous. The derivative of $f$ is a continuous linear image of the
pair $(f_x, f_t)$, so an induction on the order gives the higher derivatives.

## Implementation notes

* The symmetry of the mixed partial derivatives is part of the hypotheses of
  `contDiffOnExtendsTo_prod_of_partials`, since $g_{i+1,j+1}$ is reached from $g_{ij}$ in both
  orders.
-/

open Filter Set Topology

open scoped ContDiff

/-! ### The class $C^n$ on $s$ with derivatives that extend continuously to $t$ -/

section ExtendsTo

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {X F G : Type*} [NormedAddCommGroup X]
  [NormedSpace 𝕜 X] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G]
  [NormedSpace 𝕜 G]

/-- **The class $C^n$ on $s$ with derivatives that extend continuously to $t$.** Let $X$ and $F$ be
normed spaces over $\mathbb{K}$, let $n \in \mathbb{N} \cup \{\infty, \omega\}$, and let
$s, t \subseteq X$. A function $f \colon X \to F$ belongs to this class if $f$ is $C^n$ on $s$
and, for every natural number $m \le n$, there is a function $g \colon X \to L^m(X; F)$ that is
continuous on $t$ and agrees on $s$ with the $m$-th derivative of $f$ within $s$.

For an open $s$ and $t = \bar s$ this is the class $C^n(\bar s)$ of `ContDiffOnClosure`. The
derivatives are taken within $s$ (`iteratedFDerivWithin`), so that $s$ can have a boundary in
some directions, as the half cylinder $\Omega \times [0, \infty)$ has. The set $t$ is arbitrary,
so that the extension can be asked on a set smaller than the closure, such as
$\bar\Omega \times (0, \infty)$. Here $L^m(X; F)$ is the space of continuous $m$-linear maps. -/
def ContDiffOnExtendsTo (n : WithTop ℕ∞) (f : X → F) (s t : Set X) : Prop :=
  ContDiffOn 𝕜 n f s ∧ ∀ m : ℕ, (m : WithTop ℕ∞) ≤ n →
    ∃ g : X → X [×m]→L[𝕜] F, ContinuousOn g t ∧ EqOn g (iteratedFDerivWithin 𝕜 m f s) s

variable {𝕜} {n : WithTop ℕ∞} {f : X → F} {s t : Set X}

namespace ContDiffOnExtendsTo

/-- A function of the class `ContDiffOnExtendsTo 𝕜 n f s t` is $C^n$ on $s$. -/
theorem contDiffOn (h : ContDiffOnExtendsTo 𝕜 n f s t) : ContDiffOn 𝕜 n f s := h.1

/-- A function of the class `ContDiffOnExtendsTo 𝕜 n f s t` is continuous on $s$. -/
theorem continuousOn (h : ContDiffOnExtendsTo 𝕜 n f s t) : ContinuousOn f s :=
  h.1.continuousOn

/-- If $f$ is of the class `ContDiffOnExtendsTo 𝕜 n f s t` and $m \le n$ is a natural number, then
the $m$-th derivative of $f$ within $s$ agrees on $s$ with a function that is continuous on $t$. -/
theorem exists_continuousOn_eqOn_iteratedFDerivWithin (h : ContDiffOnExtendsTo 𝕜 n f s t)
    {m : ℕ} (hm : (m : WithTop ℕ∞) ≤ n) :
    ∃ g : X → X [×m]→L[𝕜] F, ContinuousOn g t ∧ EqOn g (iteratedFDerivWithin 𝕜 m f s) s :=
  h.2 m hm

/-- Monotonicity in the order: if $f$ is of the class `ContDiffOnExtendsTo 𝕜 n f s t` and $m \le n$,
then $f$ is of the class `ContDiffOnExtendsTo 𝕜 m f s t`. -/
theorem of_le {m : WithTop ℕ∞} (h : ContDiffOnExtendsTo 𝕜 n f s t) (hmn : m ≤ n) :
    ContDiffOnExtendsTo 𝕜 m f s t :=
  ⟨h.1.of_le hmn, fun k hk ↦ h.2 k (hk.trans hmn)⟩

/-- Monotonicity in the extension target: if $f$ is of the class `ContDiffOnExtendsTo 𝕜 n f s t` and
$t' \subseteq t$, then $f$ is of the class `ContDiffOnExtendsTo 𝕜 n f s t'`. -/
theorem mono_right {t' : Set X} (h : ContDiffOnExtendsTo 𝕜 n f s t) (ht : t' ⊆ t) :
    ContDiffOnExtendsTo 𝕜 n f s t' :=
  ⟨h.1, fun m hm ↦
    let ⟨g, hgc, hge⟩ := h.2 m hm
    ⟨g, hgc.mono ht, hge⟩⟩

/-- The class depends only on the values on $s$: if $f$ is of the class
`ContDiffOnExtendsTo 𝕜 n f s t` and $f_1 = f$ on $s$, then $f_1$ is of the class
`ContDiffOnExtendsTo 𝕜 n f₁ s t`. -/
theorem congr {f₁ : X → F} (h : ContDiffOnExtendsTo 𝕜 n f s t) (hf : EqOn f₁ f s) :
    ContDiffOnExtendsTo 𝕜 n f₁ s t :=
  ⟨h.1.congr hf, fun m hm ↦
    let ⟨g, hgc, hge⟩ := h.2 m hm
    ⟨g, hgc, fun x hx ↦ by rw [iteratedFDerivWithin_congr hf hx]; exact hge hx⟩⟩

/-- If $f$ is of the class `ContDiffOnExtendsTo 𝕜 n f s t`, then $f$ itself agrees on $s$ with a
function that is continuous on $t$. -/
theorem exists_continuousOn_eqOn (h : ContDiffOnExtendsTo 𝕜 n f s t) :
    ∃ g : X → F, ContinuousOn g t ∧ EqOn g f s := by
  obtain ⟨g₀, hgc, hge⟩ := h.2 0 (by simp)
  refine ⟨fun x ↦ continuousMultilinearCurryFin0 𝕜 X F (g₀ x),
    (continuousMultilinearCurryFin0 𝕜 X F).continuous.comp_continuousOn hgc, fun x hx ↦ ?_⟩
  change continuousMultilinearCurryFin0 𝕜 X F (g₀ x) = f x
  rw [hge hx, iteratedFDerivWithin_zero_eq_comp, Function.comp_apply]
  exact (continuousMultilinearCurryFin0 𝕜 X F).apply_symm_apply (f x)

/-- Let $s$ be uniquely differentiable (`UniqueDiffOn`), and let $L \colon F \to G$ be a continuous
linear map. If $f$ is of the class `ContDiffOnExtendsTo 𝕜 n f s t`, then so is $L \circ f$. -/
theorem continuousLinearMap_comp (h : ContDiffOnExtendsTo 𝕜 n f s t) (L : F →L[𝕜] G)
    (hs : UniqueDiffOn 𝕜 s) : ContDiffOnExtendsTo 𝕜 n (L ∘ f) s t :=
  ⟨h.contDiffOn.continuousLinearMap_comp L, fun m hm ↦
    let ⟨g, hgc, hge⟩ := h.2 m hm
    ⟨fun x ↦ L.compContinuousMultilinearMap (g x),
      (ContinuousLinearMap.compContinuousMultilinearMapL 𝕜 (fun _ : Fin m ↦ X) F G L)
        |>.continuous.comp_continuousOn hgc,
      fun x hx ↦ by
        rw [L.iteratedFDerivWithin_comp_left (h.1 x hx) hs hx hm]
        exact congrArg _ (hge hx)⟩⟩

/-- Let $s$ be uniquely differentiable (`UniqueDiffOn`). If $f$ and $g$ both belong to the class
`ContDiffOnExtendsTo` of order $n$ for $s$ and $t$, then so does $f + g$. -/
theorem add {g : X → F} (hf : ContDiffOnExtendsTo 𝕜 n f s t)
    (hg : ContDiffOnExtendsTo 𝕜 n g s t) (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOnExtendsTo 𝕜 n (f + g) s t :=
  ⟨hf.contDiffOn.add hg.contDiffOn, fun m hm ↦
    let ⟨Gf, hGfc, hGfe⟩ := hf.2 m hm
    let ⟨Gg, hGgc, hGge⟩ := hg.2 m hm
    ⟨Gf + Gg, hGfc.add hGgc, fun x hx ↦ by
      rw [Pi.add_apply, iteratedFDerivWithin_add_apply ((hf.1 x hx).of_le hm)
        ((hg.1 x hx).of_le hm) hs hx, hGfe hx, hGge hx]⟩⟩

/-- Let $s$ be uniquely differentiable (`UniqueDiffOn`). If $f \colon X \to F$ and
$g \colon X \to G$ both belong to the class `ContDiffOnExtendsTo` of order $n$ for $s$ and $t$,
then so does the pair $x \mapsto (f(x), g(x))$. -/
theorem prodMk {g : X → G} (hf : ContDiffOnExtendsTo 𝕜 n f s t)
    (hg : ContDiffOnExtendsTo 𝕜 n g s t) (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOnExtendsTo 𝕜 n (fun x ↦ (f x, g x)) s t :=
  ⟨hf.contDiffOn.prodMk hg.contDiffOn, fun m hm ↦
    let ⟨Gf, hGfc, hGfe⟩ := hf.2 m hm
    let ⟨Gg, hGgc, hGge⟩ := hg.2 m hm
    ⟨fun x ↦ (Gf x).prod (Gg x),
      (ContinuousMultilinearMap.prodL 𝕜 (fun _ : Fin m ↦ X) F G).continuous.comp_continuousOn
        (hGfc.prodMk hGgc),
      fun x hx ↦ by
        simp only [iteratedFDerivWithin_prodMk (hf.1 x hx) (hg.1 x hx) hs hx hm, hGfe hx,
          hGge hx]⟩⟩

/-- **From derivatives within $s$ to $C^n(\bar s')$ on an open subset.** Let $f$ be of the class
`ContDiffOnExtendsTo 𝕜 n f s t`. Then for every open set $s' \subseteq s$ with
$\bar s' \subseteq t$, the function $f$ is of the class $C^n(\bar s')$ of `ContDiffOnClosure`.

On the open set $s'$, the derivatives within $s$ are the ordinary derivatives. -/
theorem contDiffOnClosure {s' : Set X} (h : ContDiffOnExtendsTo 𝕜 n f s t) (hs' : IsOpen s')
    (hs's : s' ⊆ s) (hst : closure s' ⊆ t) : ContDiffOnClosure 𝕜 n f s' :=
  ⟨h.1.mono hs's, fun m hm ↦
    let ⟨g, hgc, hge⟩ := h.2 m hm
    ⟨g, hgc.mono hst, fun x hx ↦ by
      rw [hge (hs's hx), ← iteratedFDerivWithin_inter_open hs' hx, inter_eq_right.2 hs's,
        iteratedFDerivWithin_of_isOpen m hs' hx]⟩⟩

end ContDiffOnExtendsTo

/-- At order $0$, a function is of the class `ContDiffOnExtendsTo 𝕜 0 f s t` if and only if it is
continuous on $s$ and agrees on $s$ with a function that is continuous on $t$. -/
theorem contDiffOnExtendsTo_zero_iff :
    ContDiffOnExtendsTo 𝕜 0 f s t ↔
      ContinuousOn f s ∧ ∃ g : X → F, ContinuousOn g t ∧ EqOn g f s := by
  constructor
  · intro h
    exact ⟨h.continuousOn, h.exists_continuousOn_eqOn⟩
  · rintro ⟨hf, g, hgc, hge⟩
    refine ⟨contDiffOn_zero.2 hf, fun m hm ↦ ?_⟩
    obtain rfl : m = 0 := by exact_mod_cast le_zero_iff.1 hm
    refine ⟨fun x ↦ (continuousMultilinearCurryFin0 𝕜 X F).symm (g x),
      (continuousMultilinearCurryFin0 𝕜 X F).symm.continuous.comp_continuousOn hgc,
      fun x hx ↦ ?_⟩
    simp only [iteratedFDerivWithin_zero_eq_comp, Function.comp_apply, hge hx]

/-- A function is of the class `ContDiffOnExtendsTo 𝕜 ∞ f s t` if and only if it is of the class
`ContDiffOnExtendsTo 𝕜 n f s t` for every natural number $n$. -/
theorem contDiffOnExtendsTo_infty_iff :
    ContDiffOnExtendsTo 𝕜 ∞ f s t ↔ ∀ n : ℕ, ContDiffOnExtendsTo 𝕜 n f s t := by
  constructor
  · exact fun h n ↦ h.of_le (by simp)
  · intro h
    exact ⟨contDiffOn_infty.2 fun n ↦ (h n).1, fun m _ ↦ (h m).2 m le_rfl⟩

/-- Let $s$ be open. A function is of the class `ContDiffOnExtendsTo 𝕜 n f s (closure s)` if and
only if it is of the class $C^n(\bar s)$ of `ContDiffOnClosure`. -/
theorem contDiffOnExtendsTo_closure_iff_contDiffOnClosure (hs : IsOpen s) :
    ContDiffOnExtendsTo 𝕜 n f s (closure s) ↔ ContDiffOnClosure 𝕜 n f s := by
  refine ⟨fun h ↦ h.contDiffOnClosure hs subset_rfl subset_rfl, fun h ↦ ⟨h.1, fun m hm ↦ ?_⟩⟩
  obtain ⟨g, hgc, hge⟩ := h.2 m hm
  exact ⟨g, hgc, fun x hx ↦ by rw [iteratedFDerivWithin_of_isOpen m hs hx]; exact hge hx⟩

end ExtendsTo

/-! ### Differentiability on $E \times \mathbb{R}$ from the two partial derivatives -/

section Prod

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

open ContinuousLinearMap in
/-- **The derivative on $E \times \mathbb{R}$ assembled from the two partial derivatives.** It is
the continuous linear map that sends a pair $(A, b)$, with $A \colon E \to F$ continuous linear
and $b \in F$, to the continuous linear map
$$(y, \tau) \mapsto Ay + \tau b \quad \text{on } E \times \mathbb{R}.$$
-/
noncomputable def prodFDerivL (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] : (E →L[ℝ] F) × F →L[ℝ] (E × ℝ →L[ℝ] F) :=
  ((compL ℝ (E × ℝ) E F).flip (fst ℝ E ℝ)).comp (ContinuousLinearMap.fst ℝ (E →L[ℝ] F) F) +
    (smulRightL ℝ (E × ℝ) F (snd ℝ E ℝ)).comp (ContinuousLinearMap.snd ℝ (E →L[ℝ] F) F)

/-- For $A \colon E \to F$ continuous linear, $b \in F$ and $(y, \tau) \in E \times \mathbb{R}$,
`prodFDerivL E F (A, b) (y, τ) = A y + τ • b`. -/
@[simp]
theorem prodFDerivL_apply (A : E →L[ℝ] F) (b : F) (q : E × ℝ) :
    prodFDerivL E F (A, b) q = A q.1 + q.2 • b := by
  simp [prodFDerivL]

/-- **The mean value step.** Let $\Omega \subseteq E$ be open, let $s \subseteq \mathbb{R}$, and let
$f \colon E \times \mathbb{R} \to F$ and $f_x \colon E \times \mathbb{R} \to L(E; F)$ be such
that $y \mapsto f(y, t)$ has the Fréchet derivative $f_x(x, t)$ at $x$ for all $x \in \Omega$
and $t \in s$. Let $x_0 \in \Omega$ and $t_0 \in \mathbb{R}$, and let $f_x$ be continuous within
$\Omega \times s$ at $(x_0, t_0)$. Then
$$f(x, t) - f(x_0, t) - f_x(x_0, t_0)(x - x_0) = o(\|x - x_0\|)$$
as $(x, t) \to (x_0, t_0)$ within $\Omega \times s$.

The proof applies the mean value inequality on the segment $[x_0, x]$, which lies in $\Omega$
for $x$ close to $x_0$. Mathlib's `isLittleO_sub_sub_fderiv` states this, but it is not exported
from its module. -/
theorem isLittleO_sub_sub_fst_of_partial {Ω : Set E} (hΩ : IsOpen Ω) {s : Set ℝ}
    {f : E × ℝ → F} {fx : E × ℝ → E →L[ℝ] F}
    (hfx : ∀ x ∈ Ω, ∀ t ∈ s, HasFDerivAt (fun y ↦ f (y, t)) (fx (x, t)) x)
    {x₀ : E} {t₀ : ℝ} (hx₀ : x₀ ∈ Ω) (hfxc : ContinuousWithinAt fx (Ω ×ˢ s) (x₀, t₀)) :
    (fun q : E × ℝ ↦ f (q.1, q.2) - f (x₀, q.2) - fx (x₀, t₀) (q.1 - x₀))
      =o[𝓝[Ω ×ˢ s] (x₀, t₀)] fun q ↦ q.1 - x₀ := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΩ x₀ hx₀
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousWithinAt_iff.1 hfxc ε hε
  have hmem : Metric.ball (x₀, t₀) (min δ r) ∈ 𝓝[Ω ×ˢ s] (x₀, t₀) :=
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ (lt_min hδ hr))
  filter_upwards [hmem, self_mem_nhdsWithin] with q hq hqs
  obtain ⟨x, t⟩ := q
  obtain ⟨hxΩ, hts⟩ := hqs
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hq
  have hxr : x ∈ Metric.ball x₀ r := lt_of_lt_of_le hq.1 (min_le_right _ _)
  have hsegΩ : segment ℝ x₀ x ⊆ Ω :=
    ((convex_ball x₀ r).segment_subset (Metric.mem_ball_self hr) hxr).trans hball
  have hsegδ : ∀ y ∈ segment ℝ x₀ x, dist y x₀ < δ := by
    intro y hy
    have : y ∈ Metric.closedBall x₀ (dist x x₀) :=
      (convex_closedBall x₀ (dist x x₀)).segment_subset (Metric.mem_closedBall_self dist_nonneg)
        (Metric.mem_closedBall.2 le_rfl) hy
    exact (Metric.mem_closedBall.1 this).trans_lt (hq.1.trans_le (min_le_left _ _))
  have hbound : ∀ y ∈ segment ℝ x₀ x, ‖fx (y, t) - fx (x₀, t₀)‖ ≤ ε := by
    intro y hy
    have h := @hδε (y, t) ⟨hsegΩ hy, hts⟩ (by
      rw [Prod.dist_eq, max_lt_iff]
      exact ⟨hsegδ y hy, hq.2.trans_le (min_le_left _ _)⟩)
    rw [dist_eq_norm] at h
    exact h.le
  exact (convex_segment x₀ x).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (f := fun y ↦ f (y, t)) (f' := fun y ↦ fx (y, t))
    (fun y hy ↦ (hfx y (hsegΩ hy) t hts).hasFDerivWithinAt) hbound (left_mem_segment ℝ x₀ x)
    (right_mem_segment ℝ x₀ x)

/-- **Differentiability on $\Omega \times s$ from the partial derivatives.** Let
$\Omega \subseteq E$ be open, let $s \subseteq \mathbb{R}$, and let
$f \colon E \times \mathbb{R} \to F$. Suppose that for every $(x, t) \in \Omega \times s$, the
function $y \mapsto f(y, t)$ has the Fréchet derivative $f_x(x, t)$ at $x$, and
$r \mapsto f(x, r)$ has the derivative $f_t(x, t)$ at $t$ within $s$. Suppose also that $f_x$ is
continuous on $\Omega \times s$. Then at every $p \in \Omega \times s$, the function $f$ has the
derivative
$$(y, \tau) \mapsto f_x(p) y + \tau f_t(p)$$
within $\Omega \times s$.

Only the partial derivative in $x$ must be continuous. The increment $f(x, t) - f(x_0, t)$ is
controlled by the mean value inequality on the segment $[x_0, x] \subseteq \Omega$
(`isLittleO_sub_sub_fst_of_partial`), and the increment $f(x_0, t) - f(x_0, t_0)$ by the
derivative in $t$ at the point. The derivative is `prodFDerivL E F (fx p, ft p)`. -/
theorem hasFDerivWithinAt_prod_of_partials {Ω : Set E} (hΩ : IsOpen Ω) {s : Set ℝ}
    {f : E × ℝ → F} {fx : E × ℝ → E →L[ℝ] F} {ft : E × ℝ → F}
    (hfx : ∀ x ∈ Ω, ∀ t ∈ s, HasFDerivAt (fun y ↦ f (y, t)) (fx (x, t)) x)
    (hft : ∀ x ∈ Ω, ∀ t ∈ s, HasDerivWithinAt (fun r ↦ f (x, r)) (ft (x, t)) s t)
    (hfxc : ContinuousOn fx (Ω ×ˢ s)) {p : E × ℝ} (hp : p ∈ Ω ×ˢ s) :
    HasFDerivWithinAt f (prodFDerivL E F (fx p, ft p)) (Ω ×ˢ s) p := by
  obtain ⟨x₀, t₀⟩ := p
  obtain ⟨hx₀, ht₀⟩ : x₀ ∈ Ω ∧ t₀ ∈ s := hp
  -- the increment in the second variable
  have h2 : HasFDerivWithinAt (fun q : E × ℝ ↦ f (x₀, q.2))
      ((ContinuousLinearMap.snd ℝ E ℝ).smulRight (ft (x₀, t₀))) (Ω ×ˢ s) (x₀, t₀) := by
    have h := (hft x₀ hx₀ t₀ ht₀).hasFDerivWithinAt.comp (x₀, t₀)
      (hasFDerivWithinAt_snd (𝕜 := ℝ) (s := Ω ×ˢ s) (p := (x₀, t₀)))
      (fun q (hq : q ∈ Ω ×ˢ s) ↦ hq.2)
    exact h.congr_fderiv (by ext <;> simp)
  -- the increment in the first variable
  have h1 := isLittleO_sub_sub_fst_of_partial hΩ hfx hx₀ (hfxc (x₀, t₀) ⟨hx₀, ht₀⟩)
  have h1' : HasFDerivWithinAt (fun q : E × ℝ ↦ f q - f (x₀, q.2))
      ((fx (x₀, t₀)).comp (ContinuousLinearMap.fst ℝ E ℝ)) (Ω ×ˢ s) (x₀, t₀) := by
    rw [hasFDerivWithinAt_iff_isLittleO]
    refine (h1.congr_left fun q ↦ ?_).trans_isBigO (Asymptotics.isBigO_of_le _ fun q ↦ ?_)
    · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', Prod.fst_sub]
      abel
    · exact (norm_fst_le (q - (x₀, t₀))).trans_eq' (by simp)
  have := h1'.add h2
  convert this using 1
  · ext q
    simp
  · ext <;> simp

end Prod

/-! ### The induction on the order -/

section Induction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {Ω : Set E} {s : Set ℝ} {t : Set (E × ℝ)}

/-- **The induction step: $C^{n+1}$ from partial derivatives of class $C^n$, up to the boundary.**
Let $\Omega \subseteq E$ be open, let $s \subseteq \mathbb{R}$ be uniquely differentiable, let
$t \subseteq E \times \mathbb{R}$, and let $n \in \mathbb{N}$. Let
$f \colon E \times \mathbb{R} \to F$ be continuous on $\Omega \times s$ and agree there with a
function that is continuous on $t$. Suppose that at every point of $\Omega \times s$, the
function $f$ has the partial Fréchet derivative $f_x$ in $x$ and the partial derivative $f_t$ in
the time variable within $s$. If $f_x$ and $f_t$ are of class $C^n$ on $\Omega \times s$ with
derivatives that extend continuously to $t$, then $f$ is of class $C^{n+1}$ on $\Omega \times s$
with derivatives that extend continuously to $t$.

The derivative of $f$ within $\Omega \times s$ is `prodFDerivL E F (fx p, ft p)`
(`hasFDerivWithinAt_prod_of_partials`), a continuous linear image of the pair $(f_x, f_t)$. The
class is `ContDiffOnExtendsTo ℝ`. -/
theorem ContDiffOnExtendsTo.prod_succ (hΩ : IsOpen Ω) (hs : UniqueDiffOn ℝ s) {n : ℕ}
    {f : E × ℝ → F} {fx : E × ℝ → E →L[ℝ] F} {ft : E × ℝ → F}
    (hf : ContDiffOnExtendsTo ℝ 0 f (Ω ×ˢ s) t)
    (hfx : ∀ x ∈ Ω, ∀ t ∈ s, HasFDerivAt (fun y ↦ f (y, t)) (fx (x, t)) x)
    (hft : ∀ x ∈ Ω, ∀ t ∈ s, HasDerivWithinAt (fun r ↦ f (x, r)) (ft (x, t)) s t)
    (hfxn : ContDiffOnExtendsTo ℝ n fx (Ω ×ˢ s) t)
    (hftn : ContDiffOnExtendsTo ℝ n ft (Ω ×ˢ s) t) :
    ContDiffOnExtendsTo ℝ (n + 1) f (Ω ×ˢ s) t := by
  have hsu : UniqueDiffOn ℝ (Ω ×ˢ s) := UniqueDiffOn.prod hΩ.uniqueDiffOn hs
  have hd : ∀ p ∈ Ω ×ˢ s, HasFDerivWithinAt f (prodFDerivL E F (fx p, ft p)) (Ω ×ˢ s) p :=
    fun p hp ↦ hasFDerivWithinAt_prod_of_partials hΩ hfx hft hfxn.continuousOn hp
  have hfd : EqOn (fderivWithin ℝ f (Ω ×ˢ s)) (fun p ↦ prodFDerivL E F (fx p, ft p)) (Ω ×ˢ s) :=
    fun p hp ↦ (hd p hp).fderivWithin (hsu p hp)
  have hD : ContDiffOnExtendsTo ℝ n (fderivWithin ℝ f (Ω ×ˢ s)) (Ω ×ˢ s) t :=
    ((hfxn.prodMk hftn hsu).continuousLinearMap_comp (prodFDerivL E F) hsu).congr hfd
  refine ⟨?_, fun m hm ↦ ?_⟩
  · rw [contDiffOn_succ_iff_fderivWithin hsu]
    exact ⟨fun p hp ↦ (hd p hp).differentiableWithinAt, by simp, hD.contDiffOn⟩
  · cases m with
    | zero => exact hf.2 0 le_rfl
    | succ m =>
      obtain ⟨g, hgc, hge⟩ := hD.2 m (by exact_mod_cast Nat.le_of_lt_succ (by exact_mod_cast hm))
      refine ⟨fun p ↦ (continuousMultilinearCurryRightEquiv' ℝ m (E × ℝ) F).symm (g p),
        (continuousMultilinearCurryRightEquiv' ℝ m (E × ℝ) F).symm.continuous.comp_continuousOn
          hgc, fun p hp ↦ ?_⟩
      rw [iteratedFDerivWithin_succ_eq_comp_right hsu hp, Function.comp_apply]
      exact congrArg _ (hge hp)

/-- **Smoothness on $\Omega \times s$ from a family of partial derivatives, up to the boundary.**
Let $\Omega \subseteq E$ be open, let $s \subseteq \mathbb{R}$ be uniquely differentiable, let
$\Omega \times s \subseteq t$, and let $k \in \mathbb{N}$. For $i, j \in \mathbb{N}$, let
$g_{ij} \colon E \times \mathbb{R} \to L^i(E; F)$ be a candidate for the partial derivative
$\partial_t^j D_x^i f$ of $f = g_{00}$. Suppose that:
* $g_{ij}$ is continuous on $t$ whenever $i + j \le k$;
* whenever $i + 1 + j \le k$, for $x \in \Omega$ and $r \in s$ the Fréchet derivative of
  $y \mapsto g_{ij}(y, r)$ at $x$ is $g_{i+1,j}(x, r)$, read as a map $E \to L^i(E; F)$ by
  currying in the first argument;
* whenever $i + j + 1 \le k$, for $x \in \Omega$ and $r \in s$ the derivative of
  $r' \mapsto g_{ij}(x, r')$ at $r$ within $s$ is $g_{i,j+1}(x, r)$.

Then for all $n, i, j$ with $i + j + n \le k$, the function $g_{ij}$ is of class $C^n$ on
$\Omega \times s$ with derivatives that extend continuously to $t$ (`ContDiffOnExtendsTo ℝ n`).
In particular $g_{00}$ is of class $C^k$.

The function $g_{00}$ takes values in $L^0(E; F)$, the space of continuous $0$-linear maps,
which is identified with $F$. The currying is `continuousMultilinearCurryLeftEquiv`. The
symmetry of the mixed partial derivatives is part of the hypotheses, since $g_{i+1,j+1}$ is
reached from $g_{ij}$ in both orders. The proof is an induction on $n$ through
`ContDiffOnExtendsTo.prod_succ`. -/
theorem contDiffOnExtendsTo_prod_of_partials (hΩ : IsOpen Ω) (hs : UniqueDiffOn ℝ s)
    (hst : Ω ×ˢ s ⊆ t) {k : ℕ} {g : (i : ℕ) → ℕ → E × ℝ → E [×i]→L[ℝ] F}
    (hgc : ∀ i j, i + j ≤ k → ContinuousOn (g i j) t)
    (hgx : ∀ i j, i + 1 + j ≤ k → ∀ x ∈ Ω, ∀ t ∈ s, HasFDerivAt (fun y ↦ g i j (y, t))
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) ↦ E) F (g (i + 1) j (x, t))) x)
    (hgt : ∀ i j, i + (j + 1) ≤ k → ∀ x ∈ Ω, ∀ t ∈ s,
      HasDerivWithinAt (fun r ↦ g i j (x, r)) (g i (j + 1) (x, t)) s t) :
    ∀ n i j, i + j + n ≤ k → ContDiffOnExtendsTo ℝ n (g i j) (Ω ×ˢ s) t := by
  intro n
  induction n with
  | zero =>
    intro i j hij
    exact contDiffOnExtendsTo_zero_iff.2
      ⟨(hgc i j (by omega)).mono hst, g i j, hgc i j (by omega), fun _ _ ↦ rfl⟩
  | succ n ih =>
    intro i j hij
    refine ContDiffOnExtendsTo.prod_succ hΩ hs
      (fx := fun p ↦ continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) ↦ E) F
        (g (i + 1) j p))
      (contDiffOnExtendsTo_zero_iff.2
        ⟨(hgc i j (by omega)).mono hst, g i j, hgc i j (by omega), fun _ _ ↦ rfl⟩)
      (hgx i j (by omega)) (hgt i j (by omega)) ?_ (ih i (j + 1) (by omega))
    exact (ih (i + 1) j (by omega)).continuousLinearMap_comp
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) ↦ E) F).toContinuousLinearEquiv
        : (E [×(i + 1)]→L[ℝ] F) →L[ℝ] (E →L[ℝ] E [×i]→L[ℝ] F))
      (UniqueDiffOn.prod hΩ.uniqueDiffOn hs)

end Induction
