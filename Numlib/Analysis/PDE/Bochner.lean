/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Curves of class $C^k(s; V)$ and $L^p(s; V)$ read in a larger space

The evolution equations of Chapter 10 of [brezis2011functional] describe their solutions as curves
$u : [0, \infty) \to H$ in a Hilbert space $H = L^2(\Omega)$. Beside $u \in C([0, \infty); H)$,
which is Mathlib's `ContinuousOn`, the book states membership in a smaller space: $u \in C((0,
\infty); H^2(\Omega) \cap H^1_0(\Omega))$, $u \in C^1([0, \infty); H^1_0(\Omega))$,
$u \in L^2(0, \infty; H^1_0(\Omega))$. In this library the smaller spaces are separate types $V$,
mapped into the larger space $W$ by a continuous linear injection $J : V \to W$. Each such clause
then says that $u$ factors through $J$ by a curve of the required regularity. A curve
$u : \mathbb{R} \to W$ is of class $C^k(s; V)$ if $u = J \circ v$ on $s$ for a curve
$v : \mathbb{R} \to V$ of class $C^k$ on $s$, and of class $L^p(s; V)$ if $u = J \circ v$ on $s$ for
some $v$ in the Bochner space $L^p(s; V)$. The notation follows §10.1 of [brezis2011functional].

Two lemmas carry weight. The derivative of the curve is the image of the derivative of the lift,
$\frac{d}{dt} (Jv) = J \frac{dv}{dt}$; this is the step "$A \in \mathcal{L}(H_1, H)$ and
$u \in C([0, \infty); H_1)$ give $\frac{d}{dt}(Au) = A \frac{du}{dt}$" of the proof of Theorem 7.5
of [brezis2011functional]. And a continuous lift whose norm to the power $p$ is integrable gives the
class $L^p(s; V)$; in this form the energy identities of the heat equation give
$u \in L^2(0, \infty; H^1_0(\Omega))$.

## Main definitions

* `Bochner.ContDiffOnThrough`: the class $C^k(s; V)$ of a curve read in $W$.
* `Bochner.MemLpThrough`: the class $L^p(s; V)$ of a curve read in $W$.

## Main results

* `Bochner.ContDiffOnThrough.contDiffOn`: a curve of class $C^k(s; V)$ is a $C^k$ curve in $W$.
* `Bochner.ContDiffOnThrough.mono`, `Bochner.ContDiffOnThrough.of_le`: monotonicity in the set and
  in the order.
* `Bochner.ContDiffOnThrough.comp`, `Bochner.ContDiffOnThrough.of_comp`: composition with a further
  bounded map, and restriction of the lift along a factorization of $J$.
* `Bochner.ContDiffOnThrough.infty_of_forall_nat`: through an injective $J$, a curve of class
  $C^n(s; V)$ for every $n \in \mathbb{N}$ is of class $C^\infty(s; V)$.
* `Bochner.ContDiffOnThrough.derivWithin_eq`: the derivative commutes with $J$.
* `Bochner.ContDiffOnThrough.derivWithin`: the derivative of a curve of class $C^k(s; V)$ is of
  class $C^m(s; V)$ for $m + 1 \le k$.
* `Bochner.MemLpThrough.of_contDiffOnThrough_of_integrable`: a continuous lift whose norm to the
  power $p$ is integrable gives the class $L^p(s; V)$.

## Implementation notes

* The predicates need only Mathlib, and they are stated for an arbitrary continuous linear map $J$.
* The Bochner space $L^p(s; V)$ is Mathlib's `MemLp` of a $V$-valued function of a real variable for
  the restricted Lebesgue measure.
* No type $L^2(0, T; V)$ is built, and no jointly measurable representative of a curve is
  constructed. The reading of a curve of Sobolev functions as a function $u(x, t)$ of space and time
  is in `Numlib.Analysis.PDE.Bochner.SpaceTime`.
-/

open MeasureTheory Set

open scoped ENNReal Topology

namespace Bochner

variable {V W X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W] [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ### The class $C^k(s; V)$ -/

/-- **The class $C^k(s; V)$ of a curve read in $W$.** Let $J : V \to W$ be a continuous linear map,
$k \in \mathbb{N} \cup \{\infty, \omega\}$ and $s \subseteq \mathbb{R}$. A curve
$u : \mathbb{R} \to W$ is of class $C^k(s; V)$ if there is a curve $v : \mathbb{R} \to V$ of
class $C^k$ on $s$ with $u(t) = J v(t)$ for all $t \in s$. With $k = 0$ this is the class
$C(s; V)$.

The order $k$ has the type `WithTop ℕ∞` of Mathlib's `ContDiffOn`. -/
def ContDiffOnThrough (J : V →L[ℝ] W) (k : WithTop ℕ∞) (u : ℝ → W) (s : Set ℝ) : Prop :=
  ∃ v : ℝ → V, ContDiffOn ℝ k v s ∧ ∀ t ∈ s, u t = J (v t)

namespace ContDiffOnThrough

variable {J : V →L[ℝ] W} {k : WithTop ℕ∞} {u : ℝ → W} {s : Set ℝ}

/-- A curve of class $C^k(s; V)$ is a $C^k$ curve in $W$ on $s$. -/
theorem contDiffOn (h : ContDiffOnThrough J k u s) : ContDiffOn ℝ k u s := by
  obtain ⟨v, hv, huv⟩ := h
  exact (J.contDiff.comp_contDiffOn hv).congr fun t ht ↦ huv t ht

/-- A curve of class $C^k(s; V)$ is continuous on $s$ as a curve in $W$. -/
theorem continuousOn (h : ContDiffOnThrough J k u s) : ContinuousOn u s :=
  h.contDiffOn.continuousOn

/-- If $u$ is of class $C^k(s; V)$ and $s' \subseteq s$, then $u$ is of class $C^k(s'; V)$. -/
theorem mono {s' : Set ℝ} (h : ContDiffOnThrough J k u s) (hs : s' ⊆ s) :
    ContDiffOnThrough J k u s' :=
  let ⟨v, hv, huv⟩ := h
  ⟨v, hv.mono hs, fun t ht ↦ huv t (hs ht)⟩

/-- If $u$ is of class $C^k(s; V)$ and $k' \le k$, then $u$ is of class $C^{k'}(s; V)$. -/
theorem of_le {k' : WithTop ℕ∞} (h : ContDiffOnThrough J k u s) (hk : k' ≤ k) :
    ContDiffOnThrough J k' u s :=
  let ⟨v, hv, huv⟩ := h
  ⟨v, hv.of_le hk, huv⟩

/-- **One lift for all orders.** Let $J$ be injective. If $u$ is of class $C^n(s; V)$ for every
$n \in \mathbb{N}$, then $u$ is of class $C^\infty(s; V)$.

The lifts at the various orders agree on $s$, because $J$ is injective, so the lift of order $0$
is of every class. -/
theorem infty_of_forall_nat (hJ : Function.Injective J)
    (h : ∀ n : ℕ, ContDiffOnThrough J n u s) : ContDiffOnThrough J (⊤ : ℕ∞) u s := by
  obtain ⟨v, -, huv⟩ := h 0
  refine ⟨v, contDiffOn_infty.2 fun n ↦ ?_, huv⟩
  obtain ⟨w, hw, huw⟩ := h n
  exact hw.congr fun t ht ↦ hJ ((huv t ht).symm.trans (huw t ht))

/-- A $C^k$ curve $v$ in $V$ on $s$ is of class $C^k(s; V)$ through the identity map of $V$. -/
theorem of_contDiffOn {v : ℝ → V} (hv : ContDiffOn ℝ k v s) :
    ContDiffOnThrough (ContinuousLinearMap.id ℝ V) k v s :=
  ⟨v, hv, fun _ _ ↦ rfl⟩

/-- Through the identity map of $V$, a curve $v$ is of class $C^k(s; V)$ if and only if $v$ is $C^k$
on $s$. -/
theorem id_iff {v : ℝ → V} :
    ContDiffOnThrough (ContinuousLinearMap.id ℝ V) k v s ↔ ContDiffOn ℝ k v s :=
  ⟨contDiffOn, of_contDiffOn⟩

/-- If $u$ is of class $C^k(s; V)$ through $J$ and $J' : W \to X$ is continuous linear, then
$J' \circ u$ is of class $C^k(s; V)$ through $J' \circ J$. -/
theorem comp (h : ContDiffOnThrough J k u s) (J' : W →L[ℝ] X) :
    ContDiffOnThrough (J'.comp J) k (J' ∘ u) s :=
  let ⟨v, hv, huv⟩ := h
  ⟨v, hv, fun t ht ↦ by simp [huv t ht]⟩

/-- Restriction of the lift along a factorization of the embedding. Let $J_1 : V_1 \to V$ and
$J : V \to W$ be continuous linear maps. If $u$ is of class $C^k(s; V_1)$ through $J \circ J_1$,
then $u$ is of class $C^k(s; V)$ through $J$. For example, $C^k(s; H^2(\Omega))$ implies
$C^k(s; H^1(\Omega))$. -/
theorem of_comp {V₁ : Type*} [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] {J₁ : V₁ →L[ℝ] V}
    (h : ContDiffOnThrough (J.comp J₁) k u s) : ContDiffOnThrough J k u s :=
  let ⟨v, hv, huv⟩ := h
  ⟨J₁ ∘ v, J₁.contDiff.comp_contDiffOn hv, fun t ht ↦ by simpa using huv t ht⟩

/-- **The derivative commutes with the embedding.** Let $s \subseteq \mathbb{R}$ have unique
derivatives, let $v : \mathbb{R} \to V$ be $C^k$ on $s$ with $k \ge 1$, and let $u(t) = J v(t)$
for $t \in s$. Then at every $t \in s$, the derivatives within $s$ satisfy
$$u'(t) = J v'(t).$$
-/
theorem derivWithin_eq {v : ℝ → V} (hv : ContDiffOn ℝ k v s) (huv : ∀ t ∈ s, u t = J (v t))
    (hk : 1 ≤ k) (hs : UniqueDiffOn ℝ s) {t : ℝ} (ht : t ∈ s) :
    derivWithin u s t = J (derivWithin v s t) := by
  have hd : HasDerivWithinAt v (derivWithin v s t) s t :=
    ((hv.differentiableOn (ENat.one_le_iff_ne_zero_withTop.1 hk)) t ht).hasDerivWithinAt
  have := (HasFDerivAt.comp_hasDerivWithinAt t (J.hasFDerivAt (x := v t)) hd).congr
    (fun x hx ↦ huv x hx) (huv t ht)
  exact this.derivWithin (hs t ht)

/-- Let $s \subseteq \mathbb{R}$ have unique derivatives, and let $u$ be of class $C^k(s; V)$. If
$m + 1 \le k$, then the derivative of $u$ within $s$ is of class $C^m(s; V)$, and its lift is
the derivative of the lift of $u$. -/
theorem derivWithin {m : WithTop ℕ∞} (h : ContDiffOnThrough J k u s) (hs : UniqueDiffOn ℝ s)
    (hmk : m + 1 ≤ k) : ContDiffOnThrough J m (derivWithin u s) s :=
  let ⟨v, hv, huv⟩ := h
  ⟨_root_.derivWithin v s, hv.derivWithin hs hmk, fun t ht ↦
    derivWithin_eq hv huv (le_trans (by simp) hmk) hs ht⟩

end ContDiffOnThrough

/-! ### The class $L^p(s; V)$ -/

/-- **The class $L^p(s; V)$ of a curve read in $W$.** Let $J : V \to W$ be a continuous linear map,
$p \in [0, \infty]$ and $s \subseteq \mathbb{R}$. A curve $u : \mathbb{R} \to W$ is of class
$L^p(s; V)$ if there is a function $v : \mathbb{R} \to V$ in the Bochner space $L^p(s; V)$ with
$u(t) = J v(t)$ for all $t \in s$.

The Bochner space is Mathlib's `MemLp v p (volume.restrict s)`. The definition asks for
agreement at every point of $s$, not almost everywhere, because every curve to which it is
applied is continuous. -/
def MemLpThrough (J : V →L[ℝ] W) (p : ℝ≥0∞) (u : ℝ → W) (s : Set ℝ) : Prop :=
  ∃ v : ℝ → V, MemLp v p (volume.restrict s) ∧ ∀ t ∈ s, u t = J (v t)

namespace MemLpThrough

variable {J : V →L[ℝ] W} {p : ℝ≥0∞} {u : ℝ → W} {s : Set ℝ}

/-- Let $s$ be measurable. A curve of class $L^p(s; V)$ is in $L^p(s; W)$. -/
theorem memLp (hs : MeasurableSet s) (h : MemLpThrough J p u s) : MemLp u p (volume.restrict s) :=
  let ⟨_, hv, huv⟩ := h
  (hv.continuousLinearMap_comp J).ae_eq
    ((ae_restrict_iff' hs).2 (Filter.Eventually.of_forall fun t ht ↦ (huv t ht).symm))

/-- If $u$ is of class $L^p(s; V)$ and $s' \subseteq s$, then $u$ is of class $L^p(s'; V)$. -/
theorem mono {s' : Set ℝ} (h : MemLpThrough J p u s) (hs : s' ⊆ s) : MemLpThrough J p u s' :=
  let ⟨v, hv, huv⟩ := h
  ⟨v, hv.mono_measure (Measure.restrict_mono hs le_rfl), fun t ht ↦ huv t (hs ht)⟩

/-- If $u$ is of class $L^p(s; V)$ through $J$ and $J' : W \to X$ is continuous linear, then
$J' \circ u$ is of class $L^p(s; V)$ through $J' \circ J$. -/
theorem comp (h : MemLpThrough J p u s) (J' : W →L[ℝ] X) : MemLpThrough (J'.comp J) p (J' ∘ u) s :=
  let ⟨v, hv, huv⟩ := h
  ⟨v, hv, fun t ht ↦ by simp [huv t ht]⟩

/-- Restriction of the lift along a factorization of the embedding. Let $J_1 : V_1 \to V$ and
$J : V \to W$ be continuous linear maps. If $u$ is of class $L^p(s; V_1)$ through $J \circ J_1$,
then $u$ is of class $L^p(s; V)$ through $J$. -/
theorem of_comp {V₁ : Type*} [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] {J₁ : V₁ →L[ℝ] V}
    (h : MemLpThrough (J.comp J₁) p u s) : MemLpThrough J p u s :=
  let ⟨v, hv, huv⟩ := h
  ⟨J₁ ∘ v, hv.continuousLinearMap_comp J₁, fun t ht ↦ by simpa using huv t ht⟩

/-- **From continuity and an integral bound to $L^p(s; V)$.** Let $s \subseteq \mathbb{R}$ be
measurable and $0 < p < \infty$. Let $v : \mathbb{R} \to V$ be continuous on $s$, with
$t \mapsto \|v(t)\|^p$ integrable on $s$, and let $u(t) = J v(t)$ for $t \in s$. Then $u$ is of
class $L^p(s; V)$.

In this form the energy identities of the heat equation give
$u \in L^2(0, \infty; H^1_0(\Omega))$: continuity into $H^1_0(\Omega)$ together with
$\int_0^\infty \|u(t)\|_{H^1}^2 \, dt < \infty$. -/
theorem of_contDiffOnThrough_of_integrable {v : ℝ → V} (hv : ContinuousOn v s)
    (huv : ∀ t ∈ s, u t = J (v t)) (hs : MeasurableSet s) (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (hint : IntegrableOn (fun t ↦ ‖v t‖ ^ p.toReal) s) : MemLpThrough J p u s := by
  refine ⟨v, ?_, huv⟩
  have hmeas : AEStronglyMeasurable v (volume.restrict s) := hv.aestronglyMeasurable hs
  have := (memLp_norm_rpow_iff (p := p) (q := p) (μ := volume.restrict s) hmeas hp0 hp).1
  rw [ENNReal.div_self hp0 hp, memLp_one_iff_integrable] at this
  exact this hint

end MemLpThrough

end Bochner
