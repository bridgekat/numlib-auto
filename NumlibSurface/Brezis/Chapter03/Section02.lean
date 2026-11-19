/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Numlib.Analysis.Normed.Module.WeakClosed
import Numlib.Analysis.Normed.Module.WeakDual
import Numlib.Analysis.Normed.Module.WeakStarMetrizable
import NumlibSurface.Brezis.Chapter03.Section01

/-!
# Brezis, Section 3.2: Definition and elementary properties of the weak topology $\sigma(E,E^\star)$

This module formalizes Section 3.2 of [brezis2011functional] for a real Banach space $E$. The weak
topology $\sigma(E, E^\star)$ is the coarsest topology on $E$ that makes every map
$x \mapsto \langle f, x \rangle$, $f \in E^\star$, continuous. It is Hausdorff (Proposition 3.3),
and the sets $V(f_1, \dots, f_k; \varepsilon) = \{x : |\langle f_i, x - x_0 \rangle| < \varepsilon
\text{ for } i = 1, \dots, k\}$ form a basis of neighborhoods of $x_0$ (Proposition 3.4). A sequence
converges weakly, $x_n \rightharpoonup x$, if and only if $\langle f, x_n \rangle \to \langle f, x
\rangle$ for every $f \in E^\star$, and weak limits satisfy the properties of Proposition 3.5. In
finite dimension the weak and the strong topologies coincide (Proposition 3.6). In infinite
dimension the unit sphere is not weakly closed, the open unit ball is not weakly open, and the weak
topology is not metrizable.

The definition uses `Brezis.Chapter03.weakestTopology` of Section 3.1. Propositions 3.3 to 3.5
restate Mathlib and the backbone module `Numlib.Analysis.Normed.Module.WeakDual`. Proposition 3.6,
Remark 2 and Examples 1 and 2 restate `Numlib.Analysis.Normed.Module.WeakClosed`, and Remark 3
restates `Numlib.Analysis.Normed.Module.WeakStarMetrizable`.

## Main definitions

* Section 3.2, definition of the weak topology, `Brezis.Chapter03.weakTopology`: the topology
  $\sigma(E, E^\star)$.
* Section 3.2, the notation $x_n \rightharpoonup x$, `Brezis.Chapter03.WeakTendsto`: weak
  convergence of a sequence.

## Main results

* Section 3.2, `Brezis.Chapter03.weakTopology_eq`: $\sigma(E, E^\star)$ is the topology of Mathlib's
  `WeakSpace ℝ E`.
* Section 3.2, `Brezis.Chapter03.weakTopology_le`: the weak topology is weaker than the usual
  topology.
* Proposition 3.3, `Brezis.Chapter03.proposition_3_3`: $\sigma(E, E^\star)$ is Hausdorff.
* Proposition 3.4, `Brezis.Chapter03.proposition_3_4`: the sets $V(f_1, \dots, f_k; \varepsilon)$
  form a basis of neighborhoods of $x_0$.
* Proposition 3.5, `Brezis.Chapter03.proposition_3_5`: (i) $x_n \rightharpoonup x$ if and only if
  $\langle f, x_n \rangle \to \langle f, x \rangle$ for every $f \in E^\star$.
* Proposition 3.5, `Brezis.Chapter03.proposition_3_5_ii`: (ii) strong convergence implies weak
  convergence.
* Proposition 3.5, `Brezis.Chapter03.proposition_3_5_iii_bounded`: (iii) a weakly convergent
  sequence is bounded.
* Proposition 3.5, `Brezis.Chapter03.proposition_3_5_iii_liminf`: (iii) if $x_n \rightharpoonup x$,
  then $\|x\| \le \liminf \|x_n\|$.
* Proposition 3.5, `Brezis.Chapter03.proposition_3_5_iv`: (iv) if $x_n \rightharpoonup x$ and
  $f_n \to f$ in $E^\star$, then $\langle f_n, x_n \rangle \to \langle f, x \rangle$.
* Proposition 3.6, `Brezis.Chapter03.proposition_3_6`: in finite dimension, $\sigma(E, E^\star)$ is
  the usual topology.
* Proposition 3.6, `Brezis.Chapter03.proposition_3_6_tendsto`: in finite dimension, weak and strong
  convergence of sequences coincide.
* Remark 2, `Brezis.Chapter03.remark_3_2_isOpen`: a weakly open set is strongly open.
* Remark 2, `Brezis.Chapter03.remark_3_2_isClosed`: a weakly closed set is strongly closed.
* Example 1, `Brezis.Chapter03.example_3_1`: in infinite dimension, the weak closure of the unit
  sphere is the closed unit ball.
* Example 2, `Brezis.Chapter03.example_3_2`: in infinite dimension, the open unit ball is not weakly
  open.
* Remark 3, `Brezis.Chapter03.remark_3_3`: in infinite dimension, the weak topology is not
  metrizable.

## Conventions

* A point $x \in E$ with the weak topology is `toWeakSpace ℝ E x : WeakSpace ℝ E`. A set
  $s \subseteq E$ is weakly closed or weakly open if `toWeakSpace ℝ E '' s` is closed or open. Weak
  convergence $x_n \rightharpoonup x$ is `Brezis.Chapter03.WeakTendsto x u`, with the scoped
  notation `⇀`.

## Implementation notes

* The source assumes throughout that $E$ is a Banach space. The theorems carry `[CompleteSpace E]`
  as the source states it, although no proof in this section uses it.
* Remark 4 is stated in Section 3.2 of the source, but its declaration `Brezis.Chapter03.remark_3_4`
  is in `NumlibSurface.Brezis.Chapter03.Section06`, with Theorem 3.29.

## Deviations from the source

* **Weak topology and weak convergence** (generalization). The definitions and comparison of
  topologies work in incomplete normed spaces. See `Brezis.Chapter03.weakTopology`,
  `Brezis.Chapter03.weakTopology_le` and `Brezis.Chapter03.WeakTendsto`.
-/

open Filter Metric Set Topology TopologicalSpace

namespace Brezis.Chapter03

/-! ### The weak topology -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Section 3.2** of [brezis2011functional], definition of the weak topology. Let $E$ be a real
normed space. For $f \in E^\star$ let $\varphi_f : E \to \mathbb{R}$ be
$\varphi_f(x) = \langle f, x \rangle$. The **weak topology** $\sigma(E, E^\star)$ on $E$ is the
coarsest topology that makes every $\varphi_f$, $f \in E^\star$, continuous.

**Generalization.** The source takes $E$ complete. The coarsest topology making the
continuous dual's evaluations continuous is defined for any real normed space.

This is the construction of Section 3.1 with $X = E$, $Y_i = \mathbb{R}$ and $I = E^\star$:
`Brezis.Chapter03.weakestTopology`. -/
@[instance_reducible]
def weakTopology (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : TopologicalSpace E :=
  weakestTopology (fun f : StrongDual ℝ E => (f : E → ℝ))

/-- The weak topology of the source is Mathlib's: `Brezis.Chapter03.weakTopology E` is the topology
of `WeakSpace ℝ E`, transported to $E$ along the identity map `toWeakSpace ℝ E`. -/
theorem weakTopology_eq :
    weakTopology E = TopologicalSpace.induced (toWeakSpace ℝ E) inferInstance := by
  change _ = TopologicalSpace.induced (toWeakSpace ℝ E) (TopologicalSpace.induced
    (fun (x : WeakSpace ℝ E) (f : StrongDual ℝ E) => f x) Pi.topologicalSpace)
  rw [induced_compose, induced_to_pi]
  rfl

/-- **Section 3.2** of [brezis2011functional], "the weak topology is weaker than the usual
topology". Every weakly open subset of a real normed space $E$ is open in the norm topology.

**Generalization.** The source takes $E$ complete. The comparison follows from continuity
of each dual functional and also holds in incomplete normed spaces.

In Mathlib's order on topologies, the norm topology is finer:
`(norm topology) ≤ weakTopology E`. -/
theorem weakTopology_le : (inferInstance : TopologicalSpace E) ≤ weakTopology E := by
  rw [weakTopology_eq]
  exact continuous_iff_le_induced.1 (toWeakSpaceCLM ℝ E).continuous

/-- **Proposition 3.3** of [brezis2011functional]. Let $E$ be a Banach space. The weak topology
$\sigma(E, E^\star)$ is Hausdorff. -/
theorem proposition_3_3 [CompleteSpace E] : T2Space (WeakSpace ℝ E) :=
  inferInstance

/-- **Proposition 3.4** of [brezis2011functional]. Let $E$ be a Banach space and let $x_0 \in E$.
Given $\varepsilon > 0$ and a finite set $\{f_1, f_2, \dots, f_k\} \subseteq E^\star$, the set
$$V = V(f_1, f_2, \dots, f_k; \varepsilon) = \{x \in E : |\langle f_i, x - x_0 \rangle| <
  \varepsilon \ \forall i \in \{1, 2, \dots, k\}\}$$
is a neighborhood of $x_0$ for the topology $\sigma(E, E^\star)$. Moreover, these sets form a
basis of neighborhoods of $x_0$ for $\sigma(E, E^\star)$.

The finite set is a `Finset (StrongDual ℝ E)`, and the basis is indexed by the pairs of a finite
set and an $\varepsilon > 0$. -/
theorem proposition_3_4 [CompleteSpace E] (x₀ : E) :
    (∀ (s : Finset (StrongDual ℝ E)) (ε : ℝ), 0 < ε →
      toWeakSpace ℝ E '' {x | ∀ f ∈ s, |f (x - x₀)| < ε} ∈ 𝓝 (toWeakSpace ℝ E x₀)) ∧
    (𝓝 (toWeakSpace ℝ E x₀)).HasBasis (fun p : Finset (StrongDual ℝ E) × ℝ => 0 < p.2)
      (fun p => toWeakSpace ℝ E '' {x | ∀ f ∈ p.1, |f (x - x₀)| < p.2}) := by
  have hb := WeakBilin.hasBasis_nhds (topDualPairing ℝ E).flip (toWeakSpace ℝ E x₀)
  have hset : ∀ (s : Finset (StrongDual ℝ E)) (ε : ℝ),
      toWeakSpace ℝ E '' {x | ∀ f ∈ s, |f (x - x₀)| < ε} =
        {x : WeakSpace ℝ E | ∀ f ∈ s, ‖(topDualPairing ℝ E).flip x f -
          (topDualPairing ℝ E).flip (toWeakSpace ℝ E x₀) f‖ < ε} := by
    intro s ε
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      intro f hf
      have := hx f hf
      rwa [map_sub] at this
    · intro hy
      refine ⟨(toWeakSpace ℝ E).symm y, fun f hf => ?_, (toWeakSpace ℝ E).apply_symm_apply y⟩
      rw [map_sub]
      exact hy f hf
  refine ⟨fun s ε hε => ?_, hb.congr (fun _ => Iff.rfl) fun p _ => (hset p.1 p.2).symm⟩
  rw [hset]
  exact hb.mem_of_mem (i := (s, ε)) hε

/-- **Section 3.2** of [brezis2011functional], the notation $x_n \rightharpoonup x$. Let $E$ be a
real normed space. A sequence $(x_n)$ in $E$ **converges weakly** to $x$, written
$x_n \rightharpoonup x$, if $x_n \to x$ in the weak topology $\sigma(E, E^\star)$.

**Generalization.** The source takes $E$ complete. Weak convergence is defined in every
normed space, since `Brezis.Chapter03.weakTopology` needs no completeness.

Strong convergence $x_n \to x$ is Mathlib's `Tendsto x atTop (𝓝 u)`. The scoped notation is
`x ⇀ u`. -/
def WeakTendsto (x : ℕ → E) (u : E) : Prop :=
  Tendsto (fun n => toWeakSpace ℝ E (x n)) atTop (𝓝 (toWeakSpace ℝ E u))

@[inherit_doc] scoped notation:50 x:51 " ⇀ " u:51 => WeakTendsto x u

/-- **Proposition 3.5(i)** of [brezis2011functional]. Let $E$ be a Banach space and let $(x_n)$ be a
sequence in $E$. Then $x_n \rightharpoonup x$ weakly in $\sigma(E, E^\star)$ if and only if
$\langle f, x_n \rangle \to \langle f, x \rangle$ for every $f \in E^\star$. -/
theorem proposition_3_5 [CompleteSpace E] (x : ℕ → E) (u : E) :
    x ⇀ u ↔ ∀ f : StrongDual ℝ E, Tendsto (fun n => f (x n)) atTop (𝓝 (f u)) :=
  tendsto_toWeakSpace_iff

/-- **Proposition 3.5(ii)** of [brezis2011functional]. Let $E$ be a Banach space and let $(x_n)$ be
a sequence in $E$. If $x_n \to x$ strongly, then $x_n \rightharpoonup x$ weakly in
$\sigma(E, E^\star)$. -/
theorem proposition_3_5_ii [CompleteSpace E] {x : ℕ → E} {u : E} (h : Tendsto x atTop (𝓝 u)) :
    x ⇀ u :=
  ((toWeakSpaceCLM ℝ E).continuous.tendsto u).comp h

/-- **Proposition 3.5(iii)** of [brezis2011functional], boundedness. Let $E$ be a Banach space and
let $(x_n)$ be a sequence in $E$. If $x_n \rightharpoonup x$ weakly in $\sigma(E, E^\star)$,
then $(\|x_n\|)$ is bounded. -/
theorem proposition_3_5_iii_bounded [CompleteSpace E] {x : ℕ → E} {u : E} (h : x ⇀ u) :
    ∃ C : ℝ, ∀ n, ‖x n‖ ≤ C :=
  exists_norm_le_of_tendsto_toWeakSpace h

/-- **Proposition 3.5(iii)** of [brezis2011functional], lower semicontinuity of the norm. Let $E$ be
a Banach space and let $(x_n)$ be a sequence in $E$. If $x_n \rightharpoonup x$ weakly in
$\sigma(E, E^\star)$, then
$$\|x\| \le \liminf_{n \to \infty} \|x_n\|.$$
-/
theorem proposition_3_5_iii_liminf [CompleteSpace E] {x : ℕ → E} {u : E} (h : x ⇀ u) :
    ‖u‖ ≤ liminf (fun n => ‖x n‖) atTop :=
  norm_le_liminf_norm_of_weak_tendsto h

/-- **Proposition 3.5(iv)** of [brezis2011functional]. Let $E$ be a Banach space, let $(x_n)$ be a
sequence in $E$, and let $(f_n)$ be a sequence in $E^\star$. If $x_n \rightharpoonup x$ weakly
in $\sigma(E, E^\star)$ and $f_n \to f$ strongly in $E^\star$, then $\langle f_n, x_n \rangle
\to \langle f, x \rangle$. -/
theorem proposition_3_5_iv [CompleteSpace E] {x : ℕ → E} {u : E} {f : ℕ → StrongDual ℝ E}
    {g : StrongDual ℝ E} (hx : x ⇀ u) (hf : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun n => f n (x n)) atTop (𝓝 (g u)) :=
  tendsto_apply_of_tendsto_toWeakSpace_of_tendsto hx hf

/-- **Proposition 3.6** of [brezis2011functional]. Let $E$ be a finite-dimensional Banach space.
Then the weak topology $\sigma(E, E^\star)$ and the usual topology on $E$ are the same. -/
theorem proposition_3_6 [CompleteSpace E] [FiniteDimensional ℝ E] :
    weakTopology E = (inferInstance : TopologicalSpace E) := by
  rw [weakTopology_eq]
  exact ((toWeakSpaceContinuousLinearEquiv ℝ E).toHomeomorph.isInducing.eq_induced).symm

/-- **Proposition 3.6** of [brezis2011functional], the "in particular" clause. Let $E$ be a
finite-dimensional Banach space. A sequence $(x_n)$ in $E$ converges weakly to $x$ if and only
if it converges strongly to $x$. -/
theorem proposition_3_6_tendsto [CompleteSpace E] [FiniteDimensional ℝ E] (x : ℕ → E) (u : E) :
    x ⇀ u ↔ Tendsto x atTop (𝓝 u) :=
  tendsto_toWeakSpace_iff_of_finiteDimensional

/-- **Remark 2** of [brezis2011functional], open sets. Let $E$ be a Banach space. A subset of $E$
that is open in the weak topology $\sigma(E, E^\star)$ is open in the strong topology. -/
theorem remark_3_2_isOpen [CompleteSpace E] {s : Set E} (h : IsOpen (toWeakSpace ℝ E '' s)) :
    IsOpen s :=
  WeakSpace.isOpen_of_isOpen s h

/-- **Remark 2** of [brezis2011functional], closed sets. Let $E$ be a Banach space. A subset of $E$
that is closed in the weak topology $\sigma(E, E^\star)$ is closed in the strong topology.

In infinite dimension the converse fails: see Examples 1 and 2, `Brezis.Chapter03.example_3_1`
and `Brezis.Chapter03.example_3_2`. -/
theorem remark_3_2_isClosed [CompleteSpace E] {s : Set E}
    (h : IsClosed (toWeakSpace ℝ E '' s)) : IsClosed s :=
  WeakSpace.isClosed_of_isClosed h

/-- **Example 1** of Section 3.2 of [brezis2011functional]. Let $E$ be an infinite-dimensional
Banach space. The unit sphere $S = \{x \in E : \|x\| = 1\}$ is not closed in
$\sigma(E, E^\star)$. More precisely, its closure in $\sigma(E, E^\star)$ is the closed unit
ball $B_E = \{x \in E : \|x\| \le 1\}$, and $B_E$ is closed in $\sigma(E, E^\star)$. -/
theorem example_3_1 [CompleteSpace E] (h : ¬ FiniteDimensional ℝ E) :
    closure (toWeakSpace ℝ E '' sphere (0 : E) 1) = toWeakSpace ℝ E '' closedBall 0 1 ∧
      IsClosed (toWeakSpace ℝ E '' closedBall (0 : E) 1) ∧
      ¬ IsClosed (toWeakSpace ℝ E '' sphere (0 : E) 1) := by
  refine ⟨closure_image_toWeakSpace_sphere h, isClosed_image_toWeakSpace_closedBall 0 1,
    fun hc => ?_⟩
  have h0 : toWeakSpace ℝ E 0 ∈ toWeakSpace ℝ E '' sphere (0 : E) 1 := by
    rw [← hc.closure_eq, closure_image_toWeakSpace_sphere h]
    exact ⟨0, by simp, rfl⟩
  obtain ⟨z, hz, hz0⟩ := h0
  rw [(toWeakSpace ℝ E).injective.eq_iff] at hz0
  rw [hz0, mem_sphere_zero_iff_norm, norm_zero] at hz
  exact zero_ne_one hz

/-- **Example 2** of Section 3.2 of [brezis2011functional]. Let $E$ be an infinite-dimensional
Banach space. The open unit ball $U = \{x \in E : \|x\| < 1\}$ is not open in
$\sigma(E, E^\star)$. -/
theorem example_3_2 [CompleteSpace E] (h : ¬ FiniteDimensional ℝ E) :
    ¬ IsOpen (toWeakSpace ℝ E '' ball (0 : E) 1) :=
  not_isOpen_image_toWeakSpace_ball h

/-- **Remark 3** of [brezis2011functional]. Let $E$ be an infinite-dimensional Banach space. The
weak topology $\sigma(E, E^\star)$ is not metrizable: no metric on $E$ induces it. This is
Exercise 3.8 of the source.

The clause that follows in the source, that $B_E$ with the weak topology is metrizable when
$E^\star$ is separable, is Theorem 3.29. -/
theorem remark_3_3 [CompleteSpace E] (h : ¬ FiniteDimensional ℝ E) :
    ¬ MetrizableSpace (WeakSpace ℝ E) :=
  not_metrizableSpace_weakSpace h

end Brezis.Chapter03
