/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.LinearAlgebra.Dual.Lemmas
import Numlib.Analysis.Normed.Module.Reflexive
import NumlibSurface.Brezis.Chapter02.Section02
import NumlibSurface.Brezis.Chapter03.Section03

/-!
# Brezis, Section 3.4: The weak-∗ topology $\sigma(E^\star, E)$

This module formalizes Section 3.4 of [brezis2011functional] on the dual $E^\star$ of a real Banach
space $E$. The weak-∗ topology $\sigma(E^\star, E)$ is the coarsest topology on $E^\star$ for which
every evaluation $f \mapsto \langle f, x \rangle$, $x \in E$, is continuous. It is coarser than the
weak topology $\sigma(E^\star, E^{\star\star})$, which is coarser than the strong topology. The
module proves that $\sigma(E^\star, E)$ is Hausdorff (Proposition 3.11), describes its neighbourhood
basis (Proposition 3.12) and its convergent sequences (Proposition 3.13), shows that the weak-∗
continuous linear functionals on $E^\star$ are the evaluations at points of $E$ (Proposition 3.14,
Corollary 3.15), and proves the Banach–Alaoglu–Bourbaki theorem: the closed unit ball of $E^\star$
is weak-∗ compact (Theorem 3.16).

The proofs use Mathlib's `WeakDual ℝ E`, its weak representation theorem
`LinearMap.dualEmbedding_surjective` and the algebraic lemma `mem_span_of_iInf_ker_le_ker`,
Mathlib's `WeakDual.isCompact_closedBall`, and the backbone modules
`Numlib.Analysis.Normed.Module.WeakDual` and `Numlib.Analysis.Normed.Module.WeakClosed`. Corollary
3.15 and Remark 11 are proved in this module.

## Main definitions

* Section 3.4, definition of the weak-∗ topology, `Brezis.Chapter03.weakStarTopology`: the coarsest
  topology on $E^\star$ that makes every evaluation at a point of $E$ continuous.
* Section 3.4, the notation $f_n \overset{\star}{\rightharpoonup} f$,
  `Brezis.Chapter03.WeakStarTendsto`: convergence of a sequence in $\sigma(E^\star, E)$.

## Main results

* Section 3.4, `Brezis.Chapter03.weakStarTopology_eq`: $\sigma(E^\star, E)$ is the topology of
  Mathlib's `WeakDual ℝ E`, and it is coarser than $\sigma(E^\star, E^{\star\star})$, which is
  coarser than the strong topology.
* Proposition 3.11, `Brezis.Chapter03.proposition_3_11`: the weak-∗ topology is Hausdorff.
* Proposition 3.12, `Brezis.Chapter03.proposition_3_12`: the sets $V(x_1, \dots, x_k; \varepsilon)$
  form a basis of weak-∗ neighbourhoods of $f_0$.
* Proposition 3.13(i), `Brezis.Chapter03.proposition_3_13`: $f_n \overset{\star}{\rightharpoonup} f$
  if and only if $\langle f_n, x \rangle \to \langle f, x \rangle$ for every $x \in E$.
* Proposition 3.13(ii), `Brezis.Chapter03.proposition_3_13_ii_weak` and
  `Brezis.Chapter03.proposition_3_13_ii_weakStar`: strong convergence implies weak convergence in
  $\sigma(E^\star, E^{\star\star})$, which implies weak-∗ convergence.
* Proposition 3.13(iii), `Brezis.Chapter03.proposition_3_13_iii_bounded` and
  `Brezis.Chapter03.proposition_3_13_iii_liminf`: a weak-∗ convergent sequence is bounded, and
  $\|f\| \le \liminf \|f_n\|$.
* Proposition 3.13(iv), `Brezis.Chapter03.proposition_3_13_iv`: if
  $f_n \overset{\star}{\rightharpoonup} f$ and $x_n \to x$ strongly, then $\langle f_n, x_n \rangle
  \to \langle f, x \rangle$.
* Remark 9, `Brezis.Chapter03.remark_3_9`: in $\ell^2$, weak convergence of $(f_n)$ and $(x_n)$ does
  not give $\langle f_n, x_n \rangle \to \langle f, x \rangle$.
* Remark 10, `Brezis.Chapter03.remark_3_10`: in finite dimension the strong, weak and weak-∗
  topologies on $E^\star$ coincide.
* Proposition 3.14, `Brezis.Chapter03.proposition_3_14`: every weak-∗ continuous linear functional
  on $E^\star$ is the evaluation at some $x_0 \in E$.
* Lemma 3.2, `Brezis.Chapter03.lemma_3_2`: a linear functional that vanishes on the common kernel of
  $\varphi_1, \dots, \varphi_k$ is a linear combination of them.
* Corollary 3.15, `Brezis.Chapter03.corollary_3_15`: a weak-∗ closed hyperplane of $E^\star$ has the
  form $\{f : \langle f, x_0 \rangle = \beta\}$ with $x_0 \in E$, $x_0 \neq 0$.
* Remark 11, `Brezis.Chapter03.remark_3_11`: if the canonical injection $J : E \to E^{\star\star}$
  is not onto, some hyperplane is closed in $\sigma(E^\star, E^{\star\star})$ but not in
  $\sigma(E^\star, E)$.
* Theorem 3.16, `Brezis.Chapter03.theorem_3_16` (Banach–Alaoglu–Bourbaki): the closed unit ball
  $B_{E^\star}$ is compact in $\sigma(E^\star, E)$.

## Conventions

* The dual $E^\star$ is `StrongDual ℝ E` with the norm topology. The same space with the weak-∗
  topology is `WeakDual ℝ E`, and `StrongDual.toWeakDual f` is $f$ seen in `WeakDual ℝ E`. All
  results after the definition are stated on `WeakDual ℝ E`.
* Weak-∗ convergence $f_n \overset{\star}{\rightharpoonup} f$ is
  `Brezis.Chapter03.WeakStarTendsto f g`, with the scoped notation `f ⇀* g`. Weak convergence
  $f_n \rightharpoonup f$ in $\sigma(E^\star, E^{\star\star})$ is `Brezis.Chapter03.WeakTendsto` on
  the Banach space $E^\star$, with the notation `f ⇀ g`.
* The canonical injection $J : E \to E^{\star\star}$ is `NormedSpace.inclusionInDoubleDual ℝ E`.
* The theorems assume that $E$ is complete. Proposition 3.13(iii) and (iv) use it, through the
  uniform boundedness principle in $E$.

## Implementation notes

* In Mathlib's order on topologies, $\tau_1 \le \tau_2$ means that $\tau_1$ is finer than $\tau_2$.
  So "$\sigma(E^\star, E)$ is coarser than $\sigma(E^\star, E^{\star\star})$" is `weakTopology
  (StrongDual ℝ E) ≤ weakStarTopology E`.

## Not formalized

* **Remarks 8 and 12.** They are discussion.
-/

open Filter Metric Set Topology TopologicalSpace NormedSpace

namespace Brezis.Chapter03

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The weak-∗ topology -/

/-- **Section 3.4** of [brezis2011functional], definition of the weak-∗ topology. Let $E$ be a real
normed space. The **weak-∗ topology** $\sigma(E^\star, E)$ on $E^\star$ is the coarsest topology
for which every map $\varphi_x : E^\star \to \mathbb{R}$, $\varphi_x(f) = \langle f, x \rangle$
with $x \in E$, is continuous.

This is the construction of Section 3.1 with $X = E^\star$, $Y_i = \mathbb{R}$ and index set
$I = E$, that is, `Brezis.Chapter03.weakestTopology` of the family of evaluations. -/
@[instance_reducible]
def weakStarTopology (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    TopologicalSpace (StrongDual ℝ E) :=
  weakestTopology (fun x : E => fun f : StrongDual ℝ E => f x)

/-- **Section 3.4** of [brezis2011functional], comparison of the topologies on $E^\star$. Let $E$ be
a real normed space. Then:

1. the topology $\sigma(E^\star, E)$ is the topology induced on $E^\star$ by the identity map
   onto Mathlib's `WeakDual ℝ E`;
2. $\sigma(E^\star, E)$ is coarser than the weak topology $\sigma(E^\star, E^{\star\star})$;
3. $\sigma(E^\star, E^{\star\star})$ is coarser than the strong topology of $E^\star$.

In Mathlib's order on topologies, $\le$ means "finer", so (2) is `weakTopology (StrongDual ℝ E)
≤ weakStarTopology E`. The map onto `WeakDual ℝ E` is `StrongDual.toWeakDual`. -/
theorem weakStarTopology_eq :
    weakStarTopology E =
        TopologicalSpace.induced (StrongDual.toWeakDual : StrongDual ℝ E → WeakDual ℝ E)
          inferInstance ∧
      weakTopology (StrongDual ℝ E) ≤ weakStarTopology E ∧
      (inferInstance : TopologicalSpace (StrongDual ℝ E)) ≤ weakTopology (StrongDual ℝ E) := by
  have heq : weakStarTopology E =
      TopologicalSpace.induced (StrongDual.toWeakDual : StrongDual ℝ E → WeakDual ℝ E)
        inferInstance := by
    change _ = TopologicalSpace.induced (StrongDual.toWeakDual : StrongDual ℝ E → WeakDual ℝ E)
      (TopologicalSpace.induced (fun (f : WeakDual ℝ E) (x : E) => f x) Pi.topologicalSpace)
    rw [induced_compose, induced_to_pi]
    rfl
  refine ⟨heq, ?_, weakTopology_le⟩
  rw [heq, weakTopology_eq]
  have h := continuous_iff_le_induced.1 (WeakDual.continuous_weakSpace_toWeakDual (𝕜 := ℝ) (V := E))
  calc TopologicalSpace.induced (toWeakSpace ℝ (StrongDual ℝ E)) inferInstance
      ≤ TopologicalSpace.induced (toWeakSpace ℝ (StrongDual ℝ E))
        (TopologicalSpace.induced (fun f : WeakSpace ℝ (StrongDual ℝ E) =>
          StrongDual.toWeakDual ((toWeakSpace ℝ (StrongDual ℝ E)).symm f)) inferInstance) :=
        induced_mono h
    _ = TopologicalSpace.induced (StrongDual.toWeakDual : StrongDual ℝ E → WeakDual ℝ E)
        inferInstance := by
        rw [induced_compose]
        rfl

/-- **Proposition 3.11** of [brezis2011functional]. Let $E$ be a real Banach space. The weak-∗
topology $\sigma(E^\star, E)$ is Hausdorff. -/
theorem proposition_3_11 [CompleteSpace E] : T2Space (WeakDual ℝ E) :=
  inferInstance

/-- **Proposition 3.12** of [brezis2011functional]. Let $E$ be a real Banach space and
$f_0 \in E^\star$. For a finite set $\{x_1, \dots, x_k\} \subseteq E$ and $\varepsilon > 0$, the
set
$$V(x_1, \dots, x_k; \varepsilon) = \{f \in E^\star : |\langle f - f_0, x_i \rangle| <
  \varepsilon \text{ for } i = 1, \dots, k\}$$
is a neighbourhood of $f_0$ for $\sigma(E^\star, E)$. These sets, for all finite sets of points
and all $\varepsilon > 0$, form a basis of neighbourhoods of $f_0$ for $\sigma(E^\star, E)$.

The finite set is a `Finset E`, and the basis is indexed by pairs (finite set, $\varepsilon$)
with $\varepsilon > 0$. The neighbourhoods are taken in `WeakDual ℝ E`. -/
theorem proposition_3_12 [CompleteSpace E] (f₀ : StrongDual ℝ E) :
    (∀ (s : Finset E) (ε : ℝ), 0 < ε →
      StrongDual.toWeakDual '' {f | ∀ x ∈ s, |(f - f₀) x| < ε} ∈
        𝓝 (StrongDual.toWeakDual f₀)) ∧
    (𝓝 (StrongDual.toWeakDual f₀)).HasBasis (fun p : Finset E × ℝ => 0 < p.2)
      (fun p => StrongDual.toWeakDual '' {f | ∀ x ∈ p.1, |(f - f₀) x| < p.2}) := by
  have hb := WeakBilin.hasBasis_nhds (topDualPairing ℝ E) (StrongDual.toWeakDual f₀)
  have hset : ∀ (s : Finset E) (ε : ℝ),
      StrongDual.toWeakDual '' {f | ∀ x ∈ s, |(f - f₀) x| < ε} =
        {f : WeakDual ℝ E | ∀ x ∈ s, ‖topDualPairing ℝ E f x -
          topDualPairing ℝ E (StrongDual.toWeakDual f₀) x‖ < ε} := by
    intro s ε
    ext g
    constructor
    · rintro ⟨f, hf, rfl⟩
      intro x hx
      have := hf x hx
      rwa [sub_apply] at this
    · intro hg
      refine ⟨StrongDual.toWeakDual.symm g, fun x hx => ?_,
        StrongDual.toWeakDual.apply_symm_apply g⟩
      rw [sub_apply]
      exact hg x hx
  refine ⟨fun s ε hε => ?_, hb.congr (fun _ => Iff.rfl) fun p _ => (hset p.1 p.2).symm⟩
  rw [hset]
  exact hb.mem_of_mem (i := (s, ε)) hε

/-- **Section 3.4** of [brezis2011functional], the notation
$f_n \overset{\star}{\rightharpoonup} f$. A sequence $(f_n)$ in $E^\star$ **converges weakly-∗**
to $f \in E^\star$, written $f_n \overset{\star}{\rightharpoonup} f$, if it converges to $f$ in
the weak-∗ topology $\sigma(E^\star, E)$.

The scoped notation is `f ⇀* g`. Weak convergence $f_n \rightharpoonup f$ in
$\sigma(E^\star, E^{\star\star})$ is `Brezis.Chapter03.WeakTendsto` on the normed space
$E^\star$. -/
def WeakStarTendsto (f : ℕ → StrongDual ℝ E) (g : StrongDual ℝ E) : Prop :=
  Tendsto (fun n => StrongDual.toWeakDual (f n)) atTop (𝓝 (StrongDual.toWeakDual g))

@[inherit_doc] scoped notation:50 f:51 " ⇀* " g:51 => WeakStarTendsto f g

/-- **Proposition 3.13(i)** of [brezis2011functional]. Let $E$ be a real Banach space, $(f_n)$ a
sequence in $E^\star$ and $f \in E^\star$. Then $f_n \overset{\star}{\rightharpoonup} f$ in
$\sigma(E^\star, E)$ if and only if $\langle f_n, x \rangle \to \langle f, x \rangle$ for every
$x \in E$. -/
theorem proposition_3_13 [CompleteSpace E] (f : ℕ → StrongDual ℝ E) (g : StrongDual ℝ E) :
    f ⇀* g ↔ ∀ x : E, Tendsto (fun n => f n x) atTop (𝓝 (g x)) :=
  tendsto_iff_forall_eval_tendsto_topDualPairing

/-- **Proposition 3.13(ii)** of [brezis2011functional], first statement. Let $E$ be a real Banach
space, $(f_n)$ a sequence in $E^\star$ and $f \in E^\star$. If $f_n \to f$ strongly, then
$f_n \rightharpoonup f$ in $\sigma(E^\star, E^{\star\star})$. -/
theorem proposition_3_13_ii_weak [CompleteSpace E] {f : ℕ → StrongDual ℝ E}
    {g : StrongDual ℝ E} (h : Tendsto f atTop (𝓝 g)) : f ⇀ g :=
  proposition_3_5_ii h

/-- **Proposition 3.13(ii)** of [brezis2011functional], second statement. Let $E$ be a real Banach
space, $(f_n)$ a sequence in $E^\star$ and $f \in E^\star$. If $f_n \rightharpoonup f$ in
$\sigma(E^\star, E^{\star\star})$, then $f_n \overset{\star}{\rightharpoonup} f$ in
$\sigma(E^\star, E)$. -/
theorem proposition_3_13_ii_weakStar [CompleteSpace E] {f : ℕ → StrongDual ℝ E}
    {g : StrongDual ℝ E} (h : f ⇀ g) : f ⇀* g :=
  tendsto_toWeakDual_of_tendsto_toWeakSpace h

/-- **Proposition 3.13(iii)** of [brezis2011functional], boundedness. Let $E$ be a real Banach
space, $(f_n)$ a sequence in $E^\star$ and $f \in E^\star$. If
$f_n \overset{\star}{\rightharpoonup} f$, then $(\|f_n\|)$ is bounded: there is $C$ with
$\|f_n\| \le C$ for all $n$. -/
theorem proposition_3_13_iii_bounded [CompleteSpace E] {f : ℕ → StrongDual ℝ E}
    {g : StrongDual ℝ E} (h : f ⇀* g) : ∃ C : ℝ, ∀ n, ‖f n‖ ≤ C :=
  exists_norm_le_of_tendsto_toWeakDual h

/-- **Proposition 3.13(iii)** of [brezis2011functional], lower semicontinuity of the norm. Let $E$
be a real Banach space, $(f_n)$ a sequence in $E^\star$ and $f \in E^\star$. If
$f_n \overset{\star}{\rightharpoonup} f$, then
$$\|f\| \le \liminf_{n \to \infty} \|f_n\|.$$
-/
theorem proposition_3_13_iii_liminf [CompleteSpace E] {f : ℕ → StrongDual ℝ E}
    {g : StrongDual ℝ E} (h : f ⇀* g) : ‖g‖ ≤ liminf (fun n => ‖f n‖) atTop :=
  norm_le_liminf_norm_of_weakStar_tendsto h

/-- **Proposition 3.13(iv)** of [brezis2011functional]. Let $E$ be a real Banach space, $(f_n)$ a
sequence in $E^\star$, $f \in E^\star$, $(x_n)$ a sequence in $E$ and $x \in E$. If
$f_n \overset{\star}{\rightharpoonup} f$ in $\sigma(E^\star, E)$ and $x_n \to x$ strongly in
$E$, then $\langle f_n, x_n \rangle \to \langle f, x \rangle$. -/
theorem proposition_3_13_iv [CompleteSpace E] {f : ℕ → StrongDual ℝ E} {g : StrongDual ℝ E}
    {x : ℕ → E} {u : E} (hf : f ⇀* g) (hx : Tendsto x atTop (𝓝 u)) :
    Tendsto (fun n => f n (x n)) atTop (𝓝 (g u)) :=
  tendsto_apply_of_tendsto_toWeakDual_of_tendsto hf hx

/-! ### Remark 9: the example in $\ell^2$ -/

/-- The standard unit vectors $e_n$ of $\ell^2$ converge weakly to $0$. -/
private theorem weakTendsto_single_zero :
    (fun n => lp.single 2 n (1 : ℝ) : ℕ → lp (fun _ : ℕ => ℝ) 2) ⇀ 0 := by
  refine tendsto_toWeakSpace_iff.2 fun g => ?_
  obtain ⟨y, rfl⟩ := (InnerProductSpace.toDual ℝ (lp (fun _ : ℕ => ℝ) 2)).surjective g
  simp only [InnerProductSpace.toDual_apply_apply, inner_zero_right]
  refine (Brezis.Chapter02.tendsto_coord_zero y).congr fun n => ?_
  rw [lp.inner_single_right, RCLike.inner_apply, conj_trivial, one_mul]

/-- **Remark 9** in Chapter 3 of [brezis2011functional]. From
$f_n \overset{\star}{\rightharpoonup} f$, or even $f_n \rightharpoonup f$ in
$\sigma(E^\star, E^{\star\star})$, and $x_n \rightharpoonup x$ one cannot conclude
$\langle f_n, x_n \rangle \to \langle f, x \rangle$. In the Hilbert space $\ell^2$, let $e_n$ be the
$n$-th unit vector and $f_n = (e_n, \cdot)$. Then $e_n \rightharpoonup 0$, $f_n \rightharpoonup 0$
in $\sigma(E^\star, E^{\star\star})$, $f_n \overset{\star}{\rightharpoonup} 0$, and
$\langle f_n, e_n \rangle = 1$ for every $n$, so $\langle f_n, e_n \rangle$ does not converge to
$0$.

The space $\ell^2$ is `lp (fun _ : ℕ => ℝ) 2`, the unit vector $e_n$ is `lp.single 2 n 1`, and
$f_n$ is `InnerProductSpace.toDual ℝ _ (e n)`. Coordinates are indexed from $0$. -/
theorem remark_3_9 :
    let e : ℕ → lp (fun _ : ℕ => ℝ) 2 := fun n => lp.single 2 n (1 : ℝ)
    let f : ℕ → StrongDual ℝ (lp (fun _ : ℕ => ℝ) 2) :=
      fun n => InnerProductSpace.toDual ℝ _ (e n)
    e ⇀ 0 ∧ f ⇀ 0 ∧ f ⇀* 0 ∧ (∀ n, f n (e n) = 1) ∧
      ¬ Tendsto (fun n => f n (e n)) atTop
        (𝓝 ((0 : StrongDual ℝ _) (0 : lp (fun _ : ℕ => ℝ) 2))) := by
  intro e f
  have he : e ⇀ 0 := weakTendsto_single_zero
  have hfe : ∀ n, f n (e n) = 1 := fun n => by
    simp only [f, e, InnerProductSpace.toDual_apply_apply, lp.inner_single_right,
      lp.single_apply_self, RCLike.inner_apply, conj_trivial, mul_one]
  have hf : f ⇀ 0 := by
    refine tendsto_toWeakSpace_iff.2 fun ξ => ?_
    -- `ℓ²` is reflexive, so `ξ = J y` for some `y ∈ ℓ²`
    obtain ⟨y, rfl⟩ := NormedSpace.surjective_inclusionInDoubleDual (𝕜 := ℝ)
      (V := lp (fun _ : ℕ => ℝ) 2) ξ
    simp only [f, e, dual_def, InnerProductSpace.toDual_apply_apply, map_zero]
    refine (Brezis.Chapter02.tendsto_coord_zero y).congr fun n => ?_
    rw [lp.inner_single_left, RCLike.inner_apply, conj_trivial, mul_one]
  refine ⟨he, hf, proposition_3_13_ii_weakStar hf, hfe, fun h => ?_⟩
  simp only [hfe, zero_apply] at h
  exact zero_ne_one (tendsto_nhds_unique h tendsto_const_nhds)

/-! ### Finite dimension, the weak representation theorem, and Banach–Alaoglu -/

/-- **Remark 10** in Chapter 3 of [brezis2011functional]. Let $E$ be a finite-dimensional real
Banach space. Then the three topologies on $E^\star$ coincide:
$\sigma(E^\star, E) = \sigma(E^\star, E^{\star\star})$, and $\sigma(E^\star, E^{\star\star})$ is the
strong topology.

The first equality holds because $J : E \to E^{\star\star}$ is onto. The second is Proposition
3.6 for the finite-dimensional space $E^\star$. -/
theorem remark_3_10 [CompleteSpace E] [FiniteDimensional ℝ E] :
    weakStarTopology E = weakTopology (StrongDual ℝ E) ∧
      weakTopology (StrongDual ℝ E) = (inferInstance : TopologicalSpace (StrongDual ℝ E)) := by
  refine ⟨?_, proposition_3_6⟩
  rw [weakStarTopology_eq.1, weakTopology_eq]
  have h₁ := (toWeakDualContinuousLinearEquiv ℝ E).toHomeomorph.isInducing.eq_induced
  have h₂ :=
    (toWeakSpaceContinuousLinearEquiv ℝ (StrongDual ℝ E)).toHomeomorph.isInducing.eq_induced
  exact h₁.symm.trans h₂

/-- **Proposition 3.14** of [brezis2011functional]. Let $E$ be a real Banach space, and let
$\varphi : E^\star \to \mathbb{R}$ be a linear functional that is continuous for the weak-∗
topology $\sigma(E^\star, E)$. Then there is $x_0 \in E$ with
$\varphi(f) = \langle f, x_0 \rangle$ for all $f \in E^\star$.

The statement is given in two forms. In the first form, $\varphi$ is a continuous linear
functional on `WeakDual ℝ E`. In the second form, it is a linear map on `StrongDual ℝ E` that is
continuous for `Brezis.Chapter03.weakStarTopology E`. The proof uses Mathlib's
`LinearMap.dualEmbedding_surjective`. -/
theorem proposition_3_14 [CompleteSpace E] :
    (∀ φ : StrongDual ℝ (WeakDual ℝ E), ∃ x₀ : E, ∀ f : StrongDual ℝ E,
      φ (StrongDual.toWeakDual f) = f x₀) ∧
    ∀ φ : StrongDual ℝ E →ₗ[ℝ] ℝ, Continuous[weakStarTopology E, _] φ →
      ∃ x₀ : E, ∀ f : StrongDual ℝ E, φ f = f x₀ := by
  have hrep : ∀ φ : StrongDual ℝ (WeakDual ℝ E), ∃ x₀ : E, ∀ f : StrongDual ℝ E,
      φ (StrongDual.toWeakDual f) = f x₀ := fun φ => by
    obtain ⟨x₀, hx₀⟩ := LinearMap.dualEmbedding_surjective (topDualPairing ℝ E) φ
    exact ⟨x₀, fun f => by rw [← hx₀]; rfl⟩
  refine ⟨hrep, fun φ hφ => ?_⟩
  rw [weakStarTopology_eq.1] at hφ
  have hsymm : Continuous[inferInstance,
      TopologicalSpace.induced (StrongDual.toWeakDual : StrongDual ℝ E → WeakDual ℝ E)
        inferInstance] (StrongDual.toWeakDual.symm : WeakDual ℝ E → StrongDual ℝ E) :=
    continuous_induced_rng.2 (continuous_id.congr fun _ => rfl)
  have hc : Continuous (fun g : WeakDual ℝ E => φ (StrongDual.toWeakDual.symm g)) :=
    @Continuous.comp (WeakDual ℝ E) (StrongDual ℝ E) ℝ _
      (TopologicalSpace.induced (StrongDual.toWeakDual : StrongDual ℝ E → WeakDual ℝ E)
        inferInstance) _ _ _ hφ hsymm
  obtain ⟨x₀, hx₀⟩ := hrep ⟨φ ∘ₗ StrongDual.toWeakDual.symm.toLinearMap, hc⟩
  exact ⟨x₀, fun f => by simpa using hx₀ f⟩

/-- **Lemma 3.2** of [brezis2011functional]. Let $X$ be a real vector space and let
$\varphi, \varphi_1, \dots, \varphi_k$ be linear functionals on $X$ such that
$$\varphi_i(v) = 0 \text{ for all } i = 1, \dots, k \implies \varphi(v) = 0.$$
Then there are constants $\lambda_1, \dots, \lambda_k \in \mathbb{R}$ with
$\varphi = \sum_{i=1}^k \lambda_i \varphi_i$.

The functionals $\varphi_i$ are indexed by `Fin k`. The proof uses Mathlib's
`mem_span_of_iInf_ker_le_ker`. -/
theorem lemma_3_2 {X : Type*} [AddCommGroup X] [Module ℝ X] {k : ℕ} (φ : X →ₗ[ℝ] ℝ)
    (φ' : Fin k → (X →ₗ[ℝ] ℝ)) (h : ∀ v, (∀ i, φ' i v = 0) → φ v = 0) :
    ∃ lam : Fin k → ℝ, φ = ∑ i, lam i • φ' i := by
  have hmem : φ ∈ Submodule.span ℝ (Set.range φ') :=
    mem_span_of_iInf_ker_le_ker fun v hv => by
      rw [Submodule.mem_iInf] at hv
      exact h v fun i => hv i
  obtain ⟨lam, hlam⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hmem
  exact ⟨lam, hlam.symm⟩

/-- Let $\varphi \neq 0$ be a linear functional on `WeakDual ℝ E`. If a level set
$\{g : \varphi(g) = \alpha\}$ is weak-∗ closed, then $\varphi$ is weak-∗ continuous. -/
private theorem continuous_of_isClosed_level {φ : WeakDual ℝ E →ₗ[ℝ] ℝ} (hφ : φ ≠ 0)
    {α : ℝ} (hH : IsClosed {g : WeakDual ℝ E | φ g = α}) : Continuous φ := by
  obtain ⟨g, hg⟩ : ∃ g, φ g ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hφ (LinearMap.ext hcon)
  set g₁ : WeakDual ℝ E := (α / φ g) • g with hg₁
  have hφg₁ : φ g₁ = α := by rw [hg₁, map_smul, smul_eq_mul, div_mul_cancel₀ _ hg]
  have hker : (LinearMap.ker φ : Set (WeakDual ℝ E)) = (fun y => y + g₁) ⁻¹' {g | φ g = α} := by
    ext y
    simp [hφg₁]
  rw [LinearMap.continuous_iff_isClosed_ker, hker]
  exact hH.preimage (continuous_id.add continuous_const)

/-- **Corollary 3.15** of [brezis2011functional]. Let $E$ be a real Banach space, let
$\varphi : E^\star \to \mathbb{R}$ be a linear functional with $\varphi \neq 0$, and let
$\alpha \in \mathbb{R}$. Suppose that the hyperplane
$H = \{f \in E^\star : \varphi(f) = \alpha\}$ is closed in $\sigma(E^\star, E)$. Then there are
$x_0 \in E$ with $x_0 \neq 0$ and $\beta \in \mathbb{R}$ such that
$$H = \{f \in E^\star : \langle f, x_0 \rangle = \beta\}.$$

The source writes the constant $\alpha$ in place of $\beta$. The two forms are equivalent: if
$\alpha \neq 0$, then $\beta \neq 0$, and $x_0$ can be scaled by $\alpha / \beta$; if
$\alpha = 0$, then $0 \in H$ and so $\beta = 0$. The formal statement does not make this step. -/
theorem corollary_3_15 [CompleteSpace E] {φ : StrongDual ℝ E →ₗ[ℝ] ℝ} (hφ : φ ≠ 0) (α : ℝ)
    (hH : IsClosed (StrongDual.toWeakDual '' {f | φ f = α})) :
    ∃ (x₀ : E) (β : ℝ), x₀ ≠ 0 ∧ {f | φ f = α} = {f | f x₀ = β} := by
  set ψ : WeakDual ℝ E →ₗ[ℝ] ℝ := φ ∘ₗ StrongDual.toWeakDual.symm.toLinearMap with hψ
  have hψφ : ∀ f : StrongDual ℝ E, ψ (StrongDual.toWeakDual f) = φ f := fun f => by simp [hψ]
  have hψ0 : ψ ≠ 0 := by
    intro h
    refine hφ (LinearMap.ext fun f => ?_)
    have := hψφ f
    rw [h] at this
    simpa using this.symm
  have hset : StrongDual.toWeakDual '' {f | φ f = α} = {g : WeakDual ℝ E | ψ g = α} := by
    ext g
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact (hψφ f).trans hf
    · intro hg
      exact ⟨StrongDual.toWeakDual.symm g, by simpa [hψ] using hg,
        StrongDual.toWeakDual.apply_symm_apply g⟩
  rw [hset] at hH
  obtain ⟨x₀, hx₀⟩ := (proposition_3_14 (E := E)).1 ⟨ψ, continuous_of_isClosed_level hψ0 hH⟩
  have hφx : ∀ f : StrongDual ℝ E, φ f = f x₀ := fun f => (hψφ f).symm.trans (hx₀ f)
  refine ⟨x₀, α, fun h0 => hφ (LinearMap.ext fun f => ?_), Set.ext fun f => by rw [mem_ofPred_eq,
    mem_ofPred_eq, hφx]⟩
  rw [hφx, h0, map_zero, LinearMap.zero_apply]

/-- **Remark 11** in Chapter 3 of [brezis2011functional]. Let $E$ be a real Banach space, and
suppose that the canonical injection $J : E \to E^{\star\star}$ is not surjective. Let
$\xi \in E^{\star\star}$ with $\xi \notin J(E)$. Then the hyperplane
$H = \{f \in E^\star : \langle \xi, f \rangle = 0\}$ is closed in $\sigma(E^\star, E^{\star\star})$
but not closed in $\sigma(E^\star, E)$. So $\sigma(E^\star, E)$ is strictly coarser than
$\sigma(E^\star, E^{\star\star})$.

The source concludes that a convex set that is strongly closed need not be weak-∗ closed. The
weak topology $\sigma(E^\star, E^{\star\star})$ is `WeakSpace ℝ (StrongDual ℝ E)`, reached by
`toWeakSpace`. -/
theorem remark_3_11 [CompleteSpace E] {ξ : StrongDual ℝ (StrongDual ℝ E)}
    (hξ : ξ ∉ Set.range (inclusionInDoubleDual ℝ E)) :
    IsClosed (toWeakSpace ℝ (StrongDual ℝ E) '' {f | ξ f = 0}) ∧
      ¬ IsClosed (StrongDual.toWeakDual '' {f | ξ f = 0}) := by
  constructor
  · rw [LinearEquiv.image_eq_preimage_symm]
    exact isClosed_eq (WeakBilin.eval_continuous (topDualPairing ℝ (StrongDual ℝ E)).flip ξ)
      continuous_const
  · intro hH
    have hξ0 : (ξ : StrongDual ℝ E →ₗ[ℝ] ℝ) ≠ 0 := fun h => by
      refine hξ ⟨0, ?_⟩
      rw [map_zero]
      exact (ContinuousLinearMap.coe_injective
        (h.trans ContinuousLinearMap.toLinearMap_zero.symm)).symm
    obtain ⟨x₀, β, hx₀, hset⟩ := corollary_3_15 hξ0 0 hH
    have hβ : β = 0 := by
      have h0 : (0 : StrongDual ℝ E) ∈ {f | (ξ : StrongDual ℝ E →ₗ[ℝ] ℝ) f = 0} := by simp
      rw [hset] at h0
      simpa using h0.symm
    subst hβ
    obtain ⟨lam, hlam⟩ := lemma_3_2 (ξ : StrongDual ℝ E →ₗ[ℝ] ℝ)
      (fun _ : Fin 1 => (inclusionInDoubleDual ℝ E x₀ : StrongDual ℝ E →ₗ[ℝ] ℝ))
      fun f hf => by
        have : f ∈ {f : StrongDual ℝ E | f x₀ = 0} := by simpa using hf 0
        rw [← hset] at this
        exact this
    refine hξ ⟨lam 0 • x₀, ?_⟩
    rw [map_smul]
    refine ContinuousLinearMap.coe_injective ?_
    rw [hlam, Fin.sum_univ_one]
    rfl

/-- **Theorem 3.16** of [brezis2011functional] (Banach–Alaoglu–Bourbaki). Let $E$ be a real Banach
space. The closed unit ball
$$B_{E^\star} = \{f \in E^\star : \|f\| \le 1\}$$
is compact in the weak-∗ topology $\sigma(E^\star, E)$.

The proof is Mathlib's `WeakDual.isCompact_closedBall`. -/
theorem theorem_3_16 [CompleteSpace E] :
    IsCompact (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E) 1) :=
  WeakDual.isCompact_closedBall 0 1

end Brezis.Chapter03
