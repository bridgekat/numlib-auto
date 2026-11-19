/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Convex.Combination
import Numlib.Analysis.Convex.Epigraph
import Numlib.Variational.WeakMinimization
import NumlibSurface.Brezis.Chapter03.Section02

/-!
# Brezis, Section 3.3: Weak topology, convex sets, and linear operators

This module formalizes Section 3.3 of [brezis2011functional] for real Banach spaces $E$ and $F$. A
convex subset of $E$ is weakly closed if and only if it is strongly closed (Theorem 3.7, Mazur).
Hence a weakly convergent sequence $x_n \rightharpoonup x$ has convex combinations of its terms that
converge strongly to $x$ (Corollary 3.8), and a closed convex set is the intersection of the closed
half-spaces that contain it (Remark 5). A convex function $\varphi : E \to (-\infty, +\infty]$ that
is lower semicontinuous in the strong topology is lower semicontinuous in the weak topology
(Corollary 3.9). A linear operator $T : E \to F$ is continuous for the strong topologies if and only
if it is continuous for the weak topologies (Theorem 3.10).

Theorem 3.7, Corollary 3.9, Remark 6, Theorem 3.10 and Remark 7 restate the backbone module
`Numlib.Analysis.Normed.Module.WeakClosed`. Corollary 3.8 restates the backbone theorem
`exists_seq_convexCombination_tendsto` of `Numlib.Variational.WeakMinimization`. Remark 5 is
Mathlib's `RCLike.iInter_halfSpaces_eq'` for the field $\mathbb{R}$.

## Main results

* Theorem 3.7, `Brezis.Chapter03.theorem_3_7`: a convex set is weakly closed if and only if it is
  strongly closed (Mazur).
* Corollary 3.8, `Brezis.Chapter03.corollary_3_8`: if $x_n \rightharpoonup x$, then convex
  combinations of the $x_n$ converge strongly to $x$ (Mazur's lemma).
* Remark 5, `Brezis.Chapter03.remark_3_5`: a closed convex set is the intersection of the closed
  half-spaces that contain it.
* Corollary 3.9, `Brezis.Chapter03.corollary_3_9`: a convex function that is strongly lower
  semicontinuous is weakly lower semicontinuous.
* Remark 6, `Brezis.Chapter03.remark_3_6`: a convex continuous function, in particular the norm, is
  weakly lower semicontinuous, and $x_n \rightharpoonup x$ implies $\|x\| \le \liminf \|x_n\|$.
* Theorem 3.10, `Brezis.Chapter03.theorem_3_10`: a linear operator is strongly continuous if and
  only if it is weakly continuous.
* Remark 7, `Brezis.Chapter03.remark_3_7`: a linear operator that is continuous from $E$ strong into
  $F$ weak is continuous from $E$ strong into $F$ strong.

## Conventions

* A function $\varphi : E \to (-\infty, +\infty]$ is a function `E → EReal`, convex in the sense of
  `ConvexAnalysis.ConvexFn` and lower semicontinuous in the sense of `LowerSemicontinuous`, as in
  Section 1.4.
* The weak topology is that of `WeakSpace ℝ E`, as in Section 3.2.

## Deviations from the source

* **Corollary 3.8** (generalization). Each convex combination can use only terms in the
  corresponding tail. See `Brezis.Chapter03.corollary_3_8`.
* **Corollary 3.9** (generalization). The weak lower semicontinuity result also permits
  function values of $-\infty$. See `Brezis.Chapter03.corollary_3_9`.
* **Remark 6** (reading). The continuous convex function is taken to be real-valued. See
  `Brezis.Chapter03.remark_3_6`.

## Not formalized

* **Remark 7, second clause (Exercise 6.7).** A linear operator is continuous from $E$ weak into $F$
  strong if and only if it has finite rank.
* **Remark 7, last paragraph (Exercise 4.20).** The case of nonlinear maps.
-/

open Filter Metric Set Topology

namespace Brezis.Chapter03

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **Theorem 3.7** of [brezis2011functional] (Mazur). Let $E$ be a Banach space and let
$C \subseteq E$ be convex. Then $C$ is closed in the weak topology $\sigma(E, E^\star)$ if and
only if it is closed in the strong topology. -/
theorem theorem_3_7 [CompleteSpace E] {C : Set E} (hC : Convex ℝ C) :
    IsClosed (toWeakSpace ℝ E '' C) ↔ IsClosed C :=
  hC.isClosed_image_toWeakSpace_iff

/-- **Corollary 3.8** of [brezis2011functional] (Mazur's lemma). Let $E$ be a Banach space and
assume that $x_n \rightharpoonup x$ weakly in $\sigma(E, E^\star)$. Then there is a sequence
$(y_n)$ of convex combinations of the $x_n$ that converges strongly to $x$.

The statement has two parts. First, the combinations can be taken from the tails: there are
$N(n) \ge n$ and weights $\lambda_{n,i} \ge 0$ with $\sum_{i=n}^{N(n)} \lambda_{n,i} = 1$ such
that
$$\sum_{i=n}^{N(n)} \lambda_{n,i} x_i \to x \quad \text{strongly}.$$
Second, there is a sequence $(y_n)$ in the convex hull of $\{x_n : n \in \mathbb{N}\}$ with
$y_n \to x$ strongly.

**Generalization.** The source places each convex combination in the hull of the whole sequence.
The first clause takes the combination from the $n$th tail, since each tail has the same weak
limit. -/
theorem corollary_3_8 [CompleteSpace E] {x : ℕ → E} {u : E} (h : x ⇀ u) :
    (∃ (N : ℕ → ℕ) (lam : ℕ → ℕ → ℝ), (∀ n, n ≤ N n) ∧ (∀ n i, 0 ≤ lam n i) ∧
      (∀ n, ∑ i ∈ Finset.Icc n (N n), lam n i = 1) ∧
      Tendsto (fun n => ∑ i ∈ Finset.Icc n (N n), lam n i • x i) atTop (𝓝 u)) ∧
    ∃ y : ℕ → E, (∀ n, y n ∈ convexHull ℝ (Set.range x)) ∧ Tendsto y atTop (𝓝 u) := by
  obtain ⟨N, lam, hN, hlam0, hlam1, hlim⟩ :=
    exists_seq_convexCombination_tendsto (weakSeqTendsto_iff_tendsto_toWeakSpace.2 h)
  refine ⟨⟨N, lam, hN, hlam0, hlam1, hlim⟩, fun n => ∑ i ∈ Finset.Icc n (N n), lam n i • x i,
    fun n => ?_, hlim⟩
  exact (convex_convexHull ℝ _).sum_mem (fun i _ => hlam0 n i) (hlam1 n)
    fun i _ => subset_convexHull ℝ _ ⟨i, rfl⟩

/-- **Remark 5** of [brezis2011functional]. Let $E$ be a Banach space and let $C \subseteq E$ be a
closed convex set. Then $C$ coincides with the intersection of all the closed half-spaces that
contain $C$:
$$C = \bigcap \{\{x \in E : \langle f, x \rangle \le c\} : f \in E^\star,\ c \in \mathbb{R},\
  \langle f, y \rangle \le c \ \forall y \in C\}.$$
-/
theorem remark_3_5 [CompleteSpace E] {C : Set E} (hC : Convex ℝ C) (hCc : IsClosed C) :
    ⋂ (f : StrongDual ℝ E) (c : ℝ) (_ : ∀ y ∈ C, f y ≤ c), {x | f x ≤ c} = C := by
  have := RCLike.iInter_halfSpaces_eq' (𝕜 := ℝ) hC hCc
  simpa only [RCLike.re_to_real] using this

/-- **Corollary 3.9** of [brezis2011functional]. Let $E$ be a Banach space and let
$\varphi : E \to [-\infty, +\infty]$ be convex and lower semicontinuous in the strong topology.
Then $\varphi$ is lower semicontinuous in the weak topology $\sigma(E, E^\star)$.

**Generalization.** The source excludes values of $-\infty$. The proof through weak closedness
of real sublevel sets also applies at those values.

The weak lower semicontinuity is `LowerSemicontinuous (φ ∘ (toWeakSpace ℝ E).symm)` on
`WeakSpace ℝ E`. -/
theorem corollary_3_9 [CompleteSpace E] {φ : E → EReal} (hφ : ConvexAnalysis.ConvexFn φ)
    (hlsc : LowerSemicontinuous φ) : LowerSemicontinuous (φ ∘ (toWeakSpace ℝ E).symm) :=
  hlsc.comp_toWeakSpace_symm_of_convex_le (𝕜 := ℝ) fun b => hφ.convex_le b

/-- **Remark 6** of [brezis2011functional]. Let $E$ be a Banach space. A convex function
$\varphi : E \to \mathbb{R}$ that is continuous in the strong topology is lower semicontinuous
in the weak topology $\sigma(E, E^\star)$. In particular the norm $\varphi(x) = \|x\|$ is weakly
lower semicontinuous, and $x_n \rightharpoonup x$ implies
$$\|x\| \le \liminf_{n \to \infty} \|x_n\|,$$
which is Proposition 3.5(iii) again.

**Reading.** The source states the implication for a continuous convex function in the
setting of Corollary 3.9. The declaration uses a real-valued function, as in the norm example.
The version for extended-real-valued continuous functions follows from
`Brezis.Chapter03.corollary_3_9`. -/
theorem remark_3_6 [CompleteSpace E] :
    (∀ φ : E → ℝ, ConvexOn ℝ Set.univ φ → Continuous φ →
      LowerSemicontinuous (φ ∘ (toWeakSpace ℝ E).symm)) ∧
    LowerSemicontinuous (fun x : WeakSpace ℝ E => ‖(toWeakSpace ℝ E).symm x‖) ∧
    ∀ (x : ℕ → E) (u : E), x ⇀ u → ‖u‖ ≤ liminf (fun n => ‖x n‖) atTop :=
  ⟨fun _ hφ hc => hφ.lowerSemicontinuous_comp_toWeakSpace_symm (𝕜 := ℝ) hc.lowerSemicontinuous,
    lowerSemicontinuous_norm_comp_toWeakSpace_symm (𝕜 := ℝ),
    fun _ _ h => proposition_3_5_iii_liminf h⟩

/-- **Theorem 3.10** of [brezis2011functional]. Let $E$ and $F$ be two Banach spaces and let $T$ be
a linear operator from $E$ into $F$. Then $T$ is continuous in the strong topologies if and only
if $T$ is continuous from $E$ weak $\sigma(E, E^\star)$ into $F$ weak $\sigma(F, F^\star)$. -/
theorem theorem_3_10 [CompleteSpace E] [CompleteSpace F] (T : E →ₗ[ℝ] F) :
    Continuous T ↔
      Continuous (fun x : WeakSpace ℝ E => toWeakSpace ℝ F (T ((toWeakSpace ℝ E).symm x))) :=
  T.continuous_iff_continuous_weakSpace

/-- **Remark 7** of [brezis2011functional]. Let $E$ and $F$ be two Banach spaces and let
$T : E \to F$ be a linear operator that is continuous from $E$ strong into $F$ weak. Then $T$ is
continuous from $E$ strong into $F$ strong. Thus for linear operators the continuity from strong
to strong, from weak to weak, and from strong to weak are the same property. -/
theorem remark_3_7 [CompleteSpace E] [CompleteSpace F] (T : E →ₗ[ℝ] F)
    (hT : Continuous (fun x => toWeakSpace ℝ F (T x))) : Continuous T :=
  T.continuous_of_continuous_toWeakSpace_comp hT

end Brezis.Chapter03
