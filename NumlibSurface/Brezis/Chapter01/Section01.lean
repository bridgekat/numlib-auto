/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Order.Zorn
import Numlib.Analysis.Normed.Module.Reflexive
import Numlib.Analysis.Normed.Module.WeakDual

/-!
# Brezis, Section 1.1: The analytic form of the Hahn–Banach theorem

This module formalizes Section 1.1 of [brezis2011functional]: the analytic form of the Hahn–Banach
theorem and its corollaries. Let $p$ be a function on a real vector space $E$ that is positively
homogeneous and subadditive. A linear functional on a subspace that is dominated by $p$ extends to a
linear functional on all of $E$ that is still dominated by $p$ (Theorem 1.1, proved with Zorn's
lemma, Lemma 1.1). For a real normed space $E$ with dual $E^\star$ and the pairing
$\langle f, x \rangle = f(x)$, the corollaries give the norm-preserving extension of a continuous
functional (Corollary 1.2), a functional $f_0$ with $\|f_0\| = \|x_0\|$ and
$\langle f_0, x_0 \rangle = \|x_0\|^2$ (Corollary 1.3), and the dual description $\|x\| =
\max_{\|f\| \le 1} |\langle f, x \rangle|$ of the norm (Corollary 1.4).

Up to Corollary 1.4 the results restate Mathlib: `exists_extension_of_le_sublinear`,
`exists_extension_norm_eq`, `exists_dual_vector`, and the isometry
`NormedSpace.inclusionInDoubleDualLi` with `ContinuousLinearMap.sSup_unitClosedBall_eq_norm`. Remark
3 uses the backbone modules `Numlib.Analysis.Normed.Module.Reflexive` and
`Numlib.Analysis.Normed.Module.WeakDual`.

## Main definitions

* Remark 2, `Brezis.Chapter01.dualityMap`: the duality map $F(x_0) = \{f_0 \in E^\star : \|f_0\| =
  \|x_0\|,\ \langle f_0, x_0 \rangle = \|x_0\|^2\}$.

## Main results

* Theorem 1.1, `Brezis.Chapter01.theorem_1_1`: a linear functional on a subspace that is dominated
  by a positively homogeneous subadditive $p$ extends to $E$ with the same domination.
* Lemma 1.1, `Brezis.Chapter01.lemma_1_1`: every nonempty inductive ordered set has a maximal
  element (Zorn's lemma).
* Formula (5), `Brezis.Chapter01.dualNorm_eq`: $\|f\| = \sup_{\|x\| \le 1} |f(x)| = \sup_{\|x\| \le
  1} f(x)$.
* Corollary 1.2, `Brezis.Chapter01.corollary_1_2`: a continuous linear functional on a subspace
  extends to $E$ with the same norm.
* Corollary 1.3, `Brezis.Chapter01.corollary_1_3`: for every $x_0$ there is $f_0 \in E^\star$ with
  $\|f_0\| = \|x_0\|$ and $\langle f_0, x_0 \rangle = \|x_0\|^2$.
* Remark 2, `Brezis.Chapter01.dualityMap_nonempty`: the set $F(x_0)$ is nonempty.
* Remark 2, `Brezis.Chapter01.remark_1_2`: if $E^\star$ is strictly convex, then $F(x_0)$ has at
  most one element.
* Corollary 1.4, `Brezis.Chapter01.corollary_1_4`: $\|x\| = \sup_{\|f\| \le 1} |\langle f, x
  \rangle|$, and the supremum is attained.
* Remark 3, `Brezis.Chapter01.remark_1_3`: in a reflexive Banach space the supremum in (5) is
  attained.

## Conventions

* The dual $E^\star$ of a real normed space $E$ is `StrongDual ℝ E` with its operator norm, and
  $\langle f, x \rangle$ is `f x`.

## Implementation notes

* Remark 3 is proved from the backbone reflexivity modules, not from Chapter 3, so that this section
  does not depend on later chapters.

## Not formalized

* **Remark 1.** It is a discussion of Zorn's lemma.
* **Remark 3, converse (James' theorem).** A Banach space in which every $f \in E^\star$ attains its
  norm is reflexive. The source quotes this result without proof.
-/

open Filter Metric NormedSpace Topology

namespace Brezis.Chapter01

/-! ### Theorem 1.1 and Lemma 1.1 -/

/-- **Theorem 1.1** of [brezis2011functional] (Helly, Hahn–Banach theorem, analytic form). Let $E$
be a real vector space and let $p : E \to \mathbb{R}$ satisfy
$$p(\lambda x) = \lambda p(x) \quad \text{for all } \lambda > 0,\ x \in E, \qquad (1)$$
$$p(x + y) \le p(x) + p(y) \quad \text{for all } x, y \in E. \qquad (2)$$
Let $G \subseteq E$ be a linear subspace and $g : G \to \mathbb{R}$ a linear functional with
$g(x) \le p(x)$ for all $x \in G$. Then there is a linear functional $f$ on $E$ that extends
$g$, that is, $f(x) = g(x)$ for all $x \in G$, and satisfies $f(x) \le p(x)$ for all $x \in E$.

The proof specializes Mathlib's `exists_extension_of_le_sublinear`. -/
theorem theorem_1_1 {E : Type*} [AddCommGroup E] [Module ℝ E] (p : E → ℝ)
    (hp₁ : ∀ l : ℝ, 0 < l → ∀ x, p (l • x) = l * p x) (hp₂ : ∀ x y, p (x + y) ≤ p x + p y)
    (G : Submodule ℝ E) (g : G →ₗ[ℝ] ℝ) (hg : ∀ x : G, g x ≤ p x) :
    ∃ f : E →ₗ[ℝ] ℝ, (∀ x : G, f x = g x) ∧ ∀ x, f x ≤ p x :=
  exists_extension_of_le_sublinear ⟨G, g⟩ p hp₁ hp₂ hg

/-- **Lemma 1.1** of [brezis2011functional] (Zorn's lemma). Let $P$ be a nonempty ordered set that
is inductive, that is, every totally ordered subset of $P$ has an upper bound. Then $P$ has a
maximal element: there is $m \in P$ such that $m \le x$ implies $x = m$.

The order is a partial order, `PartialOrder P`, and a totally ordered subset is a chain,
`IsChain (· ≤ ·) c`. -/
theorem lemma_1_1 {P : Type*} [PartialOrder P] [Nonempty P]
    (h : ∀ c : Set P, IsChain (· ≤ ·) c → BddAbove c) : ∃ m : P, ∀ x, m ≤ x → x = m := by
  obtain ⟨m, hm⟩ := zorn_le h
  exact ⟨m, fun x hx => (hm hx).antisymm hx⟩

/-! ### The dual norm and the corollaries -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Formula (5)** of [brezis2011functional], the dual norm. Let $E$ be a real normed space. For
every $f \in E^\star$,
$$\|f\| = \sup_{\|x\| \le 1} |f(x)| = \sup_{\|x\| \le 1} f(x).$$

Here $E^\star$ is `StrongDual ℝ E` and $\|f\|$ is its operator norm. The two suprema are `sSup`
of the images of the closed unit ball `closedBall 0 1`. -/
theorem dualNorm_eq (f : StrongDual ℝ E) :
    ‖f‖ = sSup ((fun x => |f x|) '' closedBall 0 1) ∧
      ‖f‖ = sSup ((fun x => f x) '' closedBall 0 1) := by
  have h₁ : ‖f‖ = sSup ((fun x => |f x|) '' closedBall 0 1) :=
    f.sSup_unitClosedBall_eq_norm.symm
  have hle : ∀ x ∈ closedBall (0 : E) 1, |f x| ≤ ‖f‖ := fun x hx =>
    f.unit_le_opNorm x (mem_closedBall_zero_iff.1 hx)
  have hne : (closedBall (0 : E) 1).Nonempty := nonempty_closedBall.2 zero_le_one
  have hbdd : BddAbove ((fun x => f x) '' closedBall 0 1) := by
    refine ⟨‖f‖, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (le_abs_self _).trans (hle x hx)
  refine ⟨h₁, le_antisymm ?_ ?_⟩
  · rw [h₁]
    refine csSup_le (hne.image _) ?_
    rintro _ ⟨x, hx, rfl⟩
    change |f x| ≤ _
    rcases le_total 0 (f x) with h | h
    · rw [abs_of_nonneg h]
      exact le_csSup hbdd ⟨x, hx, rfl⟩
    · rw [abs_of_nonpos h, ← map_neg]
      exact le_csSup hbdd ⟨-x, by simpa using hx, rfl⟩
  · refine csSup_le (hne.image _) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact (le_abs_self _).trans (hle x hx)

/-- **Corollary 1.2** of [brezis2011functional]. Let $E$ be a real normed space, let $G \subseteq E$
be a linear subspace, and let $g : G \to \mathbb{R}$ be a continuous linear functional. Then
there is $f \in E^\star$ that extends $g$ and satisfies
$$\|f\|_{E^\star} = \|g\|_{G^\star}.$$

The proof specializes Mathlib's `exists_extension_norm_eq`. -/
theorem corollary_1_2 (G : Submodule ℝ E) (g : StrongDual ℝ G) :
    ∃ f : StrongDual ℝ E, (∀ x : G, f x = g x) ∧ ‖f‖ = ‖g‖ :=
  exists_extension_norm_eq G g

/-- **Corollary 1.3** of [brezis2011functional]. Let $E$ be a real normed space. For every
$x_0 \in E$ there is $f_0 \in E^\star$ such that
$$\|f_0\| = \|x_0\| \quad \text{and} \quad \langle f_0, x_0 \rangle = \|x_0\|^2.$$

The proof rescales the functional of Mathlib's `exists_dual_vector`; for $x_0 = 0$ it takes
$f_0 = 0$. -/
theorem corollary_1_3 (x₀ : E) :
    ∃ f₀ : StrongDual ℝ E, ‖f₀‖ = ‖x₀‖ ∧ f₀ x₀ = ‖x₀‖ ^ 2 := by
  by_cases hx : x₀ = 0
  · exact ⟨0, by simp [hx]⟩
  obtain ⟨g, hg₁, hgx⟩ := exists_dual_vector ℝ x₀ (norm_ne_zero_iff.2 hx)
  refine ⟨‖x₀‖ • g, ?_, ?_⟩
  · rw [norm_smul, hg₁, Real.norm_eq_abs, abs_norm, mul_one]
  · rw [smul_apply, hgx, smul_eq_mul, sq]
    rfl

/-- **Remark 2** of [brezis2011functional], the duality map. Let $E$ be a real normed space and
$x_0 \in E$. The **duality map** at $x_0$ is the set
$$F(x_0) = \{f_0 \in E^\star : \|f_0\| = \|x_0\| \text{ and } \langle f_0, x_0 \rangle =
  \|x_0\|^2\}$$
of the functionals that Corollary 1.3 produces. -/
def dualityMap (x₀ : E) : Set (StrongDual ℝ E) :=
  {f₀ | ‖f₀‖ = ‖x₀‖ ∧ f₀ x₀ = ‖x₀‖ ^ 2}

/-- **Remark 2** of [brezis2011functional], nonemptiness of the duality map. For every $x_0$ in a
real normed space $E$, the set $F(x_0)$ is nonempty. This is Corollary 1.3. -/
theorem dualityMap_nonempty (x₀ : E) : (dualityMap x₀).Nonempty :=
  corollary_1_3 x₀

/-- **Remark 2** of [brezis2011functional], uniqueness. Let $E$ be a real normed space whose dual
$E^\star$ is strictly convex, and let $x_0 \in E$. If $f_1, f_2 \in F(x_0)$, then $f_1 = f_2$.
Thus the functional $f_0$ of Corollary 1.3 is unique.

The strict convexity of $E^\star$ is `StrictConvexSpace ℝ (StrongDual ℝ E)`, and $F(x_0)$ is
`Brezis.Chapter01.dualityMap`. -/
theorem remark_1_2 [StrictConvexSpace ℝ (StrongDual ℝ E)] (x₀ : E) {f₁ f₂ : StrongDual ℝ E}
    (h₁ : f₁ ∈ dualityMap x₀) (h₂ : f₂ ∈ dualityMap x₀) : f₁ = f₂ := by
  obtain ⟨hn₁, hv₁⟩ := h₁
  obtain ⟨hn₂, hv₂⟩ := h₂
  by_cases hx : x₀ = 0
  · subst hx
    rw [norm_zero, norm_eq_zero] at hn₁ hn₂
    rw [hn₁, hn₂]
  have hx' : 0 < ‖x₀‖ := norm_pos_iff.2 hx
  have h := (f₁ + f₂).le_opNorm x₀
  rw [add_apply, hv₁, hv₂, Real.norm_of_nonneg (by positivity)] at h
  have hsum : (‖f₁‖ + ‖f₂‖) * ‖x₀‖ ≤ ‖f₁ + f₂‖ * ‖x₀‖ := by
    rw [hn₁, hn₂]
    nlinarith
  exact eq_of_norm_eq_of_norm_add_eq (hn₁.trans hn₂.symm)
    (le_antisymm (norm_add_le _ _) (le_of_mul_le_mul_right hsum hx'))

/-- **Corollary 1.4** of [brezis2011functional], formula (6). Let $E$ be a real normed space. For
every $x \in E$,
$$\|x\| = \sup_{f \in E^\star,\ \|f\| \le 1} |\langle f, x \rangle| = \max_{f \in E^\star,\
  \|f\| \le 1} |\langle f, x \rangle|.$$
That is, the supremum over the closed unit ball of $E^\star$ equals $\|x\|$, and some
$f \in E^\star$ with $\|f\| \le 1$ has $|\langle f, x \rangle| = \|x\|$.

The proof reads the isometry `NormedSpace.inclusionInDoubleDualLi` through
`ContinuousLinearMap.sSup_unitClosedBall_eq_norm`. -/
theorem corollary_1_4 (x : E) :
    ‖x‖ = sSup ((fun f : StrongDual ℝ E => |f x|) '' closedBall 0 1) ∧
      ∃ f : StrongDual ℝ E, ‖f‖ ≤ 1 ∧ |f x| = ‖x‖ := by
  refine ⟨?_, ?_⟩
  · rw [← (inclusionInDoubleDualLi ℝ).norm_map x,
      ← ContinuousLinearMap.sSup_unitClosedBall_eq_norm]
    rfl
  · obtain ⟨f, hf, hfx⟩ := exists_dual_vector'' ℝ x
    exact ⟨f, hf, by rw [hfx, RCLike.ofReal_real_eq_id, id, abs_norm]⟩

/-- **Remark 3** of [brezis2011functional]. Let $E$ be a reflexive Banach space. Then the supremum
in (5) is attained: for every $f \in E^\star$ there is $x \in E$ with $\|x\| \le 1$ and
$\langle f, x \rangle = \|f\|$.

Reflexivity is the backbone class `NormedSpace.IsReflexive`. The proof takes a maximizing
sequence $(x_n)$ in the closed unit ball, from `Brezis.Chapter01.dualNorm_eq`. Reflexivity gives
a weakly convergent subsequence $x_{\varphi(k)} \rightharpoonup x$
(`NormedSpace.exists_subseq_forall_dual_tendsto`). Then $f(x) = \lim f(x_{\varphi(k)}) = \|f\|$,
and $\|x\| \le \liminf \|x_{\varphi(k)}\| \le 1$ because the norm is weakly sequentially lower
semicontinuous (`norm_le_liminf_norm_of_weak_tendsto`). The converse, James' theorem, is quoted
by the source from Diestel and Holmes without proof and is not formalized. -/
theorem remark_1_3 [CompleteSpace E] [NormedSpace.IsReflexive ℝ E] (f : StrongDual ℝ E) :
    ∃ x : E, ‖x‖ ≤ 1 ∧ f x = ‖f‖ := by
  have hne : ((fun x : E => f x) '' closedBall 0 1).Nonempty :=
    (nonempty_closedBall.2 zero_le_one).image _
  have hbdd : BddAbove ((fun x : E => f x) '' closedBall 0 1) := by
    refine ⟨‖f‖, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (le_abs_self _).trans (f.unit_le_opNorm x (mem_closedBall_zero_iff.1 hx))
  obtain ⟨u, -, hu, humem⟩ := exists_seq_tendsto_sSup hne hbdd
  simp only [Set.mem_image] at humem
  choose x hx hfx using humem
  have hxle : ∀ n, ‖x n‖ ≤ 1 := fun n => mem_closedBall_zero_iff.1 (hx n)
  obtain ⟨y, φ, hφ, hlim⟩ := NormedSpace.exists_subseq_forall_dual_tendsto (𝕜 := ℝ) hxle
  have hsup : Tendsto (fun n => f (x n)) atTop (𝓝 ‖f‖) := by
    rw [(dualNorm_eq f).2]
    simpa only [hfx] using hu
  refine ⟨y, ?_, tendsto_nhds_unique (hlim f) (hsup.comp hφ.tendsto_atTop)⟩
  have hweak : Tendsto (fun k => toWeakSpace ℝ E (x (φ k))) atTop (𝓝 (toWeakSpace ℝ E y)) :=
    tendsto_toWeakSpace_iff.2 fun ℓ => hlim ℓ
  refine (norm_le_liminf_norm_of_weak_tendsto hweak).trans ?_
  exact liminf_le_of_frequently_le (Frequently.of_forall fun k => hxle (φ k))
    (isBoundedUnder_of ⟨0, fun k => norm_nonneg _⟩)

end Brezis.Chapter01
