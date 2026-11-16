/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Numlib.Analysis.Convex.RelativeInterior
import Numlib.Analysis.Normed.Module.Annihilator
import NumlibSurface.Brezis.Chapter01.Section01

/-!
# Brezis, Section 1.2: The geometric forms of the Hahn–Banach theorem

This module formalizes Section 1.2 of [brezis2011functional]: the separation of convex sets in a
real normed space $E$. An affine hyperplane is a set $[f = \alpha] = \{x \in E : f(x) = \alpha\}$,
where $f$ is a linear functional on $E$, not identically zero and not necessarily continuous, and
$\alpha \in \mathbb{R}$. It is closed if and only if $f$ is continuous (Proposition 1.5). The
hyperplane separates two sets $A$ and $B$ if $f \le \alpha$ on $A$ and $f \ge \alpha$ on $B$, and it
separates them strictly if there is a gap $\varepsilon > 0$ on both sides. Two disjoint nonempty
convex sets, one of them open, are separated by a closed hyperplane (Theorem 1.6). If one is closed
and the other compact, they are strictly separated (Theorem 1.7). Consequences are a criterion for a
subspace to be dense (Corollary 1.8 and Remark 5), and the Krein–Milman theorem of the Comments on
Chapter 1 (Theorem 1.13).

The proofs specialize Mathlib's `geometric_hahn_banach_open`, `geometric_hahn_banach_open_point`,
`geometric_hahn_banach_closed_compact`, `gauge` and `closure_convexHull_extremePoints`, the backbone
module `Numlib.Analysis.Convex.Separation`, the backbone theorems
`Submodule.exists_dual_eq_zero_of_notMem` and
`ConvexAnalysis.exists_separatesProperly_iff_disjoint_relint`, and Mathlib's
`LinearMap.continuous_iff_isClosed_ker`.

## Main definitions

* Section 1.2, definition of an affine hyperplane, `Brezis.Chapter01.IsHyperplane`: a level set
  $[f = \alpha]$ of a linear functional $f \neq 0$.
* Section 1.2, definition of separation, `Brezis.Chapter01.Separates`: $f \le \alpha$ on $A$ and
  $f \ge \alpha$ on $B$, identified with the backbone `ConvexAnalysis.Separates` by
  `Brezis.Chapter01.separates_iff`.
* Section 1.2, definition of strict separation, `Brezis.Chapter01.StrictlySeparates`:
  $f \le \alpha - \varepsilon$ on $A$ and $f \ge \alpha + \varepsilon$ on $B$ for some
  $\varepsilon > 0$, identified with the backbone `ConvexAnalysis.SeparatesStrongly` by
  `Brezis.Chapter01.strictlySeparates_iff`.

## Main results

* Proposition 1.5, `Brezis.Chapter01.proposition_1_5`: the hyperplane $[f = \alpha]$ is closed if
  and only if $f$ is continuous.
* Theorem 1.6, `Brezis.Chapter01.theorem_1_6`: two disjoint nonempty convex sets, one of them open,
  are separated by a closed hyperplane.
* Lemma 1.2, `Brezis.Chapter01.lemma_1_2`: the gauge of an open convex set $C \ni 0$ is positively
  homogeneous, subadditive and bounded by a multiple of the norm, and $C = \{p < 1\}$.
* Lemma 1.3, `Brezis.Chapter01.lemma_1_3`: a point outside a nonempty open convex set $C$ is
  separated from $C$ by a closed hyperplane.
* Theorem 1.7, `Brezis.Chapter01.theorem_1_7`: two disjoint nonempty convex sets, one closed and one
  compact, are strictly separated by a closed hyperplane.
* Remark 4, `Brezis.Chapter01.remark_1_4`: in finite dimension, any two disjoint nonempty convex
  sets are separated by a closed hyperplane.
* Corollary 1.8, `Brezis.Chapter01.corollary_1_8`: a subspace that is not dense is annihilated by a
  nonzero continuous linear functional.
* Remark 5, `Brezis.Chapter01.remark_1_5`: a subspace is dense if and only if every continuous
  linear functional that vanishes on it is zero.
* Theorem 1.13, `Brezis.Chapter01.theorem_1_13`: a compact convex set is the closed convex hull of
  its extremal points (Krein–Milman).

## Conventions

* "A closed hyperplane separates $A$ and $B$" is stated as in the source: there are a linear
  functional $f \neq 0$ and $\alpha \in \mathbb{R}$ such that $[f = \alpha]$ is closed and separates
  $A$ and $B$. The functional is `f : E →ₗ[ℝ] ℝ`, and its continuity follows from Proposition 1.5.

## Not formalized

* **Remark 4, first clause (Exercise 1.14).** Two disjoint closed convex subsets of $\ell^1$ that no
  closed hyperplane separates.
-/

open Metric Set

namespace Brezis.Chapter01

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Hyperplanes and separation -/

/-- **Section 1.2** of [brezis2011functional], definition of an affine hyperplane. A subset $H$ of a
real normed space $E$ is an **affine hyperplane** if
$$H = [f = \alpha] = \{x \in E : f(x) = \alpha\}$$
for some linear functional $f$ on $E$ that does not vanish identically and some
$\alpha \in \mathbb{R}$.

As in footnote 3 of the source, $f$ is not assumed to be continuous: it is a linear map
`E →ₗ[ℝ] ℝ`. -/
def IsHyperplane (H : Set E) : Prop :=
  ∃ (f : E →ₗ[ℝ] ℝ) (α : ℝ), f ≠ 0 ∧ H = {x | f x = α}

/-- **Proposition 1.5** of [brezis2011functional]. Let $E$ be a real normed space, $f \neq 0$ a
linear functional on $E$, and $\alpha \in \mathbb{R}$. The hyperplane $[f = \alpha]$ is closed
if and only if $f$ is continuous. -/
theorem proposition_1_5 (f : E →ₗ[ℝ] ℝ) (hf : f ≠ 0) (α : ℝ) :
    IsClosed {x | f x = α} ↔ Continuous f := by
  refine ⟨fun h => ?_, fun h => isClosed_singleton.preimage h⟩
  -- `[f = α]` is a translate of `ker f`
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hf (LinearMap.ext hcon)
  set x₁ : E := (α / f x) • x with hx₁
  have hfx₁ : f x₁ = α := by rw [hx₁, map_smul, smul_eq_mul, div_mul_cancel₀ _ hx]
  have hker : (LinearMap.ker f : Set E) = (fun y => y + x₁) ⁻¹' {x | f x = α} := by
    ext y
    simp [hfx₁]
  rw [LinearMap.continuous_iff_isClosed_ker, hker]
  exact h.preimage (continuous_id.add continuous_const)

/-- **Section 1.2** of [brezis2011functional], definition of separation. Let $f$ be a linear
functional on a real normed space $E$, $\alpha \in \mathbb{R}$, and $A, B \subseteq E$. The
hyperplane $[f = \alpha]$ **separates** $A$ and $B$ if
$$f(x) \le \alpha \quad \text{for all } x \in A \qquad \text{and} \qquad f(x) \ge \alpha \quad
  \text{for all } x \in B.$$

The predicate does not require $f \neq 0$; the theorems state this condition separately. -/
def Separates (f : E →ₗ[ℝ] ℝ) (α : ℝ) (A B : Set E) : Prop :=
  (∀ x ∈ A, f x ≤ α) ∧ ∀ x ∈ B, α ≤ f x

/-- For a continuous linear functional $f$ on $E$, the hyperplane $[f = \alpha]$ separates $A$ and
$B$ in the sense of `Brezis.Chapter01.Separates` if and only if it does so in the sense of the
backbone `ConvexAnalysis.Separates`. -/
theorem separates_iff (f : StrongDual ℝ E) (α : ℝ) (A B : Set E) :
    Separates (f : E →ₗ[ℝ] ℝ) α A B ↔ ConvexAnalysis.Separates f α A B :=
  ⟨fun h => ⟨fun x hx => h.1 x hx, fun x hx => h.2 x hx⟩,
    fun h => ⟨fun _ hx => h.le_of_mem_left hx, fun _ hx => h.le_of_mem_right hx⟩⟩

/-- **Section 1.2** of [brezis2011functional], definition of strict separation. Let $f$ be a linear
functional on a real normed space $E$, $\alpha \in \mathbb{R}$, and $A, B \subseteq E$. The
hyperplane $[f = \alpha]$ **strictly separates** $A$ and $B$ if there is $\varepsilon > 0$ such
that
$$f(x) \le \alpha - \varepsilon \quad \text{for all } x \in A \qquad \text{and} \qquad f(x) \ge
  \alpha + \varepsilon \quad \text{for all } x \in B.$$
-/
def StrictlySeparates (f : E →ₗ[ℝ] ℝ) (α : ℝ) (A B : Set E) : Prop :=
  ∃ ε > 0, (∀ x ∈ A, f x ≤ α - ε) ∧ ∀ x ∈ B, α + ε ≤ f x

/-- For a continuous linear functional $f$ on $E$, the hyperplane $[f = \alpha]$ strictly separates
$A$ and $B$ in the sense of `Brezis.Chapter01.StrictlySeparates` if and only if $f$ separates
$A$ and $B$ strongly in the sense of the backbone `ConvexAnalysis.SeparatesStrongly`, that is,
$\sup_A f < \alpha < \inf_B f$. -/
theorem strictlySeparates_iff (f : StrongDual ℝ E) (α : ℝ) (A B : Set E) :
    StrictlySeparates (f : E →ₗ[ℝ] ℝ) α A B ↔ ConvexAnalysis.SeparatesStrongly f α A B :=
  ConvexAnalysis.separatesStrongly_iff_exists_gap.symm

/-- A nonzero continuous linear functional is nonzero as a linear map. -/
private theorem coe_ne_zero {f : StrongDual ℝ E} (hf : f ≠ 0) : (f : E →ₗ[ℝ] ℝ) ≠ 0 :=
  fun h =>
    hf (ContinuousLinearMap.coe_injective (h.trans ContinuousLinearMap.toLinearMap_zero.symm))

/-! ### The two geometric forms -/

/-- **Theorem 1.6** of [brezis2011functional] (Hahn–Banach theorem, first geometric form). Let $E$
be a real normed space and let $A, B \subseteq E$ be two nonempty convex subsets with
$A \cap B = \emptyset$. Assume that one of them is open. Then there is a closed hyperplane that
separates $A$ and $B$: there are a linear functional $f \neq 0$ and $\alpha \in \mathbb{R}$ such
that $[f = \alpha]$ is closed and
$$f(x) \le \alpha \le f(y) \quad \text{for all } x \in A,\ y \in B.$$

The proof specializes Mathlib's `geometric_hahn_banach_open`; when $B$ is the open set, it
applies that theorem with the roles of $A$ and $B$ exchanged and replaces $f$ and $\alpha$ by
$-f$ and $-\alpha$. -/
theorem theorem_1_6 {A B : Set E} (hA : Convex ℝ A) (hAne : A.Nonempty) (hB : Convex ℝ B)
    (hBne : B.Nonempty) (hAB : Disjoint A B) (hopen : IsOpen A ∨ IsOpen B) :
    ∃ (f : E →ₗ[ℝ] ℝ) (α : ℝ), f ≠ 0 ∧ IsClosed {x | f x = α} ∧ Separates f α A B := by
  obtain ⟨a, ha⟩ := hAne
  obtain ⟨b, hb⟩ := hBne
  rcases hopen with hAo | hBo
  · obtain ⟨f, u, hfA, hfB⟩ := geometric_hahn_banach_open hA hAo hB hAB
    have hne : f ≠ 0 := by
      rintro rfl
      have := (hfA a ha).trans_le (hfB b hb)
      simp at this
    exact ⟨f, u, coe_ne_zero hne, isClosed_eq f.continuous continuous_const,
      fun x hx => (hfA x hx).le, fun x hx => hfB x hx⟩
  · obtain ⟨f, u, hfB, hfA⟩ := geometric_hahn_banach_open hB hBo hA hAB.symm
    have hne : f ≠ 0 := by
      rintro rfl
      have := (hfB b hb).trans_le (hfA a ha)
      simp at this
    refine ⟨-f, -u, coe_ne_zero (neg_ne_zero.2 hne), isClosed_eq (-f).continuous continuous_const,
      fun x hx => ?_, fun x hx => ?_⟩
    · have := hfA x hx
      simp only [LinearMap.neg_apply, ContinuousLinearMap.coe_coe]
      linarith
    · have := hfB x hx
      simp only [LinearMap.neg_apply, ContinuousLinearMap.coe_coe]
      linarith

/-- **Lemma 1.2** of [brezis2011functional], the gauge of a convex set. Let $E$ be a real normed
space and let $C \subseteq E$ be an open convex set with $0 \in C$. Let
$$p(x) = \inf\{\alpha > 0 : \alpha^{-1} x \in C\}$$
be the gauge (Minkowski functional) of $C$. Then $p$ satisfies (1) $p(\lambda x) = \lambda p(x)$
for all $\lambda > 0$ and $x \in E$, (2) $p(x + y) \le p(x) + p(y)$ for all $x, y \in E$, (9)
there is a constant $M$ with $0 \le p(x) \le M \|x\|$ for all $x \in E$, and (10)
$C = \{x \in E : p(x) < 1\}$.

The gauge is Mathlib's `gauge C`. -/
theorem lemma_1_2 {C : Set E} (hC : Convex ℝ C) (hCo : IsOpen C) (h0 : (0 : E) ∈ C) :
    (∀ l : ℝ, 0 < l → ∀ x, gauge C (l • x) = l * gauge C x) ∧
      (∀ x y, gauge C (x + y) ≤ gauge C x + gauge C y) ∧
      (∃ M : ℝ, ∀ x, 0 ≤ gauge C x ∧ gauge C x ≤ M * ‖x‖) ∧
      C = {x | gauge C x < 1} := by
  obtain ⟨r, hr, hrC⟩ := Metric.isOpen_iff.1 hCo 0 h0
  refine ⟨fun l hl x => gauge_smul_of_nonneg hl.le x,
    gauge_add_le hC (absorbent_nhds_zero (hCo.mem_nhds h0)), ⟨r⁻¹, fun x => ⟨gauge_nonneg x, ?_⟩⟩,
    (setOfPred_gauge_lt_one_eq_self_of_isOpen hC h0 hCo).symm⟩
  rw [← div_eq_inv_mul, le_div_iff₀' hr]
  exact mul_gauge_le_norm hrC

/-- **Lemma 1.3** of [brezis2011functional]. Let $E$ be a real normed space, let $C \subseteq E$ be
a nonempty open convex set, and let $x_0 \in E$ with $x_0 \notin C$. Then there is
$f \in E^\star$ with
$$f(x) < f(x_0) \quad \text{for all } x \in C.$$
In particular $f \neq 0$, and the hyperplane $[f = f(x_0)]$ separates $C$ and $\{x_0\}$.

The proof specializes Mathlib's `geometric_hahn_banach_open_point`. -/
theorem lemma_1_3 {C : Set E} (hC : Convex ℝ C) (hCne : C.Nonempty) (hCo : IsOpen C) {x₀ : E}
    (hx₀ : x₀ ∉ C) :
    ∃ f : StrongDual ℝ E, (∀ x ∈ C, f x < f x₀) ∧ f ≠ 0 ∧ Separates f (f x₀) C {x₀} := by
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hC hCo hx₀
  obtain ⟨c, hc⟩ := hCne
  have hne : f ≠ 0 := by
    rintro rfl
    exact lt_irrefl _ (hf c hc)
  exact ⟨f, hf, hne, fun x hx => (hf x hx).le,
    fun x hx => by rw [mem_singleton_iff.1 hx]; exact le_rfl⟩

/-- **Theorem 1.7** of [brezis2011functional] (Hahn–Banach theorem, second geometric form). Let $E$
be a real normed space and let $A, B \subseteq E$ be two nonempty convex subsets with
$A \cap B = \emptyset$. Assume that $A$ is closed and $B$ is compact. Then there is a closed
hyperplane that strictly separates $A$ and $B$: there are a linear functional $f \neq 0$,
$\alpha \in \mathbb{R}$ and $\varepsilon > 0$ such that $[f = \alpha]$ is closed and
$$f(x) \le \alpha - \varepsilon \quad \text{for all } x \in A, \qquad f(y) \ge \alpha +
  \varepsilon \quad \text{for all } y \in B.$$

The proof specializes Mathlib's `geometric_hahn_banach_closed_compact`. -/
theorem theorem_1_7 {A B : Set E} (hA : Convex ℝ A) (hAne : A.Nonempty) (hAc : IsClosed A)
    (hB : Convex ℝ B) (hBne : B.Nonempty) (hBc : IsCompact B) (hAB : Disjoint A B) :
    ∃ (f : E →ₗ[ℝ] ℝ) (α : ℝ), f ≠ 0 ∧ IsClosed {x | f x = α} ∧ StrictlySeparates f α A B := by
  obtain ⟨f, u, v, hfA, huv, hfB⟩ := geometric_hahn_banach_closed_compact hA hAc hB hBc hAB
  have hsep := ConvexAnalysis.separatesStrongly_of_forall_lt hfA huv hfB
  exact ⟨f, (u + v) / 2, coe_ne_zero (hsep.ne_zero hAne hBne),
    isClosed_eq f.continuous continuous_const, (strictlySeparates_iff f _ A B).2 hsep⟩

/-- **Remark 4** of [brezis2011functional], the finite-dimensional case. Let $E$ be a
finite-dimensional real normed space and let $A, B \subseteq E$ be two nonempty convex subsets
with $A \cap B = \emptyset$. Then there is a closed hyperplane that separates $A$ and $B$, with
no further assumption on $A$ and $B$. This is Exercise 1.9 of the source.

The proof specializes the backbone proper-separation theorem
`ConvexAnalysis.exists_separatesProperly_iff_disjoint_relint`. -/
theorem remark_1_4 [FiniteDimensional ℝ E] {A B : Set E} (hA : Convex ℝ A) (hAne : A.Nonempty)
    (hB : Convex ℝ B) (hBne : B.Nonempty) (hAB : Disjoint A B) :
    ∃ (f : E →ₗ[ℝ] ℝ) (α : ℝ), f ≠ 0 ∧ IsClosed {x | f x = α} ∧ Separates f α A B := by
  obtain ⟨f, α, hsep⟩ :=
    (ConvexAnalysis.exists_separatesProperly_iff_disjoint_relint hA hB hAne hBne).2
      (hAB.mono intrinsicInterior_subset intrinsicInterior_subset)
  exact ⟨f, α, coe_ne_zero (hsep.ne_zero hAne hBne), isClosed_eq f.continuous continuous_const,
    (separates_iff f α A B).2 hsep.toSeparates⟩

/-! ### Corollary 1.8 and the density criterion -/

/-- **Corollary 1.8** of [brezis2011functional]. Let $E$ be a real normed space and let
$F \subseteq E$ be a linear subspace with $\overline{F} \neq E$. Then there is $f \in E^\star$,
$f \not\equiv 0$, such that $\langle f, x \rangle = 0$ for all $x \in F$.

The proof specializes the backbone theorem `Submodule.exists_dual_eq_zero_of_notMem`. -/
theorem corollary_1_8 {F : Submodule ℝ E} (hF : F.topologicalClosure ≠ ⊤) :
    ∃ f : StrongDual ℝ E, f ≠ 0 ∧ ∀ x ∈ F, f x = 0 := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ ∉ F.topologicalClosure := by
    by_contra hcon
    push Not at hcon
    exact hF (Submodule.eq_top_iff'.2 hcon)
  obtain ⟨f, hf1, hf0, hfx⟩ :=
    F.topologicalClosure.exists_dual_eq_zero_of_notMem F.isClosed_topologicalClosure hx₀
  exact ⟨f, fun h => hfx (by simp [h]), fun x hx => hf0 x (F.le_topologicalClosure hx)⟩

/-- **Remark 5** of [brezis2011functional]. Let $E$ be a real normed space. A linear subspace
$F \subseteq E$ is dense if and only if every continuous linear functional on $E$ that vanishes
on $F$ vanishes everywhere on $E$. -/
theorem remark_1_5 (F : Submodule ℝ E) :
    Dense (F : Set E) ↔ ∀ f : StrongDual ℝ E, (∀ x ∈ F, f x = 0) → f = 0 := by
  rw [← Submodule.strongDualAnnihilator_eq_bot_iff, Submodule.eq_bot_iff]
  simp only [Submodule.mem_strongDualAnnihilator]

/-! ### The Krein–Milman theorem -/

/-- **Theorem 1.13** of [brezis2011functional] (Krein–Milman), from the Comments on Chapter 1. Let
$E$ be a real normed space and let $K \subseteq E$ be a compact convex set. Then $K$ coincides
with the closed convex hull of its extremal points:
$$K = \overline{\operatorname{conv}}\,(\operatorname{ext} K).$$

The extremal points are Mathlib's `Set.extremePoints`, the convex hull is `convexHull ℝ`, and
the proof specializes `closure_convexHull_extremePoints`. -/
theorem theorem_1_13 {K : Set E} (hK : IsCompact K) (hKc : Convex ℝ K) :
    closure (convexHull ℝ (K.extremePoints ℝ)) = K :=
  closure_convexHull_extremePoints hK hKc

end Brezis.Chapter01
