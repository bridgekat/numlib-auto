/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Continuity
import Numlib.Analysis.Convex.Polyhedral.Defs
import Numlib.Analysis.Convex.Polyhedral.Ops
import Numlib.Analysis.Convex.Representation
import Numlib.Analysis.Convex.Subdifferential.Defs

/-!
# The maximum of a convex function

The maximization of a convex function $f$ over a set $C$ behaves very differently from its
minimization. By the **maximum principle**, if $f$ attains its supremum over $C$ at a relative
interior point of $C$, then $f$ is constant on $C$. Thus maxima lie on the boundary: on faces of
$C$, and finally at extreme points. The convex hull raises neither the supremum nor the set of
maximum values. Hence the supremum over a closed convex set is already the supremum over its
relative boundary, and, if $C$ contains no lines and $f$ is bounded above on each half-line in $C$,
the supremum over the extreme points of $C$. This follows [rockafellar1970convex], §32.

The boundedness on half-lines is what makes the extreme directions unnecessary. For $f(x) = x$ on
$C = [0, \infty)$, the supremum over $C$ is $+\infty$, but the value at the only extreme point is
$0$. The statement `ConvexAnalysis.ConvexFn.iSup_extremePoints_add_coneHull` keeps the extreme
directions and needs no boundedness hypothesis.

## Main definitions

* `ConvexAnalysis.BddAboveOnRays`: $f$ is bounded above on every closed half-line in $C$. The
  direction $0$ makes this condition include $C \subseteq \operatorname{dom} f$.

## Main results

* `ConvexAnalysis.ConvexFn.eq_of_isMaxOn_mem_relint`: the maximum principle, Theorem 32.1 of
  [rockafellar1970convex].
* `ConvexAnalysis.exists_isFace_forall_eq_of_isMaxOn`: every maximizer lies in a face of $C$ on
  which $f$ is constant.
* `ConvexAnalysis.ConvexFn.iSup_convexHull`, `ConvexAnalysis.exists_eq_of_isMaxOn_convexHull`: the
  convex hull raises neither the supremum nor the set of maximum values.
* `ConvexAnalysis.ConvexFn.iSup_sdiff_relint`, `ConvexAnalysis.exists_notMem_relint_eq_of_isMaxOn`:
  the relative boundary carries the supremum and a maximizer.
* `ConvexAnalysis.ConvexFn.iSup_extremePoints_of_containsNoLine`,
  `ConvexAnalysis.ConvexFn.iSup_extremePoints_inter_of_isCompl`,
  `ConvexAnalysis.ConvexFn.iSup_extremePoints_add_coneHull`: the extreme point principle, Theorem
  32.3 of [rockafellar1970convex], for a set $C$ that contains no lines, for a general $C$
  intersected with a complement of its lineality space, and in the form of the representation of
  $C$.
* `ConvexAnalysis.exists_isMaxOn_of_polyhedral_of_bddAboveOnRays`,
  `ConvexAnalysis.exists_mem_extremePoints_isMaxOn_of_finitelyGenerated`: attainment of the supremum
  over a polyhedral set and over a finitely generated set.
* `ConvexAnalysis.ConvexFn.iSup_extremePoints`,
  `ConvexAnalysis.exists_mem_extremePoints_isMaxOn_of_isCompact`: the compact case.
* `ConvexAnalysis.mem_normalCone_of_mem_subdifferential_of_isMaxOn`: at a maximizer, every
  subgradient is a normal vector of $C$.

## Implementation notes

* A maximizer is Mathlib's `IsMaxOn f C x`, which is $f(z) \le f(x)$ for all $z \in C$. It does not
  require $x \in C$.
* The lineality space $L$ of $C$ is removed by intersection with a complement $N$ of $L$, not by the
  quotient $E / L$. The decomposition $C = L + (C \cap N)$ holds for every complement $N$, so no
  inner product is needed. [rockafellar1970convex] takes $N = L^\perp$.
* For the attainment over a compact set,
  `ConvexAnalysis.exists_mem_extremePoints_isMaxOn_of_isCompact` assumes $C \subseteq
  \operatorname{ri}(\operatorname{dom} f)$. Under the hypothesis $C \subseteq \operatorname{dom} f$
  of [rockafellar1970convex], the attainment claim is false.
-/

open scoped Pointwise

namespace ConvexAnalysis

/-! ### The maximum principle -/

section Relint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → EReal} {C : Set E}

/-- **The maximum principle.** Let $E$ be a real normed space, let $f : E \to [-\infty, +\infty]$ be
convex, and let $C \subseteq \operatorname{dom} f$. If $f$ attains its supremum over $C$ at a
point $z \in \operatorname{ri} C$, then $f$ is constant on $C$: $f(x) = f(z)$ for all $x \in C$.

This is Theorem 32.1 of [rockafellar1970convex]. The Lean statement does not assume that $C$ is
convex. -/
theorem ConvexFn.eq_of_isMaxOn_mem_relint (hf : ConvexFn f) (hCdom : C ⊆ convexDom f) {z : E}
    (hz : z ∈ ri C) (hmax : IsMaxOn f C z) {x : E} (hx : x ∈ C) : f x = f z := by
  rw [isMaxOn_iff] at hmax
  refine le_antisymm (hmax x hx) ?_
  by_contra hcon
  have hxlt : f x < f z := not_le.1 hcon
  obtain ⟨t, ht, hy⟩ := exists_one_lt_smul_mem_of_mem_relint hz (subset_affineSpan ℝ C hx)
  have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
  have htinv0 : (0 : ℝ) < t⁻¹ := inv_pos.2 ht0
  have htinv1 : t⁻¹ < 1 := by
    have hcancel : t * t⁻¹ = 1 := mul_inv_cancel₀ ht0.ne'
    nlinarith
  obtain ⟨ζ, hζ⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (ne_bot_of_gt hxlt)
    (mem_convexDom.1 (hCdom (intrinsicInterior_subset hz)))
  rw [hζ] at hxlt
  obtain ⟨ξ, hξ1, hξ2⟩ := EReal.lt_iff_exists_real_btwn.1 hxlt
  have hξlt : ξ < ζ := by exact_mod_cast hξ2
  have hcomb := hf.epi_combo hξ1.le ((hmax _ hy).trans hζ.le)
    (by linarith : (0 : ℝ) ≤ 1 - t⁻¹) htinv0.le (by ring)
  rw [combo_prolong x z ht0.ne', hζ, EReal.coe_le_coe_iff] at hcomb
  nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - t⁻¹) (by linarith : (0 : ℝ) < ζ - ξ)]

/-- Let $E$ be a finite-dimensional real normed space, let $f$ be convex, and let
$C \subseteq \operatorname{dom} f$ be convex. If $z \in C$ maximizes $f$ over $C$, then there is
a face $C'$ of $C$ with $z \in C'$ on which $f$ is constant: $f(x) = f(z)$ for all $x \in C'$.

Thus the set of maximizers is a union of faces. The proof applies the maximum principle on the
face whose relative interior contains $z$. -/
theorem exists_isFace_forall_eq_of_isMaxOn [FiniteDimensional ℝ E] (hf : ConvexFn f)
    (hC : Convex ℝ C) (hCdom : C ⊆ convexDom f) {z : E} (hz : z ∈ C) (hmax : IsMaxOn f C z) :
    ∃ C', IsFace C C' ∧ z ∈ C' ∧ ∀ x ∈ C', f x = f z := by
  obtain ⟨C', hface, hzri⟩ := exists_isFace_mem_relint hC hz
  have hsub : C' ⊆ C := hface.toIsExtreme.1
  exact ⟨C', hface, intrinsicInterior_subset hzri,
    fun x hx => hf.eq_of_isMaxOn_mem_relint (hsub.trans hCdom) hzri
      (hmax.of_subset hsub) hx⟩

end Relint

/-! ### Passing to the convex hull -/

section Hull

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f : E → EReal} {S : Set E}

/-- **The convex hull does not raise the supremum.** Let $f$ be convex and let $S \subseteq E$. Then
$$\sup_{x \in \operatorname{conv} S} f(x) = \sup_{x \in S} f(x).$$

The sublevel set of $f$ at the supremum over $S$ is convex and contains $S$, so it contains
$\operatorname{conv} S$. -/
theorem ConvexFn.iSup_convexHull (hf : ConvexFn f) (S : Set E) :
    (⨆ x ∈ convexHull ℝ S, f x) = ⨆ x ∈ S, f x := by
  refine le_antisymm (iSup₂_le fun x hx => ?_)
    (iSup₂_le fun x hx => le_iSup₂ (f := fun z (_ : z ∈ convexHull ℝ S) => f z) x
      (subset_convexHull ℝ S hx))
  exact convexHull_min (fun z hz => le_iSup₂ (f := fun w (_ : w ∈ S) => f w) z hz)
    (hf.convex_le _) hx

/-- **The convex hull creates no new maximum values.** Let $f$ be convex and let $S \subseteq E$. If
$x \in \operatorname{conv} S$ maximizes $f$ over $\operatorname{conv} S$, then $f(z) = f(x)$ for
some $z \in S$.

The proof uses that the strict sublevel set is convex as well. -/
theorem exists_eq_of_isMaxOn_convexHull (hf : ConvexFn f) {x : E} (hx : x ∈ convexHull ℝ S)
    (hmax : IsMaxOn f (convexHull ℝ S) x) : ∃ z ∈ S, f z = f x := by
  by_contra hcon
  push Not at hcon
  have hlt : S ⊆ {w : E | f w < f x} := fun z hz =>
    lt_of_le_of_ne (hmax (subset_convexHull ℝ S hz)) (hcon z hz)
  exact absurd (convexHull_min hlt (hf.convex_lt (f x)) hx) (lt_irrefl (f x))

end Hull

/-! ### The supremum over the relative boundary -/

section Boundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {C : Set E}

/-- Let $C$ be a closed convex subset of a finite-dimensional real normed space, and let $C$ be
neither an affine set nor a closed half of an affine set. Then $C$ is the convex hull of its
relative boundary: $\operatorname{conv}(C \setminus \operatorname{ri} C) = C$. -/
theorem convexHull_sdiff_relint (hC : Convex ℝ C) (hCcl : IsClosed C) (hhalf : ¬ IsAffineHalf C) :
    convexHull ℝ (C \ ri C) = C := by
  refine subset_antisymm (convexHull_min Set.sdiff_subset hC) fun w hw => ?_
  by_cases hwri : w ∈ ri C
  · obtain ⟨a, haC, b, hbC, hari, hbri, hseg⟩ :=
      exists_notMem_relint_mem_segment_of_not_isAffineHalf hC hCcl hhalf hwri
    exact (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ (C \ ri C) ⟨haC, hari⟩)
      (subset_convexHull ℝ (C \ ri C) ⟨hbC, hbri⟩) hseg
  · exact subset_convexHull ℝ (C \ ri C) ⟨hw, hwri⟩

/-- **The relative boundary carries the supremum.** Let $f$ be convex, and let $C$ be a closed
convex subset of a finite-dimensional real normed space that is neither an affine set nor a
closed half of an affine set. Then
$$\sup_{x \in C} f(x) = \sup_{x \in C \setminus \operatorname{ri} C} f(x).$$

The hypothesis on $C$ cannot be dropped: for $C = [0, \infty)$ the relative boundary is $\{0\}$,
but $f(x) = x$ has supremum $+\infty$ over $C$. The condition "an affine set or a closed half of
an affine set" is `ConvexAnalysis.IsAffineHalf`. -/
theorem ConvexFn.iSup_sdiff_relint (hf : ConvexFn f) (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hhalf : ¬ IsAffineHalf C) : (⨆ x ∈ C, f x) = ⨆ x ∈ C \ ri C, f x := by
  conv_lhs => rw [← convexHull_sdiff_relint hC hCcl hhalf]
  exact hf.iSup_convexHull _

/-- **The relative boundary carries a maximizer.** Under the hypotheses of
`ConvexAnalysis.ConvexFn.iSup_sdiff_relint`, if $x \in C$ maximizes $f$ over $C$, then there is
$z \in C \setminus \operatorname{ri} C$ with $f(z) = f(x)$. -/
theorem exists_notMem_relint_eq_of_isMaxOn (hf : ConvexFn f) (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hhalf : ¬ IsAffineHalf C) {x : E} (hx : x ∈ C) (hmax : IsMaxOn f C x) :
    ∃ z ∈ C \ ri C, f z = f x := by
  rw [← convexHull_sdiff_relint hC hCcl hhalf] at hmax
  rw [← convexHull_sdiff_relint hC hCcl hhalf] at hx
  exact exists_eq_of_isMaxOn_convexHull hf hx hmax

/-- Let $f$ be convex, and let $C$ be a nonempty closed convex subset of a finite-dimensional real
normed space that contains no lines and has dimension at least $2$. Then $\sup_{x \in C} f(x) =
\sup_{x \in C \setminus \operatorname{ri} C} f(x)$.

Such a set is neither an affine set nor a closed half of an affine set. The dimension of $C$ is
the dimension of `vectorSpan ℝ C`. -/
theorem ConvexFn.iSup_sdiff_relint_of_containsNoLine (hf : ConvexFn f) (hC : Convex ℝ C)
    (hCcl : IsClosed C) (hnl : ContainsNoLine C) (hne : C.Nonempty)
    (hdim : 2 ≤ Module.finrank ℝ (vectorSpan ℝ C)) :
    (⨆ x ∈ C, f x) = ⨆ x ∈ C \ ri C, f x :=
  hf.iSup_sdiff_relint hC hCcl fun h => not_containsNoLine_of_isAffineHalf h hne hdim hnl

end Boundary

/-! ### The extreme point principle -/

section Ray

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f : E → EReal} {C : Set E}

/-- **A convex function bounded above on a half-line does not increase along it.** Let $f$ be
convex, $u, v \in E$ and $\beta \in \mathbb{R}$. If $f(u + t v) \le \beta$ for every $t \ge 0$,
then $f(u + v) \le f(u)$. -/
theorem ConvexFn.add_le_of_forall_add_smul_le (hf : ConvexFn f) {u v : E} {β : ℝ}
    (hray : ∀ t : ℝ, 0 ≤ t → f (u + t • v) ≤ (β : EReal)) : f (u + v) ≤ f u := by
  by_contra hcon
  have hlt : f u < f (u + v) := not_le.1 hcon
  obtain ⟨ξ, hξ1, hξ2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  obtain ⟨η, hη1, hη2⟩ := EReal.lt_iff_exists_real_btwn.1 hξ2
  have hξη : ξ < η := by exact_mod_cast hη1
  set t : ℝ := max 1 (1 + (β - ξ) / (η - ξ)) with ht
  have ht1 : (1 : ℝ) ≤ t := le_max_left _ _
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
  have hcancel : (β - ξ) / (η - ξ) * (η - ξ) = β - ξ := div_mul_cancel₀ _ (by linarith)
  have hkey : β - ξ < t * (η - ξ) := by
    nlinarith [le_max_right (1 : ℝ) (1 + (β - ξ) / (η - ξ))]
  have hcomb := hf.epi_combo hξ1.le (hray t ht0.le) (a := 1 - t⁻¹) (b := t⁻¹)
    (by simp [inv_le_one_of_one_le₀ ht1]) (by positivity) (by ring)
  have hpt : (1 - t⁻¹) • u + t⁻¹ • (u + t • v) = u + v := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ ht0.ne', one_smul, sub_smul, one_smul]
    abel
  rw [hpt] at hcomb
  have hηlt : (η : EReal) < (((1 - t⁻¹) * ξ + t⁻¹ * β : ℝ) : EReal) := lt_of_lt_of_le hη2 hcomb
  have hηlt' : η < (1 - t⁻¹) * ξ + t⁻¹ * β := by exact_mod_cast hηlt
  have hinv0 : (0 : ℝ) < t⁻¹ := inv_pos.2 ht0
  have hmul : t⁻¹ * (β - ξ) < η - ξ := by
    have h := mul_lt_mul_of_pos_left hkey hinv0
    rwa [← mul_assoc, inv_mul_cancel₀ ht0.ne', one_mul] at h
  linarith

/-- **A convex function bounded above on $C$ does not increase along a direction of recession of
$C$.** Let $f$ be convex with $f \le \beta$ on $C$ for some $\beta \in \mathbb{R}$. If $u \in C$
and $v \in 0^+ C$, then $f(u + v) \le f(u)$. -/
theorem ConvexFn.add_le_of_mem_recessionCone (hf : ConvexFn f) {β : ℝ}
    (hbdd : ∀ x ∈ C, f x ≤ (β : EReal)) {u v : E} (hu : u ∈ C) (hv : v ∈ recessionCone C) :
    f (u + v) ≤ f u :=
  hf.add_le_of_forall_add_smul_le fun t ht => hbdd _ (hv u hu t ht)

/-- The function $f$ is **bounded above on every half-line** of $C$ if for all $u, v \in E$ such
that $u + t v \in C$ for every $t \ge 0$, there is $\beta \in \mathbb{R}$ with
$f(u + t v) \le \beta$ for every $t \ge 0$.

The direction $v = 0$ makes the condition include $C \subseteq \operatorname{dom} f$. Thus this
one predicate contains both standing hypotheses of the extreme point principle. -/
def BddAboveOnRays (f : E → EReal) (C : Set E) : Prop :=
  ∀ u v : E, (∀ t : ℝ, 0 ≤ t → u + t • v ∈ C) →
    ∃ β : ℝ, ∀ t : ℝ, 0 ≤ t → f (u + t • v) ≤ (β : EReal)

/-- If $f \le \beta$ on $C$ for some $\beta \in \mathbb{R}$, then $f$ is bounded above on every
half-line of $C$. -/
theorem bddAboveOnRays_of_forall_le {β : ℝ} (hbdd : ∀ x ∈ C, f x ≤ (β : EReal)) :
    BddAboveOnRays f C := fun _ _ hray => ⟨β, fun t ht => hbdd _ (hray t ht)⟩

/-- If $f$ is bounded above on every half-line of $C$ and $C' \subseteq C$, then $f$ is bounded
above on every half-line of $C'$. -/
theorem BddAboveOnRays.mono {C' : Set E} (hray : BddAboveOnRays f C) (hsub : C' ⊆ C) :
    BddAboveOnRays f C' := fun u v hr => hray u v fun t ht => hsub (hr t ht)

/-- If $f$ is bounded above on every half-line of $C$, then $C \subseteq \operatorname{dom} f$. The
degenerate half-lines, which are the points of $C$, give this. -/
theorem BddAboveOnRays.subset_convexDom (hray : BddAboveOnRays f C) : C ⊆ convexDom f := by
  intro u hu
  obtain ⟨β, hβ⟩ := hray u 0 fun t _ => by simpa using hu
  have hle := hβ 0 le_rfl
  simp only [smul_zero, add_zero] at hle
  exact lt_of_le_of_lt hle (by simp)

/-- Let $f$ be convex and bounded above on every half-line of $C$. If $u \in C$ and $v \in 0^+ C$,
then $f(u + v) \le f(u)$. -/
theorem ConvexFn.add_le_of_bddAboveOnRays (hf : ConvexFn f) (hray : BddAboveOnRays f C) {u v : E}
    (hu : u ∈ C) (hv : v ∈ recessionCone C) : f (u + v) ≤ f u := by
  obtain ⟨β, hβ⟩ := hray u v fun t ht => hv u hu t ht
  exact hf.add_le_of_forall_add_smul_le hβ

/-- **A convex function bounded above on the half-lines of $C$ is constant along the lineality space
of $C$.** Let $f$ be convex and bounded above on every half-line of $C$. If $u \in C$ and $v$ is
in the lineality space of $C$, then $f(u + v) = f(u)$.

The two opposite directions of recession $v$ and $-v$ give two opposite inequalities. -/
theorem ConvexFn.add_eq_of_mem_linealitySpace (hf : ConvexFn f) (hray : BddAboveOnRays f C)
    {u v : E} (hu : u ∈ C) (hv : v ∈ linealitySpace C) : f (u + v) = f u := by
  obtain ⟨hv1, hv2⟩ := mem_linealitySpace.1 hv
  refine le_antisymm (hf.add_le_of_bddAboveOnRays hray hu hv1) ?_
  have huv : u + v ∈ C := add_mem_of_mem_recessionCone hv1 hu
  have hback := hf.add_le_of_bddAboveOnRays hray huv hv2
  rwa [show u + v + -v = u by abel] at hback

/-- **Reduction from $C$ to $C \cap N$.** Let $f$ be convex and bounded above on every half-line of
$C$, and let $N$ be a complement of the lineality space $L$ of $C$. Then for every $w \in C$
there is $q \in C \cap N$ with $f(w) = f(q)$.

The decomposition $C = L + (C \cap N)$ is algebraic, and needs neither closedness nor finite
dimension. The lineality space as a subspace is `ConvexAnalysis.linealitySubmodule C`. -/
theorem ConvexFn.exists_mem_inter_eq_of_isCompl (hf : ConvexFn f) (hray : BddAboveOnRays f C)
    {N : Submodule ℝ E} (hN : IsCompl (linealitySubmodule C) N) {w : E} (hw : w ∈ C) :
    ∃ q ∈ C ∩ (N : Set E), f w = f q := by
  have hdec : C = (linealitySubmodule C : Set E) + (C ∩ (N : Set E)) :=
    eq_add_inter_of_isCompl hN
  obtain ⟨p, hp, q, hq, rfl⟩ :=
    (hdec ▸ hw : w ∈ (linealitySubmodule C : Set E) + (C ∩ (N : Set E)))
  refine ⟨q, hq, ?_⟩
  change f (p + q) = f q
  rw [show p + q = q + p by abel]
  exact hf.add_eq_of_mem_linealitySpace hray hq.1 (by simpa using hp)

end Ray

section ExtremeUnbounded

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {C : Set E}

/-- Let $E$ be a finite-dimensional real normed space, let $C \subseteq E$ be closed and convex and
contain no lines, and let $f$ be convex and bounded above on every half-line of $C$. Then for
every $x \in C$ there is $u \in \operatorname{conv}(\operatorname{ext} C)$ with $f(x) \le f(u)$.

The representation of $C$ writes $x$ as $u + v$ with $u \in
\operatorname{conv}(\operatorname{ext} C)$ and $v \in 0^+ C$. -/
theorem ConvexFn.exists_mem_convexHull_extremePoints_le (hf : ConvexFn f) (hC : Convex ℝ C)
    (hCcl : IsClosed C) (hnl : ContainsNoLine C) (hray : BddAboveOnRays f C)
    {x : E} (hx : x ∈ C) : ∃ u ∈ convexHull ℝ (C.extremePoints ℝ), f x ≤ f u := by
  have hrep := convexHullPD_extremePoints_extremeDirections hC hCcl hnl
  have hx' : x ∈ convexHullPD (C.extremePoints ℝ) (extremeDirections C) := by rw [hrep]; exact hx
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_convexHullPD.1 hx'
  refine ⟨u, hu, hf.add_le_of_bddAboveOnRays hray ?_ ?_⟩
  · rw [← hrep]
    exact convexHull_subset_convexHullPD _ _ hu
  · rw [← hrep]
    exact coneHull_subset_recessionCone_convexHullPD _ _ hv

/-- **The extreme point principle, for a set without lines.** Let $E$ be a finite-dimensional real
normed space, let $C \subseteq E$ be closed and convex and contain no lines, and let $f$ be
convex and bounded above on every half-line of $C$. Then
$$\sup_{x \in C} f(x) = \sup_{x \in \operatorname{ext} C} f(x).$$

This is Theorem 32.3 of [rockafellar1970convex] for the lineality space $L = \{0\}$. Boundedness
on every half-line is strictly weaker than a uniform bound: $f(\xi_1, \xi_2) = \xi_1$ on
$C = \{(\xi_1, \xi_2) : \xi_1^2 \le \xi_2\}$ is bounded above on each half-line in $C$ but not
on $C$. -/
theorem ConvexFn.iSup_extremePoints_of_containsNoLine (hf : ConvexFn f) (hC : Convex ℝ C)
    (hCcl : IsClosed C) (hnl : ContainsNoLine C) (hray : BddAboveOnRays f C) :
    (⨆ x ∈ C, f x) = ⨆ x ∈ C.extremePoints ℝ, f x := by
  refine le_antisymm (iSup₂_le fun x hx => ?_)
    (iSup₂_le fun x hx => le_iSup₂ (f := fun z (_ : z ∈ C) => f z) x (extremePoints_subset hx))
  obtain ⟨u, hu, hle⟩ := hf.exists_mem_convexHull_extremePoints_le hC hCcl hnl hray hx
  refine hle.trans ?_
  rw [← hf.iSup_convexHull (C.extremePoints ℝ)]
  exact le_iSup₂ (f := fun z (_ : z ∈ convexHull ℝ (C.extremePoints ℝ)) => f z) u hu

/-- Let $E$ be a finite-dimensional real normed space, let $C \subseteq E$ be closed and convex and
contain no lines, and let $f$ be convex. If $x \in C$ maximizes $f$ over $C$ and
$f(x) < +\infty$, then $f(z) = f(x)$ for some extreme point $z$ of $C$.

No boundedness hypothesis is needed, but the condition $f(x) < +\infty$ is necessary. On
$C = [0, \infty)$, let $f = 0$ on $[0, 1)$ and $f = +\infty$ on $[1, \infty)$. Then $+\infty$ is
a maximum value, but the only extreme point has the value $0$. -/
theorem exists_mem_extremePoints_eq_of_isMaxOn_of_containsNoLine (hf : ConvexFn f)
    (hC : Convex ℝ C) (hCcl : IsClosed C) (hnl : ContainsNoLine C) {x : E} (hx : x ∈ C)
    (hxt : f x ≠ ⊤) (hmax : IsMaxOn f C x) : ∃ z ∈ C.extremePoints ℝ, f z = f x := by
  rw [isMaxOn_iff] at hmax
  rcases eq_or_ne (f x) ⊥ with hbot | hbot
  · obtain ⟨z, hz⟩ := extremePoints_nonempty_of_containsNoLine hC hCcl hnl ⟨x, hx⟩
    have hzle : f z ≤ ⊥ := hbot ▸ hmax z (extremePoints_subset hz)
    exact ⟨z, hz, by rw [le_bot_iff.1 hzle, hbot]⟩
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hbot (lt_top_iff_ne_top.2 hxt)
  have hbdd : ∀ z ∈ C, f z ≤ (r : EReal) := fun z hz => hr ▸ hmax z hz
  obtain ⟨u, hu, hle⟩ :=
    hf.exists_mem_convexHull_extremePoints_le hC hCcl hnl (bddAboveOnRays_of_forall_le hbdd) hx
  have hsub : convexHull ℝ (C.extremePoints ℝ) ⊆ C := convexHull_min extremePoints_subset hC
  have hux : f u = f x := le_antisymm (hmax u (hsub hu)) hle
  obtain ⟨z, hz, hzu⟩ :=
    exists_eq_of_isMaxOn_convexHull hf hu (isMaxOn_iff.2 fun z hz => hux ▸ hmax z (hsub hz))
  exact ⟨z, hz, by rw [hzu, hux]⟩

/-- **The extreme point principle, representation form.** Let $E$ be a finite-dimensional real
normed space, let $C \subseteq E$ be closed and convex and contain no lines, and let $f$ be
convex. Then
$$\sup_{x \in C} f(x) = \sup \bigl\{ f(x) : x \in \operatorname{ext} C + \operatorname{cone} D
  \bigr\},$$
where $D$ is the set of vectors that generate extreme directions of $C$ and
$\operatorname{cone} D$ is the set of nonnegative linear combinations of elements of $D$.

No boundedness hypothesis is needed. The cone is `PointedCone.hull ℝ
(ConvexAnalysis.extremeDirections C)`. -/
theorem ConvexFn.iSup_extremePoints_add_coneHull (hf : ConvexFn f) (hC : Convex ℝ C)
    (hCcl : IsClosed C) (hnl : ContainsNoLine C) :
    (⨆ x ∈ C, f x)
      = ⨆ x ∈ C.extremePoints ℝ + (PointedCone.hull ℝ (extremeDirections C) : Set E), f x := by
  have hcone : Convex ℝ ((PointedCone.hull ℝ (extremeDirections C) : Set E)) :=
    ((PointedCone.hull ℝ (extremeDirections C) : ConvexCone ℝ E)).convex
  have hhull : convexHull ℝ
      (C.extremePoints ℝ + (PointedCone.hull ℝ (extremeDirections C) : Set E)) = C := by
    rw [convexHull_add, hcone.convexHull_eq, ← convexHullPD_def]
    exact convexHullPD_extremePoints_extremeDirections hC hCcl hnl
  conv_lhs => rw [← hhull]
  exact hf.iSup_convexHull _

/-! ### The lineality space removed -/

/-- **The extreme point principle.** Let $E$ be a finite-dimensional real normed space, let
$C \subseteq E$ be closed and convex, let $f$ be convex and bounded above on every half-line of
$C$, and let $N$ be a complement of the lineality space of $C$. Then
$$\sup_{x \in C} f(x) = \sup_{x \in \operatorname{ext}(C \cap N)} f(x).$$

This is Theorem 32.3 of [rockafellar1970convex]. The source takes $N = L^\perp$, but every
complement of $L$ works. -/
theorem ConvexFn.iSup_extremePoints_inter_of_isCompl (hf : ConvexFn f) (hC : Convex ℝ C)
    (hCcl : IsClosed C) (hray : BddAboveOnRays f C) {N : Submodule ℝ E}
    (hN : IsCompl (linealitySubmodule C) N) :
    (⨆ x ∈ C, f x) = ⨆ x ∈ (C ∩ (N : Set E)).extremePoints ℝ, f x := by
  rw [← hf.iSup_extremePoints_of_containsNoLine (hC.inter (Submodule.convex N))
    (hCcl.inter (Submodule.closed_of_finiteDimensional N))
    (containsNoLine_inter_of_isCompl hC hCcl hN) (hray.mono Set.inter_subset_left)]
  refine le_antisymm (iSup₂_le fun x hx => ?_) (iSup₂_le fun x hx =>
    le_iSup₂ (f := fun z (_ : z ∈ C) => f z) x (Set.inter_subset_left hx))
  obtain ⟨q, hq, hfq⟩ := hf.exists_mem_inter_eq_of_isCompl hray hN hx
  rw [hfq]
  exact le_iSup₂ (f := fun z (_ : z ∈ C ∩ (N : Set E)) => f z) q hq

/-- Under the hypotheses of `ConvexAnalysis.ConvexFn.iSup_extremePoints_inter_of_isCompl`, if
$x \in C$ maximizes $f$ over $C$, then $f(z) = f(x)$ for some extreme point $z$ of $C \cap N$. -/
theorem exists_mem_extremePoints_inter_eq_of_isMaxOn_of_isCompl (hf : ConvexFn f)
    (hC : Convex ℝ C) (hCcl : IsClosed C) (hray : BddAboveOnRays f C) {N : Submodule ℝ E}
    (hN : IsCompl (linealitySubmodule C) N) {x : E} (hx : x ∈ C) (hmax : IsMaxOn f C x) :
    ∃ z ∈ (C ∩ (N : Set E)).extremePoints ℝ, f z = f x := by
  obtain ⟨q, hq, hfq⟩ := hf.exists_mem_inter_eq_of_isCompl hray hN hx
  obtain ⟨z, hz, hzq⟩ := exists_mem_extremePoints_eq_of_isMaxOn_of_containsNoLine hf
    (hC.inter (Submodule.convex N)) (hCcl.inter (Submodule.closed_of_finiteDimensional N))
    (containsNoLine_inter_of_isCompl hC hCcl hN) hq
    (by rw [← hfq]; exact (mem_convexDom.1 (hray.subset_convexDom hx)).ne)
    (isMaxOn_iff.2 fun w hw => by rw [← hfq]; exact isMaxOn_iff.1 hmax w hw.1)
  exact ⟨z, hz, by rw [hzq, ← hfq]⟩

end ExtremeUnbounded

/-! ### Finitely generated sets -/

section Polyhedral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {C : Set E}

/-- **The extreme point principle for a finitely generated set.** Let $E$ be a finite-dimensional
real normed space, let $C \subseteq E$ be a nonempty finitely generated convex set that contains
no lines, and let $f$ be convex and bounded above on every half-line of $C$. Then $f$ attains
its supremum over $C$ at an extreme point $z$ of $C$: $f(w) \le f(z)$ for all $w \in C$.

The set $C$ has only finitely many extreme points. A finitely generated set is
`ConvexAnalysis.FinitelyGenerated`, a set $\operatorname{conv} P + \operatorname{cone} D$ for
finite sets $P$ and $D$. -/
theorem exists_mem_extremePoints_isMaxOn_of_finitelyGenerated_of_bddAboveOnRays (hf : ConvexFn f)
    (hC : FinitelyGenerated C) (hnl : ContainsNoLine C) (hne : C.Nonempty)
    (hray : BddAboveOnRays f C) : ∃ z ∈ C.extremePoints ℝ, ∀ w ∈ C, f w ≤ f z := by
  have hcl : IsClosed C := hC.isClosed
  obtain ⟨P, D, hCeq⟩ := hC
  have hCPD : C = convexHullPD (P : Set E) (D : Set E) := hCeq
  have hconv : Convex ℝ C := by rw [hCPD]; exact convex_convexHullPD _ _
  have hfin : (C.extremePoints ℝ).Finite := by
    rw [hCPD]; exact finite_extremePoints_convexHullPD P D
  obtain ⟨z, hz, hzmax⟩ := Set.exists_max_image (C.extremePoints ℝ) f hfin
    (extremePoints_nonempty_of_containsNoLine hconv hcl hnl hne)
  refine ⟨z, hz, fun w hw => ?_⟩
  obtain ⟨u, hu, hle⟩ := hf.exists_mem_convexHull_extremePoints_le hconv hcl hnl hray hw
  exact hle.trans (convexHull_min (fun y hy => hzmax y hy) (hf.convex_le (f z)) hu)

/-- Let $E$ be a finite-dimensional real normed space, let $C \subseteq E$ be a nonempty finitely
generated convex set that contains no lines, and let $f$ be convex with $f \le \beta$ on $C$ for
some $\beta \in \mathbb{R}$. Then $f$ attains its supremum over $C$ at an extreme point $z$ of
$C$: $f(w) \le f(z)$ for all $w \in C$.

In finite dimension a finitely generated convex set is the same as a polyhedral convex set, and
$C$ has only finitely many extreme points. -/
theorem exists_mem_extremePoints_isMaxOn_of_finitelyGenerated (hf : ConvexFn f)
    (hC : FinitelyGenerated C) (hnl : ContainsNoLine C) (hne : C.Nonempty) {β : ℝ}
    (hbdd : ∀ x ∈ C, f x ≤ (β : EReal)) : ∃ z ∈ C.extremePoints ℝ, ∀ w ∈ C, f w ≤ f z :=
  exists_mem_extremePoints_isMaxOn_of_finitelyGenerated_of_bddAboveOnRays hf hC hnl hne
    (bddAboveOnRays_of_forall_le hbdd)

/-- Let $E$ be a finite-dimensional real normed space, let $C \subseteq E$ be a nonempty polyhedral
convex set, and let $f$ be convex and bounded above on every half-line of $C$. Then $f$ attains
its supremum over $C$: there is $z \in C$ with $f(w) \le f(z)$ for all $w \in C$.

Unlike `ConvexAnalysis.exists_mem_extremePoints_isMaxOn_of_finitelyGenerated`, this result makes
no assumption about lines in $C$, and it says nothing about extreme points: a set that contains
a line has no extreme points. The maximizer is an extreme point of $C \cap N$ and depends on the
complement $N$ of the lineality space. A polyhedral set is `ConvexAnalysis.Polyhedral`, the
solution set of finitely many linear inequalities. -/
theorem exists_isMaxOn_of_polyhedral_of_bddAboveOnRays (hf : ConvexFn f) (hC : Polyhedral C)
    (hne : C.Nonempty) (hray : BddAboveOnRays f C) : ∃ z ∈ C, ∀ w ∈ C, f w ≤ f z := by
  obtain ⟨N, hN⟩ := Submodule.exists_isCompl (linealitySubmodule C)
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨q₀, hq₀, -⟩ := hf.exists_mem_inter_eq_of_isCompl hray hN hx₀
  obtain ⟨z, hz, hzmax⟩ := exists_mem_extremePoints_isMaxOn_of_finitelyGenerated_of_bddAboveOnRays
    hf (hC.inter (polyhedral_coe_submodule N)).finitelyGenerated
    (containsNoLine_inter_of_isCompl hC.convex hC.isClosed hN) ⟨q₀, hq₀⟩
    (hray.mono Set.inter_subset_left)
  refine ⟨z, (extremePoints_subset hz : z ∈ C ∩ (N : Set E)).1, fun w hw => ?_⟩
  obtain ⟨q, hq, hwq⟩ := hf.exists_mem_inter_eq_of_isCompl hray hN hw
  rw [hwq]
  exact hzmax q hq

end Polyhedral

/-! ### The extreme point principle, compact case -/

section Extreme

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {C : Set E}

/-- **The extreme point principle, compact case.** Let $E$ be a finite-dimensional real normed
space, let $C \subseteq E$ be compact and convex, and let $f$ be convex. Then
$$\sup_{x \in C} f(x) = \sup_{x \in \operatorname{ext} C} f(x).$$

The proof combines Minkowski's theorem, $C = \operatorname{conv}(\operatorname{ext} C)$, with
`ConvexAnalysis.ConvexFn.iSup_convexHull`. -/
theorem ConvexFn.iSup_extremePoints (hf : ConvexFn f) (hcomp : IsCompact C) (hconv : Convex ℝ C) :
    (⨆ x ∈ C, f x) = ⨆ x ∈ C.extremePoints ℝ, f x := by
  conv_lhs => rw [← convexHull_extremePoints hcomp hconv]
  exact hf.iSup_convexHull _

/-- Let $C$ be a compact convex subset of a finite-dimensional real normed space, and let $f$ be
convex. If $x \in C$ maximizes $f$ over $C$, then $f(z) = f(x)$ for some extreme point $z$ of
$C$. -/
theorem exists_mem_extremePoints_eq_of_isMaxOn (hf : ConvexFn f) (hcomp : IsCompact C)
    (hconv : Convex ℝ C) {x : E} (hx : x ∈ C) (hmax : IsMaxOn f C x) :
    ∃ z ∈ C.extremePoints ℝ, f z = f x := by
  rw [← convexHull_extremePoints hcomp hconv] at hmax
  rw [← convexHull_extremePoints hcomp hconv] at hx
  exact exists_eq_of_isMaxOn_convexHull hf hx hmax

/-- **Attainment over a compact set.** Let $E$ be a finite-dimensional real normed space, let $f$ be
a proper convex function, and let $C$ be a nonempty compact convex set with $C \subseteq
\operatorname{ri}(\operatorname{dom} f)$. Then $f$ attains its supremum over $C$ at an extreme
point $z$ of $C$: $f(w) \le f(z)$ for all $w \in C$.

The hypothesis is $C \subseteq \operatorname{ri}(\operatorname{dom} f)$. Under the weaker
hypothesis $C \subseteq \operatorname{dom} f$ of [rockafellar1970convex], the attainment claim
is false. -/
theorem exists_mem_extremePoints_isMaxOn_of_isCompact (hf : ConvexFn f) (hp : ProperConvex f)
    (hcomp : IsCompact C) (hconv : Convex ℝ C) (hne : C.Nonempty) (hCri : C ⊆ ri (convexDom f)) :
    ∃ z ∈ C.extremePoints ℝ, ∀ w ∈ C, f w ≤ f z := by
  obtain ⟨x, hx, hxmax⟩ :=
      hcomp.exists_isMaxOn hne ((hf.continuousOn_relint_convexDom hp).mono hCri)
  obtain ⟨z, hz, hzx⟩ :=
    exists_mem_extremePoints_eq_of_isMaxOn hf hcomp hconv hx hxmax
  exact ⟨z, hz, fun w hw => hzx ▸ isMaxOn_iff.1 hxmax w hw⟩

end Extreme

/-! ### Subgradients at a maximizer -/

section Optimality

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {C : Set E} {x : E} {y : F}

/-- Let $f : E \to [-\infty, +\infty]$, and let $x$ be a point with $f(x)$ finite and
$f(z) \le f(x)$ for all $z \in C$. Then every subgradient $y \in \partial f(x)$ is a normal
vector of $C$ at $x$: $\langle z - x, y \rangle \le 0$ for all $z \in C$.

The point $x$ need not lie in $C$. The normal cone is `ConvexAnalysis.normalCone B C x`. -/
theorem mem_normalCone_of_mem_subdifferential_of_isMaxOn (hxb : f x ≠ ⊥) (hxt : f x ≠ ⊤)
    (hmax : IsMaxOn f C x) (hy : y ∈ subdifferential B f x) : y ∈ normalCone B C x := by
  rw [isMaxOn_iff] at hmax
  intro z hz
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hxb (lt_top_iff_ne_top.2 hxt)
  have h2 : f x + ((B (z - x) y : ℝ) : EReal) ≤ f x := le_trans (hy z) (hmax z hz)
  rw [hr, ← EReal.coe_add, EReal.coe_le_coe_iff] at h2
  linarith

/-- Let $x$ satisfy $f(z) \le f(x)$ for all $z \in C$, and let $z_0 \in C$ with $f(z_0) \neq f(x)$.
Then no subgradient of $f$ at $x$ is zero: $0 \notin \partial f(x)$. -/
theorem ne_zero_of_mem_subdifferential_of_isMaxOn (hmax : IsMaxOn f C x) {z₀ : E}
    (hz₀ : z₀ ∈ C) (hne : f z₀ ≠ f x) (hy : y ∈ subdifferential B f x) : y ≠ 0 := by
  rw [isMaxOn_iff] at hmax
  rintro rfl
  have hle : f x ≤ f z₀ := by simpa using hy z₀
  exact hne (le_antisymm (hmax z₀ hz₀) hle)

/-- If $y$ is a normal vector of $C$ at $x$, then $\langle z, y \rangle \le \langle x, y \rangle$
for all $z \in C$: the linear functional $\langle \cdot, y \rangle$ attains its supremum over
$C$ at $x$. -/
theorem le_of_mem_normalCone (hy : y ∈ normalCone B C x) {z : E} (hz : z ∈ C) : B z y ≤ B x y := by
  have h := hy z hz
  rw [map_sub, LinearMap.sub_apply] at h
  linarith

end Optimality

end ConvexAnalysis
