/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Duality.Exact
import Numlib.Analysis.Convex.Duality.Ops
import Numlib.Analysis.Convex.Recession.Closedness
import Numlib.Analysis.Convex.Recession.Conjugate
import Numlib.Analysis.Convex.RelativeInterior

/-!
# The relative-interior constraint qualification

The module `Numlib.Analysis.Convex.Duality.Exact` names two conclusions,
`ConvexAnalysis.IsExactImage` and `ConvexAnalysis.IsExactSum`: a conjugate formula for an inverse
image $gA$ or for a sum $f + g$ holds with the infimum attained. This module proves the first
sufficient condition for each, the classical relative-interior hypothesis
$$A^{-1}(\operatorname{ri}(\operatorname{dom} g)) \neq \emptyset \qquad\text{and}\qquad
  \operatorname{ri}(\operatorname{dom} f) \cap \operatorname{ri}(\operatorname{dom} g) \neq
  \emptyset.$$
The presentation follows §9 and §16 of [rockafellar1970convex].

Both proofs use the same two facts. The first is that the dual object, a linear image or a sum of
closed convex sets, is closed. The second is that a linear function that is at most $0$ on a convex
set and attains this bound at a relative interior point is constant on the set.

## Main definitions

* `ConvexAnalysis.TendstoConvexClAlongSegment`: the closure $\operatorname{cl} f$ is the limit of
  $f$ along the segments that issue from a point $x_0$.

## Main results

* `ConvexAnalysis.IsExactImage.of_relint`: a proper convex function $g$ pulls back exactly along a
  linear map whose range meets $\operatorname{ri}(\operatorname{dom} g)$ (Theorem 16.3 of
  [rockafellar1970convex]). `ConvexAnalysis.IsExactImage.of_relint_closed` is the closed case, which
  carries the argument.
* `ConvexAnalysis.IsExactSum.of_relint`: two proper convex functions whose effective domains have a
  common relative interior point add exactly (Theorem 16.4 of [rockafellar1970convex]).
  `ConvexAnalysis.IsExactSum.of_relint_closed` is the closed case, and
  `ConvexAnalysis.IsExactFinsetSum.of_relint` is the form for $m$ summands.
* `ConvexAnalysis.ConvexFn.tendstoConvexClAlongSegment`,
  `ConvexAnalysis.ClosedProperConvexFn.tendstoConvexClAlongSegment`: the two ways to obtain the
  segment limit, $x_0 \in \operatorname{ri}(\operatorname{dom} f)$ for a proper convex $f$, and
  $x_0 \in \operatorname{dom} f$ for a closed proper convex $f$.
* `ConvexAnalysis.convexConj_add_eq_convexConj_convexCl_add_convexCl`,
  `ConvexAnalysis.convexConj_compLin_eq_convexConj_compLin_convexCl`: passing to closures does not
  change the conjugate of a sum or of a composition with a linear map. This removes the closedness
  hypothesis from the two closed cases.
* `ConvexAnalysis.properConvex_convexConj_of_properConvex`: in finite dimensions the conjugate of a
  proper convex function is proper, with no closedness hypothesis.

## Implementation notes

* Closures are compared in the conjugate form $(f + g)^* = (\operatorname{cl} f + \operatorname{cl}
  g)^*$ rather than as $\operatorname{cl}(f + g) = \operatorname{cl} f + \operatorname{cl} g$, which
  is `ConvexAnalysis.convexCl_add`. The conjugate form is weaker but cheaper. The identity of
  closures needs the segment limit for $f + g$ as well, hence a relative interior point of both
  domains. The conjugate form needs only a point of $\operatorname{dom} f$ and one of
  $\operatorname{ri}(\operatorname{dom} g)$.
* The two rules put topologies on opposite spaces. For $g : G \to [-\infty, +\infty]$, a linear map
  $A : E \to G$ and its adjoint $A' : H \to F$, the image rule uses the closedness theorem for
  images on $H$, so $H$ must be finite-dimensional, and the condition on
  $\operatorname{ri}(\operatorname{dom} g)$ makes $G$ finite-dimensional too. The space $F$ only
  receives an image, and $E$ carries no topology. The sum rule is the reverse:
  $\operatorname{ri}(\operatorname{dom} f)$ needs only a normed space $E$, while the closedness
  theorem for sums runs in $F \times \mathbb{R}$, so $F$ must be finite-dimensional.
-/

open Pointwise

namespace ConvexAnalysis

section Image

variable {E F G H : Type*}
  [AddCommGroup E] [Module ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ}
  {A : E →ₗ[ℝ] G} {A' : H →ₗ[ℝ] F} {g : G → EReal}

omit [FiniteDimensional ℝ G] [FiniteDimensional ℝ H] in
/-- Let $B'$ pair $G$ with $H$ compatibly with the topology of the normed space $G$, and let
$A : E \to G$ and $A' : H \to F$ be adjoint: $\langle Ax, z \rangle' = \langle x, A'z \rangle$.
Let $g$ be a closed proper convex function on $G$, and let $Ax_0 \in
\operatorname{ri}(\operatorname{dom} g)$ for some $x_0 \in E$. If $z \in H$ satisfies
$(g^* 0^+)(z) \le 0$ and $A'z = 0$, then $z$ lies in the constancy space of $g^*$.

This discharges the closedness hypothesis for the image of $g^*$ under $A'$. The condition on
$z$ says that $\langle \cdot, z \rangle'$ is at most $0$ on $\operatorname{dom} g$ and vanishes
at $Ax_0 \in \operatorname{ri}(\operatorname{dom} g)$, which makes it constant on
$\operatorname{dom} g$. -/
theorem mem_constancySpace_convexConj_of_relint [IsCompatiblePairing B']
    (hA : IsAdjointPair B B' A A') (hg : ClosedProperConvexFn g)
    {x₀ : E} (hx₀ : A x₀ ∈ ri (convexDom g)) {z : H}
    (hrec : recessionFn (convexConj B' g) z ≤ 0) (hz0 : A' z = 0) :
    z ∈ constancySpace (convexConj B' g) := by
  have hconjp : ProperConvex (convexConj B' g) := properConvex_convexConj hg
  rw [constancySpace_convexConj hg.proper hconjp]
  have hnonpos : ∀ x ∈ convexDom g, (B'.flip z) x ≤ 0 := by
    intro x hx
    rw [recessionFn_convexConj hg.proper hconjp, supportFn_le_zero_iff] at hrec
    exact hrec x hx
  have hvanish : (B'.flip z) (A x₀) = 0 := by
    rw [LinearMap.flip_apply, hA x₀ z, hz0, map_zero]
  exact eq_zero_of_nonpos_of_mem_relint hx₀ hnonpos hvanish

omit [FiniteDimensional ℝ G] in
/-- **A closed proper convex function pulls back exactly along a linear map whose range meets the
relative interior of its effective domain.** Let $B$ pair a real vector space $E$ with a normed
space $F$, and let $B'$ pair a normed space $G$ with a finite-dimensional normed space $H$. Let
$B'$, its flip and the flip of $B$ be compatible with the topologies of $G$, $H$ and $F$. Let
$A : E \to G$ and $A' : H \to F$ be adjoint: $\langle Ax, z \rangle' = \langle x, A'z \rangle$.
Let $g$ be a closed proper convex function on $G$ with $Ax_0 \in
\operatorname{ri}(\operatorname{dom} g)$ for some $x_0 \in E$. Then $g$ pulls back exactly along
$A$: $(gA)^* = A'(g^*)$, and for every $y \in F$ with $(gA)^*(y) < +\infty$ the infimum of $g^*$
over the fibre $\{z \in H \mid A'z = y\}$, which defines $A'(g^*)(y)$, is attained.

The proof shows that the image of $g^*$ under $A'$ is closed, with
`ConvexAnalysis.mem_constancySpace_convexConj_of_relint` as the hypothesis of the closedness
theorem. -/
theorem IsExactImage.of_relint_closed [IsCompatiblePairing B'] [IsCompatiblePairing B'.flip]
    [IsCompatiblePairing B.flip] (hA : IsAdjointPair B B' A A') (hg : ClosedProperConvexFn g)
    {x₀ : E} (hx₀ : A x₀ ∈ ri (convexDom g)) :
    IsExactImage B B' A A' hA g := by
  have hconjp : ProperConvex (convexConj B' g) := properConvex_convexConj hg
  have hconjcpc : ClosedProperConvexFn (convexConj B' g) :=
    ⟨convexFn_convexConj B' g, closedConvex_convexConj, hconjp⟩
  have hkey : ∀ z : H,
      recessionFn (convexConj B' g) z ≤ 0 → A' z = 0 → z ∈ constancySpace (convexConj B' g) :=
    fun z hrec hz0 => mem_constancySpace_convexConj_of_relint hA hg hx₀ hrec hz0
  obtain ⟨-, hcpc, -⟩ := closedProperConvexFn_mapLin hconjcpc A' hkey
  -- the image of the epigraph is already closed, so the closure in the identity is redundant
  have heq : convexConj B (compLin g A) = mapLin A' (convexConj B' g) := by
    rw [convexConj_compLin_eq_convexCl_mapLin hA hg.convex hg.closed]
    exact hcpc.closed
  refine ⟨hg.proper, fun y hy => ?_⟩
  rw [heq] at hy ⊢
  obtain ⟨μ, hμ⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hcpc.proper.ne_bot y) hy
  obtain ⟨z, hzy, hz⟩ :=
    exists_mapLin_eq hconjcpc A' hkey hμ.le
  exact ⟨z, hzy, hμ ▸ hz⟩

end Image

/-! ### Sums -/

section Sum

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f g : E → EReal}

omit [FiniteDimensional ℝ F] in
/-- Let $E$ be a normed space and let the pairing be compatible with its topology. Let $f$ be a
closed proper convex function on $E$, and let $(z, \nu) \in F \times \mathbb{R}$ be a direction
of recession of $\operatorname{epi} f^*$. Then $\langle x, z \rangle \le \nu$ for every
$x \in \operatorname{dom} f$.

This is the statement that the recession function of $f^*$ is the support function of
$\operatorname{dom} f$, read one point at a time. -/
theorem le_of_mk_mem_recessionCone_epi_convexConj [IsCompatiblePairing B]
    (hf : ClosedProperConvexFn f)
    {z : F} {ν : ℝ} (hp : ((z, ν) : F × ℝ) ∈ recessionCone (epi (convexConj B f)))
    {x : E} (hx : x ∈ convexDom f) : B x z ≤ ν := by
  have hle := recessionFn_le_coe_iff.2 hp
  rw [recessionFn_convexConj hf.proper (properConvex_convexConj hf), supportFn_le_coe_iff] at hle
  exact hle x hx

omit [FiniteDimensional ℝ F] in
/-- **The relative-interior step for sums.** Let $E$ be a normed space and let the pairing be
compatible with its topology. Let $f$ be a closed proper convex function on $E$, let $x_0 \in
\operatorname{ri}(\operatorname{dom} f)$, and let $(z, \nu) \in F \times \mathbb{R}$ be a
direction of recession of $\operatorname{epi} f^*$ with $\nu \le \langle x_0, z \rangle$. Then
$(z, \nu)$ lies in the lineality space of $\operatorname{epi} f^*$.

The recession direction says that $\langle \cdot, z \rangle \le \nu$ on $\operatorname{dom} f$,
and a bound that is attained at a relative interior point is attained on the whole domain. -/
theorem mk_mem_linealitySpace_epi_convexConj_of_relint [IsCompatiblePairing B]
    (hf : ClosedProperConvexFn f) {x₀ : E} (hx₀ : x₀ ∈ ri (convexDom f)) {z : F} {ν : ℝ}
    (hp : ((z, ν) : F × ℝ) ∈ recessionCone (epi (convexConj B f))) (hν : ν ≤ B x₀ z) :
    ((z, ν) : F × ℝ) ∈ linealitySpace (epi (convexConj B f)) := by
  have hx₀f : x₀ ∈ convexDom f := intrinsicInterior_subset hx₀
  have hmax : B x₀ z = ν :=
    le_antisymm (le_of_mk_mem_recessionCone_epi_convexConj hf hp hx₀f) hν
  have hconst : ∀ x ∈ convexDom f, (B.flip z) x = (B.flip z) x₀ :=
    eq_of_isMaxOn_of_mem_relint hx₀ fun x hx =>
      le_trans (le_of_mk_mem_recessionCone_epi_convexConj hf hp hx) hν
  refine mem_linealitySpace.2 ⟨hp, ?_⟩
  rw [Prod.neg_mk, ← recessionFn_le_coe_iff,
      recessionFn_convexConj hf.proper (properConvex_convexConj hf),
    supportFn_le_coe_iff]
  intro x hx
  have hx' : B x z = ν := by
    have hc := hconst x hx
    rw [LinearMap.flip_apply, LinearMap.flip_apply, hmax] at hc
    exact hc
  rw [map_neg, hx']

omit [FiniteDimensional ℝ F] in
/-- **A closed sum of conjugate epigraphs makes the sum exact.** Let $E$ and $F$ be normed spaces,
and let the pairing and its flip be compatible with their topologies. Let $f$ and $g$ be closed
proper convex functions on $E$ whose effective domains have a common point. If
$\operatorname{epi} f^* + \operatorname{epi} g^*$ is closed, then $f$ and $g$ add exactly.

When $\operatorname{epi} f^* + \operatorname{epi} g^*$ is closed, it is the epigraph of
$f^* \mathbin{\square} g^*$, which is then closed and equal to $(f + g)^*$; the splitting of
each point of the sum is the attainment that `ConvexAnalysis.IsExactSum` asks for. The two
constraint qualifications, a common relative interior point
(`ConvexAnalysis.IsExactSum.of_relint_closed`) and polyhedrality
(`ConvexAnalysis.IsExactSum.of_polyhedral_pair`), are two ways of making this sum closed. -/
theorem IsExactSum.of_isClosed_epi_add [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hf : ClosedProperConvexFn f) (hg : ClosedProperConvexFn g)
    {x₀ : E} (hxf : x₀ ∈ convexDom f) (hxg : x₀ ∈ convexDom g)
    (hclosed : IsClosed (epi (convexConj B f) + epi (convexConj B g))) :
    IsExactSum B f g := by
  have hup : ProperConvex (convexConj B f) := properConvex_convexConj hf
  have hvp : ProperConvex (convexConj B g) := properConvex_convexConj hg
  -- a closed sum of epigraphs is an epigraph, namely that of the infimal convolution
  have hmono : ∀ (y : F) (μ ν : ℝ), (y, μ) ∈ epi (convexConj B f) + epi (convexConj B g) → μ ≤ ν →
      (y, ν) ∈ epi (convexConj B f) + epi (convexConj B g) := by
    rintro y μ ν ⟨⟨y₁, a⟩, h₁, ⟨y₂, b⟩, h₂, heq⟩ hμν
    have hy : y₁ + y₂ = y := congrArg Prod.fst heq
    have hab : a + b = μ := congrArg Prod.snd heq
    refine ⟨(y₁, a), h₁, (y₂, b + (ν - μ)), mk_mem_epi.2 ?_, ?_⟩
    · exact (mk_mem_epi.1 h₂).trans (by exact_mod_cast (by linarith : b ≤ b + (ν - μ)))
    · change ((y₁, a) : F × ℝ) + (y₂, b + (ν - μ)) = (y, ν)
      rw [Prod.mk_add_mk, hy, show a + (b + (ν - μ)) = ν by linarith]
  have hepiEq : epi (infConv (convexConj B f) (convexConj B g)) = epi (convexConj B f)
      + epi (convexConj B g) :=
    epi_infConv (IsEpiLike.of_isClosed hmono hclosed)
  -- properness of the infimal convolution, from properness of `(f + g)*`
  have hdomne : (convexDom (f + g)).Nonempty :=
    ⟨x₀, by
      rw [mem_convexDom, Pi.add_apply]
      exact EReal.add_lt_top (mem_convexDom.1 hxf).ne (mem_convexDom.1 hxg).ne⟩
  have hproper : ProperConvex (infConv (convexConj B f) (convexConj B g)) := by
    refine ⟨?_, fun y hy => ?_⟩
    · obtain ⟨p, hp⟩ := hup.convexDom_nonempty
      obtain ⟨q, hq⟩ := hvp.convexDom_nonempty
      exact ⟨p + q, by rw [convexDom_infConv]; exact Set.add_mem_add hp hq⟩
    · have hle := convexConj_add_le_infConv B f g y
      rw [hy, le_bot_iff] at hle
      exact convexConj_ne_bot hdomne y hle
  have hclosedFn : ClosedConvex (infConv (convexConj B f) (convexConj B g)) :=
    (ClosedProperConvexFn.of_isClosed_epi
      (convexFn_infConv (convexFn_convexConj B f) (convexFn_convexConj B g))
      (by rw [hepiEq]; exact hclosed) hproper).closed
  have hconjadd : convexConj B (f + g) = infConv (convexConj B f) (convexConj B g) := by
    rw [convexConj_add_eq_convexCl_infConv hf.convex hf.closed hg.convex hg.closed]
    exact hclosedFn
  refine ⟨hf.proper, hg.proper, fun y => ?_⟩
  rw [hconjadd]
  rcases eq_top_or_lt_top (infConv (convexConj B f) (convexConj B g) y) with htop | htop
  · exact ⟨y, 0, add_zero y, by rw [htop]; exact le_top⟩
  obtain ⟨μ, hμ⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hproper.ne_bot y) htop
  have hmem : ((y, μ) : F × ℝ) ∈ epi (convexConj B f) + epi (convexConj B g) := by
    rw [← hepiEq]; exact mk_mem_epi.2 hμ.le
  obtain ⟨⟨y₁, a⟩, h₁, ⟨y₂, b⟩, h₂, heq⟩ := hmem
  refine ⟨y₁, y₂, congrArg Prod.fst heq, ?_⟩
  have hab : a + b = μ := congrArg Prod.snd heq
  rw [hμ]
  calc convexConj B f y₁ + convexConj B g y₂ ≤ ((a : ℝ) : EReal) + ((b : ℝ) : EReal) :=
        add_le_add (mk_mem_epi.1 h₁) (mk_mem_epi.1 h₂)
    _ = ((μ : ℝ) : EReal) := by rw [← EReal.coe_add, hab]

/-- **Two closed proper convex functions add exactly when their effective domains have a common
relative interior point.** Let $E$ be a normed space and $F$ a finite-dimensional normed space,
and let the pairing and its flip be compatible with their topologies. Let $f$ and $g$ be closed
proper convex functions on $E$, and let $x_0 \in \operatorname{ri}(\operatorname{dom} f) \cap
\operatorname{ri}(\operatorname{dom} g)$. Then $f$ and $g$ add exactly:
$(f + g)^* = f^* \mathbin{\square} g^*$, and the infimum in the infimal convolution is attained
at every point.

The proof shows that $\operatorname{epi} f^* + \operatorname{epi} g^*$ is closed, by the
closedness theorem for a sum of convex sets, and applies
`ConvexAnalysis.IsExactSum.of_isClosed_epi_add`. -/
theorem IsExactSum.of_relint_closed [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hf : ClosedProperConvexFn f) (hg : ClosedProperConvexFn g)
    {x₀ : E} (hxf : x₀ ∈ ri (convexDom f)) (hxg : x₀ ∈ ri (convexDom g)) :
    IsExactSum B f g := by
  have hx₀f : x₀ ∈ convexDom f := intrinsicInterior_subset hxf
  have hx₀g : x₀ ∈ convexDom g := intrinsicInterior_subset hxg
  have hup : ProperConvex (convexConj B f) := properConvex_convexConj hf
  have hvp : ProperConvex (convexConj B g) := properConvex_convexConj hg
  have hucpc : ClosedProperConvexFn (convexConj B f) :=
      ⟨convexFn_convexConj B f, closedConvex_convexConj, hup⟩
  have hvcpc : ClosedProperConvexFn (convexConj B g) :=
      ⟨convexFn_convexConj B g, closedConvex_convexConj, hvp⟩
  have hune : (epi (convexConj B f)).Nonempty := (epi_nonempty_iff _).2 hup.convexDom_nonempty
  have hvne : (epi (convexConj B g)).Nonempty := (epi_nonempty_iff _).2 hvp.convexDom_nonempty
  -- the closedness hypothesis, discharged from the relative-interior condition
  have hrec : ∀ p ∈ recessionCone (epi (convexConj B f)),
      ∀ q ∈ recessionCone (epi (convexConj B g)),
      p + q = 0 →
        p ∈ linealitySpace (epi (convexConj B f)) ∧ q ∈ linealitySpace (epi (convexConj B g)) := by
    rintro ⟨z, ν⟩ hp ⟨w, ρ⟩ hq hzero
    have hz : z + w = 0 := congrArg Prod.fst hzero
    have hνρ : ν + ρ = 0 := congrArg Prod.snd hzero
    have h₁ : B x₀ z ≤ ν := le_of_mk_mem_recessionCone_epi_convexConj hf hp hx₀f
    have h₂ : B x₀ w ≤ ρ := le_of_mk_mem_recessionCone_epi_convexConj hg hq hx₀g
    have hBzw : B x₀ z + B x₀ w = 0 := by rw [← map_add, hz, map_zero]
    exact ⟨mk_mem_linealitySpace_epi_convexConj_of_relint hf hxf hp (by linarith),
      mk_mem_linealitySpace_epi_convexConj_of_relint hg hxg hq (by linarith)⟩
  have hclosed : IsClosed (epi (convexConj B f) + epi (convexConj B g)) :=
    Convex.isClosed_add (convexFn_convexConj B f).convex_epi hucpc.isClosed_epi hune
      (convexFn_convexConj B g).convex_epi hvcpc.isClosed_epi hvne hrec
  exact IsExactSum.of_isClosed_epi_add hf hg hx₀f hx₀g hclosed

end Sum

/-! ### Conjugates of functions recovered along segments -/

section SegmentConj

open Filter Topology

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ}

/-- **A minorant recovered along segments has the same conjugate.** Let
$\varphi, \psi : E \to [-\infty, +\infty]$ with $\psi \le \varphi$, and let $x_0 \in E$. Suppose
that for every $x \in E$,
$$\varphi((1 - a)x_0 + ax) \to \psi(x) \qquad\text{as } a \to 1^-.$$
Then $\varphi^* = \psi^*$.

Every affine minorant of $\varphi$ passes to the limit along these segments. This is the main
step of `ConvexAnalysis.convexConj_add_eq_convexConj_convexCl_add_convexCl` and
`ConvexAnalysis.convexConj_compLin_eq_convexConj_compLin_convexCl`. -/
theorem convexConj_eq_of_le_of_tendsto {φ ψ : E → EReal} (hle : ψ ≤ φ) {x₀ : E}
    (hlim : ∀ x, Tendsto (fun a : ℝ => φ ((1 - a) • x₀ + a • x)) (𝓝[<] (1 : ℝ)) (𝓝 (ψ x))) :
    convexConj B φ = convexConj B ψ := by
  refine funext fun y => le_antisymm (convexConj_antitone B hle y) ?_
  have key : ∀ c : ℝ, convexConj B φ y ≤ (c : EReal) → convexConj B ψ y ≤ (c : EReal) := by
    intro c hc
    rw [convexConj_le_coe_iff] at hc ⊢
    intro x
    have hlin : ∀ a : ℝ, B ((1 - a) • x₀ + a • x) y = (1 - a) * B x₀ y + a * B x y := by
      intro a
      rw [map_add, map_smul, map_smul]
      simp
    have hL : Tendsto (fun a : ℝ => affineFn B y c ((1 - a) • x₀ + a • x))
        (𝓝[<] (1 : ℝ)) (𝓝 (affineFn B y c x)) := by
      simp only [affineFn_eq_coe, hlin]
      exact EReal.tendsto_coe.2
        ((tendsto_affine_nhdsLT_one (B x₀ y) (B x y)).sub tendsto_const_nhds)
    exact le_of_tendsto_of_tendsto' hL (hlim x) fun a => hc _
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨c, h1, h2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
  exact absurd (key c h1.le) (not_le.2 h2)

end SegmentConj

/-! ### Dropping closedness from the constraint qualifications -/

section Closure

open Filter Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f g : E → EReal}

/-- A function $f$ on a normed space $E$ is **recovered along segments from $x_0$** if for every
$y \in E$,
$$f((1 - a)x_0 + ay) \to (\operatorname{cl} f)(y) \qquad\text{as } a \to 1^-.$$

This holds for a proper convex $f$ when $x_0 \in \operatorname{ri}(\operatorname{dom} f)$
(`ConvexAnalysis.ConvexFn.tendstoConvexClAlongSegment`), and for a closed proper convex $f$ when
$x_0 \in \operatorname{dom} f$
(`ConvexAnalysis.ClosedProperConvexFn.tendstoConvexClAlongSegment`). It is the only property of
$x_0$ that the argument for removing closedness uses, so both constraint qualifications run
through the same lemma. -/
def TendstoConvexClAlongSegment (f : E → EReal) (x₀ : E) : Prop :=
  ∀ y, Tendsto (fun a : ℝ => f ((1 - a) • x₀ + a • y)) (𝓝[<] (1 : ℝ)) (𝓝 (convexCl f y))

omit [FiniteDimensional ℝ F] in
/-- **In finite dimensions the conjugate of a proper convex function is proper.** Let $E$ be a
finite-dimensional normed space, and let the pairing be compatible with its topology. If $f$ is
a proper convex function on $E$, then $f^*$ is proper.

No closedness hypothesis is needed. The proof uses $f^* = (\operatorname{cl} f)^*$ and the fact
that $\operatorname{cl} f$ is a closed proper convex function, which is where finite dimension
enters. -/
theorem properConvex_convexConj_of_properConvex [IsCompatiblePairing B] (hf : ConvexFn f)
    (hp : ProperConvex f) :
    ProperConvex (convexConj B f) := by
  rw [← convexConj_convexCl]
  exact properConvex_convexConj
      ⟨convexFn_convexCl hf, closedConvex_convexCl f, hf.properConvex_convexCl hp⟩

/-- **A proper convex function is recovered along segments from any relative interior point of its
effective domain.** Let $E$ be a finite-dimensional normed space, let $f$ be a proper convex
function on $E$, and let $x_0 \in \operatorname{ri}(\operatorname{dom} f)$. Then $f((1 - a)x_0 +
ay) \to (\operatorname{cl} f)(y)$ as $a \to 1^-$, for every $y$. -/
theorem ConvexFn.tendstoConvexClAlongSegment (hf : ConvexFn f) (hp : ProperConvex f) {x₀ : E}
    (hx₀ : x₀ ∈ ri (convexDom f)) : TendstoConvexClAlongSegment f x₀ := by
  intro y
  rw [hf.convexCl_eq_lscHull hp]
  exact hf.tendsto_lscHull_along_segment_relint hx₀ y

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- **A closed proper convex function is recovered along segments from any point of its effective
domain.** Let $E$ be a normed space, let $f$ be a closed proper convex function on $E$, and let
$x_0 \in \operatorname{dom} f$. Then $f((1 - a)x_0 + ay) \to (\operatorname{cl} f)(y) = f(y)$ as
$a \to 1^-$, for every $y$. No relative interior point is needed. -/
theorem ClosedProperConvexFn.tendstoConvexClAlongSegment (hf : ClosedProperConvexFn f) {x₀ : E}
    (hx₀ : x₀ ∈ convexDom f) : TendstoConvexClAlongSegment f x₀ := by
  intro y
  rw [show convexCl f = f from hf.closed]
  exact tendsto_along_segment_of_closed_proper hf hx₀ y

omit [FiniteDimensional ℝ F] in
/-- **Passing to closures does not change the conjugate of a sum.** Let $E$ be a finite-dimensional
normed space, and let $f$ and $g$ be proper convex functions on $E$ that are both recovered
along segments from one point $x_0$. Then
$$(f + g)^* = (\operatorname{cl} f + \operatorname{cl} g)^*.$$

The stronger identity $\operatorname{cl}(f + g) = \operatorname{cl} f + \operatorname{cl} g$
needs the segment limit for $f + g$ as well, hence a point of
$\operatorname{ri}(\operatorname{dom} f) \cap \operatorname{ri}(\operatorname{dom} g)$. The
conjugate form does not need it, since $f^* = (\operatorname{cl} f)^*$ holds without hypotheses.
Therefore a caller can use a point of $\operatorname{dom} f$ and a point of
$\operatorname{ri}(\operatorname{dom} g)$. -/
theorem convexConj_add_eq_convexConj_convexCl_add_convexCl (hf : ConvexFn f) (hpf : ProperConvex f)
    (hg : ConvexFn g)
    (hpg : ProperConvex g) {x₀ : E} (hsf : TendstoConvexClAlongSegment f x₀)
    (hsg : TendstoConvexClAlongSegment g x₀) :
    convexConj B (f + g) = convexConj B (convexCl f + convexCl g) := by
  have hclf : ProperConvex (convexCl f) := hf.properConvex_convexCl hpf
  have hclg : ProperConvex (convexCl g) := hg.properConvex_convexCl hpg
  refine convexConj_eq_of_le_of_tendsto (x₀ := x₀)
    (fun x => add_le_add (convexCl_le f x) (convexCl_le g x)) fun x => ?_
  have hcont : ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (convexCl f x, convexCl g x) :=
    EReal.continuousAt_add (Or.inr (hclg.ne_bot x)) (Or.inl (hclf.ne_bot x))
  exact hcont.tendsto.comp ((hsf x).prodMk_nhds (hsg x))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- **Exactness passes from the closures to the functions.** Let $E$ carry a topology for which
every functional $\langle \cdot, y \rangle$ is continuous. Let $f$ and $g$ be proper functions
on $E$ such that $\operatorname{cl} f$ and $\operatorname{cl} g$ add exactly and $(f + g)^* =
(\operatorname{cl} f + \operatorname{cl} g)^*$. Then $f$ and $g$ add exactly.

The second hypothesis is supplied by
`ConvexAnalysis.convexConj_add_eq_convexConj_convexCl_add_convexCl`. -/
theorem IsExactSum.of_convexCl [IsContinuousPairing B] (hpf : ProperConvex f) (hpg : ProperConvex g)
    (h : IsExactSum B (convexCl f) (convexCl g))
    (hconj : convexConj B (f + g) = convexConj B (convexCl f + convexCl g)) : IsExactSum B f g := by
  refine ⟨hpf, hpg, fun y => ?_⟩
  obtain ⟨y₁, y₂, hy, hle⟩ := h.exact_le y
  rw [convexConj_convexCl, convexConj_convexCl] at hle
  exact ⟨y₁, y₂, hy, by rw [hconj]; exact hle⟩

/-- **Two proper convex functions add exactly when their effective domains have a common relative
interior point.** Let $E$ and $F$ be finite-dimensional normed spaces, and let the pairing and
its flip be compatible with their topologies. Let $f$ and $g$ be proper convex functions on $E$,
and let $x_0 \in \operatorname{ri}(\operatorname{dom} f) \cap
\operatorname{ri}(\operatorname{dom} g)$. Then $f$ and $g$ add exactly:
$(f + g)^* = f^* \mathbin{\square} g^*$, and the infimum in the infimal convolution is attained
at every point. This is Theorem 16.4 of [rockafellar1970convex].

Closedness is not needed. The proof reduces to `ConvexAnalysis.IsExactSum.of_relint_closed` by
`ConvexAnalysis.convexConj_add_eq_convexConj_convexCl_add_convexCl` and the fact that
$\operatorname{ri}(\operatorname{dom} f)$ does not change under closure. -/
theorem IsExactSum.of_relint [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hf : ConvexFn f) (hpf : ProperConvex f) (hg : ConvexFn g) (hpg : ProperConvex g)
    {x₀ : E} (hxf : x₀ ∈ ri (convexDom f)) (hxg : x₀ ∈ ri (convexDom g)) : IsExactSum B f g :=
  IsExactSum.of_convexCl hpf hpg
    (IsExactSum.of_relint_closed ⟨convexFn_convexCl hf, closedConvex_convexCl f,
        hf.properConvex_convexCl hpf⟩
      ⟨convexFn_convexCl hg, closedConvex_convexCl g, hg.properConvex_convexCl hpg⟩
      (by rw [hf.relint_convexDom_convexCl hpf]; exact hxf)
          (by rw [hg.relint_convexDom_convexCl hpg]; exact hxg))
    (convexConj_add_eq_convexConj_convexCl_add_convexCl hf hpf hg hpg
      (hf.tendstoConvexClAlongSegment hpf hxf) (hg.tendstoConvexClAlongSegment hpg hxg))

end Closure

/-! ### Dropping closedness on the image side -/

section ClosureImage

open Filter Topology

variable {E F G H : Type*}
  [AddCommGroup E] [Module ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ}
  {A : E →ₗ[ℝ] G} {A' : H →ₗ[ℝ] F} {g : G → EReal}

omit [FiniteDimensional ℝ G] [FiniteDimensional ℝ H] in
/-- **Passing to closures does not change the conjugate of a composition.** Let $A : E \to G$ be a
linear map from a real vector space into a normed space, and let $g$ be a function on $G$ that
is recovered along segments from $Ax_0$. Then
$$(gA)^* = ((\operatorname{cl} g)A)^*.$$

This is cheaper than `ConvexAnalysis.convexConj_add_eq_convexConj_convexCl_add_convexCl`: one
limit instead of two, so no properness is needed. The space $E$ needs no topology, since $A$
pushes the segment forward before any limit is taken. The form in [rockafellar1970convex] is
$\operatorname{cl}(gA) = (\operatorname{cl} g)A$ (`ConvexAnalysis.convexCl_compLin`), which
needs $E$ to be a finite-dimensional normed space. -/
theorem convexConj_compLin_eq_convexConj_compLin_convexCl (A : E →ₗ[ℝ] G) {x₀ : E}
    (hs : TendstoConvexClAlongSegment g (A x₀)) :
    convexConj B (compLin g A) = convexConj B (compLin (convexCl g) A) := by
  refine convexConj_eq_of_le_of_tendsto (x₀ := x₀) (fun x => convexCl_le g (A x)) fun x => ?_
  have hmap : ∀ a : ℝ, A ((1 - a) • x₀ + a • x) = (1 - a) • A x₀ + a • A x := fun a => by
    rw [map_add, map_smul, map_smul]
  simpa only [compLin_apply, hmap] using hs (A x)

/-- **A proper convex function pulls back exactly along a linear map whose range meets the relative
interior of its effective domain.** Let $B$ pair a real vector space $E$ with a normed space
$F$, and let $B'$ pair finite-dimensional normed spaces $G$ and $H$. Let $B'$, its flip and the
flip of $B$ be compatible with the topologies of $G$, $H$ and $F$. Let $A : E \to G$ and
$A' : H \to F$ be adjoint: $\langle Ax, z \rangle' = \langle x, A'z \rangle$. Let $g$ be a
proper convex function on $G$ with $Ax_0 \in \operatorname{ri}(\operatorname{dom} g)$ for some
$x_0 \in E$. Then $g$ pulls back exactly along $A$: $(gA)^* = A'(g^*)$, and for every $y \in F$
with $(gA)^*(y) < +\infty$ the infimum of $g^*$ over the fibre $\{z \in H \mid A'z = y\}$, which
defines $A'(g^*)(y)$, is attained. This is Theorem 16.3 of [rockafellar1970convex].

Closedness is not needed. The proof reduces to `ConvexAnalysis.IsExactImage.of_relint_closed` by
`ConvexAnalysis.convexConj_compLin_eq_convexConj_compLin_convexCl` and the fact that
$\operatorname{cl} g$ has the same relative interior of the effective domain as $g$. -/
theorem IsExactImage.of_relint [IsCompatiblePairing B'] [IsCompatiblePairing B'.flip]
    [IsCompatiblePairing B.flip] (hA : IsAdjointPair B B' A A') (hg : ConvexFn g)
        (hp : ProperConvex g)
    {x₀ : E} (hx₀ : A x₀ ∈ ri (convexDom g)) :
    IsExactImage B B' A A' hA g := by
  have hcl := IsExactImage.of_relint_closed hA
    ⟨convexFn_convexCl hg, closedConvex_convexCl g, hg.properConvex_convexCl hp⟩
    (show A x₀ ∈ ri (convexDom (convexCl g)) by rw [hg.relint_convexDom_convexCl hp]; exact hx₀)
  have heq : convexConj B (compLin g A) = convexConj B (compLin (convexCl g) A) :=
    convexConj_compLin_eq_convexConj_compLin_convexCl A (hg.tendstoConvexClAlongSegment hp hx₀)
  refine ⟨hp, fun y hy => ?_⟩
  obtain ⟨z, hz, hle⟩ := hcl.exact_le y (by rw [← heq]; exact hy)
  exact ⟨z, hz, by rwa [convexConj_convexCl, ← heq] at hle⟩

end ClosureImage

/-! ### Finitely many summands -/

section FinsetSum

variable {ι : Type*} {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {s : Finset ι} {f : ι → E → EReal}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Let $(f_i)_{i \in s}$ be a finite family of proper convex functions on $E$ whose effective
domains have a common point $x_0$. Then $\sum_{i \in s} f_i$ is convex and proper, and its
effective domain is $\bigcap_{i \in s} \operatorname{dom} f_i$. These are the three facts about
the sum that the constraint qualifications for two summands ask for. -/
theorem properConvexFn_finsetSum (hf : ∀ i ∈ s, ConvexFn (f i)) (hpf : ∀ i ∈ s, ProperConvex (f i))
    {x₀ : E} (hx₀ : ∀ i ∈ s, x₀ ∈ convexDom (f i)) :
    ConvexFn (∑ i ∈ s, f i) ∧ ProperConvex (∑ i ∈ s, f i) ∧ convexDom (∑ i ∈ s, f i) = ⋂ i ∈ s,
        convexDom (f i) := by
  have hbot : ∀ i ∈ s, ∀ x, f i x ≠ ⊥ := fun i hi x => (hpf i hi).ne_bot x
  have hdom : convexDom (∑ i ∈ s, f i) = ⋂ i ∈ s, convexDom (f i) := convexDom_finsetSum hbot
  have hfun : (∑ i ∈ s, f i) = fun x => ∑ i ∈ s, f i x := by
    funext x
    rw [Finset.sum_apply]
  refine ⟨by rw [hfun]; exact ConvexFn.sum hf hbot, ⟨⟨x₀, ?_⟩, fun x => ?_⟩, hdom⟩
  · rw [hdom]
    exact Set.mem_iInter₂.2 hx₀
  · rw [Finset.sum_apply]
    exact EReal.sum_ne_bot fun i hi => hbot i hi x

omit [FiniteDimensional ℝ F] in
/-- **The relative interior of the effective domain of a sum.** Let $E$ be a finite-dimensional
normed space and $(f_i)_{i \in s}$ a finite family of proper convex functions on $E$. If $x_0
\in \operatorname{ri}(\operatorname{dom} f_i)$ for every $i \in s$, then $x_0 \in
\operatorname{ri}(\operatorname{dom} \sum_{i \in s} f_i)$. -/
theorem mem_relint_convexDom_finsetSum (hf : ∀ i ∈ s, ConvexFn (f i))
    (hpf : ∀ i ∈ s, ProperConvex (f i))
    {x₀ : E} (hx₀ : ∀ i ∈ s, x₀ ∈ ri (convexDom (f i))) : x₀ ∈ ri (convexDom (∑ i ∈ s, f i)) := by
  rw [convexDom_finsetSum fun i hi x => (hpf i hi).ne_bot x,
    Convex.relint_biInter_finset (fun i hi => (hf i hi).convex_convexDom) hx₀]
  exact Set.mem_iInter₂.2 hx₀

/-- **Finitely many proper convex functions add exactly when the relative interiors of their
effective domains have a common point.** Let $E$ and $F$ be finite-dimensional normed spaces,
and let the pairing and its flip be compatible with their topologies. Let $(f_i)_{i \in s}$ be a
nonempty finite family of proper convex functions on $E$, and let $x_0 \in
\operatorname{ri}(\operatorname{dom} f_i)$ for every $i \in s$. Then the family adds exactly:
$(f_1 + \dots + f_m)^* = f_1^* \mathbin{\square} \dots \mathbin{\square} f_m^*$, and the infimum
in the infimal convolution is attained at every point. This is the form of Theorem 16.4 of
[rockafellar1970convex] for $m$ summands.

The proof is an induction with `ConvexAnalysis.IsExactFinsetSum.cons`. Beyond the case of two
summands, it needs only that the effective domain of a partial sum is
$\bigcap_i \operatorname{dom} f_i$ and that $x_0$ lies in the relative interior of this
intersection (`ConvexAnalysis.mem_relint_convexDom_finsetSum`). -/
theorem IsExactFinsetSum.of_relint [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hs : s.Nonempty) (hf : ∀ i ∈ s, ConvexFn (f i)) (hpf : ∀ i ∈ s, ProperConvex (f i)) {x₀ : E}
    (hx₀ : ∀ i ∈ s, x₀ ∈ ri (convexDom (f i))) : IsExactFinsetSum B s f := by
  induction s using Finset.cons_induction with
  | empty => exact absurd hs (by simp)
  | cons i t hi ih =>
    have hmt : ∀ j ∈ t, j ∈ Finset.cons i t hi := fun j hj => Finset.mem_cons_of_mem hj
    rcases Finset.eq_empty_or_nonempty t with rfl | htne
    · rw [Finset.cons_empty]
      exact IsExactFinsetSum.singleton (hpf i (by simp))
    refine IsExactFinsetSum.cons hi ?_
      (ih htne (fun j hj => hf j (hmt j hj)) (fun j hj => hpf j (hmt j hj))
        (fun j hj => hx₀ j (hmt j hj)))
    obtain ⟨hconv, hprop, -⟩ :=
      properConvexFn_finsetSum (fun j hj => hf j (hmt j hj)) (fun j hj => hpf j (hmt j hj))
        (fun j hj => intrinsicInterior_subset (hx₀ j (hmt j hj)))
    exact IsExactSum.of_relint (hf i (by simp)) (hpf i (by simp)) hconv hprop (hx₀ i (by simp))
      (mem_relint_convexDom_finsetSum (fun j hj => hf j (hmt j hj)) (fun j hj => hpf j (hmt j hj))
        (fun j hj => hx₀ j (hmt j hj)))

end FinsetSum

end ConvexAnalysis
