/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Bifunction.Algebra
import Numlib.Analysis.Convex.Duality.Relint
import Numlib.Analysis.Convex.Saddle.Kernel

/-!
# Co-finite bifunctions

A convex function is **co-finite** if it is closed, proper and convex, and its epigraph contains no
non-vertical half-line; equivalently, its recession function is $+\infty$ in every nonzero
direction. A convex bifunction $F$ from $U$ to $X$ is co-finite if every slice $Fu$ is a co-finite
convex function. Under this condition the algebra of bifunctions of
`Numlib.Analysis.Convex.Bifunction.Algebra` needs no side conditions: a co-finite bifunction has
effective domain $\operatorname{dom} F = U$ and a finite inner product
$\langle Fu, y \rangle = (Fu)^*(y)$ everywhere, so the relative-interior hypotheses hold
automatically. The presentation follows [rockafellar1970convex], §38, with the finiteness criterion
for conjugates of Corollary 13.3.1 applied slice by slice.

The module also proves the identity $\langle GFu, z \rangle = \langle u, F^* G^* z \rangle$ for a
product of bifunctions, for the same reason: it needs a relative interior, hence a topology and a
finite dimension.

## Main definitions

* `ConvexAnalysis.CofiniteBifun`: a convex bifunction all of whose slices are co-finite convex
  functions.

## Main results

* `ConvexAnalysis.CofiniteBifun.convexDomBifun_eq_univ` and `ConvexAnalysis.CofiniteBifun.proper`: a
  co-finite bifunction has full effective domain and is proper.
* `ConvexAnalysis.CofiniteBifun.bracket_lt_top` and
  `ConvexAnalysis.cofiniteBifun_of_forall_bracket_lt_top`: a convex bifunction with closed proper
  convex slices is co-finite if and only if $\langle Fu, y \rangle < +\infty$ for all $u$ and $y$.
  This is Corollary 13.3.1 of [rockafellar1970convex], slice by slice.
* `ConvexAnalysis.cofinite_infConv`, `ConvexAnalysis.cofiniteBifun_infConvBifun` and
  `ConvexAnalysis.convexAdjointBifun_infConvBifun_of_cofinite`: a remark of Rockafellar, that
  $F_1 \mathbin{\square} F_2$ is co-finite and $(F_1 \mathbin{\square} F_2)^* = F_1^*
  \mathbin{\square} F_2^*$ with no hypothesis beyond co-finiteness.
* `ConvexAnalysis.cofinite_smulRight` and `ConvexAnalysis.cofiniteBifun_smulRightBifun`: the same
  for the right scalar multiple $F \lambda$ with $\lambda > 0$.
* `ConvexAnalysis.cofiniteBifun_iff_convexDomBifun_eq_univ`: a closed proper convex bifunction is
  co-finite if and only if $\operatorname{dom} F = U$ and $\operatorname{dom} F^* = Y$.
* `ConvexAnalysis.CofiniteBifun.bracket_eq_concaveBracket_convexAdjointBifun`: $\langle Fu, y
  \rangle = \langle u, F^* y \rangle$ for every $u$.
* `ConvexAnalysis.bracket_compBifun_eq_concaveBracket_concaveCompBifun`: $\langle GFu, z \rangle =
  \langle u, F^* G^* z \rangle$ for a product of bifunctions, at a relative interior point.

## Implementation notes

* Rockafellar defines co-finiteness for convex bifunctions only. The convexity is extra data: the
  graph function of a bifunction whose slices are all convex need not be convex on $U \times X$. So
  `ConvexAnalysis.CofiniteBifun` has `ConvexAnalysis.ConvexBifun` as a field.
* Elsewhere the relative-interior conditions are hypotheses of the form `ConvexAnalysis.IsExactSum`.
  Here they are proved: the functions that are added are finite on the whole space, and
  `ConvexAnalysis.IsExactSum.of_relint` applies at the origin. This is why the spaces in this module
  are finite-dimensional normed spaces.
* Rockafellar deduces the criterion `ConvexAnalysis.cofiniteBifun_iff_convexDomBifun_eq_univ` from
  the correspondence between bifunctions and saddle functions. The proof here applies the finiteness
  criterion for conjugates to each slice.
-/

open Set

namespace ConvexAnalysis

/-! ### Co-finite bifunctions -/

section Defs

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace X] {F : Bifun U X}

/-- A bifunction $F$ from $U$ to $X$ is a **co-finite convex bifunction** if it is convex, that is,
its graph function $(u, x) \mapsto (Fu)(x)$ is convex on $U \times X$, and every slice $Fu$ is a
co-finite convex function. Such a bifunction has $\operatorname{dom} F = U$ and is proper
(`ConvexAnalysis.CofiniteBifun.convexDomBifun_eq_univ` and
`ConvexAnalysis.CofiniteBifun.proper`).

Co-finiteness of a function is `ConvexAnalysis.Cofinite`: closed, proper and convex, with
recession function $+\infty$ in every nonzero direction. -/
structure CofiniteBifun (F : Bifun U X) : Prop where
  /-- The bifunction is convex: its graph function is convex on $U \times X$. -/
  convexBifun : ConvexBifun F
  /-- Every slice $Fu$ is a co-finite convex function. -/
  cofinite_apply : ∀ u, Cofinite (F u)

/-- Every slice $Fu$ of a co-finite convex bifunction is a closed proper convex function. -/
theorem CofiniteBifun.closedProperConvexFn_apply (hF : CofiniteBifun F) (u : U) :
    ClosedProperConvexFn (F u) := (hF.cofinite_apply u).toClosedProperConvexFn

/-- **Co-finiteness gives a full effective domain.** Let $F$ be a co-finite convex bifunction from
$U$ to $X$. Then its effective domain $\operatorname{dom} F = \{u \in U \mid (Fu)(x) < +\infty
\text{ for some } x\}$ is all of $U$.

The reason is that every slice $Fu$ is proper. -/
theorem CofiniteBifun.convexDomBifun_eq_univ (hF : CofiniteBifun F) : convexDomBifun F = univ :=
  eq_univ_of_forall fun u =>
    mem_convexDomBifun_iff_convexDom_nonempty.2 (hF.cofinite_apply u).proper.convexDom_nonempty

/-- **A co-finite bifunction is proper.** Let $F$ be a co-finite convex bifunction from $U$ to $X$.
Then its graph function $(u, x) \mapsto (Fu)(x)$ is proper: it is finite somewhere and never
takes the value $-\infty$. -/
theorem CofiniteBifun.proper (hF : CofiniteBifun F) : ProperConvex (graphFn F) := by
  obtain ⟨x, hx⟩ := (hF.cofinite_apply (0 : U)).proper.convexDom_nonempty
  exact ⟨⟨((0 : U), x), hx⟩, fun p => (hF.cofinite_apply p.1).proper.ne_bot p.2⟩

/-- A co-finite convex bifunction never takes the value $-\infty$. -/
theorem CofiniteBifun.ne_bot (hF : CofiniteBifun F) (u : U) (x : X) : F u x ≠ ⊥ :=
  (hF.cofinite_apply u).proper.ne_bot x

end Defs

/-! ### Finiteness of the inner product -/

section BracketNeBot

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace X] [AddCommGroup Y] [Module ℝ Y] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  {F : Bifun U X}

/-- Let $F$ be a co-finite convex bifunction from $U$ to $X$. Then the inner product
$\langle Fu, y \rangle = (Fu)^*(y)$ is never $-\infty$, because every slice is proper. With
`ConvexAnalysis.CofiniteBifun.bracket_lt_top` it is finite. -/
theorem CofiniteBifun.bracket_ne_bot (hF : CofiniteBifun F) (u : U) (y : Y) :
    bracket Bx F u y ≠ ⊥ :=
  convexConj_ne_bot (hF.cofinite_apply u).proper.convexDom_nonempty y

end BracketNeBot

section Bracket

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
  {F : Bifun U X}

/-- **The inner product of a co-finite bifunction is finite above.** Let $U$ be a real vector space,
and let $X$ and $Y$ be real normed spaces, $Y$ finite-dimensional, paired by a bilinear form
$\langle x, y \rangle$ that is compatible with the topology on both sides. Let $F$ be a
co-finite convex bifunction from $U$ to $X$. Then for all $u \in U$ and $y \in Y$
$$\langle Fu, y \rangle = (Fu)^*(y) < +\infty.$$

The compatibility is `ConvexAnalysis.IsCompatiblePairing` for `Bx` and `Bx.flip`. The proof is
the finiteness criterion `ConvexAnalysis.cofinite_iff_forall_convexConj_lt_top` for the
conjugate of a co-finite function, applied to the slice $Fu$. -/
theorem CofiniteBifun.bracket_lt_top (hF : CofiniteBifun F) (u : U) (y : Y) :
    bracket Bx F u y < ⊤ :=
  (cofinite_iff_forall_convexConj_lt_top (B := Bx) (hF.closedProperConvexFn_apply u)).1
    (hF.cofinite_apply u) y

/-- **The converse of `ConvexAnalysis.CofiniteBifun.bracket_lt_top`.** Let $U$ be a real vector
space, and let $X$ and $Y$ be real normed spaces, $Y$ finite-dimensional, paired by a bilinear
form that is compatible with the topology on both sides. Let $F$ be a convex bifunction from $U$
to $X$ whose slices $Fu$ are closed proper convex functions, and let
$\langle Fu, y \rangle < +\infty$ for all $u \in U$ and $y \in Y$. Then $F$ is co-finite.

The proof is the finiteness criterion `ConvexAnalysis.cofinite_iff_forall_convexConj_lt_top`,
applied to each slice. -/
theorem cofiniteBifun_of_forall_bracket_lt_top (hF : ConvexBifun F)
    (hcl : ∀ u, ClosedProperConvexFn (F u)) (h : ∀ (u : U) (y : Y), bracket Bx F u y < ⊤) :
    CofiniteBifun F :=
  ⟨hF, fun u => (cofinite_iff_forall_convexConj_lt_top (B := Bx) (hcl u)).2 (h u)⟩

end Bracket

/-! ### Infimal convolution of co-finite functions -/

section CofiniteInfConv

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
  {f g : E → EReal}

omit [FiniteDimensional ℝ E] in
/-- **The conjugate of a co-finite function is finite above.** Let $E$ and $F$ be real normed
spaces, $F$ finite-dimensional, paired by a bilinear form $B$ that is compatible with the
topology on both sides. If $f$ is a co-finite convex function on $E$, then $f^*(y) < +\infty$
for every $y \in F$. -/
theorem Cofinite.convexConj_lt_top (hf : Cofinite f) (y : F) : convexConj B f y < ⊤ :=
  (cofinite_iff_forall_convexConj_lt_top (B := B) hf.toClosedProperConvexFn).1 hf y

/-- **The conjugates of two co-finite functions add exactly.** Let $E$ and $F$ be finite-dimensional
real normed spaces paired by a bilinear form $B$ that is compatible with the topology on both
sides, and let $f$ and $g$ be co-finite convex functions on $E$. Then $f^*$ and $g^*$ add
exactly with respect to the flipped pairing (`ConvexAnalysis.IsExactSum`): both are proper, and
the infimal convolution that gives the conjugate of $f^* + g^*$ is attained everywhere. The
effective domains of $f^*$ and $g^*$ are the whole space, so the relative-interior condition
holds at the origin. -/
theorem Cofinite.isExactSum_convexConj (hf : Cofinite f) (hg : Cofinite g) :
    IsExactSum B.flip (convexConj B f) (convexConj B g) := by
  have hdf : (0 : F) ∈ ri (convexDom (convexConj B f)) := by
    rw [Cofinite.convexDom_convexConj_eq_univ (B := B) hf, intrinsicInterior_univ]; trivial
  have hdg : (0 : F) ∈ ri (convexDom (convexConj B g)) := by
    rw [Cofinite.convexDom_convexConj_eq_univ (B := B) hg, intrinsicInterior_univ]; trivial
  exact IsExactSum.of_relint (convexFn_convexConj B f)
      (properConvex_convexConj hf.toClosedProperConvexFn)
    (convexFn_convexConj B g) (properConvex_convexConj hg.toClosedProperConvexFn) hdf hdg

/-- **The infimal convolution of two co-finite functions is a conjugate.** Let $E$ and $F$ be
finite-dimensional real normed spaces paired by a bilinear form $B$ that is compatible with the
topology on both sides, and let $f$ and $g$ be co-finite convex functions on $E$. Then
$$f \mathbin{\square} g = (f^* + g^*)^*,$$
the outer conjugate being taken with respect to the flipped pairing. In particular
$f \mathbin{\square} g$ is closed. -/
theorem Cofinite.infConv_eq_convexConj_add (hf : Cofinite f) (hg : Cofinite g) :
    infConv f g = convexConj B.flip (convexConj B f + convexConj B g) := by
  have hbf : convexConj B.flip (convexConj B f) = f := convexBiconj_eq_self hf.convex hf.closed
  have hbg : convexConj B.flip (convexConj B g) = g := convexBiconj_eq_self hg.convex hg.closed
  rw [(Cofinite.isExactSum_convexConj (B := B) hf hg).convexConj_add, hbf, hbg]

omit [FiniteDimensional ℝ E] in
/-- Let $E$ and $F$ be real normed spaces, $F$ finite-dimensional, paired by a bilinear form that is
compatible with the topology on both sides. If $f$ and $g$ are co-finite convex functions on
$E$, then the sum $f^* + g^*$ of their conjugates is proper: it is finite somewhere and never
$-\infty$. -/
theorem Cofinite.properConvex_convexConj_add (hf : Cofinite f) (hg : Cofinite g) :
    ProperConvex (convexConj B f + convexConj B g) := by
  refine ⟨⟨0, ?_⟩, fun y => ?_⟩
  · rw [mem_convexDom, Pi.add_apply]
    exact EReal.add_lt_top (Cofinite.convexConj_lt_top (B := B) hf 0).ne
      (Cofinite.convexConj_lt_top (B := B) hg 0).ne
  · rw [Pi.add_apply, ne_eq, EReal.add_eq_bot_iff]
    push Not
    exact ⟨convexConj_ne_bot hf.proper.convexDom_nonempty y,
        convexConj_ne_bot hg.proper.convexDom_nonempty y⟩

/-- **The infimal convolution of two co-finite convex functions is co-finite.** Let $E$ and $F$ be
finite-dimensional real normed spaces paired by a bilinear form $B$ that is compatible with the
topology on both sides, and let $f$ and $g$ be co-finite convex functions on $E$. Then the
infimal convolution
$$(f \mathbin{\square} g)(x) = \inf \{ f(x_1) + g(x_2) \mid x_1 + x_2 = x \}$$
is a co-finite convex function.

The pairing $B$ is used only in the proof. By
`ConvexAnalysis.Cofinite.infConv_eq_convexConj_add`, $f \mathbin{\square} g$ is the conjugate of
$f^* + g^*$, hence closed proper convex, and its own conjugate is $f^* + g^*$, which is finite
everywhere. -/
theorem cofinite_infConv (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    [IsCompatiblePairing B] [IsCompatiblePairing B.flip] (hf : Cofinite f) (hg : Cofinite g) :
    Cofinite (infConv f g) := by
  have heq : infConv f g = convexConj B.flip (convexConj B f + convexConj B g) :=
    Cofinite.infConv_eq_convexConj_add (B := B) hf hg
  have hproper : ProperConvex (infConv f g) := by
    refine ⟨?_, fun x => ?_⟩
    · obtain ⟨x, hx⟩ := hf.proper.convexDom_nonempty
      obtain ⟨z, hz⟩ := hg.proper.convexDom_nonempty
      exact ⟨x + z, by rw [convexDom_infConv]; exact ⟨x, hx, z, hz, rfl⟩⟩
    · rw [heq]
      exact convexConj_ne_bot
          (Cofinite.properConvex_convexConj_add (B := B) hf hg).convexDom_nonempty x
  have hclosed : ClosedConvex (infConv f g) := by rw [heq]; exact closedConvex_convexConj
  have hcpc : ClosedProperConvexFn (infConv f g) :=
    ⟨convexFn_infConv hf.convex hg.convex, hclosed, hproper⟩
  refine (cofinite_iff_forall_convexConj_lt_top (B := B) hcpc).2 fun y => ?_
  rw [convexConj_infConv, Pi.add_apply]
  exact EReal.add_lt_top (Cofinite.convexConj_lt_top (B := B) hf y).ne
    (Cofinite.convexConj_lt_top (B := B) hg y).ne

end CofiniteInfConv

/-! ### Infimal convolution of co-finite bifunctions -/

section CofiniteAlgebra

variable {U V X Y : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip]
  {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
  {F F₁ F₂ : Bifun U X}

omit [FiniteDimensional ℝ U] in
/-- **The infimal convolute of two co-finite bifunctions is co-finite.** Let $U$ be a real normed
space, and let $X$ and $Y$ be finite-dimensional real normed spaces paired by a bilinear form
that is compatible with the topology on both sides. If $F_1$ and $F_2$ are co-finite convex
bifunctions from $U$ to $X$, then so is their infimal convolute $F_1 \mathbin{\square} F_2$,
$(F_1 \mathbin{\square} F_2) u = F_1 u \mathbin{\square} F_2 u$.

Slice by slice this is `ConvexAnalysis.cofinite_infConv`. The convexity of
$F_1 \mathbin{\square} F_2$ is `ConvexAnalysis.convexBifun_infConvBifun`. -/
theorem cofiniteBifun_infConvBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hF₁ : CofiniteBifun F₁)
    (hF₂ : CofiniteBifun F₂) : CofiniteBifun (infConvBifun F₁ F₂) :=
  ⟨convexBifun_infConvBifun hF₁.ne_bot hF₂.ne_bot hF₁.convexBifun hF₂.convexBifun,
    fun u => cofinite_infConv Bx (hF₁.cofinite_apply u) (hF₂.cofinite_apply u)⟩

omit [FiniteDimensional ℝ X] in
/-- Let $U$ and $V$ be finite-dimensional real normed spaces paired by a bilinear form that is
compatible with the topology on both sides, and let $X$ and $Y$ be real normed spaces, $Y$
finite-dimensional, paired in the same way. Let $F_1$ and $F_2$ be co-finite convex bifunctions
from $U$ to $X$, and let $y \in Y$. Then the functions $u \mapsto -\langle F_1 u, y \rangle$ and
$u \mapsto -\langle F_2 u, y \rangle$ on $U$ add exactly (`ConvexAnalysis.IsExactSum`), because
both are finite everywhere.

This removes the exactness hypothesis of `ConvexAnalysis.convexAdjointBifun_infConvBifun` for
co-finite bifunctions. -/
theorem isExactSum_neg_bracket_of_cofinite (hF₁ : CofiniteBifun F₁) (hF₂ : CofiniteBifun F₂)
    (y : Y) : IsExactSum Bu (fun u => -(bracket Bx F₁ u y)) (fun u => -(bracket Bx F₂ u y)) := by
  have hp : ∀ G : Bifun U X, CofiniteBifun G → ProperConvex (fun u => -(bracket Bx G u y)) := by
    intro G hG
    refine ⟨⟨0, ?_⟩, fun u => ?_⟩
    · rw [mem_convexDom, lt_top_iff_ne_top, ne_eq, EReal.neg_eq_top_iff]
      exact CofiniteBifun.bracket_ne_bot (Bx := Bx) hG 0 y
    · rw [ne_eq, EReal.neg_eq_bot_iff]
      exact (CofiniteBifun.bracket_lt_top (Bx := Bx) hG u y).ne
  have hd : ∀ G : Bifun U X, CofiniteBifun G →
      (0 : U) ∈ ri (convexDom fun u => -(bracket Bx G u y)) := by
    intro G hG
    have hdom : (convexDom fun u => -(bracket Bx G u y)) = univ :=
      eq_univ_of_forall fun u => by
        rw [mem_convexDom, lt_top_iff_ne_top, ne_eq, EReal.neg_eq_top_iff]
        exact CofiniteBifun.bracket_ne_bot (Bx := Bx) hG u y
    rw [hdom, intrinsicInterior_univ]; trivial
  exact IsExactSum.of_relint (concaveFn_iff_convexFn_neg.1 (concaveFn_bracket hF₁.convexBifun Bx y))
    (hp F₁ hF₁) (concaveFn_iff_convexFn_neg.1 (concaveFn_bracket hF₂.convexBifun Bx y))
    (hp F₂ hF₂) (hd F₁ hF₁) (hd F₂ hF₂)

omit [FiniteDimensional ℝ X] in
/-- **The adjoint of an infimal convolute of co-finite bifunctions.** Let $U$ and $V$ be
finite-dimensional real normed spaces paired by a bilinear form that is compatible with the
topology on both sides, and let $X$ and $Y$ be real normed spaces, $Y$ finite-dimensional,
paired in the same way. Let $F_1$ and $F_2$ be co-finite convex bifunctions from $U$ to $X$.
Then
$$(F_1 \mathbin{\square} F_2)^* = F_1^* \mathbin{\square} F_2^*,$$
where the right side is the supremal convolute of the concave bifunctions $F_1^*$ and $F_2^*$
from $Y$ to $V$.

This is `ConvexAnalysis.convexAdjointBifun_infConvBifun_eq_supConvBifun` with the exactness
hypothesis supplied by `ConvexAnalysis.isExactSum_neg_bracket_of_cofinite`. -/
theorem convexAdjointBifun_infConvBifun_of_cofinite (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
    (hF₁ : CofiniteBifun F₁) (hF₂ : CofiniteBifun F₂) :
    convexAdjointBifun Bu Bx (infConvBifun F₁ F₂)
      = supConvBifun (convexAdjointBifun Bu Bx F₁) (convexAdjointBifun Bu Bx F₂) :=
  convexAdjointBifun_infConvBifun_eq_supConvBifun Bu Bx F₁ F₂
    (isExactSum_neg_bracket_of_cofinite hF₁ hF₂)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] in
/-- **For a co-finite bifunction the two inner products agree at every point.** Let $U$ be a
finite-dimensional real normed space paired with a real normed space $V$ by a bilinear form that
is compatible with the topology of $U$, and let $X$ be a real normed space paired with $Y$. Let
$F$ be a co-finite convex bifunction from $U$ to $X$. Then for all $u \in U$ and $y \in Y$
$$\langle Fu, y \rangle = \langle u, F^* y \rangle,$$
where $\langle u, F^* y \rangle = \inf_v \{ \langle u, v \rangle - (F^* y)(v) \}$ is the concave
inner product with the adjoint.

The two inner products agree on the relative interior of $\operatorname{dom} F$, and
$\operatorname{dom} F$ is all of $U$. The right side is `ConvexAnalysis.concaveBracket`. -/
theorem CofiniteBifun.bracket_eq_concaveBracket_convexAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hF : CofiniteBifun F) (u : U) (y : Y) :
    bracket Bx F u y = concaveBracket Bu (convexAdjointBifun Bu Bx F) u y :=
  bracket_eq_concaveBracket_convexAdjointBifun_of_mem_relint Bu Bx hF.convexBifun
    (by rw [hF.convexDomBifun_eq_univ, intrinsicInterior_univ]; trivial) y

end CofiniteAlgebra

/-! ### Right scalar multiplication of co-finite functions -/

section CofiniteSmulRight

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {f : E → EReal} {a : ℝ}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- **The right scalar multiple $f a$ is the conjugate of $a f^*$.** Let $E$ and $F$ be real normed
spaces paired by a bilinear form $B$ that is compatible with the topology of $E$, let $f$ be a
closed convex function on $E$, and let $a > 0$. Then the right scalar multiple
$(f a)(x) = a f(a^{-1} x)$ satisfies
$$f a = (a f^*)^*,$$
the outer conjugate being taken with respect to the flipped pairing.

The proof is the conjugation rule `ConvexAnalysis.convexConj_smul` at $g = f^*$, with the
Fenchel–Moreau theorem turning $f^{**}$ back into $f$. The identity gives the closedness of
$f a$, which the definition of `ConvexAnalysis.smulRight` through the scaled epigraph does not
show. -/
theorem smulRight_eq_convexConj_smul (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    [IsCompatiblePairing B] (hc : ConvexFn f) (hcl : ClosedConvex f)
    (ha : 0 < a) : smulRight f a = convexConj B.flip (fun y => (a : EReal) * convexConj B f y) := by
  have hbi : convexConj B.flip (convexConj B f) = f := convexBiconj_eq_self hc hcl
  rw [convexConj_smul ha B.flip (convexConj B f), hbi]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Let $E$ and $F$ be real normed spaces paired by a bilinear form $B$ that is compatible with the
topology of $E$. If $f$ is a closed convex function on $E$ and $a > 0$, then the right scalar
multiple $f a$ is closed. It is a conjugate, by `ConvexAnalysis.smulRight_eq_convexConj_smul`. -/
theorem closedConvex_smulRight (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    [IsCompatiblePairing B] (hc : ConvexFn f) (hcl : ClosedConvex f)
    (ha : 0 < a) : ClosedConvex (smulRight f a) := by
  rw [smulRight_eq_convexConj_smul B hc hcl ha]
  exact closedConvex_convexConj

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
/-- For a real number $a > 0$ and an extended real number $u \neq -\infty$, the product $a u$ is not
$-\infty$. -/
theorem coe_mul_ne_bot (ha : 0 < a) {u : EReal} (hu : u ≠ ⊥) : (a : EReal) * u ≠ ⊥ := by
  intro h
  refine EReal.coe_mul_ne_top ha (u := -u) (by rwa [Ne, EReal.neg_eq_top_iff]) ?_
  rw [mul_neg, h, EReal.neg_bot]

omit [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
/-- If $f$ is a proper function on $E$ and $a > 0$, then the right scalar multiple $f a$,
$(f a)(x) = a f(a^{-1} x)$, is proper. -/
theorem properConvex_smulRight (hf : ProperConvex f)
    (ha : 0 < a) : ProperConvex (smulRight f a) := by
  refine ⟨?_, fun x => ?_⟩
  · obtain ⟨x₀, hx₀⟩ := hf.convexDom_nonempty
    refine ⟨a • x₀, mem_convexDom.2 (lt_top_iff_ne_top.2 ?_)⟩
    rw [smulRight_apply_pos ha, inv_smul_smul₀ ha.ne']
    exact EReal.coe_mul_ne_top ha (mem_convexDom.1 hx₀).ne
  · rw [smulRight_apply_pos ha]
    exact coe_mul_ne_bot ha (hf.ne_bot _)

omit [FiniteDimensional ℝ E] in
/-- **Right scalar multiplication preserves co-finiteness.** Let $E$ be a real normed space and $F$
a finite-dimensional real normed space, paired by a bilinear form $B$ that is compatible with
the topology on both sides. If $f$ is a co-finite convex function on $E$ and $a > 0$, then the
right scalar multiple $(f a)(x) = a f(a^{-1} x)$ is co-finite.

The pairing $B$ is used only in the proof. -/
theorem cofinite_smulRight (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    [IsCompatiblePairing B] [IsCompatiblePairing B.flip] (hf : Cofinite f) (ha : 0 < a) :
    Cofinite (smulRight f a) := by
  have hne : ∀ y : F, (a : EReal) * convexConj B f y ≠ ⊤ :=
    fun y => EReal.coe_mul_ne_top ha (Cofinite.convexConj_lt_top (B := B) hf y).ne
  have hcpc : ClosedProperConvexFn (smulRight f a) :=
    ⟨convexFn_smulRight a hf.convex, closedConvex_smulRight B hf.convex hf.closed ha,
      properConvex_smulRight hf.proper ha⟩
  refine (cofinite_iff_forall_convexConj_lt_top (B := B) hcpc).2 fun y => ?_
  rw [convexConj_smulRight ha B f]
  exact lt_top_iff_ne_top.2 (hne y)

end CofiniteSmulRight

/-! ### Right scalar multiplication, and the co-finiteness criterion -/

section CofiniteCriterion

variable {U V X Y : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip]
  {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
  {F : Bifun U X} {l : ℝ}

omit [FiniteDimensional ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [FiniteDimensional ℝ X] in
/-- **Right scalar multiplication preserves co-finite bifunctions.** Let $U$ be a real normed space,
and let $X$ and $Y$ be real normed spaces, $Y$ finite-dimensional, paired by a bilinear form
that is compatible with the topology on both sides. If $F$ is a co-finite convex bifunction from
$U$ to $X$ and $\lambda > 0$, then so is the right scalar multiple $F \lambda$, $((F \lambda)
u)(x) = \lambda (Fu)(\lambda^{-1} x)$.

Slice by slice this is `ConvexAnalysis.cofinite_smulRight`. The convexity of $F \lambda$ is
`ConvexAnalysis.convexBifun_smulRightBifun`. -/
theorem cofiniteBifun_smulRightBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hF : CofiniteBifun F) (hl : 0 < l) :
    CofiniteBifun (smulRightBifun F l) :=
  ⟨convexBifun_smulRightBifun hl hF.convexBifun,
    fun u => cofinite_smulRight Bx (hF.cofinite_apply u) hl⟩

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ X] in
/-- **The adjoint of a co-finite bifunction has full effective domain.** Let $U$ be a
finite-dimensional real normed space paired with a real normed space $V$ by a bilinear form that
is compatible with the topology of $U$, and let $X$ and $Y$ be real normed spaces, $Y$
finite-dimensional, paired by a bilinear form that is compatible with the topology on both
sides. If $F$ is a co-finite convex bifunction from $U$ to $X$, then the effective domain
$\operatorname{dom} F^* = \{ y \mid (F^* y)(v) > -\infty \text{ for some } v \}$ of the concave
bifunction $F^*$ is all of $Y$.

This is one half of the criterion `ConvexAnalysis.cofiniteBifun_iff_convexDomBifun_eq_univ`. The
function $u \mapsto \langle Fu, y \rangle$ is a finite concave function on $U$, so its negative
is proper convex and its conjugate is proper. The relation between the signs carries this back
to $F^* y$. -/
theorem CofiniteBifun.concaveDomBifun_convexAdjointBifun_eq_univ (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : CofiniteBifun F) :
    concaveDomBifun (convexAdjointBifun Bu Bx F) = univ := by
  refine eq_univ_of_forall fun y => ?_
  have hgc : ConvexFn (fun u => -(bracket Bx F u y)) :=
    concaveFn_iff_convexFn_neg.1 (concaveFn_bracket hF.convexBifun Bx y)
  have hgp : ProperConvex (fun u => -(bracket Bx F u y)) := by
    refine ⟨⟨0, mem_convexDom.2 (lt_top_iff_ne_top.2 ?_)⟩, fun u => ?_⟩
    · rw [ne_eq, EReal.neg_eq_top_iff]
      exact CofiniteBifun.bracket_ne_bot (Bx := Bx) hF 0 y
    · rw [ne_eq, EReal.neg_eq_bot_iff]
      exact (CofiniteBifun.bracket_lt_top (Bx := Bx) hF u y).ne
  obtain ⟨w, hw⟩ := (properConvex_convexConj_of_properConvex (B := Bu) hgc hgp).convexDom_nonempty
  refine ⟨-w, ?_⟩
  have hneg : -(concaveConj Bu (fun u => bracket Bx F u y) (-w))
      = convexConj Bu (fun u => -(bracket Bx F u y)) w := by
    rw [neg_concaveConj, neg_neg]
  rw [convexAdjointBifun_eq_concaveConj_bracket, ne_eq, ← EReal.neg_eq_top_iff, hneg]
  exact (mem_convexDom.1 hw).ne

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ V] [FiniteDimensional ℝ X]
  [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] in
/-- **A closed proper convex bifunction with full domains is co-finite.** Let $X$ and $Y$ be real
normed spaces, $Y$ finite-dimensional, paired by a bilinear form that is compatible with the
topology on both sides, and let $U$ be a real normed space paired with $V$. Let $F$ be a convex
bifunction from $U$ to $X$ whose graph function is closed and proper, with
$\operatorname{dom} F = U$ and $\operatorname{dom} F^* = Y$. Then $F$ is co-finite.

The condition $\operatorname{dom} F = U$ makes every $\langle Fu, y \rangle$ greater than
$-\infty$. The condition $\operatorname{dom} F^* = Y$ makes it less than $+\infty$: if
$\langle F u_0, y \rangle = +\infty$ for a single $u_0$, then $F^* y \equiv -\infty$. The
finiteness criterion for conjugates, applied to each slice, concludes. -/
theorem cofiniteBifun_of_convexDomBifun_eq_univ (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hp : ProperConvex (graphFn F)) (hdom : convexDomBifun F = univ)
    (hadj : concaveDomBifun (convexAdjointBifun Bu Bx F) = univ) : CofiniteBifun F := by
  refine cofiniteBifun_of_forall_bracket_lt_top (Bx := Bx) hF (fun u => ?_) (fun u y => ?_)
  · refine ⟨hF.convexFn_apply u, hcl.imageClosedBifun u, ⟨?_, fun x => hp.ne_bot (u, x)⟩⟩
    exact mem_convexDomBifun_iff_convexDom_nonempty.1 (by rw [hdom]; trivial)
  · rcases lt_or_eq_of_le (le_top : bracket Bx F u y ≤ ⊤) with h | htop
    · exact h
    · exfalso
      obtain ⟨v, hv⟩ : y ∈ concaveDomBifun (convexAdjointBifun Bu Bx F) := by rw [hadj]; trivial
      refine hv ?_
      rw [convexAdjointBifun_eq_concaveConj_bracket]
      exact congrFun (concaveConj_of_eq_top (B := Bu)
        (g := fun u' => bracket Bx F u' y) htop) v

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ X] [IsCompatiblePairing Bu.flip] in
/-- **The co-finiteness criterion.** Let $U$ be a finite-dimensional real normed space paired with a
real normed space $V$ by a bilinear form that is compatible with the topology of $U$, and let
$X$ and $Y$ be real normed spaces, $Y$ finite-dimensional, paired by a bilinear form that is
compatible with the topology on both sides. Let $F$ be a convex bifunction from $U$ to $X$ whose
graph function is closed and proper. Then $F$ is co-finite if and only if
$$\operatorname{dom} F = U \quad \text{and} \quad \operatorname{dom} F^* = Y.$$

The proof applies the finiteness criterion for conjugates to each slice. Rockafellar deduces the
criterion from the correspondence between bifunctions and saddle functions. -/
theorem cofiniteBifun_iff_convexDomBifun_eq_univ (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hp : ProperConvex (graphFn F)) :
    CofiniteBifun F ↔
      convexDomBifun F = univ ∧ concaveDomBifun (convexAdjointBifun Bu Bx F) = univ :=
  ⟨fun h => ⟨h.convexDomBifun_eq_univ,
      CofiniteBifun.concaveDomBifun_convexAdjointBifun_eq_univ Bu Bx h⟩,
    fun h => cofiniteBifun_of_convexDomBifun_eq_univ hF hcl hp h.1 h.2⟩

end CofiniteCriterion

/-! ### The inner product of a product of bifunctions -/

section CompBifunBracket

variable {U V X W Y Z : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup X] [Module ℝ X] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z]
  {F : Bifun U X} {G : Bifun X Y}

/-- **The inner product of a product of bifunctions, moved to the first factor.** Let $U$ be a
finite-dimensional real normed space paired with $V$ by a bilinear form that is compatible with
the topology of $U$, and let $X$, $Y$ be real vector spaces paired with $W$, $Z$. Let $F$ be a
bifunction from $U$ to $X$ that never takes the value $-\infty$, let $G$ be a bifunction from
$X$ to $Y$, and let the product $GF$ be convex. Let $u$ be in the relative interior of
$\operatorname{dom}(GF)$, let $z \in Z$, and for every $v \in V$ let the functions $x \mapsto
\langle v, F_* x \rangle = \inf_{u'} \{ \langle u', v \rangle + (Fu')(x) \}$ and
$x \mapsto -\langle Gx, z \rangle$ add exactly. Then
$$\langle (GF) u, z \rangle = \langle u, (F^* G^*) z \rangle,$$
where $F^* G^*$ is the concave product $((F^* G^*) z)(v) = \sup_w \{ (G^* z)(w) + (F^* w)(v)
\}$.

The two inner products of $GF$ agree at a relative interior point of $\operatorname{dom}(GF)$,
and `ConvexAnalysis.convexAdjointBifun_compBifun` rewrites $(GF)^*$ as $F^* G^*$. The companion
equality $\langle (GF) u, z \rangle = \langle Fu, G^* z \rangle$ is
`ConvexAnalysis.bracket_compBifun_eq_fenchelPairing`. Exact addition is
`ConvexAnalysis.IsExactSum`. -/
theorem bracket_compBifun_eq_concaveBracket_concaveCompBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] (Bx : X →ₗ[ℝ] W →ₗ[ℝ] ℝ) (By : Y →ₗ[ℝ] Z →ₗ[ℝ] ℝ)
    (hbF : ∀ u x, F u x ≠ ⊥) (hGF : ConvexBifun (compBifun G F)) {u : U}
    (hu : u ∈ ri (convexDomBifun (compBifun G F))) {z : Z}
    (hex : ∀ v : V, IsExactSum Bx (concaveBracket Bu.flip (inverseBifun F) v)
      (fun x => -(bracket By G x z))) :
    bracket By (compBifun G F) u z
      = concaveBracket
          Bu (concaveCompBifun (convexAdjointBifun Bx By G) (convexAdjointBifun Bu Bx F)) u z := by
  rw [bracket_eq_concaveBracket_convexAdjointBifun_of_mem_relint Bu By hGF hu z,
      concaveBracket_apply,
    concaveBracket_apply]
  exact iInf_congr fun v => by rw [convexAdjointBifun_compBifun Bu Bx By hbF (hex v)]

end CompBifunBracket

end ConvexAnalysis
