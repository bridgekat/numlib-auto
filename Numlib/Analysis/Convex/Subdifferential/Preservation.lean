/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Duality.Ops
import Numlib.Analysis.Convex.Operations.Closed
import Numlib.Analysis.Convex.Duality.Relint
import Numlib.Analysis.Convex.Recession.Closedness
import Numlib.Analysis.Convex.Subdifferential.StrictlyConvex

/-!
# Preservation of essential smoothness

Let $E$ and $G$ be finite-dimensional real inner product spaces. Essential smoothness of closed
proper convex functions is preserved by infimal convolution $f_1 \mathbin{\square} f_2$ and by the
image $Af$ under a linear map $A \colon E \to G$, under the usual exactness hypotheses. These are
Corollaries 26.3.2 and 26.3.3 of [rockafellar1970convex].

Both proofs use one argument. A closed proper convex function $f$ is essentially smooth if and only
if $f^*$ is essentially strictly convex
(`ConvexAnalysis.essentiallyStrictlyConvex_convexConj_iff_essentiallySmooth`). On the conjugate
side, infimal convolution becomes the sum $f_1^* + f_2^*$, and the image under $A$ becomes the
composition $f^* A'$ with the transpose $A'$. The rules of subdifferential calculus put the domain
of the subdifferential of this dual function inside $\operatorname{dom} \partial f^*$ (or
$\operatorname{dom} \partial f_1^*$). Strict convexity there survives the addition of a convex
function and the composition with an injective linear map. The same duality, read backwards, gives
essential smoothness.

## Main results

* `ConvexAnalysis.StrictConvexOnFn.add_convexFn`: a sum with a strictly convex summand is strictly
  convex.
* `ConvexAnalysis.StrictConvexOnFn.compLin`: strict convexity pulls back along an injective linear
  map.
* `ConvexAnalysis.IsExactSum.essentiallyStrictlyConvex_add`: if $g_1$ is essentially strictly convex
  and $g_1 + g_2$ adds exactly, then $g_1 + g_2$ is essentially strictly convex.
* `ConvexAnalysis.IsExactSum.essentiallySmooth_infConv`: if $f_1$ is essentially smooth and $f_1^*$
  and $f_2^*$ add exactly, then $f_1 \mathbin{\square} f_2$ is essentially smooth
  ([rockafellar1970convex], Corollary 26.3.2).
* `ConvexAnalysis.essentiallySmooth_infConv_of_relint`: the same when
  $\operatorname{ri}(\operatorname{dom} f_1^*) \cap \operatorname{ri}(\operatorname{dom} f_2^*) \neq
  \emptyset$.
* `ConvexAnalysis.IsExactImage.essentiallyStrictlyConvex_compLin`: if $g$ is essentially strictly
  convex and pulls back exactly along an injective $A'$, then $g A'$ is essentially strictly convex.
* `ConvexAnalysis.IsExactImage.essentiallySmooth_mapLin`: if $f$ is essentially smooth, $A'$ is
  injective and $f^*$ pulls back exactly along $A'$, then $Af$ is essentially smooth
  ([rockafellar1970convex], Corollary 26.3.3).
* `ConvexAnalysis.essentiallySmooth_mapLin_of_relint`: the same when $A$ is onto and $A' y \in
  \operatorname{ri}(\operatorname{dom} f^*)$ for some $y$.

## Implementation notes

* The result on linear images uses the exactness condition `ConvexAnalysis.IsExactImage` for the
  transpose $A'$, because the identity behind it is $Af = (f^* A')^*$. The surjectivity of $A$ is
  used only through the injectivity of $A'$.
* The transpose $A' \colon G \to E$ is data, with the adjointness $\langle A' z, x \rangle = \langle
  z, Ax \rangle$ given as `IsAdjointPair (innerₗ G) (innerₗ E) A' A`.
-/

open Pointwise

namespace ConvexAnalysis

/-! ### Strict convexity under addition and under precomposition -/

section StrictConvexOps

variable {E G : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup G] [Module ℝ G]
  {f g : E → EReal} {C : Set E}

/-- Let $C \subseteq E$ be convex, let $f$ be strictly convex on $C$, let $g$ be convex, and let $f$
and $g$ be proper and finite on $C$. Then $f + g$ is strictly convex on $C$.

Both functions must be finite on $C$. The strict inequality for $f$ holds trivially at points
where $f = +\infty$, but the strict inequality for $f + g$ does not. -/
theorem StrictConvexOnFn.add_convexFn (hC : Convex ℝ C) (hsc : StrictConvexOnFn f C)
    (hg : ConvexFn g) (hpf : ProperConvex f) (hpg : ProperConvex g) (hCf : C ⊆ convexDom f)
        (hCg : C ⊆ convexDom g) :
    StrictConvexOnFn (f + g) C := by
  intro x hx y hy hne a b ha hb hab
  have hz : a • x + b • y ∈ C := hC hx hy ha.le hb.le hab
  have hstrict := hsc hx hy hne ha hb hab
  have hconv := (convexFn_iff_le hpg.ne_bot).1 hg x y a b ha hb hab
  have hcf : ∀ ⦃z : E⦄, z ∈ C → f z = ((f z).toReal : EReal) := fun z hzC =>
    (EReal.coe_toReal (mem_convexDom.1 (hCf hzC)).ne (hpf.ne_bot z)).symm
  have hcg : ∀ ⦃z : E⦄, z ∈ C → g z = ((g z).toReal : EReal) := fun z hzC =>
    (EReal.coe_toReal (mem_convexDom.1 (hCg hzC)).ne (hpg.ne_bot z)).symm
  rw [hcf hx, hcf hy, hcf hz] at hstrict
  rw [hcg hx, hcg hy, hcg hz] at hconv
  rw [Pi.add_apply, Pi.add_apply, Pi.add_apply, hcf hx, hcf hy, hcf hz, hcg hx, hcg hy, hcg hz]
  simp only [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_lt_coe_iff,
    EReal.coe_le_coe_iff] at hstrict hconv ⊢
  linarith

/-- Let $C \subseteq E$ be convex, let $f$ be convex, let $g$ be strictly convex on $C$, and let $f$
and $g$ be proper and finite on $C$. Then $f + g$ is strictly convex on $C$. -/
theorem ConvexFn.add_strictConvexOnFn (hC : Convex ℝ C) (hf : ConvexFn f)
    (hsc : StrictConvexOnFn g C) (hpf : ProperConvex f) (hpg : ProperConvex g)
        (hCf : C ⊆ convexDom f)
    (hCg : C ⊆ convexDom g) : StrictConvexOnFn (f + g) C := by
  rw [add_comm]
  exact StrictConvexOnFn.add_convexFn hC hsc hf hpg hpf hCg hCf

/-- Let $A \colon G \to E$ be an injective linear map, let $D \subseteq G$, and let
$f \colon E \to [-\infty, +\infty]$ be strictly convex on $A(D)$. Then the composition
$f \circ A$ is strictly convex on $D$. -/
theorem StrictConvexOnFn.compLin {A : G →ₗ[ℝ] E} {D : Set G} (h : StrictConvexOnFn f (A '' D))
    (hinj : Function.Injective A) : StrictConvexOnFn (compLin f A) D := by
  intro x hx y hy hne a b ha hb hab
  have hlt := h ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ (fun hc => hne (hinj hc)) ha hb hab
  simpa only [compLin_apply, map_add, map_smul] using hlt

end StrictConvexOps

/-! ### Infimal convolution -/

section InfConv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f₁ f₂ : E → EReal}

omit [FiniteDimensional ℝ E] in
/-- Let $E$ be a real inner product space, let $g_1, g_2 \colon E \to [-\infty, +\infty]$, let $g_2$
be convex, and let $g_1$ and $g_2$ add exactly. If $g_1$ is essentially strictly convex, then so
is $g_1 + g_2$.

The sum rule for subdifferentials puts $\operatorname{dom} \partial(g_1 + g_2)$ inside
$\operatorname{dom} \partial g_1$. Exact addition is `ConvexAnalysis.IsExactSum` for the pairing
`innerₗ E`. -/
theorem IsExactSum.essentiallyStrictlyConvex_add {g₁ g₂ : E → EReal}
    (h : IsExactSum (innerₗ E) g₁ g₂) (hg₂ : ConvexFn g₂)
    (hesc : EssentiallyStrictlyConvex (B := innerₗ E) g₁) :
    EssentiallyStrictlyConvex (B := innerₗ E) (g₁ + g₂) := by
  intro C hC hCsub
  have hCdom : C ⊆ convexDom (g₁ + g₂) :=
      hCsub.trans (domSubdifferential_subset_convexDom h.properConvex_add)
  rw [convexDom_add h.properConvex_left.ne_bot h.properConvex_right.ne_bot] at hCdom
  refine StrictConvexOnFn.add_convexFn hC (hesc hC fun z hz => ?_) hg₂ h.properConvex_left
    h.properConvex_right (fun z hz => (hCdom hz).1) fun z hz => (hCdom hz).2
  obtain ⟨v, hv⟩ := hCsub hz
  rw [h.subdifferential_add z] at hv
  obtain ⟨v₁, hv₁, -, -, -⟩ := hv
  exact ⟨v₁, hv₁⟩

/-- Let $E$ be a finite-dimensional real inner product space, and let
$f_1, f_2 \colon E \to [-\infty, +\infty]$ be closed proper convex functions such that $f_1^*$
and $f_2^*$ add exactly. If $f_1$ is essentially smooth, then the infimal convolution
$f_1 \mathbin{\square} f_2$ is essentially smooth. This is Corollary 26.3.2 of
[rockafellar1970convex].

Under the exactness hypothesis, $f_1 \mathbin{\square} f_2$ is the conjugate of $f_1^* + f_2^*$,
and `ConvexAnalysis.IsExactSum.essentiallyStrictlyConvex_add` applies on the conjugate side. -/
theorem IsExactSum.essentiallySmooth_infConv
    (h : IsExactSum (innerₗ E) (convexConj (innerₗ E) f₁) (convexConj (innerₗ E) f₂))
    (h₁ : ClosedProperConvexFn f₁) (h₂ : ClosedProperConvexFn f₂)
    (hes : EssentiallySmooth f₁) : EssentiallySmooth (infConv f₁ f₂) := by
  have hsum : ClosedProperConvexFn (convexConj (innerₗ E) f₁ + convexConj (innerₗ E) f₂) :=
    ClosedProperConvexFn.add ⟨convexFn_convexConj _ f₁, closedConvex_convexConj,
        properConvex_convexConj h₁⟩
      ⟨convexFn_convexConj _ f₂, closedConvex_convexConj, properConvex_convexConj h₂⟩
          h.properConvex_add.convexDom_nonempty
  have hinf : convexConj (innerₗ E) (convexConj (innerₗ E) f₁ + convexConj (innerₗ E) f₂)
      = infConv f₁ f₂ := by
    rw [h.convexConj_add, convexConj_convexConj_innerL h₁.convex h₁.closed,
        convexConj_convexConj_innerL h₂.convex h₂.closed]
  rw [← hinf]
  refine (essentiallySmooth_convexConj_iff_essentiallyStrictlyConvex hsum.convex hsum.proper
    hsum.closed).2 (h.essentiallyStrictlyConvex_add (convexFn_convexConj _ f₂) ?_)
  exact (essentiallyStrictlyConvex_convexConj_iff_essentiallySmooth h₁.convex h₁.proper
      h₁.closed).2 hes

/-- Let $E$ be a finite-dimensional real inner product space, and let
$f_1, f_2 \colon E \to [-\infty, +\infty]$ be closed proper convex functions with $f_1$
essentially smooth. If some $y_0$ is in both $\operatorname{ri}(\operatorname{dom} f_1^*)$ and
$\operatorname{ri}(\operatorname{dom} f_2^*)$, then $f_1 \mathbin{\square} f_2$ is essentially
smooth. This common relative interior point gives the exactness of the sum $f_1^* + f_2^*$. -/
theorem essentiallySmooth_infConv_of_relint (h₁ : ClosedProperConvexFn f₁)
    (h₂ : ClosedProperConvexFn f₂) (hes : EssentiallySmooth f₁) {y₀ : E}
    (hy₁ : y₀ ∈ ri (convexDom (convexConj (innerₗ E) f₁)))
        (hy₂ : y₀ ∈ ri (convexDom (convexConj (innerₗ E) f₂))) :
    EssentiallySmooth (infConv f₁ f₂) :=
  IsExactSum.essentiallySmooth_infConv
    (IsExactSum.of_relint (convexFn_convexConj _ f₁) (properConvex_convexConj h₁)
        (convexFn_convexConj _ f₂)
      (properConvex_convexConj h₂) hy₁ hy₂) h₁ h₂ hes

end InfConv

/-! ### Linear images -/

section Image

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  {f : E → EReal} {A : E →ₗ[ℝ] G} {A' : G →ₗ[ℝ] E}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ G] in
/-- Let $A \colon E \to G$ be a linear map with the transpose $A' \colon G \to E$. If $A$ is onto,
then $A'$ is injective. -/
theorem injective_of_isAdjointPair_of_surjective (hA : IsAdjointPair (innerₗ G) (innerₗ E) A' A)
    (hsurj : Function.Surjective A) : Function.Injective A' := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro y hy
  obtain ⟨x, hx⟩ := hsurj y
  have h := hA y x
  rw [LinearMap.mem_ker.1 hy, map_zero, LinearMap.zero_apply, hx] at h
  have h2 : ‖y‖ ^ 2 = 0 := by simpa using h.symm
  exact norm_eq_zero.1 (by nlinarith [norm_nonneg y])

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ G] in
/-- Let $E$ and $G$ be real inner product spaces, let $A \colon E \to G$ be a linear map with the
transpose $A' \colon G \to E$, and let $g \colon E \to [-\infty, +\infty]$ pull back exactly
along $A'$. If $A'$ is injective and $g$ is essentially strictly convex, then $g A'$ is
essentially strictly convex.

The chain rule makes $\operatorname{dom} \partial(g A')$ the preimage of
$\operatorname{dom} \partial g$ under $A'$. Exact pullback is `ConvexAnalysis.IsExactImage`. -/
theorem IsExactImage.essentiallyStrictlyConvex_compLin {g : E → EReal}
    {hA : IsAdjointPair (innerₗ G) (innerₗ E) A' A}
    (h : IsExactImage (innerₗ G) (innerₗ E) A' A hA g) (hinj : Function.Injective A')
    (hesc : EssentiallyStrictlyConvex (B := innerₗ E) g) :
    EssentiallyStrictlyConvex (B := innerₗ G) (compLin g A') := by
  intro C hC hCsub
  refine StrictConvexOnFn.compLin (hesc (hC.linear_image A') fun z hz => ?_) hinj
  obtain ⟨y, hy, rfl⟩ := hz
  obtain ⟨v, hv⟩ := hCsub hy
  rw [h.subdifferential_compLin y] at hv
  obtain ⟨w, hw, -⟩ := hv
  exact ⟨w, hw⟩

/-- Let $E$ and $G$ be finite-dimensional real inner product spaces, let $A \colon E \to G$ be a
linear map with the transpose $A' \colon G \to E$, and let $f \colon E \to [-\infty, +\infty]$
be a closed proper convex function such that $f^*$ pulls back exactly along $A'$. If $f$ is
essentially smooth and $A'$ is injective, then the image
$$(Af)(y) = \inf \{ f(x) \mid Ax = y \}$$
is essentially smooth. This is Corollary 26.3.3 of [rockafellar1970convex].

Under the exactness hypothesis, $Af$ is the conjugate of $f^* A'$, and
`ConvexAnalysis.IsExactImage.essentiallyStrictlyConvex_compLin` applies on the conjugate side. -/
theorem IsExactImage.essentiallySmooth_mapLin {hA : IsAdjointPair (innerₗ G) (innerₗ E) A' A}
    (h : IsExactImage (innerₗ G) (innerₗ E) A' A hA (convexConj (innerₗ E) f))
    (hf : ClosedProperConvexFn f) (hes : EssentiallySmooth f) (hinj : Function.Injective A') :
    EssentiallySmooth (mapLin A f) := by
  have hk : ClosedProperConvexFn (compLin (convexConj (innerₗ E) f) A') :=
    ⟨convexFn_compLin A' (convexFn_convexConj _ f),
      closedConvex_compLin closedConvex_convexConj A'.continuous_of_finiteDimensional,
          h.properConvex_compLin⟩
  have himg : convexConj (innerₗ G) (compLin (convexConj (innerₗ E) f) A') = mapLin A f := by
    rw [h.convexConj_compLin, convexConj_convexConj_innerL hf.convex hf.closed]
  rw [← himg]
  refine (essentiallySmooth_convexConj_iff_essentiallyStrictlyConvex hk.convex hk.proper
      hk.closed).2
    (h.essentiallyStrictlyConvex_compLin hinj ?_)
  exact (essentiallyStrictlyConvex_convexConj_iff_essentiallySmooth hf.convex hf.proper
      hf.closed).2 hes

/-- Let $E$ and $G$ be finite-dimensional real inner product spaces, let $A \colon E \to G$ be a
linear map onto $G$ with the transpose $A' \colon G \to E$, and let
$f \colon E \to [-\infty, +\infty]$ be a closed proper convex function that is essentially
smooth. If $A' y_0 \in \operatorname{ri}(\operatorname{dom} f^*)$ for some $y_0 \in G$, then
$Af$ is essentially smooth.

The surjectivity of $A$ gives the injectivity of $A'$, and the relative interior point gives the
exactness. -/
theorem essentiallySmooth_mapLin_of_relint (hA : IsAdjointPair (innerₗ G) (innerₗ E) A' A)
    (hf : ClosedProperConvexFn f) (hes : EssentiallySmooth f) (hsurj : Function.Surjective A)
    {y₀ : G} (hy₀ : A' y₀ ∈ ri (convexDom (convexConj (innerₗ E) f))) :
    EssentiallySmooth (mapLin A f) :=
  IsExactImage.essentiallySmooth_mapLin
    (IsExactImage.of_relint_closed hA
        ⟨convexFn_convexConj _ f, closedConvex_convexConj, properConvex_convexConj hf⟩ hy₀) hf hes
    (injective_of_isAdjointPair_of_surjective hA hsurj)

end Image

end ConvexAnalysis
