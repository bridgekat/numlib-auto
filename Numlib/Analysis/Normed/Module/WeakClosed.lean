/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.LocallyConvex.WeakSpace` and
`Mathlib.Analysis.Normed.Module.WeakDual`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Convex.Quasiconvex
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Numlib.Analysis.Normed.Module.Annihilator

/-!
# Closed sets, semicontinuous functions and linear maps for the weak topologies

Let $E$ be a topological vector space over $\mathbb{K}$ with dual $E^*$. The weak topology
$\sigma(E, E^*)$ on $E$ is the coarsest topology for which every $f \in E^*$ is continuous, and the
weak-$*$ topology $\sigma(E^*, E)$ on $E^*$ is the coarsest topology for which every evaluation
$f \mapsto f(x)$, $x \in E$, is continuous. This file collects what §3.2–§3.4 and Problem 9 of
[brezis2011functional] say about these topologies beyond what Mathlib has. It proves Mazur's theorem
(a convex set is weakly closed if and only if it is closed) and its consequences for semicontinuous
functions, the weak closedness of closed balls and closed subspaces, the agreement of norm and weak
continuity for linear maps between Banach spaces, the agreement of the weak and norm topologies in
finite dimension and their difference in infinite dimension, the separation theorem in the weak-$*$
topology, and the weak-$*$ bipolar theorem for subspaces.

## Main results

* `WeakBilin.exists_finset_forall_norm_lt_subset_of_mem_nhds_zero` and `WeakBilin.hasBasis_nhds`:
  the basic neighbourhoods in a weak topology, cut out by finitely many functionals.
* `Convex.isClosed_image_toWeakSpace_iff`: **Mazur's theorem**, a convex set is weakly closed if and
  only if it is closed.
* `LowerSemicontinuous.comp_toWeakSpace_symm_of_convex_le` and
  `ConvexOn.lowerSemicontinuous_comp_toWeakSpace_symm`: a lower semicontinuous function with convex
  sublevel sets, in particular a convex lower semicontinuous function, is weakly lower
  semicontinuous.
* `lowerSemicontinuous_norm_comp_toWeakSpace_symm`: the norm is weakly lower semicontinuous.
* `isClosed_image_toWeakSpace_closedBall`: closed balls of a normed space are weakly closed, without
  any hypothesis on real scalars.
* `Submodule.isClosed_image_toWeakSpace_topologicalClosure`: closed subspaces are weakly closed.
* `LinearMap.continuous_iff_continuous_weakSpace`: a linear map between Banach spaces is continuous
  for the norm topologies if and only if it is continuous for the weak topologies.
* `toWeakSpaceContinuousLinearEquiv`, `tendsto_toWeakSpace_iff_of_finiteDimensional` and
  `toWeakDualContinuousLinearEquiv`: in finite dimension the weak topology is the norm topology, and
  the weak-$*$ topology of the dual is its norm topology.
* `closure_image_toWeakSpace_sphere` and `not_isOpen_image_toWeakSpace_ball`: in infinite dimension
  the weak closure of the unit sphere is the closed unit ball, and the open unit ball is not weakly
  open.
* `WeakDual.geometric_hahn_banach_closed_point`: a point outside a weak-$*$ closed convex subset of
  $E^*$ is strictly separated from it by an evaluation at a point of $E$. Its form for subspaces is
  `Submodule.exists_weakDual_eval_eq_zero_of_notMem`.
* `Submodule.strongDualAnnihilator_strongDualCoannihilator_eq_closure_toWeakDual`: **the weak-$*$
  bipolar theorem for subspaces**, $(N^\perp)^\perp$ is the weak-$*$ closure of a subspace
  $N \subseteq E^*$.

## Implementation notes

* The weak topology is the Mathlib type `WeakSpace 𝕜 E`, and the weak-$*$ topology of the dual is
  `WeakDual 𝕜 E`. A set `s` in `E` is weakly closed if `IsClosed (toWeakSpace 𝕜 E '' s)`, as in
  `Mathlib.Analysis.LocallyConvex.WeakSpace`. The definitional equality of `WeakSpace 𝕜 E` and `E`
  is never used for this.
* As in the Mathlib theorem `Convex.toWeakSpace_closure`, real convexity in a space over `RCLike 𝕜`
  is given by the hypotheses `[Module ℝ E] [IsScalarTower ℝ 𝕜 E]`, which hold automatically when
  $\mathbb{K} = \mathbb{R}$. The statements that do not need convexity (the closed ball, the sphere,
  the linear maps, the finite-dimensional facts and the weak-$*$ separation) do not have these
  hypotheses.
* `WeakSpace 𝕜 E` and `WeakDual 𝕜 E` are definitions, so instance search does not see through them.
  Finite dimension is supplied inside the proofs, and the instance
  `LocallyConvexSpace ℝ (WeakDual 𝕜 E)` is registered here through `inferInstanceAs`.
* The basic neighbourhoods of `WeakBilin` are in the pointwise form that the arguments here and in
  `Numlib.Analysis.Normed.Module.WeakStarMetrizable` use. The annihilators are those of
  `Numlib.Analysis.Normed.Module.Annihilator`.
-/

open Filter Topology Metric Set

/-! ### Basic neighbourhoods of $0$ in a weak topology -/

section Basic

variable {𝕜 E F : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F]
  [Module 𝕜 F]

/-- Let $B \colon E \times F \to \mathbb{K}$ be a bilinear form over a normed field $\mathbb{K}$,
and give $E$ the weak topology defined by $B$. Every neighbourhood $U$ of $0$ contains a set
$$\{x \in E : |B(x, y)| < \varepsilon \text{ for all } y \in s\}$$ for some finite set
$s \subseteq F$ and some $\varepsilon > 0$.

This is the pointwise form of the Mathlib seminorm basis `LinearMap.hasBasis_weakBilin`. -/
theorem WeakBilin.exists_finset_forall_norm_lt_subset_of_mem_nhds_zero
    {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} {U : Set (WeakBilin B)} (hU : U ∈ 𝓝 (0 : WeakBilin B)) :
    ∃ (s : Finset F) (ε : ℝ), 0 < ε ∧ {x : WeakBilin B | ∀ y ∈ s, ‖B x y‖ < ε} ⊆ U := by
  obtain ⟨V, hV, hVU⟩ := (LinearMap.hasBasis_weakBilin B).mem_iff.1 hU
  obtain ⟨s, ε, hε, rfl⟩ := (SeminormFamily.basisSets_iff _).1 hV
  refine ⟨s, ε, hε, fun x hx => hVU ?_⟩
  rw [id, Seminorm.ball_finset_sup_eq_iInter _ _ _ hε]
  exact Set.mem_iInter₂.2 fun y hy => (Seminorm.mem_ball_zero _).2 (hx y hy)

/-- Let $B \colon E \times F \to \mathbb{K}$ be a bilinear form over a normed field $\mathbb{K}$,
give $E$ the weak topology defined by $B$, and let $x_0 \in E$. The sets $$\{x \in E : |B(x,
y) - B(x_0, y)| < \varepsilon \text{ for all } y \in s\},$$ for finite sets $s \subseteq F$ and
$\varepsilon > 0$, form a basis of neighbourhoods of $x_0$. This is the common core of
Propositions 3.4 and 3.12 of [brezis2011functional].

The proof translates `WeakBilin.exists_finset_forall_norm_lt_subset_of_mem_nhds_zero` to an
arbitrary point. -/
theorem WeakBilin.hasBasis_nhds (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (x₀ : WeakBilin B) :
    (𝓝 x₀).HasBasis (fun p : Finset F × ℝ => 0 < p.2)
      (fun p => {x : WeakBilin B | ∀ y ∈ p.1, ‖B x y - B x₀ y‖ < p.2}) := by
  refine Filter.hasBasis_iff.2 fun t => ⟨fun ht => ?_, ?_⟩
  · have hU : (x₀ + ·) ⁻¹' t ∈ 𝓝 (0 : WeakBilin B) := by
      rw [← map_add_left_nhds_zero x₀] at ht
      exact ht
    obtain ⟨s, ε, hε, hsub⟩ := WeakBilin.exists_finset_forall_norm_lt_subset_of_mem_nhds_zero hU
    refine ⟨(s, ε), hε, fun x hx => ?_⟩
    have hmem : x - x₀ ∈ {x : WeakBilin B | ∀ y ∈ s, ‖B x y‖ < ε} := fun y hy => by
      have e : B (x - x₀) y = B x y - B x₀ y :=
        (congrArg (fun g : F →ₗ[𝕜] 𝕜 => g y) (map_sub B (x : E) x₀)).trans
          (LinearMap.sub_apply _ _ _)
      rw [e]
      exact hx y hy
    have := hsub hmem
    simpa using this
  · rintro ⟨⟨s, ε⟩, hε, hsub⟩
    dsimp only at hε hsub
    refine Filter.mem_of_superset ?_ hsub
    have hopen : IsOpen {x : WeakBilin B | ∀ y ∈ s, ‖B x y - B x₀ y‖ < ε} := by
      have : {x : WeakBilin B | ∀ y ∈ s, ‖B x y - B x₀ y‖ < ε} =
          ⋂ y ∈ s, {x : WeakBilin B | ‖B x y - B x₀ y‖ < ε} := by
        ext x
        simp only [mem_ofPred_eq, mem_iInter]
      rw [this]
      exact isOpen_biInter_finset fun y _ =>
        isOpen_lt (((WeakBilin.eval_continuous B y).sub continuous_const).norm) continuous_const
    refine hopen.mem_nhds fun y _ => ?_
    rw [sub_self, norm_zero]
    exact hε

end Basic

/-! ### Weakly closed sets and Mazur's theorem -/

section Closed

variable {𝕜 E : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

/-- Let $E$ be a topological vector space over $\mathbb{K}$, and let $s \subseteq E$. If $s$ is
weakly closed, then $s$ is closed.

The set $s$ is the preimage of its weak image under the continuous identity map
`toWeakSpaceCLM 𝕜 E`. This is the counterpart for closed sets of the Mathlib theorem
`WeakSpace.isOpen_of_isOpen`. -/
theorem WeakSpace.isClosed_of_isClosed {s : Set E} (hs : IsClosed (toWeakSpace 𝕜 E '' s)) :
    IsClosed s := by
  have : s = toWeakSpaceCLM 𝕜 E ⁻¹' (toWeakSpace 𝕜 E '' s) := by
    ext x
    simp only [mem_preimage, toWeakSpaceCLM_eq_toWeakSpace]
    exact ((toWeakSpace 𝕜 E).injective.mem_set_image).symm
  rw [this]
  exact hs.preimage (toWeakSpaceCLM 𝕜 E).continuous

end Closed

section Mazur

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E]

/-- **Mazur's theorem.** Let $E$ be a locally convex topological vector space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $s \subseteq E$ be convex over $\mathbb{R}$.
Then $s$ is weakly closed if and only if $s$ is closed.

The nontrivial direction is the Mathlib theorem `Convex.toWeakSpace_closure`: a point outside a
closed convex set is separated from it by a continuous linear functional, which is weakly
continuous. -/
theorem Convex.isClosed_image_toWeakSpace_iff {s : Set E} (hs : Convex ℝ s) :
    IsClosed (toWeakSpace 𝕜 E '' s) ↔ IsClosed s := by
  refine ⟨WeakSpace.isClosed_of_isClosed, fun h => ?_⟩
  rw [← closure_eq_iff_isClosed, ← hs.toWeakSpace_closure 𝕜, h.closure_eq]

/-- Let $E$ be a locally convex topological vector space over $\mathbb{K} = \mathbb{R}$ or
$\mathbb{C}$, let $\beta$ be a linear order, and let $f \colon E \to \beta$ be lower
semicontinuous with convex sublevel sets $\{x : f(x) \le b\}$ for all $b \in \beta$. Then $f$ is
lower semicontinuous for the weak topology of $E$.

Each sublevel set is closed and convex, hence weakly closed by Mazur's theorem. Convex functions
(`ConvexOn.lowerSemicontinuous_comp_toWeakSpace_symm`) are the main case, but only the convexity
of the sublevel sets is used. -/
theorem LowerSemicontinuous.comp_toWeakSpace_symm_of_convex_le {β : Type*} [LinearOrder β]
    {f : E → β} (hf : LowerSemicontinuous f) (hconv : ∀ b, Convex ℝ {x | f x ≤ b}) :
    LowerSemicontinuous (f ∘ (toWeakSpace 𝕜 E).symm) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage] at hf ⊢
  intro b
  have : (f ∘ (toWeakSpace 𝕜 E).symm) ⁻¹' Iic b = toWeakSpace 𝕜 E '' (f ⁻¹' Iic b) := by
    ext y
    simp only [mem_preimage, Function.comp_apply, mem_Iic, mem_image]
    constructor
    · intro h; exact ⟨(toWeakSpace 𝕜 E).symm y, h, by simp⟩
    · rintro ⟨z, hz, rfl⟩; simpa using hz
  rw [this]
  exact (hconv b).isClosed_image_toWeakSpace_iff.2 (hf b)

/-- Let $E$ be a locally convex topological vector space over $\mathbb{K} = \mathbb{R}$ or
$\mathbb{C}$, and let $f \colon E \to \mathbb{R}$ be convex and lower semicontinuous. Then $f$
is lower semicontinuous for the weak topology of $E$. -/
theorem ConvexOn.lowerSemicontinuous_comp_toWeakSpace_symm {f : E → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hlsc : LowerSemicontinuous f) :
    LowerSemicontinuous (f ∘ (toWeakSpace 𝕜 E).symm) :=
  hlsc.comp_toWeakSpace_symm_of_convex_le fun b => by simpa using hf.convex_le b

end Mazur

/-! ### Semicontinuity and quasiconvexity on a closed set, in the weak topology -/

section Sublevel

variable {α γ : Type*} [TopologicalSpace α] [LinearOrder γ] {s : Set α} {f : α → γ}

/-- Let $\alpha$ be a topological space, let $s \subseteq \alpha$ be closed, let $\gamma$ be a
linear order, and let $f \colon \alpha \to \gamma$ be lower semicontinuous on $s$. Then for
every $b \in \gamma$ the set $\{x \in s : f(x) \le b\}$ is closed. -/
theorem LowerSemicontinuousOn.isClosed_sep_le (hs : IsClosed s) (hf : LowerSemicontinuousOn f s)
    (b : γ) : IsClosed {x ∈ s | f x ≤ b} := by
  obtain ⟨v, hv, hsv⟩ := lowerSemicontinuousOn_iff_preimage_Iic.1 hf b
  have : {x ∈ s | f x ≤ b} = s ∩ v := by
    rw [← hsv]
    ext x
    simp
  rw [this]
  exact hs.inter hv

/-- Let $\alpha$ be a topological space, let $s \subseteq \alpha$ be closed, let $\gamma$ be a
linear order, and let $f \colon \alpha \to \gamma$ be upper semicontinuous on $s$. Then for
every $b \in \gamma$ the set $\{x \in s : b \le f(x)\}$ is closed. -/
theorem UpperSemicontinuousOn.isClosed_sep_ge (hs : IsClosed s) (hf : UpperSemicontinuousOn f s)
    (b : γ) : IsClosed {x ∈ s | b ≤ f x} :=
  LowerSemicontinuousOn.isClosed_sep_le (γ := γᵒᵈ) hs hf b

end Sublevel

section WeakTransfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : Set E}

/-- Let $E$ be a real normed space, let $A \subseteq E$, and let $p$ be a predicate on $E$. The
image in `WeakSpace ℝ E` of $\{v \in A : p(v)\}$ is the set of points of the image of $A$ that
satisfy $p$. -/
theorem image_toWeakSpace_sep {p : E → Prop} :
    toWeakSpace ℝ E '' {v ∈ A | p v} =
      {x ∈ toWeakSpace ℝ E '' A | p ((toWeakSpace ℝ E).symm x)} := by
  ext x
  constructor
  · rintro ⟨v, ⟨hvA, hvp⟩, rfl⟩
    exact ⟨⟨v, hvA, rfl⟩, by simpa using hvp⟩
  · rintro ⟨⟨v, hvA, rfl⟩, hp⟩
    exact ⟨v, ⟨hvA, by simpa using hp⟩, rfl⟩

/-- Let $E$ be a real normed space. If $A \subseteq E$ is convex, then its image in `WeakSpace ℝ E`
is convex. -/
theorem Convex.image_toWeakSpace (hA : Convex ℝ A) : Convex ℝ (toWeakSpace ℝ E '' A) :=
  hA.linear_image (toWeakSpace ℝ E : E →ₗ[ℝ] WeakSpace ℝ E)

/-- Let $E$ be a real normed space, let $A \subseteq E$, and let $f \colon E \to \gamma$ be
quasiconvex on $A$. Then $f$, as a function on `WeakSpace ℝ E`, is quasiconvex on the image of
$A$. -/
theorem QuasiconvexOn.comp_toWeakSpace_symm {γ : Type*} [LE γ] {f : E → γ}
    (hf : QuasiconvexOn ℝ A f) :
    QuasiconvexOn ℝ (toWeakSpace ℝ E '' A) (f ∘ (toWeakSpace ℝ E).symm) := by
  intro b
  convert (hf b).image_toWeakSpace using 1
  exact (image_toWeakSpace_sep (p := fun v => f v ≤ b)).symm

/-- Let $E$ be a real normed space, let $A \subseteq E$, and let $f \colon E \to \gamma$ be
quasiconcave on $A$. Then $f$, as a function on `WeakSpace ℝ E`, is quasiconcave on the image of
$A$. -/
theorem QuasiconcaveOn.comp_toWeakSpace_symm {γ : Type*} [LE γ] {f : E → γ}
    (hf : QuasiconcaveOn ℝ A f) :
    QuasiconcaveOn ℝ (toWeakSpace ℝ E '' A) (f ∘ (toWeakSpace ℝ E).symm) := by
  intro b
  convert (hf b).image_toWeakSpace using 1
  exact (image_toWeakSpace_sep (p := fun v => b ≤ f v)).symm

/-- Let $E$ be a real normed space, let $A \subseteq E$ be closed, let $\gamma$ be a linear order,
and let $f \colon E \to \gamma$ be quasiconvex and lower semicontinuous on $A$. Then $f$ is
lower semicontinuous on $A$ for the weak topology of $E$.

The sublevel sets of $f$ on $A$ are closed and convex, hence weakly closed by Mazur's theorem.
This is the relative version of `LowerSemicontinuous.comp_toWeakSpace_symm_of_convex_le`. The
closedness of $A$ makes the sublevel sets closed in $E$. -/
theorem LowerSemicontinuousOn.comp_toWeakSpace_symm_of_quasiconvexOn {γ : Type*} [LinearOrder γ]
    {f : E → γ} (hA : IsClosed A) (hf : QuasiconvexOn ℝ A f) (hlsc : LowerSemicontinuousOn f A) :
    LowerSemicontinuousOn (f ∘ (toWeakSpace ℝ E).symm) (toWeakSpace ℝ E '' A) := by
  rw [← lowerSemicontinuous_restrict_iff, lowerSemicontinuous_iff_isClosed_preimage]
  intro b
  have hcl : IsClosed (toWeakSpace ℝ E '' {v ∈ A | f v ≤ b}) :=
    (hf b).isClosed_image_toWeakSpace_iff.2 (hlsc.isClosed_sep_le hA b)
  convert hcl.preimage continuous_subtype_val using 1
  ext ⟨_, v, hv, rfl⟩
  simp [(toWeakSpace ℝ E).injective.mem_set_image, hv]

/-- Let $E$ be a real normed space, let $A \subseteq E$ be closed, let $\gamma$ be a linear order,
and let $f \colon E \to \gamma$ be quasiconcave and upper semicontinuous on $A$. Then $f$ is
upper semicontinuous on $A$ for the weak topology of $E$. -/
theorem UpperSemicontinuousOn.comp_toWeakSpace_symm_of_quasiconcaveOn {γ : Type*} [LinearOrder γ]
    {f : E → γ} (hA : IsClosed A) (hf : QuasiconcaveOn ℝ A f) (husc : UpperSemicontinuousOn f A) :
    UpperSemicontinuousOn (f ∘ (toWeakSpace ℝ E).symm) (toWeakSpace ℝ E '' A) :=
  LowerSemicontinuousOn.comp_toWeakSpace_symm_of_quasiconvexOn (γ := γᵒᵈ) hA hf husc

end WeakTransfer

section NormLsc

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
  [IsScalarTower ℝ 𝕜 E]

/-- Let $E$ be a normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$ with a compatible real
structure. Then the norm $x \mapsto \|x\|$ is lower semicontinuous for the weak topology of $E$.

The norm is convex and continuous. This is the topological form of
`norm_le_liminf_norm_of_weak_tendsto`. -/
theorem lowerSemicontinuous_norm_comp_toWeakSpace_symm :
    LowerSemicontinuous (fun x : WeakSpace 𝕜 E => ‖(toWeakSpace 𝕜 E).symm x‖) :=
  (convexOn_norm convex_univ).lowerSemicontinuous_comp_toWeakSpace_symm (𝕜 := 𝕜)
    continuous_norm.lowerSemicontinuous

end NormLsc

section ClosedSubspace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Let $E$ be a normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $N$ be a
subspace of $E$. Then the closure $\bar N$ is weakly closed.

This is Mazur's theorem for the closure of a subspace over $\mathbb{K}$. Its real convexity is
obtained by restriction of scalars, so no hypothesis `[NormedSpace ℝ E]` appears. -/
theorem Submodule.isClosed_image_toWeakSpace_topologicalClosure (N : Submodule 𝕜 E) :
    IsClosed (toWeakSpace 𝕜 E '' (N.topologicalClosure : Set E)) := by
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have : IsScalarTower ℝ 𝕜 E := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact (N.topologicalClosure.restrictScalars ℝ).convex.isClosed_image_toWeakSpace_iff.2
    (Submodule.isClosed_topologicalClosure N)

end ClosedSubspace

section ClosedBall

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Let $E$ be a normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $x \in E$, and let
$r \in \mathbb{R}$. Then the closed ball $\bar B(x, r)$ is weakly closed.

The weak image of $\bar B(x, r)$ is the preimage, under the continuous embedding
`NormedSpace.inclusionInDoubleDualWeak` of $E$ with the weak topology into $E^{**}$ with the
weak-$*$ topology, of the closed ball of $E^{**}$ around $Jx$, which is weak-$*$ closed
(`WeakDual.isClosed_closedBall`). The two balls correspond because $J$ is an isometry. Unlike
the proof through Mazur's theorem, this proof needs no hypothesis on real scalars. -/
theorem isClosed_image_toWeakSpace_closedBall (x : E) (r : ℝ) :
    IsClosed (toWeakSpace 𝕜 E '' closedBall x r) := by
  have : toWeakSpace 𝕜 E '' closedBall x r = NormedSpace.inclusionInDoubleDualWeak 𝕜 E ⁻¹'
      (WeakDual.toStrongDual ⁻¹' closedBall (NormedSpace.inclusionInDoubleDual 𝕜 E x) r) := by
    ext y
    simp only [Set.mem_image, mem_closedBall, Set.mem_preimage, dist_eq_norm]
    have key : ∀ z : E, ‖WeakDual.toStrongDual (NormedSpace.inclusionInDoubleDualWeak 𝕜 E
        (toWeakSpace 𝕜 E z)) - NormedSpace.inclusionInDoubleDual 𝕜 E x‖ = ‖z - x‖ := fun z => by
      rw [← (NormedSpace.inclusionInDoubleDualLi 𝕜).norm_map (z - x), map_sub]
      rfl
    constructor
    · rintro ⟨z, hz, rfl⟩
      rwa [key]
    · intro hy
      refine ⟨(toWeakSpace 𝕜 E).symm y, ?_, by simp⟩
      have := key ((toWeakSpace 𝕜 E).symm y)
      rw [LinearEquiv.apply_symm_apply] at this
      rwa [← this]
  rw [this]
  exact (WeakDual.isClosed_closedBall _ _).preimage
    (NormedSpace.inclusionInDoubleDualWeak 𝕜 E).continuous

end ClosedBall

/-! ### Linear maps: strong and weak continuity agree -/

section LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Let $E$ and $F$ be Banach spaces over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let
$T \colon E \to F$ be linear. If $T$ is continuous from the norm topology of $E$ to the weak
topology of $F$, then $T$ is continuous.

The graph of $T$ is the preimage of the diagonal of $F \times F$, with the weak topology on both
factors, under a continuous map. The diagonal is closed because the weak topology is Hausdorff,
so the graph is closed, and the closed graph theorem concludes. Completeness of both spaces is
used. -/
theorem LinearMap.continuous_of_continuous_toWeakSpace_comp [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ[𝕜] F) (hT : Continuous (fun x => toWeakSpace 𝕜 F (T x))) : Continuous T := by
  refine T.continuous_of_isClosed_graph ?_
  have : (T.graph : Set (E × F)) =
      (fun p : E × F => (toWeakSpace 𝕜 F (T p.1), toWeakSpace 𝕜 F p.2)) ⁻¹'
        Set.diagonal (WeakSpace 𝕜 F) := by
    ext p
    simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, Set.mem_preimage, Set.mem_diagonal_iff]
    exact ⟨fun h => by rw [h], fun h => (toWeakSpace 𝕜 F).injective h |>.symm⟩
  rw [this]
  exact isClosed_diagonal.preimage ((hT.comp continuous_fst).prodMk
    ((toWeakSpaceCLM 𝕜 F).continuous.comp continuous_snd))

/-- Let $E$ and $F$ be Banach spaces over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let
$T \colon E \to F$ be linear. If $T$ is continuous from the weak topology of $E$ to the weak
topology of $F$, then $T$ is continuous.

The map $T$ is then continuous from the norm topology of $E$ to the weak topology of $F$, and
`LinearMap.continuous_of_continuous_toWeakSpace_comp` applies. -/
theorem LinearMap.continuous_of_continuous_weakSpace_map [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ[𝕜] F)
    (hT : Continuous (fun x : WeakSpace 𝕜 E => toWeakSpace 𝕜 F (T ((toWeakSpace 𝕜 E).symm x)))) :
    Continuous T :=
  T.continuous_of_continuous_toWeakSpace_comp (by
    have := hT.comp (toWeakSpaceCLM 𝕜 E).continuous
    simpa [Function.comp_def] using this)

/-- Let $E$ and $F$ be Banach spaces over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let
$T \colon E \to F$ be linear. Then $T$ is continuous if and only if it is continuous from the
weak topology of $E$ to the weak topology of $F$.

The forward direction is the Mathlib construction `WeakSpace.map` and needs no completeness.
With `LinearMap.continuous_of_continuous_toWeakSpace_comp`, the three continuity properties of a
linear map between Banach spaces (norm to norm, weak to weak, and norm to weak) coincide. -/
theorem LinearMap.continuous_iff_continuous_weakSpace [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ[𝕜] F) :
    Continuous T ↔
      Continuous (fun x : WeakSpace 𝕜 E => toWeakSpace 𝕜 F (T ((toWeakSpace 𝕜 E).symm x))) :=
  ⟨fun h => (WeakSpace.map (⟨T, h⟩ : E →L[𝕜] F)).continuous,
    T.continuous_of_continuous_weakSpace_map⟩

end LinearMap

/-! ### Finite dimension: the weak topologies are the norm topologies -/

section FiniteDimensional

variable (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Let $E$ be a finite-dimensional normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$.
Then the identity map from $E$ with the weak topology to $E$ with the norm topology is
continuous, so the two topologies coincide.

Every linear map from a finite-dimensional Hausdorff topological vector space is continuous. -/
theorem WeakSpace.continuous_toWeakSpace_symm_of_finiteDimensional [FiniteDimensional 𝕜 E] :
    Continuous (toWeakSpace 𝕜 E).symm := by
  have : FiniteDimensional 𝕜 (WeakSpace 𝕜 E) := ‹FiniteDimensional 𝕜 E›
  exact LinearMap.continuous_of_finiteDimensional
    ((toWeakSpace 𝕜 E).symm : WeakSpace 𝕜 E →ₗ[𝕜] E)

/-- Let $E$ be a finite-dimensional normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. The
identity map from $E$ to `WeakSpace 𝕜 E`, as a continuous linear equivalence: the weak topology
and the norm topology coincide. -/
def toWeakSpaceContinuousLinearEquiv [FiniteDimensional 𝕜 E] : E ≃L[𝕜] WeakSpace 𝕜 E where
  toLinearEquiv := toWeakSpace 𝕜 E
  continuous_toFun := (toWeakSpaceCLM 𝕜 E).continuous
  continuous_invFun := WeakSpace.continuous_toWeakSpace_symm_of_finiteDimensional 𝕜 E

/-- The continuous linear equivalence `toWeakSpaceContinuousLinearEquiv` is the identity map
`toWeakSpace`. -/
@[simp]
theorem toWeakSpaceContinuousLinearEquiv_apply [FiniteDimensional 𝕜 E] (x : E) :
    toWeakSpaceContinuousLinearEquiv 𝕜 E x = toWeakSpace 𝕜 E x :=
  rfl

variable {𝕜 E}

/-- Let $E$ be a finite-dimensional normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. A
net in $E$ converges weakly to $u$ if and only if it converges to $u$ in norm. -/
theorem tendsto_toWeakSpace_iff_of_finiteDimensional [FiniteDimensional 𝕜 E] {ι : Type*}
    {l : Filter ι} {x : ι → E} {u : E} :
    Tendsto (fun i => toWeakSpace 𝕜 E (x i)) l (𝓝 (toWeakSpace 𝕜 E u)) ↔ Tendsto x l (𝓝 u) :=
  (toWeakSpaceContinuousLinearEquiv 𝕜 E).toHomeomorph.isInducing.tendsto_nhds_iff.symm

variable (𝕜 E)

/-- Let $E$ be a finite-dimensional normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$.
Then the identity map from $E^*$ with the weak-$*$ topology to $E^*$ with the norm topology is
continuous, so the two topologies coincide.

The dual is finite-dimensional, and `WeakDual 𝕜 E` is a Hausdorff topological vector space. The
weak-$*$ topology is always coarser than the weak topology, which is coarser than the norm
topology (`WeakDual.continuous_weakSpace_toWeakDual`, `NormedSpace.Dual.toWeakDual_continuous`),
so the three topologies of the dual coincide. -/
theorem WeakDual.continuous_toStrongDual_of_finiteDimensional [FiniteDimensional 𝕜 E] :
    Continuous (WeakDual.toStrongDual : WeakDual 𝕜 E → StrongDual 𝕜 E) := by
  have : FiniteDimensional 𝕜 (StrongDual 𝕜 E) := inferInstance
  have : FiniteDimensional 𝕜 (WeakDual 𝕜 E) := ‹FiniteDimensional 𝕜 (StrongDual 𝕜 E)›
  exact LinearMap.continuous_of_finiteDimensional
    (WeakDual.toStrongDual (𝕜 := 𝕜) (E := E)).toLinearMap

/-- Let $E$ be a finite-dimensional normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. The
identity map from $E^*$ to `WeakDual 𝕜 E`, as a continuous linear equivalence: the weak-$*$
topology and the norm topology of $E^*$ coincide. -/
def toWeakDualContinuousLinearEquiv [FiniteDimensional 𝕜 E] :
    StrongDual 𝕜 E ≃L[𝕜] WeakDual 𝕜 E where
  toLinearEquiv := StrongDual.toWeakDual
  continuous_toFun := NormedSpace.Dual.toWeakDual_continuous
  continuous_invFun := WeakDual.continuous_toStrongDual_of_finiteDimensional 𝕜 E

/-- The continuous linear equivalence `toWeakDualContinuousLinearEquiv` is the identity map
`StrongDual.toWeakDual`. -/
@[simp]
theorem toWeakDualContinuousLinearEquiv_apply [FiniteDimensional 𝕜 E] (f : StrongDual 𝕜 E) :
    toWeakDualContinuousLinearEquiv 𝕜 E f = StrongDual.toWeakDual f :=
  rfl

end FiniteDimensional

/-! ### Infinite dimension: the weak topology is strictly coarser -/

section Algebraic

variable {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- Let $E$ be an infinite-dimensional vector space over a field $\mathbb{K}$, and let
$(f_i)_{i \in \iota}$ be a finite family of linear functionals on $E$. Then there is $y \neq 0$
in $E$ with $f_i(y) = 0$ for all $i$.

Otherwise $x \mapsto (f_i(x))_i$ would embed $E$ into the finite-dimensional space
$\mathbb{K}^\iota$. -/
theorem exists_ne_zero_forall_apply_eq_zero_of_not_finiteDimensional
    (h : ¬ FiniteDimensional 𝕜 E) {ι : Type*} [Finite ι] (f : ι → E →ₗ[𝕜] 𝕜) :
    ∃ y : E, y ≠ 0 ∧ ∀ i, f i y = 0 := by
  by_contra hcon
  push Not at hcon
  refine h (Module.Finite.of_injective (LinearMap.pi f) ?_)
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_pi, Submodule.eq_bot_iff]
  intro y hy
  rw [Submodule.mem_iInf] at hy
  by_contra hy0
  obtain ⟨i, hi⟩ := hcon y hy0
  exact hi (LinearMap.mem_ker.1 (hy i))

end Algebraic

section InfiniteDimensional

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Let $E$ be an infinite-dimensional normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$.
Then the weak closure of the unit sphere $\{x : \|x\| = 1\}$ is the closed unit ball
$\{x : \|x\| \le 1\}$. In particular, the sphere is not weakly closed.

The ball is weakly closed and contains the sphere. Conversely, a basic weak neighbourhood of a
point $x_0$ of the open ball is cut out by finitely many functionals, which have a common zero
$y_0 \neq 0$. The line $t \mapsto x_0 + t y_0$ stays in the neighbourhood and meets the sphere
by the intermediate value theorem. -/
theorem closure_image_toWeakSpace_sphere (h : ¬ FiniteDimensional 𝕜 E) :
    closure (toWeakSpace 𝕜 E '' sphere (0 : E) 1) = toWeakSpace 𝕜 E '' closedBall 0 1 := by
  refine le_antisymm (closure_minimal (image_mono sphere_subset_closedBall)
    (isClosed_image_toWeakSpace_closedBall 0 1)) ?_
  rintro y ⟨x₀, hx₀, rfl⟩
  rw [mem_closedBall_zero_iff] at hx₀
  rcases hx₀.lt_or_eq with hlt | heq
  swap
  · exact subset_closure ⟨x₀, mem_sphere_zero_iff_norm.2 heq, rfl⟩
  rw [mem_closure_iff_nhds]
  intro t ht
  -- translate the neighbourhood to `0` and pick a basic set inside it
  have hU : (toWeakSpace 𝕜 E x₀ + ·) ⁻¹' t ∈ 𝓝 (0 : WeakSpace 𝕜 E) := by
    rw [← map_add_left_nhds_zero (toWeakSpace 𝕜 E x₀)] at ht
    exact ht
  obtain ⟨s, r, hr, hVU⟩ := WeakBilin.exists_finset_forall_norm_lt_subset_of_mem_nhds_zero hU
  -- a nonzero vector killed by the finitely many functionals of `s`
  obtain ⟨y₀, hy₀, hfy₀⟩ := exists_ne_zero_forall_apply_eq_zero_of_not_finiteDimensional h
    (fun f : s => ((f : StrongDual 𝕜 E) : E →ₗ[𝕜] 𝕜))
  -- the ray `x₀ + t y₀` leaves the ball, so it meets the sphere
  have hy₀' : 0 < ‖y₀‖ := norm_pos_iff.2 hy₀
  set g : ℝ → ℝ := fun t => ‖x₀ + (t : 𝕜) • y₀‖ with hg
  have hgc : Continuous g := by fun_prop
  set T : ℝ := (1 + ‖x₀‖) / ‖y₀‖ with hT
  have hT0 : 0 ≤ T := by positivity
  have hgT : 1 ≤ g T := by
    have : ‖(T : 𝕜) • y₀‖ ≤ ‖x₀ + (T : 𝕜) • y₀‖ + ‖x₀‖ := by
      calc ‖(T : 𝕜) • y₀‖ = ‖(x₀ + (T : 𝕜) • y₀) - x₀‖ := by rw [add_sub_cancel_left]
        _ ≤ _ := norm_sub_le _ _
    have h2 : ‖(T : 𝕜) • y₀‖ = 1 + ‖x₀‖ := by
      rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg hT0, hT, div_mul_cancel₀ _ hy₀'.ne']
    simp only [hg]
    linarith
  have hg0 : g 0 < 1 := by simpa [hg] using hlt
  obtain ⟨t₀, -, ht₀⟩ := intermediate_value_Icc hT0 hgc.continuousOn ⟨hg0.le, hgT⟩
  refine ⟨toWeakSpace 𝕜 E (x₀ + (t₀ : 𝕜) • y₀), ?_, x₀ + (t₀ : 𝕜) • y₀,
    mem_sphere_zero_iff_norm.2 ht₀, rfl⟩
  -- the point lies in the basic neighbourhood since the functionals of `s` kill `y₀`
  have hmem : toWeakSpace 𝕜 E ((t₀ : 𝕜) • y₀) ∈
      {x : WeakSpace 𝕜 E | ∀ f ∈ s, ‖(topDualPairing 𝕜 E).flip x f‖ < r} := by
    intro f hf
    change ‖f ((t₀ : 𝕜) • y₀)‖ < r
    have := hfy₀ ⟨f, hf⟩
    simp only [ContinuousLinearMap.coe_coe] at this
    rw [map_smul, this, smul_zero, norm_zero]
    exact hr
  have : toWeakSpace 𝕜 E x₀ + toWeakSpace 𝕜 E ((t₀ : 𝕜) • y₀) ∈ t := hVU hmem
  rwa [← map_add] at this

/-- Let $E$ be an infinite-dimensional normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$.
Then the open unit ball $\{x : \|x\| < 1\}$ is not weakly open.

Otherwise the sphere, which is the closed ball minus the open ball, would be weakly closed. But
its weak closure is the closed ball (`closure_image_toWeakSpace_sphere`), which contains $0$. -/
theorem not_isOpen_image_toWeakSpace_ball (h : ¬ FiniteDimensional 𝕜 E) :
    ¬ IsOpen (toWeakSpace 𝕜 E '' ball (0 : E) 1) := by
  intro hopen
  have hsph : IsClosed (toWeakSpace 𝕜 E '' sphere (0 : E) 1) := by
    rw [← closedBall_sdiff_ball, Set.image_sdiff (toWeakSpace 𝕜 E).injective]
    exact (isClosed_image_toWeakSpace_closedBall 0 1).sdiff hopen
  have h0 : toWeakSpace 𝕜 E 0 ∈ toWeakSpace 𝕜 E '' sphere (0 : E) 1 := by
    rw [← hsph.closure_eq, closure_image_toWeakSpace_sphere h]
    exact ⟨0, by simp, rfl⟩
  obtain ⟨z, hz, hz0⟩ := h0
  rw [(toWeakSpace 𝕜 E).injective.eq_iff] at hz0
  rw [hz0, mem_sphere_zero_iff_norm, norm_zero] at hz
  exact zero_ne_one hz

end InfiniteDimensional

/-! ### Separation in the weak-$*$ topology, and the weak-$*$ bipolar theorem for subspaces -/

section WeakStar

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The dual $E^*$ of a normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, with the
weak-$*$ topology, is a locally convex space over $\mathbb{R}$.

It is `WeakBilin (topDualPairing 𝕜 E)`, but instance search does not find the instance
`WeakBilin.locallyConvexSpace` through the definition `WeakDual`. -/
instance WeakDual.instLocallyConvexSpaceReal : LocallyConvexSpace ℝ (WeakDual 𝕜 E) :=
  inferInstanceAs (LocallyConvexSpace ℝ (WeakBilin (topDualPairing 𝕜 E)))

/-- Let $E$ be a normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $s \subseteq E^*$
be convex over $\mathbb{R}$ and closed in the weak-$*$ topology, and let
$f \in E^* \setminus s$. Then there are $x \in E$ and $u \in \mathbb{R}$ with
$$\operatorname{Re} g(x) < u < \operatorname{Re} f(x) \quad \text{for all } g \in s.$$ So $f$ is
strictly separated from $s$ by the evaluation at a point of $E$.

This is the geometric Hahn–Banach theorem `RCLike.geometric_hahn_banach_closed_point` in the
locally convex space `WeakDual 𝕜 E`. The continuous linear functionals on this space are exactly
the evaluations at points of $E$, by `LinearMap.dualEmbedding_surjective`. -/
theorem WeakDual.geometric_hahn_banach_closed_point {s : Set (WeakDual 𝕜 E)} (hs₁ : Convex ℝ s)
    (hs₂ : IsClosed s) {f : WeakDual 𝕜 E} (hf : f ∉ s) :
    ∃ (x : E) (u : ℝ), (∀ g ∈ s, RCLike.re (g x) < u) ∧ u < RCLike.re (f x) := by
  obtain ⟨φ, u, hφs, hφf⟩ :=
    RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜) (E := WeakDual 𝕜 E) hs₁ hs₂ hf
  obtain ⟨x, hx⟩ := LinearMap.dualEmbedding_surjective (topDualPairing 𝕜 E) φ
  refine ⟨x, u, fun g hg => ?_, ?_⟩
  · have := hφs g hg
    rwa [← hx] at this
  · rwa [← hx] at hφf

/-- Let $W$ be a vector space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $K$ be a subspace
of $W$, and let $\varphi$ be a linear functional on $W$. If $\operatorname{Re} \varphi(g) < u$
for all $g \in K$, then $\varphi(g) = 0$ for all $g \in K$.

Scaling by real numbers shows that the real part vanishes on $K$, and scaling by $i$ then shows
that the imaginary part vanishes. -/
theorem Submodule.forall_apply_eq_zero_of_forall_re_lt {W : Type*} [AddCommGroup W] [Module 𝕜 W]
    {K : Submodule 𝕜 W} {φ : W →ₗ[𝕜] 𝕜} {u : ℝ} (h : ∀ g ∈ K, RCLike.re (φ g) < u) :
    ∀ g ∈ K, φ g = 0 := by
  have hre : ∀ g ∈ K, RCLike.re (φ g) = 0 := by
    intro g hg
    by_contra hne
    set c : ℝ := (u + 1) / RCLike.re (φ g) with hc
    have := h ((c : 𝕜) • g) (K.smul_mem _ hg)
    rw [map_smul, smul_eq_mul, RCLike.re_ofReal_mul, hc, div_mul_cancel₀ _ hne] at this
    linarith
  intro g hg
  apply RCLike.ext
  · rw [hre g hg, map_zero]
  · have := hre ((RCLike.I : 𝕜) • g) (K.smul_mem _ hg)
    rw [map_smul, smul_eq_mul, RCLike.I_mul_re] at this
    rw [map_zero]
    linarith

/-- Let $E$ be a normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $K$ be a subspace
of $E^*$ that is closed in the weak-$*$ topology, and let $f \in E^* \setminus K$. Then there is
$x \in E$ with $g(x) = 0$ for all $g \in K$ and $f(x) \neq 0$.

By `WeakDual.geometric_hahn_banach_closed_point`, the evaluation at some $x$ has real part
bounded above on the subspace $K$, so it vanishes on $K$ by
`Submodule.forall_apply_eq_zero_of_forall_re_lt`, and $\operatorname{Re} f(x) > u > 0$. -/
theorem Submodule.exists_weakDual_eval_eq_zero_of_notMem (K : Submodule 𝕜 (WeakDual 𝕜 E))
    (hK : IsClosed (K : Set (WeakDual 𝕜 E))) {f : WeakDual 𝕜 E} (hf : f ∉ K) :
    ∃ x : E, (∀ g ∈ K, g x = 0) ∧ f x ≠ 0 := by
  have hconv : Convex ℝ (K : Set (WeakDual 𝕜 E)) := (K.restrictScalars ℝ).convex
  obtain ⟨x, u, hu, hfu⟩ := WeakDual.geometric_hahn_banach_closed_point hconv hK hf
  set φ : WeakDual 𝕜 E →ₗ[𝕜] 𝕜 := (topDualPairing 𝕜 E).flip x
  have h0 : ∀ g ∈ K, g x = 0 := Submodule.forall_apply_eq_zero_of_forall_re_lt (φ := φ) hu
  refine ⟨x, h0, fun hfx => ?_⟩
  have h0' : RCLike.re ((0 : WeakDual 𝕜 E) x) < u := hu 0 K.zero_mem
  rw [show ((0 : WeakDual 𝕜 E) x) = 0 from rfl, map_zero] at h0'
  rw [hfx, map_zero] at hfu
  linarith

/-- Let $M$ be a subspace of a normed space $E$ over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. Then
the annihilator $M^\perp \subseteq E^*$ is closed in the weak-$*$ topology.

The annihilator $M^\perp$ is the intersection over $x \in M$ of the kernels of the evaluations
$f \mapsto f(x)$, which are weak-$*$ continuous. -/
theorem Submodule.isClosed_image_toWeakDual_strongDualAnnihilator (M : Submodule 𝕜 E) :
    IsClosed (StrongDual.toWeakDual '' (M.strongDualAnnihilator : Set (StrongDual 𝕜 E))) := by
  have : StrongDual.toWeakDual '' (M.strongDualAnnihilator : Set (StrongDual 𝕜 E)) =
      ⋂ x ∈ M, {f : WeakDual 𝕜 E | f x = 0} := by
    ext f
    simp only [Set.mem_image, SetLike.mem_coe, Submodule.mem_strongDualAnnihilator, Set.mem_iInter,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨g, hg, rfl⟩ x hx
      exact hg x hx
    · intro h
      exact ⟨WeakDual.toStrongDual f, h, rfl⟩
  rw [this]
  exact isClosed_biInter fun x _ => isClosed_eq (WeakDual.eval_continuous x) continuous_const

/-- **The weak-$*$ bipolar theorem for subspaces.** Let $E$ be a normed space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $N$ be a subspace of $E^*$. Then
$(N^\perp)^\perp$ is the closure of $N$ in the weak-$*$ topology, where $N^\perp \subseteq E$
and $(N^\perp)^\perp \subseteq E^*$.

The inclusion $\supseteq$ holds because $(N^\perp)^\perp$ contains $N$ and is weak-$*$ closed.
For $\subseteq$, a functional $f_0 \in (N^\perp)^\perp$ outside the weak-$*$ closure $K$ of $N$
is separated from the closed subspace $K$ by a point $x$
(`Submodule.exists_weakDual_eval_eq_zero_of_notMem`). This point lies in $N^\perp$, but
$f_0(x) \neq 0$. The version with the norm closure,
`Submodule.strongDualAnnihilator_strongDualCoannihilator`, holds when $E$ is reflexive, where
the two closures of a subspace agree. -/
theorem Submodule.strongDualAnnihilator_strongDualCoannihilator_eq_closure_toWeakDual
    (N : Submodule 𝕜 (StrongDual 𝕜 E)) :
    StrongDual.toWeakDual '' (N.strongDualCoannihilator.strongDualAnnihilator :
      Set (StrongDual 𝕜 E)) = closure (StrongDual.toWeakDual '' (N : Set (StrongDual 𝕜 E))) := by
  refine le_antisymm (fun f₀ hf₀ => ?_)
    (closure_minimal (Set.image_mono (N.le_strongDualCoannihilator_strongDualAnnihilator))
      (N.strongDualCoannihilator.isClosed_image_toWeakDual_strongDualAnnihilator))
  obtain ⟨f₀, hf₀, rfl⟩ := hf₀
  by_contra hcl
  -- the weak-∗ closure of `N` as a closed submodule of `WeakDual 𝕜 E`
  set K : Submodule 𝕜 (WeakDual 𝕜 E) :=
    (N.map ((StrongDual.toWeakDual (𝕜 := 𝕜) (E := E)) :
      StrongDual 𝕜 E →ₗ[𝕜] WeakDual 𝕜 E)).topologicalClosure with hK
  have hKc : (K : Set (WeakDual 𝕜 E)) = closure (StrongDual.toWeakDual '' (N : Set _)) := by
    rw [hK, Submodule.topologicalClosure_coe, Submodule.map_coe]
    rfl
  have hfK : StrongDual.toWeakDual f₀ ∉ K := by rwa [← SetLike.mem_coe, hKc]
  obtain ⟨x, hx, hfx⟩ := K.exists_weakDual_eval_eq_zero_of_notMem
    (by rw [hKc]; exact isClosed_closure) hfK
  have hxN : x ∈ N.strongDualCoannihilator := Submodule.mem_strongDualCoannihilator.2 fun f hf =>
    hx (StrongDual.toWeakDual f) (Submodule.le_topologicalClosure _ ⟨f, hf, rfl⟩)
  exact hfx (Submodule.mem_strongDualAnnihilator.1 hf₀ x hxN)

end WeakStar
