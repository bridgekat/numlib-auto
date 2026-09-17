/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.LocallyConvex.WeakSpace` and
`Mathlib.Analysis.Normed.Module.WeakDual`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Numlib.Analysis.Normed.Module.Annihilator

/-!
# Closed sets, semicontinuous functions and linear maps for the weak topologies

The weak topology `σ(E, E')` of a topological vector space `E` is Mathlib's `WeakSpace 𝕜 E` and the
weak-∗ topology `σ(E', E)` of its dual is `WeakDual 𝕜 E`; a set `s ⊆ E` is *weakly closed* when
`IsClosed (toWeakSpace 𝕜 E '' s)`, the spelling of `Mathlib.Analysis.LocallyConvex.WeakSpace`,
and never by abusing the definitional equality `WeakSpace 𝕜 E = E`. This file collects what
[brezis2011functional] §3.2–§3.3 and Problem 9 say about these topologies beyond what Mathlib has.

## Main statements

* `Convex.isClosed_image_toWeakSpace_iff` — **Mazur's theorem**: a convex set is weakly closed iff
  it is closed, in the locally convex generality of Mathlib's `Convex.toWeakSpace_closure`. Hence a
  lower semicontinuous function with convex sublevel sets is weakly lower semicontinuous
  (`LowerSemicontinuous.comp_toWeakSpace_symm_of_convex_le`,
  `ConvexOn.lowerSemicontinuous_comp_toWeakSpace_symm`), in particular the norm
  (`lowerSemicontinuous_norm_comp_toWeakSpace_symm`).
* `isClosed_image_toWeakSpace_closedBall` — closed balls of a normed space are weakly closed, by
  the isometric embedding into the weak-∗ bidual, so without any real-scalar hypothesis; and
  `Submodule.isClosed_image_toWeakSpace_topologicalClosure` — closed subspaces are weakly closed.
* `LinearMap.continuous_iff_continuous_weakSpace` — a linear map between Banach spaces is
  norm–norm continuous iff it is weak–weak continuous; the harder half goes through the closed
  graph theorem in the stronger form `LinearMap.continuous_of_continuous_toWeakSpace_comp`
  (norm–weak continuity already forces norm–norm continuity).
* In finite dimension the weak topology is the norm topology
  (`toWeakSpaceContinuousLinearEquiv`, `tendsto_toWeakSpace_iff_of_finiteDimensional`) and the
  weak-∗ topology of the dual is its norm topology (`toWeakDualContinuousLinearEquiv`).
* In infinite dimension the weak topology is strictly coarser: the weak closure of the unit
  sphere is the closed unit ball (`closure_image_toWeakSpace_sphere`) and the open unit ball is
  not weakly open (`not_isOpen_image_toWeakSpace_ball`).
* `WeakDual.geometric_hahn_banach_closed_point` — **separation in the weak-∗ topology by a point
  of `E`**: a point outside a closed convex subset of `WeakDual 𝕜 E` is strictly separated from it
  by an evaluation `g ↦ g x`; this is the geometric Hahn–Banach theorem in the locally convex
  space `WeakDual 𝕜 E` followed by the weak representation theorem
  `LinearMap.dualEmbedding_surjective`. Its subspace form is
  `Submodule.exists_weakDual_eval_eq_zero_of_notMem`.
* `Submodule.strongDualAnnihilator_strongDualCoannihilator_eq_closure_toWeakDual` — **the weak-∗
  bipolar theorem for subspaces**: `(N^⊥)^⊥` is the weak-∗ closure of `N ⊆ E'`, with the
  annihilators of `Numlib.Analysis.Normed.Module.Annihilator`.
* `WeakBilin.exists_finset_forall_norm_lt_subset_of_mem_nhds_zero` — the basic neighbourhoods
  of `0` in any weak topology, cut out by finitely many functionals, in the pointwise form that
  the arguments here and in `Numlib.Analysis.Normed.Module.WeakStarMetrizable` use.

## Implementation notes

Real convexity in a space over `RCLike 𝕜` is carried, as in Mathlib's `Convex.toWeakSpace_closure`,
by the hypotheses `[Module ℝ E] [IsScalarTower ℝ 𝕜 E]` (automatic when `𝕜 = ℝ`). Statements that
do not need convexity (the closed ball, the sphere, the linear maps, the finite-dimensional facts,
the weak-∗ separation) are free of them. `WeakSpace 𝕜 E` and `WeakDual 𝕜 E` are `def`s, so
instance search does not see through them: finite-dimensionality is supplied by a `have`, and the
`LocallyConvexSpace ℝ (WeakDual 𝕜 E)` instance is registered here through `inferInstanceAs`.

## References

[brezis2011functional] §3.2, §3.3, §3.4, Problem 9.
-/

open Filter Topology Metric Set

/-!
### Basic neighbourhoods of `0` in a weak topology
-/

section Basic

variable {𝕜 E F : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F]
  [Module 𝕜 F]

/-- **Every neighbourhood of `0` in `WeakBilin B` contains a basic set**
`{x | ∀ y ∈ s, ‖B x y‖ < ε}` for a finite `s` and `ε > 0`: the pointwise form of Mathlib's
seminorm basis `LinearMap.hasBasis_weakBilin`. -/
theorem WeakBilin.exists_finset_forall_norm_lt_subset_of_mem_nhds_zero
    {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} {U : Set (WeakBilin B)} (hU : U ∈ 𝓝 (0 : WeakBilin B)) :
    ∃ (s : Finset F) (ε : ℝ), 0 < ε ∧ {x : WeakBilin B | ∀ y ∈ s, ‖B x y‖ < ε} ⊆ U := by
  obtain ⟨V, hV, hVU⟩ := (LinearMap.hasBasis_weakBilin B).mem_iff.1 hU
  obtain ⟨s, ε, hε, rfl⟩ := (SeminormFamily.basisSets_iff _).1 hV
  refine ⟨s, ε, hε, fun x hx => hVU ?_⟩
  rw [id, Seminorm.ball_finset_sup_eq_iInter _ _ _ hε]
  exact Set.mem_iInter₂.2 fun y hy => (Seminorm.mem_ball_zero _).2 (hx y hy)

end Basic

/-!
### Weakly closed sets and Mazur's theorem
-/

section Closed

variable {𝕜 E : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

/-- A set that is closed in the weak topology is closed: it is the preimage of its weak image
under the continuous identity `toWeakSpaceCLM 𝕜 E`. The closed-set companion of Mathlib's
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

/-- **Mazur's theorem**: a convex subset of a locally convex space is weakly closed iff it is
closed. The nontrivial direction is Mathlib's `Convex.toWeakSpace_closure` (separation of a point
from a closed convex set by a continuous linear functional, which is weakly continuous). -/
theorem Convex.isClosed_image_toWeakSpace_iff {s : Set E} (hs : Convex ℝ s) :
    IsClosed (toWeakSpace 𝕜 E '' s) ↔ IsClosed s := by
  refine ⟨WeakSpace.isClosed_of_isClosed, fun h => ?_⟩
  rw [← closure_eq_iff_isClosed, ← hs.toWeakSpace_closure 𝕜, h.closure_eq]

/-- **A lower semicontinuous function with convex sublevel sets is weakly lower semicontinuous**:
each sublevel set is closed and convex, hence weakly closed by Mazur's theorem. Convex functions
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

/-- **A convex lower semicontinuous function is weakly lower semicontinuous.** -/
theorem ConvexOn.lowerSemicontinuous_comp_toWeakSpace_symm {f : E → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hlsc : LowerSemicontinuous f) :
    LowerSemicontinuous (f ∘ (toWeakSpace 𝕜 E).symm) :=
  hlsc.comp_toWeakSpace_symm_of_convex_le fun b => by simpa using hf.convex_le b

end Mazur

section NormLsc

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
  [IsScalarTower ℝ 𝕜 E]

/-- **The norm is weakly lower semicontinuous**: it is convex and continuous. This is the
topological form of `norm_le_liminf_norm_of_weak_tendsto`. -/
theorem lowerSemicontinuous_norm_comp_toWeakSpace_symm :
    LowerSemicontinuous (fun x : WeakSpace 𝕜 E => ‖(toWeakSpace 𝕜 E).symm x‖) :=
  (convexOn_norm convex_univ).lowerSemicontinuous_comp_toWeakSpace_symm (𝕜 := 𝕜)
    continuous_norm.lowerSemicontinuous

end NormLsc

section ClosedSubspace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **A closed subspace is weakly closed**: Mazur's theorem for the closure of a `𝕜`-submodule,
whose real convexity is obtained by restricting scalars, so that no `[NormedSpace ℝ E]`
hypothesis appears. -/
theorem Submodule.isClosed_image_toWeakSpace_topologicalClosure (N : Submodule 𝕜 E) :
    IsClosed (toWeakSpace 𝕜 E '' (N.topologicalClosure : Set E)) := by
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have : IsScalarTower ℝ 𝕜 E := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact (N.topologicalClosure.restrictScalars ℝ).convex.isClosed_image_toWeakSpace_iff.2
    (Submodule.isClosed_topologicalClosure N)

end ClosedSubspace

section ClosedBall

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **Closed balls are weakly closed.** The weak image of `closedBall x r` is the preimage, under
the continuous embedding `inclusionInDoubleDualWeak` of the weak space into the weak-∗ bidual, of
the bidual's closed ball around `J x`, which is weak-∗ closed (`WeakDual.isClosed_closedBall`);
`J` being an isometry, the two balls correspond. No real-scalar hypothesis is needed, unlike the
route through Mazur's theorem. -/
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

/-!
### Linear maps: strong and weak continuity agree
-/

section LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **A linear map between Banach spaces that is continuous into the weak topology is
continuous.** Its graph is the preimage of the diagonal of `WeakSpace 𝕜 F × WeakSpace 𝕜 F`, a
closed set as the weak topology is Hausdorff, under a continuous map; the closed graph theorem
concludes. Completeness of both spaces is genuinely used. -/
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

/-- **A linear map between Banach spaces that is weak–weak continuous is continuous**: it is then
norm–weak continuous, and `LinearMap.continuous_of_continuous_toWeakSpace_comp` applies. -/
theorem LinearMap.continuous_of_continuous_weakSpace_map [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ[𝕜] F)
    (hT : Continuous (fun x : WeakSpace 𝕜 E => toWeakSpace 𝕜 F (T ((toWeakSpace 𝕜 E).symm x)))) :
    Continuous T :=
  T.continuous_of_continuous_toWeakSpace_comp (by
    have := hT.comp (toWeakSpaceCLM 𝕜 E).continuous
    simpa [Function.comp_def] using this)

/-- **A linear map between Banach spaces is continuous iff it is weak–weak continuous.** The
forward direction is Mathlib's `WeakSpace.map` and needs no completeness; together with
`LinearMap.continuous_of_continuous_toWeakSpace_comp`, the three continuity properties
norm–norm, weak–weak and norm–weak of a linear map between Banach spaces coincide. -/
theorem LinearMap.continuous_iff_continuous_weakSpace [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ[𝕜] F) :
    Continuous T ↔
      Continuous (fun x : WeakSpace 𝕜 E => toWeakSpace 𝕜 F (T ((toWeakSpace 𝕜 E).symm x))) :=
  ⟨fun h => (WeakSpace.map (⟨T, h⟩ : E →L[𝕜] F)).continuous,
    T.continuous_of_continuous_weakSpace_map⟩

end LinearMap

/-!
### Finite dimension: the weak topologies are the norm topologies
-/

section FiniteDimensional

variable (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **In finite dimension the weak topology is the norm topology**: the identity from
`WeakSpace 𝕜 E` to `E` is continuous, because every linear map out of a finite-dimensional
Hausdorff topological vector space is. -/
theorem WeakSpace.continuous_toWeakSpace_symm_of_finiteDimensional [FiniteDimensional 𝕜 E] :
    Continuous (toWeakSpace 𝕜 E).symm := by
  have : FiniteDimensional 𝕜 (WeakSpace 𝕜 E) := ‹FiniteDimensional 𝕜 E›
  exact LinearMap.continuous_of_finiteDimensional
    ((toWeakSpace 𝕜 E).symm : WeakSpace 𝕜 E →ₗ[𝕜] E)

/-- The identity `E ≃L[𝕜] WeakSpace 𝕜 E` of a finite-dimensional normed space as a continuous
linear equivalence: the weak topology and the norm topology coincide. -/
def toWeakSpaceContinuousLinearEquiv [FiniteDimensional 𝕜 E] : E ≃L[𝕜] WeakSpace 𝕜 E where
  toLinearEquiv := toWeakSpace 𝕜 E
  continuous_toFun := (toWeakSpaceCLM 𝕜 E).continuous
  continuous_invFun := WeakSpace.continuous_toWeakSpace_symm_of_finiteDimensional 𝕜 E

/-- `toWeakSpaceContinuousLinearEquiv` is the identity `toWeakSpace`. -/
@[simp]
theorem toWeakSpaceContinuousLinearEquiv_apply [FiniteDimensional 𝕜 E] (x : E) :
    toWeakSpaceContinuousLinearEquiv 𝕜 E x = toWeakSpace 𝕜 E x :=
  rfl

variable {𝕜 E}

/-- In a finite-dimensional normed space a net converges weakly iff it converges in norm. -/
theorem tendsto_toWeakSpace_iff_of_finiteDimensional [FiniteDimensional 𝕜 E] {ι : Type*}
    {l : Filter ι} {x : ι → E} {u : E} :
    Tendsto (fun i => toWeakSpace 𝕜 E (x i)) l (𝓝 (toWeakSpace 𝕜 E u)) ↔ Tendsto x l (𝓝 u) :=
  (toWeakSpaceContinuousLinearEquiv 𝕜 E).toHomeomorph.isInducing.tendsto_nhds_iff.symm

variable (𝕜 E)

/-- **On the dual of a finite-dimensional normed space the weak-∗ topology is the norm
topology**: the identity from `WeakDual 𝕜 E` to `StrongDual 𝕜 E` is continuous, the dual being
finite-dimensional and `WeakDual 𝕜 E` a Hausdorff topological vector space. Since weak-∗ ≤ weak ≤
norm always (`WeakDual.continuous_weakSpace_toWeakDual`, `NormedSpace.Dual.toWeakDual_continuous`),
the three topologies of the dual coincide. -/
theorem WeakDual.continuous_toStrongDual_of_finiteDimensional [FiniteDimensional 𝕜 E] :
    Continuous (WeakDual.toStrongDual : WeakDual 𝕜 E → StrongDual 𝕜 E) := by
  have : FiniteDimensional 𝕜 (StrongDual 𝕜 E) := inferInstance
  have : FiniteDimensional 𝕜 (WeakDual 𝕜 E) := ‹FiniteDimensional 𝕜 (StrongDual 𝕜 E)›
  exact LinearMap.continuous_of_finiteDimensional
    (WeakDual.toStrongDual (𝕜 := 𝕜) (E := E)).toLinearMap

/-- The identity `StrongDual 𝕜 E ≃L[𝕜] WeakDual 𝕜 E` of the dual of a finite-dimensional normed
space as a continuous linear equivalence: the weak-∗ topology and the norm topology coincide. -/
def toWeakDualContinuousLinearEquiv [FiniteDimensional 𝕜 E] :
    StrongDual 𝕜 E ≃L[𝕜] WeakDual 𝕜 E where
  toLinearEquiv := StrongDual.toWeakDual
  continuous_toFun := NormedSpace.Dual.toWeakDual_continuous
  continuous_invFun := WeakDual.continuous_toStrongDual_of_finiteDimensional 𝕜 E

/-- `toWeakDualContinuousLinearEquiv` is the identity `StrongDual.toWeakDual`. -/
@[simp]
theorem toWeakDualContinuousLinearEquiv_apply [FiniteDimensional 𝕜 E] (f : StrongDual 𝕜 E) :
    toWeakDualContinuousLinearEquiv 𝕜 E f = StrongDual.toWeakDual f :=
  rfl

end FiniteDimensional

/-!
### Infinite dimension: the weak topology is strictly coarser
-/

section Algebraic

variable {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- **In an infinite-dimensional space finitely many linear functionals have a common nonzero
zero**: otherwise `x ↦ (f i x)ᵢ` would embed `E` into the finite-dimensional `ι → 𝕜`. -/
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

/-- **The weak closure of the unit sphere of an infinite-dimensional normed space is the closed
unit ball.** The ball is weakly closed and contains the sphere; conversely, a basic weak
neighbourhood of a point `x₀` of the open ball is cut out by finitely many functionals, which
have a common nonzero zero `y₀`, and the ray `t ↦ x₀ + t y₀` stays in the neighbourhood and
crosses the sphere by the intermediate value theorem. In particular the sphere is not weakly
closed. -/
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

/-- **The open unit ball of an infinite-dimensional normed space is not weakly open**: otherwise
the sphere, the closed ball minus the open ball, would be weakly closed, whereas its weak closure
is the closed ball (`closure_image_toWeakSpace_sphere`), which contains `0`. -/
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

/-!
### Separation in the weak-∗ topology, and the weak-∗ bipolar theorem for subspaces
-/

section WeakStar

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The weak-∗ dual of a normed space is a locally convex space over `ℝ`: it is Mathlib's
`WeakBilin (topDualPairing 𝕜 E)`, whose `WeakBilin.locallyConvexSpace` instance search does not
find through the `def` `WeakDual`. -/
instance WeakDual.instLocallyConvexSpaceReal : LocallyConvexSpace ℝ (WeakDual 𝕜 E) :=
  inferInstanceAs (LocallyConvexSpace ℝ (WeakBilin (topDualPairing 𝕜 E)))

/-- **Separation in the weak-∗ topology by a point of `E`.** A point `f` outside a closed convex
subset `s` of `WeakDual 𝕜 E` is strictly separated from `s` by an evaluation at some `x : E`:
`re (g x) < u < re (f x)` for all `g ∈ s`. This is the geometric Hahn–Banach theorem
`RCLike.geometric_hahn_banach_closed_point` in the locally convex space `WeakDual 𝕜 E`, whose
continuous linear functionals are exactly the evaluations at points of `E` by the weak
representation theorem `LinearMap.dualEmbedding_surjective`. -/
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

/-- A linear functional whose real part is bounded above on a subspace vanishes on it: scaling by
real numbers kills the real part, and scaling by `I` then kills the imaginary part. -/
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

/-- **Separation from a weak-∗ closed subspace by a point of `E`**: if `f ∉ K` for a closed
subspace `K` of `WeakDual 𝕜 E`, some `x : E` is killed by every element of `K` but not by `f`.
From `WeakDual.geometric_hahn_banach_closed_point`: the evaluation at `x` is bounded above on the
subspace `K`, hence zero on it, and then `re (f x) > u > re (0 x) = 0`. -/
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

/-- **Annihilators are weak-∗ closed**: `M^⊥` is the intersection over `x ∈ M` of the kernels of
the weak-∗ continuous evaluations `f ↦ f x`. -/
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

/-- **The weak-∗ bipolar theorem for subspaces**: for a subspace `N` of the dual, `(N^⊥)^⊥` is the
weak-∗ closure of `N`. The inclusion `⊇` holds because `(N^⊥)^⊥` contains `N` and is weak-∗
closed; for `⊆`, a functional `f₀ ∈ (N^⊥)^⊥` outside the weak-∗ closure `K` of `N` is separated
from the closed subspace `K` by a point `x` (`Submodule.exists_weakDual_eval_eq_zero_of_notMem`),
which then lies in `N^⊥` while `f₀ x ≠ 0`. The norm-closure version
`Submodule.strongDualAnnihilator_strongDualCoannihilator` holds when `E` is reflexive, where the
two closures of a subspace agree. -/
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
