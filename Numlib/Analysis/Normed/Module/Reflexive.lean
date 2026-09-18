/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Module.Reflexive`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Numlib.Analysis.Normed.Module.DualSeparable
import Numlib.Analysis.Normed.Module.FiniteCodim

/-!
# Reflexive normed spaces

A normed space `V` over `𝕜` is *reflexive* when the canonical isometric embedding
`NormedSpace.inclusionInDoubleDual 𝕜 V : V →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 V)`, which sends `v`
to evaluation at `v`, is onto. This is the classical definition: the informal statement
`(V')' = V` is an identification *along that map* and not merely the existence of some isometric
isomorphism between `V` and its bidual, a strictly weaker condition by R. C. James' example of a
non-reflexive space isometric to its bidual.

Reflexivity in this sense is a statement about the *continuous* dual, and is unrelated to
Mathlib's `Module.IsReflexive`, which asks the same of the algebraic dual `Module.Dual` and holds
for essentially no infinite-dimensional normed space. The two must not be confused.

## Main definitions

* `NormedSpace.IsReflexive 𝕜 V` — the canonical embedding of `V` into its double strong dual is
  surjective.
* `NormedSpace.doubleDualIsometryEquiv` — the resulting isometric isomorphism `V ≃ₗᵢ[𝕜] (V')'`.

## Main statements

* `NormedSpace.exists_subseq_forall_dual_tendsto` — **a bounded sequence in a reflexive space has
  a weakly convergent subsequence**. The route is the classical one: restrict to the closed span of
  the sequence, which is separable and reflexive, so that its dual is separable and the sequential
  Banach–Alaoglu theorem applies to its bidual. The converse, that weak sequential compactness
  forces reflexivity, is Kakutani's theorem with the hard half of Eberlein–Šmulian and is not
  proved here.
* `NormedSpace.completeSpace_of_isReflexive` — a reflexive normed space is complete, since it is
  isometric to a dual space.
* `NormedSpace.instIsReflexiveOfInnerProductSpace` — a Hilbert space is reflexive, by the Riesz
  representation of its dual.
* `NormedSpace.isReflexive_of_isClosed` — a closed subspace of a reflexive space is reflexive.
* `NormedSpace.separableSpace_strongDual_of_isReflexive` — the dual of a separable reflexive space
  is separable.
* `NormedSpace.instIsReflexiveOfFiniteDimensional` — a finite-dimensional space is reflexive.
* `NormedSpace.isReflexive_congr` — reflexivity is invariant under continuous linear
  equivalences, so it is a property of the topology and not of the norm.
* `NormedSpace.instIsReflexiveProd`, `instIsReflexivePi`, `instIsReflexivePiLp` — finite
  products of reflexive spaces are reflexive.

Kakutani's theorem (reflexive iff the closed unit ball is weakly compact) and the Milman–Pettis
theorem are in the child modules `Numlib.Analysis.Normed.Module.Reflexive.Kakutani` and
`Numlib.Analysis.Normed.Module.MilmanPettis`.

## References

Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional Analysis
Framework*, 3rd edition, Springer, 2009, Definition 2.7.4 and Theorem 2.7.5 [han2009theoretical].
-/

noncomputable section

open Filter Function Metric Topology TopologicalSpace

namespace NormedSpace

variable (𝕜 : Type*) [RCLike 𝕜] (V : Type*) [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- A normed space `V` over `𝕜` is **reflexive** when the canonical embedding
`NormedSpace.inclusionInDoubleDual 𝕜 V` of `V` into its double strong dual is onto; the embedding
is automatically an isometry onto its image, so `V` is then isometrically isomorphic to `(V')'`
*along the canonical map*, which is what the informal `(V')' = V` means.

This is a property of the pair `(𝕜, V)` and not of `V` alone: a complex normed space may be asked
about over `ℝ` or over `ℂ`, so the scalar field is an explicit argument. -/
class IsReflexive : Prop where
  /-- The canonical embedding into the double strong dual is onto. -/
  surjective_inclusionInDoubleDual : Surjective (inclusionInDoubleDual 𝕜 V)

variable {𝕜 V}

/-- The canonical embedding of a reflexive normed space into its double strong dual is onto. -/
theorem surjective_inclusionInDoubleDual [IsReflexive 𝕜 V] :
    Surjective (inclusionInDoubleDual 𝕜 V) :=
  IsReflexive.surjective_inclusionInDoubleDual

/-- The canonical embedding of a reflexive normed space into its double strong dual is bijective:
it is injective in any normed space, being an isometry. -/
theorem bijective_inclusionInDoubleDual [IsReflexive 𝕜 V] :
    Bijective (inclusionInDoubleDual 𝕜 V) :=
  ⟨(inclusionInDoubleDualLi 𝕜).injective, surjective_inclusionInDoubleDual⟩

variable (𝕜 V)

/-- The isometric isomorphism `V ≃ₗᵢ[𝕜] (V')'` of a reflexive normed space with its double strong
dual, given by the canonical embedding. -/
def doubleDualIsometryEquiv [IsReflexive 𝕜 V] : V ≃ₗᵢ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 V) where
  toLinearEquiv :=
    LinearEquiv.ofBijective (inclusionInDoubleDual 𝕜 V).toLinearMap bijective_inclusionInDoubleDual
  norm_map' := (inclusionInDoubleDualLi 𝕜).norm_map

@[simp]
theorem doubleDualIsometryEquiv_apply [IsReflexive 𝕜 V] (v : V) (ℓ : StrongDual 𝕜 V) :
    doubleDualIsometryEquiv 𝕜 V v ℓ = ℓ v :=
  rfl

/-- **A reflexive normed space is complete**, hence a Banach space: it is isometrically isomorphic
to the dual of a normed space, and dual spaces are complete. -/
theorem completeSpace_of_isReflexive [IsReflexive 𝕜 V] : CompleteSpace V :=
  ((inclusionInDoubleDualLi 𝕜 (E := V)).isometry.isUniformInducing.completeSpace_congr
    surjective_inclusionInDoubleDual).2 inferInstance

section InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- **A Hilbert space is reflexive.** By the Fréchet–Riesz theorem every `ℓ` in the dual is
`⟪z, ·⟫` for a unique `z`, so a functional `w` on the dual is described by the conjugate-linear
functional `y ↦ w ⟪y, ·⟫` on `H`; representing *its* conjugate by a vector `x` gives `ℓ x = w ℓ`
for every `ℓ`. -/
instance instIsReflexiveOfInnerProductSpace : IsReflexive 𝕜 H := by
  refine ⟨fun w => ?_⟩
  -- `y ↦ conj (w ⟪y, ·⟫)` is a bounded linear functional: `InnerProductSpace.toDual` is
  -- conjugate-linear, and conjugating undoes that.
  let g : H →ₗ[𝕜] 𝕜 :=
    { toFun := fun y => starRingEnd 𝕜 (w (InnerProductSpace.toDual 𝕜 H y))
      map_add' := fun y₁ y₂ => by simp
      map_smul' := fun c y => by
        rw [map_smulₛₗ (InnerProductSpace.toDual 𝕜 H) c y]
        simp }
  have hbound : ∀ y : H, ‖g y‖ ≤ ‖w‖ * ‖y‖ := fun y => by
    simpa [g] using w.le_opNorm (InnerProductSpace.toDual 𝕜 H y)
  refine ⟨(InnerProductSpace.toDual 𝕜 H).symm (g.mkContinuous ‖w‖ hbound), ?_⟩
  ext ℓ
  obtain ⟨z, rfl⟩ := (InnerProductSpace.toDual 𝕜 H).surjective ℓ
  have hx : inner 𝕜 ((InnerProductSpace.toDual 𝕜 H).symm (g.mkContinuous ‖w‖ hbound)) z
      = starRingEnd 𝕜 (w (InnerProductSpace.toDual 𝕜 H z)) :=
    InnerProductSpace.toDual_symm_apply
  rw [dual_def, InnerProductSpace.toDual_apply_apply, ← inner_conj_symm, hx]
  simp

end InnerProductSpace

section Subspace

variable {𝕜 V}

/-- **A closed subspace of a reflexive normed space is reflexive.**

A functional `ψ` on `M'` is carried to the functional `f ↦ ψ (f ∘ M.subtypeL)` on `V'`, which
reflexivity of `V` represents by a vector `v`; `v` lies in `M` because a functional vanishing on
`M` is killed by the restriction map, and `v` represents `ψ` because Hahn–Banach extends every
element of `M'` to one of `V'`. -/
theorem isReflexive_of_isClosed [IsReflexive 𝕜 V] (M : Submodule 𝕜 V)
    (hM : IsClosed (M : Set V)) : IsReflexive 𝕜 M := by
  -- restriction of functionals from `V` to `M`, as a bounded linear map
  set r : StrongDual 𝕜 V →L[𝕜] StrongDual 𝕜 M :=
    (ContinuousLinearMap.compL 𝕜 M V 𝕜).flip M.subtypeL
  have hr_apply : ∀ (f : StrongDual 𝕜 V) (m : M), r f m = f m := fun _ _ => rfl
  refine ⟨fun ψ => ?_⟩
  obtain ⟨v, hv⟩ := surjective_inclusionInDoubleDual (𝕜 := 𝕜) (V := V) (ψ.comp r)
  have hvf : ∀ f : StrongDual 𝕜 V, f v = ψ (r f) := fun f => DFunLike.congr_fun hv f
  -- `v` lies in `M`: otherwise a functional vanishing on `M` would separate it
  have hvM : v ∈ M := by
    by_contra hmem
    obtain ⟨f, -, hf0, hfv⟩ := M.exists_dual_eq_zero_of_notMem hM hmem
    refine hfv ?_
    have : r f = 0 := by ext m; simpa [hr_apply] using hf0 m m.2
    rw [hvf f, this, map_zero]
  -- and it represents `ψ`, because every functional on `M` extends to one on `V`
  refine ⟨⟨v, hvM⟩, ?_⟩
  ext g
  obtain ⟨f, hf, -⟩ := exists_extension_norm_eq M g
  have hrf : r f = g := by ext m; rw [hr_apply]; exact hf m
  rw [dual_def, ← hrf, ← hvf f]
  exact hr_apply f ⟨v, hvM⟩

/-- The dual of a separable reflexive space is separable: the bidual is then a homeomorphic copy of
the space, and `separableSpace_of_separableSpace_strongDual` brings separability back down. -/
theorem separableSpace_strongDual_of_isReflexive [IsReflexive 𝕜 V] [SeparableSpace V] :
    SeparableSpace (StrongDual 𝕜 V) := by
  have : SeparableSpace (StrongDual 𝕜 (StrongDual 𝕜 V)) :=
    (doubleDualIsometryEquiv 𝕜 V).surjective.denseRange.separableSpace
      (doubleDualIsometryEquiv 𝕜 V).continuous
  exact separableSpace_of_separableSpace_strongDual (𝕜 := 𝕜)

end Subspace

section WeakCompactness

variable {𝕜 V}

/-- **A bounded sequence in a reflexive normed space has a weakly convergent subsequence**: the
"only if" half of the classical characterization of reflexivity by weak sequential compactness.

The sequence is confined to the closed span `M` of its terms, which is separable and, being a
closed subspace, reflexive; so `M'` is separable and the sequential Banach–Alaoglu theorem applies
to the bidual `M'' = (M')'`, where the sequence sits in a ball. A weak-∗ limit point of the images
in `M''` is represented by a vector of `M` because `M` is reflexive, and restriction of functionals
from `V` to `M` turns weak convergence in `M` into weak convergence in `V`.

Convergence is stated as `ℓ (v (φ k)) → ℓ u` for every bounded linear functional; this is
convergence in the topology of `WeakSpace 𝕜 V`. -/
theorem exists_subseq_forall_dual_tendsto [IsReflexive 𝕜 V] {v : ℕ → V} {C : ℝ}
    (hv : ∀ n, ‖v n‖ ≤ C) :
    ∃ (u : V) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ ℓ : StrongDual 𝕜 V, Tendsto (fun k => ℓ (v (φ k))) atTop (𝓝 (ℓ u)) := by
  -- the closed span of the sequence: separable, closed, hence reflexive
  set M : Submodule 𝕜 V := (Submodule.span 𝕜 (Set.range v)).topologicalClosure with hMdef
  have hMc : IsClosed (M : Set V) := Submodule.isClosed_topologicalClosure _
  have hvM : ∀ n, v n ∈ M :=
    fun n => (Submodule.span 𝕜 (Set.range v)).le_topologicalClosure (Submodule.subset_span ⟨n, rfl⟩)
  have hsep : IsSeparable ((M : Submodule 𝕜 V) : Set V) := by
    rw [hMdef, Submodule.topologicalClosure_coe]
    exact ((Set.countable_range v).isSeparable.span).closure
  have : SeparableSpace M := hsep.separableSpace
  have : IsReflexive 𝕜 M := isReflexive_of_isClosed M hMc
  have : SeparableSpace (StrongDual 𝕜 M) := separableSpace_strongDual_of_isReflexive
  -- the images of the sequence in the bidual of `M`, in the weak-∗ topology
  set w : ℕ → M := fun n => ⟨v n, hvM n⟩ with hw
  set Φ : ℕ → WeakDual 𝕜 (StrongDual 𝕜 M) :=
    fun n => WeakDual.toStrongDual.symm (inclusionInDoubleDual 𝕜 M (w n)) with hΦ
  have hΦapply : ∀ (n : ℕ) (g : StrongDual 𝕜 M), Φ n g = g (w n) := fun _ _ => rfl
  have hmem : ∀ n, Φ n ∈ (WeakDual.toStrongDual (𝕜 := 𝕜) (E := StrongDual 𝕜 M)) ⁻¹'
      Metric.closedBall (0 : StrongDual 𝕜 (StrongDual 𝕜 M)) C := by
    intro n
    have hval : WeakDual.toStrongDual (Φ n) = inclusionInDoubleDual 𝕜 M (w n) :=
      WeakDual.toStrongDual.apply_symm_apply _
    have hnorm : ‖inclusionInDoubleDual 𝕜 M (w n)‖ = ‖v n‖ :=
      (inclusionInDoubleDualLi 𝕜).norm_map (w n)
    simp only [Set.mem_preimage, hval, Metric.mem_closedBall, dist_zero_right, hnorm]
    exact hv n
  -- sequential Banach–Alaoglu over the separable predual `M'`
  obtain ⟨ψ, -, φ, hφ, hlim⟩ :=
    WeakDual.isSeqCompact_closedBall 𝕜 (StrongDual 𝕜 M) 0 C hmem
  obtain ⟨u₀, hu₀⟩ := surjective_inclusionInDoubleDual (WeakDual.toStrongDual ψ)
  have hψ : ∀ g : StrongDual 𝕜 M, ψ g = g u₀ := fun g => (DFunLike.congr_fun hu₀ g).symm
  refine ⟨(u₀ : V), φ, hφ, fun ℓ => ?_⟩
  -- weak convergence in `M` restricts from, and lifts to, weak convergence in `V`
  have := ((WeakDual.eval_continuous (ℓ.comp M.subtypeL)).tendsto ψ).comp hlim
  simpa [Function.comp_def, hΦapply, hψ, hw] using this

end WeakCompactness

section FiniteDimensional

variable {𝕜 V}

/-- **A finite-dimensional normed space is reflexive**: the canonical embedding into the bidual is
injective, and the bidual has the same finite dimension (`NormedSpace.finrank_strongDual` of
`Numlib.Analysis.Normed.Module.FiniteCodim`, twice), so the embedding is onto. Not to be
confused with Mathlib's `Module.IsReflexive`, which concerns the algebraic dual (see the module
doc). -/
instance instIsReflexiveOfFiniteDimensional [FiniteDimensional 𝕜 V] : IsReflexive 𝕜 V := by
  refine ⟨?_⟩
  have h : Module.finrank 𝕜 V = Module.finrank 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 V)) := by
    rw [finrank_strongDual, finrank_strongDual]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h).1
    (inclusionInDoubleDualLi 𝕜 (E := V)).injective

end FiniteDimensional

section Congr

variable {𝕜 V} {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- **Reflexivity transfers along continuous linear equivalences.** Through
`e : V ≃L[𝕜] W`, precomposition `D : f ↦ f ∘ e.symm` identifies the duals, and a functional `ψ` on
`W'` is represented by `e v`, where `v` represents `ψ ∘ D` on `V'`: `ψ g = (ψ ∘ D) (D⁻¹ g) =
(D⁻¹ g) v = g (e v)`. -/
theorem isReflexive_of_continuousLinearEquiv [IsReflexive 𝕜 V] (e : V ≃L[𝕜] W) :
    IsReflexive 𝕜 W := by
  refine ⟨fun ψ => ?_⟩
  set D : StrongDual 𝕜 V ≃L[𝕜] StrongDual 𝕜 W := e.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜)
  obtain ⟨v, hv⟩ := surjective_inclusionInDoubleDual (𝕜 := 𝕜) (V := V)
    (ψ.comp (D : StrongDual 𝕜 V →L[𝕜] StrongDual 𝕜 W))
  refine ⟨e v, ?_⟩
  ext g
  have := DFunLike.congr_fun hv (D.symm g)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply] at this
  rw [dual_def, ← this]
  simp [D]

/-- **Reflexivity is a topological property**: it is invariant under continuous linear
equivalences, in particular under passing to an equivalent norm or along an isometric
isomorphism (`e.toContinuousLinearEquiv` for `e : V ≃ₗᵢ[𝕜] W`). -/
theorem isReflexive_congr (e : V ≃L[𝕜] W) : IsReflexive 𝕜 V ↔ IsReflexive 𝕜 W :=
  ⟨fun _ => isReflexive_of_continuousLinearEquiv e,
    fun _ => isReflexive_of_continuousLinearEquiv e.symm⟩

end Congr

section Prod

variable {𝕜 V} {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F]

/-- **A product of two reflexive spaces is reflexive.** A functional `ψ` on `(E × F)'` restricts
along the two projections to functionals on `E'` and `F'`, represented by `x` and `y`; since every
`g : (E × F)'` is `(g ∘ inl) ∘ fst + (g ∘ inr) ∘ snd`, `ψ g = g (x, 0) + g (0, y) = g (x, y)`. -/
instance instIsReflexiveProd [IsReflexive 𝕜 E] [IsReflexive 𝕜 F] : IsReflexive 𝕜 (E × F) := by
  refine ⟨fun ψ => ?_⟩
  obtain ⟨x, hx⟩ := surjective_inclusionInDoubleDual (𝕜 := 𝕜) (V := E)
    (ψ.comp ((ContinuousLinearMap.compL 𝕜 (E × F) E 𝕜).flip (ContinuousLinearMap.fst 𝕜 E F)))
  obtain ⟨y, hy⟩ := surjective_inclusionInDoubleDual (𝕜 := 𝕜) (V := F)
    (ψ.comp ((ContinuousLinearMap.compL 𝕜 (E × F) F 𝕜).flip (ContinuousLinearMap.snd 𝕜 E F)))
  refine ⟨(x, y), ?_⟩
  ext g
  have hg : g = (g.comp (ContinuousLinearMap.inl 𝕜 E F)).comp (ContinuousLinearMap.fst 𝕜 E F) +
      (g.comp (ContinuousLinearMap.inr 𝕜 E F)).comp (ContinuousLinearMap.snd 𝕜 E F) := by
    refine ContinuousLinearMap.ext fun p => ?_
    obtain ⟨a, b⟩ := p
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.inr_apply]
    rw [← map_add]
    simp
  have h1 := DFunLike.congr_fun hx (g.comp (ContinuousLinearMap.inl 𝕜 E F))
  have h2 := DFunLike.congr_fun hy (g.comp (ContinuousLinearMap.inr 𝕜 E F))
  simp only [dual_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply] at h1 h2
  rw [dual_def]
  conv_rhs => rw [hg]
  rw [map_add, ← h1, ← h2]
  simp only [ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply]
  rw [← map_add]
  simp

end Prod

section Pi

variable {𝕜 V} {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, NormedSpace 𝕜 (V i)]

/-- **A finite product of reflexive spaces is reflexive** (sup norm). A functional `ψ` on the dual
of the product restricts along each projection to a functional on `(V i)'`, represented by `x i`;
since `g = ∑ i, (g ∘ single i) ∘ proj i` for every `g` (`ContinuousLinearMap.sum_comp_single`),
`ψ g = ∑ i, g (single i (x i)) = g x`. -/
instance instIsReflexivePi [∀ i, IsReflexive 𝕜 (V i)] : IsReflexive 𝕜 (∀ i, V i) := by
  classical
  refine ⟨fun ψ => ?_⟩
  have h : ∀ i, ∃ x : V i, inclusionInDoubleDual 𝕜 (V i) x = ψ.comp
      ((ContinuousLinearMap.compL 𝕜 (∀ i, V i) (V i) 𝕜).flip (ContinuousLinearMap.proj i)) :=
    fun i => surjective_inclusionInDoubleDual (𝕜 := 𝕜) (V := V i) _
  choose x hx using h
  refine ⟨x, ?_⟩
  ext g
  have hg : g = ∑ i, (g.comp (ContinuousLinearMap.single 𝕜 V i)).comp
      (ContinuousLinearMap.proj i) := by
    ext p
    simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply]
    exact (ContinuousLinearMap.sum_comp_single 𝕜 V g p).symm
  rw [dual_def]
  conv_rhs => rw [hg]
  rw [map_sum]
  have : ∀ i, ψ ((g.comp (ContinuousLinearMap.single 𝕜 V i)).comp (ContinuousLinearMap.proj i)) =
      g (ContinuousLinearMap.single 𝕜 V i (x i)) := fun i => by
    have := DFunLike.congr_fun (hx i) (g.comp (ContinuousLinearMap.single 𝕜 V i))
    simpa using this.symm
  simp_rw [this]
  exact (ContinuousLinearMap.sum_comp_single 𝕜 V g x).symm

/-- **A finite `ℓ^p` product of reflexive spaces is reflexive**, `1 ≤ p ≤ ∞`: `PiLp p V` is
continuously linearly equivalent to the plain product, which is reflexive by
`instIsReflexivePi`. -/
instance instIsReflexivePiLp (p : ENNReal) [Fact (1 ≤ p)] [∀ i, IsReflexive 𝕜 (V i)] :
    IsReflexive 𝕜 (PiLp p V) :=
  isReflexive_of_continuousLinearEquiv (PiLp.continuousLinearEquiv p 𝕜 V).symm

end Pi

end NormedSpace
