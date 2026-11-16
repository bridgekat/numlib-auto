/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

Let $V$ be a normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, with dual $V^*$ and bidual
$V^{**}$. The canonical embedding $J \colon V \to V^{**}$, $J(v)(\ell) = \ell(v)$, is a linear
isometry. The space $V$ is **reflexive** if $J$ is onto. The presentation follows Definition 2.7.4
and Theorem 2.7.5 of [han2009theoretical]. This file proves that a reflexive space is complete, that
Hilbert spaces, finite-dimensional spaces, closed subspaces of reflexive spaces and finite products
of reflexive spaces are reflexive, that reflexivity is invariant under continuous linear
equivalences, and that a bounded sequence in a reflexive space has a weakly convergent subsequence.

The informal statement $V^{**} = V$ is an identification along $J$. It is not the existence of some
isometric isomorphism between $V$ and $V^{**}$, which is a strictly weaker condition: R. C. James
gave a non-reflexive space that is isometric to its bidual. Kakutani's theorem (reflexivity is
equivalent to weak compactness of the closed unit ball) is in
`Numlib.Analysis.Normed.Module.Reflexive.Kakutani`, and the Milman–Pettis theorem is in
`Numlib.Analysis.Normed.Module.MilmanPettis`.

## Main definitions

* `NormedSpace.IsReflexive`: the canonical embedding of $V$ into $V^{**}$ is onto.
* `NormedSpace.doubleDualIsometryEquiv`: for a reflexive $V$, the isometric isomorphism
  $V \cong V^{**}$ given by $J$.

## Main results

* `NormedSpace.completeSpace_of_isReflexive`: a reflexive normed space is complete.
* `NormedSpace.instIsReflexiveOfInnerProductSpace`: a Hilbert space is reflexive.
* `NormedSpace.isReflexive_of_isClosed`: a closed subspace of a reflexive space is reflexive.
* `NormedSpace.separableSpace_strongDual_of_isReflexive`: the dual of a separable reflexive space is
  separable.
* `NormedSpace.exists_subseq_forall_dual_tendsto`: a bounded sequence in a reflexive space has a
  weakly convergent subsequence.
* `NormedSpace.instIsReflexiveOfFiniteDimensional`: a finite-dimensional normed space is reflexive.
* `NormedSpace.isReflexive_congr`: reflexivity is invariant under continuous linear equivalences, so
  it depends on the topology and not on the norm.
* `NormedSpace.instIsReflexiveProd`, `NormedSpace.instIsReflexivePi` and
  `NormedSpace.instIsReflexivePiLp`: finite products of reflexive spaces are reflexive.

## Proof outline

For the weak sequential compactness, the sequence is restricted to the closed span $M$ of its terms.
The space $M$ is separable and, as a closed subspace, reflexive, so $M^*$ is separable and the
sequential Banach–Alaoglu theorem applies in $M^{**}$. The converse, that weak sequential
compactness of the bounded sets gives reflexivity, is
`NormedSpace.isReflexive_of_forall_exists_subseq_forall_dual_tendsto` in
`Numlib.Analysis.Normed.Module.Reflexive.EberleinSmulian`; it uses Kakutani's theorem and the
Eberlein–Šmulian theorem.

## Implementation notes

* The dual is the continuous dual `StrongDual 𝕜 V`, and $J$ is
  `NormedSpace.inclusionInDoubleDual 𝕜 V`. Reflexivity in this sense is not related to the Mathlib
  class `Module.IsReflexive`, which asks the same of the algebraic dual `Module.Dual` and holds for
  almost no infinite-dimensional normed space.
* Reflexivity is a property of the pair $(\mathbb{K}, V)$: a complex normed space can be considered
  over $\mathbb{R}$ or over $\mathbb{C}$. So the scalar field is an explicit argument of
  `NormedSpace.IsReflexive`.
-/

noncomputable section

open Filter Function Metric Topology TopologicalSpace

namespace NormedSpace

variable (𝕜 : Type*) [RCLike 𝕜] (V : Type*) [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- Let $V$ be a normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. The space $V$ is
**reflexive** if the canonical embedding $J \colon V \to V^{**}$, $J(v)(\ell) = \ell(v)$, is
onto. This is Definition 2.7.4 of [han2009theoretical].

The embedding $J$ is always an isometry, so a reflexive $V$ is isometrically isomorphic to
$V^{**}$ along $J$, which is what the informal statement $V^{**} = V$ means. The scalar field is
an explicit argument, because a complex normed space can be considered over $\mathbb{R}$ or over
$\mathbb{C}$. The embedding is `NormedSpace.inclusionInDoubleDual 𝕜 V`, and the dual is the
continuous dual `StrongDual 𝕜 V`. -/
class IsReflexive : Prop where
  /-- The canonical embedding $J \colon V \to V^{**}$ is onto. -/
  surjective_inclusionInDoubleDual : Surjective (inclusionInDoubleDual 𝕜 V)

variable {𝕜 V}

/-- If $V$ is reflexive, then the canonical embedding $J \colon V \to V^{**}$ is onto. -/
theorem surjective_inclusionInDoubleDual [IsReflexive 𝕜 V] :
    Surjective (inclusionInDoubleDual 𝕜 V) :=
  IsReflexive.surjective_inclusionInDoubleDual

/-- If $V$ is reflexive, then the canonical embedding $J \colon V \to V^{**}$ is bijective. It is
injective in every normed space, because it is an isometry. -/
theorem bijective_inclusionInDoubleDual [IsReflexive 𝕜 V] :
    Bijective (inclusionInDoubleDual 𝕜 V) :=
  ⟨(inclusionInDoubleDualLi 𝕜).injective, surjective_inclusionInDoubleDual⟩

variable (𝕜 V)

/-- For a reflexive normed space $V$, the canonical embedding $J$ as an isometric isomorphism
$V \cong V^{**}$. -/
def doubleDualIsometryEquiv [IsReflexive 𝕜 V] : V ≃ₗᵢ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 V) where
  toLinearEquiv :=
    LinearEquiv.ofBijective (inclusionInDoubleDual 𝕜 V).toLinearMap bijective_inclusionInDoubleDual
  norm_map' := (inclusionInDoubleDualLi 𝕜).norm_map

/-- For a reflexive $V$, the isomorphism `NormedSpace.doubleDualIsometryEquiv` sends $v \in V$ to
the evaluation at $v$: its value at $\ell \in V^*$ is $\ell(v)$. -/
@[simp]
theorem doubleDualIsometryEquiv_apply [IsReflexive 𝕜 V] (v : V) (ℓ : StrongDual 𝕜 V) :
    doubleDualIsometryEquiv 𝕜 V v ℓ = ℓ v :=
  rfl

/-- Let $V$ be a reflexive normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. Then $V$ is
complete, so it is a Banach space.

The space $V$ is isometrically isomorphic to the dual of the normed space $V^*$, and dual spaces
are complete. -/
theorem completeSpace_of_isReflexive [IsReflexive 𝕜 V] : CompleteSpace V :=
  ((inclusionInDoubleDualLi 𝕜 (E := V)).isometry.isUniformInducing.completeSpace_congr
    surjective_inclusionInDoubleDual).2 inferInstance

section InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Let $H$ be a Hilbert space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. Then $H$ is
reflexive.

By the Fréchet–Riesz theorem every $\ell \in H^*$ is $\langle z, \cdot \rangle$ for a unique
$z \in H$. So a functional $w \in H^{**}$ defines the conjugate-linear functional
$y \mapsto w(\langle y, \cdot \rangle)$ on $H$. The representing vector $x$ of its conjugate
satisfies $\ell(x) = w(\ell)$ for every $\ell \in H^*$. -/
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

/-- Let $V$ be a reflexive normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $M$
be a closed subspace of $V$. Then $M$ is reflexive.

A functional $\psi \in M^{**}$ gives the functional $f \mapsto \psi(f|_M)$ on $V^*$, which
reflexivity of $V$ represents by a vector $v \in V$. The vector $v$ lies in $M$: a functional
$f$ that vanishes on $M$ has $f|_M = 0$, so $f(v) = 0$, and the closed subspace $M$ is the
intersection of the kernels of such functionals. The vector $v$ represents $\psi$, because by
the Hahn–Banach theorem every element of $M^*$ extends to an element of $V^*$. -/
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

/-- Let $V$ be a separable reflexive normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$.
Then the dual $V^*$ is separable.

The bidual $V^{**}$ is homeomorphic to $V$, so it is separable, and
`separableSpace_of_separableSpace_strongDual` gives the separability of $V^*$. -/
theorem separableSpace_strongDual_of_isReflexive [IsReflexive 𝕜 V] [SeparableSpace V] :
    SeparableSpace (StrongDual 𝕜 V) := by
  have : SeparableSpace (StrongDual 𝕜 (StrongDual 𝕜 V)) :=
    (doubleDualIsometryEquiv 𝕜 V).surjective.denseRange.separableSpace
      (doubleDualIsometryEquiv 𝕜 V).continuous
  exact separableSpace_of_separableSpace_strongDual (𝕜 := 𝕜)

end Subspace

section WeakCompactness

variable {𝕜 V}

/-- Let $V$ be a reflexive normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let
$(v_n)$ be a sequence in $V$ with $\|v_n\| \le C$ for all $n$. Then there are $u \in V$ and a
strictly increasing $\varphi \colon \mathbb{N} \to \mathbb{N}$ with $$\ell(v_{\varphi(k)}) \to
\ell(u) \quad \text{as } k \to \infty, \text{ for every } \ell \in V^*.$$ This is the "only if"
half of the characterization of reflexivity by weak sequential compactness of the closed unit
ball.

The convergence is convergence in the topology of `WeakSpace 𝕜 V`. The sequence lies in the
closed span $M$ of its terms, which is separable and, as a closed subspace, reflexive. So $M^*$
is separable, and the sequential Banach–Alaoglu theorem applies in the bidual $M^{**}$, where
the sequence lies in a ball. A weak-$*$ limit point of the images in $M^{**}$ is represented by
a vector of $M$ because $M$ is reflexive, and restriction of functionals from $V$ to $M$ turns
weak convergence in $M$ into weak convergence in $V$. -/
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

/-- Let $V$ be a finite-dimensional normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$.
Then $V$ is reflexive.

The canonical embedding into $V^{**}$ is injective, and $V^{**}$ has the same finite dimension
as $V$ by `NormedSpace.finrank_strongDual`, used twice. So the embedding is onto. This is not
the Mathlib class `Module.IsReflexive`, which concerns the algebraic dual. -/
instance instIsReflexiveOfFiniteDimensional [FiniteDimensional 𝕜 V] : IsReflexive 𝕜 V := by
  refine ⟨?_⟩
  have h : Module.finrank 𝕜 V = Module.finrank 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 V)) := by
    rw [finrank_strongDual, finrank_strongDual]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h).1
    (inclusionInDoubleDualLi 𝕜 (E := V)).injective

end FiniteDimensional

section Congr

variable {𝕜 V} {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- Let $V$ and $W$ be normed spaces over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let
$e \colon V \to W$ be a continuous linear equivalence. If $V$ is reflexive, then $W$ is
reflexive.

Composition with $e^{-1}$, $D \colon f \mapsto f \circ e^{-1}$, identifies $V^*$ with $W^*$. A
functional $\psi \in W^{**}$ is represented by $e(v)$, where $v$ represents $\psi \circ D$:
$\psi(g) = (\psi \circ D)(D^{-1} g) = (D^{-1} g)(v) = g(e v)$. -/
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

/-- Let $V$ and $W$ be normed spaces over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let
$e \colon V \to W$ be a continuous linear equivalence. Then $V$ is reflexive if and only if $W$
is reflexive.

So reflexivity is a topological property. It is invariant under a change to an equivalent norm,
and under an isometric isomorphism $e$, through `e.toContinuousLinearEquiv`. -/
theorem isReflexive_congr (e : V ≃L[𝕜] W) : IsReflexive 𝕜 V ↔ IsReflexive 𝕜 W :=
  ⟨fun _ => isReflexive_of_continuousLinearEquiv e,
    fun _ => isReflexive_of_continuousLinearEquiv e.symm⟩

end Congr

section Prod

variable {𝕜 V} {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F]

/-- Let $E$ and $F$ be reflexive normed spaces over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. Then
$E \times F$ is reflexive.

A functional $\psi \in (E \times F)^{**}$ restricts along the two projections to functionals on
$E^*$ and $F^*$, which are represented by $x \in E$ and $y \in F$. Every $g \in (E \times F)^*$
is $g(a, b) = g(a, 0) + g(0, b)$, so $\psi(g) = g(x, 0) + g(0, y) = g(x, y)$. -/
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

/-- Let $(V_i)_{i \in \iota}$ be a finite family of reflexive normed spaces over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. Then the product $\prod_i V_i$ with the sup norm is
reflexive.

A functional $\psi$ on the dual of the product restricts along each projection to a functional
on $V_i^*$, which is represented by $x_i \in V_i$. Every $g$ in the dual of the product is $g =
\sum_i (g \circ \mathrm{single}_i) \circ \mathrm{proj}_i$
(`ContinuousLinearMap.sum_comp_single`), so $\psi(g) = \sum_i g(\mathrm{single}_i(x_i)) = g(x)$. -/
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

/-- Let $(V_i)_{i \in \iota}$ be a finite family of reflexive normed spaces over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $1 \le p \le \infty$. Then the product
$\prod_i V_i$ with the $\ell^p$ norm, `PiLp p V`, is reflexive.

The space `PiLp p V` is continuously linearly equivalent to the product with the sup norm, which
is reflexive by `NormedSpace.instIsReflexivePi`. -/
instance instIsReflexivePiLp (p : ENNReal) [Fact (1 ≤ p)] [∀ i, IsReflexive 𝕜 (V i)] :
    IsReflexive 𝕜 (PiLp p V) :=
  isReflexive_of_continuousLinearEquiv (PiLp.continuousLinearEquiv p 𝕜 V).symm

end Pi

end NormedSpace
