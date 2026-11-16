/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Extremum.Prox
import Numlib.Analysis.Convex.Saddle.Differential
import Numlib.Analysis.Convex.Saddle.Existence

/-!
# The subdifferential of a saddle-function as a monotone mapping

Let $U, V, X, Y$ be real vector spaces with pairings $\langle \cdot, \cdot \rangle$ of $U$ with $V$
and of $X$ with $Y$, and let $K : U \times Y \to [-\infty, +\infty]$ be a saddle-function in the
class $\Omega(F)$ of a closed convex bifunction $F$ with graph function $f(u, x) = (F u)(x)$. The
subdifferential $\partial K(u, y) \subseteq V \times X$ is then the **partial inversion** of
$\partial f$: the map $((u, y), (v, x)) \mapsto ((u, x), (-v, y))$ carries the graph of $\partial K$
onto the graph of $\partial f$. Partial inversion exchanges the second component of the argument of
a relation with that of its value, and it preserves the form that defines monotonicity. The facts
about $\partial K$ in this module are therefore the matching facts about the subdifferential of a
closed proper convex function. The presentation follows [rockafellar1970convex], §37.

For finite-dimensional inner product spaces $U$ and $X$ and a closed proper $K$, the graph of
$\partial K$ is homeomorphic to $U \times X$ under $((u, x), (u^*, x^*)) \mapsto (u - u^*, x +
x^*)$, and the mapping
$$\rho(u, x) = \{(-u^*, x^*) \mid (u^*, x^*) \in \partial K(u, x)\}$$
is maximal monotone.

## Main definitions

* `ConvexAnalysis.partialInvertEquiv`: the involution $((u, y), (v, x)) \mapsto ((u, x), (v, y))$.
* `ConvexAnalysis.partialInvertNegHomeomorph`: the map $((u, y), (v, x)) \mapsto ((u, x), (-v, y))$,
  as a homeomorphism.
* `ConvexAnalysis.saddleMonotoneRel`: the mapping $\rho$, as a relation.

## Main results

* `ConvexAnalysis.prodPairing_sub_partialInvertEquiv`: partial inversion preserves the monotonicity
  form, so maximal monotonicity transfers across it
  (`ConvexAnalysis.IsMaximalMonotoneRel.preimage_partialInvertEquiv`).
* `ConvexAnalysis.saddleSubdifferentialHomeomorph`: the graph of $\partial K$ is homeomorphic to
  $U \times X$; this is Corollary 37.5.1 of [rockafellar1970convex].
* `ConvexAnalysis.isMaximalMonotoneRel_saddleMonotoneRel`: $\rho$ is maximal monotone; this is
  Corollary 37.5.2 of [rockafellar1970convex].
* `ConvexAnalysis.isMaximalMonotoneRel_setOf_hasSaddleGradientAt`: for a finite differentiable
  concave-convex $K$, the mapping $(u, x) \mapsto (-\nabla_1 K(u, x), \nabla_2 K(u, x))$ is maximal
  monotone.

## Implementation notes

* The transfer lemmas need no symmetry and hold for arbitrary pairings. An inner product enters only
  where the corresponding facts about $\partial f$ need it, and there as a self-pairing rather than
  an `InnerProductSpace` instance: `U × X` carries the supremum norm, but
  `ConvexAnalysis.prodPairing (innerₗ U) (innerₗ X)` is a continuous inner pairing on it.
* Two subdifferentials are in play: `ConvexAnalysis.saddleSubdifferentialOn C D K` for a real-valued
  `K` on an open rectangle, and `ConvexAnalysis.saddleSubdifferential Bu Bx K` for an `EReal`-valued
  `K` on the whole space. They agree at $C = U$, $D = X$
  (`ConvexAnalysis.saddleSubdifferential_eq_saddleSubdifferentialOn`), which the differentiable case
  needs.
-/

namespace ConvexAnalysis

/-! ### Partial inversion -/

section PartialInversion

variable {U V X Y : Type*}

/-- **Partial inversion**: the involution
$$((u, y), (v, x)) \mapsto ((u, x), (v, y))$$
of $(U \times Y) \times (V \times X)$ onto $(U \times X) \times (V \times Y)$. It exchanges the
second component of the argument of a relation with the second component of its value. The term
is Rockafellar's. -/
def partialInvertEquiv : ((U × Y) × (V × X)) ≃ ((U × X) × (V × Y)) where
  toFun r := ((r.1.1, r.2.2), (r.2.1, r.1.2))
  invFun s := ((s.1.1, s.2.2), (s.2.1, s.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- `ConvexAnalysis.partialInvertEquiv` sends $((u, y), (v, x))$ to $((u, x), (v, y))$. -/
@[simp] theorem partialInvertEquiv_apply (r : (U × Y) × (V × X)) :
    (partialInvertEquiv : ((U × Y) × (V × X)) ≃ ((U × X) × (V × Y))) r
      = ((r.1.1, r.2.2), (r.2.1, r.1.2)) := rfl

/-- The inverse of `ConvexAnalysis.partialInvertEquiv` sends $((u, x), (v, y))$ to
$((u, y), (v, x))$. -/
@[simp] theorem partialInvertEquiv_symm_apply (s : (U × X) × (V × Y)) :
    (partialInvertEquiv : ((U × Y) × (V × X)) ≃ ((U × X) × (V × Y))).symm s
      = ((s.1.1, s.2.2), (s.2.1, s.1.2)) := rfl

variable [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- **Partial inversion preserves the monotonicity form.** Let $B_u$ pair $U$ with $V$ and $B_x$
pair $X$ with $Y$. For $r = ((u_1, y_1), (v_1, x_1))$ and $s = ((u_2, y_2), (v_2, x_2))$,
$$B_u(u_1 - u_2, v_1 - v_2) + B_x(x_1 - x_2, y_1 - y_2)$$
is the same number whether it is read as the product pairing of $U \times Y$ with $V \times X$
(with $B_x$ transposed) at $r - s$, or as the product pairing of $U \times X$ with $V \times Y$
at the partial inversions of $r$ and $s$.

No symmetry of the pairings is needed. The pairing on the left is
`ConvexAnalysis.prodPairing Bu Bx.flip`, and the pairing on the right is
`ConvexAnalysis.prodPairing Bu Bx`. -/
theorem prodPairing_sub_partialInvertEquiv (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (r s : (U × Y) × (V × X)) :
    prodPairing Bu Bx.flip (r.1 - s.1) (r.2 - s.2)
      = prodPairing Bu Bx ((partialInvertEquiv r).1 - (partialInvertEquiv s).1)
          ((partialInvertEquiv r).2 - (partialInvertEquiv s).2) := by
  simp only [partialInvertEquiv_apply, prodPairing_apply, LinearMap.flip_apply, map_sub,
    LinearMap.sub_apply]
  ring

variable {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {σ : SetRel (U × X) (V × Y)}

/-- A relation $\sigma \subseteq (U \times X) \times (V \times Y)$ is monotone for the product
pairing of $B_u$ and $B_x$ if and only if its preimage under partial inversion is monotone for
the product pairing of $B_u$ and the transpose of $B_x$. -/
theorem isMonotoneRel_preimage_partialInvertEquiv :
    IsMonotoneRel (prodPairing Bu Bx.flip) (partialInvertEquiv ⁻¹' σ)
      ↔ IsMonotoneRel (prodPairing Bu Bx) σ := by
  constructor
  · intro h p hp q hq
    have hp' : (partialInvertEquiv.symm p : (U × Y) × (V × X)) ∈ partialInvertEquiv ⁻¹' σ := by
      rwa [Set.mem_preimage, Equiv.apply_symm_apply]
    have hq' : (partialInvertEquiv.symm q : (U × Y) × (V × X)) ∈ partialInvertEquiv ⁻¹' σ := by
      rwa [Set.mem_preimage, Equiv.apply_symm_apply]
    have hkey := h _ hp' _ hq'
    rwa [prodPairing_sub_partialInvertEquiv, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply] at hkey
  · intro h r hr s hs
    rw [prodPairing_sub_partialInvertEquiv]
    exact h _ hr _ hs

/-- **Maximal monotonicity transfers across partial inversion.** If $\sigma \subseteq (U \times X)
\times (V \times Y)$ is maximal monotone for the product pairing of $B_u$ and $B_x$, then its
preimage under `ConvexAnalysis.partialInvertEquiv` is maximal monotone for the product pairing
of $B_u$ and the transpose of $B_x$.

This is the whole content of the maximal monotonicity of $\rho$, once $\rho$ is identified with
a partially inverted $\partial f$ (`ConvexAnalysis.saddleMonotoneRel_eq_preimage`). -/
theorem IsMaximalMonotoneRel.preimage_partialInvertEquiv
    (h : IsMaximalMonotoneRel (prodPairing Bu Bx) σ) :
    IsMaximalMonotoneRel (prodPairing Bu Bx.flip) (partialInvertEquiv ⁻¹' σ) := by
  refine ⟨isMonotoneRel_preimage_partialInvertEquiv.2 h.1, fun τ hτ hsub => ?_⟩
  have hcomp : (partialInvertEquiv : ((U × Y) × (V × X)) ≃ ((U × X) × (V × Y)))
      ⁻¹' (partialInvertEquiv.symm ⁻¹' τ) = τ := by
    ext r
    rw [Set.mem_preimage, Set.mem_preimage, Equiv.symm_apply_apply]
  have hτ' : IsMonotoneRel (prodPairing Bu Bx) (partialInvertEquiv.symm ⁻¹' τ) := by
    refine isMonotoneRel_preimage_partialInvertEquiv.1 ?_
    rw [hcomp]
    exact hτ
  have hsub' : σ ⊆ partialInvertEquiv.symm ⁻¹' τ := fun s hs =>
    hsub (by rwa [Set.mem_preimage, Equiv.apply_symm_apply])
  have hfin := h.2 _ hτ' hsub'
  intro r hr
  exact hfin (by rwa [Set.mem_preimage, Equiv.symm_apply_apply])

end PartialInversion

/-! ### Partial inversion with a sign flip, as a homeomorphism -/

section Homeo

variable {U V X Y : Type*} [TopologicalSpace U] [TopologicalSpace X] [TopologicalSpace Y]
  [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]

/-- **Partial inversion with a sign flip** on the first dual component: the homeomorphism
$$((u, y), (v, x)) \mapsto ((u, x), (-v, y))$$
of $(U \times Y) \times (V \times X)$ onto $(U \times X) \times (V \times Y)$. The graph of
$\partial K$ is the preimage of the graph of $\partial f$ under this map. -/
def partialInvertNegHomeomorph : ((U × Y) × (V × X)) ≃ₜ ((U × X) × (V × Y)) where
  toFun r := ((r.1.1, r.2.2), (-r.2.1, r.1.2))
  invFun s := ((s.1.1, s.2.2), (-s.2.1, s.1.2))
  left_inv r := by
    obtain ⟨⟨u, y⟩, ⟨v, x⟩⟩ := r
    simp
  right_inv s := by
    obtain ⟨⟨u, x⟩, ⟨v, y⟩⟩ := s
    simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- `ConvexAnalysis.partialInvertNegHomeomorph` sends $((u, y), (v, x))$ to $((u, x), (-v, y))$. -/
@[simp] theorem partialInvertNegHomeomorph_apply (r : (U × Y) × (V × X)) :
    (partialInvertNegHomeomorph : ((U × Y) × (V × X)) ≃ₜ ((U × X) × (V × Y))) r
      = ((r.1.1, r.2.2), (-r.2.1, r.1.2)) := rfl

end Homeo

/-! ### The mapping $\rho$ -/

section Rho

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- **Rockafellar's mapping $\rho$**: the subdifferential of the saddle-function
$K : U \times Y \to [-\infty, +\infty]$ with the sign of its concave half reversed. A pair
$((u, y), (v, x))$ belongs to $\rho$ when $(-v, x) \in \partial K(u, y)$, so that
$$\rho(u, y) = \{(-v, x) \mid (v, x) \in \partial K(u, y)\}.$$
The sign makes $\rho$ monotone, instead of monotone in one variable and antitone in the other.

Here $\partial K$ is `ConvexAnalysis.saddleSubdifferential Bu Bx.flip K`, with values in
$V \times X$. -/
def saddleMonotoneRel (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (K : U × Y → EReal) :
    SetRel (U × Y) (V × X) :=
  {r | (-r.2.1, r.2.2) ∈ saddleSubdifferential Bu Bx.flip K r.1}

/-- A pair $((u, y), (v, x))$ belongs to $\rho$ if and only if $(-v, x) \in \partial K(u, y)$. -/
@[simp] theorem mem_saddleMonotoneRel {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
    {K : U × Y → EReal} {r : (U × Y) × (V × X)} :
    r ∈ saddleMonotoneRel Bu Bx K ↔ (-r.2.1, r.2.2) ∈ saddleSubdifferential Bu Bx.flip K r.1 :=
  Iff.rfl

end Rho

/-! ### $\rho$ as a preimage of the subdifferential of $f$ -/

section Corollaries

variable {U V X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] {F : Bifun U X} {K : U × Y → EReal}

/-- Let $F$ be a closed convex bifunction from $U$ to $X$, let $f$ be its graph function, and let
$K$ be in the class $\Omega(F)$, where $B_u$, $B_x$ and their transposes are compatible
pairings. Then the graph $\{((u, y), (v, x)) \mid (v, x) \in \partial K(u, y)\}$ of $\partial K$
is the preimage of the graph of $\partial f$ under $((u, y), (v, x)) \mapsto ((u, x), (-v, y))$.
In other words, $(v, x) \in \partial K(u, y)$ if and only if $(-v, y) \in \partial f(u, x)$. -/
theorem setOf_mem_saddleSubdifferential_eq_preimage_homeomorph (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F) :
    {r : (U × Y) × (V × X) | r.2 ∈ saddleSubdifferential Bu Bx.flip K r.1}
      = (partialInvertNegHomeomorph : ((U × Y) × (V × X)) ≃ₜ ((U × X) × (V × Y)))
        ⁻¹' subgradientRel (prodPairing Bu Bx) (graphFn F) :=
  setOf_mem_saddleSubdifferential_eq_preimage Bu Bx hF hcl hK

/-- **$\rho$ is the graph of $\partial f$, partially inverted.** Under the hypotheses of
`ConvexAnalysis.setOf_mem_saddleSubdifferential_eq_preimage_homeomorph`, the relation $\rho$ is
the preimage of the graph of $\partial f$ under `ConvexAnalysis.partialInvertEquiv`:
$((u, y), (v, x)) \in \rho$ if and only if $(v, y) \in \partial f(u, x)$.

The sign flip of `ConvexAnalysis.partialInvertNegHomeomorph` is absorbed into $\rho$, so no sign
remains on the right. -/
theorem saddleMonotoneRel_eq_preimage (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hK : K ∈ bifunSaddleClass Bu Bx F) :
    saddleMonotoneRel Bu Bx K
      = (partialInvertEquiv : ((U × Y) × (V × X)) ≃ ((U × X) × (V × Y)))
        ⁻¹' subgradientRel (prodPairing Bu Bx) (graphFn F) := by
  have h := setOf_mem_saddleSubdifferential_eq_preimage Bu Bx hF hcl hK
  ext r
  have hr := Set.ext_iff.1 h (r.1, (-r.2.1, r.2.2))
  rw [Set.mem_ofPred_eq, Set.mem_preimage] at hr
  rw [mem_saddleMonotoneRel, Set.mem_preimage, hr]
  simp

end Corollaries

/-! ### The inner-product instance -/

section Inner

variable {U X : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  {F : Bifun U X} {K : U × X → EReal}

/-- The case $V = U$, $Y = X$ of
`ConvexAnalysis.setOf_mem_saddleSubdifferential_eq_preimage_homeomorph`, for finite-dimensional
real inner product spaces $U$ and $X$ paired with themselves by the inner product. Here the
transpose of the pairing on $X$ is the pairing itself. -/
theorem setOf_mem_saddleSubdifferential_innerL_eq_preimage (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) (hK : K ∈ bifunSaddleClass (innerₗ U) (innerₗ X) F) :
    {r : (U × X) × (U × X) | r.2 ∈ saddleSubdifferential (innerₗ U) (innerₗ X) K r.1}
      = (partialInvertNegHomeomorph : ((U × X) × (U × X)) ≃ₜ ((U × X) × (U × X)))
        ⁻¹' subgradientRel (prodPairing (innerₗ U) (innerₗ X)) (graphFn F) := by
  have h := setOf_mem_saddleSubdifferential_eq_preimage_homeomorph (innerₗ U) (innerₗ X) hF hcl hK
  rwa [flip_eq_self] at h

/-- Let $U$ and $X$ be finite-dimensional real inner product spaces, let $F$ be a closed convex
bifunction from $U$ to $X$ whose graph function $f$ is proper, and let $K$ be in the class
$\Omega(F)$. Then the graph of $\partial K$ is homeomorphic to $U \times X$ under
$$((u, x), (u^*, x^*)) \mapsto (u - u^*, x + x^*).$$
This is Corollary 37.5.1 of [rockafellar1970convex].

The graph of $\partial K$ is the graph of $\partial f$ partially inverted, and the graph of
$\partial f$ maps homeomorphically onto $U \times X$ by $(z, z^*) \mapsto z + z^*$
(`ConvexAnalysis.subgradientRelHomeomorph`). -/
noncomputable def saddleSubdifferentialHomeomorph (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hpr : ProperConvex (graphFn F)) (hK : K ∈ bifunSaddleClass (innerₗ U) (innerₗ X) F) :
    ↥{r : (U × X) × (U × X) | r.2 ∈ saddleSubdifferential (innerₗ U) (innerₗ X) K r.1} ≃ₜ (U × X) :=
  (partialInvertNegHomeomorph.sets
      (setOf_mem_saddleSubdifferential_innerL_eq_preimage hF hcl hK)).trans
    (subgradientRelHomeomorph (B := prodPairing (innerₗ U) (innerₗ X)) ⟨hF, hcl, hpr⟩)

/-- `ConvexAnalysis.saddleSubdifferentialHomeomorph` sends $((u, x), (u^*, x^*))$ to
$(u - u^*, x^* + x)$. -/
@[simp] theorem saddleSubdifferentialHomeomorph_apply (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F)
    (hpr : ProperConvex (graphFn F)) (hK : K ∈ bifunSaddleClass (innerₗ U) (innerₗ X) F)
    (r : ↥{r : (U × X) × (U × X) | r.2 ∈ saddleSubdifferential (innerₗ U) (innerₗ X) K r.1}) :
    saddleSubdifferentialHomeomorph hF hcl hpr hK r
      = (r.1.1.1 - r.1.2.1, r.1.2.2 + r.1.1.2) := by
  refine Prod.ext ?_ ?_ <;> simp [saddleSubdifferentialHomeomorph, sub_eq_add_neg]

/-- Let $U$ and $X$ be finite-dimensional real inner product spaces, let $F$ be a closed convex
bifunction from $U$ to $X$ whose graph function is proper, and let $K$ be in the class
$\Omega(F)$. Then the mapping
$$\rho(u, x) = \{(-u^*, x^*) \mid (u^*, x^*) \in \partial K(u, x)\}$$
is maximal monotone for the pairing $\langle (u, x), (u', x') \rangle = \langle u, u' \rangle +
\langle x, x' \rangle$. This is Corollary 37.5.2 of [rockafellar1970convex].

The mapping $\rho$ is the partial inversion of $\partial f$
(`ConvexAnalysis.saddleMonotoneRel_eq_preimage`), partial inversion preserves maximal
monotonicity (`ConvexAnalysis.IsMaximalMonotoneRel.preimage_partialInvertEquiv`), and the
subdifferential of a closed proper convex function is maximal monotone. -/
theorem isMaximalMonotoneRel_saddleMonotoneRel (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hpr : ProperConvex (graphFn F)) (hK : K ∈ bifunSaddleClass (innerₗ U) (innerₗ X) F) :
    IsMaximalMonotoneRel (prodPairing (innerₗ U) (innerₗ X))
      (saddleMonotoneRel (innerₗ U) (innerₗ X) K) := by
  have h := (isMaximalMonotoneRel_subgradientRel
    (B := prodPairing (innerₗ U) (innerₗ X)) ⟨hF, hcl, hpr⟩).preimage_partialInvertEquiv
  rw [flip_eq_self] at h
  rwa [saddleMonotoneRel_eq_preimage (innerₗ U) (innerₗ X) hF hcl hK]

end Inner

/-! ### The finite differentiable case -/

section Differentiable

variable {U X : Type*}

/-- For a finite function $K : U \times X \to \mathbb{R}$, the lower simple extension of $K$
relative to $U \times X$ is $K$ itself, read in `EReal`. This links a real-valued $K$ with an
`EReal`-valued one. -/
theorem lowerSimpleExt_univ (K : U × X → ℝ) :
    lowerSimpleExt (Set.univ : Set U) (Set.univ : Set X) K = fun p => ((K p : ℝ) : EReal) :=
  funext fun _ => lowerSimpleExt_of_mem (Set.mem_univ _) (Set.mem_univ _)

variable [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] {K : U × X → ℝ}

omit [FiniteDimensional ℝ U] [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] in
/-- For a finite $K : U \times X \to \mathbb{R}$ and a point $p = (u, x)$, the superdifferential of
the concave slice $K(\cdot, x)$ at $u$, read in `EReal`, is the set $\partial_1 K(p)$ of
`ConvexAnalysis.superdifferentialFstOn` relative to all of $U$. -/
theorem superdifferential_eq_superdifferentialFstOn (K : U × X → ℝ) (p : U × X) :
    superdifferential (innerₗ U) (fun u => ((K (u, p.2) : ℝ) : EReal)) p.1
      = superdifferentialFstOn Set.univ K p := by
  ext y
  simp only [mem_superdifferential, mem_superdifferentialFstOn, Set.mem_univ, forall_const,
    innerₗ_apply_apply, ← EReal.coe_add, EReal.coe_le_coe_iff]

omit [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [FiniteDimensional ℝ X] in
/-- For a finite $K : U \times X \to \mathbb{R}$ and a point $p = (u, x)$, the subdifferential of
the convex slice $K(u, \cdot)$ at $x$, read in `EReal`, is the set $\partial_2 K(p)$ of
`ConvexAnalysis.subdifferentialSndOn` relative to all of $X$. -/
theorem subdifferential_eq_subdifferentialSndOn (K : U × X → ℝ) (p : U × X) :
    subdifferential (innerₗ X) (fun x => ((K (p.1, x) : ℝ) : EReal)) p.2
      = subdifferentialSndOn Set.univ K p := by
  ext y
  simp only [mem_subdifferential, mem_subdifferentialSndOn, Set.mem_univ, forall_const,
    innerₗ_apply_apply, ← EReal.coe_add, EReal.coe_le_coe_iff]

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] in
/-- For a finite $K : U \times X \to \mathbb{R}$, the subdifferential
`ConvexAnalysis.saddleSubdifferential` of $K$ read in `EReal` is equal at every point to
`ConvexAnalysis.saddleSubdifferentialOn` relative to all of $U \times X$. The two definitions
differ only in their values at degenerate arguments. -/
theorem saddleSubdifferential_eq_saddleSubdifferentialOn (K : U × X → ℝ) (p : U × X) :
    saddleSubdifferential (innerₗ U) (innerₗ X) (fun q => ((K q : ℝ) : EReal)) p
      = saddleSubdifferentialOn Set.univ Set.univ K p := by
  have h : saddleSubdifferential (innerₗ U) (innerₗ X) (fun q => ((K q : ℝ) : EReal)) p
      = superdifferential (innerₗ U) (fun u => ((K (u, p.2) : ℝ) : EReal)) p.1
        ×ˢ subdifferential (innerₗ X) (fun x => ((K (p.1, x) : ℝ) : EReal)) p.2 := rfl
  rw [h, superdifferential_eq_superdifferentialFstOn, subdifferential_eq_subdifferentialSndOn]
  rfl

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] in
/-- Let $K : U \times X \to \mathbb{R}$ be concave-convex on all of $U \times X$. If $K$ has the
gradient $\nabla K(p) = q$ at $p$, then the subdifferential of $K$, read in `EReal`, at $p$ is
the single point $q = (\nabla_1 K(p), \nabla_2 K(p))$. -/
theorem saddleSubdifferential_eq_singleton_of_hasSaddleGradientAt
    (hK : ConcaveConvexOn (Set.univ : Set U) (Set.univ : Set X) K) {q p : U × X}
    (hd : HasSaddleGradientAt K q p) :
    saddleSubdifferential (innerₗ U) (innerₗ X) (fun z => ((K z : ℝ) : EReal)) p = {q} := by
  rw [saddleSubdifferential_eq_saddleSubdifferentialOn]
  exact saddleSubdifferentialOn_eq_singleton_of_hasSaddleGradientAt isOpen_univ isOpen_univ hK
    (Set.mem_univ _) (Set.mem_univ _) hd

/-- **Rockafellar's $\rho$ for a differentiable $K$.** Let $U$ and $X$ be finite-dimensional real
inner product spaces, and let $K : U \times X \to \mathbb{R}$ be concave-convex on all of
$U \times X$ and differentiable at every point. Then $\rho$, formed from $K$ read in `EReal`, is
the graph of
$$(u, x) \mapsto (-\nabla_1 K(u, x), \nabla_2 K(u, x)).$$
-/
theorem saddleMonotoneRel_eq_setOf_hasSaddleGradientAt
    (hK : ConcaveConvexOn (Set.univ : Set U) (Set.univ : Set X) K)
    (hdiff : ∀ p : U × X, DifferentiableAt ℝ K p) :
    saddleMonotoneRel (innerₗ U) (innerₗ X) (fun z => ((K z : ℝ) : EReal))
      = {r : (U × X) × (U × X) | HasSaddleGradientAt K (-r.2.1, r.2.2) r.1} := by
  ext r
  obtain ⟨q, hq⟩ := (differentiableAt_iff_exists_hasSaddleGradientAt K r.1).1 (hdiff r.1)
  rw [mem_saddleMonotoneRel, flip_eq_self,
    saddleSubdifferential_eq_singleton_of_hasSaddleGradientAt hK hq, Set.mem_singleton_iff,
    Set.mem_ofPred_eq]
  refine ⟨fun h => h ▸ hq, fun h => ?_⟩
  have hsing := saddleSubdifferential_eq_singleton_of_hasSaddleGradientAt hK h
  rw [saddleSubdifferential_eq_singleton_of_hasSaddleGradientAt hK hq] at hsing
  exact (Set.singleton_eq_singleton_iff.1 hsing).symm

/-- Let $U$ and $X$ be finite-dimensional real inner product spaces, and let
$K : U \times X \to \mathbb{R}$ be concave-convex on all of $U \times X$ and differentiable at
every point. Then the mapping
$$(u, x) \mapsto (-\nabla_1 K(u, x), \nabla_2 K(u, x))$$
is maximal monotone for the pairing $\langle (u, x), (u', x') \rangle = \langle u, u' \rangle +
\langle x, x' \rangle$.

The mapping is stated as the set of pairs $(p, (a, b))$ with
`ConvexAnalysis.HasSaddleGradientAt K (-a, b) p`. Differentiability reduces $\partial K$ to a
point, so $\rho$ is the graph of this mapping. The bifunction that represents the class of $K$
comes from the lower simple extension of $K$ relative to $U \times X$. -/
theorem isMaximalMonotoneRel_setOf_hasSaddleGradientAt
    (hK : ConcaveConvexOn (Set.univ : Set U) (Set.univ : Set X) K)
    (hdiff : ∀ p : U × X, DifferentiableAt ℝ K p) :
    IsMaximalMonotoneRel (prodPairing (innerₗ U) (innerₗ X))
      {r : (U × X) × (U × X) | HasSaddleGradientAt K (-r.2.1, r.2.2) r.1} := by
  have hcont : Continuous K := continuous_iff_continuousAt.2 fun p => (hdiff p).continuousAt
  obtain ⟨F, hFconv, hFcl, hFmem⟩ := exists_bifunSaddleClass_lowerSimpleExt (innerₗ U) (innerₗ X)
    (convex_univ) isClosed_univ isClosed_univ Set.univ_nonempty Set.univ_nonempty hK
    (fun u _ => (hcont.comp (continuous_const.prodMk continuous_id)).continuousOn)
    (fun x _ => (hcont.comp (continuous_id.prodMk continuous_const)).continuousOn)
  have hproper := properSaddleFn_lowerSimpleExt (C := (Set.univ : Set U))
    (D := (Set.univ : Set X)) (K := K) Set.univ_nonempty Set.univ_nonempty
  rw [lowerSimpleExt_univ] at hFmem hproper
  have hpr : ProperConvex (graphFn F) :=
    properConvex_graphFn_of_properSaddleFn (innerₗ U) (innerₗ X) hFmem hproper
  rw [← saddleMonotoneRel_eq_setOf_hasSaddleGradientAt hK hdiff]
  exact isMaximalMonotoneRel_saddleMonotoneRel hFconv hFcl hpr hFmem

end Differentiable

end ConvexAnalysis
