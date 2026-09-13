import Numlib.Analysis.Convex.Optimization.Prox
import Numlib.Analysis.Convex.Saddle.Differential
import Numlib.Analysis.Convex.Saddle.Existence

/-!
# The subdifferential of a saddle-function as a monotone mapping

For a closed proper saddle-function `K`, the graph of `∂K` is homeomorphic to the underlying space
under `(u, v, u*, v*) ↦ (u - u*, v + v*)`, and the mapping
`ρ : (u, v) ↦ {(-u*, v*) | (u*, v*) ∈ ∂K (u, v)}` is *maximal monotone*.

Both come from the identification of `∂K` with the **partial inversion** of `∂f`, `f` the graph
function of a convex bifunction representing the class of `K`. Partial inversion exchanges the
second component of a relation's argument with that of its value and preserves the monotonicity
form, so each is the matching fact about the subdifferential of a closed proper convex function.

## Main definitions

* `partialInvertEquiv` — the involution `((u, y), (v, x)) ↦ ((u, x), (v, y))`.
* `partialInvertNegHomeomorph` — the same with the sign flip, a linear homeomorphism.
* `saddleMonotoneRel Bu Bx K` — Rockafellar's `ρ`, as a relation.

## Main results

* `prodPairing_sub_partialInvertEquiv` — partial inversion preserves the monotonicity form, so
  `IsMaximalMonotoneRel.preimage_partialInvertEquiv` transfers maximal monotonicity across it.
* `saddleSubdifferentialHomeomorph` — the graph of `∂K` is homeomorphic to the underlying space
  ([rockafellar1970convex] Corollary 37.5.1).
* `isMaximalMonotoneRel_saddleMonotoneRel` — `ρ` is maximal monotone
  ([rockafellar1970convex] Corollary 37.5.2).
* `isMaximalMonotoneRel_setOf_hasSaddleGradientAt` — for a finite differentiable `K` the mapping is
  `(u, v) ↦ (-∇₁K (u, v), ∇₂K (u, v))`.

## Implementation notes

The transfer lemmas need no symmetry and hold for arbitrary pairings. An inner product enters only
where the corresponding facts about `∂f` do, and there as a self-pairing rather than an
`InnerProductSpace` instance: `U × X` carries the supremum norm, but
`prodPairing (innerₗ U) (innerₗ X)` is a continuous inner pairing on it.

Two subdifferentials are in play — `subdifferentialSaddle C D K` for a real-valued `K` on an open
rectangle, `saddleSubdifferential Bu Bx K` for an `EReal`-valued one on the whole space — and they
agree at `C = D = univ`, which is what the differentiable clause below needs.

## References

* [rockafellar1970convex] §37.
-/

namespace ConvexAnalysis

/-! ### Partial inversion -/

section PartialInversion

variable {U V X Y : Type*}

/-- **Partial inversion**, Rockafellar's word: the involution exchanging the second component of a
relation's argument with that of its value, `((u, y), (v, x)) ↦ ((u, x), (v, y))`. -/
def partialInvertEquiv : ((U × Y) × (V × X)) ≃ ((U × X) × (V × Y)) where
  toFun r := ((r.1.1, r.2.2), (r.2.1, r.1.2))
  invFun s := ((s.1.1, s.2.2), (s.2.1, s.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem partialInvertEquiv_apply (r : (U × Y) × (V × X)) :
    (partialInvertEquiv : ((U × Y) × (V × X)) ≃ ((U × X) × (V × Y))) r
      = ((r.1.1, r.2.2), (r.2.1, r.1.2)) := rfl

@[simp] theorem partialInvertEquiv_symm_apply (s : (U × X) × (V × Y)) :
    (partialInvertEquiv : ((U × Y) × (V × X)) ≃ ((U × X) × (V × Y))).symm s
      = ((s.1.1, s.2.2), (s.2.1, s.1.2)) := rfl

variable [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- **Partial inversion preserves the monotonicity form.** No symmetry is needed: the `X`-half of
the form is `Bx.flip (y₁ - y₂) (x₁ - x₂)` on the source and `Bx (x₁ - x₂) (y₁ - y₂)` on the target,
which is the same number. -/
theorem prodPairing_sub_partialInvertEquiv (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (r s : (U × Y) × (V × X)) :
    prodPairing Bu Bx.flip (r.1 - s.1) (r.2 - s.2)
      = prodPairing Bu Bx ((partialInvertEquiv r).1 - (partialInvertEquiv s).1)
          ((partialInvertEquiv r).2 - (partialInvertEquiv s).2) := by
  simp only [partialInvertEquiv_apply, prodPairing_apply, LinearMap.flip_apply, map_sub,
    LinearMap.sub_apply]
  ring

variable {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {σ : SetRel (U × X) (V × Y)}

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

/-- **Maximal** monotonicity transfers across partial inversion. This is the whole content of the
maximal monotonicity of `ρ`, once `ρ` is identified with a partially inverted `∂f`. -/
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

/-- **Partial inversion with a sign flip** on the first dual component,
`((u, y), (v, x)) ↦ ((u, x), (-v, y))`: the map along which `∂K` is a preimage of `∂f`. -/
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

@[simp] theorem partialInvertNegHomeomorph_apply (r : (U × Y) × (V × X)) :
    (partialInvertNegHomeomorph : ((U × Y) × (V × X)) ≃ₜ ((U × X) × (V × Y))) r
      = ((r.1.1, r.2.2), (-r.2.1, r.1.2)) := rfl

end Homeo

/-! ### Rockafellar's `ρ` -/

section Rho

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- **Rockafellar's `ρ`**: the subdifferential of `K` with the sign of its concave half reversed,
`ρ (u, y) = {(-v, x) | (v, x) ∈ ∂K (u, y)}`. The sign is what makes `ρ` monotone rather than
monotone in one variable and antitone in the other. -/
def saddleMonotoneRel (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (K : U × Y → EReal) :
    SetRel (U × Y) (V × X) :=
  {r | (-r.2.1, r.2.2) ∈ saddleSubdifferential Bu Bx.flip K r.1}

@[simp] theorem mem_saddleMonotoneRel {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
    {K : U × Y → EReal} {r : (U × Y) × (V × X)} :
    r ∈ saddleMonotoneRel Bu Bx K ↔ (-r.2.1, r.2.2) ∈ saddleSubdifferential Bu Bx.flip K r.1 :=
  Iff.rfl

end Rho

/-! ### `ρ` as a preimage of the subdifferential of `f` -/

section Corollaries

variable {U V X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] {F : Bifun U X} {K : U × Y → EReal}

/-- The graph of `∂K` is the preimage of the graph of `∂f` along `partialInvertNegHomeomorph`. -/
theorem setOf_mem_saddleSubdifferential_eq_preimage_homeomorph (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F)
    (hcl : ClosedBifun F) (hK : K ∈ bifunSaddleClass Bu Bx F) :
    {r : (U × Y) × (V × X) | r.2 ∈ saddleSubdifferential Bu Bx.flip K r.1}
      = (partialInvertNegHomeomorph : ((U × Y) × (V × X)) ≃ₜ ((U × X) × (V × Y)))
        ⁻¹' subgradientRel (prodPairing Bu Bx) (graphFn F) :=
  setOf_mem_saddleSubdifferential_eq_preimage Bu Bx hF hcl hK

/-- **`ρ` is the graph of `∂f`, partially inverted.** The sign flip is absorbed into `ρ`, which is
why no sign survives on the right. -/
theorem saddleMonotoneRel_eq_preimage (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hcl : ClosedBifun F)
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

/-- The same preimage description for a space paired with itself, where `Bx.flip` is `Bx`. -/
theorem setOf_mem_saddleSubdifferential_innerL_eq_preimage (hF : ConvexBifun F)
    (hcl : ClosedBifun F) (hK : K ∈ bifunSaddleClass (innerₗ U) (innerₗ X) F) :
    {r : (U × X) × (U × X) | r.2 ∈ saddleSubdifferential (innerₗ U) (innerₗ X) K r.1}
      = (partialInvertNegHomeomorph : ((U × X) × (U × X)) ≃ₜ ((U × X) × (U × X)))
        ⁻¹' subgradientRel (prodPairing (innerₗ U) (innerₗ X)) (graphFn F) := by
  have h := setOf_mem_saddleSubdifferential_eq_preimage_homeomorph (innerₗ U) (innerₗ X) hF hcl hK
  rwa [flip_eq_self] at h

/-- The graph of `∂K` is homeomorphic to `U × X` under `((u, y), (v, x)) ↦ (u - v, x + y)`: it is
the graph of `∂f` partially inverted, and the graph of `∂f` maps onto `U × X` by
`(z, z*) ↦ z + z*`. -/
noncomputable def saddleSubdifferentialHomeomorph (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hK : K ∈ bifunSaddleClass (innerₗ U) (innerₗ X) F) :
    ↥{r : (U × X) × (U × X) | r.2 ∈ saddleSubdifferential (innerₗ U) (innerₗ X) K r.1} ≃ₜ (U × X) :=
  (partialInvertNegHomeomorph.sets
      (setOf_mem_saddleSubdifferential_innerL_eq_preimage hF hcl hK)).trans
    (subgradientRelHomeomorph (B := prodPairing (innerₗ U) (innerₗ X)) ⟨hF, hcl, hpr⟩)

@[simp] theorem saddleSubdifferentialHomeomorph_apply (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hK : K ∈ bifunSaddleClass (innerₗ U) (innerₗ X) F)
    (r : ↥{r : (U × X) × (U × X) | r.2 ∈ saddleSubdifferential (innerₗ U) (innerₗ X) K r.1}) :
    saddleSubdifferentialHomeomorph hF hcl hpr hK r
      = (r.1.1.1 - r.1.2.1, r.1.2.2 + r.1.1.2) := by
  refine Prod.ext ?_ ?_ <;> simp [saddleSubdifferentialHomeomorph, sub_eq_add_neg]

/-- `ρ : (u, v) ↦ {(-u*, v*) | (u*, v*) ∈ ∂K (u, v)}` is maximal monotone: it is the partial
inversion of `∂f`, partial inversion preserves the monotonicity form, and the subdifferential of a
closed proper convex function is maximal monotone. -/
theorem isMaximalMonotoneRel_saddleMonotoneRel (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hK : K ∈ bifunSaddleClass (innerₗ U) (innerₗ X) F) :
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

/-- A finite saddle-function is its own lower simple extension over the whole space: the bridge
between the real-valued `K` and the `EReal`-valued one. -/
theorem lowerSimpleExt_univ (K : U × X → ℝ) :
    lowerSimpleExt (Set.univ : Set U) (Set.univ : Set X) K = fun p => ((K p : ℝ) : EReal) :=
  funext fun _ => lowerSimpleExt_of_mem (Set.mem_univ _) (Set.mem_univ _)

variable [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] {K : U × X → ℝ}

omit [FiniteDimensional ℝ U] [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] in
/-- The concave subdifferential of the `EReal` reading of a finite saddle-function is `∂₁K`. -/
theorem concaveSubdifferential_eq_subdifferentialFst (K : U × X → ℝ) (p : U × X) :
    concaveSubdifferential (innerₗ U) (fun u => ((K (u, p.2) : ℝ) : EReal)) p.1
      = subdifferentialFst Set.univ K p := by
  ext y
  simp only [mem_concaveSubdifferential, mem_subdifferentialFst, Set.mem_univ, forall_const,
    innerₗ_apply_apply, ← EReal.coe_add, EReal.coe_le_coe_iff]

omit [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [FiniteDimensional ℝ X] in
/-- The subdifferential of the `EReal` reading of a finite saddle-function is `∂₂K`. -/
theorem subdifferential_eq_subdifferentialSnd (K : U × X → ℝ) (p : U × X) :
    subdifferential (innerₗ X) (fun x => ((K (p.1, x) : ℝ) : EReal)) p.2
      = subdifferentialSnd Set.univ K p := by
  ext y
  simp only [mem_subdifferential, mem_subdifferentialSnd, Set.mem_univ, forall_const,
    innerₗ_apply_apply, ← EReal.coe_add, EReal.coe_le_coe_iff]

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] in
/-- Over the whole space the `EReal`-valued and the real-valued `∂K` are the same set; the
definitions differ only in where their junk values live. -/
theorem saddleSubdifferential_eq_subdifferentialSaddle (K : U × X → ℝ) (p : U × X) :
    saddleSubdifferential (innerₗ U) (innerₗ X) (fun q => ((K q : ℝ) : EReal)) p
      = subdifferentialSaddle Set.univ Set.univ K p := by
  have h : saddleSubdifferential (innerₗ U) (innerₗ X) (fun q => ((K q : ℝ) : EReal)) p
      = concaveSubdifferential (innerₗ U) (fun u => ((K (u, p.2) : ℝ) : EReal)) p.1
        ×ˢ subdifferential (innerₗ X) (fun x => ((K (p.1, x) : ℝ) : EReal)) p.2 := rfl
  rw [h, concaveSubdifferential_eq_subdifferentialFst, subdifferential_eq_subdifferentialSnd]
  rfl

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] in
/-- For the `EReal`-valued subdifferential as well: where a finite concave-convex `K` has a
gradient, `∂K` is the single point `(∇₁K, ∇₂K)`. -/
theorem saddleSubdifferential_eq_singleton_of_hasSaddleGradientAt
    (hK : ConcaveConvexOn (Set.univ : Set U) (Set.univ : Set X) K) {q p : U × X}
    (hd : HasSaddleGradientAt K q p) :
    saddleSubdifferential (innerₗ U) (innerₗ X) (fun z => ((K z : ℝ) : EReal)) p = {q} := by
  rw [saddleSubdifferential_eq_subdifferentialSaddle]
  exact subdifferentialSaddle_eq_singleton_of_hasSaddleGradientAt isOpen_univ isOpen_univ hK
    (Set.mem_univ _) (Set.mem_univ _) hd

/-- **Rockafellar's `ρ` for a differentiable `K`** is the graph of
`(u, v) ↦ (-∇₁K (u, v), ∇₂K (u, v))`. -/
theorem saddleMonotoneRel_eq_setOf_hasSaddleGradientAt
    (hK : ConcaveConvexOn (Set.univ : Set U) (Set.univ : Set X) K)
    (hdiff : ∀ p : U × X, DifferentiableAt ℝ K p) :
    saddleMonotoneRel (innerₗ U) (innerₗ X) (fun z => ((K z : ℝ) : EReal))
      = {r : (U × X) × (U × X) | HasSaddleGradientAt K (-r.2.1, r.2.2) r.1} := by
  ext r
  obtain ⟨q, hq⟩ := (differentiableAt_iff_exists_hasSaddleGradientAt K r.1).1 (hdiff r.1)
  rw [Set.mem_ofPred_eq, mem_saddleMonotoneRel, flip_eq_self,
    saddleSubdifferential_eq_singleton_of_hasSaddleGradientAt hK hq, Set.mem_singleton_iff]
  refine ⟨fun h => h ▸ hq, fun h => ?_⟩
  have hsing := saddleSubdifferential_eq_singleton_of_hasSaddleGradientAt hK h
  rw [saddleSubdifferential_eq_singleton_of_hasSaddleGradientAt hK hq] at hsing
  exact (Set.singleton_eq_singleton_iff.1 hsing).symm

/-- If `K` is everywhere finite and differentiable, `(u, v) ↦ (-∇₁K (u, v), ∇₂K (u, v))` is
maximal monotone. Differentiability collapses `∂K` to a point, so `ρ` is the graph of that mapping;
the representing bifunction comes from the lower simple extension at `C = D = univ`. -/
theorem isMaximalMonotoneRel_setOf_hasSaddleGradientAt
    (hK : ConcaveConvexOn (Set.univ : Set U) (Set.univ : Set X) K)
    (hdiff : ∀ p : U × X, DifferentiableAt ℝ K p) :
    IsMaximalMonotoneRel (prodPairing (innerₗ U) (innerₗ X))
      {r : (U × X) × (U × X) | HasSaddleGradientAt K (-r.2.1, r.2.2) r.1} := by
  have hcont : Continuous K := continuous_iff_continuousAt.2 fun p => (hdiff p).continuousAt
  obtain ⟨F, hFconv, hFcl, hFmem⟩ := exists_bifunSaddleClass_lowerSimpleExt (innerₗ U) (innerₗ X)
    (convex_univ) isClosed_univ isClosed_univ Set.univ_nonempty Set.univ_nonempty
    (fun u _ => hK.convex_snd u (Set.mem_univ _)) (fun x _ => hK.concave_fst x (Set.mem_univ _))
    (fun u _ => (hcont.comp (continuous_const.prodMk continuous_id)).continuousOn)
    (fun x _ => (hcont.comp (continuous_id.prodMk continuous_const)).continuousOn)
  have hproper := properSaddleFn_lowerSimpleExt (C := (Set.univ : Set U))
    (D := (Set.univ : Set X)) (K := K) Set.univ_nonempty Set.univ_nonempty
  rw [lowerSimpleExt_univ] at hFmem hproper
  have hpr : Proper (graphFn F) :=
    proper_graphFn_of_properSaddleFn (innerₗ U) (innerₗ X) hFmem hproper
  rw [← saddleMonotoneRel_eq_setOf_hasSaddleGradientAt hK hdiff]
  exact isMaximalMonotoneRel_saddleMonotoneRel hFconv hFcl hpr hFmem

end Differentiable

end ConvexAnalysis
