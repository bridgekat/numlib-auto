import Numlib.Analysis.Convex.Subdifferential.Reconstruction

/-!
# Essential smoothness

A convex function is *essentially smooth* when the interior `C` of its effective domain is
non-empty, `f` is differentiable throughout `C`, and `‖∇f xᵢ‖ → ∞` along every sequence in `C`
approaching a point outside `C`. For a closed proper convex function on a finite-dimensional inner
product space this happens exactly when the subdifferential is single-valued, and in that case
`∂f` is the gradient on `C` and empty elsewhere — so the multivalued object `∂f` carries precisely
the information of the classical gradient mapping. That is what makes the Legendre transformation
work.

## Main results

* `EssentiallySmooth f` — the three conditions above, with the gradient written as
  `fderiv ℝ (fun z => (f z).toReal)`.
* `domSubdifferential_eq_interior_dom_of_essentiallySmooth` — `dom ∂f = int (dom f)`.
* `subsingleton_subdifferential_iff_essentiallySmooth` — essential smoothness is exactly
  single-valuedness of `∂f` ([rockafellar1970convex] Theorem 26.1).

## Implementation notes

Condition (c) is stated at every point outside `C`, where the book states it at boundary points of
`C`. Since `C` is open the two readings agree, and this one avoids re-deriving boundaryness at
every use. Gradients are compared through their Riesz representatives, since `∂f x` for the pairing
`innerₗ E` is a set of vectors while `fderiv` lands in `StrongDual ℝ E`.

## References

* [rockafellar1970convex] §26.
-/

namespace ConvexAnalysis

open Filter Metric Topology

section EssentiallySmooth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x : E}

/-- Essential smoothness. Writing `C = int (dom f)`: (a) `C` is non-empty, (b) `f` is
differentiable throughout `C`, and (c) `‖∇f xᵢ‖ → ∞` for every sequence in `C` converging to a
point outside `C`. A finite differentiable convex function on the whole space is essentially
smooth, (c) holding vacuously. -/
structure EssentiallySmooth (f : E → EReal) : Prop where
  /-- (a) The effective domain has non-empty interior. -/
  interior_dom_nonempty : (interior (dom f)).Nonempty
  /-- (b) `f` is differentiable at every interior point of its effective domain. -/
  differentiableAtFn : ∀ ⦃z : E⦄, z ∈ interior (dom f) → DifferentiableAtFn f z
  /-- (c) The gradient blows up along every approach to a point outside the interior. -/
  tendsto_norm_fderiv : ∀ ⦃z : E⦄, z ∉ interior (dom f) → ∀ zs : ℕ → E,
    (∀ i, zs i ∈ interior (dom f)) → Tendsto zs atTop (𝓝 z) →
      Tendsto (fun i => ‖fderiv ℝ (fun w => (f w).toReal) (zs i)‖) atTop atTop

/-- On the interior of the effective domain, an essentially smooth function has exactly one
subgradient, namely its gradient. -/
theorem subdifferential_eq_singleton_of_essentiallySmooth (hf : ConvexFn f)
    (hes : EssentiallySmooth f) (hx : x ∈ interior (dom f)) :
    subdifferential (innerₗ E) f x
      = {(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fun w => (f w).toReal) x)} :=
  subdifferential_innerL_eq_singleton hf
    (DifferentiableAtFn.hasGradientAtFn_fderiv (hes.differentiableAtFn hx))

/-- Off the interior of the effective domain, an essentially smooth closed proper convex function
has *no* subgradient: a subgradient at `x` would force a sequence of gradients to converge, which
condition (c) forbids. -/
theorem subdifferential_eq_empty_of_essentiallySmooth (hf : ConvexFn f) (hp : Proper f)
    (hcl : ClosedFn f) (hes : EssentiallySmooth f) (hx : x ∉ interior (dom f)) :
    subdifferential (innerₗ E) f x = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty]
  rintro ⟨v, hv⟩
  -- A subgradient is built from limits of gradients, by convex hull and normal cone.
  rw [subdifferential_eq_closure_convexHull_gradientLimits_add_normalCone hf hp hcl
    hes.interior_dom_nonempty] at hv
  obtain ⟨a, ha, _, _, _⟩ := hv
  have hSne : (gradientLimits f x).Nonempty := by
    rcases (gradientLimits f x).eq_empty_or_nonempty with hempty | hne
    · rw [hempty, convexHull_empty, closure_empty] at ha
      exact absurd ha (Set.notMem_empty a)
    · exact hne
  obtain ⟨w, xs, vs, hxs, hgrad, hvs⟩ := hSne
  -- The gradients are eventually bounded, contradicting (c).
  have hint : ∀ i, xs i ∈ interior (dom f) := fun i => (hgrad i).mem_interior_dom
  have hfd : ∀ i, fderiv ℝ (fun z => (f z).toReal) (xs i) = InnerProductSpace.toDual ℝ E (vs i) :=
    fun i => (hgrad i).fderiv_toReal_eq
  have hnorm : ∀ i, ‖fderiv ℝ (fun z => (f z).toReal) (xs i)‖ = ‖vs i‖ := fun i => by
    rw [hfd i, LinearIsometryEquiv.norm_map]
  have htop := hes.tendsto_norm_fderiv hx xs hint hxs
  rw [tendsto_congr hnorm] at htop
  exact not_tendsto_atTop_of_tendsto_nhds (hvs.norm) htop

/-- For an essentially smooth closed proper convex function, `dom ∂f` is exactly the interior of
the effective domain. -/
theorem domSubdifferential_eq_interior_dom_of_essentiallySmooth (hf : ConvexFn f) (hp : Proper f)
    (hcl : ClosedFn f) (hes : EssentiallySmooth f) :
    domSubdifferential (innerₗ E) f = interior (dom f) := by
  ext z
  rw [mem_domSubdifferential]
  constructor
  · intro hne
    by_contra hz
    rw [subdifferential_eq_empty_of_essentiallySmooth hf hp hcl hes hz] at hne
    exact absurd hne (Set.not_nonempty_empty)
  · intro hz
    rw [subdifferential_eq_singleton_of_essentiallySmooth hf hes hz]
    exact Set.singleton_nonempty _

/-- An essentially smooth closed proper convex function has a single-valued subdifferential. -/
theorem subsingleton_subdifferential_of_essentiallySmooth (hf : ConvexFn f) (hp : Proper f)
    (hcl : ClosedFn f) (hes : EssentiallySmooth f) (x : E) :
    (subdifferential (innerₗ E) f x).Subsingleton := by
  by_cases hx : x ∈ interior (dom f)
  · rw [subdifferential_eq_singleton_of_essentiallySmooth hf hes hx]
    exact Set.subsingleton_singleton
  · rw [subdifferential_eq_empty_of_essentiallySmooth hf hp hcl hes hx]
    exact Set.subsingleton_empty

/-- A single-valued subdifferential is a gradient on the relative interior: a subgradient exists
at every point of `ri (dom f)`, single-valuedness makes it the only one, and a lone subgradient is
a gradient. -/
theorem differentiableAtFn_of_subsingleton_subdifferential (hf : ConvexFn f) (hp : Proper f)
    (h : ∀ z : E, (subdifferential (innerₗ E) f z).Subsingleton) (hx : x ∈ ri (dom f)) :
    DifferentiableAtFn f x := by
  obtain ⟨v, hv⟩ := subdifferential_nonempty_of_mem_relint_dom (B := innerₗ E) hf hp hx
  exact ⟨_, hasGradientAtFn_toDual_of_subdifferential_eq_singleton hf hp
    (Set.eq_singleton_iff_unique_mem.2 ⟨hv, fun z hz => h x hz hv⟩)⟩

/-- **The substantive half**: a closed proper convex function with a single-valued
subdifferential is essentially smooth. Conditions (a) and (b) hold because a gradient exists only
at interior points, forcing `ri (dom f) = int (dom f)`; condition (c) holds because a bounded
subsequence of gradients would converge to a subgradient at the limit point. -/
theorem essentiallySmooth_of_subsingleton_subdifferential (hf : ConvexFn f) (hp : Proper f)
    (hcl : ClosedFn f) (h : ∀ z : E, (subdifferential (innerₗ E) f z).Subsingleton) :
    EssentiallySmooth f := by
  have hri : ∀ ⦃z : E⦄, z ∈ ri (dom f) → z ∈ interior (dom f) := fun z hz =>
    (differentiableAtFn_of_subsingleton_subdifferential hf hp h hz).choose_spec.mem_interior_dom
  have hne : (interior (dom f)).Nonempty := by
    obtain ⟨z, hz⟩ := Convex.relint_nonempty hf.convex_dom hp.dom_nonempty
    exact ⟨z, hri hz⟩
  refine ⟨hne, fun z hz => differentiableAtFn_of_subsingleton_subdifferential hf hp h
    (Convex.interior_subset_relint hf.convex_dom hne hz), ?_⟩
  intro z hz zs hzs hlim
  by_contra hcon
  -- A bounded subsequence of gradients.
  obtain ⟨b, hb⟩ := not_forall.1 (tendsto_atTop.not.1 hcon)
  obtain ⟨φ, hφ, hφb⟩ := Filter.extraction_of_frequently_atTop (Filter.not_eventually.1 hb)
  set vs : ℕ → E := fun i => (InnerProductSpace.toDual ℝ E).symm
    (fderiv ℝ (fun w => (f w).toReal) (zs i)) with hvsdef
  have hgrad : ∀ i, HasGradientAtFn f (InnerProductSpace.toDual ℝ E (vs i)) (zs i) := fun i => by
    rw [hvsdef, LinearIsometryEquiv.apply_symm_apply]
    exact DifferentiableAtFn.hasGradientAtFn_fderiv
      (differentiableAtFn_of_subsingleton_subdifferential hf hp h
        (Convex.interior_subset_relint hf.convex_dom hne (hzs i)))
  have hvsb : ∀ n, vs (φ n) ∈ closedBall (0 : E) b := fun n => by
    rw [mem_closedBall_zero_iff, hvsdef, LinearIsometryEquiv.norm_map]
    exact (not_le.1 (hφb n)).le
  -- Its limit is a subgradient at `z`, so `f` is differentiable at `z` and `z` is interior.
  obtain ⟨w, _, ψ, hψ, hψlim⟩ := (isCompact_closedBall (0 : E) b).tendsto_subseq hvsb
  have hmem : w ∈ gradientLimits f z :=
    ⟨fun n => zs (φ (ψ n)), fun n => vs (φ (ψ n)), hlim.comp (hφ.comp hψ).tendsto_atTop,
      fun n => hgrad (φ (ψ n)), hψlim⟩
  have hsub : w ∈ subdifferential (innerₗ E) f z :=
    gradientLimits_subset_subdifferential hf hp hcl hmem
  exact hz (hasGradientAtFn_toDual_of_subdifferential_eq_singleton hf hp
    (Set.eq_singleton_iff_unique_mem.2 ⟨hsub, fun u hu => h z hu hsub⟩)).mem_interior_dom

/-- For a closed proper convex function, single-valuedness of the subdifferential and essential
smoothness are the same thing. -/
theorem subsingleton_subdifferential_iff_essentiallySmooth (hf : ConvexFn f) (hp : Proper f)
    (hcl : ClosedFn f) :
    (∀ z : E, (subdifferential (innerₗ E) f z).Subsingleton) ↔ EssentiallySmooth f :=
  ⟨essentiallySmooth_of_subsingleton_subdifferential hf hp hcl,
    subsingleton_subdifferential_of_essentiallySmooth hf hp hcl⟩

end EssentiallySmooth

end ConvexAnalysis
