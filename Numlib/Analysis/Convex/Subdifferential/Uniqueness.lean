import Numlib.Analysis.Convex.Subdifferential.Calculus
import Numlib.Analysis.Convex.Subdifferential.Convergence
import Numlib.Analysis.Convex.Subdifferential.Gradient

/-!
# A unique subgradient forces differentiability

A proper convex function on a finite-dimensional space is differentiable at `x` exactly when it has
a single subgradient there, and that subgradient is then the gradient. The forward half is
`subdifferential_eq_singleton_of_hasFDerivAt`; the converse is proved here, and with it the exposed
points of `epi f*` and of a support set move from a subgradient form to a gradient form.

The substance is an interior step the book passes over. `∂f x = {y₀}` leaves no room for a normal
direction to `dom f`, and in finite dimensions a convex set is a neighbourhood of every point at
which its normal cone is trivial. With `x` interior, `f'(x; ·)` is finite in every direction, hence
continuous and closed, so the support-function formula — which computes only `cl f'(x; ·)` —
computes `f'(x; ·)` itself, and it is linear.

## Main results

* `mem_interior_dom_of_subdifferential_eq_singleton` — the interior step.
* `hasGradientAtFn_iff_subdifferential_eq_singleton` — the equivalence in full
  ([rockafellar1970convex] Theorem 25.1), with
  `differentiableAtFn_iff_exists_subdifferential_eq_singleton` naming no gradient.
* `hasGradientAtFn_clFn_iff` — `∇(cl f) = ∇f`: a closure changes no gradient and creates none.
* `mem_exposedPoints_epi_conj_iff_hasGradientAtFn`,
  `mem_exposedPoints_supportSet_iff_hasGradientAtFn` — the exposed points of `epi f*` and of a
  support set, for a merely proper convex `f`, by reduction to `cl f`. Only the *gradients*
  transfer: `∂f = ∂(cl f)` fails at relative boundary points, so the subgradient forms in
  `Gradient.lean` keep their `ClosedFn` hypothesis.

## References

* [rockafellar1970convex] §23, §25.
-/

open Set

namespace ConvexAnalysis

/-! ### The interior step -/

section Interior

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {x : E} {y₀ : F}

include B in
/-- A lone subgradient puts `x` in the interior of `dom f`: it leaves no room for a normal
direction to `dom f`, and in finite dimensions a convex set is a neighbourhood of every point at
which its normal cone is trivial. -/
theorem mem_interior_dom_of_subdifferential_eq_singleton [IsCompatiblePairing B] (hf : ConvexFn f)
    (hp : Proper f) (h : subdifferential B f x = {y₀}) : x ∈ interior (dom f) := by
  have hy₀ : y₀ ∈ subdifferential B f x := by rw [h]; rfl
  exact mem_interior_of_normalCone_eq_zero hf.convex_dom (mem_dom_of_mem_subdifferential hp hy₀)
    (normalCone_dom_eq_zero_of_subdifferential_eq_singleton h)

end Interior

/-! ### The converse half -/

section Converse

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {x : E} {y₀ : F}

/-- At an interior point of `dom f` the directional derivative is its own closure: it is finite in
every direction there, hence a finite convex function on the whole space, hence continuous. This is
what removes the `cl` from the support-function formula for `f'(x; ·)`. -/
theorem closedFn_dirDeriv_of_mem_interior_dom (hf : ConvexFn f) (hp : Proper f)
    (hx : x ∈ interior (dom f)) : ClosedFn (dirDeriv f x) := by
  have hri : x ∈ ri (dom f) := Convex.interior_subset_relint hf.convex_dom ⟨x, hx⟩ hx
  have hgp : Proper (dirDeriv f x) := proper_dirDeriv_of_mem_relint_dom hf hp hri
  have hgc : ConvexFn (dirDeriv f x) :=
    convexFn_dirDeriv hf (mem_dom.1 (interior_subset hx)).ne (hp.ne_bot x)
  have hdom : dom (dirDeriv f x) = univ :=
    (dom_dirDeriv_eq_univ_iff_mem_interior_dom hf hp hri).2 hx
  exact (closedFn_iff_lowerSemicontinuous hgp.ne_bot).2
    (hgc.continuous_of_dom_eq_univ hgp hdom).lowerSemicontinuous

/-- **The converse half**: a convex function with a *unique* subgradient at `x` is differentiable
there, and the subgradient is the gradient. Properness replaces the usual "let `f` be finite at
`x`", which is weaker only in appearance: where `f = -∞`, every element of `F` is a subgradient. -/
theorem hasGradientAtFn_evalCLM_of_subdifferential_eq_singleton [IsCompatiblePairing B]
    (hf : ConvexFn f) (hp : Proper f) (h : subdifferential B f x = {y₀}) :
    HasGradientAtFn f (evalCLM B y₀) x := by
  have hint := mem_interior_dom_of_subdifferential_eq_singleton hf hp h
  have ht : f x ≠ ⊤ := (mem_dom.1 (interior_subset hint)).ne
  have hb : f x ≠ ⊥ := hp.ne_bot x
  have hcl : clFn (dirDeriv f x) = dirDeriv f x := closedFn_dirDeriv_of_mem_interior_dom hf hp hint
  have heq : dirDeriv f x = fun v => ((B v y₀ : ℝ) : EReal) :=
    hcl.symm.trans (clFn_dirDeriv_eq_of_subdifferential_eq_singleton hf ht hb h)
  exact hasGradientAtFn_of_dirDeriv_eq hf ht hb fun v => congrFun heq v

end Converse

/-! ### The equivalence in full -/

section Full

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x : E} {f' : StrongDual ℝ E}

/-- The converse half in the pairing of `E` with its continuous dual: there `evalCLM` is the
identity, so the unique subgradient *is* the gradient. -/
theorem hasGradientAtFn_of_subdifferential_eq_singleton (hf : ConvexFn f) (hp : Proper f)
    (h : subdifferential (topDualPairing ℝ E).flip f x = {f'}) : HasGradientAtFn f f' x :=
  hasGradientAtFn_evalCLM_of_subdifferential_eq_singleton (B := (topDualPairing ℝ E).flip) hf hp h

/-- For a proper convex function, having gradient `f'` at `x` and having `f'` as sole subgradient
at `x` are the same thing. -/
theorem hasGradientAtFn_iff_subdifferential_eq_singleton (hf : ConvexFn f) (hp : Proper f) :
    HasGradientAtFn f f' x ↔ subdifferential (topDualPairing ℝ E).flip f x = {f'} :=
  ⟨fun h => h.subdifferential_eq hf, hasGradientAtFn_of_subdifferential_eq_singleton hf hp⟩

/-- Differentiability at `x` is exactly the subdifferential being a single point. -/
theorem differentiableAtFn_iff_exists_subdifferential_eq_singleton (hf : ConvexFn f)
    (hp : Proper f) :
    DifferentiableAtFn f x ↔
      ∃ y : StrongDual ℝ E, subdifferential (topDualPairing ℝ E).flip f x = {y} :=
  exists_congr fun _ => hasGradientAtFn_iff_subdifferential_eq_singleton hf hp

end Full

/-! ### `∇(cl f) = ∇f` -/

section Closure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x : E} {f' : StrongDual ℝ E}

/-- `cl f` agrees with `f` on a whole neighbourhood of an interior point of `dom f`, since
`interior (dom f)` is open and sits inside `ri (dom f)`. -/
theorem ConvexFn.clFn_eventuallyEq_of_mem_interior_dom (hf : ConvexFn f)
    (hx : x ∈ interior (dom f)) : clFn f =ᶠ[nhds x] f := by
  filter_upwards [isOpen_interior.mem_nhds hx] with z hz
  exact hf.clFn_eq_of_mem_relint_dom (Convex.interior_subset_relint hf.convex_dom ⟨x, hx⟩ hz)

/-- `∇(cl f) = ∇f` for a proper convex `f`: a closure changes no gradient, and creates none. One
direction holds because a gradient of `f` at `x` puts `x` in `int (dom f)`, where the two functions
agree on a neighbourhood; the other needs `ConvexFn.interior_dom_clFn`, since a gradient of `cl f`
only supplies a point interior to the larger domain `dom (cl f)`. -/
theorem hasGradientAtFn_clFn_iff (hf : ConvexFn f) (hp : Proper f) :
    HasGradientAtFn (clFn f) f' x ↔ HasGradientAtFn f f' x := by
  constructor
  · intro h
    have hx : x ∈ interior (dom f) := by
      rw [← hf.interior_dom_clFn hp]
      exact HasGradientAtFn.mem_interior_dom h
    obtain ⟨g, hfg, hd⟩ := h
    exact ⟨g, (hf.clFn_eventuallyEq_of_mem_interior_dom hx).symm.trans hfg, hd⟩
  · intro h
    have hx : x ∈ interior (dom f) := HasGradientAtFn.mem_interior_dom h
    obtain ⟨g, hfg, hd⟩ := h
    exact ⟨g, (hf.clFn_eventuallyEq_of_mem_interior_dom hx).trans hfg, hd⟩

/-- `∇(cl f) = ∇f`, in the form that names no gradient. -/
theorem differentiableAtFn_clFn_iff (hf : ConvexFn f) (hp : Proper f) :
    DifferentiableAtFn (clFn f) x ↔ DifferentiableAtFn f x :=
  exists_congr fun _ => hasGradientAtFn_clFn_iff hf hp

end Closure

/-! ### Exposed points without closedness -/

section ClosureExposedEpi

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}

/-- A subdifferential that is a single point is unchanged by taking the closure: `∂(cl f) = ∂f`
wherever `(cl f) x = f x`, and a singleton subdifferential puts `x` inside `ri (dom f)`, where the
two functions do agree. -/
theorem exists_subdifferential_clFn_eq_singleton_iff [IsCompatiblePairing B] (hf : ConvexFn f)
    (hp : Proper f) {y : F} :
    (∃ x : E, subdifferential B (clFn f) x = {y}) ↔ ∃ x : E, subdifferential B f x = {y} := by
  have key : ∀ x : E, x ∈ interior (dom f) → subdifferential B (clFn f) x = subdifferential B f x :=
    fun x hx => Set.ext fun _ => mem_subdifferential_clFn_iff
      (hf.clFn_eq_of_mem_relint_dom (Convex.interior_subset_relint hf.convex_dom ⟨x, hx⟩ hx))
  constructor
  · rintro ⟨x, hx⟩
    have hint : x ∈ interior (dom f) := by
      rw [← hf.interior_dom_clFn hp]
      exact mem_interior_dom_of_subdifferential_eq_singleton (convexFn_clFn hf) (hf.proper_clFn hp)
        hx
    exact ⟨x, (key x hint).symm.trans hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (key x (mem_interior_dom_of_subdifferential_eq_singleton hf hp hx)).trans hx⟩

variable [TopologicalSpace F]

/-- The exposed points of `epi f*` for `f` merely proper convex. `(cl f)* = f*`, and `cl f` has
exactly the same points of single-valued subdifferential as `f`, so the `ClosedFn` hypothesis of
`mem_exposedPoints_epi_conj_iff` can be discharged by passing to `cl f`. -/
theorem mem_exposedPoints_epi_conj_iff_of_proper [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip] (hf : ConvexFn f) (hp : Proper f) {y : F} {μ : ℝ} :
    (y, μ) ∈ (epi (conj B f)).exposedPoints ℝ ↔
      conj B f y = (μ : EReal) ∧ ∃ x : E, subdifferential B f x = {y} := by
  rw [← conj_clFn (B := B) f,
    mem_exposedPoints_epi_conj_iff (convexFn_clFn hf) (hf.proper_clFn hp) (closedFn_clFn f)]
  exact and_congr_right fun _ => exists_subdifferential_clFn_eq_singleton_iff hf hp

end ClosureExposedEpi

section ClosureExposedSupport

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {g : F → EReal}

/-- The exposed points of a support set for `g` merely positively homogeneous proper convex. The
reduction to `cl g` is done directly here; `cl g` supports the same set and is again positively
homogeneous. -/
theorem mem_exposedPoints_supportSet_iff_of_proper [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] (hgh : PosHomogeneous g) (hgc : ConvexFn g) (hgp : Proper g)
    {z : E} :
    z ∈ (supportSet B.flip g).exposedPoints ℝ ↔ ∃ y : F, subdifferential B.flip g y = {z} := by
  obtain ⟨w, hw⟩ := hgp.dom_nonempty
  have hne : ∃ y, g y ≠ ⊤ := ⟨w, (mem_dom.1 hw).ne⟩
  have hph := posHomogeneous_clFn hgh
  rw [← supportSet_clFn (B := B) hgh hne,
    mem_exposedPoints_supportSet_iff (B := B) hph (convexFn_clFn hgc)
    (hgc.proper_clFn hgp) (closedFn_clFn g)]
  exact exists_subdifferential_clFn_eq_singleton_iff hgc hgp

end ClosureExposedSupport

/-! ### Exposed points in differentiability form -/

section Exposed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

/-- The exposed points of `epi f*` are the points `(∇f x, f* (∇f x))` at which `f` is
differentiable. `f` need not be closed. -/
theorem mem_exposedPoints_epi_conj_iff_hasGradientAtFn (hf : ConvexFn f) (hp : Proper f)
    {y : StrongDual ℝ E} {μ : ℝ} :
    (y, μ) ∈ (epi (conj (topDualPairing ℝ E).flip f)).exposedPoints ℝ ↔
      conj (topDualPairing ℝ E).flip f y = (μ : EReal) ∧ ∃ x : E, HasGradientAtFn f y x := by
  rw [mem_exposedPoints_epi_conj_iff_of_proper hf hp]
  exact and_congr_right fun _ =>
    exists_congr fun _ => (hasGradientAtFn_iff_subdifferential_eq_singleton hf hp).symm

/-- For a proper convex positively homogeneous `f`, the exposed points of the closed convex set
that `f` supports are exactly its gradients. Again `f` need not be closed. -/
theorem mem_exposedPoints_supportSet_iff_hasGradientAtFn (hgh : PosHomogeneous f) (hgc : ConvexFn f)
    (hgp : Proper f) {z : StrongDual ℝ E} :
    z ∈ (supportSet (topDualPairing ℝ E).flip f).exposedPoints ℝ ↔
      ∃ y : E, HasGradientAtFn f z y := by
  rw [mem_exposedPoints_supportSet_iff_of_proper (B := topDualPairing ℝ E) hgh hgc hgp]
  exact exists_congr fun _ => (hasGradientAtFn_iff_subdifferential_eq_singleton hgc hgp).symm

end Exposed

end ConvexAnalysis
