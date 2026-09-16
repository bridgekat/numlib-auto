import Numlib.Analysis.Convex.Subdifferential.Differentiability
import Numlib.Analysis.Convex.Subdifferential.GradientLimit
import Numlib.Analysis.Convex.Subdifferential.Reconstruction
import NumlibSurface.Rockafellar.Common.Euclidean

/-!
# Rockafellar, §25: Differentiability of Convex Functions

The relation between the subdifferential `∂f` and the ordinary gradient `∇f`. Theorem 25.1
identifies the two where `∇f` exists, Theorems 25.3–25.5 say that is almost everywhere on
`int (dom f)`, Theorem 25.6 reconstructs the whole of `∂f` from `∇f`, and Theorem 25.7 says that
gradients of convex functions converge whenever the functions do.

All eleven numbered results of §25 are formalized: Theorems 25.1–25.7 and Corollaries 25.1.1,
25.1.2, 25.1.3, 25.5.1. Theorem 25.3 is stated over `ℝ` rather than `Rn 1`, the book's `I` being an
open interval of the real line; the rest is over `Rn n` with `pairing n`.

Rockafellar's `∇f(x)` is a *vector*, while the backbone's gradient is a continuous linear
functional. `HasGradientVecAt f b x` and `gradientVec f x` are the vector readings, translated by
`linFn`, which is the Fréchet–Riesz map. Differentiability of an extended-real-valued `f` is
`DifferentiableAtFn`: a real-valued function agreeing with `f` near `x` and differentiable there,
which is exactly what `∇f(x)` presupposes. `differentiableAtFn_iff_differentiableAt` is the
dictionary to Mathlib's `DifferentiableAt` of the real trace.

Not all of §25 is finite-dimensional. Theorem 25.1's forward half, both halves of Corollary 25.1.1,
Theorem 25.2's necessity and Theorem 25.4's density clause hold over any normed space. What
genuinely needs `ℝⁿ` is Theorem 25.1's converse, which runs through Corollary 11.6.1, together with
the continuity and measure-zero clauses of Theorems 25.4 and 25.5.

## References

* [rockafellar1970convex] §25.
-/

open Filter MeasureTheory Topology
open scoped Pointwise

namespace Rockafellar

open ConvexAnalysis

variable {n : ℕ}

/-! ### `∇f(x)` as a vector -/

section GradientVector

variable {f : Rn n → EReal} {b x : Rn n}

/-- **Rockafellar's `∇f(x) = b`**, with `b` a vector of `ℝⁿ`: `f` agrees near `x` with a
real-valued function whose Fréchet derivative at `x` is `⟨·, b⟩`. -/
def HasGradientVecAt (f : Rn n → EReal) (b x : Rn n) : Prop :=
  HasGradientAtFn f (linFn b) x

theorem hasGradientVecAt_iff_hasGradientAtFn :
    HasGradientVecAt f b x ↔ HasGradientAtFn f (linFn b) x := Iff.rfl

/-- Differentiability in the sense of §25 is the existence of a gradient *vector*. -/
theorem differentiableAtFn_iff_exists_hasGradientVecAt :
    DifferentiableAtFn f x ↔ ∃ b : Rn n, HasGradientVecAt f b x := by
  constructor
  · rintro ⟨f', hf'⟩
    obtain ⟨b, hb⟩ := exists_linFn f'
    refine ⟨b, ?_⟩
    rw [hasGradientVecAt_iff_hasGradientAtFn, hb]
    exact hf'
  · rintro ⟨b, hb⟩
    exact ⟨linFn b, hb⟩

/-- **`∇f(x)` as a vector**, defined for every `x` and correct where `f` is differentiable: the
Riesz representative of Mathlib's derivative of the real trace of `f`. -/
noncomputable def gradientVec (f : Rn n → EReal) (x : Rn n) : Rn n :=
  (InnerProductSpace.toDual ℝ (Rn n)).symm (fderiv ℝ (fun z => (f z).toReal) x)

theorem linFn_gradientVec (f : Rn n → EReal) (x : Rn n) :
    linFn (gradientVec f x) = fderiv ℝ (fun z => (f z).toReal) x := by
  rw [linFn_eq_toDual]
  exact (InnerProductSpace.toDual ℝ (Rn n)).apply_symm_apply _

/-- The gradient vector is unique where it exists, and `gradientVec` computes it. -/
theorem HasGradientVecAt.gradientVec_eq (h : HasGradientVecAt f b x) : gradientVec f x = b := by
  have hfd : fderiv ℝ (fun z => (f z).toReal) x = linFn b :=
    HasGradientAtFn.fderiv_toReal_eq (hasGradientVecAt_iff_hasGradientAtFn.1 h)
  have hg : gradientVec f x
      = (InnerProductSpace.toDual ℝ (Rn n)).symm (fderiv ℝ (fun z => (f z).toReal) x) := rfl
  rw [hg, hfd, linFn_eq_toDual, LinearIsometryEquiv.symm_apply_apply]

/-- Where `f` is differentiable, `gradientVec f x` **is** its gradient. -/
theorem hasGradientVecAt_gradientVec (h : DifferentiableAtFn f x) :
    HasGradientVecAt f (gradientVec f x) x := by
  have hd := DifferentiableAtFn.hasGradientAtFn_fderiv h
  rw [← linFn_gradientVec f x] at hd
  exact hd

/-- **The finite case.** Where the book says "let `f` be a *finite* convex function", the gradient
is Mathlib's Fréchet derivative of a real-valued function, and this is the translation. -/
theorem hasGradientVecAt_coe {g : Rn n → ℝ} (hd : HasFDerivAt g (linFn b) x) :
    HasGradientVecAt (fun z => ((g z : ℝ) : EReal)) b x :=
  hasGradientAtFn_coe hd

/-- **The dictionary to Mathlib.** At an interior point of `dom f` — and by Corollary 25.1.1 there
is nowhere else to look — differentiability in §25's sense is ordinary differentiability of the
real trace `z ↦ (f z).toReal`. -/
theorem differentiableAtFn_iff_differentiableAt (hp : Proper f) (hx : x ∈ interior (dom f)) :
    DifferentiableAtFn f x ↔ DifferentiableAt ℝ (fun z => (f z).toReal) x :=
  differentiableAtFn_iff_differentiableAt_toReal hp hx

end GradientVector

/-! ### Theorem 25.1 and its corollaries -/

section Theorem251

variable {f : Rn n → EReal} {b x : Rn n}

/-- **Theorem 25.1**, forward half. For a convex `f` finite at `x` and differentiable there,
`∇f(x)` is the *unique* subgradient of `f` at `x`. Nothing in the argument is finite-dimensional,
and the uniqueness half uses neither convexity nor properness. -/
theorem theorem_25_1_forward (hf : ConvexFn f) (h : HasGradientVecAt f b x) :
    subdifferential (pairing n) f x = {b} := by
  have hs := subdifferential_innerL_eq_singleton (E := Rn n) hf
    (hasGradientVecAt_iff_hasGradientAtFn.1 h)
  rwa [linFn_eq_toDual, LinearIsometryEquiv.symm_apply_apply] at hs

/-- **Theorem 25.1**, the displayed inequality: `f(z) ≥ f(x) + ⟨∇f(x), z - x⟩` for every `z`. Like
the forward half it holds over any normed space. -/
theorem theorem_25_1_le (hf : ConvexFn f) (h : HasGradientVecAt f b x) (z : Rn n) :
    f x + ((pairing n (z - x) b : ℝ) : EReal) ≤ f z := by
  have hle := HasGradientAtFn.le hf (hasGradientVecAt_iff_hasGradientAtFn.1 h) z
  rwa [linFn_apply] at hle

/-- **Theorem 25.1**, converse half, and **this one is genuinely finite-dimensional**. If a proper
convex `f` has a unique subgradient at `x` then `f` is differentiable at `x`. In finite dimensions
a convex set is a neighbourhood of every point whose normal cone is trivial (Corollary 11.6.1),
which is the step Rockafellar passes over. -/
theorem theorem_25_1_converse (hf : ConvexFn f) (hp : Proper f)
    (h : subdifferential (pairing n) f x = {b}) : HasGradientVecAt f b x := by
  have hg := hasGradientAtFn_toDual_of_subdifferential_eq_singleton (E := Rn n) hf hp h
  rw [hasGradientVecAt_iff_hasGradientAtFn, linFn_eq_toDual]
  exact hg

/-- **Rockafellar, Theorem 25.1**, in full: for a proper convex function on `ℝⁿ`, having gradient
`b` at `x` and having `b` as sole subgradient at `x` are the same thing. -/
theorem theorem_25_1 (hf : ConvexFn f) (hp : Proper f) :
    HasGradientVecAt f b x ↔ subdifferential (pairing n) f x = {b} :=
  ⟨theorem_25_1_forward hf, theorem_25_1_converse hf hp⟩

/-- **Theorem 25.1** as the book's following sentence states it: `∂f(x)` is a single vector exactly
when `f` is differentiable at `x`. -/
theorem theorem_25_1_differentiableAtFn (hf : ConvexFn f) (hp : Proper f) :
    DifferentiableAtFn f x ↔ ∃ b : Rn n, subdifferential (pairing n) f x = {b} := by
  rw [differentiableAtFn_iff_exists_hasGradientVecAt]
  exact exists_congr fun _ => theorem_25_1 hf hp

/-- **Corollary 25.1.1**, second half: a convex function finite and differentiable at `x` is
proper. This holds in any topological vector space. -/
theorem corollary_25_1_1_proper (hf : ConvexFn f) (h : HasGradientVecAt f b x) : Proper f :=
  HasGradientAtFn.proper hf (hasGradientVecAt_iff_hasGradientAtFn.1 h)

/-- **Corollary 25.1.1**, first half: `x ∈ int (dom f)`. It uses neither convexity nor
differentiability, only that `f` is finite near `x`, which the definition of `∇f(x)` presupposes. -/
theorem corollary_25_1_1_mem_interior (h : HasGradientVecAt f b x) : x ∈ interior (dom f) :=
  HasGradientAtFn.mem_interior_dom (hasGradientVecAt_iff_hasGradientAtFn.1 h)

/-- **Corollary 25.1.2**: for a proper convex `f` on `ℝⁿ`, the exposed points of `epi f*` are the
points `(x*, f*(x*))` such that `f` is differentiable at some `x` with `∇f(x) = x*`. **`f` need not
be closed**, as in the book, which replaces `f` by `cl f` on the strength of its unproved remark
`∇(cl f) = ∇f`; that remark needs `int (dom (cl f)) = int (dom f)` as well as `cl f = f` on the
interior, and both halves are in the backbone. -/
theorem corollary_25_1_2 (hf : ConvexFn f) (hp : Proper f) {y : Rn n} {μ : ℝ} :
    (y, μ) ∈ (epi (conj (pairing n) f)).exposedPoints ℝ ↔
      conj (pairing n) f y = (μ : EReal) ∧ ∃ x : Rn n, HasGradientVecAt f y x := by
  rw [mem_exposedPoints_epi_conj_iff_of_proper (B := pairing n) hf hp]
  exact and_congr_right fun _ => exists_congr fun _ => (theorem_25_1 hf hp).symm

/-- **Corollary 25.1.3**: let `C` be a non-empty closed convex set and `g` a positively homogeneous
proper convex function with `C = {z | ⟨y, z⟩ ≤ g(y) for all y}`. Then `z` is an exposed point of `C`
iff `g` is differentiable at some `y` with `∇g(y) = z`. Non-emptiness and closedness of
`supportSet (pairing n) g` follow from the other hypotheses and are not assumed. -/
theorem corollary_25_1_3 {g : Rn n → EReal} {C : Set (Rn n)} (hgh : PosHomogeneous g)
    (hgc : ConvexFn g) (hgp : Proper g)
    (hC : C = supportSet (pairing n) g) {z : Rn n} :
    z ∈ C.exposedPoints ℝ ↔ ∃ y : Rn n, HasGradientVecAt g z y := by
  subst hC
  have h := mem_exposedPoints_supportSet_iff_of_proper (B := pairing n) hgh hgc hgp (z := z)
  simp only [flip_pairing] at h
  rw [h]
  exact exists_congr fun _ => (theorem_25_1 hgc hgp).symm

end Theorem251

/-! ### Theorem 25.2 -/

section Theorem252

variable {f : Rn n → EReal} {b x : Rn n}

/-- **Theorem 25.2**, necessity: at a point of differentiability the directional derivative is the
linear function `y ↦ ⟨∇f(x), y⟩`. General, like Theorem 25.1's forward half. -/
theorem theorem_25_2_dirDeriv (hf : ConvexFn f) (h : HasGradientVecAt f b x) (v : Rn n) :
    dirDeriv f x v = ((pairing n v b : ℝ) : EReal) := by
  have hd := HasGradientAtFn.dirDeriv_eq hf (hasGradientVecAt_iff_hasGradientAtFn.1 h) v
  rwa [linFn_apply] at hd

/-- **Theorem 25.2**: for a convex `f` finite at `x`, differentiability at `x` is equivalent to
linearity of `f'(x; ·)`. Sufficiency is where `ℝⁿ` is used, through a cross-polytope estimate that
consumes only the `2n` one-sided derivatives along `± bⱼ`. -/
theorem theorem_25_2 (hf : ConvexFn f) (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) :
    DifferentiableAtFn f x ↔
      ∃ b : Rn n, ∀ v : Rn n, dirDeriv f x v = ((pairing n v b : ℝ) : EReal) := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := differentiableAtFn_iff_exists_hasGradientVecAt.1 h
    exact ⟨c, theorem_25_2_dirDeriv hf hc⟩
  · rintro ⟨c, hc⟩
    refine ⟨linFn c, hasGradientAtFn_of_dirDeriv_eq hf ht hb fun v => ?_⟩
    rw [hc v, linFn_apply]

/-- **Theorem 25.2**, last sentence: differentiability at `x` already follows from the existence
and finiteness of the `n` two-sided partial derivatives there. -/
theorem theorem_25_2_partial (hf : ConvexFn f) (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) (c : Fin n → ℝ)
    (hpos : ∀ j, dirDeriv f x (EuclideanSpace.single j (1 : ℝ)) = ((c j : ℝ) : EReal))
    (hneg : ∀ j, dirDeriv f x (-EuclideanSpace.single j (1 : ℝ)) = ((-c j : ℝ) : EReal)) :
    DifferentiableAtFn f x :=
  differentiableAtFn_of_forall_basis_dirDeriv_eq (EuclideanSpace.basisFun (Fin n) ℝ).toBasis hf
    ht hb c (fun j => by simpa using hpos j) fun j => by simpa using hneg j

end Theorem252

/-! ### Theorem 25.3, on the line

Rockafellar's `I` is an open interval of `ℝ` on which `f` is finite; it is `interior (dom f)` here.
His `f'` is defined on `D` only, while `rightDeriv f` is defined everywhere and agrees with `f'` on
`D`, so the clauses below are the book's, strengthened. -/

section Theorem253

variable {f : ℝ → EReal}

/-- **Theorem 25.3**, the definition of `D`: on the line, differentiability at an interior point of
`dom f` is exactly equality of the two one-sided derivatives. -/
theorem theorem_25_3_differentiableAtFn_iff (hf : ConvexFn f) (hp : Proper f) {x : ℝ}
    (hx : x ∈ interior (dom f)) : DifferentiableAtFn f x ↔ leftDeriv f x = rightDeriv f x :=
  differentiableAtFn_iff_leftDeriv_eq_rightDeriv hf hp hx

/-- **Theorem 25.3**, first assertion: `D` contains all but countably many points of `I`. -/
theorem theorem_25_3_countable (hf : ConvexFn f) (hp : Proper f) :
    {x ∈ interior (dom f) | ¬DifferentiableAtFn f x}.Countable :=
  countable_not_differentiableAtFn hf hp

/-- **Rockafellar, Theorem 25.3**, the parenthesis: `D` is dense in `I`. -/
theorem theorem_25_3_dense (hf : ConvexFn f) (hp : Proper f) :
    interior (dom f) ⊆ closure {z : ℝ | DifferentiableAtFn f z} :=
  subset_closure_differentiableAtFn hf hp

/-- **Theorem 25.3**, second assertion: `f'` is continuous relative to `D` — here in the stronger
form that `rightDeriv f` is continuous at each point of `D` in the ordinary sense. This is the
clause that wants the book's extension of `f` to a closed proper convex function on the line. -/
theorem theorem_25_3_continuousAt (hf : ClosedProperConvexFn f) {x : ℝ}
    (hx : x ∈ interior (dom f)) (hd : DifferentiableAtFn f x) : ContinuousAt (rightDeriv f) x :=
  continuousAt_rightDeriv_of_differentiableAtFn hf hx hd

/-- **Theorem 25.3**, third assertion: `f'` is non-decreasing relative to `D`. Again stronger:
`rightDeriv f` is monotone on the whole line. -/
theorem theorem_25_3_monotone (hf : ConvexFn f) (hp : Proper f) : Monotone (rightDeriv f) :=
  monotone_rightDeriv hf hp

end Theorem253

/-! ### Theorem 25.4 -/

section Theorem254

variable {f : Rn n → EReal} {x : Rn n}

/-- **Theorem 25.4**, first assertion: for proper convex `f` and fixed `y`, the two-sided
directional derivative exists at a point of `int (dom f)` exactly where `x ↦ f'(x; y)` is
continuous. Rockafellar's `y ≠ 0` is not needed — at `y = 0` both sides hold. -/
theorem theorem_25_4_continuousAt_iff (hf : ConvexFn f) (hp : Proper f)
    (hx : x ∈ interior (dom f)) (y : Rn n) :
    ContinuousAt (fun z => dirDeriv f z y) x ↔ dirDeriv f x y = -dirDeriv f x (-y) :=
  continuousAt_dirDeriv_iff hf hp hx y

/-- **Theorem 25.4**, density — **and this clause is general**: restricting `f` to the line through
`x` in the direction `y` turns it into Theorem 25.3. -/
theorem theorem_25_4_dense (hf : ConvexFn f) (hp : Proper f) (y : Rn n) :
    interior (dom f) ⊆
      closure {z ∈ interior (dom f) | dirDeriv f z y = -dirDeriv f z (-y)} :=
  subset_closure_twoSided_dirDeriv hf hp y

/-- **Theorem 25.4**, the measure-zero clause. The implication runs the other way here: Rockafellar
proves this first, by a Fubini argument over lines, and deduces Theorem 25.5; with Rademacher's
theorem available, Theorem 25.5 comes first and this is its consequence. -/
theorem theorem_25_4_measure (hf : ConvexFn f) (hp : Proper f) (y : Rn n) :
    volume (interior (dom f) \ {z | dirDeriv f z y = -dirDeriv f z (-y)}) = 0 :=
  measure_diff_twoSided_dirDeriv hf hp y

end Theorem254

/-! ### Theorem 25.5 and its corollary -/

section Theorem255

variable {f : Rn n → EReal}

/-- **Theorem 25.5**, density: the set of points where a proper convex function is differentiable
is dense in `int (dom f)`. -/
theorem theorem_25_5_dense (hf : ConvexFn f) (hp : Proper f) :
    interior (dom f) ⊆ closure {z : Rn n | DifferentiableAtFn f z} :=
  interior_dom_subset_closure_differentiableAtFn hf hp

/-- **Theorem 25.5**, measure zero: the complement of `D` in `int (dom f)` is null. This is
Rademacher's theorem; convexity contributes only the local Lipschitz constants. -/
theorem theorem_25_5_measure (hf : ConvexFn f) (hp : Proper f) :
    volume (interior (dom f) \ {z : Rn n | DifferentiableAtFn f z}) = 0 :=
  measure_diff_differentiableAtFn hf hp

/-- **Theorem 25.5**, continuity: `x ↦ ∇f(x)` is continuous on `D`. This is Corollary 24.5.1 with
both subdifferentials collapsed to singletons by Theorem 25.1. -/
theorem theorem_25_5_continuousOn (hf : ConvexFn f) (hp : Proper f) :
    ContinuousOn (gradientVec f) {z : Rn n | DifferentiableAtFn f z} :=
  (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.comp_continuousOn
    (continuousOn_fderiv_toReal hf hp)

/-- **Corollary 25.5.1**: a finite convex function differentiable on an open convex set `C` is
*continuously* differentiable on `C`. **The book states this with no proof at all.** The proof here
extends `g` by `+∞` off `C` and applies Theorem 25.5's continuity clause. -/
theorem corollary_25_5_1 {C : Set (Rn n)} {g : Rn n → ℝ} (hC : IsOpen C) (hg : ConvexOn ℝ C g)
    (hd : DifferentiableOn ℝ g C) : ContinuousOn (fderiv ℝ g) C := by
  rcases C.eq_empty_or_nonempty with rfl | hne
  · exact continuousOn_empty _
  · exact continuousOn_fderiv_of_convexOn hC hne hg hd

end Theorem255

/-! ### Theorem 25.6 -/

section Theorem256

variable {f : Rn n → EReal} {x : Rn n}

/-- **Rockafellar's `S(x)`**: the set of limits of sequences of gradients `∇f(xᵢ)` taken at points
of differentiability `xᵢ → x`. This is `gradientLimits` in the surface's vector vocabulary. -/
theorem mem_gradientLimits_iff {v : Rn n} :
    v ∈ gradientLimits f x ↔ ∃ xs vs : ℕ → Rn n, Tendsto xs atTop (𝓝 x) ∧
      (∀ i, HasGradientVecAt f (vs i) (xs i)) ∧ Tendsto vs atTop (𝓝 v) := by
  constructor
  · rintro ⟨xs, vs, h1, h2, h3⟩
    refine ⟨xs, vs, h1, fun i => ?_, h3⟩
    rw [hasGradientVecAt_iff_hasGradientAtFn, linFn_eq_toDual]
    exact h2 i
  · rintro ⟨xs, vs, h1, h2, h3⟩
    refine ⟨xs, vs, h1, fun i => ?_, h3⟩
    have hi := h2 i
    rw [hasGradientVecAt_iff_hasGradientAtFn, linFn_eq_toDual] at hi
    exact hi

/-- For `x` with `∂f(x) ≠ ∅`, the recession cone of `∂f(x)` is the normal cone to `dom f` at `x`.
Rockafellar leaves this as a §23 exercise and says it will be verified inside the proof of Theorem
25.6; **it is not** — that proof uses only `⊆`, and the equality is discharged separately. -/
theorem recessionCone_subdifferential_eq_normalCone (hp : Proper f) {v : Rn n}
    (hv : v ∈ subdifferential (pairing n) f x) :
    recessionCone (subdifferential (pairing n) f x) = normalCone (pairing n) (dom f) x :=
  ConvexAnalysis.recessionCone_subdifferential_eq_normalCone hp hv

/-- **Theorem 25.6**: for a closed proper convex `f` whose `dom f` has non-empty interior,

```
∂f(x) = cl (conv S(x)) + K(x),
```

where `K(x)` is the normal cone to `dom f` at `x` and `S(x)` is `gradientLimits f x`. The book
declares `K(x)` empty off `dom f`, whereas `normalCone` is total; the two readings agree wherever
both sides are non-empty, and off `dom f` the left side is empty, forcing `cl (conv S(x))` to be
empty too. -/
theorem theorem_25_6 (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    (hne : (interior (dom f)).Nonempty) :
    subdifferential (pairing n) f x
      = closure (convexHull ℝ (gradientLimits f x)) + normalCone (pairing n) (dom f) x :=
  subdifferential_eq_closure_convexHull_gradientLimits_add_normalCone hf hp hcl hne

end Theorem256

/-! ### Theorem 25.7 -/

section Theorem257

variable {C : Set (Rn n)} {f : ℕ → Rn n → EReal} {g : Rn n → EReal} {x : Rn n}

/-- **Theorem 25.7**: for `C` open convex and convex `fᵢ`, `g` finite and differentiable on `C`
with `fᵢ → g` pointwise on `C`, one has `∇fᵢ(x) → ∇g(x)` for every `x ∈ C`. For arbitrary
differentiable functions this is false; convexity supplies it through the upper semicontinuity of
`∂f` under pointwise convergence (Theorem 24.5). -/
theorem theorem_25_7 (hC : IsOpen C) (hCc : Convex ℝ C) (hf : ∀ i, ConvexFn (f i))
    (hfp : ∀ i, Proper (f i)) (hfC : ∀ i, C ⊆ dom (f i)) (hg : ConvexFn g) (hgp : Proper g)
    (hgC : C ⊆ dom g) (hconv : ∀ z ∈ C, Tendsto (fun i => f i z) atTop (𝓝 (g z))) (hx : x ∈ C)
    {b : ℕ → Rn n} {b' : Rn n} (hb : ∀ i, HasGradientVecAt (f i) (b i) x)
    (hb' : HasGradientVecAt g b' x) : Tendsto b atTop (𝓝 b') := by
  have h := tendsto_of_hasGradientAtFn hC hCc hf hfp hfC hg hgp hgC hconv hx
    (G := fun i => linFn (b i)) (G' := linFn b') (fun i => hb i) hb'
  have hsymm : ∀ c : Rn n, (InnerProductSpace.toDual ℝ (Rn n)).symm (linFn c) = c := fun c => by
    rw [linFn_eq_toDual, LinearIsometryEquiv.symm_apply_apply]
  have hc : Tendsto (fun i => (InnerProductSpace.toDual ℝ (Rn n)).symm (linFn (b i))) atTop
      (𝓝 ((InnerProductSpace.toDual ℝ (Rn n)).symm (linFn b'))) :=
    ((InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.tendsto _).comp h
  simpa only [hsymm] using hc

/-- **Theorem 25.7**, the sentence after it: `∇fᵢ → ∇g` uniformly on every closed bounded subset of
`C`. "Closed and bounded" is `IsCompact` in `ℝⁿ`. -/
theorem theorem_25_7_uniform (hC : IsOpen C) (hCc : Convex ℝ C) (hf : ∀ i, ConvexFn (f i))
    (hfp : ∀ i, Proper (f i)) (hfC : ∀ i, C ⊆ dom (f i)) (hg : ConvexFn g) (hgp : Proper g)
    (hgC : C ⊆ dom g) (hconv : ∀ z ∈ C, Tendsto (fun i => f i z) atTop (𝓝 (g z)))
    (hfd : ∀ i, ∀ z ∈ C, DifferentiableAtFn (f i) z)
    (hgd : ∀ z ∈ C, DifferentiableAtFn g z) {S : Set (Rn n)} (hS : IsCompact S) (hSC : S ⊆ C) :
    TendstoUniformlyOn (fun i => gradientVec (f i)) (gradientVec g) atTop S := by
  have h := tendstoUniformlyOn_fderiv_toReal hC hCc hf hfp hfC hg hgp hgC hconv hfd hgd hS hSC
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with i hi z hz
  have hdist : dist (gradientVec g z) (gradientVec (f i) z)
      = dist (fderiv ℝ (fun w => (g w).toReal) z) (fderiv ℝ (fun w => (f i w).toReal) z) :=
    (InnerProductSpace.toDual ℝ (Rn n)).symm.dist_map _ _
  rw [hdist]
  exact hi z hz

end Theorem257

end Rockafellar
