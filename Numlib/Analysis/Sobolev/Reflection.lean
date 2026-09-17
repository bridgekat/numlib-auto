/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/Cutoff.lean` and `Numlib/Analysis/Sobolev/Calculus.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Numlib.Analysis.Sobolev.Calculus

/-!
# Extension by reflection

Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, §9.2,
Lemma 9.2: the even reflection `u^⋆` of `u ∈ W^{1,p}(Q₊)` across `x_N = 0` lies in `W^{1,p}(Q)`,
with `‖u^⋆‖ ≤ 2 ‖u‖`; its tangential derivatives are the even reflections of those of `u` and its
normal derivative is the odd reflection. With it, the extension operator for the half space,
the case "`Ω = ℝ^N_+`" of Theorem 9.7, and Corollary 9.8 on the half space.

## Generality

The book proves the lemma on `Q₊` and remarks that the proof is unchanged on `ℝ^N_+`; in
Remark 9 it reflects a square across each of its sides. All of these are one statement, in
general position: `E` a finite-dimensional real inner product space with its Lebesgue measure
`volume`, `v` a unit vector, `σ = hyperplaneReflection v` the reflection across the hyperplane
`v^⊥` (Mathlib's `Submodule.reflection (ℝ ∙ v)ᗮ`), `V` an open set with `σ '' V = V`, and
`V₊ = V ∩ {0 < ⟪x, v⟫}` (`posHalf v V`). The tensor form `HasWeakFDerivOn` makes the tangential
and normal cases one formula: the derivative of `u^⋆` on the reflected half is
`(w ∘ σ) ∘ σ` (`reflectFDeriv v w`), the chain rule for the linear isometry `σ`, which evaluates
to the even reflection of `∂_y u` for `y ⊥ v` and to the odd reflection of `∂_v u` along `v`.

## Main results

* `hyperplaneReflection v`, with `inner_hyperplaneReflection : ⟪σ x, v⟫ = -⟪x, v⟫`, measure
  preservation, and the null hyperplane `volume {⟪x, v⟫ = 0} = 0`;
* `evenReflection v u`, `oddReflection v w`, `reflectFDeriv v w`: the extensions `u^⋆`, `f^□`
  and the reflected tensor derivative;
* `HasWeakFDerivOn.evenReflection`: **Lemma 9.2, the identity**
  `∂(u^⋆) = reflectFDeriv v (∂u)` on `V`, by the book's proof: for a test function `φ` on `V`,
  the cut-offs `η_k(⟪x, v⟫) φ` and `η_k(⟪x, v⟫) (φ ∘ σ)` are test functions on `V₊`; their
  defining identities, in the directions `y` and `σ y`, add up to the identity for `φ` up to a
  term carrying `k η'(k ⟪x, v⟫) (φ − φ ∘ σ)`, which tends to `0` because `φ − φ ∘ σ` vanishes
  on the hyperplane and `u` is integrable near it;
* `MemSobolev.evenReflection`: **Lemma 9.2, membership**, with `eLpNorm (u^⋆) ≤ 2 eLpNorm u`;
* `SobolevMultiIndex.evenReflectionL`, `SobolevEuclidean.evenReflectionL`: the reflection as a
  bounded linear map `W^{1,p}(V₊) → W^{1,p}(V)`;
* `SobolevEuclidean.exists_extensionL_upperHalfSpace`, `IsSobolevExtensionDomain.upperHalfSpace`:
  **Theorem 9.7 for the half space**, and
  `SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_upperHalfSpace`, **Corollary
  9.8 on the half space**.

## References

[brezis2011functional], §9.2, Lemma 9.2 and the sentences after its proof; Remark 9.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology RealInnerProductSpace

noncomputable section

/-! ### The reflection across a hyperplane -/

section HyperplaneReflection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The reflection across the hyperplane `v^⊥`**, `σ x = x - 2 ⟪x, v⟫ v` for a unit vector `v`:
Mathlib's `Submodule.reflection (ℝ ∙ v)ᗮ`, a linear isometry equivalence of `E` fixing `v^⊥` and
sending `v` to `-v`. It is the map `(x', x_N) ↦ (x', -x_N)` of [brezis2011functional] §9.2,
Lemma 9.2, for `v = e_N`. -/
def hyperplaneReflection (v : E) : E ≃ₗᵢ[ℝ] E := Submodule.reflection (ℝ ∙ v)ᗮ

variable (v : E)

/-- The reflection sends `v` to `-v`. -/
@[simp]
theorem hyperplaneReflection_apply_self : hyperplaneReflection v v = -v :=
  Submodule.reflection_orthogonalComplement_singleton_eq_neg v

/-- The reflection is an involution. -/
@[simp]
theorem hyperplaneReflection_hyperplaneReflection (x : E) :
    hyperplaneReflection v (hyperplaneReflection v x) = x :=
  Submodule.reflection_reflection _ x

/-- The reflection reverses the component along `v`. -/
theorem inner_hyperplaneReflection (x : E) : ⟪hyperplaneReflection v x, v⟫ = -⟪x, v⟫ := by
  have h := (hyperplaneReflection v).inner_map_map x v
  rw [hyperplaneReflection_apply_self, inner_neg_right] at h
  linarith

/-- The reflection fixes the hyperplane. -/
theorem hyperplaneReflection_apply_of_inner_eq_zero {x : E} (h : ⟪x, v⟫ = 0) :
    hyperplaneReflection v x = x :=
  Submodule.reflection_mem_subspace_eq_self
    (Submodule.mem_orthogonal_singleton_iff_inner_left.2 h)

/-- The reflection is an involution on sets. -/
theorem hyperplaneReflection_image_image (s : Set E) :
    hyperplaneReflection v '' (hyperplaneReflection v '' s) = s := by
  rw [Set.image_image]
  simp

/-- The preimage under the involution `σ` is the image. -/
theorem preimage_hyperplaneReflection (s : Set E) :
    hyperplaneReflection v ⁻¹' s = hyperplaneReflection v '' s := by
  ext x
  constructor
  · intro hx
    exact ⟨hyperplaneReflection v x, hx, hyperplaneReflection_hyperplaneReflection v x⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The reflection preserves Lebesgue measure. -/
theorem measurePreserving_hyperplaneReflection :
    MeasurePreserving (hyperplaneReflection v) volume volume :=
  (hyperplaneReflection v).measurePreserving

omit [FiniteDimensional ℝ E] in
/-- The reflection is a measurable embedding. -/
theorem measurableEmbedding_hyperplaneReflection :
    MeasurableEmbedding (hyperplaneReflection v) :=
  (hyperplaneReflection v).toHomeomorph.measurableEmbedding

/-- **The hyperplane `v^⊥` is null** for `v ≠ 0`: a proper subspace of `E`. -/
theorem volume_inner_eq_zero {v : E} (hv : v ≠ 0) : volume {x : E | ⟪x, v⟫ = 0} = 0 := by
  have h1 : {x : E | ⟪x, v⟫ = 0} = ((ℝ ∙ v)ᗮ : Set E) := by
    ext x
    exact (Submodule.mem_orthogonal_singleton_iff_inner_left).symm
  have h2 : (ℝ ∙ v)ᗮ ≠ ⊤ := by
    intro h
    have hv' : v ∈ (ℝ ∙ v)ᗮ := by rw [h]; exact Submodule.mem_top
    exact hv (inner_self_eq_zero.1 (Submodule.mem_orthogonal_singleton_iff_inner_left.1 hv'))
  rw [h1]
  exact Measure.addHaar_submodule volume _ h2

/-- Almost every point is off the hyperplane `v^⊥`, for `v ≠ 0`. -/
theorem ae_inner_ne_zero {v : E} (hv : v ≠ 0) : ∀ᵐ x : E, ⟪x, v⟫ ≠ 0 :=
  measure_eq_zero_iff_ae_notMem.1 (volume_inner_eq_zero hv)

end HyperplaneReflection

/-! ### The cut-off `η` in the normal direction -/

section Cutoff

/-- The cut-off `η(t) = smoothTransition (2t − 1)` of the proof of [brezis2011functional]
Lemma 9.2: smooth, `η = 0` on `(−∞, 1/2]`, `η = 1` on `[1, ∞)`, with values in `[0, 1]`. -/
def reflectionCutoff (t : ℝ) : ℝ := Real.smoothTransition (2 * t - 1)

/-- The cut-off `reflectionCutoff` is smooth. -/
theorem contDiff_reflectionCutoff : ContDiff ℝ ∞ reflectionCutoff :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)

/-- `reflectionCutoff t = 0` for `t ≤ 1/2`. -/
theorem reflectionCutoff_of_le_half {t : ℝ} (ht : t ≤ 1 / 2) : reflectionCutoff t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

/-- `reflectionCutoff t = 1` for `t ≥ 1`. -/
theorem reflectionCutoff_of_one_le {t : ℝ} (ht : 1 ≤ t) : reflectionCutoff t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

/-- `reflectionCutoff` is nonnegative. -/
theorem reflectionCutoff_nonneg (t : ℝ) : 0 ≤ reflectionCutoff t :=
  Real.smoothTransition.nonneg _

/-- `reflectionCutoff` is at most `1`. -/
theorem reflectionCutoff_le_one (t : ℝ) : reflectionCutoff t ≤ 1 :=
  Real.smoothTransition.le_one _

/-- `|reflectionCutoff t| ≤ 1`. -/
theorem abs_reflectionCutoff_le_one (t : ℝ) : |reflectionCutoff t| ≤ 1 := by
  rw [abs_of_nonneg (reflectionCutoff_nonneg t)]
  exact reflectionCutoff_le_one t

/-- The derivative of `η` vanishes where `η` is locally constant, `t < 1/2` or `t > 1`. -/
theorem deriv_reflectionCutoff_eq_zero {t : ℝ} (ht : t < 1 / 2 ∨ 1 < t) :
    deriv reflectionCutoff t = 0 := by
  rcases ht with ht | ht
  · have : reflectionCutoff =ᶠ[𝓝 t] fun _ ↦ (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      exact reflectionCutoff_of_le_half (le_of_lt hs)
    rw [this.deriv_eq, deriv_const]
  · have : reflectionCutoff =ᶠ[𝓝 t] fun _ ↦ (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact reflectionCutoff_of_one_le (le_of_lt hs)
    rw [this.deriv_eq, deriv_const]

/-- The derivative of `η` is bounded. -/
theorem exists_abs_deriv_reflectionCutoff_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |deriv reflectionCutoff t| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (contDiff_reflectionCutoff.continuous_deriv (by simp)).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t ↦ ?_⟩
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · exact ((Real.norm_eq_abs _).symm.trans_le (hC t ht)).trans (le_max_left _ _)
  · have : t < 1 / 2 ∨ 1 < t := by
      simp only [mem_Icc, not_and_or, not_le] at ht
      rcases ht with ht | ht
      · exact Or.inl (by linarith)
      · exact Or.inr ht
    rw [deriv_reflectionCutoff_eq_zero this, abs_zero]
    exact le_max_right _ _

end Cutoff

/-! ### The even and odd reflections, and the half sets -/

section Definitions

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Extension by even reflection** across the hyperplane `v^⊥`: `u^⋆ x = u x` if `0 ≤ ⟪x, v⟫`
and `u (σ x)` otherwise. This is `u^⋆` of [brezis2011functional] §9.2, Lemma 9.2, for `v = e_N`;
the value on the hyperplane itself is irrelevant, the hyperplane being null. -/
def evenReflection (v : E) (u : E → F) (x : E) : F :=
  if 0 ≤ ⟪x, v⟫ then u x else u (hyperplaneReflection v x)

/-- **Extension by odd reflection**: `f^□ x = f x` if `0 ≤ ⟪x, v⟫` and `−f (σ x)` otherwise, the
`f^□` of [brezis2011functional] §9.2, proof of Lemma 9.2. -/
def oddReflection [Neg F] (v : E) (f : E → F) (x : E) : F :=
  if 0 ≤ ⟪x, v⟫ then f x else -f (hyperplaneReflection v x)

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The reflected tensor derivative**: `w x` if `0 ≤ ⟪x, v⟫` and `(w (σ x)) ∘ σ` otherwise —
the derivative of `u^⋆` when `w` is the derivative of `u`, by the chain rule for the linear
isometry `σ`. It evaluates to `evenReflection v (w · y)` for `y ⊥ v` and to
`oddReflection v (w · v)` along `v`. -/
def reflectFDeriv (v : E) (w : E → E →L[ℝ] F) (x : E) : E →L[ℝ] F :=
  if 0 ≤ ⟪x, v⟫ then w x
  else (w (hyperplaneReflection v x)).comp
    ((hyperplaneReflection v).toContinuousLinearEquiv : E →L[ℝ] E)

variable (v : E)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- On the half space `⟪x, v⟫ ≥ 0`, the even reflection is the function itself. -/
theorem evenReflection_of_nonneg {u : E → F} {x : E} (hx : 0 ≤ ⟪x, v⟫) :
    evenReflection v u x = u x := by
  simp [evenReflection, hx]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- On the half space `⟪x, v⟫ < 0`, the even reflection is the function at the reflected point. -/
theorem evenReflection_of_neg {u : E → F} {x : E} (hx : ⟪x, v⟫ < 0) :
    evenReflection v u x = u (hyperplaneReflection v x) := by
  simp [evenReflection, not_le.2 hx]

/-- On the half space `⟪x, v⟫ ≥ 0`, `reflectFDeriv v w` is `w`. -/
theorem reflectFDeriv_of_nonneg {w : E → E →L[ℝ] F} {x : E} (hx : 0 ≤ ⟪x, v⟫) :
    reflectFDeriv v w x = w x := by
  simp [reflectFDeriv, hx]

/-- On the half space `⟪x, v⟫ < 0`, `reflectFDeriv v w` is `w ∘ σ` composed with `σ`. -/
theorem reflectFDeriv_of_neg {w : E → E →L[ℝ] F} {x : E} (hx : ⟪x, v⟫ < 0) :
    reflectFDeriv v w x = (w (hyperplaneReflection v x)).comp
      ((hyperplaneReflection v).toContinuousLinearEquiv : E →L[ℝ] E) := by
  simp [reflectFDeriv, not_le.2 hx]

/-- The reflected derivative in a direction `y ⊥ v` is the even reflection of `∂_y u`. -/
theorem reflectFDeriv_apply_of_inner_eq_zero (w : E → E →L[ℝ] F) {y : E} (hy : ⟪y, v⟫ = 0)
    (x : E) : reflectFDeriv v w x y = evenReflection v (fun z ↦ w z y) x := by
  by_cases hx : 0 ≤ ⟪x, v⟫
  · rw [reflectFDeriv_of_nonneg v hx, evenReflection_of_nonneg v hx]
  · rw [reflectFDeriv_of_neg v (not_le.1 hx), evenReflection_of_neg v (not_le.1 hx),
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      hyperplaneReflection_apply_of_inner_eq_zero v hy]

/-- The reflected derivative along `v` is the odd reflection of `∂_v u`. -/
theorem reflectFDeriv_apply_self (w : E → E →L[ℝ] F) (x : E) :
    reflectFDeriv v w x v = oddReflection v (fun z ↦ w z v) x := by
  by_cases hx : 0 ≤ ⟪x, v⟫
  · simp [reflectFDeriv, oddReflection, hx]
  · simp [reflectFDeriv, oddReflection, hx]

/-- The reflected derivative has the norm of the derivative at the reflected point. -/
theorem norm_reflectFDeriv (w : E → E →L[ℝ] F) (x : E) :
    ‖reflectFDeriv v w x‖ = ‖evenReflection v w x‖ := by
  by_cases hx : 0 ≤ ⟪x, v⟫
  · rw [reflectFDeriv_of_nonneg v hx, evenReflection_of_nonneg v hx]
  · rw [reflectFDeriv_of_neg v (not_le.1 hx), evenReflection_of_neg v (not_le.1 hx)]
    exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ _

omit [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The positive half `V₊ = V ∩ {0 < ⟪x, v⟫}`** of an open set, on which the function to be
reflected lives: `Q₊` for `Q` and `v = e_N`, the half space for `V = ⊤`. -/
def posHalf (v : E) (V : Opens E) : Opens E :=
  ⟨(V : Set E) ∩ {x | 0 < ⟪x, v⟫},
    V.isOpen.inter (isOpen_lt continuous_const (continuous_id.inner continuous_const))⟩

/-- The underlying set of `posHalf v V` is `V ∩ {x | 0 < ⟪x, v⟫}`. -/
@[simp]
theorem coe_posHalf (V : Opens E) : (posHalf v V : Set E) = (V : Set E) ∩ {x | 0 < ⟪x, v⟫} :=
  rfl

/-- `posHalf v V ≤ V`. -/
theorem posHalf_le (V : Opens E) : posHalf v V ≤ V := fun _ hx ↦ hx.1

end Definitions

/-! ### Integrals of reflected functions

A function on `V` that agrees with `A` on `{0 ≤ ⟪x, v⟫}` and with `B ∘ σ` on `{⟪x, v⟫ < 0}` has
integral `∫_{V₊} A + ∫_{V₊} B`, the hyperplane being null and `σ` measure preserving. Both
`u^⋆` and `reflectFDeriv v w`, times a test function, have this shape. -/

section Shape

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {v : E} {V : Opens E}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The negative half `V₋ = V ∩ {⟪x, v⟫ < 0}`. -/
theorem isOpen_negHalf : IsOpen ((V : Set E) ∩ {x | ⟪x, v⟫ < 0}) :=
  V.isOpen.inter (isOpen_lt (continuous_id.inner continuous_const) continuous_const)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The positive and negative halves of `V` are disjoint. -/
theorem disjoint_posHalf_negHalf :
    Disjoint (posHalf v V : Set E) ((V : Set E) ∩ {x | ⟪x, v⟫ < 0}) :=
  Set.disjoint_left.2 fun x hx hx' ↦
    (lt_asymm (show (0 : ℝ) < ⟪x, v⟫ from hx.2) (show ⟪x, v⟫ < 0 from hx'.2)).elim

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A set with `σ '' V = V` contains `σ x` with `x`. -/
theorem mem_of_image_eq (hV : hyperplaneReflection v '' (V : Set E) = V) {x : E} :
    x ∈ (V : Set E) ↔ hyperplaneReflection v x ∈ (V : Set E) := by
  constructor
  · intro hx
    rw [← hV]
    exact mem_image_of_mem _ hx
  · intro hx
    have : hyperplaneReflection v (hyperplaneReflection v x)
        ∈ hyperplaneReflection v '' (V : Set E) := mem_image_of_mem _ hx
    rwa [hyperplaneReflection_hyperplaneReflection, hV] at this

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The negative half is the reflection of the positive half. -/
theorem preimage_posHalf (hV : hyperplaneReflection v '' (V : Set E) = V) :
    hyperplaneReflection v ⁻¹' (posHalf v V : Set E) = (V : Set E) ∩ {x | ⟪x, v⟫ < 0} := by
  ext x
  simp only [mem_preimage, coe_posHalf, mem_inter_iff, mem_ofPred_eq, inner_hyperplaneReflection,
    ← mem_of_image_eq hV]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩

/-- Up to the null hyperplane, `V` is the union of its two halves. -/
theorem ae_eq_posHalf_union_negHalf (hv : v ≠ 0) :
    (V : Set E) =ᵐ[volume] (posHalf v V : Set E) ∪ ((V : Set E) ∩ {x | ⟪x, v⟫ < 0}) := by
  filter_upwards [ae_inner_ne_zero hv] with x hx
  simp only [coe_posHalf, mem_union, mem_inter_iff, mem_ofPred_eq, eq_iff_iff]
  constructor
  · intro hxV
    rcases lt_or_gt_of_ne hx with h | h
    · exact Or.inr ⟨hxV, h⟩
    · exact Or.inl ⟨hxV, h⟩
  · rintro (h | h) <;> exact h.1

variable (hv : v ≠ 0) (hV : hyperplaneReflection v '' (V : Set E) = V) {G A B : E → F}
  (hA : ∀ x ∈ (V : Set E), 0 ≤ ⟪x, v⟫ → G x = A x)
  (hB : ∀ x ∈ (V : Set E), ⟪x, v⟫ < 0 → G x = B (hyperplaneReflection v x))
include hv hV hA hB

omit [NormedSpace ℝ F] in
/-- A reflected function is almost everywhere strongly measurable on `V` when its two halves
are on `V₊`. -/
theorem aestronglyMeasurable_of_reflected
    (hAm : AEStronglyMeasurable A (volume.restrict (posHalf v V : Set E)))
    (hBm : AEStronglyMeasurable B (volume.restrict (posHalf v V : Set E))) :
    AEStronglyMeasurable G (volume.restrict (V : Set E)) := by
  have hBσ : AEStronglyMeasurable (B ∘ hyperplaneReflection v)
      (volume.restrict ((V : Set E) ∩ {x | ⟪x, v⟫ < 0})) := by
    rw [← preimage_posHalf hV]
    exact hBm.comp_measurePreserving
      ((measurePreserving_hyperplaneReflection v).restrict_preimage_emb
        (measurableEmbedding_hyperplaneReflection v) _)
  have h1 : AEStronglyMeasurable ((posHalf v V : Set E).indicator A
      + ((V : Set E) ∩ {x | ⟪x, v⟫ < 0}).indicator (B ∘ hyperplaneReflection v)) volume :=
    ((aestronglyMeasurable_indicator_iff (posHalf v V).isOpen.measurableSet).2 hAm).add
      ((aestronglyMeasurable_indicator_iff isOpen_negHalf.measurableSet).2 hBσ)
  refine (h1.mono_measure Measure.restrict_le_self).congr ?_
  filter_upwards [ae_restrict_mem V.isOpen.measurableSet,
    ae_restrict_of_ae (ae_inner_ne_zero hv)] with x hxV hx
  rcases lt_or_gt_of_ne hx with h | h
  · have hxm : x ∈ (V : Set E) ∩ {x | ⟪x, v⟫ < 0} := ⟨hxV, h⟩
    have hxp : x ∉ (posHalf v V : Set E) := fun h' ↦ lt_asymm h (show (0 : ℝ) < ⟪x, v⟫ from h'.2)
    rw [Pi.add_apply, Set.indicator_of_notMem hxp, Set.indicator_of_mem hxm, zero_add, hB x hxV h]
    rfl
  · have hxp : x ∈ (posHalf v V : Set E) := ⟨hxV, h⟩
    have hxm : x ∉ (V : Set E) ∩ {x | ⟪x, v⟫ < 0} := fun h' ↦
      lt_asymm h (show ⟪x, v⟫ < 0 from h'.2)
    rw [Pi.add_apply, Set.indicator_of_mem hxp, Set.indicator_of_notMem hxm, add_zero,
      hA x hxV h.le]

omit [NormedSpace ℝ F] in
/-- **The `L^p` norm of a reflected function** is at most the sum of the `L^p(V₊)` norms of its
two halves, for `1 ≤ p`. -/
theorem eLpNorm_le_of_reflected {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hAm : AEStronglyMeasurable A (volume.restrict (posHalf v V : Set E)))
    (hBm : AEStronglyMeasurable B (volume.restrict (posHalf v V : Set E))) :
    eLpNorm G p (volume.restrict (V : Set E))
      ≤ eLpNorm A p (volume.restrict (posHalf v V : Set E))
        + eLpNorm B p (volume.restrict (posHalf v V : Set E)) := by
  have hBσ : AEStronglyMeasurable (B ∘ hyperplaneReflection v)
      (volume.restrict ((V : Set E) ∩ {x | ⟪x, v⟫ < 0})) := by
    rw [← preimage_posHalf hV]
    exact hBm.comp_measurePreserving
      ((measurePreserving_hyperplaneReflection v).restrict_preimage_emb
        (measurableEmbedding_hyperplaneReflection v) _)
  have hA' := (aestronglyMeasurable_indicator_iff (posHalf v V).isOpen.measurableSet).2 hAm
  have hB' := (aestronglyMeasurable_indicator_iff isOpen_negHalf.measurableSet).2 hBσ
  have heq : G =ᵐ[volume.restrict (V : Set E)] (posHalf v V : Set E).indicator A
      + ((V : Set E) ∩ {x | ⟪x, v⟫ < 0}).indicator (B ∘ hyperplaneReflection v) := by
    filter_upwards [ae_restrict_mem V.isOpen.measurableSet,
      ae_restrict_of_ae (ae_inner_ne_zero hv)] with x hxV hx
    rcases lt_or_gt_of_ne hx with h | h
    · have hxm : x ∈ (V : Set E) ∩ {x | ⟪x, v⟫ < 0} := ⟨hxV, h⟩
      have hxp : x ∉ (posHalf v V : Set E) := fun h' ↦
        lt_asymm h (show (0 : ℝ) < ⟪x, v⟫ from h'.2)
      rw [Pi.add_apply, Set.indicator_of_notMem hxp, Set.indicator_of_mem hxm, zero_add,
        hB x hxV h]
      rfl
    · have hxp : x ∈ (posHalf v V : Set E) := ⟨hxV, h⟩
      have hxm : x ∉ (V : Set E) ∩ {x | ⟪x, v⟫ < 0} := fun h' ↦
        lt_asymm h (show ⟪x, v⟫ < 0 from h'.2)
      rw [Pi.add_apply, Set.indicator_of_mem hxp, Set.indicator_of_notMem hxm, add_zero,
        hA x hxV h.le]
  calc eLpNorm G p (volume.restrict (V : Set E))
      = eLpNorm ((posHalf v V : Set E).indicator A
          + ((V : Set E) ∩ {x | ⟪x, v⟫ < 0}).indicator (B ∘ hyperplaneReflection v)) p
          (volume.restrict (V : Set E)) := eLpNorm_congr_ae heq
    _ ≤ eLpNorm ((posHalf v V : Set E).indicator A) p (volume.restrict (V : Set E))
        + eLpNorm (((V : Set E) ∩ {x | ⟪x, v⟫ < 0}).indicator (B ∘ hyperplaneReflection v)) p
          (volume.restrict (V : Set E)) :=
        eLpNorm_add_le hp
    _ ≤ eLpNorm ((posHalf v V : Set E).indicator A) p volume
        + eLpNorm (((V : Set E) ∩ {x | ⟪x, v⟫ < 0}).indicator (B ∘ hyperplaneReflection v)) p
          volume :=
        add_le_add (eLpNorm_mono_measure _ Measure.restrict_le_self)
          (eLpNorm_mono_measure _ Measure.restrict_le_self)
    _ = eLpNorm A p (volume.restrict (posHalf v V : Set E))
        + eLpNorm B p (volume.restrict (posHalf v V : Set E)) := by
        rw [eLpNorm_indicator_eq_eLpNorm_restrict (posHalf v V).isOpen.measurableSet,
          eLpNorm_indicator_eq_eLpNorm_restrict isOpen_negHalf.measurableSet,
          ← preimage_posHalf hV, eLpNorm_comp_measurePreserving hBm
            ((measurePreserving_hyperplaneReflection v).restrict_preimage_emb
              (measurableEmbedding_hyperplaneReflection v) _)]

/-- **The integral of a reflected function** is `∫_{V₊} A + ∫_{V₊} B`. -/
theorem setIntegral_of_reflected [CompleteSpace F]
    (hAi : IntegrableOn A (posHalf v V : Set E)) (hBi : IntegrableOn B (posHalf v V : Set E)) :
    ∫ x in (V : Set E), G x = (∫ x in (posHalf v V : Set E), A x)
      + ∫ x in (posHalf v V : Set E), B x := by
  have hVm : MeasurableSet ((V : Set E) ∩ {x | ⟪x, v⟫ < 0}) := isOpen_negHalf.measurableSet
  have hVp : MeasurableSet (posHalf v V : Set E) := (posHalf v V).isOpen.measurableSet
  have hGA : EqOn G A (posHalf v V : Set E) := fun x hx ↦ hA x hx.1 hx.2.le
  have hGB : EqOn G (B ∘ hyperplaneReflection v) ((V : Set E) ∩ {x | ⟪x, v⟫ < 0}) :=
    fun x hx ↦ hB x hx.1 hx.2
  have hBσ : IntegrableOn (B ∘ hyperplaneReflection v) ((V : Set E) ∩ {x | ⟪x, v⟫ < 0}) := by
    rw [← preimage_posHalf hV]
    exact (((measurePreserving_hyperplaneReflection v).restrict_preimage_emb
      (measurableEmbedding_hyperplaneReflection v) _).integrable_comp_emb
      (measurableEmbedding_hyperplaneReflection v)).2 hBi
  calc ∫ x in (V : Set E), G x
      = ∫ x in (posHalf v V : Set E) ∪ ((V : Set E) ∩ {x | ⟪x, v⟫ < 0}), G x :=
        setIntegral_congr_set (ae_eq_posHalf_union_negHalf hv)
    _ = (∫ x in (posHalf v V : Set E), G x) + ∫ x in (V : Set E) ∩ {x | ⟪x, v⟫ < 0}, G x :=
        setIntegral_union disjoint_posHalf_negHalf hVm (hAi.congr_fun hGA.symm hVp)
          (hBσ.congr_fun hGB.symm hVm)
    _ = (∫ x in (posHalf v V : Set E), A x)
        + ∫ x in (V : Set E) ∩ {x | ⟪x, v⟫ < 0}, B (hyperplaneReflection v x) := by
        rw [setIntegral_congr_fun hVp hGA, setIntegral_congr_fun hVm hGB]
        rfl
    _ = (∫ x in (posHalf v V : Set E), A x) + ∫ x in (posHalf v V : Set E), B x := by
        rw [← preimage_posHalf hV,
          (measurePreserving_hyperplaneReflection v).setIntegral_preimage_emb
          (measurableEmbedding_hyperplaneReflection v) B _]

end Shape

/-! ### Lemma 9.2: the identity -/

section Identity

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {v : E} {V : Opens E} {p : ℝ≥0∞}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace F] in
/-- A continuous compactly supported function times an `L^p` function on a measurable set,
`1 ≤ p`, is integrable on the set. -/
theorem integrableOn_smul_of_memLp {μ : Measure E} [IsFiniteMeasureOnCompacts μ] {S : Set E}
    (hS : MeasurableSet S) {g : E → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    {f : E → F} (hp : 1 ≤ p) (hf : MemLp f p (μ.restrict S)) :
    IntegrableOn (fun x ↦ g x • f x) S μ := by
  obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hg
  have hgtop : MemLp g ⊤ (μ.restrict S) :=
    memLp_top_of_bound hg.aestronglyMeasurable C (Eventually.of_forall hC)
  have h1 : MemLp (fun x ↦ g x • f x) p (μ.restrict S) := hgtop.smul hf
  refine memLp_one_iff_integrable.1 (h1.mono_exponent_of_measure_support_ne_top
    (s := tsupport g) (fun x hx ↦ by simp [image_eq_zero_of_notMem_tsupport hx]) ?_ hp)
  rw [Measure.restrict_apply' hS]
  exact ((measure_mono inter_subset_left).trans_lt hgc.measure_lt_top).ne

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The derivative of `x ↦ ⟪x, v⟫` is `⟪·, v⟫`. -/
theorem hasFDerivAt_inner_right (v x : E) : HasFDerivAt (fun x ↦ ⟪x, v⟫) (innerSL ℝ v) x := by
  have : (fun x ↦ ⟪x, v⟫) = innerSL ℝ v := funext fun x ↦ by simp [real_inner_comm]
  rw [this]
  exact (innerSL ℝ v).hasFDerivAt

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The derivative of the cut-off `x ↦ η(c ⟪x, v⟫)`. -/
theorem hasFDerivAt_reflectionCutoff_inner (v : E) (c : ℝ) (x : E) :
    HasFDerivAt (fun x ↦ reflectionCutoff (c * ⟪x, v⟫))
      (deriv reflectionCutoff (c * ⟪x, v⟫) • (c • innerSL ℝ v)) x :=
  ((contDiff_reflectionCutoff.differentiable (by simp)) _).hasDerivAt.comp_hasFDerivAt x
    ((hasFDerivAt_inner_right v x).const_mul c)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The derivative of `η(c ⟪x, v⟫) φ(x)` in the direction `y`. -/
theorem fderiv_reflectionCutoff_mul_apply (v : E) {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ) (c : ℝ)
    (x y : E) :
    fderiv ℝ (fun x ↦ reflectionCutoff (c * ⟪x, v⟫) * φ x) x y
      = reflectionCutoff (c * ⟪x, v⟫) * fderiv ℝ φ x y
        + deriv reflectionCutoff (c * ⟪x, v⟫) * c * ⟪y, v⟫ * φ x := by
  have h : HasFDerivAt (fun x ↦ reflectionCutoff (c * ⟪x, v⟫) * φ x)
      (reflectionCutoff (c * ⟪x, v⟫) • fderiv ℝ φ x
        + φ x • (deriv reflectionCutoff (c * ⟪x, v⟫) • (c • innerSL ℝ v))) x :=
    (hasFDerivAt_reflectionCutoff_inner v c x).mul (hφ.differentiable one_ne_zero x).hasFDerivAt
  rw [h.fderiv]
  simp only [add_apply, smul_apply, innerSL_apply_apply, smul_eq_mul, real_inner_comm]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The cut-off `η((n + 1) ⟪x, v⟫)` tends to `1` at every point with `0 < ⟪x, v⟫`. -/
theorem tendsto_reflectionCutoff_mul {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n : ℕ ↦ reflectionCutoff (((n : ℝ) + 1) * t)) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  obtain ⟨N, hN⟩ := exists_nat_ge (1 / t)
  filter_upwards [eventually_ge_atTop N] with n hn
  refine (reflectionCutoff_of_one_le ?_).symm
  have hn' : (1 : ℝ) / t ≤ (n : ℝ) + 1 := hN.trans (by exact_mod_cast (hn.trans (Nat.le_succ n)))
  rwa [div_le_iff₀ ht] at hn'

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Eventually `(n + 1) t > 1` for `t > 0`, so that `η'((n + 1) t) = 0`. -/
theorem eventually_deriv_reflectionCutoff_mul_eq_zero {t : ℝ} (ht : 0 < t) :
    ∀ᶠ n : ℕ in atTop, deriv reflectionCutoff (((n : ℝ) + 1) * t) = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_ge (1 / t)
  filter_upwards [eventually_ge_atTop N] with n hn
  refine deriv_reflectionCutoff_eq_zero (Or.inr ?_)
  have hn' : (1 : ℝ) / t < (n : ℝ) + 1 :=
    hN.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hn)
  rwa [div_lt_iff₀ ht] at hn'

/-- The cut-off `η((n + 1) ⟪x, v⟫) φ` of a test function `φ` on `V` is a test function on
`V₊`: its support lies in `tsupport φ ∩ {1/(2(n+1)) ≤ ⟪x, v⟫}`. -/
def cutoffTestFunction (v : E) (V : Opens E) (φ : 𝓓(V, ℝ)) (n : ℕ) : 𝓓(posHalf v V, ℝ) where
  toFun x := reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) * φ x
  contDiff' := (contDiff_reflectionCutoff.comp
    (contDiff_const.mul (contDiff_id.inner ℝ contDiff_const))).mul φ.contDiff
  hasCompactSupport' := φ.hasCompactSupport.mul_left
  tsupport_subset' := by
    refine subset_inter (tsupport_mul_subset_right.trans φ.tsupport_subset) ?_
    have hcl : IsClosed {x : E | 1 / 2 ≤ ((n : ℝ) + 1) * ⟪x, v⟫} :=
      isClosed_le continuous_const (continuous_const.mul (continuous_id.inner continuous_const))
    refine (closure_minimal ?_ hcl).trans fun x hx ↦ ?_
    · intro x hx
      by_contra h
      apply hx
      change reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) * φ x = 0
      rw [reflectionCutoff_of_le_half (le_of_lt (not_le.1 h)), zero_mul]
    · have hx' : (1 : ℝ) / 2 ≤ ((n : ℝ) + 1) * ⟪x, v⟫ := hx
      by_contra hxv
      have : ((n : ℝ) + 1) * ⟪x, v⟫ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (not_lt.1 hxv)
      linarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The value of `cutoffTestFunction v V φ n` at `x`. -/
theorem cutoffTestFunction_apply (φ : 𝓓(V, ℝ)) (n : ℕ) (x : E) :
    cutoffTestFunction v V φ n x = reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) * φ x :=
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The derivative of `cutoffTestFunction v V φ n` in the direction `y`. -/
theorem fderiv_cutoffTestFunction_apply (φ : 𝓓(V, ℝ)) (n : ℕ) (x y : E) :
    fderiv ℝ (cutoffTestFunction v V φ n) x y
      = reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) * fderiv ℝ φ x y
        + deriv reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) * ((n : ℝ) + 1) * ⟪y, v⟫ * φ x :=
  fderiv_reflectionCutoff_mul_apply v (φ.contDiff.of_le (by simp)) _ x y

/-- The reflected test function `φ ∘ σ` is a test function on `V`. -/
def TestFunction.compHyperplaneReflection (hV : hyperplaneReflection v '' (V : Set E) = V)
    (φ : 𝓓(V, ℝ)) : 𝓓(V, ℝ) where
  toFun x := φ (hyperplaneReflection v x)
  contDiff' := φ.contDiff.comp (hyperplaneReflection v).contDiff
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph (hyperplaneReflection v).toHomeomorph
  tsupport_subset' := by
    have h1 : tsupport (fun x ↦ φ (hyperplaneReflection v x))
        ⊆ hyperplaneReflection v ⁻¹' tsupport φ :=
      closure_minimal (fun x hx ↦ subset_closure hx)
        ((isClosed_tsupport _).preimage (hyperplaneReflection v).continuous)
    refine h1.trans ?_
    rw [preimage_hyperplaneReflection, ← hV]
    exact image_mono φ.tsupport_subset

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The value of `φ.compHyperplaneReflection hV` at `x` is `φ (σ x)`. -/
theorem TestFunction.compHyperplaneReflection_apply (hV : hyperplaneReflection v '' (V : Set E) = V)
    (φ : 𝓓(V, ℝ)) (x : E) :
    TestFunction.compHyperplaneReflection hV φ x = φ (hyperplaneReflection v x) :=
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The chain rule for the reflection: `∂_y (φ ∘ σ)(x) = ∂_{σ y} φ (σ x)`. -/
theorem fderiv_comp_hyperplaneReflection_apply {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ) (x y : E) :
    fderiv ℝ (fun x ↦ φ (hyperplaneReflection v x)) x y
      = fderiv ℝ φ (hyperplaneReflection v x) (hyperplaneReflection v y) := by
  have hσ : HasFDerivAt (hyperplaneReflection v)
      ((hyperplaneReflection v).toContinuousLinearEquiv : E →L[ℝ] E) x :=
    (hyperplaneReflection v).toContinuousLinearEquiv.hasFDerivAt
  have h := (hφ.differentiable one_ne_zero _).hasFDerivAt.comp x hσ
  rw [show (fun x ↦ φ (hyperplaneReflection v x)) = φ ∘ hyperplaneReflection v from rfl, h.fderiv]
  rfl

/-- **Lemma 9.2 (extension by reflection), the identity**: for a unit vector `v`, an open set
`V` with `σ '' V = V`, and `u ∈ W^{1,p}(V₊)` with weak derivative `w`, `1 ≤ p`, the even
reflection `u^⋆` has the weak derivative `reflectFDeriv v w` on `V`.

Proof ([brezis2011functional] §9.2, proof of Lemma 9.2, cases (7) and (8) at once): for a test
function `φ` on `V` and a direction `y`, the cut-offs `θ_n = η_n φ` and `θ'_n = η_n (φ ∘ σ)`,
`η_n(x) = η((n + 1) ⟪x, v⟫)`, are test functions on `V₊`, so the defining identity of `w` holds
for `θ_n` in the direction `y` and for `θ'_n` in the direction `σ y`. Adding the two,
`∫_{V₊} η_n (∂_y φ + (∂_y φ) ∘ σ) u + ∫_{V₊} (n+1) η'_n ⟪y, v⟫ (φ − φ ∘ σ) u
  = −∫_{V₊} η_n (φ w(y) + (φ ∘ σ) w(σ y))`.
As `n → ∞` the first and last integrals converge by dominated convergence (`η_n → 1` off the
null hyperplane, `|η_n| ≤ 1`), and the middle one tends to `0`: `|φ − φ ∘ σ| ≤ M ⟪x, v⟫` by
the mean value theorem, `η'_n` vanishes off `{(n+1) ⟪x, v⟫ ≤ 1}`, so the integrand is bounded by
a fixed multiple of `|u|` on the support and tends to `0` pointwise. The limit identity is the
identity for `φ`, once `∫_V` is split into `∫_{V₊} + ∫_{V₋}` and `V₋` is folded onto `V₊` by
the measure-preserving `σ` (`setIntegral_of_reflected`). -/
theorem HasWeakFDerivOn.evenReflection (hv : ‖v‖ = 1)
    (hV : hyperplaneReflection v '' (V : Set E) = V) (hp : 1 ≤ p) {u : E → F}
    {w : E → E →L[ℝ] F} (hu : HasWeakFDerivOn u w (posHalf v V) volume)
    (hup : MemLp u p (volume.restrict (posHalf v V : Set E)))
    (hwp : MemLp w p (volume.restrict (posHalf v V : Set E))) :
    HasWeakFDerivOn (evenReflection v u) (reflectFDeriv v w) V volume := by
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv
  have hVp : MeasurableSet (posHalf v V : Set E) := (posHalf v V).isOpen.measurableSet
  have hum := hup.aestronglyMeasurable
  have hwm := hwp.aestronglyMeasurable
  obtain ⟨σL, hσL⟩ : ∃ σL : E →L[ℝ] E,
    σL = ((hyperplaneReflection v).toContinuousLinearEquiv : E →L[ℝ] E) := ⟨_, rfl⟩
  have hσL' : ∀ x, σL x = hyperplaneReflection v x := fun x ↦ by rw [hσL]; rfl
  have hwσm : AEStronglyMeasurable (fun z ↦ (w z).comp σL)
      (volume.restrict (posHalf v V : Set E)) :=
    ((ContinuousLinearMap.compL ℝ E E F).flip σL).continuous.comp_aestronglyMeasurable hwm
  have hwσn : ∀ z, ‖(w z).comp σL‖ = ‖w z‖ := fun z ↦ by
    rw [hσL]
    exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ _
  -- the reflected function and derivative lie in `L^p(V)`, hence are locally integrable
  have hurm : AEStronglyMeasurable (_root_.evenReflection v u) (volume.restrict (V : Set E)) :=
    aestronglyMeasurable_of_reflected hv0 hV (fun x _ hx ↦ evenReflection_of_nonneg v hx)
      (fun x _ hx ↦ evenReflection_of_neg v hx) hum hum
  have hurp : MemLp (_root_.evenReflection v u) p (volume.restrict (V : Set E)) := by
    refine (eLpNorm_le_of_reflected hv0 hV (fun x _ hx ↦ evenReflection_of_nonneg v hx)
      (fun x _ hx ↦ evenReflection_of_neg v hx) hp hum hum).trans_lt ?_
    exact ENNReal.add_lt_top.2 ⟨hup, hup⟩
  have hwrB : ∀ x ∈ (V : Set E), ⟪x, v⟫ < 0 →
      reflectFDeriv v w x = (w (hyperplaneReflection v x)).comp σL := by
    intro x _ hx
    rw [reflectFDeriv_of_neg v hx, hσL]
  have hwrp : MemLp (reflectFDeriv v w) p (volume.restrict (V : Set E)) := by
    refine (eLpNorm_le_of_reflected hv0 hV (fun x _ hx ↦ reflectFDeriv_of_nonneg v hx)
      hwrB hp hwm hwσm).trans_lt (ENNReal.add_lt_top.2 ⟨hwp, ?_⟩)
    refine (eLpNorm_mono_ae hwσm (Eventually.of_forall fun z ↦ (hwσn z).le)).trans_lt hwp
  refine hasWeakFDerivOn_iff.2 ⟨hurp.locallyIntegrableOn hp, hwrp.locallyIntegrableOn hp,
    fun φ y ↦ ?_⟩
  -- the reflected test function, and the difference `χ = φ - φ ∘ σ`
  obtain ⟨ψ, hψ⟩ : ∃ ψ : 𝓓(V, ℝ), ψ = TestFunction.compHyperplaneReflection hV φ := ⟨_, rfl⟩
  have hψx : ∀ x, ψ x = φ (hyperplaneReflection v x) := fun x ↦ by rw [hψ]; rfl
  have hψd : ∀ x, fderiv ℝ ψ x (hyperplaneReflection v y)
      = fderiv ℝ φ (hyperplaneReflection v x) y := by
    intro x
    have : (ψ : E → ℝ) = fun x ↦ φ (hyperplaneReflection v x) := funext hψx
    rw [this, fderiv_comp_hyperplaneReflection_apply (φ.contDiff.of_le (by simp)),
      hyperplaneReflection_hyperplaneReflection]
  obtain ⟨χ, hχ⟩ : ∃ χ : E → ℝ, χ = fun x ↦ φ x - φ (hyperplaneReflection v x) := ⟨_, rfl⟩
  have hχs : ContDiff ℝ ∞ χ := by
    rw [hχ]
    exact φ.contDiff.sub (φ.contDiff.comp (hyperplaneReflection v).contDiff)
  have hχc : HasCompactSupport χ := by
    rw [hχ]
    exact φ.hasCompactSupport.sub
      (φ.hasCompactSupport.comp_homeomorph (hyperplaneReflection v).toHomeomorph)
  obtain ⟨Mχ, hMχ⟩ := (hχc.fderiv ℝ).exists_bound_of_continuous (hχs.continuous_fderiv (by simp))
  have hMχ0 : 0 ≤ Mχ := (norm_nonneg _).trans (hMχ 0)
  have hχ_bound : ∀ x, |χ x| ≤ Mχ * |⟪x, v⟫| := by
    intro x
    have hx0 : χ (x - ⟪x, v⟫ • v) = 0 := by
      have h0 : ⟪x - ⟪x, v⟫ • v, v⟫ = 0 := by
        rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hv]
        ring
      rw [hχ]
      simp only
      rw [hyperplaneReflection_apply_of_inner_eq_zero v h0, sub_self]
    have := convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ ↦ (hχs.differentiable (by simp)).differentiableAt) (fun z _ ↦ hMχ z)
      (mem_univ (x - ⟪x, v⟫ • v)) (mem_univ x)
    rw [hx0, sub_zero, sub_sub_cancel, norm_smul, hv, mul_one, Real.norm_eq_abs,
      Real.norm_eq_abs] at this
    exact this
  obtain ⟨Cη, hCη0, hCη⟩ := exists_abs_deriv_reflectionCutoff_le
  -- the cut-off test functions on `V₊`
  obtain ⟨θ, hθ⟩ : ∃ θ : ℕ → 𝓓(posHalf v V, ℝ), θ = cutoffTestFunction v V φ := ⟨_, rfl⟩
  obtain ⟨θ', hθ'⟩ : ∃ θ' : ℕ → 𝓓(posHalf v V, ℝ), θ' = cutoffTestFunction v V ψ := ⟨_, rfl⟩
  have hθx : ∀ n x, θ n x = reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) * φ x := fun (n : ℕ) x ↦ by
    rw [hθ]; rfl
  have hθ'x : ∀ n x, θ' n x = reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫)
      * φ (hyperplaneReflection v x) := fun (n : ℕ) x ↦ by
    rw [hθ', cutoffTestFunction_apply, hψx]
  have hθd : ∀ n x, fderiv ℝ (θ n) x y
      = reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) * fderiv ℝ φ x y
        + deriv reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) * ((n : ℝ) + 1) * ⟪y, v⟫ * φ x :=
    fun n x ↦ by rw [hθ]; exact fderiv_cutoffTestFunction_apply φ n x y
  have hθ'd : ∀ n x, fderiv ℝ (θ' n) x (hyperplaneReflection v y)
      = reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) * fderiv ℝ φ (hyperplaneReflection v x) y
        - deriv reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) * ((n : ℝ) + 1) * ⟪y, v⟫
          * φ (hyperplaneReflection v x) := by
    intro n x
    rw [hθ', fderiv_cutoffTestFunction_apply ψ n x, hψd, inner_hyperplaneReflection, hψx]
    ring
  -- the identities of the weak derivative on `V₊` for the two cut-offs
  have hu' : HasWeakIteratedFDerivOn 1 u
      (fun x ↦ (continuousMultilinearCurryFin1 ℝ E F).symm (w x)) (posHalf v V) volume := hu
  have I1 : ∀ n : ℕ, ∫ x in (posHalf v V : Set E), fderiv ℝ (θ n) x y • u x
      = -∫ x in (posHalf v V : Set E), θ n x • w x y := fun n : ℕ ↦
    hu.integral_smul_eq (θ n) y
  have I2 : ∀ n : ℕ,
      ∫ x in (posHalf v V : Set E), fderiv ℝ (θ' n) x (hyperplaneReflection v y) • u x
      = -∫ x in (posHalf v V : Set E), θ' n x • w x (hyperplaneReflection v y) := fun n : ℕ ↦
    hu.integral_smul_eq (θ' n) (hyperplaneReflection v y)
  -- the three pieces and their limits
  obtain ⟨a, ha⟩ : ∃ a : E → ℝ,
    a = fun x ↦ fderiv ℝ φ x y + fderiv ℝ φ (hyperplaneReflection v x) y := ⟨_, rfl⟩
  have hac : Continuous a := by
    rw [ha]
    exact (φ.fderivApply y).contDiff.continuous.add
      ((φ.fderivApply y).contDiff.continuous.comp (hyperplaneReflection v).continuous)
  have hacs : HasCompactSupport a := by
    rw [ha]
    exact (φ.fderivApply y).hasCompactSupport.add
      ((φ.fderivApply y).hasCompactSupport.comp_homeomorph (hyperplaneReflection v).toHomeomorph)
  obtain ⟨b, hb⟩ : ∃ b : E → F, b = fun x ↦
    φ x • w x y + φ (hyperplaneReflection v x) • w x (hyperplaneReflection v y) := ⟨_, rfl⟩
  have hwy : ∀ z : E, MemLp (fun x ↦ w x z) p (volume.restrict (posHalf v V : Set E)) := fun z ↦
    (ContinuousLinearMap.apply ℝ F z).comp_memLp' hwp
  have hbi : IntegrableOn b (posHalf v V : Set E) := by
    rw [hb]
    exact (integrableOn_smul_of_memLp hVp φ.contDiff.continuous φ.hasCompactSupport hp
      (hwy y)).add (integrableOn_smul_of_memLp hVp
        (φ.contDiff.continuous.comp (hyperplaneReflection v).continuous)
        (φ.hasCompactSupport.comp_homeomorph (hyperplaneReflection v).toHomeomorph) hp (hwy _))
  have hai : IntegrableOn (fun x ↦ a x • u x) (posHalf v V : Set E) :=
    integrableOn_smul_of_memLp hVp hac hacs hp hup
  obtain ⟨e, he⟩ : ∃ e : ℕ → E → ℝ, e = fun (n : ℕ) (x : E) ↦
    deriv reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) * ((n : ℝ) + 1) * ⟪y, v⟫ * χ x := ⟨_, rfl⟩
  have hec : ∀ n : ℕ, Continuous (e n) := fun n : ℕ ↦ by
    rw [he]
    exact (((contDiff_reflectionCutoff.continuous_deriv (by simp)).comp
      (continuous_const.mul (continuous_id.inner continuous_const))).mul continuous_const).mul
      continuous_const |>.mul hχs.continuous
  have hecs : ∀ n : ℕ, HasCompactSupport (e n) := fun n : ℕ ↦ by
    rw [he]
    exact hχc.mul_left
  have hηc : ∀ n : ℕ, Continuous fun x ↦ reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) := fun n : ℕ ↦
    contDiff_reflectionCutoff.continuous.comp
      (continuous_const.mul (continuous_id.inner continuous_const))
  -- the algebraic identity `L_n + X_n = -R_n`
  have hLX : ∀ n : ℕ, (∫ x in (posHalf v V : Set E),
        (reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) * a x) • u x)
      + ∫ x in (posHalf v V : Set E), e n x • u x
      = -∫ x in (posHalf v V : Set E), reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) • b x := by
    intro n
    have i1 : IntegrableOn (fun x ↦ fderiv ℝ (θ n) x y • u x) (posHalf v V : Set E) :=
      integrableOn_smul_of_memLp hVp ((θ n).fderivApply y).contDiff.continuous
        ((θ n).fderivApply y).hasCompactSupport hp hup
    have i2 : IntegrableOn (fun x ↦ fderiv ℝ (θ' n) x (hyperplaneReflection v y) • u x)
        (posHalf v V : Set E) :=
      integrableOn_smul_of_memLp hVp ((θ' n).fderivApply _).contDiff.continuous
        ((θ' n).fderivApply _).hasCompactSupport hp hup
    have j1 : IntegrableOn (fun x ↦ θ n x • w x y) (posHalf v V : Set E) :=
      integrableOn_smul_of_memLp hVp (θ n).contDiff.continuous (θ n).hasCompactSupport hp (hwy y)
    have j2 : IntegrableOn (fun x ↦ θ' n x • w x (hyperplaneReflection v y))
        (posHalf v V : Set E) :=
      integrableOn_smul_of_memLp hVp (θ' n).contDiff.continuous (θ' n).hasCompactSupport hp
        (hwy _)
    have hL : (∫ x in (posHalf v V : Set E),
          (reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) * a x) • u x)
        + ∫ x in (posHalf v V : Set E), e n x • u x
        = (∫ x in (posHalf v V : Set E), fderiv ℝ (θ n) x y • u x)
          + ∫ x in (posHalf v V : Set E), fderiv ℝ (θ' n) x (hyperplaneReflection v y) • u x := by
      rw [← integral_add i1 i2]
      have hia : IntegrableOn (fun x ↦ (reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) * a x) • u x)
          (posHalf v V : Set E) :=
        integrableOn_smul_of_memLp hVp ((hηc n).mul hac) hacs.mul_left hp hup
      have hie : IntegrableOn (fun x ↦ e n x • u x) (posHalf v V : Set E) :=
        integrableOn_smul_of_memLp hVp (hec n) (hecs n) hp hup
      rw [← integral_add hia hie]
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      simp only
      rw [hθd, hθ'd, ha, he, hχ, ← add_smul, ← add_smul]
      congr 1
      simp only
      ring
    have hR : -∫ x in (posHalf v V : Set E), reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) • b x
        = -(∫ x in (posHalf v V : Set E), θ n x • w x y)
          + -∫ x in (posHalf v V : Set E), θ' n x • w x (hyperplaneReflection v y) := by
      rw [← neg_add, ← integral_add j1 j2]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      simp only
      rw [hθx, hθ'x, hb, smul_add, mul_smul, mul_smul]
    rw [hL, hR, I1, I2]
  -- the limits
  have hsplitL : Tendsto (fun n : ℕ ↦ ∫ x in (posHalf v V : Set E),
      (reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) * a x) • u x) atTop
      (𝓝 (∫ x in (posHalf v V : Set E), a x • u x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x ↦ ‖a x • u x‖)
      (fun n : ℕ ↦ ((hηc n).mul hac).aestronglyMeasurable.smul hum) hai.norm
      (fun n : ℕ ↦ Eventually.of_forall fun x ↦ ?_) ?_
    · rw [norm_smul, norm_smul, norm_mul, Real.norm_eq_abs (reflectionCutoff _)]
      calc |reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫)| * ‖a x‖ * ‖u x‖
          ≤ 1 * ‖a x‖ * ‖u x‖ := by gcongr; exact abs_reflectionCutoff_le_one _
        _ = ‖a x‖ * ‖u x‖ := by rw [one_mul]
    · filter_upwards [ae_restrict_mem hVp] with x hx
      have := ((tendsto_reflectionCutoff_mul (show (0 : ℝ) < ⟪x, v⟫ from hx.2)).mul_const
        (a x)).smul_const (u x)
      simpa using this
  have hsplitX : Tendsto (fun n : ℕ ↦ ∫ x in (posHalf v V : Set E), e n x • u x) atTop (𝓝 0) := by
    have hKint : IntegrableOn ((tsupport χ).indicator u) (posHalf v V : Set E) := by
      rw [IntegrableOn, integrable_indicator_iff (isClosed_tsupport χ).measurableSet,
        IntegrableOn, Measure.restrict_restrict (isClosed_tsupport χ).measurableSet]
      have : IsFiniteMeasure (volume.restrict (tsupport χ ∩ (posHalf v V : Set E))) :=
        isFiniteMeasure_restrict.2 ((measure_mono inter_subset_left).trans_lt
          hχc.measure_lt_top).ne
      exact (hup.mono_measure (Measure.restrict_mono inter_subset_right le_rfl)).integrable hp
    have h0 : (0 : F) = ∫ x in (posHalf v V : Set E), (0 : F) := by simp
    rw [h0]
    refine tendsto_integral_of_dominated_convergence
      (fun x ↦ (Cη * Mχ * |⟪y, v⟫|) * ‖(tsupport χ).indicator u x‖)
      (fun n : ℕ ↦ (hec n).aestronglyMeasurable.smul hum) (hKint.norm.const_mul _)
      (fun n : ℕ ↦ Eventually.of_forall fun x ↦ ?_) ?_
    · rw [norm_smul, Real.norm_eq_abs]
      by_cases hxχ : x ∈ tsupport χ
      · rw [Set.indicator_of_mem hxχ]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [he]
        simp only
        by_cases hx1 : 1 < ((n : ℝ) + 1) * ⟪x, v⟫
        · rw [deriv_reflectionCutoff_eq_zero (Or.inr hx1), zero_mul, zero_mul, zero_mul, abs_zero]
          positivity
        · rw [abs_mul, abs_mul, abs_mul]
          rcases le_or_gt ⟪x, v⟫ 0 with hxv | hxv
          · have : ((n : ℝ) + 1) * ⟪x, v⟫ ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos (by positivity) hxv
            have hηz : deriv reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) = 0 :=
              deriv_reflectionCutoff_eq_zero (Or.inl (by linarith))
            rw [hηz, abs_zero, zero_mul, zero_mul, zero_mul]
            positivity
          · calc |deriv reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫)| * |(n : ℝ) + 1| * |⟪y, v⟫|
                  * |χ x|
                ≤ Cη * |(n : ℝ) + 1| * |⟪y, v⟫| * (Mχ * |⟪x, v⟫|) := by
                  gcongr
                  · exact hCη _
                  · exact hχ_bound x
              _ = Cη * Mχ * |⟪y, v⟫| * (((n : ℝ) + 1) * ⟪x, v⟫) := by
                  rw [abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1), abs_of_pos hxv]; ring
              _ ≤ Cη * Mχ * |⟪y, v⟫| * 1 := by
                  gcongr
                  exact not_lt.1 hx1
              _ = Cη * Mχ * |⟪y, v⟫| := mul_one _
      · have hχ0 : χ x = 0 := image_eq_zero_of_notMem_tsupport hxχ
        rw [he]
        simp only
        rw [hχ0, mul_zero, abs_zero, zero_mul]
        positivity
    · filter_upwards [ae_restrict_mem hVp] with x hx
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_deriv_reflectionCutoff_mul_eq_zero
        (show (0 : ℝ) < ⟪x, v⟫ from hx.2)] with n hn
      rw [he]
      simp only
      rw [hn, zero_mul, zero_mul, zero_mul, zero_smul]
  have hsplitR : Tendsto (fun n : ℕ ↦ ∫ x in (posHalf v V : Set E),
      reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) • b x) atTop
      (𝓝 (∫ x in (posHalf v V : Set E), b x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x ↦ ‖b x‖)
      (fun n : ℕ ↦ (hηc n).aestronglyMeasurable.smul hbi.aestronglyMeasurable) hbi.norm
      (fun n : ℕ ↦ Eventually.of_forall fun x ↦ ?_) ?_
    · rw [norm_smul, Real.norm_eq_abs]
      calc |reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫)| * ‖b x‖ ≤ 1 * ‖b x‖ := by
            gcongr; exact abs_reflectionCutoff_le_one _
        _ = ‖b x‖ := one_mul _
    · filter_upwards [ae_restrict_mem hVp] with x hx
      have := (tendsto_reflectionCutoff_mul (show (0 : ℝ) < ⟪x, v⟫ from hx.2)).smul_const (b x)
      simpa using this
  -- the limit identity on `V₊`
  have hlim : (∫ x in (posHalf v V : Set E), a x • u x)
      = -∫ x in (posHalf v V : Set E), b x := by
    have h1 := hsplitL.add hsplitX
    rw [add_zero] at h1
    have h2 : Tendsto (fun n : ℕ ↦ (∫ x in (posHalf v V : Set E),
        (reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) * a x) • u x)
        + ∫ x in (posHalf v V : Set E), e n x • u x) atTop
        (𝓝 (-∫ x in (posHalf v V : Set E), b x)) := by
      simp only [hLX]
      exact hsplitR.neg
    exact tendsto_nhds_unique h1 h2
  -- fold the integrals over `V` onto `V₊`
  have hmain : ∀ x, ⟪x, v⟫ < 0 → hyperplaneReflection v (hyperplaneReflection v x) = x :=
    fun x _ ↦ hyperplaneReflection_hyperplaneReflection v x
  have hd1 : IntegrableOn (fun x ↦ fderiv ℝ φ x y • u x) (posHalf v V : Set E) :=
    integrableOn_smul_of_memLp hVp (g := fun x ↦ fderiv ℝ φ x y)
      (φ.fderivApply y).contDiff.continuous (φ.fderivApply y).hasCompactSupport hp hup
  have hd2 : IntegrableOn (fun x ↦ fderiv ℝ φ (hyperplaneReflection v x) y • u x)
      (posHalf v V : Set E) :=
    integrableOn_smul_of_memLp hVp (g := fun x ↦ fderiv ℝ φ (hyperplaneReflection v x) y)
      ((φ.fderivApply y).contDiff.continuous.comp (hyperplaneReflection v).continuous)
      ((φ.fderivApply y).hasCompactSupport.comp_homeomorph
        (hyperplaneReflection v).toHomeomorph) hp hup
  have hIL : ∫ x in (V : Set E), fderiv ℝ φ x y • _root_.evenReflection v u x
      = ∫ x in (posHalf v V : Set E), a x • u x := by
    rw [setIntegral_of_reflected hv0 hV (G := fun x ↦ fderiv ℝ φ x y • _root_.evenReflection v u x)
      (A := fun x ↦ fderiv ℝ φ x y • u x)
      (B := fun z ↦ fderiv ℝ φ (hyperplaneReflection v z) y • u z)
      (fun x _ hx ↦ by rw [evenReflection_of_nonneg v hx])
      (fun x _ hx ↦ by rw [evenReflection_of_neg v hx, hmain x hx]) hd1 hd2, ← integral_add hd1 hd2]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only
    rw [ha, ← add_smul]
  have he1 : IntegrableOn (fun x ↦ φ x • w x y) (posHalf v V : Set E) :=
    integrableOn_smul_of_memLp hVp φ.contDiff.continuous φ.hasCompactSupport hp (hwy y)
  have he2 : IntegrableOn (fun x ↦ φ (hyperplaneReflection v x) • w x (hyperplaneReflection v y))
      (posHalf v V : Set E) :=
    integrableOn_smul_of_memLp hVp (g := fun x ↦ φ (hyperplaneReflection v x))
      (φ.contDiff.continuous.comp (hyperplaneReflection v).continuous)
      (φ.hasCompactSupport.comp_homeomorph (hyperplaneReflection v).toHomeomorph) hp (hwy _)
  have hIR : ∫ x in (V : Set E), φ x • reflectFDeriv v w x y
      = ∫ x in (posHalf v V : Set E), b x := by
    rw [setIntegral_of_reflected hv0 hV (G := fun x ↦ φ x • reflectFDeriv v w x y)
      (A := fun x ↦ φ x • w x y)
      (B := fun z ↦ φ (hyperplaneReflection v z) • w z (hyperplaneReflection v y))
      (fun x _ hx ↦ by rw [reflectFDeriv_of_nonneg v hx])
      (fun x _ hx ↦ by
        rw [reflectFDeriv_of_neg v hx, hmain x hx, ContinuousLinearMap.comp_apply]
        rfl) he1 he2, ← integral_add he1 he2]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only
    rw [hb]
  rw [hIL, hIR, hlim]

end Identity

/-! ### Lemma 9.2: membership and norms -/

section Membership

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {v : E} {V : Opens E} {p : ℝ≥0∞}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedSpace ℝ F] in
/-- The even reflection is additive. -/
theorem evenReflection_add (v : E) (f g : E → F) :
    evenReflection v (f + g) = evenReflection v f + evenReflection v g := by
  funext x
  simp only [evenReflection, Pi.add_apply]
  split_ifs <;> rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The even reflection commutes with scalar multiplication. -/
theorem evenReflection_smul (v : E) (c : ℝ) (f : E → F) :
    evenReflection v (c • f) = c • evenReflection v f := by
  funext x
  simp only [evenReflection, Pi.smul_apply]
  split_ifs <;> rfl

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- The even reflection only sees the function up to a null set of `V₊`. -/
theorem evenReflection_congr_ae (hv : v ≠ 0) (hV : hyperplaneReflection v '' (V : Set E) = V)
    {f g : E → F} (h : f =ᵐ[volume.restrict (posHalf v V : Set E)] g) :
    evenReflection v f =ᵐ[volume.restrict (V : Set E)] evenReflection v g := by
  have h1 : ∀ᵐ x ∂volume, x ∈ (posHalf v V : Set E) → f x = g x :=
    (ae_restrict_iff' (posHalf v V).isOpen.measurableSet).1 h
  have h2 : ∀ᵐ x ∂volume, hyperplaneReflection v x ∈ (posHalf v V : Set E) →
      f (hyperplaneReflection v x) = g (hyperplaneReflection v x) :=
    (measurePreserving_hyperplaneReflection v).quasiMeasurePreserving.tendsto_ae.eventually h1
  filter_upwards [ae_restrict_mem V.isOpen.measurableSet, ae_restrict_of_ae (ae_inner_ne_zero hv),
    ae_restrict_of_ae h1, ae_restrict_of_ae h2] with x hxV hx hx1 hx2
  rcases lt_or_gt_of_ne hx with h | h
  · rw [evenReflection_of_neg v h, evenReflection_of_neg v h]
    refine hx2 ⟨(mem_of_image_eq hV).1 hxV, ?_⟩
    change (0 : ℝ) < ⟪hyperplaneReflection v x, v⟫
    rw [inner_hyperplaneReflection]
    linarith
  · rw [evenReflection_of_nonneg v h.le, evenReflection_of_nonneg v h.le]
    exact hx1 ⟨hxV, h⟩

omit [NormedSpace ℝ F] in
/-- **The `L^p` bound of Lemma 9.2**: `‖u^⋆‖_{L^p(V)} ≤ 2 ‖u‖_{L^p(V₊)}` for `1 ≤ p`. -/
theorem eLpNorm_evenReflection_le (hv : v ≠ 0) (hV : hyperplaneReflection v '' (V : Set E) = V)
    (hp : 1 ≤ p) {u : E → F} (hu : AEStronglyMeasurable u (volume.restrict (posHalf v V : Set E))) :
    eLpNorm (evenReflection v u) p (volume.restrict (V : Set E))
      ≤ 2 * eLpNorm u p (volume.restrict (posHalf v V : Set E)) := by
  rw [two_mul]
  exact eLpNorm_le_of_reflected hv hV (fun x _ hx ↦ evenReflection_of_nonneg v hx)
    (fun x _ hx ↦ evenReflection_of_neg v hx) hp hu hu

omit [NormedSpace ℝ F] in
/-- The even reflection of a measurable function is measurable. -/
theorem aestronglyMeasurable_evenReflection (hv : v ≠ 0)
    (hV : hyperplaneReflection v '' (V : Set E) = V) {u : E → F}
    (hu : AEStronglyMeasurable u (volume.restrict (posHalf v V : Set E))) :
    AEStronglyMeasurable (evenReflection v u) (volume.restrict (V : Set E)) :=
  aestronglyMeasurable_of_reflected hv hV (fun _ _ hx ↦ evenReflection_of_nonneg v hx)
    (fun _ _ hx ↦ evenReflection_of_neg v hx) hu hu

omit [NormedSpace ℝ F] in
/-- `L^p` membership of the even reflection. -/
theorem MeasureTheory.MemLp.evenReflection (hv : v ≠ 0)
    (hV : hyperplaneReflection v '' (V : Set E) = V)
    (hp : 1 ≤ p) {u : E → F} (hu : MemLp u p (volume.restrict (posHalf v V : Set E))) :
    MemLp (evenReflection v u) p (volume.restrict (V : Set E)) :=
  (eLpNorm_evenReflection_le hv hV hp hu.aestronglyMeasurable).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofNat_lt_top hu)

/-- The reflected derivative has the norm of the even reflection of the derivative, so its `L^p`
norm is at most `2 ‖w‖_{L^p(V₊)}`. -/
theorem eLpNorm_reflectFDeriv_le (hv : v ≠ 0) (hV : hyperplaneReflection v '' (V : Set E) = V)
    (hp : 1 ≤ p) {w : E → E →L[ℝ] F}
    (hw : AEStronglyMeasurable w (volume.restrict (posHalf v V : Set E))) :
    eLpNorm (reflectFDeriv v w) p (volume.restrict (V : Set E))
      ≤ 2 * eLpNorm w p (volume.restrict (posHalf v V : Set E)) := by
  have hwσ : AEStronglyMeasurable
      (fun z ↦ (w z).comp ((hyperplaneReflection v).toContinuousLinearEquiv : E →L[ℝ] E))
      (volume.restrict (posHalf v V : Set E)) :=
    ((ContinuousLinearMap.compL ℝ E E F).flip _).continuous.comp_aestronglyMeasurable hw
  rw [two_mul]
  refine (eLpNorm_le_of_reflected hv hV (fun x _ hx ↦ reflectFDeriv_of_nonneg v hx)
    (fun x _ hx ↦ reflectFDeriv_of_neg v hx) hp hw hwσ).trans ?_
  gcongr
  exact eLpNorm_mono_ae hwσ (Eventually.of_forall fun z ↦
    (ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ _).le)

variable [CompleteSpace F]

/-- **Lemma 9.2, membership**: for a unit vector `v`, an open `V` with `σ '' V = V`, and
`u ∈ W^{1,p}(V₊)`, `1 ≤ p ≤ ∞`, the even reflection `u^⋆` lies in `W^{1,p}(V)`, with
`‖u^⋆‖_{L^p(V)} ≤ 2 ‖u‖_{L^p(V₊)}` (`eLpNorm_evenReflection_le`) and the derivative bound
`eLpNorm_reflectFDeriv_le` ([brezis2011functional] Lemma 9.2). -/
theorem MemSobolev.evenReflection (hv : ‖v‖ = 1)
    (hV : hyperplaneReflection v '' (V : Set E) = V) (hp : 1 ≤ p) {u : E → F}
    (hu : MemSobolev u 1 p (posHalf v V) volume) :
    MemSobolev (evenReflection v u) 1 p V volume := by
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv
  obtain ⟨w, hw, hwp⟩ := hu.exists_hasWeakIteratedFDerivOn (n := 1) le_rfl
  obtain ⟨e, he⟩ : ∃ e : (E [×1]→L[ℝ] F) ≃ₗᵢ[ℝ] (E →L[ℝ] F),
    e = continuousMultilinearCurryFin1 ℝ E F := ⟨_, rfl⟩
  have hw' : HasWeakFDerivOn u (fun x ↦ e (w x)) (posHalf v V) volume := by
    unfold HasWeakFDerivOn
    rw [he]
    simpa using hw
  have hwp' : MemLp (fun x ↦ e (w x)) p (volume.restrict (posHalf v V : Set E)) :=
    e.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp' hwp
  have hid := hw'.evenReflection hv hV hp hu.memLp hwp'
  have hup : MemLp (_root_.evenReflection v u) p (volume.restrict (V : Set E)) :=
    hu.memLp.evenReflection hv0 hV hp
  have hWp : MemLp (reflectFDeriv v fun x ↦ e (w x)) p (volume.restrict (V : Set E)) :=
    (eLpNorm_reflectFDeriv_le hv0 hV hp hwp'.aestronglyMeasurable).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofNat_lt_top hwp')
  refine ⟨hup, fun n hn ↦ ?_⟩
  have hn' : n ≤ 1 := by exact_mod_cast hn
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn' with rfl | rfl
  · exact ⟨_, hasWeakIteratedFDerivOn_zero hid.locallyIntegrableOn,
      (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap
        |>.comp_memLp' hup⟩
  · exact ⟨_, hid,
      (continuousMultilinearCurryFin1 ℝ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap
        |>.comp_memLp' hWp⟩

end Membership

/-! ### Lemma 9.2 on the typed spaces -/

section Typed

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {v : E} {V : Opens E}

/-- Lemma 9.2 in the multi-index formulation. -/
theorem MemSobolevMultiIndex.evenReflection (hv : ‖v‖ = 1)
    (hV : hyperplaneReflection v '' (V : Set E) = V) {u : E → F}
    (hu : MemSobolevMultiIndex b u 1 p (posHalf v V) volume) :
    MemSobolevMultiIndex b (evenReflection v u) 1 p V volume :=
  (hu.memSobolev.evenReflection hv hV Fact.out).memSobolevMultiIndex

namespace SobolevMultiIndex

variable (hv : ‖v‖ = 1) (hV : hyperplaneReflection v '' (V : Set E) = V)
include hv hV

/-- **The extension by reflection of Lemma 9.2 on the typed spaces**, as a function: the element
of `W^{1,p}(V)` whose function is `u^⋆`. It is linear and bounded;
`SobolevMultiIndex.evenReflectionL` is its bundled form. -/
def evenReflection (u : SobolevMultiIndex F b 1 p (posHalf v V) volume) :
    SobolevMultiIndex F b 1 p V volume :=
  ((memSobolevMultiIndex u).evenReflection hv hV).exists_sobolevMultiIndex.choose

/-- The function of `SobolevMultiIndex.evenReflection hv hV u` is `u^⋆`. -/
theorem fn_evenReflection (u : SobolevMultiIndex F b 1 p (posHalf v V) volume) :
    fn (evenReflection hv hV u) =ᵐ[volume.restrict (V : Set E)] _root_.evenReflection v (fn u) :=
  ((memSobolevMultiIndex u).evenReflection hv hV).exists_sobolevMultiIndex.choose_spec

/-- On `V₊`, the reflected element is `u`. -/
theorem fn_evenReflection_restrict (u : SobolevMultiIndex F b 1 p (posHalf v V) volume) :
    fn (evenReflection hv hV u) =ᵐ[volume.restrict (posHalf v V : Set E)] fn u := by
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (posHalf_le v V) (fn_evenReflection hv hV u),
    ae_restrict_mem (posHalf v V).isOpen.measurableSet] with x hx hxV
  rw [hx, evenReflection_of_nonneg v (le_of_lt (show (0 : ℝ) < ⟪x, v⟫ from hxV.2))]

/-- The reflection is additive. -/
theorem evenReflection_add (u w : SobolevMultiIndex F b 1 p (posHalf v V) volume) :
    evenReflection hv hV (u + w) = evenReflection hv hV u + evenReflection hv hV w := by
  refine ext_of_fn_ae_eq ((fn_evenReflection hv hV (u + w)).trans (EventuallyEq.trans ?_
    (fn_add _ _).symm))
  refine (evenReflection_congr_ae (ne_zero_of_norm_ne_zero (by rw [hv]; exact one_ne_zero)) hV
    (fn_add u w)).trans ?_
  rw [_root_.evenReflection_add]
  exact ((fn_evenReflection hv hV u).add (fn_evenReflection hv hV w)).symm

/-- The reflection commutes with scalar multiplication. -/
theorem evenReflection_smul (c : ℝ) (u : SobolevMultiIndex F b 1 p (posHalf v V) volume) :
    evenReflection hv hV (c • u) = c • evenReflection hv hV u := by
  refine ext_of_fn_ae_eq ((fn_evenReflection hv hV (c • u)).trans (EventuallyEq.trans ?_
    (fn_smul _ _).symm))
  refine (evenReflection_congr_ae (ne_zero_of_norm_ne_zero (by rw [hv]; exact one_ne_zero)) hV
    (fn_smul c u)).trans ?_
  rw [_root_.evenReflection_smul]
  exact ((fn_evenReflection hv hV u).const_smul c).symm

/-- **The `L^p` bound of the typed reflection**: `‖u^⋆‖_{L^p(V)} ≤ 2 ‖u‖_{L^p(V₊)}`. -/
theorem eLpNorm_fn_evenReflection_le (u : SobolevMultiIndex F b 1 p (posHalf v V) volume) :
    eLpNorm (fn (evenReflection hv hV u)) p (volume.restrict (V : Set E))
      ≤ 2 * eLpNorm (fn u) p (volume.restrict (posHalf v V : Set E)) := by
  rw [eLpNorm_congr_ae (fn_evenReflection hv hV u)]
  exact eLpNorm_evenReflection_le (ne_zero_of_norm_ne_zero (by rw [hv]; exact one_ne_zero)) hV
    Fact.out
    (memLp u).aestronglyMeasurable

/-- The partial derivatives of the reflected element, in terms of a tensor derivative `w` of
`u`: `∂ᵢ (u^⋆) = (reflectFDeriv v w) (bᵢ)` almost everywhere on `V`. -/
theorem weakDeriv_evenReflection_single (u : SobolevMultiIndex F b 1 p (posHalf v V) volume)
    {w : E → E →L[ℝ] F} (hw : HasWeakFDerivOn (fn u) w (posHalf v V) volume)
    (hwp : MemLp w p (volume.restrict (posHalf v V : Set E))) (i : ι) :
    weakDeriv (evenReflection hv hV u) (MultiIndexLE.single i) =ᵐ[volume.restrict (V : Set E)]
      fun x ↦ reflectFDeriv v w x (b i) := by
  have h1 := (hasWeakIteratedLineDerivOn (evenReflection hv hV u) (MultiIndexLE.single i)).of_perm
    (multiIndexTuple_single_perm (b : ι → E) i)
  have h2 := (((hw.evenReflection hv hV Fact.out (memLp u) hwp) :
    HasWeakIteratedFDerivOn 1 _ _ V volume).lineDeriv ![b i]).congr_ae
    (fn_evenReflection hv hV u).symm (EventuallyEq.refl _ _)
  filter_upwards [(ae_restrict_iff' V.isOpen.measurableSet).2 (h1.ae_eq h2)] with x hx
  simpa using hx

/-- **The typed reflection is bounded**: `‖u^⋆‖ ≤ C ‖u‖` for a constant depending on the
basis only. -/
theorem exists_norm_evenReflection_le :
    ∃ C : ℝ, ∀ u : SobolevMultiIndex F b 1 p (posHalf v V) volume,
      ‖evenReflection hv hV u‖ ≤ C * ‖u‖ := by
  have hv0 : v ≠ 0 := ne_zero_of_norm_ne_zero (by rw [hv]; exact one_ne_zero)
  obtain ⟨Cb, hCb⟩ : ∃ Cb : ℝ, Cb = Fintype.card ι • ‖b.equivFunL.toContinuousLinearMap‖ :=
    ⟨_, rfl⟩
  have hCb0 : 0 ≤ Cb := by rw [hCb]; positivity
  obtain ⟨Mb, hMb⟩ : ∃ Mb : ℝ, Mb = ∑ i, ‖b i‖ := ⟨_, rfl⟩
  have hMb0 : 0 ≤ Mb := by rw [hMb]; positivity
  obtain ⟨B, hB⟩ : ∃ B : ℝ≥0∞, B = ENNReal.ofReal Mb * (2 * ENNReal.ofReal Cb) := ⟨_, rfl⟩
  have hB' : B ≠ ⊤ := by
    rw [hB]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top)
  refine ⟨_, fun u ↦ norm_le_mul_norm_of_eLpNorm_le (evenReflection hv hV u) u
    ENNReal.ofNat_ne_top hB' (eLpNorm_fn_evenReflection_le hv hV u) fun i ↦ ?_⟩
  obtain ⟨w, hw, hwp, -, hwn⟩ := exists_hasWeakFDerivOn_fn u
  rw [← hCb] at hwn
  have h1 : eLpNorm (weakDeriv (evenReflection hv hV u) (MultiIndexLE.single i)) p
      (volume.restrict (V : Set E))
      ≤ ENNReal.ofReal Mb * eLpNorm (reflectFDeriv v w) p (volume.restrict (V : Set E)) := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Lp.memLp _).aestronglyMeasurable ?_ p
    filter_upwards [weakDeriv_evenReflection_single hv hV u hw hwp i] with x hx
    rw [hx, hMb]
    calc ‖reflectFDeriv v w x (b i)‖ ≤ ‖reflectFDeriv v w x‖ * ‖b i‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖reflectFDeriv v w x‖ * ∑ j, ‖b j‖ := by
          gcongr
          exact Finset.single_le_sum (f := fun j ↦ ‖b j‖) (fun _ _ ↦ norm_nonneg _)
            (Finset.mem_univ i)
      _ = (∑ j, ‖b j‖) * ‖reflectFDeriv v w x‖ := mul_comm _ _
  calc eLpNorm (weakDeriv (evenReflection hv hV u) (MultiIndexLE.single i)) p
        (volume.restrict (V : Set E))
      ≤ ENNReal.ofReal Mb * (2 * (ENNReal.ofReal Cb
        * ∑ j, eLpNorm (weakDeriv u (MultiIndexLE.single j)) p
          (volume.restrict (posHalf v V : Set E)))) := by
        refine h1.trans ?_
        gcongr
        exact (eLpNorm_reflectFDeriv_le hv0 hV Fact.out hwp.aestronglyMeasurable).trans
          (by gcongr)
    _ = B * ∑ j, eLpNorm (weakDeriv u (MultiIndexLE.single j)) p
          (volume.restrict (posHalf v V : Set E)) := by
        rw [hB]; ring

variable (F b p) in
/-- The reflection as a linear map `W^{1,p}(V₊) → W^{1,p}(V)`. -/
def evenReflectionₗ :
    SobolevMultiIndex F b 1 p (posHalf v V) volume →ₗ[ℝ] SobolevMultiIndex F b 1 p V volume where
  toFun := evenReflection hv hV
  map_add' := evenReflection_add hv hV
  map_smul' := evenReflection_smul hv hV

variable (F b p) in
/-- **Lemma 9.2 as a bounded linear map `W^{1,p}(V₊) → W^{1,p}(V)`**, `u ↦ u^⋆`, for a unit
vector `v` and an open `V` with `σ '' V = V` ([brezis2011functional] Lemma 9.2): its function is
`u^⋆` (`SobolevMultiIndex.fn_evenReflectionL`), it restricts to `u` on `V₊`
(`SobolevMultiIndex.fn_evenReflectionL_restrict`), and its `L^p` norm is at most `2 ‖u‖_{L^p(V₊)}`
(`SobolevMultiIndex.eLpNorm_fn_evenReflectionL_le`). With `V = Q` and `v = e_N` it is the step
`v_i ↦ v_i^⋆` of the proof of the extension theorem; with `V = ⊤` it is the extension operator of
the half space. -/
def evenReflectionL :
    SobolevMultiIndex F b 1 p (posHalf v V) volume →L[ℝ] SobolevMultiIndex F b 1 p V volume :=
  (evenReflectionₗ F b p hv hV).mkContinuousOfExistsBound (exists_norm_evenReflection_le hv hV)

/-- `SobolevMultiIndex.evenReflectionL` is `SobolevMultiIndex.evenReflection`. -/
@[simp]
theorem evenReflectionL_apply (u : SobolevMultiIndex F b 1 p (posHalf v V) volume) :
    evenReflectionL F b p hv hV u = evenReflection hv hV u :=
  rfl

/-- The function of `SobolevMultiIndex.evenReflectionL hv hV u` is `u^⋆`. -/
theorem fn_evenReflectionL (u : SobolevMultiIndex F b 1 p (posHalf v V) volume) :
    fn (evenReflectionL F b p hv hV u) =ᵐ[volume.restrict (V : Set E)]
      _root_.evenReflection v (fn u) :=
  fn_evenReflection hv hV u

/-- On `V₊`, `SobolevMultiIndex.evenReflectionL hv hV u` is `u`. -/
theorem fn_evenReflectionL_restrict (u : SobolevMultiIndex F b 1 p (posHalf v V) volume) :
    fn (evenReflectionL F b p hv hV u) =ᵐ[volume.restrict (posHalf v V : Set E)] fn u :=
  fn_evenReflection_restrict hv hV u

/-- The `L^p` bound on `SobolevMultiIndex.evenReflectionL`. -/
theorem eLpNorm_fn_evenReflectionL_le (u : SobolevMultiIndex F b 1 p (posHalf v V) volume) :
    eLpNorm (fn (evenReflectionL F b p hv hV u)) p (volume.restrict (V : Set E))
      ≤ 2 * eLpNorm (fn u) p (volume.restrict (posHalf v V : Set E)) :=
  eLpNorm_fn_evenReflection_le hv hV u

end SobolevMultiIndex

end Typed

section Euclidean

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {v : EuclideanSpace ℝ (Fin N)}
  {V : Opens (EuclideanSpace ℝ (Fin N))}

/-- **Lemma 9.2 on `W^{1,p}` of an open subset of `ℝ^N`**, as a bounded linear map
`W^{1,p}(V₊) → W^{1,p}(V)`, `u ↦ u^⋆`, for `‖v‖ = 1` and `σ '' V = V`:
`SobolevMultiIndex.evenReflectionL` on `SobolevEuclidean N 1 p V₊`, with
`SobolevMultiIndex.fn_evenReflectionL`, `SobolevMultiIndex.fn_evenReflectionL_restrict` and
`SobolevMultiIndex.eLpNorm_fn_evenReflectionL_le` for its function, its restriction to `V₊` and
its `L^p` bound. With `V = Q` and `v = e_N` it is the step `v_i ↦ v_i^⋆` of the proof of
Theorem 9.7; with `V = ℝ^N` it is the extension operator of the half space. -/
noncomputable abbrev SobolevEuclidean.evenReflectionL (hv : ‖v‖ = 1)
    (hV : hyperplaneReflection v '' (V : Set (EuclideanSpace ℝ (Fin N))) = V) :
    SobolevEuclidean N 1 p (posHalf v V) →L[ℝ] SobolevEuclidean N 1 p V :=
  SobolevMultiIndex.evenReflectionL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis p hv hV

end Euclidean

/-! ### The half space: Theorem 9.7 and Corollary 9.8 for `Ω = ℝ^N_+` -/

section HalfSpace

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

open EuclideanSpace

/-- The last basis vector of `ℝ^{d+1}` is a unit vector. -/
theorem EuclideanSpace.norm_single_last_one :
    ‖(single (Fin.last d) (1 : ℝ) : EuclideanSpace ℝ (Fin (d + 1)))‖ = 1 := by
  simp

/-- The inner product with the last basis vector is the last coordinate. -/
theorem EuclideanSpace.inner_single_last_one (x : EuclideanSpace ℝ (Fin (d + 1))) :
    ⟪x, single (Fin.last d) (1 : ℝ)⟫ = x (Fin.last d) := by
  rw [EuclideanSpace.inner_single_right]
  simp

/-- The whole space is invariant under every reflection. -/
theorem hyperplaneReflection_image_top {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : E) : hyperplaneReflection v '' ((⊤ : Opens E) : Set E) = ((⊤ : Opens E) : Set E) := by
  rw [Opens.coe_top, Set.image_univ, (hyperplaneReflection v).surjective.range_eq]

/-- The positive half of the whole space for `v = e_N` is the upper half space. -/
theorem coe_posHalf_top_eq_upperHalfSpace :
    (posHalf (single (Fin.last d) (1 : ℝ)) (⊤ : Opens (EuclideanSpace ℝ (Fin (d + 1)))) :
      Set (EuclideanSpace ℝ (Fin (d + 1)))) = upperHalfSpace d := by
  ext x
  simp [coe_posHalf, upperHalfSpace, EuclideanSpace.inner_single_last_one]

/-- The positive half of the whole space for `v = e_N` is the upper half space, as opens. -/
theorem posHalf_top_eq_upperHalfSpaceOpens :
    posHalf (single (Fin.last d) (1 : ℝ)) (⊤ : Opens (EuclideanSpace ℝ (Fin (d + 1))))
      = upperHalfSpaceOpens d :=
  Opens.ext coe_posHalf_top_eq_upperHalfSpace

/-- An almost-everywhere equality for `μ.restrict s` is one for `μ.restrict t` when `s = t`;
stated over plain functions so that rewriting never touches a dependent type. -/
theorem Filter.EventuallyEq.of_restrict_eq {α β : Type*} [MeasurableSpace α] {μ : Measure α}
    {s t : Set α} {f g : α → β} (h : f =ᵐ[μ.restrict s] g) (hst : s = t) : f =ᵐ[μ.restrict t] g :=
  hst ▸ h

/-- `eLpNorm` for `μ.restrict s` and `μ.restrict t` agree when `s = t`; stated over plain
functions so that rewriting never touches a dependent type. -/
theorem eLpNorm_restrict_congr_set_eq {α β : Type*} [MeasurableSpace α] [NormedAddCommGroup β]
    {μ : Measure α} {s t : Set α} (f : α → β) (p : ℝ≥0∞) (hst : s = t) :
    eLpNorm f p (μ.restrict s) = eLpNorm f p (μ.restrict t) :=
  hst ▸ rfl

/-- The assembly of the half-space extension operator from a restriction `R` and a reflection
`T`, with the operators as variables: the elaboration of the composite is expensive when the
operators are concrete, cheap when they are not. -/
theorem SobolevEuclidean.exists_extensionL_upperHalfSpace_of_ops
    {V : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hset : (V : Set (EuclideanSpace ℝ (Fin (d + 1)))) = upperHalfSpace d)
    (R : SobolevEuclidean (d + 1) 1 p (upperHalfSpaceOpens d) →L[ℝ] SobolevEuclidean (d + 1) 1 p V)
    (T : SobolevEuclidean (d + 1) 1 p V →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤)
    (P : SobolevEuclidean (d + 1) 1 p (upperHalfSpaceOpens d) →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤)
    (hP : ∀ u, P u = T (R u))
    (hRfn : ∀ u, SobolevMultiIndex.fn (R u) =ᵐ[volume.restrict (V : Set _)] SobolevMultiIndex.fn u)
    (hTfn : ∀ w, SobolevMultiIndex.fn (T w) =ᵐ[volume.restrict (V : Set _)] SobolevMultiIndex.fn w)
    (hTLp : ∀ w, eLpNorm (SobolevMultiIndex.fn (T w)) p
      (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (d + 1)))) : Set _))
      ≤ 2 * eLpNorm (SobolevMultiIndex.fn w) p (volume.restrict (V : Set _))) :
    ∃ C : ℝ, ∀ u : SobolevEuclidean (d + 1) 1 p (upperHalfSpaceOpens d),
      SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (upperHalfSpace d)] SobolevMultiIndex.fn u ∧
      eLpNorm (SobolevMultiIndex.fn (P u)) p volume
        ≤ ENNReal.ofReal C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (upperHalfSpace d))
      ∧ ‖P u‖ ≤ C * ‖u‖ := by
  refine ⟨max 2 ‖P‖, fun u ↦ ⟨?_, ?_, ?_⟩⟩
  · rw [hP u]
    exact ((hTfn (R u)).trans (hRfn u)).of_restrict_eq hset
  · rw [hP u]
    calc eLpNorm (SobolevMultiIndex.fn (T (R u))) p volume
        = eLpNorm (SobolevMultiIndex.fn (T (R u))) p
          (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (d + 1)))) : Set _)) :=
          (eLpNorm_restrict_coe_top _ _).symm
      _ ≤ 2 * eLpNorm (SobolevMultiIndex.fn (R u)) p (volume.restrict (V : Set _)) := hTLp (R u)
      _ = 2 * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (V : Set _)) := by
          rw [eLpNorm_congr_ae (hRfn u)]
      _ = 2 * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (upperHalfSpace d)) := by
          rw [eLpNorm_restrict_congr_set_eq _ _ hset]
      _ ≤ ENNReal.ofReal (max 2 ‖P‖)
          * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (upperHalfSpace d)) := by
          gcongr
          exact (ENNReal.ofReal_ofNat 2).symm.le.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  · exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

/-- Theorem 9.7 for the half space, for any unit vector `v` whose positive half of the whole
space is the upper half space: the statement of `SobolevEuclidean.exists_extensionL_upperHalfSpace`
with `v` a variable. -/
theorem SobolevEuclidean.exists_extensionL_of_posHalf_top_eq {v : EuclideanSpace ℝ (Fin (d + 1))}
    (hv : ‖v‖ = 1)
    (hset : (posHalf v (⊤ : Opens (EuclideanSpace ℝ (Fin (d + 1)))) :
      Set (EuclideanSpace ℝ (Fin (d + 1)))) = upperHalfSpace d) :
    ∃ (P : SobolevEuclidean (d + 1) 1 p (upperHalfSpaceOpens d) →L[ℝ]
        SobolevEuclidean (d + 1) 1 p ⊤) (C : ℝ),
      ∀ u : SobolevEuclidean (d + 1) 1 p (upperHalfSpaceOpens d),
        SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (upperHalfSpace d)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume
          ≤ ENNReal.ofReal C
            * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (upperHalfSpace d))
        ∧ ‖P u‖ ≤ C * ‖u‖ := by
  have hV := hyperplaneReflection_image_top v
  have hle : posHalf v ⊤ ≤ upperHalfSpaceOpens d := by
    intro x hx
    rw [← SetLike.mem_coe, coe_upperHalfSpaceOpens, ← hset]
    exact hx
  exact ⟨SobolevEuclidean.evenReflectionL hv hV ∘L
      SobolevMultiIndex.restrictL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 p
        volume hle,
    SobolevEuclidean.exists_extensionL_upperHalfSpace_of_ops hset
    (SobolevMultiIndex.restrictL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 p volume
      hle) (SobolevEuclidean.evenReflectionL hv hV) _ (fun u ↦ rfl)
    (fun u ↦ SobolevMultiIndex.fn_restrictL _ _)
    (fun w ↦ SobolevMultiIndex.fn_evenReflectionL_restrict hv hV w)
    (fun w ↦ SobolevMultiIndex.eLpNorm_fn_evenReflectionL_le hv hV w)⟩

/-- **Theorem 9.7 for the half space** ([brezis2011functional] §9.2, "This establishes Theorem
9.7 for `Ω = ℝ^N_+`"): for `1 ≤ p ≤ ∞` there are a bounded linear extension operator
`P : W^{1,p}(ℝ^N_+) → W^{1,p}(ℝ^N)` and a constant `C` with `P u = u` on `ℝ^N_+`,
`‖P u‖_{L^p(ℝ^N)} ≤ C ‖u‖_{L^p(ℝ^N_+)}` and `‖P u‖_{W^{1,p}(ℝ^N)} ≤ C ‖u‖_{W^{1,p}(ℝ^N_+)}` —
namely the even reflection `SobolevEuclidean.evenReflectionL` across `x_N = 0` with `V = ℝ^N`,
whose `L^p` constant is `2`. The statement has the shape of the extension theorem of
`Numlib/Analysis/Sobolev/Extension.lean` for a `C^1` domain, so that the two cases are consumed
uniformly. -/
theorem SobolevEuclidean.exists_extensionL_upperHalfSpace :
    ∃ (P : SobolevEuclidean (d + 1) 1 p (upperHalfSpaceOpens d) →L[ℝ]
        SobolevEuclidean (d + 1) 1 p ⊤) (C : ℝ),
      ∀ u : SobolevEuclidean (d + 1) 1 p (upperHalfSpaceOpens d),
        SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (upperHalfSpace d)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume
          ≤ ENNReal.ofReal C
            * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (upperHalfSpace d))
        ∧ ‖P u‖ ≤ C * ‖u‖ :=
  SobolevEuclidean.exists_extensionL_of_posHalf_top_eq EuclideanSpace.norm_single_last_one
    coe_posHalf_top_eq_upperHalfSpace

/-- **The half space is a `W^{1,p}`-extension domain**, for every `1 ≤ p ≤ ∞`: the predicate of
`Numlib/Analysis/Sobolev/Cutoff.lean` instantiated by
`SobolevEuclidean.exists_extensionL_upperHalfSpace`. It is what lets the embedding and
compactness theorems on a domain be read on `ℝ^N_+` without the general extension theorem. -/
theorem IsSobolevExtensionDomain.upperHalfSpace :
    IsSobolevExtensionDomain (d + 1) p (upperHalfSpaceOpens d) := by
  obtain ⟨P, C, hP⟩ := SobolevEuclidean.exists_extensionL_upperHalfSpace (d := d) (p := p)
  exact ⟨P.comp (Submodule.subtypeL _), fun u ↦ (hP u).1⟩

/-- **Corollary 9.8 on the half space**: for `1 ≤ p < ∞`, every `u ∈ W^{1,p}(ℝ^N_+)` is the
limit in `W^{1,p}(ℝ^N_+)` of restrictions of `C_c^∞(ℝ^N)` functions — the abstract density
`SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_hasSobolevExtensionOn` applied
to the reflection extension ([brezis2011functional] Corollary 9.8, the case `Ω = ℝ^N_+`). -/
theorem SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_upperHalfSpace (hp' : p ≠ ⊤)
    (u : SobolevEuclidean (d + 1) 1 p (upperHalfSpaceOpens d)) :
    ∃ v : ℕ → EuclideanSpace ℝ (Fin (d + 1)) → ℝ, (∀ n, ContDiff ℝ ∞ (v n)) ∧
      (∀ n, HasCompactSupport (v n)) ∧
        ∃ w : ℕ → SobolevEuclidean (d + 1) 1 p (upperHalfSpaceOpens d),
        (∀ n, SobolevMultiIndex.fn (w n) =ᵐ[volume.restrict (upperHalfSpace d)] v n) ∧
        Tendsto w atTop (𝓝 u) :=
  SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_hasSobolevExtensionOn hp'
    IsSobolevExtensionDomain.upperHalfSpace ⟨u, Submodule.mem_top⟩

end HalfSpace
