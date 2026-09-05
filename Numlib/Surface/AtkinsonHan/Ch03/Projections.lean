import Numlib.Backbone
import Numlib.Surface.AtkinsonHan.Ch03.BestApprox
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Atkinson–Han §3.6: projection operators

Statements from Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework* (3rd ed.), §3.6.

## Book-specific definitions

* `IsDirectSum` — Definition 3.6.1, with `isDirectSum_iff_isCompl` identifying it with Mathlib's
  `IsCompl`.
* `IsProjectionOperator` — Definition 3.6.3 for Banach spaces: a bounded idempotent. This is
  definitionally `IsIdempotentElem`, which is the form all the backbone lemmas take.
* `IsOrthogonalProjectionOperator` — Definition 3.6.3 / (3.6.2) for Hilbert spaces, with
  `isOrthogonalProjectionOperator_iff` identifying it with Mathlib's
  `LinearMap.IsSymmetricProjection`.

## Main results

* `prop_3_6_2` — direct sums correspond to idempotent linear maps.
* `IsOrthogonalDirectSum` — the orthogonal direct sum of Definition 3.6.1.
* `example_3_6_7` — `∑ᵢ (·, φᵢ) φᵢ` is an orthogonal projection for an orthonormal family.
* `prop_3_6_9_a` … `prop_3_6_9_e` — the properties of orthogonal projections;
  `prop_3_6_9_c'` restates (c) as an orthogonal direct sum.
* `exercise_3_6_1`, `exercise_3_6_7` — `I − P` is a projection; `‖P‖ ≥ 1` for `P ≠ 0`.

## Not formalized here

Example 3.6.5 (Lagrange interpolation), Example 3.6.6 (piecewise linear interpolation) and
Example 3.6.8 (Fourier projection) need interpolation and trigonometric projection operators on
`C[a, b]` and `C_p(2π)`; these are phase-3 backbone items. Example 3.6.4 is a picture in `ℝ²`.
-/

namespace AtkinsonHan.Ch03

/-! ### Definition 3.6.1 and Proposition 3.6.2: direct sums -/

section DirectSum

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **Direct sum** `V = V₁ ⊕ V₂` (Definition 3.6.1): every `v` decomposes uniquely as
`v = v₁ + v₂` with `vᵢ ∈ Vᵢ`. -/
def IsDirectSum (V₁ V₂ : Submodule 𝕜 V) : Prop :=
  ∀ v : V, ∃! p : V × V, p.1 ∈ V₁ ∧ p.2 ∈ V₂ ∧ v = p.1 + p.2

/-- The book's direct sum is Mathlib's `IsCompl`. -/
theorem isDirectSum_iff_isCompl (V₁ V₂ : Submodule 𝕜 V) : IsDirectSum V₁ V₂ ↔ IsCompl V₁ V₂ := by
  constructor
  · intro h
    rw [isCompl_iff]
    refine ⟨?_, ?_⟩
    · rw [disjoint_iff_inf_le]
      intro x hx
      obtain ⟨p, -, huniq⟩ := h x
      have e₁ : ((x, 0) : V × V) = p := huniq _ ⟨hx.1, V₂.zero_mem, by simp⟩
      have e₂ : ((0, x) : V × V) = p := huniq _ ⟨V₁.zero_mem, hx.2, by simp⟩
      have hxx : ((x, 0) : V × V) = ((0, x) : V × V) := e₁.trans e₂.symm
      simpa using (Prod.ext_iff.1 hxx).1
    · rw [codisjoint_iff_le_sup]
      intro x _
      obtain ⟨p, ⟨hp₁, hp₂, hp₃⟩, -⟩ := h x
      rw [hp₃]
      exact Submodule.add_mem_sup hp₁ hp₂
  · intro h v
    obtain ⟨u₁, u₂, hsum, huniq⟩ := Submodule.existsUnique_add_of_isCompl h v
    refine ⟨((u₁ : V), (u₂ : V)), ⟨u₁.2, u₂.2, hsum.symm⟩, ?_⟩
    rintro ⟨w₁, w₂⟩ ⟨hw₁, hw₂, hw⟩
    obtain ⟨e₁, e₂⟩ := huniq ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ hw.symm
    exact Prod.ext (congrArg Subtype.val e₁) (congrArg Subtype.val e₂)

/-- **Proposition 3.6.2.** `V = V₁ ⊕ V₂` if and only if there is an idempotent linear map `P` with
range `V₁` and with `I − P` of range `V₂`; then `v₁ = P v` and `v₂ = (I − P) v`. -/
theorem prop_3_6_2 (V₁ V₂ : Submodule 𝕜 V) :
    IsDirectSum V₁ V₂ ↔ ∃ P : V →ₗ[𝕜] V, P ∘ₗ P = P ∧ LinearMap.range P = V₁ ∧
      LinearMap.range (LinearMap.id - P) = V₂ := by
  rw [isDirectSum_iff_isCompl]
  constructor
  · intro h
    have hidem : IsIdempotentElem (V₁.projection V₂ h) := Submodule.isIdempotentElem_projection h
    refine ⟨V₁.projection V₂ h, hidem, Submodule.range_projection h, ?_⟩
    rw [← LinearMap.IsIdempotentElem.ker_eq_range hidem]
    exact Submodule.ker_projection h
  · rintro ⟨P, hP, hr, hk⟩
    have hidem : IsIdempotentElem P := hP
    have hc : IsCompl (LinearMap.range P) (LinearMap.ker P) :=
      LinearMap.IsProj.isCompl (LinearMap.IsIdempotentElem.isProj_range P hidem)
    rwa [hr, LinearMap.IsIdempotentElem.ker_eq_range hidem, hk] at hc

/-- **Orthogonal direct sum** (Definition 3.6.1 for inner product spaces): a direct sum whose two
summands are mutually orthogonal. -/
def IsOrthogonalDirectSum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (V₁ V₂ : Submodule 𝕜 H) : Prop :=
  IsDirectSum V₁ V₂ ∧ V₁ ⟂ V₂

/-- **Projection operator** (Definition 3.6.3): a bounded linear `P` on a Banach space with
`P² = P`. This is definitionally Mathlib's `IsIdempotentElem`, which is the form the backbone's
projector lemmas take. -/
def IsProjectionOperator [CompleteSpace V] (P : V →L[𝕜] V) : Prop := IsIdempotentElem P

/-- Definition 3.6.3 is Mathlib's `IsIdempotentElem`, definitionally. -/
theorem isProjectionOperator_iff [CompleteSpace V] (P : V →L[𝕜] V) :
    IsProjectionOperator P ↔ IsIdempotentElem P := Iff.rfl

/-- **Exercise 3.6.1.** `I − P` is a projection whenever `P` is, and the two swap range and
kernel. -/
theorem exercise_3_6_1 {P : V →L[𝕜] V} (hP : IsIdempotentElem P) :
    IsIdempotentElem ((1 : V →L[𝕜] V) - P) ∧
      LinearMap.ker (P : V →ₗ[𝕜] V) = LinearMap.range (1 - (P : V →ₗ[𝕜] V)) ∧
      LinearMap.range (P : V →ₗ[𝕜] V) = LinearMap.ker (1 - (P : V →ₗ[𝕜] V)) := by
  have hlin : IsIdempotentElem (P : V →ₗ[𝕜] V) :=
    ContinuousLinearMap.IsIdempotentElem.toLinearMap hP
  exact ⟨IsIdempotentElem.one_sub hP, LinearMap.IsIdempotentElem.ker_eq_range_one_sub hlin,
    LinearMap.IsIdempotentElem.range_eq_ker_one_sub hlin⟩

/-- **Exercise 3.6.7.** A nonzero bounded projection has norm at least one. -/
theorem exercise_3_6_7 (P : V →L[𝕜] V) (hP : IsIdempotentElem P) (h0 : P ≠ 0) : 1 ≤ ‖P‖ :=
  one_le_norm_of_isIdempotentElem hP h0

end DirectSum

/-! ### Definition 3.6.3 and Proposition 3.6.9: orthogonal projections -/

section Hilbert

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- **Orthogonal projection operator** (Definition 3.6.3 / (3.6.2)): a bounded projection `P`
with `(P v, (I − P) w) = 0` for all `v, w`. -/
def IsOrthogonalProjectionOperator (P : H →L[𝕜] H) : Prop :=
  IsIdempotentElem P ∧ ∀ v w : H, inner 𝕜 (P v) (((1 : H →L[𝕜] H) - P) w) = 0

/-- **Proposition 3.6.9(a).** A bounded projection is an orthogonal projection in the sense of
(3.6.2) exactly when it is self-adjoint. -/
theorem prop_3_6_9_a (P : H →L[𝕜] H) (hP : IsIdempotentElem P) :
    (∀ v w : H, inner 𝕜 (P v) (((1 : H →L[𝕜] H) - P) w) = 0) ↔ (P : H →ₗ[𝕜] H).IsSymmetric := by
  have hPP : ∀ x : H, P (P x) = P x := fun x => DFunLike.congr_fun hP x
  have hexp : ∀ v w : H, inner 𝕜 (P v) (((1 : H →L[𝕜] H) - P) w)
      = inner 𝕜 (P v) w - inner 𝕜 (P v) (P w) := by
    intro v w
    rw [← inner_sub_right]
    simp
  constructor
  · intro h v w
    have h₁ : inner 𝕜 (P v) w = inner 𝕜 (P v) (P w) := by
      have hvw := hexp v w
      rw [h v w] at hvw
      linear_combination (norm := module) -hvw
    have h₂ : inner 𝕜 (P w) v = inner 𝕜 (P w) (P v) := by
      have hwv := hexp w v
      rw [h w v] at hwv
      linear_combination (norm := module) -hwv
    calc inner 𝕜 ((P : H →ₗ[𝕜] H) v) w = inner 𝕜 (P v) (P w) := h₁
      _ = starRingEnd 𝕜 (inner 𝕜 (P w) (P v)) := (inner_conj_symm _ _).symm
      _ = starRingEnd 𝕜 (inner 𝕜 (P w) v) := by rw [h₂]
      _ = inner 𝕜 v ((P : H →ₗ[𝕜] H) w) := inner_conj_symm _ _
  · intro h v w
    rw [hexp v w]
    have e₁ := h v (P w)
    have e₂ := h v w
    simp only [ContinuousLinearMap.coe_coe, hPP] at e₁ e₂
    rw [e₁, ← e₂, sub_self]

/-- The book's orthogonal projection operators are exactly Mathlib's symmetric projections. -/
theorem isOrthogonalProjectionOperator_iff (P : H →L[𝕜] H) :
    IsOrthogonalProjectionOperator P ↔ (P : H →ₗ[𝕜] H).IsSymmetricProjection := by
  constructor
  · rintro ⟨hP, horth⟩
    exact ⟨ContinuousLinearMap.IsIdempotentElem.toLinearMap hP, (prop_3_6_9_a P hP).1 horth⟩
  · rintro ⟨hidem, hsym⟩
    have hP : IsIdempotentElem P := ContinuousLinearMap.isIdempotentElem_toLinearMap_iff.1 hidem
    exact ⟨hP, (prop_3_6_9_a P hP).2 hsym⟩

/-- **Example 3.6.7.** For a finite orthonormal family `φ₁, …, φₙ`, the operator
`v ↦ ∑ᵢ (v, φᵢ) φᵢ` is an orthogonal projection. -/
theorem example_3_6_7 [CompleteSpace H] {n : ℕ} {u : Fin n → H} (hu : Orthonormal 𝕜 u) :
    IsOrthogonalProjectionOperator (∑ i, InnerProductSpace.rankOne 𝕜 (u i) (u i)) := by
  classical
  have hsp : (Submodule.span 𝕜 ((Finset.univ : Finset (Fin n)).image u : Set H)).starProjection
      = ∑ i, InnerProductSpace.rankOne 𝕜 (u i) (u i) := by
    rw [(OrthonormalBasis.span hu Finset.univ).starProjection_eq_sum_rankOne]
    simp only [OrthonormalBasis.span_apply]
    exact Finset.sum_coe_sort Finset.univ fun i => InnerProductSpace.rankOne 𝕜 (u i) (u i)
  rw [← hsp, isOrthogonalProjectionOperator_iff]
  exact Submodule.isSymmetricProjection_starProjection _

/-- **Proposition 3.6.9(b).** An orthogonal projection is bounded with `‖P‖ ≤ 1`, and `‖P‖ = 1`
unless `P = 0`. -/
theorem prop_3_6_9_b [CompleteSpace H] (P : H →L[𝕜] H) (hP : IsOrthogonalProjectionOperator P) :
    ‖P‖ ≤ 1 ∧ (P ≠ 0 → ‖P‖ = 1) := by
  have hone : P ≠ 0 → ‖P‖ = 1 := fun h0 =>
    (ContinuousLinearMap.IsIdempotentElem.norm_eq_one_iff_isSymmetric hP.1 h0).2
      ((prop_3_6_9_a P hP.1).1 hP.2)
  refine ⟨?_, hone⟩
  rcases eq_or_ne P 0 with h0 | h0
  · rw [h0, norm_zero]; norm_num
  · exact (hone h0).le

/-- **Proposition 3.6.9(c).** A closed subspace of a Hilbert space and its orthogonal complement
form a direct sum. -/
theorem prop_3_6_9_c [CompleteSpace H] (V₁ : Submodule 𝕜 H) (h : IsClosed (V₁ : Set H)) :
    IsCompl V₁ V₁ᗮ :=
  have := h.completeSpace_coe
  Submodule.isCompl_orthogonal V₁

/-- **Proposition 3.6.9(c)**, in the book's vocabulary: `H = V₁ ⊕ V₁ᗮ` is an orthogonal direct
sum in the sense of Definition 3.6.1. -/
theorem prop_3_6_9_c' [CompleteSpace H] (V₁ : Submodule 𝕜 H) (h : IsClosed (V₁ : Set H)) :
    IsOrthogonalDirectSum V₁ V₁ᗮ :=
  ⟨(isDirectSum_iff_isCompl V₁ V₁ᗮ).2 (prop_3_6_9_c V₁ h), Submodule.isOrtho_orthogonal_right V₁⟩

/-- An orthogonal projection is Mathlib's orthogonal projection onto its range. -/
theorem eq_starProjection_of_isOrthogonalProjectionOperator (V₁ : Submodule 𝕜 H)
    [V₁.HasOrthogonalProjection] {P : H →L[𝕜] H} (hP : IsOrthogonalProjectionOperator P)
    (hr : LinearMap.range (P : H →ₗ[𝕜] H) = V₁) : P = V₁.starProjection := by
  obtain ⟨hinst, hPeq⟩ := LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.1
    ((isOrthogonalProjectionOperator_iff P).1 hP)
  subst hr
  ext x
  exact congrFun (congrArg DFunLike.coe hPeq) x

/-- **Proposition 3.6.9(d).** There is exactly one orthogonal projection with a given closed
range `V₁`; it realizes the distance to `V₁`, and `I − P` is the orthogonal projection onto
`V₁ᗮ`. -/
theorem prop_3_6_9_d [CompleteSpace H] (V₁ : Submodule 𝕜 H) (h : IsClosed (V₁ : Set H)) :
    (∃! P : H →L[𝕜] H,
        IsOrthogonalProjectionOperator P ∧ LinearMap.range (P : H →ₗ[𝕜] H) = V₁) ∧
      ∀ P : H →L[𝕜] H, IsOrthogonalProjectionOperator P →
        LinearMap.range (P : H →ₗ[𝕜] H) = V₁ →
        (∀ v : H, ‖v - P v‖ = ⨅ w : V₁, ‖v - (w : H)‖) ∧
          IsOrthogonalProjectionOperator ((1 : H →L[𝕜] H) - P) ∧
            LinearMap.range (((1 : H →L[𝕜] H) - P : H →L[𝕜] H) : H →ₗ[𝕜] H) = V₁ᗮ := by
  have hcs := h.completeSpace_coe
  have hrange : LinearMap.range ((V₁.starProjection : H →L[𝕜] H) : H →ₗ[𝕜] H) = V₁ :=
    V₁.range_starProjection
  have hop : IsOrthogonalProjectionOperator (V₁.starProjection : H →L[𝕜] H) :=
    (isOrthogonalProjectionOperator_iff _).2 (Submodule.isSymmetricProjection_starProjection V₁)
  have honesub : (1 : H →L[𝕜] H) - V₁.starProjection = V₁ᗮ.starProjection :=
    (Submodule.starProjection_orthogonal' V₁).symm
  refine ⟨⟨V₁.starProjection, ⟨hop, hrange⟩, fun Q hQ =>
      eq_starProjection_of_isOrthogonalProjectionOperator V₁ hQ.1 hQ.2⟩, ?_⟩
  intro P hP hPr
  have hPeq : P = V₁.starProjection :=
    eq_starProjection_of_isOrthogonalProjectionOperator V₁ hP hPr
  subst hPeq
  refine ⟨fun v => ((isBestApprox_iff_norm_eq_iInf _ _ _).1
      (isBestApprox_starProjection V₁ v)).2, ?_, ?_⟩
  · rw [honesub]
    exact (isOrthogonalProjectionOperator_iff _).2
      (Submodule.isSymmetricProjection_starProjection _)
  · rw [honesub]
    exact V₁ᗮ.range_starProjection

/-- **Proposition 3.6.9(e).** The range of an orthogonal projection is closed, and `V` is the
orthogonal direct sum of `P(V)` and `(I − P)(V) = P(V)ᗮ`. -/
theorem prop_3_6_9_e [CompleteSpace H] (P : H →L[𝕜] H) (hP : IsOrthogonalProjectionOperator P) :
    IsClosed (LinearMap.range (P : H →ₗ[𝕜] H) : Set H) ∧
      IsCompl (LinearMap.range (P : H →ₗ[𝕜] H))
        (LinearMap.range (((1 : H →L[𝕜] H) - P : H →L[𝕜] H) : H →ₗ[𝕜] H)) ∧
      LinearMap.range (((1 : H →L[𝕜] H) - P : H →L[𝕜] H) : H →ₗ[𝕜] H)
        = (LinearMap.range (P : H →ₗ[𝕜] H))ᗮ := by
  have hlin : IsIdempotentElem (P : H →ₗ[𝕜] H) :=
    ContinuousLinearMap.IsIdempotentElem.toLinearMap hP.1
  have hsym : (P : H →ₗ[𝕜] H).IsSymmetric := (prop_3_6_9_a P hP.1).1 hP.2
  have hker : LinearMap.ker (P : H →ₗ[𝕜] H) = LinearMap.range (1 - (P : H →ₗ[𝕜] H)) :=
    LinearMap.IsIdempotentElem.ker_eq_range_one_sub hlin
  have hcoe : (((1 : H →L[𝕜] H) - P : H →L[𝕜] H) : H →ₗ[𝕜] H) = 1 - (P : H →ₗ[𝕜] H) := rfl
  refine ⟨ContinuousLinearMap.IsIdempotentElem.isClosed_range hP.1, ?_, ?_⟩
  · rw [hcoe, ← hker]
    exact LinearMap.IsProj.isCompl (LinearMap.IsIdempotentElem.isProj_range _ hlin)
  · rw [hcoe, ← hker, ← LinearMap.IsSymmetric.orthogonal_range hsym]

end Hilbert

end AtkinsonHan.Ch03
